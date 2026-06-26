import Complexity.Lang.Semantics
import Complexity.Lang.Frame
import Complexity.Lang.AppendGadget
import Complexity.Lang.ClearGadget
import Complexity.Complexity.TMPrimitives
import Complexity.Complexity.TapeMono
import Complexity.Lang.Compile.Core
import Complexity.Lang.Compile.Encoding
import Complexity.Lang.Compile.OpMachines
import Complexity.Lang.Compile.Cmd
import Complexity.Lang.Compile.RunClear

/-! # `Compile/RunMove` — move-one-bit / dual-target transfer + `compileTestBit` (Phase 1-refinement)

Second module of the `RunLemmas` split (see `REFACTOR-HANDOFF.md`). The
move-one-bit transfer gadget, the residue-tolerant `navigateAndTest` reading
(`skipped_*`, the Class-A cross-register helpers), the `compileTestBit` run
lemmas, and the dual-target duplicating move gadget `moveRegion2TM`. Imports
`RunClear`; consumed by `RunCopyTail`, `RunEqBit`. -/

set_option autoImplicit false

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators

/-! ### The move-one-bit transfer gadget (Risk C2, Task 2 critical path)

`moveRegionTM src dst` transfers register `src`'s content, **one bit at a time**,
to the **end** of register `dst` (FIFO — order preserved), emptying `src`. It is
the single building block of every remaining cross-register op
(`copy`/`tail`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`): e.g. `copy dst src sc`
= move `src→sc` then move `sc→`(`src`&`dst`).

**Structure — mirrors `clearRegionTM` exactly, with the content branch doing a
read+append instead of a bare delete.** The loop body navigates to `src`; on the
content branch (src non-empty) it reads the front bit (`bitReadTM`), deletes that
cell and rewinds (`stepDeleteRewindRawTM`, exactly as `clear`), then appends the
bit (`+1`) to `dst` and two-phase-rewinds; on the delim branch (src empty) it just
rewinds and the loop stops.

**✅ Probe-validated end-to-end** (2026-06-05, `#eval` on real `encodeTape`s, both
`dst>src` and `dst<src`): `encodeTape [[1,0],[1]] → encodeTape [[],[1,1,0]] ++ [0,0]`
and `encodeTape [[1],[0,1]] → encodeTape [[1,0,1],[]] ++ [0,0]` (residue =
`replicate (#moved bits) 0`). The exit-state offsets below were read off the probe
and verified to make the `loopTM` continue/terminate correctly. -/

/-- Single-bit transfer engine for a fixed bit `b`: delete `src`'s front cell and
rewind (`stepDeleteRewindRawTM`), then append `b+1` to `dst` and two-phase-rewind. -/
def Compile.moveBitM2TM (b dst : Nat) : FlatTM :=
  composeFlatTM ClearGadget.stepDeleteRewindRawTM
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ClearGadget.stepDeleteRewindTM_exit

/-- The surviving (found) exit of `moveBitM2TM` (independent of `b`): the
`stepDeleteRewindRawTM` state count plus the append bracket's found exit
(`appendAtTM.states + 6`). -/
def Compile.moveBitM2_exit (dst : Nat) : Nat :=
  ClearGadget.stepDeleteRewindRawTM.states + ((AppendGadget.appendAtTM 1 dst).states + 6)

/-- Content branch (src non-empty): read the front bit, then run the matching
single-bit transfer engine. The two bit paths exit at distinct states
(`moveContentExit0`/`moveContentExit1`), merged by `joinTwoHalts` below. -/
def Compile.moveContentRawTM (dst : Nat) : FlatTM :=
  branchComposeFlatTM Compile.bitReadTM (Compile.moveBitM2TM 0 dst) (Compile.moveBitM2TM 1 dst)
    Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1

/-- Bit-0 path exit of `moveContentRawTM`. -/
def Compile.moveContentExit0 (dst : Nat) : Nat :=
  Compile.bitReadTM.states + Compile.moveBitM2_exit dst

/-- Bit-1 path exit of `moveContentRawTM` (shifted by the bit-0 engine's states). -/
def Compile.moveContentExit1 (dst : Nat) : Nat :=
  Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states + Compile.moveBitM2_exit dst

/-- Content branch with the two bit-exits merged into one (`moveContentExit0`). -/
def Compile.moveContentTM (dst : Nat) : FlatTM :=
  Compile.joinTwoHalts (Compile.moveContentRawTM dst)
    (Compile.moveContentExit0 dst) (Compile.moveContentExit1 dst)

/-- The loop body: navigate to `src`, branch content (move one bit) vs delim
(src empty → rewind & stop). -/
def Compile.moveBodyRawTM (src dst : Nat) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM src) (Compile.moveContentTM dst)
    ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content src) (ClearGadget.navigateAndTestTM_exit_delim src)

/-- The loop's "continue" exit (content branch fired: one bit moved). -/
def Compile.moveBodyRawTM_exitLoop (src dst : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + Compile.moveContentExit0 dst

/-- The loop's "done" exit (delim branch fired: src empty). -/
def Compile.moveBodyRawTM_exitDone (src dst : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
    + ClearGadget.justRewindTM_exit

/-- The full move gadget: loop the body until `src` empties. -/
def Compile.moveRegionTM (src dst : Nat) : FlatTM :=
  loopTM (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)

/-- The single halt state of `moveRegionTM` (the `loopTM` done-exit, at `B.states`). -/
def Compile.moveRegionTM_exit (src dst : Nat) : Nat := (Compile.moveBodyRawTM src dst).states

theorem Compile.moveBitM2TM_tapes (b dst : Nat) : (Compile.moveBitM2TM b dst).tapes = 1 := by
  rw [Compile.moveBitM2TM, composeFlatTM_tapes]; exact ClearGadget.stepDeleteRewindRawTM_tapes

theorem Compile.moveContentRawTM_tapes (dst : Nat) : (Compile.moveContentRawTM dst).tapes = 1 := by
  rw [Compile.moveContentRawTM, branchComposeFlatTM_tapes]; exact Compile.bitReadTM_tapes

theorem Compile.moveContentTM_tapes (dst : Nat) : (Compile.moveContentTM dst).tapes = 1 := by
  rw [Compile.moveContentTM, Compile.joinTwoHalts_tapes]; exact Compile.moveContentRawTM_tapes dst

theorem Compile.moveBodyRawTM_tapes (src dst : Nat) : (Compile.moveBodyRawTM src dst).tapes = 1 := by
  rw [Compile.moveBodyRawTM, branchComposeFlatTM_tapes]; exact ClearGadget.navigateAndTestTM_tapes src

theorem Compile.moveRegionTM_tapes (src dst : Nat) : (Compile.moveRegionTM src dst).tapes = 1 := by
  rw [Compile.moveRegionTM, loopTM_tapes]; exact Compile.moveBodyRawTM_tapes src dst

theorem Compile.moveRegionTM_start (src dst : Nat) : (Compile.moveRegionTM src dst).start = 0 := by
  show (Compile.moveBodyRawTM src dst).start = 0
  show (branchComposeFlatTM _ _ _ _ _).start = 0
  rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src

/-- The branch that reaches the **kept** exit `h1`: `joinTwoHalts` agrees with the
raw machine, reaching `h1` at step `T`; the trajectory never hits `h1` and never
halts. -/
theorem Compile.joinTwoHalts_reaches_kept (raw : FlatTM) (h1 h2 : Nat) (cfg0 : FlatTMConfig)
    (T : Nat) (tape : List Nat × Nat × List Nat)
    (hraw : runFlatTM T raw cfg0 = some { state_idx := h1, tapes := [tape] })
    (hraw_traj : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck →
        haltingStateReached raw ck = false)
    (hh1 : raw.halt[h1]? = some true) (hh2 : raw.halt[h2]? = some true) :
    runFlatTM T (joinTwoHalts raw h1 h2) cfg0 = some { state_idx := h1, tapes := [tape] } ∧
    (∀ k, k < T → ∀ ck, runFlatTM k (joinTwoHalts raw h1 h2) cfg0 = some ck →
        ck.state_idx ≠ h1 ∧ haltingStateReached (joinTwoHalts raw h1 h2) ck = false) := by
  have hnv : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck → ck.state_idx ≠ h2 :=
    fun k hk ck hck => ClearGadget.ne_of_not_halting hh2 (hraw_traj k hk ck hck)
  refine ⟨?_, ?_⟩
  · rw [joinTwoHalts_run_eq_weak raw h1 h2 T cfg0 hnv]; exact hraw
  · intro k hk ck hck
    rw [joinTwoHalts_run_eq_weak raw h1 h2 k cfg0
        (fun j hj cj hcj => hnv j (by omega) cj hcj)] at hck
    have hnh := hraw_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting hh1 hnh, Compile.joinTwoHalts_halting_false raw h1 h2 ck hnh⟩

/-- The branch that reaches the **demoted** exit `h2`: `joinTwoHalts` reaches `h2`
at step `T`, then bridges to the kept exit `h1` in one more step. -/
theorem Compile.joinTwoHalts_reaches_demoted (raw : FlatTM) (h1 h2 : Nat) (cfg0 : FlatTMConfig)
    (T : Nat) (left right : List Nat) (head : Nat)
    (hraw : runFlatTM T raw cfg0 = some { state_idx := h2, tapes := [(left, head, right)] })
    (hraw_traj : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck →
        haltingStateReached raw ck = false)
    (hh1 : raw.halt[h1]? = some true) (hh2 : raw.halt[h2]? = some true) (hne : h1 ≠ h2)
    (h_sym : ∀ v, currentTapeSymbol (left, head, right) = some v → v < raw.sig) :
    runFlatTM (T + 1) (joinTwoHalts raw h1 h2) cfg0
        = some { state_idx := h1, tapes := [(left, head, right)] } ∧
    (∀ k, k < T + 1 → ∀ ck, runFlatTM k (joinTwoHalts raw h1 h2) cfg0 = some ck →
        ck.state_idx ≠ h1 ∧ haltingStateReached (joinTwoHalts raw h1 h2) ck = false) := by
  have hnv : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck → ck.state_idx ≠ h2 :=
    fun k hk ck hck => ClearGadget.ne_of_not_halting hh2 (hraw_traj k hk ck hck)
  have hjoinT : runFlatTM T (joinTwoHalts raw h1 h2) cfg0
      = some { state_idx := h2, tapes := [(left, head, right)] } := by
    rw [joinTwoHalts_run_eq_weak raw h1 h2 T cfg0 hnv]; exact hraw
  have hjoinHalt_h2 : haltingStateReached (joinTwoHalts raw h1 h2)
      { state_idx := h2, tapes := [(left, head, right)] } = false := by
    show (raw.halt.set h2 false).getD h2 false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl]; split <;> rfl
  have hstep : stepFlatTM (joinTwoHalts raw h1 h2)
      { state_idx := h2, tapes := [(left, head, right)] }
      = some { state_idx := h1, tapes := [(left, head, right)] } :=
    joinTwoHalts_step_to_h1 raw h1 h2 left right head h_sym
  refine ⟨?_, ?_⟩
  · rw [runFlatTM_compose (joinTwoHalts raw h1 h2) T 1 cfg0 _ hjoinT]
    show (if haltingStateReached (joinTwoHalts raw h1 h2)
              { state_idx := h2, tapes := [(left, head, right)] } = true then _
          else match stepFlatTM (joinTwoHalts raw h1 h2)
              { state_idx := h2, tapes := [(left, head, right)] } with
            | none => _ | some c => runFlatTM 0 (joinTwoHalts raw h1 h2) c) = _
    rw [if_neg (by rw [hjoinHalt_h2]; decide), hstep]
    rfl
  · intro k hk ck hck
    rcases Nat.lt_or_ge k T with hkT | hkT
    · rw [joinTwoHalts_run_eq_weak raw h1 h2 k cfg0
          (fun j hj cj hcj => hnv j (by omega) cj hcj)] at hck
      have hnh := hraw_traj k hkT ck hck
      exact ⟨ClearGadget.ne_of_not_halting hh1 hnh, Compile.joinTwoHalts_halting_false raw h1 h2 ck hnh⟩
    · have hkeq : k = T := by omega
      subst hkeq
      rw [hjoinT] at hck
      obtain rfl := (Option.some.inj hck).symm
      exact ⟨Ne.symm hne, hjoinHalt_h2⟩

/-- `appendAtTM`'s state count is independent of the inserted symbol (`ins` only
enters via `insertCarryTM ins`, whose `states` field is the constant `6`). -/
theorem Compile.appendAtTM_states_eq (ins dst : Nat) :
    (AppendGadget.appendAtTM ins dst).states = (AppendGadget.appendAtTM 1 dst).states := by
  induction dst with
  | zero => rfl
  | succ d ih =>
      rw [show AppendGadget.appendAtTM ins (d + 1)
            = composeFlatTM (ScanPast.scanPastDelimTM 4 0) (AppendGadget.appendAtTM ins d) 1 from rfl,
          show AppendGadget.appendAtTM 1 (d + 1)
            = composeFlatTM (ScanPast.scanPastDelimTM 4 0) (AppendGadget.appendAtTM 1 d) 1 from rfl,
          composeFlatTM_states, composeFlatTM_states, ih]

/-- **The single-bit transfer engine run (Risk C2, Task 2).** Run from `src`'s
content start (head `1 + |encodeRegs (s.take src)|`) with `src`'s front bit `b`
(`s.get src = b :: cs`), `moveBitM2TM b dst` deletes that front cell, rewinds,
appends `b` to the end of `dst`, and two-phase-rewinds, landing at
`moveBitM2_exit dst` with the tape
`encodeTape ((s.set src cs).set dst (s.get dst ++ [b])) ++ (res ++ [0])` and head
`0`. Composes `stepDeleteRewind_run` (on `src`) with `appendBitTwoPhase_run` (on
the deleted state, appending to `dst`). -/
theorem Compile.moveBitM2_run (s : State) (src dst : Var) (b : Nat) (cs : List Nat)
    (hb : b ≤ 1) (hsd : src ≠ dst) (hsrc : src < s.length) (hdst : dst < s.length)
    (hbit : Compile.BitState s) (hcons : s.get src = b :: cs) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBitM2TM b dst)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBitM2_exit dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBitM2TM b dst)
            { state_idx := 0,
              tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.moveBitM2TM b dst) ck = false)
    ∧ t ≤ 7 * (Compile.encodeTape s ++ res).length + 18 := by
  have hne : s.get src ≠ [] := by rw [hcons]; exact List.cons_ne_nil _ _
  have htl : (s.get src).tail = cs := by rw [hcons, List.tail_cons]
  -- Phase 1: delete src's front cell + rewind.
  obtain ⟨t1, h_sdr, h_sdr_traj, h_t1_bnd⟩ :=
    Compile.stepDeleteRewind_run s src res hsrc hbit hne hres
  rw [htl] at h_sdr
  -- Phase 2 ingredients (on the post-delete state `s.set src cs`).
  have hbit1 : Compile.BitState (s.set src cs) := by
    have := Compile.BitState_set_tail s src hbit hsrc; rwa [htl] at this
  have hlen1 : (s.set src cs).length = s.length := Compile.length_set s src cs hsrc
  have hdst1 : dst < (s.set src cs).length := by rw [hlen1]; exact hdst
  have hres1 : Compile.ValidResidue (res ++ [0]) := by
    apply Compile.ValidResidue_append _ _ hres; intro x hx
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  obtain ⟨t2, h_app, h_app_traj, h_t2_bnd⟩ :=
    Compile.appendBitTwoPhase_run b hb (s.set src cs) dst hbit1 hdst1 (res ++ [0]) hres1
  have hgetdst : (s.set src cs).get dst = s.get dst :=
    Compile.get_set_ne s src cs dst hsrc (Ne.symm hsd)
  rw [hgetdst] at h_app
  -- length balance: deleting a bit and padding the residue with `[0]` keeps the length.
  have hLbal : (Compile.encodeTape (s.set src cs) ++ (res ++ [0])).length
      = (Compile.encodeTape s ++ res).length := by
    have hbalance := Compile.encodeTape_set_length s src cs hsrc
    rw [hcons] at hbalance
    simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil]
      at hbalance ⊢
    omega
  -- M₂ start (= 0).
  have hM2start : (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).start = 0 := by
    show (composeFlatTM (AppendGadget.appendAtTM (b + 1) dst) (ScanLeft.rewindTwoPhaseTM 4 3)
          (AppendGadget.appendAtTM_exit dst)).start = 0
    rw [composeFlatTM_start, AppendGadget.appendAtTM_start]
  set right₁ : List Nat := Compile.encodeTape (s.set src cs) ++ (res ++ [0]) with hr1
  -- shared compose inputs.
  have hvalid1 : validFlatTM ClearGadget.stepDeleteRewindRawTM := ClearGadget.stepDeleteRewindRawTM_valid
  have hvalid2 : validFlatTM (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) :=
    AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst
  have hexit_lt : ClearGadget.stepDeleteRewindTM_exit < ClearGadget.stepDeleteRewindRawTM.states := by
    show (17 : Nat) < ClearGadget.stepDeleteRewindRawTM.states
    show (17 : Nat) < 19; omega
  have hcfg0lt : (0 : Nat) < ClearGadget.stepDeleteRewindRawTM.states := by
    show (0 : Nat) < 19; omega
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, right₁) = some v →
      v < max ClearGadget.stepDeleteRewindRawTM.sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).sig := by
    intro v hv
    rw [hr1, show currentTapeSymbol (([] : List Nat), 0,
          Compile.encodeTape (s.set src cs) ++ (res ++ [0])) = some 3 from rfl] at hv
    rw [show max ClearGadget.stepDeleteRewindRawTM.sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).sig = 4 from by
        rw [AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl]
    have : v = 3 := (Option.some.inj hv).symm
    omega
  -- per-component trajectory hyps with the `≠ exit` part for M₁.
  have h_traj1 : ∀ k, k < t1 → ∀ ck,
      runFlatTM k ClearGadget.stepDeleteRewindRawTM
          { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                       Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.stepDeleteRewindTM_exit ∧
      haltingStateReached ClearGadget.stepDeleteRewindRawTM ck = false := by
    intro k hk ck hck
    have hh := h_sdr_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting ClearGadget.stepDeleteRewindRawTM_halt_seventeen hh, hh⟩
  have h_app_traj' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
          { state_idx := (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).start,
            tapes := [([], 0, right₁)] } = some ck →
      haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ck = false := by
    rw [hM2start, hr1]; exact h_app_traj
  -- h_halt2 (the M₂ exit halts).
  have h_halt2 : haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
      { state_idx := 6 + (AppendGadget.appendAtTM (b + 1) dst).states,
        tapes := [([], 0, Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                    ++ (res ++ [0]))] } = true := by
    rw [show (6 : Nat) + (AppendGadget.appendAtTM (b + 1) dst).states
          = (AppendGadget.appendAtTM (b + 1) dst).states + 6 from Nat.add_comm ..]
    exact Compile.haltingStateReached_of_halt
      (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst)
  have hmoveeq : Compile.moveBitM2TM b dst
      = composeFlatTM ClearGadget.stepDeleteRewindRawTM
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
          ClearGadget.stepDeleteRewindTM_exit := rfl
  have hstate_eq : Compile.moveBitM2_exit dst
      = (6 + (AppendGadget.appendAtTM (b + 1) dst).states)
          + ClearGadget.stepDeleteRewindRawTM.states := by
    show ClearGadget.stepDeleteRewindRawTM.states + ((AppendGadget.appendAtTM 1 dst).states + 6)
        = (6 + (AppendGadget.appendAtTM (b + 1) dst).states)
            + ClearGadget.stepDeleteRewindRawTM.states
    rw [Compile.appendAtTM_states_eq (b + 1) dst]; omega
  have hmain := composeFlatTM_run hvalid1 hvalid2 hexit_lt
    { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                 Compile.encodeTape s ++ res)] }
    hcfg0lt [] 0 right₁ hsym h_sdr h_traj1
    (by rw [hM2start]; exact h_app) h_halt2
  refine ⟨t1 + 1 + t2, ?_, ?_, ?_⟩
  · rw [hmoveeq, hstate_eq]; exact hmain.1
  · intro k hk ck hck
    rw [hmoveeq] at hck ⊢
    exact composeFlatTM_no_early_halt hvalid1 hvalid2 hexit_lt
      { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                   Compile.encodeTape s ++ res)] }
      hcfg0lt [] 0 right₁ hsym h_sdr h_traj1 h_app_traj' k hk ck hck
  · rw [hLbal] at h_t2_bnd
    omega

/-! #### `moveContent` scaffolding (the bit-read branch over the transfer engine). -/

theorem Compile.moveBitM2TM_sig (b dst : Nat) : (Compile.moveBitM2TM b dst).sig = 4 := by
  rw [Compile.moveBitM2TM, composeFlatTM_sig, AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl

theorem Compile.moveBitM2TM_valid (b dst : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.moveBitM2TM b dst) :=
  composeFlatTM_valid ClearGadget.stepDeleteRewindRawTM
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ClearGadget.stepDeleteRewindTM_exit
    ClearGadget.stepDeleteRewindRawTM_valid
    (AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst)
    (by show (17 : Nat) < ClearGadget.stepDeleteRewindRawTM.states; show (17 : Nat) < 19; omega)
    ClearGadget.stepDeleteRewindRawTM_tapes
    (AppendGadget.appendAtThenTwoPhaseRewindTM_tapes (b + 1) dst)

theorem Compile.moveBitM2_exit_is_halt (b dst : Nat) :
    (Compile.moveBitM2TM b dst).halt[Compile.moveBitM2_exit dst]? = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro ClearGadget.stepDeleteRewindRawTM
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ClearGadget.stepDeleteRewindTM_exit
    ((AppendGadget.appendAtTM (b + 1) dst).states + 6)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst)
  rw [Compile.appendAtTM_states_eq (b + 1) dst] at h
  exact h

theorem Compile.moveBitM2_exit_lt (b dst : Nat) :
    Compile.moveBitM2_exit dst < (Compile.moveBitM2TM b dst).states := by
  show ClearGadget.stepDeleteRewindRawTM.states + ((AppendGadget.appendAtTM 1 dst).states + 6)
      < (composeFlatTM ClearGadget.stepDeleteRewindRawTM
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
          ClearGadget.stepDeleteRewindTM_exit).states
  rw [composeFlatTM_states, AppendGadget.appendAtThenTwoPhaseRewindTM_states,
      Compile.appendAtTM_states_eq (b + 1) dst,
      show (ScanLeft.rewindTwoPhaseTM 4 3).states = 8 from rfl]
  omega

theorem Compile.moveContentRawTM_valid (dst : Nat) : validFlatTM (Compile.moveContentRawTM dst) :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.bitReadTM_valid
    (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide)
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide)
    Compile.bitReadTM_tapes (Compile.moveBitM2TM_tapes 0 dst) (Compile.moveBitM2TM_tapes 1 dst)

theorem Compile.moveContentRawTM_sig (dst : Nat) : (Compile.moveContentRawTM dst).sig = 4 := by
  rw [Compile.moveContentRawTM, branchComposeFlatTM_sig, Compile.bitReadTM_sig,
      Compile.moveBitM2TM_sig 0 dst, Compile.moveBitM2TM_sig 1 dst]; rfl

theorem Compile.moveContentExit0_is_halt (dst : Nat) :
    (Compile.moveContentRawTM dst).halt[Compile.moveContentExit0 dst]? = some true := by
  rw [Compile.moveContentExit0, Compile.moveContentRawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2_exit_lt 0 dst)
    (Compile.moveBitM2_exit_is_halt 0 dst)

theorem Compile.moveContentExit1_is_halt (dst : Nat) :
    (Compile.moveContentRawTM dst).halt[Compile.moveContentExit1 dst]? = some true := by
  rw [Compile.moveContentExit1, Compile.moveContentRawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2_exit_is_halt 1 dst)

theorem Compile.moveContentExit0_ne_exit1 (dst : Nat) :
    Compile.moveContentExit0 dst ≠ Compile.moveContentExit1 dst := by
  show Compile.bitReadTM.states + Compile.moveBitM2_exit dst
      ≠ Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states + Compile.moveBitM2_exit dst
  have h0 : 0 < (Compile.moveBitM2TM 0 dst).states := by
    have := Compile.moveBitM2_exit_lt 0 dst; omega
  omega

/-- **The content-branch run (Risk C2, Task 2).** Run from `src`'s content start
(head `H = 1 + |regBlocks (map shiftReg (s.take src))|`) with front bit `b`
(`s.get src = b :: cs`), `moveContentTM dst` reads the bit and runs the matching
single-bit transfer, the two bit-paths merging through `joinTwoHalts` into
`moveContentExit0 dst`. The tape becomes
`encodeTape ((s.set src cs).set dst (s.get dst ++ [b])) ++ (res ++ [0])`. Mirrors
`opInnerBit_run`. -/
theorem Compile.moveContent_run (s : State) (src dst : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd : src ≠ dst)
    (hbit : Compile.BitState s) (hsrc : src < s.length) (hdst : dst < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveContentTM dst)
        { state_idx := 0,
          tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveContentExit0 dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveContentTM dst)
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.moveContentExit0 dst ∧
        haltingStateReached (Compile.moveContentTM dst) ck = false)
    ∧ t ≤ 7 * (Compile.encodeTape s ++ res).length + 21 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.moveContentRawTM dst with hrawdef
  set h1 := Compile.moveContentExit0 dst with hh1def
  set h2 := Compile.moveContentExit1 dst with hh2def
  have hraweq : branchComposeFlatTM Compile.bitReadTM
      (Compile.moveBitM2TM 0 dst) (Compile.moveBitM2TM 1 dst)
      Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1 = raw := rfl
  have hMeq : Compile.moveContentTM dst = joinTwoHalts raw h1 h2 := rfl
  rw [hMeq]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hHeq : (1 : Nat) + (Compile.encodeRegs (s.take src)).length = H := by
    rw [hHdef, hskdef, Compile.regBlocks_map_shiftReg]
  -- length facts.
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  -- content decomposition (`src` nonempty).
  set tail' := Compile.shiftReg cs ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src hsrc
    rw [← hskdef] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg cs := by
      rw [hcons]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hHlt : H < (Compile.encodeTape s ++ res).length := by
    rw [hdecomp, hHdef]; simp only [List.length_cons, List.length_append]; omega
  have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = b + 1 := by
    have h? : (Compile.encodeTape s ++ res)[H]? = some (b + 1) := by
      rw [hdecomp, hHdef,
          show ((3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail'))
            = ((3 : Nat) :: AppendGadget.regBlocks skipped) ++ ((b + 1) :: tail') from by simp,
          List.getElem?_append_right (by simp only [List.length_cons]; omega),
          show 1 + (AppendGadget.regBlocks skipped).length
            - ((3 : Nat) :: AppendGadget.regBlocks skipped).length = 0 from by
              simp only [List.length_cons]; omega]
      rfl
    rw [List.getElem?_eq_getElem hHlt] at h?
    rw [List.get_eq_getElem]; exact Option.some.inj h?
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max Compile.bitReadTM.sig
          (max (Compile.moveBitM2TM 0 dst).sig (Compile.moveBitM2TM 1 dst).sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    rw [Compile.bitReadTM_sig]
    have : v < 4 := by have : v = b + 1 := (Option.some.inj hv).symm; omega
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < Compile.bitReadTM.states := by rw [Compile.bitReadTM_states]; omega
  have hexit_neq : Compile.bitReadTM_exit_b0 ≠ Compile.bitReadTM_exit_b1 := by decide
  have hep_lt : Compile.bitReadTM_exit_b0 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide
  have hen_lt : Compile.bitReadTM_exit_b1 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide
  have hh1_is := Compile.moveContentExit0_is_halt dst
  have hh2_is := Compile.moveContentExit1_is_halt dst
  have hh_ne := Compile.moveContentExit0_ne_exit1 dst
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  have htest_run := Compile.bitReadTM_run b hb [] (Compile.encodeTape s ++ res) H hHlt hcellH
  have htest_traj : ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.bitReadTM cfg0 = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧ ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧
      haltingStateReached Compile.bitReadTM ck = false := by
    intro k hk ck hck
    exact Compile.bitReadTM_no_early_halt [] (Compile.encodeTape s ++ res) H k hk ck hck
  interval_cases b
  · -- bit 0 (cell value 1): pos branch, transfer engine for bit 0; kept exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM2_run s src dst 0 cs (by omega) hsd hsrc hdst hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM2_exit_is_halt 0 dst))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM2_exit dst + Compile.bitReadTM.states = h1 := by
      rw [hh1def]; show Compile.moveBitM2_exit dst + Compile.bitReadTM.states
        = Compile.bitReadTM.states + Compile.moveBitM2_exit dst
      omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [0])) ++ (res ++ [0]))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega
  · -- bit 1 (cell value 2): neg branch, transfer engine for bit 1; demoted exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM2_run s src dst 1 cs (by omega) hsd hsrc hdst hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM2_exit_is_halt 1 dst))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM2_exit dst
        + (Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states) = h2 := by
      rw [hh2def]; show Compile.moveBitM2_exit dst
          + (Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states)
        = Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states + Compile.moveBitM2_exit dst
      omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [1])) ++ (res ++ [0])) 0
      hneg.1 (fun k hk ck hck => hneg_traj k hk ck hck) hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [1])) ++ (res ++ [0]))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.moveContentRawTM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega

/-! ### Residue-tolerant `navigateAndTest` reading (Class-A cross-register ops)

The Class-A cross-register ops (`nonEmpty`/`head`/`eqBit`: ≤ 1-cell output) all
start by reading register `src`'s first tape cell and branching. `ClearGadget`'s
`navigateAndTestTM_run_content`/`_run_delim` do exactly this, but are stated on a
clean tape `3 :: (regBlocks skipped ++ v :: tail')`. The lemmas below lift them to
the residue-tolerant `encodeTape s ++ res` shape (the input every compiled
fragment actually sees): register `src`'s slot sits between the leading sentinel
and the trailing terminator, so the residue (past the terminator) is irrelevant
to the read. The exit head lands on `src`'s first cell at index
`1 + |regBlocks (preceding registers)|`; the **content** exit means `src` is
non-empty (answer bit `1`), the **delim** exit means `src` is empty (answer bit
`0`). Reusable by every Class-A op. -/

/-- Helper bridge: `s.take src` mapped through `shiftReg` has length `src`. -/
theorem Compile.skipped_length (s : State) (src : Var) (h : src < s.length) :
    ((s.take src).map Compile.shiftReg).length = src := by
  rw [List.length_map, List.length_take, Nat.min_eq_left (le_of_lt h)]

/-- The `h_skip` precondition: every preceding register block (`shiftReg` of a
`BitState` register) is delimiter-free and `< 4`. -/
theorem Compile.skipped_ok (s : State) (src : Var) (hbit : Compile.BitState s) :
    ∀ b' ∈ (s.take src).map Compile.shiftReg, (∀ x ∈ b', x ≠ 0) ∧ (∀ x ∈ b', x < 4) := by
  intro b' hb'
  rw [List.mem_map] at hb'
  obtain ⟨reg, hreg, rfl⟩ := hb'
  have hregs : reg ∈ s := List.mem_of_mem_take hreg
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; omega
  · intro x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hbit reg hregs y hy; omega

/-- **Residue-tolerant `navigateAndTest` — content branch (`src` non-empty).** -/
theorem Compile.navTestReg_run_content (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hne : s.get src ≠ []) :
    runFlatTM (ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1)
        (ClearGadget.navigateAndTestTM src)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_content src,
               tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                          Compile.encodeTape s ++ res)] } := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  obtain ⟨b, r, hbr⟩ : ∃ b r, s.get src = b :: r := by
    cases hsr : s.get src with
    | nil => exact absurd hsr hne
    | cons b r => exact ⟨b, r, rfl⟩
  have hb1 : b ≤ 1 := by
    have hmem : s.get src ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem b (by simp [hbr])
  set tail' := Compile.shiftReg r ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg r := by
      rw [hbr]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hcontent := ClearGadget.navigateAndTestTM_run_content skipped (b + 1) tail'
    (Compile.skipped_ok s src hbit) (by omega) (by omega)
  rw [hskiplen] at hcontent
  rw [← hdecomp] at hcontent
  exact hcontent

/-- **Residue-tolerant `navigateAndTest` — delim branch (`src` empty).** -/
theorem Compile.navTestReg_run_delim (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = []) :
    runFlatTM (ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1)
        (ClearGadget.navigateAndTestTM src)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim src,
               tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                          Compile.encodeTape s ++ res)] } := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  set tail' := Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = [] := by
      rw [hempty]; rfl
    rw [hsr, List.append_nil] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hdelim := ClearGadget.navigateAndTestTM_run_delim skipped tail'
    (Compile.skipped_ok s src hbit)
  rw [hskiplen] at hdelim
  rw [← hdecomp] at hdelim
  exact hdelim

/-- Navtest no-early-halt trajectory (avoids *both* exits), content branch. -/
theorem Compile.navTestReg_traj_content (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hne : s.get src ≠ []) :
    ∀ k, k < ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  obtain ⟨b, r, hbr⟩ : ∃ b r, s.get src = b :: r := by
    cases hsr : s.get src with
    | nil => exact absurd hsr hne
    | cons b r => exact ⟨b, r, rfl⟩
  have hb1 : b ≤ 1 := by
    have hmem : s.get src ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem b (by simp [hbr])
  set tail' := Compile.shiftReg r ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg r := by
      rw [hbr]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  intro k hk ck hck
  have hsk_eq : ClearGadget.navigateAndTestTM src = ClearGadget.navigateAndTestTM skipped.length := by
    rw [hskiplen]
  rw [hsk_eq, hdecomp] at hck
  have hh := ClearGadget.navigateAndTestTM_no_early_halt skipped (b + 1) tail'
    (Compile.skipped_ok s src hbit) (by omega) k hk ck hck
  rw [← hsk_eq] at hh
  exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
         ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh, hh⟩

/-- Navtest no-early-halt trajectory (avoids *both* exits), delim branch. -/
theorem Compile.navTestReg_traj_delim (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = []) :
    ∀ k, k < ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  set tail' := Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = [] := by rw [hempty]; rfl
    rw [hsr, List.append_nil] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  intro k hk ck hck
  have hsk_eq : ClearGadget.navigateAndTestTM src = ClearGadget.navigateAndTestTM skipped.length := by
    rw [hskiplen]
  rw [hsk_eq, hdecomp] at hck
  have hh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail'
    (Compile.skipped_ok s src hbit) (by omega) k hk ck hck
  rw [← hsk_eq] at hh
  exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
         ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh, hh⟩

/-! #### `compileTestBit` run lemmas (Risk C2, bottom-up Task 2)

The micro-steps of `exactOneOneTM`, the inner-tester composition, the raw
three-leaf tester, and the two packaged contracts `Compile.testBitReg_run_pos` /
`Compile.testBitReg_run_neg` that the `compileIfBit` residue combinator consumes:
the tester reaches `exitPos` iff `s.get t = [1]`, with the head back at `0` and
the tape **unchanged** (the branch bodies then start from their own
`initFlatConfig`). -/

/-- `exactOneOneTM` step, state 0 on a `1` cell (bit 0): → NEG, stay. -/
private theorem Compile.exactOneOne_step0_b0 (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 1) :
    stepFlatTM Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 2, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym' : cfg.tapes.map currentTapeSymbol = [some 1] := by
    show [currentTapeSymbol (left, head, right)] = [some 1]
    rw [currentTapeSymbol_in_range h, hget]
  show Option.bind (Compile.exactOneOneTM.trans.find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
  have hMatch : entryMatchesConfig
      { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
    show ((0 : Nat) == cfg.state_idx &&
        decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
    rw [hSym']; rfl
  rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
        = some { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
                 dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
    show List.find? _ (_ :: _) = _
    rw [List.find?_cons, hMatch]]
  rfl

/-- `exactOneOneTM` step, state 0 on a `2` cell (bit 1): → state 1, right. -/
private theorem Compile.exactOneOne_step0_b1 (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 2) :
    stepFlatTM Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym' : cfg.tapes.map currentTapeSymbol = [some 2] := by
    show [currentTapeSymbol (left, head, right)] = [some 2]
    rw [currentTapeSymbol_in_range h, hget]
  show Option.bind (Compile.exactOneOneTM.trans.find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
  have hNo : entryMatchesConfig
      { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
        decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym']
    have h_ne : ([some 1] : List (Option Nat)) ≠ [some 2] := by decide
    simp [h_ne]
  have hMatch : entryMatchesConfig
      { src_state := 0, src_tape_vals := [some 2], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] } cfg = true := by
    show ((0 : Nat) == cfg.state_idx &&
        decide (([some 2] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
    rw [hSym']; rfl
  rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
        = some { src_state := 0, src_tape_vals := [some 2], dst_state := 1,
                 dst_write_vals := [none], move_dirs := [TMMove.Rmove] } from by
    show List.find? _ (_ :: _ :: _) = _
    rw [List.find?_cons, hNo, List.find?_cons, hMatch]]
  rfl

/-- `exactOneOneTM` step, state 1 on a cell `v ∈ {0, 1, 2}` (the block-end `0`
→ POS = 3; a bit cell → NEG = 2): stay. -/
private theorem Compile.exactOneOne_step1 (left right : List Nat) (head : Nat) (v : Nat)
    (hv : v ≤ 2) (h : head < right.length) (hget : right.get ⟨head, h⟩ = v) :
    stepFlatTM Compile.exactOneOneTM { state_idx := 1, tapes := [(left, head, right)] }
      = some { state_idx := if v = 0 then 3 else 2, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 1, tapes := [(left, head, right)] }
  have hSym' : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]
    rw [currentTapeSymbol_in_range h, hget]
  have hNo0 : ∀ (sv : List (Option Nat)) (d : Nat) (w : List (Option Nat)) (m : List TMMove),
      entryMatchesConfig
        { src_state := 0, src_tape_vals := sv, dst_state := d,
          dst_write_vals := w, move_dirs := m } cfg = false := by
    intro sv d w m
    show ((0 : Nat) == cfg.state_idx && _) = false
    rfl
  show Option.bind (Compile.exactOneOneTM.trans.find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
  interval_cases v
  · have hMatch : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 0] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
          = some { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
                   dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
      show List.find? _ (_ :: _ :: _ :: _) = _
      rw [List.find?_cons, hNo0, List.find?_cons, hNo0, List.find?_cons, hMatch]]
    rfl
  · have hNo2 : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 0] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
      rw [hSym']
      have h_ne : ([some 0] : List (Option Nat)) ≠ [some 1] := by decide
      simp [h_ne]
    have hMatch : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
          = some { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
                   dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
      show List.find? _ (_ :: _ :: _ :: _ :: _) = _
      rw [List.find?_cons, hNo0, List.find?_cons, hNo0, List.find?_cons, hNo2,
          List.find?_cons, hMatch]]
    rfl
  · have hNo2 : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 0] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
      rw [hSym']
      have h_ne : ([some 0] : List (Option Nat)) ≠ [some 2] := by decide
      simp [h_ne]
    have hNo3 : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
      rw [hSym']
      have h_ne : ([some 1] : List (Option Nat)) ≠ [some 2] := by decide
      simp [h_ne]
    have hMatch : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 2], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 2] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
          = some { src_state := 1, src_tape_vals := [some 2], dst_state := 2,
                   dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
      show List.find? _ (_ :: _ :: _ :: _ :: _) = _
      rw [List.find?_cons, hNo0, List.find?_cons, hNo0, List.find?_cons, hNo2,
          List.find?_cons, hNo3, List.find?_cons, hMatch]]
    rfl

/-- States `0`/`1` of `exactOneOneTM` are not halting. -/
private theorem Compile.exactOneOne_not_halting (tapes : List (List Nat × Nat × List Nat))
    (i : Nat) (hi : i ≤ 1) :
    haltingStateReached Compile.exactOneOneTM { state_idx := i, tapes := tapes } = false := by
  interval_cases i <;> rfl

/-- `exactOneOneTM` run, NEG via bit `0` first cell: 1 step. -/
private theorem Compile.exactOneOne_run_b0 (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 1) :
    runFlatTM 1 Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 2, tapes := [(left, head, right)] } := by
  show (if haltingStateReached Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.exactOneOneTM cfg') = _
  rw [show haltingStateReached Compile.exactOneOneTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.exactOneOne_step0_b0 left right head h hget]
  rfl

/-- `exactOneOneTM` run, two-cell read (`2` then `v ≤ 2`): 2 steps, head `+1`;
exit POS (`3`) iff the second cell is the block-end `0`. -/
private theorem Compile.exactOneOne_run_two (left right : List Nat) (head : Nat) (v : Nat)
    (hv : v ≤ 2) (h : head < right.length) (hget : right.get ⟨head, h⟩ = 2)
    (h1 : head + 1 < right.length) (hget1 : right.get ⟨head + 1, h1⟩ = v) :
    runFlatTM 2 Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := if v = 0 then 3 else 2,
               tapes := [(left, head + 1, right)] } := by
  show (if haltingStateReached Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 1 Compile.exactOneOneTM cfg') = _
  rw [show haltingStateReached Compile.exactOneOneTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.exactOneOne_step0_b1 left right head h hget]
  show (if haltingStateReached Compile.exactOneOneTM
            { state_idx := 1, tapes := [(left, head + 1, right)] } = true then _
        else match stepFlatTM Compile.exactOneOneTM
            { state_idx := 1, tapes := [(left, head + 1, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.exactOneOneTM cfg') = _
  rw [show haltingStateReached Compile.exactOneOneTM
        { state_idx := 1, tapes := [(left, head + 1, right)] } = false from rfl,
      Compile.exactOneOne_step1 left right (head + 1) v hv h1 hget1]
  rfl

/-- `exactOneOneTM` 1-step trajectory (avoids both exits, non-halting). -/
private theorem Compile.exactOneOne_traj_one (left right : List Nat) (head : Nat) :
    ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.exactOneOneTM
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ Compile.exactOneOneTM_exitPos ∧
      ck.state_idx ≠ Compile.exactOneOneTM_exitNeg ∧
      haltingStateReached Compile.exactOneOneTM ck = false := by
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  obtain rfl : ck = { state_idx := 0, tapes := [(left, head, right)] } :=
    (Option.some.inj hck).symm
  exact ⟨show (0 : Nat) ≠ 3 by omega, show (0 : Nat) ≠ 2 by omega, rfl⟩

/-- `exactOneOneTM` 2-step trajectory (avoids both exits, non-halting). -/
private theorem Compile.exactOneOne_traj_two (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 2) :
    ∀ k, k < 2 → ∀ ck,
      runFlatTM k Compile.exactOneOneTM
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ Compile.exactOneOneTM_exitPos ∧
      ck.state_idx ≠ Compile.exactOneOneTM_exitNeg ∧
      haltingStateReached Compile.exactOneOneTM ck = false := by
  intro k hk ck hck
  interval_cases k
  · obtain rfl : ck = { state_idx := 0, tapes := [(left, head, right)] } :=
      (Option.some.inj hck).symm
    exact ⟨show (0 : Nat) ≠ 3 by omega, show (0 : Nat) ≠ 2 by omega, rfl⟩
  · have hrun1 : runFlatTM 1 Compile.exactOneOneTM
        { state_idx := 0, tapes := [(left, head, right)] }
          = some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
      show (if haltingStateReached Compile.exactOneOneTM
                { state_idx := 0, tapes := [(left, head, right)] } = true then _
            else match stepFlatTM Compile.exactOneOneTM
                { state_idx := 0, tapes := [(left, head, right)] } with
              | none => _ | some cfg' => runFlatTM 0 Compile.exactOneOneTM cfg') = _
      rw [show haltingStateReached Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
          Compile.exactOneOne_step0_b1 left right head h hget]
      rfl
    rw [hrun1] at hck
    obtain rfl : ck = { state_idx := 1, tapes := [(left, head + 1, right)] } :=
      (Option.some.inj hck).symm
    exact ⟨show (1 : Nat) ≠ 3 by omega, show (1 : Nat) ≠ 2 by omega, rfl⟩

/-- The `testBitInnerTM` symbol bound at the branch seam: any read cell value
`< 4` is below the composed alphabet. -/
private theorem Compile.testBitInner_sym_bound (left rest : List Nat) (head : Nat)
    (hlt : head < (3 :: rest).length) (v0 : Nat) (hv0 : v0 < 4)
    (hget : (3 :: rest).get ⟨head, hlt⟩ = v0) :
    ∀ v, currentTapeSymbol (left, head, (3 : Nat) :: rest) = some v →
      v < max Compile.exactOneOneTM.sig
        (max ClearGadget.justRewindTM.sig ClearGadget.justRewindTM.sig) := by
  intro v hv
  rw [currentTapeSymbol_in_range hlt, hget] at hv
  obtain rfl : v0 = v := Option.some.inj hv
  calc v0 < 4 := hv0
    _ = Compile.exactOneOneTM.sig := Compile.exactOneOneTM_sig.symm
    _ ≤ _ := le_max_left _ _

/-- Inner tester, NEG via first bit `0` (cell `1`): rewinds and exits at
`testBitInner_exitNeg` in `1 + 1 + (head + 1)` steps, tape unchanged. -/
private theorem Compile.testBitInner_run_b0 (left rest : List Nat) (head : Nat)
    (hcell : (3 :: rest)[head]? = some 1)
    (hcells : ∀ i, i < head → ∃ (hh : i < rest.length),
      rest.get ⟨i, hh⟩ < 4 ∧ rest.get ⟨i, hh⟩ ≠ 3) :
    runFlatTM (1 + 1 + (head + 1)) Compile.testBitInnerTM
        { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
      = some { state_idx := Compile.testBitInner_exitNeg,
               tapes := [(left, 0, 3 :: rest)] }
    ∧ ∀ k, k < 1 + 1 + (head + 1) → ∀ ck,
        runFlatTM k Compile.testBitInnerTM
            { state_idx := 0, tapes := [(left, head, 3 :: rest)] } = some ck →
        ck.state_idx ≠ Compile.testBitInner_exitPos ∧
        ck.state_idx ≠ Compile.testBitInner_exitNeg ∧
        haltingStateReached Compile.testBitInnerTM ck = false := by
  have hlt : head < (3 :: rest).length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hcell
    exact absurd hcell (by simp)
  have hget : (3 :: rest).get ⟨head, hlt⟩ = 1 := by
    rw [List.get_eq_getElem]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hcell)
  have hle : head ≤ rest.length := by
    simp only [List.length_cons] at hlt; omega
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
  have hrun1 := Compile.exactOneOne_run_b0 left (3 :: rest) head hlt hget
  have htraj1 := Compile.exactOneOne_traj_one left (3 :: rest) head
  have hrew := ScanLeft.rewindToStart_run 4 3 left rest head hle hcells
  have hrew_traj := ScanLeft.rewindToStart_traj 4 3 left rest head hle hcells
  have hsym := Compile.testBitInner_sym_bound left rest head hlt 1 (by omega) hget
  have hneg := branchComposeFlatTM_run_neg (by decide)
    Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
    ClearGadget.justRewindTM_valid (by decide) (by decide)
    cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left head (3 :: rest) hsym hrun1 htraj1 hrew
    (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
  have hneg_traj := branchComposeFlatTM_no_early_halt_neg (by decide)
    Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
    ClearGadget.justRewindTM_valid (by decide) (by decide)
    cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left head (3 :: rest) hsym hrun1 htraj1
    (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
  refine ⟨hneg.1, ?_⟩
  intro k hk ck hck
  have hh := hneg_traj k hk ck hck
  exact ⟨ClearGadget.ne_of_not_halting Compile.testBitInner_exitPos_is_halt hh,
         ClearGadget.ne_of_not_halting Compile.testBitInner_exitNeg_is_halt hh, hh⟩

/-- Inner tester, two-cell read (`2` then `v`): POS (`v = 0`, register `= [1]`)
or NEG (`v ∈ {1,2}`), rewinding from `head + 1`; `2 + 1 + (head + 1 + 1)` steps. -/
private theorem Compile.testBitInner_run_two (left rest : List Nat) (head : Nat) (v : Nat)
    (hv : v ≤ 2)
    (hcell : (3 :: rest)[head]? = some 2)
    (hcell1 : (3 :: rest)[head + 1]? = some v)
    (hcells : ∀ i, i < head + 1 → ∃ (hh : i < rest.length),
      rest.get ⟨i, hh⟩ < 4 ∧ rest.get ⟨i, hh⟩ ≠ 3) :
    runFlatTM (2 + 1 + (head + 1 + 1)) Compile.testBitInnerTM
        { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
      = some { state_idx := if v = 0 then Compile.testBitInner_exitPos
                            else Compile.testBitInner_exitNeg,
               tapes := [(left, 0, 3 :: rest)] }
    ∧ ∀ k, k < 2 + 1 + (head + 1 + 1) → ∀ ck,
        runFlatTM k Compile.testBitInnerTM
            { state_idx := 0, tapes := [(left, head, 3 :: rest)] } = some ck →
        ck.state_idx ≠ Compile.testBitInner_exitPos ∧
        ck.state_idx ≠ Compile.testBitInner_exitNeg ∧
        haltingStateReached Compile.testBitInnerTM ck = false := by
  have hlt1 : head + 1 < (3 :: rest).length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hcell1
    exact absurd hcell1 (by simp)
  have hlt : head < (3 :: rest).length := by omega
  have hget : (3 :: rest).get ⟨head, hlt⟩ = 2 := by
    rw [List.get_eq_getElem]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hcell)
  have hget1 : (3 :: rest).get ⟨head + 1, hlt1⟩ = v := by
    rw [List.get_eq_getElem]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt1).symm.trans hcell1)
  have hle1 : head + 1 ≤ rest.length := by
    simp only [List.length_cons] at hlt1; omega
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
  have hrun1 := Compile.exactOneOne_run_two left (3 :: rest) head v hv hlt hget hlt1 hget1
  have htraj1 := Compile.exactOneOne_traj_two left (3 :: rest) head hlt hget
  have hrew := ScanLeft.rewindToStart_run 4 3 left rest (head + 1) hle1 hcells
  have hrew_traj := ScanLeft.rewindToStart_traj 4 3 left rest (head + 1) hle1 hcells
  have hsym := Compile.testBitInner_sym_bound left rest (head + 1) hlt1 v (by omega) hget1
  by_cases hv0 : v = 0
  · subst hv0
    rw [if_pos rfl] at hrun1 ⊢
    have hpos := branchComposeFlatTM_run_pos (by decide)
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1 hrew
      (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1
      (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
    refine ⟨hpos.1, ?_⟩
    intro k hk ck hck
    have hh := hpos_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting Compile.testBitInner_exitPos_is_halt hh,
           ClearGadget.ne_of_not_halting Compile.testBitInner_exitNeg_is_halt hh, hh⟩
  · rw [if_neg hv0] at hrun1 ⊢
    have hneg := branchComposeFlatTM_run_neg (by decide)
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1 hrew
      (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg (by decide)
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1
      (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
    refine ⟨hneg.1, ?_⟩
    intro k hk ck hck
    have hh := hneg_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting Compile.testBitInner_exitPos_is_halt hh,
           ClearGadget.ne_of_not_halting Compile.testBitInner_exitNeg_is_halt hh, hh⟩

/-- Interior-cell facts for the tester rewinds: with `encodeTape s ++ res
= 3 :: rest` and `bound + 1 < |encodeTape s|`, every `rest` cell below `bound`
is in range, `< 4` and sentinel-free (it lies strictly inside the encoded
region, left of the trailing terminator). -/
private theorem Compile.testBit_rewind_cells (s : State) (res : List Nat)
    (hbit : Compile.BitState s) (rest : List Nat)
    (hrest : Compile.encodeTape s ++ res = 3 :: rest) (bound : Nat)
    (hbound : bound + 1 < (Compile.encodeTape s).length) :
    ∀ i, i < bound → ∃ (hh : i < rest.length),
      rest.get ⟨i, hh⟩ < 4 ∧ rest.get ⟨i, hh⟩ ≠ 3 := by
  intro i hi
  have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
    have h := congrArg List.length hrest
    simp only [List.length_append, List.length_cons] at h
    omega
  have hh : i < rest.length := by omega
  refine ⟨hh, ?_⟩
  have hi1lt : i + 1 < (Compile.encodeTape s).length := by omega
  have hgetE : rest.get ⟨i, hh⟩ = (Compile.encodeTape s).get ⟨i + 1, hi1lt⟩ := by
    have h1 : (3 :: rest)[i + 1]? = some (rest.get ⟨i, hh⟩) := by
      rw [List.getElem?_cons_succ, List.getElem?_eq_getElem hh, List.get_eq_getElem]
    have h2 : (Compile.encodeTape s ++ res)[i + 1]?
        = some ((Compile.encodeTape s).get ⟨i + 1, hi1lt⟩) := by
      rw [List.getElem?_append_left hi1lt, List.getElem?_eq_getElem hi1lt,
          List.get_eq_getElem]
    rw [hrest] at h2
    exact Option.some.inj (h1.symm.trans h2)
  constructor
  · rw [hgetE]
    exact Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _)
  · rw [hgetE]
    obtain ⟨hi', hne⟩ :=
      Compile.encodeTape_interior_ne_endMark s hbit (i + 1) (by omega) (by omega)
    exact hne

/-- The head-`0` seam symbol of the joined tester is the leading sentinel `3`,
below the raw tester's alphabet. -/
private theorem Compile.testBitRaw_seam_sym (t : Var) (s : State) (res rest : List Nat)
    (hrest : Compile.encodeTape s ++ res = 3 :: rest) :
    ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < (Compile.testBitRawTM t).sig := by
  intro v hv
  rw [hrest] at hv
  rw [show currentTapeSymbol (([] : List Nat), 0, (3 : Nat) :: rest) = some 3 from rfl] at hv
  obtain rfl : (3 : Nat) = v := Option.some.inj hv
  rw [Compile.testBitRawTM_sig]
  omega

/-- **Tester contract — positive (`s.get t = [1]`).** `compileTestBit t` reaches
`exitPos` with the head back at `0` and the tape **unchanged**, visiting neither
exit nor any halt state before; within `3·L + 12` steps. -/
theorem Compile.testBitReg_run_pos (t : Var) (s : State) (res : List Nat)
    (ht : t < s.length) (hbit : Compile.BitState s) (hpos : s.get t = [1]) :
    ∃ T, runFlatTM T (compileTestBit t).M
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := (compileTestBit t).exitPos,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < T → ∀ ck,
        runFlatTM k (compileTestBit t).M
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ (compileTestBit t).exitPos ∧
        ck.state_idx ≠ (compileTestBit t).exitNeg ∧
        haltingStateReached (compileTestBit t).M ck = false)
    ∧ T ≤ 3 * (Compile.encodeTape s ++ res).length + 12 := by
  set skipped := (s.take t).map Compile.shiftReg with hsk
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set tail2 := Compile.encodeRegs (s.drop (t + 1)) ++ [Compile.endMark] ++ res with htail2
  set rest := AppendGadget.regBlocks skipped ++ 2 :: 0 :: tail2 with hrest_def
  have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
    have hsplit := Compile.encodeTape_split s t ht
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get t) = [2] := by rw [hpos]; rfl
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htail2]
    simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
  -- cell facts at H and H + 1.
  have hcell : (3 :: rest)[H]? = some 2 := by
    rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
          = (AppendGadget.regBlocks skipped).length + 1 from by omega,
        List.getElem?_cons_succ, hrest_def,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hcell1 : (3 :: rest)[H + 1]? = some 0 := by
    rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length + 1
          = ((AppendGadget.regBlocks skipped).length + 1) + 1 from by omega,
        List.getElem?_cons_succ, hrest_def,
        List.getElem?_append_right (Nat.le_succ_of_le (Nat.le_refl _)),
        show (AppendGadget.regBlocks skipped).length + 1
          - (AppendGadget.regBlocks skipped).length = 1 from by omega]
    rfl
  -- length bookkeeping.
  have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
    have h := congrArg List.length hdecomp
    simp only [List.length_append, List.length_cons] at h
    omega
  have hrest_len : rest.length
      = (AppendGadget.regBlocks skipped).length + 2 + tail2.length := by
    rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
  have htail2_len : tail2.length
      = (Compile.encodeRegs (s.drop (t + 1))).length + 1 + res.length := by
    rw [htail2]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hbound : H + 2 < (Compile.encodeTape s).length := by omega
  have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp (H + 1) (by omega)
  -- inner tester run (POS: cell 2 then block-end 0).
  have hinner := Compile.testBitInner_run_two [] rest H 0 (by omega) hcell hcell1 hcells
  rw [if_pos rfl] at hinner
  rw [← hdecomp] at hinner
  -- navtest run + trajectory.
  have hne_t : s.get t ≠ [] := by rw [hpos]; simp
  have hnav_run := Compile.navTestReg_run_content s t res ht hbit hne_t
  have hnav_traj := Compile.navTestReg_traj_content s t res ht hbit hne_t
  rw [← hsk, ← hHdef] at hnav_run
  rw [← hsk] at hnav_traj
  -- the outer branch composition.
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content t
      ≠ ClearGadget.navigateAndTestTM_exit_delim t := by
    show (ClearGadget.navigateToRegTM t).states + 1 ≠ (ClearGadget.navigateToRegTM t).states + 2
    omega
  have hHlt : H < (Compile.encodeTape s ++ res).length := by
    rw [hdecomp]; simp only [List.length_cons]; omega
  have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 2 := by
    rw [List.get_eq_getElem]
    have h2 : (Compile.encodeTape s ++ res)[H]? = some 2 := by rw [hdecomp]; exact hcell
    exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
  have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
      v < max (ClearGadget.navigateAndTestTM t).sig
        (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    obtain rfl : (2 : Nat) = v := Option.some.inj hv
    calc (2 : Nat) < 4 := by omega
      _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
      _ ≤ _ := le_max_left _ _
  have hpos' := branchComposeFlatTM_run_pos hexit_neq
    (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt t)
    (ClearGadget.navigateAndTestTM_exit_delim_lt t)
    cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
      rw [ClearGadget.navigateAndTestTM_states]; omega)
    [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hinner.1
    (Compile.haltingStateReached_of_halt Compile.testBitInner_exitPos_is_halt)
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt t)
    (ClearGadget.navigateAndTestTM_exit_delim_lt t)
    cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
      rw [ClearGadget.navigateAndTestTM_states]; omega)
    [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
    (fun k' hk' ck' hck' => (hinner.2 k' hk' ck' hck').2.2)
  have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
      Compile.testBitInnerTM ClearGadget.justRewindTM
      (ClearGadget.navigateAndTestTM_exit_content t)
      (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
  have hstate_eq : Compile.testBitInner_exitPos + (ClearGadget.navigateAndTestTM t).states
      = Compile.testBitRaw_exitPos t := by
    rw [Compile.testBitRaw_exitPos]; omega
  rw [hstate_eq, hraweq] at hpos'
  rw [hraweq] at hpos_traj
  -- join transport: the run never visits the demoted delim leaf.
  set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (2 + 1 + (H + 1 + 1)) with hTdef
  have hne12 : ∀ k, k ≤ T → ∀ ck, runFlatTM k (Compile.testBitRawTM t) cfg0 = some ck →
      ck.state_idx ≠ Compile.testBitRaw_exitNegDelim t := by
    intro k hk ck hck
    rcases Nat.lt_or_ge k T with hlt | hge
    · exact ClearGadget.ne_of_not_halting (Compile.testBitRaw_exitNegDelim_is_halt t)
        (hpos_traj k hlt ck hck)
    · have hkT : k = T := by omega
      subst hkT
      rw [hpos'.1] at hck
      obtain rfl := (Option.some.inj hck).symm
      show Compile.testBitRaw_exitPos t ≠ Compile.testBitRaw_exitNegDelim t
      rw [Compile.testBitRaw_exitPos, Compile.testBitRaw_exitNegDelim,
          Compile.testBitInnerTM_states]
      have h5 : Compile.testBitInner_exitPos = 5 := rfl
      have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
      omega
  refine ⟨T, ?_, ?_, ?_⟩
  · show runFlatTM T (Compile.joinTwoHalts (Compile.testBitRawTM t)
        (Compile.testBitRaw_exitNeg t) (Compile.testBitRaw_exitNegDelim t)) cfg0 = _
    rw [Compile.joinTwoHalts_run_eq _ _ _ T cfg0 hne12]
    exact hpos'.1
  · intro k hk ck hck
    have hck' : runFlatTM k (Compile.testBitRawTM t) cfg0 = some ck := by
      rw [← Compile.joinTwoHalts_run_eq (Compile.testBitRawTM t)
          (Compile.testBitRaw_exitNeg t) (Compile.testBitRaw_exitNegDelim t) k cfg0
          (fun j hj cj hcj => hne12 j (by omega) cj hcj)]
      exact hck
    have hnh := hpos_traj k hk ck hck'
    exact ⟨ClearGadget.ne_of_not_halting (Compile.testBitRaw_exitPos_is_halt t) hnh,
           ClearGadget.ne_of_not_halting (Compile.testBitRaw_exitNeg_is_halt t) hnh,
           Compile.joinTwoHalts_halting_false _ _ _ ck hnh⟩
  · have hnavle := ClearGadget.navSteps_le skipped
    have hLlen : (Compile.encodeTape s).length ≤ (Compile.encodeTape s ++ res).length := by
      rw [List.length_append]; omega
    omega

/-- Join transport for runs ending at the raw tester's kept NEG exit (`h1`):
the joined tester reproduces the run; the trajectory avoids both exits. -/
private theorem Compile.testBit_join_kept_neg (t : Var) (cfg0 : FlatTMConfig)
    (tape : List Nat) (T : Nat)
    (hraw : runFlatTM T (Compile.testBitRawTM t) cfg0
      = some { state_idx := Compile.testBitRaw_exitNeg t, tapes := [([], 0, tape)] })
    (htraj : ∀ k, k < T → ∀ ck, runFlatTM k (Compile.testBitRawTM t) cfg0 = some ck →
      haltingStateReached (Compile.testBitRawTM t) ck = false) :
    runFlatTM T (compileTestBit t).M cfg0
      = some { state_idx := (compileTestBit t).exitNeg, tapes := [([], 0, tape)] }
    ∧ (∀ k, k < T → ∀ ck, runFlatTM k (compileTestBit t).M cfg0 = some ck →
        ck.state_idx ≠ (compileTestBit t).exitPos ∧
        ck.state_idx ≠ (compileTestBit t).exitNeg ∧
        haltingStateReached (compileTestBit t).M ck = false) := by
  obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept
    (Compile.testBitRawTM t) (Compile.testBitRaw_exitNeg t)
    (Compile.testBitRaw_exitNegDelim t) cfg0 T ([], 0, tape) hraw htraj
    (Compile.testBitRaw_exitNeg_is_halt t) (Compile.testBitRaw_exitNegDelim_is_halt t)
  refine ⟨hjoin, ?_⟩
  intro k hk ck hck
  obtain ⟨hne1, hnh⟩ := hjoin_traj k hk ck hck
  exact ⟨ClearGadget.ne_of_not_halting (compileTestBit_exitPos_is_halt t) hnh, hne1, hnh⟩

/-- **Tester contract — negative (`s.get t ≠ [1]`).** `compileTestBit t` reaches
`exitNeg` with the head back at `0` and the tape **unchanged**, visiting neither
exit nor any halt state before; within `3·L + 12` steps. Three internal cases:
register empty (delim leaf), first bit `0`, or `≥ 2` bits. -/
theorem Compile.testBitReg_run_neg (t : Var) (s : State) (res : List Nat)
    (ht : t < s.length) (hbit : Compile.BitState s) (hneg : s.get t ≠ [1]) :
    ∃ T, runFlatTM T (compileTestBit t).M
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := (compileTestBit t).exitNeg,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < T → ∀ ck,
        runFlatTM k (compileTestBit t).M
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ (compileTestBit t).exitPos ∧
        ck.state_idx ≠ (compileTestBit t).exitNeg ∧
        haltingStateReached (compileTestBit t).M ck = false)
    ∧ T ≤ 3 * (Compile.encodeTape s ++ res).length + 12 := by
  set skipped := (s.take t).map Compile.shiftReg with hsk
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set tail2 := Compile.encodeRegs (s.drop (t + 1)) ++ [Compile.endMark] ++ res with htail2
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have htail2_len : tail2.length
      = (Compile.encodeRegs (s.drop (t + 1))).length + 1 + res.length := by
    rw [htail2]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content t
      ≠ ClearGadget.navigateAndTestTM_exit_delim t := by
    show (ClearGadget.navigateToRegTM t).states + 1 ≠ (ClearGadget.navigateToRegTM t).states + 2
    omega
  have hnavle := ClearGadget.navSteps_le skipped
  have hLlen : (Compile.encodeTape s).length ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append]; omega
  rcases hsgt : s.get t with _ | ⟨b, r⟩
  · -- Case A: register empty — the delim leaf (demoted), bridged to exitNeg.
    set rest := AppendGadget.regBlocks skipped ++ 0 :: tail2 with hrest_def
    have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
      have hsplit := Compile.encodeTape_split s t ht
      rw [← hsk] at hsplit
      have hsr : Compile.shiftReg (s.get t) = [] := by rw [hsgt]; rfl
      rw [hsr, List.append_nil] at hsplit
      rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htail2]
      simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
    have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
      have h := congrArg List.length hdecomp
      simp only [List.length_append, List.length_cons] at h
      omega
    have hrest_len : rest.length
        = (AppendGadget.regBlocks skipped).length + 1 + tail2.length := by
      rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
    have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp H (by omega)
    have hHle : H ≤ rest.length := by omega
    have hrew := ScanLeft.rewindToStart_run 4 3 [] rest H hHle hcells
    have hrew_traj := ScanLeft.rewindToStart_traj 4 3 [] rest H hHle hcells
    rw [← hdecomp] at hrew hrew_traj
    have hnav_run := Compile.navTestReg_run_delim s t res ht hbit hsgt
    have hnav_traj := Compile.navTestReg_traj_delim s t res ht hbit hsgt
    rw [← hsk, ← hHdef] at hnav_run
    rw [← hsk] at hnav_traj
    have hHlt : H < (Compile.encodeTape s ++ res).length := by
      rw [hdecomp]; simp only [List.length_cons]; omega
    have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 0 := by
      rw [List.get_eq_getElem]
      have h2 : (Compile.encodeTape s ++ res)[H]? = some 0 := by
        rw [hdecomp, hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
              = (AppendGadget.regBlocks skipped).length + 1 from by omega,
            List.getElem?_cons_succ, hrest_def,
            List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
    have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
        v < max (ClearGadget.navigateAndTestTM t).sig
          (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
      intro v hv
      rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
      obtain rfl : (0 : Nat) = v := Option.some.inj hv
      calc (0 : Nat) < 4 := by omega
        _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
        _ ≤ _ := le_max_left _ _
    have hneg' := branchComposeFlatTM_run_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt t)
      (ClearGadget.navigateAndTestTM_exit_delim_lt t)
      cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
        rw [ClearGadget.navigateAndTestTM_states]; omega)
      [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hrew
      (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt t)
      (ClearGadget.navigateAndTestTM_exit_delim_lt t)
      cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
        rw [ClearGadget.navigateAndTestTM_states]; omega)
      [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
      (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
    have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
        Compile.testBitInnerTM ClearGadget.justRewindTM
        (ClearGadget.navigateAndTestTM_exit_content t)
        (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
    have hstate_eq : (1 : Nat) + ((ClearGadget.navigateAndTestTM t).states
          + Compile.testBitInnerTM.states) = Compile.testBitRaw_exitNegDelim t := by
      rw [Compile.testBitRaw_exitNegDelim]
      have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
      omega
    rw [hstate_eq, hraweq] at hneg'
    rw [hraweq] at hneg_traj
    set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (H + 1) with hTdef
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted
      (Compile.testBitRawTM t) (Compile.testBitRaw_exitNeg t)
      (Compile.testBitRaw_exitNegDelim t) cfg0 T [] (Compile.encodeTape s ++ res) 0
      hneg'.1 (fun k hk ck hck => hneg_traj k hk ck hck)
      (Compile.testBitRaw_exitNeg_is_halt t) (Compile.testBitRaw_exitNegDelim_is_halt t)
      (by rw [Compile.testBitRaw_exitNeg, Compile.testBitRaw_exitNegDelim,
              Compile.testBitInnerTM_states]
          have h8 : Compile.testBitInner_exitNeg = 8 := rfl
          have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
          omega)
      (Compile.testBitRaw_seam_sym t s res rest hdecomp)
    refine ⟨T + 1, hjoin, ?_, ?_⟩
    · intro k hk ck hck
      obtain ⟨hne1, hnh⟩ := hjoin_traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting (compileTestBit_exitPos_is_halt t) hnh, hne1, hnh⟩
    · omega
  · -- register nonempty: first bit `b ≤ 1`.
    have hb1 : b ≤ 1 := by
      have hmem : s.get t ∈ s := by
        rw [State.get, List.getElem?_eq_getElem ht]; exact List.getElem_mem ht
      exact hbit _ hmem b (by simp [hsgt])
    have hne_t : s.get t ≠ [] := by rw [hsgt]; simp
    have hnav_run := Compile.navTestReg_run_content s t res ht hbit hne_t
    have hnav_traj := Compile.navTestReg_traj_content s t res ht hbit hne_t
    rw [← hsk, ← hHdef] at hnav_run
    rw [← hsk] at hnav_traj
    rcases hb : b with _ | b'
    · -- Case B: first bit `0` — NEG after one read.
      subst hb
      set tailp := Compile.shiftReg r ++ 0 :: tail2 with htailp
      set rest := AppendGadget.regBlocks skipped ++ 1 :: tailp with hrest_def
      have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
        have hsplit := Compile.encodeTape_split s t ht
        rw [← hsk] at hsplit
        have hsr : Compile.shiftReg (s.get t) = 1 :: Compile.shiftReg r := by
          rw [hsgt]; rfl
        rw [hsr] at hsplit
        rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htailp, htail2]
        simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
      have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
        have h := congrArg List.length hdecomp
        simp only [List.length_append, List.length_cons] at h
        omega
      have hrest_len : rest.length
          = (AppendGadget.regBlocks skipped).length + 1 + tailp.length := by
        rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
      have htailp_len : tailp.length = r.length + 1 + tail2.length := by
        rw [htailp]
        simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map]
        omega
      have hcell : (3 :: rest)[H]? = some 1 := by
        rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
              = (AppendGadget.regBlocks skipped).length + 1 from by omega,
            List.getElem?_cons_succ, hrest_def,
            List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp H (by omega)
      have hinner := Compile.testBitInner_run_b0 [] rest H hcell hcells
      rw [← hdecomp] at hinner
      have hHlt : H < (Compile.encodeTape s ++ res).length := by
        rw [hdecomp]; simp only [List.length_cons]; omega
      have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 1 := by
        rw [List.get_eq_getElem]
        have h2 : (Compile.encodeTape s ++ res)[H]? = some 1 := by rw [hdecomp]; exact hcell
        exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
      have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
          v < max (ClearGadget.navigateAndTestTM t).sig
            (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
        intro v hv
        rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
        obtain rfl : (1 : Nat) = v := Option.some.inj hv
        calc (1 : Nat) < 4 := by omega
          _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
          _ ≤ _ := le_max_left _ _
      have hpos' := branchComposeFlatTM_run_pos hexit_neq
        (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
        ClearGadget.justRewindTM_valid
        (ClearGadget.navigateAndTestTM_exit_content_lt t)
        (ClearGadget.navigateAndTestTM_exit_delim_lt t)
        cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
          rw [ClearGadget.navigateAndTestTM_states]; omega)
        [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hinner.1
        (Compile.haltingStateReached_of_halt Compile.testBitInner_exitNeg_is_halt)
      have hpos_traj := branchComposeFlatTM_no_early_halt_pos
        (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
        ClearGadget.justRewindTM_valid
        (ClearGadget.navigateAndTestTM_exit_content_lt t)
        (ClearGadget.navigateAndTestTM_exit_delim_lt t)
        cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
          rw [ClearGadget.navigateAndTestTM_states]; omega)
        [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
        (fun k' hk' ck' hck' => (hinner.2 k' hk' ck' hck').2.2)
      have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
          Compile.testBitInnerTM ClearGadget.justRewindTM
          (ClearGadget.navigateAndTestTM_exit_content t)
          (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
      have hstate_eq : Compile.testBitInner_exitNeg + (ClearGadget.navigateAndTestTM t).states
          = Compile.testBitRaw_exitNeg t := by
        rw [Compile.testBitRaw_exitNeg]; omega
      rw [hstate_eq, hraweq] at hpos'
      rw [hraweq] at hpos_traj
      set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (1 + 1 + (H + 1)) with hTdef
      obtain ⟨hjoin, hjoin_traj⟩ := Compile.testBit_join_kept_neg t cfg0
        (Compile.encodeTape s ++ res) T hpos'.1
        (fun k hk ck hck => hpos_traj k hk ck hck)
      exact ⟨T, hjoin, hjoin_traj, by omega⟩
    · -- Case C: first bit `1` and a second cell — NEG after two reads.
      subst hb
      rcases r with _ | ⟨c, r'⟩
      · -- register is exactly `[1]` — contradicts `hneg`.
        exfalso
        have hb'0 : b' = 0 := by omega
        subst hb'0
        exact hneg hsgt
      · have hb'0 : b' = 0 := by omega
        subst hb'0
        have hc1 : c ≤ 1 := by
          have hmem : s.get t ∈ s := by
            rw [State.get, List.getElem?_eq_getElem ht]; exact List.getElem_mem ht
          exact hbit _ hmem c (by simp [hsgt])
        set tailpp := Compile.shiftReg r' ++ 0 :: tail2 with htailpp
        set rest := AppendGadget.regBlocks skipped ++ 2 :: (c + 1) :: tailpp with hrest_def
        have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
          have hsplit := Compile.encodeTape_split s t ht
          rw [← hsk] at hsplit
          have hsr : Compile.shiftReg (s.get t) = 2 :: (c + 1) :: Compile.shiftReg r' := by
            rw [hsgt]; rfl
          rw [hsr] at hsplit
          rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htailpp, htail2]
          simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
        have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
          have h := congrArg List.length hdecomp
          simp only [List.length_append, List.length_cons] at h
          omega
        have hrest_len : rest.length
            = (AppendGadget.regBlocks skipped).length + 2 + tailpp.length := by
          rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
        have htailpp_len : tailpp.length = r'.length + 1 + tail2.length := by
          rw [htailpp]
          simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map]
          omega
        have hcell : (3 :: rest)[H]? = some 2 := by
          rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
                = (AppendGadget.regBlocks skipped).length + 1 from by omega,
              List.getElem?_cons_succ, hrest_def,
              List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        have hcell1 : (3 :: rest)[H + 1]? = some (c + 1) := by
          rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length + 1
                = ((AppendGadget.regBlocks skipped).length + 1) + 1 from by omega,
              List.getElem?_cons_succ, hrest_def,
              List.getElem?_append_right (Nat.le_succ_of_le (Nat.le_refl _)),
              show (AppendGadget.regBlocks skipped).length + 1
                - (AppendGadget.regBlocks skipped).length = 1 from by omega]
          rfl
        have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp (H + 1) (by omega)
        have hinner := Compile.testBitInner_run_two [] rest H (c + 1) (by omega)
          hcell hcell1 hcells
        rw [if_neg (by omega)] at hinner
        rw [← hdecomp] at hinner
        have hHlt : H < (Compile.encodeTape s ++ res).length := by
          rw [hdecomp]; simp only [List.length_cons]; omega
        have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 2 := by
          rw [List.get_eq_getElem]
          have h2 : (Compile.encodeTape s ++ res)[H]? = some 2 := by rw [hdecomp]; exact hcell
          exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
        have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
            v < max (ClearGadget.navigateAndTestTM t).sig
              (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
          intro v hv
          rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
          obtain rfl : (2 : Nat) = v := Option.some.inj hv
          calc (2 : Nat) < 4 := by omega
            _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
            _ ≤ _ := le_max_left _ _
        have hpos' := branchComposeFlatTM_run_pos hexit_neq
          (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
          ClearGadget.justRewindTM_valid
          (ClearGadget.navigateAndTestTM_exit_content_lt t)
          (ClearGadget.navigateAndTestTM_exit_delim_lt t)
          cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
            rw [ClearGadget.navigateAndTestTM_states]; omega)
          [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hinner.1
          (Compile.haltingStateReached_of_halt Compile.testBitInner_exitNeg_is_halt)
        have hpos_traj := branchComposeFlatTM_no_early_halt_pos
          (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
          ClearGadget.justRewindTM_valid
          (ClearGadget.navigateAndTestTM_exit_content_lt t)
          (ClearGadget.navigateAndTestTM_exit_delim_lt t)
          cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
            rw [ClearGadget.navigateAndTestTM_states]; omega)
          [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
          (fun k' hk' ck' hck' => (hinner.2 k' hk' ck' hck').2.2)
        have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
            Compile.testBitInnerTM ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content t)
            (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
        have hstate_eq : Compile.testBitInner_exitNeg + (ClearGadget.navigateAndTestTM t).states
            = Compile.testBitRaw_exitNeg t := by
          rw [Compile.testBitRaw_exitNeg]; omega
        rw [hstate_eq, hraweq] at hpos'
        rw [hraweq] at hpos_traj
        set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (2 + 1 + (H + 1 + 1)) with hTdef
        obtain ⟨hjoin, hjoin_traj⟩ := Compile.testBit_join_kept_neg t cfg0
          (Compile.encodeTape s ++ res) T hpos'.1
          (fun k hk ck hck => hpos_traj k hk ck hck)
        exact ⟨T, hjoin, hjoin_traj, by omega⟩

theorem Compile.moveContentExit0_lt (dst : Nat) :
    Compile.moveContentExit0 dst < (Compile.moveContentRawTM dst).states := by
  rw [Compile.moveContentExit0, Compile.moveContentRawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM2_exit_lt 0 dst; omega

theorem Compile.moveContentExit1_lt (dst : Nat) :
    Compile.moveContentExit1 dst < (Compile.moveContentRawTM dst).states := by
  rw [Compile.moveContentExit1, Compile.moveContentRawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM2_exit_lt 1 dst; omega

theorem Compile.moveContentTM_valid (dst : Nat) : validFlatTM (Compile.moveContentTM dst) :=
  joinTwoHalts_valid _ _ _ (Compile.moveContentRawTM_valid dst)
    (Compile.moveContentExit0_lt dst) (Compile.moveContentExit1_lt dst)
    (Compile.moveContentRawTM_tapes dst)

theorem Compile.moveContentTM_sig (dst : Nat) : (Compile.moveContentTM dst).sig = 4 := by
  rw [Compile.moveContentTM, joinTwoHalts_sig]; exact Compile.moveContentRawTM_sig dst

theorem Compile.moveContentTM_exit0_is_halt (dst : Nat) :
    (Compile.moveContentTM dst).halt[Compile.moveContentExit0 dst]? = some true :=
  joinTwoHalts_h1_is_halt _ _ _ (Compile.moveContentExit0_ne_exit1 dst)
    (Compile.moveContentExit0_is_halt dst)

theorem Compile.moveContentExit0_lt_states (dst : Nat) :
    Compile.moveContentExit0 dst < (Compile.moveContentTM dst).states := by
  rw [Compile.moveContentTM, joinTwoHalts_states]; exact Compile.moveContentExit0_lt dst

theorem Compile.moveBodyRawTM_valid (src dst : Nat) : validFlatTM (Compile.moveBodyRawTM src dst) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.navigateAndTestTM_valid src)
    (Compile.moveContentTM_valid dst) ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    (ClearGadget.navigateAndTestTM_tapes src) (Compile.moveContentTM_tapes dst)
    ClearGadget.justRewindTM_tapes

theorem Compile.moveBodyRawTM_exitLoop_is_halt (src dst : Nat) :
    (Compile.moveBodyRawTM src dst).halt[Compile.moveBodyRawTM_exitLoop src dst]? = some true := by
  rw [Compile.moveBodyRawTM_exitLoop, Compile.moveBodyRawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveContentTM_valid dst) (Compile.moveContentExit0_lt_states dst)
    (Compile.moveContentTM_exit0_is_halt dst)

theorem Compile.moveBodyRawTM_exitDone_is_halt (src dst : Nat) :
    (Compile.moveBodyRawTM src dst).halt[Compile.moveBodyRawTM_exitDone src dst]? = some true := by
  rw [Compile.moveBodyRawTM_exitDone, Compile.moveBodyRawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveContentTM_valid dst)
    (show ClearGadget.justRewindTM.halt[ClearGadget.justRewindTM_exit]? = some true from rfl)

theorem Compile.moveBodyRawTM_exitLoop_lt (src dst : Nat) :
    Compile.moveBodyRawTM_exitLoop src dst < (Compile.moveBodyRawTM src dst).states := by
  rw [Compile.moveBodyRawTM_exitLoop, Compile.moveBodyRawTM, branchComposeFlatTM_states]
  have := Compile.moveContentExit0_lt_states dst; omega

theorem Compile.moveBodyRawTM_exitDone_lt (src dst : Nat) :
    Compile.moveBodyRawTM_exitDone src dst < (Compile.moveBodyRawTM src dst).states := by
  rw [Compile.moveBodyRawTM_exitDone, Compile.moveBodyRawTM, branchComposeFlatTM_states]
  show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
      + ClearGadget.justRewindTM_exit
    < (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
      + ClearGadget.justRewindTM.states
  show _ + _ + 1 < _ + _ + 3; omega

theorem Compile.moveBodyRawTM_exitDone_ne_exitLoop (src dst : Nat) :
    Compile.moveBodyRawTM_exitDone src dst ≠ Compile.moveBodyRawTM_exitLoop src dst := by
  rw [Compile.moveBodyRawTM_exitDone, Compile.moveBodyRawTM_exitLoop]
  have := Compile.moveContentExit0_lt_states dst; omega

/-- **Validity of `moveRegionTM`.** Mirrors `clearRegionTM_valid`: a `loopTM` over
the valid `moveBodyRawTM` body with both exits in range and single-tape. Needed to
wire `moveRegionTM` into `composeFlatTM`/`branchComposeFlatTM` when assembling the
cross-register ops. -/
theorem Compile.moveRegionTM_valid (src dst : Nat) :
    validFlatTM (Compile.moveRegionTM src dst) :=
  loopTM_valid (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)
    (Compile.moveBodyRawTM_valid src dst)
    (Compile.moveBodyRawTM_exitDone_lt src dst) (Compile.moveBodyRawTM_exitLoop_lt src dst)
    (Compile.moveBodyRawTM_tapes src dst)

/-- The compiled-machine alphabet of `moveRegionTM` is the fixed `sig = 4`. -/
theorem Compile.moveRegionTM_sig (src dst : Nat) : (Compile.moveRegionTM src dst).sig = 4 := by
  rw [Compile.moveRegionTM, loopTM_sig]
  show (Compile.moveBodyRawTM src dst).sig = 4
  show (branchComposeFlatTM _ _ _ _ _).sig = 4
  rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig]
  show max 4 (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) = 4
  rw [Compile.moveContentTM_sig dst]
  rfl

/-! ### The dual-target *duplicating* move gadget `moveRegion2TM` (Risk C2)

`moveRegion2TM src dst1 dst2` transfers `src`'s content (FIFO, one bit/iter) to the
**end of BOTH** `dst1` and `dst2`, emptying `src`. It is the duplicating primitive
the `copy`/`tail`/`concat` ops need — a single-target move (`moveRegionTM`) cannot
duplicate data (the number of copies is invariant). The structure mirrors
`moveRegionTM` exactly; the content branch appends the read bit to **two** registers
instead of one (`moveBitM3TM = moveBitM2TM b dst1 ⨾ appendAtThenTwoPhaseRewind(b+1, dst2)`).
A TM-`#eval` probe confirms the dual-append body yields the exact `encodeTape`
(head→`0`, clean halt). Only the structural scaffolding (validity/halts) is built
here; the run lemma `moveRegion2TM_run` mirrors `moveRegionTM_run` (a three-register
coupled invariant) and is the next step. -/

/-- Single-bit dual-transfer engine for a fixed bit `b`: run `moveBitM2TM` (delete
`src`'s front, append `b+1` to `dst1`, rewind), then append `b+1` to `dst2` and
two-phase-rewind. -/
def Compile.moveBitM3TM (b dst1 dst2 : Nat) : FlatTM :=
  composeFlatTM (Compile.moveBitM2TM b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1)

/-- The surviving (found) exit of `moveBitM3TM` (b-independent: `moveBitM2TM`'s state
count and `appendAtTM`'s are both b-independent). -/
def Compile.moveBitM3_exit (dst1 dst2 : Nat) : Nat :=
  (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 6)

/-- `moveBitM2TM`'s state count does not depend on the bit `b`. -/
theorem Compile.moveBitM2TM_states_eq (b dst : Nat) :
    (Compile.moveBitM2TM b dst).states = (Compile.moveBitM2TM 0 dst).states := by
  show (composeFlatTM ClearGadget.stepDeleteRewindRawTM
        (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
        ClearGadget.stepDeleteRewindTM_exit).states
      = (composeFlatTM ClearGadget.stepDeleteRewindRawTM
        (AppendGadget.appendAtThenTwoPhaseRewindTM (0 + 1) dst)
        ClearGadget.stepDeleteRewindTM_exit).states
  rw [composeFlatTM_states, composeFlatTM_states,
      AppendGadget.appendAtThenTwoPhaseRewindTM_states,
      AppendGadget.appendAtThenTwoPhaseRewindTM_states,
      Compile.appendAtTM_states_eq (b + 1) dst, Compile.appendAtTM_states_eq (0 + 1) dst]

theorem Compile.moveBitM3TM_tapes (b dst1 dst2 : Nat) :
    (Compile.moveBitM3TM b dst1 dst2).tapes = 1 := by
  rw [Compile.moveBitM3TM, composeFlatTM_tapes]; exact Compile.moveBitM2TM_tapes b dst1

theorem Compile.moveBitM3TM_sig (b dst1 dst2 : Nat) :
    (Compile.moveBitM3TM b dst1 dst2).sig = 4 := by
  rw [Compile.moveBitM3TM, composeFlatTM_sig, Compile.moveBitM2TM_sig,
      AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl

theorem Compile.moveBitM3TM_valid (b dst1 dst2 : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.moveBitM3TM b dst1 dst2) :=
  composeFlatTM_valid (Compile.moveBitM2TM b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1)
    (Compile.moveBitM2TM_valid b dst1 hb)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst2)
    (Compile.moveBitM2_exit_lt b dst1)
    (Compile.moveBitM2TM_tapes b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_tapes (b + 1) dst2)

theorem Compile.moveBitM3_exit_is_halt (b dst1 dst2 : Nat) :
    (Compile.moveBitM3TM b dst1 dst2).halt[Compile.moveBitM3_exit dst1 dst2]? = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro (Compile.moveBitM2TM b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1)
    ((AppendGadget.appendAtTM (b + 1) dst2).states + 6)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst2)
  rw [Compile.appendAtTM_states_eq (b + 1) dst2, Compile.moveBitM2TM_states_eq b dst1] at h
  exact h

theorem Compile.moveBitM3_exit_lt (b dst1 dst2 : Nat) :
    Compile.moveBitM3_exit dst1 dst2 < (Compile.moveBitM3TM b dst1 dst2).states := by
  rw [Compile.moveBitM3TM, composeFlatTM_states, Compile.moveBitM2TM_states_eq b dst1,
      AppendGadget.appendAtThenTwoPhaseRewindTM_states, Compile.appendAtTM_states_eq (b + 1) dst2,
      show (ScanLeft.rewindTwoPhaseTM 4 3).states = 8 from rfl]
  show (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 6)
      < (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 8)
  omega

/-- **The single-bit DUAL-transfer engine run (Risk C2).** From `src`'s content
start with front bit `b` (`s.get src = b :: cs`), `moveBitM3TM b dst1 dst2` deletes
`src`'s front cell, appends `b` to the end of **both** `dst1` and `dst2`, and
two-phase-rewinds, landing at `moveBitM3_exit` with the tape
`encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
  ++ (res ++ [0])` and head `0`. Composes `moveBitM2_run` (delete + append to `dst1`)
with `appendBitTwoPhase_run` (append to `dst2`). -/
theorem Compile.moveBitM3_run (s : State) (src dst1 dst2 : Var) (b : Nat) (cs : List Nat)
    (hb : b ≤ 1) (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2) (hd12 : dst1 ≠ dst2)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (hbit : Compile.BitState s) (hcons : s.get src = b :: cs) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBitM3TM b dst1 dst2)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBitM3_exit dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBitM3TM b dst1 dst2)
            { state_idx := 0,
              tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.moveBitM3TM b dst1 dst2) ck = false)
    ∧ t ≤ 10 * (Compile.encodeTape s ++ res).length + 30 := by
  -- Phase A: moveBitM2TM b dst1 (delete src front, append b to dst1).
  obtain ⟨tA, hA, hA_traj, hA_bud⟩ :=
    Compile.moveBitM2_run s src dst1 b cs hb hsd1 hsrc hdst1 hbit hcons res hres
  -- Phase B ingredients (on `mid`, appending b to dst2).
  have hbitA : Compile.BitState (s.set src cs) := by
    have := Compile.BitState_set_tail s src hbit hsrc
    rwa [show (s.get src).tail = cs from by rw [hcons, List.tail_cons]] at this
  have hgd1 : (s.set src cs).get dst1 = s.get dst1 :=
    Compile.get_set_ne s src cs dst1 hsrc (Ne.symm hsd1)
  have hdst1A : dst1 < (s.set src cs).length := by
    rw [Compile.length_set s src cs hsrc]; exact hdst1
  have hbitmid : Compile.BitState ((s.set src cs).set dst1 (s.get dst1 ++ [b])) := by
    refine Compile.BitState_set _ dst1 _ hbitA hdst1A ?_
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.BitState_get _ dst1 hbitA hdst1A x (by rw [hgd1]; exact hx)
    · simp only [List.mem_singleton] at hx; subst hx; omega
  have hdst2mid : dst2 < ((s.set src cs).set dst1 (s.get dst1 ++ [b])).length := by
    rw [Compile.length_set _ dst1 _ hdst1A, Compile.length_set s src cs hsrc]; exact hdst2
  have hgd2 : ((s.set src cs).set dst1 (s.get dst1 ++ [b])).get dst2 = s.get dst2 := by
    rw [Compile.get_set_ne (s.set src cs) dst1 (s.get dst1 ++ [b]) dst2 hdst1A (Ne.symm hd12),
        Compile.get_set_ne s src cs dst2 hsrc (Ne.symm hsd2)]
  have hres1 : Compile.ValidResidue (res ++ [0]) := by
    apply Compile.ValidResidue_append _ _ hres; intro x hx
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  obtain ⟨tB, hB, hB_traj, hB_bud⟩ :=
    Compile.appendBitTwoPhase_run b hb ((s.set src cs).set dst1 (s.get dst1 ++ [b])) dst2
      hbitmid hdst2mid (res ++ [0]) hres1
  rw [hgd2] at hB
  -- length: phase A's exit tape is one cell longer than the input tape.
  have hmidlen : (Compile.encodeTape ((s.set src cs).set dst1 (s.get dst1 ++ [b])) ++ (res ++ [0])).length
      = (Compile.encodeTape s ++ res).length + 1 := by
    have e1 := Compile.encodeTape_set_length s src cs hsrc
    have e2 := Compile.encodeTape_set_length (s.set src cs) dst1 (s.get dst1 ++ [b]) hdst1A
    rw [hgd1] at e2
    rw [hcons] at e1
    simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at e1 e2 ⊢
    omega
  -- compose: moveBitM2TM b dst1 ⨾ appendAtThenTwoPhaseRewindTM (b+1) dst2.
  set right₁ : List Nat :=
    Compile.encodeTape ((s.set src cs).set dst1 (s.get dst1 ++ [b])) ++ (res ++ [0]) with hr1
  have hvalid1 : validFlatTM (Compile.moveBitM2TM b dst1) := Compile.moveBitM2TM_valid b dst1 hb
  have hvalid2 : validFlatTM (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) :=
    AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst2
  have hexit_lt : Compile.moveBitM2_exit dst1 < (Compile.moveBitM2TM b dst1).states :=
    Compile.moveBitM2_exit_lt b dst1
  have hcfg0lt : (0 : Nat) < (Compile.moveBitM2TM b dst1).states := by
    have := Compile.moveBitM2_exit_lt b dst1; omega
  have hM2start : (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).start = 0 := by
    show (composeFlatTM (AppendGadget.appendAtTM (b + 1) dst2) (ScanLeft.rewindTwoPhaseTM 4 3)
          (AppendGadget.appendAtTM_exit dst2)).start = 0
    rw [composeFlatTM_start, AppendGadget.appendAtTM_start]
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, right₁) = some v →
      v < max (Compile.moveBitM2TM b dst1).sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).sig := by
    intro v hv
    rw [hr1, show currentTapeSymbol (([] : List Nat), 0,
          Compile.encodeTape ((s.set src cs).set dst1 (s.get dst1 ++ [b])) ++ (res ++ [0]))
        = some 3 from rfl] at hv
    rw [show max (Compile.moveBitM2TM b dst1).sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).sig = 4 from by
        rw [Compile.moveBitM2TM_sig, AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl]
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_traj1 : ∀ k, k < tA → ∀ ck,
      runFlatTM k (Compile.moveBitM2TM b dst1)
          { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                       Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ Compile.moveBitM2_exit dst1 ∧
      haltingStateReached (Compile.moveBitM2TM b dst1) ck = false := by
    intro k hk ck hck
    have hh := hA_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBitM2_exit_is_halt b dst1) hh, hh⟩
  have h_app_traj' : ∀ k, k < tB → ∀ ck,
      runFlatTM k (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2)
          { state_idx := (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).start,
            tapes := [([], 0, right₁)] } = some ck →
      haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) ck = false := by
    rw [hM2start, hr1]; exact hB_traj
  have h_halt2 : haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2)
      { state_idx := 6 + (AppendGadget.appendAtTM (b + 1) dst2).states,
        tapes := [([], 0,
          Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
            ++ (res ++ [0]))] } = true := by
    rw [show (6 : Nat) + (AppendGadget.appendAtTM (b + 1) dst2).states
          = (AppendGadget.appendAtTM (b + 1) dst2).states + 6 from Nat.add_comm ..]
    exact Compile.haltingStateReached_of_halt
      (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst2)
  have hmoveeq : Compile.moveBitM3TM b dst1 dst2
      = composeFlatTM (Compile.moveBitM2TM b dst1)
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1) := rfl
  have hstate_eq : Compile.moveBitM3_exit dst1 dst2
      = (6 + (AppendGadget.appendAtTM (b + 1) dst2).states) + (Compile.moveBitM2TM b dst1).states := by
    show (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 6)
        = (6 + (AppendGadget.appendAtTM (b + 1) dst2).states) + (Compile.moveBitM2TM b dst1).states
    rw [Compile.moveBitM2TM_states_eq b dst1, Compile.appendAtTM_states_eq (b + 1) dst2]
    omega
  have hmain := composeFlatTM_run hvalid1 hvalid2 hexit_lt
    { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                 Compile.encodeTape s ++ res)] }
    hcfg0lt [] 0 right₁ hsym hA h_traj1
    (by rw [hM2start]; exact hB) h_halt2
  refine ⟨tA + 1 + tB, ?_, ?_, ?_⟩
  · rw [hmoveeq, hstate_eq]; exact hmain.1
  · intro k hk ck hck
    rw [hmoveeq] at hck ⊢
    exact composeFlatTM_no_early_halt hvalid1 hvalid2 hexit_lt
      { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                   Compile.encodeTape s ++ res)] }
      hcfg0lt [] 0 right₁ hsym hA h_traj1 h_app_traj' k hk ck hck
  · rw [hr1, hmidlen] at hB_bud
    omega

/-- Content branch (src non-empty): read the front bit, then run the matching
dual-bit transfer engine. The two bit paths exit at distinct states, merged by
`joinTwoHalts` below. -/
def Compile.moveContent2RawTM (dst1 dst2 : Nat) : FlatTM :=
  branchComposeFlatTM Compile.bitReadTM
    (Compile.moveBitM3TM 0 dst1 dst2) (Compile.moveBitM3TM 1 dst1 dst2)
    Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1

def Compile.moveContent2Exit0 (dst1 dst2 : Nat) : Nat :=
  Compile.bitReadTM.states + Compile.moveBitM3_exit dst1 dst2

def Compile.moveContent2Exit1 (dst1 dst2 : Nat) : Nat :=
  Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states + Compile.moveBitM3_exit dst1 dst2

/-- Content branch with the two bit-exits merged into one (`moveContent2Exit0`). -/
def Compile.moveContent2TM (dst1 dst2 : Nat) : FlatTM :=
  Compile.joinTwoHalts (Compile.moveContent2RawTM dst1 dst2)
    (Compile.moveContent2Exit0 dst1 dst2) (Compile.moveContent2Exit1 dst1 dst2)

theorem Compile.moveContent2RawTM_tapes (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).tapes = 1 := by
  rw [Compile.moveContent2RawTM, branchComposeFlatTM_tapes]; exact Compile.bitReadTM_tapes

theorem Compile.moveContent2TM_tapes (dst1 dst2 : Nat) :
    (Compile.moveContent2TM dst1 dst2).tapes = 1 := by
  rw [Compile.moveContent2TM, Compile.joinTwoHalts_tapes]
  exact Compile.moveContent2RawTM_tapes dst1 dst2

theorem Compile.moveContent2RawTM_sig (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).sig = 4 := by
  rw [Compile.moveContent2RawTM, branchComposeFlatTM_sig, Compile.bitReadTM_sig,
      Compile.moveBitM3TM_sig 0 dst1 dst2, Compile.moveBitM3TM_sig 1 dst1 dst2]; rfl

theorem Compile.moveContent2TM_sig (dst1 dst2 : Nat) :
    (Compile.moveContent2TM dst1 dst2).sig = 4 := by
  rw [Compile.moveContent2TM, joinTwoHalts_sig]; exact Compile.moveContent2RawTM_sig dst1 dst2

theorem Compile.moveContent2RawTM_valid (dst1 dst2 : Nat) :
    validFlatTM (Compile.moveContent2RawTM dst1 dst2) :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.bitReadTM_valid
    (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
    (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide)
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide)
    Compile.bitReadTM_tapes (Compile.moveBitM3TM_tapes 0 dst1 dst2)
    (Compile.moveBitM3TM_tapes 1 dst1 dst2)

theorem Compile.moveContent2Exit0_is_halt (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).halt[Compile.moveContent2Exit0 dst1 dst2]? = some true := by
  rw [Compile.moveContent2Exit0, Compile.moveContent2RawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide)) (Compile.moveBitM3_exit_lt 0 dst1 dst2)
    (Compile.moveBitM3_exit_is_halt 0 dst1 dst2)

theorem Compile.moveContent2Exit1_is_halt (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).halt[Compile.moveContent2Exit1 dst1 dst2]? = some true := by
  rw [Compile.moveContent2Exit1, Compile.moveContent2RawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide)) (Compile.moveBitM3_exit_is_halt 1 dst1 dst2)

theorem Compile.moveContent2Exit0_ne_exit1 (dst1 dst2 : Nat) :
    Compile.moveContent2Exit0 dst1 dst2 ≠ Compile.moveContent2Exit1 dst1 dst2 := by
  show Compile.bitReadTM.states + Compile.moveBitM3_exit dst1 dst2
      ≠ Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states
        + Compile.moveBitM3_exit dst1 dst2
  have h0 : 0 < (Compile.moveBitM3TM 0 dst1 dst2).states := by
    have := Compile.moveBitM3_exit_lt 0 dst1 dst2; omega
  omega

theorem Compile.moveContent2Exit0_lt (dst1 dst2 : Nat) :
    Compile.moveContent2Exit0 dst1 dst2 < (Compile.moveContent2RawTM dst1 dst2).states := by
  rw [Compile.moveContent2Exit0, Compile.moveContent2RawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM3_exit_lt 0 dst1 dst2; omega

theorem Compile.moveContent2Exit1_lt (dst1 dst2 : Nat) :
    Compile.moveContent2Exit1 dst1 dst2 < (Compile.moveContent2RawTM dst1 dst2).states := by
  rw [Compile.moveContent2Exit1, Compile.moveContent2RawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM3_exit_lt 1 dst1 dst2; omega

theorem Compile.moveContent2TM_valid (dst1 dst2 : Nat) :
    validFlatTM (Compile.moveContent2TM dst1 dst2) :=
  joinTwoHalts_valid _ _ _ (Compile.moveContent2RawTM_valid dst1 dst2)
    (Compile.moveContent2Exit0_lt dst1 dst2) (Compile.moveContent2Exit1_lt dst1 dst2)
    (Compile.moveContent2RawTM_tapes dst1 dst2)

theorem Compile.moveContent2TM_exit0_is_halt (dst1 dst2 : Nat) :
    (Compile.moveContent2TM dst1 dst2).halt[Compile.moveContent2Exit0 dst1 dst2]? = some true :=
  joinTwoHalts_h1_is_halt _ _ _ (Compile.moveContent2Exit0_ne_exit1 dst1 dst2)
    (Compile.moveContent2Exit0_is_halt dst1 dst2)

theorem Compile.moveContent2Exit0_lt_states (dst1 dst2 : Nat) :
    Compile.moveContent2Exit0 dst1 dst2 < (Compile.moveContent2TM dst1 dst2).states := by
  rw [Compile.moveContent2TM, joinTwoHalts_states]; exact Compile.moveContent2Exit0_lt dst1 dst2

/-- **The dual-target content-branch run (Risk C2).** Mirrors `moveContent_run`:
run from `src`'s content start (head `H`) with front bit `b` (`s.get src = b :: cs`),
`moveContent2TM dst1 dst2` reads the bit and runs the matching dual-bit transfer
(`moveBitM3_run`), the two bit-paths merging through `joinTwoHalts` into
`moveContent2Exit0`. The tape becomes
`encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
  ++ (res ++ [0])`. -/
theorem Compile.moveContent2_run (s : State) (src dst1 dst2 : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2)
    (hd12 : dst1 ≠ dst2) (hbit : Compile.BitState s)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveContent2TM dst1 dst2)
        { state_idx := 0,
          tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveContent2Exit0 dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveContent2TM dst1 dst2)
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.moveContent2Exit0 dst1 dst2 ∧
        haltingStateReached (Compile.moveContent2TM dst1 dst2) ck = false)
    ∧ t ≤ 10 * (Compile.encodeTape s ++ res).length + 33 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.moveContent2RawTM dst1 dst2 with hrawdef
  set h1 := Compile.moveContent2Exit0 dst1 dst2 with hh1def
  set h2 := Compile.moveContent2Exit1 dst1 dst2 with hh2def
  have hraweq : branchComposeFlatTM Compile.bitReadTM
      (Compile.moveBitM3TM 0 dst1 dst2) (Compile.moveBitM3TM 1 dst1 dst2)
      Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1 = raw := rfl
  have hMeq : Compile.moveContent2TM dst1 dst2 = joinTwoHalts raw h1 h2 := rfl
  rw [hMeq]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hHeq : (1 : Nat) + (Compile.encodeRegs (s.take src)).length = H := by
    rw [hHdef, hskdef, Compile.regBlocks_map_shiftReg]
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  set tail' := Compile.shiftReg cs ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src hsrc
    rw [← hskdef] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg cs := by
      rw [hcons]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hHlt : H < (Compile.encodeTape s ++ res).length := by
    rw [hdecomp, hHdef]; simp only [List.length_cons, List.length_append]; omega
  have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = b + 1 := by
    have h? : (Compile.encodeTape s ++ res)[H]? = some (b + 1) := by
      rw [hdecomp, hHdef,
          show ((3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail'))
            = ((3 : Nat) :: AppendGadget.regBlocks skipped) ++ ((b + 1) :: tail') from by simp,
          List.getElem?_append_right (by simp only [List.length_cons]; omega),
          show 1 + (AppendGadget.regBlocks skipped).length
            - ((3 : Nat) :: AppendGadget.regBlocks skipped).length = 0 from by
              simp only [List.length_cons]; omega]
      rfl
    rw [List.getElem?_eq_getElem hHlt] at h?
    rw [List.get_eq_getElem]; exact Option.some.inj h?
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max Compile.bitReadTM.sig
          (max (Compile.moveBitM3TM 0 dst1 dst2).sig (Compile.moveBitM3TM 1 dst1 dst2).sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    rw [Compile.bitReadTM_sig]
    have : v < 4 := by have : v = b + 1 := (Option.some.inj hv).symm; omega
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < Compile.bitReadTM.states := by rw [Compile.bitReadTM_states]; omega
  have hexit_neq : Compile.bitReadTM_exit_b0 ≠ Compile.bitReadTM_exit_b1 := by decide
  have hep_lt : Compile.bitReadTM_exit_b0 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide
  have hen_lt : Compile.bitReadTM_exit_b1 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide
  have hh1_is := Compile.moveContent2Exit0_is_halt dst1 dst2
  have hh2_is := Compile.moveContent2Exit1_is_halt dst1 dst2
  have hh_ne := Compile.moveContent2Exit0_ne_exit1 dst1 dst2
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  have htest_run := Compile.bitReadTM_run b hb [] (Compile.encodeTape s ++ res) H hHlt hcellH
  have htest_traj : ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.bitReadTM cfg0 = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧ ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧
      haltingStateReached Compile.bitReadTM ck = false := by
    intro k hk ck hck
    exact Compile.bitReadTM_no_early_halt [] (Compile.encodeTape s ++ res) H k hk ck hck
  interval_cases b
  · -- bit 0: pos branch, dual transfer engine for bit 0; kept exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM3_run s src dst1 dst2 0 cs (by omega) hsd1 hsd2 hd12 hsrc hdst1 hdst2 hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM3_exit_is_halt 0 dst1 dst2))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM3_exit dst1 dst2 + Compile.bitReadTM.states = h1 := by
      rw [hh1def]; show Compile.moveBitM3_exit dst1 dst2 + Compile.bitReadTM.states
        = Compile.bitReadTM.states + Compile.moveBitM3_exit dst1 dst2
      omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [0])).set dst2
            (s.get dst2 ++ [0])) ++ (res ++ [0]))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega
  · -- bit 1: neg branch, dual transfer engine for bit 1; demoted exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM3_run s src dst1 dst2 1 cs (by omega) hsd1 hsd2 hd12 hsrc hdst1 hdst2 hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM3_exit_is_halt 1 dst1 dst2))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM3_exit dst1 dst2
        + (Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states) = h2 := by
      rw [hh2def]; show Compile.moveBitM3_exit dst1 dst2
          + (Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states)
        = Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states
            + Compile.moveBitM3_exit dst1 dst2
      omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [1])).set dst2
            (s.get dst2 ++ [1])) ++ (res ++ [0])) 0
      hneg.1 (fun k hk ck hck => hneg_traj k hk ck hck) hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [1])).set dst2
                (s.get dst2 ++ [1])) ++ (res ++ [0]))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.moveContent2RawTM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega

/-- The loop body: navigate to `src`, branch content (move one bit to both targets)
vs delim (src empty → rewind & stop). -/
def Compile.moveBody2RawTM (src dst1 dst2 : Nat) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM src) (Compile.moveContent2TM dst1 dst2)
    ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content src) (ClearGadget.navigateAndTestTM_exit_delim src)

def Compile.moveBody2RawTM_exitLoop (src dst1 dst2 : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + Compile.moveContent2Exit0 dst1 dst2

def Compile.moveBody2RawTM_exitDone (src dst1 dst2 : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
    + ClearGadget.justRewindTM_exit

/-- The full dual-target move gadget: loop the body until `src` empties. -/
def Compile.moveRegion2TM (src dst1 dst2 : Nat) : FlatTM :=
  loopTM (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)

/-- The single halt state of `moveRegion2TM` (the `loopTM` done-exit). -/
def Compile.moveRegion2TM_exit (src dst1 dst2 : Nat) : Nat :=
  (Compile.moveBody2RawTM src dst1 dst2).states

theorem Compile.moveBody2RawTM_tapes (src dst1 dst2 : Nat) :
    (Compile.moveBody2RawTM src dst1 dst2).tapes = 1 := by
  rw [Compile.moveBody2RawTM, branchComposeFlatTM_tapes]
  exact ClearGadget.navigateAndTestTM_tapes src

theorem Compile.moveBody2RawTM_valid (src dst1 dst2 : Nat) :
    validFlatTM (Compile.moveBody2RawTM src dst1 dst2) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.navigateAndTestTM_valid src)
    (Compile.moveContent2TM_valid dst1 dst2) ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    (ClearGadget.navigateAndTestTM_tapes src) (Compile.moveContent2TM_tapes dst1 dst2)
    ClearGadget.justRewindTM_tapes

theorem Compile.moveBody2RawTM_exitLoop_is_halt (src dst1 dst2 : Nat) :
    (Compile.moveBody2RawTM src dst1 dst2).halt[Compile.moveBody2RawTM_exitLoop src dst1 dst2]?
      = some true := by
  rw [Compile.moveBody2RawTM_exitLoop, Compile.moveBody2RawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveContent2TM_valid dst1 dst2) (Compile.moveContent2Exit0_lt_states dst1 dst2)
    (Compile.moveContent2TM_exit0_is_halt dst1 dst2)

theorem Compile.moveBody2RawTM_exitDone_is_halt (src dst1 dst2 : Nat) :
    (Compile.moveBody2RawTM src dst1 dst2).halt[Compile.moveBody2RawTM_exitDone src dst1 dst2]?
      = some true := by
  rw [Compile.moveBody2RawTM_exitDone, Compile.moveBody2RawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveContent2TM_valid dst1 dst2)
    (show ClearGadget.justRewindTM.halt[ClearGadget.justRewindTM_exit]? = some true from rfl)

theorem Compile.moveBody2RawTM_exitLoop_lt (src dst1 dst2 : Nat) :
    Compile.moveBody2RawTM_exitLoop src dst1 dst2 < (Compile.moveBody2RawTM src dst1 dst2).states := by
  rw [Compile.moveBody2RawTM_exitLoop, Compile.moveBody2RawTM, branchComposeFlatTM_states]
  have := Compile.moveContent2Exit0_lt_states dst1 dst2; omega

theorem Compile.moveBody2RawTM_exitDone_lt (src dst1 dst2 : Nat) :
    Compile.moveBody2RawTM_exitDone src dst1 dst2 < (Compile.moveBody2RawTM src dst1 dst2).states := by
  rw [Compile.moveBody2RawTM_exitDone, Compile.moveBody2RawTM, branchComposeFlatTM_states]
  show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
      + ClearGadget.justRewindTM_exit
    < (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
      + ClearGadget.justRewindTM.states
  show _ + _ + 1 < _ + _ + 3; omega

theorem Compile.moveBody2RawTM_exitDone_ne_exitLoop (src dst1 dst2 : Nat) :
    Compile.moveBody2RawTM_exitDone src dst1 dst2 ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 := by
  rw [Compile.moveBody2RawTM_exitDone, Compile.moveBody2RawTM_exitLoop]
  have := Compile.moveContent2Exit0_lt_states dst1 dst2; omega

theorem Compile.moveRegion2TM_tapes (src dst1 dst2 : Nat) :
    (Compile.moveRegion2TM src dst1 dst2).tapes = 1 := by
  rw [Compile.moveRegion2TM, loopTM_tapes]; exact Compile.moveBody2RawTM_tapes src dst1 dst2

theorem Compile.moveRegion2TM_start (src dst1 dst2 : Nat) :
    (Compile.moveRegion2TM src dst1 dst2).start = 0 := by
  show (Compile.moveBody2RawTM src dst1 dst2).start = 0
  show (branchComposeFlatTM _ _ _ _ _).start = 0
  rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src

/-- **Validity of `moveRegion2TM`.** Mirrors `moveRegionTM_valid`: a `loopTM` over
the valid dual-target body. -/
theorem Compile.moveRegion2TM_valid (src dst1 dst2 : Nat) :
    validFlatTM (Compile.moveRegion2TM src dst1 dst2) :=
  loopTM_valid (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)
    (Compile.moveBody2RawTM_valid src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_lt src dst1 dst2) (Compile.moveBody2RawTM_exitLoop_lt src dst1 dst2)
    (Compile.moveBody2RawTM_tapes src dst1 dst2)

theorem Compile.moveRegion2TM_sig (src dst1 dst2 : Nat) :
    (Compile.moveRegion2TM src dst1 dst2).sig = 4 := by
  rw [Compile.moveRegion2TM, loopTM_sig]
  show (Compile.moveBody2RawTM src dst1 dst2).sig = 4
  show (branchComposeFlatTM _ _ _ _ _).sig = 4
  rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig]
  show max 4 (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) = 4
  rw [Compile.moveContent2TM_sig dst1 dst2]
  rfl

/-- **Dual-target move loop body — done branch (`src` empty).** Mirrors
`moveBody_done_run`: navigate to `src`, find the delimiter (empty), rewind to head
`0`, tape unchanged, landing at `moveBody2RawTM_exitDone`. -/
theorem Compile.moveBody2_done_run (s : State) (src dst1 dst2 : Var) (res : List Nat)
    (hsrc : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBody2RawTM src dst1 dst2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBody2RawTM_exitDone src dst1 dst2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s src hsrc
  have hbit_take : Compile.BitState (s.take src) :=
    fun reg hreg => hbit reg (List.mem_of_mem_take hreg)
  set skipped : List (List Nat) := (s.take src).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take src) :=
    Compile.regBlocks_map_shiftReg (s.take src)
  have hsklen : skipped.length = src := by
    rw [hskdef, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hsrc)]
  have hskip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    rw [hskdef]; intro b hb
    rw [List.mem_map] at hb
    obtain ⟨reg, hreg, rfl⟩ := hb
    have hregmem : reg ∈ s := List.mem_of_mem_take hreg
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; omega
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      have : y ≤ 1 := hbit reg hregmem y hy; omega
  set tail' : List Nat :=
    Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htaildef
  have htape_nav : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    rw [hs, hempty, hregBlocks, htaildef]
    simp [Compile.shiftReg, Compile.endMark, List.append_assoc]
  have h_rb_le : (AppendGadget.regBlocks skipped).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [htape_nav]; simp only [List.length_cons, List.length_append]; omega
  have h_nav_le : ClearGadget.navSteps skipped ≤ 2 * (AppendGadget.regBlocks skipped).length + 1 :=
    ClearGadget.navSteps_le skipped
  have hrb : ∀ x ∈ AppendGadget.regBlocks skipped, x < 4 ∧ x ≠ 3 := by
    rw [hregBlocks]; intro x hx
    exact ⟨Compile.encodeRegs_lt_four (s.take src) hbit_take x hx,
           Compile.encodeRegs_no_endMark (s.take src) hbit_take x hx⟩
  have hpref : ∀ x ∈ AppendGadget.regBlocks skipped ++ [0], x < 4 ∧ x ≠ 3 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrb x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  have hrestsplit : AppendGadget.regBlocks skipped ++ 0 :: tail'
      = (AppendGadget.regBlocks skipped ++ [0]) ++ tail' := by simp [List.append_assoc]
  have h_rewind := ScanLeft.rewindToStart_run 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind
  have h_rewind_traj := ScanLeft.rewindToStart_traj 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind_traj
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM src).sig
        (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContent2TM_sig]; rfl,
        (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim src,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_delim skipped tail' hskip
    rw [← htape_nav, hsklen] at hn; exact hn
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail' hskip
        (by decide) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh,
           hh⟩
  have h_ne : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1
        ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1
      + ((1 + (AppendGadget.regBlocks skipped).length) + 1), ?_, ?_, ?_⟩
  · rw [show Compile.moveBody2RawTM src dst1 dst2
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
            (Compile.moveContent2TM dst1 dst2) ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content src)
            (ClearGadget.navigateAndTestTM_exit_delim src) from rfl,
      show Compile.moveBody2RawTM_exitDone src dst1 dst2
        = ClearGadget.justRewindTM_exit
            + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states)
          from by
          show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
              + ClearGadget.justRewindTM_exit
            = ClearGadget.justRewindTM_exit
                + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states)
          omega]
    exact (branchComposeFlatTM_run_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1 h_rewind
      (Compile.haltingStateReached_of_halt (show ClearGadget.justRewindTM.halt[1]? = some true from rfl))).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (fun k' hk' ck' hck' => (h_rewind_traj k' hk' ck' hck').2)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitDone_is_halt src dst1 dst2) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitLoop_is_halt src dst1 dst2) hh, hh⟩
  · omega

/-- **Dual-target move loop body — delete branch (`src` non-empty, front bit `b`).**
Navigate to `src`, the content branch reads `b` and runs the dual-bit transfer
(`moveContent2_run`), landing at `moveBody2RawTM_exitLoop` with the tape
`encodeTape (((s.set src cs).set dst1 (d1++[b])).set dst2 (d2++[b])) ++ (res ++ [0])`. -/
theorem Compile.moveBody2_delete_run (s : State) (src dst1 dst2 : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2)
    (hd12 : dst1 ≠ dst2) (hbit : Compile.BitState s)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBody2RawTM src dst1 dst2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBody2RawTM_exitLoop src dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
                   ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false)
      ∧ t ≤ 12 * (Compile.encodeTape s ++ res).length + 38 := by
  have hne : s.get src ≠ [] := by rw [hcons]; exact List.cons_ne_nil _ _
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
    Compile.moveContent2_run s src dst1 dst2 b cs hcons hb hsd1 hsd2 hd12 hbit hsrc hdst1 hdst2 res hres
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) := by
    intro v hv
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContent2TM_sig]; rfl]
    have hmem : v ∈ Compile.encodeTape s ++ res := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact htape4 v hmem
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hpos := branchComposeFlatTM_run_pos hexit_neq
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne) hbody
    (Compile.haltingStateReached_of_halt (Compile.moveContent2TM_exit0_is_halt dst1 dst2))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne)
    (fun k hk ck hck => (hbody_traj k hk ck hck).2)
  have hstate_eq : Compile.moveContent2Exit0 dst1 dst2 + (ClearGadget.navigateAndTestTM src).states
      = Compile.moveBody2RawTM_exitLoop src dst1 dst2 := by
    rw [Compile.moveBody2RawTM_exitLoop]; omega
  have hmoveeq : Compile.moveBody2RawTM src dst1 dst2
      = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
          (Compile.moveContent2TM dst1 dst2) ClearGadget.justRewindTM
          (ClearGadget.navigateAndTestTM_exit_content src)
          (ClearGadget.navigateAndTestTM_exit_delim src) := rfl
  rw [hstate_eq] at hpos
  refine ⟨(ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [hmoveeq]; exact hpos.1
  · intro k hk ck hck
    rw [hmoveeq] at hck
    have hh := hpos_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitDone_is_halt src dst1 dst2) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitLoop_is_halt src dst1 dst2) hh, hh⟩
  · have hnav : ClearGadget.navSteps ((s.take src).map Compile.shiftReg)
        ≤ 2 * (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length + 1 :=
      ClearGadget.navSteps_le _
    have hrbL : (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length
        ≤ (Compile.encodeTape s ++ res).length := by
      have hsplit := congrArg List.length (Compile.encodeTape_split s src hsrc)
      simp only [List.length_append, List.length_cons, Compile.encodeRegs_length] at hsplit
      rw [List.length_append, Compile.encodeTape_length]
      omega
    omega

/-- **Move loop body — done branch (`src` empty).** Mirrors `clearBody_done_run`:
navigate to `src`, find the delimiter (empty), rewind to head `0`, tape unchanged,
landing at `moveBodyRawTM_exitDone`. The content machine `moveContentTM dst` is the
(unused) positive branch. -/
theorem Compile.moveBody_done_run (s : State) (src dst : Var) (res : List Nat)
    (hsrc : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBodyRawTM src dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBodyRawTM_exitDone src dst,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s src hsrc
  have hbit_take : Compile.BitState (s.take src) :=
    fun reg hreg => hbit reg (List.mem_of_mem_take hreg)
  set skipped : List (List Nat) := (s.take src).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take src) :=
    Compile.regBlocks_map_shiftReg (s.take src)
  have hsklen : skipped.length = src := by
    rw [hskdef, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hsrc)]
  have hskip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    rw [hskdef]; intro b hb
    rw [List.mem_map] at hb
    obtain ⟨reg, hreg, rfl⟩ := hb
    have hregmem : reg ∈ s := List.mem_of_mem_take hreg
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; omega
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      have : y ≤ 1 := hbit reg hregmem y hy; omega
  set tail' : List Nat :=
    Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htaildef
  have htape_nav : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    rw [hs, hempty, hregBlocks, htaildef]
    simp [Compile.shiftReg, Compile.endMark, List.append_assoc]
  have h_rb_le : (AppendGadget.regBlocks skipped).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [htape_nav]; simp only [List.length_cons, List.length_append]; omega
  have h_nav_le : ClearGadget.navSteps skipped ≤ 2 * (AppendGadget.regBlocks skipped).length + 1 :=
    ClearGadget.navSteps_le skipped
  have hrb : ∀ x ∈ AppendGadget.regBlocks skipped, x < 4 ∧ x ≠ 3 := by
    rw [hregBlocks]; intro x hx
    exact ⟨Compile.encodeRegs_lt_four (s.take src) hbit_take x hx,
           Compile.encodeRegs_no_endMark (s.take src) hbit_take x hx⟩
  have hpref : ∀ x ∈ AppendGadget.regBlocks skipped ++ [0], x < 4 ∧ x ≠ 3 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrb x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  have hrestsplit : AppendGadget.regBlocks skipped ++ 0 :: tail'
      = (AppendGadget.regBlocks skipped ++ [0]) ++ tail' := by simp [List.append_assoc]
  have h_rewind := ScanLeft.rewindToStart_run 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind
  have h_rewind_traj := ScanLeft.rewindToStart_traj 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind_traj
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM src).sig
        (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContentTM_sig]; rfl,
        (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim src,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_delim skipped tail' hskip
    rw [← htape_nav, hsklen] at hn; exact hn
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail' hskip
        (by decide) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh,
           hh⟩
  have h_ne : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1
        ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1
      + ((1 + (AppendGadget.regBlocks skipped).length) + 1), ?_, ?_, ?_⟩
  · rw [show Compile.moveBodyRawTM src dst
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
            (Compile.moveContentTM dst) ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content src)
            (ClearGadget.navigateAndTestTM_exit_delim src) from rfl,
      show Compile.moveBodyRawTM_exitDone src dst
        = ClearGadget.justRewindTM_exit
            + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states)
          from by
          show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
              + ClearGadget.justRewindTM_exit
            = ClearGadget.justRewindTM_exit
                + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states)
          omega]
    exact (branchComposeFlatTM_run_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1 h_rewind
      (Compile.haltingStateReached_of_halt (show ClearGadget.justRewindTM.halt[1]? = some true from rfl))).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (fun k' hk' ck' hck' => (h_rewind_traj k' hk' ck' hck').2)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitDone_is_halt src dst) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitLoop_is_halt src dst) hh, hh⟩
  · omega

/-- **Move loop body — delete branch (`src` non-empty, front bit `b`).** Navigate
to `src`, the content branch reads bit `b` and runs the single-bit transfer
(`moveContent_run`), landing at `moveBodyRawTM_exitLoop` with the tape
`encodeTape ((s.set src cs).set dst (s.get dst ++ [b])) ++ (res ++ [0])`. Mirrors
`opHead_run`'s content case. -/
theorem Compile.moveBody_delete_run (s : State) (src dst : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd : src ≠ dst)
    (hbit : Compile.BitState s) (hsrc : src < s.length) (hdst : dst < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBodyRawTM src dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBodyRawTM_exitLoop src dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                   ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false)
      ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length + 26 := by
  have hne : s.get src ≠ [] := by rw [hcons]; exact List.cons_ne_nil _ _
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
    Compile.moveContent_run s src dst b cs hcons hb hsd hbit hsrc hdst res hres
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) := by
    intro v hv
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContentTM_sig]; rfl]
    have hmem : v ∈ Compile.encodeTape s ++ res := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact htape4 v hmem
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hpos := branchComposeFlatTM_run_pos hexit_neq
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne) hbody
    (Compile.haltingStateReached_of_halt (Compile.moveContentTM_exit0_is_halt dst))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne)
    (fun k hk ck hck => (hbody_traj k hk ck hck).2)
  have hstate_eq : Compile.moveContentExit0 dst + (ClearGadget.navigateAndTestTM src).states
      = Compile.moveBodyRawTM_exitLoop src dst := by
    rw [Compile.moveBodyRawTM_exitLoop]; omega
  have hmoveeq : Compile.moveBodyRawTM src dst
      = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
          (Compile.moveContentTM dst) ClearGadget.justRewindTM
          (ClearGadget.navigateAndTestTM_exit_content src)
          (ClearGadget.navigateAndTestTM_exit_delim src) := rfl
  rw [hstate_eq] at hpos
  refine ⟨(ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [hmoveeq]; exact hpos.1
  · intro k hk ck hck
    rw [hmoveeq] at hck
    have hh := hpos_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitDone_is_halt src dst) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitLoop_is_halt src dst) hh, hh⟩
  · -- budget: navtest (≤ 2L+3) + bridge (1) + moveContent (≤ 7L+21) ≤ 9L+26.
    have hnav : ClearGadget.navSteps ((s.take src).map Compile.shiftReg)
        ≤ 2 * (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length + 1 :=
      ClearGadget.navSteps_le _
    have hrbL : (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length
        ≤ (Compile.encodeTape s ++ res).length := by
      have hsplit := congrArg List.length (Compile.encodeTape_split s src hsrc)
      simp only [List.length_append, List.length_cons, Compile.encodeRegs_length] at hsplit
      rw [List.length_append, Compile.encodeTape_length]
      omega
    omega

/-- **Move-loop budget arithmetic.** Each iteration is `O(L)` (a deletion + an
append, each one `O(current tape length) ≤ O(2·L)`), summed over `≤ L`
iterations — dominated by the quadratic `25·L²+25` (`n+2 ≤ L`). -/
theorem Compile.moveBudget_arith (n L : Nat) (h : n + 2 ≤ L) :
    (n + 1) * (18 * L + 27) ≤ 25 * L * L + 25 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  nlinarith [Nat.zero_le n, Nat.zero_le d, Nat.zero_le (n * d)]

/-- **The residue-tolerant move contract (Risk C2 — Task 2 critical path).**
Running `moveRegionTM src dst` on `encodeTape s ++ res_in` transfers `src`'s
content (FIFO) to the end of `dst`, empties `src`, rewinds the head to `0`, and
leaves the tape `encodeTape (moved s) ++ (res_in ++ replicate |s.get src| 0)`.
Assembled from `loopTM_run`; the per-iteration invariant `T j` couples BOTH
registers (`src = drop (n−j)` of `src₀`, `dst = dst₀ ++ first (n−j) bits`), and
the moved bit's value is threaded so `dst` gets the right bit. Unlike `clear`, the
tape **grows** one residue cell per iteration (`|T j| = L + (n−j)`), so the loop
budget is `25·L²+25` with `L = |encodeTape s ++ res_in|`. -/
theorem Compile.moveRegionTM_run (s : State) (src dst : Var) (res_in : List Nat)
    (hsd : src ≠ dst) (hsrc : src < s.length) (hdst : dst < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res_in) :
    ∃ t, runFlatTM t (Compile.moveRegionTM src dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
      = some { state_idx := Compile.moveRegionTM_exit src dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set dst (s.get dst ++ s.get src)).set src [])
                   ++ (res_in ++ List.replicate (s.get src).length 0))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveRegionTM src dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } = some ck →
          ck.state_idx ≠ Compile.moveRegionTM_exit src dst ∧
          haltingStateReached (Compile.moveRegionTM src dst) ck = false)
      ∧ t ≤ 25 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
              + 25 := by
  set n := (s.get src).length with hn
  set st : Nat → State := fun m =>
    (s.set dst (s.get dst ++ (s.get src).take m)).set src ((s.get src).drop m) with hstdef
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 0, Compile.encodeTape (st (n - j)) ++ (res_in ++ List.replicate (n - j) 0)) with hTdef
  set L := (Compile.encodeTape s ++ res_in).length with hLdef
  have hsrc' : src < (s.set dst (s.get dst ++ (s.get src).take 0)).length := by
    rw [Compile.length_set s dst _ hdst]; exact hsrc
  have hv_bit : ∀ x ∈ s.get src, x ≤ 1 := Compile.BitState_get s src hbit hsrc
  have hd_bit : ∀ x ∈ s.get dst, x ≤ 1 := Compile.BitState_get s dst hbit hdst
  have hBstart : (Compile.moveBodyRawTM src dst).start = 0 := by
    show (branchComposeFlatTM _ _ _ _ _).start = 0
    rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src
  -- structural facts about `st m`.
  have hsrc_in : ∀ m, src < (s.set dst (s.get dst ++ (s.get src).take m)).length := by
    intro m; rw [Compile.length_set s dst _ hdst]; exact hsrc
  have hbit_st : ∀ m, Compile.BitState (st m) := by
    intro m
    have hbase : Compile.BitState (s.set dst (s.get dst ++ (s.get src).take m)) := by
      refine Compile.BitState_set s dst _ hbit hdst ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hd_bit x hx
      · exact hv_bit x (List.mem_of_mem_take hx)
    exact Compile.BitState_set _ src _ hbase (hsrc_in m)
      (fun x hx => hv_bit x (List.mem_of_mem_drop hx))
  have hlen_st : ∀ m, (st m).length = s.length := by
    intro m; rw [hstdef, Compile.length_set _ src _ (hsrc_in m), Compile.length_set s dst _ hdst]
  have hget_src_st : ∀ m, (st m).get src = (s.get src).drop m := by
    intro m; rw [hstdef]; exact Compile.get_set_eq _ src _ (hsrc_in m)
  have hget_dst_st : ∀ m, (st m).get dst = s.get dst ++ (s.get src).take m := by
    intro m; rw [hstdef, Compile.get_set_ne _ src _ dst (hsrc_in m) (Ne.symm hsd),
      Compile.get_set_eq s dst _ hdst]
  -- size of `st m` equals `State.size s` (bits move within the state).
  have hsize_st : ∀ m, m ≤ n → State.size (st m) = State.size s := by
    intro m hm
    have h1 := State.size_set_add s dst (s.get dst ++ (s.get src).take m)
    have h2 := State.size_set_add (s.set dst (s.get dst ++ (s.get src).take m)) src
      ((s.get src).drop m)
    rw [Compile.get_set_ne s dst _ src hdst hsd] at h2
    rw [List.length_append] at h1
    have htake : ((s.get src).take m).length = m := by rw [List.length_take, ← hn]; omega
    have hdrop : ((s.get src).drop m).length = n - m := by rw [List.length_drop, ← hn]
    rw [htake] at h1
    rw [hdrop] at h2
    simp only [hstdef] at h2 ⊢
    rw [← hn] at h2
    omega
  -- tape length of `T j`: grows by `n − j` residue cells.
  have hTlen : ∀ j, j ≤ n → (T j).2.2.length = L + (n - j) := by
    intro j hj
    simp only [hTdef, List.length_append, List.length_replicate]
    rw [Compile.encodeTape_length, hsize_st (n - j) (Nat.sub_le n j), hlen_st,
        hLdef, List.length_append, Compile.encodeTape_length]
    omega
  have hnL : n + 2 ≤ L := by
    have hsize := State.size_set_add s src ([] : List Nat)
    simp only [List.length_nil, Nat.add_zero] at hsize
    rw [hLdef, List.length_append, Compile.encodeTape_length]
    omega
  -- all tape symbols of `T j` are `< 4`.
  have hT_lt : ∀ j x, x ∈ (T j).2.2 → x < 4 := by
    intro j x hx
    simp only [hTdef] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four _ (hbit_st _) x hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hres x hx).1
      · rw [List.mem_replicate] at hx; omega
  have h_sym : ∀ m v, currentTapeSymbol (T m) = some v → v < (Compile.moveBodyRawTM src dst).sig := by
    intro m v hv
    have hsig : (Compile.moveBodyRawTM src dst).sig = 4 := by
      show (branchComposeFlatTM _ _ _ _ _).sig = 4
      rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig, Compile.moveContentTM_sig]; rfl
    rw [hsig]
    have hmem : v ∈ (T m).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_lt m v hmem
  -- done branch: `T 0`, register `src` empty.
  have hdone := Compile.moveBody_done_run (st n) src dst (res_in ++ List.replicate n 0)
    (by rw [hlen_st]; exact hsrc) (hbit_st n)
    (by rw [hget_src_st, hn]; exact List.drop_length)
    (Compile.ValidResidue_append_replicate_zero res_in n hres)
  obtain ⟨tDone, hdr, hdt, hdb⟩ := hdone
  have hT0 : T 0 = ([], 0, Compile.encodeTape (st n) ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero]
  have h_done_bnd : tDone + 1 ≤ 18 * L + 27 := by
    have hlen0 := hTlen 0 (Nat.zero_le n)
    simp only [hTdef, Nat.sub_zero] at hlen0
    rw [hlen0] at hdb
    omega
  -- per-iteration move: `T (j+1) → T j` for `j < n`, moving one bit.
  have hiter_ex : ∀ j, j < n → ∃ t,
      runFlatTM t (Compile.moveBodyRawTM src dst)
          { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBodyRawTM_exitLoop src dst, tapes := [T j] } ∧
      (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBodyRawTM src dst)
            { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] } = some ck →
        ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
        ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
        haltingStateReached (Compile.moveBodyRawTM src dst) ck = false) ∧
      t ≤ 18 * L + 26 := by
    intro j hj
    set m := n - (j + 1) with hm
    have hmn : m < n := by omega
    have hm1 : m + 1 = n - j := by omega
    have hmlen : m < (s.get src).length := by rw [← hn]; exact hmn
    -- the front bit of `st m`'s src content.
    have hdc : (s.get src).drop m = (s.get src)[m] :: (s.get src).drop (m + 1) :=
      List.drop_eq_getElem_cons hmlen
    have hb1 : (s.get src)[m] ≤ 1 := hv_bit _ (List.getElem_mem hmlen)
    have hsrc_cons : (st m).get src = (s.get src)[m] :: (s.get src).drop (m + 1) := by
      rw [hget_src_st]; exact hdc
    obtain ⟨t, hr, ht, hbnd⟩ := Compile.moveBody_delete_run (st m) src dst ((s.get src)[m])
      ((s.get src).drop (m + 1)) hsrc_cons hb1 hsd (hbit_st m) (by rw [hlen_st]; exact hsrc)
      (by rw [hlen_st]; exact hdst) (res_in ++ List.replicate m 0)
      (Compile.ValidResidue_append_replicate_zero res_in m hres)
    -- bridge the move output to `T j`.
    have hstate_eq : ((st m).set src ((s.get src).drop (m + 1))).set dst
          ((st m).get dst ++ [(s.get src)[m]]) = st (n - j) := by
      rw [hget_dst_st, hstdef]
      rw [Compile.set_set _ src _ _ (hsrc_in m)]
      rw [Compile.set_comm (s.set dst (s.get dst ++ (s.get src).take m)) src dst _ _
            (hsrc_in m) (by rw [Compile.length_set s dst _ hdst]; exact hdst) hsd,
          Compile.set_set s dst _ _ hdst]
      rw [show (s.get dst ++ (s.get src).take m) ++ [(s.get src)[m]]
            = s.get dst ++ (s.get src).take (m + 1) from by
            rw [List.append_assoc, List.take_succ_eq_append_getElem hmlen],
          ← hm1]
    have hres_eq : (res_in ++ List.replicate m 0) ++ [0] = res_in ++ List.replicate (n - j) 0 := by
      rw [List.append_assoc, ← List.replicate_succ', hm1]
    rw [hstate_eq, hres_eq] at hr
    have hlenj := hTlen (j + 1) (by omega)
    simp only [hTdef] at hlenj
    rw [show n - (j + 1) = m from rfl] at hlenj
    rw [hlenj] at hbnd
    refine ⟨t, ?_, ?_, by omega⟩
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact hr
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact ht
  -- assemble the loop.
  set tIter : Nat → Nat := fun j => if hj : j < n then (hiter_ex j hj).choose else 0 with htIter
  have h_done_full :
      runFlatTM tDone (Compile.moveBodyRawTM src dst)
          { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T 0] }
        = some { state_idx := Compile.moveBodyRawTM_exitDone src dst, tapes := [T 0] } ∧
      (∀ k, k < tDone → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false) := by
    refine ⟨?_, ?_⟩
    · rw [hBstart, hT0]; exact hdr
    · rw [hBstart, hT0]; exact hdt
  have h_iter_full : ∀ j, j < n →
      runFlatTM (tIter j) (Compile.moveBodyRawTM src dst)
          { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBodyRawTM_exitLoop src dst, tapes := [T j] } ∧
      (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false) := by
    intro j hj
    have hspec := (hiter_ex j hj).choose_spec
    simp only [htIter, dif_pos hj]
    exact ⟨hspec.1, hspec.2.1⟩
  have h_iter_bnd : ∀ j, j < n → tIter j + 1 ≤ 18 * L + 27 := by
    intro j hj
    have hb := (hiter_ex j hj).choose_spec.2.2
    simp only [htIter, dif_pos hj]
    omega
  have hmain := loopTM_run (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)
    (Compile.moveBodyRawTM_valid src dst)
    (Compile.moveBodyRawTM_exitDone_lt src dst) (Compile.moveBodyRawTM_exitLoop_lt src dst)
    (Compile.moveBodyRawTM_exitDone_ne_exitLoop src dst) T h_sym tIter tDone h_done_full n h_iter_full
  have hmain_traj := loopTM_no_early_halt (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)
    (Compile.moveBodyRawTM_valid src dst)
    (Compile.moveBodyRawTM_exitDone_lt src dst) (Compile.moveBodyRawTM_exitLoop_lt src dst)
    (Compile.moveBodyRawTM_exitDone_ne_exitLoop src dst) T h_sym tIter tDone h_done_full n h_iter_full
  -- convert `T n` (start) and `T 0` (end) to the stated forms.
  have hTn : T n = ([], 0, Compile.encodeTape s ++ res_in) := by
    simp only [hTdef, Nat.sub_self]
    rw [hstdef]
    simp only [List.take_zero, List.drop_zero, List.append_nil, List.replicate_zero]
    rw [Compile.set_get_self s dst hdst, Compile.set_get_self s src hsrc]
  have hTfin : T 0 = ([], 0, Compile.encodeTape ((s.set dst (s.get dst ++ s.get src)).set src [])
      ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero, hstdef]
    rw [show (s.get src).take n = s.get src from by rw [hn]; exact List.take_length,
        show (s.get src).drop n = [] from by rw [hn]; exact List.drop_length]
  rw [hBstart, hTn, hTfin] at hmain
  rw [hBstart, hTn] at hmain_traj
  have hMeq : Compile.moveRegionTM src dst
      = loopTM (Compile.moveBodyRawTM src dst) (Compile.moveBodyRawTM_exitDone src dst)
          (Compile.moveBodyRawTM_exitLoop src dst) := rfl
  have hExeq : Compile.moveRegionTM_exit src dst = (Compile.moveBodyRawTM src dst).states := rfl
  have hexit_halt : (Compile.moveRegionTM src dst).halt[(Compile.moveBodyRawTM src dst).states]?
      = some true := by
    rw [hMeq]
    show (loopHalt (Compile.moveBodyRawTM src dst))[(Compile.moveBodyRawTM src dst).states]? = some true
    show (List.replicate (Compile.moveBodyRawTM src dst).states false ++ [true])[(Compile.moveBodyRawTM src dst).states]?
        = some true
    rw [List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  refine ⟨loopBudget tIter tDone n, ?_, ?_, ?_⟩
  · rw [hMeq, hExeq]; exact hmain
  · intro k hk ck hck
    rw [hMeq] at hck
    have hh := hmain_traj k hk ck hck
    refine ⟨?_, hh⟩
    rw [hExeq]
    rw [hMeq] at hexit_halt
    exact ClearGadget.ne_of_not_halting hexit_halt hh
  · -- budget: `loopBudget ≤ (n+1)·(18L+27) ≤ 25L²+25` (`n+2 ≤ L`).
    rw [hLdef] at hnL ⊢
    exact le_trans
      (Compile.loopBudget_le tIter tDone (18 * L + 27) n h_done_bnd h_iter_bnd)
      (by rw [← hLdef]; exact Compile.moveBudget_arith n L (by rw [hLdef]; exact hnL))

/-- **Dual-target move-loop budget arithmetic.** `(n+1)` iterations each `≤ 36L+39`
(per-iter tape `≤ L + 2(n−j) ≤ 3L`, two appends/bit), `n+1 ≤ L`, gives a cubic-free
quadratic total. -/
theorem Compile.moveBudget2_arith (n L : Nat) (h : n + 2 ≤ L) :
    (n + 1) * (36 * L + 39) ≤ 36 * L * L + 39 * L := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  nlinarith [Nat.zero_le n, Nat.zero_le d, Nat.zero_le (n * d)]

/-- **The dual-target duplicating move contract (Risk C2).** Running
`moveRegion2TM src dst1 dst2` on `encodeTape s ++ res_in` transfers `src`'s content
(FIFO) to the end of **both** `dst1` and `dst2`, empties `src`, rewinds the head to
`0`, leaving `encodeTape (moved s) ++ (res_in ++ replicate |s.get src| 0)`. Mirrors
`moveRegionTM_run`, but the per-iteration invariant couples **three** registers and
the state size grows (each bit is duplicated), so the per-iteration tape length is
`L + 2(n−j)` and the loop budget is `36·L²+39·L`. -/
theorem Compile.moveRegion2TM_run (s : State) (src dst1 dst2 : Var) (res_in : List Nat)
    (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2) (hd12 : dst1 ≠ dst2)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res_in) :
    ∃ t, runFlatTM t (Compile.moveRegion2TM src dst1 dst2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
      = some { state_idx := Compile.moveRegion2TM_exit src dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set dst1 (s.get dst1 ++ s.get src)).set dst2 (s.get dst2 ++ s.get src)).set src [])
                   ++ (res_in ++ List.replicate (s.get src).length 0))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveRegion2TM src dst1 dst2)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } = some ck →
          ck.state_idx ≠ Compile.moveRegion2TM_exit src dst1 dst2 ∧
          haltingStateReached (Compile.moveRegion2TM src dst1 dst2) ck = false)
      ∧ t ≤ 36 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
              + 39 * (Compile.encodeTape s ++ res_in).length := by
  set n := (s.get src).length with hn
  set st : Nat → State := fun m =>
    ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2 (s.get dst2 ++ (s.get src).take m)).set src
      ((s.get src).drop m) with hstdef
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 0, Compile.encodeTape (st (n - j)) ++ (res_in ++ List.replicate (n - j) 0)) with hTdef
  set L := (Compile.encodeTape s ++ res_in).length with hLdef
  have hv_bit : ∀ x ∈ s.get src, x ≤ 1 := Compile.BitState_get s src hbit hsrc
  have hd1_bit : ∀ x ∈ s.get dst1, x ≤ 1 := Compile.BitState_get s dst1 hbit hdst1
  have hd2_bit : ∀ x ∈ s.get dst2, x ≤ 1 := Compile.BitState_get s dst2 hbit hdst2
  have hBstart : (Compile.moveBody2RawTM src dst1 dst2).start = 0 := by
    show (branchComposeFlatTM _ _ _ _ _).start = 0
    rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src
  have hlenP : ∀ (m : Nat),
      (s.set dst1 (s.get dst1 ++ (s.get src).take m)).length = s.length :=
    fun m => Compile.length_set s dst1 _ hdst1
  have hlenQ : ∀ m, ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2
      (s.get dst2 ++ (s.get src).take m)).length = s.length :=
    fun m => by rw [Compile.length_set _ dst2 _ (by rw [hlenP]; exact hdst2), hlenP]
  have hlen_st : ∀ m, (st m).length = s.length := fun m => by
    simp only [hstdef]; rw [Compile.length_set _ src _ (by rw [hlenQ]; exact hsrc), hlenQ]
  have hget_src_st : ∀ m, (st m).get src = (s.get src).drop m := fun m => by
    simp only [hstdef]; exact Compile.get_set_eq _ src _ (by rw [hlenQ]; exact hsrc)
  have hget_dst1_st : ∀ m, (st m).get dst1 = s.get dst1 ++ (s.get src).take m := fun m => by
    simp only [hstdef]
    rw [Compile.get_set_ne _ src _ dst1 (by rw [hlenQ]; exact hsrc) (Ne.symm hsd1),
        Compile.get_set_ne _ dst2 _ dst1 (by rw [hlenP]; exact hdst2) hd12,
        Compile.get_set_eq s dst1 _ hdst1]
  have hget_dst2_st : ∀ m, (st m).get dst2 = s.get dst2 ++ (s.get src).take m := fun m => by
    simp only [hstdef]
    rw [Compile.get_set_ne _ src _ dst2 (by rw [hlenQ]; exact hsrc) (Ne.symm hsd2),
        Compile.get_set_eq _ dst2 _ (by rw [hlenP]; exact hdst2)]
  have hbit_st : ∀ m, Compile.BitState (st m) := fun m => by
    simp only [hstdef]
    refine Compile.BitState_set _ src _ ?_ (by rw [hlenQ]; exact hsrc)
      (fun x hx => hv_bit x (List.mem_of_mem_drop hx))
    refine Compile.BitState_set _ dst2 _ ?_ (by rw [hlenP]; exact hdst2) ?_
    · refine Compile.BitState_set s dst1 _ hbit hdst1 ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hd1_bit x hx
      · exact hv_bit x (List.mem_of_mem_take hx)
    · intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hd2_bit x hx
      · exact hv_bit x (List.mem_of_mem_take hx)
  -- size of `st m` grows by `m` (each moved bit is duplicated into dst1 and dst2).
  have hsize_st : ∀ m, m ≤ n → State.size (st m) = State.size s + m := by
    intro m hm
    have htake : ((s.get src).take m).length = m := by rw [List.length_take, ← hn]; omega
    have hdrop : ((s.get src).drop m).length = n - m := by rw [List.length_drop, ← hn]
    have e1 := State.size_set_add s dst1 (s.get dst1 ++ (s.get src).take m)
    have hP_d2 : (s.set dst1 (s.get dst1 ++ (s.get src).take m)).get dst2 = s.get dst2 :=
      Compile.get_set_ne s dst1 _ dst2 hdst1 (Ne.symm hd12)
    have e2 := State.size_set_add (s.set dst1 (s.get dst1 ++ (s.get src).take m)) dst2
      (s.get dst2 ++ (s.get src).take m)
    rw [hP_d2] at e2
    have hQ_src : ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2
        (s.get dst2 ++ (s.get src).take m)).get src = s.get src := by
      rw [Compile.get_set_ne _ dst2 _ src (by rw [hlenP]; exact hdst2) hsd2,
          Compile.get_set_ne s dst1 _ src hdst1 hsd1]
    have e3 := State.size_set_add ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2
      (s.get dst2 ++ (s.get src).take m)) src ((s.get src).drop m)
    rw [hQ_src] at e3
    simp only [hstdef, List.length_append, htake, hdrop] at e1 e2 e3 ⊢
    omega
  have hTlen : ∀ j, j ≤ n → (T j).2.2.length = L + 2 * (n - j) := by
    intro j hj
    simp only [hTdef, List.length_append, List.length_replicate]
    rw [Compile.encodeTape_length, hsize_st (n - j) (Nat.sub_le n j), hlen_st,
        hLdef, List.length_append, Compile.encodeTape_length]
    omega
  have hnL : n + 2 ≤ L := by
    have hsize := State.size_set_add s src ([] : List Nat)
    simp only [List.length_nil, Nat.add_zero] at hsize
    rw [hLdef, List.length_append, Compile.encodeTape_length]
    omega
  have hT_lt : ∀ j x, x ∈ (T j).2.2 → x < 4 := by
    intro j x hx
    simp only [hTdef] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four _ (hbit_st _) x hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hres x hx).1
      · rw [List.mem_replicate] at hx; omega
  have h_sym : ∀ m v, currentTapeSymbol (T m) = some v → v < (Compile.moveBody2RawTM src dst1 dst2).sig := by
    intro m v hv
    have hsig : (Compile.moveBody2RawTM src dst1 dst2).sig = 4 := by
      show (branchComposeFlatTM _ _ _ _ _).sig = 4
      rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig, Compile.moveContent2TM_sig]; rfl
    rw [hsig]
    have hmem : v ∈ (T m).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_lt m v hmem
  -- done branch: `T 0`, register `src` empty.
  have hdone := Compile.moveBody2_done_run (st n) src dst1 dst2 (res_in ++ List.replicate n 0)
    (by rw [hlen_st]; exact hsrc) (hbit_st n)
    (by rw [hget_src_st, hn]; exact List.drop_length)
    (Compile.ValidResidue_append_replicate_zero res_in n hres)
  obtain ⟨tDone, hdr, hdt, hdb⟩ := hdone
  have hT0 : T 0 = ([], 0, Compile.encodeTape (st n) ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero]
  have h_done_bnd : tDone + 1 ≤ 36 * L + 39 := by
    have hlen0 := hTlen 0 (Nat.zero_le n)
    simp only [hTdef, Nat.sub_zero] at hlen0
    rw [hlen0] at hdb
    have : n ≤ L := by omega
    omega
  -- per-iteration move: `T (j+1) → T j` for `j < n`, moving one bit to both dsts.
  have hiter_ex : ∀ j, j < n → ∃ t,
      runFlatTM t (Compile.moveBody2RawTM src dst1 dst2)
          { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBody2RawTM_exitLoop src dst1 dst2, tapes := [T j] } ∧
      (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
            { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] } = some ck →
        ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
        ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
        haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false) ∧
      t ≤ 36 * L + 38 := by
    intro j hj
    set m := n - (j + 1) with hm
    have hmn : m < n := by omega
    have hm1 : m + 1 = n - j := by omega
    have hmlen : m < (s.get src).length := by rw [← hn]; exact hmn
    have hdc : (s.get src).drop m = (s.get src)[m] :: (s.get src).drop (m + 1) :=
      List.drop_eq_getElem_cons hmlen
    have hb1 : (s.get src)[m] ≤ 1 := hv_bit _ (List.getElem_mem hmlen)
    have hsrc_cons : (st m).get src = (s.get src)[m] :: (s.get src).drop (m + 1) := by
      rw [hget_src_st]; exact hdc
    obtain ⟨t, hr, ht, hbnd⟩ := Compile.moveBody2_delete_run (st m) src dst1 dst2 ((s.get src)[m])
      ((s.get src).drop (m + 1)) hsrc_cons hb1 hsd1 hsd2 hd12 (hbit_st m)
      (by rw [hlen_st]; exact hsrc) (by rw [hlen_st]; exact hdst1) (by rw [hlen_st]; exact hdst2)
      (res_in ++ List.replicate m 0)
      (Compile.ValidResidue_append_replicate_zero res_in m hres)
    -- bridge the dual-move output to `T j` (3-register reshuffle).
    have hsrcQ : ∀ (m' : Nat), src < ((s.set dst1 (s.get dst1 ++ (s.get src).take m')).set dst2
        (s.get dst2 ++ (s.get src).take m')).length := fun m' => by rw [hlenQ]; exact hsrc
    have hstate_eq : (((st m).set src ((s.get src).drop (m + 1))).set dst1
          ((st m).get dst1 ++ [(s.get src)[m]])).set dst2 ((st m).get dst2 ++ [(s.get src)[m]])
        = st (n - j) := by
      rw [hget_dst1_st, hget_dst2_st, ← hm1,
          show (s.get dst1 ++ (s.get src).take m) ++ [(s.get src)[m]]
            = s.get dst1 ++ (s.get src).take (m + 1) from by
            rw [List.append_assoc, List.take_succ_eq_append_getElem hmlen],
          show (s.get dst2 ++ (s.get src).take m) ++ [(s.get src)[m]]
            = s.get dst2 ++ (s.get src).take (m + 1) from by
            rw [List.append_assoc, List.take_succ_eq_append_getElem hmlen]]
      simp only [hstdef]
      -- normalize LHS to `((s.set dst1 X).set dst2 Y).set src Z`.
      rw [Compile.set_set _ src _ _ (hsrcQ m)]
      rw [Compile.set_comm _ dst1 dst2 _ _ (by rw [Compile.length_set _ src _ (hsrcQ m), hlenQ]; exact hdst1)
            (by rw [Compile.length_set _ src _ (hsrcQ m), hlenQ]; exact hdst2) hd12]
      rw [Compile.set_comm _ src dst2 _ _ (hsrcQ m)
            (by rw [hlenQ]; exact hdst2) hsd2]
      rw [Compile.set_set _ dst2 _ _ (by rw [hlenP]; exact hdst2)]
      rw [Compile.set_comm _ src dst1 _ _ (by rw [Compile.length_set _ dst2 _ (by rw [hlenP]; exact hdst2), hlenP]; exact hsrc)
            (by rw [Compile.length_set _ dst2 _ (by rw [hlenP]; exact hdst2), hlenP]; exact hdst1) hsd1]
      rw [Compile.set_comm _ dst2 dst1 _ _ (by rw [hlenP]; exact hdst2)
            (by rw [hlenP]; exact hdst1) (Ne.symm hd12)]
      rw [Compile.set_set _ dst1 _ _ hdst1]
    have hres_eq : (res_in ++ List.replicate m 0) ++ [0] = res_in ++ List.replicate (n - j) 0 := by
      rw [List.append_assoc, ← List.replicate_succ', hm1]
    rw [hstate_eq, hres_eq] at hr
    have hlenj := hTlen (j + 1) (by omega)
    simp only [hTdef] at hlenj
    rw [show n - (j + 1) = m from rfl] at hlenj
    rw [hlenj] at hbnd
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact hr
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact ht
    · have : m ≤ n := by omega
      omega
  set tIter : Nat → Nat := fun j => if hj : j < n then (hiter_ex j hj).choose else 0 with htIter
  have h_done_full :
      runFlatTM tDone (Compile.moveBody2RawTM src dst1 dst2)
          { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T 0] }
        = some { state_idx := Compile.moveBody2RawTM_exitDone src dst1 dst2, tapes := [T 0] } ∧
      (∀ k, k < tDone → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false) := by
    refine ⟨?_, ?_⟩
    · rw [hBstart, hT0]; exact hdr
    · rw [hBstart, hT0]; exact hdt
  have h_iter_full : ∀ j, j < n →
      runFlatTM (tIter j) (Compile.moveBody2RawTM src dst1 dst2)
          { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBody2RawTM_exitLoop src dst1 dst2, tapes := [T j] } ∧
      (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false) := by
    intro j hj
    have hspec := (hiter_ex j hj).choose_spec
    simp only [htIter, dif_pos hj]
    exact ⟨hspec.1, hspec.2.1⟩
  have h_iter_bnd : ∀ j, j < n → tIter j + 1 ≤ 36 * L + 39 := by
    intro j hj
    have hb := (hiter_ex j hj).choose_spec.2.2
    simp only [htIter, dif_pos hj]
    omega
  have hmain := loopTM_run (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)
    (Compile.moveBody2RawTM_valid src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_lt src dst1 dst2) (Compile.moveBody2RawTM_exitLoop_lt src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_ne_exitLoop src dst1 dst2) T h_sym tIter tDone h_done_full n h_iter_full
  have hmain_traj := loopTM_no_early_halt (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)
    (Compile.moveBody2RawTM_valid src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_lt src dst1 dst2) (Compile.moveBody2RawTM_exitLoop_lt src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_ne_exitLoop src dst1 dst2) T h_sym tIter tDone h_done_full n h_iter_full
  have hTn : T n = ([], 0, Compile.encodeTape s ++ res_in) := by
    simp only [hTdef, Nat.sub_self]
    rw [hstdef]
    simp only [List.take_zero, List.drop_zero, List.append_nil, List.replicate_zero]
    rw [Compile.set_get_self s dst1 hdst1, Compile.set_get_self s dst2 hdst2,
        Compile.set_get_self s src hsrc]
  have hTfin : T 0 = ([], 0, Compile.encodeTape
      (((s.set dst1 (s.get dst1 ++ s.get src)).set dst2 (s.get dst2 ++ s.get src)).set src [])
      ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero, hstdef]
    rw [show (s.get src).take n = s.get src from by rw [hn]; exact List.take_length,
        show (s.get src).drop n = [] from by rw [hn]; exact List.drop_length]
  rw [hBstart, hTn, hTfin] at hmain
  rw [hBstart, hTn] at hmain_traj
  have hMeq : Compile.moveRegion2TM src dst1 dst2
      = loopTM (Compile.moveBody2RawTM src dst1 dst2) (Compile.moveBody2RawTM_exitDone src dst1 dst2)
          (Compile.moveBody2RawTM_exitLoop src dst1 dst2) := rfl
  have hExeq : Compile.moveRegion2TM_exit src dst1 dst2 = (Compile.moveBody2RawTM src dst1 dst2).states := rfl
  have hexit_halt : (Compile.moveRegion2TM src dst1 dst2).halt[(Compile.moveBody2RawTM src dst1 dst2).states]?
      = some true := by
    rw [hMeq]
    show (loopHalt (Compile.moveBody2RawTM src dst1 dst2))[(Compile.moveBody2RawTM src dst1 dst2).states]? = some true
    show (List.replicate (Compile.moveBody2RawTM src dst1 dst2).states false ++ [true])[(Compile.moveBody2RawTM src dst1 dst2).states]?
        = some true
    rw [List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  refine ⟨loopBudget tIter tDone n, ?_, ?_, ?_⟩
  · rw [hMeq, hExeq]; exact hmain
  · intro k hk ck hck
    rw [hMeq] at hck
    have hh := hmain_traj k hk ck hck
    refine ⟨?_, hh⟩
    rw [hExeq]
    rw [hMeq] at hexit_halt
    exact ClearGadget.ne_of_not_halting hexit_halt hh
  · rw [hLdef] at hnL ⊢
    exact le_trans
      (Compile.loopBudget_le tIter tDone (36 * L + 39) n h_done_bnd h_iter_bnd)
      (by rw [← hLdef]; exact Compile.moveBudget2_arith n L (by rw [hLdef]; exact hnL))

/-- **`clearAppendM` run + no-early-halt + budget.** From head `0` on
`encodeTape s ++ res`, clearing register `dst` then appending bit `bit` reaches
the unique exit at head `0` with tape `encodeTape (s.set dst [bit]) ++ res'`
(`res' = res ++ replicate |s.get dst| 0`). The tape length is preserved, so the
append's budget is `≤ 3·L + 8` and the total is `≤ 9·L² + 3·L + 18`. -/
theorem Compile.clearAppendM_run (s : State) (dst : Var) (bit : Nat) (hb : bit ≤ 1)
    (hdst : dst < s.length) (hbit : Compile.BitState s) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.clearAppendM dst (bit + 1) (by omega))
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.clearAppendM_exit dst (bit + 1) (by omega),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [bit])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.clearAppendM dst (bit + 1) (by omega))
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.clearAppendM dst (bit + 1) (by omega)) ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 3 * (Compile.encodeTape s ++ res).length + 18 := by
  set res' := res ++ List.replicate (s.get dst).length 0 with hres'def
  have hmid_bit : Compile.BitState (s.set dst []) :=
    Compile.BitState_set s dst [] hbit hdst (by intro x hx; cases hx)
  have hmid_len : dst < (s.set dst []).length := by
    rw [Compile.length_set s dst [] hdst]; exact hdst
  have hres' : Compile.ValidResidue res' :=
    Compile.ValidResidue_append_replicate_zero res _ hres
  have hget : (s.set dst []).get dst = [] := Compile.get_set_eq s dst [] hdst
  have hset : (s.set dst []).set dst [bit] = s.set dst [bit] := Compile.set_set s dst [] [bit] hdst
  -- tape length preserved across clear: |encodeTape (s.set dst []) ++ res'| = |encodeTape s ++ res|
  have hlen_eq : (Compile.encodeTape (s.set dst []) ++ res').length
      = (Compile.encodeTape s ++ res).length := by
    have hbal := Compile.encodeTape_set_length s dst [] hdst
    simp only [List.length_nil, Nat.add_zero] at hbal
    simp only [hres'def, List.length_append, List.length_replicate]
    omega
  obtain ⟨t1, hrun1, htraj1, hbud1⟩ := Compile.clearRegionTM_run s dst res hdst hbit hres
  obtain ⟨t2, hrun2, htraj2, hbud2⟩ :=
    Compile.opAppendBit_physical_residue bit hb (s.set dst []) dst hmid_bit hmid_len res' hres'
  -- clean the append output tape: (s.set dst []).set dst ([] ++ [bit]) = s.set dst [bit]
  rw [hget, List.nil_append, hset] at hrun2
  -- expose the explicit start config of `opAppendBitRewind` (initFlatConfig form)
  simp only [initFlatConfig, List.map_cons, List.map_nil] at hrun2
  -- `clearRegionTM`'s exit tape is `encodeTape (s.set dst []) ++ res'` (defeq Op.eval)
  have hmid_eval : Op.eval (Op.clear dst) s = s.set dst [] := rfl
  rw [hmid_eval] at hrun1
  -- symbol bound at the seam
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape (s.set dst []) ++ res')
      = some v → v < max (ClearGadget.clearRegionTM dst).sig
        (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M.sig := by
    intro v hv
    have hmax : max (ClearGadget.clearRegionTM dst).sig
        (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M.sig = 4 := by
      rw [ClearGadget.clearRegionTM_sig, (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M_sig]
      rfl
    rw [hmax]
    have hlt : 0 < (Compile.encodeTape (s.set dst []) ++ res').length := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have hcell : (Compile.encodeTape (s.set dst []) ++ res').get ⟨0, hlt⟩ = 3 := rfl
    rw [hcell] at hv
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_cfg_lt : (0 : Nat) < (ClearGadget.clearRegionTM dst).states := by
    rw [ClearGadget.clearRegionTM_states]; exact Nat.succ_pos _
  have hcompose := composeFlatTM_run (ClearGadget.clearRegionTM_valid dst)
    (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M_valid
    (Compile.clearRegionTM_exit_lt dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    h_cfg_lt
    [] 0 (Compile.encodeTape (s.set dst []) ++ res') h_sym
    hrun1
    (fun k hk ck hck => htraj1 k hk ck hck)
    hrun2
    (Compile.haltingStateReached_of_halt (Compile.opAppendBitRewind (bit + 1) (by omega) dst).exit_is_halt)
  have hcompose_traj := composeFlatTM_no_early_halt (ClearGadget.clearRegionTM_valid dst)
    (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M_valid
    (Compile.clearRegionTM_exit_lt dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    h_cfg_lt
    [] 0 (Compile.encodeTape (s.set dst []) ++ res') h_sym
    hrun1
    (fun k hk ck hck => htraj1 k hk ck hck)
    (fun k hk ck hck => (htraj2 k hk ck hck).2)
  refine ⟨t1 + 1 + t2, ?_, ?_, ?_⟩
  · rw [Compile.clearAppendM, Compile.clearAppendM_exit, Nat.add_comm (ClearGadget.clearRegionTM dst).states]
    exact hcompose.1
  · intro k hk ck hck
    rw [Compile.clearAppendM] at hck ⊢
    exact hcompose_traj k hk ck hck
  · -- budget: t1 ≤ 9L²+9, t2 ≤ 3L+8 (length preserved), total ≤ 9L²+3L+18
    have hb2' : t2 ≤ 3 * (Compile.encodeTape s ++ res).length + 8 := by
      rw [← hlen_eq]; exact hbud2
    omega

/-- **`nonEmptyBranchBody` run + no-early-halt + budget.** From the `navigateAndTest`
exit config (head on register `src`'s first cell), rewind to the leading sentinel,
then clear-and-append. Exits at head `0` with `encodeTape (s.set dst [bit]) ++ res'`. -/
theorem Compile.nonEmptyBranchBody_run (s : State) (dst src : Var) (bit : Nat) (hb : bit ≤ 1)
    (hdst : dst < s.length) (hsrc : src < s.length) (hbit : Compile.BitState s)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.nonEmptyBranchBody dst (bit + 1) (by omega))
          { state_idx := 0,
            tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst (bit + 1) (by omega),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [bit])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst (bit + 1) (by omega))
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst (bit + 1) (by omega)) ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 4 * (Compile.encodeTape s ++ res).length + 19 := by
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set rest := Compile.encodeRegs s ++ [Compile.endMark] ++ res with hrestdef
  have htape_cons : Compile.encodeTape s ++ res = (3 : Nat) :: rest := by
    rw [hrestdef, Compile.encodeTape]; simp only [Compile.endMark, List.cons_append, List.append_assoc]
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  -- rewind run + trajectory
  have hcells : ∀ i, i < H → ∃ (h : i < rest.length),
      rest.get ⟨i, h⟩ < 4 ∧ rest.get ⟨i, h⟩ ≠ 3 := by
    intro i hi
    have hi_regs : i < (Compile.encodeRegs s).length := lt_of_lt_of_le hi hH_le_regs
    have hi_rest : i < rest.length := by
      rw [hrestdef, List.length_append, List.length_append]; omega
    have hget : rest.get ⟨i, hi_rest⟩ = (Compile.encodeRegs s).get ⟨i, hi_regs⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      have hget? : rest[i]? = (Compile.encodeRegs s)[i]? := by
        conv_lhs => rw [hrestdef]
        rw [List.getElem?_append_left (by rw [List.length_append]; omega),
            List.getElem?_append_left hi_regs]
      rw [List.getElem?_eq_getElem hi_rest, List.getElem?_eq_getElem hi_regs] at hget?
      exact Option.some.inj hget?
    refine ⟨hi_rest, ?_, ?_⟩
    · rw [hget]; exact Compile.encodeRegs_lt_four s hbit _ (List.get_mem _ _)
    · rw [hget]; exact Compile.encodeRegs_no_endMark s hbit _ (List.get_mem _ _)
  have hH_le_rest : H ≤ rest.length := by
    rw [hrestdef, List.length_append, List.length_append]; omega
  -- `3 :: rest` is defeq `encodeTape s ++ res` (cons_append), so `hrw` plugs in directly.
  have hrw := ScanLeft.rewindToStart_run 4 3 [] rest H hH_le_rest hcells
  have hrw_traj := ScanLeft.rewindToStart_traj 4 3 [] rest H hH_le_rest hcells
  -- clearAppend run (head 0); convert its start to M₂.start form
  obtain ⟨t2, hca_run, hca_traj, hca_bud⟩ := Compile.clearAppendM_run s dst bit hb hdst hbit res hres
  have hca_start : (Compile.clearAppendM dst (bit + 1) (by omega)).start = 0 := by
    rw [Compile.clearAppendM, composeFlatTM_start]; exact ClearGadget.clearRegionTM_start dst
  have hca_run' : runFlatTM t2 (Compile.clearAppendM dst (bit + 1) (by omega))
      { state_idx := (Compile.clearAppendM dst (bit + 1) (by omega)).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.clearAppendM_exit dst (bit + 1) (by omega),
               tapes := [([], 0, Compile.encodeTape (s.set dst [bit])
                          ++ (res ++ List.replicate (s.get dst).length 0))] } := by
    rw [hca_start]; exact hca_run
  have hca_traj' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k (Compile.clearAppendM dst (bit + 1) (by omega))
        { state_idx := (Compile.clearAppendM dst (bit + 1) (by omega)).start,
          tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.clearAppendM dst (bit + 1) (by omega)) ck = false := by
    rw [hca_start]; exact hca_traj
  -- symbol bound at the rewind exit head (head 0 = leading sentinel)
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (ScanLeft.scanLeftUntilTM 4 3).sig
        (Compile.clearAppendM dst (bit + 1) (by omega)).sig := by
    intro v hv
    have hmax : max (ScanLeft.scanLeftUntilTM 4 3).sig
        (Compile.clearAppendM dst (bit + 1) (by omega)).sig = 4 := by
      rw [Compile.clearAppendM_sig]; rfl
    rw [hmax]
    have hlt : 0 < (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have hcell : (Compile.encodeTape s ++ res).get ⟨0, hlt⟩ = 3 := rfl
    rw [hcell] at hv
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_cfg_lt : (0 : Nat) < (ScanLeft.scanLeftUntilTM 4 3).states := by decide
  have hcompose := composeFlatTM_run (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (Compile.clearAppendM_valid dst (bit + 1) (by omega)) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck) hca_run'
    (Compile.haltingStateReached_of_halt (Compile.clearAppendM_exit_is_halt dst (bit + 1) (by omega)))
  have hcompose_traj := composeFlatTM_no_early_halt (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (Compile.clearAppendM_valid dst (bit + 1) (by omega)) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck)
    (fun k hk ck hck => hca_traj' k hk ck hck)
  refine ⟨(H + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [Compile.nonEmptyBranchBody, Compile.nonEmptyBranchBody_exit,
        Nat.add_comm (ScanLeft.scanLeftUntilTM 4 3).states]
    exact hcompose.1
  · intro k hk ck hck
    rw [Compile.nonEmptyBranchBody] at hck ⊢
    exact hcompose_traj k hk ck hck
  · -- budget: rewind H+1 ≤ L, clearAppend ≤ 9L²+3L+18 ⇒ total ≤ 9L²+4L+19
    have hH_le_L : H + 1 ≤ (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]
      have h1 := hH_le_regs
      have h2 := Compile.encodeRegs_length s
      omega
    omega

/-- **`opNonEmpty` run + trajectory + budget (the residue contract for `nonEmpty`).**
Navtest `src`; the answer bit (`1` if non-empty else `0`) is written to a freshly
cleared register `dst`; the two branches merge through `joinTwoHalts`. Correct for
`dst = src` (the read precedes the clear). -/
theorem Compile.opNonEmpty_run (s : State) (dst src : Var) (res_in : List Nat)
    (hbit : Compile.BitState s) (hdst : dst < s.length) (hsrc : src < s.length)
    (hres_in : Compile.ValidResidue res_in) :
    ∃ t,
      runFlatTM t (Compile.opNonEmpty dst src).M
          (initFlatConfig (Compile.opNonEmpty dst src).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opNonEmpty dst src).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval (Op.nonEmpty dst src) s)
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opNonEmpty dst src).M
            (initFlatConfig (Compile.opNonEmpty dst src).M [Compile.encodeTape s ++ res_in]) = some ck →
        ck.state_idx ≠ (Compile.opNonEmpty dst src).exit ∧
        haltingStateReached (Compile.opNonEmpty dst src).M ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
            + 9 * (Compile.encodeTape s ++ res_in).length + 30 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.nonEmptyRawM dst src with hrawdef
  set h1 := Compile.nonEmptyRawM_h1 dst src with hh1def
  set h2 := Compile.nonEmptyRawM_h2 dst src with hh2def
  have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
      (Compile.nonEmptyBranchBody dst 2 (by decide)) (Compile.nonEmptyBranchBody dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content src)
      (ClearGadget.navigateAndTestTM_exit_delim src) = raw := rfl
  -- machine boilerplate: init config, exit, M.
  have hMstart : (Compile.opNonEmpty dst src).M.start = 0 := by
    show (joinTwoHalts raw h1 h2).start = 0
    rw [joinTwoHalts_start, hrawdef, Compile.nonEmptyRawM, branchComposeFlatTM_start]
    exact ClearGadget.navigateAndTestTM_start src
  have hinit : initFlatConfig (Compile.opNonEmpty dst src).M [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hMstart, List.map_cons, List.map_nil]
  have hMeq : (Compile.opNonEmpty dst src).M = joinTwoHalts raw h1 h2 := rfl
  have hexit : (Compile.opNonEmpty dst src).exit = h1 := rfl
  rw [hinit, hMeq, hexit]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    with hcfg0
  -- length facts.
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res_in).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  have hnav_le : ClearGadget.navSteps skipped ≤ 2 * (Compile.encodeRegs s).length := by
    have := ClearGadget.navSteps_le skipped
    rw [hHdef] at hH_le_regs; omega
  -- the branch-tape symbol bound (head H lands inside `encodeTape s`).
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res_in)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.nonEmptyBranchBody dst 2 (by decide)).sig
            (Compile.nonEmptyBranchBody dst 1 (by decide)).sig) := by
    intro v hv
    have hHlt2 : H < (Compile.encodeTape s).length := by
      rw [Compile.encodeTape_length]
      have h := hH_le_regs
      rw [Compile.encodeRegs_length] at h
      omega
    have hHlt : H < (Compile.encodeTape s ++ res_in).length := by
      rw [List.length_append]; omega
    rw [currentTapeSymbol_in_range hHlt] at hv
    have hmem : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ ∈ Compile.encodeTape s := by
      rw [List.get_eq_getElem, List.getElem_append_left hHlt2]; exact List.getElem_mem hHlt2
    have hv4 : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ < 4 :=
      Compile.encodeTape_lt_four s hbit _ hmem
    have : v < (ClearGadget.navigateAndTestTM src).sig := by
      rw [ClearGadget.navigateAndTestTM_sig, ← Option.some.inj hv]; exact hv4
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hbstart : ∀ ins (h : ins < 4), (Compile.nonEmptyBranchBody dst ins h).start = 0 := by
    intro ins h; rw [Compile.nonEmptyBranchBody, composeFlatTM_start]; rfl
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hh1_is := Compile.nonEmptyRawM_h1_is_halt dst src
  have hh2_is := Compile.nonEmptyRawM_h2_is_halt dst src
  have hh_ne := Compile.nonEmptyRawM_h1_ne_h2 dst src
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  by_cases he : s.get src = []
  · -- DELIM: answer bit 0, Op.eval = s.set dst [0]; raw reaches h2, bridges to h1.
    have hisE : Op.eval (Op.nonEmpty dst src) s = s.set dst [0] := by
      show s.set dst (if (s.get src).isEmpty then [0] else [1]) = s.set dst [0]
      rw [he]; rfl
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 0 (by omega) hdst hsrc hbit res_in hres_in
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 1 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 1 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [0])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 1 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 1 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 1 (by decide)) ck = false := by
      rw [hbstart 1 (by decide)]; exact hbody_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 1 (by decide)))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody_traj'
    -- recognise the branch machine/state as raw/h2.
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 1 (by decide)
        + ((ClearGadget.navigateAndTestTM src).states
            + (Compile.nonEmptyBranchBody dst 2 (by decide)).states) = h2 := by
      rw [hh2def, Compile.nonEmptyRawM_h2]; omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (s.set dst [0]) ++ (res_in ++ List.replicate (s.get dst).length 0)) 0
      hneg.1
      (fun k hk ck hck => hneg_traj k hk ck hck)
      hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (s.set dst [0]) ++ (res_in ++ List.replicate (s.get dst).length 0))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.nonEmptyRawM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega
  · -- CONTENT: answer bit 1, Op.eval = s.set dst [1]; raw reaches h1 directly.
    have hisE : Op.eval (Op.nonEmpty dst src) s = s.set dst [1] := by
      show s.set dst (if (s.get src).isEmpty then [0] else [1]) = s.set dst [1]
      have : (s.get src).isEmpty = false := by
        cases hsr : s.get src with
        | nil => exact absurd hsr he
        | cons _ _ => rfl
      rw [this]; rfl
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 1 (by omega) hdst hsrc hbit res_in hres_in
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 2 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 2 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [1])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 2 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 2 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 2 (by decide)) ck = false := by
      rw [hbstart 2 (by decide)]; exact hbody_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 2 (by decide)))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody_traj'
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 2 (by decide)
        + (ClearGadget.navigateAndTestTM src).states = h1 := by
      rw [hh1def, Compile.nonEmptyRawM_h1]; omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (s.set dst [1]) ++ (res_in ++ List.replicate (s.get dst).length 0))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega

/-- **`clearOnlyBranchBody` run + no-early-halt + budget.** From the navtest exit
config (head on register `src`'s first cell), rewind to the leading sentinel, then
clear `dst`. Exits at head `0` with `encodeTape (s.set dst []) ++ res'`. Mirror of
`nonEmptyBranchBody_run` with `clearRegionTM` in place of `clearAppendM`. -/
theorem Compile.clearOnlyBranchBody_run (s : State) (dst src : Var)
    (hdst : dst < s.length) (hsrc : src < s.length) (hbit : Compile.BitState s)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.clearOnlyBranchBody dst)
          { state_idx := 0,
            tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.clearOnlyBranchBody_exit dst,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.clearOnlyBranchBody dst)
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.clearOnlyBranchBody dst) ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 4 * (Compile.encodeTape s ++ res).length + 19 := by
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set rest := Compile.encodeRegs s ++ [Compile.endMark] ++ res with hrestdef
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  have hcells : ∀ i, i < H → ∃ (h : i < rest.length),
      rest.get ⟨i, h⟩ < 4 ∧ rest.get ⟨i, h⟩ ≠ 3 := by
    intro i hi
    have hi_regs : i < (Compile.encodeRegs s).length := lt_of_lt_of_le hi hH_le_regs
    have hi_rest : i < rest.length := by
      rw [hrestdef, List.length_append, List.length_append]; omega
    have hget : rest.get ⟨i, hi_rest⟩ = (Compile.encodeRegs s).get ⟨i, hi_regs⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      have hget? : rest[i]? = (Compile.encodeRegs s)[i]? := by
        conv_lhs => rw [hrestdef]
        rw [List.getElem?_append_left (by rw [List.length_append]; omega),
            List.getElem?_append_left hi_regs]
      rw [List.getElem?_eq_getElem hi_rest, List.getElem?_eq_getElem hi_regs] at hget?
      exact Option.some.inj hget?
    refine ⟨hi_rest, ?_, ?_⟩
    · rw [hget]; exact Compile.encodeRegs_lt_four s hbit _ (List.get_mem _ _)
    · rw [hget]; exact Compile.encodeRegs_no_endMark s hbit _ (List.get_mem _ _)
  have hH_le_rest : H ≤ rest.length := by
    rw [hrestdef, List.length_append, List.length_append]; omega
  have hrw := ScanLeft.rewindToStart_run 4 3 [] rest H hH_le_rest hcells
  have hrw_traj := ScanLeft.rewindToStart_traj 4 3 [] rest H hH_le_rest hcells
  obtain ⟨t2, hcl_run, hcl_traj, hcl_bud⟩ := Compile.clearRegionTM_run s dst res hdst hbit hres
  have hcl_eval : Op.eval (Op.clear dst) s = s.set dst [] := rfl
  rw [hcl_eval] at hcl_run
  have hcl_start : (ClearGadget.clearRegionTM dst).start = 0 := ClearGadget.clearRegionTM_start dst
  have hcl_run' : runFlatTM t2 (ClearGadget.clearRegionTM dst)
      { state_idx := (ClearGadget.clearRegionTM dst).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.clearRegionTM_exit dst,
               tapes := [([], 0, Compile.encodeTape (s.set dst [])
                          ++ (res ++ List.replicate (s.get dst).length 0))] } := by
    rw [hcl_start]; exact hcl_run
  have hcl_traj' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k (ClearGadget.clearRegionTM dst)
        { state_idx := (ClearGadget.clearRegionTM dst).start,
          tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (ClearGadget.clearRegionTM dst) ck = false := by
    rw [hcl_start]; intro k hk ck hck; exact (hcl_traj k hk ck hck).2
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (ScanLeft.scanLeftUntilTM 4 3).sig (ClearGadget.clearRegionTM dst).sig := by
    intro v hv
    have hmax : max (ScanLeft.scanLeftUntilTM 4 3).sig (ClearGadget.clearRegionTM dst).sig = 4 := by
      rw [ClearGadget.clearRegionTM_sig]; rfl
    rw [hmax]
    have hlt : 0 < (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have hcell : (Compile.encodeTape s ++ res).get ⟨0, hlt⟩ = 3 := rfl
    rw [hcell] at hv
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_cfg_lt : (0 : Nat) < (ScanLeft.scanLeftUntilTM 4 3).states := by decide
  have hcompose := composeFlatTM_run (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (ClearGadget.clearRegionTM_valid dst) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck) hcl_run'
    (Compile.haltingStateReached_of_halt (Compile.opClear dst).exit_is_halt)
  have hcompose_traj := composeFlatTM_no_early_halt (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (ClearGadget.clearRegionTM_valid dst) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck)
    (fun k hk ck hck => hcl_traj' k hk ck hck)
  refine ⟨(H + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [Compile.clearOnlyBranchBody, Compile.clearOnlyBranchBody_exit,
        Nat.add_comm (ScanLeft.scanLeftUntilTM 4 3).states]
    exact hcompose.1
  · intro k hk ck hck
    rw [Compile.clearOnlyBranchBody] at hck ⊢
    exact hcompose_traj k hk ck hck
  · have hH_le_L : H + 1 ≤ (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]
      have h1 := hH_le_regs
      have h2 := Compile.encodeRegs_length s
      omega
    omega

/-- **`opInnerBit` run + trajectory + budget.** From the navtest content exit
(head on `src`'s first cell, value `b+1`), `bitReadTM` reads the bit and writes
`[b]` to a freshly-cleared `dst`. The two `bitReadTM` exits merge via
`joinTwoHalts`. Requires `src` non-empty (`s.get src = b :: r`). -/
theorem Compile.opInnerBit_run (s : State) (dst src : Var) (b : Nat) (r : List Nat)
    (hbr : s.get src = b :: r) (hb1 : b ≤ 1)
    (hbit : Compile.BitState s) (hdst : dst < s.length) (hsrc : src < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.opInnerBit dst).M
          { state_idx := 0,
            tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := (Compile.opInnerBit dst).exit,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [b])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opInnerBit dst).M
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ (Compile.opInnerBit dst).exit ∧
        haltingStateReached (Compile.opInnerBit dst).M ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 5 * (Compile.encodeTape s ++ res).length + 24 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.innerBitRawM dst with hrawdef
  set h1 := Compile.innerBitRawM_h1 dst with hh1def
  set h2 := Compile.innerBitRawM_h2 dst with hh2def
  have hraweq : branchComposeFlatTM Compile.bitReadTM
      (Compile.nonEmptyBranchBody dst 2 (by decide)) (Compile.nonEmptyBranchBody dst 1 (by decide))
      Compile.bitReadTM_exit_b1 Compile.bitReadTM_exit_b0 = raw := rfl
  have hMeq : (Compile.opInnerBit dst).M = joinTwoHalts raw h1 h2 := rfl
  have hexit : (Compile.opInnerBit dst).exit = h1 := rfl
  rw [hMeq, hexit]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    with hcfg0
  -- length facts.
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  -- content decomposition (`src` nonempty)
  set tail' := Compile.shiftReg r ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src hsrc
    rw [← hskdef] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg r := by
      rw [hbr]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hHlt : H < (Compile.encodeTape s ++ res).length := by
    rw [hdecomp, hHdef]; simp only [List.length_cons, List.length_append]; omega
  have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = b + 1 := by
    have h? : (Compile.encodeTape s ++ res)[H]? = some (b + 1) := by
      rw [hdecomp, hHdef,
          show ((3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail'))
            = ((3 : Nat) :: AppendGadget.regBlocks skipped) ++ ((b + 1) :: tail') from by simp,
          List.getElem?_append_right (by simp only [List.length_cons]; omega),
          show 1 + (AppendGadget.regBlocks skipped).length
            - ((3 : Nat) :: AppendGadget.regBlocks skipped).length = 0 from by
              simp only [List.length_cons]; omega]
      rfl
    rw [List.getElem?_eq_getElem hHlt] at h?
    rw [List.get_eq_getElem]; exact Option.some.inj h?
  -- symbol bound at head H (cell value `b+1 < 4`).
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max Compile.bitReadTM.sig
          (max (Compile.nonEmptyBranchBody dst 2 (by decide)).sig
            (Compile.nonEmptyBranchBody dst 1 (by decide)).sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    have : v = b + 1 := (Option.some.inj hv).symm
    rw [Compile.bitReadTM_sig]
    have : v < 4 := by omega
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < Compile.bitReadTM.states := by rw [Compile.bitReadTM_states]; omega
  have hbstart : ∀ ins (h : ins < 4), (Compile.nonEmptyBranchBody dst ins h).start = 0 := by
    intro ins h; rw [Compile.nonEmptyBranchBody, composeFlatTM_start]; rfl
  have hexit_neq : Compile.bitReadTM_exit_b1 ≠ Compile.bitReadTM_exit_b0 := by decide
  have hep_lt : Compile.bitReadTM_exit_b1 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide
  have hen_lt : Compile.bitReadTM_exit_b0 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide
  have hh1_is := Compile.innerBitRawM_h1_is_halt dst
  have hh2_is := Compile.innerBitRawM_h2_is_halt dst
  have hh_ne := Compile.innerBitRawM_h1_ne_h2 dst
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  -- the `bitReadTM` test run + trajectory (reads cell `b+1` at head H).
  have htest_run := Compile.bitReadTM_run b hb1 [] (Compile.encodeTape s ++ res) H hHlt hcellH
  have htest_traj : ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.bitReadTM cfg0 = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧ ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧
      haltingStateReached Compile.bitReadTM ck = false := by
    intro k hk ck hck
    obtain ⟨h0, h1', hh⟩ := Compile.bitReadTM_no_early_halt [] (Compile.encodeTape s ++ res) H k hk ck hck
    exact ⟨h1', h0, hh⟩
  interval_cases b
  · -- bit 0 (cell value 1): neg branch, body `dst 1` writes `[0]`; demoted exit.
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 0 (by omega) hdst hsrc hbit res hres
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 1 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 1 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [0])
                            ++ (res ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 1 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 1 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 1 (by decide)) ck = false := by
      rw [hbstart 1 (by decide)]; exact hbody_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 1 (by decide)))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody_traj'
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 1 (by decide)
        + (Compile.bitReadTM.states + (Compile.nonEmptyBranchBody dst 2 (by decide)).states) = h2 := by
      rw [hh2def, Compile.innerBitRawM_h2]; omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (s.set dst [0]) ++ (res ++ List.replicate (s.get dst).length 0)) 0
      hneg.1
      (fun k hk ck hck => hneg_traj k hk ck hck)
      hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (s.set dst [0]) ++ (res ++ List.replicate (s.get dst).length 0))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.innerBitRawM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hb := hbody_bud
    have hL := hLge
    omega
  · -- bit 1 (cell value 2): pos branch, body `dst 2` writes `[1]`; kept exit.
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 1 (by omega) hdst hsrc hbit res hres
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 2 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 2 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [1])
                            ++ (res ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 2 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 2 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 2 (by decide)) ck = false := by
      rw [hbstart 2 (by decide)]; exact hbody_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 2 (by decide)))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody_traj'
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 2 (by decide)
        + Compile.bitReadTM.states = h1 := by
      rw [hh1def, Compile.innerBitRawM_h1]; omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (s.set dst [1]) ++ (res ++ List.replicate (s.get dst).length 0))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hb := hbody_bud
    have hL := hLge
    omega

/-- **`opHead` run + trajectory + budget (the residue contract for `head`).**
Navtest `src`; on content, `opInnerBit` writes `[first bit]`; on delim,
`clearOnlyBranchBody` writes `[]`. The outer branches merge through `joinTwoHalts`. -/
theorem Compile.opHead_run (s : State) (dst src : Var) (res_in : List Nat)
    (hbit : Compile.BitState s) (hdst : dst < s.length) (hsrc : src < s.length)
    (hres_in : Compile.ValidResidue res_in) :
    ∃ t,
      runFlatTM t (Compile.opHead dst src).M
          (initFlatConfig (Compile.opHead dst src).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opHead dst src).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval (Op.head dst src) s)
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opHead dst src).M
            (initFlatConfig (Compile.opHead dst src).M [Compile.encodeTape s ++ res_in]) = some ck →
        ck.state_idx ≠ (Compile.opHead dst src).exit ∧
        haltingStateReached (Compile.opHead dst src).M ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
            + 9 * (Compile.encodeTape s ++ res_in).length + 30 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.headRawM dst src with hrawdef
  set h1 := Compile.headRawM_h1 dst src with hh1def
  set h2 := Compile.headRawM_h2 dst src with hh2def
  have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
      (Compile.opInnerBit dst).M (Compile.clearOnlyBranchBody dst)
      (ClearGadget.navigateAndTestTM_exit_content src)
      (ClearGadget.navigateAndTestTM_exit_delim src) = raw := rfl
  have hMstart : (Compile.opHead dst src).M.start = 0 := by
    show (joinTwoHalts raw h1 h2).start = 0
    rw [joinTwoHalts_start, hrawdef, Compile.headRawM, branchComposeFlatTM_start]
    exact ClearGadget.navigateAndTestTM_start src
  have hinit : initFlatConfig (Compile.opHead dst src).M [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hMstart, List.map_cons, List.map_nil]
  have hMeq : (Compile.opHead dst src).M = joinTwoHalts raw h1 h2 := rfl
  have hexit : (Compile.opHead dst src).exit = h1 := rfl
  rw [hinit, hMeq, hexit]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    with hcfg0
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res_in).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  have hnav_le : ClearGadget.navSteps skipped ≤ 2 * (Compile.encodeRegs s).length := by
    have := ClearGadget.navSteps_le skipped
    rw [hHdef] at hH_le_regs; omega
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res_in)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.opInnerBit dst).M.sig (Compile.clearOnlyBranchBody dst).sig) := by
    intro v hv
    have hHlt2 : H < (Compile.encodeTape s).length := by
      rw [Compile.encodeTape_length]
      have h := hH_le_regs
      rw [Compile.encodeRegs_length] at h
      omega
    have hHlt : H < (Compile.encodeTape s ++ res_in).length := by
      rw [List.length_append]; omega
    rw [currentTapeSymbol_in_range hHlt] at hv
    have hmem : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ ∈ Compile.encodeTape s := by
      rw [List.get_eq_getElem, List.getElem_append_left hHlt2]; exact List.getElem_mem hHlt2
    have hv4 : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ < 4 :=
      Compile.encodeTape_lt_four s hbit _ hmem
    have : v < (ClearGadget.navigateAndTestTM src).sig := by
      rw [ClearGadget.navigateAndTestTM_sig, ← Option.some.inj hv]; exact hv4
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hh1_is := Compile.headRawM_h1_is_halt dst src
  have hh2_is := Compile.headRawM_h2_is_halt dst src
  have hh_ne := Compile.headRawM_h1_ne_h2 dst src
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  by_cases he : s.get src = []
  · -- DELIM: Op.eval head = s.set dst []; raw reaches h2 (delim), bridges to h1.
    have hisE : Op.eval (Op.head dst src) s = s.set dst [] := by
      show s.set dst (match s.get src with | [] => [] | x :: _ => [x]) = s.set dst []
      rw [he]
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.clearOnlyBranchBody_run s dst src hdst hsrc hbit res_in hres_in
    have hbody' : runFlatTM t2 (Compile.clearOnlyBranchBody dst)
        { state_idx := (Compile.clearOnlyBranchBody dst).start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := Compile.clearOnlyBranchBody_exit dst,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [show (Compile.clearOnlyBranchBody dst).start = 0 from by
            rw [Compile.clearOnlyBranchBody, composeFlatTM_start]; rfl]
      exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.clearOnlyBranchBody dst)
          { state_idx := (Compile.clearOnlyBranchBody dst).start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.clearOnlyBranchBody dst) ck = false := by
      rw [show (Compile.clearOnlyBranchBody dst).start = 0 from by
            rw [Compile.clearOnlyBranchBody, composeFlatTM_start]; rfl]
      exact hbody_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.clearOnlyBranchBody_exit_is_halt dst))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody_traj'
    have hstate_eq : Compile.clearOnlyBranchBody_exit dst
        + ((ClearGadget.navigateAndTestTM src).states + (Compile.opInnerBit dst).M.states) = h2 := by
      rw [hh2def, Compile.headRawM_h2]; omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (s.set dst []) ++ (res_in ++ List.replicate (s.get dst).length 0)) 0
      hneg.1
      (fun k hk ck hck => hneg_traj k hk ck hck)
      hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (s.set dst []) ++ (res_in ++ List.replicate (s.get dst).length 0))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.headRawM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega
  · -- CONTENT: s.get src = b :: r; opInnerBit writes [b]; raw reaches h1 directly.
    obtain ⟨b, r, hbr⟩ : ∃ b r, s.get src = b :: r := by
      cases hsr : s.get src with
      | nil => exact absurd hsr he
      | cons b r => exact ⟨b, r, rfl⟩
    have hb1 : b ≤ 1 := by
      have hmem : s.get src ∈ s := by
        rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
      exact hbit _ hmem b (by simp [hbr])
    have hisE : Op.eval (Op.head dst src) s = s.set dst [b] := by
      show s.set dst (match s.get src with | [] => [] | x :: _ => [x]) = s.set dst [b]
      rw [hbr]
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.opInnerBit_run s dst src b r hbr hb1 hbit hdst hsrc res_in hres_in
    have hbody' : runFlatTM t2 (Compile.opInnerBit dst).M
        { state_idx := (Compile.opInnerBit dst).M.start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := (Compile.opInnerBit dst).exit,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [b])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [Compile.opInnerBit_start]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.opInnerBit dst).M
          { state_idx := (Compile.opInnerBit dst).M.start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.opInnerBit dst).M ck = false := by
      rw [Compile.opInnerBit_start]; intro k hk ck hck; exact (hbody_traj k hk ck hck).2
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.opInnerBit dst).exit_is_halt)
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody_traj'
    have hstate_eq : (Compile.opInnerBit dst).exit
        + (ClearGadget.navigateAndTestTM src).states = h1 := by
      rw [hh1def, Compile.headRawM_h1]; omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (s.set dst [b]) ++ (res_in ++ List.replicate (s.get dst).length 0))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega

