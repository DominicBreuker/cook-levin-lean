import CookLevin.Lang.Semantics
import CookLevin.Lang.Frame
import CookLevin.Lang.AppendGadget
import CookLevin.Lang.ClearGadget
import CookLevin.Basic.TMPrimitives
import CookLevin.Basic.TapeMono
import CookLevin.Lang.Compile.Core
import CookLevin.Lang.Compile.Encoding
import CookLevin.Lang.Compile.OpMachines
import CookLevin.Lang.Compile.Cmd
import CookLevin.Lang.Compile.RunClear

/-!
# Run lemmas: bit transfer, head and the bit tester

Run lemmas for moving a bit between registers, for the `head` operation and for the bit
tester `compileTestBit` used by `ifBit`.
-/

set_option autoImplicit false

namespace CookLevin.Lang

open TMPrimitives
open scoped BigOperators

/-! ### The move-one-bit transfer gadget

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

Example: `encodeTape [[1,0],[1]] → encodeTape [[],[1,1,0]] ++ [0,0]`.
and `encodeTape [[1],[0,1]] → encodeTape [[1,0,1],[]] ++ [0,0]` (residue =
`replicate (#moved bits) 0`). The exit-state offsets below were read off the machine
and verified to make the `loopTM` continue/terminate correctly. -/

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

/-! #### `moveContent` scaffolding (the bit-read branch over the transfer engine). -/

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

/-! #### `compileTestBit` run lemmas

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

/-! ### The dual-target *duplicating* move gadget `moveRegion2TM`

`moveRegion2TM src dst1 dst2` transfers `src`'s content (FIFO, one bit/iter) to the
**end of BOTH** `dst1` and `dst2`, emptying `src`. It is the duplicating primitive
the `copy`/`tail`/`concat` ops need — a single-target move (`moveRegionTM`) cannot
duplicate data (the number of copies is invariant). The structure mirrors
`moveRegionTM` exactly; the content branch appends the read bit to **two** registers
instead of one (`moveBitM3TM = moveBitM2TM b dst1 ⨾ appendAtThenTwoPhaseRewind(b+1, dst2)`).
The dual-append body yields the exact `encodeTape`
(head→`0`, clean halt). Only the structural scaffolding (validity/halts) is built
here; the run lemma `moveRegion2TM_run` mirrors `moveRegionTM_run` (a three-register
coupled invariant) and is the next step. -/

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
