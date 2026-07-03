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
import Complexity.Lang.Compile.OpSound
import Complexity.Lang.Compile.Assembly

set_option autoImplicit false

/-! # `Compile/Decider` — the WALL: runtime register-width padding

Extracted from `Compile.lean` (refactor Phase 3). The register-width padding that
resolves the `k ≤ s.length` WALL: padding bookkeeping, `haltTM`, the `padBody`
run/trajectory tower, `padRegsTM` + `padBudget`, the padded decider
`paddedBitDeciderTM` + `paddedBitDecider_run`, and the padded compute run
`paddedComputeTM` + `paddedCompute_run`. Depends on `Compile/Assembly`
(`bitDeciderTM`/`bitDecider_run`/`run_physical_residue_gen`). -/

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators
/-! ## ★★ The WALL resolution — runtime register-width padding (2026-06-07)

`Compile_run_physical_residue` honestly requires `k ≤ s.length` (its per-op gadgets
assume the registers they touch already exist on the tape — `Op.inBounds`). But the
decider's *input* tape is narrow (`encodeState x = [enc x]`, width 1) while the
program touches `regBound > 1` registers, and the framework's tight
`DecidesBy.encode_size` (`2·size+4`) forbids pre-padding the *input* encoding.

**Resolution:** pad the tape *at runtime*. `padRegsTM k` grows a narrow tape
`encodeTape s` into `encodeTape (s ++ replicate k [])` (width `≥ k`) — the extra
registers are empty, so `c.eval` is unchanged register-wise (`Cmd.eval_agree`), and
the *input* encoding stays tight (`encode_size` unaffected). Prepended before the
decider, it discharges `k ≤ s'.length` for the whole run. This keeps
`Compile_run_physical_residue` and `bitDecider_run` exactly as they are.

⚠ **`padRegsTM` and its run/trajectory are the single pinned BOTTOM-UP gadget
obligation** replacing the *false* `DecidesLang'.reg_width`. A real construction:
`k`-fold `(stepRightTM ⨾ scanRightUntilTM 4 endMark ⨾ insertCarryTM 0 ⨾
rewindFromEndTM 4 endMark)` — each iteration inserts one `0` delimiter just before
the trailing `endMark`. Its validity/tapes/sig/exit are construction-shape facts;
only the behavioural `run`/`traj` are nontrivial. `Compile.paddedBitDecider_run`
below is PROVEN from this interface, validating the composition design end-to-end. -/

/-! ### Padding bookkeeping (sorry-free) -/

/-- Reading any register of `s ++ replicate k []` is reading it of `s` (the
appended blocks are empty, so out-of-range reads still return `[]`). -/
theorem Compile.get_append_replicate_nil (s : State) (k r : Nat) :
    (s ++ List.replicate k []).get r = s.get r := by
  unfold State.get
  by_cases hr : r < s.length
  · rw [List.getElem?_append_left hr]
  · have hr' : s.length ≤ r := Nat.le_of_not_lt hr
    rw [List.getElem?_append_right hr', List.getElem?_eq_none hr']
    rcases Nat.lt_or_ge (r - s.length) k with hr2 | hr2
    · simp [List.getElem?_replicate, hr2]
    · rw [List.getElem?_eq_none (by rw [List.length_replicate]; exact hr2)]

/-- Reading at or past the register count returns `[]` (`State.get` is
`getElem?`-based). With `get_append_replicate_nil` this discharges the
scratch-emptiness hypothesis for the runtime-padded states: every register
`≥ s.length` of `s ++ replicate m []` is `[]`. -/
theorem Compile.get_of_length_le (s : State) (r : Nat) (hr : s.length ≤ r) :
    State.get s r = [] := by
  unfold State.get
  rw [List.getElem?_eq_none hr]
  rfl

/-- Appending empty registers preserves `BitState`. -/
theorem Compile.BitState_append_replicate_nil (s : State) (k : Nat)
    (h : Compile.BitState s) : Compile.BitState (s ++ List.replicate k []) := by
  intro reg hreg x hx
  rcases List.mem_append.mp hreg with hs | hp
  · exact h reg hs x hx
  · obtain ⟨-, rfl⟩ := List.mem_replicate.mp hp; cases hx

/-- The aggregate size is unchanged by appending empty registers. -/
theorem Compile.size_append_replicate_nil (s : State) (k : Nat) :
    State.size (s ++ List.replicate k []) = State.size s := by
  have hz : ∀ m, (List.replicate m (0 : Nat)).foldr (· + ·) 0 = 0 := by
    intro m; induction m with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  unfold State.size
  rw [List.map_append, List.foldr_append, List.map_replicate, List.length_nil, hz]

/-- `s` and its empty-register padding agree on every register `< k`. -/
theorem Compile.agreeBelow_append_replicate_nil (s : State) (k : Nat) :
    AgreeBelow k s (s ++ List.replicate k []) :=
  fun r _ => (Compile.get_append_replicate_nil s k r).symm

/-! #### Foundational helpers for the WALL gadget proofs -/

/-- A trivial immediately-halting machine (the `k = 0` base of `padRegsTM`): one
state which is a halt state, `sig = 4`, single tape. `runFlatTM n` is the identity. -/
def Compile.haltTM : FlatTM where
  sig := 4; tapes := 1; states := 1; trans := []; start := 0; halt := [true]

theorem Compile.haltTM_valid : validFlatTM Compile.haltTM :=
  ⟨by decide, by decide, by intro e he; cases he⟩

theorem Compile.haltTM_halt {cfg : FlatTMConfig} (h : cfg.state_idx = 0) :
    haltingStateReached Compile.haltTM cfg = true := by
  show Compile.haltTM.halt.getD cfg.state_idx false = true; rw [h]; rfl

theorem Compile.haltTM_run (n : Nat) {cfg : FlatTMConfig} (h : cfg.state_idx = 0) :
    runFlatTM n Compile.haltTM cfg = some cfg := by
  cases n with
  | zero => rfl
  | succ m =>
      show (if haltingStateReached Compile.haltTM cfg then some cfg else _) = some cfg
      rw [if_pos (Compile.haltTM_halt h)]

/-- `encodeRegs` of `s` with one extra empty register appended is `encodeRegs s ++ [0]`
(the empty register contributes its lone `0` delimiter). -/
theorem Compile.encodeRegs_snoc_nil (s : State) :
    Compile.encodeRegs (s ++ [[]]) = Compile.encodeRegs s ++ [0] := by
  induction s with
  | nil => rfl
  | cons r s' ih =>
      rw [List.cons_append, Compile.encodeRegs_cons, Compile.encodeRegs_cons, ih]
      simp [List.append_assoc]

/-- One non-halting step unfolds `runFlatTM (n+1)`. -/
private theorem Compile.run_succ (M : FlatTM) (cfg c' : FlatTMConfig) (n : Nat)
    (hnh : haltingStateReached M cfg = false) (hstep : stepFlatTM M cfg = some c') :
    runFlatTM (n + 1) M cfg = runFlatTM n M c' := by
  show (if haltingStateReached M cfg then some cfg
        else match stepFlatTM M cfg with | none => some cfg | some c'' => runFlatTM n M c'') = _
  rw [if_neg (by rw [hnh]; decide), hstep]

/-- A cell read off a `< 4` tape (head track empty) is `< 4`. -/
private theorem Compile.curSym_lt {tp : List Nat} (hb : ∀ x ∈ tp, x < 4) (head : Nat) :
    ∀ v, currentTapeSymbol (([] : List Nat), head, tp) = some v → v < 4 := by
  intro v hv
  unfold currentTapeSymbol at hv
  by_cases h : head < tp.length
  · rw [dif_pos h] at hv; injection hv with hv'; subst hv'; exact hb _ (List.get_mem _ _)
  · rw [dif_neg h] at hv; exact absurd hv (by simp)

/-- **Scan-right partial trajectory.** From `{0, head}` on a tape whose cells
`head … head+gap-1` are in range and `≠ target`, after `j ≤ gap` steps
`scanRightUntilTM` is in state `0` with head at `head + j`. (The `j ≤ gap` prefix of
`scanRightUntilTM_run_found`; gives the missing `no_early_halt`.) -/
private theorem Compile.scanRight_partial
    (sig target : Nat) (left right : List Nat) (head gap : Nat)
    (hcells : ∀ k, k < gap → ∃ (h : head + k < right.length),
        right.get ⟨head + k, h⟩ < sig ∧ right.get ⟨head + k, h⟩ ≠ target) :
    ∀ j, j ≤ gap → runFlatTM j (scanRightUntilTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 0, tapes := [(left, head + j, right)] } := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      obtain ⟨hlt, hsymlt, hne⟩ := hcells j (by omega)
      have hstep := scanRightUntilTM_step_advance sig target left right (head + j) hlt hsymlt hne
      rw [runFlatTM_compose (scanRightUntilTM sig target) j 1 _ _ (ih (by omega)),
          Compile.run_succ (scanRightUntilTM sig target) _ _ 0 (by rfl) hstep]
      rfl

/-! #### The padding body `padBody` and its run/trajectory -/

/-- Insert-then-rewind: from the trailing terminator, insert one `0` before it and
rewind to the leading sentinel. -/
def Compile.padInner34 : FlatTM :=
  composeFlatTM (ShiftTape.insertCarryTM 0) (ScanLeft.rewindFromEndTM 4 3) 5

/-- Scan-right then `padInner34`. -/
def Compile.padInner234 : FlatTM :=
  composeFlatTM (scanRightUntilTM 4 3) Compile.padInner34 1

/-- **One padding-body iteration (the reusable core, REAL).** From head `0` on
`encodeTape s`: step right off the sentinel, scan right to the trailing terminator,
insert one `0` before it, rewind to the leading sentinel. Maps `encodeTape s` →
`encodeTape (s ++ [[]])`, head back to `0`, halting at state `padBodyExit = 14` in
exactly `2·|encodeTape s| + 7` steps (probe-validated). -/
def Compile.padBody : FlatTM :=
  composeFlatTM (ScanLeft.stepRightTM 4) Compile.padInner234 1

/-- `padBody`'s final halt state. -/
def Compile.padBodyExit : Nat := 14

theorem Compile.padBody_states : Compile.padBody.states = 16 := rfl
theorem Compile.padBody_tapes : Compile.padBody.tapes = 1 := rfl
theorem Compile.padBody_start : Compile.padBody.start = 0 := rfl

theorem Compile.padInner34_valid : validFlatTM Compile.padInner34 :=
  composeFlatTM_valid _ _ 5 (ShiftTape.insertCarryTM_valid 0 (by decide))
    (ScanLeft.rewindFromEndTM_valid 4 3 (by decide)) (by decide) rfl rfl

theorem Compile.padInner234_valid : validFlatTM Compile.padInner234 :=
  composeFlatTM_valid _ _ 1 (scanRightUntilTM_valid 4 3 (by decide))
    Compile.padInner34_valid (by decide) rfl rfl

theorem Compile.padBody_valid : validFlatTM Compile.padBody :=
  composeFlatTM_valid _ _ 1 (ScanLeft.stepRightTM_valid 4)
    Compile.padInner234_valid (by decide) rfl rfl

theorem Compile.padBody_halt {cfg : FlatTMConfig} (h : cfg.state_idx = 14) :
    haltingStateReached Compile.padBody cfg = true := by
  show Compile.padBody.halt.getD cfg.state_idx false = true; rw [h]; rfl

/-- The post-insert tape equals `encodeTape (s ++ [[]])`. -/
private theorem Compile.padBody_tape_eq (s : State) :
    ((3 :: Compile.encodeRegs s) ++ (0 : Nat) :: [3]) = Compile.encodeTape (s ++ [[]]) := by
  rw [Compile.encodeTape, Compile.encodeRegs_snoc_nil]
  show (3 :: Compile.encodeRegs s) ++ 0 :: [3]
      = Compile.endMark :: (Compile.encodeRegs s ++ [0] ++ [Compile.endMark])
  simp [Compile.endMark, List.append_assoc]

/-- `encodeTape s = (3 :: encodeRegs s) ++ [3]`. -/
private theorem Compile.encodeTape_cons_form (s : State) :
    Compile.encodeTape s = (3 :: Compile.encodeRegs s) ++ [3] := rfl

theorem Compile.padInner34_run (s : State) (hbit : Compile.BitState s) :
    runFlatTM ((Compile.encodeRegs s).length + 7) Compile.padInner34
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] }
      = some { state_idx := 9, tapes := [([], 0, Compile.encodeTape (s ++ [[]]))] } := by
  have hbit' : Compile.BitState (s ++ [[]]) := by
    have := Compile.BitState_append_replicate_nil s 1 hbit
    rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
  have hL : 1 + (Compile.encodeRegs s).length = (3 :: Compile.encodeRegs s).length := by simp [Nat.add_comm]
  have htape_s : Compile.encodeTape s = (3 :: Compile.encodeRegs s) ++ [3] := Compile.encodeTape_cons_form s
  have htape_s' : (3 :: Compile.encodeRegs s) ++ (0 : Nat) :: [3] = Compile.encodeTape (s ++ [[]]) :=
    Compile.padBody_tape_eq s
  have htplen : (Compile.encodeTape (s ++ [[]])).length = (Compile.encodeRegs s).length + 3 := by
    rw [Compile.encodeTape_length]
    have hsz : State.size (s ++ [[]]) = State.size s := by
      have := Compile.size_append_replicate_nil s 1
      rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
    have hwlen : (s ++ [[]]).length = s.length + 1 := by simp
    rw [hsz, hwlen, Compile.encodeRegs_length]; omega
  -- M₁ = insertCarryTM 0 : insert a `0` before the trailing terminator.
  have hins : runFlatTM 2 (ShiftTape.insertCarryTM 0)
        { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] }
      = some { state_idx := 5,
               tapes := [([], (Compile.encodeRegs s).length + 2, Compile.encodeTape (s ++ [[]]))] } := by
    have h := ShiftTape.insertCarryTM_run 0 [3] (3 :: Compile.encodeRegs s)
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; decide)
    rw [← hL, ← htape_s, htape_s'] at h
    rw [show (1 + (Compile.encodeRegs s).length + ([3] : List Nat).length)
          = (Compile.encodeRegs s).length + 2 by simp; omega] at h
    exact h
  -- M₂ = rewindFromEndTM 4 3 : rewind from the trailing terminator to the leading sentinel.
  have hrew : runFlatTM ((Compile.encodeRegs s).length + 4) (ScanLeft.rewindFromEndTM 4 3)
        { state_idx := 0, tapes := [([], (Compile.encodeRegs s).length + 2, Compile.encodeTape (s ++ [[]]))] }
      = some { state_idx := 3, tapes := [([], 0, Compile.encodeTape (s ++ [[]]))] } := by
    have h := ScanLeft.rewindFromEndTM_run 4 3 (by decide) [] (Compile.encodeTape (s ++ [[]]))
      ((Compile.encodeRegs s).length + 2) (by omega)
      (Compile.encodeTape_get_zero (s ++ [[]]) (by omega))
      (by omega) (by omega)
      (Compile.encodeTape_lt_four (s ++ [[]]) hbit' _ (List.get_mem _ _))
      (by
        intro i hi_pos hi_lt
        obtain ⟨hii, hne⟩ := Compile.encodeTape_interior_ne_endMark (s ++ [[]]) hbit' i hi_pos (by omega)
        exact ⟨hii, Compile.encodeTape_lt_four (s ++ [[]]) hbit' _ (List.get_mem _ _), hne⟩)
    rw [show (1 : Nat) + 1 + ((Compile.encodeRegs s).length + 2) = (Compile.encodeRegs s).length + 4 by omega] at h
    exact h
  -- sym bound at the bridge (head on the post-insert tape).
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), (Compile.encodeRegs s).length + 2,
        Compile.encodeTape (s ++ [[]])) = some v
      → v < max (ShiftTape.insertCarryTM 0).sig (ScanLeft.rewindFromEndTM 4 3).sig := by
    intro v hv
    rw [show max (ShiftTape.insertCarryTM 0).sig (ScanLeft.rewindFromEndTM 4 3).sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four (s ++ [[]]) hbit') _ v hv
  have hcomp := composeFlatTM_run (M₁ := ShiftTape.insertCarryTM 0)
    (M₂ := ScanLeft.rewindFromEndTM 4 3) (exit := 5)
    (ShiftTape.insertCarryTM_valid 0 (by decide)) (ScanLeft.rewindFromEndTM_valid 4 3 (by decide))
    (by decide)
    { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] }
    (by show (0 : Nat) < (ShiftTape.insertCarryTM 0).states; decide)
    [] ((Compile.encodeRegs s).length + 2) (Compile.encodeTape (s ++ [[]])) hsym
    hins
    (by
      intro k hk ck hck
      have hnh : haltingStateReached (ShiftTape.insertCarryTM 0) ck = false := by
        have := ShiftTape.insertCarryTM_no_early_halt 0 [3] (3 :: Compile.encodeRegs s)
          (by intro x hx; rcases List.mem_singleton.mp hx with rfl; decide) k (by simpa using hk) ck
        rw [← hL, ← htape_s] at this
        exact this hck
      refine ⟨fun h => ?_, hnh⟩
      have hb : haltingStateReached (ShiftTape.insertCarryTM 0) ck = true := by
        show (ShiftTape.insertCarryTM 0).halt.getD ck.state_idx false = true
        rw [h]; decide
      rw [hb] at hnh; exact absurd hnh (by decide))
    hrew (by show (ScanLeft.rewindFromEndTM 4 3).halt.getD 3 false = true; decide)
  obtain ⟨hrun, _⟩ := hcomp
  rw [show (Compile.encodeRegs s).length + 7 = 2 + 1 + ((Compile.encodeRegs s).length + 4) by omega]
  exact hrun

theorem Compile.padInner234_run (s : State) (hbit : Compile.BitState s) :
    runFlatTM (2 * (Compile.encodeRegs s).length + 9) Compile.padInner234
        { state_idx := 0, tapes := [([], 1, Compile.encodeTape s)] }
      = some { state_idx := 12, tapes := [([], 0, Compile.encodeTape (s ++ [[]]))] } := by
  have hlen : (Compile.encodeTape s).length = (Compile.encodeRegs s).length + 2 := by
    rw [Compile.encodeTape_length, Compile.encodeRegs_length]
  -- scanRightUntilTM run: from head 1, scan to the trailing terminator at index 1 + |R|.
  have hscan := scanRightUntilTM_run_found 4 3 [] (Compile.encodeTape s)
    (Compile.encodeRegs s).length 1 (by rw [hlen]; omega)
    (by
      have key : (Compile.encodeTape s)[1 + (Compile.encodeRegs s).length]? = some 3 := by
        rw [Compile.encodeTape,
            show 1 + (Compile.encodeRegs s).length = (Compile.encodeRegs s).length + 1 by omega,
            List.getElem?_cons_succ,
            List.getElem?_append_right (Nat.le_refl _)]
        simp [Compile.endMark]
      rw [List.get_eq_getElem]
      have hg := List.getElem?_eq_getElem
        (show 1 + (Compile.encodeRegs s).length < (Compile.encodeTape s).length by rw [hlen]; omega)
      rw [key] at hg
      exact (Option.some.inj hg).symm)
    (by
      intro k hk
      obtain ⟨hi, hne⟩ := Compile.encodeTape_interior_ne_endMark s hbit (1 + k) (by omega) (by rw [hlen]; omega)
      exact ⟨hi, Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _), hne⟩)
  -- sym bound at the bridge.
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 1 + (Compile.encodeRegs s).length,
        Compile.encodeTape s) = some v
      → v < max (scanRightUntilTM 4 3).sig Compile.padInner34.sig := by
    intro v hv
    rw [show max (scanRightUntilTM 4 3).sig Compile.padInner34.sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four s hbit) _ v hv
  have hcomp := composeFlatTM_run (M₁ := scanRightUntilTM 4 3) (M₂ := Compile.padInner34) (exit := 1)
    (scanRightUntilTM_valid 4 3 (by decide)) Compile.padInner34_valid (by decide)
    { state_idx := 0, tapes := [([], 1, Compile.encodeTape s)] }
    (by show (0 : Nat) < (scanRightUntilTM 4 3).states; decide)
    [] (1 + (Compile.encodeRegs s).length) (Compile.encodeTape s) hsym
    hscan
    (by
      intro k hk ck hck
      have hpart := Compile.scanRight_partial 4 3 [] (Compile.encodeTape s) 1 (Compile.encodeRegs s).length
        (by
          intro m hm
          obtain ⟨hi, hne⟩ := Compile.encodeTape_interior_ne_endMark s hbit (1 + m) (by omega) (by rw [hlen]; omega)
          exact ⟨hi, Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _), hne⟩)
        k (by omega)
      rw [hpart] at hck
      obtain rfl := Option.some.inj hck
      exact ⟨Nat.zero_ne_one, rfl⟩)
    (Compile.padInner34_run s hbit)
    (by show Compile.padInner34.halt.getD 9 false = true; decide)
  obtain ⟨hrun, _⟩ := hcomp
  rw [show 2 * (Compile.encodeRegs s).length + 9
        = ((Compile.encodeRegs s).length + 1) + 1 + ((Compile.encodeRegs s).length + 7) by omega]
  exact hrun

theorem Compile.padBody_run (s : State) (hbit : Compile.BitState s) :
    runFlatTM (2 * (Compile.encodeTape s).length + 7) Compile.padBody
        (initFlatConfig Compile.padBody [Compile.encodeTape s])
      = some { state_idx := Compile.padBodyExit,
               tapes := [([], 0, Compile.encodeTape (s ++ [[]]))] } := by
  have hlen : (Compile.encodeTape s).length = (Compile.encodeRegs s).length + 2 := by
    rw [Compile.encodeTape_length, Compile.encodeRegs_length]
  have hinit : initFlatConfig Compile.padBody [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := rfl
  rw [hinit]
  -- stepRightTM run: head 0 → 1 (off the leading sentinel).
  have hstep := ScanLeft.stepRightTM_run 4 [] (Compile.encodeTape s) 0 (by rw [hlen]; omega)
    (by rw [Compile.encodeTape_get_zero s (by rw [hlen]; omega)]; decide)
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 1, Compile.encodeTape s) = some v
      → v < max (ScanLeft.stepRightTM 4).sig Compile.padInner234.sig := by
    intro v hv
    rw [show max (ScanLeft.stepRightTM 4).sig Compile.padInner234.sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four s hbit) _ v hv
  have hcomp := composeFlatTM_run (M₁ := ScanLeft.stepRightTM 4) (M₂ := Compile.padInner234) (exit := 1)
    (ScanLeft.stepRightTM_valid 4) Compile.padInner234_valid (by decide)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] }
    (by show (0 : Nat) < (ScanLeft.stepRightTM 4).states; decide)
    [] 1 (Compile.encodeTape s) hsym
    hstep
    (fun k hk ck hck => ScanLeft.stepRightTM_no_early_halt 4 [] (Compile.encodeTape s) 0 k hk ck hck)
    (Compile.padInner234_run s hbit)
    (by show Compile.padInner234.halt.getD 12 false = true; decide)
  obtain ⟨hrun, _⟩ := hcomp
  rw [show 2 * (Compile.encodeTape s).length + 7
        = 1 + 1 + (2 * (Compile.encodeRegs s).length + 9) by omega]
  exact hrun

/-! #### The trajectory tower (no-early-halt), mirroring the run tower. -/

theorem Compile.padInner34_no_early_halt (s : State) (hbit : Compile.BitState s) :
    ∀ j, j < (Compile.encodeRegs s).length + 7 → ∀ ck,
      runFlatTM j Compile.padInner34
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] } = some ck →
      haltingStateReached Compile.padInner34 ck = false := by
  have hbit' : Compile.BitState (s ++ [[]]) := by
    have := Compile.BitState_append_replicate_nil s 1 hbit
    rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
  have hL : 1 + (Compile.encodeRegs s).length = (3 :: Compile.encodeRegs s).length := by
    simp [Nat.add_comm]
  have htape_s : Compile.encodeTape s = (3 :: Compile.encodeRegs s) ++ [3] := Compile.encodeTape_cons_form s
  have htplen : (Compile.encodeTape (s ++ [[]])).length = (Compile.encodeRegs s).length + 3 := by
    rw [Compile.encodeTape_length]
    have hsz : State.size (s ++ [[]]) = State.size s := by
      have := Compile.size_append_replicate_nil s 1
      rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
    have hwlen : (s ++ [[]]).length = s.length + 1 := by simp
    rw [hsz, hwlen, Compile.encodeRegs_length]; omega
  have hins : runFlatTM 2 (ShiftTape.insertCarryTM 0)
        { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] }
      = some { state_idx := 5,
               tapes := [([], (Compile.encodeRegs s).length + 2, Compile.encodeTape (s ++ [[]]))] } := by
    have h := ShiftTape.insertCarryTM_run 0 [3] (3 :: Compile.encodeRegs s)
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; decide)
    rw [← hL, ← htape_s, Compile.padBody_tape_eq s] at h
    rw [show (1 + (Compile.encodeRegs s).length + ([3] : List Nat).length)
          = (Compile.encodeRegs s).length + 2 by simp; omega] at h
    exact h
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), (Compile.encodeRegs s).length + 2,
        Compile.encodeTape (s ++ [[]])) = some v
      → v < max (ShiftTape.insertCarryTM 0).sig (ScanLeft.rewindFromEndTM 4 3).sig := by
    intro v hv
    rw [show max (ShiftTape.insertCarryTM 0).sig (ScanLeft.rewindFromEndTM 4 3).sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four (s ++ [[]]) hbit') _ v hv
  intro j hj ck hck
  refine composeFlatTM_no_early_halt (M₁ := ShiftTape.insertCarryTM 0)
    (M₂ := ScanLeft.rewindFromEndTM 4 3) (exit := 5)
    (t₂ := (Compile.encodeRegs s).length + 4)
    (ShiftTape.insertCarryTM_valid 0 (by decide)) (ScanLeft.rewindFromEndTM_valid 4 3 (by decide))
    (by decide)
    { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] }
    (by show (0 : Nat) < (ShiftTape.insertCarryTM 0).states; decide)
    [] ((Compile.encodeRegs s).length + 2) (Compile.encodeTape (s ++ [[]])) hsym
    hins
    (by
      intro k hk ck' hck'
      have hnh : haltingStateReached (ShiftTape.insertCarryTM 0) ck' = false := by
        have := ShiftTape.insertCarryTM_no_early_halt 0 [3] (3 :: Compile.encodeRegs s)
          (by intro x hx; rcases List.mem_singleton.mp hx with rfl; decide) k (by simpa using hk) ck'
        rw [← hL, ← htape_s] at this
        exact this hck'
      refine ⟨fun h => ?_, hnh⟩
      have hb : haltingStateReached (ShiftTape.insertCarryTM 0) ck' = true := by
        show (ShiftTape.insertCarryTM 0).halt.getD ck'.state_idx false = true
        rw [h]; decide
      rw [hb] at hnh; exact absurd hnh (by decide))
    (by
      have htraj := ScanLeft.rewindFromEndTM_no_early_halt 4 3 (by decide) []
        (Compile.encodeTape (s ++ [[]])) ((Compile.encodeRegs s).length + 2) (by omega)
        (Compile.encodeTape_get_zero (s ++ [[]]) (by omega)) (by omega) (by omega)
        (Compile.encodeTape_lt_four (s ++ [[]]) hbit' _ (List.get_mem _ _))
        (by
          intro i hi_pos hi_lt
          obtain ⟨hii, hne⟩ := Compile.encodeTape_interior_ne_endMark (s ++ [[]]) hbit' i hi_pos (by omega)
          exact ⟨hii, Compile.encodeTape_lt_four (s ++ [[]]) hbit' _ (List.get_mem _ _), hne⟩)
      intro k hk ck' hck'
      exact htraj k (by omega) ck' hck')
    j (by omega) ck hck

theorem Compile.padInner234_no_early_halt (s : State) (hbit : Compile.BitState s) :
    ∀ j, j < 2 * (Compile.encodeRegs s).length + 9 → ∀ ck,
      runFlatTM j Compile.padInner234
          { state_idx := 0, tapes := [([], 1, Compile.encodeTape s)] } = some ck →
      haltingStateReached Compile.padInner234 ck = false := by
  have hlen : (Compile.encodeTape s).length = (Compile.encodeRegs s).length + 2 := by
    rw [Compile.encodeTape_length, Compile.encodeRegs_length]
  have hscan := scanRightUntilTM_run_found 4 3 [] (Compile.encodeTape s)
    (Compile.encodeRegs s).length 1 (by rw [hlen]; omega)
    (by
      have key : (Compile.encodeTape s)[1 + (Compile.encodeRegs s).length]? = some 3 := by
        rw [Compile.encodeTape,
            show 1 + (Compile.encodeRegs s).length = (Compile.encodeRegs s).length + 1 by omega,
            List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _)]
        simp [Compile.endMark]
      rw [List.get_eq_getElem]
      have hg := List.getElem?_eq_getElem
        (show 1 + (Compile.encodeRegs s).length < (Compile.encodeTape s).length by rw [hlen]; omega)
      rw [key] at hg
      exact (Option.some.inj hg).symm)
    (by
      intro k hk
      obtain ⟨hi, hne⟩ := Compile.encodeTape_interior_ne_endMark s hbit (1 + k) (by omega) (by rw [hlen]; omega)
      exact ⟨hi, Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _), hne⟩)
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 1 + (Compile.encodeRegs s).length,
        Compile.encodeTape s) = some v
      → v < max (scanRightUntilTM 4 3).sig Compile.padInner34.sig := by
    intro v hv
    rw [show max (scanRightUntilTM 4 3).sig Compile.padInner34.sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four s hbit) _ v hv
  intro j hj ck hck
  refine composeFlatTM_no_early_halt (M₁ := scanRightUntilTM 4 3) (M₂ := Compile.padInner34) (exit := 1)
    (t₂ := (Compile.encodeRegs s).length + 7)
    (scanRightUntilTM_valid 4 3 (by decide)) Compile.padInner34_valid (by decide)
    { state_idx := 0, tapes := [([], 1, Compile.encodeTape s)] }
    (by show (0 : Nat) < (scanRightUntilTM 4 3).states; decide)
    [] (1 + (Compile.encodeRegs s).length) (Compile.encodeTape s) hsym
    hscan
    (by
      intro k hk ck' hck'
      have hpart := Compile.scanRight_partial 4 3 [] (Compile.encodeTape s) 1 (Compile.encodeRegs s).length
        (by
          intro m hm
          obtain ⟨hi, hne⟩ := Compile.encodeTape_interior_ne_endMark s hbit (1 + m) (by omega) (by rw [hlen]; omega)
          exact ⟨hi, Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _), hne⟩)
        k (by omega)
      rw [hpart] at hck'
      obtain rfl := Option.some.inj hck'
      exact ⟨Nat.zero_ne_one, rfl⟩)
    (fun k hk ck' hck' => Compile.padInner34_no_early_halt s hbit k (by omega) ck' hck')
    j (by omega) ck hck

theorem Compile.padBody_no_early_halt (s : State) (hbit : Compile.BitState s) :
    ∀ j, j < 2 * (Compile.encodeTape s).length + 7 → ∀ ck,
      runFlatTM j Compile.padBody (initFlatConfig Compile.padBody [Compile.encodeTape s]) = some ck →
      haltingStateReached Compile.padBody ck = false := by
  have hlen : (Compile.encodeTape s).length = (Compile.encodeRegs s).length + 2 := by
    rw [Compile.encodeTape_length, Compile.encodeRegs_length]
  have hinit : initFlatConfig Compile.padBody [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := rfl
  rw [hinit]
  have hstep := ScanLeft.stepRightTM_run 4 [] (Compile.encodeTape s) 0 (by rw [hlen]; omega)
    (by rw [Compile.encodeTape_get_zero s (by rw [hlen]; omega)]; decide)
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 1, Compile.encodeTape s) = some v
      → v < max (ScanLeft.stepRightTM 4).sig Compile.padInner234.sig := by
    intro v hv
    rw [show max (ScanLeft.stepRightTM 4).sig Compile.padInner234.sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four s hbit) _ v hv
  intro j hj ck hck
  refine composeFlatTM_no_early_halt (M₁ := ScanLeft.stepRightTM 4) (M₂ := Compile.padInner234) (exit := 1)
    (t₂ := 2 * (Compile.encodeRegs s).length + 9)
    (ScanLeft.stepRightTM_valid 4) Compile.padInner234_valid (by decide)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] }
    (by show (0 : Nat) < (ScanLeft.stepRightTM 4).states; decide)
    [] 1 (Compile.encodeTape s) hsym
    hstep
    (fun k hk ck' hck' => ScanLeft.stepRightTM_no_early_halt 4 [] (Compile.encodeTape s) 0 k hk ck' hck')
    (fun k hk ck' hck' => Compile.padInner234_no_early_halt s hbit k (by omega) ck' hck')
    j (by omega) ck hck

/-- **Empty-register padding machine (REAL — the WALL gadget).** `padRegsTM k` is
the `k`-fold static composition of `padBody` (recursion on `k`), base `haltTM`
(the `k = 0` no-op). Grows `encodeTape s` into `encodeTape (s ++ replicate k [])`. -/
def Compile.padRegsTM : Nat → FlatTM
  | 0     => Compile.haltTM
  | k + 1 => composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit

/-- The padding machine's halt/exit state: `0` (base) shifted up by
`padBody.states = 16` per iteration, i.e. `16·k`. -/
def Compile.padRegsExit : Nat → Nat
  | 0     => 0
  | k + 1 => Compile.padRegsExit k + 16

theorem Compile.padRegsTM_tapes (k : Nat) : (Compile.padRegsTM k).tapes = 1 := by
  cases k with
  | zero => rfl
  | succ k =>
      show (composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit).tapes = 1
      rw [composeFlatTM_tapes, Compile.padBody_tapes]

theorem Compile.padRegsTM_sig (k : Nat) : (Compile.padRegsTM k).sig = 4 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit).sig = 4
      rw [composeFlatTM_sig, ih]; rfl

theorem Compile.padRegsTM_states (k : Nat) :
    (Compile.padRegsTM k).states = 1 + 16 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit).states
          = 1 + 16 * (k + 1)
      rw [composeFlatTM_states, Compile.padBody_states, ih]; ring

theorem Compile.padRegsTM_valid (k : Nat) : validFlatTM (Compile.padRegsTM k) := by
  induction k with
  | zero => exact Compile.haltTM_valid
  | succ k ih =>
      exact composeFlatTM_valid Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit
        Compile.padBody_valid ih (by rw [Compile.padBody_states]; decide)
        Compile.padBody_tapes (Compile.padRegsTM_tapes k)

theorem Compile.padRegsExit_lt (k : Nat) :
    Compile.padRegsExit k < (Compile.padRegsTM k).states := by
  induction k with
  | zero => show (0 : Nat) < Compile.haltTM.states; decide
  | succ k ih =>
      show Compile.padRegsExit k + 16
          < (composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit).states
      rw [composeFlatTM_states, Compile.padBody_states]; omega

/-- `padRegsExit k` is a halt index of `padRegsTM k`. -/
theorem Compile.padRegsTM_halt_idx (k : Nat) :
    (Compile.padRegsTM k).halt.getD (Compile.padRegsExit k) false = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit).halt.getD
          (Compile.padRegsExit k + 16) false = true
      show (composedHalt Compile.padBody (Compile.padRegsTM k)).getD
          (Compile.padRegsExit k + 16) false = true
      rw [composedHalt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [List.length_replicate, Compile.padBody_states]; omega),
          List.length_replicate, Compile.padBody_states,
          show Compile.padRegsExit k + 16 - 16 = Compile.padRegsExit k by omega,
          ← List.getD_eq_getElem?_getD]
      exact ih

/-- `padRegsExit k` is a halt state of `padRegsTM k` (for any tape). -/
theorem Compile.padRegsTM_halt (k : Nat) {cfg : FlatTMConfig}
    (h : cfg.state_idx = Compile.padRegsExit k) :
    haltingStateReached (Compile.padRegsTM k) cfg = true := by
  show (Compile.padRegsTM k).halt.getD cfg.state_idx false = true
  rw [h]; exact Compile.padRegsTM_halt_idx k

/-- Step budget for `padRegsTM k` on `encodeTape s` — the **exact** step count
(recursion mirrors the machine). Each body is `2·|tape|+7` steps + 1 bridge; the
base is `0`. `padRegsTM_run`/`_traj` need the *exact* count (the trajectory must not
yet be at the exit), and `padBudget_le` bounds it by a clean polynomial for the
framework bridges. -/
def Compile.padBudget : Nat → State → Nat
  | 0, _     => 0
  | k + 1, s => (2 * (Compile.encodeTape s).length + 7) + 1 + Compile.padBudget k (s ++ [[]])

/-- `padBudget` is bounded by a clean polynomial in tape width and `k`. -/
theorem Compile.padBudget_le (k : Nat) (s : State) :
    Compile.padBudget k s ≤ k * (2 * State.size s + 2 * s.length + 2 * k + 12) := by
  induction k generalizing s with
  | zero => simp [Compile.padBudget]
  | succ k ih =>
      have hsize : State.size (s ++ [[]]) = State.size s := by
        have := Compile.size_append_replicate_nil s 1
        rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
      have hlen : (s ++ [[]]).length = s.length + 1 := by simp
      have hbody : (Compile.encodeTape s).length = State.size s + s.length + 2 :=
        Compile.encodeTape_length s
      have ihs := ih (s ++ [[]])
      rw [hsize, hlen] at ihs
      show (2 * (Compile.encodeTape s).length + 7) + 1 + Compile.padBudget k (s ++ [[]])
          ≤ (k + 1) * (2 * State.size s + 2 * s.length + 2 * (k + 1) + 12)
      rw [hbody]
      calc (2 * (State.size s + s.length + 2) + 7) + 1 + Compile.padBudget k (s ++ [[]])
          ≤ (2 * (State.size s + s.length + 2) + 7) + 1
              + k * (2 * State.size s + 2 * (s.length + 1) + 2 * k + 12) := by
            exact Nat.add_le_add_left ihs _
        _ ≤ (k + 1) * (2 * State.size s + 2 * s.length + 2 * (k + 1) + 12) := by ring_nf; omega

/-- **`padRegsTM` run.** From the narrow tape `encodeTape s`, reach the exit
`padRegsExit k` with tape `encodeTape (s ++ replicate k [])`, head rewound to `0`,
in exactly `padBudget k s` steps. Induction on `k` via `composeFlatTM_run`. -/
theorem Compile.padRegsTM_run (k : Nat) (s : State) (hbit : Compile.BitState s) :
    runFlatTM (Compile.padBudget k s) (Compile.padRegsTM k)
        (initFlatConfig (Compile.padRegsTM k) [Compile.encodeTape s])
      = some { state_idx := Compile.padRegsExit k,
               tapes := [([], 0, Compile.encodeTape (s ++ List.replicate k []))] } := by
  induction k generalizing s with
  | zero =>
      show runFlatTM 0 Compile.haltTM { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] }
          = some { state_idx := 0, tapes := [([], 0, Compile.encodeTape (s ++ List.replicate 0 []))] }
      rw [List.replicate_zero, List.append_nil]; rfl
  | succ k ih =>
      have hbit' : Compile.BitState (s ++ [[]]) := by
        have := Compile.BitState_append_replicate_nil s 1 hbit
        rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
      have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape (s ++ [[]])) = some v
          → v < max Compile.padBody.sig (Compile.padRegsTM k).sig := by
        intro v hv
        rw [show max Compile.padBody.sig (Compile.padRegsTM k).sig = 4 from by
              rw [Compile.padRegsTM_sig k]; decide]
        exact Compile.curSym_lt (Compile.encodeTape_lt_four (s ++ [[]]) hbit') _ v hv
      have hcomp := composeFlatTM_run (M₁ := Compile.padBody) (M₂ := Compile.padRegsTM k)
        (exit := Compile.padBodyExit)
        Compile.padBody_valid (Compile.padRegsTM_valid k)
        (by rw [Compile.padBody_states]; decide)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] }
        (by show (0 : Nat) < Compile.padBody.states; decide)
        [] 0 (Compile.encodeTape (s ++ [[]])) hsym
        (Compile.padBody_run s hbit)
        (by
          intro m hm cm hcm
          have hnh := Compile.padBody_no_early_halt s hbit m hm cm hcm
          refine ⟨fun h => ?_, hnh⟩
          have hb : haltingStateReached Compile.padBody cm = true := by
            show Compile.padBody.halt.getD cm.state_idx false = true
            rw [h]; decide
          rw [hb] at hnh; exact absurd hnh (by decide))
        (ih (s ++ [[]]) hbit')
        (Compile.padRegsTM_halt k rfl)
      obtain ⟨hrun, _⟩ := hcomp
      have htape : (s ++ [[]]) ++ List.replicate k [] = s ++ List.replicate (k + 1) [] := by
        rw [List.append_assoc]; simp [List.replicate_succ]
      rw [Compile.padBody_states] at hrun
      rw [← htape]
      exact hrun

/-- **`padRegsTM` trajectory.** It does not hit the exit or any halt state before
`padBudget k s`. Induction via `composeFlatTM_no_early_halt` + `padBody`'s trajectory. -/
theorem Compile.padRegsTM_traj (k : Nat) (s : State) (hbit : Compile.BitState s) :
    ∀ j, j < Compile.padBudget k s → ∀ ck,
      runFlatTM j (Compile.padRegsTM k)
          (initFlatConfig (Compile.padRegsTM k) [Compile.encodeTape s]) = some ck →
      ck.state_idx ≠ Compile.padRegsExit k ∧
      haltingStateReached (Compile.padRegsTM k) ck = false := by
  induction k generalizing s with
  | zero => intro j hj ck _; exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
      have hbit' : Compile.BitState (s ++ [[]]) := by
        have := Compile.BitState_append_replicate_nil s 1 hbit
        rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
      have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape (s ++ [[]])) = some v
          → v < max Compile.padBody.sig (Compile.padRegsTM k).sig := by
        intro v hv
        rw [show max Compile.padBody.sig (Compile.padRegsTM k).sig = 4 from by
              rw [Compile.padRegsTM_sig k]; decide]
        exact Compile.curSym_lt (Compile.encodeTape_lt_four (s ++ [[]]) hbit') _ v hv
      intro j hj ck hck
      have hnh := composeFlatTM_no_early_halt (M₁ := Compile.padBody) (M₂ := Compile.padRegsTM k)
        (exit := Compile.padBodyExit) (t₂ := Compile.padBudget k (s ++ [[]]))
        Compile.padBody_valid (Compile.padRegsTM_valid k)
        (by rw [Compile.padBody_states]; decide)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] }
        (by show (0 : Nat) < Compile.padBody.states; decide)
        [] 0 (Compile.encodeTape (s ++ [[]])) hsym
        (Compile.padBody_run s hbit)
        (by
          intro m hm cm hcm
          have hb := Compile.padBody_no_early_halt s hbit m hm cm hcm
          refine ⟨fun h => ?_, hb⟩
          have hh : haltingStateReached Compile.padBody cm = true := by
            show Compile.padBody.halt.getD cm.state_idx false = true
            rw [h]; decide
          rw [hh] at hb; exact absurd hb (by decide))
        (fun m hm cm hcm => (ih (s ++ [[]]) hbit' m hm cm hcm).2)
        j hj ck hck
      refine ⟨fun h => ?_, hnh⟩
      have hh : haltingStateReached (Compile.padRegsTM (k + 1)) ck = true :=
        Compile.padRegsTM_halt (k + 1) h
      have hnh' : haltingStateReached (Compile.padRegsTM (k + 1)) ck = false := hnh
      rw [hh] at hnh'; exact absurd hnh' (by decide)

/-! ### The padded decider — `padRegsTM ⨾ bitDeciderTM` -/

/-- The full decider with runtime width-padding: pad to `k + 2 * c.loopDepth`
registers — the program's `regBound = k` **plus the compiler's scratch block**
(`2 * c.loopDepth` registers at base `k`, which must physically exist on the
tape and start `[]`; the `padRegsTM` pad provides exactly that) — then run the
bit-decider at scratch base `k`. The input tape is the **narrow** `encodeTape s`. -/
def Compile.paddedBitDeciderTM (c : Cmd) (k : Nat) : FlatTM :=
  composeFlatTM (Compile.padRegsTM (k + 2 * c.loopDepth + 2)) (Compile.bitDeciderTM c k)
    (Compile.padRegsExit (k + 2 * c.loopDepth + 2))

theorem Compile.paddedBitDeciderTM_valid (c : Cmd) (k : Nat) :
    validFlatTM (Compile.paddedBitDeciderTM c k) :=
  composeFlatTM_valid (Compile.padRegsTM (k + 2 * c.loopDepth + 2)) (Compile.bitDeciderTM c k)
    (Compile.padRegsExit (k + 2 * c.loopDepth + 2))
    (Compile.padRegsTM_valid _) (Compile.bitDeciderTM_valid c k) (Compile.padRegsExit_lt _)
    (Compile.padRegsTM_tapes _) (Compile.bitDeciderTM_tapes c k)

theorem Compile.paddedBitDeciderTM_tapes (c : Cmd) (k : Nat) :
    (Compile.paddedBitDeciderTM c k).tapes = 1 := by
  show (composeFlatTM (Compile.padRegsTM (k + 2 * c.loopDepth + 2)) (Compile.bitDeciderTM c k)
    (Compile.padRegsExit (k + 2 * c.loopDepth + 2))).tapes = 1
  rw [composeFlatTM_tapes, Compile.padRegsTM_tapes]

/-- Halt bits of `paddedBitDeciderTM` past `(Compile k c).states + (padRegsTM …).states`
are the gadget's, shifted by both compositions. -/
theorem Compile.paddedBitDeciderTM_halt_shift (c : Cmd) (k i : Nat) :
    (Compile.paddedBitDeciderTM c k).halt.getD
        (i + (Compile k c).states + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states) false
      = Compile.bitTestTM.halt.getD i false := by
  show (composedHalt (Compile.padRegsTM (k + 2 * c.loopDepth + 2)) (Compile.bitDeciderTM c k)).getD
      (i + (Compile k c).states + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states) false = _
  rw [composedHalt, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate]
  have he : i + (Compile k c).states + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states
      - (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states = i + (Compile k c).states := by omega
  rw [he, ← List.getD_eq_getElem?_getD]
  exact Compile.bitDeciderTM_halt_shift c k i

/-- **★ The padded decider run (PROVEN from the `padRegsTM` interface +
`bitDecider_run`).** Runs `paddedBitDeciderTM c k` on the **narrow** input
`encodeTape s` — **no `k ≤ s.length` hypothesis** — and reaches the accept/reject
state. The pad makes `k + 2 * c.loopDepth ≤ (s ++ replicate (k + 2*c.loopDepth) []).length`
hold for the inner `bitDecider_run`, and `Cmd.eval_agree`/`cost_agree` transport the
answer/cost from the wide state back to `s`. This is the WALL resolution, validated.

`hwle : s.length ≤ k` is the **scratch-emptiness side** of the 2026-06-11 scratch
interface: the compiler's scratch block sits at registers `[k, k + 2·c.loopDepth)`,
which must be `[]` at machine start — true on the padded tape exactly when the
*input* does not itself extend past `k` (the bridges supply it from `width_le`). -/
theorem Compile.paddedBitDecider_run (c : Cmd) (s : State) (b : Nat) (k : Nat)
    (hbitst : Compile.BitState s) (hwle : s.length ≤ k)
    (huses : Cmd.UsesBelow c k)
    (hbit : b = 0 ∨ b = 1) (h0 : (c.eval s).get 0 = [b]) :
    ∃ cfg,
      runFlatTM (Compile.padBudget (k + 2 * c.loopDepth + 2) s + 1 +
            (Compile.physStepBudget
              (State.size s + (s.length + (k + 2 * c.loopDepth + 2)) + c.cost s + 2)
              (c.cost s) + 3))
          (Compile.paddedBitDeciderTM c k)
          (initFlatConfig (Compile.paddedBitDeciderTM c k) [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (Compile.paddedBitDeciderTM c k) cfg = true ∧
      cfg.state_idx
        = (if b = 1 then 1 else 2) + (Compile k c).states
          + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states := by
  set K : Nat := k + 2 * c.loopDepth + 2 with hK
  set wide : State := s ++ List.replicate K [] with hwide
  -- Facts about the widened state.
  have hbit_w : Compile.BitState wide := Compile.BitState_append_replicate_nil s K hbitst
  have hk_w : k + 2 * c.loopDepth + 2 ≤ wide.length := by
    rw [hwide, List.length_append, List.length_replicate]; omega
  have hagree : AgreeBelow k s wide :=
    fun r _ => (Compile.get_append_replicate_nil s K r).symm
  have hscratch_w : ∀ r, k ≤ r → State.get wide r = [] := by
    intro r hr
    rw [hwide, Compile.get_append_replicate_nil s K r]
    exact Compile.get_of_length_le s r (Nat.le_trans hwle hr)
  have heval0 : (c.eval s).get 0 = (c.eval wide).get 0 :=
    Cmd.eval_agree c k huses hagree 0 (Cmd.UsesBelow_pos huses)
  have h0_w : (c.eval wide).get 0 = [b] := by rw [← heval0]; exact h0
  have hcost : c.cost wide = c.cost s := (Cmd.cost_agree c k huses hagree).symm
  have hsize : State.size wide = State.size s := Compile.size_append_replicate_nil s K
  -- The inner decider run on the WIDE tape.
  obtain ⟨cfg2, hrun2, hhalt2, hstate2⟩ :=
    Compile.bitDecider_run c wide b k hbit_w hk_w huses hscratch_w hbit h0_w
  -- Rewrite its budget in terms of the narrow state's size/cost.
  have hlenw : wide.length = s.length + K := by
    rw [hwide, List.length_append, List.length_replicate]
  rw [hcost, hsize, hlenw] at hrun2
  -- Compose: pad (M₁) then the decider (M₂), spliced at `padRegsExit`.
  have hstate0 : (initFlatConfig (Compile.padRegsTM K)
      [Compile.encodeTape s]).state_idx < (Compile.padRegsTM K).states :=
    (Compile.padRegsTM_valid K).1
  -- The intermediate tape symbol (leading `endMark`) is `< max sigs`.
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0,
      Compile.encodeTape wide) = some v →
        v < max (Compile.padRegsTM K).sig (Compile.bitDeciderTM c k).sig := by
    intro v hv
    have hces : currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape wide)
        = some Compile.endMark := rfl
    have hv2 : v = Compile.endMark := ((Option.some.injEq _ _).mp (hces.symm.trans hv)).symm
    subst hv2
    have hbd : (Compile.bitDeciderTM c k).sig = max (Compile k c).sig Compile.bitTestTM.sig := by
      show (composeFlatTM (Compile k c) Compile.bitTestTM (Compile.exit k c)).sig = _
      rw [composeFlatTM_sig]
    have h4 : (4 : Nat) ≤ max (Compile.padRegsTM K).sig (Compile.bitDeciderTM c k).sig := by
      refine Nat.le_trans ?_ (Nat.le_max_right _ _)
      rw [hbd, Compile_sig]; exact Nat.le_max_left _ _
    exact Nat.lt_of_lt_of_le (by decide : Compile.endMark < 4) h4
  have hcomp := composeFlatTM_run (M₁ := Compile.padRegsTM K) (M₂ := Compile.bitDeciderTM c k)
    (exit := Compile.padRegsExit K)
    (Compile.padRegsTM_valid K) (Compile.bitDeciderTM_valid c k) (Compile.padRegsExit_lt K)
    (initFlatConfig (Compile.padRegsTM K) [Compile.encodeTape s]) hstate0
    [] 0 (Compile.encodeTape wide) hsym
    (Compile.padRegsTM_run K s hbitst) (Compile.padRegsTM_traj K s hbitst)
    hrun2 hhalt2
  obtain ⟨hcrun, hchalt⟩ := hcomp
  refine ⟨{ state_idx := cfg2.state_idx + (Compile.padRegsTM K).states,
            tapes := cfg2.tapes }, hcrun, hchalt, ?_⟩
  rw [hstate2]

/-! ## ★ The padded *compute* run — the function-side WALL resolution (2026-06-08)

The reduction side (`PolyTimeComputableLang.toFrameworkWitness'` / `ComputesBy`) faces
the **same WALL** the decider side did: `Compile_run_physical_residue` carries
`k ≤ s.length`, unsatisfiable for a narrow reduction input whose program touches
`regBound > s.length` registers. The fix is the *same* runtime register-width padding:
`paddedComputeTM c k := padRegsTM k ⨾ Compile c` widens the tape first (exactly like
`paddedBitDeciderTM`), but keeps the **full output tape** (no bit-test gadget) so a
reduction can decode an arbitrary output register. `Cmd.eval_agree`/`cost_agree`
transport the result/cost from the wide state back to `s`.

This is the function-computation analogue of `Compile.paddedBitDecider_run`, PROVEN
from the same `padRegsTM` interface + `Compile_run_physical_residue` (residual sorrys
= the pinned leaf gadgets only). It is what the retargeted `toFrameworkWitness'`
consumes in place of the (wrong-budget) `Compile_sound`. -/

/-- The padded compute machine: pad the registers to width `≥ k`, then run `Compile c`. -/
def Compile.paddedComputeTM (c : Cmd) (k : Nat) : FlatTM :=
  composeFlatTM (Compile.padRegsTM (k + 2 * c.loopDepth + 2)) (Compile k c)
    (Compile.padRegsExit (k + 2 * c.loopDepth + 2))

theorem Compile.paddedComputeTM_valid (c : Cmd) (k : Nat) :
    validFlatTM (Compile.paddedComputeTM c k) :=
  composeFlatTM_valid (Compile.padRegsTM (k + 2 * c.loopDepth + 2)) (Compile k c)
    (Compile.padRegsExit (k + 2 * c.loopDepth + 2))
    (Compile.padRegsTM_valid _) (Compile_valid k c) (Compile.padRegsExit_lt _)
    (Compile.padRegsTM_tapes _) (Compile_tapes k c)

theorem Compile.paddedComputeTM_tapes (c : Cmd) (k : Nat) :
    (Compile.paddedComputeTM c k).tapes = 1 := by
  show (composeFlatTM (Compile.padRegsTM (k + 2 * c.loopDepth + 2)) (Compile k c)
    (Compile.padRegsExit (k + 2 * c.loopDepth + 2))).tapes = 1
  rw [composeFlatTM_tapes, Compile.padRegsTM_tapes]

/-- **★ The padded compute run (PROVEN from the `padRegsTM` interface +
`Compile_run_physical_residue`).** Runs `paddedComputeTM c k` on the **narrow** input
`encodeTape s` — **no `k ≤ s.length` hypothesis** — and halts at the compiler's exit
(shifted by the padder's state count) with the tape `encodeTape (c.eval wide) ++ res`
for the widened state `wide = s ++ replicate (k + 2*c.loopDepth) []` (program
registers `< k` plus the compiler's scratch block). The pad makes the register-width
and scratch-emptiness hypotheses of the inner `Compile_run_physical_residue` hold
(`hwle : s.length ≤ k` keeps the input out of the scratch block — the bridges supply
it from `width_le`); the caller transports the decoded output from `wide` back to `s`
with `Cmd.eval_agree`. Budget: `padBudget (k + 2*c.loopDepth) s + 1 +
physStepBudget G (c.cost s)`, both `inOPoly` (`padBudget_le` / `physStepBudget_poly`). -/
theorem Compile.paddedCompute_run (c : Cmd) (s : State) (k : Nat)
    (hbitst : Compile.BitState s) (hwle : s.length ≤ k)
    (huses : Cmd.UsesBelow c k) :
    ∃ (res : List Nat),
      Compile.ValidResidue res ∧
      runFlatTM (Compile.padBudget (k + 2 * c.loopDepth + 2) s + 1 +
            Compile.physStepBudget
              (State.size s + (s.length + (k + 2 * c.loopDepth + 2)) + c.cost s + 2) (c.cost s))
          (Compile.paddedComputeTM c k)
          (initFlatConfig (Compile.paddedComputeTM c k) [Compile.encodeTape s])
        = some { state_idx := Compile.exit k c
                   + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states,
                 tapes := [([], 0,
                   Compile.encodeTape (c.eval (s ++ List.replicate (k + 2 * c.loopDepth + 2) []))
                     ++ res)] } ∧
      haltingStateReached (Compile.paddedComputeTM c k)
          { state_idx := Compile.exit k c
              + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states,
            tapes := [([], 0,
              Compile.encodeTape (c.eval (s ++ List.replicate (k + 2 * c.loopDepth + 2) []))
                ++ res)] } = true := by
  set K : Nat := k + 2 * c.loopDepth + 2 with hK
  set wide : State := s ++ List.replicate K [] with hwide
  have hbit_w : Compile.BitState wide := Compile.BitState_append_replicate_nil s K hbitst
  have hk_w : k + 2 * c.loopDepth + 2 ≤ wide.length := by
    rw [hwide, List.length_append, List.length_replicate]; omega
  have hcost : c.cost wide = c.cost s :=
    (Cmd.cost_agree c k huses
      (fun r _ => (Compile.get_append_replicate_nil s K r).symm)).symm
  have hsize : State.size wide = State.size s := Compile.size_append_replicate_nil s K
  have hscratch_w : ∀ r, k ≤ r → State.get wide r = [] := by
    intro r hr
    rw [hwide, Compile.get_append_replicate_nil s K r]
    exact Compile.get_of_length_le s r (Nat.le_trans hwle hr)
  have hlenw : wide.length = s.length + K := by
    rw [hwide, List.length_append, List.length_replicate]
  -- inner residue run on the WIDE tape
  obtain ⟨t1, res, hres, hrun2, _htraj2, ht1⟩ :=
    Compile_run_physical_residue c k wide hbit_w hk_w huses hscratch_w
  rw [hcost, hsize, hlenw] at ht1
  -- the inner exit is a halt state of `Compile k c`
  have hhalt2 : haltingStateReached (Compile k c)
      { state_idx := Compile.exit k c,
        tapes := [([], 0, Compile.encodeTape (c.eval wide) ++ res)] } = true := by
    show (Compile k c).halt.getD (Compile.exit k c) false = true
    have hex := (compileCmd k c).exit_is_halt
    show (compileCmd k c).M.halt.getD (compileCmd k c).exit false = true
    simp only [List.getD, hex, Option.getD]
  -- compose: pad (M₁) then `Compile k c` (M₂), spliced at `padRegsExit`.
  have hstate0 : (initFlatConfig (Compile.padRegsTM K)
      [Compile.encodeTape s]).state_idx < (Compile.padRegsTM K).states :=
    (Compile.padRegsTM_valid K).1
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0,
      Compile.encodeTape wide) = some v →
        v < max (Compile.padRegsTM K).sig (Compile k c).sig := by
    intro v hv
    have hces : currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape wide)
        = some Compile.endMark := rfl
    have hv2 : v = Compile.endMark := ((Option.some.injEq _ _).mp (hces.symm.trans hv)).symm
    subst hv2
    have h4 : (4 : Nat) ≤ max (Compile.padRegsTM K).sig (Compile k c).sig :=
      Nat.le_trans (Nat.le_of_eq (Compile_sig k c).symm) (Nat.le_max_right _ _)
    exact Nat.lt_of_lt_of_le (by decide : Compile.endMark < 4) h4
  have hcomp := composeFlatTM_run (M₁ := Compile.padRegsTM K) (M₂ := Compile k c)
    (exit := Compile.padRegsExit K)
    (Compile.padRegsTM_valid K) (Compile_valid k c) (Compile.padRegsExit_lt K)
    (initFlatConfig (Compile.padRegsTM K) [Compile.encodeTape s]) hstate0
    [] 0 (Compile.encodeTape wide) hsym
    (Compile.padRegsTM_run K s hbitst) (Compile.padRegsTM_traj K s hbitst)
    hrun2 hhalt2
  obtain ⟨hcrun, hchalt⟩ := hcomp
  refine ⟨res, hres, ?_, hchalt⟩
  -- pad the composed run out to the (poly) stated budget
  obtain ⟨kpad, hkpad⟩ := Nat.le.dest ht1
  have hbudget : Compile.padBudget K s + 1 +
      Compile.physStepBudget (State.size s + (s.length + K) + c.cost s + 2) (c.cost s)
      = (Compile.padBudget K s + 1 + t1) + kpad := by omega
  rw [hbudget]
  exact runFlatTM_extend (M := Compile.paddedComputeTM c k) hcrun hchalt

