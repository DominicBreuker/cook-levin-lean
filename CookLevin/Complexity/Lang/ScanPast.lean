import Complexity.Complexity.TMPrimitives

set_option autoImplicit false

/-! # Scan-past-delimiter primitive (Risk C1 of `ROADMAP.md`)

`scanPastDelimTM sig target` is a one-symbol variant of
`TMPrimitives.scanRightUntilTM`: it scans right over a `target`-free block
and, on reaching the first `target`, steps **one cell past it** (`Rmove`)
before halting in the accept state `1` — whereas `scanRightUntilTM` halts
*on* the target (`Nmove`).

This is the navigation step used to walk *across* a register delimiter onto
the start of the next register, so that the per-`Op` machines can recurse on
`dst`: `opAppendOne (d+1) = composeFlatTM (scanPastDelimTM 4 0) (opAppendOne
d) …` puts the head at the start of register `1`, after which the recursive
machine (always the *second* component) handles the remaining `d`. Because
the recursive machine is `M₂`, only this small fixed machine's trajectory is
ever needed for `composeFlatTM_run`.

The three states mirror `scanRightUntilTM`: `0` = scanning, `1` = accept
(stepped past the delimiter), `2` = reject (ran off the end). -/

namespace Complexity.Lang.ScanPast

open TMPrimitives

/-- The found-and-step-past entry: in state `0`, reading `target`, move
right and accept. (Differs from `scanRightUntilTM`'s halt entry only in the
move: `Rmove` instead of `Nmove`.) -/
def pastEntry (target : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some target]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

/-- Off-the-end entry: reject. -/
def pastNoneEntry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [none]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

/-- Keep-scanning entry for a non-`target` symbol. -/
def pastContinueEntry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 0
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

/-- Transition table for `scanPastDelimTM`. -/
def scanPastDelimTM_trans (sig target : Nat) : List FlatTMTransEntry :=
  pastEntry target :: pastNoneEntry ::
    ((List.range sig).filter (fun v => decide (v ≠ target))).map pastContinueEntry

/-- Scan right to the first `target`, then step one cell past it. -/
def scanPastDelimTM (sig target : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 3
  trans := scanPastDelimTM_trans sig target
  start := 0
  halt := [false, true, true]

theorem scanPastDelimTM_trans_eq (sig target : Nat) :
    (scanPastDelimTM sig target).trans =
      pastEntry target :: pastNoneEntry ::
        ((List.range sig).filter (fun v => decide (v ≠ target))).map pastContinueEntry := rfl

theorem scanPastDelimTM_valid (sig target : Nat) (h_target : target < sig) :
    validFlatTM (scanPastDelimTM sig target) := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 3; decide
  · show [false, true, true].length = 3; rfl
  · intro entry hentry
    have hentry' : entry ∈ scanPastDelimTM_trans sig target := hentry
    unfold scanPastDelimTM_trans at hentry'
    rcases List.mem_cons.mp hentry' with hPast | hRest
    · subst hPast
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 3; decide
      · show 1 < 3; decide
      · intro x hx; simp [pastEntry] at hx; subst hx; exact h_target
      · intro x hx; simp [pastEntry] at hx; subst hx; trivial
    · rcases List.mem_cons.mp hRest with hNone | hCont
      · subst hNone
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 3; decide
        · show 2 < 3; decide
        · intro x hx; simp [pastNoneEntry] at hx; subst hx; trivial
        · intro x hx; simp [pastNoneEntry] at hx; subst hx; trivial
      · rcases List.mem_map.mp hCont with ⟨v, hv, hmk⟩
        subst hmk
        have hvlt : v < sig := List.mem_range.mp (List.mem_filter.mp hv).1
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 3; decide
        · show 0 < 3; decide
        · intro x hx; simp [pastContinueEntry] at hx; subst hx; exact hvlt
        · intro x hx; simp [pastContinueEntry] at hx; subst hx; trivial

/-- `applyTransitionEntry` for a single-tape entry with `dst_write_vals =
[none]`: only the state and head change. -/
private theorem applyEntry_single
    (cfg_state new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) (move : TMMove) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(left, head, right)] }
        { src_state := cfg_state
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [move] } =
      some { state_idx := new_state
             tapes := [moveTapeHead (left, head, right) move] } := rfl

/-- Step on the `target` symbol: move right and accept (state 1). -/
theorem scanPastDelimTM_step_found
    (sig target : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = target) :
    stepFlatTM (scanPastDelimTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some target := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig (pastEntry target) cfg = true := by
    show ((0 : Nat) == 0 &&
            decide (([some target] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; simp
  show Option.bind ((scanPastDelimTM sig target).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [scanPastDelimTM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry cfg (pastEntry target) = _
  exact applyEntry_single 0 1 left right head (some target) TMMove.Rmove

/-- Helper: `find?` over the continue-entry list returns
`pastContinueEntry v` when `v` is present and no earlier element matches. -/
private theorem find_pastContinue_match
    (cfg : FlatTMConfig) (v : Nat) (L : List Nat)
    (h_cfg_state : cfg.state_idx = 0)
    (h_cfg_tape : cfg.tapes.map currentTapeSymbol = [some v])
    (h_mem : v ∈ L)
    (h_first : ∀ {w : Nat}, w ∈ L → w ≠ v →
      entryMatchesConfig (pastContinueEntry w) cfg = false) :
    (L.map pastContinueEntry).find?
        (fun entry => entryMatchesConfig entry cfg) =
      some (pastContinueEntry v) := by
  induction L with
  | nil => cases h_mem
  | cons w ws ih =>
      show List.find? _ (pastContinueEntry w :: ws.map pastContinueEntry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (pastContinueEntry w) cfg = true := by
          show ((0 : Nat) == cfg.state_idx &&
                  decide (([some w] : List (Option Nat)) =
                    cfg.tapes.map currentTapeSymbol)) = true
          rw [h_cfg_state, h_cfg_tape]; simp
        rw [hMatch]
      · have hNot := h_first (List.mem_cons.mpr (Or.inl rfl)) hwv
        rw [hNot]
        rcases List.mem_cons.mp h_mem with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws (fun hw hne => h_first (List.mem_cons.mpr (Or.inr hw)) hne)

/-- Step on a non-`target` in-range symbol: advance the head, stay scanning. -/
theorem scanPastDelimTM_step_advance
    (sig target : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : right.get ⟨head, h_head_lt⟩ < sig)
    (h_ne : right.get ⟨head, h_head_lt⟩ ≠ target) :
    stepFlatTM (scanPastDelimTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 0, tapes := [(left, head + 1, right)] } := by
  set v := right.get ⟨head, h_head_lt⟩ with hv
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym0 : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt]
  have hSym : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym0]
  have hNotPast : entryMatchesConfig (pastEntry target) cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some target] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([some target] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne']
  have hNotNone : entryMatchesConfig pastNoneEntry cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([none] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; cases h1
    simp [h_ne']
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ target)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, ?_⟩
    exact decide_eq_true h_ne
  have hFindCont :
      (((List.range sig).filter (fun w => decide (w ≠ target))).map pastContinueEntry).find?
          (fun entry => entryMatchesConfig entry cfg) =
        some (pastContinueEntry v) := by
    refine find_pastContinue_match cfg v _ rfl hSym hvInFilter ?_
    intro w _ hwv
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact hwv h2
    simp [h_ne']
  show Option.bind ((scanPastDelimTM sig target).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [scanPastDelimTM_trans_eq]
  rw [List.find?_cons, hNotPast, List.find?_cons, hNotNone, hFindCont]
  show applyTransitionEntry cfg (pastContinueEntry v) = _
  exact applyEntry_single 0 0 left right head (some v) TMMove.Rmove

/-- `runFlatTM` unfolds one step from a non-halting state-0 config. -/
private theorem run0_unfold
    (sig target n : Nat)
    (tapes : List (List Nat × Nat × List Nat)) (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (scanPastDelimTM sig target)
        { state_idx := 0, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (scanPastDelimTM sig target)
        { state_idx := 0, tapes := tapes } =
      runFlatTM n (scanPastDelimTM sig target) cfg' := by
  show (if haltingStateReached (scanPastDelimTM sig target)
            { state_idx := 0, tapes := tapes } = true then
          some { state_idx := 0, tapes := tapes }
        else
          match stepFlatTM (scanPastDelimTM sig target)
              { state_idx := 0, tapes := tapes } with
          | none => some { state_idx := 0, tapes := tapes }
          | some cfg' => runFlatTM n (scanPastDelimTM sig target) cfg') =
    runFlatTM n (scanPastDelimTM sig target) cfg'
  rw [show haltingStateReached (scanPastDelimTM sig target)
        { state_idx := 0, tapes := tapes } = false from rfl, h_step]
  rfl

/-- **Run lemma.** Scanning a `target`-free block `body` (in-range, no
`target`) from the start of `body` and stepping past the delimiter: after
`body.length + 1` steps the machine halts in state `1`, head one cell
**past** the marker. -/
theorem scanPastDelim_run (sig target : Nat) (left right : List Nat) :
    ∀ (gap head : Nat) (h_in_range : head + gap < right.length),
      right.get ⟨head + gap, h_in_range⟩ = target →
      (∀ k, k < gap → ∃ (h : head + k < right.length),
        right.get ⟨head + k, h⟩ < sig ∧
          right.get ⟨head + k, h⟩ ≠ target) →
      runFlatTM (gap + 1) (scanPastDelimTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 1, tapes := [(left, head + gap + 1, right)] }
  | 0, head, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨head, h_lt⟩ = target := by
        have heq : (⟨head + 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero head)
        rw [← heq]; exact h_get_target
      rw [run0_unfold sig target 0 _ _
        (scanPastDelimTM_step_found sig target left right head h_lt h_get)]
      show (some { state_idx := 1, tapes := [(left, head + 1, right)] } : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head + 0 + 1, right)] }
      rw [Nat.add_zero]
  | gap + 1, head, h_in_range, h_get_target, h_before => by
      have h_head_lt : head < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right head (gap + 1)) h_in_range
      rcases h_before 0 (Nat.zero_lt_succ _) with ⟨h_kk, h_sym_lt, h_sym_ne⟩
      have heq0 : (⟨head + 0, h_kk⟩ : Fin right.length) = ⟨head, h_head_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero head)
      have h_get_head : right.get ⟨head, h_head_lt⟩ < sig := by
        rw [heq0] at h_sym_lt; exact h_sym_lt
      have h_get_head_ne : right.get ⟨head, h_head_lt⟩ ≠ target := by
        rw [heq0] at h_sym_ne; exact h_sym_ne
      have h_succ : (head + 1) + gap = head + (gap + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 gap]
      have h_in_range' : (head + 1) + gap < right.length := by
        rw [h_succ]; exact h_in_range
      have h_get_target' :
          right.get ⟨(head + 1) + gap, h_in_range'⟩ = target := by
        have heq : (⟨(head + 1) + gap, h_in_range'⟩ : Fin right.length) =
            ⟨head + (gap + 1), h_in_range⟩ := Fin.eq_of_val_eq h_succ
        rw [heq]; exact h_get_target
      have h_before' :
          ∀ k, k < gap → ∃ (h : (head + 1) + k < right.length),
            right.get ⟨(head + 1) + k, h⟩ < sig ∧
              right.get ⟨(head + 1) + k, h⟩ ≠ target := by
        intro k hk
        rcases h_before (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk, h1, h2⟩
        have hShift : head + (k + 1) = (head + 1) + k := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        have h_kk' : (head + 1) + k < right.length := hShift ▸ h_kk
        refine ⟨h_kk', ?_, ?_⟩
        · have heq : (⟨(head + 1) + k, h_kk'⟩ : Fin right.length) =
              ⟨head + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
          rw [heq]; exact h1
        · have heq : (⟨(head + 1) + k, h_kk'⟩ : Fin right.length) =
              ⟨head + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
          rw [heq]; exact h2
      have hih :=
        scanPastDelim_run sig target left right gap (head + 1)
          h_in_range' h_get_target' h_before'
      rw [run0_unfold sig target (gap + 1) _ _
        (scanPastDelimTM_step_advance sig target left right head h_head_lt
          h_get_head h_get_head_ne)]
      rw [hih]
      show (some { state_idx := 1, tapes := [(left, (head + 1) + gap + 1, right)] } : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head + (gap + 1) + 1, right)] }
      rw [h_succ]
  termination_by gap _ _ _ _ => gap

/-- **Trajectory.** Every intermediate config of the scan (before the
found-step) is in the non-halting state `0`, head advanced by the step
count — provided each cell scanned is in-range and not `target`. -/
theorem scanPastDelim_traj (sig target : Nat) (left right : List Nat) (head : Nat) :
    ∀ k, (∀ j, j < k → ∃ (h : head + j < right.length),
            right.get ⟨head + j, h⟩ < sig ∧ right.get ⟨head + j, h⟩ ≠ target) →
      runFlatTM k (scanPastDelimTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] }
        = some { state_idx := 0, tapes := [(left, head + k, right)] }
  | 0, _ => by rw [Nat.add_zero]; rfl
  | k + 1, hb => by
      have ih := scanPastDelim_traj sig target left right head k
        (fun j hj => hb j (Nat.lt_succ_of_lt hj))
      rcases hb k (Nat.lt_succ_self k) with ⟨h_lt, h_sym_lt, h_sym_ne⟩
      have h_step := scanPastDelimTM_step_advance sig target left right (head + k)
        h_lt h_sym_lt h_sym_ne
      have h_nothalt :
          haltingStateReached (scanPastDelimTM sig target)
            { state_idx := 0, tapes := [(left, head + k, right)] } = false := rfl
      have h := runFlatTM_extend_by_step (scanPastDelimTM sig target) k _ _ _
        ih h_nothalt h_step
      rw [show head + (k + 1) = (head + k) + 1 from by omega]
      exact h

/-- The trajectory in `composeFlatTM_run`'s `h_traj1` shape (exit state `1`):
across all `gap + 1` steps the scan never reaches state `1` and never halts. -/
theorem scanPastDelim_no_early_halt (sig target : Nat) (left right : List Nat)
    (head gap : Nat)
    (hb : ∀ j, j < gap → ∃ (h : head + j < right.length),
            right.get ⟨head + j, h⟩ < sig ∧ right.get ⟨head + j, h⟩ ≠ target) :
    ∀ k, k < gap + 1 → ∀ ck,
      runFlatTM k (scanPastDelimTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ 1 ∧
      haltingStateReached (scanPastDelimTM sig target) ck = false := by
  intro k hk ck hck
  have hk' : k ≤ gap := Nat.lt_succ_iff.mp hk
  have htraj := scanPastDelim_traj sig target left right head k
    (fun j hj => hb j (Nat.lt_of_lt_of_le hj hk'))
  rw [htraj] at hck
  obtain rfl : ck = { state_idx := 0, tapes := [(left, head + k, right)] } :=
    (Option.some.inj hck).symm
  exact ⟨Nat.zero_ne_one, rfl⟩

end Complexity.Lang.ScanPast
