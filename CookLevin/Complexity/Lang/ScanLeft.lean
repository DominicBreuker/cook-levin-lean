import Complexity.Complexity.TMPrimitives

set_option autoImplicit false

/-! # Scan-left-to-marker primitive (Risk C2 of `ROADMAP.md`)

`scanLeftUntilTM sig target` is the leftward mirror of
`TMPrimitives.scanRightUntilTM`: from the current head it scans **left**
(`Lmove`) over a `target`-free block and halts in the accept state `1` on
reaching the first `target`, *on* that cell (`Nmove`).

Its purpose is the **head-rewind** needed for `compileSeq` composition: a
compiled `Op` halts with its head mid-tape, but `composeFlatTM` resumes the
next machine on that exact tape+head, while every per-`Op` soundness
statement assumes the head starts at `0` (`initFlatConfig`). Reusing the
end-of-tape terminator `endMark = 3` as a *leading* sentinel
(`encodeTape s = 3 :: encodeRegs s ++ [3]`), `scanLeftUntilTM 4 3` scans left
to that leading `3` at index `0`, restoring the canonical start config.

The three states mirror `scanRightUntilTM`: `0` = scanning, `1` = accept (on
the target), `2` = reject (ran off the left end into a blank). -/

namespace Complexity.Lang.ScanLeft

open TMPrimitives

/-- Found entry: in state `0`, reading `target`, accept without moving. -/
def leftFoundEntry (target : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some target]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

/-- Off-the-end entry: reject. -/
def leftNoneEntry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [none]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

/-- Keep-scanning entry for a non-`target` symbol: move left. -/
def leftContinueEntry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 0
    dst_write_vals := [none]
    move_dirs := [TMMove.Lmove] }

/-- Transition table for `scanLeftUntilTM`. -/
def scanLeftUntilTM_trans (sig target : Nat) : List FlatTMTransEntry :=
  leftFoundEntry target :: leftNoneEntry ::
    ((List.range sig).filter (fun v => decide (v ≠ target))).map leftContinueEntry

/-- Scan left to the first `target`, halting on it. -/
def scanLeftUntilTM (sig target : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 3
  trans := scanLeftUntilTM_trans sig target
  start := 0
  halt := [false, true, true]

theorem scanLeftUntilTM_trans_eq (sig target : Nat) :
    (scanLeftUntilTM sig target).trans =
      leftFoundEntry target :: leftNoneEntry ::
        ((List.range sig).filter (fun v => decide (v ≠ target))).map leftContinueEntry := rfl

theorem scanLeftUntilTM_valid (sig target : Nat) (h_target : target < sig) :
    validFlatTM (scanLeftUntilTM sig target) := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 3; decide
  · show [false, true, true].length = 3; rfl
  · intro entry hentry
    have hentry' : entry ∈ scanLeftUntilTM_trans sig target := hentry
    unfold scanLeftUntilTM_trans at hentry'
    rcases List.mem_cons.mp hentry' with hFound | hRest
    · subst hFound
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 3; decide
      · show 1 < 3; decide
      · intro x hx; simp [leftFoundEntry] at hx; subst hx; exact h_target
      · intro x hx; simp [leftFoundEntry] at hx; subst hx; trivial
    · rcases List.mem_cons.mp hRest with hNone | hCont
      · subst hNone
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 3; decide
        · show 2 < 3; decide
        · intro x hx; simp [leftNoneEntry] at hx; subst hx; trivial
        · intro x hx; simp [leftNoneEntry] at hx; subst hx; trivial
      · rcases List.mem_map.mp hCont with ⟨v, hv, hmk⟩
        subst hmk
        have hvlt : v < sig := List.mem_range.mp (List.mem_filter.mp hv).1
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 3; decide
        · show 0 < 3; decide
        · intro x hx; simp [leftContinueEntry] at hx; subst hx; exact hvlt
        · intro x hx; simp [leftContinueEntry] at hx; subst hx; trivial

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

/-- Step on the `target` symbol: accept (state 1), head unchanged. -/
theorem scanLeftUntilTM_step_found
    (sig target : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = target) :
    stepFlatTM (scanLeftUntilTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some target := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig (leftFoundEntry target) cfg = true := by
    show ((0 : Nat) == 0 &&
            decide (([some target] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; simp
  show Option.bind ((scanLeftUntilTM sig target).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [scanLeftUntilTM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry cfg (leftFoundEntry target) = _
  exact applyEntry_single 0 1 left right head (some target) TMMove.Nmove

/-- Helper: `find?` over the continue-entry list returns `leftContinueEntry v`
when `v` is present and no earlier element matches. -/
private theorem find_leftContinue_match
    (cfg : FlatTMConfig) (v : Nat) (L : List Nat)
    (h_cfg_state : cfg.state_idx = 0)
    (h_cfg_tape : cfg.tapes.map currentTapeSymbol = [some v])
    (h_mem : v ∈ L)
    (h_first : ∀ {w : Nat}, w ∈ L → w ≠ v →
      entryMatchesConfig (leftContinueEntry w) cfg = false) :
    (L.map leftContinueEntry).find?
        (fun entry => entryMatchesConfig entry cfg) =
      some (leftContinueEntry v) := by
  induction L with
  | nil => cases h_mem
  | cons w ws ih =>
      show List.find? _ (leftContinueEntry w :: ws.map leftContinueEntry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (leftContinueEntry w) cfg = true := by
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

/-- Step on a non-`target` in-range symbol: move left, stay scanning. -/
theorem scanLeftUntilTM_step_advance
    (sig target : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : right.get ⟨head, h_head_lt⟩ < sig)
    (h_ne : right.get ⟨head, h_head_lt⟩ ≠ target) :
    stepFlatTM (scanLeftUntilTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 0, tapes := [(left, head - 1, right)] } := by
  set v := right.get ⟨head, h_head_lt⟩ with hv
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym0 : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt]
  have hSym : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym0]
  have hNotFound : entryMatchesConfig (leftFoundEntry target) cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some target] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([some target] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne']
  have hNotNone : entryMatchesConfig leftNoneEntry cfg = false := by
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
      (((List.range sig).filter (fun w => decide (w ≠ target))).map leftContinueEntry).find?
          (fun entry => entryMatchesConfig entry cfg) =
        some (leftContinueEntry v) := by
    refine find_leftContinue_match cfg v _ rfl hSym hvInFilter ?_
    intro w _ hwv
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact hwv h2
    simp [h_ne']
  show Option.bind ((scanLeftUntilTM sig target).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [scanLeftUntilTM_trans_eq]
  rw [List.find?_cons, hNotFound, List.find?_cons, hNotNone, hFindCont]
  show applyTransitionEntry cfg (leftContinueEntry v) = _
  exact applyEntry_single 0 0 left right head (some v) TMMove.Lmove

/-- `runFlatTM` unfolds one step from a non-halting state-0 config. -/
private theorem run0_unfold
    (sig target n : Nat)
    (tapes : List (List Nat × Nat × List Nat)) (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (scanLeftUntilTM sig target)
        { state_idx := 0, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (scanLeftUntilTM sig target)
        { state_idx := 0, tapes := tapes } =
      runFlatTM n (scanLeftUntilTM sig target) cfg' := by
  show (if haltingStateReached (scanLeftUntilTM sig target)
            { state_idx := 0, tapes := tapes } = true then
          some { state_idx := 0, tapes := tapes }
        else
          match stepFlatTM (scanLeftUntilTM sig target)
              { state_idx := 0, tapes := tapes } with
          | none => some { state_idx := 0, tapes := tapes }
          | some cfg' => runFlatTM n (scanLeftUntilTM sig target) cfg') =
    runFlatTM n (scanLeftUntilTM sig target) cfg'
  rw [show haltingStateReached (scanLeftUntilTM sig target)
        { state_idx := 0, tapes := tapes } = false from rfl, h_step]
  rfl

/-- **Run lemma.** Scanning left from `head` to the `target` at index `0`:
given `right[0] = target` and that every cell `1 ≤ i ≤ head` is in-range and
not `target`, after `head + 1` steps the machine halts in state `1` with the
head rewound to `0`. -/
theorem scanLeft_run (sig target : Nat) (left right : List Nat)
    (h0 : 0 < right.length) (h_target0 : right.get ⟨0, h0⟩ = target) :
    ∀ (head : Nat) (h_head_lt : head < right.length),
      (∀ i, 0 < i → i ≤ head → ∃ (h : i < right.length),
        right.get ⟨i, h⟩ < sig ∧ right.get ⟨i, h⟩ ≠ target) →
      runFlatTM (head + 1) (scanLeftUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 1, tapes := [(left, 0, right)] }
  | 0, h_head_lt, _ => by
      have h_get : right.get ⟨0, h_head_lt⟩ = target := h_target0
      rw [run0_unfold sig target 0 _ _
        (scanLeftUntilTM_step_found sig target left right 0 h_head_lt h_get)]
      rfl
  | head + 1, h_head_lt, hb => by
      rcases hb (head + 1) (Nat.succ_pos head) (Nat.le_refl _) with
        ⟨h_lt, h_sym_lt, h_sym_ne⟩
      have heq : (⟨head + 1, h_head_lt⟩ : Fin right.length) = ⟨head + 1, h_lt⟩ := rfl
      have h_get_lt : right.get ⟨head + 1, h_head_lt⟩ < sig := by rw [heq]; exact h_sym_lt
      have h_get_ne : right.get ⟨head + 1, h_head_lt⟩ ≠ target := by rw [heq]; exact h_sym_ne
      have h_head_lt' : head < right.length := Nat.lt_of_succ_lt h_head_lt
      have hb' : ∀ i, 0 < i → i ≤ head → ∃ (h : i < right.length),
          right.get ⟨i, h⟩ < sig ∧ right.get ⟨i, h⟩ ≠ target :=
        fun i hi hle => hb i hi (Nat.le_succ_of_le hle)
      have hih := scanLeft_run sig target left right h0 h_target0 head h_head_lt' hb'
      rw [run0_unfold sig target (head + 1) _ _
        (scanLeftUntilTM_step_advance sig target left right (head + 1) h_head_lt
          h_get_lt h_get_ne)]
      show runFlatTM (head + 1) (scanLeftUntilTM sig target)
          { state_idx := 0, tapes := [(left, head + 1 - 1, right)] } = _
      rw [Nat.add_sub_cancel]
      exact hih
  termination_by head _ _ => head

/-- **Trajectory.** For `k ≤ head`, after `k` left-scan steps the machine is
still in state `0` with the head at `head - k` — provided every scanned cell
`head - k < i ≤ head` is in-range and not `target`. Stated in the
`composeFlatTM_run` `h_traj1` form (never reaches state `1`, never halts). -/
theorem scanLeft_no_early_halt (sig target : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (hb : ∀ i, 0 < i → i ≤ head → ∃ (h : i < right.length),
      right.get ⟨i, h⟩ < sig ∧ right.get ⟨i, h⟩ ≠ target) :
    ∀ k, k < head + 1 → ∀ ck,
      runFlatTM k (scanLeftUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ 1 ∧
      haltingStateReached (scanLeftUntilTM sig target) ck = false := by
  intro k hk ck hck
  have hk' : k ≤ head := Nat.lt_succ_iff.mp hk
  have htraj : ∀ (m : Nat), m ≤ head →
      runFlatTM m (scanLeftUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 0, tapes := [(left, head - m, right)] } := by
    intro m
    induction m with
    | zero => intro _; rw [Nat.sub_zero]; rfl
    | succ n ih =>
        intro hn
        have hn' : n ≤ head := Nat.le_of_succ_le hn
        have ihn := ih hn'
        have h_pos : 0 < head - n := by omega
        have h_idx_lt : head - n < right.length := by omega
        have h_idx_le : head - n ≤ head := Nat.sub_le head n
        rcases hb (head - n) h_pos h_idx_le with ⟨h_lt, h_sym_lt, h_sym_ne⟩
        have heq : (⟨head - n, h_idx_lt⟩ : Fin right.length) = ⟨head - n, h_lt⟩ := rfl
        have h_step := scanLeftUntilTM_step_advance sig target left right (head - n)
          h_idx_lt (by rw [heq]; exact h_sym_lt) (by rw [heq]; exact h_sym_ne)
        have h_nothalt :
            haltingStateReached (scanLeftUntilTM sig target)
              { state_idx := 0, tapes := [(left, head - n, right)] } = false := rfl
        have h := runFlatTM_extend_by_step (scanLeftUntilTM sig target) n _ _ _
          ihn h_nothalt h_step
        rw [show head - (n + 1) = head - n - 1 from by omega]
        exact h
  rw [htraj k hk'] at hck
  obtain rfl : ck = { state_idx := 0, tapes := [(left, head - k, right)] } :=
    (Option.some.inj hck).symm
  exact ⟨Nat.zero_ne_one, rfl⟩

/-! ### Head-rewind specialisation (the `compileSeq` composition primitive)

The two lemmas above are the general scan-left run/trajectory. The two below
specialise them to the **leading-sentinel** tape shape `m :: rest`, rewinding
the head from an interior position back to index `0` (the sentinel). This is the
canonical `Compile` tape under the leading-sentinel encoding `encodeTape s =
endMark :: encodeRegs s ++ [endMark]` (`m = endMark = 3`, `sig = 4`).

⚠ The hypothesis is **head-relative**: only the cells `rest[0 … head-1]` (the
ones the leftward scan actually reads) must be in range and `≠ m`. This is
essential because the canonical tape has *two* `endMark = 3` cells — the leading
sentinel **and** the trailing terminator — so a "no `m` anywhere in `rest`"
hypothesis would be false. The trailing `endMark` sits to the *right* of any
interior head and is never scanned, so it is unconstrained. -/

/-- Helper: from the head-relative cell hypothesis on `rest`, derive the
index-based hypothesis `scanLeft_run` / `scanLeft_no_early_halt` consume on
`m :: rest`. -/
private theorem rewind_scan_hyp (sig m : Nat) (rest : List Nat) (head : Nat)
    (h_cells : ∀ i, i < head → ∃ (h : i < rest.length),
      rest.get ⟨i, h⟩ < sig ∧ rest.get ⟨i, h⟩ ≠ m) :
    ∀ i, 0 < i → i ≤ head → ∃ (h : i < (m :: rest).length),
      (m :: rest).get ⟨i, h⟩ < sig ∧ (m :: rest).get ⟨i, h⟩ ≠ m := by
  intro i hi hile
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨hjr, hjlt, hjne⟩ := h_cells j (by omega)
  have hi' : j + 1 < (m :: rest).length := by simp only [List.length_cons]; omega
  have hget : (m :: rest).get ⟨j + 1, hi'⟩ = rest.get ⟨j, hjr⟩ := rfl
  refine ⟨hi', ?_⟩
  rw [hget]; exact ⟨hjlt, hjne⟩

/-- **Head-rewind run lemma.** On a tape `m :: rest`, `scanLeftUntilTM sig m`
started from an interior head `head ≤ rest.length` whose preceding cells
`rest[0 … head-1]` are in range and `≠ m` halts in `head + 1` steps in the
accept state `1` with the head rewound to `0`, leaving the tape unchanged. The
`h_run1` shape of `composeFlatTM_run`. -/
theorem rewindToStart_run (sig m : Nat) (left rest : List Nat) (head : Nat)
    (h_head : head ≤ rest.length)
    (h_cells : ∀ i, i < head → ∃ (h : i < rest.length),
      rest.get ⟨i, h⟩ < sig ∧ rest.get ⟨i, h⟩ ≠ m) :
    runFlatTM (head + 1) (scanLeftUntilTM sig m)
        { state_idx := 0, tapes := [(left, head, m :: rest)] } =
      some { state_idx := 1, tapes := [(left, 0, m :: rest)] } := by
  have h0 : 0 < (m :: rest).length := by simp
  have h_head_lt : head < (m :: rest).length := by simp only [List.length_cons]; omega
  exact scanLeft_run sig m left (m :: rest) h0 rfl head h_head_lt
    (rewind_scan_hyp sig m rest head h_cells)

/-- **Head-rewind trajectory.** Before the rewind completes (`k < head + 1`) the
scanner is still in the scanning state, having neither reached the accept state
`1` nor halted. The `h_traj1` shape of `composeFlatTM_run`. -/
theorem rewindToStart_traj (sig m : Nat) (left rest : List Nat) (head : Nat)
    (h_head : head ≤ rest.length)
    (h_cells : ∀ i, i < head → ∃ (h : i < rest.length),
      rest.get ⟨i, h⟩ < sig ∧ rest.get ⟨i, h⟩ ≠ m) :
    ∀ k, k < head + 1 → ∀ ck,
      runFlatTM k (scanLeftUntilTM sig m)
          { state_idx := 0, tapes := [(left, head, m :: rest)] } = some ck →
      ck.state_idx ≠ 1 ∧
      haltingStateReached (scanLeftUntilTM sig m) ck = false := by
  have h_head_lt : head < (m :: rest).length := by simp only [List.length_cons]; omega
  exact scanLeft_no_early_halt sig m left (m :: rest) head h_head_lt
    (rewind_scan_hyp sig m rest head h_cells)

/-! ### Rewind from the *trailing* terminator (`rewindFromEndTM`)

⚠ **Risk-C2 finding (verified 2026-05-30).** The append/insert gadget
(`AppendGadget.appendAtTM`) does **not** exit with its head "just left of the
trailing terminator" (as earlier docstrings claimed): `insertCarryTM_run` leaves
the head on the **last** tape cell — i.e. *on* the trailing terminator
`endMark = 3`. Empirically, `appendAtTM 2 0` on `[3,2,1,0,1,2,0,3]` exits at
`head = 8` of the 9-cell output `[3,2,1,2,0,1,2,0,3]` — the trailing `3`.

Therefore `scanLeftUntilTM 4 3` started there **halts immediately** (it reads
its target `3` on the very first cell) instead of rewinding to index `0`. The
canonical tape has *two* `3`s, and the head sits on the *wrong* one.

`rewindFromEndTM` fixes this: an unconditional one-step left move (`stepLeftTM`)
slides the head off the trailing terminator onto the marker-free interior, after
which `scanLeftUntilTM sig target` scans left to the **leading** sentinel at
index `0`. This is the rewind the per-fragment physical contract actually needs.

The starting cell (the terminator) is therefore *unconstrained* — only the
interior cells `1 … head-1` (the ones the leftward scan reads) must be in range
and `≠ target`. -/

/-- Unconditional left-move entry for a concrete in-range symbol `v`. -/
def stepLeftEntry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Lmove] }

/-- Unconditional left-move entry for a blank cell (off the right end). -/
def stepLeftNoneEntry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [none]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Lmove] }

/-- A two-state machine that moves the head left exactly once (for any current
symbol), then halts in state `1`. Used to step off the trailing terminator
before a leftward rewind scan. -/
def stepLeftTM (sig : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 2
  trans := stepLeftNoneEntry :: (List.range sig).map stepLeftEntry
  start := 0
  halt := [false, true]

theorem stepLeftTM_trans_eq (sig : Nat) :
    (stepLeftTM sig).trans = stepLeftNoneEntry :: (List.range sig).map stepLeftEntry := rfl

theorem stepLeftTM_valid (sig : Nat) : validFlatTM (stepLeftTM sig) := by
  refine ⟨show (0 : Nat) < 2 from by decide, rfl, ?_⟩
  intro entry hentry
  have hentry' : entry ∈ stepLeftNoneEntry :: (List.range sig).map stepLeftEntry := hentry
  rcases List.mem_cons.mp hentry' with hNone | hCont
  · subst hNone
    refine ⟨show (0 : Nat) < 2 from by decide, show (1 : Nat) < 2 from by decide,
      rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp [stepLeftNoneEntry] at hx; subst hx; trivial
    · intro x hx; simp [stepLeftNoneEntry] at hx; subst hx; trivial
  · rcases List.mem_map.mp hCont with ⟨v, hv, hmk⟩
    subst hmk
    have hvlt : v < sig := List.mem_range.mp hv
    refine ⟨show (0 : Nat) < 2 from by decide, show (1 : Nat) < 2 from by decide,
      rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp [stepLeftEntry] at hx; subst hx; exact hvlt
    · intro x hx; simp [stepLeftEntry] at hx; subst hx; trivial

/-- `find?` over the step-left entry list returns `stepLeftEntry v` when the head
reads the in-range symbol `v`. -/
private theorem find_stepLeft_match
    (cfg : FlatTMConfig) (v : Nat) (L : List Nat)
    (h_cfg_state : cfg.state_idx = 0)
    (h_cfg_tape : cfg.tapes.map currentTapeSymbol = [some v])
    (h_mem : v ∈ L) :
    (L.map stepLeftEntry).find?
        (fun entry => entryMatchesConfig entry cfg) =
      some (stepLeftEntry v) := by
  induction L with
  | nil => cases h_mem
  | cons w ws ih =>
      show List.find? _ (stepLeftEntry w :: ws.map stepLeftEntry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (stepLeftEntry w) cfg = true := by
          show ((0 : Nat) == cfg.state_idx &&
                  decide (([some w] : List (Option Nat)) =
                    cfg.tapes.map currentTapeSymbol)) = true
          rw [h_cfg_state, h_cfg_tape]; simp
        rw [hMatch]
      · have hNot : entryMatchesConfig (stepLeftEntry w) cfg = false := by
          show ((0 : Nat) == cfg.state_idx &&
                  decide (([some w] : List (Option Nat)) =
                    cfg.tapes.map currentTapeSymbol)) = false
          rw [h_cfg_state, h_cfg_tape]
          have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
            intro h; injection h with h1 _; injection h1 with h2; exact hwv h2
          simp [h_ne']
        rw [hNot]
        rcases List.mem_cons.mp h_mem with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- One unconditional left step on an in-range cell: head `head → head - 1`,
state `0 → 1`. -/
theorem stepLeftTM_step (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length) (h_sym_lt : right.get ⟨head, h_head_lt⟩ < sig) :
    stepFlatTM (stepLeftTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head - 1, right)] } := by
  set v := right.get ⟨head, h_head_lt⟩ with hv
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym0 : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt]
  have hSym : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym0]
  have hNotNone : entryMatchesConfig stepLeftNoneEntry cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([none] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; cases h1
    simp [h_ne']
  have hvInRange : v ∈ List.range sig := List.mem_range.mpr h_sym_lt
  have hFind :
      (((List.range sig).map stepLeftEntry).find?
          (fun entry => entryMatchesConfig entry cfg)) = some (stepLeftEntry v) :=
    find_stepLeft_match cfg v _ rfl hSym hvInRange
  show Option.bind ((stepLeftTM sig).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [stepLeftTM_trans_eq, List.find?_cons, hNotNone, hFind]
  show applyTransitionEntry cfg (stepLeftEntry v) = _
  exact applyEntry_single 0 1 left right head (some v) TMMove.Lmove

/-- `stepLeftTM` run for one step (its full computation). -/
theorem stepLeftTM_run (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length) (h_sym_lt : right.get ⟨head, h_head_lt⟩ < sig) :
    runFlatTM 1 (stepLeftTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head - 1, right)] } := by
  show (if haltingStateReached (stepLeftTM sig)
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM (stepLeftTM sig)
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _
          | some cfg' => runFlatTM 0 (stepLeftTM sig) cfg') = _
  rw [show haltingStateReached (stepLeftTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      stepLeftTM_step sig left right head h_head_lt h_sym_lt]
  rfl

/-- The corrected rewind: step off the trailing terminator, then scan left to the
leading sentinel. -/
def rewindFromEndTM (sig target : Nat) : FlatTM :=
  composeFlatTM (stepLeftTM sig) (scanLeftUntilTM sig target) 1

theorem rewindFromEndTM_sig (sig target : Nat) :
    (rewindFromEndTM sig target).sig = sig := by
  show max (stepLeftTM sig).sig (scanLeftUntilTM sig target).sig = sig
  show max sig sig = sig; omega

theorem rewindFromEndTM_tapes (sig target : Nat) :
    (rewindFromEndTM sig target).tapes = 1 := rfl

theorem rewindFromEndTM_start (sig target : Nat) :
    (rewindFromEndTM sig target).start = 0 := rfl

theorem rewindFromEndTM_valid (sig target : Nat) (h_target : target < sig) :
    validFlatTM (rewindFromEndTM sig target) :=
  composeFlatTM_valid (stepLeftTM sig) (scanLeftUntilTM sig target) 1
    (stepLeftTM_valid sig) (scanLeftUntilTM_valid sig target h_target)
    (show (1 : Nat) < 2 from by decide) rfl rfl

/-- Helper: the seam symbol (cell `head - 1`) is in range, used for the bridge
symbol bound. From `h_cells` (interior cells `< sig`) and `h_target0` (the
sentinel `= target < sig`). -/
private theorem rewind_seam_sym_lt (sig target : Nat) (tp : List Nat) (head : Nat)
    (h_target : target < sig)
    (h0 : 0 < tp.length) (h_target0 : tp.get ⟨0, h0⟩ = target)
    (h_head_pos : 0 < head) (h_head_lt : head < tp.length)
    (h_cells : ∀ i, 0 < i → i < head → ∃ (h : i < tp.length),
        tp.get ⟨i, h⟩ < sig ∧ tp.get ⟨i, h⟩ ≠ target) :
    ∀ v, currentTapeSymbol (([] : List Nat), head - 1, tp) = some v →
      v < max (stepLeftTM sig).sig (scanLeftUntilTM sig target).sig := by
  intro v hv
  have hmax : max (stepLeftTM sig).sig (scanLeftUntilTM sig target).sig = sig := by
    show max sig sig = sig; omega
  rw [hmax]
  have hlt : head - 1 < tp.length := by omega
  rw [currentTapeSymbol_in_range hlt] at hv
  injection hv with hv'
  by_cases hz : head - 1 = 0
  · have he : (⟨head - 1, hlt⟩ : Fin tp.length) = ⟨0, h0⟩ := Fin.ext hz
    rw [he, h_target0] at hv'
    rw [← hv']; exact h_target
  · have hpos : 0 < head - 1 := by omega
    have hlt' : head - 1 < head := by omega
    obtain ⟨h, hsym_lt, _⟩ := h_cells (head - 1) hpos hlt'
    have he : tp.get ⟨head - 1, hlt⟩ = tp.get ⟨head - 1, h⟩ := rfl
    rw [he] at hv'; rw [← hv']; exact hsym_lt

/-- **Rewind-from-end run lemma.** From an interior head `head ≥ 1` on a tape
`tp` whose cell `0` is the `target` sentinel and whose interior cells
`1 … head-1` are in range and `≠ target`, `rewindFromEndTM sig target` halts in
`head + 2` steps in state `3` with the head rewound to `0`, leaving the tape
unchanged. The starting cell `tp[head]` (the trailing terminator) need only be
**in range** — its *value* (it may be the `target`) is irrelevant. -/
theorem rewindFromEndTM_run (sig target : Nat) (h_target : target < sig)
    (left tp : List Nat) (head : Nat)
    (h0 : 0 < tp.length) (h_target0 : tp.get ⟨0, h0⟩ = target)
    (h_head_pos : 0 < head) (h_head_lt : head < tp.length)
    (h_start_lt : tp.get ⟨head, h_head_lt⟩ < sig)
    (h_cells : ∀ i, 0 < i → i < head → ∃ (h : i < tp.length),
        tp.get ⟨i, h⟩ < sig ∧ tp.get ⟨i, h⟩ ≠ target) :
    runFlatTM (1 + 1 + head) (rewindFromEndTM sig target)
        { state_idx := 0, tapes := [(left, head, tp)] } =
      some { state_idx := 3, tapes := [(left, 0, tp)] } := by
  -- M₁ (stepLeftTM) run: one left step off the start cell.
  have h_run1 : runFlatTM 1 (stepLeftTM sig)
      { state_idx := 0, tapes := [(left, head, tp)] }
        = some { state_idx := 1, tapes := [(left, head - 1, tp)] } :=
    stepLeftTM_run sig left tp head h_head_lt h_start_lt
  -- M₁ trajectory: one step only, start state `0 ≠ exit = 1`, non-halting.
  have h_traj1 : ∀ k, k < 1 → ∀ ck,
      runFlatTM k (stepLeftTM sig)
          { state_idx := 0, tapes := [(left, head, tp)] } = some ck →
      ck.state_idx ≠ 1 ∧ haltingStateReached (stepLeftTM sig) ck = false := by
    intro k hk ck hck
    interval_cases k
    · obtain rfl : ck = { state_idx := 0, tapes := [(left, head, tp)] } :=
        (Option.some.inj hck).symm
      exact ⟨Nat.zero_ne_one, rfl⟩
  -- M₂ (scanLeftUntilTM) run: scan left from head-1 to the sentinel at 0.
  have h_head1_lt : head - 1 < tp.length := by omega
  have hb : ∀ i, 0 < i → i ≤ head - 1 → ∃ (h : i < tp.length),
      tp.get ⟨i, h⟩ < sig ∧ tp.get ⟨i, h⟩ ≠ target :=
    fun i hi hile => h_cells i hi (by omega)
  have h_run2 : runFlatTM ((head - 1) + 1) (scanLeftUntilTM sig target)
      { state_idx := 0, tapes := [(left, head - 1, tp)] }
        = some { state_idx := 1, tapes := [(left, 0, tp)] } :=
    scanLeft_run sig target left tp h0 h_target0 (head - 1) h_head1_lt hb
  have h_run2' : runFlatTM head (scanLeftUntilTM sig target)
      { state_idx := (scanLeftUntilTM sig target).start, tapes := [(left, head - 1, tp)] }
        = some { state_idx := 1, tapes := [(left, 0, tp)] } := by
    rw [show (scanLeftUntilTM sig target).start = 0 from rfl,
        show head = (head - 1) + 1 from by omega]
    exact h_run2
  have h_halt2 : haltingStateReached (scanLeftUntilTM sig target)
      { state_idx := 1, tapes := [(left, 0, tp)] } = true := rfl
  have h_sym_bound := rewind_seam_sym_lt sig target tp head h_target h0 h_target0
    h_head_pos h_head_lt h_cells
  have hcomp := composeFlatTM_run
    (stepLeftTM_valid sig) (scanLeftUntilTM_valid sig target h_target)
    (show (1 : Nat) < 2 from by decide)
    { state_idx := 0, tapes := [(left, head, tp)] }
    (show (0 : Nat) < 2 from by decide)
    left (head - 1) tp h_sym_bound h_run1 h_traj1 h_run2' h_halt2
  -- The composite halts at state `1 + 2 = 3` with head `0`.
  have : runFlatTM (1 + 1 + head) (rewindFromEndTM sig target)
      { state_idx := 0, tapes := [(left, head, tp)] }
        = some { state_idx := 1 + (stepLeftTM sig).states, tapes := [(left, 0, tp)] } :=
    hcomp.1
  rw [this]; rfl

/-- **Rewind-from-end trajectory.** Before completing (`k < head + 2`),
`rewindFromEndTM` has not yet reached a halting state. The `h_traj1`/`h_traj2`
shape needed when bracketing a gadget with the rewind. -/
theorem rewindFromEndTM_no_early_halt (sig target : Nat) (h_target : target < sig)
    (left tp : List Nat) (head : Nat)
    (h0 : 0 < tp.length) (h_target0 : tp.get ⟨0, h0⟩ = target)
    (h_head_pos : 0 < head) (h_head_lt : head < tp.length)
    (h_start_lt : tp.get ⟨head, h_head_lt⟩ < sig)
    (h_cells : ∀ i, 0 < i → i < head → ∃ (h : i < tp.length),
        tp.get ⟨i, h⟩ < sig ∧ tp.get ⟨i, h⟩ ≠ target) :
    ∀ k, k < 1 + 1 + head → ∀ ck,
      runFlatTM k (rewindFromEndTM sig target)
          { state_idx := 0, tapes := [(left, head, tp)] } = some ck →
      haltingStateReached (rewindFromEndTM sig target) ck = false := by
  have h_run1 : runFlatTM 1 (stepLeftTM sig)
      { state_idx := 0, tapes := [(left, head, tp)] }
        = some { state_idx := 1, tapes := [(left, head - 1, tp)] } :=
    stepLeftTM_run sig left tp head h_head_lt h_start_lt
  have h_traj1 : ∀ k, k < 1 → ∀ ck,
      runFlatTM k (stepLeftTM sig)
          { state_idx := 0, tapes := [(left, head, tp)] } = some ck →
      ck.state_idx ≠ 1 ∧ haltingStateReached (stepLeftTM sig) ck = false := by
    intro k hk ck hck
    interval_cases k
    · obtain rfl : ck = { state_idx := 0, tapes := [(left, head, tp)] } :=
        (Option.some.inj hck).symm
      exact ⟨Nat.zero_ne_one, rfl⟩
  have h_head1_lt : head - 1 < tp.length := by omega
  have hb : ∀ i, 0 < i → i ≤ head - 1 → ∃ (h : i < tp.length),
      tp.get ⟨i, h⟩ < sig ∧ tp.get ⟨i, h⟩ ≠ target :=
    fun i hi hile => h_cells i hi (by omega)
  have h_traj2 : ∀ k, k < head → ∀ ck,
      runFlatTM k (scanLeftUntilTM sig target)
          { state_idx := (scanLeftUntilTM sig target).start,
            tapes := [(left, head - 1, tp)] } = some ck →
      haltingStateReached (scanLeftUntilTM sig target) ck = false := by
    intro k hk ck hck
    rw [show (scanLeftUntilTM sig target).start = 0 from rfl] at hck
    have hk' : k < (head - 1) + 1 := by omega
    exact (scanLeft_no_early_halt sig target left tp (head - 1) h_head1_lt hb k hk' ck hck).2
  have h_sym_bound := rewind_seam_sym_lt sig target tp head h_target h0 h_target0
    h_head_pos h_head_lt h_cells
  exact composeFlatTM_no_early_halt
    (stepLeftTM_valid sig) (scanLeftUntilTM_valid sig target h_target)
    (show (1 : Nat) < 2 from by decide)
    { state_idx := 0, tapes := [(left, head, tp)] }
    (show (0 : Nat) < 2 from by decide)
    left (head - 1) tp h_sym_bound h_run1 h_traj1 h_traj2

/-! ### Scan left to an *interior* mark — the residue-tolerant rewind primitive
(Risk C2, two-phase rewind)

`scanLeft_run` lands on the `target` at index `0`. Under the residue-tolerant
physical contract the tape is
`sentinel(3) :: interior(3-free) ++ [terminator(3)] ++ residue(3-free)`, and a
gadget exits with its head in the residue (or on the terminator). The first `3`
to the *left* is the **real terminator** at an interior position `p`, not the
sentinel at `0`. `scanLeftToMark_run` lands on that interior `p` in `head − p`
steps (`+1` for the accept step), reading only the `target`-free cells
`p+1 … head` on the way. Composing it with `rewindFromEndTM` (step off the
terminator, then scan to the sentinel) yields the full two-phase rewind. -/

/-- **Scan-left-to-interior-mark run lemma.** From head `head = p + n`, scanning
left over the `target`-free in-range cells `p+1 … head`, `scanLeftUntilTM` halts
in `n + 1` steps in the accept state `1` with the head on the mark at `p`
(`right[p] = target`), leaving the tape unchanged. Generalises `scanLeft_run`
(the `p = 0` case). -/
theorem scanLeftToMark_run (sig target : Nat) (left right : List Nat) (p : Nat)
    (hp : p < right.length) (h_target_p : right.get ⟨p, hp⟩ = target) :
    ∀ (n head : Nat), head = p + n → head < right.length →
      (∀ i, p < i → i ≤ head → ∃ (h : i < right.length),
        right.get ⟨i, h⟩ < sig ∧ right.get ⟨i, h⟩ ≠ target) →
      runFlatTM (n + 1) (scanLeftUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 1, tapes := [(left, p, right)] } := by
  intro n
  induction n with
  | zero =>
      intro head hhead h_head_lt _
      have hhp : head = p := by omega
      subst hhp
      have h_get : right.get ⟨head, h_head_lt⟩ = target := h_target_p
      rw [run0_unfold sig target 0 _ _
        (scanLeftUntilTM_step_found sig target left right head h_head_lt h_get)]
      rfl
  | succ m ih =>
      intro head hhead h_head_lt hb
      have h_head_gt : p < head := by omega
      rcases hb head h_head_gt (Nat.le_refl _) with ⟨h_lt, h_sym_lt, h_sym_ne⟩
      have heq : (⟨head, h_head_lt⟩ : Fin right.length) = ⟨head, h_lt⟩ := rfl
      have h_get_lt : right.get ⟨head, h_head_lt⟩ < sig := by rw [heq]; exact h_sym_lt
      have h_get_ne : right.get ⟨head, h_head_lt⟩ ≠ target := by rw [heq]; exact h_sym_ne
      have h_head_lt' : head - 1 < right.length := by omega
      have hhead' : head - 1 = p + m := by omega
      have hb' : ∀ i, p < i → i ≤ head - 1 → ∃ (h : i < right.length),
          right.get ⟨i, h⟩ < sig ∧ right.get ⟨i, h⟩ ≠ target :=
        fun i hi hle => hb i hi (by omega)
      have hih := ih (head - 1) hhead' h_head_lt' hb'
      rw [run0_unfold sig target (m + 1) _ _
        (scanLeftUntilTM_step_advance sig target left right head h_head_lt
          h_get_lt h_get_ne)]
      exact hih

/-- **Scan-left-to-interior-mark trajectory.** For `k < n + 1` the scan is still
in state `0` (head at `head − k ≥ p`), so it has neither accepted nor halted.
The `h_traj1` shape of `composeFlatTM_run`. Generalises `scanLeft_no_early_halt`.
-/
theorem scanLeftToMark_no_early_halt (sig target : Nat) (left right : List Nat) (p : Nat)
    (hp : p < right.length) (h_target_p : right.get ⟨p, hp⟩ = target)
    (n head : Nat) (hhead : head = p + n) (h_head_lt : head < right.length)
    (hb : ∀ i, p < i → i ≤ head → ∃ (h : i < right.length),
      right.get ⟨i, h⟩ < sig ∧ right.get ⟨i, h⟩ ≠ target) :
    ∀ k, k < n + 1 → ∀ ck,
      runFlatTM k (scanLeftUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ 1 ∧
      haltingStateReached (scanLeftUntilTM sig target) ck = false := by
  intro k hk ck hck
  have hk' : k ≤ n := Nat.lt_succ_iff.mp hk
  have htraj : ∀ (m : Nat), m ≤ n →
      runFlatTM m (scanLeftUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 0, tapes := [(left, head - m, right)] } := by
    intro m
    induction m with
    | zero => intro _; rw [Nat.sub_zero]; rfl
    | succ j ih =>
        intro hj
        have hj' : j ≤ n := Nat.le_of_succ_le hj
        have ihj := ih hj'
        have h_pos : p < head - j := by omega
        have h_idx_lt : head - j < right.length := by omega
        have h_idx_le : head - j ≤ head := Nat.sub_le head j
        rcases hb (head - j) h_pos h_idx_le with ⟨h_lt, h_sym_lt, h_sym_ne⟩
        have heq : (⟨head - j, h_idx_lt⟩ : Fin right.length) = ⟨head - j, h_lt⟩ := rfl
        have h_step := scanLeftUntilTM_step_advance sig target left right (head - j)
          h_idx_lt (by rw [heq]; exact h_sym_lt) (by rw [heq]; exact h_sym_ne)
        have h_nothalt :
            haltingStateReached (scanLeftUntilTM sig target)
              { state_idx := 0, tapes := [(left, head - j, right)] } = false := rfl
        have h := runFlatTM_extend_by_step (scanLeftUntilTM sig target) j _ _ _
          ihj h_nothalt h_step
        rw [show head - (j + 1) = head - j - 1 from by omega]
        exact h
  rw [htraj k hk'] at hck
  obtain rfl : ck = { state_idx := 0, tapes := [(left, head - k, right)] } :=
    (Option.some.inj hck).symm
  exact ⟨Nat.zero_ne_one, rfl⟩

/-! ### The two-phase rewind (`rewindTwoPhaseTM`) — Risk C2 residue-tolerant rewind

`rewindFromEndTM` rewinds to the leading sentinel *only when the head sits on the
trailing terminator* (no residue): it steps off one cell, then the leftward scan
runs through the terminator-free interior to the sentinel. Under the residue-
tolerant contract the head exits in the **residue** (or on the terminator), with
the real terminator at an interior position; a single `rewindFromEndTM` would
stop the inner scan on the real terminator, not the sentinel.

`rewindTwoPhaseTM = scanLeftUntilTM ⨾ rewindFromEndTM`:
* **phase 1** (`scanLeftToMark`): scan left through the terminator-free residue to
  the **real terminator** at position `p`;
* **phase 2** (`rewindFromEndTM`): step off the terminator, scan left through the
  terminator-free interior to the **leading sentinel** at `0`.

Both targets are `target = endMark = 3`; they are distinguished purely by the
terminator-free residue/interior between them. The composite halts at state `6`
with the head rewound to `0`. -/

/-- The two-phase rewind machine. -/
def rewindTwoPhaseTM (sig target : Nat) : FlatTM :=
  composeFlatTM (scanLeftUntilTM sig target) (rewindFromEndTM sig target) 1

theorem rewindTwoPhaseTM_valid (sig target : Nat) (h_target : target < sig) :
    validFlatTM (rewindTwoPhaseTM sig target) :=
  composeFlatTM_valid _ _ 1
    (scanLeftUntilTM_valid sig target h_target)
    (rewindFromEndTM_valid sig target h_target)
    (show (1 : Nat) < 3 from by decide) rfl (rewindFromEndTM_tapes sig target)

theorem rewindTwoPhaseTM_start (sig target : Nat) :
    (rewindTwoPhaseTM sig target).start = 0 := rfl

theorem rewindTwoPhaseTM_tapes (sig target : Nat) :
    (rewindTwoPhaseTM sig target).tapes = 1 := rfl

theorem rewindTwoPhaseTM_sig (sig target : Nat) :
    (rewindTwoPhaseTM sig target).sig = sig := by
  show max (scanLeftUntilTM sig target).sig (rewindFromEndTM sig target).sig = sig
  rw [rewindFromEndTM_sig]; exact Nat.max_self sig

/-! ### Halt-state characterization of the rewind machines

The two-phase rewind ends in a left scan (`scanLeftUntilTM`), whose halt vector
`[false, true, true]` has *two* halt states (1 = "found target", 2 = "hit the
left boundary without finding"). Through `composeFlatTM` (which zeroes the first
machine's halts) the composite keeps both, shifted. These lemmas pin the exact
two halt states of `rewindTwoPhaseTM sig target` so a caller can demote the
unreachable boundary one with `Compile.joinTwoHalts` and recover a unique halt.
-/

/-- A halt state of `composeFlatTM M₁ M₂ exit` lives in the `M₂` segment: it is
`M₁.states + j` for some halt state `j` of `M₂`. -/
theorem composeFlatTM_halt_some_imp (M₁ M₂ : FlatTM) (exit i : Nat)
    (hi : (composeFlatTM M₁ M₂ exit).halt[i]? = some true) :
    M₁.states ≤ i ∧ M₂.halt[i - M₁.states]? = some true := by
  change (composedHalt M₁ M₂)[i]? = some true at hi
  unfold composedHalt at hi
  by_cases hlt : i < M₁.states
  · exfalso
    rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hlt),
        List.getElem?_replicate] at hi
    simp [hlt] at hi
  · rw [Nat.not_lt] at hlt
    rw [List.getElem?_append_right (by rw [List.length_replicate]; exact hlt),
        List.length_replicate] at hi
    exact ⟨hlt, hi⟩

/-- The converse: a halt state `j` of `M₂` shifts to halt state `M₁.states + j`
of `composeFlatTM M₁ M₂ exit`. -/
theorem composeFlatTM_halt_some_intro (M₁ M₂ : FlatTM) (exit j : Nat)
    (hj : M₂.halt[j]? = some true) :
    (composeFlatTM M₁ M₂ exit).halt[M₁.states + j]? = some true := by
  change (composedHalt M₁ M₂)[M₁.states + j]? = some true
  unfold composedHalt
  rw [List.getElem?_append_right (by rw [List.length_replicate]; exact Nat.le_add_right _ _),
      List.length_replicate, Nat.add_sub_cancel_left]
  exact hj

theorem scanLeftUntilTM_halt_only (sig target i : Nat)
    (hi : (scanLeftUntilTM sig target).halt[i]? = some true) : i = 1 ∨ i = 2 := by
  change ([false, true, true] : List Bool)[i]? = some true at hi
  rcases i with _ | _ | _ | i <;> simp_all

theorem rewindFromEndTM_halt_only (sig target i : Nat)
    (hi : (rewindFromEndTM sig target).halt[i]? = some true) : i = 3 ∨ i = 4 := by
  obtain ⟨hge, hj⟩ :=
    composeFlatTM_halt_some_imp (stepLeftTM sig) (scanLeftUntilTM sig target) 1 i hi
  have hst : (stepLeftTM sig).states = 2 := rfl
  rw [hst] at hge hj
  rcases scanLeftUntilTM_halt_only sig target _ hj with h | h <;> omega

theorem rewindTwoPhaseTM_halt_only (sig target i : Nat)
    (hi : (rewindTwoPhaseTM sig target).halt[i]? = some true) : i = 6 ∨ i = 7 := by
  obtain ⟨hge, hj⟩ :=
    composeFlatTM_halt_some_imp (scanLeftUntilTM sig target) (rewindFromEndTM sig target) 1 i hi
  have hst : (scanLeftUntilTM sig target).states = 3 := rfl
  rw [hst] at hge hj
  rcases rewindFromEndTM_halt_only sig target _ hj with h | h <;> omega

/-- The surviving exit (the "found" halt) of `rewindTwoPhaseTM sig target` is
state `6`. -/
theorem rewindTwoPhaseTM_halt_six (sig target : Nat) :
    (rewindTwoPhaseTM sig target).halt[6]? = some true := by
  have h1 : (scanLeftUntilTM sig target).halt[1]? = some true := rfl
  have h3 : (rewindFromEndTM sig target).halt[3]? = some true :=
    composeFlatTM_halt_some_intro (stepLeftTM sig) (scanLeftUntilTM sig target) 1 1 h1
  exact composeFlatTM_halt_some_intro (scanLeftUntilTM sig target) (rewindFromEndTM sig target) 1 3 h3

/-- **Two-phase rewind run lemma.** On a tape `tp` with the leading sentinel
`target` at `0`, the real terminator `target` at an interior `p > 0`, a
terminator-free in-range interior `1 … p-1`, and a terminator-free in-range
residue `p+1 … head` (head `≥ p`, e.g. the head a gadget leaves in the residue),
`rewindTwoPhaseTM` halts at state `6` with the head rewound to `0`, leaving the
tape unchanged. -/
theorem rewindTwoPhase_run (sig target : Nat) (h_target : target < sig)
    (left tp : List Nat) (p head : Nat)
    (h0 : 0 < tp.length) (h_sentinel : tp.get ⟨0, h0⟩ = target)
    (hp : p < tp.length) (h_term : tp.get ⟨p, hp⟩ = target) (h_p_pos : 0 < p)
    (h_head_lt : head < tp.length) (h_p_le_head : p ≤ head)
    (h_interior : ∀ i, 0 < i → i < p → ∃ (h : i < tp.length),
        tp.get ⟨i, h⟩ < sig ∧ tp.get ⟨i, h⟩ ≠ target)
    (h_residue : ∀ i, p < i → i ≤ head → ∃ (h : i < tp.length),
        tp.get ⟨i, h⟩ < sig ∧ tp.get ⟨i, h⟩ ≠ target) :
    runFlatTM ((head - p + 1) + 1 + (1 + 1 + p)) (rewindTwoPhaseTM sig target)
        { state_idx := 0, tapes := [(left, head, tp)] } =
      some { state_idx := 6, tapes := [(left, 0, tp)] } := by
  have hhead : head = p + (head - p) := by omega
  have h_run1 := scanLeftToMark_run sig target left tp p hp h_term (head - p) head hhead
    h_head_lt h_residue
  have h_traj1 := scanLeftToMark_no_early_halt sig target left tp p hp h_term (head - p) head
    hhead h_head_lt h_residue
  have h_start_sym : tp.get ⟨p, hp⟩ < sig := by rw [h_term]; exact h_target
  have h_run2 : runFlatTM (1 + 1 + p) (rewindFromEndTM sig target)
      { state_idx := (rewindFromEndTM sig target).start, tapes := [(left, p, tp)] }
        = some { state_idx := 3, tapes := [(left, 0, tp)] } := by
    rw [rewindFromEndTM_start]
    exact rewindFromEndTM_run sig target h_target left tp p h0 h_sentinel h_p_pos hp
      h_start_sym h_interior
  have h_halt2 : haltingStateReached (rewindFromEndTM sig target)
      { state_idx := 3, tapes := [(left, 0, tp)] } = true := rfl
  have h_sym_bound : ∀ v, currentTapeSymbol (left, p, tp) = some v →
      v < max (scanLeftUntilTM sig target).sig (rewindFromEndTM sig target).sig := by
    intro v hv
    rw [currentTapeSymbol_in_range hp, h_term] at hv
    injection hv with hv'
    have hmax : max (scanLeftUntilTM sig target).sig (rewindFromEndTM sig target).sig = sig := by
      rw [rewindFromEndTM_sig]; exact Nat.max_self sig
    rw [hmax, ← hv']; exact h_target
  have hcomp := composeFlatTM_run
    (scanLeftUntilTM_valid sig target h_target) (rewindFromEndTM_valid sig target h_target)
    (by decide : (1 : Nat) < 3)
    { state_idx := 0, tapes := [(left, head, tp)] }
    (by decide : (0 : Nat) < 3)
    left p tp h_sym_bound h_run1 h_traj1 h_run2 h_halt2
  exact hcomp.1

/-- **Two-phase rewind trajectory.** Before completing, `rewindTwoPhaseTM` has not
reached a halting state — the `h_traj` input for bracketing a gadget with it. -/
theorem rewindTwoPhase_no_early_halt (sig target : Nat) (h_target : target < sig)
    (left tp : List Nat) (p head : Nat)
    (h0 : 0 < tp.length) (h_sentinel : tp.get ⟨0, h0⟩ = target)
    (hp : p < tp.length) (h_term : tp.get ⟨p, hp⟩ = target) (h_p_pos : 0 < p)
    (h_head_lt : head < tp.length) (h_p_le_head : p ≤ head)
    (h_interior : ∀ i, 0 < i → i < p → ∃ (h : i < tp.length),
        tp.get ⟨i, h⟩ < sig ∧ tp.get ⟨i, h⟩ ≠ target)
    (h_residue : ∀ i, p < i → i ≤ head → ∃ (h : i < tp.length),
        tp.get ⟨i, h⟩ < sig ∧ tp.get ⟨i, h⟩ ≠ target) :
    ∀ k, k < (head - p + 1) + 1 + (1 + 1 + p) → ∀ ck,
      runFlatTM k (rewindTwoPhaseTM sig target)
          { state_idx := 0, tapes := [(left, head, tp)] } = some ck →
      haltingStateReached (rewindTwoPhaseTM sig target) ck = false := by
  have hhead : head = p + (head - p) := by omega
  have h_run1 := scanLeftToMark_run sig target left tp p hp h_term (head - p) head hhead
    h_head_lt h_residue
  have h_traj1 := scanLeftToMark_no_early_halt sig target left tp p hp h_term (head - p) head
    hhead h_head_lt h_residue
  have h_start_sym : tp.get ⟨p, hp⟩ < sig := by rw [h_term]; exact h_target
  have h_traj2 : ∀ k, k < 1 + 1 + p → ∀ ck,
      runFlatTM k (rewindFromEndTM sig target)
          { state_idx := (rewindFromEndTM sig target).start, tapes := [(left, p, tp)] }
        = some ck → haltingStateReached (rewindFromEndTM sig target) ck = false := by
    intro k hk ck hck
    rw [rewindFromEndTM_start] at hck
    exact rewindFromEndTM_no_early_halt sig target h_target left tp p h0 h_sentinel h_p_pos hp
      h_start_sym h_interior k hk ck hck
  have h_sym_bound : ∀ v, currentTapeSymbol (left, p, tp) = some v →
      v < max (scanLeftUntilTM sig target).sig (rewindFromEndTM sig target).sig := by
    intro v hv
    rw [currentTapeSymbol_in_range hp, h_term] at hv
    injection hv with hv'
    have hmax : max (scanLeftUntilTM sig target).sig (rewindFromEndTM sig target).sig = sig := by
      rw [rewindFromEndTM_sig]; exact Nat.max_self sig
    rw [hmax, ← hv']; exact h_target
  exact composeFlatTM_no_early_halt
    (scanLeftUntilTM_valid sig target h_target) (rewindFromEndTM_valid sig target h_target)
    (by decide : (1 : Nat) < 3)
    { state_idx := 0, tapes := [(left, head, tp)] }
    (by decide : (0 : Nat) < 3)
    left p tp h_sym_bound h_run1 h_traj1 h_traj2

end Complexity.Lang.ScanLeft
