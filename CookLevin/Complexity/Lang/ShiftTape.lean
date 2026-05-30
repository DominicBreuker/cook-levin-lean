import Complexity.Complexity.TMPrimitives

set_option autoImplicit false

/-! # `insertCarryTM` — the shared single-tape "insert one symbol" gadget
(Risk C1 of `ROADMAP.md`)

Every `Lang` primitive `Op` writes a register whose length changes, so
each needs a single-tape shift loop. This file builds the reusable
*insert* loop (used by `appendOne` / `appendZero`, and the building
block for the overwrite ops): starting with the head at a position `p`,
insert symbol `ins` at `p`, carrying every cell from `p` rightward one
place to the right (the displaced symbol is held in the machine state).

The alphabet is fixed at `sig = 4` to match the encoding (`0` =
delimiter, `1`/`2` = shifted bits, `3` = end-of-tape terminator). The
gadget must carry *all four* symbols, since inserting before a register's
delimiter shifts the rest of the tape — including the terminator —
right by one. States:

- `0` : start (about to insert at the head),
- `1`, `2`, `3`, `4` : carry state holding value `0`, `1`, `2`, `3`,
- `5` : halt.

The single-step behaviour: in any state, read the current cell `y`,
write the value this state owes (`ins` from start, or the carried value
from a carry state), move right, and switch to the carry state for `y`.
At a blank cell, write the owed value (appending) and halt.

The headline result is `insertCarryTM_run`: from the start state with
the head at `pre.length` on tape `pre ++ suf`, after `suf.length + 1`
steps the machine halts with tape `pre ++ ins :: suf`. -/

namespace Complexity.Lang.ShiftTape

open TMPrimitives

/-- Build a single-tape transition entry. -/
private def mkE (s : Nat) (sym : Option Nat) (d : Nat) (w : Option Nat)
    (mv : TMMove) : FlatTMTransEntry :=
  { src_state := s, src_tape_vals := [sym], dst_state := d,
    dst_write_vals := [w], move_dirs := [mv] }

/-- Transition table for the insert-carry machine inserting `ins`. -/
def insertCarryTrans (ins : Nat) : List FlatTMTransEntry :=
  [ -- start (state 0): write `ins`, move right, carry the read symbol
    mkE 0 (some 0) 1 (some ins) .Rmove,
    mkE 0 (some 1) 2 (some ins) .Rmove,
    mkE 0 (some 2) 3 (some ins) .Rmove,
    mkE 0 (some 3) 4 (some ins) .Rmove,
    mkE 0 none      5 (some ins) .Nmove,
    -- carry 0 (state 1): write 0, move right, carry the read symbol
    mkE 1 (some 0) 1 (some 0) .Rmove,
    mkE 1 (some 1) 2 (some 0) .Rmove,
    mkE 1 (some 2) 3 (some 0) .Rmove,
    mkE 1 (some 3) 4 (some 0) .Rmove,
    mkE 1 none      5 (some 0) .Nmove,
    -- carry 1 (state 2)
    mkE 2 (some 0) 1 (some 1) .Rmove,
    mkE 2 (some 1) 2 (some 1) .Rmove,
    mkE 2 (some 2) 3 (some 1) .Rmove,
    mkE 2 (some 3) 4 (some 1) .Rmove,
    mkE 2 none      5 (some 1) .Nmove,
    -- carry 2 (state 3)
    mkE 3 (some 0) 1 (some 2) .Rmove,
    mkE 3 (some 1) 2 (some 2) .Rmove,
    mkE 3 (some 2) 3 (some 2) .Rmove,
    mkE 3 (some 3) 4 (some 2) .Rmove,
    mkE 3 none      5 (some 2) .Nmove,
    -- carry 3 (state 4)
    mkE 4 (some 0) 1 (some 3) .Rmove,
    mkE 4 (some 1) 2 (some 3) .Rmove,
    mkE 4 (some 2) 3 (some 3) .Rmove,
    mkE 4 (some 3) 4 (some 3) .Rmove,
    mkE 4 none      5 (some 3) .Nmove ]

/-- The insert-carry machine inserting symbol `ins` (sig = 4). -/
def insertCarryTM (ins : Nat) : FlatTM where
  sig := 4
  tapes := 1
  states := 6
  trans := insertCarryTrans ins
  start := 0
  halt := [false, false, false, false, false, true]

private theorem optBounded_some {k sig : Nat} (h : k < sig) :
    flatTMOptionSymbolsBounded sig [some k] := by
  intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact h

private theorem optBounded_none {sig : Nat} :
    flatTMOptionSymbolsBounded sig [none] := by
  intro x hx; simp only [List.mem_singleton] at hx; subst hx; trivial

theorem insertCarryTM_valid (ins : Nat) (h_ins : ins < 4) :
    validFlatTM (insertCarryTM ins) := by
  refine ⟨?_, ?_, ?_⟩
  · show (0 : Nat) < 6; decide
  · show ([false, false, false, false, false, true] : List Bool).length = 6; decide
  · intro e he
    simp only [insertCarryTM, insertCarryTrans, mkE, List.mem_cons, List.not_mem_nil,
      or_false] at he
    rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
      subst h <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [insertCarryTM] <;>
      first
      | rfl
      | decide
      | exact optBounded_none
      | (apply optBounded_some; omega)

/-- Value written by state `s`: `ins` from the start state, otherwise
the carried value `s - 1`. -/
private def owed (ins s : Nat) : Nat := if s = 0 then ins else s - 1

set_option maxHeartbeats 1600000 in
/-- One step on an in-range cell: write the owed value, move right, and
switch to the carry state for the symbol just read. -/
theorem insertCarryTM_step_nonblank (ins s y : Nat) (hs : s < 5) (hy : y < 4)
    (left right : List Nat) (head : Nat) (hlt : head < right.length)
    (hget : right.get ⟨head, hlt⟩ = y) :
    stepFlatTM (insertCarryTM ins)
        { state_idx := s, tapes := [(left, head, right)] }
      = some { state_idx := 1 + y,
               tapes := [(left, head + 1,
                          right.take head ++ owed ins s :: right.drop (head + 1))] } := by
  have hsym : currentTapeSymbol (left, head, right) = some y := by
    rw [currentTapeSymbol_in_range hlt, hget]
  interval_cases s <;> interval_cases y <;>
    simp_all [owed, stepFlatTM, insertCarryTM, insertCarryTrans, mkE, entryMatchesConfig,
      applyTransitionEntry, tapeStep, writeCurrentTapeSymbol, moveTapeHead]

/-- One step on a blank cell: write the owed value (appending) and halt. -/
theorem insertCarryTM_step_blank (ins s : Nat) (hs : s < 5)
    (left right : List Nat) (head : Nat) (hge : ¬ head < right.length) :
    stepFlatTM (insertCarryTM ins)
        { state_idx := s, tapes := [(left, head, right)] }
      = some { state_idx := 5,
               tapes := [(left, head,
                          right ++ List.replicate (head - right.length) 0 ++ [owed ins s])] } := by
  have hsym : currentTapeSymbol (left, head, right) = none :=
    currentTapeSymbol_out_of_range hge
  interval_cases s <;>
    simp_all [owed, stepFlatTM, insertCarryTM, insertCarryTrans, mkE, entryMatchesConfig,
      applyTransitionEntry, tapeStep, writeCurrentTapeSymbol, moveTapeHead]

/-- Unfold one non-halting step of a run. -/
private theorem run_succ_of_step (M : FlatTM) (cfg c' : FlatTMConfig) (n : Nat)
    (hnh : haltingStateReached M cfg = false) (hstep : stepFlatTM M cfg = some c') :
    runFlatTM (n + 1) M cfg = runFlatTM n M c' := by
  show (if haltingStateReached M cfg = true then some cfg
        else match stepFlatTM M cfg with
          | none => some cfg
          | some c => runFlatTM n M c) = runFlatTM n M c'
  rw [if_neg (by rw [hnh]; decide), hstep]

/-- Non-halt states `0..4` of the insert-carry machine. -/
private theorem not_halt_lt5 (ins s : Nat) (hs : s < 5) (cfg : FlatTMConfig)
    (hcfg : cfg.state_idx = s) :
    haltingStateReached (insertCarryTM ins) cfg = false := by
  show (insertCarryTM ins).halt.getD cfg.state_idx false = false
  rw [hcfg]; simp only [insertCarryTM]; interval_cases s <;> rfl

/-- **Carry phase.** Starting in carry state `1 + v` with the head at
`pre.length` on tape `pre ++ suf`, after `suf.length + 1` steps the
machine halts with the carried value `v` written at the head and `suf`
shifted one place right: tape `pre ++ v :: suf`. -/
theorem insertCarryTM_carry_run (ins : Nat) (suf : List Nat) :
    ∀ (pre : List Nat) (v : Nat), v < 4 → (∀ x ∈ suf, x < 4) →
      runFlatTM (suf.length + 1) (insertCarryTM ins)
        { state_idx := 1 + v, tapes := [([], pre.length, pre ++ suf)] }
      = some { state_idx := 5,
               tapes := [([], pre.length + suf.length, pre ++ v :: suf)] } := by
  induction suf with
  | nil =>
    intro pre v hv _
    have hge : ¬ pre.length < (pre ++ ([] : List Nat)).length := by simp
    rw [List.length_nil,
        run_succ_of_step _ _ _ 0
          (not_halt_lt5 ins (1 + v) (by omega) _ rfl)
          (insertCarryTM_step_blank ins (1 + v) (by omega) [] (pre ++ []) pre.length hge)]
    simp [runFlatTM, owed]
  | cons y suf' ih =>
    intro pre v hv hall
    have hy : y < 4 := hall y (by simp)
    have hall' : ∀ x ∈ suf', x < 4 := fun x hx => hall x (by simp [hx])
    have hlt : pre.length < (pre ++ y :: suf').length := by simp
    have hget : (pre ++ y :: suf').get ⟨pre.length, hlt⟩ = y := by
      simp [List.getElem_append_right]
    have ho : owed ins (1 + v) = v := by simp [owed]
    have hd : (pre ++ y :: suf').drop (pre.length + 1) = suf' := by
      rw [show pre.length + 1 = (pre ++ [y]).length by simp,
          show pre ++ y :: suf' = (pre ++ [y]) ++ suf' by simp, List.drop_left]
    have hstep := insertCarryTM_step_nonblank ins (1 + v) y (by omega) hy []
      (pre ++ y :: suf') pre.length hlt hget
    rw [ho, List.take_left, hd] at hstep
    -- hstep : step ... = some { 1 + y, [([], pre.length + 1, pre ++ v :: suf')] }
    rw [show (y :: suf').length + 1 = (suf'.length + 1) + 1 by simp,
        run_succ_of_step _ _ _ (suf'.length + 1)
          (not_halt_lt5 ins (1 + v) (by omega) _ rfl) hstep]
    rw [show pre.length + 1 = (pre ++ [v]).length by simp,
        show pre ++ v :: suf' = (pre ++ [v]) ++ suf' by simp,
        ih (pre ++ [v]) y hy hall']
    have hlen : (pre ++ [v]).length + suf'.length = pre.length + (y :: suf').length := by
      simp; omega
    rw [hlen, show (pre ++ [v]) ++ y :: suf' = pre ++ v :: y :: suf' by simp]

/-- **The shared "insert one symbol" run lemma (Risk C1).** Starting in
the start state with the head at `pre.length` on tape `pre ++ suf`,
after `suf.length + 1` steps the machine halts with `ins` inserted at
the head: tape `pre ++ ins :: suf`. The head ends at `pre.length +
suf.length`. This is the reusable gadget every length-changing `Op`
builds on (`appendOne` / `appendZero` directly; overwrite ops via an
insert after a delete). -/
theorem insertCarryTM_run (ins : Nat) (suf pre : List Nat)
    (hall : ∀ x ∈ suf, x < 4) :
    runFlatTM (suf.length + 1) (insertCarryTM ins)
        { state_idx := 0, tapes := [([], pre.length, pre ++ suf)] }
      = some { state_idx := 5,
               tapes := [([], pre.length + suf.length, pre ++ ins :: suf)] } := by
  cases suf with
  | nil =>
    have hge : ¬ pre.length < (pre ++ ([] : List Nat)).length := by simp
    rw [List.length_nil,
        run_succ_of_step _ _ _ 0 (not_halt_lt5 ins 0 (by omega) _ rfl)
          (insertCarryTM_step_blank ins 0 (by omega) [] (pre ++ []) pre.length hge)]
    simp [runFlatTM, owed]
  | cons y suf' =>
    have hy : y < 4 := hall y (by simp)
    have hall' : ∀ x ∈ suf', x < 4 := fun x hx => hall x (by simp [hx])
    have hlt : pre.length < (pre ++ y :: suf').length := by simp
    have hget : (pre ++ y :: suf').get ⟨pre.length, hlt⟩ = y := by
      simp [List.getElem_append_right]
    have ho : owed ins 0 = ins := by simp [owed]
    have hd : (pre ++ y :: suf').drop (pre.length + 1) = suf' := by
      rw [show pre.length + 1 = (pre ++ [y]).length by simp,
          show pre ++ y :: suf' = (pre ++ [y]) ++ suf' by simp, List.drop_left]
    have hstep := insertCarryTM_step_nonblank ins 0 y (by omega) hy []
      (pre ++ y :: suf') pre.length hlt hget
    rw [ho, List.take_left, hd] at hstep
    rw [show (y :: suf').length + 1 = (suf'.length + 1) + 1 by simp,
        run_succ_of_step _ _ _ (suf'.length + 1)
          (not_halt_lt5 ins 0 (by omega) _ rfl) hstep]
    rw [show pre.length + 1 = (pre ++ [ins]).length by simp,
        show pre ++ ins :: suf' = (pre ++ [ins]) ++ suf' by simp,
        insertCarryTM_carry_run ins suf' (pre ++ [ins]) y hy hall']
    have hlen : (pre ++ [ins]).length + suf'.length = pre.length + (y :: suf').length := by
      simp; omega
    rw [hlen, show (pre ++ [ins]) ++ y :: suf' = pre ++ ins :: y :: suf' by simp]

/-- **Carry-phase no-early-halt trajectory.** During the first `suf.length + 1`
steps of the carry loop (starting from state `1 + v`), the machine never enters
the halting state `5`. Mirrors `insertCarryTM_carry_run`'s induction. -/
theorem insertCarryTM_carry_no_early_halt (ins : Nat) (suf : List Nat) :
    ∀ (pre : List Nat) (v : Nat), v < 4 → (∀ x ∈ suf, x < 4) →
      ∀ k, k < suf.length + 1 → ∀ ck,
        runFlatTM k (insertCarryTM ins)
            { state_idx := 1 + v, tapes := [([], pre.length, pre ++ suf)] } = some ck →
        haltingStateReached (insertCarryTM ins) ck = false := by
  induction suf with
  | nil =>
    intro pre v hv _ k hk ck hck
    simp only [List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    have : ck = { state_idx := 1 + v, tapes := [([], pre.length, pre ++ [])] } :=
      (Option.some.inj hck).symm
    subst this
    exact not_halt_lt5 ins (1 + v) (by omega) _ rfl
  | cons y suf' ih =>
    intro pre v hv hall k hk ck hck
    have hy : y < 4 := hall y (by simp)
    have hall' : ∀ x ∈ suf', x < 4 := fun x hx => hall x (by simp [hx])
    cases k with
    | zero =>
      have : ck = { state_idx := 1 + v, tapes := [([], pre.length, pre ++ y :: suf')] } :=
        (Option.some.inj hck).symm
      subst this
      exact not_halt_lt5 ins (1 + v) (by omega) _ rfl
    | succ n =>
      simp only [List.length_cons] at hk
      have hn_lt : n < suf'.length + 1 := by omega
      have hlt : pre.length < (pre ++ y :: suf').length := by simp
      have hget : (pre ++ y :: suf').get ⟨pre.length, hlt⟩ = y := by
        simp [List.getElem_append_right]
      have ho : owed ins (1 + v) = v := by simp [owed]
      have hd : (pre ++ y :: suf').drop (pre.length + 1) = suf' := by
        rw [show pre.length + 1 = (pre ++ [y]).length by simp,
            show pre ++ y :: suf' = (pre ++ [y]) ++ suf' by simp, List.drop_left]
      have hstep := insertCarryTM_step_nonblank ins (1 + v) y (by omega) hy []
        (pre ++ y :: suf') pre.length hlt hget
      rw [ho, List.take_left, hd] at hstep
      rw [run_succ_of_step _ _ _ n
          (not_halt_lt5 ins (1 + v) (by omega) _ rfl) hstep] at hck
      rw [show pre.length + 1 = (pre ++ [v]).length by simp,
          show pre ++ v :: suf' = (pre ++ [v]) ++ suf' by simp] at hck
      exact ih (pre ++ [v]) y hy hall' n hn_lt ck hck

/-- **`insertCarryTM` no-early-halt trajectory.** For `k < suf.length + 1`,
the insert-carry machine has not yet halted. This is the `h_traj2` input
needed by `composeFlatTM_no_early_halt` when `insertCarryTM` sits in the M₂
slot (base case of the `appendAtTM` trajectory assembler). -/
theorem insertCarryTM_no_early_halt (ins : Nat) (suf pre : List Nat)
    (hall : ∀ x ∈ suf, x < 4) :
    ∀ k, k < suf.length + 1 → ∀ ck,
      runFlatTM k (insertCarryTM ins)
          { state_idx := 0, tapes := [([], pre.length, pre ++ suf)] } = some ck →
      haltingStateReached (insertCarryTM ins) ck = false := by
  cases suf with
  | nil =>
    intro k hk ck hck
    simp only [List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    have : ck = { state_idx := 0, tapes := [([], pre.length, pre ++ [])] } :=
      (Option.some.inj hck).symm
    subst this
    exact not_halt_lt5 ins 0 (by omega) _ rfl
  | cons y suf' =>
    intro k hk ck hck
    have hy : y < 4 := hall y (by simp)
    have hall' : ∀ x ∈ suf', x < 4 := fun x hx => hall x (by simp [hx])
    cases k with
    | zero =>
      have : ck = { state_idx := 0, tapes := [([], pre.length, pre ++ y :: suf')] } :=
        (Option.some.inj hck).symm
      subst this
      exact not_halt_lt5 ins 0 (by omega) _ rfl
    | succ n =>
      simp only [List.length_cons] at hk
      have hn_lt : n < suf'.length + 1 := by omega
      have hlt : pre.length < (pre ++ y :: suf').length := by simp
      have hget : (pre ++ y :: suf').get ⟨pre.length, hlt⟩ = y := by
        simp [List.getElem_append_right]
      have ho : owed ins 0 = ins := by simp [owed]
      have hd : (pre ++ y :: suf').drop (pre.length + 1) = suf' := by
        rw [show pre.length + 1 = (pre ++ [y]).length by simp,
            show pre ++ y :: suf' = (pre ++ [y]) ++ suf' by simp, List.drop_left]
      have hstep := insertCarryTM_step_nonblank ins 0 y (by omega) hy []
        (pre ++ y :: suf') pre.length hlt hget
      rw [ho, List.take_left, hd] at hstep
      rw [run_succ_of_step _ _ _ n
          (not_halt_lt5 ins 0 (by omega) _ rfl) hstep] at hck
      rw [show pre.length + 1 = (pre ++ [ins]).length by simp,
          show pre ++ ins :: suf' = (pre ++ [ins]) ++ suf' by simp] at hck
      exact insertCarryTM_carry_no_early_halt ins suf' (pre ++ [ins]) y hy hall' n hn_lt ck hck

end Complexity.Lang.ShiftTape
