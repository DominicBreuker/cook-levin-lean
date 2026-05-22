import Complexity.Complexity.Definitions
import Complexity.Complexity.MachineSemantics
import Complexity.Complexity.TMDecider
import Complexity.Complexity.TMPrimitives
import Complexity.Complexity.Deciders.SAT_TM
import Mathlib.Tactic

set_option autoImplicit false

/-! # EvalCnfTM primitives (Part 2, Step 11.1)

This file lands the smallest single-tape building blocks for the
multi-stage construction of `evalCnfTM` (Step 11.2–11.7). After Step
11.0's architectural pivot (multi-tape `composeFlatTM` is exponential
because `entryMatchesConfig` has no wildcard), the whole EvalCnf TM
runs on **one tape** with a delimiter-encoded scratch region appended
to the SAT input.

### Alphabet `sigEval = 11`

Extends `sigSAT = 7` (positions 0–6 unchanged) with four scratch
markers:

| symbol | meaning                                                 |
|--------|---------------------------------------------------------|
| 0–6    | inherited from `SAT_TM.sigSAT` (see `SAT_TM.lean`).     |
| 7      | scratch-region start marker.                            |
| 8      | var-buffer end marker (separator between var-buffer     |
|        | and OR-accumulator).                                    |
| 9      | OR-accumulator slot marker (separator between OR-acc    |
|        | and AND-acc).                                           |
| 10     | AND-accumulator slot end marker (also tape terminator). |

### Tape layout

```
[encodeCnf N] [encodeAssgn a] 7 [var-buffer ...] 8 [OR-acc] 9 [AND-acc] 10
```

The var-buffer is pre-allocated as a region of `0`s long enough to
hold any variable's unary encoding that will be copied into it during
the per-literal scan (Step 11.4). For simplicity we overestimate the
needed size as the length of the input encoding (way more than
needed but easy to reason about).

### Step 11.1 deliverables (this file)

- `sigEval`, `encodeInputWithScratch`, length / symbol-bound lemmas.
- `writeAtHeadTM` — 2-state TM that overwrites the current head symbol
  with a constant, then halts. `_valid` + one-step `_run` lemma.
- `scanLeftUntilTM` — mirror of `scanRightUntilTM`, scanning left
  until a target marker is found. `_valid` + `_run_found`.
  No `_run_not_found` (caller obligation; the EvalCnf design
  guarantees a target marker exists to the left whenever we scan).
-/

namespace EvalCnfTM
namespace Primitives

open TMPrimitives (currentTapeSymbol_in_range currentTapeSymbol_out_of_range)
open SAT_TM (sigSAT encodeInput encodeInput_length_le encodeInput_symbols_lt
             encodeCnf encodeAssgn)

/-! ## Alphabet -/

/-- Alphabet size for the EvalCnf TM. Bumped from `sigSAT = 7` to add
scratch markers (7-10) and a transient source-cursor marker (11) used
by `copyUnaryTM` (Step 11.3a) to disambiguate source-position tracking
during single-tape shuttling. The cursor marker never appears in the
input encoding `encodeInputWithScratch`; it's written only during
`copyUnaryTM` execution and erased before that primitive halts. -/
def sigEval : Nat := 12

theorem sigSAT_lt_sigEval : sigSAT < sigEval := by decide

theorem sigSAT_le_sigEval : sigSAT ≤ sigEval := by decide

/-! ## Tape encoding with scratch suffix -/

/-- Scratch suffix appended to every EvalCnf tape: marker `7`, a
zero-filled var-buffer of length `n`, marker `8`, an OR-accumulator
slot (initial value `0`), marker `9`, an AND-accumulator slot (initial
value `0`), and the tape-end marker `10`. -/
def scratchSuffix (n : Nat) : List Nat :=
  7 :: (List.replicate n 0 ++ [8, 0, 9, 0, 10])

/-- The input to `evalCnfTM`: `encodeInput Na` followed by a scratch
suffix sized so the var-buffer can hold any unary variable encoding
that appears in `Na`. We use `(encodeInput Na).length` as the buffer
size — a very loose upper bound, but easy to reason about. -/
def encodeInputWithScratch (Na : cnf × assgn) : List Nat :=
  encodeInput Na ++ scratchSuffix (encodeInput Na).length

/-! ### Length lemmas -/

theorem scratchSuffix_length (n : Nat) :
    (scratchSuffix n).length = n + 6 := by
  show (7 :: (List.replicate n 0 ++ [8, 0, 9, 0, 10])).length = n + 6
  rw [List.length_cons, List.length_append, List.length_replicate]
  show n + 5 + 1 = n + 6
  rfl

theorem encodeInputWithScratch_length (Na : cnf × assgn) :
    (encodeInputWithScratch Na).length =
      2 * (encodeInput Na).length + 6 := by
  show ((encodeInput Na) ++ scratchSuffix (encodeInput Na).length).length =
    2 * (encodeInput Na).length + 6
  rw [List.length_append, scratchSuffix_length]
  ring

/-- The eventual `encode` for `EvalCnfTM.decider`: its length is
polynomially bounded by `encodable.size Na`. -/
theorem encodeInputWithScratch_length_le (Na : cnf × assgn) :
    (encodeInputWithScratch Na).length ≤ 2 * encodable.size Na + 8 := by
  rw [encodeInputWithScratch_length]
  have h := encodeInput_length_le Na.1 Na.2
  -- encodeInput Na = encodeInput (Na.1, Na.2)
  have hNa : encodeInput Na = encodeInput (Na.1, Na.2) := by
    rcases Na with ⟨N, a⟩; rfl
  rw [hNa]
  calc 2 * (encodeInput (Na.1, Na.2)).length + 6
      ≤ 2 * (encodable.size (Na.1, Na.2) + 1) + 6 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 6
    _ = 2 * encodable.size (Na.1, Na.2) + 8 := by ring
    _ = 2 * encodable.size Na + 8 := by
        rcases Na with ⟨N, a⟩; rfl

/-! ### Symbol bound

Every symbol on a `encodeInputWithScratch` tape is `< sigEval = 11`. -/

theorem scratchSuffix_symbols_lt (n : Nat) :
    ∀ x ∈ scratchSuffix n, x < sigEval := by
  intro x hx
  have hx' : x ∈ 7 :: (List.replicate n 0 ++ [8, 0, 9, 0, 10]) := hx
  rcases List.mem_cons.mp hx' with h7 | hRest
  · rw [h7]; decide
  · rcases List.mem_append.mp hRest with hRep | hTail
    · rw [List.mem_replicate.mp hRep |>.2]; decide
    · -- hTail : x ∈ [8, 0, 9, 0, 10]
      rcases List.mem_cons.mp hTail with h8 | hTail1
      · rw [h8]; decide
      · rcases List.mem_cons.mp hTail1 with h0 | hTail2
        · rw [h0]; decide
        · rcases List.mem_cons.mp hTail2 with h9 | hTail3
          · rw [h9]; decide
          · rcases List.mem_cons.mp hTail3 with h0' | hTail4
            · rw [h0']; decide
            · have h10 := List.mem_singleton.mp hTail4
              rw [h10]; decide

theorem encodeInputWithScratch_symbols_lt (Na : cnf × assgn) :
    ∀ x ∈ encodeInputWithScratch Na, x < sigEval := by
  intro x hx
  have hx' : x ∈ encodeInput Na ++ scratchSuffix (encodeInput Na).length := hx
  rcases List.mem_append.mp hx' with hIn | hScratch
  · -- Symbol < sigSAT < sigEval.
    have hIn' : x ∈ encodeInput (Na.1, Na.2) := by
      rcases Na with ⟨N, a⟩; exact hIn
    have hSAT := encodeInput_symbols_lt Na.1 Na.2 x hIn'
    exact Nat.lt_of_lt_of_le hSAT sigSAT_le_sigEval
  · exact scratchSuffix_symbols_lt _ x hScratch

/-! ## Generic single-tape `find?` helpers

`find_singleSomeEntry_match` is a generalisation of `scanRightUntilTM`'s
private `find_continueEntry_match`. It works for any family of
transition entries `mk : Nat → FlatTMTransEntry` whose source state is
0 and whose source tape values are `[some w]` — the shape we use over
and over for single-tape primitives.

`find_singleSomeEntry_match_state` further generalises by allowing the
source state to be an arbitrary `N : Nat` (required for `copyUnaryTM`'s
multi-state primitives). -/

/-- `Nat.beq` is reflexive. Needed by the state-`N` variant of the
find helper because `rfl` doesn't reduce `Nat.beq N N` for opaque `N`. -/
theorem nat_beq_self (n : Nat) : (n == n) = true := beq_self_eq_true n

theorem find_singleSomeEntry_match
    (cfg : FlatTMConfig) (v : Nat) (L : List Nat)
    (mk : Nat → FlatTMTransEntry)
    (h_cfg_state : cfg.state_idx = 0)
    (h_cfg_tape : cfg.tapes.map currentTapeSymbol = [some v])
    (h_mk_src_state : ∀ w, (mk w).src_state = 0)
    (h_mk_src_tape : ∀ w, (mk w).src_tape_vals = [some w])
    (h_mem : v ∈ L)
    (h_first : ∀ {w : Nat}, w ∈ L → w ≠ v →
      entryMatchesConfig (mk w) cfg = false) :
    (L.map mk).find?
        (fun entry => entryMatchesConfig entry cfg) =
      some (mk v) := by
  induction L with
  | nil => cases h_mem
  | cons w ws ih =>
      show List.find? _ (mk w :: ws.map mk) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (mk w) cfg = true := by
          show ((mk w).src_state == cfg.state_idx &&
                  decide ((mk w).src_tape_vals =
                    cfg.tapes.map currentTapeSymbol)) = true
          rw [h_cfg_state, h_cfg_tape, h_mk_src_state w, h_mk_src_tape w]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNot := h_first (List.mem_cons.mpr (Or.inl rfl)) hwv
        rw [hNot]
        rcases List.mem_cons.mp h_mem with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws (fun hw hne => h_first (List.mem_cons.mpr (Or.inr hw)) hne)

/-- State-`N` variant of `find_singleSomeEntry_match`. Identical body
except the source state is `N` instead of `0`. -/
theorem find_singleSomeEntry_match_state
    (cfg : FlatTMConfig) (N v : Nat) (L : List Nat)
    (mk : Nat → FlatTMTransEntry)
    (h_cfg_state : cfg.state_idx = N)
    (h_cfg_tape : cfg.tapes.map currentTapeSymbol = [some v])
    (h_mk_src_state : ∀ w, (mk w).src_state = N)
    (h_mk_src_tape : ∀ w, (mk w).src_tape_vals = [some w])
    (h_mem : v ∈ L)
    (h_first : ∀ {w : Nat}, w ∈ L → w ≠ v →
      entryMatchesConfig (mk w) cfg = false) :
    (L.map mk).find?
        (fun entry => entryMatchesConfig entry cfg) =
      some (mk v) := by
  induction L with
  | nil => cases h_mem
  | cons w ws ih =>
      show List.find? _ (mk w :: ws.map mk) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (mk w) cfg = true := by
          show ((mk w).src_state == cfg.state_idx &&
                  decide ((mk w).src_tape_vals =
                    cfg.tapes.map currentTapeSymbol)) = true
          rw [h_cfg_state, h_cfg_tape, h_mk_src_state w, h_mk_src_tape w]
          have h1 : (N == N) = true := nat_beq_self N
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNot := h_first (List.mem_cons.mpr (Or.inl rfl)) hwv
        rw [hNot]
        rcases List.mem_cons.mp h_mem with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws (fun hw hne => h_first (List.mem_cons.mpr (Or.inr hw)) hne)

/-! ## `writeAtHeadTM` — overwrite the current head symbol

A 2-state TM that writes `writeSym` at the head and halts:

- state 0 = write-then-halt.
- state 1 = halt.

Transitions: one for `none` (head out of range — write extends the
tape), and one for each `some v` with `v < sig` (in-range head — just
overwrite). All transitions go `0 → 1` with `Nmove` and write
`some writeSym`. -/

/-- Transition table for `writeAtHeadTM`. Order: `none` entry first,
then `(List.range sig).map (mkSome …)`. -/
def writeAtHeadTM_trans (sig writeSym : Nat) : List FlatTMTransEntry :=
  let mkSome (v : Nat) : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [some v]
      dst_state := 1
      dst_write_vals := [some writeSym]
      move_dirs := [TMMove.Nmove] }
  let noneEntry : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [none]
      dst_state := 1
      dst_write_vals := [some writeSym]
      move_dirs := [TMMove.Nmove] }
  noneEntry :: (List.range sig).map mkSome

/-- The "write at head, then halt" TM. -/
def writeAtHeadTM (sig writeSym : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 2
  trans := writeAtHeadTM_trans sig writeSym
  start := 0
  halt := [false, true]

theorem writeAtHeadTM_valid (sig writeSym : Nat) (h_sym : writeSym < sig) :
    validFlatTM (writeAtHeadTM sig writeSym) := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 2; decide
  · show [false, true].length = 2; rfl
  · intro entry hentry
    have hentry' : entry ∈ writeAtHeadTM_trans sig writeSym := hentry
    unfold writeAtHeadTM_trans at hentry'
    rcases List.mem_cons.mp hentry' with hNone | hSome
    · -- none entry
      subst hNone
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 2; decide
      · show 1 < 2; decide
      · intro x hx
        simp at hx
        subst hx
        trivial
      · intro x hx
        simp at hx
        subst hx
        exact h_sym
    · rcases List.mem_map.mp hSome with ⟨v, hv, hmk⟩
      subst hmk
      have hvlt : v < sig := List.mem_range.mp hv
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 2; decide
      · show 1 < 2; decide
      · intro x hx
        simp at hx
        subst hx
        exact hvlt
      · intro x hx
        simp at hx
        subst hx
        exact h_sym

/-! ### Step / run lemmas for `writeAtHeadTM` -/

private def writeAtHead_noneEntry (writeSym : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [none]
    dst_state := 1
    dst_write_vals := [some writeSym]
    move_dirs := [TMMove.Nmove] }

private def writeAtHead_mkSome (writeSym v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 1
    dst_write_vals := [some writeSym]
    move_dirs := [TMMove.Nmove] }

theorem writeAtHeadTM_trans_eq (sig writeSym : Nat) :
    (writeAtHeadTM sig writeSym).trans =
      writeAtHead_noneEntry writeSym ::
      (List.range sig).map (writeAtHead_mkSome writeSym) := rfl

/-- Application of `writeAtHead_noneEntry`: writes `writeSym` at the
head (extending the tape) and goes to state 1. -/
private theorem applyEntry_writeAtHead_none
    (writeSym : Nat) (left right : List Nat) (head : Nat) :
    applyTransitionEntry
        { state_idx := 0, tapes := [(left, head, right)] }
        (writeAtHead_noneEntry writeSym) =
      some { state_idx := 1
             tapes := [writeCurrentTapeSymbol (left, head, right) (some writeSym)] } :=
  rfl

private theorem applyEntry_writeAtHead_some
    (writeSym v : Nat) (left right : List Nat) (head : Nat) :
    applyTransitionEntry
        { state_idx := 0, tapes := [(left, head, right)] }
        (writeAtHead_mkSome writeSym v) =
      some { state_idx := 1
             tapes := [writeCurrentTapeSymbol (left, head, right) (some writeSym)] } :=
  rfl

/-- One-step step lemma: when the head is in range with current symbol
`some v`, `v < sig`, one step writes `writeSym` and halts. -/
theorem writeAtHeadTM_step_inRange
    (sig writeSym : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : right.get ⟨head, h_head_lt⟩ < sig) :
    stepFlatTM (writeAtHeadTM sig writeSym)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1
             tapes := [writeCurrentTapeSymbol (left, head, right) (some writeSym)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  set v := right.get ⟨head, h_head_lt⟩ with hv
  have hSym0 : currentTapeSymbol (left, head, right) = some v :=
    currentTapeSymbol_in_range h_head_lt
  have hSym : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]
    rw [hSym0]
  -- noneEntry does NOT match (none vs some v).
  have hNotMatchNone :
      entryMatchesConfig (writeAtHead_noneEntry writeSym) cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([none] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      cases h1
    simp [h_ne]
  -- v is in List.range sig.
  have hvInRange : v ∈ List.range sig := List.mem_range.mpr h_sym_lt
  -- find? on the map returns mkSome v.
  have hFindCont :
      ((List.range sig).map (writeAtHead_mkSome writeSym)).find?
          (fun entry => entryMatchesConfig entry cfg) =
        some (writeAtHead_mkSome writeSym v) := by
    refine find_singleSomeEntry_match cfg v _ (writeAtHead_mkSome writeSym)
      rfl hSym (fun _ => rfl) (fun _ => rfl) hvInRange ?_
    intro w _ hwv
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      injection h1 with h2
      exact hwv h2
    simp [h_ne]
  -- Combine.
  show Option.bind ((writeAtHeadTM sig writeSym).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [writeAtHeadTM_trans_eq]
  rw [List.find?_cons, hNotMatchNone, hFindCont]
  exact applyEntry_writeAtHead_some writeSym v left right head

/-- Companion step lemma: when the head is out of range (current symbol
`none`), one step writes `writeSym` (extending the tape) and halts. -/
theorem writeAtHeadTM_step_outOfRange
    (sig writeSym : Nat) (left right : List Nat) (head : Nat)
    (h_head_ge : ¬ head < right.length) :
    stepFlatTM (writeAtHeadTM sig writeSym)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1
             tapes := [writeCurrentTapeSymbol (left, head, right) (some writeSym)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym0 : currentTapeSymbol (left, head, right) = none :=
    currentTapeSymbol_out_of_range h_head_ge
  have hSym : cfg.tapes.map currentTapeSymbol = [none] := by
    show [currentTapeSymbol (left, head, right)] = [none]
    rw [hSym0]
  -- noneEntry matches.
  have hMatchNone :
      entryMatchesConfig (writeAtHead_noneEntry writeSym) cfg = true := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([none] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = true
    rw [hSym]
    have h1 : ((0 : Nat) == 0) = true := rfl
    have h2 : decide (([none] : List (Option Nat)) = [none]) = true :=
      decide_eq_true rfl
    rw [h1, h2]; rfl
  show Option.bind ((writeAtHeadTM sig writeSym).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [writeAtHeadTM_trans_eq]
  rw [List.find?_cons, hMatchNone]
  exact applyEntry_writeAtHead_none writeSym left right head

/-- Halting check on a state-0 configuration: not a halting state. -/
private theorem writeAtHeadTM_state0_not_halting
    (sig writeSym : Nat) (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (writeAtHeadTM sig writeSym)
        { state_idx := 0, tapes := cfg_tapes } = false := rfl

/-- Halting check on a state-1 configuration: IS a halting state. -/
theorem writeAtHeadTM_state1_halting
    (sig writeSym : Nat) (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (writeAtHeadTM sig writeSym)
        { state_idx := 1, tapes := cfg_tapes } = true := rfl

/-- Unified one-step run lemma for `writeAtHeadTM` (head either in range
with bounded symbol, or out of range). -/
theorem writeAtHeadTM_run
    (sig writeSym : Nat) (left right : List Nat) (head : Nat)
    (h_curr : ∀ v, currentTapeSymbol (left, head, right) = some v → v < sig) :
    runFlatTM 1 (writeAtHeadTM sig writeSym)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1
             tapes := [writeCurrentTapeSymbol (left, head, right) (some writeSym)] } := by
  show (if haltingStateReached (writeAtHeadTM sig writeSym)
            { state_idx := 0, tapes := [(left, head, right)] } = true then
          some { state_idx := 0, tapes := [(left, head, right)] }
        else
          match stepFlatTM (writeAtHeadTM sig writeSym)
              { state_idx := 0, tapes := [(left, head, right)] } with
          | none => some { state_idx := 0, tapes := [(left, head, right)] }
          | some cfg' => runFlatTM 0 (writeAtHeadTM sig writeSym) cfg') = _
  rw [writeAtHeadTM_state0_not_halting]
  by_cases h_lt : head < right.length
  · have h_sym_lt : right.get ⟨head, h_lt⟩ < sig := by
      apply h_curr
      exact currentTapeSymbol_in_range h_lt
    rw [writeAtHeadTM_step_inRange sig writeSym left right head h_lt h_sym_lt]
    rfl
  · rw [writeAtHeadTM_step_outOfRange sig writeSym left right head h_lt]
    rfl

/-! ## `advanceRightTM` — move the tape head right by one cell

A 2-state TM that performs a single rightward `Rmove` and halts. No
write, no read-dependence except the entry-match requirement that the
current symbol class (`none` or `some v` with `v < sig`) is covered
by some transition.

Used by the per-literal evaluator (Step 11.5) to step past the literal
sign byte after the polarity classifier has read it, and similarly
elsewhere when a single positional shift is needed between composed
phases. -/

/-- Transition table for `advanceRightTM`. Symmetric to
`writeAtHeadTM_trans` except `dst_write_vals = [none]` and
`move_dirs = [Rmove]`. -/
def advanceRightTM_trans (sig : Nat) : List FlatTMTransEntry :=
  let mkSome (v : Nat) : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [some v]
      dst_state := 1
      dst_write_vals := [none]
      move_dirs := [TMMove.Rmove] }
  let noneEntry : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [none]
      dst_state := 1
      dst_write_vals := [none]
      move_dirs := [TMMove.Rmove] }
  noneEntry :: (List.range sig).map mkSome

/-- The "advance head right one cell, then halt" TM. -/
def advanceRightTM (sig : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 2
  trans := advanceRightTM_trans sig
  start := 0
  halt := [false, true]

theorem advanceRightTM_valid (sig : Nat) :
    validFlatTM (advanceRightTM sig) := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 2; decide
  · show [false, true].length = 2; rfl
  · intro entry hentry
    have hentry' : entry ∈ advanceRightTM_trans sig := hentry
    unfold advanceRightTM_trans at hentry'
    rcases List.mem_cons.mp hentry' with hNone | hSome
    · subst hNone
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 2; decide
      · show 1 < 2; decide
      · intro x hx
        simp at hx
        subst hx
        trivial
      · intro x hx
        simp at hx
        subst hx
        trivial
    · rcases List.mem_map.mp hSome with ⟨v, hv, hmk⟩
      subst hmk
      have hvlt : v < sig := List.mem_range.mp hv
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 2; decide
      · show 1 < 2; decide
      · intro x hx
        simp at hx
        subst hx
        exact hvlt
      · intro x hx
        simp at hx
        subst hx
        trivial

/-! ### Step / run lemmas for `advanceRightTM` -/

private def advanceRight_noneEntry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [none]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def advanceRight_mkSome (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

theorem advanceRightTM_trans_eq (sig : Nat) :
    (advanceRightTM sig).trans =
      advanceRight_noneEntry ::
      (List.range sig).map advanceRight_mkSome := rfl

/-- Application of `advanceRight_noneEntry`: moves head right (the tape
contents are unchanged because `writeCurrentTapeSymbol _ none = id`). -/
private theorem applyEntry_advanceRight_none
    (left right : List Nat) (head : Nat) :
    applyTransitionEntry
        { state_idx := 0, tapes := [(left, head, right)] }
        advanceRight_noneEntry =
      some { state_idx := 1
             tapes := [(left, head + 1, right)] } := rfl

private theorem applyEntry_advanceRight_some
    (v : Nat) (left right : List Nat) (head : Nat) :
    applyTransitionEntry
        { state_idx := 0, tapes := [(left, head, right)] }
        (advanceRight_mkSome v) =
      some { state_idx := 1
             tapes := [(left, head + 1, right)] } := rfl

/-- One-step step lemma: when the head is in range with current symbol
`some v`, `v < sig`, one step advances the head and halts. -/
theorem advanceRightTM_step_inRange
    (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : right.get ⟨head, h_head_lt⟩ < sig) :
    stepFlatTM (advanceRightTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  set v := right.get ⟨head, h_head_lt⟩ with hv
  have hSym0 : currentTapeSymbol (left, head, right) = some v :=
    currentTapeSymbol_in_range h_head_lt
  have hSym : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]
    rw [hSym0]
  have hNotMatchNone :
      entryMatchesConfig advanceRight_noneEntry cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([none] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      cases h1
    simp [h_ne]
  have hvInRange : v ∈ List.range sig := List.mem_range.mpr h_sym_lt
  have hFindCont :
      ((List.range sig).map advanceRight_mkSome).find?
          (fun entry => entryMatchesConfig entry cfg) =
        some (advanceRight_mkSome v) := by
    refine find_singleSomeEntry_match cfg v _ advanceRight_mkSome
      rfl hSym (fun _ => rfl) (fun _ => rfl) hvInRange ?_
    intro w _ hwv
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      injection h1 with h2
      exact hwv h2
    simp [h_ne]
  show Option.bind ((advanceRightTM sig).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [advanceRightTM_trans_eq]
  rw [List.find?_cons, hNotMatchNone, hFindCont]
  exact applyEntry_advanceRight_some v left right head

/-- Companion step lemma: when the head is out of range (current symbol
`none`), one step advances the head and halts. -/
theorem advanceRightTM_step_outOfRange
    (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_ge : ¬ head < right.length) :
    stepFlatTM (advanceRightTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym0 : currentTapeSymbol (left, head, right) = none :=
    currentTapeSymbol_out_of_range h_head_ge
  have hSym : cfg.tapes.map currentTapeSymbol = [none] := by
    show [currentTapeSymbol (left, head, right)] = [none]
    rw [hSym0]
  have hMatchNone :
      entryMatchesConfig advanceRight_noneEntry cfg = true := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([none] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = true
    rw [hSym]
    have h1 : ((0 : Nat) == 0) = true := rfl
    have h2 : decide (([none] : List (Option Nat)) = [none]) = true :=
      decide_eq_true rfl
    rw [h1, h2]; rfl
  show Option.bind ((advanceRightTM sig).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [advanceRightTM_trans_eq]
  rw [List.find?_cons, hMatchNone]
  exact applyEntry_advanceRight_none left right head

private theorem advanceRightTM_state0_not_halting
    (sig : Nat) (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (advanceRightTM sig)
        { state_idx := 0, tapes := cfg_tapes } = false := rfl

theorem advanceRightTM_state1_halting
    (sig : Nat) (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (advanceRightTM sig)
        { state_idx := 1, tapes := cfg_tapes } = true := rfl

/-- Unified one-step run lemma for `advanceRightTM` (head either in
range with bounded symbol, or out of range). -/
theorem advanceRightTM_run
    (sig : Nat) (left right : List Nat) (head : Nat)
    (h_curr : ∀ v, currentTapeSymbol (left, head, right) = some v → v < sig) :
    runFlatTM 1 (advanceRightTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  show (if haltingStateReached (advanceRightTM sig)
            { state_idx := 0, tapes := [(left, head, right)] } = true then
          some { state_idx := 0, tapes := [(left, head, right)] }
        else
          match stepFlatTM (advanceRightTM sig)
              { state_idx := 0, tapes := [(left, head, right)] } with
          | none => some { state_idx := 0, tapes := [(left, head, right)] }
          | some cfg' => runFlatTM 0 (advanceRightTM sig) cfg') = _
  rw [advanceRightTM_state0_not_halting]
  by_cases h_lt : head < right.length
  · have h_sym_lt : right.get ⟨head, h_lt⟩ < sig := by
      apply h_curr
      exact currentTapeSymbol_in_range h_lt
    rw [advanceRightTM_step_inRange sig left right head h_lt h_sym_lt]
    rfl
  · rw [advanceRightTM_step_outOfRange sig left right head h_lt]
    rfl

/-! ## `scanLeftUntilTM` — scan the tape head left until a target symbol

Mirror of `TMPrimitives.scanRightUntilTM`. Two states:

- state 0 = scanning. For every in-range symbol `v ≠ target`,
  transition `(0, [some v]) → (0, [some v], [Lmove])`. For the symbol
  `target`, transition `(0, [some target]) → (1, [some target], [Nmove])`.
- state 1 = accept-halt (found target).

Unlike `scanRightUntilTM`, there is **no `none` (off-tape) entry** and
no reject state. The caller's contract is that `target` appears at
some position `pos ≤ head`; if it does not, the head spins at position
0 indefinitely (Lmove from `head = 0` saturates at `0`).

This is enough for the EvalCnf TM design: every scan-left in the
construction targets a marker (`7`, `8`, `9` in the scratch region)
which is guaranteed by the encoding to exist to the left of the
current head. -/

/-- Transition table for `scanLeftUntilTM`: the halt entry first
(target match), then the filtered range of non-target symbols. -/
def scanLeftUntilTM_trans (sig target : Nat) : List FlatTMTransEntry :=
  let mkContinue (v : Nat) : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [some v]
      dst_state := 0
      dst_write_vals := [none]
      move_dirs := [TMMove.Lmove] }
  let mkHalt : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [some target]
      dst_state := 1
      dst_write_vals := [none]
      move_dirs := [TMMove.Nmove] }
  mkHalt :: ((List.range sig).filter (fun v => decide (v ≠ target))).map mkContinue

/-- The "scan left until target" TM. -/
def scanLeftUntilTM (sig target : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 2
  trans := scanLeftUntilTM_trans sig target
  start := 0
  halt := [false, true]

theorem scanLeftUntilTM_valid (sig target : Nat) (h_target : target < sig) :
    validFlatTM (scanLeftUntilTM sig target) := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 2; decide
  · show [false, true].length = 2; rfl
  · intro entry hentry
    have hentry' : entry ∈ scanLeftUntilTM_trans sig target := hentry
    unfold scanLeftUntilTM_trans at hentry'
    rcases List.mem_cons.mp hentry' with hHalt | hCont
    · subst hHalt
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 2; decide
      · show 1 < 2; decide
      · intro x hx
        simp at hx
        subst hx
        exact h_target
      · intro x hx
        simp at hx
        subst hx
        trivial
    · rcases List.mem_map.mp hCont with ⟨v, hv, hmk⟩
      subst hmk
      have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
      have hvlt : v < sig := List.mem_range.mp hv'
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 2; decide
      · show 0 < 2; decide
      · intro x hx
        simp at hx
        subst hx
        exact hvlt
      · intro x hx
        simp at hx
        subst hx
        trivial

/-! ### Step / run lemmas for `scanLeftUntilTM` -/

private def scanLeftHaltEntry (target : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some target]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def scanLeftContinueEntry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 0
    dst_write_vals := [none]
    move_dirs := [TMMove.Lmove] }

theorem scanLeftUntilTM_trans_eq (sig target : Nat) :
    (scanLeftUntilTM sig target).trans =
      scanLeftHaltEntry target ::
      ((List.range sig).filter (fun v => decide (v ≠ target))).map
        scanLeftContinueEntry := rfl

/-- Computation of `applyTransitionEntry` for a single-tape entry. -/
private theorem applyEntry_scanLeft_singleTape
    (cfg_state_idx new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) (move : TMMove) :
    applyTransitionEntry
        { state_idx := cfg_state_idx, tapes := [(left, head, right)] }
        { src_state := cfg_state_idx
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [move] } =
      some { state_idx := new_state
             tapes := [moveTapeHead (left, head, right) move] } := rfl

/-- Step lemma: on a target symbol, one step halts in state 1. -/
theorem scanLeftUntilTM_step_match
    (sig target : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = target) :
    stepFlatTM (scanLeftUntilTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some target := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig (scanLeftHaltEntry target) cfg = true := by
    show ((0 : Nat) == 0 &&
            decide (([some target] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]
    have h1 : ((0 : Nat) == 0) = true := rfl
    have h2 : decide (([some target] : List (Option Nat)) = [some target]) = true :=
      decide_eq_true rfl
    rw [h1, h2]; rfl
  show Option.bind ((scanLeftUntilTM sig target).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [scanLeftUntilTM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry cfg (scanLeftHaltEntry target) = _
  exact applyEntry_scanLeft_singleTape 0 1 left right head (some target) TMMove.Nmove

/-- Helper: among a list of `scanLeftContinueEntry` entries indexed by a
`List Nat`, `find?` of the config-match predicate returns
`scanLeftContinueEntry v` provided `v` is in the list and no earlier
element matches. -/
private theorem find_scanLeftContinueEntry_match
    (cfg : FlatTMConfig) (v : Nat) (L : List Nat)
    (h_cfg_state : cfg.state_idx = 0)
    (h_cfg_tape : cfg.tapes.map currentTapeSymbol = [some v])
    (h_mem : v ∈ L)
    (h_first : ∀ {w : Nat}, w ∈ L → w ≠ v →
      entryMatchesConfig (scanLeftContinueEntry w) cfg = false) :
    (L.map scanLeftContinueEntry).find?
        (fun entry => entryMatchesConfig entry cfg) =
      some (scanLeftContinueEntry v) := by
  induction L with
  | nil => cases h_mem
  | cons w ws ih =>
      show List.find? _ (scanLeftContinueEntry w :: ws.map scanLeftContinueEntry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (scanLeftContinueEntry w) cfg = true := by
          show ((0 : Nat) == cfg.state_idx &&
                  decide (([some w] : List (Option Nat)) =
                    cfg.tapes.map currentTapeSymbol)) = true
          rw [h_cfg_state, h_cfg_tape]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNot := h_first (List.mem_cons.mpr (Or.inl rfl)) hwv
        rw [hNot]
        rcases List.mem_cons.mp h_mem with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws (fun hw hne => h_first (List.mem_cons.mpr (Or.inr hw)) hne)

/-- One step on a non-target in-range symbol moves the head left. -/
theorem scanLeftUntilTM_step_advance
    (sig target : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : right.get ⟨head, h_head_lt⟩ < sig)
    (h_ne : right.get ⟨head, h_head_lt⟩ ≠ target) :
    stepFlatTM (scanLeftUntilTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 0, tapes := [(left, head - 1, right)] } := by
  let v := right.get ⟨head, h_head_lt⟩
  let cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym0 : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt]
  have hSym : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]
    rw [hSym0]
  -- haltEntry does NOT match (target ≠ v).
  have hNotMatchHalt : entryMatchesConfig (scanLeftHaltEntry target) cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some target] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([some target] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      injection h1 with h2
      exact h_ne h2.symm
    simp [h_ne']
  -- v is in the filtered range list.
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ target)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, ?_⟩
    show decide (v ≠ target) = true
    exact decide_eq_true h_ne
  -- find? on the filtered.map list returns continueEntry v.
  have hFindCont :
      (((List.range sig).filter (fun w => decide (w ≠ target))).map scanLeftContinueEntry).find?
          (fun entry => entryMatchesConfig entry cfg) =
        some (scanLeftContinueEntry v) := by
    refine find_scanLeftContinueEntry_match cfg v _ rfl hSym hvInFilter ?_
    intro w _ hwv
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      injection h1 with h2
      exact hwv h2
    simp [h_ne']
  -- Combine.
  show Option.bind ((scanLeftUntilTM sig target).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [scanLeftUntilTM_trans_eq]
  rw [List.find?_cons, hNotMatchHalt, hFindCont]
  show applyTransitionEntry cfg (scanLeftContinueEntry v) = _
  exact applyEntry_scanLeft_singleTape 0 0 left right head (some v) TMMove.Lmove

/-- Halting check on a state-0 configuration: not a halting state. -/
private theorem scanLeftUntilTM_state0_not_halting
    (sig target : Nat) (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (scanLeftUntilTM sig target)
        { state_idx := 0, tapes := cfg_tapes } = false := rfl

/-- A state-1 configuration of `scanLeftUntilTM` IS a halting state. -/
theorem scanLeftUntilTM_state1_halting
    (sig target : Nat) (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (scanLeftUntilTM sig target)
        { state_idx := 1, tapes := cfg_tapes } = true := rfl

/-- One unfolding step of `runFlatTM` from a state-0 config that
takes one TM step to `cfg'`. -/
private theorem runFlatTM_scanLeft_state0_unfold
    (sig target : Nat) (n : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
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
  rw [scanLeftUntilTM_state0_not_halting, h_step]
  rfl

/-- Main operational correctness for the "target found" case.

By induction on the gap `gap = head - pos`. The caller provides:
* `head`: the starting head position (in-range),
* `gap`: `head - pos`, the number of left-steps before finding target,
* `h_gap_le`: `gap ≤ head` (so `head - gap` is a real position),
* `h_in_range`: `head - gap < right.length` (target position in range),
* `h_get_target`: the symbol at `head - gap` is `target`,
* `h_before`: every position strictly to the right of the target (down
  to and including `head`) carries a non-target symbol within `[0, sig)`.

After `gap + 1` steps, the TM halts in state 1 with head at position
`head - gap`. -/
theorem scanLeftUntilTM_run_found
    (sig target : Nat) (left right : List Nat) :
    ∀ (gap head : Nat) (h_gap_le : gap ≤ head)
      (h_head_lt : head < right.length)
      (h_in_range : head - gap < right.length),
      right.get ⟨head - gap, h_in_range⟩ = target →
      (∀ k, k < gap → ∃ (h : head - k < right.length),
        right.get ⟨head - k, h⟩ < sig ∧
          right.get ⟨head - k, h⟩ ≠ target) →
      runFlatTM (gap + 1) (scanLeftUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 1, tapes := [(left, head - gap, right)] }
  | 0, head, _, h_head_lt, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := h_head_lt
      have h_get : right.get ⟨head, h_lt⟩ = target := by
        have heq : (⟨head - 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.sub_zero head)
        rw [heq] at h_get_target
        exact h_get_target
      rw [runFlatTM_scanLeft_state0_unfold sig target 0 _ _
        (scanLeftUntilTM_step_match sig target left right head h_lt h_get)]
      show (some { state_idx := 1, tapes := [(left, head, right)] } : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head - 0, right)] }
      rw [Nat.sub_zero]
  | gap + 1, head, h_gap_le, h_head_lt, h_in_range, h_get_target, h_before => by
      -- First step: advance from head to head - 1.
      have h_head_pos : head ≥ 1 := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_gap_le
      have h_head_lt' : head < right.length := h_head_lt
      rcases h_before 0 (Nat.zero_lt_succ _) with ⟨h_kk, h_sym_lt, h_sym_ne⟩
      have heq0 : (⟨head - 0, h_kk⟩ : Fin right.length) = ⟨head, h_head_lt'⟩ :=
        Fin.eq_of_val_eq (Nat.sub_zero head)
      have h_get_head : right.get ⟨head, h_head_lt'⟩ < sig := by
        rw [heq0] at h_sym_lt; exact h_sym_lt
      have h_get_head_ne : right.get ⟨head, h_head_lt'⟩ ≠ target := by
        rw [heq0] at h_sym_ne; exact h_sym_ne
      -- Recursion at (head - 1, gap).
      have h_new_head : head - 1 < right.length :=
        Nat.lt_of_le_of_lt (Nat.sub_le head 1) h_head_lt'
      have h_new_gap_le : gap ≤ head - 1 := by
        -- gap + 1 ≤ head → gap ≤ head - 1.
        exact Nat.le_sub_of_add_le h_gap_le
      -- (head - 1) - gap = head - (gap + 1).
      have h_sub_swap : (head - 1) - gap = head - (gap + 1) := by
        rw [Nat.sub_sub, Nat.add_comm 1 gap]
      have h_in_range' : (head - 1) - gap < right.length := by
        rw [h_sub_swap]; exact h_in_range
      have h_get_target' :
          right.get ⟨(head - 1) - gap, h_in_range'⟩ = target := by
        have heq : (⟨(head - 1) - gap, h_in_range'⟩ : Fin right.length) =
            ⟨head - (gap + 1), h_in_range⟩ := Fin.eq_of_val_eq h_sub_swap
        rw [heq]; exact h_get_target
      have h_before' :
          ∀ k, k < gap → ∃ (h : (head - 1) - k < right.length),
            right.get ⟨(head - 1) - k, h⟩ < sig ∧
              right.get ⟨(head - 1) - k, h⟩ ≠ target := by
        intro k hk
        rcases h_before (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk, h1, h2⟩
        have hShift : (head - 1) - k = head - (k + 1) := by
          rw [Nat.sub_sub, Nat.add_comm 1 k]
        have h_kk' : (head - 1) - k < right.length := hShift ▸ h_kk
        refine ⟨h_kk', ?_, ?_⟩
        · have heq : (⟨(head - 1) - k, h_kk'⟩ : Fin right.length) =
              ⟨head - (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift
          rw [heq]; exact h1
        · have heq : (⟨(head - 1) - k, h_kk'⟩ : Fin right.length) =
              ⟨head - (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift
          rw [heq]; exact h2
      have hih :=
        scanLeftUntilTM_run_found sig target left right gap (head - 1)
          h_new_gap_le h_new_head h_in_range' h_get_target' h_before'
      -- Unfold first step, apply step_advance, then IH.
      rw [runFlatTM_scanLeft_state0_unfold sig target (gap + 1) _ _
        (scanLeftUntilTM_step_advance sig target left right head h_head_lt'
          h_get_head h_get_head_ne)]
      rw [hih]
      show (some { state_idx := 1, tapes := [(left, (head - 1) - gap, right)] } :
              Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head - (gap + 1), right)] }
      rw [h_sub_swap]
  termination_by gap _ _ _ _ _ _ => gap

/-! ## `clearRegionTM` — scan right, writing fill, until target marker

Two states:

- state 0 = clearing. For every in-range symbol `v ≠ endMarker`,
  transition `(0, [some v]) → (0, [some fillSym], [Rmove])` (write
  fill, advance head). For the symbol `endMarker`, transition
  `(0, [some endMarker]) → (1, [none], [Nmove])` (preserve the
  marker, halt).
- state 1 = accept-halt.

As with `scanLeftUntilTM`, there is **no `none` (off-tape) entry** and
no reject state. Caller obligation: `endMarker` appears at some
in-range position to the right of (or at) the starting head. -/

/-- Transition table for `clearRegionTM`. -/
def clearRegionTM_trans (sig fillSym endMarker : Nat) : List FlatTMTransEntry :=
  let mkContinue (v : Nat) : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [some v]
      dst_state := 0
      dst_write_vals := [some fillSym]
      move_dirs := [TMMove.Rmove] }
  let mkHalt : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [some endMarker]
      dst_state := 1
      dst_write_vals := [none]
      move_dirs := [TMMove.Nmove] }
  mkHalt :: ((List.range sig).filter (fun v => decide (v ≠ endMarker))).map mkContinue

/-- "Clear region" TM: writes `fillSym` over every cell up to (but
not including) the next `endMarker`. -/
def clearRegionTM (sig fillSym endMarker : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 2
  trans := clearRegionTM_trans sig fillSym endMarker
  start := 0
  halt := [false, true]

theorem clearRegionTM_valid (sig fillSym endMarker : Nat)
    (h_fill : fillSym < sig) (h_end : endMarker < sig) :
    validFlatTM (clearRegionTM sig fillSym endMarker) := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 2; decide
  · show [false, true].length = 2; rfl
  · intro entry hentry
    have hentry' : entry ∈ clearRegionTM_trans sig fillSym endMarker := hentry
    unfold clearRegionTM_trans at hentry'
    rcases List.mem_cons.mp hentry' with hHalt | hCont
    · subst hHalt
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 2; decide
      · show 1 < 2; decide
      · intro x hx
        simp at hx
        subst hx
        exact h_end
      · intro x hx
        simp at hx
        subst hx
        trivial
    · rcases List.mem_map.mp hCont with ⟨v, hv, hmk⟩
      subst hmk
      have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
      have hvlt : v < sig := List.mem_range.mp hv'
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 2; decide
      · show 0 < 2; decide
      · intro x hx
        simp at hx
        subst hx
        exact hvlt
      · intro x hx
        simp at hx
        subst hx
        exact h_fill

/-! ### Step / run lemmas for `clearRegionTM` -/

private def clearRegionHaltEntry (endMarker : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some endMarker]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def clearRegionContinueEntry (fillSym v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 0
    dst_write_vals := [some fillSym]
    move_dirs := [TMMove.Rmove] }

theorem clearRegionTM_trans_eq (sig fillSym endMarker : Nat) :
    (clearRegionTM sig fillSym endMarker).trans =
      clearRegionHaltEntry endMarker ::
      ((List.range sig).filter (fun v => decide (v ≠ endMarker))).map
        (clearRegionContinueEntry fillSym) := rfl

/-- Application of `clearRegionHaltEntry`: state goes to 1, tape
unchanged (no write, no move). -/
private theorem applyEntry_clearRegion_halt
    (endMarker : Nat) (left right : List Nat) (head : Nat) :
    applyTransitionEntry
        { state_idx := 0, tapes := [(left, head, right)] }
        (clearRegionHaltEntry endMarker) =
      some { state_idx := 1, tapes := [(left, head, right)] } := rfl

/-- Application of `clearRegionContinueEntry`: state stays 0, writes
`fillSym` at the head, advances right. -/
private theorem applyEntry_clearRegion_continue
    (fillSym v : Nat) (left right : List Nat) (head : Nat) :
    applyTransitionEntry
        { state_idx := 0, tapes := [(left, head, right)] }
        (clearRegionContinueEntry fillSym v) =
      some { state_idx := 0
             tapes := [moveTapeHead
               (writeCurrentTapeSymbol (left, head, right) (some fillSym))
               TMMove.Rmove] } := rfl

/-- Step lemma: on `endMarker`, one step halts in state 1 with tape
unchanged. -/
theorem clearRegionTM_step_match
    (sig fillSym endMarker : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = endMarker) :
    stepFlatTM (clearRegionTM sig fillSym endMarker)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some endMarker := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig (clearRegionHaltEntry endMarker) cfg = true := by
    show ((0 : Nat) == 0 &&
            decide (([some endMarker] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]
    have h1 : ((0 : Nat) == 0) = true := rfl
    have h2 : decide (([some endMarker] : List (Option Nat)) = [some endMarker]) = true :=
      decide_eq_true rfl
    rw [h1, h2]; rfl
  show Option.bind ((clearRegionTM sig fillSym endMarker).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [clearRegionTM_trans_eq, List.find?_cons, hMatch]
  exact applyEntry_clearRegion_halt endMarker left right head

/-- Helper: among a list of `clearRegionContinueEntry` entries indexed
by a `List Nat`, `find?` of the config-match predicate returns
`clearRegionContinueEntry fillSym v` when `v` is in the list and no
earlier element matches. -/
private theorem find_clearRegionContinueEntry_match
    (cfg : FlatTMConfig) (fillSym v : Nat) (L : List Nat)
    (h_cfg_state : cfg.state_idx = 0)
    (h_cfg_tape : cfg.tapes.map currentTapeSymbol = [some v])
    (h_mem : v ∈ L)
    (h_first : ∀ {w : Nat}, w ∈ L → w ≠ v →
      entryMatchesConfig (clearRegionContinueEntry fillSym w) cfg = false) :
    (L.map (clearRegionContinueEntry fillSym)).find?
        (fun entry => entryMatchesConfig entry cfg) =
      some (clearRegionContinueEntry fillSym v) := by
  induction L with
  | nil => cases h_mem
  | cons w ws ih =>
      show List.find? _ (clearRegionContinueEntry fillSym w ::
                          ws.map (clearRegionContinueEntry fillSym)) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (clearRegionContinueEntry fillSym w) cfg = true := by
          show ((0 : Nat) == cfg.state_idx &&
                  decide (([some w] : List (Option Nat)) =
                    cfg.tapes.map currentTapeSymbol)) = true
          rw [h_cfg_state, h_cfg_tape]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNot := h_first (List.mem_cons.mpr (Or.inl rfl)) hwv
        rw [hNot]
        rcases List.mem_cons.mp h_mem with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws (fun hw hne => h_first (List.mem_cons.mpr (Or.inr hw)) hne)

/-- Step lemma: on an in-range non-endMarker symbol, one step writes
`fillSym` at the head and advances right. -/
theorem clearRegionTM_step_advance
    (sig fillSym endMarker : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : right.get ⟨head, h_head_lt⟩ < sig)
    (h_ne : right.get ⟨head, h_head_lt⟩ ≠ endMarker) :
    stepFlatTM (clearRegionTM sig fillSym endMarker)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 0
             tapes := [(left, head + 1,
                        right.take head ++ fillSym :: right.drop (head + 1))] } := by
  let v := right.get ⟨head, h_head_lt⟩
  let cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym0 : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt]
  have hSym : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]
    rw [hSym0]
  -- haltEntry does NOT match.
  have hNotMatchHalt :
      entryMatchesConfig (clearRegionHaltEntry endMarker) cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some endMarker] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([some endMarker] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      injection h1 with h2
      exact h_ne h2.symm
    simp [h_ne']
  -- v is in the filtered list.
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ endMarker)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, ?_⟩
    show decide (v ≠ endMarker) = true
    exact decide_eq_true h_ne
  -- find? returns continueEntry v.
  have hFindCont :
      (((List.range sig).filter (fun w => decide (w ≠ endMarker))).map
          (clearRegionContinueEntry fillSym)).find?
          (fun entry => entryMatchesConfig entry cfg) =
        some (clearRegionContinueEntry fillSym v) := by
    refine find_clearRegionContinueEntry_match cfg fillSym v _ rfl hSym hvInFilter ?_
    intro w _ hwv
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      injection h1 with h2
      exact hwv h2
    simp [h_ne']
  -- Combine.
  show Option.bind ((clearRegionTM sig fillSym endMarker).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [clearRegionTM_trans_eq]
  rw [List.find?_cons, hNotMatchHalt, hFindCont]
  show applyTransitionEntry { state_idx := 0, tapes := [(left, head, right)] }
        (clearRegionContinueEntry fillSym v) = _
  rw [applyEntry_clearRegion_continue fillSym v left right head]
  -- writeCurrentTapeSymbol (left, head, right) (some fillSym) with head in range
  -- = (left, head, right.take head ++ fillSym :: right.drop (head + 1))
  have h_write : writeCurrentTapeSymbol (left, head, right) (some fillSym) =
      (left, head, right.take head ++ fillSym :: right.drop (head + 1)) := by
    simp [writeCurrentTapeSymbol, h_head_lt]
  rw [h_write]
  rfl

/-- Halting check on a state-0 configuration: not a halting state. -/
private theorem clearRegionTM_state0_not_halting
    (sig fillSym endMarker : Nat) (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (clearRegionTM sig fillSym endMarker)
        { state_idx := 0, tapes := cfg_tapes } = false := rfl

/-- State-1 configuration of `clearRegionTM` IS halting. -/
theorem clearRegionTM_state1_halting
    (sig fillSym endMarker : Nat) (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (clearRegionTM sig fillSym endMarker)
        { state_idx := 1, tapes := cfg_tapes } = true := rfl

/-- One unfolding step of `runFlatTM` from a state-0 config that takes
one TM step to `cfg'`. -/
private theorem runFlatTM_clearRegion_state0_unfold
    (sig fillSym endMarker n : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (clearRegionTM sig fillSym endMarker)
        { state_idx := 0, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (clearRegionTM sig fillSym endMarker)
        { state_idx := 0, tapes := tapes } =
      runFlatTM n (clearRegionTM sig fillSym endMarker) cfg' := by
  show (if haltingStateReached (clearRegionTM sig fillSym endMarker)
            { state_idx := 0, tapes := tapes } = true then
          some { state_idx := 0, tapes := tapes }
        else
          match stepFlatTM (clearRegionTM sig fillSym endMarker)
              { state_idx := 0, tapes := tapes } with
          | none => some { state_idx := 0, tapes := tapes }
          | some cfg' => runFlatTM n (clearRegionTM sig fillSym endMarker) cfg') =
    runFlatTM n (clearRegionTM sig fillSym endMarker) cfg'
  rw [clearRegionTM_state0_not_halting, h_step]
  rfl

/-! ### `fillPrefix` — characterization of the resulting tape

After clearing `gap` cells starting from `head`, the tape becomes
`right.take head ++ List.replicate gap fillSym ++ right.drop (head + gap)`.
We name this `fillPrefix` and establish the inductive identity it
satisfies so the run lemma can substitute cleanly. -/

/-- The result of overwriting `gap` cells starting at position `head`
with `fillSym`. -/
def fillPrefix (right : List Nat) (head gap fillSym : Nat) : List Nat :=
  right.take head ++ List.replicate gap fillSym ++ right.drop (head + gap)

theorem fillPrefix_zero (right : List Nat) (head fillSym : Nat) :
    fillPrefix right head 0 fillSym = right.take head ++ right.drop head := by
  show right.take head ++ List.replicate 0 fillSym ++ right.drop (head + 0) =
    right.take head ++ right.drop head
  rw [List.replicate, List.append_nil, Nat.add_zero]

theorem fillPrefix_zero_of_le (right : List Nat) (head fillSym : Nat)
    (h_head : head ≤ right.length) :
    fillPrefix right head 0 fillSym = right := by
  rw [fillPrefix_zero]; exact List.take_append_drop _ _

/-- A `take`-of-append lemma: when the prefix has length `n`,
`(pfx ++ x :: rest).take (n + 1) = pfx ++ [x]`. -/
private theorem take_append_singleton (pfx : List Nat) (x : Nat) (rest : List Nat) :
    (pfx ++ x :: rest).take (pfx.length + 1) = pfx ++ [x] := by
  induction pfx with
  | nil => rfl
  | cons p ps ih =>
      show (p :: (ps ++ x :: rest)).take (ps.length + 1 + 1) = p :: (ps ++ [x])
      show p :: (ps ++ x :: rest).take (ps.length + 1) = p :: (ps ++ [x])
      rw [ih]

/-- A `drop`-of-append lemma: when the prefix has length `n`,
`(pfx ++ x :: rest).drop (n + 1 + gap) = rest.drop gap`. -/
private theorem drop_append_singleton (pfx : List Nat) (x : Nat) (rest : List Nat) (gap : Nat) :
    (pfx ++ x :: rest).drop (pfx.length + 1 + gap) = rest.drop gap := by
  induction pfx with
  | nil =>
      show (x :: rest).drop (0 + 1 + gap) = rest.drop gap
      rw [Nat.zero_add]
      show (x :: rest).drop (1 + gap) = rest.drop gap
      rw [Nat.add_comm 1 gap]
      rfl
  | cons p ps ih =>
      show (p :: (ps ++ x :: rest)).drop (ps.length + 1 + 1 + gap) = rest.drop gap
      have h_eq : ps.length + 1 + 1 + gap = ps.length + 1 + gap + 1 := by
        rw [Nat.add_right_comm]
      rw [h_eq]
      show (ps ++ x :: rest).drop (ps.length + 1 + gap) = rest.drop gap
      exact ih

/-- The key step lemma for `fillPrefix`: clearing `gap+1` from `head`
in `right` equals clearing `gap` from `head+1` in `right1`, where
`right1 = right.take head ++ fillSym :: right.drop (head + 1)` is the
tape after a single write at position `head`. -/
theorem fillPrefix_succ (right : List Nat) (head gap fillSym : Nat)
    (h_head : head < right.length) :
    fillPrefix (right.take head ++ fillSym :: right.drop (head + 1))
      (head + 1) gap fillSym =
    fillPrefix right head (gap + 1) fillSym := by
  have h_take_len : (right.take head).length = head :=
    List.length_take_of_le (Nat.le_of_lt h_head)
  -- Use calc-style to manipulate specific subterms.
  unfold fillPrefix
  -- Substitute take and drop pieces individually via calc.
  have h_take_piece :
      (right.take head ++ fillSym :: right.drop (head + 1)).take (head + 1) =
      right.take head ++ [fillSym] := by
    calc (right.take head ++ fillSym :: right.drop (head + 1)).take (head + 1)
        = (right.take head ++ fillSym :: right.drop (head + 1)).take ((right.take head).length + 1) := by
            rw [h_take_len]
      _ = right.take head ++ [fillSym] := take_append_singleton _ _ _
  have h_drop_piece :
      (right.take head ++ fillSym :: right.drop (head + 1)).drop ((head + 1) + gap) =
      right.drop (head + (gap + 1)) := by
    calc (right.take head ++ fillSym :: right.drop (head + 1)).drop ((head + 1) + gap)
        = (right.take head ++ fillSym :: right.drop (head + 1)).drop
            ((right.take head).length + 1 + gap) := by rw [h_take_len]
      _ = (right.drop (head + 1)).drop gap := drop_append_singleton _ _ _ _
      _ = right.drop (head + (gap + 1)) := by rw [List.drop_drop]; congr 1; ring
  rw [h_take_piece, h_drop_piece]
  -- Goal: right.take head ++ [fillSym] ++ replicate gap fillSym ++ right.drop (head + (gap+1))
  --     = right.take head ++ replicate (gap+1) fillSym ++ right.drop (head + (gap+1))
  have h_rep : ([fillSym] ++ List.replicate gap fillSym) = List.replicate (gap + 1) fillSym := by
    show fillSym :: List.replicate gap fillSym = List.replicate (gap + 1) fillSym
    rw [List.replicate_succ]
  rw [List.append_assoc (right.take head) [fillSym], h_rep]

/-- Set-form variant of `fillPrefix_succ`, used in the run-lemma's
recursive case where we work with `right.set head fillSym` for
positional facts. -/
theorem fillPrefix_set_succ (right : List Nat) (head gap fillSym : Nat)
    (h_head : head < right.length) :
    fillPrefix (right.set head fillSym) (head + 1) gap fillSym =
    fillPrefix right head (gap + 1) fillSym := by
  rw [List.set_eq_take_append_cons_drop, if_pos h_head]
  exact fillPrefix_succ right head gap fillSym h_head

/-- Length of `fillPrefix` equals length of the original tape when
`head + gap ≤ right.length`. -/
theorem fillPrefix_length (right : List Nat) (head gap fillSym : Nat)
    (h_in_range : head + gap ≤ right.length) :
    (fillPrefix right head gap fillSym).length = right.length := by
  show (right.take head ++ List.replicate gap fillSym ++ right.drop (head + gap)).length =
    right.length
  rw [List.length_append, List.length_append, List.length_replicate, List.length_take,
      List.length_drop]
  have h_head_le : head ≤ right.length := Nat.le_trans (Nat.le_add_right head gap) h_in_range
  rw [Nat.min_eq_left h_head_le]
  -- head + gap + (right.length - (head + gap)) = right.length
  exact Nat.add_sub_cancel' h_in_range

/-- Main operational correctness for `clearRegionTM`. By induction on
`gap`. -/
theorem clearRegionTM_run_found
    (sig fillSym endMarker : Nat) (left right : List Nat) :
    ∀ (gap head : Nat) (h_in_range : head + gap < right.length),
      right.get ⟨head + gap, h_in_range⟩ = endMarker →
      (∀ k, k < gap → ∃ (h : head + k < right.length),
        right.get ⟨head + k, h⟩ < sig ∧
          right.get ⟨head + k, h⟩ ≠ endMarker) →
      runFlatTM (gap + 1) (clearRegionTM sig fillSym endMarker)
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 1
               tapes := [(left, head + gap, fillPrefix right head gap fillSym)] }
  | 0, head, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨head, h_lt⟩ = endMarker := by
        have heq : (⟨head + 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero head)
        rw [heq] at h_get_target
        exact h_get_target
      rw [runFlatTM_clearRegion_state0_unfold sig fillSym endMarker 0 _ _
        (clearRegionTM_step_match sig fillSym endMarker left right head h_lt h_get)]
      -- runFlatTM 0 .. = some same_cfg
      show (some { state_idx := 1, tapes := [(left, head, right)] } : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head + 0, fillPrefix right head 0 fillSym)] }
      rw [Nat.add_zero, fillPrefix_zero_of_le right head fillSym (Nat.le_of_lt h_lt)]
  | gap + 1, head, h_in_range, h_get_target, h_before => by
      -- First step: write fillSym at head, advance to head+1.
      have h_head_lt : head < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right head (gap + 1)) h_in_range
      rcases h_before 0 (Nat.zero_lt_succ _) with ⟨h_kk, h_sym_lt, h_sym_ne⟩
      have heq0 : (⟨head + 0, h_kk⟩ : Fin right.length) = ⟨head, h_head_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero head)
      have h_get_head : right.get ⟨head, h_head_lt⟩ < sig := by
        rw [heq0] at h_sym_lt; exact h_sym_lt
      have h_get_head_ne : right.get ⟨head, h_head_lt⟩ ≠ endMarker := by
        rw [heq0] at h_sym_ne; exact h_sym_ne
      -- The post-step tape, in two equivalent forms:
      --   take/cons/drop  (what step_advance returns)
      --   right.set head fillSym  (cleaner for positional facts)
      have h_bridge :
          right.take head ++ fillSym :: right.drop (head + 1) =
          right.set head fillSym := by
        rw [List.set_eq_take_append_cons_drop, if_pos h_head_lt]
      have h_setlen : (right.set head fillSym).length = right.length := List.length_set
      -- New in-range / target / non-target conditions, lifted via getElem_set_ne.
      have h_succ : (head + 1) + gap = head + (gap + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 gap]
      have h_in_range_orig : (head + 1) + gap < right.length := by
        rw [h_succ]; exact h_in_range
      have h_in_range_set : (head + 1) + gap < (right.set head fillSym).length := by
        rw [h_setlen]; exact h_in_range_orig
      have h_pos_ne : head ≠ (head + 1) + gap := by omega
      have h_get_target' :
          (right.set head fillSym).get ⟨(head + 1) + gap, h_in_range_set⟩ = endMarker := by
        show (right.set head fillSym)[(head + 1) + gap]'h_in_range_set = endMarker
        rw [List.getElem_set_ne h_pos_ne]
        -- Now goal: right[(head + 1) + gap]'? = endMarker
        have heq : (⟨(head + 1) + gap, h_in_range_orig⟩ : Fin right.length) =
            ⟨head + (gap + 1), h_in_range⟩ := Fin.eq_of_val_eq h_succ
        show right.get ⟨(head + 1) + gap, h_in_range_orig⟩ = endMarker
        rw [heq]; exact h_get_target
      have h_before' :
          ∀ k, k < gap → ∃ (h : (head + 1) + k < (right.set head fillSym).length),
            (right.set head fillSym).get ⟨(head + 1) + k, h⟩ < sig ∧
              (right.set head fillSym).get ⟨(head + 1) + k, h⟩ ≠ endMarker := by
        intro k hk
        rcases h_before (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk, h1, h2⟩
        have hShift : head + (k + 1) = (head + 1) + k := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        have h_kk_orig : (head + 1) + k < right.length := hShift ▸ h_kk
        have h_kk_set : (head + 1) + k < (right.set head fillSym).length := h_setlen ▸ h_kk_orig
        have h_pos_ne_k : head ≠ (head + 1) + k := by omega
        have h_translate :
            (right.set head fillSym).get ⟨(head + 1) + k, h_kk_set⟩ =
              right.get ⟨(head + 1) + k, h_kk_orig⟩ := by
          show (right.set head fillSym)[(head + 1) + k]'h_kk_set =
                right[(head + 1) + k]'h_kk_orig
          rw [List.getElem_set_ne h_pos_ne_k]
        refine ⟨h_kk_set, ?_, ?_⟩
        · rw [h_translate]
          have heq : (⟨(head + 1) + k, h_kk_orig⟩ : Fin right.length) =
              ⟨head + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
          rw [heq]; exact h1
        · rw [h_translate]
          have heq : (⟨(head + 1) + k, h_kk_orig⟩ : Fin right.length) =
              ⟨head + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
          rw [heq]; exact h2
      have hih :=
        clearRegionTM_run_found sig fillSym endMarker left (right.set head fillSym)
          gap (head + 1) h_in_range_set h_get_target' h_before'
      -- Unfold the first step (returns take/cons/drop form).
      rw [runFlatTM_clearRegion_state0_unfold sig fillSym endMarker (gap + 1) _ _
        (clearRegionTM_step_advance sig fillSym endMarker left right head h_head_lt
          h_get_head h_get_head_ne)]
      -- Convert the take/cons/drop form to set form via h_bridge so IH applies.
      rw [h_bridge]
      -- Apply IH.
      rw [hih]
      -- Result: some { tapes := [(left, (head+1)+gap, fillPrefix (right.set head fillSym) (head+1) gap fillSym)] }
      -- Want:    some { tapes := [(left, head+(gap+1), fillPrefix right head (gap+1) fillSym)] }
      rw [h_succ, fillPrefix_set_succ right head gap fillSym h_head_lt]
  termination_by gap _ _ _ _ => gap


end Primitives
end EvalCnfTM