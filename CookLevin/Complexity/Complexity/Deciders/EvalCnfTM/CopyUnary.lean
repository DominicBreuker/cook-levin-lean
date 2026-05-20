import Complexity.Complexity.Deciders.EvalCnfTM.Primitives

set_option autoImplicit false

namespace EvalCnfTM
namespace Primitives

open TMPrimitives (currentTapeSymbol_in_range currentTapeSymbol_out_of_range)

/-! ## `copyUnaryTM` — copy a unary number from source to var-buffer

A 7-state single-tape TM that copies a run of `1`s from a "source" region
in the CNF input to the var-buffer (the `[7, …, 8]` scratch region).
Uses a transient source-cursor marker (alphabet symbol `11`) to track
source position across shuttle iterations between source and var-buffer.

### Semantics

- Caller positions head at the first `1` of source unary run.
- Source: `1^v <terminator>` where `terminator ∈ {2, 3, 4}` (literal
  sign or clause terminator).
- Var-buffer: a contiguous run of `0`s, preceded by marker `7` (which
  is somewhere to the right of source) and followed by marker `8`.
- `copyUnaryTM` consumes source `1`s (writing `0`s over them) and
  writes `1`s into the first `v` var-buffer positions. Halts in state
  `6` with head at the source terminator.

### State machine (7 states)

- **0** (entry / re-entry): check current source cell.
  - On `1`: write `11` (cursor), Nmove, → state 1.
  - On `v ≠ 1, v < sig`: write `none`, Nmove, → state 6 (halt).
- **1** (scan right to marker 7):
  - On `7`: write `none`, Rmove, → state 2 (advance past marker).
  - On `v ≠ 7`: write `none`, Rmove, → state 1.
- **2** (find first `0` in var-buffer):
  - On `0`: write `1`, Nmove, → state 3.
  - On `1`: write `none`, Rmove, → state 2 (skip already-written cell).
- **3** (scan left to marker 7):
  - On `7`: write `none`, Lmove, → state 4 (step past marker).
  - On `v ≠ 7`: write `none`, Lmove, → state 3.
- **4** (scan left to cursor 11):
  - On `11`: write `none`, Nmove, → state 5.
  - On `v ≠ 11`: write `none`, Lmove, → state 4.
- **5** (consume cursor, advance):
  - On `11`: write `0`, Rmove, → state 0.
- **6**: halt.

Total entries: `4 * sig + 4` (= 52 entries for `sig = 12`).

The full operational correctness lemma `copyUnaryTM_run_found` is
deferred to **Step 11.3b** (next session). This section lands the TM
definition, validity, and per-state step lemmas. -/

/-! ### Transition entries -/

private def copyUnary_s0_continue : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some 1]
    dst_state := 1
    dst_write_vals := [some 11]
    move_dirs := [TMMove.Nmove] }

private def copyUnary_s0_halt (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 6
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def copyUnary_s1_halt : FlatTMTransEntry :=
  { src_state := 1
    src_tape_vals := [some 7]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def copyUnary_s1_continue (v : Nat) : FlatTMTransEntry :=
  { src_state := 1
    src_tape_vals := [some v]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def copyUnary_s2_halt : FlatTMTransEntry :=
  { src_state := 2
    src_tape_vals := [some 0]
    dst_state := 3
    dst_write_vals := [some 1]
    move_dirs := [TMMove.Nmove] }

private def copyUnary_s2_continue : FlatTMTransEntry :=
  { src_state := 2
    src_tape_vals := [some 1]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def copyUnary_s3_halt : FlatTMTransEntry :=
  { src_state := 3
    src_tape_vals := [some 7]
    dst_state := 4
    dst_write_vals := [none]
    move_dirs := [TMMove.Lmove] }

private def copyUnary_s3_continue (v : Nat) : FlatTMTransEntry :=
  { src_state := 3
    src_tape_vals := [some v]
    dst_state := 3
    dst_write_vals := [none]
    move_dirs := [TMMove.Lmove] }

private def copyUnary_s4_halt : FlatTMTransEntry :=
  { src_state := 4
    src_tape_vals := [some 11]
    dst_state := 5
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def copyUnary_s4_continue (v : Nat) : FlatTMTransEntry :=
  { src_state := 4
    src_tape_vals := [some v]
    dst_state := 4
    dst_write_vals := [none]
    move_dirs := [TMMove.Lmove] }

private def copyUnary_s5_advance : FlatTMTransEntry :=
  { src_state := 5
    src_tape_vals := [some 11]
    dst_state := 0
    dst_write_vals := [some 0]
    move_dirs := [TMMove.Rmove] }

/-! ### TM definition -/

/-- Transition table for `copyUnaryTM`, organised in six per-state
blocks. Explicit right-associative parens so that `List.mem_append`
decomposes the membership proof level-by-level (block 0 first,
remainder, …). -/
def copyUnaryTM_trans (sig : Nat) : List FlatTMTransEntry :=
  -- Block 0: state-0 transitions.
  (copyUnary_s0_continue ::
    ((List.range sig).filter (fun v => decide (v ≠ 1))).map copyUnary_s0_halt)
  ++
  ((-- Block 1: state-1 transitions.
    copyUnary_s1_halt ::
      ((List.range sig).filter (fun v => decide (v ≠ 7))).map copyUnary_s1_continue)
   ++
   ((-- Block 2: state-2 transitions (two entries).
     [copyUnary_s2_halt, copyUnary_s2_continue])
    ++
    ((-- Block 3: state-3 transitions.
      copyUnary_s3_halt ::
        ((List.range sig).filter (fun v => decide (v ≠ 7))).map copyUnary_s3_continue)
     ++
     ((-- Block 4: state-4 transitions.
       copyUnary_s4_halt ::
         ((List.range sig).filter (fun v => decide (v ≠ 11))).map copyUnary_s4_continue)
      ++
      -- Block 5: state-5 transition (one entry).
      [copyUnary_s5_advance]))))

/-- The copy-unary TM. Caller obligation: `sig ≥ 12` so the cursor
marker `11` and all other write values are in range. -/
def copyUnaryTM (sig : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 7
  trans := copyUnaryTM_trans sig
  start := 0
  halt := [false, false, false, false, false, false, true]

/-! ### Validity -/

theorem copyUnaryTM_valid (sig : Nat) (h_sig : 12 ≤ sig) :
    validFlatTM (copyUnaryTM sig) := by
  have h_0 : (0 : Nat) < sig := Nat.lt_of_lt_of_le (by decide) h_sig
  have h_1 : (1 : Nat) < sig := Nat.lt_of_lt_of_le (by decide) h_sig
  have h_7 : (7 : Nat) < sig := Nat.lt_of_lt_of_le (by decide) h_sig
  have h_11 : (11 : Nat) < sig := Nat.lt_of_lt_of_le (by decide) h_sig
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 7; decide
  · show [false, false, false, false, false, false, true].length = 7; rfl
  · intro entry hentry
    have hentry' : entry ∈ copyUnaryTM_trans sig := hentry
    unfold copyUnaryTM_trans at hentry'
    -- Decompose the chain of `++`s level-by-level (++ is right-assoc).
    -- hentry' : entry ∈ block0 ++ (block1 ++ ([s2_halt, s2_continue] ++ (block3 ++ (block4 ++ [s5_advance]))))
    rcases List.mem_append.mp hentry' with h0 | h_r1
    · -- Block 0: state 0.
      rcases List.mem_cons.mp h0 with h0_cont | h0_halt
      · -- s0_continue
        subst h0_cont
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 7; decide
        · show 1 < 7; decide
        · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_1
        · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_11
      · rcases List.mem_map.mp h0_halt with ⟨v, hv, hmk⟩
        subst hmk
        have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
        have hvlt : v < sig := List.mem_range.mp hv'
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 7; decide
        · show 6 < 7; decide
        · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hvlt
        · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
    · rcases List.mem_append.mp h_r1 with h1 | h_r2
      · -- Block 1: state 1.
        rcases List.mem_cons.mp h1 with h1_halt | h1_cont
        · subst h1_halt
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · show 1 < 7; decide
          · show 2 < 7; decide
          · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_7
          · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
        · rcases List.mem_map.mp h1_cont with ⟨v, hv, hmk⟩
          subst hmk
          have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
          have hvlt : v < sig := List.mem_range.mp hv'
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · show 1 < 7; decide
          · show 1 < 7; decide
          · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hvlt
          · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
      · rcases List.mem_append.mp h_r2 with h2 | h_r3
        · -- Block 2: state 2.
          rcases List.mem_cons.mp h2 with h2_halt | h2_rest
          · subst h2_halt
            refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
            · show 2 < 7; decide
            · show 3 < 7; decide
            · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_0
            · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_1
          · rcases List.mem_cons.mp h2_rest with h2_cont | h2_nil
            · subst h2_cont
              refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · show 2 < 7; decide
              · show 2 < 7; decide
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_1
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
            · cases h2_nil
        · rcases List.mem_append.mp h_r3 with h3 | h_r4
          · -- Block 3: state 3.
            rcases List.mem_cons.mp h3 with h3_halt | h3_cont
            · subst h3_halt
              refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · show 3 < 7; decide
              · show 4 < 7; decide
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_7
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
            · rcases List.mem_map.mp h3_cont with ⟨v, hv, hmk⟩
              subst hmk
              have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
              have hvlt : v < sig := List.mem_range.mp hv'
              refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · show 3 < 7; decide
              · show 3 < 7; decide
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hvlt
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
          · rcases List.mem_append.mp h_r4 with h4 | h5
            · -- Block 4: state 4.
              rcases List.mem_cons.mp h4 with h4_halt | h4_cont
              · subst h4_halt
                refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                · show 4 < 7; decide
                · show 5 < 7; decide
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_11
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
              · rcases List.mem_map.mp h4_cont with ⟨v, hv, hmk⟩
                subst hmk
                have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
                have hvlt : v < sig := List.mem_range.mp hv'
                refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                · show 4 < 7; decide
                · show 4 < 7; decide
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hvlt
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
            · -- Block 5: state 5.
              rcases List.mem_cons.mp h5 with h5_adv | h5_nil
              · subst h5_adv
                refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                · show 5 < 7; decide
                · show 0 < 7; decide
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_11
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_0
              · cases h5_nil

/-! ### Step helpers -/

/-- `entryMatchesConfig` is false whenever the entry's `src_state`
differs from the configuration's `state_idx`. Mirrors the corresponding
helper in `TMPrimitives` namespace (which is private there). -/
private theorem copyUnary_entryMatchesConfig_state_ne_false
    {entry : FlatTMTransEntry} {cfg : FlatTMConfig}
    (h : entry.src_state ≠ cfg.state_idx) :
    entryMatchesConfig entry cfg = false := by
  by_contra hcontra
  apply h
  have hmatch : entryMatchesConfig entry cfg = true := by
    cases h_eq : entryMatchesConfig entry cfg with
    | true => rfl
    | false => exact absurd h_eq hcontra
  unfold entryMatchesConfig at hmatch
  rw [Bool.and_eq_true] at hmatch
  exact LawfulBEq.eq_of_beq hmatch.1

/-- If every entry in `block` has a `src_state` different from
`cfg.state_idx`, then `find?` on `block` returns `none`. -/
private theorem copyUnary_find_none_of_all_state_ne
    (block : List FlatTMTransEntry) (cfg : FlatTMConfig)
    (h_all : ∀ e ∈ block, e.src_state ≠ cfg.state_idx) :
    block.find? (fun e => entryMatchesConfig e cfg) = none := by
  rw [List.find?_eq_none]
  intro e he hmatch
  apply h_all e he
  unfold entryMatchesConfig at hmatch
  rw [Bool.and_eq_true] at hmatch
  exact LawfulBEq.eq_of_beq hmatch.1

/-! ### Per-block source-state lemmas -/

/-- Every entry in block 0 has `src_state = 0`. -/
private theorem copyUnary_block_0_src_state (sig : Nat) (e : FlatTMTransEntry)
    (he : e ∈ (copyUnary_s0_continue ::
        ((List.range sig).filter (fun v => decide (v ≠ 1))).map copyUnary_s0_halt)) :
    e.src_state = 0 := by
  rcases List.mem_cons.mp he with h_cont | h_halt
  · subst h_cont; rfl
  · rcases List.mem_map.mp h_halt with ⟨_, _, hv⟩
    subst hv; rfl

/-- Every entry in block 1 has `src_state = 1`. -/
private theorem copyUnary_block_1_src_state (sig : Nat) (e : FlatTMTransEntry)
    (he : e ∈ (copyUnary_s1_halt ::
        ((List.range sig).filter (fun v => decide (v ≠ 7))).map copyUnary_s1_continue)) :
    e.src_state = 1 := by
  rcases List.mem_cons.mp he with h_halt | h_cont
  · subst h_halt; rfl
  · rcases List.mem_map.mp h_cont with ⟨_, _, hv⟩
    subst hv; rfl

/-- Every entry in block 2 has `src_state = 2`. -/
private theorem copyUnary_block_2_src_state (e : FlatTMTransEntry)
    (he : e ∈ ([copyUnary_s2_halt, copyUnary_s2_continue] : List FlatTMTransEntry)) :
    e.src_state = 2 := by
  rcases List.mem_cons.mp he with h_halt | h_rest
  · subst h_halt; rfl
  · rcases List.mem_cons.mp h_rest with h_cont | h_nil
    · subst h_cont; rfl
    · cases h_nil

/-- Every entry in block 3 has `src_state = 3`. -/
private theorem copyUnary_block_3_src_state (sig : Nat) (e : FlatTMTransEntry)
    (he : e ∈ (copyUnary_s3_halt ::
        ((List.range sig).filter (fun v => decide (v ≠ 7))).map copyUnary_s3_continue)) :
    e.src_state = 3 := by
  rcases List.mem_cons.mp he with h_halt | h_cont
  · subst h_halt; rfl
  · rcases List.mem_map.mp h_cont with ⟨_, _, hv⟩
    subst hv; rfl

/-- Every entry in block 4 has `src_state = 4`. -/
private theorem copyUnary_block_4_src_state (sig : Nat) (e : FlatTMTransEntry)
    (he : e ∈ (copyUnary_s4_halt ::
        ((List.range sig).filter (fun v => decide (v ≠ 11))).map copyUnary_s4_continue)) :
    e.src_state = 4 := by
  rcases List.mem_cons.mp he with h_halt | h_cont
  · subst h_halt; rfl
  · rcases List.mem_map.mp h_cont with ⟨_, _, hv⟩
    subst hv; rfl

/-- Every entry in block 5 has `src_state = 5`. -/
private theorem copyUnary_block_5_src_state (e : FlatTMTransEntry)
    (he : e ∈ ([copyUnary_s5_advance] : List FlatTMTransEntry)) :
    e.src_state = 5 := by
  rcases List.mem_cons.mp he with h_adv | h_nil
  · subst h_adv; rfl
  · cases h_nil

/-! ### Per-block `find? = none` lemmas

When `cfg.state_idx = N` we want to skip every other block during the
`find?` traversal. Each `block_i_find_none` says that block `i` returns
`none` whenever `cfg.state_idx ≠ i`. -/

private theorem copyUnary_block_0_find_none (sig : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 0) :
    (copyUnary_s0_continue ::
        ((List.range sig).filter (fun v => decide (v ≠ 1))).map copyUnary_s0_halt).find?
      (fun e => entryMatchesConfig e cfg) = none := by
  apply copyUnary_find_none_of_all_state_ne
  intro e he
  rw [copyUnary_block_0_src_state sig e he]
  exact fun heq => h heq.symm

private theorem copyUnary_block_1_find_none (sig : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 1) :
    (copyUnary_s1_halt ::
        ((List.range sig).filter (fun v => decide (v ≠ 7))).map copyUnary_s1_continue).find?
      (fun e => entryMatchesConfig e cfg) = none := by
  apply copyUnary_find_none_of_all_state_ne
  intro e he
  rw [copyUnary_block_1_src_state sig e he]
  exact fun heq => h heq.symm

private theorem copyUnary_block_2_find_none (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 2) :
    ([copyUnary_s2_halt, copyUnary_s2_continue] : List FlatTMTransEntry).find?
      (fun e => entryMatchesConfig e cfg) = none := by
  apply copyUnary_find_none_of_all_state_ne
  intro e he
  rw [copyUnary_block_2_src_state e he]
  exact fun heq => h heq.symm

private theorem copyUnary_block_3_find_none (sig : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 3) :
    (copyUnary_s3_halt ::
        ((List.range sig).filter (fun v => decide (v ≠ 7))).map copyUnary_s3_continue).find?
      (fun e => entryMatchesConfig e cfg) = none := by
  apply copyUnary_find_none_of_all_state_ne
  intro e he
  rw [copyUnary_block_3_src_state sig e he]
  exact fun heq => h heq.symm

private theorem copyUnary_block_4_find_none (sig : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 4) :
    (copyUnary_s4_halt ::
        ((List.range sig).filter (fun v => decide (v ≠ 11))).map copyUnary_s4_continue).find?
      (fun e => entryMatchesConfig e cfg) = none := by
  apply copyUnary_find_none_of_all_state_ne
  intro e he
  rw [copyUnary_block_4_src_state sig e he]
  exact fun heq => h heq.symm

/-! ### State-0 step lemmas

State 0 is the entry/re-entry point. The head is expected to be on
either a source `1` (continue copying) or a terminator `v ≠ 1`
(success-halt). -/

/-- State 0, on source `1`: write cursor `11`, no move, transition to
state 1. -/
theorem copyUnaryTM_state0_step_consume (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 1) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1
             tapes := [writeCurrentTapeSymbol (left, head, right) (some 11)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym0 : currentTapeSymbol (left, head, right) = some 1 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig copyUnary_s0_continue cfg = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 1] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym0]; rfl
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.cons_append, List.find?_cons, hMatch]
  rfl

/-- State 0, on a terminator `v ≠ 1` with `v < sig`: no write, no move,
halt in state 6. -/
theorem copyUnaryTM_state0_step_halt (sig : Nat) (left right : List Nat) (head v : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : v < sig)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 1) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 6, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym0 : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym0]
  have hNotMatchCont : entryMatchesConfig copyUnary_s0_continue cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some 1] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 1] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne']
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ 1)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, decide_eq_true h_ne⟩
  have hFindHalt :
      (((List.range sig).filter (fun w => decide (w ≠ 1))).map copyUnary_s0_halt).find?
          (fun e => entryMatchesConfig e cfg) =
        some (copyUnary_s0_halt v) := by
    refine find_singleSomeEntry_match cfg v _ copyUnary_s0_halt rfl hSymTape
      (fun _ => rfl) (fun _ => rfl) hvInFilter ?_
    intro w _ hwv
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact hwv h2
    simp [h_ne']
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.cons_append, List.find?_cons, hNotMatchCont,
      List.find?_append, hFindHalt]
  rfl

/-! ### State-1 step lemmas

State 1 scans right to marker 7. -/

theorem copyUnaryTM_state1_step_match (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 7) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 2
             tapes := [moveTapeHead (left, head, right) TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 1, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 7 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig copyUnary_s1_halt cfg = true := by
    show ((1 : Nat) == 1 &&
            decide (([some 7] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    copyUnary_block_0_find_none sig cfg (by show (1 : Nat) ≠ 0; decide)
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.cons_append, List.find?_cons, hMatch]
  rfl

theorem copyUnaryTM_state1_step_advance (sig : Nat) (left right : List Nat) (head v : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : v < sig)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 7) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 1
             tapes := [moveTapeHead (left, head, right) TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 1, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym]
  have hNotMatchHalt : entryMatchesConfig copyUnary_s1_halt cfg = false := by
    show ((1 : Nat) == cfg.state_idx &&
            decide (([some 7] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 7] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne']
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ 7)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, decide_eq_true h_ne⟩
  have hFindCont :
      (((List.range sig).filter (fun w => decide (w ≠ 7))).map copyUnary_s1_continue).find?
          (fun e => entryMatchesConfig e cfg) =
        some (copyUnary_s1_continue v) := by
    refine find_singleSomeEntry_match_state cfg 1 v _ copyUnary_s1_continue rfl hSymTape
      (fun _ => rfl) (fun _ => rfl) hvInFilter ?_
    intro w _ hwv
    show ((1 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact hwv h2
    simp [h_ne']
  have h_block_0_none :=
    copyUnary_block_0_find_none sig cfg (by show (1 : Nat) ≠ 0; decide)
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.cons_append, List.find?_cons, hNotMatchHalt,
      List.find?_append, hFindCont]
  rfl

/-! ### State-2 step lemmas

State 2 finds the first `0` in the var-buffer. -/

theorem copyUnaryTM_state2_step_zero (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 0) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 2, tapes := [(left, head, right)] } =
      some { state_idx := 3
             tapes := [writeCurrentTapeSymbol (left, head, right) (some 1)] } := by
  set cfg : FlatTMConfig := { state_idx := 2, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 0 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig copyUnary_s2_halt cfg = true := by
    show ((2 : Nat) == 2 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    copyUnary_block_0_find_none sig cfg (by show (2 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    copyUnary_block_1_find_none sig cfg (by show (2 : Nat) ≠ 1; decide)
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, List.find?_cons, hMatch]
  rfl

theorem copyUnaryTM_state2_step_one (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 1) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 2, tapes := [(left, head, right)] } =
      some { state_idx := 2
             tapes := [moveTapeHead (left, head, right) TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 2, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 1 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some 1] := by
    show [currentTapeSymbol (left, head, right)] = [some 1]; rw [hSym]
  -- s2_halt is `[some 0]` which doesn't match symbol 1.
  have hNotMatchHalt : entryMatchesConfig copyUnary_s2_halt cfg = false := by
    show ((2 : Nat) == cfg.state_idx &&
            decide (([some 0] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 0] : List (Option Nat)) ≠ [some 1] := by
      intro h; injection h with h1 _; injection h1 with h2; exact (by decide : (0 : Nat) ≠ 1) h2
    simp [h_ne']
  have hMatchCont : entryMatchesConfig copyUnary_s2_continue cfg = true := by
    show ((2 : Nat) == 2 &&
            decide (([some 1] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = true
    rw [hSymTape]; rfl
  have h_block_0_none :=
    copyUnary_block_0_find_none sig cfg (by show (2 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    copyUnary_block_1_find_none sig cfg (by show (2 : Nat) ≠ 1; decide)
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, List.find?_cons, hNotMatchHalt,
      List.find?_cons, hMatchCont]
  rfl

/-! ### State-3 step lemmas

State 3 scans left to marker 7 (mirror of state 1). -/

theorem copyUnaryTM_state3_step_match (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 7) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 3, tapes := [(left, head, right)] } =
      some { state_idx := 4
             tapes := [moveTapeHead (left, head, right) TMMove.Lmove] } := by
  set cfg : FlatTMConfig := { state_idx := 3, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 7 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig copyUnary_s3_halt cfg = true := by
    show ((3 : Nat) == 3 &&
            decide (([some 7] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    copyUnary_block_0_find_none sig cfg (by show (3 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    copyUnary_block_1_find_none sig cfg (by show (3 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    copyUnary_block_2_find_none cfg (by show (3 : Nat) ≠ 2; decide)
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.cons_append, List.find?_cons, hMatch]
  rfl

theorem copyUnaryTM_state3_step_advance (sig : Nat) (left right : List Nat) (head v : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : v < sig)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 7) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 3, tapes := [(left, head, right)] } =
      some { state_idx := 3
             tapes := [moveTapeHead (left, head, right) TMMove.Lmove] } := by
  set cfg : FlatTMConfig := { state_idx := 3, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym]
  have hNotMatchHalt : entryMatchesConfig copyUnary_s3_halt cfg = false := by
    show ((3 : Nat) == cfg.state_idx &&
            decide (([some 7] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 7] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne']
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ 7)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, decide_eq_true h_ne⟩
  have hFindCont :
      (((List.range sig).filter (fun w => decide (w ≠ 7))).map copyUnary_s3_continue).find?
          (fun e => entryMatchesConfig e cfg) =
        some (copyUnary_s3_continue v) := by
    refine find_singleSomeEntry_match_state cfg 3 v _ copyUnary_s3_continue rfl hSymTape
      (fun _ => rfl) (fun _ => rfl) hvInFilter ?_
    intro w _ hwv
    show ((3 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact hwv h2
    simp [h_ne']
  have h_block_0_none :=
    copyUnary_block_0_find_none sig cfg (by show (3 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    copyUnary_block_1_find_none sig cfg (by show (3 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    copyUnary_block_2_find_none cfg (by show (3 : Nat) ≠ 2; decide)
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.cons_append, List.find?_cons, hNotMatchHalt,
      List.find?_append, hFindCont]
  rfl

/-! ### State-4 step lemmas

State 4 scans left to cursor 11. -/

theorem copyUnaryTM_state4_step_match (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 11) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 4, tapes := [(left, head, right)] } =
      some { state_idx := 5, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 4, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 11 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig copyUnary_s4_halt cfg = true := by
    show ((4 : Nat) == 4 &&
            decide (([some 11] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    copyUnary_block_0_find_none sig cfg (by show (4 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    copyUnary_block_1_find_none sig cfg (by show (4 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    copyUnary_block_2_find_none cfg (by show (4 : Nat) ≠ 2; decide)
  have h_block_3_none :=
    copyUnary_block_3_find_none sig cfg (by show (4 : Nat) ≠ 3; decide)
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.find?_append, h_block_3_none, Option.none_or,
      List.cons_append, List.find?_cons, hMatch]
  rfl

theorem copyUnaryTM_state4_step_advance (sig : Nat) (left right : List Nat) (head v : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : v < sig)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 11) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 4, tapes := [(left, head, right)] } =
      some { state_idx := 4
             tapes := [moveTapeHead (left, head, right) TMMove.Lmove] } := by
  set cfg : FlatTMConfig := { state_idx := 4, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym]
  have hNotMatchHalt : entryMatchesConfig copyUnary_s4_halt cfg = false := by
    show ((4 : Nat) == cfg.state_idx &&
            decide (([some 11] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 11] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne']
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ 11)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, decide_eq_true h_ne⟩
  have hFindCont :
      (((List.range sig).filter (fun w => decide (w ≠ 11))).map copyUnary_s4_continue).find?
          (fun e => entryMatchesConfig e cfg) =
        some (copyUnary_s4_continue v) := by
    refine find_singleSomeEntry_match_state cfg 4 v _ copyUnary_s4_continue rfl hSymTape
      (fun _ => rfl) (fun _ => rfl) hvInFilter ?_
    intro w _ hwv
    show ((4 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact hwv h2
    simp [h_ne']
  have h_block_0_none :=
    copyUnary_block_0_find_none sig cfg (by show (4 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    copyUnary_block_1_find_none sig cfg (by show (4 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    copyUnary_block_2_find_none cfg (by show (4 : Nat) ≠ 2; decide)
  have h_block_3_none :=
    copyUnary_block_3_find_none sig cfg (by show (4 : Nat) ≠ 3; decide)
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.find?_append, h_block_3_none, Option.none_or,
      List.cons_append, List.find?_cons, hNotMatchHalt,
      List.find?_append, hFindCont]
  rfl

/-! ### State-5 step lemma

State 5 consumes the cursor `11`, writes `0`, advances right, and
loops back to state 0. -/

theorem copyUnaryTM_state5_step_cursor (sig : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 11) :
    stepFlatTM (copyUnaryTM sig)
        { state_idx := 5, tapes := [(left, head, right)] } =
      some { state_idx := 0
             tapes := [moveTapeHead
               (writeCurrentTapeSymbol (left, head, right) (some 0))
               TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 5, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 11 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig copyUnary_s5_advance cfg = true := by
    show ((5 : Nat) == 5 &&
            decide (([some 11] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    copyUnary_block_0_find_none sig cfg (by show (5 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    copyUnary_block_1_find_none sig cfg (by show (5 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    copyUnary_block_2_find_none cfg (by show (5 : Nat) ≠ 2; decide)
  have h_block_3_none :=
    copyUnary_block_3_find_none sig cfg (by show (5 : Nat) ≠ 3; decide)
  have h_block_4_none :=
    copyUnary_block_4_find_none sig cfg (by show (5 : Nat) ≠ 4; decide)
  show Option.bind ((copyUnaryTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((copyUnaryTM_trans sig).find? _) _ = _
  unfold copyUnaryTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.find?_append, h_block_3_none, Option.none_or,
      List.find?_append, h_block_4_none, Option.none_or,
      List.find?_cons, hMatch]
  rfl

/-! ### Halting state lemmas -/

theorem copyUnaryTM_state0_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (copyUnaryTM sig)
        { state_idx := 0, tapes := cfg_tapes } = false := rfl

theorem copyUnaryTM_state1_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (copyUnaryTM sig)
        { state_idx := 1, tapes := cfg_tapes } = false := rfl

theorem copyUnaryTM_state2_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (copyUnaryTM sig)
        { state_idx := 2, tapes := cfg_tapes } = false := rfl

theorem copyUnaryTM_state3_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (copyUnaryTM sig)
        { state_idx := 3, tapes := cfg_tapes } = false := rfl

theorem copyUnaryTM_state4_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (copyUnaryTM sig)
        { state_idx := 4, tapes := cfg_tapes } = false := rfl

theorem copyUnaryTM_state5_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (copyUnaryTM sig)
        { state_idx := 5, tapes := cfg_tapes } = false := rfl

/-- State 6 of `copyUnaryTM` is the halt state. -/
theorem copyUnaryTM_state6_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (copyUnaryTM sig)
        { state_idx := 6, tapes := cfg_tapes } = true := rfl

/-! ### Per-state `runFlatTM` unfold helpers

For each non-halting state `s`, the helper says: if a step from
`(state s, tapes)` produces `cfg'`, then running `n + 1` steps starting
from that state equals running `n` steps from `cfg'`. This is the
mechanism used to chain step lemmas into a multi-step run, in the
style of `runFlatTM_scanLeft_state0_unfold`. -/

private theorem runFlatTM_copyUnary_state0_unfold
    (sig n : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (copyUnaryTM sig)
        { state_idx := 0, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (copyUnaryTM sig)
        { state_idx := 0, tapes := tapes } =
      runFlatTM n (copyUnaryTM sig) cfg' := by
  show (if haltingStateReached (copyUnaryTM sig)
            { state_idx := 0, tapes := tapes } = true then
          some { state_idx := 0, tapes := tapes }
        else
          match stepFlatTM (copyUnaryTM sig)
              { state_idx := 0, tapes := tapes } with
          | none => some { state_idx := 0, tapes := tapes }
          | some cfg' => runFlatTM n (copyUnaryTM sig) cfg') =
    runFlatTM n (copyUnaryTM sig) cfg'
  rw [copyUnaryTM_state0_not_halting, h_step]
  rfl

private theorem runFlatTM_copyUnary_state1_unfold
    (sig n : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (copyUnaryTM sig)
        { state_idx := 1, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (copyUnaryTM sig)
        { state_idx := 1, tapes := tapes } =
      runFlatTM n (copyUnaryTM sig) cfg' := by
  show (if haltingStateReached (copyUnaryTM sig)
            { state_idx := 1, tapes := tapes } = true then
          some { state_idx := 1, tapes := tapes }
        else
          match stepFlatTM (copyUnaryTM sig)
              { state_idx := 1, tapes := tapes } with
          | none => some { state_idx := 1, tapes := tapes }
          | some cfg' => runFlatTM n (copyUnaryTM sig) cfg') =
    runFlatTM n (copyUnaryTM sig) cfg'
  rw [copyUnaryTM_state1_not_halting, h_step]
  rfl

private theorem runFlatTM_copyUnary_state2_unfold
    (sig n : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (copyUnaryTM sig)
        { state_idx := 2, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (copyUnaryTM sig)
        { state_idx := 2, tapes := tapes } =
      runFlatTM n (copyUnaryTM sig) cfg' := by
  show (if haltingStateReached (copyUnaryTM sig)
            { state_idx := 2, tapes := tapes } = true then
          some { state_idx := 2, tapes := tapes }
        else
          match stepFlatTM (copyUnaryTM sig)
              { state_idx := 2, tapes := tapes } with
          | none => some { state_idx := 2, tapes := tapes }
          | some cfg' => runFlatTM n (copyUnaryTM sig) cfg') =
    runFlatTM n (copyUnaryTM sig) cfg'
  rw [copyUnaryTM_state2_not_halting, h_step]
  rfl

private theorem runFlatTM_copyUnary_state3_unfold
    (sig n : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (copyUnaryTM sig)
        { state_idx := 3, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (copyUnaryTM sig)
        { state_idx := 3, tapes := tapes } =
      runFlatTM n (copyUnaryTM sig) cfg' := by
  show (if haltingStateReached (copyUnaryTM sig)
            { state_idx := 3, tapes := tapes } = true then
          some { state_idx := 3, tapes := tapes }
        else
          match stepFlatTM (copyUnaryTM sig)
              { state_idx := 3, tapes := tapes } with
          | none => some { state_idx := 3, tapes := tapes }
          | some cfg' => runFlatTM n (copyUnaryTM sig) cfg') =
    runFlatTM n (copyUnaryTM sig) cfg'
  rw [copyUnaryTM_state3_not_halting, h_step]
  rfl

private theorem runFlatTM_copyUnary_state4_unfold
    (sig n : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (copyUnaryTM sig)
        { state_idx := 4, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (copyUnaryTM sig)
        { state_idx := 4, tapes := tapes } =
      runFlatTM n (copyUnaryTM sig) cfg' := by
  show (if haltingStateReached (copyUnaryTM sig)
            { state_idx := 4, tapes := tapes } = true then
          some { state_idx := 4, tapes := tapes }
        else
          match stepFlatTM (copyUnaryTM sig)
              { state_idx := 4, tapes := tapes } with
          | none => some { state_idx := 4, tapes := tapes }
          | some cfg' => runFlatTM n (copyUnaryTM sig) cfg') =
    runFlatTM n (copyUnaryTM sig) cfg'
  rw [copyUnaryTM_state4_not_halting, h_step]
  rfl

private theorem runFlatTM_copyUnary_state5_unfold
    (sig n : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (copyUnaryTM sig)
        { state_idx := 5, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (copyUnaryTM sig)
        { state_idx := 5, tapes := tapes } =
      runFlatTM n (copyUnaryTM sig) cfg' := by
  show (if haltingStateReached (copyUnaryTM sig)
            { state_idx := 5, tapes := tapes } = true then
          some { state_idx := 5, tapes := tapes }
        else
          match stepFlatTM (copyUnaryTM sig)
              { state_idx := 5, tapes := tapes } with
          | none => some { state_idx := 5, tapes := tapes }
          | some cfg' => runFlatTM n (copyUnaryTM sig) cfg') =
    runFlatTM n (copyUnaryTM sig) cfg'
  rw [copyUnaryTM_state5_not_halting, h_step]
  rfl

/-! ### Phase scan lemmas

Each scan phase of `copyUnaryTM` (states 1, 2, 3, 4) is a uniform
"advance until match" loop. We state each as a self-contained `_run`
lemma by induction on the scan distance (gap). -/

/-- **Phase 1**: state-1 scans right looking for marker `7`. From
`(state 1, head = p, right)` with `right.get ⟨p + gap, _⟩ = 7` and all
intermediate cells `< sig` and `≠ 7`, in `gap + 1` steps we reach
`(state 2, head = p + gap + 1, right)`. -/
theorem copyUnaryTM_state1_phase_run
    (sig : Nat) (left right : List Nat) :
    ∀ (gap p : Nat) (h_in_range : p + gap < right.length),
      right.get ⟨p + gap, h_in_range⟩ = 7 →
      (∀ k, k < gap → ∃ (h_lt : p + k < right.length),
          right.get ⟨p + k, h_lt⟩ < sig ∧
            right.get ⟨p + k, h_lt⟩ ≠ 7) →
      runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 1, tapes := [(left, p, right)] } =
        some { state_idx := 2, tapes := [(left, p + gap + 1, right)] }
  | 0, p, h_in_range, h_marker, _ => by
      have h_lt : p < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨p, h_lt⟩ = 7 := by
        have heq : (⟨p + 0, h_in_range⟩ : Fin right.length) = ⟨p, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero p)
        rw [heq] at h_marker; exact h_marker
      rw [runFlatTM_copyUnary_state1_unfold sig 0 _ _
        (copyUnaryTM_state1_step_match sig left right p h_lt h_get)]
      show (some { state_idx := 2, tapes := [moveTapeHead (left, p, right) TMMove.Rmove] }
              : Option FlatTMConfig) =
        some { state_idx := 2, tapes := [(left, p + 0 + 1, right)] }
      show (some { state_idx := 2, tapes := [(left, p + 1, right)] } : Option FlatTMConfig) =
        some { state_idx := 2, tapes := [(left, p + 0 + 1, right)] }
      rw [Nat.add_zero]
  | gap + 1, p, h_in_range, h_marker, h_mid => by
      have h_p_lt : p < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right p (gap + 1)) h_in_range
      rcases h_mid 0 (Nat.zero_lt_succ _) with ⟨h_p_lt', h_sym_lt, h_sym_ne⟩
      have heq0 : (⟨p + 0, h_p_lt'⟩ : Fin right.length) = ⟨p, h_p_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero p)
      have h_get_p : right.get ⟨p, h_p_lt⟩ < sig := by
        rw [heq0] at h_sym_lt; exact h_sym_lt
      have h_get_p_ne : right.get ⟨p, h_p_lt⟩ ≠ 7 := by
        rw [heq0] at h_sym_ne; exact h_sym_ne
      -- IH: starting from p+1 with gap, takes gap+1 steps to (state 2, p+1+gap+1).
      have h_in_range' : (p + 1) + gap < right.length := by
        rw [Nat.add_right_comm]; exact h_in_range
      have h_marker' : right.get ⟨(p + 1) + gap, h_in_range'⟩ = 7 := by
        have heq : (⟨(p + 1) + gap, h_in_range'⟩ : Fin right.length) =
            ⟨p + (gap + 1), h_in_range⟩ := by
          apply Fin.eq_of_val_eq
          show (p + 1) + gap = p + (gap + 1)
          rw [Nat.add_right_comm, Nat.add_assoc]
        rw [heq]; exact h_marker
      have h_mid' : ∀ k, k < gap → ∃ (h_lt : (p + 1) + k < right.length),
          right.get ⟨(p + 1) + k, h_lt⟩ < sig ∧
            right.get ⟨(p + 1) + k, h_lt⟩ ≠ 7 := by
        intro k hk
        rcases h_mid (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk, h1, h2⟩
        have hShift : p + (k + 1) = (p + 1) + k := by
          rw [Nat.add_right_comm]; rfl
        have h_kk' : (p + 1) + k < right.length := hShift ▸ h_kk
        refine ⟨h_kk', ?_, ?_⟩
        · have heq : (⟨(p + 1) + k, h_kk'⟩ : Fin right.length) =
              ⟨p + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
          rw [heq]; exact h1
        · have heq : (⟨(p + 1) + k, h_kk'⟩ : Fin right.length) =
              ⟨p + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
          rw [heq]; exact h2
      have hih := copyUnaryTM_state1_phase_run sig left right gap (p + 1)
        h_in_range' h_marker' h_mid'
      rw [runFlatTM_copyUnary_state1_unfold sig (gap + 1) _ _
        (copyUnaryTM_state1_step_advance sig left right p
          (right.get ⟨p, h_p_lt⟩) h_p_lt h_get_p rfl h_get_p_ne)]
      show runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 1, tapes := [moveTapeHead (left, p, right) TMMove.Rmove] } = _
      show runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 1, tapes := [(left, p + 1, right)] } = _
      rw [hih]
      show (some { state_idx := 2, tapes := [(left, (p + 1) + gap + 1, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 2, tapes := [(left, p + (gap + 1) + 1, right)] }
      have h_eq : (p + 1) + gap + 1 = p + (gap + 1) + 1 := by
        rw [Nat.add_right_comm p 1 gap]; rfl
      rw [h_eq]
  termination_by gap _ _ _ _ => gap

/-- **Phase 2**: state-2 scans right skipping `1`s until the first `0`,
which it overwrites with `1`. From `(state 2, head = p, right)` with
`right.get ⟨p + gap, _⟩ = 0` and `right.get ⟨p + k, _⟩ = 1` for all
`k < gap`, in `gap + 1` steps we reach
`(state 3, head = p + gap, right.set (p + gap) 1)`. -/
theorem copyUnaryTM_state2_phase_run
    (sig : Nat) (left right : List Nat) :
    ∀ (gap p : Nat) (h_in_range : p + gap < right.length),
      right.get ⟨p + gap, h_in_range⟩ = 0 →
      (∀ k, k < gap → ∃ (h_lt : p + k < right.length),
          right.get ⟨p + k, h_lt⟩ = 1) →
      runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 2, tapes := [(left, p, right)] } =
        some { state_idx := 3
               tapes := [(left, p + gap,
                 right.take (p + gap) ++ (1 : Nat) :: right.drop (p + gap + 1))] }
  | 0, p, h_in_range, h_zero, _ => by
      have h_lt : p < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨p, h_lt⟩ = 0 := by
        have heq : (⟨p + 0, h_in_range⟩ : Fin right.length) = ⟨p, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero p)
        rw [heq] at h_zero; exact h_zero
      have h_write : writeCurrentTapeSymbol (left, p, right) (some 1) =
          (left, p, right.take p ++ (1 : Nat) :: right.drop (p + 1)) := by
        simp [writeCurrentTapeSymbol, h_lt]
      rw [runFlatTM_copyUnary_state2_unfold sig 0 _ _
        (copyUnaryTM_state2_step_zero sig left right p h_lt h_get)]
      show (some { state_idx := 3
                   tapes := [writeCurrentTapeSymbol (left, p, right) (some 1)] }
              : Option FlatTMConfig) =
        some { state_idx := 3
               tapes := [(left, p + 0,
                 right.take (p + 0) ++ (1 : Nat) :: right.drop (p + 0 + 1))] }
      rw [h_write]
      simp only [Nat.add_zero]
  | gap + 1, p, h_in_range, h_zero, h_mid => by
      have h_p_lt : p < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right p (gap + 1)) h_in_range
      rcases h_mid 0 (Nat.zero_lt_succ _) with ⟨h_p_lt', h_sym_one⟩
      have heq0 : (⟨p + 0, h_p_lt'⟩ : Fin right.length) = ⟨p, h_p_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero p)
      have h_get_p_one : right.get ⟨p, h_p_lt⟩ = 1 := by
        rw [heq0] at h_sym_one; exact h_sym_one
      have h_in_range' : (p + 1) + gap < right.length := by
        rw [Nat.add_right_comm]; exact h_in_range
      have h_zero' : right.get ⟨(p + 1) + gap, h_in_range'⟩ = 0 := by
        have heq : (⟨(p + 1) + gap, h_in_range'⟩ : Fin right.length) =
            ⟨p + (gap + 1), h_in_range⟩ := by
          apply Fin.eq_of_val_eq
          show (p + 1) + gap = p + (gap + 1)
          rw [Nat.add_right_comm, Nat.add_assoc]
        rw [heq]; exact h_zero
      have h_mid' : ∀ k, k < gap → ∃ (h_lt : (p + 1) + k < right.length),
          right.get ⟨(p + 1) + k, h_lt⟩ = 1 := by
        intro k hk
        rcases h_mid (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk, h1⟩
        have hShift : p + (k + 1) = (p + 1) + k := by
          rw [Nat.add_right_comm]; rfl
        have h_kk' : (p + 1) + k < right.length := hShift ▸ h_kk
        refine ⟨h_kk', ?_⟩
        have heq : (⟨(p + 1) + k, h_kk'⟩ : Fin right.length) =
            ⟨p + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
        rw [heq]; exact h1
      have hih := copyUnaryTM_state2_phase_run sig left right gap (p + 1)
        h_in_range' h_zero' h_mid'
      rw [runFlatTM_copyUnary_state2_unfold sig (gap + 1) _ _
        (copyUnaryTM_state2_step_one sig left right p h_p_lt h_get_p_one)]
      show runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 2, tapes := [moveTapeHead (left, p, right) TMMove.Rmove] } = _
      show runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 2, tapes := [(left, p + 1, right)] } = _
      rw [hih]
      show (some { state_idx := 3
                   tapes := [(left, (p + 1) + gap,
                     right.take ((p + 1) + gap) ++ (1 : Nat) ::
                       right.drop ((p + 1) + gap + 1))] }
              : Option FlatTMConfig) =
        some { state_idx := 3
               tapes := [(left, p + (gap + 1),
                 right.take (p + (gap + 1)) ++ (1 : Nat) ::
                   right.drop (p + (gap + 1) + 1))] }
      have h_eq : (p + 1) + gap = p + (gap + 1) := by
        rw [Nat.add_right_comm]; rfl
      rw [h_eq]
  termination_by gap _ _ _ _ => gap

/-- **Phase 3**: state-3 scans left looking for marker `7`. On match
the head moves one more cell *left* (because s3_halt uses `Lmove`).
From `(state 3, head, right)` with `right.get ⟨head - gap, _⟩ = 7` and
intermediate cells `< sig` and `≠ 7`, in `gap + 1` steps we reach
`(state 4, head = head' - gap - 1, right)`. -/
theorem copyUnaryTM_state3_phase_run
    (sig : Nat) (left right : List Nat) :
    ∀ (gap head : Nat) (h_gap_le : gap ≤ head)
      (h_head_lt : head < right.length)
      (h_in_range : head - gap < right.length),
      right.get ⟨head - gap, h_in_range⟩ = 7 →
      (∀ k, k < gap → ∃ (h : head - k < right.length),
        right.get ⟨head - k, h⟩ < sig ∧
          right.get ⟨head - k, h⟩ ≠ 7) →
      runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 3, tapes := [(left, head, right)] } =
        some { state_idx := 4, tapes := [(left, head - gap - 1, right)] }
  | 0, head, _, h_head_lt, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := h_head_lt
      have h_get : right.get ⟨head, h_lt⟩ = 7 := by
        have heq : (⟨head - 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.sub_zero head)
        rw [heq] at h_get_target; exact h_get_target
      rw [runFlatTM_copyUnary_state3_unfold sig 0 _ _
        (copyUnaryTM_state3_step_match sig left right head h_lt h_get)]
      show (some { state_idx := 4, tapes := [moveTapeHead (left, head, right) TMMove.Lmove] }
              : Option FlatTMConfig) =
        some { state_idx := 4, tapes := [(left, head - 0 - 1, right)] }
      show (some { state_idx := 4, tapes := [(left, head - 1, right)] } : Option FlatTMConfig) =
        some { state_idx := 4, tapes := [(left, head - 0 - 1, right)] }
      rw [Nat.sub_zero]
  | gap + 1, head, h_gap_le, h_head_lt, h_in_range, h_get_target, h_before => by
      have h_head_pos : head ≥ 1 := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_gap_le
      have h_head_lt' : head < right.length := h_head_lt
      rcases h_before 0 (Nat.zero_lt_succ _) with ⟨h_kk, h_sym_lt, h_sym_ne⟩
      have heq0 : (⟨head - 0, h_kk⟩ : Fin right.length) = ⟨head, h_head_lt'⟩ :=
        Fin.eq_of_val_eq (Nat.sub_zero head)
      have h_get_head : right.get ⟨head, h_head_lt'⟩ < sig := by
        rw [heq0] at h_sym_lt; exact h_sym_lt
      have h_get_head_ne : right.get ⟨head, h_head_lt'⟩ ≠ 7 := by
        rw [heq0] at h_sym_ne; exact h_sym_ne
      have h_new_head : head - 1 < right.length :=
        Nat.lt_of_le_of_lt (Nat.sub_le head 1) h_head_lt'
      have h_new_gap_le : gap ≤ head - 1 :=
        Nat.le_sub_of_add_le h_gap_le
      have h_sub_swap : (head - 1) - gap = head - (gap + 1) := by
        rw [Nat.sub_sub, Nat.add_comm 1 gap]
      have h_in_range' : (head - 1) - gap < right.length := by
        rw [h_sub_swap]; exact h_in_range
      have h_get_target' :
          right.get ⟨(head - 1) - gap, h_in_range'⟩ = 7 := by
        have heq : (⟨(head - 1) - gap, h_in_range'⟩ : Fin right.length) =
            ⟨head - (gap + 1), h_in_range⟩ := Fin.eq_of_val_eq h_sub_swap
        rw [heq]; exact h_get_target
      have h_before' :
          ∀ k, k < gap → ∃ (h : (head - 1) - k < right.length),
            right.get ⟨(head - 1) - k, h⟩ < sig ∧
              right.get ⟨(head - 1) - k, h⟩ ≠ 7 := by
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
      have hih := copyUnaryTM_state3_phase_run sig left right gap (head - 1)
        h_new_gap_le h_new_head h_in_range' h_get_target' h_before'
      rw [runFlatTM_copyUnary_state3_unfold sig (gap + 1) _ _
        (copyUnaryTM_state3_step_advance sig left right head
          (right.get ⟨head, h_head_lt'⟩) h_head_lt' h_get_head rfl h_get_head_ne)]
      show runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 3, tapes := [moveTapeHead (left, head, right) TMMove.Lmove] } = _
      show runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 3, tapes := [(left, head - 1, right)] } = _
      rw [hih]
      show (some { state_idx := 4, tapes := [(left, (head - 1) - gap - 1, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 4, tapes := [(left, head - (gap + 1) - 1, right)] }
      rw [h_sub_swap]
  termination_by gap _ _ _ _ _ _ => gap

/-- **Phase 4**: state-4 scans left looking for cursor `11`. On match
the head stays (s4_halt uses `Nmove`). From `(state 4, head, right)`
with `right.get ⟨head - gap, _⟩ = 11` and intermediate cells `< sig`
and `≠ 11`, in `gap + 1` steps we reach
`(state 5, head = head' - gap, right)`. -/
theorem copyUnaryTM_state4_phase_run
    (sig : Nat) (left right : List Nat) :
    ∀ (gap head : Nat) (h_gap_le : gap ≤ head)
      (h_head_lt : head < right.length)
      (h_in_range : head - gap < right.length),
      right.get ⟨head - gap, h_in_range⟩ = 11 →
      (∀ k, k < gap → ∃ (h : head - k < right.length),
        right.get ⟨head - k, h⟩ < sig ∧
          right.get ⟨head - k, h⟩ ≠ 11) →
      runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 4, tapes := [(left, head, right)] } =
        some { state_idx := 5, tapes := [(left, head - gap, right)] }
  | 0, head, _, h_head_lt, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := h_head_lt
      have h_get : right.get ⟨head, h_lt⟩ = 11 := by
        have heq : (⟨head - 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.sub_zero head)
        rw [heq] at h_get_target; exact h_get_target
      rw [runFlatTM_copyUnary_state4_unfold sig 0 _ _
        (copyUnaryTM_state4_step_match sig left right head h_lt h_get)]
      show (some { state_idx := 5, tapes := [(left, head, right)] } : Option FlatTMConfig) =
        some { state_idx := 5, tapes := [(left, head - 0, right)] }
      rw [Nat.sub_zero]
  | gap + 1, head, h_gap_le, h_head_lt, h_in_range, h_get_target, h_before => by
      have h_head_pos : head ≥ 1 := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_gap_le
      have h_head_lt' : head < right.length := h_head_lt
      rcases h_before 0 (Nat.zero_lt_succ _) with ⟨h_kk, h_sym_lt, h_sym_ne⟩
      have heq0 : (⟨head - 0, h_kk⟩ : Fin right.length) = ⟨head, h_head_lt'⟩ :=
        Fin.eq_of_val_eq (Nat.sub_zero head)
      have h_get_head : right.get ⟨head, h_head_lt'⟩ < sig := by
        rw [heq0] at h_sym_lt; exact h_sym_lt
      have h_get_head_ne : right.get ⟨head, h_head_lt'⟩ ≠ 11 := by
        rw [heq0] at h_sym_ne; exact h_sym_ne
      have h_new_head : head - 1 < right.length :=
        Nat.lt_of_le_of_lt (Nat.sub_le head 1) h_head_lt'
      have h_new_gap_le : gap ≤ head - 1 :=
        Nat.le_sub_of_add_le h_gap_le
      have h_sub_swap : (head - 1) - gap = head - (gap + 1) := by
        rw [Nat.sub_sub, Nat.add_comm 1 gap]
      have h_in_range' : (head - 1) - gap < right.length := by
        rw [h_sub_swap]; exact h_in_range
      have h_get_target' :
          right.get ⟨(head - 1) - gap, h_in_range'⟩ = 11 := by
        have heq : (⟨(head - 1) - gap, h_in_range'⟩ : Fin right.length) =
            ⟨head - (gap + 1), h_in_range⟩ := Fin.eq_of_val_eq h_sub_swap
        rw [heq]; exact h_get_target
      have h_before' :
          ∀ k, k < gap → ∃ (h : (head - 1) - k < right.length),
            right.get ⟨(head - 1) - k, h⟩ < sig ∧
              right.get ⟨(head - 1) - k, h⟩ ≠ 11 := by
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
      have hih := copyUnaryTM_state4_phase_run sig left right gap (head - 1)
        h_new_gap_le h_new_head h_in_range' h_get_target' h_before'
      rw [runFlatTM_copyUnary_state4_unfold sig (gap + 1) _ _
        (copyUnaryTM_state4_step_advance sig left right head
          (right.get ⟨head, h_head_lt'⟩) h_head_lt' h_get_head rfl h_get_head_ne)]
      show runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 4, tapes := [moveTapeHead (left, head, right) TMMove.Lmove] } = _
      show runFlatTM (gap + 1) (copyUnaryTM sig)
          { state_idx := 4, tapes := [(left, head - 1, right)] } = _
      rw [hih]
      show (some { state_idx := 5, tapes := [(left, (head - 1) - gap, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 5, tapes := [(left, head - (gap + 1), right)] }
      rw [h_sub_swap]
  termination_by gap _ _ _ _ _ _ => gap

/-! ### Iteration trajectory and main run lemma

The state-0→0 trajectory of a single iteration:
1. `(state 0, h)` consume on `1`: write `11`, Nmove → `(state 1, h)`.
2. `(state 1, h)` scan right for `7` (at position `M`): `M - h + 1` steps
   → `(state 2, M + 1)`.
3. `(state 2, M + 1)` skip `buf_count` 1s then write a 1 over the first
   `0`: `buf_count + 1` steps → `(state 3, M + 1 + buf_count)`, tape mutated.
4. `(state 3, M + 1 + buf_count)` scan left for `7` (at position `M`):
   `buf_count + 2` steps → `(state 4, M - 1)`.
5. `(state 4, M - 1)` scan left for `11` (at position `h`): `M - h` steps
   → `(state 5, h)`.
6. `(state 5, h)` consume cursor `11`: write `0`, Rmove → `(state 0, h + 1)`.

Total per-iteration steps: `6 + 2 * (M - h) + 2 * buf_count`.
Total tape effect: `right.set h 0` then `.set (M + 1 + buf_count) 1`. -/

/-! ### Tape-position lemmas needed for the iteration proof -/

/-- The cursor-write form (returned by step_consume) equals `right.set h 11`. -/
private theorem cursorWrite_eq_set (right : List Nat) (h : Nat)
    (h_h_lt : h < right.length) :
    right.take h ++ (11 : Nat) :: right.drop (h + 1) = right.set h 11 := by
  rw [List.set_eq_take_append_cons_drop, if_pos h_h_lt]

/-- After phase 2 writes 1 at position `p` of the cursor-tape, then
state 5 writes 0 at position `h` (the cursor): the final tape equals
`(right.set h 0).set p 1`. Uses `List.set_comm` and `List.set_set`. -/
private theorem cursor_buf_set_simp (right : List Nat) (h p : Nat)
    (h_ne : h ≠ p) :
    ((right.set h 11).set p 1).set h 0 = (right.set h 0).set p 1 := by
  rw [List.set_comm 1 0 h_ne.symm, List.set_set]

/-- The cursor-write tape equals `right.set h 11`; reduces the
`writeCurrentTapeSymbol` form. -/
private theorem writeCur_eleven_eq (left : List Nat) (h : Nat) (right : List Nat)
    (h_h_lt : h < right.length) :
    writeCurrentTapeSymbol (left, h, right) (some 11) =
      (left, h, right.set h 11) := by
  have h_w : writeCurrentTapeSymbol (left, h, right) (some 11) =
      (left, h, right.take h ++ (11 : Nat) :: right.drop (h + 1)) := by
    simp [writeCurrentTapeSymbol, h_h_lt]
  rw [h_w, cursorWrite_eq_set right h h_h_lt]

/-- The write-0-at-head tape equals `right.set h 0`. -/
private theorem writeCur_zero_eq (left : List Nat) (h : Nat) (right : List Nat)
    (h_h_lt : h < right.length) :
    writeCurrentTapeSymbol (left, h, right) (some 0) =
      (left, h, right.set h 0) := by
  have h_w : writeCurrentTapeSymbol (left, h, right) (some 0) =
      (left, h, right.take h ++ (0 : Nat) :: right.drop (h + 1)) := by
    simp [writeCurrentTapeSymbol, h_h_lt]
  rw [h_w, List.set_eq_take_append_cons_drop, if_pos h_h_lt]

/-! ### Iteration trajectory and main run lemma

The state-0→0 trajectory of a single iteration:
1. `(state 0, h)` on `1`: write `11` (cursor), `Nmove` → `(state 1, h)`.
2. `(state 1, h)` scan right for `7` at `M`: `M - h + 1` steps
   → `(state 2, M + 1)`.
3. `(state 2, M + 1)` skip `buf_count` 1s then write `1` over the first
   `0`: `buf_count + 1` steps → `(state 3, M + 1 + buf_count)`, tape
   mutated at position `M + 1 + buf_count`.
4. `(state 3, M + 1 + buf_count)` scan left for `7` at `M`:
   `buf_count + 2` steps → `(state 4, M - 1)`.
5. `(state 4, M - 1)` scan left for `11` at `h`: `M - h` steps
   → `(state 5, h)`.
6. `(state 5, h)` on cursor `11`: write `0`, `Rmove` → `(state 0, h + 1)`.

Total per-iteration steps: `6 + 2 * (M - h) + 2 * buf_count`.

The iteration lemma chains the four phase lemmas with the two
single-step lemmas (`state0_step_consume`, `state5_step_cursor`). The
proof of the iteration lemma is deferred to **Step 11.3c** as labelled
`TODO(Part2-followup:copyUnaryTM_iteration_run)` because the chain of
hypothesis translations between phases (from the original `right` to
the cursor-tape `rC = right.set h 11` to the post-write tape
`rB = rC.set (M+1+buf_count) 1`) is bookkeeping-heavy and ran past
the 11.3b LOC budget. The phase scan lemmas
(`copyUnaryTM_stateN_phase_run` for `N ∈ {1,2,3,4}`) are proved
unconditionally above and ready to be glued. -/

/-- Telescoped tape state after `v` copy-unary iterations starting at
position `h` with `buf_count` cells already written in the var-buffer. -/
def copyUnaryTape (right : List Nat) (h M buf_count v : Nat) : List Nat :=
  match v with
  | 0 => right
  | w + 1 => copyUnaryTape ((right.set h 0).set (M + 1 + buf_count) 1)
                            (h + 1) M (buf_count + 1) w

theorem copyUnaryTape_zero (right : List Nat) (h M buf_count : Nat) :
    copyUnaryTape right h M buf_count 0 = right := rfl

theorem copyUnaryTape_succ (right : List Nat) (h M buf_count w : Nat) :
    copyUnaryTape right h M buf_count (w + 1) =
      copyUnaryTape ((right.set h 0).set (M + 1 + buf_count) 1)
        (h + 1) M (buf_count + 1) w := rfl

/-- **Single-iteration run lemma** (statement; proof deferred to 11.3c).

Caller obligations:
* `h < M`: marker 7 strictly to the right of source position.
* `M < right.length`, `M + 1 + buf_count < right.length`: marker and
  buffer in range.
* `right.get h = 1`: source `1` at the head.
* `right.get M = 7`: marker present.
* `h_mid`: each cell in `(h, M)` is `< sig` and `≠ 7` and `≠ 11` (so
  the right-scan and the cursor-find left-scan terminate on the
  right cells without false matches).
* `h_buf_ones`: each cell in `[M+1, M+1+buf_count)` is `1` (the
  previously written buffer cells).
* `right.get (M + 1 + buf_count) = 0`: the next-empty buffer cell. -/
theorem copyUnaryTM_iteration_run
    (sig : Nat) (h_sig : 12 ≤ sig)
    (left right : List Nat) (h M buf_count : Nat)
    (h_h_lt_M : h < M)
    (h_M_lt : M < right.length)
    (h_buf_in_range : M + 1 + buf_count < right.length)
    (h_get_h : right.get ⟨h, Nat.lt_trans h_h_lt_M h_M_lt⟩ = 1)
    (h_get_M : right.get ⟨M, h_M_lt⟩ = 7)
    (h_mid : ∀ k, 1 ≤ k → k < M - h →
        ∃ (h_lt : h + k < right.length),
          right.get ⟨h + k, h_lt⟩ < sig ∧
            right.get ⟨h + k, h_lt⟩ ≠ 7 ∧
            right.get ⟨h + k, h_lt⟩ ≠ 11)
    (h_buf_ones : ∀ j, j < buf_count →
        ∃ (h_lt : M + 1 + j < right.length),
          right.get ⟨M + 1 + j, h_lt⟩ = 1)
    (h_get_buf : right.get ⟨M + 1 + buf_count, h_buf_in_range⟩ = 0) :
    runFlatTM (6 + 2 * (M - h) + 2 * buf_count) (copyUnaryTM sig)
        { state_idx := 0, tapes := [(left, h, right)] } =
      some { state_idx := 0
             tapes := [(left, h + 1,
               (right.set h 0).set (M + 1 + buf_count) 1)] } := by
  -- ============================================================
  -- Reusable arithmetic / position facts.
  -- ============================================================
  have h_h_lt : h < right.length := Nat.lt_trans h_h_lt_M h_M_lt
  have h_h_le_M : h ≤ M := Nat.le_of_lt h_h_lt_M
  have h_M_sub_h_add : h + (M - h) = M := Nat.add_sub_cancel' h_h_le_M
  have h_h_ne_M : h ≠ M := Nat.ne_of_lt h_h_lt_M
  have h_h_lt_buf : h < M + 1 + buf_count := by omega
  have h_h_ne_buf : h ≠ M + 1 + buf_count := Nat.ne_of_lt h_h_lt_buf
  have h_M_lt_buf : M < M + 1 + buf_count := by omega
  have h_M_ne_buf : M ≠ M + 1 + buf_count := Nat.ne_of_lt h_M_lt_buf
  have h_11_lt_sig : (11 : Nat) < sig :=
    Nat.lt_of_lt_of_le (by decide : (11 : Nat) < 12) h_sig
  -- ============================================================
  -- Tape lengths preserved under `set`.
  -- ============================================================
  have h_setlen_rC : (right.set h 11).length = right.length := List.length_set
  have h_setlen_rB :
      ((right.set h 11).set (M + 1 + buf_count) 1).length = right.length := by
    rw [List.length_set, h_setlen_rC]
  have h_M_lt_rC : M < (right.set h 11).length := by
    rw [h_setlen_rC]; exact h_M_lt
  have h_buf_lt_rC : M + 1 + buf_count < (right.set h 11).length := by
    rw [h_setlen_rC]; exact h_buf_in_range
  have h_h_lt_rC : h < (right.set h 11).length := by
    rw [h_setlen_rC]; exact h_h_lt
  have h_h_lt_rB :
      h < ((right.set h 11).set (M + 1 + buf_count) 1).length := by
    rw [h_setlen_rB]; exact h_h_lt
  have h_M_lt_rB :
      M < ((right.set h 11).set (M + 1 + buf_count) 1).length := by
    rw [h_setlen_rB]; exact h_M_lt
  have h_buf_lt_rB :
      M + 1 + buf_count <
        ((right.set h 11).set (M + 1 + buf_count) 1).length := by
    rw [h_setlen_rB]; exact h_buf_in_range
  -- ============================================================
  -- Step 0 (1 step): state 0 → state 1, tape becomes `right.set h 11`.
  -- ============================================================
  have h_step0' :
      stepFlatTM (copyUnaryTM sig)
          { state_idx := 0, tapes := [(left, h, right)] } =
        some { state_idx := 1, tapes := [(left, h, right.set h 11)] } := by
    rw [copyUnaryTM_state0_step_consume sig left right h h_h_lt h_get_h]
    rw [writeCur_eleven_eq left h right h_h_lt]
  have h_run0 :
      runFlatTM 1 (copyUnaryTM sig)
          { state_idx := 0, tapes := [(left, h, right)] } =
        some { state_idx := 1, tapes := [(left, h, right.set h 11)] } := by
    rw [runFlatTM_copyUnary_state0_unfold sig 0 _ _ h_step0']; rfl
  -- ============================================================
  -- Phase 1 ((M-h) + 1 steps): state 1 → state 2.
  -- On tape rC = right.set h 11, scan right from h until 7 at M.
  -- ============================================================
  have h_marker1 :
      (right.set h 11).get
          ⟨h + (M - h),
            (show h + (M - h) < (right.set h 11).length by
              rw [h_M_sub_h_add, h_setlen_rC]; exact h_M_lt)⟩ = 7 := by
    have heq : (⟨h + (M - h),
        (show h + (M - h) < (right.set h 11).length by
          rw [h_M_sub_h_add, h_setlen_rC]; exact h_M_lt)⟩
            : Fin (right.set h 11).length) = ⟨M, h_M_lt_rC⟩ :=
      Fin.eq_of_val_eq h_M_sub_h_add
    rw [heq]
    show (right.set h 11)[M]'h_M_lt_rC = 7
    rw [List.getElem_set_ne h_h_ne_M]
    exact h_get_M
  have h_in_range1 : h + (M - h) < (right.set h 11).length := by
    rw [h_M_sub_h_add, h_setlen_rC]; exact h_M_lt
  have h_mid1 :
      ∀ k, k < M - h → ∃ (h_lt : h + k < (right.set h 11).length),
        (right.set h 11).get ⟨h + k, h_lt⟩ < sig ∧
          (right.set h 11).get ⟨h + k, h_lt⟩ ≠ 7 := by
    intro k hk
    rcases Nat.eq_or_lt_of_le (Nat.zero_le k) with h_k_eq | h_k_pos
    · -- k = 0, cell is 11 (the cursor)
      have h_k_zero : k = 0 := h_k_eq.symm
      subst h_k_zero
      have h_h_lt' : h + 0 < (right.set h 11).length := by
        rw [Nat.add_zero]; exact h_h_lt_rC
      refine ⟨h_h_lt', ?_, ?_⟩
      · show (right.set h 11)[h + 0]'h_h_lt' < sig
        have heq : (⟨h + 0, h_h_lt'⟩ : Fin (right.set h 11).length) =
            ⟨h, h_h_lt_rC⟩ := Fin.eq_of_val_eq (Nat.add_zero h)
        show (right.set h 11).get ⟨h + 0, h_h_lt'⟩ < sig
        rw [heq]
        show (right.set h 11)[h]'h_h_lt_rC < sig
        rw [List.getElem_set_self]
        exact h_11_lt_sig
      · show (right.set h 11)[h + 0]'h_h_lt' ≠ 7
        have heq : (⟨h + 0, h_h_lt'⟩ : Fin (right.set h 11).length) =
            ⟨h, h_h_lt_rC⟩ := Fin.eq_of_val_eq (Nat.add_zero h)
        show (right.set h 11).get ⟨h + 0, h_h_lt'⟩ ≠ 7
        rw [heq]
        show (right.set h 11)[h]'h_h_lt_rC ≠ 7
        rw [List.getElem_set_self]
        decide
    · -- k > 0: cell unchanged from `right`.
      rcases h_mid k h_k_pos hk with ⟨h_kk_orig, h_lt_sig, h_ne7, _⟩
      have h_kk_set : h + k < (right.set h 11).length := h_setlen_rC ▸ h_kk_orig
      have h_h_ne_k : h ≠ h + k := by omega
      refine ⟨h_kk_set, ?_, ?_⟩
      · show (right.set h 11)[h + k]'h_kk_set < sig
        rw [List.getElem_set_ne h_h_ne_k]
        exact h_lt_sig
      · show (right.set h 11)[h + k]'h_kk_set ≠ 7
        rw [List.getElem_set_ne h_h_ne_k]
        exact h_ne7
  have h_run1 :
      runFlatTM ((M - h) + 1) (copyUnaryTM sig)
          { state_idx := 1, tapes := [(left, h, right.set h 11)] } =
        some { state_idx := 2
               tapes := [(left, h + (M - h) + 1, right.set h 11)] } :=
    copyUnaryTM_state1_phase_run sig left (right.set h 11) (M - h) h
      h_in_range1 h_marker1 h_mid1
  -- Normalize the post-phase-1 head: h + (M-h) + 1 = M + 1.
  have h_head_phase1 : h + (M - h) + 1 = M + 1 := by
    rw [h_M_sub_h_add]
  have h_run1' :
      runFlatTM ((M - h) + 1) (copyUnaryTM sig)
          { state_idx := 1, tapes := [(left, h, right.set h 11)] } =
        some { state_idx := 2
               tapes := [(left, M + 1, right.set h 11)] } := by
    rw [h_run1, h_head_phase1]
  -- ============================================================
  -- Phase 2 (buf_count + 1 steps): state 2 → state 3.
  -- Scan right from M+1 to first `0` at M+1+buf_count, write 1.
  -- ============================================================
  have h_in_range2 : (M + 1) + buf_count < (right.set h 11).length := by
    rw [h_setlen_rC]; exact h_buf_in_range
  have h_zero2 :
      (right.set h 11).get ⟨(M + 1) + buf_count, h_in_range2⟩ = 0 := by
    show (right.set h 11)[(M + 1) + buf_count]'h_in_range2 = 0
    rw [List.getElem_set_ne h_h_ne_buf]
    show right.get ⟨(M + 1) + buf_count, h_buf_in_range⟩ = 0
    exact h_get_buf
  have h_mid2 :
      ∀ k, k < buf_count → ∃ (h_lt : (M + 1) + k < (right.set h 11).length),
        (right.set h 11).get ⟨(M + 1) + k, h_lt⟩ = 1 := by
    intro k hk
    rcases h_buf_ones k hk with ⟨h_kk_orig, h_eq_one⟩
    have h_kk_set : (M + 1) + k < (right.set h 11).length :=
      h_setlen_rC ▸ h_kk_orig
    have h_h_ne_pos : h ≠ (M + 1) + k := by
      have : h < (M + 1) + k := by omega
      exact Nat.ne_of_lt this
    refine ⟨h_kk_set, ?_⟩
    show (right.set h 11)[(M + 1) + k]'h_kk_set = 1
    rw [List.getElem_set_ne h_h_ne_pos]
    exact h_eq_one
  have h_run2_takecons :
      runFlatTM (buf_count + 1) (copyUnaryTM sig)
          { state_idx := 2, tapes := [(left, M + 1, right.set h 11)] } =
        some { state_idx := 3
               tapes := [(left, (M + 1) + buf_count,
                 (right.set h 11).take ((M + 1) + buf_count) ++
                   (1 : Nat) :: (right.set h 11).drop ((M + 1) + buf_count + 1))] } :=
    copyUnaryTM_state2_phase_run sig left (right.set h 11) buf_count (M + 1)
      h_in_range2 h_zero2 h_mid2
  -- Convert take/cons/drop form to `set` form.
  have h_phase2_bridge :
      (right.set h 11).take ((M + 1) + buf_count) ++
          (1 : Nat) :: (right.set h 11).drop ((M + 1) + buf_count + 1) =
        (right.set h 11).set ((M + 1) + buf_count) 1 := by
    have h_lem :
        (right.set h 11).set ((M + 1) + buf_count) (1 : Nat) =
          if (M + 1 + buf_count) < (right.set h 11).length then
            (right.set h 11).take ((M + 1) + buf_count) ++
              (1 : Nat) :: (right.set h 11).drop ((M + 1) + buf_count + 1)
          else (right.set h 11) :=
      List.set_eq_take_append_cons_drop
    rw [if_pos h_buf_lt_rC] at h_lem
    exact h_lem.symm
  have h_run2 :
      runFlatTM (buf_count + 1) (copyUnaryTM sig)
          { state_idx := 2, tapes := [(left, M + 1, right.set h 11)] } =
        some { state_idx := 3
               tapes := [(left, (M + 1) + buf_count,
                 (right.set h 11).set ((M + 1) + buf_count) 1)] } := by
    rw [h_run2_takecons, h_phase2_bridge]
  -- ============================================================
  -- Phase 3 ((buf_count + 1) + 1 steps): state 3 → state 4.
  -- Scan left from M+1+buf_count to 7 at M; end head = M - 1.
  -- ============================================================
  -- Cleaner name for the tape after phase 2:
  -- rB := (right.set h 11).set ((M + 1) + buf_count) 1
  have h_gap_le3 : buf_count + 1 ≤ (M + 1) + buf_count := by
    have : 0 + 1 ≤ M + 1 := Nat.succ_le_succ (Nat.zero_le M)
    -- (buf_count + 1) ≤ (M + 1) + buf_count ↔ 1 ≤ M + 1, trivial.
    omega
  have h_head3_lt :
      (M + 1) + buf_count <
        ((right.set h 11).set ((M + 1) + buf_count) 1).length := by
    rw [h_setlen_rB]; exact h_buf_in_range
  have h_sub_phase3 : ((M + 1) + buf_count) - (buf_count + 1) = M := by omega
  have h_in_range3 :
      ((M + 1) + buf_count) - (buf_count + 1) <
        ((right.set h 11).set ((M + 1) + buf_count) 1).length := by
    rw [h_sub_phase3, h_setlen_rB]; exact h_M_lt
  have h_get_target3 :
      ((right.set h 11).set ((M + 1) + buf_count) 1).get
          ⟨((M + 1) + buf_count) - (buf_count + 1), h_in_range3⟩ = 7 := by
    have heq : (⟨((M + 1) + buf_count) - (buf_count + 1), h_in_range3⟩
            : Fin ((right.set h 11).set ((M + 1) + buf_count) 1).length) =
        ⟨M, h_M_lt_rB⟩ := Fin.eq_of_val_eq h_sub_phase3
    rw [heq]
    show ((right.set h 11).set ((M + 1) + buf_count) 1)[M]'h_M_lt_rB = 7
    rw [List.getElem_set_ne h_M_ne_buf.symm]
    show (right.set h 11)[M]'h_M_lt_rC = 7
    rw [List.getElem_set_ne h_h_ne_M]
    exact h_get_M
  have h_before3 :
      ∀ k, k < buf_count + 1 → ∃ (hp : ((M + 1) + buf_count) - k <
        ((right.set h 11).set ((M + 1) + buf_count) 1).length),
        ((right.set h 11).set ((M + 1) + buf_count) 1).get
            ⟨((M + 1) + buf_count) - k, hp⟩ < sig ∧
          ((right.set h 11).set ((M + 1) + buf_count) 1).get
            ⟨((M + 1) + buf_count) - k, hp⟩ ≠ 7 := by
    intro k hk
    rcases Nat.eq_or_lt_of_le (Nat.zero_le k) with h_k_eq | h_k_pos
    · -- k = 0: position M+1+buf_count, value 1 (just written).
      have h_k_zero : k = 0 := h_k_eq.symm
      subst h_k_zero
      have h_pos_lt : ((M + 1) + buf_count) - 0 <
          ((right.set h 11).set ((M + 1) + buf_count) 1).length := by
        rw [Nat.sub_zero, h_setlen_rB]; exact h_buf_in_range
      refine ⟨h_pos_lt, ?_, ?_⟩
      · show ((right.set h 11).set ((M + 1) + buf_count) 1)[((M + 1) + buf_count) - 0]'h_pos_lt < sig
        have heq : (⟨((M + 1) + buf_count) - 0, h_pos_lt⟩
              : Fin ((right.set h 11).set ((M + 1) + buf_count) 1).length) =
            ⟨(M + 1) + buf_count, h_buf_lt_rB⟩ :=
          Fin.eq_of_val_eq (Nat.sub_zero _)
        show ((right.set h 11).set ((M + 1) + buf_count) 1).get
            ⟨((M + 1) + buf_count) - 0, h_pos_lt⟩ < sig
        rw [heq]
        show ((right.set h 11).set ((M + 1) + buf_count) 1)[(M + 1) + buf_count]'h_buf_lt_rB < sig
        rw [List.getElem_set_self]
        exact Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 12) h_sig
      · show ((right.set h 11).set ((M + 1) + buf_count) 1)[((M + 1) + buf_count) - 0]'h_pos_lt ≠ 7
        have heq : (⟨((M + 1) + buf_count) - 0, h_pos_lt⟩
              : Fin ((right.set h 11).set ((M + 1) + buf_count) 1).length) =
            ⟨(M + 1) + buf_count, h_buf_lt_rB⟩ :=
          Fin.eq_of_val_eq (Nat.sub_zero _)
        show ((right.set h 11).set ((M + 1) + buf_count) 1).get
            ⟨((M + 1) + buf_count) - 0, h_pos_lt⟩ ≠ 7
        rw [heq]
        show ((right.set h 11).set ((M + 1) + buf_count) 1)[(M + 1) + buf_count]'h_buf_lt_rB ≠ 7
        rw [List.getElem_set_self]
        decide
    · -- k ≥ 1: position = (M+1+buf_count) - k ∈ [M+1, M+buf_count].
      -- Write as M + 1 + (buf_count - k) using h_buf_ones.
      have h_k_le_buf : k ≤ buf_count := Nat.le_of_lt_succ hk
      have h_diff_lt : buf_count - k < buf_count := by
        have h_k_ge_1 : 1 ≤ k := h_k_pos
        omega
      rcases h_buf_ones (buf_count - k) h_diff_lt with ⟨h_kk_orig, h_eq_one⟩
      have h_pos_eq : (M + 1) + (buf_count - k) = ((M + 1) + buf_count) - k := by
        omega
      have h_kk_orig' : ((M + 1) + buf_count) - k < right.length := h_pos_eq ▸ h_kk_orig
      have h_kk_rB : ((M + 1) + buf_count) - k <
          ((right.set h 11).set ((M + 1) + buf_count) 1).length := by
        rw [h_setlen_rB]; exact h_kk_orig'
      have h_pos_ne_buf : (M + 1 + buf_count) ≠ ((M + 1) + buf_count) - k := by
        have h_sub_lt : ((M + 1) + buf_count) - k < (M + 1) + buf_count := by
          have h_k_ge_1 : 1 ≤ k := h_k_pos
          have h_buf_ge_k : k ≤ (M + 1) + buf_count := by
            calc k ≤ buf_count := h_k_le_buf
              _ ≤ (M + 1) + buf_count := Nat.le_add_left _ _
          omega
        exact Nat.ne_of_gt h_sub_lt
      have h_h_ne_pos : h ≠ ((M + 1) + buf_count) - k := by
        have h_h_lt_pos : h < ((M + 1) + buf_count) - k := by
          rw [← h_pos_eq]
          have : h ≤ M := h_h_le_M
          omega
        exact Nat.ne_of_lt h_h_lt_pos
      refine ⟨h_kk_rB, ?_, ?_⟩
      · show ((right.set h 11).set ((M + 1) + buf_count) 1)[((M + 1) + buf_count) - k]'h_kk_rB < sig
        rw [List.getElem_set_ne h_pos_ne_buf]
        show (right.set h 11)[((M + 1) + buf_count) - k]'(h_setlen_rC ▸ h_kk_orig') < sig
        rw [List.getElem_set_ne h_h_ne_pos]
        show right[((M + 1) + buf_count) - k]'h_kk_orig' < sig
        have heq : (⟨((M + 1) + buf_count) - k, h_kk_orig'⟩ : Fin right.length) =
            ⟨(M + 1) + (buf_count - k), h_kk_orig⟩ := Fin.eq_of_val_eq h_pos_eq.symm
        show right.get ⟨((M + 1) + buf_count) - k, h_kk_orig'⟩ < sig
        rw [heq, h_eq_one]
        exact Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 12) h_sig
      · show ((right.set h 11).set ((M + 1) + buf_count) 1)[((M + 1) + buf_count) - k]'h_kk_rB ≠ 7
        rw [List.getElem_set_ne h_pos_ne_buf]
        show (right.set h 11)[((M + 1) + buf_count) - k]'(h_setlen_rC ▸ h_kk_orig') ≠ 7
        rw [List.getElem_set_ne h_h_ne_pos]
        show right[((M + 1) + buf_count) - k]'h_kk_orig' ≠ 7
        have heq : (⟨((M + 1) + buf_count) - k, h_kk_orig'⟩ : Fin right.length) =
            ⟨(M + 1) + (buf_count - k), h_kk_orig⟩ := Fin.eq_of_val_eq h_pos_eq.symm
        show right.get ⟨((M + 1) + buf_count) - k, h_kk_orig'⟩ ≠ 7
        rw [heq, h_eq_one]
        decide
  have h_run3_raw :
      runFlatTM ((buf_count + 1) + 1) (copyUnaryTM sig)
          { state_idx := 3,
            tapes := [(left, (M + 1) + buf_count,
              (right.set h 11).set ((M + 1) + buf_count) 1)] } =
        some { state_idx := 4
               tapes := [(left, ((M + 1) + buf_count) - (buf_count + 1) - 1,
                 (right.set h 11).set ((M + 1) + buf_count) 1)] } :=
    copyUnaryTM_state3_phase_run sig left
      ((right.set h 11).set ((M + 1) + buf_count) 1) (buf_count + 1)
      ((M + 1) + buf_count) h_gap_le3 h_head3_lt h_in_range3
      h_get_target3 h_before3
  -- Normalize end head: ((M+1)+buf_count) - (buf_count+1) - 1 = M - 1.
  have h_head_phase3 : ((M + 1) + buf_count) - (buf_count + 1) - 1 = M - 1 := by
    omega
  have h_run3 :
      runFlatTM ((buf_count + 1) + 1) (copyUnaryTM sig)
          { state_idx := 3,
            tapes := [(left, (M + 1) + buf_count,
              (right.set h 11).set ((M + 1) + buf_count) 1)] } =
        some { state_idx := 4
               tapes := [(left, M - 1,
                 (right.set h 11).set ((M + 1) + buf_count) 1)] } := by
    rw [h_run3_raw, h_head_phase3]
  -- ============================================================
  -- Phase 4 ((M - 1 - h) + 1 = M - h steps): state 4 → state 5.
  -- Scan left from M-1 to cursor 11 at h. End head = h.
  -- ============================================================
  -- Handle the M = h+something case using h < M.
  have h_M_pos : 1 ≤ M := by omega
  have h_h_le_M1 : h ≤ M - 1 := Nat.le_sub_of_add_le h_h_lt_M
  have h_gap_le4 : M - 1 - h ≤ M - 1 := Nat.sub_le _ _
  have h_head4_lt :
      M - 1 < ((right.set h 11).set ((M + 1) + buf_count) 1).length := by
    rw [h_setlen_rB]
    exact Nat.lt_of_le_of_lt (Nat.sub_le M 1) h_M_lt
  have h_sub_phase4 : (M - 1) - (M - 1 - h) = h := by omega
  have h_in_range4 :
      (M - 1) - (M - 1 - h) <
        ((right.set h 11).set ((M + 1) + buf_count) 1).length := by
    rw [h_sub_phase4, h_setlen_rB]; exact h_h_lt
  have h_get_target4 :
      ((right.set h 11).set ((M + 1) + buf_count) 1).get
          ⟨(M - 1) - (M - 1 - h), h_in_range4⟩ = 11 := by
    have heq : (⟨(M - 1) - (M - 1 - h), h_in_range4⟩
            : Fin ((right.set h 11).set ((M + 1) + buf_count) 1).length) =
        ⟨h, h_h_lt_rB⟩ := Fin.eq_of_val_eq h_sub_phase4
    rw [heq]
    show ((right.set h 11).set ((M + 1) + buf_count) 1)[h]'h_h_lt_rB = 11
    rw [List.getElem_set_ne h_h_ne_buf.symm]
    show (right.set h 11)[h]'h_h_lt_rC = 11
    rw [List.getElem_set_self]
  have h_before4 :
      ∀ k, k < M - 1 - h → ∃ (hp : (M - 1) - k <
        ((right.set h 11).set ((M + 1) + buf_count) 1).length),
        ((right.set h 11).set ((M + 1) + buf_count) 1).get
            ⟨(M - 1) - k, hp⟩ < sig ∧
          ((right.set h 11).set ((M + 1) + buf_count) 1).get
            ⟨(M - 1) - k, hp⟩ ≠ 11 := by
    intro k hk
    -- pos = (M-1) - k ∈ [h+1, M-1].
    have h_k_le : k ≤ M - 1 - h := Nat.le_of_lt hk
    have h_pos_le : (M - 1) - k ≤ M - 1 := Nat.sub_le _ _
    have h_pos_ge : h + 1 ≤ (M - 1) - k := by omega
    have h_pos_lt_M : (M - 1) - k < M := by omega
    have h_pos_gt_h : h < (M - 1) - k := h_pos_ge
    have h_pos_lt_buf : (M - 1) - k < (M + 1) + buf_count := by
      calc (M - 1) - k ≤ M - 1 := Nat.sub_le _ _
        _ < M + 1 + buf_count := by omega
    have h_pos_lt_right : (M - 1) - k < right.length :=
      Nat.lt_trans h_pos_lt_M h_M_lt
    have h_pos_lt_rB : (M - 1) - k <
        ((right.set h 11).set ((M + 1) + buf_count) 1).length := by
      rw [h_setlen_rB]; exact h_pos_lt_right
    have h_pos_ne_h : h ≠ (M - 1) - k := Nat.ne_of_lt h_pos_gt_h
    have h_pos_ne_buf : (M + 1 + buf_count) ≠ (M - 1) - k :=
      Nat.ne_of_gt h_pos_lt_buf
    -- Use h_mid with k' = (M-1-k) - h, which is in [1, M-h-1] ⊆ [1, M-h).
    have h_k'_pos : 1 ≤ (M - 1 - k) - h := by omega
    have h_k'_lt : (M - 1 - k) - h < M - h := by omega
    have h_h_plus : h + ((M - 1 - k) - h) = (M - 1) - k := by omega
    rcases h_mid ((M - 1 - k) - h) h_k'_pos h_k'_lt with
      ⟨h_kk_orig, h_lt_sig, h_ne7, h_ne11⟩
    refine ⟨h_pos_lt_rB, ?_, ?_⟩
    · show ((right.set h 11).set ((M + 1) + buf_count) 1)[(M - 1) - k]'h_pos_lt_rB < sig
      rw [List.getElem_set_ne h_pos_ne_buf]
      show (right.set h 11)[(M - 1) - k]'(h_setlen_rC ▸ h_pos_lt_right) < sig
      rw [List.getElem_set_ne h_pos_ne_h]
      show right[(M - 1) - k]'h_pos_lt_right < sig
      have heq : (⟨(M - 1) - k, h_pos_lt_right⟩ : Fin right.length) =
          ⟨h + ((M - 1 - k) - h), h_kk_orig⟩ := Fin.eq_of_val_eq h_h_plus.symm
      show right.get ⟨(M - 1) - k, h_pos_lt_right⟩ < sig
      rw [heq]; exact h_lt_sig
    · show ((right.set h 11).set ((M + 1) + buf_count) 1)[(M - 1) - k]'h_pos_lt_rB ≠ 11
      rw [List.getElem_set_ne h_pos_ne_buf]
      show (right.set h 11)[(M - 1) - k]'(h_setlen_rC ▸ h_pos_lt_right) ≠ 11
      rw [List.getElem_set_ne h_pos_ne_h]
      show right[(M - 1) - k]'h_pos_lt_right ≠ 11
      have heq : (⟨(M - 1) - k, h_pos_lt_right⟩ : Fin right.length) =
          ⟨h + ((M - 1 - k) - h), h_kk_orig⟩ := Fin.eq_of_val_eq h_h_plus.symm
      show right.get ⟨(M - 1) - k, h_pos_lt_right⟩ ≠ 11
      rw [heq]; exact h_ne11
  have h_run4_raw :
      runFlatTM ((M - 1 - h) + 1) (copyUnaryTM sig)
          { state_idx := 4,
            tapes := [(left, M - 1,
              (right.set h 11).set ((M + 1) + buf_count) 1)] } =
        some { state_idx := 5
               tapes := [(left, (M - 1) - (M - 1 - h),
                 (right.set h 11).set ((M + 1) + buf_count) 1)] } :=
    copyUnaryTM_state4_phase_run sig left
      ((right.set h 11).set ((M + 1) + buf_count) 1) (M - 1 - h) (M - 1)
      h_gap_le4 h_head4_lt h_in_range4 h_get_target4 h_before4
  -- Normalize end head: (M-1) - (M-1-h) = h. Also step count: M-1-h+1 = M-h.
  have h_steps4 : (M - 1 - h) + 1 = M - h := by omega
  have h_run4 :
      runFlatTM (M - h) (copyUnaryTM sig)
          { state_idx := 4,
            tapes := [(left, M - 1,
              (right.set h 11).set ((M + 1) + buf_count) 1)] } =
        some { state_idx := 5
               tapes := [(left, h,
                 (right.set h 11).set ((M + 1) + buf_count) 1)] } := by
    rw [← h_steps4, h_run4_raw, h_sub_phase4]
  -- ============================================================
  -- Step 5 (1 step): state 5 → state 0; write 0 at h, Rmove.
  -- ============================================================
  -- We have rB[h] = 11 (proven above as h_get_target4 after normalization).
  have h_get_h_rB : ((right.set h 11).set ((M + 1) + buf_count) 1).get
      ⟨h, h_h_lt_rB⟩ = 11 := by
    show ((right.set h 11).set ((M + 1) + buf_count) 1)[h]'h_h_lt_rB = 11
    rw [List.getElem_set_ne h_h_ne_buf.symm]
    show (right.set h 11)[h]'h_h_lt_rC = 11
    rw [List.getElem_set_self]
  have h_step5_raw :
      stepFlatTM (copyUnaryTM sig)
          { state_idx := 5,
            tapes := [(left, h,
              (right.set h 11).set ((M + 1) + buf_count) 1)] } =
        some { state_idx := 0,
               tapes := [moveTapeHead
                 (writeCurrentTapeSymbol
                   (left, h, (right.set h 11).set ((M + 1) + buf_count) 1)
                   (some 0))
                 TMMove.Rmove] } :=
    copyUnaryTM_state5_step_cursor sig left
      ((right.set h 11).set ((M + 1) + buf_count) 1) h h_h_lt_rB h_get_h_rB
  -- Reduce the writeCurrentTapeSymbol + moveTapeHead chain.
  have h_write5 :
      writeCurrentTapeSymbol
          (left, h, (right.set h 11).set ((M + 1) + buf_count) 1) (some 0) =
        (left, h, ((right.set h 11).set ((M + 1) + buf_count) 1).set h 0) :=
    writeCur_zero_eq left h ((right.set h 11).set ((M + 1) + buf_count) 1) h_h_lt_rB
  have h_move5 :
      moveTapeHead
          (left, h, ((right.set h 11).set ((M + 1) + buf_count) 1).set h 0)
          TMMove.Rmove =
        (left, h + 1, ((right.set h 11).set ((M + 1) + buf_count) 1).set h 0) := rfl
  have h_step5 :
      stepFlatTM (copyUnaryTM sig)
          { state_idx := 5,
            tapes := [(left, h,
              (right.set h 11).set ((M + 1) + buf_count) 1)] } =
        some { state_idx := 0,
               tapes := [(left, h + 1,
                 ((right.set h 11).set ((M + 1) + buf_count) 1).set h 0)] } := by
    rw [h_step5_raw, h_write5, h_move5]
  -- Simplify final tape via cursor_buf_set_simp.
  have h_final_tape :
      ((right.set h 11).set ((M + 1) + buf_count) 1).set h 0 =
        (right.set h 0).set (M + 1 + buf_count) 1 :=
    cursor_buf_set_simp right h (M + 1 + buf_count) h_h_ne_buf
  have h_run5 :
      runFlatTM 1 (copyUnaryTM sig)
          { state_idx := 5,
            tapes := [(left, h,
              (right.set h 11).set ((M + 1) + buf_count) 1)] } =
        some { state_idx := 0,
               tapes := [(left, h + 1,
                 (right.set h 0).set (M + 1 + buf_count) 1)] } := by
    rw [runFlatTM_copyUnary_state5_unfold sig 0 _ _ h_step5]
    show runFlatTM 0 (copyUnaryTM sig)
        { state_idx := 0,
          tapes := [(left, h + 1,
            ((right.set h 11).set ((M + 1) + buf_count) 1).set h 0)] } = _
    rw [h_final_tape]
    rfl
  -- ============================================================
  -- Chain via runFlatTM_compose. Target time:
  -- 6 + 2*(M-h) + 2*buf_count = 1 + ((M-h+1) + ((buf_count+1)
  --     + ((buf_count+1)+1 + ((M-h) + 1))))
  -- ============================================================
  have h_total_eq :
      6 + 2 * (M - h) + 2 * buf_count =
        1 + ((M - h + 1) + ((buf_count + 1) + ((buf_count + 1 + 1) + ((M - h) + 1)))) := by
    ring
  rw [h_total_eq]
  rw [runFlatTM_compose (copyUnaryTM sig) 1
      ((M - h + 1) + ((buf_count + 1) + ((buf_count + 1 + 1) + ((M - h) + 1))))
      _ _ h_run0]
  rw [runFlatTM_compose (copyUnaryTM sig) (M - h + 1)
      ((buf_count + 1) + ((buf_count + 1 + 1) + ((M - h) + 1)))
      _ _ h_run1']
  rw [runFlatTM_compose (copyUnaryTM sig) (buf_count + 1)
      ((buf_count + 1 + 1) + ((M - h) + 1))
      _ _ h_run2]
  rw [runFlatTM_compose (copyUnaryTM sig) (buf_count + 1 + 1)
      ((M - h) + 1)
      _ _ h_run3]
  rw [runFlatTM_compose (copyUnaryTM sig) (M - h) 1
      _ _ h_run4]
  exact h_run5

/-- **Main run lemma** for `copyUnaryTM` (statement; proof deferred to
11.3c).

Inducts on `v` (the number of source `1`s remaining to consume). The
`v = 0` base case is the state-0 halt step (1 step from state 0 to
state 6 via `state0_step_halt` on the terminator). The inductive step
applies `copyUnaryTM_iteration_run` for one iteration, then the IH for
the remaining `v - 1` iterations on the shifted tape.

Per-iteration cost is `6 + 2(M - h) + 2 * buf_count`, which is INVARIANT
under the shift `(h, buf_count) → (h + 1, buf_count + 1)`:
`6 + 2(M - (h+1)) + 2(buf_count + 1) = 6 + 2(M - h) + 2 * buf_count`.
So total time for `v` iterations + final halt step is
`v * (6 + 2(M - h) + 2 * buf_count) + 1`. -/
theorem copyUnaryTM_run_found
    (sig : Nat) (h_sig : 12 ≤ sig) (left : List Nat) (M : Nat) :
    ∀ (v : Nat) (right : List Nat) (h buf_count : Nat)
      (h_v_le_M : h + v ≤ M)
      (h_M_lt : M < right.length)
      (h_buf_in_range : M + v + buf_count < right.length)
      (h_source : ∀ i, i < v → ∃ (h_lt : h + i < right.length),
          right.get ⟨h + i, h_lt⟩ = 1)
      (h_term_lt : h + v < right.length)
      (_h_get_term : right.get ⟨h + v, h_term_lt⟩ ≠ 1 ∧
                    right.get ⟨h + v, h_term_lt⟩ < sig ∧
                    right.get ⟨h + v, h_term_lt⟩ ≠ 7 ∧
                    right.get ⟨h + v, h_term_lt⟩ ≠ 11)
      (_h_get_M : right.get ⟨M, h_M_lt⟩ = 7)
      (_h_mid : ∀ k, h + v < k → k < M →
          ∃ (h_lt : k < right.length),
            right.get ⟨k, h_lt⟩ < sig ∧
              right.get ⟨k, h_lt⟩ ≠ 7 ∧
              right.get ⟨k, h_lt⟩ ≠ 11)
      (_h_buf_ones : ∀ j, j < buf_count →
          ∃ (h_lt : M + 1 + j < right.length),
            right.get ⟨M + 1 + j, h_lt⟩ = 1)
      (_h_buf_zeros : ∀ j, j < v →
          ∃ (h_lt : M + 1 + buf_count + j < right.length),
            right.get ⟨M + 1 + buf_count + j, h_lt⟩ = 0),
      runFlatTM (v * (6 + 2 * (M - h) + 2 * buf_count) + 1) (copyUnaryTM sig)
          { state_idx := 0, tapes := [(left, h, right)] } =
        some { state_idx := 6
               tapes := [(left, h + v, copyUnaryTape right h M buf_count v)] }
  | 0, right, h, buf_count, _h_v_le_M, h_M_lt, _h_buf_in_range,
      _h_source, h_term_lt, h_get_term, _h_get_M, _h_mid,
      _h_buf_ones, _h_buf_zeros => by
      -- v = 0 base case: one step from state 0 to halt state 6 since
      -- right[h] is the terminator (≠ 1, < sig).
      have h_h_lt : h < right.length := by
        have := h_term_lt
        rwa [Nat.add_zero] at this
      have h_get_h : right.get ⟨h, h_h_lt⟩ =
          right.get ⟨h + 0, h_term_lt⟩ := by
        have heq : (⟨h, h_h_lt⟩ : Fin right.length) = ⟨h + 0, h_term_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero h).symm
        rw [heq]
      obtain ⟨h_ne_1, h_lt_sig, _, _⟩ := h_get_term
      have h_get_h_ne_1 : right.get ⟨h, h_h_lt⟩ ≠ 1 := by rw [h_get_h]; exact h_ne_1
      have h_get_h_lt_sig : right.get ⟨h, h_h_lt⟩ < sig := by rw [h_get_h]; exact h_lt_sig
      have h_step :=
        copyUnaryTM_state0_step_halt sig left right h
          (right.get ⟨h, h_h_lt⟩) h_h_lt h_get_h_lt_sig rfl h_get_h_ne_1
      show runFlatTM (0 * (6 + 2 * (M - h) + 2 * buf_count) + 1) (copyUnaryTM sig)
          { state_idx := 0, tapes := [(left, h, right)] } =
        some { state_idx := 6,
               tapes := [(left, h + 0, copyUnaryTape right h M buf_count 0)] }
      rw [Nat.zero_mul, Nat.zero_add]
      rw [runFlatTM_copyUnary_state0_unfold sig 0 _ _ h_step]
      show runFlatTM 0 (copyUnaryTM sig)
          { state_idx := 6, tapes := [(left, h, right)] } =
        some { state_idx := 6,
               tapes := [(left, h + 0, copyUnaryTape right h M buf_count 0)] }
      show (some { state_idx := 6, tapes := [(left, h, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 6,
               tapes := [(left, h + 0, copyUnaryTape right h M buf_count 0)] }
      rw [Nat.add_zero, copyUnaryTape_zero]
  | w + 1, right, h, buf_count, h_v_le_M, h_M_lt, h_buf_in_range,
      h_source, h_term_lt, h_get_term, h_get_M, h_mid,
      h_buf_ones, h_buf_zeros => by
      -- v = w + 1: peel off one iteration, then recurse on w with
      -- shifted tape `right' = (right.set h 0).set (M+1+buf_count) 1`.
      -- ============================================================
      -- Reusable arithmetic facts
      -- ============================================================
      have h_h_lt_M : h < M := by
        have : h + 1 ≤ h + (w + 1) := by omega
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self h)
          (Nat.le_trans this h_v_le_M)
      have h_h_lt : h < right.length := Nat.lt_trans h_h_lt_M h_M_lt
      have h_h_ne_M : h ≠ M := Nat.ne_of_lt h_h_lt_M
      have h_h_lt_buf : h < M + 1 + buf_count := by omega
      have h_h_ne_buf : h ≠ M + 1 + buf_count := Nat.ne_of_lt h_h_lt_buf
      have h_M_lt_buf : M < M + 1 + buf_count := by omega
      have h_M_ne_buf : M ≠ M + 1 + buf_count := Nat.ne_of_lt h_M_lt_buf
      -- ============================================================
      -- Prerequisites for the iteration lemma.
      -- ============================================================
      -- h_get_h : right.get ⟨h, _⟩ = 1 (from h_source 0).
      rcases h_source 0 (Nat.zero_lt_succ _) with ⟨h_lt0, h_eq_1⟩
      have h_get_h : right.get ⟨h, Nat.lt_trans h_h_lt_M h_M_lt⟩ = 1 := by
        have heq : (⟨h, Nat.lt_trans h_h_lt_M h_M_lt⟩ : Fin right.length) =
            ⟨h + 0, h_lt0⟩ := Fin.eq_of_val_eq (Nat.add_zero h).symm
        rw [heq]; exact h_eq_1
      -- h_iter_buf : M + 1 + buf_count < right.length (from h_buf_in_range
      -- with v = w + 1 ≥ 1).
      have h_iter_buf : M + 1 + buf_count < right.length := by
        have : M + 1 + buf_count ≤ M + (w + 1) + buf_count := by omega
        exact Nat.lt_of_le_of_lt this h_buf_in_range
      -- h_iter_mid : ∀ k, 1 ≤ k → k < M - h →
      --   ∃ h_lt, right.get ⟨h+k, h_lt⟩ < sig ∧ ≠ 7 ∧ ≠ 11.
      -- Split: k < w + 1 (source) vs k = w + 1 (terminator) vs k > w + 1 (mid).
      have h_iter_mid :
          ∀ k, 1 ≤ k → k < M - h →
            ∃ (h_lt : h + k < right.length),
              right.get ⟨h + k, h_lt⟩ < sig ∧
                right.get ⟨h + k, h_lt⟩ ≠ 7 ∧
                right.get ⟨h + k, h_lt⟩ ≠ 11 := by
        intro k h_k_pos h_k_lt_M_h
        by_cases h_k_lt : k < w + 1
        · -- Source region: cell = 1.
          rcases h_source k h_k_lt with ⟨h_lt, h_eq_1⟩
          refine ⟨h_lt, ?_, ?_, ?_⟩
          · rw [h_eq_1]; exact Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 12) h_sig
          · rw [h_eq_1]; decide
          · rw [h_eq_1]; decide
        · -- k ≥ w + 1
          push_neg at h_k_lt
          by_cases h_k_eq : k = w + 1
          · -- Terminator at h + (w + 1) = h + v.
            subst h_k_eq
            refine ⟨h_term_lt, ?_, ?_, ?_⟩
            · exact h_get_term.2.1
            · exact h_get_term.2.2.1
            · exact h_get_term.2.2.2
          · -- k > w + 1: in mid gap (h+v, M).
            have h_k_gt : w + 1 < k := Nat.lt_of_le_of_ne h_k_lt (Ne.symm h_k_eq)
            have h_pos_gt : h + (w + 1) < h + k := Nat.add_lt_add_left h_k_gt h
            have h_pos_lt_M : h + k < M := by
              have : h + k < h + (M - h) := Nat.add_lt_add_left h_k_lt_M_h h
              have h_h_le_M : h ≤ M := Nat.le_of_lt h_h_lt_M
              rwa [Nat.add_sub_cancel' h_h_le_M] at this
            rcases h_mid (h + k) h_pos_gt h_pos_lt_M with ⟨h_lt, h1, h2, h3⟩
            exact ⟨h_lt, h1, h2, h3⟩
      -- h_iter_buf_ones : same as h_buf_ones (just types/length match).
      have h_iter_buf_ones :
          ∀ j, j < buf_count →
            ∃ (h_lt : M + 1 + j < right.length),
              right.get ⟨M + 1 + j, h_lt⟩ = 1 := h_buf_ones
      -- h_iter_get_buf : right.get ⟨M + 1 + buf_count, _⟩ = 0
      -- (from h_buf_zeros 0).
      rcases h_buf_zeros 0 (Nat.zero_lt_succ _) with ⟨h_lt_b0, h_eq_0⟩
      have h_get_buf : right.get ⟨M + 1 + buf_count, h_iter_buf⟩ = 0 := by
        have heq : (⟨M + 1 + buf_count, h_iter_buf⟩ : Fin right.length) =
            ⟨M + 1 + buf_count + 0, h_lt_b0⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero _).symm
        rw [heq]; exact h_eq_0
      -- Apply iteration lemma.
      have h_iter :=
        copyUnaryTM_iteration_run sig h_sig left right h M buf_count
          h_h_lt_M h_M_lt h_iter_buf h_get_h h_get_M h_iter_mid
          h_iter_buf_ones h_get_buf
      -- ============================================================
      -- Set up the post-iteration tape `right'` and verify IH hypotheses.
      -- ============================================================
      -- (right' = (right.set h 0).set (M + 1 + buf_count) 1)
      have h_len_right' :
          ((right.set h 0).set (M + 1 + buf_count) 1).length = right.length := by
        rw [List.length_set, List.length_set]
      -- IH hypotheses for h' = h+1, buf_count' = buf_count+1, v = w:
      have h_v_le_M' : (h + 1) + w ≤ M := by
        have := h_v_le_M; omega
      have h_M_lt' : M < ((right.set h 0).set (M + 1 + buf_count) 1).length := by
        rw [h_len_right']; exact h_M_lt
      have h_buf_in_range' :
          M + w + (buf_count + 1) <
            ((right.set h 0).set (M + 1 + buf_count) 1).length := by
        rw [h_len_right']
        have : M + w + (buf_count + 1) = M + (w + 1) + buf_count := by omega
        rw [this]; exact h_buf_in_range
      -- Length facts at hand: lengths preserved by `set`.
      have h_len_set0 : (right.set h 0).length = right.length := List.length_set
      have h_len_setset : ((right.set h 0).set (M + 1 + buf_count) 1).length =
          (right.set h 0).length := List.length_set
      -- Generic helper: read at a position untouched by either `set`.
      -- For any `pos` with `pos ≠ h` and `pos ≠ M+1+buf_count`,
      -- `((right.set h 0).set (M+1+buf_count) 1).get ⟨pos, _⟩ = right.get ⟨pos, _⟩`.
      have h_translate :
          ∀ (pos : Nat) (h_pos_ne_h : h ≠ pos)
            (h_pos_ne_buf : M + 1 + buf_count ≠ pos)
            (h_lt : pos < right.length),
            ∃ (h_lt' : pos <
              ((right.set h 0).set (M + 1 + buf_count) 1).length),
              ((right.set h 0).set (M + 1 + buf_count) 1).get ⟨pos, h_lt'⟩ =
                right.get ⟨pos, h_lt⟩ := by
        intro pos h_pos_ne_h h_pos_ne_buf h_lt
        have h_lt' : pos <
            ((right.set h 0).set (M + 1 + buf_count) 1).length := by
          rw [h_len_setset, h_len_set0]; exact h_lt
        refine ⟨h_lt', ?_⟩
        show ((right.set h 0).set (M + 1 + buf_count) 1)[pos]'h_lt' =
          right.get ⟨pos, h_lt⟩
        rw [List.getElem_set_ne h_pos_ne_buf, List.getElem_set_ne h_pos_ne_h]
        rfl
      have h_source' :
          ∀ i, i < w → ∃ (h_lt : (h + 1) + i <
            ((right.set h 0).set (M + 1 + buf_count) 1).length),
            ((right.set h 0).set (M + 1 + buf_count) 1).get
              ⟨(h + 1) + i, h_lt⟩ = 1 := by
        intro i hi
        have h_i1_lt : i + 1 < w + 1 := Nat.succ_lt_succ hi
        rcases h_source (i + 1) h_i1_lt with ⟨h_lt, h_eq_1⟩
        have h_pos_eq : h + (i + 1) = (h + 1) + i := by omega
        have h_lt' : (h + 1) + i < right.length := h_pos_eq ▸ h_lt
        have h_pos_ne_h : h ≠ (h + 1) + i := by omega
        have h_pos_ne_buf : M + 1 + buf_count ≠ (h + 1) + i := by
          have h_pos_lt : (h + 1) + i < M + 1 + buf_count := by omega
          exact Nat.ne_of_gt h_pos_lt
        rcases h_translate ((h + 1) + i) h_pos_ne_h h_pos_ne_buf h_lt' with
          ⟨h_lt_right', h_get_eq⟩
        refine ⟨h_lt_right', ?_⟩
        rw [h_get_eq]
        have heq : (⟨(h + 1) + i, h_lt'⟩ : Fin right.length) =
            ⟨h + (i + 1), h_lt⟩ := Fin.eq_of_val_eq h_pos_eq.symm
        rw [heq]; exact h_eq_1
      have h_pos_eq_term : (h + 1) + w = h + (w + 1) := by omega
      have h_lt_term : (h + 1) + w < right.length := h_pos_eq_term ▸ h_term_lt
      have h_pos_ne_h_term : h ≠ (h + 1) + w := by omega
      have h_pos_ne_buf_term : M + 1 + buf_count ≠ (h + 1) + w := by
        have : (h + 1) + w < M + 1 + buf_count := by omega
        exact Nat.ne_of_gt this
      obtain ⟨h_term_lt', h_get_term_eq⟩ :=
        h_translate ((h + 1) + w) h_pos_ne_h_term h_pos_ne_buf_term h_lt_term
      have h_finmk_term : (⟨(h + 1) + w, h_lt_term⟩ : Fin right.length) =
          ⟨h + (w + 1), h_term_lt⟩ := Fin.eq_of_val_eq h_pos_eq_term
      have h_get_term' :
          ((right.set h 0).set (M + 1 + buf_count) 1).get
              ⟨(h + 1) + w, h_term_lt'⟩ ≠ 1 ∧
            ((right.set h 0).set (M + 1 + buf_count) 1).get
              ⟨(h + 1) + w, h_term_lt'⟩ < sig ∧
            ((right.set h 0).set (M + 1 + buf_count) 1).get
              ⟨(h + 1) + w, h_term_lt'⟩ ≠ 7 ∧
            ((right.set h 0).set (M + 1 + buf_count) 1).get
              ⟨(h + 1) + w, h_term_lt'⟩ ≠ 11 := by
        rw [h_get_term_eq, h_finmk_term]
        exact h_get_term
      obtain ⟨_, h_get_M_eq⟩ :=
        h_translate M h_h_ne_M h_M_ne_buf.symm h_M_lt
      have h_get_M' :
          ((right.set h 0).set (M + 1 + buf_count) 1).get
              ⟨M, h_M_lt'⟩ = 7 := by
        rw [show (⟨M, h_M_lt'⟩ : Fin _) = ⟨M, by rw [h_len_setset, h_len_set0]; exact h_M_lt⟩
          from rfl]
        rw [h_get_M_eq]; exact h_get_M
      have h_mid' :
          ∀ k, (h + 1) + w < k → k < M →
            ∃ (h_lt : k < ((right.set h 0).set (M + 1 + buf_count) 1).length),
              ((right.set h 0).set (M + 1 + buf_count) 1).get
                  ⟨k, h_lt⟩ < sig ∧
                ((right.set h 0).set (M + 1 + buf_count) 1).get
                  ⟨k, h_lt⟩ ≠ 7 ∧
                ((right.set h 0).set (M + 1 + buf_count) 1).get
                  ⟨k, h_lt⟩ ≠ 11 := by
        intro k h_k_gt h_k_lt
        have h_k_gt' : h + (w + 1) < k := by
          have h_eq : h + (w + 1) = (h + 1) + w := by omega
          rw [h_eq]; exact h_k_gt
        rcases h_mid k h_k_gt' h_k_lt with ⟨h_lt_orig, h1, h2, h3⟩
        have h_pos_ne_h : h ≠ k := by omega
        have h_pos_ne_buf : M + 1 + buf_count ≠ k := by
          have : k < M + 1 + buf_count := by omega
          exact Nat.ne_of_gt this
        obtain ⟨h_lt_right', h_get_eq⟩ :=
          h_translate k h_pos_ne_h h_pos_ne_buf h_lt_orig
        refine ⟨h_lt_right', ?_, ?_, ?_⟩
        · rw [h_get_eq]; exact h1
        · rw [h_get_eq]; exact h2
        · rw [h_get_eq]; exact h3
      have h_buf_ones' :
          ∀ j, j < buf_count + 1 →
            ∃ (h_lt : M + 1 + j <
              ((right.set h 0).set (M + 1 + buf_count) 1).length),
              ((right.set h 0).set (M + 1 + buf_count) 1).get
                ⟨M + 1 + j, h_lt⟩ = 1 := by
        intro j hj
        by_cases h_j_lt : j < buf_count
        · -- j < buf_count: existing 1.
          rcases h_buf_ones j h_j_lt with ⟨h_lt_orig, h_eq_1⟩
          have h_pos_ne_h : h ≠ M + 1 + j := by omega
          have h_pos_ne_buf : M + 1 + buf_count ≠ M + 1 + j := by
            have : M + 1 + j < M + 1 + buf_count := by omega
            exact Nat.ne_of_gt this
          obtain ⟨h_lt_right', h_get_eq⟩ :=
            h_translate (M + 1 + j) h_pos_ne_h h_pos_ne_buf h_lt_orig
          refine ⟨h_lt_right', ?_⟩
          rw [h_get_eq]; exact h_eq_1
        · -- j = buf_count: the cell we just wrote 1 to.
          push_neg at h_j_lt
          have h_j_eq : j = buf_count := Nat.le_antisymm (Nat.le_of_lt_succ hj) h_j_lt
          have h_lt_full : M + 1 + buf_count <
              ((right.set h 0).set (M + 1 + buf_count) 1).length := by
            rw [h_len_setset, h_len_set0]; exact h_iter_buf
          refine ⟨?_, ?_⟩
          · -- length proof: rewrite j to buf_count via h_j_eq
            simp only [h_j_eq]; exact h_lt_full
          · -- value proof: again rewrite j to buf_count via h_j_eq
            simp only [h_j_eq]
            show ((right.set h 0).set (M + 1 + buf_count) 1)[M + 1 + buf_count]'h_lt_full = 1
            rw [List.getElem_set_self]
      have h_buf_zeros' :
          ∀ j, j < w →
            ∃ (h_lt : M + 1 + (buf_count + 1) + j <
              ((right.set h 0).set (M + 1 + buf_count) 1).length),
              ((right.set h 0).set (M + 1 + buf_count) 1).get
                ⟨M + 1 + (buf_count + 1) + j, h_lt⟩ = 0 := by
        intro j hj
        have h_j1_lt : j + 1 < w + 1 := Nat.succ_lt_succ hj
        rcases h_buf_zeros (j + 1) h_j1_lt with ⟨h_lt_orig, h_eq_0⟩
        have h_pos_eq : M + 1 + buf_count + (j + 1) = M + 1 + (buf_count + 1) + j := by omega
        have h_lt_right : M + 1 + (buf_count + 1) + j < right.length :=
          h_pos_eq ▸ h_lt_orig
        have h_pos_ne_h : h ≠ M + 1 + (buf_count + 1) + j := by omega
        have h_pos_ne_buf : M + 1 + buf_count ≠ M + 1 + (buf_count + 1) + j := by
          have : M + 1 + buf_count < M + 1 + (buf_count + 1) + j := by omega
          exact Nat.ne_of_lt this
        obtain ⟨h_lt_right', h_get_eq⟩ :=
          h_translate (M + 1 + (buf_count + 1) + j) h_pos_ne_h h_pos_ne_buf h_lt_right
        refine ⟨h_lt_right', ?_⟩
        rw [h_get_eq]
        have heq : (⟨M + 1 + (buf_count + 1) + j, h_lt_right⟩ : Fin right.length) =
            ⟨M + 1 + buf_count + (j + 1), h_lt_orig⟩ :=
          Fin.eq_of_val_eq h_pos_eq.symm
        rw [heq]; exact h_eq_0
      -- Apply IH (recursive call) on shifted tape.
      have h_ih :=
        copyUnaryTM_run_found sig h_sig left M w
          ((right.set h 0).set (M + 1 + buf_count) 1) (h + 1) (buf_count + 1)
          h_v_le_M' h_M_lt' h_buf_in_range' h_source' h_term_lt'
          h_get_term' h_get_M' h_mid' h_buf_ones' h_buf_zeros'
      -- ============================================================
      -- Chain iteration + IH via runFlatTM_compose.
      -- Per-iteration cost X = 6 + 2*(M-h) + 2*buf_count.
      -- IH cost (w iterations + final halt) = w * X' + 1
      --   where X' = 6 + 2*(M - (h+1)) + 2*(buf_count+1).
      -- X' = X because M - (h+1) = M - h - 1 (using h+1 ≤ M).
      -- ============================================================
      have h_h1_le_M : h + 1 ≤ M := by omega
      have h_X_eq : 6 + 2 * (M - (h + 1)) + 2 * (buf_count + 1) =
          6 + 2 * (M - h) + 2 * buf_count := by omega
      -- Rewrite IH's time bound to use X (not X').
      have h_ih' :
          runFlatTM (w * (6 + 2 * (M - h) + 2 * buf_count) + 1) (copyUnaryTM sig)
              { state_idx := 0,
                tapes := [(left, h + 1,
                  (right.set h 0).set (M + 1 + buf_count) 1)] } =
            some { state_idx := 6,
                   tapes := [(left, (h + 1) + w,
                     copyUnaryTape ((right.set h 0).set (M + 1 + buf_count) 1)
                       (h + 1) M (buf_count + 1) w)] } := by
        rw [← h_X_eq]; exact h_ih
      -- Total time: (w + 1) * X + 1 = X + (w * X + 1).
      have h_total_eq :
          (w + 1) * (6 + 2 * (M - h) + 2 * buf_count) + 1 =
            (6 + 2 * (M - h) + 2 * buf_count) +
              (w * (6 + 2 * (M - h) + 2 * buf_count) + 1) := by ring
      show runFlatTM ((w + 1) * (6 + 2 * (M - h) + 2 * buf_count) + 1) (copyUnaryTM sig)
          { state_idx := 0, tapes := [(left, h, right)] } =
        some { state_idx := 6,
               tapes := [(left, h + (w + 1),
                 copyUnaryTape right h M buf_count (w + 1))] }
      rw [h_total_eq]
      rw [runFlatTM_compose (copyUnaryTM sig) (6 + 2 * (M - h) + 2 * buf_count)
        (w * (6 + 2 * (M - h) + 2 * buf_count) + 1) _ _ h_iter]
      rw [h_ih']
      -- Final cleanup: (h+1) + w = h + (w+1); copyUnaryTape_succ.
      have h_head_eq : (h + 1) + w = h + (w + 1) := by omega
      rw [h_head_eq, copyUnaryTape_succ]
  termination_by v _ _ _ _ _ _ _ _ _ _ _ _ _ => v

end Primitives
end EvalCnfTM
