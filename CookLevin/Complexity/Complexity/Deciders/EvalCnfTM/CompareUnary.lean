import Complexity.Complexity.Deciders.EvalCnfTM.Primitives

set_option autoImplicit false

namespace EvalCnfTM
namespace Primitives

open TMPrimitives (currentTapeSymbol_in_range currentTapeSymbol_out_of_range)

/-! ## `compareUnaryAtMarkerTM` — compare two unary numbers in delimited regions

A 9-state single-tape TM that compares two unary numbers and halts in
state `7` (reject) when the two are unequal, or state `8` (accept)
when they are equal.

### Tape layout

- **Slot**: in the assignment region, encoded `[LBM] 1^s [RBM]` where
  `LBM ∈ {5, 6}` is the slot's left boundary marker and `RBM = 6` is
  the slot's right boundary marker.
- **Var-buffer**: between markers `7` and `8` (a contiguous region
  `[7] 1^v 0^(capacity - v) [8]`).

The caller positions the head at the first cell *after* `LBM` (i.e.,
the slot's leftmost `1` cell, or the `RBM = 6` if the slot is empty).

### Operational semantics (shuttle erase)

Each iteration erases one `1` from each region (slot and var-buffer)
simultaneously. The persistent cursor marker (alphabet symbol `11`,
reused from `copyUnaryTM`) sits at the slot side; the var-buffer
side's position is implicit (re-scanned from marker `7` each
iteration).

### State machine (9 states)

- **0** (slot-scan): read current slot cell.
  - On `1`: write `11` (cursor), Rmove, → state 1.
  - On `6`: no write, Nmove, → state 4 (slot exhausted; check var-buffer).
- **1** (transit right to marker `7`):
  - On `7`: no write, Rmove, → state 2.
  - On `v ≠ 7`: no write, Rmove, → state 1.
- **2** (scan var-buffer for next `1`):
  - On `0`: no write, Rmove, → state 2.
  - On `1`: write `0`, Lmove, → state 3.
  - On `8`: no write, Nmove, → state 6 (var-buffer exhausted; cleanup
    cursor before rejecting because slot still has `1`s).
- **3** (transit left to cursor `11`):
  - On `11`: write `0`, Rmove, → state 0 (resume next iteration).
  - On `v ≠ 11`: no write, Lmove, → state 3.
- **4** (slot exhausted; transit right to marker `7`):
  - On `7`: no write, Rmove, → state 5.
  - On `v ≠ 7`: no write, Rmove, → state 4.
- **5** (slot exhausted; check var-buffer is also exhausted):
  - On `0`: no write, Rmove, → state 5.
  - On `1`: no write, Nmove, → state 7 (reject: slot empty, varbuf not).
  - On `8`: no write, Nmove, → state 8 (accept: both exhausted).
- **6** (var-buffer exhausted; clean up cursor):
  - On `11`: write `0`, Nmove, → state 7 (reject: slot still has `1`s).
  - On `v ≠ 11`: no write, Lmove, → state 6.
- **7**: halt-reject.
- **8**: halt-accept.

Total entries: `4 * sig + 8` (= 56 entries for `sig = 12`).

This file lands Step 11.4a (TM def + validity + step lemmas). The
multi-step run lemmas (`compareUnaryAtMarkerTM_iteration_run`,
`compareUnaryAtMarkerTM_run_match`, `compareUnaryAtMarkerTM_run_short`,
`compareUnaryAtMarkerTM_run_long`) are deferred to Steps 11.4b–d. -/

/-! ### Transition entries -/

private def compareUnary_s0_one : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some 1]
    dst_state := 1
    dst_write_vals := [some 11]
    move_dirs := [TMMove.Rmove] }

private def compareUnary_s0_six : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some 6]
    dst_state := 4
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def compareUnary_s1_seven : FlatTMTransEntry :=
  { src_state := 1
    src_tape_vals := [some 7]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def compareUnary_s1_advance (v : Nat) : FlatTMTransEntry :=
  { src_state := 1
    src_tape_vals := [some v]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def compareUnary_s2_zero : FlatTMTransEntry :=
  { src_state := 2
    src_tape_vals := [some 0]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def compareUnary_s2_one : FlatTMTransEntry :=
  { src_state := 2
    src_tape_vals := [some 1]
    dst_state := 3
    dst_write_vals := [some 0]
    move_dirs := [TMMove.Lmove] }

private def compareUnary_s2_eight : FlatTMTransEntry :=
  { src_state := 2
    src_tape_vals := [some 8]
    dst_state := 6
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def compareUnary_s3_eleven : FlatTMTransEntry :=
  { src_state := 3
    src_tape_vals := [some 11]
    dst_state := 0
    dst_write_vals := [some 0]
    move_dirs := [TMMove.Rmove] }

private def compareUnary_s3_advance (v : Nat) : FlatTMTransEntry :=
  { src_state := 3
    src_tape_vals := [some v]
    dst_state := 3
    dst_write_vals := [none]
    move_dirs := [TMMove.Lmove] }

private def compareUnary_s4_seven : FlatTMTransEntry :=
  { src_state := 4
    src_tape_vals := [some 7]
    dst_state := 5
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def compareUnary_s4_advance (v : Nat) : FlatTMTransEntry :=
  { src_state := 4
    src_tape_vals := [some v]
    dst_state := 4
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def compareUnary_s5_zero : FlatTMTransEntry :=
  { src_state := 5
    src_tape_vals := [some 0]
    dst_state := 5
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

private def compareUnary_s5_one : FlatTMTransEntry :=
  { src_state := 5
    src_tape_vals := [some 1]
    dst_state := 7
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def compareUnary_s5_eight : FlatTMTransEntry :=
  { src_state := 5
    src_tape_vals := [some 8]
    dst_state := 8
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def compareUnary_s6_eleven : FlatTMTransEntry :=
  { src_state := 6
    src_tape_vals := [some 11]
    dst_state := 7
    dst_write_vals := [some 0]
    move_dirs := [TMMove.Nmove] }

private def compareUnary_s6_advance (v : Nat) : FlatTMTransEntry :=
  { src_state := 6
    src_tape_vals := [some v]
    dst_state := 6
    dst_write_vals := [none]
    move_dirs := [TMMove.Lmove] }

/-! ### TM definition -/

/-- Transition table for `compareUnaryAtMarkerTM`. Organised in seven
per-state blocks. Explicit right-associative parens so that
`List.mem_append` decomposes the membership proof level-by-level. -/
def compareUnaryAtMarkerTM_trans (sig : Nat) : List FlatTMTransEntry :=
  -- Block 0: state-0 transitions (two entries, both explicit).
  ([compareUnary_s0_one, compareUnary_s0_six] : List FlatTMTransEntry)
  ++
  ((-- Block 1: state-1 transitions.
    compareUnary_s1_seven ::
      ((List.range sig).filter (fun v => decide (v ≠ 7))).map compareUnary_s1_advance)
   ++
   ((-- Block 2: state-2 transitions (three entries, all explicit).
     [compareUnary_s2_zero, compareUnary_s2_one, compareUnary_s2_eight]
       : List FlatTMTransEntry)
    ++
    ((-- Block 3: state-3 transitions.
      compareUnary_s3_eleven ::
        ((List.range sig).filter (fun v => decide (v ≠ 11))).map compareUnary_s3_advance)
     ++
     ((-- Block 4: state-4 transitions.
       compareUnary_s4_seven ::
         ((List.range sig).filter (fun v => decide (v ≠ 7))).map compareUnary_s4_advance)
      ++
      ((-- Block 5: state-5 transitions (three entries, all explicit).
        [compareUnary_s5_zero, compareUnary_s5_one, compareUnary_s5_eight]
          : List FlatTMTransEntry)
       ++
       -- Block 6: state-6 transitions.
       (compareUnary_s6_eleven ::
         ((List.range sig).filter (fun v => decide (v ≠ 11))).map compareUnary_s6_advance))))))

/-- The compare-unary TM. Caller obligation: `sig ≥ 12` so the cursor
marker `11` and all other write values are in range. -/
def compareUnaryAtMarkerTM (sig : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 9
  trans := compareUnaryAtMarkerTM_trans sig
  start := 0
  halt := [false, false, false, false, false, false, false, true, true]

/-! ### Validity -/

theorem compareUnaryAtMarkerTM_valid (sig : Nat) (h_sig : 12 ≤ sig) :
    validFlatTM (compareUnaryAtMarkerTM sig) := by
  have h_0 : (0 : Nat) < sig := Nat.lt_of_lt_of_le (by decide) h_sig
  have h_6 : (6 : Nat) < sig := Nat.lt_of_lt_of_le (by decide) h_sig
  have h_7 : (7 : Nat) < sig := Nat.lt_of_lt_of_le (by decide) h_sig
  have h_8 : (8 : Nat) < sig := Nat.lt_of_lt_of_le (by decide) h_sig
  have h_11 : (11 : Nat) < sig := Nat.lt_of_lt_of_le (by decide) h_sig
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 9; decide
  · show [false, false, false, false, false, false, false, true, true].length = 9; rfl
  · intro entry hentry
    have hentry' : entry ∈ compareUnaryAtMarkerTM_trans sig := hentry
    unfold compareUnaryAtMarkerTM_trans at hentry'
    rcases List.mem_append.mp hentry' with h0 | h_r1
    · -- Block 0: state 0 (two entries).
      rcases List.mem_cons.mp h0 with h0_one | h0_rest
      · subst h0_one
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 9; decide
        · show 1 < 9; decide
        · intro x hx; rcases List.mem_singleton.mp hx with rfl
          show (1 : Nat) < sig
          exact Nat.lt_of_lt_of_le (by decide) h_sig
        · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_11
      · rcases List.mem_cons.mp h0_rest with h0_six | h0_nil
        · subst h0_six
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · show 0 < 9; decide
          · show 4 < 9; decide
          · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_6
          · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
        · cases h0_nil
    · rcases List.mem_append.mp h_r1 with h1 | h_r2
      · -- Block 1: state 1.
        rcases List.mem_cons.mp h1 with h1_seven | h1_adv
        · subst h1_seven
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · show 1 < 9; decide
          · show 2 < 9; decide
          · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_7
          · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
        · rcases List.mem_map.mp h1_adv with ⟨v, hv, hmk⟩
          subst hmk
          have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
          have hvlt : v < sig := List.mem_range.mp hv'
          refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
          · show 1 < 9; decide
          · show 1 < 9; decide
          · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hvlt
          · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
      · rcases List.mem_append.mp h_r2 with h2 | h_r3
        · -- Block 2: state 2 (three entries).
          rcases List.mem_cons.mp h2 with h2_zero | h2_rest1
          · subst h2_zero
            refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
            · show 2 < 9; decide
            · show 2 < 9; decide
            · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_0
            · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
          · rcases List.mem_cons.mp h2_rest1 with h2_one | h2_rest2
            · subst h2_one
              refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · show 2 < 9; decide
              · show 3 < 9; decide
              · intro x hx; rcases List.mem_singleton.mp hx with rfl
                show (1 : Nat) < sig
                exact Nat.lt_of_lt_of_le (by decide) h_sig
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_0
            · rcases List.mem_cons.mp h2_rest2 with h2_eight | h2_nil
              · subst h2_eight
                refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                · show 2 < 9; decide
                · show 6 < 9; decide
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_8
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
              · cases h2_nil
        · rcases List.mem_append.mp h_r3 with h3 | h_r4
          · -- Block 3: state 3.
            rcases List.mem_cons.mp h3 with h3_eleven | h3_adv
            · subst h3_eleven
              refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · show 3 < 9; decide
              · show 0 < 9; decide
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_11
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_0
            · rcases List.mem_map.mp h3_adv with ⟨v, hv, hmk⟩
              subst hmk
              have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
              have hvlt : v < sig := List.mem_range.mp hv'
              refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
              · show 3 < 9; decide
              · show 3 < 9; decide
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hvlt
              · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
          · rcases List.mem_append.mp h_r4 with h4 | h_r5
            · -- Block 4: state 4.
              rcases List.mem_cons.mp h4 with h4_seven | h4_adv
              · subst h4_seven
                refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                · show 4 < 9; decide
                · show 5 < 9; decide
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_7
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
              · rcases List.mem_map.mp h4_adv with ⟨v, hv, hmk⟩
                subst hmk
                have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
                have hvlt : v < sig := List.mem_range.mp hv'
                refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                · show 4 < 9; decide
                · show 4 < 9; decide
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hvlt
                · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
            · rcases List.mem_append.mp h_r5 with h5 | h6
              · -- Block 5: state 5 (three entries).
                rcases List.mem_cons.mp h5 with h5_zero | h5_rest1
                · subst h5_zero
                  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                  · show 5 < 9; decide
                  · show 5 < 9; decide
                  · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_0
                  · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
                · rcases List.mem_cons.mp h5_rest1 with h5_one | h5_rest2
                  · subst h5_one
                    refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                    · show 5 < 9; decide
                    · show 7 < 9; decide
                    · intro x hx; rcases List.mem_singleton.mp hx with rfl
                      show (1 : Nat) < sig
                      exact Nat.lt_of_lt_of_le (by decide) h_sig
                    · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
                  · rcases List.mem_cons.mp h5_rest2 with h5_eight | h5_nil
                    · subst h5_eight
                      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                      · show 5 < 9; decide
                      · show 8 < 9; decide
                      · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_8
                      · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial
                    · cases h5_nil
              · -- Block 6: state 6.
                rcases List.mem_cons.mp h6 with h6_eleven | h6_adv
                · subst h6_eleven
                  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                  · show 6 < 9; decide
                  · show 7 < 9; decide
                  · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_11
                  · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h_0
                · rcases List.mem_map.mp h6_adv with ⟨v, hv, hmk⟩
                  subst hmk
                  have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
                  have hvlt : v < sig := List.mem_range.mp hv'
                  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
                  · show 6 < 9; decide
                  · show 6 < 9; decide
                  · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact hvlt
                  · intro x hx; rcases List.mem_singleton.mp hx with rfl; trivial

/-! ### Step helpers -/

private theorem compareUnary_entryMatchesConfig_state_ne_false
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

private theorem compareUnary_find_none_of_all_state_ne
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

private theorem compareUnary_block_0_src_state (e : FlatTMTransEntry)
    (he : e ∈ ([compareUnary_s0_one, compareUnary_s0_six] : List FlatTMTransEntry)) :
    e.src_state = 0 := by
  rcases List.mem_cons.mp he with h_one | h_rest
  · subst h_one; rfl
  · rcases List.mem_cons.mp h_rest with h_six | h_nil
    · subst h_six; rfl
    · cases h_nil

private theorem compareUnary_block_1_src_state (sig : Nat) (e : FlatTMTransEntry)
    (he : e ∈ (compareUnary_s1_seven ::
        ((List.range sig).filter (fun v => decide (v ≠ 7))).map compareUnary_s1_advance)) :
    e.src_state = 1 := by
  rcases List.mem_cons.mp he with h_seven | h_adv
  · subst h_seven; rfl
  · rcases List.mem_map.mp h_adv with ⟨_, _, hv⟩
    subst hv; rfl

private theorem compareUnary_block_2_src_state (e : FlatTMTransEntry)
    (he : e ∈ ([compareUnary_s2_zero, compareUnary_s2_one, compareUnary_s2_eight]
        : List FlatTMTransEntry)) :
    e.src_state = 2 := by
  rcases List.mem_cons.mp he with h_zero | h_rest1
  · subst h_zero; rfl
  · rcases List.mem_cons.mp h_rest1 with h_one | h_rest2
    · subst h_one; rfl
    · rcases List.mem_cons.mp h_rest2 with h_eight | h_nil
      · subst h_eight; rfl
      · cases h_nil

private theorem compareUnary_block_3_src_state (sig : Nat) (e : FlatTMTransEntry)
    (he : e ∈ (compareUnary_s3_eleven ::
        ((List.range sig).filter (fun v => decide (v ≠ 11))).map compareUnary_s3_advance)) :
    e.src_state = 3 := by
  rcases List.mem_cons.mp he with h_eleven | h_adv
  · subst h_eleven; rfl
  · rcases List.mem_map.mp h_adv with ⟨_, _, hv⟩
    subst hv; rfl

private theorem compareUnary_block_4_src_state (sig : Nat) (e : FlatTMTransEntry)
    (he : e ∈ (compareUnary_s4_seven ::
        ((List.range sig).filter (fun v => decide (v ≠ 7))).map compareUnary_s4_advance)) :
    e.src_state = 4 := by
  rcases List.mem_cons.mp he with h_seven | h_adv
  · subst h_seven; rfl
  · rcases List.mem_map.mp h_adv with ⟨_, _, hv⟩
    subst hv; rfl

private theorem compareUnary_block_5_src_state (e : FlatTMTransEntry)
    (he : e ∈ ([compareUnary_s5_zero, compareUnary_s5_one, compareUnary_s5_eight]
        : List FlatTMTransEntry)) :
    e.src_state = 5 := by
  rcases List.mem_cons.mp he with h_zero | h_rest1
  · subst h_zero; rfl
  · rcases List.mem_cons.mp h_rest1 with h_one | h_rest2
    · subst h_one; rfl
    · rcases List.mem_cons.mp h_rest2 with h_eight | h_nil
      · subst h_eight; rfl
      · cases h_nil

private theorem compareUnary_block_6_src_state (sig : Nat) (e : FlatTMTransEntry)
    (he : e ∈ (compareUnary_s6_eleven ::
        ((List.range sig).filter (fun v => decide (v ≠ 11))).map compareUnary_s6_advance)) :
    e.src_state = 6 := by
  rcases List.mem_cons.mp he with h_eleven | h_adv
  · subst h_eleven; rfl
  · rcases List.mem_map.mp h_adv with ⟨_, _, hv⟩
    subst hv; rfl

/-! ### Per-block `find? = none` lemmas -/

private theorem compareUnary_block_0_find_none (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 0) :
    ([compareUnary_s0_one, compareUnary_s0_six] : List FlatTMTransEntry).find?
        (fun e => entryMatchesConfig e cfg) = none := by
  apply compareUnary_find_none_of_all_state_ne
  intro e he
  rw [compareUnary_block_0_src_state e he]
  exact fun heq => h heq.symm

private theorem compareUnary_block_1_find_none (sig : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 1) :
    (compareUnary_s1_seven ::
        ((List.range sig).filter (fun v => decide (v ≠ 7))).map compareUnary_s1_advance).find?
      (fun e => entryMatchesConfig e cfg) = none := by
  apply compareUnary_find_none_of_all_state_ne
  intro e he
  rw [compareUnary_block_1_src_state sig e he]
  exact fun heq => h heq.symm

private theorem compareUnary_block_2_find_none (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 2) :
    ([compareUnary_s2_zero, compareUnary_s2_one, compareUnary_s2_eight]
        : List FlatTMTransEntry).find?
      (fun e => entryMatchesConfig e cfg) = none := by
  apply compareUnary_find_none_of_all_state_ne
  intro e he
  rw [compareUnary_block_2_src_state e he]
  exact fun heq => h heq.symm

private theorem compareUnary_block_3_find_none (sig : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 3) :
    (compareUnary_s3_eleven ::
        ((List.range sig).filter (fun v => decide (v ≠ 11))).map compareUnary_s3_advance).find?
      (fun e => entryMatchesConfig e cfg) = none := by
  apply compareUnary_find_none_of_all_state_ne
  intro e he
  rw [compareUnary_block_3_src_state sig e he]
  exact fun heq => h heq.symm

private theorem compareUnary_block_4_find_none (sig : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 4) :
    (compareUnary_s4_seven ::
        ((List.range sig).filter (fun v => decide (v ≠ 7))).map compareUnary_s4_advance).find?
      (fun e => entryMatchesConfig e cfg) = none := by
  apply compareUnary_find_none_of_all_state_ne
  intro e he
  rw [compareUnary_block_4_src_state sig e he]
  exact fun heq => h heq.symm

private theorem compareUnary_block_5_find_none (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ 5) :
    ([compareUnary_s5_zero, compareUnary_s5_one, compareUnary_s5_eight]
        : List FlatTMTransEntry).find?
      (fun e => entryMatchesConfig e cfg) = none := by
  apply compareUnary_find_none_of_all_state_ne
  intro e he
  rw [compareUnary_block_5_src_state e he]
  exact fun heq => h heq.symm

/-! ### State-0 step lemmas

State 0 is the entry/re-entry point of each shuttle iteration. The
head is positioned at the slot's current `1` cell (or `6 = RBM` when
the slot has been fully consumed). -/

/-- State 0, on slot `1`: write cursor `11`, move right, transition
to state 1. -/
theorem compareUnaryAtMarkerTM_state0_step_one (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 1) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1
             tapes := [moveTapeHead
               (writeCurrentTapeSymbol (left, head, right) (some 11))
               TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 1 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig compareUnary_s0_one cfg = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 1] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.cons_append, List.find?_cons, hMatch]
  rfl

/-- State 0, on RBM `6`: no write, no move, transition to state 4. -/
theorem compareUnaryAtMarkerTM_state0_step_six (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 6) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 4, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 6 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some 6] := by
    show [currentTapeSymbol (left, head, right)] = [some 6]; rw [hSym]
  have hNotMatchOne : entryMatchesConfig compareUnary_s0_one cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some 1] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 1] : List (Option Nat)) ≠ [some 6] := by
      intro h; injection h with h1 _; injection h1 with h2; exact (by decide : (1 : Nat) ≠ 6) h2
    simp [h_ne']
  have hMatchSix : entryMatchesConfig compareUnary_s0_six cfg = true := by
    show ((0 : Nat) == 0 &&
            decide (([some 6] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = true
    rw [hSymTape]; rfl
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.cons_append, List.find?_cons, hNotMatchOne,
      List.cons_append, List.find?_cons, hMatchSix]
  rfl

/-! ### State-1 step lemmas

State 1 scans right to marker `7`. -/

theorem compareUnaryAtMarkerTM_state1_step_match (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 7) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 2
             tapes := [moveTapeHead (left, head, right) TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 1, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 7 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig compareUnary_s1_seven cfg = true := by
    show ((1 : Nat) == 1 &&
            decide (([some 7] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (1 : Nat) ≠ 0; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.cons_append, List.find?_cons, hMatch]
  rfl

theorem compareUnaryAtMarkerTM_state1_step_advance (sig : Nat) (left right : List Nat)
    (head v : Nat) (h_head_lt : head < right.length)
    (h_sym_lt : v < sig)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 7) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 1, tapes := [(left, head, right)] } =
      some { state_idx := 1
             tapes := [moveTapeHead (left, head, right) TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 1, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym]
  have hNotMatchSeven : entryMatchesConfig compareUnary_s1_seven cfg = false := by
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
  have hFindAdv :
      (((List.range sig).filter (fun w => decide (w ≠ 7))).map compareUnary_s1_advance).find?
          (fun e => entryMatchesConfig e cfg) =
        some (compareUnary_s1_advance v) := by
    refine find_singleSomeEntry_match_state cfg 1 v _ compareUnary_s1_advance rfl hSymTape
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
    compareUnary_block_0_find_none cfg (by show (1 : Nat) ≠ 0; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.cons_append, List.find?_cons, hNotMatchSeven,
      List.find?_append, hFindAdv]
  rfl

/-! ### State-2 step lemmas

State 2 scans the var-buffer for the next `1`. -/

theorem compareUnaryAtMarkerTM_state2_step_zero (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 0) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 2, tapes := [(left, head, right)] } =
      some { state_idx := 2
             tapes := [moveTapeHead (left, head, right) TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 2, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 0 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig compareUnary_s2_zero cfg = true := by
    show ((2 : Nat) == 2 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (2 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (2 : Nat) ≠ 1; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.cons_append, List.find?_cons, hMatch]
  rfl

theorem compareUnaryAtMarkerTM_state2_step_one (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 1) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 2, tapes := [(left, head, right)] } =
      some { state_idx := 3
             tapes := [moveTapeHead
               (writeCurrentTapeSymbol (left, head, right) (some 0))
               TMMove.Lmove] } := by
  set cfg : FlatTMConfig := { state_idx := 2, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 1 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some 1] := by
    show [currentTapeSymbol (left, head, right)] = [some 1]; rw [hSym]
  have hNotMatchZero : entryMatchesConfig compareUnary_s2_zero cfg = false := by
    show ((2 : Nat) == cfg.state_idx &&
            decide (([some 0] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 0] : List (Option Nat)) ≠ [some 1] := by
      intro h; injection h with h1 _; injection h1 with h2; exact (by decide : (0 : Nat) ≠ 1) h2
    simp [h_ne']
  have hMatchOne : entryMatchesConfig compareUnary_s2_one cfg = true := by
    show ((2 : Nat) == 2 &&
            decide (([some 1] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = true
    rw [hSymTape]; rfl
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (2 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (2 : Nat) ≠ 1; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.cons_append, List.find?_cons, hNotMatchZero,
      List.cons_append, List.find?_cons, hMatchOne]
  rfl

theorem compareUnaryAtMarkerTM_state2_step_eight (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 8) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 2, tapes := [(left, head, right)] } =
      some { state_idx := 6, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 2, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 8 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some 8] := by
    show [currentTapeSymbol (left, head, right)] = [some 8]; rw [hSym]
  have hNotMatchZero : entryMatchesConfig compareUnary_s2_zero cfg = false := by
    show ((2 : Nat) == cfg.state_idx &&
            decide (([some 0] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 0] : List (Option Nat)) ≠ [some 8] := by
      intro h; injection h with h1 _; injection h1 with h2; exact (by decide : (0 : Nat) ≠ 8) h2
    simp [h_ne']
  have hNotMatchOne : entryMatchesConfig compareUnary_s2_one cfg = false := by
    show ((2 : Nat) == cfg.state_idx &&
            decide (([some 1] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 1] : List (Option Nat)) ≠ [some 8] := by
      intro h; injection h with h1 _; injection h1 with h2; exact (by decide : (1 : Nat) ≠ 8) h2
    simp [h_ne']
  have hMatchEight : entryMatchesConfig compareUnary_s2_eight cfg = true := by
    show ((2 : Nat) == 2 &&
            decide (([some 8] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = true
    rw [hSymTape]; rfl
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (2 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (2 : Nat) ≠ 1; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.cons_append, List.find?_cons, hNotMatchZero,
      List.cons_append, List.find?_cons, hNotMatchOne,
      List.cons_append, List.find?_cons, hMatchEight]
  rfl

/-! ### State-3 step lemmas

State 3 transits left to the cursor marker `11`. -/

theorem compareUnaryAtMarkerTM_state3_step_cursor (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 11) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 3, tapes := [(left, head, right)] } =
      some { state_idx := 0
             tapes := [moveTapeHead
               (writeCurrentTapeSymbol (left, head, right) (some 0))
               TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 3, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 11 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig compareUnary_s3_eleven cfg = true := by
    show ((3 : Nat) == 3 &&
            decide (([some 11] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (3 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (3 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    compareUnary_block_2_find_none cfg (by show (3 : Nat) ≠ 2; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.cons_append, List.find?_cons, hMatch]
  rfl

theorem compareUnaryAtMarkerTM_state3_step_advance (sig : Nat) (left right : List Nat)
    (head v : Nat) (h_head_lt : head < right.length)
    (h_sym_lt : v < sig)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 11) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 3, tapes := [(left, head, right)] } =
      some { state_idx := 3
             tapes := [moveTapeHead (left, head, right) TMMove.Lmove] } := by
  set cfg : FlatTMConfig := { state_idx := 3, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym]
  have hNotMatchEleven : entryMatchesConfig compareUnary_s3_eleven cfg = false := by
    show ((3 : Nat) == cfg.state_idx &&
            decide (([some 11] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 11] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne']
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ 11)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, decide_eq_true h_ne⟩
  have hFindAdv :
      (((List.range sig).filter (fun w => decide (w ≠ 11))).map compareUnary_s3_advance).find?
          (fun e => entryMatchesConfig e cfg) =
        some (compareUnary_s3_advance v) := by
    refine find_singleSomeEntry_match_state cfg 3 v _ compareUnary_s3_advance rfl hSymTape
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
    compareUnary_block_0_find_none cfg (by show (3 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (3 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    compareUnary_block_2_find_none cfg (by show (3 : Nat) ≠ 2; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.cons_append, List.find?_cons, hNotMatchEleven,
      List.find?_append, hFindAdv]
  rfl

/-! ### State-4 step lemmas

State 4 transits right to marker `7` after the slot is exhausted. -/

theorem compareUnaryAtMarkerTM_state4_step_match (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 7) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 4, tapes := [(left, head, right)] } =
      some { state_idx := 5
             tapes := [moveTapeHead (left, head, right) TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 4, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 7 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig compareUnary_s4_seven cfg = true := by
    show ((4 : Nat) == 4 &&
            decide (([some 7] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (4 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (4 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    compareUnary_block_2_find_none cfg (by show (4 : Nat) ≠ 2; decide)
  have h_block_3_none :=
    compareUnary_block_3_find_none sig cfg (by show (4 : Nat) ≠ 3; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.find?_append, h_block_3_none, Option.none_or,
      List.cons_append, List.find?_cons, hMatch]
  rfl

theorem compareUnaryAtMarkerTM_state4_step_advance (sig : Nat) (left right : List Nat)
    (head v : Nat) (h_head_lt : head < right.length)
    (h_sym_lt : v < sig)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 7) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 4, tapes := [(left, head, right)] } =
      some { state_idx := 4
             tapes := [moveTapeHead (left, head, right) TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 4, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym]
  have hNotMatchSeven : entryMatchesConfig compareUnary_s4_seven cfg = false := by
    show ((4 : Nat) == cfg.state_idx &&
            decide (([some 7] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 7] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne']
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ 7)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, decide_eq_true h_ne⟩
  have hFindAdv :
      (((List.range sig).filter (fun w => decide (w ≠ 7))).map compareUnary_s4_advance).find?
          (fun e => entryMatchesConfig e cfg) =
        some (compareUnary_s4_advance v) := by
    refine find_singleSomeEntry_match_state cfg 4 v _ compareUnary_s4_advance rfl hSymTape
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
    compareUnary_block_0_find_none cfg (by show (4 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (4 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    compareUnary_block_2_find_none cfg (by show (4 : Nat) ≠ 2; decide)
  have h_block_3_none :=
    compareUnary_block_3_find_none sig cfg (by show (4 : Nat) ≠ 3; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.find?_append, h_block_3_none, Option.none_or,
      List.cons_append, List.find?_cons, hNotMatchSeven,
      List.find?_append, hFindAdv]
  rfl

/-! ### State-5 step lemmas

State 5 verifies the var-buffer is also exhausted (when the slot
exhausted first). -/

theorem compareUnaryAtMarkerTM_state5_step_zero (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 0) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 5, tapes := [(left, head, right)] } =
      some { state_idx := 5
             tapes := [moveTapeHead (left, head, right) TMMove.Rmove] } := by
  set cfg : FlatTMConfig := { state_idx := 5, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 0 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig compareUnary_s5_zero cfg = true := by
    show ((5 : Nat) == 5 &&
            decide (([some 0] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (5 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (5 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    compareUnary_block_2_find_none cfg (by show (5 : Nat) ≠ 2; decide)
  have h_block_3_none :=
    compareUnary_block_3_find_none sig cfg (by show (5 : Nat) ≠ 3; decide)
  have h_block_4_none :=
    compareUnary_block_4_find_none sig cfg (by show (5 : Nat) ≠ 4; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.find?_append, h_block_3_none, Option.none_or,
      List.find?_append, h_block_4_none, Option.none_or,
      List.cons_append, List.find?_cons, hMatch]
  rfl

theorem compareUnaryAtMarkerTM_state5_step_one (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 1) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 5, tapes := [(left, head, right)] } =
      some { state_idx := 7, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 5, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 1 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some 1] := by
    show [currentTapeSymbol (left, head, right)] = [some 1]; rw [hSym]
  have hNotMatchZero : entryMatchesConfig compareUnary_s5_zero cfg = false := by
    show ((5 : Nat) == cfg.state_idx &&
            decide (([some 0] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 0] : List (Option Nat)) ≠ [some 1] := by
      intro h; injection h with h1 _; injection h1 with h2; exact (by decide : (0 : Nat) ≠ 1) h2
    simp [h_ne']
  have hMatchOne : entryMatchesConfig compareUnary_s5_one cfg = true := by
    show ((5 : Nat) == 5 &&
            decide (([some 1] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = true
    rw [hSymTape]; rfl
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (5 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (5 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    compareUnary_block_2_find_none cfg (by show (5 : Nat) ≠ 2; decide)
  have h_block_3_none :=
    compareUnary_block_3_find_none sig cfg (by show (5 : Nat) ≠ 3; decide)
  have h_block_4_none :=
    compareUnary_block_4_find_none sig cfg (by show (5 : Nat) ≠ 4; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.find?_append, h_block_3_none, Option.none_or,
      List.find?_append, h_block_4_none, Option.none_or,
      List.cons_append, List.find?_cons, hNotMatchZero,
      List.cons_append, List.find?_cons, hMatchOne]
  rfl

theorem compareUnaryAtMarkerTM_state5_step_eight (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 8) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 5, tapes := [(left, head, right)] } =
      some { state_idx := 8, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 5, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 8 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some 8] := by
    show [currentTapeSymbol (left, head, right)] = [some 8]; rw [hSym]
  have hNotMatchZero : entryMatchesConfig compareUnary_s5_zero cfg = false := by
    show ((5 : Nat) == cfg.state_idx &&
            decide (([some 0] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 0] : List (Option Nat)) ≠ [some 8] := by
      intro h; injection h with h1 _; injection h1 with h2; exact (by decide : (0 : Nat) ≠ 8) h2
    simp [h_ne']
  have hNotMatchOne : entryMatchesConfig compareUnary_s5_one cfg = false := by
    show ((5 : Nat) == cfg.state_idx &&
            decide (([some 1] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 1] : List (Option Nat)) ≠ [some 8] := by
      intro h; injection h with h1 _; injection h1 with h2; exact (by decide : (1 : Nat) ≠ 8) h2
    simp [h_ne']
  have hMatchEight : entryMatchesConfig compareUnary_s5_eight cfg = true := by
    show ((5 : Nat) == 5 &&
            decide (([some 8] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = true
    rw [hSymTape]; rfl
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (5 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (5 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    compareUnary_block_2_find_none cfg (by show (5 : Nat) ≠ 2; decide)
  have h_block_3_none :=
    compareUnary_block_3_find_none sig cfg (by show (5 : Nat) ≠ 3; decide)
  have h_block_4_none :=
    compareUnary_block_4_find_none sig cfg (by show (5 : Nat) ≠ 4; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.find?_append, h_block_3_none, Option.none_or,
      List.find?_append, h_block_4_none, Option.none_or,
      List.cons_append, List.find?_cons, hNotMatchZero,
      List.cons_append, List.find?_cons, hNotMatchOne,
      List.cons_append, List.find?_cons, hMatchEight]
  rfl

/-! ### State-6 step lemmas

State 6 cleans up the cursor before halting in reject state. -/

theorem compareUnaryAtMarkerTM_state6_step_cursor (sig : Nat) (left right : List Nat)
    (head : Nat) (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = 11) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 6, tapes := [(left, head, right)] } =
      some { state_idx := 7
             tapes := [writeCurrentTapeSymbol (left, head, right) (some 0)] } := by
  set cfg : FlatTMConfig := { state_idx := 6, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some 11 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig compareUnary_s6_eleven cfg = true := by
    show ((6 : Nat) == 6 &&
            decide (([some 11] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym]; rfl
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (6 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (6 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    compareUnary_block_2_find_none cfg (by show (6 : Nat) ≠ 2; decide)
  have h_block_3_none :=
    compareUnary_block_3_find_none sig cfg (by show (6 : Nat) ≠ 3; decide)
  have h_block_4_none :=
    compareUnary_block_4_find_none sig cfg (by show (6 : Nat) ≠ 4; decide)
  have h_block_5_none :=
    compareUnary_block_5_find_none cfg (by show (6 : Nat) ≠ 5; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.find?_append, h_block_3_none, Option.none_or,
      List.find?_append, h_block_4_none, Option.none_or,
      List.find?_append, h_block_5_none, Option.none_or,
      List.find?_cons, hMatch]
  rfl

theorem compareUnaryAtMarkerTM_state6_step_advance (sig : Nat) (left right : List Nat)
    (head v : Nat) (h_head_lt : head < right.length)
    (h_sym_lt : v < sig)
    (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 11) :
    stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 6, tapes := [(left, head, right)] } =
      some { state_idx := 6
             tapes := [moveTapeHead (left, head, right) TMMove.Lmove] } := by
  set cfg : FlatTMConfig := { state_idx := 6, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSymTape : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym]
  have hNotMatchEleven : entryMatchesConfig compareUnary_s6_eleven cfg = false := by
    show ((6 : Nat) == cfg.state_idx &&
            decide (([some 11] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some 11] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne']
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ 11)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, decide_eq_true h_ne⟩
  have hFindAdv :
      (((List.range sig).filter (fun w => decide (w ≠ 11))).map compareUnary_s6_advance).find?
          (fun e => entryMatchesConfig e cfg) =
        some (compareUnary_s6_advance v) := by
    refine find_singleSomeEntry_match_state cfg 6 v _ compareUnary_s6_advance rfl hSymTape
      (fun _ => rfl) (fun _ => rfl) hvInFilter ?_
    intro w _ hwv
    show ((6 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSymTape]
    have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact hwv h2
    simp [h_ne']
  have h_block_0_none :=
    compareUnary_block_0_find_none cfg (by show (6 : Nat) ≠ 0; decide)
  have h_block_1_none :=
    compareUnary_block_1_find_none sig cfg (by show (6 : Nat) ≠ 1; decide)
  have h_block_2_none :=
    compareUnary_block_2_find_none cfg (by show (6 : Nat) ≠ 2; decide)
  have h_block_3_none :=
    compareUnary_block_3_find_none sig cfg (by show (6 : Nat) ≠ 3; decide)
  have h_block_4_none :=
    compareUnary_block_4_find_none sig cfg (by show (6 : Nat) ≠ 4; decide)
  have h_block_5_none :=
    compareUnary_block_5_find_none cfg (by show (6 : Nat) ≠ 5; decide)
  show Option.bind ((compareUnaryAtMarkerTM sig).trans.find? _) (applyTransitionEntry cfg) = _
  show Option.bind ((compareUnaryAtMarkerTM_trans sig).find? _) _ = _
  unfold compareUnaryAtMarkerTM_trans
  rw [List.find?_append, h_block_0_none, Option.none_or,
      List.find?_append, h_block_1_none, Option.none_or,
      List.find?_append, h_block_2_none, Option.none_or,
      List.find?_append, h_block_3_none, Option.none_or,
      List.find?_append, h_block_4_none, Option.none_or,
      List.find?_append, h_block_5_none, Option.none_or,
      List.find?_cons, hNotMatchEleven, hFindAdv]
  rfl

/-! ### Halting state lemmas -/

theorem compareUnaryAtMarkerTM_state0_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (compareUnaryAtMarkerTM sig)
        { state_idx := 0, tapes := cfg_tapes } = false := rfl

theorem compareUnaryAtMarkerTM_state1_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (compareUnaryAtMarkerTM sig)
        { state_idx := 1, tapes := cfg_tapes } = false := rfl

theorem compareUnaryAtMarkerTM_state2_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (compareUnaryAtMarkerTM sig)
        { state_idx := 2, tapes := cfg_tapes } = false := rfl

theorem compareUnaryAtMarkerTM_state3_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (compareUnaryAtMarkerTM sig)
        { state_idx := 3, tapes := cfg_tapes } = false := rfl

theorem compareUnaryAtMarkerTM_state4_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (compareUnaryAtMarkerTM sig)
        { state_idx := 4, tapes := cfg_tapes } = false := rfl

theorem compareUnaryAtMarkerTM_state5_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (compareUnaryAtMarkerTM sig)
        { state_idx := 5, tapes := cfg_tapes } = false := rfl

theorem compareUnaryAtMarkerTM_state6_not_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (compareUnaryAtMarkerTM sig)
        { state_idx := 6, tapes := cfg_tapes } = false := rfl

/-- State 7 of `compareUnaryAtMarkerTM` is a halt-reject state. -/
theorem compareUnaryAtMarkerTM_state7_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (compareUnaryAtMarkerTM sig)
        { state_idx := 7, tapes := cfg_tapes } = true := rfl

/-- State 8 of `compareUnaryAtMarkerTM` is a halt-accept state. -/
theorem compareUnaryAtMarkerTM_state8_halting (sig : Nat)
    (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (compareUnaryAtMarkerTM sig)
        { state_idx := 8, tapes := cfg_tapes } = true := rfl

/-! ### Per-state `runFlatTM` unfold helpers

Mirror of the copyUnary helpers: each says that if a step from
`(state s, tapes)` produces `cfg'`, then running `n + 1` steps from
that state equals running `n` steps from `cfg'`. -/

private theorem runFlatTM_compareUnary_state0_unfold
    (sig n : Nat) (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 0, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (compareUnaryAtMarkerTM sig)
        { state_idx := 0, tapes := tapes } =
      runFlatTM n (compareUnaryAtMarkerTM sig) cfg' := by
  show (if haltingStateReached (compareUnaryAtMarkerTM sig)
            { state_idx := 0, tapes := tapes } = true then
          some { state_idx := 0, tapes := tapes }
        else
          match stepFlatTM (compareUnaryAtMarkerTM sig)
              { state_idx := 0, tapes := tapes } with
          | none => some { state_idx := 0, tapes := tapes }
          | some cfg' => runFlatTM n (compareUnaryAtMarkerTM sig) cfg') =
    runFlatTM n (compareUnaryAtMarkerTM sig) cfg'
  rw [compareUnaryAtMarkerTM_state0_not_halting, h_step]
  rfl

private theorem runFlatTM_compareUnary_state1_unfold
    (sig n : Nat) (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 1, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (compareUnaryAtMarkerTM sig)
        { state_idx := 1, tapes := tapes } =
      runFlatTM n (compareUnaryAtMarkerTM sig) cfg' := by
  show (if haltingStateReached (compareUnaryAtMarkerTM sig)
            { state_idx := 1, tapes := tapes } = true then
          some { state_idx := 1, tapes := tapes }
        else
          match stepFlatTM (compareUnaryAtMarkerTM sig)
              { state_idx := 1, tapes := tapes } with
          | none => some { state_idx := 1, tapes := tapes }
          | some cfg' => runFlatTM n (compareUnaryAtMarkerTM sig) cfg') =
    runFlatTM n (compareUnaryAtMarkerTM sig) cfg'
  rw [compareUnaryAtMarkerTM_state1_not_halting, h_step]
  rfl

private theorem runFlatTM_compareUnary_state2_unfold
    (sig n : Nat) (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 2, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (compareUnaryAtMarkerTM sig)
        { state_idx := 2, tapes := tapes } =
      runFlatTM n (compareUnaryAtMarkerTM sig) cfg' := by
  show (if haltingStateReached (compareUnaryAtMarkerTM sig)
            { state_idx := 2, tapes := tapes } = true then
          some { state_idx := 2, tapes := tapes }
        else
          match stepFlatTM (compareUnaryAtMarkerTM sig)
              { state_idx := 2, tapes := tapes } with
          | none => some { state_idx := 2, tapes := tapes }
          | some cfg' => runFlatTM n (compareUnaryAtMarkerTM sig) cfg') =
    runFlatTM n (compareUnaryAtMarkerTM sig) cfg'
  rw [compareUnaryAtMarkerTM_state2_not_halting, h_step]
  rfl

private theorem runFlatTM_compareUnary_state3_unfold
    (sig n : Nat) (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 3, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (compareUnaryAtMarkerTM sig)
        { state_idx := 3, tapes := tapes } =
      runFlatTM n (compareUnaryAtMarkerTM sig) cfg' := by
  show (if haltingStateReached (compareUnaryAtMarkerTM sig)
            { state_idx := 3, tapes := tapes } = true then
          some { state_idx := 3, tapes := tapes }
        else
          match stepFlatTM (compareUnaryAtMarkerTM sig)
              { state_idx := 3, tapes := tapes } with
          | none => some { state_idx := 3, tapes := tapes }
          | some cfg' => runFlatTM n (compareUnaryAtMarkerTM sig) cfg') =
    runFlatTM n (compareUnaryAtMarkerTM sig) cfg'
  rw [compareUnaryAtMarkerTM_state3_not_halting, h_step]
  rfl

private theorem runFlatTM_compareUnary_state4_unfold
    (sig n : Nat) (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 4, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (compareUnaryAtMarkerTM sig)
        { state_idx := 4, tapes := tapes } =
      runFlatTM n (compareUnaryAtMarkerTM sig) cfg' := by
  show (if haltingStateReached (compareUnaryAtMarkerTM sig)
            { state_idx := 4, tapes := tapes } = true then
          some { state_idx := 4, tapes := tapes }
        else
          match stepFlatTM (compareUnaryAtMarkerTM sig)
              { state_idx := 4, tapes := tapes } with
          | none => some { state_idx := 4, tapes := tapes }
          | some cfg' => runFlatTM n (compareUnaryAtMarkerTM sig) cfg') =
    runFlatTM n (compareUnaryAtMarkerTM sig) cfg'
  rw [compareUnaryAtMarkerTM_state4_not_halting, h_step]
  rfl

private theorem runFlatTM_compareUnary_state5_unfold
    (sig n : Nat) (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 5, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (compareUnaryAtMarkerTM sig)
        { state_idx := 5, tapes := tapes } =
      runFlatTM n (compareUnaryAtMarkerTM sig) cfg' := by
  show (if haltingStateReached (compareUnaryAtMarkerTM sig)
            { state_idx := 5, tapes := tapes } = true then
          some { state_idx := 5, tapes := tapes }
        else
          match stepFlatTM (compareUnaryAtMarkerTM sig)
              { state_idx := 5, tapes := tapes } with
          | none => some { state_idx := 5, tapes := tapes }
          | some cfg' => runFlatTM n (compareUnaryAtMarkerTM sig) cfg') =
    runFlatTM n (compareUnaryAtMarkerTM sig) cfg'
  rw [compareUnaryAtMarkerTM_state5_not_halting, h_step]
  rfl

private theorem runFlatTM_compareUnary_state6_unfold
    (sig n : Nat) (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (compareUnaryAtMarkerTM sig)
        { state_idx := 6, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (compareUnaryAtMarkerTM sig)
        { state_idx := 6, tapes := tapes } =
      runFlatTM n (compareUnaryAtMarkerTM sig) cfg' := by
  show (if haltingStateReached (compareUnaryAtMarkerTM sig)
            { state_idx := 6, tapes := tapes } = true then
          some { state_idx := 6, tapes := tapes }
        else
          match stepFlatTM (compareUnaryAtMarkerTM sig)
              { state_idx := 6, tapes := tapes } with
          | none => some { state_idx := 6, tapes := tapes }
          | some cfg' => runFlatTM n (compareUnaryAtMarkerTM sig) cfg') =
    runFlatTM n (compareUnaryAtMarkerTM sig) cfg'
  rw [compareUnaryAtMarkerTM_state6_not_halting, h_step]
  rfl

/-! ### Phase scan lemmas

Each scan phase of `compareUnaryAtMarkerTM` (states 1, 2, 3, 4, 5, 6)
is a uniform "advance until match" loop. We state each as a
self-contained `_run` lemma by induction on the scan distance (gap). -/

/-- **Phase 1** (state 1): right-scan to marker `7`. From
`(state 1, head = p, right)` with `right.get ⟨p + gap, _⟩ = 7` and
intermediate cells `< sig ∧ ≠ 7`, in `gap + 1` steps we reach
`(state 2, head = p + gap + 1, right)`. -/
theorem compareUnaryAtMarkerTM_state1_phase_run
    (sig : Nat) (left right : List Nat) :
    ∀ (gap p : Nat) (h_in_range : p + gap < right.length),
      right.get ⟨p + gap, h_in_range⟩ = 7 →
      (∀ k, k < gap → ∃ (h_lt : p + k < right.length),
          right.get ⟨p + k, h_lt⟩ < sig ∧
            right.get ⟨p + k, h_lt⟩ ≠ 7) →
      runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 1, tapes := [(left, p, right)] } =
        some { state_idx := 2, tapes := [(left, p + gap + 1, right)] }
  | 0, p, h_in_range, h_marker, _ => by
      have h_lt : p < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨p, h_lt⟩ = 7 := by
        have heq : (⟨p + 0, h_in_range⟩ : Fin right.length) = ⟨p, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero p)
        rw [heq] at h_marker; exact h_marker
      rw [runFlatTM_compareUnary_state1_unfold sig 0 _ _
        (compareUnaryAtMarkerTM_state1_step_match sig left right p h_lt h_get)]
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
      have hih := compareUnaryAtMarkerTM_state1_phase_run sig left right gap (p + 1)
        h_in_range' h_marker' h_mid'
      rw [runFlatTM_compareUnary_state1_unfold sig (gap + 1) _ _
        (compareUnaryAtMarkerTM_state1_step_advance sig left right p
          (right.get ⟨p, h_p_lt⟩) h_p_lt h_get_p rfl h_get_p_ne)]
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 1, tapes := [moveTapeHead (left, p, right) TMMove.Rmove] } = _
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 1, tapes := [(left, p + 1, right)] } = _
      rw [hih]
      show (some { state_idx := 2, tapes := [(left, (p + 1) + gap + 1, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 2, tapes := [(left, p + (gap + 1) + 1, right)] }
      have h_eq : (p + 1) + gap + 1 = p + (gap + 1) + 1 := by
        rw [Nat.add_right_comm p 1 gap]; rfl
      rw [h_eq]
  termination_by gap _ _ _ _ => gap

/-- **Phase 2-one** (state 2): right-scan past `0`s to first `1`, then
write `0` and L-move. From `(state 2, p, right)` with
`right.get ⟨p + gap, _⟩ = 1` and `right.get ⟨p + k, _⟩ = 0` for `k < gap`,
in `gap + 1` steps we reach
`(state 3, p + gap - 1, right.set (p + gap) 0)`. -/
theorem compareUnaryAtMarkerTM_state2_phase_run_one
    (sig : Nat) (left right : List Nat) :
    ∀ (gap p : Nat) (h_in_range : p + gap < right.length),
      right.get ⟨p + gap, h_in_range⟩ = 1 →
      (∀ k, k < gap → ∃ (h_lt : p + k < right.length),
          right.get ⟨p + k, h_lt⟩ = 0) →
      runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 2, tapes := [(left, p, right)] } =
        some { state_idx := 3
               tapes := [(left, (p + gap) - 1, right.set (p + gap) 0)] }
  | 0, p, h_in_range, h_one, _ => by
      have h_lt : p < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨p, h_lt⟩ = 1 := by
        have heq : (⟨p + 0, h_in_range⟩ : Fin right.length) = ⟨p, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero p)
        rw [heq] at h_one; exact h_one
      have h_write : writeCurrentTapeSymbol (left, p, right) (some 0) =
          (left, p, right.set p 0) := by
        have h_w : writeCurrentTapeSymbol (left, p, right) (some 0) =
            (left, p, right.take p ++ (0 : Nat) :: right.drop (p + 1)) := by
          simp [writeCurrentTapeSymbol, h_lt]
        rw [h_w, List.set_eq_take_append_cons_drop, if_pos h_lt]
      rw [runFlatTM_compareUnary_state2_unfold sig 0 _ _
        (compareUnaryAtMarkerTM_state2_step_one sig left right p h_lt h_get)]
      show (some { state_idx := 3
                   tapes := [moveTapeHead
                     (writeCurrentTapeSymbol (left, p, right) (some 0))
                     TMMove.Lmove] }
              : Option FlatTMConfig) =
        some { state_idx := 3
               tapes := [(left, (p + 0) - 1, right.set (p + 0) 0)] }
      rw [h_write]
      simp only [Nat.add_zero]
      rfl
  | gap + 1, p, h_in_range, h_one, h_mid => by
      have h_p_lt : p < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right p (gap + 1)) h_in_range
      rcases h_mid 0 (Nat.zero_lt_succ _) with ⟨h_p_lt', h_sym_zero⟩
      have heq0 : (⟨p + 0, h_p_lt'⟩ : Fin right.length) = ⟨p, h_p_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero p)
      have h_get_p_zero : right.get ⟨p, h_p_lt⟩ = 0 := by
        rw [heq0] at h_sym_zero; exact h_sym_zero
      have h_in_range' : (p + 1) + gap < right.length := by
        rw [Nat.add_right_comm]; exact h_in_range
      have h_one' : right.get ⟨(p + 1) + gap, h_in_range'⟩ = 1 := by
        have heq : (⟨(p + 1) + gap, h_in_range'⟩ : Fin right.length) =
            ⟨p + (gap + 1), h_in_range⟩ := by
          apply Fin.eq_of_val_eq
          show (p + 1) + gap = p + (gap + 1)
          rw [Nat.add_right_comm, Nat.add_assoc]
        rw [heq]; exact h_one
      have h_mid' : ∀ k, k < gap → ∃ (h_lt : (p + 1) + k < right.length),
          right.get ⟨(p + 1) + k, h_lt⟩ = 0 := by
        intro k hk
        rcases h_mid (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk, h1⟩
        have hShift : p + (k + 1) = (p + 1) + k := by
          rw [Nat.add_right_comm]; rfl
        have h_kk' : (p + 1) + k < right.length := hShift ▸ h_kk
        refine ⟨h_kk', ?_⟩
        have heq : (⟨(p + 1) + k, h_kk'⟩ : Fin right.length) =
            ⟨p + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
        rw [heq]; exact h1
      have hih := compareUnaryAtMarkerTM_state2_phase_run_one sig left right gap (p + 1)
        h_in_range' h_one' h_mid'
      rw [runFlatTM_compareUnary_state2_unfold sig (gap + 1) _ _
        (compareUnaryAtMarkerTM_state2_step_zero sig left right p h_p_lt h_get_p_zero)]
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 2, tapes := [moveTapeHead (left, p, right) TMMove.Rmove] } = _
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 2, tapes := [(left, p + 1, right)] } = _
      rw [hih]
      show (some { state_idx := 3
                   tapes := [(left, ((p + 1) + gap) - 1,
                     right.set ((p + 1) + gap) 0)] }
              : Option FlatTMConfig) =
        some { state_idx := 3
               tapes := [(left, (p + (gap + 1)) - 1, right.set (p + (gap + 1)) 0)] }
      have h_eq : (p + 1) + gap = p + (gap + 1) := by
        rw [Nat.add_right_comm]; rfl
      rw [h_eq]
  termination_by gap _ _ _ _ => gap

/-- **Phase 2-eight** (state 2): right-scan past `0`s to marker `8`,
transition to state 6. From `(state 2, p, right)` with
`right.get ⟨p + c, _⟩ = 8` and `right.get ⟨p + k, _⟩ = 0` for `k < c`,
in `c + 1` steps we reach `(state 6, p + c, right)`. -/
theorem compareUnaryAtMarkerTM_state2_phase_run_eight
    (sig : Nat) (left right : List Nat) :
    ∀ (c p : Nat) (h_in_range : p + c < right.length),
      right.get ⟨p + c, h_in_range⟩ = 8 →
      (∀ k, k < c → ∃ (h_lt : p + k < right.length),
          right.get ⟨p + k, h_lt⟩ = 0) →
      runFlatTM (c + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 2, tapes := [(left, p, right)] } =
        some { state_idx := 6, tapes := [(left, p + c, right)] }
  | 0, p, h_in_range, h_eight, _ => by
      have h_lt : p < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨p, h_lt⟩ = 8 := by
        have heq : (⟨p + 0, h_in_range⟩ : Fin right.length) = ⟨p, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero p)
        rw [heq] at h_eight; exact h_eight
      rw [runFlatTM_compareUnary_state2_unfold sig 0 _ _
        (compareUnaryAtMarkerTM_state2_step_eight sig left right p h_lt h_get)]
      show (some { state_idx := 6, tapes := [(left, p, right)] } : Option FlatTMConfig) =
        some { state_idx := 6, tapes := [(left, p + 0, right)] }
      rw [Nat.add_zero]
  | c + 1, p, h_in_range, h_eight, h_mid => by
      have h_p_lt : p < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right p (c + 1)) h_in_range
      rcases h_mid 0 (Nat.zero_lt_succ _) with ⟨h_p_lt', h_sym_zero⟩
      have heq0 : (⟨p + 0, h_p_lt'⟩ : Fin right.length) = ⟨p, h_p_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero p)
      have h_get_p_zero : right.get ⟨p, h_p_lt⟩ = 0 := by
        rw [heq0] at h_sym_zero; exact h_sym_zero
      have h_in_range' : (p + 1) + c < right.length := by
        rw [Nat.add_right_comm]; exact h_in_range
      have h_eight' : right.get ⟨(p + 1) + c, h_in_range'⟩ = 8 := by
        have heq : (⟨(p + 1) + c, h_in_range'⟩ : Fin right.length) =
            ⟨p + (c + 1), h_in_range⟩ := by
          apply Fin.eq_of_val_eq
          show (p + 1) + c = p + (c + 1)
          rw [Nat.add_right_comm, Nat.add_assoc]
        rw [heq]; exact h_eight
      have h_mid' : ∀ k, k < c → ∃ (h_lt : (p + 1) + k < right.length),
          right.get ⟨(p + 1) + k, h_lt⟩ = 0 := by
        intro k hk
        rcases h_mid (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk, h1⟩
        have hShift : p + (k + 1) = (p + 1) + k := by
          rw [Nat.add_right_comm]; rfl
        have h_kk' : (p + 1) + k < right.length := hShift ▸ h_kk
        refine ⟨h_kk', ?_⟩
        have heq : (⟨(p + 1) + k, h_kk'⟩ : Fin right.length) =
            ⟨p + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
        rw [heq]; exact h1
      have hih := compareUnaryAtMarkerTM_state2_phase_run_eight sig left right c (p + 1)
        h_in_range' h_eight' h_mid'
      rw [runFlatTM_compareUnary_state2_unfold sig (c + 1) _ _
        (compareUnaryAtMarkerTM_state2_step_zero sig left right p h_p_lt h_get_p_zero)]
      show runFlatTM (c + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 2, tapes := [moveTapeHead (left, p, right) TMMove.Rmove] } = _
      show runFlatTM (c + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 2, tapes := [(left, p + 1, right)] } = _
      rw [hih]
      show (some { state_idx := 6, tapes := [(left, (p + 1) + c, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 6, tapes := [(left, p + (c + 1), right)] }
      have h_eq : (p + 1) + c = p + (c + 1) := by
        rw [Nat.add_right_comm]; rfl
      rw [h_eq]
  termination_by c _ _ _ _ => c

/-- **Phase 3** (state 3): left-scan to cursor `11`, write `0` and
R-move. From `(state 3, head, right)` with `right.get ⟨head - gap, _⟩ = 11`
and intermediate cells `< sig ∧ ≠ 11`, in `gap + 1` steps we reach
`(state 0, head - gap + 1, right.set (head - gap) 0)`. -/
theorem compareUnaryAtMarkerTM_state3_phase_run
    (sig : Nat) (left right : List Nat) :
    ∀ (gap head : Nat) (h_gap_le : gap ≤ head)
      (h_head_lt : head < right.length)
      (h_in_range : head - gap < right.length),
      right.get ⟨head - gap, h_in_range⟩ = 11 →
      (∀ k, k < gap → ∃ (h : head - k < right.length),
        right.get ⟨head - k, h⟩ < sig ∧
          right.get ⟨head - k, h⟩ ≠ 11) →
      runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 3, tapes := [(left, head, right)] } =
        some { state_idx := 0
               tapes := [(left, head - gap + 1, right.set (head - gap) 0)] }
  | 0, head, _, h_head_lt, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := h_head_lt
      have h_get : right.get ⟨head, h_lt⟩ = 11 := by
        have heq : (⟨head - 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.sub_zero head)
        rw [heq] at h_get_target; exact h_get_target
      have h_write : writeCurrentTapeSymbol (left, head, right) (some 0) =
          (left, head, right.set head 0) := by
        have h_w : writeCurrentTapeSymbol (left, head, right) (some 0) =
            (left, head, right.take head ++ (0 : Nat) :: right.drop (head + 1)) := by
          simp [writeCurrentTapeSymbol, h_lt]
        rw [h_w, List.set_eq_take_append_cons_drop, if_pos h_lt]
      rw [runFlatTM_compareUnary_state3_unfold sig 0 _ _
        (compareUnaryAtMarkerTM_state3_step_cursor sig left right head h_lt h_get)]
      show (some { state_idx := 0
                   tapes := [moveTapeHead
                     (writeCurrentTapeSymbol (left, head, right) (some 0))
                     TMMove.Rmove] }
              : Option FlatTMConfig) =
        some { state_idx := 0
               tapes := [(left, head - 0 + 1, right.set (head - 0) 0)] }
      rw [h_write]
      simp only [Nat.sub_zero]
      rfl
  | gap + 1, head, h_gap_le, h_head_lt, h_in_range, h_get_target, h_before => by
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
      have hih := compareUnaryAtMarkerTM_state3_phase_run sig left right gap (head - 1)
        h_new_gap_le h_new_head h_in_range' h_get_target' h_before'
      rw [runFlatTM_compareUnary_state3_unfold sig (gap + 1) _ _
        (compareUnaryAtMarkerTM_state3_step_advance sig left right head
          (right.get ⟨head, h_head_lt'⟩) h_head_lt' h_get_head rfl h_get_head_ne)]
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 3, tapes := [moveTapeHead (left, head, right) TMMove.Lmove] } = _
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 3, tapes := [(left, head - 1, right)] } = _
      rw [hih]
      show (some { state_idx := 0
                   tapes := [(left, (head - 1) - gap + 1,
                     right.set ((head - 1) - gap) 0)] }
              : Option FlatTMConfig) =
        some { state_idx := 0
               tapes := [(left, head - (gap + 1) + 1, right.set (head - (gap + 1)) 0)] }
      rw [h_sub_swap]
  termination_by gap _ _ _ _ _ _ => gap

/-- **Phase 4** (state 4): right-scan to marker `7`. From
`(state 4, p, right)` with `right.get ⟨p + gap, _⟩ = 7` and intermediate
cells `< sig ∧ ≠ 7`, in `gap + 1` steps we reach
`(state 5, p + gap + 1, right)`. -/
theorem compareUnaryAtMarkerTM_state4_phase_run
    (sig : Nat) (left right : List Nat) :
    ∀ (gap p : Nat) (h_in_range : p + gap < right.length),
      right.get ⟨p + gap, h_in_range⟩ = 7 →
      (∀ k, k < gap → ∃ (h_lt : p + k < right.length),
          right.get ⟨p + k, h_lt⟩ < sig ∧
            right.get ⟨p + k, h_lt⟩ ≠ 7) →
      runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 4, tapes := [(left, p, right)] } =
        some { state_idx := 5, tapes := [(left, p + gap + 1, right)] }
  | 0, p, h_in_range, h_marker, _ => by
      have h_lt : p < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨p, h_lt⟩ = 7 := by
        have heq : (⟨p + 0, h_in_range⟩ : Fin right.length) = ⟨p, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero p)
        rw [heq] at h_marker; exact h_marker
      rw [runFlatTM_compareUnary_state4_unfold sig 0 _ _
        (compareUnaryAtMarkerTM_state4_step_match sig left right p h_lt h_get)]
      show (some { state_idx := 5, tapes := [moveTapeHead (left, p, right) TMMove.Rmove] }
              : Option FlatTMConfig) =
        some { state_idx := 5, tapes := [(left, p + 0 + 1, right)] }
      show (some { state_idx := 5, tapes := [(left, p + 1, right)] } : Option FlatTMConfig) =
        some { state_idx := 5, tapes := [(left, p + 0 + 1, right)] }
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
      have hih := compareUnaryAtMarkerTM_state4_phase_run sig left right gap (p + 1)
        h_in_range' h_marker' h_mid'
      rw [runFlatTM_compareUnary_state4_unfold sig (gap + 1) _ _
        (compareUnaryAtMarkerTM_state4_step_advance sig left right p
          (right.get ⟨p, h_p_lt⟩) h_p_lt h_get_p rfl h_get_p_ne)]
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 4, tapes := [moveTapeHead (left, p, right) TMMove.Rmove] } = _
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 4, tapes := [(left, p + 1, right)] } = _
      rw [hih]
      show (some { state_idx := 5, tapes := [(left, (p + 1) + gap + 1, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 5, tapes := [(left, p + (gap + 1) + 1, right)] }
      have h_eq : (p + 1) + gap + 1 = p + (gap + 1) + 1 := by
        rw [Nat.add_right_comm p 1 gap]; rfl
      rw [h_eq]
  termination_by gap _ _ _ _ => gap

/-- **Phase 5-match** (state 5): right-scan past `0`s to marker `8`,
halt-accept (state 8). From `(state 5, p, right)` with
`right.get ⟨p + c, _⟩ = 8` and `right.get ⟨p + k, _⟩ = 0` for `k < c`,
in `c + 1` steps we reach `(state 8, p + c, right)`. -/
theorem compareUnaryAtMarkerTM_state5_phase_run_match
    (sig : Nat) (left right : List Nat) :
    ∀ (c p : Nat) (h_in_range : p + c < right.length),
      right.get ⟨p + c, h_in_range⟩ = 8 →
      (∀ k, k < c → ∃ (h_lt : p + k < right.length),
          right.get ⟨p + k, h_lt⟩ = 0) →
      runFlatTM (c + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 5, tapes := [(left, p, right)] } =
        some { state_idx := 8, tapes := [(left, p + c, right)] }
  | 0, p, h_in_range, h_eight, _ => by
      have h_lt : p < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨p, h_lt⟩ = 8 := by
        have heq : (⟨p + 0, h_in_range⟩ : Fin right.length) = ⟨p, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero p)
        rw [heq] at h_eight; exact h_eight
      rw [runFlatTM_compareUnary_state5_unfold sig 0 _ _
        (compareUnaryAtMarkerTM_state5_step_eight sig left right p h_lt h_get)]
      show (some { state_idx := 8, tapes := [(left, p, right)] } : Option FlatTMConfig) =
        some { state_idx := 8, tapes := [(left, p + 0, right)] }
      rw [Nat.add_zero]
  | c + 1, p, h_in_range, h_eight, h_mid => by
      have h_p_lt : p < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right p (c + 1)) h_in_range
      rcases h_mid 0 (Nat.zero_lt_succ _) with ⟨h_p_lt', h_sym_zero⟩
      have heq0 : (⟨p + 0, h_p_lt'⟩ : Fin right.length) = ⟨p, h_p_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero p)
      have h_get_p_zero : right.get ⟨p, h_p_lt⟩ = 0 := by
        rw [heq0] at h_sym_zero; exact h_sym_zero
      have h_in_range' : (p + 1) + c < right.length := by
        rw [Nat.add_right_comm]; exact h_in_range
      have h_eight' : right.get ⟨(p + 1) + c, h_in_range'⟩ = 8 := by
        have heq : (⟨(p + 1) + c, h_in_range'⟩ : Fin right.length) =
            ⟨p + (c + 1), h_in_range⟩ := by
          apply Fin.eq_of_val_eq
          show (p + 1) + c = p + (c + 1)
          rw [Nat.add_right_comm, Nat.add_assoc]
        rw [heq]; exact h_eight
      have h_mid' : ∀ k, k < c → ∃ (h_lt : (p + 1) + k < right.length),
          right.get ⟨(p + 1) + k, h_lt⟩ = 0 := by
        intro k hk
        rcases h_mid (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk, h1⟩
        have hShift : p + (k + 1) = (p + 1) + k := by
          rw [Nat.add_right_comm]; rfl
        have h_kk' : (p + 1) + k < right.length := hShift ▸ h_kk
        refine ⟨h_kk', ?_⟩
        have heq : (⟨(p + 1) + k, h_kk'⟩ : Fin right.length) =
            ⟨p + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
        rw [heq]; exact h1
      have hih := compareUnaryAtMarkerTM_state5_phase_run_match sig left right c (p + 1)
        h_in_range' h_eight' h_mid'
      rw [runFlatTM_compareUnary_state5_unfold sig (c + 1) _ _
        (compareUnaryAtMarkerTM_state5_step_zero sig left right p h_p_lt h_get_p_zero)]
      show runFlatTM (c + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 5, tapes := [moveTapeHead (left, p, right) TMMove.Rmove] } = _
      show runFlatTM (c + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 5, tapes := [(left, p + 1, right)] } = _
      rw [hih]
      show (some { state_idx := 8, tapes := [(left, (p + 1) + c, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 8, tapes := [(left, p + (c + 1), right)] }
      have h_eq : (p + 1) + c = p + (c + 1) := by
        rw [Nat.add_right_comm]; rfl
      rw [h_eq]
  termination_by c _ _ _ _ => c

/-- **Phase 5-mismatch** (state 5): right-scan past `0`s to a `1`,
halt-reject (state 7). From `(state 5, p, right)` with
`right.get ⟨p + gap, _⟩ = 1` and `right.get ⟨p + k, _⟩ = 0` for `k < gap`,
in `gap + 1` steps we reach `(state 7, p + gap, right)`. -/
theorem compareUnaryAtMarkerTM_state5_phase_run_mismatch
    (sig : Nat) (left right : List Nat) :
    ∀ (gap p : Nat) (h_in_range : p + gap < right.length),
      right.get ⟨p + gap, h_in_range⟩ = 1 →
      (∀ k, k < gap → ∃ (h_lt : p + k < right.length),
          right.get ⟨p + k, h_lt⟩ = 0) →
      runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 5, tapes := [(left, p, right)] } =
        some { state_idx := 7, tapes := [(left, p + gap, right)] }
  | 0, p, h_in_range, h_one, _ => by
      have h_lt : p < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨p, h_lt⟩ = 1 := by
        have heq : (⟨p + 0, h_in_range⟩ : Fin right.length) = ⟨p, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero p)
        rw [heq] at h_one; exact h_one
      rw [runFlatTM_compareUnary_state5_unfold sig 0 _ _
        (compareUnaryAtMarkerTM_state5_step_one sig left right p h_lt h_get)]
      show (some { state_idx := 7, tapes := [(left, p, right)] } : Option FlatTMConfig) =
        some { state_idx := 7, tapes := [(left, p + 0, right)] }
      rw [Nat.add_zero]
  | gap + 1, p, h_in_range, h_one, h_mid => by
      have h_p_lt : p < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right p (gap + 1)) h_in_range
      rcases h_mid 0 (Nat.zero_lt_succ _) with ⟨h_p_lt', h_sym_zero⟩
      have heq0 : (⟨p + 0, h_p_lt'⟩ : Fin right.length) = ⟨p, h_p_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero p)
      have h_get_p_zero : right.get ⟨p, h_p_lt⟩ = 0 := by
        rw [heq0] at h_sym_zero; exact h_sym_zero
      have h_in_range' : (p + 1) + gap < right.length := by
        rw [Nat.add_right_comm]; exact h_in_range
      have h_one' : right.get ⟨(p + 1) + gap, h_in_range'⟩ = 1 := by
        have heq : (⟨(p + 1) + gap, h_in_range'⟩ : Fin right.length) =
            ⟨p + (gap + 1), h_in_range⟩ := by
          apply Fin.eq_of_val_eq
          show (p + 1) + gap = p + (gap + 1)
          rw [Nat.add_right_comm, Nat.add_assoc]
        rw [heq]; exact h_one
      have h_mid' : ∀ k, k < gap → ∃ (h_lt : (p + 1) + k < right.length),
          right.get ⟨(p + 1) + k, h_lt⟩ = 0 := by
        intro k hk
        rcases h_mid (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk, h1⟩
        have hShift : p + (k + 1) = (p + 1) + k := by
          rw [Nat.add_right_comm]; rfl
        have h_kk' : (p + 1) + k < right.length := hShift ▸ h_kk
        refine ⟨h_kk', ?_⟩
        have heq : (⟨(p + 1) + k, h_kk'⟩ : Fin right.length) =
            ⟨p + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
        rw [heq]; exact h1
      have hih := compareUnaryAtMarkerTM_state5_phase_run_mismatch sig left right gap (p + 1)
        h_in_range' h_one' h_mid'
      rw [runFlatTM_compareUnary_state5_unfold sig (gap + 1) _ _
        (compareUnaryAtMarkerTM_state5_step_zero sig left right p h_p_lt h_get_p_zero)]
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 5, tapes := [moveTapeHead (left, p, right) TMMove.Rmove] } = _
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 5, tapes := [(left, p + 1, right)] } = _
      rw [hih]
      show (some { state_idx := 7, tapes := [(left, (p + 1) + gap, right)] }
              : Option FlatTMConfig) =
        some { state_idx := 7, tapes := [(left, p + (gap + 1), right)] }
      have h_eq : (p + 1) + gap = p + (gap + 1) := by
        rw [Nat.add_right_comm]; rfl
      rw [h_eq]
  termination_by gap _ _ _ _ => gap

/-- **Phase 6** (state 6): left-scan to cursor `11`, write `0`,
halt-reject (state 7). From `(state 6, head, right)` with
`right.get ⟨head - gap, _⟩ = 11` and intermediate cells `< sig ∧ ≠ 11`,
in `gap + 1` steps we reach
`(state 7, head - gap, right.set (head - gap) 0)`. -/
theorem compareUnaryAtMarkerTM_state6_phase_run
    (sig : Nat) (left right : List Nat) :
    ∀ (gap head : Nat) (h_gap_le : gap ≤ head)
      (h_head_lt : head < right.length)
      (h_in_range : head - gap < right.length),
      right.get ⟨head - gap, h_in_range⟩ = 11 →
      (∀ k, k < gap → ∃ (h : head - k < right.length),
        right.get ⟨head - k, h⟩ < sig ∧
          right.get ⟨head - k, h⟩ ≠ 11) →
      runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 6, tapes := [(left, head, right)] } =
        some { state_idx := 7
               tapes := [(left, head - gap, right.set (head - gap) 0)] }
  | 0, head, _, h_head_lt, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := h_head_lt
      have h_get : right.get ⟨head, h_lt⟩ = 11 := by
        have heq : (⟨head - 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.sub_zero head)
        rw [heq] at h_get_target; exact h_get_target
      have h_write : writeCurrentTapeSymbol (left, head, right) (some 0) =
          (left, head, right.set head 0) := by
        have h_w : writeCurrentTapeSymbol (left, head, right) (some 0) =
            (left, head, right.take head ++ (0 : Nat) :: right.drop (head + 1)) := by
          simp [writeCurrentTapeSymbol, h_lt]
        rw [h_w, List.set_eq_take_append_cons_drop, if_pos h_lt]
      rw [runFlatTM_compareUnary_state6_unfold sig 0 _ _
        (compareUnaryAtMarkerTM_state6_step_cursor sig left right head h_lt h_get)]
      show (some { state_idx := 7
                   tapes := [writeCurrentTapeSymbol (left, head, right) (some 0)] }
              : Option FlatTMConfig) =
        some { state_idx := 7
               tapes := [(left, head - 0, right.set (head - 0) 0)] }
      rw [h_write]
      simp only [Nat.sub_zero]
  | gap + 1, head, h_gap_le, h_head_lt, h_in_range, h_get_target, h_before => by
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
      have hih := compareUnaryAtMarkerTM_state6_phase_run sig left right gap (head - 1)
        h_new_gap_le h_new_head h_in_range' h_get_target' h_before'
      rw [runFlatTM_compareUnary_state6_unfold sig (gap + 1) _ _
        (compareUnaryAtMarkerTM_state6_step_advance sig left right head
          (right.get ⟨head, h_head_lt'⟩) h_head_lt' h_get_head rfl h_get_head_ne)]
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 6, tapes := [moveTapeHead (left, head, right) TMMove.Lmove] } = _
      show runFlatTM (gap + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 6, tapes := [(left, head - 1, right)] } = _
      rw [hih]
      show (some { state_idx := 7
                   tapes := [(left, (head - 1) - gap,
                     right.set ((head - 1) - gap) 0)] }
              : Option FlatTMConfig) =
        some { state_idx := 7
               tapes := [(left, head - (gap + 1), right.set (head - (gap + 1)) 0)] }
      rw [h_sub_swap]
  termination_by gap _ _ _ _ _ _ => gap

/-! ### Tape-position helpers for the iteration proof -/

/-- The cursor-write form returned by `state0_step_one` equals
`right.set h 11`. (Reused name from `CopyUnary`; this is the
`writeCurrentTapeSymbol` ↦ `set` bridge.) -/
private theorem cursorWrite_eq_set' (right : List Nat) (h : Nat)
    (h_h_lt : h < right.length) :
    right.take h ++ (11 : Nat) :: right.drop (h + 1) = right.set h 11 := by
  rw [List.set_eq_take_append_cons_drop, if_pos h_h_lt]

/-- After phase 2 writes `0` at position `p` and phase 3 writes `0` at
the cursor `h`, the resulting tape simplifies via `List.set_comm` +
`List.set_set`. -/
private theorem cursor_buf_set_simp_zero (right : List Nat) (h p : Nat)
    (h_ne : h ≠ p) :
    ((right.set h 11).set p 0).set h 0 = (right.set h 0).set p 0 := by
  rw [List.set_comm 0 0 h_ne.symm, List.set_set]

/-- The `writeCurrentTapeSymbol … (some 11)` form equals `right.set h 11`. -/
private theorem writeCur_eleven_eq' (left : List Nat) (h : Nat) (right : List Nat)
    (h_h_lt : h < right.length) :
    writeCurrentTapeSymbol (left, h, right) (some 11) =
      (left, h, right.set h 11) := by
  have h_w : writeCurrentTapeSymbol (left, h, right) (some 11) =
      (left, h, right.take h ++ (11 : Nat) :: right.drop (h + 1)) := by
    simp [writeCurrentTapeSymbol, h_h_lt]
  rw [h_w, cursorWrite_eq_set' right h h_h_lt]

/-- The `writeCurrentTapeSymbol … (some 0)` form equals `right.set h 0`. -/
private theorem writeCur_zero_eq' (left : List Nat) (h : Nat) (right : List Nat)
    (h_h_lt : h < right.length) :
    writeCurrentTapeSymbol (left, h, right) (some 0) =
      (left, h, right.set h 0) := by
  have h_w : writeCurrentTapeSymbol (left, h, right) (some 0) =
      (left, h, right.take h ++ (0 : Nat) :: right.drop (h + 1)) := by
    simp [writeCurrentTapeSymbol, h_h_lt]
  rw [h_w, List.set_eq_take_append_cons_drop, if_pos h_h_lt]

/-! ### Iteration trajectory and run lemma

The state-0→0 trajectory of a single iteration of `compareUnaryAtMarkerTM`
(matching slot `1` against varbuf `1`):

1. `(state 0, h, right)` reads slot `1`: write `11`, Rmove → `(state 1, h+1, rC)`
   where `rC = right.set h 11`. (1 step)
2. `(state 1, h+1, rC)` scans right for `7` at `M`. Phase length: `M - h`.
   End: `(state 2, M+1, rC)`.
3. `(state 2, M+1, rC)` scans right past `i` zeros and erases the `1` at
   `M+1+i`. Phase length: `i + 1`. End: `(state 3, M+i, rD)` where
   `rD = rC.set (M+1+i) 0`.
4. `(state 3, M+i, rD)` scans left to cursor `11` at `h`, writes `0`,
   Rmoves. Phase length: `M+i-h+1`. End: `(state 0, h+1, rE)` where
   `rE = rD.set h 0`.

Total per-iteration steps: `3 + 2 * (M - h) + 2 * i`.
Final tape collapses via `cursor_buf_set_simp_zero` to
`(right.set h 0).set (M+1+i) 0`. -/

/-- Telescoped tape state after `i` compare-unary iterations, starting
from `right` with slot LBM at `p_LBM` and varbuf marker `7` at `M`. -/
def compareUnaryTape_iter (right : List Nat) (p_LBM M : Nat) : Nat → List Nat
  | 0 => right
  | n + 1 =>
    ((compareUnaryTape_iter right p_LBM M n).set (p_LBM + 1 + n) 0).set (M + 1 + n) 0

theorem compareUnaryTape_iter_zero (right : List Nat) (p_LBM M : Nat) :
    compareUnaryTape_iter right p_LBM M 0 = right := rfl

theorem compareUnaryTape_iter_succ (right : List Nat) (p_LBM M n : Nat) :
    compareUnaryTape_iter right p_LBM M (n + 1) =
      ((compareUnaryTape_iter right p_LBM M n).set (p_LBM + 1 + n) 0).set
        (M + 1 + n) 0 := rfl

theorem compareUnaryTape_iter_length (right : List Nat) (p_LBM M : Nat) :
    ∀ n, (compareUnaryTape_iter right p_LBM M n).length = right.length
  | 0 => rfl
  | k + 1 => by
      rw [compareUnaryTape_iter_succ, List.length_set, List.length_set,
          compareUnaryTape_iter_length right p_LBM M k]

/-- For positions `k` that don't match any erased slot or varbuf
position, `compareUnaryTape_iter` is transparent. -/
theorem compareUnaryTape_iter_get_outside
    (right : List Nat) (p_LBM M : Nat) :
    ∀ (n k : Nat) (h_lt_orig : k < right.length)
      (h_lt_iter : k < (compareUnaryTape_iter right p_LBM M n).length),
      (∀ j, j < n → k ≠ p_LBM + 1 + j) →
      (∀ j, j < n → k ≠ M + 1 + j) →
      (compareUnaryTape_iter right p_LBM M n).get ⟨k, h_lt_iter⟩ =
        right.get ⟨k, h_lt_orig⟩
  | 0, k, h_lt_orig, h_lt_iter, _, _ => rfl
  | n + 1, k, h_lt_orig, h_lt_iter, h_ne_slot, h_ne_varbuf => by
      have h_lt_prev :
          k < (compareUnaryTape_iter right p_LBM M n).length := by
        rw [compareUnaryTape_iter_length]; exact h_lt_orig
      have h_ne_slot' : ∀ j, j < n → k ≠ p_LBM + 1 + j :=
        fun j hj => h_ne_slot j (Nat.lt_succ_of_lt hj)
      have h_ne_varbuf' : ∀ j, j < n → k ≠ M + 1 + j :=
        fun j hj => h_ne_varbuf j (Nat.lt_succ_of_lt hj)
      have h_p_ne : p_LBM + 1 + n ≠ k :=
        (h_ne_slot n (Nat.lt_succ_self _)).symm
      have h_q_ne : M + 1 + n ≠ k :=
        (h_ne_varbuf n (Nat.lt_succ_self _)).symm
      simp only [compareUnaryTape_iter_succ]
      show (((compareUnaryTape_iter right p_LBM M n).set (p_LBM + 1 + n) 0).set
              (M + 1 + n) 0)[k]'h_lt_iter = right[k]'h_lt_orig
      rw [List.getElem_set_ne h_q_ne, List.getElem_set_ne h_p_ne]
      show (compareUnaryTape_iter right p_LBM M n).get ⟨k, h_lt_prev⟩ =
        right.get ⟨k, h_lt_orig⟩
      exact compareUnaryTape_iter_get_outside right p_LBM M n k h_lt_orig h_lt_prev
        h_ne_slot' h_ne_varbuf'

/-- After `n` iterations, slot position `p_LBM + 1 + j` for `j < n` is
`0`. Requires the slot region to be disjoint from the varbuf region
(`p_LBM + n ≤ M`). -/
theorem compareUnaryTape_iter_get_slot_zero
    (right : List Nat) (p_LBM M : Nat) :
    ∀ (n j : Nat) (h_j_lt : j < n) (h_dist : p_LBM + n ≤ M)
      (h_lt : p_LBM + 1 + j < (compareUnaryTape_iter right p_LBM M n).length),
      (compareUnaryTape_iter right p_LBM M n).get ⟨p_LBM + 1 + j, h_lt⟩ = 0
  | 0, _, h_j_lt, _, _ => absurd h_j_lt (Nat.not_lt_zero _)
  | m + 1, j, h_j_lt, h_dist, h_lt => by
      simp only [compareUnaryTape_iter_succ]
      have h_lt_prev :
          p_LBM + 1 + j < (compareUnaryTape_iter right p_LBM M m).length := by
        rw [compareUnaryTape_iter_length]
        rw [compareUnaryTape_iter_length] at h_lt
        exact h_lt
      have h_q_ne : M + 1 + m ≠ p_LBM + 1 + j := by omega
      show (((compareUnaryTape_iter right p_LBM M m).set (p_LBM + 1 + m) 0).set
              (M + 1 + m) 0)[p_LBM + 1 + j]'h_lt = 0
      rw [List.getElem_set_ne h_q_ne]
      by_cases h_j_eq_m : j = m
      · subst h_j_eq_m
        rw [List.getElem_set_self]
      · have h_j_lt_m : j < m := by
          rcases Nat.lt_or_ge j m with h | h
          · exact h
          · exact absurd (Nat.le_antisymm (Nat.lt_succ_iff.mp h_j_lt) h) h_j_eq_m
        have h_p_ne : p_LBM + 1 + m ≠ p_LBM + 1 + j := by omega
        rw [List.getElem_set_ne h_p_ne]
        have h_dist' : p_LBM + m ≤ M := Nat.le_trans (Nat.le_succ _) h_dist
        exact compareUnaryTape_iter_get_slot_zero right p_LBM M m j h_j_lt_m
          h_dist' h_lt_prev

/-- After `n` iterations, varbuf position `M + 1 + j` for `j < n` is `0`.
Requires the slot region disjoint from the varbuf region. -/
theorem compareUnaryTape_iter_get_varbuf_zero
    (right : List Nat) (p_LBM M : Nat) :
    ∀ (n j : Nat) (h_j_lt : j < n) (h_dist : p_LBM + n ≤ M)
      (h_lt : M + 1 + j < (compareUnaryTape_iter right p_LBM M n).length),
      (compareUnaryTape_iter right p_LBM M n).get ⟨M + 1 + j, h_lt⟩ = 0
  | 0, _, h_j_lt, _, _ => absurd h_j_lt (Nat.not_lt_zero _)
  | m + 1, j, h_j_lt, h_dist, h_lt => by
      simp only [compareUnaryTape_iter_succ]
      have h_lt_prev :
          M + 1 + j < (compareUnaryTape_iter right p_LBM M m).length := by
        rw [compareUnaryTape_iter_length]
        rw [compareUnaryTape_iter_length] at h_lt
        exact h_lt
      show (((compareUnaryTape_iter right p_LBM M m).set (p_LBM + 1 + m) 0).set
              (M + 1 + m) 0)[M + 1 + j]'h_lt = 0
      by_cases h_j_eq_m : j = m
      · subst h_j_eq_m
        rw [List.getElem_set_self]
      · have h_j_lt_m : j < m := by
          rcases Nat.lt_or_ge j m with h | h
          · exact h
          · exact absurd (Nat.le_antisymm (Nat.lt_succ_iff.mp h_j_lt) h) h_j_eq_m
        have h_q_ne : M + 1 + m ≠ M + 1 + j := by omega
        rw [List.getElem_set_ne h_q_ne]
        have h_p_ne : p_LBM + 1 + m ≠ M + 1 + j := by omega
        rw [List.getElem_set_ne h_p_ne]
        have h_dist' : p_LBM + m ≤ M := Nat.le_trans (Nat.le_succ _) h_dist
        exact compareUnaryTape_iter_get_varbuf_zero right p_LBM M m j h_j_lt_m
          h_dist' h_lt_prev

/-- **Single-iteration run lemma** for `compareUnaryAtMarkerTM`.

Caller obligations on the *current* tape `right`:
* `h < M`: slot's current `1` cell is left of marker `7`.
* `M + 1 + i < right.length`: varbuf cell at offset `i` is in range.
* `right[h] = 1`: slot `1` at head.
* `right[M] = 7`: marker present.
* `right[M+1+i] = 1`: varbuf's current `1` to erase.
* `h_buf_zeros`: previously-erased varbuf cells are `0`.
* `h_mid`: cells in `(h, M)` are `< sig ∧ ≠ 7 ∧ ≠ 11` (so right-scan
  and left-scan terminate at the right cells without false matches). -/
theorem compareUnaryAtMarkerTM_iteration_run
    (sig : Nat) (h_sig : 12 ≤ sig)
    (left right : List Nat) (h M i : Nat)
    (h_h_lt_M : h < M)
    (h_M_lt : M < right.length)
    (h_buf_in_range : M + 1 + i < right.length)
    (h_get_h : right.get ⟨h, Nat.lt_trans h_h_lt_M h_M_lt⟩ = 1)
    (h_get_M : right.get ⟨M, h_M_lt⟩ = 7)
    (h_get_buf_one : right.get ⟨M + 1 + i, h_buf_in_range⟩ = 1)
    (h_buf_zeros : ∀ j, j < i →
        ∃ (h_lt : M + 1 + j < right.length),
          right.get ⟨M + 1 + j, h_lt⟩ = 0)
    (h_mid : ∀ k, 1 ≤ k → k < M - h →
        ∃ (h_lt : h + k < right.length),
          right.get ⟨h + k, h_lt⟩ < sig ∧
            right.get ⟨h + k, h_lt⟩ ≠ 7 ∧
            right.get ⟨h + k, h_lt⟩ ≠ 11) :
    runFlatTM (3 + 2 * (M - h) + 2 * i) (compareUnaryAtMarkerTM sig)
        { state_idx := 0, tapes := [(left, h, right)] } =
      some { state_idx := 0
             tapes := [(left, h + 1,
               (right.set h 0).set (M + 1 + i) 0)] } := by
  -- ============================================================
  -- Reusable arithmetic / position facts.
  -- ============================================================
  have h_h_lt : h < right.length := Nat.lt_trans h_h_lt_M h_M_lt
  have h_h_le_M : h ≤ M := Nat.le_of_lt h_h_lt_M
  have h_M_sub_h_pos : 1 ≤ M - h := by omega
  have h_M_sub_h_succ : (M - h - 1) + 1 = M - h := by omega
  have h_h_ne_M : h ≠ M := Nat.ne_of_lt h_h_lt_M
  have h_h_lt_buf : h < M + 1 + i := by omega
  have h_h_ne_buf : h ≠ M + 1 + i := Nat.ne_of_lt h_h_lt_buf
  have h_M_lt_buf : M < M + 1 + i := by omega
  have h_M_ne_buf : M ≠ M + 1 + i := Nat.ne_of_lt h_M_lt_buf
  have h_11_lt_sig : (11 : Nat) < sig :=
    Nat.lt_of_lt_of_le (by decide : (11 : Nat) < 12) h_sig
  have h_h_succ_le_M : h + 1 ≤ M := h_h_lt_M
  -- ============================================================
  -- Tape lengths preserved under `set`.
  -- ============================================================
  have h_setlen_rC : (right.set h 11).length = right.length := List.length_set
  have h_setlen_rD :
      ((right.set h 11).set (M + 1 + i) 0).length = right.length := by
    rw [List.length_set, h_setlen_rC]
  have h_h_lt_rC : h < (right.set h 11).length := by
    rw [h_setlen_rC]; exact h_h_lt
  have h_M_lt_rC : M < (right.set h 11).length := by
    rw [h_setlen_rC]; exact h_M_lt
  have h_buf_lt_rC : M + 1 + i < (right.set h 11).length := by
    rw [h_setlen_rC]; exact h_buf_in_range
  have h_h_lt_rD : h < ((right.set h 11).set (M + 1 + i) 0).length := by
    rw [h_setlen_rD]; exact h_h_lt
  have h_M_lt_rD : M < ((right.set h 11).set (M + 1 + i) 0).length := by
    rw [h_setlen_rD]; exact h_M_lt
  -- ============================================================
  -- Step 0 (1 step): state 0 → state 1.
  -- tape becomes rC = right.set h 11, head moves to h+1.
  -- ============================================================
  have h_step0' :
      stepFlatTM (compareUnaryAtMarkerTM sig)
          { state_idx := 0, tapes := [(left, h, right)] } =
        some { state_idx := 1, tapes := [(left, h + 1, right.set h 11)] } := by
    rw [compareUnaryAtMarkerTM_state0_step_one sig left right h h_h_lt h_get_h,
        writeCur_eleven_eq' left h right h_h_lt]
    rfl
  have h_run0 :
      runFlatTM 1 (compareUnaryAtMarkerTM sig)
          { state_idx := 0, tapes := [(left, h, right)] } =
        some { state_idx := 1, tapes := [(left, h + 1, right.set h 11)] } := by
    rw [runFlatTM_compareUnary_state0_unfold sig 0 _ _ h_step0']; rfl
  -- ============================================================
  -- Phase 1 (M - h steps): state 1 → state 2.
  -- Scan right from h+1 to 7 at M. gap = M - h - 1.
  -- ============================================================
  have h_in_range1 : (h + 1) + (M - h - 1) < (right.set h 11).length := by
    rw [h_setlen_rC]; omega
  have h_marker1 :
      (right.set h 11).get ⟨(h + 1) + (M - h - 1), h_in_range1⟩ = 7 := by
    have h_eq : (h + 1) + (M - h - 1) = M := by omega
    have heq : (⟨(h + 1) + (M - h - 1), h_in_range1⟩
            : Fin (right.set h 11).length) = ⟨M, h_M_lt_rC⟩ :=
      Fin.eq_of_val_eq h_eq
    rw [heq]
    show (right.set h 11)[M]'h_M_lt_rC = 7
    rw [List.getElem_set_ne h_h_ne_M]
    exact h_get_M
  have h_mid1 :
      ∀ k, k < M - h - 1 → ∃ (h_lt : (h + 1) + k < (right.set h 11).length),
        (right.set h 11).get ⟨(h + 1) + k, h_lt⟩ < sig ∧
          (right.set h 11).get ⟨(h + 1) + k, h_lt⟩ ≠ 7 := by
    intro k hk
    -- Position p = (h+1) + k. In `right`, p ≠ h since p ≥ h+1.
    have h_k'_pos : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have h_k'_lt : k + 1 < M - h := by omega
    rcases h_mid (k + 1) h_k'_pos h_k'_lt with ⟨h_kk_orig, h_lt_sig, h_ne7, _⟩
    have h_pos_eq : h + (k + 1) = (h + 1) + k := by omega
    have h_kk_orig' : (h + 1) + k < right.length := h_pos_eq ▸ h_kk_orig
    have h_kk_rC : (h + 1) + k < (right.set h 11).length := by
      rw [h_setlen_rC]; exact h_kk_orig'
    have h_pos_ne_h : h ≠ (h + 1) + k := by omega
    refine ⟨h_kk_rC, ?_, ?_⟩
    · show (right.set h 11)[(h + 1) + k]'h_kk_rC < sig
      rw [List.getElem_set_ne h_pos_ne_h]
      show right[(h + 1) + k]'h_kk_orig' < sig
      have heq : (⟨(h + 1) + k, h_kk_orig'⟩ : Fin right.length) =
          ⟨h + (k + 1), h_kk_orig⟩ := Fin.eq_of_val_eq h_pos_eq.symm
      show right.get ⟨(h + 1) + k, h_kk_orig'⟩ < sig
      rw [heq]; exact h_lt_sig
    · show (right.set h 11)[(h + 1) + k]'h_kk_rC ≠ 7
      rw [List.getElem_set_ne h_pos_ne_h]
      show right[(h + 1) + k]'h_kk_orig' ≠ 7
      have heq : (⟨(h + 1) + k, h_kk_orig'⟩ : Fin right.length) =
          ⟨h + (k + 1), h_kk_orig⟩ := Fin.eq_of_val_eq h_pos_eq.symm
      show right.get ⟨(h + 1) + k, h_kk_orig'⟩ ≠ 7
      rw [heq]; exact h_ne7
  have h_run1_raw :
      runFlatTM ((M - h - 1) + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 1, tapes := [(left, h + 1, right.set h 11)] } =
        some { state_idx := 2,
               tapes := [(left, (h + 1) + (M - h - 1) + 1, right.set h 11)] } :=
    compareUnaryAtMarkerTM_state1_phase_run sig left (right.set h 11)
      (M - h - 1) (h + 1) h_in_range1 h_marker1 h_mid1
  have h_head_phase1 : (h + 1) + (M - h - 1) + 1 = M + 1 := by omega
  have h_run1 :
      runFlatTM (M - h) (compareUnaryAtMarkerTM sig)
          { state_idx := 1, tapes := [(left, h + 1, right.set h 11)] } =
        some { state_idx := 2, tapes := [(left, M + 1, right.set h 11)] } := by
    rw [← h_M_sub_h_succ, h_run1_raw, h_head_phase1]
  -- ============================================================
  -- Phase 2-one (i + 1 steps): state 2 → state 3.
  -- Scan right from M+1, skip `i` zeros, write 0 at M+1+i, Lmove.
  -- ============================================================
  have h_in_range2 : (M + 1) + i < (right.set h 11).length := by
    rw [h_setlen_rC]; exact h_buf_in_range
  have h_one2 : (right.set h 11).get ⟨(M + 1) + i, h_in_range2⟩ = 1 := by
    show (right.set h 11)[(M + 1) + i]'h_in_range2 = 1
    rw [List.getElem_set_ne h_h_ne_buf]
    show right.get ⟨(M + 1) + i, h_buf_in_range⟩ = 1
    exact h_get_buf_one
  have h_mid2 :
      ∀ k, k < i → ∃ (h_lt : (M + 1) + k < (right.set h 11).length),
        (right.set h 11).get ⟨(M + 1) + k, h_lt⟩ = 0 := by
    intro k hk
    rcases h_buf_zeros k hk with ⟨h_kk_orig, h_eq_zero⟩
    have h_kk_rC : (M + 1) + k < (right.set h 11).length := by
      rw [h_setlen_rC]; exact h_kk_orig
    have h_pos_ne_h : h ≠ (M + 1) + k := by omega
    refine ⟨h_kk_rC, ?_⟩
    show (right.set h 11)[(M + 1) + k]'h_kk_rC = 0
    rw [List.getElem_set_ne h_pos_ne_h]
    exact h_eq_zero
  have h_run2_raw :
      runFlatTM (i + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 2, tapes := [(left, M + 1, right.set h 11)] } =
        some { state_idx := 3,
               tapes := [(left, ((M + 1) + i) - 1,
                 (right.set h 11).set ((M + 1) + i) 0)] } :=
    compareUnaryAtMarkerTM_state2_phase_run_one sig left (right.set h 11) i
      (M + 1) h_in_range2 h_one2 h_mid2
  have h_head_phase2 : ((M + 1) + i) - 1 = M + i := by omega
  have h_run2 :
      runFlatTM (i + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 2, tapes := [(left, M + 1, right.set h 11)] } =
        some { state_idx := 3,
               tapes := [(left, M + i,
                 (right.set h 11).set ((M + 1) + i) 0)] } := by
    rw [h_run2_raw, h_head_phase2]
  -- ============================================================
  -- Phase 3 ((M + i - h) + 1 steps): state 3 → state 0.
  -- Scan left from M+i to cursor 11 at h, write 0, Rmove.
  -- ============================================================
  -- rD := (right.set h 11).set ((M + 1) + i) 0
  have h_setlen_rD' :
      ((right.set h 11).set ((M + 1) + i) 0).length = right.length := h_setlen_rD
  have h_gap_le3 : (M + i) - h ≤ M + i := Nat.sub_le _ _
  have h_head3_lt : M + i < ((right.set h 11).set ((M + 1) + i) 0).length := by
    rw [h_setlen_rD']; omega
  have h_sub_phase3 : (M + i) - ((M + i) - h) = h := by omega
  have h_in_range3 :
      (M + i) - ((M + i) - h) < ((right.set h 11).set ((M + 1) + i) 0).length := by
    rw [h_sub_phase3, h_setlen_rD']; exact h_h_lt
  have h_get_target3 :
      ((right.set h 11).set ((M + 1) + i) 0).get
          ⟨(M + i) - ((M + i) - h), h_in_range3⟩ = 11 := by
    have heq : (⟨(M + i) - ((M + i) - h), h_in_range3⟩
            : Fin ((right.set h 11).set ((M + 1) + i) 0).length) =
        ⟨h, h_h_lt_rD⟩ := Fin.eq_of_val_eq h_sub_phase3
    rw [heq]
    show ((right.set h 11).set ((M + 1) + i) 0)[h]'h_h_lt_rD = 11
    rw [List.getElem_set_ne h_h_ne_buf.symm]
    show (right.set h 11)[h]'h_h_lt_rC = 11
    rw [List.getElem_set_self]
  have h_before3 :
      ∀ k, k < (M + i) - h → ∃ (hp : (M + i) - k <
        ((right.set h 11).set ((M + 1) + i) 0).length),
        ((right.set h 11).set ((M + 1) + i) 0).get
            ⟨(M + i) - k, hp⟩ < sig ∧
          ((right.set h 11).set ((M + 1) + i) 0).get
            ⟨(M + i) - k, hp⟩ ≠ 11 := by
    intro k hk
    -- pos = (M+i) - k ∈ [h+1, M+i].
    -- Case split: pos ∈ [M+1, M+i] (varbuf zone) or pos = M (marker) or
    -- pos ∈ [h+1, M-1] (intermediate zone).
    have h_pos_le : (M + i) - k ≤ M + i := Nat.sub_le _ _
    have h_pos_ge_h1 : h + 1 ≤ (M + i) - k := by omega
    have h_pos_lt_right : (M + i) - k < right.length := by
      have h_pos_le_buf : (M + i) - k < M + 1 + i := by omega
      omega
    have h_pos_lt_rD : (M + i) - k < ((right.set h 11).set ((M + 1) + i) 0).length := by
      rw [h_setlen_rD']; exact h_pos_lt_right
    have h_pos_ne_h : h ≠ (M + i) - k := by omega
    have h_pos_ne_buf : (M + 1 + i) ≠ (M + i) - k := by
      have : (M + i) - k ≤ M + i := Nat.sub_le _ _
      omega
    refine ⟨h_pos_lt_rD, ?_, ?_⟩
    · -- value < sig
      show ((right.set h 11).set ((M + 1) + i) 0)[(M + i) - k]'h_pos_lt_rD < sig
      rw [List.getElem_set_ne h_pos_ne_buf]
      show (right.set h 11)[(M + i) - k]'(h_setlen_rC ▸ h_pos_lt_right) < sig
      rw [List.getElem_set_ne h_pos_ne_h]
      -- Now we're looking at right[(M+i)-k]. Distinguish three regions.
      by_cases h_pos_eq_M : (M + i) - k = M
      · -- Marker position: value = 7 < sig.
        show right[(M + i) - k]'h_pos_lt_right < sig
        have heq : (⟨(M + i) - k, h_pos_lt_right⟩ : Fin right.length) =
            ⟨M, h_M_lt⟩ := Fin.eq_of_val_eq h_pos_eq_M
        show right.get ⟨(M + i) - k, h_pos_lt_right⟩ < sig
        rw [heq, h_get_M]
        exact Nat.lt_of_lt_of_le (by decide : (7 : Nat) < 12) h_sig
      · by_cases h_pos_gt_M : (M + i) - k > M
        · -- Varbuf zero zone: pos = M+1+j, j = pos - M - 1 < i.
          have h_j_lt : ((M + i) - k) - M - 1 < i := by omega
          have h_pos_eq : M + 1 + (((M + i) - k) - M - 1) = (M + i) - k := by omega
          rcases h_buf_zeros (((M + i) - k) - M - 1) h_j_lt with ⟨h_kk_orig, h_eq_zero⟩
          show right[(M + i) - k]'h_pos_lt_right < sig
          have heq : (⟨(M + i) - k, h_pos_lt_right⟩ : Fin right.length) =
              ⟨M + 1 + (((M + i) - k) - M - 1), h_kk_orig⟩ :=
            Fin.eq_of_val_eq h_pos_eq.symm
          show right.get ⟨(M + i) - k, h_pos_lt_right⟩ < sig
          rw [heq, h_eq_zero]
          exact Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 12) h_sig
        · -- Intermediate zone: h+1 ≤ pos < M. Use h_mid.
          have h_pos_lt_M : (M + i) - k < M := by omega
          have h_k'_def : (M + i) - k - h = (M + i) - k - h := rfl
          have h_k'_pos : 1 ≤ (M + i) - k - h := by omega
          have h_k'_lt : (M + i) - k - h < M - h := by omega
          have h_h_plus : h + ((M + i) - k - h) = (M + i) - k := by omega
          rcases h_mid ((M + i) - k - h) h_k'_pos h_k'_lt with
            ⟨h_kk_orig, h_lt_sig, _h_ne7, _h_ne11⟩
          show right[(M + i) - k]'h_pos_lt_right < sig
          have heq : (⟨(M + i) - k, h_pos_lt_right⟩ : Fin right.length) =
              ⟨h + ((M + i) - k - h), h_kk_orig⟩ := Fin.eq_of_val_eq h_h_plus.symm
          show right.get ⟨(M + i) - k, h_pos_lt_right⟩ < sig
          rw [heq]; exact h_lt_sig
    · -- value ≠ 11
      show ((right.set h 11).set ((M + 1) + i) 0)[(M + i) - k]'h_pos_lt_rD ≠ 11
      rw [List.getElem_set_ne h_pos_ne_buf]
      show (right.set h 11)[(M + i) - k]'(h_setlen_rC ▸ h_pos_lt_right) ≠ 11
      rw [List.getElem_set_ne h_pos_ne_h]
      by_cases h_pos_eq_M : (M + i) - k = M
      · show right[(M + i) - k]'h_pos_lt_right ≠ 11
        have heq : (⟨(M + i) - k, h_pos_lt_right⟩ : Fin right.length) =
            ⟨M, h_M_lt⟩ := Fin.eq_of_val_eq h_pos_eq_M
        show right.get ⟨(M + i) - k, h_pos_lt_right⟩ ≠ 11
        rw [heq, h_get_M]
        decide
      · by_cases h_pos_gt_M : (M + i) - k > M
        · have h_j_lt : ((M + i) - k) - M - 1 < i := by omega
          have h_pos_eq : M + 1 + (((M + i) - k) - M - 1) = (M + i) - k := by omega
          rcases h_buf_zeros (((M + i) - k) - M - 1) h_j_lt with ⟨h_kk_orig, h_eq_zero⟩
          show right[(M + i) - k]'h_pos_lt_right ≠ 11
          have heq : (⟨(M + i) - k, h_pos_lt_right⟩ : Fin right.length) =
              ⟨M + 1 + (((M + i) - k) - M - 1), h_kk_orig⟩ :=
            Fin.eq_of_val_eq h_pos_eq.symm
          show right.get ⟨(M + i) - k, h_pos_lt_right⟩ ≠ 11
          rw [heq, h_eq_zero]
          decide
        · have h_pos_lt_M : (M + i) - k < M := by omega
          have h_k'_pos : 1 ≤ (M + i) - k - h := by omega
          have h_k'_lt : (M + i) - k - h < M - h := by omega
          have h_h_plus : h + ((M + i) - k - h) = (M + i) - k := by omega
          rcases h_mid ((M + i) - k - h) h_k'_pos h_k'_lt with
            ⟨h_kk_orig, _h_lt_sig, _h_ne7, h_ne11⟩
          show right[(M + i) - k]'h_pos_lt_right ≠ 11
          have heq : (⟨(M + i) - k, h_pos_lt_right⟩ : Fin right.length) =
              ⟨h + ((M + i) - k - h), h_kk_orig⟩ := Fin.eq_of_val_eq h_h_plus.symm
          show right.get ⟨(M + i) - k, h_pos_lt_right⟩ ≠ 11
          rw [heq]; exact h_ne11
  have h_run3_raw :
      runFlatTM (((M + i) - h) + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 3,
            tapes := [(left, M + i, (right.set h 11).set ((M + 1) + i) 0)] } =
        some { state_idx := 0,
               tapes := [(left, (M + i) - ((M + i) - h) + 1,
                 ((right.set h 11).set ((M + 1) + i) 0).set ((M + i) - ((M + i) - h))
                   0)] } :=
    compareUnaryAtMarkerTM_state3_phase_run sig left
      ((right.set h 11).set ((M + 1) + i) 0) ((M + i) - h) (M + i)
      h_gap_le3 h_head3_lt h_in_range3 h_get_target3 h_before3
  -- Normalize: (M+i) - ((M+i) - h) = h.
  have h_run3 :
      runFlatTM (((M + i) - h) + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 3,
            tapes := [(left, M + i, (right.set h 11).set ((M + 1) + i) 0)] } =
        some { state_idx := 0,
               tapes := [(left, h + 1,
                 ((right.set h 11).set ((M + 1) + i) 0).set h 0)] } := by
    rw [h_run3_raw, h_sub_phase3]
  -- Simplify the final tape via cursor_buf_set_simp_zero.
  have h_final_tape :
      ((right.set h 11).set ((M + 1) + i) 0).set h 0 =
        (right.set h 0).set ((M + 1) + i) 0 :=
    cursor_buf_set_simp_zero right h ((M + 1) + i) h_h_ne_buf
  have h_run3' :
      runFlatTM (((M + i) - h) + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 3,
            tapes := [(left, M + i, (right.set h 11).set ((M + 1) + i) 0)] } =
        some { state_idx := 0,
               tapes := [(left, h + 1,
                 (right.set h 0).set ((M + 1) + i) 0)] } := by
    rw [h_run3, h_final_tape]
  -- ============================================================
  -- Chain via runFlatTM_compose.
  -- Total: 3 + 2*(M-h) + 2*i = 1 + ((M-h) + ((i+1) + ((M+i-h)+1))).
  -- ============================================================
  have h_total_eq :
      3 + 2 * (M - h) + 2 * i =
        1 + ((M - h) + ((i + 1) + (((M + i) - h) + 1))) := by
    have h_sub_eq : (M + i) - h = (M - h) + i := by omega
    rw [h_sub_eq]; ring
  rw [h_total_eq]
  rw [runFlatTM_compose (compareUnaryAtMarkerTM sig) 1
      ((M - h) + ((i + 1) + (((M + i) - h) + 1)))
      _ _ h_run0]
  rw [runFlatTM_compose (compareUnaryAtMarkerTM sig) (M - h)
      ((i + 1) + (((M + i) - h) + 1))
      _ _ h_run1]
  rw [runFlatTM_compose (compareUnaryAtMarkerTM sig) (i + 1)
      (((M + i) - h) + 1)
      _ _ h_run2]
  exact h_run3'

/-! ### Post-loop helper

The "post-loop" phase of `compareUnaryAtMarkerTM` — step 0 reading the
slot's right boundary marker `6` and phasing through states 4 and 5
to accept-halt at state 8 — is *abstract in the tape*. Lifting it to
a generic `rIter` (with no reference to `compareUnaryTape_iter`)
lets the main inductive `run_match` lemma below apply it cleanly in
the base case without `set rIter := … with h_rIter_def`, whose
dependent length hypotheses defeat subsequent `rw [h_rIter_def]`
("motive not type correct"). -/

/-- Abstract post-loop run of `compareUnaryAtMarkerTM`: from state 0
at slot RBM, reach accept-halt state 8 in `(M-p_LBM) - s + c + 2`
steps, leaving the tape untouched. -/
private theorem compareUnaryAtMarkerTM_post_loop_run
    (sig : Nat) (h_sig : 12 ≤ sig)
    (left rIter : List Nat) (p_LBM M s c : Nat)
    (h_pos1 : p_LBM + 1 + s < M)
    (h_pos2 : M + 1 + c < rIter.length)
    (h_RBM : ∃ (h : p_LBM + 1 + s < rIter.length),
        rIter.get ⟨p_LBM + 1 + s, h⟩ = 6)
    (h_M : ∃ (h : M < rIter.length), rIter.get ⟨M, h⟩ = 7)
    (h_8 : rIter.get ⟨M + 1 + c, h_pos2⟩ = 8)
    (h_varbuf_zeros : ∀ k, k < c → ∃ (h_lt : M + 1 + k < rIter.length),
        rIter.get ⟨M + 1 + k, h_lt⟩ = 0)
    (h_mid_between : ∀ k, p_LBM + 1 + s < k → k < M →
        ∃ (h_lt : k < rIter.length),
          rIter.get ⟨k, h_lt⟩ < sig ∧
            rIter.get ⟨k, h_lt⟩ ≠ 7) :
    runFlatTM ((M - p_LBM) - s + c + 2) (compareUnaryAtMarkerTM sig)
        { state_idx := 0, tapes := [(left, p_LBM + 1 + s, rIter)] } =
      some { state_idx := 8, tapes := [(left, M + 1 + c, rIter)] } := by
  rcases h_RBM with ⟨h_RBM_lt, h_get_RBM⟩
  rcases h_M with ⟨h_M_lt, h_get_M⟩
  have h_6_lt_sig : (6 : Nat) < sig :=
    Nat.lt_of_lt_of_le (by decide : (6 : Nat) < 12) h_sig
  -- Step 0: read 6 at p_LBM+1+s, transit to state 4 (no write, no move).
  have h_step0 :
      stepFlatTM (compareUnaryAtMarkerTM sig)
          { state_idx := 0, tapes := [(left, p_LBM + 1 + s, rIter)] } =
        some { state_idx := 4, tapes := [(left, p_LBM + 1 + s, rIter)] } :=
    compareUnaryAtMarkerTM_state0_step_six sig left rIter (p_LBM + 1 + s)
      h_RBM_lt h_get_RBM
  have h_run0 :
      runFlatTM 1 (compareUnaryAtMarkerTM sig)
          { state_idx := 0, tapes := [(left, p_LBM + 1 + s, rIter)] } =
        some { state_idx := 4, tapes := [(left, p_LBM + 1 + s, rIter)] } := by
    rw [runFlatTM_compareUnary_state0_unfold sig 0 _ _ h_step0]; rfl
  -- Phase 4: state 4, scan right from p_LBM+1+s to 7 at M.
  -- gap = M - (p_LBM+1+s); steps = gap + 1 = (M-p_LBM) - s.
  have h_in_range4 :
      (p_LBM + 1 + s) + (M - (p_LBM + 1 + s)) < rIter.length := by
    have h_eq : (p_LBM + 1 + s) + (M - (p_LBM + 1 + s)) = M := by omega
    rw [h_eq]; exact h_M_lt
  have h_marker4 :
      rIter.get ⟨(p_LBM + 1 + s) + (M - (p_LBM + 1 + s)), h_in_range4⟩ = 7 := by
    have h_eq : (p_LBM + 1 + s) + (M - (p_LBM + 1 + s)) = M := by omega
    have heq : (⟨(p_LBM + 1 + s) + (M - (p_LBM + 1 + s)), h_in_range4⟩
            : Fin rIter.length) = ⟨M, h_M_lt⟩ :=
      Fin.eq_of_val_eq h_eq
    rw [heq]; exact h_get_M
  have h_mid4 :
      ∀ k, k < M - (p_LBM + 1 + s) →
          ∃ (h_lt : (p_LBM + 1 + s) + k < rIter.length),
            rIter.get ⟨(p_LBM + 1 + s) + k, h_lt⟩ < sig ∧
              rIter.get ⟨(p_LBM + 1 + s) + k, h_lt⟩ ≠ 7 := by
    intro k hk
    by_cases h_k_zero : k = 0
    · subst h_k_zero
      have h_pos_lt_rIter : (p_LBM + 1 + s) + 0 < rIter.length := by
        rw [Nat.add_zero]; exact h_RBM_lt
      have heq : (⟨(p_LBM + 1 + s) + 0, h_pos_lt_rIter⟩ : Fin rIter.length) =
          ⟨p_LBM + 1 + s, h_RBM_lt⟩ := Fin.eq_of_val_eq (Nat.add_zero _)
      refine ⟨h_pos_lt_rIter, ?_, ?_⟩
      · rw [heq, h_get_RBM]; exact h_6_lt_sig
      · rw [heq, h_get_RBM]; decide
    · have h_k_pos : 0 < k := Nat.pos_of_ne_zero h_k_zero
      have h_pos_gt_RBM : p_LBM + 1 + s < (p_LBM + 1 + s) + k := by omega
      have h_pos_lt_M : (p_LBM + 1 + s) + k < M := by omega
      exact h_mid_between ((p_LBM + 1 + s) + k) h_pos_gt_RBM h_pos_lt_M
  have h_run4_raw :
      runFlatTM ((M - (p_LBM + 1 + s)) + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 4, tapes := [(left, p_LBM + 1 + s, rIter)] } =
        some { state_idx := 5,
               tapes := [(left, (p_LBM + 1 + s) + (M - (p_LBM + 1 + s)) + 1,
                 rIter)] } :=
    compareUnaryAtMarkerTM_state4_phase_run sig left rIter
      (M - (p_LBM + 1 + s)) (p_LBM + 1 + s) h_in_range4 h_marker4 h_mid4
  have h_gap4_succ : (M - (p_LBM + 1 + s)) + 1 = (M - p_LBM) - s := by omega
  have h_head4_eq :
      (p_LBM + 1 + s) + (M - (p_LBM + 1 + s)) + 1 = M + 1 := by omega
  have h_run4 :
      runFlatTM ((M - p_LBM) - s) (compareUnaryAtMarkerTM sig)
          { state_idx := 4, tapes := [(left, p_LBM + 1 + s, rIter)] } =
        some { state_idx := 5, tapes := [(left, M + 1, rIter)] } := by
    rw [← h_gap4_succ, h_run4_raw, h_head4_eq]
  -- Phase 5-match: state 5, scan right past zeros to 8 at M+1+c.
  -- p = M+1, c remains the same; (M+1) + c = M+1+c by left-assoc.
  have h_mid5 :
      ∀ k, k < c → ∃ (h_lt : (M + 1) + k < rIter.length),
        rIter.get ⟨(M + 1) + k, h_lt⟩ = 0 := h_varbuf_zeros
  have h_run5 :
      runFlatTM (c + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 5, tapes := [(left, M + 1, rIter)] } =
        some { state_idx := 8, tapes := [(left, M + 1 + c, rIter)] } :=
    compareUnaryAtMarkerTM_state5_phase_run_match sig left rIter c (M + 1)
      h_pos2 h_8 h_mid5
  -- Chain: total = 1 + ((M-p_LBM) - s) + (c + 1) = (M-p_LBM) - s + c + 2.
  have h_total_eq :
      (M - p_LBM) - s + c + 2 = 1 + (((M - p_LBM) - s) + (c + 1)) := by ring
  rw [h_total_eq]
  rw [runFlatTM_compose (compareUnaryAtMarkerTM sig) 1
      (((M - p_LBM) - s) + (c + 1)) _ _ h_run0]
  rw [runFlatTM_compose (compareUnaryAtMarkerTM sig) ((M - p_LBM) - s)
      (c + 1) _ _ h_run4]
  exact h_run5

/-! ### Main run lemma — match case

When `slot_size = varbuf_size = s`, the TM halts in accept state 8
after exactly `D*(2s+1) + c + 2` steps, where `D = M - p_LBM`. -/

/-- **Match run lemma**: `compareUnaryAtMarkerTM` halts accept (state 8)
in `s * (2D + 1) + (D - s + c + 2)` steps when the slot has exactly `s`
ones matching the varbuf's `s` ones. Stated by induction on the number
of remaining iterations `u`. -/
theorem compareUnaryAtMarkerTM_run_match
    (sig : Nat) (h_sig : 12 ≤ sig)
    (left right : List Nat) (p_LBM M s c : Nat)
    (h_pos1 : p_LBM + 1 + s < M)
    (h_s_le_c : s ≤ c)
    (h_pos2 : M + 1 + c < right.length)
    (h_M_marker : ∃ (h : M < right.length), right.get ⟨M, h⟩ = 7)
    (h_8_marker : right.get ⟨M + 1 + c, h_pos2⟩ = 8)
    (h_RBM : ∃ (h : p_LBM + 1 + s < right.length),
        right.get ⟨p_LBM + 1 + s, h⟩ = 6)
    (h_slot_ones : ∀ j, j < s → ∃ (h : p_LBM + 1 + j < right.length),
        right.get ⟨p_LBM + 1 + j, h⟩ = 1)
    (h_varbuf_ones : ∀ j, j < s → ∃ (h : M + 1 + j < right.length),
        right.get ⟨M + 1 + j, h⟩ = 1)
    (h_varbuf_zeros : ∀ j, s ≤ j → j < c → ∃ (h : M + 1 + j < right.length),
        right.get ⟨M + 1 + j, h⟩ = 0)
    (h_mid_between : ∀ k, p_LBM + 1 + s < k → k < M →
        ∃ (h : k < right.length),
          right.get ⟨k, h⟩ < sig ∧
            right.get ⟨k, h⟩ ≠ 7 ∧
            right.get ⟨k, h⟩ ≠ 11) :
    ∀ (u i_start : Nat), i_start + u = s →
      runFlatTM (u * (2 * (M - p_LBM) + 1) + ((M - p_LBM) - s + c + 2))
          (compareUnaryAtMarkerTM sig)
          { state_idx := 0,
            tapes := [(left, p_LBM + 1 + i_start,
              compareUnaryTape_iter right p_LBM M i_start)] } =
        some { state_idx := 8,
               tapes := [(left, M + 1 + c,
                 compareUnaryTape_iter right p_LBM M s)] } := by
  rcases h_M_marker with ⟨h_M_lt, h_get_M⟩
  rcases h_RBM with ⟨h_RBM_lt, h_get_RBM⟩
  have h_p_lt_M : p_LBM < M := by omega
  have h_p_le_M : p_LBM + s ≤ M := by omega
  intro u
  induction u with
  | zero =>
      intro i_start h_sum
      have h_i_eq_s : i_start = s := by omega
      rw [h_i_eq_s]
      -- u = 0, i_start = s. Reduce to compareUnaryAtMarkerTM_post_loop_run on
      -- rIter := compareUnaryTape_iter right p_LBM M s.
      have h_total_eq :
          0 * (2 * (M - p_LBM) + 1) + ((M - p_LBM) - s + c + 2) =
            (M - p_LBM) - s + c + 2 := by ring
      rw [h_total_eq]
      have h_rIter_len :
          (compareUnaryTape_iter right p_LBM M s).length = right.length :=
        compareUnaryTape_iter_length _ _ _ _
      have h_pos2_rIter :
          M + 1 + c < (compareUnaryTape_iter right p_LBM M s).length := by
        rw [h_rIter_len]; exact h_pos2
      have h_RBM_lt_rIter :
          p_LBM + 1 + s < (compareUnaryTape_iter right p_LBM M s).length := by
        rw [h_rIter_len]; exact h_RBM_lt
      have h_M_lt_rIter :
          M < (compareUnaryTape_iter right p_LBM M s).length := by
        rw [h_rIter_len]; exact h_M_lt
      have h_get_RBM_rIter :
          (compareUnaryTape_iter right p_LBM M s).get
              ⟨p_LBM + 1 + s, h_RBM_lt_rIter⟩ = 6 := by
        have hget := compareUnaryTape_iter_get_outside right p_LBM M s
          (p_LBM + 1 + s) h_RBM_lt h_RBM_lt_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_get_RBM
      have h_get_M_rIter :
          (compareUnaryTape_iter right p_LBM M s).get ⟨M, h_M_lt_rIter⟩ = 7 := by
        have hget := compareUnaryTape_iter_get_outside right p_LBM M s
          M h_M_lt h_M_lt_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_get_M
      have h_8_rIter :
          (compareUnaryTape_iter right p_LBM M s).get
              ⟨M + 1 + c, h_pos2_rIter⟩ = 8 := by
        have hget := compareUnaryTape_iter_get_outside right p_LBM M s
          (M + 1 + c) h_pos2 h_pos2_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_8_marker
      have h_varbuf_zeros_rIter :
          ∀ k, k < c →
              ∃ (h_lt : M + 1 + k <
                  (compareUnaryTape_iter right p_LBM M s).length),
                (compareUnaryTape_iter right p_LBM M s).get
                    ⟨M + 1 + k, h_lt⟩ = 0 := by
        intro k hk
        have h_pos_lt_orig : M + 1 + k < right.length := by
          rcases Nat.lt_or_ge (M + 1 + k) (M + 1 + c) with hlt | hge
          · exact Nat.lt_trans hlt h_pos2
          · have h_le : M + 1 + k ≤ M + 1 + c := by omega
            have h_eq : M + 1 + k = M + 1 + c := Nat.le_antisymm h_le hge
            rw [h_eq]; exact h_pos2
        have h_pos_lt_rIter :
            M + 1 + k < (compareUnaryTape_iter right p_LBM M s).length := by
          rw [h_rIter_len]; exact h_pos_lt_orig
        refine ⟨h_pos_lt_rIter, ?_⟩
        by_cases h_k_lt_s : k < s
        · exact compareUnaryTape_iter_get_varbuf_zero right p_LBM M s k h_k_lt_s
            h_p_le_M h_pos_lt_rIter
        · push_neg at h_k_lt_s
          rcases h_varbuf_zeros k h_k_lt_s hk with ⟨h_orig_lt, h_orig_zero⟩
          have hget := compareUnaryTape_iter_get_outside right p_LBM M s
            (M + 1 + k) h_orig_lt h_pos_lt_rIter
            (fun j hj => by omega) (fun j hj => by omega)
          rw [hget]; exact h_orig_zero
      have h_mid_between_rIter :
          ∀ k, p_LBM + 1 + s < k → k < M →
              ∃ (h_lt : k < (compareUnaryTape_iter right p_LBM M s).length),
                (compareUnaryTape_iter right p_LBM M s).get ⟨k, h_lt⟩ < sig ∧
                  (compareUnaryTape_iter right p_LBM M s).get ⟨k, h_lt⟩ ≠ 7 := by
        intro k hk_gt hk_lt
        rcases h_mid_between k hk_gt hk_lt with ⟨h_orig_lt, h_lt_sig, h_ne7, _⟩
        have h_pos_lt_rIter :
            k < (compareUnaryTape_iter right p_LBM M s).length := by
          rw [h_rIter_len]; exact h_orig_lt
        have hget := compareUnaryTape_iter_get_outside right p_LBM M s
          k h_orig_lt h_pos_lt_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        refine ⟨h_pos_lt_rIter, ?_, ?_⟩
        · rw [hget]; exact h_lt_sig
        · rw [hget]; exact h_ne7
      exact compareUnaryAtMarkerTM_post_loop_run sig h_sig left
        (compareUnaryTape_iter right p_LBM M s) p_LBM M s c h_pos1 h_pos2_rIter
        ⟨h_RBM_lt_rIter, h_get_RBM_rIter⟩
        ⟨h_M_lt_rIter, h_get_M_rIter⟩
        h_8_rIter h_varbuf_zeros_rIter h_mid_between_rIter
  | succ u ih =>
      intro i_start h_sum
      have h_i_lt_s : i_start < s := by omega
      have h_sum' : (i_start + 1) + u = s := by omega
      have h_h_lt_M_iter : p_LBM + 1 + i_start < M := by omega
      -- Build hypotheses for compareUnaryAtMarkerTM_iteration_run on
      -- (compareUnaryTape_iter right p_LBM M i_start).
      have h_rIter_len :
          (compareUnaryTape_iter right p_LBM M i_start).length = right.length :=
        compareUnaryTape_iter_length _ _ _ _
      have h_M_lt_iter :
          M < (compareUnaryTape_iter right p_LBM M i_start).length := by
        rw [h_rIter_len]; exact h_M_lt
      have h_buf_in_range_iter :
          M + 1 + i_start <
              (compareUnaryTape_iter right p_LBM M i_start).length := by
        rw [h_rIter_len]
        have h1 : M + 1 + i_start < M + 1 + c := by omega
        exact Nat.lt_trans h1 h_pos2
      have h_get_h_iter :
          (compareUnaryTape_iter right p_LBM M i_start).get
              ⟨p_LBM + 1 + i_start,
                Nat.lt_trans h_h_lt_M_iter h_M_lt_iter⟩ = 1 := by
        rcases h_slot_ones i_start h_i_lt_s with ⟨h_orig_lt, h_orig_one⟩
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          (p_LBM + 1 + i_start) h_orig_lt
          (Nat.lt_trans h_h_lt_M_iter h_M_lt_iter)
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_orig_one
      have h_get_M_iter :
          (compareUnaryTape_iter right p_LBM M i_start).get
              ⟨M, h_M_lt_iter⟩ = 7 := by
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          M h_M_lt h_M_lt_iter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_get_M
      have h_get_buf_one_iter :
          (compareUnaryTape_iter right p_LBM M i_start).get
              ⟨M + 1 + i_start, h_buf_in_range_iter⟩ = 1 := by
        rcases h_varbuf_ones i_start h_i_lt_s with ⟨h_orig_lt, h_orig_one⟩
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          (M + 1 + i_start) h_orig_lt h_buf_in_range_iter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_orig_one
      have h_buf_zeros_iter :
          ∀ j, j < i_start → ∃ (h_lt : M + 1 + j <
              (compareUnaryTape_iter right p_LBM M i_start).length),
            (compareUnaryTape_iter right p_LBM M i_start).get
                ⟨M + 1 + j, h_lt⟩ = 0 := by
        intro j hj
        have h_lt_iter :
            M + 1 + j < (compareUnaryTape_iter right p_LBM M i_start).length := by
          rw [h_rIter_len]
          have h1 : M + 1 + j < M + 1 + c := by omega
          exact Nat.lt_trans h1 h_pos2
        refine ⟨h_lt_iter, ?_⟩
        have h_dist : p_LBM + i_start ≤ M := by omega
        exact compareUnaryTape_iter_get_varbuf_zero right p_LBM M i_start j hj
          h_dist h_lt_iter
      have h_mid_iter :
          ∀ k, 1 ≤ k → k < M - (p_LBM + 1 + i_start) →
              ∃ (h_lt : (p_LBM + 1 + i_start) + k <
                  (compareUnaryTape_iter right p_LBM M i_start).length),
                (compareUnaryTape_iter right p_LBM M i_start).get
                    ⟨(p_LBM + 1 + i_start) + k, h_lt⟩ < sig ∧
                  (compareUnaryTape_iter right p_LBM M i_start).get
                      ⟨(p_LBM + 1 + i_start) + k, h_lt⟩ ≠ 7 ∧
                  (compareUnaryTape_iter right p_LBM M i_start).get
                      ⟨(p_LBM + 1 + i_start) + k, h_lt⟩ ≠ 11 := by
        intro k hk_pos hk_lt
        have h_pos_lt_M : (p_LBM + 1 + i_start) + k < M := by omega
        have h_pos_lt_orig : (p_LBM + 1 + i_start) + k < right.length :=
          Nat.lt_trans h_pos_lt_M h_M_lt
        have h_pos_lt_iter : (p_LBM + 1 + i_start) + k <
            (compareUnaryTape_iter right p_LBM M i_start).length := by
          rw [h_rIter_len]; exact h_pos_lt_orig
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          ((p_LBM + 1 + i_start) + k) h_pos_lt_orig h_pos_lt_iter
          (fun j hj => by omega) (fun j hj => by omega)
        refine ⟨h_pos_lt_iter, ?_, ?_, ?_⟩
        all_goals {
          rw [hget]
          by_cases h_in_slot : i_start + k < s
          · -- Slot 1 cell.
            rcases h_slot_ones (i_start + k) h_in_slot with ⟨h_orig_lt', h_one⟩
            have h_pos_eq : p_LBM + 1 + (i_start + k) =
                (p_LBM + 1 + i_start) + k := by ring
            have heq : (⟨(p_LBM + 1 + i_start) + k, h_pos_lt_orig⟩
                    : Fin right.length) =
                ⟨p_LBM + 1 + (i_start + k), h_orig_lt'⟩ :=
              Fin.eq_of_val_eq h_pos_eq.symm
            rw [heq, h_one]
            first
              | exact Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 12) h_sig
              | decide
          · push_neg at h_in_slot
            by_cases h_at_RBM : i_start + k = s
            · -- RBM (value 6).
              have h_pos_eq : (p_LBM + 1 + i_start) + k = p_LBM + 1 + s := by omega
              have heq : (⟨(p_LBM + 1 + i_start) + k, h_pos_lt_orig⟩
                      : Fin right.length) =
                  ⟨p_LBM + 1 + s, h_RBM_lt⟩ := Fin.eq_of_val_eq h_pos_eq
              rw [heq, h_get_RBM]
              first
                | exact Nat.lt_of_lt_of_le (by decide : (6 : Nat) < 12) h_sig
                | decide
            · -- Between RBM and M.
              have h_pos_gt_RBM :
                  p_LBM + 1 + s < (p_LBM + 1 + i_start) + k := by omega
              rcases h_mid_between ((p_LBM + 1 + i_start) + k) h_pos_gt_RBM
                  h_pos_lt_M
                with ⟨h_orig_lt', h_lt_sig, h_ne7, h_ne11⟩
              have heq : (⟨(p_LBM + 1 + i_start) + k, h_pos_lt_orig⟩
                      : Fin right.length) =
                  ⟨(p_LBM + 1 + i_start) + k, h_orig_lt'⟩ := rfl
              rw [heq]
              first | exact h_lt_sig | exact h_ne7 | exact h_ne11
        }
      -- Apply iteration_run.
      have h_iter_run :=
        compareUnaryAtMarkerTM_iteration_run sig h_sig left
          (compareUnaryTape_iter right p_LBM M i_start)
          (p_LBM + 1 + i_start) M i_start h_h_lt_M_iter h_M_lt_iter
          h_buf_in_range_iter h_get_h_iter h_get_M_iter h_get_buf_one_iter
          h_buf_zeros_iter h_mid_iter
      -- The result tape equals compareUnaryTape_iter right p_LBM M (i_start+1).
      have h_tape_succ :
          ((compareUnaryTape_iter right p_LBM M i_start).set
              (p_LBM + 1 + i_start) 0).set (M + 1 + i_start) 0 =
            compareUnaryTape_iter right p_LBM M (i_start + 1) := by
        rw [compareUnaryTape_iter_succ]
      have h_iter_run' :
          runFlatTM (3 + 2 * (M - (p_LBM + 1 + i_start)) + 2 * i_start)
              (compareUnaryAtMarkerTM sig)
              { state_idx := 0,
                tapes := [(left, p_LBM + 1 + i_start,
                  compareUnaryTape_iter right p_LBM M i_start)] } =
            some { state_idx := 0,
                   tapes := [(left, (p_LBM + 1 + i_start) + 1,
                     compareUnaryTape_iter right p_LBM M (i_start + 1))] } := by
        rw [h_iter_run, h_tape_succ]
      -- Step count translation: 3 + 2*(M - (p+1+i)) + 2*i = 2*(M-p) + 1.
      have h_iter_steps :
          3 + 2 * (M - (p_LBM + 1 + i_start)) + 2 * i_start =
            2 * (M - p_LBM) + 1 := by omega
      -- Head translation: (p_LBM + 1 + i_start) + 1 = p_LBM + 1 + (i_start + 1).
      have h_head_eq :
          (p_LBM + 1 + i_start) + 1 = p_LBM + 1 + (i_start + 1) := by ring
      have h_iter_run'' :
          runFlatTM (2 * (M - p_LBM) + 1) (compareUnaryAtMarkerTM sig)
              { state_idx := 0,
                tapes := [(left, p_LBM + 1 + i_start,
                  compareUnaryTape_iter right p_LBM M i_start)] } =
            some { state_idx := 0,
                   tapes := [(left, p_LBM + 1 + (i_start + 1),
                     compareUnaryTape_iter right p_LBM M (i_start + 1))] } := by
        rw [← h_iter_steps, ← h_head_eq]; exact h_iter_run'
      -- Apply IH at (i_start + 1).
      have h_ih := ih (i_start + 1) h_sum'
      -- Chain: (u+1) * (2*(M-p)+1) + ((M-p) - s + c + 2)
      --      = (2*(M-p)+1) + (u * (2*(M-p)+1) + ((M-p) - s + c + 2)).
      have h_total_eq :
          (u + 1) * (2 * (M - p_LBM) + 1) + ((M - p_LBM) - s + c + 2) =
            (2 * (M - p_LBM) + 1) +
              (u * (2 * (M - p_LBM) + 1) + ((M - p_LBM) - s + c + 2)) := by ring
      rw [h_total_eq]
      rw [runFlatTM_compose (compareUnaryAtMarkerTM sig)
          (2 * (M - p_LBM) + 1)
          (u * (2 * (M - p_LBM) + 1) + ((M - p_LBM) - s + c + 2))
          _ _ h_iter_run'']
      exact h_ih

/-! ### Post-loop helper — short case

The "short" case: slot is shorter than varbuf. After `s` iterations
the slot is at `p_LBM+1+s` showing the RBM `6`, but varbuf still has
`c - s` un-erased ones starting at position `M+1+s`. The post-loop:
step 0 transits to state 4 on `6`, phase 4 scans right to `7` at `M`,
phase 5-mismatch scans right past the `s` erased zeros and hits the
first un-erased `1` at `M+1+s`, halt-reject in state 7. -/

/-- Abstract post-loop run for the **short** case: from state 0 at
slot RBM (with un-erased varbuf `1` at `M+1+s`), reach reject-halt
state 7 at `M+1+s` in `(M-p_LBM) + 2` steps, leaving the tape
untouched. -/
private theorem compareUnaryAtMarkerTM_short_post_loop_run
    (sig : Nat) (h_sig : 12 ≤ sig)
    (left rIter : List Nat) (p_LBM M s : Nat)
    (h_pos1 : p_LBM + 1 + s < M)
    (h_buf_one_pos : M + 1 + s < rIter.length)
    (h_RBM : ∃ (h : p_LBM + 1 + s < rIter.length),
        rIter.get ⟨p_LBM + 1 + s, h⟩ = 6)
    (h_M : ∃ (h : M < rIter.length), rIter.get ⟨M, h⟩ = 7)
    (h_buf_one : rIter.get ⟨M + 1 + s, h_buf_one_pos⟩ = 1)
    (h_varbuf_zeros : ∀ k, k < s → ∃ (h_lt : M + 1 + k < rIter.length),
        rIter.get ⟨M + 1 + k, h_lt⟩ = 0)
    (h_mid_between : ∀ k, p_LBM + 1 + s < k → k < M →
        ∃ (h_lt : k < rIter.length),
          rIter.get ⟨k, h_lt⟩ < sig ∧
            rIter.get ⟨k, h_lt⟩ ≠ 7) :
    runFlatTM ((M - p_LBM) + 2) (compareUnaryAtMarkerTM sig)
        { state_idx := 0, tapes := [(left, p_LBM + 1 + s, rIter)] } =
      some { state_idx := 7, tapes := [(left, M + 1 + s, rIter)] } := by
  rcases h_RBM with ⟨h_RBM_lt, h_get_RBM⟩
  rcases h_M with ⟨h_M_lt, h_get_M⟩
  have h_6_lt_sig : (6 : Nat) < sig :=
    Nat.lt_of_lt_of_le (by decide : (6 : Nat) < 12) h_sig
  -- Step 0: read 6 → state 4.
  have h_step0 :
      stepFlatTM (compareUnaryAtMarkerTM sig)
          { state_idx := 0, tapes := [(left, p_LBM + 1 + s, rIter)] } =
        some { state_idx := 4, tapes := [(left, p_LBM + 1 + s, rIter)] } :=
    compareUnaryAtMarkerTM_state0_step_six sig left rIter (p_LBM + 1 + s)
      h_RBM_lt h_get_RBM
  have h_run0 :
      runFlatTM 1 (compareUnaryAtMarkerTM sig)
          { state_idx := 0, tapes := [(left, p_LBM + 1 + s, rIter)] } =
        some { state_idx := 4, tapes := [(left, p_LBM + 1 + s, rIter)] } := by
    rw [runFlatTM_compareUnary_state0_unfold sig 0 _ _ h_step0]; rfl
  -- Phase 4: scan right p_LBM+1+s to 7 at M (steps = (M-p_LBM) - s).
  have h_in_range4 :
      (p_LBM + 1 + s) + (M - (p_LBM + 1 + s)) < rIter.length := by
    have h_eq : (p_LBM + 1 + s) + (M - (p_LBM + 1 + s)) = M := by omega
    rw [h_eq]; exact h_M_lt
  have h_marker4 :
      rIter.get ⟨(p_LBM + 1 + s) + (M - (p_LBM + 1 + s)), h_in_range4⟩ = 7 := by
    have h_eq : (p_LBM + 1 + s) + (M - (p_LBM + 1 + s)) = M := by omega
    have heq : (⟨(p_LBM + 1 + s) + (M - (p_LBM + 1 + s)), h_in_range4⟩
            : Fin rIter.length) = ⟨M, h_M_lt⟩ :=
      Fin.eq_of_val_eq h_eq
    rw [heq]; exact h_get_M
  have h_mid4 :
      ∀ k, k < M - (p_LBM + 1 + s) →
          ∃ (h_lt : (p_LBM + 1 + s) + k < rIter.length),
            rIter.get ⟨(p_LBM + 1 + s) + k, h_lt⟩ < sig ∧
              rIter.get ⟨(p_LBM + 1 + s) + k, h_lt⟩ ≠ 7 := by
    intro k hk
    by_cases h_k_zero : k = 0
    · subst h_k_zero
      have h_pos_lt_rIter : (p_LBM + 1 + s) + 0 < rIter.length := by
        rw [Nat.add_zero]; exact h_RBM_lt
      have heq : (⟨(p_LBM + 1 + s) + 0, h_pos_lt_rIter⟩ : Fin rIter.length) =
          ⟨p_LBM + 1 + s, h_RBM_lt⟩ := Fin.eq_of_val_eq (Nat.add_zero _)
      refine ⟨h_pos_lt_rIter, ?_, ?_⟩
      · rw [heq, h_get_RBM]; exact h_6_lt_sig
      · rw [heq, h_get_RBM]; decide
    · have h_k_pos : 0 < k := Nat.pos_of_ne_zero h_k_zero
      have h_pos_gt_RBM : p_LBM + 1 + s < (p_LBM + 1 + s) + k := by omega
      have h_pos_lt_M : (p_LBM + 1 + s) + k < M := by omega
      exact h_mid_between ((p_LBM + 1 + s) + k) h_pos_gt_RBM h_pos_lt_M
  have h_run4_raw :
      runFlatTM ((M - (p_LBM + 1 + s)) + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 4, tapes := [(left, p_LBM + 1 + s, rIter)] } =
        some { state_idx := 5,
               tapes := [(left, (p_LBM + 1 + s) + (M - (p_LBM + 1 + s)) + 1,
                 rIter)] } :=
    compareUnaryAtMarkerTM_state4_phase_run sig left rIter
      (M - (p_LBM + 1 + s)) (p_LBM + 1 + s) h_in_range4 h_marker4 h_mid4
  have h_gap4_succ : (M - (p_LBM + 1 + s)) + 1 = (M - p_LBM) - s := by omega
  have h_head4_eq :
      (p_LBM + 1 + s) + (M - (p_LBM + 1 + s)) + 1 = M + 1 := by omega
  have h_run4 :
      runFlatTM ((M - p_LBM) - s) (compareUnaryAtMarkerTM sig)
          { state_idx := 4, tapes := [(left, p_LBM + 1 + s, rIter)] } =
        some { state_idx := 5, tapes := [(left, M + 1, rIter)] } := by
    rw [← h_gap4_succ, h_run4_raw, h_head4_eq]
  -- Phase 5-mismatch: gap = s, scan right from M+1 to `1` at M+1+s.
  have h_mid5 :
      ∀ k, k < s → ∃ (h_lt : (M + 1) + k < rIter.length),
        rIter.get ⟨(M + 1) + k, h_lt⟩ = 0 := h_varbuf_zeros
  have h_run5 :
      runFlatTM (s + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 5, tapes := [(left, M + 1, rIter)] } =
        some { state_idx := 7, tapes := [(left, M + 1 + s, rIter)] } :=
    compareUnaryAtMarkerTM_state5_phase_run_mismatch sig left rIter s (M + 1)
      h_buf_one_pos h_buf_one h_mid5
  -- Chain: total = 1 + ((M-p_LBM) - s) + (s + 1) = (M-p_LBM) + 2.
  -- (Holds because s ≤ M - p_LBM, from h_pos1.)
  have h_total_eq :
      (M - p_LBM) + 2 = 1 + (((M - p_LBM) - s) + (s + 1)) := by omega
  rw [h_total_eq]
  rw [runFlatTM_compose (compareUnaryAtMarkerTM sig) 1
      (((M - p_LBM) - s) + (s + 1)) _ _ h_run0]
  rw [runFlatTM_compose (compareUnaryAtMarkerTM sig) ((M - p_LBM) - s)
      (s + 1) _ _ h_run4]
  exact h_run5

/-! ### Main run lemma — short case

When `slot_size = s < varbuf_size = c`, the TM halts in reject state
7 at varbuf head `M+1+s` after exactly `s*(2D+1) + (D + 2)` steps,
where `D = M - p_LBM`. The structure mirrors `_run_match`:
shared iteration loop in the inductive step (each iteration via
`iteration_run`), short post-loop in the base case. -/

/-- **Short run lemma**: `compareUnaryAtMarkerTM` halts reject (state
7) in `s * (2D + 1) + (D + 2)` steps when the slot has `s` ones and
varbuf has `c > s` ones. Stated by induction on the remaining
iterations `u`. -/
theorem compareUnaryAtMarkerTM_run_short
    (sig : Nat) (h_sig : 12 ≤ sig)
    (left right : List Nat) (p_LBM M s c : Nat)
    (h_pos1 : p_LBM + 1 + s < M)
    (h_s_lt_c : s < c)
    (h_pos2 : M + 1 + c < right.length)
    (h_M_marker : ∃ (h : M < right.length), right.get ⟨M, h⟩ = 7)
    (h_RBM : ∃ (h : p_LBM + 1 + s < right.length),
        right.get ⟨p_LBM + 1 + s, h⟩ = 6)
    (h_slot_ones : ∀ j, j < s → ∃ (h : p_LBM + 1 + j < right.length),
        right.get ⟨p_LBM + 1 + j, h⟩ = 1)
    (h_varbuf_ones : ∀ j, j < c → ∃ (h : M + 1 + j < right.length),
        right.get ⟨M + 1 + j, h⟩ = 1)
    (h_mid_between : ∀ k, p_LBM + 1 + s < k → k < M →
        ∃ (h : k < right.length),
          right.get ⟨k, h⟩ < sig ∧
            right.get ⟨k, h⟩ ≠ 7 ∧
            right.get ⟨k, h⟩ ≠ 11) :
    ∀ (u i_start : Nat), i_start + u = s →
      runFlatTM (u * (2 * (M - p_LBM) + 1) + ((M - p_LBM) + 2))
          (compareUnaryAtMarkerTM sig)
          { state_idx := 0,
            tapes := [(left, p_LBM + 1 + i_start,
              compareUnaryTape_iter right p_LBM M i_start)] } =
        some { state_idx := 7,
               tapes := [(left, M + 1 + s,
                 compareUnaryTape_iter right p_LBM M s)] } := by
  rcases h_M_marker with ⟨h_M_lt, h_get_M⟩
  rcases h_RBM with ⟨h_RBM_lt, h_get_RBM⟩
  have h_p_lt_M : p_LBM < M := by omega
  have h_p_le_M : p_LBM + s ≤ M := by omega
  intro u
  induction u with
  | zero =>
      intro i_start h_sum
      have h_i_eq_s : i_start = s := by omega
      rw [h_i_eq_s]
      -- u = 0, i_start = s. Reduce to _short_post_loop_run.
      have h_total_eq :
          0 * (2 * (M - p_LBM) + 1) + ((M - p_LBM) + 2) =
            (M - p_LBM) + 2 := by ring
      rw [h_total_eq]
      have h_rIter_len :
          (compareUnaryTape_iter right p_LBM M s).length = right.length :=
        compareUnaryTape_iter_length _ _ _ _
      -- Position bounds.
      have h_buf_one_pos_orig : M + 1 + s < right.length := by
        have h1 : M + 1 + s < M + 1 + c := by omega
        exact Nat.lt_trans h1 h_pos2
      have h_buf_one_pos_rIter :
          M + 1 + s < (compareUnaryTape_iter right p_LBM M s).length := by
        rw [h_rIter_len]; exact h_buf_one_pos_orig
      have h_RBM_lt_rIter :
          p_LBM + 1 + s < (compareUnaryTape_iter right p_LBM M s).length := by
        rw [h_rIter_len]; exact h_RBM_lt
      have h_M_lt_rIter :
          M < (compareUnaryTape_iter right p_LBM M s).length := by
        rw [h_rIter_len]; exact h_M_lt
      -- rIter values.
      have h_get_RBM_rIter :
          (compareUnaryTape_iter right p_LBM M s).get
              ⟨p_LBM + 1 + s, h_RBM_lt_rIter⟩ = 6 := by
        have hget := compareUnaryTape_iter_get_outside right p_LBM M s
          (p_LBM + 1 + s) h_RBM_lt h_RBM_lt_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_get_RBM
      have h_get_M_rIter :
          (compareUnaryTape_iter right p_LBM M s).get ⟨M, h_M_lt_rIter⟩ = 7 := by
        have hget := compareUnaryTape_iter_get_outside right p_LBM M s
          M h_M_lt h_M_lt_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_get_M
      -- The un-erased varbuf `1` at M+1+s: from h_varbuf_ones s.
      have h_buf_one_rIter :
          (compareUnaryTape_iter right p_LBM M s).get
              ⟨M + 1 + s, h_buf_one_pos_rIter⟩ = 1 := by
        rcases h_varbuf_ones s h_s_lt_c with ⟨h_orig_lt, h_orig_one⟩
        have hget := compareUnaryTape_iter_get_outside right p_LBM M s
          (M + 1 + s) h_orig_lt h_buf_one_pos_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]
        have heq : (⟨M + 1 + s, h_orig_lt⟩ : Fin right.length) =
            ⟨M + 1 + s, h_buf_one_pos_orig⟩ := rfl
        exact h_orig_one
      -- Erased varbuf zeros for k < s.
      have h_varbuf_zeros_rIter :
          ∀ k, k < s →
              ∃ (h_lt : M + 1 + k <
                  (compareUnaryTape_iter right p_LBM M s).length),
                (compareUnaryTape_iter right p_LBM M s).get
                    ⟨M + 1 + k, h_lt⟩ = 0 := by
        intro k hk
        have h_pos_lt_orig : M + 1 + k < right.length := by
          have h1 : M + 1 + k < M + 1 + c := by omega
          exact Nat.lt_trans h1 h_pos2
        have h_pos_lt_rIter :
            M + 1 + k < (compareUnaryTape_iter right p_LBM M s).length := by
          rw [h_rIter_len]; exact h_pos_lt_orig
        refine ⟨h_pos_lt_rIter, ?_⟩
        exact compareUnaryTape_iter_get_varbuf_zero right p_LBM M s k hk
          h_p_le_M h_pos_lt_rIter
      -- Mid-between zone (drop ≠ 11).
      have h_mid_between_rIter :
          ∀ k, p_LBM + 1 + s < k → k < M →
              ∃ (h_lt : k < (compareUnaryTape_iter right p_LBM M s).length),
                (compareUnaryTape_iter right p_LBM M s).get ⟨k, h_lt⟩ < sig ∧
                  (compareUnaryTape_iter right p_LBM M s).get ⟨k, h_lt⟩ ≠ 7 := by
        intro k hk_gt hk_lt
        rcases h_mid_between k hk_gt hk_lt with ⟨h_orig_lt, h_lt_sig, h_ne7, _⟩
        have h_pos_lt_rIter :
            k < (compareUnaryTape_iter right p_LBM M s).length := by
          rw [h_rIter_len]; exact h_orig_lt
        have hget := compareUnaryTape_iter_get_outside right p_LBM M s
          k h_orig_lt h_pos_lt_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        refine ⟨h_pos_lt_rIter, ?_, ?_⟩
        · rw [hget]; exact h_lt_sig
        · rw [hget]; exact h_ne7
      exact compareUnaryAtMarkerTM_short_post_loop_run sig h_sig left
        (compareUnaryTape_iter right p_LBM M s) p_LBM M s h_pos1
        h_buf_one_pos_rIter
        ⟨h_RBM_lt_rIter, h_get_RBM_rIter⟩
        ⟨h_M_lt_rIter, h_get_M_rIter⟩
        h_buf_one_rIter h_varbuf_zeros_rIter h_mid_between_rIter
  | succ u ih =>
      intro i_start h_sum
      have h_i_lt_s : i_start < s := by omega
      have h_sum' : (i_start + 1) + u = s := by omega
      have h_h_lt_M_iter : p_LBM + 1 + i_start < M := by omega
      have h_rIter_len :
          (compareUnaryTape_iter right p_LBM M i_start).length = right.length :=
        compareUnaryTape_iter_length _ _ _ _
      have h_M_lt_iter :
          M < (compareUnaryTape_iter right p_LBM M i_start).length := by
        rw [h_rIter_len]; exact h_M_lt
      have h_buf_in_range_iter :
          M + 1 + i_start <
              (compareUnaryTape_iter right p_LBM M i_start).length := by
        rw [h_rIter_len]
        have h1 : M + 1 + i_start < M + 1 + c := by omega
        exact Nat.lt_trans h1 h_pos2
      have h_get_h_iter :
          (compareUnaryTape_iter right p_LBM M i_start).get
              ⟨p_LBM + 1 + i_start,
                Nat.lt_trans h_h_lt_M_iter h_M_lt_iter⟩ = 1 := by
        rcases h_slot_ones i_start h_i_lt_s with ⟨h_orig_lt, h_orig_one⟩
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          (p_LBM + 1 + i_start) h_orig_lt
          (Nat.lt_trans h_h_lt_M_iter h_M_lt_iter)
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_orig_one
      have h_get_M_iter :
          (compareUnaryTape_iter right p_LBM M i_start).get
              ⟨M, h_M_lt_iter⟩ = 7 := by
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          M h_M_lt h_M_lt_iter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_get_M
      have h_get_buf_one_iter :
          (compareUnaryTape_iter right p_LBM M i_start).get
              ⟨M + 1 + i_start, h_buf_in_range_iter⟩ = 1 := by
        have h_i_lt_c : i_start < c := by omega
        rcases h_varbuf_ones i_start h_i_lt_c with ⟨h_orig_lt, h_orig_one⟩
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          (M + 1 + i_start) h_orig_lt h_buf_in_range_iter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_orig_one
      have h_buf_zeros_iter :
          ∀ j, j < i_start → ∃ (h_lt : M + 1 + j <
              (compareUnaryTape_iter right p_LBM M i_start).length),
            (compareUnaryTape_iter right p_LBM M i_start).get
                ⟨M + 1 + j, h_lt⟩ = 0 := by
        intro j hj
        have h_lt_iter :
            M + 1 + j < (compareUnaryTape_iter right p_LBM M i_start).length := by
          rw [h_rIter_len]
          have h1 : M + 1 + j < M + 1 + c := by omega
          exact Nat.lt_trans h1 h_pos2
        refine ⟨h_lt_iter, ?_⟩
        have h_dist : p_LBM + i_start ≤ M := by omega
        exact compareUnaryTape_iter_get_varbuf_zero right p_LBM M i_start j hj
          h_dist h_lt_iter
      have h_mid_iter :
          ∀ k, 1 ≤ k → k < M - (p_LBM + 1 + i_start) →
              ∃ (h_lt : (p_LBM + 1 + i_start) + k <
                  (compareUnaryTape_iter right p_LBM M i_start).length),
                (compareUnaryTape_iter right p_LBM M i_start).get
                    ⟨(p_LBM + 1 + i_start) + k, h_lt⟩ < sig ∧
                  (compareUnaryTape_iter right p_LBM M i_start).get
                      ⟨(p_LBM + 1 + i_start) + k, h_lt⟩ ≠ 7 ∧
                  (compareUnaryTape_iter right p_LBM M i_start).get
                      ⟨(p_LBM + 1 + i_start) + k, h_lt⟩ ≠ 11 := by
        intro k hk_pos hk_lt
        have h_pos_lt_M : (p_LBM + 1 + i_start) + k < M := by omega
        have h_pos_lt_orig : (p_LBM + 1 + i_start) + k < right.length :=
          Nat.lt_trans h_pos_lt_M h_M_lt
        have h_pos_lt_iter : (p_LBM + 1 + i_start) + k <
            (compareUnaryTape_iter right p_LBM M i_start).length := by
          rw [h_rIter_len]; exact h_pos_lt_orig
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          ((p_LBM + 1 + i_start) + k) h_pos_lt_orig h_pos_lt_iter
          (fun j hj => by omega) (fun j hj => by omega)
        refine ⟨h_pos_lt_iter, ?_, ?_, ?_⟩
        all_goals {
          rw [hget]
          by_cases h_in_slot : i_start + k < s
          · rcases h_slot_ones (i_start + k) h_in_slot with ⟨h_orig_lt', h_one⟩
            have h_pos_eq : p_LBM + 1 + (i_start + k) =
                (p_LBM + 1 + i_start) + k := by ring
            have heq : (⟨(p_LBM + 1 + i_start) + k, h_pos_lt_orig⟩
                    : Fin right.length) =
                ⟨p_LBM + 1 + (i_start + k), h_orig_lt'⟩ :=
              Fin.eq_of_val_eq h_pos_eq.symm
            rw [heq, h_one]
            first
              | exact Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 12) h_sig
              | decide
          · push_neg at h_in_slot
            by_cases h_at_RBM : i_start + k = s
            · have h_pos_eq : (p_LBM + 1 + i_start) + k = p_LBM + 1 + s := by omega
              have heq : (⟨(p_LBM + 1 + i_start) + k, h_pos_lt_orig⟩
                      : Fin right.length) =
                  ⟨p_LBM + 1 + s, h_RBM_lt⟩ := Fin.eq_of_val_eq h_pos_eq
              rw [heq, h_get_RBM]
              first
                | exact Nat.lt_of_lt_of_le (by decide : (6 : Nat) < 12) h_sig
                | decide
            · have h_pos_gt_RBM :
                  p_LBM + 1 + s < (p_LBM + 1 + i_start) + k := by omega
              rcases h_mid_between ((p_LBM + 1 + i_start) + k) h_pos_gt_RBM
                  h_pos_lt_M
                with ⟨h_orig_lt', h_lt_sig, h_ne7, h_ne11⟩
              have heq : (⟨(p_LBM + 1 + i_start) + k, h_pos_lt_orig⟩
                      : Fin right.length) =
                  ⟨(p_LBM + 1 + i_start) + k, h_orig_lt'⟩ := rfl
              rw [heq]
              first | exact h_lt_sig | exact h_ne7 | exact h_ne11
        }
      have h_iter_run :=
        compareUnaryAtMarkerTM_iteration_run sig h_sig left
          (compareUnaryTape_iter right p_LBM M i_start)
          (p_LBM + 1 + i_start) M i_start h_h_lt_M_iter h_M_lt_iter
          h_buf_in_range_iter h_get_h_iter h_get_M_iter h_get_buf_one_iter
          h_buf_zeros_iter h_mid_iter
      have h_tape_succ :
          ((compareUnaryTape_iter right p_LBM M i_start).set
              (p_LBM + 1 + i_start) 0).set (M + 1 + i_start) 0 =
            compareUnaryTape_iter right p_LBM M (i_start + 1) := by
        rw [compareUnaryTape_iter_succ]
      have h_iter_run' :
          runFlatTM (3 + 2 * (M - (p_LBM + 1 + i_start)) + 2 * i_start)
              (compareUnaryAtMarkerTM sig)
              { state_idx := 0,
                tapes := [(left, p_LBM + 1 + i_start,
                  compareUnaryTape_iter right p_LBM M i_start)] } =
            some { state_idx := 0,
                   tapes := [(left, (p_LBM + 1 + i_start) + 1,
                     compareUnaryTape_iter right p_LBM M (i_start + 1))] } := by
        rw [h_iter_run, h_tape_succ]
      have h_iter_steps :
          3 + 2 * (M - (p_LBM + 1 + i_start)) + 2 * i_start =
            2 * (M - p_LBM) + 1 := by omega
      have h_head_eq :
          (p_LBM + 1 + i_start) + 1 = p_LBM + 1 + (i_start + 1) := by ring
      have h_iter_run'' :
          runFlatTM (2 * (M - p_LBM) + 1) (compareUnaryAtMarkerTM sig)
              { state_idx := 0,
                tapes := [(left, p_LBM + 1 + i_start,
                  compareUnaryTape_iter right p_LBM M i_start)] } =
            some { state_idx := 0,
                   tapes := [(left, p_LBM + 1 + (i_start + 1),
                     compareUnaryTape_iter right p_LBM M (i_start + 1))] } := by
        rw [← h_iter_steps, ← h_head_eq]; exact h_iter_run'
      have h_ih := ih (i_start + 1) h_sum'
      have h_total_eq :
          (u + 1) * (2 * (M - p_LBM) + 1) + ((M - p_LBM) + 2) =
            (2 * (M - p_LBM) + 1) +
              (u * (2 * (M - p_LBM) + 1) + ((M - p_LBM) + 2)) := by ring
      rw [h_total_eq]
      rw [runFlatTM_compose (compareUnaryAtMarkerTM sig)
          (2 * (M - p_LBM) + 1)
          (u * (2 * (M - p_LBM) + 1) + ((M - p_LBM) + 2))
          _ _ h_iter_run'']
      exact h_ih

/-! ### Post-loop helper — long case

The "long" case: slot is longer than varbuf. After `c` iterations,
the varbuf is exhausted (all zeros) but the slot still has un-erased
`1`s starting at position `p_LBM+1+c`. The post-loop:
step 0 reads the slot `1`, writes cursor `11`, transits to state 1;
phase 1 scans right to the marker `7` at `M`; phase 2-eight scans
the (now-all-zero) varbuf to the end-marker `8` at `M+1+c`,
transiting to state 6 cleanup; phase 6 scans left back to the
cursor at `p_LBM+1+c`, writes `0` (clearing the cursor), halt-reject
in state 7.

Final tape: `rIter.set (p_LBM+1+c) 0` (cursor written then cleared,
net effect is the slot `1` erased). -/

/-- Abstract post-loop run for the **long** case: from state 0 at
slot's next `1` (varbuf already all zero), reach reject-halt state 7
at `p_LBM+1+c` in `2*(M-p_LBM) + 2` steps, leaving the tape with
the slot `1` at `p_LBM+1+c` erased to `0`. -/
private theorem compareUnaryAtMarkerTM_long_post_loop_run
    (sig : Nat) (h_sig : 12 ≤ sig)
    (left rIter : List Nat) (p_LBM M c : Nat)
    (h_pos1 : p_LBM + 1 + c < M)
    (h_pos2 : M + 1 + c < rIter.length)
    (h_slot_one : ∃ (h : p_LBM + 1 + c < rIter.length),
        rIter.get ⟨p_LBM + 1 + c, h⟩ = 1)
    (h_M : ∃ (h : M < rIter.length), rIter.get ⟨M, h⟩ = 7)
    (h_8 : rIter.get ⟨M + 1 + c, h_pos2⟩ = 8)
    (h_varbuf_zeros : ∀ k, k < c → ∃ (h_lt : M + 1 + k < rIter.length),
        rIter.get ⟨M + 1 + k, h_lt⟩ = 0)
    (h_mid_between : ∀ k, p_LBM + 1 + c < k → k < M →
        ∃ (h_lt : k < rIter.length),
          rIter.get ⟨k, h_lt⟩ < sig ∧
            rIter.get ⟨k, h_lt⟩ ≠ 7 ∧
            rIter.get ⟨k, h_lt⟩ ≠ 11) :
    runFlatTM (2 * (M - p_LBM) + 2) (compareUnaryAtMarkerTM sig)
        { state_idx := 0, tapes := [(left, p_LBM + 1 + c, rIter)] } =
      some { state_idx := 7,
             tapes := [(left, p_LBM + 1 + c,
               rIter.set (p_LBM + 1 + c) 0)] } := by
  rcases h_slot_one with ⟨h_slot_lt, h_get_slot⟩
  rcases h_M with ⟨h_M_lt, h_get_M⟩
  have h_11_lt_sig : (11 : Nat) < sig :=
    Nat.lt_of_lt_of_le (by decide : (11 : Nat) < 12) h_sig
  have h_8_lt_sig : (8 : Nat) < sig :=
    Nat.lt_of_lt_of_le (by decide : (8 : Nat) < 12) h_sig
  have h_7_lt_sig : (7 : Nat) < sig :=
    Nat.lt_of_lt_of_le (by decide : (7 : Nat) < 12) h_sig
  have h_0_lt_sig : (0 : Nat) < sig :=
    Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 12) h_sig
  -- Step 0: read 1 at p_LBM+1+c, write 11, Rmove, → state 1.
  have h_step0_raw :=
    compareUnaryAtMarkerTM_state0_step_one sig left rIter (p_LBM + 1 + c)
      h_slot_lt h_get_slot
  have h_step0 :
      stepFlatTM (compareUnaryAtMarkerTM sig)
          { state_idx := 0, tapes := [(left, p_LBM + 1 + c, rIter)] } =
        some { state_idx := 1
               tapes := [(left, (p_LBM + 1 + c) + 1,
                 rIter.set (p_LBM + 1 + c) 11)] } := by
    rw [h_step0_raw, writeCur_eleven_eq' left (p_LBM + 1 + c) rIter h_slot_lt]
    rfl
  have h_run0 :
      runFlatTM 1 (compareUnaryAtMarkerTM sig)
          { state_idx := 0, tapes := [(left, p_LBM + 1 + c, rIter)] } =
        some { state_idx := 1
               tapes := [(left, (p_LBM + 1 + c) + 1,
                 rIter.set (p_LBM + 1 + c) 11)] } := by
    rw [runFlatTM_compareUnary_state0_unfold sig 0 _ _ h_step0]; rfl
  have hrC_len : (rIter.set (p_LBM + 1 + c) 11).length = rIter.length :=
    List.length_set
  have h_M_lt_rC : M < (rIter.set (p_LBM + 1 + c) 11).length := by
    rw [hrC_len]; exact h_M_lt
  have h_slot_lt_rC :
      p_LBM + 1 + c < (rIter.set (p_LBM + 1 + c) 11).length := by
    rw [hrC_len]; exact h_slot_lt
  -- Phase 1: scan right from (p_LBM+1+c)+1 to 7 at M.
  -- gap = M - ((p_LBM+1+c)+1); steps = gap+1 = M - (p_LBM+1+c).
  have h_in_range1 :
      ((p_LBM + 1 + c) + 1) + (M - ((p_LBM + 1 + c) + 1)) <
        (rIter.set (p_LBM + 1 + c) 11).length := by
    rw [hrC_len]
    have h_eq : ((p_LBM + 1 + c) + 1) + (M - ((p_LBM + 1 + c) + 1)) = M := by omega
    rw [h_eq]; exact h_M_lt
  have h_marker1 :
      (rIter.set (p_LBM + 1 + c) 11).get
          ⟨((p_LBM + 1 + c) + 1) + (M - ((p_LBM + 1 + c) + 1)), h_in_range1⟩ = 7 := by
    have h_eq : ((p_LBM + 1 + c) + 1) + (M - ((p_LBM + 1 + c) + 1)) = M := by omega
    have heq : (⟨((p_LBM + 1 + c) + 1) + (M - ((p_LBM + 1 + c) + 1)), h_in_range1⟩
            : Fin (rIter.set (p_LBM + 1 + c) 11).length) =
        ⟨M, h_M_lt_rC⟩ := Fin.eq_of_val_eq h_eq
    rw [heq]
    show (rIter.set (p_LBM + 1 + c) 11)[M]'h_M_lt_rC = 7
    have h_ne : p_LBM + 1 + c ≠ M := by omega
    rw [List.getElem_set_ne h_ne]
    exact h_get_M
  have h_mid1 :
      ∀ k, k < M - ((p_LBM + 1 + c) + 1) →
          ∃ (h_lt : ((p_LBM + 1 + c) + 1) + k <
              (rIter.set (p_LBM + 1 + c) 11).length),
            (rIter.set (p_LBM + 1 + c) 11).get
                ⟨((p_LBM + 1 + c) + 1) + k, h_lt⟩ < sig ∧
              (rIter.set (p_LBM + 1 + c) 11).get
                  ⟨((p_LBM + 1 + c) + 1) + k, h_lt⟩ ≠ 7 := by
    intro k hk
    have h_pos_lt_M : ((p_LBM + 1 + c) + 1) + k < M := by omega
    have h_pos_gt : p_LBM + 1 + c < ((p_LBM + 1 + c) + 1) + k := by omega
    rcases h_mid_between (((p_LBM + 1 + c) + 1) + k) h_pos_gt h_pos_lt_M with
      ⟨h_orig_lt, h_lt_sig, h_ne7, _⟩
    have h_pos_lt_rC : ((p_LBM + 1 + c) + 1) + k <
        (rIter.set (p_LBM + 1 + c) 11).length := by
      rw [hrC_len]; exact h_orig_lt
    have h_ne : p_LBM + 1 + c ≠ ((p_LBM + 1 + c) + 1) + k := by omega
    refine ⟨h_pos_lt_rC, ?_, ?_⟩
    · show (rIter.set (p_LBM + 1 + c) 11)[((p_LBM + 1 + c) + 1) + k]'h_pos_lt_rC < sig
      rw [List.getElem_set_ne h_ne]
      exact h_lt_sig
    · show (rIter.set (p_LBM + 1 + c) 11)[((p_LBM + 1 + c) + 1) + k]'h_pos_lt_rC ≠ 7
      rw [List.getElem_set_ne h_ne]
      exact h_ne7
  have h_run1_raw :
      runFlatTM ((M - ((p_LBM + 1 + c) + 1)) + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 1,
            tapes := [(left, (p_LBM + 1 + c) + 1,
              rIter.set (p_LBM + 1 + c) 11)] } =
        some { state_idx := 2,
               tapes := [(left,
                 ((p_LBM + 1 + c) + 1) + (M - ((p_LBM + 1 + c) + 1)) + 1,
                 rIter.set (p_LBM + 1 + c) 11)] } :=
    compareUnaryAtMarkerTM_state1_phase_run sig left
      (rIter.set (p_LBM + 1 + c) 11)
      (M - ((p_LBM + 1 + c) + 1)) ((p_LBM + 1 + c) + 1)
      h_in_range1 h_marker1 h_mid1
  have h_gap1_succ :
      (M - ((p_LBM + 1 + c) + 1)) + 1 = M - (p_LBM + 1 + c) := by omega
  have h_head1_eq :
      ((p_LBM + 1 + c) + 1) + (M - ((p_LBM + 1 + c) + 1)) + 1 = M + 1 := by omega
  have h_run1 :
      runFlatTM (M - (p_LBM + 1 + c)) (compareUnaryAtMarkerTM sig)
          { state_idx := 1,
            tapes := [(left, (p_LBM + 1 + c) + 1,
              rIter.set (p_LBM + 1 + c) 11)] } =
        some { state_idx := 2,
               tapes := [(left, M + 1, rIter.set (p_LBM + 1 + c) 11)] } := by
    rw [← h_gap1_succ, h_run1_raw, h_head1_eq]
  -- Phase 2-eight: scan right from M+1 past zeros to 8 at M+1+c.
  -- p = M+1, gap = c, steps = c+1.
  have h_pos2_rC : M + 1 + c < (rIter.set (p_LBM + 1 + c) 11).length := by
    rw [hrC_len]; exact h_pos2
  have h_8_rC :
      (rIter.set (p_LBM + 1 + c) 11).get ⟨M + 1 + c, h_pos2_rC⟩ = 8 := by
    show (rIter.set (p_LBM + 1 + c) 11)[M + 1 + c]'h_pos2_rC = 8
    have h_ne : p_LBM + 1 + c ≠ M + 1 + c := by omega
    rw [List.getElem_set_ne h_ne]
    exact h_8
  have h_mid2 :
      ∀ k, k < c → ∃ (h_lt : (M + 1) + k <
          (rIter.set (p_LBM + 1 + c) 11).length),
        (rIter.set (p_LBM + 1 + c) 11).get ⟨(M + 1) + k, h_lt⟩ = 0 := by
    intro k hk
    rcases h_varbuf_zeros k hk with ⟨h_orig_lt, h_zero⟩
    have h_pos_lt_rC : (M + 1) + k < (rIter.set (p_LBM + 1 + c) 11).length := by
      rw [hrC_len]; exact h_orig_lt
    refine ⟨h_pos_lt_rC, ?_⟩
    show (rIter.set (p_LBM + 1 + c) 11)[(M + 1) + k]'h_pos_lt_rC = 0
    have h_ne : p_LBM + 1 + c ≠ (M + 1) + k := by omega
    rw [List.getElem_set_ne h_ne]
    exact h_zero
  have h_run2 :
      runFlatTM (c + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 2,
            tapes := [(left, M + 1, rIter.set (p_LBM + 1 + c) 11)] } =
        some { state_idx := 6,
               tapes := [(left, M + 1 + c, rIter.set (p_LBM + 1 + c) 11)] } :=
    compareUnaryAtMarkerTM_state2_phase_run_eight sig left
      (rIter.set (p_LBM + 1 + c) 11) c (M + 1) h_pos2_rC h_8_rC h_mid2
  -- Phase 6: scan left from M+1+c to cursor 11 at p_LBM+1+c.
  -- head = M+1+c, gap = M - p_LBM, steps = gap+1 = (M - p_LBM) + 1.
  have h_gap6_le : M - p_LBM ≤ M + 1 + c := by omega
  have h_target_pos_eq : (M + 1 + c) - (M - p_LBM) = p_LBM + 1 + c := by omega
  have h_target_lt :
      (M + 1 + c) - (M - p_LBM) < (rIter.set (p_LBM + 1 + c) 11).length := by
    rw [h_target_pos_eq]; exact h_slot_lt_rC
  have h_get_target :
      (rIter.set (p_LBM + 1 + c) 11).get
          ⟨(M + 1 + c) - (M - p_LBM), h_target_lt⟩ = 11 := by
    have heq : (⟨(M + 1 + c) - (M - p_LBM), h_target_lt⟩
            : Fin (rIter.set (p_LBM + 1 + c) 11).length) =
        ⟨p_LBM + 1 + c, h_slot_lt_rC⟩ := Fin.eq_of_val_eq h_target_pos_eq
    rw [heq]
    show (rIter.set (p_LBM + 1 + c) 11)[p_LBM + 1 + c]'h_slot_lt_rC = 11
    rw [List.getElem_set_self]
  have h_before6 :
      ∀ k, k < M - p_LBM →
          ∃ (h : (M + 1 + c) - k < (rIter.set (p_LBM + 1 + c) 11).length),
            (rIter.set (p_LBM + 1 + c) 11).get ⟨(M + 1 + c) - k, h⟩ < sig ∧
              (rIter.set (p_LBM + 1 + c) 11).get ⟨(M + 1 + c) - k, h⟩ ≠ 11 := by
    intro k hk
    have h_pos_lt_orig : (M + 1 + c) - k < rIter.length :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_pos2
    have h_pos_lt_rC : (M + 1 + c) - k <
        (rIter.set (p_LBM + 1 + c) 11).length := by
      rw [hrC_len]; exact h_pos_lt_orig
    have h_pos_ne_cursor : p_LBM + 1 + c ≠ (M + 1 + c) - k := by omega
    -- Reduce rC[pos] to rIter[pos] via set_ne.
    have h_get_eq :
        (rIter.set (p_LBM + 1 + c) 11)[(M + 1 + c) - k]'h_pos_lt_rC =
          rIter[(M + 1 + c) - k]'h_pos_lt_orig := by
      rw [List.getElem_set_ne h_pos_ne_cursor]
    refine ⟨h_pos_lt_rC, ?_, ?_⟩
    · show (rIter.set (p_LBM + 1 + c) 11)[(M + 1 + c) - k]'h_pos_lt_rC < sig
      rw [h_get_eq]
      -- Now show: rIter[(M+1+c)-k] < sig. Case split on k.
      by_cases h_k0 : k = 0
      · subst h_k0
        have heq : (⟨(M + 1 + c) - 0, h_pos_lt_orig⟩ : Fin rIter.length) =
            ⟨M + 1 + c, h_pos2⟩ := Fin.eq_of_val_eq (Nat.sub_zero _)
        show rIter.get ⟨(M + 1 + c) - 0, h_pos_lt_orig⟩ < sig
        rw [heq, h_8]; exact h_8_lt_sig
      · have h_k_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h_k0
        by_cases h_k_le_c : k ≤ c
        · have h_c_pos : 1 ≤ c := Nat.le_trans h_k_pos h_k_le_c
          have h_ck_lt : c - k < c := by omega
          rcases h_varbuf_zeros (c - k) h_ck_lt with ⟨h_orig_lt, h_zero⟩
          have h_pos_eq : (M + 1 + c) - k = M + 1 + (c - k) := by omega
          have heq : (⟨(M + 1 + c) - k, h_pos_lt_orig⟩ : Fin rIter.length) =
              ⟨M + 1 + (c - k), h_orig_lt⟩ := Fin.eq_of_val_eq h_pos_eq
          show rIter.get ⟨(M + 1 + c) - k, h_pos_lt_orig⟩ < sig
          rw [heq, h_zero]; exact h_0_lt_sig
        · push_neg at h_k_le_c
          by_cases h_k_eq : k = c + 1
          · subst h_k_eq
            have h_pos_eq : (M + 1 + c) - (c + 1) = M := by omega
            have heq : (⟨(M + 1 + c) - (c + 1), h_pos_lt_orig⟩ : Fin rIter.length) =
                ⟨M, h_M_lt⟩ := Fin.eq_of_val_eq h_pos_eq
            show rIter.get ⟨(M + 1 + c) - (c + 1), h_pos_lt_orig⟩ < sig
            rw [heq, h_get_M]; exact h_7_lt_sig
          · have h_k_gt_c1 : k ≥ c + 2 := by omega
            have h_pos_gt : p_LBM + 1 + c < (M + 1 + c) - k := by omega
            have h_pos_lt_M : (M + 1 + c) - k < M := by omega
            rcases h_mid_between ((M + 1 + c) - k) h_pos_gt h_pos_lt_M with
              ⟨h_orig_lt', h_lt_sig, _, _⟩
            have heq : (⟨(M + 1 + c) - k, h_pos_lt_orig⟩ : Fin rIter.length) =
                ⟨(M + 1 + c) - k, h_orig_lt'⟩ := rfl
            show rIter.get ⟨(M + 1 + c) - k, h_pos_lt_orig⟩ < sig
            rw [heq]; exact h_lt_sig
    · show (rIter.set (p_LBM + 1 + c) 11)[(M + 1 + c) - k]'h_pos_lt_rC ≠ 11
      rw [h_get_eq]
      by_cases h_k0 : k = 0
      · subst h_k0
        have heq : (⟨(M + 1 + c) - 0, h_pos_lt_orig⟩ : Fin rIter.length) =
            ⟨M + 1 + c, h_pos2⟩ := Fin.eq_of_val_eq (Nat.sub_zero _)
        show rIter.get ⟨(M + 1 + c) - 0, h_pos_lt_orig⟩ ≠ 11
        rw [heq, h_8]; decide
      · have h_k_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h_k0
        by_cases h_k_le_c : k ≤ c
        · have h_c_pos : 1 ≤ c := Nat.le_trans h_k_pos h_k_le_c
          have h_ck_lt : c - k < c := by omega
          rcases h_varbuf_zeros (c - k) h_ck_lt with ⟨h_orig_lt, h_zero⟩
          have h_pos_eq : (M + 1 + c) - k = M + 1 + (c - k) := by omega
          have heq : (⟨(M + 1 + c) - k, h_pos_lt_orig⟩ : Fin rIter.length) =
              ⟨M + 1 + (c - k), h_orig_lt⟩ := Fin.eq_of_val_eq h_pos_eq
          show rIter.get ⟨(M + 1 + c) - k, h_pos_lt_orig⟩ ≠ 11
          rw [heq, h_zero]; decide
        · push_neg at h_k_le_c
          by_cases h_k_eq : k = c + 1
          · subst h_k_eq
            have h_pos_eq : (M + 1 + c) - (c + 1) = M := by omega
            have heq : (⟨(M + 1 + c) - (c + 1), h_pos_lt_orig⟩ : Fin rIter.length) =
                ⟨M, h_M_lt⟩ := Fin.eq_of_val_eq h_pos_eq
            show rIter.get ⟨(M + 1 + c) - (c + 1), h_pos_lt_orig⟩ ≠ 11
            rw [heq, h_get_M]; decide
          · have h_k_gt_c1 : k ≥ c + 2 := by omega
            have h_pos_gt : p_LBM + 1 + c < (M + 1 + c) - k := by omega
            have h_pos_lt_M : (M + 1 + c) - k < M := by omega
            rcases h_mid_between ((M + 1 + c) - k) h_pos_gt h_pos_lt_M with
              ⟨h_orig_lt', _, _, h_ne11⟩
            have heq : (⟨(M + 1 + c) - k, h_pos_lt_orig⟩ : Fin rIter.length) =
                ⟨(M + 1 + c) - k, h_orig_lt'⟩ := rfl
            show rIter.get ⟨(M + 1 + c) - k, h_pos_lt_orig⟩ ≠ 11
            rw [heq]; exact h_ne11
  have h_run6 :
      runFlatTM ((M - p_LBM) + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 6,
            tapes := [(left, M + 1 + c, rIter.set (p_LBM + 1 + c) 11)] } =
        some { state_idx := 7,
               tapes := [(left, (M + 1 + c) - (M - p_LBM),
                 (rIter.set (p_LBM + 1 + c) 11).set
                   ((M + 1 + c) - (M - p_LBM)) 0)] } :=
    compareUnaryAtMarkerTM_state6_phase_run sig left
      (rIter.set (p_LBM + 1 + c) 11) (M - p_LBM) (M + 1 + c) h_gap6_le
      h_pos2_rC h_target_lt h_get_target h_before6
  -- Simplify final tape: (rIter.set ... 11).set (p_LBM+1+c) 0 = rIter.set (p_LBM+1+c) 0.
  have h_final_tape :
      (rIter.set (p_LBM + 1 + c) 11).set ((M + 1 + c) - (M - p_LBM)) 0 =
        rIter.set (p_LBM + 1 + c) 0 := by
    rw [h_target_pos_eq, List.set_set]
  have h_run6' :
      runFlatTM ((M - p_LBM) + 1) (compareUnaryAtMarkerTM sig)
          { state_idx := 6,
            tapes := [(left, M + 1 + c, rIter.set (p_LBM + 1 + c) 11)] } =
        some { state_idx := 7,
               tapes := [(left, p_LBM + 1 + c,
                 rIter.set (p_LBM + 1 + c) 0)] } := by
    rw [h_run6, h_final_tape, h_target_pos_eq]
  -- Chain: total = 1 + (M - (p_LBM+1+c)) + (c+1) + ((M-p_LBM)+1)
  --             = 2*(M-p_LBM) + 2.
  have h_total_eq :
      2 * (M - p_LBM) + 2 =
        1 + ((M - (p_LBM + 1 + c)) + ((c + 1) + ((M - p_LBM) + 1))) := by omega
  rw [h_total_eq]
  rw [runFlatTM_compose (compareUnaryAtMarkerTM sig) 1
      ((M - (p_LBM + 1 + c)) + ((c + 1) + ((M - p_LBM) + 1))) _ _ h_run0]
  rw [runFlatTM_compose (compareUnaryAtMarkerTM sig) (M - (p_LBM + 1 + c))
      ((c + 1) + ((M - p_LBM) + 1)) _ _ h_run1]
  rw [runFlatTM_compose (compareUnaryAtMarkerTM sig) (c + 1)
      ((M - p_LBM) + 1) _ _ h_run2]
  exact h_run6'

/-! ### Main run lemma — long case

When `slot_size = s > varbuf_size = c`, the TM halts in reject state
7 at `p_LBM+1+c` after exactly `c*(2D+1) + (2D+2)` steps, where
`D = M - p_LBM`. The inductive structure mirrors `_run_match` and
`_run_short`: shared iteration loop in the inductive step, long
post-loop in the base case. The final tape has one additional slot
`1` erased (at `p_LBM+1+c`). -/

/-- **Long run lemma**: `compareUnaryAtMarkerTM` halts reject (state
7) in `c * (2D + 1) + (2D + 2)` steps when the slot has `s > c` ones
and varbuf has `c` ones. Stated by induction on the remaining
iterations `u` (count from `i_start` to `c`). -/
theorem compareUnaryAtMarkerTM_run_long
    (sig : Nat) (h_sig : 12 ≤ sig)
    (left right : List Nat) (p_LBM M s c : Nat)
    (h_pos1 : p_LBM + 1 + c < M)
    (h_c_lt_s : c < s)
    (h_pos2 : M + 1 + c < right.length)
    (h_slot_long : p_LBM + 1 + s ≤ right.length)
    (h_M_marker : ∃ (h : M < right.length), right.get ⟨M, h⟩ = 7)
    (h_8_marker : right.get ⟨M + 1 + c, h_pos2⟩ = 8)
    (h_slot_ones : ∀ j, j < s → ∃ (h : p_LBM + 1 + j < right.length),
        right.get ⟨p_LBM + 1 + j, h⟩ = 1)
    (h_varbuf_ones : ∀ j, j < c → ∃ (h : M + 1 + j < right.length),
        right.get ⟨M + 1 + j, h⟩ = 1)
    (h_mid_between : ∀ k, p_LBM + 1 + c < k → k < M →
        ∃ (h : k < right.length),
          right.get ⟨k, h⟩ < sig ∧
            right.get ⟨k, h⟩ ≠ 7 ∧
            right.get ⟨k, h⟩ ≠ 11) :
    ∀ (u i_start : Nat), i_start + u = c →
      runFlatTM (u * (2 * (M - p_LBM) + 1) + (2 * (M - p_LBM) + 2))
          (compareUnaryAtMarkerTM sig)
          { state_idx := 0,
            tapes := [(left, p_LBM + 1 + i_start,
              compareUnaryTape_iter right p_LBM M i_start)] } =
        some { state_idx := 7,
               tapes := [(left, p_LBM + 1 + c,
                 (compareUnaryTape_iter right p_LBM M c).set
                   (p_LBM + 1 + c) 0)] } := by
  rcases h_M_marker with ⟨h_M_lt, h_get_M⟩
  have h_p_lt_M : p_LBM < M := by omega
  have h_p_le_M : p_LBM + c ≤ M := by omega
  intro u
  induction u with
  | zero =>
      intro i_start h_sum
      have h_i_eq_c : i_start = c := by omega
      rw [h_i_eq_c]
      have h_total_eq :
          0 * (2 * (M - p_LBM) + 1) + (2 * (M - p_LBM) + 2) =
            2 * (M - p_LBM) + 2 := by ring
      rw [h_total_eq]
      have h_rIter_len :
          (compareUnaryTape_iter right p_LBM M c).length = right.length :=
        compareUnaryTape_iter_length _ _ _ _
      have h_pos2_rIter :
          M + 1 + c < (compareUnaryTape_iter right p_LBM M c).length := by
        rw [h_rIter_len]; exact h_pos2
      have h_M_lt_rIter :
          M < (compareUnaryTape_iter right p_LBM M c).length := by
        rw [h_rIter_len]; exact h_M_lt
      have h_slot_lt_rIter :
          p_LBM + 1 + c < (compareUnaryTape_iter right p_LBM M c).length := by
        rw [h_rIter_len]
        rcases h_slot_ones c h_c_lt_s with ⟨h_orig_lt, _⟩
        exact h_orig_lt
      -- The un-erased slot `1` at p_LBM+1+c: from h_slot_ones c.
      have h_get_slot_rIter :
          (compareUnaryTape_iter right p_LBM M c).get
              ⟨p_LBM + 1 + c, h_slot_lt_rIter⟩ = 1 := by
        rcases h_slot_ones c h_c_lt_s with ⟨h_orig_lt, h_orig_one⟩
        have hget := compareUnaryTape_iter_get_outside right p_LBM M c
          (p_LBM + 1 + c) h_orig_lt h_slot_lt_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_orig_one
      have h_get_M_rIter :
          (compareUnaryTape_iter right p_LBM M c).get ⟨M, h_M_lt_rIter⟩ = 7 := by
        have hget := compareUnaryTape_iter_get_outside right p_LBM M c
          M h_M_lt h_M_lt_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_get_M
      have h_8_rIter :
          (compareUnaryTape_iter right p_LBM M c).get
              ⟨M + 1 + c, h_pos2_rIter⟩ = 8 := by
        have hget := compareUnaryTape_iter_get_outside right p_LBM M c
          (M + 1 + c) h_pos2 h_pos2_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_8_marker
      -- All varbuf cells (∀ k < c) are zero in the post-c-iteration tape.
      have h_varbuf_zeros_rIter :
          ∀ k, k < c →
              ∃ (h_lt : M + 1 + k <
                  (compareUnaryTape_iter right p_LBM M c).length),
                (compareUnaryTape_iter right p_LBM M c).get
                    ⟨M + 1 + k, h_lt⟩ = 0 := by
        intro k hk
        have h_pos_lt_orig : M + 1 + k < right.length := by
          have h1 : M + 1 + k < M + 1 + c := by omega
          exact Nat.lt_trans h1 h_pos2
        have h_pos_lt_rIter :
            M + 1 + k < (compareUnaryTape_iter right p_LBM M c).length := by
          rw [h_rIter_len]; exact h_pos_lt_orig
        refine ⟨h_pos_lt_rIter, ?_⟩
        exact compareUnaryTape_iter_get_varbuf_zero right p_LBM M c k hk
          h_p_le_M h_pos_lt_rIter
      have h_mid_between_rIter :
          ∀ k, p_LBM + 1 + c < k → k < M →
              ∃ (h_lt : k < (compareUnaryTape_iter right p_LBM M c).length),
                (compareUnaryTape_iter right p_LBM M c).get ⟨k, h_lt⟩ < sig ∧
                  (compareUnaryTape_iter right p_LBM M c).get ⟨k, h_lt⟩ ≠ 7 ∧
                  (compareUnaryTape_iter right p_LBM M c).get ⟨k, h_lt⟩ ≠ 11 := by
        intro k hk_gt hk_lt
        rcases h_mid_between k hk_gt hk_lt with
          ⟨h_orig_lt, h_lt_sig, h_ne7, h_ne11⟩
        have h_pos_lt_rIter :
            k < (compareUnaryTape_iter right p_LBM M c).length := by
          rw [h_rIter_len]; exact h_orig_lt
        have hget := compareUnaryTape_iter_get_outside right p_LBM M c
          k h_orig_lt h_pos_lt_rIter
          (fun j hj => by omega) (fun j hj => by omega)
        refine ⟨h_pos_lt_rIter, ?_, ?_, ?_⟩
        · rw [hget]; exact h_lt_sig
        · rw [hget]; exact h_ne7
        · rw [hget]; exact h_ne11
      exact compareUnaryAtMarkerTM_long_post_loop_run sig h_sig left
        (compareUnaryTape_iter right p_LBM M c) p_LBM M c h_pos1 h_pos2_rIter
        ⟨h_slot_lt_rIter, h_get_slot_rIter⟩
        ⟨h_M_lt_rIter, h_get_M_rIter⟩
        h_8_rIter h_varbuf_zeros_rIter h_mid_between_rIter
  | succ u ih =>
      intro i_start h_sum
      have h_i_lt_c : i_start < c := by omega
      have h_i_lt_s : i_start < s := Nat.lt_trans h_i_lt_c h_c_lt_s
      have h_sum' : (i_start + 1) + u = c := by omega
      have h_h_lt_M_iter : p_LBM + 1 + i_start < M := by omega
      have h_rIter_len :
          (compareUnaryTape_iter right p_LBM M i_start).length = right.length :=
        compareUnaryTape_iter_length _ _ _ _
      have h_M_lt_iter :
          M < (compareUnaryTape_iter right p_LBM M i_start).length := by
        rw [h_rIter_len]; exact h_M_lt
      have h_buf_in_range_iter :
          M + 1 + i_start <
              (compareUnaryTape_iter right p_LBM M i_start).length := by
        rw [h_rIter_len]
        have h1 : M + 1 + i_start < M + 1 + c := by omega
        exact Nat.lt_trans h1 h_pos2
      have h_get_h_iter :
          (compareUnaryTape_iter right p_LBM M i_start).get
              ⟨p_LBM + 1 + i_start,
                Nat.lt_trans h_h_lt_M_iter h_M_lt_iter⟩ = 1 := by
        rcases h_slot_ones i_start h_i_lt_s with ⟨h_orig_lt, h_orig_one⟩
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          (p_LBM + 1 + i_start) h_orig_lt
          (Nat.lt_trans h_h_lt_M_iter h_M_lt_iter)
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_orig_one
      have h_get_M_iter :
          (compareUnaryTape_iter right p_LBM M i_start).get
              ⟨M, h_M_lt_iter⟩ = 7 := by
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          M h_M_lt h_M_lt_iter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_get_M
      have h_get_buf_one_iter :
          (compareUnaryTape_iter right p_LBM M i_start).get
              ⟨M + 1 + i_start, h_buf_in_range_iter⟩ = 1 := by
        rcases h_varbuf_ones i_start h_i_lt_c with ⟨h_orig_lt, h_orig_one⟩
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          (M + 1 + i_start) h_orig_lt h_buf_in_range_iter
          (fun j hj => by omega) (fun j hj => by omega)
        rw [hget]; exact h_orig_one
      have h_buf_zeros_iter :
          ∀ j, j < i_start → ∃ (h_lt : M + 1 + j <
              (compareUnaryTape_iter right p_LBM M i_start).length),
            (compareUnaryTape_iter right p_LBM M i_start).get
                ⟨M + 1 + j, h_lt⟩ = 0 := by
        intro j hj
        have h_lt_iter :
            M + 1 + j < (compareUnaryTape_iter right p_LBM M i_start).length := by
          rw [h_rIter_len]
          have h1 : M + 1 + j < M + 1 + c := by omega
          exact Nat.lt_trans h1 h_pos2
        refine ⟨h_lt_iter, ?_⟩
        have h_dist : p_LBM + i_start ≤ M := by omega
        exact compareUnaryTape_iter_get_varbuf_zero right p_LBM M i_start j hj
          h_dist h_lt_iter
      have h_mid_iter :
          ∀ k, 1 ≤ k → k < M - (p_LBM + 1 + i_start) →
              ∃ (h_lt : (p_LBM + 1 + i_start) + k <
                  (compareUnaryTape_iter right p_LBM M i_start).length),
                (compareUnaryTape_iter right p_LBM M i_start).get
                    ⟨(p_LBM + 1 + i_start) + k, h_lt⟩ < sig ∧
                  (compareUnaryTape_iter right p_LBM M i_start).get
                      ⟨(p_LBM + 1 + i_start) + k, h_lt⟩ ≠ 7 ∧
                  (compareUnaryTape_iter right p_LBM M i_start).get
                      ⟨(p_LBM + 1 + i_start) + k, h_lt⟩ ≠ 11 := by
        intro k hk_pos hk_lt
        have h_pos_lt_M : (p_LBM + 1 + i_start) + k < M := by omega
        have h_pos_lt_orig : (p_LBM + 1 + i_start) + k < right.length :=
          Nat.lt_trans h_pos_lt_M h_M_lt
        have h_pos_lt_iter : (p_LBM + 1 + i_start) + k <
            (compareUnaryTape_iter right p_LBM M i_start).length := by
          rw [h_rIter_len]; exact h_pos_lt_orig
        have hget := compareUnaryTape_iter_get_outside right p_LBM M i_start
          ((p_LBM + 1 + i_start) + k) h_pos_lt_orig h_pos_lt_iter
          (fun j hj => by omega) (fun j hj => by omega)
        refine ⟨h_pos_lt_iter, ?_, ?_, ?_⟩
        all_goals {
          rw [hget]
          by_cases h_in_slot : i_start + k < s
          · rcases h_slot_ones (i_start + k) h_in_slot with ⟨h_orig_lt', h_one⟩
            have h_pos_eq : p_LBM + 1 + (i_start + k) =
                (p_LBM + 1 + i_start) + k := by ring
            have heq : (⟨(p_LBM + 1 + i_start) + k, h_pos_lt_orig⟩
                    : Fin right.length) =
                ⟨p_LBM + 1 + (i_start + k), h_orig_lt'⟩ :=
              Fin.eq_of_val_eq h_pos_eq.symm
            rw [heq, h_one]
            first
              | exact Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 12) h_sig
              | decide
          · push_neg at h_in_slot
            -- i_start + k ≥ s > c, so i_start + k > c. position (p+1+i) + k > p+1+c.
            -- Use h_mid_between (long-case threshold is c, not s).
            have h_pos_gt_long :
                p_LBM + 1 + c < (p_LBM + 1 + i_start) + k := by omega
            rcases h_mid_between ((p_LBM + 1 + i_start) + k) h_pos_gt_long
                h_pos_lt_M
              with ⟨h_orig_lt', h_lt_sig, h_ne7, h_ne11⟩
            have heq : (⟨(p_LBM + 1 + i_start) + k, h_pos_lt_orig⟩
                    : Fin right.length) =
                ⟨(p_LBM + 1 + i_start) + k, h_orig_lt'⟩ := rfl
            rw [heq]
            first | exact h_lt_sig | exact h_ne7 | exact h_ne11
        }
      have h_iter_run :=
        compareUnaryAtMarkerTM_iteration_run sig h_sig left
          (compareUnaryTape_iter right p_LBM M i_start)
          (p_LBM + 1 + i_start) M i_start h_h_lt_M_iter h_M_lt_iter
          h_buf_in_range_iter h_get_h_iter h_get_M_iter h_get_buf_one_iter
          h_buf_zeros_iter h_mid_iter
      have h_tape_succ :
          ((compareUnaryTape_iter right p_LBM M i_start).set
              (p_LBM + 1 + i_start) 0).set (M + 1 + i_start) 0 =
            compareUnaryTape_iter right p_LBM M (i_start + 1) := by
        rw [compareUnaryTape_iter_succ]
      have h_iter_run' :
          runFlatTM (3 + 2 * (M - (p_LBM + 1 + i_start)) + 2 * i_start)
              (compareUnaryAtMarkerTM sig)
              { state_idx := 0,
                tapes := [(left, p_LBM + 1 + i_start,
                  compareUnaryTape_iter right p_LBM M i_start)] } =
            some { state_idx := 0,
                   tapes := [(left, (p_LBM + 1 + i_start) + 1,
                     compareUnaryTape_iter right p_LBM M (i_start + 1))] } := by
        rw [h_iter_run, h_tape_succ]
      have h_iter_steps :
          3 + 2 * (M - (p_LBM + 1 + i_start)) + 2 * i_start =
            2 * (M - p_LBM) + 1 := by omega
      have h_head_eq :
          (p_LBM + 1 + i_start) + 1 = p_LBM + 1 + (i_start + 1) := by ring
      have h_iter_run'' :
          runFlatTM (2 * (M - p_LBM) + 1) (compareUnaryAtMarkerTM sig)
              { state_idx := 0,
                tapes := [(left, p_LBM + 1 + i_start,
                  compareUnaryTape_iter right p_LBM M i_start)] } =
            some { state_idx := 0,
                   tapes := [(left, p_LBM + 1 + (i_start + 1),
                     compareUnaryTape_iter right p_LBM M (i_start + 1))] } := by
        rw [← h_iter_steps, ← h_head_eq]; exact h_iter_run'
      have h_ih := ih (i_start + 1) h_sum'
      have h_total_eq :
          (u + 1) * (2 * (M - p_LBM) + 1) + (2 * (M - p_LBM) + 2) =
            (2 * (M - p_LBM) + 1) +
              (u * (2 * (M - p_LBM) + 1) + (2 * (M - p_LBM) + 2)) := by ring
      rw [h_total_eq]
      rw [runFlatTM_compose (compareUnaryAtMarkerTM sig)
          (2 * (M - p_LBM) + 1)
          (u * (2 * (M - p_LBM) + 1) + (2 * (M - p_LBM) + 2))
          _ _ h_iter_run'']
      exact h_ih

end Primitives
end EvalCnfTM
