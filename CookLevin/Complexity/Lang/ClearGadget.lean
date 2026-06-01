import Complexity.Lang.ScanLeft
import Complexity.Lang.ScanPast
import Complexity.Lang.ShiftTape
import Complexity.Lang.Navigate

set_option autoImplicit false

/-! # Clear-register gadget (`clearRegionTM`)

`clearRegionTM dst` clears register `dst` by repeatedly deleting its first
content cell (each deletion is a `deleteCarryTM` pass that shifts the suffix
left by one, padding with `0`). The loop runs `|s.get dst|` times, after which
the register is empty (`Op.eval (clear dst) s = s.set dst []`).

## Architecture

The machine is `loopTM clearBodyTM exitDone exitLoop`, where `clearBodyTM` is:
1. **Navigate** from head `0` to register `dst`'s first content cell:
   `stepRightTM ⨾ scanPastDelimTM^dst`.
2. **Branch** on that cell:
   - **delimiter `0`** (register empty) → rewind to `0` → `exitDone`
   - **content ≠ 0`** → step right (so head is at `content_start + 1`),
     delete via `deleteCarryTM`, rewind to `0` → `exitLoop`

Both branches rewind the head to `0` so the loop body's entry condition
(head at the leading sentinel) is invariant across iterations.

### Rewind variants

- **Done branch:** the head is interior (on a delimiter `0`); a plain
  `scanLeftUntilTM 4 3` finds the leading sentinel at position `0`.
- **Delete branch:** after `deleteCarryTM`, the head is in the residue zone
  (past the trailing terminator); `rewindTwoPhaseTM` (scan-left-to-terminator
  ⨾ step-left ⨾ scan-left-to-sentinel) handles this.

### Submachines (building blocks)

- `navigateToRegTM dst` — `stepRightTM ⨾ scanPastDelimTM^dst`
- `delimTestTM` — read one cell and halt at state `1` (content) or `2` (delimiter)
- `deleteAndRewindTM` — `stepRightTM ⨾ deleteCarryTM ⨾ rewindTwoPhaseTM` (demoted boundary)
- `justRewindTM` — `scanLeftUntilTM 4 3`

## References

- Proven math: `Compile.deleteCarry_tail_step`, `set_tail_iterate`,
  `iterate_tail_clear`, `clear_block_decomp`, `encodeTape_reg_decomp`.
- Combinators: `composeFlatTM_run`, `branchComposeFlatTM_run_pos`/`_neg`,
  `loopTM_run`.
- Rewind: `rewindToStart_run`, `rewindTwoPhaseTM`, `rewindFromEndTM`.
-/

namespace Complexity.Lang.ClearGadget

open TMPrimitives
open Complexity.Lang.ScanLeft
open Complexity.Lang.ScanPast
open Complexity.Lang.ShiftTape

/-! ## 1. Navigation: `navigateToRegTM dst`

From head position `0` (the leading sentinel), step right once (past the
sentinel), then scan past `dst` register delimiters. The head lands on
register `dst`'s first content cell (or its delimiter if the register is
empty). Mirrors `AppendGadget.appendAtTM` but stops *at* the register
content-start rather than scanning *through* it. -/

/-- Navigate from head `0` to register `dst`'s first cell.
- `dst = 0`: just `stepRightTM 4` (head 0 → 1).
- `dst = d+1`: `scanPastDelimTM 4 0 ⨾ navigateToRegTM d` (skip one delimiter
  then recurse). -/
def navigateToRegTM : Nat → FlatTM
  | 0     => stepRightTM 4
  | d + 1 => composeFlatTM (scanPastDelimTM 4 0) (navigateToRegTM d) 1

theorem navigateToRegTM_tapes : ∀ dst, (navigateToRegTM dst).tapes = 1
  | 0     => rfl
  | _ + 1 => rfl

theorem navigateToRegTM_start : ∀ dst, (navigateToRegTM dst).start = 0
  | 0     => rfl
  | _ + 1 => rfl

theorem navigateToRegTM_sig : ∀ dst, (navigateToRegTM dst).sig = 4
  | 0     => rfl
  | d + 1 => by
      show (composeFlatTM (scanPastDelimTM 4 0) (navigateToRegTM d) 1).sig = 4
      rw [composeFlatTM_sig, navigateToRegTM_sig d]; rfl

theorem navigateToRegTM_valid : ∀ dst, validFlatTM (navigateToRegTM dst)
  | 0     => stepRightTM_valid 4
  | d + 1 =>
      composeFlatTM_valid (scanPastDelimTM 4 0) (navigateToRegTM d) 1
        (scanPastDelimTM_valid 4 0 (by decide)) (navigateToRegTM_valid d)
        (by decide) rfl (navigateToRegTM_tapes d)

/-- The exit state of `navigateToRegTM dst`. -/
def navigateToRegTM_exit : Nat → Nat
  | 0     => 1
  | d + 1 => 3 + navigateToRegTM_exit d

theorem navigateToRegTM_exit_lt : ∀ dst, navigateToRegTM_exit dst < (navigateToRegTM dst).states
  | 0     => by show 1 < 2; omega
  | d + 1 => by
      show 3 + navigateToRegTM_exit d < 3 + (navigateToRegTM d).states
      exact Nat.add_lt_add_left (navigateToRegTM_exit_lt d) 3

/-! ## 2. Delimiter test: `delimTestTM`

A tiny 3-state machine that reads the current cell:
- If the cell is `0` (delimiter) → halt at state `2` ("done/empty").
- If the cell is in-range and nonzero → halt at state `1` ("content").

State `0` is the start; states `1` and `2` are both halting. This machine
does NOT move the head.

The two exit states are:
- `delimTestTM_exit_content = 1` (cell was content)
- `delimTestTM_exit_delim = 2` (cell was delimiter 0)
-/

/-- Test entry for delimiter (0): stay, halt at state 2. -/
private def delimTestDelimEntry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some 0]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

/-- Test entry for content symbol `v ≠ 0`: stay, halt at state 1. -/
private def delimTestContentEntry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

/-- The delimiter test machine: 3 states, reads one cell, branches on `0`. -/
def delimTestTM (sig : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 3
  trans := delimTestDelimEntry ::
    ((List.range sig).filter (fun v => decide (v ≠ 0))).map delimTestContentEntry
  start := 0
  halt := [false, true, true]

def delimTestTM_exit_content : Nat := 1
def delimTestTM_exit_delim : Nat := 2

theorem delimTestTM_valid (sig : Nat) (h_sig : 0 < sig) : validFlatTM (delimTestTM sig) := by
  refine ⟨show (0 : Nat) < 3 from by decide, rfl, ?_⟩
  intro entry hentry
  rcases List.mem_cons.mp hentry with hDelim | hContent
  · subst hDelim
    refine ⟨show (0 : Nat) < 3 from by decide, show (2 : Nat) < 3 from by decide,
      rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp [delimTestDelimEntry] at hx; subst hx; exact h_sig
    · intro x hx; simp [delimTestDelimEntry] at hx; subst hx; trivial
  · rcases List.mem_map.mp hContent with ⟨v, hv, hmk⟩
    subst hmk
    have hvlt : v < sig := List.mem_range.mp (List.mem_filter.mp hv).1
    refine ⟨show (0 : Nat) < 3 from by decide, show (1 : Nat) < 3 from by decide,
      rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp [delimTestContentEntry] at hx; subst hx; exact hvlt
    · intro x hx; simp [delimTestContentEntry] at hx; subst hx; trivial

theorem delimTestTM_tapes (sig : Nat) : (delimTestTM sig).tapes = 1 := rfl
theorem delimTestTM_start (sig : Nat) : (delimTestTM sig).start = 0 := rfl
theorem delimTestTM_sig (sig : Nat) : (delimTestTM sig).sig = sig := rfl
theorem delimTestTM_states (sig : Nat) : (delimTestTM sig).states = 3 := rfl

/-- On a delimiter cell (value `0`), `delimTestTM` steps to state `2`. -/
theorem delimTestTM_step_delim (sig : Nat) (h_sig : 0 < sig)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length) (h_get : right.get ⟨head, h_head_lt⟩ = 0) :
    stepFlatTM (delimTestTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym : currentTapeSymbol (left, head, right) = some 0 := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSym' : cfg.tapes.map currentTapeSymbol = [some 0] := by
    show [currentTapeSymbol (left, head, right)] = [some 0]; rw [hSym]
  show Option.bind ((delimTestTM sig).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  have hMatch : entryMatchesConfig delimTestDelimEntry cfg = true := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some 0] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = true
    rw [hSym']; rfl
  rw [show (delimTestTM sig).trans =
    delimTestDelimEntry :: ((List.range sig).filter (fun v => decide (v ≠ 0))).map delimTestContentEntry from rfl,
    List.find?_cons, hMatch]
  rfl

/-- Helper: `find?` over the content entries returns the matching entry. -/
private theorem find_delimTestContent_match
    (cfg : FlatTMConfig) (v : Nat) (L : List Nat)
    (h_cfg_state : cfg.state_idx = 0)
    (h_cfg_tape : cfg.tapes.map currentTapeSymbol = [some v])
    (h_ne : v ≠ 0) (h_mem : v ∈ L) :
    (L.map delimTestContentEntry).find?
        (fun entry => entryMatchesConfig entry cfg) =
      some (delimTestContentEntry v) := by
  induction L with
  | nil => cases h_mem
  | cons w ws ih =>
      show List.find? _ (delimTestContentEntry w :: ws.map delimTestContentEntry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (delimTestContentEntry w) cfg = true := by
          show ((0 : Nat) == cfg.state_idx &&
                  decide (([some w] : List (Option Nat)) =
                    cfg.tapes.map currentTapeSymbol)) = true
          rw [h_cfg_state, h_cfg_tape]; simp
        rw [hMatch]
      · have hNot : entryMatchesConfig (delimTestContentEntry w) cfg = false := by
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

/-- On a content cell (value `v ≠ 0`, `v < sig`), `delimTestTM` steps to state `1`. -/
theorem delimTestTM_step_content (sig : Nat) (h_sig : 0 < sig)
    (left right : List Nat) (head v : Nat)
    (h_head_lt : head < right.length) (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 0) (h_lt : v < sig) :
    stepFlatTM (delimTestTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSym' : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]; rw [hSym]
  show Option.bind ((delimTestTM sig).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  have hNotDelim : entryMatchesConfig delimTestDelimEntry cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some 0] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym']
    have h_ne' : ([some 0] : List (Option Nat)) ≠ [some v] := by
      intro h; injection h with h1 _; injection h1 with h2; exact h_ne h2.symm
    simp [h_ne']
  have hv_mem : v ∈ (List.range sig).filter (fun w => decide (w ≠ 0)) := by
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr h_lt, by simp [h_ne]⟩
  have hFind := find_delimTestContent_match cfg v
    ((List.range sig).filter (fun w => decide (w ≠ 0)))
    rfl hSym' h_ne hv_mem
  rw [show (delimTestTM sig).trans =
    delimTestDelimEntry :: ((List.range sig).filter (fun v => decide (v ≠ 0))).map delimTestContentEntry from rfl,
    List.find?_cons, hNotDelim, hFind]
  rfl

/-- `delimTestTM` run: on a delimiter cell → state 2 in 1 step. -/
theorem delimTestTM_run_delim (sig : Nat) (h_sig : 0 < sig)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length) (h_get : right.get ⟨head, h_head_lt⟩ = 0) :
    runFlatTM 1 (delimTestTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head, right)] } := by
  show (if haltingStateReached (delimTestTM sig)
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM (delimTestTM sig)
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _
          | some cfg' => runFlatTM 0 (delimTestTM sig) cfg') = _
  rw [show haltingStateReached (delimTestTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      delimTestTM_step_delim sig h_sig left right head h_head_lt h_get]
  rfl

/-- `delimTestTM` run: on a content cell → state 1 in 1 step. -/
theorem delimTestTM_run_content (sig : Nat) (h_sig : 0 < sig)
    (left right : List Nat) (head v : Nat)
    (h_head_lt : head < right.length) (h_get : right.get ⟨head, h_head_lt⟩ = v)
    (h_ne : v ≠ 0) (h_lt : v < sig) :
    runFlatTM 1 (delimTestTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head, right)] } := by
  show (if haltingStateReached (delimTestTM sig)
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM (delimTestTM sig)
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _
          | some cfg' => runFlatTM 0 (delimTestTM sig) cfg') = _
  rw [show haltingStateReached (delimTestTM sig)
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      delimTestTM_step_content sig h_sig left right head v h_head_lt h_get h_ne h_lt]
  rfl

/-- `delimTestTM` never halts before its single step. -/
theorem delimTestTM_no_early_halt (sig : Nat)
    (left right : List Nat) (head : Nat) :
    ∀ k, k < 1 → ∀ ck,
      runFlatTM k (delimTestTM sig)
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ delimTestTM_exit_content ∧
      ck.state_idx ≠ delimTestTM_exit_delim ∧
      haltingStateReached (delimTestTM sig) ck = false := by
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  simp [runFlatTM] at hck; subst hck
  refine ⟨?_, ?_, rfl⟩
  · show (0 : Nat) ≠ 1; omega
  · show (0 : Nat) ≠ 2; omega

/-- The halt states of `delimTestTM sig` are exactly `1` and `2`. -/
theorem delimTestTM_halt_only (sig : Nat) (i : Nat)
    (hi : (delimTestTM sig).halt[i]? = some true) : i = 1 ∨ i = 2 := by
  change ([false, true, true] : List Bool)[i]? = some true at hi
  rcases i with _ | _ | _ | i <;> simp_all

/-! ## 3. Navigate-and-test composition

`navigateAndTestTM dst = composeFlatTM (navigateToRegTM dst) (delimTestTM 4) nav_exit`

This has two halt states (from `delimTestTM`, shifted by `navigateToRegTM.states`):
- content exit = `navigateToRegTM.states + 1`
- delimiter exit = `navigateToRegTM.states + 2`
-/

def navigateAndTestTM (dst : Nat) : FlatTM :=
  composeFlatTM (navigateToRegTM dst) (delimTestTM 4) (navigateToRegTM_exit dst)

def navigateAndTestTM_exit_content (dst : Nat) : Nat :=
  (navigateToRegTM dst).states + delimTestTM_exit_content

def navigateAndTestTM_exit_delim (dst : Nat) : Nat :=
  (navigateToRegTM dst).states + delimTestTM_exit_delim

theorem navigateAndTestTM_tapes (dst : Nat) : (navigateAndTestTM dst).tapes = 1 := by
  show (navigateToRegTM dst).tapes = 1; exact navigateToRegTM_tapes dst
theorem navigateAndTestTM_start (dst : Nat) : (navigateAndTestTM dst).start = 0 := by
  show (navigateToRegTM dst).start = 0; exact navigateToRegTM_start dst

theorem navigateAndTestTM_sig (dst : Nat) : (navigateAndTestTM dst).sig = 4 := by
  show max (navigateToRegTM dst).sig (delimTestTM 4).sig = 4
  rw [navigateToRegTM_sig]; rfl

theorem navigateAndTestTM_valid (dst : Nat) : validFlatTM (navigateAndTestTM dst) :=
  composeFlatTM_valid (navigateToRegTM dst) (delimTestTM 4) (navigateToRegTM_exit dst)
    (navigateToRegTM_valid dst) (delimTestTM_valid 4 (by decide))
    (navigateToRegTM_exit_lt dst) (navigateToRegTM_tapes dst) (delimTestTM_tapes 4)

theorem navigateAndTestTM_states (dst : Nat) :
    (navigateAndTestTM dst).states = (navigateToRegTM dst).states + 3 := by
  show (navigateToRegTM dst).states + (delimTestTM 4).states = _; rfl

/-! ## 4. Delete-and-rewind machine

For the content branch: step right (so head is at content_start + 1),
then `deleteCarryTM` (deletes the cell before head, shifts suffix left),
then rewind to `0` via the two-phase rewind (`rewindTwoPhaseTM`).

`deleteAndRewindRawTM = composeFlatTM (stepRightTM 4) deleteAndDeleteRewindTM exit`
where `deleteAndDeleteRewindTM = composeFlatTM deleteCarryTM (rewindTwoPhaseTM 4 3) 6`

The two-phase rewind has two halt states (6 = found, 7 = boundary).
We demote the boundary halt using `Compile.joinTwoHalts`, leaving a single
exit at the "found" position. -/

/-- The raw delete-then-rewind (before demoting boundary halt):
`deleteCarryTM ⨾ rewindTwoPhaseTM 4 3`, bridging at `deleteCarryTM`'s exit state `6`. -/
def deleteRewindRawTM : FlatTM :=
  composeFlatTM deleteCarryTM (rewindTwoPhaseTM 4 3) 6

/-- The step-right, then delete-then-rewind (no boundary demotion yet):
`stepRightTM 4 ⨾ deleteRewindRawTM`. -/
def stepDeleteRewindRawTM : FlatTM :=
  composeFlatTM (stepRightTM 4) deleteRewindRawTM 1

-- The boundary halt states need to be identified and demoted.
-- `deleteCarryTM.states = 7`, `rewindTwoPhaseTM.states = 8`.
-- `deleteRewindRawTM.states = 7 + 8 = 15`.
-- The rewind's halt states `6` and `7` become `7 + 6 = 13` and `7 + 7 = 14` in the raw composite.
-- `stepRightTM.states = 2`, so in `stepDeleteRewindRawTM`:
-- states = `2 + 15 = 17`
-- found halt = `2 + 13 = 15`
-- boundary halt = `2 + 14 = 16`

-- We keep halt `15` (found/head-rewound-to-0) and demote `16` (boundary).

def stepDeleteRewindTM_exit : Nat := 15

/-! ## 5. Done-branch rewind

For the delimiter branch (register empty): just rewind from the current
interior position to `0` using `scanLeftUntilTM 4 3` (the leading sentinel
is the only `3` between the current position and the left end). -/

def justRewindTM : FlatTM := scanLeftUntilTM 4 3

-- `justRewindTM.states = 3`.
-- Its halt states are `1` (found) and `2` (boundary).
-- We keep `1` (found) as our exit.
def justRewindTM_exit : Nat := 1

/-! ## 6. Full clear body via `branchComposeFlatTM`

`clearBodyRawTM dst = branchComposeFlatTM (navigateAndTestTM dst)
    stepDeleteRewindRawTM justRewindTM
    (navigateAndTestTM_exit_content dst) (navigateAndTestTM_exit_delim dst)`

The content path (exit_pos → M₂ = stepDeleteRewindRawTM) exits at:
  `(navigateAndTestTM dst).states + stepDeleteRewindTM_exit`
  = `(navigateToRegTM dst).states + 3 + 15`

The delimiter path (exit_neg → M₃ = justRewindTM) exits at:
  `(navigateAndTestTM dst).states + stepDeleteRewindRawTM.states + justRewindTM_exit`
  = `(navigateToRegTM dst).states + 3 + 17 + 1`

For `loopTM`:
- exitLoop = content path exit (delete and continue)
- exitDone = delimiter path exit (register empty, stop)
-/

def clearBodyRawTM (dst : Nat) : FlatTM :=
  branchComposeFlatTM (navigateAndTestTM dst) stepDeleteRewindRawTM justRewindTM
    (navigateAndTestTM_exit_content dst) (navigateAndTestTM_exit_delim dst)

-- exitLoop: the content branch exit (from stepDeleteRewindRawTM in the M₂ slot)
def clearBodyTM_exitLoop (dst : Nat) : Nat :=
  (navigateAndTestTM dst).states + stepDeleteRewindTM_exit

-- exitDone: the delimiter branch exit (from justRewindTM in the M₃ slot)
def clearBodyTM_exitDone (dst : Nat) : Nat :=
  (navigateAndTestTM dst).states + stepDeleteRewindRawTM.states + justRewindTM_exit

/-! ## 7. `clearRegionTM` via `loopTM`

The loop halts at `clearBodyRawTM.states` when the done branch fires.
We wrap it as a `CompiledCmd` (the single halt state is at `B.states`).
-/

def clearRegionTM (dst : Nat) : FlatTM :=
  loopTM (clearBodyRawTM dst) (clearBodyTM_exitDone dst) (clearBodyTM_exitLoop dst)

/-! ## 8. Validity -/

-- TODO: prove validity and halt-state properties once the intermediate
-- lemmas for `branchComposeFlatTM` are threaded through.

theorem clearRegionTM_tapes (dst : Nat) : (clearRegionTM dst).tapes = 1 := by
  show (clearBodyRawTM dst).tapes = 1
  show (branchComposeFlatTM _ _ _ _ _).tapes = 1
  rw [branchComposeFlatTM_tapes]
  exact navigateAndTestTM_tapes dst

theorem clearRegionTM_start (dst : Nat) : (clearRegionTM dst).start = 0 := by
  show (clearBodyRawTM dst).start = 0
  show (branchComposeFlatTM _ _ _ _ _).start = 0
  rw [branchComposeFlatTM_start]
  exact navigateAndTestTM_start dst

theorem clearRegionTM_sig (dst : Nat) : (clearRegionTM dst).sig = 4 := by
  show (clearBodyRawTM dst).sig = 4
  show (branchComposeFlatTM _ _ _ _ _).sig = 4
  rw [branchComposeFlatTM_sig, navigateAndTestTM_sig]
  -- max 4 (max stepDeleteRewindRawTM.sig justRewindTM.sig) = 4
  show max 4 (max stepDeleteRewindRawTM.sig justRewindTM.sig) = 4
  -- stepDeleteRewindRawTM.sig = max (stepRightTM 4).sig deleteRewindRawTM.sig
  -- deleteRewindRawTM.sig = max deleteCarryTM.sig (rewindTwoPhaseTM 4 3).sig
  -- All are = 4.
  rfl

theorem clearRegionTM_states (dst : Nat) :
    (clearRegionTM dst).states = (clearBodyRawTM dst).states + 1 := rfl

/-- The unique halt state of `clearRegionTM dst`. -/
def clearRegionTM_exit (dst : Nat) : Nat := (clearBodyRawTM dst).states

end Complexity.Lang.ClearGadget
