import Complexity.Lang.ScanLeft
import Complexity.Lang.ScanPast
import Complexity.Lang.ShiftTape
import Complexity.Lang.Navigate
import Complexity.Lang.AppendGadget

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
open Complexity.Lang.AppendGadget
open Complexity.Lang.Navigate

/-! ## 1. Navigation: `navigateToRegTM dst`

From head position `0` (the leading sentinel), step right once (past the
sentinel), then scan past `dst` register delimiters. The head lands on
register `dst`'s first content cell (or its delimiter if the register is
empty). Mirrors `AppendGadget.appendAtTM` but stops *at* the register
content-start rather than scanning *through* it. -/

/-- The exit (halt) state of `navigateToRegTM dst`. Closed form so it can be
referenced as the bridge in `navigateToRegTM`'s own recursion.
- `dst = 0`: `stepRightTM`'s halt state `1`.
- `dst = d+1`: `scanPastDelimTM`'s found halt (`1`) shifted by
  `(navigateToRegTM d).states = 2 + 3·d`, i.e. `3·d + 3`. -/
def navigateToRegTM_exit : Nat → Nat
  | 0     => 1
  | d + 1 => 3 * d + 3

/-- Navigate from head `0` to register `dst`'s first content cell
(`stepRight ⨾ scanPastDelim^dst`).
- `dst = 0`: `stepRightTM 4` (head `0 → 1`, past the leading sentinel onto
  register `0`'s content start).
- `dst = d+1`: `navigateToRegTM d ⨾ scanPastDelimTM 4 0` (navigate to register
  `d`'s content start, then scan past register `d`'s content and delimiter,
  landing on register `d+1`'s content start).

**Recursion is in the `M₁` slot** (the growing machine first, then one fixed
`scanPastDelimTM`): a `scanPastDelim` started from a register's content start
advances exactly one register, so `dst` of them after the base `stepRight` land
on register `dst`. (The previous `scanPastDelim ⨾ navigateToRegTM d` shape
overshot by the base `stepRight` — surfaced by `#eval` probing.) -/
def navigateToRegTM : Nat → FlatTM
  | 0     => stepRightTM 4
  | d + 1 => composeFlatTM (navigateToRegTM d) (scanPastDelimTM 4 0) (navigateToRegTM_exit d)

theorem navigateToRegTM_tapes : ∀ dst, (navigateToRegTM dst).tapes = 1
  | 0     => rfl
  | d + 1 => by show (navigateToRegTM d).tapes = 1; exact navigateToRegTM_tapes d

theorem navigateToRegTM_start : ∀ dst, (navigateToRegTM dst).start = 0
  | 0     => rfl
  | d + 1 => by show (navigateToRegTM d).start = 0; exact navigateToRegTM_start d

theorem navigateToRegTM_sig : ∀ dst, (navigateToRegTM dst).sig = 4
  | 0     => rfl
  | d + 1 => by
      show max (navigateToRegTM d).sig (scanPastDelimTM 4 0).sig = 4
      rw [navigateToRegTM_sig d]; rfl

/-- `(navigateToRegTM dst).states = 2 + 3·dst`. -/
theorem navigateToRegTM_states : ∀ dst, (navigateToRegTM dst).states = 2 + 3 * dst
  | 0     => rfl
  | d + 1 => by
      show (navigateToRegTM d).states + (scanPastDelimTM 4 0).states = 2 + 3 * (d + 1)
      rw [navigateToRegTM_states d, show (scanPastDelimTM 4 0).states = 3 from rfl]; omega

theorem navigateToRegTM_exit_lt : ∀ dst, navigateToRegTM_exit dst < (navigateToRegTM dst).states
  | 0     => by show 1 < 2; omega
  | d + 1 => by
      rw [navigateToRegTM_states]
      show 3 * d + 3 < 2 + 3 * (d + 1); omega

theorem navigateToRegTM_valid : ∀ dst, validFlatTM (navigateToRegTM dst)
  | 0     => stepRightTM_valid 4
  | d + 1 =>
      composeFlatTM_valid (navigateToRegTM d) (scanPastDelimTM 4 0) (navigateToRegTM_exit d)
        (navigateToRegTM_valid d) (scanPastDelimTM_valid 4 0 (by decide))
        (navigateToRegTM_exit_lt d) (navigateToRegTM_tapes d) rfl

/-! ### `navigateToRegTM` run + trajectory

`navigateToRegTM skipped.length`, started at head `0` on
`3 :: (regBlocks skipped ++ tail)` (leading sentinel `3 = endMark`, then the
encoded blocks of the `skipped` registers, then `tail` = register `dst`'s content
and the rest), lands at head `1 + |regBlocks skipped|` (register `dst`'s content
start) without changing the tape. Stated over literal `3` (not `Compile.endMark`,
which lives downstream); `Compile.lean`'s `clear` case instantiates it via
`encodeTape_reg_decomp`. -/

/-- Step count of `navigateToRegTM skipped.length`: one `stepRight` plus, per
skipped register `b`, one `scanPast` over its `|b|` content cells (`+1` to land
past the delimiter) and one bridge step (`+1`). -/
def navSteps (skipped : List (List Nat)) : Nat :=
  1 + (skipped.map (fun b => b.length + 2)).sum

theorem navSteps_nil : navSteps [] = 1 := rfl

theorem navSteps_append_singleton (init : List (List Nat)) (b : List Nat) :
    navSteps (init ++ [b]) = navSteps init + (b.length + 2) := by
  simp only [navSteps, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  omega

/-- `regBlocks` distributes over a trailing singleton. -/
theorem regBlocks_append_singleton (init : List (List Nat)) (b : List Nat) :
    regBlocks (init ++ [b]) = regBlocks init ++ (b ++ [0]) := by
  simp only [regBlocks, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil]

/-- `navigateToRegTM_exit dst` is a halt state of `navigateToRegTM dst`. -/
theorem navigateToRegTM_exit_is_halt : ∀ dst,
    (navigateToRegTM dst).halt[navigateToRegTM_exit dst]? = some true
  | 0 => rfl
  | d + 1 => by
      have hidx : navigateToRegTM_exit (d + 1) = (navigateToRegTM d).states + 1 := by
        rw [navigateToRegTM_states]; show 3 * d + 3 = 2 + 3 * d + 1; omega
      show (composedHalt (navigateToRegTM d) (scanPastDelimTM 4 0))[navigateToRegTM_exit (d+1)]?
          = some true
      rw [hidx]
      show (List.replicate (navigateToRegTM d).states false ++ (scanPastDelimTM 4 0).halt)[
            (navigateToRegTM d).states + 1]? = some true
      rw [List.getElem?_append_right (by rw [List.length_replicate]; omega),
          List.length_replicate, Nat.add_sub_cancel_left]
      rfl

/-- A non-halting config cannot sit at a halt state. -/
theorem ne_of_not_halting {M : FlatTM} {ck : FlatTMConfig} {e : Nat}
    (he : M.halt[e]? = some true) (h : haltingStateReached M ck = false) :
    ck.state_idx ≠ e := by
  intro hc
  rw [show haltingStateReached M ck = M.halt.getD ck.state_idx false from rfl, hc,
      List.getD_eq_getElem?_getD, he] at h
  simp at h

/-- **`navigateToRegTM` run + trajectory (combined induction).** The M₁-recursion
puts the growing machine first, so `composeFlatTM_run` needs its own trajectory —
hence run and no-early-halt are proven together. -/
theorem navigateToRegTM_run_traj : ∀ (skipped : List (List Nat)) (tail : List Nat),
    (∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) →
    (runFlatTM (navSteps skipped) (navigateToRegTM skipped.length)
          { state_idx := 0, tapes := [([], 0, (3 : Nat) :: (regBlocks skipped ++ tail))] }
        = some { state_idx := navigateToRegTM_exit skipped.length,
                 tapes := [([], 1 + (regBlocks skipped).length,
                            (3 : Nat) :: (regBlocks skipped ++ tail))] })
    ∧ (∀ k, k < navSteps skipped → ∀ ck,
        runFlatTM k (navigateToRegTM skipped.length)
            { state_idx := 0, tapes := [([], 0, (3 : Nat) :: (regBlocks skipped ++ tail))] }
          = some ck →
        haltingStateReached (navigateToRegTM skipped.length) ck = false) := by
  intro skipped
  induction skipped using List.reverseRecOn with
  | nil =>
      intro tail _
      simp only [regBlocks_nil, List.nil_append, List.length_nil, navSteps_nil,
        navigateToRegTM, navigateToRegTM_exit, Nat.add_zero]
      have h0 : (0 : Nat) < ((3 : Nat) :: tail).length := by simp
      have hsym : ((3 : Nat) :: tail).get ⟨0, h0⟩ < 4 := by simp
      refine ⟨by simpa using stepRightTM_run 4 [] ((3 : Nat) :: tail) 0 h0 hsym, ?_⟩
      intro k hk ck hck
      exact (stepRightTM_no_early_halt 4 [] ((3 : Nat) :: tail) 0 k hk ck hck).2
  | append_singleton init b ih =>
      intro tail h_skip
      have h_skip_init : ∀ x ∈ init, (∀ y ∈ x, y ≠ 0) ∧ (∀ y ∈ x, y < 4) :=
        fun x hx => h_skip x (List.mem_append_left _ hx)
      have h_b : (∀ y ∈ b, y ≠ 0) ∧ (∀ y ∈ b, y < 4) :=
        h_skip b (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      set pre : List Nat := (3 : Nat) :: regBlocks init with hpre
      have hpre_len : pre.length = 1 + (regBlocks init).length := by
        rw [hpre]; simp [Nat.add_comm]
      have hTassoc : (3 : Nat) :: (regBlocks init ++ (b ++ 0 :: tail)) = pre ++ b ++ 0 :: tail := by
        rw [hpre]; simp [List.append_assoc]
      -- IH instance with tail' = b ++ 0 :: tail.
      have ih' := ih (b ++ 0 :: tail) h_skip_init
      have h_run1 : runFlatTM (navSteps init) (navigateToRegTM init.length)
          { state_idx := 0, tapes := [([], 0, pre ++ b ++ 0 :: tail)] }
          = some { state_idx := navigateToRegTM_exit init.length,
                   tapes := [([], pre.length, pre ++ b ++ 0 :: tail)] } := by
        rw [hpre_len, ← hTassoc]; exact ih'.1
      have h_traj1 : ∀ k, k < navSteps init → ∀ ck,
          runFlatTM k (navigateToRegTM init.length)
              { state_idx := 0, tapes := [([], 0, pre ++ b ++ 0 :: tail)] } = some ck →
          ck.state_idx ≠ navigateToRegTM_exit init.length ∧
          haltingStateReached (navigateToRegTM init.length) ck = false := by
        intro k hk ck hck
        rw [← hTassoc] at hck
        have hh := ih'.2 k hk ck hck
        exact ⟨ne_of_not_halting (navigateToRegTM_exit_is_halt init.length) hh, hh⟩
      have h_run2 := scanPast_block pre b tail h_b.1 h_b.2
      have h_halt2 : haltingStateReached (scanPastDelimTM 4 0)
          { state_idx := 1, tapes := [([], pre.length + b.length + 1, pre ++ b ++ 0 :: tail)] }
            = true := rfl
      have h_traj2 : ∀ k, k < b.length + 1 → ∀ ck,
          runFlatTM k (scanPastDelimTM 4 0)
              { state_idx := (scanPastDelimTM 4 0).start, tapes := [([], pre.length, pre ++ b ++ 0 :: tail)] }
            = some ck → haltingStateReached (scanPastDelimTM 4 0) ck = false := by
        intro k hk ck hck
        exact (scanPastDelim_no_early_halt 4 0 [] (pre ++ b ++ 0 :: tail) pre.length b.length
          (scan_block_before 0 pre b tail h_b.1 h_b.2) k hk ck hck).2
      have h_sym_bound : ∀ v, currentTapeSymbol ([], pre.length, pre ++ b ++ 0 :: tail) = some v →
          v < max (navigateToRegTM init.length).sig (scanPastDelimTM 4 0).sig := by
        intro v hv
        have hmax : max (navigateToRegTM init.length).sig (scanPastDelimTM 4 0).sig = 4 := by
          rw [navigateToRegTM_sig]; rfl
        rw [hmax]
        have hlt : pre.length < (pre ++ b ++ 0 :: tail).length := by
          simp only [List.length_append, List.length_cons]; omega
        rw [currentTapeSymbol_in_range hlt] at hv
        injection hv with hv'
        rcases b with _ | ⟨c0, cs⟩
        · rw [← hv']
          have : (pre ++ ([] : List Nat) ++ 0 :: tail).get ⟨pre.length, hlt⟩ = 0 := by
            rw [List.get_eq_getElem,
                List.getElem_append_right (show (pre ++ ([] : List Nat)).length ≤ pre.length by simp)]
            simp
          rw [this]; omega
        · rw [← hv']
          have hc0 : (pre ++ (c0 :: cs) ++ 0 :: tail).get ⟨pre.length, hlt⟩ = c0 := by
            rw [List.get_eq_getElem,
                List.getElem_append_left
                  (show pre.length < (pre ++ (c0 :: cs)).length by simp),
                List.getElem_append_right (Nat.le_refl pre.length)]
            simp
          rw [hc0]; exact h_b.2 c0 (List.mem_cons_self ..)
      have hstate_lt : (0 : Nat) < (navigateToRegTM init.length).states := by
        rw [navigateToRegTM_states]; omega
      -- assemble both conjuncts.
      have hlen_eq : (init ++ [b]).length = init.length + 1 := by simp
      have hT : (3 : Nat) :: (regBlocks (init ++ [b]) ++ tail) = pre ++ b ++ 0 :: tail := by
        rw [regBlocks_append_singleton, hpre]; simp [List.append_assoc]
      have hmachine : navigateToRegTM (init.length + 1)
          = composeFlatTM (navigateToRegTM init.length) (scanPastDelimTM 4 0)
              (navigateToRegTM_exit init.length) := rfl
      have hsteps : navSteps (init ++ [b]) = navSteps init + 1 + (b.length + 1) := by
        rw [navSteps_append_singleton]; omega
      have hstates : (1 : Nat) + (navigateToRegTM init.length).states
          = navigateToRegTM_exit (init.length + 1) := by
        rw [navigateToRegTM_states]; show 1 + (2 + 3 * init.length) = 3 * init.length + 3; omega
      have hhead : pre.length + b.length + 1 = 1 + (regBlocks (init ++ [b])).length := by
        rw [regBlocks_append_singleton, hpre_len]; simp [List.length_append]; omega
      refine ⟨?_, ?_⟩
      · -- run
        have hcomp := composeFlatTM_run
          (navigateToRegTM_valid init.length) (scanPastDelimTM_valid 4 0 (by decide))
          (navigateToRegTM_exit_lt init.length)
          { state_idx := 0, tapes := [([], 0, pre ++ b ++ 0 :: tail)] } hstate_lt
          [] pre.length (pre ++ b ++ 0 :: tail)
          h_sym_bound h_run1 h_traj1 h_run2 h_halt2
        rw [hlen_eq, hsteps, hT, hmachine, ← hstates, ← hhead]
        exact hcomp.1
      · -- traj
        rw [hlen_eq, hsteps, hT, hmachine]
        exact composeFlatTM_no_early_halt
          (navigateToRegTM_valid init.length) (scanPastDelimTM_valid 4 0 (by decide))
          (navigateToRegTM_exit_lt init.length)
          { state_idx := 0, tapes := [([], 0, pre ++ b ++ 0 :: tail)] } hstate_lt
          [] pre.length (pre ++ b ++ 0 :: tail)
          h_sym_bound h_run1 h_traj1 h_traj2

/-- **`navigateToRegTM` run lemma.** -/
theorem navigateToRegTM_run (skipped : List (List Nat)) (tail : List Nat)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) :
    runFlatTM (navSteps skipped) (navigateToRegTM skipped.length)
        { state_idx := 0, tapes := [([], 0, (3 : Nat) :: (regBlocks skipped ++ tail))] }
      = some { state_idx := navigateToRegTM_exit skipped.length,
               tapes := [([], 1 + (regBlocks skipped).length,
                          (3 : Nat) :: (regBlocks skipped ++ tail))] } :=
  (navigateToRegTM_run_traj skipped tail h_skip).1

/-- **`navigateToRegTM` no-early-halt trajectory.** -/
theorem navigateToRegTM_no_early_halt (skipped : List (List Nat)) (tail : List Nat)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) :
    ∀ k, k < navSteps skipped → ∀ ck,
        runFlatTM k (navigateToRegTM skipped.length)
            { state_idx := 0, tapes := [([], 0, (3 : Nat) :: (regBlocks skipped ++ tail))] }
          = some ck →
        haltingStateReached (navigateToRegTM skipped.length) ck = false :=
  (navigateToRegTM_run_traj skipped tail h_skip).2

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

/-! ### `navigateAndTestTM` run + trajectory

`navigateAndTestTM skipped.length` navigates to register `dst`'s content start
and reads that cell: if it is content `v ≠ 0` (register nonempty) it exits at
`navigateAndTestTM_exit_content`; if it is the delimiter `0` (register empty) at
`navigateAndTestTM_exit_delim`. The head and tape are unchanged from the
navigation. -/

/-- The cell at register `dst`'s content start (head `1 + |regBlocks skipped|`)
on the tape `3 :: (regBlocks skipped ++ v :: tail')` is `v`. -/
theorem navAndTest_cell (skipped : List (List Nat)) (v : Nat) (tail' : List Nat)
    (hlt : 1 + (regBlocks skipped).length
        < ((3 : Nat) :: (regBlocks skipped ++ v :: tail')).length) :
    ((3 : Nat) :: (regBlocks skipped ++ v :: tail')).get
        ⟨1 + (regBlocks skipped).length, hlt⟩ = v := by
  have hcell? : ((3 : Nat) :: (regBlocks skipped ++ v :: tail'))[
        1 + (regBlocks skipped).length]? = some v := by
    rw [show ((3 : Nat) :: (regBlocks skipped ++ v :: tail'))
          = ((3 : Nat) :: regBlocks skipped) ++ (v :: tail') from by simp,
        List.getElem?_append_right (by simp),
        show 1 + (regBlocks skipped).length - ((3 : Nat) :: regBlocks skipped).length = 0 by
          simp; omega]
    rfl
  rw [List.get_eq_getElem]
  have h2 := hcell?
  rw [List.getElem?_eq_getElem hlt] at h2
  exact Option.some_inj.mp h2

theorem navAndTest_sym_bound (dst : Nat) (head : Nat) (right : List Nat) (v : Nat)
    (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = v) (hv4 : v < 4) :
    ∀ w, currentTapeSymbol ([], head, right) = some w →
      w < max (navigateToRegTM dst).sig (delimTestTM 4).sig := by
  intro w hw
  rw [currentTapeSymbol_in_range hlt, hget] at hw
  injection hw with hw'
  have hmax : max (navigateToRegTM dst).sig (delimTestTM 4).sig = 4 := by
    rw [navigateToRegTM_sig]; rfl
  rw [hmax, ← hw']; exact hv4

/-- **`navigateAndTestTM` run — content branch** (`v ≠ 0`). -/
theorem navigateAndTestTM_run_content (skipped : List (List Nat)) (v : Nat) (tail' : List Nat)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4))
    (hv0 : v ≠ 0) (hv4 : v < 4) :
    runFlatTM (navSteps skipped + 1 + 1) (navigateAndTestTM skipped.length)
        { state_idx := 0, tapes := [([], 0, (3 : Nat) :: (regBlocks skipped ++ v :: tail'))] }
      = some { state_idx := navigateAndTestTM_exit_content skipped.length,
               tapes := [([], 1 + (regBlocks skipped).length,
                          (3 : Nat) :: (regBlocks skipped ++ v :: tail'))] } := by
  set T : List Nat := (3 : Nat) :: (regBlocks skipped ++ v :: tail') with hTdef
  have hlt : 1 + (regBlocks skipped).length < T.length := by
    rw [hTdef]; simp [List.length_append]; omega
  have hcell : T.get ⟨1 + (regBlocks skipped).length, hlt⟩ = v :=
    navAndTest_cell skipped v tail' hlt
  have h_run1 := navigateToRegTM_run skipped (v :: tail') h_skip
  have h_traj1 : ∀ k, k < navSteps skipped → ∀ ck,
      runFlatTM k (navigateToRegTM skipped.length)
          { state_idx := 0, tapes := [([], 0, T)] } = some ck →
      ck.state_idx ≠ navigateToRegTM_exit skipped.length ∧
      haltingStateReached (navigateToRegTM skipped.length) ck = false := by
    intro k hk ck hck
    rw [hTdef] at hck
    have hh := navigateToRegTM_no_early_halt skipped (v :: tail') h_skip k hk ck hck
    exact ⟨ne_of_not_halting (navigateToRegTM_exit_is_halt skipped.length) hh, hh⟩
  have h_run2 := delimTestTM_run_content 4 (by decide) []
    T (1 + (regBlocks skipped).length) v hlt hcell hv0 hv4
  have hcomp := composeFlatTM_run
    (navigateToRegTM_valid skipped.length) (delimTestTM_valid 4 (by decide))
    (navigateToRegTM_exit_lt skipped.length)
    { state_idx := 0, tapes := [([], 0, T)] }
    (by show (0:Nat) < (navigateToRegTM skipped.length).states; rw [navigateToRegTM_states]; omega)
    [] (1 + (regBlocks skipped).length) T
    (navAndTest_sym_bound skipped.length _ T v hlt hcell hv4)
    h_run1 h_traj1 h_run2 rfl
  rw [show navigateAndTestTM skipped.length
        = composeFlatTM (navigateToRegTM skipped.length) (delimTestTM 4)
            (navigateToRegTM_exit skipped.length) from rfl, hcomp.1,
      show navigateAndTestTM_exit_content skipped.length
            = 1 + (navigateToRegTM skipped.length).states from by
          show (navigateToRegTM skipped.length).states + 1
            = 1 + (navigateToRegTM skipped.length).states; omega]

/-- **`navigateAndTestTM` run — delimiter branch** (register empty). -/
theorem navigateAndTestTM_run_delim (skipped : List (List Nat)) (tail' : List Nat)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) :
    runFlatTM (navSteps skipped + 1 + 1) (navigateAndTestTM skipped.length)
        { state_idx := 0, tapes := [([], 0, (3 : Nat) :: (regBlocks skipped ++ 0 :: tail'))] }
      = some { state_idx := navigateAndTestTM_exit_delim skipped.length,
               tapes := [([], 1 + (regBlocks skipped).length,
                          (3 : Nat) :: (regBlocks skipped ++ 0 :: tail'))] } := by
  set T : List Nat := (3 : Nat) :: (regBlocks skipped ++ 0 :: tail') with hTdef
  have hlt : 1 + (regBlocks skipped).length < T.length := by
    rw [hTdef]; simp [List.length_append]; omega
  have hcell : T.get ⟨1 + (regBlocks skipped).length, hlt⟩ = 0 :=
    navAndTest_cell skipped 0 tail' hlt
  have h_run1 := navigateToRegTM_run skipped (0 :: tail') h_skip
  have h_traj1 : ∀ k, k < navSteps skipped → ∀ ck,
      runFlatTM k (navigateToRegTM skipped.length)
          { state_idx := 0, tapes := [([], 0, T)] } = some ck →
      ck.state_idx ≠ navigateToRegTM_exit skipped.length ∧
      haltingStateReached (navigateToRegTM skipped.length) ck = false := by
    intro k hk ck hck
    rw [hTdef] at hck
    have hh := navigateToRegTM_no_early_halt skipped (0 :: tail') h_skip k hk ck hck
    exact ⟨ne_of_not_halting (navigateToRegTM_exit_is_halt skipped.length) hh, hh⟩
  have h_run2 := delimTestTM_run_delim 4 (by decide) []
    T (1 + (regBlocks skipped).length) hlt hcell
  have hcomp := composeFlatTM_run
    (navigateToRegTM_valid skipped.length) (delimTestTM_valid 4 (by decide))
    (navigateToRegTM_exit_lt skipped.length)
    { state_idx := 0, tapes := [([], 0, T)] }
    (by show (0:Nat) < (navigateToRegTM skipped.length).states; rw [navigateToRegTM_states]; omega)
    [] (1 + (regBlocks skipped).length) T
    (navAndTest_sym_bound skipped.length _ T 0 hlt hcell (by decide))
    h_run1 h_traj1 h_run2 rfl
  rw [show navigateAndTestTM skipped.length
        = composeFlatTM (navigateToRegTM skipped.length) (delimTestTM 4)
            (navigateToRegTM_exit skipped.length) from rfl, hcomp.1,
      show navigateAndTestTM_exit_delim skipped.length
            = 2 + (navigateToRegTM skipped.length).states from by
          show (navigateToRegTM skipped.length).states + 2
            = 2 + (navigateToRegTM skipped.length).states; omega]

/-- **`navigateAndTestTM` no-early-halt** (independent of the branch: the cell
just needs to be in-range `< 4`). -/
theorem navigateAndTestTM_no_early_halt (skipped : List (List Nat)) (v : Nat) (tail' : List Nat)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) (hv4 : v < 4) :
    ∀ k, k < navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (navigateAndTestTM skipped.length)
          { state_idx := 0, tapes := [([], 0, (3 : Nat) :: (regBlocks skipped ++ v :: tail'))] }
        = some ck →
      haltingStateReached (navigateAndTestTM skipped.length) ck = false := by
  set T : List Nat := (3 : Nat) :: (regBlocks skipped ++ v :: tail') with hTdef
  have hlt : 1 + (regBlocks skipped).length < T.length := by
    rw [hTdef]; simp [List.length_append]; omega
  have hcell : T.get ⟨1 + (regBlocks skipped).length, hlt⟩ = v :=
    navAndTest_cell skipped v tail' hlt
  have h_run1 := navigateToRegTM_run skipped (v :: tail') h_skip
  have h_traj1 : ∀ k, k < navSteps skipped → ∀ ck,
      runFlatTM k (navigateToRegTM skipped.length)
          { state_idx := 0, tapes := [([], 0, T)] } = some ck →
      ck.state_idx ≠ navigateToRegTM_exit skipped.length ∧
      haltingStateReached (navigateToRegTM skipped.length) ck = false := by
    intro k hk ck hck
    rw [hTdef] at hck
    have hh := navigateToRegTM_no_early_halt skipped (v :: tail') h_skip k hk ck hck
    exact ⟨ne_of_not_halting (navigateToRegTM_exit_is_halt skipped.length) hh, hh⟩
  have h_traj2 : ∀ k, k < 1 → ∀ ck,
      runFlatTM k (delimTestTM 4)
          { state_idx := (delimTestTM 4).start, tapes := [([], 1 + (regBlocks skipped).length, T)] }
        = some ck → haltingStateReached (delimTestTM 4) ck = false := by
    intro k hk ck hck
    exact (delimTestTM_no_early_halt 4 [] T (1 + (regBlocks skipped).length) k hk ck hck).2.2
  rw [show navigateAndTestTM skipped.length
        = composeFlatTM (navigateToRegTM skipped.length) (delimTestTM 4)
            (navigateToRegTM_exit skipped.length) from rfl]
  exact composeFlatTM_no_early_halt
    (navigateToRegTM_valid skipped.length) (delimTestTM_valid 4 (by decide))
    (navigateToRegTM_exit_lt skipped.length)
    { state_idx := 0, tapes := [([], 0, T)] }
    (by show (0:Nat) < (navigateToRegTM skipped.length).states; rw [navigateToRegTM_states]; omega)
    [] (1 + (regBlocks skipped).length) T
    (navAndTest_sym_bound skipped.length _ T v hlt hcell hv4)
    h_run1 h_traj1 h_traj2

/-- `navigateAndTestTM_exit_content dst` is a halt state. -/
theorem navigateAndTestTM_exit_content_is_halt (dst : Nat) :
    (navigateAndTestTM dst).halt[navigateAndTestTM_exit_content dst]? = some true := by
  show (composedHalt (navigateToRegTM dst) (delimTestTM 4))[
        navigateAndTestTM_exit_content dst]? = some true
  rw [navigateAndTestTM_exit_content]
  show (List.replicate (navigateToRegTM dst).states false ++ (delimTestTM 4).halt)[
        (navigateToRegTM dst).states + delimTestTM_exit_content]? = some true
  rw [List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate, Nat.add_sub_cancel_left]
  rfl

/-- `navigateAndTestTM_exit_delim dst` is a halt state. -/
theorem navigateAndTestTM_exit_delim_is_halt (dst : Nat) :
    (navigateAndTestTM dst).halt[navigateAndTestTM_exit_delim dst]? = some true := by
  show (composedHalt (navigateToRegTM dst) (delimTestTM 4))[
        navigateAndTestTM_exit_delim dst]? = some true
  rw [navigateAndTestTM_exit_delim]
  show (List.replicate (navigateToRegTM dst).states false ++ (delimTestTM 4).halt)[
        (navigateToRegTM dst).states + delimTestTM_exit_delim]? = some true
  rw [List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate, Nat.add_sub_cancel_left]
  rfl

/-! ## 4. Delete-and-rewind machine

For the content branch: step right (so head is at content_start + 1),
then `deleteCarryTM` (deletes the cell before head, shifts suffix left),
then rewind to `0` via the two-phase rewind (`rewindTwoPhaseTM`).

`deleteAndRewindRawTM = composeFlatTM (stepRightTM 4) deleteAndDeleteRewindTM exit`
where `deleteAndDeleteRewindTM = composeFlatTM deleteCarryTM (rewindTwoPhaseTM 4 3) 6`

The two-phase rewind has two halt states (6 = found, 7 = boundary).
We demote the boundary halt using `Compile.joinTwoHalts`, leaving a single
exit at the "found" position. -/

/-- The raw delete-then-rewind:
`deleteCarryTM ⨾ stepLeftTM 4 ⨾ rewindTwoPhaseTM 4 3`, bridging at
`deleteCarryTM`'s exit state `6`.

**The `stepLeftTM` is essential** (surfaced by `#eval` probing):
`deleteCarryTM` leaves the head one cell *past* the tape end (on a blank), and
`rewindTwoPhaseTM`'s phase-1 `scanLeftUntilTM` halts immediately at its boundary
state when started on a blank (it never moves). One unconditional `stepLeftTM`
moves the head onto the last real cell (a `0` filler in the residue zone), from
where the two-phase rewind scans left to the trailing terminator, then to the
leading sentinel at index `0`. -/
def deleteRewindRawTM : FlatTM :=
  composeFlatTM deleteCarryTM
    (composeFlatTM (stepLeftTM 4) (rewindTwoPhaseTM 4 3) 1) 6

/-- The step-right, then delete-then-rewind (no boundary demotion yet):
`stepRightTM 4 ⨾ deleteRewindRawTM`. -/
def stepDeleteRewindRawTM : FlatTM :=
  composeFlatTM (stepRightTM 4) deleteRewindRawTM 1

-- State accounting (`loopTM` tolerates extra non-loop halt states, so no
-- demotion is needed — the boundary halt is simply never reached on a
-- terminator-free residue):
-- `deleteCarryTM.states = 7`, `stepLeftTM.states = 2`, `rewindTwoPhaseTM.states = 8`.
-- inner `stepLeftTM ⨾ rewindTwoPhaseTM`: states `= 2 + 8 = 10`; the rewind's halts
--   `6` (found) / `7` (boundary) become `2 + 6 = 8` / `2 + 7 = 9`.
-- `deleteRewindRawTM.states = 7 + 10 = 17`; halts shift by `7`: found `15`, boundary `16`.
-- `stepRightTM.states = 2`, so in `stepDeleteRewindRawTM`:
--   states `= 2 + 17 = 19`; halts shift by `2`: found `17`, boundary `18`.

-- We keep halt `17` (found/head-rewound-to-0); halt `18` (boundary) is unreached.

def stepDeleteRewindTM_exit : Nat := 17

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
def clearBodyRawTM_exitLoop (dst : Nat) : Nat :=
  (navigateAndTestTM dst).states + stepDeleteRewindTM_exit

-- exitDone: the delimiter branch exit (from justRewindTM in the M₃ slot)
def clearBodyRawTM_exitDone (dst : Nat) : Nat :=
  (navigateAndTestTM dst).states + stepDeleteRewindRawTM.states + justRewindTM_exit

/-! ## 7. `clearRegionTM` via `loopTM`

The loop halts at `clearBodyRawTM.states` when the done branch fires.
We wrap it as a `CompiledCmd` (the single halt state is at `B.states`).
-/

def clearRegionTM (dst : Nat) : FlatTM :=
  loopTM (clearBodyRawTM dst) (clearBodyRawTM_exitDone dst) (clearBodyRawTM_exitLoop dst)

/-! ## 8. Validity -/

theorem deleteRewindRawTM_valid : validFlatTM deleteRewindRawTM :=
  composeFlatTM_valid deleteCarryTM
    (composeFlatTM (stepLeftTM 4) (rewindTwoPhaseTM 4 3) 1) 6
    deleteCarryTM_valid
    (composeFlatTM_valid (stepLeftTM 4) (rewindTwoPhaseTM 4 3) 1
      (stepLeftTM_valid 4) (rewindTwoPhaseTM_valid 4 3 (by decide))
      (show (1 : Nat) < 2 from by decide) rfl (rewindTwoPhaseTM_tapes 4 3))
    (show (6 : Nat) < 7 from by decide) rfl rfl

theorem deleteRewindRawTM_tapes : deleteRewindRawTM.tapes = 1 := rfl

/-- Validity of the inner `stepLeftTM ⨾ rewindTwoPhaseTM` of `deleteRewindRawTM`. -/
theorem innerRewind_valid :
    validFlatTM (composeFlatTM (stepLeftTM 4) (rewindTwoPhaseTM 4 3) 1) :=
  composeFlatTM_valid (stepLeftTM 4) (rewindTwoPhaseTM 4 3) 1
    (stepLeftTM_valid 4) (rewindTwoPhaseTM_valid 4 3 (by decide))
    (show (1 : Nat) < 2 from by decide) rfl (rewindTwoPhaseTM_tapes 4 3)

/-- The inner rewind's "found" halt is state `8` (= rewind's `6` + `stepLeftTM`'s
`2` states). -/
theorem innerRewind_halt_eight :
    (composeFlatTM (stepLeftTM 4) (rewindTwoPhaseTM 4 3) 1).halt[8]? = some true :=
  composeFlatTM_halt_some_intro (stepLeftTM 4) (rewindTwoPhaseTM 4 3) 1 6
    (rewindTwoPhaseTM_halt_six 4 3)

/-- `deleteRewindRawTM`'s "found" halt is state `15` (= `8` + `deleteCarryTM`'s
`7` states). -/
theorem deleteRewindRawTM_halt_fifteen : deleteRewindRawTM.halt[15]? = some true :=
  composeFlatTM_halt_some_intro deleteCarryTM
    (composeFlatTM (stepLeftTM 4) (rewindTwoPhaseTM 4 3) 1) 6 8 innerRewind_halt_eight

/-- `stepDeleteRewindRawTM`'s "found" halt is state `17` (= `15` + `stepRightTM`'s
`2` states). This is `stepDeleteRewindTM_exit`. -/
theorem stepDeleteRewindRawTM_halt_seventeen : stepDeleteRewindRawTM.halt[17]? = some true :=
  composeFlatTM_halt_some_intro (stepRightTM 4) deleteRewindRawTM 1 15 deleteRewindRawTM_halt_fifteen

theorem stepDeleteRewindRawTM_valid : validFlatTM stepDeleteRewindRawTM :=
  composeFlatTM_valid (stepRightTM 4) deleteRewindRawTM 1
    (stepRightTM_valid 4) deleteRewindRawTM_valid
    (show (1 : Nat) < 2 from by decide) rfl deleteRewindRawTM_tapes

theorem stepDeleteRewindRawTM_tapes : stepDeleteRewindRawTM.tapes = 1 := rfl

theorem justRewindTM_valid : validFlatTM justRewindTM :=
  scanLeftUntilTM_valid 4 3 (by decide)

theorem justRewindTM_tapes : justRewindTM.tapes = 1 := rfl

theorem navigateAndTestTM_exit_content_lt (dst : Nat) :
    navigateAndTestTM_exit_content dst < (navigateAndTestTM dst).states := by
  show (navigateToRegTM dst).states + delimTestTM_exit_content <
    (navigateToRegTM dst).states + (delimTestTM 4).states
  show (navigateToRegTM dst).states + 1 < (navigateToRegTM dst).states + 3
  omega

theorem navigateAndTestTM_exit_delim_lt (dst : Nat) :
    navigateAndTestTM_exit_delim dst < (navigateAndTestTM dst).states := by
  show (navigateToRegTM dst).states + delimTestTM_exit_delim <
    (navigateToRegTM dst).states + (delimTestTM 4).states
  show (navigateToRegTM dst).states + 2 < (navigateToRegTM dst).states + 3
  omega

theorem clearBodyRawTM_valid (dst : Nat) : validFlatTM (clearBodyRawTM dst) :=
  branchComposeFlatTM_valid (navigateAndTestTM dst) stepDeleteRewindRawTM justRewindTM
    (navigateAndTestTM_exit_content dst) (navigateAndTestTM_exit_delim dst)
    (navigateAndTestTM_valid dst) stepDeleteRewindRawTM_valid justRewindTM_valid
    (navigateAndTestTM_exit_content_lt dst) (navigateAndTestTM_exit_delim_lt dst)
    (navigateAndTestTM_tapes dst) stepDeleteRewindRawTM_tapes justRewindTM_tapes

theorem clearBodyRawTM_exitDone_lt (dst : Nat) :
    clearBodyRawTM_exitDone dst < (clearBodyRawTM dst).states := by
  show (navigateAndTestTM dst).states + stepDeleteRewindRawTM.states + justRewindTM_exit <
    (navigateAndTestTM dst).states + stepDeleteRewindRawTM.states + justRewindTM.states
  show _ + 1 < _ + 3
  omega

theorem clearBodyRawTM_exitLoop_lt (dst : Nat) :
    clearBodyRawTM_exitLoop dst < (clearBodyRawTM dst).states := by
  show (navigateAndTestTM dst).states + stepDeleteRewindTM_exit <
    (navigateAndTestTM dst).states + stepDeleteRewindRawTM.states + justRewindTM.states
  show _ + 17 < _ + 19 + 3
  omega

theorem clearRegionTM_valid (dst : Nat) : validFlatTM (clearRegionTM dst) :=
  loopTM_valid (clearBodyRawTM dst) (clearBodyRawTM_exitDone dst) (clearBodyRawTM_exitLoop dst)
    (clearBodyRawTM_valid dst)
    (clearBodyRawTM_exitDone_lt dst) (clearBodyRawTM_exitLoop_lt dst)
    (show (clearBodyRawTM dst).tapes = 1 from by
        show (branchComposeFlatTM _ _ _ _ _).tapes = 1
        rw [branchComposeFlatTM_tapes]; exact navigateAndTestTM_tapes dst)

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
