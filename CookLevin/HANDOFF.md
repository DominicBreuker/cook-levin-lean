# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first; they
are the authoritative status and plan. This file tells the next agent exactly
what to do next and what to watch out for.

## Where things stand

- `lake build` ✅ green (3357 jobs).
- `#print axioms CookLevin` = `[propext, sorryAx, Classical.choice, Quot.sound]`
  — conditional on `sorryAx`; also vacuous due to S1/S2/S3 (see ROADMAP).
- **Risk C2 (compiler soundness) is the current focus.** The infrastructure
  layer for the residue-tolerant physical contract is complete. The next phase
  is proving per-op gadgets against this contract.

## Architecture: the residue-tolerant contract

**The physical TM tape never shrinks** (machine-checked in `TapeMono.lean`).
This makes the old exact-tape contract (`exit tape = encodeTape output`)
unsatisfiable for any op that shortens registers. The replacement:

- **Exit tape** = `encodeTape output ++ residue`, where `residue` satisfies
  `ValidResidue` (all cells `< endMark = 3`, i.e. terminator-free).
- **Decoding works** — `decodeTape_encodeTape_append` (proved) shows `decodeTape`
  ignores the residue since it stops at the first `3`.
- **Composition works** — `compileSeq_sound_physical_residue` (proved); residue
  threads mechanically through `compileSeq_compose_physical`.
- **Two-phase rewind** — `rewindTwoPhaseTM` (proved) handles the `head→0` reset
  when residue follows the trailing terminator.

Key types/lemmas (all in `Lang/Compile.lean`):
- `ValidResidue res` := `∀ x ∈ res, x ≠ Compile.endMark`
- `TapeOK out tp` := `∃ res, ValidResidue res ∧ tp = encodeTape out ++ res`
- `compileOp_sound_physical_residue` — the per-op contract (sorry'd, correctly stated)
- `Compile_run_physical_residue` — the top-level contract (sorry'd, correctly stated)

## What's proved (all axiom-clean)

| Layer | Lemma(s) | File | Status |
|-------|----------|------|--------|
| Tape non-shrink | `runFlatTM_single_length_le` | `Complexity/TapeMono.lean` | ✅ |
| Residue decode | `decodeTape_encodeTape_append` | `Lang/Compile.lean` | ✅ |
| Residue helpers | `ValidResidue_nil/append/replicate_zero`, `TapeOK_exact/append_residue` | `Lang/Compile.lean` | ✅ |
| Seq composition | `compileSeq_sound_physical_residue` | `Lang/Compile.lean` | ✅ |
| Two-phase rewind | `rewindTwoPhaseTM` + `_run/_no_early_halt/_valid` | `Lang/ScanLeft.lean` | ✅ |
| Interior scan | `scanLeftToMark_run/_no_early_halt` | `Lang/ScanLeft.lean` | ✅ |
| Insert primitive | `insertCarryTM_run/_no_early_halt/_valid` | `Lang/ShiftTape.lean` | ✅ |
| Delete primitive | `deleteCarryTM_run/_loop_run/_no_early_halt/_valid` | `Lang/ShiftTape.lean` | ✅ |
| Append ops | `appendBit_physical` (appendOne/appendZero) | `Lang/Compile.lean` | ✅ |
| Unsatisfiability | `clear_physical_unsatisfiable` | `Lang/Compile.lean` | ✅ |

## Next steps (ordered by priority)

### 1. Wire `bitDecider_run` to use `Compile_run_physical_residue`

`Compile.bitDecider_run` (line ~2610) currently uses the exact-tape
`Compile_run_physical`. Update it to use the residue version. This is
mechanical: the tape becomes `3 :: (b+1) :: (tl ++ res)` instead of
`3 :: (b+1) :: tl`; the `bitTestTM` gadget only reads positions 0–1 so the
residue is irrelevant. The `composeFlatTM_run` seam-symbol obligation is
discharged by `ValidResidue` (all residue cells `< 4`).

### 2. Prove `compileOp_sound_physical_residue` for append ops

The append ops (`appendOne`/`appendZero`) already have `appendBit_physical`
proved with exact tapes. Lifting to the residue contract should be
straightforward: `insertCarryTM_run` is suffix-polymorphic (it treats residue
as "more suffix"), so `res_out = res_in ++ [carried_symbol]`.

### 3. Build the first deletion-op gadget: `opTail`

`opTail` is the simplest deletion op (removes one cell from a register).
The gadget pattern for deletion ops:
1. Navigate to register `dst` (`Navigate`/`ScanPast`)
2. `deleteCarryTM` the cell to remove (left-shifts suffix, appends `0` filler)
3. `rewindTwoPhaseTM` back to head `0`

Prove the `encodeTape`-level physical contract (in `TapeOK` form), then slot
it into `compileOp_sound_physical_residue`'s case split.

### 4. Remaining deletion ops

After `opTail` validates the pattern, extend to `opClear`, `opHead`, `opCopy`
(shrinking case), `opEqBit`, `opNonEmpty`, `opLength`. Most follow the same
navigate-delete-rewind pattern; `opClear` needs a loop (delete until delimiter).

**Key design question for `opClear`:** the register length is not known
statically. Options: (a) use a loop TM (`loopTM`) that counts deletes until
hitting the delimiter `0`, or (b) use `deleteCarryTM` in a `loopTM` wrapper.
Option (b) is cleaner since `loopTM_run` is already proved. The loop body
deletes one cell; the loop condition checks if the current cell is the
delimiter.

### 5. Restate `compileIfBit`/`compileForBnd` with residue

Expected to generalise like `compileSeq` (their combinators
`branchComposeFlatTM_run`/`loopTM_run` are tape-polymorphic), but confirm when
wiring. Keep **linear** per-fragment budgets.

### 6. Assemble `Compile_run_physical_residue` proof

By induction on `Cmd`, using the per-op residue contracts and the residue
versions of `compileSeq`/`compileIfBit`/`compileForBnd`.

## Key files

| File | Contents |
|------|----------|
| `Complexity/TapeMono.lean` | tape non-shrink finding |
| `Lang/Compile.lean` | compiler, physical contracts, residue infrastructure, ~2580 lines |
| `Lang/ShiftTape.lean` | `insertCarryTM` + `deleteCarryTM` (insert/delete primitives) |
| `Lang/AppendGadget.lean` | `appendAtTM`, `appendAtThenRewindTM`, `appendBit_physical` |
| `Lang/ScanLeft.lean` | `scanLeftUntilTM`, `rewindTwoPhaseTM` (two-phase rewind) |
| `Lang/Navigate.lean` / `ScanPast.lean` | register navigation atoms |
| `Lang/Syntax.lean` / `Semantics.lean` | `Op`/`Cmd`, `Op.eval`, `Op.cost` |
| `Lang/Frame.lean` / `PolyTime.lean` | register bound, S3 bridge, tape-length bound |
| `Complexity/TMPrimitives.lean` | `composeFlatTM_run/no_early_halt`, `loopTM_run` |

## Gotchas

- **Tape can't shrink**: never state an op's exit tape as exactly a shorter
  `encodeTape`. Use the `TapeOK` form with `ValidResidue`.
- **Rewind with residue**: use `rewindTwoPhaseTM` (two left-scans: first to the
  real terminator past the residue, then to the leading sentinel). Never start
  `scanLeftUntilTM` on a `3` — it halts immediately.
- **`omega` vs `Var`**: `Var := Nat` is opaque to `omega`; restate at `Nat`.
- **`omega` vs list lengths**: `simp only [List.length_*]` first.
- **`get`-congruence across list equality**: route through `getElem?`; don't
  `rw` a length-carrying index (ill-typed motive).
- **Core-only files** (`Semantics.lean`, `Frame.lean`): no Mathlib tactics.
- **`haltingStateReached` vs `exit_is_halt`**: bridge via
  `unfold haltingStateReached List.getD; simp only [...]`.
- **`rcases` numeral form**: after `rcases k with _ | _ | _ | k'`, step counts
  are already in `k' + 1` form (not `Nat.succ`). Don't add unnecessary
  `simp only [Nat.succ_eq_add_one]`.
- **`List.not_mem_nil`**: in this Lean 4 version it returns `False` when applied,
  not `¬ x ∈ []`. Use `simp at hx` instead of `absurd`.

## Conventions

- Build: `lake build` from repo root. `lake build Complexity.Lang.X` for one
  module.
- Commit per logical step with a **green build**.
- Axioms: only `propext`/`Quot.sound`/`Classical.choice`. Check with:
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean`
- See ROADMAP "Hard-won gotchas" and "How we work" for full methodology.
