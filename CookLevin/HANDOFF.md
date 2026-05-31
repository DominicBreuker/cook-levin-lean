# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first; they
are the authoritative, up-to-date status and plan. This file tells the next
agent exactly what to do and what to watch out for.

## Where things stand

- `lake build` ✅ green (3356 jobs).
- `#print axioms CookLevin` = `[propext, sorryAx, Classical.choice, Quot.sound]`
  — conditional on `sorryAx`; also vacuous due to S1/S2/S3 (see ROADMAP).
- **Risk C2 (compiler soundness) is the current focus.** The physical-contract
  composition framework is now validated:
  - `compileSeq_sound_physical` and `compileSeq_traj_physical` are **proved**
    (sorry-free, axiom-clean).
  - `compileOp_sound_physical`, `compileIfBit_sound_physical`, and
    `compileForBnd_sound_physical` are **stated with the correct physical-contract
    shape** (sorry'd — the correct next steps).
  - `Compile.appendBit_physical` is the proven **template** for per-op physical
    contracts (head-0, linear budget, trajectory).

## Next step: concretise per-op gadgets (step 1c)

The highest-value work is implementing the 10 stub `compileOp`s. Each follows
the validated `appendBit_physical` pattern:

### The per-op physical-contract pattern

1. **Build the gadget TM** for the op and prove its run-to-exit + explicit step
   count + no-early-halt trajectory (like `appendAt_run_steps` /
   `appendAt_no_early_halt` in `AppendGadget.lean`).
2. **Bracket with `ScanLeft.rewindFromEndTM 4 3`** via `composeFlatTM_run` /
   `composeFlatTM_no_early_halt`. The gadget's head exits on the trailing
   `endMark`; `rewindFromEndTM` steps off it first, then scans left to head `0`.
3. **Discharge the three `encodeTape` side-conditions** with the reusable lemmas
   `Compile.encodeTape_get_zero` / `encodeTape_lt_four` /
   `encodeTape_interior_ne_endMark`.
4. **State the `encodeTape`-level `*_physical` contract** (head-`0` exit, tape =
   `encodeTape output`, trajectory, linear budget `≤ A·tapeLen + B`) like
   `appendBit_physical`.

### Priority order for ops (by likely difficulty)

1. **`opClear dst`** — scan to register `dst`, overwrite contents with nothing
   (shift tail left). Simplest length-changing op. `Op.eval (.clear dst) s =
   s.set dst []`.
2. **`opNonEmpty dst src`** — scan to `src`, check first symbol after delimiter
   (`0` = empty → write `[0]` to `dst`; else `[1]`). Read-only on `src`.
3. **`opHead dst src`** — read first symbol of `src`, write to `dst` (single
   symbol). Similar to `opNonEmpty`.
4. **`opEqBit dst src1 src2`** — compare first symbols of `src1` and `src2`.
5. **`opTail dst src`** — drop first symbol of `src`, write rest to `dst`.
6. **`opCopy dst src`** — copy full register. Needs shift if lengths differ.
7. **`takeAt` / `dropAt` / `concat` / `consLen`** — complex length-as-value ops.

### After per-op gadgets: the assembly (steps 1b-3, 1b-4, 1d)

Once `compileOp_sound_physical` has all cases proved:

1. **Prove `compileIfBit_sound_physical`** — wire `branchComposeFlatTM_run` +
   `joinTwoHalts` + the tester's 2-step read (already sorry-free in
   `Compile.lean`).
2. **Prove `compileForBnd_sound_physical`** — wire `loopTM_run` (proven in
   `TMPrimitives.lean`) with the body's physical contract.
3. **Assemble `Compile_run_physical`** by induction on `Cmd`, using the four
   physical-contract lemmas. Lift per-fragment linear budgets to a quadratic
   total via `Cmd.encodeTape_eval_length_le` (proven).
4. **Re-derive `Compile_sound`** from `Compile_run_physical` +
   `decodeTape_encodeTape'`.

### `Op.inBounds` precondition

The physical-contract lemmas require `Op.inBounds o s` (all register operands
in bounds). This is defined in `Compile.lean` and needs to be threaded through
the `Cmd`-level induction. The `Frame.lean` register-count bound
(`Cmd.eval_length_le`) ensures this is satisfiable.

## Key files

| File | Contents |
|------|----------|
| `Lang/Compile.lean` | Compiler, composition lemmas, physical contracts |
| `Lang/AppendGadget.lean` | `appendAtTM`, `appendAtThenRewindTM`, physical contract |
| `Lang/ScanLeft.lean` | `rewindFromEndTM` (the corrected head-rewind) |
| `Lang/Navigate.lean` | `scan_to_mark` (register navigation atom) |
| `Lang/ShiftTape.lean` | `insertCarryTM` (the tape-shifting primitive) |
| `Lang/Syntax.lean` | `Op`, `Cmd` definitions |
| `Lang/Semantics.lean` | `Op.eval`, `Op.cost`, `Cmd.size_eval_le` |
| `Lang/Frame.lean` | `Cmd.eval_length_le` (register-count bound) |
| `Lang/PolyTime.lean` | `Cmd.encodeTape_eval_length_le`, S3 bridge |
| `Complexity/TMPrimitives.lean` | `composeFlatTM_run/no_early_halt`, `loopTM_run` |

## Gotchas (you will likely encounter these)

- **Rewind gotcha**: gadgets exit with head on the **trailing** `endMark = 3`.
  Use `ScanLeft.rewindFromEndTM` (steps off it first), never
  `scanLeftUntilTM`/`rewindToStart_run` directly (they halt immediately on `3`).
- **`omega` vs `Var`**: `Var := Nat` is opaque to `omega`. Use `Nat.*` lemmas
  or restate at `Nat`.
- **`omega` vs list lengths**: `omega` can't simplify `[].length` or
  `(h :: t).length`. Use `simp only [List.length_nil/cons]` first.
- **`subst` gotcha**: `subst h` for `h : a = b` eliminates the more recently
  introduced variable. Don't reference the eliminated variable afterward.
- **`get`-congruence across list equality**: don't `rw [hl]` when the index has
  a length proof (ill-typed motive). Route through `getElem?`:
  `congrArg (·[i]?) hl`, then `List.getElem?_eq_getElem`.
- **`set`/Mathlib tactics**: unavailable in `Lang/Semantics.lean` and
  `Lang/Frame.lean` (core-only files).
- **Nested `set`/`let` over `State.set`/`State.get`**: `isDefEq` blows up
  exponentially. Flatten with `simp only [Cmd.eval_op, Op.eval]`.
- **`haltingStateReached` vs `exit_is_halt`**: `haltingStateReached M ck =
  M.halt.getD ck.state_idx false` (uses `getD`), while `exit_is_halt` uses
  `getElem?`. To bridge: `unfold haltingStateReached; unfold List.getD;
  simp only [heq, exit_is_halt, Option.getD]`.

## Conventions

- Build: `lake build` from repo root.
- Commit per logical step with a **green build**; record gaps in commit messages.
- New results must be `#print axioms`-clean (only `propext` / `Quot.sound` /
  `Classical.choice`). **No new axioms.** Decompose `sorry`s; don't elaborate.
- Axiom check:
  ```
  LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean
  ```
  with `#print axioms <name>`.
- See ROADMAP "Hard-won gotchas" and "How we work" for the full methodology.
