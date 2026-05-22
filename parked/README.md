# Parked — work no longer on the proof path

This directory holds work that was on the proof path *before* the May
2026 strategic pivot (see [`../README.md`](../README.md) and the
"Status update — May 2026" section of [`../CookLevin/ROADMAP.md`](../CookLevin/ROADMAP.md)).
Nothing here is imported by `lake build`; Lake's `lean_lib` root is
`CookLevin/`, so this whole subtree is invisible to the build. The
files are preserved in case the pivot itself overruns or we need to
mine them for primitives later.

## What is here

### `PART2.md`

The detailed implementation plan and progress tracker for the
original Part 2 finish — the "hand-roll the SAT verifier as a flat
Turing machine" route. About 650 lines of substep-by-substep
bookkeeping. Useful as the historical record of *what we tried* and
*how far we got*.

### `CookLevin/Complexity/Complexity/Deciders/SAT_TM.lean` (~6.3K LOC)

The Phase-C "demonstration deciders" — a worked pattern library
built early in Part 2 to validate the proof rhythm before applying
it to the real `EvalCnfTM` decider. Frozen and never on the proof
path, but referenced by the parked `EvalCnfTM/Primitives.lean` for
its `sigSAT`, `encodeInput`, length / symbol-bound lemmas.

### `CookLevin/Complexity/Complexity/Deciders/EvalCnfTM/` (~8.3K LOC total)

The in-progress hand-rolled `EvalCnfTM` primitives:

- `Primitives.lean` (~1.6K LOC) — `sigEval`, `encodeInputWithScratch`,
  generic find-helpers, `writeAtHeadTM`, `scanLeftUntilTM`,
  `clearRegionTM`, `advanceRightTM`.
- `CopyUnary.lean` (~2.4K LOC) — `copyUnaryTM` (7 states), fully
  closed.
- `CompareUnary.lean` (~4K LOC) — `compareUnaryAtMarkerTM` (9
  states), fully closed for all three exit cases (`_run_match`,
  `_run_short`, `_run_long`).
- `PerLiteral.lean` (~0.2K LOC) — the architectural docstring and
  the start of the per-literal evaluator skeleton.

These are the substantial primitives that *were* going to be
composed into the SAT verifier. They are correct and well-tested
within their own scope; they just stop being useful under the
new direction because the higher-level computable layer (new Part 3
of the ROADMAP) compiles SAT verification down to `FlatTM` without
this level of manual scaffolding.

## What stays in the main tree

The Part 2 *framework* artefacts — `Complexity/Complexity/NP.lean`'s
`DecidesBy`, `TMDecider.lean`, `TMEncoding.lean`, and the
combinator library in `TMPrimitives.lean` — remain in
`CookLevin/`. The combinator library in particular is the natural
target for the new layer's compiler output, so it stays on the
proof path even though the higher levels above it have changed
shape.

The `Deciders/EvalCnfTM.lean` and `Deciders/CliqueRelTM.lean`
*stubs* (with their `sorry`-bodied `decider` fields) also remain in
the main tree: they declare the public interface (`inTimePolyTM_evalCnf`,
`sat_NP`, `FlatClique_in_NP`) that the rest of the chain consumes,
and the `sorry`s are exactly the open obligations the new Part 3 of
the ROADMAP closes.

## Reviving parked code

To put a parked file back on the proof path:

1. `git mv parked/CookLevin/Complexity/Complexity/Deciders/<file>.lean CookLevin/Complexity/Complexity/Deciders/<file>.lean`
2. Re-add its `import` line to `CookLevin/Complexity.lean`.
3. Re-run `lake build`.
