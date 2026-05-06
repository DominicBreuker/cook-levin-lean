# Step 03 — Replace the dummy FlatTM execution layer

## Why this task still exists

The old Step 4 introduced `FlatTM` syntax, but not real machine semantics.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/Complexity/MachineSemantics.lean`
- `CookLevin/Complexity/Complexity/Definitions.lean`
- `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`
- `CookLevin/Complexity/Complexity/NP.lean`

### Coq reference files
- `coqdoc/Undecidability.TM.TM.txt`
- `coqdoc/Complexity.L.TM.TMflat.txt`
- `coqdoc/Complexity.L.TM.TMflatFun.txt`
- `coqdoc/Complexity.L.TM.TMflatComp.txt`
- `coqdoc/Complexity.L.TM.TMflatEnc.txt`
- `coqdoc/Complexity.NP.TM.TMGenNP.txt`

## Concrete problems visible today

- `execFlatTM` always returns the initial configuration.
- `acceptsFlatTM` is only a heuristic check on machine metadata.
- `validFlatTM` is still `True` in `Definitions.lean`.
- Later steps need real machine execution to justify time bounds and acceptance predicates.

## Required work

1. Implement real step-by-step execution for the current `FlatTM` representation, or port the relevant Coq structure closely enough to obtain genuine execution semantics.
2. Replace the heuristic `acceptsFlatTM` / `acceptsInTime` layer with a definition tied to actual execution.
3. Replace `validFlatTM : Prop := True` with a meaningful wellformedness predicate.
4. Repair any immediate users of the machine layer that break because the semantics became real.
5. Keep the API stable where practical: later files already depend on `execFlatTM`, `acceptsFlatTM`, and `acceptsInTime`.

## Done when

- machine execution is no longer dummy,
- machine validity is no longer trivial,
- time-bounded acceptance means real bounded execution,
- the updated README explains which machine semantics are now trustworthy.
