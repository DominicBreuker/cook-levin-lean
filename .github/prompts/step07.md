# Step 07 — Finish the single-tape entry problem

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/SingleTMGenNP.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean`
- `CookLevin/Complexity/NP/TM/IntermediateProblems.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`

### Coq
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.TM_single.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.txt`

## Baseline you must preserve

- `FlatSingleTMGenNP` and `FlatFunSingleTMGenNP` now mention actual `acceptsFlatTM` execution.
- the TM-to-flat instance now at least forwards the bounded input/step data instead of hard-coding zero bounds.
- the reduction theorem still uses `sorry`.

## What still needs to be implemented

1. Replace the remaining default machine / empty-input placeholders with the correct flattening of the source single-tape problem.
2. Prove the reduction theorem from `TMGenNP_fixed` to `FlatFunSingleTMGenNP` honestly.
3. Verify that the flattened subproblem statement matches the Coq entry problem, especially on certificate concatenation and time bounds.
4. Keep the final theorem file importing the same theorem names.

## Deliverable

A compiling and honest entry reduction from the repaired single-tape TM problem into the flattened Cook-Levin starting language.
