# Step 08 — Finish `FlatSingleTMGenNP → FlatTCC`

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/SingleTMGenNP.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatTCC.lean`

### Coq
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatSingleTMGenNP_to_FlatTCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.PTCC_Preludes.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC.txt`

## Baseline you must preserve

- the reduction file now preserves the source `steps` field in the generated witness skeleton.
- the helper `mkTCCWitness` and flatten/unflatten support compile.
- correctness is still admitted.

## What still needs to be implemented

1. Replace the toy tableau witness with the real Coq-style tableau construction.
2. Finish `FlatSingleTMGenNP_to_FlatTCCLang_poly` without `sorry`.
3. Add only the helper lemmas that are genuinely needed by Steps 09 and 10.
4. Ensure the translation preserves bounded execution semantics from the new single-tape problem definition.

## Deliverable

A compiling and faithful first Cook-Levin tableau reduction whose produced `FlatTCC` instance carries the right structural data and correctness proof.
