# Step 13 — Remove the final admitted links and publish final status

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`
- every repaired upstream file imported there

### Coq
- `coqdoc/Complexity.NP.SAT.CookLevin.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.SingleTMGenNP_to_TCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatSingleTMGenNP_to_FlatTCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT.txt`

## Baseline you must preserve

- `lake build` currently succeeds.
- the final theorem chain compiles again.
- `fixedTM_to_FlatSingleTMGenNP` and `GenNP_to_SingleTMGenNP` are still admitted.

## What still needs to be implemented

1. Remove the remaining `sorry`s from `CookLevin/Complexity/NP/SAT/CookLevin.lean`.
2. Rebuild the final composition only from honest upstream theorems.
3. Update `README.md` one last time once the chain is fully justified.
4. Do not merge a change here unless the repository still passes `lake build` at the end.

## Deliverable

A compiling final theorem file with no admitted proof on the exported Cook-Levin / clique completeness results, plus an honest final README status update.
