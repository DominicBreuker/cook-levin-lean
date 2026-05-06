# Step 13 — Rebuild the final theorem chain and final status docs

## Why this task still exists

The final theorem file still has unfinished entry lemmas and is the file that currently breaks `lake build`.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`
- every Lean file repaired in Steps 01–12 that is imported by `CookLevin.lean`

### Coq reference files
- `coqdoc/Complexity.NP.SAT.CookLevin.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.SingleTMGenNP_to_TCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatSingleTMGenNP_to_FlatTCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT.txt`

## Concrete problems visible today

- `CookLevin/Complexity/NP/SAT/CookLevin.lean` still has unfinished theorems `fixedTM_to_FlatSingleTMGenNP` and `GenNP_to_SingleTMGenNP`.
- `lake build` currently fails in this file.
- The README still needs to be updated one final time once the theorem chain is genuinely repaired.

## Required work

1. Make `CookLevin/Complexity/NP/SAT/CookLevin.lean` compile without `sorry`.
2. Rebuild the composition lemmas only from repaired upstream theorems.
3. Re-prove `CookLevin0`, `CookLevin`, and `Clique_complete` without relying on any placeholder theorem left over from earlier stages.
4. Update `README.md` so the status section honestly reflects the final state after your repair.

## Done when

- `lake build` succeeds,
- `CookLevin.lean` contains a real final theorem chain,
- the README gives an honest final status with no stale claims.
