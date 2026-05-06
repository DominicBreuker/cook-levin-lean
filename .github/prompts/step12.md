# Step 12 — Repair the SAT and clique side

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/NP/FSAT_to_SAT.lean`
- `CookLevin/Complexity/NP/SAT.lean`
- `CookLevin/Complexity/NP/FSAT.lean`
- `CookLevin/Complexity/NP/kSAT_to_SAT.lean`
- `CookLevin/Complexity/NP/kSAT_to_FlatClique.lean`
- `CookLevin/Complexity/NP/FlatClique.lean`

### Coq
- `coqdoc/Complexity.NP.SAT.FSAT.FSAT_to_SAT.txt`
- `coqdoc/Complexity.NP.SAT.SAT_inNP.txt`
- `coqdoc/Complexity.NP.SAT.kSAT_to_SAT.txt`
- `coqdoc/Complexity.NP.Clique.FlatClique.txt`
- `coqdoc/Complexity.NP.Clique.kSAT_to_FlatClique.txt`

## Baseline you must preserve

- `FlatClique` is now a real flat clique predicate over wellformed graphs.
- the files compile, but the main SAT/clique theorems still use `sorry` and `FSAT_to_SAT` is still search-based.

## What still needs to be implemented

1. Replace the search-based `FSAT → SAT` / `FSAT → 3SAT` constructions with direct syntactic translations.
2. Finish `SAT_inNP.sat_NP`, `kSAT_to_SAT`, `kSAT_to_FlatClique_poly`, and `FlatClique_in_NP` honestly.
3. Keep the new `FlatClique` definition mathematically meaningful; do not collapse it back to `True`.
4. Ensure the final theorem file can use these exports unchanged.

## Deliverable

A compiling SAT/clique side with honest NP-membership proofs and direct polynomial reductions.
