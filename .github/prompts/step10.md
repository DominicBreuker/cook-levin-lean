# Step 10 — Finish `FlatCC → BinaryCC`

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/FlatCC_to_BinaryCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/BinaryCC.lean`

### Coq
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.CC_to_BinaryCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.CC_homomorphisms.txt`

## Baseline you must preserve

- the symbol-by-symbol binary encoding functions and their core lemmas compile.
- the structural target language `BinaryCCLang` is meaningful.
- the reduction theorem still has an admitted backward direction / computability proof.

## What still needs to be implemented

1. Finish `FlatCC_to_BinaryCC_poly` without `sorry`.
2. Check the encoding width/offset formulas carefully against Coq; do not silently change them to easier but wrong values.
3. Add only the binary helper lemmas that are needed by Step 11.
4. Keep the existing theorem names stable for the final composition file.

## Deliverable

A compiling and honest binary encoding stage from flat compatibility constraints to boolean compatibility constraints.
