# Step 11 — Replace brute-force `BinaryCC → FSAT`

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/BinaryCC_to_FSAT.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/BinaryCC.lean`
- `CookLevin/Complexity/NP/FSAT.lean`

### Coq
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC.txt`
- `coqdoc/Complexity.NP.SAT.FSAT.FSAT.txt`
- `coqdoc/Complexity.NP.SAT.FSAT.FormulaEncoding.txt`

## Baseline you must preserve

- the current file compiles, but it still uses `allBitStrings`, `acceptingRunsFrom`, and an OR over enumerated traces.
- this is still the main exponential placeholder in the chain.

## What still needs to be implemented

1. Delete the brute-force search path from the proof-critical reduction.
2. Port the direct Coq formula construction from binary tableau constraints to FSAT.
3. Prove both directions of correctness for the direct encoding.
4. Prove polynomial output-size / computability for the new construction under the current reduction API.
5. Keep `BinaryCC_to_FSAT_poly` as the exported theorem name.

## Deliverable

A compiling direct `BinaryCC → FSAT` reduction with no trace enumeration on the critical path.
