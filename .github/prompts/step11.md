# Step 11 — Replace brute-force `BinaryCC → FSAT`

## Why this task still exists

This is still the major exponential-time placeholder in the Cook-Levin chain.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/BinaryCC_to_FSAT.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/BinaryCC.lean`
- `CookLevin/Complexity/NP/FSAT.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`

### Coq reference files
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC.txt`
- `coqdoc/Complexity.NP.SAT.FSAT.FSAT.txt`
- `coqdoc/Complexity.NP.SAT.FSAT.FormulaEncoding.txt`

## Concrete problems visible today

- `allBitStrings` enumerates all candidate rows.
- `acceptingRunsFrom` enumerates all candidate traces.
- the final reduction formula is an OR over enumerated traces.
- `BinaryCC_to_FSAT_poly` still ends with a `sorry`.

## Required work

1. Remove the brute-force search path from the reduction.
2. Construct the FSAT formula directly from the BinaryCC tableau constraints.
3. Prove both directions of correctness for the direct encoding.
4. Prove polynomial output size and polynomial-time computability for the new construction.
5. Keep the theorem name `BinaryCC_to_FSAT_poly` if possible; the final theorem file already imports it.

## Done when

- `allBitStrings` and `acceptingRunsFrom` are no longer on the proof-critical path,
- the reduction is direct and syntactic,
- the README explicitly says the exponential BinaryCC placeholder is gone.
