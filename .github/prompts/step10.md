# Step 10 — Repair the `FlatCC → BinaryCC` stage

## Why this task still exists

This stage still hard-codes placeholder bounds and has not been finished under the stronger reduction notion.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/FlatCC_to_BinaryCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/BinaryCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`

### Coq reference files
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.CC_to_BinaryCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.CC_homomorphisms.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.FlatCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC.txt`

## Concrete problems visible today

- `FlatCC_to_BinaryCC_instance` still sets `offset := 0`, `width := 0`, and `steps := 0`.
- `FlatCC_to_BinaryCC_poly` still ends with a `sorry`.
- The binary subproblem file already contains the target language definition; the missing work is mainly the honest reduction and its bookkeeping.

## Required work

1. Use the Coq `CC_to_BinaryCC` construction as the blueprint.
2. Replace the placeholder bookkeeping fields with real values.
3. Finish `FlatCC_to_BinaryCC_poly` under the repaired `⪯p` API.
4. Add only the binary-encoding lemmas that are genuinely needed.

## Done when

- the translated BinaryCC instance carries real bounds,
- `FlatCC_to_BinaryCC_poly` has no `sorry`,
- the README can say the `CC → BinaryCC` stage is no longer placeholder-level.
