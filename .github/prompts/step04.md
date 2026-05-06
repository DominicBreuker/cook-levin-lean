# Step 04 — Finish the bounded generic NP source problem

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/NP/GenNP.lean`
- `CookLevin/Complexity/GenNP_is_hard.lean`
- `CookLevin/Complexity/CanEnumTerm.lean`
- `CookLevin/Complexity/Complexity/NP.lean`

### Coq
- `coqdoc/Complexity.NP.L.GenNP.txt`
- `coqdoc/Complexity.NP.L.GenNP_is_hard.txt`
- `coqdoc/Complexity.NP.L.GenNPBool.txt`
- `coqdoc/Complexity.NP.L.CanEnumTerm.txt`

## Baseline you must preserve

- `GenNPInput` now carries `maxSize`, `steps`, and certificate-size soundness.
- `genNPRel` explicitly stores a witness-size bound.
- `genNPInstance`, `genNPInstance_spec`, and `NPhard_GenNP` currently compile but still use admitted proofs.

## What still needs to be implemented

1. Replace the admitted `rel_poly` witness in `genNPInstance` with a faithful Coq-style bounded verifier argument.
2. Finish `genNPInstance_spec` and `NPhard_GenNP` honestly.
3. Make sure the bound used in `GenNPInput.maxSize` is the mathematically right one from the certificate relation, not just a convenient over-approximation.
4. Keep the bounded architecture intact; later TM bridge stages depend on these explicit size and step fields.

## Deliverable

A compiling and genuinely proved generic NP source problem that can serve as the hardness starting point for the full Cook-Levin chain.
