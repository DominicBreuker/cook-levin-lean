# Step 11 — Re-prove NP-membership results using the repaired verifier framework

## Objective
Make the “in NP” side of the completeness theorems mathematically faithful under the repaired verifier infrastructure.

## Read first
- `/home/runner/work/cook-levin-lean/cook-levin-lean/README.md`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/SAT.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/FSAT.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/kSAT.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/FlatClique.lean`
- any dedicated in-NP helper files
- matching Coq docs for SAT, kSAT, and clique NP membership

## Required work
1. Rebuild the NP-membership witnesses for SAT, kSAT, FlatClique, and any other proof-critical languages.
2. Provide explicit certificate relations and polynomial-size witness bounds.
3. Prove that the repaired verifiers run in polynomial time using the new complexity framework.
4. Remove any NP-membership theorem that still succeeds only because of older trivial infrastructure.

## Concrete expectations
- Keep the witness relations simple and explicit.
- Reuse common certificate-verifier lemmas where possible to avoid duplication.
- Make sure the final completeness theorems will be able to cite these NP-membership results directly.

## Definition of done
- The main target languages used in the final theorem chain are in NP for genuine mathematical reasons.
- The NP-membership theorems compile against the repaired complexity and reduction layers.
- `lake build` succeeds.
- `README.md` records which in-NP results are now fully faithful.
