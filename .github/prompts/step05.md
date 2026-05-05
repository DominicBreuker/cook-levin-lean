# Step 05 — Rebuild the generic NP source problem faithfully

## Objective
Repair the generic NP source problem so hardness starts from a mathematically valid formulation rather than scaffolded placeholder witnesses.

## Read first
- `README.md`
- `CookLevin/Complexity/NP/GenNP.lean`
- `CookLevin/Complexity/GenNP_is_hard.lean`
- `CookLevin/Complexity/CanEnumTerm.lean`
- `coqdoc/Complexity.NP.L.GenNP.txt`
- `coqdoc/Complexity.NP.L.GenNP_is_hard.txt`
- `coqdoc/Complexity.NP.L.CanEnumTerm.txt`

## Required work
1. Repair `GenNPInput` so its verifier side depends on the new nontrivial NP machinery.
2. Ensure certificate encoding and size information are represented explicitly enough to support the hardness proof.
3. Rebuild `genNPInstance`, `genNPInstance_spec`, and `NPhard_GenNP` against the repaired `inNP` and `⪯p` APIs.
4. Remove any remaining use of `inTimePoly_linear _` or similarly placeholder witnesses in this area.

## Concrete expectations
- Keep the generic source problem reusable for downstream reductions.
- Match the Coq architecture closely so later files can port more directly.
- If the hardness proof needs helper lemmas about encodings or certificate bounds, add them cleanly.

## Definition of done
- `GenNP` is no longer justified by trivial verifier infrastructure.
- `NPhard_GenNP` is proved using the repaired NP and reduction notions.
- The generic source problem carries real certificate information.
- `lake build` succeeds.
- `README.md` states that the hardness starting point is now faithful or explains any remaining gap precisely.
