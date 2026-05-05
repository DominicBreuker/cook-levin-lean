# Step 12 — Recompose the final theorem chain

## Objective
Rebuild the final Cook-Levin composition theorems so they now rest entirely on the repaired foundations.

## Read first
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`
- the repaired hardness, reduction, and NP-membership files from earlier steps
- `coqdoc/Complexity.NP.SAT.CookLevin.txt`

## Required work
1. Rebuild the composition proofs for the main reduction chain using the repaired intermediate theorems.
2. Re-prove `CookLevin0`, `CookLevin`, and `Clique_complete` against the repaired notions of NP-hardness, reduction, and NP membership.
3. Remove any leftover placeholder assumptions, dummy witnesses, or transitional hacks that were only there to keep earlier steps compiling.
4. Keep the final theorem file readable and aligned with the Coq structure.

## Concrete expectations
- The final theorem names should stay stable if possible.
- Prefer clean composition through already repaired lemmas rather than packing everything into one huge proof.
- If some final theorem still cannot be restored honestly, document the exact remaining blocker in `README.md`.

## Definition of done
- The final theorem chain compiles using only the repaired infrastructure.
- `CookLevin0`, `CookLevin`, and `Clique_complete` are mathematically faithful statements, not artifacts of placeholder definitions.
- `lake build` succeeds.
- `README.md` clearly states that the final theorem chain has been restored, or precisely what is still missing.
