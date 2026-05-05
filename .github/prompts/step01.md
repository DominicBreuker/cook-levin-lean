# Step 01 — Replace the placeholder complexity foundations

## Objective
Replace the `True`-based complexity placeholders with real encoding, size, monotonicity, and polynomial-growth infrastructure that future steps can build on.

## Read first
- `README.md`
- `CookLevin/Complexity/Complexity/Definitions.lean`
- `coqdoc/Complexity.Complexity.PolyTimeComputable.txt`
- `coqdoc/Complexity.Complexity.Definitions.txt`
- `coqdoc/Complexity.Complexity.ONotation.txt`
- `coqdoc/Complexity.Complexity.Monotonic.txt`

## Required work
1. Replace the placeholder `encodable` scaffold with a meaningful encoding and size interface, or port the corresponding Coq setup closely enough that size bounds can be stated and used downstream.
2. Replace `monotonic`, `inOPoly`, and any directly related placeholder definitions with mathematically meaningful ones.
3. Introduce the basic closure lemmas and helper definitions needed for later proofs about polynomial bounds and composition.
4. Remove or rewrite any theorem in this area that is currently true only because one of the placeholder definitions is `True`.
5. Keep the rest of the repository compiling, even if some downstream files need temporary but mathematically honest adaptations.

## Concrete expectations
- Prefer matching Coq names, theorem shapes, and decomposition where practical.
- Do not silently keep a placeholder under a new name.
- If some downstream theorems must temporarily weaken or be deferred, make that explicit in `README.md`.

## Definition of done
- `monotonic` and `inOPoly` are no longer trivial propositions.
- The complexity layer can state real polynomial-growth facts and use them in proofs.
- `inTimePoly_linear` is no longer a vacuous proof pattern for arbitrary predicates.
- `lake build` succeeds.
- `README.md` is updated to reflect what placeholder machinery was removed and what remains.
