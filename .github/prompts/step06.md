# Step 06 — Repair the bridge from generic NP to fixed machine problems

## Objective
Make the `GenNP → LM → mTM → single-tape TM` pipeline encode genuine bounded machine computations instead of forwarding placeholder predicates.

## Read first
- `README.md`
- `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`
- `CookLevin/Complexity/L_to_LM.lean`
- `CookLevin/Complexity/LM_to_mTM.lean`
- `CookLevin/Complexity/mTM_to_singleTapeTM.lean`
- `CookLevin/Complexity/NP/TM/IntermediateProblems.lean`
- matching Coq docs under `coqdoc/Complexity.NP.TM.*`

## Required work
1. Replace trivial certificate-size bookkeeping such as `certificateMeasure := 0` with real size bounds.
2. Remove dummy machine constants and replace them with real machine constructions or faithful ports of the Coq artifacts.
3. Make `maxSize` and `steps` express genuine bounds tied to the encoded computation.
4. Re-prove each bridge reduction using the repaired reduction notion and real machine semantics.

## Concrete expectations
- Do not merely rename the placeholder fields; connect them to actual encodings/executions.
- Preserve the high-level reduction structure from the README unless a documented correction is required.
- Keep the bridge theorems individually understandable and composable.

## Definition of done
- The bridge problems encode genuine bounded machine acceptance questions.
- `LM_to_mTM`, `mTM_to_singleTapeTM`, and the composed intermediate results are real polynomial-time reductions.
- Placeholder constants like the current manufactured machines are gone from the proof-critical path.
- `lake build` succeeds.
- `README.md` records which bridge problems are now faithful.
