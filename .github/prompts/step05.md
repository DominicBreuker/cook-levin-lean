# Step 05 — Finish the `GenNP → LMGenNP` bookkeeping bridge

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`
- `CookLevin/Complexity/L_to_LM.lean`
- `CookLevin/Complexity/NP/GenNP.lean`
- `CookLevin/Complexity/GenNP_is_hard.lean`

### Coq
- `coqdoc/Complexity.NP.TM.L_to_LM.txt`
- `coqdoc/Complexity.NP.L.GenNP.txt`
- `coqdoc/Complexity.NP.TM.IntermediateProblems.txt`

## Baseline you must preserve

- certificate size now uses `encodable.size` via `certificateMeasure`.
- `genNPToLMGenNPInstance` now forwards explicit size and step bounds instead of zero placeholders.
- the reduction theorem still has admitted computability proof obligations.

## What still needs to be implemented

1. Prove `GenNP_to_LMGenNP` under the strengthened reduction API.
2. Compare the forwarded bounds with the Coq bridge and tighten them where needed.
3. Add helper lemmas showing that the LM instance respects the source problem’s bounded certificate semantics.
4. Keep the bridge compiling and readable for later machine-translation steps.

## Deliverable

A compiling and honest `GenNP → LMGenNP` bridge whose fields are derived from the bounded generic NP instance rather than from ad hoc constants.
