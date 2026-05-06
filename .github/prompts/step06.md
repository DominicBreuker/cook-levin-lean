# Step 06 — Replace the remaining dummy machine bridge constructions

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/LM_to_mTM.lean`
- `CookLevin/Complexity/mTM_to_singleTapeTM.lean`
- `CookLevin/Complexity/NP/TM/IntermediateProblems.lean`
- `CookLevin/Complexity/Complexity/MachineSemantics.lean`

### Coq
- `coqdoc/Complexity.NP.TM.LM_to_mTM.txt`
- `coqdoc/Complexity.NP.TM.mTM_to_singleTapeTM.txt`
- `coqdoc/Complexity.NP.TM.M_LM2TM.txt`
- `coqdoc/Complexity.NP.TM.M_multi2mono.txt`
- `coqdoc/Complexity.NP.TM.IntermediateProblems.txt`

## Baseline you must preserve

- the bridge files compile and compose.
- the new flat machine semantics is available to support real simulation proofs.
- the current machine constructors are still placeholders and must not be treated as final.

## What still needs to be implemented

1. Replace the remaining dummy machine constructors with Coq-faithful machine encodings.
2. Prove `LMGenNP_to_TMGenNP_mTM` and `TMGenNP_mTM_to_TMGenNP_singleTM` honestly.
3. Ensure the intermediate problems express genuine bounded acceptance of the constructed machines.
4. Keep `IntermediateProblems.lean` composing cleanly and keep `lake build` green after every change.

## Deliverable

A compiling machine bridge that no longer forwards acceptance predicates through dummy machines and instead exposes real simulation statements.
