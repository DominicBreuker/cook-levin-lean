# Step 04 — Finish the generic NP source problem

## Why this task still exists

The old Step 5 did not complete. The generic source problem is still blocked by placeholder encodings and an unfinished hardness proof.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/NP/GenNP.lean`
- `CookLevin/Complexity/GenNP_is_hard.lean`
- `CookLevin/Complexity/CanEnumTerm.lean`
- `CookLevin/Complexity/Complexity/NP.lean`

### Coq reference files
- `coqdoc/Complexity.NP.L.GenNP.txt`
- `coqdoc/Complexity.NP.L.GenNP_is_hard.txt`
- `coqdoc/Complexity.NP.L.GenNPBool.txt`
- `coqdoc/Complexity.NP.L.CanEnumTerm.txt`
- `coqdoc/Complexity.NP.L.CanEnumTerm_def.txt`

## Concrete problems visible today

- `GenNPInput` is still very small compared with the Coq source problem interface.
- `genNPInstance` still contains a `sorry`.
- `NPhard_GenNP` still relies on the unfinished reduction layer and weak encoding interface.
- The current `CanEnumTerm` example instance is still placeholder-level.

## Required work

1. Make the Lean `GenNP` layer follow the Coq architecture much more closely.
2. Finish `genNPInstance` and `genNPInstance_spec` without `sorry`.
3. Re-prove `NPhard_GenNP` against the repaired `inNP` / reduction API.
4. Carry whatever concrete encoding facts are needed from `CanEnumTerm` into the proof instead of hiding them in comments.
5. Keep the source problem reusable for the downstream TM bridge.

## Done when

- `GenNP` no longer depends on placeholder encodings,
- `genNPInstance` and `NPhard_GenNP` are honest proofs,
- the README says the generic hardness starting point is really available.
