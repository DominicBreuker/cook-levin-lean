# Step 01 — Finish the encoding and size foundation

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/Complexity/Definitions.lean`
- `CookLevin/Complexity/CanEnumTerm.lean`
- `CookLevin/Complexity/Complexity/NP.lean`

### Coq
- `coqdoc/Complexity.Complexity.Definitions.txt`
- `coqdoc/Complexity.Complexity.EncodableP.txt`
- `coqdoc/Complexity.NP.L.CanEnumTerm_def.txt`
- `coqdoc/Complexity.NP.L.CanEnumTerm.txt`

## Baseline you must preserve

- `encodable` sizes are no longer all zero.
- `index` is no longer constant.
- `CanEnumTerm` now exposes an explicit size-bound field.
- `lake build` is green and must stay green.

## What still needs to be implemented

1. Replace any remaining uses of the default low-priority `encodable` instance on proof-critical types with explicit meaningful instances.
2. Prove the currently admitted `CanEnumTerm.encode_size_bound` obligations honestly.
3. Compare the Lean size interface with the Coq encoding layer and add any missing helper lemmas needed by later steps.
4. Do not weaken the new size-sensitive architecture back to tautological bounds.

## Deliverable

A compiling encoding layer where the important certificate / reduction datatypes all have deliberate, documented size behavior and the `CanEnumTerm` example is fully justified.
