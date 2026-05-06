# Step 01 — Repair encoding and size foundations

## Why this task still exists

The old Step 1 was only partially completed. `monotonic` and `inOPoly` are now nontrivial, but the proof-critical encoding layer is still placeholder-level.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/Complexity/Definitions.lean`
- `CookLevin/Complexity/Complexity/Subtypes.lean`
- `CookLevin/Complexity/CanEnumTerm.lean`
- `CookLevin/Complexity/Complexity/NP.lean`

### Coq reference files
- `coqdoc/Complexity.Complexity.Definitions.txt`
- `coqdoc/Complexity.Complexity.EncodableP.txt`
- `coqdoc/Complexity.Complexity.Subtypes.txt`
- `coqdoc/Complexity.NP.L.CanEnumTerm_def.txt`
- `coqdoc/Complexity.NP.L.CanEnumTerm.txt`

## Concrete problems visible today

- `encodable` only stores `size`, and the default instance gives every value size `0`.
- `index` is currently constant `0`.
- `boollists_enum_term.encode` in `CookLevin/Complexity/CanEnumTerm.lean` always returns `[]`.
- Later steps need real size information for certificate bounds and reduction-size bounds.

## Required work

1. Repair the proof-critical encoding / size interface so later files can talk about real input and certificate sizes.
2. Remove the dependency on the default size-`0` encoding in every file you touch.
3. Make `CanEnumTerm` expose an actual encoding interface that can be used in the `GenNP` hardness proof.
4. Keep names stable where practical; later steps already import these files.
5. Do not try to fix the whole reduction chain here. Only repair the common encoding layer and the immediate fallout.

## Done when

- the touched encoding definitions are no longer placeholder-level,
- `CanEnumTerm` is no longer constant on the critical example instance,
- the repository still compiles at least as far as before your change,
- `README.md` is updated if the repository status materially improves.
