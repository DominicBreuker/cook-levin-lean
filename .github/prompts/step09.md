# Step 09 — Repair the `FlatTCC → FlatCC` stage

## Why this task still exists

The current reduction still uses placeholder width/offset/step bookkeeping and has an unfinished proof.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/FlatTCC_to_FlatCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatTCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`

### Coq reference files
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.TCC_to_CC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.FlatCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.CC.txt`

## Concrete problems visible today

- `FlatTCC_to_FlatCC_instance` still sets `offset := 0`, `width := 0`, and `steps := 0`.
- `FlatTCC_to_FlatCC_poly` still contains a `sorry`.
- The flattening lemmas are already substantial; use them instead of rebuilding everything from scratch.

## Required work

1. Make the translated `FlatCC` instance carry the correct offset, width, and step information.
2. Finish `FlatTCC_to_FlatCC_poly` honestly.
3. Add only the helper lemmas that are actually needed for this reduction and the next one.
4. Reuse the existing flatten/unflatten infrastructure in `Subproblems/FlatTCC.lean` and `Subproblems/FlatCC.lean`.

## Done when

- the translated instance no longer has zero bookkeeping fields,
- the reduction theorem has no `sorry`,
- the README records that the `TCC → CC` stage is real.
