# Step 09 — Finish `FlatTCC → FlatCC`

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/FlatTCC_to_FlatCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatTCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatCC.lean`

### Coq
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.TCC_to_CC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.FlatCC.txt`

## Baseline you must preserve

- the structural `TCC_to_CC` translation now carries meaningful offset/width values.
- flattening and unflattening lemmas already exist and compile.
- the main reduction theorem still contains admitted proof obligations.

## What still needs to be implemented

1. Finish `FlatTCC_to_FlatCC_poly` honestly under the strengthened reduction API.
2. Compare the chosen offset/width bookkeeping with the Coq reduction and tighten any provisional choices.
3. Keep reusing the existing flatten/unflatten lemmas instead of re-encoding the same facts.
4. Do not break the downstream `FlatCC → BinaryCC` file.

## Deliverable

A compiling and justified `FlatTCC → FlatCC` reduction ready for downstream binary encoding.
