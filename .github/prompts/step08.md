# Step 08 — Repair the `FlatSingleTMGenNP → FlatTCC` stage

## Why this task still exists

The current `FlatSingleTMGenNP_to_FlatTCC` reduction still uses placeholder bounds and ends with a `sorry`.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatTCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/SingleTMGenNP.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`

### Coq reference files
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.FlatSingleTMGenNP_to_FlatTCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.PTCC_Preludes.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.TCC.txt`

## Concrete problems visible today

- the reduction file still sets `steps := 0`,
- `FlatSingleTMGenNP_to_FlatTCC_poly` still ends with a `sorry`,
- later stages need explicit wellformedness and size facts from `Subproblems/FlatTCC.lean`.

## Required work

1. Replace the placeholder step / size bookkeeping in the reduction with honest values derived from the source instance.
2. Finish `FlatSingleTMGenNP_to_FlatTCC_poly` without `sorry`.
3. Add whichever `FlatTCC` helper lemmas are really needed downstream, instead of forcing later files to duplicate them.
4. Keep the Lean names aligned with the Coq reduction and subproblem files.

## Done when

- the reduction no longer hard-codes zero bounds,
- `FlatSingleTMGenNP_to_FlatTCC_poly` is honest,
- the README can say the first tableau stage is real.
