# Step 07 — Finish the single-tape Cook-Levin entry problem

## Why this task still exists

The subproblem layer that starts the Cook-Levin tableau chain is still only lightly connected to the repaired TM bridge.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/SingleTMGenNP.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean`
- `CookLevin/Complexity/NP/TM/IntermediateProblems.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`

### Coq reference files
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.TM_single.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.SingleTMGenNP_to_TCC.txt`

## Concrete problems visible today

- `FlatSingleTMGenNP` / `FlatFunSingleTMGenNP` are present, but the bridge theorem from the repaired single-tape TM problem is still a `sorry`.
- `CookLevin/Complexity/NP/SAT/CookLevin.lean` still has unfinished entry lemmas `fixedTM_to_FlatSingleTMGenNP` and `GenNP_to_SingleTMGenNP`.
- Later tableau reductions depend on the exact shape of this language, so keep the interface close to Coq.

## Required work

1. Finish `TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean` honestly.
2. Re-check the definitions in `Subproblems/SingleTMGenNP.lean` against the Coq subproblem files and repair them where needed.
3. Make the bridge into `FlatSingleTMGenNP` strong enough that `CookLevin.lean` can compose it without hacks.
4. Do not move on to `FlatTCC` yet; this step is only about the entry problem and its immediate bridge.

## Done when

- the single-tape entry reduction has no `sorry`,
- `CookLevin.lean` can import a real bridge into `FlatSingleTMGenNP`,
- the README explains that the Cook-Levin chain now starts from a real single-tape machine problem.
