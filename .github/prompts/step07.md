# Step 07 — Audit and repair the Cook-Levin intermediate languages

## Objective
Preserve the useful tableau encodings while reconnecting them to real machine semantics and explicit complexity bounds.

## Read first
- `/home/runner/work/cook-levin-lean/cook-levin-lean/README.md`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/SingleTMGenNP.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatTCC.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatCC.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/BinaryCC.lean`
- matching Coq docs under `/home/runner/work/cook-levin-lean/cook-levin-lean/coqdoc/Complexity.NP.SAT.CookLevin.Subproblems.*`

## Required work
1. Re-check the meaning of every intermediate-language definition against the repaired machine layer.
2. Add any missing wellformedness or size lemmas needed to prove later reductions polynomial-time.
3. Remove assumptions that were only harmless because the machine model used to be trivial.
4. Keep the flattening/unflattening infrastructure if it is still mathematically sound, but adapt it as needed to the real encodings.

## Concrete expectations
- Be explicit about which invariants each subproblem is meant to enforce.
- Do not postpone necessary size-bound lemmas if later reductions clearly depend on them.
- Reuse existing useful lemmas rather than re-encoding the same facts from scratch.

## Definition of done
- Each intermediate language has a clear meaning tied to real computations.
- The subproblem files expose the wellformedness and bound lemmas later reductions need.
- The preserved flattening infrastructure remains correct under the repaired semantics.
- `lake build` succeeds.
- `README.md` reflects which intermediate subproblems are now trustworthy.
