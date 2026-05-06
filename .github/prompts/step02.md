# Step 02 — Finish the polynomial-time reduction API

## Why this task still exists

The old Step 3 never actually landed. The reduction layer still accepts trivial runtime witnesses.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/Complexity/NP.lean`
- `CookLevin/Complexity/Complexity/Definitions.lean`
- `CookLevin/Complexity/Complexity/MachineSemantics.lean`
- `CookLevin/Complexity/GenNP_is_hard.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`

### Coq reference files
- `coqdoc/Complexity.Complexity.NP.txt`
- `coqdoc/Complexity.Complexity.PolyTimeComputable.txt`
- `coqdoc/Complexity.Complexity.SpaceBoundsTime.txt`
- `coqdoc/Complexity.Complexity.UpToCPoly.txt`

## Concrete problems visible today

- `polyTimeComputable` is defined as `True`.
- `reducesPolyMO_reflexive` and `reducesPolyMO_transitive` use `trivial` runtime proofs.
- `red_inNP` still contains a `sorry` because the current reduction API does not control output size strongly enough.
- Downstream hardness theorems already import this API, so you must preserve theorem names if possible.

## Required work

1. Replace `polyTimeComputable` with a nontrivial interface that the rest of the repository can actually use.
2. Strengthen `ReductionWitness` so reduction proofs no longer succeed with `trivial` runtime witnesses.
3. Finish `reducesPolyMO_transitive` with honest composition of the strengthened witness.
4. Finish `red_inNP` without `sorry`; in particular, handle the certificate-size bound after reduction correctly.
5. Update only the directly affected downstream files needed to keep the repository coherent.

## Done when

- `polyTimeComputable` is no longer `True`,
- the main reduction lemmas compile without `trivial` placeholder runtime proofs,
- `red_inNP` has no `sorry`,
- `README.md` records that the reduction layer is now genuinely stronger.
