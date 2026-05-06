# Step 05 — Repair the `GenNP → LMGenNP` bookkeeping bridge

## Why this task still exists

The current bridge from generic NP instances to the machine-facing language still uses zero bounds everywhere.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`
- `CookLevin/Complexity/L_to_LM.lean`
- `CookLevin/Complexity/NP/GenNP.lean`
- `CookLevin/Complexity/GenNP_is_hard.lean`

### Coq reference files
- `coqdoc/Complexity.NP.TM.TMGenNP_fixed_mTM.txt`
- `coqdoc/Complexity.NP.TM.L_to_LM.txt`
- `coqdoc/Complexity.NP.L.LMGenNP.txt`
- `coqdoc/Complexity.NP.TM.IntermediateProblems.txt`

## Concrete problems visible today

- `certificateMeasure` is still constantly `0`.
- `genNPToLMGenNPInstance` sets `maxSize := 0` and `steps := 0`.
- `GenNP_to_LMGenNP` still ends with a `sorry`.
- Downstream machine problems cannot be faithful until these bounds mean something.

## Required work

1. Replace `certificateMeasure` with a real size measure tied to the repaired encoding layer.
2. Give `LMGenNP.Instance.maxSize` and `.steps` honest definitions derived from the source verifier and witness bound.
3. Finish `GenNP_to_LMGenNP` without `sorry`.
4. Keep the API readable: later files should be able to use these fields without reverse-engineering your proof.

## Done when

- `certificateMeasure` is not constant `0`,
- the `GenNP → LMGenNP` instance carries real bounds,
- `GenNP_to_LMGenNP` is an actual reduction theorem,
- the README records that the first TM-facing bridge is repaired.
