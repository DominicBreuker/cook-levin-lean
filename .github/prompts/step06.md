# Step 06 — Repair the `LMGenNP → mTM → single-tape TM` bridge

## Why this task still exists

The current machine bridge still manufactures dummy machines and forwards acceptance predicates directly.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/LM_to_mTM.lean`
- `CookLevin/Complexity/mTM_to_singleTapeTM.lean`
- `CookLevin/Complexity/NP/TM/IntermediateProblems.lean`
- `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`
- `CookLevin/Complexity/Complexity/MachineSemantics.lean`

### Coq reference files
- `coqdoc/Complexity.NP.TM.LM_to_mTM.txt`
- `coqdoc/Complexity.NP.TM.mTM_to_singleTapeTM.txt`
- `coqdoc/Complexity.NP.TM.M_LM2TM.txt`
- `coqdoc/Complexity.NP.TM.M_multi2mono.txt`
- `coqdoc/Complexity.NP.TM.IntermediateProblems.txt`

## Concrete problems visible today

- `M.M` and `M_multi2mono.M__mono` still return `validFlatTM_default`.
- `lmToMTMInput.accepts := inst.source.rel` simply forwards the source predicate.
- `TMGenNP_mTM_to_TMGenNP_singleTM` is currently just `Iff.rfl` after flattening the tapes.
- None of these theorems currently express real machine simulation.

## Required work

1. Replace the dummy machine constructions with real ones, following the Coq bridge files closely.
2. Make the intermediate machine languages talk about genuine bounded acceptance of those machines.
3. Re-prove `LMGenNP_to_TMGenNP_mTM`, `TMGenNP_mTM_to_TMGenNP_singleTM`, and the composed theorem in `IntermediateProblems.lean` honestly.
4. Preserve theorem names if possible: later stages already import them.

## Done when

- no dummy machine stands on the proof-critical path,
- the bridge theorems are no longer `Iff.rfl` wrappers around unchanged predicates,
- the README can honestly say the TM bridge encodes real machine computations.
