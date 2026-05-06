# Step 03 — Align the flat machine semantics with Coq

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/Complexity/MachineSemantics.lean`
- `CookLevin/Complexity/Complexity/Definitions.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/SingleTMGenNP.lean`

### Coq
- `coqdoc/Undecidability.TM.TM.txt`
- `coqdoc/Complexity.L.TM.TMflat.txt`
- `coqdoc/Complexity.L.TM.TMflatFun.txt`
- `coqdoc/Complexity.L.TM.TMflatComp.txt`
- `coqdoc/Complexity.NP.TM.TMGenNP.txt`

## Baseline you must preserve

- `validFlatTM` is now structural, not `True`.
- `execFlatTM` now steps through transitions.
- `acceptsFlatTM` is tied to the reached halting state.
- the project currently compiles.

## What still needs to be implemented

1. Check the new step semantics against the Coq flattening development and repair any mismatch in tape movement, blank handling, or halting behavior.
2. Replace any remaining simplifications in `acceptsInTime` and the machine-size bookkeeping with Coq-faithful definitions.
3. Add correctness lemmas connecting the flat execution layer to the later TM bridge files.
4. Keep the APIs `execFlatTM`, `acceptsFlatTM`, and `acceptsInTime` stable unless a Coq-faithful replacement absolutely requires a coordinated update.

## Deliverable

A compiling flat machine semantics layer whose definitions match the intended Coq model closely enough that later TM simulations can be proved on top of it without reworking the interface.
