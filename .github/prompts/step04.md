# Step 04 — Introduce a meaningful Turing-machine layer

## Objective
Replace the `Unit`-based machine model with real machine syntax, encoding, execution, and time-bounded computation notions.

## Read first
- `README.md`
- `CookLevin/Complexity/Complexity/Definitions.lean`
- relevant machine files already present under `CookLevin/Complexity/`
- `coqdoc/Complexity.NP.TM.TMGenNP.txt`
- `coqdoc/Undecidability.TM.TM.txt`
- `coqdoc/Complexity.L.TM.TMflat.txt`

## Required work
1. Replace `TM := Unit` and `flatTM := Unit` with real machine-level datatypes or faithful imports/ports of the Coq structures.
2. Introduce the execution semantics and the time-bounded computation predicates used later in the NP source problems.
3. Replace placeholder machine-validation and machine-computability definitions such as `computableTime'` with meaningful statements.
4. Adapt any directly affected files so the repository compiles against the new machine layer.

## Concrete expectations
- Prefer faithful reuse of the Coq machine architecture rather than inventing a substantially different model.
- Make sure encodings and sizes integrate with the repaired complexity layer from earlier steps.
- Do not leave a dummy machine constant standing in for real semantics.

## Definition of done
- Lean can state and prove nontrivial facts about real machine execution/time.
- `computableTime'` is no longer `True`.
- Placeholder machine abbreviations are gone from the core API.
- `lake build` succeeds.
- `README.md` records which machine semantics are now in place and what remains to be ported.
