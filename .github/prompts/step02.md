# Step 02 — Finish the strengthened reduction API

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/Complexity/NP.lean`
- `CookLevin/Complexity/Complexity/Definitions.lean`
- `CookLevin/Complexity/GenNP_is_hard.lean`

### Coq
- `coqdoc/Complexity.Complexity.NP.txt`
- `coqdoc/Complexity.Complexity.PolyTimeComputable.txt`
- `coqdoc/Complexity.Complexity.SpaceBoundsTime.txt`
- `coqdoc/Complexity.Complexity.UpToCPoly.txt`

## Baseline you must preserve

- `polyTimeComputable` is nontrivial.
- reduction witnesses carry explicit output-size bounds.
- the file compiles and downstream imports already rely on the current theorem names.

## What still needs to be implemented

1. Remove the remaining `sorry`s in `reducesPolyMO_transitive`, `red_inNP`, and related closure lemmas.
2. Port the Coq composition and size-bound arguments faithfully; do not replace them with weaker placeholders.
3. Add any missing polynomial-composition lemmas that the current Lean scaffold still lacks.
4. Keep theorem names stable so later files continue to compile.

## Deliverable

A compiling NP / reduction API with honest closure proofs and no admitted lemmas in the proof-critical reduction layer.
