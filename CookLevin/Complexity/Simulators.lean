import Complexity.Simulators.MultiToSingle
import Complexity.Simulators.CookTableau
import Complexity.Simulators.GuessTableau

set_option autoImplicit false

/-! # TM-to-TM simulators

Aggregator for the simulators introduced as part of the May 2026
pivot:

- `Simulators.MultiToSingle` (Part 5 of ROADMAP) — multi-tape →
  single-tape simulator. Replaces the placeholder `bridgeMachine` in
  `LM_to_mTM.lean` and `mTM_to_singleTapeTM.lean`.
- `Simulators.CookTableau` (Part 6 of ROADMAP) — the Cook 2D
  tableau construction (the deterministic core; `cookTableau_correct`
  proven 2026-07-18-d). Replaces the placeholder case-split in
  `Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`.
- `Simulators.GuessTableau` — the prelude/cert-guess layer on top of
  the core (2026-07-19): certificate nondeterminism as row-0 tableau
  nondeterminism; headline `guessTableau_correct`.

`MultiToSingle` is dead code (S2 needs no simulator — see ROADMAP). -/
