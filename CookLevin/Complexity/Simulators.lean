import Complexity.Simulators.MultiToSingle
import Complexity.Simulators.CookTableau

set_option autoImplicit false

/-! # TM-to-TM simulators

Aggregator for the simulators introduced as part of the May 2026
pivot:

- `Simulators.MultiToSingle` (Part 5 of ROADMAP) — multi-tape →
  single-tape simulator. Replaces the placeholder `bridgeMachine` in
  `LM_to_mTM.lean` and `mTM_to_singleTapeTM.lean`.
- `Simulators.CookTableau` (Part 6 of ROADMAP) — the Cook 2D
  tableau construction. Replaces the placeholder case-split in
  `Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`.

Both modules are skeletons at the current pivot stage: signatures
and headline bi-implications committed, bodies are `sorry`. -/
