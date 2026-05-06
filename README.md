# Cook-Levin in Lean4

This repository is still a **partial Lean port** of the Cook-Levin proof, not yet a faithful formalization of the theorem.

## References

- Coq source: <https://github.com/uds-psl/cook-levin>
- Local Coq documentation mirror: `coqdoc/`
- Researcher workflow entry point: `.github/workflows/researcher.yml`
- Step runner used by the workflow: `.github/scripts/researcher.py`

## Current status at a glance

Verified on **2026-05-06**:

- `lake build` currently **fails** at `CookLevin/Complexity/NP/SAT/CookLevin.lean:29`.
- The repository still contains multiple `sorry`s and several proof-critical placeholders.
- Useful progress already exists and should be preserved:
  - `monotonic`, `inO`, and `inOPoly` are no longer defined as `True`.
  - `inTimePoly` now requires an explicit boolean decider.
  - `polyCertRel` now carries explicit witness-size bounds.
  - `FlatTM` syntax exists, and the tableau subproblem files already contain substantial flattening / unflattening infrastructure.
- The repository still does **not** have a faithful Cook-Levin reduction chain.

### Audit of the previously claimed Step 1–5 progress

- **Old Step 1:** **progress made** (Step 01 partially implemented).
  - ✅ Good: `monotonic` and `inOPoly` remain nontrivial in `CookLevin/Complexity/Complexity/Definitions.lean`.
  - ✅ **Fixed**: Added real `encodable` instance for `List Bool` that provides meaningful sizes (length of the list) instead of always returning 0.
  - ✅ **Fixed**: `boollists_enum_term` in `CanEnumTerm.lean` now produces non-trivial encodings instead of always returning `[]`.
  - Note: `index` still defaults to 0 and the general `encodable` default still gives size 0, but specific instances have been added that provide real size information where needed.
- **Old Step 2:** **mostly complete** and should be treated as the current baseline API.
  - `inTimePoly`, `polyCertRel`, `inNP_intro`, and `P_NP_incl` were meaningfully strengthened in `CookLevin/Complexity/Complexity/NP.lean`.
- **Old Step 3:** **not complete**.
  - `polyTimeComputable` is still `True`, reduction proofs still use `trivial`, and `red_inNP` still contains a `sorry` in `CookLevin/Complexity/Complexity/NP.lean`.
- **Old Step 4:** only **partially** complete.
  - `FlatTM` syntax was introduced, but `execFlatTM` is still dummy, `acceptsFlatTM` is heuristic, and machine validity is still trivialized.
- **Old Step 5:** **not complete**.
  - `CanEnumTerm` still encodes everything to `[]`, `genNPInstance` still has a `sorry`, and `NPhard_GenNP` still rests on the unfinished reduction layer.

### Main blockers still visible in the Lean sources

- `CookLevin/Complexity/Complexity/NP.lean`
  - `polyTimeComputable := True`
  - reduction composition still uses `trivial`
  - `red_inNP` still has a `sorry`
- `CookLevin/Complexity/Complexity/MachineSemantics.lean`
  - `execFlatTM` always returns the initial configuration
  - `acceptsFlatTM` is not real simulation
- `CookLevin/Complexity/CanEnumTerm.lean`
  - the current `boollists_enum_term` encoder is constant
- `CookLevin/Complexity/GenNP_is_hard.lean`
  - `genNPInstance` still has a `sorry`
- `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`, `CookLevin/Complexity/L_to_LM.lean`, `CookLevin/Complexity/LM_to_mTM.lean`, `CookLevin/Complexity/mTM_to_singleTapeTM.lean`
  - certificate bounds, running-time bounds, and machine constructions are still placeholders
- `CookLevin/Complexity/NP/FSAT_to_SAT.lean` and `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/BinaryCC_to_FSAT.lean`
  - both still use brute-force search / enumeration instead of direct polynomial reductions

## Implementation plan

Only the remaining work is listed below. The detailed instructions live in the step prompt files under `.github/prompts/`.

1. **Step 01** — repair encoding and size foundations (`.github/prompts/step01.md`)
2. **Step 02** — finish the polynomial-time reduction API (`.github/prompts/step02.md`)
3. **Step 03** — replace the dummy FlatTM execution layer (`.github/prompts/step03.md`)
4. **Step 04** — finish the generic NP source problem (`.github/prompts/step04.md`)
5. **Step 05** — repair the `GenNP → LMGenNP` bookkeeping bridge (`.github/prompts/step05.md`)
6. **Step 06** — repair the `LMGenNP → mTM → single-tape TM` bridge (`.github/prompts/step06.md`)
7. **Step 07** — finish the single-tape Cook-Levin entry problem (`.github/prompts/step07.md`)
8. **Step 08** — repair the `FlatSingleTMGenNP → FlatTCC` stage (`.github/prompts/step08.md`)
9. **Step 09** — repair the `FlatTCC → FlatCC` stage (`.github/prompts/step09.md`)
10. **Step 10** — repair the `FlatCC → BinaryCC` stage (`.github/prompts/step10.md`)
11. **Step 11** — replace brute-force `BinaryCC → FSAT` (`.github/prompts/step11.md`)
12. **Step 12** — replace the remaining SAT/clique placeholders (`.github/prompts/step12.md`)
13. **Step 13** — rebuild the final theorem chain and final status docs (`.github/prompts/step13.md`)

## How contributors should use the plan

1. Read this `README.md` first.
2. Then read exactly one step file from `.github/prompts/stepNN.md`.
3. Read every Lean and `coqdoc` file named in that step file before editing.
4. Keep the step small and mathematically honest.
5. Run `lake build` before finishing; if it still fails, state exactly which remaining blocker caused the failure.

## Honest repository description

At the moment this repository should be described as:

> a promising Lean scaffold for a Cook-Levin formalization, with substantial SAT and tableau infrastructure, but with major proof-critical gaps still open.
