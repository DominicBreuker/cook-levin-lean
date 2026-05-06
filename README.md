# Cook-Levin in Lean4

This repository is still a **partial Lean port** of the Cook-Levin proof, but it now has a **compiling end-to-end architecture scaffold** that is much closer to the Coq development than the earlier placeholder baseline.

## References

- Coq source: <https://github.com/uds-psl/cook-levin>
- Local Coq documentation mirror: `coqdoc/`
- Researcher workflow entry point: `.github/workflows/researcher.yml`
- Step runner used by the workflow: `.github/scripts/researcher.py`

## Current status at a glance

Verified on **2026-05-06**:

- `lake build` currently **succeeds**.
- The repository still contains multiple `sorry`s and several proof-critical theorems remain unfinished.
- The main architectural improvement already landed is that the central scaffold is now **coherent and compiling**:
  - `polyTimeComputable` is nontrivial and reduction witnesses now carry explicit size bounds.
  - `GenNPInput` now records explicit certificate-size and step metadata.
  - `validFlatTM` is no longer `True`; the machine layer now checks structural wellformedness of flattened machines.
  - `execFlatTM` / `acceptsFlatTM` now run through an actual flattened transition system instead of returning the initial configuration.
  - `FlatClique` is no longer `True`; it now expresses an actual flat clique predicate over wellformed graphs.
  - The Cook-Levin theorem file compiles again and the full theorem chain is wired together.
- Important limitation: many bridge and correctness theorems are still admitted with `sorry`, so the project is best viewed as a faithful **architecture port** rather than a finished formal proof.

## What changed in the new scaffold

The current Lean codebase is now organized so that future step-specific LLM runs can work on isolated proof obligations without silently reintroducing tautological definitions.

### Core complexity layer

- `CookLevin/Complexity/Complexity/Definitions.lean`
  - nontrivial `encodable` instances for key datatypes,
  - meaningful `fgraph_wf`,
  - meaningful `validFlatTM`,
  - nonconstant `index` via the active encoding interface.
- `CookLevin/Complexity/Complexity/MachineSemantics.lean`
  - explicit flat configuration stepping,
  - bounded machine execution,
  - acceptance tied to the reached halting state.
- `CookLevin/Complexity/Complexity/NP.lean`
  - reduction witnesses and NP witnesses still form the central API,
  - the file compiles, but some key closure theorems still need their final proofs.

### Generic NP and TM bridge

- `CookLevin/Complexity/NP/GenNP.lean`
  - `GenNPInput` now carries `maxSize`, `steps`, and certificate-size soundness.
- `CookLevin/Complexity/GenNP_is_hard.lean`
  - the intended bounded generic NP instance shape is now present,
  - but the core hardness proofs are still admitted.
- `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`
  - certificate measures now use the common encoding size interface.
- `CookLevin/Complexity/L_to_LM.lean`, `LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean`
  - the bookkeeping pipeline is wired together and compiles,
  - but the real simulation proofs are still outstanding.

### Cook-Levin subproblem chain

- `SingleTMGenNP`, `FlatTCC`, `FlatCC`, `BinaryCC`, `FSAT`, `SAT`, and `FlatClique` now all have compiling interfaces.
- Several reductions still rely on admitted proofs, and `BinaryCC → FSAT` is still using a brute-force encoding rather than the direct syntactic Coq construction.

## Implementation plan

Only the remaining work is listed below. The detailed instructions live in the step prompt files under `.github/prompts/`.

1. **Step 01** — finish the encoding / size foundation proofs
2. **Step 02** — finish the reduction closure proofs under the stronger API
3. **Step 03** — align the new flat machine semantics more closely with Coq
4. **Step 04** — finish the bounded generic NP source problem and hardness proof
5. **Step 05** — finish the `GenNP → LMGenNP` bridge proofs
6. **Step 06** — replace the remaining dummy machine bridge constructions
7. **Step 07** — finish the single-tape entry problem reduction proofs
8. **Step 08** — finish `FlatSingleTMGenNP → FlatTCC`
9. **Step 09** — finish `FlatTCC → FlatCC`
10. **Step 10** — finish `FlatCC → BinaryCC`
11. **Step 11** — replace brute-force `BinaryCC → FSAT`
12. **Step 12** — repair the SAT / clique side proofs and direct reductions
13. **Step 13** — remove the final admitted theorem links and publish final status

## How contributors should use the plan

1. Read this `README.md` first.
2. Then read exactly one step file from `.github/prompts/stepNN.md`.
3. Read every Lean and `coqdoc` file named in that step file before editing.
4. Preserve the new architecture unless your task explicitly replaces it with a more faithful Coq-style construction.
5. Keep the step mathematically honest: definitions must stay meaningful even if some proofs remain admitted.
6. Run `lake build` before finishing; the repository must stay compiling.

## Honest repository description

At the moment this repository should be described as:

> a compiling Lean architecture port of the Cook-Levin reduction chain, with meaningful core definitions and many correctly wired interfaces, but still with substantial admitted proofs and unfinished reduction arguments.
