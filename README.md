# Cook-Levin in Lean4

This repository is building a Lean4 formalization of the Cook-Levin theorem: **SAT is NP-complete**.

The target is a faithful Lean development, based on the Coq implementation from the PSL group:
- Coq source: https://github.com/uds-psl/cook-levin
- Local documentation mirror used in this repository: `coqdoc/`

The current Lean codebase is a **scaffold plus initial foundational proofs**. The scaffold mirrors the relevant Coq module hierarchy under `CookLevin/Complexity/...`, while keeping `lake build` green so the proof can be developed iteratively from the bottom up.

## Goal

The end goal is to remove every remaining `sorry` and obtain a full Lean proof of:
- `CookLevin0 : NPcomplete (kSAT 3)`
- `CookLevin : NPcomplete SAT`
- `Clique_complete : NPcomplete FlatClique`

## What is already in place

The repository already contains:
- a Lean project configured with `lake`
- a Cook-Levin scaffold that mirrors the top-level Coq reduction chain
- placeholder modules for the intermediate Cook-Levin subproblems and reductions
- a basic NP infrastructure layer in `CookLevin/Complexity/Complexity/NP.lean` with:
  - explicit NP witness relations (`polyCertRel`, `inNP`)
  - explicit forward reduction witnesses (`reducesPolyMO`)
  - reduction composition lemmas and hardness / completeness wrappers used by `CookLevin.lean`
- an abstract generic NP source layer with:
  - packaged generic NP instances in `CookLevin/Complexity/NP/GenNP.lean`
  - certificate-carrier enumeration data in `CookLevin/Complexity/CanEnumTerm.lean`
  - a real hardness proof `NPhard_GenNP` in `CookLevin/Complexity/GenNP_is_hard.lean`
- real shared SAT foundations for the bottom layer of the reduction chain:
  - assignment semantics and shared SAT datatypes in `CookLevin/Complexity/Complexity/Definitions.lean`
  - CNF satisfiability semantics, variable bookkeeping, and CNF size lemmas in `CookLevin/Complexity/NP/SAT.lean`
  - formula satisfiability semantics, variable bookkeeping, and formula size in `CookLevin/Complexity/NP/FSAT.lean`
  - `kCNF`, basic `kSAT` lemmas, and a boolean `kCNF` checker in `CookLevin/Complexity/NP/kSAT.lean`

## Review of the current scaffold

A review of the current Lean port against the relevant Coq documentation shows that the high-level reduction chain is present, but a complete proof without `sorry`s still requires substantial foundational work.

The main gaps are:

1. **Turing-machine infrastructure is still skeletal**
   - `TM`, `flatTM`, and the machine-conversion modules are still stubs.
   - This blocks the early reductions from generic NP problems to tableau-style encodings.

2. **Cook-Levin subproblems now have real intermediate languages**
   - `FlatTCC`, `FlatCC`, `BinaryCC`, and `SingleTMGenNP` now carry real Lean predicates with wellformedness conditions and canonical flattening / unflattening lemmas.
   - The remaining work is to replace the still-constant phase-6 reductions by the actual constructions from the Coq development.

3. **Major reduction implementations are still scaffolded**
   - The reductions in the Cook-Levin chain are present as theorem shells, but not yet implemented.

4. **The scaffold needs to stay buildable throughout**
   - The intended development style is not “replace everything at once”, but “fill in one bottom layer at a time while keeping `lake build` passing”.

## Bottom-up implementation plan

The plan below is designed so that each phase can be completed while preserving a clean `lake build`.

### Phase 0: project discipline

- Keep the existing scaffold structure intact.
- Replace placeholder definitions with real ones one module at a time.
- Only remove a `sorry` when all dependencies under it are already real.
- Keep theorem statements stable whenever possible, so downstream files continue to compile.

### Phase 1: shared SAT foundations

Implement and complete the basic semantics used by the whole reduction chain.

Status:
- completed for `CookLevin/Complexity/Complexity/Definitions.lean`
- completed for `CookLevin/Complexity/NP/SAT.lean`
- completed for `CookLevin/Complexity/NP/FSAT.lean`
- completed for `CookLevin/Complexity/NP/kSAT.lean`

Targets:
- assignment semantics (`evalVar`)
- CNF semantics (`evalLiteral`, `evalClause`, `evalCnf`, `SAT`)
- formula semantics (`evalFormula`, `FSAT`)
- variable-occurrence bookkeeping
- size measures for formulas and CNFs

Recommended order:
- `CookLevin/Complexity/Complexity/Definitions.lean`
- `CookLevin/Complexity/NP/SAT.lean`
- `CookLevin/Complexity/NP/FSAT.lean`
- `CookLevin/Complexity/NP/kSAT.lean`

Milestone:
- all elementary SAT / FSAT / kSAT lemmas are proven without `sorry`
- these files contain real definitions rather than placeholders

### Phase 2: basic NP infrastructure

Formalize the abstract complexity layer needed to compose reductions.

Status:
- completed for `CookLevin/Complexity/Complexity/NP.lean`
- completed for the reduction-chaining theorems consumed by `CookLevin/Complexity/NP/SAT/CookLevin.lean`
- note: this phase currently models explicit witness relations and forward reduction maps; later phases can still refine these proofs toward the full Coq development

Targets:
- `inTimePoly`
- `inNP`
- `reducesPolyMO`
- `NPhard`
- `NPcomplete`
- structural lemmas such as reflexivity, transitivity, and closure under reductions

Files:
- `CookLevin/Complexity/Complexity/NP.lean`
- related support files under `CookLevin/Complexity/Complexity/`

Milestone:
- all reduction-chaining lemmas used in `CookLevin.lean` are available without `sorry`
- the Cook-Levin composition file now uses the structural reduction lemmas instead of simplifying placeholder definitions

### Phase 3: generic NP source problems

Implement the generic NP problems and their hardness facts.

Status:
- completed for `CookLevin/Complexity/NP/GenNP.lean`
- completed for `CookLevin/Complexity/CanEnumTerm.lean`
- completed for `CookLevin/Complexity/GenNP_is_hard.lean`
- note: the current Lean abstraction models a generic NP instance as a packaged certificate relation together with a certificate-carrier interface, which is enough to prove hardness from the repository's explicit `inNP` witnesses while keeping later TM-facing phases open

Targets:
- `GenNP`
- supporting enumeration machinery
- hardness theorem(s) feeding the Cook-Levin chain

Files:
- `CookLevin/Complexity/NP/GenNP.lean`
- `CookLevin/Complexity/GenNP_is_hard.lean`
- `CookLevin/Complexity/CanEnumTerm.lean`

Milestone:
- `NPhard_GenNP` is proved against real NP infrastructure
- `CookLevin0` now consumes `NPhard_GenNP` via the phase-3 certificate enumeration layer

### Phase 4: TM and machine-model translations

Port the computational-model bridge from the Coq development.

Status:
- completed for `CookLevin/Complexity/L_to_LM.lean`
- completed for `CookLevin/Complexity/LM_to_mTM.lean`
- completed for `CookLevin/Complexity/mTM_to_singleTapeTM.lean`
- completed for `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`
- completed for `CookLevin/Complexity/NP/TM/IntermediateProblems.lean`
- note: the current Lean port now exposes explicit phase-4 problem interfaces and real bridge reductions between the generic NP source, list-machine instances, fixed multi-tape machines, and fixed single-tape machines; the concrete execution semantics and sharper runtime bounds remain abstracted by the repository's placeholder machine model and will be refined in later phases

Targets:
- list-machine and TM interfaces
- multi-tape to single-tape conversion
- fixed-machine NP problems
- time bounds required for polynomial reductions

Files:
- `CookLevin/Complexity/L_to_LM.lean`
- `CookLevin/Complexity/LM_to_mTM.lean`
- `CookLevin/Complexity/mTM_to_singleTapeTM.lean`
- `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`
- `CookLevin/Complexity/NP/TM/IntermediateProblems.lean`

Milestone:
- the first half of the Cook-Levin chain (up to single-tape / flat TM encodings) is real

### Phase 5: Cook-Levin subproblems

Implement the intermediate encodings used to move from TM computations to SAT-like objects.

Status:
- completed for `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/SingleTMGenNP.lean`
- completed for `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatTCC.lean`
- completed for `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatCC.lean`
- completed for `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/BinaryCC.lean`
- note: the current Lean port now uses explicit wellformedness predicates, canonical unflattening to `Fin`-indexed alphabets for `FlatTCC` and `FlatCC`, and real bookkeeping predicates for the single-tape source problem while the downstream reduction files still use placeholder maps that target fixed positive instances until phase 6 is implemented

Targets:
- `SingleTMGenNP`
- `FlatTCC`
- `FlatCC`
- `BinaryCC`
- their wellformedness predicates
- flattening / unflattening lemmas

Files:
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/*.lean`

Milestone:
- the intermediate languages are real, with correctness lemmas in place

### Phase 6: reduction implementations

Fill in the actual reduction proofs, bottom-up.

Recommended order:
1. `FlatTCC_to_FlatCC`
2. `FlatCC_to_BinaryCC`
3. `BinaryCC_to_FSAT`
4. `FSAT_to_SAT`
5. `FSAT_to_3SAT`
6. `kSAT_to_FlatClique`
7. `FlatSingleTMGenNP_to_FlatTCC`
8. the earlier TM-side reductions

Files:
- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/*.lean`
- `CookLevin/Complexity/NP/FSAT_to_SAT.lean`
- `CookLevin/Complexity/NP/kSAT_to_SAT.lean`
- `CookLevin/Complexity/NP/kSAT_to_FlatClique.lean`

Milestone:
- each individual reduction theorem is proved in the file where it belongs

### Phase 7: final composition theorems

Once the reductions and membership proofs are real, finish the main statements.

Targets:
- `GenNP_to_SingleTMGenNP`
- `FlatSingleTMGenNP_to_3SAT`
- `GenNP_to_3SAT`
- `CookLevin0`
- `CookLevin`
- `Clique_complete`

File:
- `CookLevin/Complexity/NP/SAT/CookLevin.lean`

Milestone:
- the main Cook-Levin theorems compile with no `sorry`

## Good starter proofs

The best first proofs are the ones with low dependency fan-out and clear Coq analogues. These are the proofs we should keep tackling first:

- SAT semantics lemmas:
  - `evalLiteral_var_iff`
  - `evalClause_literal_iff`
  - `evalClause_app`
  - `evalCnf_clause_iff`
  - `evalCnf_app_iff`
  - `size_clause_app`
  - `size_cnf_app`
- FSAT semantics lemmas:
  - `evalFormula_and_iff`
  - `evalFormula_or_iff`
  - `evalFormula_not_iff`
  - `evalFormula_prim_iff`
  - `formula_maxVar_varsIn`
  - `formula_varsIn_bound`
- kSAT structure lemmas:
  - `kCNF_clause_length`
  - `kCNF_app`

These lemmas are small, useful, and directly support later reductions.

## Current iterative development strategy

To keep the repository healthy while we port the proof:

1. pick one bottom-layer module
2. replace placeholder definitions with real ones
3. prove the local helper lemmas
4. keep downstream theorem statements compiling, even if they still end in `sorry`
5. run `lake build`
6. only then move one layer upward

That strategy lets us steadily convert the scaffold into a real development without ever breaking the build.

## Build

From the repository root:

```bash
lake build
```

A GitHub Actions workflow also runs this build automatically on pushes to `main` and on pull requests.
