# Cook-Levin in Lean4

This repository contains a Lean4 formalization of the Cook-Levin theorem in the module hierarchy `CookLevin/Complexity/...`, following the structure of the original PSL Coq development.

- Coq source: https://github.com/uds-psl/cook-levin
- Local documentation mirror: `coqdoc/`

The current Lean development builds successfully and the Lean sources in this repository contain no `sorry`.

## Main results

The final composition theorems are proved in `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/SAT/CookLevin.lean`:

- `GenNP_to_SingleTMGenNP`
- `FlatSingleTMGenNP_to_3SAT`
- `GenNP_to_3SAT`
- `CookLevin0 : NPcomplete (kSAT 3)`
- `CookLevin : NPcomplete SAT`
- `Clique_complete : NPcomplete FlatClique`

## What is formalized

The repository now includes:

- shared SAT foundations:
  - assignment semantics and common datatypes in `CookLevin/Complexity/Complexity/Definitions.lean`
  - CNF satisfiability semantics and size lemmas in `CookLevin/Complexity/NP/SAT.lean`
  - formula satisfiability semantics and size lemmas in `CookLevin/Complexity/NP/FSAT.lean`
  - `kSAT` infrastructure in `CookLevin/Complexity/NP/kSAT.lean`
- NP infrastructure:
  - explicit certificate relations and membership witnesses in `CookLevin/Complexity/Complexity/NP.lean`
  - generic NP source problems in `CookLevin/Complexity/NP/GenNP.lean`
  - generic hardness in `CookLevin/Complexity/GenNP_is_hard.lean`
  - certificate-carrier enumeration support in `CookLevin/Complexity/CanEnumTerm.lean`
- machine-model bridge:
  - the reductions from generic NP instances to the fixed single-tape TM source problem in
    - `CookLevin/Complexity/L_to_LM.lean`
    - `CookLevin/Complexity/LM_to_mTM.lean`
    - `CookLevin/Complexity/mTM_to_singleTapeTM.lean`
    - `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`
    - `CookLevin/Complexity/NP/TM/IntermediateProblems.lean`
- Cook-Levin intermediate languages:
  - `SingleTMGenNP`, `FlatTCC`, `FlatCC`, and `BinaryCC`
  - their wellformedness predicates and flattening / unflattening lemmas under `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/`
- reduction chain to satisfiability and clique:
  - reductions under `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/`
  - `FSAT_to_SAT` in `CookLevin/Complexity/NP/FSAT_to_SAT.lean`
  - `kSAT_to_SAT` in `CookLevin/Complexity/NP/kSAT_to_SAT.lean`
  - `kSAT_to_FlatClique` in `CookLevin/Complexity/NP/kSAT_to_FlatClique.lean`

## Resulting theorem chain

At the top level, the development proves:

1. hardness of the generic NP source problem
2. reductions from generic NP instances to fixed single-tape TM instances
3. tableau-style reductions through the Cook-Levin intermediate languages
4. reduction to `kSAT 3`
5. NP-completeness of `kSAT 3`
6. NP-completeness of `SAT`
7. NP-completeness of `FlatClique`

## Build

From the repository root:

```bash
lake build
```

GitHub Actions also runs this build automatically on pushes to `main` and on pull requests.
