# Cook-Levin in Lean4

This repository currently **builds successfully**, and the Lean sources currently contain **no `sorry`**. However, the current development does **not** yet constitute a mathematically faithful formal proof of the Cook-Levin theorem.

The repository presently contains a **compiling scaffold** with the expected theorem names and reduction chain, but several foundational definitions are placeholders that make the current NP-completeness statements too weak to support the intended theorem.

- Coq source: https://github.com/uds-psl/cook-levin
- Local Coq documentation mirror: `coqdoc/`

## Current status at a glance

What is true today:

- `lake build` succeeds.
- The top-level theorem names exist in `CookLevin/Complexity/NP/SAT/CookLevin.lean`:
  - `GenNP_to_SingleTMGenNP`
  - `FlatSingleTMGenNP_to_3SAT`
  - `GenNP_to_3SAT`
  - `CookLevin0 : NPcomplete (kSAT 3)`
  - `CookLevin : NPcomplete SAT`
  - `Clique_complete : NPcomplete FlatClique`
- The repository has substantial SAT / CNF / tableau infrastructure and a recognizable high-level reduction pipeline.

What is **not** true today:

- The current Lean development does **not** yet faithfully model polynomial-time computation.
- The current Lean development does **not** yet faithfully model polynomial-time many–one reductions.
- The current Lean development does **not** yet faithfully model the Turing machines used in the Cook-Levin argument.
- Therefore, the current theorem named `CookLevin` should be understood as a theorem in the repository's **placeholder complexity framework**, not yet as the intended mathematical Cook-Levin theorem.

## Why the current proof is not yet faithful

The issues below are visible directly in the current Lean sources.

### 1. Polynomial-time definitions are placeholders

In `CookLevin/Complexity/Complexity/Definitions.lean`:

- `monotonic (_ : Nat → Nat) : Prop := True`
- `inOPoly (_ : Nat → Nat) : Prop := True`
- `computableTime' ... : Prop := True`

In `CookLevin/Complexity/Complexity/NP.lean`:

- `inTimePoly P := ∃ f, inOPoly f ∧ monotonic f`
- `inTimePoly_linear` proves `inTimePoly P` for **every** predicate `P`

Consequence: the current development does not enforce any real polynomial-time bound.

### 2. Reductions do not require polynomial-time computability

In `CookLevin/Complexity/Complexity/NP.lean`, `ReductionWitness` currently contains only:

- a function `reduction : X → Y`
- a one-way correctness proof `P x → Q (reduction x)`

Missing today:

- polynomial-time computability of the reduction
- the usual equivalence-style correctness `P x ↔ Q (f x)` used in the Coq development

Consequence: exponential or non-computable maps can currently count as "`⪯p`" reductions.

### 3. The machine model is a stub

In `CookLevin/Complexity/Complexity/Definitions.lean`:

- `abbrev flatTM := Unit`
- `abbrev TM (_σ : Type) (_ : Nat) := Unit`

Consequence: the current development cannot express actual machine behavior or machine running time.

### 4. Size bookkeeping is currently trivialized

In `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`:

- `certificateMeasure` is always `0`

In `CookLevin/Complexity/L_to_LM.lean`:

- `maxSize := 0`
- `steps := 0`

Consequence: certificate-size and runtime bounds are not yet connected to actual encodings or executions.

### 5. Several bridge problems forget the machine semantics

Examples:

- `LM_to_mTM.lean` packages `accepts := inst.source.rel`
- `mTM_to_singleTapeTM.lean` preserves the same `accepts` field
- `M.M` and `M_multi2mono.M__mono` manufacture placeholder machines

Consequence: the current bridge from generic NP instances to fixed Turing-machine instances does not yet prove that a real machine simulates the intended verifier within polynomial time.

### 6. Some reductions use brute-force search

In `CookLevin/Complexity/NP/FSAT_to_SAT.lean`:

- `FSAT_search` enumerates all assignments
- `FSAT_to_SAT_reduction` returns a trivial satisfiable or unsatisfiable CNF depending on that search

In `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/BinaryCC_to_FSAT.lean`:

- `allBitStrings` enumerates all bitstrings
- `acceptingRunsFrom` enumerates traces
- `BinaryCC_to_FSAT_instance` builds a disjunction over enumerated accepting traces

Consequence: these are not polynomial-time reductions in the intended sense.

### 7. The current `GenNP` hardness layer is still scaffolded

The repository no longer uses the earlier trivial `NPUniversal` in the final hardness definition, which is good. However, the current `GenNP` layer still relies on the placeholder complexity framework above, for example:

- `GenNPInput.rel_poly` depends on the current trivial `inTimePoly`
- `genNPInstance` in `CookLevin/Complexity/GenNP_is_hard.lean` fills `rel_poly` with `inTimePoly_linear _`

Consequence: the current hardness result is structurally useful, but not yet mathematically sufficient.

## What is already worth keeping

The repository is not empty work. The following parts look like useful scaffolding for a faithful port:

- SAT / FSAT / kSAT syntax and evaluation infrastructure
- the overall reduction-chain decomposition
- many flattening / unflattening lemmas for tableau encodings
- a useful local mirror of the Coq reference proof in `coqdoc/`

These should be treated as assets to preserve where possible while the placeholder complexity layer is replaced.

## Reference Coq files to follow closely

Future work should align Lean definitions and theorem statements with the Coq reference, especially:

- `coqdoc/Complexity.Complexity.PolyTimeComputable.txt`
- `coqdoc/Complexity.Complexity.NP.txt`
- `coqdoc/Complexity.NP.TM.TMGenNP.txt`
- `coqdoc/Complexity.NP.SAT.FSAT.FSAT_to_SAT.txt`
- `coqdoc/Complexity.NP.SAT.CookLevin.txt`

## Implementation plan

Use the steps below **in order**. Each step is intended to be concrete enough to hand to a separate LLM session as a prompt. Do not skip steps: later steps depend on earlier ones.

For every step below, the agent working on it should:

1. modify only the files needed for that step,
2. update this README if the repository status materially changes,
3. run `lake build`,
4. state clearly which placeholder has been removed and which theorem(s) became faithful as a result.

### Step 1 — Replace the placeholder complexity foundations

**Goal:** remove the `True`-based definitions that trivialize complexity theory.

**Primary files:**

- `CookLevin/Complexity/Complexity/Definitions.lean`
- new Lean files matching the Coq complexity infrastructure as needed

**Required outcomes:**

- replace the placeholder `encodable` scaffold with a meaningful encoding/size setup compatible with the rest of the development,
- define nontrivial versions of `monotonic`, `inOPoly`, and the base time/size notions needed downstream,
- introduce or port the supporting lemmas that the Coq proof uses for polynomial bounds and composition,
- remove any theorem whose only proof was `trivial` because of placeholder definitions.

**Done when:**

- `inTimePoly_linear` no longer proves `inTimePoly P` for arbitrary predicates without an actual decider,
- the new complexity lemmas resemble the Coq interfaces closely enough that later ports can follow them directly.

### Step 2 — Rebuild `inTimePoly`, `inNP`, and polynomial certificate relations

**Goal:** make NP membership mean what it should mean mathematically.

**Primary files:**

- `CookLevin/Complexity/Complexity/NP.lean`
- `CookLevin/Complexity/NP/GenNP.lean`

**Required outcomes:**

- redefine `inTimePoly` to require an actual decider/verifier with a polynomial time bound,
- redefine the certificate relation layer so witness size is polynomially bounded in the encoded input size,
- port the corresponding Coq structure of `polyCertRel`, `inNP`, `inP`, and `P_NP_incl`,
- update all immediate downstream uses to the new interfaces.

**Done when:**

- `inNP P` cannot be proved without a concrete bounded verifier,
- certificate size bounds are explicit and used by the API.

### Step 3 — Redefine polynomial-time many-one reduction

**Goal:** make `⪯p` match the Coq notion of polynomial-time many–one reducibility.

**Primary files:**

- `CookLevin/Complexity/Complexity/NP.lean`

**Required outcomes:**

- strengthen `ReductionWitness` / `reducesPolyMO` so a reduction includes:
  - a function,
  - a polynomial-time computability proof for that function,
  - the intended correctness statement (`↔`, not just the forward direction),
- port or re-prove reflexivity, transitivity, and `red_inNP` using the stronger notion.

**Done when:**

- a brute-force map can no longer be accepted as a polynomial-time reduction,
- composition of reductions carries composed runtime bounds.

### Step 4 — Introduce a meaningful Turing-machine layer

**Goal:** replace `TM := Unit` and `flatTM := Unit` with real computational objects.

**Primary files:**

- `CookLevin/Complexity/Complexity/Definitions.lean`
- machine-specific files mirroring the Coq development

**Required outcomes:**

- port or reconstruct the relevant TM datatypes and encodings,
- define machine execution and the time-bounded computation predicates used by the NP source problems,
- connect machine encodings to the complexity layer from Steps 1–3.

**Done when:**

- Lean can state and prove facts about the runtime of concrete machines,
- `computableTime'` is no longer `True`.

### Step 5 — Rebuild the generic NP source problem faithfully

**Goal:** make the starting NP-hard problem mathematically correct.

**Primary files:**

- `CookLevin/Complexity/NP/GenNP.lean`
- `CookLevin/Complexity/GenNP_is_hard.lean`
- `CookLevin/Complexity/CanEnumTerm.lean`

**Required outcomes:**

- ensure the generic source problem uses the new nontrivial verifier notion,
- carry actual certificate-size and encoding information through `GenNPInput`,
- re-prove `NPhard_GenNP` against the strengthened `inNP` and `⪯p`.

**Done when:**

- the hardness proof no longer relies on `inTimePoly_linear _`,
- the source problem can serve as a mathematically valid starting point for the reduction chain.

### Step 6 — Repair the bridge from generic NP to fixed machine problems

**Goal:** make the `GenNP → LM → mTM → single-tape TM` pipeline encode real verifier computations.

**Primary files:**

- `CookLevin/Complexity/TMGenNP_fixed_mTM.lean`
- `CookLevin/Complexity/L_to_LM.lean`
- `CookLevin/Complexity/LM_to_mTM.lean`
- `CookLevin/Complexity/mTM_to_singleTapeTM.lean`
- `CookLevin/Complexity/NP/TM/IntermediateProblems.lean`

**Required outcomes:**

- eliminate `certificateMeasure := 0`,
- eliminate the dummy machine constants,
- make `maxSize` and `steps` represent actual bounds,
- prove that each bridge reduction is polynomial-time and semantically correct with the strengthened reduction notion.

**Done when:**

- the fixed-machine instances encode genuine bounded machine acceptance problems,
- each bridge theorem states and proves a real polynomial-time reduction.

### Step 7 — Audit and repair the Cook-Levin intermediate languages

**Goal:** keep the useful tableau encodings, but make their interfaces depend on real machine semantics and real bounds.

**Primary files:**

- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/SingleTMGenNP.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatTCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatCC.lean`
- `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/BinaryCC.lean`

**Required outcomes:**

- verify that every wellformedness predicate and encoding lemma still matches the new machine layer,
- add any missing size bounds required to prove later reductions polynomial,
- remove any assumptions that only held because the machine model was trivial.

**Done when:**

- each intermediate language has a clear mathematical meaning tied to actual computations,
- the downstream reductions can cite explicit size and runtime bounds.

### Step 8 — Replace `BinaryCC_to_FSAT` brute-force trace enumeration

**Goal:** generate a formula that directly encodes accepting traces, instead of searching for them.

**Primary files:**

- `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/BinaryCC_to_FSAT.lean`
- corresponding Coq reference files under `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.*`

**Required outcomes:**

- remove `allBitStrings`, `acceptingRunsFrom`, and the disjunction-over-traces construction from the reduction,
- build the FSAT instance directly from the tableau constraints,
- prove both semantic correctness and polynomial-time computability of the construction.

**Done when:**

- the reduction constructs the target formula without enumerating candidate runs,
- the proof uses explicit size bounds rather than existential placeholders.

### Step 9 — Replace `FSAT_to_SAT` and `FSAT_to_3SAT` with Tseitin-style reductions

**Goal:** eliminate assignment search from the satisfiability reductions.

**Primary files:**

- `CookLevin/Complexity/NP/FSAT_to_SAT.lean`
- `coqdoc/Complexity.NP.SAT.FSAT.FSAT_to_SAT.txt`

**Required outcomes:**

- port the Tseitin transformation (including any preprocessing such as OR elimination if that remains the cleanest route),
- prove correctness of the generated clauses,
- prove polynomial size growth and polynomial-time computability,
- derive `FSAT ⪯p SAT` and `FSAT ⪯p kSAT 3` from the actual transformation.

**Done when:**

- `FSAT_search` is gone from the reduction,
- the reduction output depends only on syntactic transformation of the input formula.

### Step 10 — Re-audit every remaining reduction for the strengthened notion of `⪯p`

**Goal:** ensure no theorem survives merely because the old reduction notion was too weak.

**Primary files:**

- all reduction files under `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/`
- `CookLevin/Complexity/NP/kSAT_to_SAT.lean`
- `CookLevin/Complexity/NP/kSAT_to_FlatClique.lean`
- any other file proving `⪯p`

**Required outcomes:**

- revisit each reduction proof under the new reduction definition,
- add missing computability proofs,
- strengthen correctness statements to the required equivalence,
- remove or rewrite any reduction that still depends on search or placeholder machinery.

**Done when:**

- every theorem of the form `P ⪯p Q` exhibits a real polynomial-time computable map.

### Step 11 — Re-prove NP-membership results using the repaired verifier framework

**Goal:** ensure the "in NP" side of each completeness theorem is also faithful.

**Primary files:**

- `CookLevin/Complexity/NP/SAT.lean`
- `CookLevin/Complexity/NP/FSAT.lean`
- `CookLevin/Complexity/NP/kSAT.lean`
- `CookLevin/Complexity/NP/FlatClique.lean`
- any dedicated `*_inNP` files

**Required outcomes:**

- update each NP-membership theorem to provide actual certificate relations and real verifier bounds,
- ensure the certificate size bounds are polynomial in the input size,
- remove any uses that only worked because `inTimePoly` was trivial.

**Done when:**

- `SAT`, `kSAT 3`, and `FlatClique` are all in NP for genuine mathematical reasons.

### Step 12 — Recompose the final theorem chain only after all upstream notions are repaired

**Goal:** restore `CookLevin` as a faithful theorem, not merely a compiled name.

**Primary files:**

- `CookLevin/Complexity/NP/SAT/CookLevin.lean`

**Required outcomes:**

- rebuild the composition proofs using the repaired hardness, NP-membership, and reduction theorems,
- ensure the final statements depend only on non-placeholder infrastructure,
- confirm that the final argument matches the Coq proof architecture closely.

**Done when:**

- `CookLevin0`, `CookLevin`, and `Clique_complete` are theorems in the intended mathematical sense.

### Step 13 — Add a permanent status and audit section to the repository

**Goal:** prevent the repository from again claiming more than it currently proves.

**Primary files:**

- `README.md`
- optionally a dedicated status file if later desired

**Required outcomes:**

- keep an explicit checklist of which placeholder components remain, if any,
- record which major steps above are complete,
- document any intentionally deferred parts of the Coq port.

**Done when:**

- a new contributor can tell immediately whether the repository contains a faithful Cook-Levin proof or only a partial port.

## Short prompt templates for future LLM sessions

Use one of these per step, after replacing the step number.

> Review `README.md`, then complete **Step N** of the implementation plan. Follow the referenced Lean files and the matching `coqdoc/` files closely, keep the change mathematically faithful, update the `Current status at a glance` section and mark Step N as complete in the plan, and validate with `lake build`.

> Complete **Step N** from `README.md` only. Do not skip prerequisites. Port the corresponding Coq definitions and proofs as closely as practical, remove placeholder complexity machinery touched by this step, update the `Current status at a glance` section and mark Step N as complete in the plan, and run `lake build`.

## Minimum acceptance standard for claiming success

This repository should only claim to prove Cook-Levin once all of the following are true:

- polynomial-time computation is modeled nontrivially,
- polynomial-time reduction includes actual polynomial-time computability,
- the machine layer has real semantics,
- the generic NP source problem is faithful,
- the reduction chain avoids brute-force search,
- the final NP-completeness theorems are rebuilt from the repaired foundations.

Until then, the honest description of the repository is:

> a promising Lean scaffold for a Cook-Levin formalization, with substantial SAT and tableau infrastructure, but not yet a faithful proof of the theorem.
