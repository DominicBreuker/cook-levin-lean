# Cook–Levin in Lean 4 — Project Status

This directory contains a Lean 4 attempt at a fully formal proof of the
**Cook–Levin theorem** (SAT is NP-complete), structured as a port of the
existing Coq development by Forster, Kunze, Roth et al.

> **Honest status, May 2026.** A file named
> `Complexity/NP/SAT/CookLevin.lean` declares
> `theorem CookLevin : NPcomplete SAT` and Lean accepts it. **This term
> is still *not* a fully faithful proof of Cook–Levin** — but Part 1
> and the framework portion of Part 2 of [`ROADMAP.md`](ROADMAP.md)
> are now landed (see [`PART2.md`](PART2.md) for details). After Part
> 2's framework migration the codebase has **exactly four labelled
> `sorry`s**:
>
> 1. `EvalCnfTM.decider` (`Complexity/Complexity/Deciders/EvalCnfTM.lean`)
>    — `TODO(Part2-followup:EvalCnfTM)`: the SAT verifier TM
>    construction, deferred to Step 11 of PART2.md v2.
> 2. `CliqueRelTM.decider` (`Complexity/Complexity/Deciders/CliqueRelTM.lean`)
>    — `TODO(Part2-followup:CliqueRelTM)`: the FlatClique verifier TM
>    construction, deferred to Step 12 of PART2.md v2.
> 3. `red_inNP` TM composition (`Complexity/Complexity/NP.lean`)
>    — `TODO(Part3:red_inNP_TMcompose)`: needs Part 3's TM-backed
>    `polyTimeComputable` to run the reduction TM and then the
>    verifier TM.
> 4. `hasDeciderClassical` (`Complexity/GenNP_is_hard.lean`)
>    — `TODO(Part6:hasDeciderClassical)`: the placeholder that made
>    `NPhard_GenNP` vacuous; Part 6 rebuilds `NPhard_GenNP` to draw a
>    real verifier TM from the source `inNP` hypothesis.
>
> `inTimePoly` is now TM-backed: it requires a `Nonempty (DecidesBy P f)`
> witness, where `DecidesBy` carries a concrete `FlatTM`, validity
> proof, accept/reject halting states, and step-bound run lemmas. The
> previous propositional `HasDecider` predicate has been removed.
> `sat_NP` and `FlatClique_in_NP` build against this new framework.
> A precise list of what is sound and what is not is at the bottom of
> this README, and a step-by-step path to a faithful proof is in
> [`ROADMAP.md`](ROADMAP.md) and [`PART2.md`](PART2.md).

---

## What is in the repository

The project lives entirely under `/workspace/CookLevin/`. The build is
driven by the root `lakefile.lean`, which depends on `mathlib4`.

```
CookLevin/
├── Basic.lean               -- placeholder
├── Main.lean                -- "Hello, World!" executable entry point
├── Complexity.lean          -- top-level import aggregator
└── Complexity/
    ├── Complexity/
    │   ├── Definitions.lean       -- encodable instances, formulas, CC/TCC
    │   │                              structures, `inOPoly`, helper lemmas
    │   ├── MachineSemantics.lean  -- `FlatTM` model, `stepFlatTM`, `runFlatTM`,
    │   │                              `acceptsFlatTM`, `computableTime'`
    │   ├── NP.lean                -- `polyTimeComputable`, `inTimePoly`,
    │   │                              `inNP`, `⪯p`, `NPhard`, `NPcomplete`
    │   └── Subtypes.lean          -- empty stub
    ├── CanEnumTerm.lean           -- size-only certificate encoder
    ├── GenNP_is_hard.lean         -- generic NP-hardness of `GenNP`
    ├── L_to_LM.lean               -- GenNP ⪯ LMGenNP "bridge"
    ├── LM_to_mTM.lean             -- LMGenNP ⪯ mTM-acceptance "bridge"
    ├── mTM_to_singleTapeTM.lean   -- mTM ⪯ 1-tape TM "bridge"
    ├── TMGenNP_fixed_mTM.lean     -- problem skeletons for the TM layer
    └── NP/
        ├── GenNP.lean             -- the universal NP-source problem
        ├── SAT.lean               -- CNF SAT and `inNP SAT` (with one sorry)
        ├── kSAT.lean              -- k-CNF SAT
        ├── FSAT.lean              -- Boolean-formula SAT
        ├── FlatClique.lean        -- k-clique on flat graphs
        ├── FSAT_to_SAT.lean       -- Tseytin transform (one sorry)
        ├── kSAT_to_SAT.lean       -- trivial subtype reduction
        ├── kSAT_to_FlatClique.lean -- classical Karp construction (two sorrys)
        ├── TM/
        │   └── IntermediateProblems.lean -- chains the three TM "bridges"
        └── SAT/
            └── CookLevin.lean     -- final theorem statements
            └── CookLevin/
                ├── FlatSingleTMGenNP_to_FlatTCC.lean -- import wrapper
                ├── FlatTCC_to_FlatCC.lean            -- import wrapper
                ├── FlatCC_to_BinaryCC.lean           -- import wrapper
                ├── BinaryCC_to_FSAT.lean             -- import wrapper
                ├── Reductions/
                │   ├── FlatSingleTMGenNP_to_FlatTCC.lean
                │   ├── FlatTCC_to_FlatCC.lean
                │   ├── FlatCC_to_BinaryCC.lean
                │   ├── BinaryCC_to_FSAT.lean
                │   └── TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean
                └── Subproblems/
                    ├── SingleTMGenNP.lean
                    ├── FlatTCC.lean
                    ├── FlatCC.lean
                    └── BinaryCC.lean
```

Total: ~5800 lines of Lean.

## High-level architecture

The intended proof follows the standard Cook–Levin recipe and exactly
mirrors the Coq port. The chain of reductions used by the final theorem
is:

```
GenNP (List Bool)                       -- universal NP-source language
    ⪯p   LMGenNP (List Bool)            -- L_to_LM.lean
    ⪯p   LMtoMTMTarget                  -- LM_to_mTM.lean
    ⪯p   IntermediateTMTarget           -- mTM_to_singleTapeTM.lean
    ⪯p   FlatSingleTMGenNP              -- noncomputable wrapper
    ⪯p   FlatTCC                        -- tableau encoding of a TM run
    ⪯p   FlatCC                         -- generic covering-card system
    ⪯p   BinaryCC                       -- {0,1} alphabet
    ⪯p   FSAT                           -- Boolean-formula SAT
    ⪯p   SAT, kSAT 3                    -- CNF / 3-CNF SAT
    ⪯p   FlatClique                     -- (also derived from kSAT 3)
```

`NPhardness` is then transported from `GenNP` along this chain via
`red_NPhard`, yielding `CookLevin0 : NPcomplete (kSAT 3)`,
`CookLevin : NPcomplete SAT`, and `Clique_complete : NPcomplete FlatClique`
in `CookLevin.lean`.

### What backs each layer

| Layer                                      | Type of object                          | Status |
|--------------------------------------------|------------------------------------------|--------|
| `encodable`                                | unary size measure                       | sound  |
| `inOPoly`, `monotonic`, `inO`              | asymptotic-growth predicates             | sound  |
| `FlatTM` + `stepFlatTM` + `runFlatTM`      | concrete TM semantics                    | sound  |
| `validFlatTM_default`                      | 1-state, 0-transition halting machine    | placeholder |
| `polyTimeComputable f`                     | exists size-bound on `f`                 | **not** runtime-bounded (Part 3) |
| `DecidesBy P f` + `inTimePoly P` (Part 2)  | actual `FlatTM` + halting / time-budget proofs | TM-backed; stubs for `EvalCnfTM.decider` / `CliqueRelTM.decider` |
| `HasDecider X P f`                         | *removed in Part 2 Step 9*               | n/a |
| `bridgeMachine` (LM→mTM, mTM→1-tape)       | empty TM that halts at step 0            | placeholder |
| `TMGenNP_fixed M`, `mTMGenNP_fixed M`      | predicates that ignore `M`               | placeholder |
| `TMGenNP_fixed → FlatFunSingleTMGenNP`     | `if source then yes_inst else no_inst`   | classical, not computable |
| `FlatSingleTMGenNP → FlatTCC`              | `if source then trivial-yes else no-inst`| classical, not computable |
| `FlatTCC → FlatCC`                         | structural encoding, equivalence proved  | **sound** |
| `FlatCC → BinaryCC`                        | unary block encoding, equivalence proved | **sound** |
| `BinaryCC → FSAT`                          | tableau formula, equivalence proved      | **sound** |
| `FSAT → SAT / 3SAT` (Tseytin)              | correct map, size bound has `sorry`      | sound modulo 1 sorry |
| `kSAT → SAT`                               | inclusion reduction                      | sound  |
| `kSAT → FlatClique`                        | classical Karp construction, no proofs   | two sorrys |
| `SAT inNP`, `FlatClique inNP`              | TM-backed via `EvalCnfTM` / `CliqueRelTM` | sound modulo TM-construction stubs |
| `NPhard_GenNP` (`hasDeciderClassical`)     | retyped to `Nonempty (DecidesBy …)`, body is the Part-6 sorry | placeholder waiting on Part 6 |

### Where the project is mathematically sound

The following parts are real, computable, fully-proved Lean and contain
the most substantial work in the repository:

- **`Complexity/Complexity/MachineSemantics.lean`** — the `FlatTM` model
  itself (tapes, transitions, single-step semantics, run with step-budget).
- **`Complexity/Complexity/Definitions.lean`** — `encodable`,
  `monotonic`, `inO`, `inOPoly`, and the polynomial-composition lemmas
  `inOPoly_add`, `inOPoly_comp` with their honest analytic proofs.
- **`Complexity/Complexity/NP.lean`** — definitions and the standard
  reasoning lemmas `reducesPolyMO_reflexive`, `reducesPolyMO_transitive`,
  `red_inNP`, `red_NPhard`. These are sound given the (currently weak)
  definitions they sit on top of.
- **`Complexity/NP/SAT.lean`** — the SAT language, its evaluator, and all
  the supporting lemmas. One `sorry` in `compressAssignment_size_bound`.
- **`Complexity/NP/kSAT.lean`** and **`kSAT_to_SAT.lean`** — clean.
- **`Complexity/NP/FSAT.lean`** — clean.
- **`Complexity/NP/FSAT_to_SAT.lean`** — a genuine Tseytin transformation
  (~700 lines). Correctness is fully proved; only the polynomial
  size bound at line 706 is a `sorry`.
- **The combinatorial core, lines and proofs ~3000 LOC:**
  - `FlatTCC_to_FlatCC` (window/cover equivalence both directions, real
    size bound `5n+5`)
  - `FlatCC_to_BinaryCC` (unary block encoding, real size bound
    `50n² + 50n + 1`)
  - `BinaryCC_to_FSAT` (tableau CNF, equivalence proved both directions,
    size bound `500n⁶ + 500`)
- The `validFlattening`/`flattenString`/`unflattenList` machinery
  connecting `Fin k`-typed and `Nat`-flattened representations.

This is roughly half the lines of the repository, and it is the actually
meaningful mathematics that has been ported. The proof of Cook–Levin
*after* a TM run has been encoded as a `FlatTCC` instance is essentially
in place.

### Where the project is mathematically not sound

The current `theorem CookLevin : NPcomplete SAT` fails to be a real
proof of Cook–Levin for two distinct reasons, both of which need to be
fixed before this development can be honestly described as a Cook–Levin
formalisation:

1. **The complexity framework is too weak.** The definitions in
   `Complexity/Complexity/NP.lean` are:
   - `polyTimeComputable f` requires only that `encodable.size (f x) ≤
     bound (encodable.size x)` — i.e. that *the output* is polynomially
     bounded. Nothing in the definition refers to a Turing machine that
     computes `f` or to the number of steps such a machine takes. So
     `polyTimeComputable` does not actually express
     "polynomial-time computable".
   - `HasDecider X P f` is `∃ dec : X → Bool, ∀ x, P x ↔ dec x = true`.
     The time bound `f` is a phantom argument — the decider need not run
     in time `f`, need not run at all, need not even be computable.
   - `inTimePoly P` bundles a `HasDecider` together with a polynomial
     bound, but inherits the same weakness. Thus `inTimePoly` does not
     mean "P ∈ P".
   - `GenNP_is_hard.lean` exploits this: `hasDeciderClassical` builds an
     `X → Bool` decider for *any* `P` using `Classical.choice` and
     ignores the time bound. This is the function that makes
     `NPhard_GenNP` typecheck.

2. **The TM bridge layers are dummies.** Three "reductions" between
   Turing-machine-flavoured problems do not actually simulate Turing
   machines:
   - `LM_to_mTM.lean` defines a `bridgeMachine : TM Bool 2` whose
     transition table is empty (`trans := []`) and whose unique start
     state is already halting. The "acceptance" lemma
     `bridgeMachine_accepts` is therefore trivially true at step 0 for
     any input and any step budget.
   - `mTM_to_singleTapeTM.lean` follows the same recipe with a 1-tape,
     1-state, 0-transition machine; the multi-tape machine `M` is fed
     into the construction but completely discarded by
     `M__mono`/`projT1`.
   - The reduction
     `TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP`
     (`Reductions/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean`)
     is `noncomputable def f inst := if TMGenNP_fixed M inst then
     yesInstance else noInstance` — it case-splits on the source
     language itself, so the map is not computable. The polynomial-time
     "bound" `fun _ => size noInstance + 1` is a constant.
   - The reduction `FlatSingleTMGenNP → FlatTCC` is again
     `noncomputable` and dispatches on the answer; the "yes" tableau is
     the all-zero word with the trivial `0,0,0 → 0,0,0` card.

   So the **only conjunct of "yes-instance" that survives** through the
   bridge layers is `inst.rel cert` or `inst.accepts cert`, and the
   TM-acceptance conjuncts are dead weight. No TM is actually being
   simulated anywhere on the path to `FlatTCC`.

### Outstanding `sorry`s (verbatim list, post-Part-2 framework migration)

After Part 2 Step 10 the codebase has exactly four labelled `sorry`s,
each pointing at the roadmap step that will close it. The five
auxiliary `sorry`s listed in earlier revisions of this README were
discharged in Part 1.

```
Complexity/Complexity/NP.lean:270                  red_inNP (TM-composition slot)
                                                   -- TODO(Part3:red_inNP_TMcompose)
Complexity/Complexity/Deciders/EvalCnfTM.lean:58   EvalCnfTM.decider
                                                   -- TODO(Part2-followup:EvalCnfTM)
Complexity/Complexity/Deciders/CliqueRelTM.lean:66 CliqueRelTM.decider
                                                   -- TODO(Part2-followup:CliqueRelTM)
Complexity/GenNP_is_hard.lean:23                   hasDeciderClassical
                                                   -- TODO(Part6:hasDeciderClassical)
```

### Other smells

- `instEncodableDefault` (`Definitions.lean:14`) silently gives `size =
  0` to any type that lacks an explicit `encodable` instance, so a bound
  of `fun _ => 0` is "satisfiable" for `GenNPInput`, `LMGenNP.Instance`,
  `mTMGenNPFixedInput`, `TMGenNPFixedInput`. This loophole is the only
  reason several bridge-stage `polyTimeComputable` proofs typecheck.
- `abbrev TM (_σ : Type) (_ : Nat) := FlatTM` (`Definitions.lean:61`):
  the alphabet type and tape count are phantom parameters that do not
  constrain anything about a TM's data.
- `Complexity/Complexity/Subtypes.lean` is empty.
- `Basic.lean`/`Main.lean` are scaffolding from the Lake template.
- "Legacy constructions" block at the bottom of
  `Complexity/NP/FSAT_to_SAT.lean` (lines 726–754) introduces unused
  `FSAT_to_SAT_yes/no`, `FSAT_to_3SAT_yes/no`, `FSAT_search`. These were
  a previous fake reduction and are no longer on the proof path.
- `computableTime'` (`MachineSemantics.lean:186-194`) is the previous
  placeholder used by the Coq port via the L calculus; in its current
  form it collapses to "∃ steps, ∀ y, f y ≤ steps", which is unrelated
  to its name.
- `CanEnumTerm` for `List Bool` (`CanEnumTerm.lean`) encodes `y` as
  `[true] ++ replicate (size y) false` — this is a size-only encoding,
  not an injection, which is acceptable only because the surrounding
  framework never consults the certificate content.

## Building

`mathlib` is the only declared dependency. From the repository root:

```
lake build
```

(Note: the project assumes a pre-existing `mathlib` cache; from a clean
checkout the first build can take a long time.)

## Where to look first

If you want to see the **real, working** mathematics, read in order:

1. `Complexity/Complexity/Definitions.lean` — encodings, polynomials.
2. `Complexity/NP/SAT/CookLevin/Subproblems/FlatTCC.lean` — covering
   semantics.
3. `Complexity/NP/SAT/CookLevin/Reductions/FlatTCC_to_FlatCC.lean`.
4. `Complexity/NP/SAT/CookLevin/Reductions/FlatCC_to_BinaryCC.lean`.
5. `Complexity/NP/SAT/CookLevin/Reductions/BinaryCC_to_FSAT.lean`.
6. `Complexity/NP/FSAT_to_SAT.lean` — Tseytin transformation.

If you want to see **what still needs to be replaced**, read:

1. `Complexity/Complexity/NP.lean` — the weak `polyTimeComputable` /
   `HasDecider` / `inTimePoly` definitions.
2. `Complexity/GenNP_is_hard.lean` — the `hasDeciderClassical` shortcut.
3. `Complexity/LM_to_mTM.lean`, `Complexity/mTM_to_singleTapeTM.lean` —
   the dummy bridge machines.
4. `Complexity/NP/SAT/CookLevin/Reductions/`
   `TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean`,
   `FlatSingleTMGenNP_to_FlatTCC.lean` — the classical case-split
   reductions.

The roadmap to the real proof is in [`ROADMAP.md`](ROADMAP.md).
