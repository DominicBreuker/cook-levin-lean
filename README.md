# Cook–Levin in Lean 4

A Lean 4 formalisation effort targeting the **Cook–Levin theorem**:
SAT is NP-complete. The project is structured as a port of the
existing Coq development by Forster, Kunze, Roth et al.
(https://github.com/uds-psl/cook-levin, mirrored locally under
`coqdoc/`).

**This is a work in progress.** A file named
`CookLevin/Complexity/NP/SAT/CookLevin.lean` declares
`theorem CookLevin : NPcomplete SAT` and Lean accepts it, but the
term is not yet a faithful proof of Cook–Levin. The codebase
captures the combinatorial heart of the proof rigorously, plus a
strengthened complexity framework, but still has four labelled
`sorry`s and a documented strategic pivot in progress. See
[`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md) for the full plan
and current state.

## Status at a glance (May 2026)

- `lake build` succeeds.
- Repository size: **~11K LOC** of Lean on the proof path under
  `CookLevin/` (a further ~14K LOC of paused / superseded work
  lives under [`parked/`](parked/), not built).
- **Four labelled `sorry`s remain**, all flagged with `TODO(...)`
  tags pointing at the roadmap phase that closes them:

  | # | Location                                                              | Tag                                  | Closes at |
  |---|-----------------------------------------------------------------------|--------------------------------------|-----------|
  | 1 | `CookLevin/Complexity/Complexity/Deciders/EvalCnfTM.lean:58`          | `TODO(Part2-followup:EvalCnfTM)`     | New Part 3 of ROADMAP |
  | 2 | `CookLevin/Complexity/Complexity/Deciders/CliqueRelTM.lean:66`        | `TODO(Part2-followup:CliqueRelTM)`   | New Part 3 of ROADMAP |
  | 3 | `CookLevin/Complexity/Complexity/NP.lean:270`                         | `TODO(Part3:red_inNP_TMcompose)`     | New Part 4 of ROADMAP |
  | 4 | `CookLevin/Complexity/GenNP_is_hard.lean:23`                          | `TODO(Part6:hasDeciderClassical)`    | New Part 7 of ROADMAP |

- The build is **conditionally complete**: `theorem CookLevin :
  NPcomplete SAT` typechecks, but it depends on the four sorrys above
  and on a handful of placeholder TM-bridge constructions (see "Where
  the project is not yet sound" below).

## Strategic situation — May 2026

The project hit a scope wall midway through Part 2 of the roadmap
and pivoted. The honest summary:

- **Part 1** (foundational hygiene, small-`sorry` cleanup): ✅ done.
- **Part 2 framework** (TM-backed `inTimePoly`): ✅ done.
- **Part 2 content** (build the SAT verifier TM by hand): ⏸ paused.
  Original estimate ~1,500 LOC; actual ~14,500 LOC and ~30% done on
  the SAT verifier alone. Continuing in this style projected Parts
  2–6 at ~100–150K LOC, which is multi-year work for a side project.
  The hand-rolled primitives (~8K LOC) and the demo decider library
  (~6K LOC) are now under [`parked/`](parked/).
- **Parts 3–7** rescoped around a new **higher-level computable
  layer** (a small while-language with cost semantics, compiled
  once to `FlatTM`). This is the Lean analogue of the L calculus
  the Coq port uses. Estimated ~13K LOC for Parts 3–7 combined,
  vs ~10K LOC originally but on a much firmer footing — each LOC
  in the layer is amortised across many downstream uses, where
  each LOC of hand-rolled TM construction was bespoke.

Why we paused: building a useful algorithm out of `FlatTM`s, even
via good combinators, requires per-state step lemmas + phase scan
lemmas + iteration lemmas for every primitive. Each primitive lands
in the 1,000–2,500 LOC range with weak cross-primitive amortisation.
The Coq port avoids this by extracting TMs from a higher-level
calculus; we declined to do the same in the original roadmap, and
empirically that was the wrong call.

The full discussion, including a fallback plan if the layer also
overruns (state Cook–Levin **conditionally** on an axiomatic
`inTimePoly` interface), is in
[`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md).

## High-level architecture

The intended proof follows the standard Cook–Levin recipe and mirrors
the Coq port. The reduction chain used by the final theorem:

```
GenNP (List Bool)                  -- universal NP-source language
    ⪯p   LMGenNP (List Bool)       -- L_to_LM.lean       (placeholder bridge)
    ⪯p   LMtoMTMTarget             -- LM_to_mTM.lean     (placeholder bridge)
    ⪯p   IntermediateTMTarget      -- mTM_to_singleTapeTM.lean (placeholder bridge)
    ⪯p   FlatSingleTMGenNP         -- classical case-split (placeholder)
    ⪯p   FlatTCC                   -- Cook 2D tableau (placeholder; new Part 6)
    ⪯p   FlatCC                    -- (sound)
    ⪯p   BinaryCC                  -- (sound)
    ⪯p   FSAT                      -- (sound)
    ⪯p   SAT, kSAT 3               -- (sound)
    ⪯p   FlatClique                -- (sound, via kSAT 3)
```

NP-hardness is transported from `GenNP` along this chain via
`red_NPhard`, yielding `CookLevin0 : NPcomplete (kSAT 3)`,
`CookLevin : NPcomplete SAT`, and `Clique_complete : NPcomplete
FlatClique` in `CookLevin/Complexity/NP/SAT/CookLevin.lean`.

The chain from the second half (`FlatTCC → … → SAT`) is real
mathematics. The chain from `GenNP` down to `FlatTCC` is the part
that depends on placeholder TM bridges and on sorrys #3 and #4.

### What backs each layer

| Layer                                      | Type of object                              | Status |
|--------------------------------------------|---------------------------------------------|--------|
| `encodable`                                | unary size measure                          | sound  |
| `inOPoly`, `monotonic`, `inO`              | asymptotic-growth predicates                | sound  |
| `FlatTM` + `stepFlatTM` + `runFlatTM`      | concrete TM semantics                       | sound  |
| `composeFlatTM`, `branchComposeFlatTM`, …  | TM combinator library (~3.5K LOC)           | sound  |
| `validFlatTM_default`                      | 1-state, 0-transition halting machine       | placeholder |
| `polyTimeComputable f`                     | exists size-bound on `f`                    | **not** runtime-bounded (new Part 4) |
| `DecidesBy P f` + `inTimePoly P`           | actual `FlatTM` + halting / time-budget     | TM-backed; stubs for `EvalCnfTM`, `CliqueRelTM` (sorrys #1, #2) |
| `bridgeMachine` (LM→mTM, mTM→1-tape)       | empty TM that halts at step 0               | placeholder (new Part 5) |
| `TMGenNP_fixed M`, `mTMGenNP_fixed M`      | predicates that ignore `M`                  | placeholder |
| `TMGenNP_fixed → FlatFunSingleTMGenNP`     | `if source then yes_inst else no_inst`      | classical, not computable |
| `FlatSingleTMGenNP → FlatTCC`              | `if source then trivial-yes else no-inst`   | classical, not computable (new Part 6) |
| `FlatTCC → FlatCC`                         | structural encoding, equivalence proved     | **sound** |
| `FlatCC → BinaryCC`                        | unary block encoding, equivalence proved    | **sound** |
| `BinaryCC → FSAT`                          | tableau formula, equivalence proved         | **sound** |
| `FSAT → SAT / 3SAT` (Tseytin)              | correct map, fully proved                   | **sound** |
| `kSAT → SAT`                               | inclusion reduction                         | **sound** |
| `kSAT → FlatClique`                        | classical Karp construction, fully proved   | **sound** |
| `SAT inNP`, `FlatClique inNP`              | TM-backed via `EvalCnfTM` / `CliqueRelTM`   | sound modulo TM-construction stubs |
| `NPhard_GenNP` (`hasDeciderClassical`)     | retyped to `Nonempty (DecidesBy …)`         | placeholder waiting on new Part 7 |

## Where the project is mathematically sound

About half the repository on the proof path is real, computable,
fully-proved Lean and contains the substantial mathematical content
ported from Coq:

- **`Complexity/Complexity/MachineSemantics.lean`** — the `FlatTM`
  model itself (tapes, transitions, single-step semantics, run with
  step-budget).
- **`Complexity/Complexity/Definitions.lean`** — `encodable`,
  `monotonic`, `inO`, `inOPoly`, and the polynomial-composition
  lemmas `inOPoly_add`, `inOPoly_comp` with their honest analytic
  proofs.
- **`Complexity/Complexity/NP.lean`** — the `DecidesBy` structure,
  TM-backed `inTimePoly`, and the reduction calculus
  (`reducesPolyMO_reflexive`, `reducesPolyMO_transitive`,
  `red_inNP`, `red_NPhard`). The single sorry here is a labelled
  TM-composition placeholder for new Part 4.
- **`Complexity/Complexity/TMPrimitives.lean`** (~3.5K LOC) — the
  `composeFlatTM` / `branchComposeFlatTM` combinator family, the
  `runFlatTM_compose` and `runFlatTM_extend` machinery, scan /
  verdict / write primitives. This is the natural target language
  of the new layer's compiler.
- **`Complexity/NP/SAT.lean`** — the SAT language, its evaluator,
  and all supporting lemmas.
- **`Complexity/NP/kSAT.lean`**, **`kSAT_to_SAT.lean`**,
  **`FSAT.lean`** — clean.
- **`Complexity/NP/FSAT_to_SAT.lean`** — a genuine Tseytin
  transformation (~700 LOC), correctness and size bound fully
  proved.
- **`Complexity/NP/kSAT_to_FlatClique.lean`** — the classical Karp
  construction, fully proved.
- **The combinatorial core (~3K LOC):**
  - `FlatTCC_to_FlatCC` (window/cover equivalence both directions,
    real size bound `5n+5`)
  - `FlatCC_to_BinaryCC` (unary block encoding, real size bound
    `50n² + 50n + 1`)
  - `BinaryCC_to_FSAT` (tableau CNF, equivalence proved both
    directions, size bound `500n⁶ + 500`)
- The `validFlattening` / `flattenString` / `unflattenList` machinery
  connecting `Fin k`-typed and `Nat`-flattened representations.

This is the actually meaningful mathematics that has been ported.
The proof of Cook–Levin *after* a TM run has been encoded as a
`FlatTCC` instance is essentially in place.

## Where the project is not yet sound

Two distinct gaps remain between "Lean accepts the theorem" and "the
theorem is a real proof of Cook–Levin":

1. **The four `sorry`s above.** Each corresponds to a piece of
   infrastructure not yet built. They are detailed in the table at
   the top of this README and discussed in
   [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md).

2. **`polyTimeComputable f` only bounds output size.** The current
   `PolyTimeComputableWitness` requires
   `encodable.size (f x) ≤ bound (encodable.size x)` and says
   nothing about the TM that computes `f`. So every reduction in
   the chain is *witnessed* by a size bound, not by a real
   polynomial-time TM. The TM bridge layers
   (`LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean`,
   `…/FlatSingleTMGenNP_to_FlatTCC.lean`, …) are
   placeholders (1-state TMs, classical case-splits on the source
   language). Fixing this is Parts 4–6 of the new roadmap.

### Other smells (low priority)

- `instEncodableDefault` (`Definitions.lean:14`) silently gives
  `size = 0` to any type that lacks an explicit `encodable`
  instance, so a bound of `fun _ => 0` is "satisfiable" for a few
  bridge-stage types. The loophole is shadowed by the placeholder
  TM bridges and will close naturally as those bridges become real.
- `abbrev TM (_σ : Type) (_ : Nat) := FlatTM` (`Definitions.lean:61`):
  alphabet type and tape count are phantom parameters.
- `Complexity/Complexity/Subtypes.lean` is empty.
- `Basic.lean` / `Main.lean` are scaffolding from the Lake template.
- `computableTime'` (`MachineSemantics.lean:186-194`) is a leftover
  Coq port hook whose definition no longer matches its name. The
  new layer (Part 3) supersedes it.
- `CanEnumTerm` for `List Bool` (`CanEnumTerm.lean`) encodes `y` as
  `[true] ++ replicate (size y) false` — a size-only encoding, not
  an injection. Acceptable only because the surrounding framework
  never consults the certificate content. Replaced in new Part 7.

## Repository layout

```
.
├── README.md             -- this file: the single source of truth on status
├── lakefile.lean         -- Lake build configuration (depends on mathlib4)
├── lean-toolchain        -- pinned to leanprover/lean4:v4.30.0-rc2
├── CookLevin/            -- everything on the proof path (~11K LOC)
│   ├── ROADMAP.md        -- the multi-phase plan (read this for the strategy)
│   ├── Basic.lean        -- placeholder
│   ├── Main.lean         -- "Hello, World!" executable entry point
│   ├── Complexity.lean   -- top-level import aggregator
│   └── Complexity/
│       ├── Complexity/
│       │   ├── Definitions.lean       -- encodable, inOPoly, …
│       │   ├── MachineSemantics.lean  -- FlatTM, stepFlatTM, runFlatTM, …
│       │   ├── NP.lean                -- DecidesBy, inTimePoly, ⪯p, NPhard, …
│       │   ├── TMPrimitives.lean      -- composeFlatTM family (~3.5K LOC)
│       │   ├── TMEncoding.lean        -- list-level encoding helpers
│       │   ├── TMDecider.lean         -- inTimePolyTM, DecidesBy combinators
│       │   ├── Subtypes.lean          -- empty stub
│       │   └── Deciders/
│       │       ├── EvalCnfTM.lean     -- SAT verifier interface (sorry #1)
│       │       └── CliqueRelTM.lean   -- FlatClique verifier interface (sorry #2)
│       ├── CanEnumTerm.lean
│       ├── GenNP_is_hard.lean         -- sorry #4 (hasDeciderClassical)
│       ├── L_to_LM.lean               -- placeholder bridge
│       ├── LM_to_mTM.lean             -- placeholder bridge
│       ├── mTM_to_singleTapeTM.lean   -- placeholder bridge
│       ├── TMGenNP_fixed_mTM.lean
│       └── NP/
│           ├── GenNP.lean
│           ├── SAT.lean               -- CNF SAT
│           ├── kSAT.lean              -- k-CNF SAT
│           ├── FSAT.lean              -- Boolean-formula SAT
│           ├── FlatClique.lean        -- k-clique on flat graphs
│           ├── FSAT_to_SAT.lean       -- Tseytin transform (~700 LOC, sound)
│           ├── kSAT_to_SAT.lean
│           ├── kSAT_to_FlatClique.lean
│           ├── TM/
│           │   └── IntermediateProblems.lean
│           └── SAT/
│               ├── CookLevin.lean              -- final theorem statements
│               └── CookLevin/
│                   ├── FlatSingleTMGenNP_to_FlatTCC.lean
│                   ├── FlatTCC_to_FlatCC.lean
│                   ├── FlatCC_to_BinaryCC.lean
│                   ├── BinaryCC_to_FSAT.lean
│                   ├── Reductions/
│                   │   ├── FlatSingleTMGenNP_to_FlatTCC.lean
│                   │   ├── FlatTCC_to_FlatCC.lean
│                   │   ├── FlatCC_to_BinaryCC.lean
│                   │   ├── BinaryCC_to_FSAT.lean
│                   │   └── TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean
│                   └── Subproblems/
│                       ├── SingleTMGenNP.lean
│                       ├── FlatTCC.lean
│                       ├── FlatCC.lean
│                       └── BinaryCC.lean
├── parked/               -- work no longer on the proof path (~14K LOC, not built)
│   ├── README.md
│   ├── PART2.md          -- the paused Part 2 implementation tracker
│   └── CookLevin/Complexity/Complexity/Deciders/
│       ├── SAT_TM.lean             -- Phase-C demonstration deciders (~6.3K LOC)
│       └── EvalCnfTM/
│           ├── Primitives.lean     -- hand-rolled SAT verifier primitives
│           ├── CopyUnary.lean
│           ├── CompareUnary.lean
│           └── PerLiteral.lean
├── coqdoc/               -- local mirror of the Coq port's documentation
├── .github/
│   ├── workflows/        -- CI: lake-build + researcher driver
│   ├── prompts/step01.md … step13.md  -- legacy per-step prompts (archival)
│   └── scripts/researcher.py
└── lake-manifest.json
```

## Building

`mathlib` is the only declared dependency. From the repository root:

```
lake build
```

The first build from a clean checkout takes a long time because
`mathlib` must be cached. Lake's `lean_lib` root is `CookLevin/`,
so the contents of `parked/` are not built.

## Where to look first

If you want to see the **real, working mathematics**, read in order:

1. `CookLevin/Complexity/Complexity/Definitions.lean` — encodings,
   polynomials.
2. `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatTCC.lean`
   — covering semantics.
3. `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/FlatTCC_to_FlatCC.lean`
4. `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/FlatCC_to_BinaryCC.lean`
5. `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/BinaryCC_to_FSAT.lean`
6. `CookLevin/Complexity/NP/FSAT_to_SAT.lean` — Tseytin transformation.

If you want to see the **strengthened framework**, read:

1. `CookLevin/Complexity/Complexity/NP.lean` — `DecidesBy`,
   TM-backed `inTimePoly`, the reduction calculus.
2. `CookLevin/Complexity/Complexity/TMPrimitives.lean` — the
   `composeFlatTM` family.

If you want to see **what still needs to be replaced**, read:

1. `CookLevin/Complexity/GenNP_is_hard.lean` — the
   `hasDeciderClassical` placeholder (sorry #4).
2. `CookLevin/Complexity/LM_to_mTM.lean`,
   `CookLevin/Complexity/mTM_to_singleTapeTM.lean` — dummy bridges.
3. `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean`,
   `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`
   — classical case-split reductions.

If you want to see **what we tried and parked**, read:

1. [`parked/README.md`](parked/README.md) — an overview of what's
   parked and why.
2. [`parked/PART2.md`](parked/PART2.md) — the detailed substep
   tracker for the now-paused hand-rolled SAT verifier.

The strategic path forward (the new "Part 3: higher-level computable
layer" and Parts 4–7) is in
[`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md).

## References

- Coq source: <https://github.com/uds-psl/cook-levin>
- Local Coq documentation mirror: `coqdoc/`
- Project status / roadmap: [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md)
- Parked work overview: [`parked/README.md`](parked/README.md)
- CI: `.github/workflows/lake-build.yml`
