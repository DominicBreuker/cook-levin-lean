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
strengthened complexity framework, but the rest is a **compiling
skeleton**: ~34 labelled `sorry`s across the Parts 3–7 scaffolding,
**plus** a handful of `sorry`-free but *vacuous* reductions on the
proof path (the deepest gaps — they do not show up as `sorry`s or
under `#print axioms`). See
[`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md) for the full plan,
and its **Risk register** for the soundness gaps (Group S) and
completion gaps (Group C) tracked separately.

## Status at a glance (May 2026)

- `lake build` succeeds (3350 jobs); **0 axioms** repo-wide.
- Repository size: **~11K LOC** of Lean on the proof path under
  `CookLevin/` (a further ~14K LOC of paused / superseded work
  lives under [`parked/`](parked/), not built).
- **~34 labelled `sorry`s** across the Parts 3–7 skeleton, all
  flagged with `TODO(...)` tags. The current per-file distribution
  and the next-step ranking live in the **Risk register** of
  [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md) (Group C). The
  original "four `sorry`s" from the framework migration were
  decomposed into these when Parts 3–7 were scaffolded as a
  compiling skeleton.
- **The `sorry` count is not the soundness metric.** The deepest
  gaps on the proof path are `sorry`-**free** and so do not appear in
  that count or under `#print axioms`:
  - two `if-on-the-answer` reductions (`FlatSingleTMGenNP_to_FlatTCC`,
    `TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP`) whose output
    depends on the *truth* of the source predicate;
  - the dummy `bridgeMachine`s (1-state TMs that discard the source
    machine) reached via `GenNP_to_TMGenNP`;
  - both licensed by `polyTimeComputable` bounding only *output size*,
    not runtime.

  These are Risks **S1–S3** in the ROADMAP Risk register.
- The build is **conditionally complete**: `theorem CookLevin :
  NPcomplete SAT` typechecks, but it depends on the ~34 `sorry`s
  **and** on the `sorry`-free vacuous reductions/bridges above (see
  "Where the project is not yet sound" below).

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

## Development strategy: skeleton-first, risk-driven refinement

This is the working methodology for the remaining Parts of the
ROADMAP. **Do not deviate from it without an explicit reason** —
it is the lesson the May 2026 pivot taught us, and it directly
addresses the failure mode that produced the scope overrun.

The core idea: **write the compiling skeleton of the entire proof
path first**, with `sorry` and lightweight scaffolding wherever
proofs are hard, **then iteratively refine the highest-risk
parts**. Each refinement either validates the shape we committed
to or surfaces a real structural gap. Either outcome is information
we want *early*, not after thousands of LOC of follow-on
engineering.

### Principles

1. **Skeleton first, then refine.** Get the whole proof path to
   typecheck — with `sorry`s — before any individual proof is
   closed. A compiling skeleton exposes the shape of every
   downstream obligation; a partial proof of one isolated piece
   exposes nothing.
2. **Prefer concrete `def` + `sorry` over `axiom`.** Axioms hide
   work behind an opaque declaration and tend to accumulate.
   Concrete `def`s with `sorry`-bodied lemmas expose dependencies
   and force design questions early. **Axiom count is a metric to
   minimise.**
3. **Decompose sorrys, don't elaborate them.** When a sorry stands
   in front of real work, prefer splitting it into smaller, more
   focused sorrys rather than starting the proof. Each split is a
   structural decision: it either typechecks (the structure is
   right) or fails (a gap is surfaced).
4. **Refine the highest-risk parts first.** Iterate: look at the
   current axioms and largest sorrys, pick the most uncertain one,
   try to concretize it. Concretizing is what surfaces gaps —
   abstract declarations cannot.
5. **Build after every change.** The build is the source of truth
   for "the skeleton is still coherent". Let failures be
   deliberate; keep the build green between commits.
6. **Document gaps as they're found, not after the fact.** When
   writing concrete code surfaces a missing primitive, an
   unrealistic bound, or a wrong type signature, record it
   immediately in a comment or commit message. These notes are the
   highest-leverage TODO list we have.

### Why this works for us

The original ROADMAP described Parts 1–7 as sequential
implementation phases with LOC estimates. Part 2 blew up ~10×
*because* the proof obligations had structural issues that weren't
visible until they were tried. Skeleton-first surfaces those
issues before we commit the engineering hours.

Empirical wins from the first few iterations of this methodology
(May 2026):

- **6 axioms eliminated in one pass** the moment we tried to use
  them concretely: `Op.eval`, `Op.cost`, `Cmd.eval`, `Cmd.cost`,
  `Compile.overhead`, `Compile.decodeTape`. Lean accepted the
  structural recursion through `List.foldl` with no termination
  hints, and **6 compositional-law `sorry`s closed by `rfl` /
  `simp`** as a side benefit.
- **`DecidesLang.encodeIn_size`'s `≤ size + 1` bound was caught as
  unprovable** the moment we tried to write a real encoder for the
  SAT verifier. Relaxed to `≤ costBound size` in the same pass.
- **Two DSL expressiveness gaps surfaced** (no conditional loop,
  no constant-comparison primitive) by trying to write
  `evalCnfCmd` — found *before* paying ~10K LOC of follow-on
  Cmd-engineering work.

### What to do when stuck

If a piece of the skeleton resists refinement:

1. **State the obstacle precisely.** What specifically doesn't
   typecheck? What proof can't you construct?
2. **Classify it.** Is it a *structural gap* (wrong type
   signature, missing primitive, contradictory hypothesis) or a
   *dull engineering bottleneck* (a 200-line case analysis)?
3. **For structural gaps: fix the structure first.** Editing the
   types and rebuilding is far cheaper than working around a bad
   structure with a long proof.
4. **For engineering bottlenecks: leave the `sorry`, move on.**
   The skeleton is more valuable than any single completed proof.
5. **Always commit + push the skeleton state**, with the obstacle
   noted in a comment or commit message. The next iteration starts
   from a documented gap, not from memory.

### Metrics we track per iteration

- `lake build` status (must be green).
- Axiom count (minimise — see Principle 2).
- Sorry count by file (decompose, don't elaborate — see Principle 3).
- Gaps surfaced this iteration (record in commit message).

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

Three distinct classes of gap remain between "Lean accepts the
theorem" and "the theorem is a real proof of Cook–Levin". The first
is visible as `sorry`s; the other two are **not**, which is why the
`sorry` count alone overstates how close the proof is.

1. **The ~34 skeleton `sorry`s** (ROADMAP Risk register, Group C).
   Each is a not-yet-built piece of the higher-level computable layer
   (the compiler, its soundness, the verifier/reduction programs) or
   of the final assembly. The highest-leverage one is **C1**: prove a
   single primitive `Op` sound end-to-end, which tests the pivot's
   premise that primitives are cheap.

2. **`sorry`-free vacuous reductions on the proof path** (Risks
   S1/S2). Two reduction maps —
   `…/Reductions/FlatSingleTMGenNP_to_FlatTCC.lean` and
   `…/Reductions/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean`
   — are `if (source instance is a yes-instance) then yesInst else
   noInst`, so the reduction's output depends on the *answer* to the
   source problem. The TM bridges `LM_to_mTM.lean` /
   `mTM_to_singleTapeTM.lean` are 1-state machines that discard the
   source machine. These compile without `sorry` and do not appear
   under `#print axioms`, but carry no computational content. They
   are the deepest unsoundness; fixing them is Parts 5–6, and depends
   on the layer (Parts 3–4) landing first.

3. **`polyTimeComputable f` only bounds output size** (Risk S3). The
   current `PolyTimeComputableWitness` requires
   `encodable.size (f x) ≤ bound (encodable.size x)` and says
   nothing about the TM that computes `f`. This is the weakness that
   *licenses* the vacuous reductions in (2): every reduction in the
   chain is witnessed by a size bound, not by a real polynomial-time
   TM. Upgrading it is Part 4 (Risk C4).

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
