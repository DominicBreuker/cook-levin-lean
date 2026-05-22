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
- Repository size: **~25.7K LOC** of Lean across `CookLevin/`.
- **Four labelled `sorry`s remain**, all flagged with `TODO(...)`
  tags pointing at the roadmap phase that closes them:

  | # | Location                                          | Closes at |
  |---|---------------------------------------------------|-----------|
  | 1 | `CookLevin/Complexity/Complexity/Deciders/EvalCnfTM.lean`   | New Part 3 of ROADMAP |
  | 2 | `CookLevin/Complexity/Complexity/Deciders/CliqueRelTM.lean` | New Part 3 of ROADMAP |
  | 3 | `CookLevin/Complexity/Complexity/NP.lean`                   | New Part 4 of ROADMAP |
  | 4 | `CookLevin/Complexity/GenNP_is_hard.lean`                   | New Part 7 of ROADMAP |

- The build is **conditionally complete**: `theorem CookLevin :
  NPcomplete SAT` typechecks, but it depends on the four sorrys above
  and on a handful of placeholder TM-bridge constructions (see "Where
  the project is not yet sound" below).

## What's actually proved

The codebase divides cleanly into a **sound mathematical core**
(~half the repo, ~13K LOC) and an **infrastructure layer** that is
still under construction.

### Sound mathematical core (no sorrys, no placeholders)

- **`FlatTM` semantics.** Tapes, transitions, single-step semantics,
  bounded execution with step-budget, halting-state acceptance.
  (`CookLevin/Complexity/Complexity/MachineSemantics.lean`)
- **Asymptotic infrastructure.** `inOPoly`, `inOPoly_add`,
  `inOPoly_comp`, `monotonic`, polynomial composition.
  (`CookLevin/Complexity/Complexity/Definitions.lean`)
- **Reduction calculus.** `⪯p`, `reducesPolyMO_reflexive`,
  `reducesPolyMO_transitive`, `red_inNP`, `red_NPhard`.
  (`CookLevin/Complexity/Complexity/NP.lean`)
- **The combinatorial chain.** The full reduction
  `FlatTCC → FlatCC → BinaryCC → FSAT → SAT / 3-SAT`, with real
  size bounds (`5n+5`, `50n² + 50n + 1`, `500n⁶ + 500`), proved
  both directions. This is the substantial mathematical content
  ported from Coq.
  (`CookLevin/Complexity/NP/SAT/CookLevin/Reductions/`)
- **The Tseytin transform** `FSAT → SAT`, ~700 LOC, fully proved.
  (`CookLevin/Complexity/NP/FSAT_to_SAT.lean`)
- **k-SAT → SAT and k-SAT → FlatClique** reductions.
  (`CookLevin/Complexity/NP/kSAT_to_SAT.lean`,
   `CookLevin/Complexity/NP/kSAT_to_FlatClique.lean`)
- **`SAT_inNP`, `FlatClique_in_NP`** modulo their `DecidesBy`
  witnesses (sorrys #1 and #2): the polynomial-certificate side is
  fully proved.
- **TM combinator library.** `composeFlatTM`, `branchComposeFlatTM`,
  `runFlatTM_compose`, `runFlatTM_extend`, scan / verdict / write
  primitives. ~3.5K LOC of fully proved Lean. Will be the target
  language of the in-progress higher-level layer.
  (`CookLevin/Complexity/Complexity/TMPrimitives.lean`)

### Infrastructure layer — strengthened in Part 2 of the roadmap

- **`DecidesBy` and TM-backed `inTimePoly`.** `inTimePoly P` now
  requires a concrete `FlatTM` plus halting-state and step-bound
  run lemmas — strictly stronger than the original propositional
  `HasDecider`.
- **`sat_NP`, `FlatClique_in_NP`** rebuilt against the new
  framework. Their concrete `DecidesBy` witnesses (sorrys #1, #2)
  are the next milestone.
- **`red_inNP`, `P_NP_incl`** rebuilt against the new framework.
  The composition obligation that requires a TM-backed
  `polyTimeComputable` is sorry #3.
- **`hasDeciderClassical`** retyped to produce
  `Nonempty (DecidesBy …)`. Body is sorry #4, closed in new Part 7.

### Where the project is not yet sound

Two distinct gaps remain between "Lean accepts the theorem" and "the
theorem is a real proof of Cook–Levin":

1. **The four `sorry`s above.** Each one corresponds to a piece of
   infrastructure not yet built. Detailed status in
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
   language). Fixing this is Parts 4–6 of the roadmap.

A line-by-line audit of these issues lives at the top of
[`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md) ("Part 0 — Honest
assessment").

## Strategic situation — May 2026

The project just hit a scope wall midway through Part 2 of the
roadmap and pivoted. The honest summary:

- **Part 1** (foundational hygiene, small-`sorry` cleanup): ✅ done.
- **Part 2 framework** (TM-backed `inTimePoly`): ✅ done.
- **Part 2 content** (build the SAT verifier TM by hand): ⏸ paused.
  Original estimate ~1,500 LOC; actual ~14,500 LOC and ~30% done on
  the SAT verifier alone. Continuing in this style projected Parts
  2–6 at ~100–150K LOC, which is multi-year work for a side project.
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
the Coq port:

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

The chain from the second half (`FlatTCC → ... → SAT`) is real
mathematics. The chain from `GenNP` down to `FlatTCC` is the part
that depends on placeholder TM bridges and on sorrys #3 and #4.

## Repository layout

```
.
├── README.md             -- this file
├── lakefile.lean         -- Lake build configuration (depends on mathlib4)
├── lean-toolchain
├── CookLevin/
│   ├── README.md         -- detailed project status, per-file map
│   ├── ROADMAP.md        -- the multi-phase plan (read this for the strategy)
│   ├── PART2.md          -- Part 2 implementation tracker (paused, archival)
│   ├── Basic.lean        -- placeholder
│   ├── Main.lean         -- "Hello, World!" executable entry point
│   ├── Complexity.lean   -- top-level import aggregator
│   └── Complexity/       -- the project proper (~25K LOC)
│       ├── Complexity/   -- complexity-theoretic framework
│       │   ├── Definitions.lean
│       │   ├── MachineSemantics.lean
│       │   ├── NP.lean
│       │   ├── TMPrimitives.lean
│       │   ├── TMEncoding.lean
│       │   ├── TMDecider.lean
│       │   └── Deciders/  -- in-progress TM verifier constructions
│       └── NP/           -- the language reductions
│           ├── SAT.lean, FSAT.lean, kSAT.lean, FlatClique.lean, ...
│           ├── FSAT_to_SAT.lean, kSAT_to_SAT.lean, kSAT_to_FlatClique.lean
│           └── SAT/CookLevin/    -- the combinatorial chain
│               ├── Subproblems/
│               └── Reductions/
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
`mathlib` must be cached.

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

If you want to see **the strengthened framework**, read:

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

The strategic path forward (the new "Part 3: higher-level computable
layer" and Parts 4–7) is in
[`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md). The history of the
paused Part 2 content effort is in
[`CookLevin/PART2.md`](CookLevin/PART2.md).

## References

- Coq source: <https://github.com/uds-psl/cook-levin>
- Local Coq documentation mirror: `coqdoc/`
- Project status / roadmap: [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md)
- Detailed per-file status: [`CookLevin/README.md`](CookLevin/README.md)
- Paused Part 2 tracker (archival): [`CookLevin/PART2.md`](CookLevin/PART2.md)
- CI: `.github/workflows/lake-build.yml`
