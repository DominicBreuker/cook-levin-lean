# Cook–Levin in Lean 4

A Lean 4 formalisation targeting the **Cook–Levin theorem** (SAT is
NP-complete), structured as a port of the Coq development by Forster,
Kunze, Roth et al. (<https://github.com/uds-psl/cook-levin>, mirrored under
`coqdoc/`).

**Work in progress.** `CookLevin/Complexity/NP/SAT/CookLevin.lean` declares
`theorem CookLevin : NPcomplete SAT` and Lean accepts it, but the term is
**not yet a faithful proof**: the combinatorial heart is rigorous, but the
rest is a *compiling skeleton* (`sorry`s) plus a few `sorry`-free but
*vacuous* reductions. See [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md)
for the strategy and the **Risk register**, and
[`CookLevin/S3_RETIREMENT_EXPLORATION.md`](CookLevin/S3_RETIREMENT_EXPLORATION.md)
for the current next topic.

## Status at a glance

- `lake build` ✅ green; **0 project axioms** (only `propext` /
  `Classical.choice` / `Quot.sound`).
- ~11K LOC on the proof path under `CookLevin/` (a further ~14K parked,
  not built).
- ~29 `TODO`-tagged `sorry`s (completion gaps, Risk register Group C).
- **≥ 4 `sorry`-free *vacuous* defs** on the proof path — the deepest gaps
  (Risks S1/S2/S3). They do **not** appear in the `sorry` count or under
  `#print axioms`, so the `sorry` count overstates how close the proof is.
- `CookLevin : NPcomplete SAT` typechecks but is **conditional** on all of
  the above.

## What is sound vs. what is not

The proof follows the standard recipe; NP-hardness is transported from a
universal NP source down to SAT along a chain of `⪯p` reductions:

```
GenNP ⪯p … ⪯p FlatSingleTMGenNP ⪯p FlatTCC ⪯p FlatCC ⪯p BinaryCC ⪯p FSAT ⪯p SAT
└──────────── front: NOT sound ────────────┘└──────────── tail: SOUND ───────────┘
```

**Sound (real mathematics, ~3K LOC, do not touch):** the tail
`FlatTCC → FlatCC → BinaryCC → FSAT → SAT` (window/cover equivalence, unary
block encoding, tableau CNF, a full Tseytin transform), plus `kSAT_to_SAT`
and `kSAT_to_FlatClique`. The `FlatTM` model, the `encodable`/`inOPoly`
machinery, the `DecidesBy`/`inTimePoly` interface, and the `composeFlatTM`
combinator family (~3.5K LOC) are also sound. Cook–Levin *after* a TM run
is encoded as a `FlatTCC` is essentially in place.

**Not sound (the front, `GenNP → FlatTCC`):**
- **S1** — `FlatSingleTMGenNP ⪯p FlatTCC` is `if (source is yes-instance)
  then yesInst else noInst`; its output depends on the *answer*. Deepest
  gap. Real fix = the Cook 2D tableau (`Simulators/CookTableau.lean`,
  probed feasible-but-expensive).
- **S2** — the `LM→mTM→singleTape` bridges use a 1-state `bridgeMachine`
  that discards the source TM. Real fix = real TM simulators
  (`Simulators/MultiToSingle.lean`).
- **S3** — these typecheck only because `polyTimeComputable` bounds
  *output size*, not runtime. **Retiring S3 is the current next topic** —
  it is the linchpin that makes the layer meaningful and forces S1/S2 to
  be real.

## The strategy: a higher-level computable layer

Building verifiers/reductions directly as `FlatTM`s overran budget ~10× and
was abandoned (parked under `parked/`). The pivot: a small structured
while-language `Cmd`/`Op` with explicit **cost** semantics, compiled **once**
to `FlatTM` (`Compile`). Every downstream verifier/reduction is then a short
DSL program. This is the Lean analogue of the L calculus the Coq port uses.

The layer's three make-or-break structural unknowns are **validated**:
per-primitive compilation (C1), composition (C2,
`compileSeq_compose_physical`), and the counted loop (C3, `loopTM` +
`loopTM_run`, sorry-free). What remains in the layer is bounded
engineering. The remaining *structural* risk is **S3** (above) — see the
ROADMAP Risk register and the next-topic brief.

## Development strategy: skeleton-first, risk-driven

The working methodology (do not deviate without reason):

1. **Skeleton first** — the whole proof path compiles with `sorry`s before
   any single proof is closed.
2. **Refine the highest-risk gap next** (per the Risk register), not in
   phase order.
3. **Decompose `sorry`s, don't elaborate them** — split a big `sorry` into
   focused sub-`sorry`s; each split is a structural decision.
4. **Prefer `def` + `sorry` over `axiom`** (axiom count is a metric to
   minimise; currently 0).
5. **Probe before committing engineering** — for a big unknown, run a
   time-boxed go/no-go probe: assume lower layers, validate the structure
   additively, measure, give a verdict (feasible / feasible-but-expensive /
   trigger-fallback).
6. **Build green between commits; record gaps in commit messages.**

## Repository layout

```
CookLevin/
├── ROADMAP.md                    -- strategy + Risk register (read for direction)
├── S3_RETIREMENT_EXPLORATION.md  -- the current next-topic brief
├── Complexity/
│   ├── Complexity/
│   │   ├── Definitions.lean      -- encodable, inOPoly, monotonic
│   │   ├── MachineSemantics.lean -- FlatTM, stepFlatTM, runFlatTM
│   │   ├── NP.lean               -- DecidesBy, inTimePoly, ⪯p, NPhard (S3 lives here)
│   │   ├── TMPrimitives.lean     -- composeFlatTM/branchComposeFlatTM/loopTM (~4K LOC)
│   │   └── Deciders/             -- SAT / FlatClique verifier interfaces (C7)
│   ├── Lang/                     -- the layer: Syntax, Semantics, Compile,
│   │   │                            PolyTime (the S3/C4 bridges), gadgets
│   │   └── …
│   ├── Simulators/               -- CookTableau (S1), MultiToSingle (S2) — orphans (S4)
│   ├── GenNP_is_hard.lean        -- NPhard_GenNP (C8)
│   ├── L_to_LM / LM_to_mTM / mTM_to_singleTapeTM.lean  -- bridges (S2)
│   └── NP/
│       ├── SAT.lean / kSAT.lean / FSAT.lean / FlatClique.lean
│       ├── FSAT_to_SAT.lean      -- Tseytin (~700 LOC, sound)
│       └── SAT/CookLevin.lean + CookLevin/Reductions/ + Subproblems/
parked/                           -- paused hand-rolled work (~14K LOC, not built)
coqdoc/                           -- local mirror of the Coq port
```

## Building

`mathlib` is the only dependency. From the repo root:

```
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

First build from a clean checkout is slow (mathlib cache). Lake's
`lean_lib` root is `CookLevin/`, so `parked/` is not built.

## Where to look first

- **Real mathematics:** `NP/SAT/CookLevin/Subproblems/FlatTCC.lean` and the
  `Reductions/FlatTCC_to_FlatCC.lean → … → BinaryCC_to_FSAT.lean` chain,
  then `NP/FSAT_to_SAT.lean`.
- **The framework:** `Complexity/NP.lean` (`DecidesBy`, `inTimePoly`, `⪯p`)
  and `Complexity/TMPrimitives.lean` (`composeFlatTM`/`loopTM`).
- **The layer:** `Complexity/Lang/` (`Compile.lean`, `PolyTime.lean`).
- **What must be replaced:** the S1/S2/S3 entries in the ROADMAP Risk
  register, and the current brief
  [`CookLevin/S3_RETIREMENT_EXPLORATION.md`](CookLevin/S3_RETIREMENT_EXPLORATION.md).

## References

- Coq source: <https://github.com/uds-psl/cook-levin>; mirror `coqdoc/`.
- Roadmap / Risk register: [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md).
- Parked work: [`parked/README.md`](parked/README.md).
