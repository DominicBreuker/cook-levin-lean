# Cook–Levin in Lean 4 — Roadmap

Working strategy doc for `theorem CookLevin : NPcomplete SAT`. Written for
agents developing the project — it describes the **current risk landscape
and what to do next**, not a history. (Compact log-style notes are kept
only where they save a future agent from re-deriving a decision.)

**Orientation:** the theorem typechecks but is **conditional**. The
combinatorial heart of Cook–Levin is real and done; the rest is a
compiling skeleton plus a few `sorry`-free but *vacuous* reductions. The
strategy for making it real is the **higher-level computable layer**: a
small while-language (`Cmd`) with cost semantics, compiled once to
`FlatTM` (`Compile`), so every verifier/reduction is a short DSL program
instead of a hand-rolled Turing machine.

**The single most important thing to read next:** the Risk register
(below) and the current next-topic brief
[`S3_RETIREMENT_EXPLORATION.md`](S3_RETIREMENT_EXPLORATION.md).

---

## Status snapshot

| | |
|---|---|
| `lake build` | ✅ green |
| Project axioms | **0** (only `propext` / `Classical.choice` / `Quot.sound`) |
| Proof-path size | ~11K LOC under `CookLevin/` (a further ~14K parked, not built) |
| `sorry`s on the proof path | ~29, all `TODO(...)`-tagged (Group C) |
| `sorry`-**free** vacuous defs on the proof path | ≥ 4 (Risks S1/S2 — the deepest gaps; **not** counted above, invisible to `#print axioms`) |
| Headline | `CookLevin : NPcomplete SAT` typechecks, **conditional** on Group C **and** S1/S2/S3 |

> **The `sorry` count is not the soundness metric.** The deepest
> unsoundness (S1/S2) is `sorry`-free. Track Group S (soundness) and
> Group C (completion) separately; closing every `sorry` does **not** by
> itself make `CookLevin` unconditional.

---

## The proof path

```
GenNP                          universal NP source
  ⪯p LMGenNP                   L_to_LM.lean            (identity bridge)
  ⪯p LMtoMTMTarget             LM_to_mTM.lean          (DUMMY bridge — S2)
  ⪯p TMGenNP_fixed             mTM_to_singleTapeTM.lean(DUMMY bridge — S2)
  ⪯p FlatSingleTMGenNP         CookLevin.lean
  ⪯p FlatTCC                   Reductions/FlatSingleTMGenNP_to_FlatTCC.lean
                                                       (IF-ON-THE-ANSWER — S1)
  ⪯p FlatCC ⪯p BinaryCC ⪯p FSAT ⪯p SAT/3SAT/FlatClique   ← SOUND, done
```

NP-hardness is transported from `GenNP` along this chain via `red_NPhard`,
giving `CookLevin : NPcomplete SAT` in
`Complexity/NP/SAT/CookLevin.lean`. `inNP SAT` needs a real SAT verifier
(the layer's `evalCnfCmd`, C7).

**Sound (the genuine mathematics, ~3K LOC, sorry-free, do not touch):**
`FlatTCC → FlatCC → BinaryCC → FSAT → SAT` (window/cover equivalence, unary
block encoding, tableau CNF, Tseytin), plus `kSAT_to_SAT`,
`kSAT_to_FlatClique`. Cook–Levin *after* a TM run is encoded as a `FlatTCC`
is essentially in place.

**Not sound (the front, `GenNP → FlatTCC`):** dummy TM bridges (S2) and an
if-on-the-answer reduction (S1), both licensed by the size-only
`polyTimeComputable` (S3).

---

## Risk register

Two groups. **Group S** determines *what the conditional theorem currently
means* (several are `sorry`-free). **Group C** is the compiling-skeleton
gaps. Refine the highest-ranked item next.

### Group S — soundness gaps (mostly `sorry`-free)

| # | Gap | Location | What closing it needs |
|---|-----|----------|-----------------------|
| **S3** | **`polyTimeComputable` bounds output size only** — the enabling weakness that lets S1/S2 typecheck. `PolyTimeComputableWitness` requires only `size (f x) ≤ bound (size x)`, no TM computing `f`. | `Complexity/NP.lean`, `Lang/PolyTime.lean` | Upgrade the witness to be **TM-/layer-backed** (carry a `PolyTimeComputableLang` program). **← THE CURRENT NEXT TOPIC; see [`S3_RETIREMENT_EXPLORATION.md`](S3_RETIREMENT_EXPLORATION.md).** This is the linchpin: it makes the layer meaningful and forces S1/S2 to become real. |
| **S1** | **if-on-the-answer reduction** `FlatSingleTMGenNP ⪯p FlatTCC` — map is `if (source is yes-inst) then yesInst else noInst`; output depends on the *answer*. Deepest unsoundness. | `Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`, `.../TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean` | The real **Cook 2D tableau** (`Simulators/CookTableau.lean`). **Probed: feasible but expensive (~6–11K LOC, bijection-dominated).** Gated on S3 (dead until then). |
| **S2** | **dummy TM bridges** — `bridgeMachine` is a 1-state TM that discards the source `M`; `TMGenNP_fixed`/`mTMGenNP_fixed` ignore `M`. The `GenNP→TMGenNP` arrow carries no content. | `LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean`, `TMGenNP_fixed_mTM.lean` | Real TM simulators incl. **multi-tape → single-tape** (`Simulators/MultiToSingle.lean`, a stub). Gated on S3. |
| **S4** | **the real constructions are orphans** — `cookTableau` (real, 2 `sorry`s) and `multiToSingle` (stub, 3 `sorry`s) are referenced by **no** reduction. | `Simulators/CookTableau.lean`, `Simulators/MultiToSingle.lean` | Wiring S1/S2 to call them (after S3). Until then proving them advances `CookLevin` by zero. |

**Companion (Part 0.1):** `instEncodableDefault` (`Definitions.lean`) gives
`size = 0` to any type lacking an explicit `encodable` instance. Combined
with S3 it makes some bridge-stage bounds vacuous. Closes as the bridges
become real + real `encodable` instances are added.

### Group C — completion risks (the compiling skeleton)

C1–C4 are **structural** (validate the pivot / change downstream
signatures); C5–C6 are **design**; C7–C8 are **engineering** gated on the
above.

| # | Gap | Status |
|---|-----|--------|
| **C4** | **layer → framework bridge** (`Lang/PolyTime.lean`'s 4 bridges, `NP.lean`'s `red_inNP`). Same upgrade as **S3**. | **Top open structural item; = the S3 probe.** |
| **C1** | **per-`Op` compilation** (`compileOp` + `compileOp_sound`). | ✅ **validated** — reusable gadget library built (`insertCarryTM`, `scan_to_mark`/`scanPastDelimTM`/`scanLeftUntilTM`, `appendAtTM`); `appendOne/Zero` are real `CompiledCmd`s. Remaining: physical `compileOp_sound` per op + the length-decreasing ops (use the `endMark=3` sentinel; see lessons). Bounded eng (~1.5–2.5K LOC for all 8 ops). |
| **C2** | **composition** (`compileSeq_sound`). | ✅ **validated** — `compileSeq_compose_physical` proves fragments compose under the physical contract (halt at `exit`, head rewound to `0`, tape `= encodeTape output`, exact step, no-early-halt). Bounded eng. |
| **C3** | **`loopTM` counted loop** (`compileForBnd` + `_sound`). | ✅ **validated** — `loopTM` + full run lemma `loopTM_run` in `TMPrimitives.lean`, sorry-free, axiom-clean, ~500 LOC. Remaining: a guard + a **marker-overwrite (non-shrinking) decrement** gadget, wire `compileForBnd`, instantiate `loopTM_run`. Bounded eng. |
| **C5** | **DSL expressiveness** — `evalCnfCmd` wanted a guarded loop and a constant-comparison primitive. | Add primitives only when they materially shorten a verifier (each new `Op` = another soundness proof). |
| **C6** | **`compileIfBit` tester** — structure done (`branchComposeFlatTM`+`joinTwoHalts`); the real bit-test + `compileIfBit_sound` remain. | Same flavour as C1. |
| **C7** | **verifier bodies** — `evalCnfCmd` (SAT), `cliqueRelCmd` (`Deciders/`). | DSL engineering; gated on C3+C5 and dead until C4 makes the layer→`DecidesBy` bridge real. |
| **C8** | **real `NPhard_GenNP`** (`hasDeciderClassical`, `GenNP_is_hard.lean`). | Last `sorry`; needs C4 (verifier TM from `InNPWitness`). |

**Standing ranking.** C1/C2/C3 (the pivot's make-or-break unknowns) are
all validated, so **no Group-C item is a structural unknown** and the
layer is bounded engineering. The remaining *structural* risk lives in
Group S — and **S3/C4 is the gate** for all of it. That is why the next
topic is S3.

---

## Strategic situation: two end-states

There are two honest destinations. The next probe (S3) decides which.

1. **Real, unconditional `CookLevin`.** Requires, in order:
   (a) **retire S3** (TM-back `polyTimeComputable`) — the gate;
   (b) finish the layer: `Compile_sound` (C1 ops + C3 `compileForBnd` +
       C6 tester), then the verifier C7 → `inNP SAT`;
   (c) the real reductions S3 exposes: S1 Cook tableau (~6–11K LOC,
       probed feasible), S2 multi-tape simulator (S4, unprobed), C8;
   (d) real `encodable` instances on the chain (Part 0.1).
   Large but, post-C1/C2/C3, mostly *bounded* engineering — except the S1
   tableau (expensive-but-feasible) and the S2 simulator (the remaining
   unprobed cost).

2. **Honest conditional theorem (fallback).** If retiring S3, or the
   reductions it exposes, prove intractable for a side project: state
   `CookLevin` conditionally on a **documented axiomatic `inTimePoly` /
   `⪯p` interface**, keep the sound combinatorial tail, and stop. The code
   is ~80% there for this scope. Triggered if the S3 probe's verdict is
   (iii), or if Part 3 overruns its estimate ~3×.

**The S3 probe is the decision point** between these. It is the one
remaining structural unknown that determines whether the unconditional
path is open. See [`S3_RETIREMENT_EXPLORATION.md`](S3_RETIREMENT_EXPLORATION.md).

---

## How we work — skeleton-first, risk-driven

This methodology is the lesson of the May 2026 pivot (Part 2 blew up ~10×
because structural issues were invisible until attempted). **Do not
deviate without an explicit reason.**

1. **Skeleton first, then refine.** The whole proof path compiles (with
   `sorry`s) before any single proof is closed. A compiling skeleton
   exposes every downstream obligation; an isolated proof exposes nothing.
2. **Refine the highest-risk gap next** (per the Risk register), not in
   phase order. Each refinement either validates a committed shape or
   surfaces a gap — both are progress.
3. **Decompose `sorry`s, don't elaborate them.** Split a big `sorry` into
   focused sub-`sorry`s; each split is a structural decision that
   typechecks (right shape) or fails (gap found).
4. **Prefer concrete `def` + `sorry` over `axiom`.** Axiom count is a
   metric to minimise (currently 0).
5. **Probe before committing engineering.** For a big unknown, run a
   time-boxed go/no-go probe (assume lower layers, validate the structure
   additively, measure, give a verdict: feasible / feasible-but-expensive
   / trigger-fallback). C1/C2/C3 and the S1-tableau probe followed this.
6. **Build green between commits; record gaps in commit messages**, not
   private notes.

---

## Validated so far (probe digest)

Compact record of what each probe established (so they aren't re-run):

- **C1 (per-`Op`):** primitives are hundreds of LOC, **not** ~50 — but the
  cost front-loads into a reusable gadget library that amortises, and
  composition is cheap. `appendOne/Zero` compile end-to-end. Length-
  *decreasing* ops hit a tape-model wall (tape content never shrinks);
  resolved by the **sentinel alphabet** (`endMark = 3`, `sig = 4`, also a
  leading sentinel for head-rewind).
- **C2 (composition):** `compileSeq_compose_physical` — fragments compose
  cleanly under the **physical contract** (head-`0` exit, tape =
  `encodeTape output`, exact step, no-early-halt trajectory). The contract,
  not just the gadget, is what `composeFlatTM_run` needs.
- **C3 (`loopTM`):** GREEN. The combinator + full run lemma is ~500 LOC
  *marginal* on the composition machinery (vs. ~1000 LOC/loop-site
  hand-rolled, paid once). The feared backward-bridge/re-entry difficulty
  didn't materialise: each pass is a fresh body-phase lift chained by
  `runFlatTM_compose`, so the trajectory resets at each `body.start`.
  Finding: prefer a **non-shrinking (marker-overwrite) counter encoding**.
- **S1 (Cook tableau):** feasible but expensive (~6–11K LOC, bijection-
  dominated). `cookTableau` is a real computable construction (no
  if-on-the-answer) with a constrained-case bijection proved. Findings: the
  alphabet is `|Σ|=(M.sig+1)(M.states+2)`; size is **quartic** in `|Σ|` (the
  earlier cubic bound was false); the wildcard-free TCC card model forces
  `Θ(|Σ|³)` identity cards (a pervasive cost multiplier).

---

## Key lessons (from the abandoned hand-rolled Part 2)

For anyone tempted to build verifiers directly as `FlatTM`s again:

1. **Per-state lemmas don't amortise across primitives** — each primitive
   needs its own step/scan/run lemmas. (The layer fixes this by paying TM
   construction *once* in the compiler.)
2. **Iteration bookkeeping was the dominant cost** (~1000 LOC/loop site).
   The layer pays it once in `loopTM` (C3, validated).
3. **Single-tape with a delimiter scratch is the only economical shape**
   for hand-rolled composition — multi-tape composition needs `(sig+1)^k`
   bridge entries. The compiler respects this.
4. **The layer needs *cost* in its semantics, not just behaviour** —
   mathlib's `Computable`/`Partrec` handles computability but not
   complexity.

Why the pivot: building a useful algorithm from `FlatTM`s, even with good
combinators, ran ~10× over budget; continuing projected Parts 2–6 at
~100–150K LOC. The Coq port avoids this by extracting TMs from the L
calculus; the layer is the Lean analogue (smaller: total structured
while-language vs. general λ-calculus). Parked hand-rolled work (~14K LOC)
lives under `parked/`.

---

## References

- Coq source: <https://github.com/uds-psl/cook-levin>; local mirror `coqdoc/`.
- Status / orientation: root `README.md`.
- Current next-topic brief: [`S3_RETIREMENT_EXPLORATION.md`](S3_RETIREMENT_EXPLORATION.md).
- Parked work: `parked/README.md`, `parked/PART2.md`.
