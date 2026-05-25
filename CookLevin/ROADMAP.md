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
(below). The S3 probe ([`S3_RETIREMENT_EXPLORATION.md`](S3_RETIREMENT_EXPLORATION.md))
is **complete** — verdict *(ii) feasible but expensive* (see the S3 entry
in *Validated so far*); the new next topic is **Risk C9 (canonical layer
encoding)**, the prerequisite for executing the S3 migration.

---

## Status snapshot

| | |
|---|---|
| `lake build` | ✅ green |
| Project axioms | **0** (only `propext` / `Classical.choice` / `Quot.sound`) |
| Proof-path size | ~11K LOC under `CookLevin/` (a further ~14K parked, not built) |
| `sorry`s on the proof path | ~29, all `TODO(...)`-tagged (Group C) |
| S3 probe | ✅ complete — verdict *(ii) feasible but expensive*; honest witness + bridge landed additively in `Lang/PolyTime.lean` (sorry-free modulo `Compile_sound`) |
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
| **S3** | **`polyTimeComputable` bounds output size only** — the enabling weakness that lets S1/S2 typecheck. `PolyTimeComputableWitness` requires only `size (f x) ≤ bound (size x)`, no TM computing `f`. | `Complexity/NP.lean`, `Lang/PolyTime.lean` | **Probed: feasible but expensive — proceed after C9 (canonical encoding).** The honest TM-backed witness `PolyTimeComputableWitness'` (extends the old one) and the real bridge `toFrameworkWitness'` are built additively in `Lang/PolyTime.lean` (sorry-free modulo `Compile_sound`); D confirms S1/S2 stop typechecking. Executing the verdict = migrate `ReductionWitness`'s `reduction_poly` to `polyTimeComputable'`, which needs C9 then ripples to every reduction (see digest). |
| **S1** | **if-on-the-answer reduction** `FlatSingleTMGenNP ⪯p FlatTCC` — map is `if (source is yes-inst) then yesInst else noInst`; output depends on the *answer*. Deepest unsoundness. | `Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`, `.../TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean` | The real **Cook 2D tableau** (`Simulators/CookTableau.lean`). **Probed: feasible but expensive (~6–11K LOC, bijection-dominated).** Gated on S3 (dead until then). |
| **S2** | **dummy TM bridges** — `bridgeMachine` is a 1-state TM that discards the source `M`; `TMGenNP_fixed`/`mTMGenNP_fixed` ignore `M`. The `GenNP→TMGenNP` arrow carries no content. | `LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean`, `TMGenNP_fixed_mTM.lean` | **Probed: do NOT build a multi-tape→single-tape simulator** (`MultiToSingle.lean` is a Coq-porting orphan; `TM σ n` erases the tape count, the predicates ignore `M`). Real fix = collapse the phantom bridges and bind the `*GenNP_fixed` predicates to the **single-tape layer decider** — i.e. this folds into the **C8** work, single-tape throughout. Gated on S3. See the S2 digest. |
| **S4** | **orphan constructions.** `cookTableau` (real, 2 `sorry`s) is referenced by no reduction — wire it into S1 (after S3). `multiToSingle` (stub, 3 `sorry`s) is **dead code** per the S2 probe → park/delete, do not complete. | `Simulators/CookTableau.lean`, `Simulators/MultiToSingle.lean` | Wiring `cookTableau` into S1 (after S3). `multiToSingle` is not on any honest path. |

**Companion (Part 0.1) — now a hard requirement (per S3 probe).**
`instEncodableDefault` (`Definitions.lean`) gives `size = 0` to any type
lacking an explicit `encodable` instance. Over a size-0 type even the real
`toFrameworkWitness'` is **vacuous** (the polynomial bound is `≤ bound 0`),
so retiring S3 in earnest requires real `encodable.size` instances on
*every* chain intermediate (TCC/CC/BinaryCC/formula/…). This is no longer a
nicety; it is part of the S3 migration cost.

### Group C — completion risks (the compiling skeleton)

C1–C4 are **structural** (validate the pivot / change downstream
signatures); C5–C6 are **design**; C7–C8 are **engineering** gated on the
above.

| # | Gap | Status |
|---|-----|--------|
| **C4** | **layer → framework bridge** (`Lang/PolyTime.lean`'s 4 bridges, `NP.lean`'s `red_inNP`). Same upgrade as **S3**. | **Bridge B validated** (`toFrameworkWitness'`, sorry-free modulo `Compile_sound`). The composition bridges (`comp`, `red_inNP_via_lang`) and `red_inNP` remain `sorry` — blocked on **C9** (canonical encoding), not on Compile_sound. |
| **C9** | **canonical layer encoding** (NEW, surfaced by the S3 probe). `PolyTimeComputableLang.encodeIn`/`decodeOut` are free functions, so `comp`/`red_inNP_via_lang` cannot be stated without an encoding-compatibility bridge. Need a per-type `LangEncodable`-style class (`decode ∘ encode = id`, register-layout lemmas) so composed programs line up. | `Lang/PolyTime.lean` (`comp_computes_of_bridge` isolates exactly what's missing). Bounded design; prerequisite for C4-composition and `red_inNP`. |
| **C1** | **per-`Op` compilation** (`compileOp` + `compileOp_sound`). | ✅ **validated** — reusable gadget library built (`insertCarryTM`, `scan_to_mark`/`scanPastDelimTM`/`scanLeftUntilTM`, `appendAtTM`); `appendOne/Zero` are real `CompiledCmd`s. Remaining: physical `compileOp_sound` per op + the length-decreasing ops (use the `endMark=3` sentinel; see lessons). Bounded eng (~1.5–2.5K LOC for all 8 ops). |
| **C2** | **composition** (`compileSeq_sound`). | ✅ **validated** — `compileSeq_compose_physical` proves fragments compose under the physical contract (halt at `exit`, head rewound to `0`, tape `= encodeTape output`, exact step, no-early-halt). Bounded eng. |
| **C3** | **`loopTM` counted loop** (`compileForBnd` + `_sound`). | ✅ **validated** — `loopTM` + full run lemma `loopTM_run` in `TMPrimitives.lean`, sorry-free, axiom-clean, ~500 LOC. Remaining: a guard + a **marker-overwrite (non-shrinking) decrement** gadget, wire `compileForBnd`, instantiate `loopTM_run`. Bounded eng. |
| **C5** | **DSL expressiveness** — `evalCnfCmd` wanted a guarded loop and a constant-comparison primitive. | Add primitives only when they materially shorten a verifier (each new `Op` = another soundness proof). |
| **C6** | **`compileIfBit` tester** — structure done (`branchComposeFlatTM`+`joinTwoHalts`); the real bit-test + `compileIfBit_sound` remain. | Same flavour as C1. |
| **C7** | **verifier bodies** — `evalCnfCmd` (SAT), `cliqueRelCmd` (`Deciders/`). | DSL engineering; gated on C3+C5 and dead until C4 makes the layer→`DecidesBy` bridge real. |
| **C8** | **real `NPhard_GenNP`** (`hasDeciderClassical`, `GenNP_is_hard.lean`). | Last `sorry`; needs C4 (verifier TM from `InNPWitness`). |

**Standing ranking.** C1/C2/C3, the S3 bridge (B), and now the S2 question
are all resolved. The S2 probe **removed** the last unprobed structural
cost: the multi-tape simulator is not needed (Coq-porting artifact), so
**no unprobed structural unknown remains** — every gap is now either
validated or bounded engineering. The one new design item is **C9
(canonical layer encoding)**, the prerequisite for layer-level composition
(`comp`, `red_inNP_via_lang`, `red_inNP`); bounded *design*, not research.
**Next topic: C9**, then execute the S3 migration (its ripple is the
remaining large-but-bounded engineering).

---

## Strategic situation: two end-states

There are two honest destinations. The S3 + S2 probes have decided the
structural questions; the call is now about engineering appetite.

1. **Real, unconditional `CookLevin`.** Requires, in order:
   (a) **retire S3** (TM-back `polyTimeComputable`) — the gate (probed
       feasible; needs **C9** then the migration);
   (b) finish the layer: `Compile_sound` (C1 ops + C3 `compileForBnd` +
       C6 tester), then the verifier C7 → `inNP SAT`;
   (c) the real reductions S3 exposes: S1 Cook tableau (~6–11K LOC,
       probed feasible) and C8 (the universal-source decider, single-tape
       via the layer — this also subsumes the old "S2 simulator", which the
       S2 probe showed is *not* needed);
   (d) real `encodable` instances on the chain (Part 0.1).
   Post-C1/C2/C3/S2/S3-bridge, this is mostly *bounded* engineering — the
   only expensive-but-feasible item is the S1 tableau. **No unprobed
   structural unknown remains.**

2. **Honest conditional theorem (fallback).** If retiring S3, or the
   reductions it exposes, prove intractable for a side project: state
   `CookLevin` conditionally on a **documented axiomatic `inTimePoly` /
   `⪯p` interface**, keep the sound combinatorial tail, and stop. The code
   is ~80% there for this scope. Triggered if the S3 probe's verdict is
   (iii), or if Part 3 overruns its estimate ~3×.

**The S3 probe (now complete) made this call: the unconditional path is
open, verdict (ii) feasible-but-expensive.** The witness upgrade and bridge
exist (sorry-free modulo `Compile_sound`) and the forcing function is
confirmed, so destination 1 is reachable; but it is gated on C9 (canonical
encoding) and then a large, partly-unprobed body of engineering (the S2
simulator, the sound-tail `Cmd`s — Tseytin being the expensive one — and
the encodable sweep). The fallback (destination 2) stays the documented
escape hatch if C9 or the tail migration overruns ~3×. See the S3 entry in
*Validated so far* and [`S3_RETIREMENT_EXPLORATION.md`](S3_RETIREMENT_EXPLORATION.md).

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
- **S3 (TM-back `polyTimeComputable`):** **feasible but expensive — proceed
  after a canonical layer encoding.** The probe is additive in
  `Lang/PolyTime.lean` (sorry-free; depends only on the assumed
  `Compile_sound`):
  - *(A) interface* — `ComputesBy` (function analogue of `DecidesBy`) and
    `PolyTimeComputableWitness'`, which **extends** the old size-only
    witness. So `polyTimeComputable' f → polyTimeComputable f`
    (`polyTimeComputable'_to_polyTimeComputable`, axiom-clean): the upgrade
    is a pure *strengthening*, hence every size-bound lemma in `NP.lean`
    (`reducesPolyMO_transitive`, `red_inNP`'s `polyCertRel` half) survives
    the migration verbatim — only witness *construction* gets harder.
  - *(B) bridge* — `PolyTimeComputableLang.toFrameworkWitness'` goes through
    **cleanly** (machine = `Compile W.c`, budget = `Compile.overhead`,
    closed by `Compile_sound` + `runFlatTM_extend` budget-padding + the
    single-tape `initialTapes` collapse). Difficulty was *low*; it is the
    honest version of the faked `toFrameworkWitness`.
  - *(C) composition is where difficulty concentrates,* but it is bounded
    *design*, not a wall. TM-level `ComputesBy` composition needs a
    re-encoding tape (output of `f` → input of `g`); the layer's single
    `State` avoids it (the ROADMAP thesis holds). The residual gap is that
    `PolyTimeComputableLang.encodeIn`/`decodeOut` are **free functions** with
    no shared representation, so `comp`/`red_inNP_via_lang` cannot even be
    *stated* without an encoding-compatibility bridge.
    `comp_computes_of_bridge` proves the rest is definitional
    (`Cmd.eval_seq`) once a `reEncode` Cmd aligns them → **new Risk C9.**
    `red_inNP` therefore cannot be discharged *additively* (it is stated
    over the size-only `⪯p`, which carries no Lang program for the
    reduction); discharging it is part of the migration, gated on C9.
  - *(D) forcing function — CONFIRMED.* The if-on-the-answer S1 map is
    `noncomputable` and branches on the existential NP predicate
    `FlatSingleTMGenNP`; any layer witness computes via the **total
    computable** `Cmd.eval`. `s1_witness_forces_decider` formalizes the
    consequence: a layer witness + a constant-comparison test ⇒ a
    polynomial-cost **decider** for the source predicate — exactly what a
    many-one reduction may not produce. So S1 (and, by the same argument,
    S2's source-discarding bridges) **stop typechecking** under the upgrade.
    The upgrade is real.
  - *(E) migration ripple.* The dominant cost is downstream, not the
    witness: the real S1 tableau (~6–11K LOC, probed) and the unprobed S2
    multi-tape simulator are *rebuilds*, not migrations. The **sound tail**
    must each gain a `Cmd`: `flatTCC_to_flatCC` is a cheap structural map
    (its `if isValidFlattening` guard is a *decidable input* check, not on
    the answer — expressible); `FlatCC_to_BinaryCC` is medium (bit-block
    encode/decode); **`BinaryCC_to_FSAT` (the Tseytin transform, `500n⁶`
    bound) is the expensive tail item** — re-expressing a ~1K-LOC `formula`
    builder as a `Cmd` likely needs new `Op`s (C5). Plus the **encodable
    sweep** (Part 0.1): over a size-0 `instEncodableDefault` type
    `toFrameworkWitness'` is *still vacuous*, so every chain intermediate
    (TCC/CC/BinaryCC/formula/…) needs a real `encodable.size` — now a hard
    requirement, not a nicety.
- **S2 (multi-tape → single-tape simulator):** **do NOT build it — it is a
  Coq-porting artifact with zero footprint in the layer architecture.**
  Evidence is additive and sorry-free in `mTM_to_singleTapeTM.lean`:
  - `TM_tapecount_phantom : TM Bool 2 = TM Bool 1` by **`rfl`** — `TM σ n`
    is `abbrev`-ed to `FlatTM` (`Definitions.lean`), so the tape count is an
    *erased phantom*; there is no multi-tape object to simulate.
  - `bridgeMachine_accepts_any` — the bridge machine accepts **every** valid
    tape config in any budget, so the `acceptsFlatTM bridgeMachine …`
    conjunct the front-chain threads through is a decorative `True`; the
    real content is the abstract relation `inst.source.rel`.
  - `LMGenNP_to_TMGenNP_singleTM_direct` — `LMGenNP` reduces *directly* to
    the single-tape target via a real phantom-free map, **skipping the mTM
    node** (one-step replacement for the live two-step chain). The
    intermediate adds nothing.
  Why it was thought needed: the Coq port extracts *multi-tape* TMs from the
  L-calculus, then converts to single-tape to feed the tableau. The Lean
  pivot replaced L-extraction with the **single-tape** `Cmd` layer
  (`Compile` emits `tapes = 1`) and the universal source's relation already
  carries a single-tape decider (`GenNPInput.rel_poly : inTimePoly rel`),
  so the conversion is structurally unnecessary. **Retiring S2 = collapse
  the phantom bridges + bind the `*GenNP_fixed` predicates to the real
  single-tape layer decider (= the C8 work), NOT build a simulator.**
  `Simulators/MultiToSingle.lean` (the 3-sorry stub) is dead code → park or
  delete; do not complete it.

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
