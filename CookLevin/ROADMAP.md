# Cook–Levin in Lean 4 — Roadmap to a Faithful Proof

This document is a candid assessment of the Lean 4 Cook–Levin
formalisation under `CookLevin/`, together with a phased plan for
turning it into an honest, mathematically rigorous proof.

> **Read [Status update — May 2026](#status-update--may-2026) first.**
> The roadmap was rewritten mid-Part-2 to reflect a strategic pivot
> after the original "hand-roll each verifier as a flat Turing
> machine" approach overran its budget by an order of magnitude. The
> original Parts 2–6 are preserved as
> [Appendix C](#appendix-c--original-parts-26-plan-archival).

---

## Status update — May 2026

### Where we are

| Phase | Description                                                | Status |
|-------|------------------------------------------------------------|--------|
| 1     | Foundational hygiene, small-`sorry` cleanup                | ✅ done |
| 2 (framework) | TM-backed `DecidesBy` + `inTimePoly`               | ✅ done |
| 2 (content)   | Hand-rolled `EvalCnfTM` / `CliqueRelTM` verifiers  | ⏸ paused mid-stream |
| 3–7   | TM-backed reductions, simulators, Cook tableau             | rescoped (see below) |

- Repository size: **~25.7K LOC** of Lean.
- Build state: **`lake build` is green** (3350 jobs), **0 axioms**,
  with **~33 labelled `sorry`s** across the Parts 3–7 skeleton
  ([distribution and ranking](#current-skeleton-state)). The four
  framework-migration `sorry`s ([listed below](#the-four-open-sorrys))
  were decomposed into these when the skeleton was scaffolded.
- `theorem CookLevin : NPcomplete SAT` typechecks against the strengthened
  framework but is **conditional**: it inherits the ~33 `sorry`s, the
  `sorry`-free vacuous reductions/bridges (Risks **S1**/**S2**), the
  `polyTimeComputable` weakness (Risk **S3**), and Part 0.

### Why the pivot

The Part 2 *framework* migration (Steps 1–10 of `PART2.md`) landed
cleanly: `inTimePoly` is now backed by a real `FlatTM`-valued
`DecidesBy` structure, and `sat_NP` / `FlatClique_in_NP` rebuild
against it. That portion of the project is in good shape.

The Part 2 *content* (Step 11 of `PART2.md`: build a real TM that
verifies SAT) blew up dramatically:

| Item                                  | Original estimate | Actual / projected |
|---------------------------------------|-------------------|--------------------|
| Part 2 total                          | ~1,500 LOC        | ~14,500 LOC so far |
| `EvalCnfTM.decider` (closes 1 sorry) | (~600 LOC)        | ~8,100 LOC, ~30% done |
| Remaining Part 2 (Phase G + H)        | —                 | +~7,000 LOC projected |

The cause is structural, not accidental. Building a useful
algorithm out of `FlatTM`s — even via the `composeFlatTM` /
`branchComposeFlatTM` / `loopTM` combinators we developed — requires
per-state step lemmas, phase scan lemmas, and iteration lemmas for
each primitive. Each primitive lands in the 1,000–2,500-LOC range,
and amortisation across primitives is weak.

If the same overrun ratio applies to Parts 3–6 (each of which builds
*more* and *larger* Turing machines than Part 2), the project as
originally scoped projects to **~100,000–150,000 LOC**. That is
multi-year work for a side project and not the right shape of
investment for the mathematics involved: the combinatorial heart of
Cook–Levin (the `FlatTCC → FlatCC → BinaryCC → FSAT` chain) is already
in place at ~3,000 LOC.

The Coq port we are based on side-steps this entire problem by
extracting Turing machines from the L calculus / `computableTime'`
API: programs are written in a higher-level language and a one-time
extractor produces TM code, so each verifier proof is ~50–100 LOC of
L-level code rather than thousands of LOC of TM bookkeeping. Our
original ROADMAP (Part 4.1) explicitly declined to port L. **That
decision was the wrong one, and this revision reverses it.**

### The pivot

Pause the hand-rolled Part 2 finish. Build a small higher-level
computable layer ("the layer") with explicit cost semantics. Define
`inTimePoly` and `polyTimeComputable` through the layer. Pay the
"compile to `FlatTM`" cost *once*; every downstream verifier and
reduction is then a short program in the layer plus a short
correctness proof.

The layer is the new Part 3 of this roadmap. The old Parts 3–6 are
re-cast as content to be built on top of the layer (Parts 4–7).

The 14.5K LOC of existing Part 2 work is **not** wholly thrown away:

- `Complexity/Complexity/TMPrimitives.lean` (~3.5K LOC) — the
  `composeFlatTM` / `branchComposeFlatTM` family and the
  `runFlatTM_compose` / `runFlatTM_extend` machinery is the natural
  glue for the compiler's output. **Keep.**
- `Complexity/Complexity/TMEncoding.lean`, `TMDecider.lean`,
  `NP.lean` framework deltas. **Keep.**
- `Complexity/Complexity/Deciders/EvalCnfTM/Primitives.lean`,
  `CopyUnary.lean`, `CompareUnary.lean` (~8K LOC) —
  hand-rolled SAT-verifier primitives. **Retire.** Replaced by the
  layer.
- `Complexity/Complexity/Deciders/SAT_TM.lean` (~6.3K LOC) — the
  "demonstration deciders" Phase-C work, kept as a pattern library
  but never on the proof path. **Retire** (or relocate to `archive/`).

After the pivot lands, the `EvalCnfTM.decider` and `CliqueRelTM.decider`
sorrys close via the layer, not via hand-rolled `FlatTM`s.

### Fallback

If the pivot itself turns out to be too expensive (the layer
estimate is ~10–20K LOC; if it triples we hit a similar wall), the
fallback is option 3 of the May 2026 strategic review: state
Cook–Levin **conditionally** on a documented TM-construction
interface, treat the construction obligations as `axiom`-level
assumptions, and finish the combinatorial chain only. The current
code is already ~80% there for that scope.

---

## How we work — skeleton-first, risk-driven refinement

See the [`Development strategy`](../README.md#development-strategy-skeleton-first-risk-driven-refinement)
section of the root README for the full principles. The short
version:

- **The skeleton comes first.** The whole proof path compiles —
  with `sorry`s — before any Part is "done". This is already in
  place: see [Current skeleton state](#current-skeleton-state).
- **Refinement is risk-driven, not phase-sequential.** The Parts
  below describe the *target shape* of each area at completion;
  they do **not** prescribe an execution order. The order is
  determined by the [Risk register](#risk-register) — refine the
  highest-risk gap next, regardless of which Part it sits in.
- **Each iteration either validates a piece of the skeleton or
  surfaces a new gap.** Both outcomes are progress. Record gaps in
  the risk register and in commit messages, not in private notes.
- **Prefer concrete `def` + `sorry` over `axiom`.** Axiom count is
  a metric to minimise (see Current skeleton state).
- **Decompose sorrys, don't elaborate them.** Splitting a single
  large sorry into several focused ones is structural progress;
  starting to prove a single sorry without that decomposition risks
  hours of work on the wrong shape.

This methodology emerged from the May 2026 pivot (see
[Why the pivot](#why-the-pivot)). The original ROADMAP described
Parts 1–7 as sequential implementation phases with LOC estimates;
Part 2 blew up ~10× because its proof obligations had structural
issues that weren't visible until they were attempted. Skeleton-
first surfaces those issues before we commit the engineering
hours.

---

## Current skeleton state

Snapshot of where the compiling skeleton stands. **Update on every
iteration.**

| Metric                                | Value             | Trend |
|---------------------------------------|-------------------|-------|
| `lake build`                          | ✅ green (~3350 jobs) | unchanged |
| Axiom count (repo-wide)               | **0**             | unchanged |
| `sorry`s on the proof path            | **~33**           | ↓ −1: `decodeTape_encodeTape` proved (C1 step 1); prior "~26" had undercounted |
| Sorry-**free** vacuous defs on the proof path | **≥ 4**   | newly tracked — see Risk **S1**/**S2** |
| `theorem CookLevin : NPcomplete SAT` | typechecks, **conditional** on all of the above | unchanged since pre-pivot |

> **Sorry count is not the soundness metric (review note, May 2026).**
> The headline number on this row was stale (`~26`) and even its own
> per-file table summed to 32. The accurate count was ~34 at the
> audit (now ~33: C1 step 1 closed `decodeTape_encodeTape`). More
> importantly, the count is a *misleading* progress signal: the
> deepest unsoundness in the development is **sorry-free** (the
> `if-on-the-answer` reductions and dummy bridges of Risks S1/S2),
> so it does not appear here and does not show up under
> `#print axioms`. Track the soundness risks (Group S) separately
> from the completion risks (Group C); closing every `sorry` does
> **not** by itself make `CookLevin` unconditional.

Sorry distribution at the current snapshot (May 2026, recounted):

| File                                       | Sorrys | What they are |
|--------------------------------------------|--------|---------------|
| `Lang/Compile.lean`                        | 6      | `compileOp_sound`, `compileSeq_sound`, `compileIfBit_sound`, `compileForBnd_sound`, `Compile_sound`, `Compile_polyBound` (`decodeTape_encodeTape` ✅ proved, C1 step 1) |
| `Lang/PolyTime.lean`                       | 4      | `DecidesLang.toDecidesBy`, `inTimePolyLang_to_inTimePoly`, `PolyTimeComputableLang.comp`, `red_inNP_via_lang` |
| `Complexity/NP.lean`                       | 1      | `red_inNP` TM-composition |
| `GenNP_is_hard.lean`                       | 1      | `hasDeciderClassical` |
| `Deciders/EvalCnfCmd.lean`                 | 7      | `processOneClause`/`processOneLiteral`/`memberCheck` (sorry-typed `def`s) + `encodeCnf_length` + `encodeState_size_bound` + `evalCnfCmd_decides` + `evalCnfCmd_cost_bound` |
| `Deciders/CliqueRelTM.lean`                | **5**  | sorry-typed `cliqueRelCmd` + `cliqueRelEncode` **defs**, plus `encodeIn_size` + `decides` + `cost_bound` (prior snapshot said 3) |
| `Deciders/EvalCnfTM.lean`                  | 1      | `encodeIn_size` (`5·n + 20 ≤ (n+1)^3`) |
| `Simulators/CookTableau.lean`              | 5      | wellformedness + bijection + size bound — **but this file is an orphan (Risk S4)** |
| `Simulators/MultiToSingle.lean`            | 3      | step-bound poly/mono + acceptance — **orphan (Risk S4)** |

---

## Risk register

**Rewritten May 2026 after a structural review** (see the iteration
log entry "Risk register audit"). The previous register tracked only
the compiler-skeleton sorrys and mis-located two items at orphan
files. It is split into two groups:

- **Group S — soundness gaps.** These determine *what the
  conditional `CookLevin` theorem currently means*. Several are
  **sorry-free** and therefore were invisible to the old register and
  to `#print axioms`. **Closing every Group C sorry does not close
  these.** They do not "drop off" by refinement of the layer; each
  needs the listed reduction/bridge to be rebuilt against real
  content.
- **Group C — completion risks.** The compiling-skeleton gaps,
  ranked by **structural risk** (impact × likelihood-of-surfacing-a-
  gap). **Refine the highest-ranked C item first.**

### Group S — soundness gaps (on the proof path; mostly sorry-free)

| # | Gap | Location | Why it matters |
|---|-----|----------|----------------|
| **S1** | **`if-on-the-answer` reductions** | `…/Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`, `…/Reductions/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean` | Both reduction maps are `noncomputable def … := if Source inst then yesInst else noInst` — the image depends on the *truth* of the source predicate, which is exactly what a many-one reduction may not do. They are **sorry-free**, so they never show up in the sorry count or in `#print axioms`; they typecheck only because of S3. This is the **deepest unsoundness in the project** and was entirely absent from the old register. A real `FlatSingleTMGenNP ⪯p FlatTCC` requires the Cook tableau (a *function* of `(M, s, steps)` that encodes the TM run), i.e. the construction that `Simulators/CookTableau.lean` aspires to (S4). |
| **S2** | **Dummy bridge machines** | `LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean`, `TMGenNP_fixed_mTM.lean` | `bridgeMachine` is a 1-state TM that **discards the source machine `M`** and accepts via an empty/erased tape; `TMGenNP_fixed`/`mTMGenNP_fixed` are predicates that ignore `M`. These are reached on the path via `GenNP_to_TMGenNP` (`NP/TM/IntermediateProblems.lean`), so the `GenNP → TMGenNP_fixed` arrow carries no computational content. Sorry-free; invisible to the sorry count. |
| **S3** | **`polyTimeComputable` bounds output size only** | `Complexity/Definitions.lean`, `Complexity/NP.lean` | `PolyTimeComputableWitness f` requires only `encodable.size (f x) ≤ bound (size x)`; it says nothing about a TM computing `f`. This is the **enabling weakness** that lets S1/S2 typecheck as "polynomial-time reductions." Until it is upgraded to carry a real (layer-backed) computation, no `⪯p` arrow on the `GenNP → FlatTCC` segment is real. (Cf. Part 0.1 and `instEncodableDefault`'s `size = 0` loophole, which combines with this for the bridge-stage types.) |
| **S4** | **The "real" Part 5/6 constructions are orphans** | `Simulators/CookTableau.lean`, `Simulators/MultiToSingle.lean` | `cookTableau` and `multiToSingle` are compiled (imported by the `Complexity.Simulators` aggregator) but **referenced by no reduction** — `grep` finds zero uses outside their own files. Proving their 8 sorrys advances `CookLevin` by **zero** until S1/S2 are rewired to call them *and* the abstract-source-TM → `FlatTM` bridge exists. The old register's items #4/#5 pointed here, which created a false impression that proving those sorrys would close the corresponding soundness gap. |

**Implication for the headline.** Today `CookLevin` is conditional on
{four `sorry`s on the verifier/hardness side} **and** {S1, S2, S3 on
the reduction side}. The fallback in the [Fallback plan](#fallback-plan-if-the-layer-also-overruns) makes this
honest by stating the `inTimePoly`/reduction obligations as explicit
axioms; if the layer (Group C) does not converge, S1–S3 are the
obligations that move into that axiom interface.

### Group C — completion risks (compiling skeleton)

| # | Gap | Location | Why this ranking |
|---|-----|----------|------------------|
| **C1** | **Concretize one primitive `Op` end-to-end** (def **and** its slice of `compileOp_sound`) | `Lang/Compile.lean` | **Highest-information action available.** The entire pivot rests on the premise that primitives are "~50 LOC each" (Part 3.3). The Part-2 empirical datum is **1,000–2,500 LOC per primitive TM** (Appendix A, points 1–2). These cannot both hold. The layer amortises *composition* (`compileSeq`/`compileIfBit` discharge cheaply) but **not** the per-primitive operational proof, which is precisely what blew up. Pick the simplest op (`opNonEmpty` or `opHead`: read one cell, write one bit) and prove `compileOp_sound` for it. If that proof is small, the pivot premise holds and the rest of `compileOp` is bounded engineering; if it balloons, the premise is **falsified now** and the [Fallback plan](#fallback-plan-if-the-layer-also-overruns) (axiomatic `inTimePoly`) should trigger before more skeleton is built. The old register never prioritised this — it kept decomposing compiler *structure*, which validates nothing about the expensive part. |
| **C2** | **`compileSeq_sound` operational composition** | `Lang/Compile.lean` | `compileSeq` composes via `composeFlatTM`, which **resumes M₂ on M₁'s halting configuration**; but the soundness hypotheses (`h2`) bound M₂ when started from `initFlatConfig` — head at cell 0, fresh tape framing. Unless every compiled fragment **resets the head to 0** before halting (a new `CompiledCmd` invariant), the resume point does not match the hypothesis. This is **distinct** from the halt-uniqueness gap that risk 1d resolved; it is currently buried inside the single `compileSeq_sound` sorry and is the real obstacle there. |
| **C3** | **`loopTM` combinator + its run lemma** | `Complexity/TMPrimitives.lean`, `Lang/Compile.lean` | `compileForBnd` is a `compiledCmd_default` stub; `loopTM` is absent from `TMPrimitives`. The *combinator* is routine; the **run lemma** (iteration bookkeeping: threading tape state through the counter, post-loop cleanup) is, per Appendix A point 2, the **dominant cost** (~600 + ~400 LOC per loop site). Single-tape unary counter is the preferred design but unvalidated. Closely coupled to C1 (the loop body invokes compiled primitives). |
| **C4** | **`PolyTimeComputableLang` ↔ framework** | `Lang/PolyTime.lean`, `Complexity/NP.lean` | `polyTimeComputable` carries no Lang witness, so `red_inNP` (the `NP.lean` sorry) cannot compose at the layer level. Requires upgrading `PolyTimeComputableWitness` (or adding a parallel TM-backed witness and migrating). **This is also the structural change that begins to retire S3** — the same upgrade that lets `red_inNP` compose is what lets the chain's reductions stop relying on the size-only bound. |
| **C5** | **DSL expressiveness — missing primitives** | `Lang/Syntax.lean` | Writing `evalCnfCmd` surfaced two needs: no guarded loop (`Cmd.while`) and no constant-comparison primitive (`Op.headEqVal`). Decide their type/cost shapes before C7, or that work is redone. **Note the tension with C1/C3:** every new `Op` is another per-primitive soundness proof, so add primitives only when they materially shorten the verifiers. |
| **C6** | **`compileIfBit` tester logic** | `Lang/Compile.lean` | Structure is done (`branchComposeFlatTM` + `joinTwoHalts`, all seven invariants discharge). `branchTester_default` is a no-op 2-state stub; the remaining work is the real bit-test (read register `t`'s first symbol, dispatch to `exitPos`/`exitNeg`) plus `compileIfBit_sound`. Same primitive-proof flavour as C1. |
| **C7** | **`evalCnfCmd` / `cliqueRelCmd` bodies** | `Deciders/EvalCnfCmd.lean`, `Deciders/CliqueRelTM.lean` | Per-clause/per-literal/member-check (`evalCnfCmd`) and the whole `cliqueRelCmd`/`cliqueRelEncode` (still sorry-typed `def`s) are DSL-engineering. Mostly mechanical, but each may surface another C5 gap. **Wait for C5**, and note this is dead until C1–C4 make the layer→`DecidesBy` bridge real (otherwise the DSL programs decide nothing at the TM level). |
| **C8** | **`hasDeciderClassical`** | `GenNP_is_hard.lean` | The `NPhard_GenNP` hardness sorry. Its signature is currently too strong (a decider for *any* predicate). Tractable once C4 lands and the verifier TM can be drawn from `InNPWitness`. Last sorry to close. |

**Risk grading convention.** Group S items are **soundness**: they do
not validate-and-drop by refinement; each is closed only by replacing
a specific reduction/bridge with real content (or by moving it into
the documented axiom interface of the [Fallback plan](#fallback-plan-if-the-layer-also-overruns)). Within Group
C, **C1–C4 are structural** (they validate the pivot premise or
change downstream type signatures), **C5–C6 are design**, and
**C7–C8 are engineering** that is gated on the structural items above.

**The single most important next step** is **C1**: it is the cheapest
experiment that can falsify the pivot's central assumption, and the
methodology (surface structural gaps *early*) demands running it
before investing further in the skeleton.

#### C1 progress + interim measurement (May 2026)

Step 1 of C1 is **done**: the decoder round-trip
(`decodeTape_encodeTape`) is proved and a real bug was fixed along the
way (`flattenTape` spliced the head *index* into the tape contents).
This measures the **infrastructure** cost of a primitive's soundness:
~120 LOC of short structural inductions. Cheap. ✅

Working out the rest of one primitive's TM surfaced a sharper model of
the per-`Op` cost than "1,000–2,500 LOC each":

- **Navigation amortises.** Reaching register `dst` is "scan right to
  the next `0` delimiter, step past it" repeated `dst` times (`dst` is
  a compile-time constant). This **reuses the existing
  `scanRightUntilTM` + its run lemmas** (`scanRightUntilTM_run_found`)
  composed via `composeFlatTM_run` — *not* fresh work per op. This is
  a genuine win over hand-rolled Part 2, where nothing amortised.
- **The data-movement loop does not.** Every `Op` writes a register
  whose length changes (`clear` deletes, `appendOne/Zero` insert one
  cell, `copy/tail/head/eqBit/nonEmpty` overwrite with a different
  length), so each needs a bespoke single-tape **shift/carry loop**
  (carry a symbol in the finite state, march down the tape) with its
  own run-lemma induction over the tape suffix length. **No `Op` is
  shift-free for general `dst`.** (Special case: appending to the
  *last* register is shift-free — scan to end, overwrite the final
  delimiter, re-emit it — but that does not generalise.)

**Revised estimate.** Per `Op`: navigation ≈ free (reused) + a bespoke
data loop ≈ 200–500 LOC (def + per-state step lemmas + the shift
induction + assembly). Across the 8 `Op`s, `compileOp` alone is
plausibly **~2–4K LOC** — i.e. it consumes most of Part 3.3's ~5K-LOC
budget, and Part 3.3 was the cheapest of the layer parts. So the pivot
premise ("primitives are ~50 LOC each") is **partly falsified**: the
layer amortises *navigation and composition*, but the per-primitive
data-movement proof is real and is where the cost now sits.

**Decision point (for the next iteration / project owner).** Three
options, in increasing radicalism:
1. **Push through the 8 primitive proofs.** ~2–4K LOC, mechanical once
   the first shift-loop run lemma is built (it is reusable across the
   insert/delete/overwrite ops). Build one shared `shiftTape` /
   `carryRight` combinator + run lemma, then each `Op` is assembly.
2. **Change the encoding to one tape per register** (multi-tape
   layer). Then every `Op` is O(1) head moves — primitives become
   genuinely ~50 LOC — but composition needs the multi-tape simulator
   (Part 5 / Risk S4-area) and `branchComposeFlatTM`'s `(sig+1)^k`
   bridge-entry blow-up (Appendix A point 4). Trades per-op cost for
   composition cost.
3. **Trigger the [Fallback plan](#fallback-plan-if-the-layer-also-overruns).**
   If neither the ~2–4K-LOC `compileOp` nor the encoding change is
   worth it, state `inTimePoly` axiomatically and keep the
   combinatorial chain.

Recommended: build the **shared `shiftTape` run lemma first** (option
1's reusable core); its size is the real go/no-go signal — if *that*
one lemma balloons past ~500 LOC, prefer option 3.

##### Go/no-go result: **GREEN** (May 2026)

Built `Lang/ShiftTape.lean`: `insertCarryTM` (the single-tape
"insert one symbol, carry the rest right" gadget, alphabet fixed at
`sig = 3`) with full validity and the headline run lemma
`insertCarryTM_run` — *sorry-free*, **~200 LOC** total (well under the
500-LOC threshold). The reusable core is `insertCarryTM_run`:

```
runFlatTM (suf.length + 1) (insertCarryTM ins)
    { state_idx := 0, tapes := [([], pre.length, pre ++ suf)] }
  = some { state_idx := 4,
           tapes := [([], pre.length + suf.length, pre ++ ins :: suf)] }
```

i.e. from the head at `pre.length`, insert `ins` and shift `suf` right
in `|suf| + 1` steps. **Decision: proceed with option 1.**

Key techniques that kept it small (reusable for every other `Op`):
- **`simp` computes `find?` over the concrete transition table.** With
  the alphabet fixed at 3 and the current symbol case-split to a
  literal, each per-state step lemma
  (`insertCarryTM_step_nonblank` / `_blank`) is ~15 LOC via
  `interval_cases <;> simp_all [stepFlatTM, …]` — *no* hand-rolled
  `find?`-peeling à la `scanRightUntilTM` (which was ~40 LOC/step).
- **One `run_succ_of_step` unfolder** + a clean induction on the tape
  suffix (carrying value lives in the state; `interval_cases` the
  symbol where a literal is needed) gives the run lemma in ~50 LOC.

What this unblocks / what remains for `compileOp`:
- `appendOne` / `appendZero` (insert at the end of register `dst`):
  navigate to `dst`'s delimiter (reuse `scanRightUntilTM`), then
  `insertCarryTM_run`. Should now be assembly + a navigation lemma.
- Overwrite ops (`copy/tail/head/eqBit/nonEmpty`) and `clear` were
  expected to reuse a **companion delete/shift-left gadget** — but see
  the [tape-model finding](#go-stop-result-length-decreasing-ops-hit-a-tape-model-wall-may-2026)
  below: a naïve delete gadget is **not sound** under the current
  encoding. Resolving that is now the gating decision for half of
  `compileOp`.
- Revised `compileOp` estimate drops from ~2–4K LOC toward **~1.5–2K
  LOC** (two ~200-LOC shift gadgets + ~8 short per-`Op` assemblies +
  the `scanRightUntilTM`-based navigation lemma).

##### Navigation atom built (May 2026)

`Lang/Navigate.lean` adds `scan_to_delim` — *sorry-free*, ~40 LOC of
proof — the encoding-aware specialization of `scanRightUntilTM_run_found`:

```
runFlatTM (reg.length + 1) (scanRightUntilTM 3 0)
    { state_idx := 0, tapes := [([], pre.length, pre ++ reg ++ 0 :: post)] }
  = some { state_idx := 1,
           tapes := [([], pre.length + reg.length, pre ++ reg ++ 0 :: post)] }
```

i.e. scanning right for the delimiter `0` from the start of a register's
shifted content (`reg` is delimiter-free and in-range) lands exactly on
that register's terminating delimiter. This is the reusable navigation
atom: chained `dst` times (`dst` is a compile-time constant) it locates
register `dst` for *any* `Op`. It is independent of the tape-model
question below, so it is sound to keep regardless of how that resolves.
The two remaining mechanisms for `appendOne`/`appendZero` end-to-end are
(a) the **scan trajectory lemma** (intermediate scan configs stay in
state 0 — needed to discharge `composeFlatTM_run`'s `h_traj1`), and
(b) the **padding/empty case** (`dst ≥ s.length`: `State.set` pads with
empty registers, so the gadget must append delimiters + content at the
tape end). Both only *grow* the tape, so they are compatible with the
model — unlike the delete path.

##### Go/STOP result: length-decreasing ops hit a tape-model wall (May 2026)

Designing the "companion delete/shift-left gadget" surfaced a **genuine
architectural gap**, exactly the kind C1 exists to catch. Reading the
model (`MachineSemantics.lean`): `writeCurrentTapeSymbol` only ever
*replaces in place* or *appends* (`right.take head ++ … ` or
`right ++ …`), and `moveTapeHead` never touches `right`. **The tape
content `right` is monotonically non-shrinking** for every config
reachable from `initFlatConfig`.

Consequence for length-*decreasing* `Op`s (`clear`, `tail`, and
`copy/head/eqBit/nonEmpty` when they shorten a register):

- A delete-shift-left can only shift the tail left; it **cannot drop the
  now-redundant final cell**. So after deleting `k` cells the tape is
  `encodeTape(result) ++ [0,…,0]` (`k` trailing junk delimiters), never
  `encodeTape(result)` exactly.
- Under the current decode (`splitOnZero` then drop **one** trailing
  empty), those trailing junk `0`s become **spurious empty registers**,
  so `decodeTape cfg ≠ Op.eval o s`. And the junk is **indistinguishable
  from a legitimate trailing empty register** (e.g. one produced by
  `State.set`'s padding): both are encoded as a trailing `0`. **No
  flat-level decode rule can both preserve legit trailing empties and
  discard delete junk** — they are the same bytes.

So the originally-planned delete gadget is *not* a drop-in mirror of
`insertCarryTM` under exact-equality soundness. The **insert/append path
is unaffected** (it produces `encodeTape(result)` exactly, no junk), so
`appendOne`/`appendZero` remain fully viable; the wall is specific to
length-decreasing ops.

**Resolution fork.** Three sound options (a fourth, decode-by-head-
position, is a non-starter: gadgets like `insertCarryTM` leave the head
mid-tape, not at the logical end).

- **(A) End-of-tape sentinel.** Bump the alphabet to `sig = 4` with a
  dedicated terminator symbol `3` (`0`=delim, `1`/`2`=shifted bits,
  `3`=end). `encodeTape s := … ++ [3]`; `decodeTape` reads up to the
  first `3`. Delete shifts left and rewrites `3` one cell earlier;
  everything past it is ignored. The terminator is a *distinct,
  detectable* symbol, so gadgets navigate by "scan for `0`, or stop at
  `3`" and **never read junk as content** — the terminator *firewalls*
  the junk. *Exact, unconditional* equality is recovered, including the
  padding case (`dst ≥ length`: scan to `3`, insert delimiters+content
  before it). Cost: re-engineer `encodeTape`/`decodeTape` + re-prove the
  round-trip, and generalize `insertCarryTM` to `sig = 4` (one more
  carry state; the `interval_cases <;> simp` technique scales). All
  front-loaded and mechanical.
- **(B) Normalize + soundness up to trailing-empties.** Change
  `dropTrailingEmpty` to drop **all** trailing empty registers, and
  weaken every soundness statement to equality **up to trailing empty
  registers** (`≈`). Keeps `sig = 3` and reuses `insertCarryTM` as-is,
  and the delete gadget becomes the ~200-LOC mirror — but the cost is
  **pervasive and downstream**: (i) an `≈` relation threaded through
  `compileOp_sound`/`compileSeq_sound`/`Compile_sound` and every
  verifier proof; (ii) a register-pre-allocation invariant (`dst,src <
  length`) to stop navigation miscounting junk `0`s as delimiters —
  cheap to thread since `Op.eval` only grows `length`, but still extra;
  and, decisively, (iii) **TM-tape junk-invariance lemmas**: `compileSeq`
  physically runs `c₂`'s TM on `c₁`'s *junk-bearing* output tape (no
  re-encoding in between), so each gadget must be proved to behave
  identically with trailing junk present. (iii) grows with the layer and
  is exactly the kind of friction the layer was meant to eliminate.
- **(C) Multi-tape (one tape per register).** Ops become `O(1)` head
  moves — no shift loops, no navigation counting, deletion is local —
  so primitives become genuinely ~50 LOC. But the layer must then
  compile to a *multi-tape* `FlatTM` and a **multi-tape → single-tape
  simulator** (currently the orphaned `Simulators/MultiToSingle.lean`,
  Risk S4) is required to plug into the single-tape framework, plus
  `branchComposeFlatTM`'s `(sig+1)^k` bridge blow-up (Appendix A pt 4).
  Trades bounded per-op cost for a large, unbuilt, risky simulator.
  Textbook-clean end state, wrong near-term bet.

**Recommended: (A).** The layer's entire value proposition is making the
~10K-LOC downstream (Parts 4–7 verifier/reduction proofs) cheap and
*clean*. (A) keeps every downstream lemma **exact and unconditional**;
(B) injects `≈`-congruences, register-count invariants, and per-gadget
junk-invariance into exactly that bulk. For a proof at risk of non-
completion, minimizing friction in the bulk dominates minimizing a
bounded one-time refactor. (A)'s upfront cost is bounded and reuses
established techniques; (B)'s cost is unbounded and spreads through the
part of the proof that is supposed to amortise. (C) is the clean end
state but its simulator is unbuilt and risky. The sentinel is also the
standard device (an explicit blank symbol) and benefits every later
gadget (`loopTM`, the `compileIfBit` tester) that needs a detectable
end-of-tape. Confirm before executing, since (A) re-touches the proven
`decodeTape_encodeTape` and `insertCarryTM`.

**Execution order for (A)** (each step bounded, build green between):
1. ✅ **Done.** `encodeTape`/`decodeTape` + terminator (`endMark = 3`)
   + re-proved round-trip (now requires `Compile.BitState`).
2. ✅ **Done.** Generalized `insertCarryTM` to `sig = 4` (extra carry
   state for the terminator); re-proved validity/step/run, *sorry-free*.
   Bumped `CompiledCmd.M_sig`/`Compile_sig`/defaults and `scan_to_delim`
   to `sig = 4`. Full `Complexity.Lang` build green.
3. ✅ **Done.** Generalized navigation to `scan_to_mark` (parametric
   target); `scan_to_delim` (marker `0`) and `scan_to_end` (marker `3`,
   for the padding branch) fall out as corollaries. All *sorry-free*.
4. `appendOne`/`appendZero` end-to-end (unconditional, exact) — also
   validates the `composeFlatTM_run` gluing. **In progress:**
   - ✅ Scan-trajectory lemmas (`Navigate.scan_traj`,
     `scan_no_early_halt`, `scan_to_mark_traj`): intermediate scan configs
     stay in the non-halting state `0`, the exact `h_traj1` shape
     `composeFlatTM_run` needs. Refactored out `scan_block_before` (shared
     in-range/≠-target obligation). All *sorry-free*.
   - ✅ `AppendGadget.scan_then_insert_run`: the scan-to-delimiter ⨾
     insert composition for **register 0** (`composeFlatTM (scanRightUntilTM
     4 0) (insertCarryTM ins) 1`), via `composeFlatTM_run` — the first
     composition-spine exercise in the layer. *Sorry-free.*
   - ✅ `ScanPast.scanPastDelimTM`: the navigation primitive for `dst > 0`
     — a one-symbol variant of `scanRightUntilTM` that steps one cell
     *past* the delimiter (valid + step + run + trajectory +
     `no_early_halt`, all *sorry-free*). This lets the per-`Op` machines
     **recurse on `dst`**: `appendAt (d+1) = composeFlatTM (scanPastDelimTM
     4 0) (appendAt d) 1`, where the recursive machine is always `M₂`, so
     only the small fixed `scanPastDelimTM`'s trajectory is ever needed
     (no parametric-state `find?` reasoning required).
   - ✅ `AppendGadget.appendAtTM` + `appendAt_run`: the general-`dst`
     machine `appendAtTM ins dst` (recursion: `appendAtTM ins (d+1) =
     composeFlatTM (scanPastDelimTM 4 0) (appendAtTM ins d) 1`) and its run
     lemma by induction on `dst` (base = `scanInsert_run`, step =
     `composeFlatTM_run` with `M₁ = scanPastDelimTM`). Proves the **full
     `appendOne`/`appendZero` tape transformation for arbitrary register
     `dst`**: `pre ++ regBlocks skipped ++ body ++ 0 :: post ↦ pre ++
     regBlocks skipped ++ body ++ ins :: 0 :: post`. Axiom-clean
     (`propext`/`Classical.choice`/`Quot.sound` only), *sorry-free*. Step
     count, exit state and final head are existential (a step *bound* is a
     separate concern — item (d)).
   - ⏳ **Remaining:** (b) the decode
     round-trip
     `decodeTape (final cfg) = Op.eval (appendOne dst) s` relating
     `body = shiftReg rₔₛₜ` / `0 :: post` to `encodeTape (s.set …)` under
     `BitState`; (c) packaging the composition as a `CompiledCmd` (7
     invariants discharge from `composeFlatTM_*` since the inserter has a
     unique halt at state 5); (d) the cost bound (steps ≤
     `overhead (size s + 1)`); (e) **threading `BitState s` as a hypothesis
     of `compileOp_sound`** (the round-trip needs it) — a signature change
     that ripples to `compileSeq_sound` / `Compile_sound`.
5. Delete gadget (`sig = 4` mirror of `insertCarryTM`) + the
   length-decreasing ops.

### Iteration log

- **May 2026 — C1 option A, step 4 (cont.): general-`dst` append run
  lemma (`appendAt_run`).** Added to `Lang/AppendGadget.lean`: the
  arbitrary-prefix `scanInsert_run` (generalizing `scan_then_insert_run`
  off register 0), the navigation wrapper `scanPast_block`, the encoded
  register-prefix helper `regBlocks` (+ `regBlocks_cons`/`regBlocks_lt`),
  the recursive machine `appendAtTM ins dst` (`appendAtTM ins (d+1) =
  composeFlatTM (scanPastDelimTM 4 0) (appendAtTM ins d) 1`) with its
  `tapes`/`sig`/`start`/`valid` facts, and the headline `appendAt_run` —
  the full `appendOne`/`appendZero` tape transformation for **arbitrary
  register `dst`**, by induction on `dst` (base = `scanInsert_run`, step =
  one `composeFlatTM_run` with `M₁ = scanPastDelimTM`, so only the small
  fixed scanner's trajectory is needed). The recursion peels one register
  per step into the prefix `pre`; `composeFlatTM`'s state/tape/head
  threading is reconciled via `appendAtTM_start`/length rewrites. The step
  count/exit state/final head are existential (a step *bound* is deferred
  to the cost item). Axiom-clean, *sorry-free*; full build green; layer
  axiom-free. Next: decode round-trip + `CompiledCmd` packaging + cost
  bound + `BitState` threading to finish the `compileOp_sound` slice.

- **May 2026 — C1 option A, step 4 (cont.): `scanPastDelimTM` navigation
  primitive for general `dst`.** Added `Lang/ScanPast.lean` with
  `scanPastDelimTM sig target` — a one-symbol variant of
  `scanRightUntilTM` whose found-transition does `Rmove` (step one cell
  *past* the marker) instead of `Nmove` (halt *on* it). Proved validity,
  the step lemmas (`step_found`, `step_advance`), the run lemma
  (`scanPastDelim_run`: scan a marker-free block and step past, halting in
  state `1` one cell past the delimiter), the trajectory
  (`scanPastDelim_traj`), and the `composeFlatTM_run`-shaped `h_traj1`
  wrapper (`scanPastDelim_no_early_halt`), all *sorry-free*, mirroring the
  proven `scanRightUntilTM` lemmas. This is the navigation step that lets
  the per-`Op` machines recurse on `dst` with the recursive machine always
  in the `M₂` slot — sidestepping any parametric-state `find?` proof. Full
  build green; layer axiom-free. Next: the `appendAt` recursion + run
  lemma (induction on `dst`).

- **May 2026 — C1 option A, step 4 (partial): scan-trajectory lemmas +
  first composition-spine exercise.** Added the scan-trajectory
  infrastructure to `Lang/Navigate.lean`: `scan_traj` (every intermediate
  right-scan config is in the non-halting state `0` with the head advanced
  by exactly the step count, proved by induction via the public
  `runFlatTM_extend_by_step` + `scanRightUntilTM_step_advance`),
  `scan_no_early_halt` (the same fact packaged in `composeFlatTM_run`'s
  `h_traj1` shape: never reaches the accept state `1`, never halts), and
  `scan_to_mark_traj` (the `h_traj1` for the standard `pre ++ body ++
  target :: post` layout). Refactored the shared in-range/≠-target
  obligation out of `scan_to_mark` into `scan_block_before`. Then added
  `Lang/AppendGadget.lean` with `scan_then_insert_run`: the
  scan-to-delimiter ⨾ insert composition for register 0
  (`composeFlatTM (scanRightUntilTM 4 0) (insertCarryTM ins) 1`), the
  **first `composeFlatTM_run` gluing in the layer**, inserting `ins`
  (`2 = appendOne`, `1 = appendZero`) before register 0's delimiter:
  `body ++ 0 :: post ↦ body ++ ins :: 0 :: post`. All *sorry-free*; full
  build green; layer axiom-free. Remaining for the `compileOp_sound` slice:
  delimiter-counting navigator for `dst > 0`, the decode round-trip,
  `CompiledCmd` packaging, the cost bound, and threading `BitState` as a
  `compileOp_sound` hypothesis (see the execution order, step 4).

- **May 2026 — C1 option A, steps 1–2: end-of-tape terminator +
  `sig = 4` gadget.** Owner chose the **sentinel** resolution. Step 1:
  reworked `encodeTape`/`decodeTape` to use a reserved terminator
  (`Compile.endMark = 3`) — encode appends it, decode reads up to the
  first one — and re-proved `decodeTape_encodeTape` (now requires
  `Compile.BitState`, since shifted bits `{1,2}` must stay disjoint
  from `3`). Step 2: generalized `insertCarryTM` from `sig = 3` to
  `sig = 4` (one more carry state, so it can shift the terminator),
  re-proved validity/step/run *sorry-free* (the heavy 20-case step
  lemma needs a raised `maxHeartbeats`); bumped `CompiledCmd.M_sig`,
  `Compile_sig`, the default machines, and `scan_to_delim` to `sig = 4`.
  Step 3: generalized navigation to `scan_to_mark` (parametric target),
  with `scan_to_delim` (marker `0`) and `scan_to_end` (marker `3`, the
  padding-branch navigator) as corollaries, all *sorry-free*. Full
  `Complexity.Lang` build green; layer still axiom-free. Next: step 4
  (`appendOne` end-to-end + the scan-trajectory lemma for the
  `composeFlatTM_run` gluing).

- **May 2026 — C1: navigation atom built + length-decreasing ops
  blocked (architectural finding).** Added `Lang/Navigate.lean` with
  `scan_to_delim` (*sorry-free*, ~40 LOC): scanning for the `0`
  delimiter from a register's start lands on that register's
  terminating delimiter — the reusable navigation atom for locating
  register `dst`, built on `scanRightUntilTM_run_found`. While
  designing the planned delete/shift-left companion, found a **genuine
  tape-model wall**: `writeCurrentTapeSymbol`/`moveTapeHead` never
  shrink the tape content, so length-*decreasing* `Op`s
  (`clear/tail/...`) cannot produce `encodeTape(result)` exactly — the
  trailing junk is indistinguishable from legitimate trailing empty
  registers under the single-delimiter encoding, so a naïve delete is
  **unsound**. The insert/append path is unaffected. Recorded the
  resolution fork (sentinel `sig=4` vs. normalize-up-to-trailing-empties
  vs. multi-tape) in
  [C1 progress](#go-stop-result-length-decreasing-ops-hit-a-tape-model-wall-may-2026).
  After fuller analysis, **recommend option (A) — the end-of-tape
  sentinel** — because it keeps all downstream soundness exact and
  unconditional (the sentinel *firewalls* delete junk so no gadget ever
  reads it as content), whereas (B) spreads `≈`/invariant/junk-invariance
  friction through the whole verifier layer. Pending owner confirmation.
  Full build green; Lang layer still axiom-free. Next (append path,
  fork-independent): scan-trajectory lemma + `composeFlatTM_run` gluing.

- **May 2026 — C1 go/no-go: shared shift gadget built (GREEN).** Added
  `Lang/ShiftTape.lean`: `insertCarryTM` + validity + step lemmas +
  the run lemma `insertCarryTM_run`, **sorry-free, ~200 LOC**, well
  under the 500-LOC threshold. This is the reusable single-tape
  "insert one symbol, shift right" core that `appendOne`/`appendZero`
  use directly and the overwrite ops use after a delete. **Decision:
  proceed with option 1** (build out `compileOp`). Technique that kept
  it small: `simp` computes `find?` over the fixed 3-symbol transition
  table, so each per-state step lemma is ~15 LOC (vs ~40 for hand-
  rolled `find?`-peeling). Revised `compileOp` estimate: **~1.5–2K
  LOC** (two ~200-LOC shift gadgets + per-`Op` assembly +
  `scanRightUntilTM`-based navigation). Wired into the build via
  `Complexity.Lang`; full build green (3351 jobs), Lang layer still
  axiom-free. Next: the delete/shift-left companion, then `appendOne`
  end-to-end (def + `compileOp_sound` slice). See
  [C1 progress](#c1-progress--interim-measurement-may-2026).

- **May 2026 — C1 step 1: decoder round-trip proved, `flattenTape`
  bug fixed.** Started the top risk (C1). Proved
  `Compile.decodeTape_encodeTape` (was a `sorry`), via four short
  structural-induction helpers (`splitOnZero_append_zero`,
  `splitOnZero_encodeTape`, `dropTrailingEmpty_append_nil`,
  `unshiftReg_shiftReg`). **Bug surfaced and fixed**: `flattenTape`
  reconstructed `left.reverse ++ [head] ++ right`, splicing the head
  *index* into the tape contents as if it were a symbol; in this
  model `left` is never written and `head` is a cursor index, so the
  contents are exactly `right`. The old definition made the round-trip
  unprovable. `Compile.lean` sorrys 7 → 6; build green (3350 jobs);
  Lang layer still axiom-free. **Measurement:** the decode
  *infrastructure* for a primitive's soundness is cheap (~120 LOC); the
  remaining per-`Op` cost is the TM build + run lemma. See
  [C1 progress](#c1-progress--interim-measurement-may-2026) for the
  revised per-`Op` cost model (navigation amortises via
  `scanRightUntilTM`; the data-movement shift loop does not) and the
  resulting decision point.

- **May 2026 — Risk register audit (no code change).** Reviewed the
  whole proof path against the documented risks; `lake build` green,
  0 axioms. Findings: (1) the sorry count was wrong (`~26` headline,
  table summed to 32, actual ~34; `CliqueRelTM` was 3, is 5).
  (2) The two highest-impact gaps were **untracked** because they are
  **sorry-free**: the `if-on-the-answer` reductions
  (`FlatSingleTMGenNP_to_FlatTCC`,
  `TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP`) and the dummy
  `bridgeMachine`s reached via `GenNP_to_TMGenNP`. Now Risks **S1**/
  **S2**, enabled by **S3** (`polyTimeComputable` size-only).
  (3) Old risks **#4/#5 were mis-located** at `Simulators/CookTableau`
  and `Simulators/MultiToSingle`, which are **orphans** (compiled,
  referenced by no reduction) — proving their sorrys advances
  `CookLevin` by zero until S1/S2 are rewired. Now Risk **S4**.
  (4) Old risk **#1a was stale**: it listed `compileIfBit` as stubbed,
  but the 1d-resolution iteration already concretized it. (5) The
  register over-weighted *compiler structure* (cheap, discharges
  `CompiledCmd` invariants) and under-weighted *per-primitive
  operational soundness* (`compileOp_sound`), which is the exact
  1,000–2,500-LOC/primitive cost that caused the pivot — the layer
  does **not** amortise it. Register rewritten into Group S
  (soundness) + Group C (completion); new top item **C1** = prove one
  primitive `Op` sound end-to-end, to test the pivot premise before
  building more skeleton. Also surfaced **C2** (`compileSeq_sound`
  head-reset/resume gap, distinct from 1d).

- **May 2026 — Risk #1 decomposed.** `Lang/Compile.lean` was
  refactored from the single `Compile := fun _ => validFlatTM_default`
  stub into a structural recursion `compileCmd : Cmd → CompiledCmd`
  with four per-constructor helpers (`compileOp`, `compileSeq`,
  `compileIfBit`, `compileForBnd`), all still stubbed but with
  focused sorrys. **Structural commitments made** (any future
  implementation must respect these):
  1. `CompiledCmd` records an explicit `exit` state — bare
     `FlatTM` is not enough for `composeFlatTM`-style composition.
  2. Alphabet is fixed at `sig = 3` (delim, shifted 0, shifted 1).
     This restricts the layer's inputs to bit-strings.
  3. `Compile.overhead`'s argument is now `State.size s + cost c s`
     rather than `State.size s` — honestly accounting for tape
     growth during execution.
  4. Each compiled fragment is single-tape (`tapes = 1`).
  **New sub-gaps surfaced**: 1a (per-Op TM design), 1b (`loopTM`
  combinator missing from `TMPrimitives.lean`), 1c (two-exit
  tester for `compileIfBit`). The `Compile_sound` sorry was split
  into four per-constructor sorrys plus the assembly. Net sorry
  count: +5 (3 → 7 in `Compile.lean`). Build remains green.

- **May 2026 — `compileSeq` concretized.** The `compileSeq` helper
  in `Lang/Compile.lean` was changed from the `compiledCmd_default`
  stub to a real `composeFlatTM`-based construction. All
  `CompiledCmd` invariants (`exit_lt`, `exit_is_halt`, `M_valid`,
  `M_tapes`, `M_sig`) discharge cleanly using the existing
  `composeFlatTM_*` lemmas. **Gap surfaced**: `composeFlatTM_run`'s
  trajectory precondition (`h_traj1`) requires M₁ to avoid halting
  prematurely, but `CompiledCmd` only guarantees the exit state
  *is* a halt state — not that it is the *unique* halt state.
  Compositional soundness (the still-`sorry`-bodied
  `compileSeq_sound`) will need either a strengthened
  `halt_unique` invariant on `CompiledCmd` or a per-helper
  operational invariant. Documented inline in `compileSeq`'s
  docstring. Sorry count unchanged at 7 in `Compile.lean`; build
  remains green; Lang layer still axiom-free.

- **May 2026 — Risk #1d resolved: `Compile.joinTwoHalts`
  combinator landed.** Added a local TM combinator that takes
  `(M, h1, h2)` and produces a TM with `h2` demoted from halt to
  non-halt plus bridge entries from `h2` to `h1`. The combinator
  is intentionally minimal — no fresh state is added, just a halt-
  bit flip and `bridgeEntries M.sig h2 h1` prepended to `M.trans`.
  All four key lemmas proved: structural accessors
  (`_states`/`_start`/`_sig`/`_tapes`, all `rfl`), `_h1_is_halt`
  (preserves `h1`'s halt bit), `_halt_unique` (every halt in the
  joined TM is `h1`, given the precondition that M's halts were
  only at `{h1, h2}`), and `_valid` (full validity proof, ~25 LOC,
  using `bridgeEntries_mem` and lifting M's transition validity).
  Plus a helper `branchCompose_halt_only_at_exits` that proves the
  precondition for `branchComposeFlatTM` outputs whose branches
  are `CompiledCmd`s. Rewrote `compileIfBit` to compose
  `branchComposeFlatTM` with `joinTwoHalts`: all seven
  `CompiledCmd` invariants now discharge without sorrys. Net sorry
  count in `Compile.lean`: 8 → 7. Build green on second pass
  (first failed on `show ... at hi` syntax; corrected to
  `change ... at hi`). Lang layer still axiom-free.

- **May 2026 — `compileIfBit` concretized; multi-halt gap (risk
  1d) surfaced and isolated.** Introduced a `BranchTester`
  structure plus a stub 2-state `branchTester_default` and
  `compileTestBit`. Defined `compileIfBit` via
  `branchComposeFlatTM`. **Six of seven `CompiledCmd` structure
  fields discharge cleanly** (`exit_lt`, `exit_is_halt`, `M_valid`,
  `M_tapes`, `M_sig`, plus structural defs); the seventh,
  `halt_unique`, is a focused sorry. The gap is real and
  structural: `branchComposeFlatTM` produces a TM whose halt
  vector has two `true` entries (one per branch's exit), so no
  choice of `exit` field can satisfy `halt_unique`. The earliest
  prediction in iteration 2 ("non-unique halt could be an issue")
  is now a concrete, isolated proof obligation that documents
  exactly what construction is missing. Resolution path
  (recommended option (a)): add a *join combinator* that bridges
  two halt states to a new shared final state. Deferred to a
  future iteration. Net sorry count: 7 → 8 in `Compile.lean`;
  build green; Lang layer still axiom-free.

- **May 2026 — `compileOp` decomposed into 8 per-`Op` stubs.**
  Replaced the single uniform `compileOp (_o : Op) := compiledCmd_default`
  with a dispatch on the `Op` constructor and one named stub per
  case: `Compile.opClear`, `Compile.opAppendOne`,
  `Compile.opAppendZero`, `Compile.opCopy`, `Compile.opTail`,
  `Compile.opHead`, `Compile.opEqBit`, `Compile.opNonEmpty`. Each
  carries an inline contract describing the head movement / tape
  mutation it must perform under the `sig = 3` alphabet
  convention. **No new sorrys** — each stub still returns
  `compiledCmd_default`, so `compileOp_sound` stays as one sorry
  (decomposing it per-`Op` is deferred until at least one helper
  is concretized). Future per-`Op` iterations can now proceed
  independently without touching the rest of the compiler. Build
  green on first pass.

- **May 2026 — `halt_unique` invariant added to `CompiledCmd`.**
  Closes the gap surfaced in the previous iteration. The new
  field
  ```
  halt_unique : ∀ i, M.halt[i]? = some true → i = exit
  ```
  guarantees the compiled fragment has a single halt state, which
  feeds directly into the `h_traj1` precondition of
  `composeFlatTM_run`. Discharged for both `compiledCmd_default`
  (trivial: single-element halt vector) and `compileSeq`
  (non-trivial: case split on `i < r1.M.states`, using
  `getElem?_append_left/right`, `getElem?_replicate`, and
  `r2.halt_unique`). **No new sorrys added** — the proof
  obligation lands fully within reachable Lean library lemmas.
  Sorry count unchanged at 7 in `Compile.lean`; total tactical
  sorrys = 26; Lang layer still axiom-free; build green on first
  pass.

---

## How to read the Parts below

The Parts describe the **target shape** of each area at the end of
the project. They do **not** prescribe an execution order. Read
them as "what success looks like for this area" plus a
decomposition into sub-steps that may be useful.

The execution order is determined by the [Risk register](#risk-register).
Parts can be partially advanced in any order; the dependencies
that matter are noted in each Part's text and in the risk
register's "Why this is high-risk" column.

The notation `Part 3.1`, `Part 4.2`, etc. is used in `TODO(...)`
tags throughout the source as a pointer to the area / sub-step,
not as a time marker.

---

## Part 0 — Honest assessment of the original state

This part is preserved from the original ROADMAP as the diagnosis
that motivated all subsequent work. Items marked ✅ have been
addressed by Parts 1–2; items marked ⏸ are paused by the May 2026
pivot; items marked ⏳ are still open and addressed by the revised
plan below.

The repository currently establishes
`theorem CookLevin : NPcomplete SAT`, but the term it produces is
**not** a faithful proof of the Cook–Levin theorem. Five separate
classes of issues, listed in roughly increasing difficulty to fix:

### 0.1 The complexity framework does not constrain runtime ✅ partly

- `PolyTimeComputableWitness f` only requires
  `encodable.size (f x) ≤ bound (encodable.size x)`. This bounds the
  *output size*, not the *running time*. (Still open — addressed in
  new Part 4.)
- `HasDecider X P f := ∃ dec : X → Bool, ∀ x, P x ↔ dec x = true`
  with `f : Nat → Nat` unused. (✅ Removed in Part 2, replaced with
  the TM-backed `DecidesBy`.)
- `inTimePoly P` inherits the weakness of `HasDecider`. (✅ Replaced
  in Part 2 with `∃ f, Nonempty (DecidesBy P f) ∧ inOPoly f ∧ monotonic f`.)

### 0.2 `NPhard_GenNP` is vacuous ⏳

`Complexity/GenNP_is_hard.lean` line 9 introduces

```
theorem hasDeciderClassical (P : X → Prop) (timeBound : Nat → Nat) :
    HasDecider X P timeBound := by
  classical
  refine ⟨fun x => if P x then true else false, ?_⟩
  …
```

This is used in `genNPInstance` and `NPhard_GenNP`. In Part 2 the
theorem was **retyped** to `Nonempty (DecidesBy …)` so the rest of
the chain typechecks against the strengthened framework, but its
body remains a labelled `sorry` (`TODO(Part6:hasDeciderClassical)`).
The real version requires Parts 3–6 to be in place so the verifier
TM can be drawn from `InNPWitness`. Closed in new Part 7.

### 0.3 The TM bridge layers are dummies ⏳

- `Complexity/LM_to_mTM.lean`: `bridgeMachine` is a 1-state,
  0-transition flat TM that starts in a halting state.
- `Complexity/mTM_to_singleTapeTM.lean`: same pattern with a 1-tape
  variant. The multi-tape machine `M` is passed in and immediately
  discarded.
- `Complexity/L_to_LM.lean`: a definitional repackaging — there is
  no TM at all.
- `…/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean`:
  `noncomputable def f inst := if TMGenNP_fixed M inst then yesInst
  else noInst`. The map's value depends on the answer to the source
  language.
- `…/FlatSingleTMGenNP_to_FlatTCC.lean`: same `if`-on-the-answer
  pattern.

Addressed in new Parts 5 (mTM → 1-tape via the layer) and Part 6
(Cook tableau via the layer).

### 0.4 Definitional smells ⏳ partly

- `instEncodableDefault` (`Definitions.lean:14`) silently defaults to
  `size := 0`. Still present. (Low priority; the consumers that
  relied on `size = 0` are now mostly placeholder TM-bridge layers.)
- `abbrev TM (_σ : Type) (_ : Nat) := FlatTM` — phantom parameters.
  Still present.
- `computableTime'` in `MachineSemantics.lean:186` — leftover Coq
  port hook. Will be **superseded** by the new layer's cost
  semantics (new Part 3).

### 0.5 Outstanding `sorry`s (original) ✅ all closed in Part 1

```
Complexity/NP/SAT.lean:206              compressAssignment_size_bound
Complexity/NP/FSAT_to_SAT.lean:706      FSAT_to_SAT_size_le
Complexity/NP/FlatClique.lean:38        clique_size_bound
Complexity/NP/kSAT_to_FlatClique.lean:63 polynomial-time bound
Complexity/NP/kSAT_to_FlatClique.lean:64 reduction correctness
```

All closed in Part 1.

### The four open `sorry`s after Part 2's framework migration

After the framework migration the codebase has exactly four labelled
`sorry`s, all flagged with `TODO(...)` tags pointing at the roadmap
phase that closes them:

| # | Location                                          | Tag                                  | Closes at |
|---|---------------------------------------------------|--------------------------------------|-----------|
| 1 | `…/Deciders/EvalCnfTM.lean:58`                    | `TODO(Part2-followup:EvalCnfTM)`     | New Part 3.5 |
| 2 | `…/Deciders/CliqueRelTM.lean:66`                  | `TODO(Part2-followup:CliqueRelTM)`   | New Part 3.5 |
| 3 | `Complexity/Complexity/NP.lean:270`               | `TODO(Part3:red_inNP_TMcompose)`     | New Part 4 |
| 4 | `Complexity/GenNP_is_hard.lean:23`                | `TODO(Part6:hasDeciderClassical)`    | New Part 7 |

### What is already sound and should not be touched

- `Complexity/Complexity/MachineSemantics.lean` — `FlatTM` semantics
  and `runFlatTM` are real.
- `Complexity/Complexity/Definitions.lean` — `encodable`,
  `inOPoly`, `monotonic`, polynomial composition (`inOPoly_comp`).
- `Complexity/Complexity/NP.lean` — reduction calculus
  (`reducesPolyMO_reflexive/_transitive`, `red_inNP`, `red_NPhard`).
- `Complexity/Complexity/TMPrimitives.lean` — `composeFlatTM`,
  `branchComposeFlatTM`, `runFlatTM_extend`, `runFlatTM_compose`,
  `scanRightUntilTM`, `verdictTM` (~3.5K LOC, fully proved). This is
  the natural target language of the new layer's compiler.
- The combinatorial core
  `FlatTCC_to_FlatCC ⋅ FlatCC_to_BinaryCC ⋅ BinaryCC_to_FSAT`:
  ~3,000 LOC of fully proved, computable reductions with real size
  bounds (`5n+5`, `50n² + 50n + 1`, `500n⁶ + 500`).
- `Complexity/NP/SAT.lean`, `kSAT.lean`, `kSAT_to_SAT.lean`,
  `FSAT.lean`, `FSAT_to_SAT.lean` (Tseytin), `FlatClique.lean`,
  `kSAT_to_FlatClique.lean`.

---

## Part 1 — Foundational hygiene ✅ done

All five sub-items of P1.1–P1.5 from the original ROADMAP landed.
The original five "small" `sorry`s are closed. `Subtypes.lean` is
still present but empty (low-priority cleanup; not on the critical
path).

---

## Part 2 — TM-backed `inTimePoly` framework ✅ done; content ⏸ paused

The Part 2 *framework* (Steps 1–10 of [`PART2.md`](../parked/PART2.md))
landed in good shape:

- `Complexity/Complexity/NP.lean` gained the `DecidesBy` structure
  and a TM-backed `inTimePoly`.
- `Complexity/Complexity/TMDecider.lean` — `inTimePolyTM`,
  `DecidesBy.decideFn` + soundness, `.negate`, `.iff` combinators.
- `Complexity/Complexity/TMEncoding.lean` — list-level encoding
  helpers.
- `Complexity/Complexity/TMPrimitives.lean` — the `composeFlatTM`
  combinator family (`branchComposeFlatTM` for polarity dispatch,
  `runFlatTM_compose` for chaining, `runFlatTM_extend` for time-bound
  padding).
- `sat_NP` and `FlatClique_in_NP` rebuilt against the new framework
  (modulo their `DecidesBy` witnesses, which are sorrys #1 and #2).
- `red_inNP` and `P_NP_incl` rebuilt against the new framework
  (modulo sorry #3, the TM-composition gap).
- `hasDeciderClassical` retyped to produce `Nonempty (DecidesBy …)`
  (body is sorry #4).

The Part 2 *content* — closing sorrys #1 and #2 by constructing
actual SAT-verifier and FlatClique-verifier `FlatTM`s by hand —
is **paused** mid-stream. The detailed history of what was built
is in [`PART2.md`](../parked/PART2.md) (now treated as archival once the
pivot lands). Two primitives (`copyUnaryTM`, `compareUnaryAtMarkerTM`)
were fully closed; the per-literal / per-clause / per-CNF loops were
not, and the `CliqueRelTM` analogue was never started.

---

## Part 3 — Higher-level computable layer (NEW, the pivot)

Build a small total computation language ("the layer") with explicit
cost semantics, and a one-time compiler from the layer to `FlatTM`.
This is the central infrastructure investment of the May 2026 pivot.

### 3.1 Choose the language

Recommended: a small **structured while-language** with bounded
loops, fixed-arity primitive operations on `List Nat`, and an
explicit cost annotation per primitive. This is enough to express
every verifier and reduction we need.

Candidate shape:

```lean
inductive Cmd : Type where
  | skip   : Cmd
  | seq    : Cmd → Cmd → Cmd
  | assign : Var → Expr → Cmd
  | if_    : BExpr → Cmd → Cmd → Cmd
  | for_   : Var → Expr → Cmd → Cmd     -- counted loop, bound = Expr
```

Cost is the sum over `Cmd` of a fixed constant per node, plus the
iteration count of each `for_`. We commit to *total* cost (the bound
must always be evaluable) so the cost function is a closed-form
expression in input size.

An alternative is **μ-recursive with cost** (closer to the Coq L
calculus); the trade-off is that it puts more weight on the
compiler. The decision lands in 3.1.

### 3.2 Define `inTimePoly` and `polyTimeComputable` via the layer

```lean
def inTimePoly {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ (p : Cmd) (f : Nat → Nat),
    inOPoly f ∧ monotonic f ∧
    (∀ x, cost p (encode x) ≤ f (encodable.size x)) ∧
    (∀ x, eval p (encode x) = decide (P x))

def polyTimeComputable {X Y : Type} [encodable X] [encodable Y]
    (h : X → Y) : Prop := …    -- analogous
```

Replacing `DecidesBy` with this is a pure interface swap inside
`NP.lean`; downstream theorems (`sat_NP`, `FlatClique_in_NP`,
`red_inNP`, `red_NPhard`) keep their signatures.

### 3.3 Build the compiler `Compile : Cmd → FlatTM`

One-time engineering. Each `Cmd` constructor compiles to a small
gadget over `FlatTM` using the existing `composeFlatTM` /
`branchComposeFlatTM` combinators:

- `skip` → 1-state halt
- `seq c₁ c₂` → `composeFlatTM (Compile c₁) (Compile c₂)`
- `if_ b c₁ c₂` → `branchComposeFlatTM (CompileB b) (Compile c₁) (Compile c₂)`
- `for_` → a `loopTM` instance (the third combinator planned in
  PART2.md §11.5c, now landed here)
- primitives → small hand-rolled TMs (~50 LOC each, but a finite
  fixed set, e.g. ~10 primitives total)

**Estimated size: ~5,000 LOC.** Most of it is per-primitive
correctness lemmas; the inductive cases use the combinators as black
boxes.

### 3.4 Soundness theorem

The main extraction lemma:

```lean
theorem Compile_sound (p : Cmd) (input : List Nat) :
    ∃ cfg,
      runFlatTM (cost p input + compileOverhead) (Compile p)
          (initFlatConfig (Compile p) [input]) = some cfg ∧
      haltingStateReached (Compile p) cfg = true ∧
      readTape cfg = eval p input
```

Plus a corollary "if `cost p` is polynomial in input size, then
`runFlatTM` halts within a polynomial step budget". This is the
bridge that makes the layer-level `inTimePoly` imply the
`FlatTM`-level `DecidesBy`.

**Estimated size: ~1,500 LOC.**

### 3.5 Close sorrys #1 and #2 via the layer

Write `evalCnfCmd : Cmd` (~50 LOC) and `cliqueRelCmd : Cmd` (~80 LOC)
in the layer, prove their cost bounds (~100 LOC each), prove their
correctness against `satisfiesCnf` / `cliqueRel` (~150 LOC each),
and instantiate the bridge to close sorrys #1 and #2.

**Estimated size: ~800 LOC total, replacing the projected ~10K LOC
of hand-rolled work in Phases G+H of PART2.md.**

After Part 3, two of the four open sorrys are closed and the layer
exists as reusable infrastructure for Parts 4–7.

---

## Part 4 — `polyTimeComputable` via the layer

Migrate the `polyTimeComputable` witnesses for every reduction in
the chain to use the layer.

### 4.1 Replace the placeholder witnesses

Each reduction in `Complexity/NP/SAT/CookLevin/Reductions/` and the
Tseytin transformation currently provides a `PolyTimeComputableWitness`
that bounds only the output size. Replace each with a layer-level
program whose `cost` is polynomial in input size.

The reductions in scope:

- `kSAT_to_SAT_reduction` (trivial, ~30 LOC in the layer)
- `FSAT_to_SAT_tseytin` — already explicitly computable, the layer
  implementation is mostly transcribing the existing recursion (~300 LOC)
- `kSAT_to_FlatClique_instance` (~150 LOC)
- `flatTCC_to_flatCC`, `FlatCC_to_BinaryCC_instance`,
  `BinaryCC_to_FSAT_instance` (~100 LOC each)

### 4.2 Re-prove `red_inNP`

With the layer in place, the composition obligation that is sorry #3
(`TODO(Part3:red_inNP_TMcompose)`) is a straightforward
`Cmd.seq`-style composition: run the reduction's layer program on
the input, then the verifier's layer program on the result. The
cost composes via `inOPoly_comp`, which already exists.

**Estimated size: ~1,500 LOC.** Closes sorry #3.

After Part 4, three of the four open sorrys are closed and every
`⪯p` arrow in the chain is real.

---

## Part 5 — Multi-tape → single-tape via the layer

Replace the dummy bridges in `LM_to_mTM.lean` and
`mTM_to_singleTapeTM.lean` with the standard textbook construction,
expressed in the layer.

### 5.1 Decide the source-language model

Per the original ROADMAP P4.1, recommendation (a): drop L entirely.
Treat `GenNPInput` / `LMGenNP` as abstract NP-source formulations
and collapse the "L → LM → mTM" tower into a single
"GenNP → mTMGenNP_fixed" reduction.

### 5.2 Multi-tape → single-tape simulator

Standard construction: encode the `k` tapes with delimiters and a
head-marker extension of the alphabet. Each source step costs O(L)
target steps where L is the total tape length. The simulator
itself is **~150 LOC in the layer** plus a ~200-LOC correctness
proof.

### 5.3 GenNP → mTM reduction

Construct a (non-deterministic) multi-tape TM that guesses a
certificate and runs the verifier. With Part 4's layer-level
verifiers in hand, this is ~200 LOC.

**Estimated total for Part 5: ~1,000 LOC** (vs. the original ROADMAP's
~3,000 LOC for the same content in hand-rolled form).

---

## Part 6 — Cook tableau via the layer

The actual heart of Cook–Levin: the Cook 2D tableau. Currently
faked by `if FlatSingleTMGenNP inst then trivial-yes else trivial-no`.

### 6.1 Implement the tableau construction

For a TM `M` on input `s` with step budget `steps`, build a
`FlatTCC` instance whose
- `init` is the start configuration encoded as a row of width
  `1 + |s| + steps + 1`,
- `cards` encode the local 3-cell transitions of `M`,
- `final` matches iff a halting state appears somewhere in the
  final row,
- `Sigma` is `M`'s alphabet plus state symbols plus a head marker.

This is the classical 2D tableau. The construction is a *function*
on `M, s, steps` (no TM execution involved), so it lives at the
mathematical level — the layer is only needed for its cost bound,
not its definition.

**Estimated size: ~1,000 LOC** for the construction (vs the
original ROADMAP's ~3,000 LOC).

### 6.2 Prove the bijection

`FlatSingleTMGenNP (M, s, maxSize, steps) ↔ FlatTCC (encode M s steps)`,
both directions, via the standard tableau-to-run bijection.

**Estimated size: ~1,500 LOC.**

### 6.3 Prove the size bound

Linear in `(|s| + steps) · |Σ|`.

**Estimated size: ~200 LOC.**

After Part 6, the "M accepts s in `steps` steps" → "the FlatTCC
tableau is satisfiable" link is real, and the FlatTCC → FSAT → SAT
chain (already sound) finishes the proof.

---

## Part 7 — Real `NPhard_GenNP` and final assembly

### 7.1 Delete `hasDeciderClassical`

Replace its use in `genNPInstance` with the real verifier coming
from `InNPWitness`'s (now layer-backed) `inTimePoly`.

### 7.2 Re-state `NPhard_GenNP`

The proof goes through mechanically once the framework is sound.
Closes sorry #4.

### 7.3 Audit `CanEnumTerm`

The `boollists_enum_term` encoding is currently a size-only
encoding (not an injection). Replace with a proper binary encoding
`Y → List Bool`. Mathlib's `Encodable` / `Denumerable` may be
reusable.

### 7.4 End-to-end test

`theorem CookLevin : NPcomplete SAT` rebuilds against the new
definitions. Verify build is sorry-free, axiom-free beyond the
standard set (`propext`, `Classical.choice`, `Quot.sound`),
reproduces.

### 7.5 `#print axioms CookLevin`

Add a small file. Document the surviving axioms.

### 7.6 CI target

Fail the build if any new `sorry` or `hasDeciderClassical`-style
classical shortcut creeps in.

### 7.7 Documentation pass

Update READMEs and the "axioms used" appendix.

---

## Rough effort estimate (lower-confidence)

⚠ **Under the skeleton-first methodology, these are upper-bound
estimates we re-evaluate per iteration, not commitments.** The
original ROADMAP gave LOC estimates that turned out to be ~10× too
low because the proof obligations had unsurfaced structural
issues. The numbers below are best-effort upper bounds *given the
skeleton we have today*; they will change as the risk register
shrinks.

| Part  | Area                                                 | Estimate     | Original estimate | Status |
|-------|------------------------------------------------------|--------------|-------------------|--------|
| 1     | Cleanup & `sorry` discharge                          |  ~500 LOC    |  ~500 LOC         | ✅ done |
| 2     | TM-backed `inTimePoly` *framework*                   | ~1,500 LOC   | (subset of 1,500) | ✅ done |
| 2c    | Hand-rolled deciders *(retired)*                     | n/a          | n/a               | ⏸ retired in favour of Part 3 |
| 3     | Higher-level computable layer (skeleton landed)      | ~7,000 LOC   | n/a               | 🟡 skeleton; refining |
| 4     | `polyTimeComputable` via the layer                   | ~1,500 LOC   | ~4,000 LOC        | 🟡 skeleton; refining |
| 5     | Multi-tape → 1-tape simulator via the layer          | ~1,000 LOC   | ~3,000 LOC        | 🟡 skeleton; refining |
| 6     | Cook tableau (TM → FlatTCC) via the layer            | ~2,700 LOC   | ~3,000 LOC        | 🟡 skeleton; refining |
| 7     | Real `NPhard_GenNP`, axiom check, CI, docs           |  ~600 LOC    |  ~600 LOC         | 🟡 skeleton; refining |

**Rough remaining LOC:** ~13,000 across Parts 3–7. The skeleton
already in place means the *types and theorem statements* are
done; the LOC estimates above are for filling in the proof
bodies, with the higher-risk items more likely to overrun (see
[Risk register](#risk-register)).

### Iteration cadence

Not a fixed sequence — the risk register is the source of truth.
The shape of each iteration:

1. Pick the top item in the [Risk register](#risk-register).
2. Try to concretize it: replace the axiom with a `def`, or the
   single sorry with several smaller sorrys, or fill in a proof.
3. If it typechecks: validation. The risk register entry drops
   off or moves down.
4. If a structural gap surfaces: stop, document the gap, possibly
   add a new risk register entry, decide whether to fix the
   structure now or work around it.
5. Always commit + push with `lake build` green. The build state
   is the source of truth for "the skeleton is still coherent".
6. Update the [Current skeleton state](#current-skeleton-state)
   snapshot (axiom count, sorry count, build status).

Items 1–5 are typically one session. Item 6 is one paragraph.

---

## Things NOT to break

Every iteration must preserve the build and keep the existing
real mathematics compiling:

- `FlatTM` semantics in `MachineSemantics.lean`.
- `inOPoly`, `inOPoly_add`, `inOPoly_comp` in `Definitions.lean`.
- The combinator library in `TMPrimitives.lean`
  (`composeFlatTM`, `branchComposeFlatTM`, `runFlatTM_compose`,
  `runFlatTM_extend`). The new layer's compiler emits into this
  library.
- The full Tseytin transformation in `FSAT_to_SAT.lean`.
- The 3-level tableau core
  `FlatTCC_to_FlatCC`, `FlatCC_to_BinaryCC`, `BinaryCC_to_FSAT`.
- `SAT_inNP.sat_NP`, `FlatClique_in_NP` — the *interfaces* are
  stable; only the `DecidesBy` witnesses change underneath.
- The reduction calculus (`⪯p`, `red_NPhard`, `red_inNP`).

When introducing the layer in Part 3, add it as a new namespace
(e.g., `Complexity.Lang`) and migrate `DecidesBy` consumers one at
a time. The hand-rolled `EvalCnfTM` / `CliqueRelTM` primitives can
be retired in a single sweep at the end of Part 3.

---

## Fallback plan: if the layer also overruns

If Part 3 lands meaningfully over its ~7,000 LOC estimate (say, by
3× or more), the next pivot is to **scope-restrict the headline**:

- Define `inTimePoly` axiomatically (an interface specifying the
  operations a TM-computable predicate must support: closure under
  Boolean operations, composition, polynomial time-bounded
  iteration). Mark it as a documented assumption rather than
  proving it via a concrete TM model.
- Finish the combinatorial chain (FlatTCC → FlatCC → BinaryCC →
  FSAT → SAT) — already in place.
- State `CookLevin : NPcomplete SAT` conditionally on the
  `inTimePoly`-interface assumption, with a clearly documented
  list of obligations that a future TM model must discharge.

This gives an *honest conditional theorem* in a few weeks rather
than a *real unconditional theorem* in years. It is not as
satisfying, but it is more useful than indefinitely paused work.

---

## Appendix A — Lessons from the hand-rolled Part 2

The May 2026 pivot was driven by hard-won experience. These notes
are for anyone considering a similar approach in a different
formalisation.

1. **Per-state lemmas don't amortise across primitives.** Every
   new primitive needs its own per-state step lemmas, per-state
   run-unfold helpers, and phase scan lemmas. Reusable infrastructure
   helps the *chaining* (via `composeFlatTM_run`), but the inside of
   each primitive is fresh work each time.

2. **Iteration bookkeeping is the dominant cost.** ~600 LOC per
   loop site to thread tape state through the iteration count,
   plus another ~400 LOC of post-loop cleanup. `copyUnaryTM` and
   `compareUnaryAtMarkerTM` paid this cost twice for what are
   conceptually 5–9 state machines.

3. **A unified `loopTM` combinator helps but doesn't rescue you.**
   PART2.md Optimisation O2 (`loopTM`) was planned as the
   amortisation lever. It still only saves the iteration bookkeeping
   *between* primitives, not the per-state bookkeeping *inside*
   each primitive's body.

4. **Multi-tape vs single-tape is a real cost driver.** The
   `entryMatchesConfig` lookup has no wildcard, so a `k`-tape
   composition needs `(sig+1)^k` bridge entries per composition.
   Single-tape with a delimiter scratch is the only economical
   shape for hand-rolled TM composition. The layer's compiler
   should respect this constraint.

5. **The layer needs *cost* in its semantics, not just behaviour.**
   Mathlib's `Computable`/`Partrec` infrastructure handles
   computability but not complexity; using it as-is would close
   sorry #1 only by replacing "TM construction" with "Computable
   construction", which doesn't help unless cost annotations are
   added.

---

## Appendix B — Why the L calculus (Coq's choice) inspired the pivot

The Coq Cook–Levin port writes verifiers and reductions in the L
calculus (a small untyped lambda calculus over numerals) and uses
the `computableTime'` tactic to extract Turing machines with proved
time bounds. The L calculus itself is ~3,000 lines of Coq
infrastructure; each downstream verifier or reduction is then ~50–100
lines of L-level code.

We declined to port L in the original ROADMAP P4.1 because we
believed a Lean port should be self-contained and that the L
calculus was a "Coq-port artifact". After ~14K LOC of hand-rolled
Part 2 work, the empirical evidence is that the Coq team's
abstraction is essentially load-bearing for the whole proof, not a
local choice: any informal Cook–Levin proof spends most of its
words describing a generic polynomial-time TM, and any formalisation
must therefore commit to *some* abstraction that lets you talk
about a generic polynomial-time TM without writing it out.

The new layer (Part 3) is the Lean analogue of L. It is smaller
and weaker than L (structured while-language vs general lambda
calculus; total vs partial), but it is enough for Cook–Levin.

---

## Appendix C — Original Parts 2–6 plan (archival)

This appendix preserves the original Parts 2–6 plan from the
pre-pivot ROADMAP. It is **superseded** by Parts 3–7 above. Read
this only if you are doing historical archaeology on the project's
proof strategy.

### (Original) Part 2 — Strengthen the framework to a real `inTimePoly`

Replace `HasDecider` with a TM-backed `DecidesBy` structure, then
re-prove `sat_NP`, `FlatClique_in_NP`, `red_inNP`, `P_NP_incl`.

**Status:** Framework portion ✅ done in Steps 1–10 of PART2.md.
Content portion (hand-rolled `EvalCnfTM` / `CliqueRelTM` deciders)
⏸ paused mid-Step-11, superseded by new Part 3.

### (Original) Part 3 — Strengthen `polyTimeComputable`

Replace the output-size-only `PolyTimeComputableWitness` with a TM
that *computes* `f`, and re-prove every `_poly` theorem in the chain.

**Status:** Superseded by new Part 4 (uses the layer instead of
hand-rolled TM constructions).

### (Original) Part 4 — Replace the dummy TM bridges

Build a real multi-tape → single-tape simulator; build a real
GenNP → mTM reduction.

**Status:** Superseded by new Part 5 (uses the layer).

### (Original) Part 5 — Replace the FlatSingleTMGenNP → FlatTCC reduction

Implement the Cook 2D tableau construction.

**Status:** Superseded by new Part 6 (uses the layer for the cost
side of the construction).

### (Original) Part 6 — Replace `NPhard_GenNP`

Delete `hasDeciderClassical`, re-state `NPhard_GenNP` against the
strengthened framework.

**Status:** Superseded by new Part 7.

### (Original) Part 7 — Final assembly and CI

End-to-end test, `#print axioms`, CI target, documentation pass.

**Status:** Folded into new Part 7.
