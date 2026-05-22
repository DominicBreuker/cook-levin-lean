# Part 2 — Implementation Plan & Progress Tracker (v3.2)

Tracks Part 2 of `ROADMAP.md` (lines 166–218): replace the
propositional `inTimePoly` / `HasDecider` with a Turing-machine-backed
witness, then re-prove `sat_NP`, `FlatClique_in_NP`, `red_inNP`, and
`P_NP_incl` against the new definition.

> **v3 (prior revision).** Status sweep + compaction. The v2 pivot —
> "migrate the framework first, carry `EvalCnfTM.decider` and
> `CliqueRelTM.decider` as labelled `sorry`s, then close them
> iteratively" — was correct and is paying off. Steps 1–10 are done,
> the chain rebuilds, and `theorem CookLevin : NPcomplete SAT`
> typechecks against the strengthened `inTimePoly` with the four
> acknowledged sorrys.
>
> What v2 underestimated is the cost of hand-building each verifier TM:
> Step 11 is at ~7400 LOC across roughly a dozen sessions and only
> `copyUnaryTM` is fully closed. The pure mechanics — per-state step
> lemmas, phase scan lemmas, iteration-lemma bookkeeping across three
> tape forms — eat 1000–2500 LOC per primitive. v3 keeps the
> architecture, tightens the work plan around two compounding savings
> (unified run lemmas, a `loopTM` outer combinator), and is honest
> about the remaining scope.
>
> **v3.1 (prior revision).** Step 11.5a (architectural pass) revealed
> that the original 11.5 plan — "compose five primitives linearly via
> `composeFlatTM_run`" — was structurally wrong on two counts: the
> slot-iteration loop is a real loop (needs `loopTM`, prior 11.6) and
> the polarity-gated result bit needs a multi-exit composition
> primitive (a new `branchComposeFlatTM`). Step 11.5 is rescoped into
> five substeps 11.5a–e (see §4 and §5). `advanceRightTM` and the
> `PerLiteral.lean` skeleton with architecture doc landed this
> session. The combinators land in 11.5b/c, the per-literal
> components in 11.5d, the final assembly in 11.5e. Phase G's
> remaining estimate adjusts from ~5100 LOC to ~4800 LOC across 6–8
> sessions (more substeps, fewer LOC per session, fewer hand-rolled
> loops downstream because `loopTM` lands earlier).
>
> **v3.2 (this revision).** Step 11.5b landed cleanly:
> `branchComposeFlatTM` (definition + validity + bridge step lemmas
> for both exits + M₁/M₂/M₃ phase-run lemmas + `_run_pos` and
> `_run_neg`) came in at ~1300 LOC — larger than the v3.1 estimate
> of ~600 LOC but with no novel obstacles; the LOC inflation is
> two-bridge / two-phase duplication that mirrors `composeFlatTM`'s
> existing template. Phase G's remaining estimate refines to ~4400
> LOC across 5–7 sessions. Next session targets `loopTM` (Step
> 11.5c), the last foundation combinator before the per-literal
> evaluator can be composed.

---

## 1. Status

| Phase | Steps   | Goal                                                    | Status     |
|-------|---------|---------------------------------------------------------|------------|
| A     | 1–2     | Foundation: `DecidesBy` + encoding                      | ✅ done    |
| B     | 3–5     | TM combinator library (`composeFlatTM`, `scanRightUntil`, `verdictTM`, …) | ✅ done    |
| C     | 6.0a–o  | Demonstration deciders on SAT input (frozen, not on path)| ✅ done    |
| C′    | 1       | Delete dead `AssgnContainsVar` work                     | ✅ done    |
| D     | 2–3     | `DecidesBy` stubs for `evalCnf` and `cliqueRel`         | ✅ done    |
| E     | 4–9     | Swap `inTimePoly`; re-prove `sat_NP`, `FlatClique_in_NP`, `red_inNP`, `P_NP_incl`; retype `hasDeciderClassical` | ✅ done |
| F     | 10      | Validation: full rebuild, sorry audit                   | ✅ done    |
| G     | 11.0–4d | Step 11 partial: `composeFlatTM_run`, primitives, `copyUnaryTM`, all three `compareUnaryAtMarkerTM` run lemmas | ✅ done    |
| G     | 11.5a   | `advanceRightTM` + `PerLiteral.lean` arch skeleton + substep re-scope | ✅ done    |
| G     | 11.5b   | `branchComposeFlatTM` + `_run_pos` + `_run_neg` (`TMPrimitives.lean`) | ✅ done    |
| G     | 11.5c–8 | Step 11 finish: `loopTM`, per-literal eval, per-clause + per-CNF loops, time bound, `decider` | ⏳ pending |
| H     | 12      | Step 12: `CliqueRelTM.decider`                          | ⏳ pending |
| I     | 13      | Final Part-2 sweep (verify only Part 3 / Part 6 sorrys remain) | ⏳ pending |

**Build state.** `lake build` is clean modulo the 4 sorrys below.
`theorem CookLevin : NPcomplete SAT` typechecks.

## 2. Outstanding sorrys

The source of truth for Part 2's open obligations.

| # | Sorry                                                  | Tag                                         | Closes at |
|---|--------------------------------------------------------|---------------------------------------------|-----------|
| 1 | `EvalCnfTM.decider` (`Deciders/EvalCnfTM.lean:58`)     | `TODO(Part2-followup:EvalCnfTM)`            | Step 11.8 |
| 2 | `CliqueRelTM.decider` (`Deciders/CliqueRelTM.lean:66`) | `TODO(Part2-followup:CliqueRelTM)`          | Step 12.5 |
| 3 | `red_inNP` TM-composition (`Complexity/NP.lean:270`)   | `TODO(Part3:red_inNP_TMcompose)`            | Part 3    |
| 4 | `hasDeciderClassical` body (`GenNP_is_hard.lean:23`)   | `TODO(Part6:hasDeciderClassical)`           | Part 6    |

Part 2's definition of done allows sorrys 3 and 4 to remain (they are
structural deferrals to later phases). Sorrys 1 and 2 close inside
Part 2.

## 3. What is already built (do not re-do)

### 3.1 Framework (Steps 1–10)

- `Complexity/Complexity/TMDecider.lean` — `inTimePolyTM` alias,
  `DecidesBy.decideFn` + soundness, `.negate`, `.iff`. ~150 LOC.
- `Complexity/Complexity/NP.lean` — `DecidesBy` structure,
  `inTimePoly`, `DecidesBy.proj_left`, updated `red_inNP`, `P_NP_incl`.
  ~310 LOC.
- `Complexity/Complexity/TMEncoding.lean` — list-level encoding
  helpers (`shiftSyms`, `encodePair`, `encodeList`, length lemmas).
  ~135 LOC.
- `Complexity/Complexity/TMPrimitives.lean` — `composeFlatTM` +
  `composeFlatTM_valid` + **`composeFlatTM_run`** (Step 11.0) and its
  7 helper lemmas; **`branchComposeFlatTM`** + `_valid` +
  `_run_pos` + `_run_neg` (Step 11.5b) — two-exit generalisation
  of `composeFlatTM` for polarity dispatch in the per-literal
  evaluator; `verdictTM`, `scanRightUntilTM`,
  `runFlatTM_extend`. ~3200 LOC.
- `Complexity/Complexity/Deciders/SAT_TM.lean` — SAT input encoding
  (`sigSAT`, `encodeInput`, length / symbol-bound lemmas) plus the
  Phase-C demonstration deciders kept as a worked pattern library.
  ~6300 LOC.
- `Complexity/Complexity/Deciders/EvalCnfTM.lean` — interface stub for
  `EvalCnfTM.decider`, `EvalCnfTM.inTimePolyTM_evalCnf`, and the
  rebuilt `sat_NP`. ~100 LOC.
- `Complexity/Complexity/Deciders/CliqueRelTM.lean` — analogous stub
  + rebuilt `FlatClique_in_NP`. ~105 LOC.

### 3.2 Step 11 primitives (in progress)

- `Complexity/Complexity/Deciders/EvalCnfTM/Primitives.lean` (~1400
  LOC): `sigEval = 12`, `encodeInputWithScratch` + length /
  symbol-bound lemmas, generic find-helpers
  (`find_singleSomeEntry_match`,
  `find_singleSomeEntry_match_state`, `nat_beq_self`), `writeAtHeadTM`
  (2-state, `_run`), `scanLeftUntilTM` (2-state, `_run_found`),
  `clearRegionTM` (2-state, `_run_found` with `fillPrefix`
  characterisation).
- `Complexity/Complexity/Deciders/EvalCnfTM/CopyUnary.lean` (~2400
  LOC): `copyUnaryTM` (7-state) fully proved — definition, validity,
  per-state step lemmas, per-state run-unfold helpers, four phase scan
  lemmas, `copyUnaryTM_iteration_run`, `copyUnaryTM_run_found` (main
  inductive lemma).
- `Complexity/Complexity/Deciders/EvalCnfTM/CompareUnary.lean` (~4060
  LOC): `compareUnaryAtMarkerTM` (9-state) — definition, validity,
  step lemmas, halting lemmas (Step 11.4a); per-state run-unfold
  helpers + 8 phase scan lemmas (Step 11.4b);
  `compareUnaryTape_iter` recursive tape predicate + its
  characterisation lemmas, `compareUnaryAtMarkerTM_iteration_run`;
  `compareUnaryAtMarkerTM_post_loop_run` +
  `compareUnaryAtMarkerTM_run_match` (Step 11.4c-cont);
  `compareUnaryAtMarkerTM_short_post_loop_run` +
  `compareUnaryAtMarkerTM_run_short` (Step 11.4d);
  `compareUnaryAtMarkerTM_long_post_loop_run` +
  `compareUnaryAtMarkerTM_run_long` (Step 11.4d).
- `Complexity/Complexity/Deciders/EvalCnfTM/PerLiteral.lean` (~150
  LOC, mostly architectural docstring): top-of-file design
  document for Step 11.5 — the per-literal evaluator pipeline,
  the polarity-as-state dispatch decision, the discovered need
  for `branchComposeFlatTM` and `loopTM`, and the substep
  breakdown 11.5a–e. No concrete definitions yet (Substep 11.5a).
- `Complexity/Complexity/Deciders/EvalCnfTM/Primitives.lean`
  gained `advanceRightTM` (2-state, mirrors `writeAtHeadTM`):
  one-cell rightward head movement primitive, with `_valid`,
  step lemmas (in-range / out-of-range), halting lemmas, and a
  unified one-step `_run` lemma. Added in Step 11.5a as the
  first composition link of the per-literal evaluator.

The full architecture and design rationale (alphabet, tape layout,
state machines, cursor marker) live in the docstrings of those files;
this plan does not duplicate them.

---

## 4. Active step: 11.5c (next session)

**Goal.** Land **`loopTM`** — the outer-loop combinator (Optimisation
O2 in §5). Given a body TM `B` with a designated re-entry exit
state and a "check current symbol" state that either continues
(re-runs `B`) or terminates, build a composed TM that iterates `B`
until termination, and prove `loopTM_run` by induction on the
iteration count. This is the third and final foundation
combinator the per-literal evaluator depends on.

**Why this matters.** Without `loopTM`, the per-literal evaluator's
slot-iteration loop (Step 11.5d's `findVarInAssgnTM`) and the
per-clause / per-CNF loops (Step 11.6) all need hand-coded state
machines. Each one duplicates the ~600 LOC iteration bookkeeping
we already paid in `copyUnaryTM_iteration_run` and
`compareUnaryAtMarkerTM_iteration_run`. `loopTM_run` pays this cost
once and amortises it across all three loop sites.

**11.5c sketch.** State layout:

```
[0]                                  — check state (read current
                                       symbol; if terminator, halt;
                                       else jump to body start)
[1, 1 + B.states)                    — body's states (offset by 1)
[1 + B.states]                       — halt-accept state
```

The body's exit state `exitBody` collapses back to `0` via bridge
entries (analogous to the `bridge_pos`/`bridge_neg` entries in
`branchComposeFlatTM`). After the body re-enters state 0, the
classifier may either terminate (halt-accept) or run the body
again.

`loopTM_run` is: given a body `B` whose `_run` lemma says
"starting from state 1 with the head at cfg, B halts in `cost cfg`
steps at the next cfg' with the head advanced past a slot
separator", and an iteration count `n` plus a final-cfg with
terminator at head — total run length is
`Σ cost(cfg_i) + n + 1`, ending at the halt-accept state.

**Est diff.** ~800 LOC. Roughly comparable to
`branchComposeFlatTM` (which came in at ~1300 LOC). The proof
shape is the same template (basic accessors → validity →
halting-state lemmas → step lemmas → phase-run lemmas → main run
lemma).

**Triage point.** If `loopTM_run` exceeds 1000 LOC or doesn't
close in one session, fall back to hand-rolling each loop site in
11.5d and 11.6 and document the decision in §10. The cost
inflation if we fall back: ~2000 LOC × 3 loop sites = +6000 LOC.

**Checkpoint.** `lake build` clean; no new sorrys. The four
acknowledged sorrys from §2 remain.

### Substep status — Phase G remaining

The detailed per-substep plan is in §5 below. Quick table:

| Substep | What | Est LOC | Status |
|---------|------|---------|--------|
| 11.5a   | `advanceRightTM` + arch doc | ~300 | ✅ done |
| 11.5b   | `branchComposeFlatTM` + `_run_pos` + `_run_neg` | ~1300 | ✅ done (this session) |
| 11.5c   | `loopTM` + `_run` (Opt O2) | ~800 | ⏳ next |
| 11.5d   | `polarityClassifyTM`, `findVarInAssgnTM`, `writeOrBitTM` | ~600 | ⏳ |
| 11.5e   | `perLiteralEvalTM` + `_run` correctness | ~600 | ⏳ |
| 11.6    | Per-clause + per-CNF loops (uses 11.5c) | ~1200 | ⏳ |
| 11.7    | Time-bound proof | ~600 | ⏳ |
| 11.8    | Wire up `EvalCnfTM.decider` (closes sorry #1) | ~400 | ⏳ |

---

## 5. Phase G — finish Step 11

After 11.4c-cont closes sorry #3, the path to closing sorry #1
(`EvalCnfTM.decider`) has five remaining substeps. The v2 plan
estimated each at 500–1500 LOC; v3 applies two optimisations that
should cut the aggregate by ~30%.

### Optimisation O1 — unify mismatch run lemmas

v2 planned `_run_short`, `_run_long` as two further inductive lemmas
parallel to `_run_match`. Instead, expose a single

```lean
theorem compareUnaryAtMarkerTM_run
    … (s c : Nat) … :
  ∃ exit ∈ ({7, 8} : Set Nat),
    runFlatTM (s.max c * (2 * (M - p_LBM) + 1) + (M - p_LBM) + c + 3)
        (compareUnaryAtMarkerTM sig) initCfg =
      some { state_idx := exit, … } ∧
    (exit = 8 ↔ s = c)
```

The shared iteration loop (`compareUnaryAtMarkerTM_iteration_run`) is
identical for both match and mismatch; only the post-loop phase
diverges. Branching on `s < c` / `s = c` / `s > c` *after* the loop
costs ~200 LOC instead of ~1500 LOC for two parallel inductive
proofs.

### Optimisation O2 — `loopTM` outer combinator

Steps 11.5 / 11.6 each amount to "iterate sub-TM `B` until a
terminator symbol is read." Hand-rolling each as a state-by-state
machine repeats the same iteration bookkeeping that already cost ~600
LOC for `copyUnaryTM` and another ~600 LOC for `compareUnaryTM`. v3
front-loads a single

```lean
def loopTM (B : FlatTM) (entryState exitState : Nat)
    (terminator : Nat) : FlatTM := …
theorem loopTM_run (B : FlatTM)
    (h_body : ∀ cfg, … runFlatTM (cost cfg) B cfg = some cfg' ∧ …)
    (h_term : … the read symbol = terminator) :
    runFlatTM (n * cost_max + …) (loopTM B …) cfg = …
```

combinator under `TMPrimitives.lean`. With it, Steps 11.5 / 11.6
become "(a) build the body TM, (b) prove `h_body`, (c) instantiate
`loopTM_run`" — each in the 300–500 LOC range. We pay for `loopTM_run`
once (~800 LOC).

### Substeps

- **11.4c-cont** — `compareUnaryAtMarkerTM_post_loop_run` +
  `_run_match`. ✅ done (~430 LOC).
- **11.4d** — `compareUnaryAtMarkerTM_short_post_loop_run` +
  `_run_short` + `_long_post_loop_run` + `_run_long`. ✅ done
  (~1020 LOC). Three separate run lemmas rather than a single
  unified lemma — the optimisation O1 ("share the iteration loop")
  was *not* applied because each lemma's inductive step is ~100
  LOC of mostly-the-same proof and factoring would require
  rewriting the already-proved `_run_match`. Decision: leave
  as-is; the long-tail savings are not worth the refactor risk.
  The per-literal evaluator (Step 11.5d) will avoid dispatching
  to a specific `_run_*` lemma — instead it runs the full
  `compareUnaryAtMarkerTM` and reads the exit state (`7` =
  mismatch, `8` = match), which uniformly covers all three
  length cases.
- **11.5a** — `advanceRightTM` (one-cell rightward head movement,
  mirrors `writeAtHeadTM`) + `PerLiteral.lean` skeleton with
  comprehensive architecture docstring. The skeleton captures the
  three structural discoveries that forced a Step 11.5 rescope:
  (i) slot iteration needs `loopTM`; (ii) polarity-gated result
  bit needs `branchComposeFlatTM`; (iii) head restoration after
  the literal needs a deterministic terminator marker (likely
  cursor `11`, à la `copyUnaryTM`). ✅ done this session (~300
  LOC: ~150 in `Primitives.lean` for `advanceRightTM`, ~150 in
  `PerLiteral.lean` for the architecture doc).
- **11.5b** — `branchComposeFlatTM` + `_run_pos` + `_run_neg` in
  `TMPrimitives.lean`. Two-exit-state generalisation of
  `composeFlatTM`; chose two separate run lemmas (one per branch)
  rather than a unified theorem with a `which : Bool` parameter,
  since the `if which then` clutter in the conclusion would have
  been noisier than duplication. ✅ done this session
  (~1300 LOC). Came in higher than the ~600 LOC v3.1 estimate
  because (a) two bridge step lemmas (one per exit) instead of one,
  (b) two complete M₂/M₃ phase-run lemmas (each ~150 LOC), (c) a
  new `shiftEntries_find_eq_none_above` helper for dismissing
  shifted M₂ entries during the M₃ phase. The proof shape mirrors
  `composeFlatTM_run` exactly; no novel obstacles. The pattern
  generalises naturally to a k-exit version if a future per-clause
  / per-CNF dispatch needs three or more branches (none do today).
- **11.5c** — `loopTM` + `loopTM_run` in `TMPrimitives.lean` (Opt
  O2). State layout: `[check; body's states... offset by 1]`.
  Check-state transitions: on terminator → halt; on non-terminator →
  enter body (state 1). Body exits collapse back to check-state 0
  via re-mapped transitions. Run lemma is induction on the
  iteration count; each iteration calls the body's `_run`. ~800
  LOC. **Triage point**: if `loopTM_run`'s proof exceeds 1000 LOC
  or doesn't close in one session, fall back to hand-rolling each
  loop site in 11.5d and 11.6 (cost: ~2000 LOC × 2 per site, doubles
  Phase G's remaining estimate). Document the decision here.
- **11.5d** — Per-literal *components* (live in `PerLiteral.lean`):
  - `polarityClassifyTM` (3-state, reads sign byte `2`/`3` and
    advances right; halts in `posExit` or `negExit`).
  - `findVarInAssgnTM` (composes `loopTM` with body =
    `scanRightUntilTM(6)` + `compareUnaryAtMarkerTM` + a small
    "branch on exit" dispatch; exits in `MATCH` or `EXHAUST`).
  - `writeOrBitOneTM` (composes `scanRightUntilTM(9)` for OR-acc
    position + `writeAtHeadTM(1)` to write the OR-bit `1`).
  - `writeOrBitNoOpTM` (a 1-state TM that just halts; preserves
    OR-acc unchanged).
  - `restoreHeadAfterLiteralTM` (uses a cursor marker `11` planted
    on entry, scans left to it, erases it, halts).
  ~600 LOC.
- **11.5e** — `perLiteralEvalTM` final assembly + `_run`
  correctness. Composes the components from 11.5d into one TM via
  `branchComposeFlatTM` (polarity dispatch) and `composeFlatTM`
  links (everything else). Proves that on a well-formed input,
  the TM halts in `O((n+1)²)` steps with the head at the literal's
  end and the OR-acc updated correctly. ~600 LOC.
- **11.6** — Per-clause + per-CNF loops. Uses `loopTM` from 11.5c:
  (a) per-clause loop wraps `perLiteralEvalTM` with terminator =
  `4` (clause end), folds OR-acc into a single bit, writes that
  bit AND-style into AND-acc; (b) per-CNF loop wraps that with
  terminator = `5` (CNF end). Both loops also reset their
  respective accumulators on entry. ~1200 LOC.
- **11.7** — Time-bound proof: each variable lookup is O(|a|), each
  literal is O(|c|), each clause is O(|c|·|a|), the whole CNF is
  O(|N|·|c|·|a|) ≤ O((n+1)³). Close `decides_pos` / `decides_neg`
  against the existing `timeBound (n+1)^3`. ~600 LOC.
- **11.8** — Wire up `EvalCnfTM.decider`: instantiate the composed
  TM, prove validity by `composeFlatTM_valid` / `branchComposeFlatTM_valid`
  / `loopTM_valid` chain, prove the two `decides_*` obligations
  using the run lemmas from 11.6 + the time bound from 11.7.
  Closes sorry #1. ~400 LOC.

**Estimated total for Phase G** (after 11.5b): ~4400 LOC remaining
across 5–7 sessions. The rescope grew the substep count from 4 to 8
but shrank each individual session's load. Even with O1/O2 banked
in, this remains the largest piece of Part 2.

---

## 6. Phase H — Step 12 (`CliqueRelTM.decider`)

**Goal.** Close sorry #2 with a real FlatTM for the FlatClique
verifier predicate `fun ((G, k), l) => cliqueRel (G, k) l`.

**Reuses everything from Step 11.** Same alphabet bump pattern
(`sigClique = sigEval` or a superset), same `composeFlatTM_run`
composition, same `loopTM_run` outer combinator. The new primitives
needed:

- `equalUnaryTM` — special case of `compareUnaryAtMarkerTM` where one
  region is a single position. Used for `vertex ∈ edge endpoint`.
- `pairAdjCheckTM` — given two vertices on tape, scan the edge list
  for a matching pair. Linear in edge-list length.

### Substeps

- **12.0** — Input encoding `encodeFlatCliqueInput`: layout
  `[encode G.vertices] 4 [encode G.edges] 5 [k] 6 [encode l] 7
  [scratch]`. Length + symbol-bound lemmas. ~250 LOC.
- **12.1** — `equalUnaryTM` (4-state, `_run`). ~400 LOC.
- **12.2** — `pairAdjCheckTM` (composed: outer `loopTM` over edges,
  body = two `equalUnaryTM` calls). ~500 LOC.
- **12.3** — `nodupCheckTM`: outer `loopTM` over `l`, inner `loopTM`
  over `l`-tail, body = `equalUnaryTM` with reject on equal. ~500
  LOC.
- **12.4** — `lengthCheckTM`: tally `l`-positions, compare to encoded
  `k` via `equalUnaryTM`. ~250 LOC.
- **12.5** — `cliqueRelDecTM`: AND-fold of `nodupCheckTM` +
  `lengthCheckTM` + outer-`loopTM`-over-pairs-of-`l` with body =
  `pairAdjCheckTM`. Wire up `CliqueRelTM.decider`, prove time bound
  `(n+1)³`, close sorry #2. ~700 LOC.

**Estimated total for Phase H**: ~2600 LOC across 3–4 sessions.
Earlier the v2 estimate was 1900–2400 LOC — the v3 number rises
slightly because we deliberately route through `loopTM` (one more
primitive to wire) rather than re-deriving iteration in-place. The
trade is that 12.1–12.5 are short and uniform.

---

## 7. Phase I — Step 13: final sweep

**Goal.** Part 2 closes with *exactly* sorrys #4 (Part 3) and #5
(Part 6) remaining.

**Actions.**
- Run `grep -rn "sorry" CookLevin/Complexity` and verify only the two
  structural tags appear.
- `lake build` from scratch: clean.
- Update `README.md` sorry inventory.
- Update `ROADMAP.md` Part 2 status to ✅.
- Update `Outstanding sorrys` register in this file.

**Estimated diff.** ~30 LOC (README + this file).

---

## 8. Definition of done (Part 2)

- `inTimePoly` is TM-backed via `DecidesBy`. ✅ (Step 4)
- `sat_NP`, `FlatClique_in_NP` re-proved using concrete TM-backed
  witnesses. ✅ at the interface level; ⏳ until sorrys 1, 2 close.
- `red_inNP` builds; remaining gap is the labelled
  `TODO(Part3:red_inNP_TMcompose)`. ✅
- `P_NP_incl` builds. ✅
- `EvalCnfTM.decider` and `CliqueRelTM.decider` are real TMs with
  operational-correctness proofs. ⏳ (Steps 11.8 / 12.5)
- `hasDeciderClassical` is the only `TODO(Part 6)` sorry. ✅
- `README.md` updated; sorry inventory accurate.
- `theorem CookLevin : NPcomplete SAT` typechecks with exactly the
  two structural sorrys (Part 3, Part 6).

---

## 9. Design decisions (carried forward)

1. **Output convention.** Halting state index; `acceptState ≠
   rejectState` carried as an explicit field. `readOutput` is `decide
   (cfg.state_idx = acceptState)`.
2. **Input layout.** `initialTapes M input := input ::
   List.replicate (M.tapes - 1) []`. Definitionally `[input]` for
   single-tape TMs — single-tape proofs transport unchanged.
3. **TM construction = single-tape with delimiter scratch.** Forced
   by `entryMatchesConfig`'s lack of a wildcard:
   multi-tape composition needs `(sig+1)^k` bridge entries per
   composition. Single-tape is the only economical shape.
4. **Alphabet.** `sigEval = sigSAT + 5 = 12`. Symbols 7–10 are
   scratch markers (start, var-buf-end, OR-acc-sep, AND-acc-end);
   symbol 11 is a transient source cursor (written and erased inside
   `copyUnaryTM`). Inputs use only 0–6, so the symbol-bound lemma is
   `< 12` for the encoded portion and `≤ 10` for the initialised
   scratch.
5. **Interface-first migration.** TM constructions land as
   `sorry`-bodied `DecidesBy` *signatures* first so downstream
   consumers can rebuild immediately. Each such sorry carries a
   `TODO(Part2-followup:<Name>)` tag and appears in §2.
6. **Composition via `composeFlatTM_run`.** Hand-rolled monolithic
   state machines are forbidden for new primitives in Steps 11.4d+.
   Each new TM either is a small (≤ 9-state) building block with its
   own `_run` lemma, or is a composition expressed via
   `composeFlatTM_run` (or, when 11.6 lands, `loopTM_run`).
7. **File hygiene.** Each non-trivial TM lives in its own file under
   `Complexity/Complexity/Deciders/EvalCnfTM/` or
   `Complexity/Complexity/Deciders/CliqueRelTM/`. Soft cap 2500 LOC
   per file; split sub-files when exceeded (precedent: `CopyUnary.lean`
   was split out of `Primitives.lean` after Step 11.3c).
8. **Proof style.** Term mode preferred; `linarith` / `omega` only
   for arithmetic where the explicit chain would be a transparent
   distraction (e.g., resolving `Nat`-subtraction inside a position
   calculation). `ring` from Mathlib is fine and often the cleanest
   step in long arithmetic chains.
9. **Polarity is in the TM state, not in the scratch.** The
   per-literal evaluator's polarity bit (positive `2` vs negative
   `3`) is carried via the *exit state* of `polarityClassifyTM` and
   dispatched through `branchComposeFlatTM`. The alternative —
   adding a 1-cell `polarity` register to `scratchSuffix` — was
   rejected because it would cascade through every length /
   symbol-bound lemma and force `copyUnaryTM` and
   `compareUnaryAtMarkerTM`'s position arithmetic to be re-indexed.
   The state-encoded choice keeps the encoding stable and confines
   the polarity machinery to one new combinator (`branchComposeFlatTM`,
   Step 11.5b) plus a 3-state classifier. See `PerLiteral.lean`
   top-of-file docstring "Design choice 2" for the full trade-off.
10. **Composition combinators are landed in `TMPrimitives.lean`,
    instantiations in `PerLiteral.lean`.** Both `branchComposeFlatTM`
    (Step 11.5b) and `loopTM` (Step 11.5c) are generic over the
    sub-TMs and live alongside `composeFlatTM`. The per-literal
    components and final `perLiteralEvalTM` (Steps 11.5d/e) live in
    `PerLiteral.lean` and use the combinators as black boxes. This
    mirrors the rhythm we already use for `composeFlatTM` /
    `composeFlatTM_run` (in `TMPrimitives.lean`).

---

## 10. Risk register

- **Total remaining LOC for Phases G + H** is ~7400 across ~9–12
  sessions (revised after Step 11.5a's rescope). Two structural
  bets: (a) `branchComposeFlatTM` (Step 11.5b) follows the
  `composeFlatTM` template cleanly; (b) `loopTM_run` (Step 11.5c)
  closes in ~800 LOC. If (a) reveals state-mapping issues, the
  per-literal pipeline reverts to a polarity-as-scratch-cell encoding
  (cascades through length lemmas, adds ~400 LOC of bookkeeping but
  no new combinator). **Triage at the start of Step 11.5c**: spend at
  most 1 session attempting `loopTM_run`; if it isn't tractable, fall
  back to hand-rolling each loop site and document the decision here
  — Phase G then inflates to ~9500 LOC.
- **Step 11.5c (`loopTM_run`)** is the next major risk gate. The
  body's per-iteration `_run` lemma must thread tape-state changes
  through each iteration; if the changes don't admit a closed-form
  recurrence, the lemma blows up. Mitigation: design the body's
  `_run` lemma to be parametric in the iteration count (like
  `copyUnaryTM_iteration_run` was), so `loopTM_run` is plain
  induction on the count.
- **`encodable.size` of CNF / FlatClique inputs.** The
  `(n + 1)^3` time budget is generous; concrete cost of the SAT
  verifier is closer to `n²` and the FlatClique verifier is closer to
  `n²·log n`. We deliberately overshoot so the bookkeeping has slack.
- **Encoder coupling.** Both `EvalCnfTM` and `CliqueRelTM` already
  fix `encode := encodeInputWithScratch` / `encodeFlatCliqueInput`
  with proved length bounds. Changing them after Steps 11.4d+ would
  cascade through every step lemma; the choice is final unless a
  blocking issue surfaces.

---

## 11. Lessons learned (compact)

> The full v2 list was 160 lines; v3 keeps only the load-bearing
> patterns and quirks. Anything below has bitten us at least twice
> across Phases A–G.

### Lean toolchain quirks

- `getElem_map`, not `List.get_map`.
- `List.get ⟨k, h⟩ = l[k]'h` is `rfl`. Mix freely.
- `0 + k ≠ k` is not defeq; bridge via `Fin.eq_of_val_eq`. `rw
  [Nat.zero_add]` on a dependent `[k]'h` fails ("motive not type
  correct").
- `n + 1 + k` doesn't unfold against `runFlatTM`'s `(n+1)` pattern;
  reshape via `Nat.add_right_comm` to `(n + k) + 1` first.
- `decide` requires closed terms.
- `subst h_eq` eliminates the LHS; use `rw [h_eq]` when both names
  need to stay in scope.
- `simp at hx` doesn't unfold named `private def`s; manually
  decompose with `have hx' : … := hx; rw [List.mem_singleton] at hx'`
  + `subst`.
- `rw [List.find?_append]` leaves `Option.or`; follow with
  `Option.none_or`.
- `(a == b)` ≠ `Nat.beq a b` at default reducibility. Case-split on
  `cases hbeq : (… == …)`; the `false` branch closes by `rfl`, the
  `true` branch closes via `simpa using hbeq`.
- `set rIter := … with h_rIter_def` clashes with later `rw
  [h_rIter_def]` when a dependent length hypothesis exists.
  Workaround: extract a helper lemma parameterised over the abstract
  `rIter` (this is the resolution path for sorry #3).

### Proof patterns

- **`composeFlatTM_run` + `runFlatTM_compose` for chaining.** All
  multi-phase TM proofs decompose into "run phase 1 (a-many steps,
  end state X), run phase 2 from X (b-many steps, end state Y), …";
  the chaining is mechanical once each phase has its own `_run`
  lemma.
- **`runFlatTM_extend` for padding to a uniform time budget.** Once
  the actual run halts at `cfg'`, any extra `k` steps leave the
  config alone. Used everywhere to bridge from an exact step count
  to the decider's polynomial budget.
- **Per-state run-unfold helpers (`runFlatTM_<name>_state<N>_unfold`).**
  Lift `runFlatTM (n+1) M cfg` to `runFlatTM n M cfg'` after one
  step, hiding the `if haltingStateReached` / `match stepFlatTM`
  prelude. Pattern: one per non-halting state. ~20 LOC each.
- **Phase scan lemmas (`<name>_state<N>_phase_run`).** Each scans in
  one direction until a target match. Pattern: induction on the gap
  with the step lemma as the inductive case. ~50–100 LOC each.
- **Iteration-run lemma (`<name>_iteration_run`).** Chains the phases
  through one body of the outer loop. ~400–600 LOC. The bottleneck
  is *not* the chaining — it's translating hypotheses between
  pre-iteration, mid-iteration (cursor), and post-iteration (cursor
  erased + bit written) tape forms.
- **Main run lemma — induction over iterations.** Base case is the
  post-loop tail; inductive case is `iteration_run` + IH at shifted
  arguments. The 11.3c experience: factor a `<name>_post_loop_run`
  *parameterised by abstract tape* so the inductive step is clean.
- **`List.set_eq_take_append_cons_drop` + `List.getElem_set_ne`** to
  bridge between the take/cons/drop form (returned by
  `writeCurrentTapeSymbol` after a step) and the `right.set head sym`
  form (cleaner in positional reasoning).
- **`Fin.eq_of_val_eq`** when a position equation makes two `Fin
  L.length` indices propositionally equal but their `Nat` values
  differ syntactically. Use to coerce a `(L.get ⟨a, _⟩)` into
  `(L.get ⟨b, _⟩)` after proving `a = b`.
- **Helper-lemma extraction for dependent-position `rw`.** When a
  `rw [encodeAssgn_split]` fails inside `(encodeCnf N ++ encodeAssgn
  _)[L + k]'h`, extract the positional fact into a separate helper
  proved with `generalize h_gen : encodeAssgn (...) = enc at h_eq;
  subst h_eq`. The helper has no dependent context; the consumer
  invokes `rcases helper ...` to pull out the relevant `_get` fact.
- **Filter-range + `find_singleSomeEntry_match_state`** for the
  per-state transition tables. Building `s0_continue` etc. as
  `(List.range sig).filter (· ≠ targetSym).map (mkEntry)` keeps the
  table size manageable; the find-helper walks the filter
  inductively.

### Operational-correctness shape (the rhythm we use)

1. Define each transition entry as `private def …_entry`.
2. Define `<name>_trans` as a `++`-chain of entry blocks; define the
   TM. Prove `<name>_valid` by case analysis.
3. Per-state step lemmas — one per (state, symbol-class) combo. The
   per-state block helpers (`<name>_block_N_find_none`,
   `<name>_block_N_src_state`) let each step lemma skip over the
   non-matching prefix blocks with a single `rw`.
4. Halting lemmas — one per state.
5. Per-state run-unfold helpers (`runFlatTM_<name>_stateN_unfold`).
6. Phase scan lemmas — induction on the gap, one per scan direction
   per target symbol.
7. Iteration-run lemma — chains the phases through one outer-loop
   body.
8. Main run lemma — induction over iterations, calling
   `iteration_run` in the step and a post-loop helper at the base.
9. (Wire-up) Closure into the parent TM via `composeFlatTM_run` or,
   from Step 11.6, `loopTM_run`.

This is the rhythm. Step 11.5+ should follow it but with most of
steps 3–7 absorbed into the `loopTM` / composition machinery.
