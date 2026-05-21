# Part 2 — Implementation Plan & Progress Tracker (v3)

Tracks Part 2 of `ROADMAP.md` (lines 166–218): replace the
propositional `inTimePoly` / `HasDecider` with a Turing-machine-backed
witness, then re-prove `sat_NP`, `FlatClique_in_NP`, `red_inNP`, and
`P_NP_incl` against the new definition.

> **v3 (this revision).** Status sweep + compaction. The v2 pivot —
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
| G     | 11.5–8  | Step 11 finish: per-literal, per-clause, per-CNF loops; time bound; `decider` | ⏳ pending |
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
  7 helper lemmas; `verdictTM`, `scanRightUntilTM`,
  `runFlatTM_extend`. ~2100 LOC.
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

The full architecture and design rationale (alphabet, tape layout,
state machines, cursor marker) live in the docstrings of those files;
this plan does not duplicate them.

---

## 4. Active step: 11.5 (next session)

**Goal.** Build the **per-literal evaluator TM**: given the head at
the start of a literal `(b, v)` in a clause, copy the variable
index `v` into the var-buffer, scan the assignment region for a
matching unary slot, and write the polarity-vs-match result into the
OR-accumulator.

**Background.** With Step 11.4 complete, `compareUnaryAtMarkerTM` has
three operational-correctness lemmas covering all three exit
states (match → 8, short → 7 at varbuf, long → 7 at slot). Together
with `copyUnaryTM`, `scanRightUntilTM`, `scanLeftUntilTM`,
`writeAtHeadTM`, and `clearRegionTM`, the per-literal evaluator can
be composed via `composeFlatTM_run`.

**11.5 sketch.** Per-literal evaluator pipeline (each step a
`composeFlatTM_run` link):
1. `scanRightUntilTM` to position the head at the literal's value
   marker (sign byte `2`/`3` followed by unary `v`).
2. Read the sign byte; case-split into two parallel sub-pipelines
   (positive literal vs negative literal).
3. `copyUnaryTM` to copy `v` into the var-buffer.
4. `scanLeftUntilTM` + assignment-region scan to find the first
   slot `(LBM, 1^k, RBM)` whose `k`-value matches `v`.
5. `compareUnaryAtMarkerTM` against that slot.
6. Based on the exit state (8 = match, 7 = mismatch) and the
   polarity sign, write `0` or `1` into the OR-accumulator slot
   (via `writeAtHeadTM`).
7. `clearRegionTM` to wipe the var-buffer for the next literal.

**Estimated diff.** ~1500 LOC, dominated by step 4 (an outer scan
over slots, where each slot needs an inner length-determination step
to set up `compareUnaryAtMarkerTM`'s parameters). May spill into
two sessions.

**Checkpoint.** `lake build` clean; no new sorrys. The
`evalCnfTM_decider` and `cliqueRelDecTM_decider` sorrys remain (they
close in Steps 11.8 and 12.5 respectively).

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
  `_run_short` + `_long_post_loop_run` + `_run_long`. ✅ done this
  session (~1020 LOC). Three separate run lemmas rather than a
  single unified lemma — the optimisation O1 ("share the iteration
  loop") was *not* applied because each lemma's inductive step is
  ~100 LOC of mostly-the-same proof and factoring would require
  rewriting the already-proved `_run_match`. Decision: leave as-is;
  the long-tail savings are not worth the refactor risk. The
  per-literal evaluator (Step 11.5) will dispatch to one of the
  three based on comparing slot length vs varbuf length.
- **11.5** — Per-literal evaluator TM. Composes `copyUnaryTM` (copy
  literal's variable index into var-buffer) → `scanRightUntilTM`
  (advance to assignment slot) → `compareUnaryAtMarkerTM` (compare
  var-buffer to slot) → `writeAtHeadTM` (OR polarity into OR-acc) →
  `clearRegionTM` (reset var-buffer). All compositions via
  `composeFlatTM_run`. ~1500 LOC.
- **11.6** — Land `loopTM` + `loopTM_run` (per O2) under
  `TMPrimitives.lean`. Then build (a) outer-clause loop using
  `loopTM` with body = per-literal evaluator, terminator = `4`
  (clause sep); (b) outer-CNF loop wrapping (a) with terminator = `5`
  (CNF end), folding OR-acc into AND-acc each iteration. ~2000 LOC
  (800 for `loopTM_run`, 1200 for the two instantiations).
- **11.7** — Time-bound proof: each variable lookup is O(|a|), each
  literal is O(|c|), each clause is O(|c|·|a|), the whole CNF is
  O(|N|·|c|·|a|) ≤ O((n+1)³). Close `decides_pos` / `decides_neg`
  against the existing `timeBound (n+1)^3`. ~600 LOC.
- **11.8** — Wire up `EvalCnfTM.decider`: instantiate the composed
  TM, prove validity by `composeFlatTM_valid` chain, prove the two
  `decides_*` obligations using the run lemmas from 11.6 + the time
  bound from 11.7. Closes sorry #1. ~400 LOC.

**Estimated total for Phase G** (after 11.4c-cont): ~5100 LOC across
4–6 sessions. v2's original estimate was ~3500 LOC across 3–5
sessions (excluding 11.4c); the difference is realism after the
copyUnary/compareUnary experience plus the cost of building
`loopTM_run`. Even with O1/O2, this remains the largest piece of
Part 2.

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

---

## 10. Risk register

- **Total remaining LOC for Phases G + H** is ~7700 across ~7–10
  sessions, assuming O1 and O2 work as designed. If `loopTM_run`
  turns out to be intractable (e.g. needs a 5-tape state encoding to
  thread sub-state across iterations), Phase G reverts to per-loop
  hand-rolling and the estimate inflates to ~10000 LOC. **Triage at
  the start of Step 11.6**: spend at most 1 session attempting
  `loopTM_run`; if it isn't tractable, fall back to hand-rolling and
  document the decision here.
- **Step 11.4c-cont** is the unblocking step. If the `post_loop_run`
  refactor doesn't resolve the motive issue, the fallback is to
  inline the post-loop phase inside `_run_match` (no `set`, longer
  proof). Either way the work caps at ~1500 LOC.
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
