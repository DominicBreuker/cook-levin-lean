# Part 2 — Implementation Plan & Progress Tracker

Tracks Part 2 of `ROADMAP.md` (lines 166–218): replace the propositional
`inTimePoly` / `HasDecider` with a Turing-machine-backed `DecidesBy`
witness, then re-prove `sat_NP`, `FlatClique_in_NP`, `red_inNP`, and
`P_NP_incl` against the new definition.

## Scope

- **P2.1** Replace `HasDecider` with TM-backed `DecidesBy`; redefine
  `inTimePoly`.
- **P2.2** Re-prove `sat_NP` (`Complexity/NP/SAT.lean:299`) and
  `FlatClique_in_NP` (`Complexity/NP/FlatClique.lean:84`) by
  constructing actual `FlatTM`s for `evalCnf` and `cliqueRel`.
- **P2.3** Re-prove `red_inNP` (`Complexity/Complexity/NP.lean:152`)
  by composing the reduction's TM with the certificate-checking TM.
  Cannot fully close before Part 3 lands `polyTimeComputable`; leave
  the composition gap as a labelled `sorry`.

**Out of scope:** `polyTimeComputable` (Part 3), TM bridges (Part 4),
Cook tableau (Part 5), `hasDeciderClassical` / `NPhard_GenNP` (Part 6).

## Design decisions

1. **Boolean output via halting state index.** `DecidesBy` carries
   distinct `acceptState`, `rejectState : Nat` (both halting); answer
   read as `decide (cfg.state_idx = acceptState)`.
2. **Multi-tape input layout.** `initialTapes M input := input ::
   List.replicate (M.tapes - 1) []`. For `M.tapes = 1` this reduces
   definitionally to `[input]` — single-tape proofs transport unchanged.
3. **`DecidesBy` is `Decidable`-free.** Split into `decides_pos` /
   `decides_neg`; an extra `accept_ne_reject` field carries the
   distinctness needed for the downgrade theorem.
4. **Migration discipline.** New code lives alongside old definitions;
   only Step 8 swaps `inTimePoly` and lets the old API go.
5. **Proof style.** Term-mode over `linarith` / `omega`; `ring` from
   Mathlib is acceptable for arithmetic chains.

## Phase plan

| Phase | Steps | Goal                                  | Status     |
|-------|-------|---------------------------------------|------------|
| A     | 1–2   | Foundation: structure + encoding      | ✅ done     |
| B     | 3–5   | TM combinator library                 | ✅ done     |
| C     | 6–7   | Concrete deciders (SAT, Clique)       | 🚧 step 6   |
| D     | 8–13  | Migration & re-proofs                 | ⏳ pending  |
| —     | 14    | Validation & sorry audit              | ⏳ pending  |

## Step tracker

### Phase A — Foundation ✅

- ✅ **Step 1** — `DecidesBy` structure + output convention.
  `Complexity/Complexity/TMDecider.lean`. Fields: `encode`,
  `encode_size`, `M`, `M_valid`, `M_tapes_pos`, `acceptState`,
  `rejectState`, halting bits, `accept_ne_reject`, `decides_pos`,
  `decides_neg`. Plus `DecidesBy.decideFn`,
  `DecidesBy.decideFn_correct`, `HasDecider.of_DecidesBy`,
  `inTimePoly_of_inTimePolyTM`.
- ✅ **Step 2** — Tape encoding helpers.
  `Complexity/Complexity/TMEncoding.lean`. `shiftSyms`, `encodePair`,
  `encodeList`, length lemmas, `listNat_length_le_size`.

### Phase B — TM combinator library ✅

- ✅ **Step 3** — `composeFlatTM` (data + validity). Bridge entries
  + state-renaming; operational correctness deferred to per-decider
  need (none has needed it yet — we hand-roll instead).
- ✅ **Step 4** — Atomic Bool-output TMs. `verdictTM (sig) (verdict)`
  3-state machine; smoke-tested via `trueDecider X` / `falseDecider X`.
- ✅ **Step 5** — Tape scanners. `scanRightUntilTM sig target` with
  full `_run_found` and `_run_not_found` operational correctness.
  Plus `runFlatTM_extend` (halt-then-pad).

### Phase C — Concrete deciders 🚧

**Step 6 — `evalCnfTM`** is split into multiple substeps. We've been
building up a tower of stepping-stone deciders, each adding one new
capability needed for the eventual `evalCnfTM`:

| Sub | Decider                  | Predicate                            | New technique introduced                       |
|-----|--------------------------|--------------------------------------|------------------------------------------------|
| 6.0a| `AllFalse.decider`       | `∀ b ∈ bs, b = false`                | End-to-end `DecidesBy` example                 |
| 6.0b| `ExistsTrue.decider`     | `∃ b ∈ bs, b = true`                 | Sharing helpers across deciders                |
| 6.0c| SAT input encoding       | (encoder, not a decider)             | `sigSAT = 7` alphabet + linear size bound      |
| 6.0d| Multi-tape framework     | (framework change)                   | `M_tapes_pos`, `initialTapes` helper           |
| 6.0e| `CnfEmpty.decider`       | `N = []`                             | First SAT-input decider (1-step, read pos 0)   |
| 6.0f| `CnfEmptyAssgnEmpty`     | `N = [] ∧ a = []`                    | Multi-step run with `Rmove`; state-1 lemmas    |
| 6.0g| `AssgnEmpty.decider`     | `a = []`                             | Inductive scan-loop walking past `encodeCnf N` |
| 6.0h| `CnfStartsEmpty.decider` | `Na.1.head? = some []`               | Symbol-`4` accept; `head?`-shaped predicate    |
| 6.0i| `DecidesBy.negate/iff`   | (combinators, not deciders)          | Same TM decides `¬ P` / equivalent `Q`         |
| 6.0j| `CnfNonempty.decider`    | `Na.1 ≠ []`                          | `.negate` example — no new TM needed           |
| 6.0k| `AssgnNonempty.decider`  | `Na.2 ≠ []`                          | `.negate` example — same time bound `n + 2`    |
| 6.0l| `.iff`-derived deciders  | cons-forms; `length = 0`             | `.iff` examples — 3 predicates, no new TM      |
| 6.0m| `CnfOrAssgnNonempty`     | `Na.1 ≠ [] ∨ Na.2 ≠ []`              | `.negate` + `.iff` chain — disjunction for free |
| 6.0n| `CnfHasEmptyClause`      | `∃ c ∈ Na.1, c = []`                 | First **multi-state walker** (alternating s0/s1, prototype for `evalCnfTM`'s outer loop) |
| 6.0o| `AssgnContainsZero`      | `0 ∈ Na.2`                           | **3-state assignment walker** (state 0 CNF, state 1 ready/accept-6, state 2 in-variable) — prototype for variable lookup |
| 6a  | `evalCnfTM` validity     | (skeleton)                           | —                                              |
| 6b  | `evalCnfTM` time bound   | —                                    | —                                              |
| 6c  | `evalCnfTM` correctness  | `satisfiesCnf a N`                   | —                                              |

All of 6.0a–6.0o are landed (zero sorrys). 6a–6c are the next session's
target.

**Step 7 — `cliqueRelDecTM`** decides `cliqueRel ((G, k), l)` for
FlatClique. Three sub-checks (`fgraph_wf`, `isfClique`, `l.length = k`);
re-uses scanners from Step 5; `Nodup` is the only quadratic-time piece.
Pending; estimated 300–500 LOC.

### Phase D — Migration & re-proofs ⏳

- **Step 8** Swap the definition of `inTimePoly` in `NP.lean`. Delete
  `HasDecider`; promote `inTimePolyTM` to canonical `inTimePoly`.
  Expected to break: `sat_NP`, `FlatClique_in_NP`, `red_inNP`,
  `P_NP_incl`, `hasDeciderClassical` — fixed in 9–13.
- **Step 9** Re-prove `sat_NP` using the Step 6 witness.
- **Step 10** Re-prove `FlatClique_in_NP` using the Step 7 witness.
  Delete `cliqueRelDec` (noncomputable).
- **Step 11** `red_inNP` partial fix. Refactor; the TM-composition
  piece becomes a single `TODO(Part 3) sorry`.
- **Step 12** `P_NP_incl` partial fix via a `decidesBy_proj_left`
  combinator (no Part 3 dependency).
- **Step 13** `hasDeciderClassical` → `sorry` with `TODO(Part 6)`.
- **Step 14** Validation: `lake build` clean; `grep -rn sorry` returns
  exactly the two queued sorries (Part 3, Part 6); update `README.md`.

## Files

New under `Complexity/Complexity/`:
- `TMDecider.lean` — `DecidesBy`, `inTimePolyTM`, downgrade.
- `TMEncoding.lean` — list-level encoding helpers.
- `TMPrimitives.lean` — `composeFlatTM`, `verdictTM`,
  `scanRightUntilTM`, `runFlatTM_extend`; `AllFalse`, `ExistsTrue`
  warm-up deciders.
- `Deciders/SAT_TM.lean` — SAT input encoding + step-6 deciders
  (`CnfEmpty`, `CnfEmptyAssgnEmpty`, `AssgnEmpty`, `CnfStartsEmpty`,
  `CnfNonempty`, `AssgnNonempty`, `CnfHasEmptyClause`, and eventually
  `evalCnfTM`).

Registered in `Complexity.lean`.

Current line counts: `TMDecider.lean` ~219, `TMEncoding.lean` ~134,
`TMPrimitives.lean` ~1394, `SAT_TM.lean` ~6415.

## Lessons learned (consolidated)

### Lean toolchain quirks

- **`getElem_map` (not `List.get_map`).** Current Mathlib uses the
  `getElem`-style indexing; `List.get_map` doesn't exist.
- **`List.get ⟨k, h⟩ = l[k]'h` is `rfl`.** Mix freely between styles.
- **`0 + k ≠ k` definitionally.** `Nat.zero_add` is a theorem, not a
  defeq. When a scanner returns `head + k` and we want `head := 0`,
  bridge via `Fin.eq_of_val_eq (Nat.zero_add k)` to rewrite the whole
  `⟨…, …⟩` index in one go (`rw [Nat.zero_add]` on a dependent
  `[k]'h` fails with "motive not type correct").
- **`n + 1 + k` doesn't unfold against `runFlatTM`'s `(n+1)`
  pattern.** Reshape via `Nat.add_right_comm` to `(n + k) + 1` first.
- **`decide` needs closed terms.** Fails on goals with free
  variables ("`0 < (x :: rest).length`", "`none ≠ some _`"). Use the
  underlying constructor (`Nat.zero_lt_succ _`, `cases h`) instead.
- **`subst h_eq` direction.** With `h_eq : cfg = cfg_mid` and both
  sides local, `subst` eliminates the LHS — references to `cfg_mid`
  afterwards become "Unknown identifier". Use `rw [h_eq]` if you
  need to keep both names in scope.
- **`simp at hx` doesn't unfold named `def`s.** When `hx : x ∈ entry.src_tape_vals`
  has `entry` bound to a `private def`, `simp` makes no progress.
  Workaround: `have hx' : x ∈ ([sym] : List (Option Nat)) := hx;
  rw [List.mem_singleton] at hx'; subst hx'`.
- **`encodable.size (N, [])` after `subst ha`.** Lean loses the type
  of the empty list; spell as `encodable.size (N, ([] : assgn))`.
- **Type-annotated `show`.** Top-level structure literals in `show`
  may need an explicit `: Option FlatTMConfig`.
- **`rw [List.find?_append]` leaves `Option.or`.** Follow with
  `Option.none_or` to collapse `none.or _` to `_`.

### Proof patterns we now reach for

- **`ring` for arithmetic chains.** Faster than stacking
  `Nat.add_assoc`/`add_comm` even under term-mode preference — the
  generated term is short (a single `ring_nf` application).
- **`runFlatTM_of_halting` for the post-halt tail.** Once a config
  halts, `runFlatTM k cfg = some cfg` for any `k`. Cleaner than
  unfolding `runFlatTM` by hand.
- **`runFlatTM_extend` (halt-then-pad) + `runFlatTM_extend_by_step`
  (non-halt-then-one-step).** Together they cover any
  "scan → finish → pad" pattern.
- **Definitional equality for backward-compat extensions.** Adding
  multi-tape support didn't break single-tape proofs because
  `List.replicate 0 [] = []` is `rfl`.
- **Sharing helpers via `open Namespace (name1 name2 …)`.** Cleaner
  than re-stating shared encoder lemmas across parallel deciders.
- **`Nat.find` for constructive extraction.** Used in `AllFalse` /
  `ExistsTrue` to extract the first index with a given property.
- **Filtered-range transition tables.** Building `s0_continue`,
  `s0_reject_symbol`, etc. as `(List.range sigSAT).filter (...).map`
  keeps the transition table size manageable; the `find?` proof
  then walks the filter inductively via a per-block helper.
- **`DecidesBy.negate` for negated predicates.** One decider for `P`
  doubles as a decider for `¬ P` (swap accept/reject states). Needs
  `[DecidablePred P]` to turn `¬ ¬ P x` back into `P x`. Same TM, same
  time bound, ~30 LOC per derived decider.
- **`DecidesBy.iff` for predicate-equivalence transport.** If
  `∀ x, P x ↔ Q x`, any `DecidesBy P f` becomes a `DecidesBy Q f`
  without touching the TM. Useful when the natural Lean spelling
  (`Na.1.head? = some []`) differs from the more convenient one
  (`∃ rest, Na.1 = [] :: rest`).
- **`.negate ∘ .iff` chains** turn a single TM into a family of
  related deciders. Example: `CnfEmptyAssgnEmpty.decider`
  (predicate `Na.1 = [] ∧ Na.2 = []`) → via `.negate` → decider for
  `¬ (Na.1 = [] ∧ Na.2 = [])` → via `.iff` with De Morgan → decider
  for `Na.1 ≠ [] ∨ Na.2 ≠ []`. One TM, one time bound, four predicates.
- **`runFlatTM_compose` for general run composition.** Chains two
  `runFlatTM` runs of arbitrary lengths via induction on the first
  length. Handles stuck (`step = none`) configs uniformly via
  `runFlatTM_stuck`. Lets `TM_run_walk_clauses` recurse on the tail
  of a CNF without manually shimming the per-clause walker into the
  per-list walker.
- **`generalize + subst` for nested-`Fin`-index `rw`s.** When
  rewriting a list equation `L = L'` fails inside `(L)[i]'h` because
  `h : i < L.length`'s motive isn't type-correct, the workaround is:
  `generalize h_gen : L = enc at h_eq ⊢; subst h_eq`. After this,
  the goal is `enc[i]'(now in terms of L')` — no motive, free to
  `rw` further.
- **`List.getElem_concat_length` for the trailing singleton.**
  `(l ++ [a])[l.length] = a` — but Lean wants you to pin down `l`
  and `a` by passing the inequality `w : i < (l ++ [a]).length` as a
  second explicit argument. Avoids the `Nat.sub_self` motive trap
  that `getElem_append_right` + `rw` falls into.
- **`simp only [Nat.add_sub_cancel_left]` collapses `a + b - a`.**
  After `rw [List.getElem_append_right (Nat.le_add_right _ _)]`, the
  index becomes `L_cnf + k - L_cnf` in a dependent position. Plain
  `rw [show ... = k from h_sub]` fails (motive). `simp only` handles
  the dependent rewrite via its motive analysis. Use this when the
  arithmetic is `a + b - a = b` after an append-right rewrite.
- **`show ... = false from rfl` for state-mismatched entries.**
  When walking `find?` through transition entries whose `src_state`
  differs from the configuration's `state_idx`, the match check
  reduces to `(s == s') && _` where `(s == s')` is literal `false`.
  So `entryMatchesConfig entry cfg = false` is `rfl`. Skip via
  `rw [List.find?_cons, show ... = false from rfl]`. No need for a
  generic helper; inline `rfl` is enough.
- **Helper-lemma extraction for dependent-position `rw [h_enc_eq]`.**
  When `rw [encodeAssgn_split = ...]` fails motive inside
  `(encodeCnf N ++ encodeAssgn (...))[L_cnf + L_walk]'h`, factor the
  positional fact into a separate helper proved with
  `generalize h_gen : encodeAssgn (...) = enc at h_eq; subst h_eq`.
  The helper has no dependent context, so the substitution succeeds;
  the consumer just invokes `rcases helper ... with ⟨_, h_get⟩` and
  uses `h_get` after `getElem_append_right + simp [Nat.add_sub_cancel_left]`.

### Operational-correctness shape for hand-rolled deciders

The pattern that's emerged for SAT-input deciders in `SAT_TM.lean`:

1. Define `TM : FlatTM` with explicit transition entries (filter-range
   when the set is large).
2. Prove `TM_valid` by case analysis on every transition.
3. Define each entry as a `private def …_entry` so step lemmas can
   reference it.
4. Prove `TM_step_*` lemmas — one per (state, symbol-class) combo.
   Each shows `find?` walks past every non-matching prefix entry,
   then hits the right one via a find-helper.
5. For loops, prove an inductive run lemma (`TM_run_scan_to_5`).
6. Encoding facts: lift positional facts from `encodeCnf` / `encodeAssgn`
   to `encodeInput` via `getElem_append_left` / `_right`.
7. Decider: chain `run_X` → `TM_step_Y` → `runFlatTM_extend_by_step`
   → `runFlatTM_extend` to pad to the uniform time budget.

## Risks & open questions

- **`evalCnfTM` time bound.** Each variable lookup scans the
  assignment once, so the naive bound is `O(|N| · |a|)` — cubic in
  encoded input size. Polynomial is all we need.
- **State-renaming in `composeFlatTM`.** Operational correctness
  postponed; if a decider ever needs it, write a `relabelEntry`
  helper with a single `entryMatchesConfig` lemma.
- **`instEncodableDefault` (Part 1 cleanup).** Part 2 doesn't add
  uses; if a `DecidesBy` proof accidentally relies on it (via
  `size = 0`), catch it.

## Definition of done

- `inTimePoly` is TM-backed; `DecidesBy` witnesses make this
  unmistakeable.
- `sat_NP` and `FlatClique_in_NP` re-proved with concrete `FlatTM`s.
- `red_inNP` and `P_NP_incl` build; remaining gap is a single
  `TODO(Part 3) sorry`.
- `hasDeciderClassical` is the only `TODO(Part 6) sorry`.
- `README.md` updated.
- Cook–Levin chain `theorem CookLevin : NPcomplete SAT` still
  typechecks (now resting on the two labelled `sorry`s — which were
  *already* the underlying issues; Part 2 just exposes them
  honestly).
