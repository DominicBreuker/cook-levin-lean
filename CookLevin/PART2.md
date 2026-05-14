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
| 6a  | `evalCnfTM` validity     | (skeleton)                           | —                                              |
| 6b  | `evalCnfTM` time bound   | —                                    | —                                              |
| 6c  | `evalCnfTM` correctness  | `satisfiesCnf a N`                   | —                                              |

All of 6.0a–6.0g are landed (zero sorrys). 6a–6c are the next session's
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
  (`CnfEmpty`, `CnfEmptyAssgnEmpty`, `AssgnEmpty`, and eventually
  `evalCnfTM`).

Registered in `Complexity.lean`.

Current line counts: `TMDecider.lean` ~158, `TMEncoding.lean` ~134,
`TMPrimitives.lean` ~1394, `SAT_TM.lean` ~2997.

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
