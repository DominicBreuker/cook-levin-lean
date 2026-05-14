# Part 2 — Implementation Plan & Progress Tracker

This file tracks our work on Part 2 of `ROADMAP.md` (lines 166–218):
strengthening the framework so that `inTimePoly` and `inNP` genuinely
mean "decided by a polynomial-time Turing machine", rather than "decided
by some `X → Bool` function with a phantom time bound".

The plan is split into **four phases** and ~13 small **steps**. Every
step ends with `lake build` succeeding. Steps are small enough to
complete in a single session.

## Scope

Part 2 must accomplish three things, taken verbatim from the roadmap:

- **P2.1** Replace `HasDecider` with a TM-backed `DecidesBy` structure;
  redefine `inTimePoly` to use it.
- **P2.2** Re-prove `SAT_inNP.sat_NP` (`Complexity/NP/SAT.lean:299`)
  and `FlatClique_in_NP` (`Complexity/NP/FlatClique.lean:84`) against
  the new definition. This is the bulk of the new work: it requires
  constructing real `FlatTM`s that decide `evalCnf` and `cliqueRel`.
- **P2.3** Re-prove `red_inNP` (`Complexity/Complexity/NP.lean:152`)
  by composing the reduction's TM (Part 3) with the certificate-
  checking TM. **NOTE:** As written, P2.3 cannot be fully discharged
  before Part 3 lands, because `polyTimeComputable` is still
  output-size-only. Our plan completes the *structural* part in Part 2
  and leaves the "compose with reduction's TM" gap as a clearly
  labelled `sorry` until Part 3.

## Out of scope

- `polyTimeComputable` (Part 3).
- TM bridges `LM_to_mTM`, `mTM_to_singleTapeTM` (Part 4).
- Cook tableau (Part 5).
- Rebuilding `NPhard_GenNP` / removing `hasDeciderClassical` (Part 6).
  We *will* leave it on `sorry` once the `inTimePoly` rug is pulled —
  that is fine and expected; Part 6 fixes it.

## Design decisions (fixed at the start of Phase A)

1. **Boolean output convention.** A TM decider's answer is read from
   its halting state index. We require halting states to be either an
   `acceptState : Nat` (output `true`) or a `rejectState : Nat` (output
   `false`). `readOutput cfg := decide (cfg.state_idx = M.acceptState)`.
   `acceptState` and `rejectState` are fields of the `DecidesBy`
   witness, so each decider can choose its own.

2. **Input encoding.** A `DecidesBy P f` witness includes an
   `encode : X → List Nat` and uses the **single-tape** convention
   `initFlatConfig M [encode x]`. Multi-tape conveniences come later.
   We bound `(encode x).length ≤ c * encodable.size x + c'` for
   constants `c, c'`.

3. **Pair / list encoding on tape.** We pick the simplest possible
   delimiter encoding: reserve symbol `0` as a delimiter, shift all
   payload symbols by `+1`. Pairs `(x, y)` are encoded as
   `encode x ++ [0] ++ encode y`. Lists `[x₁, …, xₙ]` are
   `0 :: shifted x₁ ++ [0] ++ shifted x₂ ++ … ++ [0] ++ shifted xₙ ++ [0]`.

4. **Migration discipline.** New definitions live in **new files**
   alongside the old ones. Only at Step 8 do we delete the old
   `HasDecider` / `inTimePoly` and switch every consumer over in one
   sweep. This keeps every intermediate build green.

5. **Proof style.** Per repository convention we prefer explicit
   term-mode proofs and avoid `linarith` / `omega` where a direct
   `Nat.add_le_add` / `Nat.le_trans` chain works.

## Estimated effort

| Phase | Description                          | Steps  | LOC  |
|-------|--------------------------------------|--------|------|
| A     | Foundation (structure, encoding)     | 1–2    | ~200 |
| B     | TM combinator library                | 3–5    | ~800 |
| C     | Concrete deciders (SAT, Clique)      | 6–7    | ~700 |
| D     | Migration & re-proofs                | 8–13   | ~400 |
| **Total** |                                  | **13** | **~2100** |

---

## Phase A — Foundation

### Step 1 — `DecidesBy` structure + output convention ✅
**File:** new — `Complexity/Complexity/TMDecider.lean`.

Done. Final shape (deviates from the original sketch where noted):

- `readOutput (acceptState : Nat) (cfg : FlatTMConfig) : Bool`
  := `decide (cfg.state_idx = acceptState)`.
- `structure DecidesBy P timeBound` with fields
  `encode`, `encode_size`, `M`, `M_valid`, `acceptState`, `rejectState`,
  `halting_acc`, `halting_rej`, **`accept_ne_reject`**,
  `decides_pos`, `decides_neg`.
- **Deviation 1:** Added `accept_ne_reject : acceptState ≠ rejectState`.
  Without it, the downgrade theorem cannot derive `False` from "the
  TM ran but the answer disagrees with `P x`": with `accept = reject`
  the witness carries no information. Adding the distinctness fact
  is mathematically free (any TM that has informative output already
  uses distinct codes).
- **Deviation 2:** Split `decides` into two fields `decides_pos` /
  `decides_neg` so the structure does not need to assume
  `Decidable (P x)`. The two branches together are logically
  equivalent to the original single-`if` statement.
- `inTimePolyTM P := ∃ f, Nonempty (DecidesBy P f) ∧ inOPoly f ∧ monotonic f`.
- `DecidesBy.decideFn` extracts a `Bool` decider; proved
  `DecidesBy.decideFn_correct`, `HasDecider.of_DecidesBy`, and
  `inTimePoly_of_inTimePolyTM`.
- File registered in `Complexity.lean`; `lake build` green.

### Step 2 — Tape encoding helpers ✅
**File:** new — `Complexity/Complexity/TMEncoding.lean`.

Done. Pure list arithmetic — no TMs constructed here. Exposes:

- `shiftSyms : List Nat → List Nat` and its length/append lemmas.
- `encodePair xs ys := xs ++ 0 :: ys`, with `encodePair_length`.
- `encodeList : List (List Nat) → List Nat`, with `encodeList_length`.
- `listNat_length_le_size`: `xs.length ≤ encodable.size xs`.

**Deviation:** Did not yet define a type-class-polymorphic
`encodeTape : (X × Y) → List Nat`. The downstream deciders (SAT,
FlatClique) call `encodePair` on already-shifted `List Nat` words, so
the polymorphic wrapper is unnecessary at this stage. We may add it
later in Phase C if a use case appears.

---

## Phase B — TM combinator library

### Step 3 — Sequential composition `composeFlatTM` ✅ (data + validity)
**File:** new — `Complexity/Complexity/TMPrimitives.lean`.

Done at the data-definition + validity level. The operational-
correctness lemma (`runFlatTM`-tracing across the bridge) is **not yet
proved**; we will introduce it on demand when Steps 6/7 need it.

Implementation:
- `bridgeEntries sig srcState dstState` builds `sig + 1` "wildcard"
  transitions (one for each tape-symbol `none, some 0, …, some (sig-1)`)
  going from `srcState` to `dstState` with no write or move.
- `shiftEntry offset entry` shifts a transition's source/destination
  state by `offset`.
- `composedHalt M₁ M₂ := replicate M₁.states false ++ M₂.halt`. All of
  `M₁`'s halt bits become `false`; only the shifted `M₂` halts remain.
- `composeFlatTM M₁ M₂ exit` = bridge ++ M₁.trans ++ shifted M₂.trans,
  with `sig := max M₁.sig M₂.sig`, `tapes := M₁.tapes`, `states := M₁.states + M₂.states`, `start := M₁.start`, halt as above.
- Lemmas proved: `composeFlatTM_{states,start,tapes,sig}`,
  `composedHalt_length`, `composeFlatTM_halt_length`,
  `bridgeEntries_mem`, and the headline
  `composeFlatTM_valid` (assuming both machines are valid,
  `exit < M₁.states`, and both are single-tape).

**Deviation:** Operational correctness (`runFlatTM (n₁+n₂+1) composed = …`)
postponed. The validity-only milestone keeps the build green and lets
us put real machines together; we'll prove operational correctness
per-decider when we actually need it, rather than upfront in maximum
generality.

### Step 4 — Atomic Bool-output TMs ✅
**File:** extend `Complexity/Complexity/TMPrimitives.lean`.

Done. Merged "always accept" and "always reject" into a single
parameterised `verdictTM (sig : Nat) (verdict : Bool)` to avoid code
duplication.

- `verdictTM sig verdict`: 3-state, single-tape FlatTM. state 0 =
  start (non-halting), state 1 = accept-halt, state 2 = reject-halt.
  Bridge transition from state 0 (for any tape symbol, including
  `none`) routes to state 1 (if `verdict`) or state 2 (otherwise).
- `verdictTM_valid`, `verdictTM_run_one`,
  `verdictTM_finalConfig`, `verdictTM_finalConfig_state`,
  `verdictTM_finalConfig_halting` all proved by `decide`/`rfl`.
- **Smoke tests:** `trueDecider X : DecidesBy (fun _ : X => True) (fun _ => 1)`
  and `falseDecider X : DecidesBy (fun _ : X => False) (fun _ => 1)`
  fully constructed. These demonstrate the framework is non-vacuous.

**Deviation:** Did *not* yet build `ifSymbolTM` (a runtime tape-symbol
branch). The deciders for SAT and FlatClique need it; we'll add it
when Step 6 needs it rather than upfront in maximum generality.

### Step 5 — Tape scanners and segment ops ✅ (for `scanRightUntilTM`)
**File:** extend `Complexity/Complexity/TMPrimitives.lean`.

The deciders need very little tape-manipulation power. We build only
what `evalCnf` / `cliqueRelDec` require.

- ✅ `scanRightUntilTM sig target` — walk head right until the
  current symbol is `some target`; halt in state 1 on match, state 2
  on end-of-tape. 3 states, `sig + 2` transitions. Validity proved
  (assuming `target < sig`).
- ✅ **Operational correctness** (`scanRightUntilTM_run_found`):
  given a tape `right`, head starting position `head`, and a gap
  `gap` such that position `head + gap` holds `target` and all earlier
  positions hold in-range non-target symbols, the machine reaches
  state 1 at position `head + gap` in exactly `gap + 1` steps. Proved
  by induction on `gap` using three single-step lemmas
  (`scanRightUntilTM_step_match`, `_advance`, `_reject`) and a
  `runFlatTM`-unfold helper.
- ✅ Refactor: bridge / continue / halt entries now use
  `dst_write_vals = [none]` (don't-modify-tape) uniformly. This makes
  single-step traces definitionally clean.
- ⏳ `eqAtHeadTM`, `scanRightUntilOneOfTM`, `copySegmentTM`,
  `compareSegmentsTM`, `countSymbolsTM` — to be added as the deciders
  in Steps 6/7 ask for them. We are deliberately *not* building a
  pre-emptive library; each primitive lands the moment a real consumer
  forces it.

**Deviations from the original Step 5 sketch:**
- Added `Mathlib.Tactic` import to `TMPrimitives.lean` (needed for
  `set`, `injection`, `by_cases` in the operational proofs).
- The "not found" / rejection multi-step lemma is deferred — it
  follows the same pattern as the `found` version and we will add it
  if a downstream consumer requires it.

---

## Phase C — Concrete deciders

### Step 6 — `evalCnfTM`
**File:** new — `Complexity/Complexity/Deciders/SAT_TM.lean`.

- Input encoding: a single tape holding `encodePair (encode N) (encode a)`,
  where `encode N = encodeList (encode <$> N)` and similarly for `a`.
- High-level algorithm, expressed as a composition of Step 3–5
  primitives:
  ```
  init: result ← true (stored as a flag on tape 1, head at cell 0)
  for each clause C in N:
    clauseSat ← false
    for each literal (s,v) in C:
      look up v in assignment a (scan tape, compare segments)
      if a[v] = s then clauseSat ← true
    result ← result ∧ clauseSat
  accept iff result = true
  ```
- Compose the primitives from Phase B into a `FlatTM` `evalCnfTM`.
- Prove `validFlatTM evalCnfTM`.
- Prove `acceptsFlatTM evalCnfTM [encodePair (encode N) (encode a)]
  (timeBound (|N| + |a|)) = true ↔ evalCnf a N = true`
  for some explicit polynomial `timeBound` (likely cubic or quartic).
- Prove `inOPoly` and `monotonic` for `timeBound`.
- Package as a `DecidesBy (fun xy => satisfiesCnf xy.2 xy.1) timeBound`.

This is the largest single step. Estimate 300–500 LOC. Worth
splitting into Step 6a (build the TM, prove validity), Step 6b (time
bound), Step 6c (correctness ↔ evalCnf) if it stretches across
sessions.

### Step 7 — `cliqueRelDecTM`
**File:** new — `Complexity/Complexity/Deciders/Clique_TM.lean`.

- Same shape as Step 6, deciding `cliqueRel ((G, k), l)`.
- Three sub-checks composed in series:
  - `fgraph_wf G`: every edge `(u, v) ∈ G.2` satisfies `u < G.1 ∧ v < G.1`.
  - `isfClique G l`: vertices in bounds, `Nodup`, all-pairs adjacency.
  - `l.length = k`.
- Re-use scanners from Step 5. `Nodup` is the only mildly tricky
  sub-check (quadratic-time nested scan over `l`).
- Bound is polynomial in `|G| + |l| + k`.
- Package as a `DecidesBy` witness.

Estimate 300–500 LOC.

---

## Phase D — Migration & re-proofs

### Step 8 — Swap the definition of `inTimePoly`
**File:** `Complexity/Complexity/NP.lean`.

- Delete `HasDecider` and the old `inTimePoly`.
- Move the contents of `inTimePolyTM` (from `TMDecider.lean`) up into
  `NP.lean` under the canonical name `inTimePoly`. The Phase A
  downgrade lemma is no longer needed.
- This will break consumers; the next four steps fix them one by one.

After this step the build is **expected to fail** at known sites:
`sat_NP`, `FlatClique_in_NP`, `red_inNP`, `P_NP_incl`,
`hasDeciderClassical`. Each will be repaired or `sorry`-ed below.

### Step 9 — Re-prove `sat_NP`
**File:** `Complexity/NP/SAT.lean`.

- Replace the `⟨fun n => n+1, ⟨fun xy => evalCnf xy.2 xy.1, …⟩, …⟩`
  literal with the `DecidesBy` witness produced in Step 6.
- `cnf × assgn` is the carrier `X`; the predicate is
  `fun xy : cnf × assgn => satisfiesCnf xy.2 xy.1`.
- Build green.

### Step 10 — Re-prove `FlatClique_in_NP`
**File:** `Complexity/NP/FlatClique.lean`.

- Replace `cliqueRelDec` (noncomputable) with the witness from Step 7.
- Delete `cliqueRelDec` and the obsolete `cliqueRel_iff` lemma (or
  re-prove it via the new TM).
- Build green.

### Step 11 — `red_inNP` partial fix
**File:** `Complexity/Complexity/NP.lean`.

- Old proof composes `dec_R ∘ (f × id)`. With TMs, we now need a
  TM-implementation of `f`, which is Part 3 territory.
- Refactor the proof to expose the missing piece:
  ```
  -- TODO(Part 3): compose with the TM for `f` once
  -- `polyTimeComputable` becomes TM-backed.
  sorry
  ```
- The rest of the lemma (certificate bound, soundness, completeness)
  is preserved from the existing proof.
- Add a `theorem red_inNP_TODO_part3` placeholder *only* for the TM
  composition piece, so the rest is honest.

### Step 12 — `P_NP_incl` partial fix
**File:** `Complexity/Complexity/NP.lean`.

- Same flavour as Step 11: the proof needs a way to push a decider for
  `P` to a decider for `fun xy : X × Unit => P xy.fst`. This is just
  pre-composing the encoder with `Prod.fst`-style projection on the
  tape, which is a Phase B-level TM exercise we can do here (no
  Part 3 dependency).
- Provide a small `decidesBy_proj_left` combinator: from
  `DecidesBy (P : X → Prop) f` build
  `DecidesBy (fun xy : X × Unit => P xy.fst) f` by pre-pending a
  "strip the unit suffix from the input tape" pass. (This is one
  scanRightUntil + truncate.)

### Step 13 — `hasDeciderClassical` / `NPhard_GenNP` / `GenNPInput`
**Files:** `Complexity/GenNP_is_hard.lean`, `Complexity/NP/GenNP.lean`,
and any callers.

- `hasDeciderClassical` no longer typechecks (it manufactures an
  `X → Bool` from `Classical.choice`, but `DecidesBy` requires a real
  TM). We **deliberately replace its body with `sorry`** and add a
  comment pointing to Part 6.
- `genNPInstance` continues to use `hasDeciderClassical`; the new
  `sorry` therefore propagates exactly into the call site documented
  in Part 6.
- `GenNPInput.rel_poly` still asks for `inTimePoly rel`. No change
  needed — the definition is just stronger now.
- `lake build` should succeed with the single new `sorry` in
  `hasDeciderClassical` (and the one in `red_inNP`, Step 11). No
  other `sorry` should exist after Part 1.

### Step 14 — Validation & sorry audit
- `lake build` clean.
- `grep -rn "sorry" CookLevin/` must return exactly **2** lines:
  `hasDeciderClassical` (queued for Part 6) and `red_inNP`'s TM-
  composition gap (queued for Part 3). Both annotated with the
  responsible Part.
- Update this `PART2.md` "Progress" section below.
- Update `README.md` "What backs each layer" table: `inTimePoly` and
  `HasDecider` rows go from "not runtime-bounded" to "TM-backed".
- Optional: run `#print axioms SAT_inNP.sat_NP` to confirm no new
  axioms beyond `propext`, `Classical.choice`, `Quot.sound`.

---

## Progress

### Session 1 (May 2026)

Landed Phase A (Steps 1–2) and the data + validity layer of Phase B
(Steps 3–4, partial Step 5). `lake build` is green throughout. No new
`sorry`s introduced.

New files:
- `Complexity/Complexity/TMDecider.lean` (Step 1)
- `Complexity/Complexity/TMEncoding.lean` (Step 2)
- `Complexity/Complexity/TMPrimitives.lean` (Steps 3, 4, 5-partial)

Existing files touched: `Complexity.lean` (registers the new modules).

Tracker:

- [x] Step 1 — `DecidesBy` structure + output convention
- [x] Step 2 — Tape encoding helpers
- [x] Step 3 — `composeFlatTM` sequential composition (data + validity;
      operational correctness deferred to per-decider need)
- [x] Step 4 — Atomic Bool-output TMs (`verdictTM`,
      `trueDecider`, `falseDecider`; `ifSymbolTM` deferred to Step 6
      when needed)
- [x] Step 5 — Tape scanners
      - [x] `scanRightUntilTM` (data + validity)
      - [x] Operational correctness lemma (`_run_found`; "not found"
            deferred until needed)
      - [ ] Remaining primitives (added on demand)
- [ ] Step 6 — `evalCnfTM` (SAT decider)
  - [ ] 6a — Build the TM, prove validity
  - [ ] 6b — Polynomial time bound
  - [ ] 6c — Correctness ↔ `evalCnf`
- [ ] Step 7 — `cliqueRelDecTM` (FlatClique decider)
- [ ] Step 8 — Swap `inTimePoly` definition in `NP.lean`
- [ ] Step 9 — Re-prove `sat_NP`
- [ ] Step 10 — Re-prove `FlatClique_in_NP`
- [ ] Step 11 — `red_inNP` partial fix (Part 3 hook)
- [ ] Step 12 — `P_NP_incl` partial fix
- [ ] Step 13 — `hasDeciderClassical` → `sorry` (Part 6 hook)
- [ ] Step 14 — Validation & sorry audit

### Lessons learned (Session 1)

- `FlatTM`'s lack of wildcard transitions forces every "for any
  symbol" rule (e.g. bridge transitions, scanner continuations) to
  be enumerated as `sig + 1` entries. Manageable but verbose.
- `DecidesBy` needed `accept_ne_reject` and the
  `decides_pos` / `decides_neg` split (vs. a single `if P x` branch)
  to keep the structure usable without a global `[Decidable (P x)]`.
- Operational correctness of `composeFlatTM` and `scanRightUntilTM`
  was deferred deliberately. Generic operational-correctness lemmas
  are intricate; we will discharge them at the point of use (Steps
  6/7), where the surrounding context narrows the cases.
- `decide` is the natural finisher for the small numeric goals these
  proofs throw up (state-index bounds, halt-vector lengths).

## Risks & open questions

- **Time bounds on composed TMs.** Each tape-scanner has a per-call
  time bound proportional to the tape length. evalCnf scans `a` once
  per literal, so a naive bound is `O(|N| · |a|)` which is cubic in
  the encoded input size. We don't need it tight — just polynomial.
- **State-renaming bookkeeping in `composeFlatTM`.** The transition
  table must be consistently shifted. We'll write a `relabelEntry`
  helper and prove a single `entryMatchesConfig` lemma about it; that
  carries the rest.
- **Whether to keep `instEncodableDefault`.** Roadmap P1.1 calls for
  removing it; that's Part 1's job. Part 2 doesn't add new uses, but
  if a `DecidesBy` proof accidentally relies on it (via `size = 0`),
  catch it now and add the missing instance.
- **Splitting Step 6.** If Step 6 grows past one session, split as
  6a/6b/6c per the checklist. Don't bundle them into one commit.

## Definition of done for Part 2

- `inTimePoly` is TM-backed; the type signature and the existence of
  a `DecidesBy` witness make this unmistakeable.
- `sat_NP` and `FlatClique_in_NP` are re-proved against the new
  definition with concrete `FlatTM` deciders.
- `red_inNP` and `P_NP_incl` build; any remaining gap is a single
  `sorry` explicitly annotated `TODO(Part 3)`.
- `hasDeciderClassical` is the only Part 6 `sorry` in the tree.
- `README.md` reflects the new state.
- The Cook–Levin chain `theorem CookLevin : NPcomplete SAT` still
  typechecks (it now depends on the two queued `sorry`s, which were
  *already* the underlying issues — Part 2 just exposes them
  honestly).
