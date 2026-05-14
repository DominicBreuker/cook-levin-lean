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

### Step 5 — Tape scanners and segment ops ✅
**File:** extend `Complexity/Complexity/TMPrimitives.lean`.

- ✅ `scanRightUntilTM sig target` (data + validity).
- ✅ `scanRightUntilTM_run_found` — full operational correctness for
  the "target found" case.
- ✅ `scanRightUntilTM_run_not_found` — full operational correctness
  for the "ran off the right end" case. By induction on
  `right.length - head` using `scanRightUntilTM_step_advance` and
  `scanRightUntilTM_step_reject`.
- ✅ `runFlatTM_extend` — padding lemma: a run that lands in a
  halting state survives any number of extra steps. Used to fit
  early-finishing runs into a uniform polynomial time budget.
- ✅ Refactor: bridge / continue / halt entries now use
  `dst_write_vals = [none]` uniformly (don't-modify-tape). Makes
  single-step traces definitionally clean.
- ⏳ `eqAtHeadTM`, `scanRightUntilOneOfTM`, `copySegmentTM`,
  `compareSegmentsTM`, `countSymbolsTM` — to be added as the deciders
  in Steps 6/7 ask for them.

---

## Phase C — Concrete deciders

### Step 6 — `evalCnfTM` 🚧 (warm-up COMPLETE; encoding landed; TM pending)
**File:** warm-up lives in `TMPrimitives.lean` (namespaces
`AllFalse` and `ExistsTrue`); SAT-specific work in
`Complexity/Complexity/Deciders/SAT_TM.lean` (new).

**Warm-up landed (session 3): the full `AllFalse` decider.**

The framework is now demonstrated *end-to-end* on a non-trivial
predicate. `AllFalse` decides `(fun bs : List Bool => ∀ b ∈ bs, b = false)`
using the same `scanRightUntilTM 2 1` machine and ties together
**every part of the Part 2 framework** — encoding, run-found,
run-not-found, padding, and a `DecidesBy` witness.

- ✅ `AllFalse.encode`, `encode_length`, `encode_size_le`,
  `encode_get_lt_two`, `encode_get_of_false`, `encode_get_of_true`.
- ✅ `AllFalse.encode_all_zero_of_all_false` — symmetric "all zero"
  lemma for `decides_pos`.
- ✅ `AllFalse.exists_first_true` — `Nat.find`-based extractor for
  the first `true` index, used by `decides_neg`.
- ✅ **`AllFalse.decider : DecidesBy (fun bs => ∀ b ∈ bs, b = false) (fun n => n + 2)`**
  — fully witnessed, no sorrys.
- ✅ `AllFalse.timeBound_inOPoly`, `AllFalse.timeBound_monotonic`,
  `AllFalse.inTimePolyTM_allFalse : inTimePolyTM (fun bs => ∀ b ∈ bs, b = false)`.

This is the first complete `inTimePolyTM` proof in the project. It
exercises every previously-built scanner lemma:

- `decides_pos` uses `scanRightUntilTM_run_not_found` (scanner runs off
  the right end → state 2 = `acceptState`).
- `decides_neg` uses `scanRightUntilTM_run_found` (scanner finds the
  first `1` → state 1 = `rejectState`).
- Both branches use `runFlatTM_extend` to pad the early-halting run to
  the uniform time budget `encodable.size bs + 2`.

**Session 4 progress:**

- ✅ `ExistsTrue.decider` — the dual of `AllFalse`, deciding "some
  bool in the list is `true`". Same underlying TM, swapped accept/
  reject states. Second complete `DecidesBy` in the library.
- ✅ `ExistsTrue.inTimePolyTM_existsTrue`.
- ✅ **SAT input encoding** in `Complexity/Complexity/Deciders/SAT_TM.lean`:
  - `sigSAT := 7` alphabet (terminator, unary digit, pos/neg sign,
    clause separator, CNF/assgn boundary, assgn separator).
  - `encodeLiteral`, `encodeClause`, `encodeCnf`, `encodeAssgn`,
    `encodeInput` with explicit `List Nat` shapes.
  - Length identities for each.
  - **Symbol bounds**: every symbol the encoder emits is `< sigSAT`
    (`encodeInput_symbols_lt` and per-component variants).
  - **Polynomial size bound** (actually *linear*):
    `(encodeInput (N, a)).length ≤ encodable.size (N, a) + 1`
    via per-component bounds `encodeLiteral_length_le`,
    `encodeClause_length_le`, `encodeCnf_length_le`,
    `encodeAssgn_length_le`, then combined for the pair.

**Session 5 progress:**

- ✅ **Multi-tape framework extension**: `DecidesBy` now requires
  `M_tapes_pos : 0 < M.tapes` and uses a new `initialTapes` helper to
  place the input on tape 0 and leave the remaining `M.tapes - 1`
  work tapes blank. For `M.tapes = 1` this is definitionally the same
  as the old single-tape form, so all existing deciders (`trueDecider`,
  `falseDecider`, `AllFalse.decider`, `ExistsTrue.decider`) transport
  with just the new field. This unlocks multi-tape deciders for the
  upcoming SAT TM.
- ✅ **First SAT-input-based decider**: `CnfEmpty.decider` in
  `SAT_TM.lean` decides `(fun Na : cnf × assgn => Na.1 = [])` —
  i.e., "the CNF is empty". Uses a 3-state hand-rolled FlatTM that
  reads position 0 of the encoded input and branches on whether the
  symbol is `5` (CNF terminator).
- ✅ Step lemmas: `TM_step_match`, `TM_step_reject_none`,
  `TM_step_reject_symbol`, with a `find_rejectSymbolEntry_match`
  helper for the filtered-range transition lookup.
- ✅ `encodeInput_empty_cnf_head` and
  `encodeInput_nonempty_cnf_head` — the encoding facts the decider
  needs.
- ✅ `inTimePolyTM_cnfEmpty` packaged.

**Then `evalCnfTM` proper (TODO next session):**
- Build a FlatTM with explicit states for outer (clauses) / inner
  (literals) loops, variable-lookup subroutine, and result accumulator.
- Multi-tape now available — likely use 2 or 3 tapes (input + scratch).
- Prove validity + polynomial time bound + correctness ↔ `evalCnf`.
- Package as `DecidesBy (fun xy => satisfiesCnf xy.2 xy.1) timeBound`.

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
      - [x] `_run_found`, `_run_not_found`, `runFlatTM_extend`
      - [ ] Remaining primitives (added on demand)
- [ ] Step 6 — `evalCnfTM` (SAT decider)
  - [x] 6.0 — `AllFalse.decider` end-to-end warm-up
  - [x] 6.0b — `ExistsTrue.decider` (dual of `AllFalse`)
  - [x] 6.0c — SAT input encoding + length / symbol / polynomial
        size bounds
  - [x] 6.0d — Multi-tape framework extension (`M_tapes_pos`,
        `initialTapes`)
  - [x] 6.0e — `CnfEmpty.decider` — first SAT-input-based decider
        (decides `N = []`)
  - [ ] 6a — Build `evalCnfTM`, prove validity
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

### Session 5 (May 2026)

Two structural wins and the first SAT-input-based decider.

- **Multi-tape framework**: extended `DecidesBy` to support TMs with
  any number of tapes ≥ 1. Added `M_tapes_pos : 0 < M.tapes` field,
  switched `decides_pos` / `decides_neg` / `decideFn` to use a new
  `initialTapes M input := input :: List.replicate (M.tapes - 1) []`
  helper. For `M.tapes = 1`, `initialTapes` reduces definitionally to
  `[input]`, so existing deciders compile unchanged (just need the
  `M_tapes_pos := by decide` field).
- **`CnfEmpty.decider`** in `SAT_TM.lean` (761 LOC total). A real
  3-state TM that reads the first symbol of the encoded
  `(cnf × assgn)` input and accepts iff it's `5` (the CNF
  terminator), which holds iff `N = []`. Includes step lemmas
  (match / reject-none / reject-symbol), the inductive
  `find_rejectSymbolEntry_match` for the filtered-range lookup, and
  full `decides_pos` / `decides_neg`. `inTimePolyTM_cnfEmpty`
  packaged.

`lake build` clean, zero sorrys.

### Session 4 (May 2026)

Two new wins: a dual decider for the negation, and the structural
groundwork for the SAT TM.

- `ExistsTrue.decider` — adds a second working decider in
  `TMPrimitives.lean`. Same `scanRightUntilTM 2 1` machine, swapped
  accept/reject. Shares all encoding helpers with `AllFalse` via
  `open AllFalse (encode encode_length …)`.
- `ExistsTrue.inTimePolyTM_existsTrue`.
- New file `Complexity/Complexity/Deciders/SAT_TM.lean` (324 LOC):
  - Concrete 7-symbol alphabet (`sigSAT`).
  - Encoders: `encodeLiteral`, `encodeClause`, `encodeCnf`,
    `encodeAssgn`, `encodeInput`.
  - Length identities (`*_length`).
  - Symbol bounds (`*_symbols_lt`): every emitted symbol is `< 7`.
  - **Linear** size bound `encodeInput_length_le :
    (encodeInput (N, a)).length ≤ encodable.size (N, a) + 1`. This is
    the exact shape `DecidesBy.encode_size` will ask for when we
    package the SAT decider.
- Registered in `Complexity.lean`.

`lake build`: clean, 3339 jobs, zero sorrys.

### Session 3 (May 2026)

Completed the `AllFalse` end-to-end demonstrator. The framework now has
a first **fully witnessed** `DecidesBy` and `inTimePolyTM` for a real
non-trivial predicate, no sorrys. `TMPrimitives.lean` is at 1262 LOC.

- `AllFalse.encode_get_lt_two`, `_of_false`, `_of_true` — encoding
  accessor lemmas. Phrased in `[k]'h` style and converted to `.get`
  at the seams, since `getElem_map` is the canonical name (no
  `List.get_map` in this toolchain).
- `AllFalse.encode_all_zero_of_all_false`, `exists_first_true` —
  predicate-side lemmas, the second using `Nat.find` for constructive
  extraction of the first `true` index.
- **`AllFalse.decider : DecidesBy …`** — the first concrete decider
  in the codebase. Uses `scanRightUntilTM_run_not_found` +
  `runFlatTM_extend` for `decides_pos`, and
  `scanRightUntilTM_run_found` + `runFlatTM_extend` for `decides_neg`.
  `Fin.eq_of_val_eq` is the workhorse for the `0 + k` ↔ `k` index
  conversion forced by the scanner lemmas' `head + gap` shape.
- `AllFalse.timeBound_inOPoly`, `timeBound_monotonic`,
  `inTimePolyTM_allFalse`.

### Session 2 (May 2026)

Closed Step 5 fully and laid encoding pre-work for the Step 6 warm-up.
Net additions to `TMPrimitives.lean` (1006 LOC at session end):

- `scanRightUntilTM_run_not_found` — operational correctness for the
  "scan past the right end" path. Symmetric companion to `_run_found`,
  proved by induction on `right.length - head`.
- `runFlatTM_extend` — "padding" lemma. If a TM run lands in a halting
  state after `n` steps, running for any `n + k` steps gives the same
  configuration. Needed to fit early-finishing runs into the
  decider's uniform polynomial time budget.
- `AllFalse` namespace (warm-up scaffolding): `encode`,
  `encode_length`, `encode_size_le`, `encode_mem_zero_or_one`,
  `encode_mem_lt_two`. These are the input-encoding primitives for a
  small `DecidesBy` demonstrator on the "all bits are false"
  predicate — the next concrete deliverable before tackling the much
  larger SAT decider.

### Lessons learned (Session 2)

- The `n + 1 + k` shape of `runFlatTM`'s recursion does NOT
  definitionally unfold against `(if halt … then … else match step …)`
  — it must be rewritten to `(n + k) + 1` form via
  `Nat.add_right_comm` first.
- `Nat.sub_pos_of_lt` gives `1 ≤ n - m` from `m < n`; pair with
  `Nat.sub_add_cancel` and `Nat.sub_add_eq` for tape-length sub-one
  manipulations.
- `List.get_map` is NOT the canonical name in this toolchain; current
  Mathlib uses `getElem_map` / `getElem_map_rev` over the
  `getElem`-style indexing.
- Top-level structure literals in `show` need an explicit type
  annotation, e.g. `show (some {...} : Option FlatTMConfig) = ...`.

### Lessons learned (Session 5)

- Definitional equality is the key trick for backward-compatible
  framework extensions. `List.replicate 0 [] = []` reduces by `rfl`,
  so `input :: List.replicate (1 - 1) [] = input :: [] = [input]` —
  existing proofs that constructed `runFlatTM ... [input]` simply
  unify with the new shape without changes.
- For an `exact ⟨_, h, rfl, rfl⟩` where the existential's witness is
  inferred from `h`, put the *known* term first (`h`) and the unknown
  (`_`) where Lean can solve it from later constraints. Mixing
  `refine ⟨_, ?_, rfl, rfl⟩` with later `exact h` can fail when the
  `rfl`s need the witness already known to typecheck.
- `decide` fails on goals containing free variables even if the goal
  is "morally" decidable (e.g. `0 < (x :: rest).length`). Use the
  underlying constructor (`Nat.zero_lt_succ _`) instead.

### Lessons learned (Session 4)

- `ring` (from `Mathlib.Tactic`) is by far the shortest way to close
  `Nat` arithmetic identities of more than a couple of terms. Worth
  reaching for instead of stacking `Nat.add_assoc`/`add_comm` rewrites,
  even under the "prefer term-mode" preference — the term it produces
  is a single application of `ring_nf`'s normaliser.
- Sharing helpers between two parallel deciders (`AllFalse` /
  `ExistsTrue`) is cleanest via `open AllFalse (name1 name2 ...)`.
  The `decider` definition can then re-state only what differs.
- `List.foldr` on `cons` unfolds *definitionally* under `show` (no
  `simp`/`rfl` needed if you point at the right form). For mixed
  `foldl` / `foldr` proofs, `foldr` is the friendlier side.

### Lessons learned (Session 3)

- `List.get ⟨k, h⟩ = l[k]'h` is **definitional** (`rfl`) in this
  toolchain. Mixing the two styles is then free: state the encoding
  accessor lemmas in `[]` style (which `getElem_map` supports
  directly), then `show l.get ⟨k, h⟩ = ...` and convert.
- `0 + k` is **not** definitionally `k` in Lean 4 — `Nat.zero_add` is
  a theorem, not a defeq. When a scanner lemma signature has
  `head + gap` and we want `head := 0`, every position index in
  derived hypotheses comes out as `0 + k` and must be reconciled with
  the conclusion's `k` via `Fin.eq_of_val_eq (Nat.zero_add k)`.
- `obtain ⟨k, rfl⟩ : ∃ k, m = n + k := …` does **not** typecheck if
  neither side of the existential's witness is a free variable. Use a
  named hypothesis instead and `rw [h]` to insert the
  `(encode bs).length + 1 + k = encodable.size bs + 2` step.
- `Nat.add_sub_cancel'` takes the inequality `n ≤ m` and gives
  `n + (m - n) = m`. Combined with `runFlatTM_extend`, this is the
  natural way to pad a `runFlatTM n` to a `runFlatTM m`.
- `rw [Nat.zero_add]` inside a `Fin` index can fail with
  "motive is not type correct" because the index participates in a
  dependent type — `Fin.eq_of_val_eq` plus a rewrite of the whole
  `⟨…, …⟩` is the workaround.

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
