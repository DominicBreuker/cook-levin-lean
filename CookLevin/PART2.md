# Part 2 — Implementation Plan & Progress Tracker (v2)

Tracks Part 2 of `ROADMAP.md` (lines 166–218): replace the propositional
`inTimePoly` / `HasDecider` with a Turing-machine-backed witness, then
re-prove `sat_NP`, `FlatClique_in_NP`, `red_inNP`, and `P_NP_incl`
against the new definition.

> **v2 (this revision).** Pivot from the original "build evalCnfTM
> from the ground up" strategy. After ~10000 LOC of TM primitives and
> demonstration deciders (PHASES A, B, and most of C — see "What is
> already built" below) the realisation is that a hand-rolled
> evalCnfTM along the same lines will be another ~10000 LOC and many
> sessions, with very high risk of further scope creep. Instead we
> front-load the framework migration so the rest of the CookLevin
> chain rebuilds against the new TM-backed `inTimePoly`, with the two
> concrete TM constructions (evalCnfTM, cliqueRelDecTM) carried as
> *honestly labelled* `sorry`s. After the framework is in place we
> finish the TM constructions iteratively, each in its own well-scoped
> file under `Deciders/`, with no blocking dependencies left in the
> chain.

## What is already built (do not touch)

The following are landed, sorry-free, and on path to Part 2 completion.
They will be reused in the new plan; the per-step lessons in the
"Lessons learned" section at the bottom remain authoritative for any
future TM construction.

### Phase A — Foundation ✅
- `Complexity/Complexity/TMDecider.lean` (~220 LOC):
  - `DecidesBy` structure (encode, M, M_valid, M_tapes_pos,
    acceptState/rejectState halting bits, `accept_ne_reject`,
    `decides_pos`, `decides_neg`).
  - `inTimePolyTM`, the canonical new TM-backed predicate.
  - `DecidesBy.decideFn` + `decideFn_correct` — soundness of the
    Bool extraction.
  - `HasDecider.of_DecidesBy`, `inTimePoly_of_inTimePolyTM` — the
    downgrade chain.
  - `DecidesBy.negate`, `DecidesBy.iff`, `inTimePolyTM_not`,
    `inTimePolyTM_iff` — predicate-level combinators.
- `Complexity/Complexity/TMEncoding.lean` (~135 LOC):
  - `shiftSyms`, `encodePair`, `encodeList`, length lemmas,
    `listNat_length_le_size`.

### Phase B — TM combinator library ✅
- `Complexity/Complexity/TMPrimitives.lean` (~1400 LOC):
  - `composeFlatTM` data + `composeFlatTM_valid`.
  - `bridgeEntries`, `shiftEntry`, `composedHalt` plumbing.
  - `verdictTM` 3-state machine + `trueDecider`, `falseDecider`
    smoke tests.
  - `scanRightUntilTM` + the three step lemmas
    (`_step_match`, `_step_advance`, `_step_reject`) +
    `_run_found`, `_run_not_found` operational correctness.
  - `runFlatTM_extend` (halt-then-pad) helper.

### Phase C — Demonstration deciders ✅ (and frozen)
- `Complexity/Complexity/Deciders/SAT_TM.lean` lines 1–6413 (~6400 LOC)
  hosts the SAT input encoding + the demonstration deciders 6.0a–6.0o:
  `CnfEmpty`, `CnfEmptyAssgnEmpty`, `AssgnEmpty`, `CnfStartsEmpty`,
  `CnfNonempty`, `AssgnNonempty`, the `.iff`-derived deciders,
  `CnfOrAssgnNonempty`, `CnfHasEmptyClause`, `AssgnContainsZero`.
- Each is a `DecidesBy` witness with a polynomial time bound and full
  operational correctness; no sorrys.
- These are *not on the proof path to `sat_NP`*. They were stepping
  stones to evalCnfTM. They are kept as a worked library of patterns
  (`.negate`, `.iff`, parametric TM families, scan loops, find-helper
  patterns) for the eventual evalCnfTM and cliqueRelDecTM constructions.
  We will **not** add more deciders of this shape.

### Phase C — In-flight (decision required)
- `Complexity/Complexity/Deciders/SAT_TM.lean` lines 6415–7467
  (~1050 LOC) hosts the partially built `AssgnContainsVar` parametric
  TM family (state count `v + 5`; per-`k` transitions over
  `List.range v`). Landed: data, `TM_valid`, `TM_states`,
  `TM_halt_length`, the 8 positive-path step lemmas and various
  helper find-lemmas.
- **Missing** to make it a `DecidesBy`: reject-path step lemmas
  (`sready_reject_0`, `sk_reject_0`), the run lemma, encoding
  positional helpers, and the `decider` itself. Estimated ~600 LOC.
- **Recommendation:** delete it. AssgnContainsVar was a stepping-stone
  for "variable lookup inside evalCnfTM"; it is not used anywhere yet
  and the eventual evalCnfTM will need to be designed around multiple
  tapes (see step 6), in which case the single-tape AssgnContainsVar
  is the wrong shape. Step 1 of the new plan formalises this
  decision.

## Scope (unchanged from v1)

- **P2.1** Replace `HasDecider` with the TM-backed `DecidesBy`;
  redefine `inTimePoly`.
- **P2.2** Re-prove `sat_NP` (`Complexity/NP/SAT.lean:299`) and
  `FlatClique_in_NP` (`Complexity/NP/FlatClique.lean:84`) by
  constructing actual `FlatTM`s for `evalCnf` and `cliqueRel`.
- **P2.3** Re-prove `red_inNP` (`Complexity/Complexity/NP.lean:152`)
  by composing the reduction's TM with the certificate-checking TM.
  Cannot fully close before Part 3 lands `polyTimeComputable`; leave
  the composition gap as a labelled `sorry`.

**Out of scope:** `polyTimeComputable` (Part 3), TM bridges (Part 4),
Cook tableau (Part 5), `hasDeciderClassical` / `NPhard_GenNP` (Part 6).

## Design decisions (carried over from v1)

1. **Boolean output via halting state index.** `DecidesBy` carries
   distinct `acceptState`, `rejectState : Nat` (both halting); answer
   read as `decide (cfg.state_idx = acceptState)`.
2. **Multi-tape input layout.** `initialTapes M input := input ::
   List.replicate (M.tapes - 1) []`. For `M.tapes = 1` this reduces
   definitionally to `[input]` — single-tape proofs transport
   unchanged.
3. **`DecidesBy` is `Decidable`-free.** Split into `decides_pos` /
   `decides_neg`; an extra `accept_ne_reject` field carries the
   distinctness needed for the downgrade theorem.
4. **Migration discipline.** New code lives alongside old definitions
   until Step 8 swaps `inTimePoly` and lets the old API go.
5. **Proof style.** Term-mode over `linarith` / `omega`; `ring` from
   Mathlib is acceptable for arithmetic chains.
6. **New: scope discipline for TMs.** A TM construction goes in its
   own file under `Complexity/Complexity/Deciders/<Name>.lean`. The
   file owes only one external symbol — its `decider :
   DecidesBy ... timeBound` — plus a sibling `..._inTimePolyTM`
   theorem. Internal step / find / run lemmas are `private`. No file
   exceeds ~3000 LOC; if it would, refactor into sub-files.
7. **New: the "interface-first" rule.** A `DecidesBy` for a new
   predicate may be introduced with `sorry` so downstream proofs can
   migrate against its *signature* immediately. Only the
   construction is deferred; the interface itself is type-checked.
   Each such `sorry` carries a `TODO(Part2-followup:<Name>)` tag and
   is registered in the "Outstanding sorrys" register at the bottom
   of this file.

## Strategic pivot

The v1 plan tried to build `evalCnfTM` by stacking ever-larger
hand-rolled flat TMs (6.0a → 6.0p → 6a–6c). Empirically, each
additional state costs 50–200 LOC of operational-correctness boilerplate
(step lemmas, find-helpers, transition-block lemmas), and the
`evalCnfTM` design has at least a doubly-nested scan (clauses ×
literals × variables). Extrapolating gives 8000–15000 more LOC just
for `evalCnfTM`, with `cliqueRelDecTM` (which has a `Nodup` /
quadratic adjacency check) of similar magnitude. That makes
*all of Part 2* dwarf Parts 3–5 in size, which contradicts the
roadmap's effort estimate (≈1500 LOC) and locks the rest of the
project behind one giant decider.

The pivot:

- **The framework migration does not need the TM constructions to be
  proved**; it only needs `DecidesBy ... ` *witnesses to exist as
  symbols*. So we migrate first and put the two open TM constructions
  on labelled `sorry`s.
- This unblocks `sat_NP`, `FlatClique_in_NP`, `red_inNP`,
  `P_NP_incl`, and the rebuild of `theorem CookLevin` against the
  strengthened `inTimePoly`.
- The TM constructions then proceed *iteratively*, each in its own
  file, each closing one labelled `sorry`. They no longer block any
  downstream consumer.
- When the constructions land, Part 2 is closed `sorry`-free *modulo*
  the two structural Parts (3, 6) that v1 already acknowledged
  would carry sorrys past the end of Part 2.

## Phase plan (new)

| Phase | Steps | Goal                                                      | Status     |
|-------|-------|-----------------------------------------------------------|------------|
| A     | 1–2   | Foundation (`DecidesBy` + encoding)                       | ✅ done     |
| B     | 3–5   | TM combinator library                                     | ✅ done     |
| C-old | 6.0a–6.0o | Demonstration deciders (frozen at AssgnContainsZero)  | ✅ done     |
| C′    | 1     | Clean up / decide fate of AssgnContainsVar (in flight)    | ✅ done     |
| D     | 2     | Land `DecidesBy` stub for `evalCnf`                       | ✅ done     |
| D     | 3     | Land `DecidesBy` stub for `cliqueRel`                     | ✅ done     |
| E     | 4     | Swap `inTimePoly` to TM-backed; stub broken consumers     | ✅ done     |
| E     | 5     | Re-prove `sat_NP` against `EvalCnfTM.inTimePolyTM_evalCnf`| ✅ done     |
| E     | 6     | Re-prove `FlatClique_in_NP` against `CliqueRelTM.…`       | ✅ done     |
| E     | 7     | Re-prove `red_inNP` (TM-composition piece → Part-3 sorry) | ✅ done     |
| E     | 8     | Re-prove `P_NP_incl` via inline `DecidesBy.proj_left`     | ✅ done     |
| E     | 9     | Retype `hasDeciderClassical` to TM-backed (body → Part-6 sorry); delete legacy `HasDecider` | ✅ done |
| F     | 10    | Validation: rebuild `CookLevin`, sorry-audit, README      | ✅ done     |
| G     | 11    | Close `EvalCnfTM.decider` stub (build the real TM)        | ⏳ pending  |
| H     | 12    | Close `CliqueRelTM.decider` stub (build the real TM)      | ⏳ pending  |
| —     | 13    | Final Part-2 sweep (verify only Part-3 / Part-6 sorrys)   | ⏳ pending  |

Phases C′–F take Part 2 from "framework drafted" to "framework
*migrated* and Cook–Levin rebuilds" with two labelled sorries. Phases
G and H close those sorries.

Per the user's preference (work step-by-step, validate often), each
step below ends with a concrete `lake build` checkpoint and either an
expected diff size or an expected sorry count delta.

### Step 1 — Resolve AssgnContainsVar

**Goal:** Remove the in-flight AssgnContainsVar work; SAT_TM.lean
ends cleanly at AssgnContainsZero.

**Why:** AssgnContainsVar was a stepping stone to a single-tape
evalCnfTM, but Step 6 now switches to multi-tape (Step 11). The
single-tape parametric TM is the wrong shape and the partial work
won't be reused. Keeping it adds ~1000 LOC of dead code that will
need maintenance.

**Actions:**
- Delete lines 6415–7467 of `Deciders/SAT_TM.lean` (the entire
  `namespace AssgnContainsVar` block).
- Update the Phase C summary comment at the top of the file.
- `lake build` clean.

**Estimated diff:** −1050 LOC.

### Step 2 — Stub `evalCnfTM_decider`

**Goal:** Land an unconditional `DecidesBy` *signature* for the SAT
verifier, with the body a clearly tagged `sorry`. This is the
interface against which `sat_NP` will be rewritten.

**File:** New, `Complexity/Complexity/Deciders/EvalCnfTM.lean`.

**Content:**
```lean
import Complexity.Complexity.TMDecider
import Complexity.Complexity.Deciders.SAT_TM

namespace EvalCnfTM
open SAT_TM (sigSAT encodeInput encodeInput_length_le)

/-- Polynomial time budget for the eventual evalCnfTM. We pick a
loose cubic bound `(n + 1)^3` to absorb the doubly-nested scan
(clauses × literals × variable lookups). -/
def timeBound (n : Nat) : Nat := (n + 1) ^ 3

theorem timeBound_inOPoly : inOPoly timeBound := ...   -- 3-term polynomial
theorem timeBound_monotonic : monotonic timeBound := ...

/-- TM-backed decider for the SAT verification relation
`fun (N, a) => satisfiesCnf a N`. Construction deferred to Step 11
(`TODO(Part2-followup:EvalCnfTM)`); the *interface* is final and
will be consumed by `sat_NP` from Step 4 onwards. -/
def decider : DecidesBy
    (fun Na : cnf × assgn => satisfiesCnf Na.2 Na.1) timeBound :=
  sorry  -- TODO(Part2-followup:EvalCnfTM)

theorem inTimePolyTM_evalCnf :
    inTimePolyTM (fun Na : cnf × assgn => satisfiesCnf Na.2 Na.1) :=
  ⟨timeBound, ⟨decider⟩, timeBound_inOPoly, timeBound_monotonic⟩

end EvalCnfTM
```

**Actions:**
- Author the file; only `decider` carries the sorry.
- Register the imports in `Complexity.lean`.
- Add the sorry to the Outstanding sorrys register at the bottom of
  this file.
- `lake build` clean except for the one labelled sorry.

**Estimated diff:** +70 LOC (file) + 1 line (`Complexity.lean`).
**Sorry delta:** +1 (`EvalCnfTM.decider`).

### Step 3 — Stub `cliqueRelDecTM_decider`

**Goal:** Same as Step 2, for the FlatClique verifier.

**File:** New, `Complexity/Complexity/Deciders/CliqueRelTM.lean`.

**Predicate:** `fun (Gkl : (fgraph × Nat) × List fvertex) =>
cliqueRel Gkl.1 Gkl.2`. Time budget `(n + 1)^3` (covers the
`l.Nodup` and adjacency scans).

**Actions:** mirror Step 2's file structure. Register in
`Complexity.lean` and the sorry register.

**Estimated diff:** +70 LOC.
**Sorry delta:** +1 (`CliqueRelTM.decider`).

### Step 4 — Swap the definition of `inTimePoly`

**Goal:** Make `inTimePolyTM` the canonical `inTimePoly` and remove
the old propositional `HasDecider`.

**File:** `Complexity/Complexity/NP.lean`.

**Actions:**
- Replace the body of `def inTimePoly` with the body of
  `inTimePolyTM` (i.e., `∃ f, Nonempty (DecidesBy P f) ∧ inOPoly f ∧
  monotonic f`). Keep the old name `inTimePoly` so call-sites don't
  churn.
- Delete `HasDecider` and the helper `HasDecider.of_DecidesBy`
  becomes unnecessary.
- Re-export `DecidesBy`-related names from `NP.lean` if needed for
  back-compat.
- This breaks `sat_NP`, `FlatClique_in_NP`, `red_inNP`, `P_NP_incl`,
  and `hasDeciderClassical`. Steps 5–9 fix them in turn.

**Estimated diff:** ~50 LOC modify, ~30 LOC delete.
**Expected build state:** many errors in NP-tree files; we close them
one at a time below. *Do not commit* until at least one downstream
consumer (Step 5) is also updated, to keep the tree in a clearly
intermediate state.

### Step 5 — Re-prove `sat_NP`

**Goal:** `Complexity/NP/SAT.lean` builds against the new
`inTimePoly`. The verifier slot is filled by
`EvalCnfTM.inTimePolyTM_evalCnf` (from Step 2).

**Actions:**
- In `SAT.lean`, change the `inTimePoly` witness from the inline
  `⟨…, ⟨evalCnf …, _⟩, …⟩` term to
  `EvalCnfTM.inTimePolyTM_evalCnf`.
- Add `import Complexity.Complexity.Deciders.EvalCnfTM` at the top.
- `lake build CookLevin.Complexity.NP.SAT` clean (modulo the deferred
  sorry inside `EvalCnfTM.decider`).

**Estimated diff:** ~30 LOC modify in SAT.lean.

### Step 6 — Re-prove `FlatClique_in_NP`

**Goal:** Same as Step 5, for FlatClique.

**Actions:**
- `Complexity/NP/FlatClique.lean`: replace the inline
  `cliqueRelDec` decider with `CliqueRelTM.inTimePolyTM_cliqueRel`.
- Delete the `noncomputable def cliqueRelDec`.
- `lake build CookLevin.Complexity.NP.FlatClique` clean.

**Estimated diff:** ~25 LOC modify, ~10 LOC delete.

### Step 7 — Re-prove `red_inNP`

**Goal:** `red_inNP` builds against the new `inTimePoly`. The TM
*composition* (run the reduction's TM, then the verifier TM) is a
Part 3 deliverable, so this step legitimately introduces *one* labelled
sorry.

**Actions:**
- In `Complexity/Complexity/NP.lean`, rewrite `red_inNP` to:
  1. Destructure the source `inNP P` to get the verifier
     `DecidesBy P_verifier t`.
  2. Compose it (in the *predicate* sense) with the reduction
     `f : X → Y`.
  3. The new verifier predicate is
     `fun (x, c) => rel_R (f x) c`. Provide a `DecidesBy` for it
     using the source verifier `M` and *the reduction's TM* — but
     the reduction's TM is only meaningful once `polyTimeComputable`
     in Part 3 is TM-backed. Mark the missing composition as
     `TODO(Part3:red_inNP_TMcompose) sorry`.
- Register the sorry.
- `lake build CookLevin.Complexity.Complexity.NP` clean.

**Estimated diff:** ~80 LOC modify.
**Sorry delta:** +1 (`red_inNP` TM-composition gap).

### Step 8 — Re-prove `P_NP_incl`

**Goal:** `inP X P → inNP P` builds against the new `inTimePoly`,
without a Part 3 dependency.

**Strategy:** Build a small combinator
`DecidesBy.proj_left : DecidesBy P f →
DecidesBy (fun (xy : X × Unit) => P xy.1) f`
(re-uses the same TM; the encoding ignores the `Unit` payload).
`P_NP_incl` then plugs it in.

**Actions:**
- Add `DecidesBy.proj_left` to `TMDecider.lean`.
- Rewrite `P_NP_incl` in `NP.lean` to use it.
- `lake build CookLevin.Complexity.Complexity.NP` clean.

**Estimated diff:** ~30 LOC TMDecider, ~25 LOC NP.lean modify.

### Step 9 — Mark `hasDeciderClassical` for Part 6

**Goal:** `hasDeciderClassical` no longer typechecks against the new
`inTimePoly`. We tag it `sorry` with a `TODO(Part 6)` until Part 6
deletes it outright.

**Actions:**
- In `Complexity/GenNP_is_hard.lean`, change the body of
  `hasDeciderClassical` to `sorry`, with the same TODO comment.
- Confirm callers (`genNPInstance`, `NPhard_GenNP`) still typecheck
  (they will: they only require the symbol, not its proof).
- Register the sorry.
- `lake build` of the full tree clean (modulo registered sorrys).

**Estimated diff:** ~5 LOC.
**Sorry delta:** +1 (`hasDeciderClassical`).

### Step 10 — Validation milestone

**Goal:** Confirm the framework migration is complete and the chain
rebuilds.

**Actions:**
- `lake build` from scratch: clean, no errors other than registered
  sorrys.
- `grep -rn "sorry" CookLevin/Complexity` returns exactly:
  - `EvalCnfTM.decider` — `TODO(Part2-followup:EvalCnfTM)`.
  - `CliqueRelTM.decider` — `TODO(Part2-followup:CliqueRelTM)`.
  - `red_inNP` TM-composition gap — `TODO(Part3:red_inNP_TMcompose)`.
  - `hasDeciderClassical` — `TODO(Part6:hasDeciderClassical)`.
- Update `README.md`: the project's sorry inventory now lists these
  four, with a one-line explanation each.
- Update PART2.md's "Outstanding sorrys" register at the bottom.

**Estimated diff:** ~20 LOC in README + this file's footer.

At this point Part 2 is *framework-complete*. The chain
`theorem CookLevin : NPcomplete SAT` rebuilds. The remaining
deliverables are the two TM constructions.

**Step 10 milestone reached (this session).** Sorry inventory:

```
Complexity/Complexity/NP.lean:270                  red_inNP (TM-composition slot)
                                                   -- TODO(Part3:red_inNP_TMcompose)
Complexity/Complexity/Deciders/EvalCnfTM.lean:58   EvalCnfTM.decider
                                                   -- TODO(Part2-followup:EvalCnfTM)
Complexity/Complexity/Deciders/CliqueRelTM.lean:66 CliqueRelTM.decider
                                                   -- TODO(Part2-followup:CliqueRelTM)
Complexity/GenNP_is_hard.lean:23                   hasDeciderClassical
                                                   -- TODO(Part6:hasDeciderClassical)
```

### Step 11 — Construct `evalCnfTM`

**Goal:** Close the `EvalCnfTM.decider` sorry from Step 2 with a real
multi-tape FlatTM and operational correctness.

**Design (sketched; details emerge during construction):**
- **4 tapes**:
  - Tape 0: the input `encodeInput (N, a)`.
  - Tape 1: working buffer holding the current variable id being
    looked up.
  - Tape 2: per-clause OR accumulator (`0` = false so far, `1` = true).
  - Tape 3: per-CNF AND accumulator (`0` = false, `1` = true so far).
- **Outer loop (state group A):** walk tape 0 past `0` delimiters.
  At each clause start, reset tape 2 to `0`, then enter the
  per-clause loop. After the clause, AND tape 2 into tape 3.
  Halt on symbol `5` (CNF-end marker).
- **Per-clause loop (state group B):** for each literal `(b, v)` on
  tape 0, copy `v` to tape 1 (scanning right past variable bits),
  read the polarity bit `b`, then enter the variable-lookup loop.
- **Variable-lookup loop (state group C):** scan the assignment
  segment of tape 0 (after the `5` marker), comparing each variable
  encoded there to tape 1's contents. Outcome:
  - if equal: literal value = `b` (positive polarity wins);
  - if scan exhausts assignment without match: literal value = `¬ b`.
  Write `literal_value OR tape_2` to tape 2.
- **Final:** halt; output is read from tape 3.

**Implementation discipline:**
- Build sub-TMs as small flat machines (`resetAccumTM`, `copyVarTM`,
  `compareVarTM`, `orIntoTapeTM`, `andIntoTapeTM`). Each in its own
  `private namespace` inside `Deciders/EvalCnfTM.lean` or a sibling
  file `Deciders/EvalCnfTM/Primitives.lean` if size demands.
- Compose them via a *proven* `composeFlatTM_run` lemma (see Step
  11.0 below). Hand-rolled monolithic state machines are forbidden
  for this step.
- File size target: ≤ 3000 LOC for EvalCnfTM.lean. If approaching that
  limit, split into `Primitives.lean` + `Compose.lean`.

**Step 11 substeps (each its own session, each ends with `lake build`):**
- **11.0** Land `composeFlatTM_run`: if M₁ halts at config c₁ in t₁
  steps with `c₁.state_idx = exit`, and M₂ halts at c₂ in t₂ steps
  starting from `{ state_idx := M₂.start, tapes := c₁.tapes }`, then
  `composeFlatTM M₁ M₂ exit` halts at the shifted c₂ in
  `t₁ + 1 + t₂` steps. This is the lemma `composeFlatTM_valid`
  promised but never delivered in v1. ~250 LOC.
- **11.1** Land `resetTapeTM` / `writeAtHeadTM` / `gotoStartTM`
  (per-tape helpers). Multi-tape; each ~150 LOC.
- **11.2** Land `copySegmentTM`: copy current segment of tape 0
  (between delimiters `0`) onto tape 1. ~400 LOC.
- **11.3** Land `compareSegmentsTM`: compare tape 0 vs tape 1, halt
  in match/non-match state. ~400 LOC.
- **11.4** Wire up the per-literal evaluator using the primitives
  + `composeFlatTM_run`. ~400 LOC.
- **11.5** Wire up the per-clause and per-CNF loops. ~400 LOC.
- **11.6** Time-bound proof: each variable lookup is O(|a|), each
  literal is O(|c|), each clause is O(|c|·|a|), the whole CNF is
  O(|N|·|c|·|a|) ≤ O((n+1)³). Close `EvalCnfTM.timeBound_inOPoly` +
  the `decides_pos`/`decides_neg` obligations. ~300 LOC.
- **11.7** Replace the Step 2 `sorry` with the real `decider`.
  `lake build` clean. Remove the `TODO(Part2-followup:EvalCnfTM)` tag.

**Estimated total:** 2300–2800 LOC across ≥6 sessions. This is the
single largest remaining piece of Part 2.

### Step 12 — Construct `cliqueRelDecTM`

**Goal:** Close the `CliqueRelTM.decider` sorry from Step 3.

**Design:**
- **3 tapes**: input `((G, k), l)`, scratch, accumulator.
- Three sub-checks:
  - `fgraph_wf G`: bound check on vertex indices in the edge list.
  - `l.Nodup`: quadratic scan comparing every pair of vertices in `l`.
  - `l.length = k` (linear).
  - `isfClique`: for every pair (v₁, v₂) ∈ l × l with v₁ ≠ v₂, check
    `(v₁, v₂) ∈ G.2` (quadratic scan of the edge list per pair).
- Re-use `scanRightUntilTM` and the primitives from Step 11
  (`copySegmentTM`, `compareSegmentsTM`).

**Step 12 substeps:**
- **12.0** Define the FlatClique input encoding `encodeFlatCliqueInput`
  in `Deciders/CliqueRelTM.lean` plus length / symbol-bound lemmas.
  ~200 LOC.
- **12.1** Land `nodupCheckTM` (quadratic-scan helper). ~600 LOC.
- **12.2** Land `adjCheckTM` (per-pair adjacency lookup). ~500 LOC.
- **12.3** Compose `cliqueRelDecTM` from the three sub-checks.
  ~400 LOC.
- **12.4** Time-bound proof: `(n + 1)^3` covers nodup (quadratic) and
  adjacency (cubic in worst case). ~250 LOC.
- **12.5** Replace the Step 3 sorry. `lake build` clean. Remove the
  `TODO(Part2-followup:CliqueRelTM)` tag.

**Estimated total:** 1900–2400 LOC across ≥4 sessions.

### Step 13 — Final Part 2 sweep

**Goal:** Part 2 closes with only the two pre-acknowledged structural
sorrys (`red_inNP` TM composition for Part 3, `hasDeciderClassical`
for Part 6).

**Actions:**
- `grep -rn "sorry" CookLevin/Complexity` returns *exactly*:
  - `red_inNP` — `TODO(Part3:red_inNP_TMcompose)`.
  - `hasDeciderClassical` — `TODO(Part6:hasDeciderClassical)`.
- `lake build` clean.
- Update README sorry inventory.
- Update `ROADMAP.md` Part 2 status to ✅.

## Outstanding sorrys (register)

This list is the source of truth for Part 2's open obligations.
Updated at the end of each step.

| Sorry                                                            | Step it appears at | Step that closes it | Status |
|------------------------------------------------------------------|--------------------|--------------------|--------|
| `EvalCnfTM.decider` — `TODO(Part2-followup:EvalCnfTM)`           | Step 2 ✅           | Step 11.7          | open   |
| `CliqueRelTM.decider` — `TODO(Part2-followup:CliqueRelTM)`       | Step 3 ✅           | Step 12.5          | open   |
| `sat_NP` body — closed in Step 5                                 | Step 4 ✅           | Step 5 ✅           | closed |
| `FlatClique_in_NP` body — closed in Step 6                       | Step 4 ✅           | Step 6 ✅           | closed |
| `red_inNP` predicate-level body — closed in Step 7               | Step 4 ✅           | Step 7 ✅           | closed |
| `red_inNP` TM-composition — `TODO(Part3:red_inNP_TMcompose)`     | Step 7 ✅           | Part 3             | open   |
| `P_NP_incl` body — closed in Step 8                              | Step 4 ✅           | Step 8 ✅           | closed |
| `genNPInstance.rel_poly` — closed in Step 9 (replaced by         | Step 4 ✅           | Step 9 ✅           | closed |
|   `hasDeciderClassical _ _` again, now TM-backed)                |                    |                    |        |
| `hasDeciderClassical` body — `TODO(Part6:hasDeciderClassical)`   | Step 9 ✅           | Part 6             | open   |

## Files

Existing (built and frozen):
- `Complexity/Complexity/TMDecider.lean` — `DecidesBy`, `inTimePolyTM`,
  downgrade, `negate`, `iff`. ~220 LOC.
- `Complexity/Complexity/TMEncoding.lean` — list-level encoding
  helpers. ~135 LOC.
- `Complexity/Complexity/TMPrimitives.lean` — `composeFlatTM`,
  `verdictTM`, `scanRightUntilTM`, `runFlatTM_extend`, smoke
  deciders. ~1400 LOC.
- `Complexity/Complexity/Deciders/SAT_TM.lean` — SAT input encoding +
  demonstration deciders (`CnfEmpty`, …, `AssgnContainsZero`).
  ~6400 LOC after Step 1's trim.

New under `Complexity/Complexity/Deciders/`:
- `EvalCnfTM.lean` — the actual SAT verifier TM. Built in Step 11.
  Step 2 lands a stub of ~70 LOC; the full file ends at ≤ 3000 LOC.
- `CliqueRelTM.lean` — the FlatClique verifier TM. Built in Step 12.
  Step 3 lands a stub of ~70 LOC; the full file ends at ≤ 2500 LOC.
- Possibly `EvalCnfTM/Primitives.lean` and `CliqueRelTM/Primitives.lean`
  if file sizes demand splitting.

`Complexity.lean` registers all of the above.

## Risks & open questions

- **The Step 7 `red_inNP` sorry conflates two issues.** It is
  partially closable now (the *predicate*-level composition is
  straightforward), but the *TM*-level composition needs Part 3's
  TM-backed `polyTimeComputable`. We commit to the labelled sorry
  pattern for the latter only; if a clean predicate-level proof
  emerges in Step 7 that closes the full statement, even better.
- **`composeFlatTM_run`** (Step 11.0) is the load-bearing lemma for
  the whole composition strategy. If it turns out to be harder than
  expected (e.g., subtle tape-shape interactions across the bridge
  transitions), we fall back to a *monolithic* evalCnfTM design. In
  that case Step 11 reverts to "the v1 plan" and runs to many
  thousand LOC. The triage decision happens at the end of 11.0.
- **Multi-tape `composeFlatTM`.** The current `composeFlatTM` is
  proven valid only for `M₁.tapes = M₂.tapes = 1`. Step 11 needs to
  generalise to `k ≥ 1`. This is mechanical (the bridge transitions
  need `[none]` of length `k`; the validity proof gains `M₁.tapes =
  M₂.tapes` as a hypothesis). Plan ~100 LOC of generalisation as
  part of Step 11.0.
- **`encodable.size` of the input.** `EvalCnfTM.timeBound (n + 1)^3`
  is generous; the actual O is more like `n^2 log n` if we use a
  smarter lookup. We pick `(n + 1)^3` because it's easy to prove
  the inOPoly bound and definitely subsumes the actual runtime. If
  Part 3 later needs tighter, we revisit.
- **AssgnContainsVar (Step 1).** If the user prefers, the partial
  AssgnContainsVar can be *kept* (finished as a sunset chapter in
  one session — ~600 LOC of reject-path + run + encoding +
  `decider`) instead of deleted. Recommendation is delete because
  it is unused; the choice doesn't affect the rest of the plan.

## Definition of done (Part 2)

- `inTimePoly` is TM-backed; `DecidesBy` witnesses make this
  unmistakeable.
- `sat_NP` and `FlatClique_in_NP` re-proved with concrete TM-backed
  witnesses.
- `red_inNP` and `P_NP_incl` build; remaining gap in `red_inNP` is
  the single `TODO(Part 3) sorry`.
- `hasDeciderClassical` is the only `TODO(Part 6) sorry`.
- `EvalCnfTM.decider` and `CliqueRelTM.decider` are real TMs with
  operational-correctness proofs.
- `README.md` updated; sorry inventory accurate.
- `theorem CookLevin : NPcomplete SAT` typechecks with exactly the
  two structural sorrys.

---

## Lessons learned (consolidated, kept verbatim from v1)

> These remain authoritative for any future TM construction. The
> patterns in here will be reused heavily in Steps 11–12.

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
- **`++` is left-associative for `List`.** A trans list of the shape
  `A1 ++ A2 ++ … ++ A7 ++ FlatMap` parses as
  `((((((A1 ++ A2) ++ A3) ++ A4) ++ A5) ++ A6) ++ A7) ++ FlatMap`, so
  `rcases List.mem_append.mp` peels the **rightmost** segment first.
  Walk from the tail back to the head, using `rotate_left` after each
  split to handle the small right side before recursing into the larger
  left side.
- **Parametric TM families via `def TM (v : Nat) : FlatTM`.** When a TM
  needs a parameter-dependent state count, just make `TM` a function
  of that parameter. State count `states := v + 5` is fine. The validity
  proof becomes parametric: arithmetic bounds use `omega` instead of
  closed `decide`; `subst` over `k ∈ List.range v` extracts `k < v`
  cleanly; the `v = 0` edge case (empty `List.range v`) is handled
  vacuously by `List.mem_map.mp`'s impossibility witness without extra
  branching.
- **`(a == b)` is not `Nat.beq a b` at default reducibility.** Despite
  being defeq under instance unfolding, Lean's `show` / `change` /
  direct `rw` won't bridge between them. Workaround for "entry doesn't
  match" lemmas: `cases hbeq : (entry.src_state == cfg.state_idx)` —
  the `false` branch closes by `rfl` (because `false && _ = false` is
  definitional Bool), and the `true` branch contradicts via
  `by simpa using hbeq` (which unfolds the instance to bridge to
  `LawfulBEq.eq_of_beq`).
- **`beq_self_eq_true` for `(a == a) = true`.** For `[BEq α] [ReflBEq α]`
  (Nat qualifies), `beq_self_eq_true a : (a == a) = true`. Useful in
  match-helpers for entries where the source state equals the cfg state.
- **Find?-helper for parametric per-k blocks: `find_range_map_entry_at`.**
  `((List.range n).map f).find? p = some (f k₀)` when `k₀ < n`,
  `p (f k₀) = true`, and `∀ k' < k₀, p (f k') = false`. Proved by
  induction on `n`, using `List.range_succ`'s right-extension and
  `List.find?_eq_none` for the prefix-no-match case. Reusable across
  any future parametric TM with `List.range`-based transitions.

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

> This pattern is what we apply in Steps 11 and 12, but factored
> through `composeFlatTM_run` so the per-state explosion is bounded
> by the number of *primitives* rather than the number of *states*.
