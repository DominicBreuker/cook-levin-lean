# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). **This file is the forward-looking working plan.**
We work multi-session in two alternating streams — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

**Read in this order.** "Where the proof stands" → "★ Latest session" →
"★ Recommendation for the next session" → the **NEXT** section for your stream →
"Before you push". Everything from "Standing architecture risks" down is a
**reference index**: consult it before building anything, do not read it front
to back. For the evidence files, [`../probes/README.md`](../probes/README.md) is
the authoritative map — this document does not duplicate it.

## Where the proof stands (2026-08-09)

**COOK–LEVIN IS PROVEN, on the honest statement, unconditionally — audited,
non-vacuous, stated with `List Bool` on both sides of the arrow and with the
canonical layout pinned on BOTH sides of the completeness conjunction. `lake
build` carries NINE obligations: the library is `sorry`-free and axiom-clean,
the two audited functions are what the audit says, `Op.cost` is a proven time
proxy, the hypothesis class is non-vacuous, the reviewer's reading list is
complete, that list has been read, the *gates themselves* are metered for what
believing them costs, and — since 2026-08-09 — **the machine model has the
defining properties of a Turing machine**.**

```
SATStrComp.SATStr_NPcompleteStr' : NPcompleteStr' SATStr  -- ★★ QUOTE THIS ONE
CookLevinHonest.CookLevinStr     : NPcompleteStr  SAT     -- SAT is NP-complete
SATStrComp.SATStr_NPcompleteStr  : NPcompleteStr  SATStr  -- weaker membership half
CookLevinHonest.CookLevin''      : NPcomplete''   SAT     -- the general statement
all depend on axioms: [propext, Classical.choice, Quot.sound]
```

| piece | status |
|---|---|
| sound tail, C8 front, tableau maths + both size bounds | ✅ axiom-clean |
| S1 map + guard + program (all stages) + cost ladder | ✅ axiom-clean |
| `FrontS1Comp.SAT_NPhard''` (hardness) / `EvalCnfSplit.SAT_inNPLangFreeSplit` (membership) | ✅ axiom-clean |
| **`SATStrComp.SATStr_NPcompleteStr' : NPcompleteStr' SATStr`** | ✅ both conjuncts canonical |
| both chains' `decodeOut`s (`Serialize cnf` / `Serialize (List Bool)`) | ✅ real parsers, gated in `HonestyGate` |
| axiom/`sorry` hygiene · the audited functions · `Op.cost` as a time proxy · non-vacuity | ✅ *build-time* obligations, not probes |
| the reviewer's reading list is COMPLETE, and has been READ | ✅ `StatementGate.lean` + `StatementMeaning.lean` |
| **the gates are metered, and split into reading vs regression gates** | ✅ **NEW 2026-08-08** — `Complexity/GateSurfaceGate.lean` |
| **the two conjuncts rest on DISJOINT trust (FINDING AZ)** | ✅ **NEW 2026-08-08** — gated, both directions |
| **`FlatTM` has the defining properties of a Turing machine** | ✅ **NEW 2026-08-09** — `Complexity/MachineFaithfulness.lean`, metered at 2 defs |

**The honesty surface that remains** is exactly: the *statement*
(`NPcompleteStr'`, `NPhardStr`, `InNPWitnessStr`), the meaning of `SAT`, the
faithfulness of `FlatTM`/`stepFlatTM` as a Turing machine, and **one**
encoding — `EvalCnfCmd.encodeCnf` (through `SATStr.satStr_iff`) if you quote the
string headline, `Serialize cnf` if you quote `CookLevinStr`.

⚠ **After 2026-08-08 that list is shorter than it reads.** `Op.cost` is off it
for *both* conjuncts (FINDING AZ). ⚠ **And after 2026-08-09 the `FlatTM` item is
narrowed rather than open**: `Complexity/MachineFaithfulness.lean` proves the
seven textbook-defining properties (locality, one-cell head motion, finite and
*enforced* alphabet, finite control, space ≤ time), so what a reviewer still
takes on trust is only that *those are the right seven* — a question about
textbooks, not about this repository. **Nothing on either work stream is now
blocked on a model question.**

⚠ **Do not let any surface list grow silently.** You cannot: the gates fail. But
when one does fail, *do not paste the new list in*. A new name means a
reviewer's obligation changed — say what and why in `README.md` in the same
commit.

## ★ Latest session

**2026-08-09 (top-down) — the last model question got an instrument, and the
model turned out not to be quite the textbook one.**

**Landed: `Complexity/MachineFaithfulness.lean` (in the default build target,
imported by `Complexity.lean` and by `GateSurfaceGate.lean`),
`probes/MachineFaithfulnessProbe.lean`, ten new exact deltas in
`GateSurfaceGate.lean` §2, ROADMAP rows S10 / BB / the simulation verdict,
README's new item 3 of the reading list.**

1. **The go/no-go was run and the answer is: the simulation is feasible but is
   NOT the next thing to build.** ROADMAP risk S10 carries the full verdict with
   all four obstructions pinned against Mathlib's real `Turing.TM0` definitions.
   The reason it comes second is the asymmetry in the next point.
2. ★ **The asymmetry that reframes the whole question.** A model *weaker* than a
   Turing machine makes "the reduction is computed by a `FlatTM` in polynomial
   time" a **stronger** claim, so hardness holds a fortiori. Only *stronger* is
   dangerous. That direction is closed by **locality**, directly and cheaply —
   and a `TM0` simulation would largely be proving the safe direction.
3. **So the deliverable is a file of universally quantified theorems, not a
   simulation.** A step reads one cell and it is the head's; changes at most that
   cell; moves the head at most one place and never past the left end; grows the
   tape by at most one cell; selects its entry from `(state, symbols read)`
   alone; stays inside a finite and *enforced* alphabet and a finite state set;
   and therefore uses **space ≤ time** with a head that cannot jump.
4. ★ **FINDING BB — `FlatTM` is the textbook class RESTRICTED to append-only
   tapes, and nobody had said so.** Four lines
   (`probes/MachineFaithfulnessProbe.lean` §2): on `([], 1, [5])` and
   `([], 2, [5])` the head reads the *same* blank, and the *same* write appends
   on the first and is **dropped** on the second. So a step's tape effect is not
   a function of `(state, symbol read)` — it consults the frontier, which the
   control cannot see. Safe by point 2, and now stated rather than hidden. ⚠ Do
   not read `find?_congr_of_read` as being about the tape effect; it is about the
   *entry selected*, and the two come apart exactly here.
5. **Metered at TWO definitions beyond the headline**, across ten exact deltas.
   The whole machine group of `StatementGate.lean` was already in the headline's
   surface (the hardness conjunct is stated in `runFlatTM` steps), so the file
   answers a model question in the model's own vocabulary. That is the sharpest
   *reading* gate in the repo and the cleanest illustration of FINDING BA's
   distinction.
6. **A small gap the probe turned up.** `validFlatTM` bounds the symbols in the
   transition *table*, not on the initial *tape*, and `ComputesBy.computes` calls
   `runFlatTM` directly, so it never runs `execFlatTM`'s `isValidFlatTapes`
   check — a witness's `encode` *can* put an out-of-alphabet symbol on the tape.
   Harmless: `stuck_of_symbol_ge_sig` proves a valid machine then has no entry
   that can match and stalls. `M.sig` is enforced by the semantics.

**Cost.** All leaf work; `MachineFaithfulness.lean` imports only
`Complexity.Complexity.Definitions` + `TapeMono` + `Batteries.Data.List.Lemmas`
and typechecks in **under 2 s**, so iterate with `lean <file>` and never pay a
rebuild. ⚠ **The gotcha that cost ten minutes, and it is the same one as last
session in a new dress:** a `/-- … -/` docstring cannot precede a `#guard`
either — use `/-! … -/`. ⚠ Second: `List.set_eq_take_cons_drop` takes the
*element* as its explicit argument, not the list, and is in `Batteries`, not in
Lean core — importing `Batteries.Data.List.Lemmas` keeps the module off Mathlib
entirely, which is worth preserving.

## ★ Recommendation for the next session

**Run a BOTTOM-UP session, on bottom-up item 1: membership for `FlatClique`.**

The reasoning is that the top-down stream has just cleared its last *blocking*
item. Every remaining top-down entry is either short and mechanical (items 2–5
below, half an hour to an afternoon each) or a two-session build with nothing
waiting on it (item 1, the `Cmd`-level certificate search). Meanwhile the
development still contains exactly **one** problem on the NP side, which is the
most visible remaining gap to a reader who knows Cook–Levin from a textbook:
they expect a *class*, and they are shown a class with one inhabitant plus a
proof that it has no undecidable ones.

`FlatClique` membership is well-templated (`Deciders/EvalCnfSplit.lean` verbatim
against `cliqueRelDecidesLang`, axiom-clean since 2026-07-01), costs a reviewer
**nothing** — it touches no published headline's statement — and it is the only
remaining item that adds a second problem. Budget one session.

⚠ It now owes **one extra line** beyond the 2026-08-08 rule: per FINDING AZ each
new membership witness owes its machine-level restatement, and per FINDING BB
that restatement is a claim about the *append-only* machine class. One sentence
in the verdict row, not a study.

The alternatives, and why they come second. **Top-down item 3** (the `Cmd`-level
certificate search) is still the last open rung of the mathematics but nothing
waits on it and it touches `Lang/PolyTime.lean` (≈15 min cold rebuild).
**Top-down items 4–6** are good *warm-ups* inside another session rather than
sessions of their own — take item 4 or 5 as the first hour of the session after
next. **Bottom-up item 2** (hardness for `kSAT 3`/`FlatClique`) is the natural
follow-on once item 1 lands, and is the first thing that will exercise the tail
extension machinery again.

## NEXT TOP-DOWN session

The proof is done and nine obligations run inside `lake build`. Top-down work is
still **turning reading obligations into typechecking obligations** — and, since
2026-08-08, keeping the *gates* under the same discipline as the theorems they
gate, and the *linkages* under the same discipline as the gates.

⚠ **The model question is no longer the top item.** It was, for three sessions;
`Complexity/MachineFaithfulness.lean` closed the actionable part of it on
2026-08-09 (ROADMAP S10). What is left of it is item 6 below, and it is
optional.

### 1. Extend the meaning gates to the two remaining hypotheses — SHORT, START HERE if top-down

The pattern that has paid off four times now (`StatementMeaning`,
`GateSurfaceGate`, `MachineFaithfulness`) is: *find the thing a reviewer is told
to read, and state its defining properties as theorems in its own vocabulary*.
Two candidates remain, both cheap:

* **`SAT`/`cnf` (S8 verdict 11).** `StatementMeaning.lean` §5 pins the two
  degenerate cases and three separations at concrete formulas. The general
  statements are missing and are one-liners: `evalCnf` is `List.all` of
  `evalClause`, `evalClause` is `List.any` of `evalLiteral`, so *monotonicity in
  the clause list* and *`SAT (N₁ ++ N₂) ↔ ∃ a, …`* are the shape. Value: it
  turns "read `NP/SAT.lean`" into "read four theorems", exactly as this session
  did for the machine. Meter it in `GateSurfaceGate.lean` §2 — predicted cost
  **0** definitions beyond the headline, and if it is not 0, that is the finding.
* **`certState`/`strBits` (the layout on both sides of the conjunction).**
  `HonestyGate.certState_size` costs 0 and `strTail_enc_eq_head` costs 7. What is
  *not* stated is that `strBits` is injective **as a general theorem** rather
  than through `decBits_strBits`. Half an hour.

⚠ Both are `_delta`-metered against `SATStrComp.SATStr_NPcompleteStr'`. Run
`#print_statement_surface_delta` before committing to a statement's shape.

### 2. Finish the machine story — OPTIONAL, and only with a consumer

Two things `MachineFaithfulness.lean` deliberately did **not** do.

* **The `TM0` simulation** (ROADMAP S10's verdict: feasible, ~2–4 sessions).
  ⚠ **Do not start it as a side quest.** Its value is a second opinion, not a new
  guarantee; the four obstructions are itemised with costs in
  `probes/MachineFaithfulnessProbe.lean` §5. If a future session does take it,
  the direction that matters is *theirs simulates ours*, the alphabet is
  `Option (Fin sig)` decorated with a frontier marker and a left-end marker, and
  the step blowup is a constant.
* **The multi-tape lift.** §§1–6 of `MachineFaithfulness.lean` are stated for the
  tape primitives and are already general; §7's run-level statements
  (`runFlatTM_single_local`) are single-tape, which is all `Compile` emits. If a
  multi-tape machine ever reaches the proof path, generalise via a `zipWith`
  index argument — `stepFlatTM_single` is the lemma to widen, and everything
  above it follows unchanged.

### 3. The `Cmd`-level certificate search — the last rung of non-vacuity

**Target.** `inNPStr Q → ∃ f, Nonempty (DecidesBy Q f)` with `f` exponential: `Q`
is decided by a real `FlatTM` in *this development's own computability model*, not
merely by a Lean function. `Complexity/NonVacuity.lean` already pins the statement
this must reach (`searchDecide_correct` is the pure-model half), so this is a
program-and-cost job, not a design job. **This is the only open rung under ROADMAP
risk S7.**

✅ **The go/no-go is DONE (2026-08-03) and the answer is GREEN — do not redo it,
but do read the caveat.** The question was whether the bridge to a real machine
forces the *time* bound to be polynomial. It does not. `DecidesLang.toDecidesBy`
demands `inOPoly costBound` / `monotonic costBound`, but those two hypotheses are
used at **exactly two field sites**, `encodeBound_poly` and `encodeBound_mono` —
i.e. for the *encoding* bound, not the time bound. `DecidesBy.encode_size`,
`budget_ge`, `decides_pos` and `decides_neg` need no polynomiality at all.

So the bridge you need is a variant taking a **separate** polynomial `encBound`
with `∀ x, State.size (D.encodeIn x) ≤ encBound (size x)`, leaving `costBound`
completely free. **It was written and typechecked in that session** (a copy of
`toDecidesBy` with those three fields retargeted, ~85 lines, no other change) and
then reverted rather than landed, because unused API is exactly what that session
spent a commit deleting. Re-create it when you have a consumer.

⚠ **Caveat that decides where it lives:** `DecidesLang.padTimeBound` and
`DecidesLang.budget_ge` are **`private` to `Lang/PolyTime.lean`**. The variant
therefore has to be added *inside that file*, next to `toDecidesBy` — it cannot
live in a new module, and it cannot live in a probe. Budget it as an edit to
`PolyTime.lean` (≈15 min cold rebuild, everything above it in the import graph
pays).

**The program.** Registers **above** `W.verifier.regBound` (FINDING AE:
`usesBelow` means the verifier cannot touch them), so the enumerator owes no scrub
of its own state:

* `1^(2^(B+1))` as the outer loop's bound register — `B` doubling steps
  `forBnd cnt Breg (concat r r r)`. ⚠ This is exactly the shape
  `probes/CostChkIntentProbe.lean` pins `Cmd.chk` as **rejecting**; that is
  correct and expected — no polynomial bound is being claimed here, so the cost
  ladder of `Lang/CostGrow.lean` is **not** the tool. The bound must be built by
  hand from `Cmd.cost_seq`/`cost_forBnd_flat_le` (`Lang/CostFlat.lean`).
* the candidate as a `B`-bit register with a ripple-carry increment
  (`head`/`tail`/`concat`/`eqBit`, carry in one register);
* per iteration: restore register `0` from a saved copy, write the candidate to
  register `1`, `S1SATComp.clearRange 2 W.verifier.regBound` (reuse it — do not
  write a second scrub gadget), run `W.verifier.c`, OR the verdict into a found
  flag.
* the `_run` lemma is a stateful loop: use **`S1Step.emitFold_run`**, invariant
  "`FOUND = 1` ↔ `∃ j < i`, the verifier accepts candidate `j`" ∧ "`CAND` is the
  binary representation of `i`". ⚠ **Write that invariant as a `Bool` function and
  `#eval` it at every index before proving anything** (FINDING AI).
  `probes/SATStrProbe.lean` §6 is the shape to copy.

Budget: one session for the program + `_run` (the go/no-go is already spent), a
second for the cost bound. **Do not start it as a side quest**, and do not weaken
the target to the classically trivial existential
(`NonVacuity.inNPStr_exists_decider` is already there, labelled).

### 4. Generalise `satStr_membership_is_machine_time` to the whole class — SHORT (~30 lines)

`GateSurfaceGate.satStr_membership_is_machine_time` discharges the cost model for
`SATStr`'s membership conjunct. The same statement holds for **every** inhabitant
of the class, by the same one-liner:

```lean
theorem inNPStr_machine_time {Q : List Bool → Prop} (h : inNPStr Q) :
    ∃ rel, polyCertRel Q rel ∧ inTimePoly (fun p : List Bool × List Bool => rel p.1 p.2)
```

from `W.verifier.toInTimePoly W.dBound_poly W.dBound_mono`. Value: it turns
FINDING AZ from a fact about our one instance into a fact about the class, which
is what a reviewer actually wants to know about `inNPStr`.

⚠ **The design question to decide explicitly, and it is why this was not just
done:** the *hypothesis* `inNPStr Q` mentions `Cmd.cost`, so a plain `_omits`
assertion on the general theorem will **fail**. That is exactly why
`GateSurfaceGate.lean` §1 states its pins at concrete languages. Choose one:
keep the concrete pins as the gated evidence and add the general theorem
un-metered; or add a conclusion-only helper to meter; or state the verdict in
prose and say why it cannot be gated. Do not quietly drop the `_omits`.

### 5. Meter the rest of `StatementMeaning` — SHORT, mechanical

Only the four spelled-out restatements are metered. §§2–5's pins (rejection is a
verdict, the tape's edges, the empty CNF, the input measure) are not. Their
surfaces should be tiny and mostly subsets of the headline's; if one is not, that
pin is saying something about a definition outside the reading list and the S8
verdict behind it needs re-checking. Half an hour, and it either confirms the
classification or finds something.

### 6. Retire `SATStr.strEIn`'s duplicate of the canonical layout — SHORT

`Deciders/SATStr.lean` still defines `strEIn v = certState v.1 ++ certState v.2`
locally, and `EvalCnfSplit.satEIn` does the same job on the CNF side. Now that
`Lang/SerializeStr.lean` owns `strBits`, check whether `strEIn` can be stated as
`certState`-only (it can: `strEIn_lit` is already `[strBits x, strBits c]`) and
whether a single `certPairState` in the `Lang` layer would serve both. **Do this
only if it stays a rename** — the `_run` lemmas in `SATStr.lean` are pinned to
`strEIn`'s exact shape, so if the change reaches a proof body, stop and leave a
note instead. Value: one fewer layout name for a reviewer.

### 7. Audit whatever the bottom-up stream lands (S5 + S8 + S9, standing but SHORT)

By FINDING AK only the composite's **leftmost `encodeIn`** and **rightmost
`decodeOut`** matter, and by FINDING AL a seam's `mfc` needs no audit.

* head extension → nothing to do if the chain is entered through `NPhardStr`;
  otherwise audit `encX` against the criterion: every register is a constant, a
  mechanical serialization of an input field, or a *metric* of the input — never
  the reduction's output. (And it must supply `sizeLB`, which for any layout that
  spells the input out is `id` or a small multiple.)
* **tail extension → give the new output type a `Serialize` instance and define
  `decodeOut := Serialize.decodeD default ∘ get OUTREG`.** Do not hand-write an
  inverse and do not use `Function.invFun`. Two worked examples:
  `Deciders/CnfSerialize.lean` (a fuel-based parser for a real grammar, ~200
  lines) and `Lang/SerializeStr.lean` (the cell-wise one, ~40). ⚠ **Check the new
  type's `encodable.size` against the layout's cell count before writing the
  instance** (FINDING AT).
* **tail extension also needs the left composite's exit register** — use
  `SATStrComp.ExitsOnCNFOUT`/`exitsOnCNFOUT_comp` (FINDING AU); do not unfold the
  composite.
* middle witness or seam `mfc` → nothing to audit; say so in one line.
* a new **verifier** owes the `DecidesLang` version of the same check plus a
  `polyCertRel` (machine-checked non-vacuity — do not re-derive it).
* add a numbered verdict row to ROADMAP **S5**, a `#assert_axioms_clean` line to
  `Complexity/SoundnessGate.lean`, and a section to
  `probes/HonestyAuditProbe.lean` if it is `rfl`-checkable — prefer
  `Complexity/HonestyGate.lean` for a positive pin, the probe for a negative
  control.
* **(S8) if the session publishes a new *headline*, it owes a
  `#assert_statement_surface` block in `Complexity/StatementGate.lean` and a
  sentence in the README saying what a reviewer now has to read.** Run
  `#print_statement_surface` **before** you commit to the shape of the statement:
  it is seconds, and it tells you what the choice costs a reader. Extending the
  *chain* costs nothing (reductions are existentially quantified); publishing a
  new *language* pulls that language's whole definition in.
  ⚠ **If the new headline is a completeness statement for a string language,
  state it as `NPcompleteStr'` (`NPhardStr P ∧ inNPStr P`), not `NPcompleteStr`**
  (FINDING AX). The witness must be an `InNPWitnessStr`; do not weaken it with
  `.toInNPWitnessLangFreeSplit` on the way into the headline.
* **(S9, NEW) if the session adds a *gate* — any theorem a reviewer is told to
  believe instead of re-doing work — it owes a block in
  `Complexity/GateSurfaceGate.lean`.** Run `#print_statement_surface_delta`
  first and decide which kind it is:
  * cost ≲ 15 definitions beyond the headline → it is a **reading gate**; paste
    the exact delta and say in one line what the new names are;
  * cost in the hundreds → it is a **regression gate** (FINDING BA). Do **not**
    paste the list. Say so, and gate instead (a) its `_contains` shape and (b)
    its **linkage** to the object actually on the proof path — that linkage is
    what `deciderBridge_machine` is, and it is the thing that was missing.
* a new row in `probes/README.md` if the session adds a probe.

### 8. The `.github/` residue — owner decision, not ours

`.github/workflows/lake-build.yml` **already exists and already runs
`lake build`**, so the "CI question" of earlier handoffs is answered: CI is
green-gated on everything the build gates. If the owner wants the *negative*
controls covered, add `lean probes/HonestyAuditProbe.lean`,
`lean probes/CostChkIntentProbe.lean`, `lean probes/NonVacuityProbe.lean`,
`lean probes/SATToSATStrProbe.lean` and `lean probes/StatementSurfaceProbe.lean`
— the positive pins are already in the build. ⚠ **Agent sessions have no workflow
permission; do not attempt this edit.**

⚠ Stale, **not fixed here**: `.github/scripts/researcher.py` still names the
deleted `coqdoc/` folder as "the blueprint", and `.github/prompts/step*.md` still
cite files under it. That subtree is the owner's legacy porting harness. Flag it,
do not quietly edit it.

## NEXT BOTTOM-UP session

**Nothing on the critical path is waiting on a gadget.** The chain is closed at
both ends and all headline statements are proven. Everything below is *scope
extension*: more problems in the class, which is what makes the development
useful beyond the single theorem — and after 2026-08-09 it is also **the most
visible remaining gap to a textbook reader**, who expects a class of problems and
is currently shown a class with one inhabitant. That is why item 1 is the
recommendation for the next session, not merely the first item in a list.

⚠ **NEW (2026-08-09, FINDING BB — one sentence per verdict row, and it is not
optional).** `FlatTM` is the class of deterministic single-tape Turing machines
**restricted to append-only tapes**: a write strictly beyond the frontier is
dropped, so a step's tape effect is *not* a function of `(state, symbol read)`
(`probes/MachineFaithfulnessProbe.lean` §2). This is safe — the restriction makes
every "computed by a `FlatTM` in polynomial time" claim *stronger* than the
textbook one — but it means a verdict row must not say "decided by a Turing
machine" without the qualification. Say **"by a `FlatTM`, i.e. a Turing machine
with an append-only tape (ROADMAP S10 / FINDING BB)"**, once, and move on. ⚠ The
practical corollary for a *builder*: never write a gadget that relies on writing
past the frontier and coming back — the write is silently lost.
`Complexity/MachineFaithfulness.lean` §3 is the reference for what a step can and
cannot do.

⚠ **Interface note.** `InNPWitnessLangFreeSplit` carries `sizeLB` /
`sizeLB_poly` / `encX_sizeLB` (since 2026-08-02). Every **verifier/membership**
witness must supply them; for any layout that writes the input out it is one
line. `PolyTimeComputableLang` is untouched, so **reduction** witnesses are
unaffected.

⚠ **NEW (2026-08-07, FINDING AX — read this before choosing an item).** A
membership witness is worth strictly more if it is an **`InNPWitnessStr`** (the
canonical `certState` layout) rather than a bare `InNPWitnessLangFreeSplit`:
the latter class is inhabited by *every* string language, so a headline stated
over it makes no claim (`probes/HonestyAuditProbe.lean` §7c). If the problem you
are giving membership to is (or can be given as) a string language, build the
`InNPWitnessStr` and publish through `NPcompleteStr'`. If it is not a string
language, say so in the verdict row rather than letting a reader assume the
conjunct means more than it does.

⚠ **NEW (2026-08-08, FINDING AZ — one extra line per membership witness, and it
is worth it).** A membership witness proves `inNPStr Q`, which is stated
**entirely in `Cmd.cost`** — as a claim it contains no Turing machine at all,
and it is `Complexity/CostFaithfulness.lean` alone that makes it a claim about
time. So **every new membership witness owes its machine-level restatement**,
next to the `inNPStr` theorem:

```lean
theorem foo_membership_is_machine_time :
    ∃ rel, polyCertRel Foo rel ∧ inTimePoly (fun p => rel p.1 p.2) :=
  let W := fooWitness.toInNPWitnessLangFreeSplit
  ⟨W.rel, W.rel_correct, W.verifier.toInTimePoly W.dBound_poly W.dBound_mono⟩
```

One line, and it is what lets a reader take the result at face value.
`GateSurfaceGate.satStr_membership_is_machine_time` is the worked example; meter
it there with `_omits` on `Op.cost`/`Cmd.cost`/`Cmd`/`Op`. ⚠ The **hardness**
side needs nothing of the kind — it is already stated in `runFlatTM` steps.

⚠ **Statement-surface note.** `Complexity/StatementGate.lean` fails the build if
a headline's statement changes. Three cases, very different in cost:

* **extending the chain** (a new reduction, a new seam) changes **nothing** —
  reductions are existentially quantified and never appear in a surface. Free;
* **membership for another problem** (`inNPLangFreeSplit FlatClique`) does not
  touch any published headline either. Also free;
* **publishing a new headline** pulls that language's entire definition into a
  reviewer's obligation — `SATStr` cost eleven names, and a graph problem will
  cost more. Run `#print_statement_surface` on the candidate *before* building
  it, and say in the README what you are asking a reader to take on.

⚠ **Build-cost note (worth planning around).** A session that touches only
`Deciders/*`, `Reductions/*` and the gates pays seconds per file. A session that
touches `Lang/PolyTime.lean`, `Lang/Syntax.lean` or `Lang/Semantics.lean` pays
the full ~15 min rebuild (`Reductions/S1Witness.lean` alone is ~11 min) —
**including for a comment fix**, which is what the 2026-08-07 session paid for
two stale module headers. The 2026-08-05 session deliberately put three generic
lemmas (`comp_exit`, `exitsOnCNFOUT_comp`, `lt_comp_regBound`) in a *leaf* file
rather than in `PolyTime.lean` where they conceptually belong. **Move them up
when a second consumer appears** — and when you do, batch it with every other
`PolyTime.lean` edit you have queued.

### 1. Membership for `FlatClique` (~1 session, well-templated) — START HERE

Repeat `Deciders/EvalCnfSplit.lean` verbatim against `cliqueRelDecidesLang`
(axiom-clean since 2026-07-01):

* a **total** `List Bool` certificate relation — characteristic vector, never a
  sentinel format (FINDING AG);
* a split `encX`/`eIn` literal (FINDING AD: `precomposeFree` *chooses* the
  composite's `encodeIn`, so trailing scratch registers are invisible — check
  `AgreeBelow regBound`, not list equality);
* a one-register re-encoder `Cmd` with its scratch **above** the verifier's
  `regBound` (FINDING AE — then it owes no scrub);
* cost by `Cmd.chk` (`by decide`), frame by `Cmd.writes`;
* `sizeLB`;
* the `_run` lemma — and **write its loop invariant as a `Bool` function and
  `#eval` it at every index first** (FINDING AI). `probes/SATStrProbe.lean` §6
  is the most recent worked example.

Why first: it is the only remaining item that adds a *second* problem to the NP
side of this development, everything it needs already exists, and by the
statement-surface note above it costs a reviewer **nothing** — it does not touch
any published headline's statement.

⚠ Per FINDING AX, note in the verdict row that this produces an
`inNPLangFreeSplit`, i.e. a witness whose honesty is a per-witness fact (S5) and
**not** something the class enforces. Do not describe it as "`FlatClique` is in
NP" without that qualification, and do not publish it as a headline conjunct.

### 2. Hardness — `SAT ⪯p' kSAT 3`, `kSAT 3 ⪯p' FlatClique`

Free-line witnesses (template: `NP/kSAT_to_SAT_free.lean`, which already does
the mirror-image `kSAT 3 ⪯p' SAT`), then one `SeamData`/`comp` each onto
`FrontS1Comp.front_to_SAT_witness`, and `NPhard''`/`NPhardStr` transport for
free. ⚠ **This extends the chain at the TAIL**, so:
* the composite's `decodeOut` becomes the new last witness's — **the new output
  type owes a `Serialize` instance** (`FlatClique`'s output is a graph + a `k`;
  write the parser, do not use `Function.invFun`), and check FINDING AT first;
* you will need the left composite's **exit register**: use
  `SATStrComp.ExitsOnCNFOUT`/`exitsOnCNFOUT_comp` (FINDING AU). Note that the
  existing statement is specialised to `CNFOUT` and to `cnf`-valued maps —
  generalising it over the register and the output type is ~10 lines and is
  exactly the "third consumer" trigger for moving it into `Lang/PolyTime.lean`.

One verdict row, not a study; see top-down item 6.

### 3. Membership for `kSAT 3` (~1 session) — same shape as item 1

`KSat3Free` already has the re-encoder pattern. Same FINDING AX caveat.

### 4. `FlatCliqueStr` / `kSAT3Str` — string forms, now that the recipe exists

`Deciders/SATStr.lean` is a **template**: a string language for any problem whose
canonical `encodeIn` is already a flat `0`/`1` stream is (a) a DFA recognising
that encoder's image, with the `⇔` proven; (b) a `parseTotal` sending
non-encodings to a canonical *rejecting* value; (c) one validate-and-count scan;
(d) `precomposeFree` onto the existing verifier. Steps (a)–(c) are ~350 lines
each. **And the reverse direction is now also templated**:
`Reductions/SAT_to_SATStr_free.lean` + `_comp.lean` is ~250 lines end to end,
of which the seam is 40. Do this only if a consumer asks — one string language
in the class is already enough for non-vacuity, and `SATStr` is already
NP-complete in the strict sense.

⚠ Do **not** pre-factor `satPrecomposeData`/`satSplitWitnessOf`/
`strPrecomposeData` into a generic combinator before a third consumer exists —
copy first, factor when a third appears (that is how `emitFold_run` was found).

**Do NOT re-open**, on pain of re-proving an axiom-clean theorem: `s1Key`,
`s1RegBound`, `EScratch`/`CDirty`, `stageC_run`'s statement, the seams' scrub
ranges, `S1Step.stepSeg`/`stepEmit`'s contract, the entry loop's register
table, the `copy r r` no-op (FINDING X),
**`EvalCnfCmd.encodeState`/`evalCnfCmd`/`regBound = 16`**,
**`satEncX`/`satEIn`/`xWidth = 3`** (FINDING AD), **`certDecode`/
`decodeBody`/`DCUR`=16/`DIDX`=17/`DHD`=18** (the `_run` lemma is pinned to that
exact program), **`SATStr`'s scan frame `WCUR`=19…`WTAL`=24 and
`CnfWellFormed.scanStep`** (`scanBody_run` and `satStrBuild_get` are pinned to
both), or **`SATToSATStr.OUT`=0 / `SATStrComp.strMfc`** (the sixth seam's bridge
is `AgreeBelow 1` and depends on both). Stage C's 30-register licence is
**exactly** exhausted. And do not rebuild `Cmd.PolyCost` (FINDING AJ) or the
`LangEncodable` layer.

## Before you push

**`lake build` is the gate, and it now carries nine obligations.** If it is
green, then every declaration under `Complexity` is `sorry`-free and uses only
Lean's three axioms (`#assert_library_axiom_clean`), the two audited functions
are what the audit says they are (`Complexity/HonestyGate.lean`), `Op.cost` is a
proven time proxy (`Complexity/CostFaithfulness.lean`), the hypothesis of the
headline is non-vacuous (`Complexity/NonVacuity.lean`), **the reviewer's reading
list is exactly the one written down** (`Complexity/StatementGate.lean`, three
headlines), **the checkable verdicts of the audit of that list still hold**
(`Complexity/StatementMeaning.lean`) and — since 2026-08-08 — **each of those
instruments still costs a reviewer exactly what it is documented to cost**
(`Complexity/GateSurfaceGate.lean`) and — since 2026-08-09 — **the machine model
still has the defining properties of a Turing machine**
(`Complexity/MachineFaithfulness.lean`). You do not need to run `AxiomProbe`, and you
must **never** "fix" a gate failure by deleting the assertion or by pasting the
new list in without reading it.

⚠ `StatementMeaning.lean` is a **gate, not documentation.** If one of its pins
breaks, a definition in the reading list changed meaning and a ROADMAP S8
verdict is now wrong. Fix the verdict in the same commit — do not delete the
pin.

⚠ `GateSurfaceGate.lean` is the same, one level up. Its §1 `_omits` assertions
are the evidence for FINDING AZ — *the two conjuncts of the headline rest on
disjoint trust*. If one of them fires, a conjunct has started depending on
something it was advertised as independent of, and the README's trust table is
now wrong. Fix the table, not the assertion.

⚠ `MachineFaithfulness.lean` is the same again. If one of its theorems stops
holding, the *machine model* changed — and by ROADMAP S10 that is the one place
where a change is a change to what the theorem means, not to how it is proved.
Fix the model or the ROADMAP verdict; do not weaken a locality statement to make
it pass. ⚠ The one that is easiest to break by accident is
`tapeCell_write_of_ne` (locality): any edit to `writeCurrentTapeSymbol` that
re-introduces padding, shifting or multi-cell effects breaks it, which is exactly
what it is there for. `probes/MachineFaithfulnessProbe.lean` §1 carries the
rejected model that fails it.

Six things the build does **not** check — the negative controls. They are the
files that prove the positive gates could still fail:

```
export PATH="$HOME/.elan/bin:$PATH"
lake build                                   # the nine-obligation gate
export LEAN_PATH=$(lake env printenv LEAN_PATH)
lean probes/HonestyAuditProbe.lean           # ~3 s — the S5 evidence file
lean probes/CostChkIntentProbe.lean          # ~3 s — what `Cmd.chk` must accept/reject
lean probes/NonVacuityProbe.lean             # ~4 s — the decider actually runs
lean probes/SATToSATStrProbe.lean            # ~5 s — §1 is FINDING AT's control
lean probes/StatementSurfaceProbe.lean       # ~10 s — the surface gates can still fail
                                             #          (§§6-9: the delta + shape forms)
lean probes/MachineFaithfulnessProbe.lean    # ~3 s — locality's negative control (§1),
                                             #        FINDING BB (§2), the TM0 go/no-go
```

⚠ **`probes/HonestyAuditProbe.lean` §7c is the newest negative control and the
most load-bearing one**: it proves `inNPLangFreeSplit Q` for an *arbitrary*
`Q`, i.e. that the membership conjunct of `NPcompleteStr` says nothing. It is
what justifies `NPcompleteStr'` existing at all (FINDING AX). If it ever stops
elaborating, the argument for the strict headline has lost its evidence.

⚠ **Build-time gotcha:** a cold `lake build` is ~15 min and
`Reductions/S1Witness.lean` alone is **11 min** (the cost ladder's
`decide +kernel`). Anything at or above `Lang/PolyTime.lean` in the import graph
pays it — **including a comment fix in `Lang/Compile/*`**, which is how the
2026-08-06 session bought a full rebuild for two dangling probe references. For
iteration use `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean <file>` on the
single file — seconds instead of minutes — and `lake build` only at the end.
⚠ `lean <file>` needs the *dependencies'* oleans to be current, so do one
`lake build` of the subtree below your edit first. **Start the first `lake build`
of a session as a background job**; the warm-cache case is ~10 s but you cannot
tell in advance.

### The probe regression list — now indexed

**[`../probes/README.md`](../probes/README.md) is the authoritative map**: all
49 files sorted into ★ GATE / REGRESSION / ARCHAEOLOGY, each with what it pins,
its **measured** runtime and when to re-run it. Do not re-derive that list here;
the short version is:

* the six gates above, always;
* `probes/SATStrProbe.lean` (10 s), `SATSplitProbe` (4 s), `SeamS1Probe` (4 s)
  and the `S1*` family — after touching the module each names;
* ⚠ **one** slow file, not two: `S1PreludeEmitProbe` is **402 s** measured.
  `S1StepLoopProbe` is **21 s** (this document said "~3 min" until 2026-08-06)
  and `S1CardEmitProbe` 34 s; everything else is under 25 s. The emitter still
  appends cell by cell, so interpreting it is quadratic — keep every new probe
  instance at `σ ≤ 1`;
* `probes/AxiomProbe.lean` is the *reporting* instrument, not a gate.

⚠ **A probe file that does not elaborate is worse than no probe file** — it
reads as evidence and is not. Two were deleted on 2026-08-06 for exactly this.
If you add a probe, add its row to `probes/README.md`; if you break one, fix it
or delete it in the same commit.

## The S1 register frame — PINNED

```
stage P/G (Reductions/S1Parse.lean)
0  ZERO (andIn no-op target; ends [])   6  PSIG      12 PNTRANS   17 FLG
1  MREG (in) / SIGMA (out)              7  PTAPES    13 PTRANS    18 VAL
2  SREG (in) / INIT  (out)              8  PSTATES   14 SCAN      20 RES
3  1^maxSize (in) / CARDS (out)         9  PSTART    15 HEAD  ⊘   21 ONE
4  1^steps   (in) / FINAL (out)        10  PNHALT    16 INBLK ⊘   23 TSCAN
5  STEPS (out)                         11  PHALT     22 LT_B  ⊘   24 NEF
                                                     26 SKIPR ⊘   27–31 I1–I5
the emitters (Reductions/S1Emit.lean)     stage C (Reductions/S1CardEmit.lean)
32 EOUT_S  Σ's output (1^PSg)             14 CBV  1^(bv sig states)
33 EOUT_I  I's output                     18 CS1  1^(sig+1)
34 EOUT_C  C's output                     19 CS2  1^(sig+2)
35 EOUT_F  F's output                     20 CQ1  1^(states+1)
36 EOUT_T  1^(steps+1) (stage M)          21 CX   1^(xv sig states x)
37 ESG  1^(Sg M)   42 EE  scratch         23 CH   1^((sig+1)(q+1))
38 EA / 39 EB / 40 EC / 41 ED             24 CD   the draining PHALT
43 EJ1 / 44 EJ2 / 45 EJ3  counters        25 CE   the popped halt bit
46 EK1 / 47 EK2  scratch                  27 CZ   [] (the zero source)
s1RegBound = 48
```
`32`–`36` persist to stage M; `37`–`47` are scratch every stage reuses. Stage C
reuses the P/G block `[14,32)` for its constants (it is free once stage G has
run) and `EE`/`EJ1`–`EK2` for its counters; `S1Program.cFive_frame` proves that
set sits inside `CDirty`. The two seams scrub against `s1RegBound = 48` and the
tail composite's `57` — **changing `s1RegBound` means changing
`S1SATComp.scrub4` and re-running `probes/SeamS1Probe.lean` §1.**

**Stage C's prelude family (`S1Prelude.lean` + `S1PreludeEmit.lean`) — PINNED
and BUILT. `PPAᵢ` holds `1^pav` (`pav = base` for a star kind, `base + add`
otherwise) and `PJᵢ` is owned by the resolution level alone — see FINDING G:**

```
14 PBV  1^(bv σ st)      19 PKV2 1^k₂    23 PKV3 1^k₃    28 PJ1 res level 1's j
15 PKV1 1^k₁             20 PST2 star?   24 PST3 star?   29 PJ2 res level 2's j
16 PST1 star?            21 PPA2 1^pav   25 PPA3 1^pav   30 PJ3 res level 3's j
17 PPA1 1^pav            22 PKC2 band    26 PKC3 band    31 PCS2 cut-seen → 2
18 PKC1 band counter     27 PZ   []                      38 PCS3 cut-seen → 3
37 ESG 1^(Sg M)=1^sgv   39 PHB 1^(hv σ q0 0)   41 PQ0 1^q0    43 PCN preamble cnt
40 PB5 1^5              42 PDR the min drain   44 PA1 1^(q0+1) 45 PA2 1^(σ+1)
46 EK1 tally + block cnt 47 PFL preamble flag  34 EOUT_C the output
```
`PCS3 = S1Emit.EA` is a deliberate reuse of `loadSg`'s scratch, dead once the
preamble has finished. `S1Prelude.PDirty` is the list, `PDirty_cdirty` the proof
it is inside the licence, `probes/S1PreludeEmitProbe.lean` §3 the numeric check.

**Stage C's `stepBlocks` family (`S1StepEmit.lean` + `S1StepLoop.lean`) —
PINNED and BUILT. It emits *before* the prelude, and `pPre` rebuilds every
constant the prelude's nest reads, so the two frames need not agree (FINDING E,
weakened). ⚠ These 30 registers are ALL of `S1Program.CDirty`: the licence is
now EXACTLY full, so a new gadget here must reuse, never claim:**

```
constants (SConst, established by cFive — S1Step.SConst_of_cFive, free)
14 CBV 1^(bv σ st)   18 CS1 1^(σ+1)   19 CS2 1^(σ+2)   27 CZ []   6 PSIG 1^σ
per entry (SEntry, published by S1Step.entryPre)
20 TQ  1^((σ+1)(q+1))   23 TQ2 1^((σ+1)(q'+1))   24 TR  1^(rOf σ mT mV)
25 TW0 1^(wOf … false)  17 TW1 1^(wOf … true)    39 TFN "mv=2"  40 TFR "mv=1"
written by the entry body — SD3 = [TJ3,EK1] ⊂ SD2 = [TJ2,TJ3,EK1] ⊂ SD1
21 CX 1^(xv σ st x)  28/29/30 TJ1/TJ2/TJ3 counters  42 EE  46 EK1  34 EOUT_C
the entry loop (S1StepLoop.lean; LD = all of the above minus SConst, plus:)
41 SCUR  the PTRANS cursor        43 SSEEN the seen-key stream (encSyms, PREPEND)
44 SCNT  the loop counter         45 SKP   "emit this entry?"
31 SKQ   src_state, then "mTag=0" 37 SKT / 38 SKV  the option (tag, val), 2×
47 SAX   transient                22 SIX   readItem's index (LT_B; no ltCheck here)
15/16/26  CliqueRelTM.readNum's reserved HEAD/INBLK/SKIPR
```
`probes/S1StepEmitProbe.lean` §2 measures the entry body's write set as exactly
`SD1 ∪ {EOUT_C}`; `S1Step.LD` is the loop's, and `S1Program.LD_cdirty` proves it
sits inside the licence. **`SD1` doubles as the preamble's scratch** — `stepEmit`
clobbers it anyway, which is what makes the 30 registers suffice.

⚠ What no part of `stepBlocks` may touch: anything outside `CDirty` — the input
layout `1`–`5`, `PSIG`/`PSTATES`/`PSTART`/`PHALT`/`PNTRANS`/`PTRANS`, and
`EOUT_S`/`EOUT_I`.

## Composed-chain layouts — PINNED

* **chain head** (`Reductions/HeadLayout.lean`, frozen 2026-07-18):
  `headEncodeIn (M,s,maxSize,steps) = [[], encSyms (flattenTM M), encSyms s,
  1^maxSize, 1^steps]`, `headRegBound = 5`. C8-5's `mfc` keeps `0`–`4` and
  erases `[5,57)`.
* **S1 exit = tail entry**: `FlatTCCFree.encodeIn C = [] :: S1Program.s1Key C`
  (6 registers). The fourth seam's `mfc` keeps `1`–`5`, erases `0` and
  `[6,48)`; `[48,57)` closes by `Cmd.eval_length_le`.
* **`SATStr` chain end** (`regBound = 1`, 2026-08-05): the sixth seam's `mfc`
  is `copy 0 2`, the right witness's `encodeIn N = [Serialize.enc N]` and its
  `decodeOut` is `Serialize.decodeD [] ∘ get 0`. The bridge is `AgreeBelow 1`,
  so **nothing above register 0 is constrained** — changing `SATToSATStr.OUT`
  re-opens it, nothing else does.
* **tail exit** (`regBound = 57`): reg 1 = `1^|N|`, reg 2 = `encodeCnf N` (the
  SAT verifier's `CLAUSE_TALLY`/`CNF_STREAM` layout; `decodeOut =
  `Serialize.dec` on reg 2 — the canonical CNF **parser**
  `CnfSerialize.decCnf`, 2026-08-01; it used to be `Function.invFun encodeCnf`),
  reg 0 = `serF f`, `buildSAT` scratch 3–26 dirty, 27–56 hold the left
  composite's residue, `≥ 57` read `[]`.

## The free line — the working architecture (use this, and only this)

- **Verifiers**: free `DecidesLang` with bespoke bit-level `encodeIn`
  (numbers UNARY) → `DecidesLang.toDecidesBy`/`toInTimePoly` (live:
  `evalCnfDecidesLang`, `cliqueRelDecidesLang`).
- **String-language NP witnesses** (`InNPWitnessStr`): copy
  `Deciders/SATStr.lean`. The recipe is (a) a DFA recognising the target
  verifier's own encoder image, with the `⇔` proven; (b) a total decode sending
  non-encodings to a canonical *rejecting* value; (c) one validate-and-count
  scan as the re-encoder `Cmd`; (d) `precomposeFree` onto the existing verifier.
  Live: `SATStr.satStrWitness`, `NonVacuity.squareWitness`.
- **NP witnesses**: `InNPWitnessLangFree`/`inNPLangFree` (+ `inNPLangFree_to_inNP`);
  hardness is quantified over `InNPWitnessLangFreeSplit` (`NPhard''`), and — for
  the statement we publish — over `InNPWitnessStr` (`NPhardStr`,
  `Lang/HardnessStr.lean`), which is the same thing with the input layout pinned
  to `certState`. **Quote `SATStrComp.SATStr_NPcompleteStr' : NPcompleteStr' SATStr`
  — see standing risks 6 and 10.**
- **Serialization at a chain END**: `Lang/Serialize.lean` — one instance per
  concrete type, `dec_enc` + bit-level + the size sandwich (the lower half is a
  *polynomial* law, `sizeLB`, since FINDING AT). Live: `Serialize cnf`
  (`Deciders/CnfSerialize.lean`) and `Serialize (List Bool)`
  (`Lang/SerializeStr.lean`, whose `enc` is `strBits` — the same function as the
  canonical head layout `certState`). A new chain end owes an instance, not a
  hand-written inverse — and owes a check of the type's `encodable.size` against
  the layout's cell count *before* the instance is written.
- **Reductions**: free `PolyTimeComputableLang` → `toFrameworkWitness'`/
  `reducesPolyMO'_of_langFree`; verifier precomposition via
  `DecidesLang.FreePrecomposeData`/`red_inNP_of_langFree`; **witness-witness
  composition via `SeamData`/`comp` — LIVE SIX TIMES**
  (`FlatTCCBinComp.flatTCC_to_binaryCC_seam` →
  `BinaryCCFSATComp.binaryCC_to_FSAT_seam` → `FSATSATComp.fsat_to_SAT_seam` →
  `S1SATComp.s1_to_SAT_seam` → `FrontS1Comp.front_to_SAT_seam` →
  `SATStrComp.front_to_SATStr_seam`).
  ⚠ A seam whose bridge needs the LEFT composite's **exit register content**
  cannot get it from `computes` (FINDING AU) — use
  `SATStrComp.ExitsOnCNFOUT`/`exitsOnCNFOUT_comp`.
  Five seam shapes exist; pick the one that matches:
  - **wider right frame** → length argument (`BinaryCC_to_FSAT_comp.lean`);
  - **narrower right frame** → no scrub above it (`FSAT_to_SAT_comp.lean`);
  - **left is a composite** → stacked seam, unfold its `.c` with one `heval`
    and push the previous bridge through with `Cmd.eval_agree`
    (`BinaryCC_to_FSAT_comp.lean`);
  - **right is a composite** (preferred at the head of the chain — FINDING A)
    → nothing to unfold, just scrub to the composite's frame
    (`Front_to_S1_comp.lean`);
  - **right frame is ONE register** (a tail extension onto a `Serialize`-pinned
    end) → no scrub at all, the `mfc` is a single `copy`
    (`SAT_to_SATStr_comp.lean` — the cheapest of the six).
- **Templates for new reduction witnesses** — copy these, not first principles:
  - `NP/kSAT_to_SAT_free.lean`: re-encoder + reduction sharing one program,
    fold invariants, tight `encodeIn_size`, `FreePrecomposeData`.
  - `Reductions/FlatTCC_to_FlatCC_free.lean`: the unguarded-map pattern
    (backward validity transfer + unconditional iff), shared-layout registers,
    `blockMove`/`halfMove` stream re-formatting, `encSList` prefix-free
    injectivity, multi-field decode via `Function.invFun encKey`.
  - `Reductions/FlatCC_to_BinaryCC_free.lean`: **the guarded-map pattern** —
    on-machine validity flag (`allLtB` reflection ↔ `isValidFlattening` via
    `validB_iff`), guard branch to the no-instance, the item view of sentinel
    streams (`encItems`/`expandItems` — ONE loop lemma for cards+final via a
    shared scratch output `BOUT` + copy-out), unary multiplication
    (`mulLoop_run`), truncated-subtraction compare.
  - `Reductions/FSAT_to_SAT_free.lean` + `NP/FSAT_to_SAT_pre.lean`: **the
    tree-traversal pattern** — a TREE-typed *input* consumed by one forward
    token scan of its Polish serialization: positional fresh variables, right-
    child recovery by the arity-budget scan (`subtreeScan`), and a pure scan
    model proven equal to the tree map (`mScan_eq_fsatToSat`) — the template
    for "prove the machine folds compute a pure model, then close with the
    model≡tree equivalence".
  - `Reductions/S1_to_FlatTCC_comp.lean`: **the scrub-only seam** —
    `clearRange` + one `_get` clause + a bridge quantified over the left
    program's contracts. **Start here for any new seam.**
- **The canonical `LangEncodable` layer stays DEAD** (generic product encoding
  is size-unsound — `probes/UnaryProductSizeProbe.lean`). Do not rebuild it.

### ⚠ Standing architecture risks — check every new witness against these

1. **Honesty is per-witness discipline, not enforced.** `eIn`/`encodeIn` must
   be the natural layout of the *input* (never of `gmap v`), `decodeOut` the
   inverse of the natural *output* layout, all reduction work in the `Cmd`. The
   trivial dishonest instantiation satisfies every field — and
   `probes/HonestyAuditProbe.lean` §6 *is* one, sorry-free, yielding a real
   `polyTimeComputable'`. **Every witness built so far is audited** (ROADMAP
   risk S5, verdicts 1–14); **every witness you add owes a verdict.** The audit
   is short: by FINDING AK only the composite's *leftmost* `encodeIn` and
   *rightmost* `decodeOut` matter, and by FINDING AL a seam's `mfc` needs no
   audit at all. **Both current ends are now pinned**: the *tail* by
   `Serialize cnf` (give a new output type an instance and take
   `decodeOut := Serialize.decodeD`), the *head* by `encodeIn = encX` plus the
   `NPhardStr` statement. See NEXT-TOP-DOWN item 4 for the recipe.
2. **Seam discipline**: pin each new witness's input layout to its
   predecessor's exit frame and document the exit layout (dirty registers
   included) for the successor. See "Composed-chain layouts — PINNED" above;
   changing any of them re-opens a bridge.
3. **Guard-or-no-guard is a per-step decision**: probe invalid→invalid ON
   PAPER before coding (counterexample method: pick a tiny invalid instance,
   check whether its image is accidentally wellformed+satisfiable).
4. **The front instance types are size-MEASURED, not string-encodable**:
   `GenNPInput.rel` / `mTMGenNPFixedInput.accepts` / `TMGenNPFixedInput.accepts`
   are abstract predicates, so `encodable.size` counts only the data fields.
   Honest for `⪯p` size bounds, but **no TM can consume these types as
   inputs** — C8 retires the abstract front entirely. Never add a size-0
   instance to "fix" a missing-instance error; the fallback was deleted
   deliberately.
5. **`encodable.size` must DOMINATE the register content, not merely count the
   structure.** A size that counts a container's *elements* but not their
   *payloads* is honest for `⪯p` output-size bounds yet makes `encodeIn_size`
   unsatisfiable for any witness that must spell the value out on tape — that
   is what killed `sizeFlatTM`. For every new type ask: *does some witness have
   to write this structure out cell by cell?* If yes, the size must be the
   data-field sum.
6. **The hypothesis side of hardness is dishonest-capable too — and neither
   verifier witnesses nor the `sizeLB` field close it (FINDING AN/AO/AQ).**
   `inTimePoly`/`inNP` are classically TRUE for every predicate (the cheating
   `DecidesBy.encode`), which is why hardness is quantified over free-line
   verifier witnesses. But `InNPWitnessLangFreeSplit` still lets the
   *instantiator* choose `encX`, the input layout the whole composite reduction
   is built on. §7 of that probe used to present an **arbitrary** predicate with
   the answer planted in its input and get `Q ⪯p' SAT` out of `SAT_NPhard''`;
   the 2026-08-02 `sizeLB` field killed *that* instance (§7 now proves it
   unbuildable), but **§7b still typechecks** — write the honest encoding out and
   *append* the answer, and every law about `encX` holds. No further field will
   help. **The fix is to pin the input type**: `NPhardStr` quantifies over `Q : List Bool → Prop` with the canonical
   `certState` layout — no `encX` field, nothing to choose. Quote
   `CookLevinStr`. Never "fix" a hardness obligation by strengthening only the
   conclusion side, and never reintroduce anything shaped like
   `hasDeciderClassical` (deleted 2026-07-30-c). **Since 2026-08-03 this is
   machine-checked, not argued**: `NonVacuity.searchDecide_correct` shows every
   inhabitant of `inNPStr` is decidable, so a §7b-style planted answer cannot be
   presented through `NPhardStr` at all.
7. **A `sorry` inside a `def` poisons the STATEMENT of every lemma mentioning
   it**, which blinds `#print axioms` — the project's main soundness
   instrument. **Quantify skeleton-phase results over the placeholder.** This
   is why `s1Bridge` takes the program as a parameter and why
   `SAT_NPhard''_of_S1` exists; it is the single most valuable habit in this
   codebase and it is what turns "we believe S1 is the only gap" into a
   machine-checked fact.
8. **A hypothesis you strengthen is a hypothesis you must re-inhabit
   (2026-08-03, FINDING AR).** The three previous sessions each tightened
   `InNPWitnessLangFreeSplit`/`InNPWitnessStr` to kill a dishonest
   instantiation, and none re-checked that an *honest* instantiation still
   existed — the library ended up with zero `InNPWitnessStr`, i.e. a headline
   whose hardness half was vacuously true for anything a reader could verify.
   **Every future field you add to a hypothesis structure owes, in the same
   commit, a discharged instance** (`SATStr.satStrWitness` is the one to copy —
   `NonVacuity.squareWitness` is smaller but its language is in **P**, so it
   cannot show the class still contains anything hard) — and, if it is cheap, a
   proof that the class still has computational content.
9. **What a reviewer must READ is a resource, and it is now metered
   (2026-08-06, ROADMAP risk S8).** `Complexity/StatementGate.lean` fails the
   build if a headline's statement surface changes. Before you publish a new
   statement — or restate an old one "more clearly" — run
   `#print_statement_surface` on it and look at what it costs a reader. A
   restatement that adds twenty definitions to the reading list is a *worse*
   statement even if it is prettier; one that removes some is a real
   improvement worth its own commit. ⚠ Do not try to shrink the surface by
   hiding a definition behind an `abbrev` — the closure runs through definition
   bodies (`probes/StatementSurfaceProbe.lean` §3 is the control).
10. **Every conjunct of a published statement needs its own
    dishonest-instantiation question, every time you touch any of them
    (2026-08-07, FINDING AX).** `NPcompleteStr`'s membership conjunct was
    inhabited by *every* string language for as long as it existed, because the
    three sessions that hardened the hardness conjunct each asked the question
    only of the half they were editing. The general form: a hypothesis you
    strengthen is a hypothesis you must re-inhabit (risk 8 above), and a
    **conclusion** you strengthen is a conclusion whose *other* halves you must
    re-attack. Before publishing any `A ∧ B`, try to inhabit `B` for an
    arbitrary predicate — it takes minutes and `probes/HonestyAuditProbe.lean`
    §7/§7b/§7c are three worked attempts, two of which succeeded.
    ⚠ And when a class turns out to be vacuous, **remove the free field rather
    than legislating about it**: that has now worked three times
    (`hasDeciderClassical` → `InNPWitnessLangFreeSplit`, `encX` → `NPhardStr`,
    `encX` again → `NPcompleteStr'`), and adding a law has worked zero times
    (FINDING AO).

## C8 — the honest universal front: DONE (C8-0…C8-5)

The per-`Q` front and its seam into the chain are built and the front half is
axiom-clean. Consume as black boxes; do NOT re-derive the machine, the lifting,
the program or the seam:

* `Complexity.Lang.FrontWitness.front_reducesPolyMO' : Q ⪯p' FlatSingleTMGenNP`,
  the witness `WQ`, and `FrontLifting.fQ_correct` / `fQ_correct_concrete`;
* `FrontS1Comp.frontBridge` / `front_to_SAT_seam` / `SAT_NPhard''_of_S1`.

## ★ Earlier findings that still bind

Narration lives in git history; the durable results are in "Locked invariants",
"Proven, reusable" and "Conventions". These are the *findings* a new gadget
still has to respect:

- **A conjunction is only as honest as its weakest conjunct, and "we hardened
  the hypothesis" is not a statement about the conclusion (2026-08-07,
  FINDING AX).** `NPcompleteStr P = NPhardStr P ∧ inNPLangFreeSplit P`. Three
  consecutive sessions tightened the *hardness* conjunct until it had no free
  input encoder left; none re-asked the dishonest-instantiation question of the
  *membership* conjunct, which still had one. It turned out to be inhabited by
  **every** string language (`probes/HonestyAuditProbe.lean` §7c). **When you
  tighten one side of a published `∧`, re-ask the question of the other side in
  the same session.** The fix was the same shape as the original one — remove
  the free field (`NPcompleteStr' = NPhardStr P ∧ inNPStr P`), do not add a law
  about it — and it cost three lines, because the honest witness already
  existed and the headline was throwing a field away on the way out. ★ It was
  also *cheaper to read*: 112 names against 113. Do not assume the honest
  statement is the expensive one; measure.
- **Nothing in this repository can gate a docstring — audit the prose inside
  the statement surface (2026-08-07, FINDING AY).** `Lang/Syntax.lean` and
  `Lang/Semantics.lean`, the first two files of the reading list's group 2,
  carried May-2026 skeleton headers announcing that `eval`/`cost`/`Compile`
  were "deferred" and "declared as `axiom`s" — false since Part 3.2/3.3 landed
  and contradicted by every build since the axiom gate. `#assert_statement_surface`
  measures *definitions*; a stale comment in a file it names is worth more
  damage than a stale comment anywhere else, because the reading list is
  exactly what a reviewer is instructed to trust. When you touch a file in a
  surface, read its header.
- **"Which statement is cheaper to audit" is a measurable question, and prose
  about it drifts (2026-08-06, FINDING AV).** The plan of record implied the
  `List Bool`-on-both-sides headline was the cheaper read. Measured, it is the
  *dearer* one: 113 definitions against 103, because `SATStr` is **defined by
  parsing** its input, so the well-formedness DFA and the CNF parser are part of
  what it literally says. The cheaper reading is real but goes through
  `satStr_iff`, a **theorem**. Before claiming one presentation is easier to
  check than another, run `#print_statement_surface` on both — it is seconds.
- **The statement gate and the honesty gate can never merge, and the reason is
  structural (2026-08-06, FINDING AW).** Neither headline's statement surface
  contains a reduction, a `decodeOut` or a `Serialize` instance, because
  `reducesPolyMO'` quantifies over them **existentially**. So no strengthening
  of the statement can pin the witness we chose, and no audit of the witness
  tells a reader what the theorem says. Expect someone to propose unifying the
  gates; this is why the answer is no.
- **Check a class's laws against the layout the STATEMENT already pins, before
  using the class (2026-08-05, FINDING AT).** `Serialize`'s no-compression law
  was `encodable.size x ≤ (enc x).length`, and it is unsatisfiable for
  `List Bool` under the canonical one-cell-per-bit layout — not because anything
  compresses but because the generic `List` instance's `encodable.size`
  over-counts (2 for a `true`, 1 for a `false`). The wrong fix is a two-cells-
  per-bit encoding, which would disagree with `certState` and leave a reviewer
  two serializations to reconcile. The right fix is the form the development
  already used for the same obligation elsewhere:
  `size x ≤ sizeLB |enc x|` for a polynomial `sizeLB`
  (cf. `InNPWitnessLangFreeSplit.sizeLB`). **When a law and a pinned layout
  conflict, the layout wins — the statement is the thing a reviewer reads.**
- **A seam needs the left composite's exit REGISTER, and `computes` does not
  give it (2026-08-05, FINDING AU).** `computes` says the output register
  *parses* to the output; a junk register could do that too. State the register
  fact separately (`SATStrComp.ExitsOnCNFOUT`) and **transport it along seams**
  (`exitsOnCNFOUT_comp`, one line per seam) rather than unfolding a multi-level
  composite program. This is the whole cost of extending the chain at the tail.
- **Before scoping a parser, ask what the target layout's fields actually are
  (2026-08-04, FINDING AS).** Classify each field of the layout you must produce
  as (a) the input verbatim, (b) a derived *count* or other metric, or (c)
  genuinely re-structured data. Only (c) needs a parser. This layer's encodings
  are flat `0`/`1` streams by construction (`BitState`), so (a) is usually a
  `copy` and (b) is a counter in a scan you are running anyway — which is how a
  session budgeted for an on-machine CNF parser produced an 11-op loop instead.
  ⚠ The dual trap: a derived field that is only a **loop bound** could be
  over-approximated, but a field the seam compares with `AgreeBelow` cannot —
  `CLAUSE_TALLY` is compared, so it had to be counted exactly.
- **Make the "malformed input" branch decode to a canonical REJECTING value
  (2026-08-04).** `CnfWellFormed.parseTotal` sends every non-encoding to `[[]]`,
  which is unsatisfiable, so "this string is not an encoding" and "this string
  encodes an unsatisfiable formula" are the *same verdict* and one verifier
  decides both — the malformed branch is four ops, not a second mechanism. The
  honesty obligation this creates is one theorem: prove the junk value really is
  outside the language (`not_sat_botCnf`), or the branch is a silent accept.
- **When you characterise an encoder's image by a finite automaton, the state
  you will forget is "a suffix is still open" (2026-08-04).** The obvious
  three-state CNF scanner accepts `[1,1,0]` — a literal run with no clause
  terminator, which no `encodeCnf N` ever is. Probe the *shortest* bad word
  before proving anything; `probes/SATStrProbe.lean` §2 finds it at length 3.
  And prove the `⇒` direction with the "rest of a clause" statement
  *simultaneously*: the accepting and non-accepting slot states have identical
  transitions, so one strong induction serves both halves.
- `preludeBlocks` is ~96% of the card register, so the prelude is stage C's
  cost driver; `cFive`'s five families all emit IDENTITY cards and `stepBlocks`
  does **not** — `S1Step.emitCard`/`card6_run` (six pairs of registers) is the
  atom for any future non-identity card family.
- `Cmd.op (.copy r r)` is the layer's no-op (`S1CardEmit.copy_self_get`);
  `forBnd` samples its bound register's length ONCE at entry; `ifBit` reads its
  test register *before* entering the branch (which is why `CDirty` includes
  `FLG = 17`).
- `xv` is rebuilt per iteration while `hv` is carried — ask which shape a new
  value register is.
- Stages P/G/F take **no** validity hypothesis (the parse never desynchronises;
  a drained-empty `head` reads *false*, exactly `M.halt.getD` out of range) —
  but **the guard is load-bearing** for stage I (`probes/S1EmitProbe.lean`
  exhibits an off-guard instance where stage I and `preludeRow` disagree).
- `PHALT` (reg 11) is a RAW BIT LIST; registers `15`/`16`/`22`/`26` are
  RESERVED for `CliqueRelTM.readNum`/`ltBit`.
- Both S1 size bounds are `≤ (2·(b+1))^10` and the **enlarged base is not
  optional**: a `C·b^d` collapse overshoots a tight `n^10` at small `n`, and
  guess's base includes `maxSize`.
- The S1 v2 redesign's two machine-checked defects — non-local zero-padding
  jump-writes and the **phantom head** at the right row edge — are why the tape
  is append-only at the frontier and why `confRow` carries a right boundary
  marker. Both are locked invariants below.
- **`FrontWitness.exists_front_constants` is the shape to reuse if you ever need
  to move a budget between measures**: `inOPoly_monomial_bound` applied twice —
  once to `maxSizeOf`/`stepsOf` (monomials in `encodable.size x`), then to that
  monomial composed with `sizeLB`. `inOPoly_comp` needs no monotonicity of the
  outer function, and the intermediate monomial *is* monotone, which is what
  lets `encX_sizeLB` be applied inside it.

---

## Locked invariants — do NOT revisit

- **Frame facts belong in the write-set lemma, NOT in the loop invariant
  (2026-07-30-b, FINDING AH).** A loop invariant conjunct must be re-established
  in *every* branch of the body; `Cmd.eval_get_of_not_writes` is syntactic, costs
  one line per register and runs once, at the end. `EvalCnfSplit.decodeBody_run`
  carries only the two registers the loop actually changes. Probe the frame
  per-iteration if you like (`SATSplitProbe` §5 does) — do not *prove* it there.
- **Write a loop's invariant as a `Bool` function and `#eval` it at EVERY index
  before proving anything (2026-07-30-b, FINDING AI).** `SATSplitProbe` §5 fixed
  the `c.take i` / `c.drop i` split, the trip count and the postcondition before
  a line of proof existed, and the proof consumed it verbatim — zero redesign,
  ~110 lines for an 11-op program. This is the cheapest de-risking move in the
  codebase; it is what "probe before committing engineering" means for a `_run`
  lemma.
- **`Cmd.PolyCost` is DELETED and must not come back (2026-07-30-b, FINDING
  AJ).** One cap cannot survive a `forBnd` (FINDING Z below); `Cmd.CapCost`
  strictly subsumes it. The two facts worth keeping — `Cmd.get_length_eval_le`
  (per-register growth ≤ cost) and `Cmd.forBnd_counter_le` — now live in
  `Lang/CostFlat.lean`. `probes/CostChkIntentProbe.lean` pins what `Cmd.chk`
  must accept and reject.

- **A free precomposition may CHOOSE the composite's `encodeIn` — so a layout
  mismatch with the target verifier's own `encodeIn` is not a layout problem
  (2026-07-30, FINDING AD).** `DecidesLang.precomposeFree` sets the new decider's
  `encodeIn := FreePrecomposeData.eIn`, and `State.get` reads an unset register as
  `[]`. `EvalCnfSplit.satEIn` is therefore a FOUR-register literal that agrees
  with the twelve-register `EvalCnfCmd.encodeState` everywhere the verifier looks.
  Do not "trim" trailing scratch registers, and do not read a `≠`-of-lists as a
  layout obstruction: check `AgreeBelow regBound` instead.
- **A re-encoder whose scratch sits ABOVE the target verifier's `regBound` owes no
  scrub (2026-07-30, FINDING AE).** `AgreeBelow D.regBound` does not look above
  the frame, so `Cmd.eval_get_of_not_writes` (`Lang/CostFlat.lean`) closes every
  untouched register below it in one line and the bridge collapses to the
  registers the re-encoder actually rewrites. `certDecode` uses `16`–`18` against
  `evalCnfDecidesLang.regBound = 16` for exactly this reason. Prefer this to a
  scrub whenever the composite's `regBound` may simply be widened.
- **A certificate relation over `List Bool` must be TOTAL, and the
  characteristic vector is the only shape that is total for free (2026-07-30,
  FINDING AG).** `InNPWitnessLangFreeSplit` puts the certificate in `certState`
  (one register of `0`/`1` cells), so *every* bit string is in the image and the
  relation must be defined for all of them. `decodeBits` (indices where `c` is
  `true`) is total, is a one-pass machine emitter whose `forBnd` counter is the
  variable index in unary, and needs no `maxVar`: `varsOfCnf_lt_size` makes
  `List.range (encodable.size N)` a uniform certificate length. A sentinel-unary
  certificate format needs a partial parse plus a normaliser for malformed
  blocks — do not go back to it.

- **A cost predicate with ONE cap cannot survive a loop (2026-07-29,
  FINDING Z).** `Cmd.PolyCost`'s single `M` over `costReads` re-caps the body's
  outputs at `poly(M)` each iteration, so `m` iterations give a tower; that is
  why `Cmd.polyCost_forBnd` has to forbid the body from writing what it
  cost-reads. `Cmd.CapCost` splits the cap into a frozen `MF` and a global `N`,
  lets the **cost** be linear in `N` and forbids the **growth** from depending
  on it. Do not "simplify" it back to one cap.
- **A loop's frozen set may contain WRITTEN registers only via `NoGrow`
  (2026-07-29 / -b).** Promotion buys a register's cap with a *growth constant*
  `G`, so a frozen set that already contains promoted registers would need `G`
  computed at a cap that depends on `G` — circular, which is why iterating
  promotion to a fixpoint does not work and why the deleted `Cmd.GrowOk`
  required its frozen set to be unwritten. The escape is `Cmd.NoGrow`, whose
  bound `≤ max |r| 1` is **idempotent**: no trip count, no growth constant, so
  it stratifies for free. `Cmd.chk`'s `Fz = {cnt} ∪ (C \ ngm body)` is exactly
  that, and one flow-sensitive pass over it reaches `SSEEN` — the four rounds
  the old design would have needed are not required and would not have been
  sound.
- **A rejected sub-command must not blind the analysis (2026-07-29-b,
  FINDING AC).** `Cmd.chk C c = (ok, C', B)`: `C'` and `B` are sound **whether
  or not `ok` holds**, because an enclosing loop's promotion is read from `B`
  and is what makes the rejected sub-command acceptable on the second pass.
  Measured: degrade them and `S1CardEmit`'s `CH` loop and both `scanSeen` loops
  come back.
- **Register sets in the cost checker are `Nat` BITMASKS, and the kernel's wall
  is MEMORY (2026-07-29-b, FINDINGS AA/AB).** `Cmd.writes` of
  `S1Prelude.cPrelude` is a 327411-element list; the `List Var` checker was
  quadratic in program size and never terminated. `Nat.ldiff` is **unusable** —
  it goes through `Nat.bitwise`, which the kernel cannot reduce, so `decide`
  gets stuck; use `mdiff a b := a ^^^ (a &&& b)`. And a
  two-traversals-per-loop analysis was **OOM-killed at 15 GB** on `cPrelude`
  alone, so `Cmd.chk` visits each body once and pays for a second pass only
  where the first is rejected. Re-measure **memory** before making the analysis
  more precise.
- **A `cost_bound` field must be an EXISTENTIAL polynomial, not a fixed one
  (2026-07-28-c, FINDING Y).** `S1Witness.S1CostBound c` = "some `cb` is
  `inOPoly`, `monotonic`, and dominates both `c.cost (headEncodeIn x)` and
  `size (s1Map x)`". The old `c.cost ≤ S1Map.s1Bound` (degree 10, fixed) could
  not consume any generic cost lemma, whose output is always `∃ K D, K·(M+1)^D`.
  `output_size_le` is the *only* real constraint on `cost_bound`, which is why
  bundling the two obligations makes the bound free. Do not re-specialise it.
- **`Cmd.op (.copy r r)` is a semantic no-op but costs `|r| + 1`, and that cost
  is now FREE (2026-07-28-c FINDING X, resolved 2026-07-29).** It is the `ifBit`
  else-branch with `r := EOUT_C` in `S1CardEmit`, `S1Prelude`, `S1PreludeEmit`
  (and with `r := ASSGN` in `EvalCnfSplit.decodeBody`), so the emitters are
  `O(output²)` and `EOUT_C` is a genuine `Cmd.costReads` member — but
  `Cmd.CapCost`'s `(N+1)` factor pays for it. **Do not swap the no-op**: the
  pinned `_run` lemmas depend on that exact else-branch and there is no longer
  any cost reason to touch it.
- **No unconditional polynomial cost bound exists for `Cmd`
  (2026-07-28-c).** `forBnd cnt bnd (concat dst dst dst)` squares `dst` every
  iteration. Every cost lemma therefore carries a side condition; `CostSafe`'s
  is "no loop body writes a register its own cost reads". Relax it, never drop
  it — and remember the loop *bound* register is sampled once at entry, so it
  may be written by the body without harm, but an inner loop bounded by a
  register the outer body rebuilds is exactly where compounding sneaks back in.

- **A cursor loop's body must be TOTAL (2026-07-28-b, FINDING T).**
  `S1Step.emitFold_run`'s `hstep` is quantified over every iteration index, so
  the body has to emit `[]` and preserve the carried state on an exhausted
  cursor. Guard every cursor loop's body with one `nonEmpty` on its own cursor
  (`S1Step.entryBody`, `scanBody`); a guarded loop then only needs an **upper**
  bound on its iteration count (FINDING V — `Cmd.forBnd EK1 SSEEN scanBody` is
  legitimate because `|encSyms (keyFlat seen)| ≥ |seen|`). Do not spend a
  register on an exact loop count.
- **A machine-side accumulator must match its model's cons order
  (2026-07-28-b, FINDING U).** `S1Step.stepSt` conses, so the seen register is
  built by `Cmd.op (.concat SSEEN item SSEEN)` — `concat dst a b` writes
  `get a ++ get b`, so prepending is free and keeps the invariant a literal
  `encSyms (keyFlat seen)`.
- **A contract pinned for an unwritten `Cmd` must list the inputs of every
  model it will consume (2026-07-28-b, FINDING W).** `stageC_run` was pinned
  without `PSTART` and nothing noticed for three sessions, because no *built*
  consumer needed it yet — `S1Cards.preludeBlocks` is indexed by
  `min M.start M.states`. The fix was free here; it will not always be.
- **Stage C's `Cmd` is COMPLETE and its 30-register licence is EXACTLY full
  (2026-07-28-b).** `S1Program.stageC = cFive ;; S1Step.stepFam ;;
  S1Prelude.cPrelude`, emission order is `S1Cards.cardBlocks`' order, and
  `probes/S1StepLoopProbe.lean` §1 checks the full equality (not a prefix).
  Changing any register in the stage-C table re-opens `stepFam_run`,
  `cPrelude_run` and `stageC_run`.

- **A data-driven loop needs a STATEFUL loop principle (2026-07-28, FINDING R).**
  `S1CardEmit.emitLoop_run` pins the body's output to the iteration index and is
  correct only for *index-driven* loops (the five copy/halt families, the whole
  prelude nest). A loop whose output depends on registers inside its own dirty
  set — a cursor, an accumulator — must go through **`S1Step.emitFold_run`**
  (`Cmd.foldlState_range_induct` + an invariant carrying an abstract state).
  Do not try to force a cursor loop into `emitLoop_run`.
- **Parameterise a family gadget by its innermost BODY, not by its branch
  condition (2026-07-28, FINDING Q).** `stepBlocks` branches three ways on `mv`
  and has four sub-families; because the four *loop nests* are `mv`-independent,
  taking the card `Cmd` as a parameter turned 12 emitters into 4 loop lemmas +
  11 card definitions. `S1Prelude.pKindCmd` and `S1CardEmit.haltFam` are the
  same move.
- **The `stepBlocks` entry body is BUILT; its contract `SConst`/`SEntry`/`SD1`
  is PINNED (2026-07-28).** Changing any register in the table above re-opens
  `stepEmit_run` and all four family `_run`s. The entry loop must meet
  `S1Step.stepSummand_fold`; the dedup's seen-set is appended to
  **unconditionally** (FINDING S, `dedupK_congr`).
- **The prelude family is BUILT; its emission order and register table are
  PINNED (2026-07-27-b/-c).** `S1Prelude.preludeSeg`/`preludeSeg'` fix the
  nesting (kind loops outside resolution loops — finding A) and `cPrelude` is
  the emitter. Changing either re-opens `preludeBlocks_seg`,
  `preludeBlocks_seg'`, `pPre_run`, `cPrelude_run` and `S1Program.cFive_frame`.
- **Stage C needs NO unary comparison gadget — BOTH families (2026-07-27-b/-c).**
  The seven-segment split (`S1Prelude.range_seg`) makes every prelude kind's
  shape a compile-time constant; `S1Step.range_last`/`range_first_last` do the
  same for `stepBlocks`' three last-iteration tests; `S1Prelude.minReg` does
  every `min` by draining and `S1CardEmit.loadX` does every "is the counter
  zero?" with `nonEmpty`. Do not build a `<`/`=`-on-unary gadget for stage C.
- **A register may not be shared by two writers separated by a loop
  (2026-07-27-c, FINDING G).** The pinned table gave `PJᵢ` to both the kind
  level and the resolution level; because the resolution nest runs inside the
  kind levels, the kind level's value never survived to the emit body. Fold the
  extra value into an existing register (`PPAᵢ := 1^pav`) instead of making the
  frame conditional. Applies to every future multi-level emitter.
- **A deep register-generic nest needs NESTED dirty lists (2026-07-27-c,
  FINDING H).** `DK3 ⊆ DK2 ⊆ DK1` and `DR3 ⊆ DR2 ⊆ DR1`: level `i`'s frame must
  not claim level `i-1`'s registers, because the innermost body reads them. One
  global dirty list does not work. `S1Prelude.Emits.mono` is the bridge.
- **The chain composes RIGHT-NESTED: `W_Q ⨾ (S1 ⨾ tail)` (2026-07-27).**
  `S1SATComp.s1_to_SAT_witness` first, `FrontS1Comp.front_to_SAT_witness` on
  top. Re-associating turns C8-5 into a stacked seam over a composite left
  witness and re-opens `frontBridge`.
- **The two new scrub ranges are PINNED to the frames they were derived from
  (2026-07-27).** `S1SATComp.scrub4` erases `{0} ∪ [6, s1RegBound)`;
  `FrontS1Comp.headScrub` erases `[headRegBound, 57)`. `probes/SeamS1Probe.lean`
  §1 asserts both erase sets exactly. Changing `s1RegBound`, `headRegBound` or
  the tail composite's `57` means changing a scrub and re-running that probe.
- **The S1 witness is built in TWO steps and stays that way (2026-07-27).**
  `S1Witness.s1WitnessOf` takes the program + its three contracts;
  `s1_reductionLang` is the instantiation. Both seams, both composites and
  `SAT_NPhard''_of_S1` are stated over the parameterised form, which is what
  keeps them axiom-clean while stage C is a placeholder. Inlining
  `s1WitnessOf` would silently destroy that (standing risk #7).
- **The S1 program's SHAPE and `stageC_run` are PINNED (2026-07-26-b/-c,
  `Reductions/S1Program.lean`)**: `s1Program = stagePG ;; ifBit FLG yesBranch
  stageMNo`, `yesBranch = Σ ;; I ;; C ;; F ;; M-yes`, and `stageC_run` states
  exactly what the assembly consumes. `s1Program_computes` is already the
  witness's `computes` field. Changing the stage order, the contract, or the
  `EScratch`/`CDirty` licences re-opens `yesBranch_run` and hence `computes`.
- **The S1 register frame is PINNED across three files** — see "The S1 register
  frame — PINNED" above for the single authoritative table (`S1Parse` `0`–`31`,
  `S1Emit` `32`–`47`, `S1CardEmit`'s constants inside `[14,32)`,
  `s1RegBound = 48`; registers `15`, `16`, `22`, `26` RESERVED for
  `CliqueRelTM.readNum`/`ltBit`). Changing any of it re-opens `stagePG_usesBelow`,
  `stagePG_frame`, all four emitter `_run`s and every `usesBelow`.
- **Stage C emits in `cardBlocks` ORDER (2026-07-26-c).** `S1CardEmit.cFive` is
  the first five summands and `probes/S1CardEmitProbe.lean` §1 asserts its
  output is a genuine PREFIX of `encNats (cardBlocks M)`. The remaining two
  families append after it, `stepBlocks` then `preludeBlocks` — build order is
  free, emission order is not.
- **The emitter's dirty sets are register LISTS (2026-07-26-c).**
  `S1CardEmit.HD`/`ID`/`AD` with `r ∉ D` (`by decide`), plus `nmem_sub` /
  `ne_of_nmem` to move between levels and down to a per-gadget `≠`. An 11-`≠`
  frame chain is a smell; `S1Program.cFive_frame` is what proves a list-shaped
  dirty set fits the coarse `CDirty` predicate.
- **`s1Key`/`s1Extract`/`SIGMA`…`STEPS`/`s1RegBound` live in `S1Program`, not
  `S1Witness` (2026-07-26-b).** The witness imports the program. Do not move
  them back or duplicate them.
- **A skeleton-phase lemma must quantify over the placeholder it does not depend
  on (2026-07-26-b).** A `sorry` inside a `def` puts `sorryAx` in the axiom list
  of *every* lemma whose statement mentions it, proof or no proof — which blinds
  `#print axioms`, the project's main soundness instrument. `noBranch_computes`
  takes `(yes : Cmd)` and is axiom-clean; `s1Program_computes_neg` is its
  corollary and is not. State the general form first, specialise second.
- **Every size bound over an encoding with a fixed-size header needs an ADDITIVE
  term (2026-07-26).** `size (flattenTM M) ≤ 3·size M` was stated as having
  "slack" and is false at the trivial machine (`size M = 1`, six header cells).
  The correct shape is `c·size M + d`; `d = 3` here and is tight. Probe the
  empty/zero instance of every new size claim — a probe over "realistic"
  instances will print `true` and hide it (`probes/S1SizeGapProbe.lean` §3).
- **Stage C's target is `S1Cards.cardBlocks` (2026-07-25-c)** — the seven
  `List.range` streams, in that order, `emb`-free. Changing the model re-opens
  ten proven equations; extend it only by adding a family at the end (and
  re-run `probes/S1CardModelProbe.lean`).
- **The output register is built by unit-cost APPENDS, never `concat`
  (2026-07-25-c).** `Op.cost (concat dst a b) = 2(|a|+|b|)+1` reads the whole
  destination, so one `concat`-per-card would be quadratic in the emitter's own
  output. Same rule for every future large-output emitter.
- **`cost_bound` is a free polynomial, but it also carries `output_size_le`
  (2026-07-25-c).** `PolyTimeComputableLang.output_size_le` is stated against
  `cost_bound`, so any raise must keep dominating `S1Map.s1Map_size_le`; that
  is the only constraint. Never re-engineer a program to meet a self-imposed
  degree.
- **`encodable FlatTM` is the DATA-FIELD SUM (2026-07-25):**
  `sig + tapes + states + start + size halt + size trans + 1`, next to the
  instance in `Definitions.lean`. The old `sizeFlatTM` (flat `5` per
  transition entry) is deleted; never reintroduce a "roughly / approximate"
  size measure. This is what makes the S1 witness's `encodeIn_size`
  satisfiable at all (`probes/S1SizeGapProbe.lean`).
- **The S1 witness's OUTPUT layout is `FlatTCCFree.encodeIn` verbatim on
  registers 1–5 (2026-07-25, `S1Program.s1Key`)** — the sound-tail composite's
  `encodeIn` *is* `FlatTCCFree.encodeIn` (`rfl`), which is what makes the
  fourth seam a pure scrub of reg `0` and `[6, 57)`. Changing `s1Key` now
  re-opens the seam **and** `yesBranch_run`/`computes`.
- **The flat tape is APPEND-ONLY AT THE FRONTIER (2026-07-17-b):**
  `writeCurrentTapeSymbol` replaces in range, appends exactly at
  `head = right.length`, and is a NO-OP strictly beyond. Never reintroduce
  the zero-padding jump-write — it is non-local (one step rewriting cells
  arbitrarily far from the head) and falsifies every local-window tableau
  simulation (S1). New machines must not rely on writing past the frontier.
- **S1 rows carry a RIGHT boundary marker (2026-07-18-c)** — `confRow` ends
  with `bCell`, guarded by the cell-preserving `copyRightCards` family, and
  the step lemmas demand `cfgHead + 4 ≤ n` head-room. Never drop the
  marker, add another family with the marker in slot 3, or add ANY
  head-at-second-slot family: each reopens the machine-checked phantom-head
  completeness hole (`probes/S1TableauProbe.lean` §5).
- **`BitState` / `sig = 4` / numbers UNARY (Option B′).** Fixed 4-symbol
  alphabet; `encodeTape` shifts cells `+1` (`0→1`,`1→2`), `0` separates
  registers, `3` terminates/anchors. Every tape-touching state must be
  `Compile.BitState` (cells `∈ {0,1}`). Numbers unary (`enc n = replicate n 1`).
- **Runtime tape-padding resolves the register-count WALL.** `Compile.padRegsTM
  k` grows the tape during the run; `paddedBitDecider_run`/`paddedCompute_run`
  are proven with **no `k ≤ s.length`**.
- **`physStepBudget G cost = (9G²+9G+33)·(8·cost+8) + cost`** is the only
  composable budget shape. Never an `overhead`/`(·+1)²` shape.
- **`DecidesBy.encode_size` is per-decider POLYNOMIAL** (`encodeBound`).
- **Per-op contract takes a threaded scratch base `sb`**; eqBit-style ops use
  pre-existing interior scratch at `sb`/`sb+1`.
- **`Op.cost eqBit = |src1|+|src2|+1`**, **`Op.cost concat =
  2(|src1|+|src2|)+1`** (size-aware costs).
- **`NPhard'` endpoint-only; chains compose via `SeamData`/`comp`** (settled
  2026-07-02, VALIDATED LIVE 2026-07-03). No generic `⪯p'`-transitivity — do
  not attempt one.
- **No size-0 `encodable` fallback** (Part 0.1, 2026-07-04-b): the default
  instance is deleted; a missing `encodable.size` is a compile error by
  design. Give every new type a real data-field-sum size next to its
  definition.

## Proven, reusable — do NOT re-derive (index by file)

Everything below is **sorry-free and axiom-clean**. Consume it as a black box.
Re-deriving any of it costs a session and gains nothing; the whole point of this
index is that you can find the file, open it, and read its own doc comment —
each file states its endpoints at the top.

⚠ The exhaustive per-lemma catalogue that used to live here (~620 lines, every
endpoint named) was compressed on 2026-08-03 to keep this document a *plan*.
It is in git history: `git show 25323e1:CookLevin/HANDOFF.md`. Go there if you
need to know whether a specific lemma already exists before writing it — and
prefer `rg` over both.

### The statement, the gates, and non-vacuity

| file | what it gives you |
|---|---|
| `Lang/PolyTime.lean` | the whole free line: `DecidesLang`, `PolyTimeComputableLang`, `⪯p'`, `InNPWitnessLangFreeSplit`, `NPhard''`, `SeamData`/`comp`, `FreePrecomposeData`/`precomposeFree`, `toFrameworkWitness'`. **Read this one.** |
| `Lang/HardnessStr.lean` | `InNPWitnessStr` / `inNPStr` / `NPhardStr` / `NPcompleteStr` / **`NPcompleteStr'`** (the strict form — `NPhardStr P ∧ inNPStr P`, canonical layout on BOTH sides; FINDING AX, 2026-08-07) and `NPcompleteStr'_to_NPcompleteStr`, the two bridges from `NPhard''`, and the canonical-layout size sandwich (`State.size_certState`, `size_le_two_mul_length`, `length_le_size`, `canonical_sizeLB`). **Read this one too.** |
| `Complexity/NonVacuity.lean` | non-vacuity, both directions (2026-08-03, upgraded 2026-08-04 §6 with `inNPStr_SATStr` / `satStr_reducesPolyMO'_SAT`): `bitStringsUpTo` + `mem_bitStringsUpTo` + `bitStringsUpTo_length`; `searchDecide`/`searchDecide_correct`/`searchDecide_calls`; the `SquareStr` inhabitant (`squareCmd`, `squareVerifier`, `squareCertRel`, `squareWitness`, `inNPStr_squareStr`) and `squareStr_reducesPolyMO'_SAT`. |
| `Meta/AxiomGate.lean`, `SoundnessGate.lean`, `HonestyGate.lean`, `CostFaithfulness.lean`, `NonVacuity.lean` | five of the eight build-time gates. Add to them; never delete an assertion to make a build pass. |
| `Meta/StatementSurface.lean` + `StatementGate.lean` | the sixth gate (2026-08-06): `#assert_statement_surface` / `#print_statement_surface`, and the three exact lists — **112** definitions behind `SATStr_NPcompleteStr'`, 103 behind `CookLevinStr`, 113 behind `SATStr_NPcompleteStr`, grouped in reading order. **This is the file to hand a reviewer first.** Since 2026-08-08 `StatementSurface.lean` also carries the **delta** form (`#assert_statement_surface_delta thm beyond base => …`, exact in both directions, plus `#print_statement_surface_delta`) and the two **shape** forms (`_contains` / `_omits` — deliberately weaker, for structural claims about a statement; `_omits` consults the **raw** closure so a generated companion cannot satisfy an absence claim). Negative controls: `probes/StatementSurfaceProbe.lean` §§1–5 for the exact form, §§6–9 for the new three. |
| `GateSurfaceGate.lean` | the eighth gate (2026-08-08): the instruments themselves, metered. §1 is **FINDING AZ** — `squareStr_reducesPolyMO'_SATStr` and `satStr_membership_is_machine_time` (the membership conjunct with the cost model discharged, one line via `DecidesLang.toInTimePoly`) plus the four `_contains`/`_omits` pins proving the two conjuncts rest on disjoint vocabularies. §2 is the exact deltas of the reading gates (0/0/0/0, 10, 1, 0, 1, 7). §3 is **FINDING BA** — the two construction gates, reclassified, plus `deciderBridge_machine`/`deciderBridge_states`, the `rfl` linkage from `CostFaithfulness.lean`'s machine to the one `toDecidesBy` actually builds. **Any new gate owes a block here.** |
| `StatementMeaning.lean` | the seventh gate (2026-08-07): the checkable half of the S8 audit of that reading list — `hardness_spelled_out` (the headline restated in ordinary language and **proved from itself**; hand a reviewer this one *second*), plus the pins behind ROADMAP S8 verdicts 2, 3, 9, 11, 12 and 13. Extend it whenever an S8 verdict turns out to be `decide`-able. |
| `Lang/Serialize.lean` + `Deciders/CnfSerialize.lean` + `Lang/SerializeStr.lean` | the chain-end serialization discipline and its **two** live instances: `Serialize cnf` (fuel-based parser for a real grammar, `dec_enc`, both size laws) and `Serialize (List Bool)` (cell-wise; `enc = strBits`, i.e. the canonical head layout's own function, plus `boolsOf`/`strBits_boolsOf` for going the other way). A new chain end owes an **instance**, not a hand-written inverse. ⚠ FINDING AT is in `Serialize.lean`'s header. |
| `Reductions/SAT_to_SATStr_free.lean` + `SAT_to_SATStr_comp.lean` | **`NPcompleteStr SATStr`** and the template for any future tail extension: `satToStr`/`strBits_satToStr`/`satStr_satToStr`, the one-register witness, and the reusable `ExitsOnCNFOUT`/`exitsOnCNFOUT_comp`/`comp_exit`/`lt_comp_regBound` (currently leaf-local by convention — move to `PolyTime.lean` on the third consumer). |

### The layer, the compiler and the cost ladder

| file | what it gives you |
|---|---|
| `Lang/Syntax.lean`, `Lang/Semantics.lean` | `Op`/`Cmd`/`State`, `eval`/`cost`, `Cmd.decides`, the compositional laws (`eval_seq`, `cost_seq`, `eval_ifBit_*`, `cost_ifBit_*`). |
| `Lang/Compile*.lean` | the one-time compiler to `FlatTM`. **All 9 ops proven, no side conditions.** Do not restore unit cost, do not tighten the residue contract, do not rebuild the canonical `LangEncodable` layer. |
| `Lang/CostFlat.lean` | `cost_le_flat`, `cost_forBnd_flat_le`, `cost_mulLoop_le`, `cost_constLoop_le`, `cost_tailLoop_le`, `Cmd.writes`, **`Cmd.eval_get_of_not_writes`** (the one-line frame closer), `Cmd.costReads`, `Cmd.get_length_eval_le`, `Cmd.forBnd_counter_le`. **The tool for a non-polynomial cost bound.** |
| `Lang/CostGrow.lean` | **START HERE for every polynomial `cost_le` obligation.** Usually one line: `Cmd.costLeSize_of_chk c (2^k - 1) (by decide)`. `Cmd.CapCost`, `Cmd.NoGrow`/`ngm`, `Cmd.loopStep`, the decidable pass `Cmd.chk`/`chk_sound`. |
| `Lang/Frame.lean` | `Op.UsesBelow`/`Cmd.UsesBelow` + monotonicity, the behavioural `forBnd` toolkit, `Cmd.foldlState_range_induct`. |

### The chain, front to back

| file | what it gives you |
|---|---|
| `Simulators/CookTableau.lean` + `GuessTableau.lean` | the S1 tableau mathematics: the bijection `cookTableau_correct`, the cert-guess layer `guessTableau_correct`, both size bounds (`≤ (2·(n+1))^10`), and the project-wide `encodable.size` toolkit (`encodable_size_list_le`, `length_flatMap_le`, `pow_collapse`). |
| `Reductions/S1Map.lean` | the S1 reduction map, its guard `s1GuardB`, the branch equations `s1Map_pos`/`s1Map_neg` (⚠ the `match` does **not** reduce under `unfold` — always go through these), `s1Map_correct`, `s1Map_size_le`. |
| `Reductions/S1Parse.lean` · `S1Emit.lean` · `S1Cards.lean` · `S1CardEmit.lean` · `S1StepModel.lean` · `S1StepEmit.lean` · `S1StepLoop.lean` · `S1Prelude.lean` · `S1PreludeEmit.lean` | the S1 program, stage by stage. Register frame pinned below. Reusable loop principles: **`S1CardEmit.emitLoop_run`** (index-driven) and **`S1Step.emitFold_run`** (stateful/cursor-driven — the one you want for anything carrying an accumulator). |
| `Reductions/S1Program.lean` · `S1Witness.lean` | the assembly (`s1Program`, `stageC`, `s1Program_computes`/`_usesBelow`), the output-key layout `s1Key`/`s1RegBound`, the frame predicates `EScratch`/`CDirty`, and the parameterised witness `s1WitnessOf`. Nothing is open. |
| `Reductions/HeadLayout.lean` · `FrontPieces.lean` · `FrontMachine.lean` · `FrontLifting.lean` · `FrontProgram.lean` · `FrontWitness.lean` | C8, the honest universal front. Endpoints: `FrontWitness.front_reducesPolyMO' : Q ⪯p' FlatSingleTMGenNP`, `FrontLifting.fQ_correct(_concrete)`, and the register/tally gadgets (`tallyCells`, `emitRegs`, `unaryMonomial`, `powLoop`). Also **`inOPoly_monomial_bound`** — the constant extractor, reusable anywhere. |
| `Reductions/FlatTCC_to_FlatCC_free.lean` · `FlatCC_to_BinaryCC_free.lean` · `BinaryCC_to_FSAT_free*.lean` · `FSAT_to_SAT_free*.lean` | the sound tail as four free-line witnesses. **Templates — copy these, not first principles**: the unguarded-map pattern, the **guarded**-map pattern (on-machine validity flag), the Tseytin/tableau step, and the tree-traversal pattern (a TREE-typed input consumed by one forward token scan of its Polish serialization). |
| `Reductions/*_comp.lean` (five files) | the five live seams. **`S1_to_FlatTCC_comp.lean` is the scrub-only seam — start there for any new seam.** `clearRange` lives there. |
| `Deciders/EvalCnfCmd.lean` · `EvalCnfSplit.lean` · `CliqueRelTM.lean` | the two verifiers and the SAT membership half. **`EvalCnfSplit.lean` is the worked template for any future `InNPWitnessLangFreeSplit`, end to end.** |
| `Deciders/CnfWellFormed.lean` · `Deciders/SATStr.lean` | **SAT as a string language, and the template for any other one** (2026-08-04). `CnfWellFormed`: the four-state scanner `scanStep`, `wfCnfB_iff` (accepts exactly the image of `encodeCnf`, both directions), `cnfCount_eq_length`, and the total decode `parseTotal`. `SATStr`: `satStr_iff` (what the language *is*), the 11-op `scanBody` + `scanBody_run` + `scanLoop_run`, `satStrBuild_get`/`satStrBuild_bridge`, the `FreePrecomposeData`, and the complete `InNPWitnessStr`. **This is the worked template for any future `InNPWitnessStr`** — copy it before writing a string language from scratch. |
| `NP/kSAT_to_SAT_free.lean` | re-encoder + reduction sharing one program, fold invariants, tight `encodeIn_size`, `FreePrecomposeData` — the smallest complete free-line example in the repo. |


## Conventions & hard-won gotchas

- **⚠ A `def f : A × B × … → C | (a, b, …) => body` does NOT reduce under
  `unfold f` (2026-07-25).** After `obtain ⟨M, s, …⟩ := x` the goal still shows
  `match (M, s, …) with | (M, s, …) => body`, and `rw [if_pos …]` into `body`
  fails with "did not find an occurrence". Fix: prove the branch equations once
  (`show (if cond then A else B) = _ ; simp [h]` — the `show` IS the defeq step)
  and rewrite with those (`s1Map_pos`/`s1Map_neg` are the model).
- **⚠ `simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]` is
  recursive and eats the WHOLE `&&`-chain, including under `∀ x ∈ l` binders
  (2026-07-25).** So a follow-up `simp only [same set]` on a sub-goal makes no
  progress (a hard error), and any lemma stated about an *unsplit* inner
  `l.all f = true` will never match. Two safe shapes: (a) state per-level
  reflection lemmas (`optAll_iff` for the leaves, `entryB_iff` for the entry
  chain) and `simp only [Bool.and_eq_true, decide_eq_true_eq, <leaf iff>]`
  WITHOUT `List.all_eq_true`; (b) at the top level use explicit `rw` for the
  outer splits (`rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
  decide_eq_true_eq, List.all_eq_true]`) — a `decide`/`all` sitting as a *Bool
  subterm* of `&&` is not of the form `decide p = true`, so those lemmas cannot
  fire inside the chain. Close the leftover associativity with `tauto`.
- **`Function.Injective f` unfolds with STRICT-implicit binders** — after
  `intro cs; induction cs`, apply the IH as `ih h` (never `ih _ h`, which tries
  to fill the strict implicit explicitly and reports "function expected").
- **⚠ Polynomial size bounds — degree/base discipline (2026-07-24-c).**
  (a) **`ring`/`omega` whnf-TIMES-OUT on `b^k` when `b` is a `set`-let of a
  many-term sum** — the power expands to `C(terms+k-1,k)` monomials (fine at
  `b^6`, dead at `b^8`). `clear_value b` right after `set b := … with hb`; the
  `hb` equation survives and `omega` still uses it for the linear facts, while
  `ring`/`omega` treat `b` as an opaque atom. (b) **A `C·b^d` collapse
  (`d`≤top) OVERSHOOTS `n^d_top` at small `n`** — `102·(n+1)^6 > (n+1)^10`… no,
  `> n^10` at `n=2`; the pure-power upper bound inflates the small-`n` value
  past a tight target. State size bounds at **`(2·(base))^10`** (`= 1024·base^10`)
  so the `2^10` slack absorbs any `C ≤ 1024`, `d ≤ 10` loose bound; still
  `inOPoly`/`monotonic`. (c) For the FINAL `omega` combining `Sg + Σᵢ size(…) ≤
  C·b^d`, **`generalize b^d = P` and each big `encodable.size(…)` atom to a fresh
  var first** — otherwise `omega` tangles the partial power relations (`b`,`b²`,`b^d`)
  and `hb`, and whnf-chokes on the `encodable.size` giants. (d) `length_flatMap_le`
  needs its fiber-bound `c` passed EXPLICITLY (`(… ?_).trans ?_` can't infer the
  middle); for a `≤`-fiber second leg use `Nat.mul_le_mul h (le_refl _)`, for a
  `=`-length second leg `rw [<len eq>]`.
- **⚠ `Var` (= `abbrev Nat`) is OPAQUE to `omega` (2026-07-24).** A register goal
  `(x : Var) < k` makes `omega` treat `x` as an atom it can't relate to `Nat`
  arithmetic — it fails ("No usable constraints") or reports bogus counterexamples
  over metavariable atoms. Retype first: `change (_ : Nat) < _; omega`. When the
  goal is a gadget-lemma register hyp inside an application, drive it with
  `refine <lemma> ?_ … ?_ <;> · change (_ : Nat) < _; omega` — a bare
  `by omega` (or `@lemma … (by omega)`) as a metavariable-typed argument runs
  before the conclusion unifies and fails silently. `Cmd.UsesBelow`/`Op.UsesBelow`
  anonymous-constructor proofs need explicit nesting or `unfold <gadget>` first
  (the whnf that reveals the `∧`-structure does not fire through a bare `def`
  name in term mode).
- **NEW (2026-07-27): `omega` is blind to `Var`-typed HYPOTHESES, not only
  goals.** `h : (lo : Var) + 1 ≤ r` is simply not collected ("No usable
  constraints"), and `have := h.1` does not help. Scalable fix: **declare
  register parameters as `Nat`** — `Var` is an `abbrev` for it, so
  `Cmd.op (.clear lo)` accepts either, and every `omega` inside then just works
  (`S1SATComp.clearRange` and all its lemmas are stated this way).
- **NEW (2026-07-27): never let `exact`/`rfl` unify a value against
  `State.get <layout applied to a big constant> k`.** The unifier starts
  *evaluating* the constant (`flattenTM (MQ …)` — a whole compiled machine) and
  burns a 1M-heartbeat budget. Rewrite the layout to a literal list first
  (one `rfl` equation on opaque components) and read registers with `rfl`
  projections (`FrontS1Comp.get5_0`…`get5_4`).
- **NEW (2026-07-27): `by decide` cannot run on a goal that still mentions a
  parameter** ("Expected type must not contain free variables"). Once a witness
  is parameterised over its program, its `regBound` has free variables. State
  the frame as an **equation** (`… .regBound = 57`, by `rfl`) and `rw` it first.
- **NEW (2026-07-27): `variable (…)` does NOT give a family of declarations the
  same signature** — Lean includes only the variables each declaration
  *mentions*, so a theorem whose statement does not mention the parameters
  silently loses them and starts auto-binding. Spell the binders out on each
  declaration of a parameterised family.
- **⚠ `set x := e with h` leaves a LET-BOUND fvar, and `show`/`rfl` will unfold
  it (2026-08-04).** Any `show`/`rfl`/`decide` on a goal mentioning a `set`
  abbreviation for a machine state (`satStrPre.eval (...)`, a `Cmd.eval` chain)
  can whnf its way through the whole program and time out at 200000 heartbeats.
  Two fixes, both needed: **`clear_value x`** as soon as you no longer need the
  body (plus `clear` the equations), and prefer `rw [Cmd.eval_seq, Cmd.eval_op]`
  over `show (Cmd.op …).eval s = _` — the rewrite is syntactic, the `show` is a
  defeq check. Same family as the `clear_value b` rule for polynomial bounds
  below.
- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (lake **not** on
  PATH; LSP/most MCP can't find it). First build slow — kick off in background.
  Iterate one file directly: `env LEAN_PATH=$(lake env printenv LEAN_PATH)
  lean <file>` (fast, no lake) or `lake build <Module.Name>`. Commit per logical
  step, green. Headline: `Complexity.NP.SAT.CookLevin`.
  The two big witness files are SPLIT (2026-07-17): `BinaryCC_to_FSAT_free`
  and `FSAT_to_SAT_free` each = `*_defs` → `*_run` → original-name
  (cost + witness). Importing the original names still pulls in everything;
  put new codec/def-level lemmas in `_defs`, run lemmas in `_run`,
  cost/witness work in the original module — and keep `_defs` slim, it is
  what lets the two chains build in parallel. Editing a `_run` file
  re-elaborates only it + the modules after it, not a 9K-LOC monolith.
  ⚠ **The lib roots are `Basic`+`Complexity` (`lakefile.lean`), so `lake build`
  only checks modules TRANSITIVELY IMPORTED from `Complexity.lean` — a new
  `.lean` file that nothing imports is INVISIBLE to CI even if it `#eval`s/
  axiom-checks green in isolation.** When you land a new module, add its import
  to `Complexity.lean` (2026-07-12-c caught `FSAT_to_SAT_pre`/`_free` had been
  unimported since 2026-07-12-b). Verify: `find .lake -name "<Module>.olean"`.
- **Probe** a machine/program end-to-end (`#eval`) *before* proving its run
  lemma: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/X.lean`.
  Probe SEAMS end-to-end too (`FlatCCBinProbe.checkBridge` pattern: assert
  `AgreeBelow` register-by-register on concrete instances).
- **Axiom-check** via a scratch file: `#print axioms <name>` — only
  `propext`/`Classical.choice`/`Quot.sound` for new sorry-free results.
- **`omega` gotchas:** cannot see through `Var := Nat` variables
  (`simp only [Var] at *` first), `var`-typed rcases products — **and (2026-07-12-b)
  any goal whose `</=/≤` CARRIER is the `var` abbrev is silently skipped**
  (`fvar` payloads, `varInCnf` binders: bind `∀ v : Nat, …` explicitly or
  close with term lemmas); **`Nat.max` is an opaque atom** (close `max _ _ < _`
  with `Nat.max_lt.mpr ⟨by omega, by omega⟩`); or
  `encodable.size (n : Nat)` (rewrite with `(fun n => rfl : ∀ n : Nat,
  encodable.size n = n)` first); needs GROUPED products (`2*(P*P)`, never
  `2*P*P`); never splits `(l ++ r).length`; times out on products of two
  non-literal atoms (`generalize` them). **NEW: `omega` whnf-TIMES-OUT when
  `Cmd.cost`/`Cmd.eval` atoms over large states are in scope — fold every
  such atom with `set A := … with hA` + `clear_value A` + `clear hA` before
  calling it. And `omega` hits a hard performance cliff on ~20+-variable
  linear goals — extract a clean-context `private` arithmetic lemma and close
  with `linarith`, or bound componentwise with `gcongr` then `ring`-normalize
  and `omega` on single-variable monomials** (see `binBudget_arith`/
  `binBudget_le_poly`).
- **`l[i]` after a `Cmd.cost` hypothesis = whnf TIMEOUT** — hoist every
  `l[i]`-bearing `have` BEFORE `obtain`-ing a run/cost lemma.
- **`set` retro-folds eval equations but not terms produced by later `rw`** —
  fold new occurrences with `rw [← hs]`. `State.get_set_eq` can't see through
  a `set`-bound local — state a `have` via `rw [hs3]; exact State.get_set_eq
  _ _ _` first. `rw` matches registers SYNTACTICALLY — restate run-lemma
  facts at literal registers (`have hOFF' : State.get T 6 = _ := hOFF`) or
  pass the register explicitly (`State.get_set_ne _ CliqueRelTM.SKIPR _ _ h`).
- **NEW (session 3): plain (non-`omega`) `whnf` TIMEOUT from un-cleared nested
  `State.set` chains.** Threading a fold invariant through ~4+ sequential
  `set wN := w(N-1).set … with hwN` steps (one per `Op` in a straight-line
  body) makes later tactics (`show`, `rfl`, even unrelated `rw`s) try to
  unfold the whole chain back to the root state and time out — **not just
  in `omega`, this hits `rfl`/elaboration generally.** Fix: `clear_value wN`
  immediately after extracting the `get`/frame facts you need from `wN`,
  before introducing `w(N+1)`. The named equation (`hwN`) survives
  `clear_value` and is enough for everything downstream.
- **NEW (session 3): `show`-ing a composed `Cmd.eval` chain equal to a named
  end state is a DEFEQ CLAIM, not automatic — it fails whenever any step's
  `eval` equation was proved (not `rfl`).** Do not write
  `show State.get w5 R = _` hoping the real goal (`State.get ((c1;;c2;;…).eval
  w) R = _`) unifies with `w5` for free. Instead build one explicit
  `heval : (c1;;c2;;…).eval w = w5 := by rw [Cmd.eval_seq, e1, Cmd.eval_seq,
  e2, …, ← hwLast]` (peel one `Cmd.eval_seq` + one step-equation per `Op`,
  finishing with `← hwN` for every gadget-level sub-`Cmd` you black-boxed via
  its own `_run` lemma), `rw [heval]` once, *then* state the per-register
  goals — exactly the `cardStep_card`/`halfMove_run` `show (c1;;_).eval s =
  _; rw […]` pattern, which generalizes to any chain length. **Part-2
  addendum: even the initial `show`-unfolding of the program into its seq
  spine whnf-TIMES-OUT once the body contains a nested `forBnd`**
  (`emitCardsAt`'s body holds two `emitBitsFromSent` loops) — open `heval`
  with `unfold <programDef>` and peel with `rw [Cmd.eval_seq, …]` instead of
  a `show`. Factor every loop body as a named `def` (`sentBitBody`/
  `cardEmitBody`) so `_run` lemmas and `Cmd.foldlState` can name it.
- **NEW (session 3 part 2): `rw [List.replicate_add]` picks the wrong
  occurrence when the LHS replicate's length is itself a sum** (e.g.
  `replicate (a+b) 1 ++ replicate c 1 = replicate (a+b+c) 1`) — use
  `rw [← List.replicate_add]` to fold the append instead. And after
  `rw [<eq ending in serF f>]`, a residual `serF falseFml`/`serF .ftrue`
  literal does NOT auto-close — finish with an explicit `rfl`.
- **NEW (session 3 parts 3–4): more ambiguous-`rw` traps.** (a) In a
  nested-fold step lemma, `rw [List.range_succ]` grabs the goal's *inner*
  `List.range (L+1)` (from the inner-loop `_run` fact) instead of the
  outer `range (j+1)` — unroll the outer one in an isolated
  `have hsnoc : andPrefix ((List.range (j+1)).map g) = …` first, then `rw
  [hsnoc]`. (b) The `show`-as-defeq seq-spine unfolding whnf-times-out even
  for a FLAT body (no nested `forBnd`) once enough state is around — default
  to `unfold <def>` + `rw [Cmd.eval_seq, e1, …]` for every `heval`. (c) A
  `simp only [... State.set_set]`-closed branch whose goal mentions
  `[cond b 1 0]` after `cases b` leaves a `bif`-literal residue — finish
  with `rfl`. (d) When a `set wN`-named state IS the `rw`-target equation's
  RHS, the fold already happened — do not add `← hwN` (it fails with
  "pattern not found").
- **NEW (session 3 part 7): a literal `.set`-chain state (e.g. `encodeIn`)
  elaborates its `.set`s to `List.set`, NOT `State.set`** (the receiver's
  type is the unfolded `State` abbrev at definition time), so
  `State.get_set_eq`/`_ne` do NOT rewrite over it. Don't fight it: every
  `State.get (encodeIn C) r` on such a concrete frame is **definitional —
  close with `rfl`** (the `FlatCC_to_BinaryCC_free` witness fields already
  used this). Inside proofs, states built with explicit `State.set` (`s.set`
  where `s : State` is a variable) still match the `State.get_set_*` lemmas.
- **Multi-case register frames**: `interval_cases r` + per-case
  `repeat first | rw [State.get_set_eq] | rw [State.get_set_ne _ _ _ _ (by
  decide)]` walks any concrete nested-set state (the seam-bridge pattern).
- **`simp` with `List.take_succ` can hit max-recursion in a fat context** — use
  the explicit `rw [List.take_add_one, List.getElem?_eq_getElem hi]` chain.
- **`decide` fails when the goal type mentions free vars** — `show (0 : Nat) ≠ 2`
  first. `Cmd.UsesBelow` of a concrete program: full `simp [defs…]`.
- **`set` (tactic) lives only in `PolyTime.lean`, not `Frame.lean`** (core-only).
- **NEW (session 4, the cost pass):** (a) `Cmd.flatK`/`Cmd.cost` atoms in a
  goal make `omega`/`ring`/`nlinarith` whnf- or isDefEq-TIMEOUT — always
  `set K := Cmd.flatK (…) with hK; clear_value K` (and the same for
  `(Ω+1)^d` power atoms `P2/P3/…`) before the arithmetic closer; keep the
  power-tower equations (`hP3 : P3 = (Ω+1) * P2`) and close with `ring` on
  those + `omega` on the atoms. (b) `nlinarith` in a fat context (a loop
  lemma's 60+ hypotheses) TIMES OUT — extract clean-context `private`
  helpers (`one_le_P`, `le_scale`, `mulLoopClose`, `subLoopClose`). (c) Give
  every `K·(Ω+1)^d` bound Ω=0 HEADROOM (constants like `+16·P4` must cover
  the additive junk at `P4 = 1` — a too-tight constant fails only at Ω=0 and
  omega's counterexample is unreadable). (d) After `rw [Cmd.cost_op]` add
  `simp only [Op.cost]` or the un-evaluated `Op.cost` term poisons `omega`.
  (e) `;;` binds LOOSER than `=`: parenthesize the RHS of every
  `c = (a ;; b) := rfl` restructuring equation. (f) The membership hypothesis
  of `Cmd.eval_get_of_not_writes` is `decide`-able only at CONCRETE registers
  — for symbolic `BASE`, take it as a lemma hypothesis and discharge at call
  sites. (g) `emitFtrue_cost`/`emitFandTag_cost`/`emitForrTag_cost` (= 3) and
  `emitFalse_cost` (= 9) are `rfl`.
- **NEW (2026-07-12, the seam): `injection` on an equation whose CONTEXT holds
  un-`set` composite `Cmd.eval` terms whnf-TIMES-OUT** — it ends up
  symbolically executing the reduction programs (~800K `Nat.rec` unfoldings;
  found by bisect, `set_option diagnostics true` names the culprits). Split
  list equations with `simp only [List.cons.injEq, and_true] at h` +
  `obtain` instead — cheap in the same context. Restating a run-lemma fact
  at a literal register (`have h17 : State.get T 17 = _ := hBOFF`) is a safe
  defeq ascription (register defs unfold; the state arg matches
  syntactically).
- **NEW (2026-07-16, the cost assembly):** (a) the 2026-07-15-b perf
  prescription WORKS and is now the standard for big straight-line cost
  proofs — per-branch `private` lemmas + frame facts precomputed as `private`
  one-liners (each loop write-set `by decide` runs ONCE) + `clear_value`
  after every `set`: `tokenBody_cost` elaborates in ~9s where the monolith
  took >14 min. (b) **`rw [h1, h2] at *` rewrites h1 with itself** (turns it
  into `1 = 1`) — never use `at *` with hypothesis names in the rewrite list;
  distribute per-hypothesis (`rw [Nat.add_mul] at hvar`). (c) `omega` slack
  bounds for `c·X`-vs-junk goals need `27 ≤ X = (E+N+3)³`, not just `1 ≤ X`
  (e.g. `6N+5 ≤ 10X` fails at `X=1`) — bundle `N ≤ X ∧ 27 ≤ X` (`X_facts`).
  (d) distribute `(a+b)*X` with the RIGHT number of `Nat.add_mul` rewrites
  per hypothesis, then `set`+`clear_value` each `flatK·X` product so `omega`
  sees matching atoms on both sides. (e) `Nat.le_self_pow (by omega) _` gives
  `a ≤ a^3` — the cheap way to fund linear-junk-under-cubic bounds.
- **NEW (2026-07-20-b, `inOPoly` closure):** `inOPoly_comp`/`inOPoly_add`
  **UNFOLD `physStepBudget`** (and any def ending in `+ x`) during goal-driven
  unification and split the sum at the WRONG `+`, so `exact inOPoly_add … …`
  against a goal mentioning `physStepBudget` fails with an "application type
  mismatch" showing the budget unfolded. Fix: pass **explicit `(f := …)(g := …)`**
  to `inOPoly_comp`, and build every sum as a `have hsum := inOPoly_add … …`
  (types fixed from the operands, not the goal) then `exact hsum` — the defeq
  check accepts the fold without re-splitting. For a `physStepBudget A B` term
  with non-diagonal args, dominate by its diagonal `physStepBudget M M`
  (`M ≥ A, B`) via `physStepBudget_mono` + `inOPoly_of_le`, then close with
  `(fun m => physStepBudget m m) ∘ M` = `inOPoly_comp M_poly physStepBudget_poly`.
  And a `physStepBudget_mono`-bounded `≤` goal after `refine inOPoly_of_le …`
  is a beta-redex — `show`-restate it before `omega`.
- **NEW (2026-07-20-c, wiring a multi-gadget `Cmd` run lemma —
  `FrontProgram.lean`):** three `omega` traps, all with the SAME misleading
  symptom (`omega could not prove` + a counterexample listing only the ambient
  `hB`/`hxW`, i.e. an *empty* goal model). (a) **An un-ascribed `by omega` as a
  gadget-call ARGUMENT runs against a still-metavariable goal** (`?scan ≠
  ?cnt`) — the explicit register args unify too late. Fix: **type-ascribe every
  one** — `(by omega : (B + 5 : Var) ≠ B + 4)`. (b) **`refine ⟨?_,…,?_⟩ <;>
  omega` and bare `by omega` on a big `∧`-conjunction** hit the same empty-goal
  failure. Fix: prove each conjunct as its own ascribed `have`, or (for the
  final register reads) `by decide` on the constant `≠`s. (c) **After `set sᵢ
  := …`, `omega` whnf-chokes on the `let`-bound state bodies** — `clear_value
  s1 s2 s3 s4` (the `hsᵢ` equations survive) before any `omega`-heavy step. Two
  more: after `set sᵢ`, the gadget's run/frame hyps are **auto-folded to be
  about `sᵢ`** — use them directly, do NOT `rw [hsᵢ]` (unfolding `sᵢ`
  mismatches the folded hyp). And `State.get_set_ne _ _ _ _ h` does NOT match a
  `set`-opaque local (`t0`) — build the copy-block result from explicit `.set`
  terms (state the read `have`s with explicit types so the `_`s unify).
- **NEW (2026-07-16, probing):** `#eval` of a `Cmd` with nested `forBnd`s on
  a >1K-bit stream is OUT OF BUDGET (the budget scan is cubic; the T1 seam
  probe timed out at 10 min) — probe BRIDGES register-by-register on big
  instances and reserve end-to-end `#eval` for small ones. To probe against
  a `noncomputable` map, decode the machine's own output stream (`decodeF`)
  instead of cloning the map.
- **NEW (2026-07-25-b, P+G): `&&` binds LOOSER than `=`.** `a && b = c` parses
  as `a && (b = c)` — every `Bool` identity lemma needs BOTH sides
  parenthesised (`(a && b) = (c && d)`). The symptom is a goal full of
  `decide (x = y)` where you expected `&&`-atoms.
- **NEW (2026-07-25-b): `rfl` for `c.eval s = c'.eval (c₀.eval s)` whnf-TIMES
  OUT even though `Cmd.eval_seq` is `rfl`** — `Cmd.eval` is `Cmd.run`, so the
  defeq check tries to *evaluate* the loops symbolically. Always prove such
  peel equations with `unfold <suffix def>; rw [Cmd.eval_seq]`. Corollary
  shape: name every command suffix as its own `def` and give it a one-line
  `_eval` peel lemma (`S1Parse.pSuf1_eval` …). Then a register that a suffix
  does not write is read off with ONE `Cmd.eval_get_of_not_writes … (by
  decide)` over the whole suffix — the cheapest frame reasoning in the project.
- **NEW (2026-07-25-b): `Cmd.UsesBelow` has no `Decidable` instance** — `by
  decide` fails; use `simp [<every def in the program>, Cmd.UsesBelow,
  Op.UsesBelow, <every register def>]` (the `kCnf3Check_usesBelow` pattern).
  `r ∉ c.writes` at concrete registers *is* `by decide`-able, and cheap even
  for a 1.3K-LOC program.
- **NEW (2026-07-25-b): bundle a multi-register loop invariant as a `def
  … : Prop` plus `_set`/`_frame` transport lemmas** (`S1Parse.EInv`/`SInv`).
  Each program step then becomes one line, and the `by decide` write-set
  memberships are paid once per lemma instead of once per step. This is what
  kept a thirteen-step entry body to ~20 lines of proof.
- **NEW (2026-07-25-b): a big straight-line proof needs `set_option maxRecDepth
  8000`** — the suffix-peel chain exceeds the default at ~10 steps.
- **NEW (2026-07-25-b): `simp` (not `simp only`) on a `Bool` identity turns it
  into a `Prop` conjunction** and then fails; for `&&` reassociation use
  `simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]`.
- **NEW (2026-07-25-c, `Fin`→`Nat` models): the change-of-variables recipe.**
  A `Fin`-typed nest becomes a machine-shaped `List.range` nest with
  `List.map_coe_finRange_eq_range` (`(finRange n).map (↑·) = range n`) +
  `List.flatMap_map` — packaged as `S1Cards.finRange_flatMap_congr` /
  `map_finRange_congr` (`(∀ i : Fin n, f i = g i.1) ⊢ (finRange n).flatMap f =
  (range n).flatMap g`). Push the flattening through the four list combinators
  with `List.flatMap_append` / `List.flatMap_assoc` / `List.flatMap_map` and a
  hand-rolled `filterMap` lemma. **Enumerations that are not `finRange`**
  (`xOpts`, `pKindList`) need one bespoke `_flatMap` lemma each — state it via
  the *index function* (`kindIdx`) when every consumer is a function of the
  index (`pKindList_flatMap`), and with explicit per-constructor hypotheses
  when a consumer must distinguish constructors (`xOpts_flatMap`, whose
  `Lmove` case needs "is this the boundary marker?").
- **NEW (2026-07-25-c): most cell-code equalities are `rfl`.** `(tCell M b).1`,
  `(hCell M q b).1`, `(bCell M).1`, `(emb M c).1`, `(stateOf M n).1` and the
  whole `cnats ∘ flattenCard` chain reduce definitionally, so a family equation
  is usually `refine finRange_flatMap_congr _ _ _ (fun i => ?_)` nested to
  depth, then `cases mv <;> rfl`. Keep `rOf_eq`/`wOf_eq` as the only
  abstraction barrier (rewrite them on the *model* side, left to right).
- **NEW (2026-07-25-c): `{ e with a := x, b := y }` cannot break the line
  before the first field's column.** Structure-instance fields are parsed with
  `withPosition` anchored at the **first** field, so in `{ cM0 with states := …,`
  a continuation line must be indented past `states`, not past `{`. Symptom:
  `unexpected identifier; expected '}'` pointing at the previous line's end —
  and, worse, an `#eval` that silently uses the un-updated record. Prefer a
  named `def` per record.
- **NEW (2026-07-25-c): `omega` cannot use hypotheses about a `Var`-typed
  variable even after `change (_ : Nat) …`.** A frame lemma
  `(hr : 6 ≤ r ∨ r = 0) ⊢ r ≠ 5` is closed *not* by omega but by
  `rintro k hk rfl` on a decidable disjunction (`k = 1 ∨ … ∨ k = 5`) plus
  `exact absurd h (by decide)`. Also: `by omega` supplied as an *argument*
  (`key 5 (by omega)`) runs against a metavariable goal — hoist every such side
  condition into its own `have`.
- **NEW (2026-07-25-c): `simp [Bool.eq_iff_iff, List.any_eq_true]` loops.** To
  transport a member-wise `Bool` equation across `List.any`, write the two-line
  induction helper instead (`S1Cards.any_key`).
- **NEW (2026-07-25-c, tooling): never build an edit by slicing between two
  `str.index` anchors.** If the anchors come out in the wrong order the slice is
  `""` and `str.replace("", new)` inserts `new` between every character (a
  1.8M-line file). Anchor edits on literal text, or assert `start < end` first.
- **NEW (2026-07-26): a state built as `([] : State).set a x |>.set b y` in a
  PROBE elaborates its `.set`s to `List.set`, not `State.set`** (the 2026-07-12
  gotcha, hit again from the other side) — and `List.set [] 2 v = []`, so every
  register reads `[]` and every check silently prints `false`. Write
  `State.set (State.set ([] : State) a x) b y` explicitly when constructing a
  probe state.
- **NEW (2026-07-26): `rw [if_pos h]` fails when the condition is a `Bool`
  coerced to `Prop`.** `h : (fst && decide (j = 0)) = true` does not match the
  `if`'s decidable instance (the pattern comes out with a doubled `decide`).
  Use `cases hfb : (<the Bool>) with | true => … | false => …` and `simp [hfb]`
  in each branch — `hfb` rewrites the condition to a literal and the `reduceIte`
  simproc finishes.
- **NEW (2026-07-26): `simp only` does not close a goal whose two sides are the
  same STUCK `match`** (e.g. `Op.eval (.head dst src)` after rewriting the source
  register). Finish with an explicit `rfl`.
- **NEW (2026-07-26): an `induction l` INSIDE a `have` whose ambient context
  mentions `l` produces an unusable IH** (`omega` then fails on the fold sums).
  Extract every such induction as a standalone `private` lemma over a fresh list
  variable — `length_eq_sum_ones` / `mul_sum_map` / `trans_sum_le` are the model.
- **NEW (2026-07-26): a `_run` lemma with an 11-register frame chain is a smell.**
  Bundle the dirty set as one `abbrev … : Prop` (`S1Emit.IClean`) and project
  with `hr.2.2.…`; better still define the coarse `EDirty` predicate over the
  whole scratch block once (NEXT TOP-DOWN item 2) so composition is one
  hypothesis per stage. Keep BOTH frame forms available:
  `Cmd.eval_get_of_not_writes … (by decide)` is the cheapest step for a
  CONCRETE register but needs it outside the write set, and a dirty-set-keyed
  lemma cannot serve a concrete register that is merely not written.
- **NEW (2026-07-26-b): `omega` cannot see through a `def`-bound `Nat` bound.**
  `Cmd.UsesBelow_mono (by omega) h` against `6 ≤ s1RegBound` fails with a
  counterexample over the *atom* `↑s1RegBound`. Write
  `(show 6 ≤ s1RegBound by unfold s1RegBound; omega)`. Same family as the `Var`
  opacity gotcha above.
- **NEW (2026-07-26-b): `#eval` aborts on ANY expression depending on `sorryAx`,
  including down a branch it never evaluates.** A skeleton program with one
  `sorry`-ed stage cannot be `#eval`-probed at all, even on inputs that take the
  built branch. Probe the *composition the proof reduces to* instead
  (`probes/S1ProgramProbe.lean` §2), and re-point the probe when the placeholder
  lands. (`#eval!` exists but risks a runtime crash — do not use it in a
  committed probe.)
- **NEW (2026-07-26-b): a sorried `_run` contract is an unchecked assumption —
  probe it.** The assembly typechecks against whatever the contract *says*, so a
  mis-stated placeholder lemma is invisible until the stage is built. Give every
  sorried contract a numeric probe of its conclusion on real instances
  (`probes/S1ProgramProbe.lean` §3–4 does this for `stageC_run`/`stageMYes_run`).
- **NEW (2026-07-26-c): a frame clause should quantify over a register LIST, not
  a chain of `≠`s.** `∀ r, r ≠ dst → r ∉ D → …` composes: `nmem_sub (by decide)`
  widens/narrows `D` between loop levels and `ne_of_nmem h (by decide)` produces
  the per-gadget `r ≠ EK1` that an atom's `_run` wants. Both memberships are
  `by decide` at concrete registers. This is what kept five nested-loop families
  to ~40 lines of proof each.
- **NEW (2026-07-26-c): `refine <lemma> … (fun i t h1 h2 => ?_)` inside a `have`
  does not work** — `?_` is `refine`-only syntax. State the intermediate result
  as an explicit `have key : … := by refine …` and project afterwards.
- **NEW (2026-07-26-c): `rw` needs the loop body SYNTACTICALLY.** After
  `refine emitLoop_run … body …` the goal mentions the body's `def` name, while
  the atom's `_run` lemma is about its unfolded form — `unfold <bodyDef>` first
  (or close with `exact`, which is up to defeq; only `rw` is syntactic).
- **NEW (2026-07-26-c): a doc comment `/-- … -/` cannot precede `#eval`** in a
  probe (`unexpected token '#eval'; expected 'lemma'`) — use a module comment
  `/-! … -/`. And a `Prop`-valued `#eval` needs an explicit `decide`.
- **NEW (2026-07-26-c): `fin_cases h` is the way to case on `r ∈ [<literals>]`**;
  `rintro (rfl|…)` fails ("not a free variable") because list membership is not
  syntactically a nested `Or`.
- **NEW (2026-07-26-c): `Cmd.UsesBelow` of a program containing a `private`
  sub-`def` cannot be closed by `simp [<defs>]`** — the private bodies do not
  unfold. `unfold <program>; refine ⟨<sub-lemma>, ?_⟩; simp [<the rest>]`
  (`S1CardEmit.cPre_usesBelow` over `S1Emit.loadSg_usesBelow` is the model).
- Methodology: **skeleton-first; refine the highest-risk gap next; decompose
  `sorry`s, don't elaborate them; probe before committing engineering;
  `def`+`sorry` over `axiom` (count = 0); build green between commits.**
