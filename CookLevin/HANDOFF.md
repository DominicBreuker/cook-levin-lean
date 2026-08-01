# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). **This file is the forward-looking working plan.**
We work multi-session in two alternating streams — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

**Read in this order.** "Where the proof stands" → "★ Latest session" → the
**NEXT** section for your stream → "Before you push". Everything from "Standing
architecture risks" down is a **reference index**: consult it before building
anything, do not read it front to back.

## Where the proof stands (2026-08-03)

**COOK–LEVIN IS PROVEN, on the honest statement, unconditionally — audited,
stated in a form with no dishonest instantiation, and non-vacuous. `lake build`
itself proves the library is `sorry`-free and axiom-clean.**

```
CookLevinHonest.CookLevinStr : NPcompleteStr SAT      -- ★ the one to quote
CookLevinHonest.CookLevin''  : NPcomplete'' SAT       -- the general statement
both depend on axioms: [propext, Classical.choice, Quot.sound]
```

| piece | status |
|---|---|
| sound tail, C8 front, tableau maths + both size bounds | ✅ axiom-clean |
| S1 map + guard + program (all stages) + cost ladder | ✅ axiom-clean |
| `FrontS1Comp.SAT_NPhard''` (hardness) / `EvalCnfSplit.SAT_inNPLangFreeSplit` (membership) | ✅ axiom-clean |
| **`CookLevinHonest.CookLevinStr : NPcompleteStr SAT`** | ✅ the headline |
| the tail decoder `FSATSATFree.decodeOut` | ✅ a real parser (`Serialize cnf`) |
| the head encoder `FrontWitness.encodeInQ` | ✅ literally `W.encX`, i.e. `certState x` under `NPhardStr` |
| axiom/`sorry` hygiene · the two audited functions · `Op.cost` as a time proxy | ✅ *build-time* obligations, not probes |
| **non-vacuity of the `NPhardStr` hypothesis** | ✅ **NEW 2026-08-03** — inhabited *and* not satisfiable by arbitrary predicates (`Complexity/NonVacuity.lean`, gated) |

**The honesty surface that remains** is exactly: the *statement*
(`NPcompleteStr`, `NPhardStr`, `InNPWitnessStr`), the meaning of `SAT`, the
faithfulness of `FlatTM`/`stepFlatTM` as a Turing machine, and `Serialize cnf`.
Four definitions, read once. Everything else is machine-checked. Read the
README's "What a reviewer actually has to do".

⚠ **Do not let that list grow.** If you find yourself adding a fourth kind of
thing a reviewer must trust, *that is the finding* — write it down before you
write any Lean.

## ★ Latest session

**2026-08-03 (top-down) — non-vacuity, and demolition.**

**FINDING AR — a hardness statement has TWO ways to be vacuous, and four
sessions had worked on only one of them.** `NPhardStr SAT` is
`∀ Q, inNPStr Q → Q ⪯p' SAT`. Every session from 2026-07-30 to 2026-08-02 made
`inNPStr` *harder* to satisfy (the split layout laws, then `sizeLB`, then
pinning the layout outright in `InNPWitnessStr`) — each time correctly, each
time to close a dishonest-instantiation hole. **None checked that anything still
satisfied it.** Until this session the library contained **no `InNPWitnessStr`
at all**: for anything a reader could check, the headline was an implication
with an empty hypothesis class. The generalisable lesson: *every time you
strengthen a hypothesis, the very next obligation is to re-exhibit an
inhabitant* — otherwise the strengthening that makes a statement honest is the
same edit that makes it empty.

**Landed: `Complexity/NonVacuity.lean`** (gated, in the default build target),
closing both directions.

1. **Not everything.** `searchDecide W bound` is a **running `def`**: it
   enumerates every certificate of length `≤ bound (size x)` (`bitStringsUpTo`,
   with `mem_bitStringsUpTo` proving the enumeration exact) and *executes the
   witness's own verifier `Cmd`* on the canonical layout
   `certState x ++ certState c`. `searchDecide_correct` proves
   `Q x ↔ searchDecide W R.bound x = true` for any `W : InNPWitnessStr Q` and
   any `R : PolyCertRelWitness Q W.rel`. **So no undecidable `Q` inhabits
   `inNPStr`** — the freedom `probes/HonestyAuditProbe.lean` §7/§7b exploits
   against `NPhard''` is not available against `NPhardStr`.
   `searchDecide_calls` states the price: `2^(bound+1) - 1` verifier runs.
2. **Not nothing.** `SquareStr x := ∃ c, x = c ++ c` with a complete
   `InNPWitnessStr` — a two-op verifier `Cmd` (`concat 2 1 1 ;; eqBit 0 0 2`) on
   the canonical two-register layout, exact cost accounting
   (`squareCmd_cost : |x| + 6|c| + 3`), and a certificate that is *load-bearing*
   (`verifier_reads_certificate`: same input, two certificates, two answers).
   §4 separates strings, so the inhabitant is a real language and not
   `fun _ => True` in disguise.
3. **The payoff.** `squareStr_reducesPolyMO'_SAT : SquareStr ⪯p' SAT` is
   `CookLevinStr.1` applied to that witness — the whole chain, C8 front through
   the sound tail, running on a concrete problem.

**Also measured, for the next session's benefit (top-down item 1).** The
go/no-go for the `Cmd`-level search is **GREEN**: `DecidesLang.toDecidesBy`'s
`inOPoly costBound`/`monotonic costBound` hypotheses are consumed at *exactly
two field sites* (`encodeBound_poly`/`encodeBound_mono`), i.e. for the encoding
bound, not the time bound. A variant with a separate polynomial `encBound` and a
completely free `costBound` was written and **typechecked** this session, then
reverted rather than landed — unused API is what this session spent a commit
deleting. ⚠ It must live *inside* `Lang/PolyTime.lean`: `padTimeBound` and
`budget_ge` are `private` there.

⚠ **Two rungs are deliberately NOT claimed, and the file says so.**
`searchDecide` is a **Lean function, not a `Cmd` and not a `FlatTM`** — see
top-down item 1. And `SquareStr` is in **P** — an NP-complete inhabitant needs
bottom-up work, see bottom-up item 2. `inNPStr_exists_decider` (the classically
trivial `∃ f : List Bool → Bool, …`) is stated in the file *only* so that nobody
re-derives it and mistakes it for the result.

**Also landed: the `⪯p` API is gone, and so is the dead weight.**
`reducesPolyMO`/`⪯p`, `ReductionWitness`, `PolyTimeComputableWitness`,
`polyTimeComputable`, `NPUniversal`, `NPhard`, `NPcomplete`, `red_NPhard`,
`NPhard_subtype_proj`, the nine wrapper theorems, and the four bridges down from
`⪯p'`/`NPhard'` were deleted. The 2026-07-30-c decision had been to *retain*
them unused; that was reversed. A vacuous notion with no live consumer, one
bridge away from the real statement, lets a reader derive `NPcomplete SAT` from
`NPcompleteStr SAT` and come away with the wrong theorem — and reading is the
only thing between this development and its claim.
`PolyTimeComputableWitness`'s four size-bound fields are **inlined into
`Lang.PolyTimeComputableWitness'`**, where they belong (an output-size bound
*plus* a real machine). Every reduction map, correctness lemma and output-size
bound survives untouched. Deleted with it: `parked/` (~15K LOC, retired
2026-07-30-c), `coqdoc/`, `.mcp.json.bak`, `Basic.lean`, `Main.lean`;
`Complexity` is now the lakefile's only root, so "the axiom sweep covers the
library" no longer carries a footnote.

## NEXT TOP-DOWN session

The proof is done and five gates run inside `lake build` (axioms, the honesty
pins, cost-as-time, and now non-vacuity). Top-down work is still **turning
reading obligations into typechecking obligations**. Item 1 is the only real
build; 2 is blocked on bottom-up; 3–4 are maintenance.

### 1. The `Cmd`-level certificate search — the last rung of non-vacuity

**Target.** `inNPStr Q → ∃ f, Nonempty (DecidesBy Q f)` with `f` exponential:
`Q` is decided by a real `FlatTM` in *this development's own computability
model*, not merely by a Lean function. `Complexity/NonVacuity.lean` already
pins the statement this must reach (`searchDecide_correct` is the pure-model
half), so this is a program-and-cost job, not a design job.

✅ **The go/no-go is DONE (2026-08-03) and the answer is GREEN — do not redo
it, but do read the caveat.** The question was whether the bridge to a real
machine forces the *time* bound to be polynomial. It does not.
`DecidesLang.toDecidesBy` demands `inOPoly costBound` / `monotonic costBound`,
but those two hypotheses are used at **exactly two field sites**,
`encodeBound_poly` and `encodeBound_mono` — i.e. for the *encoding* bound, not
the time bound. `DecidesBy.encode_size`, `budget_ge`, `decides_pos` and
`decides_neg` need no polynomiality at all.

So the bridge you need is a variant taking a **separate** polynomial `encBound`
with `∀ x, State.size (D.encodeIn x) ≤ encBound (size x)`, leaving `costBound`
completely free. **It was written and typechecked this session** (a copy of
`toDecidesBy` with those three fields retargeted, ~85 lines, no other change)
and then reverted rather than landed, because unused API is exactly what this
session spent a commit deleting. Re-create it when you have a consumer.

⚠ **Caveat that decides where it lives:** `DecidesLang.padTimeBound` and
`DecidesLang.budget_ge` are **`private` to `Lang/PolyTime.lean`**. The variant
therefore has to be added *inside that file*, next to `toDecidesBy` — it cannot
live in a new module, and it cannot live in a probe. Budget it as an edit to
`PolyTime.lean` (≈15 min cold rebuild, everything above it in the import graph
pays).

**The program, if it is green.** Registers **above** `W.verifier.regBound`
(FINDING AE: `usesBelow` means the verifier cannot touch them), so the
enumerator owes no scrub of its own state:

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
  binary representation of `i`". ⚠ **Write that invariant as a `Bool` function
  and `#eval` it at every index before proving anything** (FINDING AI — this is
  the cheapest de-risking move in the codebase and it is what made
  `EvalCnfSplit.decodeBody_run` ~110 lines with zero redesign).

Budget: one session for the program + `_run` (the go/no-go is already spent), a
second for the cost bound. **Do not start it as a side quest**, and do not
weaken the target to the classically trivial existential
(`NonVacuity.inNPStr_exists_decider` is already there, labelled).

### 2. An NP-complete inhabitant — blocked on bottom-up item 2

`SquareStr` proves the class is non-empty; it does not prove the class contains
anything *hard*. The statement worth having is `inNPStr SATStr` for a bit-level
string encoding of SAT — then `CookLevinStr` applied to it is a genuine
self-reduction and the hypothesis class demonstrably contains an NP-complete
language. The verifier work is bottom-up (item 2 below). When it lands, top-down
owes three short things: the `InNPWitnessStr` assembly, the corollary
`SATStr ⪯p' SAT`, and a verdict row under ROADMAP risk **S7**.

### 3. Audit whatever the bottom-up stream lands (S5, standing but SHORT)

By FINDING AK only the composite's **leftmost `encodeIn`** and **rightmost
`decodeOut`** matter, and by FINDING AL a seam's `mfc` needs no audit.

* head extension → nothing to do if the chain is entered through `NPhardStr`;
  otherwise audit `encX` against the criterion: every register is a constant, a
  mechanical serialization of an input field, or a *metric* of the input — never
  the reduction's output. (And it must supply `sizeLB`, which for any layout
  that spells the input out is `id` or a small multiple.)
* **tail extension → give the new output type a `Serialize` instance and define
  `decodeOut := Serialize.decodeD default ∘ get OUTREG`.** Do not hand-write an
  inverse and do not use `Function.invFun`. `Deciders/CnfSerialize.lean` is the
  worked example (fuel-based parser, `dec_enc` by induction on the grammar,
  ~200 lines including both size laws).
* middle witness or seam `mfc` → nothing to audit; say so in one line.
* a new **verifier** owes the `DecidesLang` version of the same check plus a
  `polyCertRel` (machine-checked non-vacuity — do not re-derive it).
* add a numbered verdict row to ROADMAP **S5**, a `#assert_axioms_clean` line to
  `Complexity/SoundnessGate.lean`, and a section to
  `probes/HonestyAuditProbe.lean` if it is `rfl`-checkable — prefer
  `Complexity/HonestyGate.lean` for a positive pin, the probe for a negative
  control.

### 4. Probe-suite consolidation + `probes/README.md`

49 probe files, no index, runtimes from 4 s to ~6 min, and a reader cannot tell
which are regression gates and which were one-shot go/no-go scoping. Write the
index (what each pins · runtime · "re-run after changing X"), mark the ones that
are still gates now that the build covers axioms, the honesty pins, cost-as-time
*and* non-vacuity (should be just `HonestyAuditProbe`'s negative controls,
`CostChkIntentProbe`, and `NonVacuityProbe`'s `#eval`s), and retire
`probes/S1CardEmitProbe.lean` §1 (superseded by `S1StepLoopProbe` §1, which
asserts the full equality).

### 5. The `.github/` residue — owner decision, not ours

`.github/workflows/lake-build.yml` **already exists and already runs
`lake build`**, so the "CI question" of earlier handoffs is answered: CI is
green-gated on the axiom sweep today, and `lake build` alone is sufficient for
`sorry`/axioms. If the owner wants the *negative* controls covered too, add
`lean probes/HonestyAuditProbe.lean`, `lean probes/CostChkIntentProbe.lean` and
`lean probes/NonVacuityProbe.lean` — the positive pins are already in the build.

⚠ Stale after 2026-08-03, **not fixed here**: `.github/scripts/researcher.py`
still names the deleted `coqdoc/` folder as "the blueprint", and
`.github/prompts/step*.md` still cite files under it. Agent sessions have no
workflow permission and that subtree is the owner's legacy porting harness.
Flag it, do not quietly edit it.

## NEXT BOTTOM-UP session

**Nothing on the critical path is waiting on a gadget.** Bottom-up work is scope
extension plus one new item that now has a top-down consumer.

⚠ **Interface note.** `InNPWitnessLangFreeSplit` carries `sizeLB` /
`sizeLB_poly` / `encX_sizeLB` (since 2026-08-02). Every **verifier/membership**
witness must supply them; for any layout that writes the input out it is one
line (`sizeLB := id`, plus the "the stream is at least `size x` long" lemma —
see `EvalCnfSplit.satSplitWitnessOf`, which uses
`CnfSerialize.size_le_encodeCnf_length`). `PolyTimeComputableLang` is untouched,
so **reduction** witnesses are unaffected.

1. **Membership for `FlatClique`** (~1 session, start here — the verifier
   already exists). Repeat `Deciders/EvalCnfSplit.lean` verbatim against
   `cliqueRelDecidesLang` (axiom-clean since 2026-07-01):
   * a **total** `List Bool` certificate relation — characteristic vector, never
     a sentinel format (FINDING AG);
   * a split `encX`/`eIn` literal (FINDING AD: `precomposeFree` *chooses* the
     composite's `encodeIn`, so trailing scratch registers are invisible — check
     `AgreeBelow regBound`, not list equality);
   * a one-register re-encoder `Cmd` with its scratch **above** the verifier's
     `regBound` (FINDING AE — then it owes no scrub);
   * cost by `Cmd.chk` (`by decide`), frame by `Cmd.writes`;
   * `sizeLB`;
   * the `_run` lemma — and **write its loop invariant as a `Bool` function and
     `#eval` it at every index first** (FINDING AI).
2. **`SATStr` — SAT as a *string* language** (~1 session; **new, and it is what
   makes top-down item 2 possible**). Target: an `InNPWitnessStr` whose `Q` is
   "the bits of `x` decode to a satisfiable CNF".
   * The obstruction is real and worth probing before coding: the canonical
     layout is **one register of raw bits**, while `EvalCnfCmd`'s verifier wants
     a twelve-register layout with `CLAUSE_TALLY`/`CNF_STREAM`. So this needs an
     **on-machine parser** `Cmd` from a self-delimiting bit format into that
     layout — the `DecidesLang.FreePrecomposeData`/`precomposeFree` pattern
     (FINDING AD/AE apply verbatim).
   * ⚠ **Pin the bit format on paper and `#eval` a Lean model of the parse at
     every prefix length before writing the `Cmd`** (FINDING AI). Reuse
     `Deciders/CnfSerialize.lean`'s grammar if it fits — a format whose Lean
     parser already has `dec_enc` is a format whose `Cmd` you can state a
     `_run` lemma for.
   * `sizeLB` is free here (`Lang/HardnessStr.lean`'s
     `InNPWitnessStr.canonical_sizeLB`, `fun n => 2*n`).
3. **Membership for `kSAT 3`** (~1 session) — same shape as item 1;
   `KSat3Free` already has the re-encoder pattern.
4. **Hardness** — `SAT ⪯p' kSAT 3` and `kSAT 3 ⪯p' FlatClique` as free-line
   witnesses (template: `NP/kSAT_to_SAT_free.lean`, which already does the
   mirror-image `kSAT 3 ⪯p' SAT`), then one `SeamData`/`comp` each onto
   `FrontS1Comp.front_to_SAT_witness`, and `NPhard''`/`NPhardStr` transport for
   free. ⚠ **This extends the chain at the TAIL**, so the composite's
   `decodeOut` becomes the new last witness's — **so the new output type owes a
   `Serialize` instance** (`FlatClique`'s output is a graph + a `k`; write the
   parser, do not use `Function.invFun`). One verdict row, not a study; see
   top-down item 3.
5. **Then, and only then, an `NPcompleteStr` for the new problem.** The
   transport is `NPcomplete''_to_NPcompleteStr` plus the membership half; do not
   restate hardness from scratch.

⚠ Do **not** pre-factor `satPrecomposeData`/`satSplitWitnessOf` into a generic
combinator before the second instance exists — copy first, factor when a third
consumer appears (that is how `emitFold_run` was found).

**Do NOT re-open**, on pain of re-proving an axiom-clean theorem: `s1Key`,
`s1RegBound`, `EScratch`/`CDirty`, `stageC_run`'s statement, the two seams'
scrub ranges, `S1Step.stepSeg`/`stepEmit`'s contract, the entry loop's register
table, the `copy r r` no-op (FINDING X),
**`EvalCnfCmd.encodeState`/`evalCnfCmd`/`regBound = 16`**,
**`satEncX`/`satEIn`/`xWidth = 3`** (FINDING AD), or **`certDecode`/
`decodeBody`/`DCUR`=16/`DIDX`=17/`DHD`=18** (the `_run` lemma is pinned to that
exact program). Stage C's 30-register licence is **exactly** exhausted. And do
not rebuild `Cmd.PolyCost` (FINDING AJ) or the `LangEncodable` layer.

## Before you push

**`lake build` is the gate.** If it is green, every declaration under
`Complexity` is `sorry`-free and uses only Lean's three axioms
(`#assert_library_axiom_clean` asserts it at elaboration time), the two audited
functions are what the audit says they are (`Complexity/HonestyGate.lean`),
`Op.cost` is a proven time proxy (`Complexity/CostFaithfulness.lean`), and the
hypothesis of the headline is non-vacuous (`Complexity/NonVacuity.lean`). You do
not need to run `AxiomProbe`, and you must not "fix" a gate failure by deleting
the assertion.

Three things the build does **not** check; run them by hand:

```
export PATH="$HOME/.elan/bin:$PATH"
lake build                                   # the sorry/axiom gate
export LEAN_PATH=$(lake env printenv LEAN_PATH)
lean probes/HonestyAuditProbe.lean           # ~5 s — the S5 evidence file
lean probes/CostChkIntentProbe.lean          # ~4 s — what `Cmd.chk` must accept/reject
lean probes/NonVacuityProbe.lean             # ~5 s — the decider actually runs
```

⚠ **Build-time gotcha:** a cold `lake build` is ~15 min and
`Reductions/S1Witness.lean` alone is **11 min** (the cost ladder's
`decide +kernel`). Anything at or above `Lang/PolyTime.lean` in the import graph
pays it; `Reductions/FrontWitness.lean`, the sound tail and the probes do not.
For iteration use `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean <file>` on
the single file — seconds instead of minutes — and `lake build` only at the end.
⚠ `lean <file>` needs the *dependencies'* oleans to be current, so do one
`lake build` of the subtree below your edit first. **Start the first `lake build`
of a session as a background job**; the warm-cache case is ~10 s but you cannot
tell in advance.

### Probe regression list — cheap, and still worth running

* **`probes/HonestyAuditProbe.lean`** — after any change to a witness's
  `encodeIn`/`decodeOut`, to `comp`/`SeamData`, or to `toFrameworkWitness'`. §6
  and §7b are negative controls and are *supposed* to typecheck. §7 is a
  negative control that **died** — if you ever make §7 build again you have
  re-opened the hole, so read its comment before touching
  `InNPWitnessLangFreeSplit`.
* **`probes/NonVacuityProbe.lean`** — after any change to
  `Complexity/NonVacuity.lean`, to `certState`, to `Cmd.eval`/`Op.eval`, or to
  `InNPWitnessStr`. Keep every `#eval` there at inputs of length `≤ 6`: the
  search is exponential on purpose.
* `probes/CostChkIntentProbe.lean` — after **any** change to `Lang/CostGrow.lean`.
  It pins the shapes `Cmd.chk` must reject (the squaring loop) and must accept
  (drained cursor, counter accumulator, flow-sensitive `concat`, `certDecode`).
* `probes/AxiomProbe.lean` — the *reporting* instrument, not a gate: use it when
  you want to see an endpoint's axiom list. Keep it in sync with
  `Complexity/SoundnessGate.lean`.
* `probes/SATSplitProbe.lean` (4 s) — after any change to `EvalCnfSplit`,
  `EvalCnfCmd.encodeState` or `evalCnfCmd`'s frame.
* `probes/C8FrontProbe.lean`, `probes/SeamS1Probe.lean` — after any change to
  the front program or a seam. `C8FrontProbe` §6 `#eval`s `tallyCells`, which is
  live in `frontProgram`.
* `probes/S1PreludeProbe.lean`, `probes/S1StepModelProbe.lean`,
  `probes/S1StepEmitProbe.lean`, `probes/S1CardModelProbe.lean`,
  `probes/S1GrowSafeProbe.lean` — after any register-frame, model or cost touch.
  ⚠ `probes/S1PreludeEmitProbe.lean` takes ~6 min and `probes/S1StepLoopProbe.lean`
  ~3 min (the emitter appends cell by cell, so interpreting it is quadratic —
  keep every new probe instance at `σ ≤ 1`).

**Recommendation: run a BOTTOM-UP session next**, on `SATStr` (bottom-up item 2)
rather than `FlatClique`. Reasoning: it is the only bottom-up item with a *live
top-down consumer* — it converts the weakest part of this session's result
("the class is inhabited, by a language in P") into the strongest form available
("the class contains an NP-complete language, and the headline reduces it to
SAT"). `FlatClique` membership is well-templated and will still be there;
top-down item 1 is a two-session build that nothing else is waiting on.


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
- **NP witnesses**: `InNPWitnessLangFree`/`inNPLangFree` (+ `inNPLangFree_to_inNP`);
  hardness is quantified over `InNPWitnessLangFreeSplit` (`NPhard''`), and — for
  the statement we publish — over `InNPWitnessStr` (`NPhardStr`,
  `Lang/HardnessStr.lean`), which is the same thing with the input layout pinned
  to `certState`. **Quote `CookLevinStr`; see standing risk 6.**
- **Serialization at a chain END**: `Lang/Serialize.lean` — one instance per
  concrete type, `dec_enc` + bit-level + the size sandwich. Live:
  `Serialize cnf` (`Deciders/CnfSerialize.lean`), which the tail's `decodeOut`
  is defined from. A new chain end owes an instance, not a hand-written
  inverse.
- **Reductions**: free `PolyTimeComputableLang` → `toFrameworkWitness'`/
  `reducesPolyMO'_of_langFree`; verifier precomposition via
  `DecidesLang.FreePrecomposeData`/`red_inNP_of_langFree`; **witness-witness
  composition via `SeamData`/`comp` — LIVE FIVE TIMES**
  (`FlatTCCBinComp.flatTCC_to_binaryCC_seam` →
  `BinaryCCFSATComp.binaryCC_to_FSAT_seam` → `FSATSATComp.fsat_to_SAT_seam` →
  `S1SATComp.s1_to_SAT_seam` → `FrontS1Comp.front_to_SAT_seam`).
  Four seam shapes exist; pick the one that matches:
  - **wider right frame** → length argument (`BinaryCC_to_FSAT_comp.lean`);
  - **narrower right frame** → no scrub above it (`FSAT_to_SAT_comp.lean`);
  - **left is a composite** → stacked seam, unfold its `.c` with one `heval`
    and push the previous bridge through with `Cmd.eval_agree`
    (`BinaryCC_to_FSAT_comp.lean`);
  - **right is a composite** (preferred at the head of the chain — FINDING A)
    → nothing to unfold, just scrub to the composite's frame
    (`Front_to_S1_comp.lean`).
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
   `NPhardStr` statement. See NEXT-TOP-DOWN item 2 for the recipe.
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
   commit, a discharged instance** (`NonVacuity.squareWitness` is the one to
   copy) — and, if it is cheap, a proof that the class still has computational
   content.

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
| `Lang/HardnessStr.lean` | `InNPWitnessStr` / `inNPStr` / `NPhardStr` / `NPcompleteStr`, the two bridges from `NPhard''`, and the canonical-layout size sandwich (`State.size_certState`, `size_le_two_mul_length`, `length_le_size`, `canonical_sizeLB`). **Read this one too.** |
| `Complexity/NonVacuity.lean` | non-vacuity, both directions (2026-08-03): `bitStringsUpTo` + `mem_bitStringsUpTo` + `bitStringsUpTo_length`; `searchDecide`/`searchDecide_correct`/`searchDecide_calls`; the `SquareStr` inhabitant (`squareCmd`, `squareVerifier`, `squareCertRel`, `squareWitness`, `inNPStr_squareStr`) and `squareStr_reducesPolyMO'_SAT`. |
| `Meta/AxiomGate.lean`, `SoundnessGate.lean`, `HonestyGate.lean`, `CostFaithfulness.lean` | the four build-time gates. Add to them; never delete an assertion to make a build pass. |
| `Lang/Serialize.lean` + `Deciders/CnfSerialize.lean` | the chain-end serialization discipline and the one live instance (`Serialize cnf`, fuel-based parser, `dec_enc`, both size laws). A new chain end owes an **instance**, not a hand-written inverse. |

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
