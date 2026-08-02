# `probes/` — the evidence files, and which of them are still evidence

**Read this before opening anything in this directory.** There are 48 files
here, written across four months, and they are not all the same kind of thing.
Some are live regression gates. Some are the *negative controls* that make the
build's positive gates worth something. Most are the archaeology of a design
session: a go/no-go check run *before* the code existed, kept for the reasoning,
with nothing left to re-run. Until this index existed a reader had no way to
tell which was which — so the evidence that is here did not reach them.

## What a probe is, and what it is not

This project's method is **probe before you prove**: write the invariant as a
`Bool` function, `#eval` it on real instances (including the corners a
"realistic" instance never reaches), and only then spend a session on the proof.
It has repeatedly been the cheapest de-risking move available — see FINDING AI
in [`../CookLevin/HANDOFF.md`](../CookLevin/HANDOFF.md), where an `#eval`-ed loop
invariant was consumed verbatim by an ~110-line proof with zero redesign.

⚠ **Probes are not part of `lake build`, and no claim of this development rests
on one.** The soundness, honesty, cost-faithfulness, non-vacuity and
statement-surface gates all run *inside* the build (`CookLevin/Complexity/`:
`SoundnessGate`, `HonestyGate`, `CostFaithfulness`, `NonVacuity`,
`StatementGate`, `StatementMeaning`). What lives here is what a `Prop` cannot say: that a program
does the right thing on a concrete input, that a *rejected* design really is
rejected, and that a gate that always passed would still fail if it should.

## Running them

```
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_PATH=$(lake env printenv LEAN_PATH)
lean probes/HonestyAuditProbe.lean
```

Every probe elaborates standalone against the built `.olean`s, so `lake build`
must be current first. Most print `true` on every line; the exceptions are
called out per file below, and **an expected `false` is always a negative
control** — read the surrounding comment before "fixing" it.

## The three kinds

| kind | meaning | what to do with it |
|---|---|---|
| **★ GATE** | pins something no build check can express — a negative control, or an intent pin. | **Run before you push** if you touched what it names. |
| **REGRESSION** | imports the real definitions and checks them numerically. Breaks if the module it names breaks. | Run after touching that module. |
| **ARCHAEOLOGY** | a go/no-go from a scoping session; the design it probed is settled (or was rejected). | Read for the reasoning. Nothing to re-run. |

A quick tell for the last one: **five files import nothing at all**
(`CliqueLtProbe`, `CliqueRelProbe`, `ConcatScratchProbe`, `UnaryMigrationProbe`,
`UnaryProductSizeProbe`). They are paper models of a design, so they cannot
regress against the code — by construction they are archaeology.

## The short list — run these before you push

```
lean probes/HonestyAuditProbe.lean       # the S5 negative controls
lean probes/CostChkIntentProbe.lean      # what `Cmd.chk` must accept and reject
lean probes/NonVacuityProbe.lean         # the brute-force decider actually runs
lean probes/SATToSATStrProbe.lean        # §1 = the FINDING AT negative control
lean probes/StatementSurfaceProbe.lean   # the surface gate can still fail
```

Under a minute in total. Everything else is conditional on what you touched.

## ★ Gates

| file | what it pins | runtime | re-run after |
|---|---|---|---|
| `HonestyAuditProbe.lean` | Risk S5, machine-checked. §6 is a complete, `sorry`-free witness that satisfies **every** field while its program computes nothing — the dishonest instantiation the structures do not exclude. §7 is the hypothesis-side cheat that **died** on 2026-08-02, kept with the proof that it is now unbuildable: *if you ever make §7 elaborate again you have re-opened the hole*. §7b is the one that survives every law about `encX`, which is why the published headline quantifies over `NPhardStr` instead. **§7c (2026-08-07) is the corollary that forced `NPcompleteStr'` into existence**: `inNPLangFreeSplit Q` for an *arbitrary* `Q : List Bool → Prop`, i.e. the membership conjunct of `NPcompleteStr` is satisfied by every string language and therefore claims nothing (FINDING AX). §8 pins the composite's encode to `certState x` by `rfl`. | 3 s | any change to a witness's `encodeIn`/`decodeOut`, to `comp`/`SeamData`, or to `toFrameworkWitness'` |
| `CostChkIntentProbe.lean` | `Cmd.chk_sound` proves acceptance implies `Cmd.CapCost`, so the checker can never become *unsound* without a proof breaking. It can silently become **useless** — accept nothing — or lose a shape it must reject. This pins both directions: the squaring loop `forBnd cnt bnd (concat dst dst dst)` must be **rejected** (no polynomial bound exists for it), and the drained cursor, the counter accumulator, the flow-sensitive `concat` and `certDecode` must be **accepted**. | 3 s | **any** change to `Lang/CostGrow.lean` |
| `NonVacuityProbe.lean` | `Complexity/NonVacuity.lean` *proves* every inhabitant of `inNPStr` is decidable by brute-force search over its own verifier. This *runs* that search, so the theorem is not about a function that diverges. ⚠ Keep every `#eval` at inputs of length ≤ 6 — the search is exponential on purpose. | 4 s | any change to `NonVacuity.lean`, `certState`, `Cmd.eval`/`Op.eval`, or `InNPWitnessStr` |
| `SATToSATStrProbe.lean` | §1 is the negative control for **FINDING AT**: it prints `true` for the fact that the *identity* form of `Serialize`'s no-compression law (`encodable.size x ≤ (enc x).length`) is **unsatisfiable** for `List Bool` under the canonical one-cell-per-bit layout — which is why the law is now `size x ≤ sizeLB ∣enc x∣`. §3's third line prints `([0], [1], false)`, the control showing `strBits_boolsOf` really needs its bit hypothesis. §6 prints `(true, false)`; every other line prints `true`. | 4 s | any change to `Lang/Serialize.lean`, `Lang/SerializeStr.lean`, `Reductions/SAT_to_SATStr_free.lean` or `_comp.lean` |
| `StatementSurfaceProbe.lean` | The negative controls for `Complexity/StatementGate.lean`: a definition in a statement is in the surface, one used only in a *proof* is not, the closure runs transitively through definition bodies, and **both** failure directions fire (a list that is incomplete, and a list that is stale). Every section must elaborate **silently** — `#guard_msgs` turns a wrong answer into an error, so no output is the pass condition. | 3 s | any change to `Complexity/Meta/StatementSurface.lean` |
| `AxiomProbe.lean` | *Not a gate* — the **reporting** instrument. `Complexity/SoundnessGate.lean` is the gate and runs in the build; this file prints each endpoint's axiom list, which is what you want when investigating a regression rather than detecting one. Keep the two lists in sync. | 3 s | adding an endpoint to `SoundnessGate.lean` |

## Regression probes

Each imports the real definitions — no local copies — so it fails if the module
it names changes behaviour.

| file | what it checks | runtime | re-run after |
|---|---|---|---|
| `SATStrProbe.lean` | SAT as a string language, exhaustively: the well-formedness grammar at every word of length ≤ 8, the builder's bridge at ≤ 7, machine-vs-model at ≤ 6, and `scanBody_run`'s loop invariant at **every** index. One line prints `[false, false, false, false]` (the negative controls for the `pending` bit) and one prints a cost pair; the rest print `true`. ⚠ The shortest bad word for the naive three-state CNF scanner is found here at length 3 — see §2. | 5 s | `Deciders/CnfWellFormed.lean`, `Deciders/SATStr.lean`, `EvalCnfCmd.encodeCnf`, `EvalCnfSplit.certDecode` |
| `SATSplitProbe.lean` | The membership half's split layout: 9 checks including `decodeBody`'s loop invariant at every prefix length, garbage / short / over-long certificates, and end-to-end acceptance. §5 is the invariant the `certDecode_decodesAssgn` proof consumed verbatim. | 3 s | `EvalCnfSplit`, `EvalCnfCmd.encodeState`, `evalCnfCmd`'s frame |
| `SeamS1Probe.lean` | The fourth (S1 → tail) and fifth (front → S1) seams. §1 asserts both scrub **erase sets exactly**, pinned to `s1RegBound = 48` and `headRegBound = 5`; the C8-5 bridge is checked end to end over the full 57-register frame, with a negative control. | 2 s | any seam, `s1RegBound`, `headRegBound`, or the tail composite's `57` |
| `SATSeamProbe.lean` | The third seam (`FSAT → SAT`) end to end. | 3 s | `Reductions/FSAT_to_SAT_comp.lean` |
| `FSATSeamProbe.lean` | The second seam (`BinaryCC → FSAT`), the stacked-seam shape. | 3 s | `Reductions/BinaryCC_to_FSAT_comp.lean` |
| `C8FrontProbe.lean` | The front `Cmd` pieces against their pure models. §6 `#eval`s `tallyCells`, which is **live in `frontProgram`** — this is the one C8 probe that guards running code. | 3 s | `Reductions/FrontPieces.lean`, `FrontProgram.lean` |
| `C8ProgramProbe.lean` | The front program emits exactly the frozen `HeadLayout.headEncodeIn` layout on registers 0–4. | 3 s | `FrontProgram.lean`, `HeadLayout.lean` |
| `S1ProgramProbe.lean` | The assembled S1 program's two branches, and — the reason it exists — the **contracts** `stageC_run`/`stageMYes_run` themselves: a contract can be stated wrongly and still let the assembly typecheck. | 4 s | `Reductions/S1Program.lean` |
| `S1StepLoopProbe.lean` | Stage C end to end, and the **full equality** of its output with `encNats (cardBlocks M)` (§1) — not a prefix. The first end-to-end `#eval` of `s1Program`. ⚠ Slow: the emitter appends cell by cell, so interpreting it is quadratic. Keep every new instance at `σ ≤ 1`. | 21 s | `S1StepLoop.lean`, `S1Program.stageC` |
| `S1PreludeEmitProbe.lean` | Stage C's prelude family (~96% of the card register) as a real `Cmd`, and §3's numeric check that its register set sits inside the licence. ⚠ The slowest file here. | **402 s** | `S1PreludeEmit.lean` |
| `S1StepEmitProbe.lean` | The `stepBlocks` entry body. §2 **measures** the entry body's write set as exactly `SD1 ∪ {EOUT_C}` — the frame claim the proofs rely on. | 7 s | `S1StepEmit.lean` |
| `S1PreludeProbe.lean` | The prelude family's model shape, preamble and budget. | 22 s | `S1Prelude.lean` |
| `S1CardEmitProbe.lean` | Stage M-yes end to end, and the five `cFive` families as a prefix of the card target. §1 is **superseded as a gate** by `S1StepLoopProbe` §1 (which asserts the full equality) but is retained: a failure here says *which family* moved. | 34 s | `S1CardEmit.lean`, `S1Program.stageMYes` |
| `S1CardModelProbe.lean` | The pure `cardBlocks` model against the `Fin`-typed `guessCards`. | 5 s | `S1Cards.lean` |
| `S1StepModelProbe.lean` | The emitter-shaped `stepBlocks` model, swept over the whole parameter cube **including** the corners (`σ = 0`, all three `mv`, out-of-range `mVal`/`wVal`). | 2 s | `S1StepModel.lean` |
| `S1EmitProbe.lean` | Emitter stages Σ, I, F against the output key. Also exhibits the **off-guard instance** where stage I and `preludeRow` disagree — which is why the guard is load-bearing for stage I and not for P/G/F. | 3 s | `S1Emit.lean` |
| `S1ParseProbe.lean` | Stages P (parse) and G (guard), and the measured **cost scale** — cubic, which is what established that the parse is not the S1 budget driver. | 5 s | `S1Parse.lean` |
| `S1GrowSafeProbe.lean` | `Cmd.chk` accepts the whole real S1 program (~2 s by `#eval`, ~3 min by `decide +kernel`). | 4 s | `Lang/CostGrow.lean`, `S1Program.lean` |
| `S1SizeGapProbe.lean` | The head-layout size honesty gap and the constants that close it. §3 is the counterexample that killed `sizeFlatTM` and established the locked invariant *a fixed-size header forces an additive term* — a probe over "realistic" instances prints `true` and hides it. | 3 s | `encodable FlatTM`, `HeadLayout`, `S1Witness.flattenTM_size_le` |
| `S1TableauProbe.lean` | The v2 card algebra against real runs: every 3-window of consecutive rows is licensed, halting rows freeze, and **skipping a row is not licensed** (negative control). §5 is the machine-checked phantom-head completeness hole — the reason `confRow` carries a right boundary marker. | 4 s | `Simulators/CookTableau.lean`, `GuessTableau.lean` |
| `SizeBoundProbe.lean` | The two tableau size bounds `≤ (2·(b+1))^10` on small machines, and why the **enlarged base is not optional** (a `C·b^d` collapse overshoots a tight `n^10` at small `n`). No doc header — this table row is it. | 3 s | `CookTableau.lean`, `GuessTableau.lean`, either size bound |

## Archaeology — read, do not re-run

The design each of these scoped is settled. They still elaborate (that is
checked), but nothing downstream depends on them and a green run proves nothing
new. They are here because the *reasoning* is worth more than the check.

| file | the question it settled | runtime |
|---|---|---|
| `UnaryProductSizeProbe.lean` | ★ **A standing negative result, not just history.** The generic product encoding of the canonical `LangEncodable` layer is **size-unsound**: it violates `enc_size`. This is the evidence that the layer must stay dead — do not rebuild it. | 0 s |
| `UnaryMigrationProbe.lean` | The bit-level unary migration (`takeAt`/`dropAt`/`consLen`) round-trips and stays `BitState`. Superseded in part by the file above, which found what it missed. | 0 s |
| `C8SeamProbe.lean` | Can the per-`Q` front witness target the chain head's fixed layout? (Yes — became C8-5.) | 3 s |
| `C8GadgetsProbe.lean` | The accept-by-halting wrapper and the tape-format check (C8-2). | 3 s |
| `C8MachineProbe.lean` | The front machine `M_Q` end to end on a real compiled verifier, yes/no/garbage (C8-4). | 3 s |
| `FSATPreProbe.lean` | Go/no-go for positional-index Tseytin with no stack — the answer that made `FSAT → SAT` a single forward token scan. | 2 s |
| `FSATSerProbe.lean` | Go/no-go for the ~1K-line Tseytin builder as a free `PolyTimeComputableLang` witness. | 3 s |
| `FlatCCBinProbe.lean` | Go/no-go for `FlatCC → BinaryCC`, and the finding that the `isValidFlattening` **guard is required** — the unguarded map is provably not correct for this step. | 3 s |
| `FlatTCCConvertProbe.lean` | Go/no-go for `FlatTCC → FlatCC` as an unguarded structural map. | 3 s |
| `KCnf3ReencoderProbe.lean` | Go/no-go for the first `FreePrecomposeData` re-encoder (`kSAT 3` over the SAT verifier's layout). | 3 s |
| `CliqueRelProbe.lean` | The FlatClique verifier design, before proof engineering. Still the template if bottom-up item 1 (`FlatClique` membership) is picked up. | 0 s |
| `CliqueLtProbe.lean` | The unary `<` gadget `CliqueRel` needs and `EvalCnf` never built. | 0 s |
| `CursorCopyProbe.lean` | The in-place marking/cursor-read design for the `copy`/`tail` op gadgets. | 5 s |
| `ConcatScratchProbe.lean` | The `concat dst src1 src2` register/residue arithmetic. | 0 s |
| `ForBndSkeletonProbe.lean` | `compileForBnd`'s bookkeeping, including bodies that clobber `bound` and `counter` (the snapshot-vs-clobber gap). | 0 s |
| `GrowEmptyProbe.lean` | The residue-tolerant grow scratch-lifecycle gadget — a *paper* model over an abstract machine, so it names no live constant and its green run proves nothing about the code. | 3 s |
| `CopyEmptyProbe.lean` | The tight copy-into-empty gadget (dropping the clear phase, which alone cost ≈18L²). | 3 s |
| `EqBitProbe.lean` | The `eqBit` op-gadget design. | 1 s |
| `EqBitNoGrowProbe.lean` | ★ **Resolution B**, the design that shipped: a static scratch base `sb` threaded into `compileOp`, with pre-existing padded scratch — *no* grow/shrink. This is the file that records why design (A) was abandoned. | 4 s |
| `CompareBodyProbe.lean` / `CompareRegsBudgetProbe.lean` | The design-(A) consume loop and its budget. Design (A) was later found un-instantiable (see the row above); these two survive only because they do not name the deleted constants. | 4 s each |

## Measured 2026-08-06 — three files deleted, and one stale number corrected

Every file in this directory was run and timed to build this index. That had not
been done before, and it found two things the index would otherwise have
misrepresented.

**Three probes no longer elaborated**, and all three were **removed** rather
than repaired:

| file | errors | why it died |
|---|---|---|
| `EqBitBudgetProbe.lean` | 30 | named `Compile.compareRegsTM` |
| `CompareRegsAssemblyProbe.lean` | 13 | named `Compile.growTwoEmptyM` / `shrinkTwoEmptyM` |
| `ShrinkEmptyProbe.lean` | 20 | named `Compile.shrinkEmptyTM` |

All three constants belong to the design-(A) `eqBit` scratch-lifecycle stack,
deleted when Resolution B shipped on 2026-06-21b. They probed a design this
project **explicitly rejected**; the rejection is recorded in a file that still
runs (`EqBitNoGrowProbe.lean`), and git history keeps them
(`git show 39f491c:probes/EqBitBudgetProbe.lean`).

The general rule this suggests, for whoever adds the next probe: **a probe file
that does not elaborate is worse than no probe file.** It reads as evidence and
is not. If a scoping probe outlives the API it was written against, delete it
and keep the finding in prose — that is what `HANDOFF.md`'s findings list is
for. ⚠ And note `GrowEmptyProbe.lean`, which passed: it survived only because it
models an *abstract* machine and names no live constant. A green run there means
nothing about the code either. Passing is not the same as being evidence.

**One runtime in the plan of record was badly stale.** `S1StepLoopProbe.lean`
was documented as "~3 min"; it is **21 s**. The only genuinely slow file here is
`S1PreludeEmitProbe.lean` at **402 s** — everything else in this directory runs
in under 35 s, and the whole suite is about 10 minutes end to end. Iterating on
the S1 stack is therefore much cheaper than the handoff implied.

## Adding a probe

* Put a `/-!` header at the top saying **what it pins** and **when to re-run
  it** — this index is generated by reading those headers, and one file
  (`SizeBoundProbe.lean`) has none, which is why its row had to be written by
  hand.
* State the expected output. "Every line prints `true`" is the norm; anything
  else needs a comment saying why, *at the line*.
* If it is a **negative control**, say so loudly and say what re-opening looks
  like — `HonestyAuditProbe.lean` §7 is the model ("if you ever make this
  elaborate again you have re-opened the hole").
* Prefer a **positive** pin inside the build (`Complexity/HonestyGate.lean`,
  `Complexity/StatementGate.lean`) over a probe. A probe is for what the build
  cannot say.
* Then add a row here, in the right one of the three tables.
