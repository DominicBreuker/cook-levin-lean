# Cook–Levin in Lean 4

A Lean 4 formalisation targeting the **Cook–Levin theorem** (SAT is
NP-complete), structured as a port of the Coq development by Forster, Kunze,
Roth et al. (<https://github.com/uds-psl/cook-levin>, mirrored under `coqdoc/`).

**The theorem is proven, on the honest statement, unconditionally
(2026-07-30-b), audited (2026-07-30-c), stated in a form with no dishonest
instantiation (2026-08-01), and — since 2026-08-02 — `lake build` itself
*proves* there are no `sorry`s and no bespoke axioms anywhere in the library.**

```
CookLevinHonest.CookLevinStr : NPcompleteStr SAT   -- ★ the statement to quote
CookLevinHonest.CookLevin''  : NPcomplete''  SAT   -- the general form it comes from
both depend on axioms: [propext, Classical.choice, Quot.sound]
```

### What a reviewer actually has to do

1. **`lake build`.** If it is green then two things are machine-checked, both
   at elaboration time, with no CI step and no `grep` involved:
   * every one of the ~12 350 declarations under `Complexity` is `sorry`-free
     and uses only `propext`, `Classical.choice` and `Quot.sound`
     (`#assert_library_axiom_clean` in `Complexity/Meta/AxiomGate.lean`, swept
     from `Complexity.lean`; endpoint-by-endpoint in
     `Complexity/SoundnessGate.lean`). `sorry` is only a *warning* in Lean, so a
     green build did not use to mean this;
   * the composite reduction's `encodeIn` and `decodeOut` — the **only two
     functions** encoding honesty depends on (FINDING AK) — are the ones the
     audit says they are, including `encodeIn x = certState x` under `NPhardStr`
     (`Complexity/HonestyGate.lean`).
2. **Read three definitions**, and nothing else, to know the theorem is about
   Cook–Levin and not about something else:
   * `NPcompleteStr` / `NPhardStr` / `InNPWitnessStr` (`Complexity/Lang/HardnessStr.lean`)
     — what is being claimed, and over which hypothesis;
   * `SAT` (`Complexity/NP/SAT.lean`) — that it means satisfiability;
   * `FlatTM` / `stepFlatTM` (`Complexity/Complexity/MachineSemantics.lean`) —
     that the machine model is a Turing machine.
   * `Serialize cnf` (`Complexity/Complexity/Deciders/CnfSerialize.lean`) — the
     one encoding at a chain end that is ours to choose.

   Two things have come *off* that list. The head-side encoding
   (2026-08-02): the composite reduction's `ComputesBy.encode` is now literally
   `certState x`, the raw input string, pinned by the honesty gate. And
   **`Op.cost`**: every "polynomial time" claim here is a bound on the *layer's*
   cost, not on `stepFlatTM` steps, so a reviewer used to have to trust that the
   cost model does not undercharge — but that is proven, and
   `Complexity/CostFaithfulness.lean` now says it in one gated theorem
   (`Compile.cost_is_time_proxy`): **one** fixed polynomial bounds the running
   time of **both** compiled machines — the reduction machine and the decider
   machine — in `State.size s + c.cost s + regBound + loopDepth`, and in both
   cases the machine really halts, on the program's real output. (The converse —
   that the cost model does not *overcharge* — is deliberately not proven; it
   could only make our own obligations harder, never a proven bound weaker.)

`NPcompleteStr SAT = NPhardStr SAT ∧ inNPLangFreeSplit SAT`: every NP **string
language** — a `Q : List Bool → Prop` presented with a real `Cmd` verifier
reading the *raw string* in the canonical one-register layout — reduces to SAT
by a real `Cmd`-backed poly-time reduction, and SAT itself is verified by a real
`Cmd` program against a `List Bool` certificate inside a real polynomial cost
bound. Both halves are `sorry`-free and axiom-clean.

`NPcomplete''` is the same theorem over an *abstract* input type whose layout
the hypothesis supplies. It is logically stronger and it is what the machinery
proves — but that free layout is exactly where a dishonest reading gets in (see
the caveat below), which is why the headline is the string form.

**What changed on 2026-08-02** (top-down; enforcement):

* **The honesty pins are a typechecking obligation.**
  `Complexity/HonestyGate.lean` states, as gated `rfl` theorems inside the
  library, what the composite's two audited functions are — so a refactor of
  `PolyTimeComputableLang.comp`, of `toFrameworkWitness'`, or of a chain end's
  layout breaks the build instead of silently falsifying this file. The
  *negative* controls stay in `probes/HonestyAuditProbe.lean`, deliberately:
  they are constructions that are supposed to typecheck.
* **Axiom hygiene is a typechecking obligation.** `#assert_axioms_clean` and
  `#assert_library_axiom_clean` (`Complexity/Meta/AxiomGate.lean`) fail
  elaboration on any dependence outside `{propext, Classical.choice,
  Quot.sound}`. `Lean.collectAxioms` walks a constant's *statement* as well as
  its proof, so this also catches a `sorry` hidden inside a `def` — the failure
  mode `#print axioms` exists here to detect and that no `grep` sees through an
  import. `probes/AxiomProbe.lean` stays as the *reporting* instrument.
* **The reduction's input encoding is the input.** `W_Q.encodeIn x` was
  `W.encX x ++ [1^(encodable.size x)]`; it is now `W.encX x`. The front program
  counts its own input's cells (`FrontPieces.tallyCells`, built in July and
  unused until now), licensed by a new **no-compression** field on the
  hypothesis: `sizeLB` with `encodable.size x ≤ sizeLB (State.size (encX x))`.
* **That field killed the §7 cheat, and the probe proves it.**
  `HonestyAuditProbe` §7 — a complete, `sorry`-free split witness presenting an
  *arbitrary* predicate with the answer planted in its input — no longer
  typechecks. §7 now carries `badSplitWitnessOf` (every other field still
  discharged, so the obstruction is exactly `sizeLB`) and `badEncX_no_sizeLB`
  (no such `sizeLB` exists over `Nat`). ⚠ §7b still typechecks, as FINDING AO
  predicted: it satisfies `sizeLB` by writing the input out and *appending* the
  answer. **No law about `encX` closes the hypothesis side — only `NPhardStr`
  does.**

**What changed on 2026-08-01** (top-down; the honesty layer):

* **The tail decoder is a real parser.** `FSATSATFree.decodeOut` — one of the
  two functions the whole audit rests on — is now `Serialize.dec` of one
  register (`Complexity/Lang/Serialize.lean`, instance in
  `Deciders/CnfSerialize.lean`: a fuel-based parser for `encodeCnf` with
  `dec_enc` proven, no `Classical`). It used to be `Function.invFun encodeCnf`,
  whose behaviour off the image was unconstrained.
* **The honesty hole was on the *hypothesis* side, and it was bigger than
  believed.** `NPhard''` lets the instantiator supply `encX`, the input layout
  the composite reduction is built on. `probes/HonestyAuditProbe.lean` §7 is a
  complete, `sorry`-free split verifier witness for an **arbitrary** predicate —
  undecidable ones included — with the answer planted in its input; it yields
  `Q ⪯p' SAT`, axiom-clean. §7b shows no law *about* `encX` can rule this out
  (append the answer to an otherwise perfect encoding).
* **The fix is a restriction, not a class.** `NPhardStr` quantifies over string
  languages with the canonical layout, where `encX` is not a field at all.
  `CookLevinStr` follows from `CookLevin''` in one line, and the composite's
  input encoding becomes a closed formula pinned by `rfl`
  (`HonestyAuditProbe` §8).

**What changed on 2026-07-30-c** (the top-down audit-and-demolition session):

* **The encoding-honesty audit was done end to end** — the last thing that could
  have made the theorem mean less than it says. Verdict: **it means what it
  says** — ⚠ *with one exception found 2026-08-01: that session's verdict 12,
  on the hypothesis side of `NPhard''`, was wrong; see below.* Per-witness
  verdicts are in the ROADMAP risk register (**S5**);
  the evidence is `probes/HonestyAuditProbe.lean`. The audit's structural
  result is what made it finite: for a witness built by
  `PolyTimeComputableLang.comp`, the honesty surface is **two functions** — the
  leftmost `encodeIn` and the rightmost `decodeOut` — because every intermediate
  layout appears only on the *right* of a seam's bridge obligation, i.e. the
  composed program is *required to produce it*.
* **The legacy `⪯p` front was deleted, not proved.** `CookLevin : NPcomplete SAT`,
  `NPhard_GenNP`/`hasDeciderClassical`, the two dummy S2 bridges, the
  if-on-the-answer S1 reduction, `MultiToSingle` and `red_inNP` are all gone.
  That removed the development's **last five `sorry`s**; `⪯p` bounds only
  *output size*, so `NPcomplete` was a vacuous notion and there is deliberately
  **no** `NPcomplete'' → NPcomplete` bridge. See
  `CookLevin/Complexity/NP/SAT/CookLevin.lean` for the demolition table.

⚠ **What is still not enforced.** Encoding honesty for *intermediate* witnesses
remains per-witness discipline (`HonestyAuditProbe` §6 is the counterexample) —
though by the audit's structural result those layouts cannot license a cheat,
only make a seam bridge harder. The chain's two *ends* are now pinned: the tail
by `Serialize cnf`, the head by the `NPhardStr` statement **and** by
`encodeIn = encX` (2026-08-02). What no formalisation
removes is the definitional trust at the statement: is `FlatTM`/`stepFlatTM` a
faithful Turing machine, is `Serialize cnf` a faithful CNF encoding beyond
`dec_enc`, does `SAT` mean satisfiability. (⚠ "is `Op.cost` a faithful proxy for
time" used to be on this list — this project found one real bug of that kind —
and came **off** it on 2026-08-02: `Compile.cost_is_time_proxy`,
`Complexity/CostFaithfulness.lean`, gated.) See ROADMAP risk **S5**,
verdicts 1–14.

Read [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md) for the full risk register
and [`CookLevin/HANDOFF.md`](CookLevin/HANDOFF.md) for the working plan before
working.

## Honest status (verified 2026-07-30-c)

| | |
|---|---|
| `lake build` | ✅ green — **and it is the gate**: `#assert_library_axiom_clean Complexity` (bottom of `Complexity.lean`) fails elaboration unless all 12354 declarations in all 97 modules are `sorry`-free and axiom-clean; `Complexity/SoundnessGate.lean` does the same endpoint by endpoint, and `Complexity/HonestyGate.lean` pins the two audited functions. Runs in ~2 s. |
| **`#print axioms CookLevinHonest.CookLevinStr`** | **`[propext, Classical.choice, Quot.sound]`** — ★ **`NPcompleteStr SAT`** (2026-08-01): hardness over NP **string languages** with the canonical one-register layout `certState`, so the hypothesis carries **no free input encoder**. Derived from `CookLevin''` in one line (`NPcomplete''_to_NPcompleteStr`, `Complexity/Lang/HardnessStr.lean`). **This is the statement to quote.** |
| **`#print axioms CookLevinHonest.CookLevin''`** | **`[propext, Classical.choice, Quot.sound]`** — ★ **`NPcomplete'' SAT`, UNCONDITIONAL** (2026-07-30-b). Hardness (`FrontS1Comp.SAT_NPhard''`, 2026-07-29-b) and membership (`EvalCnfSplit.SAT_inNPLangFreeSplit`, 2026-07-30-b) are both closed. **This is the theorem this development proves.** |
| **the encoding-honesty audit (ROADMAP risk S5)** | ⚠ **audited 2026-07-30-c; PARTLY STRUCTURAL 2026-08-01; head side CLOSED 2026-08-02** — the composite's `encodeIn` is now `W.encX` verbatim, i.e. `certState x` under `NPhardStr`, so there is no head-side encoding of ours left to read.<br> The 2026-07-30-c audit's structural result stands: the honesty surface of a `comp`-built witness is the **leftmost `encodeIn`** and the **rightmost `decodeOut`**, and nothing else. Since 2026-08-01 the tail one is pinned by `Serialize cnf` and the head one by the `NPhardStr` statement. ⚠ verdict 12 (the hypothesis side of `NPhard''`) was **corrected to ❌** — `probes/HonestyAuditProbe.lean` §7/§7b — and superseded by verdict 13. Evidence `probes/HonestyAuditProbe.lean` §§1–8; verdicts 1–14 in the ROADMAP register. |
| ~~`#print axioms CookLevin`~~ | **DELETED 2026-07-30-c** together with the whole legacy `⪯p` front — it was the only remaining `sorryAx` anywhere, and it was never a statement about the mathematics. |
| `#print axioms SAT_inNP.sat_NP` | **`[propext, Classical.choice, Quot.sound]`** — the **in-NP half is sorry-free & axiom-clean** (2026-06-28, Route A). |
| `#print axioms FlatClique_in_NP` | **`[propext, Classical.choice, Quot.sound]`** — **FlatClique's in-NP half is sorry-free & axiom-clean** (2026-07-01; `cliqueRelDecidesLang` complete, `cost_bound` proven). |
| `#print axioms KSat3Free.inNP_kSAT3_free` | **`[propext, Classical.choice, Quot.sound]`** — the **first live `red_inNP` routed through the free layer engine** (`red_inNP_of_langFree` + a concrete re-encoder & reduction program, 2026-07-02). |
| `#print axioms KSat3Free.kSAT3_reducesPolyMO'` | **`[propext, Classical.choice, Quot.sound]`** — the **first live honest TM-backed reduction on the real chain** (`kSAT 3 ⪯p' SAT`, 2026-07-02). |
| `#print axioms FlatTCCFree.flatTCC_reducesPolyMO'` | **`[propext, Classical.choice, Quot.sound]`** — the **first sound-tail chain step as a live honest TM-backed reduction** (`FlatTCC ⪯p' FlatCC` via the unguarded structural map, 2026-07-02). |
| `#print axioms FlatCCBinFree.flatCC_reducesPolyMO'` | **`[propext, Classical.choice, Quot.sound]`** — **`FlatCC ⪯p' BinaryCC`** as a live honest TM-backed reduction (2026-07-03; guarded map with an **on-machine validity check** — the unguarded map is provably NOT correct for this step, see `Reductions/FlatCC_to_BinaryCC_free.lean`). |
| `#print axioms FlatTCCBinComp.flatTCC_to_binaryCC_reducesPolyMO'` | **`[propext, Classical.choice, Quot.sound]`** — **the first COMPOSED live `⪯p'`** (`FlatTCC ⪯p' BinaryCC`), produced by the **first live `SeamData`/`comp` instantiation** (2026-07-03) — the settled chain-composition engine validated on real witnesses. |
| `#print axioms BinaryCCFSATFree.binaryCC_reducesPolyMO'` | **`[propext, Classical.choice, Quot.sound]`** — **`BinaryCC ⪯p' FSAT`** as a live honest TM-backed reduction (2026-07-11; the expensive Tseytin/tableau step as a full free-line `PolyTimeComputableLang` witness — program `buildFSAT`, run stack, complete `cost_le` accounting, and mechanical fields; `Reductions/BinaryCC_to_FSAT_free.lean`). |
| `#print axioms BinaryCCFSATComp.flatTCC_to_FSAT_reducesPolyMO'` | **`[propext, Classical.choice, Quot.sound]`** — **`FlatTCC ⪯p' FSAT`** (2026-07-12): the whole sound-tail prefix `FlatTCC → FlatCC → BinaryCC → FSAT` as ONE composed live `⪯p'`, chained by the **second live `SeamData`/`comp`** (`Reductions/BinaryCC_to_FSAT_comp.lean` — a seam on a composed witness, wider right frame closed by a length argument). |
| `#print axioms FSATSATComp.flatTCC_to_SAT_reducesPolyMO'` | **`[propext, Classical.choice, Quot.sound]`** — **`FlatTCC ⪯p' SAT` — the WHOLE sound tail `FlatTCC → FlatCC → BinaryCC → FSAT → SAT` is ONE composed live `⪯p'`** (2026-07-16). The last step `FSAT ⪯p' SAT` (`FSATSATFree.fsatSAT_reducesPolyMO'`) is a full free-line witness — pre-order positional Tseytin over the Polish `serF` stream (`NP/FSAT_to_SAT_pre.lean`), program `buildSAT`, complete run ladder (`buildSAT_run`) and cost ladder (`buildSAT_cost_le`, `satBound = O(n⁸)`), all mechanical fields (`Reductions/FSAT_to_SAT_free.lean`) — chained by the **third live `SeamData`/`comp`** (`Reductions/FSAT_to_SAT_comp.lean`, probe `probes/SATSeamProbe.lean`). The tail is DONE and waits on the front (S1/C8) for the endpoint hardness bridge. |
| `NPhard'` endgame design | **SETTLED, machine-validated & now LIVE** (2026-07-02/03): `PolyTimeComputableLang.SeamData`/`comp` (Cmd-level chain composition, fully proven, first live seam `FlatTCCBinComp.flatTCC_to_binaryCC_seam`) + `NPhard'`/`NPcomplete'`; hardness is proven at chain endpoints only — see `CookLevin/HANDOFF.md`. |
| `axiom` declarations | **0** (project policy: `def`+`sorry` over `axiom`) |
| `#print axioms S1Map.s1Map_correct` | **`[propext, Classical.choice, Quot.sound]`** — the **S1 reduction map is correct** (2026-07-25): `FlatSingleTMGenNP x ↔ FlatTCCLang (s1Map x)` for the guarded map `s1Map`, with `s1Map_size_le` bounding its output. The *program* computing `s1Map` is the one remaining piece of the honest chain head (`Reductions/S1Witness.lean`, skeleton). |
| `#print axioms S1Cards.cardBlocks_eq` | **`[propext, Classical.choice, Quot.sound]`** — the **card emitter (stage C) is de-risked** (2026-07-25-c, `Reductions/S1Cards.lean`, sorry-free): `guessCards M`'s flat card stream = `cardBlocks M`, seven nested `List.range` streams over the parsed machine numbers, one proven equation per card family. Also `normModel_eq` (the `normTrans` dedup on-machine) and `stageMNo` (the multiplex's guard-false branch). |
| `#print axioms S1Parse.stagePG_run` | **`[propext, Quot.sound]`** — the **S1 program's first two stages are built** (2026-07-25-b, `Reductions/S1Parse.lean`): stage **P** parses the frozen head layout's machine register into a pinned scratch frame, stage **G** decides `S1Map.s1GuardB` on-machine; both sorry-free. Measured cost is **cubic** (`probes/S1ParseProbe.lean`), so the parse is not the S1 budget driver. |
| `#print axioms S1Emit.stageInit_run` | **`[propext, Classical.choice, Quot.sound]`** — **three more S1 program stages are built** (2026-07-26, `Reductions/S1Emit.lean`, sorry-free): the emitter atom `emitBlk` (one bare unary block, appended cell by cell — never `concat`) plus stage **Σ** (`1^(PSg M)`), stage **I** (the prelude row, `stageInit_run`) and stage **F** (the final patterns, `stageFin_run`), each with a pure `List.range` model proven equal to the `Fin`-typed definition (`initBlocks_eq`, `finBlocks_eq`). **Stage C (the card emitter) and stage M-yes are all that is left of the program.** Probe: `probes/S1EmitProbe.lean`. |
| `#print axioms S1Witness.flattenTM_size_le` | **`[propext, Classical.choice, Quot.sound]`** — `encodable.size (flattenTM M) ≤ 3·encodable.size M + 3` (2026-07-26). ⚠ Its previous statement (without the `+ 3`, annotated "the constant 3 has slack") was **FALSE** — `flattenTM` always writes six header cells, so the trivial machine has `size M = 1` and stream size `6`. See `probes/S1SizeGapProbe.lean` §3; the general rule (a fixed-size header forces an additive term) is now a locked invariant. |
| `#print axioms S1Program.noBranch_computes` | **`[propext, Quot.sound]`** — **the S1 reduction program is ASSEMBLED** (2026-07-26-b, `Reductions/S1Program.lean`): `s1Program = stagePG ;; ifBit FLG yesBranch stageMNo`, and its `computes` obligation is proven — the **guard-false half outright and axiom-clean** (this lemma, stated over an arbitrary yes branch so that the placeholder stages do not pollute its axiom list), the guard-true half (`yesBranch_run`) modulo only `stageC_run` and `stageMYes_run`. `S1Witness.s1_reductionLang` now discharges `computes`, `usesBelow` and `decode_agree` from real program lemmas; **`cost_le` is its only open field.** Probe: `probes/S1ProgramProbe.lean`. |
| `#print axioms S1CardEmit.cFive_run` | **`[propext, Classical.choice, Quot.sound]`** — **five of stage C's seven card families are BUILT** (2026-07-26-c, `Reductions/S1CardEmit.lean`, sorry-free): `copyBlocks`, `copyRightBlocks` and the three halt families as real `Cmd`s, plus the preamble `cPre` and the assembly `cFive`. Landed with them: the reusable emitter loop principle `emitLoop_run` (dirty set as a register **list**), the two-source block `emitBlk2`, the identity-card atom `emitId`, `loadX` and the shared gated `q` loop `haltFam`. Probe: `probes/S1CardEmitProbe.lean`. |
| `#print axioms S1Program.stageMYes_run` | **`[propext, Classical.choice, Quot.sound]`** — **stage M-yes is CLOSED** (2026-07-26-c): `EOUT_T := 1^(steps+1)` off register `4` *before* the five copies overwrite it, and `s1Extract (stageMYes.eval s) = s1Key (guessTableau …)`. `yesBranch_run` is now modulo `stageC_run` alone. Also proven there: `cFive_frame` / `cFive_preserves` — the built families' dirty set really does sit inside stage C's stated licence `CDirty`, and they preserve registers `1`–`5`, `PSIG`/`PSTATES`/`PHALT`/`PNTRANS`/`PTRANS` and `EOUT_S`/`EOUT_I`. |
| `#print axioms S1Prelude.preludeBlocks_seg` | **`[propext, Classical.choice, Quot.sound]`** — **stage C's prelude family (~96% of the card register) is emitter-shaped** (2026-07-27-b, `Reductions/S1Prelude.lean`, sorry-free): `preludeBlocks` re-stated as `preludeSeg`, the exact nesting the `Cmd` will implement. Four findings, each a theorem: the three *kind* loops are all outside the three *resolution* loops (an interleaved emitter emits a **permutation** — `encCardsIn` is order-sensitive); `resOf` needs **no pair-list register** (a kind is four numbers `(1^k, star?, base, add)`); `contigB`'s three class codes collapse to **one carried bit**; and the seven-segment split of the kind loop means stage C needs **no on-machine comparison gadget at all**. Landed with it: `emitList` (a run of `emitBlk2`s over a list of source pairs — `emitId` no longer serves once a family emits six *different* values), `minReg` (`1^(min a b)` by draining — needed for `min M.start M.states` and for `entryBlocks`' two state clamps), and `pPre`, the prelude preamble (`PConst`: `1^sgv`, `1^bv`, `1^5`, and the head band's base `1^((σ+1)(q0+1))` by one hoisted `unaryMulLoop`). ⚠ two measured findings: **stage C's register licence is exactly full** — `CDirty` licenses 30 registers and the prelude uses all 30, so `stepBlocks` must reuse the pool rather than claim new ones; and **the cost ladder has enormous slack** (everything built costs `6.3e4` against a budget of `9.8e16`), so it is a slack argument, not a tight one. Probe: `probes/S1PreludeProbe.lean`. |
| `#print axioms S1Prelude.cPrelude_run` | **`[propext, Classical.choice, Quot.sound]`** — **stage C's prelude family is BUILT** (2026-07-27-c, `Reductions/S1PreludeEmit.lean`, sorry-free): `cPrelude` is a real `Cmd` and `cPrelude_run` proves it lays `encNats (preludeBlocks σ states (min start states))` — ~96% of the card register — onto `EOUT_C` off nothing but the parse frame, with `cPrelude_usesBelow` (48) and `PDirty_cdirty` (its registers sit inside stage C's licence). Landed with it: the dirty-list-indexed emitter contract `Emits`/`EmitsFr` (`seq`/`mono` — the thing that makes a deep register-generic nest tractable), the register-generic gadgets `pRes`/`pSeg`/`pKindCmd`, each proven once and applied three times, and the value gadgets `setLit`/`loadSum`/`loadVal`/`setFlag`. ⚠ **A defect in the previously pinned register table was found and fixed**: `PJᵢ` cannot carry both the kind level's `add` and the resolution level's loop counter, because the resolution nest re-runs `49×` inside the kind levels and clobbers it between write and read (`preludeSeg'`/`preludeBlocks_seg'` are the re-coordinatised model). Measured: the real `cPrelude.cost` is `2.8e5 … 1.2e7` against an `S1Map.s1Bound` of `1.0e13` at `n = 7` — seven orders of magnitude of head-room on the family that dominates the whole program. Probe: `probes/S1PreludeEmitProbe.lean`. |
| `#print axioms S1Step.stepBlocks_seg` | **`[propext, Classical.choice, Quot.sound]`** — **stage C's last family is DE-RISKED** (2026-07-27-c, `Reductions/S1StepModel.lean`, sorry-free): `stepBlocks` re-stated in the emitter's own nesting, plus `stepSummand_seg` (the whole `(normTrans M).flatMap (entryBlocks M)` summand). Three findings: every branch in `stepBlocks` that reads a loop counter is a *last-iteration* test, so the range splits `range (n+1) = range n ++ [n]` and `range (σ+2) = [0] ++ (range σ).map (·+1) ++ [σ+1]` make each one a compile-time constant — **stage C as a whole needs no unary comparison gadget**; an entry contributes exactly three symbol constants (`rOf`, `wOf …false`, `wOf …true`), all hoistable; and `mv` is entry-constant, so one three-way `ifBit` chain wraps the body. Probe: `probes/S1StepModelProbe.lean` (196 parameter tuples, including `σ = 0`, all three `mv` and out-of-range `mVal`/`wVal`). |
| `#print axioms S1Step.stepEmit_run` | **`[propext, Classical.choice, Quot.sound]`** — **stage C's last family is half BUILT: the `stepBlocks` ENTRY BODY** (2026-07-28, `Reductions/S1StepEmit.lean`, sorry-free): `stepEmit` is a real `Cmd` and `stepEmit_run` proves that, given the machine constants (`SConst` — free from `cFive`, see the new `S1CardEmit.cFive_const`) and one normalised transition entry's nine numbers in registers (`SEntry`), it appends exactly that entry's cards to `EOUT_C` while touching nothing outside `SD1 = [CX, EE, TJ1, TJ2, TJ3, EK1]` (measured, `probes/S1StepEmitProbe.lean` §2). Landed with it: the card atom `emitCard`/`card6_run` (six pairs of registers — step cards are **not** identity cards), the four `mv`-independent loop nests `cenFam`/`lefFam`/`rigFam`/`inFamR`/`inFamL`, and `stepEmit_usesBelow` (48). Two findings: **the three `mv` arms share their loop nests, not their cards** (parameterising a family gadget by its innermost body turned a 3 × 4 case split into 4 loop lemmas + 11 one-line card definitions); and **`S1CardEmit.emitLoop_run` does not fit the entry loop at all** — it pins the body's output to the *iteration index*, while a cursor-driven loop's output depends on registers inside its own dirty set. The fix landed with it: **`emitFold_run`**, a stateful emitter loop principle, plus the entry loop's pure model `stepGo` and its `emitFold_run`-shaped target `stepSummand_fold`. **What is left of the whole S1 program is the per-entry preamble, the entry loop, the three-line `stageC` assembly and the cost ladder.** |
| `#print axioms FrontS1Comp.SAT_NPhard''_of_S1` | **`[propext, Classical.choice, Quot.sound]`** — **the whole HARDNESS half of Cook–Levin, `sorry`-free, modulo ONE program meeting THREE contracts** (2026-07-27). Give a `Cmd` that (1) lays `S1Program.s1Key (s1Map x)` on registers `1`–`5` of the frozen head layout, (2) stays inside `s1RegBound = 48`, and (3) costs at most `S1Map.s1Bound` — and `NPhard'' SAT` follows. Front, both new seams, the S1 reduction and the entire sound tail are inside this theorem, and it does **not** route through `hasDeciderClassical`: the legacy hardness `sorry` is bypassed, not inherited. |
| `#print axioms S1SATComp.s1Bridge` / `FrontS1Comp.frontBridge` | **`[propext, (Classical.choice,) Quot.sound]`** — **the last two structural interfaces of the chain are VALIDATED** (2026-07-27): the fourth seam (S1 → the composed sound tail, `Reductions/S1_to_FlatTCC_comp.lean`) and C8-5 (the per-`Q` front → S1, `Reductions/Front_to_S1_comp.lean`). Both `mfc`s are pure scrubs built from the new reusable `clearRange` gadget; both bridges are stated over an *arbitrary* program meeting the S1 contracts, so stage C's placeholder cannot pollute them. Probe: `probes/SeamS1Probe.lean` (erase sets pinned to `s1RegBound`/`headRegBound`; the C8-5 bridge checked end to end over the full 57-register frame, with a negative control). |
| `#print axioms S1Program.s1Program_computes` / `s1Program_usesBelow` | **`[propext, Classical.choice, Quot.sound]`** — **the S1 reduction PROGRAM IS FINISHED** (2026-07-28-b): stage C is a real `Cmd` (`Reductions/S1StepLoop.lean` + `S1Program.stageC = cFive ;; stepFam ;; cPrelude`, all sorry-free), so **two of the three contracts of `SAT_NPhard''_of_S1` are discharged at the real program**. Landed with it: `S1Step.stepFam`/`stepFam_run` (the `stepBlocks` family: the per-entry preamble `entryPre` off a `PTRANS` cursor, the `O(|trans|²)` dedup scan, the halt lookup and the `emitFold_run` loop), plus the reusable gadgets `dropLoop`/`haltBlk`/`optRead`/`hvBlk`/`optMin`/`scanSeen`/`pushKey` and the frame workhorse `keeps_of_writes`. Three findings: **a cursor loop's body must be TOTAL** (`emitFold_run`'s `hstep` is quantified over every index, so the body needs a `nonEmpty` guard on its own cursor — which also means a guarded loop needs only an *upper* bound on its iteration count); **the accumulator must match its model's cons order** (`concat SSEEN item SSEEN` prepends, matching `stepSt`); and **a contract pinned for an unwritten `Cmd` is only as good as its first consumer** — `stageC_run` had been missing its `PSTART` hypothesis for three sessions. Probe: `probes/S1StepLoopProbe.lean` (the first end-to-end `#eval` of `s1Program`; stage C's output is *exactly* `encNats (cardBlocks M)`). |
| `#print axioms FrontS1Comp.SAT_NPhard''` / `S1SATComp.s1_to_SAT_reducesPolyMO'` | **`[propext, Classical.choice, Quot.sound]`** — **the whole HARDNESS half of Cook–Levin is `sorry`-FREE and axiom-clean** (2026-07-29-b). `NPhard'' SAT` and `FlatSingleTMGenNP ⪯p' SAT` at the *real* S1 program: the last obligation, the whole-program cost ladder `S1Witness.s1Program_costLeSize`, is proven by one decidable syntactic pass (`Cmd.chk`, `Lang/CostGrow.lean`) over the 5.4·10^5-node program. Regression list: `probes/AxiomProbe.lean` (~33 endpoints, all clean). |
| the one-cap cost ladder (`Lang/CostPoly.lean`, `Cmd.PolyCost`/`Cmd.CostSafe`) | **DELETED 2026-07-30-b.** It was built 2026-07-28-c and superseded three days later by `Cmd.CapCost`: a *single* cap cannot survive a `forBnd` at all (FINDING Z), so it was a design the project had already rejected and every future reader would have had to re-reject. Measured before deleting: `CostGrow` imported it but used nothing from it, and its only other references were one never-called lemma and a probe of the superseded design. Kept and moved into `Lang/CostFlat.lean`: **`Cmd.get_length_eval_le`** (per-register growth ≤ cost — the composable strengthening of `Cmd.size_eval_le`) and `Cmd.forBnd_counter_le`; those are facts about `Cmd.eval`/`Cmd.cost`, not part of the retired predicate. Its measurements survive in the row above and in `S1Witness.S1CostBound`'s design note. |
| `#print axioms Complexity.Lang.Cmd.chk_sound` | **`[propext, Classical.choice, Quot.sound]`** — **the cost ladder, as ONE decidable forward pass** (`Lang/CostGrow.lean`, sorry-free; 2026-07-29 designed, 2026-07-29-b closed). ⚠ **FINDING Z**: a cost predicate with ONE cap cannot survive a `forBnd` — the body's outputs are re-capped at `poly(M)` each iteration, so `m` iterations give a **tower**. `Cmd.CapCost c F F'` uses **two** caps (a frozen `MF`, a global `N`): `cost ≤ K·(MF+1)^D·(N+1)`, growth `≤ N + K·(MF+1)^D`, `F'` still `≤ MF + K·(MF+1)^D`. Cost linear in `N` pays for **FINDING X** (`copy EOUT_C EOUT_C`) for free; growth independent of `N` is what stops compounding. `Cmd.chk C c = (ok, C', B)` is the checker: `ok` certifies `CapCost`, and **`C'`/`B` are sound even when `ok` is false** (FINDING AC — an enclosing loop reads them to decide what to promote, and that promotion is what makes the rejected sub-command acceptable on a second pass). Three measured facts fixed the design: register sets must be `Nat` **bitmasks** (FINDING AA — `cPrelude.writes` is a 327411-element list, which made the old `List Var` checker quadratic in program size and non-terminating); `Nat.ldiff` is unusable because the kernel cannot reduce `Nat.bitwise`; and the kernel's wall is **memory** (FINDING AB — a two-traversals-per-loop version was OOM-killed at 15 GB), which is why each body is visited once. Measured (`probes/S1GrowSafeProbe.lean`): accepts **the whole program** — ~2 s by `#eval`, ~3 min by `decide +kernel`. |
| `#print axioms EvalCnfSplit.SAT_inNPLangFreeSplit` | **`[propext, Classical.choice, Quot.sound]`** — **the MEMBERSHIP half, unconditional** (2026-07-30-b). The last obligation was the register equation below; `EvalCnfSplit.certDecode_decodesAssgn` closes it by `Cmd.eval_forBnd` + `Cmd.foldlState_range_induct` at the invariant `ASSGN = encodeAssgn (decodeBits (c.take i))`, `DCUR = cbits (c.drop i)` — the invariant `probes/SATSplitProbe.lean` §5 had already `#eval`-validated at every prefix length, consumed verbatim with zero redesign (~110 lines for an 11-op program). Two findings: **frame facts belong in the write-set lemma, not the loop invariant** (the motive carries only the two registers the loop changes; `Cmd.eval_get_of_not_writes` does registers `0`–`2`/`4`–`15` once, at the end), and **a `Bool`-valued invariant `#eval`ed at every index before the proof is the cheapest de-risking move in the codebase.** |
| `#print axioms CookLevinHonest.CookLevin''_of_decodesAssgn` | **`[propext, Classical.choice, Quot.sound]`** — **the WHOLE of Cook–Levin, on the honest statement, reduced to ONE register equation** (2026-07-30; the equation was discharged 2026-07-30-b, and this program-generic form is kept as the interface a different decoder plugs into). `NPcomplete'' SAT` follows from `∀ N c, State.get (certDecode.eval (satEIn (N,c))) ASSGN = encodeAssgn (decodeBits c)` — a `_run` lemma about an 11-op program. The hardness half (`FrontS1Comp.SAT_NPhard''`) is already unconditional; the membership half (`Complexity/Complexity/Deciders/EvalCnfSplit.lean`, sorry-free) supplies the split layout (`satEncX`/`satEIn`, `xWidth = 3`), the certificate relation and its polynomial bound (`satRel_correct : polyCertRel SAT satRel`), the decoder's cost (`by decide` through `Cmd.chk`) and frame, the frame half of the bridge (free, from `Cmd.writes`), and all four composite `DecidesLang` bounds. Three findings: the `InNPWitnessLangFreeSplit` split law is **not** a layout obstruction (`precomposeFree` chooses the composite's `encodeIn`, and `State.get` reads unset registers as `[]`, so the eight trailing scratch `[]`s of `EvalCnfCmd.encodeState` are invisible and the entire gap is one register); a re-encoder whose scratch sits **above** the target verifier's `regBound` owes no scrub; and the certificate must be the **characteristic vector** (total on every bit string — `InNPWitnessLangFreeSplit` puts certificates in `certState`, so a sentinel-unary format would need a partial parse and a normaliser). Probe: `probes/SATSplitProbe.lean` (9 checks incl. the loop invariant at every prefix length, garbage/short/over-long certificates, and end-to-end acceptance). |
| Genuine `sorry`s in built code | **0** (2026-07-30-c). The last five were all on the legacy `⪯p` path and were **deleted with it**, not proved: `red_inNP`'s `inTimePoly` half, `hasDeciderClassical`, and 3× `MultiToSingle` (dead code). None was ever on the `NPhard''` path. `lake build` emits no `declaration uses 'sorry'`, and no endpoint in `probes/AxiomProbe.lean` (59 of them) prints `sorryAx`. |
| `sorry`-**free** but **vacuous** defs on the proof path | **none.** S1 (the if-on-the-answer tableau map) and S2 (the dummy `bridgeMachine` bridges) were the two that were invisible to `#print axioms`; both files are **deleted** (2026-07-30-c). The third member, the size-0 hardness reduction, was closed by Part 0.1 (2026-07-04). |
| Proof-path size | ~16K LOC under `CookLevin/` (a further ~15K parked and **permanently retired** — see `parked/README.md`) |
| Estimated work remaining | **none on the stated goal.** The theorem is proven, unconditional, audited and `sorry`-free. Further work is *scope extension* (honest NP-completeness for `kSAT 3` / `FlatClique`) or *hygiene* — see [`CookLevin/HANDOFF.md`](CookLevin/HANDOFF.md). |

> **The `sorry` count is not the soundness metric — and this project is the
> proof.** For most of its life the deepest unsoundness here (S1's
> if-on-the-answer reduction, S2's dummy bridges, the size-only `⪯p`) was
> `sorry`-free and completely invisible to `#print axioms`. Closing every
> `sorry` would not have made the legacy `CookLevin` faithful; that is why the
> honest line `⪯p'` / `NPhard''` / `NPcomplete''` was built alongside it, and why
> the last five `sorry`s were **deleted with the legacy front rather than
> proved**. The count is `0` today, but what makes the theorem trustworthy is the
> `NPcompleteStr` *statement* plus the S5 audit — not the count.

## What the theorem says, and what stands behind it

There is now exactly **one** chain, and every arrow in it is a real `Cmd`
program with a proven polynomial cost bound:

```
Q ⪯p' FlatSingleTMGenNP ⪯p' FlatTCC ⪯p' FlatCC ⪯p' BinaryCC ⪯p' FSAT ⪯p' SAT
└─ C8 front ─┘└─ S1 ─┘└──────────────── the sound tail ───────────────────┘
        = ONE composed free-layer witness = `NPhard'' SAT` ⊇ `NPhardStr SAT`
```

for every NP problem `Q` **presented with a split free-line verifier witness**
(`InNPWitnessLangFreeSplit`: a real `Cmd` verifier over a bit-level layout, with
`List Bool` certificates in a canonical one-register format). Composition is at
the `Cmd` level, through five `SeamData`/`comp` seams; hardness is proven at the
chain endpoint only. Together with `EvalCnfSplit.SAT_inNPLangFreeSplit`
(membership), that is `CookLevinHonest.CookLevin'' : NPcomplete'' SAT` — and,
restricted to string languages, `CookLevinHonest.CookLevinStr :
NPcompleteStr SAT`, the statement to quote.

**Why the hypothesis is a verifier witness and not `inNP Q`.** `inNP`/`inTimePoly`
are *classically true for every predicate* — the framework's `DecidesBy` lets the
`encode` field do the deciding, so a hardness statement quantified over `inNP Q`
is unprovable-honestly by construction (ROADMAP risk **S0/S6**). `NPhard''`
quantifies over problems that arrive with a real verifier program. That is the
textbook verifier definition of NP, and it is the same role the L-computable
verifiers play in the Coq original.

**Why the published statement restricts further, to string languages
(2026-08-01).** A verifier witness still supplies its *own* input layout `encX`,
and the composite reduction's encoding is built from it. That is enough freedom
to present an **arbitrary** predicate — even an undecidable one — with the answer
planted in its input and a no-op verifier, which made `NPhard'' SAT` yield
`Q ⪯p' SAT` for that `Q`. ⚠ *That particular* cheat was killed on 2026-08-02 by
the `sizeLB` no-compression field (`probes/HonestyAuditProbe.lean` §7 now proves
it unbuildable) — but **§7b survives and always will**: write the honest
encoding out and *append* the answer in a second register, and every law about
`encX` still holds. Fixing the input type to `List Bool` and the layout to the
canonical `certState` removes the field entirely:

```
NPhardStr SAT : ∀ Q : List Bool → Prop, inNPStr Q → Q ⪯p' SAT
```

is `NPhard'' SAT` restricted along `NPhard''_to_NPhardStr`, and under it the
reduction's input encoding is a closed formula in `x` rather than a choice of
the reader's. `CookLevinHonest.CookLevinStr` is the corresponding headline.

**Why there is no `NPcomplete'' → NPcomplete` bridge.** `⪯p` (`reducesPolyMO`)
bounds only the reduction's *output size*, never its runtime — the reduction
function may even be noncomputable. So `NPhard`/`NPcomplete` as *defined* are too
weak to be faithful, and the honest statement does not imply the vacuous one. The
legacy headline that quoted it was **deleted** (2026-07-30-c), along with the
`sorry`-backed and vacuous machinery that fed it. `⪯p` itself survives in
`NP.lean` as the weaker notion `⪯p'` is defined to strengthen
(`reducesPolyMO'_to_reducesPolyMO`), with no live consumer.

### What was deleted on 2026-07-30-c, and why it was deleted rather than proved

| removed | it was |
|---|---|
| `CookLevin : NPcomplete SAT`, `CookLevin0`, `Clique_complete`, `GenNP ⪯p … ⪯p SAT` | the legacy headline over the vacuous `⪯p` |
| `GenNP_is_hard.lean` (`NPhard_GenNP`, `hasDeciderClassical`) | a flat `sorry` asserting a `DecidesBy` for *any* predicate — the last `sorryAx`, and **unclosable honestly**: closing it is exactly the cheat above |
| `L_to_LM.lean`, `LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean`, `NP/TM/IntermediateProblems.lean`, `Simulators/MultiToSingle.lean` | the S2 bridges: a 1-state `bridgeMachine` with no transitions that accepts everything, so the TM-acceptance conjuncts carried no information |
| `Reductions/FlatSingleTMGenNP_to_FlatTCC.lean` | the S1 original sin — literally `if (source is a yes-instance) then yesInst else noInst`, with an all-zeros tableau that never simulates `M`. `sorry`-free and **vacuous**; licensed by `⪯p` |
| `NP.lean`'s `red_inNP`, `kSAT_to_SAT.lean`'s `inNP_kSAT` | `⪯p` gives no program for the reduction, so the composed verifier cannot be built; the `inTimePoly` half was a `sorry` closable only by the same cheat. Live replacement: `Lang.red_inNP_of_langFree` |

None of it was ever reachable from `CookLevin''`. Deleting it took the
development from 5 `sorry`s to **0**.

**Sound (genuine mathematics, ~3K LOC, `sorry`-free, do not touch):** the tail
`FlatTCC → FlatCC → BinaryCC → FSAT → SAT` (window/cover equivalence, unary
block encoding, tableau CNF, a full Tseytin transform), the S1 tableau
(`Simulators/CookTableau.lean` + `GuessTableau.lean`: the bijection, the
cert-guess layer and both size bounds), plus `kSAT_to_SAT` and
`kSAT_to_FlatClique`. Their input-guarded `if isValidFlattening …` branches test
a *decidable property of the input* — audited 2026-07-30-c, see ROADMAP **S5**
verdict 6. The `FlatTM` model, the `encodable`/`inOPoly` machinery, the
`DecidesBy`/`inTimePoly` interface, and the `composeFlatTM`/`loopTM` combinator
family are also sound.

**The one thing that is not enforced:** encoding honesty for *intermediate*
witnesses. The two chain ends are pinned (tail: `Serialize cnf`; head: the
`NPhardStr` statement). See the caveat at the top of this file and ROADMAP risk
**S5**.


## The strategy: a higher-level computable layer

Building verifiers/reductions directly as `FlatTM`s overran budget ~10× and was
abandoned (parked under `parked/`, ~15K LOC). The pivot: a small structured
while-language `Cmd`/`Op` with explicit **cost** semantics, compiled **once** to
`FlatTM` (`Compile`). Every downstream verifier/reduction is then a short DSL
program. This is the Lean analogue of the L-calculus the Coq port uses — and,
being single-tape by construction, it is also why the S2 multi-tape detour is
unnecessary.

The layer's structural unknowns are **probed**: per-primitive compilation (C1),
composition (C2), and the counted loop (C3) all have proven *combinators*
(`compileSeq_compose_physical`, `loopTM_run`, `bitTestTM`, and a ~1.6K-LOC
sorry-free gadget library: `appendAt_run`, `scanLeft_run`, `insertCarryTM_run`,
…). The S3 layer→framework bridge is built **on the free-encoding line** and is
LIVE & axiom-clean (`toFrameworkWitness'`, `inNPLangFree`/`inNPLangFree_to_inNP`,
`FreePrecomposeData`/`red_inNP_of_langFree`, `reducesPolyMO'_of_langFree` — live
instances `inNP_kSAT3_free`, `kSAT3_reducesPolyMO'`, and
`flatTCC_reducesPolyMO'`). Chains of reduction witnesses compose **at the
`Cmd` level** via `PolyTimeComputableLang.SeamData`/`comp` (fully proven,
2026-07-02) — the honest replacement for `⪯p'`-transitivity, which deliberately
does not exist. A canonical
shared-encoding alternative (`LangEncodable`/`PolyTimeComputableLang'` +
`swap`/`map_fst`/`map_snd`) was built and then **retired & deleted
(2026-07-02)** — its generic product encoding is size-unsound
(`probes/UnaryProductSizeProbe.lean`) and the audit showed no remaining witness
needs it.

**C2 status:** the compiler is DONE and CLEAN. All 9 `compileOp`s are FULLY
PROVEN & axiom-clean (`appendOne`/`appendZero`/`clear`/`nonEmpty`/`head`/`copy`/
`tail`/`eqBit`/`concat`), and `compileOp_sound_physical_residue` is fully proven
with no side-conditions, so **`SAT_inNP.sat_NP` is sorry-free & axiom-clean**.
The value-as-length trio (`takeAt`/`dropAt`/`consLen`) and both isolation walls
(`NoConsLen`, `IsSupported`/`AllOpsSupported`) are **deleted** (2026-07-04): `Op`
has exactly the 9 live constructors and the compiler chain carries no wall
threading. `Compile_sound` was false as stated for *three*
reasons. (1) its budget ignored the register count; fixed by a tape-length
budget, **proven** for the real ops (`compileOp_appendOne_sound`). (2) ops were
**unit cost** but `concat`/`copy` grow the state **multiplicatively** (output
size exponential in layer cost); **fixed** by a size-aware `Op.cost`, validated
by `Op.size_eval_le`, and the **Cmd-level size bound is now PROVEN**
(`Cmd.size_eval_le : size (c.eval s) ≤ size s + c.cost s`, by charging the
`forBnd` loop counter). (3) **the per-fragment `overhead` budgets are quadratic
and do not compose** (summing ~cost quadratics → cubic), so `compileSeq_sound`
and siblings are unprovable as stated — the fix is **linear** per-fragment
budgets (the gadgets prove `≤ 2·tapeLen+3`) composing to a quadratic total; the
**linear tape-length ingredient is now proven** (`Cmd.encodeTape_eval_length_le`).
The **leading-sentinel encoding migration is now DONE** (`encodeTape s = endMark
:: encodeRegs s ++ [endMark]`, `sig` stays `4`): the physical contract's "head
rewound to `0`" needed a left sentinel the old `encodeTape` lacked (the rewind
lemmas themselves already existed, `ScanLeft.rewindToStart_run/_traj`). All real
consumers re-proven green & axiom-clean. **⚠ 2026-05 BLOCKING FINDING (machine-
checked, `Complexity/Complexity/TapeMono.lean`):** the physical TM tape **never
shrinks**, so the exact-tape physical contract (`exit tape = encodeTape output`)
is **unsatisfiable for every length-decreasing op** (`clear`/`tail`/shrinking
`copy`/…) — only the growth ops `appendOne`/`appendZero` fit. The fix — the
**residue-tolerant** contract (`encodeTape output ++ terminator-free residue`)
— is **built and fully proven** for all 9 live ops and the whole decider chain.
The compiler is done; see ROADMAP Risk C2 and
`CookLevin/HANDOFF.md` for the remaining hardness-side work.

## Development methodology: skeleton-first, risk-driven

(do not deviate without reason — full rationale in the ROADMAP)

1. **Skeleton first** — the whole proof path compiles with `sorry`s before any
   single proof is closed; this exposes every downstream obligation.
2. **Refine the highest-risk gap next** (per the Risk register), not in phase
   order.
3. **Decompose `sorry`s, don't elaborate them** — each split is a structural
   decision that typechecks (right shape) or fails (gap found).
4. **Prefer `def` + `sorry` over `axiom`** (axiom count is a metric to minimise;
   currently 0). New results must be `#print axioms`-clean (only `propext` /
   `Quot.sound` / `Classical.choice`).
5. **Probe before committing engineering** — for a big unknown, run a time-boxed
   go/no-go probe and give a verdict (feasible / feasible-but-expensive /
   trigger-fallback).
6. **Build green between commits; record gaps in commit messages.**

## Repository layout

```
CookLevin/
├── ROADMAP.md                       -- strategy + ordered plan + Risk register (read first)
├── Complexity/
│   ├── Complexity/
│   │   ├── Definitions.lean         -- encodable (real sizes, no size-0 fallback), inOPoly, monotonic
│   │   ├── MachineSemantics.lean    -- FlatTM, stepFlatTM, runFlatTM
│   │   ├── NP.lean                  -- DecidesBy, inTimePoly, inNP; the legacy ⪯p/NPhard (no live consumer)
│   │   ├── TMPrimitives.lean        -- composeFlatTM / branchComposeFlatTM / loopTM (~4K LOC, sound)
│   │   └── Deciders/                -- EvalCnfCmd/EvalCnfTM (SAT verifier), CliqueRelTM, EvalCnfSplit (membership half), CnfSerialize
│   ├── SoundnessGate.lean          -- the axiom sweep, run BY `lake build`
│   ├── HonestyGate.lean            -- risk S5's two audited functions, pinned BY `lake build`
│   ├── CostFaithfulness.lean       -- `Op.cost` is a polynomial proxy for real TM time
│   ├── Meta/AxiomGate.lean          -- `#assert_axioms_clean` / `#assert_library_axiom_clean`
│   ├── Lang/                        -- the layer: Syntax, Semantics, Compile (C1/C2/C6), Frame,
│   │   │                               PolyTime (⪯p'/NPhard''/comp — read this one),
│   │   │                               HardnessStr (NPhardStr — read this one too),
│   │   │                               Serialize, CostGrow/CostFlat, gadgets
│   │   └── …
│   ├── Simulators/                  -- CookTableau + GuessTableau (the S1 tableau, sorry-free)
│   └── NP/
│       ├── SAT.lean / kSAT.lean / FSAT.lean / FlatClique.lean
│       ├── FSAT_to_SAT.lean         -- Tseytin (~700 LOC, sound)
│       └── SAT/CookLevin/
│           ├── CookLevinHonest.lean -- ★ the theorem
│           ├── Reductions/          -- the free-line witnesses, the S1 program, the five seams
│           └── Subproblems/         -- FlatTCC / FlatCC / BinaryCC / SingleTMGenNP
probes/                              -- #eval/decide risk checks (AxiomProbe, HonestyAuditProbe, …)
parked/                              -- hand-rolled pre-pivot work (~15K LOC, PERMANENTLY RETIRED, not built)
coqdoc/                              -- local mirror of the Coq port
```

## Building

`mathlib` is the only dependency. From the repo root:

```
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

First build from a clean checkout is slow (mathlib cache). Lake's `lean_lib`
root is `CookLevin/`, so `parked/` is not built. Axiom check (lean-lsp's LSP
cannot find `lake`, so use a scratch file):

```
env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean   # `#print axioms <name>`
```

## Where to look first

- **The theorem:** `NP/SAT/CookLevin/CookLevinHonest.lean`, and the statement it
  proves — `NPcompleteStr`/`NPhardStr`/`InNPWitnessStr` in
  `Complexity/Lang/HardnessStr.lean`, and the general
  `NPcomplete''`/`NPhard''`/`InNPWitnessLangFreeSplit` in
  `Complexity/Lang/PolyTime.lean`. Read the statement before the proof.
- **The working plan:** [`CookLevin/HANDOFF.md`](CookLevin/HANDOFF.md); the risk
  register: [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md).
- **Is it honest?** `probes/HonestyAuditProbe.lean` — §6 is a witness that
  satisfies every field while computing nothing; §7 is the hypothesis-side cheat
  that **died** on 2026-08-02 (with the proof that it did); §7b is the one that
  survives every law about `encX`; §8 is the restriction that removes the field
  they exploit, and pins the composite's encode to `certState x` by `rfl`. Then
  ROADMAP risk **S5**, verdicts 1–14.
- **Is it enforced?** `Complexity/Meta/AxiomGate.lean`,
  `Complexity/SoundnessGate.lean` and `Complexity/HonestyGate.lean` — what a
  green `lake build` proves, and what it does not.
- **Is "polynomial time" real time?** `Complexity/CostFaithfulness.lean` —
  `Compile.cost_is_time_proxy`, and the module docstring on the one direction it
  deliberately does not prove.
- **Real mathematics:** `NP/SAT/CookLevin/Subproblems/FlatTCC.lean` and the
  `Reductions/FlatTCC_to_FlatCC.lean → … → BinaryCC_to_FSAT.lean` chain, then
  `NP/FSAT_to_SAT.lean`; the tableau in `Simulators/CookTableau.lean`.
- **The layer:** `Complexity/Lang/Compile.lean`, `Complexity/Lang/PolyTime.lean`.

## References

- Coq source: <https://github.com/uds-psl/cook-levin>; mirror `coqdoc/`.
- Roadmap / plan / Risk register: [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md).
- Parked work: [`parked/README.md`](parked/README.md).
