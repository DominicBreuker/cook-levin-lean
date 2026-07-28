# Cook–Levin in Lean 4

A Lean 4 formalisation targeting the **Cook–Levin theorem** (SAT is
NP-complete), structured as a port of the Coq development by Forster, Kunze,
Roth et al. (<https://github.com/uds-psl/cook-levin>, mirrored under `coqdoc/`).

**Work in progress — the theorem typechecks but is NOT yet a faithful proof.**
`CookLevin/Complexity/NP/SAT/CookLevin.lean` declares `theorem CookLevin :
NPcomplete SAT` and `lake build` accepts it, but the term is **conditional** on
both `sorry`-backed gaps and `sorry`-free *vacuous* definitions. Read
[`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md) for the plan and the full risk
register before working.

## Honest status (verified 2026-07)

| | |
|---|---|
| `lake build` | ✅ green |
| `#print axioms CookLevin` | **`[propext, sorryAx, Classical.choice, Quot.sound]`** — the headline theorem **does depend on `sorryAx`**, now **only via the hardness half** (`NPhard_GenNP`). |
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
| `#print axioms FrontS1Comp.SAT_NPhard''` / `S1SATComp.s1_to_SAT_reducesPolyMO'` | `[propext, sorryAx, Classical.choice, Quot.sound]` — `NPhard'' SAT` and `FlatSingleTMGenNP ⪯p' SAT` at the *real* S1 program; the `sorryAx` is exactly `S1Program.stageC` (a `def`+`sorry`) and `S1Witness.s1Program_cost_le`. |
| Genuine `sorry`s in built code | **9** (Group C — completion; `Reductions/S1Parse.lean`, `S1Cards.lean`, `S1Emit.lean` and `S1CardEmit.lean` are sorry-free). Five pre-existing: `red_inNP`'s `inTimePoly` half, `hasDeciderClassical`, 3× MultiToSingle (dead code). Three S1 stage markers in `Reductions/S1Program.lean` (`stageC` and its `_run` / `_usesBelow` contract — only the `def` is a real gap). One cost obligation: `S1Witness.s1Program_cost_le` (the whole-program cost ladder, now a standalone named theorem rather than a witness field). **`Simulators/CookTableau.lean` and `Simulators/GuessTableau.lean` are fully `sorry`-free** — the S1 bijection `cookTableau_correct`, the cert-guess `guessTableau_correct`, and **both size bounds** are sorry-free & axiom-clean (2026-07-18…-24). |
| `sorry`-**free** but **vacuous** defs on the proof path | S1, S2 (Group S — soundness) — invisible to `#print axioms`. The third member, the size-0 hardness reduction, was **closed by Part 0.1** (2026-07-04: real `encodable.size` everywhere, size-0 default deleted, honest `NPhard_GenNP` bound) |
| Proof-path size | ~16K LOC under `CookLevin/` (a further ~15K parked, not built) |
| Estimated work remaining to a real, unconditional proof | **~12–20K LOC** (see ROADMAP) |

> **The `sorry` count is not the soundness metric.** The deepest unsoundness
> (S1/S2, and the size-only `⪯p`) is `sorry`-free and invisible to
> `#print axioms`. Closing every `sorry` would **not** by itself make
> `CookLevin` faithful. Track **Group S** (soundness) and **Group C**
> (completion) separately.

## What is sound vs. what is not

NP-hardness is transported from a universal NP source down to SAT along a chain
of `⪯p` (poly-time many-one) reductions:

```
GenNP ⪯p … ⪯p FlatSingleTMGenNP ⪯p FlatTCC ⪯p FlatCC ⪯p BinaryCC ⪯p FSAT ⪯p SAT
└──────────── front: NOT sound ────────────┘└──────────── tail: SOUND ───────────┘
```

That is the **legacy** chain, which the headline `CookLevin` still quotes. The
honest replacement is built and composed end to end (2026-07-27):

```
Q ⪯p' FlatSingleTMGenNP ⪯p' FlatTCC ⪯p' FlatCC ⪯p' BinaryCC ⪯p' FSAT ⪯p' SAT
└─ C8 front ─┘└─ S1 ─┘└──────────────── the sound tail ───────────────────┘
        = ONE composed free-layer witness = `NPhard'' SAT`
```

for every NP problem `Q` presented with a split free-line verifier witness —
`sorry`-free except for the S1 program's stage C and its cost ladder (see
`FrontS1Comp.SAT_NPhard''_of_S1` in the table above). The legacy front is
retired only after `NPcomplete'' SAT` is stated; see `CookLevin/HANDOFF.md`.

**Sound (genuine mathematics, ~3K LOC, `sorry`-free, do not touch):** the tail
`FlatTCC → FlatCC → BinaryCC → FSAT → SAT` (window/cover equivalence, unary
block encoding, tableau CNF, a full Tseytin transform), plus `kSAT_to_SAT` and
`kSAT_to_FlatClique`. These reductions are real constructions; their
input-guarded `if isValidFlattening …` branches test a *decidable property of
the input* (legitimate), not the answer. The `FlatTM` model, the
`encodable`/`inOPoly` machinery, the `DecidesBy`/`inTimePoly` interface, and the
`composeFlatTM`/`loopTM` combinator family are also sound. Cook–Levin *after* a
TM run is encoded as a `FlatTCC` is essentially in place.

**Not sound — three independent reasons the theorem is currently vacuous:**

- **S3 (the enabling weakness, definitional).** `⪯p` (`reducesPolyMO`) is
  licensed only by `polyTimeComputable`, which bounds **output size**, not
  runtime (`NP.lean`, `PolyTimeComputableWitness.bound_valid`). The reduction
  function may even be noncomputable. So `NPhard`/`NPcomplete` as currently
  *defined* are too weak: the headline statement, even with every `sorry`
  closed, would assert a vacuous notion of NP-completeness. The honest target
  `polyTimeComputable'` (`Lang/PolyTime.lean`, `ComputesBy`: a real TM halting
  within a polynomial *time* bound) **is faithful** — confirmed — and extends
  the old witness, so retiring S3 is a strengthening, not a rewrite. But it
  forces every reduction to carry a real program (S1/S2 then *stop
  typechecking*).
- **S1 (front reduction).** `FlatSingleTMGenNP ⪯p FlatTCC`
  (`Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`) is literally
  `if (source is yes-instance) then yesInst else noInst`, where `yesInst` is an
  all-zeros 1-symbol tableau that **never simulates the source machine `M`**.
  Sorry-free but vacuous; licensed by S3. Real fix = the Cook 2D tableau —
  **v2 landed 2026-07-17** (`Simulators/CookTableau.lean`): a 2026-07-17 risk
  review found the v1 bijection *false as stated* (the flat tape's
  zero-padding jump-writes were non-local — **semantics fixed**, the tape is
  now append-only at the frontier — plus three card-family defects); the v2
  construction (boundary marker, normalised transition table, the full
  3-position + incoming-head + halt-freeze card algebra) is landed with the
  corrected statement decomposed, the assembly proven, and card/step
  agreement `#eval`-probed green (`probes/S1TableauProbe.lean`).
  **Direction (1a) — machine step/halt ⟹ card-covered row transition — is
  PROVEN (2026-07-18)** together with its gates (`stepFlatTM_normM`,
  `ConfFits_step`, `satFinal_of_halt`), **`halt_of_satFinal` — the
  backward final-pattern bridge — is PROVEN (2026-07-18-b)** on the
  cell-code disjointness algebra, and **direction (2) `cover_of_run`
  (axiom-clean) plus the direction (3) assembly `run_of_cover` are PROVEN
  (2026-07-18-c)**. A third top-down risk review (2026-07-18-c) found the
  v2 completeness direction **false at the right row edge** (a
  machine-checked *phantom head* at the row's last cell — the one cell
  with no second refuting window; `probes/S1TableauProbe.lean` §5) and
  **fixed it with a right boundary marker** + the `copyRightCards` family.
  **The (1b) inversion `step_of_validStep` is PROVEN (2026-07-18-d)**, so
  **the whole bijection `cookTableau_correct` is sorry-free & axiom-clean**
  (`[propext, Classical.choice, Quot.sound]`). **The prelude/cert-guess layer
  is COMPLETE (2026-07-19-b, `Simulators/GuessTableau.lean`)**: a band-disjoint
  prelude alphabet turns the instance's `∃ cert` into row-0 tableau
  nondeterminism while reusing the deterministic core unchanged; the headline
  `guessTableau_correct` is sorry-free & axiom-clean (P1/P2 + Γ-band transfers
  all proven; probe `probes/S1TableauProbe.lean` §6). **Both size bounds
  `cookTableau_size_bound`/`guessTableau_size_bound` are PROVEN (2026-07-24,
  `≤ (2·(n+1))^10`; see the HANDOFF risk finding on the base), so
  `CookTableau.lean`/`GuessTableau.lean` are now fully `sorry`-free.** The S1
  *reduction* is now half-built: the **map is DONE & axiom-clean**
  (2026-07-25, `Reductions/S1Map.lean`) — the decidable guard `s1GuardB`, the
  map `s1Map`, the correctness iff `s1Map_correct`, and the output-size bound
  `s1Map_size_le` — and the witness skeleton (`Reductions/S1Witness.lean`)
  pins both layouts (input = the frozen `Reductions/HeadLayout.lean`; output =
  `FlatTCCFree.encodeIn` verbatim, making the next seam a pure scrub) and
  proves the output key injective plus every mechanical field. **What remains
  is the program `s1Program` and its three fields** — the whole critical path.
  **Two of the program's seven stages have landed (2026-07-25-b,
  `Reductions/S1Parse.lean`, sorry-free & axiom-clean):** stage **P** (parse)
  drains `encSyms (flattenTM M)` into a pinned scratch frame and stage **G**
  (guard) decides `S1Map.s1GuardB` on-machine (`stagePG_run`), fixing the
  register frame every later stage lives in (`stagePG_usesBelow : UsesBelow 32`;
  `s1RegBound = 48`). Two findings: the parse's cost is **cubic**, so it is not
  the budget driver; and because `flattenEntry` writes each list's own length
  before its payload, **the parse never desynchronises even on invalid
  machines**, so neither stage needs a validity hypothesis.
  **Stage C — the card emitter, the largest remaining piece — is now
  DE-RISKED (2026-07-25-c, `Reductions/S1Cards.lean`, sorry-free &
  axiom-clean):** `cardBlocks_eq` proves the `Fin`-typed, `finRange`/
  `filterMap`-driven `guessCards M` equal to `cardBlocks M`, seven nested
  `List.range` streams whose every cell code is arithmetic in the numbers
  stage P already parses — with one equation per card family, so the emitter
  can be built and proven a family at a time. It also specifies the one
  non-loop gadget (`normModel_eq`: the `normTrans` dedup is a three-number key
  pass plus one halt-bit lookup) and closes the multiplex's guard-false branch
  (`stageMNo`). Two measured findings: the prelude family is `Θ(σ³)`, not
  `Θ(σ⁶)`; and the emitter must append cell by cell, never `concat`, since
  `Op.cost concat` charges the whole destination register. The `Cmd`s for
  stages Σ / I / C / F / M-yes and the cost ladder are what is left; no
  remaining piece's shape is unknown.
  **Three more stages landed 2026-07-26 (`Reductions/S1Emit.lean`, sorry-free &
  axiom-clean):** the emitter atom `emitBlk` (a bare unary block appended cell
  by cell) and stages **Σ**, **I** and **F**, each with a pure `List.range`
  model proven equal to the `Fin`-typed definition. Findings: stage F needs no
  validity hypothesis at all (draining `PHALT` reproduces `M.halt.getD` out of
  range too); the head-cell code is maintained *incrementally*, with the inner
  loop counter supplying its low digit — the template stage C repeats seven
  times; the prelude row is three consecutive segment loops plus one first-cell
  flag, not one branching loop; and the guard is **load-bearing**, not a
  convenience — the probe exhibits an off-guard instance where stage I and
  `preludeRow` genuinely disagree. The same session closed `flattenTM_size_le`
  after finding its previous statement false (see the table above).
  **The program is now ASSEMBLED (2026-07-26-b, `Reductions/S1Program.lean`):**
  `s1Program = stagePG ;; ifBit FLG yesBranch stageMNo`; the guard-false half of
  `computes` is proven outright and axiom-clean (`noBranch_computes`), the
  guard-true half (`yesBranch_run`) modulo only the two open stage contracts
  `stageC_run` / `stageMYes_run`, and `S1Witness.s1_reductionLang` discharges
  `computes` / `usesBelow` / `decode_agree` — **`cost_le` is its only open
  field. Stage C, stage M-yes and the cost ladder are all that is left.**
  Three findings: a `sorry` inside a `def` puts `sorryAx` in the axiom list of
  every lemma *mentioning* it, so skeleton-phase lemmas must quantify over the
  placeholder to stay honest-checkable; `#eval` refuses any expression reaching a
  `sorry` even down an untaken branch, so a skeleton program cannot be probed end
  to end; and a sorried `_run` contract is an unchecked assumption —
  `probes/S1ProgramProbe.lean` checks both contracts numerically against
  `s1Key (guessTableau …)` on the real frozen head layout. Measured there: the
  card register is `>99.8%` of the emitted output, so **stage C alone is the cost
  ladder.**
  **Stage M-yes and five of stage C's seven card families landed 2026-07-26-c**
  (`Reductions/S1Program.lean`, `Reductions/S1CardEmit.lean`, both sorry-free &
  axiom-clean): the output multiplex is closed, and `copyBlocks`,
  `copyRightBlocks` and the three halt families are real `Cmd`s assembled as
  `cFive`, whose output is machine-checked to be a genuine **prefix** of
  `encNats (cardBlocks M)`. Reusable: `emitLoop_run` (the generic `forBnd`
  emitter invariant, dirty set as a register *list* so `r ∉ D` is `by decide`),
  the two-source block `emitBlk2`, the identity-card atom `emitId` (all five
  families emit identity cards — `stepBlocks` will not), `loadX`, and the gated
  `q` loop `haltFam`. ⚠ **Measured finding that reverses the build order**:
  `preludeBlocks` is **~96%** of the card register (`(five, step, prelude)` =
  `(3708, 1386, 126957)` on the probe's smallest non-trivial instance,
  `probes/S1CardEmitProbe.lean` §3), so the *prelude* family — not `stepBlocks`,
  and certainly not the five just built — is the cost ladder. **Stage C's last
  two families and the cost ladder are all that is left of the program.**
  ⚠ Landing this required correcting `encodable FlatTM`, whose old measure
  (`sizeFlatTM`, a flat `5` per transition entry) made the witness's
  `encodeIn_size` obligation *unsatisfiable* (`probes/S1SizeGapProbe.lean`).
  **The two remaining seams landed 2026-07-27** (`Reductions/S1_to_FlatTCC_comp.lean`,
  `Reductions/Front_to_S1_comp.lean`, both sorry-free): the fourth seam joins
  the S1 witness to the whole composed sound tail (`mfc` = erase register `0`
  and the S1 scratch block `[6,48)`; registers `[48,57)` close by the
  `Cmd.eval_length_le` length argument), and C8-5 joins the per-`Q` front to
  that composite on the frozen head layout (`mfc` = erase `[5,57)`). Both
  bridges are stated over an **arbitrary** program meeting the S1 contracts and
  are axiom-clean, and the S1 witness itself is now built in two steps
  (`S1Witness.s1WitnessOf` + its instantiation) so that the whole chain can be.
  The payoff is `FrontS1Comp.SAT_NPhard''_of_S1` in the table above: **the
  hardness half of Cook–Levin, `sorry`-free, modulo one program meeting three
  contracts.** What is left of S1 is `preludeBlocks`, `stepBlocks`, the `stageC`
  assembly and `S1Witness.s1Program_cost_le` — nothing structural.
  **The prelude family — `~96%` of the card register and stage C's cost driver
  — was made emitter-shaped 2026-07-27-b** (`Reductions/S1Prelude.lean`,
  sorry-free & axiom-clean): `preludeBlocks_seg` re-states the target in the
  exact nesting the `Cmd` implements, and the four findings behind it removed
  the two design unknowns that remained (no pair-list register per kind, no
  on-machine comparison gadget). The preamble `pPre` supplies the two values no
  earlier stage computes — `min M.start M.states` (via the new `minReg`) and
  the head band's base `(σ+1)(q0+1)` — and the reusable `emitList` replaces
  `emitId` for the two families that do not emit identity cards. ⚠ It also
  found that the cost budget has ~12 orders of magnitude of slack, which fixes
  how the last two pieces must be built.
  **The prelude family's `Cmd` landed 2026-07-27-c**
  (`Reductions/S1PreludeEmit.lean`) together with the emitter-shaped model of
  `stepBlocks` (`Reductions/S1StepModel.lean`) — see the two rows in the table
  above. The earlier reading that stage C's register licence is "exactly full"
  was too pessimistic: `stepBlocks` emits *before* the prelude and the prelude's
  preamble rebuilds every constant its nest reads, so the whole 30-register
  licence is available to it.
  **`stepBlocks`'s entry body landed 2026-07-28** (`Reductions/S1StepEmit.lean`
  — see the row in the table above), together with the entry loop's pure model
  and the stateful loop principle it needs. **What is left of the whole S1
  program is the per-entry preamble (nine numbers off `PTRANS`), the entry loop,
  the three-line `stageC` assembly and the cost ladder** — no remaining piece's
  shape is unknown.
- **S2 (bridges).** `LM_to_mTM` / `mTM_to_singleTapeTM` use a 1-state
  `bridgeMachine` with empty transitions that **accepts everything**; the
  TM-acceptance conjuncts carry no information. Sorry-free but vacuous.
- **Hardness foundation also reaches a `sorry`.** `NPhard_GenNP`
  (`GenNP_is_hard.lean`) relies on `hasDeciderClassical`, a flat `sorry`
  asserting a `DecidesBy` for *any* predicate. (Its former second defect — the
  vacuous `fun _ => 0` output-size bound over the size-0
  `instEncodableDefault` — is **fixed**: Part 0.1 done 2026-07-04, real
  `encodable.size` everywhere, the size-0 fallback deleted, and the bound is
  now an honest polynomial.) **This is now the *only* `sorry` reaching the
  headline `CookLevin`**:
  the in-NP half (`SAT_inNP.sat_NP`, routed through the layer verifier
  `evalCnfCmd`) is **sorry-free & axiom-clean** (all 9 compiler ops are proven,
  and the stub trio + its isolation walls were deleted 2026-07-04). So `sorryAx`
  on `CookLevin` is now wholly a *hardness*-side fact.

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
│   │   ├── NP.lean                  -- DecidesBy, inTimePoly, ⪯p, NPhard, red_inNP (S3 lives here)
│   │   ├── TMPrimitives.lean        -- composeFlatTM / branchComposeFlatTM / loopTM (~4K LOC, sound)
│   │   └── Deciders/                -- SAT / FlatClique verifier interfaces (C7, sorry bodies)
│   ├── Lang/                        -- the layer: Syntax, Semantics, Compile (C1/C2/C6),
│   │   │                               Frame, PolyTime (S3/C4 bridges), gadgets (sound)
│   │   └── …
│   ├── Simulators/                  -- CookTableau + GuessTableau (S1, sorry-free); MultiToSingle (dead code)
│   ├── GenNP_is_hard.lean           -- NPhard_GenNP via hasDeciderClassical (C8 sorry)
│   ├── L_to_LM / LM_to_mTM / mTM_to_singleTapeTM.lean  -- bridges (S2, vacuous)
│   └── NP/
│       ├── SAT.lean / kSAT.lean / FSAT.lean / FlatClique.lean
│       ├── FSAT_to_SAT.lean         -- Tseytin (~700 LOC, sound)
│       └── SAT/CookLevin.lean + CookLevin/Reductions/ + Subproblems/
parked/                              -- paused hand-rolled work (~15K LOC, not built)
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

- **The plan and risks:** [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md).
- **Real mathematics:** `NP/SAT/CookLevin/Subproblems/FlatTCC.lean` and the
  `Reductions/FlatTCC_to_FlatCC.lean → … → BinaryCC_to_FSAT.lean` chain, then
  `NP/FSAT_to_SAT.lean`.
- **The framework:** `Complexity/NP.lean` (`⪯p`, `DecidesBy`, `red_inNP`).
- **The layer:** `Complexity/Lang/Compile.lean`, `Complexity/Lang/PolyTime.lean`.
- **What must be replaced:** the S1/S2/S3 entries in the ROADMAP Risk register.

## References

- Coq source: <https://github.com/uds-psl/cook-levin>; mirror `coqdoc/`.
- Roadmap / plan / Risk register: [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md).
- Parked work: [`parked/README.md`](parked/README.md).
