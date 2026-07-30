# Cook–Levin in Lean 4 — Roadmap

The strategy, **ordered plan**, and **risk register** for making `theorem
CookLevin : NPcomplete SAT` real and unconditional. Written for agents: it
states where the proof stands and what to do next. A living plan, not a history.

**Orientation.** The theorem typechecks but is **conditional**. The
combinatorial heart of Cook–Levin (a TM run → tableau → CNF → SAT) is real and
done (the *sound tail*). The *front* (universal NP source → single-tape TM) is a
compiling skeleton plus `sorry`-free but **vacuous** reductions. The plan to
make it real is the **computable layer**: a small while-language (`Cmd`) with
explicit cost semantics, compiled once to `FlatTM` (`Compile`), so every
verifier and reduction is a short DSL program instead of a hand-rolled TM.

---

## Status snapshot (verified 2026-07-30-c)

| | |
|---|---|
| `lake build` | ✅ green (~10 min from cold; `S1Witness.lean` alone spends ~3 min in the kernel on the cost ladder's `decide`) |
| **`sorry`s in built code** | **0** (was 5; the legacy `⪯p` front and its three dead files were **deleted** 2026-07-30-c — none was to be proved) |
| **encoding-honesty audit (S5)** | ✅ **DONE 2026-07-30-c** — verdicts in the register below, evidence `probes/HonestyAuditProbe.lean`. Standing obligation for every *new* witness. |
| compiler (Risk C2) | ✅ **DONE & CLEAN** (2026-07-04): all 9 ops proven, no side-conditions; the retired trio + both isolation walls **deleted** |
| encodable sweep (Part 0.1) | ✅ **DONE (2026-07-04-b)**: real `encodable.size` on every proof-path type; the size-0 `instEncodableDefault` fallback **deleted**; `NPhard_GenNP` + all front bridges carry honest polynomial output-size bounds (axiom-clean) |
| **`#print axioms CookLevinHonest.CookLevin''`** | `[propext, Classical.choice, Quot.sound]` — ★ **`NPcomplete'' SAT`, UNCONDITIONAL** (2026-07-30-b). Both halves closed: `FrontS1Comp.SAT_NPhard''` (hardness) and `EvalCnfSplit.SAT_inNPLangFreeSplit` (membership). **The proof is done; what is left is the honesty audit (S5) and the deletion of the legacy front.** |
| ~~`#print axioms CookLevin`~~ | **DELETED 2026-07-30-c.** The legacy headline over the vacuous `⪯p` — and its whole feeding chain (`GenNP_is_hard`, the two S2 bridges, `IntermediateProblems`, `MultiToSingle`, the if-on-the-answer `Reductions/FlatSingleTMGenNP_to_FlatTCC`, `red_inNP`, `inNP_kSAT`) — was removed, not proved. `NP/SAT/CookLevin.lean` is now a pointer file carrying the demolition table. |
| `#print axioms SAT_inNP.sat_NP` | `[propext, Classical.choice, Quot.sound]` — **in-NP half sorry-free** (Route A, 2026-06-28) |
| `#print axioms EvalCnfSplit.SAT_inNPLangFreeSplit` | `[propext, Classical.choice, Quot.sound]` — **the membership half, UNCONDITIONAL** (2026-07-30-b). `EvalCnfSplit.certDecode_decodesAssgn` discharges the last register equation by `Cmd.eval_forBnd` + `Cmd.foldlState_range_induct` at the invariant `probes/SATSplitProbe.lean` §5 had already `#eval`-validated at every prefix length. Two findings: **frame facts belong in the write-set lemma, not the loop invariant** (FINDING AH), and **a `Bool`-valued invariant checked at every index before the proof is the cheapest de-risking move available** (FINDING AI — the proof consumed §5 verbatim, zero redesign, ~110 lines for an 11-op program). The program-generic `CookLevin''_of_decodesAssgn` / `_of_bridge` / `_of_decoder` are kept as the interface a different decoder plugs into. |
| `#print axioms FlatClique_in_NP` | `[propext, Classical.choice, Quot.sound]` — **FlatClique in-NP half sorry-free & axiom-clean** (2026-07-01; `cliqueRelDecidesLang` complete) |
| `#print axioms KSat3Free.inNP_kSAT3_free` | `[propext, Classical.choice, Quot.sound]` — **first live `red_inNP` through the free layer engine** (concrete re-encoder + reduction program, `NP/kSAT_to_SAT_free.lean`, 2026-07-02) |
| `#print axioms KSat3Free.kSAT3_reducesPolyMO'` | `[propext, Classical.choice, Quot.sound]` — **first live honest `⪯p'` on the real chain** (`kSAT 3 ⪯p' SAT` via `reducesPolyMO'_of_langFree`, 2026-07-02) |
| `#print axioms FlatTCCFree.flatTCC_reducesPolyMO'` | `[propext, Classical.choice, Quot.sound]` — **first sound-tail step as a live honest `⪯p'`** (`FlatTCC ⪯p' FlatCC`, unguarded map, `Reductions/FlatTCC_to_FlatCC_free.lean`, 2026-07-02) |
| `#print axioms FlatCCBinFree.flatCC_reducesPolyMO'` | `[propext, Classical.choice, Quot.sound]` — **`FlatCC ⪯p' BinaryCC` live** (guarded map + on-machine validity check; the unguarded map is provably incorrect for this step — `Reductions/FlatCC_to_BinaryCC_free.lean`, 2026-07-03) |
| `#print axioms FlatTCCBinComp.flatTCC_to_binaryCC_reducesPolyMO'` | `[propext, Classical.choice, Quot.sound]` — **first COMPOSED live `⪯p'`** (`FlatTCC ⪯p' BinaryCC` via the **first live `SeamData`/`comp`**, `Reductions/FlatTCC_to_BinaryCC_comp.lean`, 2026-07-03) |
| `#print axioms BinaryCCFSATComp.flatTCC_to_FSAT_reducesPolyMO'` | `[propext, Classical.choice, Quot.sound]` — **`FlatTCC ⪯p' FSAT`** (2026-07-12): the whole sound-tail prefix as ONE composed live `⪯p'` via the second live seam (`Reductions/BinaryCC_to_FSAT_comp.lean`); `BinaryCC ⪯p' FSAT` itself live since 2026-07-11 (`BinaryCCFSATFree.binaryCC_reducesPolyMO'`) |
| `#print axioms FSATSATComp.flatTCC_to_SAT_reducesPolyMO'` | `[propext, Classical.choice, Quot.sound]` — **`FlatTCC ⪯p' SAT` (2026-07-16): the WHOLE sound tail `FlatTCC → FlatCC → BinaryCC → FSAT → SAT` as ONE composed live `⪯p'`** via the third live seam (`Reductions/FSAT_to_SAT_comp.lean`); the last step `FSAT ⪯p' SAT` (`FSATSATFree.fsatSAT_reducesPolyMO'`, `Reductions/FSAT_to_SAT_free.lean`) is a complete free witness (run + cost ladders + mechanical fields). **The tail is DONE** — it waits on the front (S1/C8) for the endpoint hardness bridge |
| `NPhard'` endgame design | **SETTLED, machine-validated & VALIDATED LIVE** (2026-07-02/03): `SeamData`/`PolyTimeComputableLang.comp` fully proven and instantiated on real witnesses; `NPhard'`/`NPcomplete'` defined; hardness at chain endpoints only |
| `axiom` declarations | **0** |
| `#print axioms S1Map.s1Map_correct` | `[propext, Classical.choice, Quot.sound]` — **the S1 reduction map is correct** (2026-07-25, `Reductions/S1Map.lean`): the guarded map `s1Map` satisfies `FlatSingleTMGenNP x ↔ FlatTCCLang (s1Map x)`, with `s1Map_size_le` at `(2·(n+3))^10`. The `PolyTimeComputableLang` skeleton is up (`Reductions/S1Witness.lean`, both layouts pinned, output key injective, mechanical fields proven); only the program `s1Program` is open |
| `#print axioms S1Parse.stagePG_run` | `[propext, Quot.sound]` — **the S1 program's stages P (parse) and G (guard) are built** (2026-07-25-b, `Reductions/S1Parse.lean`, sorry-free): the machine register is parsed into a pinned scratch frame (registers 6–13) and `S1Map.s1GuardB` is decided on-machine into a flag, with `stagePG_usesBelow : UsesBelow 32`. Cost measured **cubic** (`probes/S1ParseProbe.lean`) — the parse is not the S1 budget driver. Stages Σ / I / C / F / M and the cost ladder remain open |
| `#print axioms S1Cards.cardBlocks_eq` | `[propext, Classical.choice, Quot.sound]` — **stage C (the card emitter) is DE-RISKED** (2026-07-25-c, `Reductions/S1Cards.lean`, sorry-free): the `Fin`-typed, `finRange`/`filterMap`-driven `guessCards M` is proven equal to `cardBlocks M`, seven nested `List.range` streams over the numbers stage P parses, with one equation per card family. Plus `normModel_eq` (the `normTrans` dedup as a three-number key pass + one halt-bit lookup) and `stageMNo` (the guard-false branch of the multiplex). ⚠ two measured findings: the prelude family is `Θ(σ³)`, **not** `Θ(σ⁶)`, and the emitter must append cell-by-cell (never `concat`) since `Op.cost concat` reads the whole destination |
| `encodable FlatTM` | ✅ **CORRECTED (2026-07-25)** to the data-field sum. The old `sizeFlatTM` charged a flat `5` per transition entry, which made the S1 witness's `encodeIn_size` obligation **unsatisfiable** (`probes/S1SizeGapProbe.lean`); zero ripple, full build green |
| `#print axioms S1Emit.stageInit_run` | `[propext, Classical.choice, Quot.sound]` — **the emitter atom + program stages Σ / I / F are built** (2026-07-26, `Reductions/S1Emit.lean`, sorry-free): `emitBlk` (a bare unary block appended cell by cell, never `concat`), `stageSig`, `stageInit`, `stageFin`, each with a pure `List.range` model proven equal to the `Fin`-typed definition (`initBlocks_eq`, `finBlocks_eq`). Findings: stage F needs no validity hypothesis; head-cell codes are maintained *incrementally* (no multiplication inside any loop) — the template stage C repeats seven times; and the guard is load-bearing for stage I |
| `#print axioms S1Program.noBranch_computes` | `[propext, Quot.sound]` — **the S1 reduction PROGRAM is assembled** (2026-07-26-b, `Reductions/S1Program.lean`): `s1Program = stagePG ;; ifBit FLG yesBranch stageMNo`, with the **guard-false half of `computes` proven outright and axiom-clean** (this lemma, quantified over an arbitrary yes branch so the placeholder stages stay out of its axiom list) and the guard-true half (`yesBranch_run`) proven modulo only `stageC_run` / `stageMYes_run`. `S1Witness.s1_reductionLang` now discharges `computes`, `usesBelow` and `decode_agree`; **`cost_le` is its only open field.** Probe: `probes/S1ProgramProbe.lean` (measured: the card register is `>99.8%` of the emitted output — **stage C alone is the cost ladder**) |
| `#print axioms S1CardEmit.cFive_run` | `[propext, Classical.choice, Quot.sound]` — **stage M-yes is CLOSED and five of stage C's seven card families are BUILT** (2026-07-26-c, `Reductions/S1Program.lean` + the new `Reductions/S1CardEmit.lean`, both sorry-free): `copyBlocks`, `copyRightBlocks` and the three halt families as real `Cmd`s, assembled as `cFive`, plus the reusable emitter loop principle `emitLoop_run`, the atoms `emitBlk2`/`emitId`, `loadX` and the gated `q` loop `haltFam`. `yesBranch_run` is now modulo `stageC_run` alone. ⚠ **measured (`probes/S1CardEmitProbe.lean` §3): `preludeBlocks` is ~96% of the card register** — the prelude family, not `stepBlocks`, is the cost ladder, which reverses the planned build order |
| `#print axioms FrontS1Comp.SAT_NPhard''_of_S1` | `[propext, Classical.choice, Quot.sound]` — **the whole HARDNESS half is `sorry`-free modulo ONE program meeting THREE contracts** (2026-07-27): `hcomputes` (`s1Extract (c.eval (headEncodeIn x)) = s1Key (s1Map x)`), `huses` (`UsesBelow c s1RegBound`), `hcost` (`c.cost (headEncodeIn x) ≤ S1Map.s1Bound (size x)`) ⇒ `NPhard'' SAT`. Front, both head seams, the S1 reduction and the entire sound tail are inside it; it does **not** route through `hasDeciderClassical` |
| `#print axioms FrontS1Comp.SAT_NPhard''` | `[propext, Classical.choice, Quot.sound]` — **`NPhard'' SAT` AT THE REAL PROGRAM, `sorry`-free** (2026-07-29-b). All three S1 contracts are now discharged at `S1Program.s1Program`: `computes` and `usesBelow` (2026-07-28-b) and `cost` (this entry's row above). The front, both head seams, the S1 reduction and the whole sound tail are inside it, and it does **not** route through `hasDeciderClassical`. Regression list: `probes/AxiomProbe.lean` (~33 endpoints). **S1 is finished; the critical path is now the membership half.** |
| `#print axioms S1SATComp.s1Bridge` / `FrontS1Comp.frontBridge` | `[propext, (Classical.choice,) Quot.sound]` — **the last two structural interfaces are validated** (2026-07-27): the fourth seam `Reductions/S1_to_FlatTCC_comp.lean` (S1 → the composed tail; `mfc` erases reg `0` + `[6,48)`, `[48,57)` closes by the length argument) and C8-5 `Reductions/Front_to_S1_comp.lean` (front → S1 on the frozen head layout; `mfc` erases `[5,57)`). Both `mfc`s are built from the reusable `S1SATComp.clearRange`; probe `probes/SeamS1Probe.lean` |
| `#print axioms S1Prelude.preludeBlocks_seg` | `[propext, Classical.choice, Quot.sound]` — **stage C's prelude family is emitter-shaped** (2026-07-27-b, `Reductions/S1Prelude.lean`, sorry-free): `preludeBlocks` (~96% of the card register) re-stated as `preludeSeg`, the nesting the `Cmd` implements. Four findings, each a theorem: kind loops are all *outside* the resolution loops (interleaving emits a permutation of an order-sensitive target); a kind is four numbers, not a pair-list register; `contigB` is one carried bit; the seven-segment kind split removes every on-machine comparison. Plus the reusable `emitList` and `minReg`, and the preamble `pPre` (`PConst`, incl. `min M.start M.states` and `1^((σ+1)(q0+1))`). ⚠ measured: `CDirty`'s 30 registers are **exactly** exhausted by this family, and the cost budget has ~12 orders of magnitude of slack. Probe: `probes/S1PreludeProbe.lean` |
| `#print axioms S1Prelude.cPrelude_run` | `[propext, Classical.choice, Quot.sound]` — **stage C's prelude family is BUILT** (2026-07-27-c, `Reductions/S1PreludeEmit.lean`, sorry-free): `cPrelude` is a real `Cmd` laying `encNats (preludeBlocks σ states (min start states))` onto `EOUT_C`, with `cPrelude_usesBelow` (48) and `PDirty_cdirty`. Reusable: the dirty-list-indexed emitter contract `Emits`/`EmitsFr` (+`seq`/`mono`), the register-generic gadgets `pRes`/`pSeg`/`pKindCmd` (each proven once, applied three times) and the value gadgets `setLit`/`loadSum`/`loadVal`/`setFlag`. ⚠ two findings: `PJᵢ` could **not** carry both the kind level's `add` and the resolution level's counter (the nest re-runs `49×` between write and read) — fixed by folding `add` into `PPAᵢ` (`preludeBlocks_seg'`); and a deep nest needs **nested** dirty lists, not one global one. Measured: `cPrelude.cost` is `2.8e5 … 1.2e7` against `S1Map.s1Bound = 1.0e13` at `n = 7`. Probe: `probes/S1PreludeEmitProbe.lean` |
| `#print axioms S1Step.stepBlocks_seg` | `[propext, Classical.choice, Quot.sound]` — **`stepBlocks` is DE-RISKED** (2026-07-27-c, `Reductions/S1StepModel.lean`, sorry-free): `stepSeg`/`stepBlocks_seg`/`entryBlocks_seg`/`stepSummand_seg` re-state the last family in the emitter's own nesting. Findings: every counter-reading branch is a *last-iteration* test, killed by `range_last`/`range_first_last`, so **stage C needs no unary comparison gadget at all**; an entry contributes exactly three symbol constants, all hoistable; `mv` is entry-constant so one three-way `ifBit` chain wraps the body. Probe: `probes/S1StepModelProbe.lean` (196 tuples incl. `σ = 0`, all `mv`, out-of-range `mVal`/`wVal`) |
| `#print axioms S1Step.stepEmit_run` | `[propext, Classical.choice, Quot.sound]` — **`stepBlocks`'s ENTRY BODY is BUILT** (2026-07-28, `Reductions/S1StepEmit.lean`, sorry-free): `stepEmit` emits one normalised entry's cards off `SConst` (free from `cFive` — `S1CardEmit.cFive_const`) + `SEntry` (the entry's nine numbers), touching nothing outside `SD1`; plus `stepEmit_usesBelow` (48), the card atom `emitCard`/`card6_run` and the four `mv`-independent loop nests. ⚠ two findings: parameterise a family gadget by its innermost **body**, not by its branch condition (3 × 4 emitters → 4 loop lemmas + 11 cards); and **`emitLoop_run` does not fit a cursor-driven loop** (it pins the output to the iteration index) — hence the new **`emitFold_run`**, a stateful loop principle, with the entry loop's pure model `stepGo` and its target `stepSummand_fold`. Probe: `probes/S1StepEmitProbe.lean` |
| `#print axioms S1Program.s1Program_computes` / `s1Program_usesBelow` | `[propext, Classical.choice, Quot.sound]` — **the S1 reduction PROGRAM IS FINISHED** (2026-07-28-b, `Reductions/S1StepLoop.lean` + `S1Program.stageC`, both sorry-free): the per-entry preamble `entryPre` (entry parse off a `PTRANS` cursor, both head-cell bases, the three symbol constants, the two move flags, the halt lookup, the dedup scan, the key push), the entry loop `stepFam` (`emitFold_run` at `(seen, remaining entries)`), and `stageC = cFive ;; stepFam ;; cPrelude`. **Two of the three contracts of `SAT_NPhard''_of_S1` are now discharged at the real program**; only `S1Witness.s1Program_costLeSize` is open. Three findings: a cursor loop's body must be **total** (`emitFold_run`'s `hstep` is quantified over every index → guard it with one `nonEmpty` on its own cursor; a guarded loop then needs only an *upper* bound on its iteration count); the machine accumulator must match its model's **cons order** (`concat SSEEN item SSEEN` prepends); and `stageC_run`'s pinned contract had been **missing its `PSTART` hypothesis** since 2026-07-26-b — nothing noticed until the prelude family had to be wired in. Stage C's 30-register licence is now exactly full. Probe: `probes/S1StepLoopProbe.lean` (the first end-to-end `#eval` of `s1Program`; cost `3.6e5` vs a budget of `1.1e15`, floor `> 6·10^8`) |
| the one-cap cost ladder (`Lang/CostPoly.lean`) | **DELETED 2026-07-30-b** (FINDING AJ). Built 2026-07-28-c, superseded three days later by `Cmd.CapCost`: a *single* cap cannot survive a `forBnd` at all (FINDING Z), so it was a rejected design every future reader would have had to re-reject. Measured before deleting: `CostGrow` imported it but used nothing from it. `Cmd.get_length_eval_le` and `Cmd.forBnd_counter_le` moved to `Lang/CostFlat.lean`; `probes/CostChkIntentProbe.lean` now pins `Cmd.chk`'s accept/reject intent in ~5 s. |
| `#print axioms Complexity.Lang.Cmd.chk_sound` | `[propext, Classical.choice, Quot.sound]` — **the cost ladder is CLOSED** (2026-07-29 designed, 2026-07-29-b landed; `Lang/CostGrow.lean`, sorry-free). ⚠ **FINDING Z**: a cost predicate with ONE cap cannot survive a `forBnd` (the body's outputs are re-capped at `poly(M)` each iteration → a **tower**). `Cmd.CapCost c F F'` uses **two** caps (frozen `MF`, global `N`): cost `≤ K·(MF+1)^D·(N+1)`, growth `≤ N + K·(MF+1)^D`, `F'` still `≤ MF + K·(MF+1)^D`. Cost linear in `N` pays for **FINDING X** for free; growth independent of `N` stops compounding. `Cmd.chk C c = (ok, C', B)` is ONE decidable forward pass; `Cmd.costLeSize_of_chk c F (by decide +kernel)` is the one-liner that closes `S1Witness.s1Program_costLeSize`. Three measured design constraints: **FINDING AA** register sets must be `Nat` bitmasks (`cPrelude.writes` is a 327411-element list; the `List Var` checker was quadratic in program size and never terminated) and `Nat.ldiff` is unusable in the kernel; **FINDING AB** the kernel's wall is *memory* — a two-traversals-per-loop version was OOM-killed at 15 GB, so each body is visited once and a second pass is paid only where the first is rejected; **FINDING AC** `C'`/`B` must be sound even when `ok` is false, because an enclosing loop's promotion is read from them and is what makes the rejected sub-command acceptable. What closed the last two loops (both in `S1StepLoop.scanSeen`) is flow sensitivity (`concat SSEEN SAX SSEEN` — `SAX` is capped by the straight-line prefix of the same body) plus the `NoGrow`-widened frozen set (`SCUR`'s bound is *idempotent*, so the 4-deep chain `SCUR → SKQ/SKT/SKV → SAX → SSEEN` is walked in ONE pass instead of four circular rounds of promotion). Measured: accepts the whole program, ~2 s `#eval` / ~3 min `decide +kernel` (`probes/S1GrowSafeProbe.lean`). |
| Genuine `sorry`s (Group C) | **0** (2026-07-30-c). The last five were `red_inNP`'s `inTimePoly` half, `hasDeciderClassical` and 3× `MultiToSingle`; all were on the legacy `⪯p` path and were **deleted with it, not proved**. None was ever on the `NPhard''` path — the S1 cost obligation `S1Witness.s1Program_costLeSize` was the last one there and closed 2026-07-29-b. CI now fails on any new `declaration uses 'sorry'`. **`Simulators/CookTableau.lean`/`GuessTableau.lean` are fully `sorry`-free** — `cookTableau_correct`, `guessTableau_correct`, and **both size bounds** (`≤ (2·(n+1))^10`, 2026-07-24) all sorry-free & axiom-clean |
| `sorry`-free **vacuous** defs (Group S) | **none** (2026-07-30-c). All three are gone: S1's if-on-the-answer map and S2's dummy bridges were deleted with the legacy front, and the size-0 hardness reduction was closed by Part 0.1. ⚠ This group existed *because* `#print axioms` cannot see it — the successor risk of the same kind is **S5** (encoding honesty), which is audited but standing. |
| Proof-path size | ~16K LOC under `CookLevin/`; ~15K parked |
| Remaining to a real proof | **none.** The honest theorem is proven, audited and `sorry`-free. Remaining work is scope extension and hygiene — see [`HANDOFF.md`](HANDOFF.md). |

> **The `sorry` count is not the soundness metric.** Closing every `sorry`
> leaves S1/S2/S3 intact. Track Group S (soundness) and Group C (completion)
> separately.

---

## The proof path

There is now exactly **one** chain. The legacy `⪯p` chain from `GenNP` (with its
two dummy S2 bridges, its if-on-the-answer S1 step and `hasDeciderClassical`) was
**deleted** 2026-07-30-c — see `NP/SAT/CookLevin.lean` for the demolition table.

```
Q ⪯p' FlatSingleTMGenNP ⪯p' FlatTCC ⪯p' FlatCC ⪯p' BinaryCC ⪯p' FSAT ⪯p' SAT
└─ C8 front ─┘└─ S1 ─┘└──────────────── the sound tail ───────────────────┘
        = ONE composed `PolyTimeComputableLang` witness = `NPhard'' SAT`
```

for every `Q` presented with a split free-line verifier witness
(`InNPWitnessLangFreeSplit`: a real `Cmd` verifier over a bit-level layout with
`List Bool` certificates). Composition is at the `Cmd` level, five
`SeamData`/`comp` seams; hardness is proven at the chain endpoint only. The
membership half is `EvalCnfSplit.SAT_inNPLangFreeSplit`, and
`CookLevinHonest.CookLevin'' : NPcomplete'' SAT` is the headline. **Zero `sorry`s
in built code; no endpoint prints `sorryAx`.**

---

## What we know (validated foundations + this-session findings)

- **The honesty audit surface of a composed witness is TWO functions
  (2026-07-30-c, FINDING AK).** `PolyTimeComputableLang.comp` sets
  `encodeIn := Wf.encodeIn` and `decodeOut := Wg.decodeOut`, and
  `toFrameworkWitness'` hands exactly those two to `ComputesBy` as
  `encode`/`decode`. Every *intermediate* witness's `encodeIn` appears only on
  the **right** of a `SeamData.bridge` obligation — the composed program is
  required to produce that state — so a dishonest intermediate layout cannot
  license a cheat, only make the bridge harder. This is what turned "audit six
  witnesses × two fields" into "read `FrontWitness.encodeInQ` and
  `FSATSATFree.decodeOut`". Machine-checked in `probes/HonestyAuditProbe.lean`
  §1. **Any future chain extension inherits it: audit the new head's `encodeIn`
  or the new tail's `decodeOut`, and nothing else.**

- **The structures genuinely do not enforce honesty — and now we have the
  counterexample (2026-07-30-c).** `probes/HonestyAuditProbe.lean` §6 is a
  complete, `sorry`-free `PolyTimeComputableLang (fun n => n * n)` whose program
  is the layer's no-op and whose `encodeIn` lays the *answer* on the tape; it
  discharges every field and yields a real `polyTimeComputable'`. Risk S5 is
  therefore a permanent *reading* obligation on every new witness, not a
  one-time task. Keep it in the register.

- **The sound tail is genuine.** `FlatTCC → FlatCC → BinaryCC → FSAT → SAT`,
  `kSAT_to_SAT`, `kSAT_to_FlatClique` are real reductions with real correctness
  proofs (audited). Their `if isValidFlattening …` guards test a decidable
  property of the *input*, which is legitimate. Do not touch their content; the
  only future change is re-threading the witness type (S3 migration).

- **The S3 target is faithful.** `polyTimeComputable'` (`ComputesBy`: a real
  `FlatTM` halting within a polynomial *time* bound and decoding to `f x`)
  captures genuine poly-time computation, and *extends* the size-only witness
  (`polyTimeComputable'_to_polyTimeComputable`), so the size-bound lemmas in
  `NP.lean` survive verbatim. The forcing function is confirmed
  (`s1_witness_forces_decider`): an honest witness for an if-on-the-answer map
  yields a poly-time decider for the NP source, which a many-one reduction may
  not have — so S1/S2 *stop typechecking* under the upgrade.

- **The layer composes on the FREE line (C9 retired, C4/C6 done & LIVE).**
  Free `DecidesLang`/`PolyTimeComputableLang` witnesses with bespoke bit-level
  encodings, composed per seam by concrete re-encoder `Cmd`s
  (`DecidesLang.FreePrecomposeData`/`precomposeFree`,
  `InNPWitnessLangFree.precompose`, `red_inNP_of_langFree`,
  `reducesPolyMO'_of_langFree`) + the framework decider bridges
  (`DecidesLang.toDecidesBy`/`toInTimePoly`, via the `bitTestTM` tape→state
  gadget and runtime tape-padding) + the `forBnd` loop toolkit. All live &
  axiom-clean (`inNP_kSAT3_free`, `kSAT3_reducesPolyMO'`). **The canonical
  shared-encoding layer (`LangEncodable`/`PolyTimeComputableLang'`/
  `DecidesLang'`/`inNPLang` + `swap`/`map_fst`/`map_snd`) was RETIRED &
  deleted 2026-07-02**: its generic product encoding is size-unsound
  (`probes/UnaryProductSizeProbe.lean`), it could never be populated for the
  live pair-typed states, and the audit showed no remaining witness needs it.
  Do not rebuild it. ⚠ Two standing constraints (HANDOFF "standing
  architecture risks"): encoding honesty is per-witness *discipline* (the
  structures don't enforce it), and there is deliberately **no generic
  `⪯p'`-transitivity** (opaque TM-backed witnesses cannot be honestly
  composed) — chains compose at the `Cmd` level, so the migrated `NPhard'`
  transport must be designed around that.

- **S2 needs no simulator.** `TM σ n` erases the tape count (`TM_tapecount_phantom
  : TM Bool 2 = TM Bool 1` by `rfl`), the predicates ignore the machine, and
  `bridgeMachine` accepts everything. `LMGenNP` reduces *directly* to the
  single-tape target (`LMGenNP_to_TMGenNP_singleTM_direct`). Retiring S2 =
  collapse the phantom bridges and bind the predicates to the single-tape layer
  decider; **folded into C8**. `Simulators/MultiToSingle.lean` was dead code and is **deleted** (2026-07-30-c), along with all three bridges.

- **S1 is feasible but expensive — and its target is now TRUE and decomposed
  (2026-07-17).** A risk review found the v1 bijection **false as stated**:
  the flat tape's zero-padding jump-writes let one TM step rewrite cells
  arbitrarily far from the head — inexpressible by any local card family.
  The semantics were **fixed** (`writeCurrentTapeSymbol`: append-only at the
  frontier, beyond-frontier writes void; 2-file fallout, all call sites were
  already at the frontier), and v2 of `Simulators/CookTableau.lean` landed
  the complete card algebra (boundary marker, `normTrans` key-dedup, three
  window positions + incoming-head + halt-freeze families, the
  frontier-sensitive `wEff` write effect), the corrected statement (with the
  previously-missing `validFlatTM`/`tapes = 1`/alphabet hypotheses), a
  10-sub-lemma skeleton with the assembly PROVEN, and a green `#eval`
  agreement probe (`probes/S1TableauProbe.lean`). **Direction (1a) + its
  gates are PROVEN (2026-07-18)** — `stepFlatTM_normM`, `ConfFits_step`,
  `validStep_of_step`, `validStep_of_halt`, `satFinal_of_halt`, all
  axiom-clean, on a reusable window machinery — **`halt_of_satFinal` is
  PROVEN (2026-07-18-b)** on the cell-code disjointness algebra (also the
  (1b) inversion's card-classification fodder), and the chain-head input
  layout is **FROZEN** (`Reductions/HeadLayout.lean`, unblocking C8-5
  planning; C8-3's emitters — `Reductions/FrontPieces.lean` — are DONE
  against it). **Directions (2)/(3) are PROVEN (2026-07-18-c, after the
  machine-checked phantom-head defect at the right row edge was fixed by a
  right boundary marker), and the (1b) inversion `step_of_validStep` is
  PROVEN (2026-07-18-d) — the whole bijection `cookTableau_correct` is
  sorry-free & axiom-clean.** **The prelude/cert-guess layer is COMPLETE
  (2026-07-19-b, `Simulators/GuessTableau.lean`)**: a band-disjoint prelude
  alphabet (`PSg = Sg + 2·sig + 5`) turns `∃ cert` into row-0 nondeterminism,
  reusing the deterministic core UNCHANGED through a value-preserving
  embedding; `guessTableau_correct` is sorry-free & axiom-clean (P1/P2 +
  Γ-band transfers all proven). **Both size bounds
  `cookTableau_size_bound`/`guessTableau_size_bound` are PROVEN (2026-07-24,
  `≤ (2·(n+1))^10`), so both tableau files are fully `sorry`-free.**
  **The reduction MAP is DONE & axiom-clean (2026-07-25,
  `Reductions/S1Map.lean`)**: the decidable guard `s1GuardB` (+
  `isValidFlatTM_iff`), the guarded map `s1Map`, the correctness iff
  `s1Map_correct`, and `s1Map_size_le`. ⚠ the guard is **mandatory** here —
  unlike `FlatTCC → FlatCC`, the unguarded map is unsound backwards (an
  invalid `M` still yields a possibly-coverable tableau). The witness skeleton
  (`Reductions/S1Witness.lean`) pins the input layout (frozen `headEncodeIn`)
  and the output layout (`FlatTCCFree.encodeIn` verbatim on regs 1–5, so the
  next seam is a pure scrub of reg 0 and `[6, 57)`), proves the output key
  injective and every mechanical field.
  **Stages P (parse) and G (guard) of the program are DONE (2026-07-25-b,
  `Reductions/S1Parse.lean`, sorry-free & axiom-clean)**: `stagePG_run` parses
  `encSyms (flattenTM M)` into a pinned scratch frame and decides
  `S1Map.s1GuardB` on-machine, and `stagePG_usesBelow`/`stagePG_frame` fix the
  register frame every later stage lives in. Two findings: the parse is
  **cubic** (so not the budget driver — the whole degree-10 budget belongs to
  the card emitter), and it **never desynchronises even on invalid machines**
  (`flattenEntry` writes each list's own length before its payload), so neither
  stage carries a validity hypothesis.
  **Stage C's pure model is DONE (2026-07-25-c, `Reductions/S1Cards.lean`,
  sorry-free & axiom-clean)**: `cardBlocks_eq` restates the whole card stream
  as seven `List.range` nests over the parsed numbers (one proven equation per
  card family), `normModel_eq` specifies the `normTrans` dedup on-machine, and
  `stageMNo` closes the multiplex's guard-false branch.
  **The emitter atom and stages Σ / I / F are BUILT (2026-07-26,
  `Reductions/S1Emit.lean`, sorry-free & axiom-clean)**, and **the program is
  ASSEMBLED (2026-07-26-b, `Reductions/S1Program.lean`)**: `s1Program =
  stagePG ;; ifBit FLG yesBranch stageMNo`, `computes` proven — the guard-false
  half outright and axiom-clean, the guard-true half modulo only the two stage
  contracts `stageC_run` / `stageMYes_run` — and `usesBelow` / `decode_agree`
  closed, so `s1_reductionLang` is down to `s1Program_costLeSize`. **Both head
  seams landed 2026-07-27**, so `NPhard'' SAT` now follows from the three S1
  contracts alone (`FrontS1Comp.SAT_NPhard''_of_S1`, axiom-clean).
  **Stage M-yes is CLOSED and five of stage C's seven card families are built
  (2026-07-26-c, `Reductions/S1CardEmit.lean`). The prelude family — the
  remaining cost driver — was made emitter-shaped 2026-07-27-b
  (`Reductions/S1Prelude.lean`): `preludeBlocks_seg` fixes the `Cmd`'s
  structure, `emitList`/`minReg` are the two atoms the last two families need,
  and `pPre` supplies `min M.start M.states` and the head band's base.
  **The prelude's `Cmd` landed 2026-07-27-c** (`Reductions/S1PreludeEmit.lean`,
  sorry-free & axiom-clean) together with `stepBlocks`' emitter-shaped model
  (`Reductions/S1StepModel.lean`).
  **`stepBlocks`'s entry body landed 2026-07-28** (`Reductions/S1StepEmit.lean`),
  with the entry loop's pure model and the stateful loop principle it needs, and
  **the per-entry preamble, the entry loop and the `stageC` assembly landed
  2026-07-28-b** (`Reductions/S1StepLoop.lean`). **S1 IS FINISHED (2026-07-29-b).**
  The program is complete and all three of its contracts are axiom-clean:
  `s1Program_computes`, `s1Program_usesBelow` (2026-07-28-b) and the
  whole-program cost ladder `S1Witness.s1Program_costLeSize`, proven by one
  decidable syntactic pass (`Cmd.chk`, `Lang/CostGrow.lean`) with no register
  table, no invariant and no `_run` lemma. `FrontS1Comp.SAT_NPhard''` — the
  whole hardness half of Cook–Levin — is `sorry`-free and axiom-clean. Alphabet `|Σ|=(M.sig+1)(M.states+2)+1`; the card list is
  `Θ(|trans|·|Σ|⁴)` encoded (counts pinned by
  `cookCards_length_le`/`preludeCards_length_le`).

- **C2 is the linchpin — and is under-built (this session's headline finding).**
  Everything (both the reduction side `toFrameworkWitness'` and the decider side
  `inNPLang_to_inNP`) routes through `Compile_sound` / `Compile_run_physical`.
  The *combinators* are proven (`compileSeq_compose_physical`, `loopTM_run`,
  `bitTestTM`) and a ~1.6K-LOC gadget library is sorry-free. **But:**
  - 10 of 12 `compileOp`s are `compiledCmd_default` stubs; only
    `appendOne`/`appendZero` have real TM bodies.
  - All `compileOp_sound` / `compileSeq_sound` / `compileForBnd_sound` /
    `compileIfBit_sound` and the `Compile_sound` assembly are `sorry`.
  - The gadget run-lemmas *do* carry explicit step counts at the lower level
    (`scanInsert_run`, `insertCarryTM_run`: `body.length + … + post.length + …`);
    only the top-level `appendAt_run` existentializes them. So step counts are
    recoverable — but they expose a **cost-model bug** (next bullet).
  - **`compileOp_sound` is FALSE as stated** — and there are now **three
    independent reasons** (reasons 1–2 below; the third, the *budget shape*, is
    the May-2026 finding recorded after these).
    1. *(register-count bug, prior session)* Its budget `Compile.overhead
       (State.size s + cost)` uses `State.size`, which counts register *contents*
       but **ignores the register count**, whereas `appendAtTM`'s step count grows
       with the **tape length** `(encodeTape s).length = State.size s + s.length +
       1`. Witness: `s = List.replicate 6 []` has `State.size s = 0`, budget
       `overhead 1 = 4`, but `opAppendOne 0` first halts at **step 10**. Partial
       fix: the per-op budget over the **tape length**
       `Compile.overhead ((encodeTape s).length + cost)`. **This is now PROVEN for
       the real ops** — see "Progress this session".
    2. **(cost-model gap — now FIXED).** The original ops were **unit cost**
       (`Op.cost _ _ = 1`), but `concat`/`copy`/`tail`/`takeAt`/`dropAt`/`consLen`
       can grow `State.size` **multiplicatively** in one step. So a unit-cost
       program could have **output size exponential in its layer cost** (evaluated:
       `doubler := forBnd 2 1 (op (concat 0 0 0))` at `n = 10` → output length 1047
       vs even the corrected budget 676; at `n = 19`, 524329 vs 1936). **No
       fixed-degree budget polynomial could bound `Compile c`** — the unit-cost
       model was not a faithful proxy for TM time. **Fix implemented (the chosen
       option, Coq-L-calculus-aligned):** `Op.cost` now charges the size-increasing
       ops for their source data, so `State.size (Op.eval o s) ≤ State.size s +
       Op.cost o s` (`Op.size_eval_le`, proven; it was *false* under unit cost).
       *Options weighed:* (a) a separate per-witness size/weight bound and (c)
       removing size-increasing ops were both rejected — there is **no global
       `weight ≤ poly(unitCost, size)`** (size-doubling has weight exponential in
       op count), so the realistic single cost notion is necessary and lowest in
       permanent complexity; (c) is mathematically identical but needs surgery on
       the `Op` inductive. The concrete witnesses' cost bounds were re-derived
       (`id`, `swap`, `map_fst`), since their unit-cost bounds certified the wrong
       quantity. The **Cmd-level** residual (the `forBnd` counter) is **now CLOSED**
       — see reason 3 / Progress.
    3. **(budget shape — NEW, May 2026; the per-fragment budgets cannot compose).**
       The corrected per-op budget was loosened to the **quadratic** `overhead
       (tapeLen + cost) = (·+1)²`. But a quadratic is **not superadditive**, so
       summing `~cost` per-op quadratics gives a **cubic** — the per-fragment
       budgets in `compileSeq_sound`/`compileIfBit_sound`/`compileForBnd_sound` (and
       hence `Compile_sound`) are too weak to imply their composed conclusions:
       worst case `overhead(a) + 1 + overhead(a + c₂) ≤ overhead(a + 1 + c₂)` is
       **false for `a ≥ 2`** (`a = 3, c₂ = 1` → `42 ≰ 36`; gap grows with `a`). So
       **these four lemmas are unprovable as stated.** Fix: per-fragment budgets
       must be **LINEAR** in tape length — the gadgets prove it
       (`appendAt_steps_le: ≤ 2·tapeLen+3`), and linear bounds *do* compose into a
       quadratic total (`Σ_{~cost} O(tapeLen) ≤ O(cost·(size+cost+regBound)) =
       O((size+cost)²)` as `cost ≤ size+cost`). The **total** `Compile_run_physical`
       budget then needs a quadratic with constant/`regBound` slack (the tight
       `(size+cost+1)²` cannot cover constants; safe — `toFrameworkWitness'` only
       needs `inOPoly`). See the finding block above `compileSeq_sound` in
       `Compile.lean`.
  - **Progress** (`Lang/AppendGadget.lean`, `Lang/Compile.lean`, `Lang/Semantics.lean`,
    `Lang/Frame.lean`, `Lang/PolyTime.lean`; all sorry-free & axiom-clean):
    `appendAt_run_steps` re-proves `appendAt_run` with an **explicit step count**
    (`appendAt_steps`), `appendAt_steps_le` bounds it by `2·tapeLen + 3`, and
    `compileOp_appendOne_sound`/`compileOp_appendZero_sound` discharge the
    behavioural part of `compileOp_sound` for the two real ops at **general `dst`**
    (reason #1 closed for them, modulo the budget-shape restatement in reason #3).
    The **realistic cost model** (reason #2) is implemented: `Op.cost` size-aware,
    `State.size_set_add` + `Op.size_eval_le`, `Op.cost_agree`/`Cmd.cost_agree`
    generalized, witnesses re-derived. **The Cmd-level size bound (reason #2
    residual) is now PROVEN:** `Cmd.size_eval_le : State.size (c.eval s) ≤
    State.size s + c.cost s`, by charging the `forBnd` counter (`Cmd.run` adds
    `iters*iters`) — clean and depth-constant-free, replacing the proposed
    register-exclusion route. **Surfaced reason #3** (budget shape) by checking the
    arithmetic of the sorried per-fragment lemmas.

---

## The plan from here

⚠ **Destination A is REACHED and CLOSED OUT.** `NPcomplete'' SAT` was proven
2026-07-30-b; the honesty audit (S5) and the legacy-front deletion — the last two
items on the plan — landed 2026-07-30-c. **There is no remaining item on this
plan.** Destination B, the fallback, was never needed. Everything below is kept
as the finding log that got there; the live plan is in
[`HANDOFF.md`](HANDOFF.md), and it is now *scope extension* and *hygiene*, not
completion.

### Destination A — real, unconditional `CookLevin`

Ordered by dependency. The two highest-risk items are **C2** (the compiler, now
known to need step-bound machinery) and **S1** (the Cook tableau).

1. **Finish the compiler (C2). — ✅ DONE (2026-07-04).** The residue-contract
   compiler chain (`Compile_run_physical_residue` → `bitDecider_run` →
   `paddedBitDecider_run`/`paddedCompute_run`) is proven for all 9 ops, and
   `compileOp_sound_physical_residue` is fully proven with no side-conditions.
   The value-as-length trio (`takeAt`/`dropAt`/`consLen`) and both isolation
   walls (`NoConsLen`, `IsSupported`/`AllOpsSupported`) are **deleted**
   (2026-07-04) — `Op` has exactly the 9 live constructors and the chain carries
   no wall threading. No C2 work remains.
   The sub-items below are kept as the historical finding log.
   a. **Cost model — DONE.** `Op.cost` is size-aware (`Op.size_eval_le`), and the
      **Cmd-level size bound is now proven**: `Cmd.size_eval_le : State.size
      (c.eval s) ≤ State.size s + c.cost s` (`Lang/Semantics.lean`), sorry-free and
      axiom-clean. The clean bound *was* false for `forBnd` (the unary loop counter
      is uncharged size); rather than the register-exclusion route (depth-dependent
      constant), it was fixed by **charging the counter in the cost model** — the
      same faithfulness principle as the size-aware `Op.cost` (materialising
      `replicate i 1` costs Θ(i) TM steps). `Cmd.run`'s `forBnd` now adds
      `iters*iters` (closed-form lump ≥ Σ_{i<iters} i, kept outside the fold so the
      frame/locality lemmas are untouched). Ripples were contained:
      `Cmd.cost_forBnd_le` (+ `iters*iters`, no external consumers) and
      `Cmd.cost_agree`. This gives `maxIntermediateTapeLen ≤ O(size + cost +
      regBound)` (linear, no depth constant). **The linear tape-length bound is
      now PROVEN:** `Cmd.encodeTape_eval_length_le : (encodeTape (c.eval s)).length
      ≤ State.size s + c.cost s + max s.length k + 1` (`Lang/PolyTime.lean`), built
      from `Compile.encodeTape_length` (tape = contents + count + 1),
      `Cmd.size_eval_le` (contents), and `Cmd.eval_length_le` (register count ≤
      `max start regBound`, `Lang/Frame.lean`). **Remaining (1a):** thread this
      *per-fragment output* bound through the actual run as a **max over fragment
      boundaries** (needs the physical run structure from 1b/1d), then restate
      `PolyTime.toFrameworkWitness'`'s time budget.
   b. **⚠ Budget shape — FINDING (do not prove the four `compile*_sound` lemmas as
      stated).** The per-op budget had been loosened to the **quadratic**
      `Compile.overhead ((encodeTape s).length + cost) = (·+1)²`. That is the
      **wrong direction**: quadratics are not superadditive, so summing `~cost`
      per-op quadratics gives a **cubic**, and
      `compileSeq_sound`/`compileIfBit_sound`/`compileForBnd_sound`/`Compile_sound`
      are **unprovable as stated** — worst case `overhead(a)+1+overhead(a+c₂) ≤
      overhead(a+1+c₂)` is false for `a≥2` (numerically: `a=3,c₂=1` → `42 ≰ 36`).
      Fix: state each per-fragment budget **LINEAR** in tape length — the gadgets
      prove it (`AppendGadget.appendAt_steps_le: steps ≤ 2·tapeLen+3`), and the
      append ops **now carry that linear budget** (`compileOp_appendOne_sound` /
      `compileOp_appendZero_sound`, the `decodeTape`-equality form). Linear bounds
      compose: `Σ_{~cost frags} O(tapeLen) ≤ O(cost·(size+cost+regBound)) =
      O((size+cost)²)` since `cost ≤ size+cost`. Then the **total**
      `Compile_run_physical` budget must be a quadratic **with constant/`regBound`
      slack** (e.g. `C·(size+cost+regBound)²` or a cubic) — the tight
      `(size+cost+1)²` cannot cover the constants; safe since `toFrameworkWitness'`
      only needs `inOPoly`. Thread the register count (≤ `regBound`) and give each
      gadget a per-fragment *physical contract* (head rewound to `0`, tape
      `= encodeTape output`, explicit halt step `t`, no-early-halt trajectory,
      `t ≤ linear(tapeLen)`). See the finding block above `compileSeq_sound`.

      **2026-05-29 — left-sentinel finding + migration (DONE).** The physical
      contract's "head rewound to `0`" was **not implementable on the old
      encoding**: `composeFlatTM_run` (verified) *preserves* the head across the
      seam, so each fragment must rewind itself; but a TM head clamps at `0`
      under `Lmove` *without detecting it*, so rewinding needs a
      uniquely-detectable left sentinel at index `0`, which `encodeRegs s ++
      [endMark]` lacked. The rewind *lemmas* already existed (`scanLeft_run`,
      packaged as `ScanLeft.rewindToStart_run`/`_traj`). **✅ The leading-sentinel
      encoding migration (step 1b-0) is now DONE:** `encodeTape s = endMark ::
      (encodeRegs s ++ [endMark])` (reuse `3`, `sig` stays `4`); `decodeTape`
      drops the leading sentinel; `appendBit_sound` folds the sentinel into the
      first marker-free block (so the append op still runs from head `0`, no
      head-bridge); `bitTestTM` reworked to step past the sentinel then read;
      `bitDecider_run` budget `+2→+3`; framework `DecidesBy.encode_size` loosened
      `2·size+3→2·size+4`. `lake build` green (3356), axiom-clean.

      **2026-05-30 — rewind finding + per-op physical contract (1b-2 DONE for the
      append op).** ⚠ The gadget exits with its head **on the trailing
      terminator** (`endMark = 3`, the *last* tape cell — `insertCarryTM_run`
      ends there), **not** "left of" it. Verified by `#eval`. So a bare
      `scanLeftUntilTM 4 3`/`rewindToStart_run` started there **halts immediately**
      (reads its target on the first cell) and never rewinds. Fix shipped (all
      sorry-free, axiom-clean): `ScanLeft.rewindFromEndTM = composeFlatTM
      stepLeftTM scanLeftUntilTM` (one unconditional `Lmove` off the terminator,
      then scan left to the leading sentinel; `rewindFromEndTM_run`/
      `_no_early_halt`); `AppendGadget.appendAtThenRewindTM` +
      `appendAt_rewind_run`/`_no_early_halt` (gadget-level physical contract,
      head→`0`); and `Compile.appendBit_physical` (the `encodeTape`-level
      contract: head-`0` exit, tape = `encodeTape output`, trajectory, **linear**
      budget `t ≤ 3·tapeLen + 6`) with reusable `encodeTape` structure lemmas
      (`encodeTape_get_zero`/`_lt_four`/`_interior_ne_endMark`).

      **2026-05-31 — ⚠⚠ BLOCKING FINDING: the physical tape never shrinks; the
      exact-tape contract is unsatisfiable for length-DECREASING ops (do NOT
      follow the `appendBit_physical` pattern for `opClear`/etc.).** Machine-
      checked in `Complexity/Complexity/TapeMono.lean`: `writeCurrentTapeSymbol`
      keeps `right` the same length (in-range) or grows it (pad), `moveTapeHead`
      never touches `right`, so `right.length` is monotone non-decreasing along
      every run (`runFlatTM_single_length_le`, `runFlatTM_initFlatConfig_no_shrink`,
      axiom-clean). But `compileOp_sound_physical` demands the exit tape be
      *exactly* `encodeTape (Op.eval o s)`; for `clear`/`tail`/shrinking
      `copy`/`head`/`eqBit`/`nonEmpty`/length-ops that is a **shorter** list than
      the input, which **no run can produce** (concrete proof:
      `Compile.clear_physical_unsatisfiable`). Only `appendOne`/`appendZero`
      (pure growth) fit. **Resolution (validated, not yet built): a residue-
      tolerant contract** — exit tape `encodeTape output ++ residue` with
      `residue` terminator-free, hidden existentially in a `TapeOK` relation so
      composition needs no residue bookkeeping. Already proved this session:
      `Compile.decodeTape_encodeTape_append` (decode ignores residue + head — the
      foundation). Still to build: (i) a **two-phase rewind** (scan-left to the
      real terminator, step left, scan-left to the leading sentinel — both are
      `3`, distinguished by the terminator-free interior/residue); (ii) the
      missing **`deleteCarryTM`** left-shift primitive (mirror `insertCarryTM`,
      filling vacated cells with `0`); (iii) restate the four
      `compile*_sound_physical` with `TapeOK`. **Next:** items (i)–(iii), then
      the 10 stub ops (1c), then assemble (1b-3/1b-4/1d). See HANDOFF
      "THE FINDING" + "Next step".
   c. Concretise the stub `compileOp`s, each with its residue contract.
      **✅ 2026-06-03 — the `clear` op is now FULLY proven** (run + trajectory +
      the quadratic budget `t ≤ 9·tapeLen²+9`) in
      `compileOp_sound_physical_residue`, joining `appendOne`/`appendZero`. The
      step-bound was threaded through the whole clear chain (each run lemma gained
      a `∧ t ≤ linear` conjunct) and assembled with the reusable
      `Compile.loopBudget_le` + `Compile.clearBudget_arith`. **⚠ Budget-constant
      risk surfaced:** `9·tapeLen²+9` is *tight* (needs `n+2 ≤ tapeLen` and tight
      per-iter constants); since each cross-register op internally composes
      `clear ⨾ copyBlock ⨾ transform` (each `Θ(L²)`), expect to **bump the
      statement constant to a larger quadratic** (update 3 sites — statement +
      append cases + clear case; `inOPoly` is all `toFrameworkWitness'` needs).
      **⚠ 2026-06-01 finding (do not "copy the in-place append
      template"):** the remaining 9 are **cross-register** — `tail`/`copy`/
      `head`/`eqBit`/`nonEmpty`/`takeAt`/`dropAt`/`concat`/`consLen` all read
      register `src` and write register `dst` (`Op.eval`: `s.set dst (f (s.get
      src))`), and the real witnesses use `dst ≠ src` (`PolyTime.lean`:
      `Op.head 1 0`, `Op.tail 2 0`, `Op.takeAt 3 2 1`). The gadget library has
      **no data-transport gadget** (only scan / insert-one-symbol / delete-one-
      cell), so the missing critical-path primitive is a single-tape **block-move
      gadget `copyBlockTM`** (carry `src` content to `dst`, resizing the slot).
      Once it exists, every cross-register op = (clear dst) ⨾ (copyBlock src→dst)
      ⨾ (in-place transform on dst). Only `clear dst` (no source) and the two
      append ops are genuinely in-place. **Order:** probe `copyBlockTM` go/no-go
      (verify the exit head lands in residue past the terminator, as the append
      op needed), prove its run/`_no_early_halt`, then per-op contracts via the
      `opAppendBit_physical_residue` template + `rewindBracket`. New bookkeeping
      lemmas landed (axiom-clean): `Compile.encodeTape_set_length` (tape-length
      balance for a register write), `Compile.ValidResidue_append_replicate_zero`,
      and `Compile.clear_block_decomp` — the `clear` gadget's proven spec bridge
      (clearing `dst` deletes exactly the `shiftReg (s.get dst)` block; gives the
      input/output target for a future `clearRegionTM_run`). Note clearing `dst`'s
      old slot is a shared prerequisite for *every* cross-register op, so the
      `clear`/delete-region machinery is foundational. **2026-06-01(b) — budget
      finding:** `compileOp_sound_physical_residue`'s budget was loosened from the
      linear `3·tapeLen+8` to the **quadratic `9·tapeLen²+9`**: multi-cell ops are
      inherently Θ(tapeLen²) on a single-tape machine (deleting/moving Θ(tapeLen)
      cells, each its own O(tapeLen) shift pass), so the linear bound was
      unsatisfiable for them. This composes — `compileSeq_sound_physical` is
      additive (`t₁+1+t₂`), so per-op quadratics sum to a polynomial total
      (`inOPoly` suffices). Append cases relax via `linear_le_quadratic_tapeLen`.
      See HANDOFF.md "the previous plan was wrong" + "budget is now QUADRATIC".
   d. Assemble `compileSeq_sound` from `compileSeq_compose_physical`,
      `compileForBnd_sound` from `loopTM_run`, `compileIfBit_sound` from
      `branchComposeFlatTM_run`; then `Compile_sound` / `Compile_run_physical` by
      induction. This discharges the one obligation the whole S3 bridge sits on.
   *Estimate ~3–5K LOC. One structural prerequisite remains — the
   leading-sentinel encoding migration (1b-0) — after which the step-bound
   accounting (linear-then-quadratic) and rewind-bracketing is real but
   structural-unknown-free work.*

2. **Retire S3 — migrate `⪯p` to `polyTimeComputable'`.** Swap
   `ReductionWitness.reduction_poly` to the TM-backed witness (the strengthening
   lemma keeps size-bound lemmas valid). Infrastructure is built **on the free
   line** (`⪯p'`, `reducesPolyMO'_of_langFree`; live instances
   `kSAT3_reducesPolyMO' : kSAT 3 ⪯p' SAT` and `flatTCC_reducesPolyMO' :
   FlatTCC ⪯p' FlatCC`). The work:
   - **The sound-tail reductions as free `PolyTimeComputableLang` witnesses**
     (templates: `NP/kSAT_to_SAT_free.lean` and — for the sound-tail
     unguarded-map pattern — `Reductions/FlatTCC_to_FlatCC_free.lean`).
     ✅ `flatTCC_to_flatCC` DONE (2026-07-02, unguarded map, probe-validated).
     ✅ `FlatCC_to_BinaryCC` DONE (2026-07-03, GUARDED map — the guard is
     provably necessary here — with on-machine validity check;
     probe-validated). ✅ `BinaryCC_to_FSAT` DONE (2026-07-11, the expensive
     Tseytin/tableau item — program `buildFSAT`, full run + cost stack,
     `Reductions/BinaryCC_to_FSAT_free.lean`). ✅ **`FSAT_to_SAT` DONE
     (2026-07-16)** — the last tail item: positional Tseytin over the Polish
     stream (design probed GO), map proven correct, full run ladder
     (`buildSAT_run`), full cost ladder (`buildSAT_cost_le`, `satBound =
     O(n⁸)`), witness `fsatSAT_reductionLang`, and the third live seam
     (`Reductions/FSAT_to_SAT_comp.lean`) — **the whole sound tail is ONE
     live chain `flatTCC_to_SAT_reducesPolyMO' : FlatTCC ⪯p' SAT`**.
     `map`-over-lists gates parts (near-complete draft at
     `parked/MapNatList_WIP.lean`).
   - **✅ SETTLED (2026-07-02): the migrated `NPhard'` transport.** There is
     deliberately **no generic `⪯p'`-transitivity**; the answer is
     `PolyTimeComputableLang.SeamData`/`comp` (fully proven, `PolyTime.lean`):
     chains fold into ONE witness through concrete per-seam re-encoder `Cmd`s
     (bridge = `AgreeBelow` on the right frame), then bridge once.
     `NPhard'`/`NPcomplete'` are defined; **`NPhard'` is proven at chain
     endpoints only** — C8 must emit the per-`Q` front witness *with its
     `SeamData` into the fixed chain head*. ✅ VALIDATED LIVE (2026-07-03):
     the first seam `FlatTCCBinComp.flatTCC_to_binaryCC_seam` joins
     `flatTCC_reductionLang` to `flatCCBin_reductionLang` (a pure 19-clear
     scrub — seam discipline pins each witness's input layout to its
     predecessor's exit frame), giving the first composed live `⪯p'`
     `FlatTCC ⪯p' BinaryCC`. ✅ CHAINED (2026-07-12): the second live seam
     `BinaryCCFSATComp.binaryCC_to_FSAT_seam` composes ON the composed
     witness, giving `flatTCC_to_FSAT_reducesPolyMO' : FlatTCC ⪯p' FSAT`
     (`Reductions/BinaryCC_to_FSAT_comp.lean`) — seams stack with no new
     machinery. ✅ TAIL COMPLETE (2026-07-16): the third seam
     (`Reductions/FSAT_to_SAT_comp.lean`) lands
     `flatTCC_to_SAT_reducesPolyMO' : FlatTCC ⪯p' SAT`.
   - At this point **S1 and S2 stop typechecking**; the conditional theorem
     breaks until they are honest — plan the swap as one coordinated batch.
   *Estimate ~2–4K LOC.*

3. **Real front reductions.** Build the **S1 Cook tableau**
   (`Simulators/CookTableau.lean`, ~6–11K LOC) and the **C8** universal-source
   decider (single-tape via `Lang.DecidesLang`, which **subsumes the old S2
   simulator** — collapse the phantom bridges here).

4. **In-NP verifiers (C7).** `evalCnfCmd` (SAT) and `cliqueRelCmd`, as `Cmd`s,
   give `inNP SAT` / `FlatClique`. Gated on C2 making the layer→`DecidesBy`
   bridge real. *Estimate ~1–2K LOC.*

5. **Encodable sweep (Part 0.1). — ✅ DONE (2026-07-04-b).** Every type on the
   proof path carries a real `encodable.size`; the size-0
   `instEncodableDefault` fallback is **deleted** (a missing instance is now a
   compile error by design). The actual holes were the four *front* instance
   types (`GenNPInput`/`LMGenNP.Instance`/`mTMGenNPFixedInput`/
   `TMGenNPFixedInput` — data-field-sum sizes; abstract `rel`/`accepts`
   predicate fields carry 0, see HANDOFF standing risk #4) and the
   `fun _ => 0` output-size bounds they licensed — all replaced by honest
   polynomial bounds, incl. `NPhard_GenNP`'s
   (`certBound n + timeBound (n + certBound n) + 3`). Axiom-clean; headline
   profile unchanged. This ungates C8.

**Total rough estimate: ~15–25K LOC**, dominated by the S1 tableau (3) and the
compiler step-bound machinery (1).

### Destination B — honest conditional theorem (fallback)

If C2 or the S3 tail ripple proves intractable for a side project, state
`CookLevin` conditionally on a **documented axiomatic `inTimePoly` / `⪯p`
interface**, keep the sound combinatorial tail, and stop. Trigger if step 1 or 2
overruns its estimate ~3×.

---

## Risk register

Two groups. **Group S** (soundness) determines *what the conditional theorem
currently means* — several entries are `sorry`-free. **Group C** (completion) is
the compiling-skeleton engineering. Refine the highest-ranked open item next.

### Group S — soundness gaps (mostly `sorry`-free, invisible to `#print axioms`)

| # | Gap | Location | Status / fix |
|---|-----|----------|--------------|
| **S3** | `⪯p` bounds **output size only**, never runtime — the enabling weakness that let S1/S2 typecheck and made `NPcomplete` too weak to be faithful. | `NP.lean`, `Lang/PolyTime.lean` | ✅ **CLOSED by deletion (2026-07-30-c).** The honest line `⪯p'`/`NPhard''`/`NPcomplete''` is the only one left; `NPcomplete`/`NPhard`/`red_NPhard` survive in `NP.lean` as **unused** definitions (no live consumer — see the live-mention list below). Historical note: **Superseded, not migrated.** The honest line `⪯p'`/`NPhard''`/`NPcomplete''` is built end to end and `CookLevin''` quotes it; there is deliberately **no** `NPcomplete'' → NPcomplete` bridge. `⪯p` survives only under the legacy front, and dies with it. Historical note: **Engine live & endgame design SETTLED.** Honest target `polyTimeComputable'`/`⪯p'` built on the free line; live chain instances `kSAT3_reducesPolyMO'` and `flatTCC_reducesPolyMO'` (first sound-tail step, 2026-07-02). The `NPhard'` transport is settled & machine-validated: `SeamData`/`comp` (Cmd-level chain composition, fully proven) + `NPhard'`/`NPcomplete'`, hardness at endpoints only. Execute via plan step 2. |
| **S1** | **if-on-the-answer** `FlatSingleTMGenNP ⪯p FlatTCC` (all-zeros tableau, never simulates `M`). Was the deepest unsoundness. | ~~`Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`~~ (**deleted** 2026-07-30-c) | ✅ **CLOSED, and the dishonest file is GONE (2026-07-30-c).** Historically: closed on the honest line 2026-07-29-b. The tableau mathematics, both size bounds, the map, the guard, the correctness iff, all seven program stages and both head seams are built and axiom-clean; `FrontS1Comp.SAT_NPhard''` is unconditional and `sorry`-free. The vacuous `if (source is yes-instance) then yesInst else noInst` reduction that gave this risk its name was deleted with the legacy front — it was never proved, and nothing on the `CookLevin''` path referenced it. |
| **S2** | **dummy TM bridges** — `bridgeMachine` discards `M`; predicates ignore `M`. | ~~`LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean`, `L_to_LM.lean`, `NP/TM/IntermediateProblems.lean`, `Simulators/MultiToSingle.lean`~~ | ✅ **CLOSED by deletion (2026-07-30-c).** C8's per-`Q` front replaces the whole bridge stack, and the `Cmd` layer is single-tape by construction, so there is no multi-tape detour left to bridge. All five files are gone. |
| **S0** | **hardness reduction reaches a `sorry`** — `NPhard_GenNP` relies on `hasDeciderClassical` (`sorry`). Its second defect (the vacuous `fun _ => 0` size bound) is **fixed** — Part 0.1, 2026-07-04-b: the bound is now the honest `certBound n + timeBound (n + certBound n) + 3`. | ~~`GenNP_is_hard.lean`~~ (**deleted** 2026-07-30-c) | ✅ **CLOSED by deletion (2026-07-30-c).** `FrontS1Comp.SAT_NPhard''` proves the hardness half without ever touching `hasDeciderClassical`. ⚠ The `sorry` was *classically closable* by the cheating encoder — deleting it is what keeps that door shut. The honest replacement is `NPhard''`'s hypothesis: a real verifier witness. |
| **S5** | **ENCODING HONESTY IS NOT ENFORCED** — a witness's `encodeIn` must be the natural layout of its *input*, `decodeOut` the inverse of the natural *output* layout, and all reduction work must live in the `Cmd`. The trivial dishonest instantiation satisfies **every** field (machine-checked: `probes/HonestyAuditProbe.lean` §6 builds one). | the composed endpoint witness; the two verifiers | ✅ **AUDITED 2026-07-30-c — verdict: the theorem means what it says.** Per-witness verdicts below; evidence `probes/HonestyAuditProbe.lean`. ⚠ **Status is STANDING, not closed**: this is *discipline*, so every new witness must be audited when it lands and its verdict added below. **The structural fix is scoped** — `ComputesBy`'s free `encode`/`decode` fields are the entire hole, and by FINDING AK they only matter at the two chain ends, where the types are concrete; replacing them with a canonical `Serialize` class makes the dishonest witness *unwriteable* and takes the audit from O(witnesses, forever) to O(1). This is **HANDOFF NEXT-TOP-DOWN item 1**, with a three-step go/no-go probe and a layout-DSL fallback. It is not the retired `LangEncodable`: no generic product instance is needed, so the size-unsoundness that killed that layer does not apply. |

**S5 verdicts (2026-07-30-c).** The audit's structural result came first and is
what made it finite — see the "audit surface" note under "What we know".

| # | audited | verdict |
|---|---|---|
| 1 | **the audit surface itself** | ✅ `comp` sets `encodeIn := Wf.encodeIn` (leftmost) and `decodeOut := Wg.decodeOut` (rightmost), and `toFrameworkWitness'` hands exactly those to `ComputesBy` as `encode`/`decode`. So `Q ⪯p' SAT`'s honesty is **two functions**, not twelve. Machine-checked (`HonestyAuditProbe` §1, at both nesting levels). |
| 2 | `FrontWitness.encodeInQ` (**the** input layout of the whole chain) | ✅ **honest.** `encX x ++ [1^(size x)]`. `encX` is the *hypothesis witness's own* layout — the one `Q`'s verifier already reads. The extra register is `encodable.size x` in unary: a **metric of the input**, consumed by the front program's `unaryMonomial` loops to build `maxSize`/`steps` on-machine. Neither component mentions `fQ`, `s1Map`, satisfiability or `Q x`. This is the least obvious verdict in the list; the tally is layout, not work. |
| 3 | `FSATSATFree.decodeOut` (**the** output decoder of the whole chain) | ✅ **honest.** `Function.invFun encodeCnf (get s CNFOUT)` — read one designated register, invert an **injective** serialization (`KSat3Free.encodeCnf_injective`). No input, no branch. |
| 4 | the five seams' `mfc`s | ✅ **honesty-irrelevant, by construction.** An `mfc` is a `Cmd` and runs inside the composite's program, so anything it does is *machine work*. (They are in fact pure `clearRange` scrubs — `probes/SeamS1Probe.lean` §1 pins the erase sets — but that is a frame fact, not an honesty fact.) |
| 5 | the four intermediate `encodeIn`s (`S1Witness`=`headEncodeIn`, `FlatTCCFree`, `FlatCCBinFree`, `BinaryCCFSATFree`, `FSATSATFree`) | ✅ **honesty-irrelevant, and independently honest.** Irrelevant because each appears only on the **right** of a `SeamData.bridge` obligation — the composed program is *required to produce it*, so a dishonest layout could only make the bridge harder, never license a cheat. Independently: each is a fixed-register spread of the input's own fields (unary numbers, sentinel streams), and each `decodeOut` is `Function.invFun <injective natural output key>`. So the **per-step** `⪯p'` theorems quoted in the README are honest too. |
| 6 | the reduction maps' guards | ✅ **honest.** `s1Map` branches on `s1GuardB M s` (validity of the flat TM), `FlatCC_to_BinaryCC_instance` on `isValidFlattening C`, `BinaryCC_to_FSAT_instance` on `BinaryCC_wellformed C`; `flatTCC_to_flatCC` and `fsatToSat` are unguarded. Every guard is a decidable property of the **input's structure**, never of the answer — the S1 original sin (`if source is yes-instance then …`) is gone with the legacy file that held it. |
| 7 | `fQ`, the front instance | ✅ **honest, and it is what makes hardness non-vacuous.** `fQ x = (MQ W.verifier.c …, 3 :: encodeRegs (encX x), maxSize x, steps x)`: the emitted machine is built **from `Q`'s own verifier program**. Textbook Cook–Levin. |
| 8 | membership: `satEncX` / `satEIn` | ✅ **honest.** `satEncX N` is *registers `0`–`2` of the live verifier's own `encodeState`* (`= encodeState (N,a) |>.take 3`, `rfl`), plus the **raw** certificate register. Register 1's `1^\|N\|` is derived, but inherited — `evalCnfDecidesLang` already demands it as `CLAUSE_TALLY`. Bits → assignment is done by `certDecode`, a `Cmd`. |
| 9 | membership: non-vacuity | ✅ **machine-checked, not audited.** `satRel_correct : polyCertRel SAT satRel` *is* soundness + completeness + a polynomial certificate bound. Nothing to read. |
| 10 | `InNPWitnessLangFreeSplit.encX_size` | ⚠ **not an honesty check** — measured slack `23` vs `≥ 200000`. It constrains nothing; do not cite it as one. |
| 11 | `S1Witness.S1CostBound.cost_bound` | ✅ **nothing depends on it definitionally.** It is an anonymous `Exists.choose`, and the whole project builds — so no consumer unfolds it to `S1Map.s1Bound`. |
| 12 | the *hypothesis* side of `NPhard''` | ✅ **honest by design.** Quantified over `InNPWitnessLangFreeSplit Q`: a real `Cmd` verifier plus `polyCertRel`. It is **not** the cheat-inhabited `inNP Q` (standing risk #6), which is why `NPhard''` and not `NPhard'` is the headline. |

**What still mentions the legacy `⪯p` notions, after the demolition
(recorded once, 2026-07-30-c — do not re-litigate).** All of it is **retained
deliberately** and none of it has a live consumer:

* `Complexity/NP.lean` — `reducesPolyMO` (`⪯p`) + `ReductionWitness`,
  `reducesPolyMO_reflexive`/`_transitive`, `NPhard`, `NPcomplete`, `red_NPhard`,
  `NPhard_subtype_proj`, `inP`, `P_NP_incl`.
* `Lang/PolyTime.lean` — `reducesPolyMO'_to_reducesPolyMO`,
  `polyTimeComputable'_to_polyTimeComputable`, `NPhard'_to_NPhard`.
* nine `⪯p` statements of real reductions, each a thin wrapper with no consumer:
  `kSAT_to_SAT`, `kSAT_to_FlatClique_poly`, `FlatTCC_to_FlatCC_poly`,
  `FlatCC_to_BinaryCC_poly`, `BinaryCC_to_FSAT_poly`, `FSAT_to_SAT_poly`,
  `FSAT_to_3SAT_poly`.
* `inNP` is still *produced* by `sat_NP`, `FlatClique_in_NP` and
  `inNP_kSAT3_free`, and consumed by nothing.

**Why retained, not deleted:** `⪯p` is not *wrong*, it is *weak*, and `⪯p'` is
defined as a strengthening of it — the bridge `reducesPolyMO'_to_reducesPolyMO`
is what lets an honest result be restated in the classical vocabulary if ever
wanted. What was dishonest was *proving `NPcomplete SAT` through a vacuous
chain*, and that is gone. If a future session wants them out anyway, it is one
self-contained commit (delete the nine wrappers, then the `NP.lean` block, then
the three bridges) and a full rebuild — do not mix it with anything else.
| **S4** | **membership half of the honest headline** — `inNPLangFreeSplit SAT`. Without it `NPcomplete'' SAT` cannot be stated and the honest hardness line has no headline to feed. | `Deciders/EvalCnfSplit.lean`, `CookLevinHonest.lean` | ✅ **CLOSED (2026-07-30-b).** `EvalCnfSplit.SAT_inNPLangFreeSplit` is unconditional and axiom-clean: the split layout, `xWidth = 3`, `polyCertRel SAT satRel`, the decoder `certDecode` with all three contracts (`CertBridge` from `certDecode_decodesAssgn`, cost and frame by `decide`), and all four composite `DecidesLang` bounds. `CookLevinHonest.CookLevin'' : NPcomplete'' SAT` follows. The two honesty verdicts this half still owes moved to **S5**. |
| **Part 0.1** | ~~size-0 `instEncodableDefault`~~ | `Definitions.lean` | ✅ **CLOSED (2026-07-04-b)** — real sizes everywhere, the fallback **deleted** (missing instance = compile error). See plan step 5. |

### Group C — completion risks (the compiling skeleton)

| # | Gap | Status |
|---|-----|--------|
| **C2** | **compiler soundness** `Compile_sound` / `Compile_run_physical_residue`. | ✅ **DONE & CLEAN (2026-07-04).** All 9 live ops proven, `compileOp_sound_physical_residue` fully proven with no side-conditions, both isolation walls and the value-as-length trio deleted. The build narration (a ~40-entry session log, Jun 2026) was compressed away 2026-07-30-c; git history has it. **The five findings that still bind:** ① the physical tape **never shrinks** (`Complexity/TapeMono.lean`), so an exact-tape contract is unsatisfiable for every length-decreasing op — the contract is **residue-tolerant** (`exit tape = encodeTape output ++ terminator-free residue`), and every rewinding op needs the **two-phase** rewind (residue follows the trailing terminator). ② Per-fragment budgets must be **LINEAR** in tape length; quadratics are not superadditive, so summing them gives a cubic and the composed lemmas become unprovable (the per-op budget is `(9L²+9L+30)·(cost+1)`, the *fragment* bound is `≤ 2·tapeLen+3`). ③ The compiler is **`BitState`-only** (`sig = 4`), so every encoding on the proof path is bit-level with **numbers in unary** — this is why `enc_bit` is a field on the witness structures. ④ `Op.cost` must be **size-aware**: under unit cost, `concat`/`copy` grow the state multiplicatively and no fixed-degree budget polynomial can bound `Compile c` (`doubler := forBnd 2 1 (concat 0 0 0)`); `Op.size_eval_le` and `Cmd.size_eval_le` are what replaced it, the latter by charging the `forBnd` counter. ⑤ The generic product encoding is **size-unsound** — no polynomial `enc_size` exists for any inline self-delimiting prefix (`probes/UnaryProductSizeProbe.lean`), which is why the whole canonical `LangEncodable` layer was retired and every witness uses a bespoke free encoding. **Do not rebuild the canonical layer, do not restore unit cost, do not tighten the residue contract.** |
| **C1** | **per-`Op` compilation** (`compileOp` + soundness). | ✅ **DONE for all live ops** (9/9): `appendOne`/`appendZero`/`clear`/`nonEmpty`/`head`/`copy`/`tail`/`eqBit`/`concat`, all FULLY PROVEN & axiom-clean. The value-as-length trio `takeAt`/`dropAt`/`consLen` was **DELETED (2026-07-04)** — never needed by any remaining witness. |
| **C3** | **`loopTM` counted loop** (`compileForBnd` + soundness). | `loopTM`/`loopTM_run` proven; behavioural `forBnd` toolkit (`Lang/Frame.lean`) proven. ✅ 2026-06-11b: the snapshot-vs-clobber gap is closed at the interface — `compileCmd` assigns **static scratch registers** (`K1/K2` per nesting level, `Cmd.loopDepth`), the contract is re-pinned + probe-validated (`probes/ForBndSkeletonProbe.lean`), `physStepBudget` re-pinned ×8 to fund the loop bookkeeping. Machine build is UNGATED, gated only on the cursor-copy/`tail` op gadgets; see HANDOFF bottom-up tasks 1–2. |
| **C4** | **layer → framework bridge.** | ✅ **DONE on the free line, LIVE & axiom-clean**: `toFrameworkWitness`/`toFrameworkWitness'`, `inNPLangFree`/`inNPLangFree_to_inNP`, `FreePrecomposeData`/`precomposeFree`, `red_inNP_of_langFree` (live: `inNP_kSAT3_free`), `reducesPolyMO'_of_langFree` (live: `kSAT3_reducesPolyMO'`). The canonical engine was RETIRED & deleted 2026-07-02 (size-unsound product encoding — see C2). ⚠ `FreePrecomposeData`/`PolyTimeComputableLang` do not *enforce* encoding honesty (`eIn`/`decodeOut` unconstrained) — see HANDOFF standing risks. Remaining: honest layer reductions (S1 + sound tail). |
| **C6** | **bit-test tester.** | ✅ DONE (2026-06-11): `bitTestTM` (tape→state, register 0) AND the general `compileTestBit t` tester are real & sorry-free; `compileIfBit_sound_physical_residue` PROVEN (the `ifBit` combinator is closed). |
| **C7** | **verifier bodies** — `evalCnfCmd` (SAT, gates `inNP SAT`), `cliqueRelCmd`. | **EvalCnf: ✅ DONE (2026-06-10)** — `EvalCnfCmd.lean` sorry-free; `evalCnfDecidesLang` axiom-clean (budget quartic `200000·(n+1)^4`, `regBound 16`). **CliqueRel: ENCODING + PROGRAM + STRUCTURAL FIELDS ✅ DONE (2026-06-29)** — `cliqueRelEncode` concrete + bit-level + probe-validated; `cliqueRelCmd` is the concrete probe-validated 5-check verifier (`checkWf`/`checkOfType`/`checkLen`/`checkNodup`/`checkClique`, trio-free), and the structural `DecidesLang` fields `usesBelow`/`noConsLen`/`allOpsSupported` join the 4 encoding fields PROVEN & axiom-clean (quartic `timeBound`, `regBound 32`). Probes: `CliqueRelProbe` + `CliqueLtProbe`. **2026-06-30: ⚠ found+fixed a BUG in `ltBit`** (it guarded its consume-loop with `Cmd.ifBit`, which tests `= [1]` *exactly*, not nonemptiness, so it mis-decided operands `> 1`); **fixed to the unconditional-drain form and PROVED `ltBit_run` (axiom-clean).** **2026-06-30b: ✅ proved the keystone leaf `readNum_run` + 3/5 per-check run-lemmas (all axiom-clean).** **2026-06-30c: ✅ proved the remaining checks `memberEdge_run`/`checkNodup_run` (double `forBnd`)/`checkClique_run` (depth-4, calls `memberEdge`), AND the `decides` field (`cliqueRelCmd_decides` + bridge `cliqueRel_iff_checks`) — all axiom-clean.** The nested-loop pattern (inner-run lemma proven by `foldlState_range_induct`, called inside the outer step; outer counter survives as a frame fact) is established. **2026-07-01: ✅ `cost_bound` PROVEN — `cliqueRelDecidesLang` sorry-free & `FlatClique_in_NP` AXIOM-CLEAN** (`[propext, Classical.choice, Quot.sound]`). The full cost-lemma stack (`readNum_cost` → per-check `_cost` lemmas → `cliqueRelCmd_cost_bound`) uses **length-only loop invariants** for the `hC` uniform body-cost bound (reusing the behavioural `*_step` for `hM`). ★ FINDING: `timeBound` bumped quartic→**quintic** `(n+1)^5` — uniform-bound accounting makes the depth-4 `checkClique` nest degree 5 (innermost `readNum` is `Θ(S²)` under three `forBnd`s); the true TM cost is quartic but amortisation is invisible to `cost_forBnd_le`. **CliqueRel C7 is now COMPLETE.** Both in-NP verifiers (SAT + FlatClique) axiom-clean; all remaining `sorryAx` on `CookLevin`/`Clique_complete` is hardness-side. |
| **C8** | **an honest universal front** (the replacement for `NPhard_GenNP`/`hasDeciderClassical`). | ✅ **DONE (C8-0…C8-5).** The per-`Q` front machine, its lifting, the reduction program and the seam into the chain are built and axiom-clean: `FrontWitness.front_reducesPolyMO' : Q ⪯p' FlatSingleTMGenNP`, `FrontLifting.fQ_correct`, `FrontS1Comp.frontBridge`/`front_to_SAT_seam`. **Consume these as black boxes.** The finding that shaped the whole design (**F1**, 2026-07-04): the `inNP` hypothesis is classically TRUE for every predicate (the cheating `DecidesBy.encode`), so `NPhard'` over it can *never* be proven honestly — the hypothesis had to strengthen to a free-line verifier witness. That is `NPhard''` over `InNPWitnessLangFreeSplit` (Cert = `List Bool` in a canonical one-register layout, split pair layout, a real `Cmd` verifier), and it is why the headline is `NPcomplete''`. Also found and fixed then: a `FlatSingleTMGenNP` port bug (`list_ofFlatType 1` vs Coq's `sig M`, missing `tapes M = 1` — F2) and the hard-coded `encodeIn_size ≤ 2n+1` that blocked `W_Q` (F3, generalized to the per-witness `encBound`). Subsumed S2. |
| **C5/C5a/C9** | DSL expressiveness; pair plumbing; canonical encoding. | **CLOSED — canonical encoding RETIRED (2026-07-02).** Pair plumbing is done bespokely inside each free witness (live ×3); the `forBnd` toolkit stands. Add new `Op`s only when one materially shortens a verifier (each new `Op` = another soundness proof). |

---

## How we work — skeleton-first, risk-driven

Learned the hard way in the May 2026 pivot (the hand-rolled Part 2 blew up ~10×
because structural issues were invisible until attempted). **Do not deviate
without an explicit reason.**

1. **Skeleton first, then refine.** A compiling skeleton exposes every
   downstream obligation; an isolated proof exposes nothing.
2. **Refine the highest-risk gap next** (per the register), not in phase order.
3. **Decompose `sorry`s, don't elaborate them.** Each split is a structural
   decision that typechecks (right shape) or fails (gap found). The
   behavioural/cost split of `compileOp_sound` this session is an example.
4. **Prefer concrete `def` + `sorry` over `axiom`** (currently 0).
5. **Probe before committing engineering.** Time-boxed go/no-go: assume lower
   layers, validate the structure additively, measure, verdict.
6. **Build green between commits; record gaps in commit messages.**

### Hard-won gotchas (you WILL hit these)

- **`omega` cannot see through `Var := Nat` for *variables*.** A register
  `r : Var` (or a literal ascribed `(0 : Var)`) is opaque to `omega` (`↑`
  coercions, "no usable constraints"). Restate at `Nat` or use explicit
  `Nat.*` lemmas (`Nat.min_eq_left`, `Nat.lt_of_le_of_ne`, …). `omega` *does*
  work on genuinely-`Nat` terms (`regBound`, cost/size bounds).
- **Avoid nested `set`/`let` chains over `State.set`/`State.get`** — `isDefEq`
  blows up exponentially (×8 per level). Flatten with one
  `simp only [Cmd.eval_op, Op.eval]`.
- **`.get` mis-resolves on `State` *literals*** (picks `List.get`, wants `Fin`).
  Write `State.get s r` explicitly on literals.
- **`set` lives only in `PolyTime.lean`, not `Frame.lean`** (the latter is
  core-only, no Mathlib tactics).

---

## Why the layer (and why not hand-rolled TMs)

Building a useful algorithm directly from `FlatTM`s ran ~10× over budget;
continuing projected Parts 2–6 at ~100–150K LOC. The lessons:

1. **Per-state lemmas don't amortise across primitives** — each primitive needs
   its own step/scan/run lemmas. The layer pays TM construction *once*.
2. **Iteration bookkeeping was the dominant cost** (~1000 LOC/loop site). The
   layer pays it once in `loopTM`.
3. **Single-tape with a delimiter scratch is the only economical shape** for
   composition (multi-tape needs `(sig+1)^k` bridge entries). This is also why
   the S2 multi-tape detour is unnecessary.
4. **The layer needs *cost* in its semantics, not just behaviour** — mathlib's
   `Computable`/`Partrec` handles computability but not complexity.

The Coq port avoids the blow-up by extracting TMs from the L-calculus; the layer
is the Lean analogue (a total structured while-language vs a general
λ-calculus). Parked hand-rolled work (~15K LOC) lives under `parked/`.

---

## References

- Coq source: <https://github.com/uds-psl/cook-levin>; local mirror `coqdoc/`.
- Status / orientation: root [`README.md`](../README.md).
- Parked work: `parked/README.md`, `parked/PART2.md`.
