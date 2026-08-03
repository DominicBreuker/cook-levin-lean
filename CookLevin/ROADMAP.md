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

## Status snapshot (verified 2026-08-06)

| | |
|---|---|
| `lake build` | ✅ green (~10 min from cold; `S1Witness.lean` alone spends ~3 min in the kernel on the cost ladder's `decide`) — **and since 2026-08-02 it is the soundness gate**: `#assert_library_axiom_clean Complexity` at the bottom of `Complexity.lean` fails elaboration unless every declaration in every module is `sorry`-free and uses only `propext`/`Classical.choice`/`Quot.sound` (**12 680** declarations, **106** modules, ~2 s). `Complexity/SoundnessGate.lean` gates the endpoints individually, `Complexity/HonestyGate.lean` pins risk S5's two audited functions (`encodeIn`/`decodeOut` of the composite, incl. `encodeIn x = certState x` under `NPhardStr`) as gated `rfl` theorems, `Complexity/CostFaithfulness.lean` gates `Compile.cost_is_time_proxy`, `Complexity/NonVacuity.lean` gates non-vacuity of the `NPhardStr` hypothesis, `Complexity/StatementGate.lean` (2026-08-06) gates the reviewer's *reading list*, `Complexity/StatementMeaning.lean` (2026-08-07) gates the checkable verdicts of the **audit** of that list, and `Complexity/GateSurfaceGate.lean` (2026-08-08) gates what each of those instruments costs a reviewer to read *beyond* the headline. Eight obligations, no CI step and no `grep` involved — see `Complexity/Meta/AxiomGate.lean` and `Complexity/Meta/StatementSurface.lean`. |
| **the gates themselves are metered (S9)** | ✅ **NEW 2026-08-08 (top-down).** `Complexity/GateSurfaceGate.lean`. Every instrument a reviewer is told to believe is a theorem whose *statement* they must also read, and until now nothing measured those statements — the same hole `StatementGate.lean` closed one level down. The instrument is `#assert_statement_surface_delta`, which reports the **difference** against a baseline headline (a gate about the headline shares nearly all of its surface; only the difference informs), plus `_contains`/`_omits` for shape claims. Negative controls: `probes/StatementSurfaceProbe.lean` §§6–9, including the subtle one — `_omits` must consult the **raw** closure, or an absence claim could be satisfied through a generated companion the report filter hides. **`lake build` now carries eight obligations.** Two findings, AZ and BA, in their own rows. |
| **FINDING AZ (2026-08-08)** | ★ **The two conjuncts of the published headline are stated over DISJOINT vocabularies, so the two remaining trust items do not compound.** `NPcompleteStr' SATStr = NPhardStr SATStr ∧ inNPStr SATStr`. Metered separately — each instantiated at a concrete language so no class hypothesis blurs the measurement — the **hardness** conjunct's surface contains `FlatTM`/`runFlatTM`/`stepFlatTM`/`validFlatTM` and **omits** `Op.cost`/`Cmd.cost`/`Cmd`/`Op`; the **membership** conjunct's contains `Op.cost`/`Cmd.cost`/`Cmd` and **omits** `FlatTM`/`runFlatTM`/`stepFlatTM`. All four assertions are gated. Consequences: (a) a reviewer who rejects our cost model outright still has the entire hardness half of Cook–Levin, because its polynomial bound already counts `stepFlatTM` steps inside `ComputesBy`; (b) the converse is the uncomfortable one — *as stated*, `inNPStr SATStr` contains **no Turing machine at all**, so "SAT is in NP" in this development is a claim about `Cmd.cost` and `Complexity/CostFaithfulness.lean` is the only thing making it a claim about time. Fixed by stating the machine-level version: `GateSurfaceGate.satStr_membership_is_machine_time` gives a sound, complete, polynomially bounded certificate relation for `SATStr` decided by a real `FlatTM` inside a real `runFlatTM` bound, and it is one line (`DecidesLang.toInTimePoly`). **After that theorem neither conjunct depends on `Op.cost`.** ⚠ **The generalisable lesson: meter a conjunction's conjuncts SEPARATELY and at concrete instances. A joint surface is the union, which hides exactly the fact that the two halves rest on different things — and "which of my trust assumptions are needed for which half" is the question a reviewer most wants answered and can least easily answer by reading.** |
| **FINDING BA (2026-08-08)** | **The gates are two different kinds of evidence, and were being advertised as one.** Measured as additional definitions beyond the headline's 112: `StatementMeaning`'s four restatements cost **0** (they say nothing the headline does not — the control the previous session asked for, and it passes); `NonVacuity.searchDecide_correct` **10**, `searchDecide_calls` **1**; the `HonestyGate` pins about the chain *ends* **0, 1 and 7**. Against that: `Compile.cost_is_time_proxy` costs **265** and `HonestyGate.str_encodeIn_eq_certState` costs **1045** — the whole compiler and the whole six-seam reduction chain. **This is not fixable and is not a defect**: it is FINDING AW from the other side. Both are statements *about the witness we built*, and every headline quantifies the witness away existentially, so their surfaces can never be subsets of a headline's. The honest conclusion is that they are **regression gates, not reading instruments** — their value is that `lake build` fails when the construction changes — and the README no longer asks anyone to read them. What *is* readable about them is pinned instead (`_contains` on both, plus the linkage below). ⚠ **A gap this surfaced and closed:** `CostFaithfulness.lean` bounds `Compile.paddedBitDeciderTM`, and **nothing said that is the machine `DecidesLang.toDecidesBy` produces** — a retarget would have left the gate green and about a machine no longer on the proof path. `GateSurfaceGate.deciderBridge_machine`/`_states` pin it by `rfl`. The reduction side deliberately has no counterpart: `toFrameworkWitness'` is a *theorem* returning `Nonempty`, so its machine is unreachable — and by FINDING AZ that half does not depend on the cost model anyway. **The generalisable lesson: when a gate is about a construction rather than about a statement, measuring its surface tells you to stop calling it a reading obligation — and the thing worth gating instead is its LINKAGE to the object on the proof path.** |
| **the reviewer's reading list (S8)** | ✅ **COMPLETE AND GATED (2026-08-06, top-down).** `Complexity/StatementGate.lean` lists every constant of this repository reachable from a headline's **type**; `#assert_statement_surface` recomputes the closure each build and fails unless the list matches **exactly** (equality, not containment). **103** definitions behind `CookLevinStr`, **113** behind `SATStr_NPcompleteStr`, grouped in reading order: what-is-claimed · the layer · the machine · SAT · input size. ⚠ **FINDING AV** — the string headline's surface is *larger*, not smaller: `SATStr` is defined by parsing, so the well-formedness DFA and the CNF parser are part of what it says; the cheaper route is `satStr_iff`, a **theorem**. ⚠ **FINDING AW** — neither surface contains a reduction, a `decodeOut` or a `Serialize` instance (they are existentially quantified), so the statement gate and the honesty gate can never merge. ~~What is **not** claimed: that anyone has read the 103~~ — **READ 2026-08-07 (top-down). The verdict table is in the S8 row of the risk register below, and its checkable half is gated by the build (`Complexity/StatementMeaning.lean`).** Fifteen verdicts; two findings, one of them a defect in the published statement (FINDING AX, its own row below) and one a defect in the reading list's own prose (FINDING AY). Negative controls: `probes/StatementSurfaceProbe.lean`. |
| **FINDING AX (2026-08-07)** | ❌→✅ **The membership conjunct of the published headline was VACUOUS, and the fix was three lines because the honest witness already existed.** `NPcompleteStr P = NPhardStr P ∧ inNPLangFreeSplit P`. Three sessions had hardened the *hardness* conjunct until it had no free input encoder; nobody checked the other one. `InNPWitnessLangFreeSplit` still carries `encX`, and by FINDING AO no law about `encX` can exclude "the honest encoding plus one register holding the answer" — so `probes/HonestyAuditProbe.lean` §7c proves `inNPLangFreeSplit Q` for an **arbitrary** `Q : List Bool → Prop`, undecidable ones included. A conjunct true of every language is not a claim about `P`; all of that half's content was that *our* instance is honest, which is S5's business and unreadable from the statement (FINDING AW). **Fix, same shape as `NPhardStr`'s — remove the field, do not add a law:** `NPcompleteStr' P = NPhardStr P ∧ inNPStr P`, with `SATStrComp.SATStr_NPcompleteStr'` proving it for `SATStr`. `SATStr.satStrWitness` was *already* an `InNPWitnessStr`; the old headline was calling `.toInNPWitnessLangFreeSplit` on it, i.e. deleting the `encX_canonical` field on the way out. ★ **Measured: the strict statement is 112 definitions against 113 — strictly stronger AND one name cheaper to read**, because `inNPLangFreeSplit` leaves the surface and `inNPStr` was already in it. ⚠ `CookLevinStr : NPcompleteStr SAT` cannot be strengthened this way (`SAT` is on `cnf`, and `inNPStr` is only defined for string languages), which is a third independent reason to quote the `SATStr` headline. **The generalisable lesson: a conjunction is only as honest as its weakest conjunct, and "we hardened the hypothesis" is not a statement about the conclusion. When you tighten one side of a published `∧`, re-ask the dishonest-instantiation question of the other side in the same session.** |
| **FINDING AY (2026-08-07)** | ⚠→✅ **The reading list contained two files whose own module docstrings said the definitions in them were `axiom`s.** `Lang/Syntax.lean` announced that "`eval`, `cost`, and `Compile` … are deferred … (declared as `axiom`s in `Semantics.lean` and `Compile.lean`)" and `Lang/Semantics.lean` that its definitions were "deferred to Part 3.2". True of the May 2026 skeleton, false since Part 3.2/3.3 landed, and contradicted every build since 2026-08-02 by the axiom gate. These are the **first two files of group 2** of `Complexity/StatementGate.lean` — a reviewer working the list in the prescribed order met them immediately and was told that the semantics of the language every witness in the development is written in were unproven placeholders. Both headers rewritten 2026-08-07, with the three load-bearing choices in `Cmd.run` (single-pass run, `forBnd` sampling its bound once so the language is **total**, and the `iters*iters` counter charge) spelled out where a reader needs them. **The generalisable lesson: `#assert_statement_surface` measures *definitions*, and prose is not a definition — nothing in this repository can gate a docstring. Audit the comments inside the surface, not only the code; a stale comment in the reading list does more damage than a stale comment anywhere else, because the reading list is precisely what a reviewer is told to trust.** |
| **`#print axioms SATStrComp.SATStr_NPcompleteStr'`** | `[propext, Classical.choice, Quot.sound]` — ★★ **`NPcompleteStr' SATStr`, the statement to quote** (2026-08-07). NP-completeness with `List Bool` on both sides of the arrow *and* the canonical `certState` layout pinned on both sides of the conjunction. See FINDING AX for why the previous headline was not enough and why this one cost nothing. Gated: `Complexity/StatementGate.lean` carries its 112-name surface. |
| **`sorry`s in built code** | **0**, and this is now *machine-checked by the build itself* (see the row above); `sorry` is only a warning in Lean, so it used not to be. (Was 5; the legacy `⪯p` front and its three dead files were **deleted** 2026-07-30-c — none was to be proved.) |
| **non-vacuity of the published hypothesis (S7)** | ✅ **CLOSED both directions 2026-08-03, and UPGRADED 2026-08-04** — gated (`Complexity/NonVacuity.lean`). **Inhabited, by a hard problem**: `SATStr` — the bit strings that spell out a satisfiable CNF (`Deciders/SATStr.lean`, `Deciders/CnfWellFormed.lean`) — has a complete `InNPWitnessStr`, and `NonVacuity.satStr_reducesPolyMO'_SAT : SATStr ⪯p' SAT` is `CookLevinStr` applied to (a string form of) **its own target**. The 2026-08-03 inhabitant `SquareStr` stays as the minimal example, but it is in **P**. **Not everything**: `searchDecide_correct` — every inhabitant is decided by brute-force search over its own verifier `Cmd`, so no undecidable predicate inhabits the class. ⚠ ~~Two rungs~~ **one** rung still open and labelled: the decider is a Lean function, not a compiled `FlatTM` (HANDOFF top-down item 2). `NPhardStr SATStr` **was** claimed and proven on 2026-08-05 (`SATStrComp.satStr_NPhardStr`), so the class's inhabitant is NP-**complete** in this development's own sense. |
| `#print axioms SATStr.inNPStr_SATStr` | `[propext, Classical.choice, Quot.sound]` — **SAT as a STRING language is in the published hypothesis class** (2026-08-04, bottom-up). `SATStr x := SAT (parseTotal (strBits x))`, proven equal to `∃ N, strBits x = encodeCnf N ∧ SAT N` (`satStr_iff`), with a complete `InNPWitnessStr` over the canonical one-register layout. ⚠ **FINDING AS — the planned on-machine CNF parser does not exist and is not needed.** `EvalCnfCmd.encodeCnf` is already a flat 0/1 cell stream and `certState x` is already one register of 0/1 cells, so `CNF_STREAM` is a **copy of the input register**; the only field of the verifier's twelve-register layout the raw string does not carry is `CLAUSE_TALLY = 1^|N|`. The whole re-encoder is therefore ONE left-to-right scan that validates the grammar and counts the clauses — a four-state DFA, `scanBody`, 11 ops (`Deciders/CnfWellFormed.lean` has the DFA and `wfCnfB_iff : wfCnfB l = true ↔ ∃ N, encodeCnf N = l` over 0/1 streams, both directions). Two further findings: the DFA's `pending` bit is **load-bearing** (a three-state version accepts `[1,1,0]`, a literal run with no clause terminator, which is not an encoding — `not_wfCnfB_lit_unterminated`); and "not an encoding" and "unsatisfiable" are made the **same verdict** by sending every non-encoding to `[[]]` (`parseTotal`), which is why one verifier decides both and the malformed branch is four ops. `EvalCnfSplit.certDecode` is reused verbatim, bridge included, via `Cmd.eval_agree`. Cost: `Cmd.chk` accepts the re-encoder by `decide` in ~5 s. Probe: `probes/SATStrProbe.lean` (exhaustive: the grammar at length ≤ 8, the bridge at ≤ 7, machine-vs-model at ≤ 6, the loop invariant at every index). |
| `#print axioms SATStrComp.SATStr_NPcompleteStr` | `[propext, Classical.choice, Quot.sound]` — ★ **`NPcompleteStr SATStr`: NP-completeness with `List Bool` on BOTH sides of the arrow** (2026-08-05, bottom-up). The reverse reduction `SAT ⪯p' SATStr` (`Reductions/SAT_to_SATStr_free.lean`) plus the **sixth seam** (`SAT_to_SATStr_comp.lean`) hang the string form off the tail of the honest chain. Three things worth knowing. (a) **The reduction map is the identity on tape cells**: `strBits (satToStr N) = encodeCnf N`, so the `Cmd` is the layer's no-op — the content is `satStr_satToStr : SATStr (satToStr N) ↔ SAT N`, whose `⇒` half needs `encodeCnf`'s injectivity (`CnfSerialize.decCnf_encodeCnf`). (b) **A seam needs the left composite's exit REGISTER, which `computes` does not give** — `computes` only says the register *parses* to the output. `SATStrComp.ExitsOnCNFOUT` is the missing statement and it **transports along a seam in one line** (`exitsOnCNFOUT_comp`), carrying `FSATSATFree.buildSAT_run` from the innermost tail step out through four `comp`s to the whole chain. Any future tail extension needs exactly this. (c) ⚠ **FINDING AT** — see its own row. Probe: `probes/SATToSATStrProbe.lean` (~5 s). |
| **FINDING AT (2026-08-05)** | **The `Serialize` no-compression law had to become a POLYNOMIAL law, and the canonical bit-string layout is why.** `Serialize.size_le_enc_length` read `encodable.size x ≤ (enc x).length`. That is **unsatisfiable for `List Bool` under the canonical layout**: `encodable.size ([true] : List Bool) = 2` (the generic list instance charges 1 per element *plus* `size true = 1`) while `(strBits [true]).length = 1`. Nothing is compressed — `strBits` is a bijection onto `{0,1}^n` — `encodable.size` simply over-counts by up to 2×. An instance satisfying the identity form would have to spend two cells per bit and would then **disagree with `certState`**, leaving the development with two serializations of a bit string for a reviewer to reconcile: strictly worse. The law is now `encodable.size x ≤ sizeLB (enc x).length` for a polynomial, monotone `sizeLB` — *the same shape `InNPWitnessLangFreeSplit.sizeLB` has carried since 2026-08-02 for the same obligation*, and the purpose (a program counts `enc x`'s cells and applies `sizeLB` on-machine) is served identically. `Serialize cnf` keeps `sizeLB := id`, so nothing about the existing chain end changed. ⚠ The generalisation is a real cost: the identity form was checkable by eye. The guard against a huge `sizeLB` hiding a lossy layout is `dec_enc` (injectivity), which no `sizeLB` weakens. **The generalisable lesson: before pinning a chain end with a class, check the class's laws against the layout the *statement* already pins — the statement wins.** Negative control: `probes/SATToSATStrProbe.lean` §1. |
| **encoding-honesty audit (S5)** | ⚠ **audited 2026-07-30-c, partly STRUCTURAL 2026-08-01, head side CLOSED 2026-08-02.** Tail: a real `Serialize`-backed parser. Head: the composite's `encodeIn` is now `W.encX` **verbatim** (no appended tally — the front counts its own input's cells), so under `NPhardStr` it is `certState x`, the raw string, by `rfl`. The hypothesis-side hole (FINDING AN/AO) is closed by *restricting* the statement — and since 2026-08-07 the **conclusion**-side twin of it is too (FINDING AX): `SATStrComp.SATStr_NPcompleteStr' : NPcompleteStr' SATStr` is the one to quote. Verdicts 1–14 below; evidence `probes/HonestyAuditProbe.lean` §§1–8. |
| **`#print axioms CookLevinHonest.CookLevinStr`** | `[propext, Classical.choice, Quot.sound]` — ★ **`NPcompleteStr SAT`** (2026-08-01): hardness over NP **string languages** with the canonical one-register layout, so the hypothesis has no free input encoder. Derived from `CookLevin''` via `NPcomplete''_to_NPcompleteStr`. |
| compiler (Risk C2) | ✅ **DONE & CLEAN** (2026-07-04): all 9 ops proven, no side-conditions; the retired trio + both isolation walls **deleted** |
| **`Op.cost` is a faithful time proxy** | ✅ **STATED AND GATED 2026-08-02** (`Complexity/CostFaithfulness.lean`). `Compile.cost_is_time_proxy`: ONE fixed polynomial (`timeProxyBound`, degree 3, exhibited) bounds the running time of **both** compiled machines — `paddedComputeTM` (reductions, via `toFrameworkWitness'`) and `paddedBitDeciderTM` (verifiers, via `DecidesLang.toDecidesBy`) — in `State.size s + c.cost s + regBound + loopDepth`, uniformly over every program and input, with the machine really halting on the program's real output / in the accept-reject state matching its answer bit. The content was already proven (`paddedCompute_run`, `padBudget_le`, `physStepBudget_poly`); what was missing was a single readable statement, which is what let "is `Op.cost` faithful?" sit on the reviewer's *trust* list. It is off that list now. ⚠ The converse (no *over*charging) is deliberately NOT proven — it could only make our own `cost_le` obligations harder, never a proven bound weaker. Do not add it. |
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
| Proof-path size | ~16K LOC under `CookLevin/`. The ~15K LOC of parked hand-rolled `FlatTM` work (retired 2026-07-30-c) was **deleted 2026-08-03**; git history keeps it, and the methodology argument it was evidence for is below. |
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
  discharges every field and yields a real `polyTimeComputable'`.

- **The same hole is in the HYPOTHESIS of `NPhard''`, and it is the bigger one
  (2026-08-01, FINDING AN).** `InNPWitnessLangFreeSplit` lets the instantiator
  choose `encX`, the input layout the whole composite reduction is built on, so
  `HonestyAuditProbe` §7 presents an **arbitrary** predicate — undecidable ones
  included — with the answer planted in its input and gets `Q ⪯p' SAT` out of
  `SAT_NPhard''`, axiom-clean. No discipline on *our* witnesses could have
  discharged that: it is in the statement.

- **No law about `encX` can fix it; only removing the field can (FINDING AO).**
  §7b is a second cheat whose layout writes the whole raw input out
  (size-faithful, injective, `Serialize`-able) and merely *appends* the answer.
  So the planned "canonical `Serialize` on the input type" fix would not have
  worked either. **`NPhardStr`** (`Lang/HardnessStr.lean`) pins the input type
  to `List Bool` and the layout to `certState`; `CookLevinStr : NPcompleteStr
  SAT` follows from `CookLevin''` in one line and is the statement to quote.

- **At a chain END, `decodeOut`/`encodeIn` should come from a `Serialize`
  instance (2026-08-01).** `Lang/Serialize.lean` is the class (`dec_enc`,
  bit-level, and the two-sided size sandwich `size x ≤ sizeLB |enc x|` and
  `|enc x| ≤ encLen (size x)` — the lower half became a *polynomial* law on
  2026-08-05, FINDING AT); `Deciders/CnfSerialize.lean` and
  `Lang/SerializeStr.lean` are the two live instances and the worked examples of
  writing a parser + `dec_enc`. Risk S5's *tail* half is therefore no longer
  a reading obligation. There is deliberately **no generic product instance** —
  that is what made `LangEncodable` size-unsound, and by FINDING AK only the two
  concrete chain ends need one.

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

2. **Retire S3 — the honest reduction type.** ⚠ *Historical framing: this was
   written as a "migration" of `⪯p` to `polyTimeComputable'`. It was executed
   instead as a **replacement** — the honest line was built alongside and the
   `⪯p` API was deleted outright (2026-07-30-c, completed 2026-08-03). Read the
   sub-items for the work, not the framing.* Infrastructure is built **on the
   free line** (`⪯p'`, `reducesPolyMO'_of_langFree`; live instances
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
     `map`-over-lists gates parts (a near-complete draft existed in the
     parked subtree, deleted 2026-08-03 — git history).
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

⚠ **Never triggered, and now unreachable: Destination A was reached.** Kept as a
record of the fallback that was on the table. It said: if C2 or the S3 tail
ripple proved intractable, state `CookLevin` conditionally on a documented
axiomatic interface, keep the sound combinatorial tail, and stop. Trigger was
step 1 or 2 overrunning ~3×.

---

## Risk register

Two groups. **Group S** (soundness) determines *what the conditional theorem
currently means* — several entries are `sorry`-free. **Group C** (completion) is
the compiling-skeleton engineering. Refine the highest-ranked open item next.

### Group S — soundness gaps (mostly `sorry`-free, invisible to `#print axioms`)

| # | Gap | Location | Status / fix |
|---|-----|----------|--------------|
| **S3** | `⪯p` bounds **output size only**, never runtime — the enabling weakness that let S1/S2 typecheck and made `NPcomplete` too weak to be faithful. | ~~`NP.lean`~~, `Lang/PolyTime.lean` | ✅ **CLOSED by deletion (2026-07-30-c), and the notion itself is GONE (2026-08-03).** The honest line `⪯p'`/`NPhard''`/`NPcompleteStr` is the only one left, and it is now the only one in the library: `reducesPolyMO`, `ReductionWitness`, `PolyTimeComputableWitness`, `NPhard`, `NPcomplete`, `red_NPhard`, `NPhard_subtype_proj`, the nine wrapper theorems and the three downward bridges were deleted. Historical note: **Superseded, not migrated.** The honest line `⪯p'`/`NPhard''`/`NPcomplete''` is built end to end and `CookLevin''` quotes it; there is deliberately **no** `NPcomplete'' → NPcomplete` bridge. `⪯p` survives only under the legacy front, and dies with it. Historical note: **Engine live & endgame design SETTLED.** Honest target `polyTimeComputable'`/`⪯p'` built on the free line; live chain instances `kSAT3_reducesPolyMO'` and `flatTCC_reducesPolyMO'` (first sound-tail step, 2026-07-02). The `NPhard'` transport is settled & machine-validated: `SeamData`/`comp` (Cmd-level chain composition, fully proven) + `NPhard'`/`NPcomplete'`, hardness at endpoints only. Execute via plan step 2. |
| **S1** | **if-on-the-answer** `FlatSingleTMGenNP ⪯p FlatTCC` (all-zeros tableau, never simulates `M`). Was the deepest unsoundness. | ~~`Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`~~ (**deleted** 2026-07-30-c) | ✅ **CLOSED, and the dishonest file is GONE (2026-07-30-c).** Historically: closed on the honest line 2026-07-29-b. The tableau mathematics, both size bounds, the map, the guard, the correctness iff, all seven program stages and both head seams are built and axiom-clean; `FrontS1Comp.SAT_NPhard''` is unconditional and `sorry`-free. The vacuous `if (source is yes-instance) then yesInst else noInst` reduction that gave this risk its name was deleted with the legacy front — it was never proved, and nothing on the `CookLevin''` path referenced it. |
| **S2** | **dummy TM bridges** — `bridgeMachine` discards `M`; predicates ignore `M`. | ~~`LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean`, `L_to_LM.lean`, `NP/TM/IntermediateProblems.lean`, `Simulators/MultiToSingle.lean`~~ | ✅ **CLOSED by deletion (2026-07-30-c).** C8's per-`Q` front replaces the whole bridge stack, and the `Cmd` layer is single-tape by construction, so there is no multi-tape detour left to bridge. All five files are gone. |
| **S0** | **hardness reduction reaches a `sorry`** — `NPhard_GenNP` relies on `hasDeciderClassical` (`sorry`). Its second defect (the vacuous `fun _ => 0` size bound) is **fixed** — Part 0.1, 2026-07-04-b: the bound is now the honest `certBound n + timeBound (n + certBound n) + 3`. | ~~`GenNP_is_hard.lean`~~ (**deleted** 2026-07-30-c) | ✅ **CLOSED by deletion (2026-07-30-c).** `FrontS1Comp.SAT_NPhard''` proves the hardness half without ever touching `hasDeciderClassical`. ⚠ The `sorry` was *classically closable* by the cheating encoder — deleting it is what keeps that door shut. The honest replacement is `NPhard''`'s hypothesis: a real verifier witness. |
| **S5** | **ENCODING HONESTY IS NOT ENFORCED** — a witness's `encodeIn` must be the natural layout of its *input*, `decodeOut` the inverse of the natural *output* layout, and all reduction work must live in the `Cmd`. The trivial dishonest instantiation satisfies **every** field (machine-checked: `probes/HonestyAuditProbe.lean` §6 builds one). | the composed endpoint witness; the two verifiers | ⚠ **AUDITED 2026-07-30-c; PARTLY STRUCTURAL 2026-08-01; BOTH CHAIN ENDS PINNED 2026-08-02** (head: `encodeIn = encX`, i.e. `certState` under `NPhardStr`; tail: `Serialize cnf`) **— and since 2026-08-05 there is a SECOND chain, whose tail end is pinned by `Serialize (List Bool)`, i.e. by the SAME function as its head (`certState x = [Serialize.enc x]`, `rfl`; `HonestyGate` §5, verdicts 16–17).**<br> Per-witness verdicts below; evidence `probes/HonestyAuditProbe.lean`. **Tail: fixed structurally** — `FSATSATFree.decodeOut` is now `Serialize.dec` of one register (`Lang/Serialize.lean` + `Deciders/CnfSerialize.lean`, a real parser with `dec_enc`), so a new chain end owes an *instance*, not a reading (verdict 3). **Head: the hole was on the HYPOTHESIS side and it was bigger than believed** — `InNPWitnessLangFreeSplit` lets the *instantiator* choose `encX`, and `HonestyAuditProbe` §7 uses that to present an **arbitrary** predicate (undecidable ones included) with the answer planted in its input, obtaining `Q ⪯p' SAT` from `SAT_NPhard''`, axiom-clean (FINDING AN, verdict 12 corrected). §7b shows no law *about* `encX` can close it — appending the answer to an otherwise perfect encoding satisfies every no-compression / canonical-serialization law (FINDING AO). **The fix is a restriction, not a class**: `NPhardStr` (`Lang/HardnessStr.lean`) quantifies over string languages `Q : List Bool → Prop` with the canonical `certState` layout, where there is no `encX` field; `CookLevinHonest.CookLevinStr : NPcompleteStr SAT` follows from `CookLevin''` in one line (verdict 13). ⚠ Since 2026-08-07 the statement to quote is `SATStrComp.SATStr_NPcompleteStr'` — this verdict covers only the *hardness* conjunct, and FINDING AX is about the other one. ~~Remaining: the handed-over `1^(size x)` register at the head~~ — **removed 2026-08-02** (FINDING AP realised: `sizeLB` + `FrontPieces.tallyCells`; verdicts 2 and 14). What remains is *intermediate*-witness honesty, which by verdict 5 cannot license a cheat, and the irreducible definitional trust listed in the README. |

**S5 verdicts (2026-07-30-c).** The audit's structural result came first and is
what made it finite — see the "audit surface" note under "What we know".

| # | audited | verdict |
|---|---|---|
| 1 | **the audit surface itself** | ✅ `comp` sets `encodeIn := Wf.encodeIn` (leftmost) and `decodeOut := Wg.decodeOut` (rightmost), and `toFrameworkWitness'` hands exactly those to `ComputesBy` as `encode`/`decode`. So `Q ⪯p' SAT`'s honesty is **two functions**, not twelve. Machine-checked (`HonestyAuditProbe` §1, at both nesting levels). |
| 2 | `FrontWitness.encodeInQ` (**the** input layout of the whole chain) | ✅ **honest — and since 2026-08-02 there is nothing left to judge.** It is `W.encX x`, the *hypothesis witness's own* layout, verbatim: the layout `Q`'s verifier already reads. (It used to be `encX x ++ [1^(size x)]`, honest but requiring the reader to accept that a unary size tally is a *metric of the input* rather than work. The front program now counts those cells itself — `FrontPieces.tallyCells` — licensed by the new `sizeLB` field, so the register is gone.) |
| 3 | `FSATSATFree.decodeOut` (**the** output decoder of the whole chain) | ✅ **honest — and since 2026-08-01 STRUCTURAL.** It is `Serialize.dec` of one designated register: the canonical CNF **parser** `CnfSerialize.decCnf`, with `dec_enc` proven and no `Classical`, and a *constant* fallback off the image. (It was `Function.invFun encodeCnf` — correct, but noncomputable and unconstrained off the image, so the verdict rested on arguing the junk branch unreachable.) No input, no branch. |
| 4 | the five seams' `mfc`s | ✅ **honesty-irrelevant, by construction.** An `mfc` is a `Cmd` and runs inside the composite's program, so anything it does is *machine work*. (They are in fact pure `clearRange` scrubs — `probes/SeamS1Probe.lean` §1 pins the erase sets — but that is a frame fact, not an honesty fact.) |
| 5 | the four intermediate `encodeIn`s (`S1Witness`=`headEncodeIn`, `FlatTCCFree`, `FlatCCBinFree`, `BinaryCCFSATFree`, `FSATSATFree`) | ✅ **honesty-irrelevant, and independently honest.** Irrelevant because each appears only on the **right** of a `SeamData.bridge` obligation — the composed program is *required to produce it*, so a dishonest layout could only make the bridge harder, never license a cheat. Independently: each is a fixed-register spread of the input's own fields (unary numbers, sentinel streams), and each `decodeOut` is `Function.invFun <injective natural output key>`. So the **per-step** `⪯p'` theorems quoted in the README are honest too. |
| 6 | the reduction maps' guards | ✅ **honest.** `s1Map` branches on `s1GuardB M s` (validity of the flat TM), `FlatCC_to_BinaryCC_instance` on `isValidFlattening C`, `BinaryCC_to_FSAT_instance` on `BinaryCC_wellformed C`; `flatTCC_to_flatCC` and `fsatToSat` are unguarded. Every guard is a decidable property of the **input's structure**, never of the answer — the S1 original sin (`if source is yes-instance then …`) is gone with the legacy file that held it. |
| 7 | `fQ`, the front instance | ✅ **honest, and it is what makes hardness non-vacuous.** `fQ x = (MQ W.verifier.c …, 3 :: encodeRegs (encX x), maxSize x, steps x)`: the emitted machine is built **from `Q`'s own verifier program**. Textbook Cook–Levin. |
| 8 | membership: `satEncX` / `satEIn` | ✅ **honest.** `satEncX N` is *registers `0`–`2` of the live verifier's own `encodeState`* (`= encodeState (N,a) |>.take 3`, `rfl`), plus the **raw** certificate register. Register 1's `1^\|N\|` is derived, but inherited — `evalCnfDecidesLang` already demands it as `CLAUSE_TALLY`. Bits → assignment is done by `certDecode`, a `Cmd`. |
| 9 | membership: non-vacuity | ✅ **machine-checked, not audited.** `satRel_correct : polyCertRel SAT satRel` *is* soundness + completeness + a polynomial certificate bound. Nothing to read. |
| 10 | `InNPWitnessLangFreeSplit.encX_size` | ⚠ **not an honesty check** — measured slack `23` vs `≥ 200000`. It constrains nothing; do not cite it as one. |
| 11 | `S1Witness.S1CostBound.cost_bound` | ✅ **nothing depends on it definitionally.** It is an anonymous `Exists.choose`, and the whole project builds — so no consumer unfolds it to `S1Map.s1Bound`. |
| 12 | the *hypothesis* side of `NPhard''` | ❌ **CORRECTED 2026-08-01 — the 2026-07-30-c verdict ("honest by design") was WRONG.** Quantifying over `InNPWitnessLangFreeSplit Q` does rule out the `inNP` cheat (standing risk #6), but it leaves `encX : X → State` a free field of the hypothesis — and the composite reduction's `ComputesBy.encode` is built from it. `probes/HonestyAuditProbe.lean` §7 exhibits a complete, `sorry`-free witness for an **arbitrary** predicate with `encX x = [[if Q x then 1 else 0]]` and a no-op verifier; §7b does the same with a size-faithful, injective, `Serialize`-able layout that merely *appends* the answer. Both yield `Q ⪯p' SAT`. `NPhard''` is therefore only as strong as the presentation a reader plugs in. |
| 13 | the *hypothesis* side of `NPhardStr` (the **hardness** conjunct of the statement to quote) | ✅ **honest, structurally.** `InNPWitnessStr` fixes the input type to `List Bool` and the layout to `certState`, so there is no `encX` field to choose: the composite's encode is `certState x` — the raw input string, one register, one cell per bit (`HonestyAuditProbe` §8, `rfl`; it was `certState x ++ [1^(size x)]` until 2026-08-02). The verifier must decide from that string. `CookLevinHonest.CookLevinStr : NPcompleteStr SAT`, axiom-clean, derived from `CookLevin''` in one line. |
| 14 | the `sizeLB` field of `InNPWitnessLangFreeSplit` (**new 2026-08-02**) | ✅ **a genuine strengthening of the hypothesis, and it kills one cheat outright.** `encodable.size x ≤ sizeLB (State.size (encX x))` with `sizeLB` polynomial: the input's size must be recoverable from its own layout. §7's answer-planting layout is one cell wide for every input, so no `sizeLB` exists over an unbounded type — `HonestyAuditProbe.HypothesisCheat.badEncX_no_sizeLB` **proves** it, and `badSplitWitnessOf` keeps every other field discharged so it is machine-checked that this field is the sole obstruction. ⚠ It does **not** rescue `NPhard''`: §7b satisfies `sizeLB` by writing the input out and appending the answer (FINDING AO). Its real payoff is verdict 2 — the head encoding may now be `encX` itself. Live instance: `EvalCnfSplit.satSplitWitnessOf` takes `sizeLB := id`, from `CnfSerialize.size_le_encodeCnf_length`. |
| 15 | `SATStr`'s witness (**new 2026-08-04**) | ✅ **honest.** It is an `InNPWitnessStr`, so by verdict 13 there is no `encX` to audit — the input layout is `certState x` by the statement. What a reader must check instead is that the *language* is SAT: `SATStr.satStr_iff` proves `SATStr x ↔ ∃ N, strBits x = encodeCnf N ∧ SAT N`, and `CnfWellFormed.not_sat_botCnf` proves the junk branch (`[[]]`) is unsatisfiable, so a non-encoding is out of the language rather than silently in it. The verifier is not a no-op: `SATStr.verifier_reads_certificate` runs the composite program on one input at two certificates and gets two verdicts, and `verifier_rejects_malformed` shows a non-encoding rejected. The re-encoder owes no `decodeOut` (it is a verifier, not a reduction). |
| 16 | `SATToSATStr.decodeOut` — **the SECOND chain's output decoder** (new 2026-08-05) | ✅ **honest, and structurally so.** Extending the chain at the tail *moves* the rightmost `decodeOut` (FINDING AK), so it is a fresh obligation and it is discharged by an instance, not a reading: `Serialize.decodeD` of one designated register, instance `Complexity.Lang.instSerializeListBool` (`enc := strBits`, `dec := decBits`, `dec_enc` proven, no `Classical`, constant fallback). What makes this the *smallest* such obligation in the development: `Serialize.enc = strBits` is **the same function** as the canonical head layout (`certState x = [Serialize.enc x]`, `rfl`, gated in `HonestyGate` §5), so a reviewer who has read `strBits` once for the head has read the tail too. |
| 17 | `SATToSATStr.encodeIn` and the no-op program (new 2026-08-05) | ✅ **honest — and the no-op is a measurement, not a licence.** `encodeIn N = [Serialize.enc N]` is the canonical CNF layout, and by verdict 5 an intermediate `encodeIn` cannot license a cheat anyway. The program being `copy r r` is *correct*: `strBits (satToStr N) = encodeCnf N`, so the map really is the identity on cells and there is nothing for a machine to do. ⚠ The distinguishing question against `HonestyAuditProbe` §6 (where a no-op `Cmd` **is** dishonest) is *who does the work*: there, `encodeIn`/`decodeOut` compute; here both are fixed canonical layouts pinned by `Serialize` instances and the *map* is the identity. The real content sits in `satStr_satToStr`, which is not trivial — it needs `encodeCnf` injective. |

**The legacy `⪯p` notions are GONE (2026-08-03) — do not reintroduce them.**
The 2026-07-30-c decision was to *retain* them (unused, on the grounds that `⪯p`
is weak rather than wrong and `⪯p'` is defined as a strengthening of it). That
was reconsidered and reversed: a vacuous notion with no live consumer, sitting
one bridge (`reducesPolyMO'_to_reducesPolyMO`) away from the real statement, is a
way for a reader to derive `NPcomplete SAT` from `NPcompleteStr SAT` and come
away with the wrong theorem. Reading is the only thing standing between this
development and its claim, so the reading hazard outweighed the convenience.

Deleted, in one commit: the nine `⪯p` wrapper theorems (`kSAT_to_SAT`,
`kSAT_to_FlatClique_poly`, `FlatTCC_to_FlatCC_poly`, `FlatCC_to_BinaryCC_poly`,
`BinaryCC_to_FSAT_poly`, `FSAT_to_SAT_poly`, `FSAT_to_3SAT_poly`, plus
`reducesPolyMO_reflexive`/`_transitive`); the `NP.lean` block (`NPUniversal`,
`ReductionWitness`, `reducesPolyMO`/`⪯p`, `reducesPolyMO_elim`, `NPhard`,
`NPcomplete`, `red_NPhard`, `NPhard_subtype_proj`, `PolyTimeComputableWitness`,
`polyTimeComputable`); and the bridges (`polyTimeComputable'_to_polyTimeComputable`,
`reducesPolyMO'_to_reducesPolyMO`, `NPhard'_to_NPhard`,
`NPcomplete'_to_NPcomplete`, `PolyTimeComputableLang.toFrameworkWitness`).

**What survived and why.** Every reduction *map*, its correctness lemma and its
output-size bound (`kSAT_to_SAT_correct`, `kSAT_to_FlatClique_f_size_bound`,
`FSAT_to_SAT_size_le`, …) — that is real mathematics and is what a future `⪯p'`
witness for those steps is built from. `PolyTimeComputableWitness`'s four
size-bound fields are **inlined into `Lang.PolyTimeComputableWitness'`**: the
output-size bound is genuine content (`PolyTimeComputableLang.output_size_le`
discharges it, seam length arguments consume it), it simply was never
*sufficient*, and having it as a separate structure named for *time* invited
exactly the "the size bound is the reduction" reading this project spent three
sessions removing. `inNP` is still produced by `sat_NP`, `FlatClique_in_NP` and
`inNP_kSAT3_free`, and consumed by nothing — it is the *framework* notion the
free line bridges into, not part of the `⪯p` API.

| **S7** | **vacuity of the published hardness statement** — `NPhardStr SAT` quantifies over `inNPStr Q`; if that class were empty the theorem would be vacuously true, and if it were everything the theorem would not be about NP. Sessions 2026-07-30…2026-08-02 made the class progressively harder to inhabit and **none checked that anything still inhabited it**; until 2026-08-03 the library contained no `InNPWitnessStr` at all. | `Complexity/NonVacuity.lean` | ✅ **CLOSED both directions (2026-08-03), gated.** *Inhabited*: `inNPStr_squareStr` (complete `InNPWitnessStr` for `SquareStr`, certificate load-bearing, language separates strings) and `squareStr_reducesPolyMO'_SAT : SquareStr ⪯p' SAT`. *Not everything*: `searchDecide_correct` — for any `W : InNPWitnessStr Q` and certificate bound, `Q x ↔ searchDecide W bound x = true`, where `searchDecide` is a **running** `def` that enumerates the certificate space and executes `W`'s own verifier `Cmd`; hence no undecidable `Q`. `searchDecide_calls` states the `2^(bound+1) - 1` cost. ⚠ **Open rung, do not overstate:** `searchDecide` is a Lean function, not a `Cmd`/`FlatTM`. `inNPStr Q → ∃ f, Nonempty (DecidesBy Q f)` inside this development's own computability model needs the search compiled to a `Cmd` with an exponential cost bound — HANDOFF top-down item 2. ⚠ Second open rung, **closed 2026-08-04**: `SquareStr` is in **P**, so it said nothing about the class containing anything hard. `SATStr` (`Deciders/SATStr.lean`) is the upgrade — SAT itself as a bit-string language, complete `InNPWitnessStr`, and `NonVacuity.satStr_reducesPolyMO'_SAT : SATStr ⪯p' SAT`. The scoping was wrong: an on-machine CNF *parser* is not needed, because `encodeCnf` is already a flat 0/1 stream and `certState` is already one register of 0/1 cells — see the FINDING AS row. ⚠ ~~What is still NOT claimed is `NPhardStr SATStr`~~ — **claimed and proven 2026-08-05**: `SATStrComp.satStr_NPhardStr` / `SATStr_NPcompleteStr`, gated in `NonVacuity.lean` as `npcompleteStr_SATStr`. The class's inhabitant is now NP-**complete** in this development's own sense, both halves proven here — the strongest non-vacuity statement available. The only rung left under S7 is the `Cmd`-level certificate search. |
| **S8** | **the READING surface of the published statement is unbounded and unverified** — everything this register closes is about whether the theorem is *proved*; none of it says how much of *our own code* a reviewer must read to know the theorem is the right theorem. The README named four topics, but that list was prose: nothing computed it, nothing checked it was complete, and nothing would have noticed a later session pulling another definition into a headline's statement. For a development whose entire thesis is "you should not have to trust us", a hand-maintained list of what you must trust is the wrong shape. | `Complexity/Meta/StatementSurface.lean`, `Complexity/StatementGate.lean` | ✅ **CLOSED (2026-08-06), gated by `lake build`.** `#assert_statement_surface thm => n₁ …` computes the repository-local constant closure of a theorem's **type** — descending through definition bodies, inductive constructors and field types, stopping at Lean core / Mathlib, and **not** through proofs — and fails elaboration unless the set is *exactly* the list given. Equality, not containment, so the list can neither grow silently nor rot into a vacuous superset. `Complexity/StatementGate.lean` carries the two lists, grouped in reading order (what-is-claimed · the layer · the machine · SAT · input size) and is now the reviewer's entry point. **Measured: 103 definitions behind `CookLevinStr`, 113 behind `SATStr_NPcompleteStr`.** ⚠ **The measurement corrected a claim of the plan of record**: the string-language headline's statement surface is *larger*, not smaller — `SATStr` is **defined by parsing** (`cnfOf = parseTotal ∘ strBits`), so the well-formedness scanner and the CNF parser are literally part of what it says; the cheaper route through `EvalCnfCmd.encodeCnf` is `satStr_iff`, a **theorem**, not a definition. ⚠ Equally worth saying: no reduction, no `decodeOut` and no `Serialize` instance appears in either surface, because they are existentially quantified — which is *why* encoding honesty (S5) needs its own gate and cannot be read off the statement. The two claims are separate and have separate instruments. Negative controls: `probes/StatementSurfaceProbe.lean`. ⚠ **AUDITED 2026-08-07 — the 103 have been read; verdicts below, and one of them is a defect in the published statement (FINDING AX).** |

**S8 verdicts (2026-08-07, top-down).** Somebody read the 103 definitions the
statement gate enumerates and asked of each: *could a subtly wrong definition
here make the headline true but meaningless, and would anything notice?* The
verdicts are grouped as `Complexity/StatementGate.lean` groups them. **Wherever a
verdict was checkable rather than merely arguable it is checked by the build** —
`Complexity/StatementMeaning.lean`, the section numbers below.

| # | audited | verdict |
|---|---|---|
| 1 | **the headline, unpacked** (`NPcompleteStr`, `NPhardStr`, `reducesPolyMO'`, `ReductionWitness'`) | ✅ **it is the textbook statement, and the build now says so in ordinary language.** `StatementMeaning.hardness_spelled_out` restates the hardness half as *for every NP string language `Q` there is a polynomial-time computable `f : List Bool → cnf` with `Q x ↔ SAT (f x)`*, and **proves it from the headline**, so the restatement cannot drift. ★ The structural point a reviewer should take from it: `f` is an ordinary Lean function and `reduction_correct` is an honest `↔` about it, so **no encoding and no machine anywhere in this development can weaken that equivalence**. What `polyTimeComputable' f` adds on top — a real `FlatTM` inside a polynomial bound — is stated through the witness's own `encode`/`decode` and is the half risk S5 exists for. Take the two apart there. |
| 2 | `DecidesLang.decides`, i.e. `Cmd.decides` — *is rejection a real verdict?* | ✅ **yes, two-sided.** `∀ x, (P x ↔ isAccept) ∧ (¬P x ↔ isReject)`, and `isAccept`/`isReject` are independent tests of register `0` against `[1]` and `[0]`. A state can fail both — `StatementMeaning` §2 exhibits two — so the second conjunct is a positive obligation on the program, not the negation of the first. A one-sided "accepts iff `P`" reading would have admitted a verifier that leaves the output register junk on negative instances; this does not. |
| 3 | `ComputesBy` — *does it demand the machine halt, or only that a halting run has the output?* | ✅ **it demands halting** — but ⚠ **not through the conjunct a reader will pick.** `runFlatTM` is **total**: out of budget, halted, and *stuck* (no matching transition) all return `some`, so `= some cfg` is vacuous. The content is entirely in `haltingStateReached M cfg = true`, which requires the machine to sit in a state its own `halt` table marks halting within `timeBound (size x)`. `StatementMeaning` §4 pins a transition-free, halt-free machine that "runs" 100 steps and returns its initial configuration. |
| 4 | `polyCertRel` / `PolyCertRelWitness` — *is the certificate bound on the right side?* | ✅ **yes.** `sound : R x y → P x`, `complete : P x → ∃ y, R x y ∧ encodable.size y ≤ bound (encodable.size x)`, `bound` `inOPoly` and monotone. The certificate's size is bounded by a polynomial **in the input's** size — the correct direction; the reverse would have permitted certificates that carry the answer's whole computation. |
| 5 | `inO` / `inOPoly` / `monotonic` | ✅ **the textbook definitions**, re-confirmed by reading (spot-checked 2026-08-06, recorded here rather than re-derived): `inO f g = ∃ c n₀, ∀ n ≥ n₀, f n ≤ c·g n`, `inOPoly f = ∃ k, inO f (·^k)`, `monotonic f = ∀ x ≤ x', f x ≤ f x'`. |
| 6 | group 2 as a whole — `Op.eval`/`Op.cost`/`Cmd.run` | ✅ **concrete definitions, no axioms, and the cost model is the audited one.** `Cmd.run` is one structurally recursive pass returning (state, cost); `forBnd` samples its bound register's length **once at entry**, so the layer is **total by construction** — no program in it can diverge, which is why "cost" is a closed form and not a partial function. `Op.cost` is size-aware (`copy`/`tail`/`concat`/`eqBit` charge for the data they move), and whether that is a faithful proxy for `stepFlatTM` time is **not re-opened here**: `Complexity/CostFaithfulness.lean` proves it and this verdict cites it. |
| 7 | ❌ **`NPcompleteStr`'s MEMBERSHIP conjunct — `inNPLangFreeSplit P` — is VACUOUS (FINDING AX, new)** | ❌ **and now fixed.** `InNPWitnessLangFreeSplit` still carries the free input layout `encX`, and by FINDING AO no law about `encX` can exclude "the honest encoding, plus one register holding the answer". Nobody had drawn the conclusion for the **conclusion** side: `probes/HonestyAuditProbe.lean` §7c now proves `inNPLangFreeSplit Q` for an **arbitrary** `Q : List Bool → Prop`, undecidable ones included. A conjunct true of every language is not a claim about `P`. **The fix is the same shape as `NPhardStr`'s — remove the field, do not add a law**: `Complexity.Lang.NPcompleteStr' P = NPhardStr P ∧ inNPStr P` pins the membership layout to `certState` as well, and `SATStrComp.SATStr_NPcompleteStr'` proves it **at zero cost** — `SATStr.satStrWitness` was already an `InNPWitnessStr` and the old headline was discarding exactly the `encX_canonical` field that makes the conjunct real. ★ **`SATStr_NPcompleteStr'` is the statement to quote.** ⚠ `CookLevinStr : NPcompleteStr SAT` cannot be strengthened the same way — `SAT` lives on `cnf`, not `List Bool`, and `inNPStr` is only defined for string languages; that is a third independent reason to prefer the `SATStr` headline. |
| 8 | `InNPWitnessStr` / `inNPStr` / `certState` (the hardness hypothesis) | ✅ **nothing left to choose, as designed.** `encX_canonical : ∀ x, encX x = certState x` and `certState c = [c.map (fun b => if b then 1 else 0)]` — one register, one cell per bit. This is S5 verdict 13 restated from the statement side, and it is what verdict 7 has now brought the membership half up to. |
| 9 | `writeCurrentTapeSymbol` — **the one a reviewer will stumble on** | ✅ **deliberate, locked, and the alternative is unsound.** It replaces in range, **appends** exactly at the frontier and is a silent **no-op** strictly beyond. That reads like a restriction smuggled in to make the tableau work; it is the opposite. The zero-padding jump-write it replaced let one step materialise cells arbitrarily far from the head — non-local, so no three-cell-window simulation can track it, and `cookTableau_correct` was **false as stated** against `validFlatTM`-valid adversarial machines (`probes/S1TableauProbe.lean` §5). Pinned in `StatementMeaning` §3 together with two facts a reader also needs: the tape is **one-way infinite** (`Lmove` at `0` is a no-op) and a cell past the frontier reads **`none`, not `some 0`** — blank and zero are not confused. |
| 10 | `stepFlatTM` / `entryMatchesConfig` / `validFlatTM` | ✅ **a deterministic machine, honestly.** `stepFlatTM` takes `M.trans.find?`, so the *first* matching entry wins and the machine is deterministic even if the table lists a key twice; `validFlatTM` accordingly does **not** require the table to be functional, which is a completeness gap in the *validity predicate* and not a soundness one (no proof relies on uniqueness). Determinism here is correct: this is Cook–Levin, so nondeterminism belongs to the certificate, not to the machine. `haltingStateReached` reads `M.halt.getD idx false` — out of range is *not* halting, the conservative direction. |
| 11 | group 4 — `SAT`, `cnf`, `clause`, `literal`, `assgn`, `evalCnf`/`evalClause`/`evalLiteral`/`evalVar` | ✅ **satisfiability, and the degenerate cases are the right way round.** An `assgn` is a `List var` read as *the set of true variables*; a literal `(s, v)` is satisfied when `v`'s value equals `s`; a clause is `List.any` (disjunction), a CNF is `List.all` (conjunction). The two easy-to-invert cases both check out and both are pinned in `StatementMeaning` §5: the **empty clause is unsatisfiable**, the **empty CNF is satisfiable**. `SAT` is pinned neither identically true nor identically false (a satisfiable formula, the canonical `[[]]`, and `x ∧ ¬x`). |
| 12 | ⚠ **`encodable.size` on `Nat` is `id` — every number in this development is measured in UNARY** | ⚠ **honest, but it must be said, and it is an argument about which headline to quote.** On the **hardness** side the measure is faithful and this does not arise: an input is a `List Bool` and its size is between its length and twice it (`StatementMeaning` §6). On the **membership** side `SAT`'s input is a `cnf` whose measured size counts each variable *index* in unary, so a formula mentioning variable `2^40` measures as astronomically large, and a polynomial bound in that measure is a **weaker** claim than the same bound over a binary encoding. It is not a cheat, because the measure **agrees with the layout the machines actually use** — everything on the proof path is a flat `0`/`1` stream with numbers unary (`Compile.BitState`, `sig = 4`), and `sizeLB` forces the input's size to be recoverable from its own layout's cell count, so the polynomials really do bound real time on a real tape. ★ Over `SATStr` the question does not arise on either side: the input **is** the bit string, and `instEncodableNat` is precisely the one name of the 103 that is *not* among the 113. |
| 13 | ⚠ `encodable.size_ge_logical` | ⚠ **vacuous, and it has no consumers.** The class law reads `∀ x, ∃ n : Nat, size x ≥ n`, which `n := 0` discharges for *any* function — `StatementMeaning.size_ge_logical_is_vacuous` proves it without mentioning `encodable`. A `grep` finds it only at the twelve instance-definition sites. A reviewer should be told not to look for content in it: `encodable` is a `size` function and nothing else, and everything that constrains `size` is stated where it is used (`InNPWitnessLangFreeSplit.sizeLB`, `Serialize`'s size sandwich, `DecidesLang.encodeIn_size`). Harmless, but it is dead weight in a reading list whose whole point is that every item on it matters. |
| 14 | ⚠ **the reading list contained two files whose own docstrings said the definitions were `axiom`s (FINDING AY, new)** | ⚠ **FIXED 2026-08-07.** `Lang/Syntax.lean`'s header said "`eval`, `cost`, and `Compile` … are deferred … (declared as `axiom`s in `Semantics.lean` and `Compile.lean`)" and `Lang/Semantics.lean`'s said "The definitions are deferred to Part 3.2; the skeleton commits to the *signatures*". Both were true in May 2026 and false since; the axiom gate proves the library has **no** bespoke axiom. These are the first two files of group 2 — a reviewer working the list top-down met them immediately and was told the semantics of the language every witness is written in were unproven placeholders. **The generalisable lesson: the statement gate measures definitions, and prose is not a definition. Audit the docstrings *inside* the surface, not only the code — a stale comment in the reading list is worth more damage than a stale comment anywhere else, because the reading list is exactly what a reviewer is instructed to trust.** |
| 15 | `flatTM` (the `abbrev` of `FlatTM`) | ✅ cosmetic — the surface carries both names for one structure because `abbrev`s are transparent to the closure. Nothing to check; noted so the next reader does not go looking for a second machine type. |

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
λ-calculus). The measured evidence: ~15K LOC of hand-rolled `FlatTM` work got a
fraction of the way, against ~16K LOC on the layer that finished the whole
theorem. That subtree was retired 2026-07-30-c and deleted 2026-08-03 — it is in
git history, and its `FlatTM` run lemmas were in any case stale (several *false*)
against the append-only-at-the-frontier tape of 2026-07-17.

---

## References

- Coq source: <https://github.com/uds-psl/cook-levin>.
- Status / orientation: root [`README.md`](../README.md).
- Working plan for the next session: [`HANDOFF.md`](HANDOFF.md).
