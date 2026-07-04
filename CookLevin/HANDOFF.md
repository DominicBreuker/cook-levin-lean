# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). This file is the forward-looking working plan; we
work **multi-session in two alternating streams** — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

## Where the proof stands (2026-07-05; session 3 part 1 in progress)

- **In-NP side: DONE & axiom-clean.** `SAT_inNP.sat_NP`, `FlatClique_in_NP`,
  `KSat3Free.inNP_kSAT3_free`, `KSat3Free.kSAT3_reducesPolyMO'` are all
  `[propext, Classical.choice, Quot.sound]`.
- **The S3 migration is EXECUTING and the endgame design is VALIDATED LIVE.**
  Live honest `⪯p'` witnesses `kSAT3_reducesPolyMO'`, `flatTCC_reducesPolyMO'`,
  `FlatCCBinFree.flatCC_reducesPolyMO'`, and the **first COMPOSED live `⪯p'`**
  `FlatTCCBinComp.flatTCC_to_binaryCC_reducesPolyMO' : FlatTCC ⪯p' BinaryCC`
  (first live `SeamData`/`comp`). All axiom-clean. **Next chain step
  `BinaryCC ⪯p' FSAT`: the program is BUILT & `#eval`-validated (session 2); its
  witness proofs are the next top-down session.**
- **Headline `CookLevin` still depends on `sorryAx` — wholly hardness-side.**
  `sorry`s in built code: `red_inNP`'s `inTimePoly` half (`NP.lean`),
  `hasDeciderClassical` (`GenNP_is_hard.lean`), 2× `CookTableau` (S1), 3×
  `MultiToSingle` (dead code). Plus the `sorry`-free **vacuous** defs (S1/S2 +
  size-0 hardness reduction) invisible to `#print axioms` — Group S.
- **The compiler (Risk C2) is DONE and CLEAN.** All **9** ops proven &
  axiom-clean; `compileOp_sound_physical_residue` is fully proven with no
  side-conditions. The retired value-as-length trio and BOTH isolation walls
  (`NoConsLen`, `IsSupported`/`AllOpsSupported`) are **deleted**: `Op` has
  exactly the 9 live constructors, the witness structures carry no wall fields,
  and the compiler chain threads no `hnc`/`hsupp`. **No bottom-up compiler debt
  remains.**
- **Part 0.1 (the encodable sweep) is DONE (bottom-up, 2026-07-04-b).** The
  size-0 `instEncodableDefault` fallback is **DELETED** — a type without a real
  `encodable.size` is now a compile error. The front-chain instance types
  (`GenNPInput`/`LMGenNP.Instance`/`mTMGenNPFixedInput`/`TMGenNPFixedInput`)
  carry real data-field-sum sizes, and every `fun _ => 0` output-size bound
  they licensed is replaced by an honest polynomial bound —
  including `NPhard_GenNP`'s (now `certBound n + timeBound (n + certBound n)
  + 3`, poly+mono from the witness fields). All re-proven bridges axiom-clean;
  headline axiom profile unchanged (`sorryAx` = hardness half only). **C8 is
  no longer gated on Part 0.1.**

## ★ Latest sessions

- **2026-07-05 (top-down), `BinaryCC_to_FSAT` session 3 part 1:** the run-lemma
  stack is STARTED and the fold-invariant methodology is now PROVEN to work on
  this program (previously only design/`#eval`-validated). Landed, sorry-free
  & axiom-clean (`[propext, Quot.sound]`, no `Classical.choice` even):
  `encodeIn_size_le` (`≤ 2·size+1`, plan step 1 — DONE) and
  `emitBitsFromScan_run` (plan step 2's first leaf: the direct/unencoded
  bit-list emitter, including its own serialization sub-lemmas `litFor`/
  `bitsPrefix`/`serF_encodeBitsAt`/`bitsPrefix_append`/`bitsPrefix_take_succ`
  and the OUT-only literal-tag gadget lemmas `emit{0,1,Ftrue,FandTag,VarW,
  LitAt}_run`/`_frame`). **This is the template for every remaining run
  lemma** — see NEXT TOP-DOWN. Two proof-engineering gotchas surfaced and are
  recorded below ("Conventions"): the `whnf` timeout from un-cleared nested
  `State.set` chains, and the `show`-vs-`rw` trap when a composed `Cmd.eval`
  must be threaded down to a named end state.
- **2026-07-05 (top-down), `BinaryCC_to_FSAT` session 2:** the whole reduction
  program `buildFSAT : Cmd` + `encodeIn` is BUILT & `#eval`-validated
  end-to-end (`Reductions/BinaryCC_to_FSAT_free.lean`, `probes/FSATSerProbe.lean`
  §4 — wellformed, all four guard-failure shapes, and the `decodeF` round-trip
  all check). The crux engineering risk (nested-loop var-index arithmetic on a
  TREE output) is resolved; **what remains is pure proof work** — see NEXT
  TOP-DOWN.
- **2026-07-04-b (bottom-up), Part 0.1 DONE:** real `encodable.size`
  everywhere; the size-0 default fallback deleted (see "Where the proof
  stands"). Scoping finding: the chain intermediates (FlatTCC/FlatCC/BinaryCC/
  formula/CC/TCC/FlatTM/cnf) already had real sizes — the actual hole was the
  four *front* instance types and the `fun _ => 0` bounds they licensed.

**Composite tail exit layout** (unchanged; what the NEXT tail seam
re-encodes/scrubs): BinaryCC outputs at regs 17 `offset`/18 `width`/19 `init`
(raw bits)/20 `cards`/21 `final` (sentinel bit-lists)/5 `steps`; DIRTY at exit:
intermediate FlatCC inputs in 1/2/4/6/7/8 and scratch 9–16, 23, 24, 25 (`BOUT`),
26. Regs 0, 3, 22 are `[]`.

## The free line — the working architecture (use this, and only this)

- **Verifiers**: free `DecidesLang` with bespoke bit-level `encodeIn`
  (numbers UNARY) → `DecidesLang.toDecidesBy`/`toInTimePoly` (live:
  `evalCnfDecidesLang`, `cliqueRelDecidesLang`).
- **NP witnesses**: `InNPWitnessLangFree`/`inNPLangFree` (+ `inNPLangFree_to_inNP`).
- **Reductions**: free `PolyTimeComputableLang` → `toFrameworkWitness'`/
  `reducesPolyMO'_of_langFree`; verifier precomposition via
  `DecidesLang.FreePrecomposeData`/`red_inNP_of_langFree`; **witness-witness
  composition via `SeamData`/`comp` — now LIVE**
  (`FlatTCCBinComp.flatTCC_to_binaryCC_seam`, the model for every next seam).
- **Templates for new reduction witnesses** — copy these, not first principles:
  - `NP/kSAT_to_SAT_free.lean`: re-encoder + reduction sharing one program,
    fold invariants, tight `encodeIn_size`, `FreePrecomposeData`.
  - `Reductions/FlatTCC_to_FlatCC_free.lean`: the sound-tail unguarded-map
    pattern (backward validity transfer + unconditional iff), shared-layout
    registers, `blockMove`/`halfMove` stream re-formatting, `encSList`
    prefix-free injectivity, multi-field decode via `Function.invFun encKey`.
  - `Reductions/FlatCC_to_BinaryCC_free.lean`: **the guarded-map pattern** —
    on-machine validity flag (`allLtB` reflection ↔ `isValidFlattening` via
    `validB_iff`), guard branch to the no-instance, the item view of sentinel
    streams (`encItems`/`expandItems` — ONE loop lemma for cards+final via a
    shared scratch output `BOUT` + copy-out), unary multiplication
    (`mulLoop_run`), truncated-subtraction compare.
  - `Reductions/FlatTCC_to_BinaryCC_comp.lean`: **the seam pattern** — scrub
    `mfc`, `interval_cases`-bridge over the frame, constant seam budget.
- **The canonical `LangEncodable` layer stays DEAD** (generic product encoding
  is size-unsound — `probes/UnaryProductSizeProbe.lean`). Do not rebuild it.

### ⚠ Standing architecture risks — check every new witness against these

1. **Honesty is per-witness discipline, not enforced.** `eIn`/`encodeIn` must
   be the natural layout of the *input* (never of `gmap v`), `decodeOut` the
   inverse of the natural *output* layout, all reduction work in the `Cmd`.
   The trivial dishonest instantiation satisfies every field — review each
   witness. (Shared-layout registers for identity fields are fine.)
2. **Seam discipline** (VALIDATED this session): pin each new witness's input
   layout to its predecessor's exit frame and document the exit layout
   (dirty registers included) for the successor. Watch that C8's per-`Q`
   witness can actually target the chain's fixed input layout — probe this
   when C8 is scoped.
3. **Guard-or-no-guard is a per-step decision**: probe invalid→invalid ON
   PAPER before coding (counterexample method: pick a tiny invalid instance,
   check whether its image is accidentally wellformed+satisfiable).
4. **The front instance types are size-MEASURED, not string-encodable**
   (Part 0.1 finding): `GenNPInput.rel` / `mTMGenNPFixedInput.accepts` /
   `TMGenNPFixedInput.accepts` are abstract predicates, so their
   `encodable.size` counts only the data fields (tapes + the two numeric
   parameters). That is honest for `⪯p` size bounds, but **no TM can consume
   these types as inputs** — C8 must replace the abstract front with
   concrete-machine types (the settled S2-collapse design). Never add a
   size-0 instance to "fix" a missing-instance error; the fallback was
   deleted deliberately.

---

## NEXT BOTTOM-UP session — C8 scoping probe (now UNGATED by Part 0.1)

Part 0.1 is done, so the last foundational gate on **C8** (the real
universal-source decider replacing `hasDeciderClassical`, subsuming S2) is
gone. C8 is the biggest remaining hardness-side unknown after S1, and it has a
**standing un-probed design risk** (architecture risk #2: can the per-`Q`
front witness actually target the chain's fixed input layout?). A time-boxed
scoping session, not a build session:

1. **Scope the shape.** Read `GenNP_is_hard.lean` (the docstring on
   `hasDeciderClassical` sketches the Part-7 plan) + `GenNP.lean` +
   `Lang/PolyTime.lean` (`SeamData`). Answer on paper: what concrete type
   replaces the abstract-`rel` `GenNPInput` front (standing risk #4 — the
   predicate fields must become concrete machines/programs), what does the
   per-`Q` `DecidesLang` for `genNPRel` look like on the free line, and where
   exactly does its `SeamData` plug into the chain head
   (`FlatSingleTMGenNP`'s input layout)?
2. **Probe the seam-targeting risk** (`#eval`, additive): build a toy per-`Q`
   witness for one tiny `Q` and check register-by-register (`AgreeBelow`, the
   `FlatCCBinProbe.checkBridge` pattern) that its exit frame can feed the
   chain-head input layout.
3. **Verdict + decomposition**: feasible / feasible-but-expensive /
   trigger-fallback, plus a `sorry`-decomposed skeleton list for the build
   sessions. Do NOT start building the decider inside the scoping session.

**Alternative (if C8 scoping stalls or a shorter session is wanted):** the
`FSAT_to_SAT` free witness (Tseytin as a `Cmd`; the last small sound-tail
item). Paper-probe the guard question first (formula inputs have no invalid
instances — expect the unguarded pattern of
`Reductions/FlatTCC_to_FlatCC_free.lean`), then program + probe + proofs, and
its seam from `BinaryCC_to_FSAT`'s exit frame (blocked on top-down session 3
pinning that exit frame — coordinate).

## NEXT TOP-DOWN session — continue **session 3**: the `BinaryCC_to_FSAT` witness PROOFS

The program `buildFSAT` + `encodeIn` are **built and `#eval`-validated
end-to-end** (session 2). All remaining `sorryAx` on `CookLevin`/`Clique_complete`
is hardness-side. **Session 3 is pure proof work — no design risk** — filling the
`PolyTimeComputableLang BinaryCC_to_FSAT_instance` witness. Step 1
(`encodeIn_size_le`) and the first leaf of step 2 (`emitBitsFromScan_run`) are
**DONE** (session 3 part 1, this session) — see the in-file section
`## 2b.`/`### Run lemmas for the literal-tag emitters` in
`Reductions/BinaryCC_to_FSAT_free.lean` for the landed proofs, and the
**DESIGN COMPLETE — NEXT-SESSION PLAN** block at the bottom of that file for
the still-current full ordered spec. Remaining, in order:

2. **Run lemmas bottom-up (the crux, IN PROGRESS)** — the reusable stack from
   this session: `litFor`/`bitsPrefix`/`serF_encodeBitsAt`/
   `bitsPrefix_append`/`bitsPrefix_take_succ` (the serialization algebra) +
   `emit{Ftrue,FandTag,VarW,LitAt}_run`/`_frame` (OUT-only gadget lemmas) +
   `BSInv`/`BSInv_step` (the fold-invariant pattern) + `emitBitsFromScan_run`
   (done). **Copy this pattern** for the rest, in order:
   - **`emitBitsFromSent_run`** (next) — same shape as `emitBitsFromScan_run`
     but decodes the `encSList`-style sentinel stream (`ifBit DONE`/
     `ifBit EMARK` branches, `DONE`-flag idle case) instead of reading `SCAN`
     bare; template the branching/idle structure on `sentStep_step`/
     `sentLoop_run` (`FlatCC_to_BinaryCC_free.lean`) the same way this
     session's `BSInv_step` templated the non-branching arithmetic on
     `cardStep_step`. Conclusion needs an extra clause: `SCAN` ends up
     *past* the terminator (not merely equal to `bits.drop bound`).
   - **`emitCardsAt_run`** — an outer `nonEmpty`-guarded loop over a *copy* of
     `CARDS` (template: `cardStep`/`cardConvert_run`,
     `FlatTCC_to_FlatCC_free.lean`), each live iteration calling
     `emitBitsFromSent_run` twice (prem, conc). Algebraic target:
     `serF (encodeCardsAt C startA startB) = serF (listOr …)` — unroll via
     the same `forr`-tag-per-element + `falseFml`-close pattern as
     `bitsPrefix`/`serF_encodeBitsAt`, now over `List (CCCard Bool)` instead
     of `List Bool`.
   - **`emitAllSteps_run`** — nested loop (line × step), same `listAnd`
     unrolling one level higher; reuses `emitCardsAt_run` and the unary
     `LINEL`/`STEPO`/`STARTA`/`STARTB` index arithmetic (`concat`-chains —
     mechanical, `List.replicate_add`).
   - **`readOneFinal_run`**/**`emitFinal_run`** — `readOneFinal` is a
     sentinel-stream *parse* (mirror `emitBitsFromSent`'s decode half without
     re-emitting); `emitFinal` is another `listOr`-over-`listOr` unroll
     calling it + `emitBitsFromScan_run` (on the parsed `FBITS`).
   - **`computeWF_run`** — `GWF = if BinaryCC_wellformed C then [1] else []`;
     needs unary `leCheck`/`dvdCheck` ⇔ `≤`/`∣` lemmas (new: unary mod via
     truncated-subtraction loop) and `cardLenCheck` ⇔ `∀ card, |prem|=|conc|=
     width`. Independent of the emitter stack above — could be split into a
     parallel sub-session if the emitter chain is taking a while.
   - **`buildFSAT_run`** — assembles all of the above + `precompLen_run`
     (trivial); `computes = decodeOut_of_serF + buildFSAT_run`. The `hWf`
     guard is NECESSARY (`encodeTableau_correct` assumes it) — do not try to
     drop it.
3. **`cost_le`** — low-degree polynomial (nested-loop product; `cost_forBnd_le`
   accounting pass, cf. CliqueRel quartic→quintic, `binBudget_le_poly`); the
   var-index mul-loops are `Θ(index)` over `Θ(steps·L)` indices.
   `output_size_le` reuses `BinaryCC_to_FSAT_instance_size_bound`.
4. **`enc_bit`/`usesBelow`/`width_le`/`decode_agree`** — mechanical
   (`regBound := regFrame + 2·buildFSAT.loopDepth`; copy `flatCCBin_reductionLang`).
   Then `reducesPolyMO'_of_langFree … BinaryCC_to_FSAT_instance_correct` gives
   `BinaryCC ⪯p' FSAT`.
5. **The seam** `Reductions/BinaryCC_to_FSAT_comp.lean` (copy
   `FlatTCC_to_BinaryCC_comp.lean`): a near-pure scrub joining
   `flatTCC_to_binaryCC_witness`'s exit frame to `encodeIn` here (already pinned
   to it) → the whole sound tail `FlatTCC → … → FSAT` as ONE composed live `⪯p'`.

**Session-sizing note:** each remaining run lemma in step 2 is a few hundred
LOC of fold-invariant bookkeeping (see the two gotchas below) — budget one
lemma (or a tightly related pair, e.g. `readOneFinal_run`+`emitFinal_run`) per
session rather than trying to clear the whole stack in one sitting; commit
each lemma once it compiles green.

**After the witness lands**, the remaining top-down chain (unchanged):

1. **`FSAT_to_SAT` as a free witness + its seam** (smaller; CNF conversion).
   After it, the whole sound tail `FlatTCC → … → SAT` is ONE composable
   witness chain.
3. **S1 Cook 2D tableau** (`Simulators/CookTableau.lean`, 2 sorries, ~6–11K
   LOC) — the deepest unsoundness, the real front reduction.
4. **C8** — the universal-source decider (`hasDeciderClassical`), single-tape
   via free `DecidesLang`; subsumes S2 (collapse the phantom bridges there).
   Must ALSO produce the per-`Q` `SeamData` into the chain head (the settled,
   now-validated design). **UNGATED as of 2026-07-04-b** (Part 0.1 done);
   scoping probe queued as the next bottom-up session.

---

## Locked invariants — do NOT revisit

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

## Proven, reusable — do not re-derive

- **The FlatCC→BinaryCC free-reduction stack**
  (`Reductions/FlatCC_to_BinaryCC_free.lean`): `binConvert_run` (6-output run
  lemma with guard), the item view (`encItems`/`expandItems`/`itemsOkB` +
  `sitemsOf`/`citemsOf`/`fitemsOf` conversions), `sentLoop_run` (generic
  sentinel-stream transform loop), `initLoop_run` (bare-block loop),
  `mulLoop_run` (unary product), `remCheck_run` (truncated-subtraction
  compare + flag), `validB_iff` (Bool ↔ `isValidFlattening`),
  `encKeyB_injective`, `bitsNat_encodeString`/`cardsNat_encodeCards`/
  `finalNat_encodeFinal` (flat-level ↔ `Fin`-level correspondence),
  `encCardsOut_length_le`.
- **The live seam** (`Reductions/FlatTCC_to_BinaryCC_comp.lean`): `scrub` +
  `scrub_eval`/`scrub_cost`, `flatTCC_to_binaryCC_seam`, the composed witness
  + `flatTCC_to_binaryCC_reducesPolyMO'`.
- **The FSAT output codec** (`Reductions/BinaryCC_to_FSAT_free.lean`, 2026-07-05):
  `serF`/`deserF`/`decodeF` (prefix/Polish bit-serialization of the `formula`
  tree) + the PROVEN round-trip `decodeF_serF` + `decodeOut_of_serF` — the
  injectivity backbone of the target-#2 witness's `decodeOut`. This is the
  reusable pattern for any TREE-typed reduction output.
- **The `BinaryCC_to_FSAT` program** (`Reductions/BinaryCC_to_FSAT_free.lean`,
  session 2): `buildFSAT`/`encodeIn` + all emitters (`emitBitsFromScan`/
  `emitBitsFromSent`/`emitCardsAt`/`emitAllSteps`/`readOneFinal`/`emitFinal`) and
  the on-machine guard (`computeWF`/`leCheck`/unary-modulo `dvdCheck`/
  `cardLenCheck`) — pure `Cmd` DATA, `#eval`-validated end-to-end (`FSATSerProbe`
  §4). Do not re-derive; session 3 proves the run/cost lemmas over these.
- **The `BinaryCC_to_FSAT` size + first run lemma** (same file, session 3 part
  1, sorry-free & axiom-clean `[propext, Quot.sound]`): `encodeIn_size_le`
  (+ its helpers `encodable_size_bitsNat`/`_cardNat`/`_map_cardNat`/
  `_map_bitsNat`, `fresh_set_size`, `get_unset_of_ne`); the serialization
  algebra `litFor`/`encodeBitsAt_cons`/`bitsPrefix`/`serF_encodeBitsAt`/
  `bitsPrefix_append`/`bitsPrefix_take_succ` (reusable for EVERY remaining
  emitter — cards/steps/final all reduce to the same tag-then-child unrolling
  one level up); the OUT-only gadget lemmas `emit{Ftrue,FandTag,VarW,
  LitAt}_run`/`_frame`; and `emitBitsFromScan_run` (the fold-invariant
  template `BSInv`/`BSInv_step` — copy this shape, do not re-derive the
  `clear_value`/`heval` bookkeeping from scratch each time).
- **The flatTCC free-reduction stack** (`Reductions/FlatTCC_to_FlatCC_free.lean`):
  `blockMove_run`/`halfMove_run`, `cardStep_step`, `encSList` +
  `encSList_append_inj`, `encKey_injective`/`extractKey`,
  `flatTCC_to_flatCC_correct`.
- **The chain-composition engine** (`PolyTime.lean`): `SeamData`/`comp`,
  `State.get_append_replicate_nil`, `NPhard'`/`NPcomplete'` + bridges.
- **The kSAT3 free-reduction stack** (`NP/kSAT_to_SAT_free.lean`): `kCnf3Check`
  + run lemma + `kSAT3_precomposeData` + `encodeCnf_injective` +
  `encodeCnf_tally_tight` + the `kCheckBudget_le_poly` monomial-domination
  pattern.
- **The free engine** (`PolyTime.lean`): `InNPWitnessLangFree`/`inNPLangFree`
  + `inNPLangFree_to_inNP`, `FreePrecomposeData`/`precomposeFree`,
  `red_inNP_of_langFree`, `reducesPolyMO'_of_langFree`.
- **The verifier stacks** — `EvalCnfCmd.lean` (SAT) and `CliqueRelTM.lean`
  (FlatClique; `readNum_run`/`readNum_cost`/`ltBit_run`, `memberEdge_run`
  nested-loop template, length-only-invariant cost stack).
- **The compiler assembly** (`Compile/`): `run_physical_residue_gen`,
  `compileSeq_sound_physical_residue`(+`_traj`), `compileForBnd_…`,
  `compileIfBit_…`, `bitDecider_run`, `paddedBitDecider_run`,
  `paddedComputeTM`/`paddedCompute_run`; the op gadget stacks; the
  branch/loop/move toolkit; the threading toolkit. ⚠ `Compile_sound`/
  `Compile_run_physical`/`Compile_polyBound` are DEAD/superseded — do not
  attempt to prove.

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (lake **not** on
  PATH; LSP/most MCP can't find it). First build slow — kick off in background.
  Iterate one file directly: `env LEAN_PATH=$(lake env printenv LEAN_PATH)
  lean <file>` (fast, no lake). Commit per logical step, green.
  Headline: `Complexity.NP.SAT.CookLevin`.
- **Probe** a machine/program end-to-end (`#eval`) *before* proving its run
  lemma: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/X.lean`.
  Probe SEAMS end-to-end too (`FlatCCBinProbe.checkBridge` pattern: assert
  `AgreeBelow` register-by-register on concrete instances).
- **Axiom-check** via a scratch file: `#print axioms <name>` — only
  `propext`/`Classical.choice`/`Quot.sound` for new sorry-free results.
- **`omega` gotchas:** cannot see through `Var := Nat` variables
  (`simp only [Var] at *` first), `var`-typed rcases products, or
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
  _; rw […]` pattern, which generalizes to any chain length.
- **Multi-case register frames**: `interval_cases r` + per-case
  `repeat first | rw [State.get_set_eq] | rw [State.get_set_ne _ _ _ _ (by
  decide)]` walks any concrete nested-set state (the seam-bridge pattern).
- **`simp` with `List.take_succ` can hit max-recursion in a fat context** — use
  the explicit `rw [List.take_add_one, List.getElem?_eq_getElem hi]` chain.
- **`decide` fails when the goal type mentions free vars** — `show (0 : Nat) ≠ 2`
  first. `Cmd.UsesBelow` of a concrete program: full `simp [defs…]`.
- **`set` (tactic) lives only in `PolyTime.lean`, not `Frame.lean`** (core-only).
- Methodology: **skeleton-first; refine the highest-risk gap next; decompose
  `sorry`s, don't elaborate them; probe before committing engineering;
  `def`+`sorry` over `axiom` (count = 0); build green between commits.**
