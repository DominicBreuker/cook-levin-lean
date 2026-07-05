# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). This file is the forward-looking working plan; we
work **multi-session in two alternating streams** — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

## Where the proof stands (2026-07-05-b; C8-2 done, BinaryCC→FSAT run lemmas ~80%)

- **In-NP side: DONE & axiom-clean.** `SAT_inNP.sat_NP`, `FlatClique_in_NP`,
  `KSat3Free.inNP_kSAT3_free`, `KSat3Free.kSAT3_reducesPolyMO'` are all
  `[propext, Classical.choice, Quot.sound]`.
- **The S3 migration is EXECUTING and the endgame design is VALIDATED LIVE.**
  Live honest `⪯p'` witnesses `kSAT3_reducesPolyMO'`, `flatTCC_reducesPolyMO'`,
  `FlatCCBinFree.flatCC_reducesPolyMO'`, and the **first COMPOSED live `⪯p'`**
  `FlatTCCBinComp.flatTCC_to_binaryCC_reducesPolyMO' : FlatTCC ⪯p' BinaryCC`
  (first live `SeamData`/`comp`). All axiom-clean. **Next chain step
  `BinaryCC ⪯p' FSAT`: the program is BUILT & `#eval`-validated (session 2);
  the witness-proof run-lemma stack (session 3) is ~80% done — size bound +
  seven run lemmas landed through `emitAllSteps_run` and `readOneFinal_run`;
  `emitFinal_run` (the last big emitter) is next, then `computeWF_run` +
  assembly.**
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

- **2026-07-05-b (top-down), session 3 parts 3–4:** two more run lemmas,
  sorry-free & axiom-clean (`[propext, Quot.sound]`), probe green, one commit
  each. **`emitAllSteps_run`** (the two-level `listAnd` fold): ONE generic
  `andPrefix`/`serF_listAnd` serves both levels (steps-in-line,
  lines-in-tableau) — prefer this generic-algebra shape for `emitFinal`'s
  `orPrefix`/`serF_listOr` too; invariants `ASInv` (inner, black-boxed
  `stepBody_run`, exact bound so NO idle case) and `ALInv` (outer, per-line
  `LINEL` via `unaryMulLoop_run`); bodies named `stepIterBody`/`lineBody`.
  **`readOneFinal_run`** (the sentinel-stream *parse*): `RFInv` = `SBInv`'s
  decode half — outputs `FBITS` (raw bits) + `BLEN` (unary length), `SCANF`
  past the terminator (chains per-string calls in `emitFinal`); body named
  `readFinBody`. New gotchas below: ambiguous `rw [List.range_succ]` with two
  ranges in the goal; `show`-spine unfolding times out even on flat bodies.
- **2026-07-05 (bottom-up), C8-2 DONE — both TM gadgets, sorry-free &
  axiom-clean, probe green (`probes/C8GadgetsProbe.lean`).**
  (a) **F4 closed** (`Lang/AcceptHalt.lean`): `AcceptHalt.demoteHalt M r`
  demotes the reject state WITHOUT bridging (contrast `joinTwoHalts`) and
  filters its outgoing transitions, so the machine parks at `r` by
  construction; transport pair `demoteHalt_run_accept`/`_run_reject` +
  `acceptsFlatTM`-level `demoteHalt_accepts`/`_not_accepts`.
  **`runFlatTM_first_halt`** recovers the no-early-halt trajectory from a
  bare `run ∧ halting` pair (`runFlatTM` freezes at the first halt), so the
  transports consume `paddedBitDecider_run`'s exact output shape — C8-4
  needs no new decider lemmas. (b) **F5 closed** (`Lang/FormatCheck.lean`):
  `formatCheckTM w` (states `w+7`, writes nothing, unique halt `w+6`)
  verifies the whole-tape grammar `3 ({1,2}* 0)^(w+1) 3⟨end⟩` and rewinds;
  forward `formatCheck_run`/`_traj` (exactly `2·|tape|+1` steps, tape
  unchanged, head 0, `composeFlatTM_run` input shape), backward
  `formatCheck_stuck` (bad cert region ⇒ never halts, any budget); grammar
  `certOKB`/`certOKB_iff` + `encodeTape_certSplit` (format-valid ⇔ cert
  `= shiftReg creg ++ [0,3]`, reassembling `encodeTape (sx ++ [creg])`).
  The separator COUNT is load-bearing: a cert containing `0`s would parse as
  extra registers exactly where the padded scratch must be empty.
  (c) **The C8-4 composition glue is pre-proven**: new public
  `composeFlatTM_stuck_M1` (`TMPrimitives.lean`) — guard stuck ⇒ composite
  never halts (the M₂-stuck case was already covered by
  `composeFlatTM_no_early_halt` with arbitrary `t₂`). Proof method worth
  copying for bespoke scan machines: the **`Seg` framework** (run +
  done-state-free trajectory in one predicate, composing additively) — for
  a single-halt-state machine it is simultaneously run lemma and
  no-early-halt trajectory.
- **2026-07-04 (bottom-up, part 2), C8-0 SIGNED OFF + C8-1 DONE (the
  framework batch), build green, axiom profiles unchanged.**
  (a) **F2 fixed**: `FlatSingleTMGenNP` now Coq-faithful
  (`list_ofFlatType M.sig` + `M.tapes = 1`); the vacuous S1 yes-branch
  builds its all-zeros tableau over `[]` (it only ever used `s.length`).
  (b) **F3 fixed**: `PolyTimeComputableLang` carries per-witness
  `encBound`/`_poly`/`_mono`; `padTimeBound`/`budget_ge`/
  `toFrameworkWitness'`/`comp` re-derived; the three live chain witnesses
  supply `fun n => 2n+1`. (c) **F1 landed**: `certState`,
  `InNPWitnessLangFreeSplit`, `inNPLangFreeSplit`, `NPhard''`/`NPcomplete''`
  + bridges (`PolyTime.lean` end); `NPhard'` marked superseded.
  (d) **C8-1d layout check**: the live SAT verifier does NOT factor
  verbatim — `assgn` certs are `List Nat` (true-var indices,
  sentinel-unary), not `List Bool`, and `encodeState` has 8 explicit
  scratch `[]`s AFTER the cert register. Adaptation is known-pattern work
  (trim trailing `[]`s — behavior-preserving, `State.get` of missing regs
  is `[]` — plus a bits→sentinel decode-prefix `Cmd`), needed only for the
  endgame `NPcomplete''` membership half, NOT on the C8 critical path.
- **2026-07-04 (bottom-up), C8 SCOPING PROBE DONE — verdict
  FEASIBLE-BUT-EXPENSIVE, gated on ONE owner decision.** Probe
  `probes/C8SeamProbe.lean` (green): a `Cmd` per-`Q` front program hits a
  pinned chain-head layout register-exactly (constant-machine emission,
  per-symbol re-encode, unary monomials via mul-loop, scrub; `enc_bit`
  clean) — **risk #2 seam-targeting: GO**. Paper findings F1–F6 + the build
  decomposition C8-0…C8-5 are recorded in the C8 section below. Headline
  finding **F1**: `NPhard'` over the current `inNP` can NEVER be honest —
  `inNP Q` is classically TRUE for every predicate (the cheating encoder),
  so the hypothesis must be strengthened to a free-line verifier witness
  (owner decision). Also found: `FlatSingleTMGenNP` has a port bug
  (`list_ofFlatType 1` vs Coq's `sig M`; machine-checked in the probe).
- **2026-07-04/05 (top-down), sessions 2 + 3 parts 1–2 (compressed):**
  `buildFSAT`/`encodeIn` BUILT & `#eval`-validated end-to-end
  (`probes/FSATSerProbe.lean` §4 — the TREE-output design risk is resolved);
  then `encodeIn_size_le` + the first five run lemmas
  (`emitBitsFromScan_run`/`emitBitsFromSent_run`/`emitCardsAt_run`/
  `stepBody_run` + gadget `_run`/`_frame` lemmas and the register-generic
  `unaryMulLoop_run`/`unarySubLoop_run`), all sorry-free & axiom-clean. The
  invariant templates and gotchas are catalogued in "Proven, reusable" and
  "Conventions" below.
- **2026-07-04-b (bottom-up), Part 0.1 DONE:** real `encodable.size`
  everywhere; the size-0 default fallback deleted (see "Where the proof
  stands").

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
2. **Seam discipline**: pin each new witness's input layout to its
   predecessor's exit frame and document the exit layout (dirty registers
   included) for the successor. C8's per-`Q`-witness seam-targeting is
   **probed GO** (2026-07-04, `probes/C8SeamProbe.lean`) against the pinned
   candidate chain-head layout `headEncodeIn` — freeze it with the S1
   witness design.
3. **Guard-or-no-guard is a per-step decision**: probe invalid→invalid ON
   PAPER before coding (counterexample method: pick a tiny invalid instance,
   check whether its image is accidentally wellformed+satisfiable).
4. **The front instance types are size-MEASURED, not string-encodable**
   (Part 0.1 finding): `GenNPInput.rel` / `mTMGenNPFixedInput.accepts` /
   `TMGenNPFixedInput.accepts` are abstract predicates, so their
   `encodable.size` counts only the data fields (tapes + the two numeric
   parameters). That is honest for `⪯p` size bounds, but **no TM can consume
   these types as inputs** — C8 retires the abstract front entirely (scoped
   2026-07-04: per-`Q` witnesses target corrected `FlatSingleTMGenNP`
   directly). Never add a size-0 instance to "fix" a missing-instance error;
   the fallback was deleted deliberately.
5. **The hypothesis side of hardness is dishonest-capable too (C8 finding
   F1).** `inTimePoly`/`inNP` are classically TRUE for every predicate (the
   cheating `DecidesBy.encode`), so any `∀ Q, inNP Q → …` hardness statement
   is unprovable-honestly by construction. Quantify hardness over free-line
   verifier witnesses (`NPhard''` over `InNPWitnessLangFreeSplit`, C8-0/C8-1)
   and never "fix" a hardness obligation by strengthening only the
   conclusion side.

---

## C8 — SCOPED (2026-07-04). Verdict: FEASIBLE-BUT-EXPENSIVE (~5–7 sessions,
## ~2–4K LOC), gated on owner decision C8-0

The scoping probe (`probes/C8SeamProbe.lean`, green) + paper analysis settled
the shape of the real universal-source front (replacing `hasDeciderClassical`,
subsuming S2). **The answers to the three scoping questions:**

- **No concrete type "replaces" `GenNPInput` — the abstract front dies.** In
  the honest endgame the per-`Q` witness maps `Q`-instances DIRECTLY to
  (corrected) `FlatSingleTMGenNP` instances (`flatTM × List Nat × Nat × Nat`);
  `GenNP`/`LMGenNP`/the mTM bridges/`GenNP_is_hard.lean` stay only in the
  legacy `⪯p` chain until the S3 swap, then get deleted (that IS the S2
  collapse).
- **The per-`Q` front witness** `W_Q : PolyTimeComputableLang (fQ)` with
  `fQ x = (M_Q, s_x, maxSize x, steps x)`: `M_Q` = the compiled+padded
  verifier of the *hypothesis's* free NP witness, wrapped accept-by-halting
  (a CONSTANT per `Q`, emitted verbatim by the `Cmd`); `s_x` = per-symbol
  re-encoding of `encX x`; `maxSize`/`steps` = unary values of concrete
  monomials `c·(n+1)^k` overshooting the hypothesis's abstract `inOPoly`
  bounds (constants extracted classically once per `Q`).
- **The seam** plugs into the FUTURE S1 free witness's input layout, which
  does not exist yet — the probe **pins a candidate** (`headEncodeIn`: reg 1
  machine as sentinel bit-stream, reg 2 `s`, regs 3/4 unary params) and
  validates a toy `W_Q` hits it register-exactly (`checkBridge` + `enc_bit`).
  **Risk #2 for C8: GO.** The S1 designer co-owns freezing this layout.

**Findings (F1–F6) — read before building:**

1. **F1 (BLOCKING, owner decision C8-0): `NPhard'` over the current `inNP`
   can never be honest.** `DecidesBy.encode` is a free function, so
   `inTimePoly P` holds *classically for every predicate* (encode
   `x ↦ [if P x then 1 else 0]` + a 2-state bit-test machine — why
   `hasDeciderClassical`'s docstring says "vacuously true"), hence `inNP Q`
   is TRUE for every `Q` (Cert `Unit`, `rel x _ := Q x`). So
   `NPhard' SAT = ∀ Q, inNP Q → Q ⪯p' SAT` quantifies over undecidable
   predicates; an honest witness would decide them — impossible — so any
   proof must route through the `ComputesBy.encode` cheat and the migrated
   headline stays vacuous. **Fix: strengthen the hypothesis** to a free-line
   verifier witness — `NPhard'' P := ∀ Y _ Q, inNPLangFreeSplit Q → Q ⪯p' P`
   where `InNPWitnessLangFreeSplit` = today's `InNPWitnessLangFree` with
   (a) **Cert := List Bool** (certificates are strings — textbook), (b) a
   **split pair layout** `verifier.encodeIn (x,c) = encX x ++ encC c` with
   pinned `encC` (the tape must factor as `s_x ++ cert`), (c) a size bound
   on `encX`. This is the standard verifier-based NP definition and changes
   the headline's meaning (hardness quantified over free-line-verified NP
   problems) — hence owner sign-off. Do NOT close `hasDeciderClassical` with
   the cheating encoder meanwhile: the sorry is the honest marker of the open
   hardness half (and as literally stated, with arbitrary `timeBound`, it is
   anyway false for `timeBound ≡ 0` on mixed predicates).
2. **F2: `FlatSingleTMGenNP` is port-buggy** (`SingleTMGenNP.lean`): it
   demands `list_ofFlatType 1 s` (= all-zero strings; machine-checked in the
   probe — no data-carrying instance exists) where Coq has
   `list_ofFlatType (sig M) s`, and it omits Coq's `tapes M = 1`. Fix to the
   Coq form; the vacuous S1 + bridges re-typecheck mechanically.
3. **F3: `PolyTimeComputableLang.encodeIn_size` hard-codes `≤ 2n+1`**, but
   `W_Q.encodeIn` must be the hypothesis's `encX` (the only honest access to
   an abstract `x`), whose bound is the hypothesis's polynomial. Generalize
   to a per-witness `encBound` field (precedent: `DecidesBy.encodeBound`,
   owner-decision 2026-06-07). Contained ripple: `padTimeBound` +
   `toFrameworkWitness'` arithmetic + `comp`.
4. **F4: acceptance is accept-by-HALTING** (`acceptsFlatTM` = reached a halt
   state within `steps`), but compiled deciders halt on accept AND reject.
   Wrapper: demote `rejectState` from the halt list — the machine sticks at
   reject (`validFlatTM` does not demand totality; stuck ⇒ not halting ⇒
   reject). Needs a run-transport lemma pair (accept-run preserved,
   reject-run never halts).
5. **F5: garbage certificates need an on-machine tape-FORMAT guard.** The
   instance's `∃ cert` ranges over raw strings; compiled-`Cmd` run lemmas
   only cover tapes `= encodeTape (encodeIn …)`. A TM-level format-check
   gadget (scan the cert region for the `{1,2}`-block/`0`-separator/endMark
   grammar, reject ⇒ stick) must prefix the wrapped verifier. With
   Cert = List Bool + pinned `encC`, format-valid ⇒ decodes — closing the
   backward correctness direction.
6. **F6: abstract `inOPoly` bounds → concrete monomials** for the
   `maxSize`/`steps` registers: extract `c`,`k`,`n0` classically once per
   `Q`, overshoot with `c·(n+1)^k + maxPrefix`, compute unary via the proven
   mul-loop shape (the probe exercises the quadratic case).

**Build decomposition (one per session; commit each green):**

- **C8-0 — ✅ SIGNED OFF (owner, 2026-07-04).**
- **C8-1 — ✅ DONE (2026-07-04, part 2):** `InNPWitnessLangFreeSplit` +
  `NPhard''`/`NPcomplete''` live at the end of `PolyTime.lean`;
  `FlatSingleTMGenNP` Coq-faithful; `encBound` generalization threaded.
  Layout-check finding: the live SAT verifier needs a trailing-`[]` trim +
  a bits→sentinel decode-prefix `Cmd` before it can be a Split witness
  (endgame membership-half work — see the latest-sessions entry).
- **C8-2 — ✅ DONE (2026-07-05):** the accept-by-halting wrapper
  (`Lang/AcceptHalt.lean`) and the tape-format-check gadget
  (`Lang/FormatCheck.lean`), both run directions each, + the composition
  glue `composeFlatTM_stuck_M1`; all sorry-free & axiom-clean, probe
  `probes/C8GadgetsProbe.lean` green. See the latest-sessions entry and the
  **C8-4 assembly notes** below.
- **C8-3 (Cmd pieces + run lemmas):** `emitConst` (fold of appends; run lemma
  by induction on the constant), the unary monomial evaluator (`c·(n+1)^k`
  via k-fold `unaryMulLoop_run`), the per-symbol re-encoder (`expandSent`
  shape).
- **C8-4 (W_Q assembly):** `fQ` + the correctness iff (forward:
  `paddedBitDecider_run` + wrapper transport within the `steps` budget;
  backward: accepted ⇒ format-valid ⇒ decodes ⇒ `rel` ⇒ `Q x` via
  `rel_correct.sound`) + the `PolyTimeComputableLang` fields.
- **C8-5 (the seam):** `SeamData W_Q W_head` against the frozen head layout —
  blocked on the S1 free witness existing; until then `C8SeamProbe.headEncodeIn`
  is the layout spec.

## NEXT BOTTOM-UP session — C8-3 (the `Cmd` pieces + run lemmas)

C8-0/C8-1/C8-2 are done, so next is **C8-3**: the `Cmd` building blocks of
the per-`Q` front program `W_Q` (shape validated by
`probes/C8SeamProbe.lean` — `buildFront` there is the toy blueprint):

1. **`emitConst dst bits`** (the constant-machine emitter): fold of
   `appendOne`/`appendZero` over a literal list (the probe's `emitBits`).
   Run lemma by induction on the constant; the frame is OUT-only (mirror the
   `emit*_run`/`_frame` OUT-only gadget lemmas in
   `Reductions/BinaryCC_to_FSAT_free.lean`).
2. **The unary monomial evaluator** for `c·(n+1)^k + d`: `k`-fold
   `unaryMulLoop_run` (register-generic, already proven in
   `BinaryCC_to_FSAT_free.lean` — do NOT re-derive) + constant append tail.
   This funds the `maxSize x`/`steps x` registers (F6).
3. **The per-symbol re-encoder** (`encX x`'s bit register → the instance's
   sentinel-expanded `s_x` register): the `expandSent`/`sentLoop_run` shape
   from `Reductions/FlatCC_to_BinaryCC_free.lean`; per-bit body = the
   probe's 3-append `forBnd` body.

Probe each piece with `#eval` before its run lemma (extend
`C8SeamProbe`/`C8GadgetsProbe`). These are ordinary `Cmd` fold-invariant
lemmas — copy `BSInv` (plain fold) from `BinaryCC_to_FSAT_free.lean`.

**C8-4 assembly notes (recorded 2026-07-05, C8-2 session — read before
building C8-4):**

- **The machine**: `M_Q := composeFlatTM (formatCheckTM xWidth)
  (AcceptHalt.demoteHalt (paddedBitDeciderTM c regBound) rejectState)
  (xWidth + 6)` where `rejectState = 2 + (Compile regBound c).states +
  (padRegsTM …).states` (accept is `1 + …`, from `paddedBitDecider_run`);
  `rejectState`'s halt bit is discharged by `paddedBitDeciderTM_halt_shift`
  at `i = 2`. Validity/tapes/sig lemmas for all three layers exist.
- **Forward (yes ⇒ accepted)**: `formatCheck_run`/`formatCheck_traj` on
  `encodeTape (encX x ++ certState c)` (via `encodeIn_eq`; the exit config
  `([], 0, tape)` IS the `initFlatConfig` shape M₂ needs) →
  `composeFlatTM_run` → `runFlatTM_first_halt` + `demoteHalt_run_accept`
  on `paddedBitDecider_run`'s bare output. Budget: `2·|tape|+1 + 1 +
  (padBudget + 1 + physStepBudget… + 3)` — the `steps x` monomial must
  overshoot it (F6).
- **Backward (accepted ⇒ yes)**: split the raw tape as `s_x ++ cert`
  (`s_x = 3 :: encodeRegs (encX x)`), then case on `certOKB cert`:
  - **bad**: `formatCheck_stuck` + `composeFlatTM_stuck_M1` ⇒ the composite
    never halts ⇒ `acceptsFlatTM = false`, contradiction. (Note
    `formatCheck_stuck`'s trajectory also gives `≠ exit` via
    `formatCheck_halting_iff` — the only halt state IS the exit.)
  - **good**: `certOKB_iff` + `encodeTape_certSplit` ⇒ tape
    `= encodeTape (encX x ++ [creg])`; convert the bit-register `creg` to
    `c : List Bool` (`certState c` is register-equal); if the verifier
    rejects, `demoteHalt_run_reject` makes M₂ never halt and
    `composeFlatTM_no_early_halt` (arbitrary `t₂`) kills the accept —
    so the verifier accepted ⇒ `rel x c` ⇒ `Q x` via `rel_correct.sound`.
- **Yes-instance cert**: `cert := shiftReg (c.map bit) ++ [0, 3]` — length
  `|c| + 2`, so the `maxSize x` monomial must overshoot `certBound + 2`;
  `list_ofFlatType 4 cert` is immediate (cells ≤ 3).

**Alternative (the right choice for a shorter session):** the
`FSAT_to_SAT` free witness (Tseytin as a `Cmd`; the last small sound-tail
item). Paper-probe the guard question first (formula inputs have no invalid
instances — expect the unguarded pattern of
`Reductions/FlatTCC_to_FlatCC_free.lean`), then program + probe + proofs, and
its seam from `BinaryCC_to_FSAT`'s exit frame (blocked on top-down session 3
pinning that exit frame — coordinate).

## NEXT TOP-DOWN session — continue **session 3**: the `BinaryCC_to_FSAT` witness PROOFS

The program `buildFSAT` + `encodeIn` are **built and `#eval`-validated
end-to-end** (session 2), and the run-lemma stack is **~80% done**: step 1
(`encodeIn_size_le`) plus `emitBitsFromScan_run`, `emitBitsFromSent_run`,
`emitCardsAt_run`, `stepBody_run`, `emitAllSteps_run`, `readOneFinal_run`
(and the register-generic `unaryMulLoop_run`/`unarySubLoop_run`) are all
landed, sorry-free & axiom-clean. See the **DESIGN COMPLETE — NEXT-SESSION
PLAN** block at the bottom of `Reductions/BinaryCC_to_FSAT_free.lean` (kept
current, with a detailed `emitFinal_run` battle plan). **Session 3 is pure
proof work — no design risk.** Remaining, in order (budget ~one lemma per
session; commit each green):

2. **Run lemmas bottom-up (the crux, IN PROGRESS).** Copy the landed
   patterns — `BSInv` (plain fold), `SBInv` (two-phase sentinel re-emit),
   `RFInv` (two-phase sentinel *parse*), `CAInv` (single-phase
   `nonEmpty`-guarded loop over a stream copy, inner emitters as black-boxed
   `_run` facts), `ASInv`/`ALInv` (exact-bound nested `listAnd` folds),
   `stepBody_run` (straight-line chain + guard branch):
   - **`emitFinal_run`** (NEXT — the last big emitter): the
     `listOr`-over-`listOr` unroll. Mirror `andPrefix`/`serF_listAnd` with a
     generic `orPrefix` (`[1,0]`-tag) + `serF_listOr` (falseFml-close);
     outer = `CAInv`-style guarded loop over the `SCANF` stream, one
     black-boxed `readOneFinal_run` per live iteration (its
     past-the-terminator `SCANF` clause chains the calls); inner =
     exact-bound `LREG1` loop with `stepBody_run`'s arithmetic shape
     (`STEPO` mul, `SUMW = STEPO ++ BLEN`, `REM` sub, guard ⇔
     `encodeFinalAtStep`'s dite) + `emitBitsFromScan_run` on
     `SCAN := FBITS` at `FSTART = STEPSL ++ STEPO`; guard-fail emits
     `falseFml`, NOT `ftrue`. Full plan in the file's bottom block.
   - **`computeWF_run`** — `GWF = if BinaryCC_wellformed C then [1] else []`;
     needs unary `leCheck`/`dvdCheck` ⇔ `≤`/`∣` lemmas (unary mod via
     `unarySubLoop_run`-style repeated subtraction) and `cardLenCheck` ⇔
     `∀ card, |prem|=|conc|=width`. Independent of the emitter stack —
     can run as a parallel sub-session.
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
4. **C8** — the per-`Q` universal-source front; subsumes S2. **SCOPED
   2026-07-04: FEASIBLE-BUT-EXPENSIVE**, decomposition C8-0…C8-5 above
   (bottom-up stream). Coordinate here: the S1 witness design must freeze
   the chain-head input layout the C8 seam targets
   (`probes/C8SeamProbe.lean` `headEncodeIn` is the candidate spec).

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

- **The C8-2 gadget layer (2026-07-05)**: `AcceptHalt.demoteHalt` +
  structure/step/halting lemmas, `demoteHalt_run_eq`/`_weak`, the transport
  pair `demoteHalt_run_accept`/`_run_reject`, `acceptsFlatTM`-level
  `demoteHalt_accepts`/`_not_accepts`, and `runFlatTM_first_halt`
  (trajectory recovery from bare `run ∧ halting` — reusable wherever a
  consumer lacks a no-early-halt conjunct). `FormatCheck.formatCheckTM` +
  `formatCheck_run`/`_traj`/`_stuck`, `certOKB`/`certOKB_iff`/
  `encodeTape_certSplit`, and the **`Seg` framework** (exact run +
  done-state-free trajectory, additive composition — the template for any
  bespoke single-halt-state scan machine). `composeFlatTM_stuck_M1`
  (TMPrimitives): guard-stuck ⇒ composite-never-halts.
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
- **The `BinaryCC_to_FSAT` run-lemma stack** (same file, session 3 parts 1–2,
  all sorry-free & axiom-clean `[propext, Quot.sound]`): `encodeIn_size_le`
  (+ helpers `encodable_size_bitsNat`/`_cardNat`/`_map_*`, `fresh_set_size`,
  `get_unset_of_ne`); the serialization algebra `litFor`/`bitsPrefix`/
  `serF_encodeBitsAt`/`bitsPrefix_append`/`bitsPrefix_take_succ` and its
  card-level lift `cardsPrefix`/`cardsPrefix_append`/`serF_encodeCardsAt`
  (steps/lines/final reduce to the same tag-then-child unrolling one level
  up); the **generic `listAnd` algebra `andPrefix`/`andPrefix_append`/
  `serF_listAnd`** (one definition serves every `listAnd` level — mirror it
  for `listOr` as `orPrefix`/`serF_listOr`, do NOT re-specialize per level);
  the OUT-only gadget lemmas `emit{Ftrue,FandTag,ForrTag,False,VarW,
  LitAt}_run`/`_frame`; the fold-invariant templates **`BSInv`** (plain,
  `emitBitsFromScan_run`), **`SBInv`** (two-phase sentinel with
  past-the-terminator exit, `emitBitsFromSent_run`), **`RFInv`** (two-phase
  sentinel *parse*, `readOneFinal_run` — outputs `FBITS`/`BLEN`, `SCANF`
  past the terminator), **`CAInv`** (`nonEmpty`-guarded stream loop with
  black-boxed inner `_run` facts, `emitCardsAt_run`), **`ASInv`/`ALInv`**
  (exact-bound nested folds with a black-boxed inner-loop `_run`,
  `emitAllSteps_run`); **`stepBody_run`** (var-index arithmetic + on-machine
  bound guard ⇔ `encodeStepConstraint`'s dite); and the register-generic
  unary loops **`unaryMulLoop_run`/`unarySubLoop_run`** (use these at every
  remaining mul/truncated-subtraction site — do not re-derive). Copy these
  shapes; do not re-derive the `clear_value`/`heval` bookkeeping.
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
