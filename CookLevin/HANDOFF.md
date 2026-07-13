# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). This file is the forward-looking working plan; we
work **multi-session in two alternating streams** — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

## Where the proof stands (2026-07-12-c; **`FlatTCC ⪯p' FSAT` is LIVE**; the last tail step `FSAT → SAT` is MID-FLIGHT — map PROVEN correct, program written & probed GO, **run-lemma step 1(i) DONE (pure model PROVEN = tree map)**; machine folds (1(ii)), cost, fields, witness, seam remain)

- **In-NP side: DONE & axiom-clean.** `SAT_inNP.sat_NP`, `FlatClique_in_NP`,
  `KSat3Free.inNP_kSAT3_free`, `KSat3Free.kSAT3_reducesPolyMO'` are all
  `[propext, Classical.choice, Quot.sound]`.
- **The S3 migration is EXECUTING and the endgame design is VALIDATED LIVE.**
  Live honest `⪯p'` witnesses: `kSAT3_reducesPolyMO'`, `flatTCC_reducesPolyMO'`,
  `FlatCCBinFree.flatCC_reducesPolyMO'`,
  `BinaryCCFSATFree.binaryCC_reducesPolyMO' : BinaryCC ⪯p' FSAT` (the expensive
  Tseytin/tableau step, `binaryCCFSAT_reductionLang`), and — chained by TWO live
  `SeamData`/`comp` instances —
  `FlatTCCBinComp.flatTCC_to_binaryCC_reducesPolyMO' : FlatTCC ⪯p' BinaryCC`
  and **`BinaryCCFSATComp.flatTCC_to_FSAT_reducesPolyMO' : FlatTCC ⪯p' FSAT`
  (2026-07-12)** — the whole sound-tail prefix
  `FlatTCC → FlatCC → BinaryCC → FSAT` as ONE composed free witness
  (`flatTCC_to_FSAT_witness`). **The only missing tail piece is `FSAT → SAT`,
  now MID-FLIGHT (2026-07-12-b):** the machine-friendly map
  (`PreTseytin.preTseytin`) is PROVEN correct & axiom-clean
  (`FSATSATFree.fsatToSat_correct`), the full program `buildSAT` is written
  and `#eval`-validated end-to-end; the run/cost lemmas, the
  `PolyTimeComputableLang` witness, and the seam remain (~1–2 sessions);
  after them the tail is one chain `FlatTCC ⪯p' SAT` ready for the endpoint
  bridge.
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

- **2026-07-12-c (top-down) — `FSAT → SAT` run-lemma **step 1(i) DONE**: the
  pure scan model is now PROVEN = the tree map (was `#eval`-only), axiom-clean,
  1 commit.** Promoted the probe's model into the witness file
  (`Reductions/FSAT_to_SAT_free.lean`) and proved the equivalence the probe
  only `#eval`-checked: `subtreeTok_serF : subtreeTok (serF g ++ rest) =
  formula_size g` (Lemma A — arity-budget scan recovers the first-subtree token
  count, via the core budget invariant `budgetStep_iterate_subtree` +
  `budgetStep_iterate_freeze`), `scanClauses_serF` (Lemma B — scanning
  `serF f ++ rest` emits `ptseytin (b+k) f` then continues on `rest` with the
  token counter advanced by `formula_size f`), and the headline
  **`mScan_eq_fsatToSat : mScan (serF f) = fsatToSat f`**. This factors the
  tree recursion OFF the eventual machine ↔ model reduction — 1(ii) now only
  needs "the machine folds compute `mScan (serF f)`", no tree induction on the
  machine side. **Build-integrity fix (surfaced this session):**
  `FSAT_to_SAT_pre` + `FSAT_to_SAT_free` were landed 2026-07-12-b but never
  imported by a build root, so `lake build` never checked them — now wired into
  `Complexity.lean` (full build 3381 jobs green; headline axioms unchanged).
  ⚠ Gotcha: in `scanClauses_serF`, the `fand`/`forr` case's induction binders
  `a b` SHADOW the base `b : Nat` — name subformulas `f₁ f₂`. `Nat.add_comm`
  in a `rw` chain rewrites BOTH the iterate exponent and the goal RHS (commute
  the final `have` to match, or close with `omega` after `congr`).
- **2026-07-12-b (top-down) — `FSAT → SAT` design risk RESOLVED + map PROVEN +
  full program WRITTEN (compressed).** Probe-first (`probes/FSATPreProbe.lean`,
  green): **design (a) — positional-index Tseytin, no stack — GO**; FULL grammar
  (`tseytinOr` handles `forr`, no `eliminateOR`); fresh-var base
  `b := (serF f).length` (valid by `formula_maxVar_lt_serF_length`, kills the
  on-machine max). Landed axiom-clean: `NP/FSAT_to_SAT_pre.lean` (`ptseytin`,
  `preTseytin_correct` via `ptseytin_repr`, `preTseytin_kCNF3`/`_3SAT_correct`,
  `ptseytin_length_le`/`preTseytin_size_le` size fodder) and `buildSAT` +
  `fsatToSat`/`fsatToSat_correct` (`Reductions/FSAT_to_SAT_free.lean`).
  ⚠ omega BLIND at carrier `var` (fvar payloads) and treats `Nat.max` as opaque
  (`Nat.max_lt.mpr ⟨by omega, by omega⟩`).
- **2026-07-12 (top-down) — the `BinaryCC→FSAT` SEAM CLOSED:
  `flatTCC_to_FSAT_reducesPolyMO' : FlatTCC ⪯p' FSAT`, axiom-clean.**
  Second live `SeamData`/`comp` (`Reductions/BinaryCC_to_FSAT_comp.lean`),
  seam ON a composed witness, `mfc = scrub2`, probe-first
  (`probes/FSATSeamProbe.lean`). Artifacts + the wider-right-frame length
  argument catalogued in "Proven, reusable"; the `injection`-whnf-timeout
  gotcha in "Conventions".
- **2026-07-11 (top-down), session 5 — `BinaryCC ⪯p' FSAT` CLOSED** (cost
  pass at the `masterOmega` ceiling + mechanical fields + the witness).
  Everything reusable is catalogued in "Proven, reusable" (the cost toolkit
  block) and the omega/cost gotchas in "Conventions".
- **2026-07-05-b…2026-07-11 (top-down), sessions 2–5 (compressed):** the whole
  `BinaryCC ⪯p' FSAT` witness was built and closed — program + probes, the
  full `_run` stack, the guard (`computeWF`), `cost_le` at the master ceiling
  `Ω := 2000·(n+1)⁶`, and the mechanical fields. Every artifact + invariant
  template + gotcha is catalogued in "Proven, reusable" and "Conventions"
  below; the exit layout is the block above the next-session sections.
- **2026-07-04/05 (bottom-up), C8-0 SIGNED OFF + C8-1 + C8-2 DONE
  (compressed):** the C8 framework batch (`InNPWitnessLangFreeSplit`,
  `NPhard''`/`NPcomplete''`, Coq-faithful `FlatSingleTMGenNP`, per-witness
  `encBound`) and both TM gadgets (`AcceptHalt.demoteHalt`,
  `FormatCheck.formatCheckTM`, glue `composeFlatTM_stuck_M1`), all
  sorry-free & axiom-clean, probes green (`probes/C8SeamProbe.lean`,
  `probes/C8GadgetsProbe.lean`). Everything forward-looking lives in the C8
  section below (findings F1–F6, decomposition C8-0…C8-5, the C8-4 assembly
  notes) and in "Proven, reusable" (the C8-2 gadget layer). One endgame note
  kept: the live SAT verifier does NOT factor verbatim as a Split witness —
  `assgn` certs are `List Nat` (sentinel-unary), and `encodeState` has 8
  scratch `[]`s after the cert register; adaptation = trailing-`[]` trim +
  a bits→sentinel decode-prefix `Cmd` (endgame membership half only, NOT on
  the C8 critical path).

**Composite tail exit layout** (updated 2026-07-12; what the NEXT tail seam —
`FSAT_to_SAT`'s — re-encodes/scrubs): the composed `flatTCC_to_FSAT_witness`
exits with `buildFSAT`'s frame: **`FOUT` = reg 0 holds `serF (formula)`** (the
only output); regs 5/17–21 still hold `binaryCCFSAT`'s `encodeIn` values
(steps/offset/width/init/cards/final); everything else `< 57` is potentially
dirty (`OUT` = 22 holds a copy of the output; emitter/guard scratch 23–56);
regs `≥ 57` read `[]` (the composite's `regBound` is 57). So the
`FSAT_to_SAT` witness pins `encodeIn f = [serF f]` (done, 2026-07-12-b) and
its seam `mfc` is scrub-everything-except-reg-0. **The `FSAT_to_SAT` witness's
own exit layout** (what the ENDPOINT bridge sees): reg 0 = `serF f`
(preserved), reg 1 = `replicate |N| 1`, reg 2 = `encodeCnf N` (regs 1/2 = the
SAT verifier's `CLAUSE_TALLY`/`CNF_STREAM` layout, by design); scratch 3–26
dirty; frame 27.

## The free line — the working architecture (use this, and only this)

- **Verifiers**: free `DecidesLang` with bespoke bit-level `encodeIn`
  (numbers UNARY) → `DecidesLang.toDecidesBy`/`toInTimePoly` (live:
  `evalCnfDecidesLang`, `cliqueRelDecidesLang`).
- **NP witnesses**: `InNPWitnessLangFree`/`inNPLangFree` (+ `inNPLangFree_to_inNP`).
- **Reductions**: free `PolyTimeComputableLang` → `toFrameworkWitness'`/
  `reducesPolyMO'_of_langFree`; verifier precomposition via
  `DecidesLang.FreePrecomposeData`/`red_inNP_of_langFree`; **witness-witness
  composition via `SeamData`/`comp` — LIVE TWICE and chains on composed
  witnesses** (`FlatTCCBinComp.flatTCC_to_binaryCC_seam`, then
  `BinaryCCFSATComp.binaryCC_to_FSAT_seam` on top of it — the models for
  every next seam, incl. the wider-right-frame length argument).
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
  - `Reductions/BinaryCC_to_FSAT_comp.lean`: **the stacked-seam pattern** —
    seam on a COMPOSED left witness (unfold its `.c` with one `heval`, push
    the previous seam's bridge through with `Cmd.eval_agree`), the
    wider-right-frame close (registers above the left frame via
    `Cmd.eval_length_le` + `get_nil_of_len_le`), local `binConvert_key`
    extraction of the predecessor's exit key.
  - `Reductions/FSAT_to_SAT_free.lean` + `NP/FSAT_to_SAT_pre.lean`: **the
    tree-traversal pattern** — a TREE-typed *input* consumed by one forward
    token scan of its Polish serialization: positional fresh variables
    (`b + token index`, base `b := stream length`), right-child recovery by
    the arity-budget scan (`subtreeScan`), and a Lean-side positional
    equivalent (`ptseytin`) proven correct where recursion is free. **The pure
    scan model (`budgetStep`/`subtreeTok`/`scanClauses`/`mScan`) is PROVEN =
    the tree map** (`mScan_eq_fsatToSat`, via `subtreeTok_serF` +
    `scanClauses_serF`) — the template for "prove the machine folds compute a
    pure model, then close with the model≡tree equivalence" (factors the tree
    recursion off the machine proof). The core budget-scan invariant
    (`budgetStep_iterate_subtree`: processing `serF g`'s tokens pays off one
    budget obligation) + the freeze lemma are reusable for any prefix-parse
    counter.
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
  (endgame membership-half work only, not on the C8 critical path).
- **C8-2 — ✅ DONE (2026-07-05):** the accept-by-halting wrapper
  (`Lang/AcceptHalt.lean`) and the tape-format-check gadget
  (`Lang/FormatCheck.lean`), both run directions each, + the composition
  glue `composeFlatTM_stuck_M1`; all sorry-free & axiom-clean, probe
  `probes/C8GadgetsProbe.lean` green. Artifact list in "Proven, reusable"
  (the C8-2 gadget layer); assembly guidance in the **C8-4 assembly notes**
  below.
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

**Alternative:** pieces of the `FSAT_to_SAT` run-lemma ladder (top-down's next
item — see NEXT TOP-DOWN; step 1(i) is now DONE). Self-contained bottom-up bites
that unblock 1(ii): the `encodeCnf_append` prefix algebra (pure Lean,
`List.foldr` over `++`), or the `subtreeScan_run` / `drainSkipBody` /
`drainVarBody` `_run` lemmas (machine folds over the proven pure model — the
`subtreeScan_run` nested loop is the highest-risk piece, ideal to probe first).
Coordinate so nothing is done twice.

## NEXT TOP-DOWN session — finish the `FSAT_to_SAT` witness (run lemmas → cost → witness → seam)

The design phase + run-lemma **step 1(i) are DONE** (2026-07-12-b/-c). What
EXISTS, all green & axiom-clean: the map + correctness (`NP/FSAT_to_SAT_pre.lean`:
`preTseytin`, `ptseytin_repr`, `preTseytin_correct`, size lemmas); the full
program + layouts + chain-step correctness (`Reductions/FSAT_to_SAT_free.lean`:
`buildSAT`, `encodeIn f = [serF f]`, outputs `TALLY`(1)/`CNFOUT`(2), `decodeOut
= invFun encodeCnf`, `fsatToSat`, `fsatToSat_correct`); **and the pure scan
model now PROVEN = the tree map** (same file: `budgetStep`/`subtreeTok`/
`scanClauses`/`mScan` + `subtreeTok_serF`, `scanClauses_serF`,
`mScan_eq_fsatToSat`). The probe (`probes/FSATPreProbe.lean`) keeps an
independent `#eval` copy. Remaining ladder (~1–2 sessions):

1. **Run lemmas — step 1(ii): machine folds compute `mScan (serF f)`.** Target:
   `(buildSAT.eval [serF f]).get CNFOUT = encodeCnf (fsatToSat f)` (+ `TALLY =
   replicate |N| 1`, + frame). Step 1(i) removed the tree recursion, so ONLY
   linear fold invariants remain. **Prerequisite algebra (cheap, do first):**
   `encodeCnf_append : encodeCnf (M ++ N) = encodeCnf M ++ encodeCnf N` (it is
   `List.foldr` over `++` — one lemma; `encodeClause`/`encodeLit` are in
   `EvalCnfCmd.lean`), the incremental-emission backbone. Recommended order
   (probe each `#eval`-first, extend `FSATPreProbe`):
   - **(a) `subtreeScan_run` (the hard nut — do FIRST as a risk probe):**
     `(subtreeScan.eval s).get T = replicate (subtreeTok (s.get SCAN)) 1`, SCAN
     preserved, SC2/BUD/T/… scratch framed. The outer `budgetBody` loop folds
     the pure `budgetStep`; its inner `drainSkipBody` (skip one unary block past
     the `0`) is a black-boxed `RFInv`-style sentinel skip. Mirror
     `unaryMulLoop_run` register-genericity + the `CAInv` guard.
   - **(b) `tokenBody_run` (one iteration ≡ one `scanClauses` token):** dispatch
     on the tag; `fvar` uses `drainVarBody` (`RFInv` read into `VREG`), the two
     binary tags black-box `subtreeScan_run`, then emit via the gadget lemmas
     (`emitLit`→`encodeLit` append, `endClause`→`[0]`+tally). The clause list of
     each gadget = `encodeCnf` of that gadget (via `encodeCnf_append`).
   - **(c) the outer `forBnd IDX1 SERF tokenBody` invariant** (`CAInv`
     `nonEmpty`-guarded stream loop, black-boxing `tokenBody_run`): after the
     scan is consumed the loop idles (`tokens ≤ bits`), so relate the machine
     state to `scanClauses` having consumed all tokens.
   - **(d) phase 0 + assembly:** the `B := 1^|serF f|` length loop, the top
     clause emission, then `buildSAT_run` composed with `mScan_eq_fsatToSat`
     (`= encodeCnf (mScan (serF f)) = encodeCnf (fsatToSat f)`).
2. **`cost_le`** — the `masterOmega` pattern; generous ceiling: outer
   `|serF f| ≤ 4n` iterations × (budget scan `O(|serF|)` + emission
   `O(b+n)`) — a single `C·(n+1)³`-ish ceiling should dominate everything.
3. **Mechanical fields** — copy the `binaryCCFSAT_reductionLang` templates:
   `usesBelow` (`simp only` over all sub-defs + register defs; frame is 27),
   `enc_bit` (`serF` cells are `{0,1}` — small induction, or reuse the
   BinaryCC witness's output-bit lemma), `width_le` (`encodeIn` has length 1),
   `decode_agree` (`Cmd.eval_agree` at `CNFOUT`), `encBound := fun n => 4*n`
   (`serF_length_le_size`), `output_size_le` via `preTseytin_size_le` +
   `serF_length_le_size` (vars < `b + size f` with `b ≤ 4n`).
4. **The witness + chain step**: `fsatSAT_reductionLang :
   PolyTimeComputableLang fsatToSat`, then `reducesPolyMO'_of_langFree _
   fsatToSat_correct : FSAT ⪯p' SAT`.
5. **The seam**: `SeamData flatTCC_to_FSAT_witness fsatSAT_reductionLang` —
   `mfc` = scrub-everything-except-reg-0 below the left frame 57 (the
   `scrub2` pattern of `BinaryCC_to_FSAT_comp.lean`; reg 0 already holds
   `serF f` = exactly `encodeIn f`; note the RIGHT frame 27 is *narrower*
   than the left 57 this time — the previous seam's wider-right-frame length
   argument may be unnecessary, check `SeamData`'s exact obligation). Probe
   the seam first (`FSATSeamProbe.checkBridge57` pattern). Then the composed
   **`flatTCC_to_SAT_reducesPolyMO' : FlatTCC ⪯p' SAT` — the whole sound
   tail as ONE live chain.**

**Reusable machinery** (do not re-derive — in
`Reductions/BinaryCC_to_FSAT_free.lean` §4/§5 and `Lang/CostFlat.lean`): the
generic loop-free cost toolkit; the `serF`-length + `and/orPrefix` algebra; the
per-emitter `_cost`/`_effect` lemmas; the `masterOmega`/`buildFSATBound`
pattern (one master ceiling, `cost_bound` symbolic over `flatK`);
the mechanical-field recipes (`Cmd.eval_agree` for `decode_agree`,
`List.mem_or_eq_of_mem_set` chain for `BitState`, `simp`-closed `UsesBelow`);
and the two live seams (`FlatTCC_to_BinaryCC_comp.lean`,
`BinaryCC_to_FSAT_comp.lean`) for every seam obligation.

**After the sound tail is one chain**, the remaining top-down work:

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
- **The live seams**: (`Reductions/FlatTCC_to_BinaryCC_comp.lean`) `scrub` +
  `scrub_eval`/`scrub_cost`, `flatTCC_to_binaryCC_seam`, the composed witness
  + `flatTCC_to_binaryCC_reducesPolyMO'`; (`Reductions/BinaryCC_to_FSAT_comp.lean`,
  2026-07-12) `scrub2`, `binConvert_key` (the predecessor's exit key as one
  local lemma), `get_nil_of_len_le`, `binaryCC_to_FSAT_seam` (seam ON a
  composed witness + the wider-right-frame length close),
  `flatTCC_to_FSAT_witness` + `flatTCC_to_FSAT_reducesPolyMO'`.
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
  up); the **generic `listAnd`/`listOr` algebras `andPrefix`/`serF_listAnd`
  and `orPrefix`/`orPrefix_append`/`serF_listOr`** (one definition per
  connective serves every level — do NOT re-specialize per level;
  `serF_encodeFinalConstraint` is the `listOr` top closer); the OUT-only
  gadget lemmas `emit{Ftrue,FandTag,ForrTag,False,VarW,LitAt}_run`/`_frame`;
  the fold-invariant templates **`BSInv`** (plain, `emitBitsFromScan_run` —
  now carries a **frame clause**), **`SBInv`** (two-phase sentinel with
  past-the-terminator exit, `emitBitsFromSent_run`), **`RFInv`** (two-phase
  sentinel *parse*, `readOneFinal_run` — outputs `FBITS`/`BLEN`, `SCANF`
  past the terminator), **`CAInv`/`FFInv`** (`nonEmpty`-guarded stream loops
  with black-boxed inner `_run` facts, `emitCardsAt_run`/`emitFinal_run` —
  `FFInv`'s live iteration chains `readOneFinal_run` + `innerFinalSteps_run` +
  `emitFalse`), **`ASInv`/`ALInv`/`FSInv`** (exact-bound nested `listAnd`/
  `listOr` folds with a black-boxed inner-loop `_run`, `emitAllSteps_run`/
  `innerFinalSteps_run`); **`stepBody_run`/`finalStepBody_run`** (var-index
  arithmetic + on-machine bound guard ⇔ `encodeStepConstraint`/
  `encodeFinalAtStep`'s dite); and the register-generic unary loops
  **`unaryMulLoop_run`/`unarySubLoop_run`** (use these at every remaining
  mul/truncated-subtraction site — do not re-derive). **The wellformedness
  guard stack (2026-07-09):** `computeWF_run`, the three checks
  `leCheck_run`/`dvdCheck_run` (reusable pure-arithmetic `DvdArith.subMod`/
  `subMod_eq_mod` unary-`mod` + machine fold `dvdBody_step`)/`cardLenCheck_run`
  (`CLInv` guarded card stream + `cardLenItem_run`/`CEInv` per-item parse), the
  assembly helpers `andFlag_run`/`nonEmptyTFLG_run`, and the spec bridges
  `wf_iff`/`cardsOKB_iff` (`cardsOKB` = the decidable `Bool` card-length flag);
  `computeWF_run` now carries a **frame clause** (its 14-register write set).
  **The assembly layer (2026-07-10):** `precompLen_run` (LREG/LREG1 off INIT)
  and **`buildFSAT_run`** — `(buildFSAT.eval (encodeIn C)).get FOUT =
  serF (BinaryCC_to_FSAT_instance C)` — the correctness crux of the
  `BinaryCC ⪯p' FSAT` witness (`computes` = this + `decodeOut_of_serF`).
  **Factor any monolithic
  emitter into named defeq sub-`def`s (per loop level) BEFORE its run lemma**
  (as `emitFinal` → `finalStepBody`/`finalStepIterBody`/`finalStringBody`);
  the probe stays green (defeq). Copy these shapes; do not re-derive the
  `clear_value`/`heval` bookkeeping.
- **The cost toolkit (2026-07-10-b).** Generic (`Lang/CostFlat.lean`):
  `Cmd.cost_le_flat` (loop-free flat bound over `Cmd.costReads` ceilings +
  growth clause), `Cmd.writes`/`Cmd.eval_get_of_not_writes` (decide-able
  frame), `cost_mulLoop_le`/`cost_tailLoop_le`/`cost_constLoop_le`,
  `Cmd.cost_forBnd_flat_le`, `State.get_length_le_size`. In the witness file:
  the `serF`-length algebra (`serF_length_le_size`,
  `serF_length_le_of_mem_listAnd/Or`, `and/orPrefix_take_length_le`,
  `and/orPrefix_range_succ/_le`, `bitsPrefix/cardsPrefix_take_length_le`,
  `encSList/encCardsOut/encFinal_drop_length_le`, `encSList_length_ge`), the
  WREG transports (`bsBody_WREG`/`sentBitBody_WREG`/`emitBitsFromScan_WREG`/
  `emitBitsFromSent_WREG`/`emitCardsAt_WREG`), the arithmetic closers
  (`mulLoopClose`/`subLoopClose`/`one_le_P`/`le_scale`), and the FULL
  `_cost`/`_effect` stack for every emitter + guard (`emit*_cost`,
  `computeWF_cost`, `leCheck/dvdCheck/cardLen*_cost`, `precompLen_cost`) up to
  the assembly `buildFSAT_cost_le` at the master ceiling `masterOmega`/
  `buildFSATBound`. **The whole `BinaryCC→FSAT` witness `binaryCCFSAT_reductionLang`
  + `binaryCC_reducesPolyMO' : BinaryCC ⪯p' FSAT` is landed & axiom-clean** —
  the mechanical fields (`buildFSAT_usesBelow`/`encodeIn_bitState`/`decode_agree`
  via `Cmd.eval_agree`) are the copy-templates for the next witnesses. Do not
  re-derive.
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
  lean <file>` (fast, no lake) or `lake build <Module.Name>`. Commit per logical
  step, green. Headline: `Complexity.NP.SAT.CookLevin`.
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
- Methodology: **skeleton-first; refine the highest-risk gap next; decompose
  `sorry`s, don't elaborate them; probe before committing engineering;
  `def`+`sorry` over `axiom` (count = 0); build green between commits.**
