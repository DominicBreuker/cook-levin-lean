# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). This file is the forward-looking working plan; we
work **multi-session in two alternating streams** — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

## Where the proof stands (2026-07-18-b; **THE SOUND TAIL IS COMPLETE** (`FSATSATComp.flatTCC_to_SAT_reducesPolyMO'`, axiom-clean), **S1 DIRECTION (1a) + `halt_of_satFinal` ARE PROVEN** (machine step/halt ⟹ card-covered row transition, its gates, AND the backward final-pattern bridge on the new cell-code disjointness algebra — 6 of the 10 skeleton sorries closed, all axiom-clean), **THE CHAIN-HEAD LAYOUT IS FROZEN** (`Reductions/HeadLayout.lean`, the S1↔C8-5 interface), and **C8-3 IS DONE** (`Reductions/FrontPieces.lean`: `emitConst`/`reencLoop`/`unaryMonomial` + run/frame/cost lemmas, axiom-clean, probe green) — next: **S1 direction (2) assembly + direction (1b)** top-down and **C8-4 (the `W_Q` assembly)** bottom-up)

- **In-NP side: DONE & axiom-clean.** `SAT_inNP.sat_NP`, `FlatClique_in_NP`,
  `KSat3Free.inNP_kSAT3_free`, `KSat3Free.kSAT3_reducesPolyMO'` are all
  `[propext, Classical.choice, Quot.sound]`.
- **The S3 migration's TAIL is DONE.** Live honest `⪯p'` witnesses:
  `kSAT3_reducesPolyMO'`, `flatTCC_reducesPolyMO'`,
  `FlatCCBinFree.flatCC_reducesPolyMO'`,
  `BinaryCCFSATFree.binaryCC_reducesPolyMO' : BinaryCC ⪯p' FSAT`,
  `FSATSATFree.fsatSAT_reducesPolyMO' : FSAT ⪯p' SAT` (2026-07-16), and —
  chained by THREE live `SeamData`/`comp` instances
  (`FlatTCC_to_BinaryCC_comp` → `BinaryCC_to_FSAT_comp` →
  `FSAT_to_SAT_comp`) — **the whole sound tail
  `FlatTCC → FlatCC → BinaryCC → FSAT → SAT` as ONE composed free witness**
  (`FSATSATComp.flatTCC_to_SAT_witness`), giving
  **`flatTCC_to_SAT_reducesPolyMO' : FlatTCC ⪯p' SAT`**. The tail is ready
  for the endpoint hardness bridge and BLOCKED ONLY on the front
  (S1 + C8 must deliver an honest `… ⪯p' FlatTCC` prefix).
- **Headline `CookLevin` still depends on `sorryAx` — wholly hardness-side.**
  `sorry`s in built code: `red_inNP`'s `inTimePoly` half (`NP.lean`),
  `hasDeciderClassical` (`GenNP_is_hard.lean`), 4× `CookTableau` (the S1
  skeleton: `step_of_validStep` (1b), `cover_of_run`/`run_of_cover`,
  `cookTableau_size_bound` — each with a proof-plan docstring), 3×
  `MultiToSingle` (dead code). Plus the `sorry`-free **vacuous** defs
  (S1-stub/S2) invisible to `#print axioms` — Group S.
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

- **2026-07-18-b (bottom-up) — C8-3 DONE + `halt_of_satFinal` PROVEN (the
  self-contained bite), all axiom-clean, build green (3388).**
  (1) **`Reductions/FrontPieces.lean`** — the three `W_Q` building blocks,
  register-generic (`unaryMulLoop_run` style — C8-4 owns the register map),
  probed first (`probes/C8FrontProbe.lean`, 19 checks green incl. the
  `C8SeamProbe` toy front REBUILT from the real pieces hitting the frozen
  `headEncodeIn` register-exactly): `appendConst`/`emitConst` (exact
  emission + `dst`-only frame + exact cost; the seed-`Cmd` parameter glues
  constant tails without a `nop`), `appendItem` (the `encSyms` sentinel item),
  `reencBody`/`reencLoop` (drains a bit register, appends
  `encSyms (bits.map (· + off))` — `off` is a per-`Q` constant: `off = 1` is
  the `shiftReg` cell shift the real `s_x = 3 :: encodeRegs (encX x)` needs,
  `off = 0` the raw toy stream; the shift decision is surfaced to C8-4, not
  hard-coded), `mulStep`/`powLoop`/`unaryMonomial` (`dst := 1^(c·(n+1)^k+d)`,
  `src` survives; cost ≤ `monomialCost` with the exact-shape recursive
  `powCost` + closed form `powCost_le`, degree-`k` monomial). Also
  `HeadLayout.encSyms_snoc` (additive; both seam probes re-run green).
  (2) **`halt_of_satFinal` PROVEN** via the new **cell-code disjointness
  algebra** (`CookTableau.lean`: `hCell_val_lb`/`_ub`, `tCell_ne_hCell`,
  `hCell_ne_bCell`, `tCell_ne_bCell`, `hCell_inj`, `tCell_inj` — the three
  disjoint code bands; these pay again in stage (i) of the (1b) inversion):
  a final pattern is a singleton halting head cell, the bands force its
  `confRow` occurrence to be the head coordinate, `hCell_inj` + `state_lt`
  identify the state. ⚠ gotchas: `omega` cannot link `(hCell …).1` to its
  formula after `unfold` — use defeq ASCRIPTIONS (`have h : sig+1 ≤ (sig+1)*
  (q.1+1)+b.1 := hCell_val_lb …`); `++` is LEFT-assoc, so an `isSubstring`
  split needs `List.append_assoc` before `List.getElem?_append_right`; index
  a row via `getElem?` (non-dependent, `rw`-safe), not `getElem`.
- **2026-07-18 (top-down) — S1 DIRECTION (1a) PROVEN + THE CHAIN-HEAD LAYOUT
  FROZEN.** All of step-2's plan landed, axiom-clean, build green (3387):
  (1) **`stepFlatTM_normM`** (normalisation agreement) via the combined
  dedup+filter `find?` characterisation (`dedupGo_filter_find?` with the
  seen-keys invariant; `dedupGo_no_match` covers the filtered-out-first-match
  case — dedup guarantees no shadow matcher remains). (2) **`ConfFits_step`**
  on two shared helpers the rest of S1 keeps consuming: **`step_desc`**
  (a successful step unfolded: fired entry + single-tape payload `w`/`mv` +
  the successor's explicit shape) and **`write_facts`** (the packaged write
  effect: length growth ≤ 1, alphabet preserved, away-from-head cells
  unchanged, head cell `= wEff` at the `decide (len < hd)` frontier flag —
  the in-range case rides `List.set`). (3) the **window machinery**:
  coordinate cells `rowCell`/`rowX`, `confRow_window` (a 3-window = its
  three cells via `take3_drop`/`coversHead_take3`), the frontier ⟺
  blank-left-neighbour lemmas (`tapeSymAt_blank_iff`/`rowX_isBlank`),
  membership lemmas for EVERY card family, and the generic `copy_window`.
  (4) **`validStep_of_halt`** and **`validStep_of_step`** — the latter by
  the full 17-branch case analysis (3 moves × {center, left-of, right-of,
  incoming, copy} incl. the `Lmove` clamp/interior split). (5)
  **`satFinal_of_halt`**. (6) **the layout freeze**:
  `Reductions/HeadLayout.lean` promotes `C8SeamProbe.headEncodeIn` to built
  code (imported by `Complexity.lean`; the probe now consumes the frozen
  defs so it cannot drift) + `headEncodeIn_bitState` (the future S1
  witness's `enc_bit` field) — **C8-5's seam target is now fixed; C8-3/C8-4
  can build against it.** ⚠ tactic notes: the per-window subgoal recipe is
  4-phase — rw row cells (+`hBst`/`hBright`/`hBhd` projections), simp-show
  index normalisation, bridge rewrites (`hR`/`hwrhd`/`hunch`/`← hxb*` — the
  `←` direction turns the row's `decide` frontier form back into the card's
  `xIsBlank` form so the final `rfl` closes against the unreduced card
  application), `rfl`. `x + k - 1` is DEFEQ to `x + (k-1)` (no norm needed
  for `rfl`), but `hd - 1 + 1` is not `hd` — those need `show … from by
  omega` sims before pattern-matching rewrites. Pass `(j := …)` explicitly
  to every rowCell rewrite (metavariable indices break the `by omega`
  side-goals). Structure-instance `{ prem := …, conc := … }` continuation
  lines mis-parse in `refine` — use nested `⟨⟨⟨…⟩, ⟨…⟩⟩, …⟩`.
- **2026-07-17-b (top-down) — S1 RISK REVIEW + v2 REDESIGN: `cookTableau_correct`
  was FALSE as stated; the tape semantics are FIXED, the full card algebra is
  landed, the bijection is DECOMPOSED, and agreement is PROBED GREEN.** Four
  independent v1 defects were found *before* any bijection work was spent on
  them: (1) **BLOCKING — non-local jump-writes.** `writeCurrentTapeSymbol`
  zero-padded writes beyond the tape frontier, so ONE machine step rewrote
  `head − len` cells at arbitrary distance from the head — inexpressible by
  ANY local 3-window card family (counterexample: wander ≥ 3 cells past the
  frontier reading `none`, write once, walk back, branch on `some 0`-vs-blank;
  the probe's `M2` accept/reject flips under the two semantics). **FIXED in
  `MachineSemantics.lean`**: the tape is append-only at the frontier —
  beyond-frontier writes are VOID; all in-range/frontier behaviour unchanged;
  total fallout was 2 files (`TapeMono`, `ShiftTape.insertCarryTM_step_blank`
  restated at the frontier — every call site already was there). This is also
  closer to Coq's `midtape/rightof` tape, which cannot wander at all.
  (2) v1 had only head-at-CENTER transition cards — *soundness* fails for any
  machine that moves (the head-adjacent windows had no matching card). v2 has
  the closed algebra: 3 window positions per entry + `Rmove`/`Lmove`
  incoming-head families + halt freeze ×3 positions + boundary variants. The
  completeness linchpin is the deliberate ABSENCE of an all-tape-premise
  head-at-second-slot family — spurious heads cannot materialise (a head can
  only arrive from an adjacent cell, which such a window would contain).
  (3) `moveTapeHead` clamps `Lmove` at tape position 0, but cards are
  position-blind — v2 rows carry a leading BOUNDARY MARKER (`bCell`, top
  code) and the clamp cards key on it. (4) v1's `none`-write card wrote the
  blank; v2's `wEff` keeps the read symbol and implements the
  frontier-sensitive void write (blank-left-neighbour ⟺ strictly beyond the
  frontier, under the run invariant "in-range symbols < sig"). Two further
  prerequisites: `validFlatTM` forces neither transition-KEY-UNIQUENESS
  (`stepFlatTM` = `find?`, shadowed duplicates would break completeness) nor
  well-shaped `dst` lists — cards are generated from **`normTrans`**
  (first-per-key dedup, shape filter, halting-src drop; step-invisible on
  the run: `stepFlatTM_normM`). The restated `cookTableau_correct` carries
  the previously-MISSING `validFlatTM`/`tapes = 1`/`list_ofFlatType`
  hypotheses (v1 was false without them; they are exactly the witness's
  future guard). Landed: the 10-sorry decomposition skeleton (each with a
  proof-plan docstring), PROVEN assembly glue + wellformedness + the ported
  `immediateHalt` constrained case (axiom-clean), the restated degree-10
  size bound, and `probes/S1TableauProbe.lean` GREEN (every M1/M2 run step
  card-covered incl. the frontier-append and void-write paths; halt rows
  freeze; skip-a-row and live-head stalling correctly NOT covered; final
  patterns exact).
- **2026-07-17 (bottom-up) — build health DONE: the two giant witness files
  SPLIT; full clean rebuild 4m45s → 4m05s wall (4-core session container).**
  `BinaryCC_to_FSAT_free.lean` and `FSAT_to_SAT_free.lean` are each three
  modules now — `*_defs` (codec/program/model defs), `*_run` (the run-lemma
  ladders), and the ORIGINAL module name (cost + witness + headline `⪯p'`,
  so every downstream import is unchanged). `FSAT_to_SAT_free_defs` imports
  ONLY `BinaryCC_to_FSAT_free_defs` (the `serF` codec + layout +
  `serF_length_le_size`), so the two witness chains build IN PARALLEL
  (run 19s∥23s, cost 36s∥32s). Content moved verbatim, nothing re-proven;
  33 BinaryCC run-region loop invariants lost `private` (the cost module
  consumes them across the new boundary); axiom profiles unchanged, build
  green (3386). ⚠ FINDING (corrects the old build-health note): `_run` →
  cost is inherently SERIAL — the cost ladders consume the run lemmas
  (`buildSAT_cost_le` walks `buildSAT_run`'s state chain), so run∥cost
  parallelism is impossible; the wall-clock win is the `_defs` extraction.
- **2026-07-16 (top-down) — `FSAT → SAT` FINISHED: cost assembly + witness +
  seam; THE SOUND TAIL IS ONE LIVE CHAIN.** 5 commits, all axiom-clean, full
  build green (3382). Landed: (1) **`tokenBody_cost`** (`≤ tokFK·(E+N+3)³`) —
  the 2026-07-15-b perf blocker is RESOLVED by exactly the prescribed fixes
  (five per-branch `private` lemmas, loop frame facts precomputed as
  `private` one-liners so each write-set `by decide` runs once, `clear_value`
  after every `set`): the whole block elaborates in ~9s (was >14 min).
  (2) **`outerLoop_cost`** — `Cmd.cost_forBnd_le` over `outerLoop_run`'s
  semantic invariant + a `|SCAN| ≤ L` clause preserved MODEL-side
  (`tokRem_length_le`, 5-case, no machine walk); the split equation pins the
  emit buffer to `|C0| + |encodeCnf (fsatToSat f)| ≤ E`. (3)
  **`buildSAT_cost_le`** at `satBound n := satK·(satOmega n + 1)⁴ = O(n⁸)`
  (`satOmega = 1700(n+1)²`, symbolic `satK := tokFK + 12·emitLit.flatK + 100`
  — flatK numerals never evaluated) + `satBound_poly/_mono/_output`; prefix
  ops exact via `buildSAT_run`'s state chain, top-clause emitters via
  `Cmd.cost_le_flat` at exact entry lengths (`emitLit_run`). (4) the witness
  **`fsatSAT_reductionLang`** + **`fsatSAT_reducesPolyMO' : FSAT ⪯p' SAT`**.
  (5) the THIRD live seam (`Reductions/FSAT_to_SAT_comp.lean`, probe-first:
  `probes/SATSeamProbe.lean` green incl. the real 1756-bit tableau path) —
  `scrub3` clears regs 1–26 ONLY: the right frame (27) is NARROWER than the
  left (57), so the left residue above 27 is outside the bridge's scope (no
  wider-frame length argument needed). Yields
  **`flatTCC_to_SAT_reducesPolyMO' : FlatTCC ⪯p' SAT`**. ⚠ new gotchas in
  "Conventions" (the `rw … at *` self-rewrite footgun; `omega` needs `27 ≤ X`
  not `1 ≤ X` for cubic-slack goals; probe `#eval` of `buildSAT` on >1K-bit
  streams is out of budget — check bridges, not end-to-end, on big instances).
- **2026-07-12-b…2026-07-15-b (top-down), the `FSAT → SAT` build-out
  (compressed):** design probe GO (positional Tseytin over the Polish `serF`
  stream, no stack; `probes/FSATPreProbe.lean`); map `preTseytin` +
  `fsatToSat_correct` proven (`NP/FSAT_to_SAT_pre.lean`); program `buildSAT`
  written + `#eval`-validated; the pure scan model PROVEN = the tree map
  (`mScan_eq_fsatToSat` via `subtreeTok_serF`/`scanClauses_serF`); the whole
  run ladder (`budgetBody_*` leaves → `subtreeScan_run` (Dyck-forest `∃ gs`
  invariant) → `tokenBody_run` → `outerLoop_run` → **`buildSAT_run`**); the 6
  mechanical fields; the leaf loop-cost lemmas + all effect lemmas + the
  gadget-bound helper `gad_le`/`tokFK`. Everything reusable is catalogued in
  "Proven, reusable"; the hard-won tactic gotchas in "Conventions".
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

**Final tail exit layout** (updated 2026-07-16; what the ENDPOINT bridge
sees from the full composed `flatTCC_to_SAT_witness`, `regBound = 57`):
**reg 1 = `replicate |N| 1`, reg 2 = `encodeCnf N`** — the SAT verifier's
`CLAUSE_TALLY`/`CNF_STREAM` layout, by design (`decodeOut = invFun encodeCnf`
on reg 2); reg 0 = `serF f` (the intermediate formula, preserved);
`buildSAT` scratch 3–26 dirty; regs 27–56 hold the LEFT composite's residue
(the last seam's `scrub3` deliberately does not touch them — outside the
right frame 27); regs `≥ 57` read `[]`. The endgame membership half will
adapt the live SAT verifier to consume regs 1/2 (see the C8 endgame note
above).

## The free line — the working architecture (use this, and only this)

- **Verifiers**: free `DecidesLang` with bespoke bit-level `encodeIn`
  (numbers UNARY) → `DecidesLang.toDecidesBy`/`toInTimePoly` (live:
  `evalCnfDecidesLang`, `cliqueRelDecidesLang`).
- **NP witnesses**: `InNPWitnessLangFree`/`inNPLangFree` (+ `inNPLangFree_to_inNP`).
- **Reductions**: free `PolyTimeComputableLang` → `toFrameworkWitness'`/
  `reducesPolyMO'_of_langFree`; verifier precomposition via
  `DecidesLang.FreePrecomposeData`/`red_inNP_of_langFree`; **witness-witness
  composition via `SeamData`/`comp` — LIVE THRICE, stacking on composed
  witnesses** (`FlatTCCBinComp.flatTCC_to_binaryCC_seam` →
  `BinaryCCFSATComp.binaryCC_to_FSAT_seam` → `FSATSATComp.fsat_to_SAT_seam`
  — the models for every next seam, incl. both frame-mismatch variants:
  wider right frame = length argument; narrower right frame = no scrub
  above it).
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
  - `Reductions/FSAT_to_SAT_comp.lean`: **the narrow-right-frame seam** —
    when the right witness's frame is NARROWER than the left composite's,
    the bridge only quantifies below the right frame, so `mfc` scrubs only
    registers inside it and the left residue above needs NO handling; the
    right `encodeIn`'s missing registers read `[]` and close by `rfl`.
    Probe: `probes/SATSeamProbe.lean` (decode the machine's own intermediate
    stream with `decodeF` instead of cloning noncomputable maps; check
    bridges — not end-to-end `#eval` — on >1K-bit instances).
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
   included) for the successor. The chain-head layout is **FROZEN
   (2026-07-18, `Reductions/HeadLayout.lean`)** — `headEncodeIn`
   (`headRegBound = 5`) + the `headEncodeIn_bitState` certification; the
   S1 witness's `encodeIn` MUST be it and C8-5's seam MUST hit it. Do not
   change it without re-running `probes/C8SeamProbe.lean` and updating both
   build plans.
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
- **C8-3 — ✅ DONE (2026-07-18-b):** `Reductions/FrontPieces.lean` —
  `emitConst`, `unaryMonomial` (+ `powCost`/`powCost_le`), `reencLoop`
  (offset-parameterized re-encoder), all with run/frame/cost lemmas,
  register-generic, axiom-clean; probe `probes/C8FrontProbe.lean` green
  (incl. the toy front rebuilt from the real pieces against the frozen
  `headEncodeIn`). Artifact list in "Proven, reusable".
- **C8-4 (W_Q assembly):** `fQ` + the correctness iff (forward:
  `paddedBitDecider_run` + wrapper transport within the `steps` budget;
  backward: accepted ⇒ format-valid ⇒ decodes ⇒ `rel` ⇒ `Q x` via
  `rel_correct.sound`) + the `PolyTimeComputableLang` fields.
- **C8-5 (the seam):** `SeamData W_Q W_head` against the head layout — the
  layout is now **FROZEN** (`HeadLayout.headEncodeIn`, 2026-07-18), so
  C8-3/C8-4 can emit against it today; the `SeamData` instance itself still
  waits for the S1 free witness to exist.

## NEXT BOTTOM-UP session — C8-4 (the `W_Q` assembly)

C8-0…C8-3 are done. Next is **C8-4**: assemble the per-`Q` front witness
`W_Q : PolyTimeComputableLang fQ`, `fQ x = (M_Q, s_x, maxSize x, steps x)`,
from the proven pieces. Suggested order (probe-first, commit each green):

1. **The program**: fix a register map (interface `< headRegBound = 5`,
   scratch ≥ 5) and glue `FrontPieces`: `emitConst` reg 1 with
   `encSyms (flattenTM M_Q)` (a per-`Q` constant), `s_x` into reg 2
   (`emitConst`-prefix `encSyms [3]` + per-register `reencLoop` at `off = 1`
   + `emitConst` separators — decide the EXACT `s_x` cell stream against
   `encodeRegs` FIRST on paper, then extend `C8FrontProbe` with a real
   compiled-verifier `#eval` before any lemma), `unaryMonomial` regs 3/4
   from the hypothesis's `encBound`-derived constants (F6), `clear` the
   input register(s). `probes/C8FrontProbe.lean` §4 (`buildFront'`) is the
   validated shape at `off = 0`.
2. **The machine `M_Q` + correctness iff**: the 2026-07-05 assembly notes
   below are the plan (forward via `formatCheck_run` → `composeFlatTM_run` →
   `demoteHalt_run_accept`; backward via `certOKB` split). This is the bulk
   of the session(s) — likely worth splitting machine-iff and witness-fields
   across two sessions.
3. **The witness fields**: run lemma from the `FrontPieces` `_run` lemmas
   (each is get-exact, so `computes` falls out register-by-register); cost
   from the exact-shape cost conjuncts (`monomialCost`/`powCost_le` are the
   `inOPoly` inputs); `enc_bit` against `headEncodeIn_bitState`.
4. ⚠ Risks to check before coding (standing risk #1/#3): `W_Q.encodeIn`
   MUST be the hypothesis witness's `encX` layout verbatim (the only honest
   access to `x`), and the no-instance/garbage-cert direction needs the
   guard story of F5 — re-read findings F1–F6.

One further self-contained bite remains (either stream, no design risk):
**`cookTableau_size_bound`** (see the block before the top-down section).

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

**`FSAT → SAT` is DONE end-to-end (2026-07-16)**, **build health is DONE
(2026-07-17)**, **C8-3 is DONE and `halt_of_satFinal` is PROVEN
(2026-07-18-b)** — the one remaining self-contained bite (no design risk,
proof plan in the docstring), either stream can take it:

- **`cookTableau_size_bound`** (restated 2026-07-17-b at degree 10 for the v2
  card families): ~150–300 LOC of foldl-over-`flatMap` `encodable.size`
  arithmetic (dominant terms: `Θ(|Σ|³)` copy cards + `Θ(|trans|·|Σ|³)`
  incoming-head cards, each of size `Θ(|Σ|)`). Closing it early de-risks the
  S1 cost ladder.

## NEXT TOP-DOWN session — S1 step 3: direction (2) assembly, then the (1b) inversion

Direction (1a) + its gates are PROVEN and the layout is FROZEN (2026-07-18,
see ★ Latest sessions — read that entry's tactic notes before touching the
file). Recommended order (commit each green):

1. **Direction (2): `cover_of_run`** — now FULLY UNBLOCKED (every lemma it
   consumes is proven: `ConfFits_init`/`ConfFits_step`,
   `validStep_of_step`/`validStep_of_halt`, `satFinal_of_halt`). Induction
   unfolding `runFlatTM` from `initFlatConfig M [s]` (`isValidFlatTapes`
   from `hT`/`hs`): a halting configuration freezes for the remaining budget
   (`validStep_of_halt` iterated, cf. `freeze_relpower`), a stepping one
   advances (`validStep_of_step`), a stuck non-halting one contradicts
   `hacc` (`runFlatTM` then returns the stuck config, still non-halting).
   Window-room side conditions from the `ConfFits` bounds (`head ≤ t ≤
   steps`, `len ≤ |s| + t`) against `n = |s| + steps + 3`. Landing this
   FIRST banks half the bijection while (1b) is still open.
2. **Direction (1b): `step_of_validStep`** — the inversion heart (~2K lines
   in the Coq port; est. 1–3 sessions; the docstring lists the four stages).
   Load-bearing facts: the head/tape/boundary **code-disjointness lemmas —
   LANDED 2026-07-18-b** (`hCell_val_lb`/`_ub`, `tCell_ne_hCell`,
   `hCell_ne_bCell`, `tCell_ne_bCell`, `hCell_inj`, `tCell_inj`; ⚠ pair
   them with defeq ascriptions, `omega` cannot see `(hCell …).1` through an
   `unfold`), key-uniqueness inside `dedupKeys` (extend the `dedupGo` lemma
   family), and the deliberate ABSENCE of a head-at-second-slot family.
   Reuse the window machinery backwards: from `TCC.coversHead card
   (a.drop i) (b.drop i)` + the row length, extract the three cell equations
   (an inversion counterpart of `coversHead_take3` — `isPrefix` +
   `take3_drop` gives `(b.drop i).take 3 = ↑card.conc`, then `b`'s cells
   pointwise), then enumerate which family the matched card can lie in by
   its premise cells.
3. **Direction (3): `run_of_cover`** — extraction by induction on the
   `relpower` chain threading `ConfFits` and "the current row is `confRow`
   of the current configuration" via `step_of_validStep`;
   `runFlatTM_of_halting` on the halting branch; `halt_of_satFinal` (PROVEN
   2026-07-18-b) fires on the last row.
4. **The prelude/cert-guess layer** (DESIGN task — paper + probe pass BEFORE
   coding): the deterministic core gives `accepts M [s] steps ↔ tableau`,
   but the S1 witness needs `(∃ cert, |cert| ≤ maxSize ∧ accepts M
   [s ++ cert] steps) ↔ tableau'`. Coq's `preludeRules` shape: wildcard
   cells in the cert region of row 0, guess cards resolving them in covering
   step 1, contiguity enforced window-locally (no symbol right of a blank in
   the guessed region), budget `steps + 1`. Extends the alphabet and
   `cookInit` only — the card algebra and directions (1a)/(1b) are reused
   as-is on rows 1…steps.
5. **The free witness program** (after 1–4): a `Cmd` emitting
   `encodeIn (cookTableau M s steps)` from the FROZEN chain-head layout
   (`HeadLayout.headEncodeIn`; its `enc_bit` field is
   `headEncodeIn_bitState`, already proven) — the emitter patterns
   (`BinaryCC_to_FSAT_free`'s per-stream loops, unary mul for the
   `Θ(|trans|·|Σ|³)` card enumeration) and the standard
   run/cost/witness/seam ladder apply unchanged. ⚠ size: the card list is
   `Θ(|trans|·|Σ|⁴)` encoded — budget `satBound`-style headroom from the
   start (the size bound is stated at degree 10).

**Reusable machinery for ALL of it** (do not re-derive): the
`Lang/CostFlat.lean` toolkit; the witness templates
(`binaryCCFSAT_reductionLang`, `fsatSAT_reductionLang` — field-for-field);
the three live seams (narrow-right-frame variant: `FSAT_to_SAT_comp.lean`);
the cost-assembly pattern of 2026-07-16 (per-branch `private` lemmas +
precomputed frame facts + `clear_value` discipline + symbolic `flatK`
constants); and the run-ladder pattern (pure scan model ≡ tree map, machine
folds ⇒ model).

**After S1 + C8**, the remaining assembly: swap the headline to
`NPhard''`/`NPcomplete''` over the composed front+tail chain and delete the
legacy `⪯p` front (the S2 collapse) — see the C8 section above.

---

## Locked invariants — do NOT revisit

- **The flat tape is APPEND-ONLY AT THE FRONTIER (2026-07-17-b):**
  `writeCurrentTapeSymbol` replaces in range, appends exactly at
  `head = right.length`, and is a NO-OP strictly beyond. Never reintroduce
  the zero-padding jump-write — it is non-local (one step rewriting cells
  arbitrarily far from the head) and falsifies every local-window tableau
  simulation (S1). New machines must not rely on writing past the frontier.
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

- **The C8-3 front-piece layer (2026-07-18-b,
  `Reductions/FrontPieces.lean`, all axiom-clean, register-generic —
  C8-4/C8-5 consume these verbatim)**: `appendConst_run` (seed-`Cmd`-glued
  constant append, exact cost `+2/cell`), `emitConst_run`/`_bits`,
  `appendItem_run` (the `encSyms` item), `reencBody`/`reencLoop_run`
  (bit register → `encSyms ((·+off)`-shifted stream), `scan` drained, `src`
  intact, quadratic cost), `mulStep_run`/`powLoop_run` (`acc := 1^(a·m^k)`
  on `unaryMulLoop_run`, cost `powCost` + closed form `powCost_le`),
  `unaryMonomial_run` (`dst := 1^(c·(n+1)^k+d)`, cost `monomialCost`);
  `HeadLayout.encSyms_snoc` (the `encSyms` loop-invariant closer).
- **The S1 cell-code algebra (2026-07-18-b, `Simulators/CookTableau.lean`)**:
  `hCell_val_lb`/`hCell_val_ub`, `tCell_ne_hCell`/`hCell_ne_bCell`/
  `tCell_ne_bCell`, `hCell_inj`/`tCell_inj` — the three disjoint code bands;
  built for `halt_of_satFinal` (now proven), reused by the (1b) inversion's
  card-classification stage.
- **The S1 (1a) layer (2026-07-18, `Simulators/CookTableau.lean`, all
  axiom-clean)**: `stepFlatTM_normM` + `normTrans_subset`/`dedupGo_subset` +
  the `dedupGo` `find?` lemma family; `step_desc` (unfolded step: fired
  entry + payload + successor shape) and `write_facts` (the packaged write
  effect incl. the `wEff`-at-frontier-flag head-cell fact) — consume these
  for EVERY remaining S1 direction; `ConfFits_init`/`ConfFits_step`; the
  window machinery (`rowCell`/`rowX`/`confRow_window`/`take3_drop`/
  `coversHead_take3`, frontier detection `tapeSymAt_blank_iff`/
  `rowX_isBlank`, membership lemmas for all five step families + all four
  copy/halt families, `copy_window`); `validStep_of_step`/
  `validStep_of_halt`/`satFinal_of_halt`. **The frozen head layout**
  (`Reductions/HeadLayout.lean`): `headEncodeIn`/`headRegBound`/`encSyms`/
  `flattenTM` + `headEncodeIn_bitState` — the S1 witness's `encodeIn` and
  C8-5's seam target; imported by `Complexity.lean`, consumed by
  `probes/C8SeamProbe.lean`.
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
- **The `FSAT_to_SAT` run-lemma LEAVES** (`Reductions/FSAT_to_SAT_free.lean`,
  2026-07-13, all axiom-clean): `encodeCnf_append`/`_cons` (foldr-over-`++`
  distribution — the incremental-emission backbone); the emit-gadget
  projections `emitLit_{cnfout,frame,run}`, `endClause_run`, and per gadget
  `emit{TrueG,EquivG,AndG,OrG,NotG}_{cnfout,tally,frame}` (write exactly
  `encodeCnf (tseytin…)` onto `CNFOUT` + `numClauses` ones onto `TALLY`;
  frames via `Cmd.eval_get_of_not_writes`); the two sentinel-drain inner loops
  `drainSkip_run` (subtreeScan fvar-payload skip) / `drainVar_run` (tokenBody
  fvar read into `VREG`) + their per-shape `_done`/`_one`/`_zero` step helpers;
  and the **complete `budgetBody` dispatch** `budgetBody_frame`,
  `budgetBody_enter`, `budgetBody_{ftrue,fand,forr,fneg,fvar}` (⇒ pure
  `budgetStep_*`), `budgetBody_freeze` (bud=0). `budgetBody` is now factored as
  `nonEmpty NEB BUD ;; ifBit NEB budgetBodyInner nop`.
- **The `FSAT_to_SAT` run-lemma LOOP ASSEMBLIES** (same file, 2026-07-15, all
  axiom-clean — the machine ⇒ map obligation, DONE): **`subtreeScan_run`**
  (Dyck-forest `∃ gs` invariant folding the `budgetBody_*` leaves;
  `T = 1^(formula_size g)`), **`tokenBody_run`** (one iteration = one
  `scanClauses` token, per-shape dispatch integrating `subtreeScan_run`/
  `drainVar_run`/`emit*G`; frame via `tokenBody.writes`) with model bridge
  `tokHead`/`tokRem`/`scanClauses_tok`, **`outerLoop_run`** (Dyck-forest token
  loop; helpers `tokForest`/`tokForest_flatten`/`tokForest_sum`), **`Bloop_run`**
  (the `B := 1^|serF|` length loop), and **`buildSAT_run`** (the assembly:
  `(buildSAT.eval [serF f]).get CNFOUT = encodeCnf (fsatToSat f)` ∧
  `.get TALLY = 1^|fsatToSat f|`). The next witness's `computes` field is
  `buildSAT_run` + `decodeOut = invFun encodeCnf`. Do NOT re-derive.
- **The `FSAT_to_SAT` MECHANICAL FIELDS + LEAF COSTS** (same file, 2026-07-15-b,
  all axiom-clean): the 6 witness fields as standalone theorems — `serF_bit`/
  `encodeIn_bitState` (`enc_bit`), `encodeIn_size_le` (`encBound = 4n`),
  `encodeIn_width` (`width_le`), `buildSAT_usesBelow` (`FRAME = 27`),
  `buildSAT_computes` (`buildSAT_run.1` + `KSat3Free.encodeCnf_injective`),
  `fsatToSat_size_le` (`≤ 300·(n+1)²`, `output_size_le` fodder),
  `buildSAT_decode_agree`; and the 3 leaf loop-cost lemmas `drainVar_cost`/
  `drainSkip_cost` (via `Cmd.cost_forBnd_flat_le` + the `_SCAN_le`/`_SC2_le`
  scan-monotonicity helpers) and `Bloop_cost` (via `cost_constLoop_le`). The
  cost-assembly ladder consumes these unchanged. Do NOT re-derive.
- **The `FSAT_to_SAT` COST ASSEMBLY + WITNESS + SEAM** (2026-07-16, all
  axiom-clean): `tokenBody_cost` (`≤ tokFK·(E+N+3)³`; per-branch `private`
  lemmas `brTrue/brBin/brVar/brTag11/tree_cost`, `X_facts`/`sq_le_X`
  arithmetic helpers, precomputed `subtreeScan_fr_*`/`drainVarLoop_fr_*`
  frame one-liners, `drainVar_cost_le`); `outerLoop_cost` (semantic-invariant
  reuse + `tokRem_length_le`); `satOmega`/`satK`/`satBound` +
  `satBound_poly/_mono/_output`; `buildSAT_cost_le`; the witness
  `fsatSAT_reductionLang` + `fsatSAT_reducesPolyMO' : FSAT ⪯p' SAT`
  (`Reductions/FSAT_to_SAT_free.lean`); and the third seam `scrub3` +
  `fsat_to_SAT_seam` + `flatTCC_to_SAT_witness` +
  `flatTCC_to_SAT_reducesPolyMO' : FlatTCC ⪯p' SAT`
  (`Reductions/FSAT_to_SAT_comp.lean`). **The tail is closed; consume
  `flatTCC_to_SAT_witness`/`flatTCC_to_SAT_reducesPolyMO'` from the endpoint
  bridge — do not re-derive anything below it.**
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
- **NEW (2026-07-16, probing):** `#eval` of a `Cmd` with nested `forBnd`s on
  a >1K-bit stream is OUT OF BUDGET (the budget scan is cubic; the T1 seam
  probe timed out at 10 min) — probe BRIDGES register-by-register on big
  instances and reserve end-to-end `#eval` for small ones. To probe against
  a `noncomputable` map, decode the machine's own output stream (`decodeF`)
  instead of cloning the map.
- Methodology: **skeleton-first; refine the highest-risk gap next; decompose
  `sorry`s, don't elaborate them; probe before committing engineering;
  `def`+`sorry` over `axiom` (count = 0); build green between commits.**
