# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). This file is the forward-looking working plan; we
work **multi-session in two alternating streams** — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

## Where the proof stands (2026-07-19; **THE SOUND TAIL IS COMPLETE** (`FSATSATComp.flatTCC_to_SAT_reducesPolyMO'`, axiom-clean), **THE S1 BIJECTION IS COMPLETE** (`cookTableau_correct` sorry-free & axiom-clean, 2026-07-18-d; only `cookTableau_size_bound` left in CookTableau), **THE PRELUDE/CERT-GUESS LAYER IS COMPLETE** (`Simulators/GuessTableau.lean`, 2026-07-19-b: `guessTableau_correct` is sorry-free & axiom-clean — P1 `prelude_validStep_of_cert` and P2 `cert_of_prelude_validStep` both PROVEN), **THE CHAIN-HEAD LAYOUT IS FROZEN** (`Reductions/HeadLayout.lean`), **C8-3 IS DONE** (`Reductions/FrontPieces.lean`), **C8-4 IN PROGRESS** (2026-07-19-c/-d: every gadget exists; **2026-07-20: the front machine `M_Q` + machine-iff DONE (`FrontMachine.lean`); 2026-07-20-b: the ABSTRACT LIFTING `FlatSingleTMGenNP (fQ x) ↔ Q x` DONE & axiom-clean, both the parameterized `fQ_correct` and the hypothesis-free `fQ_correct_concrete` with the F6 monomials proven `inOPoly`, `Reductions/FrontLifting.lean`**) — next: **the S1 free-witness program** (emit `guessTableau` as a `PolyTimeComputableLang` reduction) top-down and **C8-4's reduction program + witness fields** bottom-up)

- **C8-4 (the `W_Q` assembly) is IN PROGRESS — GADGETS + MACHINE + MACHINE-IFF
  + ABSTRACT LIFTING + REDUCTION PROGRAM DONE.** All gadgets exist
  (`FrontPieces.emitRegs`/`emitConst`/`unaryMonomial`, 2026-07-19-c/-d; note
  `tallyCells` is now UNUSED, see the finding), the front machine `M_Q` +
  machine-iff are done (`Reductions/FrontMachine.lean`, 2026-07-20), **the
  abstract lifting `FlatSingleTMGenNP (fQ x) ↔ Q x` is done & axiom-clean**
  (`Reductions/FrontLifting.lean`, 2026-07-20-b: `fQ_correct` +
  `fQ_correct_concrete`, F6 monomials `inOPoly`), and **the reduction PROGRAM +
  register-exact run lemma are done & axiom-clean** (`Reductions/FrontProgram.lean`,
  2026-07-20-c: `frontProgram` + `frontProgram_run`). **What's left for C8-4**:
  (iii) the `PolyTimeComputableLang fQ` **witness fields** — `computes` (from
  `frontProgram_run` + `decodeOut`), the cost ladder, and the remaining mechanical
  fields, then wrap into `Q ⪯p' FlatSingleTMGenNP` via `reducesPolyMO'_of_langFree`
  + `fQ_correct`. ⚠ the design uses a **unary size register** in `encodeIn`
  (finding 2026-07-20-c); `tallyCells` and the "encodeIn = encX verbatim" note are
  retired for C8-4. See the rewritten C8-4 section.
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
  `hasDeciderClassical` (`GenNP_is_hard.lean`), 1× `CookTableau`
  (`cookTableau_size_bound` only — **the bijection `cookTableau_correct`
  is sorry-free & axiom-clean, 2026-07-18-d**), 3× `MultiToSingle` (dead
  code). Plus the `sorry`-free **vacuous** defs (S1-stub/S2) invisible to
  `#print axioms` — Group S.
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

- **2026-07-20-c (bottom-up) — C8-4 piece 2: the reduction PROGRAM +
  register-exact run lemma DONE & axiom-clean (`Reductions/FrontProgram.lean`,
  build green 3350→full, probe `probes/C8ProgramProbe.lean` green).**
  `frontProgram MQconst xWidth B cm km dm cs ks ds` wires the C8-3 gadgets
  (`emitRegs`/`unaryMonomial`×2/`emitConst`) into the four `headEncodeIn`
  registers, and **`frontProgram_run`** proves regs 0–4 =
  `headEncodeIn (M_Q, 3::encodeRegs(encX x), cm·(m+1)^km+dm, cs·(m+1)^ks+ds)`
  for input `s` with `encX x` at regs `0..xWidth-1` and the **size register
  `1^m` at `xWidth`** (`[propext, Quot.sound]`).
  **⚠⚠ DESIGN FINDING (risk-based, blocking piece 3 as previously planned):**
  the HANDOFF's `tallyCells` monomial argument (`1^(State.size (encX x))`)
  **cannot discharge `fQ_correct`'s `hmax`/`hsteps`**. Those need the emitted
  budget registers to *dominate* bounds in `encodable.size x` (via
  `certBoundOf`, `MQbudget ≤ dCap (size x)`), but the tally has only an
  **upper** bound to `size x` (`encX_size`) — never a lower one (`encX` need
  not be injective, only Q-value-separating), so no monomial in the tally is
  provably ≥ a `size x`-budget. The plan was internally inconsistent (demanded
  both "monomial ≥ stepsOf(size x)" *and* "argument = tally"); `FrontLifting`
  had punted this exact obligation to piece 2. **Resolution shipped (Option A,
  local & honest):** `W_Q.encodeIn x := encX x ++ [1^(encodable.size x)]` — a
  unary size register, so the monomial argument IS `size x` and the F6
  overshoot is provable (correct direction). This **relaxes the "encodeIn =
  encX verbatim" note** and makes `tallyCells` unused by C8-4; the C8-5 seam
  drops the extra register (scratch `≥ headRegBound`). ⚠ owner may prefer
  **Option B** (add a structural lower-bound field
  `encodable.size x ≤ sizeLB (State.size (encX x))` to `InNPWitnessLangFreeSplit`,
  keeping `encodeIn = encX` but changing the frozen C8-0 interface) — flagged
  for review. Gotchas landed in "Conventions" (metavar-goal omega in
  gadget-call args; `clear_value`; bare-`omega`-on-a-conjunction choke). Next
  bottom-up: **piece 3, the `PolyTimeComputableLang fQ` witness fields** — see
  the rewritten C8-4 section.
- **2026-07-20-b (bottom-up) — C8-4 piece 1: the abstract lifting
  `FlatSingleTMGenNP (fQ x) ↔ Q x` DONE & axiom-clean
  (`Reductions/FrontLifting.lean`, build green 3391).** The conceptual bridge
  validating that `FrontMachine`'s two lemmas exactly match what
  `InNPWitnessLangFreeSplit` supplies. `fQ W maxSize steps x := (MQ verifier.c
  verifier.regBound verifier.xWidth, 3 :: encodeRegs (encX x), maxSize x,
  steps x)`. **`fQ_correct`** (parameterized over `maxSize`/`steps` with two
  clean domination hypotheses `hmax`/`hsteps`): forward = completeness cert →
  `verifier.decides` accept → `encodeIn_eq` splits the pair as
  `encX x ++ [certReg c]` → `MQ_accepts_of_accept`, the yes-cert
  `shiftReg (certReg c) ++ [0,3]` is `list_ofFlatType 4` (sig via `MQ_sig`) and
  its length ≤ `maxSize` via `hmax`; backward = `MQ_no_reject_of_accepts` →
  grammar-valid `creg` + verifier-does-not-reject → `decides` totality gives
  accept → `rel x (decodeReg creg)` → `rel_correct.sound`. **F6 discharged
  concretely** (`fQ_correct_concrete`, no hypotheses): `maxSizeOf n :=
  certBoundOf n + 2`, `stepsOf n` an explicit polynomial dominating `MQbudget`
  on size-bounded certs (`MQbudget_le`, via `padBudget_le` +
  `physStepBudget_mono` + `encodeTape_length`, register frame
  `regBound+2·loopDepth+2` inlined so `omega` matches `MQbudget`'s unfolding),
  BOTH proven `inOPoly` (`maxSizeOf_poly`/`stepsOf_poly` — the `physStepBudget`
  summand dominated by its diagonal via `physStepBudget_poly`). Codec
  `certReg`/`decodeReg` + `certReg_decodeReg`; `certBoundOf`/`cert_complete`/
  `cert_sound` extract the cert bound classically from `rel_correct`;
  `front_state_bounds` routes `State.size`/cost/width through the verifier's own
  `encodeIn_size`/`cost_bound`/`width_le` at `(x,c)` since
  `encX x ++ [certReg c] = verifier.encodeIn (x,c)`. **⚠ gotcha (added to
  Conventions):** `inOPoly_comp`/`inOPoly_add` unfold `physStepBudget` during
  goal-driven unification and split it at the wrong `+` — pass explicit `f`/`g`
  to `inOPoly_comp` and build sums as a `have` (fixed type), then `exact`. Next
  bottom-up: pieces (ii)/(iii) — the reduction program + witness fields; consume
  `fQ_correct_concrete` as a black box (do NOT re-derive the lift). See the
  rewritten C8-4 section.
- **2026-07-20 (bottom-up) — C8-4: the front machine `M_Q` + the machine-level
  correctness iff, BOTH directions, axiom-clean (`Reductions/FrontMachine.lean`,
  build green 3390, new probe `probes/C8MachineProbe.lean` green).** The riskiest
  C8-4 integration — wiring `formatCheckTM` + `demoteHalt` + `paddedBitDeciderTM`
  + `composeFlatTM` into one accept-by-halting machine — is DONE. `MQ c k w :=
  composeFlatTM (formatCheckTM w) (demoteHalt (paddedBitDeciderTM c k)
  (rejectState c k)) (w+6)` over an **abstract verifier `Cmd c`** (`k = regBound`,
  `w = xWidth`); `rejectState = 2 + (Compile k c).states + (padRegsTM …).states`
  (from `paddedBitDecider_run`, `b = 0`). Structural lemmas `MQ_sig`(= 4)/
  `MQ_tapes`(= 1)/`MQ_valid` + `paddedBitDeciderTM_halt_rejectState` (the reject
  state's halt bit, via `_halt_shift` at `i = 2`). **Forward**
  `MQ_accepts_of_accept`: verifier accepts the decoded `sx ++ [creg]` ⇒ `M_Q`
  accepts `(3::encodeRegs sx) ++ (shiftReg creg ++ [0,3])` for every
  `steps ≥ MQbudget c k (sx++[creg])` (the **explicit** F6-overshoot budget =
  format scan + bridge + `paddedBitDecider` budget). **Backward**
  `MQ_no_reject_of_accepts`: `M_Q` accepts `(3::encodeRegs sx) ++ cert` at ANY
  budget ⇒ `cert = shiftReg creg ++ [0,3]` for a bit register `creg` AND the
  verifier does not reject (`(c.eval (sx++[creg])).get 0 ≠ [0]`) — bad grammar
  ⇒ format-check sticks (`composeFlatTM_stuck_M1`), verifier reject ⇒ park
  (`demoteHalt_run_reject` + `composeFlatTM_no_early_halt`); the cert width is the
  constant `w+1`, so the frame hypothesis is the single `w+1 ≤ k`. **⚠ FINDING
  (design validated, no surprises):** the probe (`#eval acceptsFlatTM M_Q` on
  yes/no/garbage certs, toy verifier `nonEmpty 0 2`) confirmed the 2026-07-05
  assembly notes verbatim — the machine story had no misconceptions. Next
  bottom-up: the **abstract lifting** `FlatSingleTMGenNP (fQ x) ↔ Q x` (combine
  the two lemmas with `InNPWitnessLangFreeSplit`'s `verifier.decides`/
  `rel_correct` + the `creg ↔ List Bool` cert bijection + F6 monomials for
  `maxSize`/`steps`), the **reduction program** (wire `emitRegs`/`tallyCells`/
  `unaryMonomial`/`emitConst`, R1 discipline), and the witness fields — see the
  rewritten C8-4 section.
- **2026-07-19-d (bottom-up) — C8-4: the R2 cell-counter gadget landed &
  axiom-clean (`Reductions/FrontPieces.lean`, build green 3389, probe §6
  green).** `FrontPieces.tallyCells cnt dst srcs` emits
  `1^(Σ_{src ∈ srcs} |State.get s src|)` — the input registers' total cell
  count in unary — by folding one `tallyReg` (`forBnd`-bounded-by-`src`
  appending one `1`/cell) per register into a cleared `dst`; sources survive
  read-only, only `dst`/`cnt` touched (`tallyReg_run`/`tallyCells_run`, both
  `[propext, Quot.sound]`). For `srcs = List.range xWidth` the count is exactly
  `State.size (encX x)` (probe §6 checks this) — **the monomial argument `n`
  that regs 3/4's `unaryMonomial` consumes (finding F6, risk R2)**. Cost bound
  `tallyCells_cost` (`≤ 1 + Σ (2 + |src|·5 + |src|²)`, the `inOPoly` input for
  the witness cost field) landed alongside. **This closes R2 — the one
  genuinely-unbuilt C8-4 gadget; every piece the `W_Q` assembly needs now
  exists.** Next bottom-up: the assembly itself (register map + machine `M_Q`
  iff), NOT more gadgets — see the C8-4 section.
- **2026-07-19-c (bottom-up) — C8-4 STARTED: the reg-2 input-string emitter
  landed & axiom-clean (`Reductions/FrontPieces.lean`, build green 3389, probe
  §5 green).** `emitRegs cnt scan tflg dst srcs` folds `reencLoop`(`off=1`) +
  `[0]` separators over the input's register list, emitting exactly
  `encSyms (3 :: encodeRegs (srcs.map (State.get s)))` into a scratch `dst`
  (`emitRegs_run`, `[propext, Quot.sound]`); its `encSyms`-shaped goal closes on
  the new `HeadLayout.encSyms_append` (encSyms is a `++`-homomorphism).
  Design settled this session (all `#eval`-validated): `s_x = 3 :: encodeRegs
  (encX x)` and `s_x ++ cert = encodeTape (encX x ++ certState c)` (the C8-2
  gadget-probe split, re-derived from the emitter's own `s_x`); the machine's
  input tape is `[encodeTape (encX x ++ certState c)]`, which the format check
  passes through unchanged into `paddedBitDecider_run`'s `initFlatConfig` shape.
  **⚠ two risks surfaced (recorded in the C8-4 section — do NOT skip):**
  (R1) the reg-2 read/write collision (build `s_x` in scratch, then move —
  reg 2 may be a source); (R2) the monomial-argument materialization (regs 3/4
  need `1^n` from the input; decide what `n` is and emit it before
  `unaryMonomial`). Next bottom-up: R2 + regs 3/4, then the machine iff.
- **2026-07-19-b (top-down) — THE PRELUDE/CERT-GUESS LAYER IS COMPLETE:
  `guessTableau_correct` sorry-free & axiom-clean (`Simulators/GuessTableau.lean`,
  build green 3389, probe §6 green).** Both remaining sorries closed. The
  spine both directions share (all axiom-clean, catalogued in "Proven,
  reusable"): `gKind`/`gCls` (kind + cert-resolution class at a row
  coordinate), `preludeRow_getElem?`, `gRes_mem` (the deterministic core's
  cell at a coordinate, paired with `gCls`, is a listed resolution of
  `gKind`) + `confRow_res_mem`, `gCls_contig` (the cert's `live* cut*`
  shape ⟹ window-local `contigOK`), and the membership algebra
  `pCell_inj`/`pKindList_mem`/`preludeCards_mem`/the `pRes_*_mem` family.
  **P1** (`prelude_validStep_of_cert`) assembles the window cards from
  `confRow_res_mem` + `gCls_contig`. **P2** (`cert_of_prelude_validStep`)
  is the inversion: `prelude_window_shape` pins each covered window to a
  prelude card (band mismatch rules out embedded cards; `pCell_inj` pins
  the kinds); `row1 = b.map emb`; the cert is read off the star region by
  `findIdx`/`take` on `decodeSym`-decoded cells; `hlive`/`hstop`/`hprop`
  (cut propagates right, straight from the window `contigOK`)/`htail` give
  the `live* cut*` shape; `hgkStar` characterises star coordinates;
  non-star coordinates close by resolution-uniqueness against `gRes_mem`,
  star coordinates by the decode. ⚠ gotchas (added to "Conventions"):
  reuse of the deterministic core's window lemmas across files required
  **un-`private`-ing** `rowCell`/`confRow_getElem[_last]`/`confRow_window`/
  `take3_drop`/`coversHead_take3` in `CookTableau.lean` (visibility only);
  `(⟨v, h⟩ : Fin _).1` is an omega **atom** — feed a `:= rfl` bridge to
  `σ.1`; `rw`ing a `set`-bound list under `getElem` trips "motive not type
  correct" (go through `getElem?`); `PKind.noConfusion h` mis-elaborates —
  close constructor-disjointness with `simp at h`.
- **2026-07-19 (top-down) — the prelude/cert-guess layer DESIGNED (full
  rationale in the `GuessTableau.lean` module docstring).** Band
  disjointness (`PSg = Sg + 2·sig + 5`, a fresh code band above Γ) turns
  the instance's `∃ cert` into row-0 tableau nondeterminism while reusing
  the proven deterministic core UNCHANGED through the value-preserving
  `emb`; row 0 bakes in everything known so `preludeCards M` depends only
  on `M`; cert contiguity is window-local (`contigOK`). The Γ-band
  transfers T1 (`validStep_emb`), T2 (`relpower_emb`, ⚠ FALSE without
  `3 ≤ a.length` — vacuous windows), T3 (`satFinal_emb`) were proven this
  session and `guessTableau_correct` assembled over the two prelude-step
  sorries later closed in -b.
- **2026-07-18…-d (top-down ×3 + bottom-up, compressed) — THE WHOLE S1
  BIJECTION `cookTableau_correct` PROVEN, sorry-free & axiom-clean.**
  (1a) `validStep_of_step`/`validStep_of_halt` + `stepFlatTM_normM` +
  `ConfFits_step` + `satFinal_of_halt` on the shared window machinery;
  `halt_of_satFinal` on the cell-code disjointness algebra; (2)/(3)
  `cover_of_run`/`run_of_cover` on the trajectory inductions; (1b) the
  inversion `step_of_validStep` (window inversion → card classification →
  key uniqueness → coordinate pinning → `assemble_row`). ⚠ **The
  phantom-head defect** (v2 was completeness-unsound at the right row
  edge; machine-checked counterexample `M4`, probe §5) was **fixed by the
  right boundary marker** + `copyRightCards` + the `cfgHead + 4 ≤ n`
  head-room hypotheses. C8-3 (`Reductions/FrontPieces.lean`) landed the
  same window (2026-07-18-b). All artifacts catalogued in "Proven,
  reusable"; the hard-won tactic gotchas (dependent-motive `getElem`
  rewrites via `getElem?`; `cases hmv : e` substitutes the goal only;
  inline-`match`-typed `have`s over-generalize; `rw [h]`-auto-`rfl` can't
  delta-unfold behind projections; `omega` vs. stranded `rw`; defeq
  ascriptions to link `(hCell …).1` to its formula; `++` left-assoc +
  `List.append_assoc` before `getElem?_append_right`) in "Conventions".
- **2026-07-17-b (top-down) — S1 RISK REVIEW + v2 REDESIGN (compressed;
  full rationale lives in the `CookTableau.lean` module docstring).** Four
  independent v1 defects were found *before* bijection effort was spent:
  non-local zero-padding jump-writes (BLOCKING — **semantics fixed**, the
  flat tape is append-only at the frontier; see Locked invariants),
  head-at-center-only cards, no left-edge detection (→ the boundary
  marker), and the `none`-write bug (→ `wEff`). v2 landed the full card
  algebra generated from the key-deduped, shape-filtered **`normTrans`**
  (`stepFlatTM` = `find?` — shadowed duplicates would break completeness),
  the restated `cookTableau_correct` (with the previously-missing
  `validFlatTM`/`tapes = 1`/`list_ofFlatType` hypotheses — exactly the
  future witness's guard), the proven assembly + `immediateHalt` case, and
  the green agreement probe (`probes/S1TableauProbe.lean`).
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
- **C8-4 (W_Q assembly) — MACHINE + LIFTING DONE, PROGRAM/FIELDS LEFT.** The
  front machine `M_Q` + machine-iff (`Reductions/FrontMachine.lean`, 2026-07-20)
  and the abstract correctness iff `FlatSingleTMGenNP (fQ x) ↔ Q x`
  (`Reductions/FrontLifting.lean`, 2026-07-20-b: `fQ_correct` +
  `fQ_correct_concrete`, F6 monomials `inOPoly`) are proven & axiom-clean.
  The reduction `Cmd` `frontProgram` + its run lemma are DONE
  (`Reductions/FrontProgram.lean`, 2026-07-20-c). Remaining: the
  `PolyTimeComputableLang` witness fields — see the "NEXT BOTTOM-UP session"
  section.
- **C8-5 (the seam):** `SeamData W_Q W_head` against the head layout — the
  layout is now **FROZEN** (`HeadLayout.headEncodeIn`, 2026-07-18), so
  C8-3/C8-4 can emit against it today; the `SeamData` instance itself still
  waits for the S1 free witness to exist.

## NEXT BOTTOM-UP session — C8-4 piece 3 (the `PolyTimeComputableLang` witness)

C8-0…C8-3, the machine/machine-iff, the abstract lifting, **and the reduction
PROGRAM** are all DONE & axiom-clean. **Consume `fQ_correct` /
`fQ_correct_concrete` (`FrontLifting.lean`) and `frontProgram_run`
(`FrontProgram.lean`) as black boxes; do NOT re-derive the lift or the program.**
What remains is the single witness `W_Q : PolyTimeComputableLang (fQ …)` and the
one-line wrap into `Q ⪯p' FlatSingleTMGenNP`.

**★ The settled design (read this — it supersedes the old plan).** Finding
2026-07-20-c: the budget registers must dominate `size x`-bounds, so the
monomial argument must be `size x`, materialized from a **unary size register**
in the input:

* **`encodeIn x := W.encX x ++ [1^(encodable.size x)]`** (the size register at
  index `W.xWidth`). NOT `encX` verbatim — that is the whole point of the fix.
* **`f := fQ W Mmax Mstep`** where `Mmax`/`Mstep : X → Nat` are the F6 overshoot
  monomials **as functions of `encodable.size x`** — `Mmax x = cm·(size x+1)^km
  + dm ≥ maxSizeOf W (size x)`, `Mstep x = cs·(size x+1)^ks + ds ≥ stepsOf W
  (size x)`. Extract `(cm,km,dm)`/`(cs,ks,ds)` classically from
  `maxSizeOf_poly`/`stepsOf_poly` via a **global monomial bound** lemma
  (`inOPoly f → ∃ c k d, ∀ n, f n ≤ c·(n+1)^k + d`; `inOPoly` gives `≤ C·n^K`
  past `n0` — fold the `< n0` prefix into `d` with `maxPrefix`). Prove this
  helper first; it is reusable.
* **`c := frontProgram (encSyms (flattenTM M_Q)) W.xWidth B cm km dm cs ks ds`**
  with `B := max headRegBound (W.xWidth + 1)`, `M_Q := MQ W.verifier.c
  W.verifier.regBound W.xWidth`.
* **`decodeOut st := (M_Q, Function.invFun HeadLayout.encSyms (State.get st 2),
  (State.get st 3).length, (State.get st 4).length)`.** Needs **`encSyms`
  injective** (prove `Function.Injective HeadLayout.encSyms` — a self-contained
  prefix-free-decoding lemma; then `Function.leftInverse_invFun` gives
  `decodeOut (headEncodeIn (fQ x)) = fQ x`). The machine component is the
  per-`Q` CONSTANT `M_Q` (honest: reg 1 genuinely holds `encSyms (flattenTM
  M_Q)`, its inverse is the constant).

**The 13 fields** (probe-first is unnecessary — `frontProgram_run` already
pins the outputs; go straight to the fields):
- `computes`: `frontProgram_run` gives regs 0–4 = `headEncodeIn (fQ x)`; apply
  `decodeOut` and the `encSyms`-injectivity left-inverse + the two
  `(replicate _ 1).length` reads. Feed `frontProgram_run`'s hypotheses:
  `hsize` = `State.get (encodeIn x) xWidth = 1^(size x)` (holds by construction),
  `hbits` = `encX_bit` (from `FrontLifting`), `hMQ` = `encSyms_bit`.
- `cost_bound`/`cost_le`: the program cost is `emitRegs` cost (⚠ **still no cost
  bound — add one**, copy `tallyCells_cost`'s foldl template; quadratic in the
  input cell count `≤ dBound (size x)`) + `2·monomialCost` (`powCost_le` closed
  form) + `emitConst` cost (`1 + 2·|encSyms (flattenTM M_Q)|`, a per-`Q`
  constant) + 5 copies. All `inOPoly` in `size x` via `dBound_poly` and the
  monomial degrees.
- `output_size_le`: `encodable.size (fQ x)` = size of the tuple = `sizeFlatTM
  M_Q` (const) + `|s_x|` (linear in `size x`) + `Mmax x` + `Mstep x` (the
  monomials) + overhead; all `inOPoly`.
- `encBound`/`encodeIn_size`: `State.size (encodeIn x) = State.size (encX x) +
  size x ≤ dBound (size x) + size x` (from `encX_size`); `encBound := fun n =>
  dBound n + n`.
- `enc_bit`: `encX_bit` on the `encX` part, `replicate _ 1` bit-level on the
  size register.
- `regBound := B + 9`; `usesBelow`: `frontProgram` touches regs `< B+9` — needs
  a **`Cmd.UsesBelow` lemma for `frontProgram`** (and for each gadget:
  `emitRegs`/`unaryMonomial`/`emitConst` have run/frame/cost lemmas but **no
  `UsesBelow` lemma yet** — add them, register-generic, by induction on the
  `foldl`/recursion, like the run lemmas).
- `width_le`: `(encodeIn x).length = xWidth + 1 ≤ B ≤ B+9`.
- `decode_agree`: padding by empty registers past `B+9` leaves regs 2/3/4
  unchanged (`Cmd.eval_agree` + `usesBelow`), so `decodeOut` is stable.

**Then** `Q ⪯p' FlatSingleTMGenNP` via `reducesPolyMO'_of_langFree W_Q
(fun x => (fQ_correct W Mmax Mstep hmax hsteps x).symm)`, discharging
`hmax`/`hsteps` from the global-monomial-bound helper. (Use `fQ_correct`, NOT
`fQ_correct_concrete` — the monomials overshoot, they don't hit `maxSizeOf`
exactly.)

**⚠ Option B alternative (owner call, not yet taken).** Instead of the size
register, add a structural field `encodable.size x ≤ sizeLB (State.size (encX
x))` (+ `sizeLB` poly) to `InNPWitnessLangFreeSplit`, keeping `encodeIn = encX`
and reinstating `tallyCells`. This changes the frozen C8-0 interface (every
split-witness provider, incl. the eventual SAT membership witness, must supply
it) — heavier, but keeps the "encodeIn = encX" invariant. If the owner prefers
B, the `frontProgram`/`decodeOut`/`computes` shapes are unchanged except the
size register becomes `tallyCells` output and `encodeIn` reverts to `encX`.

Then C8-5: a fourth `SeamData`/`comp` onto the S1 free witness (waits on S1
existing); `mfc` drops the size register (scratch `≥ headRegBound`) and is
otherwise the identity onto `headEncodeIn`.

Two self-contained size-bound bites remain (either stream, no design risk):
**`cookTableau_size_bound`** (see the block before the top-down section) and
its sibling **`guessTableau_size_bound`** (needed by the S1 witness; state it
next to `cookTableau_size_bound` at the same degree 10). Closing either
early de-risks the S1 cost ladder; a bottom-up session that finishes C8-4
quickly should pick one up.

**The machine + machine-iff + abstract lifting are BUILT** — consume
`MQ_accepts_of_accept`/`MQ_no_reject_of_accepts` (`FrontMachine.lean`) and
`fQ_correct`/`fQ_correct_concrete` (`FrontLifting.lean`) as black boxes; do not
re-derive the compose/demote/format-check plumbing or the predicate-level lift.

**`FSAT → SAT` is DONE end-to-end (2026-07-16)**, **build health is DONE
(2026-07-17)**, **C8-3 is DONE (2026-07-18-b)**, and **the whole S1
bijection `cookTableau_correct` is PROVEN (2026-07-18-d)** — the one
remaining self-contained bite (no design risk, proof plan in the
docstring), either stream can take it:

- **`cookTableau_size_bound`** (restated 2026-07-17-b at degree 10 for the v2
  card families; statement unchanged by the 2026-07-18-c marker fix — the
  extra `copyRightCards` family is only `Θ(|Σ|²)` and the row grew one
  cell): ~150–300 LOC of foldl-over-`flatMap` `encodable.size` arithmetic
  (dominant terms: `Θ(|Σ|³)` copy cards + `Θ(|trans|·|Σ|³)` incoming-head
  cards, each of size `Θ(|Σ|)`). Closing it early de-risks the S1 cost
  ladder.

## NEXT TOP-DOWN session — the S1 free-witness program

The S1 **correctness** target is CLOSED: `guessTableau_correct`
(`Simulators/GuessTableau.lean`) is sorry-free & axiom-clean, so `∃ cert,
… ∧ acceptsFlatTM M [s ++ cert] steps ⟺ FlatTCCLang (guessTableau M s
maxSize steps)`. What remains for S1 is the honest **reduction witness** that
maps a `FlatSingleTMGenNP` instance to that `FlatTCC` — the guarded-map
pattern, guard = exactly `guessTableau_correct`'s decidable hypotheses
(`validFlatTM`/`tapes = 1`/`list_ofFlatType`). In order:

1. **`guessTableau_size_bound`** — state it next to `cookTableau_size_bound`
   (same degree-10 `(n+1)^10` shape; the prelude adds only `Θ(|Σ|³)` cards,
   `Θ(|Σ|)` each, so degree 10 has headroom). Mechanical foldl-over-`flatMap`
   `encodable.size` arithmetic; do it FIRST — it de-risks the witness's cost
   ladder and is a self-contained bite. (`cookTableau_size_bound` is the same
   kind of bite and is still open — either can be taken standalone by either
   stream; see the block above.)
2. **The free witness program** (the bulk): a `Cmd` emitting
   `encodeIn (guessTableau M s maxSize steps)` from the FROZEN
   `HeadLayout.headEncodeIn` layout (`headRegBound = 5`; C8-5's seam MUST
   hit the same layout, so pin the input frame to it and document the exit
   frame). ⚠ the card list is `Θ(|trans|·|Σ|⁴)` encoded — budget
   `satBound`-style headroom in the cost ladder. Emitter/run/cost patterns:
   copy `BinaryCC_to_FSAT_free` field-for-field (see "Reusable machinery"
   below). Deliverable: `guessTableau_reducesPolyMO' :
   FlatSingleTMGenNP ⪯p' FlatTCC` (honest), chaining onto the sound tail's
   `flatTCC_to_SAT_witness` via a fourth `SeamData`/`comp`.
3. **`cookTableau_size_bound`** stays available as the fallback
   self-contained bite (see the block above) if step 1/2 stall.

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
  `HeadLayout.encSyms_snoc` (the `encSyms` loop-invariant closer). **Added
  2026-07-19-c**: `emitRegs`/`emitRegs_run` (the reg-2 input-string emitter —
  `dst := encSyms (3 :: encodeRegs (srcs.map get))`, `src` regs intact, only
  `dst`/`scan`/`tflg`/`cnt` touched; NO cost bound yet — add one in C8-4) and
  `HeadLayout.encSyms_append` (encSyms distributes over `++` — the closer for
  every `encSyms`-of-a-concatenation goal). **Added 2026-07-19-d**:
  `tallyReg`/`tallyReg_run` (single register: `dst := dst ++ 1^|src|`,
  `forBnd`-bounded-by-`src` appending one `1`/cell, cost `≤ 1+|src|·5+|src|²`
  via `cost_constLoop_le`) and `tallyCells`/`tallyCells_run`/`tallyCells_cost`
  (the R2 input-cell counter: `dst := 1^(Σ_{src ∈ srcs}|get src|)`, sources
  read-only, only `dst`/`cnt` touched; for `srcs = List.range xWidth` the count
  is `State.size (encX x)` — the `unaryMonomial` argument `n`; cost
  `≤ 1 + Σ(2+|src|·5+|src|²)`, the foldl-cost template `emitRegs`'s missing cost
  bound should copy). All `[propext, Quot.sound]`; probe `C8FrontProbe` §6.
- **The C8-4 front machine + machine-iff (2026-07-20,
  `Reductions/FrontMachine.lean`, all axiom-clean — consume as black boxes for
  the C8-4 witness's correctness field)**: `MQ c k w` (the accept-by-halting
  front machine over an abstract verifier `Cmd`), `rejectState`/`acceptState`
  (`+2`/`+1` shifted, `acceptState_ne_rejectState`), `M2` (the demoted decider);
  the structural lemmas `MQ_sig`(= 4)/`MQ_tapes`(= 1)/`MQ_states`/`MQ_valid` +
  `paddedBitDeciderTM_sig`/`M2_sig`/`_tapes`/`_valid` +
  `paddedBitDeciderTM_halt_rejectState`; the **explicit budget** `MQbudget c k s`
  (the F6 overshoot target); **forward** `MQ_accepts_of_accept` (verifier
  accepts `sx++[creg]` ⇒ `M_Q` accepts `(3::encodeRegs sx)++(shiftReg creg++[0,3])`
  for `steps ≥ MQbudget`) and **backward** `MQ_no_reject_of_accepts` (`M_Q`
  accepts `(3::encodeRegs sx)++cert` ⇒ `cert = shiftReg creg++[0,3]` bit-valid ∧
  `(c.eval (sx++[creg])).get 0 ≠ [0]`; frame hyp is the single `w+1 ≤ k`).
  Probe `probes/C8MachineProbe.lean` (`#eval acceptsFlatTM M_Q` on yes/no/garbage
  certs). Do NOT re-derive the compose/demote/format-check plumbing.
- **The C8-4 abstract lifting (2026-07-20-b, `Reductions/FrontLifting.lean`, all
  axiom-clean — consume as black boxes for the C8-4 witness's correctness field;
  do NOT re-derive the predicate-level lift)**: `fQ W maxSize steps` (the per-`Q`
  front instance, `maxSize`/`steps` abstract), **`fQ_correct`** (the iff,
  parameterized over `maxSize`/`steps` with the two domination hyps `hmax`
  (`certBoundOf + 2 ≤ maxSize`) / `hsteps` (`MQbudget ≤ steps` on size-bounded
  certs)), and **`fQ_correct_concrete`** (hypothesis-free, with concrete
  `maxSizeOf`/`stepsOf`). Supporting: the codec `certReg`/`decodeReg` +
  `certReg_decodeReg` + `certState_eq`; `list_length_le_size`; `encX_bit`/
  `xWidth_succ_le`; `certBoundOf`/`cert_complete`/`cert_sound` (classical cert
  bound from `rel_correct`); `argBound`/`dCap`/`front_state_bounds` (the split
  pair `encX x ++ [certReg c] = verifier.encodeIn (x,c)`, so `State.size`/cost/
  width route through the verifier's own bounds); `MQbudget_le`; the `inOPoly`
  proofs `certBoundOf_poly`/`argBound_poly`/`dCap_poly`/`maxSizeOf_poly`/
  `stepsOf_poly` (helper `lin_dCap_poly`).
- **The C8-4 reduction program (2026-07-20-c, `Reductions/FrontProgram.lean`,
  `[propext, Quot.sound]` — consume as a black box for the C8-4 witness's
  `computes`/`cost` fields; do NOT re-derive the wiring)**: `frontProgram
  MQconst xWidth B cm km dm cs ks ds` (the four-register emitter: `emitRegs`
  into scratch `B`, two `unaryMonomial`s into `B+1`/`B+2`, `emitConst` into
  `B+3`, then `clear 0` + 4 copies into output regs 0–4) and
  **`frontProgram_run`** (regs 0–4 = `headEncodeIn (M_Q, 3::encodeRegs(input),
  cm·(m+1)^km+dm, cs·(m+1)^ks+ds)` for input split as `encX x ++ [1^m]`,
  hyps `5 ≤ B`, `xWidth < B`, `MQconst` bit-level, size reg `= 1^m`, sources
  bit-level). Probe `probes/C8ProgramProbe.lean`. ⚠ **no cost or `UsesBelow`
  lemma yet** — piece 3 adds them (and `UsesBelow` lemmas for the `FrontPieces`
  gadgets, which also lack them).
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
  `validStep_of_halt`/`satFinal_of_halt`. **The S1 trajectory + right-marker
  layer (2026-07-18-c)**: `ConfFits_mono`, `isValidFlatTapes_single`,
  `relpower_of_run`/`cover_of_run`, `run_of_relpower`/`run_of_cover`, and
  the marker machinery `copyRightCards` + `copyRightCard_mem(_cookCards)`,
  `confRow_getElem_last`/`confRow_window_last`/`copyRight_window`.
  **The S1 (1b) inversion layer (2026-07-18-d — all axiom-clean; the whole
  bijection `cookTableau_correct` now sorry-free)**: `window_card`
  (covering ⟹ six cell equations) on the total coordinate view
  `rowCellM`/`confRow_getElem'`; `cookCards_cases`/`stepCardsOf_cases`
  (membership by family); the shape lemmas `card_headfree_middle`/
  `card_bfirst`/`card_blast`/`card_head_center`; key uniqueness
  `dedupGo_notin_seen`/`dedupGo_pairwise`/`normTrans_find?_eq`;
  `stateOf_inj_lt`/`optSym_inj_valid`/`xCell_inj`/`xCell_ne_hCell`; the
  pinning lemmas `validStep_zero`/`validStep_last`/`validStep_away` and
  the `assemble_row` scaffold — if the prelude layer special-cases row 0,
  ALL of this is reused unchanged on rows 1…steps. **The frozen head layout**
  (`Reductions/HeadLayout.lean`): `headEncodeIn`/`headRegBound`/`encSyms`/
  `flattenTM` + `headEncodeIn_bitState` — the S1 witness's `encodeIn` and
  C8-5's seam target; imported by `Complexity.lean`, consumed by
  `probes/C8SeamProbe.lean`.
- **The S1 prelude/guess layer (2026-07-19/-b, `Simulators/GuessTableau.lean`;
  everything PROVEN & axiom-clean — `guessTableau_correct` is sorry-free)**:
  the band alphabet `PSg`/`emb`/`embCard` + `emb_inj`/`emb_val_lt`/`pCell_ge`/
  `preludeCard_shape`/`preludeCard_prem_ge`; the construction
  `PKind`/`pCell`/`pResolutions`/`contigOK`/`preludeCardsOf`/`preludeCards`/
  `guessCards`/`pKindAt`/`preludeRow`/`guessWidth`/`guessFinal`/
  `guessTableau(Typed)` + `guessTableau_wellformed`; the Γ-transfer layer
  `isPrefix_map_emb`/`prelude_no_cover_emb`/`coversHead_emb_of`/`_inv`/
  **`validStep_emb` (T1)**/`exists_preimage_map_emb`/`validStep_emb_row`/
  **`relpower_emb` (T2 — ⚠ requires `3 ≤ a.length`)**/`relpower_emb_of`/
  **`satFinal_emb` (T3)**; **the shared coordinate spine** `gKind`/`gCls`/
  `preludeRow_getElem?`/`gRes_mem`/`confRow_res_mem`/`gCls_cut_live`/
  `gCls_contig` + the membership algebra `pCell_inj`/`pKindList_mem`/
  `preludeCardsOf_mem`/`preludeCards_mem`/`pRes_*_mem`; **P1**
  `prelude_validStep_of_cert`; **the P2 inversion** `cert_of_prelude_validStep`
  with `decodeSym`(`_tCell`/`_hCell`)/`starRes_class`/`star_res_cases`/
  `initStar_res_cases`/`prelude_window_shape`. The eventual S1 witness's guard
  is exactly `guessTableau_correct`'s hypotheses; consume `guessTableau_correct`
  as a black box. Probe: `probes/S1TableauProbe.lean` §6. (⚠ this un-`private`d
  the `CookTableau.lean` window lemmas `rowCell`/`confRow_getElem[_last]`/
  `confRow_window[_last]`/`take3_drop`/`coversHead_take3` — visibility only.)
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
- Methodology: **skeleton-first; refine the highest-risk gap next; decompose
  `sorry`s, don't elaborate them; probe before committing engineering;
  `def`+`sorry` over `axiom` (count = 0); build green between commits.**
