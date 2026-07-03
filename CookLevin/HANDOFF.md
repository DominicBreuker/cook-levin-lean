# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). This file is the forward-looking working plan; we
work **multi-session in two alternating streams** — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

## Where the proof stands (2026-07-05)

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
  (`NoConsLen`, `IsSupported`/`AllOpsSupported`) are **deleted** (this session):
  `Op` has exactly the 9 live constructors, the witness structures carry no wall
  fields, and the compiler chain threads no `hnc`/`hsupp`. **No bottom-up
  compiler debt remains.**

## ★ This session (2026-07-05, top-down): `BinaryCC_to_FSAT` — session 2 (the FULL program, `#eval`-validated end-to-end)

Target #2's **whole reduction program is built and validated** — design GO on
every count. Deliverables, green & sorry-free (pure `Cmd`/`State` data + the
proven codec; `CookLevin` unchanged):

- **`Reductions/BinaryCC_to_FSAT_free.lean`** now carries the complete
  `buildFSAT : Cmd` + `encodeIn : BinaryCC → State` (pinned to the seam frame
  17/18/19/20/21/5). `buildFSAT` = `precompLen ;; computeWF ;; if GWF then
  (serialize `fand init (fand allSteps final)`) else `serF falseFml`. The Polish
  emission collapses the tree into token-emission ORDER; absolute variable
  indices `line*L + step*offset (+i)` are built UNARY from the loop counters via
  `concat`/mul-loops; the wellformedness guard `computeWF` is reproduced
  on-machine (nonEmpty + `leCheck` + unary-modulo `dvdCheck` + `cardLenCheck`).
- **`probes/FSATSerProbe.lean` §4 `runOut`** (`#eval`, all `true`): on real
  instances, `buildFSAT.eval (encodeIn C)` at `FOUT` equals
  `serF (encodeTableau C)` for wellformed `C` and `serF falseFml = [1,1,0,0,0]`
  for non-wellformed `C` (guard tested with width=0, offset=0, bad card length,
  offset∤width) — i.e. exactly `serF (BinaryCC_to_FSAT_instance C)`. The
  `decodeF` round-trip (the real `decodeOut` path) also validated.

This resolves the crux engineering risk (nested-loop var-index arithmetic on a
TREE output). **What remains is pure proof work** (no design risk): the run/cost
lemmas + the `PolyTimeComputableLang` witness + the seam — see NEXT TOP-DOWN.

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
   PAPER before coding (this session's counterexample method: pick a tiny
   invalid instance, check whether its image is accidentally wellformed+
   satisfiable).

---

## NEXT BOTTOM-UP session — Part 0.1: the Encodable sweep (real `encodable.size`)

The compiler cleanup is done; the **only** open bottom-up foundational item is
**Part 0.1** — replace the size-0 `instEncodableDefault` (`Definitions.lean`)
with a real `encodable.size` on every chain-intermediate type
(TCC/CC/BinaryCC/formula/GenNPInput/…). **Why it matters (risk):** over a size-0
type even the *honest* `toFrameworkWitness'` is vacuous (`bound 0`), and the
hardness reduction's `fun _ => 0` output bound is only "valid" because of it —
so this gates BOTH the C8 hardness reduction (top-down) and making any `⪯p'`
non-vacuous. Pervasive but mechanical (~0.5–1K LOC). Approach:

1. Scope it: `grep` every `instEncodableDefault`/`instEncodable*` on the proof
   path; list the types that need a real `size`. Pick the natural `size` per
   type (sum of field sizes; keep it monotone).
2. Do the leaf types first (BinaryCC/formula), then the composites, so each
   `encodable.size` rewrite has its dependencies in place. Re-prove the
   `encodeIn_size`/`output_size_le` obligations on the live free witnesses
   (`kSAT3`, `flatTCC`, `flatCC`, comp) — they currently lean on the size-0
   type; expect small bound bumps.
3. **Probe first**: `#eval` the chosen `size` on a couple of instances and
   confirm the witness `encodeIn_size : ≤ 2·size+1` still holds before proving.

Part 0.1 is now the **sole** open bottom-up item: the previously-suggested
`map`-over-lists gadget (`parked/MapNatList_WIP.lean`) is **no longer needed** —
the top-down `BinaryCC_to_FSAT` builder uses nested `forBnd` token-emit loops,
not a list-map (resolved 2026-07-05). If Part 0.1 feels too big to start cold,
scope it first (the grep + per-type `size` list in step 1) and land the leaf
types as a standalone commit.

## NEXT TOP-DOWN session — target #2 **session 3**: the `BinaryCC_to_FSAT` witness PROOFS

The program `buildFSAT` + `encodeIn` are **built and `#eval`-validated
end-to-end** (session 2). All remaining `sorryAx` on `CookLevin`/`Clique_complete`
is hardness-side. **Session 3 is pure proof work — no design risk** — filling the
`PolyTimeComputableLang BinaryCC_to_FSAT_instance` witness. The full ordered spec
is the in-file **DESIGN COMPLETE — NEXT-SESSION PLAN** block at the bottom of
`Reductions/BinaryCC_to_FSAT_free.lean`; read it first. Summary:

1. **`encodeIn_size ≤ 2·size+1`** — all unary/bit, no doubling; mirror
   `flatCCBin_reductionLang.encodeIn_size` (reuse `encCardsOut_length_le`/
   `encFinal_length_le`).
2. **Run lemmas bottom-up (the crux of the remaining work)** — fold invariants
   à la `sentStep_run`/`initStep_run`:
   `emitBitsFromScan_run`/`emitBitsFromSent_run` (leaf: `OUT = OUT₀ ++
   serF (encodeBitsAt start bits)`; `_Sent` also advances `SCAN` past the
   terminator) → `emitCardsAt_run`/`emitAllSteps_run`/`readOneFinal_run`/
   `emitFinal_run` (compose over the `listAnd`/`listOr` folds via the
   `serF (listAnd/listOr …)` identities) → `computeWF_run` (`GWF = if
   BinaryCC_wellformed C then [1] else []`; needs unary-modulo⇔`∣`, `1^a=1^b↔a=b`)
   → `buildFSAT_run`. Then `computes = decodeOut_of_serF + buildFSAT_run`;
   correctness reuses the sound `encodeTableau_correct` (guard is NECESSARY — it
   assumes `hWf`).
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

**After the witness lands**, the remaining top-down chain (unchanged):

1. **`FSAT_to_SAT` as a free witness + its seam** (smaller; CNF conversion).
   After it, the whole sound tail `FlatTCC → … → SAT` is ONE composable
   witness chain.
3. **S1 Cook 2D tableau** (`Simulators/CookTableau.lean`, 2 sorries, ~6–11K
   LOC) — the deepest unsoundness, the real front reduction.
4. **C8** — the universal-source decider (`hasDeciderClassical`), single-tape
   via free `DecidesLang`; subsumes S2 (collapse the phantom bridges there).
   Must ALSO produce the per-`Q` `SeamData` into the chain head (the settled,
   now-validated design). Requires Part 0.1 (real `encodable.size` on chain
   intermediates).

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
