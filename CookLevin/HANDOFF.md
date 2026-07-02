# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). This file is the forward-looking working plan; we
work **multi-session in two alternating streams** — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

## Where the proof stands (2026-07-02, evening)

- **In-NP side: DONE & axiom-clean.** `SAT_inNP.sat_NP`, `FlatClique_in_NP`,
  `KSat3Free.inNP_kSAT3_free`, `KSat3Free.kSAT3_reducesPolyMO'` (`kSAT 3 ⪯p' SAT`)
  are all `[propext, Classical.choice, Quot.sound]`.
- **The S3 migration is now EXECUTING.** Two live honest `⪯p'` witnesses
  (`kSAT3_reducesPolyMO'` and **`FlatTCCFree.flatTCC_reducesPolyMO' :
  FlatTCC.FlatTCCLang ⪯p' FlatCCLang`**, the first *sound-tail* step, this
  session), and the **`NPhard'` endgame design is SETTLED & machine-validated**
  (`PolyTimeComputableLang.SeamData`/`comp` fully proven — see below).
- **Headline `CookLevin` still depends on `sorryAx` — wholly hardness-side.**
  `sorry`s in built code: `red_inNP`'s `inTimePoly` half (`NP.lean`),
  `hasDeciderClassical` (`GenNP_is_hard.lean`), 2× `CookTableau` (S1), 3×
  `MultiToSingle` (dead code). Plus the `sorry`-free **vacuous** defs (S1/S2 +
  size-0 hardness reduction) invisible to `#print axioms` — Group S.
- **The compiler (Risk C2) is DONE for everything the proof needs.** 9 ops
  proven; the value-as-length trio is retired behind the `Op.IsSupported`/
  `Cmd.AllOpsSupported` wall, awaiting deletion (bottom-up task below).

## ★ SETTLED (2026-07-02, top-down): the `NPhard'` endgame design

`PolyTime.lean` now carries the whole migrated-hardness architecture,
**sorry-free**:

- **`PolyTimeComputableLang.SeamData`/`comp`** — the Cmd-level chain
  composition (the migrated `red_NPhard`). A seam = a concrete re-encoder
  `Cmd` `mfc` with bridge law `AgreeBelow Wg.regBound ((Wf.c ;; mfc).eval …)
  (Wg.encodeIn (f x))` (same shape as the live `kCnf3Check_bridge`), a
  `decode_frame` law (`Wg.decodeOut` reads only `Wg`'s frame — true of every
  honest decode), and `mfc`'s cost bound. `comp` discharges **all** composite
  witness fields from the seam — chains fold into ONE witness, then bridge
  once via `reducesPolyMO'_of_langFree`.
- **`NPhard'`/`NPcomplete'`** (mirroring `NPhard` over `⪯p'`) + strengthening
  bridges `NPhard'_to_NPhard`/`NPcomplete'_to_NPcomplete`.
- **The rule: `NPhard'` is proven at chain ENDPOINTS only** — never state it
  of an intermediate (no `⪯p'`-transitivity exists, deliberately). C8 must
  produce, per NP problem `Q`, the front witness `W_Q` **together with its
  `SeamData W_Q W_chain`** (output pinned to the chain's fixed input layout);
  `NPhard' SAT := fun Y _ Q hQ => reducesPolyMO'_of_langFree (W_Q.comp … ) …`.
- **Seam discipline (the new standing obligation):** every chain-step witness
  should exit with the canonical layout of its *output type* on the next
  witness's frame — scrub scratch on-machine, or let the seam's `mfc` (short
  copy/clear program) do it. The live `flatTCC_reductionLang` currently leaves
  scratch (regs 9–13, 15, 16, 26) dirty; its first seam's `mfc` must scrub or
  the witness gets a scrubbing epilogue then.

## The free line — the working architecture (use this, and only this)

- **Verifiers**: free `DecidesLang` with bespoke bit-level `encodeIn`
  (numbers UNARY) → `DecidesLang.toDecidesBy`/`toInTimePoly` (live:
  `evalCnfDecidesLang`, `cliqueRelDecidesLang`).
- **NP witnesses**: `InNPWitnessLangFree`/`inNPLangFree` (+ `inNPLangFree_to_inNP`).
- **Reductions**: free `PolyTimeComputableLang` → `toFrameworkWitness'`/
  `reducesPolyMO'_of_langFree`; verifier precomposition via
  `DecidesLang.FreePrecomposeData`/`red_inNP_of_langFree`; **witness-witness
  composition via `SeamData`/`comp`** (no live seam yet — first one is the
  `flatTCC → FlatCC_to_BinaryCC` join, top-down task 2).
- **Templates for new reduction witnesses** — copy these, not first principles:
  - `NP/kSAT_to_SAT_free.lean`: re-encoder + reduction sharing one program,
    fold invariants, tight `encodeIn_size`, `FreePrecomposeData`.
  - `NP/SAT/CookLevin/Reductions/FlatTCC_to_FlatCC_free.lean`: **the sound-tail
    pattern** — drop the input-validity guard when invalid maps to invalid
    (`flatTCC_to_flatCC_isValidFlattening`-style backward transfer + an
    unconditional correctness iff), shared-layout registers for identity
    fields, `blockMove`/`halfMove` stream re-formatting over
    `CliqueRelTM.readNum`, sentinel-list encoding `encSList` + prefix-free
    injectivity, and multi-field decode via `Function.invFun encKey` over an
    extracted register tuple.
- **The canonical `LangEncodable` layer stays DEAD** (deleted 2026-07-02;
  generic product encoding is size-unsound —
  `probes/UnaryProductSizeProbe.lean`). Do not rebuild it.

### ⚠ Standing architecture risks — check every new witness against these

1. **Honesty is per-witness discipline, not enforced.** `eIn`/`encodeIn` must
   be the natural layout of the *input* (never of `gmap v`), `decodeOut` the
   inverse of the natural *output* layout, all reduction work in the `Cmd`.
   The trivial dishonest instantiation satisfies every field — review each
   witness. (Shared-layout registers for fields the map leaves identical are
   fine — the honest program for an identity field costs nothing.)
2. **Seam discipline** (successor of the old "no `⪯p'`-transitivity" risk,
   which is now *answered* by `SeamData`/`comp`): seams are per-pair concrete
   engineering; layouts are pinned by discipline, not types. Watch that C8's
   per-`Q` witness can actually target the chain's fixed input layout — probe
   this when C8 is scoped.

---

## NEXT BOTTOM-UP session — delete the trio ops (Route B by deletion)

Unchanged plan; one atomic batch (editing `Syntax.lean` rebuilds everything —
plan a full-rebuild session):

1. Remove `takeAt`/`dropAt`/`consLen` from the `Op` inductive (`Syntax.lean`)
   and their case arms everywhere (`Semantics.lean`, `Frame.lean`,
   `Compile/OpSound.lean` wall-discharged cases, `decide`/`simp` sets over `Op`).
2. Delete **both walls**: `Cmd.NoConsLen` and `Op.IsSupported`/
   `Cmd.AllOpsSupported` + the `noConsLen`/`allOpsSupported` fields on
   `DecidesLang`/`PolyTimeComputableLang`/`FreePrecomposeData`/**`SeamData`**
   + their supplies (`evalCnfCmd_*`, `cliqueRelCmd_*`, `kCnf3Check_*`,
   `cardConvert_*`) + the `hsupp`/`hnc` threading through
   `compileOp_sound_physical_residue` → `run_physical_residue_gen` →
   `Compile_run_physical_residue` → `bitDecider_run` → `paddedBitDecider_run`/
   `paddedCompute_run`. (The deep `forBnd` `hnc_body` machinery is the
   fiddliest spot.)
3. Re-check axioms of the headline results + build green.

The wall is proven infrastructure and can stay forever — the deletion buys
cleanliness, not soundness. Time-box it; if it overruns, revert and record.

## NEXT TOP-DOWN session — continue target #2: the sound tail as free witnesses

All remaining `sorryAx` on `CookLevin`/`Clique_complete` is hardness-side.
Ordered:

1. **`FlatCC_to_BinaryCC` as a free `PolyTimeComputableLang`** (medium). Use
   the `FlatTCC_to_FlatCC_free.lean` template. Work through the same design
   questions FIRST, in this order: (a) can the `isValidFlattening` guard be
   dropped (invalid → invalid)? — probe the correctness iff on paper before
   coding; (b) the map does real work here (unary block encoding of symbols
   over `Sigma`), so the program needs per-symbol block expansion — probe the
   program with `#eval` before proving (`probes/` pattern); (c) `map`-over-lists
   may be needed — a near-complete draft exists at `parked/MapNatList_WIP.lean`.
2. **The FIRST LIVE `SeamData`**: join `flatTCC_reductionLang` to the new
   `FlatCC_to_BinaryCC` witness via `PolyTimeComputableLang.comp` and check
   the composite's axioms. This validates the settled endgame design on real
   witnesses (the seam `mfc` re-encodes the flatTCC output registers
   `{1,6,7,2,8,4,5}` + scrubs scratch into the new witness's input layout).
   Budget it as its own work item — the bridge proof is a `cardConvert_run`-
   style frame argument, not a formality.
3. **`BinaryCC_to_FSAT` (Tseytin) as a free witness** — the expensive tail
   item (~1K-LOC formula builder re-expressed as a `Cmd`); after it,
   `FSAT_to_SAT`. Only then is the whole sound tail one composable chain.
4. **S1 Cook 2D tableau** (`Simulators/CookTableau.lean`, 2 sorries, ~6–11K
   LOC) — the deepest unsoundness, the real front reduction.
5. **C8** — the universal-source decider (`hasDeciderClassical`), single-tape
   via free `DecidesLang`; subsumes S2 (collapse the phantom bridges here).
   Must now ALSO produce the per-`Q` `SeamData` into the chain head (see the
   settled design). Requires Part 0.1 (real `encodable.size` on chain
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
  2026-07-02, above). No generic `⪯p'`-transitivity — do not attempt one.

## Proven, reusable — do not re-derive

- **The flatTCC free-reduction stack** (`Reductions/FlatTCC_to_FlatCC_free.lean`):
  `blockMove_run`/`halfMove_run` (bare-block → sentinel-element stream
  transport over `readNum`), `cardStep_step` (clamped-`drop`/`take` single
  invariant covering work+idle phases), `encSList` + `encSList_append_inj`
  (prefix-free sentinel lists — reuse for any nested-list layout),
  `encKey_injective`/`extractKey` (multi-field record decode via one
  `Function.invFun`), `flatTCC_to_flatCC_correct` (unguarded-map iff).
- **The chain-composition engine** (`PolyTime.lean`): `SeamData`/`comp`,
  `State.get_append_replicate_nil`, `NPhard'`/`NPcomplete'` + bridges.
- **The kSAT3 free-reduction stack** (`NP/kSAT_to_SAT_free.lean`): `kCnf3Check`
  + run lemma + `kSAT3_precomposeData` + `encodeCnf_injective` +
  `encodeCnf_tally_tight` + the `kCheckBudget_le_poly` monomial-domination
  pattern (`ring`-expand both sides, `omega` finishes).
- **The free engine** (`PolyTime.lean`): `InNPWitnessLangFree`/`inNPLangFree`
  + `inNPLangFree_to_inNP`, `FreePrecomposeData`/`precomposeFree`,
  `red_inNP_of_langFree`, `reducesPolyMO'_of_langFree`.
- **The verifier stacks** — `EvalCnfCmd.lean` (SAT) and `CliqueRelTM.lean`
  (FlatClique; `readNum_run`/`readNum_cost`/`ltBit_run`, `memberEdge_run`
  nested-loop template, length-only-invariant cost stack). De-privated:
  `readNum_cost`, `readNum_stream_le`, `cSkip_eval`/`cSkip_cost`,
  `replicate_one_snoc`/`replicate_one_eq_iff`, `eqBit_replicate`.
- **The compiler assembly** (`Compile/`): `run_physical_residue_gen`,
  `compileSeq_sound_physical_residue`(+`_traj`), `compileForBnd_…`,
  `compileIfBit_…`, `bitDecider_run`, `paddedBitDecider_run`,
  `paddedComputeTM`/`paddedCompute_run`; the op gadget stacks; the
  branch/loop/move toolkit; the threading toolkit (`Cmd.eval_preserves_BitState`,
  `Cmd.size_eval_le`, `State.ext_of_get`, `AgreeBelow`, `Cmd.eval_agree`/
  `cost_agree`, …). ⚠ `Compile_sound`/`Compile_run_physical`/`Compile_polyBound`
  are DEAD/superseded — do not attempt to prove.

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (lake **not** on
  PATH; LSP/most MCP can't find it). First build slow — kick off in background.
  Iterate one module: `lake build Complexity.Lang.PolyTime`. Commit per logical
  step, green. Headline: `Complexity.NP.SAT.CookLevin`.
- **Probe** a machine/program end-to-end (`#eval`) *before* proving its run
  lemma: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/X.lean`.
  Every TM gadget exits with its head on the trailing terminator — rewind-
  bracket it.
- **Axiom-check** via a scratch file: `#print axioms <name>` — only
  `propext`/`Classical.choice`/`Quot.sound` for new sorry-free results.
- **`omega` gotchas:** cannot see through `Var := Nat` variables
  (`simp only [Var] at *` first), `var`-typed rcases products (retype via
  `obtain ⟨w, hw⟩ : ∃ w : Nat, w = v`), **or `encodable.size (n : Nat)`**
  (rewrite with `(fun n => rfl : ∀ n : Nat, encodable.size n = n)` first);
  needs GROUPED products (`2*(P*P)`, never `2*P*P`); never splits
  `(l ++ r).length` (hand it `List.length_append`); times out on products of
  two non-literal atoms (`generalize` them). Budget certs: `ring`-expand both
  sides into monomials via `have`s, `omega` closes by coefficient domination.
  Un-beta-reduced structure-field lambdas are opaque atoms — `show` the
  beta-reduced form first.
- **`l[i]` after a `Cmd.cost` hypothesis = whnf TIMEOUT** (`get_elem_tactic`'s
  `assumption` pass defeq-checks against every hypothesis). Hoist every
  `l[i]`-bearing `have` BEFORE `obtain`-ing a run/cost lemma.
- **`set` retro-folds eval equations but not terms produced by later `rw`** —
  fold new occurrences with `rw [← hs]`. `State.get_set_eq` can't see through
  a `set`-bound local (`s3.get OUT` where `s3 := _.set OUT v`) — state a
  `have hs3OUT : … := by rw [hs3]; exact State.get_set_eq _ _ _` first.
  `rw` matches registers SYNTACTICALLY — wrap as `(by exact hge 26 (by omega))`
  so the expected type drives elaboration. Avoid nested `set`/`let` over
  `State.set`/`.get` (`isDefEq` ×8/level) — flatten with
  `simp only [Cmd.eval_op, Op.eval]`. `.get` mis-resolves on `State` literals —
  write `State.get s r`.
- **`simp` with `List.take_succ` can hit max-recursion in a fat context** — use
  the explicit `rw [List.take_add_one, List.getElem?_eq_getElem hi]` chain.
- **`decide` fails when the goal type mentions free vars** — `show (0 : Nat) ≠ 2`
  first. `Cmd.UsesBelow`/`NoConsLen` of a concrete program: full `simp [defs…]`
  (not `simp only … decide`).
- **`set` (tactic) lives only in `PolyTime.lean`, not `Frame.lean`** (core-only).
- Methodology: **skeleton-first; refine the highest-risk gap next; decompose
  `sorry`s, don't elaborate them; probe before committing engineering;
  `def`+`sorry` over `axiom` (count = 0); build green between commits.**
