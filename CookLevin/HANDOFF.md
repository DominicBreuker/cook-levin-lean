# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). This file is the forward-looking working plan; we
work **multi-session in two alternating streams** — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

## Where the proof stands (2026-07-02)

- **In-NP side: DONE & axiom-clean.** `SAT_inNP.sat_NP`, `FlatClique_in_NP`,
  `KSat3Free.inNP_kSAT3_free` (the first live `red_inNP` through the free
  engine), and `KSat3Free.kSAT3_reducesPolyMO'` (`kSAT 3 ⪯p' SAT`, the first
  live honest TM-backed reduction) are all
  `[propext, Classical.choice, Quot.sound]`.
- **Headline `CookLevin` still depends on `sorryAx` — wholly hardness-side.**
  `sorry`s in built code: `red_inNP`'s `inTimePoly` half (`NP.lean`),
  `hasDeciderClassical` (`GenNP_is_hard.lean`), 2× `CookTableau` (S1), 3×
  `MultiToSingle` (dead code). Plus the `sorry`-free **vacuous** defs (S1/S2 +
  size-0 hardness reduction) that `#print axioms` cannot see — Group S in the
  ROADMAP.
- **The compiler (Risk C2) is DONE for everything the proof needs.** 9 ops
  proven; the value-as-length trio (`takeAt`/`dropAt`/`consLen`) is **RETIRED**
  (see below), isolated behind the `Op.IsSupported`/`Cmd.AllOpsSupported` wall.
  `Compile.lean` is a 39-line facade over `Compile/`; new run lemmas go in the
  per-gadget `Compile/Run*` modules, contracts in `Compile/OpSound.lean`.
  Iteration cost: editing a `Run*` module rebuilds it + downstream (~30s);
  editing `OpMachines` rebuilds the chain (~2–3 min). All Compile modules are
  structurally bound except `Decider` (~3.4s) and `Assembly` (~1.2s) — judged
  not worth further perf work.

## ★ SETTLED (2026-07-02, bottom-up audit): the trio & the canonical layer are RETIRED

The audit of the remaining proof path (sound-tail reductions, C8 decider, S1
tableau reduction, `⪯p'` re-typing) confirmed **option (B)**: *nothing* needs
the generic `LangEncodable (X × Y)` product trio — every witness is a bespoke
bit-level **free** witness (`PolyTimeComputableLang`/`DecidesLang`), the pattern
proven live three times (`EvalCnfCmd`, `CliqueRelTM`, `kSAT_to_SAT_free`).
Consequences, all executed:

- **The owner decision on an encoding redesign (Elias-γ prefix, old step 2
  option A) is OBSOLETE.** The unary product migration is dead; do not revive it.
  (Why it was blocked: the bit-level product encoding is size-unsound under
  nesting — machine-checked in `probes/UnaryProductSizeProbe.lean`.)
- **The canonical scaffolding is DELETED** (~1.8K LOC from `PolyTime.lean`:
  `LangEncodable`/`BitEncodable` + instances, `PolyTimeComputableLang'`,
  `DecidesLang'`, `inNPLang`/`red_inNPLang`/`inNPLang_to_inNP`,
  `red_inNP_of_lang`, `swap`/`map_fst`/`map_snd`, `ExtractOnes.lean`). This
  removed 6 permanently-unprovable wall `sorry`s. **Do not rebuild it** — the
  free line covers every role it had (see "The free line" below).
- **The Route-A wall is permanent** until the trio ops themselves are deleted
  (the concrete next bottom-up task, below).

## The free line — the working architecture (use this, and only this)

- **Verifiers**: free `DecidesLang` with a bespoke bit-level `encodeIn`
  (numbers UNARY), bridged by `DecidesLang.toDecidesBy`/`toInTimePoly` →
  `inTimePolyLang_to_inTimePoly` (live: `evalCnfDecidesLang`,
  `cliqueRelDecidesLang`).
- **NP witnesses**: `InNPWitnessLangFree`/`inNPLangFree` (+ `inNPLangFree_to_inNP`);
  the verifier `Cmd` stays recoverable for precomposition.
- **Reductions**: free `PolyTimeComputableLang` → `toFrameworkWitness'` gives
  `polyTimeComputable'`; `reducesPolyMO'_of_langFree` gives `P ⪯p' Q`;
  `red_inNP_of_langFree` gives the `red_inNP` step (verifier precomposition via
  `DecidesLang.FreePrecomposeData`/`precomposeFree`).
- **Composition happens at the `Cmd` level, per seam.** Free encodings share no
  layout, so each seam needs a concrete re-encoder `Cmd` (`FreePrecomposeData`
  pattern; `comp_computes_of_bridge` is the map-side statement of the seam).
- **`NP/kSAT_to_SAT_free.lean` is the template for every further free witness**:
  bespoke layout, ONE generic run+frame+cost lemma per program
  (`kCnf3Check_run`-style, over any base state carrying the input registers —
  that is what lets one program serve several witnesses), `decodeOut :=
  Function.invFun enc` backed by a prefix-free-block injectivity induction, and
  a tight size lemma if `encodeIn_size ≤ 2·size+1` bites
  (`encodeCnf_tally_tight`-style; the loose learned bounds usually scare you off
  a satisfiable obligation).

### ⚠ Two standing architecture risks — check every new witness against these

1. **Honesty is per-witness discipline, not enforced.** `FreePrecomposeData`
   /`PolyTimeComputableLang` have unconstrained `eIn`/`decodeOut`; the trivial
   dishonest instantiation (`eIn := D.encodeIn ∘ gmap`, `mfc := no-op`)
   satisfies every field. `eIn` must be the natural layout of the *input*
   (never of `gmap v`), all reduction work in the `Cmd`. The S3 endgame must
   eventually PIN encodings (per-type pinned layouts, or chain composition
   where stage *n*'s `eIn` is stage *n−1*'s output layout).
2. **There is NO generic `⪯p'`-transitivity, deliberately.** Two opaque
   `polyTimeComputable'` witnesses cannot be honestly composed (no re-encoder
   is recoverable). Today's `red_NPhard` leans on `reducesPolyMO_transitive`
   (size-only — fine); the **migrated** `NPhard'` transport cannot work that
   way. The endgame design must compose chains at the `Cmd` level *first* (the
   C8 wrapper program's output layout pinned to the chain's input layout), then
   bridge once to `⪯p'`. **This is the key open design question of ROADMAP
   step 2 — settle it top-down before building the chain witnesses' seams.**

---

## NEXT BOTTOM-UP session — delete the trio ops (Route B by deletion)

The trio is retired, so finishing Route B is now *deletion*, not proof. One
atomic batch (editing `Syntax.lean` rebuilds everything — plan a full-rebuild
session):

1. Remove `takeAt`/`dropAt`/`consLen` from the `Op` inductive (`Syntax.lean`)
   and their case arms everywhere (`Semantics.lean`, `Frame.lean`,
   `Compile/OpSound.lean` wall-discharged cases, any `decide`/`simp` sets over
   `Op`).
2. Delete **both walls**: `Cmd.NoConsLen` and `Op.IsSupported`/
   `Cmd.AllOpsSupported` (Syntax.lean) + the `noConsLen`/`allOpsSupported`
   fields on `DecidesLang`/`PolyTimeComputableLang`/`FreePrecomposeData` + their
   supplies (`evalCnfCmd_noConsLen`/`_allOpsSupported`,
   `cliqueRelCmd_*`, `kCnf3Check_*`) + the `hsupp`/`hnc` threading through
   `compileOp_sound_physical_residue` → `run_physical_residue_gen` →
   `Compile_run_physical_residue` → `bitDecider_run` → `paddedBitDecider_run`/
   `paddedCompute_run`. (Mechanical reverse of the Route-A threading; the deep
   `forBnd` `hnc_body` machinery is the fiddliest spot.)
3. Re-check axioms of the four headline results + build green.

`compileOp_sound_physical_residue` then covers **all** ops unconditionally.
Alternative if the batch overruns: the wall is proven infrastructure and can
stay forever — the deletion buys cleanliness, not soundness. Time-box it.

## NEXT TOP-DOWN session — start target #2: the sound-tail reductions as free witnesses

All remaining `sorryAx` on `CookLevin`/`Clique_complete` is hardness-side.
Ordered:

1. **`flatTCC_to_flatCC` as a free `PolyTimeComputableLang`** — the cheapest
   next reduction witness; build it exactly like `kSAT_to_SAT_free.lean` (the
   template). Then `FlatCC_to_BinaryCC` (medium), `BinaryCC_to_FSAT` (Tseytin,
   the expensive ~1K-LOC item). `map`-over-lists (`parked/MapNatList_WIP.lean`,
   near-complete draft) gates parts of the chain.
2. **Settle the `NPhard'`/`⪯p'` migration design** (see standing risk 2): how
   hardness transports once `⪯p` is re-typed — Cmd-level chain composition with
   pinned layouts, `NPhard'` proven at the chain endpoint. S1/S2 *stop
   typechecking* when the re-typing lands, so plan the swap as a coordinated
   batch with honest witnesses for the whole tail.
3. **S1 Cook 2D tableau** (`Simulators/CookTableau.lean`, 2 sorries, ~6–11K
   LOC) — the deepest unsoundness, the real front reduction. After #1/#2.
4. **C8** — the universal-source decider (`hasDeciderClassical`,
   `GenNP_is_hard.lean`), single-tape via free `DecidesLang`; subsumes S2
   (collapse the phantom bridges here). Also requires Part 0.1 (real
   `encodable.size` on chain intermediates).

---

## Locked invariants — do NOT revisit

- **`BitState` / `sig = 4` / numbers UNARY (Option B′).** Fixed 4-symbol
  alphabet; `encodeTape` shifts cells `+1` (`0→1`,`1→2`), `0` separates
  registers, `3` terminates/anchors. Every tape-touching state must be
  `Compile.BitState` (cells `∈ {0,1}`). Numbers unary (`enc n = replicate n 1`).
  Owner-settled.
- **Runtime tape-padding resolves the register-count WALL.** `Compile.padRegsTM
  k` grows the tape during the run; `paddedBitDecider_run`/`paddedCompute_run`
  are proven with **no `k ≤ s.length`**. Padding reserves
  `k + 2·loopDepth + 2` registers.
- **`physStepBudget G cost = (9G²+9G+33)·(8·cost+8) + cost`** is the only
  composable budget shape (`_seq` superadditive, `_mono`, cubic `_poly` const
  817). Never an `overhead`/`(·+1)²` shape (quadratics don't compose).
- **`DecidesBy.encode_size` is per-decider POLYNOMIAL** (`encodeBound`). Final
  boundary — do not re-tighten to linear.
- **Per-op contract takes a threaded scratch base `sb`** (`Compile k c`); eqBit-
  style ops use pre-existing interior scratch at `sb`/`sb+1`.
- **`Op.cost eqBit = |src1|+|src2|+1`**, **`Op.cost concat =
  2(|src1|+|src2|)+1`** (size-aware costs; budget bounds that look "off by 2×"
  are usually the `enc_size ≤ 2·size+1` slack).

## Proven, reusable — do not re-derive

- **The kSAT3 free-reduction stack** (`NP/kSAT_to_SAT_free.lean`): `kCnf3Check`
  + `kCnf3Check_run` (run+frame+cost in one statement) + `kSAT3_precomposeData`
  + `kSAT3_reductionLang` + `encodeCnf_injective` (prefix-free-block induction)
  + `encodeCnf_tally_tight` + the `kCheckBudget_le_poly` monomial-domination
  pattern (`ring`-expand both sides, `omega` finishes).
- **The free engine** (`PolyTime.lean`): `InNPWitnessLangFree`/`inNPLangFree`
  + `inNPLangFree_to_inNP`, `DecidesLang.FreePrecomposeData`/`precomposeFree`,
  `InNPWitnessLangFree.precompose`, `red_inNP_of_langFree`,
  `reducesPolyMO'_of_langFree`; concrete witnesses
  `SAT_inNPWitnessLangFree`/`FlatClique_inNPWitnessLangFree`.
- **The verifier stacks** — `EvalCnfCmd.lean` (SAT; probe→step→fold
  invariant→`cost_forBnd_le`) and `CliqueRelTM.lean` (FlatClique; `readNum_run`
  /`ltBit_run` leaves, the 5 per-check run lemmas, `memberEdge_run` as the
  nested-loop template, the length-only-invariant cost stack
  `readNum_cost`→`cliqueRelCmd_cost_bound`). De-privated & reusable:
  `readNum_cost`, `readNum_stream_le`, `readNumBody_effect`,
  `cSkip_eval`/`cSkip_cost`, `replicate_one_snoc`/`replicate_one_eq_iff`,
  `eqBit_replicate`.
- **The compiler assembly** (`Compile/`): `run_physical_residue_gen`,
  `compileSeq_sound_physical_residue`(+`_traj`), `compileForBnd_…` (counted
  loop, fully proven), `compileIfBit_…`, `bitDecider_run`,
  `paddedBitDecider_run`, `paddedComputeTM`/`paddedCompute_run`; the op gadget
  stacks (`opCopy`/`opCopyAppend`/`opConcat`/`opTail`/`opNonEmpty`/`opHead`/
  `opEqBitNG` + run lemmas); the branch/loop/move toolkit (`joinTwoHalts*`,
  `rewindBracket`, `loopTM`, `moveRegionTM` — the move gadgets are
  residue-costly, one-shot bookkeeping only); the threading toolkit
  (`Cmd.eval_preserves_BitState`, `Cmd.size_eval_le`, `State.ext_of_get`, …).
  ⚠ `Compile_sound`/`Compile_run_physical`/`Compile_polyBound` are
  DEAD/superseded — do not attempt to prove.

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (lake **not** on
  PATH; LSP/most MCP can't find it). First build slow — kick off in background.
  Iterate one module: `lake build Complexity.Lang.PolyTime`. Commit per logical
  step, green. Headline: `Complexity.NP.SAT.CookLevin`.
- **Probe** a machine end-to-end (`#eval`/`runFlatTM`) *before* proving its run
  lemma: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/x.lean`. Every
  gadget exits with its head on the trailing terminator — rewind-bracket it.
- **Axiom-check** via a scratch file: `#print axioms <name>` — only
  `propext`/`Classical.choice`/`Quot.sound` for new sorry-free results.
- **`omega` gotchas:** cannot see through `Var := Nat` variables
  (`simp only [Var] at *` first) or through `var`-typed rcases products
  (retype via `obtain ⟨w, hw⟩ : ∃ w : Nat, w = v`); needs GROUPED products
  (`2*(P*P)`, never `2*P*P`); never splits `(l ++ r).length` (hand it
  `List.length_append`); times out on products of two non-literal atoms
  (`generalize` them). Budget certs: `ring`-expand both sides into monomials
  via `have`s, `omega` closes by coefficient domination.
- **`l[i]` after a `Cmd.cost` hypothesis = whnf TIMEOUT** (`get_elem_tactic`'s
  `assumption` pass defeq-checks against every hypothesis). Hoist every
  `l[i]`-bearing `have` BEFORE `obtain`-ing a run/cost lemma.
- **`set` retro-folds eval equations** (a later `rw [← hs]` finds nothing);
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
