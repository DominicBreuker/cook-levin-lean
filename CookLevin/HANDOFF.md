# Handoff — the computable layer / compiler (Risk C2)

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). **This file is the working plan for the compiler
(Risk C2)** — the one obligation the whole NP-completeness bridge sits on.

We work **multi-session in two alternating streams**; at the start of each session
the owner says **`bottom-up`** or **`top-down`**:

- **Bottom-up** — build the gadgets/lemmas the contracts need (the remaining ops),
  iterating toward the final proofs.
- **Top-down** — work the final assembly, design its proofs, create supporting
  lemmas with `sorry` when reasonably provable, and surface gaps early.

> **The compiler refactor is DONE** (`Compile.lean` is now a 39-line facade over a
> `Compile/` module DAG; the old refactor stream is closed). **Where new code goes:**
> per-op contract + stub-op cases in `Compile/OpSound.lean`; op-machine `def`s +
> shape lemmas in `Compile/OpMachines.lean`; run lemmas in the per-gadget
> `Compile/Run*` modules (`RunClear` → `RunMove` → `RunCopyTail` → `RunEqBit`, a
> serial chain); assembly/decider in `Compile/Assembly.lean`/`Decider.lean`.
> **Iteration cost:** editing a `Run*` module rebuilds it + everything downstream
> (`OpSound`/`Assembly`/`Decider` ≈ 30s); editing `OpMachines` rebuilds the whole
> chain (~2–3 min) — so prototype run lemmas *first*, add the machine `def` last.
> Profile a module with `lake env lean -Dprofiler=true CookLevin/.../Compile/<Mod>.lean`.
> All Compile modules are now structurally bound (no tactic >0.3s) except `Decider`
> (~3.4s structural `isDefEq`) and `Assembly` (~1.2s `nlinarith` load) — both
> investigated and judged not worth further perf work.

---

## The goal of this stream: all 12 `compileOp`s proven

The compiler `Compile : Cmd → FlatTM` is sound iff every `Op` has a discharged
soundness case in `compileOp_sound_physical_residue`. **9/12 are done; the plan is
to finish the remaining 3** (`takeAt`, `dropAt`, `consLen` — the value-as-length
trio, all gated on the unary migration).

> **★ HEADLINE (2026-06-28, Route A — DONE): `SAT_inNP.sat_NP` is now SORRY-FREE.**
> `#print axioms SAT_inNP.sat_NP = [propext, Classical.choice, Quot.sound]` — the
> **in-NP half of Cook–Levin is axiom-clean.** Achieved by threading an
> op-supportedness wall (`Op.IsSupported` / `Cmd.AllOpsSupported`, Syntax.lean)
> through the decider chain so the *live* trio-free path (`evalCnfCmd`) discharges
> its op cases without touching the 3 stub `sorry`s. The headline `CookLevin`
> theorem **still** depends on `sorryAx` — but now *only* via the **hardness half**
> (`NPhard_GenNP` → `hasDeciderClassical`, plus the S1/S2/S3 vacuity); the in-NP
> route no longer contributes any `sorry`.

Why still finish all 12 (rather than stop at the wall): the **reduction half**
(`⪯p` / `toFrameworkWitness'`, the S3 endgame that compiles the whole reduction
chain to `Cmd`s) uses the full op set including the trio, and Route B then drops
the wall entirely (`compileOp_sound_physical_residue` becomes unconditionally
sorry-free).

**The live dependency chain `sat_NP` walks (all ✅, wall-isolated):**
```
sat_NP (EvalCnfTM.lean)
  → inTimePolyLang_to_inTimePoly → DecidesLang.toInTimePoly/.toDecidesBy   (PolyTime.lean; ✅)
       → Compile.paddedBitDecider_run → Compile.bitDecider_run            (Compile.lean; ✅)
            → Compile_run_physical_residue → run_physical_residue_gen      (✅, threads AllOpsSupported)
                 → compileOp_sound_physical_residue                        (✅ for supported ops;
                                                                            trio cases = absurd hsupp)
       evalCnfDecidesLang : DecidesLang …                                  (✅ COMPLETE, axiom-clean,
                                                                            supplies allOpsSupported)
```
`evalCnfCmd` is `concat`/`takeAt`/`dropAt`/`consLen`-free, budget quartic
(`200000·(n+1)^4`), `regBound = 16`. The verifier layer is **done**. Both bridges
(canonical `DecidesLang'`/`inNPLang_to_inNP`, free/live `DecidesLang`/
`inTimePolyLang_to_inTimePoly`) are assembled on `paddedBitDecider_run`.

---

## Current op status (9/12)

**Proven & axiom-clean** in `compileOp_sound_physical_residue` (each carries the
W-invariant ①; per-op budget `(54·L²+54·L+180)·(Op.cost+1)`):
`appendOne`, `appendZero`, `clear`, `nonEmpty`, `head`, `copy`, `tail`, `eqBit`,
**`concat`** (done this session — `Compile/OpSound.lean`, via `opConcat_run`).

**Remaining (raw `sorry`, `Compile/OpSound.lean` `compileOp_sound_physical_residue`):**
`takeAt`, `dropAt`, `consLen` — the value-as-length trio, all **gated on the unary
migration** (step 2 below, **design now ✅ probe-validated**). There is no more
"buildable without the migration" op; the next bottom-up work is the migration. Its
one additive (independently-committable, green) sub-step is `extractLeadingOnes`
(step 2a); the rest is one atomic batch.

---

## Locked invariants — do NOT revisit

- **`BitState` / `sig = 4` / numbers UNARY (Option B′).** Fixed 4-symbol alphabet;
  `encodeTape` shifts cells `+1` (`0→1`,`1→2`), `0` separates registers, `3`
  terminates/anchors. Every tape-touching state must be `Compile.BitState` (cells
  `∈ {0,1}`). Numbers are unary (`enc n = replicate n 1`); sound because
  `encodable.size Nat = id`. Owner-settled — no further sign-off needed.
- **The WALL is resolved (runtime tape-padding).** `Compile.padRegsTM k` grows the
  tape *during the run* (`encodeTape s → encodeTape (s ++ replicate k [])`), so the
  per-op `hk : k ≤ s.length` is discharged without constraining the input.
  `paddedBitDecider_run`/`paddedCompute_run` are PROVEN with no `k ≤ s.length`. The
  padding reserves `k + 2·loopDepth + 2` registers (program frame + forBnd scratch
  + eqBit's 2 scratch). `padRegsTM` + all interface lemmas are sorry-free.
- **`physStepBudget G cost = (9G²+9G+33)·(8·cost+8) + cost`** is the only composable
  budget shape (`_seq` superadditive, `_mono`, cubic `_poly` const 817). The 8
  units/cost-item fund forBnd bookkeeping — do not re-tighten. Never an
  `overhead`/`(·+1)²` shape (quadratics don't compose).
- **`DecidesBy.encode_size` is per-decider POLYNOMIAL** (`encodeBound` + `_poly` +
  `_mono`). Final boundary — do not re-tighten to linear.
- **Per-op contract takes a threaded scratch base `sb`** (`Compile k c`): the eqBit-
  style ops use pre-existing interior scratch at `sb`/`sb+1` (`sb+1 < s.length`,
  `s.get sb = s.get (sb+1) = []`).
- **`Op.cost eqBit = |src1|+|src2|+1`** (reads two sources; not unit cost). Any new
  `Cmd` using `eqBit` must charge for it.

---

## The plan to 12 ops

### 1. `concat` — ✅ DONE (this session, axiom-clean)
`Compile.opConcat` (Cmd.lean) = the aliasing-safe 4-stage scratch chain
`opCopy sb src1 ⨾ opCopyAppend sb src2 ⨾ opCopy dst sb ⨾ clear sb`; the OpSound
case is discharged by `Compile.opConcat_run` (OpSound.lean). `Op.cost concat` was
bumped to `2(|src1|+|src2|)+1` (the scratch round-trip dumps ~2|V| into the
residue; needed for the W-invariant). New **reusable** infrastructure (do not
re-derive — see "Proven, reusable" below): `opCopyAppend`/`copyAppendRaw_run`/
`opCopyAppend_run` (the nonempty-`dst` cursor copy = `opCopy` minus the clear),
and the **4-stage `compileSeq_sound_physical_residue` composition pattern** with
its `nlinarith`-over-ℤ budget certificate `concat_budget_arith`.

### 2. Unary migration — **START HERE** (bottom-up; gates the trio; needed for S3 anyway)
**✅ DESIGN VALIDATED 2026-06-28** (`probes/UnaryMigrationProbe.lean`, axiom-free
`#eval`; `lean probes/UnaryMigrationProbe.lean` → all `true`). It is a single
**coupled atomic batch** — `Op.eval` for the trio breaks BOTH `swapCmd` and
`mapFstCmd` in `PolyTime.lean` at once, so they all re-derive together (nothing
decouples; blast radius is otherwise contained — the product toolkit has **no
external consumers**, only `PolyTime.lean` references it). The validated design:

- **Bit-level product encoding** (replaces the single non-bit length-prefix cell):
  `enc(x,y) = replicate |enc x| 1 ++ [0] ++ enc x ++ enc y` (unary length prefix,
  `0` separator, then the two components). `BitState`-clean; the `0` separator makes
  the leading 1-run unambiguous even when `enc x` is empty or itself starts with `1`s.
  New `dec` = (count leading 1s = L; `rest := drop (L+1)`; `(rest.take L, rest.drop L)`).
- **New trio semantics** (count = the register's **unary length**, not `.headD 0`):
  `takeAt dst src lenReg := (s.get src).take (s.get lenReg).length`; `dropAt` mirror;
  **`consLen dst lenSrc src := replicate (s.get lenSrc).length 1 ++ [0] ++ s.get src`**
  (now writes a unary block → **preserves `BitState`**, so `Op.consLen_breaks_BitState`
  becomes false and the `NoConsLen` walls can eventually be dropped — but leave that
  threading for a follow-up; restating `consLen` does not require dropping it).
  Bump `Op.cost consLen` (it now materialises `|lenSrc|` cells).

- **★ KEY FINDING (the old "just re-derive swap" was an under-estimate).** Product
  *unpacking* must recover `L = |enc x|` from the unary prefix, which the current op
  set **cannot do** (`head` peels one cell; `takeAt`/`dropAt` need the very count they
  seek). Two routes, BOTH `#eval`-validated in the probe:
  * **Option L (RECOMMENDED)** — a reusable DSL subroutine `extractLeadingOnes dst src`
    (scratch params) built from EXISTING ops + one `forBnd` over `src`:
    `head HD SC ⨾ ifBit DONE (noop) (ifBit HD (appendOne dst) (appendOne DONE)) ⨾ tail SC SC`.
    **No new op, no new gadget, op count stays 12.** Correctness = a `forBnd` fold
    invariant (DONE flag), the same pattern as the proven `EvalCnfCmd.memberCheck`.
    Build it once; `swap`/`mapFst`/`mapSnd` consume it. Cost becomes quadratic
    (`forBnd`'s `iters²`) — fine, only `inOPoly`/`monotonic` is needed downstream.
  * **Option H** — a new op `headOnes dst src := (s.get src).takeWhile (·==1)`. Cleaner
    straight-line `swap`, but adds a 13th op + its counted-loop gadget + a contract
    case + ~13 exhaustive-match arms. Rejected unless Option L's loop proof stalls.

- **`BitEncodable` plumbing:** add `[BitEncodable X] [BitEncodable Y]` to `swap`/`mapFst`/
  `mapSnd`; give `BitEncodable (X × Y)` (bit-level product); set `enc_bit :=
  BitEncodable.enc_bit` — this **discharges the two live `enc_bit := sorry`s**
  (`PolyTime.lean:1321`, `:1733`). ⚠ `BitEncodable (List Nat)` is FALSE under the
  `id` encoding (cells can be ≥2) — do NOT claim it; the generic witnesses are over
  abstract `X`/`Y` so they don't need it. Migrating `List Nat` to a bit-level encoding
  (drop the `id` shortcut for the length-prefixed `encListGen`) is a SEPARATE, later
  ripple — not needed for this batch.

**Concrete batch order:** (a) `extractLeadingOnes` def + fold-invariant correctness
lemma (additive, green — the only piece that can land as its own commit); (b) restate
trio `Op.eval`/`Op.cost`; (c) new product `enc`/`dec`/`dec_enc`/`enc_size` + `BitEncodable`;
(d) rewrite `swapCmd`/`mapFstCmd`/`mapSndCmd` (`_eval`/`_cost`/`normalizes`/`usesBelow`/
`enc_bit`) against the new design; (e) fix the trio `Op.inBounds`/`BitState`-preservation
cases in `Compile/RunClear.lean`. Steps (b)–(e) land together (atomic).

### 3. `takeAt` / `dropAt` / `consLen` TM gadgets (bottom-up; after step 2 — the actual op-soundness deliverable)
Each is a **counted loop** reusing proven patterns: the unary `lenReg`/`lenSrc` is a
loop bound (`forBnd`); `takeAt`/`dropAt` are counter-driven cursor copies (reuse
`opCopy`/`copyLoop_run`, `loopBudget_le`); `consLen` writes `replicate |lenSrc| 1 ++ [0]`
then appends `src` (an `appendOne`-loop + the `concat`/`opCopyAppend` toolkit). Discharge
the three cases of `compileOp_sound_physical_residue`. After this all 12 ops are proven →
`compileOp_sound_physical_residue` is sorry-free *unconditionally*, which lets Route B
**delete the `Op.IsSupported` wall** (`sat_NP` is already sorry-free via Route A; the
wall is then pure overhead). Feasibility of all three is probe-asserted (counted loops
over proven gadgets).

### 4. Close out

**Route A — ✅ DONE (2026-06-28).** `Op.IsSupported`/`Cmd.AllOpsSupported`
(Syntax.lean) threaded through the decider chain; `sat_NP` is sorry-free &
axiom-clean. The wall is now **proven, reusable infrastructure** (see below). No
further work on the in-NP soundness win.

**Route B (after all 12 proven): unconditional close-out + drop the wall.** Once
the trio is done (steps 2–3), `compileOp_sound_physical_residue`'s trio cases
become real, so the `Op.IsSupported` hypothesis is satisfiable for *every* `Cmd`.
Then **delete the wall** (`hsupp`/`allOpsSupported` field + the two reduction-side
`c_allOpsSupported` sorries at `PolyTime.lean`) — they exist only to isolate the
trio. This also lets the reduction-side `c_noConsLen` sorries go (consLen becomes
`BitState`-preserving). Mechanical reverse of Route A's threading.

⚠ **Cost-bump ripple note (for whoever touches the product toolkit / endgame
`Cmd.cost`):** `Op.cost concat = 2(|src1|+|src2|)+1` now. The product-toolkit
witnesses absorbed this — `swapCmd` bound is `12·n+22`, `mapFstCmd` is
`7·cost_bound + 18·n + 31` (PolyTime.lean). `enc_size` is `|enc x| ≤ 2·size+1`
(NOT `≤ size`) — budget bounds that look "off by 2×" are usually this.

### TOP-DOWN follow-up (concrete next top-down session; Route A is done)
Pick one — both are independent of the bottom-up trio work:
- **CliqueRelTM** (`Deciders/CliqueRelTM.lean`, still raw `sorry` defs+fields,
  incl. the new `allOpsSupported := by sorry` — trivial once `cliqueRelCmd` is
  concrete & trio-free): replicate the proven EvalCnf end-to-end template
  (probe→step-lemma→invariant→`cost_forBnd_le`; uniform-bound cost fixes degree per
  loop nest; be generous with scratch). This makes `FlatClique`'s in-NP half
  axiom-clean too (same `allOpsSupported`-wall win as SAT, for free once the
  fields are real). Gates `FlatClique_in_NP → Clique_complete`. **Recommended next
  top-down** — it is the EvalCnf template applied once more, low structural risk.
- **Framework `red_inNP`** (`NP.lean:291`) / **S3 migration**: blocked by design —
  `inNP` exposes an opaque `FlatTM`, no `Cmd` recoverable. Fix = make framework
  `inNP`/`inTimePoly` layer-native (carry a `DecidesLang`), then it collapses to
  `red_inNP_of_lang`. Deep S3-migration item; design with ROADMAP step 2. Higher
  structural risk; do CliqueRelTM first.

---

## Proven, reusable — do not re-derive

The op builds below are templates; the helper stacks are axiom-clean.

- **The op-supportedness wall (Route A) is closed.** `Op.IsSupported`/
  `Cmd.AllOpsSupported` (Syntax.lean) + the field `allOpsSupported` on
  `DecidesLang`/`PolyTimeComputableLang`, threaded through
  `compileOp_sound_physical_residue` (`hsupp`; trio cases = `simp only
  [Op.IsSupported] at hsupp`) → `run_physical_residue_gen` →
  `Compile_run_physical_residue` → `bitDecider_run` →
  `paddedBitDecider_run`/`paddedCompute_run`. The wall rides *parallel* to the
  `NoConsLen` wall (it only needs to reach the op leaf; the deep `forBnd`
  `hnc_body` machinery is untouched). `evalCnfCmd_allOpsSupported` is the real
  supply (mirrors `evalCnfCmd_noConsLen`); reduction-side `c_allOpsSupported` are
  sorry placeholders (same status as `c_noConsLen`). **Reuse this pattern for any
  new concrete trio-free decider** (e.g. CliqueRelTM) to get its in-NP half
  axiom-clean. Delete the whole wall in Route B once the trio is proven.
- **Assembly is closed.** `run_physical_residue_gen` (residue induction; op/seq
  proven, ifBit/forBnd dispatch to their combinators; W-① + budget ② + scratch
  invariant threaded), `compileSeq_sound_physical_residue` (+`_traj`) — now placed
  **above** the op contract in OpSound so per-op gadgets (e.g. `opConcat_run`) can
  chain stages; `bitDecider_run`, `paddedBitDecider_run`, `paddedComputeTM`/`paddedCompute_run`
  (function-side WALL). Both decider bridges + the reduction bridge
  (`PolyTimeComputableLang.toFrameworkWitness'` on `paddedCompute_run`) + layer
  composition / NP-routing (`red_inNP_of_lang`) are sorry-free modulo the 3 ops.
  ⚠ `Compile_sound`/`Compile_run_physical`/`Compile_polyBound` are DEAD/superseded
  — do not attempt to prove.
- **`compileForBnd_sound_physical_residue`** — the counted loop, FULLY PROVEN &
  axiom-clean (`forBndIterate`/`forBndLoopTM`, both `loopTM` contracts, the five
  fold invariants + `forBndLoop_invariant`, `forBndLoop_eval`/`_agree`,
  `cost_forBnd_eq`, the budget collapse `physStepBudget_sum_le`/`forBndBudget_arith`).
- **`compileIfBit_sound_physical_residue`** — PROVEN (real `compileTestBit` tester +
  `branchComposeFlatTM` + `joinTwoHalts`).
- **The op gadget stacks** (each = real `CompiledCmd` + run lemma + contract case),
  all axiom-clean: `opCopy`/`copyLoop_run`/`opCopy_run` (cursor-copy, marked-tape
  toolkit) + **`copyLoopAppend_run`** (the nonempty-`dst` generalisation, appends
  `src` to `s.get dst`) + **`opCopyAppend`/`copyAppendRaw_run`/`opCopyAppend_run`**
  (the CompiledCmd cursor-copy WITHOUT the clear = `opCopy` minus phase 1; appends
  `src` to `dst`, residue unchanged — the `concat` second-copy primitive),
  **`opConcat`/`opConcat_run`** (the 4-stage scratch chain + its `concat_budget_arith`
  ℤ-`nlinarith` certificate; the **template for any multi-`CompiledCmd` op**: chain
  per-stage run/traj lemmas through `compileSeq_sound_physical_residue`/`_traj`, then
  bound the additive-seam budget `Σtᵢ+3` by per-stage tape-length equalities + a
  cert), `opTail`/`opTail_run`,
  `opNonEmpty`, `opHead`/`bitReadTM` (nested 2-way
  branches), `opEqBitNG`/`opEqBitNG_run` (the `compareRegsNoGrowM` consume-loop tree:
  `copyEmptyRawTM`/`compareLoopTM`/`eqVerdictM`/`bitCompareM`/`bothNonemptyM`/
  `testMachine`/`compareBodyTM` + `consumeStep`/`matchLen` semantics + the
  `eqBit_budget_arith` certificate).
- **Branch/loop/move toolkit:** `joinTwoHalts*` (+ `_reaches_kept`/`_step_to_h1`/
  transport variants), `rewindBracket`/`_transport`, `branchComposeFlatTM` halt-only
  generalizations (`_M2two`/`_M3two`/both), `opRewindToZero` (rewind-to-sentinel
  leaf), `navTestRewindM`/`readBitRewindM`, `loopTM`(+`_run`/`_no_early_halt`)/
  `loopBudget_le`, `moveRegionTM`/`moveRegion2TM`. ⚠ The move gadgets are
  **residue-costly** (append `|src|` zeros/pass) — one-shot bookkeeping only, never
  for factor-1 W-invariant per-op contracts.
- **EvalCnf verifier (LIVE) — DONE & axiom-clean** (`EvalCnfCmd.lean`): unary/
  bit-level encoding (`encodeState_bit`, the `encsize_list_foldr`/`length_le_encsize`
  size helpers, `encodeState_size_bound ≤ 6·size`), all inner bodies + contracts +
  assembly (`evalCnfDecidesLang`). Reusable for CliqueRelTM.
- **Threading toolkit:** `Cmd.eval_preserves_BitState`, `Op.inBounds_of_UsesBelow`,
  `Cmd.eval_length_ge/_le`, `Cmd.size_eval_le`, `State.set_set`/`set_length_ge`,
  `BitState_set_pad`, `consumeStep_frame`/`_clear_restore`, `State.ext_of_get`.

---

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (lake **not** on PATH;
  LSP/most MCP can't find it). First build slow — kick off in background. Iterate one
  module: `lake build Complexity.Lang.Compile` / `…PolyTime`. Commit per logical
  step, green. Headline: `Complexity.NP.SAT.CookLevin`.
- **Probe** a machine end-to-end (`#eval` / `runFlatTM`) *before* proving its run
  lemma: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/x.lean`. Every
  gadget exits with its head on the trailing terminator — rewind-bracket it. Append
  a bit `b` = `appendAtTM (b+1)`; `deleteCarryTM` deletes the cell left of the head;
  `navigateAndTestTM src` lands the head **on** src's first content.
- **Axiom-check** via a scratch file: `#print axioms <name>` — only `propext`/
  `Classical.choice`/`Quot.sound` for new sorry-free results.
- **`omega` can't see through `Var := Nat`.** A bare `sb : Var` atom reports "no
  usable constraints"; `show (… : Nat)` does NOT help (the hypothesis keeps the
  `Var` atom). Fix: **`simp only [Var] at *; omega`**, or explicit `Nat.*` lemmas.
  `(State.get s r).length` (opaque `Nat`) is fine. `omega` never splits
  `(l ++ r).length` — hand it `List.length_append`. `omega` hits `whnf`/`isDefEq`
  TIMEOUTS on products of two non-literal atoms — `generalize` the products or end
  with explicit `Nat.add_le_add`/`Nat.mul_le_mul` terms. `omega` DOES handle opaque
  nonlinear atoms (`m*m`, `m^k`, `cost`) given explicit bridge facts.
- **Avoid nested `set`/`let` over `State.set`/`.get`** (`isDefEq` blows up ×8/level)
  — flatten with `simp only [Cmd.eval_op, Op.eval]`. **`.get` mis-resolves on `State`
  literals** — write `State.get s r`. **Dependent `Fin`-index rewrites** fail
  ("motive not type correct") — route via `getElem?` + `List.getElem?_eq_getElem`.
- **`decide` fails when the goal type mentions free vars** — `show (0 : Nat) ≠ 2`
  first. `Cmd.UsesBelow`/`NoConsLen` of a concrete program: full `simp [defs…]`.
- **`set` lives only in `PolyTime.lean`, not `Frame.lean`** (core-only, no Mathlib).
- Methodology: **skeleton-first; refine the highest-risk gap next; decompose
  `sorry`s, don't elaborate them; probe before committing engineering; `def`+`sorry`
  over `axiom` (count = 0); build green between commits.**
</content>
