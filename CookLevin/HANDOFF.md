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
trio, all gated on the unary migration). Why all 12 (not the `Op.IsSupported`
shortcut that would isolate only the live SAT path):

- We need them anyway — the **reduction half** (`⪯p` / `toFrameworkWitness'`, the
  S3 endgame that compiles the whole reduction chain to `Cmd`s) uses the full op
  set, including the value-as-length trio.
- Once all 12 are discharged, `compileOp_sound_physical_residue` is **sorry-free**,
  so `SAT_inNP.sat_NP` becomes sorry-free **automatically** — no extra threading.
  (`#print axioms` taints on the whole constant body, so today the 4 stub `sorry`s
  keep `sat_NP` at `sorryAx` even though `evalCnfCmd` uses none of them.)

**The live dependency chain `sat_NP` walks:**
```
sat_NP (EvalCnfTM.lean)
  → inTimePolyLang_to_inTimePoly → DecidesLang.toInTimePoly/.toDecidesBy   (PolyTime.lean; ✅)
       → Compile.paddedBitDecider_run → Compile.bitDecider_run            (Compile.lean; ✅)
            → Compile_run_physical_residue → run_physical_residue_gen      (✅ from the assembly)
                 → compileOp_sound_physical_residue                        (⚠ 3 stub sorries)
       evalCnfDecidesLang : DecidesLang …                                  (✅ COMPLETE, axiom-clean)
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
migration** (step 2 below). There is no more "buildable without the migration" op;
the next bottom-up work is the migration itself.

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
The value-as-length trio `takeAt`/`dropAt`/`consLen` is meaningless under `BitState`
with the current `.headD 0` length. Re-state them with **count = the register's
unary length**; bump `consLen`'s `Op.cost`; re-lay the `Nat`/product/`List` canonical
encodings bit-level (the product's single length-prefix cell → a unary block) +
`BitEncodable` instances; re-derive `swapCmd`/`mapFstCmd`/`mapSndCmd` correctness.
After this, `consLen` preserves `BitState` and the `NoConsLen` side-conditions
(`DecidesLang'.c_noConsLen`, `PolyTimeComputableLang'.c_noConsLen`,
`DecidesLang.noConsLen`) can be **dropped**. ⚠ Ripples to the proven product-toolkit
`normalizes`/cost proofs — schedule as its own batch.

### 3. `takeAt` / `dropAt` / `consLen` (bottom-up; after step 2)
Build on the unary length register as a loop counter (the same counted-loop pattern
as `copy`/`forBnd`). Reuse `loopBudget_le`, the cursor-copy toolkit, and the
counter-driven block transfer.

### 4. Close out — two independent routes to the headline soundness win

**Route A (top-down, do this FIRST — does NOT wait for the trio): `Op.IsSupported`
threading.** The live `sat_NP` path (`evalCnfCmd`) uses none of `takeAt`/`dropAt`/
`consLen`, yet `#print axioms SAT_inNP.sat_NP` is still `sorryAx` because it walks
the *generic* `compileOp_sound_physical_residue` whose body still has the 3 stub
sorries (`#print axioms` taints on the whole constant). Fix: add a predicate
`Op.IsSupported` (true for the 9 proven ops, false for the trio) + `Cmd.AllOpsSupported`,
thread it as a hypothesis through `compileOp_sound_physical_residue` →
`run_physical_residue_gen` → `bitDecider_run` → … so the trio cases discharge by
`exact absurd … (by simp [Op.IsSupported])` instead of `sorry`. `evalCnfCmd`
satisfies `AllOpsSupported` by `decide`. This makes `sat_NP` sorry-free — the first
headline soundness win — **without** the unary migration. Estimate: medium (the
threading touches the assembly chain but each step is mechanical).

**Route B (after all 12 proven): unconditional close-out.** Once the trio is done
(steps 2–3), `compileOp_sound_physical_residue` is sorry-free outright, so `sat_NP`
drops `sorryAx` automatically (no `IsSupported` plumbing needed). Then **update
README + ROADMAP** (the "in-NP half reaches a `sorry`" line becomes false for SAT).

⚠ **Cost-bump ripple note (for whoever touches the product toolkit / endgame
`Cmd.cost`):** `Op.cost concat = 2(|src1|+|src2|)+1` now. The product-toolkit
witnesses absorbed this — `swapCmd` bound is `12·n+22`, `mapFstCmd` is
`7·cost_bound + 18·n + 31` (PolyTime.lean). `enc_size` is `|enc x| ≤ 2·size+1`
(NOT `≤ size`) — budget bounds that look "off by 2×" are usually this.

### Standalone top-down work (not on the 12-op critical path)
- **CliqueRelTM** (`Deciders/CliqueRelTM.lean`, still raw `sorry` defs+fields):
  replicate the proven EvalCnf end-to-end template (probe→step-lemma→invariant→
  `cost_forBnd_le`; uniform-bound cost fixes degree per loop nest; be generous with
  scratch). Gates `FlatClique_in_NP → Clique_complete` (a secondary theorem).
- **Framework `red_inNP`** (`NP.lean:291`): blocked by design — `inNP` exposes an
  opaque `FlatTM`, no `Cmd` recoverable. Fix = make framework `inNP`/`inTimePoly`
  layer-native (carry a `DecidesLang`), then it collapses to `red_inNP_of_lang`.
  Deep S3-migration item; design with ROADMAP step 2.

---

## Proven, reusable — do not re-derive

The op builds below are templates; the helper stacks are axiom-clean.

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
