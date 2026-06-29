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

> **Most recent session (2026-06-29, TOP-DOWN, CliqueRelTM): ✅ the verifier
> PROGRAM is now CONCRETE + the structural `DecidesLang` fields are PROVEN.**
> `cliqueRelCmd` (was `sorry`) is the probe-validated 5-check FlatClique verifier
> transcribed into the DSL (`Deciders/CliqueRelTM.lean`), built only from the proven
> trio-free ops, and `usesBelow`/`noConsLen`/`allOpsSupported` are PROVEN &
> axiom-clean (joining the already-proven encoding fields). **Remaining CliqueRel
> sorries: just `decides` + `cost_bound`** (top-down Task 1 below). ⚠ **Risk-based
> finding (the prior "pure EvalCnf grind" framing understated this):** two patterns
> here are NOT in the EvalCnf template — (1) **unary `<`** (checks 1–2 need a strict
> order test, but the only comparison op is `eqBit`/equality), built as the lockstep
> gadget `ltBit`, design `#eval`-validated in the new `probes/CliqueLtProbe.lean`
> (agrees with `<` over a 7×7 grid); (2) **loop-counter reads** (`Nodup` reads the
> unary `forBnd` counters to skip the diagonal `i=j`; EvalCnf never reads a
> counter). Both are sound and shallow but each needs its own fold-invariant lemma
> in `decides` — budget for them. The clique check is also **loop-nest depth 4**
> (vs EvalCnf's 3). **Recommended next: continue TOP-DOWN on CliqueRel `decides`**
> (low structural risk now the program is fixed). Bottom-up remains BLOCKED on the
> encoding-design decision (unchanged — see step 2).
>
> **Prior finding still open (2026-06-29, BOTTOM-UP): the unary product migration as
> designed is SIZE-UNSOUND.** The bit-level product encoding
> `enc(x,y) = replicate |enc x| 1 ++ [0] ++ enc x ++ enc y` **violates the
> `LangEncodable.enc_size` contract** (`(enc x).length ≤ 2·size x + 1`,
> `PolyTime.lean:572`): the unary prefix doubles `|enc x|` per nesting level
> (depth-`d`: `|enc| = 2^d·(m+1)−1` while `encodable.size = m+d`), so the generic
> instance's obligation `B(a+b+1) ≥ 2·B(a)+B(b)` has **no polynomial solution** — the
> field is *false*, the generic instance cannot exist. Machine-checked, axiom-free:
> `probes/UnaryProductSizeProbe.lean`. **The bottom-up trio/product migration is
> BLOCKED pending an encoding-design decision (owner-level — touches `enc_size`/S3);
> see step 2.**

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
migration, which is now ⚠ BLOCKED** (the 2026-06-28 design is size-unsound — see
step 2 below). These three are **off the live `sat_NP` path** (isolated by the
Route-A wall), so they are *not* required for the in-NP half; finishing them only
buys Route B (drop the wall — cosmetic).

> **Concrete next BOTTOM-UP action (no owner sign-off needed — it is analysis, and
> may render the whole migration moot):** scope **option (B)** of step 2 — audit the
> *future* S3 reduction chain (the sound-tail reductions as `Cmd`s) and determine
> whether any of them actually needs the *generic* `LangEncodable (X × Y)` product
> trio, or whether each can use a bespoke bit-level free `encodeIn` the way the live
> `evalCnfCmd`/`cliqueRelCmd` do (neither uses the trio). If none needs it, the
> trio/product migration is **unnecessary**, the Route-A wall stays permanently, and
> bottom-up's remaining work is documentation + deleting dead scaffolding. Only if a
> generic bit-level canonical product is genuinely required does the (A) binary/Elias
> length-prefix redesign (owner decision) become necessary.

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

### 2. Unary migration — **⚠ BLOCKED: size-unsound as designed (2026-06-29); needs an encoding-design decision before any code**
**The 2026-06-28 design is wrong.** The bit-level product encoding
`enc(x,y) = replicate |enc x| 1 ++ [0] ++ enc x ++ enc y` is **exponential-size
under nested products** (`probes/UnaryProductSizeProbe.lean`, machine-checked):
the unary prefix has length `|enc x|`, so `|enc(x,y)| = 2·|enc x| + 1 + |enc y|` —
the first component **doubles per nesting level**. The generic `LangEncodable
(X × Y)` instance must prove `enc_size : (enc x).length ≤ 2·size x + 1`
(`PolyTime.lean:572`), which needs `B(a+b+1) ≥ 2·B(a)+B(b)`; that recurrence has
only **exponential** solutions, so **no polynomial `B` works** — the field is
*false*, the instance cannot exist. (Old size-tight encoding `|enc x| :: (enc x ++
enc y)` satisfies it but is not `BitState` — the cell holds the *value* `|enc x|`.)

**Why this blocks the whole bottom-up critical path.** Finishing the trio ops
(step 3 → Route B) requires restating `consLen` to a `BitState`-preserving form;
that restatement (and the trio count-by-length restatement) **breaks
`swapCmd`/`mapFstCmd`** (their only consumers), and re-proving those needs a
bit-level *and* size-sound *and* generic product encoding — which the above shows
cannot use a unary prefix. So: **no green increment is possible until the encoding
is redesigned.** `extractLeadingOnes` (step 2a, `ExtractOnes.lean`, proven) reads a
*unary* prefix and is only reusable if a redesign keeps one.

**Fundamental constraint.** Bit-level + polynomial-size + generic-nestable is
*unachievable with any inline self-delimiting prefix* (unary, continuation-bit
interleave, bit-doubling escape all cost `Ω(|enc x|)` and compound). The only
`O(log)`-overhead bit-level option is a **binary length prefix**.

**Redesign options (owner decision — both change the documented S3 plan):**
- **(A) Binary/Elias-γ length prefix + loosen `enc_size` to a polynomial.**
  `enc(x,y) = eliasγ(|enc x|) ++ enc x ++ enc y` (self-delimiting, bit-level,
  `O(log)` overhead → no compounding). Forces: (i) `LangEncodable.enc_size` from the
  tight `2·size+1` to a **quadratic** (a linear bound still fails — the `log` term;
  a quadratic closes; downstream only needs `inOPoly`/`monotonic`, so the ripple
  through `size_encodeState`/`comp`/witness cost-bounds is mechanical but wide); and
  (ii) a runtime **binary→unary** count gadget (replaces `extractLeadingOnes`) so the
  restated count-by-length trio can loop, plus a `consLen` that *writes* an Elias-γ
  prefix. Self-contained and fully general, but sizeable (bigger than the old
  estimate). **Audit `enc_size`'s consumers first** before committing.
- **(B) Decouple — don't make the canonical product bit-level at all.** `sat_NP` is
  already sorry-free (Route A) via the **free `DecidesLang` path with a bespoke
  bit-level `encodeIn`** (EvalCnf-style), *not* a canonical `LangEncodable` product.
  Recommendation: build the future S3 reduction chain the same way (bespoke bit-level
  free encodings + loop/concat repackaging), leaving the canonical `swap`/`mapFst`
  `enc_bit` as documented residuals and keeping the Route-A wall permanently. Then
  the trio/product migration may be **unnecessary** — verify whether any live S3
  reduction actually needs the generic trio (EvalCnf needs none). Lowest-risk;
  matches the working live architecture; defers/avoids the encoding redesign.

**Recommended:** investigate **(B)** first (cheap to scope: does the S3 chain need
the generic trio? if not, the whole migration is moot and the wall stays). Pursue
**(A)** only if a generic bit-level canonical product is genuinely required.

### 3. `takeAt` / `dropAt` / `consLen` TM gadgets (bottom-up; **gated on step 2's redesign** — the actual op-soundness deliverable)
*Only reachable once step 2's encoding redesign lands and the trio `Op.eval` is
restated.* Each is a **counted loop** reusing proven patterns: the unary `lenReg`/`lenSrc` is a
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
- **★ CliqueRelTM — finish `decides` + `cost_bound`** (`Deciders/CliqueRelTM.lean`).
  **2026-06-29: the program + 3 structural fields + 4 encoding fields are DONE &
  axiom-clean.** Only two `DecidesLang` fields remain `sorry`:
  - **`decides`** — `Cmd.decides cliqueRelCmd cliqueRelEncode (cliqueRel …)`. The
    program is `appendOne OUTPUT ⨾ checkWf ⨾ checkOfType ⨾ checkLen ⨾ checkNodup ⨾
    checkClique` (each a named `def`). Prove a `*_run` contract per check (output bit
    = the check's truth value, frame = OUTPUT + that check's scratch) then AND them:
    `OUTPUT` starts `[1]`, each check only ever *rejects* (sets `[0]`), so the final
    bit is the conjunction. Replicate the EvalCnf template (probe→per-iteration
    step-lemma→fold invariant via `Cmd.foldlState_range_induct`). **Build the
    reusable leaf lemmas first** (each used by several checks):
    - `readNum_run` — one terminated unary block off a stream into `dst`
      (`= replicate v 1`), stream loses the block. Invariant = `EvalCnfCmd.varExtractBody`
      (an `IN_BLOCK` flag fold); the parser automaton is the only new fold.
    - `ltBit_run` — **NEW vs EvalCnf** (`ltBit dst A B`): `dst = [if a<b then 1 else 0]`.
      Lockstep-consume invariant over `min`-truncation; design validated in
      `probes/CliqueLtProbe.lean`. Spec: after `|A|` steps `a<b ⇔ LT_A=[] ∧ LT_B≠[]`.
    - `memberEdge_run` — `FOUND = [if (a,b)∈edges then 1 else 0]`; this is exactly
      `EvalCnfCmd.memberCheck` with TWO unary `eqBit`s per edge.
    Then `checkWf`/`checkOfType` = a `forBnd` of (readNum ⨾ ltBit); `checkLen` = one
    `eqBit`; `checkNodup` = a double `forBnd` reading the **unary loop counters**
    `IDX1`/`IDX2` to skip `i=j` (**also NEW vs EvalCnf** — needs a counter-value fact
    from the `forBnd` toolkit; the counter is `replicate i 1` at iteration `i`);
    `checkClique` = depth-4 (outer/inner `forBnd` + `memberEdge`).
  - **`cost_bound`** — `cliqueRelCmd.cost (cliqueRelEncode x) ≤ timeBound (size x)`
    (`200000·(n+1)^4`, already quartic). Per-loop `Cmd.cost_forBnd_le` with a uniform
    per-iteration bound (mirror `evalCnfCmd_cost_bound`); the depth-4 clique nest is
    the dominant term — confirm degree ≤ 4 against the budget, bump the `200000`
    constant if needed (downstream only needs `inOPoly`/`monotonic`).
  Closing both makes `FlatClique`'s in-NP half axiom-clean (the trio-free
  `allOpsSupported`-wall win, for free). Gates `FlatClique_in_NP → Clique_complete`.
  **Recommended next top-down** — the program is fixed, so this is invariant grind;
  the only structural unknowns (`ltBit`/counter-read) are isolated leaf lemmas.
- **Framework `red_inNP`** (`NP.lean:291`) / **S3 migration**: blocked by design —
  `inNP` exposes an opaque `FlatTM`, no `Cmd` recoverable. Fix = make framework
  `inNP`/`inTimePoly` layer-native (carry a `DecidesLang`), then it collapses to
  `red_inNP_of_lang`. Deep S3-migration item; design with ROADMAP step 2. Higher
  structural risk; do CliqueRelTM first.

---

## Proven, reusable — do not re-derive

The op builds below are templates; the helper stacks are axiom-clean.

- **`extractLeadingOnes` (unary-migration step 2a) is PROVEN** —
  `Lang/ExtractOnes.lean`, axiom-clean. Recovers the unary length prefix
  `L = leadingOnes src` as `replicate L 1` in `dst`, via a `forBnd` DONE-flag fold
  invariant (template: `EvalCnfCmd.memberCheck`). `extractLeadingOnes_get_dst` +
  `_usesBelow`. The unpacking primitive `swap`/`mapFst`/`mapSnd` need in step 2d.
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
  assembly (`evalCnfDecidesLang`). **The template for CliqueRel** (probe→step→fold
  invariant→`cost_forBnd_le`; structural fields via full `simp` over the op leaves —
  NB: full `simp` with the register `def`s, not `simp only … decide`; `decide` fails
  `Decidable`-synthesis on the larger checks' conjunctions).
- **CliqueRel verifier (TOP-DOWN) — program CONCRETE, structural fields PROVEN**
  (`Deciders/CliqueRelTM.lean`, 2026-06-29). `cliqueRelCmd` + the 5 check `def`s
  (`checkWf`/`checkOfType`/`checkLen`/`checkNodup`/`checkClique` + `memberEdge`) +
  helpers (`readNum`/`ltBit`/`cSkip`/`cReject`) are concrete & trio-free;
  `cliqueRelCmd_usesBelow`/`_noConsLen`/`_allOpsSupported` + the 4 encoding fields are
  PROVEN & axiom-clean. Probes: `CliqueRelProbe` (algorithm), `CliqueLtProbe` (the
  unary-`<` lockstep gadget). Only `decides`/`cost_bound` remain (top-down Task 1).
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
