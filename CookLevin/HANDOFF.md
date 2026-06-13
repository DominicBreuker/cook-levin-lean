# Handoff — the computable layer / compiler (Risk C2)

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). **This file is the working plan for the compiler
(Risk C2)** — the one obligation the whole NP-completeness bridge sits on.

We work **multi-session in two alternating work streams**. At the start of each
session the owner says **`bottom-up`** or **`top-down`**:

- **Bottom-up** — build the gadgets/lemmas the contracts need (the 7 stub ops,
  the loop/branch machines), iterating toward the final proofs.
- **Top-down** — work on the final assembly, *design* its proofs, create
  supporting lemmas with `sorry` (when reasonably provable), and **surface gaps
  early** so we don't waste effort on code that must be discarded.

The two streams **share one interface** — the per-fragment *physical-residue
contracts* and the bridge that consumes them — and meet in the middle there.
Keep both stream sections below concrete and forward-looking.

---

## The bigger picture (read once)

We are proving `theorem CookLevin : NPcomplete SAT`, real and unconditional.
NP-hardness is transported along a chain of poly-time reductions whose **tail**
(`FlatTCC → … → SAT`) is real, done mathematics. The remaining work routes through
one device: **the computable layer** — a tiny structured while-language (`Cmd`/`Op`
with explicit **cost** semantics) compiled **once** to a single-tape `FlatTM`
(`Compile`). Every verifier and reduction is then a short DSL program.

This is **Risk C2**. The live `sat_NP : inNP SAT` and the framework bridges all
reduce to discharging the compiler's physical run contract plus the leaf gadgets.

**The live dependency chain `sat_NP` actually walks (top to bottom):**
```
sat_NP (EvalCnfTM.lean)
  → inTimePolyTM_evalCnf → inTimePolyLang_to_inTimePoly      (PolyTime.lean; ✅ PROVEN — reduces to
                                                               DecidesLang.toInTimePoly)
       → DecidesLang.toInTimePoly / .toDecidesBy (free enc.)  (PolyTime.lean; ✅ PROVEN — runtime-padded,
                                                               sorry only via the pinned gadgets below)
            → Compile.paddedBitDecider_run                    (Compile.lean ~11257; ✅ PROVEN, no k ≤ s.length)
                 → Compile.bitDecider_run                     (Compile.lean ~10415; physStepBudget)
                      → Compile_run_physical_residue          (Compile.lean ~10358; PROVEN from the assembly,
                                                               sorry only via the leaf gadgets below)
       evalCnfDecidesLang : DecidesLang …                     (EvalCnfTM.lean; ✅ COMPLETE & AXIOM-CLEAN
                                                               (2026-06-10): the verifier Cmd, its inner
                                                               bodies, and ALL contracts are PROVEN; budget
                                                               quartic 200000·(n+1)^4; regBound=16)
REAL REMAINING MATH under the assembly:
  padRegsTM_run / _traj   (Compile.lean ~11116; ✅ PROVEN, sorry-free — the WALL gadget
                           is COMPLETE)
  compileOp_sound_physical_residue   (Compile.lean ~12300 statement; **7/12 ops FULLY
                           PROVEN** (appendOne/appendZero/clear/nonEmpty/head/copy/
                           **tail** — the tail stack `tailLoop_run → tailBranch_run →
                           opTailSelf_run_done/_delete + opTail_run` completed &
                           axiom-clean 2026-06-12c); 5 ops still raw SORRY
                           (eqBit/concat/takeAt/dropAt/consLen))
  compileIfBit_sound_physical_residue  (✅ PROVEN —
                           real compileTestBit tester + branchCompose + joinTwoHalts)
  compileForBnd_sound_physical_residue (SORRY — interface RE-PINNED 2026-06-11; the
                           per-iteration chain `forBndIterate_run`, the loop machine
                           `forBndBodyTM`/`forBndLoopTM` + structural lemmas, BOTH
                           `loopTM` contracts (`forBndBody_done_run` + `_iterate_run`),
                           all five fold invariants + the **fold-invariant induction
                           `forBndLoop_invariant`**, AND the **tightened per-iteration
                           budgets** (`|K2|`-explicit, so the loop sum closes) are PROVEN
                           & axiom-clean (2026-06-13c). Remaining: the ASSEMBLY — the
                           `.choose` loop run via `loopTM_run` + the entry `opCopy`/exit
                           `opClear` wiring — done inside `compileForBnd_sound` after the
                           def-reordering. THE bottom-up task — see BOTTOM-UP task 1.)
```
Both the **canonical** path (`DecidesLang'` / `inNPLang_to_inNP`) and the **free/live**
path (`DecidesLang` / `inTimePolyLang_to_inTimePoly`) are now assembled and bridge the
same `paddedBitDecider_run` → `bitDecider_run`. **The decider half's only remaining
sorrys are the pinned compiler gadgets above** — the verifier (EvalCnf) layer is done.

---

## ⚠ The invariant: `BitState` — LOCKED, do not revisit

The compiled machine has a **fixed 4-symbol alphabet** (`sig = 4`). `encodeTape`
shifts each register cell `+1` (`0→1`, `1→2`), `0` separates registers, `3`
terminates/anchors. A cell `≥ 2` shifts to `≥ 3` and collides with the terminator,
so **every state touching the tape must be `Compile.BitState`** (all cells `∈ {0,1}`,
`Compile.lean:1708`). Numbers are therefore **UNARY** (`enc n = replicate n 1`).
Sound for the size law because `encodable.size Nat = id`: unary length `= n`.
`sig=4`/`BitState`/Option B′ is **owner-settled**; no further design sign-off needed.

---

## ★★ THE WALL — RESOLVED on BOTH bridges (2026-06-07).

**The problem (for reference).** `Compile_run_physical_residue` carries
`huses : Cmd.UsesBelow c k` and **`hk : k ≤ s.length`** — its per-op gadgets assume
the registers they touch already exist on the tape (`Op.inBounds`: gadgets navigate
by counting `0`-separators). The decider's input tape is narrow while composed
programs touch `regBound > 1` registers, so `hk` was unsatisfiable.

**The resolution — runtime tape-padding.** `Compile.padRegsTM k` grows the tape
*during the run*: `encodeTape s → encodeTape (s ++ replicate k [])` (width `≥ k`).
Empty pad registers leave `c.eval` unchanged (`Cmd.eval_agree`/`cost_agree`), and the
*input* encoding is untouched. Composed before the decider
(`Compile.paddedBitDeciderTM := padRegsTM ⨾ bitDeciderTM`), it discharges
`k ≤ wide.length` for the inner `bitDecider_run`. `Compile.paddedBitDecider_run` is
**PROVEN** with **no `k ≤ s.length`**.

**Both bridges are now assembled on it:**
- **Canonical** (`DecidesLang'.toDecidesBy`/`toInTimePoly`) — tight single-register
  input, budget `DecidesLang'.padTimeBound`.
- **Free / live** (`DecidesLang.toDecidesBy`/`toInTimePoly`, what `sat_NP` walks) —
  multi-register `encodeIn`, budget `DecidesLang.padTimeBound`. The `DecidesLang`
  structure now carries `regBound`/`usesBelow`/`width_le`/`noConsLen`;
  `inTimePolyLang_to_inTimePoly` is **PROVEN** (reduces to `DecidesLang.toInTimePoly`).

**OWNER DECISION (settled this session) — `DecidesBy.encode_size` is now per-decider
POLYNOMIAL.** The old globally-fixed linear `2·size+4` forbade the multi-register
`EvalCnfCmd.encodeState` (`≤ 5·size+20`). It was loosened not to per-decider *linear*
but to per-decider **polynomial**: `DecidesBy` now carries
`encodeBound : Nat → Nat` + `encodeBound_poly : inOPoly` + `encodeBound_mono`, with
`encode_size : (encode x).length ≤ encodeBound (size x)`. **Why polynomial, not
linear:** poly-size-encoding is the principled complexity-theory notion (poly encode
+ poly *time* = faithful); it does not add vacuity (the time bound is still
`poly(size x)`; `encode` being an arbitrary function is a *separate* pre-existing
weakness); and it is **future-proof** — the endgame compiles the whole reduction
chain / S1 tableau to `Cmd`s, whose encodings may be super-linear, so linear would
force a *second* framework change later. The ripple was clean (monotonicity discharges
`proj_left` + the product lift). The canonical layer keeps the linear instance
`encodeBound n = 2·n+4`; the free path uses `costBound n + regBound + 2`. **Do not
revisit — polynomial is the final boundary.**

**The remaining pinned obligations** (now identical for both bridges, all BOTTOM-UP):
✅ `Compile.padRegsTM` is **DONE**; ✅ `evalCnfDecidesLang` is **DONE & axiom-clean**
(2026-06-10 — verifier Cmds + all contracts proven). What's left under the decider
bridges is just the **5 leaf ops + 1 combinator** (`compileOp_…` for `eqBit`/`concat`/
`takeAt`/`dropAt`/`consLen`, plus `compileForBnd_sound_physical_residue`) — see the
stream sections. The LIVE path needs only **`eqBit` + the `forBnd` combinator**.

---

## ✅ What this session (2026-06-13c, bottom-up) did — **the ITERATE contract, the complete fold-invariant layer, and the BUDGET FIX**

**`compileForBnd` now has every per-iteration and fold-level building block its
loop run needs, plus the budget tightened so the loop sum closes.** All
axiom-clean, build green (3358 jobs). What's left is the *assembly* (the loop run
+ entry/exit wiring), which intertwines with `forBnd.cost`/`eval` and so belongs
inside `compileForBnd_sound` after the def-wiring (BOTTOM-UP task 1).

1. **`Compile.forBndBody_iterate_run`** (Compile.lean ~15580) — the `loopTM_run`
   `h_iter` contract (`K1=sb` nonempty ⇒ navigate-content → `forBndContentTM`
   rewind+`forBndIterate` → land at `exitLoop` on `forBndIterateState …` + W-inv).
   Mirrors `clearBody_delete_run`; the content M₂ slot is `forBndContentTM`, so
   `h_run2`/`h_traj2` come from `composeFlatTM_run`/`composeFlatTM_no_early_halt`
   of `rewindToStart_run` + `forBndIterate_run`.
2. **`Compile.forBndIterateState_{get_sb, get_sb1, scratch, length_ge, bitState}`**
   + **`Compile.forBndLoop_invariant`** (Compile.lean ~15040–15250) — the fold
   invariants AND their `∀ i ≤ iters` induction along `A i =
   (forBndIterateState …)^[i] s`: `BitState`, scratch `≥ sb+2` empty, length
   `≥ sb+2+2·loopDepth`, **`|K1_i| = iters−i`** (counts down to the done branch),
   **`|K2_i| = i`** (K2 empty at entry + `get_sb1` appends `[1]` ⇒ `K2_i =
   replicate i 1`). This is the precondition-threading the loop run consumes.
3. **★ BUDGET FINDING + FIX (the key risk surfaced & resolved).** Summing
   `forBndIterate_run`'s **loose** `(G+2)` copy-cost factor over `iters`
   iterations gives `~iters·G³`, which **overdraws** `physStepBudget G
   (forBnd.cost)` once `iters > 8` (since `G ≥ forBnd.cost ≥ iters²`). **Fix:**
   keep the copy SOURCE length **`|K2_i| = (s.get (sb+1)).length`** explicit (do
   NOT bound it by `G`). Then the loop sum is `Σ_{i<iters}(|K2_i|+2) = Σ(i+2) ~
   iters²/2`, which fits comfortably under `physStepBudget`'s `8·iters²` headroom.
   Tightened both `forBndIterate_run` and `forBndBody_iterate_run` budgets to
   `(9G²+9G+30)·((s.get (sb+1)).length + 2) + physStepBudget G (body.cost …) + …`.

**Gotchas reconfirmed:** `sb counter : Var` opaque to `omega` (use `Nat.*`
lemmas or `simp only [Var] at *; omega`); the budget product
`(9*G*G+9*G+30)*(…)` must be `set`-abstracted before `omega` (whnf timeout).
After `set s1 := …`, the budget's `body.cost (s.set …)` displays as
`body.cost s1` — `set B := … (body.cost s1)`. `justRewindTM = scanLeftUntilTM
4 3` (defeq), `_exit=1`, `.states=3`, `.sig=4`.

---

## ✅ PROVEN, reusable — do not re-derive

- **`Compile.run_physical_residue_gen`** (Compile.lean ~10211) — the residue
  induction; `op`/`seq` cases proven, `ifBit`/`forBnd` dispatch to the two
  combinators. W-invariant ① + `physStepBudget` budget ② + the **scratch
  invariant** (`∀ r ≥ k, s.get r = []`, preserved via `Cmd.eval_get_frame`;
  `k` generalized in the induction — forBnd recurses at `k+2`) all threaded.
  ⚠ `compileCmd`/`Compile`/`Compile.exit` take the scratch base first:
  `Compile k c`.
- **`physStepBudget G cost = (9G²+9G+33)·(8·cost+8) + cost`** + `_seq` (exact
  superadditivity) / `_mono` / `_poly` (cubic diagonal, const 817) — the
  composable budget. **The only correct budget shape; 8 units/cost-item is
  load-bearing for forBnd bookkeeping — do not re-tighten.**
- **`Compile.bitDecider_run`** — decider boundary, now `physStepBudget`. Sorry-free
  except transitively via the leaf gadgets.
- **`Compile.paddedBitDecider_run`** — the WALL resolution: pad-then-decide on a
  **narrow** input, **no `k ≤ s.length`**. Proven from the `padRegsTM` interface +
  `bitDecider_run`. Pads to `k + 2·c.loopDepth` (program frame + compiler scratch)
  and carries `hwle : s.length ≤ k` (from `width_le` at the bridges). Plus the
  `*_append_replicate_nil` padding bookkeeping + `Compile.get_of_length_le`
  (sorry-free).
- **Both decider bridges** (PolyTime.lean), sorry-free as written (transitive sorrys =
  the pinned gadgets only): canonical `DecidesLang'.{padTimeBound,budget_ge,toDecidesBy,
  toInTimePoly}` + `inNPLang_to_inNP`; free/live `DecidesLang.{padTimeBound,budget_ge,
  toDecidesBy,toInTimePoly}` + `inTimePolyLang_to_inTimePoly`. Both consume
  `paddedBitDecider_run`. `inOPoly_of_le` (pointwise domination) helper (now upstream).
- **★ `Compile.paddedComputeTM` / `Compile.paddedCompute_run`** (Compile.lean, end) — the
  **function-side WALL resolution** (analogue of `paddedBitDecider_run`; keeps the full
  output tape). PROVEN sorry-free from the `padRegsTM` interface + `Compile_run_physical_
  residue`. Budget `padBudget k s + 1 + physStepBudget G (c.cost s)`.
- **The REDUCTION bridge retargeted** (PolyTime.lean): `PolyTimeComputableLang.{padTimeBound,
  budget_ge,toFrameworkWitness'}` now consume `paddedCompute_run` (NOT `Compile_sound`),
  sorry-free as written. `PolyTimeComputableLang` carries the WALL fields
  (`regBound`/`usesBelow`/`width_le`/`noConsLen`/`decode_agree`); `toLang` populates them.
  ⇒ `Compile_sound` / `Compile_run_physical` / `Compile_polyBound` (overhead budget) are
  **DEAD/superseded — do not attempt to prove**.
- **Layer composition + NP-routing CLOSED** (PolyTime.lean): `PolyTimeComputableLang'.comp`
  (intra-layer, sorry-free) + `PolyTimeComputableLang.comp` (`(Wg.comp Wh).toLang`, bridges
  to the free witness; sorry only via pinned `c_noConsLen`) + `red_inNPLang` +
  `inNPLang_to_inNP` = `red_inNP_of_lang` (framework `inNP P` from a canonical layer
  reduction + `inNPLang Q`). **The free `comp` / `red_inNP_via_lang` are gone** (unneeded:
  the chain composes via `reducesPolyMO_transitive`). `comp_computes_of_bridge` retained as
  the documented free-encoding gap. **Do not re-introduce a free `comp`.**
- **`DecidesBy.encode_size` is per-decider polynomial** (`encodeBound`+`_poly`+`_mono`);
  all constructors migrated. **Settled — do not re-tighten.**
- **★ EvalCnf UNARY encoding (LIVE `sat_NP`) — DONE (2026-06-09).** `EvalCnfCmd.encodeState`
  is bit-level/self-delimiting (`{0,1}` only). Proven & axiom-clean: the BitState chain
  `encodeLit_bit`/`encodeClause_bit`/`encodeCnf_bit`/`encodeAssgn_bit`/`encodeState_bit`
  (⇒ `evalCnfDecidesLang.enc_bit`); the unary size accounting `encsize_list_foldr` /
  `foldl_encsize_acc` / `length_le_encsize` (generic `encodable.size`-of-list helpers) +
  `encodeCnf_length` (`≤5·size`) / `encodeAssgn_length_le` (`≤2·size`) /
  `encodeState_size_bound` (`≤6·size`) (⇒ `evalCnfDecidesLang.encodeIn_size`).
  **The live keystone scoping finding:** `evalCnfCmd` is genuinely
  `consLen`/`takeAt`/`dropAt`-free — those are canonical-toolkit only — so the live path did
  NOT need the (separate, larger) product/`consLen` unary migration.
- **★ EvalCnf VERIFIER (LIVE `sat_NP`) — FULLY DONE (2026-06-09/10).**
  `EvalCnfCmd.lean` is sorry-free: concrete bodies + all contracts + the assembly;
  `evalCnfDecidesLang` axiom-clean. Budget **quartic** (`timeBound = 200000·(n+1)^4` —
  cubic unprovable under uniform-bound loop accounting); frame **`regBound = 16`**.
  **Do not re-tighten either without an amortized `cost_forBnd` lemma / register audit.**
  Reusable for the next verifier (CliqueRelTM): the probe-then-prove method, the
  step-lemma/invariant/cost pattern (`mcStep`/`MCInv`/`LVInv`/`CInv`), `mcSkip` (unit-cost
  no-op), `replicate_one_eq_iff`, the `encodeLits` clause-block algebra, and the final
  product-atom arithmetic (`omega` over `m`/`m*m`/`m^k` atoms with explicit
  `Nat.mul_le_mul`/`pow_le_pow_left` bridge facts).
- **★ `Compile.padRegsTM` — the WALL gadget — is COMPLETE and sorry-free** (Compile.lean
  ~9540–10160): `k`-fold static composition (recursion on `k`) of `Compile.padBody`
  (= `stepRightTM ⨾ scanRightUntilTM 4 3 ⨾ insertCarryTM 0 ⨾ rewindFromEndTM 4 3`), base
  `Compile.haltTM` (trivial immediate-halt; trivializes `k=0`). **All interface lemmas
  proven** (`[propext, Classical.choice, Quot.sound]`): shape (`padRegsTM_{tapes,sig,
  states=1+16k,valid}`, `padRegsExit k = 16k`, `padRegsExit_lt`, `padRegsTM_halt`); run
  tower (`padInner34_run`, `padInner234_run`, `padBody_run` — `2·|tape|+7` steps/body);
  trajectory tower (`padInner34/234/padBody_no_early_halt`); and **`padRegsTM_run` /
  `padRegsTM_traj`** (the `k`-inductions via `composeFlatTM_run`/`_no_early_halt`).
  Reusable helpers: `haltTM*`, `encodeRegs_snoc_nil`, `run_succ`, `curSym_lt`,
  `scanRight_partial` (the previously-missing `scanRightUntilTM` trajectory),
  `padBody_tape_eq`, `padInner34/234_valid`. **`#eval`-validated** throughout.
- **`Compile.padBudget` is the EXACT recursive step count** (`0` base;
  `(2·|tape|+7)+1+padBudget k (s++[[]])` step) — **required** because `composeFlatTM_run`'s
  `h_traj1` needs the exit reached at *exactly* `t₁` (a loose upper bound makes the
  trajectory false once the machine idles at its halt/exit). `Compile.padBudget_le`
  bounds it by the clean poly `(k)·(2·size+2·s.length+2·k+12)`; both bridges' `budget_ge`
  use `padBudget_le`. The old `(k+1)·(size+s.length+k+2)` was **doubly wrong** (too small
  AND not exact) — `#eval`-proven.
- **`compileSeq_sound_physical_residue`** + `_traj` — residue `seq` composition.
- **Threading toolkit** (now all in `Compile.lean`): `Cmd.eval_preserves_BitState`,
  `Op.inBounds_of_UsesBelow`, `Cmd.eval_length_ge`/`_le`, `Cmd.size_eval_le`,
  `State.set_length_ge`, `BitState_set_pad`.
- **Move/branch/loop gadgets:** `moveRegionTM`/`moveRegion2TM` (single/dual FIFO
  transfer), `joinTwoHalts*`, `rewindBracket`/`_transport`, `bitReadTM`,
  `rewindTwoPhaseTM`, `deleteCarryTM`, `navigateAndTestTM`, `loopTM`(+`_run`/
  `_no_early_halt`), `loopBudget_le`. All axiom-clean. ⚠ The move gadgets are
  **residue-costly** (each pass appends `|src|` zeros to the residue) — **not**
  usable for the factor-1 W-invariant per-op contracts, and (2026-06-11b probe)
  **not even for the forBnd per-iteration counter copy** (joint growth `3i`/round
  overdraws the `iters²` lump from `iters = 2`). One-shot entry/exit bookkeeping
  only.
- **★ `compileTestBit` is REAL + `compileIfBit_sound_physical_residue` PROVEN**
  (2026-06-11): `exactOneOneTM`/`testBitInnerTM`/`testBitRawTM` + the packaged
  tester contracts `testBitReg_run_pos`/`_run_neg` (head-0 exit, tape unchanged,
  `T ≤ 3·L+12`) + the full residue `ifBit` combinator (TRUE branch through the
  demoted `haltT` bridge, FALSE through the kept `haltE`). Reusable patterns:
  read-only tester leaves can use the bare single-phase `justRewindTM` (block-end
  cells are always the register's own `0` delimiter, never `3`); join transport
  for a run ending at a *non-`h1`* kept halt = `joinTwoHalts_run_eq` + a
  `∀ k ≤ T, ≠ h2` argument (`testBitReg_run_pos`'s ending).
- **7/12 ops FULLY PROVEN** in `compileOp_sound_physical_residue`: `appendOne`,
  `appendZero`, `clear`, `nonEmpty`, `head`, **`copy`**, **`tail`** (each carries
  the W-invariant ①). The per-op budget is **cost-scaled**:
  `(9L²+9L+30)·(Op.cost+1)` — settled, do not revert.
- **★ `Compile.forBndIterate` + `forBndIterate_run` (2026-06-13)** — the `forBnd`
  per-iteration bookkeeping chain `copy cnt K2 ⨾ rbody ⨾ appendOne K2 ⨾ tail K1
  K1` as a `CompiledCmd` (built by `compileSeq` from the proven op gadgets;
  output `Compile.forBndIterateState`) + its **exact-residue run lemma**, PROVEN
  & axiom-clean: W-invariant ① (`+|K2|+body.cost+1`), residue-tolerant run +
  trajectory, cubic budget. Takes the **verbatim** `compileForBnd_sound`
  body contract `hbody`; reused by the loop induction (BOTTOM-UP task 1). Proof
  pattern = 3× `compileSeq_sound_physical_residue` + `_traj`; the W-telescope is
  `State.size_set_add` balances + `omega` (all atoms `Nat`; **no bare `sb`** —
  `Var` is opaque to `omega`, use `Nat.*` lemmas or `simp only [Var] at *`).
- **★ The `forBnd` loop MACHINE + BOTH `loopTM` contracts + the full fold layer
  (2026-06-13b/c)** — `Compile.forBndContentTM` (content branch =
  `justRewindTM`-rewind ⨾ `forBndIterate.M`), `Compile.forBndBodyTM`
  (`= branchComposeFlatTM (navigateAndTestTM sb) forBndContentTM justRewindTM …`,
  the `clearBodyRawTM` shape), `Compile.forBndLoopTM := loopTM forBndBodyTM
  exitDone exitLoop` + the FULL structural-lemma family; the **DONE** contract
  `Compile.forBndBody_done_run` AND the **ITERATE** contract
  `Compile.forBndBody_iterate_run` (both `|K2|`-explicit budgets — the loop sum
  closes); the five fold invariants `Compile.forBndIterateState_{get_sb, get_sb1,
  scratch, length_ge, bitState}` AND their `∀ i ≤ iters` induction
  `Compile.forBndLoop_invariant` (gives `BitState`/scratch/length/`|K1_i|=iters−i`/
  `|K2_i|=i` along `A i = (forBndIterateState …)^[i] s`). All axiom-clean,
  probe-validated. **What remains for `compileForBnd`:** the assembly (loop run via
  `loopTM_run` + entry/exit wiring) inside `compileForBnd_sound` — see BOTTOM-UP
  task 1.
- **★ The cursor-copy layer is COMPLETE (2026-06-12/12b)** — `Compile.opCopy`
  (REAL `CompiledCmd`, all invariants proven), its parts (`markBitTM`/
  `restoreStepTM`/`skipReadTM`, the staged pipeline `copyRet1TM`/
  `copyPipeA2..A5TM`/`copyPipeTM`, `copyContentRawTM`/`copyContentTM`/
  `copyBodyTM`/`copyLoopTM`/`copyRegionFullTM`, halt characterizations,
  `cursor_cell`), and the FULL run-lemma stack **PROVEN & axiom-clean**:
  `copyPipe_run`, `copyBody_run_iter`, `copyBody_run_done`, `copyLoop_run`,
  `opCopy_run` (exact residue `res ++ replicate |dst₀| 0`). Plus the
  **marked-tape toolkit** (`encodeTape_set_cell_res`, `markedTape_get_mark`/
  `_getElem_off`/`_take_drop`/`_interior_cell`, `appendAt_encTape_run`,
  `copyRet1_encTape_run`, `sym_bound_of_lt_four`, `appendAtTM_exit_eq`,
  `restoreStepTM_run`, the ≤2-valued `le_two_set` family,
  `encodeTape_append_getElem_last`) — reuse these for `eqBit`/`concat`;
  they make every cursor-style scan/mark/append proof mechanical.
- **★ The `tail` op layer is COMPLETE (2026-06-12c)** — `Compile.opTail`
  (REAL `CompiledCmd`, both `dst = src` and `dst ≠ src`), machines
  (`tailInPlaceTM` = joined `clearBodyRawTM` ⨾ `idTM`; `tailRegionFullTM` =
  clear ⨾ nav ⨾ `tailBranchTM` ⨾ rewind) + the full run-lemma stack PROVEN &
  axiom-clean: `skipReadTM_run_delim/_run_bit/_no_early_halt`, `tailLoop_run`
  (the cursor loop entered mid-register — ONE skipped cell), `tailBranch_run`,
  `opTailSelf_run_done/_delete`, `opTail_run` (exact residue
  `res ++ replicate |dst₀| 0`). Plus the **compose-with-`idTM` halt-zeroing
  trick** for stray unreachable halts, and `copyLoopTM_exit_is_halt`/
  `copyLoopTM_halt_unique`/`clearBodyRawTM_sig/_tapes/_start`/`idTM_halt_unique`.

---

# ▶ TOP-DOWN work stream — next steps

You assemble final pieces and design their proofs; create `sorry` lemmas when
provable; surface gaps early.

✅ **The decider half's top-down AND verifier work is COMPLETE** (2026-06-10):
both bridges assembled, the WALL resolved, `encode_size` settled, layer
composition/NP-routing closed, and the EvalCnf verifier fully proven. Every
residual sorry on the `sat_NP` decider path AND the `⪯p`/`toFrameworkWitness'`
reduction path is a **compiler gadget**. The top-down frontier:

✅ **Task 1 (`compileForBnd` interface design) is DONE (2026-06-11b)** — see the
session block: scratch interface re-pinned, gen lemma threaded, probe green.
The build is UNGATED for bottom-up. New frontier:

1. **CliqueRelTM — replicate the EvalCnf pattern (highest standalone top-down value).**
   `Deciders/CliqueRelTM.lean` is still the pre-pattern skeleton: `cliqueRelCmd`/
   `cliqueRelEncode` are `sorry` **defs** and every witness field is a raw `sorry`
   (including `regBound`!). It gates `FlatClique_in_NP` → `Clique_complete` (a headline
   secondary theorem; NOT on `CookLevin`'s own path — `inNP_kSAT` routes via `red_inNP`
   + `sat_NP`). The EvalCnf template is now proven END-TO-END — encoding (unary/
   bit-level, reuse `encsize_list_foldr`/`length_le_encsize`), `enc_bit`/`encodeIn_size`/
   `width_le`, fixed `regBound`, pinned per-edge/per-vertex body contracts, assembly,
   AND the inner-body build+proof method (see the 2026-06-10 session block: probe
   first, step-lemma + invariant + `cost_forBnd_le`). Design with the two known
   findings from the start: uniform-bound cost accounting fixes the degree (expect
   one degree per loop nest level); be generous with scratch registers.
2. **Framework `red_inNP` (NP.lean:291) — layer-native `inNP` refinement.** The one genuine
   framework-side `sorry` for NP-routing (consumed by `inNP_kSAT`, hence on `CookLevin`'s
   path). It is **blocked by design**: `inNP Q` exposes only an opaque `FlatTM` decider
   (`inTimePoly`), from which no `Cmd` is recoverable, so the layer engine has nothing to
   precompose. The fix is to make the framework's `inNP`/`inTimePoly` **layer-native**
   (carry a `DecidesLang`), after which `red_inNP` collapses to the proven
   `red_inNP_of_lang`. Deep S3-migration item; design when the S3 retirement
   (ROADMAP step 2) is underway.
3. **(optional cleanup)** ✅ The dead `overhead`/exact-tape family is DELETED
   (2026-06-11b). Remaining doc scrubs: stale `Compile_sound`/`Compile_run_physical`
   references in PolyTime.lean/Compile.lean header comments, and the stale
   `≤ 5·size+20` encodeState size quoted in NP.lean/PolyTime.lean comments
   (the proven bound is `≤ 6·size`). Low priority.

# ▶ BOTTOM-UP work stream — next steps

You build the gadgets the (pinned) contracts need. Build green per item;
`#print axioms`-clean. Probe each machine end-to-end (`#eval`) before proving.

✅ "EvalCnf inner bodies" CLOSED (2026-06-10); ✅ `compileTestBit`/`ifBit`
combinator CLOSED (2026-06-11); ✅ the `copy`/`tail` ops CLOSED (2026-06-12b/c);
✅ the `forBnd` per-iteration chain CLOSED (2026-06-13: `forBndIterate_run`);
✅ the `forBnd` loop MACHINE + structural lemmas CLOSED (2026-06-13b);
✅ **BOTH `loopTM` contracts + all five fold invariants + the fold-invariant
induction `forBndLoop_invariant` + the BUDGET FIX CLOSED (2026-06-13c,
axiom-clean)** — only the loop-run ASSEMBLY remains (task 1).
Everything left bottom-up is TM-level compiler work in Compile.lean. Both the
decider half (`sat_NP`) and the reduction half (`⪯p`/`toFrameworkWitness'`) rest
on the SAME gadgets, so Tasks 1 + 2 close **both** halves of the live chain at
once. Remaining: the `forBnd` loop-run assembly, the `eqBit` op (+ the non-live
`concat`/`takeAt`/`dropAt`/`consLen`).

1. **`compileForBnd` — THE highest-value item. ALL per-iteration/fold building
   blocks DONE (2026-06-13b/c, axiom-clean): BOTH `loopTM` contracts (with
   `|K2|`-explicit budgets), the five fold invariants, `forBndLoop_invariant`, and
   the budget tightening. Remaining: the ASSEMBLY — the `.choose` loop run + the
   entry/exit wiring, done inside `compileForBnd_sound` after the def-reordering.**
   The pinned program is `copy K1 bnd ⨾ loop{test K1 ⨾ copy cnt K2 ⨾ rbody ⨾
   appendOne K2 ⨾ tail K1 K1} ⨾ clear K2` (`K1 = sb`, `K2 = sb + 1`; docstring at
   `compileForBnd` ~Compile.lean 2947). The loop body is
   `Compile.forBndBodyTM counter sb rbody`; its contracts are
   `Compile.forBndBody_{done,iterate}_run`. **⚠ Finding (this session): the loop
   run does NOT cleanly stand alone — its W-invariant and budget intertwine with
   `(forBnd …).cost`/`eval` and the `clear K2` step, so build it INSIDE
   `compileForBnd_sound` (after the def-wiring (c)), where those are in scope.**
   **Concrete remaining steps:**
   - **(c) def-reordering FIRST.** Move the machine DEFS
     (`forBndIterate`/`forBndContentTM`/`forBndBodyTM`/`forBndLoopTM` — NOT their
     run lemmas) above line 2947, then set `compileForBnd counter bnd sb rbody :=
     (opCopy sb bnd) ⨾ forBndLoopTM ⨾ (opClear (sb+1))` as a `CompiledCmd`
     (`composeFlatTM`, `joinTwoHalts`-demote stray halts as `opCopy`/`opTail` do).
     Rebuild everything (it touches `compileCmd`'s output value).
   - **(d) the loop run + assembly in `compileForBnd_sound_physical_residue`**
     (the SORRY, ~Compile.lean 15920). Structure: entry `opCopy_run` (`copy K1 bnd`,
     establishing `A 0` with `K1` = snapshot, `K2 = []`) → the `loopTM_run` loop →
     exit `clearRegionTM_run` (`clear K2`). For the loop:
     - **State fold** `A i = (forBndIterateState counter sb body)^[i] s0`,
       `iters = (s0.get sb).length`. `Compile.forBndLoop_invariant` (PROVEN) gives
       `BitState`/scratch/length/`|K1_i|=iters−i`/`|K2_i|=i` at every `i ≤ iters` —
       feed these to `forBndBody_iterate_run` (`i < iters`, K1 nonempty) and
       `forBndBody_done_run` (`i = iters`, K1 empty).
     - **Residue fold** `R i` via `.choose` of `forBndBody_iterate_run` at
       `(A i, R i)`, guarded by a `dite` on the bundled preconditions (use
       `Classical.propDecidable`); prove `∀ i ≤ iters, Pre (A i) (R i)` by a single
       induction (`Pre` = the invariant + `ValidResidue (R i)` + the per-iteration
       `hG`). `tIter i := (… ).choose` step count. **Mirror
       `clearRegionTM_run`** (Compile.lean ~5775, the analogous variable-length
       loop) for the `tIter`-via-`.choose` + `loopTM_run`/`loopTM_no_early_halt`
       wiring; the ONLY difference is `A`/`R` are folds (not closed forms).
     - **`T m := ([], 0, encodeTape (A (iters−m)) ++ R (iters−m))`**; `h_done` =
       `forBndBody_done_run` at `T 0`, `h_iter j` = `forBndBody_iterate_run` at
       `T(j+1)→T(j)`. `loopTM_run`/`_no_early_halt` close the loop run + trajectory.
     - **W-invariant**: the per-iteration W (`forBndBody_iterate_run`'s) telescopes
       to `State.size (A iters) + |R iters| ≤ State.size s0 + |R 0| + Σ_{i<iters}
       (|K2_i| + body.cost(A i .set cnt K2_i) + 1)`. With `|K2_i| = i` and
       `Cmd.eval_forBnd`/`cost_forBnd_le` (`K2_i = replicate i 1` ⇒ the semantic
       step matches), this ties `A iters` (minus the K2 scratch, cleared next) to
       `(forBnd …).eval s` and the sum to `(forBnd …).cost s`.
     - **Budget**: `loopBudget tIter tDone iters ≤ physStepBudget G (forBnd.cost)`.
       The per-iteration budget is now `|K2|`-explicit (`Σ(|K2_i|+2) = Σ(i+2) ~
       iters²/2`), so it fits under `physStepBudget`'s `8·iters²` headroom (the
       BUDGET FIX — see this session's block). Done branch ≤ `6L+12 ≤ 6G+12`.
   Expect ~1 session: (c) is mechanical-but-wide; (d) is the keystone, but every
   contract/invariant/budget it needs is now PROVEN — it is assembly, not
   structural unknowns.
2. **`eqBit` design + probe (then build).** `Op.cost eqBit = 1` ⇒ ZERO residue
   beyond clear's `|dst₀|` — read-only two-mark ping-pong (marks only ever sit
   on BITS, never delimiters): special-case empties via `navigateAndTest`
   pre-branches; both nonempty → mark src1's bit, rewind, navigate src2, mark
   its bit, compare in FSM (pipelines carry the bit pair); on match restore
   M2 + read-mark its next cell, scan to M1 (compile-time order picks the scan
   direction), restore + read-mark next, iterate; first mismatch/exhaustion
   decides; cleanup restores both marks (values carried in the pipeline
   branch), then `clear dst ⨾ append answer`. An exhausted side is never
   marked (delimiters unmarkable) — at most one round runs with an exhausted
   side, and it decides. PROBE FIRST (`CursorCopyProbe` pattern); fallback =
   owner-approved `Op.cost eqBit` bump (ripples into EvalCnf constants).
   Then `concat` (cursor machinery, cost `|src1|+|src2|+1` is generous), and
   last the value-as-length trio `takeAt`/`dropAt`/`consLen` (canonical
   toolkit only — gated on Task 3).
3. **Canonical product-toolkit unary migration** (separate from the live path; needed for
   S3 endgame, NOT for `sat_NP`). Restate `takeAt`/`dropAt`/`consLen` unary (count = the
   register's unary length, not `headD 0`); bump `consLen`'s `Op.cost`; re-lay the `Nat`/
   product/`List` canonical encodings bit-level (the product's single length-prefix cell →
   unary block) + `BitEncodable` instances; re-derive `swapCmd`/`mapFstCmd` correctness.
   After this, `consLen` preserves `BitState` and the `NoConsLen` side-conditions
   (`DecidesLang'.c_noConsLen` + `PolyTimeComputableLang'.c_noConsLen` +
   `DecidesLang.noConsLen`) are **dropped**. ⚠ This ripples to the proven product-toolkit
   `normalizes`/cost proofs — sizeable; schedule as its own batch.

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (`lake` is **not** on
  PATH; LSP/most MCP features can't find it). First build slow (~minutes); iterate a
  single module with `lake build Complexity.Lang.Compile` / `…PolyTime`. Commit per
  logical step, green. Headline module: `Complexity.NP.SAT.CookLevin`.
- **Probe** a built machine end-to-end *before* proving its run lemma:
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/x.lean` with
  `import Complexity.Lang.Compile`, `open Complexity.Lang`,
  `runFlatTM N M { state_idx := M.start, tapes := [([], 0, Compile.encodeTape s)] }`.
  Every gadget exits with its head on the trailing terminator — rewind-bracket.
- **Axiom-check** via a scratch file: `#print axioms <name>` — must show only
  `propext`/`Classical.choice`/`Quot.sound` for new sorry-free results.
- **Budget:** only `physStepBudget` composes. Never an `overhead`/`(·+1)²` shape.
- **`omega` hits `whnf`/`isDefEq` TIMEOUTS on product atoms multiplying
  two-atom sums** (e.g. `(regBound + 2·loopDepth + 1) * (4n + …)` — both factors
  non-literal). Root-caused 2026-06-11b with a /tmp minimal repro (not specific
  to any def). End such proofs with explicit `Nat.add_le_add` terms, or
  `generalize` the products first.
- **Append a BIT `b`** = `appendAtTM (b+1)`. `deleteCarryTM` deletes the cell **left
  of the head**; `navigateAndTestTM src` lands the head **on** src's first content.
- **`omega` can't see through `Var := Nat`** — root cause refined 2026-06-12b:
  it is the **goal's elaborated type**. A bare `show 13 + 3*dst = …` with
  `dst : Var` elaborates the `=`/`<` at type `Var` and omega bails; ascribe
  **`show (13 + 3*dst : Nat) = …`** and it works. **(2026-06-13 refinement)** a
  bare `sb : Var` *atom* (e.g. proving `sb + 1 < s.length` from `hlen : sb + … ≤
  s.length`) reports **"No usable constraints found"** — and `show (sb : Nat) …`
  does NOT help (the *hypothesis* still has the `Var` atom). Fix: **`simp only
  [Var] at *; omega`** (unfolds the abbrev everywhere; safe even with big hyps),
  OR derive the order facts with explicit `Nat.*` lemmas (`Nat.le_trans`/
  `Nat.lt_trans`/`Nat.ne_of_lt`/`Nat.lt_succ_self`). Note `(State.get s r).length`
  (an opaque `Nat` atom containing no *bare* `sb`) is fine for omega. Also: implicit-arg by-blocks
  (`composeFlatTM_run`'s `h_exit_lt` etc.) elaborate BEFORE the run argument
  pins `?exit` — pin it with the `show`. omega never splits `(l ++ r).length` —
  hand it `List.length_append` facts. `rw`'s rfl-extension closes `a ≤ a`, so a
  trailing `exact Nat.le_refl _` can die with "no goals". Record projections /
  `def`-constants need `show` of the reduced form first; `set x := e` hyps
  created *after* the `set` stay raw (convert with `rw [← hxdef]`).
  **Avoid nested `set`/`let` over `State.set`/
  `.get`** (`isDefEq` blows up ×8/level — flatten with `simp only [Cmd.eval_op, Op.eval]`).
  **`.get` mis-resolves on `State` literals** — write `State.get s r` explicitly.
  **Dependent `Fin`-index rewrites** (`rw` under `.get ⟨i, h⟩`) fail with
  "motive is not type correct" — route through `getElem?` +
  `List.getElem?_eq_getElem`/`Option.some_inj`.
- **`rcases h : e with …` substitutes `e` in the goal** (when `e` occurs there) —
  a later `rw [h]` then fails with "did not find occurrence"; just drop the `rw`.
  **`List.length_tail` takes the list implicitly.** **`decide` fails when the
  goal's type mentions free variables** even if the projection reduces
  (`{…cfg literal…}.state_idx ≠ 2`) — `show (0 : Nat) ≠ 2` first. **Scaling an
  opaque budget product** `Q·2 ≤ Q·(cost+1)` (cost non-literal) is beyond omega —
  use `Nat.mul_le_mul_left _ (by omega)`.
- **A polymorphic structure field over `encodeState` needs `∀ x : X`** (annotate the
  binder) or inference loops.
- **`Cmd`-level proof engineering** (EvalCnfCmd.lean patterns): compute register reads
  through `State.set`-chains with explicit `rw [State.get_set_ne _ _ _ _ (by decide), …,
  State.get_set_eq]` — count the chain depth per branch; one-shot `simp` stalls on the
  conditional `get_set_ne`. `Cmd.UsesBelow`/`NoConsLen` of a concrete program: full
  `simp [defs…, register defs…]` (plain `decide`/`omega` both fail on the `Var` defs).
  Final cost arithmetic: `omega` DOES handle opaque nonlinear atoms (`m*m`, `m^3`,
  `cost`-terms) if you hand it explicit bridge facts (`Nat.mul_le_mul`,
  `Nat.pow_le_pow_left`, `ring` expansions).
- Methodology: **skeleton-first, refine the highest-risk gap next, decompose
  `sorry`s don't elaborate them, probe before committing engineering, `def`+`sorry`
  over `axiom` (count = 0), build green between commits.**
