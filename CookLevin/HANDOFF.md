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
  compileForBnd_sound_physical_residue (✅ PROVEN & axiom-clean 2026-06-14 — the
                           forBnd counted loop is fully assembled & discharged.)
```
**The live `sat_NP` decider half now needs only ONE compiler gadget: `eqBit`.**
With `compileForBnd` proven, `evalCnfCmd`'s only remaining stub op is `eqBit`
(`evalCnfCmd` is `consLen`/`takeAt`/`dropAt`-free). Closing `eqBit` makes the
entire live decider chain (`sat_NP → … → Compile_run_physical_residue`)
**sorry-free** — the single highest-value bottom-up item. See BOTTOM-UP task 1.
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

## ✅ What the last session (2026-06-21, top-down) did — **the eqBit BUDGET FEASIBILITY GATE (top-down task 0a): re-validated; VERDICT = GREEN. Corrected the prior bottom-up RISK FINDING (it was over-pessimistic). Shipped a worst-case probe + a PROVEN arithmetic backbone (`probes/EqBitBudgetProbe.lean`, all theorems nlinarith-checked).**

Risk-based de-risking session. The prior bottom-up session flagged that the
`compareRegsTM` working tape is `L4 ≈ 3·op-L` and that the provable bounds sum to
`~133·op-L²` vs the const-72 ceiling `144·op-L²` — a fragile ~92% margin — and asked
for a feasibility re-validation BEFORE finishing the eqBit assembly. This session ran
that gate. **Result: the assembly is comfortably FEASIBLE; the alarm was a false
alarm.** No design change, no `Op.cost` bump.

### ★ VERDICT — GREENLIGHT the eqBit d2-iv assembly (prefix + top bounds + d1 wrapper).
Use **const-72** for the per-op contract (covers ALL eqBit inputs; free vs
`physStepBudget` — `72 = 8·9`, the discharge is termwise with `L ≤ G`). The current
`opBudgetLoosen` const-54 already suffices for *every case except* the fully-degenerate
`eqBit r r r` (a register compared to itself AND written to itself — off every real path).

### Two corrections to the prior finding (both machine-checked):
1. **`L4 < 2·op-L` when `src1 ≠ src2`** (every real program incl. the live EvalCnf
   path), **NOT `3·op-L`.** `L4 = op-L + |g1| + |g2| + 2`, and since `src1`/`src2`
   coexist in the same input `s`, `|g1|+|g2| ≤ State.size s = op-L − len − 2`. So
   `L4 ≤ 2·op-L` (measured ratio 1.87–1.90). `≈3·op-L` is reachable ONLY when
   `src1 = src2` (both scratch copies duplicate one giant register; measured up to 2.57,
   →3 as the register grows).
2. **The per-stage worst cases are MUTUALLY EXCLUSIVE.** A long match (loop
   `(matchLen+1)·24L4` expensive) forces short leftover suffixes (`c_i = g_i.drop
   matchLen`, cleanup cheap), and vice versa. Summing each stage's *independent* worst
   case (what the finding did → `133·op-L²`) double-counts; the JOINT worst is far
   smaller.

### Measured + PROVEN (`EqBitBudgetProbe.lean`; lift the theorems into `Compile.lean`):
- Real worst-case full `opEqBit` steps ≈ `12–13·op-L²` (~70% of the old `18·op-L²`).
- **`compareBudget_arith_fits54`** (distinct `src`): the TIGHT iteration-explicit stage
  sum fits **const-54 at ≤28%**; the fully-DECOUPLED honest bound (loop≤`|g1|`,
  cleanup≤`|g1|+|g2|` — the finding's over-counting method, but with the corrected `L4`)
  fits const-54 at **≤53%**.
- **`selfBudget_neqDst_54`** (`src1=src2≠dst`): fits **const-54** (constraint
  `l+dlen+2 ≤ op-L`).
- **`selfBudget_eqDst_72`** (`eqBit r r r`): fits **const-72** (constraint `l+3 ≤ op-L`,
  i.e. the register coexists on the tape). The ONLY case needing 72. ⚠ `l ≤ op-L`
  *alone* is too weak — the additive gadget overheads bust a tiny `op-L` ceiling; thread
  the coexistence `l+3 ≤ op-L` (always available: `op-L = State.size+len+2`, `len ≥ 1`).

### Concrete handoff to bottom-up (the proven arithmetic IS the backbone):
- **Lift `compareBudget_arith_fits54` + `selfBudget_eqDst_72` from the probe into
  `Compile.lean`** next to `opBudgetLoosen` for the top bound. Their hypotheses are
  exactly what the run lemmas supply: `matchLen ≤ |g_i|`, `c1+c2 ≤ l1+l2` (`length_drop`),
  `l1+l2+2 ≤ op-L` (`encodeTape_length` + `State.size`), `dlen ≤ op-L`. Each stage's
  budget is bounded by the uniform working tape `L4` (monotone in tape length).
- **Bump `opBudgetLoosen`/the contract `54 → 72`** (one line; free vs `physStepBudget`).
  Then **the cleanup TIGHTENING (old d2-iv step 1) is NICE-TO-HAVE, not a blocker**: even
  the COLLAPSED currently-proven cleanup `18L4²` + clear `9L4²` fits const-72 at ≤88% for
  `src1≠src2` (measured), and for `eqBit r r r` the cleanup is `c=0` = linear (collapsed
  is irrelevant there). Do the tightening only if cheap (it drops the margin 88%→28%,
  robustifying the final `nlinarith`).
- **Alternative to bumping:** keep const-54 and add a side-condition `src1 ≠ src2 ∨
  src1 ≠ dst` to the eqBit contract case if the witnesses guarantee it (the live EvalCnf
  `eqBit` uses distinct registers). But const-72 is simpler and free.

### Gotchas confirmed this session
- **The "independent per-stage worst-case sum" over-counts on a quadratic budget.** When
  validating a composed budget, compute the JOINT worst case (respect the constraints
  tying the stages: here `matchLen + |leftover| ≤ |operand|`, `Σ operands ≤ op-L`). The
  probe's `provableTight` (real matchLen/leftover) vs `provableDecoupled` (relaxed
  independently) makes the gap visible — measure both.
- **A correct-asymptotically budget can fail `nlinarith` at SMALL sizes** because the
  additive gadget-overhead constants (`+21`, `+45`, …) exceed a tiny `c·op-L²` ceiling.
  Fix by threading the *real* lower bound on `op-L` (here `op-L ≥ l + 3`, from
  `encodeTape_length`), not a loose `l ≤ op-L`.
- `nlinarith` for these sums needs the cross-term hints `l*opL ≤ opL*opL`
  (`Nat.mul_le_mul hl (Nat.le_refl opL)`) and `l*l ≤ opL*opL` (`Nat.mul_le_mul hl hl`),
  plus `Nat.zero_le` of every product atom. `Nat.zero_le (l*opL)` alone is useless (gives
  `≥0`, not the `≤opL²` bound needed).

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
  the W-invariant ①). The per-op contract budget is **cost-scaled and LOOSENED
  (2026-06-20d)**: `(54·L²+54·L+180)·(Op.cost+1)` (was `9·…`; the 7 proven ops keep
  their tight `9·…` internally and relax via **`Compile.opBudgetLoosen`**). The
  loosening is free against `physStepBudget` (8× headroom, `54 ≤ 72`) and gives the
  `eqBit` symbolic component-sum (`~60L²`) comfortable room — **do not re-tighten
  below the symbolic sum; can go up to `72` if a future op needs it** (see the
  2026-06-20d session block).
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
  probe-validated.
- **★ `compileForBnd_sound_physical_residue` is FULLY PROVEN & axiom-clean
  (2026-06-14)** — the forBnd counted loop is closed. `compileForBnd = compileSeq
  (opCopy sb bound) (compileSeq (forBndLoopCmd …) (opClear (sb+1)))`. Reusable
  parts (all axiom-clean): **`Compile.forBndLoop_eval`** (machine fold, K2-cleared,
  `= (forBnd).eval s`); **`Compile.forBndLoop_agree`** (`AgreeBelow`/`K2=replicate
  i 1`, extracted from `forBndLoop_eval`'s `key`); **`Compile.forBndLoop_{fold,run}`**
  (the loopTM run; W + budget as `Finset` sums over the fold states);
  **`Cmd.cost_forBnd_eq`** (cost as a `Finset` sum over pure fold states);
  **`Compile.{physStepBudget_sum_le,loopBudget_eq_sum,forBndBudget_arith}`** (the
  budget collapse via superadditivity). The contract now also carries
  `huses_body`/`hnc_body`/`hG` (gaps fixed — see this-session block). ⇒ The forBnd
  combinator in `run_physical_residue_gen` is sorry-free.
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
- **★ `Compile.iterTailsTM` / `Compile.iterTails_run` (2026-06-14c)** — the `eqBit`
  consume-loop **ITERATE leaf**: `opTail sc1 sc1 ⨾ opTail sc2 sc2` (delete both
  heads in place, entered at head 0) as a `composeFlatTM` of the proven
  `opTailSelf_run_delete`, with run lemma (exit `(opTail sc2).exit + (opTail sc1).M.states`,
  residue `++ [0,0]`). PROVEN & axiom-clean; the first proven piece of `compareRegsTM`
  (HANDOFF bottom-up task 1 d2a). Pattern: `composeFlatTM_run` threaded over two
  `opTailSelf_run_delete`s + the head-0 symbol bound (`encodeTape_get_zero`).
- **★ `Compile.opRewindToZero` / `opRewindToZero_run` (2026-06-15)** — the
  halt-unique single-exit "rewind interior head → leading sentinel" leaf
  (`joinTwoHalts justRewindTM 1 2`, demoting the stray boundary halt). Run lemma
  on `(left, head, 3 :: rest)` with `rest[0..head)` terminator-free (`<4`, `≠3`):
  `head+1` steps, demoted boundary never visited. **Use this wherever a branch
  body ends in a rewind** (`composeFlatTM` only zeroes its FIRST arg's halts).
- **★ `Compile.navTestRewindM` / `navTestRewindM_run_content` / `_run_delim`
  (2026-06-15)** — the clean 2-exit "test register emptiness, head restored to 0"
  tester (`branchComposeFlatTM (navigateAndTestTM sc) opRewindToZero opRewindToZero
  …`). Full structural family + both run lemmas (with both-exits no-early-halt
  trajectory). Reuse for the `eqBit` verdict (d2b: nest `navTestRewindM sc1` /
  `navTestRewindM sc2`) and the consume-loop testMachine's empty guards (d2a).
- **★ `Compile.branchComposeFlatTM_halt_only_M3two` (2026-06-15b)** — the 2-halt-`M₃`
  generalization of `branchComposeFlatTM_halt_only`. Keystone for nesting any 2-exit
  tester as the negative branch.
- **★ `Compile.branchComposeFlatTM_halt_only_M2two_M3two` (2026-06-15c)** — the
  both-branches-2-exit (4-halt) generalization. For `bitCompareM` / the loop body `B`,
  where each side branches MATCH/NOMATCH (resp. ITER/DONE).
- **★ `Compile.readBitRewindM sc` / `readBitRewindM_run` (2026-06-15c)** — the `eqBit`
  consume-loop **bit-read leaf**: clean 2-exit `BIT0`/`BIT1` tester reading `sc`'s first
  *bit* (not just emptiness), head restored to `0`, tape unchanged, for `sc` nonempty
  (`= joinTwoHalts (branchComposeFlatTM (navigateAndTestTM sc) opRewindToZero
  readRewindInnerM (delim) (content)) raw_b0 raw_dead`, the 2-exit reader as M₃). Full
  structural family + `readRewindInner_run` (the inner `bitReadTM`+`opRewindToZero` from
  the post-navigation head) + `readBitRewindM_run` (both bit cases + no-early-halt traj).
  **Used twice in `bitCompareM`.** Cell-value fact = the `moveContent_run` derivation;
  rewind reuses `navTestRewind_rewind_run`.
- **★ `Compile.bitCompareM sc1 sc2` / `bitCompareM_run` (2026-06-15d)** — the `eqBit`
  consume-loop **bit-compare leaf**: clean 2-exit MATCH/NOMATCH tester, MATCH iff the
  first bits of two NONEMPTY registers are equal, head restored to `0`, tape unchanged
  (`= joinTwoHalts (joinTwoHalts (branchComposeFlatTM (readBitRewindM sc1)
  (readBitRewindM sc2) (readBitRewindM sc2) (exit_b0 sc1) (exit_b1 sc1)) m00 m11) m01
  m10` — 4 raw halts merged to 2). Full structural family + `bitCompareM_run` (single
  `if a = b` lemma, 4 bit-cases + traj), via 3 reusable join-transport helpers
  (`_transport_kept`/`_transport_m11`/`_transport_m10`) + raw-run helper
  `bitCompareRawM_run`. **The d2a bit-compare core is done; plug it into `testMachine`.**
  See the double-`joinTwoHalts` reusable pattern in this session's block.
- **★ `Compile.branchComposeFlatTM_halt_only_M2two` (2026-06-15d)** — mirror of `_M3two`:
  positive `M₂` 2-exit + negative `M₃` halt-unique → 3 shifted halts. For the
  `testMachine` guards (2-exit tester positive, `idTM` negative).
- **★ `Compile.eqVerdictM` / `eqVerdictM_run_{neq_left,neq_right,eq}` (2026-06-15b)** —
  the `eqBit` verdict: a clean 2-exit "are BOTH `sc1` and `sc2` empty?" tester
  (`joinTwoHalts (branchComposeFlatTM (navTestRewindM sc1) idTM (navTestRewindM sc2)
  …) neqA neqB`), head restored to `0`, tape unchanged. Full structural family + the
  three input-case run lemmas (the neq-right case demonstrates the
  `joinTwoHalts_run_eq_weak` + `joinTwoHalts_step_to_h1` bridge for an outcome that
  lands on the demoted halt). The reusable nested-2-exit-tester recipe (see this
  session's block). Consumed by the `eqBit` (d1) wrapper / the `compareRegsTM` (d2)
  verdict stage.
- **★ `Compile.bothNonemptyM sc1 sc2` / `bothNonemptyM_run_{yes,no_left,no_right}`
  (2026-06-15e)** — clean 2-exit guard "are BOTH `sc1` and `sc2` nonempty?", head `0`,
  tape unchanged (`joinTwoHalts (branchComposeFlatTM (navTestRewindM sc1)
  (navTestRewindM sc2) idTM …) noA noB`; structural mirror of `eqVerdictM` with idTM in
  the NEGATIVE branch). Full structural family + 3 input-case run lemmas.
- **★ `Compile.testMachine sc1 sc2` / `testMachine_run_{iter,done_left,done_right,
  done_neq}` (2026-06-15e)** — the consume-loop body DECISION: clean 2-exit ITER/DONE,
  ITER iff both scratch regs nonempty AND first bits match, head `0`, tape unchanged
  (`joinTwoHalts (branchComposeFlatTM (bothNonemptyM sc1 sc2) (bitCompareM sc1 sc2) idTM
  exit_yes exit_no) done nomatch`). Full structural family (`halt_only` via `_M2two`) +
  the 4 input-case run lemmas — the body contracts `compareBodyTM` consumes.
- **★ `Compile.iterTailsTM` structural family + `iterTails_run` (+traj) (2026-06-16)** —
  the ITERATE leaf, with `iterTailsTM_exit`/`_exit_lt`/`_exit_is_halt` and the
  no-early-halt trajectory (needed by `loopTM`/`branchComposeFlatTM_run_pos`). ⚠ `loopTM`
  tolerates its stray composeFlatTM halt — no `joinTwoHalts` wrap.
- **★ `Compile.compareBodyTM sc1 sc2` / `compareBody_{iterate,done}_run` (2026-06-16)** —
  the consume-loop body `branchComposeFlatTM (testMachine) (iterTailsTM) idTM …`; full
  structural family (+ `compareBodyTM_exit{Loop,Done}_is_halt`) + the ITER contract
  (`_iterate_run`) and the generic-tape DONE contract (`_done_run`). The
  `loopTM_run`-body template (see this session's REUSABLE PATTERN).
- **★ Consume-loop semantics (2026-06-16)** — `Compile.matchLen` (iteration count),
  `matchLen_step` (per-iter matching heads), `matchLen_stop` (3 DONE cases),
  `consumeStep`/`consumeIter_spec` (state transform + closed-form `drop k` register
  contents, `BitState`/length preserved), `matchLen_drop_empty_iff` (equal ⟺ both
  suffixes empty — the d2 verdict's decision fact).
- **★ `Compile.compareLoopTM` / `compareLoop_run` (2026-06-16)** — `loopTM compareBodyTM
  exitDone exitLoop` + its run lemma (the d2a milestone): loop halts at
  `compareBodyTM.states` with `sc1`/`sc2` = their `matchLen`-dropped suffixes, residue
  `++ replicate (2·matchLen) 0`. ⚠ Step bound = the opaque `loopBudget tIter tDone n`
  (no closed form yet — d2 must bound it `O(L²)`). **The `eqBit` consume loop is closed;
  d2 (assemble `compareRegsTM`) + d1 (wrapper) remain.**
- **★ `Compile.growEmptyTM`/`growEmpty_run` + `growTwoEmptyM`/`growTwoEmpty_run`
  (2026-06-16b)** — the `eqBit` scratch-GROW gadget (Compile.lean, end). Forward insert
  (`growScanInsM`/`growInsertM` = `stepRight ⨾ scanRight ⨾ insertCarryTM 0`) bracketed by
  the two-phase rewind (`rewindBracket growInsertM 10`): from `encodeTape s ++ res`
  (head 0) → `encodeTape (s ++ [[]]) ++ res` (head 0), `O(L)`, residue unchanged;
  `growTwoEmpty` = two of these (`s ++ [[],[]]`). ⚠ single-phase rewind is WRONG with
  residue (insertCarry parks the head past the residue; a single left-scan stops at `3`).
- **★ `Compile.copyEmptyRawTM`/`copyEmpty_run` (2026-06-19)** — the `eqBit` (d2) copy
  stage (Compile.lean, end): head-`0`→head-`0` copy of `src` into an EMPTY register `dst`,
  `= opCopy` phases 2–4 (`navigateToRegTM ⨾ copyLoopTM ⨾ justRewindTM`, NO clear). From
  `encodeTape s ++ res` → `encodeTape (s.set dst (s.get src)) ++ res` (head 0, **residue
  unchanged**); TIGHT budget `(|src|+1)(5L+23)+3L+4`. The clear-free variant the two scratch
  copies need (`opCopy` busts the budget via its double `clearRegionTM`). No `joinTwoHalts`
  wrap (trailing `justRewindTM` reject halt is unreachable; the raw trajectory excludes both).
- **★ `Compile.shrinkEmptyTM`/`shrinkEmpty_run` + `shrinkTwoEmptyM`/`shrinkTwoEmpty_run`
  (2026-06-16c)** — the `eqBit` scratch-SHRINK gadget (Compile.lean, end), the grow mirror.
  Compute = `stepRight ⨾ scanRight 3 ⨾ deleteCarryTM ⨾ stepLeftTM` (delete the trailing
  empty register's `0` separator; `stepLeft` needed — delete ends past-end), bracketed by
  `rewindBracket shrinkComputeM 13`: from `encodeTape (s ++ [[]]) ++ res` (head 0) →
  `encodeTape s ++ (res ++ [0])` (head 0), `O(L)`; `shrinkTwoEmpty` = two
  (`encodeTape (s ++ [[],[]]) ++ res → encodeTape s ++ (res ++ [0,0])`). ⚠ residue grows by
  one `0`/shrink; scan gap is `R+1` (extra separator) so step count is `R+2`. **Templates
  for any residue-tolerant resize-then-rewind op — see this-session REUSABLE PATTERN.**
- **★ `Compile.compareRegsPrefixM`/`compareRegsPrefix_run` (2026-06-20) + `Compile.compareRegsTM`/
  `compareRegsTM_run_{eq,neq}` (2026-06-20b) — the `eqBit` (d2) tester is STRUCTURALLY COMPLETE.**
  `compareRegsTM sc1 sc2 src1 src2 = compareRegsPrefixM ⨾ compareBranchM` is a 2-exit EQ/NEQ
  register-equality tester (`EQ ⟺ s0.get src1 = s0.get src2`), tape **restored** to
  `encodeTape s0 ++ residue` (existential `ValidResidue`), with the no-early-halt trajectory.
  Full shape family (`compareRegsTM_{sig,tapes,start,states,valid,exit_eq,exit_neq,_lt,
  _eq_ne_neq,_is_halt}`, `compareBranchM_*`, `compareRegsPrefixM_*`). Reusable: the closed
  `State` form `consumeStep_iterate_append` (`consumeStep^[k] (s0++[a,b]) = s0++[a.drop k,
  b.drop k]`), `BitState_append_drop_pair`, `halt_getElem_of_haltingStateReached`,
  `compareLoopTM_halt_getElem`. ⚠ **`compareRegsTM_run_*` (top) + `compareRegsPrefix_run`
  step bounds not yet added** (all sub-gadgets ARE bounded; the FEASIBILITY GATE passed
  2026-06-21 — see d2-iv + the proven `compareBudget_arith_fits54`). The d1 `opEqBit`
  wrapper drops `compareRegsTM` in as `branchComposeFlatTM`'s M₁.

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

✅ **Task 0a (eqBit BUDGET FEASIBILITY gate) is DONE (2026-06-21, top-down) — VERDICT
   GREEN.** Re-validated with a worst-case probe + proven arithmetic (see this session's
   block above and `probes/EqBitBudgetProbe.lean`). The prior `~133·op-L²`/fragile-92%
   alarm was over-pessimistic (`L4 < 2·op-L` for distinct `src`; per-stage worst cases
   are mutually exclusive). **Proceed with the bottom-up assembly at const-72** (free vs
   `physStepBudget`); the cleanup tightening is no longer a blocker. The proven
   `compareBudget_arith_fits54` / `selfBudget_eqDst_72` are the top-bound backbone.

   **▶ NEXT TOP-DOWN SESSION:** with 0a done, the eqBit ball is in bottom-up's court
   (assembling d2-iv). The next *non-gated* top-down item is **Task 1 (CliqueRelTM)** —
   standalone, highest standalone top-down value, not blocked by the compiler. Task 0
   (the eqBit-completion axiom checkpoint) is gated on bottom-up finishing the wrapper.
0. **`eqBit`-completion checkpoint (do this the session AFTER bottom-up closes the
   d2 `compareRegsTM` + d1 `opEqBit` wrapper).** When the `eqBit` case of
   `compileOp_sound_physical_residue` (Compile.lean ~18183, currently raw `sorry`) is
   discharged, the **entire live decider chain `sat_NP → … → Compile_run_physical_residue`
   becomes sorry-free** (`evalCnfCmd` is `consLen`/`takeAt`/`dropAt`-free). Concrete top-down
   work: `#print axioms sat_NP` / `inTimePolyTM_evalCnf` and confirm `sorryAx` is GONE from
   the decider half (only `eqBit`'s sibling stub ops + S1/S2/S3 + `red_inNP` remain on
   `CookLevin`). Update README/ROADMAP status tables (the "in-NP half reaches a `sorry`"
   line in README "Not sound" becomes false for SAT). This is the **first headline soundness
   win** and worth a careful audit. Then proceed to Task 1/2.
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
✅ the `forBnd` per-iteration chain + loop machine + BOTH `loopTM` contracts +
fold invariants + budget fix CLOSED (2026-06-13/b/c); ✅ **`compileForBnd_sound_physical_residue`
FULLY PROVEN & axiom-clean (2026-06-14)** — the forBnd counted loop is closed.
Everything left bottom-up is TM-level compiler work in Compile.lean: the **5 stub
ops** in `compileOp_sound_physical_residue` (Compile.lean ~18009; raw `sorry`s at
`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`, ~18183). Both the decider half
(`sat_NP`) and the reduction half (`⪯p`/`toFrameworkWitness'`) rest on these ops.

1. **`eqBit` — THE highest-value item (the ONLY op the LIVE `sat_NP` decider still
   needs).** `evalCnfCmd` is `consLen`/`takeAt`/`dropAt`-free, so discharging the
   `eqBit` case of `compileOp_sound_physical_residue` (Compile.lean ~18183) makes
   the entire live decider chain `sat_NP → … → Compile_run_physical_residue`
   **sorry-free**. The **design is settled** (see this session's block above — read
   it first). `Op.cost eqBit = 1`; residue beyond `clear`'s `|dst₀|` is ZERO; output
   is exactly `[answer]` (1 cell). **Decomposed build plan (build (d2) first, then
   the (d1) wrapper):**

   **(d2) `compareRegsTM src1 src2` — design (A), `cost=1` (budget SETTLED this
   session — see the session block; reuse `copyLoop_run`, NOT `opCopy_run`).**
   Runs on `encodeTape s ++ res`, leaves the tape **restored**, halts in EQ or NEQ
   with `EQ ⟺ s.get src1 = s.get src2`. Structure: `growTwoEmpty ⨾ copy src1→sc1 ⨾
   copy src2→sc2 ⨾ consumeLoop ⨾ verdict ⨾ clear sc1 ⨾ clear sc2 ⨾ shrinkTwoEmpty`.
   Build & prove bottom-up:
   **★ RECOMMENDED ORDER NOW (2026-06-19):** ✅ (d2b-prep), ✅ (d2b verdict
   `eqVerdictM`), ✅ ALL of d2a (leaves + body + `compareLoop_run`), ✅ (d2c-GROW),
   ✅ (d2c-SHRINK), ✅ **(d2-COPY: `copyEmptyRawTM`/`copyEmpty_run` — DONE &
   axiom-clean 2026-06-19).** **ALL d2 sub-gadgets are now proven — the only
   remaining bottom-up work for `eqBit` is the STITCHING:**

   **▶ THE IMMEDIATE NEXT STEP — d2-iv (BUDGET): leaves+body+invariance DONE; finish
   the loop + prefix + top bounds.** `compareRegsTM_run_{eq,neq}` is structurally
   PROVEN; its sub-gadgets (the whole consume-loop cascade) now carry `t ≤ …`
   bounds, and the keystone tape-invariance lemma is proven (2026-06-20d). What's
   left is to bound `compareLoop_run`, `compareRegsPrefix_run`, and the two
   `compareRegsTM_run_*` so the `eqBit` op contract (`(54·L²+54·L+180)·(cost+1)`,
   loosened 2026-06-20d) discharges. **d1 (the wrapper) is BLOCKED on the top bound**
   — without it the wrapper's run lemma has no step bound and the contract can't
   close. The full structural
   assembly (`growTwoEmpty ⨾ copyEmpty src1→sc1 ⨾ copyEmpty src2→sc2 ⨾ compareLoop ⨾
   branchComposeFlatTM eqVerdictM cleanup cleanup exitEQ exitNEQ`) is `#eval`-validated
   (`probes/CompareRegsAssemblyProbe.lean`) and proven. Sub-steps:
   - ✅ **(d2-i CLEANUP) DONE & axiom-clean (2026-06-19b)** — `Compile.compareCleanupM
     sc1 sc2` (= `clear sc1 ⨾ clear sc2 ⨾ shrinkTwoEmpty`) + `compareCleanup_run`:
     from `encodeTape (base++[c1,c2]) ++ res` (sc1=base.length, sc2=base.length+1)
     → `encodeTape base ++ (((res++replicate|c1|0)++replicate|c2|0)++[0,0])`, head 0,
     + no-early-halt. Plus `compareCleanupM_{exit,exit_is_halt,valid,sig,tapes,states}`
     and `shrinkTwoEmptyM_{exit_is_halt,valid,sig,tapes,start}`. **`compareCleanupM_exit_is_halt`
     is ready for the branch wrap (cleanup = M₂ = M₃).**
   - **(d2-ii PREFIX) ✅ DONE & axiom-clean (2026-06-20).** `Compile.compareRegsPrefixM
     sc1 sc2 src1 src2` (= `growTwoEmpty ⨾ copyEmpty sc1 src1 ⨾ copyEmpty sc2 src2 ⨾
     compareLoop sc1 sc2`) + `compareRegsPrefix_run`: from `encodeTape s0 ++ res`
     (sc1=s0.length, sc2=s0.length+1, src1/src2 `< s0.length`) → exit
     `compareRegsPrefixM_exit`, tape `encodeTape ((consumeStep sc1 sc2)^[matchLen g1 g2]
     (s0 ++ [g1, g2])) ++ (res ++ replicate (2·matchLen g1 g2) 0)` (g1=`s0.get src1`,
     g2=`s0.get src2`) + no-early-halt. 4-stage `composeFlatTM_run`/`_no_early_halt`
     thread (model: `copyEmpty_run`). Also added: the prefix-machine shape lemmas
     (`growTwoEmptyM_*`, `copyEmptyRawTM_{start,exit_lt}`, `compareLoopTM_*`) and
     `compareLoop_run` now returns the no-early-halt trajectory too.
     ⚠⚠ **GOTCHA (cost me a session): `omega` SILENTLY FAILS on trivial arithmetic
     side-goals inside this large-context proof** — it returns "could not prove" with
     spurious counterexamples referencing *unrelated* hypotheses (e.g. `length(s0 ++
     [g1,g2]) ≥ 2` for a goal `s0.length < s0.length + 2`). The whole prefix proof uses
     **term-mode `Nat` lemmas** (`Nat.lt_succ_of_lt`, `Nat.lt_of_lt_of_le`,
     `Nat.add_lt_add_left`, `Nat.add_comm`, `Nat.add_sub_cancel_left n m`, …) for ALL
     arithmetic. **Do NOT use `omega` in `compareRegsTM`/the d1 wrapper** — it will fail
     on goals that are obviously true. (Suspected: omega chokes scanning the many
     `List`/encodeTape hypotheses. The next agent with a working `lean_goal` could
     confirm; here the LSP was off-limits.) Also: pin implicit list args of
     `List.set_append_right`/`List.getElem?_append_right` (`(s := …)`, or feed
     `Nat.le_refl _`/`Nat.le_succ _` as the hypothesis) so the side-condition doesn't
     elaborate against a metavariable.
   - **(d2-iii BRANCH WRAP) ✅ DONE & axiom-clean (2026-06-20b).** `Compile.compareRegsTM
     sc1 sc2 src1 src2 = compareRegsPrefixM ⨾ compareBranchM`
     (`compareBranchM := branchComposeFlatTM eqVerdictM cleanup cleanup eqVerdictM_exit_eq
     eqVerdictM_exit_neq`). `compareRegsTM_run_eq` (EQ via `branchComposeFlatTM_run_pos`)
     / `compareRegsTM_run_neq` (NEQ via `_run_neg`, splitting on which `drop n` suffix is
     nonempty), tape restored to `encodeTape s0 ++ residue` (existential `ValidResidue`).
     The prefix→state rewrite used the new `consumeStep_iterate_append` (NOT
     `consumeIter_spec` — the closed `State` form is cleaner). Plus the full shape family
     `compareRegsTM_{exit_eq,exit_neq,_lt,_ne,_is_halt,sig,tapes,start,states,valid}` and
     `compareBranchM_*`, `compareRegsPrefixM_{states,sig,tapes,valid,exit_lt,exit_is_halt}`.
     **NB: `omega` worked fine in these small shape-lemma contexts** (the d2-ii
     omega-failure was specific to the huge prefix proof; not a general ban).
   - **(d2-iv BUDGET) — ALL sub-gadgets bounded; FEASIBILITY GATE PASSED (top-down
     2026-06-21). Remaining: prefix + top bounds + d1 wrapper.** ✅ Bounded & axiom-clean:
     `compareLoop_run` **`(matchLen+1)·(24·L+45)`** (iteration-explicit), `growEmpty ≤ 2L+9`,
     `growTwoEmpty ≤ 4L+21`, `shrinkEmpty ≤ 4L+12`, `shrinkTwoEmpty ≤ 8L+25`,
     `compareCleanup ≤ 18L²+8L+45` (collapsed — fine, see below), `eqVerdictM ≤ 6L+2`,
     `copyEmpty (|src|+1)(5L+23)+3L+4`. **The gate (top-down) PROVED the composition fits
     — see the session block + `probes/EqBitBudgetProbe.lean`. Do this at const-72.**
     1. **Bump `opBudgetLoosen`/the contract `54 → 72`** (one line; free vs `physStepBudget`).
        Then **cleanup tightening is OPTIONAL** — the collapsed `compareCleanup ≤ 18L²` + the
        collapsed d1 `clear dst ≤ 9L²` fit const-72 at ≤88% for `src1≠src2` (measured/proven).
        Tighten only if cheap (`clearRegionTM_run_tight` sibling exposing the `(n+1)·(6L+13)`
        already inside `clearRegionTM_run` before `clearBudget_arith` collapses it) — it drops
        the margin to ~28% and robustifies `nlinarith`, but is NOT a blocker.
     2. **Prefix `compareRegsPrefix_run`** (sum grow+copy1+copy2+compareLoop, witness
        `((t1+1+t2)+1+t3)+1+t4`): all four bounded. Thread the tape lengths
        (`L'(copy1)=L+|g1|+2`, `L''(copy2)=L4=L+|g1|+|g2|+2`; bound everything by `L4`),
        `|g1|+|g2| ≤ op-L` (`encodeTape_set_length`/`size_set_add`), `matchLen ≤ |g1|`.
     3. **Top `compareRegsTM_run_{eq,neq}`** (= prefix + verdict + cleanup): sum and discharge
        via the PROVEN **`compareBudget_arith_fits54`** (distinct `src`) — lift it from the
        probe into `Compile.lean`. The d1 wrapper additionally needs **`selfBudget_eqDst_72`**
        for the degenerate `eqBit r r r` (constraint `l+3 ≤ op-L`). Hypotheses (all from the
        run lemmas): `matchLen ≤ |g_i|`, `c1+c2 ≤ l1+l2` (`length_drop`), `l1+l2+2 ≤ op-L`,
        `dlen ≤ op-L`. **The hard final arithmetic is already discharged — just port it.**
     **After the top bound, d1 (the `opEqBit` wrapper) is unblocked.**

   - ✅ **(d2-COPY) `copyEmptyRawTM`/`copyEmpty_run` — DONE & axiom-clean (2026-06-19).**
     `encodeTape s ++ res` (head 0, `dst` EMPTY) → `encodeTape (s.set dst (s.get src)) ++ res`
     (head 0, **res unchanged**), tight budget `(|src|+1)(5L+23)+3L+4`. The clear-free
     `navigateToRegTM ⨾ copyLoopTM ⨾ justRewindTM` (= `opCopy` phases 2–4). Probe
     `probes/CopyEmptyProbe.lean`. Place the copies so `dst = sc1 = s.length`, `sc2 = s.length+1`
     (the grown-empty registers); `copyEmpty_run` needs `dst ≠ src`, `dst < length`, `src < length`,
     `BitState`, `s.get dst = []` — all hold post-`growTwoEmpty`.
   - ✅ **(d2b-prep / d2b / d2a) — ALL DONE & axiom-clean.** Key outputs the assembly
     consumes: **`Compile.compareLoop_run`** (from `encodeTape s ++ res` head `0`,
     loop halts at `compareBodyTM.states` with `sc1`/`sc2` = their `matchLen`-dropped
     suffixes, residue `++ replicate (2n) 0`); **`Compile.matchLen_drop_empty_iff`**
     (equal ⟺ both suffixes empty — the verdict's decision fact). ✅ `compareLoop_run`'s
     step bound is now PROVEN iteration-explicit `(matchLen+1)·(24·L+45)` (2026-06-21).
   - ✅ **(d2c-GROW) `growEmptyTM`/`growTwoEmpty` — DONE & axiom-clean (2026-06-16b).**
     Grows `encodeTape s ++ res` → `encodeTape (s ++ [[]]/[[],[]]) ++ res` (head 0),
     `O(L)`, residue passes through. Place `sc1,sc2` at the register-list END = `s.length`,
     `s.length+1` (so `src1`/`src2` indices are unchanged).
   - ✅ **(d2c-SHRINK) `shrinkEmptyTM`/`shrinkEmpty_run` + `shrinkTwoEmptyM`/
     `shrinkTwoEmpty_run` — DONE & axiom-clean (2026-06-16c).** `encodeTape (s ++ [[]]) ++
     res → encodeTape s ++ (res ++ [0])` (head 0), `O(L)`; two-version
     `encodeTape (s ++ [[],[]]) ++ res → encodeTape s ++ (res ++ [0,0])`. ⚠ residue grows
     by one `0`/shrink. Probe `probes/ShrinkEmptyProbe.lean` (incl. grow→shrink round-trip).
     **No explicit round-trip lemma is needed — the (d2) seam just threads the concrete
     output tapes; `shrinkTwoEmpty_run` is applied to the post-`clear` `encodeTape
     (s ++ [[],[]]) ++ res'` state.**
   - **Budget (settled, `cost=1` ≈ 18L²):** the two copies use **`copyEmpty_run`**
     (`(|src|+1)(5L+23)+3L+4`, built on the tight `copyLoop_run`) ⇒ `≤ ~10L²` total;
     the consume loop is `Θ(L²)` (a few passes/bit on shrinking scratch) ⇒ `≤ ~8L²`;
     grow/shrink/verdict `O(L)`. Probe `CompareRegsBudgetProbe.lean`. **Do NOT reuse
     `opCopy_run` (loose `9L²·|src|` busts the budget). Do NOT bump `Op.cost eqBit`.**
   - **Reuse heavily:** `navigateAndTestTM`/`bitReadTM`/`opTail`/`copyLoop_run`/
     `clear`/`insertCarryTM`/`deleteCarryTM` (all proven + `#eval`-validated),
     `branchComposeFlatTM`/`joinTwoHalts`/`loopTM` run-lemma stacks, and
     `clearBodyRawTM`/`forBndLoop_run`/`opNonEmpty_run` as proof templates.

   **(d1) WRAPPER — reuse `nonEmptyRawM` verbatim — BLOCKED on d2-iv (do it AFTER the
   budget).** `compareRegsTM` is now a complete 2-exit tester (`compareRegsTM_run_{eq,neq}`
   + `compareRegsTM_{exit_eq,exit_neq}_{is_halt,lt}` + `_exit_eq_ne_neq` + `_valid` +
   `_sig`/`_tapes`/`_start` — all PROVEN, ready to drop in as the `branchComposeFlatTM`
   M₁). Define `opEqBit dst src1 src2 := joinTwoHalts (branchComposeFlatTM (compareRegsTM
   s.length (s.length+1) src1 src2) (nonEmptyBranchBody dst 2 _) (nonEmptyBranchBody dst 1
   _) compareRegsTM_exit_eq compareRegsTM_exit_neq) …` — structurally identical to
   `Compile.nonEmptyRawM`/`opNonEmpty` with `compareRegsTM` swapped in for
   `navigateAndTestTM`. The shape/valid/halt lemmas and `opEqBit_run` are a **mechanical
   port of `opNonEmpty`'s**; the `eqBit` contract case is then a copy of the `nonEmpty`
   case at Compile.lean ~18183 (residue `res_in ++ replicate |dst₀| 0`, W-invariant via
   `State.size_set_add`). ⚠ **The contract's per-op budget can only be met once
   `compareRegsTM_run_{eq,neq}` carry a `t ≤ …` bound (d2-iv).** The EQ/NEQ residue from
   `compareRegsTM` is existential — `obtain` it, then the `nonEmptyBranchBody` clear of
   `dst` absorbs it (`dst < s.length`, content = original, restored by the tester).

2. **`concat` (next after `eqBit`; reduction-half only, not live `sat_NP`).**
   `concat dst src1 src2 = s.set dst (s.get src1 ++ s.get src2)`. = `clear dst ⨾
   copy-append src1 ⨾ copy-append src2`. The copy op's `copyLoop` already appends
   `src` to `dst`'s end — but `copyLoop_run` assumes **`dst` empty**; `concat`'s
   second append needs a **`copyLoop_run` generalized to nonempty `dst`** (gives
   `s.set dst (dst ++ src)`). Generalize that one lemma, then `concat` is two
   `copyLoop`s. Cost `|src1|+|src2|+1` is generous. Then the value-as-length trio
   `takeAt`/`dropAt`/`consLen` (canonical toolkit only — gated on Task 3).
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
