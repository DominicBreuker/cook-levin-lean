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

## ✅ What the last session (2026-06-20b, bottom-up) did — **`compareRegsTM` (d2-iii) the BRANCH WRAP is PROVEN & axiom-clean** — `compareRegsTM` is now a complete 2-exit EQ/NEQ tester; only d2-iv (budget) + d1 (wrapper) remain for `eqBit`

Closed the d2-iii STITCHING (HANDOFF "▶ THE IMMEDIATE NEXT STEP"). All sub-gadgets
were proven; this session assembled the final `compareRegsTM`. **Full build green
(3358), all new results axiom-clean (`[propext, Classical.choice, Quot.sound]`).**

1. **`Compile.compareRegsTM sc1 sc2 src1 src2` is DONE** (`= compareRegsPrefixM ⨾
   compareBranchM`, where `compareBranchM := branchComposeFlatTM eqVerdictM cleanup
   cleanup (eqVerdictM_exit_eq) (eqVerdictM_exit_neq)` — BOTH branches the same
   cleanup). With its full shape family: `compareBranchM_{sig,tapes,start,states,valid}`,
   `compareRegsTM_{sig,tapes,start,states,valid}`, the two exit defs
   `compareRegsTM_exit_{eq,neq}` + `_{eq,neq}_lt` + `_eq_ne_neq` + `_{eq,neq}_is_halt`.
2. **`compareRegsTM_run_eq` / `compareRegsTM_run_neq` PROVEN** — the 2-exit tester
   contract: from `encodeTape s0 ++ res` (head `0`, `sc1 = s0.length`,
   `sc2 = s0.length+1`, `src1/src2 < s0.length`), reaches `compareRegsTM_exit_eq`
   when `s0.get src1 = s0.get src2` (EQ) / `compareRegsTM_exit_neq` when `≠` (NEQ),
   tape **restored** (`∃ residue, ValidResidue residue ∧ tape = encodeTape s0 ++
   residue`), + the no-early-halt trajectory. NEQ splits on which suffix is nonempty
   (`eqVerdictM_run_neq_left` / `_right`). **Residue is existential** (the d1 wrapper
   re-clears `dst` anyway) — avoids the trailing-zeros `List.replicate` algebra.
3. **Reusable helpers added (axiom-clean):** `consumeStep_iterate_append` (the
   `State` closed form `consumeStep^[k] (s0 ++ [a,b]) = s0 ++ [a.drop k, b.drop k]`),
   `BitState_append_drop_pair`, `halt_getElem_of_haltingStateReached` (generic
   `haltingStateReached`-true → `.halt[i]? = some true`), `compareLoopTM_halt_getElem`,
   `compareCleanupM_{start,exit_lt,halt_getElem}`, and the prefix shape family
   `compareRegsPrefixM_{states,sig,tapes,valid,exit_lt,exit_is_halt}`.

### ⚠ THE remaining bottom-up blocker for `eqBit` is d2-iv (BUDGET) — still the open GAP

`compareRegsTM_run_{eq,neq}` are **`∃ t` with NO `t ≤ …` conjunct**, inherited from
`growTwoEmpty_run` / `shrinkTwoEmpty_run` / `compareLoop_run` / `compareCleanup_run`
(`compareLoop_run`'s bound is the OPAQUE `loopBudget tIter tDone n`). The `eqBit`
contract case (`compileOp_sound_physical_residue`) **requires** the per-op budget
`(9L²+9L+30)·(cost+1)`, so **d1 (the wrapper) cannot close `eqBit` until the budget
exists.** ⇒ **d2-iv is THE critical path, not d1.** Plan (probe-validated feasible
`≈18L²` in `CompareRegsBudgetProbe`): add a `t ≤ …` conjunct to each of
grow/shrink/compareLoop (grow/shrink `O(L)` — `rewindBracket` step counts recoverable;
`compareLoop` needs `loopBudget_le`-bounding of `loopBudget tIter tDone n` with
`tIter,tDone = O(L)`, `n ≤ L`), thread them through `compareRegsPrefix_run` /
`compareRegsTM_run_{eq,neq}`. `copyEmpty_run`/`clearRegionTM_run` already carry their
bounds (`(|src|+1)(5L+23)+3L+4`, `9L²+9`). See BOTTOM-UP task 1 (d2-iv).

### ★ FINDINGS (this session) — reusable for branch wraps / future 2-exit testers

- **`rw [<def>]` on a plain `def` (e.g. `compareRegsTM`) can FAIL** ("did not find
  pattern") when the goal already shows it through a projection. The composite
  machine is **defeq** to its `composeFlatTM`/`branchComposeFlatTM` body, so just
  `exact h` (or `exact this k …`) lets the kernel unfold — drop the `rw`.
- **`rcases hh : e with …` / `cases hh : e` SUBSTITUTES `e` in the goal** (when it
  occurs there) — so a later `rw [hh]` on the goal fails ("no occurrence"). In the
  `some` branch the goal is already `some b = …`; close with `simp only [hh, …] at h';
  subst h'; rfl` (don't re-`rw [hh]` the goal).
- **A 2-exit tester's `_run` trajectory is `(≠ exit_neg ∧ ≠ exit_pos ∧ ¬halt)`** (the
  `eqVerdictM`/`compareRegsTM` shape). `branchComposeFlatTM_run_pos/_neg` want
  `(≠ exit_pos ∧ ≠ exit_neg ∧ ¬halt)` — **reorder** with
  `fun k hk ck hck => ⟨(h …).2.1, (h …).1, (h …).2.2⟩`.
- **Lift a composite's exit halt to `getElem?` form** = `composeFlatTM_halt_intro` /
  `branchComposeFlatTM_M2_halt_intro` (pos) / `_M3_halt_intro` (neg), each consuming
  the inner `.halt[e]? = some true`; the index comes out `M₁.states + e` (commute with
  the def's order via a `show … from by …; omega` rewrite). `loopTM`'s loop halt in
  `getElem?` form: `(loopHalt B)[B.states]?` via `getElem?_append_right` + `Nat.sub_self`.
- **`consumeStep`'s SECOND `State.get` reads the ORIGINAL `s`, not the post-`set`
  state** (`(s.set sc1 …).set sc2 (State.get s sc2).tail`) — state the two `get`-facts
  on `s0 ++ [a,b]` (NOT on the half-updated list).
- **The branch's `M₂`/`M₃` run starts at `M₂.start` (not literal `0`)** —
  `compareCleanupM_start`/`compareBranchM_start` are `= 0`, so convert
  `h_run2`/`h_traj2` with `rw [compareBranchM_start]` then `exact`; the no-early-halt
  hyp already uses `cfgB` (state `0`), so DON'T `rw … at` it (only the goal).
- **`List.set_append_right`/`getElem?_append_right`: feed the side-condition as
  `Nat.le_refl _` / `Nat.le_succ _`** (not `by omega` — the implicit index metavar
  defeats it here) and the leftover index via `show … from Nat.add_sub_cancel_left …`.

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
  `compareLoopTM_halt_getElem`. ⚠ **NO step bound yet** (the `∃ t` is budget-free —
  d2-iv). The d1 `opEqBit` wrapper drops this in as `branchComposeFlatTM`'s M₁.

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

0. **`eqBit`-completion checkpoint (do this the session AFTER bottom-up closes the
   d2 `compareRegsTM` + d1 `opEqBit` wrapper).** When the `eqBit` case of
   `compileOp_sound_physical_residue` (Compile.lean ~15261, currently raw `sorry`) is
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
ops** in `compileOp_sound_physical_residue` (Compile.lean ~15089; raw `sorry`s at
`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`, ~15261–15280). Both the decider half
(`sat_NP`) and the reduction half (`⪯p`/`toFrameworkWitness'`) rest on these ops.

1. **`eqBit` — THE highest-value item (the ONLY op the LIVE `sat_NP` decider still
   needs).** `evalCnfCmd` is `consLen`/`takeAt`/`dropAt`-free, so discharging the
   `eqBit` case of `compileOp_sound_physical_residue` (Compile.lean ~15261) makes
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

   **▶ THE IMMEDIATE NEXT STEP — d2-iv (BUDGET): the structural assembly is DONE;
   only the step-count GAP remains.** `compareRegsTM` (the 2-exit EQ/NEQ tester) is
   fully PROVEN & axiom-clean (`compareRegsTM_run_{eq,neq}`, see this-session block).
   What's left is to give it (and its sub-gadgets) explicit `t ≤ …` bounds so the
   `eqBit` op contract (which needs `(9L²+9L+30)·(cost+1)`) can be discharged. **d1
   (the wrapper) is BLOCKED on d2-iv** — without the budget the wrapper's run lemma
   has no step bound and the contract case can't close. The full structural
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
   - **(d2-iv BUDGET) ← DO THIS NEXT — the only remaining bottom-up blocker for `eqBit`.**
     Add a `t ≤ …` conjunct to `growTwoEmpty_run` (`O(L)`), `shrinkTwoEmpty_run` (`O(L)`),
     `compareLoop_run` (bound the OPAQUE `loopBudget tIter tDone n` via `loopBudget_le`
     with `tIter,tDone = O(L)`, iteration count `n ≤ L`), and `compareCleanup_run`
     (`clearRegionTM_run` already carries `9L²+9`; `shrinkTwoEmpty` `O(L)`). Then thread
     the sums through `compareRegsPrefix_run` and `compareRegsTM_run_{eq,neq}` (the
     `composeFlatTM_run`/`branchComposeFlatTM_run_*` give `t₁+1+t₂`-additive totals —
     just carry the `≤` alongside). Probe `CompareRegsBudgetProbe` validated `≈18L² ≤
     (9L²+9L+30)·2` feasible. `copyEmpty_run` already has `(|src|+1)(5L+23)+3L+4`.
     **Only after d2-iv does d1 become unblocked.**

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
     (equal ⟺ both suffixes empty — the verdict's decision fact). ⚠ `compareLoop_run`'s
     step bound is the OPAQUE `loopBudget tIter tDone n` — the d2 assembly must bound
     it (`O(L²)`).
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
   case at Compile.lean ~15262 (residue `res_in ++ replicate |dst₀| 0`, W-invariant via
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
