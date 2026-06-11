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
            → Compile.paddedBitDecider_run                    (Compile.lean ~9654; ✅ PROVEN, no k ≤ s.length)
                 → Compile.bitDecider_run                     (Compile.lean ~9486; physStepBudget)
                      → Compile_run_physical_residue          (Compile.lean ~9225; PROVEN from the assembly,
                                                               sorry only via the leaf gadgets below)
       evalCnfDecidesLang : DecidesLang …                     (EvalCnfTM.lean; ✅ COMPLETE & AXIOM-CLEAN
                                                               (2026-06-10): the verifier Cmd, its inner
                                                               bodies, and ALL contracts are PROVEN; budget
                                                               quartic 200000·(n+1)^4; regBound=16)
REAL REMAINING MATH under the assembly:
  padRegsTM_run / _traj   (Compile.lean ~10130; ✅ PROVEN, sorry-free — the WALL gadget
                           is COMPLETE. paddedBitDecider_run's residual sorryAx is now
                           ONLY the leaf gadgets below, not padRegsTM)
  compileOp_sound_physical_residue   (Compile.lean ~9000; 5/12 ops PROVEN, 7 SORRY)
  compileIfBit_sound_physical_residue  (Compile.lean ~10240; ✅ PROVEN 2026-06-11 —
                           real compileTestBit tester + branchCompose + joinTwoHalts)
  compileForBnd_sound_physical_residue (Compile.lean ~10430; SORRY — ⚠ DESIGN GAP
                           surfaced 2026-06-11: likely UNPROVABLE as pinned, see
                           TOP-DOWN task 1)
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
bridges is just the **7 leaf ops + 2 combinators** (`compileOp_/compileIfBit_/
compileForBnd_sound_physical_residue`) — see the stream sections. The LIVE path needs
only `tail`/`copy`/`eqBit` of the 7, plus both combinators.

---

## ✅ What this session (2026-06-11, bottom-up) did — `ifBit` combinator CLOSED + op/forBnd design findings

**1. `compileIfBit_sound_physical_residue` is PROVEN (axiom-clean), and
`compileTestBit` is REAL** (the `branchTester_default` stub is retired):

- `Compile.exactOneOneTM` (4-state "register block = exactly `[2]`" reader) +
  step/run/traj lemmas; `Compile.testBitInnerTM` (read ⨾ `justRewindTM` leaves);
  `Compile.testBitRawTM t` (`navigateAndTestTM t` ⨾ inner / delim-rewind);
  NEG leaves merged by `joinTwoHalts`. `#eval`-probe-validated FIRST
  (17-state battery; observed ≤ 2·L+5 steps).
- Packaged contracts **`Compile.testBitReg_run_pos` / `_run_neg`**: the tester
  reaches `exitPos` iff `s.get t = [1]`, head back at `0`, **tape unchanged**
  (so the chosen branch starts from its own `initFlatConfig`), traj avoids both
  exits + halts, `T ≤ 3·L + 12`. Key structural fact making the single-phase
  `justRewindTM` sound everywhere: every register block ends in its **own `0`
  delimiter** (the leaf heads never sit on a `3`).
- **Two pinned-interface gaps fixed (machine-checked necessity):** the `ifBit`
  contract gained `(ht : t < s.length)` (the tester must physically navigate to
  register `t`) and `(hG : size + s.length + |res0| + 2 ≤ G)` (the tester's step
  count is linear in the tape length; without a tape bound the budget conjunct
  is unprovable). Both are supplied at the single call site
  (`run_physical_residue_gen`'s `ifBit` case: `huses.1` + its own `hG`).
- Budget composes via `physStepBudget_seq G 0 c` (the tester + bridge steps fit
  inside one extra `physStepBudget` unit: `3·G+12+2 ≤ 9G²+9G+33`).

**2. ⚠⚠ Design findings (settle BEFORE building the remaining gadgets — they
invalidate the previous session's Task-1/Task-2 plans):** see the stream
sections below. In short: (a) the planned `moveRegion2TM`+scratch implementation
of `copy`/`tail`/`eqBit` **violates the pinned W-invariant ①** and has **no
scratch register** to use; the in-place **marking/cursor** design is forced (or
an owner-approved `Op.cost` bump that ripples into the proven EvalCnf budgets);
(b) the pinned `compileForBnd` contract is **likely unprovable as stated**
(loop-count snapshot vs. clobbering bodies + existential residue) — a genuine
interface-design task, now TOP-DOWN task 1.

Build green (3358 jobs); new lemmas `[propext, Classical.choice, Quot.sound]`;
`#print axioms CookLevin` unchanged (`sorryAx` via the remaining gadgets + the
hardness half only).

---

## ✅ PROVEN, reusable — do not re-derive

- **`Compile.run_physical_residue_gen`** (Compile.lean ~9225) — the residue
  induction; `op`/`seq` cases proven, `ifBit`/`forBnd` dispatch to the two
  combinators. W-invariant ① + `physStepBudget` budget ② both threaded.
- **`physStepBudget`** + `_seq` (exact superadditivity) / `_mono` / `_poly`
  (cubic diagonal) — the composable budget. **The only correct budget shape.**
- **`Compile.bitDecider_run`** — decider boundary, now `physStepBudget`. Sorry-free
  except transitively via the leaf gadgets.
- **`Compile.paddedBitDecider_run`** — the WALL resolution: pad-then-decide on a
  **narrow** input, **no `k ≤ s.length`**. Proven from the `padRegsTM` interface +
  `bitDecider_run`. Plus the `*_append_replicate_nil` padding bookkeeping (sorry-free).
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
- **`Compile.sound_of_run_residue`** — residue run ⇒ `Compile_sound` shape.
- **Threading toolkit** (now all in `Compile.lean`): `Cmd.eval_preserves_BitState`,
  `Op.inBounds_of_UsesBelow`, `Cmd.eval_length_ge`/`_le`, `Cmd.size_eval_le`,
  `State.set_length_ge`, `BitState_set_pad`.
- **Move/branch/loop gadgets:** `moveRegionTM`/`moveRegion2TM` (single/dual FIFO
  transfer), `joinTwoHalts*`, `rewindBracket`/`_transport`, `bitReadTM`,
  `rewindTwoPhaseTM`, `deleteCarryTM`, `navigateAndTestTM`, `loopTM`(+`_run`/
  `_no_early_halt`), `loopBudget_le`. All axiom-clean. ⚠ The move gadgets are
  **residue-costly** (each pass appends `|src|` zeros to the residue) — fine
  inside `forBnd` bookkeeping (covered by the `iters²` cost lump), **not** usable
  for the factor-1 W-invariant per-op contracts (see BOTTOM-UP task 1).
- **★ `compileTestBit` is REAL + `compileIfBit_sound_physical_residue` PROVEN**
  (2026-06-11): `exactOneOneTM`/`testBitInnerTM`/`testBitRawTM` + the packaged
  tester contracts `testBitReg_run_pos`/`_run_neg` (head-0 exit, tape unchanged,
  `T ≤ 3·L+12`) + the full residue `ifBit` combinator (TRUE branch through the
  demoted `haltT` bridge, FALSE through the kept `haltE`). Reusable patterns:
  read-only tester leaves can use the bare single-phase `justRewindTM` (block-end
  cells are always the register's own `0` delimiter, never `3`); join transport
  for a run ending at a *non-`h1`* kept halt = `joinTwoHalts_run_eq` + a
  `∀ k ≤ T, ≠ h2` argument (`testBitReg_run_pos`'s ending).
- **5/12 ops PROVEN** in `compileOp_sound_physical_residue`: `appendOne`,
  `appendZero`, `clear`, `nonEmpty`, `head` (each carries the W-invariant ①).

---

# ▶ TOP-DOWN work stream — next steps

You assemble final pieces and design their proofs; create `sorry` lemmas when
provable; surface gaps early.

✅ **The decider half's top-down AND verifier work is COMPLETE** (2026-06-10):
both bridges assembled, the WALL resolved, `encode_size` settled, layer
composition/NP-routing closed, and the EvalCnf verifier fully proven. Every
residual sorry on the `sat_NP` decider path AND the `⪯p`/`toFrameworkWitness'`
reduction path is a **compiler gadget**. The top-down frontier:

1. **⚠ `compileForBnd` interface design (NEW 2026-06-11 — blocks the last
   combinator; settle BEFORE any bottom-up forBnd build).** The pinned
   `compileForBnd_sound_physical_residue` is **likely unprovable as stated**,
   for two machine-independent reasons:
   - **Snapshot vs. clobber.** `Cmd.run` snapshots `iters = |s.get bound|` at
     loop **entry**; the body may legally clobber `bound` AND `counter`
     mid-loop, yet the machine must still execute exactly `iters` iterations
     and re-materialise `counter := replicate i 1` each round. A TM cannot hold
     `iters` in finite control, and **no tape region survives the body
     reliably**: registers can be clobbered by the body, and the body contract's
     exit residue is **existential** (a conforming body could mangle any count
     stored past the terminator).
   - **The only sound storage is a register the body provably does not touch**
     (the body's physical contract preserves *all* registers ≥ its `UsesBelow`
     bound, as `encodeTape (body.eval s')` content). But `compileForBnd
     counter bound rbody` has no static fresh register index to use.
   **Design direction (validate, then re-pin):** compiler-assigned static
   scratch registers (e.g. 2 per `forBnd` nesting level, above the program's
   syntactic max register, threaded as a `compileCmd` parameter), plus an
   interface extension: "scratch registers are `[]`" threaded through
   `run_physical_residue_gen` (they start `[]` on the live path — `padRegsTM`
   pads with `[]` — and each loop must restore them to `[]`), `UsesBelow`/
   `regBound` widened accordingly (ripples: `evalCnfDecidesLang.regBound 16 →
   16 + 2·depth`, mechanical). Loop bookkeeping (move one `1`-cell
   `K1 → K2` per iteration, nondestructive `copy K2 → counter`) can use the
   proven `moveRegionTM` family — their residue cost is covered by `forBnd`'s
   `iters²` cost lump, which factor-1 per-op contracts don't have. ⚠ The
   per-iteration `counter` copy ALSO needs the nondestructive-copy gadget
   (BOTTOM-UP task 1) — design them together. Deliverable: a re-pinned
   `compileForBnd` contract + gen patch that typechecks (`sorry` bodies fine),
   plus an `#eval` probe of the loop skeleton.
2. **CliqueRelTM — replicate the EvalCnf pattern (highest standalone top-down value).**
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
3. **Framework `red_inNP` (NP.lean:291) — layer-native `inNP` refinement.** The one genuine
   framework-side `sorry` for NP-routing (consumed by `inNP_kSAT`, hence on `CookLevin`'s
   path). It is **blocked by design**: `inNP Q` exposes only an opaque `FlatTM` decider
   (`inTimePoly`), from which no `Cmd` is recoverable, so the layer engine has nothing to
   precompose. The fix is to make the framework's `inNP`/`inTimePoly` **layer-native**
   (carry a `DecidesLang`), after which `red_inNP` collapses to the proven
   `red_inNP_of_lang`. Deep S3-migration item; design when the S3 retirement
   (ROADMAP step 2) is underway.
4. **(optional cleanup) Delete the dead `Compile_sound` / `Compile_run_physical` /
   `Compile_polyBound`** (overhead budget, superseded by the residue route, nothing
   consumes them). Low priority; scrub their stale doc references in PolyTime.lean headers
   (also stale: the `≤ 5·size+20` encodeState size quoted in NP.lean/PolyTime.lean
   comments — the proven bound is `≤ 6·size`).

# ▶ BOTTOM-UP work stream — next steps

You build the gadgets the (pinned) contracts need. Build green per item;
`#print axioms`-clean. Probe each machine end-to-end (`#eval`) before proving.

✅ "EvalCnf inner bodies" CLOSED (2026-06-10); ✅ **`compileTestBit` +
`compileIfBit_sound_physical_residue` CLOSED (2026-06-11)**. Everything left
bottom-up is TM-level compiler work in Compile.lean. Both the decider half
(`sat_NP`) and the reduction half (`⪯p`/`toFrameworkWitness'`) rest on the SAME
gadgets below, so discharging Tasks 1–2 closes **both** halves of the live
chain at once. Remaining: the **7 sorry ops** + the **`forBnd` combinator**.

1. **The 3 live-path op gadgets** in `compileOp_sound_physical_residue`
   (Compile.lean ~9000): **`tail`, `copy`, `eqBit`** (5/12 proven: `appendOne`/
   `appendZero`/`clear`/`nonEmpty`/`head`; `evalCnfCmd` needs only these three
   more, plus the combinators).
   **⚠⚠ 2026-06-11 DESIGN FINDING — the prior plan (two-phase transfer via
   `moveRegion2TM` + scratch) is DEAD for these ops as pinned, for two
   independent reasons:**
   - **No scratch register exists.** The pinned contract quantifies over all
     in-bounds states; `Op` syntax carries no scratch operand and no register is
     known empty. (Changing `Op` syntax/`inBounds` would ripple into the proven
     `EvalCnfCmd.lean` and `Op.inBounds_of_UsesBelow` — do not.)
   - **The W-invariant ① forbids move-based copying.** Every `moveRegionTM` pass
     appends `|src|` zeros to the residue (delete+insert per bit), so any
     move-based `copy` grows `size+residue` by `≈ 2·|src|` while
     `Op.cost copy = |src|+1` allows only `|dst₀|+1` residue growth. Worse,
     `eqBit` has `Op.cost = 1` — NO length-dependent residue growth is
     affordable, under ANY constant-factor loosening of ①.
   **The forced design (validate by `#eval` probe first): in-place
   marking/cursor reads.** Temporarily overwrite one cell with `3` (the marked
   tape is `encodeTape` of a state with a `2`-valued cell — still a legal state,
   so non-`BitState`-requiring gadget lemmas apply verbatim), append the read
   bit to `dst` (raw `appendAtTM`, NO standard rewind brackets — they scan for
   `3` and find the mark; scan-left-from-the-right-end DOES find the mark,
   which is exactly the return path), restore the bit, advance. Residue growth:
   only `clear dst`'s `|dst₀|` — fits ① exactly. `copy dst src` with
   `dst = src` is a compile-time special case (no-op machine; `List.set` with
   the same value). `eqBit`: cursor-compare with one mark per source register
   (two interior `3`s are distinguished by compile-time position order).
   Budget: ~4 passes per bit ⇒ `O(L²)` — fits `9L²+9L+30` (bump the constant if
   tight; it is tunable). Alternative if marking probes badly: owner-approved
   `Op.cost` bumps (`copy/tail ≥ 2|src|`, `eqBit ≥ |src1|+|src2|`) — honest
   (cost model's own "charge for reads" philosophy) but ripples into the proven
   EvalCnf step-lemma constants (`100`/`300`/`1000`) and witness cost bounds.
   Then `concat` (same cursor machinery), and last the value-as-length trio
   `takeAt`/`dropAt`/`consLen` (canonical toolkit only — gated on Task 3).
2. **`compileForBnd` build — GATED on the TOP-DOWN task-1 interface design**
   (snapshot-vs-clobber: the loop count must live in compiler-assigned static
   scratch registers; the pinned contract needs a scratch-emptiness extension).
   Do NOT build a `loopTM`-over-`bound` machine against the current contract:
   a body that clobbers `bound`/`counter` makes it wrong (machine-independent).
   Once re-pinned: loop skeleton = `loopTM`, bookkeeping via `moveRegionTM` +
   the task-1 nondestructive copy; budget via `loopBudget_le` against the
   `iters²` cost lump.
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
- **Append a BIT `b`** = `appendAtTM (b+1)`. `deleteCarryTM` deletes the cell **left
  of the head**; `navigateAndTestTM src` lands the head **on** src's first content.
- **`omega` can't see through `Var := Nat`** (use a `Nat`-typed param), record
  projections / `def`-constants (`show` the reduced form first), nor a `set x := e`
  for hyps created *after* the `set`. **Avoid nested `set`/`let` over `State.set`/
  `.get`** (`isDefEq` blows up ×8/level — flatten with `simp only [Cmd.eval_op, Op.eval]`).
  **`.get` mis-resolves on `State` literals** — write `State.get s r` explicitly.
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
