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
       evalCnfDecidesLang : DecidesLang …                     (EvalCnfTM.lean; regBound=12, width_le PROVEN;
                                                               SORRY fields: encodeIn_size, enc_bit,
                                                               usesBelow, noConsLen — all BOTTOM-UP, Task 1)
REAL REMAINING MATH under the assembly:
  padRegsTM_run / _traj   (Compile.lean ~10130; ✅ PROVEN, sorry-free — the WALL gadget
                           is COMPLETE. paddedBitDecider_run's residual sorryAx is now
                           ONLY the leaf gadgets below, not padRegsTM)
  compileOp_sound_physical_residue   (Compile.lean:8238; 5/12 ops PROVEN, 7 SORRY)
  compileIfBit_sound_physical_residue  (Compile.lean ~9111; SORRY — gated on real compileTestBit)
  compileForBnd_sound_physical_residue (Compile.lean ~9164; SORRY — gated on real compileForBnd)
```
Both the **canonical** path (`DecidesLang'` / `inNPLang_to_inNP`) and the **free/live**
path (`DecidesLang` / `inTimePolyLang_to_inTimePoly`) are now assembled and bridge the
same `paddedBitDecider_run` → `bitDecider_run`. The remaining sorrys are exactly the
pinned bottom-up gadgets above plus EvalCnf's bottom-up encoding fields.

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
✅ `Compile.padRegsTM` is **DONE** (run/traj/shape all proven sorry-free). What's left
under the decider bridges is just the **7 leaf ops + 2 combinators** (`compileOp_/
compileIfBit_/compileForBnd_sound_physical_residue`) — see the stream sections. For the
FREE path specifically, `evalCnfDecidesLang` still owes its bottom-up encoding fields
(`encodeIn_size`, `enc_bit`, `usesBelow`, `noConsLen`; `width_le` and `regBound=12` are
done) — Task 1.

---

## ✅ What this session (top-down, 2026-06-08) did — retarget the REDUCTION side

The decider half was already on the residue/`physStepBudget` contract with the WALL
resolved (`paddedBitDecider_run`). This session did the **analogue for the map/reduction
half** (S3 migration, ROADMAP step 2) — `PolyTimeComputableLang.toFrameworkWitness'` was
still on the **wrong-budget** `overhead` `Compile_sound`. It is now retargeted onto the
residue contract, mirroring the decider side exactly:

- **Built the function-side WALL resolution** `Compile.paddedComputeTM` +
  **`Compile.paddedCompute_run`** (Compile.lean, end of file) — the analogue of
  `paddedBitDecider_run` but keeping the **full output tape** (no bit-test gadget), so a
  reduction can decode an arbitrary output register. `padRegsTM k ⨾ Compile c` on the
  narrow input, **no `k ≤ s.length`**; PROVEN sorry-free from the `padRegsTM` interface +
  `Compile_run_physical_residue` (residual `sorryAx` = the pinned leaf gadgets only).
- **Augmented `PolyTimeComputableLang`** with the WALL fields (mirrors `DecidesLang`):
  `regBound`/`usesBelow`/`width_le`/`noConsLen` + **`decode_agree`** (decode is
  insensitive to the `regBound` empty pad registers — the output register is `< regBound`,
  so `Cmd.eval_agree` transports it).
- **Retargeted `toFrameworkWitness'`** onto `paddedComputeTM` + a poly `padTimeBound` /
  `budget_ge` (same shape as the decider's `DecidesLang.padTimeBound`). It now **bypasses
  `Compile_sound` entirely** (just as `bitDecider_run` bypasses it on the decider side).
  Sorry-free as written.
- **`PolyTimeComputableLang'.toLang`** populates the new fields: `regBound`/`usesBelow`
  from `W`; `width_le` via `Cmd.UsesBelow_pos` (`0 < regBound`); `decode_agree` via
  `Cmd.eval_agree` at register `0`; `noConsLen` via a new pinned `PolyTimeComputableLang'.
  c_noConsLen` sorry (the **same** consLen-unary obligation `DecidesLang'.c_noConsLen`
  carries — Task 1 drops both).
- Relocated `inOPoly_of_le` upstream so the reduction bridge can use it.
- Build green (3358 jobs); `#print axioms CookLevin` unchanged
  (`[propext, sorryAx, Classical.choice, Quot.sound]`); `paddedCompute_run` +
  `toFrameworkWitness'` verified to depend only on `sorryAx` (via the pinned gadgets +
  `c_noConsLen`), no new independent gaps.

**Net effect:** the reduction side no longer routes through the wrong-budget
`Compile_sound` / `Compile_run_physical` / `Compile_polyBound` (overhead shape) — those
are now **DEAD** (nothing consumes them; `Compile_sound`'s `overhead` budget is
unprovable per Finding A — **do not try to prove them; they are superseded by the residue
route**). Every residual sorry on **both** the decider and reduction halves is now a
**pinned bottom-up gadget** (`padRegsTM` ✅ done; the 7 ops + 2 combinators) plus the
shared consLen-unary `c_noConsLen` and EvalCnf's encoding fields.

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
- **`DecidesBy.encode_size` is per-decider polynomial** (`encodeBound`+`_poly`+`_mono`);
  all constructors migrated. **Settled — do not re-tighten.**
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
  `_no_early_halt`), `loopBudget_le`. All axiom-clean.
- **5/12 ops PROVEN** in `compileOp_sound_physical_residue`: `appendOne`,
  `appendZero`, `clear`, `nonEmpty`, `head` (each carries the W-invariant ①).

---

# ▶ TOP-DOWN work stream — next steps

You assemble final pieces and design their proofs; create `sorry` lemmas when
provable; surface gaps early.

✅ **Both decider AND reduction bridges are now assembled** on the residue/`physStepBudget`
contract, the WALL is resolved on both (decider: `paddedBitDecider_run`; function/reduction:
`paddedCompute_run`), and `encode_size` is settled (polynomial). Every residual sorry on the
`sat_NP` decider path AND the `⪯p`/`toFrameworkWitness'` reduction path is now a **pinned
bottom-up gadget** (+ the shared `c_noConsLen`). The top-down frontier moves to the layer
**composition** lemmas and the **EvalCnf verifier** design:

1. **`PolyTimeComputableLang.comp` / `red_inNP_via_lang`** (PolyTime.lean, both `sorry`) —
   the layer composition lemmas the S3 reduction chain needs (ROADMAP step 2's tail). Now
   the **highest** top-down value. **Key leverage:** the *primed* `PolyTimeComputableLang'.
   comp` (line ~700) is already **sorry-free** and `toLang` now supplies ALL WALL fields
   (`regBound`/`usesBelow`/`width_le`/`noConsLen`/`decode_agree`) **generically** (e.g.
   `decode_agree` via `Cmd.eval_agree` at register 0, for *any* canonical witness). So for
   canonical-encoded types the unprimed `comp` can be obtained as
   `(Wg'.comp Wh').toLang` — no new per-composite WALL reasoning needed. The remaining
   genuine work is the *free* unprimed `comp` (arbitrary `encodeIn`/`decodeOut`): sequence
   `Wh.c` then `Wg.c` with a register shuffle, thread the cost bound (`Wh.cost_bound +
   Wg.cost_bound ∘ Wh.cost_bound`), and re-derive `decode_agree` for the composite's
   `decodeOut`. `comp_computes_of_bridge` (PROVEN) already isolates the encoding-
   compatibility gap (a real `comp` supplies `reEncode` from a canonical encoding) — prefer
   routing through the primed/`toLang` path over re-deriving it.
2. **Plan the EvalCnf inner bodies' contracts** (`processOneClause`/`processOneLiteral`/
   `memberCheck`, EvalCnfCmd.lean, all `sorry` `Cmd`s). These gate `evalCnfCmd_decides`/
   `_cost_bound`/`usesBelow`/`noConsLen`. Top-down: pin their `decides`/cost sub-contracts
   so the bottom-up DSL author has targets. (Coupled with Task 1's unary re-encoding —
   coordinate.) Also discharge `evalCnfDecidesLang`'s `usesBelow`/`noConsLen` once the inner
   bodies are concrete (each touches only registers 0..11).
3. **(validated, low priority) The `ifBit`/`forBnd` residue combinator interfaces**
   (`compileIfBit_sound_physical_residue` / `compileForBnd_sound_physical_residue`,
   Compile.lean ~9111/9164, both `sorry`) are **statement-validated**: `run_physical_
   residue_gen` typechecks its dispatch to them, so their budget/residue/W-invariant shapes
   compose. No restatement needed — they are now purely BOTTOM-UP build targets.
4. **(optional cleanup) Delete the dead `Compile_sound` / `Compile_run_physical` /
   `Compile_polyBound`** (overhead budget, superseded by the residue route, nothing
   consumes them). Low priority; scrub their doc references (several in PolyTime.lean
   headers still say "modulo the assumed `Compile_sound`" — now stale, the bridges consume
   `Compile_run_physical_residue` via `paddedCompute_run`/`paddedBitDecider_run`).

# ▶ BOTTOM-UP work stream — next steps

You build the gadgets the (pinned) contracts need. Build green per item;
`#print axioms`-clean. Probe each machine end-to-end (`#eval`) before proving.

**Both** the decider half (`sat_NP`) and the reduction half (`⪯p`/`toFrameworkWitness'`)
now rest on the SAME pinned gadgets below (`paddedBitDecider_run` and `paddedCompute_run`
both consume `Compile_run_physical_residue`). So discharging Tasks 2–4 closes **both**
halves at once.

1. ✅ **WALL gadget `Compile.padRegsTM` — DONE (sorry-free).** Run + trajectory + all
   shape/helper lemmas proven (see the PROVEN list). `paddedBitDecider_run`'s residual
   `sorryAx` is now **only** the leaf op gadgets below — so the **entire decider half of
   `sat_NP` rests on Tasks 2–4 alone**. The remaining bottom-up work:
2. **Task 1 — unary encodings + scratch operands** (gates all 7 ops). Restate
   `takeAt`/`dropAt`/`consLen` unary (length = the register's unary count, not
   `headD 0`); bump `consLen`'s `Op.cost`; add empty-scratch operands
   (`copy`/`tail`/`concat` need 1, `eqBit` needs 2); re-lay `Nat`/product/`List`
   encodings bit-level + `BitEncodable` instances; **re-lay `EvalCnfCmd.encodeState`
   UNARY** (the LIVE `sat_NP` encoding, cells `v+3`/`2` today) and discharge its
   `enc_bit` / `encodeIn_size`. After this, `consLen` preserves `BitState`, the
   `NoConsLen` side-conditions (`DecidesLang'.c_noConsLen` **and** the free-path
   `evalCnfDecidesLang.noConsLen`) are **dropped entirely**. Note the free path now
   *also* owes `evalCnfDecidesLang.usesBelow : UsesBelow evalCnfCmd 12` — provable once
   the inner bodies (Task 4 / EvalCnf) are concrete; each touches only registers 0..11.
3. **The 7 op gadgets** in `compileOp_sound_physical_residue` (Compile.lean
   ~8238): `copy`/`tail`/`concat` via `moveRegion2TM`; `eqBit` via compare-and-
   delete (2 scratch); `takeAt`/`dropAt` via counter-bounded transfer over
   `lenReg`; `consLen` unary. Each must establish the W-invariant ①
   (`State.size(out) + |res_out| ≤ State.size s + |res_in| + Op.cost o s`).
4. **The two stub machines (gate the `ifBit`/`forBnd` combinators):**
   - `compileTestBit t` (Compile.lean:1483): navigate to register `t` + `bitReadTM`,
     two-exit tester; then prove `compileIfBit_sound_physical_residue` via
     `branchComposeFlatTM_run` + `joinTwoHalts` + the rewind bracket.
   - `compileForBnd counter bound body` (Compile.lean:1631): a `loopTM` over the
     bound's unary length; then `compileForBnd_sound_physical_residue` via
     `loopTM_run`/`_no_early_halt` + the body's residue contract.

---

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
- Methodology: **skeleton-first, refine the highest-risk gap next, decompose
  `sorry`s don't elaborate them, probe before committing engineering, `def`+`sorry`
  over `axiom` (count = 0), build green between commits.**
