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
  → inTimePolyTM_evalCnf → inTimePolyLang_to_inTimePoly      (PolyTime.lean:140, SORRY — blocked, see WALL)
       → DecidesLang.toDecidesBy   (free encoding)            (PolyTime.lean:125, SORRY — blocked, see WALL)
            → Compile.bitDecider_run                          (Compile.lean ~9486; ✅ migrated to physStepBudget)
                 → Compile_run_physical_residue               (Compile.lean ~9225; PROVEN from the assembly,
                                                               sorry only via the leaf gadgets below)
       evalCnfDecidesLang : DecidesLang …                     (EvalCnfTM.lean:63; SORRY fields: encodeIn_size,
                                                               enc_bit — and now owes regBound/usesBelow/
                                                               noConsLen/width once the bridge is restated)
LEAF GADGETS (the only real remaining math under the assembly):
  compileOp_sound_physical_residue   (Compile.lean:8238; 5/12 ops PROVEN, 7 SORRY)
  compileIfBit_sound_physical_residue  (Compile.lean ~9111; SORRY — gated on real compileTestBit)
  compileForBnd_sound_physical_residue (Compile.lean ~9164; SORRY — gated on real compileForBnd)
```
The **canonical** path (`DecidesLang'` / `inNPLang_to_inNP`) is parallel infra,
not yet on the live `CookLevin` path; it bridges the same `bitDecider_run`.

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

## ★★ THE WALL — surfaced + RESOLVED (canonical bridge) 2026-06-07.

**The problem.** `Compile_run_physical_residue` (correctly) carries
`huses : Cmd.UsesBelow c k` and **`hk : k ≤ s.length`** — its per-op gadgets assume
the registers they touch already exist on the tape (`Op.inBounds`: gadgets navigate
by counting `0`-separators; a register past the tape width is not there to navigate
to). But the decider's *input* tape is narrow (`encodeState x = [enc x]`, width 1)
while composed programs touch `regBound > 1` registers — so `hk` is unsatisfiable —
**and** the framework's tight `DecidesBy.encode_size` (`≤ 2·size+4`, NP.lean) forbids
pre-padding the *input* encoding (each pad register adds a cell). The earlier
`DecidesLang'.reg_width` (`regBound ≤ 1`) was therefore a *false* `sorry`.

**The resolution — runtime tape-padding (CHOSEN, implemented at the canonical
bridge).** Grow the tape *during the run*: `Compile.padRegsTM k` maps `encodeTape s`
→ `encodeTape (s ++ replicate k [])` (width `≥ k`). The extra registers are empty, so
`c.eval` is unchanged register-wise (`Cmd.eval_agree`/`cost_agree`), and the *input*
encoding stays the tight single register (`encode_size` untouched). Composed before
the decider (`Compile.paddedBitDeciderTM := padRegsTM ⨾ bitDeciderTM`), it discharges
`k ≤ wide.length` for the inner `bitDecider_run`. So `Compile_run_physical_residue`
and `bitDecider_run` stay exactly as they are — the fix is purely additive.

**Status:** `Compile.paddedBitDecider_run` (Compile.lean) is **PROVEN** from the
`padRegsTM` interface + `bitDecider_run` via `composeFlatTM_run` — **no `k ≤ s.length`
hypothesis**. `DecidesLang'.toDecidesBy`/`toInTimePoly` are rewired to it (tight input
encoding, `physStepBudget`-shaped poly budget `DecidesLang'.padTimeBound`); the false
`reg_width` is **deleted**. The canonical decider bridge `inNPLang → inNP` is now
sorry-free **except** for the precisely-pinned obligations below.

**The single pinned BOTTOM-UP obligation that remains (replacing the false sorry):**
build `Compile.padRegsTM k` and discharge its interface lemmas (`_valid`/`_tapes`/
`_sig`/`padRegsExit_lt`/`_run`/`_traj`, all `sorry` in Compile.lean). The spec is
*true and buildable*: a `k`-fold `(stepRightTM ⨾ scanRightUntilTM 4 endMark ⨾
insertCarryTM 0 ⨾ rewindFromEndTM 4 endMark)`, each iteration inserting one `0`
delimiter just before the trailing `endMark`.

**Still open for the FREE/live path** (`DecidesLang.toDecidesBy`, what `sat_NP`
walks): the same padding applies, BUT `evalCnfDecidesLang`'s encoding is
`≤ 5·size+20 ⊄ 2·size+4`, so the free path *additionally* needs the framework's
`DecidesBy.encode_size` loosened to a per-decider linear `c₁·size+c₂` (ripples to
NP.lean:143's product lift) — an **owner decision**. Plus `c_noConsLen` (consLen,
Task 1). See the stream sections.

---

## ✅ What this session (top-down, 2026-06-07) did — the budget-shape migration

The C2 obligation was already **proven from the assembly** as the (then primed)
`Compile_run_physical_residue'` with the **correct `physStepBudget` budget**. This
session executed the **GAP-4 ripple** at the compiler→decider boundary:

- **Deleted** the unprimed `Compile_run_physical_residue` (the unprovable
  `overhead (size+cost)` budget — wrong degree AND dropped `s.length`, ROADMAP
  Finding A). **Renamed** the correct lemma to `Compile_run_physical_residue` (now
  THE obligation: `physStepBudget` budget, `UsesBelow`/`k ≤ s.length`/`NoConsLen`).
- **Retargeted `Compile.bitDecider_run`** to consume it: new params
  `(k) (hk : k ≤ s.length) (huses) (hnc)`, budget now
  `physStepBudget (State.size s + s.length + c.cost s + 2) (c.cost s) + 3`. So the
  live decider boundary rests on the **provable** budget shape.
- **Migrated `DecidesLang'.toDecidesBy` / `budget_ge` / `toInTimePoly`** to the new
  budget. Added `inOPoly_of_le` (pointwise domination) helper.

Then **resolved the WALL at the canonical bridge** (runtime tape-padding):
- Added `Compile.padRegsTM` + interface (`sorry` — the pinned gadget),
  `Compile.paddedBitDeciderTM`, and **proved `Compile.paddedBitDecider_run`** from
  the interface + `bitDecider_run` via `composeFlatTM_run` — **no `k ≤ s.length`**.
  Sorry-free bookkeeping: `get/size/BitState/agreeBelow_append_replicate_nil`,
  `paddedBitDeciderTM_valid/_tapes/_halt_shift`.
- Rewired `DecidesLang'.toDecidesBy`/`toInTimePoly` onto it with the poly budget
  `DecidesLang'.padTimeBound`; **deleted the false `reg_width`**. Tight input
  encoding preserved (`encode_size ≤ 2·size+4`).
- Build green (3358 jobs); `#print axioms CookLevin` unchanged
  (`[propext, sorryAx, Classical.choice, Quot.sound]`).

Net effect: the wrong-budget sorry and the false `reg_width` are gone; the WALL is
resolved by an additive, validated design whose only residual is the buildable
`padRegsTM` gadget. **Do not re-introduce an `overhead`-shaped budget anywhere** — it
is not superadditive and cannot compose (Finding #3 / A).

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

1. ✅ **WALL resolved at the canonical bridge** (runtime padding; `paddedBitDecider_run`
   proven, `reg_width` deleted). **Remaining top-down on the WALL = the FREE/live path:**
   give `DecidesLang.toDecidesBy` (free encoding, what `sat_NP` walks) the same
   padded-decider treatment. This needs (i) the same `paddedBitDecider_run` (reuse it),
   (ii) `DecidesLang` to expose `regBound`/`usesBelow`/`noConsLen` (add as fields —
   coordinate with the EvalCnf instance), and (iii) an **owner decision** to loosen the
   framework `DecidesBy.encode_size` from the tight `2·size+4` to a per-decider linear
   `c₁·size+c₂` (EvalCnf's encoding is `5·size+20`; ripples to NP.lean:143's product
   lift). Surface (iii) to the owner before implementing.
2. **Then close `inTimePolyLang_to_inTimePoly`** (the headline the free bridge feeds)
   by mirroring `DecidesLang'.toInTimePoly` (`inOPoly_of_le` + `physStepBudget_poly`/
   `_mono` are ready). This finishes the path `sat_NP` walks (modulo the leaf gadgets
   + EvalCnf's unary re-encoding, bottom-up).
3. **Retarget the reduction side** (`Compile_sound`, Compile.lean:8750, still an
   independent `sorry`; `PolyTimeComputableLang.toFrameworkWitness'`,
   PolyTime.lean) to the `physStepBudget` budget via `sound_of_run_residue` + the
   new `Compile_run_physical_residue`. Lower priority (not on the live in-NP path).

# ▶ BOTTOM-UP work stream — next steps

You build the gadgets the (pinned) contracts need. Build green per item;
`#print axioms`-clean. Probe each machine end-to-end (`#eval`) before proving.

1. **Build `Compile.padRegsTM` (THE pinned WALL gadget — interface already stubbed
   in `Compile.lean`).** Discharge `padRegsTM_valid`/`_tapes`/`_sig`/`padRegsExit_lt`/
   `padRegsTM_run`/`padRegsTM_traj`. Spec (true + buildable): map `encodeTape s` →
   `encodeTape (s ++ replicate k [])`, head rewound to `0`, within `padBudget`, no
   early halt. Suggested construction: `k`-fold `(stepRightTM ⨾ scanRightUntilTM 4
   endMark ⨾ insertCarryTM 0 ⨾ rewindFromEndTM 4 endMark)` (each iteration inserts one
   `0` delimiter before the trailing `endMark`). `#eval`-probe one iteration first.
   Discharging these makes `paddedBitDecider_run` (already proven on top) axiom-clean,
   which closes the canonical decider bridge `inNPLang → inNP`.
2. **Task 1 — unary encodings + scratch operands** (gates all 7 ops). Restate
   `takeAt`/`dropAt`/`consLen` unary (length = the register's unary count, not
   `headD 0`); bump `consLen`'s `Op.cost`; add empty-scratch operands
   (`copy`/`tail`/`concat` need 1, `eqBit` needs 2); re-lay `Nat`/product/`List`
   encodings bit-level + `BitEncodable` instances; **re-lay `EvalCnfCmd.encodeState`
   UNARY** (the LIVE `sat_NP` encoding, cells `v+3`/`2` today) and discharge its
   `enc_bit` / `encodeIn_size`. After this, `consLen` preserves `BitState` and the
   `NoConsLen` side-condition (`DecidesLang'.c_noConsLen`) is **dropped entirely**.
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
