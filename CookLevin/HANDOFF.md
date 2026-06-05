# Handoff — the computable layer / compiler (Risk C2)

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). **This file is the working plan for the compiler
(Risk C2)** — the one obligation the whole NP-completeness bridge sits on.

---

## The bigger picture (read once)

We are proving `theorem CookLevin : NPcomplete SAT`, real and unconditional.
NP-hardness is transported along a chain of poly-time reductions whose **tail**
(`FlatTCC → … → SAT`) is real, done mathematics. The remaining work routes through
one device: **the computable layer** — a tiny structured while-language (`Cmd`/`Op`
with explicit **cost** semantics) compiled **once** to a single-tape `FlatTM`
(`Compile`). Every verifier and reduction is then a short DSL program.

This is **Risk C2**. The framework bridge (`toFrameworkWitness'`, `inNPLang_to_inNP`)
and the live `sat_NP : inNP SAT` all reduce to one obligation:
**`Compile_sound` / `Compile_run_physical_residue`** (still `sorry`). Discharging it
is the job.

---

## ⚠ The invariant: `BitState` (and the design fork you must settle FIRST)

The compiled machine has a **fixed 4-symbol alphabet** (`sig = 4`). `encodeTape`
shifts each register cell `+1` (`0→1`, `1→2`), `0` separates registers, `3`
terminates. A cell `≥ 2` shifts to `≥ 3` and collides with the terminator, so
**every state touching the tape must be `Compile.BitState`** (all cells `∈ {0,1}`).
Numbers are therefore **UNARY** (`enc n = replicate n 1`). This is sound for the size
law because `encodable.size Nat = id` (verified): unary length `= n = size n`, so
`enc_size : len ≤ 2·size+1` holds. (No log-vs-unary blowup — the whole framework is
already unary-flavoured.)

### ★ BLOCKING DESIGN DECISION (owner, settle before writing Task 2)

The three top-level obligations — `Compile_sound` (Compile.lean:6047),
`Compile_run_physical` (6207), `Compile_run_physical_residue` (6237) — are stated
**without** a `BitState s` hypothesis, **but every per-op/per-fragment lemma
requires it** (`compileOp_sound_physical_residue`:5564 has `(hbit : BitState s)`, as
do all 10 fragment lemmas at lines 2393/2554/2901/3025/3160/3387/3535/3761/3823/4149).
So **the assembly cannot use the per-op contracts until `hbit` is added to the three
obligations.** This is the masked gap (Task 1). Adding it forces the bridge to supply
`BitState (encodeState x)` generically — and **how** to supply it is a real fork:

- **Option A (uniform).** Add a field `enc_bit : ∀ x, ∀ c ∈ enc x, c ≤ 1` to the
  `LangEncodable` class. *Every* instance must then be bit-level — including
  **`LangEncodable (List Nat) = id`** (currently allows arbitrary Nats!) and the
  product (its length-prefix is a Nat cell). A bit-level `List Nat` exists
  (`enc xs = (xs.map (replicate · 1 ++ [0])).flatten`, all cells `∈{0,1}`, splits on
  the bit-`0`s, `enc_size` ok) but it is **no longer the identity** — every program
  that treats a register as a raw list breaks. Widest ripple; cleanest invariant.
- **Option B (localized, RECOMMENDED).** Make bit-ness a property of *compiled*
  types only: a separate class `BitEncodable X` (or a `BitState (encodeState x)`
  field carried by the layer witnesses `DecidesLang` / `PolyTimeComputableLang'`),
  required by the bridge/`bitDecider_run`, discharged per concrete compiled type.
  Keeps `LangEncodable (List Nat) = id` and the generic toolkit untouched. The only
  live compiled type is **`cnf × assgn`** (`evalCnfCmd`, EvalCnfCmd.lean:128) — give
  it (and the GenNP input type for S1 later) a bit-level encoding; the sound-tail
  reductions are not compiled via the layer until the S3 migration.

I (this session) recommend **Option B**: bit-ness is genuinely a property of the
handful of types we compile, not of every `encodable`; it avoids disturbing the
native `List Nat = id` register and the whole `swap`/`mapFst`/`mapSnd` toolkit.
**Confirm with the owner before implementing — it sets the shape of Task 2.**

---

## ⚠⚠ Corrected sequencing (this session's headline risk finding)

The previous handoff's order — *"build the transfer gadget → takeAt/dropAt →
copy/tail/concat/eqBit → Tasks 1+2"* — is **inconsistent with its own findings**.
All 7 remaining ops are gated on Task 2:

- `takeAt`/`dropAt`/`consLen` read a length from a register **cell value**
  (`(s.get lenReg).headD 0`). Under `BitState` that value is `≤ 1`, so the current
  semantics can only take/drop 0 or 1 elements. They are **meaningless until Task 2
  restates the length as a UNARY count** (`= the register's length`). Building them
  first builds semantics Task 2 throws away.
- `copy`/`tail`/`concat`/`eqBit` must **preserve `src`** (`Op.eval` writes only
  `dst`). A mark-free single-tape copy that preserves the source needs a
  **guaranteed-empty scratch register** → an extra `Op` operand → an `Op`-signature
  change that is *"folded into Task 2"*.
- The only current witnesses using these ops (`swapCmd`/`mapFstCmd`/`mapSndCmd`,
  PolyTime.lean ~970/1200) are **built on the current non-unary product encoding**
  (they unpack via the Nat length-prefix). Task 2 rewrites them anyway — so a scratch
  operand added *before* Task 2 would force a `swapCmd` rewrite Task 2 then **rewrites
  again** (double work — exactly what we avoid).

**Correct order:** settle the fork → **Task 2 (coupled batch) FIRST** → then the op
gadgets → Finding A budget → assembly. The *raw-tape transfer gadget* (below) is the
**one** op-related piece that is encoding-agnostic and may be built before/concurrent
with Task 2.

---

## ✅ Probe verdict: the transfer-gadget design is GO (validated this session)

The recommended op realization (deep-pass "Finding B") is a **counter-free two-phase
transfer** that reuses **only already-proven gadgets**. Validated end-to-end by
`#eval` on real `encodeTape`s (probe files were `/tmp/probe*.lean`; reproduce with
`env LEAN_PATH=$(lake env printenv LEAN_PATH) lean <file>`):

**Move-one-bit primitive** (the inner loop body of each phase): from
`encodeTape s ++ res`, do
`navigateAndTestTM src` → (content) `bitReadTM` (reads bit into the state) →
`deleteCarryTM` (delete src's front cell, left-shift, `+1` `0`-residue) → rewind to 0
→ `appendAtTM (bit+1) dst` → rewind to 0. Probed (`src=[[1,0],[1]]`, move reg0's
front bit to reg1): `[3,2,1,0,2,0,3] → [3,1,0,2,2,0,3,0]` =
`encodeTape [[0],[1,1]] ++ [0]` (terminator-free residue). **Works for `dst>src`
AND `dst<src`** (probed both). ⚠ **The append symbol is `bit+1`, not `bit`** (the
encoding shifts `+1`; `appendAtTM (bit+1)` — already the convention used by the proven
append op, Compile.lean:2396). Each phase is a `clear`-style `loopTM` that **terminates
by emptying a register** (the proven termination mode), so `loopTM_run` /
`loopTM_no_early_halt` apply directly.

**Per-op realizations** (all from the move primitive, after Task 2 adds scratch `sc`):
`copy dst src sc` = move `src→sc` (src empties) ⨾ move `sc→src`&`dst` (sc empties,
src rebuilt, dst built, order preserved); `tail` = drop the first transferred bit for
`dst`; `concat` = two copies; `eqBit` = transfer both, AND the front bits;
`takeAt`/`dropAt` bound phase 2 by the unary `lenReg`; `consLen` similar. **No new
low-level TM is needed** — the rotation/`copyBlockTM` sketches from older handoffs are
dropped.

**Probe verdict: GO.** No tape-level snag; the only new requirement is the empty
scratch operand (Task 2). Build the move primitive + its run/`_no_early_halt`/budget
**mirroring the proven `clearRegionTM_run` chain** (it is the same `loopTM` shape with
an extra `appendAtTM` in the body). **Re-probe each assembled machine end-to-end
before proving its run lemma** (architecture bugs are invisible to validity proofs).

---

## The ordered plan from here

**0. (owner) Settle the BitState fork** (Option A vs B above). Recommended: B.

**1. Task 2 — bit-level encodings + restated ops + scratch operand (one coupled
green-landing batch).** Per the fork decision:
- Encodings: `Nat` unary (`replicate n 1`); product/list length-prefixes unary &
  self-delimiting (or, Option B, a bit-level `cnf × assgn` encoding only). Re-prove
  `dec_enc`/`enc_size` (unary roughly doubles size — loosen `enc_size`'s constant if
  needed; ripples to `NP.lean` `DecidesBy.encode_size` and the decider budget; both
  need only `inOPoly`/`monotonic`).
- Add `BitState s` to the 3 obligations; supply `BitState (encodeState x)` at the
  bridge per the fork. Confirm `BitState` is `Op.eval`-preserved (`BitState_set`,
  `BitState_set_tail` exist).
- Restate `Op.takeAt`/`dropAt`/`consLen` so length = the register's **unary count**,
  not `(s.get lenReg).headD 0`.
- Add an empty-scratch operand to `copy`/`tail`/`concat`/`eqBit`
  (`copy dst src sc`, precondition `s.get sc = []`, `sc < length`, `sc ∉ {dst,src}`;
  `Op.eval` ignores `sc` and the gadget restores it to `[]`).
- Re-derive `swapCmd`/`mapFstCmd`/`mapSndCmd` against the new encoding & signatures
  (witnesses already allocate spare scratch registers).

**2. Build the 7 op gadgets** (`compileOp_sound_physical_residue`, the 7 remaining
`sorry`s at Compile.lean:5610–5626): the move-bit primitive (probe-validated) + the
two-phase transfer loop, wired per op. **Templates:** `clearRegionTM_run` (the
`loopTM` chain to mirror), `opNonEmpty_run` (branch-merge engine + budget),
`opHead_run` (nested branch + `bitReadTM` reuse). Bump the per-op budget when a
chain exceeds the current `9·L²+9·L+30` (3 sites: statement + the two relaxing
`le_trans … (by omega)` in the proven append/clear cases).

**3. Finding A — restate the top-level budget (do this WITH the assembly, not
before).** The stated `overhead(size+cost)` with `overhead m = (m+1)²` is **too small
on two counts**: per-op budgets are `Θ(L²)` (multi-cell ops) so summing `~cost` of
them is **cubic**, and `L = size + s.length + 2` includes the **register count
`s.length`** which `overhead(size+cost)` drops. Restate as
`overhead(State.size s + s.length + c.cost s)` with `overhead` bumped to **cubic**
(e.g. `9·(m+1)³`). Downstream consumers (`bitDecider_run`, `DecidesBy` budgets,
`toFrameworkWitness'.timeBound`) use only `overhead_poly`/`overhead_mono`
(degree-agnostic) → ripples mechanically. Stays poly on the live path (`encodeState x`
is 1 register; the program adds a constant `regBound`).

**4. Assemble** `Compile_run_physical_residue` → `Compile_sound` by induction on
`Cmd`: per-`Op` from step 2, `seq` from `compileSeq_sound_physical_residue` (PROVEN),
`ifBit`/`forBnd` from their residue siblings (`branchComposeFlatTM_run` / `loopTM_run`
+ `loopTM_no_early_halt`; the `compileIfBit`/`compileForBnd` residue contracts at
~5884/5934 are stated, sorry'd). This discharges C2; downstream unlocks S3 migration,
C7 verifiers, C8 hardness, S1 tableau.

---

## Inventory — the C2 working set

| Name (file) | Role |
|------|------|
| `Compile.encodeTape`/`encodeRegs`/`shiftReg`/`BitState`/`ValidResidue`/`decodeTape` (`Lang/Compile.lean`) | `sig=4` tape encoding; the standing bit invariant; residue-tolerant contract |
| `compileOp_sound_physical_residue` (5564) | per-op contract, `(hbit : BitState s)`, budget `9·L²+9·L+30`. **PROVEN:** `appendOne`/`appendZero`/`clear`/`nonEmpty`/`head`. **`sorry` (7):** `copy`/`tail`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen` (5610–5626) |
| `opNonEmpty`(+`_run`), `opHead`(+`_run`), `bitReadTM`, `opInnerBit`, `clearOnlyBranchBody` | ✅ the two proven cross-register ops + the **branching-op templates** (`joinTwoHalts` branch-merge engine; `bitReadTM` = bit-value cell test; nested 2-way branches) |
| `clearRegionTM_run` ← `clearBody_delete_run`/`_done_run` ← `stepDeleteRewind_run` (4148+, 200+) | **the `loopTM` chain to MIRROR** for the transfer gadget (run + trajectory + quadratic budget; threads a `∧ t ≤ …` through every layer) |
| `loopTM`(+`_run`/`_no_early_halt`), `loopBudget`(+`_le`), `clearBudget_arith` (`TMPrimitives`, `Compile`) | counted loop (terminate-by-emptying mode) + reusable budget closers |
| `navigateAndTestTM` (+`_exit_content`/`_delim`), `appendAtTM` (+`appendAt_run`, exit), `deleteCarryTM`(+`_run`/`_no_early_halt`), `scanLeft`/`rewindTwoPhaseTM` | ✅ the proven gadget pieces the move primitive composes |
| `compileSeq_sound_physical_residue` (PROVEN); `compileIfBit`/`compileForBnd` residue (~5884/5934, stated `sorry`) | the `Cmd`-constructor assembly pieces |
| `Compile_run_physical_residue` (6237), `Compile_sound` (6047) | **the C2 obligations (`sorry`)** — add `(hbit : BitState s)` (Task 1) |
| `LangEncodable` (`enc`/`dec`/`enc_size`) + instances `Nat`/`List Nat`/product (`Lang/PolyTime.lean` 440/640/839) | **Task 2 rewrites these bit-level** per the fork |
| `swapCmd`/`mapFstCmd`/`mapSndCmd` (PolyTime.lean ~970/1200) | only users of `takeAt`/`dropAt`/`consLen` — re-derived in Task 2 |
| `toFrameworkWitness'` (632), `bitDecider_run` (6297), the `DecidesBy` decider (PolyTime ~1700) | the bridge that consumes the obligations — gains the `BitState` supply (fork) |

---

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (`lake` is **not** on
  PATH; LSP/most MCP features can't find it). First build slow; one module ~10s
  (`lake build Complexity.Lang.Compile` to iterate). Commit per logical step, green.
- **Probe** a built machine end-to-end *before* proving its run lemma:
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/x.lean` with
  `import Complexity.Lang.Compile`, `open Complexity.Lang`, and
  `runFlatTM N M { state_idx := M.start, tapes := [([], 0, Compile.encodeTape s)] }`.
  Namespaces: `Compile.*`, `ClearGadget.*`, `AppendGadget.*`, `ShiftTape.*`,
  `Compile.bitReadTM`. **Every gadget exits with its head on the trailing terminator**
  — rewind-bracket, don't assume "left of" it.
- **Axiom-check** via a scratch file: `#print axioms <name>` must show only
  `propext`/`Classical.choice`/`Quot.sound` — **no `sorryAx`**.
- **Append a BIT `b`** = `appendAtTM (b+1)` (the encoding shifts `+1`). `deleteCarryTM`
  deletes the cell **left of the head** (head at `pre.length+1` deletes index
  `pre.length`); `navigateAndTestTM src` lands the head **on** src's first content cell.
- **`omega` can't see through `Var := Nat`** (use a `Nat`-typed `bit` param, not `Var`),
  **record projections / `def`-constants** (`show` the reduced form first), nor a
  `set x := e` for hyps created *after* the `set` (`rw [hxdef] at h` first).
- Branching-op correctness for `dst = src`: **read `src` BEFORE clearing/writing `dst`**
  (`Op.inBounds` does NOT force `dst ≠ src`).
- Methodology (do not deviate without reason): **skeleton-first, refine the
  highest-risk gap next, decompose `sorry`s don't elaborate them, probe before
  committing engineering, `def`+`sorry` over `axiom` (count = 0).**
