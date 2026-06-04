# Handoff — the computable layer / compiler (Risk C2)

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). **This file is the working plan for the compiler
(Risk C2)** — what we are building, why, the invariant you must not break, the
ordered tasks, and an inventory of the code you will touch.

---

## The bigger picture (read once)

We are proving `theorem CookLevin : NPcomplete SAT`, real and unconditional.
NP-hardness is transported along a chain of poly-time reductions
`GenNP ⪯p … ⪯p FlatTCC ⪯p … ⪯p SAT`; the **sound tail** (`FlatTCC → … → SAT`) is
real, done mathematics. The remaining work is the *front* and the `⪯p` / in-NP
**interfaces** — and those all route through one device:

**The computable layer.** Hand-rolling each verifier/reduction as a raw `FlatTM`
overran budget ~10×. Instead we have a tiny structured while-language
(`Cmd`/`Op`, with explicit **cost** semantics) compiled **once** to a single-tape
`FlatTM` (`Compile`). Every verifier and reduction is then a short DSL program.
This is the linchpin, **Risk C2**: the framework bridge (`toFrameworkWitness'`,
`inNPLang_to_inNP`) and the *live* `sat_NP : inNP SAT` both reduce to a single
obligation — **`Compile_sound` / `Compile_run_physical_residue`** (still `sorry`).
Discharging it is the job.

---

## ⚠ The invariant you must not break: `BitState`

The compiled machine has a **fixed 4-symbol alphabet** (`sig = 4`):
`encodeTape s = 3 :: (encodeRegs s ++ [3])`, where each register's bits are
shifted `+1` (`0→1`, `1→2`), `0` separates registers, and `3` is the terminator.
**A register cell `≥ 2` would shift to `≥ 3` and collide with the terminator.** So
every state that touches the tape must be `Compile.BitState` (all cells `∈ {0,1}`).

**The mistake the plan already corrected (do NOT reintroduce it).** The
`LangEncodable` encodings were Nat-valued — `enc (n : Nat) = [n]`, and the product
`enc (x,y) = (enc x).length :: (enc x ++ enc y)` puts a *length* (a Nat) in one
cell — and `takeAt`/`dropAt`/`consLen` were defined around Nat length cells. That
is **incompatible** with the BitState compiler (it would put symbols `> 3` on the
tape), and `Compile_sound` was even mis-stated *without* a `BitState` hypothesis,
which hid the gap. The gap is on the **live** in-NP path
(`CookLevin → sat_NP → evalCnfCmd → Compile`), masked today only by sorries.

**The decision (owner-approved): everything is bit-level; numbers are UNARY.**
This keeps `sig = 4`/`BitState` (so all proven gadgets stay valid), keeps sizes
polynomial (every length/index `≤` input size), and — the key payoff — a unary
length register *is a loop counter*, which makes the hard data-movement gadgets
**mark-free** (see Task 3).

---

## The plan — option B (unary lengths, bit data), ordered

> **Status (this session).** Build green (3358 jobs). **✅ Task 3 `nonEmpty` is
> FULLY PROVEN and axiom-clean** (`compileOp_sound_physical_residue` now discharges
> the `nonEmpty` case; only `propext`/`Classical.choice`/`Quot.sound`). This is the
> first cross-register op done and it builds the whole **branch-merge machinery**
> the other branching ops reuse. **Recommended order from here:** `head` (needs a
> bit-*value* read — see Class A below), then `eqBit`, then the Class-B block-copy
> ops, then Tasks 1+2 together (**one monolithic change** — see ⚠ below), then
> Task 4.
>
> **Budget bumped:** `compileOp_sound_physical_residue`'s budget is now
> `9·L² + 9·L + 30` (multi-phase Class-A ops have linear overhead on top of the
> `clear`'s `9·L²`). When you add an op whose chain is longer, bump again (3 sites:
> statement + the relaxing `le_trans … (by omega)` in each proven case).
>
> **⚠ Tasks 1 & 2 are coupled and large; do NOT start them piecemeal.** Adding
> `BitState` to `Compile_sound` forces the bridge (`toFrameworkWitness'`,
> `bitDecider_run`) to supply `BitState (encodeState x)`, which requires a new
> `LangEncodable` field `enc_bit : ∀ x, ∀ c ∈ enc x, c ≤ 1`. To satisfy that field
> **every** instance must be bit-level — including `LangEncodable (List Nat) = id`
> (currently allows arbitrary Nats!) and the product (Nat length-prefix cell). So
> Task 2 must re-encode `Nat`/`List Nat`/product unary **and** re-derive
> `swap`/`mapFst`/`mapSnd` (they decode via the Nat prefix) **and** loosen
> `enc_size` (unary prefix ≈ doubles size — ripples to `NP.lean`
> `DecidesBy.encode_size` and the decider budget) in one green-landing batch.
> Budget a full session; it is mechanical but wide.

### ⚠ Risk analysis & recommended sequencing (2026-06-04, probe-validated)

A focused risk pass on the 8 remaining ops (with `#eval` probes). **Verdict: the
plan is feasible and C2 is converging, but the Class-B ops have ONE unresolved
design decision (the scratch counter) that you must settle BEFORE building them.**

**(1) Do `head` next — lowest risk, counter-free.** `head dst src` writes `[]` /
`[0]` / `[1]` (≤1 cell), so it reuses the *entire* `nonEmpty` engine
(`clearAppendM_run` + the `joinTwoHalts` branch-merge). The **only** new piece is a
**bit-*value* test** (branch cell `=1` vs `=2` vs delim) — a direct mirror of
`ClearGadget.delimTestTM` (which already branches delim-vs-content). `head` is a
3-way branch (empty→`[]` i.e. just clear `dst`; bit0→`[0]`; bit1→`[1]`): nest two
`joinTwoHalts` merges, or merge a 3-exit machine. Estimate ~300–400 LOC.

**(2) The 6 block-copy ops + `eqBit` need a guaranteed-empty SCRATCH register —
this is the one real gap. Resolve it before building.** The "counter + rotation =
mark-free block copy" claim is **algorithmically correct** (probed: rotating `src`
one bit/iteration restores `src` after `|src|` iters while `dst` accumulates the
copy). BUT `loopTM` terminates by *reading a shrinking tape region* (cf. `clear`,
which loops until the register empties), and a rotated `src` never shrinks — so the
loop must consume a **scratch counter** (`replicate |src| 1`, cleared over the run).
`Op.eval` does **not** designate a free register, and the probe shows using a
register past `s.length` **adds a trailing register** (extra `0` separator ⇒ the
exit tape is `≠ encodeTape output ++ residue`; breaks the residue contract).
**Recommended resolution (cheapest, validated):** give these ops an explicit
**empty-scratch operand** (`copy dst src sc`, …) with contract precondition
`s.get sc = []`, `sc < s.length`, `sc ∉ {dst,src}`; `Op.eval` is unchanged
(`s.set dst (…)` — the gadget restores `sc = []`). The witnesses already allocate
scratch registers (`swapCmd` uses regs 1–5; reductions use `regBound+k`), so they
pass a known-empty one. **This Op-signature change is best folded into Task 2**
(the witnesses are re-derived there anyway) — i.e. do Task 2's `Op` restatement and
the scratch-operand addition together, then build the Class-B gadgets against the
new signatures. (Alternative without an `Op` change: a temporary trailing register
+ delete-its-separator cleanup, or scratch in the residue past the terminator —
both add gadget machinery and are riskier; not recommended.)

**(3) Build `copy` FIRST among the rotation ops, and `#eval`-probe the rotation
machine end-to-end as a real `FlatTM` before proving** (compose `navigate` +
`deleteCarryTM` (front) + `insertCarryTM`/`appendAtTM` (src-back & dst-back) +
counter-consume into a `loopTM` body; verify exit head + exact tape on a real
`encodeTape`). `copy`'s gadget is the rotation infrastructure; `tail` (skip first
bit), `concat` (two copies), `takeAt`/`dropAt` (`lenReg` is the counter directly —
**these two need NO scratch**, the unary `lenReg` already shrinks), `consLen`
(prepend a unary length) then reuse it. **`eqBit` is the hardest** (lockstep compare
of two registers, or rotate-both-and-AND) — do it last, and first check whether the
live verifier (`EvalCnfCmd`) only needs `eqBit` against a 1-cell constant (a much
cheaper special case).

**Sequencing:** `head` → (settle the scratch-operand decision) → `copy` (probe +
rotation infra) → `tail`/`concat`/`takeAt`/`dropAt`/`consLen` → `eqBit` →
Tasks 1+2 (fold the `Op` scratch change in here) → Task 4 (assemble).

**Bigger-picture sanity check.** C2 is on a converging track: the per-op cost drops
sharply as infrastructure compounds (the `nonEmpty` branch-merge engine and the
future rotation gadget are *one-time* builds). Estimate **~4–7 more sessions** to
finish C2. The overall proof is still ~15–25K LOC dominated by **S1 (the Cook 2D
tableau, ~6–11K LOC)** — C2 is necessary but a fraction of the whole. The compiler
strategy remains sound; **no trigger for the destination-B fallback.** The single
thing that could still derail C2 is a tape-level snag in the rotation realization —
which is exactly why step (3) says *probe `copy` end-to-end before committing the
proof engineering.*

**1. Make the `BitState` invariant explicit and true.**
- Add `(hbit : Compile.BitState s)` to `Compile_sound` and
  `Compile_run_physical_residue` (and thread it through the assembly).
- Give `LangEncodable` a guarantee that every `encodeState x` is `BitState` (a new
  field, or a derived lemma per instance), so the bridge `toFrameworkWitness'`
  can supply `hbit`. Confirm `BitState` is preserved by `Op.eval` (it is the
  standing convention — `BitState_set`, `BitState_set_tail` already exist).

**2. Re-encode numbers as unary; keep every cell `∈ {0,1}`.**
- `LangEncodable Nat`: `enc n = List.replicate n 1` (not `[n]`). Make the product
  length-prefix a unary block (self-delimiting with the existing `0` separators).
  Re-prove `dec_enc` and `enc_size` (unary length is `≤` size, still linear/poly).
- Restate `Op.takeAt`/`Op.dropAt`/`Op.consLen` so the length is a *unary count*
  (the register's length / number of `1`s), not `(s.get lenReg).headD 0` of a Nat
  cell. **Only three witnesses use these ops** — `swapCmd`, `mapFstCmd`,
  `mapSndCmd`, all in `Lang/PolyTime.lean` — so the re-prove surface is small.

**3. Build the 9 cross-register ops (`compileOp_sound_physical_residue`).**
`Op.eval` of each is `s.set dst (f (s.get src…))`. **✅ `nonEmpty` DONE; 8 left**
(`copy`/`tail`/`head`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`). Two classes:

**Class A — `nonEmpty` (✅ DONE), `head`, `eqBit` (`≤ 1`-cell output).** The
**proven `nonEmpty` machine and the reusable building blocks** (all in
`Compile.lean`, axiom-clean):
- `Compile.opNonEmpty dst src` — the `CompiledCmd`: `joinTwoHalts (nonEmptyRawM …)
  h1 h2` where `nonEmptyRawM = branchComposeFlatTM (navigateAndTestTM src) body₂
  body₁ exit_content exit_delim`, `bodyᵢ = nonEmptyBranchBody dst ins` =
  `rewind (scanLeftUntilTM 4 3) ⨾ clear dst ⨾ append bit`. **Read `src` FIRST,
  clear `dst` AFTER** (so it is correct for `dst = src` — verified). Structural
  `CompiledCmd` fields proven via the new halt-characterization helpers.
- `Compile.opNonEmpty_run` — the full residue contract (run + trajectory + budget
  `9·L²+9·L+30`); the **template to copy** for any branching op. Cases on
  `s.get src = []` and feeds `joinTwoHalts_reaches_kept` (content) /
  `joinTwoHalts_reaches_demoted` (delim, the `+1` bridge step).
- **Reusable infrastructure (use verbatim):**
  - `Compile.clearAppendM_run` — clear `dst` ⨾ append bit ⇒ `encodeTape (s.set dst
    [bit]) ++ (res ++ replicate |s.get dst| 0)`, head 0. **`head`/`eqBit` reuse this
    to write their answer bit.**
  - `Compile.nonEmptyBranchBody_run` — rewind-from-`navtest`-exit ⨾ clearAppend.
  - `Compile.navTestReg_run_content`/`_run_delim` + `_traj_content`/`_traj_delim`
    — residue-tolerant `navigateAndTest` run + no-early-halt (≠ both exits).
  - `Compile.joinTwoHalts_reaches_kept`/`_reaches_demoted` — **the branch-merge
    engine**: given the raw branch run (to kept exit `h1` / demoted exit `h2`) +
    trajectory + `h1`/`h2` are halts + `h1≠h2` (+ tape-symbol bound for demoted),
    produce the `joinTwoHalts` run-to-`h1` + trajectory. Any 2-way branching op
    plugs straight in.
  - `joinTwoHalts_step_to_h1` (bridge step `h2→h1`) ← `stepFlatTM_bridge_prefix`
    (new, **`TMPrimitives.lean`**, generic bridge step for any
    `bridgeEntries sig src dst ++ rest` trans); `joinTwoHalts_run_eq_weak`
    (run-preserve while intermediate `≠ h2`); `joinTwoHalts_halting_false`;
    `branchComposeFlatTM_M2_halt_intro`/`_M3_halt_intro`,
    `Compile.branchComposeFlatTM_halt_only`, `composeFlatTM_halt_unique`.
- **⚠ `head`/`eqBit` are NOT a copy-paste of `nonEmpty`.** `navigateAndTestTM`
  branches only **delim vs content** — content covers BOTH bit `0` (cell `1`) and
  bit `1` (cell `2`), so it does *not* read the bit value. `head dst src` =
  `[src.head]` needs the actual first bit ⇒ build a **bit-value branch** (read the
  cell, branch `1`-vs-`2`; extend `delimTestTM`/`navigateAndTestTM` to a 3-way, or
  add a `navigateAndReadBitTM`). Then it is `clearAppendM` with the read bit. The
  empty case writes `[]` (just `clear dst`, no append) — a third branch, so `head`
  is a 3-way branch (`joinTwoHalts` twice, or a nested merge). `eqBit dst src1
  src2` compares two full registers — a **cell-by-cell `loopTM` compare** (more
  than `nonEmpty`); scope it as its own gadget.

**Class B — `copy`/`tail`/`concat`/`takeAt`/`dropAt`/`consLen` (block copy).**
Counter + rotation = non-destructive block copy, no spare symbol:
- Each `loopTM` iteration moves `src`'s front cell to both `dst` and `src`'s back;
  after `N` (= counter) iterations `src` is rotated full-circle (unchanged), `dst`
  holds the copy. `takeAt`/`dropAt`: `lenReg` (unary) is the counter directly.
  `copy`/`tail`/`concat`: first **count** `src`'s length into a scratch register
  (mirror the `clear` count loop), then rotate-copy. **Probe the rotation machine
  with `#eval` before proving.** Budget: per-iteration linear `∧ t ≤ c·L + d`,
  assemble with `Compile.loopBudget_le` + a `Compile.clearBudget_arith`-style
  closer → quadratic (bump the op budget again).

**⚠ `#eval`-probe every new machine end-to-end before proving its run lemma** —
architecture bugs (wrong exit head, off-by-one slot) are invisible to validity
proofs and the proofs are expensive. Probe template (run a composed `FlatTM` on a
real `encodeTape`, check the exit state + head + tape):
`(runFlatTM N M (initFlatConfig M [Compile.encodeTape s])).map (·.tapes)` via the
`LEAN_PATH` lean invocation.

**★ The proven `nonEmpty` chain is the template for the next branching op:
`Compile.opNonEmpty_run` (`Compile.lean`).** It shows verbatim how to: decompose
the tape, build the navtest run + trajectory, apply `branchComposeFlatTM_run_pos`
/`_run_neg`, convert the branch output state (commute to `h1`/`h2`), and merge via
`joinTwoHalts_reaches_kept`/`_demoted`. The older `Compile.clearBody_delete_run`
(~`Compile.lean` 2750) is the lower-level `navtest → branch → rewind` example.

<details><summary>(historical, now superseded) the clearBody template walkthrough</summary>
shows how to: decompose the tape (`htape_nav`),
bound `navSteps`/`regBlocks`, **discharge the `rewindToStart_run`/`_traj` cell
conditions** (the fiddly part — copy lines ~2884–2921), set the
`branchComposeFlatTM` symbol bound, and assemble. For `nonEmpty`, swap the two
sub-machines for `thenM`/`elseM` (rewind ⨾ append), and (unlike clear's loop)
**merge the two branch exits with `joinTwoHalts`** as described above.
</details>

**4. Assemble `Compile_run_physical_residue` → `Compile_sound`.** Compose per-op
contracts with `compileSeq_sound_physical_residue` (done), the `compileIfBit` /
`compileForBnd` residue contracts (`branchComposeFlatTM_run` / `loopTM_run` +
`loopTM_no_early_halt`), then induction on `Cmd`. This discharges the C2 obligation
the whole bridge sits on. Downstream then unlocks: S3 migration (ROADMAP step 2),
C7 verifiers (`evalCnfCmd`), C8 hardness, S1 tableau.

---

## Inventory — the C2 working set

### Machine model — `Complexity/Complexity/MachineSemantics.lean`
| Name | Role |
|------|------|
| `FlatTM`, `FlatTMConfig`, `FlatTMTransEntry` | single-tape TM (head = index into `right`; `left` unused) |
| `stepFlatTM`, `runFlatTM`, `currentTapeSymbol`, `haltingStateReached`, `initFlatConfig` | semantics; `runFlatTM` stops at a halt state or when no transition matches |

### Combinators — `Complexity/Complexity/TMPrimitives.lean` (~4K LOC, sound)
| Name | Role |
|------|------|
| `composeFlatTM` / `branchComposeFlatTM` / `loopTM` (+ `_run`, `_no_early_halt`, `_valid`) | sequence / 2-way branch / counted loop; `sig = max` (so a higher-`sig` gadget composes — not needed under plan B) |
| `loopBudget`, `loopTM_no_early_halt` | per-iteration step budget; the loop never early-halts |

### Compiler & encoding — `Complexity/Lang/Compile.lean`
| Name | Role |
|------|------|
| `Compile.encodeTape` / `encodeRegs` / `shiftReg` / `endMark` / `decodeTape` | the `sig=4` tape encoding; `decodeTape` ignores residue + head |
| `Compile.BitState` | the standing invariant (cells `∈ {0,1}`); `BitState_set`, `BitState_set_tail` preserve it |
| `Compile.encodeTape_length`, `encodeTape_set_length`, `encodeRegs_no_endMark` | length balance; why BitState is required |
| `Compile.ValidResidue`, `TapeOK`, `decodeTape_encodeTape_append` | residue-tolerant contract (the tape never shrinks, so deletion ops leave terminator-free residue) |
| `rewindBracket`, `rewindBracket_transport`, `opAppendBit_physical_residue` | **template for any head-moving op**: wrap a compute machine with the two-phase rewind, demote the extra halt → unique-exit `CompiledCmd` |
| `compileOp_sound_physical_residue` | per-op contract; budget `9·L²+9·L+30`. PROVEN: `appendOne`/`appendZero`/`clear`/**`nonEmpty`**. `sorry`: `copy`/`tail`/`head`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen` (8) |
| `Compile.opNonEmpty` (+ `_run`) | **✅ NEW, PROVEN** the `nonEmpty` `CompiledCmd` (navtest-first; `joinTwoHalts` merge) + its full residue contract — **the template for any branching op** |
| `Compile.clearAppendM_run`, `nonEmptyBranchBody_run` | **NEW** clear `dst` ⨾ append bit (head 0); rewind ⨾ clearAppend — reuse for `head`/`eqBit`'s answer-bit write |
| `Compile.navTestReg_run_content`/`_run_delim`/`_traj_content`/`_traj_delim` (+ `skipped_length`/`skipped_ok`) | residue-tolerant `navigateAndTest` reading + no-early-halt of register `src` (content ⇒ non-empty, delim ⇒ empty). **NB only delim-vs-content, not the bit value** — `head`/`eqBit` need a bit-value read |
| `Compile.joinTwoHalts_reaches_kept`/`_reaches_demoted`, `joinTwoHalts_step_to_h1`, `joinTwoHalts_run_eq_weak`, `joinTwoHalts_halting_false` | **NEW branch-merge engine**: a 2-way `branchComposeFlatTM` (`joinTwoHalts`-merged) op plugs straight in |
| `stepFlatTM_bridge_prefix` (`TMPrimitives.lean`), `branchComposeFlatTM_M2_halt_intro`/`_M3_halt_intro`, `branchComposeFlatTM_halt_only`, `composeFlatTM_halt_unique` | **NEW** generic bridge step + branch halt-state characterization |
| `compileSeq_sound_physical_residue` | PROVEN (additive budget `t₁+1+t₂`) |
| `Compile_run_physical_residue`, `Compile_sound` | **the C2 obligations (`sorry`)** — need the `BitState` hypothesis (Task 1) |
| `Compile.loopBudget_le`, `Compile.clearBudget_arith` | **reusable budget template** (per-iteration `M` → `(n+1)·M`; quadratic closer) |

**The `clear` op chain (the model to copy for every `loopTM`-based op):**
`clearRegionTM_run` (loop, run + trajectory + budget `≤ 9·L²+9`) ← `clearBody_delete_run` /
`clearBody_done_run` (`≤ 6·L+12`) ← `stepDeleteRewind_run` (`≤ 4·L+9`) ←
`encodeTape_residue_twoPhaseRewind` (`≤ L+3`). Each existential carries a
`∧ t ≤ <linear/quadratic>` bound; `clearRegionTM_run` proves every loop tape has
the same length `L` and `n+2 ≤ L`.

### Gadget library (sorry-free; sig=4)
| File | Gadgets |
|------|---------|
| `Lang/ClearGadget.lean` | `navigateToRegTM`, `navigateAndTestTM` (read+branch), `clearBodyRawTM`, `clearRegionTM`; `navSteps`, `navSteps_le` (loop-count) |
| `Lang/AppendGadget.lean` | `appendAtTM` (insert a bit at register `dst`), `regBlocks`, `appendAt_run` |
| `Lang/ScanLeft.lean` | `scanLeftUntilTM`, `stepLeft/RightTM`, `rewindToStart_run`, `rewindTwoPhaseTM` (the two-phase rewind) |
| `Lang/ShiftTape.lean` | `insertCarryTM` / `deleteCarryTM` (single-cell carries; the rotation in Task 3 builds on these) |

### Layer semantics & bridge
| Name (file) | Role |
|------|------|
| `Op`, `Cmd`, `State` (`Lang/Syntax.lean`) | the while-language; `State = List (List Nat)` (registers) |
| `Op.eval`, `Op.cost`, `Cmd.eval`, `Cmd.size_eval_le`, `State.size_set_add` (`Lang/Semantics.lean`) | size-aware cost model (charges size-growing ops + the `forBnd` counter) |
| `LangEncodable` (`enc`/`dec`/`enc_size`), `encodeState`, instances `Nat`/`List Nat`/`Bool`/`×` (`Lang/PolyTime.lean`) | canonical per-type encoding — **Task 2 rewrites these to be unary/BitState** |
| `PolyTimeComputableLang'`, `toFrameworkWitness'`, `ComputesBy` (`Lang/PolyTime.lean`) | layer witness → framework witness; consumes `Compile_sound` |
| `inNPLang`, `red_inNPLang`, `inNPLang_to_inNP`, `reducesPolyMO_of_lang`, `red_inNP_of_lang`, `bitTestTM` | the layer-native NP class + capstones; sorry-free **modulo C2** |
| `swapCmd`, `mapFstCmd`, `mapSndCmd` (`Lang/PolyTime.lean`) | the repack toolkit every reduction is built from — the **only** users of `takeAt`/`dropAt`/`consLen` (Task 2 re-proves them) |
| `DecidesBy`, `inTimePoly`, `⪯p`, `NPhard`, `polyTimeComputable'` (`Complexity/NP.lean`) | the framework; `polyTimeComputable'` is the faithful (TM-time) target for S3 |

---

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (first build slow;
  one module ~10s after; `lake build Complexity.Lang.Compile` to iterate one
  module). `lake` is **not on PATH**. Commit per logical step with a **green
  build**.
- **NEW — `omega` can't see through `Var := Nat`.** A tape *symbol* / *bit*
  parameter must be typed `Nat`, **not** `Var` — otherwise `(by omega : bit+1 < 4)`
  fails on the `↑bit` coercion. (`Compile.clearAppendM_run` takes `bit : Nat`.)
- **NEW — `set x := e` folds the goal but NOT hyps created later.** Lemmas
  obtained *after* the `set` carry the *unfolded* `e`, so `omega` sees `x` and `e`
  as two atoms and fails. Fix: `rw [hxdef] at h` to unfold before `omega` (e.g.
  `rw [hskdef] at hn` before the budget `omega`).
- **NEW — branching op correctness for `dst = src`.** Read `src` BEFORE clearing
  `dst` (the `nonEmpty` machine is navtest-first); clear-first is WRONG when
  `dst = src`. `Op.inBounds` does NOT force `dst ≠ src`.
- **NEW — `max 4 4 = 4` is not closed by `rw` alone** — append `rfl`/`decide`.
- **Axiom-check** via a scratch file (LSP can't find `lake`):
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean` with
  `import Complexity.Lang.Compile` + `#print axioms <Fully.Qualified.name>`. New
  results must show only `propext`/`Classical.choice`/`Quot.sound` — **no `sorryAx`**.
- **`#eval`-probe a built machine end-to-end before proving its run lemma.** Every
  gadget so far exits with its head **on the trailing terminator** (rewind-bracket,
  don't assume "left of" it). Probe with the same `LEAN_PATH` invocation.
- **Threading a step bound through `∃ t, …`:** add a `∧ t ≤ <bound>` conjunct; the
  witness is explicit, so `refine ⟨<expr>, ?_, ?_, ?_⟩` leaves an `omega` goal.
  For `loopTM` totals use `loopBudget_le` + a `clearBudget_arith`-style closer.
- **`rw [List.length_cons]` fires on the *first* `(_::_).length`** — often a
  `pre = endMark :: …` you didn't mean. Prefer `simp [List.length_append,
  List.length_cons]` (full simp normalises the Nat arithmetic and dodges it).
- **`omega` can't see through record projections / `def`-constants, nor `Var := Nat`
  coercions** — `show` the reduced `Nat` form first.
- **`set x := e with h`** makes `x` defeq `e`; `Classical.choose` is
  proof-irrelevant, so `simp only [hx, dif_pos hj]` exposes `(…).choose` and
  `.choose_spec.2.2` is the bound conjunct.
- Methodology (do not deviate without reason): **skeleton-first, refine the
  highest-risk gap next, decompose `sorry`s don't elaborate them, probe before
  committing engineering, `def`+`sorry` over `axiom` (count = 0).** See ROADMAP
  "How we work".
