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

**The standing decision (owner-approved): everything is bit-level; numbers are
UNARY.** The `LangEncodable` encodings are currently Nat-valued (`enc (n:Nat) =
[n]`, the product puts a Nat *length* cell on the tape) — **incompatible** with
the BitState compiler, and `Compile_sound` is still (mis-)stated *without* a
`BitState` hypothesis, which hides the gap on the live in-NP path
(`CookLevin → sat_NP → evalCnfCmd → Compile`). Fixing this is Tasks 1+2 below.
Unary keeps `sig = 4`/`BitState` (all proven gadgets stay valid) and keeps sizes
polynomial.

---

## Status (2026-06-10) and the two work streams

Build green (3358 jobs); all new results axiom-clean (`propext` /
`Classical.choice` / `Quot.sound` only).

**Per-op contract `compileOp_sound_physical_residue` (budget `9L²+9L+30`):
5 of 12 ops PROVEN** — `appendOne`/`appendZero`/`clear`/`nonEmpty`/**`head`
(new)**. 7 left: `copy`/`tail`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`.

**★ Class-B design RESOLVED & probe-validated (this session's headline).** The
remaining 6 block ops do **not** need a unary scratch *counter* or rotation.
The old "counter + rotation" sketch was **circular** (counting `src`'s length
non-destructively has no shrinking region to terminate on; and consuming
`lenReg` as a counter violates the contract — `Op.eval` *preserves* `lenReg`).
The validated replacement is **counter-free `move`-twice**:

- `moveRegTM src tgt` — loop { navtest `src`: delim → done; content → read the
  bit value (`eqTestTM 4 2`), `stepDeleteRewind` (delete `src`'s front cell),
  `opAppendBitRewind` (append it at `tgt`'s end) }. Terminates because **`src`
  shrinks** — exactly the proven `clear`-loop termination shape.
- `dupRegTM src tgt1 tgt2` — same loop, appending each bit to **two** targets.
- `copy dst src sc` (with `sc` an **empty scratch**, `sc ∉ {dst,src}`) =
  `clear dst ⨾ move sc src ⨾ dup (src,dst) sc` — restores `src`, writes `dst`,
  leaves `sc = []`.

**`parked/ProbeMoveCopy.lean` is the validated machine architecture** (run
instructions in its header): all 6 `#eval` probes (move both directions, empty
src, full copy incl. input residue) exit at the loop halt, head `0`, tape
exactly `encodeTape output ++ zero-residue`. Build the real gadgets from those
exact definitions. Derived ops: `tail dst src sc` = `copy` then one-shot
guarded front-delete on `dst`; `concat dst s1 s2 sc` = `clear dst ⨾ (move sc
s1 ⨾ dup (s1,dst) sc) ⨾ (move sc s2 ⨾ dup (s2,dst) sc)`; `takeAt`/`dropAt`
need **two** scratches (counted dup-loop that consumes a moved copy of
`lenReg` while restoring `lenReg` 1-bit-per-iteration — sketch in the
2026-06-10 commit message; design the exact `Op` signatures in Task 2).

We alternate sessions between two streams; each has a concrete next job:

### Bottom-up stream — NEXT: prove the `move`/`dup` loop run lemmas

Proof engineering on the probed machines (no design unknowns left):

1. Port `moveRegTM`/`dupRegTM` (+ exits) from `parked/ProbeMoveCopy.lean` into
   `Compile.lean`, with the structural lemma block (valid/tapes/sig/halt —
   mirror the `headBitM`/`headEmptyBody` blocks verbatim; the content arm is a
   `joinTwoHalts`-merged inner branch exactly like `headBitM`).
2. Prove the loop-body run lemma (per-iteration: navtest + eqTest + delete +
   append, both branch shapes exist — `headBitM_run` is the 2-level-branch
   template; `clearBody_delete_run` is the delete-iteration template), then the
   `loopTM` assembly (copy `clearRegionTM_run`'s structure: the per-iteration
   tape `T j`, `loopBudget_le`, a `clearBudget_arith`-style closer). The loop
   invariant is `src` shrinking by one front bit per iteration while `tgt`
   grows at its end; deletes lengthen the residue by one `0`, appends grow the
   tape by one cell.
3. `copyRegTM_run` = two `composeFlatTM_run` applications on top.
   **⚠ Budget: expect a bump** — `move` costs ~`(|src|)·(9L+c)` and `copy`
   stacks three quadratics, so the per-op budget constant will exceed
   `9L²+9L+30`; bump the statement (3 sites: statement + the relaxing
   `le_trans … (by omega)` in each proven case) to whatever the arithmetic
   needs (`inOPoly` is all that matters downstream).
4. `copy` **cannot be wired into `compileOp`** until the `Op` signature gains
   the scratch operand (Task 2, top-down) — stop at a fully-proven
   `copyRegTM_run` and the next top-down session connects it. `eqBit` last:
   first check whether the live verifier (`EvalCnfCmd`) only needs a 1-cell
   compare (then it is `head`-shaped, cheap).

### Top-down stream — NEXT: Tasks 1+2 (one monolithic session)

**⚠ Coupled and wide; do NOT start piecemeal — budget a full session.**

**Task 1 — make `BitState` explicit and true.** Add `(hbit : Compile.BitState
s)` to `Compile_sound` / `Compile_run_physical_residue` and thread it through.
Give `LangEncodable` a new field `enc_bit : ∀ x, ∀ c ∈ enc x, c ≤ 1` so the
bridge (`toFrameworkWitness'`, `bitDecider_run`) can supply it.

**Task 2 — unary re-encode + `Op` signature fixes (the `enc_bit` field forces
every instance to change at once):**
- `LangEncodable Nat`: `enc n = List.replicate n 1`; product length-prefix → a
  unary block (self-delimiting with the `0` separators); `LangEncodable (List
  Nat)` (currently `id` — allows arbitrary Nats!) re-encoded bit-level.
  Re-prove `dec_enc`, loosen `enc_size` (≈ doubles — ripples to `NP.lean`
  `DecidesBy.encode_size` and the decider budget).
- **Give the Class-B ops their scratch operands** (probe-validated): `copy dst
  src sc` / `tail dst src sc` / `concat dst s1 s2 sc` with contract
  preconditions `s.get sc = []`, `sc < s.length`, `sc ∉ {dst,src,…}`;
  `takeAt`/`dropAt` get **two** scratches and a *unary* length register
  (length = the register's bit count, NOT a Nat cell); restate `consLen`
  unary. `Op.eval` stays `s.set dst (…)` (gadgets restore the scratches).
  You have design freedom here: the witnesses (`swapCmd`/`mapFstCmd`/
  `mapSndCmd` in `Lang/PolyTime.lean` — the **only** users of
  `takeAt`/`dropAt`/`consLen`) are re-derived in this task anyway, so pick the
  op set that matches what `move`/`dup` implement naturally.
- The witnesses already allocate scratch registers (`swapCmd` uses regs 1–5;
  reductions use `regBound+k`), so they can pass known-empty ones.

**After both streams converge:** wire the Class-B gadgets into `compileOp` +
the per-op contract, then **Task 4 — assemble `Compile_run_physical_residue` →
`Compile_sound`**: compose per-op contracts with
`compileSeq_sound_physical_residue` (done) and the `compileIfBit` /
`compileForBnd` residue contracts (`branchComposeFlatTM_run` / `loopTM_run` +
`loopTM_no_early_halt`), then induction on `Cmd`. This discharges C2; then S3
migration (ROADMAP step 2), C7 verifiers (`evalCnfCmd`), C8 hardness, S1
tableau.

**Trajectory check (2026-06-10).** C2 remains converging: `head` needed *zero*
new generic machinery (the `nonEmpty` engine + one 150-LOC test gadget), and
the Class-B probe closed the last open design decision. Estimate **~3–5 more
sessions for C2** (move/dup proofs ~1–2, Tasks 1+2 ~1, remaining ops ~1,
assembly ~1). No trigger for the destination-B fallback.

---

## The proven op architecture (templates to copy)

**Class A (≤1-cell output): `nonEmpty` ✅, `head` ✅ — `eqBit` may fit too.**
- `Compile.opNonEmpty(_run)` — 2-way branch: `branchComposeFlatTM
  (navigateAndTestTM src) body₁ body₂` + ONE `joinTwoHalts` merge. The run
  proof template: navtest run/traj (`navTestReg_run_*`/`_traj_*`) →
  `branchComposeFlatTM_run_pos`/`_neg` → `joinTwoHalts_reaches_kept`/`_demoted`.
- `Compile.opHead(_run)` — adds the **bit-value read**: the content arm is
  itself a 2-way branch on `eqTestTM 4 2` whose two exits are merged by
  `joinTwoHalts` *inside* the arm (`headBitM`), so the outer machine keeps the
  `opNonEmpty` shape exactly. The empty arm (`headEmptyBody` = rewind ⨾
  `clearRegionTM`) writes `[]`. **Merging inner branches first is the pattern
  for any op with >2 outcomes** — it avoids any multi-exit generalization of
  the engine lemmas.
- Reusable engine (all in `Compile.lean`, axiom-clean): `clearAppendM_run`
  (clear `dst` ⨾ append bit), `nonEmptyBranchBody_run` (rewind ⨾ clearAppend),
  `headEmptyBody_run` (rewind ⨾ clear), `headBitM_run` (the 2-level branch),
  `joinTwoHalts_reaches_kept`/`_reaches_demoted` (the branch-merge engine),
  `branchComposeFlatTM_M2/_M3_halt_intro`, `branchComposeFlatTM_halt_only`,
  `composeFlatTM_halt_unique`, `stepFlatTM_bridge_prefix` (`TMPrimitives`).

**Class B (block ops): probe-validated, unproven.** See the bottom-up stream
above and `parked/ProbeMoveCopy.lean`.

**The `clear` op chain (the model for every `loopTM`-based op):**
`clearRegionTM_run` (loop, run + trajectory + budget `≤ 9·L²+9`) ←
`clearBody_delete_run` / `clearBody_done_run` (`≤ 6·L+12`) ←
`stepDeleteRewind_run` (`≤ 4·L+9`) ← `encodeTape_residue_twoPhaseRewind`
(`≤ L+3`). Each existential carries a `∧ t ≤ <bound>` conjunct;
`clearRegionTM_run` proves every loop tape has the same length `L`.

**⚠ `#eval`-probe every new machine end-to-end before proving its run lemma**
(architecture bugs are invisible to validity proofs and the proofs are
expensive). Templates: `parked/ProbeHead.lean`, `parked/ProbeMoveCopy.lean`
(run instructions in their headers; they are NOT built by lake).

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
| `composeFlatTM` / `branchComposeFlatTM` / `loopTM` (+ `_run`, `_no_early_halt`, `_valid`) | sequence / 2-way branch / loop |
| `loopBudget`, `loopTM_no_early_halt`, `stepFlatTM_bridge_prefix` | per-iteration step budget; generic bridge step |

### Compiler & encoding — `Complexity/Lang/Compile.lean`
| Name | Role |
|------|------|
| `Compile.encodeTape` / `encodeRegs` / `shiftReg` / `endMark` / `decodeTape` | the `sig=4` tape encoding; `decodeTape` ignores residue + head |
| `Compile.BitState` (+ `BitState_set`, `BitState_set_tail`) | the standing invariant (cells `∈ {0,1}`) |
| `Compile.ValidResidue`, `TapeOK`, `decodeTape_encodeTape_append` | residue-tolerant contract (the tape never shrinks) |
| `rewindBracket`, `rewindBracket_transport`, `opAppendBit_physical_residue` | template for any head-moving op (two-phase rewind, demoted halt) |
| `compileOp_sound_physical_residue` | per-op contract; budget `9·L²+9·L+30`. PROVEN: `appendOne`/`appendZero`/`clear`/`nonEmpty`/**`head`**. `sorry`: `copy`/`tail`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen` (7) |
| `Compile.opNonEmpty` (+ `_run`) | the 2-way-branch op template |
| `Compile.opHead` (+ `_run`), `headBitM(_run)`, `headEmptyBody(_run)`, `headBitRawM_*`, `headRawM_*` | **✅ NEW** the bit-value-reading op; the inner-merge pattern |
| `Compile.clearAppendM_run`, `nonEmptyBranchBody_run` | clear ⨾ append building blocks (any answer-bit write) |
| `Compile.navTestReg_run_content`/`_run_delim`/`_traj_*` | residue-tolerant navigate+test of register `src` |
| `Compile.joinTwoHalts_reaches_kept`/`_reaches_demoted` + halt lemmas | the branch-merge engine |
| `compileSeq_sound_physical_residue` | PROVEN (additive budget `t₁+1+t₂`) |
| `Compile_run_physical_residue`, `Compile_sound` | **the C2 obligations (`sorry`)** — need the `BitState` hypothesis (Task 1) |
| `Compile.loopBudget_le`, `Compile.clearBudget_arith` | reusable budget template (per-iteration `M` → `(n+1)·M`; quadratic closer) |

### Gadget library (sorry-free; sig=4)
| File | Gadgets |
|------|---------|
| `Lang/ClearGadget.lean` | `navigateToRegTM`, `navigateAndTestTM` (read+branch empty/non-empty), **`eqTestTM sig v` (✅ NEW: cell-value test `= v` → exit 1, else exit 2)**, `clearBodyRawTM`, `clearRegionTM`, `stepDeleteRewindRawTM`, `justRewindTM`; `navSteps`, `navSteps_le` |
| `Lang/AppendGadget.lean` | `appendAtTM` (insert a bit at register `dst`'s end), `regBlocks`, `appendAt_run` |
| `Lang/ScanLeft.lean` | `scanLeftUntilTM`, `stepLeft/RightTM`, `rewindToStart_run`, `rewindTwoPhaseTM` |
| `Lang/ShiftTape.lean` | `insertCarryTM` / `deleteCarryTM` (single-cell carries) |
| `parked/ProbeMoveCopy.lean` | **✅ NEW (not built)** the validated `moveRegTM`/`dupRegTM`/`copyRegTM` compositions for Class B |

### Layer semantics & bridge
| Name (file) | Role |
|------|------|
| `Op`, `Cmd`, `State` (`Lang/Syntax.lean`) | the while-language; `State = List (List Nat)` |
| `Op.eval`, `Op.cost`, `Cmd.eval`, `Cmd.size_eval_le`, `State.size_set_add` (`Lang/Semantics.lean`) | size-aware cost model |
| `LangEncodable` (`enc`/`dec`/`enc_size`), `encodeState`, instances (`Lang/PolyTime.lean`) | per-type encoding — **Task 2 rewrites these to be unary/BitState** |
| `PolyTimeComputableLang'`, `toFrameworkWitness'`, `ComputesBy` (`Lang/PolyTime.lean`) | layer witness → framework witness; consumes `Compile_sound` |
| `inNPLang`, `red_inNPLang`, `inNPLang_to_inNP`, `bitTestTM` | the layer-native NP class + capstones; sorry-free **modulo C2** |
| `swapCmd`, `mapFstCmd`, `mapSndCmd` (`Lang/PolyTime.lean`) | the repack toolkit — the **only** users of `takeAt`/`dropAt`/`consLen` (Task 2 re-proves them) |
| `DecidesBy`, `inTimePoly`, `⪯p`, `NPhard`, `polyTimeComputable'` (`Complexity/NP.lean`) | the framework; `polyTimeComputable'` is the faithful target for S3 |

---

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (first build slow;
  `lake build Complexity.Lang.Compile` to iterate one module). `lake` is **not
  on PATH**. Commit per logical step with a **green build**.
- **NEW — `branchComposeFlatTM` exit metavariables elaborate unpredictably**
  (symbolic exit constant vs its literal value — they are defeq, but `rw` with
  a machine-equation then fails). Don't `rw [hraweq] at h`; **convert by defeq
  instead**: `have h' : <statement over raw> := h` (or
  `fun k hk ck hck => h k hk ck hck`), and recognise the exit state via
  `rw [← hstate_eq]; exact h.1`. See the `headBitM_run` merge steps.
- **`omega` can't see through `Var := Nat`.** A tape *symbol* / *bit*
  parameter must be typed `Nat`, **not** `Var` — `(by omega : bit+1 < 4)`
  fails on the `↑bit` coercion.
- **`set x := e` folds the goal but NOT hyps created later.** Lemmas obtained
  *after* the `set` carry the *unfolded* `e`; `rw [hxdef] at h` before `omega`.
- **Branching op correctness for `dst = src`:** read `src` BEFORE clearing
  `dst` (navtest-first). `Op.inBounds` does NOT force `dst ≠ src`.
- **`max 4 4 = 4` is not closed by `rw` alone** — append `rfl`/`decide`.
- **Axiom-check** via a scratch file (LSP can't find `lake`):
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean` with
  `#print axioms <name>`. New results must show only
  `propext`/`Classical.choice`/`Quot.sound` — **no `sorryAx`**.
- **Threading a step bound through `∃ t, …`:** add a `∧ t ≤ <bound>` conjunct;
  `refine ⟨<expr>, ?_, ?_, ?_⟩` leaves an `omega` goal. For `loopTM` totals use
  `loopBudget_le` + a `clearBudget_arith`-style closer.
- **`rw [List.length_cons]` fires on the *first* `(_::_).length`** — prefer
  `simp [List.length_append, List.length_cons]`.
- **`omega` can't see through record projections / `def`-constants** — `show`
  the reduced `Nat` form first.
- Methodology (do not deviate without reason): **skeleton-first, refine the
  highest-risk gap next, decompose `sorry`s don't elaborate them, probe before
  committing engineering, `def`+`sorry` over `axiom` (count = 0).** See ROADMAP
  "How we work".
