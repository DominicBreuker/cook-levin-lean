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

> **Status (this session).** Nothing of Tasks 1–4 was *broken*; the build is
> green (3358 jobs). **Task 3 Class-A architecture is now validated in code** and
> its reading lemmas are committed (see Task 3). **Recommended order from here:**
> finish **Task 3 `nonEmpty`** first (fully scoped + validated below — a contained
> win that proves the Class-A skeleton end-to-end), then `head`/`eqBit`, then the
> Class-B block-copy ops, then Tasks 1+2 together (they are **one monolithic
> change** — see the ⚠ below), then Task 4.
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

**3. Build the 9 cross-register ops (`compileOp_sound_physical_residue`, 9 sorrys
left).** `Op.eval` of each is `s.set dst (f (s.get src…))` (read `src`, write
`dst`, `dst ≠ src`). Two classes:

**Class A — `nonEmpty`/`head`/`eqBit` (`≤ 1`-cell output). ARCHITECTURE VALIDATED;
do `nonEmpty` next.** Machine = `clear dst ⨾ (navigate+read-bit branch) ⨾ rewind ⨾
append answer-bit`. The whole `nonEmpty` machine was **`#eval`-verified end-to-end**
this session:
```
nonEmptyTM dst src :=                          -- exit head 0, residue = cleared-cell zeros
  composeFlatTM (clearRegionTM dst)
    (branchComposeFlatTM (navigateAndTestTM src) thenM elseM
       (navigateAndTestTM_exit_content src) (navigateAndTestTM_exit_delim src))
    (clearRegionTM_exit dst)
thenM/elseM := composeFlatTM (scanLeftUntilTM 4 3) (appendAtThenTwoPhaseRewindTM ins dst) 1
               -- ins=2 (bit 1) for content/non-empty, ins=1 (bit 0) for delim/empty
```
On `s=[[1,0],[1],[]]`, `nonEmptyTM 0 2` (src empty) → head `0`, tape
`encodeTape(s.set 0 [0]) ++ [0,0]`; `nonEmptyTM 0 1` (src non-empty) →
`encodeTape(s.set 0 [1]) ++ [0,0]`. Both exactly the residue contract shape.
- **Reading is DONE & committed:** `Compile.navTestReg_run_content` /
  `_run_delim` (residue-tolerant `navigateAndTest` on `encodeTape s ++ res`,
  reading register `src`; content exit ⇒ src non-empty, delim ⇒ empty). Plus
  helpers `Compile.skipped_length` / `skipped_ok`. Axiom-clean.
- **Branch exits MERGE via `joinTwoHalts`, not demote.** The branch has *two*
  reachable exits (content-branch halt vs delim-branch halt, after the outer
  `composeFlatTM` shifts). `joinTwoHalts raw contentExit delimExit` adds a bridge
  `delimExit → contentExit` (delim path takes one extra step) ⇒ unique exit
  `contentExit`. Use `joinTwoHalts_run_eq` (content case never visits delimExit)
  for the positive branch; for the delim branch chain the `+1` bridge step.
- **Assembly lemmas (all proven, just plumb):** `branchComposeFlatTM_run_pos`
  (content) / `_run_neg` (delim) + `_no_early_halt_pos`/`_neg`; the branch
  `h_traj1` (≠ both exits) follows from `navigateAndTestTM_no_early_halt` +
  `ne_of_not_halting` (both exits are halt states:
  `navigateAndTestTM_exit_content_is_halt`/`_delim_is_halt`). `thenM`/`elseM`
  run = `composeFlatTM_run` of `ScanLeft.rewindToStart_run` (head→0; interior
  cells `<4`/`≠3` from `BitState`) then `opAppendBit_physical_residue` (applied to
  the **cleared** state `s.set dst []`, so `s'.get dst ++ [bit] = [bit]`). Outer
  compose with `clearRegionTM_run` (proven). Budget: clear is `9·L²+9`, each other
  fragment linear, sum is a polynomial — `inOPoly` is all `toFrameworkWitness'`
  needs (bump the stated `9·L²+9` to a larger quadratic/cubic if needed; update
  the 3 sites: statement + append cases + clear case). `head` and `eqBit` reuse
  the same skeleton (`head` writes `[src.head]`; `eqBit` is two reads + compare).

**Class B — `copy`/`tail`/`concat`/`takeAt`/`dropAt`/`consLen` (block copy).**
Counter + rotation = non-destructive block copy, no spare symbol:
- Each `loopTM` iteration moves `src`'s front cell to both `dst` and `src`'s back;
  after `N` (= counter) iterations `src` is rotated full-circle (unchanged), `dst`
  holds the copy. `takeAt`/`dropAt`: `lenReg` (unary) is the counter directly.
  `copy`/`tail`/`concat`: first **count** `src`'s length into a scratch register
  (mirror the `clear` count loop), then rotate-copy. **Probe the rotation machine
  with `#eval` before proving** (the Class-A probe above is the template).
- Budget: per-iteration linear `∧ t ≤ c·L + d`, assemble with
  `Compile.loopBudget_le` + a `Compile.clearBudget_arith`-style closer → quadratic.

**⚠ `#eval`-probe every new machine end-to-end before proving its run lemma** —
architecture bugs (wrong exit head, off-by-one slot) are invisible to validity
proofs and the proofs are expensive.

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
| `compileOp_sound_physical_residue` | per-op contract (`appendOne`/`appendZero`/**`clear`** PROVEN; 9 cross-register `sorry`) |
| `Compile.navTestReg_run_content` / `_run_delim` (+ `skipped_length`/`skipped_ok`) | **NEW** residue-tolerant `navigateAndTest` reading of register `src` on `encodeTape s ++ res`; the Class-A reading step (content ⇒ src non-empty, delim ⇒ empty) |
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
  one module ~10s after). `lake` is **not on PATH** and most MCP/LSP features
  can't find it. Commit per logical step with a **green build**.
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
