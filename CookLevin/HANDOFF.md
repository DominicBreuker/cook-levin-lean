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
is the job. The design is **settled (Option B′)**; execution is underway.

---

## ⚠ The invariant: `BitState` — LOCKED, do not revisit

The compiled machine has a **fixed 4-symbol alphabet** (`sig = 4`). `encodeTape`
shifts each register cell `+1` (`0→1`, `1→2`), `0` separates registers, `3`
terminates/anchors. A cell `≥ 2` shifts to `≥ 3` and collides with the terminator,
so **every state touching the tape must be `Compile.BitState`** (all cells `∈ {0,1}`,
`Compile.lean:1708`). Numbers are therefore **UNARY** (`enc n = replicate n 1`).
Sound for the size law because `encodable.size Nat = id` (verified `Definitions.lean:18`):
unary length `= n = size n`. `sig=4`/`BitState` is **owner-settled**; the design
choice is **Option B′** (witness-carried `enc_bit` + a `BitEncodable` mixin + bit-
level unary canonical encodings). No further design sign-off is needed.

---

## ▶ ACTIVE BUILD (chosen larger item): the move-one-bit transfer primitive

**Why this item.** It is the single critical-path TM gadget the whole of `Compile_sound`
waits on: once the move primitive + its loop run-lemma exist, **all 7 remaining
cross-register ops** (`copy`/`tail`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`)
become wiring (Task 2). Its design is **probe-validated GO** and it is the **one**
op-piece buildable before the Task-1 encoding rework. (The alternative larger item,
closing the live free bridges, only consolidates onto `Compile_sound`; this advances
it.)

**✅ Probe (re-validated 2026-06-05, this session — reproduce with the trace below).**
`encodeTape [[1,0],[1]] = [3,2,1,0,2,0,3]`; move reg0's front bit to reg1:
```
A  navigateAndTestTM 0          → state 3 (content exit), head=1 on src cell `2`
B  bitReadTM                    → state 2 (= bit 1; Nmove, head unmoved)
C  stepDeleteRewindRawTM        → [3,1,0,2,0,3,0] head 0  (src front cell deleted, 0-residue)
D  appendAtThenTwoPhaseRewindTM 2 1 → [3,1,0,2,2,0,3,0] head 0 = encodeTape [[0],[1,1]] ++ [0]
```
Works for `dst>src` and (per prior probe) `dst<src`. ⚠ **append symbol = `bit+1`**.

**Machine structure (mirror `clearBodyRawTM`/`clearRegionTM` exactly).** In `Compile.lean`
(needs `bitReadTM`, which lives there):
- `moveBodyM2TM b dst := composeFlatTM stepDeleteRewindRawTM
     (appendAtThenTwoPhaseRewindTM (b+1) dst) stepDeleteRewindTM_exit`
  — delete src's front cell + rewind, then append `(b+1)` to `dst` + two-phase rewind.
- `moveBodyContentTM src dst := branchComposeFlatTM bitReadTM
     (moveBodyM2TM 0 dst) (moveBodyM2TM 1 dst) bitReadTM_exit_b0 bitReadTM_exit_b1`
  — on the front cell, read the bit then run the bit-dependent delete+append.
- `moveBodyRawTM src dst := branchComposeFlatTM (navigateAndTestTM src)
     (moveBodyContentTM src dst) justRewindTM
     (navigateAndTestTM_exit_content src) (navigateAndTestTM_exit_delim src)`
  — content branch = move one bit & continue; delim branch (src empty) = rewind & stop.
- `moveRegionTM src dst := loopTM (moveBodyRawTM src dst) <exitDone> <exitLoop>`.

**Run-lemma plan (mirror the `clearRegionTM_run` chain).** Per-iteration invariant
`T j` couples BOTH registers: src = the last `j` bits of src₀ (drop `n−j`), dst =
dst₀ ++ (first `n−j` bits of src₀, in order — FIFO, append-at-end preserves order),
residue grows by one `0` per moved bit. Prove `moveBody_delete_run` (`T(j+1)→T j`,
one bit moved) + `moveBody_done_run` (src empty → rewind, stop), then assemble via
`loopTM_run`/`loopTM_no_early_halt` into `moveRegionTM_run` with a quadratic budget
(same shape as `clearRegionTM_run`: `9·L²+…`). ⚠ The new content vs clear: the moved
bit's value must be threaded so the dst-invariant gets the *right* bit — that is the
one genuinely new accounting vs `clear` (where dst is untouched).

**✅ Status — machine DEFINED & probe-validated, run contract STATED (`sorry`).**
Landed in `Compile.lean` (after `clearRegionTM_run`, search `Compile.moveRegionTM`):
`moveBitM2TM`, `moveBitM2_exit`, `moveContentRawTM`/`moveContentExit0`/`Exit1`,
`moveContentTM` (the `joinTwoHalts` merge), `moveBodyRawTM`(+`_exitLoop`/`_exitDone`),
`moveRegionTM`(+`_exit`/`_tapes`), and the contract **`Compile.moveRegionTM_run`**
(residue-tolerant; result tape `encodeTape ((s.set dst (dst₀++src₀)).set src []) ++
res_in ++ replicate |src₀| 0`). The exit-state offset formulas were read off the
probe and verified to make the loop continue/terminate (⚠ the composed `moveBitM2TM`
found-exit includes `stepDeleteRewindRawTM.states` — dropping it silently breaks the
loop; that bug was caught by the full-machine probe). Build green; the def block is
purely additive.

**▶ NEXT (the bulk — proving `moveRegionTM_run`):** mirror the `clearRegionTM_run`
chain exactly.
1. `moveBody_done_run` (delim branch, src empty): like `clearBody_done_run` —
   `branchComposeFlatTM_run_neg` into `justRewindTM`, exit `moveBodyRawTM_exitDone`.
2. `moveBody_delete_run` (content branch, one bit moved): the new piece. Compose
   `navigateAndTestTM_run_content` → `bitReadTM_step` (branch on the front bit) →
   `stepDeleteRewindRawTM` run (reuse the `clearBody_delete_run` internals) →
   `appendAt_twoPhaseRewind_run` (append `bit+1` to `dst`), through
   `branchComposeFlatTM_run` (outer navtest branch) and the inner `bitRead` branch +
   `joinTwoHalts_run_eq` (to land the merged `moveContentExit0`). The per-iteration
   invariant `T j` couples src and dst (see contract docstring); thread the moved
   bit's value into the dst block.
3. Assemble with `loopTM_run` + `loopTM_no_early_halt` (as `clearRegionTM_run` does),
   then tighten the budget constant (currently a provisional `25·L²+25`).
Then wire `moveRegionTM_run` into the 7 `compileOp_sound_physical_residue` ops
(needs the Task-1 scratch operand for `copy`/`tail`/`concat`/`eqBit`).

## ✅ DONE this session (2026-06-05): Task 1 batch 1 — the `BitState` plumbing

The architecture is now wired end-to-end and **proven to compose** (the core risk
of B′). Build green (3358 jobs); `#print axioms CookLevin` unchanged; 0 `axiom`s.

- The three obligations `Compile_sound` (Compile.lean:6047),
  `Compile_run_physical` (6207), `Compile_run_physical_residue` (6237) now take
  `(hbit : Compile.BitState s)`. `bitDecider_run` (6304) and `Compile_polyBound`
  thread it.
- Witness field `enc_bit : ∀ x, Compile.BitState (encodeIn x)` added to
  `DecidesLang`, `PolyTimeComputableLang`, `DecidesLang'`, `PolyTimeComputableLang'`
  (PolyTime.lean). Mixin `class BitEncodable X` + helper `BitState_encodeState_iff`.
- `BitEncodable Bool/Unit/(List Bool)` proved **sorry-free**, and **`Nat` re-laid
  UNARY** (`replicate n 1`) with `BitEncodable Nat` proved (the first bit-level
  canonical encoding; isolated change, no concrete consumers of the old `[n]`).
  `constTrueBool` is now a **complete, axiom-clean** canonical
  witness exercising the new field. `comp`/`toLang`/`precompose` derive `enc_bit`
  from sub-witnesses (sorry-free); `id_witness` uses `[BitEncodable X]`.
- **Surfaced as explicit `enc_bit := sorry` (each with a TODO):** `swap`, `map_fst`
  (product encoding non-bit), and **`evalCnfDecidesLang`** (the LIVE `sat_NP`
  encoding) + `cliqueRelDecidesLang`. These are the concrete remaining gaps below.

---

## The ordered plan from here

### 1. Finish Task 1 — make the encodings actually bit-level (unary)

Each item replaces an `enc_bit := sorry` with a real proof. Land green per item.

- **`EvalCnfCmd.encodeState` UNARY (the LIVE `sat_NP` obligation — highest value).**
  Today (`EvalCnfCmd.lean:87`) its cells are `v+3` (variable values) and
  `CLAUSE_END=2` → not `BitState`, not `sig=4`-representable. Re-lay it unary:
  variables as `1`-blocks, polarity/clause-end markers as bit-patterns in `{0,1}`
  (no `2`/`+3` literal cells). Rewrites `memberCheck` (variable equality becomes
  unary-block equality). Then discharge `evalCnfDecidesLang.enc_bit`
  (EvalCnfTM.lean:67-area). `evalCnfCmd`'s bodies are already `sorry`, so no proven
  work is discarded. **This — not a `LangEncodable (cnf × assgn)` instance — is what
  the live path needs.**
- **Close the live free bridges** `DecidesLang.toDecidesBy` /
  `inTimePolyLang_to_inTimePoly` (PolyTime.lean:125/140, **still `sorry`**). The
  `enc_bit` field is now available to feed `Compile_sound`'s `hbit`. ⚠ **Concrete
  obstacle (this session):** `DecidesBy.encode_size` needs the encoder's *register
  COUNT* bounded, which the free `DecidesLang` does **not** carry (only
  `encodeIn_size` bounds content). Either add a register-count field to
  `DecidesLang` (supply it from evalCnf's fixed ~12-register layout) or route the
  live path through a canonical `DecidesLang'`. Decide and execute.
- **Canonical encodings bit-level + `BitEncodable` instances.** ✅ **`Nat` DONE**
  (unary `replicate n 1`, `dec = length`; `BitEncodable Nat` proved axiom-clean).
  **Remaining:** `X×Y` unary length-prefix; `List X` self-delimiting on bit
  separators. Re-prove `dec_enc`/`enc_size` (unary roughly doubles size — loosen
  `enc_size`'s constant; ripples to `NP.lean` `DecidesBy.encode_size` + the decider
  budget, both need only `inOPoly`/`monotonic`). Then `BitEncodable (X×Y)` (→
  unblocks `swap`/`map_fst` `enc_bit`, switch those to `[BitEncodable …]` +
  `BitEncodable.enc_bit`), `BitEncodable (List X)`. Retire `List Nat = id` from the
  compiled path (quarantine; verify nothing non-compiled breaks before deleting).
  ⚠ The product `dec` currently reads its length prefix via `headD 0` (a single
  non-bit cell); the unary version must parse a `1`-block, which is coupled to the
  value-as-length op rework below.
- **Value-as-length ops → unary:** restate `Op.takeAt`/`dropAt`/`consLen` so length
  = the register's **unary count**, not `(s.get lenReg).headD 0` (meaningless under
  `BitState`, ≤1). Add an empty-scratch operand to `copy`/`tail`/`concat`/`eqBit`
  (`copy dst src sc`, precond `s.get sc = []`, `sc ∉ {dst,src}`; `Op.eval` ignores
  `sc`, the gadget restores it to `[]`). Re-derive `swapCmd`/`mapFstCmd`/`mapSndCmd`
  against the new encoding & signatures (witnesses already allocate spare scratch).
- **Confirm** `BitState` is `Op.eval`-preserved through the induction
  (`BitState_set`, `BitState_set_tail` exist, Compile.lean:2976/3132) — needed by
  step 4.

### 2. Build the 7 op gadgets (the `sorry`s in `compileOp_sound_physical_residue`)

Remaining `sorry`s (Compile.lean ~5610–5626): `copy`/`tail`/`eqBit`/`takeAt`/
`dropAt`/`concat`/`consLen`. **PROVEN already:** `appendOne`/`appendZero`/`clear`/
`nonEmpty`/`head`.

**✅ Probe-validated GO design (counter-free two-phase transfer).** Reuses only
proven gadgets. **Move-one-bit primitive** (inner loop body), from
`encodeTape s ++ res`: `navigateAndTestTM src` → `bitReadTM` (read bit into state)
→ `deleteCarryTM` (delete src's front cell, left-shift, `0`-residue) → rewind to 0
→ `appendAtTM (bit+1) dst` → rewind to 0. ⚠ **append symbol is `bit+1`, not `bit`**
(the encoding shifts `+1`). Works for `dst>src` AND `dst<src` (both `#eval`-probed).
Each phase is a `clear`-style `loopTM` terminating by emptying a register, so
`loopTM_run`/`loopTM_no_early_halt` apply.

Per-op realizations (after scratch `sc` exists): `copy dst src sc` = move `src→sc`
(src empties) ⨾ move `sc→src`&`dst` (sc empties, src rebuilt, dst built);
`tail` = drop the first transferred bit for `dst`; `concat` = two copies;
`eqBit` = transfer both, AND the front bits; `takeAt`/`dropAt`/`consLen` bound
phase 2 by the unary length. **No new low-level TM needed.** Build the move
primitive + run/`_no_early_halt`/budget **mirroring `clearRegionTM_run`** (same
`loopTM` shape + an extra `appendAtTM` in the body). **Re-probe each assembled
machine end-to-end (`#eval`) before proving its run lemma.** Templates:
`clearRegionTM_run` (the chain to mirror), `opNonEmpty_run` (branch-merge engine),
`opHead_run` (nested branch + `bitReadTM`).

### 3. Finding A — restate the top-level budget (do WITH the assembly)

The stated `overhead(size+cost)`, `overhead m = (m+1)²`, is **too small** on two
counts: per-op budgets are `Θ(L²)` (multi-cell ops) so summing `~cost` of them is
**cubic**, and `L = size + s.length + 2` includes the **register count `s.length`**
which `overhead(size+cost)` drops. Restate as
`overhead(State.size s + s.length + c.cost s)` with `overhead` bumped to **cubic**
(e.g. `9·(m+1)³`). Downstream uses only `overhead_poly`/`overhead_mono` → ripples
mechanically. Stays poly on the live path (`encodeState x` is 1 register; programs
add a constant `regBound`).

### 4. Assemble

`Compile_run_physical_residue` → `Compile_sound` by induction on `Cmd`: per-`Op`
from step 2 (now feeding `hbit`); `seq` from `compileSeq_sound_physical_residue`
(PROVEN); `ifBit`/`forBnd` from their residue siblings
(`branchComposeFlatTM_run` / `loopTM_run` + `loopTM_no_early_halt`; the
`compileIfBit`/`compileForBnd` residue contracts at ~5892/5943 are stated, sorry'd).
This discharges C2; downstream unlocks S3 migration, C7 verifiers, C8 hardness.

---

## Inventory — the C2 working set

| Name (file) | Role |
|------|------|
| `Compile.BitState`/`encodeTape`/`encodeRegs`/`shiftReg`/`ValidResidue`/`decodeTape` (Compile.lean) | `sig=4` tape encoding; the standing bit invariant; residue-tolerant contract |
| `Compile_sound` (6047), `Compile_run_physical` (6207), `Compile_run_physical_residue` (6237) | **the C2 obligations (`sorry`)** — now carry `(hbit : BitState s)` |
| `compileOp_sound_physical_residue` (5564) | per-op contract, `(hbit)`, budget `9·L²+9·L+30`. **PROVEN:** appendOne/Zero/clear/nonEmpty/head. **`sorry` (7):** copy/tail/eqBit/takeAt/dropAt/concat/consLen |
| `opNonEmpty`/`opHead`/`bitReadTM`/`joinTwoHalts*` | proven cross-register ops + branch-merge templates |
| `clearRegionTM_run` chain (4148+) | **the `loopTM` chain to MIRROR** for the transfer gadget (run + traj + quadratic budget) |
| `navigateAndTestTM`/`appendAtTM`/`deleteCarryTM`/`rewindTwoPhaseTM` | the proven gadget pieces the move primitive composes |
| `loopTM`(+`_run`/`_no_early_halt`), `loopBudget_le`, `clearBudget_arith` | counted loop (terminate-by-emptying) + budget closers |
| `LangEncodable` + `BitEncodable` mixin + `BitState_encodeState_iff` (PolyTime.lean) | per-type encoding + the bit-level mixin (**`BitEncodable Bool/Unit/List Bool` proven**) |
| `DecidesLang`/`DecidesLang'`/`PolyTimeComputableLang`/`PolyTimeComputableLang'` | witness structures — now carry `enc_bit`; constructions wired (sorry only at non-bit leaves: `swap`/`map_fst`/`evalCnf`/`cliqueRel`) |
| `EvalCnfCmd.encodeState` (EvalCnfCmd.lean:87) + `evalCnfDecidesLang` (EvalCnfTM.lean) | **the LIVE `sat_NP` encoding** (free `DecidesLang`); cells `v+3`/`2` → re-lay unary (Task 1, item 1) + discharge `enc_bit` |
| `DecidesLang.toDecidesBy`/`inTimePolyLang_to_inTimePoly` (PolyTime.lean:125/140, **`sorry`**) | live free bridge — close with the new `enc_bit` field + a register-count bound (see Task 1) |
| `swapCmd`/`mapFstCmd`/`mapSndCmd` (PolyTime.lean) | only users of takeAt/dropAt/consLen — re-derive in Task 1 |

---

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (`lake` is **not** on
  PATH; LSP/most MCP features can't find it). First build slow (~minutes); one
  module `lake build Complexity.Lang.Compile` to iterate. Commit per logical step,
  green.
- **Probe** a built machine end-to-end *before* proving its run lemma:
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/x.lean` with
  `import Complexity.Lang.Compile`, `open Complexity.Lang`, and
  `runFlatTM N M { state_idx := M.start, tapes := [([], 0, Compile.encodeTape s)] }`.
  **Every gadget exits with its head on the trailing terminator** — rewind-bracket.
- **Axiom-check** via a scratch file (LSP can't find `lake`):
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean` with
  `#print axioms <name>` — must show only `propext`/`Classical.choice`/`Quot.sound`
  for new sorry-free results. The headline module is `Complexity.NP.SAT.CookLevin`.
- **Append a BIT `b`** = `appendAtTM (b+1)`. `deleteCarryTM` deletes the cell **left
  of the head**; `navigateAndTestTM src` lands the head **on** src's first content.
- **A polymorphic structure field over `encodeState` needs `∀ x : X`** (annotate the
  binder) — without an `encodeIn` field to pin the type, inference loops (this
  session's first build error).
- **`omega` can't see through `Var := Nat`** (use a `Nat`-typed `bit` param), record
  projections / `def`-constants (`show` the reduced form first), nor a `set x := e`
  for hyps created *after* the `set`.
- **`decide` rejects goals with free variables** (e.g. `BitEncodable Unit`); use
  `simp`/`cases` to remove the var first.
- Branching-op correctness for `dst = src`: **read `src` BEFORE clearing/writing
  `dst`** (`Op.inBounds` does NOT force `dst ≠ src`).
- Methodology (do not deviate without reason): **skeleton-first, refine the
  highest-risk gap next, decompose `sorry`s don't elaborate them, probe before
  committing engineering, `def`+`sorry` over `axiom` (count = 0), build green
  between commits.**
