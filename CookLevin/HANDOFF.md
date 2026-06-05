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

## ⚠ The invariant: `BitState`

The compiled machine has a **fixed 4-symbol alphabet** (`sig = 4`). `encodeTape`
shifts each register cell `+1` (`0→1`, `1→2`), `0` separates registers, `3`
terminates. A cell `≥ 2` shifts to `≥ 3` and collides with the terminator, so
**every state touching the tape must be `Compile.BitState`** (all cells `∈ {0,1}`).
Numbers are therefore **UNARY** (`enc n = replicate n 1`). This is sound for the size
law because `encodable.size Nat = id` (verified): unary length `= n = size n`, so
`enc_size : len ≤ 2·size+1` holds. (No log-vs-unary blowup — the whole framework is
already unary-flavoured.) `sig=4`/`BitState` is **owner-settled** (2026-06-03;
the `sig=6` block-copy alternative was dropped). It is therefore **locked**: every
encoding that ever reaches `Compile` must be bit-level. This is the premise the
design decision below rests on.

### ★ DESIGN DECISION — SETTLED (reviewed 2026-06-05): adopt **Option B′**

The three top-level obligations — `Compile_sound` (Compile.lean:6047),
`Compile_run_physical` (6207), `Compile_run_physical_residue` (6237) — are stated
**without** a `BitState s` hypothesis, but every per-op/per-fragment lemma needs it
(`compileOp_sound_physical_residue`:5564 + the 10 lemmas at
2393/2554/2901/3025/3160/3387/3535/3761/3823/4149). Adding `hbit` (Task 1) forces
each compile site to supply `BitState` of the state it feeds in. The previous
handoff posed this as a fork (A: bundle `enc_bit` into `LangEncodable`, breaking
`List Nat = id`; B: a localized `BitEncodable` keeping the generic toolkit
untouched) and recommended **B**. **This review validated B's *mechanism* but found
its *justification* is a misconception that would waste effort if followed
literally.** Two machine-checked findings:

1. **The bit-level work is systemic, not localizable.** `BitState` is mandatory for
   *every* state reaching `Compile`, and in the endgame (S3 migration) *every* chain
   type is compiled — so every canonical encoding (`Nat`, `X×Y`, `List X`) must
   become bit-level eventually. The value-as-length ops that build/read the product
   length-prefix — `consLen` (writes `(s.get lenSrc).length`, Semantics.lean:60),
   `takeAt`/`dropAt` (read `(s.get lenReg).headD 0`, :53–56) — and the entire
   `swap`/`mapFst`/`mapSnd` product toolkit built on them (PolyTime.lean:1643) are
   **fundamentally non-`BitState`** and must be rebuilt unary **regardless of fork**.
   So B's headline selling point — "keeps `List Nat = id` and the generic toolkit
   untouched" — is **false**. `List Nat = id` (arbitrary Nat cells) and `Nat = [n]`
   have **no compiled future** under `sig=4`; they are vestiges, not assets to
   protect.
2. **The live `sat_NP` path does not use `LangEncodable` at all.** `sat_NP →
   inTimePolyTM_evalCnf → inTimePolyLang_to_inTimePoly → DecidesLang.toDecidesBy`
   (PolyTime.lean:117, **still `sorry`**) runs the **free-encoding** `DecidesLang`
   with the bespoke 12-register `EvalCnfCmd.encodeState` (EvalCnfCmd.lean:87) — whose
   cells are `v+3` (variable values) and `CLAUSE_END=2`, i.e. **not `BitState` and
   not even `sig=4`-representable**. So "give `cnf × assgn` a bit-level
   `LangEncodable` encoding" does **not** discharge the live obligation; the live
   obligation is `BitState (EvalCnfCmd.encodeState x)`, a property of that
   hand-written encoding, which must itself be re-laid out unary (variables unary, no
   `+3`/`2` literal cells).

**Conclusion: the only genuine, still-open choice is *where the `BitState` guarantee
is attached*, given bit-level encodings are mandatory either way. Attach it on the
witness, supplied by a reusable mixin — call this Option B′:**

- **Do NOT bundle `enc_bit` into `LangEncodable`** (Option A). Keep `LangEncodable`
  the bare encode/decode/size class. Bundling forces a big-bang where every instance
  must be bit-level at once (breaks "green between commits") and still cannot cover
  the free-encoding live path.
- **Add `enc_bit : ∀ x, Compile.BitState (encodeIn x)` as a FIELD on the witness
  structures** `DecidesLang`, `DecidesLang'`, `PolyTimeComputableLang`,
  `PolyTimeComputableLang'`. This is the **load-bearing, universal home**: `encodeIn`
  is a free function there, so it covers both the live free path (`evalCnfCmd`) and
  the canonical path. This is what `Compile_run_physical_residue`'s `hbit` is fed
  from at each bridge.
- **Add a reusable mixin `class BitEncodable (X) [encodable X] [LangEncodable X] :
  Prop where enc_bit : ∀ x, Compile.BitState (LangEncodable.encodeState x)`** so
  canonical witnesses (`DecidesLang'`, `PolyTimeComputableLang'`) discharge their
  field once-per-type instead of per-witness. Prove it for each bit-level canonical
  type as it is migrated — this gives the **incremental** migration B promised, but
  honestly (no false "toolkit untouched" claim).
- **Make the canonical encodings bit-level** (`Nat` unary; `X×Y` unary length-prefix;
  `List X` self-delimiting on bit separators) and give each a `BitEncodable` instance.
  **Retire `List Nat = id` / `Nat = [n]` from the compiled path** (quarantine, don't
  necessarily delete — verify no non-compiled lemma depends on them first; default is
  to replace with the bit versions).

Net: B′ = **B's typeclass shape** (witness-carried obligation + `BitEncodable` mixin,
incremental) **+ A's substance** (bit-level canonical encodings, unary `Nat`, rebuilt
ops/toolkit). It is neither naive-A (big-bang) nor naive-B (the false "localized to
`cnf × assgn`, toolkit untouched" framing). No owner sign-off is required to proceed —
the only premise (`sig=4`) is already owner-settled.

---

## ⚠⚠ Corrected sequencing (this session's headline risk finding)

The previous handoff's order — *"build the transfer gadget → takeAt/dropAt →
copy/tail/concat/eqBit → encodings"* — is **inconsistent with its own findings**.
All 7 remaining ops are gated on **Task 1 (the `BitState` plumbing)**:

- `takeAt`/`dropAt`/`consLen` read a length from a register **cell value**
  (`(s.get lenReg).headD 0`). Under `BitState` that value is `≤ 1`, so the current
  semantics can only take/drop 0 or 1 elements. They are **meaningless until Task 1
  restates the length as a UNARY count** (`= the register's length`). Building them
  first builds semantics Task 1 throws away.
- `copy`/`tail`/`concat`/`eqBit` must **preserve `src`** (`Op.eval` writes only
  `dst`). A mark-free single-tape copy that preserves the source needs a
  **guaranteed-empty scratch register** → an extra `Op` operand → an `Op`-signature
  change that is *"folded into Task 1"*.
- The only current witnesses using these ops (`swapCmd`/`mapFstCmd`/`mapSndCmd`,
  PolyTime.lean ~970/1200) are **built on the current non-unary product encoding**
  (they unpack via the Nat length-prefix). Task 1 rewrites them anyway — so a scratch
  operand added *before* Task 1 would force a `swapCmd` rewrite Task 1 then **rewrites
  again** (double work — exactly what we avoid).

**Correct order:** **Task 1 (coupled batch) FIRST** → then the op gadgets →
Finding A budget → assembly. The *raw-tape transfer gadget* (below) is the **one**
op-related piece that is encoding-agnostic and may be built before/concurrent with
Task 1.

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

**Per-op realizations** (all from the move primitive, after Task 1 adds scratch `sc`):
`copy dst src sc` = move `src→sc` (src empties) ⨾ move `sc→src`&`dst` (sc empties,
src rebuilt, dst built, order preserved); `tail` = drop the first transferred bit for
`dst`; `concat` = two copies; `eqBit` = transfer both, AND the front bits;
`takeAt`/`dropAt` bound phase 2 by the unary `lenReg`; `consLen` similar. **No new
low-level TM is needed** — the rotation/`copyBlockTM` sketches from older handoffs are
dropped.

**Probe verdict: GO.** No tape-level snag; the only new requirement is the empty
scratch operand (Task 1). Build the move primitive + its run/`_no_early_halt`/budget
**mirroring the proven `clearRegionTM_run` chain** (it is the same `loopTM` shape with
an extra `appendAtTM` in the body). **Re-probe each assembled machine end-to-end
before proving its run lemma** (architecture bugs are invisible to validity proofs).

---

## The ordered plan from here

The fork is settled (**B′**, above). The raw-tape transfer gadget (below the GO
verdict) is the **one** op-piece buildable before Task 1; everything else waits on
Task 1.

**1. The `BitState` plumbing (one coupled green-landing batch).** This is the old
"Task 2" restated per B′. Land it green in this order:
- **Obligations:** add `(hbit : Compile.BitState s)` to `Compile_sound`,
  `Compile_run_physical`, `Compile_run_physical_residue`. Confirm `BitState` is
  `Op.eval`-preserved through the induction (`BitState_set`, `BitState_set_tail`
  already exist).
- **Witness field:** add `enc_bit : ∀ x, Compile.BitState (encodeIn x)` to
  `DecidesLang`, `DecidesLang'`, `PolyTimeComputableLang`, `PolyTimeComputableLang'`.
  This is what feeds `hbit` at every bridge (`bitDecider_run`,
  `DecidesLang.toDecidesBy`, `toFrameworkWitness'`). **The free-encoding bridges
  (`DecidesLang.toDecidesBy`, `inTimePolyLang_to_inTimePoly`, PolyTime.lean:117/132)
  are still `sorry` — close them now using the new field.**
- **Mixin:** `class BitEncodable (X) [encodable X] [LangEncodable X] : Prop where
  enc_bit : ∀ x, Compile.BitState (LangEncodable.encodeState x)`; use it to supply
  the `enc_bit` field of the canonical witnesses once-per-type.
- **Bit-level canonical encodings:** `Nat` unary (`replicate n 1`); `X×Y` unary
  length-prefix; `List X` self-delimiting on bit separators. Re-prove
  `dec_enc`/`enc_size` (unary roughly doubles size — loosen `enc_size`'s constant if
  needed; ripples to `NP.lean` `DecidesBy.encode_size` + the decider budget, both
  need only `inOPoly`/`monotonic`). Give each a `BitEncodable` instance. Retire
  `List Nat = id` / `Nat = [n]` from the compiled path (quarantine; verify nothing
  non-compiled breaks before deleting).
- **Value-as-length ops → unary:** restate `Op.takeAt`/`dropAt`/`consLen` so length =
  the register's **unary count**, not `(s.get lenReg).headD 0` / not a written
  `.length` cell. Add an empty-scratch operand to `copy`/`tail`/`concat`/`eqBit`
  (`copy dst src sc`, precondition `s.get sc = []`, `sc < length`, `sc ∉ {dst,src}`;
  `Op.eval` ignores `sc`, the gadget restores it to `[]`). Re-derive
  `swapCmd`/`mapFstCmd`/`mapSndCmd` against the new encoding & signatures (witnesses
  already allocate spare scratch registers).
- **The live path — `EvalCnfCmd` (EvalCnfCmd.lean):** re-lay `encodeState` unary so
  it is `BitState` *and* `sig=4`-representable — today its cells are `v+3` (variables,
  unbounded) and `CLAUSE_END=2`. Variables must be **unary blocks**; the polarity /
  clause-end markers must live in `{0,1}` (use a bit-pattern delimiter, not a `2`).
  This also rewrites `memberCheck` (variable equality becomes unary-block equality,
  `eqBit`/transfer-based). Supply its `enc_bit` field. **This — not a `LangEncodable
  (cnf × assgn)` instance — is what discharges `sat_NP`.** (`evalCnfCmd`'s bodies are
  already `sorry`, so no proven work is discarded.)

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
| `LangEncodable` (`enc`/`dec`/`enc_size`) + instances `Nat`/`List Nat`/product (`Lang/PolyTime.lean` 440/640/839) | **Task 1 rewrites these bit-level** (B′); add the `BitEncodable` mixin alongside |
| `DecidesLang`/`DecidesLang'`/`PolyTimeComputableLang`/`PolyTimeComputableLang'` (PolyTime.lean 62/1100/85/483) | the witness structures — **gain the `enc_bit : ∀ x, BitState (encodeIn x)` field** (B′) |
| `EvalCnfCmd.encodeState` (EvalCnfCmd.lean:87) + `evalCnfDecidesLang` (EvalCnfTM.lean:63) | **the LIVE `sat_NP` encoding** (free `DecidesLang`); cells `v+3`/`2` → re-lay unary in Task 1 |
| `DecidesLang.toDecidesBy` / `inTimePolyLang_to_inTimePoly` (PolyTime.lean 117/132, **`sorry`**) | the live free-encoding bridge — close in Task 1 using the new `enc_bit` field |
| `swapCmd`/`mapFstCmd`/`mapSndCmd` (PolyTime.lean ~970/1200) | only users of `takeAt`/`dropAt`/`consLen` — re-derived in Task 1 |
| `toFrameworkWitness'` (632), `bitDecider_run` (6297), the `DecidesBy` decider (PolyTime ~1700) | the bridge that consumes the obligations — gains the `BitState` supply (B′) |

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
