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

## ✅ PROVEN gadgets the ops build on (reuse, do not re-derive)

- **`Compile.moveRegionTM_run`** (axiom-clean) — the **single-target** FIFO
  transfer: moves `src`'s content one bit/iter to the **end** of `dst`, empties
  `src`, rewinds to head `0`. Result tape
  `encodeTape ((s.set dst (dst₀++src₀)).set src []) ++ (res_in ++ replicate |src₀| 0)`,
  budget `25·L²+25`. Built from `loopTM_run` over `moveBodyRawTM` (body =
  `navigateAndTestTM ⨾ bitReadTM ⨾ stepDeleteRewind ⨾ appendAtThenTwoPhaseRewind(bit+1, dst)`).
  Full validity/halt scaffolding exists (`moveBitM2TM_valid`/`_sig`/`_exit_*`,
  `moveContent*`, `moveBodyRawTM_valid`/`_exit{Loop,Done}_{is_halt,lt}`/`_ne_`).
- **`Compile.moveRegionTM_valid` / `_sig`** (axiom-clean, this session) — the
  `loopTM_valid`/`loopTM_sig` wrappers needed to drop `moveRegionTM` into
  `composeFlatTM`/`branchComposeFlatTM`.

## ⚠ DESIGN CORRECTION (this session, probe-validated): the 7 ops are 4 different shapes — NOT all "built from moveRegionTM"

`moveRegionTM` is **single-target** (one `dst`). The prior plan said all 7 ops
reduce to it; that is false. A conservative single-target move can never
*duplicate* data (the number of copies is invariant), and `copy`/`tail`/`concat`
must duplicate. State-level + TM-level `#eval` probes (this session) reproduce
every `Op.eval` exactly and pin the four real shapes:

1. **`copy`/`tail`/`concat` — need a NEW dual-target duplicating move
   `moveRegion2TM`** (append `src`'s content to the end of **both** `dst1` and
   `dst2`, empty `src`). Validated recipes (registers must be **distinct**;
   `sc` starts empty):
   - `copy dst src sc` = `clear dst ⨾ move src→sc ⨾ move2 sc→(src,dst)`.
   - `tail dst src sc` = `copy dst src sc ⨾ deleteFirstBit dst` (one `stepDeleteRewind` on dst's front).
   - `concat dst src1 src2 sc` = `copy dst src1 sc ⨾ move src2→sc ⨾ move2 sc→(src2,dst)`.
   **`moveRegion2TM` is buildable by mirroring `moveRegionTM`** with a second
   append in the body: `moveBitM3TM b dst1 dst2 := moveBitM2TM b dst1 ⨾
   appendAtThenTwoPhaseRewindTM (b+1) dst2`. ✅ TM-`#eval` confirms the dual
   append (append `b` to dst1 then dst2 from head 0, residue-tolerant) yields the
   exact `encodeTape` with head→0 and a clean halt. The `_run` lemma mirrors
   `moveRegionTM_run` but its per-iter invariant couples **three** registers
   (`src`, `dst1`, `dst2`) and the budget grows (two appends/bit). This is the
   single highest-value next gadget — it unblocks 3 of the 7 ops.
2. **`eqBit` — NOT moves; a comparison-loop gadget.** Copy both operands to **two**
   scratch regs, then loop: compare-and-delete the front bits; equal iff fronts
   always matched and both empty together. **Needs 2 scratch operands**, not 1.
3. **`takeAt`/`dropAt` — a counter-bounded transfer**, NOT `moveRegionTM` (which
   transfers *all*). Under `BitState` the count is `k = (s.get lenReg).length`
   (unary), so the loop is `loopTM`/`forBnd`-shaped over `lenReg`; transfer/skip
   the first `k` bits. Validated specs: `takeAt → src.take k`, `dropAt → src.drop k`.
   Needs 1 scratch.
4. **`consLen` — the ONLY op whose `Op.eval` must be RESTATED unary:**
   `dst := replicate |lenSrc| 1 ++ src` (validated spec). ⚠ **Its `Op.cost` must
   ALSO be bumped to charge `|lenSrc|`** (today only `|src|+1`), else
   `Op.size_eval_le` breaks (output grows by `|lenSrc|+|src|`).

**Scratch-operand counts (corrects "all need one sc"):** copy/tail/concat/takeAt/
dropAt/consLen need **1**; **eqBit needs 2**. Size the `Op` signature change to
this before refactoring.

## ▶ NEXT STEPS (risk-first summary; full detail in "The ordered plan from here" below)

Task 1 (the coupled encoding/signature batch) gates all 7 ops and must come first;
the dual-target gadget can be built in parallel.

1. **Task 1 — unary encodings + scratch operands** (see "The ordered plan from
   here §1" below for the full item list). Add the scratch operands above to the
   `Op` constructors (`Op.eval` ignores them; the gadget restores them to `[]`);
   restate `takeAt`/`dropAt`/`consLen` unary (+ the `consLen` cost bump);
   re-derive `swapCmd`/`mapFstCmd`/`mapSndCmd`. Land green per item.
2. **Build `moveRegion2TM` + `moveRegion2TM_run`** (mirror `moveRegionTM_run`;
   probe each assembled machine with `#eval` BEFORE proving). Then the comparison
   loop (`eqBit`) and the counter-bounded transfer (`takeAt`/`dropAt`).
3. **Wire each op into `compileOp_sound_physical_residue`** (the 7 `sorry`s,
   ~Compile.lean:7109–7125) via the proven `clear`/`nonEmpty`/`head` templates +
   `rewindBracket`/`joinTwoHalts` to keep a unique halt. **Re-`#eval` end-to-end
   before proving each run lemma.**

## ✅ Already PROVEN — the residue-induction invariant toolkit (reuse, don't re-derive)

Ported (and re-verified axiom-clean) the proven invariant scaffolding from the
parallel branch (old PR #55, which is conflict-stranded against the move-gadget
merge — its run-gadget half differs, but this invariant half is move-gadget-
*independent*). Build green; all new decls `#print axioms`-clean (no `sorryAx`).
These are **exactly the lemmas the `Compile_run_physical_residue` induction and the
`→ Compile_sound` assembly will call** — reuse them directly, do not re-derive:

- **The last mile is PROVEN — `Compile.sound_of_run_residue`** (Compile.lean, after
  `Compile_run_physical_residue`): given the residue run's components + `BitState
  (c.eval s)`, extends the run to the full `overhead` budget and decodes (residue
  invisible). So once `Compile_run_physical_residue` is discharged, `Compile_sound`
  closes mechanically.
- **`BitState` is preserved through the induction:** `Op.eval_preserves_BitState`
  (per-op step: `BitState s → o.inBounds s → consLen-side-cond → BitState (Op.eval o
  s)`) + the unconditional `Compile.BitState_set_pad` (for `forBnd`'s padding
  counter-write) + `Cmd.eval_preserves_BitState` (PolyTime.lean — the **full `Cmd`
  induction composes**, incl. the `forBnd` fold; hyps `UsesBelow c k`, `k ≤
  s.length`, `Cmd.NoConsLen c`).
- **`inBounds` threads from a static bound:** `Op.inBounds_of_UsesBelow`
  (PolyTime.lean) + register-count monotonicity `State.set_length_ge` /
  `Op.eval_length_ge` / `Cmd.eval_length_ge` (Frame.lean). Fix `k ≤ s.length` with
  `Cmd.UsesBelow c k`; width never shrinks, so every reached state keeps width `≥ k`.
- ⚠ **Risk finding (machine-checked):** only **`consLen`** actually breaks `BitState`
  (`Op.consLen_breaks_BitState` is an explicit counterexample); `takeAt`/`dropAt`
  *preserve* it (sub-list of a bit register), they are merely *useless* under it. So
  Task 1's unary restatement is required for **correctness** only for `consLen`.
- ⚠ **Consequence for the obligation:** `Compile_run_physical_residue` will need
  **added hyps `(hk : k ≤ s.length)`, `(huses : Cmd.UsesBelow c k)`, `(hnc :
  Cmd.NoConsLen c)`** alongside `hbit` — the bridge supplies them from the witness
  (`encodeState` fixes `s.length = 1`; the program's `regBound` / `usesBelow`
  fixes the footprint; live `Cmd`s are `consLen`-free once Task 1 rebuilds the
  product toolkit). Worth confirming `EvalCnfCmd`/reduction `Cmd`s are already
  `consLen`-free (consLen is used only by `swap`/`mapFst`/`mapSnd`, rebuilt in Task 1).

**Already in place from the prior batch (do not redo):** the three obligations
(`Compile_sound`/`Compile_run_physical`/`_residue`) carry `(hbit : BitState s)`;
witness field `enc_bit : ∀ x, BitState (encodeIn x)` on all four witness structures
+ the `BitEncodable` mixin; `BitEncodable Bool/Unit/List Bool` proven and `Nat`
re-laid UNARY (`replicate n 1`). **Still `enc_bit := sorry`:** `swap`, `map_fst`
(product encoding non-bit), `evalCnfDecidesLang` (LIVE `sat_NP`), `cliqueRelDecidesLang`.

---

## ⚠ Four under-acknowledged C2 obligations (code-audited 2026-06-05b — do not rediscover)

The residue + size-aware-cost design is **internally consistent and the poly bound is
genuinely TRUE** (verified: `Op.cost` charges every size-growing op — `copy`/`tail`/
`takeAt`/`dropAt` cost `|src|+1`, `concat` `|src1|+|src2|+1`, `Semantics.lean:75` +
`Op.size_eval_le`; so physical-tape growth/op ≤ cost/op, max tape `O(size+regCount+
cost)`, **not** exponential). **No showstopper.** But discharging C2 is bigger than the
plan below frames it — four obligations beyond Finding A:

1. **`Compile_run_physical_residue` (Compile.lean:6519) is too weak to be its own
   induction hypothesis.** It is stated with **no incoming residue** (input
   `[encodeTape s]`), but the proven `compileSeq_sound_physical_residue` threads
   `res0→res1→res2` — the second fragment runs on `encodeTape mid ++ res1`, *with* the
   first's residue. So the `seq` case cannot apply the IH to `c2`. **Generalize the
   obligation to carry an arbitrary incoming `(res0 : List Nat) (ValidResidue res0)`**
   (output `encodeTape (c.eval s) ++ res_out`); prove the live instance with `res0 = []`.
   The per-op lemma already is residue-in/out — only the top obligation is wrong-shaped.
2. **Nothing bounds the physical tape length *including residue*, yet the per-op budgets
   are quadratic in exactly that.** Per-op budget is `9·L²+9·L+30` with `L = (encodeTape
   s ++ res_in).length`. But `ValidResidue` constrains only *symbols*, **not length**
   (Compile.lean:2858); `Cmd.encodeTape_eval_length_le` bounds output *content* only (no
   residue). So a **new lemma is required: max physical tape ≤ poly(size + regCount +
   cost)**, proved by charging each op's physical growth to the size-aware cost and
   threading it through the run. This is **separate from Finding A** (which only covers
   budget *degree* + register count) and is real work coupled to the budget proof. The
   generalized obligation's budget should be `overhead(size + s.length + cost + |res0|)`,
   cubic.
3. **The branch and loop *machines* are still STUBS — not just their contracts.**
   `compileForBnd` (1631) and `compileTestBit` (1483, feeding `compileIfBit`'s tester)
   are `compiledCmd_default`/`branchTester_default` — they do not branch/loop at all yet.
   The `ifBit`/`forBnd` assembly is gated on **building** a real `compileTestBit`
   (navigate + `bitReadTM`) and a real `compileForBnd` (a `loopTM` over the bound's unary
   length that materialises the counter) — each C1/C3 gadget work comparable to a
   cross-register op, on top of the residue restatement of their contracts.
4. **Minor couplings (none fatal):** (a) **`consLen` cost under unary** — Task 1's unary
   `consLen` writes `|lenSrc|` cells (not 1), so `Op.cost (consLen …)` must *also* charge
   `(s.get lenSrc).length` or obligation #2 breaks for it. (b) **Residue must stay inert**
   — every gadget's scans/rewinds must stop at the terminator and never read into residue
   (the point of `rewindTwoPhaseTM`); this is where bugs hide in the move gadget + 7 ops.
   (c) **Stray halt states** — `joinTwoHalts`/`loopTM` must demote every halt but one or
   `halt_unique` fails and the op can't be wired into `compileOp` (PR #55 hit a stray
   state 18; clear/nonEmpty/head already handle it).

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

Remaining `sorry`s (Compile.lean 7109–7125): `copy`/`tail`/`eqBit`/`takeAt`/
`dropAt`/`concat`/`consLen`. **PROVEN already:** `appendOne`/`appendZero`/`clear`/
`nonEmpty`/`head`.

**See "⚠ DESIGN CORRECTION" near the top** for the validated per-op recipes and the
four gadget shapes. Summary: `moveRegionTM` (single-target FIFO move) is one phase
but is **not** sufficient alone — `copy`/`tail`/`concat` need the new dual-target
`moveRegion2TM`, `eqBit` a comparison loop, `takeAt`/`dropAt` a counter-bounded
transfer, and `consLen` a unary `Op.eval`+cost restatement. Build each gadget +
run/`_no_early_halt`/budget **mirroring `clearRegionTM_run`/`moveRegionTM_run`**, and
**re-probe each assembled machine end-to-end (`#eval`) before proving its run
lemma.** Templates: `moveRegionTM_run`/`clearRegionTM_run` (the loop chains to
mirror), `opNonEmpty_run` (branch-merge engine), `opHead_run` (nested branch +
`bitReadTM`).

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

`Compile_run_physical_residue` → `Compile_sound`. **The last mile and the induction
invariants are now PROVEN (this session) — reuse, don't re-derive:**
- `Compile_run_physical_residue` (the residue run) by induction on `Cmd`: per-`Op`
  from step 2 (feeding `hbit` re-established by `Op.eval_preserves_BitState` and
  `inBounds` by `Op.inBounds_of_UsesBelow`); `seq` from
  `compileSeq_sound_physical_residue` (PROVEN); `ifBit`/`forBnd` from their residue
  siblings (`branchComposeFlatTM_run` / `loopTM_run` + `loopTM_no_early_halt`; the
  `compileIfBit`/`compileForBnd` residue contracts are stated, sorry'd). ⚠ Thread
  the added `UsesBelow`/`k ≤ s.length`/`NoConsLen` hyps (see DONE-this-session) — or
  prove `Cmd.eval_preserves_BitState` is enough to supply `BitState (c.eval s)` for
  every fragment boundary.
- `→ Compile_sound`: feed the residue run + `Cmd.eval_preserves_BitState`'s
  `BitState (c.eval s)` to **`Compile.sound_of_run_residue` (PROVEN)**. Done.
This discharges C2; downstream unlocks S3 migration, C7 verifiers, C8 hardness.

---

## Inventory — the C2 working set

| Name (file) | Role |
|------|------|
| `Compile.BitState`/`encodeTape`/`encodeRegs`/`shiftReg`/`ValidResidue`/`decodeTape` (Compile.lean) | `sig=4` tape encoding; the standing bit invariant; residue-tolerant contract |
| `Compile_sound`, `Compile_run_physical`, `Compile_run_physical_residue` (search; line nums drift) | **the C2 obligations (`sorry`)** — now carry `(hbit : BitState s)` |
| `compileOp_sound_physical_residue` (Compile.lean:7063) | per-op contract, `(hbit)`, budget `9·L²+9·L+30`. **PROVEN:** appendOne/Zero/clear/nonEmpty/head. **`sorry` (7):** copy/tail/eqBit/takeAt/dropAt/concat/consLen (lines 7109–7125) — see the DESIGN CORRECTION above for the 4 gadget shapes (needs Task 1 scratch/unary) |
| `opNonEmpty`/`opHead`/`bitReadTM`/`joinTwoHalts*` | proven cross-register ops + branch-merge templates |
| `Compile.moveRegionTM_run` (+`_valid`/`_sig`, `moveBitM2_run`/`moveContent_run`/`moveBody_{done,delete}_run`) | ✅ **PROVEN** **single-target** FIFO transfer `src→end of dst`. Used by `copy`/`tail`/`concat`/`takeAt`/`dropAt` as one phase — but NOT sufficient alone (see DESIGN CORRECTION) |
| `Compile.moveRegion2TM` / `_run` | ⬜ **NOT BUILT** — the dual-target *duplicating* move (`src→` end of both `dst1`&`dst2`). The next gadget to build; mirror `moveRegionTM_run`, body adds a 2nd `appendAtThenTwoPhaseRewindTM`. Probe-confirmed feasible. Unblocks copy/tail/concat |
| `clearRegionTM_run` chain | the `loopTM` chain `moveRegionTM_run` mirrored (run + traj + quadratic budget) |
| `Compile.sound_of_run_residue` (Compile.lean) | ✅ **PROVEN last mile** — residue run + `BitState(c.eval s)` ⇒ `Compile_sound` |
| `Op.eval_preserves_BitState`/`Compile.BitState_set_pad`/`Cmd.eval_preserves_BitState` (Compile/PolyTime) | ✅ **PROVEN** `BitState` induction step + full-`Cmd` composition (hyps `UsesBelow`/`k≤len`/`NoConsLen`); `Op.consLen_breaks_BitState` = the only breaker |
| `Op.inBounds_of_UsesBelow` (PolyTime) + `State.set_length_ge`/`Op`/`Cmd.eval_length_ge` (Frame) | ✅ **PROVEN** `inBounds`-threading (width never shrinks) |
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
