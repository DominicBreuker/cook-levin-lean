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

## ✅ DONE this session (2026-06-06): the move-one-bit transfer gadget is PROVEN

**`Compile.moveRegionTM_run` is fully proven and axiom-clean** (only
`propext`/`Classical.choice`/`Quot.sound`). This was the single critical-path TM
gadget the whole of `Compile_sound` waited on. It transfers register `src`'s
content (FIFO, one bit/iteration) to the end of `dst`, empties `src`, rewinds to
head `0`: result tape `encodeTape ((s.set dst (dst₀++src₀)).set src []) ++
(res_in ++ replicate |src₀| 0)`, budget `25·L²+25`. Reusable lemmas landed (all
in `Compile.lean`, all axiom-clean — **reuse, do not re-derive**):

- `Compile.appendBitTwoPhase_run` — bracket-free raw two-phase append (head 0 →
  append `bit` to `dst`'s end → rewind), `≤ 3·L+8`. The shared append core.
- `Compile.moveBitM2_run` — single-bit transfer engine (delete src front +
  append to dst), `≤ 7·L+18`, via `composeFlatTM_run` over
  `stepDeleteRewind_run` + `appendBitTwoPhase_run`.
- `Compile.moveContent_run` — the bit-read branch (`bitReadTM` → `moveBitM2`),
  two paths merged by `joinTwoHalts` into `moveContentExit0`, `≤ 7·L+21`.
- `Compile.moveBody_done_run` (src empty → rewind, `≤ 6·L+12`) and
  `Compile.moveBody_delete_run` (one bit moved, `≤ 9·L+26`): the loop-body
  branches.
- `Compile.moveRegionTM_run` — the loop assembly (`loopTM_run` +
  `loopTM_no_early_halt`), per-iter invariant `T j` couples both registers
  (`src = drop (n−j)`, `dst = dst₀ ++ take (n−j)`), threads the moved bit.
- Full validity/halt scaffolding: `moveBitM2TM_valid`/`_sig`/`_exit_is_halt`/
  `_exit_lt`, `moveContentRawTM_valid`/`_sig`, `moveContentExit{0,1}_is_halt`/`_lt`,
  `moveContentTM_valid`/`_sig`/`_exit0_is_halt`, `moveBodyRawTM_valid`/
  `_exitLoop_is_halt`/`_exitDone_is_halt`/`_exitLoop_lt`/`_exitDone_lt`/
  `_exitDone_ne_exitLoop`. Plus utilities `Compile.get_set_ne`/`set_comm`,
  `appendAtTM_states_eq`, `moveBudget_arith`.
- ⚠ **Key finding vs `clear`:** the move tape **grows** one residue cell per
  iteration (`|T j| = L + (n−j)`; delete adds a `0`, append grows `encodeTape`,
  total +1). So the per-iteration budget is in the *current* (growing) tape length,
  bounded by `2L`; this is the one accounting that differs from `clearRegionTM_run`.
- ⚠ **Stray halts are fine for the run:** `appendAtThenTwoPhaseRewindTM` has a
  boundary halt (state 7) that `moveBitM2TM`/`moveContentRawTM` inherit and that
  `joinTwoHalts` does NOT demote — but it is **never reached**, so every run/traj
  lemma goes through (`composeFlatTM_no_early_halt` proves halting-false at every
  reached step). The next agent does **not** need a `halt_unique` for `moveRegionTM`.

## ▶ ACTIVE BUILD (next agent): Task 1 (unary encodings + scratch), then wire the 7 ops

`moveRegionTM_run` is the data-transport primitive. The **7 remaining cross-register
ops** (`copy`/`tail`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`, the `sorry`s in
`compileOp_sound_physical_residue`, ~Compile.lean:5892) are now gated **only** on
Task 1 (the coupled encoding batch), which must come first (see the ordered plan
below — "the prior 'build ops before Tasks 1+2' was self-contradictory"):

1. **Task 1 — unary `Nat`/product encodings + a scratch operand** (ordered plan §1).
   `copy`/`tail`/`concat`/`eqBit` need an **empty-scratch operand** `sc` (precond
   `s.get sc = []`, `sc ∉ {dst,src}`; `Op.eval` ignores it); `takeAt`/`dropAt`/
   `consLen` need the **unary length** restatement (`.headD 0` is meaningless under
   `BitState`). `swapCmd`/`mapFstCmd`/`mapSndCmd` (the only users) re-derive against
   the new signatures.
2. **Wire `moveRegionTM_run` into the ops** (ordered plan §2). Probe-validated
   design: every op is a **two-phase counter-free transfer** built from
   `moveRegionTM_run` (move `src→sc` until src empties, then `sc→`(`src`&`dst`)).
   `copy dst src sc` = move `src→sc` ⨾ move `sc→src`&`dst`; `tail` = drop the first
   moved bit for dst; `concat` = two copies; `eqBit` = transfer both + AND fronts;
   `takeAt`/`dropAt`/`consLen` bound phase 2 by the unary length. Each op's per-op
   contract: feed `moveRegionTM_run` + the residue bookkeeping into the
   `compileOp_sound_physical_residue` shape (template: the proven `appendOne`/`clear`/
   `nonEmpty`/`head` cases). **Re-probe each assembled op (`#eval`) before proving.**
   ⚠ You will likely need `moveRegionTM_valid`/`_sig`/`_start` wrappers (mirror
   `clearRegionTM_valid` — `loopTM_valid` over `moveBodyRawTM_valid` which now
   exists; numeric `exit_lt` via `moveRegionTM_exit = moveBodyRawTM.states`).

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
| `compileOp_sound_physical_residue` (search) | per-op contract, `(hbit)`, budget `9·L²+9·L+30`. **PROVEN:** appendOne/Zero/clear/nonEmpty/head. **`sorry` (7):** copy/tail/eqBit/takeAt/dropAt/concat/consLen — now wire from `moveRegionTM_run` (needs Task 1 scratch/unary) |
| `opNonEmpty`/`opHead`/`bitReadTM`/`joinTwoHalts*` | proven cross-register ops + branch-merge templates |
| `Compile.moveRegionTM_run` (+`moveBitM2_run`/`moveContent_run`/`moveBody_{done,delete}_run`/`appendBitTwoPhase_run`) | ✅ **PROVEN** move-one-bit transfer gadget (data transport, FIFO `src→end of dst`); the primitive the 7 ops are built from |
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
