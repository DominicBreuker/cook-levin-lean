# Handoff — the computable layer / compiler (Risk C2)

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). **This file is the working plan for the compiler
(Risk C2)** — the one obligation the whole NP-completeness bridge sits on.

We now work **multi-session in two alternating work streams**. At the start of
each session the owner says **`bottom-up`** or **`top-down`**:

- **Bottom-up** — build the gadgets/lemmas the contracts need, iterating toward
  the final proofs (the way we always worked).
- **Top-down** — work directly on the final pieces to assemble, *design* their
  proofs, and create whatever supporting lemmas/gadgets we need with `sorry` (if
  they look reasonably provable). Surfaces gaps *before* we waste effort.

The two streams **share one interface** — the per-fragment *physical-residue
contracts* — and are meant to **meet in the middle** there. Keep both stream
sections below concrete and forward-looking. When you rewrite this file at the
end of a session, reflect the whole picture so the streams stay aligned.

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
**`Compile_run_physical_residue` ⇒ `Compile_sound`** (still `sorry`). Discharging it
is the job. The design is **settled (Option B′)**; execution is underway.

**The whole live dependency chain (top to bottom):**
```
sat_NP → inNPLang_to_inNP → Compile.bitDecider_run            (Compile.lean:9015)
       → Compile_run_physical_residue                          (Compile.lean:8910, SORRY — THE OBLIGATION)
       → [per-fragment physical-residue contracts]             ← THE SHARED INTERFACE
            ├ compileOp_sound_physical_residue                 (Compile.lean:8237; +W-invariant ①; 5/12 ops done, 7 sorry)
            ├ compileSeq_sound_physical_residue                (Compile.lean:8454; PROVEN)
            ├ compileIfBit_sound_physical_residue              (PolyTime.lean; stated, sorry — gated on real compileTestBit)
            └ compileForBnd_sound_physical_residue             (PolyTime.lean; stated, sorry — gated on real compileForBnd)
       Compile.run_physical_residue_gen                        (PolyTime.lean; ★ MECHANIZED — assembles the above)
DecidesLang.toDecidesBy / inTimePolyLang_to_inTimePoly         (PolyTime.lean:228/243, SORRY — live bridge)
```

---

## ⚠ The invariant: `BitState` — LOCKED, do not revisit

The compiled machine has a **fixed 4-symbol alphabet** (`sig = 4`). `encodeTape`
shifts each register cell `+1` (`0→1`, `1→2`), `0` separates registers, `3`
terminates/anchors. A cell `≥ 2` shifts to `≥ 3` and collides with the terminator,
so **every state touching the tape must be `Compile.BitState`** (all cells `∈ {0,1}`,
`Compile.lean:1708`). Numbers are therefore **UNARY** (`enc n = replicate n 1`).
Sound for the size law because `encodable.size Nat = id`: unary length `= n = size n`.
`sig=4`/`BitState`/Option B′ is **owner-settled**; no further design sign-off needed.

---

## ★ TOP-DOWN findings (2026-06-06, first top-down pass) — the assembly design

A top-down pass over the final assembly (`Compile_run_physical_residue` and the
per-fragment contracts) **mechanized the composition and pinned the exact
remaining interface**. The headline result: the obligation is provable by a clean
induction, the budget composes with the *right* shape, and the residue stays
polynomially bounded. The designed artifact is in `Lang/PolyTime.lean` (search
`run_physical_residue_gen`).

### ✅ STATUS — `Compile.run_physical_residue_gen` is MECHANIZED (sorry-free proof body)
The full induction is **proven** (build green; `#print axioms` shows `sorryAx`
only *transitively*, via the honest leaf gaps below — the assembly's own proof has
no `sorry`):
- **`op`** — reduces to `compileOp_sound_physical_residue` (now carries the
  W-invariant ①, discharged for the 5 done ops); budget ② via `L ≤ G`. ✅
- **`seq`** — reduces to the PROVEN `compileSeq_sound_physical_residue` +
  `compileSeq_traj_physical_residue`; ① telescopes; ② is the exact `physStepBudget`
  superadditivity (`Compile.physStepBudget_seq`, axiom-clean). ✅
- **`ifBit`/`forBnd`** — dispatch to the two residue combinators (proven reductions;
  the combinators themselves are the `sorry` leaves, gated on the stub machines). ✅

So the **assembly is done**: what remains are exactly the leaf gadgets (the 7 ops,
the 2 stub machines + their combinators) and the upstream wiring (GAP 3/4). No
composition surprises remain — the induction compile-checks end to end.

### The designed induction — `Compile.run_physical_residue_gen`
The top obligation `Compile_run_physical_residue` (no incoming residue) is **too
weak to be its own induction hypothesis**: in the `seq` case the second fragment
runs on `encodeTape mid ++ res1` — *with* the first fragment's residue. So the
real lemma carries an **arbitrary incoming residue `res0`** (live instance:
`res0 = []`), plus the threading hyps and a shared tape bound `G`:

```
Compile.run_physical_residue_gen (c) (k) (s) (res0) (G)
  (hbit : BitState s) (hk : k ≤ s.length)
  (huses : Cmd.UsesBelow c k) (hnc : Cmd.NoConsLen c)
  (hres0 : ValidResidue res0)
  (hG : State.size s + s.length + res0.length + c.cost s + 2 ≤ G) :
  ∃ t res, ValidResidue res
    ∧ State.size (c.eval s) + res.length ≤ State.size s + res0.length + c.cost s   -- ① W-invariant
    ∧ runFlatTM t (Compile c) (init [encodeTape s ++ res0])
        = some {exit c, [([], 0, encodeTape (c.eval s) ++ res)]}                     -- run
    ∧ (trajectory: never halts / hits exit before t)
    ∧ t ≤ Compile.physStepBudget G (c.cost s)                                        -- ② budget
```
Induction on `c`: **op** → `compileOp_sound_physical_residue`; **seq** →
`compileSeq_sound_physical_residue` + `compileSeq_traj_physical_residue` (both
PROVEN); **ifBit/forBnd** → the two residue combinators below. `BitState mid` and
`k ≤ mid.length` thread via `Cmd.eval_preserves_BitState` / `Cmd.eval_length_ge`
(both PROVEN). The `op`/`seq` structural cases are written; the **W-invariant ①
and budget ② steps are `sorry`** (validated arithmetic below — mechanical Nat work).

### ① The W-invariant — resolves "obligation #2: nothing bounds the residue"
**Key insight:** track `W := State.size + residueLength` *jointly*. Then
**`W_out ≤ W_in + Op.cost o s` for every op** (clear: size shrinks by `|dst|`,
residue grows by `|dst|` → `W` unchanged, cost ≥ 0; append: `W` +1 = cost; copy:
`W` +`|src|` ≤ cost). This is **non-compounding** (unlike "`|res| ≤ size + |res0| +
cost`", which re-adds `size` at every `seq` and blows up). Globally `State.size
(c.eval s) + |res| ≤ State.size s + |res0| + c.cost s`. Hence every physical tape
(monotone, `TapeMono.lean`) `≤ State.size s + s.length + res0.length + c.cost s + 2
= the bound `hG``, so a **single shared `G` bounds all sub-fragment tapes** with no
compounding — this is what makes the budget compose.

### ② The budget — `physStepBudget`, exactly superadditive (fixes ROADMAP Finding #3)
`Compile.physStepBudget G cost := (9·G² + 9·G + 33)·(cost + 1) + cost`. Per-op
budget `9·L²+9·L+30` with `L ≤ G` fits (op `cost ≥ 1`). It is **exactly
superadditive under `seq`**: `physStepBudget G (1+c₁+c₂) = physStepBudget G c₁ + 1
+ physStepBudget G c₂` (the `(cost+1)` factor counts the ops, the `+cost` slack
absorbs `seq`'s control step). `ifBit` composes with room (`+3` ≤ one extra
`(9G²+…)` unit). It is `inOPoly`/`monotonic` in `G` and `cost` (downstream only
needs that). **This is why the old `overhead(size+cost)=(·+1)²` was unprovable:
quadratics are not superadditive, and it dropped both `s.length` and the residue.**

### THE GAPS this pass surfaced (now the concrete shared interface / bottom-up work)
1. **`compileIfBit_sound_physical_residue` / `compileForBnd_sound_physical_residue`
   needed to exist** (only the no-incoming-residue `*_sound_physical`, Compile.lean
   8565/8616, did). The induction *cannot* thread residue through branches/loops
   without them. **Statements are now written (`sorry`) in `PolyTime.lean` and
   `run_physical_residue_gen` dispatches to them** (the dispatch is proven) — they
   are the pinned interface the bottom-up stream must hit. ⚠ The `forBnd` body
   hypothesis is the *full* `run_physical_residue_gen` conclusion with its **own
   per-call tape bound `G'`** and a `k ≤ s'.length` premise (the fold-states grow,
   so a single fixed `G` is dishonest) — match this when proving it.
2. **`compileForBnd` and `compileTestBit` are still STUBS** (`compiledCmd_default`
   / `branchTester_default`, **0 transitions** — `#eval`-confirmed). The loop and
   branch-tester *machines themselves* don't exist. Building them (a `loopTM` over
   the bound's unary length; a navigate+`bitReadTM` tester) is bottom-up gadget
   work comparable to a cross-register op, and **gates** combinator #1.
3. ✅ **Architecture / file order — DONE (relocation, 2026-06-06).** The threading
   lemmas + budget lemmas + the two residue combinators + `run_physical_residue_gen`
   now live in `Compile.lean` **before** `Compile_run_physical_residue` (added
   `import Complexity.Lang.Frame` to Compile.lean — Frame depends only on Semantics,
   no cycle). So the assembly is now positioned to discharge the obligation. **What
   remains:** actually replace the `sorry` at `Compile_run_physical_residue` with the
   `res0 = []` instance of `run_physical_residue_gen` — which requires the budget
   restatement (GAP 4), since the obligation's current budget `overhead (size+cost)`
   is the wrong (unprovable) shape.
4. **Budget restatement ripples (do together with #3):** `Compile_run_physical_residue`
   (Compile.lean:8910), `sound_of_run_residue`, `Compile_sound`, `Compile_polyBound`,
   `bitDecider_run` all carry the **wrong** `Compile.overhead (State.size s + c.cost s)`
   budget. Restate them with `physStepBudget G (c.cost s)` (or any `inOPoly` bound in
   `size + s.length + cost`). **Register-count coupling:** the budget legitimately
   includes `s.length`, which is **not** bounded by `costBound(size)` in general — so
   `DecidesLang.toDecidesBy` / `Compile_polyBound` need a **register-count bound**
   (add a `regCount`/`usesBelow` field to `DecidesLang`, or route the live path
   through the canonical `DecidesLang'`). On the live path `encodeState x` has a
   constant register count, so it stays poly.

### Reflection — where the streams meet
The **shared interface is the four per-fragment physical-residue contracts** (op,
seq, ifBit, forBnd) **plus the per-op W-invariant ①**. Top-down *consumes* them in
`run_physical_residue_gen`; bottom-up *produces* them (7 ops, the loop/branch
machines, the two new combinators). With the statements now pinned, the streams
have a precise rendezvous: **a contract is "met" when its statement (already
written) is `sorry`-free.** No further design surprises are expected on the
assembly side — the composition is hand-validated.

---

## ✅ PROVEN gadgets the ops build on (reuse, do not re-derive)

- **`Compile.moveRegionTM_run`** (axiom-clean) — **single-target** FIFO transfer:
  moves `src` one bit/iter to the **end** of `dst`, empties `src`, rewinds head→0.
  Budget `25·L²+25`. Built from `loopTM_run` over `moveBodyRawTM`.
- **`Compile.moveRegion2TM_run`** (axiom-clean) — **dual-target duplicating move**
  (`src`→ end of **both** `dst1` & `dst2`, empties `src`). Budget `36·L²+39·L`. The
  primitive `copy`/`tail`/`concat` build on. ⚠ duplicates ⇒ `State.size` grows by `m`.
- **`compileOp_sound_physical_residue`** (Compile.lean:8237) — per-op contract,
  carries incoming residue. **PROVEN:** `appendOne`/`appendZero`/`clear`/`nonEmpty`/
  `head`. **`sorry` (7):** `copy`/`tail`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`.
- **`compileSeq_sound_physical_residue`** + **`compileSeq_traj_physical_residue`**
  (Compile.lean:8454/8502) — residue-tolerant `seq` composition + trajectory.
- **`Compile.sound_of_run_residue`** (Compile.lean:8960) — last mile: residue run +
  `BitState (c.eval s)` ⇒ `Compile_sound`. PROVEN.
- **Threading toolkit** (PolyTime.lean — relocate upstream, see GAP 3):
  `Cmd.eval_preserves_BitState`, `Op.inBounds_of_UsesBelow`, `Cmd.eval_length_ge`/
  `_le`, `Cmd.size_eval_le`, `State.set_length_ge`, `BitState_set_pad`. All PROVEN.
- **Branch-merge / rewind:** `joinTwoHalts*`, `rewindBracket`/`_transport`,
  `bitReadTM`, `rewindTwoPhaseTM`, `deleteCarryTM`, `navigateAndTestTM`. PROVEN.
- **Loop:** `loopTM` (+`_run`/`_no_early_halt`), `loopBudget_le`. PROVEN.

---

# ▶ TOP-DOWN work stream — next steps

You are assembling the final pieces and designing their proofs. Create supporting
lemmas with `sorry` when they look provable; surface gaps early.

✅ **DONE (2026-06-06):** `Compile.run_physical_residue_gen` is mechanized
(op/seq proven, ifBit/forBnd dispatch proven); the W-invariant ① is on
`compileOp_sound_physical_residue` and discharged for the 5 done ops;
`physStepBudget` + its `seq` superadditivity / mono / poly are proven; **the whole
assembly is RELOCATED into `Compile.lean`** (GAP 3) before the obligation. Remaining
top-down work:

1. ✅ **DONE — the C2 obligation is PROVEN from the assembly:**
   `Compile_run_physical_residue'` (Compile.lean, right after the unprimed sorry) is
   the `res0 = []` instance of `run_physical_residue_gen`, with the correct
   `physStepBudget` budget and the `UsesBelow`/`k ≤ s.length`/`NoConsLen` hypotheses.
   Its proof body is `sorry`-free; the transitive `sorryAx` is **only** the leaf gaps
   (7 stub ops + 2 stub loop/branch machines). **What remains (the deferred GAP-4
   ripple — retarget consumers to the primed lemma):**
   - Restate `bitDecider_run` / `Compile_sound` / `Compile_polyBound` /
     `sound_of_run_residue` budgets from `overhead (size+cost)` to
     `physStepBudget …` and have them consume `Compile_run_physical_residue'`
     (threading `UsesBelow`/`NoConsLen` + a **register-count bound** through their
     signatures), then delete the unprimed `Compile_run_physical_residue` sorry.
   - Ripple the budget-shape change to the `PolyTime.lean` consumers
     (`DecidesLang.toDecidesBy`, the `inNPLang` decider bridge). The
     `inOPoly`/`monotonic` facts they need are ready (`physStepBudget_mono`/`_poly`).
2. **Close the live bridge** `DecidesLang.toDecidesBy` / `inTimePolyLang_to_inTimePoly`
   (PolyTime.lean) using the new budget shape + a **register-count bound** added to
   `DecidesLang` (or route via `DecidesLang'`) + the witness `enc_bit`. This is what
   `sat_NP` actually calls.

# ▶ BOTTOM-UP work stream — next steps

You build the gadgets the (now-pinned) contracts need. Build green per item;
`#print axioms`-clean. Probe each assembled machine end-to-end (`#eval`) before
proving its run lemma.

1. **Task 1 — unary encodings + scratch operands** (gates all 7 ops; can run in
   parallel with the move gadgets, which are done). Restate `takeAt`/`dropAt`/
   `consLen` unary (length = the register's **unary count**, not `headD 0`); bump
   `consLen`'s `Op.cost` to charge `|lenSrc|`; add empty-scratch operands
   (`copy`/`tail`/`concat` need **1**, `eqBit` needs **2**); re-lay `Nat`/product/
   `List` canonical encodings bit-level (`Nat` DONE) + `BitEncodable` instances;
   re-derive `swapCmd`/`mapFstCmd`/`mapSndCmd`; re-lay `EvalCnfCmd.encodeState`
   unary (the LIVE `sat_NP` encoding, cells `v+3`/`2` today) and discharge its
   `enc_bit`.
2. **The 7 op gadgets** in `compileOp_sound_physical_residue` (Compile.lean
   7109–7125): `copy`/`tail`/`concat` via the validated `moveRegion2TM` recipes;
   `eqBit` via a compare-and-delete loop (2 scratch); `takeAt`/`dropAt` via a
   counter-bounded transfer over `lenReg`; `consLen` unary. **The W-invariant ① is
   now a literal conjunct of `compileOp_sound_physical_residue`**
   (`State.size(out) + |res_out| ≤ State.size s + |res_in| + Op.cost o s`, already
   discharged for the 5 done ops) — each new op must establish it (it holds for the
   move recipes: freed cells → residue, scratch returns to `[]`).
3. **Build the real loop/branch machines (GAP 2 — currently 0-transition stubs):**
   - `compileTestBit t` (Compile.lean:1483): navigate to register `t` + `bitReadTM`,
     two-exit tester; feeds `compileIfBit`. Then prove
     `compileIfBit_sound_physical_residue` (statement pinned in PolyTime.lean) via
     `branchComposeFlatTM_run` + `joinTwoHalts` + the rewind bracket.
   - `compileForBnd counter bound body` (Compile.lean:1631): a `loopTM` over the
     bound's unary length that materialises the unary counter each iteration, runs
     the body, advances. Then prove `compileForBnd_sound_physical_residue` via
     `loopTM_run` + `loopTM_no_early_halt` + the body's residue contract.
   These two machines are the critical-path gadget work that unblocks the
   `ifBit`/`forBnd` cases of the assembly.

---

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (`lake` is **not** on
  PATH; LSP/most MCP features can't find it). First build slow (~minutes); iterate a
  single module with `lake build Complexity.Lang.Compile` / `…PolyTime`. Commit per
  logical step, green. The headline module is `Complexity.NP.SAT.CookLevin`.
- **Probe** a built machine end-to-end *before* proving its run lemma:
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/x.lean` with
  `import Complexity.Lang.Compile`, `open Complexity.Lang`,
  `runFlatTM N M { state_idx := M.start, tapes := [([], 0, Compile.encodeTape s)] }`.
  **Every gadget exits with its head on the trailing terminator** — rewind-bracket.
- **Axiom-check** via a scratch file: `#print axioms <name>` — must show only
  `propext`/`Classical.choice`/`Quot.sound` for new sorry-free results.
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
