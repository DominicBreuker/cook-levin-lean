# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first; they
are the authoritative, up-to-date status and plan. This file is a short pointer,
not a log.

## Where things stand

- `lake build` ✅ green (3356 jobs). `#print axioms CookLevin` =
  `[propext, sorryAx, Classical.choice, Quot.sound]` — the headline theorem is
  **conditional** (depends on `sorryAx`) and, separately, **vacuous** (S1/S2/S3,
  see ROADMAP risk register).
- The **S3 migration engine** is built and sorry-free *modulo* the one compiler
  obligation `Compile_run_physical` / `Compile_sound` (Risk **C2**).

## This session's work (recorded in ROADMAP)

All sorry-free, `#print axioms`-clean (`propext`/`Quot.sound` only); `CookLevin`
axiom profile unchanged.

**(1) The Cmd-level size bound — plan step 1a, now PROVEN.**
`Cmd.size_eval_le : State.size (c.eval s) ≤ State.size s + c.cost s`
(`Lang/Semantics.lean`). This is the clean linear invariant the compiler's
tape-length budget rests on (every intermediate tape in a `Compile c` run is
`encodeTape` of a sub-evaluation, whose size this bounds).
- The clean bound was **false for `forBnd`** (the unary loop counter
  `set counter (replicate i 1)`, size `i`, is uncharged size). The handoff's
  proposed *register-excluding* route gives a depth-dependent constant. Instead
  I **charged the counter in the cost model** — the *same* faithfulness
  principle as the prior size-aware `Op.cost` fix (writing `i` unary cells costs
  Θ(i) TM steps). `Cmd.run`'s `forBnd` now adds `iters * iters` (a closed-form
  lump ≥ Σ_{i<iters} i, kept **outside** the fold so every frame/locality lemma
  is untouched). Result: clean, depth-constant-free, and cost stays polynomial.
- Ripples were contained: `Cmd.cost_forBnd_le` gains `+ iters*iters` (no
  external consumers) and `Cmd.cost_agree`'s `forBnd` case threads the
  (agreement-stable) lump.

**(2) ⚠ NEW FINDING — the per-fragment compiler budgets cannot compose.**
While checking the next step (threading the budget), I found that the four
sorried budget lemmas are **unprovable as stated**: `compileSeq_sound`,
`compileIfBit_sound`, `compileForBnd_sound`, and the `Compile_sound` assembly
take each sub-machine's budget as the **quadratic** `Compile.overhead =(·+1)²`
and claim a quadratic-of-the-sum for the composite. But a quadratic is **not
superadditive** — summing `~cost` per-op quadratics gives a **cubic**. Worst
case `overhead(a) + 1 + overhead(a+c₂) ≤ overhead(a+1+c₂)` is **false for
`a ≥ 2`** (`a=3, c₂=1` → `42 ≰ 36`; gap grows with `a`). The fix: per-fragment
budgets must be **LINEAR** in tape length (the gadgets already prove
`appendAt_steps_le : ≤ 2·tapeLen+3`), which *do* compose into a quadratic total.
A prominent finding block now sits above `compileSeq_sound` in `Compile.lean`;
full writeup in ROADMAP Risk C2 / plan step 1b.

**(3) The linear tape-length bound — plan step 1b ingredient, now PROVEN.**
The corrected per-fragment budget must be linear in the tape length; this
supplies the analytic fact:
`Cmd.encodeTape_eval_length_le : (Compile.encodeTape (c.eval s)).length ≤
State.size s + c.cost s + max s.length k + 1` (`Lang/PolyTime.lean`), for any `c`
with `Cmd.UsesBelow c k`. Built from three reusable pieces:
- `Compile.encodeTape_length : (encodeTape s).length = State.size s + s.length +
  1` (+ `encodeRegs_length`) — `Lang/Compile.lean`.
- `Cmd.size_eval_le` (contents bound, prior session).
- `Cmd.eval_length_le : (c.eval s).length ≤ max s.length k` (register count never
  exceeds `regBound`), with helpers `State.set_length_le` /
  `State.set_length_le_of_lt` / `Op.eval_length_le` — `Lang/Frame.lean`.

## Recommended next step (plan step 1b/1c/1d — the C2 budget restatement)

Steps 1a (size bound) and the linear tape-length ingredient are done. What
remains is the run-structure work — intricate but structural-unknown-free:

1. **Restate the per-fragment contracts LINEAR.** For each gadget, the
   per-fragment physical contract should be: halts at its `exit` state, head
   rewound to `0`, tape `= encodeTape output`, at an explicit step
   `t ≤ A·(encodeTape s).length + B·cost + C` (linear), with the no-early-halt
   trajectory. The append ops already have the linear step count
   (`appendAt_steps` / `appendAt_steps_le`); `compileOp_appendOne_sound` merely
   *loosened* it to the quadratic `overhead` — restate it linear instead.
   ⚠ **Gap to close first:** the gadgets (`appendAt_run_steps`) leave the exit
   head position *existential* and do **not** rewind the head to `0` or expose a
   no-early-halt trajectory — both are required by `compileSeq_compose_physical`.
   Add head-rewind + trajectory lemmas to the gadget library before assembling.
2. **Lift the per-fragment output bound to a max-over-fragments bound.**
   `Cmd.encodeTape_eval_length_le` (done) bounds each fragment boundary's tape;
   thread it through the run so every intermediate tape is `≤ size + cost +
   regBound + 1`.
3. **Set the total budget with slack.** Define `Compile_run_physical`'s total as
   a quadratic-with-constant — concretely `Q(size,cost) ≈ C·cost·(size+cost+
   regBound+1)`, which I checked **composes** for `seq` (superadditive:
   `Q(a,c1)+Q(a+c1,c2)+1 ≤ Q(a,1+c1+c2)`, the `-C·c1·c2` cross term gives the
   slack) and for `forBnd` (the loop sums cost·tape over iterations ≤ total
   cost × max tape). The tight `(size+cost+1)²` cannot absorb the per-fragment
   constants. Safe: `toFrameworkWitness'` only needs `inOPoly`/`monotonic` — so
   replace `Compile.overhead`'s use here with `Q` (or a cubic) and re-thread
   `PolyTime.toFrameworkWitness'` / `Compile.bitDecider_run`.
4. **Concretise the 10 stub `compileOp`s** from the gadget library, each with
   its **linear-budget** `compileOp_sound`.
5. **Assemble** `compileSeq_sound` from `compileSeq_compose_physical`,
   `compileForBnd_sound` from `loopTM_run`, `compileIfBit_sound` from
   `branchComposeFlatTM_run`; then `Compile_sound`/`Compile_run_physical` by
   induction.

(Alternatively, the cheaper `map`-over-lists witness — ROADMAP step 2,
`parked/MapNatList_WIP.lean` — keeps the S3 migration moving while C2 is built.)

## Conventions

- Commit per logical step with a **green build**; record gaps in commit messages.
- New results must be `#print axioms`-clean (only `propext` / `Quot.sound` /
  `Classical.choice`). **No new axioms.** Decompose `sorry`s; don't elaborate.
- Axiom check (lean-lsp's LSP has no `lake` on PATH):
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean` with
  `#print axioms <name>`.
- See ROADMAP "Hard-won gotchas" (the `omega`/`Var` trap, nested `set` blowup,
  `State.get` literal mis-resolution). **New gotcha this session:** `set` and
  other Mathlib tactics are **unavailable in `Lang/Semantics.lean` and
  `Lang/Frame.lean`** (core-only files); write folds out explicitly or factor a
  helper lemma (see `Cmd.size_run_foldl_le`).
