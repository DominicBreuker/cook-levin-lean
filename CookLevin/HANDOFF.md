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

All sorry-free, axiom-clean. Two pieces:

**(1) Explicit step counts + corrected per-op budget** (`Lang/AppendGadget.lean`,
`Lang/Compile.lean`):
- **`appendAt_run_steps`** / **`appendAt_steps`** — `appendAt_run` re-proved with
  an explicit step count (no longer existential); **`appendAt_steps_le`** bounds it
  by `2·tapeLen + 3 ≤ overhead(tapeLen+1)`.
- **`compileOp_appendOne_sound` / `compileOp_appendZero_sound`** — discharge
  `compileOp_sound` for the two ops with real TM bodies at **general `dst`** under
  the corrected tape-length budget (closes the register-count budget bug for them).

**(2) The realistic (size-aware) cost model** — fixes the deeper cost-model gap
(`Lang/Semantics.lean`, `Lang/Frame.lean`, `Lang/PolyTime.lean`):
- Old ops were **unit cost**, but `concat`/`copy`/… grow `State.size`
  multiplicatively, so output size (hence TM steps) could be **exponential in
  layer cost** (`doubler` at n=10 → 1047 vs budget 676). **No** budget polynomial
  could bound `Compile c`. **Fix (chosen option, Coq-L-calculus-aligned):**
  `Op.cost` now charges size-increasing ops for their source data, so
  **`Op.size_eval_le : State.size (Op.eval o s) ≤ State.size s + Op.cost o s`** —
  the invariant that was *false* under unit cost, now proven (`State.size_set_add`
  is the engine). `Op.cost_agree`/`Cmd.cost_agree` generalized; the concrete
  witnesses (`id`/`swap`/`map_fst`) cost bounds re-derived.
- *Options weighed (full text in ROADMAP C2):* a separate per-witness size/weight
  bound and removing size-increasing ops were rejected — no global `weight ≤
  poly(unitCost, size)` exists, so the single realistic cost notion is necessary
  and lowest-complexity.

## Residual finding — the `forBnd` counter (next step)

The **Cmd-level** size invariant is subtler than `Op.size_eval_le`. The clean
`State.size (c.eval s) ≤ State.size s + c.cost s` is **FALSE for `forBnd`**: the
unary loop counter (`set counter (replicate i 1)`, size `i`) is *uncharged*
size. Witness: `forBnd 0 1 (op (appendOne 2))` on `[[], replicate n 1, []]` gives
output size `3n−1 > 2n+1 = size + cost`. The correct bound is still **linear** in
`(size + cost)` (counter ≤ `iters ≤ cost`, a replace not a cumulative sum), with
a constant that grows with loop-nesting depth.

## Recommended next step

Per ROADMAP plan step 1:
1. **Prove the Cmd-level size bound.** Recommended: a *register-excluding* size
   (`size minus the loop counter`) is preserved by the counter-set and grows ≤
   cost under the body (lift `Op.size_eval_le`); bound the output counter
   separately (`iters ≤ |bound| ≤ size`). Gives `maxIntermediateTapeLen ≤
   O(size + cost)`. Then restate `PolyTime.toFrameworkWitness'`'s time budget.
2. **Then** restate `Compile_sound` over the tape-length budget threading
   `regBound`, give explicit step counts to the remaining gadgets, concretise the
   10 stub `compileOp`s, and assemble.

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
  `State.get` literal mis-resolution).
