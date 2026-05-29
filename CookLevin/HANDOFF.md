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

New, sorry-free, axiom-clean (`Lang/AppendGadget.lean`, `Lang/Compile.lean`):
- **`appendAt_run_steps`** — `appendAt_run` re-proved with an **explicit step
  count** `appendAt_steps` (no longer existential). `appendAt_run` kept as the
  existential corollary.
- **`appendAt_steps_le`** — the step count is `≤ 2·tapeLen + 3`, hence below
  `Compile.overhead (tapeLen + 1) = (tapeLen + 2)²`.
- **`compileOp_appendOne_sound` / `compileOp_appendZero_sound`** (via private
  `Compile.appendBit_sound`) — discharge `compileOp_sound` for the two ops with
  real TM bodies, at **general `dst`**, under the corrected tape-length budget
  `Compile.overhead ((encodeTape s).length + Op.cost o s)`. This closes the
  prior session's register-count budget bug (reason #1) for the append ops.

## This session's finding — the cost-model gap (the new gating issue)

Fixing the budget to tape length is **necessary but NOT sufficient**.
`compileOp_sound`/`Compile_sound` is false for a *second, deeper* reason:

- Ops are **unit cost** (`Op.cost _ _ = 1`), but `concat`/`copy`/`consLen` grow
  `State.size` **multiplicatively** in one step. So a unit-cost program can have
  **output size exponential in its layer cost**, and the TM must write that
  output. Evaluated witness `doubler := forBnd 2 1 (op (concat 0 0 0))` on
  `[[1], replicate n 1]`: at `n = 10` output tape length is **1047** vs corrected
  budget **676**; at `n = 19`, **524329 vs 1936**.
- ⇒ **No fixed-degree budget polynomial in `(inputSize + cost)` can bound
  `Compile c`'s step count.** The invariant the budget silently assumes —
  `maxIntermediateTapeLen ≤ inputLen + cost` — fails for size-increasing ops.

## Recommended next step

Per ROADMAP plan step 1 (now reordered):
1. **Resolve the cost-model gap first (a design fork).** Recommended, Coq-aligned:
   redefine `Op.cost o s` to dominate per-op size growth
   (`State.size (Op.eval o s) - State.size s ≤ Op.cost o s`), then prove
   `State.size (c.eval s) ≤ State.size s + c.cost s` (and for intermediate
   states) by induction on `Cmd`. That restores `maxSize ≤ inputSize + cost`.
   *Ripples:* re-derive `cost_le`/`forBnd`-cost lemmas; restate
   `PolyTime.toFrameworkWitness'`'s time budget (it bakes in the old budget).
   *(Alternative: carry a per-`Cmd` `maxSize` bound and budget `cost ×
   overhead(maxSize)`.)*
2. **Then** restate `Compile_sound` over the tape-length budget threading
   `regBound`, give explicit step counts to the remaining gadgets (lower-level
   lemmas already carry them), concretise the 10 stub `compileOp`s, and assemble.

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
