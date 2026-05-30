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
- **Step 1b-0 (leading-sentinel encoding migration) is DONE**: `encodeTape s =
  endMark :: (encodeRegs s ++ [endMark])`, `sig` stays `4`. All real consumers
  re-proven green & axiom-clean.
- **Step 1b-1 (gadget trajectory assembly) is DONE**: `appendAt_no_early_halt`
  and all its prerequisite trajectories (`composeFlatTM_no_early_halt`,
  `insertCarryTM_no_early_halt`, `scanPastDelim_no_early_halt`,
  `scan_to_mark_traj`) are proven, sorry-free, axiom-clean.

## Latest session (2026-05-30) — build fix + trajectory assembler

### Build repair

The previous agent left the build broken (5 errors in `TMPrimitives.lean`, 1 in
`Compile.lean`). Root causes:

1. **`TMPrimitives.lean` line 1161**: After `subst this` where `this : ck = c'`,
   the variable `c'` was eliminated but still referenced downstream. Fixed by
   changing `c'` → `ck` in the `state_idx_lt_states_of_step` call.
2. **`TMPrimitives.lean` line 1217**: `runFlatTM_extend_by_step` takes 5
   positional args; call was missing `_`. Added the missing argument.
3. **`TMPrimitives.lean` lines 1221–1244**: Struct literal for M₂-phase
   configuration failed to unify. Rewrote to use `h_cfg_eq` approach matching
   the working `composeFlatTM_run` pattern.
4. **`TMPrimitives.lean`**: `Option.map_some'` renamed to `Option.map_some` in
   current Mathlib.
5. **`Compile.lean`**: `appendAt_run_steps` API changed from 4 existentials
   `⟨st', hd', hrun, hhalt⟩` to 3 `⟨st', hrun, hhalt⟩` with the head explicit.
   Updated `appendBit_sound` destructuring accordingly.

### New theorems (all sorry-free, axiom-clean)

1. **`insertCarryTM_carry_no_early_halt`** (`Lang/ShiftTape.lean`): trajectory
   for the carry phase of `insertCarryTM`, by induction on `suf`.
2. **`insertCarryTM_no_early_halt`** (`Lang/ShiftTape.lean`): full trajectory
   from state 0, by cases on `suf`.
3. **`composeFlatTM_no_early_halt`** (`TMPrimitives.lean`): build repair, was
   added by previous agent but broken. Now compiles and is axiom-clean
   (`propext`/`Classical.choice`/`Quot.sound` only).
4. **`appendAt_no_early_halt`** (`Lang/AppendGadget.lean`): the **main
   trajectory assembler** for the `appendAtTM` gadget. For any step
   `k < appendAt_steps`, the machine has not reached a halting state. Built
   by induction on `dst`, mirroring `appendAt_run_steps`:
   - Base case (dst=0): `composeFlatTM_no_early_halt` combines
     `scan_to_mark_traj` with `insertCarryTM_no_early_halt`
   - Recursive case (dst=d+1): `composeFlatTM_no_early_halt` combines
     `scanPastDelim_no_early_halt` with IH

### Gotchas discovered

- **`omega` can't simplify `[].length` or `(y :: suf').length`**: need explicit
  `simp only [List.length_nil]` or `simp only [List.length_cons]` before `omega`.
- **`subst` for `h : a = b` eliminates the more recently introduced variable**:
  if `b` was introduced later, `subst` eliminates `b`, so subsequent references
  to `b` become invalid. Use the surviving variable name.
- **`simp` can close a goal that `simp; omega` can't**: if `simp` closes the
  goal, don't add `omega` — it causes "No goals to be solved" errors.

## Recommended next step — bracket the gadget with a rewind (1b-2)

### What is now done

Step 1b-1 (the trajectory assembler) is complete. You have:
- `appendAt_run_exit`: the gadget reaches exit state `appendAtTM_exit dst`
- `appendAt_no_early_halt`: for all `k < appendAt_steps`, no halting state is
  reached
- `rewindToStart_run`/`_traj`: head-rewind from any interior position to index 0

### What to do next

**Step 1b-2 — per-fragment physical contract with rewind bracket.**

Each compiled fragment's TM should be `composeFlatTM gadgetTM (scanLeftUntilTM 4 3) exit`.
The contract: halts at composite exit, head back at sentinel (index 0),
tape = `encodeTape output`, in ≤ `A·(encodeTape s).length + B·cost + C` steps
(linear budget — the gadget's `2·tapeLen+3` plus the rewind's `tapeLen+1`).

Concrete steps:
1. **Expose the explicit exit head** in `appendAt_run_steps`/`appendAt_run_exit`.
   Currently the head is existential. The head is
   `pre.length + (regBlocks skipped).length + body.length + (0::post).length`
   — already explicit in `scanInsert_run` (base case). Thread it through the
   `dst` recursion.
2. **Compose gadget with rewind** via `composeFlatTM_run`:
   - M₁ = `appendAtTM ins dst`, M₂ = `scanLeftUntilTM 4 3`
   - h_run1 = `appendAt_run_exit`, h_traj1 = `appendAt_no_early_halt` ✅
   - h_run2 = `rewindToStart_run`, h_traj2 = `rewindToStart_traj`
   - Check that the interior cells (between head and sentinel) are all `< sig`
     and ≠ `endMark` — this follows from the encoding (interior = `{0,1,2}`).
3. **State the linear per-fragment contract** as a standalone lemma
   `appendBit_physical` or similar.

**Step 1b-3 — lift the per-fragment output bound to a max-over-fragments bound.**
`Cmd.encodeTape_eval_length_le` (done) bounds each fragment boundary's tape;
thread it through the run so every intermediate tape is `≤ size + cost +
regBound + 2`.

**Step 1b-4 — set the total budget with slack.** Define `Compile_run_physical`'s
total as a quadratic-with-constant — concretely `Q(size,cost) ≈ C·cost·(size+
cost+regBound+1)`, which composes for `seq` and `forBnd`. Replace
`Compile.overhead`'s use with `Q` and re-thread `PolyTime.toFrameworkWitness'`.

**Step 1c — concretise the 10 stub `compileOp`s** from the gadget library.

**Step 1d — assemble** `compileSeq_sound`, `compileForBnd_sound`,
`compileIfBit_sound`; then `Compile_sound`/`Compile_run_physical` by induction.

## Earlier sessions' work (recorded in ROADMAP)

**(1) Cmd-level size bound (step 1a, PROVEN).**
`Cmd.size_eval_le : State.size (c.eval s) ≤ State.size s + c.cost s`
(`Lang/Semantics.lean`).

**(2) Linear tape-length bound (step 1b ingredient, PROVEN).**
`Cmd.encodeTape_eval_length_le` (`Lang/PolyTime.lean`).

**(3) Leading-sentinel encoding (step 1b-0, DONE).**
`Compile.encodeTape s = Compile.endMark :: (Compile.encodeRegs s ++ [Compile.endMark])`.

**(4) Head-rewind primitive (call-ready).**
`ScanLeft.rewindToStart_run`/`_traj` (`Lang/ScanLeft.lean`).

**(5) ⚠ KEY FINDING — per-fragment budgets must be LINEAR.**
The four sorried budget lemmas are unprovable as stated with quadratic
`Compile.overhead = (·+1)²`. Per-fragment budgets must be linear in tape length
(gadgets prove `appendAt_steps_le : ≤ 2·tapeLen+3`), which compose into a
quadratic total. See ROADMAP Risk C2.

## Conventions

- Build: `lake build` from repo root.
- Commit per logical step with a **green build**; record gaps in commit messages.
- New results must be `#print axioms`-clean (only `propext` / `Quot.sound` /
  `Classical.choice`). **No new axioms.** Decompose `sorry`s; don't elaborate.
- Axiom check:
  ```
  LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean
  ```
  with `#print axioms <name>`.
- See ROADMAP "Hard-won gotchas" (the `omega`/`Var` trap, nested `set` blowup,
  `State.get` literal mis-resolution).
- **`omega` gotcha**: `omega` can't simplify `[].length` or `(h :: t).length`.
  Use `simp only [List.length_nil]` or `simp only [List.length_cons]` first.
- **`subst` gotcha**: `subst h` for `h : a = b` eliminates the more recently
  introduced variable. Don't reference the eliminated variable afterward.
- **`set`/Mathlib tactics**: unavailable in `Lang/Semantics.lean` and
  `Lang/Frame.lean` (core-only files); write folds out explicitly.
