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
- **Step 1b-2 (per-fragment physical contract for the append op) is DONE**:
  `ScanLeft.rewindFromEndTM` (the *corrected* tail rewind — see finding below),
  `AppendGadget.appendAt_rewind_run`/`_no_early_halt`, and
  `Compile.appendBit_physical` (the `encodeTape`-level contract) are proven,
  sorry-free, axiom-clean. See "Latest session" below.

## Latest session (2026-05-30, second) — rewind finding + per-fragment physical contract (step 1b-2 DONE for the append op)

### ⚠ KEY RISK FINDING (verified empirically + by arithmetic)

The append gadget **exits with its head on the trailing terminator** (`endMark =
3`), **not** "just left of it" as the previous docstrings/HANDOFF claimed.
`insertCarryTM_run` leaves the head on the *last* tape cell (head = tapeLen − 1).
Verified by `#eval`: `appendAtTM 2 0` on `[3,2,1,0,1,2,0,3]` exits at **head 8**
of the 9-cell output `[3,2,1,2,0,1,2,0,3]` (the trailing `3`).

**Consequence:** the planned rewind `scanLeftUntilTM 4 3` started there **halts
immediately** (it reads its target `3` on the very first cell) and never rewinds
to index `0`. The canonical tape has *two* `3`s and the head sits on the wrong
one. The naive 1b-2 plan does not work. (The stale "to the left of the trailing
terminator" docstrings in `AppendGadget.lean` are now corrected.)

### Fix shipped (all sorry-free, axiom-clean: `propext`/`Classical.choice`/`Quot.sound`)

1. **`ScanLeft.rewindFromEndTM sig target := composeFlatTM (stepLeftTM sig)
   (scanLeftUntilTM sig target) 1`.** A new `stepLeftTM` does one unconditional
   `Lmove` (off the terminator), then `scanLeftUntilTM` scans left to the
   **leading** sentinel at index `0`. Lemmas: `stepLeftTM_step/_run/_valid`,
   `rewindFromEndTM_run` (halts in `head + 2` steps at state `3`, head `0`),
   `rewindFromEndTM_no_early_halt`. The starting cell is **unconstrained**; only
   interior cells `1 … head-1` must be `< sig` and `≠ target`. Verified:
   `rewindFromEndTM 4 3` from head 8 reaches state 3, head 0.
2. **`AppendGadget.appendAtThenRewindTM ins dst := composeFlatTM (appendAtTM ins
   dst) (rewindFromEndTM 4 3) (appendAtTM_exit dst)`** with the gadget-level
   physical contract: `appendAt_rewind_run` (run to composite exit `3 +
   appendAtTM.states`, head `0`, tape `= … ++ ins :: 0 :: post`) and
   `appendAt_rewind_no_early_halt` (trajectory). Verified end-to-end: state 12,
   head 0, tape = output encoding.
3. **`Compile.appendBit_physical`** (the `encodeTape`-level per-fragment
   contract): on `encodeTape s`, the bracketed machine halts at exit `3 +
   appendAtTM.states`, head `0`, tape `= encodeTape (s.set dst (s.get dst ++
   [bit]))`, never halting earlier, in **linear** steps `t ≤ 3·(encodeTape
   s).length + 6`. Three rewind side-conditions discharged from `encodeTape`
   structure via new reusable lemmas `Compile.encodeTape_get_zero`,
   `encodeTape_lt_four`, `encodeTape_interior_ne_endMark`. **This is the exact
   form `compileSeq_compose_physical` consumes.**

### Recommended next step

The per-op physical-contract *pattern* is now established and validated for the
append op. The remaining C2 work is structural-unknown-free:
- **1b-3/1b-4:** restate `compileSeq_sound`/`compileIfBit_sound`/
  `compileForBnd_sound` and `Compile_run_physical` with the **physical**
  contract (the `appendBit_physical` shape: explicit `t`, head-`0` exit, tape =
  `encodeTape output`, trajectory, linear/quadratic budget). Compose via
  `compileSeq_compose_physical` (already proven). Lift per-fragment linear bounds
  to a quadratic total with `regBound`/constant slack (see ROADMAP C2 reason #3).
- **1c:** concretise the 10 stub `compileOp`s, each with a `*_physical` contract
  mirroring `appendBit_physical` (gadget → `rewindFromEndTM` bracket → discharge
  the three `encodeTape` conditions).
- **1d:** assemble `Compile_run_physical` by induction on `Cmd`.

⚠ When bracketing **any** future gadget with a rewind: its head will be on the
trailing terminator (the inserters/scanners end at the right), so use
`rewindFromEndTM`, never a bare `scanLeftUntilTM`/`rewindToStart`. The
`rewindToStart_run`/`_traj` wrappers (head-relative, constrain the head cell) are
**only** valid when the head is NOT on a `target` cell — which is not the gadget
exit case.

## Earlier this session (2026-05-30) — build fix + trajectory assembler

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

## Recommended next step — generalise the per-fragment contract, then assemble

Step 1b-2 (the per-op physical contract) is **DONE for the append op** — see
"Latest session" above for `rewindFromEndTM`, `appendAt_rewind_run`/
`_no_early_halt`, and `Compile.appendBit_physical`. The structural unknowns of
the rewind bracket are now resolved and validated. What remains in C2 is
unknown-free engineering following the established pattern.

**The per-op physical-contract pattern** (replicate for each op):
1. Build the gadget machine (the op's TM) and prove its run-to-exit + explicit
   step count + no-early-halt trajectory (like `appendAt_run_exit` /
   `appendAt_no_early_halt`).
2. Bracket with `ScanLeft.rewindFromEndTM 4 3` via `composeFlatTM_run` /
   `composeFlatTM_no_early_halt`. **The head exits on the trailing terminator —
   `rewindFromEndTM` steps off it first; a bare `scanLeftUntilTM`/`rewindToStart`
   would halt immediately.** Discharge the three `encodeTape` side-conditions
   with `Compile.encodeTape_get_zero`/`encodeTape_lt_four`/
   `encodeTape_interior_ne_endMark` (all proven, reusable).
3. State the `encodeTape`-level `*_physical` contract (explicit `t`, head-`0`
   exit, tape = `encodeTape output`, trajectory, **linear** budget) like
   `Compile.appendBit_physical`.

**Step 1c — concretise the 10 stub `compileOp`s** (`opClear`, `opCopy`, `opTail`,
`opHead`, `opEqBit`, `opNonEmpty`, the four length-as-value ops) from the gadget
library, each with its `*_physical` contract per the pattern above.

**Step 1b-3/1b-4/1d — assemble `Compile_run_physical`.**
- Restate `compileSeq_sound`/`compileIfBit_sound`/`compileForBnd_sound` with the
  **physical** contract (the `appendBit_physical` shape), composing via the
  already-proven `compileSeq_compose_physical` (and `branchComposeFlatTM_run` /
  `loopTM_run`). Each fragment's exit has head `0`, so its config *is* the next
  fragment's `initFlatConfig` — composition is clean.
- Lift per-fragment **linear** budgets to a **quadratic total** with
  `regBound`/constant slack (ROADMAP C2 reason #3): `Σ_{~cost frags}
  O(tapeLen) ≤ O(cost·(size+cost+regBound))`. `Cmd.encodeTape_eval_length_le`
  (done) caps each intermediate tape; thread it as a max over fragment
  boundaries.
- Assemble `Compile_run_physical` by induction on `Cmd`, then re-thread
  `PolyTime.toFrameworkWitness'` (it only needs `inOPoly`).

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
- **`get`-congruence across a list equality without a dependent `rw`**: to prove
  `l.get ⟨i,h⟩ = l'.get ⟨i,h'⟩` from `hl : l = l'`, do **not** `rw [hl]` (the
  Fin's proof `h : i < l.length` makes the motive ill-typed). Route through
  `getElem?` (no proof arg): `congrArg (·[i]?) hl`, then
  `rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem h']` and
  `Option.some.inj`. See `Compile.appendBit_physical`'s `hget_eq`.
- **Rewind gotcha (the 2026-05-30 finding)**: a gadget's head exits on the
  **trailing** `endMark`, so use `ScanLeft.rewindFromEndTM` (steps off it first),
  never `scanLeftUntilTM`/`rewindToStart_run` directly (they halt on the first
  `3`).
- **`set`/Mathlib tactics**: unavailable in `Lang/Semantics.lean` and
  `Lang/Frame.lean` (core-only files); write folds out explicitly.
