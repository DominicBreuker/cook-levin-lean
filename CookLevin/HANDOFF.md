# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first for the
authoritative status and plan. This file says exactly what to do next.

## Where things stand

- `lake build` ✅ green (3358 jobs). First build is slow (mathlib); one module
  rebuilds in ~5–10s after. `lake` is **not on PATH** —
  `export PATH="$HOME/.elan/bin:$PATH"`.
- **Risk C2 (compiler soundness) is the focus.** The `clear` op has a **real TM
  machine** (`clearRegionTM` in `ClearGadget.lean`), wired into `compileOp` with a
  sorry-free `CompiledCmd`. The `clear` case of `compileOp_sound_physical_residue`
  (Compile.lean ~2744) still has a `sorry` for its **run lemma**; the remaining
  cross-register ops (`copy`/`tail`/`head`/…) are also `sorry`.

## ⚠ This session: `clearRegionTM` had two architecture bugs (now FIXED + validated)

The machine had been *built and proven valid* but **never run end-to-end**.
`#eval` probing (the risk-based go/no-go) found two structural bugs that would
have made the run lemma unprovable:

1. **delete branch (all dst):** `deleteCarryTM` leaves the head one cell *past*
   the tape end (on a blank), and `rewindTwoPhaseTM`'s phase-1 `scanLeftUntilTM`
   halts immediately at its boundary on a blank. **Fix:** insert one `stepLeftTM 4`
   between `deleteCarryTM` and `rewindTwoPhaseTM` in `deleteRewindRawTM`.
2. **navigation (dst≥1):** the old `navigateToRegTM (d+1) = scanPastDelim ⨾
   navigateToRegTM d` overshot (the inner base `stepRight` was spurious). **Fix:**
   M₁-recursion `navigateToRegTM (d+1) = navigateToRegTM d ⨾ scanPastDelim`
   (= `stepRight ⨾ scanPastDelim^dst`).

Both fixes are validated by `#eval` of the *real* `clearRegionTM` for dst∈{0,1,2},
empty/nonempty regs, multi-register nav, and incoming residue — every case yields
`encodeTape (clear dst s) ++ (res_in ++ replicate |s.get dst| 0)`, head 0, at the
loop's unique exit. **The machine now computes correctly; build the run lemma
against it with confidence.**

## Validated machine facts (use these — they are #eval-confirmed)

- `navigateToRegTM dst`: `states = 2 + 3·dst` (`navigateToRegTM_states`), exit
  `navigateToRegTM_exit dst`, lands head at register `dst`'s content start.
- `delimTestTM 4`: 3 states; exit `1` (content) / `2` (delimiter), no head move.
- `deleteRewindRawTM`: `states = 17`. `stepDeleteRewindRawTM`: `states = 19`,
  **found halt `stepDeleteRewindTM_exit = 17`**, unreached boundary halt `18`.
- `clearBodyRawTM_exitLoop dst = (navigateAndTestTM dst).states + 17` (delete+continue);
  `clearBodyRawTM_exitDone dst = (navigateAndTestTM dst).states + 19 + 1` (empty, stop).
- `clearRegionTM dst = loopTM (clearBodyRawTM dst) exitDone exitLoop`; unique exit
  `clearRegionTM_exit dst = (clearBodyRawTM dst).states`. `loopTM` tolerates the
  extra unreached halt `18`, so **no boundary demotion is needed** for `clear`.

## Proven this session (sorry-free, axiom-clean) — the run-lemma foundations

In `ClearGadget.lean`, stated with literal `3` as the leading sentinel (Compile is
downstream, can't be imported; instantiate via `encodeTape_reg_decomp`). The tape
is `3 :: (regBlocks skipped ++ tail)` where `regBlocks`/`scanPast_block`/
`scan_block_before` are reused from `AppendGadget`/`Navigate`.

- **Step 1 — `navigateToRegTM_run` / `_no_early_halt`** (via combined
  `navigateToRegTM_run_traj`, reverseRecOn on `skipped`). Lands head at
  `1 + |regBlocks skipped|`, `navSteps skipped` steps, tape unchanged. Helpers:
  `navSteps`, `navSteps_append_singleton`, `regBlocks_append_singleton`,
  `navigateToRegTM_exit_is_halt`, generic `ne_of_not_halting`.
  *Note: M₁-recursion forces run+traj to be proven together (composeFlatTM_run
  needs the recursive machine's own trajectory).*
- **Step 2 — `navigateAndTestTM_run_content` / `_run_delim` / `_no_early_halt`**
  + `navigateAndTestTM_exit_content_is_halt` / `_delim_is_halt`. Helpers
  `navAndTest_cell` (content-start cell value, via `getElem?` to dodge
  dependent-`Fin` `rw` motive errors) and `navAndTest_sym_bound`.

## NEXT TASK: finish the `clear` run lemma (steps 3–6)

### Step 3 — delete-branch run (content path of `clearBodyRawTM`)
Use `branchComposeFlatTM_run_pos` with M₁ = `navigateAndTestTM dst`,
M₂ = `stepDeleteRewindRawTM`, exit_pos = `navigateAndTestTM_exit_content dst`,
exit_neg = `navigateAndTestTM_exit_delim dst`.
- `h_run1` = `navigateAndTestTM_run_content` (reg nonempty: `tail = (c0+1)::…`).
- `h_traj1` (needs `≠exit_pos ∧ ≠exit_neg ∧ halting=false`): from
  `navigateAndTestTM_no_early_halt` + the two `..._is_halt` lemmas via `ne_of_not_halting`.
- `h_run2` = run of `stepDeleteRewindRawTM` = `stepRightTM ⨾ (deleteCarryTM ⨾
  stepLeftTM ⨾ rewindTwoPhaseTM)`. Thread head positions:
  content-start `p = 1+|regBlocks skipped|` → stepRight `p+1` → `deleteCarry_tail_step`
  (head `p+1+L`, = tape end, tape `encodeTape (s.set dst tail) ++ (res++[0])`) →
  stepLeft (head end−1) → `rewindTwoPhase_run` (head 0). Result exit
  `(navigateAndTestTM dst).states + 17`.
The math is `Compile.deleteCarry_tail_step` (already proven); compose the
sub-machine runs with `composeFlatTM_run` (3 levels) to assemble `stepDeleteRewindRawTM`'s run.

### Step 4 — done-branch run (delim path of `clearBodyRawTM`)
`branchComposeFlatTM_run_neg`, M₃ = `justRewindTM = scanLeftUntilTM 4 3`.
`h_run1` = `navigateAndTestTM_run_delim`. `h_run2` = scanLeftUntilTM from the
empty register's delimiter (head `1+|regBlocks skipped|`, interior) left to the
sentinel `3` at index 0 — use `ScanLeft.rewindToStart_run`/`scanLeft_run` (all
cells between are `{0,1,2}`, no `3`). Tape unchanged; exit
`(navigateAndTestTM dst).states + 19 + 1`.

### Step 5 — assemble `clearRegionTM` run via `loopTM_run`
`T j = encodeTape (s.set dst ((s.get dst).drop (n−j))) ++ (res_in ++ replicate (n−j) 0)`
with `n = |s.get dst|`, so `T n = encodeTape s ++ res_in` (via `set_get_self`) and
`T 0 = encodeTape (clear dst s) ++ (res_in ++ replicate n 0)`. Feed `loopTM_run`:
`tDone` = step-4 count (register empty at `T 0`); `tIter j` = step-3 count
(delete one cell, `T (j+1) → T j`); iteration count `n`. Each `T j`'s register-`dst`
block decomposition comes from `encodeTape_reg_decomp` / `clear_block_decomp` /
`set_tail_iterate` (proven). Convert literal-`3` nav lemmas to `encodeTape` form
here (`encodeTape s = 3 :: (encodeRegs s ++ [3])`, so the nav `skipped` = the first
`dst` registers, `tail` = `shiftReg (s.get dst) ++ 0 :: rest`).

### Step 6 — discharge the `clear` case of `compileOp_sound_physical_residue`
`res_out = res_in ++ replicate |s.get dst| 0` (`ValidResidue` via
`ValidResidue_append_replicate_zero`). Budget `9·tapeLen²+9` (quadratic; each of
the `n ≤ tapeLen` iterations is O(tapeLen)). Then move to the cross-register ops
(see ROADMAP C2.c: `copyBlockTM` is the missing primitive).

## Gotchas (hit this session)
- **`#eval`-probe a built machine end-to-end before proving its run lemma.** Both
  bugs above were invisible to validity proofs; one probe surfaced them.
- **`deleteCarryTM` leaves the head one past the tape end** (on a blank) and
  `scanLeftUntilTM` won't start on a blank — always `stepLeftTM` first.
- **Don't `rw` a list inside `l.get ⟨i, h⟩`** — `h`'s type depends on `l`, giving
  "motive is not type correct". Compute via `getElem?` (proof-free), then transport
  with `List.getElem?_eq_getElem`.
- **M₁-recursion** (recursive machine in the `composeFlatTM` M₁ slot) needs that
  machine's *trajectory* for `composeFlatTM_run` — prove run + no-early-halt
  together. (`appendAtTM` avoids this with M₂-recursion + a fixed M₁.)
- `omega` can't see through record projections (`{…}.state_idx`) or `def`-constants
  (`delimTestTM_exit_content`) — `show` the reduced/`Nat` form first.
- `composeFlatTM_haltingStateReached_M2` is `private`; derive "exit is a halt
  state" from `composedHalt = replicate M₁.states false ++ M₂.halt` directly.

## Key files

| File | Contents |
|------|----------|
| `Lang/ClearGadget.lean` | `navigateToRegTM` (**M₁-recursion, fixed**), `delimTestTM`, `navigateAndTestTM`, `deleteRewindRawTM` (**stepLeft inserted, fixed**), `clearRegionTM`; **all validity + run-lemma steps 1–2 proven**; steps 3–6 TODO |
| `Lang/Compile.lean` | compiler; residue infra (`TapeOK`/`ValidResidue`); append op done; `compileOp_sound_physical_residue` (`clear` + 9 cross-register `sorry`s); proven `clear` math (`deleteCarry_tail_step`, `set_tail_iterate`, `iterate_tail_clear`, `clear_block_decomp`, `encodeTape_reg_decomp`); `Compile_run_physical_residue` (`sorry`) |
| `Lang/ScanLeft.lean` | `stepLeftTM`/`stepRightTM`, `scanLeftUntilTM`, `rewindToStart_run`, `rewindFromEndTM`, `rewindTwoPhaseTM` (+`rewindTwoPhase_run`/`_no_early_halt`) |
| `Lang/AppendGadget.lean` | `appendAtTM`, `regBlocks`, `scanPast_block`, append op residue contract template (`opAppendBit_physical_residue`) |
| `Lang/ShiftTape.lean` | `deleteCarryTM` (+`_run`/`_no_early_halt`), `insertCarryTM` |
| `Complexity/TMPrimitives.lean` | `composeFlatTM`/`branchComposeFlatTM`/`loopTM` (+ `_run`/`_no_early_halt`/`_valid`) |

## Conventions
- Build `lake build` (or `lake build Complexity.Lang.X`); commit per logical step
  with a **green build**; new results must be `#print axioms`-clean (only
  `propext`/`Quot.sound`/`Classical.choice`; **no `sorryAx`** for a finished lemma).
- Probe `#eval` files via
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/probe.lean`.
- See ROADMAP "Hard-won gotchas" and "How we work" for full methodology.
