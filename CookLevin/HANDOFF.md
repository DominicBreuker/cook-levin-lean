# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first for the
authoritative status and plan. This file says exactly what to do next.

## Where things stand

- `lake build` ✅ green (3358 jobs). First build is slow (mathlib); one module
  rebuilds in ~5–10s after. `lake` is **not on PATH** —
  `export PATH="$HOME/.elan/bin:$PATH"`.
- **Risk C2 (compiler soundness) is the focus.** The `clear` op has a **real TM
  machine** (`clearRegionTM` in `ClearGadget.lean`), wired into `compileOp` with a
  sorry-free `CompiledCmd`. Its **run lemma is being built** (steps 1–6 below):
  steps 1–3 are **DONE** (navigation + the full delete branch,
  `Compile.clearBody_delete_run`); steps 4–6 remain. The `clear` case of
  `compileOp_sound_physical_residue` (Compile.lean) is still `sorry` (closes at
  step 6); the cross-register ops (`copy`/`tail`/`head`/…) are also `sorry`.

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
- **Step 3 — delete branch DONE** (in `Compile.lean`, since it ties to
  `encodeTape`): `Compile.clearBody_delete_run` — when register `dst` is nonempty,
  `clearBodyRawTM dst` from head `0` on `encodeTape s ++ res` reaches
  `clearBodyRawTM_exitLoop dst` with head `0` and tape `encodeTape (s.set dst
  (s.get dst).tail) ++ (res ++ [0])`. Core sub-lemma `Compile.stepDeleteRewind_run`
  (the `stepRight ⨾ deleteCarry ⨾ stepLeft ⨾ rewindTwoPhase` positioning — where
  both bugs lived). New reusable pieces: `encodeTape_residue_twoPhaseRewind`,
  `encodeTape_reg_decomp_at` (explicit `pre`/`rest`), `regBlocks_map_shiftReg`
  (already existed), `BitState_set_tail`, `haltingStateReached_of_halt`,
  `stepLeftTM_run_blank` (ScanLeft), and the ClearGadget halt lemmas
  `innerRewind_halt_eight` / `deleteRewindRawTM_halt_fifteen` /
  `stepDeleteRewindRawTM_halt_seventeen`.

## NEXT TASK: finish the `clear` run lemma (steps 4–6)

### Step 4 — done-branch run (delim path of `clearBodyRawTM`)
Mirror `clearBody_delete_run`, but use `branchComposeFlatTM_run_neg` (M₃ =
`justRewindTM = scanLeftUntilTM 4 3`) with `navigateAndTestTM_run_delim` (register
empty: `tail = 0 :: …`). `h_run2` = run of `justRewindTM` from the empty
register's delimiter (head `1+|regBlocks skipped|`, interior) left to the sentinel
`3` at index 0 — use `ScanLeft.rewindToStart_run`/`scanLeft_run` (all cells
between are `{0,1,2}`, no `3`). Tape unchanged; result exit
`clearBodyRawTM_exitDone dst = (navigateAndTestTM dst).states + 19 + 1`. The
target lemma: `Compile.clearBody_done_run` (register empty → `s` unchanged, exit
done, head 0, tape `encodeTape s ++ res`). Reuse the step-3 setup
(`encodeTape_reg_decomp_at`, `regBlocks_map_shiftReg`, the `htape_nav` connection,
`htape4`); for the empty case `s.get dst = []` so the content start cell is the
delimiter `0` (use the second conjunct of `encodeTape_reg_decomp_at` with
`shiftReg [] = []`).

### Step 5 — assemble `clearRegionTM` run via `loopTM_run`
**⚠ First build a `branchComposeFlatTM_no_early_halt` combinator** (TMPrimitives,
mirror `composeFlatTM_no_early_halt`): `loopTM_run`'s per-iteration contract needs
each body run's *trajectory* (`≠exitDone ∧ ≠exitLoop ∧ halting=false`), but steps
3–4 only produce the *run*. With it, give `clearBody_delete_run`/`_done_run` a
trajectory each (they already produce the run; the no-early-halt is the same
`branchComposeFlatTM` shape with the sub-machine trajectories — nav's traj exists
(`navigateAndTestTM_no_early_halt`), the M₂/M₃ trajs need `stepDeleteRewind`/
`justRewind` no-early-halt, also missing — derive from the nested `composeFlatTM_no_early_halt`).

Then feed `loopTM_run` with
`T j = encodeTape (s.set dst ((s.get dst).drop (n−j))) ++ (res_in ++ replicate (n−j) 0)`,
`n = |s.get dst|`, so `T n = encodeTape s ++ res_in` (via `set_get_self`) and
`T 0 = encodeTape (clear dst s) ++ (res_in ++ replicate n 0)`. `tDone` = step-4
count; `tIter j` = step-3 count (`T (j+1) → T j`); iteration count `n`. The
register-`dst` block invariant across iterations is `set_tail_iterate` /
`iterate_tail_clear` (proven). Note step-3/4 are stated generically over any
`s'`/`res'`, so each iteration instantiates them at `s' = s.set dst (drop (n−j−1))`,
`res' = res_in ++ replicate (n−j−1) 0`.

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
