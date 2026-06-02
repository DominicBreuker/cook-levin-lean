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
  steps 1–4 are **DONE** (navigation, navigate-and-test, the full delete branch
  `Compile.clearBody_delete_run`, the done branch `Compile.clearBody_done_run`),
  plus step 5's `branchComposeFlatTM_no_early_halt_pos/_neg` combinator and the
  `clearBodyRawTM` halt facts. Remaining: the `stepDeleteRewind` trajectory cascade
  (step 5a) + the `loopTM` assembly (step 5b) + step 6. The `clear` case of
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

- **Step 4 — done branch DONE**: `Compile.clearBody_done_run` — register `dst`
  empty → `clearBodyRawTM dst` reaches `clearBodyRawTM_exitDone dst`, tape
  unchanged, head `0`. Via `branchComposeFlatTM_run_neg` (M₃ = `justRewindTM`) +
  `navigateAndTestTM_run_delim` + `ScanLeft.rewindToStart_run` (cells to the
  sentinel are `{0,1,2}` via `encodeRegs_no_endMark`).
- **Step 5 — combinator + halt facts DONE**:
  `TMPrimitives.branchComposeFlatTM_no_early_halt_pos`/`_neg` (the branch analogue
  of `composeFlatTM_no_early_halt`, needed for `loopTM`'s per-iteration
  trajectory) and `ClearGadget.clearBodyRawTM_exitLoop_is_halt` /
  `_exitDone_is_halt`.

## NEXT TASK: finish step 5 (trajectory cascade + `loopTM` assembly), then step 6

### Step 5a — the `stepDeleteRewind` trajectory cascade (the one remaining blocker)
`loopTM`'s iteration contract needs the delete-body *trajectory*; via
`branchComposeFlatTM_no_early_halt_pos` (M₂ = `stepDeleteRewindRawTM`) that needs
a `stepDeleteRewindRawTM` no-early-halt, which the run side
(`Compile.stepDeleteRewind_run`) doesn't yet produce. Build the cascade
(mirroring `stepDeleteRewind_run`, replacing each `composeFlatTM_run` with
`composeFlatTM_no_early_halt`; all sub-machine trajectories exist:
`stepRightTM_no_early_halt`, `deleteCarryTM_no_early_halt`,
`stepLeftTM_no_early_halt`, `ScanLeft.rewindTwoPhase_no_early_halt`):
1. **Upgrade `Compile.encodeTape_residue_twoPhaseRewind`** to return `run ∧ traj`
   with a shared step count (add `ScanLeft.rewindTwoPhase_no_early_halt`, same
   side-conditions already discharged). Cleanest: change it to return the explicit
   `(head-p+1)+1+(1+1+p)` step count instead of `∃ steps`.
2. `Compile.stepDeleteRewind_no_early_halt` — 3-level `composeFlatTM_no_early_halt`
   reusing the step-3 setup (decomp / `midSuf` / `Tout` / `htape_in` / `htape_out`).
   The `h_run1` at each level = the same `stepRight`/`deleteCarry`/`stepLeft` runs;
   the `≠exit` of `deleteCarry`'s `h_traj1` comes from `ne_of_not_halting` (halt 6).
3. **Give `clearBody_delete_run` / `clearBody_done_run` a trajectory each** (return
   `run ∧ traj`): `branchComposeFlatTM_no_early_halt_pos` (h_traj2 = step 5a.2) for
   delete; `_neg` (h_traj3 = `ScanLeft.rewindToStart_traj`) for done. The `h_traj1`
   = `navigateAndTestTM_no_early_halt` + the two `..._is_halt` lemmas. Update the
   call sites (`obtain ⟨t, h_run, h_traj⟩`).

### Step 5b — assemble `clearRegionTM` run via `loopTM_run`
`loopTM_run` (`TMPrimitives.lean` @3788) needs (`B = clearBodyRawTM dst`,
`exitDone`/`exitLoop` = the two `clearBodyRawTM_exit…`, `B.start = 0`):
- `T : Nat → tape`, `h_sym : ∀ n v, currentTapeSymbol (T n) = some v → v < B.sig` (=4);
- `tDone` + **`h_done`**: `run tDone B {0,[T 0]} = some {exitDone, [T 0]}` **∧** its
  trajectory `∀ k<tDone, ≠exitDone ∧ ≠exitLoop ∧ halting=false` — this is exactly
  `clearBody_done_run`(+traj) at the **empty** state (register cleared, `T 0`);
- per-iteration **`h_iter j`** (for `j < n`): `run (tIter j) B {0,[T (j+1)]}
  = some {exitLoop, [T j]}` **∧** trajectory — exactly `clearBody_delete_run`(+traj);
- conclusion: `run (loopBudget tIter tDone n) (loopTM B exitDone exitLoop) {0,[T n]}
  = some {B.states, [T 0]}` (and `B.states = clearRegionTM_exit dst`).

Use `T j = encodeTape (s.set dst ((s.get dst).drop (n−j))) ++ (res_in ++ replicate (n−j) 0)`,
`n = |s.get dst|`, so `T n = encodeTape s ++ res_in` (via `set_get_self`,
`drop 0`, `replicate 0`) and `T 0 = encodeTape (clear dst s) ++ (res_in ++
replicate n 0)` (`drop n` empties `dst`). Instantiate the generic step-3/4 lemmas
per iteration at `s' = s.set dst (drop (n−j−1))`, `res' = res_in ++ replicate
(n−j−1) 0`; the bridge `s'.set dst (s'.get dst).tail = s.set dst (drop (n−j))`
and `res'++[0] = res_in ++ replicate (n−j) 0` is `set_tail_iterate` +
`List.replicate_succ` (proven `clear` math). The done branch fires at `T 0`
because `(s.set dst (drop n)).get dst = [] ` (`iterate_tail_clear`/`drop_length`).
Then `clearRegionTM_run` (head `0`, exit `clearRegionTM_exit dst`, output tape
`T 0`) follows; wrap as the `opClear` `CompiledCmd` run.

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
  (`delimTestTM_exit_content`, `stepDeleteRewindTM_exit`) — `show` the reduced/`Nat`
  form first (e.g. `show (navigateToRegTM dst).states + 1 ≠ … + 2`).
- **`refine ⟨_, ?_⟩` for an `∃` goal fails** with *"don't know how to synthesize
  placeholder for argument `w`"* (the `Exists.intro` witness can't be postponed
  here). Use **`exact ⟨_, by …; exact (composeFlatTM_run …).1⟩`** — letting the
  proof determine the witness — and inline the big combinator call into the
  `exact` so the goal type drives elaboration (also fixes spurious `w`-synthesis in
  `h_sym_bound` lambdas).
- **`set x := e` folds `e` in *existing* hypotheses** (e.g. a prior `htape_nav`)
  but **not** in terms produced *later* by lemma applications → `rw [← htape_nav]`
  then can't match. Either don't `set` the shared sub-term, or establish all the
  `have`s that reference it *after* the `set`.
- The composite result state is `c₂.state_idx + M₁.states` (run_pos) /
  `c₃.state_idx + (M₁.states + M₂.states)` (run_neg) — **`+`-order differs** from
  the `exit…` defs (`M₁.states + 17`), so `rw [show exitLoop = 17 + M₁.states from
  by …omega]` before the final `exact`.
- `composeFlatTM_haltingStateReached_M2` is `private`; derive "exit is a halt
  state" from `composedHalt = replicate M₁.states false ++ M₂.halt` (or
  `composedBranchHalt`) + `getElem?_append_right`/`composeFlatTM_halt_some_intro`.
- **MCP `lean-lsp` / `#print axioms` can't find `lake`.** Axiom-check via a scratch
  file: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean` with
  `#print axioms <fully.qualified.name>` (want only `propext`/`Classical.choice`/
  `Quot.sound`; **no `sorryAx`**).

## Key files & exact locations

| File | Contents |
|------|----------|
| `Lang/ClearGadget.lean` | `navigateToRegTM` (**M₁-recursion, fixed**), `delimTestTM`, `navigateAndTestTM`, `deleteRewindRawTM` (**stepLeft inserted, fixed**), `clearBodyRawTM`, `clearRegionTM`; all validity; **run-lemma steps 1–2** (`navigateToRegTM_run_traj`, `navigateAndTestTM_run_content`/`_run_delim`/`_no_early_halt`); halt facts (`innerRewind_halt_eight`, `deleteRewindRawTM_halt_fifteen`, `stepDeleteRewindRawTM_halt_seventeen`, `clearBodyRawTM_exitLoop_is_halt`/`_exitDone_is_halt`); the generic `ne_of_not_halting` |
| `Lang/Compile.lean` | compiler; residue infra (`TapeOK`/`ValidResidue`); append op done; **clear run-lemma steps 3–4** (`stepDeleteRewind_run` @2417, `clearBody_delete_run` @2569, `clearBody_done_run` @2676; helpers `encodeTape_residue_twoPhaseRewind`, `encodeTape_reg_decomp_at`, `BitState_set_tail`, `haltingStateReached_of_halt`); proven `clear` math (`deleteCarry_tail_step`, `set_tail_iterate`, `iterate_tail_clear`, `clear_block_decomp`, `encodeTape_reg_decomp`, `regBlocks_map_shiftReg`, `set_get_self`); `compileOp_sound_physical_residue` @3221 (**`clear` case `sorry` @3252**, 9 cross-register `sorry`s); `Compile_run_physical_residue` @3881 (`sorry` @3699) |
| `Lang/ScanLeft.lean` | `stepLeftTM`/`stepRightTM` (+`stepLeftTM_run_blank`/`_no_early_halt`), `scanLeftUntilTM`, `rewindToStart_run`/`rewindToStart_traj`, `rewindFromEndTM`, `rewindTwoPhaseTM` (+`rewindTwoPhase_run`/`_no_early_halt`), `composeFlatTM_halt_some_intro` |
| `Lang/AppendGadget.lean` | `appendAtTM`, `regBlocks` (+`regBlocks_cons`), `scanPast_block`, `scan_block_before` (in `Navigate.lean`), append op residue contract template (`opAppendBit_physical_residue`) |
| `Lang/ShiftTape.lean` | `deleteCarryTM` (+`_run`/`_no_early_halt`), `insertCarryTM` |
| `Complexity/TMPrimitives.lean` | `composeFlatTM`/`branchComposeFlatTM`/`loopTM` + `_run`/`_no_early_halt`/`_valid`; **`branchComposeFlatTM_no_early_halt_pos`/`_neg`** (new); `loopTM_run` @3788; `composedBranchHalt`; `state_idx_lt_states_of_run` |

**Where to put the step-5a/5b lemmas:** in `Compile.lean` next to the step-3/4
lemmas (the trajectory lemmas right after `stepDeleteRewind_run` /
`clearBody_delete_run` / `clearBody_done_run`; the `clearRegionTM_run` and the
`clear`-case discharge right before `compileOp_sound_physical_residue` @3221).
Step-3/4 are **generic over `s`/`res`** so the loop instantiates them per
iteration; keep that genericity.

## Conventions
- Build `lake build` (or `lake build Complexity.Lang.X`); commit per logical step
  with a **green build**; new results must be `#print axioms`-clean (only
  `propext`/`Quot.sound`/`Classical.choice`; **no `sorryAx`** for a finished lemma).
- Probe `#eval` files via
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/probe.lean`.
- See ROADMAP "Hard-won gotchas" and "How we work" for full methodology.
