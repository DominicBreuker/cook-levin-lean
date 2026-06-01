# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first for the
authoritative status and plan. This file says exactly what to do next.

## Where things stand

- `lake build` ✅ green (3358 jobs). First build is slow (mathlib); one module
  rebuilds in ~5–10s after. `lake` is **not on PATH** —
  `export PATH="$HOME/.elan/bin:$PATH"`.
- **Risk C2 (compiler soundness) is the focus.** The `clear` op now has a **real
  TM machine** (`clearRegionTM` in `ClearGadget.lean`), fully wired into
  `compileOp`, with a sorry-free `CompiledCmd` (validity, halt uniqueness,
  correct sig/tapes — all proven). The `clear` case in
  `compileOp_sound_physical_residue` still has a `sorry` for its **run lemma**
  (the `loopTM_run` plumbing). The remaining work is 9 stub cross-register ops
  and the run-lemma assembly.

## Architecture of clearRegionTM (built this session, ClearGadget.lean)

`clearRegionTM dst = loopTM (clearBodyRawTM dst) exitDone exitLoop`

The loop body `clearBodyRawTM dst` is a `branchComposeFlatTM`:
- **M₁** = `navigateAndTestTM dst` (stepRight ⨾ scanPastDelim^dst ⨾ delimTest)
  Two exits: `exit_content` (cell ≠ 0) and `exit_delim` (cell = 0).
- **M₂** = `stepDeleteRewindRawTM` (stepRight ⨾ deleteCarryTM ⨾ rewindTwoPhaseTM)
  Content branch: delete first cell, rewind to 0 → exitLoop.
- **M₃** = `justRewindTM` (scanLeftUntilTM 4 3)
  Delimiter branch: register empty, rewind to 0 → exitDone.

New primitives (all sorry-free, axiom-clean):
- `stepRightTM` in `ScanLeft.lean` — mirror of `stepLeftTM`, with run/valid/traj
- `delimTestTM` in `ClearGadget.lean` — reads one cell, halts at state 1 (content)
  or state 2 (delimiter); step/run/no-early-halt all proven
- `navigateToRegTM dst` — stepRight ⨾ scanPastDelim^dst; recursive like appendAtTM
- Full validity chain: every submachine → clearRegionTM proven valid

## NEXT TASK: prove the `clear` run lemma

The `clear` case in `compileOp_sound_physical_residue` (line ~2744 of Compile.lean)
is `sorry`. To discharge it, build the run lemma for `clearRegionTM`:

### Step 1: navigateToRegTM run lemma

Prove `navigateToRegTM_run`: from head 0 on tape
`encodeTape s ++ res_in`, after some steps, head lands at register `dst`'s first
content cell (or delimiter). Follow the `appendAt_run` pattern (recursive on `dst`;
uses `composeFlatTM_run` + `scanPastDelim_run`).

### Step 2: navigateAndTestTM run lemma (two cases)

Compose navigation with `delimTestTM`:
- **Empty register** (`s.get dst = []`): cell at dst is delimiter `0` →
  `delimTestTM` → exit at `navigateAndTestTM_exit_delim`.
- **Non-empty register** (`s.get dst ≠ []`): cell is shifted content `c0+1 ≠ 0` →
  `delimTestTM` → exit at `navigateAndTestTM_exit_content`.

Use `composeFlatTM_run` to thread navigation into delimTest.

### Step 3: delete-branch run lemma (stepDeleteRewindRawTM)

After `navigateAndTestTM` exits content, head is at the first content cell `p`:
1. `stepRightTM` → head at `p+1`
2. `deleteCarryTM` → deletes cell at `p`, tape becomes
   `encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0])`,
   head at some position past the trailing endMark (in residue zone)
3. `rewindTwoPhaseTM` → scan left to trailing endMark, step left, scan left to
   leading sentinel → head at 0

The math is already proven:
- `deleteCarry_tail_step` gives the deleteCarryTM run
- `set_tail_iterate` / `iterate_tail_clear` give the loop invariant

### Step 4: done-branch run lemma (justRewindTM)

After `navigateAndTestTM` exits delimiter, head is at register dst's delimiter
(an interior position). `scanLeftUntilTM 4 3` scans left to the leading sentinel
(3) at position 0. Use `rewindToStart_run` with the appropriate tape decomposition.

### Step 5: assemble via loopTM_run

Feed `loopTM_run` with:
- `T n` = tape after `n` deletions (from `set_tail_iterate`)
- `tDone` = step count for the done branch (last iteration, register empty)
- `tIter j` = step count for iteration `j` (delete one cell + rewind)
- Iteration count = `|s.get dst|` (from `iterate_tail_clear`)

### Step 6: connect to compileOp_sound_physical_residue

The run lemma gives the exact tape `encodeTape (Op.eval (clear dst) s) ++
(res_in ++ replicate |s.get dst| 0)`. The residue `res_out` is `ValidResidue`
by `ValidResidue_append_replicate_zero`. The budget `9·L²+9` needs to be verified
(each iteration is O(tapeLen), with |s.get dst| iterations → O(tapeLen²)).

## After `clear`: the cross-register ops, then assemble

1. **`copyBlockTM`** (the largest remaining gadget — has no existing primitive).
   Probe go/no-go first (`#eval`: does it reproduce `src` at `dst` and resize; does
   its exit head land in residue past the terminator for the two-phase rewind;
   is it linear-per-symbol). Then `_run`/`_no_early_halt`, wrap with `rewindBracket`,
   prove each cross-register op's residue contract by **copying the
   `opAppendBit_physical_residue` template**.
2. **`compileIfBit`/`compileForBnd`** residue contracts (`joinTwoHalts_run_eq` is the
   run lemma `compileIfBit` needs; `loopTM_run` for `forBnd`).
3. **Assemble `Compile_run_physical_residue`** by induction on `Cmd` from
   `compileOp_sound_physical_residue` (Op) + `compileSeq_sound_physical_residue` (seq,
   proven) + the ifBit/forBnd combinators. This discharges the one obligation the
   whole S3 bridge sits on.

## Key files

| File | Contents |
|------|----------|
| `Lang/ClearGadget.lean` | **NEW**: `navigateToRegTM`, `delimTestTM`, `clearBodyRawTM`, `clearRegionTM`; all validity + primitives sorry-free |
| `Lang/Compile.lean` | compiler; residue infra (`TapeOK`/`ValidResidue`); `joinTwoHalts`; `rewindBracket`(+`_transport`); append op done; **all proven `clear` lemmas**; `compileOp_sound_physical_residue` (append done, `clear` has real machine but sorry'd run, 9 cross-register `sorry`s); `Compile_run_physical_residue` (`sorry`) |
| `Lang/ScanLeft.lean` | `stepLeftTM`, `stepRightTM` **(NEW)**, `scanLeftUntilTM`, `rewindToStart_run`, `rewindFromEndTM`, `rewindTwoPhaseTM` |
| `Lang/AppendGadget.lean` | `appendAtTM` (+ recursive navigation pattern), `appendAt_twoPhaseRewind_run/_no_early_halt` |
| `Lang/ShiftTape.lean` | `insertCarryTM` (fixed symbol), `deleteCarryTM` (+ `_loop_run`/`_no_early_halt`) |
| `Lang/ScanPast.lean` / `Navigate.lean` | `scanPastDelimTM`(+`scanPast_block`), `scan_to_delim`/`scan_to_end` |
| `Lang/Semantics.lean` | `Op.eval` (the cross-register truth), `Op.cost`, `State.size_set_add` |
| `Complexity/TMPrimitives.lean` | `composeFlatTM`/`branchComposeFlatTM`/`loopTM` (+ `_run`/`_valid`) |
| `Complexity/TapeMono.lean` | tape non-shrink finding |

## Gotchas

- **Never build a read-src/write-dst op as an in-place edit** — it must transport
  data via `copyBlockTM`.
- **`deleteCarryTM` deletes the cell *before* the head** (head at `p+1` deletes `p`),
  and **leaves the head one past the tape end** (on a blank) — step left off it before
  any rewind (like `rewindFromEndTM`). The loop body's per-pass head reset is cleanest
  as **rewind-to-0 + re-navigate** (mid-tape markers aren't unique) — this is what
  makes `clear` quadratic.
- **`halt_unique` for rewinds**: a machine ending in a left-scan has 2 halt states —
  demote the boundary (`joinTwoHalts`/`rewindBracket`); don't hand-build the `CompiledCmd`.
- **Tape can't shrink**: never state an op's exit tape as a shorter `encodeTape`; use
  `TapeOK`/`ValidResidue` (deletion residue is `res_in ++ replicate n 0`).
- **`.get`/`.set` on a `State` literal mis-resolves to `List.get`** — write
  `State.get`/`State.set` explicitly, or rewrite to `List.set` via `set_eq_list_set`.
- **`omega` can't see through `Var := Nat`** — restate at `Nat`.
- **`branchComposeFlatTM_run_pos`/`_neg` require the *exact* exit state numbers** for
  the composed machine's M₂/M₃ halts; trace them through `composeFlatTM_halt_some_intro`
  as the existing `rewindBracket_transport` does.
- **`exact` defeq across `opXxx`/`rewindBracket` + `initFlatConfig`** — normalise the
  start config with an explicit `hinit` (via `M.start = 0`) before `exact`.

## Conventions

- Build `lake build` (or `lake build Complexity.Lang.X`); commit per logical step with
  a **green build**; new results must be `#print axioms`-clean (only `propext`/
  `Quot.sound`/`Classical.choice`; **no `sorryAx`** for a finished lemma).
- See ROADMAP "Hard-won gotchas" and "How we work" for full methodology.
