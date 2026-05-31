# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first; they
are the authoritative status and plan. This file tells the next agent exactly
what to do next and what to watch out for.

## Where things stand

- `lake build` ✅ green (3357 jobs). First build is slow (mathlib); after that,
  one module rebuilds in ~5–10s. `lake` is **not on PATH** — prefix with
  `export PATH="$HOME/.elan/bin:$PATH"`.
- `#print axioms CookLevin` = `[propext, sorryAx, Classical.choice, Quot.sound]`
  — conditional on `sorryAx`; also vacuous due to S1/S2/S3 (see ROADMAP).
- **Risk C2 (compiler soundness) is the current focus.** The residue-tolerant
  contract composes (proven), the decider bridge uses it, the residue-tolerant
  two-phase append rewind gadget is proven, **and the halt-uniqueness obstacle
  (below) is now RESOLVED** with a general, reusable builder. The next phase is
  the (mechanical) per-op `encodeTape` contracts + wiring `compileOp`.

## ✅ RESOLVED this session: the halt-uniqueness obstacle (read before building any op)

**The problem (was blocking).** Every per-op physical contract demands the head
exit at `0`. Rewinding to `0` uses a **left scan** (`scanLeftUntilTM`,
`halt = [false, true, true]`), which has *two* halt states (1 = found, 2 =
boundary). Through `composeFlatTM` any rewinding composite inherits both, so
`CompiledCmd.halt_unique` is statically false (`#eval`: the append bracket halts
at `{compute.states+6, compute.states+7}`). That is why `compileOp` for append
*used* to wrap the non-rewinding `appendAtTM`.

**The fix (built + proven, axiom-clean).** `Compile.rewindBracket compute exit …
: CompiledCmd` wraps **any** `compute` machine with the two-phase rewind and
demotes the boundary halt `compute.states+7` via `Compile.joinTwoHalts`, leaving
the found-state `compute.states+6` as the unique exit. The full chain is proven:
- `joinTwoHalts_run_eq` (`Compile.lean`): if a run of `M` never visits the
  demoted `h2`, `joinTwoHalts M h1 h2` produces the **identical** run. (`h2` is a
  halt state, so a no-early-halt trajectory forbids it.) Foundational; **also
  unblocks `compileIfBit_sound`.**
- `rewindBracket` discharges all seven `CompiledCmd` fields; `rewindBracket_M`/
  `_exit` are `rfl`.
- `rewindBracket_transport`: feeds a gadget's proven run + no-early-halt
  trajectory through `joinTwoHalts_run_eq` to give the `CompiledCmd`'s run +
  no-early-exit/no-early-halt trajectory.

**Every rewinding op reuses these verbatim** — only the `compute` machine differs
(append: `appendAtTM ins dst`; deletion: `navigate ⨾ deleteCarry`). The append
instance is live: `Compile.opAppendBitRewind ins h_ins dst :=
rewindBracket (appendAtTM ins dst) (appendAtTM_exit dst) …`.

## Architecture: the residue-tolerant contract

**The physical TM tape never shrinks** (machine-checked in `TapeMono.lean`), so
the exit tape is `encodeTape output ++ residue` with `ValidResidue residue`
(every cell `< 4 ∧ ≠ endMark`, i.e. `∈ {0,1,2}`), hidden existentially in
`TapeOK`. Decode ignores residue (`decodeTape_encodeTape_append`, proven);
composition threads residue mechanically (`compileSeq_sound_physical_residue`,
proven).

**Residue lives *after* the trailing terminator.** In `compileSeq`, fragment N+1
runs on `encodeTape mid ++ res`, i.e. `endMark :: encodeRegs mid ++ [endMark] ++
res`. So a rewinding gadget's head exits *inside the residue*, past the real
terminator — a single-phase `rewindFromEndTM` would stop the left-scan on the
real (interior) terminator, not the leading sentinel. Use the **two-phase
rewind** `rewindTwoPhaseTM` (scan-left through residue to the real terminator,
step off, scan-left to the sentinel). It works whether or not residue is present
(`head = p` is the no-residue case).

## What's proved (all axiom-clean)

| Layer | Lemma(s) | File | Status |
|-------|----------|------|--------|
| Tape non-shrink | `runFlatTM_single_length_le` | `Complexity/TapeMono.lean` | ✅ |
| Residue decode | `decodeTape_encodeTape_append` | `Lang/Compile.lean` | ✅ |
| Residue helpers | `ValidResidue_*`, `TapeOK_*` | `Lang/Compile.lean` | ✅ |
| Seq composition (residue) | `compileSeq_sound_physical_residue`, `compileSeq_traj_physical_residue` | `Lang/Compile.lean` | ✅ |
| Two-phase rewind | `rewindTwoPhase_run/_no_early_halt`, `rewindTwoPhaseTM_start/_sig/_tapes` | `Lang/ScanLeft.lean` | ✅ |
| **Two-phase append gadget** | `appendAt_twoPhaseRewind_run/_no_early_halt` (machine `appendAtThenTwoPhaseRewindTM`) | `Lang/AppendGadget.lean` | ✅ **(new)** |
| Insert/delete primitives | `insertCarryTM_*`, `deleteCarryTM_*` | `Lang/ShiftTape.lean` | ✅ |
| Decider bridge (residue) | `bitDecider_run` uses `Compile_run_physical_residue` | `Lang/Compile.lean` | ✅ **(new)** |
| **Halt-merge run lemma** | `joinTwoHalts_step_eq/_halting_eq/_run_eq` | `Lang/Compile.lean` | ✅ **(new)** |
| **Rewind halt characterization** | `composeFlatTM_halt_some_imp/_intro`, `(scanLeftUntilTM/rewindFromEndTM/rewindTwoPhaseTM)_halt_only`, `rewindTwoPhaseTM_halt_six/_seven` | `Lang/ScanLeft.lean` | ✅ **(new)** |
| **General rewinding-op builder** | `rewindBracket` (CompiledCmd) + `rewindBracket_M/_exit/_transport` | `Lang/Compile.lean` | ✅ **(new)** |
| **Append op as CompiledCmd** | `opAppendBitRewind := rewindBracket (appendAtTM …)` | `Lang/Compile.lean` | ✅ **(new)** |

## Next steps (ordered — the halt-uniqueness fix is DONE; what remains is mechanical)

### 1. Per-op `encodeTape` residue contract for append, then wire `compileOp`

- Prove `compileOp_sound_physical_residue` (or a helper `opAppendBit_physical_residue`)
  for the append cases: instantiate **`rewindBracket_transport`** with
  `compute := appendAtTM ins dst`, `exit := appendAtTM_exit dst`, feeding the
  **already-proven** `appendAt_twoPhaseRewind_run`/`_no_early_halt` as `hrun`/`htraj`
  (`appendAtThenTwoPhaseRewindTM` is defeq to `compute ⨾ rewindTwoPhase`; note the
  exit state `6 + appendAtTM.states` vs `appendAtTM.states + 6` — `Nat.add_comm`).
  The remaining work is the **`encodeTape` decomposition** to discharge those
  gadget hypotheses: input tape `encodeTape s ++ res_in`, `post := encodeRegs
  (s.drop (dst+1)) ++ [endMark] ++ res_in`, terminator position
  `p = (encodeTape output).length − 1`, conditions from `encodeTape_get_zero` /
  `encodeTape_interior_ne_endMark` / `ValidResidue res_in`. **This is mechanical**
  — `appendBit_physical` (the no-residue single-phase analogue) is the template;
  copy it, append `res_in` to `post`, and use the two-phase run. **`res_out = res_in`**
  (the insert grows `encodeTape output` by one cell; residue passes through).
- Wire `compileOp`: dispatch `appendOne`/`appendZero` to `opAppendBitRewind 2/1`.
  ⚠ **Code ordering:** `opAppendOne`/`compileOp` sit *before* `joinTwoHalts`/
  `rewindBracket` in `Compile.lean`. Move the op-definition block (lines ~197–260)
  to *after* `rewindBracket`, or hoist `joinTwoHalts`+`rewindBracket` above it.
  The old non-rewinding `opAppendOne`/`compileOp_appendOne_sound`/`appendBit_physical`
  and the exact-tape `Compile_run_physical` are unused in proof terms — safe to
  delete/repurpose.

### 2. First deletion op `opTail` (now de-risked — reuses `rewindBracket`)

`compute := navigate-to-`dst` ⨾ deleteCarryTM`; then `opTail := rewindBracket
compute …`. `rewindBracket`/`rewindBracket_transport` give the `CompiledCmd` and
its run transport for free — supply only `compute`'s validity + a gadget run
lemma for `compute ⨾ rewindTwoPhase` (analogous to `appendAt_twoPhaseRewind_run`)
and the `encodeTape` decomposition. `deleteCarryTM` left-shifts the suffix and
appends a `0` filler, so **`res_out = res_in ++ [0]`** (stays `ValidResidue`).
The deletion primitives (`deleteCarryTM_run/_no_early_halt`) are proven; the new
work is the navigate + the `encodeTape`-level contract (the halt-demotion wrapper
is now free via `rewindBracket`).

### 3. Remaining deletion ops, then `compileIfBit`/`compileForBnd` residue, then
assemble `Compile_run_physical_residue` by induction on `Cmd`. `opClear` needs a
`loopTM` (delete until the register delimiter `0`; a `loopTM` body is a
`CompiledCmd`, so `rewindBracket`'s unique halt is exactly what `loopTM` needs).
Keep **linear** per-fragment budgets (quadratics don't compose — see the finding
block above `compileSeq_sound`). `compileIfBit_sound` is also unblocked now —
`joinTwoHalts_run_eq` is the run lemma it was missing.

## Key files

| File | Contents |
|------|----------|
| `Lang/Compile.lean` | compiler, physical contracts, residue infra, `joinTwoHalts`+run lemma, `rewindBracket` (general rewinding-op builder), `opAppendBitRewind` |
| `Lang/AppendGadget.lean` | `appendAtTM`, `appendAtThenRewindTM` (single-phase), `appendAtThenTwoPhaseRewindTM` (residue), `appendBit_physical` |
| `Lang/ScanLeft.lean` | `scanLeftUntilTM`, `rewindFromEndTM`, `rewindTwoPhaseTM` |
| `Lang/ShiftTape.lean` | `insertCarryTM` + `deleteCarryTM` |
| `Lang/Navigate.lean` / `ScanPast.lean` | register navigation atoms |
| `Complexity/TMPrimitives.lean` | `composeFlatTM_run/_no_early_halt`, `loopTM_run` |
| `Complexity/TapeMono.lean` | tape non-shrink finding |

## Gotchas

- **`halt_unique` for rewinds (RESOLVED)**: any machine ending in a left-scan
  has 2 halt states. Don't hand-build the `CompiledCmd` — use `rewindBracket`,
  which demotes the boundary halt via `joinTwoHalts` and gives the contract via
  `rewindBracket_transport`. Only supply the `compute` machine + its
  `compute ⨾ rewindTwoPhase` gadget run lemma.
- **Tape can't shrink**: never state an op's exit tape as a shorter `encodeTape`.
  Use `TapeOK`/`ValidResidue`.
- **Residue follows the terminator** → always two-phase rewind. Never start
  `scanLeftUntilTM` on a `3` (it halts immediately).
- **`set` then `appendAt_run_exit`**: introduce `set TP`/`set HD` *before* the
  `appendAt_run_exit`/`appendAt_no_early_halt` haves so `composeFlatTM_run`
  unifies the let-defs against the explicit expressions (see
  `appendAt_twoPhaseRewind_run` for the working pattern).
- **`omega` vs `Var`**: `Var := Nat` is opaque to `omega`; restate at `Nat`.
- **`get`-congruence across list equality**: route through `getElem?`.
- **`#print axioms`** needs the full name `Complexity.Lang.Compile.<x>` and the
  import `Complexity.Lang.Compile` (not `CookLevin.…`). Use a scratch file:
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean`.

## Conventions

- Build: `lake build` (or `lake build Complexity.Lang.X` for one module).
- Commit per logical step with a **green build**.
- New results must be `#print axioms`-clean (only `propext`/`Quot.sound`/
  `Classical.choice`; **no `sorryAx`** for a finished lemma).
- See ROADMAP "Hard-won gotchas" and "How we work" for full methodology.
