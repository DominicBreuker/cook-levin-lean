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
  contract composes (proven), the decider bridge now uses it, and the
  residue-tolerant **append rewind gadget** is proven. The next phase is
  resolving the halt-uniqueness obstacle (below) and turning the rewinding ops
  into `CompiledCmd`s.

## ⚠⚠ THE CURRENT BLOCKER (verified this session — read before building any op)

**Rewinding op machines have TWO halt states, so they cannot be `CompiledCmd`s
as-is.** Every per-op physical contract (`compileOp_sound_physical_residue`)
demands the head exit at `0`. Rewinding to `0` uses a **left scan**
(`scanLeftUntilTM`, `halt = [false, true, true]`), which has *two* halt states:
state 1 = "found target", state 2 = "hit left boundary without finding". Through
`composeFlatTM` (which zeroes the *first* machine's halts but keeps the *last*
machine's), any rewinding composite inherits both. Verified by `#eval`:
`appendAtThenTwoPhaseRewindTM 2 0` halts at states `{15, 16}` (15 = found = the
real exit; 16 = the unreachable boundary state). So `CompiledCmd.halt_unique` is
**statically false** for it — you cannot fill that field.

This is why `compileOp` for the append ops still wraps the **non-rewinding**
`appendAtTM` (a genuine `CompiledCmd`): the previous design never reconciled
"per-op rewind to head 0" with `halt_unique`. The handoff used to call step 2
"straightforward" — **it is not**; it needs the halt-demotion step below.

**Resolution (precedent already exists).** `Compile.joinTwoHalts M h1 h2`
(built for `compileIfBit`'s two-branch-exit problem, lines ~387–470 of
`Compile.lean`) demotes halt state `h2` to a non-halt and bridges it to `h1`,
leaving `h1` the unique halt. It already has `_states/_start/_sig/_tapes/
_h1_is_halt/_halt_unique/_valid`. **The one missing piece is a run-preservation
lemma:** if a run of `M` never visits `h2`, then `joinTwoHalts M h1 h2` produces
the *same* run (the only `trans` change is bridge entries *out of* `h2`, and the
only `halt` change is at `h2`). This lemma does **not exist yet** — even
`compileIfBit_sound` is still sorry'd partly for this reason (line ~2248). It is
the foundational unblock for **all** rewinding ops (append and every deletion
op). Prove it first.

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
| Decider bridge (residue) | `bitDecider_run` now uses `Compile_run_physical_residue` | `Lang/Compile.lean` | ✅ **(new)** |
| Single halt merge | `joinTwoHalts` + `_halt_unique/_valid/_h1_is_halt` | `Lang/Compile.lean` | ✅ (no run lemma) |

## Next steps (ordered — the halt-uniqueness fix gates everything)

### 1. Prove `joinTwoHalts` run-preservation (the unblock)

State and prove: if `runFlatTM k M cfg0` never has `state_idx = h2` for any
`k' ≤ k` (and `cfg0.state_idx ≠ h2`), then `runFlatTM k (joinTwoHalts M h1 h2)
cfg0 = runFlatTM k M cfg0`, and likewise `haltingStateReached` agrees off `h2`.
Proof: induction on `k`; `stepFlatTM` agrees because the prepended bridge
`trans` entries key on state `h2` only, and `halt` differs only at `h2`. Look at
`stepFlatTM`/the trans-lookup in `MachineSemantics.lean` for the exact lookup
mechanism. This is ~50–100 LOC and unblocks both `compileIfBit_sound` and all
rewinding ops.

### 2. Make the rewinding append op a `CompiledCmd`, prove its residue contract

- Define `opAppendOne dst` (and `opAppendZero`) as
  `joinTwoHalts (appendAtThenTwoPhaseRewindTM 2 dst) <found-exit> <boundary-state>`,
  with the found-exit `= 6 + (appendAtTM 2 dst).states` (state 15 for `dst=0`)
  and the boundary state to demote `= 7 + (appendAtTM 2 dst).states` (state 16).
  Confirm the two halt indices via `#eval (…).halt.zipIdx.filter (·.1) |>.map (·.2)`.
  All seven `CompiledCmd` fields then discharge from the `joinTwoHalts_*` lemmas.
- Prove `compileOp_sound_physical_residue` for the append cases: feed
  `appendAt_twoPhaseRewind_run`/`_no_early_halt` (already proven) through the
  step-1 run-preservation lemma. **`res_out = res_in`** (the insert grows
  `encodeTape output` by one cell at the carry's end; the residue passes through
  unchanged — *not* `res_in ++ [carried]` as an older note claimed). The exit
  tape is `encodeTape (s.set dst (s.get dst ++ [bit])) ++ res_in`. The terminator
  position is `p = (encodeTape output).length - 1`; discharge the gadget's
  `h_t0`/`h_term`/`h_interior_ne`/`h_residue_ne` from `encodeTape_get_zero`,
  `encodeTape_interior_ne_endMark`, and `ValidResidue res_in` (mirror the
  structure plumbing in the older `appendBit_physical`, which is the no-residue
  single-phase analogue and a good template).
- ⚠ The old `opAppendOne`/`opAppendZero` use the **non-rewinding** `appendAtTM`;
  the only consumers of the old behavioural lemmas (`compileOp_appendOne_sound`,
  `appendBit_physical`) are docs — safe to repurpose/delete. The exact-tape
  `Compile_run_physical` is now also unused in proof terms (only `*_residue` is).

### 3. First deletion op `opTail` (validates the deletion pattern)

Same shape: navigate to register `dst` → `deleteCarryTM` (left-shifts suffix,
appends a `0` filler, so **`res_out = res_in ++ [0]`** and stays `ValidResidue`)
→ two-phase rewind → `joinTwoHalts` demotion. The deletion primitives
(`deleteCarryTM_run/_no_early_halt`) are proven; the new work is the navigate +
the `encodeTape`-level contract and the same halt-demotion wrapper as step 2.

### 4. Remaining deletion ops, then `compileIfBit`/`compileForBnd` residue, then
assemble `Compile_run_physical_residue` by induction on `Cmd`. `opClear` needs a
`loopTM` (delete until the register delimiter `0`). Keep **linear** per-fragment
budgets (quadratics don't compose — see the finding block above `compileSeq_sound`).

## Key files

| File | Contents |
|------|----------|
| `Lang/Compile.lean` | compiler, physical contracts, residue infra, `joinTwoHalts`, ~2670 lines |
| `Lang/AppendGadget.lean` | `appendAtTM`, `appendAtThenRewindTM` (single-phase), `appendAtThenTwoPhaseRewindTM` (residue), `appendBit_physical` |
| `Lang/ScanLeft.lean` | `scanLeftUntilTM`, `rewindFromEndTM`, `rewindTwoPhaseTM` |
| `Lang/ShiftTape.lean` | `insertCarryTM` + `deleteCarryTM` |
| `Lang/Navigate.lean` / `ScanPast.lean` | register navigation atoms |
| `Complexity/TMPrimitives.lean` | `composeFlatTM_run/_no_early_halt`, `loopTM_run` |
| `Complexity/TapeMono.lean` | tape non-shrink finding |

## Gotchas

- **`halt_unique` for rewinds**: see THE BLOCKER. Any machine ending in a
  left-scan has ≥2 halt states; wrap with `joinTwoHalts` (needs the step-1 run
  lemma). Same was already done for `compileIfBit` (two branch exits).
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
