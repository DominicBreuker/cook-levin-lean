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
  contract composes (proven), the decider bridge uses it, the halt-uniqueness
  obstacle is resolved (`rewindBracket`), **and step 1 — the append per-op residue
  contract + `compileOp` wiring — is now DONE** (see below). The next phase is the
  remaining per-op contracts (`opTail` first) + the `Compile_run_physical_residue`
  assembly. The append op is the **template**; every other rewinding op copies it.

## Background: the halt-uniqueness obstacle (RESOLVED earlier — context for `rewindBracket`)

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
| **General rewinding-op builder** | `rewindBracket` (CompiledCmd) + `rewindBracket_M/_exit/_transport` | `Lang/Compile.lean` | ✅ |
| **Append op as CompiledCmd** | `opAppendBitRewind := rewindBracket (appendAtTM …)`, now `compileOp`'s `appendOne`/`appendZero` | `Lang/Compile.lean` | ✅ |
| **Append per-op residue contract** | `opAppendBit_physical_residue` (template for all rewinding ops); `encodeTape_get_last` | `Lang/Compile.lean` | ✅ **(new)** |
| **`compileOp` residue contract (append cases)** | `compileOp_sound_physical_residue` (append PROVEN; 10 stub ops `sorry`) | `Lang/Compile.lean` | 🟡 **(new — append done)** |
| Two-phase rewind (`p ≤ HD`) | `appendAt_twoPhaseRewind_run/_no_early_halt` loosened to cover no-residue | `Lang/AppendGadget.lean` | ✅ |

## ✅ DONE this session: step 1 — append residue contract PROVEN + `compileOp` wired

`Compile.opAppendBit_physical_residue` (Compile.lean) is the **template for every
rewinding op**: it instantiates `rewindBracket_transport` (compute `= appendAtTM
ins dst`) with the proven `appendAt_twoPhaseRewind_run`/`_no_early_halt`, plus the
`encodeTape`-decomposition that discharges the gadget's tape side-conditions. The
exit tape is `encodeTape output ++ res_in` (**`res_out = res_in`**), head at `0`.
`compileOp` now dispatches `appendOne`/`appendZero` to `opAppendBitRewind 2/1`, and
the **append cases of `compileOp_sound_physical_residue` are PROVEN** (the 10 stub
ops are still `sorry`). New helper: `Compile.encodeTape_get_last` (trailing
terminator `3`).

Two findings, both folded in:
- **Per-op budget is `3·inputTapeLen + 8`, not `+6`.** The two-phase rewind costs
  two more `Lmove`s than the single-phase. Still linear → composes into the
  quadratic total with constant slack. `compileOp_sound_physical_residue` now states `+8`.
- **`appendAt_twoPhaseRewind_run`/`_no_early_halt` were over-strict** (`p < HD`);
  loosened to **`p ≤ HD`** so the no-residue case (`res_in = []`, head *on* the
  terminator) is covered — `compileOp` must run the two-phase rewind even with no
  residue (the first fragment has none).

The **mechanism is now validated end-to-end**: `rewindBracket` → `rewindBracket_transport`
→ per-op residue contract → `compileOp` → `compileSeq_sound_physical_residue`. Every
remaining rewinding op is a copy of this template with a different `compute` machine.

## Next steps (ordered)

### 1. First deletion op `opTail` (de-risked — copy the append template)

`compute := navigate-to-`dst` ⨾ deleteCarryTM`; then `opTail := rewindBracket
compute (exit) …` (mirror `opAppendBitRewind`). Then prove `opTail`'s residue
contract by **copying `opAppendBit_physical_residue`**:
- Supply a **gadget run lemma** for `compute ⨾ rewindTwoPhase` (analogous to
  `appendAt_twoPhaseRewind_run`) — this is the new gadget work: compose
  `deleteCarryTM_run/_no_early_halt` (proven, `ShiftTape.lean`) with navigation
  (`Navigate.lean`/`ScanPast.lean`) via `composeFlatTM_run`, then bracket with
  `rewindTwoPhaseTM`. ⚠ **Check the delete gadget's exit head lands in the
  residue past the real terminator** (the two-phase rewind's precondition; verify
  with `#eval` first, as the append session did).
- The `encodeTape` decomposition: `deleteCarryTM` left-shifts the suffix and pads
  one `0`, so the output is one cell **shorter** → **`res_out = res_in ++ [0]`**
  (stays `ValidResidue` via `ValidResidue_append`/`ValidResidue_replicate_zero`).
  Terminator position `p = (encodeTape output).length − 1` as before.
- Discharge the `tail` branch of `compileOp_sound_physical_residue`. ⚠ The shared
  per-op budget is `3·L+8`; navigation adds `O(dst) ≤ O(L)` steps, so bump the
  constant if needed (still linear — keep it linear, never quadratic per fragment).

### 2. Remaining ops, then assemble.

`opClear` = `loopTM` of delete-until-delimiter (`loopTM` body is a `CompiledCmd`,
so `rewindBracket`'s unique halt is exactly what `loopTM_run` needs). `opCopy`,
`opHead`, `opEqBit`, `opNonEmpty`, the four length ops likewise. Then the residue
`compileIfBit`/`compileForBnd` (`compileIfBit_sound` is unblocked —
`joinTwoHalts_run_eq` is the run lemma it needed), then assemble
`Compile_run_physical_residue` by induction on `Cmd` from
`compileOp_sound_physical_residue` (Op) + `compileSeq_sound_physical_residue` (seq,
proven) + the ifBit/forBnd residue combinators. Keep **linear** per-fragment
budgets (quadratics don't compose — finding block above `compileSeq_sound`).

## Key files

| File | Contents |
|------|----------|
| `Lang/Compile.lean` | compiler, physical contracts, residue infra, `joinTwoHalts`+run lemma, `rewindBracket` (general rewinding-op builder), `opAppendBitRewind`, **`opAppendBit_physical_residue` (the per-op template), `compileOp_sound_physical_residue`** |
| `Lang/AppendGadget.lean` | `appendAtTM`, `appendAtThenRewindTM` (single-phase), `appendAtThenTwoPhaseRewindTM` (residue), `appendBit_physical` (single-phase, now gadget-only) |
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
- **`get`-congruence across list equality**: route through `getElem?`. When copying
  `opAppendBit_physical_residue`, reuse its `hleft`/`hright` split helpers (transfer
  `L.get` to `(encodeTape output).get` / `res_in.get` via `getElem?_append_left/right`
  + `Option.some.inj`) — `rw [List.getElem_append_left …]` fails directly because
  `List.get_eq_getElem` leaves a `Fin.val` coercion that won't key-match.
- **Don't `set` a length you also feed to `getElem_append_*`.** `set EO :=
  (encodeTape output).length` folds `(encodeTape output).length` everywhere, breaking
  `getElem_append_left`'s `i < l₁.length` unification. Keep the length explicit; only
  `set` the terminator position `p := (encodeTape output).length - 1`.
- **`exact` defeq across `opXxx`/`rewindBracket` + `initFlatConfig`.** `compileOp o`,
  `opAppendBitRewind …`, and `rewindBracket …` are defeq but `exact` may not unfold far
  enough. Normalise the start config with an explicit `hinit : initFlatConfig … = {…}`
  (via `M.start = 0`) and `rw [hinit]` before `exact htrans.1`.
- **`#print axioms`** needs the full name `Complexity.Lang.Compile.<x>` and the
  import `Complexity.Lang.Compile` (not `CookLevin.…`). Use a scratch file:
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean`.

## Conventions

- Build: `lake build` (or `lake build Complexity.Lang.X` for one module).
- Commit per logical step with a **green build**.
- New results must be `#print axioms`-clean (only `propext`/`Quot.sound`/
  `Classical.choice`; **no `sorryAx`** for a finished lemma).
- See ROADMAP "Hard-won gotchas" and "How we work" for full methodology.
