# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first for the
authoritative status and plan. This file says exactly what to do next.

## Where things stand

- `lake build` ✅ green (3357 jobs). First build is slow (mathlib); one module
  rebuilds in ~5–10s after. `lake` is **not on PATH** —
  `export PATH="$HOME/.elan/bin:$PATH"`.
- **Risk C2 (compiler soundness) is the focus.** The architecture is settled and
  the append op is done end-to-end; the remaining work is the **10 stub `compileOp`s**
  and the `Compile_run_physical_residue` assembly. The very next concrete task is
  finishing the **`clear` op** (all its math is proven — only the TM machine
  remains; see below).

## Two findings that shape all remaining op work (now established facts)

1. **The ops are cross-register.** `tail`/`copy`/`head`/`eqBit`/`nonEmpty`/`takeAt`/
   `dropAt`/`concat`/`consLen` are `s.set dst (f (s.get src))` — read `src`, write
   `dst`, with `dst ≠ src` in the real witnesses (`PolyTime.lean`: `Op.head 1 0`,
   `Op.tail 2 0`, …). They are **not** in-place edits. The gadget library has no
   data-transport gadget, so they need a new **`copyBlockTM`** (block move src→dst);
   then each decomposes as `clear dst ⨾ copyBlock src→dst ⨾ (in-place transform)`.
   Only `clear dst` (no source) and `tail dst dst` are genuinely in-place.
2. **Per-op budget is QUADRATIC.** `compileOp_sound_physical_residue`'s budget is
   `9·tapeLen² + 9` (was `3·tapeLen+8`, which is unsatisfiable: a single-tape machine
   deleting/moving `Θ(tapeLen)` cells needs `Θ(tapeLen)` shift passes ⇒ `Θ(tapeLen²)`).
   This composes — `compileSeq_sound_physical` is additive (`t₁+1+t₂`), so per-op
   quadratics sum to a polynomial total (`inOPoly` suffices). Only the append ops
   are linear; they relax to the quadratic via `linear_le_quadratic_tapeLen`. **Target
   `9·tapeLen²+9` for `clear`/`copy` gadgets** (the `clear` loop costs ≈ `6·tapeLen²`).

## NEXT TASK: build the `clear` machine (`clearRegionTM`)

All the **mathematics is proven** (inventory below); only the autonomous TM and its
`loopTM_run` plumbing remain. `clear dst` deletes register `dst`'s content by a loop
of single-cell deletions, leaving the freed cells as `0` residue past the terminator.
Design: `clearRegionTM := loopTM B exitDone exitLoop` where the body
`B = navigate-from-0-to-register-dst ⨾ branch(cell = delimiter? done : delete) ⨾
rewind-to-0`, iteration count `= |s.get dst|`, final state via `iterate_tail_clear`.
Validated end-to-end by `#eval` (the mechanism produces exactly
`encodeTape(cleared) ++ residue` and the rewind returns head to 0).

### Pre-build checklist (audited — no hidden surprises)

**Build these small machines first (currently MISSING):**
- **`stepRightTM`** — one-cell right move (only `stepLeftTM` exists, `ScanLeft.lean`).
  The navigation base case needs it: head `0` is the leading sentinel `3` (not a
  delimiter, so `scanPastDelimTM` doesn't apply); navigation =
  `stepRightTM ⨾ scanPastDelimTM^dst`. Mirror `stepLeftTM`.
- **A "current cell = delimiter `0`?" branch machine** (the `M₁` for
  `branchComposeFlatTM`). `bitTestTM` is **not** reusable (hard-wired position,
  tests `2`-vs-`1`). Have it **also step the head right by one** while testing —
  this fixes the alignment that `deleteCarryTM` deletes the cell *before* the head
  (head at `content-start+1` deletes `content-start`), avoiding a separate step.

**Design choices (decide up front — they change which proven lemmas apply):**
- **First-cell vs last-cell deletion.** The proven lemmas (`deleteCarry_tail_step`,
  `set_tail_iterate`) delete the **first** content cell (`tail`; head at
  `content-start+1`, needs `stepRightTM`). Alternative: navigate to register `dst`'s
  **delimiter** (reuse `appendAtTM`'s scan-to-`0`, *no* `stepRightTM`) and delete the
  cell before it (the **last** cell, `dropLast`) — needs `dropLast` variants of those
  two lemmas (modest re-proof). Pick one.
- **Internal rewind halts.** Rewinds have **two** halt states (found + boundary).
  Inside `B`, demote the boundary (`joinTwoHalts`, as `rewindBracket` does) or prove
  it unreachable, so `B` presents clean `exitDone`/`exitLoop` and the `loopTM_run`
  no-early-halt trajectory holds.
- **Probably NO outer `rewindBracket`** (unlike append): both branches end head-`0`
  and `loopTM` has a single halt (`B.states`), so `loopTM B` may be a `CompiledCmd`
  directly. Confirm when building.

**Confirmed present (reuse as-is):**
- `loopTM`/`loopTM_run`, `composeFlatTM_run`/`_no_early_halt`,
  `branchComposeFlatTM_run_pos`/`_neg`, all combinator `*_valid` lemmas.
- Navigation: `scanPastDelimTM` + `scanPast_block` + `scanPastDelim_no_early_halt`.
- **Done-branch rewind** (empty register, head interior/left of terminator):
  `ScanLeft.rewindToStart_run`/`_traj` (single-phase scan left to the sentinel).
- **Delete-branch rewind** (head in residue past terminator):
  `rewindTwoPhase_run`/`_no_early_halt`.

### Proven `clear` inventory (all axiom-clean, `Compile.lean`)

Every obligation the machine faces is pre-discharged by one of these:
- `encodeTape_reg_decomp` — **master register-slot decomposition**:
  `encodeTape (s.set dst v) = pre ++ shiftReg v ++ 0::rest`, `pre`/`rest` independent
  of `v` (the workhorse every register-writing op uses).
- `clear_block_decomp` — clearing `dst` deletes exactly the `shiftReg (s.get dst)`
  block; the gadget's input/output target, residue `res_out = res_in ++ replicate |old| 0`.
- `deleteCarry_drop_head` — one `deleteCarryTM` pass: `pre ++ (c0+1)::M → pre ++ M ++ [0]`.
- `deleteCarry_tail_step` — **one deletion = the in-place `tail` step** on the encoded
  tape (also the core of the `tail dst dst` op).
- `set_tail_iterate`, `iterate_tail_clear` — loop **state invariant**: iterating the
  tail-body `n` times drops `n` symbols; at `n = |content|` it equals `clear`.
  (+ `State` algebra `set_eq_list_set`/`get_set_eq`/`set_get_self`/`set_set`.)
- Budget/residue infra: `linear_le_quadratic_tapeLen`, `encodeTape_set_length`
  (`|encodeTape (s.set dst v)| + |old| = |encodeTape s| + |v|`),
  `ValidResidue_append_replicate_zero`.

Then discharge the `clear` branch of `compileOp_sound_physical_residue` (the 10
`sorry`s); `compileOp` already dispatches `clear → opClear` (currently a stub).

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

## Architecture recap (the residue-tolerant contract)

The physical TM tape **never shrinks** (`TapeMono.lean`), so an exit tape is
`encodeTape output ++ residue` with `ValidResidue residue` (cells ∈ {0,1,2}), hidden
existentially in `TapeOK`. Decode ignores residue (`decodeTape_encodeTape_append`);
`compileSeq_sound_physical_residue` threads it. Residue lives **after** the trailing
terminator, so a rewinding gadget exits inside it → use the **two-phase rewind**
`rewindTwoPhaseTM` (never start `scanLeftUntilTM` on a `3`).

**`rewindBracket compute exit … : CompiledCmd`** wraps any `compute` machine with the
two-phase rewind, demotes its boundary halt (`joinTwoHalts`), and gives a unique-exit
`CompiledCmd`; `rewindBracket_transport` turns the gadget's proven run + trajectory
into the `CompiledCmd`'s. The append op (`opAppendBit_physical_residue`) is the worked
template: `rewindBracket_transport` (compute = `appendAtTM`) + the `encodeTape ++
residue` decomposition discharging the tape side-conditions. Copy it for each new op.

## Key files

| File | Contents |
|------|----------|
| `Lang/Compile.lean` | compiler; residue infra (`TapeOK`/`ValidResidue`); `joinTwoHalts`; `rewindBracket`(+`_transport`); append op done; **all proven `clear` lemmas**; `compileOp_sound_physical_residue` (append done, 10 `sorry`s); `Compile_run_physical_residue` (`sorry`) |
| `Lang/AppendGadget.lean` | `appendAtTM` (+ recursive navigation pattern), `appendAt_twoPhaseRewind_run/_no_early_halt` |
| `Lang/ScanLeft.lean` | `stepLeftTM`, `scanLeftUntilTM`, `rewindToStart_run`, `rewindFromEndTM`, `rewindTwoPhaseTM` |
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
- **`get`-congruence across list equality**: route through `getElem?` (reuse the
  `hleft`/`hright` split in `opAppendBit_physical_residue`); `rw [List.getElem_append_left]`
  fails directly (leftover `Fin.val` coercion).
- **`exact` defeq across `opXxx`/`rewindBracket` + `initFlatConfig`** — normalise the
  start config with an explicit `hinit` (via `M.start = 0`) before `exact`.
- **`#print axioms`** needs the full name + `import Complexity.Lang.Compile`; scratch:
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean`.

## Conventions

- Build `lake build` (or `lake build Complexity.Lang.X`); commit per logical step with
  a **green build**; new results must be `#print axioms`-clean (only `propext`/
  `Quot.sound`/`Classical.choice`; **no `sorryAx`** for a finished lemma).
- See ROADMAP "Hard-won gotchas" and "How we work" for full methodology.
