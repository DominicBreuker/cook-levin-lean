# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first; they
are the authoritative status and plan. This file tells the next agent exactly
what to do next and what to watch out for.

## Where things stand

- `lake build` ✅ green (3357 jobs). First build is slow (mathlib); after that,
  one module rebuilds in ~5–10s. `lake` is **not on PATH** — prefix with
  `export PATH="$HOME/.elan/bin:$PATH"`.
- **Risk C2 (compiler soundness) is the focus.** Done & axiom-clean: the
  residue-tolerant contract + composition (`compileSeq_sound_physical_residue`),
  the `rewindBracket` builder (`rewindBracket_transport`), the two-phase rewind,
  and the **append op end-to-end** (`opAppendBit_physical_residue`, the append
  cases of `compileOp_sound_physical_residue`). The decider bridge uses the
  residue contract. The remaining work is the **10 stub ops** + assembling
  `Compile_run_physical_residue`.

## ⚠ READ THIS FIRST — the previous plan was wrong (cross-register finding)

The old handoff said "next: `opTail` via `compute := navigate-to-dst ⨾
deleteCarryTM`, then copy that template for every other op." **That is a
misconception.** Those ops are **cross-register**, not in-place:

```
tail dst src  =  s.set dst (s.get src).tail        -- read src, WRITE dst
copy/head/eqBit/nonEmpty/takeAt/dropAt/concat/consLen  -- all read src(s), write dst
```

The real DSL witnesses use them cross-register — `PolyTime.lean` has
`Op.head 1 0`, `Op.tail 2 0`, `Op.takeAt 3 2 1`, `Op.tail (Wf.regBound+1) 0`.
An in-place delete at `dst` does **not** compute `dst := f (s.get src)` when
`dst ≠ src`. The gadget library (scan / insert-one-symbol / delete-one-cell) has
**no data-transport gadget**, so none of these 9 ops can be built from it as-is.

**Only three ops are genuinely in-place:** the two append ops (done) and
`clear dst` (no source register). Everything else needs a new primitive.

### The real critical path: a single-tape block-move gadget

Build **`copyBlockTM`** — transport register `src`'s (shifted) content to just
inside register `dst`'s slot, resizing the slot (insert/delete cells) so the new
length fits. On a one-head single tape this is the classic shuttle: mark a
position, carry one symbol across, repeat — O(n·distance) steps, still
polynomial (linear per symbol × linear distance ⇒ keep the per-fragment budget
*linear in tape length per carried symbol*; the whole fragment is then
≤ quadratic, which composes into the global quadratic with slack — see ROADMAP
1b on linear-not-cubic budgets). Once `copyBlockTM` exists, **every cross-register
op decomposes**: `dst := f(src)` = (clear dst) ⨾ (copyBlock src→dst) ⨾ (the
in-place transform on dst). For example `tail dst src` = copy src→dst, then
delete dst's first content cell; `head dst src` = copy, then clear all but the
first; the length ops are copy + in-place truncate.

**Recommended order:**
1. **Probe `copyBlockTM` first (go/no-go, time-boxed).** Define the TM, `#eval`
   it on a small encoded tape, and confirm: (a) it reproduces `src` content at
   `dst` and resizes correctly, (b) its exit head lands in the residue past the
   real terminator (so the **two-phase rewind** applies — same precondition the
   append op needed; verify with `#eval`), (c) the step count is linear-per-symbol.
   Decompose into existing atoms where possible (`scanRightUntilTM`,
   `insertCarryTM`, `deleteCarryTM`) glued by `composeFlatTM`. **Verdict before
   committing the run-lemma engineering.**
2. Prove `copyBlockTM_run` / `_no_early_halt` (the new gadget work — the bulk).
3. Wrap with `rewindBracket` (head→0), and prove the per-op residue contract by
   **copying the `opAppendBit_physical_residue` template** (Compile.lean): feed
   `rewindBracket_transport` the gadget run + the `encodeTape ++ residue`
   decomposition. Use the two new bookkeeping lemmas (below) for the residue
   length / validity. Then discharge that op's branch of
   `compileOp_sound_physical_residue`.
4. `clear dst` is **also foundational, not just a quick win**: clearing `dst`'s
   old slot is the shared prerequisite for *every* cross-register op (you must
   vacate `dst` before writing the new value). Its **spec bridge is now proven**
   — `Compile.clear_block_decomp` (Compile.lean): clearing `dst` deletes exactly
   the contiguous `shiftReg (s.get dst)` block before that register's `0`
   delimiter, so the gadget input `encodeTape s ++ res_in` is
   `pre ++ shiftReg(s.get dst) ++ (0 :: rest ++ res_in)` and deleting those
   `|s.get dst|` cells yields exactly
   `encodeTape (Op.eval (clear dst) s) ++ (res_in ++ replicate |s.get dst| 0)`
   (residue `res_out = res_in ++ replicate |old| 0`, valid by
   `ValidResidue_append_replicate_zero`). **Remaining for `clear`:** build the
   gadget `clearRegionTM` (navigate to `dst`'s content start, then a `loopTM`
   that deletes one content cell per pass until it reads the `0` delimiter, head
   reset each pass — `loopTM`/`loopTM_run` proven, `TMPrimitives.lean`; body =
   `deleteCarryTM` + a rewind-to-content-start guard); prove `clearRegionTM_run`
   against the `clear_block_decomp` target; wrap with `rewindBracket` (head→0,
   two-phase since the freed `0`s are residue past the terminator); then discharge
   the `clear` branch of `compileOp_sound_physical_residue` via the
   `opAppendBit_physical_residue` template.

   **✅ Design validated by `#eval` (2026-06-01) — the mechanism works on a real
   tape.** For `s = [[1,0],[1],[]]`, clearing register 0 (content length 2):
   `encodeTape s = [3,2,1,0,2,0,0,3]`; running `deleteCarryTM` from head 2 twice
   (deleting register 0's two content cells) gives `[3,0,2,0,0,3,0,0]`, which
   **equals** `encodeTape (s.set 0 []) ++ [0,0]` (= `encodeTape(cleared) ++
   replicate 2 0`) — confirming `clear_block_decomp`'s residue accounting. Then
   `rewindTwoPhaseTM 4 3` started on the last real cell returns to `{state 6,
   head 0}` (the `rewindBracket` exit). Re-run it (proven primitives only):
   ```
   import Complexity.Lang.Compile; import Complexity.Lang.ShiftTape; import Complexity.Lang.ScanLeft
   open Complexity.Lang Complexity.Lang.ShiftTape Complexity.Lang.ScanLeft
   def s0 : State := [[1,0],[1],[]]
   def stepDel (t : List Nat) : List Nat :=
     match runFlatTM 50 deleteCarryTM { state_idx := 0, tapes := [([], 2, t)] } with
     | some c => match c.tapes with | (_,_,r) :: _ => r | _ => [] | none => []
   #eval stepDel (stepDel (Compile.encodeTape s0)) == Compile.encodeTape (s0.set 0 []) ++ [0,0]  -- true
   ```
   ⚠ **Head management is the fiddly part** (confirmed by `#eval`): `deleteCarryTM`
   leaves the head **one past the end** (on the blank), so the gadget steps left
   off the blank before the two-phase rewind (like `rewindFromEndTM`). And the
   loop body's rewind to a *fixed reference* each pass is cleanest as
   **rewind-to-0 + re-navigate** (mid-tape markers aren't unique — the reason the
   two-phase rewind exists), which is what makes `clear` quadratic (budget below).

   **✅ Inductive heart PROVEN (2026-06-01), axiom-clean.** The mathematical core
   is done — the rest is TM-composition plumbing:
   - `Compile.encodeTape_reg_decomp` — master register-slot decomposition:
     `encodeTape (s.set dst v) = pre ++ shiftReg v ++ 0::rest` with `pre`/`rest`
     **independent of `v`** (the workhorse every register-writing op uses).
   - `Compile.deleteCarry_drop_head` — one `deleteCarryTM` pass deletes a block's
     head: `pre ++ (c0+1)::M → pre ++ M ++ [0]` (from `deleteCarryTM_loop_run`).
   - `Compile.deleteCarry_tail_step` — **one deletion = the in-place `tail` step**
     on the encoded tape: deleting register `dst`'s first content cell yields
     `encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0])`. **Also the core of
     the in-place `tail` op** (`tail dst dst`).
   - `Compile.set_tail_iterate` — the loop's **state-level invariant**:
     `(fun t => t.set dst t.tail)^[n] s = s.set dst ((s.get dst).drop n)`; at
     `n = |s.get dst|` this is `clear`. (Plus the supporting `State` algebra
     `set_eq_list_set`/`get_set_eq`/`set_get_self`/`set_set`.)

   - `Compile.iterate_tail_clear` — `(tail-body)^[|s.get dst|] s = Op.eval (clear
     dst) s`: the exact `loopTM` iteration count.

   So **both halves of the loop's correctness are proven** — the per-iteration tape
   effect (`deleteCarry_tail_step`) and the iterated state effect
   (`set_tail_iterate`/`iterate_tail_clear`). What remains is purely the
   autonomous-machine packaging.

   **Complete proven inventory for `clear` (all axiom-clean, in `Compile.lean`):**
   `encodeTape_reg_decomp`, `clear_block_decomp`, `deleteCarry_drop_head`,
   `deleteCarry_tail_step`, `set_eq_list_set`, `get_set_eq`, `set_get_self`,
   `set_set`, `set_tail_iterate`, `iterate_tail_clear` — plus the budget infra
   (`linear_le_quadratic_tapeLen`, `encodeTape_set_length`,
   `ValidResidue_append_replicate_zero`). Every obligation the machine will face is
   pre-discharged as one of these.

   **Machine-assembly notes (for the next session):**
   - ⚠ **No `stepRightTM` exists** (only `stepLeftTM`, `ScanLeft.lean`). Navigation
     to register `dst`'s content-start from head 0 needs a rightward move past the
     leading sentinel for the base case. Either add `stepRightTM` (mirror
     `stepLeftTM`) or design the loop body around register `dst`'s **delimiter**
     instead (reusing `appendAtTM`'s scan-to-delimiter navigation pattern: delete
     the cell *before* the delimiter — the last content cell — each pass; "empty"
     is detected when that cell is `0`/`3`).
   - The body `B` (two exits) = `navigate ⨾ branch(cell=delim? done : delete) ⨾
     two-phase-rewind-to-0`; the navigation recursion mirrors `appendAtTM`
     (`composeFlatTM (scanPastDelimTM 4 0) … 1`); the delete step's tape contract IS
     `deleteCarry_tail_step`; the rewind is `rewindTwoPhaseTM`. Feed `B` to
     `loopTM_run` (tape family `T n` = "head 0, register `dst` has `n` content
     cells, residue carries the `|content|−n` freed zeros"; count `= |s.get dst|`,
     final state via `iterate_tail_clear`). Wrap in `rewindBracket`; discharge the
     `clear` branch of `compileOp_sound_physical_residue` (budget `9·tapeLen²+9`).

   **Remaining (the loopTM plumbing — large but mechanical, no unknowns):**
   1. Body machine `B` (two exits): from head 0, `NAV` (scan past `dst` delimiters
      to content-start — chain `scanPastDelimTM`/`scan_to_delim`), read the cell:
      delimiter `0` → `exitDone`; nonzero → `deleteCarryTM` (per `deleteCarry_tail_step`)
      ⨾ two-phase rewind to 0 → `exitLoop`. Compose via `composeFlatTM`/
      `branchComposeFlatTM`; prove `B`'s per-iteration + done contracts (the
      iteration contract's tape step IS `deleteCarry_tail_step`).
   2. `clearRegionTM := loopTM B exitDone exitLoop`; apply `loopTM_run` with tape
      family `T n` = "head 0, register `dst` has `n` content cells, residue has the
      `|content|−n` freed zeros", iteration count `= |s.get dst|`. Conclusion: the
      cleared tape (`clear_block_decomp` gives the closed form).
   3. Wrap in `rewindBracket` (already head-0 if the loop ends at 0; else final
      rewind), discharge the `clear` branch of `compileOp_sound_physical_residue`
      (budget `9·tapeLen²+9`, satisfied since the loop is `≈ 6·tapeLen²`).

### ⚠ The per-op budget is now QUADRATIC (was linear — a blocking finding)

`compileOp_sound_physical_residue`'s budget was `3·tapeLen + 8` (linear). That is
**unsatisfiable for every multi-cell op**: on a single-tape machine `clear`/`tail`/
`copy`/… must delete or move `Θ(tapeLen)` cells, and each delete/insert shifts the
suffix in its own O(tapeLen) pass (one head can't shift a block by a data-dependent
distance in one pass), so they are inherently **Θ(tapeLen²)**. The budget is now
`9·tapeLen² + 9` (constant generous, tunable). This composes: `compileSeq_sound_physical`
uses the *additive* `t₁+1+t₂` (no linearity baked in), so summing per-op quadratics
over `≤ cost` fragments stays polynomial (`toFrameworkWitness'` only needs `inOPoly`).
The append cases now relax their linear bound via `Compile.linear_le_quadratic_tapeLen`.
**When building `clear`/`copy` gadgets, target `9·tapeLen²+9`** (e.g. the rewind-to-0
loop design for `clear` costs ≈ `6·tapeLen²`); bump the constant if a gadget needs it.

### New this session (axiom-clean, ready to use)

- `Compile.linear_le_quadratic_tapeLen`: `3·L+8 ≤ 9·L²+9` (the append→contract
  budget relaxation; `L = tapeLen ≥ 2`).
- `Compile.clear_block_decomp` (Compile.lean, after `encodeTape_split`): the
  **`clear` gadget's input/output spec bridge** (see step 4 below) — clearing
  `dst` deletes exactly the `shiftReg (s.get dst)` block; the proven target a
  future `clearRegionTM_run` discharges.
- `Compile.encodeTape_set_length` (Compile.lean, near `encodeTape_length`):
  `|encodeTape (s.set dst v)| + |old dst| = |encodeTape s| + |v|` for
  `dst < s.length` — the residue/budget bookkeeping for **every** cross-register
  op (the register count is preserved by an in-range `set`, so only the contents
  term moves, via `State.size_set_add`).
- `Compile.ValidResidue_append_replicate_zero`: `res ++ replicate n 0` is
  `ValidResidue` — the residue shape a length-decreasing write produces.

## Architecture recap (still valid — the residue-tolerant contract)

**The physical TM tape never shrinks** (`TapeMono.lean`), so an exit tape is
`encodeTape output ++ residue` with `ValidResidue residue` (every cell ∈ {0,1,2}),
hidden existentially in `TapeOK`. Decode ignores residue
(`decodeTape_encodeTape_append`); composition threads it
(`compileSeq_sound_physical_residue`). **Residue lives *after* the trailing
terminator**, so a rewinding gadget exits inside the residue → always use the
**two-phase rewind** `rewindTwoPhaseTM` (scan-left through residue to the real
terminator, step off, scan-left to the leading sentinel). Never start
`scanLeftUntilTM` on a `3`.

**`rewindBracket compute exit … : CompiledCmd`** wraps any `compute` machine with
the two-phase rewind and demotes its boundary halt (`joinTwoHalts`), giving a
unique-exit `CompiledCmd`. `rewindBracket_transport` turns the gadget's proven
run + no-early-halt trajectory into the `CompiledCmd`'s. **Every rewinding op
(append, and the future `copyBlock`-based ops) reuses these verbatim** — only the
`compute` machine differs.

## The append template (copy this for each new op)

`Compile.opAppendBit_physical_residue` (Compile.lean) is the worked example:
`rewindBracket_transport` (compute = `appendAtTM ins dst`) fed by
`appendAt_twoPhaseRewind_run`/`_no_early_halt`, plus the `encodeTape`
decomposition (sentinel-folded blocks, terminator position
`p = |encodeTape output| − 1`, residue past `p`) that discharges the gadget's
tape side-conditions. Per-op budget is **`3·tapeLen + 8`** (two-phase rewind = 2
more `Lmove`s than single-phase). Keep every per-fragment budget **linear** —
quadratics don't compose (finding block above `compileSeq_sound`).

## Key files

| File | Contents |
|------|----------|
| `Lang/Compile.lean` | compiler, residue infra (`TapeOK`/`ValidResidue` + helpers, `encodeTape_set_length`), `joinTwoHalts`+run lemma, `rewindBracket`(+`_transport`), `opAppendBitRewind`, `opAppendBit_physical_residue` (template), `compileOp_sound_physical_residue` (append done; 10 sorries), `Compile_run_physical_residue` (sorry) |
| `Lang/AppendGadget.lean` | `appendAtTM`, `appendAtThenTwoPhaseRewindTM`, `appendAt_twoPhaseRewind_run/_no_early_halt` |
| `Lang/ScanLeft.lean` | `scanLeftUntilTM`, `rewindFromEndTM`, `rewindTwoPhaseTM` (+ halt characterization) |
| `Lang/ShiftTape.lean` | `insertCarryTM` + `deleteCarryTM` (+ run / `_no_early_halt`) — the atoms `copyBlockTM` will compose |
| `Lang/Navigate.lean` / `ScanPast.lean` | register navigation atoms (`scan_to_delim`/`scan_to_end`/`scanPastDelimTM`) |
| `Lang/Semantics.lean` | `Op.eval` (← the cross-register truth), `Op.cost`, `State.size_set_add` |
| `Complexity/TMPrimitives.lean` | `composeFlatTM_run/_no_early_halt`, `loopTM_run` |
| `Complexity/TapeMono.lean` | tape non-shrink finding |

## Gotchas

- **Cross-register reality (above)** — do not build any read-src/write-dst op as
  an in-place edit. It must transport data via `copyBlockTM`.
- **`halt_unique` for rewinds**: any machine ending in a left-scan has 2 halt
  states. Don't hand-build the `CompiledCmd` — use `rewindBracket`.
- **Tape can't shrink**: never state an op's exit tape as a shorter `encodeTape`.
  Use `TapeOK`/`ValidResidue`; deletion residue is `res_in ++ replicate n 0`.
- **`omega` vs `Var`**: `Var := Nat` is opaque to `omega`; restate at `Nat`.
- **`get`-congruence across list equality**: route through `getElem?`. Reuse the
  `hleft`/`hright` split helpers in `opAppendBit_physical_residue`
  (`getElem?_append_left/right` + `Option.some.inj`); `rw [List.getElem_append_left]`
  fails directly (leftover `Fin.val` coercion).
- **Don't `set` a length you also feed to `getElem_append_*`** — it folds the
  length everywhere and breaks unification. Only `set` the terminator position.
- **`exact` defeq across `opXxx`/`rewindBracket` + `initFlatConfig`** — normalise
  the start config with an explicit `hinit` (via `M.start = 0`) and `rw [hinit]`
  before `exact htrans.1` (see the append proof's `hstart0`/`hinit`).
- **`#print axioms`** needs the full name `Complexity.Lang.Compile.<x>` and the
  import `Complexity.Lang.Compile`. Scratch file:
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean`.

## Conventions

- Build: `lake build` (or `lake build Complexity.Lang.X` for one module).
- Commit per logical step with a **green build**.
- New results must be `#print axioms`-clean (only `propext`/`Quot.sound`/
  `Classical.choice`; **no `sorryAx`** for a finished lemma).
- See ROADMAP "Hard-won gotchas" and "How we work" for full methodology.
