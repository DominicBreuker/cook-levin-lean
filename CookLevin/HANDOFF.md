# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first; they
are the authoritative status and plan. This file tells the next agent exactly
what to do next and what to watch out for.

## Where things stand

- `lake build` ✅ green (3357 jobs).
- `#print axioms CookLevin` = `[propext, sorryAx, Classical.choice, Quot.sound]`
  — conditional on `sorryAx`; also vacuous due to S1/S2/S3 (see ROADMAP).
- **Risk C2 (compiler soundness) is the current focus**, and this session
  surfaced a **blocking structural finding** that redirects the per-op work.

## ⚠ THE FINDING (read before touching `compileOp_sound_physical`)

**The physical TM tape can never shrink.** In this machine model a tape is
`(left, head, right)` with all content in `right`; `writeCurrentTapeSymbol`
keeps `right` the same length (in-range write) or grows it (out-of-range pad),
and `moveTapeHead` never touches `right`. So `right.length` is **monotonically
non-decreasing along every run** — machine-checked in
[`Complexity/Complexity/TapeMono.lean`](Complexity/Complexity/TapeMono.lean)
(`runFlatTM_single_length_le`, `runFlatTM_initFlatConfig_no_shrink`,
axiom-clean).

But `compileOp_sound_physical` requires the gadget to halt with its tape
**exactly** `encodeTape (Op.eval o s)` (so fragments compose via
`compileSeq_compose_physical`). For every **length-decreasing** op — `clear`,
`tail`, shrinking `copy`, `head`, `eqBit`, `nonEmpty`, and the length-as-value
ops — that target is a **shorter** list than the input `encodeTape s`, so **no
run can produce it**. The exact-tape contract is *unsatisfiable* for them. This
is machine-checked: `Compile.clear_physical_unsatisfiable` (in `Compile.lean`).

`appendOne`/`appendZero` are the only ops done precisely because they purely
**grow** the tape (insert one cell), so the lengths match exactly. **Do not try
to implement `opClear`/etc. against the current exact-tape contract — it cannot
be proved.** The prior handoff's "follow the `appendBit_physical` pattern for
the 10 stub ops" instruction is void as stated.

## Next step: the residue-tolerant physical contract (Risk C2, step 1b-fix)

Replace the exact-tape contract with a **residue-tolerant** one before
concretising any deletion op. The design (validated this session — see
"What is already proved" below):

1. **Contract shape.** A gadget's exit tape is `encodeTape (output) ++ residue`
   (head rewound to `0`), where `residue` is a **terminator-free** trailing
   block (the cells vacated by left-shifting, overwritten with a non-`3`
   filler — `0` is simplest). Capture this with a relation, e.g.
   `TapeOK out tp := ∃ res, (∀ x ∈ res, x ≠ endMark) ∧ tp = ([], 0, encodeTape out ++ res)`.
   The start tape is also `TapeOK`, so the residue is hidden existentially and
   composition needs no residue bookkeeping.

2. **Decoding still works** — proved: `Compile.decodeTape_encodeTape_append`
   (`decodeTape` of `encodeTape s ++ residue` at any head `= s`, any residue),
   because `decodeTape`'s `takeWhile (· ≠ endMark)` stops at the first real
   terminator and `encodeRegs` of a `BitState` is terminator-free.

3. **Two-phase rewind.** With residue present the head no longer ends on *the*
   trailing terminator. Rewind in two scans: `scanLeftUntil 3` (lands on the
   real terminator — residue is terminator-free, so it's the first `3` from the
   right), `stepLeft`, `scanLeftUntil 3` (lands on the leading sentinel at index
   `0` — the interior `encodeRegs` is terminator-free). Build this from
   `ScanLeft.scanLeftUntilTM` + `stepLeftTM` (both exist), generalising
   `rewindFromEndTM`. **Invariant each gadget must keep:** after its main work,
   the head is at-or-left of the real terminator (so the first left-scan finds
   it). Both append and delete naturally satisfy this.

4. **The deletion primitive `deleteCarryTM`** — the genuinely missing gadget
   (mirror of `ShiftTape.insertCarryTM`). Left-shifts a suffix by one, deleting
   the cell at the head and writing a `0` filler into the vacated trailing cell
   (keeping `right.length` fixed, residue terminator-free). Sketch (3 non-halt
   states): from head `p+1` read `cell[p+1]`, move left, write it at `p`, move
   right twice; repeat; halt on the blank past the end. Prove its `_run` +
   `_no_early_halt` lemmas like `insertCarryTM`. **This is the first concrete
   coding step** and unblocks `clear`/`tail`/`copy`/… (each is navigate-to-`dst`
   + delete-old-content + insert-new-content + rewind).

5. **Restate the four `compile*_sound_physical` lemmas** with `TapeOK` instead
   of the exact tape. `compileSeq_sound_physical`/`compileSeq_traj_physical` are
   already proved for the exact form (`Compile.lean`); re-derive them for
   `TapeOK` (the head-`0` exit still makes `r1`'s config the `initFlatConfig` of
   `r2`, now modulo residue). Keep the **linear** per-fragment budgets (see
   ROADMAP Risk C2 budget-shape finding — quadratics do **not** compose).

6. **Then** concretise the 10 stub `compileOp`s (4) and assemble
   `Compile_run_physical` by induction on `Cmd` (`compileIfBit`/`compileForBnd`
   via `branchComposeFlatTM_run`/`loopTM_run`).

### What is already proved (this session, all axiom-clean)

| Lemma | File | Use |
|------|------|-----|
| `runFlatTM_single_length_le`, `runFlatTM_initFlatConfig_no_shrink` | `Complexity/TapeMono.lean` | the non-shrink finding; reuse for any tape-length bound |
| `Compile.clear_physical_unsatisfiable` | `Lang/Compile.lean` | concrete proof the exact contract fails for `clear` |
| `Compile.decodeTape_encodeTape_append` | `Lang/Compile.lean` | residue-tolerant decode — foundation of step 2 |
| `Compile.ValidResidue` + `compileSeq_sound_physical_residue` / `compileSeq_traj_physical_residue` | `Lang/Compile.lean` | **design validation: the residue-tolerant contract composes** (step 5, `compileSeq` case, done) |

### Design probe — does the residue-tolerant redesign blow up later? (risk register)

Pressure-tested before building the gadgets. **It does not blow up at the
design/composition level**, and several existing lemmas turn out to already be
residue-polymorphic. Residual risks are all *gadget-level proof effort*, not
soundness.

- ✅ **Composition threads residue mechanically.** `compileSeq_*_physical_residue`
  are proved by the *same* script as the exact versions — `compileSeq_compose_physical`
  is already polymorphic in the inter-fragment tape; the only new obligation is
  "seam symbols `< 4`", discharged by `ValidResidue`. The `Cmd` induction's
  spine is sound under residue.
- ✅ **Append generalises for free.** `ShiftTape.insertCarryTM_run` is stated for
  an arbitrary suffix with all symbols `< 4`, so trailing residue is just "more
  suffix" — no re-proof needed. Append on `encodeTape s ++ res` yields
  `encodeTape output ++ (res ++ [carried])`, residue grown by one interior cell.
- ✅ **Decode ignores residue** (`decodeTape_encodeTape_append`), so the decider
  bridge (`bitTestTM` reads register `0` at the front; `decodeTape` for output)
  is unaffected.
- ✅ **Budget stays quadratic.** Physical tape length is non-decreasing and
  bounded by the high-water content `≤ size + cost + regBound` (each insertion
  is charged in `Op.cost`; `Cmd.size_eval_le`). So `|residue| ≤ size + cost`,
  every per-fragment linear budget is `O(size+cost)`, and the `O(cost)` fragments
  sum to `O((size+cost)²)`. Residue does not inflate the degree.
- ⚠ **`ValidResidue` is an invariant each gadget must preserve** (residue ⊆
  `{0,1,2}`, i.e. terminator-free). Append preserves it (carries interior
  symbols); delete must write `0` filler, never duplicate the terminator `3`.
  Provable, but it's a real per-gadget obligation — state it in the contract.
- ⚠ **Two-phase rewind is unbuilt and is the trickiest navigation.** Find the
  *real* terminator (first `3` from the right, past the terminator-free residue),
  step left, find the leading sentinel (first `3` past the terminator-free
  interior). Both targets are `3`; correctness relies on `ValidResidue` +
  `BitState`-interior being terminator-free. Each gadget must leave the head
  at-or-right-of the real terminator so phase 1 finds it. **Build + prove this
  before any deletion op.**
- ⚠ **`deleteCarryTM` correctness is the one genuinely new proof.** Left-shift +
  `0`-fill, preserving content `= encodeTape output` and `ValidResidue` residue.
  Sketch in step 4; mirror `insertCarryTM`'s run/no-early-halt structure.
- ◻ **Not yet probed:** `compileIfBit`/`compileForBnd` under residue. Expected
  to generalise like `compileSeq` (their combinators `branchComposeFlatTM_run` /
  `loopTM_run` are likewise tape-polymorphic), but confirm when wiring them.

## Key files

| File | Contents |
|------|----------|
| `Complexity/TapeMono.lean` | **NEW** — tape non-shrink finding |
| `Lang/Compile.lean` | compiler, composition lemmas, physical contracts, residue decode |
| `Lang/ShiftTape.lean` | `insertCarryTM` (insertion) — **mirror for `deleteCarryTM`** |
| `Lang/AppendGadget.lean` | `appendAtTM`, `appendAtThenRewindTM`, `appendBit_physical` |
| `Lang/ScanLeft.lean` | `scanLeftUntilTM`, `stepLeftTM`, `rewindFromEndTM` (→ two-phase rewind) |
| `Lang/Navigate.lean` / `ScanPast.lean` | register navigation atoms |
| `Lang/Syntax.lean` / `Semantics.lean` | `Op`/`Cmd`, `Op.eval`, `Op.cost`, `Cmd.size_eval_le` |
| `Lang/Frame.lean` / `PolyTime.lean` | register bound, S3 bridge, tape-length bound |
| `Complexity/TMPrimitives.lean` | `composeFlatTM_run/no_early_halt`, `loopTM_run` |

## Gotchas (you will likely hit these)

- **Tape can't shrink** (the finding): never state an op's exit tape as exactly
  a shorter `encodeTape`. Use the residue-tolerant `TapeOK` form.
- **Rewind**: gadgets exit with head on/right-of the trailing `endMark = 3`.
  Use a left-scan to the terminator first; never `scanLeftUntilTM` started on a
  `3` (it halts immediately). With residue there may be one real terminator and
  a leading sentinel — both `3`; distinguish by position via the two-phase scan.
- **`omega` vs `Var`**: `Var := Nat` is opaque to `omega`; restate at `Nat`.
- **`omega` vs list lengths**: `simp only [List.length_*]` first.
- **`get`-congruence across list equality**: route through `getElem?`
  (`congrArg (·[i]?) hl`, then `List.getElem?_eq_getElem`); don't `rw` a length-
  carrying index (ill-typed motive).
- **Core-only files** (`Semantics.lean`, `Frame.lean`): no Mathlib tactics
  (`set`, etc.); `TapeMono.lean` imports only `MachineSemantics`, so use
  `Nat.le_refl`/`Nat.le_trans`, not bare `le_refl`.
- **`haltingStateReached` vs `exit_is_halt`**: `getD` vs `getElem?`; bridge with
  `unfold haltingStateReached List.getD; simp only [heq, exit_is_halt, Option.getD]`.

## Conventions

- Build: `export PATH="$HOME/.elan/bin:$PATH"; lake build` from repo root.
  First build is slow — kick it off in the background early. `lake build
  Complexity.Lang.X` rebuilds one module fast once deps are built.
- Commit per logical step with a **green build**; record gaps in commit messages.
- New results must be `#print axioms`-clean (only `propext` / `Quot.sound` /
  `Classical.choice`). **No new axioms.** Decompose `sorry`s; don't elaborate.
- Axiom check (lean-lsp can't find `lake`):
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean` with
  `#print axioms <name>`.
- See ROADMAP "Hard-won gotchas" and "How we work" for the full methodology.
