import Complexity.Complexity.Deciders.EvalCnfTM.Primitives
import Complexity.Complexity.Deciders.EvalCnfTM.CopyUnary
import Complexity.Complexity.Deciders.EvalCnfTM.CompareUnary
import Mathlib.Tactic

set_option autoImplicit false

/-! # Per-literal evaluator TM (Part 2, Step 11.5)

This file lands the **per-literal evaluator** — the inner-most loop
body of `evalCnfTM`. Given a tape positioned at the **sign byte** of
a literal `(b, v)` in the CNF region, it computes
`evalLiteral a (b, v) : Bool` and ORs the result into the
per-clause OR-accumulator.

The file is a *companion* to `CopyUnary.lean` and `CompareUnary.lean`:
those build the single-purpose primitives (a 7-state TM and a
9-state TM), each ~2.5–4 kLOC; this file assembles them into a
multi-phase pipeline via `composeFlatTM_run`.

### Why this file is opened as a **skeleton + architecture doc** in
Step 11.5a

When Step 11.5 was first scoped (v3 of `PART2.md`), the pipeline was
imagined as five linear `composeFlatTM_run` links (~1.5 kLOC). Three
discoveries during this session forced a rethink:

1. **Slot iteration is a loop, not a chain.** The "scan assignment for
   matching slot" step is fundamentally `forall slot ∈ assgn, compare
   varbuf` with early exit on match. This is the same loop pattern as
   `copyUnaryTM`'s outer iteration over copied `1`s, but with a more
   complex body. Hand-rolling it as a state machine duplicates the
   400–600 LOC iteration-run bookkeeping we already paid twice. The
   only economical path is the **`loopTM` combinator** (Optimisation
   O2 in `PART2.md` §5).

2. **Polarity gates the result bit.** After the loop yields a "match"
   or "no-match" outcome, the bit written to the OR-accumulator is
   `polarity XOR (¬ match)`. The cleanest expression is to **branch
   the pipeline on the sign byte** read in step (1) — i.e. dispatch to
   one of two result-writers. Linear `composeFlatTM_run` doesn't
   support multi-exit dispatch; we need a **`branchComposeFlatTM`
   combinator** (or a polarity-as-scratch-cell workaround; see
   "Design choice 2" below).

3. **Cursor restoration matters for outer composition.** The per-
   *clause* loop (Step 11.6) expects the per-literal pipeline to halt
   with the head at the *first cell past the literal* — i.e., at the
   start of the next literal's sign byte (or at the clause-terminator
   `4`). This means the pipeline must end with a deterministic
   "restore head to position-after-literal" phase. With our current
   primitives that's a `scanLeftUntilTM` to the start-of-scratch
   marker `7`, then a `scanRightUntilTM` of the right kind — but
   getting the *right* kind requires a marker we can place reliably
   (currently `7` is the only one available, and the trip is O(n)).

The session's contribution (11.5a):

* Adds the `advanceRightTM` primitive to `Primitives.lean` — a
  2-state TM that moves the head right by one and halts. Mirrors
  `writeAtHeadTM` in structure. Will be the first composition link
  after the polarity classifier.
* Creates this file with the architecture doc you are reading. No
  concrete `def`s land here yet — every subsequent substep adds
  exactly one or two definitions whose runtime cost is independently
  measurable.

The substep breakdown is:

| Substep | Goal                                                | Est LOC | Sessions |
|---------|-----------------------------------------------------|---------|----------|
| 11.5a   | `advanceRightTM` + this file's skeleton             | ~300    | ✅ done   |
| 11.5b   | `branchComposeFlatTM` (in `TMPrimitives.lean`) + `_run` | ~600    | next     |
| 11.5c   | `loopTM` (in `TMPrimitives.lean`) + `_run` (Opt O2) | ~800    | +1       |
| 11.5d   | `polarityClassifyTM`, `findVarInAssgnTM`, `writeOrBitTM` (this file) | ~600 | +2      |
| 11.5e   | `perLiteralEvalTM` assembly + `_run` correctness    | ~600    | +3       |

(LOC estimates assume each substep follows the
`Primitives.lean`/`CompareUnary.lean` rhythm: definition,
`validFlatTM`, per-state step lemma, per-state halting lemma, run
lemma. They will drift; revise after each.)

### Design choice 1 — alphabet stays at `sigEval = 12`

The polarity bit could be hidden in a new scratch cell, but every
extension of `sigEval` cascades through `encodeInputWithScratch` and
the existing primitives' validity proofs. We avoid that by carrying
polarity in the **TM state**, dispatched via `branchComposeFlatTM`.

### Design choice 2 — polarity dispatch is structural, not data

Two viable encodings of polarity were considered:

* **A: Scratch-cell polarity.** Add a `polarity` cell to the scratch
  suffix; classifier writes 0 or 1 there; the result-writer reads it.
  *Cost:* `scratchSuffix` length changes, all six existing length /
  symbol-bound lemmas update, downstream position arithmetic in
  `copyUnaryTM` / `compareUnaryAtMarkerTM` may need re-indexing.
* **B: State-encoded polarity (chosen).** Classifier halts in one of
  two states (`pos-exit`, `neg-exit`); a new `branchComposeFlatTM M₁
  M₂ M₃ exit_pos exit_neg` dispatches `M₂` on `pos-exit` and `M₃` on
  `neg-exit`. *Cost:* one new combinator, but no encoding churn.

Choice B is structurally cleaner and keeps the encoding stable. The
combinator is symmetric with `composeFlatTM` and reuses most of its
state-mapping plumbing.

### Tape layout assumed by this file

`encodeInputWithScratch (N, a)` is

```
[encodeCnf N] [encodeAssgn a] 7 [varbuf 0s] 8 [OR-acc] 9 [AND-acc] 10
```

where each literal in `N` is `[2|3] [v ones]`, each clause ends in
`4`, the CNF ends in `5`, the assignment is `[v₁ ones] 6 … 6 [vₖ
ones] 6 0`.

The per-literal evaluator is entered with the head positioned on the
literal's sign byte (the `2` or `3`). It exits with the head one cell
past the literal's last `1` — i.e., on the next literal's sign byte,
or on the clause-terminator `4`.

### Pipeline (when fully built — Substeps 11.5d/e)

```
  ENTRY: head at sign byte of literal (b, v)
    │
    ▼
  ┌───────────────────────┐
  │  polarityClassifyTM   │  read 2 or 3; halt at +1 in one of two states
  └────────┬──────────────┘
           │ pos                                       neg
           ▼                                            ▼
  ┌────────────────────────────────────┐    (mirror branch)
  │  copyUnaryTM (sig=12)              │     same pipeline, but
  │   — copies v ones from CNF region   │     with writeOrBitTM
  │     into varbuf (using marker 7)    │     producing the negated
  └────────┬───────────────────────────┘     result bit
           ▼
  ┌────────────────────────────────────┐
  │  scanLeftUntilTM(target=5)          │
  │   + advanceRightTM (skip past 5)    │
  │   — position at start of assgn      │
  └────────┬───────────────────────────┘
           ▼
  ┌────────────────────────────────────┐
  │  findVarInAssgnTM (uses loopTM)     │
  │   — loops slot-by-slot calling      │
  │     compareUnaryAtMarkerTM;          │
  │     exits in MATCH or EXHAUST state │
  └────────┬───────────────────────────┘
           ▼                ▼
        match           exhaust
           ▼                ▼
  ┌──────────────┐   ┌──────────────┐
  │ writeOrBitTM │   │ writeOrBitTM │
  │  (write 1)   │   │  (no-op)     │
  └──────┬───────┘   └──────┬───────┘
         ▼                  ▼
  ┌────────────────────────────────────┐
  │  clearRegionTM(fillSym=0,           │
  │                  endMarker=8)        │
  │   — wipe varbuf for next literal    │
  └────────┬───────────────────────────┘
           ▼
  ┌────────────────────────────────────┐
  │  restoreHeadAfterLiteralTM          │
  │   — scanLeft(7) + scanRight(skip    │
  │     past CNF prefix to end of this  │
  │     literal). Uses a position       │
  │     remembered via cursor marker 11 │
  │     written just-after-entry?       │
  └────────┬───────────────────────────┘
           ▼
  EXIT: head at first cell past the literal
```

The "restore head" phase is the trickiest; an alternative is to
**remember the literal's end position by writing cursor 11 before the
copy phase and erasing it after the OR-bit phase**, then scanning to
it. This mirrors the `copyUnaryTM` source-cursor trick.

### Open questions for substeps 11.5b–e

* Should `findVarInAssgnTM` dispatch to `_run_match` / `_run_short` /
  `_run_long` based on the *current slot's* unary length vs the
  var-buffer's effective length `v`? The dispatch is determined by
  comparing two unary regions before running compareUnary — which is
  itself a comparison! The cleanest path is: don't dispatch — just
  run the *full* compareUnaryAtMarkerTM (which handles all three
  cases internally; the three `_run_*` lemmas already partition the
  proof obligations). The per-slot exit state encodes the result.
* Does `loopTM_run` need to thread `loop-iteration-count`-many
  hypotheses through the body, or can the body's per-iteration run
  lemma encapsulate that? The latter is preferable; the former cubes
  the proof's bookkeeping.

These are resolved when 11.5b / 11.5c land. -/

namespace EvalCnfTM
namespace PerLiteral

/-! ## Skeleton

This namespace is intentionally empty in 11.5a. Concrete definitions
land in substeps 11.5b–e per the table above. The namespace exists so
downstream files can already write `import
Complexity.Complexity.Deciders.EvalCnfTM.PerLiteral` without breaking
the build. -/

end PerLiteral
end EvalCnfTM
