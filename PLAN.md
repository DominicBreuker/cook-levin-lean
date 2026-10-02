# Plan: hardness for all of NP — done

## Status

The goal of the previous plan is reached. `CookLevin/Theorem.lean` proves

```lean
theorem cook_levin : NPcomplete SATStr
theorem inNP_iff_inNPCmd (Q : List Bool → Prop) : inNP Q ↔ inNPCmd Q
theorem cook_levin_cmd : NPcompleteCmd SATStr   -- the former statement
```

with `NPhard P := ∀ Q, inNP Q → Q ⪯p P` and `NPcomplete P := NPhard P ∧ inNP P`
(`Basic/StringTM.lean`). The statement no longer mentions the register language; its
reading list (`ReadingList.lean`) has 68 definitions instead of 111. The build is green and
the axiom gate covers the new modules.

## A correction to the definition of NP

The previous plan aimed at `inNP ⊆ inNPCmd` with the old definition of `inNP`, in which the
certificate bound was any function `p` with `inOPoly p`. That inclusion is false: with
`R x c := |c| = |x| + 1` (decidable in polynomial time) and `p n = n + [n ∈ H]` (bounded by
`2n`) for an arbitrary `H ⊆ ℕ`, the language `x ∈ Q ⇔ |x| ∈ H` satisfies the old `inNP`,
while every `inNPCmd` language is decidable (`SearchDecide.lean`) and reduces to `SATStr`.
`inNP` now bounds certificates by an explicit polynomial `a·|x|^k + b`, as the textbook
definition does (GUIDE §4.2 explains this to readers). The running-time bound `t` stays an
`inOPoly` function: it only bounds a halting time, and `inOPoly_monomial_bound` turns it into
an explicit polynomial inside the proof.

## How `inNP ⊆ inNPCmd` is proved (`CookLevin/Simulation/`)

| file | content |
|---|---|
| `Zipper.lean` | `runFlatTM n M cfg = some ((stepCfg M)^[n] cfg)`; the tape `(h, right)` as a zipper (cells left of the head, cells from the head, excess of the head beyond the end) and `zip_tapeStep`: a machine step is a local zipper operation |
| `Gadgets.lean` | register names; blocks (`blk W v = 1^v 0^(W-v)`, `W = sig + 4`); `takeTo`/`dropRep` (move/drop `W` cells, loop-free) |
| `Step.lean` | `writeCode`, `moveCode`, `testCode`, `applyCode`, the first-match `chainCode`; `Repr M cfg s`; `guardedStep_run : Repr M cfg s → Repr M (stepCfg M cfg) (guardedStep M).eval s` |
| `Program.lean` | `simTM`: certificate-length test, time budget `T = ct·(n+1)^kt + dt`, initial tape, `T` guarded steps, verdict; `simTM_get` (what it outputs); `simTM_ub` (registers) |
| `Cost.lean` | cost of each phase; the main loop body is loop-free, so `Cmd.cost_forBnd_flat_le` applies with register lengths bounded through `Repr` and `iterate_growth` |
| `Witness.lean` | `simBound` (a monotone polynomial), `simTM_cost`, and `inNP_inNPCmd` building the `NPWitnessStr` |

## Possible follow-ups (none is needed for the theorem)

* `StatementMeaning.lean` could state the counterexample above as a theorem (it needs a
  concrete machine deciding `|c| = |x| + 1`, e.g. compiled from a register program with
  `inNPCmd_inNP`), to document why the certificate bound is an explicit polynomial.
* `SearchDecide.lean` could restate its result for `inNP` via `inNP_iff_inNPCmd`.
* `Simulation/Cost.lean` bounds the loop body with `Cmd.flatK`, a constant that is huge for
  machines with many transitions; harmless for polynomiality, but a tighter bound would be
  needed if anyone wanted concrete running times.
