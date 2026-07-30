import Complexity.Lang.CostGrow
import Complexity.Complexity.Deciders.EvalCnfSplit

set_option autoImplicit false

/-! # Probe — what `Cmd.chk` is *supposed* to accept and reject

`Cmd.chk_sound` says acceptance implies `Cmd.CapCost`, so the analysis can never
become *unsound* without a proof breaking. The risk this file covers is the
other two directions, neither of which any theorem catches:

* **silent narrowing** — a refactor that makes `chk` reject a shape the real
  program relies on. The whole-program `decide` in `S1Witness.lean` catches that
  for `s1Program`, but only after a ~3 min kernel run, and it says nothing about
  which *shape* regressed. The positive specimens below name the shapes.
* **silent widening** — a change that makes `chk` accept a shape it must not.
  That would eventually surface as an unprovable `chk_sound`, but only if
  someone re-proves it; the negative specimens below pin the intent *now*, in
  `by decide`, at one hand-sized `Cmd` per rule.

**Every `example` in this file is `by decide` and the whole file runs in
seconds.** Run it after ANY change to `Lang/CostGrow.lean`. If a negative
specimen starts passing, the analysis has been widened — go and check
`chk_sound` still holds before believing it. If a positive specimen starts
failing, the S1 cost ladder is about to break.

## The rule each specimen pins

| § | specimen | verdict | why |
|---|---|---|---|
| 1 | `forBnd cnt bnd (concat d d d)` | **reject** | THE counterexample: squares `d` each iteration, so no polynomial bound exists (locked invariant, 2026-07-28-c). `chk` accepting this would make `chk_sound` false. |
| 1 | `concat d a b` with `a`, `b` uncapped | **reject** | the cap has to come from somewhere. |
| 2 | a drained cursor `forBnd i r (tail r r)` | **accept** | `Cmd.NoGrow`: the bound is `≤ max \|r\| 1`, idempotent, no trip count (FINDING Z's escape). |
| 2 | `certDecode`'s accumulator loop | **accept** | `concat ASSGN ASSGN DIDX` inside a loop, capped because `DIDX` is the loop counter. The live positive specimen the membership half depends on. |
| 3 | flow sensitivity | **accept** | `concat dst src dst` where `src` is built by the straight-line prefix of the same body — what closed `S1StepLoop.scanSeen`. |
| 4 | `C'`/`B` sound when `ok = false` | **accept** | FINDING AC: an enclosing loop's promotion is read off a *rejected* body, and is what makes it acceptable on the second pass. Degrade it and the outer loop fails. |

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/CostChkIntentProbe.lean` -/

open Complexity.Lang

namespace CostChkIntentProbe

/-- Every register capped at entry — the seed the real ladder uses. -/
def allC : Nat := 2 ^ 60 - 1
/-- Nothing capped at entry. -/
def noC : Nat := 0

/-- Readable verdicts for the `#eval`s at the bottom. -/
def ok (C : Nat) (c : Cmd) : Bool := (c.chk C).1

/-! ## §1 — the shapes that MUST be rejected

These are not conservatism: for each of them `Cmd.CapCost` is genuinely false,
so `chk_sound` is what forces the rejection. -/

/-- **The squaring loop.** `forBnd cnt bnd (concat d d d)` doubles `|d|`'s
exponent every iteration: after `m` iterations `|d|` is `|d₀|·2^m`, which no
polynomial in the *entry* sizes bounds. This is the counterexample behind "no
unconditional polynomial cost bound exists for `Cmd`". -/
def squareLoop : Cmd := Cmd.forBnd 1 2 (Cmd.op (.concat 3 3 3))

example : ok allC squareLoop = false := by decide

/-- Still rejected when the destination is also the loop's bound register. -/
example : ok allC (Cmd.forBnd 1 3 (Cmd.op (.concat 3 3 3))) = false := by decide

/-- **An uncapped `concat`.** With no register capped at entry there is nothing
to bound the output by. -/
example : ok noC (Cmd.op (.concat 3 4 5)) = false := by decide

/-- ... and capping the sources fixes exactly that. -/
example : ok allC (Cmd.op (.concat 3 4 5)) = true := by decide

/-- **An inner loop bounded by a register the outer body rebuilds** — the shape
the locked invariant warns compounding sneaks back in through. -/
def rebuiltBound : Cmd :=
  Cmd.forBnd 1 2 (Cmd.op (.concat 4 4 4) ;; Cmd.forBnd 5 4 (Cmd.op (.appendOne 6)))

example : ok allC rebuiltBound = false := by decide

/-! ## §2 — the shapes that MUST be accepted

Each of these occurs in the real program; a narrowing that rejects one of them
re-opens `S1Witness.s1Program_costLeSize`. -/

/-- **A drained cursor.** The loop's own bound register is the one being
consumed. `Cmd.NoGrow`'s bound `≤ max |r| 1` is idempotent — no trip count, no
growth constant — which is what lets it into the frozen set. Without this rule
`stagePG` and `stageInit` fail. -/
def drainLoop : Cmd := Cmd.forBnd 1 2 (Cmd.op (.tail 2 2))

example : ok allC drainLoop = true := by decide

/-- **The `copy r r` no-op** (FINDING X): semantically nothing, but it costs
`|r| + 1` and makes `r` a genuine `costReads` member. `Cmd.CapCost`'s `(N+1)`
factor pays for it. It is the `ifBit` else-branch of every emitter, and of
`EvalCnfSplit.decodeBody`. -/
example : ok allC (Cmd.forBnd 1 2 (Cmd.op (.copy 3 3))) = true := by decide

/-- **An accumulator driven by the loop counter.** `concat dst dst cnt` grows
`dst` by `|cnt| ≤ trip count` per iteration — linear, not squaring. This is
`EvalCnfSplit.decodeBody`'s emit arm. -/
def counterAccum : Cmd := Cmd.forBnd 1 2 (Cmd.op (.concat 3 3 1))

example : ok allC counterAccum = true := by decide

/-- **The live specimen**: the SAT membership decoder, whose loop body is a
guarded accumulator (`concat ASSGN ASSGN DIDX` under two `ifBit`s). This is the
same `decide` that `EvalCnfSplit.certDecode_chk` runs — pinned here so that a
`CostGrow` change shows up in this file rather than in the membership half. -/
example : ok EvalCnfSplit.decRegs EvalCnfSplit.certDecode = true := by decide

/-! ## §3 — flow sensitivity

`concat dst src dst` where `src` is *built by the straight-line prefix of the
same body*. A flow-insensitive growth check (the deleted `Cmd.GrowOk`) cannot
see that `src` is capped, and rejects. This is what closed the last two loops of
the S1 ladder, both in `S1StepLoop.scanSeen`. -/

def flowAccum : Cmd :=
  Cmd.forBnd 1 2 (Cmd.op (.head 4 5) ;; Cmd.op (.concat 3 4 3))

example : ok allC flowAccum = true := by decide

/-- The same body with `4` never written — nothing caps it, so it is rejected.
The negative control for §3: acceptance above really is flow sensitivity, not
a blanket allowance for `concat dst src dst`. -/
example : ok (2 ^ 4 - 1) (Cmd.forBnd 1 2 (Cmd.op (.concat 3 4 3))) = false := by decide

/-! ## §4 — a rejected sub-command must not blind the analysis (FINDING AC)

`Cmd.chk C c = (ok, C', B)`: `C'` and `B` are sound *whether or not* `ok` holds.
An enclosing loop reads them to decide what to promote, and that promotion is
what makes the rejected sub-command acceptable on the second pass. Here the
inner loop is rejected on the first pass; the outer loop still succeeds. -/

def outerOverInnerReject : Cmd :=
  Cmd.forBnd 1 2 (Cmd.forBnd 5 6 (Cmd.op (.appendOne 7)) ;; Cmd.op (.copy 8 7))

example : ok allC outerOverInnerReject = true := by decide

/-! ## Diagnostics -/

#eval (ok allC squareLoop, ok allC rebuiltBound, ok noC (Cmd.op (.concat 3 4 5)))
#eval (ok allC drainLoop, ok allC counterAccum, ok allC flowAccum,
  ok allC outerOverInnerReject)
#eval ok EvalCnfSplit.decRegs EvalCnfSplit.certDecode

/-! Everything at once: the three rejects are `false`, the five accepts `true`. -/
#eval !(ok allC squareLoop) && !(ok allC rebuiltBound) && !(ok noC (Cmd.op (.concat 3 4 5)))
  && ok allC drainLoop && ok allC counterAccum && ok allC flowAccum
  && ok allC outerOverInnerReject && ok EvalCnfSplit.decRegs EvalCnfSplit.certDecode

end CostChkIntentProbe
