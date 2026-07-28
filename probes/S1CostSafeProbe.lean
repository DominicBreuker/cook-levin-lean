import Complexity.Lang.CostPoly
import Complexity.NP.SAT.CookLevin.Reductions.S1Program

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Probe — how far the `Cmd.PolyCost` cost ladder gets on `s1Program`

`S1Witness.s1Program_polyCost` is the last S1 obligation. `Lang/CostPoly.lean`
reduces it to a per-loop syntactic question:

> does any `forBnd` body **write** a register its own **cost reads**?

If no, `Cmd.polyCost_of_costSafe (by decide)` closes the whole program in one
line. This probe measures the actual split, exhibits the shapes that fail, and
pins the two facts a next session should not re-derive:

* `decide` on `Cmd.CostSafe` is **cheap** even for a real closed gadget
  (§3 runs in seconds) — the residual below is a genuine program property, not
  a tooling limit;
* the leaf emitter `S1Emit.emitBlk` is cost-safe **unconditionally** (§4), which
  is the locked "output register is built by unit-cost appends" invariant
  showing up syntactically: unit-cost ops carry no `costReads` at all.

⚠ §1/§2 walk the *fully unfolded* `s1Program` term and take a few minutes.
-/

open Complexity.Lang

namespace S1CostSafeProbe

/-- Number of `forBnd` nodes. -/
def loops : Cmd → Nat
  | .op _ => 0
  | .seq a b => loops a + loops b
  | .ifBit _ a b => loops a + loops b
  | .forBnd _ _ body => 1 + loops body

/-- Number of `forBnd` nodes whose body writes one of its own cost reads. -/
def unsafeLoops : Cmd → Nat
  | .op _ => 0
  | .seq a b => unsafeLoops a + unsafeLoops b
  | .ifBit _ a b => unsafeLoops a + unsafeLoops b
  | .forBnd _ _ body =>
      unsafeLoops body
        + (if body.costReads.all (fun r => decide (r ∉ body.writes)) then 0 else 1)

/-- The offenders as `(bound register, counter, registers both cost-read and
written by the body)`. -/
def offenders : Cmd → List (Nat × Nat × List Nat)
  | .op _ => []
  | .seq a b => offenders a ++ offenders b
  | .ifBit _ a b => offenders a ++ offenders b
  | .forBnd cnt bnd body =>
      offenders body ++
        (let bad := body.costReads.filter (fun r => decide (r ∈ body.writes))
         if bad.isEmpty then [] else [(bnd, cnt, bad.eraseDups)])

/-! ## §1 — the whole program (2026-07-28-c measurement)

```
loops       S1Program.s1Program = 116825
unsafeLoops S1Program.s1Program =   4683      (4.0%)
```
96% of the program's loops are cost-safe: every emitter loop appends with
`appendOne`, whose `Op.costReads` is `[]`. -/

-- #eval loops S1Program.s1Program
-- #eval unsafeLoops S1Program.s1Program

/-! ## §2 — what the 4% look like

Three shapes, all with a *stable* per-iteration growth budget, i.e. all in
range of `Cmd.polyCost_forBnd_grow`:

1. **unary drains** — `forBnd cnt r (tail r r)`, where the bound register is
   also the drained one (`(14,27,[14])`, `(40,45,[40])`, `(41,22,[41])`,
   `(42,22,[42])`, `(23,28,[23])`). `Cmd.polyCost_tailLoop` closes these.
2. **unary products** — `forBnd cnt bnd (concat dst dst src)` inside
   `hvBlk`/`pushKey`. `Cmd.polyCost_mulLoop` closes these.
3. **per-iteration value rebuilds** — the big ones, e.g.
   `(19,43,[21,44,45])` (the body rebuilds `CX` every iteration — `loadX`, the
   `xv` recompute, S1CardEmit finding 3) and `(20,43,[24,23,44,45,47,34])`
   (`CD` drained, `CH` advanced, the inner counters `EJ2`/`EJ3` used as emitter
   *bounds*). Each such register is overwritten from a stable register every
   iteration, so its growth budget really is stable — but seeing that needs a
   must-def (kill) analysis, not the current read/write over-approximation.

⚠ **FINDING X — `Cmd.op (.copy r r)` is a semantic no-op but NOT a cost no-op,
and it is used on the OUTPUT register.** `Op.cost (copy dst src) = |src| + 1`,
so the else-branch no-op (`S1CardEmit.copy_self_get`, `S1Prelude.pKindCmd`'s
`[]` case, `S1PreludeEmit`) charges the whole emitted stream *once per
iteration* — which is why `EOUT_C = 34` shows up as a genuine `costRead` above,
against the "output is built by unit-cost appends" invariant's spirit. The
program stays polynomial (it is `O(output²)`, and the measured head-room is
`> 6·10^8`), so **do not re-open the pinned `_run` lemmas to swap the no-op**.
But it does mean the output register is an accumulator for cost purposes:
`Cmd.polyCost_forBnd_grow` is *required*, not optional, and its growth budget
must cover `EOUT_C`.

**The concrete next bottom-up task**: a structural growth analysis
(`Cmd.GrowSafe`) that (a) allows a self-referential write whose sources are
stable, and (b) kills a register the body *overwrites* before reading, so shape
3 stops counting as an accumulator. With it, `polyCost_of_costSafe` generalises
to `polyCost_of_growSafe` and the ladder becomes one `decide`. Note (b) is what
`EOUT_C` does *not* satisfy — it is a true accumulator, so its growth budget is
the per-iteration emitted length, bounded by the stable registers. -/

-- #eval (offenders S1CardEmit.cCopy).eraseDups

/-! ## §3 — `decide` scales

`S1CardEmit.cCopy` is a real closed stage-C family; the kernel decides its
`CostSafe` in seconds. (It decides to `false` — see §2 shape 3, the `CX`
rebuild — so this is an interface check, not a proof.) -/

example : S1CardEmit.cCopy.CostSafe = false := by decide

/-! ## §4 — the leaf emitter is cost-safe with NO side conditions

`emitBlk cnt src dst` = `tallyReg` (a `forBnd cnt src (appendOne dst)`) plus one
`appendZero`. Nothing reads `dst`, so no register aliasing hypothesis is needed
— contrast `emitBlk_run`, which needs `cnt ≠ dst`. Every emitter leaf in the
project should close exactly like this. -/

theorem emitBlk_polyCost (cnt src dst : Var) :
    Cmd.PolyCost (S1Emit.emitBlk cnt src dst) := by
  refine Cmd.polyCost_of_costSafe _ ?_
  simp [S1Emit.emitBlk, FrontPieces.tallyReg, Cmd.CostSafe, Cmd.costReads,
    Cmd.writes, Op.costReads, Op.writesTo]

/-- The three ready-made self-referential rules typecheck against the real
register numbers (interface check for the next session). -/
example : Cmd.PolyCost (Cmd.forBnd S1Emit.EJ1 S1CardEmit.CD
    (Cmd.op (.tail S1CardEmit.CD S1CardEmit.CD))) :=
  Cmd.polyCost_tailLoop _ _ _ (by decide)

/-! ## §5 — a worked walk of one real family: `S1CardEmit.cCopy`

This is the template for route (a) of the NEXT-BOTTOM-UP plan. `cCopy` is
`forBnd EJ1 CS2 (loadX EJ1 ;; copyLoopB)`, three loop levels over
`emitId EK1 CX CZ EJ2 CZ EJ3 CZ EOUT_C`. Walking it outwards:

* `copyInner` reads `{CX, CZ, EJ2, EJ3}` and writes `{EK1, EOUT_C}` — disjoint,
  so it is cost-safe.
* `copyLoopC = forBnd EJ3 CS1 copyInner` — still disjoint (`EJ3` is the loop's
  own counter, written by `forBnd` itself and **not** by the body). **Cost-safe,
  and it closes with one `decide`** (checked below).
* `copyLoopB = forBnd EJ2 CS1 copyLoopC` — **this is where it breaks**:
  `EJ3 ∈ copyLoopC.writes` (the inner loop writes its counter) and
  `EJ3 ∈ copyLoopC.costReads` (the emitter emits the counter's value). Nothing
  is accumulating; `EJ3` is simply re-set each inner run. `Cmd.forBnd_counter_le`
  is the lemma that says so: after `copyLoopC`, `|EJ3| ≤ max |EJ3| |CS1|`.
* `cCopy` then wraps `loadX EJ1 ;; copyLoopB`, where `loadX` rebuilds `CX` from
  the stable `CBV` — the same pattern one level up.

So a *per-family* `PolyCost` proof is: `polyCost_of_costSafe (by decide)` for
the inner nest, then `polyCost_forBnd_grow` at each level whose body re-sets a
register the level below reads, with `Cmd.forBnd_counter_le` (and the analogous
"rebuilt from a stable register" fact for `CX`) supplying the growth budget.
**Estimate: one such proof per card family, not one per loop** — seven for
stage C, plus the prelude and step nests. -/

/-- The inner two levels really are cost-safe: no invariant, no register table. -/
example : S1CardEmit.copyLoopC.CostSafe = true := by decide

example : Cmd.PolyCost S1CardEmit.copyLoopC := Cmd.polyCost_of_costSafe _ (by decide)

/-- …and the third level is not — the inner counter `EJ3` is both written and
cost-read. This is shape 3 in the small. -/
example : S1CardEmit.copyLoopB.CostSafe = false := by decide

end S1CostSafeProbe
