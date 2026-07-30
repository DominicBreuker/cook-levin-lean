import Complexity.Lang.CostGrow
import Complexity.NP.SAT.CookLevin.Reductions.S1Program

set_option autoImplicit false
set_option maxRecDepth 4000000

/-! # Probe — `Cmd.chk` on the real S1 program

`Lang/CostGrow.lean` replaces the naive single cap by two (`MF` over a
frozen set `F`, `N` over everything) and ships `Cmd.chk`, a decidable forward
analysis whose success certifies `Cmd.CapCost`. **It now accepts the whole
program**, which is what closes `S1Witness.s1Program_costLeSize`.

## §1 measurement (2026-07-29-b, the session that closed the ladder)

```
stageSig  ok    stageInit ok    stageFin  ok    stagePG   ok
stageMYes ok    stageMNo  ok    cFive     ok    cPrelude  ok
stepFam   ok    s1Program ok
```

`#eval` over the whole program: **~2 s**. Kernel `decide +kernel`: **~3 min**.

## §2 what each feature buys — turn one off and re-run §3

* **the `(N+1)` factor in `Cmd.CapCost`'s cost clause** — `copy EOUT_C EOUT_C`
  (FINDING X), for free, with no pinned `_run` lemma re-opened;
* **`Cmd.NoGrow`, widened into the frozen set `Fz`** — every drained cursor
  (`forBnd idx SCAN (… tail SCAN SCAN …)`), whose own bound register is the one
  being consumed. Its bound is *idempotent*, so it needs no trip count and no
  growth constant: that is what makes the two-level stratification (`Fz` first,
  then the promoted set) free of circularity. Without it `stagePG` and
  `stageInit` fail — and, less obviously, so does `SSEEN`, because `SCUR` has to
  be capped before the flow can reach `SKQ` → `SAX` → `SSEEN`.
* **flow sensitivity** — `Cmd.op (.concat SSEEN SAX SSEEN)` in
  `S1StepLoop.pushKey`. `SAX` is built by the straight-line prefix of the very
  body that then appends it, so a flow-*insensitive* growth check (the old
  `Cmd.GrowOk`) can never see that it is capped. This is what closed the last
  two rejected loops, `(43, 46)` and `(42, 22)`, both in `S1StepLoop.scanSeen`.
* **the always-sound capped set** — `Cmd.chk` returns `(ok, C', B)` with `C'`
  and `B` valid *even when `ok` is false*. Without that the analysis degrades
  after the first rejected sub-command, and the promotion an enclosing loop
  reads is exactly what would have made that sub-command acceptable: dropping it
  puts `(23, 46)` (`S1CardEmit`'s `CH`-bounded loop) and both `scanSeen` loops
  back. Measured, not guessed.
* **the second pass** — `S1CardEmit.CH` and `S1Emit.EC` (a register advanced by
  `tallyReg` inside the very loop that then uses it as an inner trip bound). It
  is taken only where the first pass is rejected, which on this program is
  inside `cFive` and `stepFam` and **never** inside `cPrelude`.

## §3 the numbers that fix the representation

`Cmd.writes` of `S1Prelude.cPrelude` is a **327411-element list**, and the old
`List Var` checker ran `List.contains` on it once per candidate register (61)
per enclosing loop. `cPrelude` could not be checked at all — neither by `#eval`
nor by `decide`, in 10 minutes. With register sets as `Nat` bitmasks the same
work is a handful of GMP word operations.

```
S1Prelude.cPrelude   538486 Cmd nodes, 7 loops deep
S1Program.s1Program  541378 Cmd nodes, 7 loops deep
```

⚠ **The kernel's wall is MEMORY, not time.** An earlier, two-traversals-per-loop
version of this analysis was **OOM-killed** at 15 GB on `cPrelude` alone. The
single-traversal rule is what makes the whole-program `decide` fit. If you make
the analysis more precise, re-measure §4 before relying on it.
-/

open Complexity.Lang

namespace S1GrowSafeProbe

/-- The whole S1 frame as a bitmask. `S1Program.s1RegBound = 48`; the tail
composite reaches `57`. At program entry every register is bounded by the input
size, so handing the analysis all of them is sound. -/
def allC : Nat := 2 ^ 60 - 1

def loops : Cmd → Nat
  | .op _ => 0
  | .seq a b => loops a + loops b
  | .ifBit _ a b => loops a + loops b
  | .forBnd _ _ body => 1 + loops body

def nodes : Cmd → Nat
  | .op _ => 1
  | .seq a b => 1 + nodes a + nodes b
  | .ifBit _ a b => 1 + nodes a + nodes b
  | .forBnd _ _ body => 1 + nodes body

def depth : Cmd → Nat
  | .op _ => 0
  | .seq a b => max (depth a) (depth b)
  | .ifBit _ a b => max (depth a) (depth b)
  | .forBnd _ _ body => 1 + depth body

/-- Where the analysis still rejects, as `(bound register, counter)` for a loop
and `(dst, 999)` for a `concat` with two uncapped sources. Empty on every
gadget below — keep it that way. -/
def bad : Nat → Cmd → List (Nat × Nat)
  | C, .op o =>
      match o with
      | .concat d a b => if C.testBit a || C.testBit b then [] else [(d, 999)]
      | _ => []
  | C, .seq a b => bad C a ++ bad (Cmd.chk C a).2.1 b
  | C, .ifBit _ a b => bad C a ++ bad C b
  | C, .forBnd cnt bnd body =>
      let Fz := bitOf cnt ||| mdiff C body.ngm
      let r0 := Cmd.chk Fz body
      let F1 := if r0.1 then Fz else Fz ||| mdiff C r0.2.2
      (if C.testBit bnd then [] else [(bnd, cnt)]) ++ bad F1 body

def verdict (name : String) (c : Cmd) : String :=
  s!"{name}: loops={loops c} ok={(c.chk allC).1} bad={(bad allC c).eraseDups}"

/-! ## §4 — per-stage verdicts.  Run each `#eval` on its own. -/

-- #eval verdict "stageSig  " S1Emit.stageSig
-- #eval verdict "stageInit " S1Emit.stageInit
-- #eval verdict "stageFin  " S1Emit.stageFin
-- #eval verdict "stagePG   " S1Parse.stagePG
-- #eval verdict "stageMYes " S1Program.stageMYes
-- #eval verdict "stageMNo  " S1Cards.stageMNo
-- #eval verdict "cFive     " S1CardEmit.cFive
-- #eval verdict "cPrelude  " S1Prelude.cPrelude
-- #eval verdict "stepFam   " S1Step.stepFam
-- #eval verdict "s1Program " S1Program.s1Program

-- #eval (nodes S1Prelude.cPrelude, depth S1Prelude.cPrelude)
-- #eval (nodes S1Program.s1Program, depth S1Program.s1Program)
-- #eval S1Prelude.cPrelude.writes.length   -- 327411: why the lists had to go

/-! ## §5 — kernel checks

The whole-program one is `S1Witness.s1Program_costLeSize` itself; these are the
cheap regression guards. -/

example : (Cmd.chk allC (S1Emit.emitBlk 43 37 34)).1 = true := by decide

example : (Cmd.chk allC S1CardEmit.cFive).1 = true := by decide

example : (Cmd.chk allC S1Step.stepFam).1 = true := by decide

end S1GrowSafeProbe
