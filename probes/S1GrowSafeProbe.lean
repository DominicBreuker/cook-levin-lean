import Complexity.Lang.CostGrow
import Complexity.NP.SAT.CookLevin.Reductions.S1Program

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Probe — `Cmd.capChk` on the real S1 program

`Lang/CostGrow.lean` replaces `Cmd.PolyCost`'s single cap by two (`MF` over a
frozen set `F`, `N` over everything) and ships `Cmd.capChk`, a decidable forward
analysis whose success certifies `Cmd.CapCost`. This probe measures where that
analysis stands on the real program, stage by stage, and localises whatever it
still rejects.

**Run each `#eval` on its own** — the big families take minutes.

## §1 measurement (2026-07-29, the session that built `CostGrow.lean`)

```
stageSig     3 loops   ok     stageMYes    0 loops  ok
stageInit   12 loops   ok     stageMNo     0 loops  ok
stageFin     5 loops   ok     cFive       81 loops  ok
stagePG     30 loops   ok     cPrelude       —      TIMES OUT (see §3)
stepFam    359 loops   ✗  bad = [(43,46), (42,22)]
s1Program           ✗  bad = [(43,46), (42,22)]
```

Everything passes **except two loops**, and both are in `S1StepLoop.scanSeen`:

* `(43, 46)` = `Cmd.forBnd EK1 SSEEN scanBody` — the dedup scan, bounded by the
  seen-set accumulator;
* `(42, 22)` = `Cmd.forBnd SIX EE …` inside `readItem TJ1 EE SIX` in `scanBody`,
  where `EE` is `copy EE SSEEN`.

Both would close if `SSEEN` were promoted, and `SSEEN` genuinely is
`≤ poly`: the entry loop runs `≤ |PNTRANS|` times and each iteration appends one
capped key. What blocks it is that `Cmd.GrowOk` is **flow-insensitive** — it
cannot see that `SAX` is capped at the point of `concat SSEEN SAX SSEEN`, because
`SAX` is *built* earlier in the same body. See the HANDOFF for the fix.

`S1CardEmit.cFive` passing is the measurement that matters for the design: it is
a real, closed stage-C family with three loop levels over `emitId`, and it
exercises all three shapes the 2026-07-28-c probe found unsafe (`loadX`'s
per-iteration `CX` rebuild, the `EJ2`/`EJ3` inner counters used as emitter
bounds, and `EOUT_C` as a genuine `costRead` — FINDING X).

## What each feature buys

Turning a feature off and re-running §2 shows what it covers:

* **the `(N+1)` factor in the cost clause** — `copy EOUT_C EOUT_C` (FINDING X);
* **`Cmd.promote`** — `S1CardEmit.CH` and `S1Emit.EC` (a register advanced by
  `tallyReg` inside the very loop that then uses it as an inner trip bound), and
  `loadSg`'s `ESG`;
* **`Cmd.NoGrow`'s escape inside `GrowOk`** — every drained cursor
  (`forBnd idx SCAN (… tail SCAN SCAN …)`), where the loop's own bound register
  is the one being consumed. Without it `stagePG` and `stageInit` fail.

Each was found by measurement, in that order; none is decorative.
-/

open Complexity.Lang

namespace S1GrowSafeProbe

/-- The whole S1 frame. `S1Program.s1RegBound = 48`; the tail composite reaches
`57`. At program entry every register is bounded by the input size, so handing
the analysis all of them is sound (`Cmd.CapCost`'s `MF` and `N` are both taken
to be `State.size s` by `Cmd.CapCost.cost_le_size`). -/
def allRegs : List Var := List.range 60

def loops : Cmd → Nat
  | .op _ => 0
  | .seq a b => loops a + loops b
  | .ifBit _ a b => loops a + loops b
  | .forBnd _ _ body => 1 + loops body

/-- The loops `capChk` rejects, as `(bound register, counter)`. A rejected loop
is one whose bound register the analysis cannot certify capped at that point;
that is the only way `capChk` fails on a `forBnd` (the only failing `op` is a
`concat` with two uncapped sources, which does not occur in this program). -/
def badLoops : List Var → Cmd → List (Nat × Nat)
  | _, .op _ => []
  | F, .seq a b =>
      match Cmd.capChk F a with
      | some F1 => badLoops F a ++ badLoops F1 b
      | none => badLoops F a
  | F, .ifBit _ a b => badLoops F a ++ badLoops F b
  | F, .forBnd cnt bnd body =>
      (if F.contains bnd then [] else [(bnd, cnt)])
        ++ badLoops (Cmd.freezeFor F cnt body ++ Cmd.promote F cnt body) body

def verdict (name : String) (c : Cmd) : String :=
  s!"{name}: loops={loops c} ok={(Cmd.capChk allRegs c).isSome}" ++
  s!" bad={(badLoops allRegs c).eraseDups}"

/-! ## §2 — per-stage verdicts

Uncomment one at a time. -/

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

/-! ## §3 — cost of running the checker

`Cmd.costLeSize_of_capChk c allRegs (by decide)` is the intended call, and the
kernel has to *evaluate* `capChk` on the closed term. Measured:

```
S1Emit.emitBlk        1 loop        < 1 s
S1CardEmit.cCopy     15 loops       ~ 1 s
S1CardEmit.cFive     81 loops       ~ 8 s
S1Program.s1Program  116825 loops    19 s   ← SHORT-CIRCUITS, see below
S1Prelude.cPrelude    (the deep nest)  > 10 min, both `#eval` and `decide`
```

⚠ **The 19 s figure is not what it looks like.** `Option.bind` in `capChk`'s
`seq` case stops at the first `none`, and `stepFam` — which sits *before*
`cPrelude` in `stageC` — is where the analysis fails. So the whole-program run
never reaches the expensive family. A *successful* whole-program run has not
been timed and, on the `cPrelude` evidence, will not be fast as the checker
stands.

**The remedy is mechanical**, and should be done before the analysis is made
more precise: `capChk` recomputes `Cmd.writes` over the whole subtree at every
enclosing loop, and runs `Cmd.GrowOk` once per candidate register (up to 60) per
loop. Represent register sets as a `Nat` bitmask — `Nat.testBit` / `|||` /
`&&&` are GMP-accelerated in the kernel and every register is `< 64` — and hoist
`Cmd.writes` to one computation per node. -/

example : (Cmd.capChk allRegs (S1Emit.emitBlk 43 37 34)).isSome = true := by decide

example : (Cmd.capChk allRegs S1CardEmit.cFive).isSome = true := by decide

/-- The residual, machine-checked: the analysis as it stands rejects `stepFam`.
When the merged flow-sensitive pass lands (HANDOFF, NEXT BOTTOM-UP) this example
must be deleted, not flipped. -/
example : (Cmd.capChk allRegs S1Step.stepFam).isSome = false := by decide

end S1GrowSafeProbe
