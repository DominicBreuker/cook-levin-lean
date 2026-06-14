import Complexity.Lang.Compile
open Complexity.Lang TMPrimitives

/-! # `compareRegsTM` consume-loop body probe (bottom-up, 2026-06-14c)

Validate, end-to-end by `#eval`, the consume-loop body `B` of design (A): per
iteration, ITERATE (delete both heads) while *both scratch regs nonempty AND
heads equal*; DONE otherwise. We build `B` from proven gadgets, then DRIVE it
manually (run to halt; if the tape changed = a pair was consumed, re-enter;
else stop) and check the result matches the abstract consume.

This validates the WIRING (nested `branchComposeFlatTM`/`composeFlatTM` over
`navigateAndTestTM`/`bitReadTM`/`opTail`/`justRewindTM`) before we port the
machine into `Compile.lean` and prove its `loopTM` run lemma. -/

namespace CompareBodyProbe

abbrev nav (s : Nat) : FlatTM := ClearGadget.navigateAndTestTM s
abbrev navc (s : Nat) : Nat := ClearGadget.navigateAndTestTM_exit_content s
abbrev navd (s : Nat) : Nat := ClearGadget.navigateAndTestTM_exit_delim s
abbrev rew : FlatTM := ClearGadget.justRewindTM
abbrev rewE : Nat := ClearGadget.justRewindTM_exit
abbrev br : FlatTM := Compile.bitReadTM
abbrev b0 : Nat := Compile.bitReadTM_exit_b0
abbrev b1 : Nat := Compile.bitReadTM_exit_b1
abbrev tail (s : Nat) : FlatTM := (Compile.opTail s s).M
abbrev tailE (s : Nat) : Nat := (Compile.opTail s s).exit

/-- rewind to head 0, then run `M` from its start. -/
def rewindThen (M : FlatTM) : FlatTM := composeFlatTM rew M rewE

/-- ITERATE: rewind ⨾ tail sc1 ⨾ tail sc2 (each `opTail` ends at head 0). -/
def iterTails (sc1 sc2 : Nat) : FlatTM :=
  rewindThen (composeFlatTM (tail sc1) (tail sc2) (tailE sc1))

/-- DONE: just rewind to head 0. -/
def doneM : FlatTM := rew

/-- given `bit_a` known, branch on `bit_b`: ITERATE iff bits match. -/
def cmpA0 (sc1 sc2 : Nat) : FlatTM := branchComposeFlatTM br (iterTails sc1 sc2) doneM b0 b1  -- a=0
def cmpA1 (sc1 sc2 : Nat) : FlatTM := branchComposeFlatTM br doneM (iterTails sc1 sc2) b0 b1  -- a=1

/-- from head 0: navtest sc2 (content) ⨾ read its bit ⨾ `cmp`. -/
def readSc2 (sc2 : Nat) (cmp : FlatTM) : FlatTM := composeFlatTM (nav sc2) cmp (navc sc2)

/-- after reading `bit_a` (head still on sc1): rewind ⨾ read sc2's bit ⨾ compare. -/
def afterBitA (sc2 : Nat) (cmp : FlatTM) : FlatTM := rewindThen (readSc2 sc2 cmp)

/-- from head on sc1's content: read `bit_a`, branch. -/
def bitAbranch (sc1 sc2 : Nat) : FlatTM :=
  branchComposeFlatTM br (afterBitA sc2 (cmpA0 sc1 sc2)) (afterBitA sc2 (cmpA1 sc1 sc2)) b0 b1

/-- from head 0: navtest sc1 (content) ⨾ read bit_a ⨾ … -/
def readSc1 (sc1 sc2 : Nat) : FlatTM := composeFlatTM (nav sc1) (bitAbranch sc1 sc2) (navc sc1)

/-- both nonempty: rewind ⨾ read sc1 then sc2 ⨾ compare. -/
def bothNonempty (sc1 sc2 : Nat) : FlatTM := rewindThen (readSc1 sc1 sc2)

/-- sc1 nonempty (head on sc1 content): rewind ⨾ navtest sc2 (content→compare, delim→DONE). -/
def contentBranch (sc1 sc2 : Nat) : FlatTM :=
  rewindThen (branchComposeFlatTM (nav sc2) (bothNonempty sc1 sc2) doneM (navc sc2) (navd sc2))

/-- **The consume-loop body.** navtest sc1: content → `contentBranch`, delim → DONE. -/
def B (sc1 sc2 : Nat) : FlatTM :=
  branchComposeFlatTM (nav sc1) (contentBranch sc1 sc2) doneM (navc sc1) (navd sc1)

/-! ## Driver -/

partial def runToHalt (M : FlatTM) (right : List Nat) (fuel : Nat) : List Nat :=
  let cfg := runFlatTM fuel M { state_idx := M.start, tapes := [([], 0, right)] }
  ((cfg.getD { state_idx := 0, tapes := [] }).tapes.headD ([], 0, [])).2.2

partial def driveLoop (M : FlatTM) (right : List Nat) (rounds fuel : Nat) : List Nat :=
  match rounds with
  | 0 => right
  | rounds + 1 =>
      let right' := runToHalt M right fuel
      if right' = right then right else driveLoop M right' rounds fuel

def consumeOnTape (data1 data2 : List Nat) : State :=
  let s : State := [data1, data2]
  let M := B 0 1
  let start := Compile.encodeTape s
  let fuel := 50 * (start.length + 2) * (start.length + 2)
  let final := driveLoop M start (data1.length + data2.length + 2) fuel
  Compile.decodeTape { state_idx := 0, tapes := [([], 0, final)] }

def consumeAbstract : List Nat → List Nat → (List Nat × List Nat)
  | [], r2 => ([], r2)
  | r1, [] => (r1, [])
  | a :: r1, b :: r2 => if a = b then consumeAbstract r1 r2 else (a :: r1, b :: r2)

def expected (data1 data2 : List Nat) : List (List Nat) :=
  let (s1, s2) := consumeAbstract data1 data2
  [s1, s2]

def check (data1 data2 : List Nat) : Bool :=
  consumeOnTape data1 data2 == expected data1 data2

-- equal lists → both fully consumed to []
#eval check [1,0,1] [1,0,1]
#eval check [] []
#eval check [1] [1]
-- bit mismatch → stop at first differing position
#eval check [1,0] [1,1]
#eval check [0,1,1] [0,0,1]
-- length mismatch → shorter empties, prefix consumed
#eval check [1,0] [1,0,1]
#eval check [1,0,1] [1,0]
#eval check [1] []
#eval check [] [1]
#eval check [0,0,0] [0,0,0]
#eval check [1,1,0,1] [1,1,1,1]

end CompareBodyProbe
