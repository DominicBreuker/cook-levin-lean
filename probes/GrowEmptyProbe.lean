import Complexity.Lang.Compile
open Complexity.Lang

/-! # Residue-tolerant `growEmpty` gadget design probe (bottom-up, 2026-06-16, d2c)

Validates the `eqBit` scratch-lifecycle **grow** gadget BEFORE proving its run
lemma. The gadget appends one empty register at the END of the register list,
**tolerating a terminator-free residue** to the right of the trailing terminator.

Design (HANDOFF d2c): reuse `padBody`'s forward part
`stepRightTM ⨾ scanRightUntilTM 4 3 ⨾ insertCarryTM 0` (residue-tolerant: scan
stops at the trailing `3` BEFORE the residue; insert shifts `[3] ++ res` right by
one, head ends PAST the residue), then a **two-phase** rewind (`rewindTwoPhaseTM`)
to get the head back to `0` past the trailing `3`. (Single-phase rewind is WRONG
with residue: `insertCarryTM` parks the head past the residue, and a single
left-scan stops at the trailing `3`, not the leading sentinel.) -/

namespace GrowEmptyProbe

open Complexity.Lang.ScanLeft Complexity.Lang.ShiftTape TMPrimitives

/-- The forward "insert one empty register at the end" machine (no rewind). -/
def growInsertM : FlatTM :=
  composeFlatTM (stepRightTM 4)
    (composeFlatTM (scanRightUntilTM 4 3) (insertCarryTM 0) 1) 1

/-- Full grow: forward insert ⨾ two-phase rewind (raw, boundary halt not demoted). -/
def growRawM : FlatTM :=
  composeFlatTM growInsertM (rewindTwoPhaseTM 4 3) 10

/-- A sample state: register 0 = a 3-bit unary block, plus 2 empty registers. -/
def sampleState : State := [List.replicate 3 1, [], []]

/-- A terminator-free residue (cells `< 4`, none `= 3`). -/
def sampleRes : List Nat := [0, 1, 2, 0]

partial def stepsToHalt (M : FlatTM) (cfg : FlatTMConfig) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
      if haltingStateReached M cfg then 0
      else match stepFlatTM M cfg with
        | none => 0
        | some cfg' => stepsToHalt M cfg' fuel + 1

/-- Run `M` to its halt (or fuel) and return the resulting config. -/
partial def runToHalt (M : FlatTM) (cfg : FlatTMConfig) (fuel : Nat) : FlatTMConfig :=
  match fuel with
  | 0 => cfg
  | fuel + 1 =>
      if haltingStateReached M cfg then cfg
      else match stepFlatTM M cfg with
        | none => cfg
        | some cfg' => runToHalt M cfg' fuel

def startCfg (M : FlatTM) (s : State) (res : List Nat) : FlatTMConfig :=
  { state_idx := M.start, tapes := [([], 0, Compile.encodeTape s ++ res)] }

/-! ## State-count sanity (expect `growInsertM.states = 11`, exit `10`). -/
#eval growInsertM.states            -- expect 11
#eval (rewindTwoPhaseTM 4 3).states -- expect 8

/-! ## Forward insert: where does the head land, and is the tape right? -/

-- expected tape: encodeTape (sampleState ++ [[]]) ++ sampleRes ; head at the END.
#eval (runToHalt growInsertM (startCfg growInsertM sampleState sampleRes) 200)
#eval Compile.encodeTape (sampleState ++ [[]]) ++ sampleRes
#eval (runToHalt growInsertM (startCfg growInsertM sampleState sampleRes) 200).state_idx -- expect 10

/-! ## Full grow (raw, with two-phase rewind): head back to `0`, tape grown. -/

-- expect: state 16 (= 10 + 6, the two-phase "found" halt), head 0, tape grown.
#eval (runToHalt growRawM (startCfg growRawM sampleState sampleRes) 400)

/-- **The verdict.** Full grow yields head `0` + `encodeTape (s ++ [[]]) ++ res`. -/
def growCorrect (s : State) (res : List Nat) : Bool :=
  let out := runToHalt growRawM (startCfg growRawM s res) 400
  out.tapes == [([], 0, Compile.encodeTape (s ++ [[]]) ++ res)]

#eval growCorrect sampleState sampleRes          -- expect true
#eval growCorrect sampleState []                 -- expect true (empty residue)
#eval growCorrect [List.replicate 5 1, []] [1,1] -- expect true

/-! ## Step count is linear in tape length (grow is O(L)). -/
#eval stepsToHalt growRawM (startCfg growRawM sampleState sampleRes) 400
#eval (Compile.encodeTape sampleState ++ sampleRes).length

end GrowEmptyProbe
