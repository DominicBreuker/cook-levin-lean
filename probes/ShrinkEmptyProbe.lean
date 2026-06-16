import Complexity.Lang.Compile
open Complexity.Lang

/-! # Residue-tolerant `shrinkEmpty` gadget validation probe (bottom-up, 2026-06-16c, d2c)

End-to-end `#eval` validation of the `eqBit` scratch-lifecycle **teardown** gadget
(`Compile.shrinkEmptyTM` / `Compile.shrinkTwoEmptyM`), the mirror of `growEmptyTM`.
It removes one (resp. two) trailing **empty** register(s), tolerating a
terminator-free residue.

Design (HANDOFF d2c-SHRINK): `stepRightTM ⨾ scanRightUntilTM 4 3 ⨾ deleteCarryTM ⨾
stepLeftTM` (navigate to the trailing terminator, delete the empty register's `0`
separator left of it, step left off the past-the-end blank) then a **two-phase**
rewind (via `rewindBracket`). Deleting a cell frees one tape slot, so the residue
grows by a single `0` per shrink (still `ValidResidue`). -/

namespace ShrinkEmptyProbe

partial def runToHalt (M : FlatTM) (cfg : FlatTMConfig) (fuel : Nat) : FlatTMConfig :=
  match fuel with
  | 0 => cfg
  | fuel + 1 =>
      if haltingStateReached M cfg then cfg
      else match stepFlatTM M cfg with
        | none => cfg
        | some cfg' => runToHalt M cfg' fuel

partial def stepsToHalt (M : FlatTM) (cfg : FlatTMConfig) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
      if haltingStateReached M cfg then 0
      else match stepFlatTM M cfg with
        | none => 0
        | some cfg' => stepsToHalt M cfg' fuel + 1

/-- A sample state: register 0 = a 3-bit unary block, plus 2 empty registers. -/
def sampleState : State := [List.replicate 3 1, [], []]
def sampleRes : List Nat := [0, 1, 2, 0]

def startCfg (M : FlatTM) (s : State) (res : List Nat) : FlatTMConfig :=
  { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }

/-! ## State-count sanity. -/
#eval Compile.shrinkComputeM.states   -- expect 14
#eval Compile.shrinkEmptyTM.exit      -- expect 20 (= 14 + 6)

/-! ## One shrink: `encodeTape (s ++ [[]]) ++ res → encodeTape s ++ (res ++ [0])`, head 0. -/

#eval (runToHalt Compile.shrinkEmptyTM.M (startCfg Compile.shrinkEmptyTM.M (sampleState ++ [[]]) sampleRes) 400)
#eval Compile.encodeTape sampleState ++ (sampleRes ++ [0])

/-- **The verdict.** One shrink yields head `0` + `encodeTape s ++ (res ++ [0])`. -/
def shrinkCorrect (s : State) (res : List Nat) : Bool :=
  let out := runToHalt Compile.shrinkEmptyTM.M (startCfg Compile.shrinkEmptyTM.M (s ++ [[]]) res) 400
  out.tapes == [([], 0, Compile.encodeTape s ++ (res ++ [0]))]
    && out.state_idx == Compile.shrinkEmptyTM.exit

#eval shrinkCorrect sampleState sampleRes            -- expect true
#eval shrinkCorrect sampleState []                   -- expect true (empty residue)
#eval shrinkCorrect [List.replicate 5 1, []] [1, 1]  -- expect true

/-! ## Two shrinks: `encodeTape (s ++ [[],[]]) ++ res → encodeTape s ++ (res ++ [0,0])`. -/

def shrinkTwoCorrect (s : State) (res : List Nat) : Bool :=
  let out := runToHalt Compile.shrinkTwoEmptyM (startCfg Compile.shrinkTwoEmptyM (s ++ [[], []]) res) 800
  out.tapes == [([], 0, Compile.encodeTape s ++ (res ++ [0, 0]))]

#eval shrinkTwoCorrect sampleState sampleRes          -- expect true
#eval shrinkTwoCorrect [List.replicate 4 1] []        -- expect true

/-! ## grow-then-shrink round-trip (identity on `s` modulo residue growth). -/
def roundTrip (s : State) (res : List Nat) : Bool :=
  -- grow two, then shrink two: tape returns to `encodeTape s ++ (res ++ [0,0])`.
  let grown := runToHalt Compile.growTwoEmptyM (startCfg Compile.growTwoEmptyM s res) 800
  match grown.tapes with
  | [([], _, t)] =>
      let out := runToHalt Compile.shrinkTwoEmptyM { state_idx := 0, tapes := [([], 0, t)] } 800
      out.tapes == [([], 0, Compile.encodeTape s ++ (res ++ [0, 0]))]
  | _ => false

#eval roundTrip sampleState sampleRes   -- expect true

/-! ## Step count is linear in tape length (shrink is O(L)). -/
#eval stepsToHalt Compile.shrinkEmptyTM.M (startCfg Compile.shrinkEmptyTM.M (sampleState ++ [[]]) sampleRes) 400
#eval (Compile.encodeTape (sampleState ++ [[]]) ++ sampleRes).length

end ShrinkEmptyProbe
