import Complexity.Lang.AcceptHalt
import Complexity.Lang.FormatCheck
import Complexity.Lang.Compile.Decider

/-! # C8-4 probe — the front machine `M_Q`, end-to-end (probe-before-prove)

The HANDOFF C8-4 plan (step 2) demands: **before proving the correctness iff,
`#eval acceptsFlatTM M_Q [s_x ++ cert] steps` on a real compiled verifier
(yes + no + garbage cert) — the whole machine story is cheaply falsifiable.**

`M_Q := composeFlatTM (formatCheckTM w) (demoteHalt (paddedBitDeciderTM c k) r) (w+6)`
with `r = 2 + (Compile k c).states + (padRegsTM (k + 2·loopDepth + 2)).states`
(the reject state from `paddedBitDecider_run`, `b = 0`), `w = xWidth`,
`k = regBound`.

Toy verifier: `c := op (nonEmpty 0 2)` — "accept iff register 2 (the cert) is
non-empty". `xWidth = 2` (input regs 0,1), `k = regBound = 3` (input has 3
registers `sx ++ [creg]`). We check:

* valid non-empty cert  → verifier accepts → `M_Q` accepts;
* valid empty cert       → verifier rejects → `M_Q` does NOT accept (parks at r);
* garbage cert (bad grammar) → format check sticks → `M_Q` does NOT accept.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/C8MachineProbe.lean`
-/

open Complexity.Lang
open Complexity.Lang.AcceptHalt (demoteHalt)
open Complexity.Lang.FormatCheck (formatCheckTM)
open TMPrimitives (composeFlatTM)

namespace C8MachineProbe

-- The toy verifier: accept iff the cert register (reg 2) is non-empty.
def cVer : Cmd := Cmd.op (Op.nonEmpty 0 2)

def xWidth : Nat := 2
def regBound : Nat := 3

-- The padded, bit-level decider for `cVer`.
def dec : FlatTM := Compile.paddedBitDeciderTM cVer regBound

-- The reject state from `paddedBitDecider_run` (`b = 0`): index `2` shifted by
-- both compositions.
def rejectState : Nat :=
  2 + (Compile regBound cVer).states
    + (Compile.padRegsTM (regBound + 2 * cVer.loopDepth + 2)).states

-- The accept-by-halting-wrapped verifier: the reject state is demoted, so the
-- machine parks (never halts) when the verifier rejects.
def M2 : FlatTM := demoteHalt dec rejectState

-- The full per-`Q` front machine.
def MQ : FlatTM := composeFlatTM (formatCheckTM xWidth) M2 (xWidth + 6)

-- Sanity: structural fields.
#eval MQ.sig            -- expect 4
#eval MQ.tapes          -- expect 1
#eval (formatCheckTM xWidth).states  -- expect w + 7 = 9
#eval rejectState

-- Build the machine input tape `(3 :: encodeRegs sx) ++ cert`.
def tapeOf (sx : State) (cert : List Nat) : List Nat :=
  (3 :: Compile.encodeRegs sx) ++ cert

-- Valid cert region for a bit register `creg`: `shiftReg creg ++ [0, 3]`.
def certOf (creg : List Nat) : List Nat := Compile.shiftReg creg ++ [0, 3]

def sx : State := [[1, 0], [1]]        -- two input registers (xWidth = 2)

def steps : Nat := 200000               -- generous budget for the probe

-- Yes-instance: non-empty cert `creg = [1]` ⇒ verifier accepts.
#eval acceptsFlatTM MQ [tapeOf sx (certOf [1])] steps        -- expect true
-- No-instance: empty cert `creg = []` ⇒ verifier rejects ⇒ parks at r.
#eval acceptsFlatTM MQ [tapeOf sx (certOf [])] steps         -- expect false
-- Garbage cert (symbol `5` ∉ {1,2}) ⇒ format check sticks.
#eval acceptsFlatTM MQ [tapeOf sx ([5, 0, 3])] steps         -- expect false
-- Garbage cert (missing trailing terminator) ⇒ format check sticks.
#eval acceptsFlatTM MQ [tapeOf sx ([2, 0])] steps            -- expect false

-- A different valid non-empty cert `creg = [0]` (a single `0` bit ⇒ cell `1`)
-- is still non-empty ⇒ accepts.
#eval acceptsFlatTM MQ [tapeOf sx (certOf [0])] steps        -- expect true

-- Sanity: the underlying (un-demoted) decider actually HALTS on the empty cert
-- (at the reject state) — so the demotion is what turns reject into park.
#eval acceptsFlatTM dec [Compile.encodeTape (sx ++ [[]])] steps  -- expect true
#eval acceptsFlatTM dec [Compile.encodeTape (sx ++ [[1]])] steps -- expect true

-- The verifier's pure output on the decoded states (ground truth).
#eval (cVer.eval (sx ++ [[1]])).get 0    -- expect [1]  (nonEmpty cert)
#eval (cVer.eval (sx ++ [[]])).get 0     -- expect [0]  (empty cert)

-- Verdict.
def probeMachine : Bool :=
  (acceptsFlatTM MQ [tapeOf sx (certOf [1])] steps == true) &&
  (acceptsFlatTM MQ [tapeOf sx (certOf [0])] steps == true) &&
  (acceptsFlatTM MQ [tapeOf sx (certOf [])] steps == false) &&
  (acceptsFlatTM MQ [tapeOf sx ([5, 0, 3])] steps == false) &&
  (acceptsFlatTM MQ [tapeOf sx ([2, 0])] steps == false)

#eval probeMachine   -- the C8-4 machine verdict; expect true

end C8MachineProbe
