import Complexity.Lang.Compile
open Complexity.Lang

/-! # `eqBit` Resolution-B (no-grow, pre-existing scratch) assembly probe (bottom-up, 2026-06-21b)

**Why this probe exists.** The 2026-06-21b bottom-up session found that the d2
`compareRegsTM` stack is un-instantiable into the position-fixed `opEqBit`: it
addresses scratch by the runtime index `sc1 = s.length` (grow-at-end), but
`compileOp : Op → CompiledCmd` builds a machine fixed by `dst/src1/src2` only.
The fix (Resolution B, HANDOFF) mirrors `forBnd`: thread a static scratch base
`sb` into `compileOp`, and use **pre-existing PADDED scratch** at the fixed
compile-time indices `sb`, `sb+1` — so **no `growTwoEmpty`/`shrinkTwoEmpty`**.

This probe validates, by `#eval` (before any proof engineering), that the no-grow
assembly DECIDES equality and RESTORES the tape, exactly as Resolution B needs.
It feeds each PROVEN stage's machine forward (the chain the no-grow run lemma
will prove):

  copyEmpty src1→sb ⨾ copyEmpty src2→(sb+1) ⨾ compareLoop sb (sb+1)
    ⨾ [verdict reads sb/(sb+1)] ⨾ clear sb ⨾ clear (sb+1)

with `sb`, `sb+1` PRE-EXISTING EMPTY registers in the input state (the precondition
the contract supplies via `hscratch` + the reserved padding). All `true` ⟹ Res B
assembles correctly; the remaining work is the seam-threading proof + the
`compileOp`-scratch-base / padding redesign (top-down task 0b).

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/EqBitNoGrowProbe.lean`
-/

namespace EqBitNoGrowProbe

partial def runToHalt (M : FlatTM) (cfg : FlatTMConfig) (fuel : Nat) : Option FlatTMConfig :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if haltingStateReached M cfg then some cfg
      else match stepFlatTM M cfg with
        | none => none
        | some cfg' => runToHalt M cfg' fuel

def stageTape (M : FlatTM) (tape : List Nat) (fuel : Nat) : Option (List Nat) :=
  match runToHalt M { state_idx := 0, tapes := [([], 0, tape)] } fuel with
  | some cfg => match cfg.tapes with
                | (_, _, r) :: _ => some r
                | _ => none
  | none => none

def bigFuel : Nat := 2000000

def dec (r : List Nat) : State :=
  Compile.decodeTape { state_idx := 0, tapes := [([], 0, r)] }

/-- A state whose registers `0 .. nreal-1` are the real program registers and
whose registers `sb = nreal`, `sb+1 = nreal+1` are PRE-EXISTING EMPTY scratch
(plus an optional trailing empty, to model deeper padding). -/
def st (reals : List (List Nat)) (extra : Nat) : State :=
  reals ++ [[], []] ++ List.replicate extra []

/-- Run the no-grow pipeline at the machine level on a state with pre-existing
empty scratch at `sb = reals.length`, `sb+1`. Compares registers `src1`, `src2`
(both `< sb`). Returns `(bothEmptyAfterLoop, restoredOK)`. -/
def pipeline (reals : List (List Nat)) (extra : Var) (src1 src2 : Var) :
    Option (Bool × Bool) := do
  let s0 := st reals extra
  let sb := reals.length
  -- stage 1: copy src1 → sb (sb pre-existing empty)
  let t1 ← stageTape (Compile.copyEmptyRawTM sb src1) (Compile.encodeTape s0) bigFuel
  -- stage 2: copy src2 → sb+1
  let t2 ← stageTape (Compile.copyEmptyRawTM (sb + 1) src2) t1 bigFuel
  -- stage 3: compare loop (consume matched prefix of sb / sb+1)
  let t3 ← stageTape (Compile.compareLoopTM sb (sb + 1)) t2 bigFuel
  -- verdict: read sb / (sb+1) emptiness from the decode
  let decoded := dec t3
  let bothEmpty := (decoded.getD sb [] == []) && (decoded.getD (sb + 1) [] == [])
  -- stage 4: cleanup — clear sb, clear (sb+1) (restore scratch to empty)
  let t4 ← stageTape (ClearGadget.clearRegionTM sb) t3 bigFuel
  let t5 ← stageTape (ClearGadget.clearRegionTM (sb + 1)) t4 bigFuel
  -- restored iff decoding the final tape matches decoding the original
  let restoredOK := dec t5 == dec (Compile.encodeTape s0)
  some (bothEmpty, restoredOK)

def checkEQ (reals : List (List Nat)) (extra src1 src2 : Var) : Bool :=
  match pipeline reals extra src1 src2 with
  | some (bothEmpty, restoredOK) => bothEmpty && restoredOK
  | none => false

def checkNEQ (reals : List (List Nat)) (extra src1 src2 : Var) : Bool :=
  match pipeline reals extra src1 src2 with
  | some (bothEmpty, restoredOK) => (!bothEmpty) && restoredOK
  | none => false

/-! ## EQ inputs: src1 = src2 (compare registers 0 and 1, which are equal). -/

#eval checkEQ [[1,0,1], [1,0,1]] 0 0 1          -- equal, length 3, no extra padding
#eval checkEQ [[], []] 0 0 1                      -- both empty → equal
#eval checkEQ [[1,1,0,0], [1,1,0,0], [1]] 2 0 1 -- equal, extra real reg + 2 padding
#eval checkEQ [[0], [0]] 1 0 1                    -- single bit equal, 1 extra padding

/-! ## NEQ inputs: src1 ≠ src2. -/

#eval checkNEQ [[1,0], [1,1]] 0 0 1              -- bit mismatch
#eval checkNEQ [[1,0], [1,0,1]] 0 0 1            -- prefix (length) mismatch
#eval checkNEQ [[1,0,1], [1,0]] 0 0 1           -- the other length mismatch
#eval checkNEQ [[1], []] 0 0 1                    -- one empty
#eval checkNEQ [[], [0]] 1 0 1                    -- other empty

/-! ## Comparing non-adjacent real registers (src1, src2 not 0/1). -/

#eval checkEQ [[1,1], [0], [1,1], [0,0,1]] 1 0 2   -- reg0 = reg2 (equal)
#eval checkNEQ [[1,1], [0], [1,0], [0,0,1]] 1 0 2  -- reg0 ≠ reg2

/-! ## Visual: final decoded tape for one EQ + one NEQ (scratch restored to empty). -/

#eval (pipeline [[1,0,1], [1,0,1]] 1 0 1).map (fun (b, r) => (b, r))
#eval (pipeline [[1,0], [1,1]] 1 0 1).map (fun (b, r) => (b, r))
#eval dec (Compile.encodeTape (st [[1,0,1],[1,0,1]] 1))  -- original (trailing empties trimmed)

end EqBitNoGrowProbe
