import Complexity.Lang.Compile

-- NOT built by lake (parked/). Run with:
--   env LEAN_PATH=$(lake env printenv LEAN_PATH) lean parked/ProbeHead.lean
-- Probe run 2026-06-10 (pre-proof validation of `Compile.opHead`): all 7
-- cases match. Kept as the probe template for future Class-A ops.

open Complexity.Lang

-- probe: run the compiled head machine end-to-end on real encoded tapes.
def probeHead (dst src : Var) (s : State) (res : List Nat) (n : Nat) :
    Option (Nat × List (List Nat × Nat × List Nat)) :=
  let cc := Compile.opHead dst src
  (runFlatTM n cc.M (initFlatConfig cc.M [Compile.encodeTape s ++ res])).map
    (fun c => (c.state_idx, c.tapes))

def expectHead (dst src : Var) (s : State) (res : List Nat) : (Nat × List Nat) :=
  let out := Op.eval (Op.head dst src) s
  ((Compile.opHead dst src).exit,
   Compile.encodeTape out ++ (res ++ List.replicate (State.get s dst).length 0))

-- 1. src nonempty bit0, dst ≠ src
#eval probeHead 1 0 [[0,1],[1]] [] 2000
#eval expectHead 1 0 [[0,1],[1]] []
-- 2. src nonempty bit1, dst empty
#eval probeHead 1 0 [[1,0],[]] [] 2000
#eval expectHead 1 0 [[1,0],[]] []
-- 3. src empty
#eval probeHead 1 0 [[],[1,1]] [] 2000
#eval expectHead 1 0 [[],[1,1]] []
-- 4. dst = src, nonempty bit1
#eval probeHead 0 0 [[1,0]] [] 2000
#eval expectHead 0 0 [[1,0]] []
-- 5. dst = src, empty
#eval probeHead 0 0 [[]] [] 2000
#eval expectHead 0 0 [[]] []
-- 6. with input residue + later registers
#eval probeHead 2 1 [[1],[0,0],[1,1],[]] [0,0] 2000
#eval expectHead 2 1 [[1],[0,0],[1,1],[]] [0,0]
-- 7. src nonempty bit0, src after dst
#eval probeHead 0 1 [[1,1],[0]] [] 2000
#eval expectHead 0 1 [[1,1],[0]] []
