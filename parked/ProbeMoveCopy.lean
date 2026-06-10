import Complexity.Lang.Compile

-- NOT built by lake (parked/). Run with:
--   env LEAN_PATH=$(lake env printenv LEAN_PATH) lean parked/ProbeMoveCopy.lean
-- Probe run 2026-06-10: ALL 6 cases match (exit state, head 0, exact tape
-- `encodeTape output ++ zero residue`). This file is the validated machine
-- architecture for the Class-B ops -- build `moveRegTM`/`dupRegTM` in
-- `Compile.lean` from these exact definitions.

/-! # Probe: counter-free block move/copy (Class-B go/no-go)

`move tgt src`: loop { navtest src: delim -> done; content -> read bit value
(eqTestTM), stepDeleteRewind (delete src's front cell, rewind), appendAtRewind
(append the bit at tgt's end, rewind) }. Terminates because src shrinks (the
clear-loop termination shape) -- NO unary counter needed.

`copy dst src sc` (sc an empty scratch): clear dst ; move sc src ;
dupMove (src,dst) sc  -- the dup phase appends each bit to BOTH src and dst,
restoring src and writing dst, terminating on sc.
-/

open Complexity.Lang
open TMPrimitives

-- delete src's front cell (head on src content start) + rewind, then append
-- bit `ins` at register tgt's end + rewind.
def moveBitBody (ins : Nat) (h : ins < 4) (tgt : Var) : FlatTM :=
  composeFlatTM ClearGadget.stepDeleteRewindRawTM (Compile.opAppendBitRewind ins h tgt).M 17

def moveBitBody_exit (ins : Nat) (h : ins < 4) (tgt : Var) : Nat :=
  ClearGadget.stepDeleteRewindRawTM.states + (Compile.opAppendBitRewind ins h tgt).exit

-- the two-bit-value branch (raw, two exits), then merged.
def moveContentRaw (tgt : Var) : FlatTM :=
  branchComposeFlatTM (ClearGadget.eqTestTM 4 2)
    (moveBitBody 2 (by decide) tgt) (moveBitBody 1 (by decide) tgt)
    ClearGadget.eqTestTM_exit_eq ClearGadget.eqTestTM_exit_ne

def moveContentRaw_h1 (tgt : Var) : Nat :=
  (ClearGadget.eqTestTM 4 2).states + moveBitBody_exit 2 (by decide) tgt
def moveContentRaw_h2 (tgt : Var) : Nat :=
  (ClearGadget.eqTestTM 4 2).states + (moveBitBody 2 (by decide) tgt).states
    + moveBitBody_exit 1 (by decide) tgt

def moveContent (tgt : Var) : FlatTM :=
  Compile.joinTwoHalts (moveContentRaw tgt) (moveContentRaw_h1 tgt) (moveContentRaw_h2 tgt)

-- the loop body: navtest src -> content: moveContent | delim: justRewind.
def moveBodyRaw (src tgt : Var) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
    (moveContent tgt) ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content src)
    (ClearGadget.navigateAndTestTM_exit_delim src)

def moveBody_exitLoop (src tgt : Var) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + moveContentRaw_h1 tgt
def moveBody_exitDone (src tgt : Var) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (moveContent tgt).states
    + ClearGadget.justRewindTM_exit

def moveRegTM (src tgt : Var) : FlatTM :=
  loopTM (moveBodyRaw src tgt) (moveBody_exitDone src tgt) (moveBody_exitLoop src tgt)

def moveRegTM_exit (src tgt : Var) : Nat := (moveBodyRaw src tgt).states

-- ## dup phase: append each bit to TWO targets (restores src, writes dst).
def dupBitBody (ins : Nat) (h : ins < 4) (tgt1 tgt2 : Var) : FlatTM :=
  composeFlatTM (moveBitBody ins h tgt1) (Compile.opAppendBitRewind ins h tgt2).M
    (moveBitBody_exit ins h tgt1)

def dupBitBody_exit (ins : Nat) (h : ins < 4) (tgt1 tgt2 : Var) : Nat :=
  (moveBitBody ins h tgt1).states + (Compile.opAppendBitRewind ins h tgt2).exit

def dupContentRaw (tgt1 tgt2 : Var) : FlatTM :=
  branchComposeFlatTM (ClearGadget.eqTestTM 4 2)
    (dupBitBody 2 (by decide) tgt1 tgt2) (dupBitBody 1 (by decide) tgt1 tgt2)
    ClearGadget.eqTestTM_exit_eq ClearGadget.eqTestTM_exit_ne

def dupContentRaw_h1 (tgt1 tgt2 : Var) : Nat :=
  (ClearGadget.eqTestTM 4 2).states + dupBitBody_exit 2 (by decide) tgt1 tgt2
def dupContentRaw_h2 (tgt1 tgt2 : Var) : Nat :=
  (ClearGadget.eqTestTM 4 2).states + (dupBitBody 2 (by decide) tgt1 tgt2).states
    + dupBitBody_exit 1 (by decide) tgt1 tgt2

def dupContent (tgt1 tgt2 : Var) : FlatTM :=
  Compile.joinTwoHalts (dupContentRaw tgt1 tgt2) (dupContentRaw_h1 tgt1 tgt2)
    (dupContentRaw_h2 tgt1 tgt2)

def dupBodyRaw (src tgt1 tgt2 : Var) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
    (dupContent tgt1 tgt2) ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content src)
    (ClearGadget.navigateAndTestTM_exit_delim src)

def dupBody_exitLoop (src tgt1 tgt2 : Var) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + dupContentRaw_h1 tgt1 tgt2
def dupBody_exitDone (src tgt1 tgt2 : Var) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (dupContent tgt1 tgt2).states
    + ClearGadget.justRewindTM_exit

def dupRegTM (src tgt1 tgt2 : Var) : FlatTM :=
  loopTM (dupBodyRaw src tgt1 tgt2) (dupBody_exitDone src tgt1 tgt2)
    (dupBody_exitLoop src tgt1 tgt2)

-- ## full copy: clear dst ; move sc src ; dup (src,dst) sc.
def copyRegTM (dst src sc : Var) : FlatTM :=
  composeFlatTM
    (composeFlatTM (ClearGadget.clearRegionTM dst) (moveRegTM src sc)
      (ClearGadget.clearRegionTM_exit dst))
    (dupRegTM sc src dst)
    ((ClearGadget.clearRegionTM dst).states + moveRegTM_exit src sc)

def copyRegTM_exit (dst src sc : Var) : Nat :=
  (ClearGadget.clearRegionTM dst).states + (moveRegTM src sc).states
    + (dupBodyRaw sc src dst).states

-- ## probes
def probeM (M : FlatTM) (s : State) (res : List Nat) (n : Nat) :
    Option (Nat × List (List Nat × Nat × List Nat)) :=
  (runFlatTM n M (initFlatConfig M [Compile.encodeTape s ++ res])).map
    (fun c => (c.state_idx, c.tapes))

-- move: s = [[1,0,1],[]] src 0 -> tgt 1; expect [[],[1,0,1]]
#eval probeM (moveRegTM 0 1) [[1,0,1],[]] [] 100000
#eval (moveRegTM_exit 0 1, Compile.encodeTape [[],[1,0,1]])
-- move backwards (tgt before src): s = [[],[0,1]] src 1 -> tgt 0; expect [[0,1],[]]
#eval probeM (moveRegTM 1 0) [[],[0,1]] [] 100000
#eval (moveRegTM_exit 1 0, Compile.encodeTape [[0,1],[]])
-- move with empty src: no-op
#eval probeM (moveRegTM 0 1) [[],[1]] [] 100000
#eval (moveRegTM_exit 0 1, Compile.encodeTape [[],[1]])

-- full copy: s = [[1,0],[1,1],[]] copy dst=1 src=0 sc=2; expect [[1,0],[1,0],[]]
#eval probeM (copyRegTM 1 0 2) [[1,0],[1,1],[]] [] 1000000
#eval (copyRegTM_exit 1 0 2, Compile.encodeTape [[1,0],[1,0],[]])
-- copy onto empty dst, with input residue
#eval probeM (copyRegTM 2 0 1) [[0,1,1],[],[1]] [0,0] 1000000
#eval (copyRegTM_exit 2 0 1, Compile.encodeTape [[0,1,1],[],[0,1,1]])
-- copy of empty src
#eval probeM (copyRegTM 1 0 2) [[],[1,1],[]] [] 1000000
#eval (copyRegTM_exit 1 0 2, Compile.encodeTape [[],[],[]])
