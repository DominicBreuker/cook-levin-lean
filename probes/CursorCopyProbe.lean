import Complexity.Lang.Compile

/-! # Cursor-copy op gadget probe (bottom-up, 2026-06-11)

`#eval` end-to-end validation of the pinned in-place **marking/cursor-read**
design for the `copy`/`tail` op gadgets (HANDOFF bottom-up task 1) BEFORE any
proof engineering. The design under test (`copy dst src`, `dst ≠ src`):

  clearRegionTM dst ⨾ navigateToRegTM src ⨾ loopTM(cursor body) ⨾ justRewind

where the cursor body, started with the head ON the next unprocessed cell of
`src`, reads it: `0` (delimiter) → DONE exit; bit `b` (cell `b+1`) → overwrite
with the mark `3`, rewind left to the sentinel, `appendAtTM (b+1) dst`, return
to the mark by scan-left-from-the-end (trailing terminator, step left, mark),
restore `b+1`, step right onto the next cursor → ITERATE exit.

Residue: exactly `clear dst`'s `replicate |dst₀| 0` — the cursor loop adds NONE
(insertions grow the encoded region, the mark is restored in place).

Also probed: the in-place `tail dst dst` (one clear-style delete of the head
cell — `clearBodyRawTM` with both exits kept) and the general `tail dst src`
(`dst ≠ src`: clear ⨾ nav ⨾ skip-first-cell ⨾ the same cursor loop ⨾ rewind). -/

open TMPrimitives
open Complexity.Lang
open Complexity.Lang.ScanLeft
open Complexity.Lang.ClearGadget
open Complexity.Lang.AppendGadget

def mkE1 (s : Nat) (sym : Option Nat) (d : Nat) (w : Option Nat) (mv : TMMove) :
    FlatTMTransEntry :=
  { src_state := s, src_tape_vals := [sym], dst_state := d,
    dst_write_vals := [w], move_dirs := [mv] }

/-- `(machine, exit)` sequential composition. -/
def cseq : (FlatTM × Nat) → (FlatTM × Nat) → (FlatTM × Nat)
  | (m1, e1), (m2, e2) => (composeFlatTM m1 m2 e1, m1.states + e2)

/-- The REAL compiled `copy` machine (`Compile.opCopy`, now defined in
`Compile.lean` with the nested delimTest/markBit branch structure); the probe
runs it end-to-end. -/
def copyRegionTM (dst src : Nat) : FlatTM × Nat :=
  ((Compile.opCopy dst src).M, (Compile.opCopy dst src).exit)

/-- The real cursor loop, probed in isolation too (against `copyLoop_run`'s
statement shapes). -/
def copyLoopTM (dst : Nat) : FlatTM := Compile.copyLoopTM dst

/-! ## Tail machines -/

/-- In-place `tail dst dst`: exactly ONE clear-style iteration — navigate+test,
content → step-right + delete-left-cell + two-phase rewind; delimiter →
just-rewind. `clearBodyRawTM` IS this machine; we join its two live exits
(content exit `exitLoop` demoted into the kept `exitDone`). The boundary halts
(`stepDeleteRewindRawTM`'s 18-shift, `justRewindTM`'s reject) are unreachable
on valid tapes; they stay halt states here (probe tolerates; the real
`CompiledCmd` will demote them too for `halt_unique`). -/
def tailInPlaceTM (dst : Nat) : FlatTM :=
  Compile.joinTwoHalts (clearBodyRawTM dst)
    (clearBodyRawTM_exitDone dst) (clearBodyRawTM_exitLoop dst)

def tailInPlace_exit (dst : Nat) : Nat := clearBodyRawTM_exitDone dst

/-- Skip the first cell of `src`: `0` → exit 1 (src empty); bit → step right,
exit 2. -/
def skipReadTM : FlatTM where
  sig := 4
  tapes := 1
  states := 3
  trans := [mkE1 0 (some 0) 1 none .Nmove,
            mkE1 0 (some 1) 2 none .Rmove,
            mkE1 0 (some 2) 2 none .Rmove]
  start := 0
  halt := [false, true, true]

/-- Trivial immediate-halt machine (empty-src branch body). -/
def idTM : FlatTM where
  sig := 4
  tapes := 1
  states := 1
  trans := []
  start := 0
  halt := [true]

/-- `tail dst src` (`dst ≠ src`): clear ⨾ nav ⨾ skip-first ⨾ cursor loop ⨾ rewind. -/
def tailBranchRawTM (dst : Nat) : FlatTM :=
  branchComposeFlatTM skipReadTM (copyLoopTM dst) idTM 2 1

def tailBranch_loopExit (dst : Nat) : Nat := 3 + Compile.copyLoopTM_exit dst
def tailBranch_emptyExit (dst : Nat) : Nat := 3 + (copyLoopTM dst).states

def tailBranchTM (dst : Nat) : FlatTM :=
  Compile.joinTwoHalts (tailBranchRawTM dst)
    (tailBranch_loopExit dst) (tailBranch_emptyExit dst)

def tailRegionTM (dst src : Nat) : FlatTM × Nat :=
  cseq (cseq (cseq
    (clearRegionTM dst, clearRegionTM_exit dst)
    (navigateToRegTM src, navigateToRegTM_exit src))
    (tailBranchTM dst, tailBranch_loopExit dst))
    (justRewindTM, 1)

/-! ## Probe runner -/

/-- Step to the first halting state, counting steps. -/
def stepsToHalt (M : FlatTM) : Nat → FlatTMConfig → Nat → Option (Nat × FlatTMConfig)
  | 0, _, _ => none
  | fuel + 1, cfg, t =>
      if haltingStateReached M cfg then some (t, cfg)
      else match stepFlatTM M cfg with
        | none => none
        | some c => stepsToHalt M fuel c (t + 1)

/-- Check a machine against an expected exit state + exit tape (head 0):
returns `(ok, steps, state_idx, tape)`. -/
def chk (Me : FlatTM × Nat) (input expected : List Nat) (fuel : Nat := 100000) :
    Bool × Nat × Nat × List (List Nat × Nat × List Nat) :=
  match stepsToHalt Me.1 fuel (initFlatConfig Me.1 [input]) 0 with
  | some (t, c) =>
      (c.state_idx == Me.2 && c.tapes == [([], 0, expected)], t, c.state_idx, c.tapes)
  | none => (false, 0, 999999, [])

def expectCopy (dst src : Nat) (s : State) (res : List Nat) : List Nat :=
  Compile.encodeTape (State.set s dst (State.get s src))
    ++ res ++ List.replicate (State.get s dst).length 0

def chkCopy (dst src : Nat) (s : State) (res : List Nat) :
    Bool × Nat × Nat × List (List Nat × Nat × List Nat) :=
  chk (copyRegionTM dst src) (Compile.encodeTape s ++ res) (expectCopy dst src s res)

def expectTail (dst src : Nat) (s : State) (res : List Nat) : List Nat :=
  Compile.encodeTape (State.set s dst (State.get s src).tail)
    ++ res ++ List.replicate (State.get s dst).length 0

def chkTail (dst src : Nat) (s : State) (res : List Nat) :
    Bool × Nat × Nat × List (List Nat × Nat × List Nat) :=
  chk (tailRegionTM dst src) (Compile.encodeTape s ++ res) (expectTail dst src s res)

/-- in-place tail: residue grows by `[0]` iff `dst` nonempty. -/
def expectTailIP (dst : Nat) (s : State) (res : List Nat) : List Nat :=
  Compile.encodeTape (State.set s dst (State.get s dst).tail)
    ++ res ++ (if (State.get s dst).isEmpty then [] else [0])

def chkTailIP (dst : Nat) (s : State) (res : List Nat) :
    Bool × Nat × Nat × List (List Nat × Nat × List Nat) :=
  chk (tailInPlaceTM dst, tailInPlace_exit dst)
    (Compile.encodeTape s ++ res) (expectTailIP dst s res)

/-! ## copy probes (expect `.1 = true` everywhere) -/

-- 1. dst BEFORE src (insertion shifts the mark)
#eval chkCopy 0 1 [[1, 0], [1, 1, 0]] []
-- 2. dst AFTER src (navigation to dst crosses the mark)
#eval chkCopy 1 0 [[1, 0], [1, 1, 0]] []
-- 3. empty src (zero iterations)
#eval chkCopy 0 1 [[1, 0], []] []
-- 4. empty initial dst (no clear residue)
#eval chkCopy 0 1 [[], [0, 1]] []
-- 5. nonempty incoming residue (return path must stop at trailing terminator)
#eval chkCopy 0 1 [[1, 0], [1, 1]] [0, 1, 2]
-- 6. middle registers, dst = 2, src = 0, four registers
#eval chkCopy 2 0 [[1, 1], [0], [1, 0, 1], [0, 0]] []
-- 7. src = last register, mark on the last bit next to its delimiter
#eval chkCopy 0 2 [[0], [1], [1, 1]] []
-- 8. adjacent registers dst = 1 src = 2 with residue
#eval chkCopy 1 2 [[0], [1, 1], [0, 1]] [2, 2]
-- 9. single register pair, both empty
#eval chkCopy 0 1 [[], []] []
-- 10. long src (budget feel): |src| = 6
#eval chkCopy 0 1 [[1], [1, 0, 1, 1, 0, 1]] []

/-! ## tail (dst ≠ src) probes -/

#eval chkTail 0 1 [[1, 0], [1, 1, 0]] []      -- 11.
#eval chkTail 1 0 [[1, 0], [1, 1, 0]] []      -- 12.
#eval chkTail 0 1 [[1, 0], []] []             -- 13. empty src
#eval chkTail 0 1 [[1, 0], [1]] [0, 1]        -- 14. singleton src (tail = []), residue
#eval chkTail 2 0 [[1, 1], [0], [1]] []       -- 15.

/-! ## tail in-place (dst = src) probes -/

#eval chkTailIP 0 [[1, 0, 1], [1]] []          -- 16.
#eval chkTailIP 1 [[1, 0], [0, 1]] [1, 0]      -- 17.
#eval chkTailIP 0 [[], [1]] []                 -- 18. empty register
#eval chkTailIP 1 [[0], [1]] []                -- 19. singleton
#eval chkTailIP 0 [[1], []] []                 -- 20. last cell, register 0

/-! ## budget probe: steps vs `(9L² + 9L + 30)·(cost+1)`, `L` = input tape len -/

def budgetOK (dst src : Nat) (s : State) (res : List Nat) : Bool × Nat × Nat :=
  let L := (Compile.encodeTape s ++ res).length
  let cost := (State.get s src).length + 1
  let (_, t, _, _) := chkCopy dst src s res
  (t ≤ (9 * L * L + 9 * L + 30) * (cost + 1), t, (9 * L * L + 9 * L + 30) * (cost + 1))

#eval budgetOK 0 1 [[1, 0], [1, 1, 0]] []
#eval budgetOK 0 1 [[1], [1, 0, 1, 1, 0, 1]] []
#eval budgetOK 2 0 [[1, 1], [0], [1, 0, 1], [0, 0]] []
#eval budgetOK 0 1 [[1, 0, 1, 1], []] []

/-! ## Lemma-statement validation (2026-06-12): the pinned `copyPipe_run` /
`copyBody_run_iter` / `copyBody_run_done` / `copyLoop_run` statements, checked
against the real machines — exit state, EXACT head position formula, exact
tape, and the stated budgets. -/

/-- `copyBody_run_iter`'s statement: from the unmarked cursor config (head ON
src's cell `i = |w₁|`), the body reaches `copyBody_exitLoop` on the predicted
next-cursor config within the stated budget. -/
def chkBodyIter (q : State) (dst src b : Nat) (w1 w2 res : List Nat) : Bool :=
  -- precondition: State.get q src = w1 ++ b :: w2
  (State.get q src == w1 ++ b :: w2) &&
  let H := 1 + (Compile.encodeRegs (q.take src)).length + w1.length
  let q' := State.set q dst (State.get q dst ++ [b])
  let H' := 1 + (Compile.encodeRegs (q'.take src)).length + w1.length + 1
  let M := Compile.copyBodyTM dst
  match stepsToHalt M 100000 { state_idx := 0, tapes := [([], H, Compile.encodeTape q ++ res)] } 0 with
  | some (t, c) =>
      c.state_idx == Compile.copyBody_exitLoop dst &&
      c.tapes == [([], H', Compile.encodeTape q' ++ res)] &&
      t ≤ 5 * (Compile.encodeTape q' ++ res).length + 21
  | none => false

/-- `copyPipe_run`'s statement: from the marked cursor config, the pipeline
reaches its exit on the predicted config within `5·L' + 16`. -/
def chkPipe (q : State) (dst src b : Nat) (w1 w2 res : List Nat) : Bool :=
  (State.get q src == w1 ++ b :: w2) &&
  let H := 1 + (Compile.encodeRegs (q.take src)).length + w1.length
  let qM := State.set q src (w1 ++ 2 :: w2)
  let q' := State.set q dst (State.get q dst ++ [b])
  let H' := 1 + (Compile.encodeRegs (q'.take src)).length + w1.length + 1
  let M := Compile.copyPipeTM b dst
  match stepsToHalt M 100000 { state_idx := 0, tapes := [([], H, Compile.encodeTape qM ++ res)] } 0 with
  | some (t, c) =>
      c.state_idx == Compile.copyPipeTM_exit dst &&
      c.tapes == [([], H', Compile.encodeTape q' ++ res)] &&
      t ≤ 5 * (Compile.encodeTape q' ++ res).length + 16
  | none => false

/-- `copyLoop_run`'s statement: dst pre-cleared, head on src's first cell →
loop halt with head on src's delimiter, dst = src, stated budget. -/
def chkLoop (q : State) (dst src : Nat) (res : List Nat) : Bool :=
  (State.get q dst == []) &&
  let H := 1 + (Compile.encodeRegs (q.take src)).length
  let u := State.get q src
  let q' := State.set q dst u
  let H' := 1 + (Compile.encodeRegs (q'.take src)).length + u.length
  let M := Compile.copyLoopTM dst
  match stepsToHalt M 100000 { state_idx := 0, tapes := [([], H, Compile.encodeTape q ++ res)] } 0 with
  | some (t, c) =>
      c.state_idx == Compile.copyLoopTM_exit dst &&
      c.tapes == [([], H', Compile.encodeTape q' ++ res)] &&
      t ≤ (u.length + 1) * (5 * (Compile.encodeTape q' ++ res).length + 23)
  | none => false

-- iter: dst before src / after src / first bit / last bit / b=0 / b=1 / residue
#eval chkBodyIter [[], [1,0,1]] 0 1 1 [] [0,1] []        -- b=1, first bit, dst<src
#eval chkBodyIter [[1], [1,0,1]] 0 1 0 [1] [1] [0,2]     -- b=0, middle bit, residue
#eval chkBodyIter [[1,0], [1,0,1]] 0 1 1 [1,0] [] []     -- b=1, last bit
#eval chkBodyIter [[1,0,1], [1]] 1 0 1 [] [0,1] [1]      -- dst>src, first bit
#eval chkBodyIter [[1,0,1], [0]] 1 0 1 [1,0] [] []       -- dst>src, last bit
#eval chkBodyIter [[0], [1,1], [0,0]] 2 0 0 [] [] [0]    -- middle, singleton src
-- pipe directly (marked-tape entry)
#eval chkPipe [[], [1,0,1]] 0 1 1 [] [0,1] []
#eval chkPipe [[1], [1,0,1]] 0 1 0 [1] [1] [0,2]
#eval chkPipe [[1,0,1], [1]] 1 0 1 [] [0,1] [1]
#eval chkPipe [[0], [1,1], [0,0]] 2 0 0 [] [] [0]
-- loop end-to-end
#eval chkLoop [[], [1,0,1]] 0 1 []
#eval chkLoop [[1,0,1], []] 1 0 [0,1]   -- empty src (zero iterations)... dst must be [] though
#eval chkLoop [[], [1,1,0,1]] 0 1 [2]
#eval chkLoop [[1], [], [0,1]] 1 2 []   -- dst=1 pre-cleared? get=[] ✓ src=2
