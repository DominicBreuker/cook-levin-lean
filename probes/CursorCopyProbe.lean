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

/-- Read the cursor cell: `0` → exit `1` (done, no write); shifted bit `b+1` →
write the mark `3`, exit `2+b` (Nmove — the head stays on the mark). -/
def markReadTM : FlatTM where
  sig := 4
  tapes := 1
  states := 4
  trans := [mkE1 0 (some 0) 1 none .Nmove,
            mkE1 0 (some 1) 2 (some 3) .Nmove,
            mkE1 0 (some 2) 3 (some 3) .Nmove]
  start := 0
  halt := [false, true, true, true]

/-- At the mark: restore the shifted bit (write `b+1`) and step right onto the
next cursor cell. -/
def restoreStepTM (b : Nat) : FlatTM where
  sig := 4
  tapes := 1
  states := 2
  trans := [mkE1 0 (some 3) 1 (some (b + 1)) .Rmove]
  start := 0
  halt := [false, true]

/-- `(machine, exit)` sequential composition. -/
def cseq : (FlatTM × Nat) → (FlatTM × Nat) → (FlatTM × Nat)
  | (m1, e1), (m2, e2) => (composeFlatTM m1 m2 e1, m1.states + e2)

/-- The per-bit pipeline for bit `b`: from the freshly written mark, step left,
scan left to the leading sentinel, append `b` to `dst`, scan left to the
trailing terminator, step left, scan left to the mark, restore + step right. -/
def pipelineTM (b dst : Nat) : FlatTM × Nat :=
  cseq (cseq (cseq (cseq (cseq (cseq
    (stepLeftTM 4, 1)
    (scanLeftUntilTM 4 3, 1))
    (appendAtTM (b + 1) dst, appendAtTM_exit dst))
    (scanLeftUntilTM 4 3, 1))
    (stepLeftTM 4, 1))
    (scanLeftUntilTM 4 3, 1))
    (restoreStepTM b, 1)

/-- Loop body (3-way branch): done / copy-bit-0 / copy-bit-1. -/
def copyBodyRawTM (dst : Nat) : FlatTM :=
  branchComposeFlatTM markReadTM (pipelineTM 0 dst).1 (pipelineTM 1 dst).1 2 3

def copyBody_done : Nat := 1
def copyBody_iter0 (dst : Nat) : Nat := 4 + (pipelineTM 0 dst).2
def copyBody_iter1 (dst : Nat) : Nat :=
  4 + (pipelineTM 0 dst).1.states + (pipelineTM 1 dst).2

/-- The two iterate exits merged (`joinTwoHalts` bridges iter1 → iter0). -/
def copyBodyTM (dst : Nat) : FlatTM :=
  Compile.joinTwoHalts (copyBodyRawTM dst) (copyBody_iter0 dst) (copyBody_iter1 dst)

def copyLoopTM (dst : Nat) : FlatTM :=
  loopTM (copyBodyTM dst) copyBody_done (copyBody_iter0 dst)

def copyLoop_exit (dst : Nat) : Nat := (copyBodyTM dst).states

/-- Full `copy dst src` machine (`dst ≠ src`). -/
def copyRegionTM (dst src : Nat) : FlatTM × Nat :=
  cseq (cseq (cseq
    (clearRegionTM dst, clearRegionTM_exit dst)
    (navigateToRegTM src, navigateToRegTM_exit src))
    (copyLoopTM dst, copyLoop_exit dst))
    (justRewindTM, 1)

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

def tailBranch_loopExit (dst : Nat) : Nat := 3 + copyLoop_exit dst
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
