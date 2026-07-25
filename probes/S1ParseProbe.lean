import Complexity.NP.SAT.CookLevin.Reductions.S1Parse

/-! # S1 probe — stages P (parse) and G (guard)

Machine-checks the two stages that were built bottom-up on 2026-07-25-b
(`Reductions/S1Parse.lean`) and records the **cost scale**, which is the risk
this stage was scheduled first to surface.

§1 the parse outputs (header, halt bits, transition sub-stream) on valid *and*
invalid machines — the parse is data-driven and must never desynchronise;
§2 the guard flag against `S1Map.s1GuardB` on one witness per failing conjunct;
§3/§4 the cost, at a point and along three growth families.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1ParseProbe.lean`
-/

open Complexity.Lang HeadLayout S1Parse

/-! ## Test machines -/

/-- A minimal valid machine. -/
def pM0 : FlatTM :=
  { sig := 2, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some 0],
                dst_state := 1, dst_write_vals := [some 1],
                move_dirs := [TMMove.Rmove] }] }

def pM1 : FlatTM := { pM0 with start := 5 }              -- start ≥ states
def pM2 : FlatTM := { pM0 with halt := [false] }         -- |halt| ≠ states
def pM3 : FlatTM := { pM0 with tapes := 2 }              -- tapes ≠ 1

/-- `dst_state ≥ states`. -/
def pM4 : FlatTM :=
  { pM0 with trans := [{ src_state := 0, src_tape_vals := [some 0],
                         dst_state := 9, dst_write_vals := [some 1],
                         move_dirs := [TMMove.Rmove] }] }

/-- a source symbol `≥ sig`. -/
def pM5 : FlatTM :=
  { pM0 with trans := [{ src_state := 0, src_tape_vals := [some 7],
                         dst_state := 1, dst_write_vals := [some 1],
                         move_dirs := [TMMove.Rmove] }] }

/-- an arity mismatch — the case that would desynchronise a `tapes`-driven
parse. The parse must still land exactly past the entry. -/
def pM6 : FlatTM :=
  { pM0 with trans := [{ src_state := 0, src_tape_vals := [some 0, none],
                         dst_state := 1, dst_write_vals := [some 1],
                         move_dirs := [TMMove.Rmove] }] }

/-- valid, several entries, `none` payloads (the one-item `encOptN` branch). -/
def pM7 : FlatTM :=
  { sig := 3, tapes := 1, states := 3, start := 2, halt := [false, false, true],
    trans := [{ src_state := 0, src_tape_vals := [none],
                dst_state := 1, dst_write_vals := [none],
                move_dirs := [TMMove.Lmove] },
              { src_state := 1, src_tape_vals := [some 2],
                dst_state := 2, dst_write_vals := [some 0],
                move_dirs := [TMMove.Nmove] }] }

/-- no transitions at all. -/
def pM8 : FlatTM :=
  { sig := 1, tapes := 1, states := 1, start := 0, halt := [true], trans := [] }

def pIn (M : FlatTM) (s : List Nat) : State := headEncodeIn (M, s, 3, 4)

/-! ## §1 — stage P -/

/-- `[sig, tapes, states, start, |halt|]` as parsed (unary lengths). -/
def pHdr (M : FlatTM) (s : List Nat) : List Nat :=
  let t := stageP.eval (pIn M s)
  [(State.get t PSIG).length, (State.get t PTAPES).length,
   (State.get t PSTATES).length, (State.get t PSTART).length,
   (State.get t PNHALT).length, (State.get t PNTRANS).length]

#eval pHdr pM0 [0,1]   -- expect [2,1,2,0,2,1]
#eval pHdr pM7 [1,2]   -- expect [3,1,3,2,3,2]
#eval pHdr pM8 []      -- expect [1,1,1,0,1,0]

/-- Every stage-P output, against its specification. -/
def pOK (M : FlatTM) (s : List Nat) : Bool :=
  let t := stageP.eval (pIn M s)
  (State.get t PSIG == List.replicate M.sig 1) &&
  (State.get t PTAPES == List.replicate M.tapes 1) &&
  (State.get t PSTATES == List.replicate M.states 1) &&
  (State.get t PSTART == List.replicate M.start 1) &&
  (State.get t PNHALT == List.replicate M.halt.length 1) &&
  (State.get t PHALT == M.halt.map bitOf) &&
  (State.get t PNTRANS == List.replicate M.trans.length 1) &&
  (State.get t PTRANS == encSyms (transFlat M))

-- ⚠ `pM6` (arity ≠ tapes) is the interesting one: the parse must still be exact.
#eval [pOK pM0 [0,1], pOK pM1 [0,1], pOK pM2 [0,1], pOK pM3 [0,1], pOK pM4 [0,1],
       pOK pM5 [0,1], pOK pM6 [0,1], pOK pM7 [1,2], pOK pM8 []]

/-! ## §2 — stage G -/

def gOK (M : FlatTM) (s : List Nat) : Bool :=
  State.get (stagePG.eval (pIn M s)) FLG
    == (if S1Map.s1GuardB M s then [1] else [])

def gFlag (M : FlatTM) (s : List Nat) : List Nat :=
  State.get (stagePG.eval (pIn M s)) FLG

-- one machine per failing conjunct, plus the two valid ones
#eval [(gFlag pM0 [0,1], S1Map.s1GuardB pM0 [0,1]),
       (gFlag pM1 [0,1], S1Map.s1GuardB pM1 [0,1]),
       (gFlag pM2 [0,1], S1Map.s1GuardB pM2 [0,1]),
       (gFlag pM3 [0,1], S1Map.s1GuardB pM3 [0,1]),
       (gFlag pM4 [0,1], S1Map.s1GuardB pM4 [0,1]),
       (gFlag pM5 [0,1], S1Map.s1GuardB pM5 [0,1]),
       (gFlag pM6 [0,1], S1Map.s1GuardB pM6 [0,1]),
       (gFlag pM7 [1,2], S1Map.s1GuardB pM7 [1,2]),
       (gFlag pM8 [],    S1Map.s1GuardB pM8 [])]

#eval [gOK pM0 [0,1], gOK pM1 [0,1], gOK pM2 [0,1], gOK pM3 [0,1], gOK pM4 [0,1],
       gOK pM5 [0,1], gOK pM6 [0,1], gOK pM7 [1,2], gOK pM8 []]

-- the input-string conjunct (`∀ x ∈ s, x < sig`), incl. the empty string
#eval [gOK pM0 [], gOK pM0 [0], gOK pM0 [1,1,0], gOK pM0 [2], gOK pM0 [0,5],
       gOK pM7 [0,1,2], gOK pM7 [3]]

-- register 0 ends empty (what the fourth seam's scrub relies on)
#eval [State.get (stagePG.eval (pIn pM0 [0,1])) ZERO,
       State.get (stagePG.eval (pIn pM7 [1,2])) ZERO]

/-! ## §3 — cost at a point (`State.size` of the input, `stagePG.cost`) -/

def pt (M : FlatTM) (s : List Nat) : Nat × Nat :=
  (State.size (pIn M s), stagePG.cost (pIn M s))

#eval [pt pM0 [0,1], pt pM7 [1,2], pt pM8 []]

/-! ## §4 — cost scale — **THE FINDING**

Three growth families. Measured degrees: transitions ≈ 3, alphabet ≈ 1.8,
input string ≈ 2. So **P + G is cubic** in the head layout's register content,
against a `cost_bound` of `S1Map.s1Bound n = (2·(n+3))^10`. The parse is not
the S1 budget driver — stage C (the card emitter) is. -/

def famT (k : Nat) : FlatTM :=
  { sig := 2, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := (List.range k).map (fun i =>
      { src_state := i % 2, src_tape_vals := [some (i % 2)],
        dst_state := (i+1) % 2, dst_write_vals := [some ((i+1) % 2)],
        move_dirs := [TMMove.Rmove] }) }

def famS (k : Nat) : FlatTM :=
  { sig := k, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some (k-1)],
                dst_state := 1, dst_write_vals := [some 0],
                move_dirs := [TMMove.Rmove] }] }

-- |trans| = 1,2,4,8,16 : (size, cost) — cost grows ≈ n³
#eval [pt (famT 1) [], pt (famT 2) [], pt (famT 4) [], pt (famT 8) [],
       pt (famT 16) []]
-- sig = 2,4,8,16,32 : cost grows ≈ n^1.8
#eval [pt (famS 2) [], pt (famS 4) [], pt (famS 8) [], pt (famS 16) [],
       pt (famS 32) []]
-- |s| = 0,4,8,16,32 : cost grows ≈ n²
#eval [pt pM0 [], pt pM0 (List.replicate 4 1), pt pM0 (List.replicate 8 1),
       pt pM0 (List.replicate 16 1), pt pM0 (List.replicate 32 1)]

#eval [gOK (famT 16) [], gOK (famS 32) [], gOK (famS 32) [31], gOK (famS 32) [32]]

/-! ## §5 — structural numbers for the next stages -/

-- loop nesting depth (drives the compiler's static scratch base: a program
-- compiled at base `sb` touches registers `< sb + 2·loopDepth`)
#eval stagePG.loopDepth
-- the syntactic write set, and the register frame bound proven in the file
#eval (stagePG.writes.foldl (fun a v => max a v) 0)
