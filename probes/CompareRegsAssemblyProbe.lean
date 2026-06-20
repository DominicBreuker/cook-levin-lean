import Complexity.Lang.Compile
open Complexity.Lang

/-! # `eqBit` (d2) `compareRegsTM` END-TO-END ASSEMBLY probe (bottom-up, 2026-06-19b)

HANDOFF "▶ THE IMMEDIATE NEXT STEP — (d2) assemble `compareRegsTM`". All sub-gadgets
are proven as head-`0`→head-`0` run lemmas. Before investing in the ~1000-line
seam-threading proof, this probe validates the full pipeline SEMANTICS by running
each PROVEN stage's machine from its start (state 0) on the current tape and
feeding the resulting tape forward — exactly the chain the (d2) run lemma proves:

  growTwoEmpty ⨾ copyEmpty src1→sc1 ⨾ copyEmpty src2→sc2 ⨾ compareLoop
    ⨾ [eqVerdict reads sc1/sc2] ⨾ clear sc1 ⨾ clear sc2 ⨾ shrinkTwoEmpty

We check, for EQ and NEQ inputs at several lengths:
  (1) the final tape is `encodeTape s0 ++ (terminator-free residue)` — i.e. the
      ORIGINAL registers are restored (the d1 wrapper sees a clean tape);
  (2) the verdict register-emptiness AFTER compareLoop decides equality
      (`matchLen_drop_empty_iff`): both scratch suffixes empty ⟺ src1 = src2.

`true` everywhere = design (A) assembles correctly; the proof is pure seam-threading. -/

namespace CompareRegsAssemblyProbe

/-- Run `M` from `cfg` until it reaches a halting state (or fuel runs out),
returning the halted config. -/
partial def runToHalt (M : FlatTM) (cfg : FlatTMConfig) (fuel : Nat) : Option FlatTMConfig :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if haltingStateReached M cfg then some cfg
      else match stepFlatTM M cfg with
        | none => none
        | some cfg' => runToHalt M cfg' fuel

/-- The tape contents (the `right` part) after running `M` from head-0 on `tape`. -/
def stageTape (M : FlatTM) (tape : List Nat) (fuel : Nat) : Option (List Nat) :=
  match runToHalt M { state_idx := 0, tapes := [([], 0, tape)] } fuel with
  | some cfg => match cfg.tapes with
                | (_, _, r) :: _ => some r
                | _ => none
  | none => none

/-- The halted state index after running `M` from head-0 on `tape`. -/
def stageState (M : FlatTM) (tape : List Nat) (fuel : Nat) : Option Nat :=
  (runToHalt M { state_idx := 0, tapes := [([], 0, tape)] } fuel).map (·.state_idx)

def bigFuel : Nat := 2000000

/-- Decode a raw tape-`right` list (head-0) back to a register list.
`decodeTape` ignores the leading sentinel + terminator-free residue and trims
trailing empty registers. -/
def dec (r : List Nat) : State :=
  Compile.decodeTape { state_idx := 0, tapes := [([], 0, r)] }

/- The pure semantic spec the assembly should realise: after compareLoop, the two
scratch registers hold `drop n c1` / `drop n c2` where `n = matchLen c1 c2`.
We trust the proven `compareLoop_run`; here we drive the actual machines. -/

/-- Build a state with registers `regs`. -/
def st (regs : List (List Nat)) : State := regs

/-- Run the FULL pipeline at the machine level (feeding tapes forward through the
proven stages) and return `(finalTape, postLoopBothEmpty, restoredOK)`.
`sc1 = s0.length`, `sc2 = s0.length + 1` (the two grown-empty registers). -/
def pipeline (s0 : State) (src1 src2 : Var) :
    Option (List Nat × Bool × Bool) := do
  let sc1 := s0.length
  let sc2 := s0.length + 1
  -- stage 1: grow two empty scratch registers at the end.
  let t1 ← stageTape Compile.growTwoEmptyM (Compile.encodeTape s0) bigFuel
  -- stage 2: copy src1 → sc1
  let t2 ← stageTape (Compile.copyEmptyRawTM sc1 src1) t1 bigFuel
  -- stage 3: copy src2 → sc2
  let t3 ← stageTape (Compile.copyEmptyRawTM sc2 src2) t2 bigFuel
  -- stage 4: compare loop (consume matched prefix of sc1/sc2)
  let t4 ← stageTape (Compile.compareLoopTM sc1 sc2) t3 bigFuel
  -- stage 5: the verdict reads sc1/sc2 — recover their emptiness from the decode.
  let decoded := dec t4
  let bothEmpty := (decoded.getD sc1 [] == []) && (decoded.getD sc2 [] == [])
  -- stage 6: cleanup — clear sc1, clear sc2, shrink two.
  let t5 ← stageTape (ClearGadget.clearRegionTM sc1) t4 bigFuel
  let t6 ← stageTape (ClearGadget.clearRegionTM sc2) t5 bigFuel
  let t7 ← stageTape Compile.shrinkTwoEmptyM t6 bigFuel
  -- restored iff decoding the final tape matches decoding the original encoding.
  let restoredOK := dec t7 == dec (Compile.encodeTape s0)
  some (t7, bothEmpty, restoredOK)

/-- For an EQ input (src1 = src2) we expect `bothEmpty = true`, `restoredOK = true`. -/
def checkEQ (s0 : State) (src1 src2 : Var) : Bool :=
  match pipeline s0 src1 src2 with
  | some (_, bothEmpty, restoredOK) => bothEmpty && restoredOK
  | none => false

/-- For a NEQ input we expect `bothEmpty = false`, `restoredOK = true`. -/
def checkNEQ (s0 : State) (src1 src2 : Var) : Bool :=
  match pipeline s0 src1 src2 with
  | some (_, bothEmpty, restoredOK) => (!bothEmpty) && restoredOK
  | none => false

/-! ## EQ inputs: src1 = src2 (registers 0 and 1 equal). -/

#eval checkEQ (st [[1,0,1], [1,0,1]]) 0 1            -- equal, length 3
#eval checkEQ (st [[], []]) 0 1                       -- both empty → equal
#eval checkEQ (st [[1,1,0,0], [1,1,0,0], []]) 0 1    -- equal, length 4, extra reg
#eval checkEQ (st [[0], [0]]) 0 1                     -- single bit equal

/-! ## NEQ inputs: src1 ≠ src2. -/

#eval checkNEQ (st [[1,0], [1,1]]) 0 1                -- bit mismatch
#eval checkNEQ (st [[1,0], [1,0,1]]) 0 1              -- prefix (length) mismatch
#eval checkNEQ (st [[1,0,1], [1,0]]) 0 1             -- the other length mismatch
#eval checkNEQ (st [[1], []]) 0 1                     -- one empty
#eval checkNEQ (st [[], [0]]) 0 1                     -- other empty

/-! ## Show the actual final tapes for one EQ + one NEQ case (visual sanity). -/

#eval (pipeline (st [[1,0,1], [1,0,1]]) 0 1).map (fun (t, _, _) => dec t)
#eval (pipeline (st [[1,0], [1,1]]) 0 1).map (fun (t, b, r) => (b, r, dec t))

end CompareRegsAssemblyProbe
