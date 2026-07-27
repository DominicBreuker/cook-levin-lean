import Complexity.NP.SAT.CookLevin.Reductions.S1Prelude
import Complexity.NP.SAT.CookLevin.Reductions.S1Program

/-! # S1 probe — stage C's prelude family: model shape, preamble, budget

`Reductions/S1Prelude.lean` re-states `S1Cards.preludeBlocks` in the shape the
emitter will implement and builds the preamble that supplies its two derived
constants. All of that is proven; what this probe adds is the numeric checks
the proofs cannot express.

§1 **the emitter-shaped model agrees with the target** on a spread of
   `(σ, states, q0)`, including the degenerate `σ = 0` corner (where both bands
   are empty and only the five special kinds fire) — the "probe the empty/zero
   instance of every claim" invariant;
§2 **the preamble runs**: `pPre` on a real machine, after the real stage P/G,
   produces exactly the five `PConst` registers — in particular `PQ0` is
   `min M.start M.states` and `PHB` is `(σ+1)(q0+1)`, the two values no earlier
   stage computes;
§3 **the register table is consistent**: the 30 registers the family claims are
   distinct (bar one deliberate reuse) and every one of them is inside
   `S1Program.CDirty` — which they exactly exhaust;
§4 **the cost budget has room**. `S1Map.s1Bound` is `(2(n+3))^10`; this prints
   it next to what the five built families actually cost, and next to the block
   counts of the two unbuilt ones, so the ladder's slack is on the record
   *before* the ladder is attempted.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1PreludeProbe.lean`
-/

open Complexity.Lang Complexity.Simulators S1Program S1Prelude

/-! ## §1 — the emitter-shaped model equals the target -/

/-! `(σ, states, q0)` triples; `(0,0,0)` is the degenerate machine. -/
def pTriples : List (Nat × Nat × Nat) :=
  [(0, 0, 0), (0, 3, 0), (1, 1, 0), (2, 2, 0), (2, 2, 1), (3, 3, 2), (4, 2, 1), (2, 5, 3)]

#eval pTriples.map (fun p =>
  decide (S1Cards.preludeBlocks p.1 p.2.1 p.2.2 = preludeSeg p.1 p.2.1 p.2.2))
  -- expect all true

/-! ⚠ At `σ = 0` both bands are empty and every star kind has *no* live
resolution — the case where an emitter that assumed `σ ≥ 1` would silently
emit nothing. The family is still non-empty. -/
#eval pTriples.map (fun p => (S1Cards.preludeBlocks p.1 p.2.1 p.2.2).length)

/-! ## §2 — the preamble, on the real machines -/

def rM0 : FlatTM :=
  { sig := 2, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some 0],
                dst_state := 1, dst_write_vals := [some 1],
                move_dirs := [TMMove.Rmove] }] }

def rM1 : FlatTM := { rM0 with sig := 3, states := 3, halt := [false, true, true] }

/-! A machine whose `start` is OUT OF RANGE: `preludeBlocks` is applied at
`min M.start M.states`, so the clamp is load-bearing and `minReg` is what
performs it. -/
def rMwide : FlatTM := { rM0 with start := 7 }

def rMtriv : FlatTM :=
  { sig := 0, tapes := 1, states := 0, start := 0, halt := [true], trans := [] }

def rCases : List (FlatTM × List Nat × Nat × Nat) :=
  [(rM0, [], 0, 0), (rM0, [1, 0], 2, 3), (rM1, [2, 1, 0], 1, 2),
   (rMwide, [1], 1, 1), (rMtriv, [], 0, 0)]

def rIn (x : FlatTM × List Nat × Nat × Nat) : State := HeadLayout.headEncodeIn x

/-- Everything before the prelude family: parse + guard, then Σ, I and the five
built card families. -/
def rPre (x : FlatTM × List Nat × Nat × Nat) : State :=
  S1CardEmit.cFive.eval
    ((S1Parse.stagePG ;; S1Emit.stageSig ;; S1Emit.stageInit).eval (rIn x))

def rPost (x : FlatTM × List Nat × Nat × Nat) : State := pPre.eval (rPre x)

/-! The five `PConst` registers, as numbers, next to what they should be. -/
#eval rCases.map (fun x =>
  let M := x.1
  let q0 := min M.start M.states
  let t := rPost x
  (((State.get t S1Emit.ESG).length, S1Cards.sgv M.sig M.states),
   ((State.get t PBV).length, S1Cards.bv M.sig M.states),
   ((State.get t PZ).length, 0),
   ((State.get t PB5).length, 5),
   ((State.get t PHB).length, S1Cards.hv M.sig q0 0)))

/-! …and the same as a single verdict, including that every register really is
a block of `1`s (`PConst` asserts `List.replicate _ 1`, not just a length). -/
#eval rCases.map (fun x =>
  let M := x.1
  let q0 := min M.start M.states
  let t := rPost x
  decide (State.get t S1Emit.ESG = List.replicate (S1Cards.sgv M.sig M.states) 1
    ∧ State.get t PBV = List.replicate (S1Cards.bv M.sig M.states) 1
    ∧ State.get t PZ = []
    ∧ State.get t PB5 = List.replicate 5 1
    ∧ State.get t PHB = List.replicate (S1Cards.hv M.sig q0 0) 1))
  -- expect all true

/-! ⚠ The preamble must not disturb what the *earlier* stages produced: the
five built card families' output register and the parse outputs the prelude
still reads. -/
#eval rCases.map (fun x =>
  decide (State.get (rPost x) S1Emit.EOUT_C = State.get (rPre x) S1Emit.EOUT_C
    ∧ State.get (rPost x) S1Parse.PSIG = State.get (rPre x) S1Parse.PSIG
    ∧ State.get (rPost x) S1Emit.EOUT_S = State.get (rPre x) S1Emit.EOUT_S
    ∧ State.get (rPost x) S1Emit.EOUT_I = State.get (rPre x) S1Emit.EOUT_I))
  -- expect all true

/-! ## §3 — the register table -/

/-! The 30 registers the prelude family claims. -/
def rAll : List Var := PAll ++ [S1Emit.EOUT_C]

/-! ⚠ Pairwise distinct — a silent collision between, say, a kind level's base
and a resolution counter would make the emitter wrong in a way no type checks. -/
#eval (rAll.length, rAll.eraseDups.length)   -- expect (31, 30): one deliberate reuse

/-! ⚠ The single repeat is `PCS3 = S1Emit.EA`: `loadSg` uses `EA` as
multiplication scratch inside the preamble, and the nest uses the same register
for level 3's cut-seen bit *after* the preamble has finished. Every other pair
is distinct. -/
#eval (rAll.eraseDups.filter (fun r => decide (rAll.count r > 1)))   -- expect [38]

/-! ⚠ …and every one of them is inside stage C's stated licence `CDirty`, so
`stageC_run`'s frame clause stays meetable. -/
#eval decide (rAll.all (fun r => decide (CDirty r)))   -- expect true

/-! ⚠ **The count is exact and the licence is FULL.** `CDirty` licenses
`[14,32) ∪ [37,48) ∪ {EOUT_C}` = 30 registers, and the prelude family uses all
30 — the second `#eval` prints the *unused* licensed registers and it is empty.
So `stepBlocks` has no fresh register to claim inside stage C's licence: it
runs before the prelude and must reuse this same pool (or `CDirty`, and with it
`stageC_run`, has to be widened — which re-opens `S1Program.cFive_frame`). -/
#eval ((List.range 48).filter (fun r => decide (CDirty r))).length
#eval ((List.range 48).filter (fun r => decide (CDirty r) ∧ ¬ (r ∈ rAll)))

/-! ## §4 — the cost budget -/

def rCost (x : FlatTM × List Nat × Nat × Nat) : Nat :=
  ((S1Parse.stagePG ;; S1Emit.stageSig ;; S1Emit.stageInit) ;;
    (S1CardEmit.cFive ;; pPre)).cost (rIn x)

/-! Input size, the budget `S1Map.s1Bound`, and what everything built so far
actually costs. The gap is the head-room the (still open) cost ladder has to
work with — it is enormous, so the ladder is a slack argument, not a tight
one. -/
#eval rCases.map (fun x =>
  (encodable.size x, S1Map.s1Bound (encodable.size x), rCost x))

/-! Block counts of the three card sub-streams `(five, step, prelude)` — the
prelude family dominates, which is why it was built first. -/
#eval rCases.map (fun x =>
  let M := x.1
  ((S1Cards.copyBlocks M.sig M.states ++ S1Cards.copyRightBlocks M.sig M.states ++
     S1Cards.haltLeftBlocks M.sig M.states (M.halt.map S1Parse.bitOf) ++
     S1Cards.haltCenterBlocks M.sig M.states (M.halt.map S1Parse.bitOf) ++
     S1Cards.haltRightBlocks M.sig M.states (M.halt.map S1Parse.bitOf)).length,
   ((normTrans M).flatMap (S1Cards.entryBlocks M)).length,
   (S1Cards.preludeBlocks M.sig M.states (min M.start M.states)).length))
