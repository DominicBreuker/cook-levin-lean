import Complexity.NP.SAT.CookLevin.Reductions.S1StepEmit

/-! # S1 probe — stage C's `stepBlocks` family, the entry body

`Reductions/S1StepEmit.lean` builds `S1Step.stepEmit`, the `Cmd` that emits one
normalised transition entry's cards, and `stepGo`, the pure model the entry loop
must meet. Both are `sorry`-free, so both can be `#eval`-ed end to end.

§1 **`stepEmit` end to end**: run it on a hand-built register frame and compare
   `EOUT_C` with `FlatTCCFree.encNats (stepSeg …)` over a parameter sweep that
   includes `σ = 0`, all three `mv` arms, both option tags and out-of-range
   `mVal`/`wVal` (the `min · σ` clamps);
§2 **the frame**: `stepEmit` must leave every register outside `SD1` alone —
   in particular the constants it reads and the parse outputs stage C may not
   touch;
§3 **`stepGo` is the entry loop's spec**: `stepGo M [] M.trans` equals the
   `stepBlocks` summand `(normTrans M).flatMap (entryBlocks M)` on real
   machines, *including* ones with duplicate keys and halting sources — the two
   things the dedup pass exists for;
§4 scale: how many cells one entry emits, for the cost ladder's record.

⚠ **Probe gotcha (2026-07-27-c, still true)**: `State` is an `abbrev` for
`List (List Nat)`, so `s.set v x` resolves to `List.set` — a silent no-op past
the end of a short list. Every write below goes through `State.set` explicitly
and starts from a 48-register frame.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1StepEmitProbe.lean`
-/

open Complexity.Lang Complexity.Simulators S1Cards S1Step

/-! ## The register frame, built by hand -/

def base48 : State := List.replicate 48 ([] : List Nat)

/-- `SConst σ st` + `SEntry σ q q' mT mV wT wV mv`, laid out explicitly. -/
def frameOf (σ st q q' mT mV wT wV mv : Nat) : State :=
  let s := base48
  let s := State.set s S1CardEmit.CBV (List.replicate (bv σ st) 1)
  let s := State.set s S1CardEmit.CS1 (List.replicate (σ + 1) 1)
  let s := State.set s S1CardEmit.CS2 (List.replicate (σ + 2) 1)
  let s := State.set s S1CardEmit.CZ []
  let s := State.set s S1Parse.PSIG (List.replicate σ 1)
  let s := State.set s TQ (List.replicate (hv σ q 0) 1)
  let s := State.set s TQ2 (List.replicate (hv σ q' 0) 1)
  let s := State.set s TR (List.replicate (rOf σ mT mV) 1)
  let s := State.set s TW0 (List.replicate (wOf σ mT mV wT wV false) 1)
  let s := State.set s TW1 (List.replicate (wOf σ mT mV wT wV true) 1)
  let s := State.set s TFN (S1Prelude.flagRep (decide (mv = 2)))
  State.set s TFR (S1Prelude.flagRep (decide (mv = 1)))

/-- `(σ, states, q, q', mTag, mVal, wTag, wVal, mv)`. -/
abbrev Nine := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

def esweep : List Nine :=
  (([0, 1, 2] : List Nat).flatMap (fun σ =>
    ([0, 2] : List Nat).flatMap (fun st =>
      ([0, 1, 2] : List Nat).flatMap (fun mv =>
        ([0, 1] : List Nat).flatMap (fun mT =>
          ([0, 1] : List Nat).flatMap (fun wT =>
            ([0, 5] : List Nat).map (fun v =>
              (σ, st, min 1 st, st, mT, v, wT, v, mv))))))))
  ++ [(0, 0, 0, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 1, 0, 1, 0, 1),
      (1, 1, 1, 0, 1, 1, 1, 0, 2), (2, 3, 3, 1, 0, 9, 1, 9, 0)]

#eval esweep.length

def runStep (p : Nine) : List Nat :=
  State.get (stepEmit.eval (frameOf p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
    p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2))
    S1Emit.EOUT_C

def wantStep (p : Nine) : List Nat :=
  FlatTCCFree.encNats (stepSeg p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
    p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)

/-! ## §1 — the entry body emits exactly its entry's cards -/

#eval decide (esweep.all (fun p => decide (runStep p = wantStep p)))
  -- expect true

/-! A negative control: the same comparison against a *different* `mv` must
fail somewhere, or §1 would be vacuous. -/
#eval decide (esweep.any (fun p =>
  decide (runStep p ≠ FlatTCCFree.encNats (stepSeg p.1 p.2.1 p.2.2.1 p.2.2.2.1
    p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1
    ((p.2.2.2.2.2.2.2.2 + 1) % 3)))))
  -- expect true

/-! ## §2 — the frame: only `SD1 ∪ {EOUT_C}` moves

⚠ This is the check that keeps `stepBlocks` compatible with the rest of stage C:
the prelude's preamble rebuilds its own constants, but the *parse* outputs
(`PSIG`, `PSTATES`, `PSTART`, `PHALT`, `PNTRANS`, `PTRANS`) and the input layout
`1`–`5` are outside `CDirty` and must survive untouched. -/
def touched (p : Nine) : List Var :=
  let s0 := frameOf p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
    p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2
  let s1 := stepEmit.eval s0
  (List.range 48).filter (fun r => State.get s1 r ≠ State.get s0 r)

#eval decide (esweep.all (fun p =>
  (touched p).all (fun r => r ∈ (S1Emit.EOUT_C :: SD1))))
  -- expect true

/-! The registers actually written, over the whole sweep. -/
#eval (esweep.flatMap touched).eraseDups.mergeSort (fun a b => a ≤ b)
  -- expect a sublist of SD1 ∪ {EOUT_C} = [21, 28, 29, 30, 34, 42, 46]

/-! ## §3 — `stepGo` is the entry loop's specification

The dedup pass exists for two reasons; both must be exercised. `pM2` has two
entries with the **same key** (same source state and read symbol) and `pM3` has
an entry whose source state **halts**. -/

def pM0 : FlatTM :=
  { sig := 2, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some 0],
                dst_state := 1, dst_write_vals := [some 1],
                move_dirs := [TMMove.Rmove] }] }

/-- Two entries with the same key — the second must be dropped. -/
def pM2 : FlatTM :=
  { pM0 with trans := pM0.trans ++
      [{ src_state := 0, src_tape_vals := [some 0],
         dst_state := 0, dst_write_vals := [none], move_dirs := [TMMove.Lmove] },
       { src_state := 0, src_tape_vals := [some 1],
         dst_state := 1, dst_write_vals := [some 0], move_dirs := [TMMove.Nmove] }] }

/-- An entry whose source state halts — it must be filtered out. -/
def pM3 : FlatTM :=
  { pM2 with trans := pM2.trans ++
      [{ src_state := 1, src_tape_vals := [some 0],
         dst_state := 0, dst_write_vals := [some 0], move_dirs := [TMMove.Rmove] }] }

/-- The trivial machine: no symbols, no transitions. -/
def pMtriv : FlatTM :=
  { sig := 0, tapes := 1, states := 0, start := 0, halt := [true], trans := [] }

def pCases : List FlatTM := [pM0, pM2, pM3, pMtriv]

#eval decide (pCases.all (fun M =>
  decide (stepGo M [] M.trans = (normTrans M).flatMap (entryBlocks M))))
  -- expect true

/-! …and the `emitFold_run` shape agrees with `stepGo`. -/
#eval decide (pCases.all (fun M =>
  decide ((List.range M.trans.length).flatMap
      (fun i => stepOut M (stepSt^[i] ([], M.trans)))
    = stepGo M [] M.trans)))
  -- expect true

/-! ⚠ The dedup and the halt filter are load-bearing, not decoration: on `pM3`
the raw stream is strictly longer than the normalised one. -/
#eval pCases.map (fun M => (M.trans.length, (normTrans M).length))
  -- expect (1,1) (3,2) (4,2) (0,0)

/-! ## §4 — how much one entry emits (the cost ladder's raw numbers) -/

#eval ([0, 1, 2, 3] : List Nat).map (fun σ =>
  (σ, (stepSeg σ 2 1 2 1 0 1 0 0).length, (stepSeg σ 2 1 2 1 0 1 0 1).length,
      (stepSeg σ 2 1 2 1 0 1 0 2).length))

#eval pCases.map (fun M => ((normTrans M).flatMap (entryBlocks M)).length)
