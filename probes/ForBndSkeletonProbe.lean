import Complexity.Lang.Semantics
open Complexity.Lang

/-! # `compileForBnd` loop-skeleton probe (top-down, 2026-06-11)

Functional model of the pinned `compileForBnd` machine bookkeeping (scratch
`K1 = sb` remaining / `K2 = sb+1` done, counter rebuilt from `K2` each round),
checked against `Cmd.run`'s fold semantics — including bodies that CLOBBER
`bound` and `counter` (the snapshot-vs-clobber gap). -/

def machineModel (cnt bnd : Var) (body : Cmd) (sb : Nat) (s : State) : State :=
  let iters := (State.get s bnd).length
  -- entry: K1 := copy of bnd (cursor copy); K2 starts []
  let s1 := State.set s sb (State.get s bnd)
  let rec go : Nat → State → State
    | 0, st => st
    | fuel+1, st =>
      if State.get st sb = [] then st
      else
        let st1 := State.set st cnt (State.get st (sb+1))    -- copy cnt K2
        let st2 := body.eval st1                             -- body (contract)
        let st3 := State.set st2 (sb+1) (State.get st2 (sb+1) ++ [1])  -- appendOne K2
        let st4 := State.set st3 sb (State.get st3 sb).tail  -- tail K1 K1
        go fuel st4
  let sf := go (iters + 1) s1
  State.set sf (sb + 1) []                                   -- clear K2 (K1 is [])

def chk (cnt bnd : Var) (body : Cmd) (sb : Nat) (s : State) : Bool :=
  machineModel cnt bnd body sb s == (Cmd.forBnd cnt bnd body).eval s

-- registers: cnt=0, bnd=1, data=2; sb=3 (K1=3, K2=4); width 6 ≥ sb+2.
def s0 : State := [[1], [1,0,1], [0,1], [], [], []]

-- 1. benign body: copies counter into data (reads cnt each round)
#eval chk 0 1 (.op (.copy 2 0)) 3 s0
-- 2. body CLOBBERS bound mid-loop
#eval chk 0 1 (.op (.clear 1)) 3 s0
-- 3. body CLOBBERS counter mid-loop
#eval chk 0 1 (.op (.appendOne 0)) 3 s0
-- 4. body clobbers BOTH (clear bnd ;; clear cnt)
#eval chk 0 1 (.op (.clear 1) ;; .op (.clear 0)) 3 s0
-- 5. body grows a register each round
#eval chk 0 1 (.op (.appendZero 2)) 3 s0
-- 6. zero iterations (bound empty)
#eval chk 0 1 (.op (.clear 1)) 3 [[1], [], [0,1], [], [], []]
-- 7. one iteration
#eval chk 0 1 (.op (.appendOne 2)) 3 [[1], [0], [0,1], [], [], []]
-- 8. nested loop body (inner forBnd over data; inner scratch would sit at sb+2 —
--    semantically eval'd here; checks the OUTER bookkeeping tolerates it)
#eval chk 0 1 (.forBnd 0 2 (.op (.appendOne 2))) 3
  [[1], [1,1], [1], [], [], [], [], []]
-- 9. body writes bound LONGER than the snapshot (loop count must stay = 3)
#eval chk 0 1 (.op (.concat 1 2 2)) 3 [[], [1,1,1], [0,1], [], [], []]

/-! ## W-invariant ① accounting (cursor-copy bookkeeping, exact residue):
joint (size+residue) growth of the bookkeeping =
  iters (entry copy) + Σ_{i<iters} (i (counter copy) + 1 (appendOne K2))
must fit the loop's cost lump `1 + iters²`. Tight at iters ∈ {1,2}. -/
#eval (List.range 80).all (fun iters =>
  iters + (List.range iters).foldl (fun a i => a + i + 1) 0 ≤ 1 + iters * iters)

/-! ## Budget ② unit accounting (physStepBudget α = 8): per-iteration overhead
≤ 6 units (test + counter-copy + appendOne + tail + seams) + 4 entry/exit units,
body costs ≤ 8·(bc_i + 1) units each; available 8·(Σbc + iters² + 2).
Reduces to `14·iters + 4 ≤ 8·iters² + 16` — must hold for ALL iters. -/
#eval (List.range 200).all (fun it => 14 * it + 4 ≤ 8 * it * it + 16)

/-! ## counterexample check the moveRegion-based copy (joint 3i per round) FAILS ①: -/
#eval (List.range 12).map (fun iters =>
  decide (iters + (List.range iters).foldl (fun a i => a + 3 * i + 1) 0 ≤ 1 + iters * iters))

/-! ## Probe results (2026-06-11, all green)

Run with: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/ForBndSkeletonProbe.lean`

- 9/9 `machineModel = (forBnd …).eval` checks `true` — including bodies that
  clobber `bound`, clobber `counter`, clobber both, grow registers, nested
  loops, zero/one iterations, and a body that rewrites `bound` LONGER than the
  snapshot (the loop count stays the entry snapshot).
- W-invariant ① accounting (cursor-copy bookkeeping): holds for all
  `iters < 80` (tight at `iters ∈ {1,2}`).
- Budget ② unit accounting (`physStepBudget` α = 8): holds for all `iters < 200`.
- moveRegion-based counter copy (joint `3i`/round): FAILS ① from `iters = 2` —
  the cursor copy is mandatory for the per-iteration counter rebuild. -/
