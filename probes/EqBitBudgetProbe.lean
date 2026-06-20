import Complexity.Lang.Compile
open Complexity.Lang

/-! # `eqBit` FULL-assembly budget risk probe (bottom-up, 2026-06-20c)

**Why this probe exists.** The prior probe `CompareRegsBudgetProbe.lean` only
validated that the **two copies** of design (A) fit *half* the `cost=1` budget
`(9·L²+9·L+30)·2`. It never measured the **full** `compareRegsTM` (consume loop +
cleanup clears) nor the d1 wrapper (`+ clear dst + append`). This probe closes
that gap and surfaces the budget risk that d2-iv (the step-bound threading) must
respect.

**Findings (measured below):**

1. **REAL steps FIT.** The full `compareRegsTM` real steps asymptote to **~70%**
   of `(9·L²+9·L+30)·2`; the full `opEqBit` approximation (`compareRegsTM` then
   `clear dst`) sits at **~60%**. So the operation genuinely fits `cost=1` — no
   `Op.cost` bump is warranted (a data-aware cost would over-charge to Θ(L³) and
   re-open EvalCnf's quartic).

2. **⚠ PROVABLE LOOSE bounds BUST.** The step bounds recoverable from the existing
   sub-gadgets are *loose* (e.g. `navSteps_le` is already a 2× over-estimate;
   each `branchComposeFlatTM` seam adds slack). Composed bottom-up
   (`loopBudget ≤ (matchLen+1)·M_body` with the provable `M_body ≈ 18·L`, vs the
   real `≈ 13·L`), the worst case (equal operands, longest loop) reaches **~121%**
   of the `cost=1` budget. Even *near-perfect* tight bounds land at ~97% — too
   fragile to prove robustly.

3. **✅ FREE FIX (shipped): loosen the per-op CONTRACT budget `9 → 27`.** The
   consumer `run_physical_residue_gen` ② discharges the per-op budget against
   `physStepBudget`'s `(9G²+9G+33)·(8·cost+8)` — an **8× headroom** (`27 ≤ 72`).
   So loosening the contract's quadratic constant `9 → 27` is free: it does NOT
   touch `physStepBudget`, `Op.cost`, or EvalCnf (degree unchanged). The looser
   `(27·L²+27·L+90)·2` gives the eqBit cascade ~3× room — the loose bottom-up
   bounds now fit with margin. (Done in `Compile.lean`: statement +
   `Compile.opBudgetLoosen` + the 7 proven ops + the gen-lemma `h1`/`h2`.)

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/EqBitBudgetProbe.lean`
-/

namespace EqBitBudgetProbe

partial def runToHalt (M : FlatTM) (cfg : FlatTMConfig) (fuel : Nat) : Nat × FlatTMConfig :=
  match fuel with
  | 0 => (999999999, cfg)
  | fuel + 1 =>
      if haltingStateReached M cfg then (0, cfg)
      else match stepFlatTM M cfg with
        | none => (0, cfg)
        | some cfg' => let (k, c) := runToHalt M cfg' fuel; (k + 1, c)

def stepsToHalt (M : FlatTM) (cfg : FlatTMConfig) (fuel : Nat) : Nat := (runToHalt M cfg fuel).1

/-- The `cost=1` per-op budget at tape length `L`: `(9·L²+9·L+30)·2`. -/
def budget1 (L : Nat) : Nat := (9 * L * L + 9 * L + 30) * 2

/-- The LOOSENED (shipped) per-op budget: `(27·L²+27·L+90)·2`. -/
def budget1_loose (L : Nat) : Nat := (27 * L * L + 27 * L + 90) * 2

/-! ## Finding 1a — full `compareRegsTM` real steps vs `cost=1` budget.
`(realSteps, L, budget1, real·100/budget1)`. Equal operands = longest loop. -/

def mkEq (m nregs : Nat) : State :=
  List.replicate m 1 :: List.replicate m 1 :: List.replicate (nregs - 2) []

def measureCRT (m nregs : Nat) : Nat × Nat × Nat × Nat :=
  let s0 := mkEq m nregs
  let M := Compile.compareRegsTM s0.length (s0.length + 1) 0 1
  let cfg : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s0)] }
  let L := (Compile.encodeTape s0).length
  let steps := stepsToHalt M cfg (60 * (L + 2) * (L + 2))
  (steps, L, budget1 L, steps * 100 / budget1 L)

#eval measureCRT 8 4    -- ~67%
#eval measureCRT 16 4   -- ~69%
#eval measureCRT 24 4   -- ~70%

/-! ## Finding 1b — full `opEqBit` ≈ `compareRegsTM` then `clear dst` vs `cost=1`. -/

def mkEqDst (m d nregs : Nat) : State :=
  List.replicate m 1 :: List.replicate m 1 :: List.replicate d 1 :: List.replicate (nregs - 3) []

def measureEqBit (m d nregs : Nat) : Nat × Nat × Nat × Nat :=
  let s0 := mkEqDst m d nregs
  let L := (Compile.encodeTape s0).length
  let M1 := Compile.compareRegsTM s0.length (s0.length + 1) 0 1
  let cfg1 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s0)] }
  let (steps1, cfgEnd) := runToHalt M1 cfg1 (60 * (L + 2) * (L + 2))
  let tape := match cfgEnd.tapes with | (_, _, t) :: _ => t | [] => []
  let M2 := (compileOp (Op.clear 2)).M
  let cfg2 : FlatTMConfig := { state_idx := M2.start, tapes := [([], 0, tape)] }
  let (steps2, _) := runToHalt M2 cfg2 (60 * (L + 2) * (L + 2))
  let total := steps1 + 1 + steps2 + 4
  (total, L, budget1 L, total * 100 / budget1 L)

#eval measureEqBit 8 8 5     -- ~50%
#eval measureEqBit 12 12 5   -- ~50%
#eval measureEqBit 14 14 4   -- ~61%

/-! ## Finding 2 — per-iteration `compareBodyTM` real slope (~13·L) vs the
provable loose bound (~18·L). `sc1,sc2` placed at the register-list END (the
loop's real operating position), so every navigation is Θ(L). -/

def mkEnd (nlead a b : Nat) : State :=
  List.replicate nlead [] ++ [List.replicate a 1, List.replicate b 1]

def measureBody (nlead a b : Nat) : Nat × Nat × Nat :=
  let s := mkEnd nlead a b
  let M := Compile.compareBodyTM nlead (nlead + 1)
  let cfg : FlatTMConfig := { state_idx := M.start, tapes := [([], 0, Compile.encodeTape s)] }
  let L := (Compile.encodeTape s).length
  (stepsToHalt M cfg (1000 * (L + 2)), L, 18 * L)   -- real ≈ 13·L < loose 18·L

#eval measureBody 4 8 8
#eval measureBody 8 16 16
#eval measureBody 16 16 16

/-! ## Finding 3 — the loosened budget gives comfortable margin.
`(realFull, budget1, budget1_loose)`: real << loose, and the provable loose
cascade (≈ 1.7× real, see Finding 2) also fits `budget1_loose`. -/

def marginCheck (m nregs : Nat) : Nat × Nat × Nat :=
  let (steps, L, _, _) := measureCRT m nregs
  (steps, budget1 L, budget1_loose L)

#eval marginCheck 16 4
#eval marginCheck 24 4

end EqBitBudgetProbe
