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

/-! ============================================================================
## ★ WORST-CASE RE-VALIDATION (top-down, 2026-06-21) — the de-risking gate.

The 2026-06-21 bottom-up RISK FINDING claimed the `compareRegsTM` working tape is
`L4 ≈ 3·(op-input L)` and that the iteration-explicit provable bounds sum to
`~133·op-L²` vs the `const-72` ceiling `144·op-L²` — a fragile ~92% margin.

This section re-validates that claim at the TRUE worst case. Two corrections it
checks:

  (1) `L4 = op-L + |g1| + |g2| + 2`, and since `src1`/`src2` **coexist in the
      same input state** `s`, `|g1| + |g2| ≤ State.size s = op-L − s.length − 2`.
      Hence `L4 < 2·op-L` — NOT `3·op-L`. (`encodeTape_length : op-L = size + len + 2`.)

  (2) The per-stage worst cases are MUTUALLY EXCLUSIVE: a long match (loop
      expensive) forces short leftover suffixes (cleanup cheap), and vice versa
      (`|c_i| = |g_i| − matchLen`). Summing each stage's independent worst case
      (what the finding did) double-counts. The JOINT worst case is far smaller.

`measureWorst` computes, at a given operand profile, the REAL steps AND the
symbolic provable iteration-explicit bound (exactly what bottom-up will thread),
and compares both to the contract ceiling at const 54 (current) and 72.
============================================================================ -/

/-- Longest common prefix length of two unary/bit blocks (= `matchLen`). -/
def commonPrefix : List Nat → List Nat → Nat
  | a :: as, b :: bs => if a = b then 1 + commonPrefix as bs else 0
  | _, _ => 0

/-- The contract ceiling for `eqBit` (cost = 1) at quadratic constant `K`:
`(K·L² + K·L + (10/3)·K)·2`. (`opBudgetLoosen` uses 180 = 6·30 for K = 54.) -/
def ceilingAt (K opL : Nat) : Nat := (K * opL * opL + K * opL + (K * 10 / 3)) * 2

/-- `mB n` = an `n`-bit unary block. -/
def mB (n : Nat) : List Nat := List.replicate n 1

/-- The PROVABLE iteration-explicit bound for the full `opEqBit`, composed exactly
as bottom-up will (every stage bounded by the working tape `L4`, joint constraints
`matchLen ≤ |g_i|`, `|c_i| = |g_i| − matchLen` threaded). Uses the TIGHT cleanup +
clear bounds (the d2-iv target). -/
def provableTight (g1 g2 dst0 : List Nat) (opL : Nat) : Nat :=
  let l1 := g1.length
  let l2 := g2.length
  let ml := commonPrefix g1 g2
  let c1 := l1 - ml
  let c2 := l2 - ml
  let L4 := opL + l1 + l2 + 2           -- working tape after both copies
  let grow    := 4 * L4 + 21
  let copy1   := (l1 + 1) * (5 * L4 + 23) + 3 * L4 + 4
  let copy2   := (l2 + 1) * (5 * L4 + 23) + 3 * L4 + 4
  let loop    := (ml + 1) * (24 * L4 + 45)
  let verdict := 6 * L4 + 2
  let cleanup := (c1 + c2 + 1) * (6 * L4 + 13) + (8 * L4 + 25)   -- tight target
  let clrDst  := (dst0.length + 1) * (6 * L4 + 13)               -- d1 wrapper, tight
  grow + 1 + copy1 + 1 + copy2 + 1 + loop + 1 + verdict + 1 + cleanup + 1 + clrDst + 8

/-- The PROVABLE bound using the CURRENTLY-PROVEN (collapsed) cleanup `18L4²` and
clear `9L4²` — i.e. what bottom-up gets WITHOUT tightening cleanup/clear. -/
def provableCollapsed (g1 g2 dst0 : List Nat) (opL : Nat) : Nat :=
  let l1 := g1.length
  let l2 := g2.length
  let ml := commonPrefix g1 g2
  let L4 := opL + l1 + l2 + 2
  let grow    := 4 * L4 + 21
  let copy1   := (l1 + 1) * (5 * L4 + 23) + 3 * L4 + 4
  let copy2   := (l2 + 1) * (5 * L4 + 23) + 3 * L4 + 4
  let loop    := (ml + 1) * (24 * L4 + 45)
  let verdict := 6 * L4 + 2
  let cleanup := 18 * L4 * L4 + 8 * L4 + 45     -- currently proven (collapsed)
  let clrDst  := 9 * L4 * L4 + 9                 -- currently proven (collapsed)
  grow + 1 + copy1 + 1 + copy2 + 1 + loop + 1 + verdict + 1 + cleanup + 1 + clrDst + 8

/-- The DECOUPLED-pessimistic provable bound: loop bounded by `l1` (not the real
`matchLen`) AND cleanup bounded by `l1+l2` (not the real leftover `c1+c2`) — i.e.
`nlinarith` makes NO use of the `matchLen + leftover ≤ |g|` trade-off (the exact
over-counting the 2026-06-21 finding did, but now with the corrected `L4 < 2·opL`).
This is the loosest bound bottom-up could honestly thread; if even THIS fits, the
final arithmetic is robust. Tight cleanup/clear. -/
def provableDecoupled (g1 g2 dst0 : List Nat) (opL : Nat) : Nat :=
  let l1 := g1.length
  let l2 := g2.length
  let L4 := opL + l1 + l2 + 2
  let grow    := 4 * L4 + 21
  let copy1   := (l1 + 1) * (5 * L4 + 23) + 3 * L4 + 4
  let copy2   := (l2 + 1) * (5 * L4 + 23) + 3 * L4 + 4
  let loop    := (l1 + 1) * (24 * L4 + 45)            -- matchLen relaxed to l1
  let verdict := 6 * L4 + 2
  let cleanup := (l1 + l2 + 1) * (6 * L4 + 13) + (8 * L4 + 25)  -- c1+c2 relaxed to l1+l2
  let clrDst  := (dst0.length + 1) * (6 * L4 + 13)
  grow + 1 + copy1 + 1 + copy2 + 1 + loop + 1 + verdict + 1 + cleanup + 1 + clrDst + 8

def decoupledPct (g1 g2 dst0 : List Nat) (nfill : Nat) : Nat × Nat × Nat :=
  let s0 : State := g1 :: g2 :: dst0 :: List.replicate nfill []
  let opL := (Compile.encodeTape s0).length
  let pD := provableDecoupled (State.get s0 0) (State.get s0 1) dst0 opL
  (pD, pD * 100 / ceilingAt 54 opL, pD * 100 / ceilingAt 72 opL)

#eval decoupledPct (mB 24) (mB 24) [] 2        -- equal
#eval decoupledPct (2 :: mB 23) (mB 24) [] 2   -- mismatch
#eval decoupledPct (mB 40) (mB 2) [] 2         -- one-big
#eval decoupledPct (mB 16) (mB 16) (mB 16) 2   -- big-dst

def decoupledFits54 (g1 g2 dst0 : List Nat) (nfill : Nat) : Bool :=
  let (pD, p54, _) := decoupledPct g1 g2 dst0 nfill
  let _ := pD
  p54 ≤ 100

#eval decoupledFits54 (mB 24) (mB 24) [] 2
#eval decoupledFits54 (2 :: mB 23) (mB 24) [] 2
#eval decoupledFits54 (mB 40) (mB 2) [] 2
#eval decoupledFits54 (mB 16) (mB 16) (mB 16) 2

/-- Full re-validation at one operand profile. `g1`/`g2` = the two compared
registers, `dst0` = the answer register's prior content, `nfill` extra empties.
Returns:
`(opL, L4, ⌈100·L4/opL⌉, realSteps, provTight, provCollapsed, ceil54, ceil72,
  tightPct54, collapsedPct72)`. -/
def measureWorst (g1 g2 dst0 : List Nat) (nfill : Nat) : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let s0 : State := g1 :: g2 :: dst0 :: List.replicate nfill []
  let opL := (Compile.encodeTape s0).length
  let g1' := State.get s0 0
  let g2' := State.get s0 1
  let L4 := opL + g1'.length + g2'.length + 2
  -- real steps: compareRegsTM (src1=0, src2=1) then clear dst (=2)
  let M1 := Compile.compareRegsTM s0.length (s0.length + 1) 0 1
  let cfg1 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s0)] }
  let (steps1, cfgEnd) := runToHalt M1 cfg1 (80 * (L4 + 2) * (L4 + 2))
  let tape := match cfgEnd.tapes with | (_, _, t) :: _ => t | [] => []
  let M2 := (compileOp (Op.clear 2)).M
  let cfg2 : FlatTMConfig := { state_idx := M2.start, tapes := [([], 0, tape)] }
  let (steps2, _) := runToHalt M2 cfg2 (80 * (L4 + 2) * (L4 + 2))
  let real := steps1 + 1 + steps2 + 4
  let pT := provableTight g1' g2' dst0 opL
  let pC := provableCollapsed g1' g2' dst0 opL
  let c54 := ceilingAt 54 opL
  let c72 := ceilingAt 72 opL
  (opL, L4, L4 * 100 / opL, real, pT, pC, c54, c72, pT * 100 / c54, pC * 100 / c72)

/-! ### Profile sweep. The cases span the operand trade-off: equal (max match,
min cleanup), early-mismatch (min match, max cleanup), and one-big-one-small
(max single |g|, the finding's feared case). -/

-- equal operands (longest loop; cleanup ~empty)
#eval measureWorst (mB 16) (mB 16) [] 2
#eval measureWorst (mB 24) (mB 24) [] 2
-- early mismatch (loop ~0; longest cleanup) — g1 = 0…, g2 = 1…
#eval measureWorst (2 :: mB 23) (mB 24) [] 2
-- prefix match then diverge (both loop and cleanup nontrivial)
#eval measureWorst (mB 12 ++ [2] ++ mB 11) (mB 12 ++ [1] ++ mB 11) [] 2
-- one big, one small (the finding's |g1|≈op-L fear) — match bounded by small |g2|
#eval measureWorst (mB 40) (mB 2) [] 2
-- big dst answer register (max d1 clear)
#eval measureWorst (mB 16) (mB 16) (mB 16) 2

/-! ### ★ The `src1 = src2` (self-compare) edge case — the ONLY scenario where
`L4 ≈ 3·op-L` is real (both scratch copies duplicate the SAME giant register).
`s0 = [giant, dst0, fills…]`, comparing reg 0 with itself. Here `matchLen = |g|`
(full match), `c1 = c2 = []` (cleanup is cheap/linear). Returns
`(opL, L4, 100·L4/opL, real, provTight, ceil54, ceil72, tightPct54, tightPct72)`. -/
def measureSelf (giant dst0 : List Nat) (nfill : Nat) : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let s0 : State := giant :: dst0 :: List.replicate nfill []
  let opL := (Compile.encodeTape s0).length
  let g := State.get s0 0
  let L4 := opL + g.length + g.length + 2
  let M1 := Compile.compareRegsTM s0.length (s0.length + 1) 0 0
  let cfg1 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s0)] }
  let (steps1, cfgEnd) := runToHalt M1 cfg1 (80 * (L4 + 2) * (L4 + 2))
  let tape := match cfgEnd.tapes with | (_, _, t) :: _ => t | [] => []
  let M2 := (compileOp (Op.clear 1)).M
  let cfg2 : FlatTMConfig := { state_idx := M2.start, tapes := [([], 0, tape)] }
  let (steps2, _) := runToHalt M2 cfg2 (80 * (L4 + 2) * (L4 + 2))
  let real := steps1 + 1 + steps2 + 4
  let pT := provableTight g g dst0 opL
  (opL, L4, L4 * 100 / opL, real, pT, ceilingAt 54 opL, ceilingAt 72 opL,
   pT * 100 / ceilingAt 54 opL, pT * 100 / ceilingAt 72 opL)

-- giant self-compared register, tiny dst (the joint worst: loop & copies max, clrDst linear)
-- NOTE: kept small — the interpreter runs the real TM; the SYMBOLIC `selfBudget_54/72`
-- theorems below prove this case for ALL sizes. Real steps shown only as a spot-check.
#eval measureSelf (mB 10) [] 1
#eval measureSelf (mB 14) [] 1
-- giant src AND sizeable dst — but they coexist, so dst eats into the budget the other way
#eval measureSelf (mB 8) (mB 6) 1

/-- **VERDICT predicates.** `tightFits54` = the tight provable bound fits the
CURRENT const-54 ceiling. `collapsedFits72` = even without tightening
cleanup/clear, the provable bound fits the const-72 ceiling. -/
def tightFits54 (g1 g2 dst0 : List Nat) (nfill : Nat) : Bool :=
  let (_, _, _, _, pT, _, c54, _, _, _) := measureWorst g1 g2 dst0 nfill
  pT ≤ c54

def collapsedFits72 (g1 g2 dst0 : List Nat) (nfill : Nat) : Bool :=
  let (_, _, _, _, _, pC, _, c72, _, _) := measureWorst g1 g2 dst0 nfill
  pC ≤ c72

#eval tightFits54 (mB 24) (mB 24) [] 2          -- equal worst
#eval tightFits54 (2 :: mB 23) (mB 24) [] 2     -- mismatch worst
#eval tightFits54 (mB 40) (mB 2) [] 2           -- one-big worst
#eval collapsedFits72 (mB 24) (mB 24) [] 2
#eval collapsedFits72 (2 :: mB 23) (mB 24) [] 2
#eval collapsedFits72 (mB 40) (mB 2) [] 2

/-! ## ★ The final-arithmetic de-risking THEOREM (proven, const 54).

The `#eval`s above measure; this THEOREM proves (symbolically, all operand
profiles at once) that the tight iteration-explicit stage sum fits the CURRENT
const-54 contract ceiling. Lift this into `Compile.lean` next to
`Compile.opBudgetLoosen` when assembling `compareRegsTM_run_*` (d2-iv step 3) /
the d1 `opEqBit` wrapper — the constraints are exactly what the run lemmas supply:

- `hml1/hml2 : matchLen ≤ |g1|, |g2|`  (`Compile.matchLen_le_*`, or `min`),
- `hc : c1 + c2 ≤ l1 + l2`             (`c_i = g_i.drop matchLen`, `length_drop`),
- `hsum : l1 + l2 + 2 ≤ opL`           (`|g1|+|g2| ≤ State.size = opL − len − 2`,
                                         `encodeTape_length`),
- `hdlen : dlen ≤ opL`                 (`|dst| ≤ State.size ≤ opL`).

`L4 = opL + l1 + l2 + 2` is the working tape (`< 2·opL` by `hsum`). Each stage's
budget below is its PROVEN run-lemma bound, evaluated at the uniform upper bound
`L4` (monotone in tape length). **No constant bump (54 suffices), no design
change.** -/
theorem compareBudget_arith_fits54
    (opL l1 l2 ml c1 c2 dlen : Nat)
    (hml1 : ml ≤ l1) (hml2 : ml ≤ l2)
    (hc : c1 + c2 ≤ l1 + l2)
    (hsum : l1 + l2 + 2 ≤ opL)
    (hdlen : dlen ≤ opL) :
    (4*(opL+l1+l2+2)+21) + 1
    + ((l1+1)*(5*(opL+l1+l2+2)+23) + 3*(opL+l1+l2+2)+4) + 1
    + ((l2+1)*(5*(opL+l1+l2+2)+23) + 3*(opL+l1+l2+2)+4) + 1
    + ((ml+1)*(24*(opL+l1+l2+2)+45)) + 1
    + (6*(opL+l1+l2+2)+2) + 1
    + ((c1+c2+1)*(6*(opL+l1+l2+2)+13) + (8*(opL+l1+l2+2)+25)) + 1
    + ((dlen+1)*(6*(opL+l1+l2+2)+13)) + 8
    ≤ (54*opL*opL + 54*opL + 180) * 2 := by
  nlinarith [hml1, hml2, hc, hsum, hdlen,
             Nat.mul_le_mul hml1 (Nat.le_refl (opL+l1+l2+2)),
             Nat.zero_le (l1*l2), Nat.zero_le (l1*opL), Nat.zero_le (l2*opL),
             Nat.zero_le (ml*opL), Nat.zero_le (dlen*opL), Nat.zero_le (l1*l1),
             Nat.zero_le (l2*l2), Nat.zero_le (ml*l1), Nat.zero_le (ml*l2)]

/-! ### The `src1 = src2` (self-compare) degenerate cases, proven symbolically.

`l1 = l2 = l`, `ml = l`, `c1 = c2 = 0`, `L4 = opL + 2l + 2` (can reach `≈ 3·opL`).
Two sub-cases by whether `dst` overlaps the (giant) source:

- **`src ≠ dst`** (`eqBit dst r r`, `r ≠ dst`): the joint constraint is
  `l + dlen + 2 ≤ opL` (giant src and dst coexist as distinct registers). Fits
  **const-54**. (`selfBudget_neqDst_54`.)
- **`src = dst`** (`eqBit r r r`, fully degenerate): `dlen = l` and they are the
  SAME register, so `l + dlen` over-counts — only `l ≤ opL` holds, and `L4 ≈ 3opL`
  with `clrDst` also quadratic. This busts const-54 but fits **const-72** (the one
  case that needs 72; free vs `physStepBudget`, `72 = 8·9`, `L ≤ G`). -/
theorem selfBudget_neqDst_54 (opL l dlen : Nat) (hsum : l + dlen + 2 ≤ opL) :
    (4*(opL+l+l+2)+21) + 1
    + ((l+1)*(5*(opL+l+l+2)+23) + 3*(opL+l+l+2)+4) + 1
    + ((l+1)*(5*(opL+l+l+2)+23) + 3*(opL+l+l+2)+4) + 1
    + ((l+1)*(24*(opL+l+l+2)+45)) + 1
    + (6*(opL+l+l+2)+2) + 1
    + ((0+1)*(6*(opL+l+l+2)+13) + (8*(opL+l+l+2)+25)) + 1
    + ((dlen+1)*(6*(opL+l+l+2)+13)) + 8
    ≤ (54*opL*opL + 54*opL + 180) * 2 := by
  nlinarith [hsum, Nat.zero_le (l*opL), Nat.zero_le (l*l), Nat.zero_le (dlen*opL),
             Nat.zero_le (l*dlen), Nat.mul_le_mul hsum hsum]

theorem selfBudget_eqDst_72 (opL l : Nat) (hl : l + 3 ≤ opL) :
    -- `l + 3 ≤ opL`: register `r` (size `l`) occupies the tape, `len ≥ 1`, so
    -- `opL = State.size + len + 2 ≥ l + 3`. (Without it, `l = opL` is spuriously
    -- "allowed" and the additive gadget overheads bust the small-`opL` ceiling.)
    (4*(opL+l+l+2)+21) + 1
    + ((l+1)*(5*(opL+l+l+2)+23) + 3*(opL+l+l+2)+4) + 1
    + ((l+1)*(5*(opL+l+l+2)+23) + 3*(opL+l+l+2)+4) + 1
    + ((l+1)*(24*(opL+l+l+2)+45)) + 1
    + (6*(opL+l+l+2)+2) + 1
    + ((0+1)*(6*(opL+l+l+2)+13) + (8*(opL+l+l+2)+25)) + 1
    + ((l+1)*(6*(opL+l+l+2)+13)) + 8          -- dlen = l (dst IS the source)
    ≤ (72*opL*opL + 72*opL + 240) * 2 := by
  nlinarith [hl, Nat.mul_le_mul hl hl, Nat.mul_le_mul hl (Nat.le_refl opL),
             Nat.zero_le l, Nat.zero_le opL, Nat.zero_le (l*l), Nat.zero_le (l*opL)]

end EqBitBudgetProbe
