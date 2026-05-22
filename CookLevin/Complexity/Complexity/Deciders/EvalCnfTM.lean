import Complexity.Complexity.TMDecider
import Complexity.NP.SAT

set_option autoImplicit false

/-! # The SAT-verifier TM (Part 2, Step 11 destination)

This file owns the TM-backed decider for the SAT verification
relation `fun (N, a) => satisfiesCnf a N` — i.e., the witness that
`SAT ∈ NP`.

**Status.** Step 2 of `PART2.md` v2 lands this file as an
*interface-first* stub: the `decider` body is a single labelled
`sorry`, but its *type* and the surrounding time-bound infrastructure
are final. From Step 4 onward, `sat_NP` (`Complexity/NP/SAT.lean`)
will consume `inTimePolyTM_evalCnf` directly. The construction of
`decider` itself is completed in Step 11 of the plan.

**Time budget.** We pick `timeBound n := (n + 1) ^ 3`. The eventual
construction (4 tapes: input, var-buffer, per-clause OR accumulator,
per-CNF AND accumulator) has a doubly-nested scan — clauses ×
literals × variable lookups — whose worst-case cost is bounded by
`|N| · |c| · |a|`, which fits comfortably inside `(n + 1) ^ 3` for
the natural input-size measure `n = encodable.size (N, a)`. The
cubic budget is generous on purpose so the bookkeeping in Step 11
has slack.
-/

namespace EvalCnfTM

/-- Polynomial time budget for `evalCnfTM`. -/
def timeBound (n : Nat) : Nat := (n + 1) ^ 3

theorem timeBound_inOPoly : inOPoly timeBound := by
  refine ⟨3, ⟨8, 1, ?_⟩⟩
  intro n hn
  -- For n ≥ 1: (n + 1) ≤ n + n, hence (n+1)^3 ≤ (n+n)^3 = 8·n^3.
  have hle : n + 1 ≤ n + n := Nat.add_le_add_left hn n
  show (n + 1) ^ 3 ≤ 8 * n ^ 3
  calc (n + 1) ^ 3
      ≤ (n + n) ^ 3 := Nat.pow_le_pow_left hle 3
    _ = 8 * n ^ 3 := by ring

theorem timeBound_monotonic : monotonic timeBound :=
  fun _ _ h => Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 3

/-- TM-backed decider for the SAT verification relation
`fun (N, a) => satisfiesCnf a N`.

**Construction deferred to Step 11 of `PART2.md` v2**
(`TODO(Part2-followup:EvalCnfTM)`). The interface — encoding,
acceptance / rejection state codes, time budget — is committed; only
the body of the witness is `sorry`. Downstream consumers (`sat_NP`,
`P_NP_incl`) bind against `inTimePolyTM_evalCnf` below from Step 4
onward, so this gap does not propagate into their signatures. -/
def decider : DecidesBy
    (fun Na : cnf × assgn => satisfiesCnf Na.2 Na.1) timeBound :=
  sorry  -- TODO(Part2-followup:EvalCnfTM)

/-- `fun (N, a) ↦ satisfiesCnf a N` is decided by a polynomial-time
Turing machine — the headline statement consumed by `sat_NP`. -/
theorem inTimePolyTM_evalCnf :
    inTimePolyTM (fun Na : cnf × assgn => satisfiesCnf Na.2 Na.1) :=
  ⟨timeBound, ⟨decider⟩, timeBound_inOPoly, timeBound_monotonic⟩

end EvalCnfTM

/-! ## `SAT ∈ NP` (Step 5 of `PART2.md` v2)

Originally proved in `Complexity/NP/SAT.lean`. After Step 4's
framework swap the `inTimePoly` slot needs a TM-backed witness
(`EvalCnfTM.inTimePolyTM_evalCnf`), and EvalCnfTM imports
`Complexity.NP.SAT`, so the cleanest place for the theorem is here
— right next to its `inTimePoly` ingredient. The fully-qualified
name remains `SAT_inNP.sat_NP`, so consumers (`kSAT_to_SAT.lean`,
`SAT/CookLevin.lean`) need no change. -/

namespace SAT_inNP

theorem sat_NP : inNP SAT := by
  refine inNP_intro SAT (fun N a => satisfiesCnf a N) ?_ ?_
  · -- inTimePoly slot: the TM-backed evalCnfTM decider.
    exact EvalCnfTM.inTimePolyTM_evalCnf
  · -- polyCertRel slot: every SAT instance has a polynomially-bounded
    -- certificate via `compressAssignment` (unchanged from pre-Step-4).
    refine ⟨⟨fun n => n ^ 2 + 1, ?_, ?_, ?_, ?_⟩⟩
    · -- sound: a satisfying assignment witnesses SAT
      intro N a h; exact ⟨a, h⟩
    · -- complete: compress the satisfying assignment to a bounded one
      intro N ⟨a, ha⟩
      exact ⟨compressAssignment a N, (compressAssignment_cnf_equiv a N).mp ha,
             compressAssignment_size_bound a N⟩
    · -- inOPoly: n^2 + 1 is polynomial
      exact ⟨2, ⟨2, 1, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩
    · -- monotonic
      intro a b h; nlinarith [Nat.pow_le_pow_left h 2]

end SAT_inNP
