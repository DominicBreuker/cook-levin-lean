import Complexity.Complexity.TMDecider
import Complexity.NP.FlatClique

set_option autoImplicit false

/-! # The FlatClique-verifier TM (Part 2, Step 12 destination)

This file owns the TM-backed decider for the FlatClique verification
relation
`fun (Gkl : (fgraph × Nat) × List fvertex) => cliqueRel Gkl.1 Gkl.2`
— i.e., the witness that `FlatClique ∈ NP`.

**Status.** Step 3 of `PART2.md` v2 lands this file as an
*interface-first* stub: the `decider` body is a single labelled
`sorry`, but its *type* and the surrounding time-bound infrastructure
are final. From Step 6 onward, `FlatClique_in_NP`
(`Complexity/NP/FlatClique.lean`) consumes `inTimePolyTM_cliqueRel`
directly. The construction of `decider` itself is completed in
Step 12 of the plan.

**Time budget.** We pick `timeBound n := (n + 1) ^ 3`. The eventual
construction has three sub-checks:
1. `fgraph_wf G` — linear scan with per-edge bound checks.
2. `l.length = k` — linear.
3. `l.Nodup` — quadratic in `|l|` (pairwise comparison).
4. `isfClique G l` — for each pair (v₁, v₂) in `l × l` with v₁ ≠ v₂,
   verify `(v₁, v₂) ∈ G.2`, where each lookup scans the edge list.
   Cost is `O(|l|² · |E|)`, which is bounded by `O(n³)` for
   `n = encodable.size ((G, k), l)`.

The cubic budget thus comfortably absorbs the dominant `isfClique`
cost. As with `EvalCnfTM`, the bound is generous on purpose so the
Step 12 bookkeeping has slack.
-/

namespace CliqueRelTM

/-- Polynomial time budget for `cliqueRelDecTM`. -/
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

/-- TM-backed decider for the FlatClique verification relation
`fun (Gkl : (fgraph × Nat) × List fvertex) => cliqueRel Gkl.1 Gkl.2`.

**Construction deferred to Step 12 of `PART2.md` v2**
(`TODO(Part2-followup:CliqueRelTM)`). The interface — encoding,
acceptance / rejection state codes, time budget — is committed; only
the body of the witness is `sorry`. `FlatClique_in_NP` (Step 6
of the plan) binds against `inTimePolyTM_cliqueRel` below, so this
gap does not propagate into downstream signatures. -/
def decider : DecidesBy
    (fun Gkl : (fgraph × Nat) × List fvertex => cliqueRel Gkl.1 Gkl.2)
    timeBound :=
  sorry  -- TODO(Part2-followup:CliqueRelTM)

/-- `fun ((G, k), l) ↦ cliqueRel (G, k) l` is decided by a
polynomial-time Turing machine — the headline statement consumed by
`FlatClique_in_NP`. -/
theorem inTimePolyTM_cliqueRel :
    inTimePolyTM
      (fun Gkl : (fgraph × Nat) × List fvertex => cliqueRel Gkl.1 Gkl.2) :=
  ⟨timeBound, ⟨decider⟩, timeBound_inOPoly, timeBound_monotonic⟩

end CliqueRelTM

/-! ## `FlatClique ∈ NP` (Step 6 of `PART2.md` v2)

Originally proved in `Complexity/NP/FlatClique.lean`. After Step 4's
framework swap the `inTimePoly` slot needs a TM-backed witness
(`CliqueRelTM.inTimePolyTM_cliqueRel`), and CliqueRelTM imports
`Complexity.NP.FlatClique`, so the cleanest place for the theorem
is here. The fully-qualified name remains `FlatClique_in_NP`, so
consumers (`SAT/CookLevin.lean`) need no change. -/

theorem FlatClique_in_NP : inNP FlatClique := by
  refine inNP_intro FlatClique cliqueRel ?_ ?_
  · -- inTimePoly slot: the TM-backed cliqueRelDecTM decider.
    exact CliqueRelTM.inTimePolyTM_cliqueRel
  · -- polyCertRel slot: every FlatClique instance has a polynomially-bounded
    -- certificate (unchanged from pre-Step-4).
    refine ⟨⟨fun n => n ^ 2 + 1, ?_, ?_, ?_, ?_⟩⟩
    · -- sound: a valid clique list witnesses FlatClique
      rintro ⟨G, k⟩ l ⟨hwf, hclq⟩
      exact ⟨l, hwf, hclq⟩
    · -- complete: the witnessing list is a valid certificate
      rintro ⟨G, k⟩ ⟨l, hwf, hclq⟩
      exact ⟨l, ⟨hwf, hclq⟩, clique_size_bound _ l ⟨hwf, hclq⟩⟩
    · -- inOPoly
      exact ⟨2, ⟨2, 1, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩
    · -- monotonic
      intro a b h; nlinarith [Nat.pow_le_pow_left h 2]
