import Complexity.Complexity.TMDecider
import Complexity.NP.FlatClique
import Complexity.Lang

set_option autoImplicit false

/-! # The FlatClique-verifier — closed via the Lang layer (Part 3.5)

This file owns the TM-backed decider for the FlatClique verification
relation
`fun (Gkl : (fgraph × Nat) × List fvertex) => cliqueRel Gkl.1 Gkl.2`
— i.e., the witness that `FlatClique ∈ NP`.

**Skeleton status (post-pivot, May 2026).** The construction is now
routed through the higher-level `Lang` layer (Part 3 of
`ROADMAP.md`). The original single `sorry` for `decider` is now
decomposed into a handful of small, focused sorrys (the program
itself, the encoding, encoding-size bound, correctness, cost bound).

Note: `inTimePolyTM_cliqueRel` keeps its full name + signature so
`FlatClique_in_NP` (below) does not need to change.
-/

namespace CliqueRelTM

open Complexity.Lang

/-- Polynomial time budget for `cliqueRelDecTM`. -/
def timeBound (n : Nat) : Nat := (n + 1) ^ 3

theorem timeBound_inOPoly : inOPoly timeBound := by
  refine ⟨3, ⟨8, 1, ?_⟩⟩
  intro n hn
  have hle : n + 1 ≤ n + n := Nat.add_le_add_left hn n
  show (n + 1) ^ 3 ≤ 8 * n ^ 3
  calc (n + 1) ^ 3
      ≤ (n + n) ^ 3 := Nat.pow_le_pow_left hle 3
    _ = 8 * n ^ 3 := by ring

theorem timeBound_monotonic : monotonic timeBound :=
  fun _ _ h => Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 3

/-! ## The verifier program in the layer -/

/-- The FlatClique verifier as a `Lang.Cmd`.

**Skeleton stub.** Will be a concrete `Cmd` (~80 LOC of DSL) in
Part 3.5. The intended algorithm has four sub-checks:
1. `fgraph_wf G` — linear scan with per-edge bound checks.
2. `l.length = k` — linear unary length compare.
3. `l.Nodup` — quadratic in `|l|`.
4. `isfClique G l` — for each pair in `l × l`, scan `G.2`. -/
noncomputable def cliqueRelCmd : Cmd := sorry  -- TODO(Part3.5-Cmd)

/-- How to lay out a `((fgraph, Nat), List fvertex)` input as a
`Lang.State`. -/
noncomputable def cliqueRelEncode :
    (fgraph × Nat) × List fvertex → State := sorry
  -- TODO(Part3.5-encode)

/-- The Lang-level decider witness for the FlatClique verifier. -/
noncomputable def cliqueRelDecidesLang :
    DecidesLang
      (fun Gkl : (fgraph × Nat) × List fvertex => cliqueRel Gkl.1 Gkl.2)
      timeBound where
  c := cliqueRelCmd
  encodeIn := cliqueRelEncode
  encodeIn_size := by intro x; sorry  -- TODO(Part3.5-encode-size)
  decides := by sorry                  -- TODO(Part3.5-correctness)
  cost_bound := by intro x; sorry      -- TODO(Part3.5-cost-bound)

/-- The Lang-level `inTimePolyLang` witness. -/
theorem inTimePolyLang_cliqueRel :
    inTimePolyLang
      (fun Gkl : (fgraph × Nat) × List fvertex => cliqueRel Gkl.1 Gkl.2) :=
  ⟨timeBound, ⟨cliqueRelDecidesLang⟩, timeBound_inOPoly, timeBound_monotonic⟩

/-- `fun ((G, k), l) ↦ cliqueRel (G, k) l` is decided by a
polynomial-time Turing machine — the headline statement consumed by
`FlatClique_in_NP`. -/
theorem inTimePolyTM_cliqueRel :
    inTimePolyTM
      (fun Gkl : (fgraph × Nat) × List fvertex => cliqueRel Gkl.1 Gkl.2) :=
  inTimePolyLang_to_inTimePoly inTimePolyLang_cliqueRel

end CliqueRelTM

/-! ## `FlatClique ∈ NP` (unchanged from the pre-pivot version) -/

theorem FlatClique_in_NP : inNP FlatClique := by
  refine inNP_intro FlatClique cliqueRel ?_ ?_
  · exact CliqueRelTM.inTimePolyTM_cliqueRel
  · refine ⟨⟨fun n => n ^ 2 + 1, ?_, ?_, ?_, ?_⟩⟩
    · rintro ⟨G, k⟩ l ⟨hwf, hclq⟩
      exact ⟨l, hwf, hclq⟩
    · rintro ⟨G, k⟩ ⟨l, hwf, hclq⟩
      exact ⟨l, ⟨hwf, hclq⟩, clique_size_bound _ l ⟨hwf, hclq⟩⟩
    · exact ⟨2, ⟨2, 1, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩
    · intro a b h; nlinarith [Nat.pow_le_pow_left h 2]
