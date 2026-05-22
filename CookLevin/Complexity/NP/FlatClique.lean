import Complexity.Complexity.NP
import Complexity.Complexity.Definitions
import Mathlib.Tactic

set_option autoImplicit false
open Classical

def isfClique (G : fgraph) (l : List fvertex) : Prop :=
  list_ofFlatType G.1 l ∧
    l.Nodup ∧
    ∀ v₁ v₂, v₁ ∈ l → v₂ ∈ l → v₁ ≠ v₂ → (v₁, v₂) ∈ G.2

def isfKClique (k : Nat) (G : fgraph) (l : List fvertex) : Prop :=
  isfClique G l ∧ l.length = k

def FlatClique : (fgraph × Nat) → Prop
  | (G, k) => ∃ l, fgraph_wf G ∧ isfKClique k G l

/-- The certificate relation: a list of vertices witnessing a k-clique. -/
def cliqueRel : (fgraph × Nat) → List fvertex → Prop
  | (G, k), l => fgraph_wf G ∧ isfKClique k G l

/-- A list of `Nat`s whose elements are all strictly less than `B` has
`encodable.size ≤ |xs| * B + |xs|`. Each entry contributes `x + 1 ≤ B + 1`
to the size and there are `|xs|` entries. -/
private theorem encodable_size_listNat_bounded (B : Nat) :
    ∀ (xs : List Nat), list_ofFlatType B xs →
      encodable.size xs ≤ xs.length * B + xs.length
  | [], _ => by simp [encodable.size]
  | x :: xs, h => by
      obtain ⟨hx, hxs⟩ := list_ofFlatType_cons.mp h
      have ih := encodable_size_listNat_bounded B xs hxs
      rw [encodable_size_list_cons]
      have hsx : (encodable.size x : Nat) = x := rfl
      rw [hsx]
      simp only [List.length_cons]
      have hxB : x + 1 ≤ B := hx
      nlinarith

/-- Size bound for clique certificates: quadratic in the input size.
The clique list has length `k ≤ size(G,k)` with each vertex `< G.1 ≤ size(G,k)`,
so `encodable.size l ≤ k * (G.1 + 1) ≤ size(G,k) ^ 2`. -/
theorem clique_size_bound (Gk : fgraph × Nat) (l : List fvertex)
    (hl : cliqueRel Gk l) :
    encodable.size l ≤ encodable.size Gk ^ 2 + 1 := by
  obtain ⟨G, k⟩ := Gk
  rcases hl with ⟨_hwf, ⟨⟨hOfType, _hNodup, _hAdj⟩, hlen⟩⟩
  set S := encodable.size ((G, k) : fgraph × Nat)
  -- Bound the size of the certificate list.
  have hSizeL : encodable.size l ≤ k * G.1 + k := by
    have h := encodable_size_listNat_bounded G.1 l hOfType
    rw [hlen] at h
    linarith
  -- Bound the size of the (G, k) input from below.
  have hSGk : G.1 + k + 1 ≤ S := by
    have hPair : encodable.size ((G, k) : fgraph × Nat) =
        encodable.size G + encodable.size k + 1 := rfl
    have hG : encodable.size G = encodable.size G.1 + encodable.size G.2 + 1 := rfl
    have hNat1 : (encodable.size G.1 : Nat) = G.1 := rfl
    have hNat2 : (encodable.size k : Nat) = k := rfl
    show G.1 + k + 1 ≤ encodable.size ((G, k) : fgraph × Nat)
    rw [hPair, hG, hNat1, hNat2]
    linarith [Nat.zero_le (encodable.size G.2)]
  -- Combine: k * (G.1 + 1) ≤ S * S = S ^ 2.
  have hKle : k ≤ S := by linarith
  have hG1le : G.1 + 1 ≤ S := by linarith
  have hProd : k * (G.1 + 1) ≤ S * S := Nat.mul_le_mul hKle hG1le
  calc
    encodable.size l ≤ k * G.1 + k := hSizeL
    _ = k * (G.1 + 1) := by ring
    _ ≤ S * S := hProd
    _ = S ^ 2 := by ring
    _ ≤ S ^ 2 + 1 := by linarith

-- `FlatClique_in_NP : inNP FlatClique` is proved in
-- `Complexity/Complexity/Deciders/CliqueRelTM.lean` after Step 6 of
-- PART2.md v2 (moved there for the same reason as `sat_NP`: the
-- `inTimePoly` slot needs CliqueRelTM.inTimePolyTM_cliqueRel, whose
-- construction lives downstream of this file).
