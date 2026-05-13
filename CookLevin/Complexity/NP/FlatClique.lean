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

/-- Classical Boolean decider for cliqueRel.
TODO(step14): replace with an explicit computable Bool function. -/
noncomputable def cliqueRelDec : (fgraph × Nat) × List fvertex → Bool :=
  fun ⟨⟨G, k⟩, l⟩ => decide (fgraph_wf G ∧ isfKClique k G l)

theorem cliqueRel_iff (Gk : fgraph × Nat) (l : List fvertex) :
    cliqueRel Gk l ↔ cliqueRelDec ⟨Gk, l⟩ = true := by
  simp [cliqueRel, cliqueRelDec, decide_eq_true_eq]

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

theorem FlatClique_in_NP : inNP FlatClique := by
  refine inNP_intro FlatClique cliqueRel ?_ ?_
  · -- inTimePoly: classical decider cliqueRelDec
    exact ⟨fun n => n + 1,
      ⟨cliqueRelDec, fun xy => (cliqueRel_iff xy.1 xy.2)⟩,
      ⟨1, ⟨2, 1, by intro n hn; simp [pow_one]; omega⟩⟩,
      fun x x' h => Nat.add_le_add_right h 1⟩
  · -- polyCertRel: every FlatClique instance has a polynomially-bounded certificate
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
