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

/-- Size bound for clique certificates: quadratic in the input size.
Proof sketch: the clique list has at most k ≤ size(G,k) vertices,
each with value < G.1 ≤ size(G,k), giving a quadratic size bound. -/
theorem clique_size_bound (Gk : fgraph × Nat) (l : List fvertex)
    (hl : cliqueRel Gk l) :
    encodable.size l ≤ encodable.size Gk ^ 2 + 1 := by
  sorry

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
