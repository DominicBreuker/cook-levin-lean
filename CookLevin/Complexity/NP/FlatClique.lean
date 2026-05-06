import Complexity.Complexity.NP
import Complexity.Complexity.Definitions

set_option autoImplicit false

def isfClique (G : fgraph) (l : List fvertex) : Prop :=
  list_ofFlatType G.1 l ∧
    l.Nodup ∧
    ∀ v₁ v₂, v₁ ∈ l → v₂ ∈ l → v₁ ≠ v₂ → (v₁, v₂) ∈ G.2

def isfKClique (k : Nat) (G : fgraph) (l : List fvertex) : Prop :=
  isfClique G l ∧ l.length = k

def FlatClique : (fgraph × Nat) → Prop
  | (G, k) => ∃ l, fgraph_wf G ∧ isfKClique k G l

theorem FlatClique_in_NP : inNP FlatClique := by
  sorry
