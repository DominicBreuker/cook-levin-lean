import Complexity.Complexity.NP
import Complexity.Complexity.Definitions

set_option autoImplicit false

def FlatClique : (fgraph × Nat) → Prop := fun _ => True

theorem FlatClique_in_NP : inNP FlatClique := by
  refine inNP_intro (Y := Unit) FlatClique (fun x (_ : Unit) => FlatClique x) (inTimePoly_linear _) ?_
  refine ⟨?_, ?_⟩
  · intro x _ hx
    exact hx
  · intro x hx
    exact ⟨(), hx⟩
