import Complexity.Complexity.NP
import Complexity.Complexity.Definitions

set_option autoImplicit false

def FlatClique : (fgraph × Nat) → Prop := fun _ => True

theorem FlatClique_in_NP : inNP FlatClique := by
  sorry
