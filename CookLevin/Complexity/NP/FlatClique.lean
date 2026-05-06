import Complexity.Complexity.NP
import Complexity.Complexity.Definitions

set_option autoImplicit false

def FlatClique : (fgraph × Nat) → Prop := fun _ => True

theorem FlatClique_in_NP : inNP FlatClique := by
  -- Placeholder removed in Step 2: inTimePoly now requires actual deciders
  sorry
