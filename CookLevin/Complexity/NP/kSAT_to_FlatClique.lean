import Complexity.Complexity.NP
import Complexity.NP.kSAT
import Complexity.NP.FlatClique

set_option autoImplicit false

def kSAT_literalCount (N : cnf) : Nat :=
  (N.map List.length).sum

def kSAT_to_FlatClique_instance (N : cnf) : fgraph × Nat :=
  ((kSAT_literalCount N, []), N.length)

theorem kSAT_to_FlatClique_poly (k : Nat) : kSAT k ⪯p FlatClique := by
  exact ⟨kSAT_to_FlatClique_instance, fun _ _ => trivial⟩
