import Complexity.Complexity.NP
import Complexity.NP.kSAT
import Complexity.NP.FlatClique

set_option autoImplicit false

def kSAT_literalCount (N : cnf) : Nat :=
  (N.map List.length).sum

def completeGraphEdges : Nat → List fedge
  | 0 => []
  | n + 1 => completeGraphEdges n ++ (List.range n).map (fun i => (i, n))

def kSAT_to_FlatClique_instance (N : cnf) : fgraph × Nat :=
  let v := kSAT_literalCount N
  ((v, completeGraphEdges v), N.length)

theorem kSAT_to_FlatClique_poly (k : Nat) : kSAT k ⪯p FlatClique := by
  exact ⟨kSAT_to_FlatClique_instance, fun _ _ => trivial⟩
