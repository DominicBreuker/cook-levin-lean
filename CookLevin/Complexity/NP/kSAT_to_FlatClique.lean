import Complexity.Complexity.NP
import Complexity.NP.kSAT
import Complexity.NP.FlatClique

set_option autoImplicit false

theorem kSAT_to_FlatClique_poly (k : Nat) : kSAT k ⪯p FlatClique := by
  simp [reducesPolyMO]
