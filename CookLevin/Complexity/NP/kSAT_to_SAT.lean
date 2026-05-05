import Complexity.Complexity.NP
import Complexity.NP.SAT
import Complexity.NP.kSAT

set_option autoImplicit false

theorem kSAT_to_SAT (k : Nat) : kSAT k ⪯p SAT := by
  exact ⟨id, fun _ h => h.2.2⟩

theorem inNP_kSAT (k : Nat) : inNP (kSAT k) := by
  exact red_inNP (kSAT k) SAT (kSAT_to_SAT k) SAT_inNP.sat_NP
