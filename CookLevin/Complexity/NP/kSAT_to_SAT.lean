import Complexity.Complexity.NP
import Complexity.NP.SAT
import Complexity.NP.kSAT

set_option autoImplicit false

theorem kSAT_to_SAT (k : Nat) : kSAT k ⪯p SAT := by
  sorry

theorem inNP_kSAT (k : Nat) : inNP (kSAT k) := by
  sorry
