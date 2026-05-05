import Complexity.Complexity.NP
import Complexity.NP.SAT
import Complexity.NP.kSAT

set_option autoImplicit false

theorem kSAT_to_SAT (k : Nat) : kSAT k ⪯p SAT := by
  refine ⟨⟨id, ?_⟩⟩
  intro N hKSat
  rcases hKSat with ⟨_, _, hSat⟩
  exact hSat

theorem inNP_kSAT (k : Nat) : inNP (kSAT k) := by
  exact red_inNP (kSAT k) SAT (kSAT_to_SAT k) SAT_inNP.sat_NP
