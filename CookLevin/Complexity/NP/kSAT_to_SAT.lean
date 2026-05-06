import Complexity.Complexity.NP
import Complexity.NP.SAT
import Complexity.NP.kSAT

set_option autoImplicit false

theorem kSAT_to_SAT (k : Nat) : kSAT k ⪯p SAT := by
  refine ⟨⟨id, trivial, ?_⟩⟩
  intro N
  -- kSAT k N ↔ SAT (id N) = SAT N
  -- This is just unrolling the definitions
  sorry

theorem inNP_kSAT (k : Nat) : inNP (kSAT k) := by
  exact red_inNP (kSAT k) SAT (kSAT_to_SAT k) SAT_inNP.sat_NP
