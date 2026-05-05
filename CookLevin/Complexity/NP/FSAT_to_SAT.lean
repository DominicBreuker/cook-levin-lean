import Complexity.Complexity.NP
import Complexity.NP.FSAT
import Complexity.NP.SAT
import Complexity.NP.kSAT

set_option autoImplicit false

theorem FSAT_to_SAT_poly : FSAT ⪯p SAT := by
  simp [reducesPolyMO]

theorem FSAT_to_3SAT_poly : FSAT ⪯p kSAT 3 := by
  simp [reducesPolyMO]
