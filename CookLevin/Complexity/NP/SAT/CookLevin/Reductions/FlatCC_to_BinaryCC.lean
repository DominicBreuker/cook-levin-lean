import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.FlatCC
import Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC

set_option autoImplicit false

theorem FlatCC_to_BinaryCC_poly : FlatCCLang ⪯p BinaryCCLang := by
  simp [reducesPolyMO]
