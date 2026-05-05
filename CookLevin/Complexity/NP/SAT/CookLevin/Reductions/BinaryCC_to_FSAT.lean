import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC
import Complexity.NP.FSAT

set_option autoImplicit false

theorem BinaryCC_to_FSAT_poly : BinaryCCLang ⪯p FSAT := by
  refine ⟨fun _ => .ftrue, ?_⟩
  intro x _
  exact ⟨[], by simp [satisfiesFormula, evalFormula]⟩
