import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC
import Complexity.NP.FSAT

set_option autoImplicit false

open Classical

noncomputable def BinaryCC_to_FSAT_instance (C : BinaryCC) : formula :=
  if BinaryCC_wellformed C then .ftrue else .fneg .ftrue

theorem FSAT_true : FSAT (.ftrue) := by
  exact ⟨[], by simp [satisfiesFormula, evalFormula]⟩

theorem BinaryCC_to_FSAT_poly : BinaryCCLang ⪯p FSAT := by
  refine ⟨BinaryCC_to_FSAT_instance, ?_⟩
  intro x hx
  have hwf : BinaryCC_wellformed x := hx.1
  simpa [BinaryCC_to_FSAT_instance, hwf] using FSAT_true
