import Complexity.Complexity.NP
import Complexity.NP.GenNP
import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

def genNPToLMGenNPInstance {X : Type} [encodable X] (inst : GenNPInput X) :
    LMGenNP.Instance X where
  source := inst
  maxSize := inst.maxSize
  steps := inst.steps

theorem GenNP_to_LMGenNP (X : Type) [encodable X] :
    GenNP X ⪯p LMGenNP.LMGenNP X := by
  refine ⟨⟨genNPToLMGenNPInstance, by sorry, fun {inst} => ?_⟩⟩
  constructor
  · rintro ⟨cert, hsize, hrel⟩
    exact ⟨cert, hsize, hsize, hrel⟩
  · rintro ⟨cert, hsize, _, hrel⟩
    exact ⟨cert, hsize, hrel⟩
