import Complexity.Complexity.NP
import Complexity.NP.GenNP
import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

def genNPToLMGenNPInstance {X : Type} [encodable X] (inst : GenNPInput X) :
    LMGenNP.Instance X where
  source := inst
  maxSize := 0
  steps := 0

theorem GenNP_to_LMGenNP (X : Type) [encodable X] :
    GenNP X ⪯p LMGenNP.LMGenNP X := by
  refine ⟨⟨genNPToLMGenNPInstance, trivial, fun {inst} => ?_⟩⟩
  simp [GenNP, LMGenNP, genNPToLMGenNPInstance, certificateMeasure]
