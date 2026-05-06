import Complexity.Complexity.NP
import Complexity.NP.GenNP
import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

def genNPToLMGenNPInstance {X : Type} [encodable X] (inst : GenNPInput X) :
    LMGenNP.Instance X where
  source := inst
  maxSize := inst.maxSize
  steps := inst.steps

theorem genNPToLMGenNPInstance_bounds {X : Type} [encodable X] (inst : GenNPInput X) :
    (genNPToLMGenNPInstance inst).maxSize = inst.maxSize ∧
      (genNPToLMGenNPInstance inst).steps = inst.steps := by
  simp [genNPToLMGenNPInstance]

theorem genNPToLMGenNPInstance_spec {X : Type} [encodable X] (inst : GenNPInput X) :
    LMGenNP.LMGenNP X (genNPToLMGenNPInstance inst) ↔ GenNP X inst := by
  constructor
  · rintro ⟨cert, hsize, _, hrel⟩
    exact ⟨cert, hsize, hrel⟩
  · rintro ⟨cert, hsize, hrel⟩
    exact ⟨cert, hsize, hsize, hrel⟩

theorem GenNP_to_LMGenNP (X : Type) [encodable X] :
    GenNP X ⪯p LMGenNP.LMGenNP X := by
  refine ⟨⟨genNPToLMGenNPInstance, ?_, fun {inst} => (genNPToLMGenNPInstance_spec inst).symm⟩⟩
  refine ⟨⟨fun _ => 0, inOPoly_const 0, ?_, ?_⟩⟩
  · intro a b hab
    simp
  · intro inst
    exact Nat.le_refl _
