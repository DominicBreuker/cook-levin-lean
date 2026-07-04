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
  -- The wrapper repeats the source's parameters, so its size is exactly
  -- twice the input size.
  refine ⟨⟨fun n => 2 * n, ?_, ?_, ?_⟩⟩
  · exact ⟨1, 2, 0, fun n _ => Nat.le_of_eq (by simp)⟩
  · intro a b hab
    exact Nat.mul_le_mul (Nat.le_refl 2) hab
  · intro inst
    show encodable.size (genNPToLMGenNPInstance inst) ≤ 2 * encodable.size inst
    simp [genNPToLMGenNPInstance]
    omega
