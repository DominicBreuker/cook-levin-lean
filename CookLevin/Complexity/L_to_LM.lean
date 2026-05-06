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
  refine ⟨⟨genNPToLMGenNPInstance, trivial, ?_⟩⟩
  intro inst
  -- Goal: GenNP X inst ↔ LMGenNP.LMGenNP X (genNPToLMGenNPInstance inst)
  -- GenNP X inst = ∃ cert, inst.rel cert
  -- LMGenNP.LMGenNP X (genNPToLMGenNPInstance inst) = ∃ cert, certificateMeasure cert ≤ 0 ∧ (genNPToLMGenNPInstance inst).source.rel cert
  -- Since (genNPToLMGenNPInstance inst).source = inst and certificateMeasure is always 0, these are equivalent
  simp [GenNP, LMGenNP, certificateMeasure, genNPToLMGenNPInstance]
  <;> aesop
