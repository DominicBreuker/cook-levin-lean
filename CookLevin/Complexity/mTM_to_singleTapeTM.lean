import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

namespace M_multi2mono

def M__mono {σ : finType} (_ : TM σ 2) : Sigma (fun _ : TM σ 1 => Unit) := 
  ⟨validFlatTM_default, ()⟩

end M_multi2mono

def multiTapeToSingleTapeInput {σ : Type} (inst : mTMGenNPFixedInput σ) : TMGenNPFixedInput σ where
  input := initTape_singleTapeTM (inst.workTapes.foldr List.append [])
  maxSize := inst.maxSize
  steps := inst.steps
  accepts := inst.accepts

theorem TMGenNP_mTM_to_TMGenNP_singleTM {σ : finType} (M : TM σ 2) :
    mTMGenNP_fixed M ⪯p TMGenNP_fixed (projT1 (M_multi2mono.M__mono M)) := by
  refine ⟨⟨multiTapeToSingleTapeInput, trivial, fun {inst} => Iff.rfl⟩⟩
