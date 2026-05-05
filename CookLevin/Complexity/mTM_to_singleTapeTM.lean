import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

namespace M_multi2mono

def M__mono {σ : finType} (_ : TM σ 2) : Sigma (fun tm : TM σ 1 => Unit) := ⟨(), ()⟩

end M_multi2mono

def multiTapeToSingleTapeInput {σ : Type} (inst : mTMGenNPFixedInput σ) : TMGenNPFixedInput σ where
  input := initTape_singleTapeTM inst.workTapes.join
  maxSize := inst.maxSize
  steps := inst.steps
  accepts := inst.accepts

theorem TMGenNP_mTM_to_TMGenNP_singleTM {σ : finType} (M : TM σ 2) :
    mTMGenNP_fixed M ⪯p TMGenNP_fixed (projT1 (M_multi2mono.M__mono M)) := by
  refine ⟨⟨multiTapeToSingleTapeInput, ?_⟩⟩
  intro inst hInst
  rcases hInst with ⟨cert, hSize, hAccepts⟩
  exact ⟨cert, by simpa [certificateMeasure] using hSize, hAccepts⟩
