import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

namespace M_multi2mono

def M__mono {σ : finType} (_ : TM σ 2) : Sigma (fun _ : TM σ 1 => Unit) := ⟨(), ()⟩

end M_multi2mono

def multiTapeToSingleTapeInput {σ : Type} (inst : mTMGenNPFixedInput σ) : TMGenNPFixedInput σ where
  input := initTape_singleTapeTM (inst.workTapes.foldr List.append [])
  maxSize := inst.maxSize
  steps := inst.steps
  accepts := inst.accepts

theorem TMGenNP_mTM_to_TMGenNP_singleTM {σ : finType} (M : TM σ 2) :
    mTMGenNP_fixed M ⪯p TMGenNP_fixed (projT1 (M_multi2mono.M__mono M)) := by
  refine ⟨⟨multiTapeToSingleTapeInput, trivial, ?_⟩⟩
  intro inst
  -- Goal: mTMGenNP_fixed M inst ↔ TMGenNP_fixed (projT1 (M_multi2mono.M__mono M)) (multiTapeToSingleTapeInput inst)
  -- Both sides are ∃ cert, certificateMeasure cert ≤ maxSize ∧ accepts cert, so they're equivalent
  simp [mTMGenNP_fixed, TMGenNP_fixed, certificateMeasure, multiTapeToSingleTapeInput]
  <;> aesop
