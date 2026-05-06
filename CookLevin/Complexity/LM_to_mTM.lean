import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

namespace M

def M : Sigma (fun _ : TM Bool 2 => Unit) := ⟨(), ()⟩

end M

def lmToMTMInput (inst : LMGenNP.Instance (List Bool)) : mTMGenNPFixedInput Bool where
  workTapes := []
  maxSize := inst.maxSize
  steps := inst.steps
  accepts := inst.source.rel

theorem LMGenNP_to_TMGenNP_mTM :
    LMGenNP.LMGenNP (List Bool) ⪯p mTMGenNP_fixed (projT1 M.M) := by
  refine ⟨⟨lmToMTMInput, trivial, fun {inst} => Iff.rfl⟩⟩
