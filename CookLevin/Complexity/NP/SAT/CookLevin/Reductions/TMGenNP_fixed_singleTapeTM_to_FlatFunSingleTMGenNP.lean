import Complexity.Complexity.NP
import Complexity.NP.TM.IntermediateProblems
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP

set_option autoImplicit false

theorem TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP {sig : finType} (M : TM sig 1) :
    TMGenNP_fixed M ⪯p FlatFunSingleTMGenNP := by
  exact ⟨fun _ => ((), [], 0, 0), fun _ _ => flatFunSingleTMGenNP_yes⟩
