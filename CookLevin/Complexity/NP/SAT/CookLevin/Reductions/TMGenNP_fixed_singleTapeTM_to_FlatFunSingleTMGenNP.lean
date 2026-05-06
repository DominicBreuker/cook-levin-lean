import Complexity.Complexity.NP
import Complexity.NP.TM.IntermediateProblems
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP

set_option autoImplicit false

def TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP_instance {sig : finType} [encodable sig]
    (inst : TMGenNPFixedInput sig) : flatTM × List Nat × Nat × Nat :=
  (validFlatTM_default, inst.input.map index, inst.maxSize, inst.steps)

theorem TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP {sig : finType} [encodable sig] (M : TM sig 1) :
    TMGenNP_fixed M ⪯p FlatFunSingleTMGenNP := by
  sorry
