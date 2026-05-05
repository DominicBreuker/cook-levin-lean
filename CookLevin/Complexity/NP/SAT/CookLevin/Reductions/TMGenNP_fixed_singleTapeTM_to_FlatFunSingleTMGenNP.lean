import Complexity.Complexity.NP
import Complexity.NP.TM.IntermediateProblems
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP

set_option autoImplicit false

def TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP_instance {sig : finType}
    (inst : TMGenNPFixedInput sig) : flatTM × List Nat × Nat × Nat :=
  ((), [], inst.maxSize, inst.steps)

theorem TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP {sig : finType} (M : TM sig 1) :
    TMGenNP_fixed M ⪯p FlatFunSingleTMGenNP := by
  refine ⟨TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP_instance, ?_⟩
  intro inst hinst
  rcases hinst with ⟨cert, hcert, _⟩
  refine ⟨trivial, list_ofFlatType_nil 1, ?_⟩
  exact ⟨[], list_ofFlatType_nil 1, by simp [isValidCert]⟩
