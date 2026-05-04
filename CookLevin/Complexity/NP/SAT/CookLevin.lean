import Complexity.Complexity.Definitions
import Complexity.Complexity.NP
import Complexity.Complexity.Subtypes
import Complexity.NP.GenNP
import Complexity.NP.TM.IntermediateProblems
import Complexity.NP.SAT
import Complexity.NP.FSAT
import Complexity.NP.kSAT
import Complexity.NP.FlatClique
import Complexity.NP.FSAT_to_SAT
import Complexity.NP.kSAT_to_SAT
import Complexity.NP.kSAT_to_FlatClique
import Complexity.NP.SAT.CookLevin.Subproblems.FlatCC
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP
import Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC
import Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC
import Complexity.NP.SAT.CookLevin.FlatSingleTMGenNP_to_FlatTCC
import Complexity.NP.SAT.CookLevin.FlatTCC_to_FlatCC
import Complexity.NP.SAT.CookLevin.FlatCC_to_BinaryCC
import Complexity.NP.SAT.CookLevin.BinaryCC_to_FSAT
import Complexity.GenNP_is_hard
import Complexity.CanEnumTerm

set_option autoImplicit false

theorem GenNP_to_LMGenNP :
    GenNP (List Bool) ⪯p LMGenNP.LMGenNP (List Bool) := by
  sorry

theorem LMGenNP_to_TMGenNP :
    LMGenNP.LMGenNP (List Bool) ⪯p mTMGenNP_fixed (projT1 M.M) := by
  sorry

theorem TMGenNP_to_TMGenNP_fixed_singleTapeTM :
    mTMGenNP_fixed (projT1 M.M) ⪯p TMGenNP_fixed (projT1 (M_multi2mono.M__mono (projT1 M.M))) := by
  sorry

theorem fixedTM_to_FlatSingleTMGenNP (sig : finType) (M : TM sig 1)
    (reg__sig : encodable sig)
    (index__comp : Sigma (fun c => computableTime' (index (F := sig)) (fun _ : sig => fun _ : Nat => (c, ()))) ) :
    TMGenNP_fixed M ⪯p FlatSingleTMGenNP := by
  sorry

theorem GenNP_to_SingleTMGenNP :
    GenNP (List Bool) ⪯p FlatSingleTMGenNP := by
  sorry

theorem FlatSingleTMGenNP_to_FlatTCC : FlatSingleTMGenNP ⪯p FlatTCC.FlatTCCLang := by
  sorry

theorem FlatTCC_to_FlatCC : FlatTCC.FlatTCCLang ⪯p FlatCCLang := by
  sorry

theorem FlatCC_to_BinaryCC : FlatCCLang ⪯p BinaryCCLang := by
  sorry

theorem BinaryCC_to_FSAT : BinaryCCLang ⪯p FSAT := by
  sorry

theorem FSAT_to_SAT : FSAT ⪯p SAT := by
  sorry

theorem FSAT_to_3SAT : FSAT ⪯p kSAT 3 := by
  sorry

theorem kSAT_to_FlatClique (k : Nat) : kSAT k ⪯p FlatClique := by
  sorry

theorem FlatSingleTMGenNP_to_3SAT : FlatSingleTMGenNP ⪯p kSAT 3 := by
  sorry

theorem GenNP_to_3SAT : GenNP (List Bool) ⪯p kSAT 3 := by
  sorry

theorem CookLevin0 : NPcomplete (kSAT 3) := by
  sorry

/-- The Cook-Levin-Theorem: SAT is NP-complete. -/
theorem CookLevin : NPcomplete SAT := by
  sorry

theorem Clique_complete : NPcomplete FlatClique := by
  sorry
