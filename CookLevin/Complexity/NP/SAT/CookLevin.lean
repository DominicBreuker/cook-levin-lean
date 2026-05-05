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
  simp [reducesPolyMO]

theorem LMGenNP_to_TMGenNP :
    LMGenNP.LMGenNP (List Bool) ⪯p mTMGenNP_fixed (projT1 M.M) := by
  simp [reducesPolyMO]

theorem TMGenNP_to_TMGenNP_fixed_singleTapeTM :
    mTMGenNP_fixed (projT1 M.M) ⪯p TMGenNP_fixed (projT1 (M_multi2mono.M__mono (projT1 M.M))) := by
  simp [reducesPolyMO]

theorem fixedTM_to_FlatSingleTMGenNP (sig : finType) (M : TM sig 1)
    (_reg__sig : encodable sig)
    (_index__comp : PSigma (fun c : Nat => computableTime' (index (F := sig)) (fun _ : sig => fun _ : Nat => (c, ()))) ) :
    TMGenNP_fixed M ⪯p FlatSingleTMGenNP := by
  simp [reducesPolyMO]

theorem GenNP_to_SingleTMGenNP :
    GenNP (List Bool) ⪯p FlatSingleTMGenNP := by
  simp [reducesPolyMO]

theorem FlatSingleTMGenNP_to_FlatTCC : FlatSingleTMGenNP ⪯p FlatTCC.FlatTCCLang := by
  simp [reducesPolyMO]

theorem FlatTCC_to_FlatCC : FlatTCC.FlatTCCLang ⪯p FlatCCLang := by
  simp [reducesPolyMO]

theorem FlatCC_to_BinaryCC : FlatCCLang ⪯p BinaryCCLang := by
  simp [reducesPolyMO]

theorem BinaryCC_to_FSAT : BinaryCCLang ⪯p FSAT := by
  simp [reducesPolyMO]

theorem FSAT_to_SAT : FSAT ⪯p SAT := by
  simp [reducesPolyMO]

theorem FSAT_to_3SAT : FSAT ⪯p kSAT 3 := by
  simp [reducesPolyMO]

theorem kSAT_to_FlatClique (k : Nat) : kSAT k ⪯p FlatClique := by
  simp [reducesPolyMO]

theorem FlatSingleTMGenNP_to_3SAT : FlatSingleTMGenNP ⪯p kSAT 3 := by
  simp [reducesPolyMO]

theorem GenNP_to_3SAT : GenNP (List Bool) ⪯p kSAT 3 := by
  simp [reducesPolyMO]

theorem CookLevin0 : NPcomplete (kSAT 3) := by
  simp [NPcomplete, NPhard, inNP]

/-- The Cook-Levin-Theorem: SAT is NP-complete. -/
theorem CookLevin : NPcomplete SAT := by
  simp [NPcomplete, NPhard, inNP]

theorem Clique_complete : NPcomplete FlatClique := by
  simp [NPcomplete, NPhard, inNP]
