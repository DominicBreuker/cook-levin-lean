import Complexity.Complexity.Definitions
import Complexity.Complexity.NP
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
import Complexity.NP.SAT.CookLevin.Reductions.TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP
import Complexity.GenNP_is_hard
import Complexity.CanEnumTerm

set_option autoImplicit false

theorem fixedTM_to_FlatSingleTMGenNP (sig : finType) (M : TM sig 1)
    (_reg__sig : encodable sig) :
    TMGenNP_fixed M ⪯p FlatSingleTMGenNP := by
  have hFun : TMGenNP_fixed M ⪯p FlatFunSingleTMGenNP :=
    TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP M
  have hEquiv : FlatFunSingleTMGenNP ⪯p FlatSingleTMGenNP := by
    refine ⟨⟨id, ?_, fun {inst} => ?_⟩⟩
    · exact ⟨⟨fun n => n, inOPoly_id, (by intro a b hab; exact hab), by intro x; simp⟩⟩
    · rcases inst with ⟨M, s, maxSize, steps⟩
      simpa using FlatFunSingleTMGenNP_FlatSingleTMGenNP_equiv M s maxSize steps
  exact reducesPolyMO_transitive _ _ _ hFun hEquiv

theorem GenNP_to_SingleTMGenNP :
    GenNP (List Bool) ⪯p FlatSingleTMGenNP := by
  have hTM : GenNP (List Bool) ⪯p TMGenNP_fixed (σ := Bool) validFlatTM_default := by
    simpa [IntermediateTMTarget, TMGenNP_fixed] using GenNP_to_TMGenNP
  exact reducesPolyMO_transitive _ _ _ hTM
    (fixedTM_to_FlatSingleTMGenNP Bool validFlatTM_default instEncodableBool)

theorem FlatSingleTMGenNP_to_FlatTCC : FlatSingleTMGenNP ⪯p FlatTCC.FlatTCCLang := by
  exact FlatSingleTMGenNP_to_FlatTCCLang_poly

theorem FlatTCC_to_FlatCC : FlatTCC.FlatTCCLang ⪯p FlatCCLang := by
  exact FlatTCC_to_FlatCC_poly

theorem FlatCC_to_BinaryCC : FlatCCLang ⪯p BinaryCCLang := by
  exact FlatCC_to_BinaryCC_poly

theorem BinaryCC_to_FSAT : BinaryCCLang ⪯p FSAT := by
  exact BinaryCC_to_FSAT_poly

theorem FSAT_to_SAT : FSAT ⪯p SAT := by
  exact FSAT_to_SAT_poly

theorem FSAT_to_3SAT : FSAT ⪯p kSAT 3 := by
  exact FSAT_to_3SAT_poly

theorem kSAT_to_FlatClique (k : Nat) : kSAT k ⪯p FlatClique := by
  exact kSAT_to_FlatClique_poly k

theorem FlatSingleTMGenNP_to_3SAT : FlatSingleTMGenNP ⪯p kSAT 3 := by
  have hToFlatCC : FlatSingleTMGenNP ⪯p FlatCCLang :=
    reducesPolyMO_transitive _ _ _ FlatSingleTMGenNP_to_FlatTCC FlatTCC_to_FlatCC
  have hToBinaryCC : FlatSingleTMGenNP ⪯p BinaryCCLang :=
    reducesPolyMO_transitive _ _ _ hToFlatCC FlatCC_to_BinaryCC
  have hToFSAT : FlatSingleTMGenNP ⪯p FSAT :=
    reducesPolyMO_transitive _ _ _ hToBinaryCC BinaryCC_to_FSAT
  exact reducesPolyMO_transitive _ _ _ hToFSAT FSAT_to_3SAT

theorem GenNP_to_3SAT : GenNP (List Bool) ⪯p kSAT 3 := by
  exact reducesPolyMO_transitive _ _ _ GenNP_to_SingleTMGenNP FlatSingleTMGenNP_to_3SAT

theorem CookLevin0 : NPcomplete (kSAT 3) := by
  refine ⟨red_NPhard _ _ GenNP_to_3SAT (NPhard_GenNP (List Bool) boollist_enum.boollists_enum_term), inNP_kSAT 3⟩

/-- The Cook-Levin-Theorem: SAT is NP-complete. -/
theorem CookLevin : NPcomplete SAT := by
  refine ⟨red_NPhard _ _ (kSAT_to_SAT 3) CookLevin0.1, SAT_inNP.sat_NP⟩

theorem Clique_complete : NPcomplete FlatClique := by
  refine ⟨red_NPhard _ _ (kSAT_to_FlatClique 3) CookLevin0.1, FlatClique_in_NP⟩
