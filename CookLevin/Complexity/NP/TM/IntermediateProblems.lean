import Complexity.Complexity.Definitions

import Complexity.L_to_LM
import Complexity.LM_to_mTM
import Complexity.mTM_to_singleTapeTM

set_option autoImplicit false

theorem GenNP_to_TMGenNP :
    GenNP (List Bool) ⪯p TMGenNP_fixed (projT1 (M_multi2mono.M__mono (projT1 M.M))) := by
  have hLM : GenNP (List Bool) ⪯p LMGenNP.LMGenNP (List Bool) :=
    GenNP_to_LMGenNP (List Bool)
  have hmTM : LMGenNP.LMGenNP (List Bool) ⪯p mTMGenNP_fixed (projT1 M.M) :=
    LMGenNP_to_TMGenNP_mTM
  have hTM : mTMGenNP_fixed (projT1 M.M) ⪯p TMGenNP_fixed (projT1 (M_multi2mono.M__mono (projT1 M.M))) :=
    TMGenNP_mTM_to_TMGenNP_singleTM (projT1 M.M)
  exact reducesPolyMO_transitive _ _ _ (reducesPolyMO_transitive _ _ _ hLM hmTM) hTM
