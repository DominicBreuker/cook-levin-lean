import Complexity.Complexity.Definitions

import Complexity.L_to_LM
import Complexity.LM_to_mTM
import Complexity.mTM_to_singleTapeTM

set_option autoImplicit false

abbrev IntermediateTMTarget : TMGenNPFixedInput Bool → Prop :=
  fun inst =>
    ∃ cert : List Bool,
      @certificateMeasure (List Bool) (@instEncodableList Bool instEncodableBool) cert ≤ inst.maxSize ∧
        inst.accepts cert

theorem GenNP_to_TMGenNP :
    GenNP (List Bool) ⪯p IntermediateTMTarget := by
  have hLM : GenNP (List Bool) ⪯p LMGenNP.LMGenNP (List Bool) :=
    GenNP_to_LMGenNP (List Bool)
  have hmTM : LMGenNP.LMGenNP (List Bool) ⪯p LMtoMTMTarget :=
    LMGenNP_to_TMGenNP_mTM
  have hTM : LMtoMTMTarget ⪯p IntermediateTMTarget := by
    simpa [IntermediateTMTarget] using ExplicitMTMTarget_to_TMGenNP_singleTM (projT1 M.M)
  exact reducesPolyMO_transitive _ _ _ (reducesPolyMO_transitive _ _ _ hLM hmTM) hTM
