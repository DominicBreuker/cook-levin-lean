import Complexity.Meta.AxiomGate
import Complexity.NP.SAT.CookLevin.CookLevinHonest
import Complexity.NP.SAT.CookLevin.Reductions.Front_to_S1_comp
import Complexity.NP.SAT.CookLevin.Reductions.SAT_to_SATStr_comp

set_option autoImplicit false

/-! # The soundness gate — the axiom sweep, run BY `lake build`

Every endpoint of the proof path, asserted axiom-clean at **elaboration time**.
If any of these ever depends on `sorryAx` — or on a bespoke `axiom` — this file
fails to elaborate and `lake build` goes red. No probe to remember, no CI step,
no `grep`.

Read `Complexity/Meta/AxiomGate.lean` for what the assertion means and, just as
important, what it does *not* mean (it cannot see an encoding-honesty defect;
that is risk S5, whose instruments are `probes/HonestyAuditProbe.lean` and the
`NPhardStr` statement).

`probes/AxiomProbe.lean` remains as the *reporting* instrument — it prints each
endpoint's axiom list, which is what you want when investigating. This file is
the *gate*: it says nothing and fails loudly. Keep the two lists in sync; when
you add an endpoint, add it here first.

## The three that matter

```
CookLevinHonest.CookLevinStr : NPcompleteStr SAT   -- ★ the statement to quote
CookLevinHonest.CookLevin''  : NPcomplete''  SAT   -- the general form
FrontS1Comp.SAT_NPhard''                           -- the hardness half
```

Everything else below is the chain that feeds them, gated so that a regression
is attributed to the piece that caused it rather than to the headline.
-/

namespace Complexity.SoundnessGate

/-! ## The headline -/

#assert_axioms_clean
  CookLevinHonest.CookLevinStr
  CookLevinHonest.CookLevin''
  CookLevinHonest.SAT_NPhardStr
  CookLevinHonest.SAT_NPhard''
  CookLevinHonest.SAT_inNPLangFreeSplit

/-! ## The statement-level bridges (`NPhard''` ⇒ `NPhardStr`) -/

#assert_axioms_clean
  Complexity.Lang.NPhard''_to_NPhardStr
  Complexity.Lang.NPcomplete''_to_NPcompleteStr
  Complexity.Lang.size_le_two_mul_length
  Complexity.Lang.length_le_size
  Complexity.Lang.InNPWitnessStr.canonical_sizeLB

/-! ## The chain head — the input encoding and the on-machine size tally -/

#assert_axioms_clean
  FrontProgram.tallyStage_run
  FrontProgram.frontProgram_run
  FrontProgram.frontProgram_cost_le
  Complexity.Lang.FrontWitness.encodeInQ_tally
  Complexity.Lang.FrontWitness.exists_front_constants
  Complexity.Lang.FrontWitness.front_reducesPolyMO'

/-! ## The cost layer -/

#assert_axioms_clean
  Complexity.Lang.Cmd.chk_sound
  Complexity.Lang.Cmd.capCost_forBnd
  Complexity.Lang.Cmd.loopStep
  Complexity.Lang.Cmd.noGrow_sound
  Complexity.Lang.Cmd.noGrow_of_ngm
  Complexity.Lang.Cmd.costLeSize_of_chk
  Complexity.Lang.Cmd.get_length_eval_le

/-! ## The S1 reduction program (all stages) -/

#assert_axioms_clean
  S1Parse.stagePG_run
  S1Emit.stageInit_run
  S1Emit.stageFin_run
  S1CardEmit.cFive_run
  S1Prelude.cPrelude_run
  S1Step.stepEmit_run
  S1Step.entryPre_run
  S1Step.stepFam_run
  S1Program.stageC_run
  S1Program.stageMYes_run
  S1Program.s1Program_computes
  S1Program.s1Program_usesBelow

/-! ## The S1 witness and its cost ladder -/

#assert_axioms_clean
  S1Map.s1Map_correct
  S1Witness.s1CostBound_of_costLeSize
  S1Witness.s1Program_costLeSize
  S1Witness.s1Program_costBound
  S1Witness.s1_reductionLang
  S1Witness.s1_reducesPolyMO'

/-! ## The tableau and the composed chain -/

#assert_axioms_clean
  Simulators.cookTableau_correct
  Simulators.guessTableau_correct
  FSATSATComp.flatTCC_to_SAT_reducesPolyMO'
  S1SATComp.s1Bridge
  S1SATComp.s1_to_SAT_reducesPolyMO'
  FrontS1Comp.frontBridge
  FrontS1Comp.SAT_NPhard''_of_S1
  FrontS1Comp.SAT_NPhard''

/-! ## The membership half -/

#assert_axioms_clean
  EvalCnfSplit.satRel_correct
  EvalCnfSplit.satRel_satCert
  EvalCnfSplit.varsOfCnf_lt_size
  EvalCnfSplit.satEIn_bit
  EvalCnfSplit.satEIn_size_le
  EvalCnfSplit.size_decodeBits_le
  EvalCnfSplit.certDecode_chk
  EvalCnfSplit.certDecode_costBound
  EvalCnfSplit.certDecode_usesBelow
  EvalCnfSplit.certBridge_of_decodesAssgn
  EvalCnfSplit.decodeBits_take_succ
  EvalCnfSplit.satPrecomposeData
  EvalCnfSplit.satSplitVerifier
  EvalCnfSplit.satSplitWitnessOf
  EvalCnfSplit.decodeBody_run
  EvalCnfSplit.certDecode_eval_eq
  EvalCnfSplit.certDecode_decodesAssgn
  EvalCnfSplit.certDecode_bridge
  EvalCnfSplit.SAT_inNPLangFreeSplit_of
  EvalCnfSplit.SAT_inNPLangFreeSplit_of_decodesAssgn
  EvalCnfSplit.SAT_inNPLangFreeSplit
  CookLevinHonest.CookLevin''_of_decoder
  CookLevinHonest.CookLevin''_of_decodesAssgn

/-! ## The honesty layer — the serializers at the chain's two ends -/

#assert_axioms_clean
  CnfSerialize.decCnf_encodeCnf
  CnfSerialize.size_le_encodeCnf_length
  CnfSerialize.instSerializeCnf
  FSATSATFree.buildSAT_computes
  Complexity.Lang.decBits_strBits
  Complexity.Lang.strBits_boolsOf
  Complexity.Lang.instSerializeListBool

/-! ## `SATStr` — NP-completeness with `List Bool` on BOTH sides (2026-08-05)

The sixth seam and the endpoints it produces. `SATStrComp.SATStr_NPcompleteStr`
is the statement whose hypothesis *and* conclusion are languages of bit strings;
`CookLevinHonest.CookLevinStr` remains the statement about SAT itself. -/

#assert_axioms_clean
  SATToSATStr.strBits_satToStr
  SATToSATStr.satStr_satToStr
  SATToSATStr.strCmd_computes
  SATToSATStr.satToStr_reductionLang
  SATToSATStr.sat_reducesPolyMO'_satStr
  SATStrComp.comp_exit
  SATStrComp.exitsOnCNFOUT_comp
  SATStrComp.fsat_exitsOnCNFOUT
  SATStrComp.s1_exitsOnCNFOUT
  SATStrComp.front_exitsOnCNFOUT
  SATStrComp.front_to_SATStr_seam
  SATStrComp.front_to_SATStr_witness
  SATStrComp.front_to_SATStr_reducesPolyMO'
  SATStrComp.satStr_NPhardStr
  SATStrComp.SATStr_NPcompleteStr

end Complexity.SoundnessGate
