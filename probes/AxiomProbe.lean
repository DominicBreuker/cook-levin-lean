import Complexity.NP.SAT.CookLevin.Reductions.Front_to_S1_comp
import Complexity.NP.SAT.CookLevin.CookLevinHonest

set_option autoImplicit false

/-! # Probe — the axiom regression list

The project's soundness instrument is `#print axioms`, and it is **blind to a
`sorry` inside a `def`**: such a `sorry` poisons the *statement* of every lemma
mentioning it, so a lemma can be "green" and still be worthless (standing
architecture risk #7). The discipline that protects against this is to quantify
skeleton-phase results over the placeholder; this file is the check that the
discipline held.

**Run it after any change to the S1 program, the cost layer, or a seam.** Every
line below must print exactly

```
[propext, Classical.choice, Quot.sound]
```

(some print the shorter `[propext, Quot.sound]`; that is also clean). A
`sorryAx` anywhere in this list is a regression.

## §1 measurement (2026-07-30-b)

All clean, including the headline:

```
FrontS1Comp.SAT_NPhard''              clean   ← hardness   (2026-07-29-b)
EvalCnfSplit.certDecode_decodesAssgn  clean   ← the decoder `_run` lemma
EvalCnfSplit.SAT_inNPLangFreeSplit    clean   ← membership (2026-07-30-b)
CookLevinHonest.CookLevin''           clean   ← ★ NPcomplete'' SAT, UNCONDITIONAL
```

⚠ `CookLevin` itself still depends on `sorryAx`, and that is **correct**: it
quotes the *legacy* `⪯p` front (`NPhard_GenNP` → `hasDeciderClassical`). Retiring
it is the top-down job, not a regression here. -/

open Complexity Complexity.Lang

section CostLayer
#print axioms Complexity.Lang.Cmd.chk_sound
#print axioms Complexity.Lang.Cmd.capCost_forBnd
#print axioms Complexity.Lang.Cmd.loopStep
#print axioms Complexity.Lang.Cmd.noGrow_sound
#print axioms Complexity.Lang.Cmd.noGrow_of_ngm
#print axioms Complexity.Lang.Cmd.costLeSize_of_chk
#print axioms Complexity.Lang.Cmd.get_length_eval_le
end CostLayer

section S1Program
#print axioms S1Parse.stagePG_run
#print axioms S1Emit.stageInit_run
#print axioms S1Emit.stageFin_run
#print axioms S1CardEmit.cFive_run
#print axioms S1Prelude.cPrelude_run
#print axioms S1Step.stepEmit_run
#print axioms S1Step.entryPre_run
#print axioms S1Step.stepFam_run
#print axioms S1Program.stageC_run
#print axioms S1Program.stageMYes_run
#print axioms S1Program.s1Program_computes
#print axioms S1Program.s1Program_usesBelow
end S1Program

section S1Witness
#print axioms S1Map.s1Map_correct
#print axioms S1Witness.s1CostBound_of_costLeSize
#print axioms S1Witness.s1Program_costLeSize
#print axioms S1Witness.s1Program_costBound
#print axioms S1Witness.s1_reductionLang
#print axioms S1Witness.s1_reducesPolyMO'
end S1Witness

section Chain
#print axioms Simulators.cookTableau_correct
#print axioms Simulators.guessTableau_correct
#print axioms FSATSATComp.flatTCC_to_SAT_reducesPolyMO'
#print axioms S1SATComp.s1Bridge
#print axioms S1SATComp.s1_to_SAT_reducesPolyMO'
#print axioms FrontS1Comp.frontBridge
#print axioms FrontS1Comp.SAT_NPhard''_of_S1
#print axioms FrontS1Comp.SAT_NPhard''
end Chain

section SATMembership
-- The membership half: the split layout, the certificate relation, the decoder's
-- `_run` ladder, the composite verifier and the honest headline. The `_of_*`
-- entries are still quantified over the decoder contracts (that is the
-- program-generic interface, standing risk #7); the unconditional endpoints are
-- at the bottom of the section.
#print axioms EvalCnfSplit.satRel_correct
#print axioms EvalCnfSplit.satRel_satCert
#print axioms EvalCnfSplit.varsOfCnf_lt_size
#print axioms EvalCnfSplit.satEIn_bit
#print axioms EvalCnfSplit.satEIn_size_le
#print axioms EvalCnfSplit.size_decodeBits_le
#print axioms EvalCnfSplit.certDecode_chk
#print axioms EvalCnfSplit.certDecode_costBound
#print axioms EvalCnfSplit.certDecode_usesBelow
#print axioms EvalCnfSplit.certBridge_of_decodesAssgn
#print axioms EvalCnfSplit.decodeBits_take_succ
#print axioms EvalCnfSplit.satPrecomposeData
#print axioms EvalCnfSplit.satSplitVerifier
#print axioms EvalCnfSplit.satSplitWitnessOf
#print axioms EvalCnfSplit.SAT_inNPLangFreeSplit_of
#print axioms EvalCnfSplit.SAT_inNPLangFreeSplit_of_decodesAssgn
#print axioms CookLevinHonest.CookLevin''_of_decoder
#print axioms CookLevinHonest.CookLevin''_of_decodesAssgn
-- The decoder's `_run` ladder (2026-07-30-b) and the UNCONDITIONAL endpoints.
#print axioms EvalCnfSplit.decodeBody_run
#print axioms EvalCnfSplit.certDecode_eval_eq
#print axioms EvalCnfSplit.certDecode_decodesAssgn
#print axioms EvalCnfSplit.certDecode_bridge
#print axioms EvalCnfSplit.SAT_inNPLangFreeSplit
#print axioms CookLevinHonest.SAT_NPhard''
#print axioms CookLevinHonest.SAT_inNPLangFreeSplit
-- ★ THE HEADLINE. `NPcomplete'' SAT`, unconditional.
#print axioms CookLevinHonest.CookLevin''
end SATMembership
