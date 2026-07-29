import Complexity.NP.SAT.CookLevin.Reductions.Front_to_S1_comp

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

## §1 measurement (2026-07-29-b)

All clean, including — for the first time — the four endpoints that used to
inherit `sorryAx` from the cost ladder:

```
S1Witness.s1Program_costLeSize        clean   ← the ladder, closed this session
S1Witness.s1_reductionLang            clean
S1Witness.s1_reducesPolyMO'           clean
S1SATComp.s1_to_SAT_reducesPolyMO'    clean
FrontS1Comp.SAT_NPhard''              clean   ← NPhard'' SAT is axiom-clean
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
