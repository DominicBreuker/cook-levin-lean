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

**Run it first thing in every session, and after any change to the S1 program,
the cost layer, a seam or the membership half.** Every line below must print
exactly

```
[propext, Classical.choice, Quot.sound]
```

(some print the shorter `[propext, Quot.sound]`; that is also clean). A
`sorryAx` anywhere in this list is a regression.

⚠ **This probe is the REPORTING instrument, not the gate.** Since 2026-08-02 the
gate is `CookLevin/Complexity/SoundnessGate.lean` plus the whole-library sweep at
the bottom of `CookLevin/Complexity.lean`: `#assert_axioms_clean` /
`#assert_library_axiom_clean` fail *elaboration*, so `lake build` itself goes red
on a `sorryAx` — no CI step, no `grep`, nothing to remember. Use this file when
you want to *see* an endpoint's axiom list; keep the two lists in sync.

## §1 measurement (2026-07-30-c)

All 59 endpoints clean, including the headline (§6 added 7 more 2026-08-01):

```
FrontS1Comp.SAT_NPhard''              clean   ← hardness   (2026-07-29-b)
EvalCnfSplit.certDecode_decodesAssgn  clean   ← the decoder `_run` lemma
EvalCnfSplit.SAT_inNPLangFreeSplit    clean   ← membership (2026-07-30-b)
CookLevinHonest.CookLevin''           clean   ← ★ NPcomplete'' SAT, UNCONDITIONAL
```

There is no longer any endpoint anywhere that prints `sorryAx`: the legacy `⪯p`
front, which was the only one, was **deleted** 2026-07-30-c.

⚠ **This probe cannot see an encoding-honesty defect** — that is the whole
point of standing risk S5, and the deepest historical unsoundness in this project
(S1's if-on-the-answer map, S2's dummy bridges) was `sorry`-free and invisible
here. Its companion is `probes/HonestyAuditProbe.lean`; run both. -/

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

/-! ## §6 — the honesty-enforcement layer (2026-08-01, top-down)

The canonical CNF serializer (which the tail's `decodeOut` is now pinned to) and
the string-language headline. See `probes/HonestyAuditProbe.lean` §§3/7/8 for
what these buy. -/

section Honesty
#print axioms Complexity.Lang.Compile.cost_is_time_proxy
#print axioms Complexity.Lang.Compile.time_le_timeProxyBound
#print axioms Complexity.Lang.Compile.deciderTime_le_timeProxyBound
#print axioms Complexity.Lang.InNPWitnessStr.canonical_sizeLB
#print axioms FrontProgram.tallyStage_run
#print axioms Complexity.Lang.FrontWitness.encodeInQ_tally
#print axioms Complexity.Lang.FrontWitness.exists_front_constants
#print axioms Complexity.Lang.FrontWitness.front_reducesPolyMO'
#print axioms CnfSerialize.decCnf_encodeCnf
#print axioms CnfSerialize.size_le_encodeCnf_length
#print axioms CnfSerialize.instSerializeCnf
#print axioms FSATSATFree.buildSAT_computes
#print axioms Complexity.Lang.NPhard''_to_NPhardStr
#print axioms CookLevinHonest.SAT_NPhardStr
-- ★ THE HONEST HEADLINE. `NPcompleteStr SAT` — no free input layout.
#print axioms CookLevinHonest.CookLevinStr
end Honesty
