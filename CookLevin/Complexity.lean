import Complexity.Complexity.MachineSemantics
import Complexity.Complexity.TMDecider
import Complexity.Complexity.TMEncoding
import Complexity.Complexity.TMPrimitives
import Complexity.Lang
import Complexity.Lang.Serialize
import Complexity.Lang.HardnessStr
import Complexity.Simulators
import Complexity.Complexity.Deciders.EvalCnfCmd
import Complexity.Complexity.Deciders.CnfSerialize
import Complexity.Complexity.Deciders.EvalCnfTM
import Complexity.Complexity.Deciders.CliqueRelTM
import Complexity.NP.kSAT_to_FlatClique
import Complexity.NP.SAT.CookLevin
import Complexity.NP.kSAT_to_SAT_free
import Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC_free
import Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC_free
import Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_BinaryCC_comp
import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_free_defs
import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_free_run
import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_free
import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_comp
import Complexity.NP.FSAT_to_SAT_pre
import Complexity.NP.SAT.CookLevin.Reductions.FSAT_to_SAT_free_defs
import Complexity.NP.SAT.CookLevin.Reductions.FSAT_to_SAT_free_run
import Complexity.NP.SAT.CookLevin.Reductions.FSAT_to_SAT_free
import Complexity.NP.SAT.CookLevin.Reductions.FSAT_to_SAT_comp
import Complexity.NP.SAT.CookLevin.Reductions.HeadLayout
import Complexity.NP.SAT.CookLevin.Reductions.FrontPieces
import Complexity.NP.SAT.CookLevin.Reductions.FrontMachine
import Complexity.NP.SAT.CookLevin.Reductions.FrontLifting
import Complexity.NP.SAT.CookLevin.Reductions.FrontProgram
import Complexity.NP.SAT.CookLevin.Reductions.FrontWitness
import Complexity.NP.SAT.CookLevin.Reductions.S1Map
import Complexity.NP.SAT.CookLevin.Reductions.S1Program
import Complexity.NP.SAT.CookLevin.Reductions.S1Witness
import Complexity.NP.SAT.CookLevin.Reductions.S1Parse
import Complexity.NP.SAT.CookLevin.Reductions.S1Cards
import Complexity.NP.SAT.CookLevin.Reductions.S1Emit
import Complexity.NP.SAT.CookLevin.Reductions.S1CardEmit
import Complexity.NP.SAT.CookLevin.Reductions.S1_to_FlatTCC_comp
import Complexity.NP.SAT.CookLevin.Reductions.Front_to_S1_comp
import Complexity.Complexity.Deciders.EvalCnfSplit
import Complexity.Complexity.Deciders.CnfWellFormed
import Complexity.Complexity.Deciders.SATStr
import Complexity.Lang.SerializeStr
import Complexity.NP.SAT.CookLevin.Reductions.SAT_to_SATStr_free
import Complexity.NP.SAT.CookLevin.Reductions.SAT_to_SATStr_comp
import Complexity.NP.SAT.CookLevin.CookLevinHonest
import Complexity.SoundnessGate
import Complexity.StatementGate
import Complexity.StatementMeaning
import Complexity.HonestyGate
import Complexity.CostFaithfulness
import Complexity.NonVacuity

set_option autoImplicit false

/-! # The library root — and the whole-library soundness gate

The gates below are part of the default build target and run on every
`lake build`:

* `Complexity/SoundnessGate.lean` — the axiom sweep, endpoint by endpoint;
* `Complexity/StatementGate.lean` — the complete list of *this repository's*
  definitions that the headline **statements** are built from, asserted exact.
  It is the reading list a reviewer works through, and the build proves nothing
  is missing from it;
* `Complexity/StatementMeaning.lean` — the headline restated in ordinary
  mathematical language, plus the checkable half of the S8 audit of that reading
  list: that rejection is a real verdict, what the tape does at its edges, that
  a `runFlatTM` result is not a halting claim, that SAT means satisfiability and
  what the input measure is. Read it right after the statement gate;
* `Complexity/HonestyGate.lean` — what the composite reduction's `encodeIn` and
  `decodeOut` actually *are* (risk S5's two audited functions);
* `Complexity/CostFaithfulness.lean` — that `Op.cost`, the number every
  "polynomial time" claim in this development is a bound on, is a polynomial
  proxy for real `stepFlatTM` time;
* `Complexity/NonVacuity.lean` — that the hypothesis of the published hardness
  statement is neither empty (a complete `InNPWitnessStr` is exhibited) nor
  satisfiable by an arbitrary predicate (every inhabitant is decidable by a
  brute-force search over its own verifier program).

This file is the only module that transitively imports **every** other, so it is
where the whole-library sweep belongs: the line below asserts that no declaration
anywhere under `Complexity` depends on `sorryAx` or on a bespoke `axiom`.

`sorry` is a *warning* in Lean, so `lake build` succeeding proves nothing about
it on its own. With this line, it does: **a green `lake build` is a machine-
checked proof that this library contains no `sorry` at all.** See
`Complexity/Meta/AxiomGate.lean` for what that does and does not buy. -/

#assert_library_axiom_clean Complexity
