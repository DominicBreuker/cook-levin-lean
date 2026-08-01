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
import Complexity.NP.SAT.CookLevin.CookLevinHonest
import Complexity.SoundnessGate

set_option autoImplicit false

/-! # The library root — and the whole-library soundness gate

`Complexity/SoundnessGate.lean` gates the *endpoints*. This file is the only
place that transitively imports **every** module of the development, so it is
where the sweep belongs: the line below asserts that no declaration anywhere
under `Complexity` depends on `sorryAx` or on a bespoke `axiom`.

`sorry` is a *warning* in Lean, so `lake build` succeeding proves nothing about
it on its own. With this line, it does: **a green `lake build` is a machine-
checked proof that this library contains no `sorry` at all.** See
`Complexity/Meta/AxiomGate.lean` for what that does and does not buy. -/

#assert_library_axiom_clean Complexity
