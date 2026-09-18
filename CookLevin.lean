import CookLevin.Theorem
import CookLevin.ReadingList
import CookLevin.StatementMeaning
import CookLevin.MachineFaithfulness
import CookLevin.SearchDecide
import CookLevin.Basic.Definitions
import CookLevin.Basic.MachineSemantics
import CookLevin.Basic.NP
import CookLevin.Basic.StringTM
import CookLevin.Basic.TMPrimitives
import CookLevin.Basic.TapeMono
import CookLevin.Lang.AcceptHalt
import CookLevin.Lang.AppendGadget
import CookLevin.Lang.ClearGadget
import CookLevin.Lang.Compile
import CookLevin.Lang.Compile.Assembly
import CookLevin.Lang.Compile.Cmd
import CookLevin.Lang.Compile.Core
import CookLevin.Lang.Compile.Decider
import CookLevin.Lang.Compile.Encoding
import CookLevin.Lang.Compile.OpMachines
import CookLevin.Lang.Compile.OpSound
import CookLevin.Lang.Compile.RunClear
import CookLevin.Lang.Compile.RunCopyTail
import CookLevin.Lang.Compile.RunEqBit
import CookLevin.Lang.Compile.RunMove
import CookLevin.Lang.CostFlat
import CookLevin.Lang.CostGrow
import CookLevin.Lang.CostGrowHole
import CookLevin.Lang.FormatCheck
import CookLevin.Lang.Frame
import CookLevin.Lang.HardnessStr
import CookLevin.Lang.Navigate
import CookLevin.Lang.NumGadgets
import CookLevin.Lang.PolyTime
import CookLevin.Lang.ScanLeft
import CookLevin.Lang.ScanPast
import CookLevin.Lang.Semantics
import CookLevin.Lang.Serialize
import CookLevin.Lang.SerializeStr
import CookLevin.Lang.ShiftTape
import CookLevin.Lang.Syntax
import CookLevin.Lang.ToMachine
import CookLevin.Meta.AxiomGate
import CookLevin.Meta.StatementSurface
import CookLevin.Problems.BinaryCC
import CookLevin.Problems.FlatCC
import CookLevin.Problems.FlatTCC
import CookLevin.Problems.SingleTMGenNP
import CookLevin.Reductions.BinaryCC_to_FSAT
import CookLevin.Reductions.BinaryCC_to_FSAT_comp
import CookLevin.Reductions.BinaryCC_to_FSAT_free
import CookLevin.Reductions.BinaryCC_to_FSAT_free_defs
import CookLevin.Reductions.BinaryCC_to_FSAT_free_run
import CookLevin.Reductions.FSAT_to_SAT_comp
import CookLevin.Reductions.FSAT_to_SAT_free
import CookLevin.Reductions.FSAT_to_SAT_free_defs
import CookLevin.Reductions.FSAT_to_SAT_free_run
import CookLevin.Reductions.FlatCC_to_BinaryCC
import CookLevin.Reductions.FlatCC_to_BinaryCC_free
import CookLevin.Reductions.FlatTCC_to_BinaryCC_comp
import CookLevin.Reductions.FlatTCC_to_FlatCC
import CookLevin.Reductions.FlatTCC_to_FlatCC_free
import CookLevin.Reductions.FrontLifting
import CookLevin.Reductions.FrontMachine
import CookLevin.Reductions.FrontPieces
import CookLevin.Reductions.FrontProgram
import CookLevin.Reductions.FrontWitness
import CookLevin.Reductions.Front_to_S1_comp
import CookLevin.Reductions.HeadLayout
import CookLevin.Reductions.S1CardEmit
import CookLevin.Reductions.S1Cards
import CookLevin.Reductions.S1Emit
import CookLevin.Reductions.S1Map
import CookLevin.Reductions.S1Parse
import CookLevin.Reductions.S1Prelude
import CookLevin.Reductions.S1PreludeEmit
import CookLevin.Reductions.S1Program
import CookLevin.Reductions.S1StepEmit
import CookLevin.Reductions.S1StepLoop
import CookLevin.Reductions.S1StepModel
import CookLevin.Reductions.S1Witness
import CookLevin.Reductions.S1_to_FlatTCC_comp
import CookLevin.Reductions.SAT_to_SATStr_comp
import CookLevin.Reductions.SAT_to_SATStr_free
import CookLevin.SAT.CnfSerialize
import CookLevin.SAT.CnfWellFormed
import CookLevin.SAT.EvalCnfCmd
import CookLevin.SAT.EvalCnfSplit
import CookLevin.SAT.EvalCnfTM
import CookLevin.SAT.FSAT
import CookLevin.SAT.FSAT_to_SAT
import CookLevin.SAT.FSAT_to_SAT_pre
import CookLevin.SAT.KCNF
import CookLevin.SAT.SAT
import CookLevin.SAT.SATStr
import CookLevin.Tableau.CookTableau
import CookLevin.Tableau.GuessTableau

set_option autoImplicit false

/-! # Cook–Levin in Lean 4

The main theorem is `CookLevin.cook_levin` in `CookLevin/Theorem.lean`. This module imports
every module of the library, and the command below makes the build fail unless every
declaration in every one of them depends on nothing beyond Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). In particular a green build proves that the
library contains no `sorry`. -/

#assert_library_axiom_clean CookLevin
