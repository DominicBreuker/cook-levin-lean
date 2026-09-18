import CookLevin.Meta.StatementSurface
import CookLevin.Theorem

set_option autoImplicit false

/-! # The reading list

Every definition of this repository that the **statement** of the main theorem depends on,
in reading order. `#assert_statement_surface` (`Meta/StatementSurface.lean`) recomputes that
set from the statement's type and fails the build unless it is exactly the list below, so
the list can neither miss a definition nor contain a stale one. Everything else the statement
mentions is from Lean's core library (`List`, `Nat`, `Bool`, `Option`, `Prod`, …).

A reader who has read these definitions and agrees that each means what its name says knows
what `cook_levin` asserts. Theorem *proofs* are not part of the surface: they cannot change
what a statement means, and the kernel checks them. -/

namespace CookLevin.ReadingList

/-! ## `cook_levin : NPcomplete SATStr` -/

#assert_statement_surface CookLevin.cook_levin =>
  -- 1. The claim (`Lang/HardnessStr.lean`, `Basic/StringTM.lean`).
  CookLevin.Lang.NPcomplete
  CookLevin.Lang.NPhard
  CookLevin.Lang.inNPCmd
  CookLevin.reducesPoly
  CookLevin.computesInTime
  CookLevin.stringTape
  CookLevin.symbolsOf
  CookLevin.outputString
  -- 2. Turing machines (`Basic/MachineSemantics.lean`, `Basic/Definitions.lean`).
  FlatTM
  flatTM
  FlatTM.sig
  FlatTM.tapes
  FlatTM.states
  FlatTM.start
  FlatTM.halt
  FlatTM.trans
  FlatTMTransEntry
  FlatTMTransEntry.src_state
  FlatTMTransEntry.src_tape_vals
  FlatTMTransEntry.dst_state
  FlatTMTransEntry.dst_write_vals
  FlatTMTransEntry.move_dirs
  TMMove
  TMMove.Lmove
  TMMove.Rmove
  TMMove.Nmove
  FlatTMConfig
  FlatTMConfig.state_idx
  FlatTMConfig.tapes
  initFlatConfig
  currentTapeSymbol
  writeCurrentTapeSymbol
  moveTapeHead
  tapeStep
  entryMatchesConfig
  applyTransitionEntry
  stepFlatTM
  haltingStateReached
  runFlatTM
  validFlatTM
  flatTMTransEntryValid
  flatTMOptionSymbolsBounded
  -- 3. Polynomials and sizes (`Basic/Definitions.lean`).
  inOPoly
  inO
  monotonic
  encodable
  encodable.size
  instEncodableBool
  instEncodableList
  instEncodableProd
  -- 4. Verifier programs (`Lang/HardnessStr.lean`, `Lang/PolyTime.lean`, `Basic/NP.lean`).
  CookLevin.Lang.NPWitnessStr
  CookLevin.Lang.NPWitness
  CookLevin.Lang.NPWitness.encX
  CookLevin.Lang.certState
  CookLevin.Lang.DecidesLang
  CookLevin.Lang.DecidesLang.encodeIn
  polyCertRel
  PolyCertRelWitness
  -- 5. The register language (`Lang/Syntax.lean`, `Lang/Semantics.lean`, `Lang/Frame.lean`,
  --    `Lang/Compile/Encoding.lean`).
  CookLevin.Lang.Var
  CookLevin.Lang.State
  CookLevin.Lang.State.get
  CookLevin.Lang.State.set
  CookLevin.Lang.State.size
  CookLevin.Lang.State.isAccept
  CookLevin.Lang.State.isReject
  CookLevin.Lang.Op
  CookLevin.Lang.Op.clear
  CookLevin.Lang.Op.appendOne
  CookLevin.Lang.Op.appendZero
  CookLevin.Lang.Op.copy
  CookLevin.Lang.Op.tail
  CookLevin.Lang.Op.head
  CookLevin.Lang.Op.eqBit
  CookLevin.Lang.Op.nonEmpty
  CookLevin.Lang.Op.concat
  CookLevin.Lang.Op.eval
  CookLevin.Lang.Op.cost
  CookLevin.Lang.Op.UsesBelow
  CookLevin.Lang.Cmd
  CookLevin.Lang.Cmd.op
  CookLevin.Lang.Cmd.seq
  CookLevin.Lang.Cmd.ifBit
  CookLevin.Lang.Cmd.forBnd
  CookLevin.Lang.Cmd.run
  CookLevin.Lang.Cmd.eval
  CookLevin.Lang.Cmd.cost
  CookLevin.Lang.Cmd.decides
  CookLevin.Lang.Cmd.UsesBelow
  CookLevin.Lang.Compile.BitState
  -- 6. SAT (`Basic/Definitions.lean`, `SAT/SAT.lean`).
  var
  literal
  clause
  cnf
  assgn
  evalVar
  evalLiteral
  evalClause
  evalCnf
  satisfiesCnf
  SAT
  -- 7. SAT as a language of bit strings (`SAT/SATStr.lean`, `Lang/SerializeStr.lean`,
  --    `SAT/CnfWellFormed.lean`, `SAT/CnfSerialize.lean`).
  SATStr
  SATStr.cnfOf
  CookLevin.Lang.strBits
  CnfWellFormed.parseTotal
  CnfWellFormed.wfCnfB
  CnfWellFormed.scanRun
  CnfWellFormed.scanStep
  CnfSerialize.decCnf
  CnfSerialize.decCnfAux
  CnfSerialize.decClause
  CnfSerialize.scanUnary

/-! ## `SATStr_inNP : inNP SATStr`

The membership half at the level of Turing machines. Its statement mentions no verifier
program: only the machine model, the tape conventions, polynomials, and `SATStr`. -/

#assert_statement_surface CookLevin.SATStr_inNP =>
  -- 1. The claim (`Basic/StringTM.lean`).
  CookLevin.inNP
  CookLevin.decidesPairInTime
  CookLevin.pairTape
  CookLevin.symbolsOf
  -- 2. Turing machines.
  FlatTM
  flatTM
  FlatTM.sig
  FlatTM.tapes
  FlatTM.states
  FlatTM.start
  FlatTM.halt
  FlatTM.trans
  FlatTMTransEntry
  FlatTMTransEntry.src_state
  FlatTMTransEntry.src_tape_vals
  FlatTMTransEntry.dst_state
  FlatTMTransEntry.dst_write_vals
  FlatTMTransEntry.move_dirs
  TMMove
  TMMove.Lmove
  TMMove.Rmove
  TMMove.Nmove
  FlatTMConfig
  FlatTMConfig.state_idx
  FlatTMConfig.tapes
  initFlatConfig
  currentTapeSymbol
  writeCurrentTapeSymbol
  moveTapeHead
  tapeStep
  entryMatchesConfig
  applyTransitionEntry
  stepFlatTM
  haltingStateReached
  runFlatTM
  validFlatTM
  flatTMTransEntryValid
  flatTMOptionSymbolsBounded
  -- 3. Polynomials.
  inOPoly
  inO
  -- 4. SAT.
  var
  literal
  clause
  cnf
  assgn
  evalVar
  evalLiteral
  evalClause
  evalCnf
  satisfiesCnf
  SAT
  -- 5. SAT as a language of bit strings.
  SATStr
  SATStr.cnfOf
  CookLevin.Lang.strBits
  CnfWellFormed.parseTotal
  CnfWellFormed.wfCnfB
  CnfWellFormed.scanRun
  CnfWellFormed.scanStep
  CnfSerialize.decCnf
  CnfSerialize.decCnfAux
  CnfSerialize.decClause
  CnfSerialize.scanUnary

end CookLevin.ReadingList
