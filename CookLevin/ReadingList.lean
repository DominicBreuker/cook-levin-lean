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

/-! ## `cook_levin : NPcomplete SATStr`

The statement mentions Turing machines, the tape conventions for strings, polynomials and
CNF formulas, and nothing else of this repository: in particular nothing of the register
language the proof is carried out in. -/

#assert_statement_surface CookLevin.cook_levin =>
  -- 1. The claim (`Basic/StringTM.lean`).
  CookLevin.NPcomplete
  CookLevin.NPhard
  CookLevin.inNP
  CookLevin.reducesPoly
  CookLevin.computesInTime
  CookLevin.decidesPairInTime
  CookLevin.stringTape
  CookLevin.pairTape
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
  -- 3. Polynomials (`Basic/Definitions.lean`).
  inOPoly
  inO
  -- 4. SAT (`Basic/Definitions.lean`, `SAT/SAT.lean`).
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
  -- 5. SAT as a language of bit strings (`SAT/SATStr.lean`, `Lang/SerializeStr.lean`,
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

end CookLevin.ReadingList
