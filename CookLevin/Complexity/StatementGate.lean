import Complexity.Meta.StatementSurface
import Complexity.NP.SAT.CookLevin.CookLevinHonest
import Complexity.NP.SAT.CookLevin.Reductions.SAT_to_SATStr_comp

set_option autoImplicit false

/-! # The statement gate — *everything a reviewer must read*, checked by `lake build`

**This is the reading list for the whole development, and the build proves it is
complete.** Every constant below is declared in this repository and is reachable
from the **statement** — the type, not the proof — of the theorem it sits under.
Nothing else of ours can affect what that theorem says. If you read these
definitions and believe each one means what its name suggests, then you know the
headline is the Cook–Levin theorem and not something weaker wearing its name.

Everything the lists do *not* mention is either Lean's own kernel/`Init`/`Std`,
or Mathlib. See `Complexity/Meta/StatementSurface.lean` for exactly what
"reachable" means, why theorem *proofs* are excluded, and why the filter that
hides compiler-generated companions cannot hide anything else.

## How to use this file

Read it **top-down in group order**, not alphabetically. The groups are:

1. *what is claimed* — the complexity-theoretic vocabulary;
2. *the programming layer* — the syntax the witnesses are written in;
3. *the machine* — the Turing machine that layer compiles to, and which every
   "polynomial time" claim is ultimately about;
4. *SAT* — that the problem is satisfiability;
5. *input size* — the measure the polynomials are polynomials in.

Group 1 is the one that decides whether the theorem is the right theorem;
groups 2–5 decide whether it is about real machines and real formulas. There is
no group for the *reduction*: the reduction is existentially quantified, so no
choice we made in building it appears here. That is precisely why encoding
honesty needs a separate instrument (`Complexity/HonestyGate.lean`), and why
"the statement is clean" and "the witness is honest" are two different claims
with two different gates.

## Read this before you edit either list

A name appearing in the gate's failure output is **not a chore**. It means the
statement of a headline theorem changed, and therefore that a reviewer's reading
obligation changed. Say what and why in `README.md`'s reviewer checklist in the
same commit; the list is the evidence, the README is the explanation.

## The measured trade between the two headlines (2026-08-06)

`CookLevinStr` costs **103** definitions, `SATStr_NPcompleteStr` **113**. The
string-language headline is the textbook shape — `List Bool` on both sides of
the arrow — but its statement surface is *larger*, not smaller, and it is worth
being precise about why. All 103 of `CookLevinStr`'s names recur in it except
`instEncodableNat`; the eleven additions are group 6 below: `SATStr` is
*defined* by parsing its input (`cnfOf = parseTotal ∘ strBits`), so the
well-formedness scanner and the CNF parser are part of what the string headline
literally says.

A reviewer does not have to read them, but the escape is a **theorem**, not a
definition: `SATStr.satStr_iff : SATStr x ↔ ∃ N, strBits x = encodeCnf N ∧ SAT N`
re-presents the language in terms of the 12-line encoder `EvalCnfCmd.encodeCnf`,
and it is axiom-clean (`Complexity/SoundnessGate.lean`). Read the definition or
read the theorem — but the choice is now a measured one instead of a claim. -/

namespace Complexity.StatementGate

/-! ## ★ `CookLevinHonest.CookLevinStr : NPcompleteStr SAT`

Every NP string language reduces to SAT, and SAT is in NP. 103 definitions. -/

#assert_statement_surface CookLevinHonest.CookLevinStr =>
  -- 1. What is claimed: hardness, membership, reduction, verifier, polynomial.
  Complexity.Lang.NPcompleteStr
  Complexity.Lang.NPhardStr
  Complexity.Lang.inNPStr
  Complexity.Lang.InNPWitnessStr
  Complexity.Lang.inNPLangFreeSplit
  Complexity.Lang.InNPWitnessLangFreeSplit
  Complexity.Lang.InNPWitnessLangFreeSplit.encX
  Complexity.Lang.certState
  Complexity.Lang.reducesPolyMO'
  Complexity.Lang.ReductionWitness'
  Complexity.Lang.polyTimeComputable'
  Complexity.Lang.PolyTimeComputableWitness'
  Complexity.Lang.ComputesBy
  Complexity.Lang.DecidesLang
  Complexity.Lang.DecidesLang.encodeIn
  polyCertRel
  PolyCertRelWitness
  inOPoly
  inO
  monotonic
  -- 2. The programming layer: the syntax every witness's program is written in,
  --    its semantics, and its cost — the number the polynomials bound.
  Complexity.Lang.Var
  Complexity.Lang.State
  Complexity.Lang.State.get
  Complexity.Lang.State.set
  Complexity.Lang.State.size
  Complexity.Lang.State.isAccept
  Complexity.Lang.State.isReject
  Complexity.Lang.Op
  Complexity.Lang.Op.clear
  Complexity.Lang.Op.copy
  Complexity.Lang.Op.concat
  Complexity.Lang.Op.head
  Complexity.Lang.Op.tail
  Complexity.Lang.Op.appendZero
  Complexity.Lang.Op.appendOne
  Complexity.Lang.Op.eqBit
  Complexity.Lang.Op.nonEmpty
  Complexity.Lang.Op.eval
  Complexity.Lang.Op.cost
  Complexity.Lang.Op.UsesBelow
  Complexity.Lang.Cmd
  Complexity.Lang.Cmd.op
  Complexity.Lang.Cmd.seq
  Complexity.Lang.Cmd.ifBit
  Complexity.Lang.Cmd.forBnd
  Complexity.Lang.Cmd.eval
  Complexity.Lang.Cmd.cost
  Complexity.Lang.Cmd.run
  Complexity.Lang.Cmd.decides
  Complexity.Lang.Cmd.UsesBelow
  Complexity.Lang.Compile.BitState
  -- 3. The machine: `stepFlatTM` is the Turing machine step relation, and the
  --    reduction witness's `machine` field is a compiled `FlatTM` running it.
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
  stepFlatTM
  runFlatTM
  tapeStep
  applyTransitionEntry
  entryMatchesConfig
  currentTapeSymbol
  writeCurrentTapeSymbol
  moveTapeHead
  initFlatConfig
  initialTapes
  haltingStateReached
  validFlatTM
  flatTMTransEntryValid
  flatTMOptionSymbolsBounded
  -- 4. SAT: that the problem really is satisfiability of a CNF.
  SAT
  cnf
  clause
  literal
  var
  assgn
  satisfiesCnf
  evalCnf
  evalClause
  evalLiteral
  evalVar
  -- 5. Input size: what the polynomials are polynomials in.
  encodable
  encodable.size
  instEncodableBool
  instEncodableNat
  instEncodableList
  instEncodableProd

/-! ## ★ `SATStrComp.SATStr_NPcompleteStr : NPcompleteStr SATStr`

The same theorem with `List Bool` on both sides of the arrow. 113 definitions:
groups 1–5 above minus `instEncodableNat`, plus group 6. -/

#assert_statement_surface SATStrComp.SATStr_NPcompleteStr =>
  -- 1. What is claimed.
  Complexity.Lang.NPcompleteStr
  Complexity.Lang.NPhardStr
  Complexity.Lang.inNPStr
  Complexity.Lang.InNPWitnessStr
  Complexity.Lang.inNPLangFreeSplit
  Complexity.Lang.InNPWitnessLangFreeSplit
  Complexity.Lang.InNPWitnessLangFreeSplit.encX
  Complexity.Lang.certState
  Complexity.Lang.reducesPolyMO'
  Complexity.Lang.ReductionWitness'
  Complexity.Lang.polyTimeComputable'
  Complexity.Lang.PolyTimeComputableWitness'
  Complexity.Lang.ComputesBy
  Complexity.Lang.DecidesLang
  Complexity.Lang.DecidesLang.encodeIn
  polyCertRel
  PolyCertRelWitness
  inOPoly
  inO
  monotonic
  -- 2. The programming layer.
  Complexity.Lang.Var
  Complexity.Lang.State
  Complexity.Lang.State.get
  Complexity.Lang.State.set
  Complexity.Lang.State.size
  Complexity.Lang.State.isAccept
  Complexity.Lang.State.isReject
  Complexity.Lang.Op
  Complexity.Lang.Op.clear
  Complexity.Lang.Op.copy
  Complexity.Lang.Op.concat
  Complexity.Lang.Op.head
  Complexity.Lang.Op.tail
  Complexity.Lang.Op.appendZero
  Complexity.Lang.Op.appendOne
  Complexity.Lang.Op.eqBit
  Complexity.Lang.Op.nonEmpty
  Complexity.Lang.Op.eval
  Complexity.Lang.Op.cost
  Complexity.Lang.Op.UsesBelow
  Complexity.Lang.Cmd
  Complexity.Lang.Cmd.op
  Complexity.Lang.Cmd.seq
  Complexity.Lang.Cmd.ifBit
  Complexity.Lang.Cmd.forBnd
  Complexity.Lang.Cmd.eval
  Complexity.Lang.Cmd.cost
  Complexity.Lang.Cmd.run
  Complexity.Lang.Cmd.decides
  Complexity.Lang.Cmd.UsesBelow
  Complexity.Lang.Compile.BitState
  -- 3. The machine.
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
  stepFlatTM
  runFlatTM
  tapeStep
  applyTransitionEntry
  entryMatchesConfig
  currentTapeSymbol
  writeCurrentTapeSymbol
  moveTapeHead
  initFlatConfig
  initialTapes
  haltingStateReached
  validFlatTM
  flatTMTransEntryValid
  flatTMOptionSymbolsBounded
  -- 4. SAT.
  SAT
  cnf
  clause
  literal
  var
  assgn
  satisfiesCnf
  evalCnf
  evalClause
  evalLiteral
  evalVar
  -- 5. Input size.
  encodable
  encodable.size
  instEncodableBool
  instEncodableList
  instEncodableProd
  -- 6. The language `SATStr` itself — the price of the textbook shape.
  --    `SATStr x = SAT (cnfOf x)`, `cnfOf = parseTotal ∘ strBits`: the string is
  --    read as a CNF by a total parser whose malformed branch is a canonically
  --    UNSATISFIABLE formula, so "not an encoding" and "encodes something
  --    unsatisfiable" are one verdict. `satStr_iff` lets you read
  --    `EvalCnfCmd.encodeCnf` instead of these eleven.
  SATStr.SATStr
  SATStr.cnfOf
  Complexity.Lang.strBits
  CnfWellFormed.parseTotal
  CnfWellFormed.wfCnfB
  CnfWellFormed.scanRun
  CnfWellFormed.scanStep
  CnfSerialize.decCnf
  CnfSerialize.decCnfAux
  CnfSerialize.decClause
  CnfSerialize.scanUnary

end Complexity.StatementGate
