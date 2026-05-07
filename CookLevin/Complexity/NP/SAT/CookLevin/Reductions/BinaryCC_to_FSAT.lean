import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC
import Complexity.NP.FSAT
import Mathlib.Tactic

set_option autoImplicit false

open Classical

namespace BinaryCCToFSAT

abbrev falseFormula : formula := .fneg .ftrue

/-- Conjunction over a list of formulas. -/
def listAnd : List formula → formula
  | [] => .ftrue
  | f :: fs => .fand f (listAnd fs)

/-- Disjunction over a list of formulas. -/
def listOr : List formula → formula
  | [] => falseFormula
  | f :: fs => .forr f (listOr fs)

/-- Encode a single bit-string starting at variable `start`. -/
def encodeBitsAt : Nat → List Bool → formula
  | _, [] => .ftrue
  | start, b :: bs =>
      .fand (if b then .fvar start else .fneg (.fvar start)) (encodeBitsAt (start + 1) bs)

/-- Encode one covering card at two absolute tableau positions. -/
def encodeCardAt (startA startB : Nat) (card : CCCard Bool) : formula :=
  .fand (encodeBitsAt startA card.prem) (encodeBitsAt startB card.conc)

/-- Disjunction over all cards that could cover at the chosen positions. -/
def encodeCardsAt (C : BinaryCC) (startA startB : Nat) : formula :=
  listOr (C.cards.map (encodeCardAt startA startB))

/-- Constraint for one local offset in one tableau row transition. -/
def encodeStepConstraint (C : BinaryCC) (line step : Nat) : formula :=
  if _ : step * C.offset + C.width ≤ C.init.length then
    encodeCardsAt C (line * C.init.length + step * C.offset)
      ((line + 1) * C.init.length + step * C.offset)
  else
    .ftrue

/-- Conjunction of all local transition constraints for one tableau row. -/
def encodeLineConstraints (C : BinaryCC) (line : Nat) : formula :=
  listAnd ((List.range (C.init.length + 1)).map (encodeStepConstraint C line))

/-- Conjunction of all row-transition constraints in the tableau. -/
def encodeAllStepConstraints (C : BinaryCC) : formula :=
  listAnd ((List.range C.steps).map (encodeLineConstraints C))

/-- Encode that a final substring occurs at a chosen offset in the last row. -/
def encodeFinalAtStep (C : BinaryCC) (step : Nat) (bits : List Bool) : formula :=
  if _ : step * C.offset ≤ C.init.length then
    encodeBitsAt (C.steps * C.init.length + step * C.offset) bits
  else
    falseFormula

/-- Disjunction over all admissible offsets for one accepting substring. -/
def encodeFinalString (C : BinaryCC) (bits : List Bool) : formula :=
  listOr ((List.range (C.init.length + 1)).map (fun step => encodeFinalAtStep C step bits))

/-- Final-row acceptance constraint. -/
def encodeFinalConstraint (C : BinaryCC) : formula :=
  listOr (C.final.map (encodeFinalString C))

/-- The direct Cook-Levin tableau formula for a wellformed `BinaryCC` instance. -/
def encodeTableau (C : BinaryCC) : formula :=
  .fand (encodeBitsAt 0 C.init) (.fand (encodeAllStepConstraints C) (encodeFinalConstraint C))

/-- Non-wellformed instances are mapped to a trivial unsatisfiable formula. -/
noncomputable def BinaryCC_to_FSAT_instance (C : BinaryCC) : formula :=
  if _ : BinaryCC_wellformed C then encodeTableau C else falseFormula

end BinaryCCToFSAT

open BinaryCCToFSAT

theorem falseFormula_unsat : ¬ FSAT falseFormula := by
  rintro ⟨a, h⟩
  simp [satisfiesFormula, evalFormula] at h

theorem BinaryCC_to_FSAT_poly : BinaryCCLang ⪯p FSAT := by
  refine ⟨⟨BinaryCC_to_FSAT_instance, ?_, ?_⟩⟩
  · sorry
  · intro C
    constructor
    · intro hBC
      sorry
    · intro hFSAT
      sorry
