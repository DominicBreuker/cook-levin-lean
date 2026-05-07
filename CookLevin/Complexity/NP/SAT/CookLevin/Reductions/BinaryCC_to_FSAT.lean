import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC
import Complexity.NP.FSAT
import Mathlib.Tactic

set_option autoImplicit false

open Classical

namespace BinaryCCToFSAT

abbrev falseFml : formula := .fneg .ftrue

def explicitAssignment (a : assgn) (lower : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => evalVar a lower :: explicitAssignment a (lower + 1) n

def trueVarsAt : Nat → List Bool → assgn
  | _, [] => []
  | start, b :: bs =>
      (if b then [start] else []) ++ trueVarsAt (start + 1) bs

def projVars (start len : Nat) (xs : List Bool) : List Bool :=
  (xs.drop start).take len

theorem explicitAssignment_length (a : assgn) (lower len : Nat) :
    (explicitAssignment a lower len).length = len := by
  induction len generalizing lower with
  | zero => simp [explicitAssignment]
  | succ len ih => simp [explicitAssignment, ih]

/-- Conjunction over a list of formulas. -/
def listAnd : List formula → formula
  | [] => .ftrue
  | f :: fs => .fand f (listAnd fs)

/-- Disjunction over a list of formulas. -/
def listOr : List formula → formula
  | [] => falseFml
  | f :: fs => .forr f (listOr fs)

/-- Encode a single bit-string starting at variable `start`. -/
def encodeBitsAt : Nat → List Bool → formula
  | _, [] => .ftrue
  | start, b :: bs =>
      .fand (if b then .fvar start else .fneg (.fvar start)) (encodeBitsAt (start + 1) bs)

theorem trueVarsAt_ge :
    ∀ start bs v, v ∈ trueVarsAt start bs → start ≤ v
  | _, [], _, hv => by cases hv
  | start, b :: bs, v, hv => by
      cases b <;> simp [trueVarsAt] at hv
      · have hge : start + 1 ≤ v := trueVarsAt_ge (start + 1) bs v hv
        omega
      · rcases hv with rfl | hv
        · omega
        · have hge : start + 1 ≤ v := trueVarsAt_ge (start + 1) bs v hv
          omega

theorem explicitAssignment_getElem? (a : assgn) (lower len i : Nat) :
    (explicitAssignment a lower len)[i]? =
      if h : i < len then some (evalVar a (lower + i)) else none := by
  induction len generalizing lower i with
  | zero => simp [explicitAssignment]
  | succ len ih =>
      cases i with
      | zero => simp [explicitAssignment]
      | succ i =>
          simp [explicitAssignment, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem eval_listAnd_iff (a : assgn) :
    ∀ fs, evalFormula a (listAnd fs) = true ↔ ∀ f, f ∈ fs → evalFormula a f = true
  | [] => by simp [listAnd, evalFormula]
  | f :: fs => by
      simp [listAnd, evalFormula, eval_listAnd_iff a fs, Bool.and_eq_true]

theorem eval_listOr_iff (a : assgn) :
    ∀ fs, evalFormula a (listOr fs) = true ↔ ∃ f, f ∈ fs ∧ evalFormula a f = true
  | [] => by simp [listOr, falseFml, evalFormula]
  | f :: fs => by
      simp [listOr, evalFormula, eval_listOr_iff a fs, Bool.or_eq_true]

theorem encodeBitsAt_iff (a : assgn) :
    ∀ start bs, evalFormula a (encodeBitsAt start bs) = true ↔ explicitAssignment a start bs.length = bs
  | _, [] => by simp [encodeBitsAt, explicitAssignment, evalFormula]
  | start, b :: bs => by
      cases b <;>
        simp [encodeBitsAt, explicitAssignment, evalFormula, encodeBitsAt_iff a (start + 1) bs,
          Bool.and_eq_true]

theorem evalVar_trueVarsAt :
    ∀ start bs i, i < bs.length → evalVar (trueVarsAt start bs) (start + i) = bs[i]!
  | _, [], _, h => by cases Nat.not_lt_zero _ h
  | start, b :: bs, 0, _ => by
      cases b
      · have hnot : start ∉ trueVarsAt (start + 1) bs := by
          intro hmem
          have hge := trueVarsAt_ge (start + 1) bs start hmem
          omega
        simp [trueVarsAt, evalVar, hnot]
      · simp [trueVarsAt, evalVar]
  | start, b :: bs, i + 1, h => by
      have hi : i < bs.length := Nat.lt_of_succ_lt_succ h
      cases b
      · simpa [trueVarsAt, evalVar, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (evalVar_trueVarsAt (start + 1) bs i hi)
      · have hne : start + (i + 1) ≠ start := by omega
        simpa [trueVarsAt, evalVar, hne, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (evalVar_trueVarsAt (start + 1) bs i hi)

theorem explicitAssignment_trueVarsAt (start : Nat) (bs : List Bool) :
    explicitAssignment (trueVarsAt start bs) start bs.length = bs := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < bs.length
  · have hleft := explicitAssignment_getElem? (trueVarsAt start bs) start bs.length i
    rw [hleft]
    simp [hi, evalVar_trueVarsAt start bs i hi]
  · have hleft := explicitAssignment_getElem? (trueVarsAt start bs) start bs.length i
    rw [hleft]
    simp [hi]


theorem projVars_length {xs : List Bool} {start len : Nat} (h : start + len ≤ xs.length) :
    (projVars start len xs).length = len := by
  unfold projVars
  rw [List.length_take, List.length_drop]
  omega

theorem projVars_eq_take_drop (start : Nat) (xs : List Bool) :
    projVars start (xs.drop start).length xs = xs.drop start := by
  unfold projVars
  simp

theorem projVars_prefix {subs xs : List Bool} {start : Nat}
    (h : isPrefix subs (xs.drop start)) :
    projVars start subs.length xs = subs := by
  rcases h with ⟨rest, hrest⟩
  unfold projVars
  rw [hrest]
  simp

theorem prefix_of_projVars {xs subs : List Bool} {start : Nat}
    (h : projVars start subs.length xs = subs) :
    isPrefix subs (xs.drop start) := by
  refine ⟨xs.drop (start + subs.length), ?_⟩
  have htake : List.take subs.length (xs.drop start) = subs := by
    simpa [projVars] using h
  calc
    xs.drop start = List.take subs.length (xs.drop start) ++ List.drop subs.length (xs.drop start) := by
      exact (List.take_append_drop subs.length (xs.drop start)).symm
    _ = subs ++ List.drop subs.length (xs.drop start) := by rw [htake]
    _ = subs ++ xs.drop (start + subs.length) := by rw [List.drop_drop]

theorem explicitAssignment_shift (a : assgn) (base offset len total : Nat)
    (h : offset + len ≤ total) :
    explicitAssignment a (base + offset) len =
      projVars offset len (explicitAssignment a base total) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < len
  · have h' : offset + i < total := by omega
    calc
      (explicitAssignment a (base + offset) len)[i]? = some (evalVar a (base + offset + i)) := by
        simpa [hi, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (explicitAssignment_getElem? a (base + offset) len i)
      _ = (projVars offset len (explicitAssignment a base total))[i]? := by
        simp [projVars, hi, h', explicitAssignment_getElem?, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · rw [explicitAssignment_getElem?]
    simp [projVars, hi]

theorem explicitAssignment_trueVarsAt_shift (bs : List Bool) (start len : Nat)
    (h : start + len ≤ bs.length) :
    explicitAssignment (trueVarsAt 0 bs) start len = projVars start len bs := by
  calc
    explicitAssignment (trueVarsAt 0 bs) start len =
        projVars start len (explicitAssignment (trueVarsAt 0 bs) 0 bs.length) := by
          simpa using explicitAssignment_shift (trueVarsAt 0 bs) 0 start len bs.length h
    _ = projVars start len bs := by rw [explicitAssignment_trueVarsAt 0 bs]

theorem projVars_app1 (xs ys : List Bool) :
    projVars 0 xs.length (xs ++ ys) = xs := by
  unfold projVars
  simp

theorem projVars_app2 (xs ys : List Bool) :
    projVars xs.length ys.length (xs ++ ys) = ys := by
  unfold projVars
  simp

theorem projVars_app3 (xs ys : List Bool) (u m : Nat) :
    projVars (xs.length + u) m (xs ++ ys) = projVars u m ys := by
  unfold projVars
  rw [List.drop_append]
  rw [List.drop_eq_nil_of_le (by omega)]
  simp

theorem projVars_drop (start len : Nat) (xs : List Bool) :
    projVars 0 len (xs.drop start) = projVars start len xs := by
  simp [projVars]

def rowBits (a : assgn) (C : BinaryCC) (line : Nat) : List Bool :=
  explicitAssignment a (line * C.init.length) C.init.length

theorem segment_eq_projVars_row (a : assgn) (C : BinaryCC) (line offset len : Nat)
    (h : offset + len ≤ C.init.length) :
    explicitAssignment a (line * C.init.length + offset) len =
      projVars offset len (rowBits a C line) := by
  simpa [rowBits, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    explicitAssignment_shift a (line * C.init.length) offset len C.init.length h

/-- Encode one covering card at two absolute tableau positions. -/
def encodeCardAt (startA startB : Nat) (card : CCCard Bool) : formula :=
  .fand (encodeBitsAt startA card.prem) (encodeBitsAt startB card.conc)

/-- Disjunction over all cards that could cover at the chosen positions. -/
def encodeCardsAt (C : BinaryCC) (startA startB : Nat) : formula :=
  listOr (C.cards.map (encodeCardAt startA startB))

theorem encodeCardAt_iff (a : assgn) (startA startB : Nat) (card : CCCard Bool) :
    evalFormula a (encodeCardAt startA startB card) = true ↔
      explicitAssignment a startA card.prem.length = card.prem ∧
      explicitAssignment a startB card.conc.length = card.conc := by
  simp [encodeCardAt, encodeBitsAt_iff, evalFormula, Bool.and_eq_true]

theorem encodeCardsAt_iff (a : assgn) (C : BinaryCC) (startA startB : Nat) :
    evalFormula a (encodeCardsAt C startA startB) = true ↔
      ∃ card, card ∈ C.cards ∧
        explicitAssignment a startA card.prem.length = card.prem ∧
        explicitAssignment a startB card.conc.length = card.conc := by
  constructor
  · intro h
    rcases (eval_listOr_iff a (C.cards.map (encodeCardAt startA startB))).mp h with ⟨f, hf, hsat⟩
    rcases List.mem_map.mp hf with ⟨card, hcard, rfl⟩
    exact ⟨card, hcard, (encodeCardAt_iff a startA startB card).mp hsat⟩
  · rintro ⟨card, hcard, hprem, hconc⟩
    refine (eval_listOr_iff a (C.cards.map (encodeCardAt startA startB))).mpr ?_
    refine ⟨encodeCardAt startA startB card, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨card, hcard, rfl⟩
    · exact (encodeCardAt_iff a startA startB card).mpr ⟨hprem, hconc⟩

theorem prefix_length_le {α : Type} {xs ys : List α} :
    isPrefix xs ys → xs.length ≤ ys.length := by
  rintro ⟨rest, rfl⟩
  simp

theorem coversHead_of_segments {row row' : List Bool} {card : CCCard Bool}
    {offset width : Nat}
    (hprem : projVars offset width row = card.prem)
    (hconc : projVars offset width row' = card.conc)
    (hwprem : card.prem.length = width)
    (hwconc : card.conc.length = width) :
    coversHead card (row.drop offset) (row'.drop offset) := by
  constructor
  · rw [← hwprem] at hprem
    exact prefix_of_projVars hprem
  · rw [← hwconc] at hconc
    exact prefix_of_projVars hconc

theorem segments_of_coversHead {row row' : List Bool} {card : CCCard Bool}
    {offset width : Nat}
    (hcover : coversHead card row row')
    (hwprem : card.prem.length = width)
    (hwconc : card.conc.length = width) :
    projVars 0 width row = card.prem ∧ projVars 0 width row' = card.conc := by
  constructor
  · rw [← hwprem]
    exact projVars_prefix hcover.1
  · rw [← hwconc]
    exact projVars_prefix hcover.2

/-- Constraint for one local offset in one tableau row transition. -/
def encodeStepConstraint (C : BinaryCC) (line step : Nat) : formula :=
  if h : step * C.offset + C.width ≤ C.init.length then
    let _ : step * C.offset + C.width ≤ C.init.length := h
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
  if h : step * C.offset ≤ C.init.length then
    let _ : step * C.offset ≤ C.init.length := h
    encodeBitsAt (C.steps * C.init.length + step * C.offset) bits
  else
    falseFml

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
  if _ : BinaryCC_wellformed C then encodeTableau C else falseFml

end BinaryCCToFSAT

open BinaryCCToFSAT

theorem falseFml_unsat : ¬ FSAT falseFml := by
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
