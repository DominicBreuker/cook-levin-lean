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
  if h : step * C.offset + bits.length ≤ C.init.length then
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
  if hWf : BinaryCC_wellformed C then encodeTableau C else falseFml

theorem rowBits_length (a : assgn) (C : BinaryCC) (line : Nat) :
    (rowBits a C line).length = C.init.length := by
  simp [rowBits, explicitAssignment_length]

theorem projVars_all (xs : List Bool) :
    projVars 0 xs.length xs = xs := by
  unfold projVars
  simp

theorem projVars_length_le (start len : Nat) (xs : List Bool) :
    (projVars start len xs).length ≤ xs.length - start := by
  unfold projVars
  rw [List.length_take, List.length_drop]
  exact Nat.min_le_right _ _

theorem rowBits_trueVarsAt (C : BinaryCC) (m : List Bool) (line : Nat)
    (h : line * C.init.length + C.init.length ≤ m.length) :
    rowBits (trueVarsAt 0 m) C line = projVars (line * C.init.length) C.init.length m := by
  unfold rowBits
  simpa using explicitAssignment_trueVarsAt_shift m (line * C.init.length) C.init.length h

theorem Binary_relpower_length {offset width : Nat} (cards : List (CCCard Bool)) :
    ∀ {n a b}, relpower (validStep offset width cards) n a b → a.length = b.length
  | _, _, _, .refl _ => rfl
  | _, _, _, .step hstep hrest => hstep.1.trans (Binary_relpower_length cards hrest)

theorem encodeLineConstraints_iff (a : assgn) (C : BinaryCC)
    (hWf : BinaryCC_wellformed C) (line : Nat) :
    evalFormula a (encodeLineConstraints C line) = true ↔
      validStep C.offset C.width C.cards (rowBits a C line) (rowBits a C (line + 1)) := by
  rcases hWf with ⟨hwidthPos, hoffPos, _, _, hcardsW, _⟩
  constructor
  · intro h
    refine ⟨by simp [rowBits, explicitAssignment_length], ?_⟩
    intro step hstepRow
    have hstep : step * C.offset + C.width ≤ C.init.length := by
      simpa [rowBits_length] using hstepRow
    have hstepMem : step ∈ List.range (C.init.length + 1) := by
      have hlt : step < C.init.length + 1 := by
        have hoff1 : 1 ≤ C.offset := Nat.succ_le_of_lt hoffPos
        have hmul : step ≤ step * C.offset := by
          calc
            step = step * 1 := by simp
            _ ≤ step * C.offset := Nat.mul_le_mul_left _ hoff1
        omega
      simp [List.mem_range, hlt]
    have hall :=
      (eval_listAnd_iff a ((List.range (C.init.length + 1)).map (encodeStepConstraint C line))).mp h
    have hloc : evalFormula a (encodeStepConstraint C line step) = true := by
      exact hall _ (List.mem_map.mpr ⟨step, hstepMem, rfl⟩)
    unfold encodeStepConstraint at hloc
    simp [hstep] at hloc
    rcases (encodeCardsAt_iff a C
      (line * C.init.length + step * C.offset)
      ((line + 1) * C.init.length + step * C.offset)).mp hloc with ⟨card, hcard, hpremAbs, hconcAbs⟩
    have hw := hcardsW card hcard
    rw [hw.1] at hpremAbs
    rw [hw.2] at hconcAbs
    refine ⟨card, hcard, ?_⟩
    apply coversHead_of_segments
    · calc
        projVars (step * C.offset) C.width (rowBits a C line)
            = explicitAssignment a (line * C.init.length + step * C.offset) C.width := by
                symm
                exact segment_eq_projVars_row a C line (step * C.offset) C.width hstep
        _ = card.prem := hpremAbs
    · calc
        projVars (step * C.offset) C.width (rowBits a C (line + 1))
            = explicitAssignment a ((line + 1) * C.init.length + step * C.offset) C.width := by
                symm
                exact segment_eq_projVars_row a C (line + 1) (step * C.offset) C.width hstep
        _ = card.conc := hconcAbs
    · exact hw.1
    · exact hw.2
  · intro h
    refine (eval_listAnd_iff a ((List.range (C.init.length + 1)).map (encodeStepConstraint C line))).mpr ?_
    intro f hf
    rcases List.mem_map.mp hf with ⟨step, hstepMem, rfl⟩
    by_cases hstep : step * C.offset + C.width ≤ C.init.length
    · have hstepRow : step * C.offset + C.width ≤ (rowBits a C line).length := by
        simpa [rowBits_length] using hstep
      rcases h.2 step hstepRow with ⟨card, hcard, hcover⟩
      have hw := hcardsW card hcard
      have hpremAbs :
          explicitAssignment a (line * C.init.length + step * C.offset) C.width = card.prem := by
        calc
          explicitAssignment a (line * C.init.length + step * C.offset) C.width
              = projVars (step * C.offset) C.width (rowBits a C line) := by
                  exact segment_eq_projVars_row a C line (step * C.offset) C.width hstep
          _ = card.prem := by
                have hseg := (segments_of_coversHead (offset := step * C.offset) (width := C.width) hcover hw.1 hw.2).1
                rw [projVars_drop] at hseg
                exact hseg
      have hconcAbs :
          explicitAssignment a ((line + 1) * C.init.length + step * C.offset) C.width = card.conc := by
        calc
          explicitAssignment a ((line + 1) * C.init.length + step * C.offset) C.width
              = projVars (step * C.offset) C.width (rowBits a C (line + 1)) := by
                  exact segment_eq_projVars_row a C (line + 1) (step * C.offset) C.width hstep
          _ = card.conc := by
                have hseg := (segments_of_coversHead (offset := step * C.offset) (width := C.width) hcover hw.1 hw.2).2
                rw [projVars_drop] at hseg
                exact hseg
      have hpremAbs' :
          explicitAssignment a (line * C.init.length + step * C.offset) card.prem.length = card.prem := by
        simpa [hw.1] using hpremAbs
      have hconcAbs' :
          explicitAssignment a ((line + 1) * C.init.length + step * C.offset) card.conc.length = card.conc := by
        simpa [hw.2] using hconcAbs
      unfold encodeStepConstraint
      simp [hstep]
      exact (encodeCardsAt_iff a C
        (line * C.init.length + step * C.offset)
        ((line + 1) * C.init.length + step * C.offset)).mpr ⟨card, hcard, hpremAbs', hconcAbs'⟩
    · exact by simp [encodeStepConstraint, hstep, evalFormula]

theorem encodeAllStepConstraints_iff (a : assgn) (C : BinaryCC)
    (hWf : BinaryCC_wellformed C) :
    evalFormula a (encodeAllStepConstraints C) = true ↔
      ∀ line, line < C.steps → validStep C.offset C.width C.cards (rowBits a C line) (rowBits a C (line + 1)) := by
  constructor
  · intro h line hline
    have hall := (eval_listAnd_iff a ((List.range C.steps).map (encodeLineConstraints C))).mp h
    have hmem : line ∈ List.range C.steps := by simp [List.mem_range, hline]
    exact (encodeLineConstraints_iff a C hWf line).mp (hall _ (List.mem_map.mpr ⟨line, hmem, rfl⟩))
  · intro h
    refine (eval_listAnd_iff a ((List.range C.steps).map (encodeLineConstraints C))).mpr ?_
    intro f hf
    rcases List.mem_map.mp hf with ⟨line, hlineMem, rfl⟩
    have hline : line < C.steps := by simpa [List.mem_range] using hlineMem
    exact (encodeLineConstraints_iff a C hWf line).mpr (h line hline)

theorem encodeFinalAtStep_iff (a : assgn) (C : BinaryCC) (step : Nat) (bits : List Bool) :
    evalFormula a (encodeFinalAtStep C step bits) = true ↔
      step * C.offset + bits.length ≤ C.init.length ∧
      projVars (step * C.offset) bits.length (rowBits a C C.steps) = bits := by
  by_cases hstep : step * C.offset + bits.length ≤ C.init.length
  · constructor
    · intro h
      unfold encodeFinalAtStep at h
      simp [hstep] at h
      refine ⟨hstep, ?_⟩
      calc
        projVars (step * C.offset) bits.length (rowBits a C C.steps)
            = explicitAssignment a (C.steps * C.init.length + step * C.offset) bits.length := by
                symm
                exact segment_eq_projVars_row a C C.steps (step * C.offset) bits.length hstep
        _ = bits := by
              exact (encodeBitsAt_iff a (C.steps * C.init.length + step * C.offset) bits).mp
                (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h)
    · rintro ⟨_, hbits⟩
      unfold encodeFinalAtStep
      simp [hstep]
      have habs :
          explicitAssignment a (C.steps * C.init.length + step * C.offset) bits.length = bits := by
        calc
          explicitAssignment a (C.steps * C.init.length + step * C.offset) bits.length
              = projVars (step * C.offset) bits.length (rowBits a C C.steps) := by
                  exact segment_eq_projVars_row a C C.steps (step * C.offset) bits.length hstep
          _ = bits := hbits
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (encodeBitsAt_iff a (C.steps * C.init.length + step * C.offset) bits).mpr habs
  · constructor
    · intro h
      unfold encodeFinalAtStep at h
      simp [hstep, falseFml, evalFormula] at h
    · rintro ⟨hbound, _⟩
      exact (hstep hbound).elim

theorem encodeFinalString_iff (a : assgn) (C : BinaryCC)
    (hWf : BinaryCC_wellformed C) (bits : List Bool) :
    evalFormula a (encodeFinalString C bits) = true ↔
      ∃ step, step * C.offset ≤ C.init.length ∧
        isPrefix bits ((rowBits a C C.steps).drop (step * C.offset)) := by
  rcases hWf with ⟨_, hoffPos, _, _, _, _⟩
  constructor
  · intro h
    rcases (eval_listOr_iff a ((List.range (C.init.length + 1)).map (fun step => encodeFinalAtStep C step bits))).mp h with
      ⟨f, hf, hsat⟩
    rcases List.mem_map.mp hf with ⟨step, hstepMem, rfl⟩
    rcases (encodeFinalAtStep_iff a C step bits).mp hsat with ⟨hbound, hbits⟩
    refine ⟨step, Nat.le_trans (Nat.le_add_right _ _) hbound, ?_⟩
    exact prefix_of_projVars hbits
  · rintro ⟨step, hstepLe, hprefix⟩
    let suffix := (rowBits a C C.steps).drop (step * C.offset)
    have hlen : bits.length ≤ suffix.length := prefix_length_le hprefix
    have hbound : step * C.offset + bits.length ≤ C.init.length := by
      have hrowLen : (rowBits a C C.steps).length = C.init.length := rowBits_length a C C.steps
      dsimp [suffix] at hlen
      rw [List.length_drop, hrowLen] at hlen
      omega
    have hmem : step ∈ List.range (C.init.length + 1) := by
      have hlt : step < C.init.length + 1 := by
        have hmul : step ≤ step * C.offset := by
          have hoff1 : 1 ≤ C.offset := Nat.succ_le_of_lt hoffPos
          calc
            step = step * 1 := by simp
            _ ≤ step * C.offset := Nat.mul_le_mul_left _ hoff1
        omega
      simp [List.mem_range, hlt]
    refine (eval_listOr_iff a ((List.range (C.init.length + 1)).map (fun step => encodeFinalAtStep C step bits))).mpr ?_
    refine ⟨encodeFinalAtStep C step bits, List.mem_map.mpr ⟨step, hmem, rfl⟩, ?_⟩
    exact (encodeFinalAtStep_iff a C step bits).mpr ⟨hbound, projVars_prefix hprefix⟩

theorem encodeFinalConstraint_iff (a : assgn) (C : BinaryCC)
    (hWf : BinaryCC_wellformed C) :
    evalFormula a (encodeFinalConstraint C) = true ↔
      satFinal C.offset C.init.length C.final (rowBits a C C.steps) := by
  constructor
  · intro h
    rcases (eval_listOr_iff a (C.final.map (encodeFinalString C))).mp h with ⟨f, hf, hsat⟩
    rcases List.mem_map.mp hf with ⟨bits, hbits, rfl⟩
    rcases (encodeFinalString_iff a C hWf bits).mp hsat with ⟨step, hstepLe, hprefix⟩
    exact ⟨bits, step, hbits, hstepLe, hprefix⟩
  · rintro ⟨bits, step, hbits, hstepLe, hprefix⟩
    refine (eval_listOr_iff a (C.final.map (encodeFinalString C))).mpr ?_
    refine ⟨encodeFinalString C bits, List.mem_map.mpr ⟨bits, hbits, rfl⟩, ?_⟩
    exact (encodeFinalString_iff a C hWf bits).mpr ⟨step, hstepLe, hprefix⟩

theorem encodeTableau_iff (a : assgn) (C : BinaryCC) (hWf : BinaryCC_wellformed C) :
    evalFormula a (encodeTableau C) = true ↔
      rowBits a C 0 = C.init ∧
      (∀ line, line < C.steps →
        validStep C.offset C.width C.cards (rowBits a C line) (rowBits a C (line + 1))) ∧
      satFinal C.offset C.init.length C.final (rowBits a C C.steps) := by
  constructor
  · intro h
    simp [encodeTableau, evalFormula, Bool.and_eq_true] at h
    rcases h with ⟨hinit, hrest⟩
    rcases hrest with ⟨hsteps, hfinal⟩
    refine ⟨?_, (encodeAllStepConstraints_iff a C hWf).mp hsteps, (encodeFinalConstraint_iff a C hWf).mp hfinal⟩
    simpa [rowBits] using (encodeBitsAt_iff a 0 C.init).mp hinit
  · rintro ⟨hinit, hsteps, hfinal⟩
    simp [encodeTableau, evalFormula, Bool.and_eq_true]
    refine ⟨?_, (encodeAllStepConstraints_iff a C hWf).mpr hsteps, (encodeFinalConstraint_iff a C hWf).mpr hfinal⟩
    simpa [rowBits] using (encodeBitsAt_iff a 0 C.init).mpr (by simpa [rowBits] using hinit)

theorem rows_valid_to_relpower (C : BinaryCC) :
    ∀ n (rows : Nat → List Bool),
      (∀ i, i < n → validStep C.offset C.width C.cards (rows i) (rows (i + 1))) →
        relpower (validStep C.offset C.width C.cards) n (rows 0) (rows n)
  | 0, rows, _ => by
      change relpower (validStep C.offset C.width C.cards) 0 (rows 0) (rows 0)
      exact relpower.refl _
  | n + 1, rows, hrows =>
      relpower.step (hrows 0 (Nat.succ_pos _))
        (rows_valid_to_relpower C n (fun i => rows (i + 1)) (by
          intro i hi
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrows (i + 1) (Nat.succ_lt_succ hi)))

theorem relpower_valid_to_assignment (C : BinaryCC) :
    ∀ {n x y},
      relpower (validStep C.offset C.width C.cards) n x y →
        x.length = C.init.length →
          ∃ m, m.length = (n + 1) * C.init.length ∧
            projVars 0 C.init.length m = x ∧
            projVars (n * C.init.length) C.init.length m = y ∧
            ∀ i, i < n →
              validStep C.offset C.width C.cards
                (projVars (i * C.init.length) C.init.length m)
                (projVars ((i + 1) * C.init.length) C.init.length m)
  | 0, x, _, .refl _, hlen => by
      refine ⟨x, by simpa [hlen], ?_, ?_, ?_⟩
      · unfold projVars
        simpa [hlen]
      · simpa [hlen] using (projVars_all x)
      · intro i hi
        cases Nat.not_lt_zero _ hi
  | n + 1, x, y, .step hstep hrest, hlenX => by
      have hlenMid : _ := hstep.1.symm.trans hlenX
      rcases relpower_valid_to_assignment C hrest hlenMid with ⟨m, hmLen, hmFirst, hmLast, hmSteps⟩
      refine ⟨x ++ m, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, hmLen, hlenX]
        ring
      · simpa [hlenX] using (projVars_app1 x m)
      · have : projVars (x.length + n * C.init.length) C.init.length (x ++ m) =
            projVars (n * C.init.length) C.init.length m := projVars_app3 x m (n * C.init.length) C.init.length
        simpa [hlenX, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this.trans hmLast
      · intro i hi
        cases i with
        | zero =>
            have hleft : projVars 0 C.init.length (x ++ m) = x := by
              simpa [hlenX] using (projVars_app1 x m)
            have hright : projVars C.init.length C.init.length (x ++ m) = projVars 0 C.init.length m := by
              simpa [hlenX, Nat.zero_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (projVars_app3 x m 0 C.init.length)
            simpa [hleft, hright, hmFirst] using hstep
        | succ i =>
            have hi' : i < n := Nat.lt_of_succ_lt_succ hi
            have hproj1 :
                projVars ((i + 1) * C.init.length) C.init.length (x ++ m) =
                  projVars (i * C.init.length) C.init.length m := by
              simpa [hlenX, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (projVars_app3 x m (i * C.init.length) C.init.length)
            have hproj2 :
                projVars ((i + 1 + 1) * C.init.length) C.init.length (x ++ m) =
                  projVars ((i + 1) * C.init.length) C.init.length m := by
              simpa [hlenX, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (projVars_app3 x m ((i + 1) * C.init.length) C.init.length)
            simpa [hproj1, hproj2] using hmSteps i hi'

theorem encodeTableau_correct (C : BinaryCC) (hWf : BinaryCC_wellformed C) :
    FSAT (encodeTableau C) ↔
      ∃ sf, relpower (validStep C.offset C.width C.cards) C.steps C.init sf ∧
        satFinal C.offset C.init.length C.final sf := by
  constructor
  · rintro ⟨a, ha⟩
    rcases (encodeTableau_iff a C hWf).mp ha with ⟨hinit, hsteps, hfinal⟩
    refine ⟨rowBits a C C.steps, ?_, hfinal⟩
    have hrel := rows_valid_to_relpower C C.steps (rowBits a C) hsteps
    simpa [hinit] using hrel
  · rintro ⟨sf, hrel, hfinal⟩
    rcases relpower_valid_to_assignment C hrel rfl with ⟨m, hmLen, hmInit, hmLast, hmSteps⟩
    refine ⟨trueVarsAt 0 m, (encodeTableau_iff (trueVarsAt 0 m) C hWf).mpr ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · calc
        rowBits (trueVarsAt 0 m) C 0 = projVars 0 C.init.length m := by
            have hbound0 : 0 * C.init.length + C.init.length ≤ m.length := by
              rw [hmLen, Nat.zero_mul, zero_add]
              calc
                C.init.length = 1 * C.init.length := by simp
                _ ≤ (C.steps + 1) * C.init.length := Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le _))
            have h0 : rowBits (trueVarsAt 0 m) C 0 = projVars (0 * C.init.length) C.init.length m := by
              apply rowBits_trueVarsAt
              exact hbound0
            simpa [Nat.zero_mul] using h0
        _ = C.init := hmInit
    · intro line hline
      have hrow :
          rowBits (trueVarsAt 0 m) C line = projVars (line * C.init.length) C.init.length m := by
        apply rowBits_trueVarsAt
        rw [hmLen]
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.le_of_lt hline))
      have hrow' :
          rowBits (trueVarsAt 0 m) C (line + 1) = projVars ((line + 1) * C.init.length) C.init.length m := by
        apply rowBits_trueVarsAt
        rw [hmLen]
        rw [← Nat.succ_mul]
        apply Nat.mul_le_mul_right
        exact Nat.succ_le_succ (Nat.succ_le_of_lt hline)
      simpa [hrow, hrow'] using hmSteps line hline
    · rcases hfinal with ⟨bits, step, hbits, hstepLe, hprefix⟩
      refine ⟨bits, step, hbits, hstepLe, ?_⟩
      have hrow :
          rowBits (trueVarsAt 0 m) C C.steps = projVars (C.steps * C.init.length) C.init.length m := by
        apply rowBits_trueVarsAt
        rw [hmLen]
        rw [← Nat.succ_mul]
      simpa [hrow, hmLast] using hprefix

theorem BinaryCC_to_FSAT_instance_correct (C : BinaryCC) :
    BinaryCCLang C ↔ FSAT (BinaryCC_to_FSAT_instance C) := by
  by_cases hWf : BinaryCC_wellformed C
  · constructor
    · rintro ⟨_, sf, hrel, hfinal⟩
      simpa [BinaryCC_to_FSAT_instance, hWf] using
        (encodeTableau_correct C hWf).2 ⟨sf, hrel, hfinal⟩
    · intro h
      have hsat : FSAT (encodeTableau C) := by simpa [BinaryCC_to_FSAT_instance, hWf] using h
      exact ⟨hWf, (encodeTableau_correct C hWf).1 hsat⟩
  · constructor
    · rintro ⟨hwf, _⟩
      exact (hWf hwf).elim
    · intro h
      exfalso
      simpa [BinaryCC_to_FSAT_instance, hWf, falseFml, FSAT, satisfiesFormula, evalFormula] using h


-- ─── Size-bound helpers ──────────────────────────────────────────────────────

/-- encodable.size of a formula is bounded by formula_size * (formula_maxVar + 2). -/
private theorem enc_le_fsize_maxvar (f : formula) :
    encodable.size f ≤ formula_size f * (formula_maxVar f + 2) := by
  induction f with
  | ftrue => simp only [encodable_size_formula_ftrue, formula_size, formula_maxVar]; norm_num
  | fvar v => simp only [encodable_size_formula_fvar, formula_size, formula_maxVar]; omega
  | fand φ ψ ih₁ ih₂ =>
      simp only [encodable_size_formula_fand, formula_size, formula_maxVar]
      nlinarith [Nat.le_max_left (formula_maxVar φ) (formula_maxVar ψ),
                 Nat.le_max_right (formula_maxVar φ) (formula_maxVar ψ)]
  | forr φ ψ ih₁ ih₂ =>
      simp only [encodable_size_formula_forr, formula_size, formula_maxVar]
      nlinarith [Nat.le_max_left (formula_maxVar φ) (formula_maxVar ψ),
                 Nat.le_max_right (formula_maxVar φ) (formula_maxVar ψ)]
  | fneg φ ih =>
      simp only [encodable_size_formula_fneg, formula_size, formula_maxVar]; nlinarith

private theorem encodeBitsAt_maxVar_le (start : Nat) (bs : List Bool) :
    formula_maxVar (encodeBitsAt start bs) ≤ start + bs.length := by
  induction bs generalizing start with
  | nil => simp [encodeBitsAt, formula_maxVar]
  | cons b bs ih =>
      simp only [encodeBitsAt, formula_maxVar, List.length_cons]
      have hb : formula_maxVar (if b then formula.fvar start else (formula.fvar start).fneg) = start := by
        cases b <;> simp [formula_maxVar]
      rw [hb]
      have hih := ih (start + 1)
      simp only [Nat.max_le]; omega

private theorem encodeBitsAt_fsize_le (start : Nat) (bs : List Bool) :
    formula_size (encodeBitsAt start bs) ≤ 3 * bs.length + 1 := by
  induction bs generalizing start with
  | nil => simp [encodeBitsAt, formula_size]
  | cons b bs ih =>
      simp only [encodeBitsAt, formula_size, List.length_cons]
      have hb : formula_size (if b then formula.fvar start else (formula.fvar start).fneg) ≤ 2 := by
        cases b <;> simp [formula_size]
      have hih := ih (start + 1); omega

private theorem listOr_fsize (fs : List formula) :
    formula_size (listOr fs) = (fs.map formula_size).sum + fs.length + 2 := by
  induction fs with
  | nil => simp [listOr, falseFml, formula_size]
  | cons f fs ih =>
      simp only [listOr, formula_size, List.map, List.sum_cons, List.length_cons]; omega

private theorem listAnd_fsize (fs : List formula) :
    formula_size (listAnd fs) = (fs.map formula_size).sum + fs.length + 1 := by
  induction fs with
  | nil => simp [listAnd, formula_size]
  | cons f fs ih =>
      simp only [listAnd, formula_size, List.map, List.sum_cons, List.length_cons]; omega

private theorem list_sum_fsize_le {fs : List formula} {bound : Nat}
    (h : ∀ f ∈ fs, formula_size f ≤ bound) :
    (fs.map formula_size).sum ≤ fs.length * bound := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      simp only [List.map, List.sum_cons, List.length_cons]
      nlinarith [h f (by simp), ih (fun g hg => h g (by simp [hg]))]

private theorem list_length_le_size {α : Type} [encodable α] (xs : List α) :
    xs.length ≤ encodable.size xs := by
  induction xs with
  | nil => simp [encodable.size]
  | cons x xs ih => rw [encodable_size_list_cons]; simp [List.length]; omega

private theorem list_elem_size_le {α : Type} [encodable α] {xs : List α} {x : α}
    (hx : x ∈ xs) : encodable.size x ≤ encodable.size xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rw [encodable_size_list_cons]
      cases List.mem_cons.mp hx with
      | inl h => subst h; omega
      | inr h => exact le_trans (ih h) (by omega)

private theorem listOr_maxVar_le {fs : List formula} {M : Nat}
    (h : ∀ f ∈ fs, formula_maxVar f ≤ M) : formula_maxVar (listOr fs) ≤ M := by
  induction fs with
  | nil => simp [listOr, falseFml, formula_maxVar]
  | cons f fs ih =>
      simp only [listOr, formula_maxVar, Nat.max_le]
      exact ⟨h f (by simp), ih (fun g hg => h g (by simp [hg]))⟩

private theorem listAnd_maxVar_le {fs : List formula} {M : Nat}
    (h : ∀ f ∈ fs, formula_maxVar f ≤ M) : formula_maxVar (listAnd fs) ≤ M := by
  induction fs with
  | nil => simp [listAnd, formula_maxVar]
  | cons f fs ih =>
      simp only [listAnd, formula_maxVar, Nat.max_le]
      exact ⟨h f (by simp), ih (fun g hg => h g (by simp [hg]))⟩

private theorem encodeCardsAt_fsize_le (C : BinaryCC) (startA startB n : Nat)
    (hcards : encodable.size C.cards ≤ n) :
    formula_size (encodeCardsAt C startA startB) ≤ C.cards.length * (6 * n + 5) + C.cards.length + 2 := by
  unfold encodeCardsAt; rw [listOr_fsize]
  have hcprem : ∀ c ∈ C.cards, c.prem.length ≤ n := fun c hc =>
    le_trans (list_length_le_size _)
      (le_trans (by simp [encodable.size]; omega) (le_trans (list_elem_size_le hc) hcards))
  have hcconc : ∀ c ∈ C.cards, c.conc.length ≤ n := fun c hc =>
    le_trans (list_length_le_size _)
      (le_trans (by simp [encodable.size]; omega) (le_trans (list_elem_size_le hc) hcards))
  have hbound : ∀ f ∈ (C.cards.map (encodeCardAt startA startB)), formula_size f ≤ 6 * n + 5 := by
    intro f hf; rcases List.mem_map.mp hf with ⟨c, hc, rfl⟩
    simp only [encodeCardAt, formula_size]
    linarith [encodeBitsAt_fsize_le startA c.prem, encodeBitsAt_fsize_le startB c.conc,
              hcprem c hc, hcconc c hc]
  have hsum := list_sum_fsize_le hbound
  simp only [List.length_map] at hsum ⊢
  linarith [hsum]

private theorem encodeCardsAt_maxVar_le (C : BinaryCC) (startA startB n : Nat)
    (hcards : encodable.size C.cards ≤ n) (hstartA : startA ≤ startB) :
    formula_maxVar (encodeCardsAt C startA startB) ≤ startB + n := by
  unfold encodeCardsAt
  apply listOr_maxVar_le
  intro f hf; rcases List.mem_map.mp hf with ⟨c, hc, rfl⟩
  simp only [encodeCardAt, formula_maxVar, Nat.max_le]
  have hcprem : c.prem.length ≤ n :=
    le_trans (list_length_le_size _)
      (le_trans (by simp [encodable.size]; omega) (le_trans (list_elem_size_le hc) hcards))
  have hcconc : c.conc.length ≤ n :=
    le_trans (list_length_le_size _)
      (le_trans (by simp [encodable.size]; omega) (le_trans (list_elem_size_le hc) hcards))
  exact ⟨by linarith [encodeBitsAt_maxVar_le startA c.prem],
         by linarith [encodeBitsAt_maxVar_le startB c.conc]⟩

/-- The tableau formula has encodable.size bounded by 500 * n^6 + 500. -/
private theorem encodeTableau_enc_size_le (C : BinaryCC) (n : Nat) (hn : encodable.size C ≤ n) :
    encodable.size (encodeTableau C) ≤ 500 * n ^ 6 + 500 := by
  have hSizeEq : C.offset + C.width + encodable.size C.init + encodable.size C.cards +
      encodable.size C.final + C.steps + 1 = encodable.size C := by rfl
  have hn1 : 1 ≤ n := by omega
  have hoffset : C.offset ≤ n := by omega
  have hwidth : C.width ≤ n := by omega
  have hsteps : C.steps ≤ n := by omega
  have hinit : encodable.size C.init ≤ n := by omega
  have hcards : encodable.size C.cards ≤ n := by omega
  have hfinal : encodable.size C.final ≤ n := by omega
  have hinitLen : C.init.length ≤ n := le_trans (list_length_le_size _) hinit
  have hcardsLen : C.cards.length ≤ n := le_trans (list_length_le_size _) hcards
  have hfinalLen : C.final.length ≤ n := le_trans (list_length_le_size _) hfinal
  -- (A) formula_size of each encodeStepConstraint ≤ 6n²+6n+2
  have hStepFsize : ∀ line step,
      formula_size (encodeStepConstraint C line step) ≤ 6 * n ^ 2 + 6 * n + 2 := by
    intro line step; unfold encodeStepConstraint
    split_ifs with h
    · have hcs := encodeCardsAt_fsize_le C (line * C.init.length + step * C.offset)
            ((line + 1) * C.init.length + step * C.offset) n hcards
      have hmul : C.cards.length * (6 * n + 5) ≤ n * (6 * n + 5) :=
        Nat.mul_le_mul_right _ hcardsLen
      nlinarith [hcs]
    · simp [formula_size]
  -- (B) formula_size of each encodeLineConstraints ≤ 7n³+15n²+10n+3
  have hLineFsize : ∀ line,
      formula_size (encodeLineConstraints C line) ≤ 7 * n ^ 3 + 15 * n ^ 2 + 10 * n + 3 := by
    intro line; unfold encodeLineConstraints; rw [listAnd_fsize]
    have hbound : ∀ f ∈ (List.range (C.init.length + 1)).map (encodeStepConstraint C line),
        formula_size f ≤ 6 * n ^ 2 + 6 * n + 2 := by
      intro f hf; rcases List.mem_map.mp hf with ⟨step, _, rfl⟩; exact hStepFsize line step
    have hsum := list_sum_fsize_le hbound
    simp only [List.length_map, List.length_range] at hsum ⊢
    nlinarith [hsum, Nat.one_le_pow 2 n hn1, Nat.one_le_pow 3 n hn1]
  -- (C) formula_size of encodeAllStepConstraints ≤ 8n⁴+15n³+10n²+4n+1
  have hAllStepFsize : formula_size (encodeAllStepConstraints C) ≤ 8 * n ^ 4 + 15 * n ^ 3 + 10 * n ^ 2 + 4 * n + 1 := by
    unfold encodeAllStepConstraints; rw [listAnd_fsize]
    have hbound : ∀ f ∈ (List.range C.steps).map (encodeLineConstraints C),
        formula_size f ≤ 7 * n ^ 3 + 15 * n ^ 2 + 10 * n + 3 := by
      intro f hf; rcases List.mem_map.mp hf with ⟨line, _, rfl⟩; exact hLineFsize line
    have hsum := list_sum_fsize_le hbound
    simp only [List.length_map, List.length_range] at hsum ⊢
    nlinarith [hsum, Nat.one_le_pow 3 n hn1, Nat.one_le_pow 4 n hn1]
  -- (D) formula_size of each encodeFinalAtStep ≤ 3n+2
  have hFinalAtFsize : ∀ step (bits : List Bool), bits.length ≤ n →
      formula_size (encodeFinalAtStep C step bits) ≤ 3 * n + 2 := by
    intro step bits hbits; unfold encodeFinalAtStep
    split_ifs with h
    · exact le_trans (encodeBitsAt_fsize_le _ bits) (by omega)
    · simp [falseFml, formula_size]
  -- (E) formula_size of each encodeFinalString ≤ 4n²+6n+5
  have hFinalStringFsize : ∀ (bits : List Bool), bits.length ≤ n →
      formula_size (encodeFinalString C bits) ≤ 4 * n ^ 2 + 6 * n + 5 := by
    intro bits hbits; unfold encodeFinalString; rw [listOr_fsize]
    have hbound : ∀ f ∈ (List.range (C.init.length + 1)).map (fun step => encodeFinalAtStep C step bits),
        formula_size f ≤ 3 * n + 2 := by
      intro f hf; rcases List.mem_map.mp hf with ⟨step, _, rfl⟩; exact hFinalAtFsize step bits hbits
    have hsum := list_sum_fsize_le hbound
    simp only [List.length_map, List.length_range] at hsum ⊢
    nlinarith [hsum, hinitLen, Nat.one_le_pow 2 n hn1]
  -- (F) formula_size of encodeFinalConstraint ≤ 5n³+6n²+6n+2
  have hFinalFsize : formula_size (encodeFinalConstraint C) ≤ 5 * n ^ 3 + 6 * n ^ 2 + 6 * n + 2 := by
    unfold encodeFinalConstraint; rw [listOr_fsize]
    have hbound : ∀ f ∈ C.final.map (encodeFinalString C), formula_size f ≤ 4 * n ^ 2 + 6 * n + 5 := by
      intro f hf; rcases List.mem_map.mp hf with ⟨bits, hbits, rfl⟩
      apply hFinalStringFsize
      exact le_trans (list_length_le_size bits) (le_trans (list_elem_size_le hbits) hfinal)
    have hsum := list_sum_fsize_le hbound
    simp only [List.length_map] at hsum ⊢
    nlinarith [hsum, Nat.one_le_pow 2 n hn1, Nat.one_le_pow 3 n hn1]
  -- (G) formula_size of encodeTableau ≤ 9n⁴+22n³+17n²+14n+7
  have hTableauFsize : formula_size (encodeTableau C) ≤ 9 * n ^ 4 + 22 * n ^ 3 + 17 * n ^ 2 + 14 * n + 7 := by
    unfold encodeTableau; simp only [formula_size]
    nlinarith [encodeBitsAt_fsize_le 0 C.init, hinitLen, hAllStepFsize, hFinalFsize,
               Nat.zero_le (n^4), Nat.zero_le (n^3), Nat.zero_le (n^2)]
  -- (H) formula_maxVar of encodeStepConstraint ≤ 2n²+2n (for line ≤ n, step ≤ n)
  have hStepMaxVar : ∀ line step, line ≤ n → step ≤ n →
      formula_maxVar (encodeStepConstraint C line step) ≤ 2 * n ^ 2 + 2 * n := by
    intro line step hline hstep; unfold encodeStepConstraint
    split_ifs with h
    · have hstartA : line * C.init.length + step * C.offset ≤
          (line + 1) * C.init.length + step * C.offset :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
      have hstartB : (line + 1) * C.init.length + step * C.offset ≤ 2 * n ^ 2 + n := by
        have h1 : (line + 1) * C.init.length ≤ n ^ 2 + n :=
          calc (line + 1) * C.init.length
              ≤ (n + 1) * n := Nat.mul_le_mul (Nat.succ_le_succ hline) hinitLen
            _ = n ^ 2 + n := by ring
        have h2 : step * C.offset ≤ n ^ 2 :=
          calc step * C.offset
              ≤ n * n := Nat.mul_le_mul hstep hoffset
            _ = n ^ 2 := by ring
        linarith
      have hmv := encodeCardsAt_maxVar_le C
          (line * C.init.length + step * C.offset)
          ((line + 1) * C.init.length + step * C.offset)
          n hcards hstartA
      linarith [hmv]
    · simp [formula_maxVar]
  -- (I) formula_maxVar of encodeLineConstraints ≤ 2n²+2n (for line ≤ n)
  have hLineMaxVar : ∀ line, line ≤ n →
      formula_maxVar (encodeLineConstraints C line) ≤ 2 * n ^ 2 + 2 * n := by
    intro line hline; unfold encodeLineConstraints
    apply listAnd_maxVar_le
    intro f hf; rcases List.mem_map.mp hf with ⟨step, hstep_mem, rfl⟩
    apply hStepMaxVar line step hline
    have := List.mem_range.mp hstep_mem; omega
  -- (J) formula_maxVar of encodeAllStepConstraints ≤ 2n²+2n
  have hAllStepMaxVar : formula_maxVar (encodeAllStepConstraints C) ≤ 2 * n ^ 2 + 2 * n := by
    unfold encodeAllStepConstraints
    apply listAnd_maxVar_le
    intro f hf; rcases List.mem_map.mp hf with ⟨line, hline_mem, rfl⟩
    apply hLineMaxVar line
    have := List.mem_range.mp hline_mem; omega
  -- (K) formula_maxVar of encodeFinalAtStep ≤ 2n²+n (for step ≤ n, bits.length ≤ n)
  have hFinalAtMaxVar : ∀ step (bits : List Bool), step ≤ n → bits.length ≤ n →
      formula_maxVar (encodeFinalAtStep C step bits) ≤ 2 * n ^ 2 + n := by
    intro step bits hstep hbits; unfold encodeFinalAtStep
    split_ifs with h
    · apply le_trans (encodeBitsAt_maxVar_le _ bits)
      have h1 : C.steps * C.init.length ≤ n ^ 2 :=
        calc C.steps * C.init.length
            ≤ n * n := Nat.mul_le_mul hsteps hinitLen
          _ = n ^ 2 := by ring
      have h2 : step * C.offset ≤ n ^ 2 :=
        calc step * C.offset
            ≤ n * n := Nat.mul_le_mul hstep hoffset
          _ = n ^ 2 := by ring
      linarith
    · simp [falseFml, formula_maxVar]
  -- (L) formula_maxVar of encodeFinalString ≤ 2n²+n
  have hFinalStringMaxVar : ∀ (bits : List Bool), bits.length ≤ n →
      formula_maxVar (encodeFinalString C bits) ≤ 2 * n ^ 2 + n := by
    intro bits hbits; unfold encodeFinalString
    apply listOr_maxVar_le
    intro f hf; rcases List.mem_map.mp hf with ⟨step, hstep_mem, rfl⟩
    apply hFinalAtMaxVar step bits _ hbits
    have := List.mem_range.mp hstep_mem; omega
  -- (M) formula_maxVar of encodeFinalConstraint ≤ 2n²+n
  have hFinalMaxVar : formula_maxVar (encodeFinalConstraint C) ≤ 2 * n ^ 2 + n := by
    unfold encodeFinalConstraint
    apply listOr_maxVar_le
    intro f hf; rcases List.mem_map.mp hf with ⟨bits, hbits, rfl⟩
    apply hFinalStringMaxVar
    exact le_trans (list_length_le_size bits) (le_trans (list_elem_size_le hbits) hfinal)
  -- (N) formula_maxVar of encodeTableau ≤ 2n²+2n
  have hTableauMaxVar : formula_maxVar (encodeTableau C) ≤ 2 * n ^ 2 + 2 * n := by
    unfold encodeTableau; simp only [formula_maxVar]
    simp only [Nat.max_le]
    exact ⟨by linarith [encodeBitsAt_maxVar_le 0 C.init], hAllStepMaxVar,
           by linarith [hFinalMaxVar]⟩
  -- (O) Combine: encodable.size ≤ formula_size * (maxVar + 2) ≤ polynomial
  calc encodable.size (encodeTableau C)
      ≤ formula_size (encodeTableau C) * (formula_maxVar (encodeTableau C) + 2) :=
          enc_le_fsize_maxvar _
    _ ≤ (9 * n ^ 4 + 22 * n ^ 3 + 17 * n ^ 2 + 14 * n + 7) * (2 * n ^ 2 + 2 * n + 2) := by
          apply Nat.mul_le_mul hTableauFsize (by omega)
    _ ≤ 500 * n ^ 6 + 500 := by
          have h_pos : 0 < n := hn1
          have h43 : n ^ 3 ≤ n ^ 4 := Nat.pow_le_pow_right h_pos (by norm_num)
          have h42 : n ^ 2 ≤ n ^ 4 := Nat.pow_le_pow_right h_pos (by norm_num)
          have h41 : n ≤ n ^ 4 := by
            have := Nat.pow_le_pow_right h_pos (show 1 ≤ 4 from by norm_num)
            simpa [pow_one] using this
          have h40 : 1 ≤ n ^ 4 := Nat.one_le_pow 4 n hn1
          have h21 : n ≤ n ^ 2 := by
            have := Nat.pow_le_pow_right h_pos (show 1 ≤ 2 from by norm_num)
            simpa [pow_one] using this
          have h20 : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n hn1
          calc (9 * n ^ 4 + 22 * n ^ 3 + 17 * n ^ 2 + 14 * n + 7) * (2 * n ^ 2 + 2 * n + 2)
              ≤ 70 * n ^ 4 * (6 * n ^ 2) :=
                  Nat.mul_le_mul (by linarith) (by linarith)
            _ = 420 * n ^ 6 := by ring
            _ ≤ 500 * n ^ 6 + 500 := by linarith [Nat.one_le_pow 6 n hn1]

/-- The size of BinaryCC_to_FSAT_instance C is bounded by 500 * n^6 + 500. -/
theorem BinaryCC_to_FSAT_instance_size_bound (C : BinaryCC) :
    encodable.size (BinaryCC_to_FSAT_instance C) ≤ 500 * encodable.size C ^ 6 + 500 := by
  unfold BinaryCC_to_FSAT_instance
  split_ifs with hWf
  · exact encodeTableau_enc_size_le C _ le_rfl
  · -- falseFml has encodable.size = 2
    have hn : 1 ≤ encodable.size C := by simp [encodable.size]
    simp only [falseFml, encodable_size_formula_fneg, encodable_size_formula_ftrue]
    nlinarith [Nat.one_le_pow 6 (encodable.size C) hn]

end BinaryCCToFSAT

open BinaryCCToFSAT

theorem falseFml_unsat : ¬ FSAT falseFml := by
  rintro ⟨a, h⟩
  simp [satisfiesFormula, evalFormula] at h

theorem BinaryCC_to_FSAT_poly : BinaryCCLang ⪯p FSAT := by
  refine ⟨⟨BinaryCC_to_FSAT_instance, ?_, ?_⟩⟩
  · -- Polynomial-time computability witness
    refine ⟨⟨fun n => 500 * n ^ 6 + 500, ?_, ?_, ?_⟩⟩
    · -- inOPoly: 500 * n^6 + 500 ≤ 1000 * n^6 for n ≥ 1
      -- degree 6: n^4 (formula_size) * n^2 (maxVar); constant 1000 because 1000 * 1^6 = 1000 ≥ 1000 = 500 + 500
      refine ⟨6, ⟨1000, 1, ?_⟩⟩
      intro n hn
      have hn6 : 1 ≤ n ^ 6 := Nat.one_le_pow 6 n (by omega)
      linarith [Nat.mul_le_mul_left 500 hn6]
    · -- Monotonicity
      intro x x' hxx'
      have hpow : x ^ 6 ≤ x' ^ 6 := Nat.pow_le_pow_left hxx' 6
      linarith
    · -- Bound valid
      intro C
      exact BinaryCC_to_FSAT_instance_size_bound C
  · intro C
    simpa using BinaryCC_to_FSAT_instance_correct C
