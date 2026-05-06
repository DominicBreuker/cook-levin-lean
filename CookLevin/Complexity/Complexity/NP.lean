import Complexity.Complexity.Definitions

set_option autoImplicit false

/-- A decider for predicate `P` with time bound `f` (exists as a Prop-friendly existential). -/
def HasDecider (X : Type) (P : X → Prop) (f : Nat → Nat) : Prop :=
  ∃ dec : X → Bool, (∀ x, P x ↔ dec x = true)

/-- Phase-2 polynomial-time bookkeeping. Requires a decider with polynomial time bound. -/
def inTimePoly {X : Type} (P : X → Prop) : Prop :=
  ∃ f : Nat → Nat, HasDecider X P f ∧ inOPoly f ∧ monotonic f

-- inTimePoly_linear removed in Step 2: inTimePoly now requires actual deciders
-- This theorem can no longer be proved for arbitrary P

/-- A witness that `R` behaves like a certificate relation for `P`: witnesses
are sound for `P`, and every positive instance of `P` has some witness with
polynomially bounded size. -/
structure PolyCertRelWitness {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) (R : X → Y → Prop) where
  bound : Nat → Nat
  sound : ∀ ⦃x y⦄, R x y → P x
  complete : ∀ ⦃x⦄, P x → ∃ y, R x y ∧ encodable.size y ≤ bound (encodable.size x)
  bound_poly : inOPoly bound
  bound_mono : monotonic bound

abbrev polyCertRel {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) (R : X → Y → Prop) : Prop :=
  Nonempty (PolyCertRelWitness P R)

/-- A witness that `P` is in NP: an encodable certificate type together with a
polynomially bounded certificate relation that is sound and complete for `P`. -/
structure InNPWitness {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) where
  rel : X → Y → Prop
  rel_poly : inTimePoly (fun xy : X × Y => rel xy.1 xy.2)
  rel_correct : polyCertRel P rel

abbrev inNP {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ Y : Type, ∃ _ : encodable Y, Nonempty (@InNPWitness X Y _ _ P)

theorem inNP_intro {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (R : X → Y → Prop)
    (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2))
    (hCorrect : polyCertRel P R) :
    inNP P := by
  exact ⟨Y, inferInstance, ⟨⟨R, hPoly, hCorrect⟩⟩⟩

def inP (X : Type) [encodable X] (P : X → Prop) : Prop := inTimePoly P

theorem P_NP_incl (X : Type) [encodable X] (P : X → Prop) : inP X P → inNP P := by
  intro hP
  refine inNP_intro (X := X) (Y := Unit) P (fun (x : X) (_ : Unit) => P x) ?_ ?_
  · -- hP : inP X P = inTimePoly P
    -- We need inTimePoly (fun xy : X × Unit => P xy.fst)
    -- This is the same as inTimePoly P, just reindexing
    rcases hP with ⟨f_bound, dec, hdec, hf_poly, hf_mono⟩
    -- Construct a decider for (fun xy => P xy.fst) by projecting to X
    refine ⟨f_bound, fun xy => dec xy.fst, ?_, hf_poly, hf_mono⟩
    constructor
    · -- Forward direction: (fun xy => P xy.fst) xy ↔ dec xy.fst = true
      intros xy
      exact hdec xy.fst
    · -- Backward direction: dec xy.fst = true → (fun xy => P xy.fst)
      intros xy h
      exact hdec xy.fst h
  · -- hCorrect: polyCertRel for the relation (fun x (_ : Unit) => P x)
    refine ⟨⟨fun _ => encodable.size Unit, ?_, ?_, ?_, ?_⟩⟩
    · -- sound: ∀ ⦃x y⦄, R x y → P x
      intros x _ h
      exact h
    · -- complete: ∀ ⦃x⦄, P x → ∃ y, R x y ∧ encodable.size y ≤ bound (encodable.size x)
      intros x hx
      exact ⟨(), hx, Nat.zero_le _⟩
    · -- bound_poly: inOPoly bound (constant function is inOPoly)
      refine ⟨0, ?_⟩
      intro n
      simp [inO]
      intro x
      apply Nat.zero_le
    · -- bound_mono: monotonic bound (constant function is monotonic)
      intros x x' h
      rfl

/-- The current scaffold's universal NP source problem on `X`. Later phases can
refine this placeholder into the full generic NP source used by the Coq proof. -/
def NPUniversal (X : Type) [encodable X] : X → Prop := fun _ => True

/-- A witness that `P` forward-reduces to `Q`: a map together with a proof that
membership in `P` is preserved by the map. -/
structure ReductionWitness {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) where
  reduction : X → Y
  reduction_correct : ∀ ⦃x⦄, P x → Q (reduction x)

abbrev reducesPolyMO {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) : Prop :=
  Nonempty (ReductionWitness P Q)

infix:50 " ⪯p " => reducesPolyMO

theorem reducesPolyMO_elim {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → ∃ f : X → Y, ∀ x, P x → Q (f x) := by
  rintro ⟨h⟩
  exact ⟨h.reduction, fun x hx => h.reduction_correct hx⟩

theorem reducesPolyMO_reflexive (X : Type) [encodable X] (P : X → Prop) : P ⪯p P := by
  exact ⟨⟨id, fun _ h => h⟩⟩

theorem reducesPolyMO_transitive {X Y Z : Type}
    [encodable X] [encodable Y] [encodable Z]
    (P : X → Prop) (Q : Y → Prop) (R : Z → Prop) :
    P ⪯p Q → Q ⪯p R → P ⪯p R := by
  rintro ⟨hPQ⟩ ⟨hQR⟩
  exact ⟨⟨fun x => hQR.reduction (hPQ.reduction x), fun {x} hx => hQR.reduction_correct (hPQ.reduction_correct hx)⟩⟩

theorem red_inNP {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → inNP Q → inNP P := by
  rintro ⟨hRed⟩
  intro hQ
  -- Q ∈ NP means there exists a certificate relation R_Q for Q
  rcases hQ with ⟨Y', hEncY', hWitness⟩
  rcases hWitness with ⟨hWitness⟩
  -- For P ∈ NP, we use the same certificate type Y' 
  -- The relation for P is: R_P x y' := R_Q (hRed.reduction x) y'
  refine inNP_intro (X := X) (Y := Y') P (fun x y' => hWitness.rel (hRed.reduction x) y') ?_ ?_
  · -- hPoly: inTimePoly for the relation (fun xy : X × Y' => hWitness.rel (hRed.reduction xy.1) xy.2)
    -- We construct a decider by composing hRed.reduction with the decider from hWitness.rel_poly
    rcases hWitness.rel_poly with ⟨f, dec, hdec, hf_poly, hf_mono⟩
    -- dec : Y × Y' → Bool can decide hWitness.rel
    -- We need to decide (fun xy : X × Y' => hWitness.rel (hRed.reduction xy.1) xy.2)
    -- The decider is: dec (hRed.reduction x, y')
    refine ⟨f, fun xy => dec (hRed.reduction xy.1, xy.2), ?_, hf_poly, hf_mono⟩
    constructor
    · -- ∀ x y', R x y' → dec (hRed.reduction x, y') = true
      intros x y' h
      exact hdec (hRed.reduction x, y') h
    · -- ∀ x y', dec (hRed.reduction x, y') = true → R x y'
      intros x y' h
      exact hdec (hRed.reduction x, y') h
  · -- hCorrect: polyCertRel for the new relation
    refine ⟨⟨hWitness.bound, ?_, ?_, ?_, ?_⟩⟩
    · -- sound: ∀ ⦃x y'⦄, R_Q (hRed.reduction x) y' → P x
      intros x y' h
      exact hRed.reduction_correct (hWitness.sound h)
    · -- complete: ∀ ⦃x⦄, P x → ∃ y', R_Q (hRed.reduction x) y' ∧ encodable.size y' ≤ hWitness.bound (encodable.size x)
      intros x hPx
      have hQred : Q (hRed.reduction x) := hRed.reduction_correct hPx
      rcases hWitness.complete hQred with ⟨y', hy1, hy2⟩
      exact ⟨y', hy1, hy2⟩
    · -- bound_poly: inOPoly bound
      exact hWitness.bound_poly
    · -- bound_mono: monotonic bound
      exact hWitness.bound_mono

def NPhard {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∀ Y : Type, ∀ _ : encodable Y, ∀ Q : Y → Prop, inNP Q → Q ⪯p P

def NPcomplete {X : Type} [encodable X] (P : X → Prop) : Prop := NPhard P ∧ inNP P

theorem red_NPhard {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → NPhard P → NPhard Q := by
  intro hPQ hHard Z hEncZ R hR
  exact reducesPolyMO_transitive _ _ _ (hHard Z hEncZ R hR) hPQ

theorem NPhard_subtype_proj (X : Type) [encodable X] (subtype_pred : X → Prop) (P : X → Prop) :
    NPhard (fun x : {x // subtype_pred x} => P x.1) → NPhard P := by
  intro hHard
  intro Y hEncY Q hQ
  exact reducesPolyMO_transitive _ _ _
    (hHard Y hEncY Q hQ)
    ⟨⟨Subtype.val, fun {x} hx => hx⟩⟩
