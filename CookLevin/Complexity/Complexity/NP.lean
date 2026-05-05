import Complexity.Complexity.Definitions

set_option autoImplicit false

/-- Phase-2 polynomial-time bookkeeping. The predicate argument is already kept
in the interface, even though the current scaffold only records the existence
of a polynomial bound and does not yet model the underlying machine semantics. -/
def inTimePoly {X : Type} (_ : X → Prop) : Prop :=
  ∃ f : Nat → Nat, inOPoly f ∧ monotonic f

theorem inTimePoly_linear {X : Type} (P : X → Prop) : inTimePoly P := by
  refine ⟨fun n => n, ?_, ?_⟩ <;> simp [inOPoly, monotonic]

/-- A witness that `R` behaves like a certificate relation for `P`: witnesses
are sound for `P`, and every positive instance of `P` has some witness. -/
structure PolyCertRelWitness {X Y : Type} (P : X → Prop) (R : X → Y → Prop) where
  sound : ∀ ⦃x y⦄, R x y → P x
  complete : ∀ ⦃x⦄, P x → ∃ y, R x y

abbrev polyCertRel {X Y : Type} (P : X → Prop) (R : X → Y → Prop) : Prop :=
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
  · simpa using hP
  · refine ⟨⟨?_, ?_⟩⟩
    · intro x y h
      exact h
    · intro x h
      exact ⟨(), h⟩

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
  rintro ⟨hPQ⟩ ⟨Cert, hEncCert, hQ⟩
  letI := hEncCert
  rcases hQ with ⟨hQ⟩
  refine ⟨Cert, inferInstance, ?_⟩
  refine ⟨⟨fun x c => P x ∧ hQ.rel (hPQ.reduction x) c, inTimePoly_linear _, ?_⟩⟩
  refine ⟨⟨?_, ?_⟩⟩
  · intro x c h
    exact h.1
  · intro x hPx
    rcases hQ.rel_correct with ⟨hCert⟩
    rcases hCert.complete (hPQ.reduction_correct hPx) with ⟨c, hc⟩
    exact ⟨c, hPx, hc⟩

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
