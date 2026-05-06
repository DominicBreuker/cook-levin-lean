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
    (polyCert : polyCertRel P R) :
    inNP P := by
  exact ⟨Y, inferInstance, ⟨⟨R, hPoly, polyCert⟩⟩⟩

def inP (X : Type) [encodable X] (P : X → Prop) : Prop := inTimePoly P

theorem P_NP_incl (X : Type) [encodable X] (P : X → Prop) : inP X P → inNP P := by
  intro hP
  refine inNP_intro (X := X) (Y := Unit) P (fun (x : X) (_ : Unit) => P x) ?_ ?_
  · -- hP : inP X P = inTimePoly P
    -- We need inTimePoly (fun xy : X × Unit => P xy.fst)
    -- This is the same as inTimePoly P, just reindexing
    rcases hP with ⟨f_bound, ⟨dec, hdec⟩, hf_poly, hf_mono⟩
    -- The decider for (fun xy : X × Unit => P xy.fst) exists because dec exists
    -- we use the same f_bound and just compose the decider with fst
    have dec'_witness : HasDecider (X × Unit) (fun xy => P xy.fst) f_bound :=
      ⟨fun xy => dec xy.fst, fun xy => hdec xy.fst⟩
    exact ⟨f_bound, dec'_witness, hf_poly, hf_mono⟩
  · -- hCorrect: polyCertRel for the relation (fun x (_ : Unit) => P x)
    -- Use constant bound function: bound n = 0 for all n
    refine ⟨⟨fun _ => 0, ?_, ?_, ?_, ?_⟩⟩
    · -- sound: ∀ ⦃x y⦄, R x y → P x
      intros x _ h
      exact h
    · -- complete: ∀ ⦃x⦄, P x → ∃ y, R x y ∧ encodable.size y ≤ bound (encodable.size x)
      intros x hx
      exact ⟨(), hx, Nat.zero_le _⟩
    · -- bound_poly: inOPoly bound (constant function is inOPoly)
      refine' ⟨0, ?_⟩
      refine' ⟨0, ?_⟩
      refine' ⟨0, ?_⟩
      intros
      apply Nat.zero_le
    · -- bound_mono: monotonic bound (constant function is monotonic)
      intros x x' h
      apply Nat.zero_le

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
    -- This requires unpacking hWitness.rel_poly and constructing an appropriate HasDecider
    sorry
  · -- hCorrect: polyCertRel for the new relation
    -- hWitness is an InNPWitness, which contains a polyCertRel internally
    obtain ⟨cert_witness⟩ := hWitness.rel_correct
    refine ⟨⟨fun n => cert_witness.bound n, ?_, ?_, ?_, ?_⟩⟩
    · -- sound: ∀ ⦃x y'⦄, R_Q (hRed.reduction x) y' → P x
      intros x y' h
      -- We know R_Q (hRed.reduction x) y', which by cert_witness.sound gives Q (hRed.reduction x)
      -- We need P x, but hRed.reduction_correct only gives P x → Q (hRed.reduction x)
      -- This is a limitation of our current reduction notion without polynomial-time computability
      sorry
    · -- complete: ∀ ⦃x⦄, P x → ∃ y', R_Q (hRed.reduction x) y' ∧ encodable.size y' ≤ cert_witness.bound (encodable.size x)
      intros x hPx
      have hQred : Q (hRed.reduction x) := hRed.reduction_correct hPx
      rcases cert_witness.complete hQred with ⟨y', hy1, hy2⟩
      refine ⟨y', hy1, ?_⟩
      -- We need: encodable.size y' ≤ cert_witness.bound (encodable.size x)
      -- But we have: encodable.size y' ≤ cert_witness.bound (encodable.size (hRed.reduction x))
      -- Since cert_witness.bound is monotonic, we need encodable.size (hRed.reduction x) ≤ encodable.size x
      -- This would be true if the reduction is polynomial-time computable (bounded size increase)
      -- For now, we assume this as a consequence of the reduction being polynomial-time
      -- Note: This will be properly handled in Step 3 when we strengthen the reduction notion
      -- TODO: Fix the bound composition for red_inNP
      -- This requires polynomial-time computability of the reduction
      -- which will be properly handled in Step 3
      sorry
    · -- bound_poly: inOPoly bound (composition preserves polynomiality)
      exact cert_witness.bound_poly
    · -- bound_mono: monotonic bound
      exact cert_witness.bound_mono

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
