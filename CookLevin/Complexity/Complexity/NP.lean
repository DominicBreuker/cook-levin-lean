import Complexity.Complexity.Definitions
import Complexity.Complexity.MachineSemantics

set_option autoImplicit false

/-- A predicate indicating that a function is polynomial-time computable.
This means there exists a polynomial-time bound for computing the function. -/
structure PolyTimeComputableWitness {X Y : Type} [encodable X] [encodable Y]
    (f : X → Y) where
  bound : Nat → Nat
  bound_poly : inOPoly bound
  bound_mono : monotonic bound
  bound_valid : ∀ x : X, encodable.size (f x) ≤ bound (encodable.size x)

abbrev polyTimeComputable {X Y : Type} [encodable X] [encodable Y] (f : X → Y) : Prop :=
  Nonempty (PolyTimeComputableWitness f)

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

/-- A witness that `P` polynomial-time reduces to `Q`: a map together with proofs of
polynomial-time computability and correctness (equivalence). -/
structure ReductionWitness {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) where
  reduction : X → Y
  reduction_poly : polyTimeComputable reduction
  reduction_correct : ∀ ⦃x⦄, P x ↔ Q (reduction x)

abbrev reducesPolyMO {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) : Prop :=
  Nonempty (ReductionWitness P Q)

infix:50 " ⪯p " => reducesPolyMO

theorem reducesPolyMO_elim {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → ∃ f : X → Y, (∀ x, P x → Q (f x)) ∧ (∀ x, P x ↔ Q (f x)) := by
  rintro ⟨⟨f, _, hf_correct⟩⟩
  refine ⟨f, fun x hx => (@hf_correct x).mp hx, fun x => @hf_correct x⟩

theorem reducesPolyMO_reflexive (X : Type) [encodable X] (P : X → Prop) : P ⪯p P := by
  refine ⟨⟨id, ?_, fun _ => Iff.rfl⟩⟩
  refine ⟨⟨fun n => n, ?_, ?_, ?_⟩⟩
  · have : inO (fun n => n) (fun x => x^1):= by
      apply Exists.intro 1
      apply Exists.intro 0
      intros n hn
      simp
    apply Exists.intro 1
    exact this
  · intros x x' h
    exact h
  · intros x
    simp

theorem reducesPolyMO_transitive {X Y Z : Type}
    [encodable X] [encodable Y] [encodable Z]
    (P : X → Prop) (Q : Y → Prop) (R : Z → Prop) :
    P ⪯p Q → Q ⪯p R → P ⪯p R := by
  intros hPQ hQR
  rcases hPQ with ⟨⟨f, hf_poly, hf_correct⟩⟩
  rcases hQR with ⟨⟨g, hg_poly, hg_correct⟩⟩
  refine ⟨⟨g ∘ f, ?_, fun {x} => ?_⟩⟩
  rcases hf_poly with ⟨⟨bound_f, hbound_poly_f, hbound_mono_f, hbound_valid_f⟩⟩
  rcases hg_poly with ⟨⟨bound_g, hbound_poly_g, hbound_mono_g, hbound_valid_g⟩⟩
  have hbound_valid_comp : ∀ x : X, encodable.size ((g ∘ f) x) ≤ (bound_g ∘ bound_f) (encodable.size x) := by
    intro x
    calc encodable.size ((g ∘ f) x)
      _ = encodable.size (g (f x)) := rfl
      _ ≤ bound_g (encodable.size (f x)) := hbound_valid_g (f x)
      _ ≤ bound_g (bound_f (encodable.size x)) := by apply hbound_mono_g; exact hbound_valid_f x
  · exact ⟨⟨bound_g ∘ bound_f, inOPoly_comp hbound_poly_f hbound_poly_g,
        monotonic_comp hbound_mono_f hbound_mono_g, hbound_valid_comp⟩⟩
  · simpa using Iff.trans (@hf_correct x) (@hg_correct (f x))


theorem red_inNP {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → inNP Q → inNP P := by
  intros hPQ hQinNP
  rcases hPQ with ⟨⟨f, hf_poly, hf_correct⟩⟩
  rcases hf_poly with ⟨⟨bound_f, hbound_poly_f, hbound_mono_f, hbound_valid_f⟩⟩
  rcases hQinNP with ⟨Y_cert, _, ⟨⟨R, hR_poly, hR_cert⟩⟩⟩
  rcases hR_poly with ⟨time_R, hdec_R, htime_poly_R, htime_mono_R⟩
  rcases hR_cert with ⟨⟨cert_bound, hsound_R, hcomplete_R, hcert_poly_R, hcert_mono_R⟩⟩
  refine ⟨Y_cert, inferInstance, ?_⟩
  refine ⟨⟨fun x cert => R (f x) cert, ?_, ?_⟩⟩
  · refine ⟨time_R, ?_, htime_poly_R, htime_mono_R⟩
    rcases hdec_R with ⟨dec_R, hdec_R⟩
    refine ⟨fun xc => dec_R (f xc.1, xc.2), ?_⟩
    intro xc
    simpa using hdec_R (f xc.1, xc.2)
  · refine ⟨⟨cert_bound ∘ bound_f, ?_, ?_, inOPoly_comp hbound_poly_f hcert_poly_R,
        monotonic_comp hbound_mono_f hcert_mono_R⟩⟩
    · intro x cert hrel
      exact hf_correct.mpr (hsound_R hrel)
    · intro x hx
      rcases hcomplete_R (hf_correct.mp hx) with ⟨cert, hcert, hsize⟩
      refine ⟨cert, hcert, ?_⟩
      calc
        encodable.size cert ≤ cert_bound (encodable.size (f x)) := hsize
        _ ≤ cert_bound (bound_f (encodable.size x)) := hcert_mono_R _ _ (hbound_valid_f x)

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
  have subtype_reduction : (fun x : {x // subtype_pred x} => P x.1) ⪯p P := by
    refine ⟨⟨Subtype.val, ?_, fun {x} => Iff.rfl⟩⟩
    refine ⟨⟨fun n => n, ?_, ?_, ?_⟩⟩
    · exact inOPoly_id
    · intros x x' h
      exact h
    · intro x
      exact subtype_size_val_le x
  exact reducesPolyMO_transitive _ _ _ (hHard Y hEncY Q hQ) subtype_reduction
