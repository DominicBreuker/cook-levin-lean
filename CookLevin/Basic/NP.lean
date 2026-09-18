import CookLevin.Basic.Definitions

set_option autoImplicit false

/-! # Certificate relations

A relation `R : X → Y → Prop` is a polynomially bounded certificate relation for a
predicate `P` when every `y` with `R x y` certifies `P x` (soundness) and every `x` with
`P x` has such a certificate of size polynomial in the size of `x` (completeness). -/

/-- `R` is a sound and complete certificate relation for `P`, with certificates of
polynomially bounded size. -/
structure PolyCertRelWitness {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (R : X → Y → Prop) where
  /-- The certificate size bound. -/
  bound : Nat → Nat
  /-- Certificates only exist for positive instances. -/
  sound : ∀ ⦃x y⦄, R x y → P x
  /-- Every positive instance has a certificate of bounded size. -/
  complete : ∀ ⦃x⦄, P x → ∃ y, R x y ∧ encodable.size y ≤ bound (encodable.size x)
  bound_poly : inOPoly bound
  bound_mono : monotonic bound

/-- `R` is a polynomially bounded certificate relation for `P`. -/
abbrev polyCertRel {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (R : X → Y → Prop) : Prop :=
  Nonempty (PolyCertRelWitness P R)
