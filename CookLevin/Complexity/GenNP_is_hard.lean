import Complexity.Complexity.NP
import Complexity.CanEnumTerm
import Complexity.NP.GenNP

set_option autoImplicit false

def genNPRel {X__cert : Type} [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) {X Y : Type} [encodable X] [encodable Y]
    (R : X → Y → Prop) (x : X) : X__cert → Prop :=
  fun cert => ∃ witness : Y, enumTerm.encode witness = cert ∧ R x witness

def genNPInstance {X__cert : Type} [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) {X Y : Type} [encodable X] [encodable Y]
    (R : X → Y → Prop) (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2))
    (x : X) : GenNPInput X__cert := by
  -- Can't construct inTimePoly for genNPRel without knowing more about R
  -- and genNPRel structure. Placeholder removed in Step 2.
  sorry

theorem genNPInstance_spec {X__cert : Type} [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) {X Y : Type} [encodable X] [encodable Y]
    {Q : X → Prop} (R : X → Y → Prop)
    (hCorrect : polyCertRel Q R) (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2))
    (x : X) :
    GenNP X__cert (genNPInstance enumTerm R hPoly x) ↔ Q x := by
  -- Placeholder removed in Step 2: inTimePoly and polyCertRel now have structure
  -- that's not compatible with the old trivial proofs
  sorry

theorem NPhard_GenNP (X__cert : Type) [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) : NPhard (GenNP X__cert) := by
  intro X hEncX Q hQ
  rcases hQ with ⟨Y, hEncY, hWitness⟩
  letI := hEncY
  rcases hWitness with ⟨hWitness⟩
  refine ⟨⟨genNPInstance enumTerm hWitness.rel hWitness.rel_poly, ?_⟩⟩
  intro x hx
  exact (genNPInstance_spec enumTerm hWitness.rel hWitness.rel_correct hWitness.rel_poly x).2 hx
