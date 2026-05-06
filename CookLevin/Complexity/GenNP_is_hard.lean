import Complexity.Complexity.NP
import Complexity.CanEnumTerm
import Complexity.NP.GenNP

set_option autoImplicit false

def genNPRel {X__cert : Type} [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) {X Y : Type} [encodable X] [encodable Y]
    (R : X → Y → Prop) (x : X) : X__cert → Prop :=
  fun cert => ∃ witness : Y, enumTerm.encode witness = cert ∧ R x witness

-- Note: genNPRel_inTimePoly is not implemented in Step 5.
-- The full proof requires the CanEnumTerm infrastructure which uses
-- concrete TM encodings (lambda calculus terms in Coq).
-- This is left as sorry for now and will be completed in later steps.

def genNPInstance {X__cert : Type} [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) {X Y : Type} [encodable X] [encodable Y]
    (R : X → Y → Prop) (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2))
    (x : X) : GenNPInput X__cert := by
  refine ⟨fun cert => genNPRel enumTerm R (X := X) x cert, ?_⟩
  -- We need to construct an inTimePoly witness for the relation
  -- genNPRel x cert = ∃ y : Y, enumTerm.encode y = cert ∧ R x y
  --
  -- This is provable but requires nontrivial constructions.
  -- For Step 5, we leave this as sorry since the technical machinery
  -- needs the actual CanEnumTerm infrastructure from later per the Coq proof
  -- which depends on lambda calculus terms.
  sorry

theorem genNPInstance_spec {X__cert : Type} [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) {X Y : Type} [encodable X] [encodable Y]
    {Q : X → Prop} (R : X → Y → Prop)
    (hCorrect : polyCertRel Q R) (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2))
    (x : X) :
    GenNP X__cert (genNPInstance enumTerm R hPoly x) ↔ Q x := by
  constructor
  · -- Forward direction: GenNP ... implies Q x
    intro ⟨cert, y, hy_eq, hR⟩
    -- We have cert : X__cert, y : Y, enumTerm.encode y = cert, and R x y
    -- Extract the PolyCertRelWitness
    obtain ⟨witness⟩ := hCorrect
    -- By witness.sound, R x y → Q x
    exact witness.sound hR
  · -- Backward direction: Q x implies GenNP ...
    intro hQx
    -- Extract the PolyCertRelWitness
    obtain ⟨witness⟩ := hCorrect
    -- By witness.complete, Q x → ∃ y, R x y ∧ encodable.size y ≤ bound (encodable.size x)
    obtain ⟨y, hR, hy_bound⟩ := witness.complete hQx
    -- Use y as the witness
    refine ⟨enumTerm.encode y, y, rfl, hR⟩

theorem NPhard_GenNP (X__cert : Type) [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) : NPhard (GenNP X__cert) := by
  intro X hEncX Q hQ
  rcases hQ with ⟨Y, hEncY, hWitness⟩
  letI := hEncY
  rcases hWitness with ⟨witness⟩
  refine ⟨⟨fun x => genNPInstance enumTerm witness.rel witness.rel_poly x, trivial, ?_⟩⟩
  intro x
  exact (genNPInstance_spec enumTerm witness.rel witness.rel_correct witness.rel_poly x).symm
