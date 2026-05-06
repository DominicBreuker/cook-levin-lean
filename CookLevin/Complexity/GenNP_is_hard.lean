import Complexity.Complexity.NP
import Complexity.CanEnumTerm
import Complexity.NP.GenNP

set_option autoImplicit false

open Classical

def genNPRel {X__cert : Type} [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) {X Y : Type} [encodable X] [encodable Y]
    (bound : Nat → Nat) (R : X → Y → Prop) (x : X) : X__cert → Prop :=
  fun cert =>
    ∃ witness : Y,
      enumTerm.encode witness = cert ∧
      R x witness ∧
      encodable.size witness ≤ bound (encodable.size x)

noncomputable def genNPTimeBound {X Y : Type} [encodable X] [encodable Y]
    (R : X → Y → Prop) (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2)) :
    Nat → Nat :=
  Classical.choose hPoly

noncomputable def genNPCertBound {X Y : Type} [encodable X] [encodable Y]
    {Q : X → Prop} (R : X → Y → Prop) (hCorrect : polyCertRel Q R) :
    Nat → Nat :=
  (Classical.choice hCorrect).bound

noncomputable def genNPInstance {X__cert : Type} [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) {X Y : Type} [encodable X] [encodable Y]
    {Q : X → Prop} (R : X → Y → Prop)
    (hCorrect : polyCertRel Q R)
    (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2))
    (x : X) : GenNPInput X__cert :=
  { rel := genNPRel enumTerm (genNPCertBound R hCorrect) R x
    rel_poly := by sorry
    maxSize := genNPCertBound R hCorrect (encodable.size x) + 2
    steps := genNPTimeBound R hPoly (encodable.size x + genNPCertBound R hCorrect (encodable.size x))
    rel_size := by
      intro cert hrel
      rcases hrel with ⟨witness, hwitness, _, hwitnessBound⟩
      calc
        encodable.size cert = encodable.size (enumTerm.encode witness) := by simpa [hwitness]
        _ ≤ encodable.size witness + 2 := enumTerm.encode_size_bound witness
        _ ≤ genNPCertBound R hCorrect (encodable.size x) + 2 := Nat.add_le_add_right hwitnessBound 2 }

theorem genNPInstance_spec {X__cert : Type} [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) {X Y : Type} [encodable X] [encodable Y]
    {Q : X → Prop} (R : X → Y → Prop)
    (hCorrect : polyCertRel Q R) (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2))
    (x : X) :
    GenNP X__cert (genNPInstance enumTerm R hCorrect hPoly x) ↔ Q x := by
  sorry

theorem NPhard_GenNP (X__cert : Type) [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) : NPhard (GenNP X__cert) := by
  sorry
