import Complexity.Complexity.NP
import Complexity.CanEnumTerm
import Complexity.NP.GenNP

set_option autoImplicit false

open Classical

theorem hasDeciderClassical {X : Type} (P : X → Prop) (timeBound : Nat → Nat) : HasDecider X P timeBound := by
  classical
  refine ⟨fun x => if P x then true else false, ?_⟩
  intro x
  by_cases h : P x
  · simp [h]
  · simp [h]

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
  let certBound := genNPCertBound R hCorrect (encodable.size x)
  let steps := genNPTimeBound R hPoly (encodable.size x + certBound)
  { rel := genNPRel enumTerm (genNPCertBound R hCorrect) R x
    rel_poly := by
      refine ⟨fun _ => steps, hasDeciderClassical _ _, inOPoly_const _, ?_⟩
      intro a b hab
      simp [steps]
    maxSize := certBound + 2
    steps := steps
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
  let hWitness := Classical.choice hCorrect
  have hsound : ∀ ⦃x y⦄, R x y → Q x := hWitness.sound
  have hcomplete : ∀ ⦃x⦄, Q x → ∃ y, R x y ∧ encodable.size y ≤ hWitness.bound (encodable.size x) :=
    hWitness.complete
  constructor
  · rintro ⟨cert, _, witness, hwitness, hR, hbound⟩
    exact hsound hR
  · intro hx
    rcases hcomplete hx with ⟨witness, hR, hbound⟩
    refine ⟨enumTerm.encode witness, ?_, witness, rfl, hR, ?_⟩
    · calc
        encodable.size (enumTerm.encode witness) ≤ encodable.size witness + 2 :=
          enumTerm.encode_size_bound witness
        _ ≤ hWitness.bound (encodable.size x) + 2 := Nat.add_le_add_right hbound 2
    · simpa [genNPCertBound, hWitness]

theorem NPhard_GenNP (X__cert : Type) [encodable X__cert]
    (enumTerm : CanEnumTerm X__cert) : NPhard (GenNP X__cert) := by
  intro X hEncX Q hQ
  rcases hQ with ⟨Y, hEncY, ⟨⟨R, hPoly, hCorrect⟩⟩⟩
  refine ⟨⟨genNPInstance enumTerm R hCorrect hPoly, ?_, ?_⟩⟩
  · refine ⟨⟨fun _ => 0, inOPoly_const 0, ?_, ?_⟩⟩
    · intro a b hab
      simp
    · intro x
      simp [encodable.size]
  · intro x
    simpa using (genNPInstance_spec enumTerm R hCorrect hPoly x).symm
