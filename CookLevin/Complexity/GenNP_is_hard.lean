import Complexity.Complexity.NP
import Complexity.CanEnumTerm
import Complexity.NP.GenNP

set_option autoImplicit false

open Classical

/-- Placeholder that produces a `Nonempty (DecidesBy P timeBound)`
witness for *any* predicate `P` and *any* `timeBound`. Vacuously
true at the framework's pre-pivot definitions; documented as a
deferred gap in `ROADMAP.md` Part 7.

After the May 2026 pivot, the Part 7 replacement strategy is:
1. Take `genNPRel` and the underlying `R : X → Y → Prop` with
   `hPoly : inTimePoly (fun xy => R xy.1 xy.2)`.
2. Destructure `hPoly` to obtain a `Lang.DecidesLang` for R.
3. Compose with the certificate decoder
   `enumTerm.decode : X__cert → Option Y` (lifted to a `Lang.Cmd`)
   to obtain a `Lang.DecidesLang` for `genNPRel`.
4. Bridge to `Nonempty (DecidesBy ...)` via
   `Lang.DecidesLang.toDecidesBy`.

The current `hasDeciderClassical`'s signature is too strong — it
claims a decider for *any* predicate, not just `genNPRel`. The
Part 7 rewrite tightens the signature to the specific shape
`genNPInstance` needs, at which point the body is constructive. -/
theorem hasDeciderClassical {X : Type} [encodable X]
    (P : X → Prop) (timeBound : Nat → Nat) :
    Nonempty (DecidesBy P timeBound) := by
  -- TODO(Part7:hasDeciderClassical) — see file docstring above.
  sorry

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

theorem genNPTimeBound_poly {X Y : Type} [encodable X] [encodable Y]
    (R : X → Y → Prop) (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2)) :
    inOPoly (genNPTimeBound R hPoly) :=
  (Classical.choose_spec hPoly).2.1

theorem genNPTimeBound_mono {X Y : Type} [encodable X] [encodable Y]
    (R : X → Y → Prop) (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2)) :
    monotonic (genNPTimeBound R hPoly) :=
  (Classical.choose_spec hPoly).2.2

theorem genNPCertBound_poly {X Y : Type} [encodable X] [encodable Y]
    {Q : X → Prop} (R : X → Y → Prop) (hCorrect : polyCertRel Q R) :
    inOPoly (genNPCertBound R hCorrect) :=
  (Classical.choice hCorrect).bound_poly

theorem genNPCertBound_mono {X Y : Type} [encodable X] [encodable Y]
    {Q : X → Prop} (R : X → Y → Prop) (hCorrect : polyCertRel Q R) :
    monotonic (genNPCertBound R hCorrect) :=
  (Classical.choice hCorrect).bound_mono

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
  -- Honest output-size bound (Part 0.1): the produced instance's size is
  -- exactly its two parameters, `certBound n + 2` and
  -- `timeBound (n + certBound n)` — a polynomial in `n` because the
  -- certificate bound and the decider time bound are.
  · refine ⟨⟨fun n => genNPCertBound R hCorrect n +
        genNPTimeBound R hPoly (n + genNPCertBound R hCorrect n) + 3, ?_, ?_, ?_⟩⟩
    · have hinner : inOPoly (fun n => n + genNPCertBound R hCorrect n) :=
        inOPoly_add inOPoly_id (genNPCertBound_poly R hCorrect)
      have hcomp : inOPoly
          (fun n => genNPTimeBound R hPoly (n + genNPCertBound R hCorrect n)) :=
        inOPoly_comp hinner (genNPTimeBound_poly R hPoly)
      exact inOPoly_add (inOPoly_add (genNPCertBound_poly R hCorrect) hcomp)
        (inOPoly_const 3)
    · intro a b hab
      have hcert := genNPCertBound_mono R hCorrect a b hab
      have htime := genNPTimeBound_mono R hPoly (a + genNPCertBound R hCorrect a)
        (b + genNPCertBound R hCorrect b) (Nat.add_le_add hab hcert)
      exact Nat.add_le_add (Nat.add_le_add hcert htime) (Nat.le_refl 3)
    · intro x
      show encodable.size (genNPInstance enumTerm R hCorrect hPoly x) ≤ _
      simp [genNPInstance]
      omega
  · intro x
    simpa using (genNPInstance_spec enumTerm R hCorrect hPoly x).symm
