import CookLevin.Lang.ToMachine

set_option autoImplicit false

/-! # NP via verifier programs, NP-hardness, NP-completeness

`NPWitness Q` (`Lang/PolyTime.lean`) presents a language `Q` by a verifier program: a
program of the register language deciding a certificate relation `rel` for `Q` within a
polynomial cost bound, together with the layout `encX` in which it expects its input.
`NPWitnessStr` fixes that layout to the canonical one, `certState x`, so that the verifier
must read the raw bit string `x` and nothing else.

`inNPCmd Q` says that such a witness exists. This is the hypothesis of the hardness half of
the main theorem. Every language in `inNPCmd` is in `inNP` (`Basic/StringTM.lean`), the
class defined with Turing-machine verifiers: `inNPCmd_inNP` compiles the verifier program.
-/

namespace CookLevin.Lang

open CookLevin

/-- An NP witness for a string language whose verifier reads its input in the canonical
one-register layout `certState`. -/
structure NPWitnessStr (Q : List Bool → Prop) extends NPWitness Q where
  /-- The input layout is the raw string, one cell per bit, in one register. -/
  encX_canonical : ∀ x, encX x = certState x

/-- `Q` has a polynomial-cost verifier program reading the raw input string. -/
def inNPCmd (Q : List Bool → Prop) : Prop := Nonempty (NPWitnessStr Q)

/-- `P` is NP-hard: every language with a polynomial-cost verifier program reduces to `P`
in polynomial time (`⪯p`, `Basic/StringTM.lean`). -/
def NPhard (P : List Bool → Prop) : Prop := ∀ Q : List Bool → Prop, inNPCmd Q → Q ⪯p P

/-- `P` is NP-complete: NP-hard, and itself presented by a polynomial-cost verifier
program. -/
def NPcomplete (P : List Bool → Prop) : Prop := NPhard P ∧ inNPCmd P

/-- The canonical layout of `x` has `x.length` cells. -/
theorem State.size_certState (x : List Bool) : State.size (certState x) = x.length := by
  show (x.map (fun b => if b then 1 else 0)).length + 0 = x.length
  rw [List.length_map, Nat.add_zero]

/-- **Verifier programs are Turing-machine verifiers.** A language with a polynomial-cost
verifier program is in NP: the program compiles to a polynomial-time single-tape Turing
machine deciding the same certificate relation. -/
theorem inNPCmd_inNP {Q : List Bool → Prop} (h : inNPCmd Q) : inNP Q := by
  obtain ⟨W⟩ := h
  obtain ⟨t, M, acc, rej, ht, hM, h1, hdec⟩ :=
    W.verifier.toMachine W.dBound_poly W.dBound_mono
      (fun x c => by rw [W.encodeIn_eq, W.encX_canonical])
  obtain ⟨B⟩ := W.rel_correct
  refine ⟨W.rel, fun n => B.bound (2 * n), t, M, acc, rej,
    inOPoly_comp (inOPoly_mul (inOPoly_const 2) inOPoly_id) B.bound_poly,
    ht, hM, h1, ?_, hdec⟩
  intro x
  constructor
  · intro hx
    obtain ⟨c, hc, hsize⟩ := B.complete hx
    refine ⟨c, ?_, hc⟩
    calc c.length ≤ encodable.size c := length_le_size c
      _ ≤ B.bound (encodable.size x) := hsize
      _ ≤ B.bound (2 * x.length) := B.bound_mono _ _ (size_le_two_mul_length x)
  · rintro ⟨c, -, hc⟩
    exact B.sound hc

end CookLevin.Lang
