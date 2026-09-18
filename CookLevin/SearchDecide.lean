import CookLevin.Lang.HardnessStr

set_option autoImplicit false

/-! # Every language with a verifier program is decidable

A sanity check on the hypothesis of the hardness half of the main theorem. `inNPCmd Q`
(`Lang/HardnessStr.lean`) says that `Q` has a polynomial-cost verifier program. This file
shows that the class so defined contains no undecidable language: from a witness one can
decide `Q x` by enumerating every certificate up to the witness's own length bound and
running its verifier program on each. `searchDecide` is an executable function, and
`searchDecide_correct` proves it decides `Q`. The search is exponential
(`searchDecide_calls`); nothing here claims efficiency. -/

namespace CookLevin.SearchDecide

open CookLevin.Lang

/-- Every bit string of length at most `n`. -/
def bitStringsUpTo : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => [] :: (bitStringsUpTo n).flatMap (fun c => [false :: c, true :: c])

theorem mem_bitStringsUpTo : ∀ (n : Nat) (c : List Bool),
    c ∈ bitStringsUpTo n ↔ c.length ≤ n
  | 0, c => by
      constructor
      · intro h
        have : c = [] := by simpa [bitStringsUpTo] using h
        simp [this]
      · intro h
        have : c = [] := List.eq_nil_of_length_eq_zero (Nat.le_antisymm h (Nat.zero_le _))
        simp [bitStringsUpTo, this]
  | n + 1, c => by
      simp only [bitStringsUpTo, List.mem_cons, List.mem_flatMap]
      constructor
      · rintro (rfl | ⟨d, hd, hc⟩)
        · exact Nat.zero_le _
        · have hd' : d.length ≤ n := (mem_bitStringsUpTo n d).mp hd
          have : c = false :: d ∨ c = true :: d := by simpa using hc
          rcases this with rfl | rfl <;> simpa using Nat.succ_le_succ hd'
      · intro h
        cases c with
        | nil => exact Or.inl rfl
        | cons b t =>
            refine Or.inr ⟨t, (mem_bitStringsUpTo n t).mpr (Nat.le_of_succ_le_succ h), ?_⟩
            cases b <;> simp

theorem bitStringsUpTo_length : ∀ n : Nat, (bitStringsUpTo n).length = 2 ^ (n + 1) - 1
  | 0 => rfl
  | n + 1 => by
      have ih := bitStringsUpTo_length n
      have hpos : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      have hflat : ((bitStringsUpTo n).flatMap
          (fun c => [false :: c, true :: c])).length = 2 * (bitStringsUpTo n).length := by
        induction bitStringsUpTo n with
        | nil => simp
        | cons a t iht => simp [List.flatMap_cons] at iht ⊢; omega
      simp only [bitStringsUpTo, List.length_cons, hflat, ih]
      have : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by
        rw [Nat.pow_succ]; omega
      omega

section

variable {Q : List Bool → Prop}

/-- The verifier's input layout: the input bits in register `0`, the certificate bits in
register `1`. -/
def strLayout (x c : List Bool) : State := certState x ++ certState c

theorem encodeIn_eq_strLayout (W : NPWitnessStr Q) (x c : List Bool) :
    W.verifier.encodeIn (x, c) = strLayout x c := by
  rw [W.encodeIn_eq x c, W.encX_canonical x]; rfl

/-- Run the witness's verifier program on the pair `(x, c)`. -/
def verifierAccepts (W : NPWitnessStr Q) (x c : List Bool) : Bool :=
  (W.verifier.c.eval (strLayout x c)).isAccept

theorem verifierAccepts_iff (W : NPWitnessStr Q) (x c : List Bool) :
    W.rel x c ↔ verifierAccepts W x c = true := by
  have h := (W.verifier.decides (x, c)).1
  rw [encodeIn_eq_strLayout W x c] at h
  exact h

/-- Brute-force search: run the verifier on every certificate up to the length bound. -/
def searchDecide (W : NPWitnessStr Q) (bound : Nat → Nat) (x : List Bool) : Bool :=
  (bitStringsUpTo (bound (encodable.size x))).any (fun c => verifierAccepts W x c)

/-- **The search decides `Q`.** Hence no undecidable language has a verifier program. -/
theorem searchDecide_correct (W : NPWitnessStr Q) (R : PolyCertRelWitness Q W.rel)
    (x : List Bool) : Q x ↔ searchDecide W R.bound x = true := by
  constructor
  · intro hx
    obtain ⟨c, hrel, hsize⟩ := R.complete hx
    have hlen : c.length ≤ R.bound (encodable.size x) :=
      Nat.le_trans (length_le_size c) hsize
    refine List.any_eq_true.mpr ⟨c, (mem_bitStringsUpTo _ c).mpr hlen, ?_⟩
    exact (verifierAccepts_iff W x c).mp hrel
  · intro h
    obtain ⟨c, _, hacc⟩ := List.any_eq_true.mp h
    exact R.sound ((verifierAccepts_iff W x c).mpr hacc)

/-- The search runs the verifier exponentially often. -/
theorem searchDecide_calls (bound : Nat → Nat) (x : List Bool) :
    (bitStringsUpTo (bound (encodable.size x))).length
      = 2 ^ (bound (encodable.size x) + 1) - 1 :=
  bitStringsUpTo_length _

end

end CookLevin.SearchDecide
