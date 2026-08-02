import Complexity.Meta.AxiomGate
import Complexity.NP.SAT.CookLevin.CookLevinHonest
import Complexity.Complexity.Deciders.SATStr
import Complexity.NP.SAT.CookLevin.Reductions.SAT_to_SATStr_comp

set_option autoImplicit false

/-! # Non-vacuity of `NPhardStr` — the hypothesis is neither empty nor free

`CookLevinHonest.CookLevinStr : NPcompleteStr SAT` unfolds to

```
(∀ Q : List Bool → Prop, inNPStr Q → Q ⪯p' SAT) ∧ inNPLangFreeSplit SAT
```

and a universally quantified implication has **two** ways to mean nothing:

1. **The hypothesis class is empty.** If no `Q` at all satisfies `inNPStr Q`, the
   hardness half is vacuously true and says nothing — the classic trap for a
   statement that has been strengthened until it is safe. Every previous session
   worked on making `inNPStr` *harder* to satisfy (`InNPWitnessLangFreeSplit`'s
   layout laws, then `sizeLB`, then pinning the layout outright in
   `InNPWitnessStr`); **none checked that anything still satisfies it.** Until
   this file, the library contained no `InNPWitnessStr` at all.
2. **The hypothesis class is everything.** If `inNPStr Q` held for an arbitrary
   predicate — an undecidable one included — the produced `Q ⪯p' SAT` would be a
   real machine on a dishonest presentation and the theorem would not be about
   NP. This is the failure `probes/HonestyAuditProbe.lean` §7/§7b exhibits for
   `NPhard''`, and the reason `NPhardStr` exists (ROADMAP risk **S5**,
   standing architecture risk 6).

This file closes both, machine-checked, and is gated:

* **§1–§2 (not everything).** `inNPStr Q` forces `Q` to be **decidable** — and
  not by a classical existence argument. `searchDecide` is an explicit, running
  Lean function: it enumerates every certificate of length `≤ bound (size x)`
  and *runs the witness's own verifier `Cmd`* on the canonical layout
  `certState x ++ certState c`. `searchDecide_correct` proves
  `Q x ↔ searchDecide … x = true`, so **no undecidable predicate inhabits
  `inNPStr`**.
* **§3–§4 (not nothing).** `SquareStr x := ∃ c, x = c ++ c` comes with a
  complete `InNPWitnessStr`: a two-op verifier `Cmd` over the canonical
  two-register layout, a real cost bound, and a certificate relation whose
  certificate is *load-bearing* (the verifier reads register `1` and the answer
  changes with it). `SquareStr` separates strings (§4), so the class contains a
  language that is neither empty nor total.
* **§5 (the payoff).** `CookLevinStr` applied to that witness yields a concrete
  `SquareStr ⪯p' SAT` — the whole chain, front to tail, instantiated at a real
  problem rather than quantified over an empty class.
* **§6 (not nothing, and not easy either).** The same, at `SATStr` — SAT
  presented as a language of bit strings — so the class demonstrably contains a
  problem nobody expects to be in P.

## ⚠ What this file does NOT claim — read before extending it

`searchDecide` is a **Lean function**, not a `Cmd` and not a `FlatTM`. It shows
that the *mathematical* content of `inNPStr Q` pins `Q` down to a bounded search
over a concrete decidable machine predicate; it does **not** exhibit a Turing
machine deciding `Q` in this development's own computability model. The next
rung — `inNPStr Q → ∃ f, Nonempty (DecidesBy Q f)` with `f` exponential, by
compiling the search to a `Cmd` — is real work and is scoped in `HANDOFF.md`.

Do **not** "strengthen" §1 to `∃ f : List Bool → Bool, ∀ x, Q x ↔ f x = true`
and call it decidability: that statement is classically true for *every*
predicate and is worth exactly nothing. `inNPStr_exists_decider` states it at
the bottom of §2 with that warning attached, precisely so nobody re-derives it
and mistakes it for the result.

Likewise, `SquareStr` (§3) is in **P** — it is an inhabitant, not evidence that
the class contains hard problems. **§6 settles that**: `SATStr`
(`Complexity/Complexity/Deciders/SATStr.lean`) is SAT itself as a bit-string
language, with a complete `InNPWitnessStr`. `SquareStr` is kept as the minimal
example — two ops, every field readable at a glance.

⚠ §6 does **not** claim `NPhardStr SATStr`; that needs a reduction in the other
direction plus a seam. See `HANDOFF.md`, bottom-up item 1.
-/

namespace Complexity.NonVacuity

open Complexity.Lang

/-! ## 0 — arithmetic of `encodable.size` on bit strings

Two facts the search needs: `size` is additive over `++`, and a string's own
length never exceeds its size (`length_le_size`, already in
`Lang/HardnessStr.lean`). -/

/-- `encodable.size` on `List Bool` is additive: the instance is a `foldl` whose
step depends only on the element. -/
theorem size_append (a b : List Bool) :
    encodable.size (a ++ b) = encodable.size a + encodable.size b := by
  have shift : ∀ (l : List Bool) (acc : Nat),
      l.foldl (fun acc x => acc + encodable.size x + 1) acc
        = acc + l.foldl (fun acc x => acc + encodable.size x + 1) 0 := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons b t ih =>
        intro acc
        simp only [List.foldl_cons, Nat.zero_add]
        rw [ih (acc + encodable.size b + 1), ih (encodable.size b + 1)]
        omega
  show (a ++ b).foldl (fun acc x => acc + encodable.size x + 1) 0
      = a.foldl (fun acc x => acc + encodable.size x + 1) 0
        + b.foldl (fun acc x => acc + encodable.size x + 1) 0
  rw [List.foldl_append, shift b]

/-! ## 1 — the certificate space, enumerated

`bitStringsUpTo n` is every bit string of length `≤ n`. It is a `def`, it runs,
and its length is `2^(n+1) - 1` — the search below is exponential and says so. -/

/-- Every bit string of length `≤ n`, shortest first. -/
def bitStringsUpTo : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => [] :: (bitStringsUpTo n).flatMap (fun c => [false :: c, true :: c])

/-- The enumeration is exactly the length-`≤ n` strings — nothing missing (which
is what makes the search *complete*) and nothing extra. -/
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

/-- The search space is exponential, stated explicitly rather than left to the
reader: `2^(n+1) - 1` candidates. -/
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

/-! ## 2 — `inNPStr Q` forces `Q` to be decidable, by running the witness

The whole content is that the verifier is a **program**: `verifierAccepts` calls
`Cmd.eval` on the canonical layout and nothing else. -/

section Content

variable {Q : List Bool → Prop}

/-- The canonical two-register layout the string hypothesis pins: input bits in
register `0`, certificate bits in register `1`. -/
def strLayout (x c : List Bool) : State := certState x ++ certState c

/-- Under `InNPWitnessStr` the verifier's own input encoding **is** that layout —
this is the field `encX_canonical` doing its job, and it is why the search below
may call the verifier on a formula in `x` and `c` rather than on an opaque
`encodeIn`. -/
theorem encodeIn_eq_strLayout (W : InNPWitnessStr Q) (x c : List Bool) :
    W.verifier.encodeIn (x, c) = strLayout x c := by
  rw [W.encodeIn_eq x c, W.encX_canonical x]; rfl

/-- Run the witness's verifier program on the raw pair. **This is a `Cmd.eval`,
not a proposition** — it is the executable core of the whole file. -/
def verifierAccepts (W : InNPWitnessStr Q) (x c : List Bool) : Bool :=
  (W.verifier.c.eval (strLayout x c)).isAccept

/-- The program computes the certificate relation. -/
theorem verifierAccepts_iff (W : InNPWitnessStr Q) (x c : List Bool) :
    W.rel x c ↔ verifierAccepts W x c = true := by
  have h := (W.verifier.decides (x, c)).1
  rw [encodeIn_eq_strLayout W x c] at h
  exact h

/-- **The brute-force decider.** Given the witness (for its verifier program) and
the certificate-size bound (for the search radius), this is a running function:
it enumerates the certificate space and executes the verifier on each candidate.

It is a `def`, not a `noncomputable def`; `probes/NonVacuityProbe.lean` `#eval`s
it. That is the difference between this and the classical triviality warned about
at the bottom of this section. -/
def searchDecide (W : InNPWitnessStr Q) (bound : Nat → Nat) (x : List Bool) : Bool :=
  (bitStringsUpTo (bound (encodable.size x))).any (fun c => verifierAccepts W x c)

/-- **`inNPStr` has computational content.** For any string-language NP witness
and any certificate-size bound it comes with, `Q` is decided by the brute-force
search over that witness's own verifier.

Consequently **no undecidable `Q` satisfies `inNPStr Q`** — the freedom that
`probes/HonestyAuditProbe.lean` §7/§7b exploits against `NPhard''` is not
available against `NPhardStr`, and the hypothesis of `CookLevinStr` really is a
hypothesis about decidable problems. -/
theorem searchDecide_correct (W : InNPWitnessStr Q) (R : PolyCertRelWitness Q W.rel)
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

/-- The number of verifier runs the search performs, explicitly: exponential in
the certificate bound. Stated so that "decidable" here is never read as
"efficiently decidable". -/
theorem searchDecide_calls (bound : Nat → Nat) (x : List Bool) :
    (bitStringsUpTo (bound (encodable.size x))).length
      = 2 ^ (bound (encodable.size x) + 1) - 1 :=
  bitStringsUpTo_length _

/-- ⚠ **The weak form, stated only to be labelled.** This existential is
classically true for *every* predicate on every type (take `f := fun x => decide
(Q x)` with `Classical`), so on its own it certifies nothing. It is the theorem
this file must not be mistaken for; the content is `searchDecide` above, which is
a concrete running program built from the witness's own `Cmd`. -/
theorem inNPStr_exists_decider (h : inNPStr Q) :
    ∃ f : List Bool → Bool, ∀ x, Q x ↔ f x = true := by
  obtain ⟨W⟩ := h
  obtain ⟨R⟩ := W.rel_correct
  exact ⟨searchDecide W R.bound, fun x => searchDecide_correct W R x⟩

end Content

/-! ## 3 — the class is inhabited: `SquareStr`, with a real verifier `Cmd`

The cheapest language whose certificate is genuinely load-bearing: `x` is the
concatenation of some string with itself, and the certificate is that string.
The verifier doubles register `1` and compares with register `0` — two ops, and
it visibly *reads the certificate*. -/

/-- Bit strings as register content: one cell per bit. -/
def bits (l : List Bool) : List Nat := l.map (fun b => if b then 1 else 0)

theorem certState_eq_bits (l : List Bool) : certState l = [bits l] := rfl

theorem bits_append (a b : List Bool) : bits (a ++ b) = bits a ++ bits b := by
  simp [bits]

/-- The cell encoding is injective, so comparing register content really compares
strings. -/
theorem bits_inj : ∀ {a b : List Bool}, bits a = bits b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [bits] at h
  | _ :: _, [], h => by simp [bits] at h
  | a :: as, b :: bs, h => by
      simp only [bits, List.map_cons, List.cons.injEq] at h
      have hab : a = b := by cases a <;> cases b <;> simp_all
      have := bits_inj (a := as) (b := bs) (by simpa [bits] using h.2)
      rw [hab, this]

theorem bits_length (l : List Bool) : (bits l).length = l.length :=
  List.length_map _

/-- `x` is a square word. -/
def SquareStr (x : List Bool) : Prop := ∃ c, x = c ++ c

/-- Its certificate relation: the certificate is the half. -/
def squareRel (x c : List Bool) : Prop := x = c ++ c

/-- The verifier: `reg2 := reg1 ++ reg1; reg0 := (reg0 == reg2)`. Register `0`
holds the input bits, register `1` the certificate bits (the canonical layout),
and register `0` is the output by the layer's convention. -/
def squareCmd : Cmd := Cmd.op (.concat 2 1 1) ;; Cmd.op (.eqBit 0 0 2)

theorem squareCmd_get0 (x c : List Bool) :
    State.get (squareCmd.eval (strLayout x c)) 0
      = if bits x = bits c ++ bits c then [1] else [0] := rfl

theorem squareCmd_accepts (x c : List Bool) :
    (squareCmd.eval (strLayout x c)).isAccept = true ↔ x = c ++ c := by
  simp only [State.isAccept, beq_iff_eq, squareCmd_get0]
  constructor
  · intro h
    by_cases hb : bits x = bits c ++ bits c
    · exact bits_inj (by rw [hb, bits_append])
    · rw [if_neg hb] at h; exact absurd h (by simp)
  · intro h
    rw [if_pos (by rw [h, bits_append])]

theorem squareCmd_rejects (x c : List Bool) :
    (squareCmd.eval (strLayout x c)).isReject = true ↔ ¬ x = c ++ c := by
  simp only [State.isReject, beq_iff_eq, squareCmd_get0]
  constructor
  · intro h hx
    rw [if_pos (by rw [hx, bits_append])] at h
    exact absurd h (by simp)
  · intro h
    by_cases hb : bits x = bits c ++ bits c
    · exact absurd (bits_inj (by rw [hb, bits_append])) h
    · rw [if_neg hb]

/-- The layout's cell count is the two strings' lengths — no padding, no header. -/
theorem strLayout_size (x c : List Bool) :
    State.size (strLayout x c) = x.length + c.length := by
  show ((([bits x, bits c] : State)).map List.length).foldr (· + ·) 0 = x.length + c.length
  simp [bits_length]

theorem bits_cells (l : List Bool) : ∀ v ∈ bits l, v ≤ 1 := by
  intro v hv
  obtain ⟨b, _, hb⟩ := List.mem_map.mp hv
  subst hb
  cases b <;> decide

theorem strLayout_bitState (x c : List Bool) : Compile.BitState (strLayout x c) := by
  intro reg hreg v hv
  have : reg = bits x ∨ reg = bits c := by
    simpa [strLayout, certState_eq_bits] using hreg
  rcases this with rfl | rfl
  · exact bits_cells x v hv
  · exact bits_cells c v hv

/-- Cost of the two ops on the canonical layout, exactly. -/
theorem squareCmd_cost (x c : List Bool) :
    squareCmd.cost (strLayout x c) = x.length + 6 * c.length + 3 := by
  show 1 + Op.cost (.concat 2 1 1) (strLayout x c)
        + Op.cost (.eqBit 0 0 2) (Op.eval (.concat 2 1 1) (strLayout x c))
      = x.length + 6 * c.length + 3
  show 1 + (2 * (((strLayout x c).get 1).length + ((strLayout x c).get 1).length) + 1)
        + ((((strLayout x c).set 2 ((strLayout x c).get 1 ++ (strLayout x c).get 1)).get 0).length
          + (((strLayout x c).set 2 ((strLayout x c).get 1 ++ (strLayout x c).get 1)).get 2).length
          + 1)
      = x.length + 6 * c.length + 3
  simp only [strLayout, certState_eq_bits]
  show 1 + (2 * ((bits c).length + (bits c).length) + 1)
        + ((bits x).length + ((bits c) ++ (bits c)).length + 1)
      = x.length + 6 * c.length + 3
  simp [bits_length]
  omega

/-- The verifier's cost bound: `6n` on `n = encodable.size (x, c)`. -/
def squareBound : Nat → Nat := fun n => 6 * n

theorem squareBound_poly : inOPoly squareBound := by
  refine ⟨1, ⟨6, 0, ?_⟩⟩
  intro n _
  simp [squareBound]

theorem squareBound_mono : monotonic squareBound := by
  intro a b h
  exact Nat.mul_le_mul_left 6 h

/-- The verifier as a free-line `DecidesLang` over the canonical layout. -/
def squareVerifier :
    DecidesLang (fun xc : List Bool × List Bool => squareRel xc.1 xc.2) squareBound where
  c := squareCmd
  encodeIn := fun xc => strLayout xc.1 xc.2
  encodeIn_size := by
    rintro ⟨x, c⟩
    have hx : x.length ≤ encodable.size x := length_le_size x
    have hc : c.length ≤ encodable.size c := length_le_size c
    show State.size (strLayout x c) ≤ 6 * (encodable.size x + encodable.size c + 1)
    rw [strLayout_size]
    omega
  decides := by
    rintro ⟨x, c⟩
    exact ⟨(squareCmd_accepts x c).symm, (squareCmd_rejects x c).symm⟩
  cost_bound := by
    rintro ⟨x, c⟩
    have hx : x.length ≤ encodable.size x := length_le_size x
    have hc : c.length ≤ encodable.size c := length_le_size c
    show squareCmd.cost (strLayout x c) ≤ 6 * (encodable.size x + encodable.size c + 1)
    rw [squareCmd_cost]
    omega
  enc_bit := by rintro ⟨x, c⟩; exact strLayout_bitState x c
  regBound := 3
  usesBelow := ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩
  width_le := by rintro ⟨x, c⟩; exact (by decide : (2 : Nat) ≤ 3)

/-- The certificate relation is sound, complete and polynomially bounded — the
half `x = c ++ c` is never bigger than `x`. -/
def squareCertRel : PolyCertRelWitness SquareStr squareRel where
  bound := fun n => n
  sound := by rintro x c rfl; exact ⟨c, rfl⟩
  complete := by
    rintro x ⟨c, rfl⟩
    exact ⟨c, rfl, by rw [size_append]; omega⟩
  bound_poly := inOPoly_id
  bound_mono := fun _ _ h => h

/-- **The inhabitant.** A complete `InNPWitnessStr` — every field discharged,
`sorry`-free, over the canonical layout. `inNPStr` is not the empty class. -/
def squareWitness : InNPWitnessStr SquareStr where
  rel := squareRel
  dBound := squareBound
  dBound_poly := squareBound_poly
  dBound_mono := squareBound_mono
  verifier := squareVerifier
  rel_correct := ⟨squareCertRel⟩
  encX := certState
  encodeIn_eq := fun _ _ => rfl
  xWidth := 1
  encX_width := fun _ => rfl
  encX_size := by
    intro x
    have hx : x.length ≤ encodable.size x := length_le_size x
    show State.size (certState x) ≤ 6 * encodable.size x
    rw [State.size_certState]
    omega
  sizeLB := fun n => 2 * n
  sizeLB_poly := by
    refine ⟨1, ⟨2, 0, ?_⟩⟩
    intro n _
    simp
  encX_sizeLB := by
    intro x
    rw [State.size_certState]
    exact size_le_two_mul_length x
  encX_canonical := fun _ => rfl

theorem inNPStr_squareStr : inNPStr SquareStr := ⟨squareWitness⟩

/-! ## 4 — the inhabitant is a real language

`SquareStr` is neither empty nor total: it separates strings. Without this a
reader has no way to tell that §3 did not simply present `fun _ => True`. -/

theorem squareStr_nil : SquareStr [] := ⟨[], rfl⟩

theorem squareStr_tt : SquareStr [true, true] := ⟨[true], rfl⟩

theorem squareStr_tf : SquareStr [true, false, true, false] := ⟨[true, false], rfl⟩

/-- Odd length is impossible: `x = c ++ c` forces `|x| = 2|c|`. -/
theorem not_squareStr_of_odd_length {x : List Bool} (h : x.length % 2 = 1) : ¬ SquareStr x := by
  rintro ⟨c, rfl⟩
  rw [List.length_append] at h
  omega

theorem not_squareStr_single : ¬ SquareStr [true] :=
  not_squareStr_of_odd_length rfl

/-- …and even length is not sufficient either, so the language is not "the even
strings" in disguise. -/
theorem not_squareStr_tf2 : ¬ SquareStr [true, false] := by
  rintro ⟨c, hc⟩
  cases c with
  | nil => simp at hc
  | cons b t =>
      have hlen := congrArg List.length hc
      simp only [List.length_cons, List.length_append, List.length_nil] at hlen
      have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst ht
      simp at hc

/-- The certificate is load-bearing: the verifier's answer on the *same* input
changes with the certificate register. -/
theorem verifier_reads_certificate :
    verifierAccepts squareWitness [true, false, true, false] [true, false] = true ∧
    verifierAccepts squareWitness [true, false, true, false] [true, true] = false := by
  constructor <;> rfl

/-! ## 5 — the payoff: `CookLevinStr` at a concrete problem

The hardness half of the published theorem, applied to §3's witness. This is the
whole chain — C8 front, S1, and the four-step sound tail — instantiated, and it
is what makes `NPhardStr SAT` a statement with consequences. -/

theorem squareStr_reducesPolyMO'_SAT : SquareStr ⪯p' SAT :=
  CookLevinHonest.CookLevinStr.1 SquareStr inNPStr_squareStr

/-! ## 6 — the inhabitant that is not in P: SAT itself, as a string language

`SquareStr` shows the class is non-empty; it does not show the class contains
anything *hard* — it is decidable in linear time. `SATStr`
(`Complexity/Complexity/Deciders/SATStr.lean`) is the upgrade: the language of
bit strings that spell out a satisfiable CNF, with a complete `InNPWitnessStr`
whose verifier is the development's own SAT verifier `Cmd` preceded by a
four-state validating scan.

`satStr_reducesPolyMO'_SAT` is then the published theorem applied to (a string
form of) **its own target** — the whole chain, C8 front through the sound tail,
running on SAT.

✅ **Closed 2026-08-05: the class contains an NP-*complete* problem.** The
reverse reduction `SAT ⪯p' SATStr` and its seam landed
(`Reductions/SAT_to_SATStr_free.lean` + `SAT_to_SATStr_comp.lean`), so
`NPhardStr SATStr` and `NPcompleteStr SATStr` are theorems. The inhabitant this
section exhibits is therefore not merely "hard given Cook–Levin" but
NP-complete *in this development's own sense*, both halves proven here. -/

theorem inNPStr_SATStr : inNPStr SATStr.SATStr := SATStr.inNPStr_SATStr

/-- **The payoff, at a hard problem.** `CookLevinStr`'s hardness half applied to
SAT presented as a string language. -/
theorem satStr_reducesPolyMO'_SAT : SATStr.SATStr ⪯p' SAT :=
  CookLevinHonest.CookLevinStr.1 SATStr.SATStr SATStr.inNPStr_SATStr

/-- **…and the class's inhabitant is NP-complete, not merely non-trivial**
(2026-08-05). Both halves are theorems of this development: membership is
`SATStr.satStrWitness`, hardness is the whole chain with a sixth seam on its
tail. This is the strongest non-vacuity statement available: the hypothesis of
`NPhardStr` is inhabited by a problem to which *every* inhabitant reduces. -/
theorem npcompleteStr_SATStr : NPcompleteStr SATStr.SATStr :=
  SATStrComp.SATStr_NPcompleteStr

/-- **…and in the strict sense, where the membership conjunct is not vacuous**
(2026-08-07, FINDING AX). `NPcompleteStr`'s membership half quantifies over
`InNPWitnessLangFreeSplit`, a class that carries a free input layout and is
therefore inhabited by *every* string language
(`probes/HonestyAuditProbe.lean` §7c) — so the statement above, read alone, says
only that `SATStr` is NP-**hard**. `NPcompleteStr' = NPhardStr P ∧ inNPStr P`
pins the membership layout to `certState` as well, and `SATStr.satStrWitness`
already meets it. **This is the non-vacuity claim to quote**: the hypothesis
class of `NPhardStr` contains a problem that is NP-complete in this
development's own sense, with both conjuncts making a real claim. -/
theorem npcompleteStr'_SATStr : NPcompleteStr' SATStr.SATStr :=
  SATStrComp.SATStr_NPcompleteStr'

/-! ## The gate -/

#assert_axioms_clean
  Complexity.NonVacuity.searchDecide_correct
  Complexity.NonVacuity.searchDecide_calls
  Complexity.NonVacuity.mem_bitStringsUpTo
  Complexity.NonVacuity.bitStringsUpTo_length
  Complexity.NonVacuity.verifierAccepts_iff
  Complexity.NonVacuity.inNPStr_squareStr
  Complexity.NonVacuity.not_squareStr_single
  Complexity.NonVacuity.not_squareStr_tf2
  Complexity.NonVacuity.verifier_reads_certificate
  Complexity.NonVacuity.squareStr_reducesPolyMO'_SAT
  Complexity.NonVacuity.inNPStr_SATStr
  Complexity.NonVacuity.satStr_reducesPolyMO'_SAT
  Complexity.NonVacuity.npcompleteStr_SATStr
  Complexity.NonVacuity.npcompleteStr'_SATStr
  SATStr.satStr_iff
  SATStr.inNPStr_SATStr
  SATStr.verifier_reads_certificate
  SATStr.verifier_rejects_malformed
  SATStr.not_satStr_true
  SATStr.not_satStr_x0_and_not_x0
  SATStr.satStr_x0
  CnfWellFormed.wfCnfB_iff
  CnfWellFormed.cnfCount_eq_length
  CnfWellFormed.encodeCnf_parseTotal
  CnfWellFormed.not_sat_botCnf

end Complexity.NonVacuity
