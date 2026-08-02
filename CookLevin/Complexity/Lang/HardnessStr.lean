import Complexity.Lang.PolyTime

set_option autoImplicit false

/-! # `NPhardStr` — hardness over STRING languages, the honest headline

## The problem this file fixes (top-down, 2026-08-01)

`NPhard'' P = ∀ Y, ∀ _ : encodable Y, ∀ Q : Y → Prop, inNPLangFreeSplit Q → Q ⪯p' P`
quantifies over an **abstract** type `Y` together with a witness that supplies
its own input layout `encX : Y → State`. `encX` is a free function, and the
composite reduction's `ComputesBy.encode` is built from it
(`FrontWitness.encodeInQ W x = W.encX x ++ [1^(size x)]`, FINDING AK). So the
hypothesis carries a hole of exactly the shape `probes/HonestyAuditProbe.lean`
§6 exhibits on the conclusion side — and §7 of that probe now exhibits it here:

> for **every** predicate `Q` on **every** encodable type — including
> undecidable ones — there is a complete, `sorry`-free `InNPWitnessLangFreeSplit
> Q` whose `encX x` is the single register `[if Q x then 1 else 0]` and whose
> verifier is the layer's no-op. Hence `NPhard'' SAT` yields `Q ⪯p' SAT` for an
> arbitrary `Q`.

That is not an inconsistency — the produced `⪯p'` is a real machine on an
answer-bearing encoding, exactly as in §6 — but it does mean **`NPhard''` cannot
be read as "every NP problem reduces to SAT" without also reading the
presentation's `encX`**. The audit obligation was on the *consumer*, and no
amount of care on our own witnesses could discharge it.

## The fix: quantify over bit strings, where there is nothing left to choose

The textbook statement is about languages `L ⊆ Σ*`. Take `Y := List Bool` and
**pin the input layout to the canonical one-register string layout**
`certState` — the same layout the certificate side already uses. Then:

* there is no `encX` to audit: it is `certState`, fixed by the statement;
* the composite reduction's encode is **`certState x` itself** — the raw input
  string, one register, one cell per bit (`probes/HonestyAuditProbe.lean` §8
  pins it). ⚠ Until 2026-08-02 a unary tally `1^(encodable.size x)` was appended;
  the reduction now counts its own input's cells on-machine, so there is no
  formula left to read at all;
* the hypothesis has real content: the verifier is a `Cmd` that must decide
  `rel x c` **from the raw string**, so it can no longer be a no-op reading a
  planted answer.

`NPhardStr` is a *restriction* of `NPhard''`, so it is logically weaker and
follows in one line (`NPhard''_to_NPhardStr`). Its value is not logical strength
but that **its statement has no dishonest instantiation**: it is the strongest
hardness claim of this development whose meaning survives an adversarial reader.

## What is still not enforced (say it plainly)

* The reduction's *output* decoder is still a free field of the witness; at the
  chain's tail it is pinned to the canonical CNF parser by hand
  (`FSATSATFree.decodeOut = Serialize.dec ∘ get CNFOUT`, 2026-08-01).
* ~~The size register is handed over by `encodeIn`~~ — **closed 2026-08-02.**
  `InNPWitnessLangFreeSplit.sizeLB` supplies the lower bound the front needed,
  `FrontPieces.tallyCells` counts the cells, and `encodeIn` is `encX` verbatim.
* The definitional trust at the statement is untouched and irreducible: is
  `FlatTM`/`stepFlatTM` a faithful Turing machine, is `Op.cost` a faithful proxy
  for time, does `SAT` mean satisfiability.
-/

namespace Complexity.Lang

/-- **A string-language NP witness.** An `InNPWitnessLangFreeSplit` over
`List Bool` whose input layout is the canonical string layout `certState`, i.e.
one register holding the raw bits. Everything else is inherited: a real `Cmd`
verifier over `certState x ++ certState c`, a polynomial cost bound, and a
sound/complete polynomially-bounded certificate relation.

There is deliberately **no** field left that an instantiator can use to hide the
answer in the input. -/
structure InNPWitnessStr (Q : List Bool → Prop) extends InNPWitnessLangFreeSplit Q where
  /-- The input layout is the canonical one: the raw string, one register. -/
  encX_canonical : ∀ x, encX x = certState x

/-- `Q` is a string language in NP, presented with a real verifier over the raw
string. -/
def inNPStr (Q : List Bool → Prop) : Prop := Nonempty (InNPWitnessStr Q)

/-- The canonical layout has width one. -/
theorem InNPWitnessStr.xWidth_eq_one {Q : List Bool → Prop} (W : InNPWitnessStr Q) :
    W.xWidth = 1 := by
  have h := W.encX_width []
  rw [W.encX_canonical []] at h
  exact h.symm

/-- **The honest hardness statement**: every NP *string language* — presented
with a real `Cmd` verifier reading the raw string — reduces to `P` by a real
TM-backed poly-time reduction. -/
def NPhardStr {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∀ Q : List Bool → Prop, inNPStr Q → Q ⪯p' P

/-- **The honest completeness statement.**

⚠ **Read the note on `NPcompleteStr'` below before quoting this one.** Its
*hardness* conjunct is the honest one — `NPhardStr` has no `encX` to choose. Its
*membership* conjunct `inNPLangFreeSplit P` is not: that class is inhabited for
**every** string language, undecidable ones included
(`probes/HonestyAuditProbe.lean` §7b/§7c). So the second half of this statement
carries no information on its own; all of its content is that *our* instance is
honest, which is risk S5's business, not this statement's. -/
def NPcompleteStr {X : Type} [encodable X] (P : X → Prop) : Prop :=
  NPhardStr P ∧ inNPLangFreeSplit P

/-- **The completeness statement to quote for a bit-string language** — both
halves over the canonical layout (top-down audit, ROADMAP risk S8, 2026-08-07).

`NPcompleteStr` states membership as `inNPLangFreeSplit P`, whose witness
structure still carries a free input layout `encX`. By FINDING AO no law about
`encX` can rule out "the honest encoding, plus one register holding the answer",
and `probes/HonestyAuditProbe.lean` §7c turns that into the flat statement:
`inNPLangFreeSplit Q` holds for **every** `Q : List Bool → Prop`. A conjunct
that is true of everything says nothing.

`inNPStr P` is the same claim with the layout pinned to `certState` — the raw
input string, one register, one cell per bit — exactly as the hardness half
already pins it. There is nothing left for an instantiator to choose on either
side of the conjunction, so this statement, unlike `NPcompleteStr`, has no
dishonest instantiation in *either* half.

This costs nothing: `SATStr.satStrWitness` is already an `InNPWitnessStr`, and
`SATStrComp.SATStr_NPcompleteStr` was discarding precisely the `encX_canonical`
field that makes the conjunct real. Live at
`SATStrComp.SATStr_NPcompleteStr'`. -/
def NPcompleteStr' (P : List Bool → Prop) : Prop :=
  NPhardStr P ∧ inNPStr P

/-- The strict statement implies the general one: `InNPWitnessStr` forgets to
`InNPWitnessLangFreeSplit`. The converse does **not** hold, which is the whole
point — see the docstrings above. -/
theorem NPcompleteStr'_to_NPcompleteStr {P : List Bool → Prop}
    (h : NPcompleteStr' P) : NPcompleteStr P :=
  ⟨h.1, by obtain ⟨W⟩ := h.2; exact ⟨W.toInNPWitnessLangFreeSplit⟩⟩

/-- `NPhard''` implies `NPhardStr`: the string presentation is one of the
presentations `NPhard''` quantifies over. One line — the whole point is that the
*statement* is cleaner, not that the theorem is harder. -/
theorem NPhard''_to_NPhardStr {X : Type} [encodable X] {P : X → Prop}
    (h : NPhard'' P) : NPhardStr P := by
  intro Q hQ
  obtain ⟨W⟩ := hQ
  exact h (List Bool) inferInstance Q ⟨W.toInNPWitnessLangFreeSplit⟩

/-- `NPcomplete''` implies `NPcompleteStr`. -/
theorem NPcomplete''_to_NPcompleteStr {X : Type} [encodable X] {P : X → Prop}
    (h : NPcomplete'' P) : NPcompleteStr P :=
  ⟨NPhard''_to_NPhardStr h.1, h.2⟩

/-! ## The sandwich the head needs, as a THEOREM (not a hypothesis)

Under the canonical layout the input register's length is a *faithful* measure
of the input: `encodable.size` of a `List Bool` is between one and two cells per
bit. This is the fact the C8-4 finding of 2026-07-20-c said was missing for an
abstract `encX` ("`encX` need not be injective, so no monomial in
`State.size (encX x)` can be *proven* to dominate a `size x`-budget") — for
string languages it is not an assumption, it is arithmetic. -/

/-- `State.size (certState x) = x.length`: the canonical layout is one register
holding one cell per bit. -/
theorem State.size_certState (x : List Bool) : State.size (certState x) = x.length := by
  show (x.map (fun b => if b then 1 else 0)).length + 0 = x.length
  rw [List.length_map, Nat.add_zero]

/-- **No compression**, canonical side: `encodable.size` of a bit string is at
most twice its length, so a unary tally of the input register dominates any
`encodable.size`-stated budget up to a constant factor. -/
theorem size_le_two_mul_length (x : List Bool) : encodable.size x ≤ 2 * x.length := by
  show x.foldl (fun acc b => acc + encodable.size b + 1) 0 ≤ 2 * x.length
  have key : ∀ (l : List Bool) (acc : Nat),
      l.foldl (fun acc b => acc + encodable.size b + 1) acc ≤ acc + 2 * l.length := by
    intro l
    induction l with
    | nil => intro acc; exact Nat.le_of_eq (by simp)
    | cons b t ih =>
        intro acc
        have hb : encodable.size b ≤ 1 := by
          cases b
          · exact Nat.zero_le 1
          · exact Nat.le_refl 1
        have h := ih (acc + encodable.size b + 1)
        simp only [List.foldl_cons, List.length_cons]
        omega
  have := key x 0
  omega

/-- …and the other direction: the string's own length never exceeds its size. -/
theorem length_le_size (x : List Bool) : x.length ≤ encodable.size x := by
  show x.length ≤ x.foldl (fun acc b => acc + encodable.size b + 1) 0
  have key : ∀ (l : List Bool) (acc : Nat),
      acc + l.length ≤ l.foldl (fun acc b => acc + encodable.size b + 1) acc := by
    intro l
    induction l with
    | nil => intro acc; exact Nat.le_of_eq (by simp)
    | cons b t ih =>
        intro acc
        have h := ih (acc + encodable.size b + 1)
        simp only [List.foldl_cons, List.length_cons]
        omega
  have := key x 0
  omega

/-- **The `sizeLB` field is not a choice for a string language.** The general
hypothesis (`InNPWitnessLangFreeSplit`, 2026-08-02) asks the instantiator for a
polynomial recovering `encodable.size x` from the layout's own cell count. Under
`encX_canonical` the layout is `certState`, so `fun n => 2 * n` always works and
is always *correct* — the field adds an obligation, never a freedom. -/
theorem InNPWitnessStr.canonical_sizeLB {Q : List Bool → Prop} (W : InNPWitnessStr Q)
    (x : List Bool) : encodable.size x ≤ 2 * State.size (W.encX x) := by
  rw [W.encX_canonical x, State.size_certState]
  exact size_le_two_mul_length x

end Complexity.Lang
