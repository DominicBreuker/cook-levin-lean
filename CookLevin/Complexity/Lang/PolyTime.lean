import Complexity.Lang.Compile
import Complexity.Complexity.NP

set_option autoImplicit false

/-! # Lang-level polynomial-time predicates and bridges to `inTimePoly`

The whole point of the layer is to *replace* the hand-rolled
`DecidesBy` and `PolyTimeComputableWitness` constructions with
layer-level programs. This file:

1. Defines `inTimePolyLang P` and `PolyTimeComputableLang f` — the
   layer-level analogues of the framework predicates.
2. Provides bridge theorems that lift a layer-level witness to the
   framework's TM-backed witness, via `Compile`.

Bridges are sorry-bodied at the skeleton stage; they all reduce to
`Compile_sound` once that lands.
-/

namespace Complexity.Lang

/-- A program `c` *decides* a predicate `P` in cost bound `costBound`
when run on the encoded input `encodeIn`.

This is the layer-level analogue of `DecidesBy`. The TM-level
`DecidesBy` is then obtained from `inTimePolyLang_to_DecidesBy`
below. -/
structure DecidesLang {X : Type} [encodable X]
    (P : X → Prop) (costBound : Nat → Nat) where
  /-- The DSL program. -/
  c : Cmd
  /-- How inputs are laid out in the program's initial state. -/
  encodeIn : X → State
  /-- The encoded state's size is linearly bounded by the input
  size, modulo a constant. -/
  encodeIn_size : ∀ x, State.size (encodeIn x) ≤ encodable.size x + 1
  /-- The program decides `P` from the encoded input. -/
  decides : Cmd.decides c encodeIn P
  /-- Cost bound: running `c` on `encodeIn x` costs at most
  `costBound (encodable.size x)` primitive operations. -/
  cost_bound : ∀ x, c.cost (encodeIn x) ≤ costBound (encodable.size x)

/-- `P` is in polynomial time *at the layer level*: there is a
`DecidesLang` witness with polynomially bounded cost. -/
def inTimePolyLang {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ f, Nonempty (DecidesLang P f) ∧ inOPoly f ∧ monotonic f

/-- A polynomial-time computable function `f` *at the layer level*:
a `Cmd` that reads `f`'s input from the encoded state and writes
`f`'s output to a designated output register, with polynomially
bounded cost. -/
structure PolyTimeComputableLang {X Y : Type} [encodable X] [encodable Y]
    (f : X → Y) where
  c : Cmd
  encodeIn : X → State
  decodeOut : State → Y
  cost_bound : Nat → Nat
  cost_bound_poly : inOPoly cost_bound
  cost_bound_mono : monotonic cost_bound
  encodeIn_size : ∀ x, State.size (encodeIn x) ≤ encodable.size x + 1
  /-- After running `c`, the output register decodes to `f x`. -/
  computes : ∀ x, decodeOut (c.eval (encodeIn x)) = f x
  /-- Running `c` is polynomial-time. -/
  cost_le : ∀ x, c.cost (encodeIn x) ≤ cost_bound (encodable.size x)
  /-- Output size is bounded by the output of `cost_bound` —
  i.e. polynomial-time output is polynomial-size. -/
  output_size_le : ∀ x, encodable.size (f x) ≤ cost_bound (encodable.size x)

/-! ## Bridges

These are the *main results* of Part 3 from the consumer's
perspective. They are stated here with `sorry` bodies; the proofs
follow mechanically from `Compile_sound` once that lands. -/

/-- **Bridge 1 (Part 3.4):** a layer-level `DecidesLang` witness
extends to a framework-level `DecidesBy` witness. -/
theorem DecidesLang.toDecidesBy {X : Type} [encodable X]
    {P : X → Prop} {costBound : Nat → Nat}
    (D : DecidesLang P costBound)
    (h_mono : monotonic costBound) :
    Nonempty (DecidesBy P (fun n => Compile.overhead n * (costBound n + 1))) := by
  sorry  -- TODO(Part3.5)

/-- **Bridge 2 (Part 3.4):** `inTimePolyLang P` implies
`inTimePoly P`. This is the headline consumer-facing fact. -/
theorem inTimePolyLang_to_inTimePoly {X : Type} [encodable X]
    {P : X → Prop} (h : inTimePolyLang P) : inTimePoly P := by
  sorry  -- TODO(Part3.5): use DecidesLang.toDecidesBy + inOPoly_comp.

/-- **Bridge 3 (Part 4.1):** a layer-level `PolyTimeComputableLang`
witness extends to a framework-level `PolyTimeComputableWitness`. -/
theorem PolyTimeComputableLang.toFrameworkWitness
    {X Y : Type} [encodable X] [encodable Y] {f : X → Y}
    (W : PolyTimeComputableLang f) :
    polyTimeComputable f := by
  -- The framework currently bounds *output size*, so this is the
  -- easy direction. The forward bridge (use `Compile` to produce a
  -- TM that computes `f` in poly time) is the more interesting
  -- content; until the framework upgrades `polyTimeComputable` to
  -- be TM-backed (Part 4.1 proper), this is what we have.
  refine ⟨⟨W.cost_bound, W.cost_bound_poly, W.cost_bound_mono, ?_⟩⟩
  intro x
  exact W.output_size_le x

/-- **Composition (Part 4 / Part 3):** the layer is closed under
`Cmd.seq`, so polynomially-bounded computable functions compose. -/
noncomputable def PolyTimeComputableLang.comp
    {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    {g : Y → Z} {h : X → Y}
    (Wg : PolyTimeComputableLang g) (Wh : PolyTimeComputableLang h) :
    PolyTimeComputableLang (g ∘ h) := by
  sorry  -- TODO(Part4.1): sequence Wh.c then Wg.c with a register-
         -- shuffle in between; cost is bound by Wh.cost_bound +
         -- Wg.cost_bound ∘ Wh.cost_bound.

/-- **NP-style composition (Part 4):** if `P ⪯p Q` (via a
poly-time reduction witnessed at the layer level) and `Q ∈ inNP`
(via a layer-level verifier), then `P ∈ inNP`. This is the missing
piece that closes the `red_inNP` TM-composition sorry. -/
theorem red_inNP_via_lang
    {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop)
    (f : X → Y) (hf : PolyTimeComputableLang f)
    (hf_correct : ∀ x, P x ↔ Q (f x))
    (hQ : inNP Q) :
    inNP P := by
  sorry  -- TODO(Part4.2): destructure hQ, compose the verifier
         -- with hf via Cmd.seq, repackage as inNP P.

end Complexity.Lang
