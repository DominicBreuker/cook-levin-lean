import CookLevin.Basic.Definitions

/-!
# The binary covering-card problem

`BinaryCCLang C`: the rows of a tableau over `Bool` of the given width, starting from the
initial row, can be rewritten `steps` times by the cards (`validStep`, every window is
covered by a card) to a row containing a final substring.
-/

set_option autoImplicit false

def BinaryCC_wellformed (C : BinaryCC) : Prop :=
  C.width > 0 ∧
    C.offset > 0 ∧
    (∃ k, k > 0 ∧ C.width = k * C.offset) ∧
    C.init.length ≥ C.width ∧
    (∀ card, card ∈ C.cards → card.prem.length = C.width ∧ card.conc.length = C.width) ∧
    (∃ k, C.init.length = k * C.offset)

def coversHead (card : CCCard Bool) (a b : List Bool) : Prop :=
  isPrefix card.prem a ∧ isPrefix card.conc b

def validStep (offset width : Nat) (cards : List (CCCard Bool)) (a b : List Bool) : Prop :=
  a.length = b.length ∧
    ∀ step, step * offset + width ≤ a.length →
      ∃ card, card ∈ cards ∧ coversHead card (a.drop (step * offset)) (b.drop (step * offset))

def satFinal (offset l : Nat) (final : List (List Bool)) (s : List Bool) : Prop :=
  ∃ subs step, subs ∈ final ∧ step * offset ≤ l ∧ isPrefix subs (s.drop (step * offset))

def BinaryCCLang (C : BinaryCC) : Prop :=
  BinaryCC_wellformed C ∧
    ∃ sf, relpower (validStep C.offset C.width C.cards) C.steps C.init sf ∧
      satFinal C.offset C.init.length C.final sf
