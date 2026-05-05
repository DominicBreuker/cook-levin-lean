import Complexity.Complexity.Definitions

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

def binaryCCYesInstance : BinaryCC where
  offset := 1
  width := 1
  init := [false]
  cards := []
  final := [[false]]
  steps := 0

theorem binaryCCYesInstance_valid : BinaryCCLang binaryCCYesInstance := by
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, by decide, ⟨1, by decide, by decide⟩, by simp [binaryCCYesInstance], ?_, ⟨1, by simp [binaryCCYesInstance]⟩⟩
    intro card hcard
    cases hcard
  · refine ⟨binaryCCYesInstance.init, relpower.refl _, ?_⟩
    refine ⟨[false], 0, by simp [binaryCCYesInstance], by decide, ?_⟩
    refine ⟨[], rfl⟩
