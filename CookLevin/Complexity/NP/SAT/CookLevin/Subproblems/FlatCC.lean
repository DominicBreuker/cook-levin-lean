import Complexity.Complexity.Definitions

set_option autoImplicit false

namespace CC

def CCCard_of_size {α : Type} (card : CCCard α) (k : Nat) : Prop :=
  card.prem.length = k ∧ card.conc.length = k

def wellformed (C : CC) : Prop :=
  C.width > 0 ∧
    C.offset > 0 ∧
    (∃ k, k > 0 ∧ C.width = k * C.offset) ∧
    C.init.length ≥ C.width ∧
    (∀ card, card ∈ C.cards → CCCard_of_size card C.width) ∧
    (∃ k, C.init.length = k * C.offset)

def coversHead {k : Nat} (card : CCCard (Fin k)) (a b : List (Fin k)) : Prop :=
  isPrefix card.prem a ∧ isPrefix card.conc b

def satFinal {k : Nat} (offset l : Nat) (final : List (List (Fin k))) (s : List (Fin k)) : Prop :=
  ∃ subs step, subs ∈ final ∧ step * offset ≤ l ∧ isPrefix subs (s.drop (step * offset))

def validStep {k : Nat} (offset width : Nat) (cards : List (CCCard (Fin k)))
    (a b : List (Fin k)) : Prop :=
  a.length = b.length ∧
    ∀ step, step * offset + width ≤ a.length →
      ∃ card, card ∈ cards ∧ coversHead card (a.drop (step * offset)) (b.drop (step * offset))

def CCLang (C : CC) : Prop :=
  wellformed C ∧
    ∃ sf, relpower (validStep C.offset C.width C.cards) C.steps C.init sf ∧
      satFinal C.offset C.init.length C.final sf

end CC

def CCCard_ofFlatType (card : CCCard Nat) (k : Nat) : Prop :=
  list_ofFlatType k card.prem ∧ list_ofFlatType k card.conc

def isValidFlatCards (cards : List (CCCard Nat)) (k : Nat) : Prop :=
  ∀ card, card ∈ cards → CCCard_ofFlatType card k

def isValidFlatFinal (final : List (List Nat)) (k : Nat) : Prop :=
  ∀ s, s ∈ final → list_ofFlatType k s

def isValidFlatInitial (init : List Nat) (k : Nat) : Prop :=
  list_ofFlatType k init

def FlatCC_wellformed (C : FlatCC) : Prop :=
  C.width > 0 ∧
    C.offset > 0 ∧
    (∃ k, k > 0 ∧ C.width = k * C.offset) ∧
    C.init.length ≥ C.width ∧
    (∀ card, card ∈ C.cards → CC.CCCard_of_size card C.width) ∧
    (∃ k, C.init.length = k * C.offset)

def isValidFlattening (C : FlatCC) : Prop :=
  isValidFlatInitial C.init C.Sigma ∧
    isValidFlatFinal C.final C.Sigma ∧
    isValidFlatCards C.cards C.Sigma

def flattenCard {k : Nat} (card : CCCard (Fin k)) : CCCard Nat where
  prem := flattenString card.prem
  conc := flattenString card.conc

def flattenFinal {k : Nat} (final : List (List (Fin k))) : List (List Nat) :=
  final.map flattenString

def flattenCC (C : CC) : FlatCC where
  Sigma := C.Sigma
  offset := C.offset
  width := C.width
  init := flattenString C.init
  cards := C.cards.map flattenCard
  final := flattenFinal C.final
  steps := C.steps

theorem CCCard_ofFlatType_flatten {k : Nat} (card : CCCard (Fin k)) :
    CCCard_ofFlatType (flattenCard card) k := by
  exact ⟨flattenString_list_ofFlatType card.prem, flattenString_list_ofFlatType card.conc⟩

theorem isValidFlatFinal_flatten {k : Nat} (final : List (List (Fin k))) :
    isValidFlatFinal (flattenFinal final) k := by
  intro s hs
  simp [flattenFinal] at hs
  rcases hs with ⟨s', hs', rfl⟩
  exact flattenString_list_ofFlatType s'

theorem isValidFlattening_flattenCC (C : CC) :
    isValidFlattening (flattenCC C) := by
  refine ⟨flattenString_list_ofFlatType C.init, isValidFlatFinal_flatten C.final, ?_⟩
  intro card hcard
  simp [flattenCC] at hcard
  rcases hcard with ⟨card', hcard', rfl⟩
  exact CCCard_ofFlatType_flatten card'

theorem flattenCC_wellformed {C : CC} :
    CC.wellformed C → FlatCC_wellformed (flattenCC C) := by
  intro h
  rcases h with ⟨hwidth, hoffset, hmult, hinit, hcards, hlen⟩
  refine ⟨hwidth, hoffset, hmult, by simpa [flattenCC, flattenString] using hinit, ?_, ?_⟩
  intro card hcard
  simp [flattenCC] at hcard
  rcases hcard with ⟨card', hcard', rfl⟩
  simpa [CC.CCCard_of_size, flattenCard, flattenString] using hcards card' hcard'
  rcases hlen with ⟨k, hk⟩
  exact ⟨k, by simpa [flattenCC, flattenString] using hk⟩

def unflattenCard (k : Nat) (card : CCCard Nat) (h : CCCard_ofFlatType card k) : CCCard (Fin k) where
  prem := unflattenList k card.prem h.1
  conc := unflattenList k card.conc h.2

def unflattenCards (k : Nat) :
    (cards : List (CCCard Nat)) → isValidFlatCards cards k → List (CCCard (Fin k))
  | [], _ => []
  | card :: cards, h =>
      have hcard : CCCard_ofFlatType card k := h card (by simp)
      have hcards : isValidFlatCards cards k := by
        intro card' hcard'
        exact h card' (by simp [hcard'])
      unflattenCard k card hcard :: unflattenCards k cards hcards

def unflattenFinal (k : Nat) :
    (final : List (List Nat)) → isValidFlatFinal final k → List (List (Fin k))
  | [], _ => []
  | s :: final, h =>
      have hs : list_ofFlatType k s := h s (by simp)
      have hfinal : isValidFlatFinal final k := by
        intro s' hs'
        exact h s' (by simp [hs'])
      unflattenList k s hs :: unflattenFinal k final hfinal

def unflattenCC (C : FlatCC) (h : isValidFlattening C) : CC where
  Sigma := C.Sigma
  offset := C.offset
  width := C.width
  init := unflattenList C.Sigma C.init h.1
  cards := unflattenCards C.Sigma C.cards h.2.2
  final := unflattenFinal C.Sigma C.final h.2.1
  steps := C.steps

theorem flatten_unflattenCard (k : Nat) (card : CCCard Nat) (h : CCCard_ofFlatType card k) :
    flattenCard (unflattenCard k card h) = card := by
  cases card
  cases h
  simp [unflattenCard, flattenCard, flatten_unflattenList]

theorem flatten_unflattenCards (k : Nat) :
    ∀ cards (h : isValidFlatCards cards k), (unflattenCards k cards h).map flattenCard = cards
  | [], _ => rfl
  | card :: cards, h => by
      have hcard : CCCard_ofFlatType card k := h card (by simp)
      have hcards : isValidFlatCards cards k := by
        intro card' hcard'
        exact h card' (by simp [hcard'])
      simp [unflattenCards, flatten_unflattenCard, flatten_unflattenCards, hcard, hcards]

theorem flatten_unflattenFinal (k : Nat) :
    ∀ final (h : isValidFlatFinal final k), (unflattenFinal k final h).map flattenString = final
  | [], _ => rfl
  | s :: final, h => by
      have hs : list_ofFlatType k s := h s (by simp)
      have hfinal : isValidFlatFinal final k := by
        intro s' hs'
        exact h s' (by simp [hs'])
      simp [unflattenFinal, flatten_unflattenList, flatten_unflattenFinal, hs, hfinal]

theorem unflatten_flattenCard {k : Nat} (card : CCCard (Fin k)) :
    unflattenCard k (flattenCard card) (CCCard_ofFlatType_flatten card) = card := by
  cases card
  simp [unflattenCard, flattenCard, unflatten_flattenString]

theorem unflatten_flattenCards {k : Nat} :
    ∀ cards : List (CCCard (Fin k)),
      unflattenCards k (cards.map flattenCard) (by
        intro card hcard
        simp at hcard
        rcases hcard with ⟨card', hcard', rfl⟩
        exact CCCard_ofFlatType_flatten card') = cards
  | [] => rfl
  | card :: cards => by
      simp [unflattenCards, unflatten_flattenCard, unflatten_flattenCards]

theorem unflatten_flattenFinal {k : Nat} :
    ∀ final : List (List (Fin k)),
      unflattenFinal k (final.map flattenString) (isValidFlatFinal_flatten final) = final
  | [] => rfl
  | s :: final => by
      simp [unflattenFinal, unflatten_flattenString, unflatten_flattenFinal]

theorem flatten_unflattenCC (C : FlatCC) (h : isValidFlattening C) :
    flattenCC (unflattenCC C h) = C := by
  cases C with
  | mk Sigma offset width init cards final steps =>
      simp [unflattenCC, flattenCC, flatten_unflattenList, flatten_unflattenCards]
      exact flatten_unflattenFinal Sigma final h.2.1

theorem unflatten_flattenCC (C : CC) :
    unflattenCC (flattenCC C) (isValidFlattening_flattenCC C) = C := by
  cases C with
  | mk Sigma offset width init cards final steps =>
      simp [unflattenCC, flattenCC, unflatten_flattenString, unflatten_flattenCards]
      exact unflatten_flattenFinal final

def FlatCCLang (C : FlatCC) : Prop :=
  FlatCC_wellformed C ∧ ∃ h : isValidFlattening C, CC.CCLang (unflattenCC C h)

def flatCCYesInstance : FlatCC where
  Sigma := 1
  offset := 1
  width := 1
  init := [0]
  cards := []
  final := [[0]]
  steps := 0

def yesCC : CC where
  Sigma := 1
  offset := 1
  width := 1
  init := [⟨0, by decide⟩]
  cards := []
  final := [[⟨0, by decide⟩]]
  steps := 0

theorem yesCC_valid : CC.CCLang yesCC := by
  refine ⟨?_, ?_⟩
  · refine ⟨by decide, by decide, ⟨1, by decide, by decide⟩, by simp [yesCC], ?_, ⟨1, by simp [yesCC]⟩⟩
    intro card hcard
    cases hcard
  · refine ⟨yesCC.init, relpower.refl _, ?_⟩
    refine ⟨yesCC.init, 0, by decide, by decide, ?_⟩
    refine ⟨[], rfl⟩

theorem flatCCYesInstance_valid : FlatCCLang flatCCYesInstance := by
  have hflat : isValidFlattening flatCCYesInstance := by
    simpa [flatCCYesInstance, yesCC, flattenCC] using isValidFlattening_flattenCC yesCC
  refine ⟨?_, ⟨hflat, ?_⟩⟩
  · simpa [flatCCYesInstance, yesCC, flattenCC, flattenString] using
      flattenCC_wellformed (C := yesCC) yesCC_valid.1
  · simpa [flatCCYesInstance, yesCC, flattenCC, unflatten_flattenCC] using yesCC_valid
