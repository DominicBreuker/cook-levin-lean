import Complexity.Complexity.Definitions

set_option autoImplicit false

namespace TCC

def wellformed (C : TCC) : Prop :=
  C.init.length ≥ 3

def coversHead {k : Nat} (card : TCCCard (Fin k)) (a b : List (Fin k)) : Prop :=
  isPrefix (card.prem : List (Fin k)) a ∧ isPrefix (card.conc : List (Fin k)) b

def coversHeadList {k : Nat} (cards : List (TCCCard (Fin k))) (a b : List (Fin k)) : Prop :=
  ∃ card, card ∈ cards ∧ coversHead card a b

def satFinal {k : Nat} (final : List (List (Fin k))) (s : List (Fin k)) : Prop :=
  ∃ subs, subs ∈ final ∧ isSubstring subs s

def validStep {k : Nat} (cards : List (TCCCard (Fin k))) (a b : List (Fin k)) : Prop :=
  a.length = b.length ∧ ∀ i, i + 3 ≤ a.length → coversHeadList cards (a.drop i) (b.drop i)

def TCCLang (C : TCC) : Prop :=
  wellformed C ∧ ∃ sf, relpower (validStep C.cards) C.steps C.init sf ∧ satFinal C.final sf

end TCC

namespace FlatTCC

def TCCCardP_ofFlatType (cardp : TCCCardP Nat) (k : Nat) : Prop :=
  cardp.cardEl1 < k ∧ cardp.cardEl2 < k ∧ cardp.cardEl3 < k

def TCCCard_ofFlatType (card : TCCCard Nat) (k : Nat) : Prop :=
  TCCCardP_ofFlatType card.prem k ∧ TCCCardP_ofFlatType card.conc k

def isValidFlatCards (cards : List (TCCCard Nat)) (k : Nat) : Prop :=
  ∀ card, card ∈ cards → TCCCard_ofFlatType card k

def isValidFlatFinal (final : List (List Nat)) (k : Nat) : Prop :=
  ∀ s, s ∈ final → list_ofFlatType k s

def isValidFlatInitial (init : List Nat) (k : Nat) : Prop :=
  list_ofFlatType k init

def FlatTCC_wellformed (C : FlatTCC) : Prop :=
  C.init.length ≥ 3

def isValidFlattening (C : FlatTCC) : Prop :=
  isValidFlatInitial C.init C.Sigma ∧
    isValidFlatFinal C.final C.Sigma ∧
    isValidFlatCards C.cards C.Sigma

def flattenCardP {k : Nat} (card : TCCCardP (Fin k)) : TCCCardP Nat where
  cardEl1 := card.cardEl1.1
  cardEl2 := card.cardEl2.1
  cardEl3 := card.cardEl3.1

def flattenCard {k : Nat} (card : TCCCard (Fin k)) : TCCCard Nat where
  prem := flattenCardP card.prem
  conc := flattenCardP card.conc

def flattenFinal {k : Nat} (final : List (List (Fin k))) : List (List Nat) :=
  final.map flattenString

def flattenTCC (C : TCC) : FlatTCC where
  Sigma := C.Sigma
  init := flattenString C.init
  cards := C.cards.map flattenCard
  final := flattenFinal C.final
  steps := C.steps

theorem TCCCardP_ofFlatType_flatten {k : Nat} (card : TCCCardP (Fin k)) :
    TCCCardP_ofFlatType (flattenCardP card) k := by
  exact ⟨card.cardEl1.2, card.cardEl2.2, card.cardEl3.2⟩

theorem TCCCard_ofFlatType_flatten {k : Nat} (card : TCCCard (Fin k)) :
    TCCCard_ofFlatType (flattenCard card) k := by
  exact ⟨TCCCardP_ofFlatType_flatten card.prem, TCCCardP_ofFlatType_flatten card.conc⟩

theorem isValidFlatFinal_flatten {k : Nat} (final : List (List (Fin k))) :
    isValidFlatFinal (flattenFinal final) k := by
  intro s hs
  simp [flattenFinal] at hs
  rcases hs with ⟨s', hs', rfl⟩
  exact flattenString_list_ofFlatType s'

theorem isValidFlattening_flattenTCC (C : TCC) :
    isValidFlattening (flattenTCC C) := by
  refine ⟨flattenString_list_ofFlatType C.init, isValidFlatFinal_flatten C.final, ?_⟩
  intro card hcard
  simp [flattenTCC] at hcard
  rcases hcard with ⟨card', hcard', rfl⟩
  exact TCCCard_ofFlatType_flatten card'

theorem flattenTCC_wellformed {C : TCC} :
    TCC.wellformed C → FlatTCC_wellformed (flattenTCC C) := by
  simpa [TCC.wellformed, FlatTCC_wellformed, flattenTCC, flattenString]

def unflattenCardP (k : Nat) (card : TCCCardP Nat) (h : TCCCardP_ofFlatType card k) : TCCCardP (Fin k) where
  cardEl1 := ⟨card.cardEl1, h.1⟩
  cardEl2 := ⟨card.cardEl2, h.2.1⟩
  cardEl3 := ⟨card.cardEl3, h.2.2⟩

def unflattenCard (k : Nat) (card : TCCCard Nat) (h : TCCCard_ofFlatType card k) : TCCCard (Fin k) where
  prem := unflattenCardP k card.prem h.1
  conc := unflattenCardP k card.conc h.2

def unflattenCards (k : Nat) :
    (cards : List (TCCCard Nat)) → isValidFlatCards cards k → List (TCCCard (Fin k))
  | [], _ => []
  | card :: cards, h =>
      have hcard : TCCCard_ofFlatType card k := h card (by simp)
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

def unflattenTCC (C : FlatTCC) (h : isValidFlattening C) : TCC where
  Sigma := C.Sigma
  init := unflattenList C.Sigma C.init h.1
  cards := unflattenCards C.Sigma C.cards h.2.2
  final := unflattenFinal C.Sigma C.final h.2.1
  steps := C.steps

theorem flatten_unflattenCardP (k : Nat) (card : TCCCardP Nat) (h : TCCCardP_ofFlatType card k) :
    flattenCardP (unflattenCardP k card h) = card := by
  cases card
  cases h
  rfl

theorem flatten_unflattenCard (k : Nat) (card : TCCCard Nat) (h : TCCCard_ofFlatType card k) :
    flattenCard (unflattenCard k card h) = card := by
  cases card
  rcases h with ⟨hp, hc⟩
  simp [unflattenCard, flattenCard, flatten_unflattenCardP, hp, hc]

theorem flatten_unflattenCards (k : Nat) :
    ∀ cards (h : isValidFlatCards cards k), (unflattenCards k cards h).map flattenCard = cards
  | [], _ => rfl
  | card :: cards, h => by
      have hcard : TCCCard_ofFlatType card k := h card (by simp)
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

theorem unflatten_flattenCardP {k : Nat} (card : TCCCardP (Fin k)) :
    unflattenCardP k (flattenCardP card) (TCCCardP_ofFlatType_flatten card) = card := by
  cases card
  simp [unflattenCardP, flattenCardP]
  repeat constructor <;> apply Fin.ext <;> rfl

theorem unflatten_flattenCard {k : Nat} (card : TCCCard (Fin k)) :
    unflattenCard k (flattenCard card) (TCCCard_ofFlatType_flatten card) = card := by
  cases card
  simp [unflattenCard, flattenCard, unflatten_flattenCardP]

theorem unflatten_flattenCards {k : Nat} :
    ∀ cards : List (TCCCard (Fin k)),
      unflattenCards k (cards.map flattenCard) (by
        intro card hcard
        simp at hcard
        rcases hcard with ⟨card', hcard', rfl⟩
        exact TCCCard_ofFlatType_flatten card') = cards
  | [] => rfl
  | card :: cards => by
      simp [unflattenCards, unflatten_flattenCard, unflatten_flattenCards]

theorem unflatten_flattenFinal {k : Nat} :
    ∀ final : List (List (Fin k)),
      unflattenFinal k (final.map flattenString) (isValidFlatFinal_flatten final) = final
  | [] => rfl
  | s :: final => by
      simp [unflattenFinal, unflatten_flattenString, unflatten_flattenFinal]

theorem flatten_unflattenTCC (C : FlatTCC) (h : isValidFlattening C) :
    flattenTCC (unflattenTCC C h) = C := by
  cases C with
  | mk Sigma init cards final steps =>
      simp [unflattenTCC, flattenTCC, flatten_unflattenList, flatten_unflattenCards]
      exact flatten_unflattenFinal Sigma final h.2.1

theorem unflatten_flattenTCC (C : TCC) :
    unflattenTCC (flattenTCC C) (isValidFlattening_flattenTCC C) = C := by
  cases C with
  | mk Sigma init cards final steps =>
      simp [unflattenTCC, flattenTCC, unflatten_flattenString, unflatten_flattenCards]
      exact unflatten_flattenFinal final

def FlatTCCLang (C : FlatTCC) : Prop :=
  FlatTCC_wellformed C ∧ ∃ h : isValidFlattening C, TCC.TCCLang (unflattenTCC C h)

def yesInstance : FlatTCC where
  Sigma := 1
  init := [0, 0, 0]
  cards := []
  final := [[0, 0, 0]]
  steps := 0

def yesTCC : TCC where
  Sigma := 1
  init := [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]
  cards := []
  final := [[⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]]
  steps := 0

theorem yesTCC_valid : TCC.TCCLang yesTCC := by
  refine ⟨by simp [TCC.wellformed, yesTCC], ?_⟩
  refine ⟨yesTCC.init, relpower.refl _, ?_⟩
  refine ⟨yesTCC.init, by decide, ?_⟩
  refine ⟨[], [], rfl⟩

theorem yesInstance_valid : FlatTCCLang yesInstance := by
  have hflat : isValidFlattening yesInstance := by
    simpa [yesInstance, yesTCC, flattenTCC] using isValidFlattening_flattenTCC yesTCC
  refine ⟨?_, ⟨hflat, ?_⟩⟩
  · simpa [yesInstance, yesTCC, flattenTCC, flattenString] using
      flattenTCC_wellformed (C := yesTCC) yesTCC_valid.1
  · simpa [yesInstance, yesTCC, flattenTCC, unflatten_flattenTCC] using yesTCC_valid

end FlatTCC
