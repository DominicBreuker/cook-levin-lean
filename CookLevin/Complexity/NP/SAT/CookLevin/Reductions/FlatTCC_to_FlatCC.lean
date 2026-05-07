import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC
import Complexity.NP.SAT.CookLevin.Subproblems.FlatCC
import Mathlib.Tactic

set_option autoImplicit false

open Classical

def TCCCard_to_CCCard {k : Nat} (card : TCCCard (Fin k)) : CCCard (Fin k) where
  prem := card.prem
  conc := card.conc

def TCC_to_CC (C : TCC) : CC where
  Sigma := C.Sigma
  offset := 1
  width := 3
  init := C.init
  cards := C.cards.map TCCCard_to_CCCard
  final := C.final
  steps := C.steps

theorem TCCCard_to_CCCard_size {k : Nat} (card : TCCCard (Fin k)) :
    CC.CCCard_of_size (TCCCard_to_CCCard card) 3 := by
  simp [TCCCard_to_CCCard, CC.CCCard_of_size, TCCCardP.toList]

theorem TCC_validStep_to_CC_validStep {k : Nat} (cards : List (TCCCard (Fin k))) (a b : List (Fin k)) :
    TCC.validStep cards a b →
      CC.validStep 1 3 (cards.map TCCCard_to_CCCard) a b := by
  rintro ⟨hlen, hsteps⟩
  refine ⟨hlen, ?_⟩
  intro step hstep
  have hstep' : step + 3 ≤ a.length := by simpa using hstep
  rcases hsteps step hstep' with ⟨card, hcard, hcover⟩
  refine ⟨TCCCard_to_CCCard card, List.mem_map.mpr ⟨card, hcard, rfl⟩, ?_⟩
  simpa [TCC.coversHead, CC.coversHead, TCCCard_to_CCCard] using hcover

theorem TCC_relpower_to_CC_relpower {k : Nat} (cards : List (TCCCard (Fin k))) :
    ∀ {n a b}, relpower (TCC.validStep cards) n a b →
      relpower (CC.validStep 1 3 (cards.map TCCCard_to_CCCard)) n a b
  | _, _, _, .refl a => relpower.refl a
  | _, _, _, .step hstep hrest =>
      relpower.step (TCC_validStep_to_CC_validStep cards _ _ hstep)
        (TCC_relpower_to_CC_relpower cards hrest)

theorem CC_validStep_to_TCC_validStep {k : Nat} (cards : List (TCCCard (Fin k))) (a b : List (Fin k)) :
    CC.validStep 1 3 (cards.map TCCCard_to_CCCard) a b →
      TCC.validStep cards a b := by
  rintro ⟨hlen, hsteps⟩
  refine ⟨hlen, ?_⟩
  intro step hstep
  have hstep' : step * 1 + 3 ≤ a.length := by simpa using hstep
  rcases hsteps step hstep' with ⟨card, hcard, hcover⟩
  rcases List.mem_map.mp hcard with ⟨card', hcard', rfl⟩
  refine ⟨card', hcard', ?_⟩
  simpa [TCC.coversHead, CC.coversHead, TCCCard_to_CCCard] using hcover

theorem CC_relpower_to_TCC_relpower {k : Nat} (cards : List (TCCCard (Fin k))) :
    ∀ {n a b}, relpower (CC.validStep 1 3 (cards.map TCCCard_to_CCCard)) n a b →
      relpower (TCC.validStep cards) n a b
  | _, _, _, .refl a => relpower.refl a
  | _, _, _, .step hstep hrest =>
      relpower.step (CC_validStep_to_TCC_validStep cards _ _ hstep)
        (CC_relpower_to_TCC_relpower cards hrest)

theorem TCC_relpower_length {k : Nat} (cards : List (TCCCard (Fin k))) :
    ∀ {n a b}, relpower (TCC.validStep cards) n a b → a.length = b.length
  | _, _, _, .refl _ => rfl
  | _, _, _, .step hstep hrest => hstep.1.trans (TCC_relpower_length cards hrest)

theorem TCC_satFinal_to_CC_satFinal {k : Nat} (final : List (List (Fin k))) (s : List (Fin k)) (l : Nat) :
    TCC.satFinal final s → s.length = l → CC.satFinal 1 l final s := by
  rintro ⟨subs, hsubs, left, right, hs⟩ hlen
  refine ⟨subs, left.length, hsubs, ?_, ?_⟩
  · rw [← hlen, hs]
    simp
  · refine ⟨right, ?_⟩
    rw [hs]
    simp [isPrefix]

theorem CC_satFinal_to_TCC_satFinal {k : Nat} (final : List (List (Fin k))) (s : List (Fin k)) (l : Nat) :
    CC.satFinal 1 l final s → s.length = l → TCC.satFinal final s := by
  rintro ⟨subs, step, hsubs, _, hprefix⟩ hlen
  rcases hprefix with ⟨rest, hrest⟩
  refine ⟨subs, hsubs, List.take step s, rest, ?_⟩
  calc
    s = List.take step s ++ List.drop step s := by
      symm
      exact List.take_append_drop step s
    _ = List.take step s ++ (subs ++ rest) := by
      simpa using congrArg (fun t => List.take step s ++ t) hrest
    _ = List.take step s ++ subs ++ rest := by
      simp [List.append_assoc]

theorem TCC_to_CC_lang (C : TCC) : TCC.TCCLang C → CC.CCLang (TCC_to_CC C) := by
  rintro ⟨hwf, sf, hsteps, hfinal⟩
  have hw : CC.wellformed (TCC_to_CC C) := by
    have hwidth : (TCC_to_CC C).width > 0 := by simp [TCC_to_CC]
    have hoffset : (TCC_to_CC C).offset > 0 := by simp [TCC_to_CC]
    refine ⟨hwidth, hoffset, ?_, ?_, ?_, ?_⟩
    · exact ⟨3, by decide, by simp [TCC_to_CC]⟩
    · simpa [TCC_to_CC, TCC.wellformed] using hwf
    · intro card hcard
      rcases List.mem_map.mp hcard with ⟨card', hcard', rfl⟩
      exact TCCCard_to_CCCard_size card'
    · exact ⟨C.init.length, by simp [TCC_to_CC]⟩
  refine ⟨hw, ⟨sf, TCC_relpower_to_CC_relpower C.cards hsteps, ?_⟩⟩
  apply TCC_satFinal_to_CC_satFinal C.final sf C.init.length hfinal
  exact (TCC_relpower_length C.cards hsteps).symm

theorem CC_to_TCC_lang (C : TCC) : CC.CCLang (TCC_to_CC C) → TCC.TCCLang C := by
  rintro ⟨hwf, sf, hsteps, hfinal⟩
  refine ⟨?_, sf, CC_relpower_to_TCC_relpower C.cards hsteps, ?_⟩
  · simpa [TCC_to_CC, TCC.wellformed] using hwf.2.2.2.1
  · apply CC_satFinal_to_TCC_satFinal C.final sf C.init.length hfinal
    exact (TCC_relpower_length C.cards (CC_relpower_to_TCC_relpower C.cards hsteps)).symm

def flatTCCCard_to_CCCard (card : TCCCard Nat) : CCCard Nat where
  prem := card.prem
  conc := card.conc

def flatTCC_to_flatCC (C : FlatTCC) : FlatCC where
  Sigma := C.Sigma
  offset := 1
  width := 3
  init := C.init
  cards := C.cards.map flatTCCCard_to_CCCard
  final := C.final
  steps := C.steps

def flatCCNoInstance : FlatCC where
  Sigma := 1
  offset := 0
  width := 0
  init := []
  cards := []
  final := []
  steps := 0

noncomputable def FlatTCC_to_FlatCC_instance (C : FlatTCC) : FlatCC :=
  if h : FlatTCC.isValidFlattening C then
    flatTCC_to_flatCC C
  else
    flatCCNoInstance

theorem flatten_unflatten_flatTCCCard_to_CCCard {k : Nat} (card : TCCCard Nat)
    (h : FlatTCC.TCCCard_ofFlatType card k) :
    flattenCard (TCCCard_to_CCCard (FlatTCC.unflattenCard k card h)) = flatTCCCard_to_CCCard card := by
  cases card with
  | mk prem conc =>
      rcases h with ⟨hprem, hconc⟩
      simp [FlatTCC.unflattenCard, FlatTCC.unflattenCardP, TCCCard_to_CCCard,
        flatTCCCard_to_CCCard, flattenCard, flattenString, TCCCardP.toList]

theorem flatten_unflatten_flatTCCCards_to_CCCards {k : Nat} :
    ∀ cards (h : FlatTCC.isValidFlatCards cards k),
      List.map (flattenCard ∘ TCCCard_to_CCCard) (FlatTCC.unflattenCards k cards h) =
        List.map flatTCCCard_to_CCCard cards
  | [], _ => rfl
  | card :: cards, h => by
      have hcard : FlatTCC.TCCCard_ofFlatType card k := h card (by simp)
      have hcards : FlatTCC.isValidFlatCards cards k := by
        intro card' hcard'
        exact h card' (by simp [hcard'])
      simp [FlatTCC.unflattenCards, hcard, hcards,
        flatten_unflatten_flatTCCCard_to_CCCard, flatten_unflatten_flatTCCCards_to_CCCards]

theorem flatTCC_to_flatCC_eq (C : FlatTCC) (h : FlatTCC.isValidFlattening C) :
    flatTCC_to_flatCC C = flattenCC (TCC_to_CC (FlatTCC.unflattenTCC C h)) := by
  cases C with
  | mk Sigma init cards final steps =>
      have hfinal :
          flattenFinal (FlatTCC.unflattenFinal Sigma final h.2.1) = final := by
        simpa [flattenFinal] using FlatTCC.flatten_unflattenFinal Sigma final h.2.1
      simp [flatTCC_to_flatCC, FlatTCC.unflattenTCC, flattenCC, TCC_to_CC,
        flatten_unflattenList, flatten_unflatten_flatTCCCards_to_CCCards, hfinal]

theorem flatCCNoInstance_not_lang : ¬ FlatCCLang flatCCNoInstance := by
  rintro ⟨hwf, _⟩
  exact Nat.lt_irrefl 0 hwf.1

theorem flatTCCCard_to_CCCard_size (card : TCCCard Nat) :
    encodable.size (flatTCCCard_to_CCCard card) ≤ encodable.size card + 4 := by
  cases card with
  | mk prem conc =>
      cases prem <;> cases conc <;> simp [flatTCCCard_to_CCCard, TCCCardP.toList, encodable.size]
      omega

theorem flatTCCCards_size_bound :
    ∀ cards : List (TCCCard Nat),
      encodable.size (cards.map flatTCCCard_to_CCCard) ≤ 5 * encodable.size cards
  | [] => by simp [encodable.size]
  | card :: cards => by
      have hcard := flatTCCCard_to_CCCard_size card
      have hcards := flatTCCCards_size_bound cards
      simp [encodable_size_list_cons] at hcards ⊢
      omega

theorem flatTCC_to_flatCC_size_bound (C : FlatTCC) :
    encodable.size (flatTCC_to_flatCC C) ≤ 5 * encodable.size C + 5 := by
  cases C with
  | mk Sigma init cards final steps =>
      have hcards := flatTCCCards_size_bound cards
      simp [flatTCC_to_flatCC, encodable.size] at hcards ⊢
      omega

theorem FlatTCC_to_FlatCC_instance_size_bound (C : FlatTCC) :
    encodable.size (FlatTCC_to_FlatCC_instance C) ≤ 5 * encodable.size C + 5 := by
  by_cases h : FlatTCC.isValidFlattening C
  · simpa [FlatTCC_to_FlatCC_instance, h] using flatTCC_to_flatCC_size_bound C
  · cases C with
    | mk Sigma init cards final steps =>
        simp [FlatTCC_to_FlatCC_instance, h, flatCCNoInstance, encodable.size]

theorem FlatTCC_to_FlatCC_poly : FlatTCC.FlatTCCLang ⪯p FlatCCLang := by
  refine ⟨⟨FlatTCC_to_FlatCC_instance, ?_, fun {inst} => ?_⟩⟩
  · refine ⟨⟨fun n => 5 * n + 5, ?_, ?_, FlatTCC_to_FlatCC_instance_size_bound⟩⟩
    · refine ⟨1, ⟨10, 1, ?_⟩⟩
      intro n hn
      have h5 : 5 ≤ 5 * n := by
        simpa using Nat.mul_le_mul_left 5 hn
      calc
        5 * n + 5 ≤ 5 * n + 5 * n := Nat.add_le_add_left h5 (5 * n)
        _ = 10 * n := by ring
        _ = 10 * n ^ 1 := by simp
    · intro x x' hxx'
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 5 hxx') 5
  · constructor
    · rintro ⟨_, hflat, hlang⟩
      have hEq := flatTCC_to_flatCC_eq inst hflat
      rw [FlatTCC_to_FlatCC_instance, dif_pos hflat, hEq]
      refine ⟨flattenCC_wellformed (C := TCC_to_CC (FlatTCC.unflattenTCC inst hflat)) (TCC_to_CC_lang _ hlang).1,
        ⟨isValidFlattening_flattenCC _, ?_⟩⟩
      simpa [unflatten_flattenCC] using TCC_to_CC_lang (FlatTCC.unflattenTCC inst hflat) hlang
    · intro hFlat
      by_cases hflat : FlatTCC.isValidFlattening inst
      · have hEq := flatTCC_to_flatCC_eq inst hflat
        rw [FlatTCC_to_FlatCC_instance, dif_pos hflat, hEq] at hFlat
        rcases hFlat with ⟨_, hccflat, hlang⟩
        refine ⟨?_, ⟨hflat, ?_⟩⟩
        · simpa [FlatTCC.flatten_unflattenTCC inst hflat] using
            FlatTCC.flattenTCC_wellformed (C := FlatTCC.unflattenTCC inst hflat)
              (CC_to_TCC_lang (FlatTCC.unflattenTCC inst hflat) (by
                simpa [unflatten_flattenCC] using hlang)).1
        · simpa using
            CC_to_TCC_lang (FlatTCC.unflattenTCC inst hflat) (by
              simpa [unflatten_flattenCC] using hlang)
      · exfalso
        have : FlatCCLang flatCCNoInstance := by simpa [FlatTCC_to_FlatCC_instance, hflat] using hFlat
        exact flatCCNoInstance_not_lang this
