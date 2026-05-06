import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC
import Complexity.NP.SAT.CookLevin.Subproblems.FlatCC

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
    flattenCC (TCC_to_CC (FlatTCC.unflattenTCC C h))
  else
    flatCCNoInstance

theorem FlatTCC_to_FlatCC_poly : FlatTCC.FlatTCCLang ⪯p FlatCCLang := by
  refine ⟨⟨FlatTCC_to_FlatCC_instance, trivial, ?_⟩⟩
  rintro C ⟨_, hflat, hlang⟩
  simp [FlatTCC_to_FlatCC_instance, hflat]
  refine ⟨flattenCC_wellformed (C := TCC_to_CC (FlatTCC.unflattenTCC C hflat)) (TCC_to_CC_lang _ hlang).1,
    ⟨isValidFlattening_flattenCC _, ?_⟩⟩
  simpa [unflatten_flattenCC] using TCC_to_CC_lang (FlatTCC.unflattenTCC C hflat) hlang
