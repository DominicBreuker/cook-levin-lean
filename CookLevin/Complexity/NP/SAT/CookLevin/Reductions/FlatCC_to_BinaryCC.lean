import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.FlatCC
import Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC
import Mathlib.Tactic

set_option autoImplicit false

open Classical

def encodeSymbol {k : Nat} (x : Fin k) : List Bool :=
  (List.range k).map (fun idx => decide (idx = x.1))

def encodeString {k : Nat} : List (Fin k) → List Bool
  | [] => []
  | x :: xs => encodeSymbol x ++ encodeString xs

def encodeCard {k : Nat} (card : CCCard (Fin k)) : CCCard Bool where
  prem := encodeString card.prem
  conc := encodeString card.conc

def encodeFinal {k : Nat} : List (List (Fin k)) → List (List Bool)
  | [] => []
  | s :: ss => encodeString s :: encodeFinal ss

def CC_to_BinaryCC (C : CC) : BinaryCC where
  offset := C.Sigma * C.offset
  width := C.Sigma * C.width
  init := encodeString C.init
  cards := C.cards.map encodeCard
  final := encodeFinal C.final
  steps := C.steps

theorem encodeSymbol_length {k : Nat} (x : Fin k) :
    (encodeSymbol x).length = k := by
  simp [encodeSymbol]

theorem encodeString_length {k : Nat} :
    ∀ xs : List (Fin k), (encodeString xs).length = k * xs.length
  | [] => by simp [encodeString]
  | x :: xs => by
      simp [encodeString, encodeSymbol_length, encodeString_length, Nat.left_distrib, Nat.add_comm, Nat.add_left_comm]

theorem encodeString_append {k : Nat} :
    ∀ xs ys : List (Fin k), encodeString (xs ++ ys) = encodeString xs ++ encodeString ys
  | [], ys => by simp [encodeString]
  | x :: xs, ys => by
      simp [encodeString, encodeString_append]

theorem encodeString_prefix {k : Nat} {xs ys : List (Fin k)} :
    isPrefix xs ys → isPrefix (encodeString xs) (encodeString ys) := by
  rintro ⟨rest, rfl⟩
  refine ⟨encodeString rest, ?_⟩
  simp [encodeString_append]

theorem encodeString_drop_blocks {k : Nat} :
    ∀ n (xs : List (Fin k)), List.drop (n * k) (encodeString xs) = encodeString (xs.drop n)
  | 0, xs => by simp [encodeString]
  | n + 1, [] => by simp [encodeString]
  | n + 1, x :: xs => by
    rw [Nat.succ_mul, encodeString]
    rw [List.drop_append]
    simp [encodeSymbol_length, encodeString_drop_blocks]

theorem sigma_pos_of_cc_wf {C : CC} (h : CC.wellformed C) : 0 < C.Sigma := by
  rcases h with ⟨hwidth, _, _, hinit, _, _⟩
  cases hxs : C.init with
  | nil =>
      simp [hxs] at hinit
      omega
  | cons x xs =>
      exact Nat.pos_of_ne_zero (by
        intro hSigma
        simpa [hSigma] using x.2)

theorem encodeCard_size {k : Nat} (width : Nat) (card : CCCard (Fin k)) :
    CC.CCCard_of_size card width →
      (encodeCard card).prem.length = k * width ∧ (encodeCard card).conc.length = k * width := by
  rintro ⟨hp, hc⟩
  simp [encodeCard, encodeString_length, hp, hc]

theorem CC_validStep_to_Binary_validStep {k offset width : Nat}
    (cards : List (CCCard (Fin k))) (hk : 0 < k) (a b : List (Fin k)) :
    CC.validStep offset width cards a b →
      validStep (k * offset) (k * width) (cards.map encodeCard) (encodeString a) (encodeString b) := by
  rintro ⟨hlen, hstep⟩
  refine ⟨by simp [encodeString_length, hlen], ?_⟩
  intro step hstepEnc
  have hstepPlain : step * offset + width ≤ a.length := by
    have hkstep : k * (step * offset + width) ≤ k * a.length := by
      simpa [encodeString_length, hlen, Nat.mul_assoc, Nat.left_distrib, Nat.right_distrib,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstepEnc
    exact Nat.le_of_mul_le_mul_left hkstep hk
  rcases hstep step hstepPlain with ⟨card, hcard, hprefix⟩
  refine ⟨encodeCard card, List.mem_map.mpr ⟨card, hcard, rfl⟩, ?_⟩
  rcases hprefix with ⟨hprem, hconc⟩
  constructor
  · have hdrop :
      List.drop (step * (k * offset)) (encodeString a) = encodeString (a.drop (step * offset)) := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (encodeString_drop_blocks (step * offset) a)
    rw [hdrop]
    simpa [encodeCard] using
      (encodeString_prefix (xs := card.prem) (ys := a.drop (step * offset)) hprem)
  · have hdrop :
      List.drop (step * (k * offset)) (encodeString b) = encodeString (b.drop (step * offset)) := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (encodeString_drop_blocks (step * offset) b)
    rw [hdrop]
    simpa [encodeCard] using
      (encodeString_prefix (xs := card.conc) (ys := b.drop (step * offset)) hconc)

theorem CC_relpower_to_Binary_relpower {k offset width : Nat}
    (cards : List (CCCard (Fin k))) (hk : 0 < k) :
    ∀ {n a b}, relpower (CC.validStep offset width cards) n a b →
      relpower (validStep (k * offset) (k * width) (cards.map encodeCard))
        n (encodeString a) (encodeString b)
  | _, _, _, .refl a => relpower.refl _
  | _, _, _, .step hstep hrest =>
      relpower.step (CC_validStep_to_Binary_validStep cards hk _ _ hstep)
        (CC_relpower_to_Binary_relpower cards hk hrest)

theorem CC_relpower_length {k offset width : Nat} (cards : List (CCCard (Fin k))) :
    ∀ {n a b}, relpower (CC.validStep offset width cards) n a b → a.length = b.length
  | _, _, _, .refl _ => rfl
  | _, _, _, .step hstep hrest => hstep.1.trans (CC_relpower_length cards hrest)

theorem CC_satFinal_to_Binary_satFinal {k offset l : Nat}
    (final : List (List (Fin k))) (hk : 0 < k) (s : List (Fin k)) :
    CC.satFinal offset l final s →
      satFinal (k * offset) (k * l) (encodeFinal final) (encodeString s) := by
  intro h
  rcases h with ⟨subs, step, hsubs, hle, hprefix⟩
  refine ⟨encodeString subs, step, ?_, ?_, ?_⟩
  · induction final with
    | nil => cases hsubs
    | cons s ss ih =>
        simp [encodeFinal] at hsubs ⊢
        rcases hsubs with rfl | hsubs
        · exact Or.inl rfl
        · exact Or.inr (ih hsubs)
  · simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_left k hle
  · rcases hprefix with ⟨rest, hrest⟩
    refine ⟨encodeString rest, ?_⟩
    rw [show step * (k * offset) = (step * offset) * k by ac_rfl]
    rw [encodeString_drop_blocks (step * offset) s]
    simp [hrest, encodeString_append]

theorem CC_to_BinaryCC_lang (C : CC) : CC.CCLang C → BinaryCCLang (CC_to_BinaryCC C) := by
  rintro ⟨hwf, sf, hsteps, hfinal⟩
  have hk : 0 < C.Sigma := sigma_pos_of_cc_wf hwf
  refine ⟨?_, ⟨encodeString sf, CC_relpower_to_Binary_relpower C.cards hk hsteps, ?_⟩⟩
  · rcases hwf with ⟨hwidth, hoffset, hmul, hinit, hcards, hlen⟩
    refine ⟨Nat.mul_pos hk hwidth, Nat.mul_pos hk hoffset, ?_, ?_, ?_, ?_⟩
    · rcases hmul with ⟨t, htpos, htw⟩
      refine ⟨t, htpos, ?_⟩
      calc
        C.Sigma * C.width = C.Sigma * (t * C.offset) := by simpa [htw]
        _ = t * (C.Sigma * C.offset) := by ac_rfl
    · simpa [CC_to_BinaryCC, encodeString_length, Nat.mul_assoc] using
        Nat.mul_le_mul_left C.Sigma hinit
    · intro card hcard
      rcases List.mem_map.mp hcard with ⟨card', hcard', rfl⟩
      exact encodeCard_size C.width card' (hcards card' hcard')
    · rcases hlen with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      calc
        (encodeString C.init).length = C.Sigma * C.init.length := by simp [encodeString_length]
        _ = C.Sigma * (t * C.offset) := by simpa [ht]
        _ = t * (C.Sigma * C.offset) := by ac_rfl
  · have hlen : sf.length = C.init.length := (CC_relpower_length C.cards hsteps).symm
    simpa [CC_to_BinaryCC, encodeString_length, hlen] using
      CC_satFinal_to_Binary_satFinal C.final hk sf hfinal

def binaryCCNoInstance : BinaryCC where
  offset := 0
  width := 0
  init := []
  cards := []
  final := []
  steps := 0

noncomputable def FlatCC_to_BinaryCC_instance (C : FlatCC) : BinaryCC :=
  if h : isValidFlattening C then
    CC_to_BinaryCC (unflattenCC C h)
  else
    binaryCCNoInstance

theorem FlatCC_to_BinaryCC_poly : FlatCCLang ⪯p BinaryCCLang := by
  refine ⟨⟨FlatCC_to_BinaryCC_instance, trivial, ?_⟩⟩
  intro C
  constructor
  · intro hFlat
    rcases hFlat with ⟨_, hflat, hlang⟩
    simpa [FlatCC_to_BinaryCC_instance, hflat] using
      CC_to_BinaryCC_lang (unflattenCC C hflat) hlang
  · intro hBC
    sorry
