import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.FlatCC
import Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC
import Mathlib.Tactic

set_option autoImplicit false

open Classical

def encodeSymbol {k : Nat} (x : Fin k) : List Bool :=
  List.replicate x.1 false ++ [true] ++ List.replicate (k - x.1 - 1) false

def encodeString {k : Nat} : List (Fin k) → List Bool
  | [] => []
  | x :: xs => encodeSymbol x ++ encodeString xs

def encodeCard {k : Nat} (card : CCCard (Fin k)) : CCCard Bool where
  prem := encodeString card.prem
  conc := encodeString card.conc

def encodeFinal {k : Nat} : List (List (Fin k)) → List (List Bool)
  | [] => []
  | s :: ss => encodeString s :: encodeFinal ss

theorem encodeFinal_eq_map {k : Nat} (final : List (List (Fin k))) :
    encodeFinal final = final.map encodeString := by
  induction final with
  | nil => rfl
  | cons s ss ih => simp [encodeFinal, ih]

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
  omega

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

theorem encodeSymbol_idxOf_true {k : Nat} (x : Fin k) :
    (encodeSymbol x).idxOf true = x.1 := by
  have hfalse : true ∉ List.replicate x.1 false := by
    simp
  rw [encodeSymbol, List.append_assoc]
  rw [List.idxOf_append_of_notMem (l₂ := [true] ++ List.replicate (k - x.1 - 1) false) hfalse]
  simp

def decodeBlock (k : Nat) (hk : 0 < k) (bs : List Bool) : Fin k :=
  ⟨min (bs.idxOf true) (k - 1), by
    have hk' : k - 1 < k := Nat.pred_lt hk.ne'
    exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hk'⟩

def decodeStringN (k : Nat) (hk : 0 < k) : Nat → List Bool → List (Fin k)
  | 0, _ => []
  | n + 1, bs => decodeBlock k hk (bs.take k) :: decodeStringN k hk n (bs.drop k)

theorem decodeBlock_encodeSymbol {k : Nat} (hk : 0 < k) (x : Fin k) :
    decodeBlock k hk (encodeSymbol x) = x := by
  apply Fin.ext
  change min (List.idxOf true (encodeSymbol x)) (k - 1) = x.1
  rw [encodeSymbol_idxOf_true]
  exact Nat.min_eq_left (Nat.le_pred_of_lt x.2)

theorem decodeStringN_length {k : Nat} (hk : 0 < k) :
    ∀ n (bs : List Bool), (decodeStringN k hk n bs).length = n
  | 0, _ => rfl
  | n + 1, bs => by simp [decodeStringN, decodeStringN_length]

theorem decodeStringN_append {k : Nat} (hk : 0 < k) :
    ∀ xs n rest,
      decodeStringN k hk (xs.length + n) (encodeString xs ++ rest) =
        xs ++ decodeStringN k hk n rest
  | [], n, rest => by simp [encodeString, decodeStringN]
  | x :: xs, n, rest => by
      rw [show (x :: xs).length + n = (xs.length + n) + 1 by
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]]
      rw [encodeString]
      simp [decodeStringN]
      rw [List.take_append_of_le_length (by simpa [encodeSymbol_length x] using (le_rfl : k ≤ k))]
      rw [List.drop_append_of_le_length (by simpa [encodeSymbol_length x] using (le_rfl : k ≤ k))]
      have htake : List.take k (encodeSymbol x) = encodeSymbol x := by
        simpa [encodeSymbol_length x] using List.take_all_of_le (show (encodeSymbol x).length ≤ k by simpa [encodeSymbol_length x])
      have hdrop : List.drop k (encodeSymbol x) = [] := by
        simpa [encodeSymbol_length x] using List.drop_eq_nil_of_le (show (encodeSymbol x).length ≤ k by simpa [encodeSymbol_length x])
      simp [htake, hdrop, decodeBlock_encodeSymbol, decodeStringN_append, encodeSymbol_length]

theorem decodeStringN_encodeString {k : Nat} (hk : 0 < k) (xs : List (Fin k)) :
    decodeStringN k hk xs.length (encodeString xs) = xs := by
  simpa [decodeStringN] using decodeStringN_append hk xs 0 []

theorem decodeStringN_drop_blocks {k : Nat} (hk : 0 < k) :
    ∀ m n (bs : List Bool),
      List.drop m (decodeStringN k hk (m + n) bs) =
        decodeStringN k hk n (List.drop (m * k) bs)
  | 0, n, bs => by simp [decodeStringN]
  | m + 1, n, bs => by
      rw [show (m + 1) + n = (m + n) + 1 by omega]
      simp [decodeStringN]
      rw [decodeStringN_drop_blocks hk m n (List.drop k bs)]
      rw [List.drop_drop]
      simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem prefix_length_le {α : Type} {xs ys : List α} :
    isPrefix xs ys → xs.length ≤ ys.length := by
  rintro ⟨rest, rfl⟩
  simp

theorem encodeString_prefix_decoded {k : Nat} (hk : 0 < k) {xs : List (Fin k)} {ys : List Bool}
    {n : Nat} :
    isPrefix (encodeString xs) ys → xs.length ≤ n → isPrefix xs (decodeStringN k hk n ys) := by
  rintro ⟨rest, rfl⟩ hlen
  refine ⟨decodeStringN k hk (n - xs.length) rest, ?_⟩
  rw [show n = xs.length + (n - xs.length) by omega]
  simpa using decodeStringN_append hk xs (n - xs.length) rest

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

theorem Binary_relpower_length {offset width : Nat} (cards : List (CCCard Bool)) :
    ∀ {n a b}, relpower (validStep offset width cards) n a b → a.length = b.length
  | _, _, _, .refl _ => rfl
  | _, _, _, .step hstep hrest => hstep.1.trans (Binary_relpower_length cards hrest)

theorem Binary_validStep_to_CC_validStep {k offset width n : Nat}
    (cards : List (CCCard (Fin k))) (hk : 0 < k) {aBits bBits : List Bool}
    (hlenA : aBits.length = k * n) :
    validStep (k * offset) (k * width) (cards.map encodeCard) aBits bBits →
      CC.validStep offset width cards
        (decodeStringN k hk n aBits) (decodeStringN k hk n bBits) := by
  rintro ⟨hlenBits, hstep⟩
  have hlenB : bBits.length = k * n := by
    rw [← hlenBits, hlenA]
  refine ⟨by simp [decodeStringN_length], ?_⟩
  intro step hstepPlain
  have hstepPlainN : step * offset + width ≤ n := by
    simpa [decodeStringN_length] using hstepPlain
  have hstepBits : step * (k * offset) + k * width ≤ aBits.length := by
    calc
      step * (k * offset) + k * width = k * (step * offset + width) := by ring
      _ ≤ k * n := Nat.mul_le_mul_left _ hstepPlainN
      _ = aBits.length := hlenA.symm
  rcases hstep step hstepBits with ⟨card, hcard, hprefixBits⟩
  rcases List.mem_map.mp hcard with ⟨card', hcard', rfl⟩
  rcases hprefixBits with ⟨hpremBits, hconcBits⟩
  refine ⟨card', hcard', ?_⟩
  constructor
  · have hstepLe : step * offset ≤ n := Nat.le_trans (Nat.le_add_right _ _) hstepPlainN
    have hdropA :
        List.drop (step * offset) (decodeStringN k hk n aBits) =
          decodeStringN k hk (n - step * offset) (List.drop (step * (k * offset)) aBits) := by
      rw [show n = step * offset + (n - step * offset) by omega]
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        decodeStringN_drop_blocks hk (step * offset) (n - step * offset) aBits
    have hdropLenA :
        (List.drop (step * (k * offset)) aBits).length = k * (n - step * offset) := by
      calc
        (List.drop (step * (k * offset)) aBits).length = aBits.length - step * (k * offset) := by
          simp [List.length_drop]
        _ = k * n - k * (step * offset) := by
          rw [hlenA]
          ac_rfl
        _ = k * (n - step * offset) := by
          rw [Nat.mul_sub_left_distrib]
    have hlenPremBits :
        k * card'.prem.length ≤ (List.drop (step * (k * offset)) aBits).length := by
      calc
        k * card'.prem.length = (encodeString card'.prem).length := by simp [encodeString_length]
        _ ≤ (List.drop (step * (k * offset)) aBits).length := prefix_length_le hpremBits
    have hlenPrem : card'.prem.length ≤ n - step * offset := by
      rw [hdropLenA] at hlenPremBits
      exact Nat.le_of_mul_le_mul_left hlenPremBits hk
    have hprem :
        isPrefix card'.prem
          (decodeStringN k hk (n - step * offset) (List.drop (step * (k * offset)) aBits)) :=
      encodeString_prefix_decoded hk hpremBits hlenPrem
    simpa [hdropA] using hprem
  · have hstepLe : step * offset ≤ n := Nat.le_trans (Nat.le_add_right _ _) hstepPlainN
    have hdropB :
        List.drop (step * offset) (decodeStringN k hk n bBits) =
          decodeStringN k hk (n - step * offset) (List.drop (step * (k * offset)) bBits) := by
      rw [show n = step * offset + (n - step * offset) by omega]
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        decodeStringN_drop_blocks hk (step * offset) (n - step * offset) bBits
    have hdropLenB :
        (List.drop (step * (k * offset)) bBits).length = k * (n - step * offset) := by
      calc
        (List.drop (step * (k * offset)) bBits).length = bBits.length - step * (k * offset) := by
          simp [List.length_drop]
        _ = k * n - k * (step * offset) := by
          rw [hlenB]
          ac_rfl
        _ = k * (n - step * offset) := by
          rw [Nat.mul_sub_left_distrib]
    have hlenConcBits :
        k * card'.conc.length ≤ (List.drop (step * (k * offset)) bBits).length := by
      calc
        k * card'.conc.length = (encodeString card'.conc).length := by simp [encodeString_length]
        _ ≤ (List.drop (step * (k * offset)) bBits).length := prefix_length_le hconcBits
    have hlenConc : card'.conc.length ≤ n - step * offset := by
      rw [hdropLenB] at hlenConcBits
      exact Nat.le_of_mul_le_mul_left hlenConcBits hk
    have hconc :
        isPrefix card'.conc
          (decodeStringN k hk (n - step * offset) (List.drop (step * (k * offset)) bBits)) :=
      encodeString_prefix_decoded hk hconcBits hlenConc
    simpa [hdropB] using hconc

theorem Binary_relpower_to_CC_relpower {k offset width n : Nat}
    (cards : List (CCCard (Fin k))) (hk : 0 < k) :
    ∀ {steps aBits bBits},
      aBits.length = k * n →
      relpower (validStep (k * offset) (k * width) (cards.map encodeCard)) steps aBits bBits →
        relpower (CC.validStep offset width cards)
          steps (decodeStringN k hk n aBits) (decodeStringN k hk n bBits)
  := by
  intro steps aBits bBits hlenA hrel
  induction hrel generalizing n with
  | refl a =>
      exact relpower.refl _
  | @step m a b c hstep hrest ih =>
      have hccStep := Binary_validStep_to_CC_validStep cards hk hlenA hstep
      have hlenMid : b.length = k * n := by
        rw [← hstep.1, hlenA]
      exact relpower.step hccStep (ih hlenMid)

theorem Binary_satFinal_to_CC_satFinal {k offset l : Nat}
    (final : List (List (Fin k))) (hk : 0 < k) {sBits : List Bool}
    (hlen : sBits.length = k * l) :
    satFinal (k * offset) (k * l) (encodeFinal final) sBits →
      CC.satFinal offset l final (decodeStringN k hk l sBits) := by
  rintro ⟨subsBits, step, hsubsBits, hleBits, hprefixBits⟩
  have hsubsMap : subsBits ∈ final.map encodeString := by simpa [encodeFinal_eq_map] using hsubsBits
  rcases List.mem_map.mp hsubsMap with ⟨subs, hsubs, rfl⟩
  have hstepLe : step * offset ≤ l := by
    have hkMul : k * (step * offset) ≤ k * l := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hleBits
    exact Nat.le_of_mul_le_mul_left hkMul hk
  have hdrop :
      List.drop (step * offset) (decodeStringN k hk l sBits) =
        decodeStringN k hk (l - step * offset) (List.drop (step * (k * offset)) sBits) := by
    rw [show l = step * offset + (l - step * offset) by omega]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      decodeStringN_drop_blocks hk (step * offset) (l - step * offset) sBits
  have hdropLen :
      (List.drop (step * (k * offset)) sBits).length = k * (l - step * offset) := by
    calc
      (List.drop (step * (k * offset)) sBits).length = sBits.length - step * (k * offset) := by
        simp [List.length_drop]
      _ = k * l - k * (step * offset) := by
        rw [hlen]
        ac_rfl
      _ = k * (l - step * offset) := by
        rw [Nat.mul_sub_left_distrib]
  have hlenSubsBits :
      k * subs.length ≤ (List.drop (step * (k * offset)) sBits).length := by
    calc
      k * subs.length = (encodeString subs).length := by simp [encodeString_length]
      _ ≤ (List.drop (step * (k * offset)) sBits).length := prefix_length_le hprefixBits
  have hlenSubs : subs.length ≤ l - step * offset := by
    rw [hdropLen] at hlenSubsBits
    exact Nat.le_of_mul_le_mul_left hlenSubsBits hk
  have hprefix :
      isPrefix subs
        (decodeStringN k hk (l - step * offset) (List.drop (step * (k * offset)) sBits)) :=
    encodeString_prefix_decoded hk hprefixBits hlenSubs
  exact ⟨subs, step, hsubs, hstepLe, by simpa [hdrop] using hprefix⟩

theorem Binary_to_CC_wellformed (C : CC) :
    BinaryCC_wellformed (CC_to_BinaryCC C) → CC.wellformed C := by
  rintro ⟨hwidthB, hoffsetB, hmulB, hinitB, hcardsB, hlenB⟩
  have hk : 0 < C.Sigma := by
    have : 0 < C.Sigma * C.offset := by simpa [CC_to_BinaryCC] using hoffsetB
    exact Nat.pos_of_ne_zero (by
      intro hSigma
      simp [hSigma] at this)
  have hwidth : 0 < C.width := by
    have : 0 < C.Sigma * C.width := by simpa [CC_to_BinaryCC] using hwidthB
    exact Nat.pos_of_ne_zero (by
      intro hWidthZero
      simp [hWidthZero] at this)
  have hoffset : 0 < C.offset := by
    have : 0 < C.Sigma * C.offset := by simpa [CC_to_BinaryCC] using hoffsetB
    exact Nat.pos_of_ne_zero (by
      intro hOffsetZero
      simp [hOffsetZero] at this)
  refine ⟨hwidth, hoffset, ?_, ?_, ?_, ?_⟩
  · rcases hmulB with ⟨t, htpos, ht⟩
    refine ⟨t, htpos, ?_⟩
    have hEq : C.Sigma * C.width = C.Sigma * (t * C.offset) := by
      calc
        C.Sigma * C.width = t * (C.Sigma * C.offset) := by simpa [CC_to_BinaryCC] using ht
        _ = C.Sigma * (t * C.offset) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hk hEq
  · have : C.Sigma * C.width ≤ C.Sigma * C.init.length := by
      simpa [CC_to_BinaryCC, encodeString_length, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hinitB
    exact Nat.le_of_mul_le_mul_left this hk
  · intro card hcard
    have hcardEnc := hcardsB (encodeCard card) (List.mem_map.mpr ⟨card, hcard, rfl⟩)
    constructor
    · have : C.Sigma * card.prem.length = C.Sigma * C.width := by
        simpa [CC_to_BinaryCC, encodeCard, encodeString_length] using hcardEnc.1
      exact Nat.eq_of_mul_eq_mul_left hk this
    · have : C.Sigma * card.conc.length = C.Sigma * C.width := by
        simpa [CC_to_BinaryCC, encodeCard, encodeString_length] using hcardEnc.2
      exact Nat.eq_of_mul_eq_mul_left hk this
  · rcases hlenB with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hEq : C.Sigma * C.init.length = C.Sigma * (t * C.offset) := by
      calc
        C.Sigma * C.init.length = t * (C.Sigma * C.offset) := by
          simpa [CC_to_BinaryCC, encodeString_length, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ht
        _ = C.Sigma * (t * C.offset) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hk hEq

theorem BinaryCC_to_CC_lang (C : CC) : BinaryCCLang (CC_to_BinaryCC C) → CC.CCLang C := by
  rintro ⟨hwfB, sfBits, hstepsBits, hfinalBits⟩
  have hwf : CC.wellformed C := Binary_to_CC_wellformed C hwfB
  have hk : 0 < C.Sigma := sigma_pos_of_cc_wf hwf
  refine ⟨hwf, ⟨decodeStringN C.Sigma hk C.init.length sfBits, ?_, ?_⟩⟩
  · have hrel :=
      Binary_relpower_to_CC_relpower C.cards hk
        (n := C.init.length) (aBits := encodeString C.init) (bBits := sfBits)
        (by simp [encodeString_length]) hstepsBits
    simpa [decodeStringN_encodeString] using hrel
  · have hsfLen : sfBits.length = C.Sigma * C.init.length := by
      rw [← Binary_relpower_length ((CC_to_BinaryCC C).cards) hstepsBits]
      simp [CC_to_BinaryCC, encodeString_length]
    have hfinalEnc :
        satFinal (C.Sigma * C.offset) (C.Sigma * C.init.length) (encodeFinal C.final) sfBits := by
      simpa [CC_to_BinaryCC, encodeString_length] using hfinalBits
    simpa using Binary_satFinal_to_CC_satFinal C.final hk hsfLen hfinalEnc

theorem list_length_le_size {α : Type} [encodable α] :
    ∀ xs : List α, xs.length ≤ encodable.size xs
  | [] => by simp [encodable.size]
  | x :: xs => by
      calc
        (x :: xs).length = xs.length + 1 := by simp
        _ ≤ encodable.size xs + 1 := by
          gcongr
          exact list_length_le_size xs
        _ ≤ encodable.size x + 1 + encodable.size xs := by omega
        _ = encodable.size (x :: xs) := by
          simp [encodable_size_list_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem bool_list_size_le_twice_length :
    ∀ bs : List Bool, encodable.size bs ≤ 2 * bs.length
  | [] => by simp [encodable.size]
  | b :: bs => by
      cases b
      · calc
          encodable.size (false :: bs) = 1 + encodable.size bs := by
            rw [encodable_size_list_cons]
            simp [encodable.size]
          _ ≤ 1 + 2 * bs.length := by gcongr; exact bool_list_size_le_twice_length bs
          _ ≤ 2 * (List.length (false :: bs)) := by
            simpa using (show 1 + 2 * bs.length ≤ 2 * (bs.length + 1) by omega)
      · calc
          encodable.size (true :: bs) = 2 + encodable.size bs := by
            rw [encodable_size_list_cons]
            simp [encodable.size]
          _ ≤ 2 + 2 * bs.length := by gcongr; exact bool_list_size_le_twice_length bs
          _ = 2 * (List.length (true :: bs)) := by
            simp
            omega

theorem encodeString_size_bound {k : Nat} (xs : List (Fin k)) :
    encodable.size (encodeString xs) ≤ (2 * k + 2) * encodable.size xs := by
  calc
    encodable.size (encodeString xs) ≤ 2 * (encodeString xs).length := bool_list_size_le_twice_length _
    _ = 2 * (k * xs.length) := by rw [encodeString_length]
    _ ≤ 2 * (k * encodable.size xs) := by
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left k (list_length_le_size xs))
    _ = (2 * k) * encodable.size xs := by ring
    _ ≤ (2 * k + 2) * encodable.size xs := by
      exact Nat.mul_le_mul_right _ (by omega)

theorem encodeCard_size_bound {k : Nat} (card : CCCard (Fin k)) :
    encodable.size (encodeCard card) ≤ (2 * k + 2) * encodable.size card := by
  have hp := encodeString_size_bound (k := k) card.prem
  have hc := encodeString_size_bound (k := k) card.conc
  have hcoeff : 1 ≤ 2 * k + 2 := by omega
  calc
    encodable.size (encodeCard card) =
        encodable.size (encodeString card.prem) + encodable.size (encodeString card.conc) + 1 := by
          simp [encodeCard, encodable.size]
    _ ≤ (2 * k + 2) * encodable.size card.prem + (2 * k + 2) * encodable.size card.conc + 1 := by
          omega
    _ ≤ (2 * k + 2) * encodable.size card.prem + (2 * k + 2) * encodable.size card.conc + (2 * k + 2) := by
          omega
    _ = (2 * k + 2) * (encodable.size card.prem + encodable.size card.conc + 1) := by ring
    _ = (2 * k + 2) * encodable.size card := by
          simp [encodable.size]

theorem encodeCards_size_bound {k : Nat} :
    ∀ cards : List (CCCard (Fin k)),
      encodable.size (cards.map encodeCard) ≤ (2 * k + 2) * encodable.size cards
  | [] => by simp [encodable.size]
  | card :: cards => by
      have hcard := encodeCard_size_bound (k := k) card
      have hcards := encodeCards_size_bound cards
      have hcoeff : 1 ≤ 2 * k + 2 := by omega
      calc
        encodable.size ((card :: cards).map encodeCard) =
            encodable.size (encodeCard card) + 1 + encodable.size (cards.map encodeCard) := by
              simp [encodable_size_list_cons]
        _ ≤ (2 * k + 2) * encodable.size card + 1 + (2 * k + 2) * encodable.size cards := by
              omega
        _ ≤ (2 * k + 2) * encodable.size card + (2 * k + 2) + (2 * k + 2) * encodable.size cards := by
              omega
        _ = (2 * k + 2) * (encodable.size card + 1 + encodable.size cards) := by ring
        _ = (2 * k + 2) * encodable.size (card :: cards) := by
              rw [encodable_size_list_cons]

theorem encodeFinal_size_bound {k : Nat} :
    ∀ final : List (List (Fin k)),
      encodable.size (encodeFinal final) ≤ (2 * k + 2) * encodable.size final
  | [] => by simp [encodeFinal, encodable.size]
  | s :: final => by
      have hs := encodeString_size_bound (k := k) s
      have hfinal := encodeFinal_size_bound final
      have hcoeff : 1 ≤ 2 * k + 2 := by omega
      calc
        encodable.size (encodeFinal (s :: final)) =
            encodable.size (encodeString s) + 1 + encodable.size (encodeFinal final) := by
              simp [encodeFinal, encodable_size_list_cons]
        _ ≤ (2 * k + 2) * encodable.size s + 1 + (2 * k + 2) * encodable.size final := by
              omega
        _ ≤ (2 * k + 2) * encodable.size s + (2 * k + 2) + (2 * k + 2) * encodable.size final := by
              omega
        _ = (2 * k + 2) * (encodable.size s + 1 + encodable.size final) := by ring
        _ = (2 * k + 2) * encodable.size (s :: final) := by
              rw [encodable_size_list_cons]

theorem unflattenList_size {k : Nat} :
    ∀ xs (h : list_ofFlatType k xs), encodable.size (unflattenList k xs h) = encodable.size xs
  | [], _ => rfl
  | x :: xs, h => by
      have hxs : list_ofFlatType k xs := by
        intro y hy
        exact h y (by simp [hy])
      calc
        encodable.size (unflattenList k (x :: xs) h) =
            encodable.size (show Fin k from ⟨x, h x (by simp)⟩) + 1 +
              encodable.size (unflattenList k xs hxs) := by
              rw [unflattenList, encodable_size_list_cons]
        _ = x + 1 + encodable.size xs := by
              rw [unflattenList_size xs hxs]
              simp [encodable.size]
        _ = encodable.size (x :: xs) := by
              rw [encodable_size_list_cons]
              simp [encodable.size]

theorem unflattenCard_size {k : Nat} (card : CCCard Nat) (h : CCCard_ofFlatType card k) :
    encodable.size (unflattenCard k card h) = encodable.size card := by
  cases card with
  | mk prem conc =>
      rcases h with ⟨hp, hc⟩
      change encodable.size (unflattenList k prem hp) + encodable.size (unflattenList k conc hc) + 1 =
        encodable.size prem + encodable.size conc + 1
      rw [unflattenList_size prem hp, unflattenList_size conc hc]

theorem unflattenCards_size {k : Nat} :
    ∀ cards (h : isValidFlatCards cards k), encodable.size (unflattenCards k cards h) = encodable.size cards
  | [], _ => rfl
  | card :: cards, h => by
      have hcard : CCCard_ofFlatType card k := h card (by simp)
      have hcards : isValidFlatCards cards k := by
        intro card' hcard'
        exact h card' (by simp [hcard'])
      simp [unflattenCards, encodable_size_list_cons, unflattenCard_size, unflattenCards_size, hcard, hcards]

theorem unflattenFinal_size {k : Nat} :
    ∀ final (h : isValidFlatFinal final k), encodable.size (unflattenFinal k final h) = encodable.size final
  | [], _ => rfl
  | s :: final, h => by
      have hs : list_ofFlatType k s := h s (by simp)
      have hfinal : isValidFlatFinal final k := by
        intro s' hs'
        exact h s' (by simp [hs'])
      simp [unflattenFinal, encodable_size_list_cons, unflattenList_size, unflattenFinal_size, hs, hfinal]

theorem unflattenCC_size (C : FlatCC) (h : isValidFlattening C) :
    encodable.size (unflattenCC C h) = encodable.size C := by
  cases C with
  | mk Sigma offset width init cards final steps =>
      change Sigma + offset + width + encodable.size (unflattenList Sigma init h.1) +
          encodable.size (unflattenCards Sigma cards h.2.2) +
          encodable.size (unflattenFinal Sigma final h.2.1) + steps + 1 =
        Sigma + offset + width + encodable.size init + encodable.size cards + encodable.size final + steps + 1
      rw [unflattenList_size init h.1, unflattenCards_size cards h.2.2, unflattenFinal_size final h.2.1]

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

theorem binaryCCNoInstance_not_lang : ¬ BinaryCCLang binaryCCNoInstance := by
  rintro ⟨hwf, _⟩
  exact Nat.lt_irrefl 0 hwf.1

theorem CC_to_BinaryCC_size_bound (C : CC) :
    encodable.size (CC_to_BinaryCC C) ≤
      50 * encodable.size C * encodable.size C + 50 * encodable.size C + 1 := by
  let n := encodable.size C
  have hSigma : C.Sigma ≤ n := by
    simp [n, encodable.size]
    omega
  have hOffset : C.offset ≤ n := by
    simp [n, encodable.size]
    omega
  have hWidth : C.width ≤ n := by
    simp [n, encodable.size]
    omega
  have hInitSize : encodable.size C.init ≤ n := by
    simp [n, encodable.size]
    omega
  have hCardsSize : encodable.size C.cards ≤ n := by
    simp [n, encodable.size]
    omega
  have hFinalSize : encodable.size C.final ≤ n := by
    simp [n, encodable.size]
    omega
  have hSteps : C.steps ≤ n := by
    simp [n, encodable.size]
    omega
  have hInit : encodable.size (encodeString C.init) ≤
      (2 * n + 2) * n := by
    have hcoef : 2 * C.Sigma + 2 ≤ 2 * n + 2 := by omega
    calc
      encodable.size (encodeString C.init) ≤ (2 * C.Sigma + 2) * encodable.size C.init :=
        encodeString_size_bound (k := C.Sigma) C.init
      _ ≤ (2 * n + 2) * encodable.size C.init := by
        exact Nat.mul_le_mul_right _ hcoef
      _ ≤ (2 * n + 2) * n := by
        exact Nat.mul_le_mul_left _ hInitSize
  have hCards : encodable.size (C.cards.map encodeCard) ≤
      (2 * n + 2) * n := by
    have hcoef : 2 * C.Sigma + 2 ≤ 2 * n + 2 := by omega
    calc
      encodable.size (C.cards.map encodeCard) ≤ (2 * C.Sigma + 2) * encodable.size C.cards :=
        encodeCards_size_bound (k := C.Sigma) C.cards
      _ ≤ (2 * n + 2) * encodable.size C.cards := by
        exact Nat.mul_le_mul_right _ hcoef
      _ ≤ (2 * n + 2) * n := by
        exact Nat.mul_le_mul_left _ hCardsSize
  have hFinal : encodable.size (encodeFinal C.final) ≤
      (2 * n + 2) * n := by
    have hcoef : 2 * C.Sigma + 2 ≤ 2 * n + 2 := by omega
    calc
      encodable.size (encodeFinal C.final) ≤ (2 * C.Sigma + 2) * encodable.size C.final :=
        encodeFinal_size_bound (k := C.Sigma) C.final
      _ ≤ (2 * n + 2) * encodable.size C.final := by
        exact Nat.mul_le_mul_right _ hcoef
      _ ≤ (2 * n + 2) * n := by
        exact Nat.mul_le_mul_left _ hFinalSize
  have hOffsetProd : C.Sigma * C.offset ≤ n * n := by
    calc
      C.Sigma * C.offset ≤ n * C.offset := Nat.mul_le_mul_right _ hSigma
      _ ≤ n * n := Nat.mul_le_mul_left _ hOffset
  have hWidthProd : C.Sigma * C.width ≤ n * n := by
    calc
      C.Sigma * C.width ≤ n * C.width := Nat.mul_le_mul_right _ hSigma
      _ ≤ n * n := Nat.mul_le_mul_left _ hWidth
  have hn1 : 1 ≤ n := by
    simp [n, encodable.size]
  have hi : (2 * n + 2) * n ≤ 4 * n * n := by
    calc
      (2 * n + 2) * n ≤ (4 * n) * n := by
        apply Nat.mul_le_mul_right
        omega
      _ = 4 * n * n := by ring
  calc
    encodable.size (CC_to_BinaryCC C)
        ≤ C.Sigma * C.offset + C.Sigma * C.width + encodable.size (encodeString C.init) +
            encodable.size (C.cards.map encodeCard) + encodable.size (encodeFinal C.final) + C.steps + 1 := by
          simp [CC_to_BinaryCC, encodable.size]
    _ ≤ n * n + C.Sigma * C.width + encodable.size (encodeString C.init) +
            encodable.size (C.cards.map encodeCard) + encodable.size (encodeFinal C.final) + C.steps + 1 := by
          omega
    _ ≤ n * n + n * n + encodable.size (encodeString C.init) +
            encodable.size (C.cards.map encodeCard) + encodable.size (encodeFinal C.final) + C.steps + 1 := by
          omega
    _ ≤ n * n + n * n + (2 * n + 2) * n +
            encodable.size (C.cards.map encodeCard) + encodable.size (encodeFinal C.final) + C.steps + 1 := by
          gcongr
    _ ≤ n * n + n * n + (2 * n + 2) * n + (2 * n + 2) * n +
            encodable.size (encodeFinal C.final) + C.steps + 1 := by
          gcongr
    _ ≤ n * n + n * n + (2 * n + 2) * n + (2 * n + 2) * n + (2 * n + 2) * n + C.steps + 1 := by
          omega
    _ ≤ n * n + n * n + (2 * n + 2) * n + (2 * n + 2) * n + (2 * n + 2) * n + n + 1 := by
          gcongr
    _ ≤ n * n + n * n + 4 * n * n + 4 * n * n + 4 * n * n + n + 1 := by
          gcongr
    _ = 14 * n * n + n + 1 := by
          ring
    _ ≤ 50 * n * n + 50 * n + 1 := by
          have hn2 : n ≤ n * n := by
            simpa [pow_two] using Nat.mul_le_mul_left n hn1
          calc
            14 * n * n + n + 1 ≤ 14 * n * n + n * n + 1 := by
              gcongr
            _ = 15 * n * n + 1 := by ring
            _ ≤ 50 * n * n + 1 := by
              gcongr
              omega
            _ ≤ 50 * n * n + 50 * n + 1 := by
              omega
    _ = 50 * encodable.size C * encodable.size C + 50 * encodable.size C + 1 := by
          simp [n]

theorem FlatCC_to_BinaryCC_instance_size_bound (C : FlatCC) :
    encodable.size (FlatCC_to_BinaryCC_instance C) ≤
      50 * encodable.size C * encodable.size C + 50 * encodable.size C + 1 := by
  by_cases h : isValidFlattening C
  · have hsize := CC_to_BinaryCC_size_bound (unflattenCC C h)
    rw [unflattenCC_size C h] at hsize
    simpa [FlatCC_to_BinaryCC_instance, h] using hsize
  · simp [FlatCC_to_BinaryCC_instance, h, binaryCCNoInstance, encodable.size]

theorem FlatCC_to_BinaryCC_poly : FlatCCLang ⪯p BinaryCCLang := by
  refine ⟨⟨FlatCC_to_BinaryCC_instance, ?_, ?_⟩⟩
  · refine ⟨⟨fun n => 100 * n ^ 2 + 1, ?_, ?_, ?_⟩⟩
    · refine ⟨2, ⟨101, 1, ?_⟩⟩
      intro n hn
      calc
        100 * n ^ 2 + 1 ≤ 101 * n ^ 2 := by
          have hn2 : 1 ≤ n ^ 2 := by
            have : 1 ≤ n := hn
            simpa [pow_two] using Nat.mul_le_mul this this
          omega
        _ = 101 * n ^ 2 := rfl
    · intro x x' hxx'
      have hpow : x ^ 2 ≤ x' ^ 2 := by
        simpa [pow_two] using Nat.mul_le_mul hxx' hxx'
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 100 hpow) 1
    · intro x
      have hsize := FlatCC_to_BinaryCC_instance_size_bound x
      have hx1 : 1 ≤ encodable.size x := by
        cases x
        simp [encodable.size]
      calc
        encodable.size (FlatCC_to_BinaryCC_instance x) ≤
            50 * encodable.size x * encodable.size x + 50 * encodable.size x + 1 := hsize
        _ ≤ 100 * encodable.size x ^ 2 + 1 := by
          have hx2 : encodable.size x ≤ encodable.size x ^ 2 := by
            simpa [pow_two] using Nat.mul_le_mul_left (encodable.size x) hx1
          have hlin :
              50 * encodable.size x * encodable.size x + 50 * encodable.size x + 1 ≤
                50 * encodable.size x * encodable.size x + 50 * (encodable.size x ^ 2) + 1 := by
            gcongr
          calc
            50 * encodable.size x * encodable.size x + 50 * encodable.size x + 1 ≤
                50 * encodable.size x * encodable.size x + 50 * (encodable.size x ^ 2) + 1 := hlin
            _ = 100 * encodable.size x ^ 2 + 1 := by
                simp [pow_two]
                ring
  · intro C
    constructor
    · intro hFlat
      rcases hFlat with ⟨_, hflat, hlang⟩
      simpa [FlatCC_to_BinaryCC_instance, hflat] using
        CC_to_BinaryCC_lang (unflattenCC C hflat) hlang
    · intro hBC
      by_cases hflat : isValidFlattening C
      · have hcc : CC.CCLang (unflattenCC C hflat) := by
          have hbc' : BinaryCCLang (CC_to_BinaryCC (unflattenCC C hflat)) := by
            simpa [FlatCC_to_BinaryCC_instance, hflat] using hBC
          exact BinaryCC_to_CC_lang (unflattenCC C hflat) hbc'
        refine ⟨?_, ⟨hflat, hcc⟩⟩
        simpa [flatten_unflattenCC C hflat] using
          flattenCC_wellformed (C := unflattenCC C hflat) hcc.1
      · exfalso
        have : BinaryCCLang binaryCCNoInstance := by
          simpa [FlatCC_to_BinaryCC_instance, hflat] using hBC
        exact binaryCCNoInstance_not_lang this
