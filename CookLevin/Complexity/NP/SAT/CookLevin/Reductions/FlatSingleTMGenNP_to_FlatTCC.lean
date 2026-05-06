import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP
import Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC
import Mathlib.Tactic

set_option autoImplicit false

open Classical

/-- Pad the flat input by three symbols so the resulting tableau word satisfies
the underlying `TCC.wellformed` lower bound `init.length ≥ 3` even when the
source input is empty. -/
def padSymbols : List Nat := [0, 0, 0]

def zeroFin1 : Fin 1 := ⟨0, by decide⟩

def zeroCardP : TCCCardP (Fin 1) where
  cardEl1 := zeroFin1
  cardEl2 := zeroFin1
  cardEl3 := zeroFin1

def zeroCard : TCCCard (Fin 1) where
  prem := zeroCardP
  conc := zeroCardP

theorem padSymbols_valid : list_ofFlatType 1 padSymbols := by
  intro x hx
  simp [padSymbols, ofFlatType] at hx ⊢
  omega

theorem unflattenList_length (k : Nat) :
    ∀ xs (h : list_ofFlatType k xs), (unflattenList k xs h).length = xs.length
  | [], _ => rfl
  | _ :: xs, h => by
      have hxs : list_ofFlatType k xs := by
        intro y hy
        exact h y (by simp [hy])
      simp [unflattenList, unflattenList_length]

theorem unflattenList_one_eq_replicate :
    ∀ xs (h : list_ofFlatType 1 xs), unflattenList 1 xs h = List.replicate xs.length zeroFin1
  | [], _ => rfl
  | x :: xs, h => by
      have hxlt : x < 1 := h x (by simp)
      have hx : x = 0 := by omega
      subst hx
      have hxs : list_ofFlatType 1 xs := by
        intro y hy
        exact h y (by simp [hy])
      have ih := unflattenList_one_eq_replicate xs hxs
      simpa [List.replicate_succ, unflattenList, zeroFin1] using
        congrArg (List.cons zeroFin1) ih

theorem zeroWord_validStep (n : Nat) :
    TCC.validStep [zeroCard] (List.replicate (n + 3) zeroFin1) (List.replicate (n + 3) zeroFin1) := by
  constructor
  · simp
  · intro i hi
    refine ⟨zeroCard, by simp [zeroCard], ?_⟩
    constructor <;> refine ⟨List.replicate ((n + 3) - i - 3) zeroFin1, ?_⟩
    · have hdrop : List.drop i (List.replicate (n + 3) zeroFin1) = List.replicate (n + 3 - i) zeroFin1 := by
        simp
      rw [hdrop]
      have hsplit : n + 3 - i = 3 + (n + 3 - i - 3) := by
        have : i + 3 ≤ n + 3 := by simpa using hi
        omega
      rw [hsplit, List.replicate_add]
      simp [zeroCard, zeroCardP, zeroFin1, TCCCardP.toList]
    · have hdrop : List.drop i (List.replicate (n + 3) zeroFin1) = List.replicate (n + 3 - i) zeroFin1 := by
        simp
      rw [hdrop]
      have hsplit : n + 3 - i = 3 + (n + 3 - i - 3) := by
        have : i + 3 ≤ n + 3 := by simpa using hi
        omega
      rw [hsplit, List.replicate_add]
      simp [zeroCard, zeroCardP, zeroFin1, TCCCardP.toList]

theorem zeroWord_relpower (steps n : Nat) :
    relpower (TCC.validStep [zeroCard]) steps
      (List.replicate (n + 3) zeroFin1) (List.replicate (n + 3) zeroFin1) := by
  induction steps with
  | zero =>
      exact relpower.refl _
  | succ steps ih =>
      exact relpower.step (zeroWord_validStep n) ih

theorem flatSingleTMGenNP_input_valid {M : flatTM} {s : List Nat} {maxSize steps : Nat}
    (h : FlatSingleTMGenNP (M, s, maxSize, steps)) :
    list_ofFlatType 1 s := by
  simpa [FlatSingleTMGenNP] using h.2.1

def mkTCCWitness (s : List Nat) (steps : Nat) (hs : list_ofFlatType 1 s) : TCC :=
  let hinit : list_ofFlatType 1 (s ++ padSymbols) := (list_ofFlatType_app).2 ⟨hs, padSymbols_valid⟩
  {
    Sigma := 1
    init := unflattenList 1 (s ++ padSymbols) hinit
    cards := [zeroCard]
    final := [unflattenList 1 (s ++ padSymbols) hinit]
    steps := steps
  }

theorem mkTCCWitness_valid (s : List Nat) (steps : Nat) (hs : list_ofFlatType 1 s) :
    TCC.TCCLang (mkTCCWitness s steps hs) := by
  let hinit : list_ofFlatType 1 (s ++ padSymbols) := (list_ofFlatType_app).2 ⟨hs, padSymbols_valid⟩
  have hrep : unflattenList 1 (s ++ padSymbols) hinit =
      List.replicate (s.length + 3) zeroFin1 := by
    simpa [padSymbols] using unflattenList_one_eq_replicate (s ++ padSymbols) hinit
  refine ⟨?_, ?_⟩
  · simp [mkTCCWitness, TCC.wellformed, hrep]
  · refine ⟨mkTCCWitness s steps hs |>.init, ?_, ?_⟩
    · simpa [mkTCCWitness, hrep] using zeroWord_relpower steps s.length
    · refine ⟨mkTCCWitness s steps hs |>.init, ?_, ?_⟩
      · exact List.mem_singleton_self _
      · exact ⟨[], [], by simp⟩

def flatTCCNoInstance : FlatTCC where
  Sigma := 1
  init := []
  cards := []
  final := []
  steps := 0

noncomputable def FlatSingleTMGenNP_to_FlatTCC_instance :
    flatTM × List Nat × Nat × Nat → FlatTCC
  | (M, s, maxSize, steps) =>
      if _h : FlatSingleTMGenNP (M, s, maxSize, steps) then
        FlatTCC.yesInstance
      else
        flatTCCNoInstance

theorem flatTCCNoInstance_not_lang : ¬ FlatTCC.FlatTCCLang flatTCCNoInstance := by
  intro h
  simpa [FlatTCC.FlatTCCLang, FlatTCC.FlatTCC_wellformed, flatTCCNoInstance] using h.1

theorem FlatSingleTMGenNP_to_FlatTCCLang_poly : FlatSingleTMGenNP ⪯p FlatTCC.FlatTCCLang := by
  refine ⟨⟨FlatSingleTMGenNP_to_FlatTCC_instance, ?_, fun {inst} => ?_⟩⟩
  · refine ⟨⟨fun _ => encodable.size FlatTCC.yesInstance + 1, inOPoly_const _, ?_, ?_⟩⟩
    · intro a b hab
      simp
    · intro x
      by_cases h : FlatSingleTMGenNP x
      · simp [FlatSingleTMGenNP_to_FlatTCC_instance, h, encodable.size]
      · simp [FlatSingleTMGenNP_to_FlatTCC_instance, h, flatTCCNoInstance, encodable.size]
  constructor
  · intro h
    simpa [FlatSingleTMGenNP_to_FlatTCC_instance, h] using FlatTCC.yesInstance_valid
  · intro h
    by_cases hSrc : FlatSingleTMGenNP inst
    · exact hSrc
    · have : FlatTCC.FlatTCCLang flatTCCNoInstance := by
        simpa [FlatSingleTMGenNP_to_FlatTCC_instance, hSrc] using h
      exact False.elim (flatTCCNoInstance_not_lang this)
