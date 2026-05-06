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
      simp [unflattenList, unflattenList_length, hxs]

def mkTCCWitness (s : List Nat) (steps : Nat) (hs : list_ofFlatType 1 s) : TCC :=
  let hinit : list_ofFlatType 1 (s ++ padSymbols) := (list_ofFlatType_app).2 ⟨hs, padSymbols_valid⟩
  {
    Sigma := 1
    init := unflattenList 1 (s ++ padSymbols) hinit
    cards := []
    final := [unflattenList 1 (s ++ padSymbols) hinit]
    steps := steps
  }

theorem mkTCCWitness_valid (s : List Nat) (steps : Nat) (hs : list_ofFlatType 1 s) :
    TCC.TCCLang (mkTCCWitness s steps hs) := by
  sorry

def flatTCCNoInstance : FlatTCC where
  Sigma := 1
  init := []
  cards := []
  final := []
  steps := 0

noncomputable def FlatSingleTMGenNP_to_FlatTCC_instance :
    flatTM × List Nat × Nat × Nat → FlatTCC
  | (_, s, _, steps) =>
      if hs : list_ofFlatType 1 s then
        FlatTCC.flattenTCC (mkTCCWitness s steps hs)
      else
        flatTCCNoInstance

theorem FlatSingleTMGenNP_to_FlatTCCLang_poly : FlatSingleTMGenNP ⪯p FlatTCC.FlatTCCLang := by
  refine ⟨⟨FlatSingleTMGenNP_to_FlatTCC_instance, by sorry, fun {inst} => ?_⟩⟩
  constructor
  · intro h
    rcases inst with ⟨M, s, maxSize, steps⟩
    simp [FlatSingleTMGenNP] at h
    rcases h with ⟨_, hs, _⟩
    simp [FlatSingleTMGenNP_to_FlatTCC_instance, hs]
    refine ⟨FlatTCC.flattenTCC_wellformed (C := mkTCCWitness s steps hs) (mkTCCWitness_valid s steps hs).1,
      ⟨FlatTCC.isValidFlattening_flattenTCC _, ?_⟩⟩
    simpa [FlatTCC.unflatten_flattenTCC] using mkTCCWitness_valid s steps hs
  · intro h
    sorry
