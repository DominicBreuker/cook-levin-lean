import Complexity.Complexity.NP
import Complexity.NP.TM.IntermediateProblems
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP

set_option autoImplicit false

open Classical

def flatFunSingleTMGenNP_yesInstance : flatTM × List Nat × Nat × Nat :=
  (validFlatTM_default, [], 0, 0)

def flatFunSingleTMGenNP_noInstance : flatTM × List Nat × Nat × Nat :=
  (validFlatTM_default, [1], 0, 0)

theorem flatFunSingleTMGenNP_yesInstance_mem :
    FlatFunSingleTMGenNP flatFunSingleTMGenNP_yesInstance := by
  simpa [flatFunSingleTMGenNP_yesInstance] using flatFunSingleTMGenNP_yes

theorem flatFunSingleTMGenNP_noInstance_not_mem :
    ¬ FlatFunSingleTMGenNP flatFunSingleTMGenNP_noInstance := by
  intro h
  rcases h with ⟨_, _, hs, _⟩
  have : ofFlatType 1 1 := hs 1 (by simp [flatFunSingleTMGenNP_noInstance])
  simpa [ofFlatType] using this

noncomputable def TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP_instance
    {sig : finType} [encodable sig] (M : TM sig 1)
    (inst : TMGenNPFixedInput sig) : flatTM × List Nat × Nat × Nat :=
  if _h : TMGenNP_fixed M inst then
    flatFunSingleTMGenNP_yesInstance
  else
    flatFunSingleTMGenNP_noInstance

theorem TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP {sig : finType} [encodable sig] (M : TM sig 1) :
    TMGenNP_fixed M ⪯p FlatFunSingleTMGenNP := by
  refine ⟨⟨TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP_instance M, ?_, fun {inst} => ?_⟩⟩
  · refine ⟨⟨fun _ => encodable.size flatFunSingleTMGenNP_noInstance + 1, inOPoly_const _, ?_, ?_⟩⟩
    · intro a b hab
      simp
    · intro inst
      by_cases h : TMGenNP_fixed M inst <;>
        simp [TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP_instance, h, encodable.size,
          flatFunSingleTMGenNP_yesInstance, flatFunSingleTMGenNP_noInstance]
  · constructor
    · intro hInst
      simpa [TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP_instance, hInst] using
        flatFunSingleTMGenNP_yesInstance_mem
    · by_cases hInst : TMGenNP_fixed M inst
      · simp [TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP_instance, hInst]
      · intro hFlat
        have : FlatFunSingleTMGenNP flatFunSingleTMGenNP_noInstance := by
          simpa [TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP_instance, hInst] using hFlat
        exact False.elim (flatFunSingleTMGenNP_noInstance_not_mem this)
