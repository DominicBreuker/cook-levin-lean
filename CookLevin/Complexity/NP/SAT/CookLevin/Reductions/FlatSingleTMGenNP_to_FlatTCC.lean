import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP
import Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC

set_option autoImplicit false

open Classical

def flatTCCNoInstance : FlatTCC where
  Sigma := 1
  init := []
  cards := []
  final := []
  steps := 0

noncomputable def FlatSingleTMGenNP_to_FlatTCC_instance (x : flatTM × List Nat × Nat × Nat) : FlatTCC :=
  if FlatSingleTMGenNP x then FlatTCC.yesInstance else flatTCCNoInstance

theorem FlatSingleTMGenNP_to_FlatTCCLang_poly : FlatSingleTMGenNP ⪯p FlatTCC.FlatTCCLang := by
  refine ⟨FlatSingleTMGenNP_to_FlatTCC_instance, ?_⟩
  intro x hx
  simpa [FlatSingleTMGenNP_to_FlatTCC_instance, hx] using FlatTCC.yesInstance_valid
