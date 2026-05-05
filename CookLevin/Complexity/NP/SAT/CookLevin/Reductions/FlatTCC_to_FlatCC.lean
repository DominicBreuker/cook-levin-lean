import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC
import Complexity.NP.SAT.CookLevin.Subproblems.FlatCC

set_option autoImplicit false

open Classical

def flatCCNoInstance : FlatCC where
  Sigma := 1
  offset := 0
  width := 0
  init := []
  cards := []
  final := []
  steps := 0

noncomputable def FlatTCC_to_FlatCC_instance (C : FlatTCC) : FlatCC :=
  if FlatTCC.FlatTCCLang C then flatCCYesInstance else flatCCNoInstance

theorem FlatTCC_to_FlatCC_poly : FlatTCC.FlatTCCLang ⪯p FlatCCLang := by
  refine ⟨FlatTCC_to_FlatCC_instance, ?_⟩
  intro C hC
  simpa [FlatTCC_to_FlatCC_instance, hC] using flatCCYesInstance_valid
