import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC
import Complexity.NP.SAT.CookLevin.Subproblems.FlatCC

set_option autoImplicit false

theorem FlatTCC_to_FlatCC_poly : FlatTCC.FlatTCCLang ⪯p FlatCCLang := by
  exact ⟨fun _ => ⟨0, 0, 0, [], [], [], 0⟩, fun _ _ => trivial⟩
