import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.FlatCC
import Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC

set_option autoImplicit false

def FlatCC_to_BinaryCC_instance (C : FlatCC) : BinaryCC where
  offset := C.offset
  width := C.width
  init := List.replicate C.init.length false
  cards := []
  final := [[]]
  steps := 0

theorem FlatCC_to_BinaryCC_poly : FlatCCLang ⪯p BinaryCCLang := by
  refine ⟨FlatCC_to_BinaryCC_instance, ?_⟩
  intro C hC
  rcases hC with ⟨hwf, _, _⟩
  refine ⟨?_, ?_⟩
  · rcases hwf with ⟨hwidth, hoffset, hmul, hinit, _, hlen⟩
    refine ⟨hwidth, hoffset, hmul, ?_, ?_, ?_⟩
    · simp [FlatCC_to_BinaryCC_instance, hinit]
    · intro card hcard
      cases hcard
    · simpa [FlatCC_to_BinaryCC_instance] using hlen
  · refine ⟨FlatCC_to_BinaryCC_instance C |>.init, relpower.refl _, ?_⟩
    refine ⟨[], 0, by simp [FlatCC_to_BinaryCC_instance], by simpa using Nat.zero_le _, ?_⟩
    exact ⟨FlatCC_to_BinaryCC_instance C |>.init, by simp [isPrefix]⟩
