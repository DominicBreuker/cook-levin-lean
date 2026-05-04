import Complexity.Complexity.NP
import Complexity.Complexity.Definitions

set_option autoImplicit false

def SAT : cnf → Prop := fun _ => True

namespace SAT_inNP

theorem sat_NP : inNP SAT := by
  sorry

end SAT_inNP
