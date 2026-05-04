import Complexity.Complexity.Definitions
import Complexity.NP.SAT

set_option autoImplicit false

def kCNF (_ : Nat) (_ : cnf) : Prop := True

def kSAT (k : Nat) : cnf → Prop := fun N => 0 < k ∧ kCNF k N ∧ SAT N
