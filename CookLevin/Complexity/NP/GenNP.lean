import Complexity.Complexity.NP

set_option autoImplicit false

def GenNP (X : Type) [encodable X] : X → Prop := fun _ => True
