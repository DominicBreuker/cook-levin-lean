import Complexity.Complexity.NP

set_option autoImplicit false

abbrev GenNP (X : Type) [encodable X] : X → Prop := NPUniversal X
