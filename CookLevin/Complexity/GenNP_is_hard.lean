import Complexity.Complexity.NP
import Complexity.NP.GenNP

set_option autoImplicit false

theorem NPhard_GenNP (X__cert : Type) [encodable X__cert] : NPhard (GenNP X__cert) := by
  exact ⟨X__cert, inferInstance, reducesPolyMO_reflexive X__cert (GenNP X__cert)⟩
