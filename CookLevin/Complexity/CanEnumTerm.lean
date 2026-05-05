import Complexity.Complexity.Definitions

set_option autoImplicit false

class CanEnumTerm (X__cert : Type) [encodable X__cert] where
  encode {Y : Type} [encodable Y] : Y → X__cert

namespace boollist_enum

@[reducible] def boollists_enum_term : CanEnumTerm (List Bool) :=
  ⟨fun {_} {_} _ => []⟩

end boollist_enum
