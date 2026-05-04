import Complexity.Complexity.Definitions

set_option autoImplicit false

namespace LMGenNP

def LMGenNP (X : Type) [encodable X] : X → Prop := fun _ => True

end LMGenNP

def mTMGenNP_fixed {α : Sort _} (_ : α) : Unit → Prop := fun _ => True

def TMGenNP_fixed {α : Sort _} (_ : α) : Unit → Prop := fun _ => True

namespace M

def M : Sigma (fun _ : Unit => Unit) := ⟨(), ()⟩

end M

namespace M_multi2mono

def M__mono {α : Sort _} (_ : α) : Sigma (fun _ : Unit => Unit) := ⟨(), ()⟩

end M_multi2mono
