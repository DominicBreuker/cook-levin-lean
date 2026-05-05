import Complexity.Complexity.NP

set_option autoImplicit false

structure GenNPInput (X__cert : Type) [encodable X__cert] where
  instance : Type
  instance_encodable : encodable instance
  rel : instance → X__cert → Prop
  rel_poly : inTimePoly (fun xc : instance × X__cert => rel xc.1 xc.2)
  input : instance

attribute [instance] GenNPInput.instance_encodable

def GenNP (X__cert : Type) [encodable X__cert] : GenNPInput X__cert → Prop :=
  fun inst => ∃ cert : X__cert, inst.rel inst.input cert

theorem genNP_iff {X__cert : Type} [encodable X__cert] (inst : GenNPInput X__cert) :
    GenNP X__cert inst ↔ ∃ cert : X__cert, inst.rel inst.input cert := by
  rfl
