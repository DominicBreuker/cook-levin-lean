import Complexity.Complexity.NP

set_option autoImplicit false

structure GenNPInput (X__cert : Type) [encodable X__cert] where
  rel : X__cert → Prop
  rel_poly : inTimePoly rel

def GenNP (X__cert : Type) [encodable X__cert] : GenNPInput X__cert → Prop :=
  fun inst => ∃ cert : X__cert, inst.rel cert

theorem genNP_iff {X__cert : Type} [encodable X__cert] (inst : GenNPInput X__cert) :
    GenNP X__cert inst ↔ ∃ cert : X__cert, inst.rel cert := by
  rfl
