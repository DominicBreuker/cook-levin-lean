import Complexity.Complexity.NP

set_option autoImplicit false

structure GenNPInput (X__cert : Type) [encodable X__cert] where
  rel : X__cert → Prop
  rel_poly : inTimePoly rel
  maxSize : Nat
  steps : Nat
  rel_size : ∀ ⦃cert⦄, rel cert → encodable.size cert ≤ maxSize

/-- Real size for `GenNPInput` (Part 0.1): the data content of an instance is
its two numeric parameters, which are exactly what the downstream tableau size
depends on. The `rel` field is an abstract predicate — it is not
string-encodable data, so it contributes nothing. This makes `encodable.size`
here a size *measure*, not a full encoding; the abstract-`rel` front types are
scheduled to be replaced by concrete machines in C8, at which point instances
become genuine strings. -/
instance {X__cert : Type} [encodable X__cert] : encodable (GenNPInput X__cert) where
  size := fun inst => inst.maxSize + inst.steps + 1
  size_ge_logical := fun inst => ⟨inst.maxSize + inst.steps + 1, Nat.le_refl _⟩

@[simp]
theorem encodable_size_GenNPInput {X__cert : Type} [encodable X__cert]
    (inst : GenNPInput X__cert) :
    encodable.size inst = inst.maxSize + inst.steps + 1 := rfl

def GenNP (X__cert : Type) [encodable X__cert] : GenNPInput X__cert → Prop :=
  fun inst => ∃ cert : X__cert, encodable.size cert ≤ inst.maxSize ∧ inst.rel cert

theorem genNP_iff {X__cert : Type} [encodable X__cert] (inst : GenNPInput X__cert) :
    GenNP X__cert inst ↔ ∃ cert : X__cert, encodable.size cert ≤ inst.maxSize ∧ inst.rel cert := by
  rfl
