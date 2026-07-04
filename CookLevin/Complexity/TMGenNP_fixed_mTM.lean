import Complexity.Complexity.Definitions
import Complexity.Complexity.NP
import Complexity.NP.GenNP

set_option autoImplicit false

/-- Certificate size is measured by the repository-wide `encodable.size`
interface so every bridge stage talks about the same notion of input size. -/
def certificateMeasure {α : Sort _} [encodable α] (cert : α) : Nat := encodable.size cert

theorem certificateMeasure_eq_size {α : Sort _} [encodable α] (x : α) :
    certificateMeasure x = encodable.size x := rfl

theorem certificateMeasure_le_add_right {α : Sort _} [encodable α] (x : α) (n : Nat) :
    certificateMeasure x ≤ certificateMeasure x + n := by
  simp [certificateMeasure]

namespace LMGenNP

structure Instance (X : Type) [encodable X] where
  source : GenNPInput X
  maxSize : Nat
  steps : Nat

/-- Real size for `LMGenNP.Instance` (Part 0.1): the wrapped source instance
plus the stage's own numeric parameters. -/
instance {X : Type} [encodable X] : encodable (Instance X) where
  size := fun inst => encodable.size inst.source + inst.maxSize + inst.steps + 1
  size_ge_logical := fun inst =>
    ⟨encodable.size inst.source + inst.maxSize + inst.steps + 1, Nat.le_refl _⟩

@[simp]
theorem encodable_size_Instance {X : Type} [encodable X] (inst : Instance X) :
    encodable.size inst = encodable.size inst.source + inst.maxSize + inst.steps + 1 := rfl

def LMGenNP (X : Type) [encodable X] : Instance X → Prop :=
  fun inst =>
    ∃ cert : X,
      certificateMeasure cert ≤ inst.maxSize ∧
      certificateMeasure cert ≤ inst.source.maxSize ∧
      inst.source.rel cert

end LMGenNP

structure mTMGenNPFixedInput (σ : Type) where
  workTapes : List (List σ)
  maxSize : Nat
  steps : Nat
  accepts : List σ → Prop

/-- Real size for `mTMGenNPFixedInput` (Part 0.1): tape contents plus the
numeric parameters; the `accepts` predicate is abstract (see `GenNPInput`). -/
instance {σ : Type} [encodable σ] : encodable (mTMGenNPFixedInput σ) where
  size := fun inst => encodable.size inst.workTapes + inst.maxSize + inst.steps + 1
  size_ge_logical := fun inst =>
    ⟨encodable.size inst.workTapes + inst.maxSize + inst.steps + 1, Nat.le_refl _⟩

@[simp]
theorem encodable_size_mTMGenNPFixedInput {σ : Type} [encodable σ]
    (inst : mTMGenNPFixedInput σ) :
    encodable.size inst = encodable.size inst.workTapes + inst.maxSize + inst.steps + 1 := rfl

def mTMGenNP_fixed {σ : Type} [instσ : encodable σ] (_ : TM σ 2) : mTMGenNPFixedInput σ → Prop :=
  fun inst =>
    ∃ cert : List σ,
      @certificateMeasure (List σ) (@instEncodableList σ instσ) cert ≤ inst.maxSize ∧ inst.accepts cert

structure TMGenNPFixedInput (σ : Type) where
  input : List σ
  maxSize : Nat
  steps : Nat
  accepts : List σ → Prop

/-- Real size for `TMGenNPFixedInput` (Part 0.1): tape content plus the
numeric parameters; the `accepts` predicate is abstract (see `GenNPInput`). -/
instance {σ : Type} [encodable σ] : encodable (TMGenNPFixedInput σ) where
  size := fun inst => encodable.size inst.input + inst.maxSize + inst.steps + 1
  size_ge_logical := fun inst =>
    ⟨encodable.size inst.input + inst.maxSize + inst.steps + 1, Nat.le_refl _⟩

@[simp]
theorem encodable_size_TMGenNPFixedInput {σ : Type} [encodable σ]
    (inst : TMGenNPFixedInput σ) :
    encodable.size inst = encodable.size inst.input + inst.maxSize + inst.steps + 1 := rfl

def initTape_singleTapeTM {σ : Type} (s : List σ) : List σ := s

def TMGenNP_fixed {σ : Type} [instσ : encodable σ] (_ : TM σ 1) : TMGenNPFixedInput σ → Prop :=
  fun inst =>
    ∃ cert : List σ,
      @certificateMeasure (List σ) (@instEncodableList σ instσ) cert ≤ inst.maxSize ∧ inst.accepts cert
