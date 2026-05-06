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

def mTMGenNP_fixed {σ : Type} [instσ : encodable σ] (_ : TM σ 2) : mTMGenNPFixedInput σ → Prop :=
  fun inst =>
    ∃ cert : List σ,
      @certificateMeasure (List σ) (@instEncodableList σ instσ) cert ≤ inst.maxSize ∧ inst.accepts cert

structure TMGenNPFixedInput (σ : Type) where
  input : List σ
  maxSize : Nat
  steps : Nat
  accepts : List σ → Prop

def initTape_singleTapeTM {σ : Type} (s : List σ) : List σ := s

def TMGenNP_fixed {σ : Type} [instσ : encodable σ] (_ : TM σ 1) : TMGenNPFixedInput σ → Prop :=
  fun inst =>
    ∃ cert : List σ,
      @certificateMeasure (List σ) (@instEncodableList σ instσ) cert ≤ inst.maxSize ∧ inst.accepts cert
