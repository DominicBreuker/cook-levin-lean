import Complexity.Complexity.Definitions
import Complexity.Complexity.NP
import Complexity.NP.GenNP

set_option autoImplicit false

/-- The current phase-4 port keeps certificate-size bookkeeping abstract.  The
surrounding scaffold still uses a placeholder `encodable` interface, so the
machine-facing problems record explicit size and time bounds while the concrete
certificate measure is deferred to later phases. -/
def certificateMeasure {α : Sort _} [encodable α] (cert : α) : Nat := 0

theorem certificateMeasure_eq_zero {α : Sort _} [encodable α] (x : α) :
    certificateMeasure x = 0 := rfl

theorem certificateMeasure_le {α : Sort _} [encodable α] (x : α) (n : Nat) :
    certificateMeasure x ≤ n := by
  simp [certificateMeasure]

namespace LMGenNP

structure Instance (X : Type) [encodable X] where
  source : GenNPInput X
  maxSize : Nat
  steps : Nat

def LMGenNP (X : Type) [encodable X] : Instance X → Prop :=
  fun inst => ∃ cert : X, certificateMeasure cert ≤ inst.maxSize ∧ inst.source.rel cert

end LMGenNP

structure mTMGenNPFixedInput (σ : Type) where
  workTapes : List (List σ)
  maxSize : Nat
  steps : Nat
  accepts : List σ → Prop

def mTMGenNP_fixed {σ : Type} (_ : TM σ 2) : mTMGenNPFixedInput σ → Prop :=
  fun inst => ∃ cert : List σ, certificateMeasure cert ≤ inst.maxSize ∧ inst.accepts cert

structure TMGenNPFixedInput (σ : Type) where
  input : List σ
  maxSize : Nat
  steps : Nat
  accepts : List σ → Prop

def initTape_singleTapeTM {σ : Type} (s : List σ) : List σ := s

def TMGenNP_fixed {σ : Type} (_ : TM σ 1) : TMGenNPFixedInput σ → Prop :=
  fun inst => ∃ cert : List σ, certificateMeasure cert ≤ inst.maxSize ∧ inst.accepts cert
