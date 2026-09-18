import CookLevin.Basic.Definitions
import Mathlib.Tactic

/-!
# Formula satisfiability

`evalFormula` evaluates a Boolean formula (`formula`: `ftrue`, `fvar`, `fand`, `forr`,
`fneg`) under an assignment, and `FSAT f` says some assignment satisfies `f`.
-/

set_option autoImplicit false

def evalFormula (a : assgn) : formula → Bool
  | .ftrue => true
  | .fvar v => evalVar a v
  | .fand φ ψ => evalFormula a φ && evalFormula a ψ
  | .forr φ ψ => evalFormula a φ || evalFormula a ψ
  | .fneg φ => !(evalFormula a φ)

def satisfiesFormula (a : assgn) (f : formula) : Prop := evalFormula a f = true

def FSAT (f : formula) : Prop := ∃ a, satisfiesFormula a f

theorem evalFormula_and_iff (a : assgn) (f₁ f₂ : formula) :
    evalFormula a (.fand f₁ f₂) = true ↔ evalFormula a f₁ = true ∧ evalFormula a f₂ = true := by
  simp [evalFormula, Bool.and_eq_true]

theorem evalFormula_or_iff (a : assgn) (f₁ f₂ : formula) :
    evalFormula a (.forr f₁ f₂) = true ↔ evalFormula a f₁ = true ∨ evalFormula a f₂ = true := by
  simp [evalFormula, Bool.or_eq_true]

inductive varInFormula (v : var) : formula → Prop where
  | var : varInFormula v (.fvar v)
  | andLeft (f₁ f₂ : formula) : varInFormula v f₁ → varInFormula v (.fand f₁ f₂)
  | andRight (f₁ f₂ : formula) : varInFormula v f₂ → varInFormula v (.fand f₁ f₂)
  | orLeft (f₁ f₂ : formula) : varInFormula v f₁ → varInFormula v (.forr f₁ f₂)
  | orRight (f₁ f₂ : formula) : varInFormula v f₂ → varInFormula v (.forr f₁ f₂)
  | neg (f : formula) : varInFormula v f → varInFormula v (.fneg f)

def formula_varsIn (p : Nat → Prop) (f : formula) : Prop := ∀ v, varInFormula v f → p v

def formula_maxVar : formula → Nat
  | .ftrue => 0
  | .fvar v => v
  | .fand f₁ f₂ => Nat.max (formula_maxVar f₁) (formula_maxVar f₂)
  | .forr f₁ f₂ => Nat.max (formula_maxVar f₁) (formula_maxVar f₂)
  | .fneg f => formula_maxVar f

theorem formula_maxVar_varsIn (f : formula) :
    formula_varsIn (fun n => n < formula_maxVar f + 1) f := by
  intro v hv
  induction hv with
  | var =>
      simp [formula_maxVar]
  | andLeft f₁ f₂ hv ih =>
      simp [formula_maxVar]
      omega
  | andRight f₁ f₂ hv ih =>
      simp [formula_maxVar]
      omega
  | orLeft f₁ f₂ hv ih =>
      simp [formula_maxVar]
      omega
  | orRight f₁ f₂ hv ih =>
      simp [formula_maxVar]
      omega
  | neg f hv ih =>
      simpa [formula_maxVar] using ih

def formula_size : formula → Nat
  | .ftrue => 1
  | .fvar _ => 1
  | .fand f₁ f₂ => formula_size f₁ + formula_size f₂ + 1
  | .forr f₁ f₂ => formula_size f₁ + formula_size f₂ + 1
  | .fneg f => formula_size f + 1
