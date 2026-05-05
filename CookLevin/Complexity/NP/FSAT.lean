import Complexity.Complexity.Definitions
import Mathlib.Tactic

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

theorem evalFormula_and_iff' (a : assgn) (f₁ f₂ : formula) :
    evalFormula a (.fand f₁ f₂) = false ↔ evalFormula a f₁ = false ∨ evalFormula a f₂ = false := by
  cases h₁ : evalFormula a f₁ <;> cases h₂ : evalFormula a f₂ <;> simp [evalFormula, h₁, h₂]

theorem evalFormula_or_iff (a : assgn) (f₁ f₂ : formula) :
    evalFormula a (.forr f₁ f₂) = true ↔ evalFormula a f₁ = true ∨ evalFormula a f₂ = true := by
  simp [evalFormula, Bool.or_eq_true]

theorem evalFormula_not_iff (a : assgn) (f : formula) :
    evalFormula a (.fneg f) = true ↔ ¬ evalFormula a f = true := by
  cases h : evalFormula a f <;> simp [evalFormula, h]

theorem evalFormula_prim_iff (a : assgn) (v : var) :
    evalFormula a (.fvar v) = true ↔ v ∈ a := by
  simp [evalFormula, evalVar]

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

theorem formula_varsIn_bound (f : formula) (c : Nat) :
    formula_varsIn (fun n => n ≤ c) f → formula_maxVar f ≤ c := by
  intro h
  induction f with
  | ftrue =>
      simp [formula_maxVar]
  | fvar v =>
      exact h v varInFormula.var
  | fand f₁ f₂ ih₁ ih₂ =>
      simp [formula_maxVar]
      exact ⟨
        ih₁ (fun v hv => h v (varInFormula.andLeft _ _ hv)),
        ih₂ (fun v hv => h v (varInFormula.andRight _ _ hv))⟩
  | forr f₁ f₂ ih₁ ih₂ =>
      simp [formula_maxVar]
      exact ⟨
        ih₁ (fun v hv => h v (varInFormula.orLeft _ _ hv)),
        ih₂ (fun v hv => h v (varInFormula.orRight _ _ hv))⟩
  | fneg f ih =>
      simpa [formula_maxVar] using ih (fun v hv => h v (varInFormula.neg _ hv))

def formula_size : formula → Nat
  | .ftrue => 1
  | .fvar _ => 1
  | .fand f₁ f₂ => formula_size f₁ + formula_size f₂ + 1
  | .forr f₁ f₂ => formula_size f₁ + formula_size f₂ + 1
  | .fneg f => formula_size f + 1
