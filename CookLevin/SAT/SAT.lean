import CookLevin.Basic.NP
import CookLevin.Basic.Definitions
import Mathlib.Tactic

/-!
# CNF satisfiability

`evalCnf a N` evaluates a CNF under an assignment, given as the list of true variables, and
`SAT N` says some assignment satisfies `N`. `varsOfCnf` lists the variables occurring in
`N`.
-/

set_option autoImplicit false

def evalLiteral (a : assgn) : literal → Bool
  | (s, v) => decide (evalVar a v = s)

def evalClause (a : assgn) (C : clause) : Bool := C.any (evalLiteral a)

def evalCnf (a : assgn) (N : cnf) : Bool := N.all (evalClause a)

def satisfiesCnf (a : assgn) (N : cnf) : Prop := evalCnf a N = true

def SAT (N : cnf) : Prop := ∃ a : assgn, satisfiesCnf a N

theorem evalClause_literal_iff (a : assgn) (C : clause) :
    evalClause a C = true ↔ ∃ l, l ∈ C ∧ evalLiteral a l = true := by
  induction C with
  | nil =>
      simp [evalClause]
  | cons l C ih =>
      simp [evalClause, Bool.or_eq_true]

theorem evalCnf_clause_iff (a : assgn) (N : cnf) :
    evalCnf a N = true ↔ ∀ C, C ∈ N → evalClause a C = true := by
  induction N with
  | nil =>
      simp [evalCnf]
  | cons C N ih =>
      simp [evalCnf, Bool.and_eq_true]

theorem evalCnf_app_iff (a : assgn) (N₁ N₂ : cnf) :
    evalCnf a (N₁ ++ N₂) = true ↔ evalCnf a N₁ = true ∧ evalCnf a N₂ = true := by
  rw [evalCnf_clause_iff, evalCnf_clause_iff, evalCnf_clause_iff]
  constructor
  · intro h
    constructor
    · intro C hC
      exact h C (List.mem_append.mpr (Or.inl hC))
    · intro C hC
      exact h C (List.mem_append.mpr (Or.inr hC))
  · rintro ⟨h₁, h₂⟩ C hC
    rcases List.mem_append.mp hC with hC | hC
    · exact h₁ C hC
    · exact h₂ C hC

def varInLiteral (v : var) (l : literal) : Prop := ∃ b, l = (b, v)

def varInClause (v : var) (c : clause) : Prop := ∃ l, l ∈ c ∧ varInLiteral v l

def varInCnf (v : var) (N : cnf) : Prop := ∃ C, C ∈ N ∧ varInClause v C

def cnf_varsIn (p : Nat → Prop) (N : cnf) : Prop := ∀ v, varInCnf v N → p v

namespace SAT_inNP

/-! ## Variables used in a CNF

We define `varsOfCnf N` as the list of variable indices appearing in any literal
of `N`. The compressed assignment `compressAssignment a N` restricts an
assignment to only those variables. This gives a polynomially-bounded certificate. -/

def varsOfLiteral (l : literal) : List Nat := [l.2]

def varsOfClause (C : clause) : List Nat := (C.map varsOfLiteral).flatten

def varsOfCnf (N : cnf) : List Nat := (N.map varsOfClause).flatten

/-- A variable that appears in `N` is in `varsOfCnf N`. -/
theorem varsOfCnf_mem (N : cnf) (C : clause) (l : literal)
    (hC : C ∈ N) (hl : l ∈ C) : l.2 ∈ varsOfCnf N := by
  apply List.mem_flatten.mpr
  exact ⟨varsOfClause C, List.mem_map.mpr ⟨C, hC, rfl⟩,
    List.mem_flatten.mpr ⟨varsOfLiteral l, List.mem_map.mpr ⟨l, hl, rfl⟩,
      List.mem_singleton.mpr rfl⟩⟩


end SAT_inNP
