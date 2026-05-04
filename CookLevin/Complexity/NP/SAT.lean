import Complexity.Complexity.NP
import Complexity.Complexity.Definitions

set_option autoImplicit false


def evalLiteral (a : assgn) : literal → Bool
  | (s, v) => decide (evalVar a v = s)

def evalClause (a : assgn) (C : clause) : Bool := C.any (evalLiteral a)

def evalCnf (a : assgn) (N : cnf) : Bool := N.all (evalClause a)

def satisfiesCnf (a : assgn) (N : cnf) : Prop := evalCnf a N = true

def SAT (N : cnf) : Prop := ∃ a : assgn, satisfiesCnf a N

theorem evalLiteral_var_iff (a : assgn) (b : Bool) (v : var) :
    evalLiteral a (b, v) = true ↔ evalVar a v = b := by
  simp [evalLiteral]

theorem evalClause_literal_iff (a : assgn) (C : clause) :
    evalClause a C = true ↔ ∃ l, l ∈ C ∧ evalLiteral a l = true := by
  induction C with
  | nil =>
      simp [evalClause]
  | cons l C ih =>
      simp [evalClause, Bool.or_eq_true]

theorem evalClause_app (a : assgn) (C₁ C₂ : clause) :
    evalClause a (C₁ ++ C₂) = true ↔ evalClause a C₁ = true ∨ evalClause a C₂ = true := by
  rw [evalClause_literal_iff, evalClause_literal_iff, evalClause_literal_iff]
  constructor
  · rintro ⟨l, hl, hEval⟩
    rcases List.mem_append.mp hl with hl | hl
    · exact Or.inl ⟨l, hl, hEval⟩
    · exact Or.inr ⟨l, hl, hEval⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨l, hl, hEval⟩
      exact ⟨l, List.mem_append.mpr (Or.inl hl), hEval⟩
    · rcases h with ⟨l, hl, hEval⟩
      exact ⟨l, List.mem_append.mpr (Or.inr hl), hEval⟩

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

def clause_varsIn (p : Nat → Prop) (c : clause) : Prop := ∀ v, varInClause v c → p v

def cnf_varsIn (p : Nat → Prop) (N : cnf) : Prop := ∀ v, varInCnf v N → p v

theorem cnf_varsIn_app (c₁ c₂ : cnf) (p : Nat → Prop) :
    cnf_varsIn p (c₁ ++ c₂) ↔ cnf_varsIn p c₁ ∧ cnf_varsIn p c₂ := by
  constructor
  · intro h
    constructor
    · intro v hv
      rcases hv with ⟨C, hC, hVar⟩
      exact h v ⟨C, List.mem_append.mpr (Or.inl hC), hVar⟩
    · intro v hv
      rcases hv with ⟨C, hC, hVar⟩
      exact h v ⟨C, List.mem_append.mpr (Or.inr hC), hVar⟩
  · rintro ⟨h₁, h₂⟩ v ⟨C, hC, hv⟩
    rcases List.mem_append.mp hC with hC | hC
    · exact h₁ v ⟨C, hC, hv⟩
    · exact h₂ v ⟨C, hC, hv⟩

theorem cnf_varsIn_monotonic (p₁ p₂ : Nat → Prop) (N : cnf) :
    (∀ n, p₁ n → p₂ n) → cnf_varsIn p₁ N → cnf_varsIn p₂ N := by
  intro hmono hvars v hv
  exact hmono v (hvars v hv)

def size_clause (C : clause) : Nat := C.length

def size_cnf (N : cnf) : Nat := (N.map size_clause).sum + N.length

theorem size_clause_app (C₁ C₂ : clause) :
    size_clause (C₁ ++ C₂) = size_clause C₁ + size_clause C₂ := by
  simp [size_clause]

theorem size_cnf_app (N₁ N₂ : cnf) :
    size_cnf (N₁ ++ N₂) = size_cnf N₁ + size_cnf N₂ := by
  simp [size_cnf, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

namespace SAT_inNP

theorem sat_NP : inNP SAT := by
  sorry

end SAT_inNP
