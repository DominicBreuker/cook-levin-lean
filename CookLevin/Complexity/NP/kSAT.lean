import Complexity.Complexity.Definitions
import Complexity.NP.SAT

set_option autoImplicit false

inductive kCNF (k : Nat) : cnf → Prop where
  | nil : kCNF k []
  | cons (N : cnf) (C : clause) : C.length = k → kCNF k N → kCNF k (C :: N)

theorem kCNF_clause_length (k : Nat) (N : cnf) :
    kCNF k N ↔ ∀ C, C ∈ N → C.length = k := by
  constructor
  · intro h
    induction h with
    | nil =>
        intro C hC
        cases hC
    | cons N C hlen hN ih =>
        intro C' hC'
        simp at hC'
        rcases hC' with rfl | hC'
        · exact hlen
        · exact ih C' hC'
  · intro h
    induction N with
    | nil =>
        exact kCNF.nil
    | cons C N ih =>
        apply kCNF.cons
        · exact h C (by simp)
        · apply ih
          intro C' hC'
          exact h C' (by simp [hC'])

theorem kCNF_app (k : Nat) (N₁ N₂ : cnf) :
    kCNF k (N₁ ++ N₂) ↔ kCNF k N₁ ∧ kCNF k N₂ := by
  rw [kCNF_clause_length, kCNF_clause_length, kCNF_clause_length]
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

def kSAT (k : Nat) : cnf → Prop := fun N => 0 < k ∧ kCNF k N ∧ SAT N
