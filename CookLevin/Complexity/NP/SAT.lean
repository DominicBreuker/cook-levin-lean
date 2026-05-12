import Complexity.Complexity.NP
import Complexity.Complexity.Definitions
import Mathlib.Tactic

set_option autoImplicit false


def evalLiteral (a : assgn) : literal → Bool
  | (s, v) => decide (evalVar a v = s)

def evalClause (a : assgn) (C : clause) : Bool := C.any (evalLiteral a)

def evalCnf (a : assgn) (N : cnf) : Bool := N.all (evalClause a)

def satisfiesCnf (a : assgn) (N : cnf) : Prop := evalCnf a N = true

def SAT (N : cnf) : Prop := ∃ a : assgn, satisfiesCnf a N

theorem evalClause_step_inv (a : assgn) (C : clause) (l : literal) (b : Bool) :
    evalClause a (l :: C) = b ↔
      ∃ b₁ b₂, evalClause a C = b₂ ∧ evalLiteral a l = b₁ ∧ b = (b₁ || b₂) := by
  constructor
  · intro h
    refine ⟨evalLiteral a l, evalClause a C, rfl, rfl, ?_⟩
    simpa [evalClause] using h.symm
  · rintro ⟨b₁, b₂, rfl, rfl, h⟩
    simpa [evalClause] using h.symm

theorem evalCnf_step_inv (a : assgn) (N : cnf) (C : clause) (b : Bool) :
    evalCnf a (C :: N) = b ↔
      ∃ b₁ b₂, evalCnf a N = b₂ ∧ evalClause a C = b₁ ∧ b = (b₁ && b₂) := by
  constructor
  · intro h
    refine ⟨evalClause a C, evalCnf a N, rfl, rfl, ?_⟩
    simpa [evalCnf] using h.symm
  · rintro ⟨b₁, b₂, rfl, rfl, h⟩
    simpa [evalCnf] using h.symm

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

theorem evalLiteral_assgn_equiv {a₁ a₂ : assgn} (hEq : assgnEquiv a₁ a₂) (l : literal) :
    evalLiteral a₁ l = evalLiteral a₂ l := by
  rcases l with ⟨b, v⟩
  rw [evalLiteral, evalLiteral, evalVar_assgn_equiv hEq v]

theorem evalClause_assgn_equiv {a₁ a₂ : assgn} (hEq : assgnEquiv a₁ a₂) (C : clause) :
    evalClause a₁ C = evalClause a₂ C := by
  induction C with
  | nil =>
      rfl
  | cons l C ih =>
      have hLit : evalLiteral a₁ l = evalLiteral a₂ l := evalLiteral_assgn_equiv hEq l
      have ih' : C.any (evalLiteral a₁) = C.any (evalLiteral a₂) := by
        simpa [evalClause] using ih
      simp [evalClause, hLit, ih']

theorem evalCnf_assgn_equiv {a₁ a₂ : assgn} (hEq : assgnEquiv a₁ a₂) (N : cnf) :
    evalCnf a₁ N = evalCnf a₂ N := by
  induction N with
  | nil =>
      rfl
  | cons C N ih =>
      have hClause : evalClause a₁ C = evalClause a₂ C := evalClause_assgn_equiv hEq C
      have ih' : N.all (evalClause a₁) = N.all (evalClause a₂) := by
        simpa [evalCnf] using ih
      simp [evalCnf, hClause, ih']

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

/-! ## Variables used in a CNF

We define `varsOfCnf N` as the list of variable indices appearing in any literal
of `N`. The compressed assignment `compressAssignment a N` restricts an
assignment to only those variables. This gives a polynomially-bounded certificate. -/

def varsOfLiteral (l : literal) : List Nat := [l.2]

def varsOfClause (C : clause) : List Nat := (C.map varsOfLiteral).flatten

def varsOfCnf (N : cnf) : List Nat := (N.map varsOfClause).flatten

/-- The compressed assignment: keep only variables appearing in `N`, deduplicated. -/
def compressAssignment (a : assgn) (N : cnf) : assgn :=
  (a.filter (fun v => decide (v ∈ varsOfCnf N))).dedup

/-- A variable that appears in `N` is in `varsOfCnf N`. -/
theorem varsOfCnf_mem (N : cnf) (C : clause) (l : literal)
    (hC : C ∈ N) (hl : l ∈ C) : l.2 ∈ varsOfCnf N := by
  apply List.mem_flatten.mpr
  exact ⟨varsOfClause C, List.mem_map.mpr ⟨C, hC, rfl⟩,
    List.mem_flatten.mpr ⟨varsOfLiteral l, List.mem_map.mpr ⟨l, hl, rfl⟩,
      List.mem_singleton.mpr rfl⟩⟩

/-- For variables in `N`, the compressed assignment agrees with the original. -/
theorem compressAssignment_evalVar (a : assgn) (N : cnf) (v : Nat)
    (hv : v ∈ varsOfCnf N) :
    evalVar a v = evalVar (compressAssignment a N) v := by
  simp only [evalVar, compressAssignment, List.mem_dedup, List.mem_filter,
             decide_eq_true_eq, hv, and_true]

/-- A CNF evaluates the same under `a` and `compressAssignment a N`. -/
theorem compressAssignment_cnf_equiv (a : assgn) (N : cnf) :
    satisfiesCnf a N ↔ satisfiesCnf (compressAssignment a N) N := by
  simp only [satisfiesCnf, evalCnf_clause_iff, evalClause_literal_iff]
  apply forall_congr'; intro C; apply imp_congr_right; intro hC
  apply exists_congr; intro l; apply and_congr_right; intro hl
  rcases l with ⟨b, v⟩
  simp only [evalLiteral, ← compressAssignment_evalVar a N v (varsOfCnf_mem N C _ hC hl)]

/-- Size bound for the compressed assignment: quadratic in the size of N.
The proof sketch: compressAssignment a N has at most |varsOfCnf N| ≤ size(N)
many variables, each with value ≤ size(N), giving a quadratic size bound. -/
theorem compressAssignment_size_bound (a : assgn) (N : cnf) :
    encodable.size (compressAssignment a N) ≤ encodable.size N ^ 2 + 1 := by
  sorry

theorem sat_NP : inNP SAT := by
  refine inNP_intro SAT (fun N a => satisfiesCnf a N) ?_ ?_
  · -- inTimePoly: the Boolean decision procedure evalCnf is the decider
    exact ⟨fun n => n + 1,
      ⟨fun xy => evalCnf xy.2 xy.1, fun _ => Iff.rfl⟩,
      ⟨1, ⟨2, 1, by intro n hn; simp [pow_one]; omega⟩⟩,
      fun x x' h => Nat.add_le_add_right h 1⟩
  · -- polyCertRel: every SAT instance has a polynomially-bounded certificate
    refine ⟨⟨fun n => n ^ 2 + 1, ?_, ?_, ?_, ?_⟩⟩
    · -- sound: a satisfying assignment witnesses SAT
      intro N a h; exact ⟨a, h⟩
    · -- complete: compress the satisfying assignment to a bounded one
      intro N ⟨a, ha⟩
      exact ⟨compressAssignment a N, (compressAssignment_cnf_equiv a N).mp ha,
             compressAssignment_size_bound a N⟩
    · -- inOPoly: n^2 + 1 is polynomial
      exact ⟨2, ⟨2, 1, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩
    · -- monotonic
      intro a b h; nlinarith [Nat.pow_le_pow_left h 2]

end SAT_inNP
