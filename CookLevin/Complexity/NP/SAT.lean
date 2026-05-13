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

/-- For any encodable list, the size of any element plus 1 is bounded by the
size of the whole list. -/
private theorem encodable_size_mem_le {α : Type _} [encodable α] :
    ∀ {x : α} {xs : List α}, x ∈ xs → encodable.size x + 1 ≤ encodable.size xs := by
  intro x xs
  induction xs with
  | nil => intro h; simp at h
  | cons y ys ih =>
      intro hx
      rw [encodable_size_list_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.le_add_right _ _
      · calc encodable.size x + 1
            ≤ encodable.size ys := ih hx'
          _ ≤ encodable.size y + 1 + encodable.size ys := Nat.le_add_left _ _

/-- A list of `Nat`s whose every element satisfies `x + 1 ≤ S` has
`encodable.size xs ≤ xs.length * S`. -/
private theorem encodable_size_listNat_le_mul (S : Nat) :
    ∀ (xs : List Nat), (∀ x ∈ xs, x + 1 ≤ S) →
      encodable.size xs ≤ xs.length * S
  | [], _ => by simp [encodable.size]
  | x :: xs, h => by
      have hx : x + 1 ≤ S := h x (by simp)
      have hxs : ∀ y ∈ xs, y + 1 ≤ S := fun y hy => h y (by simp [hy])
      have ih := encodable_size_listNat_le_mul S xs hxs
      rw [encodable_size_list_cons]
      show encodable.size x + 1 + encodable.size xs ≤ (x :: xs).length * S
      have hsx : encodable.size x = x := rfl
      rw [hsx, List.length_cons]
      -- Goal: x + 1 + encodable.size xs ≤ (xs.length + 1) * S
      calc x + 1 + encodable.size xs
          ≤ S + encodable.size xs := Nat.add_le_add_right hx _
        _ ≤ S + xs.length * S := Nat.add_le_add_left ih _
        _ = (xs.length + 1) * S := by ring

/-- A `Nodup` list of `Nat`s with every element `< S` has length `≤ S`. -/
private theorem nodupListNat_length_le (S : Nat) (xs : List Nat)
    (hNodup : xs.Nodup) (hBound : ∀ x ∈ xs, x < S) : xs.length ≤ S := by
  have hSubset : xs ⊆ List.range S := fun x hx => List.mem_range.mpr (hBound x hx)
  have hSubperm : List.Subperm xs (List.range S) := hNodup.subperm hSubset
  have hLen := hSubperm.length_le
  rwa [List.length_range] at hLen

/-- Size bound for the compressed assignment: quadratic in the size of N.
`compressAssignment a N` is a Nodup list with values drawn from
`varsOfCnf N`. Each such variable satisfies `v + 1 ≤ size N` (it lives inside
a literal of a clause of N), so the list has length `≤ size N` and
`encodable.size ≤ size N * size N`. -/
theorem compressAssignment_size_bound (a : assgn) (N : cnf) :
    encodable.size (compressAssignment a N) ≤ encodable.size N ^ 2 + 1 := by
  set S := encodable.size N
  -- Every variable appearing in `N` satisfies `v + 1 ≤ S`.
  have hVarBound : ∀ v ∈ varsOfCnf N, v + 1 ≤ S := by
    intro v hv
    rw [varsOfCnf] at hv
    rcases List.mem_flatten.mp hv with ⟨vsC, hvsC, hvInvsC⟩
    rcases List.mem_map.mp hvsC with ⟨C, hCN, rfl⟩
    rw [varsOfClause] at hvInvsC
    rcases List.mem_flatten.mp hvInvsC with ⟨vsL, hvsL, hvInvsL⟩
    rcases List.mem_map.mp hvsL with ⟨l, hlC, rfl⟩
    rw [varsOfLiteral, List.mem_singleton] at hvInvsL
    subst hvInvsL
    -- l ∈ C ∈ N, and v = l.2.
    have hlSize : l.2 + 1 ≤ encodable.size l := by
      show l.2 + 1 ≤ encodable.size l.1 + l.2 + 1
      exact Nat.add_le_add_right (Nat.le_add_left _ _) 1
    have hCSize : encodable.size l + 1 ≤ encodable.size C := encodable_size_mem_le hlC
    have hNSize : encodable.size C + 1 ≤ encodable.size N := encodable_size_mem_le hCN
    show l.2 + 1 ≤ encodable.size N
    calc l.2 + 1
        ≤ encodable.size l := hlSize
      _ ≤ encodable.size l + 1 := Nat.le_succ _
      _ ≤ encodable.size C := hCSize
      _ ≤ encodable.size C + 1 := Nat.le_succ _
      _ ≤ encodable.size N := hNSize
  -- Properties of the compressed assignment.
  have hcNodup : (compressAssignment a N).Nodup := List.nodup_dedup _
  have hcSubset : ∀ v ∈ compressAssignment a N, v ∈ varsOfCnf N := by
    intro v hv
    simp only [compressAssignment, List.mem_dedup, List.mem_filter,
               decide_eq_true_eq] at hv
    exact hv.2
  have hcVarBound : ∀ v ∈ compressAssignment a N, v + 1 ≤ S :=
    fun v hv => hVarBound v (hcSubset v hv)
  have hcLt : ∀ v ∈ compressAssignment a N, v < S := fun v hv =>
    Nat.lt_of_succ_le (hcVarBound v hv)
  have hcLenBound : (compressAssignment a N).length ≤ S :=
    nodupListNat_length_le S _ hcNodup hcLt
  have hcSizeBound : encodable.size (compressAssignment a N) ≤
      (compressAssignment a N).length * S :=
    encodable_size_listNat_le_mul S _ hcVarBound
  calc encodable.size (compressAssignment a N)
      ≤ (compressAssignment a N).length * S := hcSizeBound
    _ ≤ S * S := Nat.mul_le_mul_right S hcLenBound
    _ = S ^ 2 := by ring
    _ ≤ S ^ 2 + 1 := by linarith

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
