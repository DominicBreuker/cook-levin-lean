import CookLevin.Basic.NP
import CookLevin.SAT.FSAT
import CookLevin.SAT.SAT
import CookLevin.SAT.KCNF
import Mathlib.Tactic

/-!
# Tseytin gadgets

The 3-CNF gadgets `tseytinTrue`, `tseytinEquiv`, `tseytinAnd`, `tseytinNot` with their
satisfaction lemmas, and lemmas about assignments extended by fresh variables. Used by the
positional Tseytin transform of `FSAT_to_SAT_pre.lean`.
-/

set_option autoImplicit false
open Classical

-- ─── Bounded-assignment utilities ───────────────────────────────────────────

def boundedAssignment (n : Nat) (a : assgn) : assgn :=
  (List.range n).filter (fun v => evalVar a v)

theorem mem_boundedAssignment_iff (n : Nat) (a : assgn) (v : Nat) :
    v ∈ boundedAssignment n a ↔ v < n ∧ evalVar a v = true := by
  simp [boundedAssignment, evalVar, List.mem_range]

theorem evalVar_boundedAssignment (a : assgn) {n v : Nat} (hv : v < n) :
    evalVar (boundedAssignment n a) v = evalVar a v := by
  by_cases hmem : v ∈ a
  · simp [evalVar, mem_boundedAssignment_iff, hv, hmem]
  · simp [evalVar, mem_boundedAssignment_iff, hv, hmem]

theorem evalFormula_boundedAssignment_of_bound (a : assgn) :
    ∀ (f : formula) (n : Nat),
      formula_varsIn (fun v => v < n) f →
        evalFormula (boundedAssignment n a) f = evalFormula a f
  | .ftrue, _, _ => rfl
  | .fvar v, _, h => evalVar_boundedAssignment a (h v varInFormula.var)
  | .fand f₁ f₂, n, h => by
      simp [evalFormula,
        evalFormula_boundedAssignment_of_bound a f₁ n (fun v hv => h v (varInFormula.andLeft _ _ hv)),
        evalFormula_boundedAssignment_of_bound a f₂ n (fun v hv => h v (varInFormula.andRight _ _ hv))]
  | .forr f₁ f₂, n, h => by
      simp [evalFormula,
        evalFormula_boundedAssignment_of_bound a f₁ n (fun v hv => h v (varInFormula.orLeft _ _ hv)),
        evalFormula_boundedAssignment_of_bound a f₂ n (fun v hv => h v (varInFormula.orRight _ _ hv))]
  | .fneg f, n, h => by
      simp [evalFormula,
        evalFormula_boundedAssignment_of_bound a f n (fun v hv => h v (varInFormula.neg _ hv))]

-- Tseytin clause gadgets

def tseytinTrue (v : var) : cnf := [[(true, v), (true, v), (true, v)]]
def tseytinEquiv (v v' : var) : cnf :=
  [[(false, v), (true, v'), (true, v')], [(false, v'), (true, v), (true, v)]]
def tseytinAnd (v v₁ v₂ : var) : cnf :=
  [[(false, v), (true, v₁), (true, v₁)],
   [(false, v), (true, v₂), (true, v₂)],
   [(false, v₁), (false, v₂), (true, v)]]
def tseytinNot (v v' : var) : cnf :=
  [[(false, v), (false, v'), (false, v')],
   [(true, v), (true, v'), (true, v')]]

theorem tseytinTrue_sat (a : assgn) (v : var) :
    satisfiesCnf a (tseytinTrue v) ↔ evalVar a v = true := by
  unfold tseytinTrue satisfiesCnf
  cases h : evalVar a v <;> simp [evalCnf, evalClause, evalLiteral, h]

theorem tseytinEquiv_sat (a : assgn) (v v' : var) :
    satisfiesCnf a (tseytinEquiv v v') ↔ (evalVar a v = true ↔ evalVar a v' = true) := by
  unfold tseytinEquiv satisfiesCnf
  cases h₁ : evalVar a v <;> cases h₂ : evalVar a v' <;>
    simp [evalCnf, evalClause, evalLiteral, h₁, h₂]

theorem tseytinAnd_sat (a : assgn) (v v₁ v₂ : var) :
    satisfiesCnf a (tseytinAnd v v₁ v₂) ↔
      (evalVar a v = true ↔ (evalVar a v₁ = true ∧ evalVar a v₂ = true)) := by
  unfold tseytinAnd satisfiesCnf
  cases h₁ : evalVar a v <;> cases h₂ : evalVar a v₁ <;> cases h₃ : evalVar a v₂ <;>
    simp [evalCnf, evalClause, evalLiteral, h₁, h₂, h₃]

theorem tseytinNot_sat (a : assgn) (v v' : var) :
    satisfiesCnf a (tseytinNot v v') ↔ (evalVar a v = true ↔ ¬evalVar a v' = true) := by
  unfold tseytinNot satisfiesCnf
  cases h₁ : evalVar a v <;> cases h₂ : evalVar a v' <;>
    simp [evalCnf, evalClause, evalLiteral, h₁, h₂]

theorem tseytinTrue_kCNF (v : var) : kCNF 3 (tseytinTrue v) :=
  kCNF.cons _ _ rfl kCNF.nil
theorem tseytinEquiv_kCNF (v v' : var) : kCNF 3 (tseytinEquiv v v') :=
  kCNF.cons _ _ rfl (kCNF.cons _ _ rfl kCNF.nil)
theorem tseytinAnd_kCNF (v v₁ v₂ : var) : kCNF 3 (tseytinAnd v v₁ v₂) :=
  kCNF.cons _ _ rfl (kCNF.cons _ _ rfl (kCNF.cons _ _ rfl kCNF.nil))
theorem tseytinNot_kCNF (v v' : var) : kCNF 3 (tseytinNot v v') :=
  kCNF.cons _ _ rfl (kCNF.cons _ _ rfl kCNF.nil)

def assgn_varsIn (p : Nat → Prop) (a : assgn) : Prop := ∀ v ∈ a, p v

-- Prepending fresh vars doesn't change evalVar for old vars
theorem evalVar_append_fresh (a' a : assgn) (v b : Nat)
    (ha' : assgn_varsIn (fun n => b ≤ n) a') (hv : v < b) :
    evalVar (a' ++ a) v = evalVar a v := by
  simp only [evalVar, List.mem_append]
  have hva' : v ∉ a' := fun hmem => absurd (ha' v hmem) (by omega)
  simp [hva']

-- If v ∉ pfx, prepending pfx doesn't change evalVar
theorem evalVar_prepend_notmem (pfx base : assgn) (v : Nat) (h : v ∉ pfx) :
    evalVar (pfx ++ base) v = evalVar base v := by
  simp [evalVar, List.mem_append, h]

-- Inserting a middle assignment (disjoint from outer) doesn't change evalVar
theorem evalVar_insert_notmem (outer middle inner : assgn) (v : Nat)
    (h : v ∉ middle) :
    evalVar (outer ++ (middle ++ inner)) v = evalVar (outer ++ inner) v := by
  simp only [evalVar, List.mem_append]
  by_cases hout : v ∈ outer <;> simp [hout, h]

-- Prepending a disjoint assignment (no shared vars with N) preserves satisfiability
theorem satisfiesCnf_prepend_notmem (pfx base : assgn) (N : cnf)
    (hdisjoint : ∀ v, varInCnf v N → v ∉ pfx)
    (hsat : satisfiesCnf base N) :
    satisfiesCnf (pfx ++ base) N := by
  rw [satisfiesCnf, evalCnf_clause_iff]
  intro C hC
  rw [evalClause_literal_iff]
  obtain ⟨l, hl, heval⟩ := (evalClause_literal_iff base C).mp
    ((evalCnf_clause_iff base N).mp hsat C hC)
  rcases l with ⟨s, v⟩
  exact ⟨(s, v), hl, by
    simp only [evalLiteral] at *
    rw [evalVar_prepend_notmem pfx base v
      (hdisjoint v ⟨C, hC, (s, v), hl, s, rfl⟩)]
    exact heval⟩

-- Inserting a disjoint assignment in the middle preserves satisfiability
theorem satisfiesCnf_insert_notmem (outer middle inner : assgn) (N : cnf)
    (hdisjoint : ∀ v, varInCnf v N → v ∉ middle)
    (hsat : satisfiesCnf (outer ++ inner) N) :
    satisfiesCnf (outer ++ (middle ++ inner)) N := by
  rw [satisfiesCnf, evalCnf_clause_iff]
  intro C hC
  rw [evalClause_literal_iff]
  obtain ⟨l, hl, heval⟩ := (evalClause_literal_iff (outer ++ inner) C).mp
    ((evalCnf_clause_iff (outer ++ inner) N).mp hsat C hC)
  rcases l with ⟨s, v⟩
  exact ⟨(s, v), hl, by
    simp only [evalLiteral] at *
    rw [evalVar_insert_notmem outer middle inner v
      (hdisjoint v ⟨C, hC, (s, v), hl, s, rfl⟩)]
    exact heval⟩

-- Extension doesn't affect evaluation of formula over old vars
theorem evalFormula_append_fresh (a' a : assgn) (b : Nat) (f : formula)
    (ha' : assgn_varsIn (fun n => b ≤ n) a') (hf : formula_varsIn (fun n => n < b) f) :
    evalFormula (a' ++ a) f = evalFormula a f := by
  induction f with
  | ftrue => rfl
  | fvar v =>
      simp only [evalFormula]
      exact evalVar_append_fresh a' a v b ha' (hf v varInFormula.var)
  | fand f₁ f₂ ih₁ ih₂ =>
      simp [evalFormula, ih₁ (fun v hv => hf v (varInFormula.andLeft _ _ hv)),
                         ih₂ (fun v hv => hf v (varInFormula.andRight _ _ hv))]
  | forr f₁ f₂ ih₁ ih₂ =>
      simp [evalFormula, ih₁ (fun v hv => hf v (varInFormula.orLeft _ _ hv)),
                         ih₂ (fun v hv => hf v (varInFormula.orRight _ _ hv))]
  | fneg f ih =>
      simp [evalFormula, ih (fun v hv => hf v (varInFormula.neg _ hv))]

-- Splitting satisfiesCnf over append
theorem satisfiesCnf_app (a : assgn) (N₁ N₂ : cnf) :
    satisfiesCnf a (N₁ ++ N₂) ↔ satisfiesCnf a N₁ ∧ satisfiesCnf a N₂ := by
  simp [satisfiesCnf, evalCnf_app_iff]

-- The FSAT → SAT Tseytin reduction

-- ─── Size bound helpers ──────────────────────────────────────────────────────

theorem encodable_size_literal_le (l : literal) :
    encodable.size l ≤ l.2 + 2 := by
  obtain ⟨b, v⟩ := l
  have hpair : encodable.size (b, v) = encodable.size b + v + 1 := rfl
  have hbool : encodable.size b ≤ 1 := by cases b <;> decide
  omega

theorem encodable_size_clause3_le {C : clause} {M : Nat}
    (hLen : C.length = 3) (hVars : ∀ l ∈ C, l.2 < M) :
    encodable.size C ≤ 3 * (M + 1) + 3 := by
  obtain ⟨l₁, l₂, l₃, rfl⟩ : ∃ l₁ l₂ l₃, C = [l₁, l₂, l₃] := by
    match C, hLen with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  have hv₁ := hVars l₁ (by simp)
  have hv₂ := hVars l₂ (by simp)
  have hv₃ := hVars l₃ (by simp)
  have hs₁ := encodable_size_literal_le l₁
  have hs₂ := encodable_size_literal_le l₂
  have hs₃ := encodable_size_literal_le l₃
  have hbound₁ : encodable.size l₁ ≤ M + 1 :=
    Nat.le_trans hs₁ (Nat.add_le_add_right hv₁ 1)
  have hbound₂ : encodable.size l₂ ≤ M + 1 :=
    Nat.le_trans hs₂ (Nat.add_le_add_right hv₂ 1)
  have hbound₃ : encodable.size l₃ ≤ M + 1 :=
    Nat.le_trans hs₃ (Nat.add_le_add_right hv₃ 1)
  simp only [encodable_size_list_cons, encodable_size_list_nil]
  linarith

theorem encodable_size_cnf3_le {N : cnf} {M : Nat}
    (hClauses : ∀ C ∈ N, C.length = 3)
    (hVars : ∀ v, varInCnf v N → v < M) :
    encodable.size N ≤ N.length * (3 * (M + 1) + 4) := by
  induction N with
  | nil => simp [encodable_size_list_nil]
  | cons C N' ih =>
      rw [encodable_size_list_cons]
      have hC_len : C.length = 3 := hClauses C List.mem_cons_self
      have hC_vars : ∀ l ∈ C, l.2 < M := by
        intro l hl
        apply hVars l.2
        exact ⟨C, List.mem_cons_self, l, hl, l.1, (Prod.eta l).symm⟩
      have hN'_clauses : ∀ C' ∈ N', C'.length = 3 :=
        fun C' hC' => hClauses C' (List.mem_cons_of_mem _ hC')
      have hN'_vars : ∀ v, varInCnf v N' → v < M := by
        intro v ⟨C', hC', hvar⟩
        exact hVars v ⟨C', List.mem_cons_of_mem _ hC', hvar⟩
      have ih' := ih hN'_clauses hN'_vars
      have hC_size := encodable_size_clause3_le hC_len hC_vars
      simp only [List.length_cons]
      have h_expand : (N'.length + 1) * (3 * (M + 1) + 4) =
          N'.length * (3 * (M + 1) + 4) + (3 * (M + 1) + 4) := by ring
      linarith


