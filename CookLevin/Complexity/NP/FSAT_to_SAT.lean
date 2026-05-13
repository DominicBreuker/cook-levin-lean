import Complexity.Complexity.NP
import Complexity.NP.FSAT
import Complexity.NP.SAT
import Complexity.NP.kSAT
import Mathlib.Tactic

set_option autoImplicit false
open Classical

-- ─── Bounded-assignment utilities ───────────────────────────────────────────

def allAssignments : Nat → List assgn
  | 0 => [[]]
  | n + 1 =>
      let prev := allAssignments n
      prev ++ prev.map (fun a => a ++ [n])

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

theorem evalFormula_boundedAssignment (a : assgn) (f : formula) :
    evalFormula (boundedAssignment (formula_maxVar f + 1) a) f = evalFormula a f :=
  evalFormula_boundedAssignment_of_bound a f (formula_maxVar f + 1) (formula_maxVar_varsIn f)

theorem boundedAssignment_succ (n : Nat) (a : assgn) :
    boundedAssignment (n + 1) a =
      if evalVar a n = true then boundedAssignment n a ++ [n] else boundedAssignment n a := by
  by_cases h : evalVar a n = true
  · simp [boundedAssignment, List.range_succ, List.filter_append, h]
  · simp [boundedAssignment, List.range_succ, List.filter_append, h]

theorem boundedAssignment_mem_allAssignments :
    ∀ n (a : assgn), boundedAssignment n a ∈ allAssignments n
  | 0, _ => by simp [boundedAssignment, allAssignments]
  | n + 1, a => by
      rw [boundedAssignment_succ]
      by_cases h : evalVar a n = true
      · simp [allAssignments, h, boundedAssignment_mem_allAssignments n a]
      · simp [allAssignments, h, boundedAssignment_mem_allAssignments n a]

-- ─── Step 1: Eliminate ORs ───────────────────────────────────────────────────

def eliminateOR : formula → formula
  | .ftrue => .ftrue
  | .fvar v => .fvar v
  | .fand f₁ f₂ => .fand (eliminateOR f₁) (eliminateOR f₂)
  | .fneg f => .fneg (eliminateOR f)
  | .forr f₁ f₂ => .fneg (.fand (.fneg (eliminateOR f₁)) (.fneg (eliminateOR f₂)))

inductive orFree : formula → Prop
  | ftrue : orFree .ftrue
  | fvar (v : var) : orFree (.fvar v)
  | fand {f₁ f₂} : orFree f₁ → orFree f₂ → orFree (.fand f₁ f₂)
  | fneg {f} : orFree f → orFree (.fneg f)

theorem orFree_eliminate (f : formula) : orFree (eliminateOR f) := by
  induction f with
  | ftrue => exact .ftrue
  | fvar v => exact .fvar v
  | fand _ _ ih₁ ih₂ => exact .fand ih₁ ih₂
  | forr _ _ ih₁ ih₂ => exact .fneg (.fand (.fneg ih₁) (.fneg ih₂))
  | fneg _ ih => exact .fneg ih

theorem eliminateOR_eval (a : assgn) (f : formula) :
    evalFormula a f = evalFormula a (eliminateOR f) := by
  induction f with
  | ftrue => rfl
  | fvar v => rfl
  | fand _ _ ih₁ ih₂ => simp [eliminateOR, evalFormula, ih₁, ih₂]
  | forr _ _ ih₁ ih₂ =>
      simp only [eliminateOR, evalFormula, ← ih₁, ← ih₂]
      cases evalFormula a _ <;> cases evalFormula a _ <;> rfl
  | fneg _ ih => simp [eliminateOR, evalFormula, ih]

theorem eliminateOR_FSAT (f : formula) : FSAT f ↔ FSAT (eliminateOR f) := by
  unfold FSAT satisfiesFormula
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [← eliminateOR_eval]; exact ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [eliminateOR_eval]; exact ha⟩

-- ─── Step 2: Tseytin clause gadgets ─────────────────────────────────────────

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

-- ─── Step 3: Recursive Tseytin transformation ────────────────────────────────

def tseytin' (nfVar : var) : formula → var × cnf × var
  | .ftrue => (nfVar, tseytinTrue nfVar, nfVar + 1)
  | .fvar v => (nfVar, tseytinEquiv v nfVar, nfVar + 1)
  | .fand f₁ f₂ =>
      let (rv₁, N₁, nf₁) := tseytin' nfVar f₁
      let (rv₂, N₂, nf₂) := tseytin' nf₁ f₂
      (nf₂, N₁ ++ N₂ ++ tseytinAnd nf₂ rv₁ rv₂, nf₂ + 1)
  | .fneg f =>
      let (rv, N, nf') := tseytin' nfVar f
      (nf', N ++ tseytinNot nf' rv, nf' + 1)
  | .forr _ _ => (nfVar, [], nfVar)

def tseytin (f : formula) : var × cnf :=
  let (rv, N, _) := tseytin' (formula_maxVar f + 1) f
  (rv, N)

theorem tseytin'_nf_mono (nf : var) (f : formula) : nf ≤ (tseytin' nf f).2.2 := by
  induction f generalizing nf with
  | ftrue | fvar _ | forr _ _ _ _ => simp [tseytin']
  | fand f₁ f₂ ih₁ ih₂ =>
      simp only [tseytin']
      exact le_trans (ih₁ nf) (le_trans (ih₂ _) (Nat.le_succ _))
  | fneg f ih => simp only [tseytin']; exact le_trans (ih nf) (Nat.le_succ _)

theorem tseytin'_kCNF3 (nf : var) (f : formula) (hor : orFree f) :
    kCNF 3 (tseytin' nf f).2.1 := by
  induction f generalizing nf with
  | ftrue => simp [tseytin', tseytinTrue_kCNF]
  | fvar v => simp [tseytin', tseytinEquiv_kCNF]
  | fand f₁ f₂ ih₁ ih₂ =>
      cases hor with | fand h₁ h₂ =>
      simp only [tseytin', ← List.append_assoc]
      exact (kCNF_app 3 _ _).mpr ⟨(kCNF_app 3 _ _).mpr ⟨ih₁ nf h₁, ih₂ _ h₂⟩,
                                    tseytinAnd_kCNF _ _ _⟩
  | forr _ _ _ _ => cases hor
  | fneg f ih =>
      cases hor with | fneg h =>
      simp only [tseytin']
      exact (kCNF_app 3 _ _).mpr ⟨ih nf h, tseytinNot_kCNF _ _⟩

-- ─── Step 4: Strengthened Tseytin invariant ─────────────────────────────────

def assgn_varsIn (p : Nat → Prop) (a : assgn) : Prop := ∀ v ∈ a, p v

def tseytin_formula_repr (f : formula) (N : cnf) (v : var) (b nf nf' : Nat) : Prop :=
  cnf_varsIn (fun n => n < b ∨ (nf ≤ n ∧ n < nf')) N ∧
  nf ≤ v ∧ v < nf' ∧
  (∀ a, assgn_varsIn (fun n => n < b) a →
    ∃ a', assgn_varsIn (fun n => nf ≤ n ∧ n < nf') a' ∧ satisfiesCnf (a' ++ a) N) ∧
  (∀ a, satisfiesCnf a N → (evalVar a v = true ↔ evalFormula a f = true))

-- Prepending fresh vars doesn't change evalVar for old vars
theorem evalVar_append_fresh (a' a : assgn) (v b : Nat)
    (ha' : assgn_varsIn (fun n => b ≤ n) a') (hv : v < b) :
    evalVar (a' ++ a) v = evalVar a v := by
  simp only [evalVar, List.mem_append]
  have hva' : v ∉ a' := fun hmem => absurd (ha' v hmem) (by omega)
  simp [hva']

-- If v ∉ pfx, prepending pfx doesn't change evalVar
private theorem evalVar_prepend_notmem (pfx base : assgn) (v : Nat) (h : v ∉ pfx) :
    evalVar (pfx ++ base) v = evalVar base v := by
  simp [evalVar, List.mem_append, h]

-- Inserting a middle assignment (disjoint from outer) doesn't change evalVar
private theorem evalVar_insert_notmem (outer middle inner : assgn) (v : Nat)
    (h : v ∉ middle) :
    evalVar (outer ++ (middle ++ inner)) v = evalVar (outer ++ inner) v := by
  simp only [evalVar, List.mem_append]
  by_cases hout : v ∈ outer <;> simp [hout, h]

-- Prepending a disjoint assignment (no shared vars with N) preserves satisfiability
private theorem satisfiesCnf_prepend_notmem (pfx base : assgn) (N : cnf)
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
private theorem satisfiesCnf_insert_notmem (outer middle inner : assgn) (N : cnf)
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
private theorem satisfiesCnf_app (a : assgn) (N₁ N₂ : cnf) :
    satisfiesCnf a (N₁ ++ N₂) ↔ satisfiesCnf a N₁ ∧ satisfiesCnf a N₂ := by
  simp [satisfiesCnf, evalCnf_app_iff]

theorem tseytinP_repr {b : Nat} (f : formula)
    (hor : orFree f) (hvars : formula_varsIn (fun n => n < b) f)
    (nf : Nat) (hnf : b ≤ nf) :
    tseytin_formula_repr f (tseytin' nf f).2.1 (tseytin' nf f).1 b nf (tseytin' nf f).2.2 := by
  induction f generalizing nf with
  | ftrue =>
      simp only [tseytin', tseytin_formula_repr]
      refine ⟨?_, le_refl _, Nat.lt_succ_self _, ?_, ?_⟩
      · -- cnf_varsIn
        intro v hv
        unfold varInCnf varInClause varInLiteral at hv
        obtain ⟨C, hC, l, hl, b', hlv⟩ := hv
        simp only [tseytinTrue, List.mem_singleton] at hC; subst hC
        simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hl
        rcases hl with rfl | rfl | rfl <;>
          (simp only [Prod.mk.injEq] at hlv; obtain ⟨-, rfl⟩ := hlv; right; omega)
      · -- ext
        intro a _
        exact ⟨[nf], fun v hv => by simp at hv; subst hv; omega,
          by rw [tseytinTrue_sat]; simp [evalVar]⟩
      · -- spec
        intro a ha
        constructor
        · intro _; rfl
        · intro _; exact (tseytinTrue_sat a nf).mp ha
  | fvar v₀ =>
      simp only [tseytin', tseytin_formula_repr]
      have hv_lt : v₀ < b := hvars v₀ varInFormula.var
      refine ⟨?_, le_refl _, Nat.lt_succ_self _, ?_, ?_⟩
      · -- cnf_varsIn: vars of tseytinEquiv v₀ nf are v₀ and nf
        intro u hu
        obtain ⟨C, hC, l, hl, s, heq⟩ := hu
        simp only [tseytinEquiv, List.mem_cons, List.mem_singleton,
                   List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl <;>
          (simp only [List.mem_cons, List.mem_singleton,
                      List.mem_nil_iff, or_false] at hl
           rcases hl with rfl | rfl | rfl <;>
             (simp only [Prod.mk.injEq] at heq
              obtain ⟨-, rfl⟩ := heq)) <;>
          first
          | exact Or.inl hv_lt
          | exact Or.inr ⟨le_refl _, Nat.lt_succ_self _⟩
      · -- ext: include nf in assignment iff v₀ is true
        intro a ha
        by_cases hv₀ : evalVar a v₀ = true
        · refine ⟨[nf], ?_, ?_⟩
          · intro v hv
            simp only [List.mem_singleton] at hv; subst hv
            exact ⟨le_refl _, Nat.lt_succ_self _⟩
          · rw [tseytinEquiv_sat]
            have h_nf : evalVar ([nf] ++ a) nf = true := by
              simp [evalVar, List.mem_append, List.mem_singleton]
            have h_v₀ : evalVar ([nf] ++ a) v₀ = evalVar a v₀ :=
              evalVar_append_fresh [nf] a v₀ nf
                (fun v hv => by simp only [List.mem_singleton] at hv; subst hv; exact le_refl _)
                (hv_lt.trans_le hnf)
            rw [h_v₀, h_nf, hv₀]
        · refine ⟨[], ?_, ?_⟩
          · intro v hv; simp at hv
          · simp only [List.nil_append]
            rw [tseytinEquiv_sat]
            have h_nf : evalVar a nf = false := by
              simp only [evalVar, decide_eq_false_iff_not]
              intro hmem; exact absurd (ha nf hmem) (by omega)
            simp [Bool.of_not_eq_true hv₀, h_nf]
      · -- spec
        intro a ha
        have := (tseytinEquiv_sat a v₀ nf).mp ha
        constructor
        · intro h; simp only [evalFormula]; exact this.mpr h
        · intro h; simp only [evalFormula] at h; exact this.mp h
  | fand f₁ f₂ ih₁ ih₂ =>
      cases hor with | fand hor₁ hor₂ =>
      have hv₁ : formula_varsIn (fun n => n < b) f₁ :=
        fun v hv => hvars v (varInFormula.andLeft _ _ hv)
      have hv₂ : formula_varsIn (fun n => n < b) f₂ :=
        fun v hv => hvars v (varInFormula.andRight _ _ hv)
      have repr₁ := ih₁ hor₁ hv₁ nf hnf
      have mono₁ : nf ≤ (tseytin' nf f₁).2.2 := tseytin'_nf_mono nf f₁
      have repr₂ := ih₂ hor₂ hv₂ (tseytin' nf f₁).2.2 (by linarith)
      have mono₂ : (tseytin' nf f₁).2.2 ≤ (tseytin' (tseytin' nf f₁).2.2 f₂).2.2 :=
        tseytin'_nf_mono _ f₂
      obtain ⟨hcnf₁, hrv₁_lo, hrv₁_hi, hext₁, hspec₁⟩ := repr₁
      obtain ⟨hcnf₂, hrv₂_lo, hrv₂_hi, hext₂, hspec₂⟩ := repr₂
      dsimp only [tseytin']
      simp only [List.append_assoc, tseytin_formula_repr]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- cnf_varsIn: N₁ ++ N₂ ++ tseytinAnd, all vars in [0,b) ∪ [nf, nf₂+1)
        -- Use explicit intro/rcases to avoid cnf_varsIn_app typeclass issues
        intro u ⟨C, hC, hVar⟩
        rcases List.mem_append.mp hC with hC1 | hC2
        · -- C ∈ N₁
          rcases hcnf₁ u ⟨C, hC1, hVar⟩ with h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le h2 mono₂)⟩
        · rcases List.mem_append.mp hC2 with hC2a | hC3
          · -- C ∈ N₂
            rcases hcnf₂ u ⟨C, hC2a, hVar⟩ with h | ⟨h1, h2⟩
            · exact Or.inl h
            · exact Or.inr ⟨Nat.le_trans mono₁ h1, Nat.lt_succ_of_lt h2⟩
          · -- C ∈ tseytinAnd nf₂ rv₁ rv₂
            simp only [tseytinAnd, List.mem_cons, List.mem_singleton,
                       List.mem_nil_iff, or_false] at hC3
            obtain ⟨l, hl, s, heq⟩ := hVar
            rcases hC3 with rfl | rfl | rfl <;>
              (simp only [List.mem_cons, List.mem_singleton,
                          List.mem_nil_iff, or_false] at hl
               rcases hl with rfl | rfl | rfl <;>
                 (simp only [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq))
            · exact Or.inr ⟨Nat.le_trans mono₁ mono₂, Nat.lt_succ_self _⟩
            · exact Or.inr ⟨hrv₁_lo, Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hrv₁_hi mono₂)⟩
            · exact Or.inr ⟨hrv₁_lo, Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hrv₁_hi mono₂)⟩
            · exact Or.inr ⟨Nat.le_trans mono₁ mono₂, Nat.lt_succ_self _⟩
            · exact Or.inr ⟨Nat.le_trans mono₁ hrv₂_lo, Nat.lt_succ_of_lt hrv₂_hi⟩
            · exact Or.inr ⟨Nat.le_trans mono₁ hrv₂_lo, Nat.lt_succ_of_lt hrv₂_hi⟩
            · exact Or.inr ⟨hrv₁_lo, Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hrv₁_hi mono₂)⟩
            · exact Or.inr ⟨Nat.le_trans mono₁ hrv₂_lo, Nat.lt_succ_of_lt hrv₂_hi⟩
            · exact Or.inr ⟨Nat.le_trans mono₁ mono₂, Nat.lt_succ_self _⟩
      · -- nf ≤ nf₂
        exact Nat.le_trans mono₁ mono₂
      · -- nf₂ < nf₂ + 1
        exact Nat.lt_succ_self _
      · -- ext: combine extensions from both subformulas
        intro a ha
        obtain ⟨a₁', ha₁'_vars, ha₁'_sat⟩ := hext₁ a ha
        obtain ⟨a₂', ha₂'_vars, ha₂'_sat⟩ := hext₂ a ha
        -- Evaluate the representative variables under their extensions
        let rv₁_val := evalVar (a₁' ++ a) (tseytin' nf f₁).1
        let rv₂_val := evalVar (a₂' ++ a) (tseytin' (tseytin' nf f₁).2.2 f₂).1
        -- nf₂_piece: include nf₂ iff both subformulas are true
        let nf₂ := (tseytin' (tseytin' nf f₁).2.2 f₂).2.2
        let nf₂_piece : assgn := if (rv₁_val && rv₂_val) = true then [nf₂] else []
        refine ⟨nf₂_piece ++ a₂' ++ a₁', ?_, ?_⟩
        · -- vars of extension are in [nf, nf₂+1)
          intro v hv
          simp only [List.mem_append] at hv
          rcases hv with ((hv | hv) | hv)
          · -- v ∈ nf₂_piece
            simp only [nf₂_piece] at hv
            split_ifs at hv with h
            · simp only [List.mem_singleton] at hv; subst hv
              exact ⟨Nat.le_trans mono₁ mono₂, Nat.lt_succ_self _⟩
            · simp at hv
          · -- v ∈ a₂'
            obtain ⟨h1, h2⟩ := ha₂'_vars v hv
            exact ⟨Nat.le_trans mono₁ h1, Nat.lt_succ_of_lt h2⟩
          · -- v ∈ a₁'
            obtain ⟨h1, h2⟩ := ha₁'_vars v hv
            exact ⟨h1, Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le h2 mono₂)⟩
        · -- satisfiesCnf (ext ++ a) CNF: use satisfiesCnf_app to split
          rw [show (nf₂_piece ++ a₂' ++ a₁') ++ a =
                   nf₂_piece ++ (a₂' ++ (a₁' ++ a)) from by simp [List.append_assoc]]
          refine (satisfiesCnf_app _ _ _).mpr ⟨?_, (satisfiesCnf_app _ _ _).mpr ⟨?_, ?_⟩⟩
          · -- N₁ satisfied: nf₂_piece ++ a₂' is disjoint from N₁
            rw [← List.append_assoc]
            apply satisfiesCnf_prepend_notmem (nf₂_piece ++ a₂') (a₁' ++ a)
            · intro v hv
              simp only [List.mem_append, not_or]
              refine ⟨?_, ?_⟩
              · -- v ∉ nf₂_piece
                simp only [nf₂_piece]; split_ifs with h
                · simp only [List.mem_singleton]
                  intro heq; subst heq
                  rcases hcnf₁ _ hv with h | ⟨h1, h2⟩
                  · exact absurd h (Nat.not_lt.mpr
                      (Nat.le_trans hnf (Nat.le_trans mono₁ mono₂)))
                  · exact absurd (h2.trans_le mono₂) (Nat.lt_irrefl _)
                · simp
              · -- v ∉ a₂'
                intro hmem
                rcases hcnf₁ v hv with h | ⟨h1, h2⟩
                · exact absurd (ha₂'_vars v hmem).1
                    (Nat.not_le.mpr (Nat.lt_of_lt_of_le h (Nat.le_trans hnf mono₁)))
                · exact absurd (ha₂'_vars v hmem).1 (Nat.not_le.mpr h2)
            · exact ha₁'_sat
          · -- N₂ satisfied: insert a₁' (disjoint from N₂), then prepend nf₂_piece
            apply satisfiesCnf_prepend_notmem nf₂_piece
            · intro v hv
              simp only [nf₂_piece]; split_ifs with h
              · simp only [List.mem_singleton]
                intro heq; subst heq
                rcases hcnf₂ _ hv with h | ⟨h1, h2⟩
                · exact absurd h (Nat.not_lt.mpr
                    (Nat.le_trans hnf (Nat.le_trans mono₁ mono₂)))
                · exact Nat.lt_irrefl _ h2
              · simp
            · apply satisfiesCnf_insert_notmem a₂' a₁' a
              · intro v hv hmem
                rcases hcnf₂ v hv with h | ⟨h1, h2⟩
                · exact absurd (ha₁'_vars v hmem).1
                    (Nat.not_le.mpr (Nat.lt_of_lt_of_le h hnf))
                · exact absurd (ha₁'_vars v hmem).2 (Nat.not_lt.mpr h1)
              · exact ha₂'_sat
          · -- tseytinAnd satisfied: nf₂ ↔ rv₁ ∧ rv₂
            rw [tseytinAnd_sat]
            -- compute evalVar for nf₂, rv₁, rv₂ under the full assignment
            have h_rv₁ : evalVar (nf₂_piece ++ (a₂' ++ (a₁' ++ a)))
                (tseytin' nf f₁).1 = rv₁_val := by
              have hnotpfx : (tseytin' nf f₁).1 ∉ nf₂_piece := by
                simp only [nf₂_piece]; split_ifs with h
                · simp only [List.mem_singleton]; intro heq
                  exact absurd heq (Nat.ne_of_lt (Nat.lt_of_lt_of_le hrv₁_hi mono₂))
                · simp
              rw [evalVar_prepend_notmem _ _ _ hnotpfx,
                  evalVar_prepend_notmem a₂' (a₁' ++ a) _ (by
                    intro hmem
                    exact absurd (ha₂'_vars _ hmem).1 (Nat.not_le.mpr hrv₁_hi))]
            have h_rv₂ : evalVar (nf₂_piece ++ (a₂' ++ (a₁' ++ a)))
                (tseytin' (tseytin' nf f₁).2.2 f₂).1 = rv₂_val := by
              have hnotpfx : (tseytin' (tseytin' nf f₁).2.2 f₂).1 ∉ nf₂_piece := by
                simp only [nf₂_piece]; split_ifs with h
                · simp only [List.mem_singleton]; intro heq
                  exact absurd heq (Nat.ne_of_lt hrv₂_hi)
                · simp
              rw [evalVar_prepend_notmem _ _ _ hnotpfx,
                  evalVar_insert_notmem a₂' a₁' a _ (by
                    intro hmem
                    exact absurd (ha₁'_vars _ hmem).2 (Nat.not_lt.mpr hrv₂_lo))]
            have h_nf₂ : evalVar (nf₂_piece ++ (a₂' ++ (a₁' ++ a)))
                (tseytin' (tseytin' nf f₁).2.2 f₂).2.2 = (rv₁_val && rv₂_val) := by
              by_cases hboth : (rv₁_val && rv₂_val) = true
              · have hpiece : nf₂_piece = [nf₂] := if_pos hboth
                rw [hpiece, hboth]
                simp only [evalVar, List.mem_append, List.mem_singleton, decide_eq_true_eq]
                exact Or.inl rfl
              · have hpiece : nf₂_piece = [] := if_neg hboth
                rw [hpiece, Bool.of_not_eq_true hboth]
                simp only [List.nil_append, evalVar, decide_eq_false_iff_not,
                  List.mem_append, not_or]
                refine ⟨?_, ?_, ?_⟩
                · intro hmem
                  exact absurd (ha₂'_vars _ hmem).2 (Nat.lt_irrefl _)
                · intro hmem
                  exact absurd ((ha₁'_vars _ hmem).2.trans_le mono₂) (Nat.lt_irrefl _)
                · intro hmem
                  exact absurd (Nat.lt_of_lt_of_le (ha _ hmem)
                    (Nat.le_trans hnf (Nat.le_trans mono₁ mono₂))) (Nat.lt_irrefl _)
            rw [h_nf₂, h_rv₁, h_rv₂]
            simp [Bool.and_eq_true]
      · -- spec
        intro a ha
        rw [satisfiesCnf_app, satisfiesCnf_app] at ha
        obtain ⟨haN₁, haN₂, haAnd⟩ := ha
        have hAnd := (tseytinAnd_sat a _ _ _).mp haAnd
        constructor
        · intro h
          rw [evalFormula_and_iff]
          obtain ⟨h₁, h₂⟩ := hAnd.mp h
          exact ⟨(hspec₁ a haN₁).mp h₁, (hspec₂ a haN₂).mp h₂⟩
        · intro h
          apply hAnd.mpr
          rw [evalFormula_and_iff] at h
          exact ⟨(hspec₁ a haN₁).mpr h.1, (hspec₂ a haN₂).mpr h.2⟩
  | forr _ _ _ _ => cases hor
  | fneg f ih =>
      cases hor with | fneg hor' =>
      have hv' : formula_varsIn (fun n => n < b) f :=
        fun v hv => hvars v (varInFormula.neg _ hv)
      have repr := ih hor' hv' nf hnf
      have mono : nf ≤ (tseytin' nf f).2.2 := tseytin'_nf_mono nf f
      obtain ⟨hcnf, hrv_lo, hrv_hi, hext, hspec⟩ := repr
      simp only [tseytin', tseytin_formula_repr]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- cnf_varsIn: N ++ tseytinNot nf' rv, vars in [0,b) ∪ [nf, nf'+1)
        rw [cnf_varsIn_app]
        refine ⟨?_, ?_⟩
        · exact cnf_varsIn_monotonic _ _ _
            (fun v hv => hv.imp_right (fun ⟨h1, h2⟩ => ⟨h1, Nat.lt_succ_of_lt h2⟩)) hcnf
        · -- tseytinNot vars: rv and nf', both in [nf, nf'+1)
          intro u hu
          obtain ⟨C, hC, l, hl, s, heq⟩ := hu
          simp only [tseytinNot, List.mem_cons, List.mem_singleton,
                     List.mem_nil_iff, or_false] at hC
          rcases hC with rfl | rfl <;>
            (simp only [List.mem_cons, List.mem_singleton,
                        List.mem_nil_iff, or_false] at hl
             rcases hl with rfl | rfl | rfl <;>
               (simp only [Prod.mk.injEq] at heq
                obtain ⟨-, rfl⟩ := heq))
          · exact Or.inr ⟨mono, Nat.lt_succ_self _⟩
          · exact Or.inr ⟨hrv_lo, Nat.lt_succ_of_lt hrv_hi⟩
          · exact Or.inr ⟨hrv_lo, Nat.lt_succ_of_lt hrv_hi⟩
          · exact Or.inr ⟨mono, Nat.lt_succ_self _⟩
          · exact Or.inr ⟨hrv_lo, Nat.lt_succ_of_lt hrv_hi⟩
          · exact Or.inr ⟨hrv_lo, Nat.lt_succ_of_lt hrv_hi⟩
      · -- nf ≤ nf' (= (tseytin' nf f).2.2)
        exact mono
      · -- nf' < nf' + 1
        exact Nat.lt_succ_self _
      · -- ext: include nf' iff the subformula is false
        intro a ha
        obtain ⟨a', ha'_vars, ha'_sat⟩ := hext a ha
        let nf' := (tseytin' nf f).2.2
        by_cases hrv : evalVar (a' ++ a) (tseytin' nf f).1 = true
        · -- rv is true, NOT-node is false: keep a', don't add nf'
          refine ⟨a', ?_, ?_⟩
          · exact fun v hv => ⟨(ha'_vars v hv).1, Nat.lt_succ_of_lt (ha'_vars v hv).2⟩
          · refine (satisfiesCnf_app _ _ _).mpr ⟨ha'_sat, ?_⟩
            rw [tseytinNot_sat]
            have h_nf' : evalVar (a' ++ a) nf' = false := by
              simp only [evalVar, decide_eq_false_iff_not, List.mem_append, not_or]
              refine ⟨?_, ?_⟩
              · intro hmem
                exact absurd (ha'_vars _ hmem).2 (Nat.lt_irrefl _)
              · intro hmem
                exact absurd (ha _ hmem) (Nat.not_lt.mpr (Nat.le_trans hnf mono))
            rw [h_nf', hrv]; simp
        · -- rv is false, NOT-node is true: prepend [nf'] to a'
          refine ⟨[nf'] ++ a', ?_, ?_⟩
          · intro v hv
            simp only [List.mem_append, List.mem_singleton] at hv
            rcases hv with rfl | hv
            · exact ⟨mono, Nat.lt_succ_self _⟩
            · exact ⟨(ha'_vars v hv).1, Nat.lt_succ_of_lt (ha'_vars v hv).2⟩
          · rw [show ([nf'] ++ a') ++ a = [nf'] ++ (a' ++ a) from by simp [List.append_assoc]]
            refine (satisfiesCnf_app _ _ _).mpr ⟨?_, ?_⟩
            · -- N satisfied: prepend [nf'] is disjoint from N
              apply satisfiesCnf_prepend_notmem [nf'] (a' ++ a)
              · intro v hv
                simp only [List.mem_singleton]
                intro heq; subst heq
                rcases hcnf _ hv with h | ⟨h1, h2⟩
                · exact absurd h (Nat.not_lt.mpr (Nat.le_trans hnf mono))
                · exact Nat.lt_irrefl _ h2
              · exact ha'_sat
            · -- tseytinNot satisfied
              rw [tseytinNot_sat]
              have h_nf' : evalVar ([nf'] ++ (a' ++ a)) nf' = true := by
                simp [evalVar, List.mem_append, List.mem_singleton]
              have h_rv : evalVar ([nf'] ++ (a' ++ a)) (tseytin' nf f).1 =
                  evalVar (a' ++ a) (tseytin' nf f).1 := by
                rw [evalVar_prepend_notmem [nf'] (a' ++ a) _ (by
                  simp only [List.mem_singleton]; intro heq
                  exact absurd heq (Nat.ne_of_lt hrv_hi))]
              rw [h_nf', h_rv, Bool.of_not_eq_true hrv]; simp
      · -- spec
        intro a ha
        rw [satisfiesCnf_app] at ha
        obtain ⟨haN, haNot⟩ := ha
        have hNot := (tseytinNot_sat a _ _).mp haNot
        constructor
        · intro h
          simp only [evalFormula]
          cases hf : evalFormula a f
          · rfl
          · exact absurd ((hspec a haN).mpr hf) (hNot.mp h)
        · intro h
          simp only [evalFormula] at h
          apply hNot.mpr
          intro hrv
          have hf_true : evalFormula a f = true := (hspec a haN).mp hrv
          simp [evalFormula, hf_true] at h

-- ─── Step 5: The FSAT → SAT Tseytin reduction ───────────────────────────────

def FSAT_to_SAT_tseytin (f : formula) : cnf :=
  let f' := eliminateOR f
  let (rv, N) := tseytin f'
  [(true, rv), (true, rv), (true, rv)] :: N

theorem FSAT_to_SAT_tseytin_correct (f : formula) :
    FSAT f ↔ SAT (FSAT_to_SAT_tseytin f) := by
  rw [eliminateOR_FSAT]
  set f' := eliminateOR f
  set b := formula_maxVar f' + 1
  simp only [FSAT_to_SAT_tseytin, tseytin, FSAT, satisfiesFormula, SAT]
  set rv₀ := (tseytin' b f').1
  set N₀ := (tseytin' b f').2.1
  obtain ⟨_, _, _, hext₀, hspec₀⟩ :=
    tseytinP_repr f' (orFree_eliminate f) (formula_maxVar_varsIn f') b (le_refl b)
  constructor
  · intro ⟨a, ha⟩
    set a_old := boundedAssignment b a
    have ha_old : assgn_varsIn (fun n => n < b) a_old :=
      fun v hv => (mem_boundedAssignment_iff b a v).mp hv |>.1
    obtain ⟨a', ha'_vars, ha'_sat⟩ := hext₀ a_old ha_old
    have hrv₀_true : evalVar (a' ++ a_old) rv₀ = true := by
      rw [hspec₀ (a' ++ a_old) ha'_sat]
      rwa [evalFormula_append_fresh a' a_old b f'
        (fun v hv => by have := ha'_vars v hv; omega) (formula_maxVar_varsIn f'),
        evalFormula_boundedAssignment]
    refine ⟨a' ++ a_old, ?_⟩
    rw [satisfiesCnf, evalCnf_clause_iff]
    intro C hC
    simp only [List.mem_cons] at hC
    rcases hC with rfl | hC
    · rw [evalClause, List.any_cons]
      simp [evalLiteral, hrv₀_true]
    · exact (evalCnf_clause_iff _ _).mp ha'_sat C hC
  · intro ⟨a, ha⟩
    have hN_sat : satisfiesCnf a N₀ := by
      rw [satisfiesCnf, evalCnf_clause_iff]
      intro C hC
      exact (evalCnf_clause_iff a _).mp ha C (List.mem_cons_of_mem _ hC)
    have hrv : evalVar a rv₀ = true := by
      have hC := (evalCnf_clause_iff a _).mp ha [(true, rv₀), (true, rv₀), (true, rv₀)]
                  List.mem_cons_self
      simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false] at hC
      cases h : evalVar a rv₀ <;> simp_all
    exact ⟨a, (hspec₀ a hN_sat).mp hrv⟩

theorem FSAT_to_3SAT_tseytin_correct (f : formula) :
    FSAT f ↔ kSAT 3 (FSAT_to_SAT_tseytin f) := by
  rw [FSAT_to_SAT_tseytin_correct]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨by omega, ?_, ⟨a, ha⟩⟩
    rw [kCNF_clause_length 3]
    intro C hC
    simp only [FSAT_to_SAT_tseytin, tseytin] at hC
    simp only [List.mem_cons] at hC
    rcases hC with rfl | hC
    · rfl
    · exact (kCNF_clause_length 3 _).mp (tseytin'_kCNF3 _ (eliminateOR f) (orFree_eliminate f)) C hC
  · rintro ⟨_, _, hsat⟩; exact hsat

-- ─── Size bound helpers ──────────────────────────────────────────────────────

private theorem formula_size_le_encodable (f : formula) :
    formula_size f ≤ encodable.size f := by
  induction f with
  | ftrue => simp [formula_size]
  | fvar v => simp [formula_size]
  | fand _ _ ih₁ ih₂ => simp only [formula_size, encodable_size_formula_fand]; omega
  | forr _ _ ih₁ ih₂ => simp only [formula_size, encodable_size_formula_forr]; omega
  | fneg _ ih => simp only [formula_size, encodable_size_formula_fneg]; omega

private theorem formula_maxVar_lt_encodable (f : formula) :
    formula_maxVar f < encodable.size f := by
  induction f with
  | ftrue => simp [formula_maxVar]
  | fvar v => simp [formula_maxVar]
  | fand _ _ ih₁ ih₂ =>
      simp only [formula_maxVar, encodable_size_formula_fand]
      exact Nat.max_lt.mpr ⟨by linarith, by linarith⟩
  | forr _ _ ih₁ ih₂ =>
      simp only [formula_maxVar, encodable_size_formula_forr]
      exact Nat.max_lt.mpr ⟨by linarith, by linarith⟩
  | fneg _ ih =>
      simp only [formula_maxVar, encodable_size_formula_fneg]; omega

private theorem formula_maxVar_eliminateOR (f : formula) :
    formula_maxVar (eliminateOR f) = formula_maxVar f := by
  induction f with
  | ftrue => simp [eliminateOR, formula_maxVar]
  | fvar v => simp [eliminateOR, formula_maxVar]
  | fand _ _ ih₁ ih₂ => simp [eliminateOR, formula_maxVar, ih₁, ih₂]
  | forr _ _ ih₁ ih₂ => simp [eliminateOR, formula_maxVar, ih₁, ih₂]
  | fneg _ ih => simp [eliminateOR, formula_maxVar, ih]

private theorem formula_size_eliminateOR_le (f : formula) :
    formula_size (eliminateOR f) ≤ 4 * formula_size f := by
  induction f with
  | ftrue => simp [eliminateOR, formula_size]
  | fvar _ => simp [eliminateOR, formula_size]
  | fand _ _ ih₁ ih₂ => simp [eliminateOR, formula_size]; omega
  | forr _ _ ih₁ ih₂ => simp [eliminateOR, formula_size]; omega
  | fneg _ ih => simp [eliminateOR, formula_size]; omega

private theorem tseytin'_clauses_le (nf : Nat) (f : formula) :
    (tseytin' nf f).2.1.length ≤ 3 * formula_size f := by
  induction f generalizing nf with
  | ftrue => simp [tseytin', tseytinTrue, formula_size]
  | fvar _ => simp [tseytin', tseytinEquiv, formula_size]
  | fand f₁ f₂ ih₁ ih₂ =>
      have h₁ := ih₁ nf
      have h₂ := ih₂ (tseytin' nf f₁).2.2
      have hkey : (tseytin' nf (formula.fand f₁ f₂)).2.1.length =
          (tseytin' nf f₁).2.1.length + (tseytin' (tseytin' nf f₁).2.2 f₂).2.1.length + 3 := by
        have heq : (tseytin' nf (formula.fand f₁ f₂)).2.1 =
            (tseytin' nf f₁).2.1 ++ (tseytin' (tseytin' nf f₁).2.2 f₂).2.1 ++
            tseytinAnd (tseytin' (tseytin' nf f₁).2.2 f₂).2.2
                       (tseytin' nf f₁).1 (tseytin' (tseytin' nf f₁).2.2 f₂).1 := rfl
        simp only [heq, List.length_append, tseytinAnd, List.length_cons, List.length_nil]
      simp only [formula_size]; linarith
  | fneg f ih =>
      have h := ih nf
      have hkey : (tseytin' nf (formula.fneg f)).2.1.length = (tseytin' nf f).2.1.length + 2 := by
        simp [tseytin', tseytinNot, List.length_append, List.length_cons, List.length_nil]
      simp only [formula_size]; linarith
  | forr _ _ _ _ => simp [tseytin', formula_size]

private theorem tseytin'_nf_size_le (nf : Nat) (f : formula) :
    (tseytin' nf f).2.2 ≤ nf + formula_size f := by
  induction f generalizing nf with
  | ftrue => simp [tseytin', formula_size]
  | fvar _ => simp [tseytin', formula_size]
  | fand f₁ f₂ ih₁ ih₂ =>
      have h₁ := ih₁ nf
      have h₂ := ih₂ (tseytin' nf f₁).2.2
      calc (tseytin' nf (formula.fand f₁ f₂)).2.2
          = (tseytin' (tseytin' nf f₁).2.2 f₂).2.2 + 1 := rfl
        _ ≤ (tseytin' nf f₁).2.2 + formula_size f₂ + 1 :=
              Nat.add_le_add_right h₂ 1
        _ ≤ nf + formula_size f₁ + formula_size f₂ + 1 :=
              Nat.add_le_add_right (Nat.add_le_add_right h₁ (formula_size f₂)) 1
        _ = nf + formula_size (formula.fand f₁ f₂) := by simp only [formula_size]; ring
  | fneg f ih =>
      have h := ih nf
      calc (tseytin' nf (formula.fneg f)).2.2
          = (tseytin' nf f).2.2 + 1 := rfl
        _ ≤ nf + formula_size f + 1 := Nat.add_le_add_right h 1
        _ = nf + formula_size (formula.fneg f) := by simp only [formula_size]; ring
  | forr _ _ _ _ => simp [tseytin', formula_size]

private theorem one_le_encodable_size_formula (f : formula) :
    1 ≤ encodable.size f := by
  cases f <;>
    simp [encodable_size_formula_ftrue, encodable_size_formula_fvar,
          encodable_size_formula_fand, encodable_size_formula_forr,
          encodable_size_formula_fneg] <;>
    omega

private theorem encodable_size_literal_le (l : literal) :
    encodable.size l ≤ l.2 + 2 := by
  obtain ⟨b, v⟩ := l
  have hpair : encodable.size (b, v) = encodable.size b + v + 1 := rfl
  have hbool : encodable.size b ≤ 1 := by cases b <;> decide
  omega

private theorem encodable_size_clause3_le {C : clause} {M : Nat}
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

private theorem encodable_size_cnf3_le {N : cnf} {M : Nat}
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

-- ─── Size bound ─────────────────────────────────────────────────────────────

theorem FSAT_to_SAT_size_le (f : formula) :
    encodable.size (FSAT_to_SAT_tseytin f) ≤ 200 * encodable.size f ^ 2 + 300 := by
  have hn_pos : 1 ≤ encodable.size f := one_le_encodable_size_formula f
  simp only [FSAT_to_SAT_tseytin, tseytin]
  have hf'_size_le : formula_size (eliminateOR f) ≤ 4 * encodable.size f :=
    calc formula_size (eliminateOR f) ≤ 4 * formula_size f := formula_size_eliminateOR_le f
      _ ≤ 4 * encodable.size f := Nat.mul_le_mul_left 4 (formula_size_le_encodable f)
  have hb_le_n : formula_maxVar (eliminateOR f) + 1 ≤ encodable.size f := by
    linarith [formula_maxVar_eliminateOR f ▸ formula_maxVar_lt_encodable f]
  have hN_len : (tseytin' (formula_maxVar (eliminateOR f) + 1) (eliminateOR f)).2.1.length ≤
      12 * encodable.size f := by
    linarith [tseytin'_clauses_le (formula_maxVar (eliminateOR f) + 1) (eliminateOR f)]
  have hT3_le : (tseytin' (formula_maxVar (eliminateOR f) + 1) (eliminateOR f)).2.2 ≤
      5 * encodable.size f :=
    calc (tseytin' (formula_maxVar (eliminateOR f) + 1) (eliminateOR f)).2.2
        ≤ (formula_maxVar (eliminateOR f) + 1) + formula_size (eliminateOR f) :=
            tseytin'_nf_size_le _ _
      _ ≤ encodable.size f + 4 * encodable.size f :=
            Nat.add_le_add hb_le_n hf'_size_le
      _ = 5 * encodable.size f := by ring
  have hb_le_T3 := tseytin'_nf_mono (formula_maxVar (eliminateOR f) + 1) (eliminateOR f)
  have hrepr := tseytinP_repr (eliminateOR f) (orFree_eliminate f)
    (formula_maxVar_varsIn (eliminateOR f)) (formula_maxVar (eliminateOR f) + 1) (le_refl _)
  have hrv_lt := hrepr.2.2.1
  have hN_vars : ∀ v, varInCnf v (tseytin' (formula_maxVar (eliminateOR f) + 1) (eliminateOR f)).2.1 →
      v < (tseytin' (formula_maxVar (eliminateOR f) + 1) (eliminateOR f)).2.2 := by
    intro v hv
    rcases hrepr.1 v hv with h | ⟨_, h⟩
    · exact lt_of_lt_of_le h hb_le_T3
    · exact h
  have hN_kCNF : ∀ C ∈ (tseytin' (formula_maxVar (eliminateOR f) + 1) (eliminateOR f)).2.1,
      C.length = 3 :=
    (kCNF_clause_length 3 _).mp (tseytin'_kCNF3 _ _ (orFree_eliminate f))
  set n := encodable.size f
  set b := formula_maxVar (eliminateOR f) + 1
  set N := (tseytin' b (eliminateOR f)).2.1
  set T3 := (tseytin' b (eliminateOR f)).2.2
  set rv := (tseytin' b (eliminateOR f)).1
  have hN_size : encodable.size N ≤ 180 * n ^ 2 + 84 * n :=
    calc encodable.size N
        ≤ N.length * (3 * (T3 + 1) + 4) :=
            encodable_size_cnf3_le hN_kCNF (fun v hv => hN_vars v hv)
      _ ≤ 12 * n * (3 * (5 * n + 1) + 4) :=
            Nat.mul_le_mul hN_len
              (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hT3_le 1)) 4)
      _ = 180 * n ^ 2 + 84 * n := by ring
  have hrv_size : encodable.size ((true, rv) : literal) = rv + 2 := by
    show (1 : Nat) + rv + 1 = rv + 2; omega
  have hhead_size : encodable.size ([(true, rv), (true, rv), (true, rv)] : clause) = 3 * rv + 9 := by
    simp only [encodable_size_list_cons, encodable_size_list_nil, hrv_size]; ring
  have h_rv_bound : 3 * rv + 3 ≤ 15 * n :=
    calc 3 * rv + 3 = 3 * (rv + 1) := by ring
      _ ≤ 3 * T3 := Nat.mul_le_mul_left 3 hrv_lt
      _ ≤ 3 * (5 * n) := Nat.mul_le_mul_left 3 hT3_le
      _ = 15 * n := by ring
  calc encodable.size ([(true, rv), (true, rv), (true, rv)] :: N)
      = encodable.size [(true, rv), (true, rv), (true, rv)] + 1 + encodable.size N :=
          encodable_size_list_cons _ _
    _ = 3 * rv + 9 + 1 + encodable.size N := by rw [hhead_size]
    _ ≤ 200 * n ^ 2 + 300 := by
        have h20 : 99 * n ≤ 20 * n ^ 2 + 293 := by
          have : (99 : ℤ) * n ≤ 20 * (n : ℤ) ^ 2 + 293 := by
            nlinarith [sq_nonneg ((n : ℤ) - 3)]
          exact_mod_cast this
        set n2 := n ^ 2
        linarith [hN_size, h_rv_bound, h20]

-- ─── Final polynomial reduction theorems ────────────────────────────────────

theorem FSAT_to_SAT_poly : FSAT ⪯p SAT :=
  ⟨⟨FSAT_to_SAT_tseytin,
    ⟨⟨fun n => 200 * n ^ 2 + 300,
      ⟨2, ⟨201, 18, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩,
      fun a b h => by nlinarith [Nat.pow_le_pow_left h 2],
      FSAT_to_SAT_size_le⟩⟩,
    FSAT_to_SAT_tseytin_correct⟩⟩

theorem FSAT_to_3SAT_poly : FSAT ⪯p kSAT 3 :=
  ⟨⟨FSAT_to_SAT_tseytin,
    ⟨⟨fun n => 200 * n ^ 2 + 300,
      ⟨2, ⟨201, 18, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩,
      fun a b h => by nlinarith [Nat.pow_le_pow_left h 2],
      FSAT_to_SAT_size_le⟩⟩,
    FSAT_to_3SAT_tseytin_correct⟩⟩

-- ─── Legacy constructions ───────────────────────────────────────────────────

def FSAT_search (f : formula) : Bool :=
  (allAssignments (formula_maxVar f + 1)).any (fun a => evalFormula a f)

theorem FSAT_search_complete (f : formula) : FSAT f → FSAT_search f = true := by
  rintro ⟨a, ha⟩
  exact List.any_eq_true.mpr ⟨_, boundedAssignment_mem_allAssignments _ a,
    (evalFormula_boundedAssignment a f).trans ha⟩

def FSAT_to_SAT_yes : cnf := [[(true, 0)]]
def FSAT_to_SAT_no : cnf := [[]]
theorem FSAT_to_SAT_yes_sat : SAT FSAT_to_SAT_yes :=
  ⟨[0], by simp [FSAT_to_SAT_yes, satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar]⟩

def FSAT_to_3SAT_yes : cnf := [[(true, 0), (true, 1), (true, 2)]]
def FSAT_to_3SAT_no : cnf :=
  [[(true, 0), (true, 1), (true, 2)],
   [(false, 0), (false, 1), (false, 2)],
   [(true, 0), (true, 1), (false, 2)],
   [(true, 0), (false, 1), (true, 2)],
   [(false, 0), (true, 1), (true, 2)],
   [(true, 0), (false, 1), (false, 2)],
   [(false, 0), (true, 1), (false, 2)],
   [(false, 0), (false, 1), (true, 2)]]
theorem FSAT_to_3SAT_yes_sat : kSAT 3 FSAT_to_3SAT_yes :=
  ⟨by decide, kCNF.cons _ _ rfl kCNF.nil,
   ⟨[0], by simp [FSAT_to_3SAT_yes, satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar]⟩⟩
