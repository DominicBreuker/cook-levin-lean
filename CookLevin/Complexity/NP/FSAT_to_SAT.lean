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

-- If v ∉ prefix, prepending prefix doesn't change evalVar
private theorem evalVar_prepend_notmem (prefix base : assgn) (v : Nat) (h : v ∉ prefix) :
    evalVar (prefix ++ base) v = evalVar base v := by
  simp [evalVar, List.mem_append, h]

-- Inserting a middle assignment (disjoint from outer) doesn't change evalVar
private theorem evalVar_insert_notmem (outer middle inner : assgn) (v : Nat)
    (h : v ∉ middle) :
    evalVar (outer ++ (middle ++ inner)) v = evalVar (outer ++ inner) v := by
  simp only [evalVar, List.mem_append]
  by_cases hout : v ∈ outer <;> simp [hout, h]

-- Prepending a disjoint assignment (no shared vars with N) preserves satisfiability
private theorem satisfiesCnf_prepend_notmem (prefix base : assgn) (N : cnf)
    (hdisjoint : ∀ v, varInCnf v N → v ∉ prefix)
    (hsat : satisfiesCnf base N) :
    satisfiesCnf (prefix ++ base) N := by
  rw [satisfiesCnf, evalCnf_clause_iff]
  intro C hC
  rw [evalClause_literal_iff]
  obtain ⟨l, hl, heval⟩ := (evalClause_literal_iff base C).mp
    ((evalCnf_clause_iff base N).mp hsat C hC)
  rcases l with ⟨s, v⟩
  exact ⟨(s, v), hl, by
    simp only [evalLiteral] at *
    rw [evalVar_prepend_notmem prefix base v
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
                (fun v hv => by simp only [List.mem_singleton] at hv; subst hv)
                (hv_lt.trans_le hnf)
            simp [h_v₀, h_nf, hv₀]
        · refine ⟨[], ?_, ?_⟩
          · intro v hv; simp at hv
          · simp only [List.nil_append]
            rw [tseytinEquiv_sat]
            have h_nf : evalVar a nf = false := by
              simp only [evalVar, decide_eq_false_iff_not]
              intro hmem; exact absurd (ha nf hmem) (by omega)
            simp [Bool.not_eq_true.mp hv₀, h_nf]
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
      simp only [tseytin', ← List.append_assoc, tseytin_formula_repr]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- cnf_varsIn: N₁ ++ N₂ ++ tseytinAnd, all vars in [0,b) ∪ [nf, nf₂+1)
        rw [cnf_varsIn_app, cnf_varsIn_app]
        refine ⟨?_, ?_, ?_⟩
        · exact cnf_varsIn_monotonic _ _ _
            (fun v hv => hv.imp_right (fun ⟨h1, h2⟩ => ⟨h1, by linarith⟩)) hcnf₁
        · exact cnf_varsIn_monotonic _ _ _
            (fun v hv => hv.imp_right (fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩)) hcnf₂
        · -- tseytinAnd vars: rv₁, rv₂, nf₂ – all in [nf, nf₂+1)
          intro u hu
          obtain ⟨C, hC, l, hl, s, heq⟩ := hu
          simp only [tseytinAnd, List.mem_cons, List.mem_singleton,
                     List.mem_nil_iff, or_false] at hC
          rcases hC with rfl | rfl | rfl <;>
            (simp only [List.mem_cons, List.mem_singleton,
                        List.mem_nil_iff, or_false] at hl
             rcases hl with rfl | rfl | rfl <;>
               (simp only [Prod.mk.injEq] at heq
                obtain ⟨-, rfl⟩ := heq)) <;>
            exact Or.inr ?_
          · exact ⟨by linarith, Nat.lt_succ_self _⟩
          · exact ⟨hrv₁_lo, by linarith⟩
          · exact ⟨hrv₁_lo, by linarith⟩
          · exact ⟨by linarith, by linarith⟩
          · exact ⟨by linarith, by linarith⟩
          · exact ⟨by linarith, Nat.lt_succ_self _⟩
          · exact ⟨hrv₁_lo, by linarith⟩
          · exact ⟨hrv₁_lo, by linarith⟩
          · exact ⟨by linarith, by linarith⟩
      · -- nf ≤ nf₂
        linarith
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
        let nf₂_piece : assgn := if rv₁_val && rv₂_val then [nf₂] else []
        refine ⟨nf₂_piece ++ a₂' ++ a₁', ?_, ?_⟩
        · -- vars of extension are in [nf, nf₂+1)
          intro v hv
          simp only [List.mem_append] at hv
          rcases hv with ((hv | hv) | hv)
          · -- v ∈ nf₂_piece
            simp only [nf₂_piece] at hv
            split_ifs at hv with h
            · simp only [List.mem_singleton] at hv; subst hv
              exact ⟨by linarith, Nat.lt_succ_self _⟩
            · simp at hv
          · -- v ∈ a₂'
            obtain ⟨h1, h2⟩ := ha₂'_vars v hv
            exact ⟨by linarith, by omega⟩
          · -- v ∈ a₁'
            obtain ⟨h1, h2⟩ := ha₁'_vars v hv
            exact ⟨h1, by linarith⟩
        · -- satisfiesCnf (ext ++ a) CNF
          rw [show (nf₂_piece ++ a₂' ++ a₁') ++ a =
                   nf₂_piece ++ (a₂' ++ (a₁' ++ a)) from by simp [List.append_assoc]]
          rw [satisfiesCnf, evalCnf_app_iff, evalCnf_app_iff]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · -- N₁ satisfied: nf₂_piece ++ a₂' is disjoint from N₁
            apply satisfiesCnf_prepend_notmem (nf₂_piece ++ a₂') (a₁' ++ a)
            · intro v hv
              simp only [List.mem_append]
              push_neg
              refine ⟨?_, ?_⟩
              · -- v ∉ nf₂_piece
                simp only [nf₂_piece]; split_ifs with h
                · simp only [List.mem_singleton]
                  intro heq; subst heq
                  rcases hcnf₁ v hv with h | ⟨h1, h2⟩ <;> omega
                · simp
              · -- v ∉ a₂'
                intro hmem
                rcases hcnf₁ v hv with h | ⟨h1, h2⟩
                · exact absurd (ha₂'_vars v hmem).1 (by omega)
                · exact absurd (ha₂'_vars v hmem).1 (by omega)
            · exact ha₁'_sat
          · -- N₂ satisfied: first insert a₁' (disjoint from N₂), then prepend nf₂_piece
            apply satisfiesCnf_prepend_notmem nf₂_piece
            · intro v hv
              simp only [nf₂_piece]; split_ifs with h
              · simp only [List.mem_singleton]
                intro heq; subst heq
                rcases hcnf₂ v hv with h | ⟨h1, h2⟩ <;> omega
              · simp
            · apply satisfiesCnf_insert_notmem a₂' a₁' a
              · intro v hv
                intro hmem
                rcases hcnf₂ v hv with h | ⟨h1, h2⟩
                · exact absurd (ha₁'_vars v hmem).1 (by omega)
                · exact absurd (ha₁'_vars v hmem).2 (by omega)
              · exact ha₂'_sat
          · -- tseytinAnd satisfied: nf₂ ↔ rv₁ ∧ rv₂
            rw [tseytinAnd_sat]
            -- compute evalVar for nf₂, rv₁, rv₂ under the full assignment
            have h_rv₁ : evalVar (nf₂_piece ++ (a₂' ++ (a₁' ++ a)))
                (tseytin' nf f₁).1 = rv₁_val := by
              have hnotpfx : (tseytin' nf f₁).1 ∉ nf₂_piece := by
                simp only [nf₂_piece]; split_ifs with h
                · simp only [List.mem_singleton]; intro heq; omega
                · simp
              rw [evalVar_prepend_notmem _ _ _ hnotpfx,
                  evalVar_prepend_notmem a₂' (a₁' ++ a) _ (by
                    intro hmem; exact absurd (ha₂'_vars _ hmem).1 (by omega))]
            have h_rv₂ : evalVar (nf₂_piece ++ (a₂' ++ (a₁' ++ a)))
                (tseytin' (tseytin' nf f₁).2.2 f₂).1 = rv₂_val := by
              have hnotpfx : (tseytin' (tseytin' nf f₁).2.2 f₂).1 ∉ nf₂_piece := by
                simp only [nf₂_piece]; split_ifs with h
                · simp only [List.mem_singleton]; intro heq; omega
                · simp
              rw [evalVar_prepend_notmem _ _ _ hnotpfx,
                  evalVar_insert_notmem a₂' a₁' a _ (by
                    intro hmem; exact absurd (ha₁'_vars _ hmem).2 (by omega))]
            have h_nf₂ : evalVar (nf₂_piece ++ (a₂' ++ (a₁' ++ a)))
                (tseytin' (tseytin' nf f₁).2.2 f₂).2.2 = rv₁_val && rv₂_val := by
              by_cases hboth : rv₁_val && rv₂_val = true
              · have : nf₂_piece = [nf₂] := if_pos hboth
                rw [this, hboth]
                simp [evalVar, List.mem_append, List.mem_singleton]
              · have : nf₂_piece = [] := if_neg hboth
                rw [this, Bool.not_eq_true.mp hboth]
                simp only [List.nil_append]
                simp only [evalVar, decide_eq_false_iff_not, List.mem_append]
                push_neg
                exact ⟨⟨fun hmem => absurd (ha₂'_vars _ hmem).2 (by omega),
                         fun hmem => absurd (ha₁'_vars _ hmem).2 (by omega)⟩,
                        fun hmem => absurd (ha _ hmem) (by omega)⟩
            rw [h_nf₂, h_rv₁, h_rv₂]
            simp [Bool.and_eq_true]
      · -- spec
        intro a ha
        rw [satisfiesCnf, evalCnf_app_iff, evalCnf_app_iff] at ha
        obtain ⟨⟨haN₁_raw, haN₂_raw⟩, haAnd_raw⟩ := ha
        have haN₁ : satisfiesCnf a (tseytin' nf f₁).2.1 := haN₁_raw
        have haN₂ : satisfiesCnf a (tseytin' (tseytin' nf f₁).2.2 f₂).2.1 := haN₂_raw
        have haAnd : satisfiesCnf a (tseytinAnd
            (tseytin' (tseytin' nf f₁).2.2 f₂).2.2
            (tseytin' nf f₁).1
            (tseytin' (tseytin' nf f₁).2.2 f₂).1) := haAnd_raw
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
            (fun v hv => hv.imp_right (fun ⟨h1, h2⟩ => ⟨h1, by linarith⟩)) hcnf
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
                obtain ⟨-, rfl⟩ := heq)) <;>
            exact Or.inr ?_
          · exact ⟨by linarith, Nat.lt_succ_self _⟩
          · exact ⟨hrv_lo, by linarith⟩
          · exact ⟨hrv_lo, by linarith⟩
          · exact ⟨by linarith, Nat.lt_succ_self _⟩
          · exact ⟨hrv_lo, by linarith⟩
          · exact ⟨hrv_lo, by linarith⟩
      · -- nf ≤ nf' (= (tseytin' nf f).2.2)
        exact mono
      · -- nf' < nf' + 1
        exact Nat.lt_succ_self _
      · -- ext: include nf' iff the subformula is false
        intro a ha
        obtain ⟨a', ha'_vars, ha'_sat⟩ := hext a ha
        let nf' := (tseytin' nf f).2.2
        let rv_val := evalVar (a' ++ a) (tseytin' nf f).1
        by_cases hrv : rv_val = true
        · -- rv is true, NOT-node is false: keep a', don't add nf'
          refine ⟨a', ?_, ?_⟩
          · exact fun v hv => ⟨(ha'_vars v hv).1, by linarith [(ha'_vars v hv).2]⟩
          · rw [satisfiesCnf, evalCnf_app_iff]
            refine ⟨ha'_sat, ?_⟩
            rw [tseytinNot_sat]
            have h_nf' : evalVar (a' ++ a) nf' = false := by
              simp only [evalVar, decide_eq_false_iff_not, List.mem_append]
              push_neg
              exact ⟨fun hmem => absurd (ha'_vars _ hmem).2 (by omega),
                     fun hmem => absurd (ha _ hmem) (by omega)⟩
            rw [h_nf', hrv]; simp
        · -- rv is false, NOT-node is true: prepend [nf'] to a'
          refine ⟨[nf'] ++ a', ?_, ?_⟩
          · intro v hv
            simp only [List.mem_append, List.mem_singleton] at hv
            rcases hv with rfl | hv
            · exact ⟨mono, Nat.lt_succ_self _⟩
            · exact ⟨(ha'_vars v hv).1, by linarith [(ha'_vars v hv).2]⟩
          · rw [show ([nf'] ++ a') ++ a = [nf'] ++ (a' ++ a) from by simp [List.append_assoc]]
            rw [satisfiesCnf, evalCnf_app_iff]
            refine ⟨?_, ?_⟩
            · -- N satisfied: prepend [nf'] is disjoint from N
              apply satisfiesCnf_prepend_notmem [nf'] (a' ++ a)
              · intro v hv
                simp only [List.mem_singleton]
                intro heq; subst heq
                rcases hcnf v hv with h | ⟨h1, h2⟩ <;> omega
              · exact ha'_sat
            · -- tseytinNot satisfied
              rw [tseytinNot_sat]
              have h_nf' : evalVar ([nf'] ++ (a' ++ a)) nf' = true := by
                simp [evalVar, List.mem_append, List.mem_singleton]
              have h_rv : evalVar ([nf'] ++ (a' ++ a)) (tseytin' nf f).1 = rv_val := by
                rw [evalVar_prepend_notmem [nf'] (a' ++ a) _ (by
                  simp only [List.mem_singleton]; intro heq; omega)]
              rw [h_nf', h_rv, Bool.not_eq_true.mp hrv]; simp
      · -- spec
        intro a ha
        rw [satisfiesCnf, evalCnf_app_iff] at ha
        obtain ⟨haN_raw, haNot_raw⟩ := ha
        have haN : satisfiesCnf a (tseytin' nf f).2.1 := haN_raw
        have haNot : satisfiesCnf a (tseytinNot (tseytin' nf f).2.2 (tseytin' nf f).1) :=
          haNot_raw
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
          exact absurd h (by simp [(hspec a haN).mp hrv])

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
    rw [satisfiesCnf, ← evalCnf_clause_iff]
    intro C hC
    simp only [List.mem_cons] at hC
    rcases hC with rfl | hC
    · rw [evalClause, List.any_cons]
      simp [evalLiteral, hrv₀_true]
    · exact (evalCnf_clause_iff _ _).mp ha'_sat C hC
  · intro ⟨a, ha⟩
    have hN_sat : satisfiesCnf a N₀ := by
      rw [satisfiesCnf, ← evalCnf_clause_iff]
      intro C hC
      exact (evalCnf_clause_iff a _).mp ha C (List.mem_cons_of_mem _ hC)
    have hrv : evalVar a rv₀ = true := by
      have hC := (evalCnf_clause_iff a _).mp ha [(true, rv₀), (true, rv₀), (true, rv₀)]
                  (List.mem_cons_self _ _)
      simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false] at hC
      cases h : evalVar a rv₀ <;> simp_all
    exact ⟨a, (hspec₀ a hN_sat).mp hrv⟩

theorem FSAT_to_3SAT_tseytin_correct (f : formula) :
    FSAT f ↔ kSAT 3 (FSAT_to_SAT_tseytin f) := by
  rw [FSAT_to_SAT_tseytin_correct]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨by omega, ?_, ⟨a, ha⟩⟩
    rw [kCNF_clause_length]
    intro C hC
    simp only [FSAT_to_SAT_tseytin, tseytin] at hC
    simp only [List.mem_cons] at hC
    rcases hC with rfl | hC
    · rfl
    · exact kCNF_clause_length.mp (tseytin'_kCNF3 _ (eliminateOR f) (orFree_eliminate f)) C hC
  · rintro ⟨_, _, hsat⟩; exact hsat

-- ─── Size bound ─────────────────────────────────────────────────────────────

theorem FSAT_to_SAT_size_le (f : formula) :
    encodable.size (FSAT_to_SAT_tseytin f) ≤ encodable.size f ^ 2 + 200 := by
  sorry

-- ─── Final polynomial reduction theorems ────────────────────────────────────

theorem FSAT_to_SAT_poly : FSAT ⪯p SAT :=
  ⟨⟨FSAT_to_SAT_tseytin,
    ⟨⟨fun n => n ^ 2 + 200,
      ⟨2, ⟨2, 15, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩,
      fun a b h => by nlinarith [Nat.pow_le_pow_left h 2],
      FSAT_to_SAT_size_le⟩⟩,
    FSAT_to_SAT_tseytin_correct⟩⟩

theorem FSAT_to_3SAT_poly : FSAT ⪯p kSAT 3 :=
  ⟨⟨FSAT_to_SAT_tseytin,
    ⟨⟨fun n => n ^ 2 + 200,
      ⟨2, ⟨2, 15, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩,
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
