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

-- ─── Size bound ─────────────────────────────────────────────────────────────

/-! ### Helpers for the size bound

We bound the Tseytin output as follows.  Let `S = encodable.size f` and write
`f' = eliminateOR f`.  Then:

* `formula_size f ≤ S` and `formula_maxVar f ≤ S` (a constructor / variable
  occurrence each contribute at least 1 to the encoding size).
* `eliminateOR` leaves `formula_maxVar` unchanged and at most triples
  `formula_size`.
* `(tseytin' nf f').2.2 ≤ nf + formula_size f'` (the fresh-variable counter
  increases by at most one per orFree constructor).
* `(tseytin' nf f').1 < (tseytin' nf f').2.2` (the representative is a fresh
  variable allocated during the recursive call).
* Each Tseytin gadget produces a 3-CNF; its encoded size is therefore at most
  `30 * (max var + 3)` per clause, and a 3-CNF has at most three new clauses
  per formula constructor.

Combining yields `encodable.size N ≤ 30 · formula_size f' · (nf + formula_size f')`,
which after substituting the bounds above becomes
`≤ 360 · S² + 102 · S + 13 ≤ 500 · S² + 100`.  We use `500 · n² + 100` as the
target polynomial so the arithmetic has room. -/

private theorem formula_size_le_encodable (f : formula) :
    formula_size f ≤ encodable.size f := by
  induction f with
  | ftrue => simp [formula_size]
  | fvar v => simp [formula_size]; omega
  | fand _ _ ih₁ ih₂ => simp [formula_size]; omega
  | forr _ _ ih₁ ih₂ => simp [formula_size]; omega
  | fneg _ ih => simp [formula_size]; omega

private theorem formula_maxVar_le_encodable (f : formula) :
    formula_maxVar f ≤ encodable.size f := by
  induction f with
  | ftrue => simp [formula_maxVar]
  | fvar v => simp [formula_maxVar]
  | fand _ _ ih₁ ih₂ => simp [formula_maxVar]; omega
  | forr _ _ ih₁ ih₂ => simp [formula_maxVar]; omega
  | fneg _ ih => simp [formula_maxVar]; omega

private theorem eliminateOR_maxVar (f : formula) :
    formula_maxVar (eliminateOR f) = formula_maxVar f := by
  induction f with
  | ftrue => rfl
  | fvar _ => rfl
  | fand _ _ ih₁ ih₂ => simp [eliminateOR, formula_maxVar, ih₁, ih₂]
  | forr _ _ ih₁ ih₂ => simp [eliminateOR, formula_maxVar, ih₁, ih₂]
  | fneg _ ih => simp [eliminateOR, formula_maxVar, ih]

private theorem eliminateOR_size_le (f : formula) :
    formula_size (eliminateOR f) ≤ 3 * formula_size f := by
  induction f with
  | ftrue => simp [eliminateOR, formula_size]
  | fvar _ => simp [eliminateOR, formula_size]
  | fand _ _ ih₁ ih₂ => simp [eliminateOR, formula_size]; omega
  | forr _ _ ih₁ ih₂ => simp [eliminateOR, formula_size]; omega
  | fneg _ ih => simp [eliminateOR, formula_size]; omega

private theorem tseytin'_nf_bound (nf : Nat) (f : formula) :
    (tseytin' nf f).2.2 ≤ nf + formula_size f := by
  induction f generalizing nf with
  | ftrue => simp [tseytin', formula_size]
  | fvar _ => simp [tseytin', formula_size]
  | forr _ _ _ _ => simp [tseytin', formula_size]
  | fand f₁ f₂ ih₁ ih₂ =>
      simp only [tseytin', formula_size]
      have h₁ := ih₁ nf
      have h₂ := ih₂ (tseytin' nf f₁).2.2
      omega
  | fneg f ih =>
      simp only [tseytin', formula_size]
      have h := ih nf
      omega

private theorem tseytin'_rv_lt_nf' (nf : Nat) (f : formula) (hor : orFree f) :
    (tseytin' nf f).1 < (tseytin' nf f).2.2 := by
  induction f generalizing nf with
  | ftrue => simp [tseytin']
  | fvar _ => simp [tseytin']
  | fand f₁ f₂ ih₁ ih₂ =>
      cases hor with | fand _ _ =>
      simp [tseytin']
  | fneg f ih =>
      cases hor with | fneg hf =>
      simp only [tseytin']
      have := ih nf hf
      omega
  | forr _ _ _ _ => cases hor

/-- Helper: encodable.size of a literal `(b, v)` with `v ≤ V` is at most `V + 2`. -/
private theorem encodable_size_lit_le (b : Bool) (v V : Nat) (hv : v ≤ V) :
    encodable.size ((b, v) : literal) ≤ V + 2 := by
  show encodable.size b + encodable.size v + 1 ≤ V + 2
  have hsv : (encodable.size v : Nat) = v := rfl
  have hsb : encodable.size b ≤ 1 := by
    cases b
    · show (0 : Nat) ≤ 1; omega
    · show (1 : Nat) ≤ 1; omega
  rw [hsv]; omega

/-- For any list whose elements all have `encodable.size ≤ M`,
`encodable.size xs ≤ xs.length * (M + 1)`. -/
private theorem encodable_size_list_le_length_mul {α : Type _} [encodable α]
    (M : Nat) : ∀ (xs : List α), (∀ x ∈ xs, encodable.size x ≤ M) →
      encodable.size xs ≤ xs.length * (M + 1)
  | [], _ => by simp [encodable.size]
  | x :: xs, h => by
      have hx : encodable.size x ≤ M := h x (by simp)
      have hxs : ∀ y ∈ xs, encodable.size y ≤ M := fun y hy => h y (by simp [hy])
      have ih := encodable_size_list_le_length_mul M xs hxs
      rw [encodable_size_list_cons, List.length_cons]
      calc encodable.size x + 1 + encodable.size xs
          ≤ M + 1 + encodable.size xs := by omega
        _ ≤ M + 1 + xs.length * (M + 1) := by omega
        _ = (xs.length + 1) * (M + 1) := by ring

/-- Bound on the encoded size of a single 3-CNF clause whose variables are all `≤ V`. -/
private theorem clause_size_bound_of_vars_le (C : clause) (V : Nat)
    (hk : C.length = 3) (h : ∀ l ∈ C, l.2 ≤ V) :
    encodable.size C ≤ 3 * (V + 3) := by
  have := encodable_size_list_le_length_mul (V + 2) C (by
    intro l hl
    rcases l with ⟨b, v⟩
    exact encodable_size_lit_le b v V (h (b, v) hl))
  rw [hk] at this
  -- this : encodable.size C ≤ 3 * (V + 2 + 1) = 3 * (V + 3)
  have : encodable.size C ≤ 3 * (V + 2 + 1) := by linarith
  linarith

/-- A 3-CNF whose every variable is `≤ V` has encoded size `≤ |N| * (3V + 10)`. -/
private theorem cnf_size_bound_of_3CNF_vars_le (N : cnf) (V : Nat)
    (hk : kCNF 3 N) (hvars : ∀ v, varInCnf v N → v ≤ V) :
    encodable.size N ≤ N.length * (3 * V + 10) := by
  have hclen : ∀ C ∈ N, C.length = 3 := (kCNF_clause_length 3 N).mp hk
  have := encodable_size_list_le_length_mul (3 * (V + 3)) N (by
    intro C hC
    apply clause_size_bound_of_vars_le C V (hclen C hC)
    intro l hl
    -- l ∈ C, C ∈ N, so l.2 is a var in N
    rcases l with ⟨s, v⟩
    exact hvars v ⟨C, hC, (s, v), hl, s, rfl⟩)
  -- this : encodable.size N ≤ N.length * (3*(V+3) + 1)
  have hbound : 3 * (V + 3) + 1 ≤ 3 * V + 10 := by linarith
  calc encodable.size N
      ≤ N.length * (3 * (V + 3) + 1) := this
    _ ≤ N.length * (3 * V + 10) := Nat.mul_le_mul_left _ hbound

/-- Length bound for the Tseytin CNF: at most `3 * formula_size f` clauses. -/
private theorem tseytin'_length_le (nf : Nat) (f : formula) (hor : orFree f) :
    (tseytin' nf f).2.1.length ≤ 3 * formula_size f := by
  induction f generalizing nf with
  | ftrue => simp [tseytin', tseytinTrue, formula_size]
  | fvar v => simp [tseytin', tseytinEquiv, formula_size]
  | forr _ _ _ _ => cases hor
  | fand f₁ f₂ ih₁ ih₂ =>
      cases hor with | fand h₁ h₂ =>
      simp only [tseytin', List.length_append, List.length_append,
                 tseytinAnd, List.length_cons, List.length_nil, formula_size]
      have e₁ := ih₁ nf h₁
      have e₂ := ih₂ (tseytin' nf f₁).2.2 h₂
      omega
  | fneg f ih =>
      cases hor with | fneg h =>
      simp only [tseytin', List.length_append, tseytinNot,
                 List.length_cons, List.length_nil, formula_size]
      have e := ih nf h
      omega

/-- Variable bound: every variable in the Tseytin CNF is `< nf + formula_size f`.
This follows from `tseytin_formula_repr` combined with `tseytin'_nf_bound`. -/
private theorem tseytin'_var_bound (b nf : Nat) (f : formula) (hor : orFree f)
    (hvars : formula_varsIn (fun n => n < b) f) (hb : b ≤ nf)
    (v : var) (hv : varInCnf v (tseytin' nf f).2.1) :
    v < nf + formula_size f := by
  obtain ⟨hcnf, _, _, _, _⟩ := tseytinP_repr f hor hvars nf hb
  rcases hcnf v hv with h | ⟨_, h⟩
  · -- v < b ≤ nf ≤ nf + formula_size f
    have : nf ≤ nf + formula_size f := Nat.le_add_right _ _
    omega
  · -- nf ≤ v < (tseytin' nf f).2.2 ≤ nf + formula_size f
    have := tseytin'_nf_bound nf f
    omega

/-- Main bound: the Tseytin CNF has size `≤ 3 * size f * (3 * (nf + size f) + 10)`. -/
private theorem tseytin'_encSize_bound (b nf : Nat) (f : formula)
    (hor : orFree f) (hvars : formula_varsIn (fun n => n < b) f) (hb : b ≤ nf) :
    encodable.size (tseytin' nf f).2.1 ≤
      3 * formula_size f * (3 * (nf + formula_size f) + 10) := by
  set V := nf + formula_size f - 1 with hV_def
  have hkCNF : kCNF 3 (tseytin' nf f).2.1 := tseytin'_kCNF3 nf f hor
  -- Every variable in N is < nf + formula_size f, so ≤ nf + formula_size f - 1 = V.
  -- But for `V` we need a value, not a strict bound. Use the simpler bound:
  -- every var is ≤ nf + formula_size f (loose).
  have hVarsLe : ∀ v, varInCnf v (tseytin' nf f).2.1 → v ≤ nf + formula_size f := by
    intro v hv
    have := tseytin'_var_bound b nf f hor hvars hb v hv
    omega
  have hSize := cnf_size_bound_of_3CNF_vars_le (tseytin' nf f).2.1 (nf + formula_size f)
                  hkCNF hVarsLe
  have hLen := tseytin'_length_le nf f hor
  calc encodable.size (tseytin' nf f).2.1
      ≤ (tseytin' nf f).2.1.length * (3 * (nf + formula_size f) + 10) := hSize
    _ ≤ (3 * formula_size f) * (3 * (nf + formula_size f) + 10) :=
        Nat.mul_le_mul_right _ hLen

theorem FSAT_to_SAT_size_le (f : formula) :
    encodable.size (FSAT_to_SAT_tseytin f) ≤ 500 * encodable.size f ^ 2 + 100 := by
  set S := encodable.size f
  -- Names and basic bounds
  set f' := eliminateOR f with hf'_def
  have hor : orFree f' := orFree_eliminate f
  have hvars : formula_varsIn (fun n => n < formula_maxVar f' + 1) f' :=
    formula_maxVar_varsIn f'
  set b := formula_maxVar f' + 1 with hb_def
  -- Numerical bounds linking `formula_size` / `formula_maxVar` of `f'` to `S`.
  have hSize_f : formula_size f ≤ S := formula_size_le_encodable f
  have hMaxVar_f : formula_maxVar f ≤ S := formula_maxVar_le_encodable f
  have hSize_f' : formula_size f' ≤ 3 * formula_size f := eliminateOR_size_le f
  have hMaxVar_f' : formula_maxVar f' = formula_maxVar f := eliminateOR_maxVar f
  have hb_le : b ≤ S + 1 := by rw [hb_def, hMaxVar_f']; omega
  have hsf'_le : formula_size f' ≤ 3 * S := by omega
  -- Unfold the reduction.
  show encodable.size (let f' := eliminateOR f
                       let (rv, N, _) := tseytin' (formula_maxVar f' + 1) f'
                       [(true, rv), (true, rv), (true, rv)] :: N) ≤
    500 * S ^ 2 + 100
  -- Tseytin output structure
  set rv := (tseytin' b f').1 with hrv_def
  set N := (tseytin' b f').2.1 with hN_def
  set nf' := (tseytin' b f').2.2 with hnf'_def
  have hrv_lt_nf' : rv < nf' := tseytin'_rv_lt_nf' b f' hor
  have hnf'_le : nf' ≤ b + formula_size f' := tseytin'_nf_bound b f'
  have hrv_le : rv ≤ b + formula_size f' - 1 := by omega
  have hrv_le_4S : rv ≤ 4 * S + 1 := by omega
  -- CNF size bound
  have hN_size :
      encodable.size N ≤ 3 * formula_size f' * (3 * (b + formula_size f') + 10) :=
    tseytin'_encSize_bound b b f' hor hvars (le_refl b)
  -- Combine to bound the CNF part
  have hN_bound : encodable.size N ≤ 360 * S ^ 2 + 90 * S := by
    have h₁ : 3 * formula_size f' ≤ 9 * S := by omega
    have h₂ : 3 * (b + formula_size f') + 10 ≤ 3 * (S + 1 + 3 * S) + 10 := by omega
    have h₃ : 3 * (S + 1 + 3 * S) + 10 = 12 * S + 13 := by ring
    -- We need: 9 * S * (12 * S + 13) ≤ 360 * S^2 + 90 * S, but actually
    -- 9 * S * (12 * S + 13) = 108 * S^2 + 117 * S
    -- This is ≤ 360 * S^2 + 90 * S provided 27 * S ≤ 252 * S^2 + 90*S - ...
    -- Let me just use a looser bound: 9*S*(12S+13) ≤ 9*S*(12S+13)
    -- ≤ 360 S^2 + 90 S iff 108 S^2 + 117 S ≤ 360 S^2 + 90 S iff 252 S^2 ≥ 27 S
    -- For S ≥ 1 this is true (252 ≥ 27); for S = 0 we get 0 ≤ 0.
    nlinarith [Nat.zero_le S, hN_size, h₁, h₂, h₃, sq_nonneg S]
  -- Header clause size
  -- size [(true,rv),(true,rv),(true,rv)] = 3*(rv+2) + 3 = 3*rv + 9
  have hHeader_size :
      encodable.size [((true, rv) : literal), (true, rv), (true, rv)] ≤ 3 * rv + 9 := by
    -- Each literal has size rv + 2; the list has length 3.
    have hLits : ∀ l ∈ [((true, rv) : literal), (true, rv), (true, rv)],
        encodable.size l ≤ rv + 2 := by
      intro l hl
      simp at hl
      rcases hl with rfl | rfl | rfl <;>
        exact encodable_size_lit_le true rv rv (le_refl rv)
    have := encodable_size_list_le_length_mul (rv + 2)
              ([((true, rv) : literal), (true, rv), (true, rv)]) hLits
    simp [List.length] at this
    -- this : encodable.size [...] ≤ 3 * (rv + 3)
    linarith
  -- The full output is `[(true,rv),(true,rv),(true,rv)] :: N`
  -- size = (header_clause_size) + 1 + size N
  have hOutput :
      encodable.size ([((true, rv) : literal), (true, rv), (true, rv)] :: N) =
        encodable.size ([((true, rv) : literal), (true, rv), (true, rv)]) + 1 +
          encodable.size N := encodable_size_list_cons _ _
  -- Header contributes ≤ 3*rv + 10 to the cons.
  have hHeader_total : encodable.size ([((true, rv) : literal), (true, rv), (true, rv)]) + 1
                        ≤ 12 * S + 13 := by
    have hrv2 : rv ≤ 4 * S + 1 := hrv_le_4S
    -- 3 * rv + 9 + 1 = 3*rv + 10 ≤ 3*(4S+1) + 10 = 12S + 13
    linarith
  -- Final assembly
  show encodable.size ([((true, rv) : literal), (true, rv), (true, rv)] :: N) ≤
    500 * S ^ 2 + 100
  rw [hOutput]
  -- Goal: header_size + 1 + size N ≤ 500*S² + 100
  -- We have header + 1 ≤ 12S + 13 and size N ≤ 360 S^2 + 90 S
  -- Total ≤ 360 S^2 + 90 S + 12 S + 13 = 360 S^2 + 102 S + 13
  -- Need 360 S^2 + 102 S + 13 ≤ 500 S^2 + 100
  -- 140 S^2 ≥ 102 S - 87, i.e., for S ≥ 1, 140 ≥ 102 - 87 = 15 ✓; for S = 0, 0 ≥ -87 ✓
  nlinarith [hHeader_total, hN_bound, sq_nonneg S, Nat.zero_le S]

-- ─── Final polynomial reduction theorems ────────────────────────────────────

theorem FSAT_to_SAT_poly : FSAT ⪯p SAT :=
  ⟨⟨FSAT_to_SAT_tseytin,
    ⟨⟨fun n => 500 * n ^ 2 + 100,
      ⟨2, ⟨501, 10, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩,
      fun a b h => by nlinarith [Nat.pow_le_pow_left h 2],
      FSAT_to_SAT_size_le⟩⟩,
    FSAT_to_SAT_tseytin_correct⟩⟩

theorem FSAT_to_3SAT_poly : FSAT ⪯p kSAT 3 :=
  ⟨⟨FSAT_to_SAT_tseytin,
    ⟨⟨fun n => 500 * n ^ 2 + 100,
      ⟨2, ⟨501, 10, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩,
      fun a b h => by nlinarith [Nat.pow_le_pow_left h 2],
      FSAT_to_SAT_size_le⟩⟩,
    FSAT_to_3SAT_tseytin_correct⟩⟩
