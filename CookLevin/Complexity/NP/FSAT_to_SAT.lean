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
      · -- cnf_varsIn
        intro u hu
        simp [tseytinEquiv, varInCnf, varInClause, varInLiteral] at hu
        rcases hu with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact Or.inl hv_lt
        · right; omega
      · -- ext
        sorry
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
      obtain ⟨_, hrv₁_lo, hrv₁_hi, _, hspec₁⟩ := repr₁
      obtain ⟨_, hrv₂_lo, hrv₂_hi, _, hspec₂⟩ := repr₂
      simp only [tseytin', ← List.append_assoc, tseytin_formula_repr]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · sorry -- cnf_varsIn
      · linarith  -- nf ≤ nf₂
      · omega     -- nf₂ < nf₂ + 1
      · sorry  -- ext
      · -- spec
        intro a ha
        have haN₁ : satisfiesCnf a (tseytin' nf f₁).2.1 := by
          rw [satisfiesCnf, ← evalCnf_clause_iff] at ha ⊢
          intro C hC; exact (evalCnf_clause_iff a _).mp ha C
            (List.mem_append_left _ (List.mem_append_left _ hC))
        have haN₂ : satisfiesCnf a (tseytin' (tseytin' nf f₁).2.2 f₂).2.1 := by
          rw [satisfiesCnf, ← evalCnf_clause_iff] at ha ⊢
          intro C hC; exact (evalCnf_clause_iff a _).mp ha C
            (List.mem_append_left _ (List.mem_append_right _ hC))
        have haAnd : satisfiesCnf a (tseytinAnd
            (tseytin' (tseytin' nf f₁).2.2 f₂).2.2
            (tseytin' nf f₁).1
            (tseytin' (tseytin' nf f₁).2.2 f₂).1) := by
          rw [satisfiesCnf, ← evalCnf_clause_iff] at ha ⊢
          intro C hC; exact (evalCnf_clause_iff a _).mp ha C (List.mem_append_right _ hC)
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
      obtain ⟨_, hrv_lo, hrv_hi, _, hspec⟩ := repr
      simp only [tseytin', tseytin_formula_repr]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · sorry -- cnf_varsIn
      · omega
      · omega
      · sorry -- ext
      · -- spec
        intro a ha
        have haN : satisfiesCnf a (tseytin' nf f).2.1 := by
          rw [satisfiesCnf, ← evalCnf_clause_iff] at ha ⊢
          intro C hC; exact (evalCnf_clause_iff a _).mp ha C (List.mem_append_left _ hC)
        have haNot : satisfiesCnf a (tseytinNot (tseytin' nf f).2.2 (tseytin' nf f).1) := by
          rw [satisfiesCnf, ← evalCnf_clause_iff] at ha ⊢
          intro C hC; exact (evalCnf_clause_iff a _).mp ha C (List.mem_append_right _ hC)
        have hNot := (tseytinNot_sat a _ _).mp haNot
        constructor
        · intro h
          simp only [evalFormula, Bool.not_eq_true]
          intro heq
          exact hNot.mp h ((hspec a haN).mpr heq)
        · intro h
          apply hNot.mpr
          simp only [evalFormula] at h
          intro hrv
          exact absurd ((hspec a haN).mp hrv) (Bool.not_eq_true.mp (Bool.not_eq_true_of_eq_false (by
            cases hf : evalFormula a f <;> simp_all [evalFormula])))

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
