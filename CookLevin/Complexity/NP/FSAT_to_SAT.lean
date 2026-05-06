import Complexity.Complexity.NP
import Complexity.NP.FSAT
import Complexity.NP.SAT
import Complexity.NP.kSAT

set_option autoImplicit false

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
      have h₁ : formula_varsIn (fun v => v < n) f₁ := by
        intro v hv
        exact h v (varInFormula.andLeft _ _ hv)
      have h₂ : formula_varsIn (fun v => v < n) f₂ := by
        intro v hv
        exact h v (varInFormula.andRight _ _ hv)
      simp [evalFormula, evalFormula_boundedAssignment_of_bound a f₁ n h₁,
        evalFormula_boundedAssignment_of_bound a f₂ n h₂]
  | .forr f₁ f₂, n, h => by
      have h₁ : formula_varsIn (fun v => v < n) f₁ := by
        intro v hv
        exact h v (varInFormula.orLeft _ _ hv)
      have h₂ : formula_varsIn (fun v => v < n) f₂ := by
        intro v hv
        exact h v (varInFormula.orRight _ _ hv)
      simp [evalFormula, evalFormula_boundedAssignment_of_bound a f₁ n h₁,
        evalFormula_boundedAssignment_of_bound a f₂ n h₂]
  | .fneg f, n, h => by
      have h' : formula_varsIn (fun v => v < n) f := by
        intro v hv
        exact h v (varInFormula.neg _ hv)
      simp [evalFormula, evalFormula_boundedAssignment_of_bound a f n h']

theorem evalFormula_boundedAssignment (a : assgn) (f : formula) :
    evalFormula (boundedAssignment (formula_maxVar f + 1) a) f = evalFormula a f := by
  exact evalFormula_boundedAssignment_of_bound a f (formula_maxVar f + 1) (formula_maxVar_varsIn f)

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

def FSAT_search (f : formula) : Bool :=
  (allAssignments (formula_maxVar f + 1)).any (fun a => evalFormula a f)

theorem FSAT_search_complete (f : formula) : FSAT f → FSAT_search f = true := by
  rintro ⟨a, ha⟩
  have hmem : boundedAssignment (formula_maxVar f + 1) a ∈ allAssignments (formula_maxVar f + 1) :=
    boundedAssignment_mem_allAssignments _ a
  have hEval : evalFormula (boundedAssignment (formula_maxVar f + 1) a) f = true := by
    exact (evalFormula_boundedAssignment a f).trans ha
  exact List.any_eq_true.mpr ⟨boundedAssignment (formula_maxVar f + 1) a, hmem, hEval⟩

def FSAT_to_SAT_yes : cnf := [[(true, 0)]]

def FSAT_to_SAT_no : cnf := [[]]

theorem FSAT_to_SAT_yes_sat : SAT FSAT_to_SAT_yes := by
  exact ⟨[0], by simp [FSAT_to_SAT_yes, satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar]⟩

def FSAT_to_SAT_reduction (f : formula) : cnf :=
  if FSAT_search f then FSAT_to_SAT_yes else FSAT_to_SAT_no

def FSAT_to_3SAT_yes : cnf := [[(true, 0), (true, 1), (true, 2)]]

/-- An explicit unsatisfiable 3-CNF over three variables, obtained by listing
all eight truth-table rows as forbidden clauses. -/
def FSAT_to_3SAT_no : cnf :=
  [
    [(true, 0), (true, 1), (true, 2)],
    [(false, 0), (false, 1), (false, 2)],
    [(true, 0), (true, 1), (false, 2)],
    [(true, 0), (false, 1), (true, 2)],
    [(false, 0), (true, 1), (true, 2)],
    [(true, 0), (false, 1), (false, 2)],
    [(false, 0), (true, 1), (false, 2)],
    [(false, 0), (false, 1), (true, 2)]
  ]

theorem FSAT_to_3SAT_yes_sat : kSAT 3 FSAT_to_3SAT_yes := by
  refine ⟨by decide, ?_, ?_⟩
  · exact kCNF.cons _ _ rfl kCNF.nil
  · exact ⟨[0], by simp [FSAT_to_3SAT_yes, satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar]⟩

def FSAT_to_3SAT_reduction (f : formula) : cnf :=
  if FSAT_search f then FSAT_to_3SAT_yes else FSAT_to_3SAT_no

theorem FSAT_to_SAT_poly : FSAT ⪯p SAT := 
  ⟨⟨FSAT_to_SAT_reduction, trivial, by
    intro x
    have hsearch : FSAT_search x = true := FSAT_search_complete x
    simpa [FSAT_to_SAT_reduction, hsearch] using FSAT_to_SAT_yes_sat⟩⟩

theorem FSAT_to_3SAT_poly : FSAT ⪯p kSAT 3 := 
  ⟨⟨FSAT_to_3SAT_reduction, trivial, by
    intro x
    have hsearch : FSAT_search x = true := FSAT_search_complete x
    simpa [FSAT_to_3SAT_reduction, hsearch] using FSAT_to_3SAT_yes_sat⟩⟩
