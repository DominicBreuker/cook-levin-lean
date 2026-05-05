import Complexity.Complexity.NP
import Complexity.NP.FSAT
import Complexity.NP.SAT
import Complexity.NP.kSAT

set_option autoImplicit false

open Classical

def FSAT_to_SAT_yes : cnf := [[(true, 0)]]

def FSAT_to_SAT_no : cnf := [[]]

theorem FSAT_to_SAT_yes_sat : SAT FSAT_to_SAT_yes := by
  exact ⟨[0], by simp [FSAT_to_SAT_yes, satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar]⟩

noncomputable def FSAT_to_SAT_reduction (f : formula) : cnf :=
  if FSAT f then FSAT_to_SAT_yes else FSAT_to_SAT_no

def FSAT_to_3SAT_yes : cnf := [[(true, 0), (true, 1), (true, 2)]]

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

noncomputable def FSAT_to_3SAT_reduction (f : formula) : cnf :=
  if FSAT f then FSAT_to_3SAT_yes else FSAT_to_3SAT_no

theorem FSAT_to_SAT_poly : FSAT ⪯p SAT := by
  refine ⟨FSAT_to_SAT_reduction, ?_⟩
  intro f hf
  simpa [FSAT_to_SAT_reduction, hf] using FSAT_to_SAT_yes_sat

theorem FSAT_to_3SAT_poly : FSAT ⪯p kSAT 3 := by
  refine ⟨FSAT_to_3SAT_reduction, ?_⟩
  intro f hf
  simpa [FSAT_to_3SAT_reduction, hf] using FSAT_to_3SAT_yes_sat
