import Complexity.Complexity.NP
import Complexity.NP.SAT
import Complexity.NP.kSAT
import Complexity.Complexity.Deciders.EvalCnfTM
import Mathlib.Tactic

set_option autoImplicit false

/-- The unsatisfiable CNF consisting of a single empty clause.
Any assignment fails to satisfy the empty clause. -/
def emptyClauseCnf : cnf := [[]]

theorem emptyClauseCnf_unsat : ¬ SAT emptyClauseCnf := by
  rintro ⟨a, ha⟩
  simp [emptyClauseCnf, satisfiesCnf, evalCnf, evalClause] at ha

/-- Decidability instance for kCNF via the Boolean decision procedure. -/
instance kCNF_decidable (k : Nat) (N : cnf) : Decidable (kCNF k N) :=
  if h : kCNF_decb k N = true then isTrue ((kCNF_decb_iff k N).mp h)
  else isFalse (fun hc => h ((kCNF_decb_iff k N).mpr hc))

/-- Reduction from kSAT k to SAT:
- On valid kCNF inputs with 0 < k, return N itself.
- On other inputs (not yes-instances of kSAT k), return an unsatisfiable CNF.
  This mirrors the Coq trivialNoInstance pattern. -/
def kSAT_to_SAT_reduction (k : Nat) (N : cnf) : cnf :=
  if 0 < k ∧ kCNF k N then N else emptyClauseCnf

theorem kSAT_to_SAT_correct (k : Nat) (N : cnf) :
    kSAT k N ↔ SAT (kSAT_to_SAT_reduction k N) := by
  unfold kSAT kSAT_to_SAT_reduction
  split_ifs with h
  · exact ⟨fun ⟨_, _, hsat⟩ => hsat, fun hsat => ⟨h.1, h.2, hsat⟩⟩
  · constructor
    · intro ⟨hk, hcnf, _⟩; exact absurd ⟨hk, hcnf⟩ h
    · intro hsat; exact absurd hsat emptyClauseCnf_unsat

/-- kSAT k polynomial-time reduces to SAT. -/
theorem kSAT_to_SAT (k : Nat) : kSAT k ⪯p SAT :=
  ⟨⟨kSAT_to_SAT_reduction k,
    ⟨⟨fun n => n + 2,
      ⟨1, ⟨3, 2, by intro n hn; simp only [pow_one]; omega⟩⟩,
      fun a b h => by simp only; omega,
      fun N => by
        unfold kSAT_to_SAT_reduction emptyClauseCnf
        split_ifs with h
        · simp
        · -- size of [[]] = 1 ≤ encodable.size N + 2
          have h2 : encodable.size ([[]] : cnf) = 1 := by
            simp [encodable_size_list_cons, encodable_size_list_nil]
          show encodable.size ([[]] : cnf) ≤ encodable.size N + 2
          omega⟩⟩,
    kSAT_to_SAT_correct k⟩⟩

/-! **`inNP_kSAT` was DELETED (2026-07-30-c)** with `red_inNP`, the `sorry`-backed
`⪯p`-based composition it routed through. The honest, live replacement is
`KSat3Free.inNP_kSAT3_free` (`NP/kSAT_to_SAT_free.lean`) — same statement for
`k = 3`, produced by `Lang.red_inNP_of_langFree` from a real re-encoder `Cmd`,
axiom-clean. The map and correctness proof above are untouched and are what the
free witness consumes. -/
