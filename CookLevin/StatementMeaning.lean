import CookLevin.Theorem

set_option autoImplicit false

/-! # What the statement says

Small, machine-checked facts about the definitions the main theorem is stated with. Each
one settles a question a reader might otherwise have to answer by tracing definitions: that
the theorem unfolds to the expected quantifier structure, that accepting and rejecting are
two distinct verdicts, what the tape does at its edges, that a run returning `some` is not
by itself a halting claim, that `SAT` means satisfiability, and how input size is measured.
-/

namespace CookLevin.StatementMeaning

open CookLevin.Lang

/-! ## The theorem, unfolded

`NPcomplete SATStr` is, by definition, the conjunction below: every language with a
polynomial-cost verifier program reduces to `SATStr` by a polynomial-time single-tape
Turing machine, and `SATStr` itself has a polynomial-cost verifier program. -/

theorem cook_levin_unfolded :
    (∀ Q : List Bool → Prop, inNPCmd Q →
        ∃ (f : List Bool → List Bool) (t : Nat → Nat) (M : FlatTM),
          inOPoly t ∧ validFlatTM M ∧ M.tapes = 1 ∧ computesInTime M f t ∧
          ∀ x, Q x ↔ SATStr (f x)) ∧
    inNPCmd SATStr :=
  cook_levin

/-! ## Accepting and rejecting are two distinct verdicts

`Cmd.decides` requires `P x ↔ accept` **and** `¬ P x ↔ reject`. A state accepts when register
`0` holds exactly `[1]` and rejects when it holds exactly `[0]`; a state can do neither, so
the second conjunct is a real obligation on the program. -/

theorem neither_accept_nor_reject : State.isAccept [] = false ∧ State.isReject [] = false := by
  decide

theorem accept_is_one : State.isAccept [[1]] = true ∧ State.isReject [[1]] = false := by decide

theorem reject_is_zero : State.isAccept [[0]] = false ∧ State.isReject [[0]] = true := by decide

theorem junk_is_no_verdict :
    State.isAccept [[1, 1]] = false ∧ State.isReject [[1, 1]] = false := by decide

/-! ## The tape at its edges

`writeCurrentTapeSymbol` replaces the cell under the head when it is inside the written
region, appends a cell when the head is exactly at the frontier, and does nothing when the
head is strictly beyond it. The head cannot move left of cell `0`, and a cell beyond the
frontier reads `none` (blank), which is different from the symbol `0`. -/

theorem write_beyond_frontier_is_noop :
    writeCurrentTapeSymbol ([], 5, [1, 1]) (some 1) = ([], 5, [1, 1]) := rfl

theorem write_at_frontier_appends :
    writeCurrentTapeSymbol ([], 2, [1, 1]) (some 0) = ([], 2, [1, 1, 0]) := rfl

theorem write_in_range_replaces :
    writeCurrentTapeSymbol ([], 1, [1, 1]) (some 0) = ([], 1, [1, 0]) := rfl

theorem left_end_is_a_wall : moveTapeHead ([], 0, [1]) TMMove.Lmove = ([], 0, [1]) := rfl

theorem beyond_frontier_reads_blank : currentTapeSymbol ([], 3, [1, 1]) = none := rfl

/-! ## A run returning `some` is not a halting claim

`runFlatTM` is total: it returns `some` when the budget is exhausted, when a halting state
is reached, and when the machine is stuck (no transition applies). The halting claim in
`computesInTime` and `decidesPairInTime` is the separate conjunct
`haltingStateReached M cfg = true`. -/

/-- A machine with no transitions and no halting states. -/
def stuckM : FlatTM := ⟨1, 1, 1, [], 0, [false]⟩

theorem stuck_run_returns_some :
    runFlatTM 100 stuckM (initFlatConfig stuckM [[]]) = some (initFlatConfig stuckM [[]]) := rfl

theorem stuck_run_never_halted :
    haltingStateReached stuckM (initFlatConfig stuckM [[]]) = false := by decide

/-! ## `SAT` means satisfiability

`SAT N` says some assignment (a list of the variables set to `true`) satisfies every clause
of `N`, where a clause is satisfied when one of its literals `(sign, v)` has `evalVar a v =
sign`. The empty clause is unsatisfiable, the empty CNF is satisfiable, and the sign is a
sign. -/

theorem empty_clause_is_false : evalClause [] [] = false := rfl

theorem empty_cnf_is_true : evalCnf [] [] = true := rfl

theorem sat_empty_cnf : SAT [] := ⟨[], rfl⟩

theorem not_sat_empty_clause : ¬ SAT [[]] := CnfWellFormed.not_sat_botCnf

theorem sat_singleton : SAT [[(true, 0)]] := ⟨[0], rfl⟩

theorem not_sat_contradiction : ¬ SAT [[(true, 0)], [(false, 0)]] := by
  rintro ⟨a, ha⟩
  by_cases h : (0 : Nat) ∈ a <;>
    simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar, h] at ha

/-! ## Input size

The cost bounds of verifier programs are stated in `encodable.size`. On a bit string this
is between the length and twice the length, so "polynomial in the size" is "polynomial in
the length". Numbers are measured in unary (`encodable.size (n : Nat) = n`); the field
`size_ge_logical` of `encodable` holds of every function and constrains nothing. -/

theorem size_faithful_lower (x : List Bool) : x.length ≤ encodable.size x :=
  length_le_size x

theorem size_faithful_upper (x : List Bool) : encodable.size x ≤ 2 * x.length :=
  size_le_two_mul_length x

theorem nat_size_is_unary : encodable.size (7 : Nat) = 7 := rfl

theorem size_ge_logical_is_vacuous (f : Nat → Nat) : ∀ x : Nat, ∃ n : Nat, f x ≥ n :=
  fun _ => ⟨0, Nat.zero_le _⟩

#assert_axioms_clean CookLevin.StatementMeaning.cook_levin_unfolded

end CookLevin.StatementMeaning
