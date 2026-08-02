import Complexity.StatementGate

set_option autoImplicit false

/-! # The meaning gate — the S8 verdicts, machine-checked

`Complexity/StatementGate.lean` proves the reviewer's reading list is
**complete**: 112 definitions behind `SATStrComp.SATStr_NPcompleteStr'`, 103
behind `CookLevinHonest.CookLevinStr`, 113 behind
`SATStrComp.SATStr_NPcompleteStr`, and nothing else of ours can affect what
those theorems say. It does *not* say anyone has read them, and it cannot: a
subtly wrong definition would still produce a perfectly exact list.

This file is the other half. Someone read the 103 (top-down session
2026-08-07) and asked of each group: *could a wrong definition here make the
headline true but meaningless, and would anything notice?* The answers are
ROADMAP risk **S8**'s verdict table. Wherever a verdict was checkable rather
than merely arguable, it is checked **here**, by `lake build`.

## How to use this file

Read `StatementGate.lean` first — it tells you *what* you must read. Read this
one second: it is the shortest path to convincing yourself that the handful of
definitions where a reader's intuition could be wrong are in fact right. Each
section names its ROADMAP S8 verdict number.

Three things this file deliberately does **not** try to do.

* It is not a substitute for reading the 103. A pin fixes one behaviour of one
  definition; only reading tells you the definition as a whole means what its
  name says.
* It says nothing about the *witness* we built — that is `HonestyGate.lean`,
  and by FINDING AW the two can never merge (no reduction, no `decodeOut` and
  no `Serialize` instance appears in either statement surface, because
  `reducesPolyMO'` quantifies over them existentially).
* It does not re-open anything `CostFaithfulness.lean` settles. `Op.cost` being
  a faithful proxy for `stepFlatTM` time is proven there; S8 verdict 6 cites it.
-/

namespace Complexity.StatementMeaning

open Complexity.Lang

/-! ## §1 · The headline, spelled out (S8 verdict 1)

The single most useful thing a reviewer can be handed: the theorem restated in
ordinary mathematical language, with the structures unpacked, and **proved from
the headline** so the restatement cannot drift from it.

`NPcompleteStr SAT` unfolds to a conjunction of two claims. The first is
hardness, and after unpacking `⪯p'` = `Nonempty (ReductionWitness' Q SAT)` it
says exactly what a textbook says: *for every NP string language `Q` there is a
polynomial-time computable function `f` from strings to CNF formulas such that
`x ∈ Q` if and only if `f x` is satisfiable.*

Note where the mathematical content sits. `f` is an ordinary Lean function and
`reduction_correct` is an honest `↔` about it — **no encoding, no machine and no
choice we made anywhere in the development can weaken that equivalence.** What
`polyTimeComputable' f` adds on top is the claim that `f` is computed by a real
`FlatTM` inside a polynomial time bound; *that* half is stated through the
witness's own `encode`/`decode` and is therefore the half risk S5 exists for. A
reader who wants the cleanest possible reading should take the two apart exactly
here. -/

/-- **Hardness, spelled out.** Every NP string language many-one reduces to SAT
by a polynomial-time computable map. -/
theorem hardness_spelled_out :
    ∀ Q : List Bool → Prop, inNPStr Q →
      ∃ f : List Bool → cnf, (∀ x, Q x ↔ SAT (f x)) ∧ polyTimeComputable' f := by
  intro Q hQ
  obtain ⟨W⟩ := CookLevinHonest.CookLevinStr.1 Q hQ
  exact ⟨W.reduction, fun x => W.reduction_correct (x := x), W.reduction_poly⟩

/-- **Membership, spelled out.** SAT itself is presented by a free-line verifier
witness — a real `Cmd` deciding a sound, complete, polynomially bounded
certificate relation.

⚠ Read this conjunct with S8 verdict 7 (FINDING AX) in hand: `inNPLangFreeSplit`
is a class whose witnesses supply their own input layout, and it is inhabited by
**every** string language, so this statement's content is that *our* witness is
honest (risk S5), not that the class demands it. The two theorems below are the
version without that caveat. -/
theorem membership_spelled_out : inNPLangFreeSplit SAT :=
  CookLevinHonest.CookLevinStr.2

/-! ### …and the same for the statement to quote

`SATStrComp.SATStr_NPcompleteStr' : NPcompleteStr' SATStr` is the headline whose
*both* conjuncts pin the canonical layout. Spelled out, it is a language
`L ⊆ {0,1}*` that is NP-hard among bit-string languages and is itself verified,
from the raw input string, by a real `Cmd`. -/

/-- **Hardness of the string language, spelled out.** -/
theorem strict_hardness_spelled_out :
    ∀ Q : List Bool → Prop, inNPStr Q →
      ∃ f : List Bool → List Bool,
        (∀ x, Q x ↔ SATStr.SATStr (f x)) ∧ polyTimeComputable' f := by
  intro Q hQ
  obtain ⟨W⟩ := SATStrComp.SATStr_NPcompleteStr'.1 Q hQ
  exact ⟨W.reduction, fun x => W.reduction_correct (x := x), W.reduction_poly⟩

/-- **Membership of the string language, with the layout pinned.** Unlike
`membership_spelled_out` this conjunct carries `encX_canonical`, so the verifier
must decide from `certState x` — the raw bit string, one register, one cell per
bit — and there is no layout left for anyone to choose. -/
theorem strict_membership_spelled_out : inNPStr SATStr.SATStr :=
  SATStrComp.SATStr_NPcompleteStr'.2

/-! ## §2 · Rejection is a verdict, not the absence of acceptance (S8 verdict 2)

`DecidesLang.decides` is `Cmd.decides c encodeIn P`, which is **two-sided**:

```
∀ x, (P x ↔ (c.eval (encodeIn x)).isAccept) ∧ (¬ P x ↔ (c.eval (encodeIn x)).isReject)
```

A one-sided reading — "`P x` iff the program accepts" — would be satisfied by a
program that accepts exactly the positive instances and *diverges in the output
register* on the rest. It cannot happen here, because `isAccept` and `isReject`
are two independent tests of register `0` against two different literals, and a
state can fail both. The pins below exhibit a state that is neither, which is
what makes the second conjunct real content rather than the negation of the
first. -/

theorem neither_accept_nor_reject : State.isAccept [] = false ∧ State.isReject [] = false := by
  decide

theorem accept_is_one : State.isAccept [[1]] = true ∧ State.isReject [[1]] = false := by decide

theorem reject_is_zero : State.isAccept [[0]] = false ∧ State.isReject [[0]] = true := by decide

/-- A register that is neither literal is neither verdict — so "rejects" is a
positive obligation on the program, not a default. -/
theorem junk_is_no_verdict :
    State.isAccept [[1, 1]] = false ∧ State.isReject [[1, 1]] = false := by decide

/-! ## §3 · The machine: what `stepFlatTM` does at the tape's edges (S8 verdict 9)

This is the one place in the whole reading list where a reviewer is likely to
stop and suspect a restriction has been smuggled in to make the tableau
construction work. It has not, and the reason is worth stating plainly.

`writeCurrentTapeSymbol` replaces a cell in range, **appends** exactly at the
frontier (`head = right.length`), and is a silent **no-op** strictly beyond it.
That last clause looks like a gap. It is deliberate, it is a locked invariant of
this development, and the alternative is *unsound*: the definition it replaced
zero-padded jump-writes, so a single step could materialise cells arbitrarily
far from the head, which is non-local and falsifies every three-cell-window
tableau simulation — `cookTableau_correct` was **false as stated** against it for
adversarial but `validFlatTM`-valid machines. See `probes/S1TableauProbe.lean`
§5 and the docstring on `writeCurrentTapeSymbol` itself.

Two consequences a reader should also see, both pinned below: the head cannot
run off the left end (`Lmove` at `0` stays at `0` — a one-way-infinite tape),
and a cell past the frontier reads `none` (blank), which is a *different* symbol
from `some 0`. Blank and zero are not confused. -/

theorem write_beyond_frontier_is_noop :
    writeCurrentTapeSymbol ([], 5, [1, 1]) (some 1) = ([], 5, [1, 1]) := rfl

theorem write_at_frontier_appends :
    writeCurrentTapeSymbol ([], 2, [1, 1]) (some 0) = ([], 2, [1, 1, 0]) := rfl

theorem write_in_range_replaces :
    writeCurrentTapeSymbol ([], 1, [1, 1]) (some 0) = ([], 1, [1, 0]) := rfl

/-- The tape is one-way infinite: moving left at cell `0` is a no-op. -/
theorem left_end_is_a_wall : moveTapeHead ([], 0, [1]) TMMove.Lmove = ([], 0, [1]) := rfl

/-- Past the frontier the machine reads `none`, not `some 0`. -/
theorem beyond_frontier_reads_blank : currentTapeSymbol ([], 3, [1, 1]) = none := rfl

/-! ## §4 · `runFlatTM` returning `some` is not evidence of halting (S8 verdict 3)

`ComputesBy.computes` demands

```
∃ cfg, runFlatTM (timeBound (size x)) M (initFlatConfig M (initialTapes M (encode x))) = some cfg
       ∧ haltingStateReached M cfg = true ∧ decode cfg = f x
```

and a reader skimming it may take `= some cfg` to be the halting claim. It is
not: `runFlatTM` is **total** — out of budget, halted, and *stuck* (no matching
transition entry) all return `some`. The machine below has no transitions and no
halting states; it "runs" for any budget and yields its initial configuration.

So the load-bearing conjunct is `haltingStateReached M cfg = true`, and it is a
real obligation: the machine must be in a state its own `halt` table marks
halting, within the budget. `runFlatTM_of_halting` and `runFlatTM_extend` are
what make a *shorter* real run satisfy a *longer* budget. -/

/-- A machine with no transitions and no halting states. -/
def stuckM : FlatTM := ⟨1, 1, 1, [], 0, [false]⟩

theorem stuck_run_returns_some :
    runFlatTM 100 stuckM (initFlatConfig stuckM [[]]) = some (initFlatConfig stuckM [[]]) := rfl

theorem stuck_run_never_halted :
    haltingStateReached stuckM (initFlatConfig stuckM [[]]) = false := by decide

/-! ## §5 · SAT means satisfiability (S8 verdict 11)

`SAT N = ∃ a : assgn, evalCnf a N = true`, where an `assgn` is a `List var` read
as **the set of variables assigned `true`** (`evalVar a v = decide (v ∈ a)`), a
`literal` is a `(sign, var)` pair satisfied when the variable's value equals the
sign, a `clause` is satisfied by `List.any` (disjunction) and a `cnf` by
`List.all` (conjunction).

The two degenerate cases are the ones to check, because both are easy to get
backwards and either would make the theorem meaningless: the empty clause must
be **unsatisfiable** and the empty CNF must be **satisfiable**. They are. And
`SAT` is neither identically true nor identically false — pinned below with a
satisfiable formula, an unsatisfiable one-clause formula and an unsatisfiable
two-clause one, so no reader has to take on faith that the predicate separates
anything. -/

theorem empty_clause_is_false : evalClause [] [] = false := rfl

theorem empty_cnf_is_true : evalCnf [] [] = true := rfl

theorem sat_empty_cnf : SAT [] := ⟨[], rfl⟩

/-- The canonical unsatisfiable formula — also the value the string language's
parser sends every malformed input to, which is why a non-encoding is *outside*
`SATStr` rather than silently inside it. -/
theorem not_sat_empty_clause : ¬ SAT [[]] := CnfWellFormed.not_sat_botCnf

theorem sat_singleton : SAT [[(true, 0)]] := ⟨[0], rfl⟩

/-- `x ∧ ¬x` is unsatisfiable: the sign field really is a sign. -/
theorem not_sat_contradiction : ¬ SAT [[(true, 0)], [(false, 0)]] := by
  rintro ⟨a, ha⟩
  by_cases h : (0 : Nat) ∈ a <;>
    simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar, h] at ha

/-! ## §6 · Input size: what the polynomials are polynomials in (S8 verdicts 12–13)

Two things a reviewer must know about `encodable`, and only one of them is
comfortable.

**The comfortable one.** On the hardness side the measure is *faithful*: an
input to `NPhardStr` is a `List Bool`, and its `encodable.size` is between its
length and twice its length. So "polynomial in `encodable.size x`" is
"polynomial in the length of the input string", which is the textbook meaning.
Both bounds are theorems of `Lang/HardnessStr.lean`, re-pinned here because they
are the reason the headline's polynomials mean what a reader assumes.

**The uncomfortable one.** `encodable.size` on `Nat` is `id` — numbers are
measured in **unary**, uniformly, throughout this development. This is not an
oversight and not a cheat, but it must be said out loud: a CNF's measured size
counts each variable *index* in unary, so a formula mentioning variable `2^40`
is measured as astronomically large. The measure is honest here only because it
**agrees with the layout the machines actually use** — every encoding on the
proof path is a flat `0`/`1` stream with numbers in unary (`Compile.BitState`,
`sig = 4`), and `InNPWitnessLangFreeSplit.sizeLB` demands the input's size be
recoverable from its own layout's cell count. Measure and tape agree, so the
polynomial bounds are bounds on real machine time on a real tape.

⚠ **What this does cost.** `SAT ∈ NP` is stated against a unary-measured `cnf`,
which is a *weaker* claim than the same statement over a binary-encoded CNF —
the input looks bigger, so a polynomial bound is easier to meet. This is the
strongest argument for quoting `SATStrComp.SATStr_NPcompleteStr` rather than
`CookLevinHonest.CookLevinStr`: over `SATStr` the input **is** the bit string,
`instEncodableNat` drops out of the statement surface entirely (it is the one
name in the 103 that is not in the 113), and the measure question does not arise
on either side of the arrow. -/

/-- The hardness side's measure is the string's length, up to a factor of two. -/
theorem size_faithful_lower (x : List Bool) : x.length ≤ encodable.size x :=
  Complexity.Lang.length_le_size x

theorem size_faithful_upper (x : List Bool) : encodable.size x ≤ 2 * x.length :=
  Complexity.Lang.size_le_two_mul_length x

/-- Numbers are measured in **unary**. -/
theorem nat_size_is_unary : encodable.size (7 : Nat) = 7 := rfl

/-- ⚠ **`encodable.size_ge_logical` is vacuous and constrains nothing.** The
class field reads `∀ x, ∃ n : Nat, size x ≥ n`, which `n := 0` discharges for
*any* function whatsoever — as this proof, which never mentions `encodable`,
demonstrates. It has no consumers anywhere in the library. A reviewer working
through the reading list should not spend time looking for content in it: the
`encodable` class is a `size` function and nothing else, and everything that
constrains `size` is stated where it is used (`InNPWitnessLangFreeSplit.sizeLB`,
`Serialize`'s size sandwich, `DecidesLang.encodeIn_size`). -/
theorem size_ge_logical_is_vacuous (f : Nat → Nat) : ∀ x : Nat, ∃ n : Nat, f x ≥ n :=
  fun _ => ⟨0, Nat.zero_le _⟩

end Complexity.StatementMeaning
