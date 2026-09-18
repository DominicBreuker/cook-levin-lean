import CookLevin.Reductions.SAT_to_SATStr_comp
import CookLevin.Meta.AxiomGate

set_option autoImplicit false

/-! # The Cook–Levin theorem

`SATStr` (`SAT/SATStr.lean`) is satisfiability of CNF formulas, presented as a language
of bit strings: `SATStr x` holds when the bits of `x` spell out a satisfiable CNF in the
encoding `EvalCnfCmd.encodeCnf`.

The theorem below says that `SATStr` is NP-complete:

* **hardness** — every language `Q` in `inNPCmd` (a language with a polynomial-cost verifier
  program, `Lang/HardnessStr.lean`) reduces to `SATStr` in polynomial time: there are a
  function `f` and a single-tape Turing machine computing `f` in polynomial time such that
  `Q x ↔ SATStr (f x)` for every string `x` (`⪯p`, `Basic/StringTM.lean`);
* **membership** — `SATStr` itself is in `inNPCmd`, and hence (`SATStr_inNP`) in the class
  `inNP` defined with polynomial-time Turing-machine verifiers.

The `#assert_axioms_clean` line makes the build fail unless every theorem named depends on
nothing beyond the three standard axioms of Lean (`propext`, `Classical.choice`,
`Quot.sound`); in particular, none of them uses `sorry`. -/

namespace CookLevin

open CookLevin.Lang

/-- **The Cook–Levin theorem: `SATStr` is NP-complete.** -/
theorem cook_levin : NPcomplete SATStr := ⟨SATStrComp.satStr_NPhard, SATStr.inNPCmd_SATStr⟩

/-- The hardness half: every language with a polynomial-cost verifier program reduces to
`SATStr` by a polynomial-time Turing machine. -/
theorem SATStr_NPhard : ∀ Q : List Bool → Prop, inNPCmd Q → Q ⪯p SATStr := cook_levin.1

/-- The membership half, at the level of Turing machines: `SATStr` has a polynomial-time
Turing-machine verifier. -/
theorem SATStr_inNP : inNP SATStr := inNPCmd_inNP cook_levin.2

/-- The hypothesis class of the hardness half is contained in NP. -/
theorem inNPCmd_subset_inNP : ∀ Q : List Bool → Prop, inNPCmd Q → inNP Q :=
  fun _ h => inNPCmd_inNP h

#assert_axioms_clean CookLevin.cook_levin CookLevin.SATStr_NPhard CookLevin.SATStr_inNP
  CookLevin.inNPCmd_subset_inNP

end CookLevin
