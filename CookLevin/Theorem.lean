import CookLevin.Reductions.SAT_to_SATStr_comp
import CookLevin.Simulation.Witness
import CookLevin.Meta.AxiomGate

set_option autoImplicit false

/-! # The Cook–Levin theorem

`SATStr` (`SAT/SATStr.lean`) is satisfiability of CNF formulas, presented as a language
of bit strings: `SATStr x` holds when the bits of `x` spell out a satisfiable CNF in the
encoding `EvalCnfCmd.encodeCnf`.

The theorem below says that `SATStr` is NP-complete (`NPcomplete`, `Basic/StringTM.lean`):

* **hardness** — every language `Q` in NP (`inNP`: `Q` has a polynomial-time Turing-machine
  verifier with polynomially bounded certificates) reduces to `SATStr` in polynomial time:
  there are a function `f` and a single-tape Turing machine computing `f` in polynomial
  time such that `Q x ↔ SATStr (f x)` for every string `x` (`⪯p`);
* **membership** — `SATStr` itself is in NP.

The statement mentions Turing machines, strings, polynomials and CNF formulas only. The
proof goes through the register language of `Lang/`: `inNP` coincides with `inNPCmd`, the
class of languages with a polynomial-cost verifier *program* (`inNP_iff_inNPCmd`). One
direction compiles programs to machines (`Lang/ToMachine.lean`), the other simulates
machines by programs (`Simulation/`). Hardness is proved for `inNPCmd`
(`SATStrComp.satStr_NPhard`), membership by a verifier program for `SATStr`.

The `#assert_axioms_clean` line makes the build fail unless every theorem named depends on
nothing beyond the three standard axioms of Lean (`propext`, `Classical.choice`,
`Quot.sound`); in particular, none of them uses `sorry`. -/

namespace CookLevin

open CookLevin.Lang

/-- NP, defined by Turing-machine verifiers, is the class of languages with a
polynomial-cost verifier program. -/
theorem inNP_iff_inNPCmd (Q : List Bool → Prop) : inNP Q ↔ inNPCmd Q :=
  ⟨Sim.inNP_inNPCmd, inNPCmd_inNP⟩

/-- **The Cook–Levin theorem: `SATStr` is NP-complete.** -/
theorem cook_levin : NPcomplete SATStr :=
  ⟨fun Q hQ => SATStrComp.satStr_NPhard Q (Sim.inNP_inNPCmd hQ),
   inNPCmd_inNP SATStr.inNPCmd_SATStr⟩

/-- The hardness half: every language in NP reduces to `SATStr` by a polynomial-time
Turing machine. -/
theorem SATStr_NPhard : NPhard SATStr := cook_levin.1

/-- The membership half: `SATStr` has a polynomial-time Turing-machine verifier. -/
theorem SATStr_inNP : inNP SATStr := cook_levin.2

/-- The theorem as it is proved, for the class `inNPCmd` of languages with a verifier
program. Equivalent to `cook_levin` by `inNP_iff_inNPCmd`. -/
theorem cook_levin_cmd : NPcompleteCmd SATStr :=
  ⟨SATStrComp.satStr_NPhard, SATStr.inNPCmd_SATStr⟩

#assert_axioms_clean CookLevin.cook_levin CookLevin.SATStr_NPhard CookLevin.SATStr_inNP
  CookLevin.inNP_iff_inNPCmd CookLevin.cook_levin_cmd

end CookLevin
