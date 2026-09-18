# The Cook–Levin theorem in Lean 4

A machine-checked proof that SAT is NP-complete, with the theorem stated in terms of
Turing machines on bit strings and every definition the statement depends on laid out for
inspection.

The main theorem is `CookLevin.cook_levin` in [`CookLevin/Theorem.lean`](CookLevin/Theorem.lean):

```lean
theorem cook_levin : NPcomplete SATStr
```

`SATStr` is satisfiability of CNF formulas, presented as a language of bit strings.
`NPcomplete P` says that every language with a polynomial-time verifier reduces to `P` by a
polynomial-time Turing machine, and that `P` itself has a polynomial-time verifier. What
these words mean here, what a reader has to check to trust the theorem, and how it compares
to the textbook statement is explained in [GUIDE.md](GUIDE.md).

## Checking the proof

```
lake build
```

This needs the Lean toolchain named in `lean-toolchain` (installed by
[elan](https://github.com/leanprover/elan)); the first build downloads Mathlib's build
cache. A green build establishes:

* **No `sorry`, no extra axioms.** The last line of `CookLevin.lean` runs
  `#assert_library_axiom_clean CookLevin`, which inspects every declaration of every module
  and fails the build if any of them depends on an axiom other than Lean's three standard
  ones (`propext`, `Classical.choice`, `Quot.sound`). `sorry` is an axiom, so a green build
  proves there is none.
* **The reading list is complete.** `CookLevin/ReadingList.lean` fails the build unless the
  definitions of this repository that the *statement* of the main theorem depends on are
  exactly the ones listed there.

`#print axioms CookLevin.cook_levin` prints `[propext, Classical.choice, Quot.sound]`.

## Layout

```
CookLevin.lean                    root module; the whole-library axiom check
CookLevin/Theorem.lean            the main theorem
CookLevin/ReadingList.lean        the definitions the statement depends on, checked by the build
CookLevin/StatementMeaning.lean   small checked facts about those definitions
CookLevin/MachineFaithfulness.lean  the machine model has the defining properties of a Turing machine
CookLevin/SearchDecide.lean       every language with a verifier program is decidable
CookLevin/Basic/                  Turing machines, strings on tapes, reductions, NP, sizes
CookLevin/Lang/                   the register language, its cost model, its compiler to Turing machines
CookLevin/SAT/                    CNF formulas, SAT, the CNF encoding, the SAT verifier program
CookLevin/Problems/               the intermediate problems of the reduction chain
CookLevin/Tableau/                Cook's tableau: a machine run as a covering problem
CookLevin/Reductions/             the reduction chain and its composition
CookLevin/Meta/                   the build-time checks (axioms, statement surface)
```

## Structure of the proof

The proof follows the Coq development of Gäher and Kunze (*Mechanising Complexity Theory:
The Cook-Levin Theorem in Coq*, ITP 2021, <https://github.com/uds-psl/cook-levin>). Every
reduction and verifier is written as a program of a small register language
(`CookLevin/Lang`) with an explicit cost model, and a single verified compiler turns such
programs into Turing machines with a polynomial time bound.

Hardness is proved along the chain

```
Q  →  FlatSingleTMGenNP  →  FlatTCC  →  FlatCC  →  BinaryCC  →  FSAT  →  SAT  →  SATStr
```

for every language `Q` presented by a verifier program: the verifier is embedded into a
Turing machine (the first step), a run of that machine is turned into a covering problem
by Cook's tableau (`FlatTCC`), which is rewritten in stages into a Boolean formula (`FSAT`)
and then, by a Tseytin transformation, into a CNF. The steps are composed at the level of
programs and the composite is compiled once. Membership is a verifier program for SAT that
checks an assignment against the formula.
