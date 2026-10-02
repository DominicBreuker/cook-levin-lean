# Reader's guide: what is proved, and what you have to check

This guide is for a mathematician who wants to know exactly what the theorem in this
repository says and what has to be believed to accept it. It assumes familiarity with the
textbook statement of the Cook–Levin theorem and no familiarity with Lean.

## 1. The claim

`CookLevin/Theorem.lean` proves

```lean
theorem cook_levin : NPcomplete SATStr
```

which unfolds (`StatementMeaning.cook_levin_unfolded`) to the conjunction of

1. **hardness**: for every language `Q ⊆ {0,1}*` in NP (`inNP Q`, §4.2) there are a function
   `f : {0,1}* → {0,1}*`, a single-tape Turing machine `M` and a polynomial `t` such that
   `M`, started on the tape holding `x`, halts within `t(|x|)` steps with `f(x)` written on
   the tape, and `x ∈ Q ⇔ f(x) ∈ SATStr`;
2. **membership**: `SATStr` is in NP.

Both halves are stated with Turing machines only. The proof works in a small register
language with an explicit cost model (§4.6); the same file proves that the class of
languages with a polynomial-cost verifier program in that language is exactly NP:

```lean
theorem inNP_iff_inNPCmd (Q : List Bool → Prop) : inNP Q ↔ inNPCmd Q
```

## 2. What you have to trust

1. **Lean's kernel and its three standard axioms** `propext`, `Classical.choice`,
   `Quot.sound`. The build itself checks that nothing else is used anywhere in the library
   (`#assert_library_axiom_clean CookLevin` in `CookLevin.lean`); `sorry` counts as an axiom
   and is therefore excluded. You can also run `#print axioms CookLevin.cook_levin`.
2. **The definitions the statement is built from.** A theorem is only as good as its
   statement. `CookLevin/ReadingList.lean` lists every definition of this repository that
   the statement of `cook_levin` depends on (68 of them), and the build fails unless the
   list is exact. Everything the statement mentions that is not on the list comes from
   Lean's core library (`List`, `Nat`, `Bool`, …); Mathlib is used in proofs only. §4 walks
   through the list.

Nothing about the *proof* has to be read: it is checked by the kernel. Nothing about the
*reduction* has to be read either: the theorem asserts that a machine with the stated
properties exists, so a wrong construction could only have made the proof fail.

## 3. What the build checks

`lake build` elaborates every file and runs three kinds of build-time checks:

* the axiom check above;
* the reading list (`ReadingList.lean`);
* the sanity checks of `StatementMeaning.lean`, `MachineFaithfulness.lean` and
  `SearchDecide.lean` (§5), which are ordinary theorems about the definitions.

The axiom check and the reading-list check are commands defined in this repository
(`Meta/`). To check the result without trusting them, run `lake env lean Verify.lean`: it
prints the main theorem, its central definitions and its axioms using only Lean's built-in
commands.

## 4. Reading the statement

The reading list groups the definitions by topic. File names are relative to `CookLevin/`.

### 4.1 Turing machines (`Basic/MachineSemantics.lean`, `Basic/Definitions.lean`)

A machine `FlatTM` has an alphabet `{0, …, sig-1}`, a number of tapes, a number of states
`{0, …, states-1}`, a start state, a list `halt` marking the halting states, and a
transition table `trans`: a list of entries, each matching a state and the symbols read on
the tapes (`none` is the blank) and giving the next state, the symbols to write and the
head moves. `validFlatTM` says all indices are in range. A configuration is a state and, per
tape, a triple `(left, head, right)`; only `right` (the written cells) and `head` (an index
into it) matter, `left` is always empty. `stepFlatTM` takes the first matching entry and
applies it; `runFlatTM n M cfg` runs at most `n` steps and stops early at a halting state
or when no entry matches. `haltingStateReached` is the halting test. Time is the number of
steps; the theorems only use single-tape machines (`M.tapes = 1`).

Two details differ from the usual textbook picture; both make the machine weaker:

* the tape is one-way infinite: moving left at cell `0` leaves the head at `0`;
* the tape is append-only: a write is performed when the head is at or before the end of
  the written region and dropped when it is strictly beyond it (a head can be moved beyond
  the region; it then reads blanks). A machine can therefore never create an unwritten gap.

The machine model occurs on both sides of the theorem, with opposite effects. The reduction
is a machine of this model, so a weaker model makes the hardness half *stronger*. The
verifiers in the hypothesis `inNP` are machines of this model too, so a weaker model could
make the class `inNP` *smaller* than NP. It does not, but this rests on the standard
robustness of the Turing-machine model, which is not formalised here: a textbook machine
(two-way infinite tape, writes anywhere) is simulated by one of this model with polynomial
overhead, by folding the tape at cell `0` and writing a blank-standing symbol whenever the
head steps onto a new cell. What *is* formalised is that the class is robust in another
sense: `inNP` coincides with the class of languages that have a polynomial-cost verifier in
the register language of §4.6 (`inNP_iff_inNPCmd`).

`MachineFaithfulness.lean` proves, for every machine, that a step reads one cell, changes at
most that cell, moves the head by at most one, extends the tape by at most one cell, is
selected from the state and the symbols read only, and stays inside the finite alphabet and
state set; hence space is bounded by time.

### 4.2 Strings, reductions, NP (`Basic/StringTM.lean`)

A bit string `x` is written on the tape as `3, s₁, …, sₙ, 0, 3` with `sᵢ = 1` for `false`
and `2` for `true` (`stringTape`); a pair `(x, c)` as `3, sym x, 0, sym c, 0, 3`
(`pairTape`). The output of a halted machine (`outputString`) is read back from the tape
the same way: after the leading `3`, the symbols up to the first `0` or `3`, with `2` as
`true`.

* `computesInTime M f t`: for every `x`, `M` started on `stringTape x` reaches a halting
  state within `t |x|` steps with `outputString = f x`.
* `Q ⪯p P` (`reducesPoly`): there are `f`, a polynomial `t` (`inOPoly`: bounded by
  `c · n^k` for large `n`) and a valid single-tape `M` with `computesInTime M f t` and
  `Q x ↔ P (f x)` for all `x`. This is polynomial-time many-one reducibility.
* `inNP Q`: there are a relation `R` on pairs of strings, natural numbers `a`, `k`, `b`, a
  polynomial `t`, a valid single-tape machine `M` and two states `acc`, `rej` such that `M`
  on `pairTape x c` halts within `t (|x| + |c|)` steps, in state `acc` exactly when `R x c`
  and in state `rej` exactly when not (`decidesPairInTime`), and `x ∈ Q` iff some `c` with
  `|c| ≤ a·|x|^k + b` has `R x c`. This is the verifier definition of NP.
* `NPhard P`: every `Q` with `inNP Q` has `Q ⪯p P`; `NPcomplete P`: `NPhard P ∧ inNP P`.

The certificate bound is an explicit polynomial on purpose. If it were only required to be
*bounded* by a polynomial (`inOPoly`, as the time bound `t` is), the class would contain
undecidable languages: with `R x c := (|c| = |x| + 1)`, which a machine decides in
polynomial time, and the bound `p n = n + [n ∈ H]` for an arbitrary set `H ⊆ ℕ`,
`x ∈ Q ⇔ |x| ∈ H`. Such a `Q` cannot reduce to `SATStr`, so the hardness half would be
false. For the time bound `t` the weaker requirement is harmless: it only bounds when the
machine halts, and every such `t` lies below an explicit polynomial.

### 4.3 What is not in the statement

The statement contains no verifier programs, no cost model and no size measure on data:
the register language of `Lang/` is a proof device (§4.6). Everything a reader has to
check is in §4.1, §4.2, §4.4, §4.5 and the reading list.

### 4.4 SAT (`Basic/Definitions.lean`, `SAT/SAT.lean`, `SAT/SATStr.lean`)

A variable is a natural number, a literal a pair `(sign, variable)`, a clause a list of
literals, a CNF a list of clauses, an assignment the list of variables set to `true`.
`evalLiteral`, `evalClause` (some literal is true) and `evalCnf` (every clause is true)
evaluate under an assignment, and `SAT N` says some assignment satisfies `N`.

`SATStr x` (`SAT/SATStr.lean`) reads the bit string `x` as a CNF and asks whether it is
satisfiable. The encoding (`EvalCnfCmd.encodeCnf`) is: a literal `(s, v)` is
`1, s, 1^v, 0` (a marker, the sign bit, the variable in unary, a terminator); a clause is
its literals followed by `0`; a CNF is the concatenation of its clauses. `SATStr.cnfOf`
parses a string with a total parser (`CnfWellFormed.parseTotal`): a string that is not an
encoding is read as the unsatisfiable formula `[[]]`, so it is outside `SATStr`.
`SATStr.satStr_iff` restates the language without the parser:
`SATStr x ↔ ∃ N, x = encodeCnf N ∧ SAT N` (as bit strings).

The variable indices are unary. A CNF with `m` literals can be renamed to use variables
below `m`, after which the encoding has length `O(m²)`, so this is polynomially equivalent to
the usual binary encoding; the renaming is not part of the formal development.

### 4.5 Polynomials (`Basic/Definitions.lean`)

`inOPoly t` says `t n ≤ c · n^k` for all `n` beyond some `n₀`. It is used for running times
only (`reducesPoly`, `inNP`); certificate lengths are bounded by an explicit polynomial
(§4.2).

### 4.6 How the proof is organised (not part of the statement)

Reductions and verifiers are written as programs of a small register language
(`Lang/Syntax.lean`, `Lang/Semantics.lean`): a state is a list of registers holding lists
of bits; nine operations (clear, append `0` or `1`, copy, tail, head, equality test,
non-emptiness test, concatenation), sequencing, a branch on a register holding `[1]`, and a
loop `forBnd` running its body once per cell of a register. Every operation has a cost: one
unit plus the lengths of the registers it reads. `inNPCmd Q` (`Lang/HardnessStr.lean`)
says that `Q` has a verifier program in this language with polynomial cost, measured in
`encodable.size` (between the length and twice the length of a string).

* `inNPCmd_inNP` (`Lang/HardnessStr.lean`): every verifier program compiles to a
  polynomial-time single-tape Turing machine (`Lang/ToMachine.lean`).
* `Sim.inNP_inNPCmd` (`Simulation/Witness.lean`): every polynomial-time verifier machine
  is simulated by a polynomial-cost verifier program. The program keeps the tape as a
  zipper of fixed-width blocks and the state in unary, performs one machine step with a
  loop-free fragment that tests the transition entries in order (`Simulation/Step.lean`),
  runs that step `T(|x| + |c|)` times for a polynomial `T` bounding the running time, and
  checks the certificate length (`Simulation/Program.lean`, `Simulation/Cost.lean`).
* `SATStrComp.satStr_NPhard`: every language in `inNPCmd` reduces to `SATStr` along the
  chain described in the README; `SATStr.inNPCmd_SATStr`: `SATStr` has a verifier program.
  `cook_levin_cmd : NPcompleteCmd SATStr` is this form of the theorem.

## 5. Sanity checks

Three files contain theorems whose only purpose is to confirm that the definitions behave
as described; they are checked by the build.

* `StatementMeaning.lean`: the theorem unfolds to the quantifier structure of §1; what a
  write does at the tape's end; a run returning `some` is not a halting claim (the halting
  conjunct is separate); the empty clause is unsatisfiable and the empty CNF satisfiable;
  and two facts about the register language of the proof (accepting and rejecting are
  distinct verdicts; the size measure on strings).
* `MachineFaithfulness.lean`: the locality and finiteness properties of §4.1.
* `SearchDecide.lean`: decidability of every language in `inNPCmd`, hence (by
  `inNP_iff_inNPCmd`) of every language in NP.

## 6. Comparison with the textbook theorem

| textbook | here |
|---|---|
| deterministic single-tape Turing machine, two-way infinite tape | `FlatTM` with one tape, one-way infinite, append-only (§4.1); equivalent up to polynomial overhead by the standard simulation, which is not formalised (§4.1) |
| input written on the tape | `stringTape`: one symbol per bit between markers (§4.2) |
| `Q ≤p P` | `Q ⪯p P` (§4.2), the same notion |
| `P ∈ NP` via a polynomial-time verifier | `inNP` (§4.2), the same notion, certificates of length at most `a·n^k + b` |
| hardness: for all `Q ∈ NP`, `Q ≤p SAT` | `NPhard SATStr` (§4.2), the same notion |
| SAT over CNF formulas in some fixed encoding | `SATStr`: CNFs in the encoding of §4.4, variables in unary |
| `SAT ∈ NP` | `SATStr_inNP` |
