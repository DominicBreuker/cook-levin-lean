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

1. **hardness**: for every language `Q ⊆ {0,1}*` that has a polynomial-cost verifier
   program (`inNPCmd Q`, §4.3) there are a function `f : {0,1}* → {0,1}*`, a single-tape
   Turing machine `M` and a polynomial `t` such that `M`, started on the tape holding `x`,
   halts within `t(|x|)` steps with `f(x)` written on the tape, and `x ∈ Q ⇔ f(x) ∈ SATStr`;
2. **membership**: `SATStr` has a polynomial-cost verifier program.

Two further theorems in the same file state membership at the level of Turing machines and
relate the two notions of "verifier":

```lean
theorem SATStr_inNP : inNP SATStr             -- a polynomial-time Turing-machine verifier
theorem inNPCmd_subset_inNP : ∀ Q, inNPCmd Q → inNP Q
```

`inNP` is the textbook verifier definition of NP (§4.2). So the hardness half is proved for
a class `inNPCmd` that is contained in NP; whether it is all of NP is discussed in §4.3.

## 2. What you have to trust

1. **Lean's kernel and its three standard axioms** `propext`, `Classical.choice`,
   `Quot.sound`. The build itself checks that nothing else is used anywhere in the library
   (`#assert_library_axiom_clean CookLevin` in `CookLevin.lean`); `sorry` counts as an axiom
   and is therefore excluded. You can also run `#print axioms CookLevin.cook_levin`.
2. **The definitions the statement is built from.** A theorem is only as good as its
   statement. `CookLevin/ReadingList.lean` lists every definition of this repository that
   the statement of `cook_levin` (and of `SATStr_inNP`) depends on, and the build fails
   unless the list is exact. Everything the statement mentions that is not on the list comes
   from Lean's core library (`List`, `Nat`, `Bool`, …); Mathlib is used in proofs only.
   §4 walks through the list.

Nothing about the *proof* has to be read: it is checked by the kernel. Nothing about the
*reduction* has to be read either: the theorem asserts that a machine with the stated
properties exists, so a wrong construction could only have made the proof fail.

## 3. What the build checks

`lake build` elaborates every file and runs three kinds of build-time checks:

* the axiom check above;
* the reading list (`ReadingList.lean`);
* the sanity checks of `StatementMeaning.lean`, `MachineFaithfulness.lean` and
  `SearchDecide.lean` (§5), which are ordinary theorems about the definitions.

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

Two details differ from the usual textbook picture, both in the direction that makes the
machine weaker and the hardness statement therefore stronger:

* the tape is one-way infinite: moving left at cell `0` leaves the head at `0`;
* the tape is append-only: a write is performed when the head is at or before the end of
  the written region and dropped when it is strictly beyond it (a head can be moved beyond
  the region; it then reads blanks). A machine can therefore never create an unwritten gap.

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
* `inNP Q`: there are a relation `R` on pairs of strings, polynomials `p`, `t`, a valid
  single-tape machine `M` and two states `acc`, `rej` such that `M` on `pairTape x c` halts
  within `t (|x| + |c|)` steps, in state `acc` exactly when `R x c` and in state `rej`
  exactly when not (`decidesPairInTime`), and `x ∈ Q` iff some `c` with `|c| ≤ p |x|` has
  `R x c`. This is the verifier definition of NP.

### 4.3 Verifier programs (`Lang/Syntax.lean`, `Lang/Semantics.lean`, `Lang/PolyTime.lean`, `Lang/HardnessStr.lean`)

The hypothesis of the hardness half is not `inNP Q` but `inNPCmd Q`: `Q` has a verifier
written in a small register language. This is the one place where the development departs
from the textbook, and the reason is practical: reductions are written as programs of this
language and compiled to Turing machines, so hardness is naturally proved for languages
whose verifier is itself such a program.

The language (`Lang/Syntax.lean`): a state is a list of registers, each a list of natural
numbers (in every program used here, of bits). The nine operations clear a register, append
`0` or `1`, copy, take the tail or the head of a register, test two registers for equality,
test a register for non-emptiness, and concatenate two registers into a third. Commands are
operations, sequencing, a branch on whether a register holds exactly `[1]`, and a loop
`forBnd counter bound body` that runs `body` once per element of the `bound` register,
with the iteration index in unary in `counter`. Register `0` holds the verdict: `[1]`
accepts, `[0]` rejects. `Lang/Semantics.lean` gives the meaning (`Cmd.eval`) and the cost
(`Cmd.cost`): one unit per control step, plus the lengths of the registers an operation
reads.

`NPWitness Q` (`Lang/PolyTime.lean`) is a certificate relation `rel` together with a
program deciding it on the layout `encX x ++ certState c` within a polynomial cost bound
(`DecidesLang`), the requirement that `rel` is sound and complete for `Q` with certificates
of polynomial size (`polyCertRel`, `Basic/NP.lean`), and bounds on the layout `encX`.
`NPWitnessStr` (`Lang/HardnessStr.lean`) fixes `encX x = certState x`: one register holding
the bits of `x`. `inNPCmd Q` says such a witness exists.

What is proved about this class:

* `inNPCmd_subset_inNP`: every language in `inNPCmd` is in `inNP` — the verifier program
  compiles to a polynomial-time Turing machine (`Lang/ToMachine.lean`). So the cost model
  of the language never undercounts machine time by more than a polynomial.
* `SearchDecide.searchDecide_correct`: every language in `inNPCmd` is decidable, by running
  the verifier on all short certificates. The class is not degenerate.

What is not proved is the converse inclusion `inNP ⊆ inNPCmd`, i.e. that every
polynomial-time Turing machine can be simulated by a program of the register language at
polynomial cost. That is the usual simulation of a Turing machine by a while-program with
unary counters and is expected to hold, but it is not formalised. The hardness half is
therefore a statement about `inNPCmd`, a subclass of NP that contains `SATStr`.

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

### 4.5 Sizes (`Basic/Definitions.lean`)

The cost bounds of verifier programs are stated in `encodable.size`, a size measure on
the input type. On a bit string it lies between the length and twice the length
(`StatementMeaning.size_faithful_lower`, `size_faithful_upper`), so "polynomial in the
size" is "polynomial in the length"; on natural numbers it is the number itself (unary).
All statements about Turing machines in §4.2 use the length `|x|` directly.

## 5. Sanity checks

Three files contain theorems whose only purpose is to confirm that the definitions behave
as described; they are checked by the build.

* `StatementMeaning.lean`: the theorem unfolds to the quantifier structure of §1; accept and
  reject are two distinct verdicts, so a program is obliged to reject; what a write does at
  the tape's end; a run returning `some` is not a halting claim (the halting conjunct is
  separate); the empty clause is unsatisfiable and the empty CNF satisfiable; the size
  measure is as described.
* `MachineFaithfulness.lean`: the locality and finiteness properties of §4.1.
* `SearchDecide.lean`: decidability of every language in `inNPCmd`.

## 6. Comparison with the textbook theorem

| textbook | here |
|---|---|
| deterministic single-tape Turing machine, two-way infinite tape | `FlatTM` with one tape, one-way infinite, append-only (§4.1); both restrictions weaken the machine |
| input written on the tape | `stringTape`: one symbol per bit between markers (§4.2) |
| `Q ≤p P` | `Q ⪯p P` (§4.2), the same notion |
| `P ∈ NP` via a polynomial-time verifier | `inNP` (§4.2), the same notion |
| hardness: for all `Q ∈ NP`, `Q ≤p SAT` | for all `Q ∈ inNPCmd`, `Q ⪯p SATStr`, where `inNPCmd ⊆ inNP` is the class of languages with a verifier program (§4.3) |
| SAT over CNF formulas in some fixed encoding | `SATStr`: CNFs in the encoding of §4.4, variables in unary |
| `SAT ∈ NP` | `SATStr_inNP` |
