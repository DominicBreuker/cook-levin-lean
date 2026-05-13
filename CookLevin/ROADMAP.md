# Cook–Levin in Lean 4 — Roadmap to a Faithful Proof

This document is a candid assessment of the current state of the
Lean 4 Cook–Levin formalisation under `CookLevin/`, together with a
phased plan for turning it into an honest, mathematically rigorous
proof.

The plan is organised so that each phase produces a strict improvement
over the previous one, leaves the project building, and keeps the parts
that are already sound (the FlatTCC → FlatCC → BinaryCC → FSAT → SAT
combinatorial core, the Tseytin transform, and the `FlatTM` semantics).

---

## Part 0 — Honest assessment of the current state

The repository currently establishes
`theorem CookLevin : NPcomplete SAT`, but the term it produces is
**not** a faithful proof of the Cook–Levin theorem. Five separate
classes of issues, listed in roughly increasing difficulty to fix:

### 0.1 The complexity framework does not constrain runtime

In `Complexity/Complexity/NP.lean`:

- `PolyTimeComputableWitness f` only requires
  `encodable.size (f x) ≤ bound (encodable.size x)`. This bounds the
  *output size*, not the *running time*. So `polyTimeComputable f`
  literally means "f has polynomially-bounded output", which is much
  weaker than poly-time computable.
- `HasDecider X P f := ∃ dec : X → Bool, ∀ x, P x ↔ dec x = true`. The
  argument `f : Nat → Nat` is unused. A function that is `Classical`-
  noncomputable can satisfy this.
- `inTimePoly P := ∃ f, HasDecider X P f ∧ inOPoly f ∧ monotonic f`.
  Inherits the weakness of `HasDecider`.

### 0.2 `NPhard_GenNP` is vacuous

`Complexity/GenNP_is_hard.lean` line 9 introduces

```
theorem hasDeciderClassical (P : X → Prop) (timeBound : Nat → Nat) :
    HasDecider X P timeBound := by
  classical
  refine ⟨fun x => if P x then true else false, ?_⟩
  …
```

This is used in `genNPInstance` (line 46) and `NPhard_GenNP` (line 81).
Because of (0.1), this theorem builds a "decider" via
`Classical.choice` for *any* predicate with *any* alleged time bound.
Therefore `NPhard_GenNP` as currently stated proves NP-hardness for
every classical predicate including the undecidable ones — the
underlying definitions are unsound as a model of "P ∈ NP ⇒ P ⪯p
GenNP".

### 0.3 The TM bridge layers are dummies

- `Complexity/LM_to_mTM.lean`: `bridgeMachine` is a 1-state, 0-transition
  flat TM that starts in a halting state.
  `bridgeMachine_accepts` is trivially true for any tapes and any step
  count. The actual L-or-LMGenNP-to-multi-tape simulator is absent.
- `Complexity/mTM_to_singleTapeTM.lean`: same pattern with a 1-tape
  variant. The multi-tape machine `M` is passed in and immediately
  discarded by `M__mono`.
- `Complexity/L_to_LM.lean`: a definitional repackaging — there is no
  TM at all.
- `Complexity/NP/SAT/CookLevin/Reductions/`
  `TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean`:
  `noncomputable def f inst := if TMGenNP_fixed M inst then yesInst else
  noInst`. The map's value depends on the *answer* to the source
  language, so it's not computable.
- `Complexity/NP/SAT/CookLevin/Reductions/`
  `FlatSingleTMGenNP_to_FlatTCC.lean` (line 127-133): same `if`-on-the-
  answer pattern, returning a trivially-accepting TCC instance or
  a trivially-rejecting one.

### 0.4 Definitional smells

- `instEncodableDefault` (`Definitions.lean:14`) silently defaults to
  `size := 0` for any type without an explicit instance. This is the
  reason a `bound := fun _ => 0` typechecks for `LMGenNP.Instance`,
  `mTMGenNPFixedInput`, `TMGenNPFixedInput`.
- `abbrev TM (_σ : Type) (_ : Nat) := FlatTM` (`Definitions.lean:61`):
  the alphabet `σ` and tape count `k` are phantom — *any* `FlatTM` has
  type `TM σ k` for any `σ`, `k`.
- `computableTime'` in `MachineSemantics.lean:186` — a leftover Coq
  port hook whose current definition collapses to a uniform-bound on
  `f`, with no link to the machine `M`.

### 0.5 Outstanding `sorry`s

```
Complexity/NP/SAT.lean:206              compressAssignment_size_bound
Complexity/NP/FSAT_to_SAT.lean:706      FSAT_to_SAT_size_le
Complexity/NP/FlatClique.lean:38        clique_size_bound
Complexity/NP/kSAT_to_FlatClique.lean:63 polynomial-time bound
Complexity/NP/kSAT_to_FlatClique.lean:64 reduction correctness
```

### What is already sound and should not be touched

- `Complexity/Complexity/MachineSemantics.lean` — the `FlatTM` semantics
  and `runFlatTM` are real.
- `Complexity/Complexity/Definitions.lean` — `encodable`,
  `inOPoly`, `monotonic`, and analytic lemmas, including the polynomial
  composition `inOPoly_comp`.
- `Complexity/Complexity/NP.lean` — the reduction calculus
  (`reducesPolyMO_reflexive`, `reducesPolyMO_transitive`, `red_inNP`,
  `red_NPhard`) is correct given its definitions.
- The combinatorial core
  `FlatTCC_to_FlatCC ⋅ FlatCC_to_BinaryCC ⋅ BinaryCC_to_FSAT`:
  ~3000 lines of fully proved, computable reductions with real size
  bounds (`5n+5`, `50n² + 50n + 1`, `500n⁶ + 500`).
- `Complexity/NP/SAT.lean` (except line 206), `kSAT.lean`,
  `kSAT_to_SAT.lean`, `FSAT.lean`.
- `Complexity/NP/FSAT_to_SAT.lean` (Tseytin transformation, except the
  size bound at line 706).

## Part 1 — Foundational hygiene (low cost, high signal)

These are local cleanups that make subsequent phases easier and remove
loose ends without changing the proof architecture.

**P1.1 Remove the silent `instEncodableDefault` fallback.**
Either delete `instEncodableDefault` (`Definitions.lean:14`) or rename
it to a non-default `encodable.trivial` that must be invoked
explicitly. Then add real `encodable` instances for `GenNPInput`,
`LMGenNP.Instance`, `mTMGenNPFixedInput`, `TMGenNPFixedInput`. This
will expose every place that currently relies on `size = 0`.

**P1.2 Make `TM σ k` a real type, not an abbrev.**
Introduce a structure `TM (σ : Type) (k : Nat)` that bundles a `FlatTM
M` with proofs `M.sig = encodable.size σ` (or the size of a finite
enumeration of `σ`) and `M.tapes = k`. The current `abbrev` lets every
"bridgeMachine" lie about its alphabet and tape count.

**P1.3 Delete `Complexity/Complexity/Subtypes.lean`.**
Empty file, contributes nothing.

**P1.4 Move the "Legacy constructions" block.**
`Complexity/NP/FSAT_to_SAT.lean` lines 726–754 (`FSAT_to_SAT_yes/no`,
`FSAT_to_3SAT_yes/no`, `FSAT_search`) are remnants of an earlier fake
reduction and are not on the proof path. Either delete them or move
them to a clearly-named appendix file.

**P1.5 Clear the "small" `sorry`s.**
The five remaining `sorry`s are all genuinely provable lemmas. They
should be discharged in this phase so the project becomes
`sorry`-free *modulo* the structural issues addressed below. Order
of difficulty:
- `clique_size_bound` (`FlatClique.lean:38`) — straightforward list
  length bound.
- `compressAssignment_size_bound` (`SAT.lean:206`) — bound the dedup
  of a filtered assignment.
- `FSAT_to_SAT_size_le` (`FSAT_to_SAT.lean:706`) — induction over the
  Tseytin recursion structure.
- `kSAT_to_FlatClique_poly` (`kSAT_to_FlatClique.lean:63-64`) —
  the construction is in place; the correctness proof has not been
  written yet. This is a real reduction proof and may take ~300 LOC.

After Part 1 the project is `sorry`-free with the *current* (still
weak) definitions, all encodings are explicit, and the cleanup
landscape is clear.

## Part 2 — Strengthen the framework to a real `inTimePoly` (the user's R1)

Currently `HasDecider X P f` is propositional and `f` is unused. The
fix is to replace it with a TM-backed predicate.

**P2.1 Replace `HasDecider` with a TM-backed witness.**
In `Complexity/Complexity/NP.lean` replace

```
def HasDecider (X : Type) (P : X → Prop) (f : Nat → Nat) : Prop :=
  ∃ dec : X → Bool, ∀ x, P x ↔ dec x = true
```

with

```
structure DecidesBy {X : Type} [encodable X]
    (P : X → Prop) (timeBound : Nat → Nat) where
  encode : X → List Nat                                -- input → tape word
  encode_size : ∀ x, (encode x).length ≤ encodable.size x + const
  M : FlatTM
  M_valid : validFlatTM M
  -- one-tape machine running on encode(x), terminating in
  -- ≤ timeBound (encodable.size x) steps, ending in a halting state
  -- whose result symbol encodes the truth value of P x
  decides : ∀ x, ∃ cfg,
    runFlatTM (timeBound (encodable.size x)) M
      (initFlatConfig M [encode x]) = some cfg ∧
    haltingStateReached M cfg = true ∧
    readOutput cfg = decideBool (P x)
```

(A 2-state "accept/reject" output convention or a designated output
tape will need to be fixed; the Coq port uses a Boolean output via the
state index.) Then redefine

```
def inTimePoly {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ f, Nonempty (DecidesBy P f) ∧ inOPoly f ∧ monotonic f
```

**P2.2 Re-prove `SAT_inNP.sat_NP` and `FlatClique_in_NP` against the
new definition.** Both `evalCnf` and `cliqueRelDec` (currently
`noncomputable`) need an explicit polynomial-time TM. This requires a
mini-library of "Boolean primitives on a flat TM": copy a tape segment,
compare two segments, loop counters, etc. ~1000 LOC of TM-bookkeeping.

**P2.3 Re-prove `red_inNP`** so that the composed decider for the
reduced problem is a TM that first runs the reduction's TM and then
runs the certificate-checking TM.

After Part 2, `inTimePoly` and `inNP` genuinely mean what they say.

## Part 3 — Strengthen `polyTimeComputable` (the user's R2)

`PolyTimeComputableWitness f` currently bounds only the output size.
Replace it with a TM that *computes* `f`.

**P3.1 New witness.**

```
structure PolyTimeComputableWitness {X Y : Type} [encodable X] [encodable Y]
    (f : X → Y) where
  time_bound : Nat → Nat
  bound_poly : inOPoly time_bound
  bound_mono : monotonic time_bound
  encode_in  : X → List Nat
  decode_out : List Nat → Y
  M : FlatTM
  M_valid : validFlatTM M
  computes :
    ∀ x, ∃ cfg,
      runFlatTM (time_bound (encodable.size x)) M
        (initFlatConfig M [encode_in x]) = some cfg ∧
      haltingStateReached M cfg = true ∧
      decode_out (readTape cfg) = f x
```

(Plus the obvious "output size bounded" corollary.)

**P3.2 Re-prove every `_poly` theorem currently in the chain against
this stronger definition.** Concretely, this means *constructing* a
poly-time TM for each of:
- `kSAT_to_SAT_reduction` (trivial: it is `if … then N else [[]]`,
  which is a one-pass O(|N|) algorithm)
- `FSAT_to_SAT_tseytin` (the Tseytin transform — already explicitly
  computable; needs a TM implementation of the recursion)
- `kSAT_to_FlatClique_instance` (the graph construction)
- `flatTCC_to_flatCC`, `FlatCC_to_BinaryCC_instance`,
  `BinaryCC_to_FSAT_instance`

For each, the combinatorial encoding work is already done; what's new
is the TM-construction obligation. This is where the bulk of the new
Lean proof effort lives — roughly 3000–4000 LOC of TM primitives plus
per-reduction simulation lemmas.

**P3.3 Reflexivity/transitivity.** `reducesPolyMO_reflexive` is the
"identity" TM; `reducesPolyMO_transitive` is sequential composition of
two TMs, which requires a "run M, then run N on M's output" combinator
in the TM library.

After Part 3, `⪯p` is a real polynomial-time many-one reduction.

## Part 4 — Replace the dummy TM bridges (the user's R3)

This is the largest engineering item. The empty `bridgeMachine`s in
`LM_to_mTM.lean` and `mTM_to_singleTapeTM.lean` need to become actual
simulators.

**P4.1 Decide the source-language model.** The Coq port uses the L
calculus together with `computableTime'` extraction. There are two
realistic choices for the Lean port:

  - (a) **Drop the L layer entirely.** Treat `GenNPInput`/`LMGenNP` as
    abstract "NP source" formulations whose only purpose is to bridge
    to `mTMGenNP_fixed`. Then the entire "L → LM → mTM" tower can be
    collapsed into a single "GenNP → mTMGenNP_fixed" reduction that
    builds a deterministic multi-tape TM out of the verifier
    advertised by `inNP`. This is roughly the construction used in
    most textbook proofs (Sipser, Arora-Barak) and is the recommended
    path for a Lean port.
  - (b) **Port L.** Faithfully replicate the Coq L calculus and its
    `computableTime'` API. This is the most faithful port but adds
    many thousands of lines of L-calculus infrastructure.

Recommendation: (a). The L calculus is not specifically required by
Cook–Levin; it is a Coq-port artifact.

**P4.2 Build a real multi-tape → single-tape simulator.**
This is the standard textbook construction: encode the `k` tapes onto
a single tape using a delimiter symbol and a "head-marker" extension
of the alphabet. The simulator processes one source step in O(L) target
steps where L is the current total tape length, giving a quadratic
time blow-up. Replace `bridgeMachine` in `mTM_to_singleTapeTM.lean`
with this construction and prove `acceptsFlatTM M' ↔ acceptsFlatTM M`
(with the time bound transformed by the quadratic).

**P4.3 Build the GenNP → mTM reduction.**
Given an `InNPWitness P` whose certificate-checking relation is now
decided by an actual TM (Part 2), construct a non-deterministic
multi-tape TM that guesses a certificate of size ≤ certBound and runs
the verifier. (Or, since the chain targets *deterministic* TMs at the
single-tape level, simulate the non-determinism by enumerating
certificates with an explicit "advice tape".)

After Part 4, the L → LM → mTM → 1-tape tower is replaced by a real
simulator chain.

## Part 5 — Replace the FlatSingleTMGenNP → FlatTCC reduction

This is the actual heart of Cook–Levin: the Cook tableau construction.
The current implementation is `if FlatSingleTMGenNP inst then trivial-yes
else trivial-no`, which is the only step the Coq port writes out in
full and the only step we currently fake.

**P5.1 Implement the tableau construction.** For a TM `M` on input `s`
with step budget `steps`, build a `FlatTCC` instance whose
- `init` is the start configuration encoded as a row of width
  `1 + |s| + steps + 1` (state plus tape, with a head marker),
- `cards` encode the local 3-cell transitions of `M`,
- `final` matches if and only if a halting state appears somewhere in
  the final row,
- `Sigma` is the alphabet of M plus state symbols plus a head marker.

This is the famous Cook 2D tableau and there are many model proofs
to follow (notably the existing Coq port's
`SingleTMGenNP_to_TCC.v`).

**P5.2 Prove the bijection.** `FlatSingleTMGenNP (M,s,maxSize,steps)
↔ FlatTCC (encode M s steps)` — both directions, with the explicit
tableau-to-run bijection.

**P5.3 Prove the size bound.** The encoding is linear in `(|s| +
steps) · |Σ|`, polynomial in the input size.

After Part 5, the chain from "M accepts s in `steps` steps" to "the
FlatTCC tableau is satisfiable" is real, and the FlatTCC → FlatCC →
BinaryCC → FSAT → SAT chain (which is *already* sound) finishes the
proof.

## Part 6 — Replace `NPhard_GenNP` (the user's R4)

Once Parts 2–4 are in place, `hasDeciderClassical` can be deleted: the
generic NP-hardness of `GenNP` follows from the construction
"take the (now real) verifier TM, package it as a `GenNPInput`". This
phase is essentially mechanical once the framework is sound.

**P6.1 Delete `hasDeciderClassical`** and replace its use in
`genNPInstance` with the real verifier TM coming from `InNPWitness`'s
new (Part 2) `inTimePoly`.

**P6.2 Re-state `NPhard_GenNP`** in terms of the strengthened framework
and verify the proof goes through.

**P6.3 Audit `CanEnumTerm`.** The `boollists_enum_term` encoding
(`CanEnumTerm.lean:40`) is not an injection; in a real framework the
certificate must be recoverable, so this needs to be replaced with a
proper binary encoding `Y → List Bool` (i.e. a real Gödel numbering).
Mathlib's `Encodable`/`Denumerable` infrastructure may be reusable
here.

## Part 7 — Final assembly and CI

**P7.1 End-to-end test.** With Parts 1–6 in place, `theorem CookLevin
: NPcomplete SAT` is rebuilt against the new definitions. Verify the
build is `sorry`-free, axiom-free (beyond `propext`, `Classical.choice`
where unavoidable, and `Quot.sound`), and reproduces.

**P7.2 Print-the-axioms check.** Add a small file that runs
`#print axioms CookLevin` (and the same for `CookLevin0`,
`Clique_complete`). Document the surviving axioms.

**P7.3 Make a CI target** that fails if any new `sorry` or
`hasDeciderClassical`-style classical shortcut creeps in.

**P7.4 Documentation pass.** Update `README.md` to reflect the new
state, and add a short "axioms used" appendix.

---

## Suggested phase ordering and effort estimate

| Phase | Description                          | Estimated LOC | Risk |
|-------|--------------------------------------|---------------|------|
| 1     | Cleanup & `sorry` discharge          |  ~500         | low |
| 2     | TM-backed `inTimePoly`               | ~1500         | med |
| 3     | TM-backed `polyTimeComputable`       | ~4000         | high |
| 4     | Real multi-tape → 1-tape simulator   | ~3000         | high |
| 5     | Cook tableau (TM → FlatTCC)          | ~3000         | high |
| 6     | Real `NPhard_GenNP`                  |  ~500         | low |
| 7     | CI / docs                            |  ~100         | low |

The phases are *almost* independent but in practice Part 2 unlocks
Part 3, Part 3 unlocks Parts 4–5, and Part 6 depends on all of them.
A reasonable cadence is to land Part 1 first, then alternate between
infrastructure (Parts 2–3) and Cook–tableau content (Part 5), since
Part 5's TM construction is large but does not depend on Part 4.

## Things NOT to break while doing this

Each phase should preserve the build and each new definition should
keep the existing real-mathematical content compiling:

- `FlatTM` semantics in `MachineSemantics.lean`.
- `inOPoly`, `inOPoly_add`, `inOPoly_comp` in `Definitions.lean`.
- The full Tseytin transformation in `FSAT_to_SAT.lean`.
- The 3-level tableau core
  `FlatTCC_to_FlatCC`, `FlatCC_to_BinaryCC`, `BinaryCC_to_FSAT`.
- `SAT_inNP.sat_NP` modulo the size-bound `sorry`.
- The reduction calculus (`⪯p`, `red_NPhard`, `red_inNP`).

In particular, when introducing the stronger
`PolyTimeComputableWitness` in Part 3, the prudent path is to
*add* it as a new structure (e.g. `PolyTimeComputableTMWitness`) and
keep the existing one alive until every consumer is migrated, then
delete the old one in a single sweep at the end of Part 3.
