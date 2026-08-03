import Complexity.StatementGate

set_option autoImplicit false

/-! # Negative controls for the statement-surface gate (~10 s)

`Complexity/StatementGate.lean` claims that the lists it carries are the
**complete** set of this repository's definitions the headline statements are
built from. That claim is only worth something if the machinery behind it can
actually fail, and fails for the right reasons. This file exhibits that on toy
declarations whose surface a reader can verify by eye.

Re-run after any change to `Complexity/Meta/StatementSurface.lean`. Every
section below must elaborate **silently**: `#guard_msgs` turns a wrong answer
into an error, so "no output" is the pass condition.

Run it with:

```
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_PATH=$(lake env printenv LEAN_PATH)
lean probes/StatementSurfaceProbe.lean
```
-/

namespace StatementSurfaceProbe

/-! ## §1 — a definition in the STATEMENT is in the surface

`toyUsed` occurs in the type of `toyStatementDep`, so it must be reported. Note
what is *not* reported: `Nat`, `OfNat.ofNat`, `Eq` — Lean core is the trust
boundary, and this development's claim is only about its own definitions. -/

def toyUsed : Nat := 7

theorem toyStatementDep : toyUsed = 7 := rfl

/-- info: statement surface of 'StatementSurfaceProbe.toyStatementDep': 1 of 1
  StatementSurfaceProbe.toyUsed -/
#guard_msgs in
#print_statement_surface toyStatementDep

/-! ## §2 — a definition used only in the PROOF is NOT in the surface

This is the design decision the gate rests on, and it is the one most likely to
be misread as a hole. It is not: a proof cannot change what a statement means,
and whether the proof is *valid* is `#assert_axioms_clean`'s job — including the
case (standing architecture risk #7) where a `sorry` hides inside a `def` that a
statement mentions, which `collectAxioms` walks statements precisely to catch.

`toyProofOnly` is used by `toyAux`, which is used by `toyProofDep`'s proof.
Neither may appear. -/

def toyProofOnly : Nat := 8

theorem toyAux : toyProofOnly = 8 := rfl

theorem toyProofDep : toyUsed = 7 := by
  have _ := toyAux
  rfl

/-- info: statement surface of 'StatementSurfaceProbe.toyProofDep': 1 of 1
  StatementSurfaceProbe.toyUsed -/
#guard_msgs in
#print_statement_surface toyProofDep

/-! ## §3 — the surface is TRANSITIVE through definition bodies

`toyTransitive`'s statement mentions only `toyWrapper` syntactically; the gate
must still report `toyUsed`, because unfolding `toyWrapper` is how a reader
learns what it says. A gate that only looked one level deep would let a session
arbitrary definition one `abbrev` away from the headline. -/

def toyWrapper : Nat := toyUsed + 1

theorem toyTransitive : toyWrapper = 8 := rfl

/-- info: statement surface of 'StatementSurfaceProbe.toyTransitive': 2 of 2
  StatementSurfaceProbe.toyUsed
  StatementSurfaceProbe.toyWrapper -/
#guard_msgs in
#print_statement_surface toyTransitive

/-! ## §4 — an INCOMPLETE list fails the gate

The failure a reviewer cares about: someone adds a definition to a headline's
statement and does not tell anyone. Here the list omits `toyWrapper`. -/

/--
error: statement-surface gate FAILED for 'StatementSurfaceProbe.toyTransitive'
  reachable from the statement but NOT listed (1) — the trusted surface GREW:
    StatementSurfaceProbe.toyWrapper
  ⚠ Do not just paste the new list in. A name appearing here means the STATEMENT of the headline changed; say in `README.md` what a reviewer now has to read, and why.
-/
#guard_msgs in
#assert_statement_surface toyTransitive =>
  toyUsed

/-! ## §5 — a STALE list fails the gate too

The gate asserts equality, not containment, so a name that has fallen out of the
statement is also a failure. Without this direction the list would rot into a
superset that says nothing. -/

/--
error: statement-surface gate FAILED for 'StatementSurfaceProbe.toyStatementDep'
  listed but NOT reachable (1) — the list is stale:
    StatementSurfaceProbe.toyProofOnly
  ⚠ Do not just paste the new list in. A name appearing here means the STATEMENT of the headline changed; say in `README.md` what a reviewer now has to read, and why.
-/
#guard_msgs in
#assert_statement_surface toyStatementDep =>
  toyUsed
  toyProofOnly

/-! ## §6 — the DELTA form: what a gate costs beyond a baseline

`Complexity/GateSurfaceGate.lean` meters the *instruments* rather than the
headline, and it does so as a difference — a gate about the headline shares
nearly all of the headline's surface, so only the difference carries
information. The three sections below are that command's negative controls.

`toyTransitive`'s surface is `{toyUsed, toyWrapper}` and `toyStatementDep`'s is
`{toyUsed}`, so the delta is exactly `{toyWrapper}`. -/

/-- info: statement surface of 'StatementSurfaceProbe.toyTransitive' beyond 'StatementSurfaceProbe.toyStatementDep': 1 new, 1 already read
  StatementSurfaceProbe.toyWrapper -/
#guard_msgs in
#print_statement_surface_delta toyTransitive beyond toyStatementDep

/-! The empty delta — the strongest outcome, and the one four of
`GateSurfaceGate.lean`'s entries report. A baseline that already covers the
whole surface costs a reader nothing further. -/
#assert_statement_surface_delta toyStatementDep beyond toyTransitive =>
  -- (empty)

/-! ## §7 — an UNDER-declared delta fails

The failure that matters here: an instrument quietly starts depending on
something the baseline does not cover, i.e. believing the gate gets more
expensive and nobody is told. -/

/--
error: statement-surface delta gate FAILED for 'StatementSurfaceProbe.toyTransitive' beyond 'StatementSurfaceProbe.toyStatementDep'
  read by 'StatementSurfaceProbe.toyTransitive' but not by 'StatementSurfaceProbe.toyStatementDep' and NOT listed (1) — this gate now costs a reviewer MORE:
    StatementSurfaceProbe.toyWrapper
  ⚠ Do not just paste the new list in. A name here means the price of BELIEVING one of this development's instruments changed; say what and why in `README.md`.
-/
#guard_msgs in
#assert_statement_surface_delta toyTransitive beyond toyStatementDep =>
  -- (empty, and wrongly so)

/-! ## §8 — an OVER-declared delta fails too

Equality, not containment, in this direction as well: a listed name that the
baseline turns out to cover is a stale claim about the price. -/

/--
error: statement-surface delta gate FAILED for 'StatementSurfaceProbe.toyStatementDep' beyond 'StatementSurfaceProbe.toyTransitive'
  listed but not actually extra (1) — either the gate shrank or the baseline grew:
    StatementSurfaceProbe.toyUsed
  ⚠ Do not just paste the new list in. A name here means the price of BELIEVING one of this development's instruments changed; say what and why in `README.md`.
-/
#guard_msgs in
#assert_statement_surface_delta toyStatementDep beyond toyTransitive =>
  toyUsed

/-! ## §9 — the SHAPE forms: presence and absence

`#assert_statement_surface_contains` / `_omits` are deliberately weaker than the
exact form — they pin individual names rather than the whole set. They exist for
`GateSurfaceGate.lean` §1, where the interesting content of two 60-name surfaces
is six presences and six absences (the two conjuncts of the headline rest on
disjoint vocabularies). Both must be able to fail, in both directions. -/

#assert_statement_surface_contains toyTransitive =>
  toyUsed
  toyWrapper

#assert_statement_surface_omits toyTransitive =>
  toyProofOnly

/--
error: statement-surface CONTAINS gate FAILED for 'StatementSurfaceProbe.toyTransitive': 1 listed name(s) are NOT reachable from its statement
    StatementSurfaceProbe.toyProofOnly
  ⚠ The statement no longer rests on what this gate says it rests on. Say what changed in `README.md`.
-/
#guard_msgs in
#assert_statement_surface_contains toyTransitive =>
  toyProofOnly

/--
error: statement-surface OMITS gate FAILED for 'StatementSurfaceProbe.toyTransitive': 1 listed name(s) ARE reachable from its statement
    StatementSurfaceProbe.toyWrapper
  ⚠ A definition this statement was claimed to be independent of has entered it. This is a strictly weaker theorem than advertised; say so in `README.md`.
-/
#guard_msgs in
#assert_statement_surface_omits toyTransitive =>
  toyWrapper

/-! ⚠ **`_omits` sees the raw closure, generated companions included.** The
report filter hides recursors, `casesOn`s and structure constructors because a
*reading list* should not show them; an **absence** claim may not use that
filter, or "this statement does not mention `Foo`" could be satisfied by a
statement that reaches `Foo.mk`. `ToyPair.mk` is filtered out of the report
below and must still be caught by `_omits`. -/

structure ToyPair where
  fst : Nat
  snd : Nat

theorem toyPairStatement : (ToyPair.mk 1 2).fst = 1 := rfl

/-- info: statement surface of 'StatementSurfaceProbe.toyPairStatement': 2 of 3
  StatementSurfaceProbe.ToyPair
  StatementSurfaceProbe.ToyPair.fst -/
#guard_msgs in
#print_statement_surface toyPairStatement

/--
error: statement-surface OMITS gate FAILED for 'StatementSurfaceProbe.toyPairStatement': 1 listed name(s) ARE reachable from its statement
    StatementSurfaceProbe.ToyPair.mk
  ⚠ A definition this statement was claimed to be independent of has entered it. This is a strictly weaker theorem than advertised; say so in `README.md`.
-/
#guard_msgs in
#assert_statement_surface_omits toyPairStatement =>
  StatementSurfaceProbe.ToyPair.mk

/-! ## §10 — the real headline, reported rather than asserted

The positive pins live in the build (`Complexity/StatementGate.lean`); this is
the reporting instrument, and it is what to run when adding an endpoint there.
Uncomment to see the full 103-name list. -/

-- #print_statement_surface CookLevinHonest.CookLevinStr

end StatementSurfaceProbe
