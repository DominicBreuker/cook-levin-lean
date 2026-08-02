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

/-! ## §6 — the real headline, reported rather than asserted

The positive pins live in the build (`Complexity/StatementGate.lean`); this is
the reporting instrument, and it is what to run when adding an endpoint there.
Uncomment to see the full 103-name list. -/

-- #print_statement_surface CookLevinHonest.CookLevinStr

end StatementSurfaceProbe
