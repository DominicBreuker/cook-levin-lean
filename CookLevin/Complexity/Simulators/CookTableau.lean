import Complexity.Complexity.MachineSemantics
import Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP

set_option autoImplicit false

/-! # Cook tableau construction (skeleton, Part 6 of ROADMAP)

The actual heart of the Cook–Levin theorem: given a single-tape TM
`M` on input `s` with step budget `steps`, build a `FlatTCC`
instance whose satisfiability is equivalent to `M` accepting `s`
within `steps` steps.

This skeleton commits to the construction's signature and the
headline bi-implication. The implementation is Part 6.1; the proof
is Part 6.2; the size bound is Part 6.3.

The current placeholder in
`Complexity/NP/SAT/CookLevin/Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`
is `if FlatSingleTMGenNP inst then trivial-yes else trivial-no`,
which case-splits on the answer. The real construction is a
*function* of `(M, s, steps)`, computable, with no `if-on-answer`. -/

namespace Complexity.Simulators

/-- The Cook 2D tableau as a `FlatTCC` instance.

**Skeleton stub.** Returns a `FlatTCC.mk` with placeholder fields.
Replace in Part 6.1 with the real `2D` tableau:

- `Sigma`   : `M`'s alphabet plus state symbols plus a head marker.
- `init`    : the start configuration encoded as a row of width
              `1 + |s| + steps + 1`.
- `cards`   : the local 3-cell transition cards encoding `M`'s steps.
- `final`   : `[[halt-symbol]]`-like patterns matching halting states.
- `steps`   : `steps`.

The construction is linear in `(|s| + steps) · |Σ|`. -/
noncomputable def cookTableau (M : FlatTM) (s : List Nat) (steps : Nat) :
    FlatTCC :=
  { Sigma := M.sig + M.states + 1
    init := []  -- TODO(Part6.1)
    cards := []  -- TODO(Part6.1)
    final := []  -- TODO(Part6.1)
    steps := steps }

/-- The tableau is a well-formed `FlatTCC` instance. -/
theorem cookTableau_wellformed (M : FlatTM) (s : List Nat) (steps : Nat)
    (_hValid : validFlatTM M) :
    FlatTCC.FlatTCC_wellformed (cookTableau M s steps) ∧
    FlatTCC.isValidFlattening (cookTableau M s steps) := by
  sorry  -- TODO(Part6.1)

/-- **Main bijection (Part 6.2).** A TM `M` accepts `s` within
`steps` steps iff the Cook tableau is satisfiable. -/
theorem cookTableau_correct (M : FlatTM) (s : List Nat) (steps : Nat)
    (hValid : validFlatTM M) :
    acceptsFlatTM M [s] steps = true ↔
    FlatTCC.FlatTCCLang (cookTableau M s steps) := by
  sorry  -- TODO(Part6.2)

/-- **Size bound (Part 6.3).** The tableau's encoded size is
polynomial in `|s| + steps + |M|`. -/
theorem cookTableau_size_bound (M : FlatTM) (s : List Nat) (steps : Nat) :
    encodable.size (cookTableau M s steps) ≤
      (s.length + steps + M.sig + M.states + 1) ^ 3 := by
  sorry  -- TODO(Part6.3)

/-- Polynomial size bound function. -/
def cookTableau_sizeBound (n : Nat) : Nat := (n + 1) ^ 3

theorem cookTableau_sizeBound_poly : inOPoly cookTableau_sizeBound := by
  sorry  -- TODO(Part6.3)

theorem cookTableau_sizeBound_mono : monotonic cookTableau_sizeBound := by
  sorry  -- TODO(Part6.3)

end Complexity.Simulators
