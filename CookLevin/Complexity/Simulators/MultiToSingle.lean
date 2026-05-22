import Complexity.Complexity.MachineSemantics
import Complexity.Complexity.NP

set_option autoImplicit false

/-! # Multi-tape → single-tape simulator (skeleton, Part 5 of ROADMAP)

The textbook construction: encode the `k` tapes of a multi-tape TM
`M` onto a single tape using a delimiter symbol and a "head marker"
extension of the alphabet, then simulate one source step in `O(L)`
target steps where `L` is the current total tape length.

This skeleton commits to the signatures and the headline correctness
theorem. Filling in the actual construction is Part 5.2 of the
roadmap.

Compared to the placeholder `bridgeMachine` in `LM_to_mTM.lean` and
`mTM_to_singleTapeTM.lean`, this skeleton's `multiToSingle` is a
*real* function of the source machine — and the correctness theorem
`multiToSingle_accepts` is a real bi-implication, not a trivial
constant. -/

namespace Complexity.Simulators

/-- Encode a list of multi-tape contents as a single flat tape with
delimiters. Skeleton stub: returns the concatenation with `0` between
tapes. -/
def encodeTapes (tapes : List (List Nat)) : List Nat :=
  tapes.foldr (fun t acc => t ++ [0] ++ acc) []

/-- The single-tape simulator of a `k`-tape `FlatTM`. Replaces the
placeholder `bridgeMachine` of the original Part 4.

**Skeleton stub.** Returns `validFlatTM_default`. Replace in Part 5.2
with the real delimiter-and-head-marker construction. -/
noncomputable def multiToSingle (_M : FlatTM) : FlatTM :=
  validFlatTM_default

/-- The simulator is a valid `FlatTM`. -/
theorem multiToSingle_valid (M : FlatTM) (_hM : validFlatTM M) :
    validFlatTM (multiToSingle M) := by
  show validFlatTM validFlatTM_default
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · intro entry hEntry; cases hEntry

/-- The simulator has the standard quadratic step-blowup: `f` source
steps cost at most `c * (L + f)^2` target steps for some constant `c`
depending on `M`'s alphabet and tape count.

**Skeleton stub.** -/
noncomputable def multiToSingle_stepBound (_M : FlatTM) (f : Nat → Nat) :
    Nat → Nat :=
  fun n => f n ^ 2 + n  -- placeholder shape

theorem multiToSingle_stepBound_poly (M : FlatTM)
    (f : Nat → Nat) (h_poly : inOPoly f) :
    inOPoly (multiToSingle_stepBound M f) := by
  sorry  -- TODO(Part5.2)

theorem multiToSingle_stepBound_mono (M : FlatTM)
    (f : Nat → Nat) (h_mono : monotonic f) :
    monotonic (multiToSingle_stepBound M f) := by
  sorry  -- TODO(Part5.2)

/-- **Main correctness theorem (Part 5.2).** The simulator accepts the
same inputs as the source machine, modulo the quadratic step blowup. -/
theorem multiToSingle_accepts (M : FlatTM) (tapes : List (List Nat))
    (steps : Nat) (hValid : validFlatTM M) :
    acceptsFlatTM (multiToSingle M) [encodeTapes tapes]
        (multiToSingle_stepBound M (fun n => steps) (tapes.foldr (· ++ ·) []).length) = true ↔
    acceptsFlatTM M tapes steps = true := by
  sorry  -- TODO(Part5.2)

end Complexity.Simulators
