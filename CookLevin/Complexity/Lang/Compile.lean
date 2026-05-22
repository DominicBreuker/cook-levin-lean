import Complexity.Lang.Semantics
import Complexity.Complexity.TMPrimitives

set_option autoImplicit false

/-! # The Cmd → FlatTM compiler (skeleton, Part 3.3 / 3.4 of ROADMAP)

`Compile` emits a `FlatTM` for each `Cmd`. The compiler is the
one-time engineering investment that justifies the layer's
existence: every downstream verifier and reduction is written as a
`Cmd`, and the compiler produces a real polynomial-time Turing
machine.

**Skeleton status.** `Compile`, `Compile_valid`, and the main
soundness theorem `Compile_sound` are stubbed: `Compile` maps every
`Cmd` to `validFlatTM_default`, `Compile_valid` follows trivially,
and `Compile_sound` is `sorry`. The signatures pin down what the
real compiler must produce.

The intended compilation is constructor-by-constructor:

| `Cmd` constructor | Compiles to                                            |
|-------------------|--------------------------------------------------------|
| `op o`            | a small per-op TM (~10 LOC each, ~7 ops)               |
| `seq c1 c2`       | `composeFlatTM (Compile c1) (Compile c2)`              |
| `ifBit t cT cE`   | `branchComposeFlatTM (testBitTM t) (Compile cT) (Compile cE)` |
| `forBnd c b body` | `loopTM (Compile body)` with a counter / bound thread  |

`loopTM` is itself part of the skeleton's TM combinator family. It
was planned in `parked/PART2.md` §11.5c and is the last combinator
the compiler depends on; it is left as a `sorry`-bodied combinator
in `TMPrimitives.lean` if the layer needs it before Part 3.3 lands. -/

namespace Complexity.Lang

/-- Compile a `Cmd` to a `FlatTM`. The state encoding maps register
`v` to a contiguous slot on the tape; the layout is fixed by the
compiler and exposed via `Compile.encode` below.

**Skeleton stub:** every `Cmd` is compiled to `validFlatTM_default`,
a 1-state halting machine. Replace in Part 3.3. -/
def Compile : Cmd → FlatTM := fun _ => validFlatTM_default

theorem Compile_valid (c : Cmd) : validFlatTM (Compile c) := by
  -- With the stub, every `Compile c` is `validFlatTM_default`, which
  -- is valid by definition. Replace in Part 3.3 with the real validity
  -- proof (constructor-by-constructor).
  show validFlatTM validFlatTM_default
  refine ⟨?_, ?_, ?_⟩
  · decide  -- 0 < 1
  · decide  -- [true].length = 1
  · intro entry hEntry
    -- trans = [], so the membership is vacuously impossible.
    cases hEntry

/-- Tape encoding of a `State`: stack the registers separated by a
delimiter symbol.

**Skeleton stub.** The real encoding fixes the delimiter (likely the
new alphabet's highest symbol) and proves a length bound
`(encodeTape s).length ≤ State.size s · k + (s.length + 1)` for a
fixed `k`. -/
def Compile.encodeTape (s : State) : List Nat :=
  s.foldr (fun reg acc => reg ++ [0] ++ acc) []
  -- TODO(Part3.3): commit to a delimiter that is reserved by Compile.

/-- Decode an output configuration back into a `State`. Used by
`Compile_sound`. The real implementation reads the (one) tape and
splits on the register delimiter. -/
axiom Compile.decodeTape : FlatTMConfig → State

/-- A polynomial overhead constant for `Compile_sound`'s time bound.
The simulator adds at most a constant factor of TM-bookkeeping per
`Cmd` step (state-table traversal, head movement). -/
axiom Compile.overhead : Nat → Nat
axiom Compile.overhead_poly : inOPoly Compile.overhead
axiom Compile.overhead_mono : monotonic Compile.overhead

/-- **Main soundness theorem (Part 3.4).** Running `Compile c` on the
encoded state simulates `c.eval`, with TM step count bounded by
`overhead · cost c`.

Stated for now with an explicit `cfg` existential and the
"`decodeTape` matches `eval`" conclusion; the final shape may be
slightly different (e.g., we may carry an `acceptState`/`rejectState`
pair from the TM-side directly). -/
theorem Compile_sound (c : Cmd) (s : State) :
    ∃ cfg,
      runFlatTM (Compile.overhead (State.size s) * (c.cost s + 1)) (Compile c)
          (initFlatConfig (Compile c) [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (Compile c) cfg = true ∧
      Compile.decodeTape cfg = c.eval s := by
  sorry  -- TODO(Part3.4)

/-- Corollary: a `Cmd` with polynomial cost compiles to a TM with
polynomial step bound. -/
theorem Compile_polyBound (c : Cmd)
    (costBound : Nat → Nat) (h_poly : inOPoly costBound)
    (h_mono : monotonic costBound)
    (h_bound : ∀ s, c.cost s ≤ costBound (State.size s)) :
    ∃ tmBound : Nat → Nat, inOPoly tmBound ∧ monotonic tmBound ∧
      ∀ s, ∃ cfg,
        runFlatTM (tmBound (State.size s)) (Compile c)
            (initFlatConfig (Compile c) [Compile.encodeTape s]) = some cfg ∧
        haltingStateReached (Compile c) cfg = true ∧
        Compile.decodeTape cfg = c.eval s := by
  sorry  -- TODO(Part3.4): follow from Compile_sound + inOPoly_comp.

end Complexity.Lang
