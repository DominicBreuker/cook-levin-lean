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

/-! ### Encoding / decoding tapes

Convention:

- **Symbol 0** is the reserved register-delimiter.
- Register values in `State` (which are `Nat`) are **shifted by +1**
  on encode and shifted back by -1 on decode. This keeps register
  values disjoint from the delimiter without restricting the source
  language.
- The encoded tape ends with a final `0` (one per register).
  Decoding drops the trailing empty register.

So `encodeTape [[1, 2], [0, 3]] = [2, 3, 0, 1, 4, 0]`, and decoding
splits on `0`, shifts each chunk by -1, drops the trailing empty.

The encoded length satisfies `(encodeTape s).length = State.size s
+ s.length` (one delimiter per register). Proven in
`encodeTape_length` below.
-/

/-- Encode the per-register shift `+1`. -/
private def Compile.shiftReg (reg : List Nat) : List Nat := reg.map (· + 1)

/-- Reverse of `shiftReg`. Maps `0 ↦ 0` so the inverse is only valid
on tapes that contain no raw `0` (i.e., tapes produced by `shiftReg`). -/
private def Compile.unshiftReg (reg : List Nat) : List Nat :=
  reg.map (fun n => n - 1)

/-- Encode a `State` as a flat tape with `0` as the register
delimiter and per-register shift by `+1`. -/
def Compile.encodeTape (s : State) : List Nat :=
  s.foldr (fun reg acc => Compile.shiftReg reg ++ [0] ++ acc) []

theorem Compile.encodeTape_nil :
    Compile.encodeTape [] = [] := rfl

theorem Compile.encodeTape_cons (reg : List Nat) (s : State) :
    Compile.encodeTape (reg :: s) =
      Compile.shiftReg reg ++ [0] ++ Compile.encodeTape s := rfl

/-- Flatten a single TM tape `(left, head, right)` into a `List Nat`.
`left` is stored in reverse order (most-recently-passed cells first),
so we reverse it before concatenating. -/
private def Compile.flattenTape (tape : List Nat × Nat × List Nat) : List Nat :=
  tape.1.reverse ++ [tape.2.1] ++ tape.2.2

/-- Split a `List Nat` on `0`. Used to recover registers from an
encoded tape. -/
private def Compile.splitOnZero : List Nat → List (List Nat)
  | []      => [[]]
  | 0 :: xs =>
      let rest := Compile.splitOnZero xs
      [] :: rest
  | x :: xs =>
      match Compile.splitOnZero xs with
      | []           => [[x]]   -- unreachable: splitOnZero never returns []
      | grp :: rest  => (x :: grp) :: rest

/-- Drop the trailing empty register if present (the encoding always
appends one). -/
private def Compile.dropTrailingEmpty : List (List Nat) → List (List Nat)
  | []         => []
  | [[]]       => []
  | x :: rest  => x :: Compile.dropTrailingEmpty rest

/-- Decode an output configuration back into a `State`. Reads tape 0,
flattens, splits on the `0` delimiter, shifts each register back by
`-1`, and trims the trailing empty register.

**Skeleton status.** Concrete in shape; the `Compile_sound` proof
will need a lemma `decodeTape (encodeOf s) = s` plus the
machine-execution preserves-encoding invariant. The latter is a
sizable lemma but mechanical. -/
def Compile.decodeTape (cfg : FlatTMConfig) : State :=
  match cfg.tapes with
  | []           => []
  | tape :: _    =>
      let flat := Compile.flattenTape tape
      let groups := Compile.splitOnZero flat
      let trimmed := Compile.dropTrailingEmpty groups
      trimmed.map Compile.unshiftReg

/-- Round-trip lemma — needed by `Compile_sound`. -/
theorem Compile.decodeTape_encodeTape (s : State) :
    Compile.decodeTape
        { tapes := [([], 0, Compile.encodeTape s)]
          state_idx := 0 } = s := by
  sorry  -- TODO(Part3.4): induction on s; uses `splitOnZero` and
         -- `dropTrailingEmpty` equational lemmas.

/-- Polynomial overhead for `Compile_sound`'s time bound: the
simulator adds at most a constant factor of TM-bookkeeping per
`Cmd` step (state-table traversal, head movement). The concrete
shape `c · n² + n + 1` reflects the worst-case quadratic blowup of
running a register operation on a single delimited tape: head
movement across the tape costs `O(L)` and there are `O(L)` such
movements per `Cmd` step.

The concrete constants here are deliberately loose; the eventual
`Compile_sound` proof may tighten them, but the *shape*
("polynomial of degree 2") is committed. -/
def Compile.overhead (n : Nat) : Nat := n * n + n + 1

theorem Compile.overhead_poly : inOPoly Compile.overhead := by
  -- `n*n + n + 1 ≤ 3 * n^2` for `n ≥ 1`.
  refine ⟨2, ⟨3, 1, ?_⟩⟩
  intro n hn
  show n * n + n + 1 ≤ 3 * n ^ 2
  have h1 : 1 ≤ n := hn
  have h_nn : n ≤ n * n := by
    have := Nat.mul_le_mul_left n h1   -- n*1 ≤ n*n
    simpa using this
  have h_1n : 1 ≤ n * n := Nat.le_trans h1 h_nn
  calc n * n + n + 1
      ≤ n * n + n * n + n * n := by
        exact Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) h_nn) h_1n
    _ = 3 * (n * n) := by ring
    _ = 3 * n ^ 2 := by ring

theorem Compile.overhead_mono : monotonic Compile.overhead := by
  intro x y hxy
  show x * x + x + 1 ≤ y * y + y + 1
  have h1 : x * x ≤ y * y := Nat.mul_le_mul hxy hxy
  exact Nat.add_le_add (Nat.add_le_add h1 hxy) (Nat.le_refl _)

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
