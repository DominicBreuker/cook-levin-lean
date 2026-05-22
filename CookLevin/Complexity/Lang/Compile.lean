import Complexity.Lang.Semantics
import Complexity.Complexity.TMPrimitives

set_option autoImplicit false

/-! # The Cmd → FlatTM compiler (skeleton, Part 3.3 / 3.4 of ROADMAP)

`Compile` emits a `FlatTM` for each `Cmd`. The compiler is the
one-time engineering investment that justifies the layer's
existence: every downstream verifier and reduction is written as a
`Cmd`, and the compiler produces a real polynomial-time Turing
machine.

## Skeleton status

The body of `Compile` is now a structural recursion over `Cmd`,
delegating to four per-constructor helpers (`compileOp`,
`compileSeq`, `compileIfBit`, `compileForBnd`). The helpers
themselves are stubs returning `compiledCmd_default` (a 1-state
halting machine paired with exit state `0`). Per-constructor
soundness lemmas (`compileOp_sound`, …) are sorry-bodied, so that
the proof obligations for each constructor are localized and can
be discharged independently in Part 3.3.

This decomposition replaced the single
`Compile := fun _ => validFlatTM_default` stub. The decomposition
surfaced the following structural commitments / gaps, which are
now recorded in the `ROADMAP.md` risk register:

1. **`CompiledCmd` carries an exit state**, because `composeFlatTM`
   and `branchComposeFlatTM` require an explicit "designated exit
   state of `M₁`". A bare `FlatTM` is not enough for compositional
   compilation; the natural shape is `(M, exit, exit_lt)`.
2. **Alphabet is fixed at `sig = 3`**: symbol `0` is the
   register-delimiter, symbols `1`, `2` are the shifted register
   values for `0`, `1` respectively. This commits the layer's
   inputs to bit-strings (the standard NP-completeness convention).
   `Op.eval` on bit-shaped states stays bit-shaped — there is no
   primitive that introduces other natural-number values. A future
   refinement may want a `BitState` invariant to make this explicit.
3. **`Compile.overhead`'s shape changed** from `Nat → Nat` applied
   to `State.size s` to `Nat → Nat` applied to `State.size s + cost`.
   The motivation: each TM-simulation of a `Cmd`-step costs `O(L)`
   where `L` is the current tape length, and `L` can grow by `+1`
   per `Cmd`-step. So the natural bound on a single Cmd-step is
   `poly(sizeIn + cost)`, not `poly(sizeIn)`. The `Compile_polyBound`
   corollary still produces a `Nat → Nat` poly bound in input size,
   via `inOPoly_comp`.
4. **`branchComposeFlatTM` requires distinct exit states** in M₁
   for the positive and negative branches (`exit_pos ≠ exit_neg`).
   The `compileIfBit` helper therefore needs a two-exit tester
   machine, not a single-exit one. The skeleton currently uses a
   placeholder `branchTester_default`.
5. **`loopTM` is still not in `TMPrimitives.lean`.** `compileForBnd`
   uses a stub. The shape of the eventual `loopTM` combinator —
   probably "run body, decrement counter, repeat until counter is
   empty" — is committed by `compileForBnd`'s contract but not
   implemented.

The intended compilation, once the helpers are real:

| `Cmd` constructor | Compiles to                                            |
|-------------------|--------------------------------------------------------|
| `op o`            | a small per-op TM (~10 LOC each, ~8 ops)               |
| `seq c1 c2`       | `composeFlatTM r1.M r2.M r1.exit`                      |
| `ifBit t cT cE`   | `branchComposeFlatTM tester.M rT.M rE.M e_pos e_neg`   |
| `forBnd c b body` | `loopTM rb.M` with a counter / bound thread           |

-/

namespace Complexity.Lang

/-! ## The `CompiledCmd` record

The output of compiling a single `Cmd` is a `FlatTM` together with
its designated "exit state" — the state reached just before the
machine halts, used as the bridge target by `composeFlatTM` and
`branchComposeFlatTM`. Bundling them keeps the structural
recursion in `compileCmd` typechecking cleanly. -/

/-- The output of `compileCmd`: a FlatTM, its designated exit
state, and validity bookkeeping. -/
structure CompiledCmd where
  /-- The compiled Turing machine. -/
  M : FlatTM
  /-- The designated "exit" state of `M`. This is the state reached
  when the machine has finished computing, before halting. Used as
  the bridge target by `composeFlatTM`. By convention the exit
  state IS a halt state of `M`; `composeFlatTM` will turn off
  M₁'s halt bits, so this halts only when used as the *final*
  compiled fragment, not when used as `M₁` in a composition. -/
  exit : Nat
  /-- The exit state is a valid state index. -/
  exit_lt : exit < M.states
  /-- The exit state is the unique halt state of `M`. (This
  invariant is convenient because it lets `composeFlatTM` use the
  same `exit` field for `exit`.) -/
  exit_is_halt : M.halt[exit]? = some true
  /-- The machine is valid (well-typed states, well-formed
  transitions). -/
  M_valid : validFlatTM M
  /-- The machine is single-tape (the layer's standing assumption). -/
  M_tapes : M.tapes = 1
  /-- The machine's alphabet is exactly 3: `0` = delimiter,
  `1` = shifted `0`, `2` = shifted `1`. -/
  M_sig : M.sig = 3

/-- The trivial 1-state halting machine, packaged as a
`CompiledCmd` with `exit = 0`. Used as the default body of all
the stub helpers. -/
def compiledCmd_default : CompiledCmd where
  M :=
    { sig := 3
      tapes := 1
      states := 1
      trans := []
      start := 0
      halt := [true] }
  exit := 0
  exit_lt := by decide
  exit_is_halt := by decide
  M_valid := by
    refine ⟨?_, ?_, ?_⟩
    · decide
    · decide
    · intro entry hEntry
      cases hEntry
  M_tapes := rfl
  M_sig := rfl

/-! ## Per-constructor compilation helpers

Each helper has the contract:

- input: the compiled sub-`Cmd`(s) (already `CompiledCmd`-typed),
- output: a `CompiledCmd` that decides the parent constructor.

Helpers are currently stubs returning `compiledCmd_default`; their
correctness is captured by the per-constructor soundness lemmas
below (each sorry-bodied).
-/

/-- Compile a single primitive operation `Op` into a `CompiledCmd`.
**Stub.** The real implementation must:
- emit a TM that navigates to the operand registers using `0`-
  delimiters,
- mutate the tape according to `Op.eval`,
- halt in a designated exit state.

The state count depends linearly on the operand indices (each
register skipped costs ~1 state). The alphabet is `sig = 3` by the
layer's convention. -/
def compileOp (_o : Op) : CompiledCmd := compiledCmd_default

/-- Compile `seq c1 c2` from already-compiled sub-machines.

The intended body is
`composeFlatTM r1.M r2.M r1.exit` paired with the exit state
`r1.M.states + r2.exit` (the exit of `r2`, shifted into the
composed state space). The validity of the result follows from
`composeFlatTM_valid` once we plumb the side-conditions through. -/
def compileSeq (_r1 _r2 : CompiledCmd) : CompiledCmd := compiledCmd_default

/-- Compile `ifBit t cT cE` from already-compiled sub-branches.

The intended body is
`branchComposeFlatTM tester.M rT.M rE.M tester.exitPos tester.exitNeg`
where `tester` is a small TM that reads register `t`'s first symbol
and dispatches to one of two exit states. The exit of the
composed machine is whichever branch ran. -/
def compileIfBit (_t : Var) (_rT _rE : CompiledCmd) : CompiledCmd :=
  compiledCmd_default

/-- Compile `forBnd counter bound body` from the already-compiled
body. The intended body is a `loopTM`-style combinator that:

- reads the length of register `bound` (in unary),
- iterates `body` that many times, writing the loop index into
  register `counter` between iterations.

`loopTM` is not yet defined in `TMPrimitives.lean`; landing it is
part of the same Part 3.3 work that fills in the stubs here. -/
def compileForBnd (_counter _bound : Var) (_rbody : CompiledCmd) :
    CompiledCmd := compiledCmd_default

/-! ## The compiler -/

/-- Compile a `Cmd` to its `CompiledCmd` package. Structural
recursion over `Cmd`. Each constructor delegates to a per-
constructor helper. -/
def compileCmd : Cmd → CompiledCmd
  | .op o                 => compileOp o
  | .seq c1 c2            => compileSeq (compileCmd c1) (compileCmd c2)
  | .ifBit t cT cE        => compileIfBit t (compileCmd cT) (compileCmd cE)
  | .forBnd cnt bnd body  => compileForBnd cnt bnd (compileCmd body)

/-- Consumer-facing API: the bare TM produced by compilation. -/
def Compile (c : Cmd) : FlatTM := (compileCmd c).M

/-- Consumer-facing API: the exit state of `Compile c`. -/
def Compile.exit (c : Cmd) : Nat := (compileCmd c).exit

/-- The compiled machine is valid. With the stubbed helpers this is
immediate (every case is `compiledCmd_default`); with the real
helpers it follows from the per-constructor validity of each
helper and the existing combinator-validity lemmas
(`composeFlatTM_valid`, `branchComposeFlatTM_valid`). -/
theorem Compile_valid (c : Cmd) : validFlatTM (Compile c) :=
  (compileCmd c).M_valid

theorem Compile_tapes (c : Cmd) : (Compile c).tapes = 1 :=
  (compileCmd c).M_tapes

theorem Compile_sig (c : Cmd) : (Compile c).sig = 3 :=
  (compileCmd c).M_sig

/-! ### Encoding / decoding tapes

Convention:

- **Symbol 0** is the reserved register-delimiter.
- Register values are restricted to `{0, 1}` (bit strings) and are
  **shifted by +1** on encode: `0 ↦ 1`, `1 ↦ 2`. Decoding shifts
  back by `-1`. This keeps register values disjoint from the
  delimiter without restricting the source language (which is bit-
  shaped by convention; cf. `BitState` future work).
- The encoded tape ends with a final `0` (one per register).
  Decoding drops the trailing empty register.

So `encodeTape [[1, 0], [0, 1]] = [2, 1, 0, 1, 2, 0]`, and decoding
splits on `0`, shifts each chunk by -1, drops the trailing empty.

The encoded length satisfies
`(encodeTape s).length = State.size s + s.length` (one delimiter
per register). The alphabet used by `encodeTape` is `{0, 1, 2}`,
matching `Compile_sig`.

`State.size` is the sum of register lengths. The alphabet bound is
ensured externally: callers must provide bit-shaped states. -/

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
`-1`, and trims the trailing empty register. -/
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

/-! ## Cost / overhead

**Shape change vs. pre-decomposition skeleton.** The previous
`overhead : Nat → Nat` was applied to `State.size s`, the *input*
size. That bound is too loose, because during execution the tape
may grow by `+1` per `Cmd`-step (e.g. `appendOne`, `appendZero`).
After `cost c s` Cmd-steps the tape can have up to
`State.size s + cost c s` symbols, and the per-Cmd-step TM cost is
`O(tape length)`, so the cumulative TM cost is
`O((sizeIn + cost) * cost)`.

We now define `overhead` so that
`overhead (State.size s + cost c s)` upper-bounds the *total* TM-
step count for simulating `c` on `s`. The corollary
`Compile_polyBound` re-expresses this as a polynomial in input
size only, by composing with the caller-supplied `costBound`. -/

/-- TM-step bound for simulating a `Cmd` whose execution touches at
most `m` tape cells: `(m + 1)^2`. The quadratic shape reflects the
worst-case
`O(L) per Cmd-step × cost(c) Cmd-steps = O(L · cost)` total cost
with `L ≤ m`. -/
def Compile.overhead (m : Nat) : Nat := (m + 1) * (m + 1)

theorem Compile.overhead_poly : inOPoly Compile.overhead := by
  -- `(m + 1)^2 ≤ 4 * m^2` for `m ≥ 1`.
  refine ⟨2, ⟨4, 1, ?_⟩⟩
  intro n hn
  show (n + 1) * (n + 1) ≤ 4 * n ^ 2
  have h1 : 1 ≤ n := hn
  have h_nn : n ≤ n * n := by
    have := Nat.mul_le_mul_left n h1   -- n*1 ≤ n*n
    simpa using this
  have h_1n : 1 ≤ n * n := Nat.le_trans h1 h_nn
  -- (n + 1)^2 = n^2 + 2n + 1 ≤ n^2 + 2*n^2 + n^2 = 4 n^2
  calc (n + 1) * (n + 1)
      = n * n + n + n + 1 := by ring
    _ ≤ n * n + n * n + n * n + n * n := by
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) h_nn) h_nn) h_1n
    _ = 4 * (n * n) := by ring
    _ = 4 * n ^ 2 := by ring

theorem Compile.overhead_mono : monotonic Compile.overhead := by
  intro x y hxy
  show (x + 1) * (x + 1) ≤ (y + 1) * (y + 1)
  have h : x + 1 ≤ y + 1 := Nat.add_le_add_right hxy 1
  exact Nat.mul_le_mul h h

/-! ## Per-constructor soundness lemmas (decomposed sorrys)

The single `Compile_sound` sorry from the pre-decomposition
skeleton is now four focused sorrys, one per `Cmd` constructor.
Each lemma states what its constructor's compilation must achieve
in isolation. Filling these in (Part 3.3) closes the main
`Compile_sound` mechanically (induction). -/

/-- Soundness obligation for `compileOp`. -/
theorem compileOp_sound (o : Op) (s : State) :
    ∃ cfg,
      runFlatTM (Compile.overhead (State.size s + 1))
          (compileOp o).M
          (initFlatConfig (compileOp o).M [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (compileOp o).M cfg = true ∧
      Compile.decodeTape cfg = Op.eval o s := by
  sorry  -- TODO(Part3.3:compileOp): implement per-Op TMs.

/-- Soundness obligation for `compileSeq`, given the IHs for both
sub-machines. -/
theorem compileSeq_sound
    (r1 r2 : CompiledCmd)
    (eval1 eval2 : State → State)
    (cost1 cost2 : State → Nat)
    (h1 : ∀ s, ∃ cfg, runFlatTM (Compile.overhead (State.size s + cost1 s)) r1.M
            (initFlatConfig r1.M [Compile.encodeTape s]) = some cfg ∧
            haltingStateReached r1.M cfg = true ∧
            Compile.decodeTape cfg = eval1 s)
    (h2 : ∀ s, ∃ cfg, runFlatTM (Compile.overhead (State.size s + cost2 s)) r2.M
            (initFlatConfig r2.M [Compile.encodeTape s]) = some cfg ∧
            haltingStateReached r2.M cfg = true ∧
            Compile.decodeTape cfg = eval2 s)
    (s : State) :
    ∃ cfg,
      runFlatTM (Compile.overhead (State.size s + 1 + cost1 s + cost2 (eval1 s)))
          (compileSeq r1 r2).M
          (initFlatConfig (compileSeq r1 r2).M [Compile.encodeTape s])
          = some cfg ∧
      haltingStateReached (compileSeq r1 r2).M cfg = true ∧
      Compile.decodeTape cfg = eval2 (eval1 s) := by
  sorry  -- TODO(Part3.3:compileSeq): apply composeFlatTM_run.

/-- Soundness obligation for `compileIfBit`. The two branches are
mutually exclusive on the value of `s.get t`, so the IH for the
*taken* branch is the only one needed; we state both for symmetry. -/
theorem compileIfBit_sound
    (t : Var) (rT rE : CompiledCmd)
    (evalT evalE : State → State)
    (costT costE : State → Nat)
    (hT : ∀ s, ∃ cfg, runFlatTM (Compile.overhead (State.size s + costT s)) rT.M
            (initFlatConfig rT.M [Compile.encodeTape s]) = some cfg ∧
            haltingStateReached rT.M cfg = true ∧
            Compile.decodeTape cfg = evalT s)
    (hE : ∀ s, ∃ cfg, runFlatTM (Compile.overhead (State.size s + costE s)) rE.M
            (initFlatConfig rE.M [Compile.encodeTape s]) = some cfg ∧
            haltingStateReached rE.M cfg = true ∧
            Compile.decodeTape cfg = evalE s)
    (s : State) :
    let chosen := if s.get t = [1] then evalT s else evalE s
    let chosenCost := if s.get t = [1] then costT s else costE s
    ∃ cfg,
      runFlatTM (Compile.overhead (State.size s + 1 + chosenCost))
          (compileIfBit t rT rE).M
          (initFlatConfig (compileIfBit t rT rE).M [Compile.encodeTape s])
          = some cfg ∧
      haltingStateReached (compileIfBit t rT rE).M cfg = true ∧
      Compile.decodeTape cfg = chosen := by
  sorry  -- TODO(Part3.3:compileIfBit): apply branchComposeFlatTM_run
         -- with the test-bit tester.

/-- Soundness obligation for `compileForBnd`. The iteration count
is `(s.get bound).length`, with the loop index threaded through
`counter`. -/
theorem compileForBnd_sound
    (counter bound : Var)
    (rbody : CompiledCmd)
    (evalBody : State → State)
    (costBody : State → Nat)
    (hb : ∀ s, ∃ cfg, runFlatTM (Compile.overhead (State.size s + costBody s)) rbody.M
            (initFlatConfig rbody.M [Compile.encodeTape s]) = some cfg ∧
            haltingStateReached rbody.M cfg = true ∧
            Compile.decodeTape cfg = evalBody s)
    (s : State) :
    -- The aggregated body-state and cost from running the loop.
    let iters := (s.get bound).length
    let folded := (List.range iters).foldl
      (fun acc i =>
        let s' := acc.1.set counter (List.replicate i 1)
        (evalBody s', acc.2 + costBody s'))
      (s, 0)
    ∃ cfg,
      runFlatTM (Compile.overhead (State.size s + 1 + folded.2 + iters))
          (compileForBnd counter bound rbody).M
          (initFlatConfig (compileForBnd counter bound rbody).M
              [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (compileForBnd counter bound rbody).M cfg = true ∧
      Compile.decodeTape cfg = folded.1 := by
  sorry  -- TODO(Part3.3:compileForBnd): land `loopTM` in
         -- TMPrimitives.lean first, then apply its run lemma.

/-- **Main soundness theorem (Part 3.4).** Running `Compile c` on
the encoded state simulates `c.eval`, with TM step count bounded
by `Compile.overhead (sizeIn + cost)`.

The bound shape `Compile.overhead (State.size s + c.cost s)`
(rather than the pre-decomposition `overhead(size s) * (cost + 1)`)
honestly accounts for tape growth during execution; see the
docstring on `Compile.overhead`. -/
theorem Compile_sound (c : Cmd) (s : State) :
    ∃ cfg,
      runFlatTM (Compile.overhead (State.size s + c.cost s))
          (Compile c)
          (initFlatConfig (Compile c) [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (Compile c) cfg = true ∧
      Compile.decodeTape cfg = c.eval s := by
  -- Induction on c, using the per-constructor lemmas above.
  sorry  -- TODO(Part3.4): assemble from compileOp_sound, compileSeq_sound,
         -- compileIfBit_sound, compileForBnd_sound. Each step matches the
         -- corresponding constructor's case in `Cmd.run`.

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
         -- tmBound n := Compile.overhead (n + costBound n).

end Complexity.Lang
