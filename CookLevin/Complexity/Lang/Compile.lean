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

open TMPrimitives

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
  /-- The exit state IS a halt state of `M`. (This invariant is
  convenient because it lets `composeFlatTM` use the same `exit`
  field for `exit`.) -/
  exit_is_halt : M.halt[exit]? = some true
  /-- The exit state is the **unique** halt state of `M`. Required
  for compositional soundness: `composeFlatTM_run`'s `h_traj1`
  precondition needs M₁ to avoid halting before reaching `exit`,
  which is guaranteed exactly when `exit` is the only halt state.
  Combined with `exit_is_halt`, the halt vector is morally
  `replicate exit false ++ [true] ++ replicate _ false`. -/
  halt_unique : ∀ i, M.halt[i]? = some true → i = exit
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
  halt_unique := by
    intro i hi
    -- M.halt = [true]; hi : [true][i]? = some true
    rcases i with _ | n
    · rfl
    · simp at hi
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

/-! ### Per-`Op` helpers (one stub per `Op` constructor)

Each `Op` constructor compiles to a small TM whose state count
depends linearly on the operand register indices (one extra state
per register-delimiter skipped). All per-`Op` helpers are stubs
returning `compiledCmd_default`; they are listed separately so
that future iterations can concretize them one at a time without
re-touching the rest of the compiler.

Per-`Op` TM contracts (informal):

- `opClear dst` — find the `dst`-th register's start, then shift
  the tail of the tape left to remove the register's contents,
  leaving the trailing delimiter in place. State count: `O(dst)`.
- `opAppendOne dst` — navigate to the end of register `dst`
  (the delimiter just after it), then *insert* symbol `2` (shifted
  `1`) by shifting everything right by one cell and writing.
- `opAppendZero dst` — analogous, but inserts symbol `1`
  (shifted `0`).
- `opCopy dst src` — read register `src`'s contents (between
  delimiters), then overwrite register `dst` with them; this
  involves shifting if the lengths differ. State count: `O(dst + src)`.
- `opTail dst src` — read `src`, drop its first symbol (if any),
  then write to `dst`.
- `opHead dst src` — read `src`'s first symbol, then write to
  `dst` (single-symbol register).
- `opEqBit dst src1 src2` — read `src1` and `src2` cell-by-cell,
  comparing; write `[1]` or `[0]` (shifted) to `dst`.
- `opNonEmpty dst src` — examine the first symbol after the
  `src`-th delimiter: if it is `0`, the register is empty.

All eight stubs share the same shape: they take operand register
indices and return a `CompiledCmd`. Soundness obligations are
collected by `compileOp_sound` (currently one sorry; can be
decomposed per-`Op` when those helpers are concretized). -/

/-- Compile `Op.clear dst`. **Stub.** -/
def Compile.opClear (_dst : Var) : CompiledCmd := compiledCmd_default

/-- Compile `Op.appendOne dst`. **Stub.** -/
def Compile.opAppendOne (_dst : Var) : CompiledCmd := compiledCmd_default

/-- Compile `Op.appendZero dst`. **Stub.** -/
def Compile.opAppendZero (_dst : Var) : CompiledCmd := compiledCmd_default

/-- Compile `Op.copy dst src`. **Stub.** -/
def Compile.opCopy (_dst _src : Var) : CompiledCmd := compiledCmd_default

/-- Compile `Op.tail dst src`. **Stub.** -/
def Compile.opTail (_dst _src : Var) : CompiledCmd := compiledCmd_default

/-- Compile `Op.head dst src`. **Stub.** -/
def Compile.opHead (_dst _src : Var) : CompiledCmd := compiledCmd_default

/-- Compile `Op.eqBit dst src1 src2`. **Stub.** -/
def Compile.opEqBit (_dst _src1 _src2 : Var) : CompiledCmd := compiledCmd_default

/-- Compile `Op.nonEmpty dst src`. **Stub.** -/
def Compile.opNonEmpty (_dst _src : Var) : CompiledCmd := compiledCmd_default

/-- Compile a single primitive operation `Op` to a `CompiledCmd`
by dispatching on the constructor. The actual TM construction
lives in the per-`Op` helpers above. -/
def compileOp : Op → CompiledCmd
  | .clear dst                 => Compile.opClear dst
  | .appendOne dst             => Compile.opAppendOne dst
  | .appendZero dst            => Compile.opAppendZero dst
  | .copy dst src              => Compile.opCopy dst src
  | .tail dst src              => Compile.opTail dst src
  | .head dst src              => Compile.opHead dst src
  | .eqBit dst src1 src2       => Compile.opEqBit dst src1 src2
  | .nonEmpty dst src          => Compile.opNonEmpty dst src

/-- Compile `seq c1 c2` from already-compiled sub-machines.

Concrete implementation via `composeFlatTM`:
- The composed TM is `composeFlatTM r1.M r2.M r1.exit` (M₁'s exit
  state triggers the bridge into M₂).
- The composed exit state is `r1.M.states + r2.exit` (r2's exit,
  shifted into the composed state space).
- All `CompiledCmd` invariants discharge via the existing
  `composeFlatTM_*` lemmas, given that both sub-machines satisfy
  the invariants.

**Gap surfaced.** `composeFlatTM_run`'s `h_traj1` precondition
requires M₁ not to reach a halt state before `exit`. The current
`CompiledCmd` invariants guarantee `exit` IS a halt state of M₁
(via `exit_is_halt`) but do NOT guarantee it is the *unique* halt
state. With a non-unique halt vector, a sub-machine could halt at
some other state, violating `h_traj1`. The eventual
`compileSeq_sound` proof will therefore need either:
- a strengthened `CompiledCmd.halt_unique : ∀ i, M.halt[i]? =
  some true → i = exit` invariant (forces every helper to produce
  a single-halt-state machine), or
- a separate operational invariant proved per-helper.

For now we keep the structural invariants minimal; the gap is
recorded in the ROADMAP risk register as part of risk #1a. -/
def compileSeq (r1 r2 : CompiledCmd) : CompiledCmd where
  M := composeFlatTM r1.M r2.M r1.exit
  exit := r1.M.states + r2.exit
  exit_lt := by
    show r1.M.states + r2.exit < (composeFlatTM r1.M r2.M r1.exit).states
    rw [composeFlatTM_states]
    exact Nat.add_lt_add_left r2.exit_lt r1.M.states
  exit_is_halt := by
    -- composeFlatTM's halt vector is `composedHalt r1.M r2.M`
    -- = `replicate r1.M.states false ++ r2.M.halt`. Index
    -- `r1.M.states + r2.exit` falls into the r2.M.halt segment.
    show (composeFlatTM r1.M r2.M r1.exit).halt[r1.M.states + r2.exit]?
        = some true
    show (composedHalt r1.M r2.M)[r1.M.states + r2.exit]? = some true
    unfold composedHalt
    have h_len : (List.replicate r1.M.states false).length ≤
        r1.M.states + r2.exit := by
      rw [List.length_replicate]; exact Nat.le_add_right _ _
    rw [List.getElem?_append_right h_len]
    -- Goal: r2.M.halt[r1.M.states + r2.exit - (replicate _ _).length]? = some true
    have h_idx : r1.M.states + r2.exit - (List.replicate r1.M.states false).length
        = r2.exit := by
      rw [List.length_replicate]; omega
    rw [h_idx]
    exact r2.exit_is_halt
  halt_unique := by
    -- composedHalt = replicate r1.M.states false ++ r2.M.halt.
    -- For i < r1.M.states, the value is `some false`; for
    -- i ≥ r1.M.states, the value is `r2.M.halt[i - r1.M.states]?`
    -- and equality with `some true` forces (by r2.halt_unique)
    -- i - r1.M.states = r2.exit, hence i = r1.M.states + r2.exit.
    intro i hi
    change (composedHalt r1.M r2.M)[i]? = some true at hi
    unfold composedHalt at hi
    -- hi : (List.replicate r1.M.states false ++ r2.M.halt)[i]? = some true
    by_cases hlt : i < r1.M.states
    · -- left segment: value is `some false`, contradiction
      exfalso
      have h_lt' : i < (List.replicate r1.M.states false).length := by
        rw [List.length_replicate]; exact hlt
      rw [List.getElem?_append_left h_lt'] at hi
      -- hi : (List.replicate r1.M.states false)[i]? = some true
      rw [List.getElem?_replicate] at hi
      -- hi : (if i < r1.M.states then some false else none) = some true
      simp [hlt] at hi
    · -- right segment: i ≥ r1.M.states
      push_neg at hlt
      have h_ge : (List.replicate r1.M.states false).length ≤ i := by
        rw [List.length_replicate]; exact hlt
      rw [List.getElem?_append_right h_ge, List.length_replicate] at hi
      -- hi : r2.M.halt[i - r1.M.states]? = some true
      have h_idx : i - r1.M.states = r2.exit := r2.halt_unique _ hi
      show i = r1.M.states + r2.exit
      omega
  M_valid :=
    composeFlatTM_valid r1.M r2.M r1.exit r1.M_valid r2.M_valid
      r1.exit_lt r1.M_tapes r2.M_tapes
  M_tapes := by
    show (composeFlatTM r1.M r2.M r1.exit).tapes = 1
    rw [composeFlatTM_tapes]; exact r1.M_tapes
  M_sig := by
    show (composeFlatTM r1.M r2.M r1.exit).sig = 3
    rw [composeFlatTM_sig, r1.M_sig, r2.M_sig]
    rfl

/-! ### `compileIfBit`: two-exit tester + branch composition + join

The construction is `branchComposeFlatTM tester rT rE exit_pos
exit_neg` composed with `Compile.joinTwoHalts` to merge the two
branches' halt states into a single surviving halt. `tester` is a
small TM that reads register `t`'s first symbol and reaches one
of two designated states (`exitPos`, `exitNeg`) before the bridge
fires into the appropriate branch.

**Risk #1d resolution (May 2026).** The previous iteration
documented a structural gap: `branchComposeFlatTM`'s halt vector
is `replicate _ false ++ M₂.halt ++ M₃.halt`, so with two
`CompiledCmd` branches (each with a unique halt) the composed TM
has TWO halt states, violating `CompiledCmd.halt_unique`. The
resolution implemented here is the recommended option (a): a
local `Compile.joinTwoHalts M h1 h2` combinator that demotes `h2`
from halt to non-halt and adds bridge entries from `h2` to `h1`.
The combinator's correctness is proved in the `Compile`
namespace; all seven `CompiledCmd` invariants discharge for
`compileIfBit` without any sorrys.

The choice of `h1` (surviving halt) vs `h2` (absorbed halt) is
symmetric; this implementation picks `haltE = tester.states +
rT.states + rE.exit` as the surviving exit. -/

/-! ### Local TM combinator: merge two halt states (risk #1d resolution)

`branchComposeFlatTM`'s halt vector has up to two `true` entries
(one per branch's exit), incompatible with `CompiledCmd.halt_unique`.
The `Compile.joinTwoHalts M h1 h2` combinator turns `h2` into a
non-halt state and bridges it to `h1`, leaving exactly one halt
state (`h1`). The construction is intentionally minimal — no fresh
state is added; the bridge entries from `h2` are placed first in
`trans` so they take precedence over any (typically non-existent)
outgoing M.trans entry from `h2`. -/

namespace Compile

/-- Merge designated halt state `h2` into `h1` by replacing `h2`'s
halt bit with `false` and bridging it to `h1`. -/
def joinTwoHalts (M : FlatTM) (h1 h2 : Nat) : FlatTM where
  sig := M.sig
  tapes := M.tapes
  states := M.states
  trans := bridgeEntries M.sig h2 h1 ++ M.trans
  start := M.start
  halt := M.halt.set h2 false

theorem joinTwoHalts_states (M : FlatTM) (h1 h2 : Nat) :
    (joinTwoHalts M h1 h2).states = M.states := rfl

theorem joinTwoHalts_start (M : FlatTM) (h1 h2 : Nat) :
    (joinTwoHalts M h1 h2).start = M.start := rfl

theorem joinTwoHalts_sig (M : FlatTM) (h1 h2 : Nat) :
    (joinTwoHalts M h1 h2).sig = M.sig := rfl

theorem joinTwoHalts_tapes (M : FlatTM) (h1 h2 : Nat) :
    (joinTwoHalts M h1 h2).tapes = M.tapes := rfl

/-- `h1` remains a halt state in the joined TM. -/
theorem joinTwoHalts_h1_is_halt (M : FlatTM) (h1 h2 : Nat)
    (h_distinct : h1 ≠ h2) (h_h1_halt : M.halt[h1]? = some true) :
    (joinTwoHalts M h1 h2).halt[h1]? = some true := by
  show (M.halt.set h2 false)[h1]? = some true
  rw [List.getElem?_set_ne (fun h => h_distinct h.symm)]
  exact h_h1_halt

/-- The joined TM has a unique halt state at `h1`, provided that
M's only `some true` entries in its halt vector were at `h1` and
`h2`. -/
theorem joinTwoHalts_halt_unique (M : FlatTM) (h1 h2 : Nat)
    (h_only_h1_h2 : ∀ i, M.halt[i]? = some true → i = h1 ∨ i = h2) :
    ∀ i, (joinTwoHalts M h1 h2).halt[i]? = some true → i = h1 := by
  intro i hi
  change (M.halt.set h2 false)[i]? = some true at hi
  rw [List.getElem?_set] at hi
  by_cases h_eq : h2 = i
  · -- i = h2: value is `some false` or `none`, both ≠ some true
    exfalso
    rw [if_pos h_eq] at hi
    split at hi
    · -- h2 < M.halt.length: value = some false
      simp at hi
    · -- h2 ≥ M.halt.length: value = none
      simp at hi
  · rw [if_neg h_eq] at hi
    -- hi : M.halt[i]? = some true
    rcases h_only_h1_h2 i hi with h | h
    · exact h
    · exfalso; exact h_eq h.symm

/-- Validity of `joinTwoHalts`. Mirrors `composeFlatTM_valid`'s
structure: case-split on transition bucket (bridge from h2 vs.
original M.trans), use `bridgeEntries_mem` for bridge entries. -/
theorem joinTwoHalts_valid (M : FlatTM) (h1 h2 : Nat)
    (h_valid : validFlatTM M)
    (h_h1 : h1 < M.states) (h_h2 : h2 < M.states)
    (h_tapes : M.tapes = 1) :
    validFlatTM (joinTwoHalts M h1 h2) := by
  obtain ⟨h_start, h_halt_len, h_trans⟩ := h_valid
  refine ⟨?_, ?_, ?_⟩
  · -- start < states
    exact h_start
  · -- halt.length = states
    show (M.halt.set h2 false).length = M.states
    rw [List.length_set]; exact h_halt_len
  · intro entry hentry
    show flatTMTransEntryValid (joinTwoHalts M h1 h2) entry
    have h_sig_eq : (joinTwoHalts M h1 h2).sig = M.sig := rfl
    have h_states_eq : (joinTwoHalts M h1 h2).states = M.states := rfl
    have h_tapes_eq : (joinTwoHalts M h1 h2).tapes = M.tapes := rfl
    rcases List.mem_append.mp hentry with h_bridge | h_orig
    · -- bridge entry from h2
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ :=
        bridgeEntries_mem h_bridge
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsrc, h_states_eq]; exact h_h2
      · rw [hdst, h_states_eq]; exact h_h1
      · rw [hsrcLen, h_tapes_eq, h_tapes]
      · rw [hdstLen, h_tapes_eq, h_tapes]
      · rw [hmovLen, h_tapes_eq, h_tapes]
      · rw [h_sig_eq]; exact hsymSrc
      · rw [h_sig_eq]; exact hsymDst
    · -- original M.trans entry — just lift the validity bound
      have hval := h_trans entry h_orig
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ := hval
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_states_eq]; exact hsrc
      · rw [h_states_eq]; exact hdst
      · rw [h_tapes_eq]; exact hsrcLen
      · rw [h_tapes_eq]; exact hdstLen
      · rw [h_tapes_eq]; exact hmovLen
      · rw [h_sig_eq]; exact hsymSrc
      · rw [h_sig_eq]; exact hsymDst

end Compile

/-- A two-exit "tester" TM bundling a `FlatTM` with two distinct
designated exit states. The contract: after running on the input
tape, the machine reaches *one* of `exitPos` / `exitNeg`
depending on whether the tested bit is true or false. -/
structure BranchTester where
  M : FlatTM
  exitPos : Nat
  exitNeg : Nat
  exitPos_lt : exitPos < M.states
  exitNeg_lt : exitNeg < M.states
  exit_distinct : exitPos ≠ exitNeg
  M_valid : validFlatTM M
  M_tapes : M.tapes = 1
  M_sig : M.sig = 3

/-- A placeholder 2-state tester. `exitPos = 0`, `exitNeg = 1`,
no transitions, neither state halts (the bridge in
`branchComposeFlatTM` is what makes progress). Replace with a
real bit-test once the per-register navigation primitives land. -/
def branchTester_default : BranchTester where
  M :=
    { sig := 3
      tapes := 1
      states := 2
      trans := []
      start := 0
      halt := [false, false] }
  exitPos := 0
  exitNeg := 1
  exitPos_lt := by decide
  exitNeg_lt := by decide
  exit_distinct := by decide
  M_valid := by
    refine ⟨?_, ?_, ?_⟩
    · decide
    · decide
    · intro entry hEntry; cases hEntry
  M_tapes := rfl
  M_sig := rfl

/-- Compile a "test bit in register `t`" gadget. **Stub.** Replace
with a real tester once register-navigation primitives land. -/
def compileTestBit (_t : Var) : BranchTester := branchTester_default

/-- Helper: the halt states of `branchComposeFlatTM`, when both
branches are `CompiledCmd`s with unique halts, are exactly the
two branch exits shifted into the composed state space. Used to
satisfy the precondition of `Compile.joinTwoHalts_halt_unique` in
`compileIfBit`. -/
theorem branchCompose_halt_only_at_exits
    (tester : BranchTester) (rT rE : CompiledCmd) (i : Nat)
    (hi : (branchComposeFlatTM tester.M rT.M rE.M
              tester.exitPos tester.exitNeg).halt[i]? = some true) :
    i = tester.M.states + rT.M.states + rE.exit ∨
    i = tester.M.states + rT.exit := by
  change (composedBranchHalt tester.M rT.M rE.M)[i]? = some true at hi
  unfold composedBranchHalt at hi
  have h_rT_len : rT.M.halt.length = rT.M.states := rT.M_valid.2.1
  -- hi : ((replicate tester.M.states false ++ rT.M.halt) ++ rE.M.halt)[i]? = some true
  by_cases h_outer : i <
      (List.replicate tester.M.states false ++ rT.M.halt).length
  · -- Falls into (replicate ++ rT.M.halt) segment
    rw [List.getElem?_append_left h_outer] at hi
    by_cases h_inner : i < tester.M.states
    · -- Falls into replicate segment: value = some false, contradiction
      exfalso
      have h_rep_len : i < (List.replicate tester.M.states false).length := by
        rw [List.length_replicate]; exact h_inner
      rw [List.getElem?_append_left h_rep_len] at hi
      rw [List.getElem?_replicate] at hi
      simp [h_inner] at hi
    · -- Falls into rT.M.halt segment
      push_neg at h_inner
      have h_rep_le : (List.replicate tester.M.states false).length ≤ i := by
        rw [List.length_replicate]; exact h_inner
      rw [List.getElem?_append_right h_rep_le, List.length_replicate] at hi
      have h_idx : i - tester.M.states = rT.exit := rT.halt_unique _ hi
      right; omega
  · -- Falls into rE.M.halt segment
    push_neg at h_outer
    rw [List.getElem?_append_right h_outer] at hi
    have h_outer_len :
        (List.replicate tester.M.states false ++ rT.M.halt).length
          = tester.M.states + rT.M.states := by
      rw [List.length_append, List.length_replicate, h_rT_len]
    rw [h_outer_len] at hi
    have h_idx : i - (tester.M.states + rT.M.states) = rE.exit :=
      rE.halt_unique _ hi
    left; omega

/-- Compile `ifBit t cT cE` using `branchComposeFlatTM` over the
two-exit tester, followed by `Compile.joinTwoHalts` to merge the
two branches' halt states into one. The composed `exit` is the
`else`-branch's exit shifted into the composed state space. See the
`compileIfBit` namespace docstring above for the `halt_unique`
gap. -/
def compileIfBit (t : Var) (rT rE : CompiledCmd) : CompiledCmd :=
  let tester := compileTestBit t
  let branched := branchComposeFlatTM tester.M rT.M rE.M
                    tester.exitPos tester.exitNeg
  let haltE := tester.M.states + rT.M.states + rE.exit
  let haltT := tester.M.states + rT.exit
  -- haltE ≠ haltT (rT.exit < rT.M.states, so haltE > haltT)
  have h_distinct : haltE ≠ haltT := by
    have h1 : rT.exit < rT.M.states := rT.exit_lt
    intro h
    -- tester.M.states + rT.M.states + rE.exit = tester.M.states + rT.exit
    -- ⟹ rT.M.states + rE.exit = rT.exit, but rT.exit < rT.M.states
    omega
  -- haltE < branched.states
  have h_haltE_lt : haltE < branched.states := by
    show haltE < (branchComposeFlatTM tester.M rT.M rE.M
                    tester.exitPos tester.exitNeg).states
    rw [branchComposeFlatTM_states]
    exact Nat.add_lt_add_left rE.exit_lt _
  -- haltT < branched.states
  have h_haltT_lt : haltT < branched.states := by
    show haltT < (branchComposeFlatTM tester.M rT.M rE.M
                    tester.exitPos tester.exitNeg).states
    rw [branchComposeFlatTM_states]
    have h_rT : rT.exit < rT.M.states := rT.exit_lt
    -- tester + rT.exit < tester + rT.M.states + rE.M.states
    omega
  -- branched is valid
  have h_branched_valid : validFlatTM branched :=
    branchComposeFlatTM_valid tester.M rT.M rE.M
      tester.exitPos tester.exitNeg
      tester.M_valid rT.M_valid rE.M_valid
      tester.exitPos_lt tester.exitNeg_lt
      tester.M_tapes rT.M_tapes rE.M_tapes
  -- branched is single-tape
  have h_branched_tapes : branched.tapes = 1 := by
    show (branchComposeFlatTM tester.M rT.M rE.M
            tester.exitPos tester.exitNeg).tapes = 1
    rw [branchComposeFlatTM_tapes]
    exact tester.M_tapes
  -- branched.halt[haltE]? = some true (rE.exit's halt bit, shifted)
  have h_branched_haltE : branched.halt[haltE]? = some true := by
    show (composedBranchHalt tester.M rT.M rE.M)[haltE]? = some true
    unfold composedBranchHalt
    have h_outer_len :
        (List.replicate tester.M.states false ++ rT.M.halt).length ≤ haltE := by
      rw [List.length_append, List.length_replicate, rT.M_valid.2.1]
      show tester.M.states + rT.M.states ≤ tester.M.states + rT.M.states + rE.exit
      exact Nat.le_add_right _ _
    rw [List.getElem?_append_right h_outer_len]
    have h_idx :
        haltE - (List.replicate tester.M.states false ++ rT.M.halt).length
          = rE.exit := by
      rw [List.length_append, List.length_replicate, rT.M_valid.2.1]
      show tester.M.states + rT.M.states + rE.exit - (tester.M.states + rT.M.states)
          = rE.exit
      omega
    rw [h_idx]
    exact rE.exit_is_halt
  { M := Compile.joinTwoHalts branched haltE haltT
    exit := haltE
    exit_lt := by
      rw [Compile.joinTwoHalts_states]
      exact h_haltE_lt
    exit_is_halt :=
      Compile.joinTwoHalts_h1_is_halt branched haltE haltT
        h_distinct h_branched_haltE
    halt_unique :=
      Compile.joinTwoHalts_halt_unique branched haltE haltT
        (fun i hi => branchCompose_halt_only_at_exits tester rT rE i hi)
    M_valid :=
      Compile.joinTwoHalts_valid branched haltE haltT
        h_branched_valid h_haltE_lt h_haltT_lt h_branched_tapes
    M_tapes := by
      rw [Compile.joinTwoHalts_tapes]
      exact h_branched_tapes
    M_sig := by
      rw [Compile.joinTwoHalts_sig]
      show branched.sig = 3
      rw [show branched =
            branchComposeFlatTM tester.M rT.M rE.M
              tester.exitPos tester.exitNeg from rfl,
          branchComposeFlatTM_sig, tester.M_sig, rT.M_sig, rE.M_sig]
      rfl }

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

In this machine model (`MachineSemantics.lean`) the head is an *index*
into `right`, and the `left` component is never written by
`writeCurrentTapeSymbol` / `moveTapeHead` — it stays `[]` for every
configuration reachable from `initFlatConfig`. The full tape contents
are therefore exactly `right` (`tape.2.2`); `left` and the head index
carry no content. (The earlier definition concatenated
`left.reverse ++ [head] ++ right`, which spliced the head *index* into
the contents as if it were a symbol — that made the round-trip lemma
below unprovable.) -/
private def Compile.flattenTape (tape : List Nat × Nat × List Nat) : List Nat :=
  tape.2.2

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

/-! ### Round-trip lemmas for `decodeTape ∘ encodeTape`

These discharge the `decodeTape_encodeTape` obligation by a short
chain of structural inductions over the encoder's pieces. -/

/-- `splitOnZero` never returns the empty list (every branch produces
at least one group). -/
private theorem Compile.splitOnZero_ne_nil :
    ∀ l : List Nat, Compile.splitOnZero l ≠ []
  | []          => by simp [Compile.splitOnZero]
  | 0 :: _      => by simp [Compile.splitOnZero]
  | (_ + 1) :: xs => by
      simp only [Compile.splitOnZero]
      cases Compile.splitOnZero xs <;> simp

/-- Shifted register contents contain no `0` (the delimiter), since
`shiftReg` maps every value to its successor. -/
private theorem Compile.shiftReg_no_zero (reg : List Nat) :
    ∀ x ∈ Compile.shiftReg reg, x ≠ 0 := by
  intro x hx
  simp only [Compile.shiftReg, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  omega

/-- Splitting `a ++ 0 :: b` on the delimiter, when `a` has no
delimiter, peels off `a` as the first group. -/
private theorem Compile.splitOnZero_append_zero :
    ∀ (a b : List Nat), (∀ x ∈ a, x ≠ 0) →
      Compile.splitOnZero (a ++ 0 :: b) = a :: Compile.splitOnZero b
  | [],          b, _ => by simp [Compile.splitOnZero]
  | (x :: a'), b, h => by
      have hx : x ≠ 0 := h x (by simp)
      have ha' : ∀ y ∈ a', y ≠ 0 := fun y hy => h y (by simp [hy])
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hx
      simp only [List.cons_append, Compile.splitOnZero,
        Compile.splitOnZero_append_zero a' b ha']

/-- The decoder's split step recovers exactly the shifted registers
plus the trailing empty group from the encoder's final delimiter. -/
private theorem Compile.splitOnZero_encodeTape :
    ∀ s : State,
      Compile.splitOnZero (Compile.encodeTape s)
        = s.map Compile.shiftReg ++ [[]]
  | []          => by simp [Compile.encodeTape, Compile.splitOnZero]
  | reg :: rest => by
      rw [Compile.encodeTape_cons]
      have happ : Compile.shiftReg reg ++ [0] ++ Compile.encodeTape rest
          = Compile.shiftReg reg ++ 0 :: Compile.encodeTape rest := by simp
      rw [happ, Compile.splitOnZero_append_zero _ _ (Compile.shiftReg_no_zero reg),
          Compile.splitOnZero_encodeTape rest, List.map_cons, List.cons_append]

/-- `dropTrailingEmpty` peels exactly one trailing empty group. -/
private theorem Compile.dropTrailingEmpty_cons_ne_nil
    (x : List Nat) (ys : List (List Nat)) (h : ys ≠ []) :
    Compile.dropTrailingEmpty (x :: ys) = x :: Compile.dropTrailingEmpty ys := by
  cases ys with
  | nil => exact absurd rfl h
  | cons _ _ => cases x <;> rfl

/-- The encoder's trailing empty group is exactly what
`dropTrailingEmpty` removes, leaving the list of shifted registers. -/
private theorem Compile.dropTrailingEmpty_append_nil :
    ∀ l : List (List Nat), Compile.dropTrailingEmpty (l ++ [[]]) = l
  | []        => rfl
  | x :: rest => by
      have h : rest ++ [[]] ≠ [] := by
        intro hc; simpa using congrArg List.length hc
      rw [List.cons_append, Compile.dropTrailingEmpty_cons_ne_nil x _ h,
          Compile.dropTrailingEmpty_append_nil rest]

/-- `unshiftReg` inverts `shiftReg`. -/
private theorem Compile.unshiftReg_shiftReg (reg : List Nat) :
    Compile.unshiftReg (Compile.shiftReg reg) = reg := by
  simp only [Compile.unshiftReg, Compile.shiftReg, List.map_map]
  have h : ((fun n => n - 1) ∘ fun x => x + 1) = id := by funext n; simp
  rw [h, List.map_id]

/-- Decoding the shifted registers recovers the original state. -/
private theorem Compile.map_unshift_shift (s : State) :
    (s.map Compile.shiftReg).map Compile.unshiftReg = s := by
  rw [List.map_map,
      show Compile.unshiftReg ∘ Compile.shiftReg = id from
        funext Compile.unshiftReg_shiftReg,
      List.map_id]

/-- Round-trip lemma — needed by `Compile_sound`. The decoder, applied
to the encoder's initial configuration, recovers the state exactly. -/
theorem Compile.decodeTape_encodeTape (s : State) :
    Compile.decodeTape
        { tapes := [([], 0, Compile.encodeTape s)]
          state_idx := 0 } = s := by
  show (Compile.dropTrailingEmpty
        (Compile.splitOnZero
          (Compile.flattenTape (([] : List Nat), (0 : Nat), Compile.encodeTape s)))).map
        Compile.unshiftReg = s
  rw [show Compile.flattenTape (([] : List Nat), (0 : Nat), Compile.encodeTape s)
        = Compile.encodeTape s from rfl,
      Compile.splitOnZero_encodeTape, Compile.dropTrailingEmpty_append_nil,
      Compile.map_unshift_shift]

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
