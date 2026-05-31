import Complexity.Lang.Semantics
import Complexity.Lang.AppendGadget
import Complexity.Complexity.TMPrimitives
import Complexity.Complexity.TapeMono

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
2. **Alphabet is fixed at `sig = 4`**: symbol `0` is the
   register-delimiter, symbols `1`, `2` are the shifted register
   values for `0`, `1`, and symbol `3` is the end-of-tape terminator
   (`Compile.endMark`; see the encoding section / Risk C1 option A).
   This commits the layer's inputs to bit-strings (the standard
   NP-completeness convention), made explicit by `Compile.BitState`;
   `Op.eval` on bit-shaped states stays bit-shaped.
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
  /-- The machine's alphabet is exactly 4: `0` = delimiter,
  `1` = shifted `0`, `2` = shifted `1`, `3` = end-of-tape terminator. -/
  M_sig : M.sig = 4

/-- The trivial 1-state halting machine, packaged as a
`CompiledCmd` with `exit = 0`. Used as the default body of all
the stub helpers. -/
def compiledCmd_default : CompiledCmd where
  M :=
    { sig := 4
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

/-- Compile `Op.appendOne dst`: navigate past the `dst` preceding
register-delimiters, then insert symbol `2` (the shifted bit `1`) just
before register `dst`'s delimiter. Realized by `AppendGadget.appendAtTM`
with `ins = 2`; all `CompiledCmd` invariants come from that gadget's
exit/halt lemmas. -/
def Compile.opAppendOne (dst : Var) : CompiledCmd where
  M := AppendGadget.appendAtTM 2 dst
  exit := AppendGadget.appendAtTM_exit dst
  exit_lt := AppendGadget.appendAtTM_exit_lt 2 dst
  exit_is_halt := AppendGadget.appendAtTM_exit_is_halt 2 dst
  halt_unique := AppendGadget.appendAtTM_halt_unique 2 dst
  M_valid := AppendGadget.appendAtTM_valid 2 (by decide) dst
  M_tapes := AppendGadget.appendAtTM_tapes 2 dst
  M_sig := AppendGadget.appendAtTM_sig 2 dst

/-- Compile `Op.appendZero dst`: as `opAppendOne`, but inserts symbol `1`
(the shifted bit `0`). Realized by `AppendGadget.appendAtTM` with
`ins = 1`. -/
def Compile.opAppendZero (dst : Var) : CompiledCmd where
  M := AppendGadget.appendAtTM 1 dst
  exit := AppendGadget.appendAtTM_exit dst
  exit_lt := AppendGadget.appendAtTM_exit_lt 1 dst
  exit_is_halt := AppendGadget.appendAtTM_exit_is_halt 1 dst
  halt_unique := AppendGadget.appendAtTM_halt_unique 1 dst
  M_valid := AppendGadget.appendAtTM_valid 1 (by decide) dst
  M_tapes := AppendGadget.appendAtTM_tapes 1 dst
  M_sig := AppendGadget.appendAtTM_sig 1 dst

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
  -- Length-as-value ops (C5a). Stubs, like the other non-bit ops: their physical
  -- soundness folds into the (already assumed) `Compile_sound` gap.
  | .takeAt _dst _src _lenReg  => compiledCmd_default
  | .dropAt _dst _src _lenReg  => compiledCmd_default
  | .concat _dst _src1 _src2   => compiledCmd_default
  | .consLen _dst _lenSrc _src => compiledCmd_default

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
    show (composeFlatTM r1.M r2.M r1.exit).sig = 4
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
  M_sig : M.sig = 4

/-- A placeholder 2-state tester. `exitPos = 0`, `exitNeg = 1`,
no transitions, neither state halts (the bridge in
`branchComposeFlatTM` is what makes progress). Replace with a
real bit-test once the per-register navigation primitives land. -/
def branchTester_default : BranchTester where
  M :=
    { sig := 4
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
      show branched.sig = 4
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

theorem Compile_sig (c : Cmd) : (Compile c).sig = 4 :=
  (compileCmd c).M_sig

/-! ### Encoding / decoding tapes

Convention (alphabet `sig = 4`; Risk C1, option A):

- **Symbol 0** is the reserved register-delimiter.
- Register values are restricted to `{0, 1}` (bit strings) and are
  **shifted by +1** on encode: `0 ↦ 1`, `1 ↦ 2`. Decoding shifts
  back by `-1`. This keeps register values (`{1, 2}`) disjoint from
  both the delimiter `0` and the terminator below.
- **Symbol 3 = `endMark`** is the reserved end-of-tape terminator,
  appended once after all registers. Decoding reads only up to the
  first `endMark`. This is the device that makes length-*decreasing*
  `Op`s sound: such an `Op` cannot shrink the tape (the model only
  appends / overwrites), so it shifts content left and rewrites
  `endMark` one cell earlier — anything past the terminator is junk
  and is ignored by the decoder *and* by every navigation gadget,
  which stop at the terminator rather than reading past it.

So `encodeTape [[1, 0], [0, 1]] = [2, 1, 0, 1, 2, 0, 3]`, and decoding
takes the prefix before `3`, splits on `0`, shifts each chunk by `-1`,
and drops the trailing empty.

The shift+terminator scheme requires inputs to be **bit-shaped**
(`Compile.BitState`): with a register value of `2`, `shiftReg` would
emit `3` and collide with the terminator. `BitState` is the layer's
standing convention (NP-completeness inputs are bit strings) and is
preserved by `Op.eval`; it is also exactly what tape-validity needs
(every symbol `< sig = 4`). -/

/-- Encode the per-register shift `+1`. -/
private def Compile.shiftReg (reg : List Nat) : List Nat := reg.map (· + 1)

/-- Reverse of `shiftReg`. Maps `0 ↦ 0` so the inverse is only valid
on tapes that contain no raw `0` (i.e., tapes produced by `shiftReg`). -/
private def Compile.unshiftReg (reg : List Nat) : List Nat :=
  reg.map (fun n => n - 1)

/-- The reserved end-of-tape terminator symbol. -/
def Compile.endMark : Nat := 3

/-- A state is *bit-shaped* if every register holds only `0`/`1`.
The layer's standing convention; preserved by `Op.eval`. Keeps the
shifted values `{1, 2}` disjoint from the terminator `endMark = 3`. -/
def Compile.BitState (s : State) : Prop := ∀ reg ∈ s, ∀ x ∈ reg, x ≤ 1

/-- Encode the registers contiguously: each shifted by `+1` and
followed by the `0` delimiter. Does **not** include the terminator. -/
def Compile.encodeRegs (s : State) : List Nat :=
  s.foldr (fun reg acc => Compile.shiftReg reg ++ [0] ++ acc) []

theorem Compile.encodeRegs_nil :
    Compile.encodeRegs [] = [] := rfl

theorem Compile.encodeRegs_cons (reg : List Nat) (s : State) :
    Compile.encodeRegs (reg :: s) =
      Compile.shiftReg reg ++ [0] ++ Compile.encodeRegs s := rfl

/-- Encode a `State` as a flat tape: a **leading sentinel** `endMark`, the
registers (`encodeRegs`), and the end-of-tape terminator `endMark`.

The leading sentinel (reusing `endMark = 3`, so the alphabet stays `sig = 4`) is
the head-rewind anchor required to *compose* compiled fragments (Risk C2): a
compiled `Op` halts with its head mid-tape, but `composeFlatTM` resumes the next
machine on that exact head, while every per-`Op` soundness statement assumes the
head starts at `0`. `scanLeftUntilTM 4 3` (`ScanLeft.rewindToStart_run`) scans
left to this leading `3` at index `0`, since the interior carries only
`{0, 1, 2}` (`encodeRegs` of a `BitState`). The head starts at index `0` on the
sentinel; the scan/insert gadgets fold it into their first (marker-free) block,
so no head-bridge is needed. -/
def Compile.encodeTape (s : State) : List Nat :=
  Compile.endMark :: (Compile.encodeRegs s ++ [Compile.endMark])

/-- The encoded registers occupy `State.size s + s.length` cells: each register
contributes its (shifted) contents plus one `0` delimiter. -/
theorem Compile.encodeRegs_length (s : State) :
    (Compile.encodeRegs s).length = State.size s + s.length := by
  induction s with
  | nil => rfl
  | cons reg s ih =>
      rw [Compile.encodeRegs_cons]
      simp only [List.length_append, Compile.shiftReg, List.length_map, List.length_cons,
        List.length_nil, ih, State.size, List.map_cons, List.foldr_cons]
      omega

/-- **Tape length = contents + register count + 2.** The encoded tape is the
registers (`State.size s + s.length` cells) plus the leading and trailing
`endMark` sentinels. This is the link
between the per-op gadget step bounds (which grow with the *tape length*) and the
`State.size` / register-count bounds (`Cmd.size_eval_le` / `Cmd.eval_length_le`)
— so the intermediate tape length during a `Compile` run is bounded linearly in
`size + cost + regBound`. -/
theorem Compile.encodeTape_length (s : State) :
    (Compile.encodeTape s).length = State.size s + s.length + 2 := by
  rw [Compile.encodeTape, List.length_cons, List.length_append,
      Compile.encodeRegs_length]; rfl

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
      -- Drop the leading sentinel, then read up to the trailing terminator.
      let content := flat.tail.takeWhile (· != Compile.endMark)
      let groups := Compile.splitOnZero content
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
private theorem Compile.splitOnZero_encodeRegs :
    ∀ s : State,
      Compile.splitOnZero (Compile.encodeRegs s)
        = s.map Compile.shiftReg ++ [[]]
  | []          => by simp [Compile.encodeRegs, Compile.splitOnZero]
  | reg :: rest => by
      rw [Compile.encodeRegs_cons]
      have happ : Compile.shiftReg reg ++ [0] ++ Compile.encodeRegs rest
          = Compile.shiftReg reg ++ 0 :: Compile.encodeRegs rest := by simp
      rw [happ, Compile.splitOnZero_append_zero _ _ (Compile.shiftReg_no_zero reg),
          Compile.splitOnZero_encodeRegs rest, List.map_cons, List.cons_append]

/-- `encodeRegs` of a bit-shaped state never emits the terminator
`endMark`: delimiters are `0` and shifted bits are `{1, 2}`. -/
private theorem Compile.encodeRegs_no_endMark :
    ∀ (s : State), Compile.BitState s →
      ∀ x ∈ Compile.encodeRegs s, x ≠ Compile.endMark
  | [],          _, x, hx => by simp [Compile.encodeRegs] at hx
  | reg :: rest, h, x, hx => by
      rw [Compile.encodeRegs_cons] at hx
      simp only [List.append_assoc, List.mem_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx
      · simp only [Compile.shiftReg, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have : y ≤ 1 := h reg (by simp) y hy
        simp only [Compile.endMark]; omega
      · simp only [Compile.endMark]; omega
      · exact Compile.encodeRegs_no_endMark rest
          (fun r hr => h r (by simp [hr])) x hx

/-- Taking the prefix before the terminator recovers the registers,
provided the registers themselves contain no terminator. -/
private theorem Compile.takeWhile_no_endMark :
    ∀ (l : List Nat), (∀ x ∈ l, x ≠ Compile.endMark) →
      (l ++ [Compile.endMark]).takeWhile (· != Compile.endMark) = l
  | [],     _ => by decide
  | a :: t, h => by
      have ha : a ≠ Compile.endMark := h a (by simp)
      have ht : ∀ x ∈ t, x ≠ Compile.endMark := fun x hx => h x (by simp [hx])
      rw [List.cons_append, List.takeWhile_cons,
          if_pos (by simp [bne_iff_ne, ha]), Compile.takeWhile_no_endMark t ht]

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
to the encoder's initial configuration, recovers the state exactly,
for any bit-shaped state. -/
theorem Compile.decodeTape_encodeTape (s : State) (h : Compile.BitState s) :
    Compile.decodeTape
        { tapes := [([], 0, Compile.encodeTape s)]
          state_idx := 0 } = s := by
  show (Compile.dropTrailingEmpty
        (Compile.splitOnZero
          ((Compile.flattenTape (([] : List Nat), (0 : Nat), Compile.encodeTape s)).tail.takeWhile
            (· != Compile.endMark)))).map Compile.unshiftReg = s
  rw [show (Compile.flattenTape (([] : List Nat), (0 : Nat), Compile.encodeTape s)).tail
        = Compile.encodeRegs s ++ [Compile.endMark] from rfl,
      Compile.takeWhile_no_endMark _ (Compile.encodeRegs_no_endMark s h),
      Compile.splitOnZero_encodeRegs, Compile.dropTrailingEmpty_append_nil,
      Compile.map_unshift_shift]

/-- Generalisation of `takeWhile_no_endMark`: taking the prefix before the first
terminator recovers `l`, even when arbitrary `rest` follows the terminator. -/
private theorem Compile.takeWhile_no_endMark_append :
    ∀ (l rest : List Nat), (∀ x ∈ l, x ≠ Compile.endMark) →
      (l ++ Compile.endMark :: rest).takeWhile (· != Compile.endMark) = l
  | [],     rest, _ => by
      rw [List.nil_append, List.takeWhile_cons, if_neg (by simp [bne_iff_ne])]
  | a :: t, rest, h => by
      have ha : a ≠ Compile.endMark := h a (by simp)
      have ht : ∀ x ∈ t, x ≠ Compile.endMark := fun x hx => h x (by simp [hx])
      rw [List.cons_append, List.takeWhile_cons,
          if_pos (by simp [bne_iff_ne, ha]), Compile.takeWhile_no_endMark_append t rest ht]

/-- **Residue-tolerant decode (Risk C2 resolution foundation).** `decodeTape`
ignores both the head position and any trailing residue after the encoded tape:
decoding `encodeTape s ++ residue` recovers `s` for *any* `residue` and *any*
head `hd`. This holds because `decodeTape` reads `takeWhile (· ≠ endMark)` of the
tail, which stops at the **first** (real) terminator — and `encodeRegs s` of a
`BitState` contains no terminator. This is the key lemma that makes the
recommended residue-tolerant physical contract decode correctly: a length-
decreasing op may leave `encodeTape (output) ++ residue` on the (non-shrinking)
tape (see `Complexity/Complexity/TapeMono.lean`), yet still decode to `output`.
-/
theorem Compile.decodeTape_encodeTape_append (s : State) (residue : List Nat)
    (q hd : Nat) (h : Compile.BitState s) :
    Compile.decodeTape
        { state_idx := q, tapes := [([], hd, Compile.encodeTape s ++ residue)] } = s := by
  show (Compile.dropTrailingEmpty (Compile.splitOnZero
        ((Compile.flattenTape (([] : List Nat), hd, Compile.encodeTape s ++ residue)).tail.takeWhile
          (· != Compile.endMark)))).map Compile.unshiftReg = s
  have htail : (Compile.flattenTape (([] : List Nat), hd, Compile.encodeTape s ++ residue)).tail
      = Compile.encodeRegs s ++ Compile.endMark :: residue := by
    show (Compile.encodeTape s ++ residue).tail = Compile.encodeRegs s ++ Compile.endMark :: residue
    rw [Compile.encodeTape, List.cons_append, List.tail_cons, List.append_assoc, List.cons_append,
        List.nil_append]
  rw [htail, Compile.takeWhile_no_endMark_append _ residue (Compile.encodeRegs_no_endMark s h),
      Compile.splitOnZero_encodeRegs, Compile.dropTrailingEmpty_append_nil,
      Compile.map_unshift_shift]

/-- After the leading sentinel, the encoded tape continues with `shiftReg`-ed
register `0`. When register `0` holds a single bit `b` (the decider answer
convention — `[1]` for accept, `[0]` for reject), the encoded tape is
`endMark :: (b + 1) :: …`. This is the only fact the tape→state bit-test gadget
needs about the encoding (it steps past the sentinel, then reads `b + 1`). -/
theorem Compile.encodeTape_eq_cons_of_get_zero (s : State) (b : Nat)
    (h : s.get 0 = [b]) :
    ∃ tl, Compile.encodeTape s = Compile.endMark :: (b + 1) :: tl := by
  cases s with
  | nil => simp [State.get] at h
  | cons r0 rest =>
      have hr0 : r0 = [b] := by simpa [State.get] using h
      refine ⟨[0] ++ Compile.encodeRegs rest ++ [Compile.endMark], ?_⟩
      show Compile.endMark :: (Compile.encodeRegs (r0 :: rest) ++ [Compile.endMark])
          = Compile.endMark :: (b + 1) :: ([0] ++ Compile.encodeRegs rest ++ [Compile.endMark])
      rw [Compile.encodeRegs_cons, hr0]
      simp [Compile.shiftReg]

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

/-! ### Encoding-seam helpers for the per-op soundness lemma

`compileOp_sound` above is sorry-bodied for *all* ops. The helpers below
(`encodeTape_split`, the `shiftReg`/`regBlocks` algebra, the `BitState`
preservation lemmas, and the `decodeTape`/`encodeTape` round trip) connect the
compiler's single-tape `encodeTape`/`decodeTape` contract to the proven gadget
library (`AppendGadget.appendAt_run_steps`, …). They feed the live per-op
soundness lemma `Compile.appendBit_sound` (general `dst`, linear step budget)
below, which discharges the behavioural + budget halves of `compileOp_sound`
for the two real ops `appendOne`/`appendZero`.

Note the **leading-sentinel encoding** (`encodeTape s = endMark :: encodeRegs s
++ [endMark]`): the gadget starts at head `0` on the sentinel, which
`appendBit_sound` folds into the first marker-free block so the scan still
begins at head `0` (no head-bridge needed). -/

private theorem Compile.encodeRegs_append (a b : State) :
    Compile.encodeRegs (a ++ b)
      = Compile.encodeRegs a ++ Compile.encodeRegs b := by
  induction a with
  | nil => rfl
  | cons r a ih =>
      rw [List.cons_append, Compile.encodeRegs_cons, Compile.encodeRegs_cons, ih]
      simp [List.append_assoc]

private theorem Compile.regBlocks_map_shiftReg (l : State) :
    AppendGadget.regBlocks (l.map Compile.shiftReg) = Compile.encodeRegs l := by
  induction l with
  | nil => rfl
  | cons r l ih =>
      rw [List.map_cons, AppendGadget.regBlocks_cons, Compile.encodeRegs_cons, ih]
      simp [List.append_assoc]

private theorem Compile.shiftReg_append_one (l : List Nat) :
    Compile.shiftReg (l ++ [1]) = Compile.shiftReg l ++ [2] := by
  simp [Compile.shiftReg]

private theorem Compile.shiftReg_append (l : List Nat) (b : Nat) :
    Compile.shiftReg (l ++ [b]) = Compile.shiftReg l ++ [b + 1] := by
  simp [Compile.shiftReg]

private theorem Compile.list_set_eq_take_cons_drop {α : Type} :
    ∀ (l : List α) (i : Nat) (v : α), i < l.length →
      l.set i v = l.take i ++ v :: l.drop (i + 1)
  | _ :: _, 0, _, _ => by simp
  | a :: l, i + 1, v, h => by
      simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons,
        List.cons_append]
      rw [Compile.list_set_eq_take_cons_drop l i v (by simpa using h)]
  | [], _, _, h => by simp at h

private theorem Compile.list_eq_take_getElem_drop {α : Type} :
    ∀ (l : List α) (i : Nat) (h : i < l.length),
      l = l.take i ++ l[i] :: l.drop (i + 1)
  | _ :: _, 0, _ => by simp
  | a :: l, i + 1, h => by
      simp only [List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ,
        List.cons_append]
      exact congrArg (a :: ·) (Compile.list_eq_take_getElem_drop l i (by simpa using h))
  | [], _, h => by simp at h

/-- The **registers part** of the encoded tape (i.e. `encodeTape s` with its
leading and trailing sentinels stripped — equivalently `encodeRegs s ++
[endMark]`) splits at register `dst` into the preceding register blocks, the
target register's shifted contents, its delimiter, and the rest — exactly the
shape `AppendGadget.appendAt_run` consumes (with empty prefix). The leading
sentinel of `encodeTape` is reattached by the caller (`appendBit_sound`). -/
private theorem Compile.encodeTape_split (s : State) (dst : Var) (h : dst < s.length) :
    AppendGadget.regBlocks ((s.take dst).map Compile.shiftReg)
        ++ Compile.shiftReg (s.get dst)
        ++ 0 :: (Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark])
      = Compile.encodeRegs s ++ [Compile.endMark] := by
  have hget : s.get dst = s[dst] := by
    rw [State.get, List.getElem?_eq_getElem h]; rfl
  have hs : Compile.encodeRegs s
      = Compile.encodeRegs (s.take dst) ++ Compile.shiftReg s[dst]
          ++ [0] ++ Compile.encodeRegs (s.drop (dst + 1)) := by
    conv_lhs => rw [Compile.list_eq_take_getElem_drop s dst h]
    rw [Compile.encodeRegs_append, Compile.encodeRegs_cons]
    simp [List.append_assoc]
  rw [Compile.regBlocks_map_shiftReg, hget, hs]
  simp [List.append_assoc]

/-- `appendOne` preserves bit-shape (it appends the bit `1`). -/
private theorem Compile.BitState_appendOne (s : State) (dst : Var)
    (h : Compile.BitState s) (hdst : dst < s.length) :
    Compile.BitState (Op.eval (Op.appendOne dst) s) := by
  show Compile.BitState (s.set dst (s.get dst ++ [1]))
  rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst]
  intro reg hreg x hx
  simp only [List.mem_append, List.mem_cons] at hreg
  rcases hreg with hr | hr | hr
  · exact h reg (List.mem_of_mem_take hr) x hx
  · subst hr
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have hmem : s.get dst ∈ s := by
        rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
      exact h _ hmem x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega
  · exact h reg (List.mem_of_mem_drop hr) x hx

/-- Appending any bit `b ≤ 1` to register `dst` preserves bit-shape. The
general form of `BitState_appendOne` covering both `appendOne` (`b = 1`) and
`appendZero` (`b = 0`). -/
private theorem Compile.BitState_appendBit (b : Nat) (hb : b ≤ 1) (s : State)
    (dst : Var) (h : Compile.BitState s) (hdst : dst < s.length) :
    Compile.BitState (s.set dst (s.get dst ++ [b])) := by
  rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst]
  intro reg hreg x hx
  simp only [List.mem_append, List.mem_cons] at hreg
  rcases hreg with hr | hr | hr
  · exact h reg (List.mem_of_mem_take hr) x hx
  · subst hr
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have hmem : s.get dst ∈ s := by
        rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
      exact h _ hmem x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega
  · exact h reg (List.mem_of_mem_drop hr) x hx

/-- Every symbol of `encodeRegs t` is `< 4` when `t` is bit-shaped (shifted
bits are `1`/`2`, delimiters are `0`). -/
private theorem Compile.encodeRegs_lt_four (t : State)
    (h : ∀ b ∈ t, ∀ x ∈ b, x ≤ 1) : ∀ y ∈ Compile.encodeRegs t, y < 4 := by
  induction t with
  | nil => intro y hy; simp [Compile.encodeRegs] at hy
  | cons r t ih =>
      intro y hy
      rw [Compile.encodeRegs_cons, List.mem_append, List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · rw [Compile.shiftReg, List.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        have := h r (List.mem_cons_self ..) z hz; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega
      · exact ih (fun b hb x hx => h b (List.mem_cons_of_mem _ hb) x hx) y hy

/-- `decodeTape` ignores the state index, head position and `left` track, so
the round-trip `decodeTape ∘ encodeTape = id` holds at any halting config. -/
private theorem Compile.decodeTape_encodeTape' (q hd : Nat) (t : State)
    (h : Compile.BitState t) :
    Compile.decodeTape { state_idx := q, tapes := [([], hd, Compile.encodeTape t)] } = t :=
  Compile.decodeTape_encodeTape t h

/-! ### Structure of `encodeTape` (for the rewind side-conditions, step 1b-2)

The `appendAt_rewind_run` bracket needs three facts about the gadget's *exit*
tape (which is `encodeTape output`): its cell `0` is the leading sentinel `3`,
every cell is `< 4`, and the interior (everything but the trailing terminator)
is sentinel-free. -/

/-- Cell `0` of any `encodeTape` is the leading sentinel `endMark = 3`. -/
theorem Compile.encodeTape_get_zero (t : State)
    (h : 0 < (Compile.encodeTape t).length) :
    (Compile.encodeTape t).get ⟨0, h⟩ = 3 := rfl

/-- Every symbol of `encodeTape t` is `< 4` for a bit-shaped `t`. -/
theorem Compile.encodeTape_lt_four (t : State) (h : Compile.BitState t) :
    ∀ x ∈ Compile.encodeTape t, x < 4 := by
  intro x hx
  rw [Compile.encodeTape, List.mem_cons, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx | hx
  · subst hx; decide
  · exact Compile.encodeRegs_lt_four t h x hx
  · subst hx; decide

/-- Every interior cell of `encodeTape t` (i.e. every cell *except* the trailing
terminator) is `≠ endMark = 3`: cell `0` is the leading sentinel `3` but cell
`i ≥ 1` with `i + 1 < length` lands inside `encodeRegs t`, which is
sentinel-free. The leading sentinel at `0` is the rewind *target*, so the
interior-non-sentinel claim is restricted to `0 < i`. -/
theorem Compile.encodeTape_interior_ne_endMark (t : State) (h : Compile.BitState t) :
    ∀ i, 0 < i → i + 1 < (Compile.encodeTape t).length →
      ∃ (hi : i < (Compile.encodeTape t).length),
        (Compile.encodeTape t).get ⟨i, hi⟩ ≠ 3 := by
  intro i hi_pos hi_lt
  refine ⟨by omega, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  -- encodeTape t = 3 :: (encodeRegs t ++ [3]); cell j+1 = (encodeRegs t ++ [3])[j].
  have hlen : (Compile.encodeTape t).length = (Compile.encodeRegs t).length + 2 := by
    rw [Compile.encodeTape]; simp [List.length_append]
  have hj : j < (Compile.encodeRegs t).length := by omega
  simp only [List.get_eq_getElem, Compile.encodeTape, List.getElem_cons_succ]
  rw [List.getElem_append_left hj]
  exact Compile.encodeRegs_no_endMark t h _ (List.getElem_mem hj)

/-! ### Per-op soundness for `appendOne`/`appendZero` (general `dst`, LINEAR budget)

The two append ops are the only `compileOp`s with real TM bodies. The lemma
below discharges `compileOp_sound` for both — at **general `dst`** and with the
**linear tape-length budget** `2 · (encodeTape s).length + 3`. This is the
*composable* per-fragment budget (ROADMAP Risk C2 / plan step 1b): the quadratic
`overhead` budget the earlier version used does **not** compose (summing `~cost`
quadratics → cubic; see the finding block below `compileSeq_sound`), whereas
linear per-fragment bounds sum to a quadratic total.

It composes `AppendGadget.appendAt_run_steps` (explicit step count) with
`appendAt_steps_le` (the step count is exactly `≤ 2·tapeLen + 3`). The leading
sentinel of `encodeTape` is folded into the first marker-free block so the
gadget runs from head `0`. (Recovering the old quadratic budget, if ever needed,
is just `Nat`-monotone padding: `2·tapeLen + 3 ≤ overhead (tapeLen + 1)`.) -/
private theorem Compile.appendBit_sound (bit : Nat) (hb : bit ≤ 1)
    (s : State) (dst : Var) (hbit : Compile.BitState s) (hdst : dst < s.length) :
    ∃ cfg,
      runFlatTM (2 * (Compile.encodeTape s).length + 3)
          (AppendGadget.appendAtTM (bit + 1) dst)
          (initFlatConfig (AppendGadget.appendAtTM (bit + 1) dst)
            [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (AppendGadget.appendAtTM (bit + 1) dst) cfg = true ∧
      Compile.decodeTape cfg = s.set dst (s.get dst ++ [bit]) := by
  have h_ins : bit + 1 < 4 := by omega
  set post : List Nat := Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] with hpost
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskip
  set body : List Nat := Compile.shiftReg (s.get dst) with hbody
  have hget_mem : s.get dst ∈ s := by
    rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
  -- Side conditions for `appendAt_run_steps`, all from bit-shape.
  have hshift_lt : ∀ (r : List Nat), (∀ x ∈ r, x ≤ 1) → ∀ x ∈ Compile.shiftReg r, x < 4 := by
    intro r hr x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hr y hy; omega
  have hshift_ne : ∀ (r : List Nat), ∀ x ∈ Compile.shiftReg r, x ≠ 0 := by
    intro r x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; omega
  have hlen : skipped.length = dst := by
    rw [hskip, List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hdst)]
  have h_pre : ∀ x ∈ ([] : List Nat), x < 4 := by intro x hx; cases hx
  have h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    intro b hbm
    rw [hskip, List.mem_map] at hbm
    obtain ⟨r, hr, rfl⟩ := hbm
    exact ⟨hshift_ne r, hshift_lt r (fun x hx => hbit r (List.mem_of_mem_take hr) x hx)⟩
  have hbody_ne : ∀ x ∈ body, x ≠ 0 := by rw [hbody]; exact hshift_ne _
  have hbody_lt : ∀ x ∈ body, x < 4 := by
    rw [hbody]; exact hshift_lt _ (fun x hx => hbit _ hget_mem x hx)
  have hpost_lt : ∀ x ∈ post, x < 4 := by
    rw [hpost]; intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeRegs_lt_four _
        (fun b hbm y hy => hbit b (List.mem_of_mem_drop hbm) y hy) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide
  -- **Fold the leading sentinel into the first marker-free block.** The new
  -- `encodeTape` is `endMark :: (encodeRegs s ++ [endMark])`, but the gadget
  -- starts at head `0` (`initFlatConfig`). Rather than bridge head `0 → 1`, we
  -- absorb the leading `endMark` into the first scanned block: into `body` when
  -- `dst = 0` (no skipped registers), or into the first skipped register when
  -- `dst ≥ 1`. Both keep the gadget's head at `0` over the *full* tape.
  have key : ∃ (sk : List (List Nat)) (bd : List Nat),
      sk.length = dst ∧
      (∀ b ∈ sk, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) ∧
      (∀ x ∈ bd, x ≠ 0) ∧ (∀ x ∈ bd, x < 4) ∧
      AppendGadget.regBlocks sk ++ bd
        = Compile.endMark :: (AppendGadget.regBlocks skipped ++ body) := by
    cases hsk : skipped with
    | nil =>
        refine ⟨[], Compile.endMark :: body, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hlen, hsk]
        · intro b hb; cases hb
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_ne x h
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_lt x h
        · simp [AppendGadget.regBlocks_nil]
    | cons hd tl =>
        refine ⟨(Compile.endMark :: hd) :: tl, body, ?_, ?_, hbody_ne, hbody_lt, ?_⟩
        · rw [hsk] at hlen; simpa using hlen
        · intro b hb
          rcases List.mem_cons.mp hb with h | h
          · subst h
            refine ⟨?_, ?_⟩
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).1 x h0
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).2 x h0
          · exact h_skip b (by rw [hsk]; exact List.mem_cons_of_mem _ h)
        · simp [AppendGadget.regBlocks_cons]
  obtain ⟨sk, bd, hlen_sk, h_skip_sk, hbd_ne, hbd_lt, hsfold⟩ := key
  -- The gadget run lemma, with its explicit step count, on the folded blocks.
  obtain ⟨st', hrun, hhalt⟩ :=
    AppendGadget.appendAt_run_steps (bit + 1) h_ins dst [] sk bd post hlen_sk
      h_pre h_skip_sk hbd_ne hbd_lt hpost_lt
  -- Name the explicit exit head for convenience.
  set hd' : Nat := [].length + (AppendGadget.regBlocks sk).length + bd.length
      + (0 :: post).length with hd'_def
  -- The sentinel-free split: `regBlocks skipped ++ body ++ 0 :: post` is the
  -- registers part of `encodeTape s` (= `encodeRegs s ++ [endMark]`).
  have hsplit0 : AppendGadget.regBlocks skipped ++ body ++ 0 :: post
      = Compile.encodeRegs s ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost]; exact Compile.encodeTape_split s dst hdst
  -- Reattaching the leading sentinel recovers the full `encodeTape s`.
  have hsplit : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post
      = Compile.encodeTape s := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, hsplit0]
  rw [List.length_nil, hsplit] at hrun
  have hinit : initFlatConfig (AppendGadget.appendAtTM (bit + 1) dst) [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := by
    simp only [initFlatConfig, AppendGadget.appendAtTM_start, List.map_cons, List.map_nil]
  -- The explicit step count is **linear** in the tape length (`≤ 2·tapeLen + 3`,
  -- directly from `appendAt_steps_le`); this is the composable per-fragment bound.
  have hstep_le : AppendGadget.appendAt_steps sk bd post
      ≤ 2 * (Compile.encodeTape s).length + 3 := by
    have hb' := AppendGadget.appendAt_steps_le sk bd post
    have hL : (AppendGadget.regBlocks sk ++ bd ++ 0 :: post).length
        = (Compile.encodeTape s).length := by rw [← hsplit]; simp
    rw [hL] at hb'; exact hb'
  obtain ⟨k, hk⟩ := Nat.le.dest hstep_le
  -- The output tape decodes to the evaluated state.
  have htape0 : AppendGadget.regBlocks skipped ++ body ++ (bit + 1) :: 0 :: post
      = Compile.encodeRegs (s.set dst (s.get dst ++ [bit])) ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost, Compile.regBlocks_map_shiftReg]
    rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst,
        Compile.encodeRegs_append, Compile.encodeRegs_cons, Compile.shiftReg_append]
    simp [List.append_assoc]
  have htape : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post
      = Compile.encodeTape (s.set dst (s.get dst ++ [bit])) := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, htape0]
  refine ⟨{ state_idx := st',
            tapes := [([], hd',
              ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
                ++ (bit + 1) :: 0 :: post)] }, ?_, ?_, ?_⟩
  · rw [hinit, ← hk]; exact runFlatTM_extend hrun hhalt
  · exact hhalt
  · rw [show Compile.decodeTape
          { state_idx := st',
            tapes := [([], hd',
              ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
                ++ (bit + 1) :: 0 :: post)] }
        = Compile.decodeTape
          { state_idx := st',
            tapes := [([], hd',
              Compile.encodeTape (s.set dst (s.get dst ++ [bit])))] }
        from by rw [htape]]
    exact Compile.decodeTape_encodeTape' st' hd' _
      (Compile.BitState_appendBit bit hb s dst hbit hdst)

/-- **`compileOp_sound` for `appendOne`, general `dst`, LINEAR budget**
(`2 · (encodeTape s).length + 3` — the composable per-fragment bound). -/
theorem compileOp_appendOne_sound (s : State) (dst : Var)
    (hbit : Compile.BitState s) (hdst : dst < s.length) :
    ∃ cfg,
      runFlatTM (2 * (Compile.encodeTape s).length + 3)
          (compileOp (Op.appendOne dst)).M
          (initFlatConfig (compileOp (Op.appendOne dst)).M
            [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (compileOp (Op.appendOne dst)).M cfg = true ∧
      Compile.decodeTape cfg = Op.eval (Op.appendOne dst) s :=
  Compile.appendBit_sound 1 (by omega) s dst hbit hdst

/-- **`compileOp_sound` for `appendZero`, general `dst`, LINEAR budget**
(`2 · (encodeTape s).length + 3` — the composable per-fragment bound). -/
theorem compileOp_appendZero_sound (s : State) (dst : Var)
    (hbit : Compile.BitState s) (hdst : dst < s.length) :
    ∃ cfg,
      runFlatTM (2 * (Compile.encodeTape s).length + 3)
          (compileOp (Op.appendZero dst)).M
          (initFlatConfig (compileOp (Op.appendZero dst)).M
            [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (compileOp (Op.appendZero dst)).M cfg = true ∧
      Compile.decodeTape cfg = Op.eval (Op.appendZero dst) s :=
  Compile.appendBit_sound 0 (by omega) s dst hbit hdst

/-- **Per-fragment physical contract for the append op (Risk C2, step 1b-2).**
The bracketed machine `appendAtThenRewindTM (bit+1) dst` run on `encodeTape s`
halts at the composite exit `3 + appendAtTM.states` with the **head rewound to
`0`** and the tape exactly `encodeTape (output)` — never halting earlier — in a
**linear** number of steps `≤ 3·(encodeTape s).length + 6`. This is the
`encodeTape`-level instance of `AppendGadget.appendAt_rewind_run`, and the form
`compileSeq_compose_physical` consumes when composing fragments (head `0` makes
the exit config equal `initFlatConfig` of the next fragment). The three rewind
side-conditions are discharged from the `encodeTape` structure. -/
theorem Compile.appendBit_physical (bit : Nat) (hb : bit ≤ 1)
    (s : State) (dst : Var) (hbit : Compile.BitState s) (hdst : dst < s.length) :
    ∃ t : Nat,
      runFlatTM t (AppendGadget.appendAtThenRewindTM (bit + 1) dst)
          (initFlatConfig (AppendGadget.appendAtThenRewindTM (bit + 1) dst)
            [Compile.encodeTape s])
        = some { state_idx := 3 + (AppendGadget.appendAtTM (bit + 1) dst).states,
                 tapes := [([], 0,
                   Compile.encodeTape (s.set dst (s.get dst ++ [bit])))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (AppendGadget.appendAtThenRewindTM (bit + 1) dst)
              (initFlatConfig (AppendGadget.appendAtThenRewindTM (bit + 1) dst)
                [Compile.encodeTape s]) = some ck →
          haltingStateReached (AppendGadget.appendAtThenRewindTM (bit + 1) dst) ck = false)
      ∧ t ≤ 3 * (Compile.encodeTape s).length + 6 := by
  have h_ins : bit + 1 < 4 := by omega
  set post : List Nat := Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] with hpost
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskip
  set body : List Nat := Compile.shiftReg (s.get dst) with hbody
  have hget_mem : s.get dst ∈ s := by
    rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
  have hshift_lt : ∀ (r : List Nat), (∀ x ∈ r, x ≤ 1) → ∀ x ∈ Compile.shiftReg r, x < 4 := by
    intro r hr x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hr y hy; omega
  have hshift_ne : ∀ (r : List Nat), ∀ x ∈ Compile.shiftReg r, x ≠ 0 := by
    intro r x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; omega
  have hlen : skipped.length = dst := by
    rw [hskip, List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hdst)]
  have h_pre : ∀ x ∈ ([] : List Nat), x < 4 := by intro x hx; cases hx
  have h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    intro b hbm
    rw [hskip, List.mem_map] at hbm
    obtain ⟨r, hr, rfl⟩ := hbm
    exact ⟨hshift_ne r, hshift_lt r (fun x hx => hbit r (List.mem_of_mem_take hr) x hx)⟩
  have hbody_ne : ∀ x ∈ body, x ≠ 0 := by rw [hbody]; exact hshift_ne _
  have hbody_lt : ∀ x ∈ body, x < 4 := by
    rw [hbody]; exact hshift_lt _ (fun x hx => hbit _ hget_mem x hx)
  have hpost_lt : ∀ x ∈ post, x < 4 := by
    rw [hpost]; intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeRegs_lt_four _
        (fun b hbm y hy => hbit b (List.mem_of_mem_drop hbm) y hy) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide
  have key : ∃ (sk : List (List Nat)) (bd : List Nat),
      sk.length = dst ∧
      (∀ b ∈ sk, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) ∧
      (∀ x ∈ bd, x ≠ 0) ∧ (∀ x ∈ bd, x < 4) ∧
      AppendGadget.regBlocks sk ++ bd
        = Compile.endMark :: (AppendGadget.regBlocks skipped ++ body) := by
    cases hsk : skipped with
    | nil =>
        refine ⟨[], Compile.endMark :: body, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hlen, hsk]
        · intro b hb; cases hb
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_ne x h
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_lt x h
        · simp [AppendGadget.regBlocks_nil]
    | cons hd tl =>
        refine ⟨(Compile.endMark :: hd) :: tl, body, ?_, ?_, hbody_ne, hbody_lt, ?_⟩
        · rw [hsk] at hlen; simpa using hlen
        · intro b hb
          rcases List.mem_cons.mp hb with h | h
          · subst h
            refine ⟨?_, ?_⟩
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).1 x h0
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).2 x h0
          · exact h_skip b (by rw [hsk]; exact List.mem_cons_of_mem _ h)
        · simp [AppendGadget.regBlocks_cons]
  obtain ⟨sk, bd, hlen_sk, h_skip_sk, hbd_ne, hbd_lt, hsfold⟩ := key
  have hsplit0 : AppendGadget.regBlocks skipped ++ body ++ 0 :: post
      = Compile.encodeRegs s ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost]; exact Compile.encodeTape_split s dst hdst
  have hsplit : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post
      = Compile.encodeTape s := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, hsplit0]
  have htape0 : AppendGadget.regBlocks skipped ++ body ++ (bit + 1) :: 0 :: post
      = Compile.encodeRegs (s.set dst (s.get dst ++ [bit])) ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost, Compile.regBlocks_map_shiftReg]
    rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst,
        Compile.encodeRegs_append, Compile.encodeRegs_cons, Compile.shiftReg_append]
    simp [List.append_assoc]
  have htape : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post
      = Compile.encodeTape (s.set dst (s.get dst ++ [bit])) := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, htape0]
  set output : State := s.set dst (s.get dst ++ [bit]) with houtput
  have hbit_out : Compile.BitState output :=
    Compile.BitState_appendBit bit hb s dst hbit hdst
  -- `htape : LT = encodeTape output`, where `LT` is the gadget's exit tape.
  -- Head/length relations (`HD = L`, `|encodeTape output| = HD + 1`).
  have hHD_L : ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
        + (0 :: post).length = (Compile.encodeTape s).length := by
    rw [← hsplit]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hEO_HD : (Compile.encodeTape output).length
      = ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
        + (0 :: post).length + 1 := by
    rw [← htape]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  -- `get`-equality across `htape` (no dependent rewrite: route through `getElem?`).
  have hget_eq : ∀ (i : Nat)
      (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post).length)
      (h' : i < (Compile.encodeTape output).length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post).get ⟨i, h⟩
        = (Compile.encodeTape output).get ⟨i, h'⟩ := by
    intro i h h'
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hopt := congrArg (fun l => l[i]?) htape
    simp only at hopt
    rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem h'] at hopt
    exact Option.some.inj hopt
  -- The three rewind side-conditions, from the `encodeTape output` structure.
  have h_tp_lt : ∀ x ∈ ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
      ++ (bit + 1) :: 0 :: post, x < 4 := by
    intro x hx; rw [htape] at hx; exact Compile.encodeTape_lt_four output hbit_out x hx
  have h_t0 : ∀ (h : 0 < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post).length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post).get ⟨0, h⟩
        = 3 := by
    intro h
    have h' : 0 < (Compile.encodeTape output).length := by rw [← htape]; exact h
    rw [hget_eq 0 h h']; exact Compile.encodeTape_get_zero output h'
  have h_interior_ne : ∀ i, 0 < i →
      i < ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
        + (0 :: post).length →
      ∃ (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
          ++ (bit + 1) :: 0 :: post).length),
        (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post).get ⟨i, h⟩
          ≠ 3 := by
    intro i hi hilt
    have hi1 : i + 1 < (Compile.encodeTape output).length := by rw [hEO_HD]; omega
    obtain ⟨hEO, hne⟩ := Compile.encodeTape_interior_ne_endMark output hbit_out i hi hi1
    have hlt : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post).length := by rw [htape]; exact hEO
    exact ⟨hlt, by rw [hget_eq i hlt hEO]; exact hne⟩
  -- The bracketed run and trajectory (over the *folded* blocks `sk`/`bd`).
  have hrun := AppendGadget.appendAt_rewind_run (bit + 1) h_ins dst [] sk bd post
    hlen_sk h_pre h_skip_sk hbd_ne hbd_lt hpost_lt h_tp_lt h_t0 h_interior_ne
  have htraj := AppendGadget.appendAt_rewind_no_early_halt (bit + 1) h_ins dst [] sk bd post
    hlen_sk h_pre h_skip_sk hbd_ne hbd_lt hpost_lt h_tp_lt h_t0 h_interior_ne
  -- Rewrite the gadget's count (`HD → L`), start tape (`→ encodeTape s`) and exit
  -- tape (`→ encodeTape output`) into the contract's canonical form.
  rw [hHD_L, hsplit, htape] at hrun
  rw [hHD_L, hsplit] at htraj
  -- The start config = initFlatConfig on `encodeTape s`.
  have hstart0 : (AppendGadget.appendAtThenRewindTM (bit + 1) dst).start = 0 := by
    show (composeFlatTM (AppendGadget.appendAtTM (bit + 1) dst) _ _).start = 0
    rw [composeFlatTM_start, AppendGadget.appendAtTM_start]
  have hinit : initFlatConfig (AppendGadget.appendAtThenRewindTM (bit + 1) dst)
        [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := by
    simp only [initFlatConfig, hstart0, List.map_cons, List.map_nil]
  refine ⟨AppendGadget.appendAt_steps sk bd post + 1
      + (1 + 1 + (Compile.encodeTape s).length), ?_, ?_, ?_⟩
  · rw [hinit]; exact hrun.1
  · intro k hk ck hck
    rw [hinit] at hck
    exact htraj k hk ck hck
  · -- budget: appendAt_steps + 1 + (1 + 1 + L) ≤ 3·L + 6, via `appendAt_steps_le`.
    have hstep_le : AppendGadget.appendAt_steps sk bd post
        ≤ 2 * (Compile.encodeTape s).length + 3 := by
      have hb' := AppendGadget.appendAt_steps_le sk bd post
      have hL : (AppendGadget.regBlocks sk ++ bd ++ 0 :: post).length
          = (Compile.encodeTape s).length := by rw [← hsplit]; simp
      rw [hL] at hb'; exact hb'
    omega

/-! ### ⚠ C2 budget-shape finding — the per-fragment `overhead` budgets are
**too loose to compose** (do not try to prove the four `compile*_sound` lemmas
below as stated).

`compileSeq_sound` (and its `compileIfBit`/`compileForBnd` siblings, and the
`Compile_sound` assembly) take each sub-machine's budget as the **quadratic**
`Compile.overhead (size + cost) = (size + cost + 1)²` and claim the composite
runs within `overhead (size + 1 + cost₁ + cost₂)`. But the composed machine runs
in `t₁ + 1 + t₂` actual steps (`compileSeq_compose_physical`), and a sub-machine
satisfying the hypothesis may take its full budget, so the worst case is

  `overhead(a) + 1 + overhead(a + c₂) ≤ overhead(a + 1 + c₂)`,  `a = size + cost₁`,

which is **false for `a ≥ 2`** (e.g. `a=3, c₂=1`: `42 ≰ 36`; the gap grows with
`a`). A quadratic is not superadditive: summing `~cost` quadratic per-op budgets
gives a **cubic**, not the claimed quadratic-of-the-sum. So these hypotheses are
too weak to imply their conclusions — the lemmas are unprovable *as stated*.

The actual gadgets are **linear** (`AppendGadget.appendAt_steps_le`:
`steps ≤ 2·tapeLen + 3`), and linear per-fragment bounds *do* compose: summing
`~cost` of them over a tape of length `≤ size + cost + regBound`
(`Cmd.size_eval_le` bounds the intermediate sizes) gives
`O(cost · (size + cost + regBound))`, which **is** `O((size+cost)²)` since
`cost ≤ size + cost`. So the correct decomposition is:
  1. per-fragment **linear** step bound `A·tapeLen + B·cost_frag + C` (the
     gadgets prove this; `compileOp_appendOne_sound`/`compileOp_appendZero_sound`
     now carry the linear `2·tapeLen + 3` budget — the four sorried lemmas below
     should be restated to match, using `Cmd.encodeTape_eval_length_le` to cap
     each fragment's tape length);
  2. a **quadratic total** budget for `Compile_run_physical` — but with a
     constant factor / `regBound` term of slack (e.g. `C·(size+cost+regBound)²`
     or a cubic), since the tight `(size+cost+1)²` cannot cover the constants.
     Safe: `toFrameworkWitness'` only needs the total to be `inOPoly`.
The four lemmas below should be **restated with linear per-fragment budgets**
before any proof attempt. See ROADMAP Risk C2 (plan step 1b). -/

/-- Soundness obligation for `compileSeq`, given the IHs for both
sub-machines. **Budget mis-stated** — see the finding block above. -/
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

/-! ### C2 validation: composition under the *physical* per-`Op` contract

The fixed-budget `decodeTape`-equality contract above cannot feed
`composeFlatTM_run` (it lacks the exact halt step, the no-early-halt
trajectory, and the head-`0` exit config). The lemma below is the decisive
check that the **physical** contract — each fragment halts at its `exit`
state with the head rewound to `0` and tape exactly `encodeTape (output)`,
reached at an explicit step `t` with a no-early-halt trajectory — composes
cleanly: with head `0`, `M₁`'s exit config *is* `initFlatConfig M₂ […]`, so
`M₂`'s contract plugs straight into `composeFlatTM_run`'s `h_run2`. It is
additive (the sorry'd `compileSeq_sound` above is left untouched pending the
file-wide contract restatement). See ROADMAP Risk C2. -/
theorem compileSeq_compose_physical
    (r1 r2 : CompiledCmd) (enc1 enc2 : List Nat) {t1 t2 : Nat} {cfg2 : FlatTMConfig}
    (h_sym2 : ∀ v, currentTapeSymbol (([] : List Nat), 0, enc2) = some v → v < 4)
    (h_run1 : runFlatTM t1 r1.M (initFlatConfig r1.M [enc1])
                = some { state_idx := r1.exit, tapes := [([], 0, enc2)] })
    (h_traj1 : ∀ k, k < t1 → ∀ ck,
        runFlatTM k r1.M (initFlatConfig r1.M [enc1]) = some ck →
        ck.state_idx ≠ r1.exit ∧ haltingStateReached r1.M ck = false)
    (h_run2 : runFlatTM t2 r2.M (initFlatConfig r2.M [enc2]) = some cfg2)
    (h_halt2 : haltingStateReached r2.M cfg2 = true) :
    runFlatTM (t1 + 1 + t2) (compileSeq r1 r2).M
        (initFlatConfig (compileSeq r1 r2).M [enc1])
      = some { state_idx := cfg2.state_idx + r1.M.states, tapes := cfg2.tapes } ∧
    haltingStateReached (compileSeq r1 r2).M
      { state_idx := cfg2.state_idx + r1.M.states, tapes := cfg2.tapes } = true := by
  have h_cfg0_state_lt :
      (initFlatConfig r1.M [enc1]).state_idx < r1.M.states := r1.M_valid.1
  have h_sym_bound :
      ∀ v, currentTapeSymbol (([] : List Nat), 0, enc2) = some v →
        v < max r1.M.sig r2.M.sig := by
    intro v hv
    rw [r1.M_sig, r2.M_sig]
    exact h_sym2 v hv
  exact composeFlatTM_run (M₁ := r1.M) (M₂ := r2.M) (exit := r1.exit)
    r1.M_valid r2.M_valid r1.exit_lt
    (initFlatConfig r1.M [enc1]) h_cfg0_state_lt
    [] 0 enc2 h_sym_bound h_run1 h_traj1 h_run2 h_halt2

/-! ### Physical-contract restated composition lemmas (Risk C2, step 1b-3)

The original `compileSeq_sound` / `compileIfBit_sound` / `compileForBnd_sound` /
`Compile_sound` are stated with the **quadratic** `Compile.overhead` per-fragment
budget — which is **unprovable** because quadratic budgets don't compose additively
(see the budget-shape finding above). The lemmas below restate every composition
combinator with the **physical** per-fragment contract: each sub-machine

  (1) halts at `exit` with head `0` and tape `= encodeTape output`,
  (2) has a no-early-halt trajectory,
  (3) satisfies a **linear** step budget `t ≤ A * tapeLen + B`.

Linear budgets compose: the composed machine runs in `t₁ + 1 + t₂` steps
(`compileSeq_compose_physical`), and bounding each `tᵢ` linearly in the tape
length at its entry gives a sum that telescopes into a quadratic total.

These restated lemmas are the **correct** decomposition for proving
`Compile_run_physical` by induction on `Cmd`. -/

/-- An `Op` is in-bounds with respect to a state when all its register operands
are valid indices. Needed because the TM must physically navigate to each
register. -/
def Op.inBounds (o : Op) (s : State) : Prop :=
  match o with
  | .clear dst | .appendOne dst | .appendZero dst => dst < s.length
  | .copy dst src | .tail dst src | .head dst src | .nonEmpty dst src =>
      dst < s.length ∧ src < s.length
  | .eqBit dst src1 src2 => dst < s.length ∧ src1 < s.length ∧ src2 < s.length
  | .takeAt dst src lenReg | .dropAt dst src lenReg | .consLen dst lenReg src =>
      dst < s.length ∧ src < s.length ∧ lenReg < s.length
  | .concat dst src1 src2 => dst < s.length ∧ src1 < s.length ∧ src2 < s.length

/-- **Risk C2 finding (machine-checked): the exact-tape physical contract is
unsatisfiable for length-decreasing ops.** No `FlatTM`, in any number of steps,
can run from `encodeTape s` to a configuration whose tape is *exactly*
`encodeTape (Op.eval (.clear dst) s)` when register `dst` is non-empty — because
the physical tape never shrinks (`runFlatTM_initFlatConfig_no_shrink`) yet
clearing a non-empty register *shortens* the encoded tape. Concrete witness
`s = [[1]]`, `dst = 0`: `encodeTape [[1]]` has length `4`, but
`encodeTape (clear 0 ↦ [[]])` has length `3`.

This is the obstruction behind `compileOp_sound_physical` (below): it **cannot**
be proved for `clear` / `tail` / shrinking `copy` / `head` / `eqBit` /
`nonEmpty` / the length ops as stated, since each can shorten the tape. Only
`appendOne` / `appendZero` (which purely grow it) fit the exact-tape contract.
See `Complexity/Complexity/TapeMono.lean` and ROADMAP Risk C2 for the resolution
(a residue-tolerant contract `encodeTape output ++ filler` + a left-shift delete
gadget). -/
theorem Compile.clear_physical_unsatisfiable (M : FlatTM) (n q : Nat) :
    runFlatTM n M (initFlatConfig M [Compile.encodeTape [[1]]])
      ≠ some { state_idx := q,
               tapes := [([], 0, Compile.encodeTape (Op.eval (Op.clear 0) [[1]]))] } := by
  intro h
  have hno : (Compile.encodeTape [[1]]).length
      ≤ (Compile.encodeTape (Op.eval (Op.clear 0) [[1]])).length :=
    runFlatTM_initFlatConfig_no_shrink M n (Compile.encodeTape [[1]]) _ _ h rfl
  have hin : (Compile.encodeTape [[1]]).length = 4 := by
    rw [Compile.encodeTape_length]; decide
  have hout : (Compile.encodeTape (Op.eval (Op.clear 0) [[1]])).length = 3 := by
    rw [Compile.encodeTape_length]; decide
  rw [hin, hout] at hno
  omega

theorem compileOp_sound_physical (o : Op) (s : State)
    (hbit : Compile.BitState s) (hbnd : o.inBounds s) :
    ∃ t : Nat,
      runFlatTM t (compileOp o).M
          (initFlatConfig (compileOp o).M [Compile.encodeTape s])
        = some { state_idx := (compileOp o).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval o s))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (compileOp o).M
              (initFlatConfig (compileOp o).M [Compile.encodeTape s]) = some ck →
          ck.state_idx ≠ (compileOp o).exit ∧
          haltingStateReached (compileOp o).M ck = false)
      ∧ t ≤ 3 * (Compile.encodeTape s).length + 6 := by
  sorry  -- TODO(C2, step 1c): case-split on `o`; the `appendOne`/`appendZero`
         -- cases follow from `appendBit_physical`; the remaining 10 ops need
         -- their gadgets concretised first (each with its `*_physical` contract).

/-- **Physical-contract `compileSeq` composition (PROVEN).** Given two
sub-machines each satisfying the physical contract (head-`0` exit, exact tape,
trajectory), `compileSeq r1 r2` satisfies it with additive budget `t₁ + 1 + t₂`.
This is the proved instance of `compileSeq_compose_physical` lifted to the
`CompiledCmd` level.

The head-`0` exit of `r1` makes its exit config literally equal to
`initFlatConfig r2.M [enc_output₁]`, so `r2`'s physical contract plugs
straight in. -/
theorem compileSeq_sound_physical
    (r1 r2 : CompiledCmd) (s mid final : State)
    (hbit_s : Compile.BitState s)
    (hbit_mid : Compile.BitState mid)
    {t1 t2 : Nat}
    (h_run1 : runFlatTM t1 r1.M (initFlatConfig r1.M [Compile.encodeTape s])
                = some { state_idx := r1.exit,
                         tapes := [([], 0, Compile.encodeTape mid)] })
    (h_traj1 : ∀ k, k < t1 → ∀ ck,
        runFlatTM k r1.M (initFlatConfig r1.M [Compile.encodeTape s]) = some ck →
        ck.state_idx ≠ r1.exit ∧ haltingStateReached r1.M ck = false)
    (h_run2 : runFlatTM t2 r2.M (initFlatConfig r2.M [Compile.encodeTape mid])
                = some { state_idx := r2.exit,
                         tapes := [([], 0, Compile.encodeTape final)] })
    (h_traj2 : ∀ k, k < t2 → ∀ ck,
        runFlatTM k r2.M (initFlatConfig r2.M [Compile.encodeTape mid]) = some ck →
        ck.state_idx ≠ r2.exit ∧ haltingStateReached r2.M ck = false)
    (h_halt2 : haltingStateReached r2.M
        { state_idx := r2.exit,
          tapes := [([], 0, Compile.encodeTape final)] } = true) :
    runFlatTM (t1 + 1 + t2) (compileSeq r1 r2).M
        (initFlatConfig (compileSeq r1 r2).M [Compile.encodeTape s])
      = some { state_idx := (compileSeq r1 r2).exit,
               tapes := [([], 0, Compile.encodeTape final)] } ∧
    haltingStateReached (compileSeq r1 r2).M
      { state_idx := (compileSeq r1 r2).exit,
        tapes := [([], 0, Compile.encodeTape final)] } = true := by
  -- The head-0 exit of r1 makes its config = initFlatConfig r2 [encodeTape mid].
  -- Feed into the already-proven `compileSeq_compose_physical`.
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape mid)
      = some v → v < 4 := by
    intro v hv
    simp only [currentTapeSymbol] at hv
    split at hv
    case isTrue h =>
      rw [Option.some.injEq] at hv; subst hv
      exact Compile.encodeTape_lt_four mid hbit_mid _
        (List.getElem_mem h)
    case isFalse => exact absurd hv (by simp)
  -- `compileSeq_compose_physical` produces `cfg2.state_idx + r1.M.states` where
  -- `cfg2 = { state_idx := r2.exit, … }`, giving `r2.exit + r1.M.states`.
  -- Our conclusion uses `(compileSeq r1 r2).exit = r1.M.states + r2.exit`.
  have key := compileSeq_compose_physical r1 r2 (Compile.encodeTape s) (Compile.encodeTape mid)
    h_sym h_run1 h_traj1 h_run2 h_halt2
  -- key : runFlatTM … = some { state_idx := r2.exit + r1.M.states, … } ∧ …
  -- goal : … (compileSeq r1 r2).exit = r1.M.states + r2.exit …
  rw [show (compileSeq r1 r2).exit = r2.exit + r1.M.states from Nat.add_comm ..]
  exact key

/-- **Physical-contract trajectory for `compileSeq` (PROVEN).** If both
sub-machines never halt before their exit, neither does the composition. -/
theorem compileSeq_traj_physical
    (r1 r2 : CompiledCmd) (s mid : State)
    (hbit_mid : Compile.BitState mid)
    {t1 t2 : Nat}
    (h_run1 : runFlatTM t1 r1.M (initFlatConfig r1.M [Compile.encodeTape s])
                = some { state_idx := r1.exit,
                         tapes := [([], 0, Compile.encodeTape mid)] })
    (h_traj1 : ∀ k, k < t1 → ∀ ck,
        runFlatTM k r1.M (initFlatConfig r1.M [Compile.encodeTape s]) = some ck →
        ck.state_idx ≠ r1.exit ∧ haltingStateReached r1.M ck = false)
    (h_traj2 : ∀ k, k < t2 → ∀ ck,
        runFlatTM k r2.M (initFlatConfig r2.M [Compile.encodeTape mid]) = some ck →
        ck.state_idx ≠ r2.exit ∧ haltingStateReached r2.M ck = false) :
    ∀ k, k < t1 + 1 + t2 → ∀ ck,
      runFlatTM k (compileSeq r1 r2).M
          (initFlatConfig (compileSeq r1 r2).M [Compile.encodeTape s]) = some ck →
      ck.state_idx ≠ (compileSeq r1 r2).exit ∧
      haltingStateReached (compileSeq r1 r2).M ck = false := by
  -- Use `composeFlatTM_no_early_halt` for `haltingStateReached = false`,
  -- then derive `state_idx ≠ exit` from `exit_is_halt` + `halt_unique`.
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape mid)
      = some v → v < max r1.M.sig r2.M.sig := by
    intro v hv
    rw [r1.M_sig, r2.M_sig]
    simp only [currentTapeSymbol] at hv
    split at hv
    case isTrue h =>
      rw [Option.some.injEq] at hv; subst hv
      exact Compile.encodeTape_lt_four mid hbit_mid _
        (List.getElem_mem h)
    case isFalse => exact absurd hv (by simp)
  have h_traj2' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k r2.M { state_idx := r2.M.start, tapes := [([], 0, Compile.encodeTape mid)] }
        = some ck → haltingStateReached r2.M ck = false := by
    intro k hk ck hck
    exact (h_traj2 k hk ck hck).2
  have h_nohalt := composeFlatTM_no_early_halt r1.M_valid r2.M_valid r1.exit_lt
    (initFlatConfig r1.M [Compile.encodeTape s]) r1.M_valid.1
    [] 0 (Compile.encodeTape mid) h_sym h_run1 h_traj1 h_traj2'
  -- h_nohalt : ∀ k < …, … haltingStateReached (composeFlatTM r1.M r2.M r1.exit) ck = false
  -- The goal's `(compileSeq r1 r2).M` = `composeFlatTM r1.M r2.M r1.exit` by definition,
  -- and `(compileSeq r1 r2).exit` = `r1.M.states + r2.exit`. Both unfold by `dsimp [compileSeq]`.
  intro k hk ck hck
  constructor
  · -- `state_idx ≠ exit`: if equal, `exit_is_halt` makes `haltingStateReached = true`.
    intro heq
    have hnh : haltingStateReached (compileSeq r1 r2).M ck = false :=
      h_nohalt k hk ck hck
    -- `exit_is_halt : M.halt[exit]? = some true`
    -- `haltingStateReached M ck = M.halt.getD ck.state_idx false`
    -- With heq, getD exit false = (some true).getD false = true.
    have hh : haltingStateReached (compileSeq r1 r2).M ck = true := by
      show (compileSeq r1 r2).M.halt.getD ck.state_idx false = true
      rw [heq]
      -- Now: (compileSeq r1 r2).M.halt.getD (compileSeq r1 r2).exit false = true
      -- This follows from exit_is_halt.
      have := (compileSeq r1 r2).exit_is_halt
      -- this : (compileSeq r1 r2).M.halt[(compileSeq r1 r2).exit]? = some true
      simp only [List.getD, this, Option.getD]
    rw [hh] at hnh
    exact absurd hnh Bool.noConfusion
  · exact h_nohalt k hk ck hck

/-- **Physical-contract `compileIfBit` (sorry'd, step 1b-3).** Given two
branches each satisfying the physical contract, `compileIfBit t rT rE` satisfies
it for the taken branch, with the tester's overhead `+1` steps added.

The tester (`bitTestTM`-derived) reads register `t`'s first symbol (2 steps past
the leading sentinel), then bridges to the chosen branch. The branch's physical
contract starts from head `0` (the tester exits at head `1`, but
`joinTwoHalts` + the rewind bracket brings the head back). -/
theorem compileIfBit_sound_physical
    (t : Var) (rT rE : CompiledCmd)
    (evalT evalE : State → State)
    (hbit : ∀ s : State, Compile.BitState s → Compile.BitState (evalT s))
    (hbit' : ∀ s : State, Compile.BitState s → Compile.BitState (evalE s))
    {budgetT budgetE : State → Nat}
    (hT : ∀ s, Compile.BitState s →
      ∃ t : Nat,
        runFlatTM t rT.M (initFlatConfig rT.M [Compile.encodeTape s])
          = some { state_idx := rT.exit,
                   tapes := [([], 0, Compile.encodeTape (evalT s))] }
        ∧ (∀ k, k < t → ∀ ck,
            runFlatTM k rT.M (initFlatConfig rT.M [Compile.encodeTape s]) = some ck →
            ck.state_idx ≠ rT.exit ∧ haltingStateReached rT.M ck = false)
        ∧ t ≤ budgetT s)
    (hE : ∀ s, Compile.BitState s →
      ∃ t : Nat,
        runFlatTM t rE.M (initFlatConfig rE.M [Compile.encodeTape s])
          = some { state_idx := rE.exit,
                   tapes := [([], 0, Compile.encodeTape (evalE s))] }
        ∧ (∀ k, k < t → ∀ ck,
            runFlatTM k rE.M (initFlatConfig rE.M [Compile.encodeTape s]) = some ck →
            ck.state_idx ≠ rE.exit ∧ haltingStateReached rE.M ck = false)
        ∧ t ≤ budgetE s)
    (s : State) (hbs : Compile.BitState s) :
    let chosen := if s.get t = [1] then evalT s else evalE s
    let chosenBudget := if s.get t = [1] then budgetT s else budgetE s
    ∃ t : Nat,
      runFlatTM t (compileIfBit t rT rE).M
          (initFlatConfig (compileIfBit t rT rE).M [Compile.encodeTape s])
        = some { state_idx := (compileIfBit t rT rE).exit,
                 tapes := [([], 0, Compile.encodeTape chosen)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (compileIfBit t rT rE).M
              (initFlatConfig (compileIfBit t rT rE).M [Compile.encodeTape s]) = some ck →
          ck.state_idx ≠ (compileIfBit t rT rE).exit ∧
          haltingStateReached (compileIfBit t rT rE).M ck = false)
      ∧ t ≤ chosenBudget + 3 := by
  sorry  -- TODO(C2, step 1b-3): use `branchComposeFlatTM_run` + `joinTwoHalts`.
         -- The tester reads 2 steps (past sentinel + answer bit), bridges 1 step,
         -- then the branch's physical contract runs. The +3 covers tester + bridge.

/-- **Physical-contract `compileForBnd` (sorry'd, step 1b-3).** Given a loop body
satisfying the physical contract, `compileForBnd counter bound rbody` satisfies
it with the iterated body's budget summed over iterations.

The construction uses `loopTM` (already proven in `TMPrimitives.lean`). Each
iteration: (1) write the counter value to register `counter`, (2) run the body,
(3) decrement/check the bound. The bound-length read is `O(bound_len)` steps;
counter-write is `O(counter_val)` per iteration. The total budget is the sum
of per-iteration budgets plus the loop overhead. -/
theorem compileForBnd_sound_physical
    (counter bound : Var)
    (rbody : CompiledCmd)
    (evalBody : State → State)
    (hbit_body : ∀ s : State, Compile.BitState s → Compile.BitState (evalBody s))
    {budgetBody : State → Nat}
    (hb : ∀ s, Compile.BitState s →
      ∃ t : Nat,
        runFlatTM t rbody.M (initFlatConfig rbody.M [Compile.encodeTape s])
          = some { state_idx := rbody.exit,
                   tapes := [([], 0, Compile.encodeTape (evalBody s))] }
        ∧ (∀ k, k < t → ∀ ck,
            runFlatTM k rbody.M (initFlatConfig rbody.M [Compile.encodeTape s]) = some ck →
            ck.state_idx ≠ rbody.exit ∧ haltingStateReached rbody.M ck = false)
        ∧ t ≤ budgetBody s)
    (s : State) (hbs : Compile.BitState s) :
    let iters := (s.get bound).length
    let folded := (List.range iters).foldl
      (fun acc i =>
        let s' := acc.1.set counter (List.replicate i 1)
        (evalBody s', acc.2 + budgetBody s'))
      (s, 0)
    ∃ t : Nat,
      runFlatTM t (compileForBnd counter bound rbody).M
          (initFlatConfig (compileForBnd counter bound rbody).M [Compile.encodeTape s])
        = some { state_idx := (compileForBnd counter bound rbody).exit,
                 tapes := [([], 0, Compile.encodeTape folded.1)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (compileForBnd counter bound rbody).M
              (initFlatConfig (compileForBnd counter bound rbody).M
                [Compile.encodeTape s]) = some ck →
          ck.state_idx ≠ (compileForBnd counter bound rbody).exit ∧
          haltingStateReached (compileForBnd counter bound rbody).M ck = false)
      ∧ t ≤ folded.2 + 3 * iters + 3 := by
  sorry  -- TODO(C2, step 1b-3): use `loopTM_run` with the body's physical contract.
         -- Each iteration: counter-write (O(i) steps) + body run (budgetBody steps).
         -- Total: Σ budgetBody_i + loop overhead.

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
polynomial step bound. Follows from `Compile_sound` by padding the
per-state budget `overhead (size + cost)` up to the polynomial
`overhead (size + costBound size)`. -/
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
  refine ⟨fun n => Compile.overhead (n + costBound n), ?_, ?_, ?_⟩
  · -- `inOPoly`: composition of `(· + costBound ·)` with `overhead`.
    have hinner : inOPoly (fun n => n + costBound n) := inOPoly_add inOPoly_id h_poly
    show inOPoly (Compile.overhead ∘ fun n => n + costBound n)
    exact inOPoly_comp hinner Compile.overhead_poly
  · -- `monotonic`: composition.
    intro a b hab
    have h1 : costBound a ≤ costBound b := h_mono a b hab
    exact Compile.overhead_mono _ _ (by omega)
  · -- For each `s`, pad the `Compile_sound` budget up to the bound.
    intro s
    obtain ⟨cfg, hrun, hhalt, hdec⟩ := Compile_sound c s
    refine ⟨cfg, ?_, hhalt, hdec⟩
    have hle : Compile.overhead (State.size s + c.cost s)
        ≤ Compile.overhead (State.size s + costBound (State.size s)) :=
      Compile.overhead_mono _ _ (by have := h_bound s; omega)
    obtain ⟨k, hk⟩ := Nat.le.dest hle
    show runFlatTM (Compile.overhead (State.size s + costBound (State.size s)))
        (Compile c) (initFlatConfig (Compile c) [Compile.encodeTape s]) = some cfg
    rw [← hk]
    exact runFlatTM_extend hrun hhalt

/-- The exit state is a valid state of the compiled machine. -/
theorem Compile_exit_lt (c : Cmd) : Compile.exit c < (Compile c).states :=
  (compileCmd c).exit_lt

/-! ## C6 — the tape→state bit-test gadget (`DecidesLang' → DecidesBy` bridge)

`Compile c` always halts in its single `exit` state with the answer written on
the **tape** (register `0` = `[1]` accept / `[0]` reject). `DecidesBy` instead
reads its answer from the **state index** (`acceptState` / `rejectState`). The
gap is closed by composing `Compile c` with a tiny gadget that reads the tape's
first symbol — `2` (shifted `1`, accept) or `1` (shifted `0`, reject), per the
`encodeTape` format — and halts in a *distinct* state for each.

This gadget and its run lemmas depend **only** on the encoding format, not on
`Compile_sound` / the physical run contract, so they are isolable and
`sorry`-free. -/

/-- The bit-test gadget: a single-tape, 4-symbol, 4-state `FlatTM`. The encoded
tape begins with the leading sentinel `endMark = 3`, so from the (non-halting)
start state `0` the gadget reads `3` and **steps right** past the sentinel into
state `3`; there, reading the answer bit `2` jumps to the halting state `1`
(accept) and `1` jumps to the halting state `2` (reject), without further
movement. -/
def Compile.bitTestTM : FlatTM where
  sig := 4
  tapes := 1
  states := 4
  trans :=
    [ { src_state := 0, src_tape_vals := [some 3], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] },
      { src_state := 3, src_tape_vals := [some 2], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] },
      { src_state := 3, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] } ]
  start := 0
  halt := [false, true, true, false]

theorem Compile.bitTestTM_valid : validFlatTM Compile.bitTestTM := by
  refine ⟨by decide, rfl, ?_⟩
  intro entry hentry
  have hmem : entry ∈
      [ ({ src_state := 0, src_tape_vals := [some 3], dst_state := 3,
           dst_write_vals := [none], move_dirs := [TMMove.Rmove] } : FlatTMTransEntry),
        { src_state := 3, src_tape_vals := [some 2], dst_state := 1,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] },
        { src_state := 3, src_tape_vals := [some 1], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } ] := hentry
  have hbound3 : flatTMOptionSymbolsBounded 4 [some 3] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide
  have hbound2 : flatTMOptionSymbolsBounded 4 [some 2] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide
  have hbound1 : flatTMOptionSymbolsBounded 4 [some 1] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide
  have hboundNone : flatTMOptionSymbolsBounded 4 [none] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; trivial
  rcases List.mem_cons.mp hmem with h | hmem
  · subst h; exact ⟨by decide, by decide, rfl, rfl, rfl, hbound3, hboundNone⟩
  · rcases List.mem_cons.mp hmem with h | hmem
    · subst h; exact ⟨by decide, by decide, rfl, rfl, rfl, hbound2, hboundNone⟩
    · rcases List.mem_cons.mp hmem with h | h
      · subst h; exact ⟨by decide, by decide, rfl, rfl, rfl, hbound1, hboundNone⟩
      · simp at h

theorem Compile.bitTestTM_tapes : Compile.bitTestTM.tapes = 1 := rfl

theorem Compile.bitTestTM_sig : Compile.bitTestTM.sig = 4 := rfl

theorem Compile.bitTestTM_start : Compile.bitTestTM.start = 0 := rfl

/-- After the leading sentinel `3`, reading the answer `2` (accept) halts the
gadget in state `1` in two steps (one to step past the sentinel). -/
theorem Compile.bitTestTM_run_two (left rest : List Nat) :
    runFlatTM 2 Compile.bitTestTM { state_idx := 0, tapes := [(left, 0, 3 :: 2 :: rest)] }
      = some { state_idx := 1, tapes := [(left, 1, 3 :: 2 :: rest)] } := rfl

/-- After the leading sentinel `3`, reading the answer `1` (reject) halts the
gadget in state `2` in two steps. -/
theorem Compile.bitTestTM_run_one (left rest : List Nat) :
    runFlatTM 2 Compile.bitTestTM { state_idx := 0, tapes := [(left, 0, 3 :: 1 :: rest)] }
      = some { state_idx := 2, tapes := [(left, 1, 3 :: 1 :: rest)] } := rfl

/-- State `1` (accept) and state `2` (reject) are both halting states. -/
theorem Compile.bitTestTM_halt_one : Compile.bitTestTM.halt.getD 1 false = true := rfl
theorem Compile.bitTestTM_halt_two : Compile.bitTestTM.halt.getD 2 false = true := rfl

/-! ## The physical run contract of `Compile` (Risk C2)

`Compile_sound` (above) only states `decodeTape cfg = c.eval s`: it pins down
neither the head position nor the exact tape, nor the halt step / no-early-halt
trajectory. None of that is enough to *compose* `Compile c` with the bit-test
gadget via `composeFlatTM_run`, which needs the explicit exit configuration and
the trajectory (`compileSeq_compose_physical` documents exactly this gap).

The lemma below states the compiler's intended **physical contract** (ROADMAP
Risk C2): `Compile c` reaches its `exit` state at an explicit step `t`, with the
head rewound to `0` and the tape exactly `encodeTape (c.eval s)`, never halting
or hitting `exit` earlier, within the `overhead` budget. It is the top-level
restatement of the per-fragment physical contract whose composition
`compileSeq_compose_physical` already validates; discharging it is the remaining
C1/C2 compiler-engineering obligation (the same gap `Compile_sound` sits behind),
so it is left as a single, focused `sorry`.

⚠ **Prerequisite (2026-05-29): the "head rewound to `0`" clause is not
implementable on the current encoding.** `composeFlatTM_run` preserves the head
across the seam (it does not reset it), so each fragment must rewind itself; but
a TM head clamps at `0` under `Lmove` without being able to *detect* it, so
rewinding needs a uniquely-detectable left sentinel at index `0` that
`encodeTape` (= `encodeRegs s ++ [endMark]`) lacks. The rewind itself is ready
(`ScanLeft.rewindToStart_run`/`_traj`). **Before discharging this `sorry`,
migrate to the leading-sentinel encoding** `encodeTape s = endMark ::
encodeRegs s ++ [endMark]` (reuse `3`, `sig` stays `4`) — full steps in
HANDOFF.md "Recommended next step" (1b-0 … 1d). -/
theorem Compile_run_physical (c : Cmd) (s : State) :
    ∃ t : Nat,
      runFlatTM t (Compile c) (initFlatConfig (Compile c) [Compile.encodeTape s])
          = some { state_idx := Compile.exit c,
                   tapes := [([], 0, Compile.encodeTape (c.eval s))] } ∧
      (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile c)
              (initFlatConfig (Compile c) [Compile.encodeTape s]) = some ck →
          ck.state_idx ≠ Compile.exit c ∧
          haltingStateReached (Compile c) ck = false) ∧
      t ≤ Compile.overhead (State.size s + c.cost s) := by
  sorry  -- TODO(C2): the physical compiler contract; composes per-fragment
         -- via `compileSeq_compose_physical`, gated on the per-`Op` gadgets.

/-- The compiled decider machine: run `Compile c`, then the bit-test gadget. The
gadget converts register `0`'s answer (on the tape) into a distinct halting
*state*, as `DecidesBy` requires. -/
def Compile.bitDeciderTM (c : Cmd) : FlatTM :=
  composeFlatTM (Compile c) Compile.bitTestTM (Compile.exit c)

theorem Compile.bitDeciderTM_valid (c : Cmd) : validFlatTM (Compile.bitDeciderTM c) :=
  composeFlatTM_valid (Compile c) Compile.bitTestTM (Compile.exit c)
    (Compile_valid c) Compile.bitTestTM_valid (Compile_exit_lt c)
    (Compile_tapes c) Compile.bitTestTM_tapes

theorem Compile.bitDeciderTM_tapes (c : Cmd) : (Compile.bitDeciderTM c).tapes = 1 := by
  show (composeFlatTM (Compile c) Compile.bitTestTM (Compile.exit c)).tapes = 1
  rw [composeFlatTM_tapes, Compile_tapes]

/-- The canonical single-register tape `encodeTape [r]` has length `r.length + 3`
(the leading sentinel, the shifted register, the `0` delimiter, and the trailing
`endMark`). Used to bound the `DecidesBy.encode_size` of the canonical decider
bridge. -/
theorem Compile.encodeTape_singleton_length (r : List Nat) :
    (Compile.encodeTape [r]).length = r.length + 3 := by
  simp [Compile.encodeTape, Compile.encodeRegs, Compile.shiftReg]

/-- **C6 headline.** Running `bitDeciderTM c` on `encodeTape s` halts, within
`overhead (size s + cost s) + 3` steps, in state `1 + (Compile c).states` when
register `0` of `c.eval s` is `[1]` (accept) and `2 + (Compile c).states` when
it is `[0]` (reject). Combines the physical run contract of `Compile c` with the
`sorry`-free gadget run lemma, via `composeFlatTM_run`. (The `+3` is one bridge
step plus the two gadget steps — step past the leading sentinel, then read.) -/
theorem Compile.bitDecider_run (c : Cmd) (s : State) (b : Nat)
    (hbit : b = 0 ∨ b = 1) (h0 : (c.eval s).get 0 = [b]) :
    ∃ cfg,
      runFlatTM (Compile.overhead (State.size s + c.cost s) + 3) (Compile.bitDeciderTM c)
          (initFlatConfig (Compile.bitDeciderTM c) [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (Compile.bitDeciderTM c) cfg = true ∧
      cfg.state_idx = (if b = 1 then 1 else 2) + (Compile c).states := by
  obtain ⟨tl, htl⟩ := Compile.encodeTape_eq_cons_of_get_zero (c.eval s) b h0
  obtain ⟨t1, hrun1, htraj1, ht1⟩ := Compile_run_physical c s
  -- Rewrite the physical exit tape via the encoding lemma (leading sentinel).
  rw [htl] at hrun1
  -- The gadget's exit state for this bit.
  set dst : Nat := if b = 1 then 1 else 2 with hdst
  -- Gadget run + halt (split on the bit): step past the sentinel `3`, then read.
  have hrun2 : runFlatTM 2 Compile.bitTestTM
      { state_idx := Compile.bitTestTM.start,
        tapes := [([], 0, Compile.endMark :: (b + 1) :: tl)] }
      = some { state_idx := dst, tapes := [([], 1, Compile.endMark :: (b + 1) :: tl)] } := by
    rcases hbit with hb | hb <;> subst hb <;>
      simp only [Compile.bitTestTM_start, hdst] <;> rfl
  have hhalt2 : haltingStateReached Compile.bitTestTM
      { state_idx := dst, tapes := [([], 1, Compile.endMark :: (b + 1) :: tl)] } = true := by
    rcases hbit with hb | hb <;> subst hb <;> rfl
  -- The first tape symbol is the leading sentinel `endMark = 3 < 4`.
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.endMark :: (b + 1) :: tl)
      = some v → v < max (Compile c).sig Compile.bitTestTM.sig := by
    intro v hv
    have : v = Compile.endMark := by simpa [currentTapeSymbol] using hv.symm
    subst this
    rw [Compile_sig, Compile.bitTestTM_sig]
    decide
  have hstate0 : (initFlatConfig (Compile c) [Compile.encodeTape s]).state_idx
      < (Compile c).states := (Compile_valid c).1
  -- Compose.
  have hcomp := composeFlatTM_run (M₁ := Compile c) (M₂ := Compile.bitTestTM)
    (exit := Compile.exit c) (Compile_valid c) Compile.bitTestTM_valid
    (Compile_exit_lt c)
    (initFlatConfig (Compile c) [Compile.encodeTape s]) hstate0
    [] 0 (Compile.endMark :: (b + 1) :: tl) hsym hrun1 htraj1 hrun2 hhalt2
  obtain ⟨hcrun, hchalt⟩ := hcomp
  -- Pad the run up to the stated budget.
  obtain ⟨k, hk⟩ := Nat.le.dest ht1
  refine ⟨{ state_idx := dst + (Compile c).states,
            tapes := [([], 1, Compile.endMark :: (b + 1) :: tl)] }, ?_, ?_, ?_⟩
  · show runFlatTM (Compile.overhead (State.size s + c.cost s) + 3) (Compile.bitDeciderTM c)
        (initFlatConfig (Compile.bitDeciderTM c) [Compile.encodeTape s]) = _
    have hbudget : Compile.overhead (State.size s + c.cost s) + 3 = (t1 + 1 + 2) + k := by omega
    rw [hbudget]
    exact runFlatTM_extend (M := Compile.bitDeciderTM c) hcrun hchalt
  · exact hchalt
  · show dst + (Compile c).states = (if b = 1 then 1 else 2) + (Compile c).states
    rw [hdst]

/-- Halt bits of `bitDeciderTM` past `(Compile c).states` are exactly the
gadget's: the composed halt vector is `replicate (Compile c).states false ++
bitTestTM.halt`. Gives the two accept/reject states' `halting_*` obligations. -/
theorem Compile.bitDeciderTM_halt_shift (c : Cmd) (i : Nat) :
    (Compile.bitDeciderTM c).halt.getD (i + (Compile c).states) false
      = Compile.bitTestTM.halt.getD i false := by
  show (composedHalt (Compile c) Compile.bitTestTM).getD (i + (Compile c).states) false
      = Compile.bitTestTM.halt.getD i false
  rw [composedHalt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [List.length_replicate]; exact Nat.le_add_left _ _),
      List.length_replicate, Nat.add_sub_cancel]

end Complexity.Lang
