import Complexity.Lang.Semantics
import Complexity.Lang.AppendGadget
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

/-- Encode a `State` as a flat tape: the registers (`encodeRegs`)
followed by the end-of-tape terminator `endMark`. -/
def Compile.encodeTape (s : State) : List Nat :=
  Compile.encodeRegs s ++ [Compile.endMark]

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

/-- **Tape length = contents + register count + 1.** The encoded tape is the
registers (`State.size s + s.length` cells) plus the `endMark`. This is the link
between the per-op gadget step bounds (which grow with the *tape length*) and the
`State.size` / register-count bounds (`Cmd.size_eval_le` / `Cmd.eval_length_le`)
— so the intermediate tape length during a `Compile` run is bounded linearly in
`size + cost + regBound`. -/
theorem Compile.encodeTape_length (s : State) :
    (Compile.encodeTape s).length = State.size s + s.length + 1 := by
  rw [Compile.encodeTape, List.length_append, Compile.encodeRegs_length]; rfl

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
      let content := flat.takeWhile (· != Compile.endMark)
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
          ((Compile.flattenTape (([] : List Nat), (0 : Nat), Compile.encodeTape s)).takeWhile
            (· != Compile.endMark)))).map Compile.unshiftReg = s
  rw [show Compile.flattenTape (([] : List Nat), (0 : Nat), Compile.encodeTape s)
        = Compile.encodeTape s from rfl,
      show Compile.encodeTape s = Compile.encodeRegs s ++ [Compile.endMark] from rfl,
      Compile.takeWhile_no_endMark _ (Compile.encodeRegs_no_endMark s h),
      Compile.splitOnZero_encodeRegs, Compile.dropTrailingEmpty_append_nil,
      Compile.map_unshift_shift]

/-- The first symbol of the encoded tape is `shiftReg`-ed register `0`. When
register `0` holds a single bit `b` (the decider answer convention — `[1]` for
accept, `[0]` for reject), the encoded tape begins with `b + 1`. This is the
only fact the tape→state bit-test gadget needs about the encoding. -/
theorem Compile.encodeTape_eq_cons_of_get_zero (s : State) (b : Nat)
    (h : s.get 0 = [b]) :
    ∃ tl, Compile.encodeTape s = (b + 1) :: tl := by
  cases s with
  | nil => simp [State.get] at h
  | cons r0 rest =>
      have hr0 : r0 = [b] := by simpa [State.get] using h
      refine ⟨[0] ++ Compile.encodeRegs rest ++ [Compile.endMark], ?_⟩
      show Compile.encodeRegs (r0 :: rest) ++ [Compile.endMark]
          = (b + 1) :: ([0] ++ Compile.encodeRegs rest ++ [Compile.endMark])
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

/-! ### C1/C2 integration probe — behavioural soundness of `appendOne`

`compileOp_sound` above is sorry-bodied for *all* ops and demands the
**exact** budget `Compile.overhead (size + 1)`. The proven gadget library
(`AppendGadget.appendAt_run`, …) establishes the *tape transformation* but
deliberately leaves the step count **existential** ("a step bound is a
separate concern").

`compileOp_appendOne_behavioural` below closes the **behavioural** half
end-to-end for `appendOne`: running `Compile.opAppendOne dst` on
`Compile.encodeTape s` halts with a tape that `Compile.decodeTape`s back to
`Op.eval (appendOne dst) s`. This is the first end-to-end demonstration that
the compiler's single-tape `encodeTape`/`decodeTape` contract and the gadget
library actually compose — the key untested seam of Risk C2. It shows the
residual per-op obligation is **purely the step bound** (i.e. replacing the
`∃ steps` here by the fixed `Compile.overhead (size + 1)` budget — the
cost-accounting that the gadget run-lemmas do not yet provide). -/

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

/-- The encoded tape of `s` splits at register `dst` into the preceding
register blocks, the target register's shifted contents, its delimiter, and
the rest — exactly the shape `AppendGadget.appendAt_run` consumes (with empty
prefix). -/
private theorem Compile.encodeTape_split (s : State) (dst : Var) (h : dst < s.length) :
    AppendGadget.regBlocks ((s.take dst).map Compile.shiftReg)
        ++ Compile.shiftReg (s.get dst)
        ++ 0 :: (Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark])
      = Compile.encodeTape s := by
  have hget : s.get dst = s[dst] := by
    rw [State.get, List.getElem?_eq_getElem h]; rfl
  have hs : Compile.encodeRegs s
      = Compile.encodeRegs (s.take dst) ++ Compile.shiftReg s[dst]
          ++ [0] ++ Compile.encodeRegs (s.drop (dst + 1)) := by
    conv_lhs => rw [Compile.list_eq_take_getElem_drop s dst h]
    rw [Compile.encodeRegs_append, Compile.encodeRegs_cons]
    simp [List.append_assoc]
  rw [Compile.regBlocks_map_shiftReg, hget, Compile.encodeTape, hs]
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

/-- **Behavioural soundness of `appendOne` (Risk C2 seam validation).**
`Compile.opAppendOne dst` run on `Compile.encodeTape s` halts and decodes to
`Op.eval (appendOne dst) s`. The step count is existential — bounding it by
`Compile.overhead (size + 1)` is the remaining cost-accounting obligation. -/
theorem compileOp_appendOne_behavioural (s : State) (dst : Var)
    (hbit : Compile.BitState s) (hdst : dst < s.length) :
    ∃ (steps : Nat) (cfg : FlatTMConfig),
      runFlatTM steps (Compile.opAppendOne dst).M
          (initFlatConfig (Compile.opAppendOne dst).M [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (Compile.opAppendOne dst).M cfg = true ∧
      Compile.decodeTape cfg = Op.eval (Op.appendOne dst) s := by
  -- Abbreviations matching `appendAt_run`'s `skipped`/`body`/`post`.
  set post : List Nat := Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] with hpost
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskip
  set body : List Nat := Compile.shiftReg (s.get dst) with hbody
  have hget_mem : s.get dst ∈ s := by
    rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
  -- Side conditions for `appendAt_run`, all from bit-shape.
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
    intro b hb
    rw [hskip, List.mem_map] at hb
    obtain ⟨r, hr, rfl⟩ := hb
    exact ⟨hshift_ne r, hshift_lt r (fun x hx => hbit r (List.mem_of_mem_take hr) x hx)⟩
  have hbody_ne : ∀ x ∈ body, x ≠ 0 := by rw [hbody]; exact hshift_ne _
  have hbody_lt : ∀ x ∈ body, x < 4 := by
    rw [hbody]; exact hshift_lt _ (fun x hx => hbit _ hget_mem x hx)
  have hpost_lt : ∀ x ∈ post, x < 4 := by
    rw [hpost]; intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeRegs_lt_four _
        (fun b hb y hy => hbit b (List.mem_of_mem_drop hb) y hy) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide
  -- The gadget run lemma (existential step count).
  obtain ⟨steps, st', hd', hrun, hhalt⟩ :=
    AppendGadget.appendAt_run 2 (by decide) dst [] skipped body post hlen
      h_pre h_skip hbody_ne hbody_lt hpost_lt
  -- Identify the input config with `initFlatConfig … [encodeTape s]`.
  have hsplit : ([] : List Nat) ++ AppendGadget.regBlocks skipped ++ body ++ 0 :: post
      = Compile.encodeTape s := by
    rw [List.nil_append, hskip, hbody, hpost]; exact Compile.encodeTape_split s dst hdst
  rw [List.length_nil, hsplit] at hrun
  have hinit : initFlatConfig (Compile.opAppendOne dst).M [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := by
    show initFlatConfig (AppendGadget.appendAtTM 2 dst) [Compile.encodeTape s] = _
    simp only [initFlatConfig, AppendGadget.appendAtTM_start, List.map_cons, List.map_nil]
  -- The output tape decodes to the evaluated state.
  have htape : ([] : List Nat) ++ AppendGadget.regBlocks skipped ++ body ++ 2 :: 0 :: post
      = Compile.encodeTape (Op.eval (Op.appendOne dst) s) := by
    rw [List.nil_append, hskip, hbody, hpost, Compile.regBlocks_map_shiftReg]
    show _ = Compile.encodeTape (s.set dst (s.get dst ++ [1]))
    rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst,
        Compile.encodeTape, Compile.encodeRegs_append, Compile.encodeRegs_cons,
        Compile.shiftReg_append_one]
    simp [List.append_assoc]
  refine ⟨steps,
    { state_idx := st',
      tapes := [([], hd', ([] : List Nat) ++ AppendGadget.regBlocks skipped ++ body ++ 2 :: 0 :: post)] },
    ?_, ?_, ?_⟩
  · rw [hinit]; exact hrun
  · exact hhalt
  · rw [show Compile.decodeTape
          { state_idx := st',
            tapes := [([], hd', ([] : List Nat) ++ AppendGadget.regBlocks skipped ++ body ++ 2 :: 0 :: post)] }
        = Compile.decodeTape
          { state_idx := st', tapes := [([], hd', Compile.encodeTape (Op.eval (Op.appendOne dst) s))] }
        from by rw [htape]]
    exact Compile.decodeTape_encodeTape' st' hd' _ (Compile.BitState_appendOne s dst hbit hdst)

/-! ### C2 cost-model finding — `compileOp_sound`'s budget is too tight

`compileOp_sound`'s budget is `Compile.overhead (State.size s + cost)`, but
`State.size s` (the sum of register *contents*) **ignores the register count**,
while `appendAtTM`'s step count grows with the **tape length**
`(encodeTape s).length = State.size s + s.length + 1` — reaching register `dst`
scans past every preceding register and `scanInsert` shifts the whole suffix.

Concretely (verified by evaluation), for `s = List.replicate 6 []` we have
`State.size s = 0`, so the stated budget is `overhead 1 = 4`, yet
`opAppendOne 0` first reaches a halting state only at **step 10** and after 4
steps decodes to the wrong state. So **`compileOp_sound` is false as stated.**

Fix: the per-op budget must be over the tape length,
`Compile.overhead ((encodeTape s).length + cost)`, and `Compile_sound`'s
assembly must thread the register count (bounded by the program's `regBound`).
The lemma below proves the corrected budget is provable (base case `dst = 0`,
from `AppendGadget.scanInsert_run`'s explicit step count). -/
theorem compileOp_appendOne_zero_sound (s : State) (hbit : Compile.BitState s)
    (hlen : 0 < s.length) :
    ∃ cfg,
      runFlatTM (Compile.overhead (Compile.encodeTape s).length)
          (Compile.opAppendOne 0).M
          (initFlatConfig (Compile.opAppendOne 0).M [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (Compile.opAppendOne 0).M cfg = true ∧
      Compile.decodeTape cfg = Op.eval (Op.appendOne 0) s := by
  set body : List Nat := Compile.shiftReg (s.get 0) with hbody
  set post : List Nat := Compile.encodeRegs (s.drop 1) ++ [Compile.endMark] with hpost
  have hget_mem : s.get 0 ∈ s := by
    rw [State.get, List.getElem?_eq_getElem hlen]; exact List.getElem_mem hlen
  have hbody_lt : ∀ x ∈ body, x < 4 := by
    rw [hbody]; intro x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx; have := hbit _ hget_mem y hy; omega
  have hpost_lt : ∀ x ∈ post, x < 4 := by
    rw [hpost]; intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeRegs_lt_four _
        (fun b hb y hy => hbit b (List.mem_of_mem_drop hb) y hy) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide
  -- `encodeTape s` peels at register 0 as `body ++ 0 :: post`.
  have henc : Compile.encodeTape s = body ++ 0 :: post := by
    rw [hbody, hpost, ← Compile.encodeTape_split s 0 hlen]
    simp [AppendGadget.regBlocks_nil]
  -- The gadget run with its *explicit* step count.
  obtain ⟨hrun, hhalt⟩ :=
    AppendGadget.scanInsert_run 2 (by decide) [] body post
      (by rw [hbody]; exact Compile.shiftReg_no_zero _) hbody_lt hpost_lt
  rw [List.length_nil, List.nil_append] at hrun hhalt
  rw [← henc] at hrun
  have hinit : initFlatConfig (Compile.opAppendOne 0).M [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := by
    show initFlatConfig (AppendGadget.appendAtTM 2 0) [Compile.encodeTape s] = _
    simp only [initFlatConfig, AppendGadget.appendAtTM_start, List.map_cons, List.map_nil]
  -- Budget: the explicit step count is `≤ overhead (tape length)`.
  have hstep_le : body.length + 1 + 1 + ((0 :: post).length + 1)
      ≤ Compile.overhead (Compile.encodeTape s).length := by
    have hcount : (Compile.encodeTape s).length = body.length + (0 :: post).length := by
      rw [henc, List.length_append]
    have hb1 : 1 ≤ (0 :: post).length := by rw [List.length_cons]; omega
    rw [Compile.overhead, hcount]
    nlinarith [hb1, Nat.zero_le body.length]
  obtain ⟨k, hk⟩ := Nat.le.dest hstep_le
  -- Output tape `body ++ 2 :: 0 :: post = encodeTape (eval (appendOne 0) s)`.
  have htape : body ++ 2 :: 0 :: post
      = Compile.encodeTape (Op.eval (Op.appendOne 0) s) := by
    rw [hbody, hpost]
    show _ = Compile.encodeTape (s.set 0 (s.get 0 ++ [1]))
    rw [State.set, if_pos hlen, Compile.list_set_eq_take_cons_drop s 0 _ hlen,
        Compile.encodeTape, List.take_zero, List.nil_append, Compile.encodeRegs_cons,
        Compile.shiftReg_append_one]
    simp [List.append_assoc]
  refine ⟨{ state_idx := 5 + (scanRightUntilTM 4 0).states,
            tapes := [([], 0 + body.length + (0 :: post).length, body ++ 2 :: 0 :: post)] },
    ?_, ?_, ?_⟩
  · rw [hinit, ← hk]; exact runFlatTM_extend hrun hhalt
  · exact hhalt
  · rw [htape]
    exact Compile.decodeTape_encodeTape' _ _ _
      (Compile.BitState_appendOne s 0 hbit hlen)

/-! ### Budgeted per-op soundness for `appendOne`/`appendZero` (general `dst`)

The two append ops are the only `compileOp`s with real TM bodies. The lemma
below discharges `compileOp_sound` for both — at **general `dst`** and with the
**corrected tape-length budget** `Compile.overhead ((encodeTape s).length +
Op.cost o s)` (the fix for the cost-model bug: the old `State.size`-based budget
ignored the register count and was false; see `compileOp_appendOne_zero_sound`).

It composes `AppendGadget.appendAt_run_steps` (explicit step count) with
`appendAt_steps_le` (the step count is `≤ 2·tapeLen + 3`, hence below
`overhead (tapeLen + 1) = (tapeLen + 2)²`) and the encoding seam already
validated in `compileOp_appendOne_behavioural`. This converts last session's
"`compileOp_sound` is false as stated, base case `dst = 0` only" into a proven
result for the real ops at all `dst`. -/
private theorem Compile.appendBit_sound (bit : Nat) (hb : bit ≤ 1)
    (s : State) (dst : Var) (hbit : Compile.BitState s) (hdst : dst < s.length) :
    ∃ cfg,
      runFlatTM (Compile.overhead ((Compile.encodeTape s).length + 1))
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
  -- The gadget run lemma, with its explicit step count.
  obtain ⟨st', hd', hrun, hhalt⟩ :=
    AppendGadget.appendAt_run_steps (bit + 1) h_ins dst [] skipped body post hlen
      h_pre h_skip hbody_ne hbody_lt hpost_lt
  -- The input tape is exactly `encodeTape s`.
  have hsplit : ([] : List Nat) ++ AppendGadget.regBlocks skipped ++ body ++ 0 :: post
      = Compile.encodeTape s := by
    rw [List.nil_append, hskip, hbody, hpost]; exact Compile.encodeTape_split s dst hdst
  rw [List.length_nil, hsplit] at hrun
  have hinit : initFlatConfig (AppendGadget.appendAtTM (bit + 1) dst) [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := by
    simp only [initFlatConfig, AppendGadget.appendAtTM_start, List.map_cons, List.map_nil]
  -- The explicit step count is `≤ overhead (tapeLen + 1)`.
  have hstep_le : AppendGadget.appendAt_steps skipped body post
      ≤ Compile.overhead ((Compile.encodeTape s).length + 1) := by
    have hb' := AppendGadget.appendAt_steps_le skipped body post
    have hL : (AppendGadget.regBlocks skipped ++ body ++ 0 :: post).length
        = (Compile.encodeTape s).length := by rw [← hsplit]; simp
    rw [hL] at hb'
    rw [Compile.overhead]
    nlinarith [hb', Nat.zero_le (Compile.encodeTape s).length]
  obtain ⟨k, hk⟩ := Nat.le.dest hstep_le
  -- The output tape decodes to the evaluated state.
  have htape : ([] : List Nat) ++ AppendGadget.regBlocks skipped ++ body ++ (bit + 1) :: 0 :: post
      = Compile.encodeTape (s.set dst (s.get dst ++ [bit])) := by
    rw [List.nil_append, hskip, hbody, hpost, Compile.regBlocks_map_shiftReg]
    rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst,
        Compile.encodeTape, Compile.encodeRegs_append, Compile.encodeRegs_cons,
        Compile.shiftReg_append]
    simp [List.append_assoc]
  refine ⟨{ state_idx := st',
            tapes := [([], hd',
              ([] : List Nat) ++ AppendGadget.regBlocks skipped ++ body
                ++ (bit + 1) :: 0 :: post)] }, ?_, ?_, ?_⟩
  · rw [hinit, ← hk]; exact runFlatTM_extend hrun hhalt
  · exact hhalt
  · rw [show Compile.decodeTape
          { state_idx := st',
            tapes := [([], hd',
              ([] : List Nat) ++ AppendGadget.regBlocks skipped ++ body
                ++ (bit + 1) :: 0 :: post)] }
        = Compile.decodeTape
          { state_idx := st',
            tapes := [([], hd',
              Compile.encodeTape (s.set dst (s.get dst ++ [bit])))] }
        from by rw [htape]]
    exact Compile.decodeTape_encodeTape' st' hd' _
      (Compile.BitState_appendBit bit hb s dst hbit hdst)

/-- **`compileOp_sound` for `appendOne`, general `dst`, corrected budget.** -/
theorem compileOp_appendOne_sound (s : State) (dst : Var)
    (hbit : Compile.BitState s) (hdst : dst < s.length) :
    ∃ cfg,
      runFlatTM (Compile.overhead ((Compile.encodeTape s).length
            + Op.cost (Op.appendOne dst) s))
          (compileOp (Op.appendOne dst)).M
          (initFlatConfig (compileOp (Op.appendOne dst)).M
            [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (compileOp (Op.appendOne dst)).M cfg = true ∧
      Compile.decodeTape cfg = Op.eval (Op.appendOne dst) s :=
  Compile.appendBit_sound 1 (by omega) s dst hbit hdst

/-- **`compileOp_sound` for `appendZero`, general `dst`, corrected budget.** -/
theorem compileOp_appendZero_sound (s : State) (dst : Var)
    (hbit : Compile.BitState s) (hdst : dst < s.length) :
    ∃ cfg,
      runFlatTM (Compile.overhead ((Compile.encodeTape s).length
            + Op.cost (Op.appendZero dst) s))
          (compileOp (Op.appendZero dst)).M
          (initFlatConfig (compileOp (Op.appendZero dst)).M
            [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (compileOp (Op.appendZero dst)).M cfg = true ∧
      Compile.decodeTape cfg = Op.eval (Op.appendZero dst) s :=
  Compile.appendBit_sound 0 (by omega) s dst hbit hdst

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
     gadgets already prove this; `compileOp_appendOne_sound` *loosened* it to the
     quadratic `overhead`, which is the wrong direction for the assembly);
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

/-- The bit-test gadget: a single-tape, 4-symbol, 3-state `FlatTM`. From the
(non-halting) start state `0`, reading tape symbol `2` jumps to the halting
state `1` (accept); reading `1` jumps to the halting state `2` (reject). It does
not move the head or write. -/
def Compile.bitTestTM : FlatTM where
  sig := 4
  tapes := 1
  states := 3
  trans :=
    [ { src_state := 0, src_tape_vals := [some 2], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] },
      { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] } ]
  start := 0
  halt := [false, true, true]

theorem Compile.bitTestTM_valid : validFlatTM Compile.bitTestTM := by
  refine ⟨by decide, rfl, ?_⟩
  intro entry hentry
  have hmem : entry ∈
      [ ({ src_state := 0, src_tape_vals := [some 2], dst_state := 1,
           dst_write_vals := [none], move_dirs := [TMMove.Nmove] } : FlatTMTransEntry),
        { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } ] := hentry
  have hbound2 : flatTMOptionSymbolsBounded 4 [some 2] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide
  have hbound1 : flatTMOptionSymbolsBounded 4 [some 1] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide
  have hboundNone : flatTMOptionSymbolsBounded 4 [none] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; trivial
  rcases List.mem_cons.mp hmem with h | hmem
  · subst h; exact ⟨by decide, by decide, rfl, rfl, rfl, hbound2, hboundNone⟩
  · rcases List.mem_cons.mp hmem with h | h
    · subst h; exact ⟨by decide, by decide, rfl, rfl, rfl, hbound1, hboundNone⟩
    · simp at h

theorem Compile.bitTestTM_tapes : Compile.bitTestTM.tapes = 1 := rfl

theorem Compile.bitTestTM_sig : Compile.bitTestTM.sig = 4 := rfl

theorem Compile.bitTestTM_start : Compile.bitTestTM.start = 0 := rfl

/-- Reading symbol `2` (accept) from the start state halts the gadget in
state `1` in one step. -/
theorem Compile.bitTestTM_run_two (left rest : List Nat) :
    runFlatTM 1 Compile.bitTestTM { state_idx := 0, tapes := [(left, 0, 2 :: rest)] }
      = some { state_idx := 1, tapes := [(left, 0, 2 :: rest)] } := rfl

/-- Reading symbol `1` (reject) from the start state halts the gadget in
state `2` in one step. -/
theorem Compile.bitTestTM_run_one (left rest : List Nat) :
    runFlatTM 1 Compile.bitTestTM { state_idx := 0, tapes := [(left, 0, 1 :: rest)] }
      = some { state_idx := 2, tapes := [(left, 0, 1 :: rest)] } := rfl

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
so it is left as a single, focused `sorry`. -/
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

/-- The canonical single-register tape `encodeTape [r]` has length `r.length + 2`
(the shifted register, the `0` delimiter, and the `endMark`). Used to bound the
`DecidesBy.encode_size` of the canonical decider bridge. -/
theorem Compile.encodeTape_singleton_length (r : List Nat) :
    (Compile.encodeTape [r]).length = r.length + 2 := by
  simp [Compile.encodeTape, Compile.encodeRegs, Compile.shiftReg]

/-- **C6 headline.** Running `bitDeciderTM c` on `encodeTape s` halts, within
`overhead (size s + cost s) + 2` steps, in state `1 + (Compile c).states` when
register `0` of `c.eval s` is `[1]` (accept) and `2 + (Compile c).states` when
it is `[0]` (reject). Combines the physical run contract of `Compile c` with the
`sorry`-free gadget run lemma, via `composeFlatTM_run`. -/
theorem Compile.bitDecider_run (c : Cmd) (s : State) (b : Nat)
    (hbit : b = 0 ∨ b = 1) (h0 : (c.eval s).get 0 = [b]) :
    ∃ cfg,
      runFlatTM (Compile.overhead (State.size s + c.cost s) + 2) (Compile.bitDeciderTM c)
          (initFlatConfig (Compile.bitDeciderTM c) [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (Compile.bitDeciderTM c) cfg = true ∧
      cfg.state_idx = (if b = 1 then 1 else 2) + (Compile c).states := by
  obtain ⟨tl, htl⟩ := Compile.encodeTape_eq_cons_of_get_zero (c.eval s) b h0
  obtain ⟨t1, hrun1, htraj1, ht1⟩ := Compile_run_physical c s
  -- Rewrite the physical exit tape via the encoding lemma.
  rw [htl] at hrun1
  -- The gadget's exit state for this bit.
  set dst : Nat := if b = 1 then 1 else 2 with hdst
  -- Gadget run + halt (split on the bit).
  have hrun2 : runFlatTM 1 Compile.bitTestTM
      { state_idx := Compile.bitTestTM.start, tapes := [([], 0, (b + 1) :: tl)] }
      = some { state_idx := dst, tapes := [([], 0, (b + 1) :: tl)] } := by
    rcases hbit with hb | hb <;> subst hb <;>
      simp only [Compile.bitTestTM_start, hdst] <;> rfl
  have hhalt2 : haltingStateReached Compile.bitTestTM
      { state_idx := dst, tapes := [([], 0, (b + 1) :: tl)] } = true := by
    rcases hbit with hb | hb <;> subst hb <;> rfl
  -- The first tape symbol is bounded by the alphabet.
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, (b + 1) :: tl) = some v →
      v < max (Compile c).sig Compile.bitTestTM.sig := by
    intro v hv
    have : v = b + 1 := by simpa [currentTapeSymbol] using hv.symm
    subst this
    rw [Compile_sig, Compile.bitTestTM_sig]
    rcases hbit with hb | hb <;> subst hb <;> decide
  have hstate0 : (initFlatConfig (Compile c) [Compile.encodeTape s]).state_idx
      < (Compile c).states := (Compile_valid c).1
  -- Compose.
  have hcomp := composeFlatTM_run (M₁ := Compile c) (M₂ := Compile.bitTestTM)
    (exit := Compile.exit c) (Compile_valid c) Compile.bitTestTM_valid
    (Compile_exit_lt c)
    (initFlatConfig (Compile c) [Compile.encodeTape s]) hstate0
    [] 0 ((b + 1) :: tl) hsym hrun1 htraj1 hrun2 hhalt2
  obtain ⟨hcrun, hchalt⟩ := hcomp
  -- Pad the run up to the stated budget.
  obtain ⟨k, hk⟩ := Nat.le.dest ht1
  refine ⟨{ state_idx := dst + (Compile c).states, tapes := [([], 0, (b + 1) :: tl)] }, ?_, ?_, ?_⟩
  · show runFlatTM (Compile.overhead (State.size s + c.cost s) + 2) (Compile.bitDeciderTM c)
        (initFlatConfig (Compile.bitDeciderTM c) [Compile.encodeTape s]) = _
    have hbudget : Compile.overhead (State.size s + c.cost s) + 2 = (t1 + 1 + 1) + k := by omega
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
