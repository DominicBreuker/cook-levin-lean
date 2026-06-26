import Complexity.Lang.Semantics
import Complexity.Lang.Frame
import Complexity.Lang.AppendGadget
import Complexity.Lang.ClearGadget
import Complexity.Complexity.TMPrimitives
import Complexity.Complexity.TapeMono
import Complexity.Lang.Compile.Core
import Complexity.Lang.Compile.Encoding
import Complexity.Lang.Compile.OpMachines

set_option autoImplicit false

/-! # `Compile/Cmd` — the per-constructor compilers + the compiler `compileCmd`

Extracted from `Compile.lean` (refactor Phase 2, see `REFACTOR-HANDOFF.md`).
The compiler *definitions* layer: every `Cmd`/`Op` constructor's compiled
`CompiledCmd`, plus the top-level recursion `compileCmd` and the consumer API.

- `compileOp` (dispatch to the per-`Op` machines in `Compile/OpMachines`),
  `compileSeq` (via `composeFlatTM`).
- `compileIfBit` + the bit tester `compileTestBit` (`exactOneOneTM`/
  `testBitInnerTM`/`testBitRawTM` leaves + `branchCompose_halt_only_at_exits`).
- the `forBnd` loop machines (`forBndIterate`, `forBndContentTM`/`forBndBodyTM`/
  `forBndLoopTM`/`forBndLoopCmd`) + `compileForBnd`.
- `compileCmd`/`Compile`/`Compile.exit` + the `Compile_valid`/`_tapes`/`_sig`
  structural lemmas.

These are the compiler *constructions* only — the run/behaviour lemmas and the
per-op soundness contract live downstream in `Compile.lean`. Depends only on
`Compile/OpMachines` (+ `Core`/`Encoding` + the gadget primitives). -/

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators
/-- Compile a single primitive operation `Op` to a `CompiledCmd`
by dispatching on the constructor. The actual TM construction
lives in the per-`Op` helpers above. -/
def compileOp (sb : Nat) : Op → CompiledCmd
  | .clear dst                 => Compile.opClear dst
  | .appendOne dst             => Compile.opAppendOne dst
  | .appendZero dst            => Compile.opAppendZero dst
  | .copy dst src              => Compile.opCopy dst src
  | .tail dst src              => Compile.opTail dst src
  | .head dst src              => Compile.opHead dst src
  | .eqBit dst src1 src2       => Compile.opEqBit sb dst src1 src2
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

/-! ### The real bit tester `compileTestBit` (Risk C2, bottom-up Task 2)

`ifBit t cT cE` branches on `s.get t = [1]` — register `t` holds **exactly** the
single bit `1` (tape block `[2]`). The tester reads that and *restores* the
machine to the branch bodies' expected start (head `0`, tape unchanged):

- `navigateAndTestTM t` — head onto `t`'s first cell (content) or its `0`
  delimiter (register empty → NEG);
- content → `exactOneOneTM`: first cell `1` (bit 0) → NEG; `2` (bit 1) → step
  right: `0` (block end) → POS; `1`/`2` (≥ 2 bits) → NEG;
- every leaf rewinds to the leading sentinel with `justRewindTM`
  (`scanLeftUntilTM 4 3` — sound because the head is never *on* a `3`: every
  register block ends in its own `0` delimiter, and the leaf heads sit inside
  the encoded region), leaving the tape unchanged;
- the two NEG leaves merge through `Compile.joinTwoHalts`.

`#eval`-validated end-to-end (17-state battery × test registers × residues;
observed step counts ≤ 2·L + 5). Run lemmas: `Compile.testBitReg_run_pos` /
`Compile.testBitReg_run_neg` (below the `navTestReg` block, where the
`encodeTape` decomposition lemmas live). -/

/-- Read "register block = exactly `[2]`" from the block's first cell: state 0
reads the first cell (`1` → NEG, `2` → step right), state 1 reads the second
cell (`0` → POS, `1`/`2` → NEG). Exits: `2` = NEG, `3` = POS. The block-end cell
is always the register's own `0` delimiter (never the terminator `3`), so the
two states need only the four bit/delimiter symbols. -/
def Compile.exactOneOneTM : FlatTM where
  sig := 4
  tapes := 1
  states := 4
  trans := [
    { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
      dst_write_vals := [none], move_dirs := [TMMove.Nmove] },
    { src_state := 0, src_tape_vals := [some 2], dst_state := 1,
      dst_write_vals := [none], move_dirs := [TMMove.Rmove] },
    { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
      dst_write_vals := [none], move_dirs := [TMMove.Nmove] },
    { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
      dst_write_vals := [none], move_dirs := [TMMove.Nmove] },
    { src_state := 1, src_tape_vals := [some 2], dst_state := 2,
      dst_write_vals := [none], move_dirs := [TMMove.Nmove] }]
  start := 0
  halt := [false, false, true, true]

def Compile.exactOneOneTM_exitNeg : Nat := 2
def Compile.exactOneOneTM_exitPos : Nat := 3

theorem Compile.exactOneOneTM_tapes : Compile.exactOneOneTM.tapes = 1 := rfl
theorem Compile.exactOneOneTM_start : Compile.exactOneOneTM.start = 0 := rfl
theorem Compile.exactOneOneTM_sig : Compile.exactOneOneTM.sig = 4 := rfl
theorem Compile.exactOneOneTM_states : Compile.exactOneOneTM.states = 4 := rfl

theorem Compile.exactOneOneTM_valid : validFlatTM Compile.exactOneOneTM := by
  refine ⟨show (0 : Nat) < 4 from by decide, rfl, ?_⟩
  intro entry hentry
  fin_cases hentry <;>
    exact ⟨by decide, by decide, rfl, rfl, rfl,
      by intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide,
      by intro x hx; simp only [List.mem_singleton] at hx; subst hx; trivial⟩

/-- `justRewindTM`'s (`= scanLeftUntilTM 4 3`) accept exit `1` is a halt. -/
theorem Compile.justRewindTM_exit_is_halt :
    ClearGadget.justRewindTM.halt[ClearGadget.justRewindTM_exit]? = some true := rfl

/-- The inner content tester: `exactOneOneTM`, each exit followed by the
left-rewind to the leading sentinel. States: `4 + 3 + 3 = 10`.
Exits: POS = `4 + 1 = 5`, NEG = `4 + 3 + 1 = 8`. -/
def Compile.testBitInnerTM : FlatTM :=
  branchComposeFlatTM Compile.exactOneOneTM
    ClearGadget.justRewindTM ClearGadget.justRewindTM
    Compile.exactOneOneTM_exitPos Compile.exactOneOneTM_exitNeg

def Compile.testBitInner_exitPos : Nat :=
  Compile.exactOneOneTM.states + ClearGadget.justRewindTM_exit

def Compile.testBitInner_exitNeg : Nat :=
  Compile.exactOneOneTM.states + ClearGadget.justRewindTM.states
    + ClearGadget.justRewindTM_exit

theorem Compile.testBitInnerTM_tapes : Compile.testBitInnerTM.tapes = 1 := rfl
theorem Compile.testBitInnerTM_sig : Compile.testBitInnerTM.sig = 4 := rfl
theorem Compile.testBitInnerTM_states : Compile.testBitInnerTM.states = 10 := rfl
theorem Compile.testBitInnerTM_start : Compile.testBitInnerTM.start = 0 := rfl

theorem Compile.testBitInnerTM_valid : validFlatTM Compile.testBitInnerTM :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.exactOneOneTM_valid
    (ClearGadget.justRewindTM_valid) (ClearGadget.justRewindTM_valid)
    (by decide) (by decide) rfl rfl rfl

theorem Compile.testBitInner_exitPos_is_halt :
    Compile.testBitInnerTM.halt[Compile.testBitInner_exitPos]? = some true :=
  Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    ClearGadget.justRewindTM_valid (by decide) Compile.justRewindTM_exit_is_halt

theorem Compile.testBitInner_exitNeg_is_halt :
    Compile.testBitInnerTM.halt[Compile.testBitInner_exitNeg]? = some true :=
  Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    ClearGadget.justRewindTM_valid Compile.justRewindTM_exit_is_halt

/-- The raw three-leaf tester: navigate to register `t`, content → inner tester,
empty → rewind (NEG). Exits: POS = `N + 5`, NEG (inner) = `N + 8`,
NEG (delim) = `N + 10 + 1` with `N = (navigateAndTestTM t).states`. -/
def Compile.testBitRawTM (t : Var) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
    Compile.testBitInnerTM ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content t)
    (ClearGadget.navigateAndTestTM_exit_delim t)

def Compile.testBitRaw_exitPos (t : Var) : Nat :=
  (ClearGadget.navigateAndTestTM t).states + Compile.testBitInner_exitPos

def Compile.testBitRaw_exitNeg (t : Var) : Nat :=
  (ClearGadget.navigateAndTestTM t).states + Compile.testBitInner_exitNeg

def Compile.testBitRaw_exitNegDelim (t : Var) : Nat :=
  (ClearGadget.navigateAndTestTM t).states + Compile.testBitInnerTM.states
    + ClearGadget.justRewindTM_exit

theorem Compile.testBitRawTM_tapes (t : Var) : (Compile.testBitRawTM t).tapes = 1 := by
  rw [Compile.testBitRawTM, branchComposeFlatTM_tapes]
  exact ClearGadget.navigateAndTestTM_tapes t

theorem Compile.testBitRawTM_sig (t : Var) : (Compile.testBitRawTM t).sig = 4 := by
  rw [Compile.testBitRawTM, branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig]
  rfl

theorem Compile.testBitRawTM_states (t : Var) :
    (Compile.testBitRawTM t).states = (ClearGadget.navigateAndTestTM t).states + 13 := by
  rw [Compile.testBitRawTM, branchComposeFlatTM_states, Compile.testBitInnerTM_states]
  rfl

theorem Compile.testBitRawTM_start (t : Var) : (Compile.testBitRawTM t).start = 0 := by
  rw [Compile.testBitRawTM, branchComposeFlatTM_start]
  exact ClearGadget.navigateAndTestTM_start t

theorem Compile.testBitRawTM_valid (t : Var) : validFlatTM (Compile.testBitRawTM t) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.navigateAndTestTM_valid t)
    Compile.testBitInnerTM_valid ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt t)
    (ClearGadget.navigateAndTestTM_exit_delim_lt t)
    (ClearGadget.navigateAndTestTM_tapes t) Compile.testBitInnerTM_tapes rfl

theorem Compile.testBitRaw_exitPos_is_halt (t : Var) :
    (Compile.testBitRawTM t).halt[Compile.testBitRaw_exitPos t]? = some true :=
  Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    Compile.testBitInnerTM_valid (by rw [Compile.testBitInnerTM_states]; decide)
    Compile.testBitInner_exitPos_is_halt

theorem Compile.testBitRaw_exitNeg_is_halt (t : Var) :
    (Compile.testBitRawTM t).halt[Compile.testBitRaw_exitNeg t]? = some true :=
  Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    Compile.testBitInnerTM_valid (by rw [Compile.testBitInnerTM_states]; decide)
    Compile.testBitInner_exitNeg_is_halt

theorem Compile.testBitRaw_exitNegDelim_is_halt (t : Var) :
    (Compile.testBitRawTM t).halt[Compile.testBitRaw_exitNegDelim t]? = some true :=
  Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    Compile.testBitInnerTM_valid Compile.justRewindTM_exit_is_halt

/-- Compile a "test register `t` = `[1]`" gadget — the **real** tester (the
`branchTester_default` stub is retired). The two NEG leaves (inner / delim) are
merged by demoting the delim leaf into the inner one. -/
def compileTestBit (t : Var) : BranchTester where
  M := Compile.joinTwoHalts (Compile.testBitRawTM t)
        (Compile.testBitRaw_exitNeg t) (Compile.testBitRaw_exitNegDelim t)
  exitPos := Compile.testBitRaw_exitPos t
  exitNeg := Compile.testBitRaw_exitNeg t
  exitPos_lt := by
    rw [Compile.joinTwoHalts_states, Compile.testBitRawTM_states,
        Compile.testBitRaw_exitPos]
    have : Compile.testBitInner_exitPos = 5 := rfl
    omega
  exitNeg_lt := by
    rw [Compile.joinTwoHalts_states, Compile.testBitRawTM_states,
        Compile.testBitRaw_exitNeg]
    have : Compile.testBitInner_exitNeg = 8 := rfl
    omega
  exit_distinct := by
    rw [Compile.testBitRaw_exitPos, Compile.testBitRaw_exitNeg]
    have h5 : Compile.testBitInner_exitPos = 5 := rfl
    have h8 : Compile.testBitInner_exitNeg = 8 := rfl
    omega
  M_valid := Compile.joinTwoHalts_valid _ _ _ (Compile.testBitRawTM_valid t)
    (by rw [Compile.testBitRawTM_states, Compile.testBitRaw_exitNeg]
        have : Compile.testBitInner_exitNeg = 8 := rfl
        omega)
    (by rw [Compile.testBitRawTM_states, Compile.testBitRaw_exitNegDelim,
            Compile.testBitInnerTM_states]
        have : ClearGadget.justRewindTM_exit = 1 := rfl
        omega)
    (Compile.testBitRawTM_tapes t)
  M_tapes := by rw [Compile.joinTwoHalts_tapes]; exact Compile.testBitRawTM_tapes t
  M_sig := by rw [Compile.joinTwoHalts_sig]; exact Compile.testBitRawTM_sig t

theorem compileTestBit_start (t : Var) : (compileTestBit t).M.start = 0 := by
  show (Compile.joinTwoHalts (Compile.testBitRawTM t) _ _).start = 0
  rw [Compile.joinTwoHalts_start]
  exact Compile.testBitRawTM_start t

/-- The POS exit survives the join untouched (it is neither `h1` nor `h2`). -/
theorem compileTestBit_exitPos_is_halt (t : Var) :
    (compileTestBit t).M.halt[(compileTestBit t).exitPos]? = some true := by
  show ((Compile.testBitRawTM t).halt.set
      (Compile.testBitRaw_exitNegDelim t) false)[Compile.testBitRaw_exitPos t]? = some true
  rw [List.getElem?_set_ne (by
    rw [Compile.testBitRaw_exitNegDelim, Compile.testBitRaw_exitPos,
        Compile.testBitInnerTM_states]
    have h5 : Compile.testBitInner_exitPos = 5 := rfl
    have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
    omega)]
  exact Compile.testBitRaw_exitPos_is_halt t

/-- The NEG exit (the join's kept state `h1`) remains a halt. -/
theorem compileTestBit_exitNeg_is_halt (t : Var) :
    (compileTestBit t).M.halt[(compileTestBit t).exitNeg]? = some true :=
  Compile.joinTwoHalts_h1_is_halt _ _ _
    (by rw [Compile.testBitRaw_exitNeg, Compile.testBitRaw_exitNegDelim,
            Compile.testBitInnerTM_states]
        have h8 : Compile.testBitInner_exitNeg = 8 := rfl
        have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
        omega)
    (Compile.testBitRaw_exitNeg_is_halt t)

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

/-! ### The `forBnd` loop-body bookkeeping chain (`forBndIterate`)

The per-iteration work of the pinned `compileForBnd` machine, expressed as a
`CompiledCmd` built by `compileSeq` from the PROVEN op gadgets. One iteration
(`K1 = sb` holds the remaining count, `K2 = sb + 1` the done count):

```
copy counter K2 ⨾ rbody ⨾ appendOne K2 ⨾ tail K1 K1
```

(`copy counter K2` re-materialises `counter` from the done count, `rbody` runs one
body iteration, `appendOne K2` increments the done count, `tail K1 K1` decrements
the remaining count.) `forBndIterate_run` discharges its TM-level run from the four
op run lemmas via `compileSeq_sound_physical_residue`, validating the **W-invariant
① accounting** (joint size+residue grows by ≤ the iteration's cost contribution
`|K2| + body.cost + 1`) at the *machine* level — the claim the
`ForBndSkeletonProbe` only checked arithmetically.

⚠ **The loop body machine** (next bottom-up session) wraps this chain behind the
`navigateAndTestTM K1` guard: the guard leaves the head in the tape **interior**
(`navigateAndTestTM_run_content` ends at index `1 + |regBlocks|`, NOT `0`), but
`forBndIterate`'s first op (`opCopy`) navigates from head `0`, so the content
branch must **rewind to the leading sentinel** first (`justRewindTM =
scanLeftUntilTM 4 3` from the interior lands on index `0`; the only `3` to the
head's left). I.e. `Mcontent = composeFlatTM justRewindTM (forBndIterate …).M …`,
`Mdelim = justRewindTM` — the `clearBodyRawTM` branch shape with the work chain in
the content slot. -/

/-- The per-iteration output state of `forBndIterate` (= the loop fold's
`body.eval (st.set counter (replicate i 1))` followed by the bookkeeping, when
`State.get s (sb+1) = replicate i 1`; matches `ForBndSkeletonProbe.machineModel`'s
`go` body). -/
def Compile.forBndIterateState (counter sb : Var) (body : Cmd) (s : State) : State :=
  let s1 := s.set counter (State.get s (sb + 1))
  let s2 := body.eval s1
  let s3 := s2.set (sb + 1) (State.get s2 (sb + 1) ++ [1])
  s3.set sb (State.get s3 sb).tail

/-- The per-iteration bookkeeping chain `copy counter K2 ⨾ rbody ⨾ appendOne K2 ⨾
tail K1 K1`, as a `CompiledCmd` (`K1 = sb`, `K2 = sb + 1`). -/
def Compile.forBndIterate (counter sb : Var) (rbody : CompiledCmd) : CompiledCmd :=
  compileSeq (Compile.opCopy counter (sb + 1))
    (compileSeq rbody
      (compileSeq (Compile.opAppendBitRewind (1 + 1) (by omega) (sb + 1))
        (Compile.opTail sb sb)))

/-! ### The `forBnd` loop-body machine (`forBndBodyTM`) and loop (`forBndLoopTM`)

`forBndBodyTM counter sb rbody` is the `loopTM` body for the pinned `compileForBnd`
machine: a `branchComposeFlatTM (navigateAndTestTM sb) …` mirroring
`ClearGadget.clearBodyRawTM` exactly, but with the per-iteration bookkeeping chain
`forBndIterate` in the content slot. The guard `navigateAndTestTM sb` leaves the
head in the tape **interior**, so the content branch first **rewinds** to the
leading sentinel (`justRewindTM`) before running `forBndIterate` (whose first op
navigates from head `0`) — the structural finding of the prior session. The
delimiter branch is a bare `justRewindTM` (register `K1 = sb` empty ⇒ stop).

Like `clearBodyRawTM`, this is a *bare* branch machine (no `joinTwoHalts`): `loopTM`
tolerates the two extra unreachable boundary halts (`justRewindTM`'s reject in each
slot), never triggered on a terminator-free residue. **Probe-validated end-to-end**
(content → `exitLoop`, delim → `exitDone`; exact output tapes), see
`forBndIterate_run` for the per-iteration contract this body wraps. -/

/-- Content branch: rewind to the leading sentinel, then run the per-iteration
chain `forBndIterate`. -/
def Compile.forBndContentTM (counter sb : Var) (rbody : CompiledCmd) : FlatTM :=
  composeFlatTM ClearGadget.justRewindTM (Compile.forBndIterate counter sb rbody).M
    ClearGadget.justRewindTM_exit

/-- The `forBnd` loop body (the `loopTM` body machine). -/
def Compile.forBndBodyTM (counter sb : Var) (rbody : CompiledCmd) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM sb)
    (Compile.forBndContentTM counter sb rbody) ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content sb) (ClearGadget.navigateAndTestTM_exit_delim sb)

/-- `exitLoop`: the content-branch exit (one iteration done, continue the loop). -/
def Compile.forBndBodyTM_exitLoop (counter sb : Var) (rbody : CompiledCmd) : Nat :=
  (ClearGadget.navigateAndTestTM sb).states
    + (ClearGadget.justRewindTM.states + (Compile.forBndIterate counter sb rbody).exit)

/-- `exitDone`: the delimiter-branch exit (`K1` empty, stop the loop). -/
def Compile.forBndBodyTM_exitDone (counter sb : Var) (rbody : CompiledCmd) : Nat :=
  (ClearGadget.navigateAndTestTM sb).states + (Compile.forBndContentTM counter sb rbody).states
    + ClearGadget.justRewindTM_exit

/-! #### Content-branch structural lemmas -/

theorem Compile.forBndContentTM_states (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndContentTM counter sb rbody).states
      = ClearGadget.justRewindTM.states + (Compile.forBndIterate counter sb rbody).M.states := by
  rw [Compile.forBndContentTM, composeFlatTM_states]

theorem Compile.forBndContentTM_tapes (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndContentTM counter sb rbody).tapes = 1 := by
  rw [Compile.forBndContentTM, composeFlatTM_tapes]; exact ClearGadget.justRewindTM_tapes

theorem Compile.forBndContentTM_sig (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndContentTM counter sb rbody).sig = 4 := by
  show max ClearGadget.justRewindTM.sig (Compile.forBndIterate counter sb rbody).M.sig = 4
  rw [(Compile.forBndIterate counter sb rbody).M_sig]; rfl

theorem Compile.forBndContentTM_valid (counter sb : Var) (rbody : CompiledCmd) :
    validFlatTM (Compile.forBndContentTM counter sb rbody) :=
  composeFlatTM_valid ClearGadget.justRewindTM (Compile.forBndIterate counter sb rbody).M
    ClearGadget.justRewindTM_exit ClearGadget.justRewindTM_valid
    (Compile.forBndIterate counter sb rbody).M_valid (by decide)
    ClearGadget.justRewindTM_tapes (Compile.forBndIterate counter sb rbody).M_tapes

/-! #### Loop-body structural lemmas -/

theorem Compile.forBndBodyTM_tapes (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndBodyTM counter sb rbody).tapes = 1 := by
  rw [Compile.forBndBodyTM, branchComposeFlatTM_tapes]; exact ClearGadget.navigateAndTestTM_tapes sb

theorem Compile.forBndBodyTM_start (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndBodyTM counter sb rbody).start = 0 := by
  rw [Compile.forBndBodyTM, branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start sb

theorem Compile.forBndBodyTM_sig (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndBodyTM counter sb rbody).sig = 4 := by
  rw [Compile.forBndBodyTM, branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig,
      Compile.forBndContentTM_sig]; rfl

theorem Compile.forBndBodyTM_states (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndBodyTM counter sb rbody).states
      = (ClearGadget.navigateAndTestTM sb).states
        + (Compile.forBndContentTM counter sb rbody).states + ClearGadget.justRewindTM.states := by
  rw [Compile.forBndBodyTM, branchComposeFlatTM_states]

theorem Compile.forBndBodyTM_valid (counter sb : Var) (rbody : CompiledCmd) :
    validFlatTM (Compile.forBndBodyTM counter sb rbody) :=
  branchComposeFlatTM_valid (ClearGadget.navigateAndTestTM sb)
    (Compile.forBndContentTM counter sb rbody) ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content sb) (ClearGadget.navigateAndTestTM_exit_delim sb)
    (ClearGadget.navigateAndTestTM_valid sb) (Compile.forBndContentTM_valid counter sb rbody)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt sb) (ClearGadget.navigateAndTestTM_exit_delim_lt sb)
    (ClearGadget.navigateAndTestTM_tapes sb) (Compile.forBndContentTM_tapes counter sb rbody)
    ClearGadget.justRewindTM_tapes

theorem Compile.forBndBodyTM_exitLoop_lt (counter sb : Var) (rbody : CompiledCmd) :
    Compile.forBndBodyTM_exitLoop counter sb rbody
      < (Compile.forBndBodyTM counter sb rbody).states := by
  rw [Compile.forBndBodyTM_exitLoop, Compile.forBndBodyTM_states, Compile.forBndContentTM_states]
  have := (Compile.forBndIterate counter sb rbody).exit_lt
  omega

theorem Compile.forBndBodyTM_exitDone_lt (counter sb : Var) (rbody : CompiledCmd) :
    Compile.forBndBodyTM_exitDone counter sb rbody
      < (Compile.forBndBodyTM counter sb rbody).states := by
  rw [Compile.forBndBodyTM_exitDone, Compile.forBndBodyTM_states]
  have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
  have h2 : ClearGadget.justRewindTM.states = 3 := rfl
  omega

theorem Compile.forBndBodyTM_exitDone_ne_exitLoop (counter sb : Var) (rbody : CompiledCmd) :
    Compile.forBndBodyTM_exitDone counter sb rbody
      ≠ Compile.forBndBodyTM_exitLoop counter sb rbody := by
  rw [Compile.forBndBodyTM_exitDone, Compile.forBndBodyTM_exitLoop, Compile.forBndContentTM_states]
  have := (Compile.forBndIterate counter sb rbody).exit_lt
  have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
  have h2 : ClearGadget.justRewindTM.states = 3 := rfl
  omega

/-- `exitLoop` (the content-branch exit, in the `forBndContentTM` M₂ slot) IS a
halt state of the loop body. -/
theorem Compile.forBndBodyTM_exitLoop_is_halt (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndBodyTM counter sb rbody).halt[
        Compile.forBndBodyTM_exitLoop counter sb rbody]? = some true := by
  have hc : (Compile.forBndContentTM counter sb rbody).halt[
      ClearGadget.justRewindTM.states + (Compile.forBndIterate counter sb rbody).exit]?
        = some true :=
    ScanLeft.composeFlatTM_halt_some_intro ClearGadget.justRewindTM
      (Compile.forBndIterate counter sb rbody).M ClearGadget.justRewindTM_exit
      (Compile.forBndIterate counter sb rbody).exit
      (Compile.forBndIterate counter sb rbody).exit_is_halt
  show (List.replicate (ClearGadget.navigateAndTestTM sb).states false
        ++ (Compile.forBndContentTM counter sb rbody).halt ++ ClearGadget.justRewindTM.halt)[
        (ClearGadget.navigateAndTestTM sb).states
          + (ClearGadget.justRewindTM.states + (Compile.forBndIterate counter sb rbody).exit)]?
        = some true
  have hlen : (Compile.forBndContentTM counter sb rbody).halt.length
      = (Compile.forBndContentTM counter sb rbody).states :=
    (Compile.forBndContentTM_valid counter sb rbody).2.1
  rw [List.append_assoc,
      List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate, Nat.add_sub_cancel_left,
      List.getElem?_append_left (by
        rw [hlen, Compile.forBndContentTM_states]
        have := (Compile.forBndIterate counter sb rbody).exit_lt; omega)]
  exact hc

/-- `exitDone` (the delimiter-branch exit, `justRewindTM`'s found halt `1` in the
M₃ slot) IS a halt state of the loop body. -/
theorem Compile.forBndBodyTM_exitDone_is_halt (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndBodyTM counter sb rbody).halt[
        Compile.forBndBodyTM_exitDone counter sb rbody]? = some true := by
  show (List.replicate (ClearGadget.navigateAndTestTM sb).states false
        ++ (Compile.forBndContentTM counter sb rbody).halt ++ ClearGadget.justRewindTM.halt)[
        (ClearGadget.navigateAndTestTM sb).states
          + (Compile.forBndContentTM counter sb rbody).states + ClearGadget.justRewindTM_exit]?
        = some true
  have hlen : (Compile.forBndContentTM counter sb rbody).halt.length
      = (Compile.forBndContentTM counter sb rbody).states :=
    (Compile.forBndContentTM_valid counter sb rbody).2.1
  rw [List.getElem?_append_right (by rw [List.length_append, List.length_replicate, hlen]; omega),
      List.length_append, List.length_replicate, hlen,
      show (ClearGadget.navigateAndTestTM sb).states
            + (Compile.forBndContentTM counter sb rbody).states + ClearGadget.justRewindTM_exit
          - ((ClearGadget.navigateAndTestTM sb).states
            + (Compile.forBndContentTM counter sb rbody).states)
          = ClearGadget.justRewindTM_exit from by omega]
  rfl

/-! #### The loop machine `forBndLoopTM = loopTM forBndBodyTM exitDone exitLoop` -/

/-- The pinned `forBnd` loop: `loopTM` of the body, with `exitDone` (register empty)
the done exit and `exitLoop` the per-iteration continue exit. -/
def Compile.forBndLoopTM (counter sb : Var) (rbody : CompiledCmd) : FlatTM :=
  loopTM (Compile.forBndBodyTM counter sb rbody)
    (Compile.forBndBodyTM_exitDone counter sb rbody)
    (Compile.forBndBodyTM_exitLoop counter sb rbody)

/-- The loop halts at its dedicated halt state `(forBndBodyTM …).states`. -/
def Compile.forBndLoopTM_exit (counter sb : Var) (rbody : CompiledCmd) : Nat :=
  (Compile.forBndBodyTM counter sb rbody).states

theorem Compile.forBndLoopTM_tapes (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndLoopTM counter sb rbody).tapes = 1 :=
  Compile.forBndBodyTM_tapes counter sb rbody

theorem Compile.forBndLoopTM_sig (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndLoopTM counter sb rbody).sig = 4 :=
  Compile.forBndBodyTM_sig counter sb rbody

theorem Compile.forBndLoopTM_start (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndLoopTM counter sb rbody).start = 0 :=
  Compile.forBndBodyTM_start counter sb rbody

theorem Compile.forBndLoopTM_valid (counter sb : Var) (rbody : CompiledCmd) :
    validFlatTM (Compile.forBndLoopTM counter sb rbody) :=
  loopTM_valid (Compile.forBndBodyTM counter sb rbody)
    (Compile.forBndBodyTM_exitDone counter sb rbody)
    (Compile.forBndBodyTM_exitLoop counter sb rbody)
    (Compile.forBndBodyTM_valid counter sb rbody)
    (Compile.forBndBodyTM_exitDone_lt counter sb rbody)
    (Compile.forBndBodyTM_exitLoop_lt counter sb rbody)
    (Compile.forBndBodyTM_tapes counter sb rbody)


/-- The number of states of the `forBnd` loop machine (`loopTM` adds one halt). -/
theorem Compile.forBndLoopTM_states (counter sb : Var) (rbody : CompiledCmd) :
    (Compile.forBndLoopTM counter sb rbody).states
      = (Compile.forBndBodyTM counter sb rbody).states + 1 := rfl

/-- **The `forBnd` loop as a `CompiledCmd`.** Wraps `forBndLoopTM` (a `loopTM`)
with its unique dedicated halt state (`loopTM`'s `B.states`) as the exit, mirroring
`Compile.opClear`'s wrapping of `clearRegionTM`. This is the middle fragment of the
pinned `compileForBnd` machine `copy K1 bound ⨾ loop ⨾ clear K2`. -/
def Compile.forBndLoopCmd (counter sb : Var) (rbody : CompiledCmd) : CompiledCmd where
  M := Compile.forBndLoopTM counter sb rbody
  exit := Compile.forBndLoopTM_exit counter sb rbody
  exit_lt := by
    rw [Compile.forBndLoopTM_states, Compile.forBndLoopTM_exit]; omega
  exit_is_halt := by
    show (Compile.forBndLoopTM counter sb rbody).halt[
        Compile.forBndLoopTM_exit counter sb rbody]? = some true
    change (loopHalt (Compile.forBndBodyTM counter sb rbody))[
        (Compile.forBndBodyTM counter sb rbody).states]? = some true
    show (List.replicate (Compile.forBndBodyTM counter sb rbody).states false
          ++ [true])[(Compile.forBndBodyTM counter sb rbody).states]? = some true
    rw [List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  halt_unique := by
    intro i hi
    show i = (Compile.forBndBodyTM counter sb rbody).states
    change (loopHalt (Compile.forBndBodyTM counter sb rbody))[i]? = some true at hi
    change (List.replicate (Compile.forBndBodyTM counter sb rbody).states false
          ++ [true])[i]? = some true at hi
    by_cases hlt : i < (Compile.forBndBodyTM counter sb rbody).states
    · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hlt),
          List.getElem?_replicate] at hi
      split at hi <;> simp_all
    · rw [Nat.not_lt] at hlt
      rw [List.getElem?_append_right (by rw [List.length_replicate]; exact hlt),
          List.length_replicate] at hi
      rcases hi' : i - (Compile.forBndBodyTM counter sb rbody).states with _ | n
      · omega
      · rw [hi'] at hi; simp at hi
  M_valid := Compile.forBndLoopTM_valid counter sb rbody
  M_tapes := Compile.forBndLoopTM_tapes counter sb rbody
  M_sig := Compile.forBndLoopTM_sig counter sb rbody

/-- Compile `forBnd counter bound body` from the already-compiled body,
at **static scratch base `sb`** (the 2026-06-11 re-pinned interface; the
machine is still a stub — bottom-up task, gated on the `copy`/`tail` op
gadgets).

**The pinned machine design (validated for the W-invariant ① and the
`physStepBudget` ② — see `compileForBnd_sound_physical_residue`).** The
loop count `iters = |s.get bound|` is snapshotted at entry into the
compiler-assigned scratch register `K1 = sb` (the body may legally clobber
`bound` and `counter` mid-loop, and nothing past the terminator survives a
body run, so a *register the body provably never touches* — `UsesBelow
body sb` + the eval-level frame — is the only sound storage). `K2 = sb + 1`
holds the **done** count as an all-`1`s block (`replicate i 1`), which is
exactly the value `counter` must be re-materialised to each round:

```
copy K1 bound                      -- snapshot: |K1| = iters (cursor copy)
loop {
  test K1 nonempty — exit if empty -- navigateAndTestTM-style
  copy counter K2                  -- counter := replicate i 1 (cursor copy)
  rbody                            -- one body iteration
  appendOne K2                     -- done++        (PROVEN op gadget)
  tail K1 K1                       -- remaining--   (in-place delete-head)
}
clear K2                           -- restore scratch (K1 is [] already)
```

⚠ **Both per-iteration copies MUST be the in-place cursor/marking copy**
(residue growth = `|dst₀|` only, joint size+residue growth = `|src|`), i.e.
the same gadget the `copy` op needs (bottom-up task 1). A `moveRegionTM`-based
copy (delete+insert per cell, residue `+|src|` per pass) overdraws the
W-invariant ①: its per-iteration joint growth is `~3i`, and
`iters + Σ(3i+1) ≰ 1 + iters²` already from `iters = 2` (`#eval`-checked).
With the cursor copy the total
bookkeeping joint growth is `iters(entry) + Σᵢ(i + 1) =
iters(iters−1)/2 + 2·iters ≤ 1 + iters²` — exactly `(iters−1)(iters−2) ≥ 0`,
tight at `iters ∈ {1,2}`, so the combinator proof must consume the ops'
**exact residue formulas**, not the existential W-≤ of
`compileOp_sound_physical_residue`. -/
def compileForBnd (counter bound : Var) (sb : Nat) (rbody : CompiledCmd) :
    CompiledCmd :=
  compileSeq (Compile.opCopy sb bound)
    (compileSeq (Compile.forBndLoopCmd counter sb rbody) (Compile.opClear (sb + 1)))

/-! ## The compiler -/

/-- Compile a `Cmd` to its `CompiledCmd` package, at **scratch base `sb`**.
Structural recursion over `Cmd`. Each constructor delegates to a
per-constructor helper.

`sb` is the compiler's static scratch-register assignment (re-pinned
2026-06-11, the `forBnd` snapshot-vs-clobber fix): every `forBnd` node
compiled at base `b` uses registers `b`, `b + 1` for its loop counts and
compiles its body at base `b + 2`, so the whole program touches registers
`< sb + 2 * c.loopDepth`. The caller must choose `sb` so that the *program
proper* satisfies `Cmd.UsesBelow c sb` and the input state has registers
`≥ sb` empty (the run contract `Compile.run_physical_residue_gen` carries
both; the live bridges use `sb = regBound` and discharge the emptiness from
`width_le` + the `padRegsTM` `[]`-padding). `seq`/`ifBit` pass `sb` through
unchanged — scratch is transient (each loop restores its pair to `[]`), so
siblings reuse it. -/
def compileCmd : Nat → Cmd → CompiledCmd
  | sb, .op o                 => compileOp sb o
  | sb, .seq c1 c2            => compileSeq (compileCmd sb c1) (compileCmd sb c2)
  | sb, .ifBit t cT cE        => compileIfBit t (compileCmd sb cT) (compileCmd sb cE)
  | sb, .forBnd cnt bnd body  => compileForBnd cnt bnd sb (compileCmd (sb + 2) body)

/-- Consumer-facing API: the bare TM produced by compilation at scratch base `sb`. -/
def Compile (sb : Nat) (c : Cmd) : FlatTM := (compileCmd sb c).M

/-- Consumer-facing API: the exit state of `Compile sb c`. -/
def Compile.exit (sb : Nat) (c : Cmd) : Nat := (compileCmd sb c).exit

/-- The compiled machine is valid. With the stubbed helpers this is
immediate (every case is `compiledCmd_default`); with the real
helpers it follows from the per-constructor validity of each
helper and the existing combinator-validity lemmas
(`composeFlatTM_valid`, `branchComposeFlatTM_valid`). -/
theorem Compile_valid (sb : Nat) (c : Cmd) : validFlatTM (Compile sb c) :=
  (compileCmd sb c).M_valid

theorem Compile_tapes (sb : Nat) (c : Cmd) : (Compile sb c).tapes = 1 :=
  (compileCmd sb c).M_tapes

theorem Compile_sig (sb : Nat) (c : Cmd) : (Compile sb c).sig = 4 :=
  (compileCmd sb c).M_sig
