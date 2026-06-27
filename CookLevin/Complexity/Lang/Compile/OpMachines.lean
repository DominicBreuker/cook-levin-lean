import Complexity.Lang.Semantics
import Complexity.Lang.Frame
import Complexity.Lang.AppendGadget
import Complexity.Lang.ClearGadget
import Complexity.Complexity.TMPrimitives
import Complexity.Complexity.TapeMono
import Complexity.Lang.Compile.Core

set_option autoImplicit false

/-! # `Compile/OpMachines` — the per-`Op` TM machines (defs + shape lemmas)

Extracted from `Compile.lean` (refactor Phase 1, see `REFACTOR-HANDOFF.md`).
Every `Op` constructor's compiled `FlatTM` machine plus its structural
("shape") lemmas (`_valid`/`_sig`/`_tapes`/`_exit*`/`_halt*`), which `compileOp`
dispatches to:

- append/clear: `opAppendBitRewind`, `opClear`, `opAppendOne`, `opAppendZero`.
- the in-place cursor-copy gadget and the `copy`/`tail` machines.
- `nonEmpty`, `head` (incl. `bitReadTM`/`exactOneOneTM`/`testBit*` leaves).
- the `eqBit` no-grow `compareRegsNoGrowM` tree + `opEqBit`/`opEqBitNG`.

These are the machine *constructions* only — the run/behaviour lemmas and the
soundness contracts live downstream in `Compile.lean`. The block references only
`Compile/Core` + the gadget primitives (it predates the encoding layer in the old
file order, so it is independent of `Compile/Encoding`). Former `private`
modifiers were dropped so the few cross-referenced cursor-loop entries export. -/

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators

/-- **Rewinding append op as a `CompiledCmd`** — the `rewindBracket` instance for
the append `compute` machine `appendAtTM ins dst`. Demoting the left-scan boundary
halt makes the head-`0`-rewinding append op a genuine `CompiledCmd` (`ins = 2`
for `appendOne`, `ins = 1` for `appendZero`). Its run/trajectory contract comes
from `rewindBracket_transport` (general) fed by `appendAt_twoPhaseRewind_run`/
`_no_early_halt` (`appendAtThenTwoPhaseRewindTM` is defeq to the bracket's
`compute ⨾ rewindTwoPhase`). -/
def Compile.opAppendBitRewind (ins : Nat) (h_ins : ins < 4) (dst : Var) : CompiledCmd :=
  Compile.rewindBracket (AppendGadget.appendAtTM ins dst) (AppendGadget.appendAtTM_exit dst)
    (AppendGadget.appendAtTM_valid ins h_ins dst) (AppendGadget.appendAtTM_exit_lt ins dst)
    (AppendGadget.appendAtTM_tapes ins dst) (AppendGadget.appendAtTM_sig ins dst)

/-- Compile `Op.clear dst`. The real machine: `clearRegionTM dst` from
`ClearGadget.lean` — a `loopTM` that navigates to register `dst`, tests if
it's empty, and if not, deletes the first content cell and rewinds, repeating
until the register is cleared. The loop's single halt state (at `B.states`)
is the unique exit. -/
def Compile.opClear (dst : Var) : CompiledCmd where
  M := ClearGadget.clearRegionTM dst
  exit := ClearGadget.clearRegionTM_exit dst
  exit_lt := by
    show ClearGadget.clearRegionTM_exit dst < (ClearGadget.clearRegionTM dst).states
    rw [ClearGadget.clearRegionTM_states]
    show (ClearGadget.clearBodyRawTM dst).states < (ClearGadget.clearBodyRawTM dst).states + 1
    omega
  exit_is_halt := by
    show (ClearGadget.clearRegionTM dst).halt[ClearGadget.clearRegionTM_exit dst]? = some true
    -- loopHalt B has a single `true` at B.states.
    change (loopHalt (ClearGadget.clearBodyRawTM dst))[(ClearGadget.clearBodyRawTM dst).states]? = some true
    show (List.replicate (ClearGadget.clearBodyRawTM dst).states false ++ [true])[(ClearGadget.clearBodyRawTM dst).states]? = some true
    rw [List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  halt_unique := by
    intro i hi
    show i = (ClearGadget.clearBodyRawTM dst).states
    change (loopHalt (ClearGadget.clearBodyRawTM dst))[i]? = some true at hi
    change (List.replicate (ClearGadget.clearBodyRawTM dst).states false ++ [true])[i]? = some true at hi
    by_cases hlt : i < (ClearGadget.clearBodyRawTM dst).states
    · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hlt),
          List.getElem?_replicate] at hi
      split at hi <;> simp_all
    · rw [Nat.not_lt] at hlt
      rw [List.getElem?_append_right (by rw [List.length_replicate]; exact hlt),
          List.length_replicate] at hi
      rcases hi' : i - (ClearGadget.clearBodyRawTM dst).states with _ | n
      · omega
      · rw [hi'] at hi; simp at hi
  M_valid := ClearGadget.clearRegionTM_valid dst
  M_tapes := ClearGadget.clearRegionTM_tapes dst
  M_sig := ClearGadget.clearRegionTM_sig dst

/-- Compile `Op.appendOne dst`: navigate past the `dst` preceding
register-delimiters, insert symbol `2` (the shifted bit `1`) just before register
`dst`'s delimiter, then **two-phase rewind the head back to `0`** (so the fragment
composes — `compileSeq` needs each fragment's head at the leading sentinel). The
unique-halt `CompiledCmd` comes from `opAppendBitRewind` (the `rewindBracket`
instance that demotes the left-scan's boundary halt). Its residue-tolerant
physical contract is `opAppendBit_physical_residue`. -/
def Compile.opAppendOne (dst : Var) : CompiledCmd :=
  Compile.opAppendBitRewind 2 (by decide) dst

/-- Compile `Op.appendZero dst`: as `opAppendOne`, but inserts symbol `1`
(the shifted bit `0`). -/
def Compile.opAppendZero (dst : Var) : CompiledCmd :=
  Compile.opAppendBitRewind 1 (by decide) dst

/-! ### Class-A op machinery: `copy`/`tail` — the in-place cursor-copy gadget

The W-invariant ① forbids move-based copying (every `moveRegionTM` pass appends
`|src|` zeros to the residue), and the pinned per-op contract has no scratch
register. The forced — and `#eval`-probe-validated (`probes/CursorCopyProbe.lean`,
2026-06-11) — design is the **in-place marking/cursor read**:

`copyRegionFullTM dst src` (`dst ≠ src`) =
  `clearRegionTM dst ⨾ navigateToRegTM src ⨾ loopTM(cursor body) ⨾ justRewind`

The cursor body starts with the head ON the next unprocessed cell of `src`
(`markReadTM`): a `0` delimiter → the DONE exit; a shifted bit `b+1` → overwrite
it with the mark `endMark = 3` and run the per-bit pipeline `copyPipeTM b dst`:
step left off the mark, scan left to the leading sentinel, `appendAtTM (b+1) dst`
(its existing run lemmas tolerate the interior `3` verbatim: `skipped` blocks and
`post` only need `≠ 0` / `< 4`), then return — scan left from the tape end to the
*trailing terminator*, step left, scan left to the *mark* (the only interior `3`),
restore `b+1` over it and step right onto the next cursor. The marked tape is
`encodeTape` of a state with one `2`-valued cell, so the `encodeTape` structure
lemmas apply; the loop adds NO residue (insertions grow the encoded region).

Residue: exactly the clear phase's `replicate |dst₀| 0`.
`copy dst dst` is a compile-time no-op (`compiledCmd_default`); `tail dst dst`
is one clear-style delete (`clearBodyRawTM` with both exits joined); `tail dst
src` (`dst ≠ src`) is the same machine with a `skipReadTM` pre-stage stepping
over `src`'s first cell before entering the cursor loop. -/

/-- `markBitTM` entry: shifted bit `b+1` → write the mark `3`, exit `1+b`. -/
def Compile.markBitEntry (b : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some (b + 1)], dst_state := 1 + b,
    dst_write_vals := [some 3], move_dirs := [TMMove.Nmove] }

/-- Read a CONTENT cursor cell (head ON it; the delimiter case is dispatched by
an outer `delimTestTM` branch): shifted bit `b+1` → write the mark `3` over it,
exit `1+b`. Head does not move. The marking analogue of `bitReadTM`. -/
def Compile.markBitTM : FlatTM where
  sig := 4
  tapes := 1
  states := 3
  trans := [Compile.markBitEntry 0, Compile.markBitEntry 1]
  start := 0
  halt := [false, true, true]

def Compile.markBitTM_exit (b : Nat) : Nat := 1 + b

theorem Compile.markBitTM_tapes : Compile.markBitTM.tapes = 1 := rfl
theorem Compile.markBitTM_start : Compile.markBitTM.start = 0 := rfl
theorem Compile.markBitTM_sig : Compile.markBitTM.sig = 4 := rfl
theorem Compile.markBitTM_states : Compile.markBitTM.states = 3 := rfl

theorem Compile.markBitTM_valid : validFlatTM Compile.markBitTM := by
  refine ⟨show (0 : Nat) < 3 from by decide, rfl, ?_⟩
  intro entry hentry
  rcases List.mem_cons.mp hentry with h1 | hrest'
  · subst h1
    refine ⟨show (0:Nat) < 3 from by decide, show (1:Nat) < 3 from by decide,
      rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp [Compile.markBitEntry] at hx; subst hx; decide
    · intro x hx; simp [Compile.markBitEntry] at hx; subst hx; decide
  · rcases List.mem_cons.mp hrest' with h2 | hnil
    · subst h2
      refine ⟨show (0:Nat) < 3 from by decide, show (2:Nat) < 3 from by decide,
        rfl, rfl, rfl, ?_, ?_⟩
      · intro x hx; simp [Compile.markBitEntry] at hx; subst hx; decide
      · intro x hx; simp [Compile.markBitEntry] at hx; subst hx; decide
    · exact absurd hnil (by simp)

/-- The trivial immediate-halt machine (a branch body that does nothing —
its start state IS its unique halt state). -/
def Compile.idTM : FlatTM where
  sig := 4
  tapes := 1
  states := 1
  trans := []
  start := 0
  halt := [true]

theorem Compile.idTM_valid : validFlatTM Compile.idTM := by
  refine ⟨by decide, rfl, ?_⟩
  intro entry hentry
  exact absurd hentry (by simp [Compile.idTM])

/-- `restoreStepTM b` entry: at the mark `3`, write `b+1` back and move right. -/
def Compile.restoreStepEntry (b : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some 3], dst_state := 1,
    dst_write_vals := [some (b + 1)], move_dirs := [TMMove.Rmove] }

/-- At the mark: restore the shifted bit `b+1` over the `3` and step right onto
the next cursor cell. -/
def Compile.restoreStepTM (b : Nat) : FlatTM where
  sig := 4
  tapes := 1
  states := 2
  trans := [Compile.restoreStepEntry b]
  start := 0
  halt := [false, true]

theorem Compile.restoreStepTM_tapes (b : Nat) : (Compile.restoreStepTM b).tapes = 1 := rfl
theorem Compile.restoreStepTM_states (b : Nat) : (Compile.restoreStepTM b).states = 2 := rfl

theorem Compile.restoreStepTM_valid (b : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.restoreStepTM b) := by
  refine ⟨show (0 : Nat) < 2 from by decide, rfl, ?_⟩
  intro entry hentry
  rcases List.mem_cons.mp hentry with h0 | hnil
  · subst h0
    refine ⟨show (0:Nat) < 2 from by decide, show (1:Nat) < 2 from by decide,
      rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp [Compile.restoreStepEntry] at hx; subst hx
      show (3 : Nat) < 4; decide
    · intro x hx; simp [Compile.restoreStepEntry] at hx; subst hx
      show b + 1 < 4; omega
  · exact absurd hnil (by simp)

/-- `skipReadTM` entry: `0` delimiter → exit `1` (src empty, no move). -/
def Compile.skipReadDelimEntry : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some 0], dst_state := 1,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

/-- `skipReadTM` entry: content cell `v ∈ {1,2}` → step right, exit `2`. -/
def Compile.skipReadBitEntry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some v], dst_state := 2,
    dst_write_vals := [none], move_dirs := [TMMove.Rmove] }

/-- Skip `src`'s first cell (for `tail`): `0` → exit `1` (src empty); a content
cell → step right onto the second cell, exit `2`. -/
def Compile.skipReadTM : FlatTM where
  sig := 4
  tapes := 1
  states := 3
  trans := [Compile.skipReadDelimEntry, Compile.skipReadBitEntry 1,
            Compile.skipReadBitEntry 2]
  start := 0
  halt := [false, true, true]

def Compile.skipReadTM_exit_empty : Nat := 1
def Compile.skipReadTM_exit_bit : Nat := 2

theorem Compile.skipReadTM_tapes : Compile.skipReadTM.tapes = 1 := rfl
theorem Compile.skipReadTM_states : Compile.skipReadTM.states = 3 := rfl

theorem Compile.skipReadTM_valid : validFlatTM Compile.skipReadTM := by
  refine ⟨show (0 : Nat) < 3 from by decide, rfl, ?_⟩
  intro entry hentry
  rcases List.mem_cons.mp hentry with h0 | hrest
  · subst h0
    refine ⟨show (0:Nat) < 3 from by decide, show (1:Nat) < 3 from by decide,
      rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp [Compile.skipReadDelimEntry] at hx; subst hx; decide
    · intro x hx; simp [Compile.skipReadDelimEntry] at hx; subst hx; trivial
  · rcases List.mem_cons.mp hrest with h1 | hrest'
    · subst h1
      refine ⟨show (0:Nat) < 3 from by decide, show (2:Nat) < 3 from by decide,
        rfl, rfl, rfl, ?_, ?_⟩
      · intro x hx; simp [Compile.skipReadBitEntry] at hx; subst hx; decide
      · intro x hx; simp [Compile.skipReadBitEntry] at hx; subst hx; trivial
    · rcases List.mem_cons.mp hrest' with h2 | hnil
      · subst h2
        refine ⟨show (0:Nat) < 3 from by decide, show (2:Nat) < 3 from by decide,
          rfl, rfl, rfl, ?_, ?_⟩
        · intro x hx; simp [Compile.skipReadBitEntry] at hx; subst hx; decide
        · intro x hx; simp [Compile.skipReadBitEntry] at hx; subst hx; trivial
      · exact absurd hnil (by simp)

/-- `appendAtTM`'s state count: `9` (scanner `3` + inserter `6`) plus `3` per
skipped register. So `appendAtTM_exit dst = 8 + 3·dst` is its last state. -/
theorem Compile.appendAtTM_states (ins : Nat) :
    ∀ dst, (AppendGadget.appendAtTM ins dst).states = 9 + 3 * dst
  | 0     => rfl
  | d + 1 => by
      show (composeFlatTM _ (AppendGadget.appendAtTM ins d) _).states = _
      rw [composeFlatTM_states, Compile.appendAtTM_states ins d]
      show 3 + (9 + 3 * d) = 9 + 3 * (d + 1); omega

/-- A `branchComposeFlatTM` of two unique-halt sub-machines has exactly the two
shifted branch exits as halt states. -/
theorem Compile.branchComposeFlatTM_halt_only (M₁ M₂ M₃ : FlatTM) (ep en e₂ e₃ : Nat)
    (h2v : validFlatTM M₂) (h3v : validFlatTM M₃)
    (h2 : ∀ i, M₂.halt[i]? = some true → i = e₂)
    (h3 : ∀ i, M₃.halt[i]? = some true → i = e₃) :
    ∀ i, (branchComposeFlatTM M₁ M₂ M₃ ep en).halt[i]? = some true →
      i = M₁.states + e₂ ∨ i = M₁.states + M₂.states + e₃ := by
  intro i hi
  change (composedBranchHalt M₁ M₂ M₃)[i]? = some true at hi
  unfold composedBranchHalt at hi
  rw [List.append_assoc] at hi
  by_cases h1 : i < M₁.states
  · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact h1),
        List.getElem?_replicate] at hi
    simp [h1] at hi
  · rw [Nat.not_lt] at h1
    rw [List.getElem?_append_right (by rw [List.length_replicate]; exact h1),
        List.length_replicate] at hi
    by_cases h2lt : i - M₁.states < M₂.states
    · left
      rw [List.getElem?_append_left (by rw [h2v.2.1]; exact h2lt)] at hi
      have := h2 _ hi; omega
    · rw [Nat.not_lt] at h2lt
      rw [List.getElem?_append_right (by rw [h2v.2.1]; exact h2lt), h2v.2.1] at hi
      have := h3 _ hi; omega

/-- **Variant allowing a 2-exit negative branch `M₃`** (d2b-prep, Risk C2). A
`branchComposeFlatTM` whose positive branch `M₂` is halt-unique (`e₂`) but whose
negative branch `M₃` is a *nested 2-exit tester* (halts only at `e₃a` or `e₃b`)
has exactly the **three** shifted exits as halt states. This is the keystone for
every nested 2-exit machine (the `eqBit` verdict nests `navTestRewindM sc2` as
`M₃`; the consume-loop testMachine nests one likewise). Its proof is the parent
lemma's, with the single `M₃` exit split into two by `rcases … <;> omega`. -/
theorem Compile.branchComposeFlatTM_halt_only_M3two (M₁ M₂ M₃ : FlatTM)
    (ep en e₂ e₃a e₃b : Nat)
    (h2v : validFlatTM M₂) (h3v : validFlatTM M₃)
    (h2 : ∀ i, M₂.halt[i]? = some true → i = e₂)
    (h3 : ∀ i, M₃.halt[i]? = some true → i = e₃a ∨ i = e₃b) :
    ∀ i, (branchComposeFlatTM M₁ M₂ M₃ ep en).halt[i]? = some true →
      i = M₁.states + e₂ ∨ i = M₁.states + M₂.states + e₃a ∨
        i = M₁.states + M₂.states + e₃b := by
  intro i hi
  change (composedBranchHalt M₁ M₂ M₃)[i]? = some true at hi
  unfold composedBranchHalt at hi
  rw [List.append_assoc] at hi
  by_cases h1 : i < M₁.states
  · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact h1),
        List.getElem?_replicate] at hi
    simp [h1] at hi
  · rw [Nat.not_lt] at h1
    rw [List.getElem?_append_right (by rw [List.length_replicate]; exact h1),
        List.length_replicate] at hi
    by_cases h2lt : i - M₁.states < M₂.states
    · left
      rw [List.getElem?_append_left (by rw [h2v.2.1]; exact h2lt)] at hi
      have := h2 _ hi; omega
    · rw [Nat.not_lt] at h2lt
      rw [List.getElem?_append_right (by rw [h2v.2.1]; exact h2lt), h2v.2.1] at hi
      rcases h3 _ hi with h | h <;> omega

/-- **Variant allowing 2-exit branches on BOTH sides** (d2a, Risk C2). A
`branchComposeFlatTM` whose positive branch `M₂` AND negative branch `M₃` are each
nested 2-exit testers has exactly the **four** shifted exits as halt states. Needed
for the `eqBit` bit-comparison body (read both bits, `M₂`/`M₃` each branch
MATCH/NOMATCH) and the consume-loop body (each side ITER/DONE). Proof is the parent
lemma's, both single `M₂`/`M₃` exits split into two by `rcases … <;> omega`. -/
theorem Compile.branchComposeFlatTM_halt_only_M2two_M3two (M₁ M₂ M₃ : FlatTM)
    (ep en e₂a e₂b e₃a e₃b : Nat)
    (h2v : validFlatTM M₂) (h3v : validFlatTM M₃)
    (h2 : ∀ i, M₂.halt[i]? = some true → i = e₂a ∨ i = e₂b)
    (h3 : ∀ i, M₃.halt[i]? = some true → i = e₃a ∨ i = e₃b) :
    ∀ i, (branchComposeFlatTM M₁ M₂ M₃ ep en).halt[i]? = some true →
      i = M₁.states + e₂a ∨ i = M₁.states + e₂b ∨
        i = M₁.states + M₂.states + e₃a ∨ i = M₁.states + M₂.states + e₃b := by
  intro i hi
  change (composedBranchHalt M₁ M₂ M₃)[i]? = some true at hi
  unfold composedBranchHalt at hi
  rw [List.append_assoc] at hi
  by_cases h1 : i < M₁.states
  · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact h1),
        List.getElem?_replicate] at hi
    simp [h1] at hi
  · rw [Nat.not_lt] at h1
    rw [List.getElem?_append_right (by rw [List.length_replicate]; exact h1),
        List.length_replicate] at hi
    by_cases h2lt : i - M₁.states < M₂.states
    · rw [List.getElem?_append_left (by rw [h2v.2.1]; exact h2lt)] at hi
      rcases h2 _ hi with h | h <;> omega
    · rw [Nat.not_lt] at h2lt
      rw [List.getElem?_append_right (by rw [h2v.2.1]; exact h2lt), h2v.2.1] at hi
      rcases h3 _ hi with h | h <;> omega

/-- **Variant allowing a 2-exit POSITIVE branch `M₂`** (mirror of `_M3two`). A
`branchComposeFlatTM` whose positive branch `M₂` is a nested 2-exit tester
(`e₂a`/`e₂b`) but whose negative branch `M₃` is halt-unique (`e₃`) has exactly the
**three** shifted exits as halt states. Needed for the `eqBit` consume-loop's
`testMachine` (the "both nonempty?" guard and the bitCompare wrapper each put a
2-exit tester in the positive slot and `idTM` in the negative). -/
theorem Compile.branchComposeFlatTM_halt_only_M2two (M₁ M₂ M₃ : FlatTM)
    (ep en e₂a e₂b e₃ : Nat)
    (h2v : validFlatTM M₂) (h3v : validFlatTM M₃)
    (h2 : ∀ i, M₂.halt[i]? = some true → i = e₂a ∨ i = e₂b)
    (h3 : ∀ i, M₃.halt[i]? = some true → i = e₃) :
    ∀ i, (branchComposeFlatTM M₁ M₂ M₃ ep en).halt[i]? = some true →
      i = M₁.states + e₂a ∨ i = M₁.states + e₂b ∨ i = M₁.states + M₂.states + e₃ := by
  intro i hi
  change (composedBranchHalt M₁ M₂ M₃)[i]? = some true at hi
  unfold composedBranchHalt at hi
  rw [List.append_assoc] at hi
  by_cases h1 : i < M₁.states
  · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact h1),
        List.getElem?_replicate] at hi
    simp [h1] at hi
  · rw [Nat.not_lt] at h1
    rw [List.getElem?_append_right (by rw [List.length_replicate]; exact h1),
        List.length_replicate] at hi
    by_cases h2lt : i - M₁.states < M₂.states
    · rw [List.getElem?_append_left (by rw [h2v.2.1]; exact h2lt)] at hi
      rcases h2 _ hi with h | h <;> omega
    · rw [Nat.not_lt] at h2lt
      rw [List.getElem?_append_right (by rw [h2v.2.1]; exact h2lt), h2v.2.1] at hi
      have := h3 _ hi; omega

/-- A halt state of `M₂` (with `e₂ < M₂.states`) shifts to a halt of the
branch composite (positive branch). -/
theorem Compile.branchComposeFlatTM_M2_halt_intro (M₁ M₂ M₃ : FlatTM) (ep en e₂ : Nat)
    (h2v : validFlatTM M₂) (he : e₂ < M₂.states) (h : M₂.halt[e₂]? = some true) :
    (branchComposeFlatTM M₁ M₂ M₃ ep en).halt[M₁.states + e₂]? = some true := by
  change (composedBranchHalt M₁ M₂ M₃)[M₁.states + e₂]? = some true
  unfold composedBranchHalt
  rw [List.append_assoc,
      List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate, Nat.add_sub_cancel_left,
      List.getElem?_append_left (by rw [h2v.2.1]; exact he)]
  exact h

/-- A halt state of `M₃` shifts to a halt of the branch composite (negative
branch). -/
theorem Compile.branchComposeFlatTM_M3_halt_intro (M₁ M₂ M₃ : FlatTM) (ep en e₃ : Nat)
    (h2v : validFlatTM M₂) (h : M₃.halt[e₃]? = some true) :
    (branchComposeFlatTM M₁ M₂ M₃ ep en).halt[M₁.states + M₂.states + e₃]? = some true := by
  change (composedBranchHalt M₁ M₂ M₃)[M₁.states + M₂.states + e₃]? = some true
  unfold composedBranchHalt
  have hlen : (List.replicate M₁.states false ++ M₂.halt).length = M₁.states + M₂.states := by
    rw [List.length_append, List.length_replicate, h2v.2.1]
  rw [List.getElem?_append_right (by rw [hlen]; omega), hlen,
      show M₁.states + M₂.states + e₃ - (M₁.states + M₂.states) = e₃ by omega]
  exact h

/-- `composeFlatTM` inherits a unique halt from `M₂`'s unique halt. -/
theorem Compile.composeFlatTM_halt_unique (M₁ M₂ : FlatTM) (e₂ exit : Nat)
    (h2 : ∀ i, M₂.halt[i]? = some true → i = e₂) :
    ∀ i, (composeFlatTM M₁ M₂ exit).halt[i]? = some true → i = M₁.states + e₂ := by
  intro i hi
  obtain ⟨hge, hh⟩ := ScanLeft.composeFlatTM_halt_some_imp M₁ M₂ exit i hi
  have := h2 _ hh; omega

/-- Pipeline stage 1–2: step off the mark, scan left to the leading sentinel.
States `5`, exit `3` (the scan's found state, shifted). -/
def Compile.copyRet1TM : FlatTM :=
  composeFlatTM (ScanLeft.stepLeftTM 4) (ScanLeft.scanLeftUntilTM 4 3) 1

theorem Compile.copyRet1TM_states : Compile.copyRet1TM.states = 5 := rfl
theorem Compile.copyRet1TM_start : Compile.copyRet1TM.start = 0 := rfl
theorem Compile.copyRet1TM_tapes : Compile.copyRet1TM.tapes = 1 := rfl
theorem Compile.copyRet1TM_sig : Compile.copyRet1TM.sig = 4 := rfl

theorem Compile.copyRet1TM_valid : validFlatTM Compile.copyRet1TM :=
  composeFlatTM_valid _ _ _ (ScanLeft.stepLeftTM_valid 4)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide)) (by decide) rfl rfl

/-- Pipeline stages 1–3: … then `appendAtTM (b+1) dst` (append the bit to
`dst`'s end). States `14 + 3·dst`, exit `5 + appendAtTM_exit dst = 13 + 3·dst`. -/
def Compile.copyPipeA2TM (b dst : Nat) : FlatTM :=
  composeFlatTM Compile.copyRet1TM (AppendGadget.appendAtTM (b + 1) dst) 3

theorem Compile.copyPipeA2TM_states (b dst : Nat) :
    (Compile.copyPipeA2TM b dst).states = 14 + 3 * dst := by
  show (composeFlatTM _ _ _).states = _
  rw [composeFlatTM_states, Compile.copyRet1TM_states, Compile.appendAtTM_states]
  omega

theorem Compile.copyPipeA2TM_valid (b dst : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.copyPipeA2TM b dst) :=
  composeFlatTM_valid _ _ _ Compile.copyRet1TM_valid
    (AppendGadget.appendAtTM_valid (b + 1) (by omega) dst)
    (by rw [Compile.copyRet1TM_states]; decide) Compile.copyRet1TM_tapes
    (AppendGadget.appendAtTM_tapes _ dst)

/-- Stages 1–4: … then scan left from the tape end to the trailing terminator.
States `17 + 3·dst`, exit `15 + 3·dst`. -/
def Compile.copyPipeA3TM (b dst : Nat) : FlatTM :=
  composeFlatTM (Compile.copyPipeA2TM b dst) (ScanLeft.scanLeftUntilTM 4 3) (13 + 3 * dst)

theorem Compile.copyPipeA3TM_states (b dst : Nat) :
    (Compile.copyPipeA3TM b dst).states = 17 + 3 * dst := by
  show (composeFlatTM _ _ _).states = _
  rw [composeFlatTM_states, Compile.copyPipeA2TM_states]
  show 14 + 3 * dst + 3 = 17 + 3 * dst; omega

theorem Compile.copyPipeA3TM_valid (b dst : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.copyPipeA3TM b dst) :=
  composeFlatTM_valid _ _ _ (Compile.copyPipeA2TM_valid b dst hb)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (by show (13 + 3 * dst : Nat) < (Compile.copyPipeA2TM b dst).states
        rw [Compile.copyPipeA2TM_states]; omega) Compile.copyRet1TM_tapes rfl

/-- Stages 1–5: … then step left off the trailing terminator.
States `19 + 3·dst`, exit `18 + 3·dst`. -/
def Compile.copyPipeA4TM (b dst : Nat) : FlatTM :=
  composeFlatTM (Compile.copyPipeA3TM b dst) (ScanLeft.stepLeftTM 4) (15 + 3 * dst)

theorem Compile.copyPipeA4TM_states (b dst : Nat) :
    (Compile.copyPipeA4TM b dst).states = 19 + 3 * dst := by
  show (composeFlatTM _ _ _).states = _
  rw [composeFlatTM_states, Compile.copyPipeA3TM_states]
  show 17 + 3 * dst + 2 = 19 + 3 * dst; omega

theorem Compile.copyPipeA4TM_valid (b dst : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.copyPipeA4TM b dst) :=
  composeFlatTM_valid _ _ _ (Compile.copyPipeA3TM_valid b dst hb)
    (ScanLeft.stepLeftTM_valid 4)
    (by show (15 + 3 * dst : Nat) < (Compile.copyPipeA3TM b dst).states
        rw [Compile.copyPipeA3TM_states]; omega) Compile.copyRet1TM_tapes rfl

/-- Stages 1–6: … then scan left to the mark (the only interior `3`).
States `22 + 3·dst`, exit `20 + 3·dst`. -/
def Compile.copyPipeA5TM (b dst : Nat) : FlatTM :=
  composeFlatTM (Compile.copyPipeA4TM b dst) (ScanLeft.scanLeftUntilTM 4 3) (18 + 3 * dst)

theorem Compile.copyPipeA5TM_states (b dst : Nat) :
    (Compile.copyPipeA5TM b dst).states = 22 + 3 * dst := by
  show (composeFlatTM _ _ _).states = _
  rw [composeFlatTM_states, Compile.copyPipeA4TM_states]
  show 19 + 3 * dst + 3 = 22 + 3 * dst; omega

theorem Compile.copyPipeA5TM_valid (b dst : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.copyPipeA5TM b dst) :=
  composeFlatTM_valid _ _ _ (Compile.copyPipeA4TM_valid b dst hb)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (by show (18 + 3 * dst : Nat) < (Compile.copyPipeA4TM b dst).states
        rw [Compile.copyPipeA4TM_states]; omega) Compile.copyRet1TM_tapes rfl

/-- The full per-bit pipeline (head starts ON the freshly written mark):
`stepLeft ⨾ scanLeft₃ ⨾ appendAtTM (b+1) dst ⨾ scanLeft₃ ⨾ stepLeft ⨾
scanLeft₃ ⨾ restoreStep b`. States: `24 + 3·dst`; exit `23 + 3·dst`
(`restoreStepTM`'s halt, shifted — the unique halt state). -/
def Compile.copyPipeTM (b dst : Nat) : FlatTM :=
  composeFlatTM (Compile.copyPipeA5TM b dst) (Compile.restoreStepTM b) (20 + 3 * dst)

def Compile.copyPipeTM_exit (dst : Nat) : Nat := 23 + 3 * dst

theorem Compile.copyPipeTM_states (b dst : Nat) :
    (Compile.copyPipeTM b dst).states = 24 + 3 * dst := by
  show (composeFlatTM _ _ _).states = _
  rw [composeFlatTM_states, Compile.copyPipeA5TM_states]
  show 22 + 3 * dst + 2 = 24 + 3 * dst; omega

theorem Compile.copyPipeTM_tapes (b dst : Nat) : (Compile.copyPipeTM b dst).tapes = 1 := rfl
theorem Compile.copyPipeTM_start (b dst : Nat) : (Compile.copyPipeTM b dst).start = 0 := rfl

theorem Compile.copyPipeA2TM_sig (b dst : Nat) : (Compile.copyPipeA2TM b dst).sig = 4 := by
  show max Compile.copyRet1TM.sig (AppendGadget.appendAtTM (b + 1) dst).sig = 4
  rw [AppendGadget.appendAtTM_sig]
  rfl

theorem Compile.copyPipeA3TM_sig (b dst : Nat) : (Compile.copyPipeA3TM b dst).sig = 4 := by
  show max (Compile.copyPipeA2TM b dst).sig (ScanLeft.scanLeftUntilTM 4 3).sig = 4
  rw [Compile.copyPipeA2TM_sig]
  rfl

theorem Compile.copyPipeA4TM_sig (b dst : Nat) : (Compile.copyPipeA4TM b dst).sig = 4 := by
  show max (Compile.copyPipeA3TM b dst).sig (ScanLeft.stepLeftTM 4).sig = 4
  rw [Compile.copyPipeA3TM_sig]
  rfl

theorem Compile.copyPipeA5TM_sig (b dst : Nat) : (Compile.copyPipeA5TM b dst).sig = 4 := by
  show max (Compile.copyPipeA4TM b dst).sig (ScanLeft.scanLeftUntilTM 4 3).sig = 4
  rw [Compile.copyPipeA4TM_sig]
  rfl

theorem Compile.copyPipeTM_sig (b dst : Nat) : (Compile.copyPipeTM b dst).sig = 4 := by
  show max (Compile.copyPipeA5TM b dst).sig (Compile.restoreStepTM b).sig = 4
  rw [Compile.copyPipeA5TM_sig]
  rfl

theorem Compile.copyPipeTM_valid (b dst : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.copyPipeTM b dst) :=
  composeFlatTM_valid _ _ _ (Compile.copyPipeA5TM_valid b dst hb)
    (Compile.restoreStepTM_valid b hb)
    (by show (20 + 3 * dst : Nat) < (Compile.copyPipeA5TM b dst).states
        rw [Compile.copyPipeA5TM_states]; omega) Compile.copyRet1TM_tapes rfl

/-- The pipeline's exit is a halt state (`restoreStepTM`'s halt `1`, shifted by
`copyPipeA5TM.states = 22 + 3·dst`). -/
theorem Compile.copyPipeTM_exit_is_halt (b dst : Nat) :
    (Compile.copyPipeTM b dst).halt[Compile.copyPipeTM_exit dst]? = some true := by
  have h := AppendGadget.composeFlatTM_shifted_is_halt
    (Compile.copyPipeA5TM b dst) (Compile.restoreStepTM b) (20 + 3 * dst) 1 (by rfl)
  rw [Compile.copyPipeA5TM_states] at h
  show (Compile.copyPipeTM b dst).halt[23 + 3 * dst]? = some true
  rw [show 23 + 3 * dst = 22 + 3 * dst + 1 from by omega]
  exact h

/-- The pipeline's halt is unique (only `restoreStepTM`'s halt survives the
`composedHalt` zeroing). -/
theorem Compile.copyPipeTM_halt_unique (b dst : Nat) :
    ∀ i, (Compile.copyPipeTM b dst).halt[i]? = some true →
      i = Compile.copyPipeTM_exit dst := by
  intro i hi
  have h := Compile.composeFlatTM_halt_unique (Compile.copyPipeA5TM b dst)
    (Compile.restoreStepTM b) 1 (20 + 3 * dst)
    (by intro j hj
        change ([false, true] : List Bool)[j]? = some true at hj
        rcases j with _ | _ | j <;> simp_all) i hi
  rw [Compile.copyPipeA5TM_states] at h
  show i = 23 + 3 * dst
  omega

/-- The content half of the cursor-loop body, raw: `markBitTM` branched into
the two per-bit pipelines. States: `3 + 2·(24 + 3·dst) = 51 + 6·dst`. -/
def Compile.copyContentRawTM (dst : Nat) : FlatTM :=
  branchComposeFlatTM Compile.markBitTM
    (Compile.copyPipeTM 0 dst) (Compile.copyPipeTM 1 dst)
    (Compile.markBitTM_exit 0) (Compile.markBitTM_exit 1)

/-- The bit-0 pipeline's exit (the kept exit after the join). -/
def Compile.copyContent_exit0 (dst : Nat) : Nat := 3 + Compile.copyPipeTM_exit dst
/-- The bit-1 pipeline's exit (demoted into `copyContent_exit0` by the join). -/
def Compile.copyContent_exit1 (dst : Nat) : Nat :=
  3 + (24 + 3 * dst) + Compile.copyPipeTM_exit dst

theorem Compile.copyContentRawTM_states (dst : Nat) :
    (Compile.copyContentRawTM dst).states = 51 + 6 * dst := by
  show (branchComposeFlatTM _ _ _ _ _).states = _
  rw [branchComposeFlatTM_states, Compile.markBitTM_states,
      Compile.copyPipeTM_states, Compile.copyPipeTM_states]
  omega

theorem Compile.copyContentRawTM_valid (dst : Nat) :
    validFlatTM (Compile.copyContentRawTM dst) :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.markBitTM_valid
    (Compile.copyPipeTM_valid 0 dst (by decide)) (Compile.copyPipeTM_valid 1 dst (by decide))
    (by rw [Compile.markBitTM_states]; decide) (by rw [Compile.markBitTM_states]; decide)
    Compile.markBitTM_tapes (Compile.copyPipeTM_tapes 0 dst) (Compile.copyPipeTM_tapes 1 dst)

theorem Compile.copyContentRawTM_sig (dst : Nat) : (Compile.copyContentRawTM dst).sig = 4 := by
  show max Compile.markBitTM.sig
    (max (Compile.copyPipeTM 0 dst).sig (Compile.copyPipeTM 1 dst).sig) = 4
  rw [Compile.markBitTM_sig, Compile.copyPipeTM_sig, Compile.copyPipeTM_sig]
  rfl

theorem Compile.copyContentRawTM_tapes (dst : Nat) : (Compile.copyContentRawTM dst).tapes = 1 :=
  Compile.markBitTM_tapes

/-- The content half with the two pipeline exits merged (`exit1 → exit0`). -/
def Compile.copyContentTM (dst : Nat) : FlatTM :=
  Compile.joinTwoHalts (Compile.copyContentRawTM dst)
    (Compile.copyContent_exit0 dst) (Compile.copyContent_exit1 dst)

theorem Compile.copyContentTM_states (dst : Nat) :
    (Compile.copyContentTM dst).states = 51 + 6 * dst := Compile.copyContentRawTM_states dst

theorem Compile.copyContentTM_valid (dst : Nat) : validFlatTM (Compile.copyContentTM dst) :=
  Compile.joinTwoHalts_valid _ _ _ (Compile.copyContentRawTM_valid dst)
    (by rw [Compile.copyContentRawTM_states]
        show 3 + (23 + 3 * dst) < 51 + 6 * dst; omega)
    (by rw [Compile.copyContentRawTM_states]
        show 3 + (24 + 3 * dst) + (23 + 3 * dst) < 51 + 6 * dst; omega)
    (Compile.copyContentRawTM_tapes dst)

/-- The cursor-loop body: outer `delimTestTM` branch — content cell → the
marked-copy pass (`copyContentTM`, M₂ slot), delimiter (src exhausted) → the
trivial `idTM` (M₃ slot). States: `3 + (51 + 6·dst) + 1 = 55 + 6·dst`. The two
`loopTM` exits: ITERATE = `29 + 3·dst` (contentTM's kept exit, shifted), DONE =
`54 + 6·dst` (`idTM`'s start/halt, shifted). -/
def Compile.copyBodyTM (dst : Nat) : FlatTM :=
  branchComposeFlatTM (ClearGadget.delimTestTM 4) (Compile.copyContentTM dst) Compile.idTM
    ClearGadget.delimTestTM_exit_content ClearGadget.delimTestTM_exit_delim

def Compile.copyBody_exitLoop (dst : Nat) : Nat := 29 + 3 * dst
def Compile.copyBody_exitDone (dst : Nat) : Nat := 54 + 6 * dst

theorem Compile.copyBodyTM_states (dst : Nat) :
    (Compile.copyBodyTM dst).states = 55 + 6 * dst := by
  show (branchComposeFlatTM _ _ _ _ _).states = _
  rw [branchComposeFlatTM_states, ClearGadget.delimTestTM_states,
      Compile.copyContentTM_states]
  show 3 + (51 + 6 * dst) + 1 = 55 + 6 * dst; omega

theorem Compile.copyBodyTM_valid (dst : Nat) : validFlatTM (Compile.copyBodyTM dst) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.delimTestTM_valid 4 (by decide))
    (Compile.copyContentTM_valid dst) Compile.idTM_valid
    (by rw [ClearGadget.delimTestTM_states]; decide)
    (by rw [ClearGadget.delimTestTM_states]; decide)
    (ClearGadget.delimTestTM_tapes 4) (Compile.copyContentRawTM_tapes dst) rfl

theorem Compile.copyBodyTM_sig (dst : Nat) : (Compile.copyBodyTM dst).sig = 4 := by
  show max (ClearGadget.delimTestTM 4).sig
    (max (Compile.copyContentTM dst).sig Compile.idTM.sig) = 4
  rw [ClearGadget.delimTestTM_sig]
  show max 4 (max (Compile.copyContentRawTM dst).sig 4) = 4
  rw [Compile.copyContentRawTM_sig]
  rfl

theorem Compile.copyBodyTM_tapes (dst : Nat) : (Compile.copyBodyTM dst).tapes = 1 :=
  ClearGadget.delimTestTM_tapes 4

/-- `copyContentTM`'s kept exit is a halt state (pipe-0's exit, shifted past
`markBitTM`, surviving the join). -/
theorem Compile.copyContentTM_exit_is_halt (dst : Nat) :
    (Compile.copyContentTM dst).halt[Compile.copyContent_exit0 dst]? = some true := by
  refine Compile.joinTwoHalts_h1_is_halt _ _ _ ?_ ?_
  · show 3 + (23 + 3 * dst) ≠ 3 + (24 + 3 * dst) + (23 + 3 * dst); omega
  · have h := Compile.branchComposeFlatTM_M2_halt_intro Compile.markBitTM
      (Compile.copyPipeTM 0 dst) (Compile.copyPipeTM 1 dst)
      (Compile.markBitTM_exit 0) (Compile.markBitTM_exit 1)
      (Compile.copyPipeTM_exit dst)
      (Compile.copyPipeTM_valid 0 dst (by decide))
      (by rw [Compile.copyPipeTM_states]
          show 23 + 3 * dst < 24 + 3 * dst; omega)
      (Compile.copyPipeTM_exit_is_halt 0 dst)
    rw [Compile.markBitTM_states] at h
    exact h

/-- `copyContentRawTM`'s halts are exactly the two pipeline exits. -/
theorem Compile.copyContentRawTM_halt_only (dst : Nat) :
    ∀ i, (Compile.copyContentRawTM dst).halt[i]? = some true →
      i = Compile.copyContent_exit0 dst ∨ i = Compile.copyContent_exit1 dst := by
  intro i hi
  have h := Compile.branchComposeFlatTM_halt_only Compile.markBitTM
    (Compile.copyPipeTM 0 dst) (Compile.copyPipeTM 1 dst)
    (Compile.markBitTM_exit 0) (Compile.markBitTM_exit 1)
    (Compile.copyPipeTM_exit dst) (Compile.copyPipeTM_exit dst)
    (Compile.copyPipeTM_valid 0 dst (by decide)) (Compile.copyPipeTM_valid 1 dst (by decide))
    (Compile.copyPipeTM_halt_unique 0 dst) (Compile.copyPipeTM_halt_unique 1 dst) i hi
  rw [Compile.markBitTM_states, Compile.copyPipeTM_states] at h
  exact h

/-- `copyContentTM`'s halt is unique after the join. -/
theorem Compile.copyContentTM_halt_unique (dst : Nat) :
    ∀ i, (Compile.copyContentTM dst).halt[i]? = some true →
      i = Compile.copyContent_exit0 dst :=
  Compile.joinTwoHalts_halt_unique _ _ _ (Compile.copyContentRawTM_halt_only dst)

/-- The body's ITERATE exit is a halt state (`copyContentTM`'s kept exit,
shifted past `delimTestTM`). -/
theorem Compile.copyBodyTM_exitLoop_is_halt (dst : Nat) :
    (Compile.copyBodyTM dst).halt[Compile.copyBody_exitLoop dst]? = some true := by
  have h := Compile.branchComposeFlatTM_M2_halt_intro (ClearGadget.delimTestTM 4)
    (Compile.copyContentTM dst) Compile.idTM
    ClearGadget.delimTestTM_exit_content ClearGadget.delimTestTM_exit_delim
    (Compile.copyContent_exit0 dst)
    (Compile.copyContentTM_valid dst)
    (by rw [Compile.copyContentTM_states]
        show 3 + (23 + 3 * dst) < 51 + 6 * dst; omega)
    (Compile.copyContentTM_exit_is_halt dst)
  rw [ClearGadget.delimTestTM_states] at h
  show (Compile.copyBodyTM dst).halt[29 + 3 * dst]? = some true
  rw [show 29 + 3 * dst = 3 + (3 + (23 + 3 * dst)) from by omega]
  exact h

/-- The body's DONE exit is a halt state (`idTM`'s halt, shifted). -/
theorem Compile.copyBodyTM_exitDone_is_halt (dst : Nat) :
    (Compile.copyBodyTM dst).halt[Compile.copyBody_exitDone dst]? = some true := by
  have h := Compile.branchComposeFlatTM_M3_halt_intro (ClearGadget.delimTestTM 4)
    (Compile.copyContentTM dst) Compile.idTM
    ClearGadget.delimTestTM_exit_content ClearGadget.delimTestTM_exit_delim
    0 (Compile.copyContentTM_valid dst) (by rfl)
  rw [ClearGadget.delimTestTM_states, Compile.copyContentTM_states] at h
  show (Compile.copyBodyTM dst).halt[54 + 6 * dst]? = some true
  rw [show 54 + 6 * dst = 3 + (51 + 6 * dst) + 0 from by omega]
  exact h

/-- The cursor-copy loop: iterate the body until `src` is exhausted. The loop's
dedicated halt state is `copyBodyTM.states = 55 + 6·dst`. -/
def Compile.copyLoopTM (dst : Nat) : FlatTM :=
  loopTM (Compile.copyBodyTM dst) (Compile.copyBody_exitDone dst)
    (Compile.copyBody_exitLoop dst)

def Compile.copyLoopTM_exit (dst : Nat) : Nat := 55 + 6 * dst

theorem Compile.copyLoopTM_states (dst : Nat) :
    (Compile.copyLoopTM dst).states = 56 + 6 * dst := by
  show (loopTM _ _ _).states = _
  rw [loopTM_states, Compile.copyBodyTM_states]
  omega

theorem Compile.copyLoopTM_tapes (dst : Nat) : (Compile.copyLoopTM dst).tapes = 1 :=
  Compile.copyBodyTM_tapes dst

theorem Compile.copyLoopTM_sig (dst : Nat) : (Compile.copyLoopTM dst).sig = 4 :=
  Compile.copyBodyTM_sig dst

theorem Compile.copyLoopTM_valid (dst : Nat) : validFlatTM (Compile.copyLoopTM dst) :=
  loopTM_valid _ _ _ (Compile.copyBodyTM_valid dst)
    (by rw [Compile.copyBodyTM_states]
        show 54 + 6 * dst < 55 + 6 * dst; omega)
    (by rw [Compile.copyBodyTM_states]
        show 29 + 3 * dst < 55 + 6 * dst; omega)
    (Compile.copyBodyTM_tapes dst)

/-- The full `copy dst src` machine (`dst ≠ src`):
`clearRegionTM dst ⨾ navigateToRegTM src ⨾ copyLoopTM dst ⨾ justRewindTM`. -/
def Compile.copyRegionFullTM (dst src : Nat) : FlatTM :=
  composeFlatTM
    (composeFlatTM
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.copyLoopTM dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src))
    ClearGadget.justRewindTM
    ((ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (55 + 6 * dst))

/-- States below the final `justRewindTM` block. -/
def Compile.copyRegionPreStates (dst src : Nat) : Nat :=
  (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (56 + 6 * dst)

/-- The kept exit: `justRewindTM`'s found state, shifted. -/
def Compile.copyRegionFullTM_exit (dst src : Nat) : Nat :=
  Compile.copyRegionPreStates dst src + 1

/-- The (unreachable) boundary halt: `justRewindTM`'s reject state, shifted. -/
def Compile.copyRegionFullTM_reject (dst src : Nat) : Nat :=
  Compile.copyRegionPreStates dst src + 2

theorem Compile.copyRegionFullTM_states (dst src : Nat) :
    (Compile.copyRegionFullTM dst src).states = Compile.copyRegionPreStates dst src + 3 := by
  show (composeFlatTM _ _ _).states = _
  repeat rw [composeFlatTM_states]
  rw [ClearGadget.navigateToRegTM_states, Compile.copyLoopTM_states]
  show _ + (2 + 3 * src) + (56 + 6 * dst) + 3 = _
  rfl

theorem Compile.copyRegionFullTM_valid (dst src : Nat) :
    validFlatTM (Compile.copyRegionFullTM dst src) := by
  refine composeFlatTM_valid _ _ _ (composeFlatTM_valid _ _ _ (composeFlatTM_valid _ _ _
      (ClearGadget.clearRegionTM_valid dst) (ClearGadget.navigateToRegTM_valid src)
      ?_ (ClearGadget.clearRegionTM_tapes dst) (ClearGadget.navigateToRegTM_tapes src))
      (Compile.copyLoopTM_valid dst) ?_ ?_ (Compile.copyLoopTM_tapes dst))
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide)) ?_ ?_ rfl
  · -- clearRegionTM_exit < clearRegionTM.states
    rw [ClearGadget.clearRegionTM_states]
    show (ClearGadget.clearBodyRawTM dst).states < (ClearGadget.clearBodyRawTM dst).states + 1
    omega
  · -- nav exit < composed states
    rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states]
    have := ClearGadget.navigateToRegTM_exit_lt src
    rw [ClearGadget.navigateToRegTM_states] at this
    omega
  · show (composeFlatTM _ _ _).tapes = 1
    show (ClearGadget.clearRegionTM dst).tapes = 1
    exact ClearGadget.clearRegionTM_tapes dst
  · -- loop exit < composed states
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.copyLoopTM_states]
    omega
  · show (composeFlatTM _ _ _).tapes = 1
    show (composeFlatTM _ _ _).tapes = 1
    show (ClearGadget.clearRegionTM dst).tapes = 1
    exact ClearGadget.clearRegionTM_tapes dst

theorem Compile.copyRegionFullTM_sig (dst src : Nat) :
    (Compile.copyRegionFullTM dst src).sig = 4 := by
  show max (max (max (ClearGadget.clearRegionTM dst).sig
      (ClearGadget.navigateToRegTM src).sig) (Compile.copyLoopTM dst).sig)
      ClearGadget.justRewindTM.sig = 4
  rw [ClearGadget.clearRegionTM_sig, ClearGadget.navigateToRegTM_sig,
      Compile.copyLoopTM_sig]
  rfl

theorem Compile.copyRegionFullTM_tapes (dst src : Nat) :
    (Compile.copyRegionFullTM dst src).tapes = 1 :=
  ClearGadget.clearRegionTM_tapes dst

/-- Halt characterization of the full chain: only `justRewindTM`'s two halt
states (shifted) are halting (`composedHalt` zeroes every `M₁` halt bit). -/
theorem Compile.copyRegionFullTM_halt_only (dst src : Nat) :
    ∀ i, (Compile.copyRegionFullTM dst src).halt[i]? = some true →
      i = Compile.copyRegionFullTM_exit dst src ∨
      i = Compile.copyRegionFullTM_reject dst src := by
  intro i hi
  obtain ⟨hge, hh⟩ := ScanLeft.composeFlatTM_halt_some_imp _ _ _ i hi
  have honly := ScanLeft.scanLeftUntilTM_halt_only 4 3 (i - _) hh
  have hpre : (composeFlatTM
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.copyLoopTM dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src)).states
      = Compile.copyRegionPreStates dst src := by
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.copyLoopTM_states]
    rfl
  rw [hpre] at hge hh honly
  rcases honly with h | h
  · left; show i = Compile.copyRegionPreStates dst src + 1; omega
  · right; show i = Compile.copyRegionPreStates dst src + 2; omega

/-- `justRewindTM`'s found state `1`, shifted, IS a halt of the full chain. -/
theorem Compile.copyRegionFullTM_exit_is_halt (dst src : Nat) :
    (Compile.copyRegionFullTM dst src).halt[Compile.copyRegionFullTM_exit dst src]?
      = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro
    (composeFlatTM
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.copyLoopTM dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src))
    ClearGadget.justRewindTM
    ((ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (55 + 6 * dst))
    1 (by rfl)
  have hpre : (composeFlatTM
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.copyLoopTM dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src)).states
      = Compile.copyRegionPreStates dst src := by
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.copyLoopTM_states]
    rfl
  rw [hpre] at h
  exact h

/-- Compile `Op.copy dst src`: the cursor-copy machine, with the rewind's
boundary halt demoted (`joinTwoHalts`) for `halt_unique`. `dst = src` is a
compile-time no-op (`Op.eval` leaves the state unchanged). -/
def Compile.opCopy (dst src : Var) : CompiledCmd :=
  if dst = src then compiledCmd_default else
  { M := Compile.joinTwoHalts (Compile.copyRegionFullTM dst src)
      (Compile.copyRegionFullTM_exit dst src) (Compile.copyRegionFullTM_reject dst src)
    exit := Compile.copyRegionFullTM_exit dst src
    exit_lt := by
      show _ < (Compile.joinTwoHalts _ _ _).states
      rw [Compile.joinTwoHalts_states, Compile.copyRegionFullTM_states]
      show Compile.copyRegionPreStates dst src + 1 < Compile.copyRegionPreStates dst src + 3
      omega
    exit_is_halt :=
      Compile.joinTwoHalts_h1_is_halt _ _ _
        (by show Compile.copyRegionPreStates dst src + 1 ≠ Compile.copyRegionPreStates dst src + 2
            omega)
        (Compile.copyRegionFullTM_exit_is_halt dst src)
    halt_unique :=
      Compile.joinTwoHalts_halt_unique _ _ _ (Compile.copyRegionFullTM_halt_only dst src)
    M_valid := Compile.joinTwoHalts_valid _ _ _ (Compile.copyRegionFullTM_valid dst src)
      (by rw [Compile.copyRegionFullTM_states]
          show Compile.copyRegionPreStates dst src + 1 < Compile.copyRegionPreStates dst src + 3
          omega)
      (by rw [Compile.copyRegionFullTM_states]
          show Compile.copyRegionPreStates dst src + 2 < Compile.copyRegionPreStates dst src + 3
          omega)
      (Compile.copyRegionFullTM_tapes dst src)
    M_tapes := Compile.copyRegionFullTM_tapes dst src
    M_sig := Compile.copyRegionFullTM_sig dst src }

/-! ### The `tail` op machines (`compileOp` dispatches here)

`tail dst dst` (in-place) deletes register `dst`'s first cell: exactly ONE
clear-style iteration — `clearBodyRawTM dst` (navigate+test; content →
step-right + delete-left-cell + two-phase rewind; delimiter → just-rewind) with
the content exit demoted into the kept done exit (`joinTwoHalts`), then composed
with the trivial halt machine `idTM` so the two unreachable boundary halts are
zeroed by `composedHalt` and exactly one halt remains.

`tail dst src` (`dst ≠ src`) is the cursor-copy machine with a `skipReadTM`
pre-stage stepping over `src`'s first cell before the (unchanged) cursor loop:
`clearRegionTM dst ⨾ navigateToRegTM src ⨾ (skipReadTM ⨠ copyLoopTM dst /
idTM, exits joined) ⨾ justRewindTM`, rewind boundary halt demoted — the
`opCopy` assembly with one extra branch stage. Probe-validated end-to-end
(`probes/CursorCopyProbe.lean`). -/

/-- `clearBodyRawTM`'s sig, via the (defeq) `loopTM` wrapper's lemma. -/
theorem Compile.clearBodyRawTM_sig (dst : Nat) : (ClearGadget.clearBodyRawTM dst).sig = 4 :=
  ClearGadget.clearRegionTM_sig dst

theorem Compile.clearBodyRawTM_tapes (dst : Nat) : (ClearGadget.clearBodyRawTM dst).tapes = 1 :=
  ClearGadget.clearRegionTM_tapes dst

theorem Compile.clearBodyRawTM_start (dst : Nat) : (ClearGadget.clearBodyRawTM dst).start = 0 :=
  ClearGadget.clearRegionTM_start dst

/-- `idTM`'s single state is its unique halt. -/
theorem Compile.idTM_halt_unique : ∀ i, Compile.idTM.halt[i]? = some true → i = 0 := by
  intro i hi
  match i with
  | 0 => rfl
  | n + 1 => exact absurd hi (by simp [Compile.idTM])

/-- In-place `tail dst dst`, raw: one clear-style delete with the content exit
(`exitLoop`) demoted into the kept done exit (`exitDone`). -/
def Compile.tailInPlaceRawTM (dst : Nat) : FlatTM :=
  Compile.joinTwoHalts (ClearGadget.clearBodyRawTM dst)
    (ClearGadget.clearBodyRawTM_exitDone dst) (ClearGadget.clearBodyRawTM_exitLoop dst)

/-- The in-place `tail dst dst` machine: composing with `idTM` zeroes ALL the
body's halt bits (incl. the two unreachable boundary halts), leaving the single
halt at `idTM`'s (shifted) start. -/
def Compile.tailInPlaceTM (dst : Nat) : FlatTM :=
  composeFlatTM (Compile.tailInPlaceRawTM dst) Compile.idTM
    (ClearGadget.clearBodyRawTM_exitDone dst)

def Compile.tailInPlaceTM_exit (dst : Nat) : Nat := (ClearGadget.clearBodyRawTM dst).states

theorem Compile.tailInPlaceRawTM_states (dst : Nat) :
    (Compile.tailInPlaceRawTM dst).states = (ClearGadget.clearBodyRawTM dst).states := rfl

theorem Compile.tailInPlaceTM_states (dst : Nat) :
    (Compile.tailInPlaceTM dst).states = (ClearGadget.clearBodyRawTM dst).states + 1 := by
  show (composeFlatTM _ _ _).states = _
  rw [composeFlatTM_states]
  rfl

theorem Compile.tailInPlaceRawTM_valid (dst : Nat) :
    validFlatTM (Compile.tailInPlaceRawTM dst) :=
  Compile.joinTwoHalts_valid _ _ _ (ClearGadget.clearBodyRawTM_valid dst)
    (ClearGadget.clearBodyRawTM_exitDone_lt dst) (ClearGadget.clearBodyRawTM_exitLoop_lt dst)
    (Compile.clearBodyRawTM_tapes dst)

theorem Compile.tailInPlaceTM_valid (dst : Nat) : validFlatTM (Compile.tailInPlaceTM dst) :=
  composeFlatTM_valid _ _ _ (Compile.tailInPlaceRawTM_valid dst) Compile.idTM_valid
    (ClearGadget.clearBodyRawTM_exitDone_lt dst) (Compile.clearBodyRawTM_tapes dst) rfl

theorem Compile.tailInPlaceTM_tapes (dst : Nat) : (Compile.tailInPlaceTM dst).tapes = 1 :=
  Compile.clearBodyRawTM_tapes dst

theorem Compile.tailInPlaceTM_sig (dst : Nat) : (Compile.tailInPlaceTM dst).sig = 4 := by
  show max (ClearGadget.clearBodyRawTM dst).sig Compile.idTM.sig = 4
  rw [Compile.clearBodyRawTM_sig]
  rfl

theorem Compile.tailInPlaceTM_start (dst : Nat) : (Compile.tailInPlaceTM dst).start = 0 :=
  Compile.clearBodyRawTM_start dst

theorem Compile.tailInPlaceTM_halt_unique (dst : Nat) :
    ∀ i, (Compile.tailInPlaceTM dst).halt[i]? = some true →
      i = Compile.tailInPlaceTM_exit dst := by
  intro i hi
  have h := Compile.composeFlatTM_halt_unique (Compile.tailInPlaceRawTM dst) Compile.idTM 0
    (ClearGadget.clearBodyRawTM_exitDone dst) Compile.idTM_halt_unique i hi
  rw [Compile.tailInPlaceRawTM_states] at h
  show i = (ClearGadget.clearBodyRawTM dst).states
  omega

theorem Compile.tailInPlaceTM_exit_is_halt (dst : Nat) :
    (Compile.tailInPlaceTM dst).halt[Compile.tailInPlaceTM_exit dst]? = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro (Compile.tailInPlaceRawTM dst) Compile.idTM
    (ClearGadget.clearBodyRawTM_exitDone dst) 0 rfl
  exact h

/-- The cursor loop's halt vector has its single `true` at `copyLoopTM_exit`. -/
theorem Compile.copyLoopTM_exit_is_halt (dst : Nat) :
    (Compile.copyLoopTM dst).halt[Compile.copyLoopTM_exit dst]? = some true := by
  show (List.replicate (Compile.copyBodyTM dst).states false
      ++ [true])[Compile.copyLoopTM_exit dst]? = some true
  rw [show Compile.copyLoopTM_exit dst = (Compile.copyBodyTM dst).states from by
        rw [Compile.copyBodyTM_states]; rfl,
      List.getElem?_append_right (by rw [List.length_replicate]),
      List.length_replicate, Nat.sub_self]
  rfl

theorem Compile.copyLoopTM_halt_unique (dst : Nat) :
    ∀ i, (Compile.copyLoopTM dst).halt[i]? = some true → i = Compile.copyLoopTM_exit dst := by
  intro i hi
  show i = Compile.copyLoopTM_exit dst
  rw [show Compile.copyLoopTM_exit dst = (Compile.copyBodyTM dst).states from by
        rw [Compile.copyBodyTM_states]; rfl]
  change (List.replicate (Compile.copyBodyTM dst).states false ++ [true])[i]? = some true at hi
  by_cases hlt : i < (Compile.copyBodyTM dst).states
  · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hlt),
        List.getElem?_replicate] at hi
    split at hi <;> simp_all
  · rw [Nat.not_lt] at hlt
    rw [List.getElem?_append_right (by rw [List.length_replicate]; exact hlt),
        List.length_replicate] at hi
    rcases hi' : i - (Compile.copyBodyTM dst).states with _ | n
    · omega
    · rw [hi'] at hi; simp at hi

/-- `tail dst src` branch stage, raw: `skipReadTM` dispatches — content cell →
step right onto `src`'s second cell and run the cursor loop; delimiter (`src`
empty) → `idTM` (no-op). -/
def Compile.tailBranchRawTM (dst : Nat) : FlatTM :=
  branchComposeFlatTM Compile.skipReadTM (Compile.copyLoopTM dst) Compile.idTM
    Compile.skipReadTM_exit_bit Compile.skipReadTM_exit_empty

/-- The kept exit: the cursor loop's halt, shifted into the branch composite. -/
def Compile.tailBranch_keptExit (dst : Nat) : Nat := 3 + Compile.copyLoopTM_exit dst

/-- The empty-src exit (`idTM`'s start, shifted) — demoted into the kept exit. -/
def Compile.tailBranch_emptyExit (dst : Nat) : Nat := 3 + (Compile.copyLoopTM dst).states

def Compile.tailBranchTM (dst : Nat) : FlatTM :=
  Compile.joinTwoHalts (Compile.tailBranchRawTM dst)
    (Compile.tailBranch_keptExit dst) (Compile.tailBranch_emptyExit dst)

theorem Compile.tailBranch_keptExit_eq (dst : Nat) :
    Compile.tailBranch_keptExit dst = 58 + 6 * dst := by
  show 3 + (55 + 6 * dst) = 58 + 6 * dst
  omega

theorem Compile.tailBranch_emptyExit_eq (dst : Nat) :
    Compile.tailBranch_emptyExit dst = 59 + 6 * dst := by
  rw [Compile.tailBranch_emptyExit, Compile.copyLoopTM_states]
  omega

theorem Compile.tailBranchRawTM_states (dst : Nat) :
    (Compile.tailBranchRawTM dst).states = 60 + 6 * dst := by
  show Compile.skipReadTM.states + (Compile.copyLoopTM dst).states + Compile.idTM.states = _
  rw [Compile.skipReadTM_states, Compile.copyLoopTM_states]
  show 3 + (56 + 6 * dst) + 1 = 60 + 6 * dst
  omega

theorem Compile.tailBranchTM_states (dst : Nat) :
    (Compile.tailBranchTM dst).states = 60 + 6 * dst :=
  Compile.tailBranchRawTM_states dst

theorem Compile.tailBranchRawTM_valid (dst : Nat) : validFlatTM (Compile.tailBranchRawTM dst) :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.skipReadTM_valid (Compile.copyLoopTM_valid dst)
    Compile.idTM_valid
    (by rw [Compile.skipReadTM_states]; show (2 : Nat) < 3; omega)
    (by rw [Compile.skipReadTM_states]; show (1 : Nat) < 3; omega)
    (Compile.skipReadTM_tapes) (Compile.copyLoopTM_tapes dst) rfl

theorem Compile.tailBranchTM_valid (dst : Nat) : validFlatTM (Compile.tailBranchTM dst) :=
  Compile.joinTwoHalts_valid _ _ _ (Compile.tailBranchRawTM_valid dst)
    (by rw [Compile.tailBranchRawTM_states, Compile.tailBranch_keptExit_eq]; omega)
    (by rw [Compile.tailBranchRawTM_states, Compile.tailBranch_emptyExit_eq]; omega)
    Compile.skipReadTM_tapes

theorem Compile.tailBranchTM_tapes (dst : Nat) : (Compile.tailBranchTM dst).tapes = 1 :=
  Compile.skipReadTM_tapes

theorem Compile.tailBranchRawTM_sig (dst : Nat) : (Compile.tailBranchRawTM dst).sig = 4 := by
  show max Compile.skipReadTM.sig (max (Compile.copyLoopTM dst).sig Compile.idTM.sig) = 4
  rw [Compile.copyLoopTM_sig]
  rfl

theorem Compile.tailBranchTM_sig (dst : Nat) : (Compile.tailBranchTM dst).sig = 4 :=
  Compile.tailBranchRawTM_sig dst

theorem Compile.tailBranchTM_start (dst : Nat) : (Compile.tailBranchTM dst).start = 0 := rfl

/-- The kept exit is a halt of the raw branch composite (the loop's halt,
`M₂`-shifted). -/
theorem Compile.tailBranchRawTM_keptExit_is_halt (dst : Nat) :
    (Compile.tailBranchRawTM dst).halt[Compile.tailBranch_keptExit dst]? = some true :=
  Compile.branchComposeFlatTM_M2_halt_intro Compile.skipReadTM (Compile.copyLoopTM dst)
    Compile.idTM Compile.skipReadTM_exit_bit Compile.skipReadTM_exit_empty
    (Compile.copyLoopTM_exit dst) (Compile.copyLoopTM_valid dst)
    (by rw [Compile.copyLoopTM_states]; show 55 + 6 * dst < 56 + 6 * dst; omega)
    (Compile.copyLoopTM_exit_is_halt dst)

/-- The empty-src exit is a halt of the raw branch composite (`idTM`'s halt,
`M₃`-shifted). -/
theorem Compile.tailBranchRawTM_emptyExit_is_halt (dst : Nat) :
    (Compile.tailBranchRawTM dst).halt[Compile.tailBranch_emptyExit dst]? = some true :=
  Compile.branchComposeFlatTM_M3_halt_intro Compile.skipReadTM (Compile.copyLoopTM dst)
    Compile.idTM Compile.skipReadTM_exit_bit Compile.skipReadTM_exit_empty 0
    (Compile.copyLoopTM_valid dst) rfl

theorem Compile.tailBranchTM_keptExit_is_halt (dst : Nat) :
    (Compile.tailBranchTM dst).halt[Compile.tailBranch_keptExit dst]? = some true :=
  Compile.joinTwoHalts_h1_is_halt _ _ _
    (by rw [Compile.tailBranch_keptExit_eq, Compile.tailBranch_emptyExit_eq]; omega)
    (Compile.tailBranchRawTM_keptExit_is_halt dst)

/-- The full `tail dst src` machine (`dst ≠ src`):
`clearRegionTM dst ⨾ navigateToRegTM src ⨾ tailBranchTM dst ⨾ justRewindTM`. -/
def Compile.tailRegionFullTM (dst src : Nat) : FlatTM :=
  composeFlatTM
    (composeFlatTM
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.tailBranchTM dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src))
    ClearGadget.justRewindTM
    ((ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (58 + 6 * dst))

/-- States below the final `justRewindTM` block. -/
def Compile.tailRegionPreStates (dst src : Nat) : Nat :=
  (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (60 + 6 * dst)

/-- The kept exit: `justRewindTM`'s found state, shifted. -/
def Compile.tailRegionFullTM_exit (dst src : Nat) : Nat :=
  Compile.tailRegionPreStates dst src + 1

/-- The (unreachable) boundary halt: `justRewindTM`'s reject state, shifted. -/
def Compile.tailRegionFullTM_reject (dst src : Nat) : Nat :=
  Compile.tailRegionPreStates dst src + 2

theorem Compile.tailRegionFullTM_states (dst src : Nat) :
    (Compile.tailRegionFullTM dst src).states = Compile.tailRegionPreStates dst src + 3 := by
  show (composeFlatTM _ _ _).states = _
  repeat rw [composeFlatTM_states]
  rw [ClearGadget.navigateToRegTM_states, Compile.tailBranchTM_states]
  show _ + (2 + 3 * src) + (60 + 6 * dst) + 3 = _
  rfl

theorem Compile.tailRegionFullTM_valid (dst src : Nat) :
    validFlatTM (Compile.tailRegionFullTM dst src) := by
  refine composeFlatTM_valid _ _ _ (composeFlatTM_valid _ _ _ (composeFlatTM_valid _ _ _
      (ClearGadget.clearRegionTM_valid dst) (ClearGadget.navigateToRegTM_valid src)
      ?_ (ClearGadget.clearRegionTM_tapes dst) (ClearGadget.navigateToRegTM_tapes src))
      (Compile.tailBranchTM_valid dst) ?_ ?_ (Compile.tailBranchTM_tapes dst))
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide)) ?_ ?_ rfl
  · -- clearRegionTM_exit < clearRegionTM.states
    rw [ClearGadget.clearRegionTM_states]
    show (ClearGadget.clearBodyRawTM dst).states < (ClearGadget.clearBodyRawTM dst).states + 1
    omega
  · -- nav exit < composed states
    rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states]
    have := ClearGadget.navigateToRegTM_exit_lt src
    rw [ClearGadget.navigateToRegTM_states] at this
    omega
  · show (composeFlatTM _ _ _).tapes = 1
    show (ClearGadget.clearRegionTM dst).tapes = 1
    exact ClearGadget.clearRegionTM_tapes dst
  · -- kept branch exit < composed states
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.tailBranchTM_states]
    omega
  · show (composeFlatTM _ _ _).tapes = 1
    show (composeFlatTM _ _ _).tapes = 1
    show (ClearGadget.clearRegionTM dst).tapes = 1
    exact ClearGadget.clearRegionTM_tapes dst

theorem Compile.tailRegionFullTM_sig (dst src : Nat) :
    (Compile.tailRegionFullTM dst src).sig = 4 := by
  show max (max (max (ClearGadget.clearRegionTM dst).sig
      (ClearGadget.navigateToRegTM src).sig) (Compile.tailBranchTM dst).sig)
      ClearGadget.justRewindTM.sig = 4
  rw [ClearGadget.clearRegionTM_sig, ClearGadget.navigateToRegTM_sig,
      Compile.tailBranchTM_sig]
  rfl

theorem Compile.tailRegionFullTM_tapes (dst src : Nat) :
    (Compile.tailRegionFullTM dst src).tapes = 1 :=
  ClearGadget.clearRegionTM_tapes dst

/-- Halt characterization of the full chain: only `justRewindTM`'s two halt
states (shifted) are halting (`composedHalt` zeroes every `M₁` halt bit). -/
theorem Compile.tailRegionFullTM_halt_only (dst src : Nat) :
    ∀ i, (Compile.tailRegionFullTM dst src).halt[i]? = some true →
      i = Compile.tailRegionFullTM_exit dst src ∨
      i = Compile.tailRegionFullTM_reject dst src := by
  intro i hi
  obtain ⟨hge, hh⟩ := ScanLeft.composeFlatTM_halt_some_imp _ _ _ i hi
  have honly := ScanLeft.scanLeftUntilTM_halt_only 4 3 (i - _) hh
  have hpre : (composeFlatTM
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.tailBranchTM dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src)).states
      = Compile.tailRegionPreStates dst src := by
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.tailBranchTM_states]
    rfl
  rw [hpre] at hge hh honly
  rcases honly with h | h
  · left; show i = Compile.tailRegionPreStates dst src + 1; omega
  · right; show i = Compile.tailRegionPreStates dst src + 2; omega

/-- `justRewindTM`'s found state `1`, shifted, IS a halt of the full chain. -/
theorem Compile.tailRegionFullTM_exit_is_halt (dst src : Nat) :
    (Compile.tailRegionFullTM dst src).halt[Compile.tailRegionFullTM_exit dst src]?
      = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro
    (composeFlatTM
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.tailBranchTM dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src))
    ClearGadget.justRewindTM
    ((ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (58 + 6 * dst))
    1 (by rfl)
  have hpre : (composeFlatTM
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.tailBranchTM dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src)).states
      = Compile.tailRegionPreStates dst src := by
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.tailBranchTM_states]
    rfl
  rw [hpre] at h
  exact h

/-- The (unreachable) boundary halt IS a halt of the full chain. -/
theorem Compile.tailRegionFullTM_reject_is_halt (dst src : Nat) :
    (Compile.tailRegionFullTM dst src).halt[Compile.tailRegionFullTM_reject dst src]?
      = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro
    (composeFlatTM
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.tailBranchTM dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src))
    ClearGadget.justRewindTM
    ((ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (58 + 6 * dst))
    2 (by rfl)
  have hpre : (composeFlatTM
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.tailBranchTM dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src)).states
      = Compile.tailRegionPreStates dst src := by
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.tailBranchTM_states]
    rfl
  rw [hpre] at h
  exact h

/-- Compile `Op.tail dst src`: the in-place delete for `dst = src`, the
skip-then-cursor-copy machine for `dst ≠ src` (rewind boundary halt demoted,
following the `opCopy` pattern). -/
def Compile.opTail (dst src : Var) : CompiledCmd :=
  if dst = src then
    { M := Compile.tailInPlaceTM dst
      exit := Compile.tailInPlaceTM_exit dst
      exit_lt := by
        rw [Compile.tailInPlaceTM_states]
        show (ClearGadget.clearBodyRawTM dst).states < (ClearGadget.clearBodyRawTM dst).states + 1
        omega
      exit_is_halt := Compile.tailInPlaceTM_exit_is_halt dst
      halt_unique := Compile.tailInPlaceTM_halt_unique dst
      M_valid := Compile.tailInPlaceTM_valid dst
      M_tapes := Compile.tailInPlaceTM_tapes dst
      M_sig := Compile.tailInPlaceTM_sig dst }
  else
    { M := Compile.joinTwoHalts (Compile.tailRegionFullTM dst src)
        (Compile.tailRegionFullTM_exit dst src) (Compile.tailRegionFullTM_reject dst src)
      exit := Compile.tailRegionFullTM_exit dst src
      exit_lt := by
        show _ < (Compile.joinTwoHalts _ _ _).states
        rw [Compile.joinTwoHalts_states, Compile.tailRegionFullTM_states]
        show Compile.tailRegionPreStates dst src + 1 < Compile.tailRegionPreStates dst src + 3
        omega
      exit_is_halt :=
        Compile.joinTwoHalts_h1_is_halt _ _ _
          (by show Compile.tailRegionPreStates dst src + 1
                ≠ Compile.tailRegionPreStates dst src + 2
              omega)
          (Compile.tailRegionFullTM_exit_is_halt dst src)
      halt_unique :=
        Compile.joinTwoHalts_halt_unique _ _ _ (Compile.tailRegionFullTM_halt_only dst src)
      M_valid := Compile.joinTwoHalts_valid _ _ _ (Compile.tailRegionFullTM_valid dst src)
        (by rw [Compile.tailRegionFullTM_states]
            show Compile.tailRegionPreStates dst src + 1 < Compile.tailRegionPreStates dst src + 3
            omega)
        (by rw [Compile.tailRegionFullTM_states]
            show Compile.tailRegionPreStates dst src + 2 < Compile.tailRegionPreStates dst src + 3
            omega)
        (Compile.tailRegionFullTM_tapes dst src)
      M_tapes := Compile.tailRegionFullTM_tapes dst src
      M_sig := Compile.tailRegionFullTM_sig dst src }

/-! ### Class-A op machinery: `nonEmpty` (`compileOp` dispatches here)

`nonEmpty dst src` reads register `src`, branches, and writes a single answer bit
to (a freshly cleared) register `dst`. The machine reads `src` FIRST (so it is
correct even when `dst = src`): `navigateAndTest src ⨠ branch ⨠ (rewind ⨠ clear
dst ⨠ append answer-bit)`. Each branch's clear-then-append reuses the proven
`opClear`/`opAppendBitRewind` `CompiledCmd`s. The two branch exits are merged into
a single exit by `joinTwoHalts` (bridge `delimExit → contentExit`). Validated
end-to-end by `#eval` (incl. `dst = src`). -/

/-- `M₂`'s halt state shifts to a halt of `composeFlatTM` (intro). -/
theorem Compile.composeFlatTM_halt_intro (M₁ M₂ : FlatTM) (e₂ exit : Nat)
    (h : M₂.halt[e₂]? = some true) :
    (composeFlatTM M₁ M₂ exit).halt[M₁.states + e₂]? = some true :=
  ScanLeft.composeFlatTM_halt_some_intro M₁ M₂ exit e₂ h

/-- `joinTwoHalts` only demotes `h2`; it never *adds* a halt, so a non-halting
config of `M` stays non-halting. -/
theorem Compile.joinTwoHalts_halting_false (M : FlatTM) (h1 h2 : Nat) (cfg : FlatTMConfig)
    (h : haltingStateReached M cfg = false) :
    haltingStateReached (joinTwoHalts M h1 h2) cfg = false := by
  show (M.halt.set h2 false).getD cfg.state_idx false = false
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hh : h2 = cfg.state_idx
  · rw [if_pos hh]; split <;> rfl
  · rw [if_neg hh, ← List.getD_eq_getElem?_getD]; exact h

/-- Clear register `dst`, then append the shifted bit `ins` — both head-`0`-exit
machines, composed. The unique exit is at
`clearRegionTM.states + opAppendBitRewind.exit`. -/
def Compile.clearAppendM (dst : Var) (ins : Nat) (h_ins : ins < 4) : FlatTM :=
  composeFlatTM (ClearGadget.clearRegionTM dst) (Compile.opAppendBitRewind ins h_ins dst).M
    (ClearGadget.clearRegionTM_exit dst)

def Compile.clearAppendM_exit (dst : Var) (ins : Nat) (h_ins : ins < 4) : Nat :=
  (ClearGadget.clearRegionTM dst).states + (Compile.opAppendBitRewind ins h_ins dst).exit

theorem Compile.clearAppendM_tapes (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    (Compile.clearAppendM dst ins h_ins).tapes = 1 := by
  rw [Compile.clearAppendM, composeFlatTM_tapes]; exact ClearGadget.clearRegionTM_tapes dst

theorem Compile.clearAppendM_sig (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    (Compile.clearAppendM dst ins h_ins).sig = 4 := by
  rw [Compile.clearAppendM, composeFlatTM_sig, ClearGadget.clearRegionTM_sig,
      (Compile.opAppendBitRewind ins h_ins dst).M_sig]
  rfl

theorem Compile.clearRegionTM_exit_lt (dst : Var) :
    ClearGadget.clearRegionTM_exit dst < (ClearGadget.clearRegionTM dst).states := by
  rw [ClearGadget.clearRegionTM_states]
  show (ClearGadget.clearBodyRawTM dst).states < (ClearGadget.clearBodyRawTM dst).states + 1
  omega

theorem Compile.clearAppendM_valid (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    validFlatTM (Compile.clearAppendM dst ins h_ins) :=
  composeFlatTM_valid _ _ _ (ClearGadget.clearRegionTM_valid dst)
    (Compile.opAppendBitRewind ins h_ins dst).M_valid (Compile.clearRegionTM_exit_lt dst)
    (ClearGadget.clearRegionTM_tapes dst) (Compile.opAppendBitRewind ins h_ins dst).M_tapes

theorem Compile.clearAppendM_halt_unique (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    ∀ i, (Compile.clearAppendM dst ins h_ins).halt[i]? = some true →
      i = Compile.clearAppendM_exit dst ins h_ins := by
  rw [Compile.clearAppendM, Compile.clearAppendM_exit]
  exact Compile.composeFlatTM_halt_unique _ _ _ _ (Compile.opAppendBitRewind ins h_ins dst).halt_unique

theorem Compile.clearAppendM_exit_is_halt (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    (Compile.clearAppendM dst ins h_ins).halt[Compile.clearAppendM_exit dst ins h_ins]? = some true := by
  rw [Compile.clearAppendM, Compile.clearAppendM_exit]
  exact Compile.composeFlatTM_halt_intro _ _ _ _ (Compile.opAppendBitRewind ins h_ins dst).exit_is_halt

/-- A branch body: rewind to the leading sentinel, then clear-and-append. -/
def Compile.nonEmptyBranchBody (dst : Var) (ins : Nat) (h_ins : ins < 4) : FlatTM :=
  composeFlatTM (ScanLeft.scanLeftUntilTM 4 3) (Compile.clearAppendM dst ins h_ins) 1

def Compile.nonEmptyBranchBody_exit (dst : Var) (ins : Nat) (h_ins : ins < 4) : Nat :=
  (ScanLeft.scanLeftUntilTM 4 3).states + Compile.clearAppendM_exit dst ins h_ins

theorem Compile.nonEmptyBranchBody_tapes (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    (Compile.nonEmptyBranchBody dst ins h_ins).tapes = 1 := by
  rw [Compile.nonEmptyBranchBody, composeFlatTM_tapes]; rfl

theorem Compile.nonEmptyBranchBody_valid (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    validFlatTM (Compile.nonEmptyBranchBody dst ins h_ins) :=
  composeFlatTM_valid _ _ _ (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (Compile.clearAppendM_valid dst ins h_ins) (by decide)
    rfl (Compile.clearAppendM_tapes dst ins h_ins)

theorem Compile.nonEmptyBranchBody_halt_unique (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    ∀ i, (Compile.nonEmptyBranchBody dst ins h_ins).halt[i]? = some true →
      i = Compile.nonEmptyBranchBody_exit dst ins h_ins := by
  rw [Compile.nonEmptyBranchBody, Compile.nonEmptyBranchBody_exit]
  exact Compile.composeFlatTM_halt_unique _ _ _ _ (Compile.clearAppendM_halt_unique dst ins h_ins)

theorem Compile.nonEmptyBranchBody_exit_is_halt (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    (Compile.nonEmptyBranchBody dst ins h_ins).halt[Compile.nonEmptyBranchBody_exit dst ins h_ins]?
      = some true := by
  rw [Compile.nonEmptyBranchBody, Compile.nonEmptyBranchBody_exit]
  exact Compile.composeFlatTM_halt_intro _ _ _ _ (Compile.clearAppendM_exit_is_halt dst ins h_ins)

theorem Compile.nonEmptyBranchBody_exit_lt (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    Compile.nonEmptyBranchBody_exit dst ins h_ins < (Compile.nonEmptyBranchBody dst ins h_ins).states := by
  rw [Compile.nonEmptyBranchBody_exit, Compile.nonEmptyBranchBody, composeFlatTM_states,
      Compile.clearAppendM_exit, Compile.clearAppendM, composeFlatTM_states]
  have := (Compile.opAppendBitRewind ins h_ins dst).exit_lt
  omega

/-- The raw (two-exit) `nonEmpty` machine: branch on `navigateAndTest src`. -/
def Compile.nonEmptyRawM (dst src : Var) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
    (Compile.nonEmptyBranchBody dst 2 (by decide))
    (Compile.nonEmptyBranchBody dst 1 (by decide))
    (ClearGadget.navigateAndTestTM_exit_content src)
    (ClearGadget.navigateAndTestTM_exit_delim src)

/-- content exit (positive branch). -/
def Compile.nonEmptyRawM_h1 (dst src : Var) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + Compile.nonEmptyBranchBody_exit dst 2 (by decide)

/-- delim exit (negative branch). -/
def Compile.nonEmptyRawM_h2 (dst src : Var) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (Compile.nonEmptyBranchBody dst 2 (by decide)).states
    + Compile.nonEmptyBranchBody_exit dst 1 (by decide)

theorem Compile.nonEmptyRawM_valid (dst src : Var) : validFlatTM (Compile.nonEmptyRawM dst src) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.navigateAndTestTM_valid src)
    (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
    (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    (ClearGadget.navigateAndTestTM_tapes src)
    (Compile.nonEmptyBranchBody_tapes dst 2 (by decide))
    (Compile.nonEmptyBranchBody_tapes dst 1 (by decide))

theorem Compile.nonEmptyRawM_tapes (dst src : Var) : (Compile.nonEmptyRawM dst src).tapes = 1 := by
  rw [Compile.nonEmptyRawM, branchComposeFlatTM_tapes]; exact ClearGadget.navigateAndTestTM_tapes src

theorem Compile.nonEmptyRawM_sig (dst src : Var) : (Compile.nonEmptyRawM dst src).sig = 4 := by
  rw [Compile.nonEmptyRawM, branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig]
  rw [show (Compile.nonEmptyBranchBody dst 2 (by decide)).sig = 4 from by
        rw [Compile.nonEmptyBranchBody, composeFlatTM_sig, Compile.clearAppendM_sig]; rfl,
      show (Compile.nonEmptyBranchBody dst 1 (by decide)).sig = 4 from by
        rw [Compile.nonEmptyBranchBody, composeFlatTM_sig, Compile.clearAppendM_sig]; rfl]
  rfl

theorem Compile.nonEmptyRawM_h1_ne_h2 (dst src : Var) :
    Compile.nonEmptyRawM_h1 dst src ≠ Compile.nonEmptyRawM_h2 dst src := by
  rw [Compile.nonEmptyRawM_h1, Compile.nonEmptyRawM_h2]
  have hb2 := Compile.nonEmptyBranchBody_exit_lt dst 2 (by decide)
  omega

theorem Compile.nonEmptyRawM_halt_only (dst src : Var) :
    ∀ i, (Compile.nonEmptyRawM dst src).halt[i]? = some true →
      i = Compile.nonEmptyRawM_h1 dst src ∨ i = Compile.nonEmptyRawM_h2 dst src := by
  rw [Compile.nonEmptyRawM_h1, Compile.nonEmptyRawM_h2, Compile.nonEmptyRawM]
  exact Compile.branchComposeFlatTM_halt_only _ _ _ _ _ _ _
    (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
    (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
    (Compile.nonEmptyBranchBody_halt_unique dst 2 (by decide))
    (Compile.nonEmptyBranchBody_halt_unique dst 1 (by decide))

theorem Compile.nonEmptyRawM_h1_is_halt (dst src : Var) :
    (Compile.nonEmptyRawM dst src).halt[Compile.nonEmptyRawM_h1 dst src]? = some true := by
  rw [Compile.nonEmptyRawM_h1, Compile.nonEmptyRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
    (Compile.nonEmptyBranchBody_exit_lt dst 2 (by decide))
    (Compile.nonEmptyBranchBody_exit_is_halt dst 2 (by decide))

theorem Compile.nonEmptyRawM_h1_lt (dst src : Var) :
    Compile.nonEmptyRawM_h1 dst src < (Compile.nonEmptyRawM dst src).states := by
  rw [Compile.nonEmptyRawM_h1, Compile.nonEmptyRawM, branchComposeFlatTM_states]
  have := Compile.nonEmptyBranchBody_exit_lt dst 2 (by decide)
  omega

theorem Compile.nonEmptyRawM_h2_is_halt (dst src : Var) :
    (Compile.nonEmptyRawM dst src).halt[Compile.nonEmptyRawM_h2 dst src]? = some true := by
  rw [Compile.nonEmptyRawM_h2, Compile.nonEmptyRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
    (Compile.nonEmptyBranchBody_exit_is_halt dst 1 (by decide))

theorem Compile.nonEmptyRawM_h2_lt (dst src : Var) :
    Compile.nonEmptyRawM_h2 dst src < (Compile.nonEmptyRawM dst src).states := by
  rw [Compile.nonEmptyRawM_h2, Compile.nonEmptyRawM, branchComposeFlatTM_states]
  have := Compile.nonEmptyBranchBody_exit_lt dst 1 (by decide)
  omega

/-- Compile `Op.nonEmpty dst src`: the `joinTwoHalts`-merged branch machine. -/
def Compile.opNonEmpty (dst src : Var) : CompiledCmd where
  M := joinTwoHalts (Compile.nonEmptyRawM dst src)
        (Compile.nonEmptyRawM_h1 dst src) (Compile.nonEmptyRawM_h2 dst src)
  exit := Compile.nonEmptyRawM_h1 dst src
  exit_lt := by
    rw [joinTwoHalts_states]; exact Compile.nonEmptyRawM_h1_lt dst src
  exit_is_halt :=
    joinTwoHalts_h1_is_halt _ _ _ (Compile.nonEmptyRawM_h1_ne_h2 dst src)
      (Compile.nonEmptyRawM_h1_is_halt dst src)
  halt_unique :=
    joinTwoHalts_halt_unique _ _ _ (Compile.nonEmptyRawM_halt_only dst src)
  M_valid := joinTwoHalts_valid _ _ _ (Compile.nonEmptyRawM_valid dst src)
    (Compile.nonEmptyRawM_h1_lt dst src) (Compile.nonEmptyRawM_h2_lt dst src)
    (Compile.nonEmptyRawM_tapes dst src)
  M_tapes := by rw [joinTwoHalts_tapes]; exact Compile.nonEmptyRawM_tapes dst src
  M_sig := by rw [joinTwoHalts_sig]; exact Compile.nonEmptyRawM_sig dst src

/-! ### The `head` op — bit-value read (Class A, 3-way branch)

`head dst src` writes `[]` (src empty), `[0]` (first bit 0) or `[1]` (first bit 1).
Unlike `nonEmpty` (a 2-way empty-vs-nonempty branch), `head` must read the **bit
value**. We nest two 2-way branches, reusing the `nonEmpty` engine:

- **Outer** (`headRawM`): `navigateAndTestTM src` (empty-vs-content). The delim
  branch writes `[]` (`clearOnlyBranchBody`); the content branch runs `opInnerBit`.
- **Inner** (`innerBitRawM`/`opInnerBit`): from the navtest exit (head on `src`'s
  first cell), `bitReadTM` reads that cell — `2` (bit 1) → write `[1]`, `1` (bit 0)
  → write `[0]` — reusing `nonEmptyBranchBody`. Two exits merged by `joinTwoHalts`.

Both levels are `joinTwoHalts`-merged so each is a unique-halt `CompiledCmd`. -/

/-- Test entry for content bit `0` (cell value `1`): stay, halt at state 1. -/
def Compile.bitReadBit0Entry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some 1]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

/-- Test entry for content bit `1` (cell value `2`): stay, halt at state 2. -/
def Compile.bitReadBit1Entry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some 2]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

/-- The bit-value test machine: 3 states, reads one cell, branches `1` vs `2`.
Unlike `delimTestTM` (delim-vs-content), this reads the **bit value** of a content
cell: `1` (bit 0) → state 1, `2` (bit 1) → state 2. Used by `head` (and later
`eqBit`), which need the actual first bit, not just empty-vs-nonempty. -/
def Compile.bitReadTM : FlatTM where
  sig := 4
  tapes := 1
  states := 3
  trans := [Compile.bitReadBit0Entry, Compile.bitReadBit1Entry]
  start := 0
  halt := [false, true, true]

def Compile.bitReadTM_exit_b0 : Nat := 1
def Compile.bitReadTM_exit_b1 : Nat := 2

theorem Compile.bitReadTM_tapes : Compile.bitReadTM.tapes = 1 := rfl
theorem Compile.bitReadTM_start : Compile.bitReadTM.start = 0 := rfl
theorem Compile.bitReadTM_sig : Compile.bitReadTM.sig = 4 := rfl
theorem Compile.bitReadTM_states : Compile.bitReadTM.states = 3 := rfl

theorem Compile.bitReadTM_valid : validFlatTM Compile.bitReadTM := by
  refine ⟨show (0 : Nat) < 3 from by decide, rfl, ?_⟩
  intro entry hentry
  rcases List.mem_cons.mp hentry with h0 | hrest
  · subst h0
    refine ⟨show (0:Nat) < 3 from by decide, show (1:Nat) < 3 from by decide, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; simp [Compile.bitReadBit0Entry] at hx; subst hx; decide
    · intro x hx; simp [Compile.bitReadBit0Entry] at hx; subst hx; trivial
  · rcases List.mem_cons.mp hrest with h1 | hnil
    · subst h1
      refine ⟨show (0:Nat) < 3 from by decide, show (2:Nat) < 3 from by decide, rfl, rfl, rfl, ?_, ?_⟩
      · intro x hx; simp [Compile.bitReadBit1Entry] at hx; subst hx; decide
      · intro x hx; simp [Compile.bitReadBit1Entry] at hx; subst hx; trivial
    · exact absurd hnil (by simp)

/-- On a `bit+1` cell (`bit ≤ 1`), `bitReadTM` steps to state `bit+1`. -/
theorem Compile.bitReadTM_step (bit : Nat) (hb : bit ≤ 1)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length) (h_get : right.get ⟨head, h_head_lt⟩ = bit + 1) :
    stepFlatTM Compile.bitReadTM
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := bit + 1, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym : currentTapeSymbol (left, head, right) = some (bit + 1) := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hSym' : cfg.tapes.map currentTapeSymbol = [some (bit + 1)] := by
    show [currentTapeSymbol (left, head, right)] = [some (bit + 1)]; rw [hSym]
  show Option.bind (Compile.bitReadTM.trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  interval_cases bit
  · have hMatch : entryMatchesConfig Compile.bitReadBit0Entry cfg = true := by
      show ((0 : Nat) == cfg.state_idx &&
              decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    show Option.bind ([Compile.bitReadBit0Entry, Compile.bitReadBit1Entry].find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
    rw [List.find?_cons, hMatch]; rfl
  · have hNo0 : entryMatchesConfig Compile.bitReadBit0Entry cfg = false := by
      show ((0 : Nat) == cfg.state_idx &&
              decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
      rw [hSym']
      have h_ne' : ([some 1] : List (Option Nat)) ≠ [some (1 + 1)] := by decide
      simp [h_ne']
    have hMatch : entryMatchesConfig Compile.bitReadBit1Entry cfg = true := by
      show ((0 : Nat) == cfg.state_idx &&
              decide (([some 2] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    show Option.bind ([Compile.bitReadBit0Entry, Compile.bitReadBit1Entry].find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
    rw [List.find?_cons, hNo0, List.find?_cons, hMatch]; rfl

/-- `bitReadTM` run: `bit+1` cell → state `bit+1` in 1 step. -/
theorem Compile.bitReadTM_run (bit : Nat) (hb : bit ≤ 1)
    (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length) (h_get : right.get ⟨head, h_head_lt⟩ = bit + 1) :
    runFlatTM 1 Compile.bitReadTM
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := bit + 1, tapes := [(left, head, right)] } := by
  show (if haltingStateReached Compile.bitReadTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.bitReadTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.bitReadTM cfg') = _
  rw [show haltingStateReached Compile.bitReadTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.bitReadTM_step bit hb left right head h_head_lt h_get]
  rfl

/-- `bitReadTM` never halts before its single step. -/
theorem Compile.bitReadTM_no_early_halt (left right : List Nat) (head : Nat) :
    ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.bitReadTM
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧
      ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧
      haltingStateReached Compile.bitReadTM ck = false := by
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  simp [runFlatTM] at hck; subst hck
  refine ⟨?_, ?_, rfl⟩
  · show (0 : Nat) ≠ 1; omega
  · show (0 : Nat) ≠ 2; omega

/-- The halt states of `bitReadTM` are exactly `1` and `2`. -/
theorem Compile.bitReadTM_halt_only (i : Nat)
    (hi : Compile.bitReadTM.halt[i]? = some true) : i = 1 ∨ i = 2 := by
  change ([false, true, true] : List Bool)[i]? = some true at hi
  rcases i with _ | _ | _ | i <;> simp_all

/-- The delim-branch body for `head`: rewind to the leading sentinel, then **clear**
register `dst` (no append). Writes `[]` to `dst`. Mirror of `nonEmptyBranchBody`
but with `clearRegionTM` (clear-only) instead of `clearAppendM`. -/
def Compile.clearOnlyBranchBody (dst : Var) : FlatTM :=
  composeFlatTM (ScanLeft.scanLeftUntilTM 4 3) (ClearGadget.clearRegionTM dst) 1

def Compile.clearOnlyBranchBody_exit (dst : Var) : Nat :=
  (ScanLeft.scanLeftUntilTM 4 3).states + ClearGadget.clearRegionTM_exit dst

theorem Compile.clearOnlyBranchBody_tapes (dst : Var) :
    (Compile.clearOnlyBranchBody dst).tapes = 1 := by
  rw [Compile.clearOnlyBranchBody, composeFlatTM_tapes]; rfl

theorem Compile.clearOnlyBranchBody_sig (dst : Var) :
    (Compile.clearOnlyBranchBody dst).sig = 4 := by
  rw [Compile.clearOnlyBranchBody, composeFlatTM_sig, ClearGadget.clearRegionTM_sig]; rfl

theorem Compile.clearOnlyBranchBody_valid (dst : Var) :
    validFlatTM (Compile.clearOnlyBranchBody dst) :=
  composeFlatTM_valid _ _ _ (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (ClearGadget.clearRegionTM_valid dst) (by decide)
    rfl (ClearGadget.clearRegionTM_tapes dst)

theorem Compile.clearOnlyBranchBody_halt_unique (dst : Var) :
    ∀ i, (Compile.clearOnlyBranchBody dst).halt[i]? = some true →
      i = Compile.clearOnlyBranchBody_exit dst := by
  rw [Compile.clearOnlyBranchBody, Compile.clearOnlyBranchBody_exit]
  exact Compile.composeFlatTM_halt_unique _ _ _ _ (Compile.opClear dst).halt_unique

theorem Compile.clearOnlyBranchBody_exit_is_halt (dst : Var) :
    (Compile.clearOnlyBranchBody dst).halt[Compile.clearOnlyBranchBody_exit dst]? = some true := by
  rw [Compile.clearOnlyBranchBody, Compile.clearOnlyBranchBody_exit]
  exact Compile.composeFlatTM_halt_intro _ _ _ _ (Compile.opClear dst).exit_is_halt

theorem Compile.clearOnlyBranchBody_exit_lt (dst : Var) :
    Compile.clearOnlyBranchBody_exit dst < (Compile.clearOnlyBranchBody dst).states := by
  rw [Compile.clearOnlyBranchBody_exit, Compile.clearOnlyBranchBody, composeFlatTM_states]
  have := Compile.clearRegionTM_exit_lt dst
  omega

/-! #### Inner machine: read the first bit, write `[bit]`. -/

/-- The raw (two-exit) inner `head` machine: `bitReadTM` reads `src`'s first cell,
branching to `nonEmptyBranchBody dst 2` (writes `[1]`) on bit 1, or
`nonEmptyBranchBody dst 1` (writes `[0]`) on bit 0. -/
def Compile.innerBitRawM (dst : Var) : FlatTM :=
  branchComposeFlatTM Compile.bitReadTM
    (Compile.nonEmptyBranchBody dst 2 (by decide))
    (Compile.nonEmptyBranchBody dst 1 (by decide))
    Compile.bitReadTM_exit_b1 Compile.bitReadTM_exit_b0

/-- bit-1 exit (positive branch). -/
def Compile.innerBitRawM_h1 (dst : Var) : Nat :=
  Compile.bitReadTM.states + Compile.nonEmptyBranchBody_exit dst 2 (by decide)

/-- bit-0 exit (negative branch). -/
def Compile.innerBitRawM_h2 (dst : Var) : Nat :=
  Compile.bitReadTM.states + (Compile.nonEmptyBranchBody dst 2 (by decide)).states
    + Compile.nonEmptyBranchBody_exit dst 1 (by decide)

theorem Compile.innerBitRawM_valid (dst : Var) : validFlatTM (Compile.innerBitRawM dst) :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.bitReadTM_valid
    (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
    (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide)
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide)
    Compile.bitReadTM_tapes
    (Compile.nonEmptyBranchBody_tapes dst 2 (by decide))
    (Compile.nonEmptyBranchBody_tapes dst 1 (by decide))

theorem Compile.innerBitRawM_tapes (dst : Var) : (Compile.innerBitRawM dst).tapes = 1 := by
  rw [Compile.innerBitRawM, branchComposeFlatTM_tapes]; exact Compile.bitReadTM_tapes

theorem Compile.innerBitRawM_sig (dst : Var) : (Compile.innerBitRawM dst).sig = 4 := by
  rw [Compile.innerBitRawM, branchComposeFlatTM_sig, Compile.bitReadTM_sig]
  rw [show (Compile.nonEmptyBranchBody dst 2 (by decide)).sig = 4 from by
        rw [Compile.nonEmptyBranchBody, composeFlatTM_sig, Compile.clearAppendM_sig]; rfl,
      show (Compile.nonEmptyBranchBody dst 1 (by decide)).sig = 4 from by
        rw [Compile.nonEmptyBranchBody, composeFlatTM_sig, Compile.clearAppendM_sig]; rfl]
  rfl

theorem Compile.innerBitRawM_h1_ne_h2 (dst : Var) :
    Compile.innerBitRawM_h1 dst ≠ Compile.innerBitRawM_h2 dst := by
  rw [Compile.innerBitRawM_h1, Compile.innerBitRawM_h2]
  have hb2 := Compile.nonEmptyBranchBody_exit_lt dst 2 (by decide)
  omega

theorem Compile.innerBitRawM_halt_only (dst : Var) :
    ∀ i, (Compile.innerBitRawM dst).halt[i]? = some true →
      i = Compile.innerBitRawM_h1 dst ∨ i = Compile.innerBitRawM_h2 dst := by
  rw [Compile.innerBitRawM_h1, Compile.innerBitRawM_h2, Compile.innerBitRawM]
  exact Compile.branchComposeFlatTM_halt_only _ _ _ _ _ _ _
    (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
    (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
    (Compile.nonEmptyBranchBody_halt_unique dst 2 (by decide))
    (Compile.nonEmptyBranchBody_halt_unique dst 1 (by decide))

theorem Compile.innerBitRawM_h1_is_halt (dst : Var) :
    (Compile.innerBitRawM dst).halt[Compile.innerBitRawM_h1 dst]? = some true := by
  rw [Compile.innerBitRawM_h1, Compile.innerBitRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
    (Compile.nonEmptyBranchBody_exit_lt dst 2 (by decide))
    (Compile.nonEmptyBranchBody_exit_is_halt dst 2 (by decide))

theorem Compile.innerBitRawM_h1_lt (dst : Var) :
    Compile.innerBitRawM_h1 dst < (Compile.innerBitRawM dst).states := by
  rw [Compile.innerBitRawM_h1, Compile.innerBitRawM, branchComposeFlatTM_states]
  have := Compile.nonEmptyBranchBody_exit_lt dst 2 (by decide)
  omega

theorem Compile.innerBitRawM_h2_is_halt (dst : Var) :
    (Compile.innerBitRawM dst).halt[Compile.innerBitRawM_h2 dst]? = some true := by
  rw [Compile.innerBitRawM_h2, Compile.innerBitRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
    (Compile.nonEmptyBranchBody_exit_is_halt dst 1 (by decide))

theorem Compile.innerBitRawM_h2_lt (dst : Var) :
    Compile.innerBitRawM_h2 dst < (Compile.innerBitRawM dst).states := by
  rw [Compile.innerBitRawM_h2, Compile.innerBitRawM, branchComposeFlatTM_states]
  have := Compile.nonEmptyBranchBody_exit_lt dst 1 (by decide)
  omega

/-- The inner `head` machine: read `src`'s first bit and write `[bit]` to `dst`.
The two `bitReadTM` exits merge through `joinTwoHalts`. -/
def Compile.opInnerBit (dst : Var) : CompiledCmd where
  M := joinTwoHalts (Compile.innerBitRawM dst)
        (Compile.innerBitRawM_h1 dst) (Compile.innerBitRawM_h2 dst)
  exit := Compile.innerBitRawM_h1 dst
  exit_lt := by
    rw [joinTwoHalts_states]; exact Compile.innerBitRawM_h1_lt dst
  exit_is_halt :=
    joinTwoHalts_h1_is_halt _ _ _ (Compile.innerBitRawM_h1_ne_h2 dst)
      (Compile.innerBitRawM_h1_is_halt dst)
  halt_unique :=
    joinTwoHalts_halt_unique _ _ _ (Compile.innerBitRawM_halt_only dst)
  M_valid := joinTwoHalts_valid _ _ _ (Compile.innerBitRawM_valid dst)
    (Compile.innerBitRawM_h1_lt dst) (Compile.innerBitRawM_h2_lt dst)
    (Compile.innerBitRawM_tapes dst)
  M_tapes := by rw [joinTwoHalts_tapes]; exact Compile.innerBitRawM_tapes dst
  M_sig := by rw [joinTwoHalts_sig]; exact Compile.innerBitRawM_sig dst

theorem Compile.opInnerBit_start (dst : Var) : (Compile.opInnerBit dst).M.start = 0 := by
  show (joinTwoHalts (Compile.innerBitRawM dst) _ _).start = 0
  rw [joinTwoHalts_start, Compile.innerBitRawM, branchComposeFlatTM_start]
  exact Compile.bitReadTM_start

/-! #### Outer machine: navigate, branch empty-vs-content, write the head. -/

/-- The raw (two-exit) outer `head` machine: `navigateAndTestTM src` branches
content (→ `opInnerBit`, writes `[first bit]`) vs delim (→ `clearOnlyBranchBody`,
writes `[]`). -/
def Compile.headRawM (dst src : Var) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
    (Compile.opInnerBit dst).M
    (Compile.clearOnlyBranchBody dst)
    (ClearGadget.navigateAndTestTM_exit_content src)
    (ClearGadget.navigateAndTestTM_exit_delim src)

/-- content exit (positive branch). -/
def Compile.headRawM_h1 (dst src : Var) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (Compile.opInnerBit dst).exit

/-- delim exit (negative branch). -/
def Compile.headRawM_h2 (dst src : Var) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (Compile.opInnerBit dst).M.states
    + Compile.clearOnlyBranchBody_exit dst

theorem Compile.headRawM_valid (dst src : Var) : validFlatTM (Compile.headRawM dst src) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.navigateAndTestTM_valid src)
    (Compile.opInnerBit dst).M_valid
    (Compile.clearOnlyBranchBody_valid dst)
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    (ClearGadget.navigateAndTestTM_tapes src)
    (Compile.opInnerBit dst).M_tapes
    (Compile.clearOnlyBranchBody_tapes dst)

theorem Compile.headRawM_tapes (dst src : Var) : (Compile.headRawM dst src).tapes = 1 := by
  rw [Compile.headRawM, branchComposeFlatTM_tapes]; exact ClearGadget.navigateAndTestTM_tapes src

theorem Compile.headRawM_sig (dst src : Var) : (Compile.headRawM dst src).sig = 4 := by
  rw [Compile.headRawM, branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig,
      (Compile.opInnerBit dst).M_sig, Compile.clearOnlyBranchBody_sig]
  rfl

theorem Compile.headRawM_h1_ne_h2 (dst src : Var) :
    Compile.headRawM_h1 dst src ≠ Compile.headRawM_h2 dst src := by
  rw [Compile.headRawM_h1, Compile.headRawM_h2]
  have := (Compile.opInnerBit dst).exit_lt
  omega

theorem Compile.headRawM_halt_only (dst src : Var) :
    ∀ i, (Compile.headRawM dst src).halt[i]? = some true →
      i = Compile.headRawM_h1 dst src ∨ i = Compile.headRawM_h2 dst src := by
  rw [Compile.headRawM_h1, Compile.headRawM_h2, Compile.headRawM]
  exact Compile.branchComposeFlatTM_halt_only _ _ _ _ _ _ _
    (Compile.opInnerBit dst).M_valid
    (Compile.clearOnlyBranchBody_valid dst)
    (Compile.opInnerBit dst).halt_unique
    (Compile.clearOnlyBranchBody_halt_unique dst)

theorem Compile.headRawM_h1_is_halt (dst src : Var) :
    (Compile.headRawM dst src).halt[Compile.headRawM_h1 dst src]? = some true := by
  rw [Compile.headRawM_h1, Compile.headRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.opInnerBit dst).M_valid
    (Compile.opInnerBit dst).exit_lt
    (Compile.opInnerBit dst).exit_is_halt

theorem Compile.headRawM_h1_lt (dst src : Var) :
    Compile.headRawM_h1 dst src < (Compile.headRawM dst src).states := by
  rw [Compile.headRawM_h1, Compile.headRawM, branchComposeFlatTM_states]
  have := (Compile.opInnerBit dst).exit_lt
  omega

theorem Compile.headRawM_h2_is_halt (dst src : Var) :
    (Compile.headRawM dst src).halt[Compile.headRawM_h2 dst src]? = some true := by
  rw [Compile.headRawM_h2, Compile.headRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.opInnerBit dst).M_valid
    (Compile.clearOnlyBranchBody_exit_is_halt dst)

theorem Compile.headRawM_h2_lt (dst src : Var) :
    Compile.headRawM_h2 dst src < (Compile.headRawM dst src).states := by
  rw [Compile.headRawM_h2, Compile.headRawM, branchComposeFlatTM_states]
  have := Compile.clearOnlyBranchBody_exit_lt dst
  omega

/-- Compile `Op.head dst src`: the nested `joinTwoHalts`-merged branch machine. -/
def Compile.opHead (dst src : Var) : CompiledCmd where
  M := joinTwoHalts (Compile.headRawM dst src)
        (Compile.headRawM_h1 dst src) (Compile.headRawM_h2 dst src)
  exit := Compile.headRawM_h1 dst src
  exit_lt := by
    rw [joinTwoHalts_states]; exact Compile.headRawM_h1_lt dst src
  exit_is_halt :=
    joinTwoHalts_h1_is_halt _ _ _ (Compile.headRawM_h1_ne_h2 dst src)
      (Compile.headRawM_h1_is_halt dst src)
  halt_unique :=
    joinTwoHalts_halt_unique _ _ _ (Compile.headRawM_halt_only dst src)
  M_valid := joinTwoHalts_valid _ _ _ (Compile.headRawM_valid dst src)
    (Compile.headRawM_h1_lt dst src) (Compile.headRawM_h2_lt dst src)
    (Compile.headRawM_tapes dst src)
  M_tapes := by rw [joinTwoHalts_tapes]; exact Compile.headRawM_tapes dst src
  M_sig := by rw [joinTwoHalts_sig]; exact Compile.headRawM_sig dst src

/-! ### `eqBit` machine defs + shape lemmas (relocated above `compileOp` to wire
the `eqBit` op — HANDOFF bottom-up Task 1(B). Behavioural run lemmas stay below,
after the copy/tail run lemmas they consume. -/
/-- The `eqBit` consume-loop ITERATE machine: delete `sc1`'s head, then `sc2`'s
head (both in place), entered at head `0`. -/
def Compile.iterTailsTM (sc1 sc2 : Var) : FlatTM :=
  composeFlatTM (Compile.opTail sc1 sc1).M (Compile.opTail sc2 sc2).M (Compile.opTail sc1 sc1).exit

/-- The composed (unique) exit of `iterTailsTM`: `opTail sc2`'s exit, shifted past
`opTail sc1`. Matches the exit reached by `iterTails_run`. -/
def Compile.iterTailsTM_exit (sc1 sc2 : Var) : Nat :=
  (Compile.opTail sc2 sc2).exit + (Compile.opTail sc1 sc1).M.states

theorem Compile.iterTailsTM_tapes (sc1 sc2 : Var) :
    (Compile.iterTailsTM sc1 sc2).tapes = 1 := by
  rw [Compile.iterTailsTM, composeFlatTM_tapes]; exact (Compile.opTail sc1 sc1).M_tapes

theorem Compile.iterTailsTM_sig (sc1 sc2 : Var) :
    (Compile.iterTailsTM sc1 sc2).sig = 4 := by
  rw [Compile.iterTailsTM, composeFlatTM_sig, (Compile.opTail sc1 sc1).M_sig,
      (Compile.opTail sc2 sc2).M_sig]; rfl

theorem Compile.iterTailsTM_start (sc1 sc2 : Var) :
    (Compile.iterTailsTM sc1 sc2).start = (Compile.opTail sc1 sc1).M.start := by
  rw [Compile.iterTailsTM, composeFlatTM_start]

theorem Compile.iterTailsTM_states (sc1 sc2 : Var) :
    (Compile.iterTailsTM sc1 sc2).states
      = (Compile.opTail sc1 sc1).M.states + (Compile.opTail sc2 sc2).M.states := by
  rw [Compile.iterTailsTM, composeFlatTM_states]

theorem Compile.iterTailsTM_valid (sc1 sc2 : Var) :
    validFlatTM (Compile.iterTailsTM sc1 sc2) :=
  composeFlatTM_valid (Compile.opTail sc1 sc1).M (Compile.opTail sc2 sc2).M
    (Compile.opTail sc1 sc1).exit (Compile.opTail sc1 sc1).M_valid (Compile.opTail sc2 sc2).M_valid
    (Compile.opTail sc1 sc1).exit_lt (Compile.opTail sc1 sc1).M_tapes (Compile.opTail sc2 sc2).M_tapes

theorem Compile.iterTailsTM_exit_lt (sc1 sc2 : Var) :
    Compile.iterTailsTM_exit sc1 sc2 < (Compile.iterTailsTM sc1 sc2).states := by
  rw [Compile.iterTailsTM_exit, Compile.iterTailsTM_states]
  have := (Compile.opTail sc2 sc2).exit_lt
  omega

theorem Compile.iterTailsTM_exit_is_halt (sc1 sc2 : Var) :
    (Compile.iterTailsTM sc1 sc2).halt[Compile.iterTailsTM_exit sc1 sc2]? = some true := by
  rw [Compile.iterTailsTM_exit, Compile.iterTailsTM]
  show (List.replicate (Compile.opTail sc1 sc1).M.states false ++ (Compile.opTail sc2 sc2).M.halt)[
      (Compile.opTail sc2 sc2).exit + (Compile.opTail sc1 sc1).M.states]? = some true
  rw [List.getElem?_append_right (by rw [List.length_replicate]; exact Nat.le_add_left _ _),
      List.length_replicate, Nat.add_sub_cancel]
  exact (Compile.opTail sc2 sc2).exit_is_halt

/-- **Halt-unique "rewind interior head to the leading sentinel" gadget.**
`justRewindTM` (`= scanLeftUntilTM 4 3`) has two static halt states — `1` (found
the sentinel) and `2` (boundary, reached only if no sentinel exists). On a tape
`(left, head, 3 :: rest)` with a terminator-free `rest[0..head)`, the boundary is
never reached, but it is still a static halt, so the bare machine is not
`halt_unique` and cannot serve as a clean single-exit branch leaf.
`opRewindToZero` demotes the boundary `2` via `joinTwoHalts`, leaving `1` as the
unique exit. -/
def Compile.opRewindToZero : CompiledCmd where
  M := joinTwoHalts ClearGadget.justRewindTM 1 2
  exit := 1
  exit_lt := by rw [joinTwoHalts_states]; show (1 : Nat) < 3; omega
  exit_is_halt := joinTwoHalts_h1_is_halt _ 1 2 (by decide) (by decide)
  halt_unique := joinTwoHalts_halt_unique _ 1 2 (by
    intro i hi
    change ([false, true, true] : List Bool)[i]? = some true at hi
    rcases i with _ | _ | _ | i <;> simp_all)
  M_valid := joinTwoHalts_valid _ 1 2 ClearGadget.justRewindTM_valid (by decide) (by decide)
    ClearGadget.justRewindTM_tapes
  M_tapes := by rw [joinTwoHalts_tapes]; exact ClearGadget.justRewindTM_tapes
  M_sig := by rw [joinTwoHalts_sig]; show ClearGadget.justRewindTM.sig = 4; rfl

theorem Compile.opRewindToZero_start : Compile.opRewindToZero.M.start = 0 := rfl

/-- Test register `sc` for emptiness, restoring the head to `0`. -/
def Compile.navTestRewindM (sc : Var) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM sc)
    Compile.opRewindToZero.M Compile.opRewindToZero.M
    (ClearGadget.navigateAndTestTM_exit_content sc)
    (ClearGadget.navigateAndTestTM_exit_delim sc)

/-- content (nonempty) exit. -/
def Compile.navTestRewindM_exit_content (sc : Var) : Nat :=
  (ClearGadget.navigateAndTestTM sc).states + Compile.opRewindToZero.exit
/-- delim (empty) exit. -/
def Compile.navTestRewindM_exit_delim (sc : Var) : Nat :=
  (ClearGadget.navigateAndTestTM sc).states + Compile.opRewindToZero.M.states
    + Compile.opRewindToZero.exit

theorem Compile.navTestRewindM_start (sc : Var) : (Compile.navTestRewindM sc).start = 0 := by
  rw [Compile.navTestRewindM, branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start sc

theorem Compile.navTestRewindM_tapes (sc : Var) : (Compile.navTestRewindM sc).tapes = 1 := by
  rw [Compile.navTestRewindM, branchComposeFlatTM_tapes]; exact ClearGadget.navigateAndTestTM_tapes sc

theorem Compile.navTestRewindM_sig (sc : Var) : (Compile.navTestRewindM sc).sig = 4 := by
  rw [Compile.navTestRewindM, branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig,
      Compile.opRewindToZero.M_sig]
  rfl

theorem Compile.navTestRewindM_valid (sc : Var) : validFlatTM (Compile.navTestRewindM sc) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.navigateAndTestTM_valid sc)
    Compile.opRewindToZero.M_valid Compile.opRewindToZero.M_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt sc)
    (ClearGadget.navigateAndTestTM_exit_delim_lt sc)
    (ClearGadget.navigateAndTestTM_tapes sc)
    Compile.opRewindToZero.M_tapes Compile.opRewindToZero.M_tapes

theorem Compile.navTestRewindM_exit_content_ne_delim (sc : Var) :
    Compile.navTestRewindM_exit_content sc ≠ Compile.navTestRewindM_exit_delim sc := by
  rw [Compile.navTestRewindM_exit_content, Compile.navTestRewindM_exit_delim]
  have := Compile.opRewindToZero.exit_lt
  omega

theorem Compile.navTestRewindM_halt_only (sc : Var) :
    ∀ i, (Compile.navTestRewindM sc).halt[i]? = some true →
      i = Compile.navTestRewindM_exit_content sc ∨ i = Compile.navTestRewindM_exit_delim sc := by
  rw [Compile.navTestRewindM_exit_content, Compile.navTestRewindM_exit_delim, Compile.navTestRewindM]
  exact Compile.branchComposeFlatTM_halt_only _ _ _ _ _ _ _
    Compile.opRewindToZero.M_valid Compile.opRewindToZero.M_valid
    Compile.opRewindToZero.halt_unique Compile.opRewindToZero.halt_unique

theorem Compile.navTestRewindM_exit_content_is_halt (sc : Var) :
    (Compile.navTestRewindM sc).halt[Compile.navTestRewindM_exit_content sc]? = some true := by
  rw [Compile.navTestRewindM_exit_content, Compile.navTestRewindM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    Compile.opRewindToZero.M_valid Compile.opRewindToZero.exit_lt Compile.opRewindToZero.exit_is_halt

theorem Compile.navTestRewindM_exit_delim_is_halt (sc : Var) :
    (Compile.navTestRewindM sc).halt[Compile.navTestRewindM_exit_delim sc]? = some true := by
  rw [Compile.navTestRewindM_exit_delim, Compile.navTestRewindM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    Compile.opRewindToZero.M_valid Compile.opRewindToZero.exit_is_halt

theorem Compile.navTestRewindM_exit_content_lt (sc : Var) :
    Compile.navTestRewindM_exit_content sc < (Compile.navTestRewindM sc).states := by
  rw [Compile.navTestRewindM_exit_content, Compile.navTestRewindM, branchComposeFlatTM_states]
  have := Compile.opRewindToZero.exit_lt
  omega

theorem Compile.navTestRewindM_exit_delim_lt (sc : Var) :
    Compile.navTestRewindM_exit_delim sc < (Compile.navTestRewindM sc).states := by
  rw [Compile.navTestRewindM_exit_delim, Compile.navTestRewindM, branchComposeFlatTM_states]
  have := Compile.opRewindToZero.exit_lt
  omega

/-- The inner read-and-rewind machine: from a head on `sc`'s first content cell,
read its bit (`bitReadTM`) and rewind to `0` (`opRewindToZero`), exiting in the
bit-dependent state `readRewindInner_exit b`. -/
def Compile.readRewindInnerM : FlatTM :=
  branchComposeFlatTM Compile.bitReadTM Compile.opRewindToZero.M Compile.opRewindToZero.M
    Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1

/-- The bit-`b` exit of `readRewindInnerM` (`b = 0` → positive `bitReadTM` branch,
`b = 1` → negative). -/
def Compile.readRewindInner_exit (b : Nat) : Nat :=
  Compile.opRewindToZero.exit + Compile.bitReadTM.states + b * Compile.opRewindToZero.M.states

theorem Compile.readRewindInnerM_start : Compile.readRewindInnerM.start = 0 := by
  rw [Compile.readRewindInnerM, branchComposeFlatTM_start]; exact Compile.bitReadTM_start

theorem Compile.readRewindInnerM_tapes : Compile.readRewindInnerM.tapes = 1 := by
  rw [Compile.readRewindInnerM, branchComposeFlatTM_tapes]; exact Compile.bitReadTM_tapes

theorem Compile.readRewindInnerM_sig : Compile.readRewindInnerM.sig = 4 := by
  rw [Compile.readRewindInnerM, branchComposeFlatTM_sig, Compile.bitReadTM_sig,
      Compile.opRewindToZero.M_sig]
  rfl

theorem Compile.readRewindInnerM_valid : validFlatTM Compile.readRewindInnerM :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.bitReadTM_valid
    Compile.opRewindToZero.M_valid Compile.opRewindToZero.M_valid
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide)
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide)
    Compile.bitReadTM_tapes Compile.opRewindToZero.M_tapes Compile.opRewindToZero.M_tapes

theorem Compile.readRewindInner_exit_b0_ne_b1 :
    Compile.readRewindInner_exit 0 ≠ Compile.readRewindInner_exit 1 := by
  rw [Compile.readRewindInner_exit, Compile.readRewindInner_exit]
  have := Compile.opRewindToZero.exit_lt
  omega

theorem Compile.readRewindInner_exit_lt (b : Nat) (hb : b ≤ 1) :
    Compile.readRewindInner_exit b < Compile.readRewindInnerM.states := by
  rw [Compile.readRewindInner_exit, Compile.readRewindInnerM, branchComposeFlatTM_states]
  have := Compile.opRewindToZero.exit_lt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h <;> subst h <;> simp <;> omega

theorem Compile.readRewindInnerM_halt_only :
    ∀ i, Compile.readRewindInnerM.halt[i]? = some true →
      i = Compile.readRewindInner_exit 0 ∨ i = Compile.readRewindInner_exit 1 := by
  intro i hi
  rw [Compile.readRewindInner_exit, Compile.readRewindInner_exit]
  have h := Compile.branchComposeFlatTM_halt_only Compile.bitReadTM
    Compile.opRewindToZero.M Compile.opRewindToZero.M _ _ _ _
    Compile.opRewindToZero.M_valid Compile.opRewindToZero.M_valid
    Compile.opRewindToZero.halt_unique Compile.opRewindToZero.halt_unique i hi
  rcases h with h | h
  · left; omega
  · right; omega

theorem Compile.readRewindInner_exit_b0_is_halt :
    Compile.readRewindInnerM.halt[Compile.readRewindInner_exit 0]? = some true := by
  rw [Compile.readRewindInner_exit, Compile.readRewindInnerM,
      show Compile.opRewindToZero.exit + Compile.bitReadTM.states + 0 * Compile.opRewindToZero.M.states
        = Compile.bitReadTM.states + Compile.opRewindToZero.exit from by omega]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    Compile.opRewindToZero.M_valid Compile.opRewindToZero.exit_lt Compile.opRewindToZero.exit_is_halt

theorem Compile.readRewindInner_exit_b1_is_halt :
    Compile.readRewindInnerM.halt[Compile.readRewindInner_exit 1]? = some true := by
  rw [Compile.readRewindInner_exit, Compile.readRewindInnerM,
      show Compile.opRewindToZero.exit + Compile.bitReadTM.states + 1 * Compile.opRewindToZero.M.states
        = Compile.bitReadTM.states + Compile.opRewindToZero.M.states + Compile.opRewindToZero.exit
        from by omega]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    Compile.opRewindToZero.M_valid Compile.opRewindToZero.exit_is_halt

/-- The raw read machine (3 halts: `b0`, `b1`, and the dead `sc`-empty rewind). The
bit-reader `readRewindInnerM` is the **negative** (content) branch. -/
def Compile.readBitRewindRawM (sc : Var) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM sc)
    Compile.opRewindToZero.M Compile.readRewindInnerM
    (ClearGadget.navigateAndTestTM_exit_delim sc)
    (ClearGadget.navigateAndTestTM_exit_content sc)

/-- dead exit (`sc` empty — `M₂`, positive/delim branch). -/
def Compile.readBitRewindRawM_dead (sc : Var) : Nat :=
  (ClearGadget.navigateAndTestTM sc).states + Compile.opRewindToZero.exit
/-- bit-`b` exit (`M₃` content branch). -/
def Compile.readBitRewindRawM_bit (sc : Var) (b : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM sc).states + Compile.opRewindToZero.M.states
    + Compile.readRewindInner_exit b

theorem Compile.readBitRewindRawM_start (sc : Var) :
    (Compile.readBitRewindRawM sc).start = 0 := by
  rw [Compile.readBitRewindRawM, branchComposeFlatTM_start]
  exact ClearGadget.navigateAndTestTM_start sc

theorem Compile.readBitRewindRawM_tapes (sc : Var) :
    (Compile.readBitRewindRawM sc).tapes = 1 := by
  rw [Compile.readBitRewindRawM, branchComposeFlatTM_tapes]
  exact ClearGadget.navigateAndTestTM_tapes sc

theorem Compile.readBitRewindRawM_sig (sc : Var) :
    (Compile.readBitRewindRawM sc).sig = 4 := by
  rw [Compile.readBitRewindRawM, branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig,
      Compile.opRewindToZero.M_sig, Compile.readRewindInnerM_sig]
  rfl

theorem Compile.readBitRewindRawM_states (sc : Var) :
    (Compile.readBitRewindRawM sc).states =
      (ClearGadget.navigateAndTestTM sc).states + Compile.opRewindToZero.M.states
        + Compile.readRewindInnerM.states := by
  rw [Compile.readBitRewindRawM, branchComposeFlatTM_states]

theorem Compile.readBitRewindRawM_dead_lt (sc : Var) :
    Compile.readBitRewindRawM_dead sc < (Compile.readBitRewindRawM sc).states := by
  rw [Compile.readBitRewindRawM_dead, Compile.readBitRewindRawM_states]
  have := Compile.opRewindToZero.exit_lt
  have := Compile.readRewindInner_exit_lt 0 (by omega)
  omega

theorem Compile.readBitRewindRawM_bit_lt (sc : Var) (b : Nat) (hb : b ≤ 1) :
    Compile.readBitRewindRawM_bit sc b < (Compile.readBitRewindRawM sc).states := by
  rw [Compile.readBitRewindRawM_bit, Compile.readBitRewindRawM_states]
  have := Compile.readRewindInner_exit_lt b hb
  omega

theorem Compile.readBitRewindRawM_dead_ne_b0 (sc : Var) :
    Compile.readBitRewindRawM_bit sc 0 ≠ Compile.readBitRewindRawM_dead sc := by
  rw [Compile.readBitRewindRawM_bit, Compile.readBitRewindRawM_dead,
      Compile.readRewindInner_exit]
  have := Compile.opRewindToZero.exit_lt
  omega

theorem Compile.readBitRewindRawM_b0_ne_b1 (sc : Var) :
    Compile.readBitRewindRawM_bit sc 0 ≠ Compile.readBitRewindRawM_bit sc 1 := by
  rw [Compile.readBitRewindRawM_bit, Compile.readBitRewindRawM_bit]
  have := Compile.readRewindInner_exit_b0_ne_b1
  omega

theorem Compile.readBitRewindRawM_valid (sc : Var) :
    validFlatTM (Compile.readBitRewindRawM sc) :=
  branchComposeFlatTM_valid _ _ _ _ _
    (ClearGadget.navigateAndTestTM_valid sc) Compile.opRewindToZero.M_valid
    Compile.readRewindInnerM_valid
    (ClearGadget.navigateAndTestTM_exit_delim_lt sc)
    (ClearGadget.navigateAndTestTM_exit_content_lt sc)
    (ClearGadget.navigateAndTestTM_tapes sc) Compile.opRewindToZero.M_tapes
    Compile.readRewindInnerM_tapes

theorem Compile.readBitRewindRawM_halt_only (sc : Var) :
    ∀ i, (Compile.readBitRewindRawM sc).halt[i]? = some true →
      i = Compile.readBitRewindRawM_dead sc ∨ i = Compile.readBitRewindRawM_bit sc 0
        ∨ i = Compile.readBitRewindRawM_bit sc 1 := by
  rw [Compile.readBitRewindRawM_dead, Compile.readBitRewindRawM_bit,
      Compile.readBitRewindRawM_bit, Compile.readBitRewindRawM]
  exact Compile.branchComposeFlatTM_halt_only_M3two _ _ _ _ _ _ _ _
    Compile.opRewindToZero.M_valid Compile.readRewindInnerM_valid
    Compile.opRewindToZero.halt_unique Compile.readRewindInnerM_halt_only

theorem Compile.readBitRewindRawM_dead_is_halt (sc : Var) :
    (Compile.readBitRewindRawM sc).halt[Compile.readBitRewindRawM_dead sc]? = some true := by
  rw [Compile.readBitRewindRawM_dead, Compile.readBitRewindRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    Compile.opRewindToZero.M_valid Compile.opRewindToZero.exit_lt Compile.opRewindToZero.exit_is_halt

theorem Compile.readBitRewindRawM_b0_is_halt (sc : Var) :
    (Compile.readBitRewindRawM sc).halt[Compile.readBitRewindRawM_bit sc 0]? = some true := by
  rw [Compile.readBitRewindRawM_bit, Compile.readBitRewindRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    Compile.opRewindToZero.M_valid Compile.readRewindInner_exit_b0_is_halt

theorem Compile.readBitRewindRawM_b1_is_halt (sc : Var) :
    (Compile.readBitRewindRawM sc).halt[Compile.readBitRewindRawM_bit sc 1]? = some true := by
  rw [Compile.readBitRewindRawM_bit, Compile.readBitRewindRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    Compile.opRewindToZero.M_valid Compile.readRewindInner_exit_b1_is_halt

/-- **The clean 2-exit read machine** = merge the dead `sc`-empty halt into `BIT0`. -/
def Compile.readBitRewindM (sc : Var) : FlatTM :=
  joinTwoHalts (Compile.readBitRewindRawM sc)
    (Compile.readBitRewindRawM_bit sc 0) (Compile.readBitRewindRawM_dead sc)

/-- bit-`0` exit. -/
def Compile.readBitRewindM_exit_b0 (sc : Var) : Nat := Compile.readBitRewindRawM_bit sc 0
/-- bit-`1` exit. -/
def Compile.readBitRewindM_exit_b1 (sc : Var) : Nat := Compile.readBitRewindRawM_bit sc 1

theorem Compile.readBitRewindM_start (sc : Var) : (Compile.readBitRewindM sc).start = 0 := by
  rw [Compile.readBitRewindM, joinTwoHalts_start]; exact Compile.readBitRewindRawM_start sc

theorem Compile.readBitRewindM_tapes (sc : Var) : (Compile.readBitRewindM sc).tapes = 1 := by
  rw [Compile.readBitRewindM, joinTwoHalts_tapes]; exact Compile.readBitRewindRawM_tapes sc

theorem Compile.readBitRewindM_sig (sc : Var) : (Compile.readBitRewindM sc).sig = 4 := by
  rw [Compile.readBitRewindM, joinTwoHalts_sig]; exact Compile.readBitRewindRawM_sig sc

theorem Compile.readBitRewindM_states (sc : Var) :
    (Compile.readBitRewindM sc).states = (Compile.readBitRewindRawM sc).states := rfl

theorem Compile.readBitRewindM_valid (sc : Var) : validFlatTM (Compile.readBitRewindM sc) :=
  joinTwoHalts_valid _ _ _ (Compile.readBitRewindRawM_valid sc)
    (Compile.readBitRewindRawM_bit_lt sc 0 (by omega)) (Compile.readBitRewindRawM_dead_lt sc)
    (Compile.readBitRewindRawM_tapes sc)

theorem Compile.readBitRewindM_exit_b0_ne_b1 (sc : Var) :
    Compile.readBitRewindM_exit_b0 sc ≠ Compile.readBitRewindM_exit_b1 sc :=
  Compile.readBitRewindRawM_b0_ne_b1 sc

theorem Compile.readBitRewindM_exit_b0_lt (sc : Var) :
    Compile.readBitRewindM_exit_b0 sc < (Compile.readBitRewindM sc).states := by
  rw [Compile.readBitRewindM_exit_b0, Compile.readBitRewindM_states]
  exact Compile.readBitRewindRawM_bit_lt sc 0 (by omega)

theorem Compile.readBitRewindM_exit_b1_lt (sc : Var) :
    Compile.readBitRewindM_exit_b1 sc < (Compile.readBitRewindM sc).states := by
  rw [Compile.readBitRewindM_exit_b1, Compile.readBitRewindM_states]
  exact Compile.readBitRewindRawM_bit_lt sc 1 (by omega)

theorem Compile.readBitRewindM_halt_only (sc : Var) :
    ∀ i, (Compile.readBitRewindM sc).halt[i]? = some true →
      i = Compile.readBitRewindM_exit_b0 sc ∨ i = Compile.readBitRewindM_exit_b1 sc := by
  intro i hi
  rw [Compile.readBitRewindM_exit_b0, Compile.readBitRewindM_exit_b1]
  change ((Compile.readBitRewindRawM sc).halt.set (Compile.readBitRewindRawM_dead sc) false)[i]?
    = some true at hi
  rw [List.getElem?_set] at hi
  by_cases h_eq : Compile.readBitRewindRawM_dead sc = i
  · exfalso; rw [if_pos h_eq] at hi; split at hi <;> simp at hi
  · rw [if_neg h_eq] at hi
    rcases Compile.readBitRewindRawM_halt_only sc i hi with h | h | h
    · exact absurd h.symm h_eq
    · exact Or.inl h
    · exact Or.inr h

theorem Compile.readBitRewindM_exit_b0_is_halt (sc : Var) :
    (Compile.readBitRewindM sc).halt[Compile.readBitRewindM_exit_b0 sc]? = some true := by
  rw [Compile.readBitRewindM_exit_b0, Compile.readBitRewindM]
  exact joinTwoHalts_h1_is_halt _ _ _
    (Compile.readBitRewindRawM_dead_ne_b0 sc) (Compile.readBitRewindRawM_b0_is_halt sc)

theorem Compile.readBitRewindM_exit_b1_is_halt (sc : Var) :
    (Compile.readBitRewindM sc).halt[Compile.readBitRewindM_exit_b1 sc]? = some true := by
  rw [Compile.readBitRewindM_exit_b1, Compile.readBitRewindM]
  show ((Compile.readBitRewindRawM sc).halt.set (Compile.readBitRewindRawM_dead sc) false)[Compile.readBitRewindRawM_bit sc 1]?
    = some true
  rw [List.getElem?_set_ne (by
    have := Compile.readBitRewindRawM_b0_ne_b1 sc
    rw [Compile.readBitRewindRawM_bit, Compile.readBitRewindRawM_bit,
        Compile.readBitRewindRawM_dead, Compile.readRewindInner_exit] at *
    have := Compile.opRewindToZero.exit_lt
    omega)]
  exact Compile.readBitRewindRawM_b1_is_halt sc

/-- Raw verdict machine (3 halts). -/
def Compile.eqVerdictRawM (sc1 sc2 : Var) : FlatTM :=
  branchComposeFlatTM (Compile.navTestRewindM sc1) Compile.idTM (Compile.navTestRewindM sc2)
    (Compile.navTestRewindM_exit_content sc1) (Compile.navTestRewindM_exit_delim sc1)

/-- NEQ exit when `sc1` is nonempty (positive `idTM` branch, head already `0`). -/
def Compile.eqVerdictRawM_neqA (sc1 : Var) : Nat := (Compile.navTestRewindM sc1).states
/-- NEQ exit when `sc1` empty but `sc2` nonempty (`M₃` content). -/
def Compile.eqVerdictRawM_neqB (sc1 sc2 : Var) : Nat :=
  (Compile.navTestRewindM sc1).states + Compile.idTM.states
    + Compile.navTestRewindM_exit_content sc2
/-- EQ exit when both empty (`M₃` delim). -/
def Compile.eqVerdictRawM_eq (sc1 sc2 : Var) : Nat :=
  (Compile.navTestRewindM sc1).states + Compile.idTM.states
    + Compile.navTestRewindM_exit_delim sc2

theorem Compile.eqVerdictRawM_start (sc1 sc2 : Var) : (Compile.eqVerdictRawM sc1 sc2).start = 0 := by
  rw [Compile.eqVerdictRawM, branchComposeFlatTM_start]; exact Compile.navTestRewindM_start sc1

theorem Compile.eqVerdictRawM_tapes (sc1 sc2 : Var) : (Compile.eqVerdictRawM sc1 sc2).tapes = 1 := by
  rw [Compile.eqVerdictRawM, branchComposeFlatTM_tapes]; exact Compile.navTestRewindM_tapes sc1

theorem Compile.eqVerdictRawM_sig (sc1 sc2 : Var) : (Compile.eqVerdictRawM sc1 sc2).sig = 4 := by
  rw [Compile.eqVerdictRawM, branchComposeFlatTM_sig, Compile.navTestRewindM_sig,
      Compile.navTestRewindM_sig]
  decide

theorem Compile.eqVerdictRawM_states (sc1 sc2 : Var) :
    (Compile.eqVerdictRawM sc1 sc2).states =
      (Compile.navTestRewindM sc1).states + Compile.idTM.states
        + (Compile.navTestRewindM sc2).states := by
  rw [Compile.eqVerdictRawM, branchComposeFlatTM_states]

theorem Compile.eqVerdictRawM_neqA_lt (sc1 sc2 : Var) :
    Compile.eqVerdictRawM_neqA sc1 < (Compile.eqVerdictRawM sc1 sc2).states := by
  rw [Compile.eqVerdictRawM_neqA, Compile.eqVerdictRawM_states]
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.eqVerdictRawM_neqB_lt (sc1 sc2 : Var) :
    Compile.eqVerdictRawM_neqB sc1 sc2 < (Compile.eqVerdictRawM sc1 sc2).states := by
  rw [Compile.eqVerdictRawM_neqB, Compile.eqVerdictRawM_states]
  have := Compile.navTestRewindM_exit_content_lt sc2
  omega

theorem Compile.eqVerdictRawM_eq_lt (sc1 sc2 : Var) :
    Compile.eqVerdictRawM_eq sc1 sc2 < (Compile.eqVerdictRawM sc1 sc2).states := by
  rw [Compile.eqVerdictRawM_eq, Compile.eqVerdictRawM_states]
  have := Compile.navTestRewindM_exit_delim_lt sc2
  omega

theorem Compile.eqVerdictRawM_neqA_ne_neqB (sc1 sc2 : Var) :
    Compile.eqVerdictRawM_neqA sc1 ≠ Compile.eqVerdictRawM_neqB sc1 sc2 := by
  rw [Compile.eqVerdictRawM_neqA, Compile.eqVerdictRawM_neqB]
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.eqVerdictRawM_neqB_ne_eq (sc1 sc2 : Var) :
    Compile.eqVerdictRawM_neqB sc1 sc2 ≠ Compile.eqVerdictRawM_eq sc1 sc2 := by
  rw [Compile.eqVerdictRawM_neqB, Compile.eqVerdictRawM_eq]
  have := Compile.navTestRewindM_exit_content_ne_delim sc2
  omega

theorem Compile.eqVerdictRawM_valid (sc1 sc2 : Var) :
    validFlatTM (Compile.eqVerdictRawM sc1 sc2) :=
  branchComposeFlatTM_valid _ _ _ _ _
    (Compile.navTestRewindM_valid sc1) Compile.idTM_valid (Compile.navTestRewindM_valid sc2)
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    (Compile.navTestRewindM_tapes sc1) rfl (Compile.navTestRewindM_tapes sc2)

theorem Compile.eqVerdictRawM_halt_only (sc1 sc2 : Var) :
    ∀ i, (Compile.eqVerdictRawM sc1 sc2).halt[i]? = some true →
      i = Compile.eqVerdictRawM_neqA sc1 ∨ i = Compile.eqVerdictRawM_neqB sc1 sc2
        ∨ i = Compile.eqVerdictRawM_eq sc1 sc2 := by
  rw [Compile.eqVerdictRawM_neqA, Compile.eqVerdictRawM_neqB, Compile.eqVerdictRawM_eq,
      Compile.eqVerdictRawM]
  exact Compile.branchComposeFlatTM_halt_only_M3two _ _ _ _ _ _ _ _
    Compile.idTM_valid (Compile.navTestRewindM_valid sc2)
    Compile.idTM_halt_unique (Compile.navTestRewindM_halt_only sc2)

theorem Compile.eqVerdictRawM_neqA_is_halt (sc1 sc2 : Var) :
    (Compile.eqVerdictRawM sc1 sc2).halt[Compile.eqVerdictRawM_neqA sc1]? = some true := by
  rw [Compile.eqVerdictRawM_neqA, Compile.eqVerdictRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ 0
    Compile.idTM_valid (by decide) (by decide)

theorem Compile.eqVerdictRawM_neqB_is_halt (sc1 sc2 : Var) :
    (Compile.eqVerdictRawM sc1 sc2).halt[Compile.eqVerdictRawM_neqB sc1 sc2]? = some true := by
  rw [Compile.eqVerdictRawM_neqB, Compile.eqVerdictRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    Compile.idTM_valid (Compile.navTestRewindM_exit_content_is_halt sc2)

theorem Compile.eqVerdictRawM_eq_is_halt (sc1 sc2 : Var) :
    (Compile.eqVerdictRawM sc1 sc2).halt[Compile.eqVerdictRawM_eq sc1 sc2]? = some true := by
  rw [Compile.eqVerdictRawM_eq, Compile.eqVerdictRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    Compile.idTM_valid (Compile.navTestRewindM_exit_delim_is_halt sc2)

/-- **The clean 2-exit verdict** = merge the two NEQ halts of the raw machine. -/
def Compile.eqVerdictM (sc1 sc2 : Var) : FlatTM :=
  joinTwoHalts (Compile.eqVerdictRawM sc1 sc2)
    (Compile.eqVerdictRawM_neqA sc1) (Compile.eqVerdictRawM_neqB sc1 sc2)

/-- NEQ exit (operands differ). -/
def Compile.eqVerdictM_exit_neq (sc1 : Var) : Nat := Compile.eqVerdictRawM_neqA sc1
/-- EQ exit (operands equal: both scratch registers empty). -/
def Compile.eqVerdictM_exit_eq (sc1 sc2 : Var) : Nat := Compile.eqVerdictRawM_eq sc1 sc2

theorem Compile.eqVerdictM_start (sc1 sc2 : Var) : (Compile.eqVerdictM sc1 sc2).start = 0 := by
  rw [Compile.eqVerdictM, joinTwoHalts_start]; exact Compile.eqVerdictRawM_start sc1 sc2

theorem Compile.eqVerdictM_tapes (sc1 sc2 : Var) : (Compile.eqVerdictM sc1 sc2).tapes = 1 := by
  rw [Compile.eqVerdictM, joinTwoHalts_tapes]; exact Compile.eqVerdictRawM_tapes sc1 sc2

theorem Compile.eqVerdictM_sig (sc1 sc2 : Var) : (Compile.eqVerdictM sc1 sc2).sig = 4 := by
  rw [Compile.eqVerdictM, joinTwoHalts_sig]; exact Compile.eqVerdictRawM_sig sc1 sc2

theorem Compile.eqVerdictM_states (sc1 sc2 : Var) :
    (Compile.eqVerdictM sc1 sc2).states = (Compile.eqVerdictRawM sc1 sc2).states := rfl

theorem Compile.eqVerdictM_valid (sc1 sc2 : Var) : validFlatTM (Compile.eqVerdictM sc1 sc2) :=
  joinTwoHalts_valid _ _ _ (Compile.eqVerdictRawM_valid sc1 sc2)
    (Compile.eqVerdictRawM_neqA_lt sc1 sc2) (Compile.eqVerdictRawM_neqB_lt sc1 sc2)
    (Compile.eqVerdictRawM_tapes sc1 sc2)

theorem Compile.eqVerdictM_exit_neq_ne_eq (sc1 sc2 : Var) :
    Compile.eqVerdictM_exit_neq sc1 ≠ Compile.eqVerdictM_exit_eq sc1 sc2 := by
  rw [Compile.eqVerdictM_exit_neq, Compile.eqVerdictM_exit_eq,
      Compile.eqVerdictRawM_neqA, Compile.eqVerdictRawM_eq]
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.eqVerdictM_exit_neq_lt (sc1 sc2 : Var) :
    Compile.eqVerdictM_exit_neq sc1 < (Compile.eqVerdictM sc1 sc2).states := by
  rw [Compile.eqVerdictM_exit_neq, Compile.eqVerdictM_states]
  exact Compile.eqVerdictRawM_neqA_lt sc1 sc2

theorem Compile.eqVerdictM_exit_eq_lt (sc1 sc2 : Var) :
    Compile.eqVerdictM_exit_eq sc1 sc2 < (Compile.eqVerdictM sc1 sc2).states := by
  rw [Compile.eqVerdictM_exit_eq, Compile.eqVerdictM_states]
  exact Compile.eqVerdictRawM_eq_lt sc1 sc2

theorem Compile.eqVerdictM_halt_only (sc1 sc2 : Var) :
    ∀ i, (Compile.eqVerdictM sc1 sc2).halt[i]? = some true →
      i = Compile.eqVerdictM_exit_neq sc1 ∨ i = Compile.eqVerdictM_exit_eq sc1 sc2 := by
  intro i hi
  rw [Compile.eqVerdictM_exit_neq, Compile.eqVerdictM_exit_eq]
  change ((Compile.eqVerdictRawM sc1 sc2).halt.set (Compile.eqVerdictRawM_neqB sc1 sc2) false)[i]?
    = some true at hi
  rw [List.getElem?_set] at hi
  by_cases h_eq : Compile.eqVerdictRawM_neqB sc1 sc2 = i
  · exfalso; rw [if_pos h_eq] at hi; split at hi <;> simp at hi
  · rw [if_neg h_eq] at hi
    rcases Compile.eqVerdictRawM_halt_only sc1 sc2 i hi with h | h | h
    · exact Or.inl h
    · exact absurd h.symm h_eq
    · exact Or.inr h

theorem Compile.eqVerdictM_exit_neq_is_halt (sc1 sc2 : Var) :
    (Compile.eqVerdictM sc1 sc2).halt[Compile.eqVerdictM_exit_neq sc1]? = some true := by
  rw [Compile.eqVerdictM_exit_neq, Compile.eqVerdictM]
  exact joinTwoHalts_h1_is_halt _ _ _
    (Compile.eqVerdictRawM_neqA_ne_neqB sc1 sc2) (Compile.eqVerdictRawM_neqA_is_halt sc1 sc2)

theorem Compile.eqVerdictM_exit_eq_is_halt (sc1 sc2 : Var) :
    (Compile.eqVerdictM sc1 sc2).halt[Compile.eqVerdictM_exit_eq sc1 sc2]? = some true := by
  rw [Compile.eqVerdictM_exit_eq, Compile.eqVerdictM]
  show ((Compile.eqVerdictRawM sc1 sc2).halt.set (Compile.eqVerdictRawM_neqB sc1 sc2) false)[Compile.eqVerdictRawM_eq sc1 sc2]?
    = some true
  rw [List.getElem?_set_ne (Compile.eqVerdictRawM_neqB_ne_eq sc1 sc2)]
  exact Compile.eqVerdictRawM_eq_is_halt sc1 sc2

/-- Raw bit-comparison machine (4 halts: `m00`/`m01`/`m10`/`m11`). -/
def Compile.bitCompareRawM (sc1 sc2 : Var) : FlatTM :=
  branchComposeFlatTM (Compile.readBitRewindM sc1) (Compile.readBitRewindM sc2)
    (Compile.readBitRewindM sc2)
    (Compile.readBitRewindM_exit_b0 sc1) (Compile.readBitRewindM_exit_b1 sc1)

/-- `a=0, b=0` raw exit — MATCH (kept MATCH exit). -/
def Compile.bitCompareRawM_m00 (sc1 sc2 : Var) : Nat :=
  (Compile.readBitRewindM sc1).states + Compile.readBitRewindM_exit_b0 sc2
/-- `a=0, b=1` raw exit — NOMATCH (kept NOMATCH exit). -/
def Compile.bitCompareRawM_m01 (sc1 sc2 : Var) : Nat :=
  (Compile.readBitRewindM sc1).states + Compile.readBitRewindM_exit_b1 sc2
/-- `a=1, b=0` raw exit — NOMATCH (demoted → `m01`). -/
def Compile.bitCompareRawM_m10 (sc1 sc2 : Var) : Nat :=
  (Compile.readBitRewindM sc1).states + (Compile.readBitRewindM sc2).states
    + Compile.readBitRewindM_exit_b0 sc2
/-- `a=1, b=1` raw exit — MATCH (demoted → `m00`). -/
def Compile.bitCompareRawM_m11 (sc1 sc2 : Var) : Nat :=
  (Compile.readBitRewindM sc1).states + (Compile.readBitRewindM sc2).states
    + Compile.readBitRewindM_exit_b1 sc2

theorem Compile.bitCompareRawM_start (sc1 sc2 : Var) :
    (Compile.bitCompareRawM sc1 sc2).start = 0 := by
  rw [Compile.bitCompareRawM, branchComposeFlatTM_start]; exact Compile.readBitRewindM_start sc1

theorem Compile.bitCompareRawM_tapes (sc1 sc2 : Var) :
    (Compile.bitCompareRawM sc1 sc2).tapes = 1 := by
  rw [Compile.bitCompareRawM, branchComposeFlatTM_tapes]; exact Compile.readBitRewindM_tapes sc1

theorem Compile.bitCompareRawM_sig (sc1 sc2 : Var) :
    (Compile.bitCompareRawM sc1 sc2).sig = 4 := by
  rw [Compile.bitCompareRawM, branchComposeFlatTM_sig, Compile.readBitRewindM_sig,
      Compile.readBitRewindM_sig]
  decide

theorem Compile.bitCompareRawM_states (sc1 sc2 : Var) :
    (Compile.bitCompareRawM sc1 sc2).states =
      (Compile.readBitRewindM sc1).states + (Compile.readBitRewindM sc2).states
        + (Compile.readBitRewindM sc2).states := by
  rw [Compile.bitCompareRawM, branchComposeFlatTM_states]

/-- `(readBitRewindM sc).states ≥ 1` (used for halt distinctness). -/
theorem Compile.readBitRewindM_states_pos (sc : Var) :
    0 < (Compile.readBitRewindM sc).states :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.readBitRewindM_exit_b0_lt sc)

theorem Compile.bitCompareRawM_m00_lt (sc1 sc2 : Var) :
    Compile.bitCompareRawM_m00 sc1 sc2 < (Compile.bitCompareRawM sc1 sc2).states := by
  rw [Compile.bitCompareRawM_m00, Compile.bitCompareRawM_states]
  have := Compile.readBitRewindM_exit_b0_lt sc2; have := Compile.readBitRewindM_states_pos sc2; omega

theorem Compile.bitCompareRawM_m01_lt (sc1 sc2 : Var) :
    Compile.bitCompareRawM_m01 sc1 sc2 < (Compile.bitCompareRawM sc1 sc2).states := by
  rw [Compile.bitCompareRawM_m01, Compile.bitCompareRawM_states]
  have := Compile.readBitRewindM_exit_b1_lt sc2; have := Compile.readBitRewindM_states_pos sc2; omega

theorem Compile.bitCompareRawM_m10_lt (sc1 sc2 : Var) :
    Compile.bitCompareRawM_m10 sc1 sc2 < (Compile.bitCompareRawM sc1 sc2).states := by
  rw [Compile.bitCompareRawM_m10, Compile.bitCompareRawM_states]
  have := Compile.readBitRewindM_exit_b0_lt sc2; omega

theorem Compile.bitCompareRawM_m11_lt (sc1 sc2 : Var) :
    Compile.bitCompareRawM_m11 sc1 sc2 < (Compile.bitCompareRawM sc1 sc2).states := by
  rw [Compile.bitCompareRawM_m11, Compile.bitCompareRawM_states]
  have := Compile.readBitRewindM_exit_b1_lt sc2; omega

/-- The four raw halts are pairwise distinct. Bundled for `omega` reuse. -/
theorem Compile.bitCompareRawM_distinct (sc1 sc2 : Var) :
    Compile.bitCompareRawM_m00 sc1 sc2 ≠ Compile.bitCompareRawM_m01 sc1 sc2 ∧
    Compile.bitCompareRawM_m00 sc1 sc2 ≠ Compile.bitCompareRawM_m10 sc1 sc2 ∧
    Compile.bitCompareRawM_m00 sc1 sc2 ≠ Compile.bitCompareRawM_m11 sc1 sc2 ∧
    Compile.bitCompareRawM_m01 sc1 sc2 ≠ Compile.bitCompareRawM_m10 sc1 sc2 ∧
    Compile.bitCompareRawM_m01 sc1 sc2 ≠ Compile.bitCompareRawM_m11 sc1 sc2 ∧
    Compile.bitCompareRawM_m10 sc1 sc2 ≠ Compile.bitCompareRawM_m11 sc1 sc2 := by
  rw [Compile.bitCompareRawM_m00, Compile.bitCompareRawM_m01, Compile.bitCompareRawM_m10,
      Compile.bitCompareRawM_m11]
  have h01 := Compile.readBitRewindM_exit_b0_ne_b1 sc2
  have h0 := Compile.readBitRewindM_exit_b0_lt sc2
  have h1 := Compile.readBitRewindM_exit_b1_lt sc2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem Compile.bitCompareRawM_valid (sc1 sc2 : Var) :
    validFlatTM (Compile.bitCompareRawM sc1 sc2) :=
  branchComposeFlatTM_valid _ _ _ _ _
    (Compile.readBitRewindM_valid sc1) (Compile.readBitRewindM_valid sc2)
    (Compile.readBitRewindM_valid sc2)
    (Compile.readBitRewindM_exit_b0_lt sc1) (Compile.readBitRewindM_exit_b1_lt sc1)
    (Compile.readBitRewindM_tapes sc1) (Compile.readBitRewindM_tapes sc2)
    (Compile.readBitRewindM_tapes sc2)

theorem Compile.bitCompareRawM_halt_only (sc1 sc2 : Var) :
    ∀ i, (Compile.bitCompareRawM sc1 sc2).halt[i]? = some true →
      i = Compile.bitCompareRawM_m00 sc1 sc2 ∨ i = Compile.bitCompareRawM_m01 sc1 sc2 ∨
        i = Compile.bitCompareRawM_m10 sc1 sc2 ∨ i = Compile.bitCompareRawM_m11 sc1 sc2 := by
  intro i hi
  rw [Compile.bitCompareRawM_m00, Compile.bitCompareRawM_m01, Compile.bitCompareRawM_m10,
      Compile.bitCompareRawM_m11]
  have h := Compile.branchComposeFlatTM_halt_only_M2two_M3two _ _ _ _ _ _ _ _ _
    (Compile.readBitRewindM_valid sc2) (Compile.readBitRewindM_valid sc2)
    (Compile.readBitRewindM_halt_only sc2) (Compile.readBitRewindM_halt_only sc2) i hi
  rw [Compile.readBitRewindM_exit_b0, Compile.readBitRewindM_exit_b1] at *
  rcases h with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem Compile.bitCompareRawM_m00_is_halt (sc1 sc2 : Var) :
    (Compile.bitCompareRawM sc1 sc2).halt[Compile.bitCompareRawM_m00 sc1 sc2]? = some true := by
  rw [Compile.bitCompareRawM_m00, Compile.bitCompareRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.readBitRewindM_valid sc2)
    (Compile.readBitRewindM_exit_b0_lt sc2) (Compile.readBitRewindM_exit_b0_is_halt sc2)

theorem Compile.bitCompareRawM_m01_is_halt (sc1 sc2 : Var) :
    (Compile.bitCompareRawM sc1 sc2).halt[Compile.bitCompareRawM_m01 sc1 sc2]? = some true := by
  rw [Compile.bitCompareRawM_m01, Compile.bitCompareRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.readBitRewindM_valid sc2)
    (Compile.readBitRewindM_exit_b1_lt sc2) (Compile.readBitRewindM_exit_b1_is_halt sc2)

theorem Compile.bitCompareRawM_m10_is_halt (sc1 sc2 : Var) :
    (Compile.bitCompareRawM sc1 sc2).halt[Compile.bitCompareRawM_m10 sc1 sc2]? = some true := by
  rw [Compile.bitCompareRawM_m10, Compile.bitCompareRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.readBitRewindM_valid sc2) (Compile.readBitRewindM_exit_b0_is_halt sc2)

theorem Compile.bitCompareRawM_m11_is_halt (sc1 sc2 : Var) :
    (Compile.bitCompareRawM sc1 sc2).halt[Compile.bitCompareRawM_m11 sc1 sc2]? = some true := by
  rw [Compile.bitCompareRawM_m11, Compile.bitCompareRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.readBitRewindM_valid sc2) (Compile.readBitRewindM_exit_b1_is_halt sc2)

/-- **The clean 2-exit bit-comparison machine** = merge the four raw halts down to
two via a double `joinTwoHalts` (`m11 → m00` for MATCH, `m10 → m01` for NOMATCH). -/
def Compile.bitCompareM (sc1 sc2 : Var) : FlatTM :=
  joinTwoHalts
    (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
      (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2))
    (Compile.bitCompareRawM_m01 sc1 sc2) (Compile.bitCompareRawM_m10 sc1 sc2)

/-- MATCH exit (first bits equal). -/
def Compile.bitCompareM_exit_match (sc1 sc2 : Var) : Nat := Compile.bitCompareRawM_m00 sc1 sc2
/-- NOMATCH exit (first bits differ). -/
def Compile.bitCompareM_exit_nomatch (sc1 sc2 : Var) : Nat := Compile.bitCompareRawM_m01 sc1 sc2

/-- The inner join (demote `m11`). -/
abbrev Compile.bitCompareInnerM (sc1 sc2 : Var) : FlatTM :=
  joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
    (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)

theorem Compile.bitCompareM_start (sc1 sc2 : Var) : (Compile.bitCompareM sc1 sc2).start = 0 := by
  rw [Compile.bitCompareM, joinTwoHalts_start, joinTwoHalts_start]
  exact Compile.bitCompareRawM_start sc1 sc2

theorem Compile.bitCompareM_tapes (sc1 sc2 : Var) : (Compile.bitCompareM sc1 sc2).tapes = 1 := by
  rw [Compile.bitCompareM, joinTwoHalts_tapes, joinTwoHalts_tapes]
  exact Compile.bitCompareRawM_tapes sc1 sc2

theorem Compile.bitCompareM_sig (sc1 sc2 : Var) : (Compile.bitCompareM sc1 sc2).sig = 4 := by
  rw [Compile.bitCompareM, joinTwoHalts_sig, joinTwoHalts_sig]
  exact Compile.bitCompareRawM_sig sc1 sc2

theorem Compile.bitCompareM_states (sc1 sc2 : Var) :
    (Compile.bitCompareM sc1 sc2).states = (Compile.bitCompareRawM sc1 sc2).states := rfl

theorem Compile.bitCompareM_valid (sc1 sc2 : Var) : validFlatTM (Compile.bitCompareM sc1 sc2) := by
  rw [Compile.bitCompareM]
  exact joinTwoHalts_valid _ _ _
    (joinTwoHalts_valid _ _ _ (Compile.bitCompareRawM_valid sc1 sc2)
      (Compile.bitCompareRawM_m00_lt sc1 sc2) (Compile.bitCompareRawM_m11_lt sc1 sc2)
      (Compile.bitCompareRawM_tapes sc1 sc2))
    (Compile.bitCompareRawM_m01_lt sc1 sc2) (Compile.bitCompareRawM_m10_lt sc1 sc2)
    (Compile.bitCompareRawM_tapes sc1 sc2)

theorem Compile.bitCompareM_exit_match_ne_nomatch (sc1 sc2 : Var) :
    Compile.bitCompareM_exit_match sc1 sc2 ≠ Compile.bitCompareM_exit_nomatch sc1 sc2 :=
  (Compile.bitCompareRawM_distinct sc1 sc2).1

theorem Compile.bitCompareM_exit_match_lt (sc1 sc2 : Var) :
    Compile.bitCompareM_exit_match sc1 sc2 < (Compile.bitCompareM sc1 sc2).states := by
  rw [Compile.bitCompareM_exit_match, Compile.bitCompareM_states]; exact Compile.bitCompareRawM_m00_lt sc1 sc2

theorem Compile.bitCompareM_exit_nomatch_lt (sc1 sc2 : Var) :
    Compile.bitCompareM_exit_nomatch sc1 sc2 < (Compile.bitCompareM sc1 sc2).states := by
  rw [Compile.bitCompareM_exit_nomatch, Compile.bitCompareM_states]; exact Compile.bitCompareRawM_m01_lt sc1 sc2

/-- The inner join keeps exactly `{m00, m01, m10}` as halts (demotes `m11`). -/
theorem Compile.bitCompareInnerM_halt_only (sc1 sc2 : Var) :
    ∀ i, (Compile.bitCompareInnerM sc1 sc2).halt[i]? = some true →
      i = Compile.bitCompareRawM_m00 sc1 sc2 ∨ i = Compile.bitCompareRawM_m01 sc1 sc2 ∨
        i = Compile.bitCompareRawM_m10 sc1 sc2 := by
  intro i hi
  change ((Compile.bitCompareRawM sc1 sc2).halt.set (Compile.bitCompareRawM_m11 sc1 sc2) false)[i]?
    = some true at hi
  rw [List.getElem?_set] at hi
  by_cases h_eq : Compile.bitCompareRawM_m11 sc1 sc2 = i
  · exfalso; rw [if_pos h_eq] at hi; split at hi <;> simp at hi
  · rw [if_neg h_eq] at hi
    rcases Compile.bitCompareRawM_halt_only sc1 sc2 i hi with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h.symm h_eq

theorem Compile.bitCompareM_halt_only (sc1 sc2 : Var) :
    ∀ i, (Compile.bitCompareM sc1 sc2).halt[i]? = some true →
      i = Compile.bitCompareM_exit_match sc1 sc2 ∨ i = Compile.bitCompareM_exit_nomatch sc1 sc2 := by
  intro i hi
  rw [Compile.bitCompareM_exit_match, Compile.bitCompareM_exit_nomatch]
  change ((Compile.bitCompareInnerM sc1 sc2).halt.set (Compile.bitCompareRawM_m10 sc1 sc2) false)[i]?
    = some true at hi
  rw [List.getElem?_set] at hi
  by_cases h_eq : Compile.bitCompareRawM_m10 sc1 sc2 = i
  · exfalso; rw [if_pos h_eq] at hi; split at hi <;> simp at hi
  · rw [if_neg h_eq] at hi
    rcases Compile.bitCompareInnerM_halt_only sc1 sc2 i hi with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h.symm h_eq

theorem Compile.bitCompareM_exit_match_is_halt (sc1 sc2 : Var) :
    (Compile.bitCompareM sc1 sc2).halt[Compile.bitCompareM_exit_match sc1 sc2]? = some true := by
  rw [Compile.bitCompareM_exit_match, Compile.bitCompareM]
  obtain ⟨_, hne_m00_m10, _, _, _, _⟩ := Compile.bitCompareRawM_distinct sc1 sc2
  show ((Compile.bitCompareInnerM sc1 sc2).halt.set (Compile.bitCompareRawM_m10 sc1 sc2) false)[Compile.bitCompareRawM_m00 sc1 sc2]?
    = some true
  rw [List.getElem?_set_ne (fun h => hne_m00_m10 h.symm)]
  exact joinTwoHalts_h1_is_halt _ _ _
    (Compile.bitCompareRawM_distinct sc1 sc2).2.2.1 (Compile.bitCompareRawM_m00_is_halt sc1 sc2)

theorem Compile.bitCompareM_exit_nomatch_is_halt (sc1 sc2 : Var) :
    (Compile.bitCompareM sc1 sc2).halt[Compile.bitCompareM_exit_nomatch sc1 sc2]? = some true := by
  rw [Compile.bitCompareM_exit_nomatch, Compile.bitCompareM]
  obtain ⟨_, _, _, hne_m01_m10, hne_m01_m11, _⟩ := Compile.bitCompareRawM_distinct sc1 sc2
  refine joinTwoHalts_h1_is_halt _ _ _ hne_m01_m10 ?_
  show ((Compile.bitCompareRawM sc1 sc2).halt.set (Compile.bitCompareRawM_m11 sc1 sc2) false)[Compile.bitCompareRawM_m01 sc1 sc2]?
    = some true
  rw [List.getElem?_set_ne (fun h => hne_m01_m11 h.symm)]
  exact Compile.bitCompareRawM_m01_is_halt sc1 sc2

/-- Raw guard machine (3 halts). -/
def Compile.bothNonemptyRawM (sc1 sc2 : Var) : FlatTM :=
  branchComposeFlatTM (Compile.navTestRewindM sc1) (Compile.navTestRewindM sc2) Compile.idTM
    (Compile.navTestRewindM_exit_content sc1) (Compile.navTestRewindM_exit_delim sc1)

/-- YES exit (both nonempty): positive `navTestRewindM sc2` content. -/
def Compile.bothNonemptyRawM_yes (sc1 sc2 : Var) : Nat :=
  (Compile.navTestRewindM sc1).states + Compile.navTestRewindM_exit_content sc2
/-- NO_b exit (`sc1` nonempty, `sc2` empty): positive `navTestRewindM sc2` delim. -/
def Compile.bothNonemptyRawM_noB (sc1 sc2 : Var) : Nat :=
  (Compile.navTestRewindM sc1).states + Compile.navTestRewindM_exit_delim sc2
/-- NO_a exit (`sc1` empty): negative `idTM` exit `0`. -/
def Compile.bothNonemptyRawM_noA (sc1 sc2 : Var) : Nat :=
  (Compile.navTestRewindM sc1).states + (Compile.navTestRewindM sc2).states

theorem Compile.bothNonemptyRawM_start (sc1 sc2 : Var) :
    (Compile.bothNonemptyRawM sc1 sc2).start = 0 := by
  rw [Compile.bothNonemptyRawM, branchComposeFlatTM_start]; exact Compile.navTestRewindM_start sc1

theorem Compile.bothNonemptyRawM_tapes (sc1 sc2 : Var) :
    (Compile.bothNonemptyRawM sc1 sc2).tapes = 1 := by
  rw [Compile.bothNonemptyRawM, branchComposeFlatTM_tapes]; exact Compile.navTestRewindM_tapes sc1

theorem Compile.bothNonemptyRawM_sig (sc1 sc2 : Var) :
    (Compile.bothNonemptyRawM sc1 sc2).sig = 4 := by
  rw [Compile.bothNonemptyRawM, branchComposeFlatTM_sig, Compile.navTestRewindM_sig,
      Compile.navTestRewindM_sig]
  decide

theorem Compile.bothNonemptyRawM_states (sc1 sc2 : Var) :
    (Compile.bothNonemptyRawM sc1 sc2).states =
      (Compile.navTestRewindM sc1).states + (Compile.navTestRewindM sc2).states
        + Compile.idTM.states := by
  rw [Compile.bothNonemptyRawM, branchComposeFlatTM_states]

theorem Compile.bothNonemptyRawM_yes_lt (sc1 sc2 : Var) :
    Compile.bothNonemptyRawM_yes sc1 sc2 < (Compile.bothNonemptyRawM sc1 sc2).states := by
  rw [Compile.bothNonemptyRawM_yes, Compile.bothNonemptyRawM_states]
  have := Compile.navTestRewindM_exit_content_lt sc2
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.bothNonemptyRawM_noB_lt (sc1 sc2 : Var) :
    Compile.bothNonemptyRawM_noB sc1 sc2 < (Compile.bothNonemptyRawM sc1 sc2).states := by
  rw [Compile.bothNonemptyRawM_noB, Compile.bothNonemptyRawM_states]
  have := Compile.navTestRewindM_exit_delim_lt sc2
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.bothNonemptyRawM_noA_lt (sc1 sc2 : Var) :
    Compile.bothNonemptyRawM_noA sc1 sc2 < (Compile.bothNonemptyRawM sc1 sc2).states := by
  rw [Compile.bothNonemptyRawM_noA, Compile.bothNonemptyRawM_states]
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.bothNonemptyRawM_yes_ne_noB (sc1 sc2 : Var) :
    Compile.bothNonemptyRawM_yes sc1 sc2 ≠ Compile.bothNonemptyRawM_noB sc1 sc2 := by
  rw [Compile.bothNonemptyRawM_yes, Compile.bothNonemptyRawM_noB]
  have := Compile.navTestRewindM_exit_content_ne_delim sc2
  omega

theorem Compile.bothNonemptyRawM_yes_ne_noA (sc1 sc2 : Var) :
    Compile.bothNonemptyRawM_yes sc1 sc2 ≠ Compile.bothNonemptyRawM_noA sc1 sc2 := by
  rw [Compile.bothNonemptyRawM_yes, Compile.bothNonemptyRawM_noA]
  have := Compile.navTestRewindM_exit_content_lt sc2
  omega

theorem Compile.bothNonemptyRawM_noA_ne_noB (sc1 sc2 : Var) :
    Compile.bothNonemptyRawM_noA sc1 sc2 ≠ Compile.bothNonemptyRawM_noB sc1 sc2 := by
  rw [Compile.bothNonemptyRawM_noA, Compile.bothNonemptyRawM_noB]
  have := Compile.navTestRewindM_exit_delim_lt sc2
  omega

theorem Compile.bothNonemptyRawM_valid (sc1 sc2 : Var) :
    validFlatTM (Compile.bothNonemptyRawM sc1 sc2) :=
  branchComposeFlatTM_valid _ _ _ _ _
    (Compile.navTestRewindM_valid sc1) (Compile.navTestRewindM_valid sc2) Compile.idTM_valid
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    (Compile.navTestRewindM_tapes sc1) (Compile.navTestRewindM_tapes sc2) rfl

theorem Compile.bothNonemptyRawM_halt_only (sc1 sc2 : Var) :
    ∀ i, (Compile.bothNonemptyRawM sc1 sc2).halt[i]? = some true →
      i = Compile.bothNonemptyRawM_yes sc1 sc2 ∨ i = Compile.bothNonemptyRawM_noB sc1 sc2
        ∨ i = Compile.bothNonemptyRawM_noA sc1 sc2 := by
  rw [Compile.bothNonemptyRawM_yes, Compile.bothNonemptyRawM_noB, Compile.bothNonemptyRawM_noA,
      Compile.bothNonemptyRawM]
  exact Compile.branchComposeFlatTM_halt_only_M2two _ _ _ _ _ _ _ _
    (Compile.navTestRewindM_valid sc2) Compile.idTM_valid
    (Compile.navTestRewindM_halt_only sc2) Compile.idTM_halt_unique

theorem Compile.bothNonemptyRawM_yes_is_halt (sc1 sc2 : Var) :
    (Compile.bothNonemptyRawM sc1 sc2).halt[Compile.bothNonemptyRawM_yes sc1 sc2]? = some true := by
  rw [Compile.bothNonemptyRawM_yes, Compile.bothNonemptyRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.navTestRewindM_valid sc2) (Compile.navTestRewindM_exit_content_lt sc2)
    (Compile.navTestRewindM_exit_content_is_halt sc2)

theorem Compile.bothNonemptyRawM_noB_is_halt (sc1 sc2 : Var) :
    (Compile.bothNonemptyRawM sc1 sc2).halt[Compile.bothNonemptyRawM_noB sc1 sc2]? = some true := by
  rw [Compile.bothNonemptyRawM_noB, Compile.bothNonemptyRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.navTestRewindM_valid sc2) (Compile.navTestRewindM_exit_delim_lt sc2)
    (Compile.navTestRewindM_exit_delim_is_halt sc2)

theorem Compile.bothNonemptyRawM_noA_is_halt (sc1 sc2 : Var) :
    (Compile.bothNonemptyRawM sc1 sc2).halt[Compile.bothNonemptyRawM_noA sc1 sc2]? = some true := by
  rw [Compile.bothNonemptyRawM_noA, Compile.bothNonemptyRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.navTestRewindM_valid sc2) (show Compile.idTM.halt[(0 : Nat)]? = some true from rfl)

/-- **The clean 2-exit guard** = merge the two NO halts of the raw machine. -/
def Compile.bothNonemptyM (sc1 sc2 : Var) : FlatTM :=
  joinTwoHalts (Compile.bothNonemptyRawM sc1 sc2)
    (Compile.bothNonemptyRawM_noA sc1 sc2) (Compile.bothNonemptyRawM_noB sc1 sc2)

/-- YES exit (both nonempty). -/
def Compile.bothNonemptyM_exit_yes (sc1 sc2 : Var) : Nat := Compile.bothNonemptyRawM_yes sc1 sc2
/-- NO exit (at least one empty). -/
def Compile.bothNonemptyM_exit_no (sc1 sc2 : Var) : Nat := Compile.bothNonemptyRawM_noA sc1 sc2

theorem Compile.bothNonemptyM_start (sc1 sc2 : Var) : (Compile.bothNonemptyM sc1 sc2).start = 0 := by
  rw [Compile.bothNonemptyM, joinTwoHalts_start]; exact Compile.bothNonemptyRawM_start sc1 sc2

theorem Compile.bothNonemptyM_tapes (sc1 sc2 : Var) : (Compile.bothNonemptyM sc1 sc2).tapes = 1 := by
  rw [Compile.bothNonemptyM, joinTwoHalts_tapes]; exact Compile.bothNonemptyRawM_tapes sc1 sc2

theorem Compile.bothNonemptyM_sig (sc1 sc2 : Var) : (Compile.bothNonemptyM sc1 sc2).sig = 4 := by
  rw [Compile.bothNonemptyM, joinTwoHalts_sig]; exact Compile.bothNonemptyRawM_sig sc1 sc2

theorem Compile.bothNonemptyM_states (sc1 sc2 : Var) :
    (Compile.bothNonemptyM sc1 sc2).states = (Compile.bothNonemptyRawM sc1 sc2).states := rfl

theorem Compile.bothNonemptyM_valid (sc1 sc2 : Var) : validFlatTM (Compile.bothNonemptyM sc1 sc2) :=
  joinTwoHalts_valid _ _ _ (Compile.bothNonemptyRawM_valid sc1 sc2)
    (Compile.bothNonemptyRawM_noA_lt sc1 sc2) (Compile.bothNonemptyRawM_noB_lt sc1 sc2)
    (Compile.bothNonemptyRawM_tapes sc1 sc2)

theorem Compile.bothNonemptyM_exit_yes_ne_no (sc1 sc2 : Var) :
    Compile.bothNonemptyM_exit_yes sc1 sc2 ≠ Compile.bothNonemptyM_exit_no sc1 sc2 := by
  rw [Compile.bothNonemptyM_exit_yes, Compile.bothNonemptyM_exit_no]
  exact Compile.bothNonemptyRawM_yes_ne_noA sc1 sc2

theorem Compile.bothNonemptyM_exit_yes_lt (sc1 sc2 : Var) :
    Compile.bothNonemptyM_exit_yes sc1 sc2 < (Compile.bothNonemptyM sc1 sc2).states := by
  rw [Compile.bothNonemptyM_exit_yes, Compile.bothNonemptyM_states]
  exact Compile.bothNonemptyRawM_yes_lt sc1 sc2

theorem Compile.bothNonemptyM_exit_no_lt (sc1 sc2 : Var) :
    Compile.bothNonemptyM_exit_no sc1 sc2 < (Compile.bothNonemptyM sc1 sc2).states := by
  rw [Compile.bothNonemptyM_exit_no, Compile.bothNonemptyM_states]
  exact Compile.bothNonemptyRawM_noA_lt sc1 sc2

theorem Compile.bothNonemptyM_halt_only (sc1 sc2 : Var) :
    ∀ i, (Compile.bothNonemptyM sc1 sc2).halt[i]? = some true →
      i = Compile.bothNonemptyM_exit_yes sc1 sc2 ∨ i = Compile.bothNonemptyM_exit_no sc1 sc2 := by
  intro i hi
  rw [Compile.bothNonemptyM_exit_yes, Compile.bothNonemptyM_exit_no]
  change ((Compile.bothNonemptyRawM sc1 sc2).halt.set (Compile.bothNonemptyRawM_noB sc1 sc2) false)[i]?
    = some true at hi
  rw [List.getElem?_set] at hi
  by_cases h_eq : Compile.bothNonemptyRawM_noB sc1 sc2 = i
  · exfalso; rw [if_pos h_eq] at hi; split at hi <;> simp at hi
  · rw [if_neg h_eq] at hi
    rcases Compile.bothNonemptyRawM_halt_only sc1 sc2 i hi with h | h | h
    · exact Or.inl h
    · exact absurd h.symm h_eq
    · exact Or.inr h

theorem Compile.bothNonemptyM_exit_yes_is_halt (sc1 sc2 : Var) :
    (Compile.bothNonemptyM sc1 sc2).halt[Compile.bothNonemptyM_exit_yes sc1 sc2]? = some true := by
  rw [Compile.bothNonemptyM_exit_yes, Compile.bothNonemptyM]
  show ((Compile.bothNonemptyRawM sc1 sc2).halt.set (Compile.bothNonemptyRawM_noB sc1 sc2) false)[Compile.bothNonemptyRawM_yes sc1 sc2]?
    = some true
  rw [List.getElem?_set_ne (fun h => Compile.bothNonemptyRawM_yes_ne_noB sc1 sc2 h.symm)]
  exact Compile.bothNonemptyRawM_yes_is_halt sc1 sc2

theorem Compile.bothNonemptyM_exit_no_is_halt (sc1 sc2 : Var) :
    (Compile.bothNonemptyM sc1 sc2).halt[Compile.bothNonemptyM_exit_no sc1 sc2]? = some true := by
  rw [Compile.bothNonemptyM_exit_no, Compile.bothNonemptyM]
  exact joinTwoHalts_h1_is_halt _ _ _
    (Compile.bothNonemptyRawM_noA_ne_noB sc1 sc2) (Compile.bothNonemptyRawM_noA_is_halt sc1 sc2)

/-- Raw decision machine (3 halts). -/
def Compile.testMachineRawM (sc1 sc2 : Var) : FlatTM :=
  branchComposeFlatTM (Compile.bothNonemptyM sc1 sc2) (Compile.bitCompareM sc1 sc2) Compile.idTM
    (Compile.bothNonemptyM_exit_yes sc1 sc2) (Compile.bothNonemptyM_exit_no sc1 sc2)

/-- ITER exit (both nonempty, bits match): positive `bitCompareM` MATCH. -/
def Compile.testMachineRawM_iter (sc1 sc2 : Var) : Nat :=
  (Compile.bothNonemptyM sc1 sc2).states + Compile.bitCompareM_exit_match sc1 sc2
/-- NOMATCH exit (both nonempty, bits differ): positive `bitCompareM` NOMATCH. -/
def Compile.testMachineRawM_nomatch (sc1 sc2 : Var) : Nat :=
  (Compile.bothNonemptyM sc1 sc2).states + Compile.bitCompareM_exit_nomatch sc1 sc2
/-- DONE_a exit (at least one empty): negative `idTM` exit `0`. -/
def Compile.testMachineRawM_done (sc1 sc2 : Var) : Nat :=
  (Compile.bothNonemptyM sc1 sc2).states + (Compile.bitCompareM sc1 sc2).states

theorem Compile.testMachineRawM_start (sc1 sc2 : Var) :
    (Compile.testMachineRawM sc1 sc2).start = 0 := by
  rw [Compile.testMachineRawM, branchComposeFlatTM_start]; exact Compile.bothNonemptyM_start sc1 sc2

theorem Compile.testMachineRawM_tapes (sc1 sc2 : Var) :
    (Compile.testMachineRawM sc1 sc2).tapes = 1 := by
  rw [Compile.testMachineRawM, branchComposeFlatTM_tapes]; exact Compile.bothNonemptyM_tapes sc1 sc2

theorem Compile.testMachineRawM_sig (sc1 sc2 : Var) :
    (Compile.testMachineRawM sc1 sc2).sig = 4 := by
  rw [Compile.testMachineRawM, branchComposeFlatTM_sig, Compile.bothNonemptyM_sig,
      Compile.bitCompareM_sig]
  decide

theorem Compile.testMachineRawM_states (sc1 sc2 : Var) :
    (Compile.testMachineRawM sc1 sc2).states =
      (Compile.bothNonemptyM sc1 sc2).states + (Compile.bitCompareM sc1 sc2).states
        + Compile.idTM.states := by
  rw [Compile.testMachineRawM, branchComposeFlatTM_states]

theorem Compile.testMachineRawM_iter_lt (sc1 sc2 : Var) :
    Compile.testMachineRawM_iter sc1 sc2 < (Compile.testMachineRawM sc1 sc2).states := by
  rw [Compile.testMachineRawM_iter, Compile.testMachineRawM_states]
  have := Compile.bitCompareM_exit_match_lt sc1 sc2
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.testMachineRawM_nomatch_lt (sc1 sc2 : Var) :
    Compile.testMachineRawM_nomatch sc1 sc2 < (Compile.testMachineRawM sc1 sc2).states := by
  rw [Compile.testMachineRawM_nomatch, Compile.testMachineRawM_states]
  have := Compile.bitCompareM_exit_nomatch_lt sc1 sc2
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.testMachineRawM_done_lt (sc1 sc2 : Var) :
    Compile.testMachineRawM_done sc1 sc2 < (Compile.testMachineRawM sc1 sc2).states := by
  rw [Compile.testMachineRawM_done, Compile.testMachineRawM_states]
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.testMachineRawM_iter_ne_nomatch (sc1 sc2 : Var) :
    Compile.testMachineRawM_iter sc1 sc2 ≠ Compile.testMachineRawM_nomatch sc1 sc2 := by
  rw [Compile.testMachineRawM_iter, Compile.testMachineRawM_nomatch]
  have := Compile.bitCompareM_exit_match_ne_nomatch sc1 sc2
  omega

theorem Compile.testMachineRawM_iter_ne_done (sc1 sc2 : Var) :
    Compile.testMachineRawM_iter sc1 sc2 ≠ Compile.testMachineRawM_done sc1 sc2 := by
  rw [Compile.testMachineRawM_iter, Compile.testMachineRawM_done]
  have := Compile.bitCompareM_exit_match_lt sc1 sc2
  omega

theorem Compile.testMachineRawM_done_ne_nomatch (sc1 sc2 : Var) :
    Compile.testMachineRawM_done sc1 sc2 ≠ Compile.testMachineRawM_nomatch sc1 sc2 := by
  rw [Compile.testMachineRawM_done, Compile.testMachineRawM_nomatch]
  have := Compile.bitCompareM_exit_nomatch_lt sc1 sc2
  omega

theorem Compile.testMachineRawM_valid (sc1 sc2 : Var) :
    validFlatTM (Compile.testMachineRawM sc1 sc2) :=
  branchComposeFlatTM_valid _ _ _ _ _
    (Compile.bothNonemptyM_valid sc1 sc2) (Compile.bitCompareM_valid sc1 sc2) Compile.idTM_valid
    (Compile.bothNonemptyM_exit_yes_lt sc1 sc2) (Compile.bothNonemptyM_exit_no_lt sc1 sc2)
    (Compile.bothNonemptyM_tapes sc1 sc2) (Compile.bitCompareM_tapes sc1 sc2) rfl

theorem Compile.testMachineRawM_halt_only (sc1 sc2 : Var) :
    ∀ i, (Compile.testMachineRawM sc1 sc2).halt[i]? = some true →
      i = Compile.testMachineRawM_iter sc1 sc2 ∨ i = Compile.testMachineRawM_nomatch sc1 sc2
        ∨ i = Compile.testMachineRawM_done sc1 sc2 := by
  rw [Compile.testMachineRawM_iter, Compile.testMachineRawM_nomatch, Compile.testMachineRawM_done,
      Compile.testMachineRawM]
  exact Compile.branchComposeFlatTM_halt_only_M2two
    (Compile.bothNonemptyM sc1 sc2) (Compile.bitCompareM sc1 sc2) Compile.idTM
    (Compile.bothNonemptyM_exit_yes sc1 sc2) (Compile.bothNonemptyM_exit_no sc1 sc2)
    (Compile.bitCompareM_exit_match sc1 sc2) (Compile.bitCompareM_exit_nomatch sc1 sc2) 0
    (Compile.bitCompareM_valid sc1 sc2) Compile.idTM_valid
    (Compile.bitCompareM_halt_only sc1 sc2) Compile.idTM_halt_unique

theorem Compile.testMachineRawM_iter_is_halt (sc1 sc2 : Var) :
    (Compile.testMachineRawM sc1 sc2).halt[Compile.testMachineRawM_iter sc1 sc2]? = some true := by
  rw [Compile.testMachineRawM_iter, Compile.testMachineRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.bitCompareM_valid sc1 sc2) (Compile.bitCompareM_exit_match_lt sc1 sc2)
    (Compile.bitCompareM_exit_match_is_halt sc1 sc2)

theorem Compile.testMachineRawM_nomatch_is_halt (sc1 sc2 : Var) :
    (Compile.testMachineRawM sc1 sc2).halt[Compile.testMachineRawM_nomatch sc1 sc2]? = some true := by
  rw [Compile.testMachineRawM_nomatch, Compile.testMachineRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.bitCompareM_valid sc1 sc2) (Compile.bitCompareM_exit_nomatch_lt sc1 sc2)
    (Compile.bitCompareM_exit_nomatch_is_halt sc1 sc2)

theorem Compile.testMachineRawM_done_is_halt (sc1 sc2 : Var) :
    (Compile.testMachineRawM sc1 sc2).halt[Compile.testMachineRawM_done sc1 sc2]? = some true := by
  rw [Compile.testMachineRawM_done, Compile.testMachineRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro
    (Compile.bothNonemptyM sc1 sc2) (Compile.bitCompareM sc1 sc2) Compile.idTM
    (Compile.bothNonemptyM_exit_yes sc1 sc2) (Compile.bothNonemptyM_exit_no sc1 sc2) 0
    (Compile.bitCompareM_valid sc1 sc2) (show Compile.idTM.halt[(0 : Nat)]? = some true from rfl)

/-- **The clean 2-exit decision** = merge NOMATCH + DONE_a of the raw machine. -/
def Compile.testMachine (sc1 sc2 : Var) : FlatTM :=
  joinTwoHalts (Compile.testMachineRawM sc1 sc2)
    (Compile.testMachineRawM_done sc1 sc2) (Compile.testMachineRawM_nomatch sc1 sc2)

/-- ITER exit (delete both heads, continue). -/
def Compile.testMachine_exit_iter (sc1 sc2 : Var) : Nat := Compile.testMachineRawM_iter sc1 sc2
/-- DONE exit (stop the consume loop). -/
def Compile.testMachine_exit_done (sc1 sc2 : Var) : Nat := Compile.testMachineRawM_done sc1 sc2

theorem Compile.testMachine_start (sc1 sc2 : Var) : (Compile.testMachine sc1 sc2).start = 0 := by
  rw [Compile.testMachine, joinTwoHalts_start]; exact Compile.testMachineRawM_start sc1 sc2

theorem Compile.testMachine_tapes (sc1 sc2 : Var) : (Compile.testMachine sc1 sc2).tapes = 1 := by
  rw [Compile.testMachine, joinTwoHalts_tapes]; exact Compile.testMachineRawM_tapes sc1 sc2

theorem Compile.testMachine_sig (sc1 sc2 : Var) : (Compile.testMachine sc1 sc2).sig = 4 := by
  rw [Compile.testMachine, joinTwoHalts_sig]; exact Compile.testMachineRawM_sig sc1 sc2

theorem Compile.testMachine_states (sc1 sc2 : Var) :
    (Compile.testMachine sc1 sc2).states = (Compile.testMachineRawM sc1 sc2).states := rfl

theorem Compile.testMachine_valid (sc1 sc2 : Var) : validFlatTM (Compile.testMachine sc1 sc2) :=
  joinTwoHalts_valid _ _ _ (Compile.testMachineRawM_valid sc1 sc2)
    (Compile.testMachineRawM_done_lt sc1 sc2) (Compile.testMachineRawM_nomatch_lt sc1 sc2)
    (Compile.testMachineRawM_tapes sc1 sc2)

theorem Compile.testMachine_exit_iter_ne_done (sc1 sc2 : Var) :
    Compile.testMachine_exit_iter sc1 sc2 ≠ Compile.testMachine_exit_done sc1 sc2 := by
  rw [Compile.testMachine_exit_iter, Compile.testMachine_exit_done]
  exact Compile.testMachineRawM_iter_ne_done sc1 sc2

theorem Compile.testMachine_exit_iter_lt (sc1 sc2 : Var) :
    Compile.testMachine_exit_iter sc1 sc2 < (Compile.testMachine sc1 sc2).states := by
  rw [Compile.testMachine_exit_iter, Compile.testMachine_states]
  exact Compile.testMachineRawM_iter_lt sc1 sc2

theorem Compile.testMachine_exit_done_lt (sc1 sc2 : Var) :
    Compile.testMachine_exit_done sc1 sc2 < (Compile.testMachine sc1 sc2).states := by
  rw [Compile.testMachine_exit_done, Compile.testMachine_states]
  exact Compile.testMachineRawM_done_lt sc1 sc2

theorem Compile.testMachine_halt_only (sc1 sc2 : Var) :
    ∀ i, (Compile.testMachine sc1 sc2).halt[i]? = some true →
      i = Compile.testMachine_exit_iter sc1 sc2 ∨ i = Compile.testMachine_exit_done sc1 sc2 := by
  intro i hi
  rw [Compile.testMachine_exit_iter, Compile.testMachine_exit_done]
  change ((Compile.testMachineRawM sc1 sc2).halt.set (Compile.testMachineRawM_nomatch sc1 sc2) false)[i]?
    = some true at hi
  rw [List.getElem?_set] at hi
  by_cases h_eq : Compile.testMachineRawM_nomatch sc1 sc2 = i
  · exfalso; rw [if_pos h_eq] at hi; split at hi <;> simp at hi
  · rw [if_neg h_eq] at hi
    rcases Compile.testMachineRawM_halt_only sc1 sc2 i hi with h | h | h
    · exact Or.inl h
    · exact absurd h.symm h_eq
    · exact Or.inr h

theorem Compile.testMachine_exit_iter_is_halt (sc1 sc2 : Var) :
    (Compile.testMachine sc1 sc2).halt[Compile.testMachine_exit_iter sc1 sc2]? = some true := by
  rw [Compile.testMachine_exit_iter, Compile.testMachine]
  show ((Compile.testMachineRawM sc1 sc2).halt.set (Compile.testMachineRawM_nomatch sc1 sc2) false)[Compile.testMachineRawM_iter sc1 sc2]?
    = some true
  rw [List.getElem?_set_ne (fun h => Compile.testMachineRawM_iter_ne_nomatch sc1 sc2 h.symm)]
  exact Compile.testMachineRawM_iter_is_halt sc1 sc2

theorem Compile.testMachine_exit_done_is_halt (sc1 sc2 : Var) :
    (Compile.testMachine sc1 sc2).halt[Compile.testMachine_exit_done sc1 sc2]? = some true := by
  rw [Compile.testMachine_exit_done, Compile.testMachine]
  exact joinTwoHalts_h1_is_halt _ _ _
    (Compile.testMachineRawM_done_ne_nomatch sc1 sc2) (Compile.testMachineRawM_done_is_halt sc1 sc2)

def Compile.compareBodyTM (sc1 sc2 : Var) : FlatTM :=
  branchComposeFlatTM (Compile.testMachine sc1 sc2) (Compile.iterTailsTM sc1 sc2) Compile.idTM
    (Compile.testMachine_exit_iter sc1 sc2) (Compile.testMachine_exit_done sc1 sc2)

/-- `exitLoop`: the ITER (`iterTailsTM`) exit, continue the consume loop. -/
def Compile.compareBodyTM_exitLoop (sc1 sc2 : Var) : Nat :=
  (Compile.testMachine sc1 sc2).states + Compile.iterTailsTM_exit sc1 sc2

/-- `exitDone`: the DONE (`idTM`) exit, stop the consume loop. -/
def Compile.compareBodyTM_exitDone (sc1 sc2 : Var) : Nat :=
  (Compile.testMachine sc1 sc2).states + (Compile.iterTailsTM sc1 sc2).states

theorem Compile.compareBodyTM_tapes (sc1 sc2 : Var) :
    (Compile.compareBodyTM sc1 sc2).tapes = 1 := by
  rw [Compile.compareBodyTM, branchComposeFlatTM_tapes]; exact Compile.testMachine_tapes sc1 sc2

theorem Compile.compareBodyTM_start (sc1 sc2 : Var) :
    (Compile.compareBodyTM sc1 sc2).start = 0 := by
  rw [Compile.compareBodyTM, branchComposeFlatTM_start]; exact Compile.testMachine_start sc1 sc2

theorem Compile.compareBodyTM_sig (sc1 sc2 : Var) :
    (Compile.compareBodyTM sc1 sc2).sig = 4 := by
  rw [Compile.compareBodyTM, branchComposeFlatTM_sig, Compile.testMachine_sig,
      Compile.iterTailsTM_sig]; decide

theorem Compile.compareBodyTM_states (sc1 sc2 : Var) :
    (Compile.compareBodyTM sc1 sc2).states =
      (Compile.testMachine sc1 sc2).states + (Compile.iterTailsTM sc1 sc2).states
        + Compile.idTM.states := by
  rw [Compile.compareBodyTM, branchComposeFlatTM_states]

theorem Compile.compareBodyTM_valid (sc1 sc2 : Var) :
    validFlatTM (Compile.compareBodyTM sc1 sc2) :=
  branchComposeFlatTM_valid _ _ _ _ _
    (Compile.testMachine_valid sc1 sc2) (Compile.iterTailsTM_valid sc1 sc2) Compile.idTM_valid
    (Compile.testMachine_exit_iter_lt sc1 sc2) (Compile.testMachine_exit_done_lt sc1 sc2)
    (Compile.testMachine_tapes sc1 sc2) (Compile.iterTailsTM_tapes sc1 sc2) rfl

theorem Compile.compareBodyTM_exitLoop_lt (sc1 sc2 : Var) :
    Compile.compareBodyTM_exitLoop sc1 sc2 < (Compile.compareBodyTM sc1 sc2).states := by
  rw [Compile.compareBodyTM_exitLoop, Compile.compareBodyTM_states]
  have := Compile.iterTailsTM_exit_lt sc1 sc2
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.compareBodyTM_exitDone_lt (sc1 sc2 : Var) :
    Compile.compareBodyTM_exitDone sc1 sc2 < (Compile.compareBodyTM sc1 sc2).states := by
  rw [Compile.compareBodyTM_exitDone, Compile.compareBodyTM_states]
  have hid : Compile.idTM.states = 1 := rfl
  omega

theorem Compile.compareBodyTM_exitDone_ne_exitLoop (sc1 sc2 : Var) :
    Compile.compareBodyTM_exitDone sc1 sc2 ≠ Compile.compareBodyTM_exitLoop sc1 sc2 := by
  rw [Compile.compareBodyTM_exitDone, Compile.compareBodyTM_exitLoop]
  have := Compile.iterTailsTM_exit_lt sc1 sc2
  omega

theorem Compile.compareBodyTM_exitLoop_is_halt (sc1 sc2 : Var) :
    (Compile.compareBodyTM sc1 sc2).halt[Compile.compareBodyTM_exitLoop sc1 sc2]? = some true := by
  rw [Compile.compareBodyTM_exitLoop, Compile.compareBodyTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.iterTailsTM_valid sc1 sc2) (Compile.iterTailsTM_exit_lt sc1 sc2)
    (Compile.iterTailsTM_exit_is_halt sc1 sc2)

theorem Compile.compareBodyTM_exitDone_is_halt (sc1 sc2 : Var) :
    (Compile.compareBodyTM sc1 sc2).halt[Compile.compareBodyTM_exitDone sc1 sc2]? = some true := by
  rw [Compile.compareBodyTM_exitDone, Compile.compareBodyTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro
    (Compile.testMachine sc1 sc2) (Compile.iterTailsTM sc1 sc2) Compile.idTM
    (Compile.testMachine_exit_iter sc1 sc2) (Compile.testMachine_exit_done sc1 sc2) 0
    (Compile.iterTailsTM_valid sc1 sc2)
    (show Compile.idTM.halt[(0 : Nat)]? = some true from rfl)

def Compile.compareLoopTM (sc1 sc2 : Var) : FlatTM :=
  loopTM (Compile.compareBodyTM sc1 sc2)
    (Compile.compareBodyTM_exitDone sc1 sc2) (Compile.compareBodyTM_exitLoop sc1 sc2)

def Compile.copyEmptyRawTM (dst src : Var) : FlatTM :=
  composeFlatTM
    (composeFlatTM (ClearGadget.navigateToRegTM src) (Compile.copyLoopTM dst)
      (ClearGadget.navigateToRegTM_exit src))
    ClearGadget.justRewindTM
    ((2 + 3 * src) + (55 + 6 * dst))

/-- States below the final `justRewindTM` block. -/
def Compile.copyEmptyPreStates (dst src : Var) : Nat := (2 + 3 * src) + (56 + 6 * dst)

/-- The kept "found" exit: `justRewindTM`'s found state `1`, shifted. -/
def Compile.copyEmptyRawTM_exit (dst src : Var) : Nat := Compile.copyEmptyPreStates dst src + 1

theorem Compile.copyEmptyRawTM_states (dst src : Nat) :
    (Compile.copyEmptyRawTM dst src).states = Compile.copyEmptyPreStates dst src + 3 := by
  show (composeFlatTM _ _ _).states = _
  repeat rw [composeFlatTM_states]
  rw [ClearGadget.navigateToRegTM_states, Compile.copyLoopTM_states]
  show (2 + 3 * src) + (56 + 6 * dst) + 3 = _
  rfl

theorem Compile.copyEmptyRawTM_tapes (dst src : Nat) :
    (Compile.copyEmptyRawTM dst src).tapes = 1 :=
  ClearGadget.navigateToRegTM_tapes src

theorem Compile.copyEmptyRawTM_sig (dst src : Nat) :
    (Compile.copyEmptyRawTM dst src).sig = 4 := by
  show max (max (ClearGadget.navigateToRegTM src).sig (Compile.copyLoopTM dst).sig)
      ClearGadget.justRewindTM.sig = 4
  rw [ClearGadget.navigateToRegTM_sig, Compile.copyLoopTM_sig]
  rfl

theorem Compile.copyEmptyRawTM_valid (dst src : Nat) :
    validFlatTM (Compile.copyEmptyRawTM dst src) := by
  refine composeFlatTM_valid _ _ _ (composeFlatTM_valid _ _ _
      (ClearGadget.navigateToRegTM_valid src) (Compile.copyLoopTM_valid dst)
      (ClearGadget.navigateToRegTM_exit_lt src)
      (ClearGadget.navigateToRegTM_tapes src) (Compile.copyLoopTM_tapes dst))
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide)) ?_ ?_ rfl
  · -- loop exit (seam) < composed (nav⨾loop) states
    rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states, Compile.copyLoopTM_states]
    omega
  · show (composeFlatTM _ _ _).tapes = 1
    exact ClearGadget.navigateToRegTM_tapes src

/-- `justRewindTM`'s found state `1`, shifted, IS a halt of the raw chain. -/
theorem Compile.copyEmptyRawTM_exit_is_halt (dst src : Nat) :
    (Compile.copyEmptyRawTM dst src).halt[Compile.copyEmptyRawTM_exit dst src]?
      = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro
    (composeFlatTM (ClearGadget.navigateToRegTM src) (Compile.copyLoopTM dst)
      (ClearGadget.navigateToRegTM_exit src))
    ClearGadget.justRewindTM
    ((2 + 3 * src) + (55 + 6 * dst))
    1 (by rfl)
  have hpre : (composeFlatTM (ClearGadget.navigateToRegTM src) (Compile.copyLoopTM dst)
      (ClearGadget.navigateToRegTM_exit src)).states = Compile.copyEmptyPreStates dst src := by
    rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states, Compile.copyLoopTM_states]
    rfl
  rw [hpre] at h
  exact h

theorem Compile.copyEmptyRawTM_start (dst src : Var) :
    (Compile.copyEmptyRawTM dst src).start = 0 := by
  show (composeFlatTM _ _ _).start = 0
  rw [composeFlatTM_start, composeFlatTM_start]; exact ClearGadget.navigateToRegTM_start src

theorem Compile.copyEmptyRawTM_exit_lt (dst src : Var) :
    Compile.copyEmptyRawTM_exit dst src < (Compile.copyEmptyRawTM dst src).states := by
  rw [Compile.copyEmptyRawTM_states, Compile.copyEmptyRawTM_exit]; omega

theorem Compile.compareLoopTM_valid (sc1 sc2 : Var) :
    validFlatTM (Compile.compareLoopTM sc1 sc2) :=
  loopTM_valid _ _ _ (Compile.compareBodyTM_valid sc1 sc2)
    (Compile.compareBodyTM_exitDone_lt sc1 sc2) (Compile.compareBodyTM_exitLoop_lt sc1 sc2)
    (Compile.compareBodyTM_tapes sc1 sc2)

theorem Compile.compareLoopTM_sig (sc1 sc2 : Var) : (Compile.compareLoopTM sc1 sc2).sig = 4 := by
  show (loopTM _ _ _).sig = 4; rw [loopTM_sig]; exact Compile.compareBodyTM_sig sc1 sc2

theorem Compile.compareLoopTM_tapes (sc1 sc2 : Var) : (Compile.compareLoopTM sc1 sc2).tapes = 1 := by
  show (loopTM _ _ _).tapes = 1; rw [loopTM_tapes]; exact Compile.compareBodyTM_tapes sc1 sc2

/-- `compareLoopTM`'s loop halt at `compareBodyTM.states` in `getElem?` form. -/
theorem Compile.compareLoopTM_halt_getElem (sc1 sc2 : Var) :
    (Compile.compareLoopTM sc1 sc2).halt[(Compile.compareBodyTM sc1 sc2).states]? = some true := by
  show (loopHalt (Compile.compareBodyTM sc1 sc2))[(Compile.compareBodyTM sc1 sc2).states]? = some true
  show (List.replicate (Compile.compareBodyTM sc1 sc2).states false ++ [true])[(Compile.compareBodyTM sc1 sc2).states]? = some true
  rw [List.getElem?_append_right (by rw [List.length_replicate]),
      List.length_replicate, Nat.sub_self]; rfl

def Compile.cmpNGCleanupM (sb : Var) : FlatTM :=
  composeFlatTM (ClearGadget.clearRegionTM sb) (ClearGadget.clearRegionTM (sb + 1))
    (ClearGadget.clearRegionTM_exit sb)

def Compile.cmpNGCleanupM_exit (sb : Var) : Nat :=
  (ClearGadget.clearRegionTM sb).states + ClearGadget.clearRegionTM_exit (sb + 1)

theorem Compile.cmpNGCleanupM_sig (sb : Var) : (Compile.cmpNGCleanupM sb).sig = 4 := by
  rw [Compile.cmpNGCleanupM, composeFlatTM_sig, ClearGadget.clearRegionTM_sig,
      ClearGadget.clearRegionTM_sig]; rfl

theorem Compile.cmpNGCleanupM_tapes (sb : Var) : (Compile.cmpNGCleanupM sb).tapes = 1 := by
  rw [Compile.cmpNGCleanupM, composeFlatTM_tapes]; exact ClearGadget.clearRegionTM_tapes sb

theorem Compile.cmpNGCleanupM_start (sb : Var) : (Compile.cmpNGCleanupM sb).start = 0 := by
  rw [Compile.cmpNGCleanupM, composeFlatTM_start, ClearGadget.clearRegionTM_start]

theorem Compile.cmpNGCleanupM_states (sb : Var) :
    (Compile.cmpNGCleanupM sb).states =
      (ClearGadget.clearRegionTM sb).states + (ClearGadget.clearRegionTM (sb + 1)).states := by
  rw [Compile.cmpNGCleanupM, composeFlatTM_states]

theorem Compile.cmpNGCleanupM_valid (sb : Var) : validFlatTM (Compile.cmpNGCleanupM sb) :=
  composeFlatTM_valid _ _ _ (ClearGadget.clearRegionTM_valid sb)
    (ClearGadget.clearRegionTM_valid (sb + 1)) (Compile.clearRegionTM_exit_lt sb)
    (ClearGadget.clearRegionTM_tapes sb) (ClearGadget.clearRegionTM_tapes (sb + 1))

theorem Compile.cmpNGCleanupM_exit_lt (sb : Var) :
    Compile.cmpNGCleanupM_exit sb < (Compile.cmpNGCleanupM sb).states := by
  rw [Compile.cmpNGCleanupM_exit, Compile.cmpNGCleanupM_states]
  have := Compile.clearRegionTM_exit_lt (sb + 1)
  omega

theorem Compile.cmpNGCleanupM_halt_getElem (sb : Var) :
    (Compile.cmpNGCleanupM sb).halt[Compile.cmpNGCleanupM_exit sb]? = some true := by
  have h := Compile.composeFlatTM_halt_intro (ClearGadget.clearRegionTM sb)
    (ClearGadget.clearRegionTM (sb + 1)) (ClearGadget.clearRegionTM_exit (sb + 1))
    (ClearGadget.clearRegionTM_exit sb) (Compile.opClear (sb + 1)).exit_is_halt
  rw [Compile.cmpNGCleanupM,
      show Compile.cmpNGCleanupM_exit sb
        = (ClearGadget.clearRegionTM sb).states + ClearGadget.clearRegionTM_exit (sb + 1) from
        rfl]
  exact h

def Compile.cmpNGPrefixM (sb src1 src2 : Var) : FlatTM :=
  composeFlatTM
    (composeFlatTM (Compile.copyEmptyRawTM sb src1) (Compile.copyEmptyRawTM (sb + 1) src2)
      (Compile.copyEmptyRawTM_exit sb src1))
    (Compile.compareLoopTM sb (sb + 1))
    ((Compile.copyEmptyRawTM sb src1).states + Compile.copyEmptyRawTM_exit (sb + 1) src2)

def Compile.cmpNGPrefixM_exit (sb src1 src2 : Var) : Nat :=
  (Compile.compareBodyTM sb (sb + 1)).states
    + ((Compile.copyEmptyRawTM sb src1).states + (Compile.copyEmptyRawTM (sb + 1) src2).states)

theorem Compile.cmpNGPrefixM_sig (sb src1 src2 : Var) :
    (Compile.cmpNGPrefixM sb src1 src2).sig = 4 := by
  rw [Compile.cmpNGPrefixM, composeFlatTM_sig, composeFlatTM_sig,
      Compile.copyEmptyRawTM_sig, Compile.copyEmptyRawTM_sig, Compile.compareLoopTM_sig]; rfl

theorem Compile.cmpNGPrefixM_tapes (sb src1 src2 : Var) :
    (Compile.cmpNGPrefixM sb src1 src2).tapes = 1 := by
  rw [Compile.cmpNGPrefixM, composeFlatTM_tapes, composeFlatTM_tapes]
  exact Compile.copyEmptyRawTM_tapes sb src1

theorem Compile.cmpNGPrefixM_start (sb src1 src2 : Var) :
    (Compile.cmpNGPrefixM sb src1 src2).start = 0 := by
  rw [Compile.cmpNGPrefixM, composeFlatTM_start, composeFlatTM_start, Compile.copyEmptyRawTM_start]

theorem Compile.cmpNGPrefixM_states (sb src1 src2 : Var) :
    (Compile.cmpNGPrefixM sb src1 src2).states =
      ((Compile.copyEmptyRawTM sb src1).states + (Compile.copyEmptyRawTM (sb + 1) src2).states)
        + (Compile.compareLoopTM sb (sb + 1)).states := by
  rw [Compile.cmpNGPrefixM, composeFlatTM_states, composeFlatTM_states]

theorem Compile.cmpNGPrefixM_valid (sb src1 src2 : Var) :
    validFlatTM (Compile.cmpNGPrefixM sb src1 src2) := by
  have hMB_valid := composeFlatTM_valid _ _ _ (Compile.copyEmptyRawTM_valid sb src1)
    (Compile.copyEmptyRawTM_valid (sb + 1) src2) (Compile.copyEmptyRawTM_exit_lt sb src1)
    (Compile.copyEmptyRawTM_tapes sb src1) (Compile.copyEmptyRawTM_tapes (sb + 1) src2)
  have hexit_lt : (Compile.copyEmptyRawTM sb src1).states + Compile.copyEmptyRawTM_exit (sb + 1) src2
      < (composeFlatTM (Compile.copyEmptyRawTM sb src1) (Compile.copyEmptyRawTM (sb + 1) src2)
          (Compile.copyEmptyRawTM_exit sb src1)).states := by
    rw [composeFlatTM_states]; exact Nat.add_lt_add_left (Compile.copyEmptyRawTM_exit_lt (sb + 1) src2) _
  rw [Compile.cmpNGPrefixM]
  exact composeFlatTM_valid _ _ _ hMB_valid (Compile.compareLoopTM_valid sb (sb + 1)) hexit_lt
    (by rw [composeFlatTM_tapes]; exact Compile.copyEmptyRawTM_tapes sb src1)
    (Compile.compareLoopTM_tapes sb (sb + 1))

theorem Compile.cmpNGPrefixM_exit_lt (sb src1 src2 : Var) :
    Compile.cmpNGPrefixM_exit sb src1 src2 < (Compile.cmpNGPrefixM sb src1 src2).states := by
  rw [Compile.cmpNGPrefixM_exit, Compile.cmpNGPrefixM_states]
  have hcl : (Compile.compareLoopTM sb (sb + 1)).states = (Compile.compareBodyTM sb (sb + 1)).states + 1 := by
    rw [Compile.compareLoopTM, loopTM_states]
  omega

theorem Compile.cmpNGPrefixM_exit_is_halt (sb src1 src2 : Var) :
    (Compile.cmpNGPrefixM sb src1 src2).halt[Compile.cmpNGPrefixM_exit sb src1 src2]? = some true := by
  have h := Compile.composeFlatTM_halt_intro
    (composeFlatTM (Compile.copyEmptyRawTM sb src1) (Compile.copyEmptyRawTM (sb + 1) src2)
      (Compile.copyEmptyRawTM_exit sb src1))
    (Compile.compareLoopTM sb (sb + 1)) (Compile.compareBodyTM sb (sb + 1)).states
    ((Compile.copyEmptyRawTM sb src1).states + Compile.copyEmptyRawTM_exit (sb + 1) src2)
    (Compile.compareLoopTM_halt_getElem sb (sb + 1))
  rw [Compile.cmpNGPrefixM,
      show Compile.cmpNGPrefixM_exit sb src1 src2
        = (composeFlatTM (Compile.copyEmptyRawTM sb src1) (Compile.copyEmptyRawTM (sb + 1) src2)
                (Compile.copyEmptyRawTM_exit sb src1)).states
            + (Compile.compareBodyTM sb (sb + 1)).states from by
        rw [composeFlatTM_states, Compile.cmpNGPrefixM_exit]; omega]
  exact h

def Compile.cmpNGBranchM (sb : Var) : FlatTM :=
  branchComposeFlatTM (Compile.eqVerdictM sb (sb + 1)) (Compile.cmpNGCleanupM sb)
    (Compile.cmpNGCleanupM sb)
    (Compile.eqVerdictM_exit_eq sb (sb + 1)) (Compile.eqVerdictM_exit_neq sb)

theorem Compile.cmpNGBranchM_sig (sb : Var) : (Compile.cmpNGBranchM sb).sig = 4 := by
  rw [Compile.cmpNGBranchM, branchComposeFlatTM_sig, Compile.eqVerdictM_sig,
      Compile.cmpNGCleanupM_sig]; rfl

theorem Compile.cmpNGBranchM_tapes (sb : Var) : (Compile.cmpNGBranchM sb).tapes = 1 := by
  rw [Compile.cmpNGBranchM, branchComposeFlatTM_tapes]; exact Compile.eqVerdictM_tapes sb (sb + 1)

theorem Compile.cmpNGBranchM_start (sb : Var) : (Compile.cmpNGBranchM sb).start = 0 := by
  rw [Compile.cmpNGBranchM, branchComposeFlatTM_start]; exact Compile.eqVerdictM_start sb (sb + 1)

theorem Compile.cmpNGBranchM_states (sb : Var) :
    (Compile.cmpNGBranchM sb).states =
      (Compile.eqVerdictM sb (sb + 1)).states + (Compile.cmpNGCleanupM sb).states
        + (Compile.cmpNGCleanupM sb).states := by
  rw [Compile.cmpNGBranchM, branchComposeFlatTM_states]

theorem Compile.cmpNGBranchM_valid (sb : Var) : validFlatTM (Compile.cmpNGBranchM sb) :=
  branchComposeFlatTM_valid _ _ _ _ _
    (Compile.eqVerdictM_valid sb (sb + 1)) (Compile.cmpNGCleanupM_valid sb)
    (Compile.cmpNGCleanupM_valid sb)
    (Compile.eqVerdictM_exit_eq_lt sb (sb + 1)) (Compile.eqVerdictM_exit_neq_lt sb (sb + 1))
    (Compile.eqVerdictM_tapes sb (sb + 1)) (Compile.cmpNGCleanupM_tapes sb)
    (Compile.cmpNGCleanupM_tapes sb)

def Compile.compareRegsNoGrowM (sb src1 src2 : Var) : FlatTM :=
  composeFlatTM (Compile.cmpNGPrefixM sb src1 src2) (Compile.cmpNGBranchM sb)
    (Compile.cmpNGPrefixM_exit sb src1 src2)

def Compile.compareRegsNoGrowM_exit_eq (sb src1 src2 : Var) : Nat :=
  (Compile.cmpNGCleanupM_exit sb + (Compile.eqVerdictM sb (sb + 1)).states)
    + (Compile.cmpNGPrefixM sb src1 src2).states

def Compile.compareRegsNoGrowM_exit_neq (sb src1 src2 : Var) : Nat :=
  (Compile.cmpNGCleanupM_exit sb
      + ((Compile.eqVerdictM sb (sb + 1)).states + (Compile.cmpNGCleanupM sb).states))
    + (Compile.cmpNGPrefixM sb src1 src2).states

theorem Compile.compareRegsNoGrowM_sig (sb src1 src2 : Var) :
    (Compile.compareRegsNoGrowM sb src1 src2).sig = 4 := by
  rw [Compile.compareRegsNoGrowM, composeFlatTM_sig, Compile.cmpNGPrefixM_sig,
      Compile.cmpNGBranchM_sig]; rfl

theorem Compile.compareRegsNoGrowM_tapes (sb src1 src2 : Var) :
    (Compile.compareRegsNoGrowM sb src1 src2).tapes = 1 := by
  rw [Compile.compareRegsNoGrowM, composeFlatTM_tapes]
  exact Compile.cmpNGPrefixM_tapes sb src1 src2

theorem Compile.compareRegsNoGrowM_start (sb src1 src2 : Var) :
    (Compile.compareRegsNoGrowM sb src1 src2).start = 0 := by
  rw [Compile.compareRegsNoGrowM, composeFlatTM_start]
  exact Compile.cmpNGPrefixM_start sb src1 src2

theorem Compile.compareRegsNoGrowM_states (sb src1 src2 : Var) :
    (Compile.compareRegsNoGrowM sb src1 src2).states =
      (Compile.cmpNGPrefixM sb src1 src2).states + (Compile.cmpNGBranchM sb).states := by
  rw [Compile.compareRegsNoGrowM, composeFlatTM_states]

theorem Compile.compareRegsNoGrowM_valid (sb src1 src2 : Var) :
    validFlatTM (Compile.compareRegsNoGrowM sb src1 src2) := by
  rw [Compile.compareRegsNoGrowM]
  exact composeFlatTM_valid _ _ _ (Compile.cmpNGPrefixM_valid sb src1 src2)
    (Compile.cmpNGBranchM_valid sb) (Compile.cmpNGPrefixM_exit_lt sb src1 src2)
    (Compile.cmpNGPrefixM_tapes sb src1 src2) (Compile.cmpNGBranchM_tapes sb)

theorem Compile.compareRegsNoGrowM_exit_eq_lt (sb src1 src2 : Var) :
    Compile.compareRegsNoGrowM_exit_eq sb src1 src2 < (Compile.compareRegsNoGrowM sb src1 src2).states := by
  rw [Compile.compareRegsNoGrowM_exit_eq, Compile.compareRegsNoGrowM_states, Compile.cmpNGBranchM_states]
  have := Compile.cmpNGCleanupM_exit_lt sb
  omega

theorem Compile.compareRegsNoGrowM_exit_neq_lt (sb src1 src2 : Var) :
    Compile.compareRegsNoGrowM_exit_neq sb src1 src2 < (Compile.compareRegsNoGrowM sb src1 src2).states := by
  rw [Compile.compareRegsNoGrowM_exit_neq, Compile.compareRegsNoGrowM_states, Compile.cmpNGBranchM_states]
  have := Compile.cmpNGCleanupM_exit_lt sb
  omega

theorem Compile.compareRegsNoGrowM_exit_eq_ne_neq (sb src1 src2 : Var) :
    Compile.compareRegsNoGrowM_exit_eq sb src1 src2 ≠ Compile.compareRegsNoGrowM_exit_neq sb src1 src2 := by
  rw [Compile.compareRegsNoGrowM_exit_eq, Compile.compareRegsNoGrowM_exit_neq]
  have := Compile.cmpNGCleanupM_exit_lt sb
  omega

theorem Compile.compareRegsNoGrowM_exit_eq_is_halt (sb src1 src2 : Var) :
    (Compile.compareRegsNoGrowM sb src1 src2).halt[Compile.compareRegsNoGrowM_exit_eq sb src1 src2]? = some true := by
  have hbranch : (Compile.cmpNGBranchM sb).halt[(Compile.eqVerdictM sb (sb + 1)).states
        + Compile.cmpNGCleanupM_exit sb]? = some true := by
    rw [Compile.cmpNGBranchM]
    exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
      (Compile.cmpNGCleanupM_valid sb) (Compile.cmpNGCleanupM_exit_lt sb)
      (Compile.cmpNGCleanupM_halt_getElem sb)
  have hfull := Compile.composeFlatTM_halt_intro (Compile.cmpNGPrefixM sb src1 src2)
    (Compile.cmpNGBranchM sb)
    ((Compile.eqVerdictM sb (sb + 1)).states + Compile.cmpNGCleanupM_exit sb)
    (Compile.cmpNGPrefixM_exit sb src1 src2) hbranch
  rw [Compile.compareRegsNoGrowM,
      show Compile.compareRegsNoGrowM_exit_eq sb src1 src2
        = (Compile.cmpNGPrefixM sb src1 src2).states
            + ((Compile.eqVerdictM sb (sb + 1)).states + Compile.cmpNGCleanupM_exit sb) from by
        rw [Compile.compareRegsNoGrowM_exit_eq]; omega]
  exact hfull

theorem Compile.compareRegsNoGrowM_exit_neq_is_halt (sb src1 src2 : Var) :
    (Compile.compareRegsNoGrowM sb src1 src2).halt[Compile.compareRegsNoGrowM_exit_neq sb src1 src2]? = some true := by
  have hbranch : (Compile.cmpNGBranchM sb).halt[(Compile.eqVerdictM sb (sb + 1)).states
        + (Compile.cmpNGCleanupM sb).states + Compile.cmpNGCleanupM_exit sb]? = some true := by
    rw [Compile.cmpNGBranchM]
    exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
      (Compile.cmpNGCleanupM_valid sb) (Compile.cmpNGCleanupM_halt_getElem sb)
  have hfull := Compile.composeFlatTM_halt_intro (Compile.cmpNGPrefixM sb src1 src2)
    (Compile.cmpNGBranchM sb)
    ((Compile.eqVerdictM sb (sb + 1)).states + (Compile.cmpNGCleanupM sb).states
      + Compile.cmpNGCleanupM_exit sb)
    (Compile.cmpNGPrefixM_exit sb src1 src2) hbranch
  rw [Compile.compareRegsNoGrowM,
      show Compile.compareRegsNoGrowM_exit_neq sb src1 src2
        = (Compile.cmpNGPrefixM sb src1 src2).states
            + ((Compile.eqVerdictM sb (sb + 1)).states + (Compile.cmpNGCleanupM sb).states
                + Compile.cmpNGCleanupM_exit sb) from by
        rw [Compile.compareRegsNoGrowM_exit_neq]; omega]
  exact hfull

/-- `clearAppendM`'s start is head `0` (it begins by navigating to `dst`). -/
theorem Compile.clearAppendM_start (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    (Compile.clearAppendM dst ins h_ins).start = 0 := by
  rw [Compile.clearAppendM, composeFlatTM_start]; exact ClearGadget.clearRegionTM_start dst

/-- `clearAppendM`'s exit index is `< states`. -/
theorem Compile.clearAppendM_exit_lt (dst : Var) (ins : Nat) (h_ins : ins < 4) :
    Compile.clearAppendM_exit dst ins h_ins < (Compile.clearAppendM dst ins h_ins).states := by
  rw [Compile.clearAppendM_exit, Compile.clearAppendM, composeFlatTM_states]
  have := (Compile.opAppendBitRewind ins h_ins dst).exit_lt
  omega

/-- The raw (two-exit) `eqBit` machine: branch on `compareRegsNoGrowM`. -/
def Compile.eqBitNGRawM (sb dst src1 src2 : Var) : FlatTM :=
  branchComposeFlatTM (Compile.compareRegsNoGrowM sb src1 src2)
    (Compile.clearAppendM dst 2 (by decide))
    (Compile.clearAppendM dst 1 (by decide))
    (Compile.compareRegsNoGrowM_exit_eq sb src1 src2)
    (Compile.compareRegsNoGrowM_exit_neq sb src1 src2)

/-- EQ exit (positive branch). -/
def Compile.eqBitNGRawM_h1 (sb dst src1 src2 : Var) : Nat :=
  (Compile.compareRegsNoGrowM sb src1 src2).states + Compile.clearAppendM_exit dst 2 (by decide)

/-- NEQ exit (negative branch). -/
def Compile.eqBitNGRawM_h2 (sb dst src1 src2 : Var) : Nat :=
  (Compile.compareRegsNoGrowM sb src1 src2).states + (Compile.clearAppendM dst 2 (by decide)).states
    + Compile.clearAppendM_exit dst 1 (by decide)

theorem Compile.eqBitNGRawM_valid (sb dst src1 src2 : Var) :
    validFlatTM (Compile.eqBitNGRawM sb dst src1 src2) :=
  branchComposeFlatTM_valid _ _ _ _ _ (Compile.compareRegsNoGrowM_valid sb src1 src2)
    (Compile.clearAppendM_valid dst 2 (by decide))
    (Compile.clearAppendM_valid dst 1 (by decide))
    (Compile.compareRegsNoGrowM_exit_eq_lt sb src1 src2)
    (Compile.compareRegsNoGrowM_exit_neq_lt sb src1 src2)
    (Compile.compareRegsNoGrowM_tapes sb src1 src2)
    (Compile.clearAppendM_tapes dst 2 (by decide))
    (Compile.clearAppendM_tapes dst 1 (by decide))

theorem Compile.eqBitNGRawM_tapes (sb dst src1 src2 : Var) :
    (Compile.eqBitNGRawM sb dst src1 src2).tapes = 1 := by
  rw [Compile.eqBitNGRawM, branchComposeFlatTM_tapes]
  exact Compile.compareRegsNoGrowM_tapes sb src1 src2

theorem Compile.eqBitNGRawM_sig (sb dst src1 src2 : Var) :
    (Compile.eqBitNGRawM sb dst src1 src2).sig = 4 := by
  rw [Compile.eqBitNGRawM, branchComposeFlatTM_sig, Compile.compareRegsNoGrowM_sig,
      Compile.clearAppendM_sig, Compile.clearAppendM_sig, Nat.max_self, Nat.max_self]

theorem Compile.eqBitNGRawM_h1_ne_h2 (sb dst src1 src2 : Var) :
    Compile.eqBitNGRawM_h1 sb dst src1 src2 ≠ Compile.eqBitNGRawM_h2 sb dst src1 src2 := by
  rw [Compile.eqBitNGRawM_h1, Compile.eqBitNGRawM_h2]
  have hb2 := Compile.clearAppendM_exit_lt dst 2 (by decide)
  omega

theorem Compile.eqBitNGRawM_halt_only (sb dst src1 src2 : Var) :
    ∀ i, (Compile.eqBitNGRawM sb dst src1 src2).halt[i]? = some true →
      i = Compile.eqBitNGRawM_h1 sb dst src1 src2 ∨ i = Compile.eqBitNGRawM_h2 sb dst src1 src2 := by
  rw [Compile.eqBitNGRawM_h1, Compile.eqBitNGRawM_h2, Compile.eqBitNGRawM]
  exact Compile.branchComposeFlatTM_halt_only _ _ _ _ _ _ _
    (Compile.clearAppendM_valid dst 2 (by decide))
    (Compile.clearAppendM_valid dst 1 (by decide))
    (Compile.clearAppendM_halt_unique dst 2 (by decide))
    (Compile.clearAppendM_halt_unique dst 1 (by decide))

theorem Compile.eqBitNGRawM_h1_is_halt (sb dst src1 src2 : Var) :
    (Compile.eqBitNGRawM sb dst src1 src2).halt[Compile.eqBitNGRawM_h1 sb dst src1 src2]? = some true := by
  rw [Compile.eqBitNGRawM_h1, Compile.eqBitNGRawM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.clearAppendM_valid dst 2 (by decide))
    (Compile.clearAppendM_exit_lt dst 2 (by decide))
    (Compile.clearAppendM_exit_is_halt dst 2 (by decide))

theorem Compile.eqBitNGRawM_h1_lt (sb dst src1 src2 : Var) :
    Compile.eqBitNGRawM_h1 sb dst src1 src2 < (Compile.eqBitNGRawM sb dst src1 src2).states := by
  rw [Compile.eqBitNGRawM_h1, Compile.eqBitNGRawM, branchComposeFlatTM_states]
  have := Compile.clearAppendM_exit_lt dst 2 (by decide)
  omega

theorem Compile.eqBitNGRawM_h2_is_halt (sb dst src1 src2 : Var) :
    (Compile.eqBitNGRawM sb dst src1 src2).halt[Compile.eqBitNGRawM_h2 sb dst src1 src2]? = some true := by
  rw [Compile.eqBitNGRawM_h2, Compile.eqBitNGRawM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.clearAppendM_valid dst 2 (by decide))
    (Compile.clearAppendM_exit_is_halt dst 1 (by decide))

theorem Compile.eqBitNGRawM_h2_lt (sb dst src1 src2 : Var) :
    Compile.eqBitNGRawM_h2 sb dst src1 src2 < (Compile.eqBitNGRawM sb dst src1 src2).states := by
  rw [Compile.eqBitNGRawM_h2, Compile.eqBitNGRawM, branchComposeFlatTM_states]
  have := Compile.clearAppendM_exit_lt dst 1 (by decide)
  omega

/-- Compile `Op.eqBit dst src1 src2` (Resolution B): the `joinTwoHalts`-merged branch
machine. The eventual `opEqBit` (post def-reorg). -/
def Compile.opEqBitNG (sb dst src1 src2 : Var) : CompiledCmd where
  M := joinTwoHalts (Compile.eqBitNGRawM sb dst src1 src2)
        (Compile.eqBitNGRawM_h1 sb dst src1 src2) (Compile.eqBitNGRawM_h2 sb dst src1 src2)
  exit := Compile.eqBitNGRawM_h1 sb dst src1 src2
  exit_lt := by
    rw [joinTwoHalts_states]; exact Compile.eqBitNGRawM_h1_lt sb dst src1 src2
  exit_is_halt :=
    joinTwoHalts_h1_is_halt _ _ _ (Compile.eqBitNGRawM_h1_ne_h2 sb dst src1 src2)
      (Compile.eqBitNGRawM_h1_is_halt sb dst src1 src2)
  halt_unique :=
    joinTwoHalts_halt_unique _ _ _ (Compile.eqBitNGRawM_halt_only sb dst src1 src2)
  M_valid := joinTwoHalts_valid _ _ _ (Compile.eqBitNGRawM_valid sb dst src1 src2)
    (Compile.eqBitNGRawM_h1_lt sb dst src1 src2) (Compile.eqBitNGRawM_h2_lt sb dst src1 src2)
    (Compile.eqBitNGRawM_tapes sb dst src1 src2)
  M_tapes := by rw [joinTwoHalts_tapes]; exact Compile.eqBitNGRawM_tapes sb dst src1 src2
  M_sig := by rw [joinTwoHalts_sig]; exact Compile.eqBitNGRawM_sig sb dst src1 src2


/-- Compile `Op.eqBit dst src1 src2` at scratch base `sb` (Resolution B, no-grow).
Wired into `compileOp`; the behavioural contract is `opEqBitNG_run` (below). -/
def Compile.opEqBit (sb dst src1 src2 : Var) : CompiledCmd :=
  Compile.opEqBitNG sb dst src1 src2

