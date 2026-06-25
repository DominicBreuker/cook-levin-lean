import Complexity.Lang.Semantics
import Complexity.Lang.Frame
import Complexity.Lang.AppendGadget
import Complexity.Lang.ClearGadget
import Complexity.Complexity.TMPrimitives
import Complexity.Complexity.TapeMono

set_option autoImplicit false

/-! # `Compile/Core` — the `CompiledCmd` record and generic TM combinators

Extracted from `Compile.lean` (refactor Phase 1, see `REFACTOR-HANDOFF.md`).
This is the foundational layer the whole compiler builds on:

- `CompiledCmd` — a `FlatTM` + its designated exit state + validity bookkeeping.
- `Compile.joinTwoHalts` — merge two halt states into one (the `branchComposeFlatTM`
  halt-uniqueness fix).
- `Compile.rewindBracket` — wrap a `compute` machine with the two-phase head rewind
  to make a head-`0`-rewinding op a genuine single-exit `CompiledCmd`.

These are generic over arbitrary `FlatTM`s; the per-op machines, `compileOp`, the
soundness contracts, and the assembly all live downstream and import this module. -/

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators

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

/-- `joinTwoHalts` re-keys only transitions out of `h2`: at any state `≠ h2` the
step function is unchanged. The prepended `bridgeEntries` all have source `h2`,
so `find?` skips them and falls through to `M.trans`. -/
theorem joinTwoHalts_step_eq (M : FlatTM) (h1 h2 : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ h2) :
    stepFlatTM (joinTwoHalts M h1 h2) cfg = stepFlatTM M cfg := by
  have hnone : (bridgeEntries M.sig h2 h1).find?
      (fun entry => entryMatchesConfig entry cfg) = none := by
    rw [List.find?_eq_none]
    intro e he
    have hsrc : e.src_state = h2 := (bridgeEntries_mem he).1
    simp only [entryMatchesConfig, Bool.not_eq_true, Bool.and_eq_false_imp]
    intro hbeq
    rw [hsrc, beq_iff_eq] at hbeq
    exact absurd hbeq.symm h
  show ((bridgeEntries M.sig h2 h1 ++ M.trans).find?
      (fun entry => entryMatchesConfig entry cfg)).bind (applyTransitionEntry cfg)
    = (M.trans.find? (fun entry => entryMatchesConfig entry cfg)).bind (applyTransitionEntry cfg)
  rw [List.find?_append, hnone]
  rfl

/-- `joinTwoHalts` flips only `h2`'s halt bit: `haltingStateReached` is unchanged
at any state `≠ h2`. -/
theorem joinTwoHalts_halting_eq (M : FlatTM) (h1 h2 : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ h2) :
    haltingStateReached (joinTwoHalts M h1 h2) cfg = haltingStateReached M cfg := by
  show (M.halt.set h2 false).getD cfg.state_idx false = M.halt.getD cfg.state_idx false
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (fun heq => h heq.symm)]

/-- **Run-preservation under `joinTwoHalts` (the foundational unblock).** If the
`M`-run from `cfg0` never visits the demoted state `h2` within `t` steps, the
joined machine produces the identical run. This is what lets a gadget whose only
extra halt state (`h2`, e.g. a left-scan's unreachable "boundary" state) is
demoted inherit the gadget's proven run/trajectory. The "never visits `h2`"
premise is discharged from a no-early-halt trajectory when `h2` is a halt state
of `M`: a run that never halts before `t` never sits on any halt state. -/
theorem joinTwoHalts_run_eq (M : FlatTM) (h1 h2 : Nat) :
    ∀ (t : Nat) (cfg0 : FlatTMConfig),
      (∀ k, k ≤ t → ∀ ck, runFlatTM k M cfg0 = some ck → ck.state_idx ≠ h2) →
      runFlatTM t (joinTwoHalts M h1 h2) cfg0 = runFlatTM t M cfg0 := by
  intro t
  induction t with
  | zero => intro cfg0 _; rfl
  | succ n ih =>
      intro cfg0 hstate
      have h0 : cfg0.state_idx ≠ h2 := hstate 0 (Nat.zero_le _) cfg0 rfl
      have hhaltj : haltingStateReached (joinTwoHalts M h1 h2) cfg0 = haltingStateReached M cfg0 :=
        joinTwoHalts_halting_eq M h1 h2 cfg0 h0
      have hstepj : stepFlatTM (joinTwoHalts M h1 h2) cfg0 = stepFlatTM M cfg0 :=
        joinTwoHalts_step_eq M h1 h2 cfg0 h0
      by_cases hhalt : haltingStateReached M cfg0 = true
      · rw [runFlatTM_of_halting (joinTwoHalts M h1 h2) cfg0 (n + 1) (by rw [hhaltj]; exact hhalt),
            runFlatTM_of_halting M cfg0 (n + 1) hhalt]
      · cases hstep : stepFlatTM M cfg0 with
        | none =>
            rw [runFlatTM_stuck (joinTwoHalts M h1 h2) cfg0
                  (by rw [hhaltj]; exact Bool.not_eq_true _ ▸ hhalt) (by rw [hstepj]; exact hstep),
                runFlatTM_stuck M cfg0 (Bool.not_eq_true _ ▸ hhalt) hstep]
        | some cfg' =>
            -- unfold one step on both machines (not halting, step = some cfg')
            have hL : runFlatTM (n + 1) (joinTwoHalts M h1 h2) cfg0
                = runFlatTM n (joinTwoHalts M h1 h2) cfg' := by
              show (if haltingStateReached (joinTwoHalts M h1 h2) cfg0 = true then some cfg0
                    else match stepFlatTM (joinTwoHalts M h1 h2) cfg0 with
                      | none => some cfg0
                      | some c => runFlatTM n (joinTwoHalts M h1 h2) c) = _
              rw [if_neg (by rw [hhaltj]; exact hhalt), hstepj, hstep]
            have hunfold : ∀ k, runFlatTM (k + 1) M cfg0 = runFlatTM k M cfg' := by
              intro k
              show (if haltingStateReached M cfg0 = true then some cfg0
                    else match stepFlatTM M cfg0 with
                      | none => some cfg0
                      | some c => runFlatTM k M c) = _
              rw [if_neg hhalt, hstep]
            rw [hL, hunfold n]
            exact ih cfg' (fun k hk ck hck =>
              hstate (k + 1) (Nat.succ_le_succ hk) ck (by rw [hunfold k]; exact hck))

/-- **Weak run-preservation.** If the raw run never visits the demoted state `h2`
*strictly before* step `t`, then `joinTwoHalts` agrees with `M` at step `t`.
Unlike `joinTwoHalts_run_eq` this allows the step-`t` config itself to be `h2`
(the divergence only happens when stepping *out of* `h2`). Used for the branch
that reaches the demoted exit, which then bridges to the kept exit in one step. -/
theorem joinTwoHalts_run_eq_weak (M : FlatTM) (h1 h2 : Nat) :
    ∀ (t : Nat) (cfg0 : FlatTMConfig),
      (∀ k, k < t → ∀ ck, runFlatTM k M cfg0 = some ck → ck.state_idx ≠ h2) →
      runFlatTM t (joinTwoHalts M h1 h2) cfg0 = runFlatTM t M cfg0 := by
  intro t
  induction t with
  | zero => intro cfg0 _; rfl
  | succ n ih =>
      intro cfg0 hstate
      have h0 : cfg0.state_idx ≠ h2 := hstate 0 (Nat.succ_pos n) cfg0 rfl
      have hhaltj : haltingStateReached (joinTwoHalts M h1 h2) cfg0 = haltingStateReached M cfg0 :=
        joinTwoHalts_halting_eq M h1 h2 cfg0 h0
      have hstepj : stepFlatTM (joinTwoHalts M h1 h2) cfg0 = stepFlatTM M cfg0 :=
        joinTwoHalts_step_eq M h1 h2 cfg0 h0
      by_cases hhalt : haltingStateReached M cfg0 = true
      · rw [runFlatTM_of_halting (joinTwoHalts M h1 h2) cfg0 (n + 1) (by rw [hhaltj]; exact hhalt),
            runFlatTM_of_halting M cfg0 (n + 1) hhalt]
      · cases hstep : stepFlatTM M cfg0 with
        | none =>
            rw [runFlatTM_stuck (joinTwoHalts M h1 h2) cfg0
                  (by rw [hhaltj]; exact Bool.not_eq_true _ ▸ hhalt) (by rw [hstepj]; exact hstep),
                runFlatTM_stuck M cfg0 (Bool.not_eq_true _ ▸ hhalt) hstep]
        | some cfg' =>
            have hL : runFlatTM (n + 1) (joinTwoHalts M h1 h2) cfg0
                = runFlatTM n (joinTwoHalts M h1 h2) cfg' := by
              show (if haltingStateReached (joinTwoHalts M h1 h2) cfg0 = true then some cfg0
                    else match stepFlatTM (joinTwoHalts M h1 h2) cfg0 with
                      | none => some cfg0
                      | some c => runFlatTM n (joinTwoHalts M h1 h2) c) = _
              rw [if_neg (by rw [hhaltj]; exact hhalt), hstepj, hstep]
            have hunfold : ∀ k, runFlatTM (k + 1) M cfg0 = runFlatTM k M cfg' := by
              intro k
              show (if haltingStateReached M cfg0 = true then some cfg0
                    else match stepFlatTM M cfg0 with
                      | none => some cfg0
                      | some c => runFlatTM k M c) = _
              rw [if_neg hhalt, hstep]
            rw [hL, hunfold n]
            exact ih cfg' (fun k hk ck hck =>
              hstate (k + 1) (Nat.succ_lt_succ hk) ck (by rw [hunfold k]; exact hck))

/-- **`joinTwoHalts` bridge step.** From the demoted state `h2` (single tape, head
symbol in range), one step jumps to the kept exit `h1` leaving the tape
unchanged. The prepended `bridgeEntries h2 h1` fire. -/
theorem joinTwoHalts_step_to_h1 (M : FlatTM) (h1 h2 : Nat)
    (left right : List Nat) (head : Nat)
    (h_sym : ∀ v, currentTapeSymbol (left, head, right) = some v → v < M.sig) :
    stepFlatTM (joinTwoHalts M h1 h2) { state_idx := h2, tapes := [(left, head, right)] }
      = some { state_idx := h1, tapes := [(left, head, right)] } :=
  stepFlatTM_bridge_prefix (joinTwoHalts M h1 h2) h2 h1 M.trans rfl left right head h_sym

/-! ### General rewinding-op `CompiledCmd` builder (`rewindBracket`)

Every rewinding op (the append ops, and every deletion op
`navigate ⨾ shift ⨾ rewind`) has the same shape: a "compute" machine followed by
the two-phase rewind. That composite has **two** halt states (the left scan's
found-state `compute.states + 6` and its unreachable boundary-state
`compute.states + 7`), which violates `CompiledCmd.halt_unique`. `rewindBracket`
packages the fix once: demote the boundary state via `joinTwoHalts`, leaving the
found-state as the unique exit. Its transport lemma turns the gadget's proven
run/trajectory into the `CompiledCmd`'s. Deletion ops reuse both verbatim by
supplying their own `compute` machine. -/

/-- The two-phase rewind composite (`compute ⨾ rewindTwoPhase`) has exactly two
halt states: the found-state `compute.states + 6` and the boundary-state
`compute.states + 7`. -/
theorem rewindComposite_halt_only (compute : FlatTM) (exit i : Nat)
    (hi : (composeFlatTM compute (ScanLeft.rewindTwoPhaseTM 4 3) exit).halt[i]? = some true) :
    i = compute.states + 6 ∨ i = compute.states + 7 := by
  obtain ⟨hge, hj⟩ :=
    ScanLeft.composeFlatTM_halt_some_imp compute (ScanLeft.rewindTwoPhaseTM 4 3) exit i hi
  rcases ScanLeft.rewindTwoPhaseTM_halt_only 4 3 _ hj with h | h <;> omega

/-- Build a rewinding op as a `CompiledCmd` from its `compute` machine: compose
with the two-phase rewind, then demote the boundary halt. The found-state
`compute.states + 6` is the unique exit. -/
def rewindBracket (compute : FlatTM) (exit : Nat)
    (h_valid : validFlatTM compute) (h_exit : exit < compute.states)
    (h_tapes : compute.tapes = 1) (h_sig : compute.sig = 4) : CompiledCmd where
  M := joinTwoHalts (composeFlatTM compute (ScanLeft.rewindTwoPhaseTM 4 3) exit)
        (compute.states + 6) (compute.states + 7)
  exit := compute.states + 6
  exit_lt := by
    rw [joinTwoHalts_states, composeFlatTM_states]
    have : (ScanLeft.rewindTwoPhaseTM 4 3).states = 8 := rfl
    omega
  exit_is_halt :=
    joinTwoHalts_h1_is_halt _ _ _ (by omega)
      (ScanLeft.composeFlatTM_halt_some_intro compute (ScanLeft.rewindTwoPhaseTM 4 3) exit 6
        (ScanLeft.rewindTwoPhaseTM_halt_six 4 3))
  halt_unique := joinTwoHalts_halt_unique _ _ _ (rewindComposite_halt_only compute exit)
  M_valid :=
    joinTwoHalts_valid _ _ _
      (composeFlatTM_valid compute (ScanLeft.rewindTwoPhaseTM 4 3) exit h_valid
        (ScanLeft.rewindTwoPhaseTM_valid 4 3 (by decide)) h_exit h_tapes
        (ScanLeft.rewindTwoPhaseTM_tapes 4 3))
      (by rw [composeFlatTM_states]
          have : (ScanLeft.rewindTwoPhaseTM 4 3).states = 8 := rfl
          omega)
      (by rw [composeFlatTM_states]
          have : (ScanLeft.rewindTwoPhaseTM 4 3).states = 8 := rfl
          omega)
      (by rw [composeFlatTM_tapes]; exact h_tapes)
  M_tapes := by rw [joinTwoHalts_tapes, composeFlatTM_tapes]; exact h_tapes
  M_sig := by rw [joinTwoHalts_sig, composeFlatTM_sig, h_sig, ScanLeft.rewindTwoPhaseTM_sig]; rfl

theorem rewindBracket_M (compute : FlatTM) (exit : Nat)
    (h_valid : validFlatTM compute) (h_exit : exit < compute.states)
    (h_tapes : compute.tapes = 1) (h_sig : compute.sig = 4) :
    (rewindBracket compute exit h_valid h_exit h_tapes h_sig).M
      = joinTwoHalts (composeFlatTM compute (ScanLeft.rewindTwoPhaseTM 4 3) exit)
          (compute.states + 6) (compute.states + 7) := rfl

theorem rewindBracket_exit (compute : FlatTM) (exit : Nat)
    (h_valid : validFlatTM compute) (h_exit : exit < compute.states)
    (h_tapes : compute.tapes = 1) (h_sig : compute.sig = 4) :
    (rewindBracket compute exit h_valid h_exit h_tapes h_sig).exit = compute.states + 6 := rfl

/-- **Run/trajectory transport for `rewindBracket` (the mechanism, reusable for
every rewinding op).** Given the raw composite's run to its found-state
`compute.states + 6` and its no-early-halt trajectory, the `joinTwoHalts`-wrapped
`CompiledCmd` produces the same run to its `exit`, plus its no-early-exit/
no-early-halt trajectory. Proof via `joinTwoHalts_run_eq`: the raw run never
visits the demoted boundary `+7` (a halt state, forbidden before `t` by
no-early-halt; the run ends at `+6` at `t`). -/
theorem rewindBracket_transport (compute : FlatTM) (exit : Nat)
    (h_valid : validFlatTM compute) (h_exit : exit < compute.states)
    (h_tapes : compute.tapes = 1) (h_sig : compute.sig = 4)
    {t : Nat} {cfg0 : FlatTMConfig} {tapeOut : List Nat × Nat × List Nat}
    (hrun : runFlatTM t (composeFlatTM compute (ScanLeft.rewindTwoPhaseTM 4 3) exit) cfg0
        = some { state_idx := compute.states + 6, tapes := [tapeOut] })
    (htraj : ∀ k, k < t → ∀ ck,
        runFlatTM k (composeFlatTM compute (ScanLeft.rewindTwoPhaseTM 4 3) exit) cfg0 = some ck →
        haltingStateReached (composeFlatTM compute (ScanLeft.rewindTwoPhaseTM 4 3) exit) ck = false) :
    runFlatTM t (rewindBracket compute exit h_valid h_exit h_tapes h_sig).M cfg0
        = some { state_idx := (rewindBracket compute exit h_valid h_exit h_tapes h_sig).exit,
                 tapes := [tapeOut] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (rewindBracket compute exit h_valid h_exit h_tapes h_sig).M cfg0 = some ck →
        ck.state_idx ≠ (rewindBracket compute exit h_valid h_exit h_tapes h_sig).exit ∧
        haltingStateReached (rewindBracket compute exit h_valid h_exit h_tapes h_sig).M ck
          = false) := by
  set raw : FlatTM := composeFlatTM compute (ScanLeft.rewindTwoPhaseTM 4 3) exit with hraw
  set h1 : Nat := compute.states + 6 with hh1
  set h2 : Nat := compute.states + 7 with hh2
  rw [rewindBracket_M, rewindBracket_exit]
  have hhalt_h1 : raw.halt[h1]? = some true := by
    rw [hraw, hh1]
    exact ScanLeft.composeFlatTM_halt_some_intro compute (ScanLeft.rewindTwoPhaseTM 4 3) exit 6
      (ScanLeft.rewindTwoPhaseTM_halt_six 4 3)
  have hhalt_h2 : raw.halt[h2]? = some true := by
    rw [hraw, hh2]
    exact ScanLeft.composeFlatTM_halt_some_intro compute (ScanLeft.rewindTwoPhaseTM 4 3) exit 7
      (ScanLeft.rewindTwoPhaseTM_halt_seven 4 3)
  have hhalt_imp : ∀ (ck : FlatTMConfig), raw.halt[ck.state_idx]? = some true →
      haltingStateReached raw ck = true := by
    intro ck hx
    show raw.halt.getD ck.state_idx false = true
    rw [List.getD_eq_getElem?_getD, hx]; rfl
  have hnv : ∀ k, k ≤ t → ∀ ck, runFlatTM k raw cfg0 = some ck → ck.state_idx ≠ h2 := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · intro hcontra
      have hnh : haltingStateReached raw ck = false := htraj k hlt ck hck
      rw [hhalt_imp ck (by rw [hcontra]; exact hhalt_h2)] at hnh
      exact Bool.noConfusion hnh
    · have hck2 : ck = { state_idx := h1, tapes := [tapeOut] } :=
        Option.some.inj (hck.symm.trans hrun)
      rw [hck2]; show h1 ≠ h2; omega
  refine ⟨?_, ?_⟩
  · rw [joinTwoHalts_run_eq raw h1 h2 t cfg0 hnv, hrun]
  · intro k hk ck hck
    rw [joinTwoHalts_run_eq raw h1 h2 k cfg0
          (fun j hj => hnv j (Nat.le_trans hj (Nat.le_of_lt hk)))] at hck
    have hnh : haltingStateReached raw ck = false := htraj k hk ck hck
    have hne_h2 : ck.state_idx ≠ h2 := hnv k (Nat.le_of_lt hk) ck hck
    refine ⟨fun hcontra => ?_, ?_⟩
    · rw [hhalt_imp ck (by rw [hcontra]; exact hhalt_h1)] at hnh
      exact Bool.noConfusion hnh
    · rw [joinTwoHalts_halting_eq raw h1 h2 ck hne_h2]; exact hnh

end Compile
