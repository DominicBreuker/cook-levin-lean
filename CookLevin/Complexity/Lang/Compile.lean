import Complexity.Lang.Semantics
import Complexity.Lang.Frame
import Complexity.Lang.AppendGadget
import Complexity.Lang.ClearGadget
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
private def Compile.markBitEntry (b : Nat) : FlatTMTransEntry :=
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
private def Compile.restoreStepEntry (b : Nat) : FlatTMTransEntry :=
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
private def Compile.skipReadDelimEntry : FlatTMTransEntry :=
  { src_state := 0, src_tape_vals := [some 0], dst_state := 1,
    dst_write_vals := [none], move_dirs := [TMMove.Nmove] }

/-- `skipReadTM` entry: content cell `v ∈ {1,2}` → step right, exit `2`. -/
private def Compile.skipReadBitEntry (v : Nat) : FlatTMTransEntry :=
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
    (by rw [Compile.copyPipeA2TM_states]; omega) Compile.copyRet1TM_tapes rfl

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
    (by rw [Compile.copyPipeA3TM_states]; omega) Compile.copyRet1TM_tapes rfl

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
    (by rw [Compile.copyPipeA4TM_states]; omega) Compile.copyRet1TM_tapes rfl

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
    (by rw [Compile.copyPipeA5TM_states]; omega) Compile.copyRet1TM_tapes rfl

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

/-- Compile `Op.tail dst src`. **Stub for now** — the machines are probe-validated
(`probes/CursorCopyProbe.lean`: `tailInPlaceTM` = one clear-style delete via
`clearBodyRawTM` with joined exits for `dst = src`; `skipReadTM ⨾ copyLoopTM` for
`dst ≠ src`); wiring them as a `CompiledCmd` follows the `opCopy` pattern. -/
def Compile.opTail (_dst _src : Var) : CompiledCmd := compiledCmd_default

/-- Compile `Op.eqBit dst src1 src2`. **Stub.** -/
def Compile.opEqBit (_dst _src1 _src2 : Var) : CompiledCmd := compiledCmd_default

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
private def Compile.bitReadBit0Entry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some 1]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

/-- Test entry for content bit `1` (cell value `2`): stay, halt at state 2. -/
private def Compile.bitReadBit1Entry : FlatTMTransEntry :=
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
def compileForBnd (_counter _bound : Var) (_sb : Nat) (_rbody : CompiledCmd) :
    CompiledCmd := compiledCmd_default

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
  | _,  .op o                 => compileOp o
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

/-- **Encoded-tape length balance for a register write (cross-register op
bookkeeping).** Writing `v` to an in-range register `dst` changes the encoded
tape length by `|v| − |old dst|`, stated in balance form to avoid ℕ subtraction:
`|encodeTape (s.set dst v)| + |old dst| = |encodeTape s| + |v|`.

Every cross-register op `dst := f (s.get src)` needs exactly this to express its
residue length (`res_out`) and bound its budget: a `set` in range preserves the
register count (`s.length`), so only the contents term moves — by
`State.size_set_add`. (Length-growing writes — `v` longer than the old register
— extend the tape; length-shrinking writes leave the freed cells as `0` residue,
which is why the deletion-op residue is `res_in ++ replicate (|old| − |v|) 0`.) -/
theorem Compile.encodeTape_set_length (s : State) (dst : Var) (v : List Nat)
    (h : dst < s.length) :
    (Compile.encodeTape (s.set dst v)).length + (s.get dst).length
      = (Compile.encodeTape s).length + v.length := by
  have hlen : (s.set dst v).length = s.length := by
    simp only [State.set, if_pos h, List.length_set]
  rw [Compile.encodeTape_length, Compile.encodeTape_length, hlen]
  have hbal := State.size_set_add s dst v
  omega

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

/-! ### (The old `Compile.overhead`/exact-tape lemma family is DELETED.)

The original decode-level obligations (`compileOp_sound`, `compileSeq_sound`,
`compileIfBit_sound`, `compileForBnd_sound`, `Compile_sound`, `Compile_polyBound`)
and the exact-tape physical family (`compileOp_sound_physical`,
`compileIfBit_sound_physical`, `compileForBnd_sound_physical`,
`Compile_run_physical`), together with their budget `Compile.overhead (m+1)²`,
were all **superseded by the residue-tolerant `physStepBudget` route**
(`Compile_run_physical_residue` + `paddedBitDecider_run`/`paddedCompute_run`) and
deleted 2026-06-11: the exact-tape contract is unsatisfiable for
length-decreasing ops (`clear_physical_unsatisfiable`) and the `overhead`
budget shape does not compose (ROADMAP Finding #3). Do not re-introduce. -/

/-! ### Encoding-seam helpers for the per-op soundness lemmas

The helpers below
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

/-- **Master register-slot decomposition.** The encoded tape splits at register
`dst` into a prefix `pre`, that register's shifted content, its `0` delimiter, and
a suffix `rest` — and **`pre`/`rest` do not depend on the register's content**, so
writing any value `v` to register `dst` only swaps the middle block:
`encodeTape (s.set dst v) = pre ++ shiftReg v ++ 0 :: rest` for every `v`.
(`pre = endMark :: encodeRegs (s.take dst)`, `rest = encodeRegs (s.drop (dst+1)) ++
[endMark]`.) This is the workhorse every register-writing op uses: with `v = s.get
dst` it gives `encodeTape s` itself (`set` is the identity there), and varying `v`
gives the op's output tape with the same surrounding cells — so a gadget that edits
only the middle block discharges its `encodeTape`-level contract. -/
theorem Compile.encodeTape_reg_decomp (s : State) (dst : Var) (h : dst < s.length) :
    ∃ pre rest : List Nat,
      (∀ v : List Nat,
        Compile.encodeTape (s.set dst v) = pre ++ (Compile.shiftReg v ++ (0 :: rest))) ∧
      Compile.encodeTape s = pre ++ (Compile.shiftReg (s.get dst) ++ (0 :: rest)) := by
  refine ⟨Compile.endMark :: Compile.encodeRegs (s.take dst),
          Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark], ?_, ?_⟩
  · intro v
    have hset : s.set dst v = s.take dst ++ v :: s.drop (dst + 1) := by
      rw [State.set, if_pos h]; exact Compile.list_set_eq_take_cons_drop s dst v h
    have hs : Compile.encodeRegs (s.set dst v)
        = Compile.encodeRegs (s.take dst)
            ++ (Compile.shiftReg v ++ ([0] ++ Compile.encodeRegs (s.drop (dst + 1)))) := by
      rw [hset, Compile.encodeRegs_append, Compile.encodeRegs_cons]
      simp [List.append_assoc]
    rw [Compile.encodeTape, hs]
    simp [List.append_assoc]
  · have hget : s.get dst = s[dst] := by
      rw [State.get, List.getElem?_eq_getElem h]; rfl
    have hs : Compile.encodeRegs s
        = Compile.encodeRegs (s.take dst)
            ++ (Compile.shiftReg (s.get dst)
                ++ ([0] ++ Compile.encodeRegs (s.drop (dst + 1)))) := by
      conv_lhs => rw [Compile.list_eq_take_getElem_drop s dst h]
      rw [Compile.encodeRegs_append, Compile.encodeRegs_cons, ← hget]
      simp [List.append_assoc]
    rw [Compile.encodeTape, hs]
    simp [List.append_assoc]

/-- **Spec bridge for `clear` (the deletion gadget's input/output contract).**
Specialises `encodeTape_reg_decomp`: clearing register `dst` removes exactly the
contiguous `shiftReg (s.get dst)` block before that register's `0` delimiter. With
any incoming residue `res_in`:

1. the gadget's **input** tape `encodeTape s ++ res_in` is
   `pre ++ shiftReg (s.get dst) ++ (0 :: rest ++ res_in)` — block to delete is
   `shiftReg (s.get dst)`, of length `|s.get dst|` (conjunct 3); and
2. after deleting those `|s.get dst|` cells (each `deleteCarryTM` pushes one `0`
   filler to the far end), the tape is
   `encodeTape (Op.eval (clear dst) s) ++ (res_in ++ replicate |s.get dst| 0)`.

So `res_out = res_in ++ replicate |old| 0` (`ValidResidue` by
`ValidResidue_append_replicate_zero`); the freed cells become terminator-free `0`
residue past the real terminator, so the **two-phase rewind** applies. -/
theorem Compile.clear_block_decomp (s : State) (dst : Var) (res_in : List Nat)
    (h : dst < s.length) :
    ∃ pre rest : List Nat,
      Compile.encodeTape s ++ res_in
          = pre ++ (Compile.shiftReg (s.get dst) ++ (0 :: rest ++ res_in)) ∧
      pre ++ ((0 :: rest ++ res_in) ++ List.replicate (s.get dst).length 0)
          = Compile.encodeTape (Op.eval (Op.clear dst) s)
              ++ (res_in ++ List.replicate (s.get dst).length 0) ∧
      (Compile.shiftReg (s.get dst)).length = (s.get dst).length := by
  obtain ⟨pre, rest, hv, hs⟩ := Compile.encodeTape_reg_decomp s dst h
  refine ⟨pre, rest, ?_, ?_, ?_⟩
  · rw [hs]; simp [List.append_assoc]
  · -- `Op.eval (clear dst) s = s.set dst []`, and `shiftReg [] = []`.
    have hcl : Compile.encodeTape (Op.eval (Op.clear dst) s) = pre ++ (0 :: rest) := by
      show Compile.encodeTape (s.set dst []) = _
      rw [hv []]; simp [Compile.shiftReg]
    rw [hcl]; simp [List.append_assoc]
  · rw [Compile.shiftReg, List.length_map]

/-- **One `deleteCarryTM` pass deletes the head of a marker-free block.** From the
read state at head `pre.length + 1` on `pre ++ (c0+1) :: M` (a nonempty,
in-range `M`), after `3·|M| + 1` steps the machine halts having deleted the cell
`c0+1` and shifted `M` left by one with a `0` filler: tape `pre ++ M ++ [0]`. The
degenerate-suffix branch of `deleteCarryTM_loop_run` is ruled out by `M ≠ []`. -/
theorem Compile.deleteCarry_drop_head (pre M : List Nat) (c0 : Nat)
    (hc0 : c0 + 1 < 4) (hM : M ≠ []) (hMb : ∀ x ∈ M, x < 4) :
    runFlatTM (3 * M.length + 1) Complexity.Lang.ShiftTape.deleteCarryTM
        { state_idx := 0, tapes := [([], pre.length + 1, pre ++ (c0 + 1) :: M)] }
      = some { state_idx := 6,
               tapes := [([], pre.length + 1 + M.length, pre ++ M ++ [0])] } := by
  have h := Complexity.Lang.ShiftTape.deleteCarryTM_loop_run M pre (c0 + 1) hc0 hMb
  rw [if_neg hM, ← List.append_assoc] at h
  exact h

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

/-- The **trailing terminator**: the last cell of `encodeTape t` is the `endMark`
`3`. This pins the real-terminator position for the residue-tolerant two-phase
rewind (`p = (encodeTape output).length - 1`). -/
theorem Compile.encodeTape_get_last (t : State)
    (h : (Compile.encodeTape t).length - 1 < (Compile.encodeTape t).length) :
    (Compile.encodeTape t).get ⟨(Compile.encodeTape t).length - 1, h⟩ = 3 := by
  rw [List.get_eq_getElem]
  -- Work at the proof-free `getElem?` level to avoid a dependent-index rewrite.
  have key : (Compile.encodeTape t)[(Compile.encodeTape t).length - 1]? = some 3 := by
    rw [Compile.encodeTape]
    rw [show (Compile.endMark :: (Compile.encodeRegs t ++ [Compile.endMark])).length - 1
          = (Compile.encodeRegs t).length + 1 by
        simp only [List.length_cons, List.length_append, List.length_nil]; omega]
    rw [List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _)]
    simp [Compile.endMark]
  exact (Option.some.inj (key.symm.trans (List.getElem?_eq_getElem h))).symm

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

-- (The old `compileOp_appendOne_sound`/`_appendZero_sound` asserted the *exact-tape*,
-- non-rewinding contract about the bare `appendAtTM`. Since `compileOp` now dispatches
-- the append ops to the head-rewinding `opAppendBitRewind`, the live per-op contract is
-- the residue-tolerant `compileOp_sound_physical_residue` (append cases discharged by
-- `Compile.opAppendBit_physical_residue`). The single-phase `appendBit_sound` /
-- `appendBit_physical` remain as gadget-level lemmas about `appendAtTM`/`appendAtThenRewindTM`.)

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

/-- A residue block carries only **interior** symbols `{0, 1, 2}`: below the
alphabet bound (`< 4`) and free of the terminator `endMark = 3`. The left-shift
delete gadgets fill vacated cells with `0`; append carries interior symbols; so
the trailing residue on every physical tape stays `ValidResidue`. This is exactly
what the composition lemmas need to bound the inter-fragment tape symbols. -/
def Compile.ValidResidue (res : List Nat) : Prop :=
  ∀ x ∈ res, x < 4 ∧ x ≠ Compile.endMark

theorem Compile.ValidResidue_nil : Compile.ValidResidue [] := by
  intro x hx; simp at hx

theorem Compile.ValidResidue_append (a b : List Nat)
    (ha : Compile.ValidResidue a) (hb : Compile.ValidResidue b) :
    Compile.ValidResidue (a ++ b) := by
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with h | h
  · exact ha x h
  · exact hb x h

theorem Compile.ValidResidue_replicate_zero (n : Nat) :
    Compile.ValidResidue (List.replicate n 0) := by
  intro x hx
  rw [List.mem_replicate] at hx
  obtain ⟨_, rfl⟩ := hx
  exact ⟨by omega, by decide⟩

/-- The residue a length-decreasing op produces: the incoming residue with `n`
zero filler cells appended (the cells freed by a left-shift `deleteCarryTM`).
Stays `ValidResidue` — the convenience form of `ValidResidue_append` +
`ValidResidue_replicate_zero` that every deletion / shrinking-write op's residue
contract (`res_out = res_in ++ replicate n 0`) discharges with. -/
theorem Compile.ValidResidue_append_replicate_zero (res : List Nat) (n : Nat)
    (hres : Compile.ValidResidue res) :
    Compile.ValidResidue (res ++ List.replicate n 0) :=
  Compile.ValidResidue_append res _ hres (Compile.ValidResidue_replicate_zero n)

/-- **One deletion = the in-place `tail` step (the loop's inductive heart).**
Running `deleteCarryTM` from one past register `dst`'s content-start on
`encodeTape s ++ res` (register `dst` nonempty) deletes that register's first
content cell, yielding `encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0])`:
it drops one symbol from register `dst`, the incoming residue gaining one `0`
filler. Iterating this `|s.get dst|` times clears the register (the clear gadget's
loop body); a single application is the `tail`-in-place op. The content-start
position `p` and the shifted-suffix length `L` are existential (the caller's
navigation supplies the head position). Built from `deleteCarry_drop_head` +
`encodeTape_reg_decomp`. -/
theorem Compile.deleteCarry_tail_step (s : State) (dst : Var) (res : List Nat)
    (h : dst < s.length) (hbit : Compile.BitState s) (hne : s.get dst ≠ [])
    (hres : Compile.ValidResidue res) :
    ∃ p L : Nat,
      runFlatTM (3 * L + 1) Complexity.Lang.ShiftTape.deleteCarryTM
          { state_idx := 0, tapes := [([], p + 1, Compile.encodeTape s ++ res)] }
        = some { state_idx := 6,
                 tapes := [([], p + 1 + L,
                   Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))] } := by
  obtain ⟨pre, rest, hv, hs⟩ := Compile.encodeTape_reg_decomp s dst h
  obtain ⟨c0, cs, hcons⟩ : ∃ c0 cs, s.get dst = c0 :: cs := by
    cases hg : s.get dst with
    | nil => exact absurd hg hne
    | cons c0 cs => exact ⟨c0, cs, rfl⟩
  have hshift : Compile.shiftReg (c0 :: cs) = (c0 + 1) :: Compile.shiftReg cs := by
    simp [Compile.shiftReg]
  set M : List Nat := Compile.shiftReg cs ++ 0 :: rest ++ res with hMdef
  have htape : Compile.encodeTape s ++ res = pre ++ (c0 + 1) :: M := by
    rw [hs, hcons, hshift, hMdef]; simp [List.append_assoc]
  have hc0le : c0 ≤ 1 := by
    have hmem : s.get dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem c0 (by rw [hcons]; exact List.mem_cons_self ..)
  have hM : M ≠ [] := by
    rw [hMdef]; intro hc
    have := congrArg List.length hc; simp [List.append_assoc] at this
  have hMb : ∀ x ∈ M, x < 4 := by
    intro x hx
    have hxin : x ∈ Compile.encodeTape s ++ res := by
      rw [htape]; exact List.mem_append_right pre (List.mem_cons_of_mem _ hx)
    rw [List.mem_append] at hxin
    rcases hxin with hx' | hx'
    · exact Compile.encodeTape_lt_four s hbit x hx'
    · exact (hres x hx').1
  have hout : Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0])
      = pre ++ M ++ [0] := by
    rw [hcons]; show Compile.encodeTape (s.set dst cs) ++ (res ++ [0]) = _
    rw [hv cs, hMdef]; simp [List.append_assoc]
  refine ⟨pre.length, M.length, ?_⟩
  rw [htape, hout]
  exact Compile.deleteCarry_drop_head pre M c0 (by omega) hM hMb

/-- In-range, `State.set` is `List.set`. -/
theorem Compile.set_eq_list_set (s : State) (dst : Var) (w : List Nat) (h : dst < s.length) :
    s.set dst w = List.set s dst w := by rw [State.set, if_pos h]

/-- Reading back a just-written register (in range). (Local — `Frame`'s
`State.get_set_eq` is not imported here.) -/
theorem Compile.get_set_eq (s : State) (dst : Var) (v : List Nat) (h : dst < s.length) :
    (s.set dst v).get dst = v := by
  unfold State.get
  rw [Compile.set_eq_list_set s dst v h, List.getElem?_set_self h, Option.getD_some]

/-- Writing register `dst` to its current value is a no-op (in range). -/
theorem Compile.set_get_self (s : State) (dst : Var) (h : dst < s.length) :
    s.set dst (s.get dst) = s := by
  have hg : s.get dst = s[dst] := by rw [State.get, List.getElem?_eq_getElem h]; rfl
  rw [Compile.set_eq_list_set s dst _ h, hg]
  exact List.set_getElem_self h

/-- Two successive writes to the same register: the first is overwritten. -/
theorem Compile.set_set (s : State) (dst : Var) (a b : List Nat) (h : dst < s.length) :
    (s.set dst a).set dst b = s.set dst b := by
  have hla : dst < (s.set dst a).length := by
    rw [Compile.set_eq_list_set s dst a h, List.length_set]; exact h
  rw [Compile.set_eq_list_set (s.set dst a) dst b hla, Compile.set_eq_list_set s dst a h,
      List.set_set, Compile.set_eq_list_set s dst b h]

/-- Writing register `dst` (in range) preserves the register count. -/
theorem Compile.length_set (s : State) (dst : Var) (v : List Nat) (h : dst < s.length) :
    (s.set dst v).length = s.length := by
  rw [Compile.set_eq_list_set s dst v h, List.length_set]

/-- Reading a register other than the one just written (in range). (Local —
`Frame`'s `State.get_set_ne` is not imported here.) -/
theorem Compile.get_set_ne (s : State) (v : Var) (val : List Nat) (r : Var)
    (hv : v < s.length) (hr : r ≠ v) :
    (s.set v val).get r = s.get r := by
  unfold State.get
  rw [Compile.set_eq_list_set s v val hv, List.getElem?_set_ne hr.symm]

/-- Writes to distinct in-range registers commute. (Local — `Frame` not imported.) -/
theorem Compile.set_comm (s : State) (a b : Var) (u w : List Nat)
    (ha : a < s.length) (hb : b < s.length) (hab : a ≠ b) :
    (s.set a u).set b w = (s.set b w).set a u := by
  have hbla : b < (s.set a u).length := by rw [Compile.length_set s a u ha]; exact hb
  have halb : a < (s.set b w).length := by rw [Compile.length_set s b w hb]; exact ha
  rw [Compile.set_eq_list_set (s.set a u) b w hbla, Compile.set_eq_list_set s a u ha,
      Compile.set_eq_list_set (s.set b w) a u halb, Compile.set_eq_list_set s b w hb,
      List.set_comm u w hab]

/-- `BitState` is preserved by writing a `≤ 1`-valued register. The general form
of `BitState_set_tail` (used by the `clear` loop, where the register is a `drop`
of the original bit-shaped content). -/
theorem Compile.BitState_set (s : State) (dst : Var) (v : List Nat)
    (h : Compile.BitState s) (hdst : dst < s.length) (hv : ∀ x ∈ v, x ≤ 1) :
    Compile.BitState (s.set dst v) := by
  rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst]
  intro reg hreg x hx
  simp only [List.mem_append, List.mem_cons] at hreg
  rcases hreg with hr | hr | hr
  · exact h reg (List.mem_of_mem_take hr) x hx
  · subst hr; exact hv x hx
  · exact h reg (List.mem_of_mem_drop hr) x hx

/-- **Padding-tolerant `BitState_set`.** `BitState` is preserved by writing a
`≤ 1`-valued register to *any* index — including one past the current length,
where `State.set` pads with empty (hence bit-safe) registers. This is the
unconditional form the `forBnd` counter-write (`set counter (replicate i 1)`,
where `counter` may exceed the live register count) and the residue-tolerant
`Cmd` induction need; `BitState_set` requires `dst < s.length`. -/
theorem Compile.BitState_set_pad (s : State) (dst : Var) (v : List Nat)
    (h : Compile.BitState s) (hv : ∀ x ∈ v, x ≤ 1) :
    Compile.BitState (s.set dst v) := by
  by_cases hd : dst < s.length
  · exact Compile.BitState_set s dst v h hd hv
  · rw [State.set, if_neg hd]
    have hpad : Compile.BitState (s ++ List.replicate (dst + 1 - s.length) ([] : List Nat)) := by
      intro reg hreg x hx
      rw [List.mem_append] at hreg
      rcases hreg with hr | hr
      · exact h reg hr x hx
      · rw [List.mem_replicate] at hr; rw [hr.2] at hx; simp at hx
    have hlen : dst < (s ++ List.replicate (dst + 1 - s.length) ([] : List Nat)).length := by
      rw [List.length_append, List.length_replicate]
      have hle : s.length ≤ dst + 1 := Nat.le_succ_of_le (Nat.le_of_not_lt hd)
      rw [Nat.add_sub_cancel' hle]
      exact Nat.lt_succ_self dst
    rw [Compile.list_set_eq_take_cons_drop _ dst v hlen]
    intro reg hreg x hx
    simp only [List.mem_append, List.mem_cons] at hreg
    rcases hreg with hr | hr | hr
    · exact hpad reg (List.mem_of_mem_take hr) x hx
    · subst hr; exact hv x hx
    · exact hpad reg (List.mem_of_mem_drop hr) x hx

/-- **State-level invariant of the `clear` loop.** Iterating the in-place `tail`
body `t ↦ t.set dst t.tail` `n` times drops the first `n` symbols of register
`dst`: `(·.set dst ·.tail)^[n] s = s.set dst ((s.get dst).drop n)`. At
`n = |s.get dst|` (`drop` empties the register) this is `clear`. Combined with the
tape-level `deleteCarry_tail_step`, this is the loop's correctness content. -/
theorem Compile.set_tail_iterate (s : State) (dst : Var) (h : dst < s.length) :
    ∀ n, (fun t : State => t.set dst (t.get dst).tail)^[n] s
        = s.set dst ((s.get dst).drop n) := by
  intro n
  induction n with
  | zero => rw [Function.iterate_zero, id_eq, List.drop_zero, Compile.set_get_self s dst h]
  | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih,
          Compile.get_set_eq s dst _ h, Compile.set_set s dst _ _ h, List.tail_drop]

/-- **`clear` = iterating the `tail` body exactly `|s.get dst|` times.** The loop
count the clear gadget's `loopTM` runs: dropping every symbol of register `dst`
empties it (`Op.eval (clear dst) s = s.set dst []`). -/
theorem Compile.iterate_tail_clear (s : State) (dst : Var) (h : dst < s.length) :
    (fun t : State => t.set dst (t.get dst).tail)^[(s.get dst).length] s
      = Op.eval (Op.clear dst) s := by
  rw [Compile.set_tail_iterate s dst h, List.drop_length]; rfl

/-! ### `clear` run lemma — reusable building blocks (Risk C2, step 3)

The delete branch of `clearRegionTM`'s loop body deletes register `dst`'s first
content cell (`deleteCarryTM`), then rewinds the head to `0`. After
`deleteCarryTM` the head sits one cell *past* the tape end, so the rewind is
`stepLeftTM ⨾ rewindTwoPhaseTM` on the post-deletion tape, which has the shape
`encodeTape output ++ ValidResidue`. The helper below packages the two-phase
rewind for any such tape. -/

/-- **Two-phase rewind on `encodeTape output ++ residue`.** From the head one cell
*before* the end (where `stepLeftTM` lands after `deleteCarryTM`), the two-phase
rewind scans left to the trailing terminator, steps off it, and scans to the
leading sentinel at index `0`. Reaches `rewindTwoPhaseTM`'s "found" halt (state
`6`) with the head at `0` and the tape unchanged. -/
theorem Compile.encodeTape_residue_twoPhaseRewind (output : State) (residue : List Nat)
    (hbit : Compile.BitState output) (hres : Compile.ValidResidue residue) :
    ∃ steps, runFlatTM steps (ScanLeft.rewindTwoPhaseTM 4 3)
        { state_idx := 0,
          tapes := [([], (Compile.encodeTape output ++ residue).length - 1,
                     Compile.encodeTape output ++ residue)] }
      = some { state_idx := 6,
               tapes := [([], 0, Compile.encodeTape output ++ residue)] }
      ∧ (∀ k, k < steps → ∀ ck,
          runFlatTM k (ScanLeft.rewindTwoPhaseTM 4 3)
              { state_idx := 0,
                tapes := [([], (Compile.encodeTape output ++ residue).length - 1,
                           Compile.encodeTape output ++ residue)] } = some ck →
          haltingStateReached (ScanLeft.rewindTwoPhaseTM 4 3) ck = false)
      ∧ steps ≤ (Compile.encodeTape output ++ residue).length + 3 := by
  set tp := Compile.encodeTape output ++ residue with htp
  have hEO2 : 2 ≤ (Compile.encodeTape output).length := by rw [Compile.encodeTape_length]; omega
  have hEOle : (Compile.encodeTape output).length ≤ tp.length := by
    rw [htp, List.length_append]; omega
  have htp_pos : 0 < tp.length := by omega
  -- getElem transfers (proof-free via getElem?).
  have hleft : ∀ i (hi : i < (Compile.encodeTape output).length) (htpi : i < tp.length),
      tp.get ⟨i, htpi⟩ = (Compile.encodeTape output).get ⟨i, hi⟩ := by
    intro i hi htpi
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc : tp[i]? = (Compile.encodeTape output)[i]? := by
      rw [htp, List.getElem?_append_left hi]
    rw [List.getElem?_eq_getElem htpi, List.getElem?_eq_getElem hi] at hc
    exact Option.some.inj hc
  have hright : ∀ i (htpi : i < tp.length) (hge : (Compile.encodeTape output).length ≤ i)
      (hir : i - (Compile.encodeTape output).length < residue.length),
      tp.get ⟨i, htpi⟩ = residue.get ⟨i - (Compile.encodeTape output).length, hir⟩ := by
    intro i htpi hge hir
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc : tp[i]? = residue[i - (Compile.encodeTape output).length]? := by
      rw [htp, List.getElem?_append_right hge]
    rw [List.getElem?_eq_getElem htpi, List.getElem?_eq_getElem hir] at hc
    exact Option.some.inj hc
  -- side conditions, shared by the run and the trajectory.
  have h_sent : tp.get ⟨0, htp_pos⟩ = 3 := by
    rw [hleft 0 (by omega) htp_pos]; exact Compile.encodeTape_get_zero output (by omega)
  have hp_lt : (Compile.encodeTape output).length - 1 < tp.length := by omega
  have h_term : tp.get ⟨(Compile.encodeTape output).length - 1, hp_lt⟩ = 3 := by
    rw [hleft ((Compile.encodeTape output).length - 1) (by omega) hp_lt]
    exact Compile.encodeTape_get_last output (by omega)
  have h_int : ∀ i, 0 < i → i < (Compile.encodeTape output).length - 1 →
      ∃ (h : i < tp.length), tp.get ⟨i, h⟩ < 4 ∧ tp.get ⟨i, h⟩ ≠ 3 := by
    intro i hi0 hip
    have hiEO : i + 1 < (Compile.encodeTape output).length := by omega
    obtain ⟨hi_lt, hne⟩ := Compile.encodeTape_interior_ne_endMark output hbit i hi0 hiEO
    have hitp : i < tp.length := by omega
    refine ⟨hitp, ?_, ?_⟩
    · rw [hleft i hi_lt hitp]; exact Compile.encodeTape_lt_four output hbit _ (List.get_mem _ _)
    · rw [hleft i hi_lt hitp]; exact hne
  have h_res : ∀ i, (Compile.encodeTape output).length - 1 < i → i ≤ tp.length - 1 →
      ∃ (h : i < tp.length), tp.get ⟨i, h⟩ < 4 ∧ tp.get ⟨i, h⟩ ≠ 3 := by
    intro i hpi hih
    have hge : (Compile.encodeTape output).length ≤ i := by omega
    have hitp : i < tp.length := by omega
    have hir : i - (Compile.encodeTape output).length < residue.length := by
      rw [htp, List.length_append] at hitp; omega
    refine ⟨hitp, ?_, ?_⟩
    · rw [hright i hitp hge hir]; exact (hres _ (List.get_mem _ _)).1
    · rw [hright i hitp hge hir]; exact (hres _ (List.get_mem _ _)).2
  have hrun := ScanLeft.rewindTwoPhase_run 4 3 (by decide) [] tp
    ((Compile.encodeTape output).length - 1) (tp.length - 1)
    htp_pos h_sent hp_lt h_term (by omega) (by omega) (by omega) h_int h_res
  have htraj := ScanLeft.rewindTwoPhase_no_early_halt 4 3 (by decide) [] tp
    ((Compile.encodeTape output).length - 1) (tp.length - 1)
    htp_pos h_sent hp_lt h_term (by omega) (by omega) (by omega) h_int h_res
  -- the step count `(head−p+1)+1+(1+1+p)` with `head = tp.length−1`, `p = E−1`
  -- equals exactly `tp.length + 3`; bound it with `omega` (`2 ≤ E ≤ tp.length`).
  refine ⟨_, hrun, htraj, ?_⟩
  omega

/-- **Explicit register decomposition of `encodeTape`** (the existential `pre`/
`rest` of `encodeTape_reg_decomp` made concrete). `pre = endMark :: encodeRegs
(s.take dst)` and `rest = encodeRegs (s.drop (dst+1)) ++ [endMark]`, so the
literal-`3` navigation lemmas (`pre = 3 :: regBlocks ((s.take dst).map shiftReg)`,
via `regBlocks_map_shiftReg`) and the `deleteCarryTM` decomposition both apply. -/
theorem Compile.encodeTape_reg_decomp_at (s : State) (dst : Var) (h : dst < s.length) :
    (∀ v : List Nat, Compile.encodeTape (s.set dst v)
        = (Compile.endMark :: Compile.encodeRegs (s.take dst))
            ++ (Compile.shiftReg v
                ++ (0 :: (Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark])))) ∧
      Compile.encodeTape s
        = (Compile.endMark :: Compile.encodeRegs (s.take dst))
            ++ (Compile.shiftReg (s.get dst)
                ++ (0 :: (Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark]))) := by
  refine ⟨?_, ?_⟩
  · intro v
    have hset : s.set dst v = s.take dst ++ v :: s.drop (dst + 1) := by
      rw [State.set, if_pos h]; exact Compile.list_set_eq_take_cons_drop s dst v h
    have hs : Compile.encodeRegs (s.set dst v)
        = Compile.encodeRegs (s.take dst)
            ++ (Compile.shiftReg v ++ ([0] ++ Compile.encodeRegs (s.drop (dst + 1)))) := by
      rw [hset, Compile.encodeRegs_append, Compile.encodeRegs_cons]; simp [List.append_assoc]
    rw [Compile.encodeTape, hs]; simp [List.append_assoc]
  · have hget : s.get dst = s[dst] := by rw [State.get, List.getElem?_eq_getElem h]; rfl
    have hs : Compile.encodeRegs s
        = Compile.encodeRegs (s.take dst)
            ++ (Compile.shiftReg (s.get dst)
                ++ ([0] ++ Compile.encodeRegs (s.drop (dst + 1)))) := by
      conv_lhs => rw [Compile.list_eq_take_getElem_drop s dst h]
      rw [Compile.encodeRegs_append, Compile.encodeRegs_cons, ← hget]; simp [List.append_assoc]
    rw [Compile.encodeTape, hs]; simp [List.append_assoc]

/-- `BitState` is preserved by clearing register `dst`'s first cell. -/
private theorem Compile.BitState_set_tail (s : State) (dst : Var)
    (h : Compile.BitState s) (hdst : dst < s.length) :
    Compile.BitState (s.set dst (s.get dst).tail) := by
  rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst]
  intro reg hreg x hx
  simp only [List.mem_append, List.mem_cons] at hreg
  rcases hreg with hr | hr | hr
  · exact h reg (List.mem_of_mem_take hr) x hx
  · subst hr
    have hmem : s.get dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
    exact h _ hmem x (List.mem_of_mem_tail hx)
  · exact h reg (List.mem_of_mem_drop hr) x hx

/-- `haltingStateReached` from a `halt[i]? = some true` fact. -/
private theorem Compile.haltingStateReached_of_halt {M : FlatTM} {i : Nat} {tapes}
    (hi : M.halt[i]? = some true) :
    haltingStateReached M { state_idx := i, tapes := tapes } = true := by
  show M.halt.getD i false = true
  rw [List.getD_eq_getElem?_getD, hi]; rfl

/-- **Delete-branch core (Risk C2, step 3): `stepDeleteRewindRawTM` run.** From
register `dst`'s content start (head `1 + |encodeRegs (s.take dst)|`) on
`encodeTape s ++ res` (register `dst` nonempty), step right, delete the first
content cell (`deleteCarryTM`), step left off the past-the-end blank, and
two-phase rewind to head `0`. Lands at `stepDeleteRewindTM_exit = 17` with the
tape `encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0])`. -/
theorem Compile.stepDeleteRewind_run (s : State) (dst : Var) (res : List Nat)
    (h : dst < s.length) (hbit : Compile.BitState s) (hne : s.get dst ≠ [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t ClearGadget.stepDeleteRewindRawTM
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (s.take dst)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.stepDeleteRewindTM_exit,
               tapes := [([], 0,
                 Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k ClearGadget.stepDeleteRewindRawTM
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (s.take dst)).length,
                           Compile.encodeTape s ++ res)] } = some ck →
          haltingStateReached ClearGadget.stepDeleteRewindRawTM ck = false)
      ∧ t ≤ 4 * (Compile.encodeTape s ++ res).length + 9 := by
  obtain ⟨c0, cs, hcons⟩ : ∃ c0 cs, s.get dst = c0 :: cs := by
    cases hg : s.get dst with
    | nil => exact absurd hg hne
    | cons c0 cs => exact ⟨c0, cs, rfl⟩
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s dst h
  have hc0le : c0 ≤ 1 := by
    have hmem : s.get dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem c0 (by rw [hcons]; exact List.mem_cons_self ..)
  have hbit_out : Compile.BitState (s.set dst cs) := by
    have := Compile.BitState_set_tail s dst hbit h; rwa [hcons] at this
  have hres0 : Compile.ValidResidue (res ++ [0]) := by
    apply Compile.ValidResidue_append _ _ hres; intro x hx
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  set pre : List Nat := Compile.endMark :: Compile.encodeRegs (s.take dst) with hpredef
  set rest : List Nat := Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] with hrestdef
  set midSuf : List Nat := Compile.shiftReg cs ++ 0 :: (rest ++ res) with hmidSufdef
  have hpre_len : pre.length = 1 + (Compile.encodeRegs (s.take dst)).length := by
    rw [hpredef]; simp [Nat.add_comm]
  set Tout : List Nat := Compile.encodeTape (s.set dst cs) ++ (res ++ [0]) with hToutdef
  have hshift : Compile.shiftReg (c0 :: cs) = (c0 + 1) :: Compile.shiftReg cs := by
    simp [Compile.shiftReg]
  -- input/output tape decompositions.
  have htape_in : Compile.encodeTape s ++ res = pre ++ (c0 + 1) :: midSuf := by
    rw [hs, hcons, hshift, hmidSufdef]; simp [List.append_assoc]
  have htape_out : pre ++ midSuf ++ [0] = Tout := by
    rw [hToutdef, hv cs, hmidSufdef]; simp [List.append_assoc]
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have hmid4 : ∀ x ∈ midSuf, x < 4 := by
    intro x hx; exact htape4 x (by rw [htape_in]; exact List.mem_append_right pre (List.mem_cons_of_mem _ hx))
  have hmid_ne : midSuf ≠ [] := by rw [hmidSufdef]; simp
  obtain ⟨tt, suf, hts⟩ := List.exists_cons_of_ne_nil hmid_ne
  have hmidlen : 1 ≤ midSuf.length := by rw [hts]; simp
  have htt4 : tt < 4 := hmid4 tt (by rw [hts]; exact List.mem_cons_self ..)
  have hsuf4 : ∀ x ∈ suf, x < 4 := fun x hx => hmid4 x (by rw [hts]; exact List.mem_cons_of_mem tt hx)
  -- length facts.
  have hTout_len : Tout.length = pre.length + midSuf.length + 1 := by
    rw [← htape_out]; simp [List.length_append]; omega
  have hhead_eq : pre.length + 1 + (tt :: suf).length = Tout.length := by
    rw [← hts, hTout_len]; omega
  have hTout4 : ∀ x ∈ Tout, x < 4 := by
    intro x hx; rw [hToutdef, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four (s.set dst cs) hbit_out x hx
    · exact (hres0 x hx).1
  have htape_eq : pre ++ (c0 + 1) :: tt :: suf = Compile.encodeTape s ++ res := by
    rw [htape_in, hts]
  -- (1) inner rewind: stepLeft (blank) ⨾ rewindTwoPhase, on Tout, head Tout.length → 0.
  obtain ⟨t_rw, h_rw, h_rw_traj, h_rw_bnd⟩ :=
    Compile.encodeTape_residue_twoPhaseRewind (s.set dst cs) (res ++ [0]) hbit_out hres0
  rw [← hToutdef] at h_rw h_rw_traj h_rw_bnd
  -- length bridge: the output tape `Tout` has the same length as the input
  -- (`encodeTape s ++ res`), and `(tt :: suf).length` is bounded by it.
  have hLinTout : (Compile.encodeTape s ++ res).length = Tout.length := by
    rw [htape_in, hTout_len]
    simp [List.length_append, List.length_cons, Nat.add_assoc]
  have hsuf_le : (tt :: suf).length ≤ (Compile.encodeTape s ++ res).length := by
    rw [hLinTout, ← hhead_eq]; omega
  have h_innerRewind :
      runFlatTM (1 + 1 + t_rw)
        (composeFlatTM (ScanLeft.stepLeftTM 4) (ScanLeft.rewindTwoPhaseTM 4 3) 1)
        { state_idx := 0, tapes := [([], Tout.length, Tout)] }
      = some { state_idx := 8, tapes := [([], 0, Tout)] } := by
    have hcomp := composeFlatTM_run (ScanLeft.stepLeftTM_valid 4)
      (ScanLeft.rewindTwoPhaseTM_valid 4 3 (by decide)) (show (1 : Nat) < 2 by decide)
      { state_idx := 0, tapes := [([], Tout.length, Tout)] }
      (by show (0 : Nat) < (ScanLeft.stepLeftTM 4).states; decide)
      [] (Tout.length - 1) Tout
      (by intro w hw
          have hr : Tout.length - 1 < Tout.length := by omega
          rw [currentTapeSymbol_in_range hr] at hw
          injection hw with hw'
          rw [show max (ScanLeft.stepLeftTM 4).sig (ScanLeft.rewindTwoPhaseTM 4 3).sig = 4 from rfl,
              ← hw', List.get_eq_getElem]
          exact hTout4 _ (List.getElem_mem hr))
      (ScanLeft.stepLeftTM_run_blank 4 [] Tout Tout.length (Nat.le_refl _))
      (ScanLeft.stepLeftTM_no_early_halt 4 [] Tout Tout.length)
      (by rw [ScanLeft.rewindTwoPhaseTM_start]; exact h_rw)
      (Compile.haltingStateReached_of_halt (ScanLeft.rewindTwoPhaseTM_halt_six 4 3))
    exact hcomp.1
  have h_innerRewind_traj :
      ∀ k, k < (1 + 1 + t_rw) → ∀ ck,
        runFlatTM k (composeFlatTM (ScanLeft.stepLeftTM 4) (ScanLeft.rewindTwoPhaseTM 4 3) 1)
            { state_idx := 0, tapes := [([], Tout.length, Tout)] } = some ck →
        haltingStateReached
          (composeFlatTM (ScanLeft.stepLeftTM 4) (ScanLeft.rewindTwoPhaseTM 4 3) 1) ck = false := by
    apply composeFlatTM_no_early_halt (ScanLeft.stepLeftTM_valid 4)
      (ScanLeft.rewindTwoPhaseTM_valid 4 3 (by decide)) (show (1 : Nat) < 2 by decide)
      { state_idx := 0, tapes := [([], Tout.length, Tout)] }
      (by show (0 : Nat) < (ScanLeft.stepLeftTM 4).states; decide)
      [] (Tout.length - 1) Tout
      (by intro w hw
          have hr : Tout.length - 1 < Tout.length := by omega
          rw [currentTapeSymbol_in_range hr] at hw
          injection hw with hw'
          rw [show max (ScanLeft.stepLeftTM 4).sig (ScanLeft.rewindTwoPhaseTM 4 3).sig = 4 from rfl,
              ← hw', List.get_eq_getElem]
          exact hTout4 _ (List.getElem_mem hr))
      (ScanLeft.stepLeftTM_run_blank 4 [] Tout Tout.length (Nat.le_refl _))
      (ScanLeft.stepLeftTM_no_early_halt 4 [] Tout Tout.length)
      (by rw [ScanLeft.rewindTwoPhaseTM_start]; exact h_rw_traj)
  -- (2) deleteCarry ⨾ inner rewind = deleteRewindRawTM.
  have h_deleteCarry : runFlatTM (3 * (tt :: suf).length + 1) ShiftTape.deleteCarryTM
      { state_idx := 0, tapes := [([], pre.length + 1, Compile.encodeTape s ++ res)] }
      = some { state_idx := 6, tapes := [([], Tout.length, Tout)] } := by
    have hd := ShiftTape.deleteCarryTM_run pre (c0 + 1) tt suf (by omega) htt4 hsuf4
    rw [htape_eq, hhead_eq, show pre ++ tt :: suf ++ [0] = Tout by rw [← hts]; exact htape_out] at hd
    exact hd
  have h_deleteRewind :
      runFlatTM ((3 * (tt :: suf).length + 1) + 1 + (1 + 1 + t_rw)) ClearGadget.deleteRewindRawTM
        { state_idx := 0, tapes := [([], pre.length + 1, Compile.encodeTape s ++ res)] }
      = some { state_idx := 15, tapes := [([], 0, Tout)] } := by
    have hcomp := composeFlatTM_run ShiftTape.deleteCarryTM_valid
      ClearGadget.innerRewind_valid (show (6 : Nat) < 7 by decide)
      { state_idx := 0, tapes := [([], pre.length + 1, Compile.encodeTape s ++ res)] }
      (by show (0 : Nat) < ShiftTape.deleteCarryTM.states; decide)
      [] Tout.length Tout
      (by intro w hw
          rw [currentTapeSymbol_out_of_range (by omega)] at hw; exact absurd hw (by simp))
      h_deleteCarry
      (by intro k hk ck hck
          have hh := ShiftTape.deleteCarryTM_no_early_halt pre (c0 + 1) tt suf (by omega) htt4 hsuf4
            k hk ck (by rw [htape_eq]; exact hck)
          exact ⟨ClearGadget.ne_of_not_halting (show ShiftTape.deleteCarryTM.halt[6]? = some true from rfl) hh, hh⟩)
      h_innerRewind
      (Compile.haltingStateReached_of_halt ClearGadget.innerRewind_halt_eight)
    exact hcomp.1
  have h_deleteRewind_traj :
      ∀ k, k < ((3 * (tt :: suf).length + 1) + 1 + (1 + 1 + t_rw)) → ∀ ck,
        runFlatTM k ClearGadget.deleteRewindRawTM
            { state_idx := 0, tapes := [([], pre.length + 1, Compile.encodeTape s ++ res)] }
          = some ck →
        haltingStateReached ClearGadget.deleteRewindRawTM ck = false := by
    apply composeFlatTM_no_early_halt ShiftTape.deleteCarryTM_valid
      ClearGadget.innerRewind_valid (show (6 : Nat) < 7 by decide)
      { state_idx := 0, tapes := [([], pre.length + 1, Compile.encodeTape s ++ res)] }
      (by show (0 : Nat) < ShiftTape.deleteCarryTM.states; decide)
      [] Tout.length Tout
      (by intro w hw
          rw [currentTapeSymbol_out_of_range (by omega)] at hw; exact absurd hw (by simp))
      h_deleteCarry
      (by intro k hk ck hck
          have hh := ShiftTape.deleteCarryTM_no_early_halt pre (c0 + 1) tt suf (by omega) htt4 hsuf4
            k hk ck (by rw [htape_eq]; exact hck)
          exact ⟨ClearGadget.ne_of_not_halting (show ShiftTape.deleteCarryTM.halt[6]? = some true from rfl) hh, hh⟩)
      h_innerRewind_traj
  -- (3) stepRight ⨾ deleteRewindRawTM = stepDeleteRewindRawTM.
  have hcell : (Compile.encodeTape s ++ res).get
      ⟨pre.length, by rw [htape_in]; simp [List.length_append]⟩ = c0 + 1 := by
    have hlt : pre.length < (Compile.encodeTape s ++ res).length := by
      rw [htape_in]; simp [List.length_append]
    have hc? : (Compile.encodeTape s ++ res)[pre.length]? = some (c0 + 1) := by
      rw [htape_in, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
    rw [List.get_eq_getElem, List.getElem?_eq_getElem hlt] at *
    exact Option.some.inj hc?
  have hr1 : pre.length < (Compile.encodeTape s ++ res).length := by
    rw [htape_in]; simp [List.length_append]
  have hr2 : pre.length + 1 < (Compile.encodeTape s ++ res).length := by
    rw [htape_in]; simp [List.length_append]; omega
  refine ⟨(1 : Nat) + 1 + ((3 * (tt :: suf).length + 1) + 1 + (1 + 1 + t_rw)), ?_, ?_, ?_⟩
  · rw [show ClearGadget.stepDeleteRewindRawTM
          = composeFlatTM (ScanLeft.stepRightTM 4) ClearGadget.deleteRewindRawTM 1 from rfl,
        ← hpre_len, hcons]
    exact (composeFlatTM_run (ScanLeft.stepRightTM_valid 4)
      ClearGadget.deleteRewindRawTM_valid (show (1 : Nat) < 2 by decide)
      { state_idx := 0, tapes := [([], pre.length, Compile.encodeTape s ++ res)] }
      (by show (0 : Nat) < (ScanLeft.stepRightTM 4).states; decide)
      [] (pre.length + 1) (Compile.encodeTape s ++ res)
      (fun w hw => by
          rw [currentTapeSymbol_in_range hr2, List.get_eq_getElem] at hw
          rw [show max (ScanLeft.stepRightTM 4).sig ClearGadget.deleteRewindRawTM.sig = 4 from rfl,
              (Option.some.inj hw).symm]
          exact htape4 _ (List.getElem_mem hr2))
      (ScanLeft.stepRightTM_run 4 [] (Compile.encodeTape s ++ res) pre.length hr1
        (by rw [hcell]; omega))
      (ScanLeft.stepRightTM_no_early_halt 4 [] (Compile.encodeTape s ++ res) pre.length)
      h_deleteRewind
      (Compile.haltingStateReached_of_halt ClearGadget.deleteRewindRawTM_halt_fifteen)).1
  · rw [show ClearGadget.stepDeleteRewindRawTM
          = composeFlatTM (ScanLeft.stepRightTM 4) ClearGadget.deleteRewindRawTM 1 from rfl,
        ← hpre_len]
    exact composeFlatTM_no_early_halt (ScanLeft.stepRightTM_valid 4)
      ClearGadget.deleteRewindRawTM_valid (show (1 : Nat) < 2 by decide)
      { state_idx := 0, tapes := [([], pre.length, Compile.encodeTape s ++ res)] }
      (by show (0 : Nat) < (ScanLeft.stepRightTM 4).states; decide)
      [] (pre.length + 1) (Compile.encodeTape s ++ res)
      (fun w hw => by
          rw [currentTapeSymbol_in_range hr2, List.get_eq_getElem] at hw
          rw [show max (ScanLeft.stepRightTM 4).sig ClearGadget.deleteRewindRawTM.sig = 4 from rfl,
              (Option.some.inj hw).symm]
          exact htape4 _ (List.getElem_mem hr2))
      (ScanLeft.stepRightTM_run 4 [] (Compile.encodeTape s ++ res) pre.length hr1
        (by rw [hcell]; omega))
      (ScanLeft.stepRightTM_no_early_halt 4 [] (Compile.encodeTape s ++ res) pre.length)
      h_deleteRewind_traj
  · -- budget: `3·M + t_rw + 6 ≤ 4·Tout.length + 9 = 4·Lin + 9` (`M ≤ Tout`, `t_rw ≤ Tout+3`).
    rw [hLinTout]
    have hd : (tt :: suf).length ≤ Tout.length := by omega
    omega

/-- **Clear loop body — delete branch (Risk C2, step 3).** When register `dst` is
nonempty, the loop body `clearBodyRawTM dst` navigates to it, tests its content
start (nonzero → content branch), deletes the first cell and rewinds, landing at
`clearBodyRawTM_exitLoop dst` with the tape `encodeTape (s.set dst (s.get
dst).tail) ++ (res ++ [0])` and head `0`. Built by `branchComposeFlatTM_run_pos`
over `navigateAndTestTM_run_content` (step 2) and `stepDeleteRewind_run`. -/
theorem Compile.clearBody_delete_run (s : State) (dst : Var) (res : List Nat)
    (h : dst < s.length) (hbit : Compile.BitState s) (hne : s.get dst ≠ [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (ClearGadget.clearBodyRawTM dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.clearBodyRawTM_exitLoop dst,
               tapes := [([], 0,
                 Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (ClearGadget.clearBodyRawTM dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitDone dst ∧
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitLoop dst ∧
          haltingStateReached (ClearGadget.clearBodyRawTM dst) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨c0, cs, hcons⟩ : ∃ c0 cs, s.get dst = c0 :: cs := by
    cases hg : s.get dst with
    | nil => exact absurd hg hne
    | cons c0 cs => exact ⟨c0, cs, rfl⟩
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s dst h
  have hc0le : c0 ≤ 1 := by
    have hmem : s.get dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem c0 (by rw [hcons]; exact List.mem_cons_self ..)
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take dst) :=
    Compile.regBlocks_map_shiftReg (s.take dst)
  have hsklen : skipped.length = dst := by
    rw [hskdef, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt h)]
  have hskip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    rw [hskdef]; intro b hb
    rw [List.mem_map] at hb
    obtain ⟨reg, hreg, rfl⟩ := hb
    have hregmem : reg ∈ s := List.mem_of_mem_take hreg
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; omega
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      have : y ≤ 1 := hbit reg hregmem y hy; omega
  set midSuf : List Nat :=
    Compile.shiftReg cs ++ 0 :: (Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] ++ res)
    with hmidSufdef
  have hshift : Compile.shiftReg (c0 :: cs) = (c0 + 1) :: Compile.shiftReg cs := by
    simp [Compile.shiftReg]
  have htape_nav : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf) := by
    rw [hs, hcons, hshift, hregBlocks, hmidSufdef]; simp [Compile.endMark, List.append_assoc]
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  -- M₂: the deletion+rewind core (step 3 sub-lemma).
  obtain ⟨t2, h_sdr, h_sdr_traj, h_t2_bnd⟩ := Compile.stepDeleteRewind_run s dst res h hbit hne hres
  rw [← hregBlocks] at h_sdr h_sdr_traj
  -- `regBlocks skipped` and `midSuf` partition the tape after the leading sentinel
  -- and `dst`'s first cell, so `|regBlocks skipped| + 2 ≤ Lin`.
  have h_rb_le : (AppendGadget.regBlocks skipped).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [htape_nav]; simp only [List.length_cons, List.length_append]; omega
  have h_nav_le : ClearGadget.navSteps skipped ≤ 2 * (AppendGadget.regBlocks skipped).length + 1 :=
    ClearGadget.navSteps_le skipped
  -- navigation run, transported to `encodeTape` form.
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_content dst,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_content skipped (c0 + 1) midSuf hskip
      (by omega) (by omega)
    rw [← htape_nav, hsklen] at hn; exact hn
  -- shared `branchComposeFlatTM` inputs (M₁ navigation, sym-bound, M₁ trajectory).
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM dst).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM dst).sig
        (max ClearGadget.stepDeleteRewindRawTM.sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM dst).sig
          (max ClearGadget.stepDeleteRewindRawTM.sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig]; rfl, (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM dst)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content dst ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim dst ∧
      haltingStateReached (ClearGadget.navigateAndTestTM dst) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM dst) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped (c0 + 1) midSuf hskip
        (by omega) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt dst) hh,
           hh⟩
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [show ClearGadget.clearBodyRawTM dst
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM dst)
            ClearGadget.stepDeleteRewindRawTM ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content dst)
            (ClearGadget.navigateAndTestTM_exit_delim dst) from rfl,
      show ClearGadget.clearBodyRawTM_exitLoop dst
        = ClearGadget.stepDeleteRewindTM_exit + (ClearGadget.navigateAndTestTM dst).states from by
          show (ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindTM_exit
            = ClearGadget.stepDeleteRewindTM_exit + (ClearGadget.navigateAndTestTM dst).states
          omega]
    exact (branchComposeFlatTM_run_pos
      (show ClearGadget.navigateAndTestTM_exit_content dst
          ≠ ClearGadget.navigateAndTestTM_exit_delim dst from by
        show (ClearGadget.navigateToRegTM dst).states + 1
            ≠ (ClearGadget.navigateToRegTM dst).states + 2
        omega)
      (ClearGadget.navigateAndTestTM_valid dst) ClearGadget.stepDeleteRewindRawTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt dst)
      (ClearGadget.navigateAndTestTM_exit_delim_lt dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (by rw [show ClearGadget.stepDeleteRewindRawTM.start = 0 from rfl]; exact h_sdr)
      (Compile.haltingStateReached_of_halt ClearGadget.stepDeleteRewindRawTM_halt_seventeen)).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_pos
      (ClearGadget.navigateAndTestTM_valid dst) ClearGadget.stepDeleteRewindRawTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt dst)
      (ClearGadget.navigateAndTestTM_exit_delim_lt dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (by rw [show ClearGadget.stepDeleteRewindRawTM.start = 0 from rfl]; exact h_sdr_traj)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.clearBodyRawTM_exitDone_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.clearBodyRawTM_exitLoop_is_halt dst) hh, hh⟩
  · -- budget: `navSteps + 3 + t2 ≤ (2·rb+1) + 3 + (4·Lin+9) ≤ 6·Lin+12` (`rb+2 ≤ Lin`).
    omega

/-- **Clear loop body — done branch (Risk C2, step 4).** When register `dst` is
empty, the loop body `clearBodyRawTM dst` navigates to it, finds the delimiter `0`
(empty → delimiter branch), and rewinds to head `0`, leaving the tape unchanged
and landing at `clearBodyRawTM_exitDone dst`. Built by `branchComposeFlatTM_run_neg`
over `navigateAndTestTM_run_delim` (step 2) and `rewindToStart_run`
(`justRewindTM = scanLeftUntilTM 4 3`). -/
theorem Compile.clearBody_done_run (s : State) (dst : Var) (res : List Nat)
    (h : dst < s.length) (hbit : Compile.BitState s) (hempty : s.get dst = [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (ClearGadget.clearBodyRawTM dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.clearBodyRawTM_exitDone dst,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (ClearGadget.clearBodyRawTM dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitDone dst ∧
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitLoop dst ∧
          haltingStateReached (ClearGadget.clearBodyRawTM dst) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s dst h
  have hbit_take : Compile.BitState (s.take dst) :=
    fun reg hreg => hbit reg (List.mem_of_mem_take hreg)
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take dst) :=
    Compile.regBlocks_map_shiftReg (s.take dst)
  have hsklen : skipped.length = dst := by
    rw [hskdef, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt h)]
  have hskip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    rw [hskdef]; intro b hb
    rw [List.mem_map] at hb
    obtain ⟨reg, hreg, rfl⟩ := hb
    have hregmem : reg ∈ s := List.mem_of_mem_take hreg
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; omega
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      have : y ≤ 1 := hbit reg hregmem y hy; omega
  set tail' : List Nat :=
    Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] ++ res with htaildef
  have htape_nav : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    rw [hs, hempty, hregBlocks, htaildef]
    simp [Compile.shiftReg, Compile.endMark, List.append_assoc]
  -- linear budget ingredients: `|regBlocks skipped| + 2 ≤ Lin` and `navSteps ≤ 2·rb+1`.
  have h_rb_le : (AppendGadget.regBlocks skipped).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [htape_nav]; simp only [List.length_cons, List.length_append]; omega
  have h_nav_le : ClearGadget.navSteps skipped ≤ 2 * (AppendGadget.regBlocks skipped).length + 1 :=
    ClearGadget.navSteps_le skipped
  -- `regBlocks skipped` is `{0,1,2}`-valued (no terminator).
  have hrb : ∀ x ∈ AppendGadget.regBlocks skipped, x < 4 ∧ x ≠ 3 := by
    rw [hregBlocks]; intro x hx
    exact ⟨Compile.encodeRegs_lt_four (s.take dst) hbit_take x hx,
           Compile.encodeRegs_no_endMark (s.take dst) hbit_take x hx⟩
  have hpref : ∀ x ∈ AppendGadget.regBlocks skipped ++ [0], x < 4 ∧ x ≠ 3 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrb x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  have hrestsplit : AppendGadget.regBlocks skipped ++ 0 :: tail'
      = (AppendGadget.regBlocks skipped ++ [0]) ++ tail' := by simp [List.append_assoc]
  -- M₃: rewind to the leading sentinel.
  have h_rewind := ScanLeft.rewindToStart_run 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind
  have h_rewind_traj := ScanLeft.rewindToStart_traj 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind_traj
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  -- shared `branchComposeFlatTM` inputs.
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM dst).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM dst).sig
        (max ClearGadget.stepDeleteRewindRawTM.sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM dst).sig
          (max ClearGadget.stepDeleteRewindRawTM.sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig]; rfl, (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim dst,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_delim skipped tail' hskip
    rw [← htape_nav, hsklen] at hn; exact hn
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM dst)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content dst ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim dst ∧
      haltingStateReached (ClearGadget.navigateAndTestTM dst) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM dst) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail' hskip
        (by decide) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt dst) hh,
           hh⟩
  have h_ne : ClearGadget.navigateAndTestTM_exit_content dst
      ≠ ClearGadget.navigateAndTestTM_exit_delim dst := by
    show (ClearGadget.navigateToRegTM dst).states + 1
        ≠ (ClearGadget.navigateToRegTM dst).states + 2
    omega
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1
      + ((1 + (AppendGadget.regBlocks skipped).length) + 1), ?_, ?_, ?_⟩
  · rw [show ClearGadget.clearBodyRawTM dst
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM dst)
            ClearGadget.stepDeleteRewindRawTM ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content dst)
            (ClearGadget.navigateAndTestTM_exit_delim dst) from rfl,
      show ClearGadget.clearBodyRawTM_exitDone dst
        = ClearGadget.justRewindTM_exit
            + ((ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindRawTM.states)
          from by
          show (ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindRawTM.states
              + ClearGadget.justRewindTM_exit
            = ClearGadget.justRewindTM_exit
                + ((ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindRawTM.states)
          omega]
    exact (branchComposeFlatTM_run_neg h_ne
      (ClearGadget.navigateAndTestTM_valid dst) ClearGadget.stepDeleteRewindRawTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt dst)
      (ClearGadget.navigateAndTestTM_exit_delim_lt dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1 h_rewind
      (Compile.haltingStateReached_of_halt (show ClearGadget.justRewindTM.halt[1]? = some true from rfl))).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_neg h_ne
      (ClearGadget.navigateAndTestTM_valid dst) ClearGadget.stepDeleteRewindRawTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt dst)
      (ClearGadget.navigateAndTestTM_exit_delim_lt dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (fun k' hk' ck' hck' => (h_rewind_traj k' hk' ck' hck').2)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.clearBodyRawTM_exitDone_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.clearBodyRawTM_exitLoop_is_halt dst) hh, hh⟩
  · -- budget: `navSteps + (rb + 5) ≤ (2·rb+1) + rb + 5 = 3·rb+6 ≤ 3·Lin ≤ 6·Lin+12`.
    omega

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

/-- Reading an in-range register of a `BitState` yields a bit-shaped list (every
symbol `≤ 1`). The atom for `Op.eval_preserves_BitState`. -/
private theorem Compile.BitState_get (s : State) (r : Var)
    (hbit : Compile.BitState s) (hr : r < s.length) :
    ∀ x ∈ s.get r, x ≤ 1 := by
  intro x hx
  refine hbit (s.get r) ?_ x hx
  rw [State.get, List.getElem?_eq_getElem hr]; exact List.getElem_mem hr

/-- **`BitState` is preserved by every op except `consLen` (HANDOFF bottom-up Task 4 — the
induction step the residue-tolerant compiler contract needs).**

`Compile_run_physical_residue` is proved by induction on `Cmd`, and every
per-fragment lemma it composes carries an `(hbit : BitState s)` premise (the
compiler's `sig = 4` alphabet has no room for a register cell `≥ 2`). So the
induction must re-establish `BitState` after each `Op`. This lemma is that step.

**Machine-checked risk finding (refines HANDOFF's "value-as-length ops are
non-`BitState`"):** of the three value-as-length ops, only **`consLen`** actually
*breaks* `BitState` — it writes `(s.get lenSrc).length` as a single cell, which is
`≥ 2` whenever `lenSrc` holds `≥ 2` symbols (witness `Op.consLen_breaks_BitState`).
`takeAt`/`dropAt` *preserve* `BitState` (their output is a sub-list of a bit-shaped
register); they are merely *useless* under `BitState` (the length read from a
`≤ 1` cell is `0` or `1`), not invariant-breaking. So Task 4's unary restatement is
required for **correctness** only for `consLen`; for `takeAt`/`dropAt` it is
required only for **expressiveness**. The `hcons` hypothesis isolates exactly the
`consLen` obligation: once HANDOFF bottom-up Task 4 restates `consLen` to write a unary block, the
written head cell is `≤ 1` and `hcons` is discharged unconditionally. -/
theorem Op.eval_preserves_BitState (o : Op) (s : State)
    (hbit : Compile.BitState s) (hbnd : o.inBounds s)
    (hcons : ∀ dst lenSrc src, o = Op.consLen dst lenSrc src →
        (s.get lenSrc).length ≤ 1) :
    Compile.BitState (Op.eval o s) := by
  cases o with
  | clear dst =>
      exact Compile.BitState_set s dst [] hbit hbnd (by simp)
  | appendOne dst =>
      refine Compile.BitState_set s dst _ hbit hbnd ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact Compile.BitState_get s dst hbit hbnd x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega
  | appendZero dst =>
      refine Compile.BitState_set s dst _ hbit hbnd ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact Compile.BitState_get s dst hbit hbnd x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega
  | copy dst src =>
      obtain ⟨hd, hs⟩ := hbnd
      exact Compile.BitState_set s dst _ hbit hd (Compile.BitState_get s src hbit hs)
  | tail dst src =>
      obtain ⟨hd, hs⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      exact Compile.BitState_get s src hbit hs x (List.mem_of_mem_tail hx)
  | head dst src =>
      obtain ⟨hd, hs⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      cases hsrc : s.get src with
      | nil => rw [hsrc] at hx; simp at hx
      | cons y ys =>
          rw [hsrc] at hx
          have hy : ∀ z ∈ (y :: ys), z ≤ 1 := by
            rw [← hsrc]; exact Compile.BitState_get s src hbit hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; exact hy y (List.mem_cons_self ..)
  | eqBit dst src1 src2 =>
      obtain ⟨hd, _, _⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      split at hx <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
  | nonEmpty dst src =>
      obtain ⟨hd, _⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      split at hx <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
  | takeAt dst src lenReg =>
      obtain ⟨hd, hs, _⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      exact Compile.BitState_get s src hbit hs x (List.mem_of_mem_take hx)
  | dropAt dst src lenReg =>
      obtain ⟨hd, hs, _⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      exact Compile.BitState_get s src hbit hs x (List.mem_of_mem_drop hx)
  | concat dst src1 src2 =>
      obtain ⟨hd, hs1, hs2⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact Compile.BitState_get s src1 hbit hs1 x hx
      · exact Compile.BitState_get s src2 hbit hs2 x hx
  | consLen dst lenSrc src =>
      obtain ⟨hd, hs, _⟩ := hbnd
      have hlen := hcons dst lenSrc src rfl
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · subst hx; exact hlen
      · exact Compile.BitState_get s src hbit hs x hx

/-- **Machine-checked counterexample: `consLen` is the one op that breaks
`BitState`.** With `s = [[1, 1]]` (a valid `BitState`) and `o = consLen 0 0 0`,
the op writes `(s.get 0).length = 2` as a register cell, so the result `[[2,1,1]]`
is *not* a `BitState`. This is why HANDOFF bottom-up Task 4 must restate `consLen` to a unary block;
the corresponding `hcons` hypothesis of `Op.eval_preserves_BitState` fails here
(`(s.get 0).length = 2 > 1`). -/
theorem Op.consLen_breaks_BitState :
    ¬ Compile.BitState (Op.eval (Op.consLen 0 0 0) [[1, 1]]) := by
  intro h
  have : (2 : Nat) ≤ 1 := by
    refine h [2, 1, 1] ?_ 2 (by simp)
    show ([2, 1, 1] : List Nat) ∈ ([[2, 1, 1]] : State)
    simp
  omega

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

/-- The **residue-tolerant** tape relation (Risk C2, the finding fix). A tape
satisfies `TapeOK out tp` when the `right` component is `encodeTape out ++ res`
for some terminator-free residue `res` (`ValidResidue`), and the head is rewound
to `0`. This replaces the exact-tape contract `tp = encodeTape out` which is
**unsatisfiable for length-decreasing ops** (the physical tape never shrinks,
`TapeMono.lean`).

Composition hides the residue existentially: the `compileSeq_sound_physical_residue`
combinator takes `TapeOK` inputs and produces a `TapeOK` output. Decode is
unaffected (`decodeTape_encodeTape_append`: `decodeTape` stops at the first
`endMark` terminator, so the trailing residue is invisible). -/
def Compile.TapeOK (out : State) (tp : List Nat) : Prop :=
  ∃ res : List Nat, Compile.ValidResidue res ∧ tp = Compile.encodeTape out ++ res

theorem Compile.TapeOK_exact (out : State) :
    Compile.TapeOK out (Compile.encodeTape out) :=
  ⟨[], Compile.ValidResidue_nil, (List.append_nil _).symm⟩

theorem Compile.TapeOK_append_residue (out : State) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    Compile.TapeOK out (Compile.encodeTape out ++ res) :=
  ⟨res, hres, rfl⟩


/-- **Reusable raw two-phase append run (Risk C2, Task 2 critical path).** Running
`appendAtThenTwoPhaseRewindTM (bit+1) dst` from head `0` on `encodeTape s ++ res`
appends bit `bit` to the end of register `dst` and two-phase-rewinds the head to
`0`, leaving `encodeTape (s.set dst (s.get dst ++ [bit])) ++ res` (residue passes
through unchanged), at the gadget's found exit `6 + (appendAtTM (bit+1) dst).states`,
never halting earlier, in `≤ 3·inputTapeLen + 8` steps. This is the bracket-free
core shared by `opAppendBit_physical_residue` (which wraps it in `rewindBracket`)
and the move gadget's `moveBitM2_run` (which composes it after a delete). -/
theorem Compile.appendBitTwoPhase_run (bit : Nat) (hb : bit ≤ 1)
    (s : State) (dst : Var) (hbit : Compile.BitState s) (hdst : dst < s.length)
    (res_in : List Nat) (hres_in : Compile.ValidResidue res_in) :
    ∃ t : Nat,
      runFlatTM t (AppendGadget.appendAtThenTwoPhaseRewindTM (bit + 1) dst)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := 6 + (AppendGadget.appendAtTM (bit + 1) dst).states,
                 tapes := [([], 0,
                   Compile.encodeTape (s.set dst (s.get dst ++ [bit])) ++ res_in)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (AppendGadget.appendAtThenTwoPhaseRewindTM (bit + 1) dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } = some ck →
          haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (bit + 1) dst) ck = false)
      ∧ t ≤ 3 * (Compile.encodeTape s ++ res_in).length + 8 := by
  have h_ins : bit + 1 < 4 := by omega
  -- === encodeTape decomposition (mirrors `opAppendBit_physical_residue`) ===
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
  -- === residue extension: post' = post ++ res_in, terminator at p = |encodeTape output| - 1 ===
  set post' : List Nat := post ++ res_in with hpost'
  set p : Nat := (Compile.encodeTape output).length - 1 with hpdef
  have hsplitr : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post'
      = Compile.encodeTape s ++ res_in := by
    rw [hpost', show (0 : Nat) :: (post ++ res_in) = (0 :: post) ++ res_in from rfl,
        ← List.append_assoc, hsplit]
  have hTPr : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post'
      = Compile.encodeTape output ++ res_in := by
    rw [hpost', show (bit + 1 : Nat) :: 0 :: (post ++ res_in)
          = ((bit + 1) :: 0 :: post) ++ res_in from rfl,
        ← List.append_assoc, htape]
  have hEO_succ : (Compile.encodeTape output).length = (Compile.encodeTape s).length + 1 := by
    have hl1 := congrArg List.length htape
    have hl2 := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil] at hl1 hl2
    omega
  have hEO_pos : 0 < (Compile.encodeTape output).length := by omega
  have hEs_ge : 2 ≤ (Compile.encodeTape s).length := by rw [Compile.encodeTape_length]; omega
  have hHDlen : ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
      + (0 :: post').length = (Compile.encodeTape s ++ res_in).length := by
    have h := congrArg List.length hsplitr
    simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega
  have hleft : ∀ i (hiL : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length)
      (hi_lt : i < (Compile.encodeTape output).length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, hiL⟩
        = (Compile.encodeTape output).get ⟨i, hi_lt⟩ := by
    intro i hiL hi_lt
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc := congrArg (fun l => l[i]?) hTPr
    simp only [] at hc
    rw [List.getElem?_eq_getElem hiL, List.getElem?_append_left hi_lt,
        List.getElem?_eq_getElem hi_lt] at hc
    exact Option.some.inj hc
  have hright : ∀ i (hiL : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length)
      (hi_ge : (Compile.encodeTape output).length ≤ i)
      (hir : i - (Compile.encodeTape output).length < res_in.length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, hiL⟩
        = res_in.get ⟨i - (Compile.encodeTape output).length, hir⟩ := by
    intro i hiL hi_ge hir
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc := congrArg (fun l => l[i]?) hTPr
    simp only [] at hc
    rw [List.getElem?_eq_getElem hiL, List.getElem?_append_right hi_ge,
        List.getElem?_eq_getElem hir] at hc
    exact Option.some.inj hc
  have h_tp_lt : ∀ x ∈ ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
      ++ (bit + 1) :: 0 :: post', x < 4 := by
    intro x hx; rw [hTPr, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four output hbit_out x hx
    · exact (hres_in x hx).1
  have h_t0 : ∀ (h : 0 < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨0, h⟩
        = 3 := by
    intro h
    rw [hleft 0 h hEO_pos]
    exact Compile.encodeTape_get_zero output hEO_pos
  have h_term : ∀ (h : p < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨p, h⟩
        = 3 := by
    intro h
    have hpEO : p < (Compile.encodeTape output).length := by rw [hpdef]; omega
    rw [hleft p h hpEO]
    exact Compile.encodeTape_get_last output hpEO
  have h_interior_ne : ∀ i, 0 < i → i < p →
      ∃ (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
          ++ (bit + 1) :: 0 :: post').length),
        (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, h⟩
          ≠ 3 := by
    intro i hi hip
    have hiEO : i + 1 < (Compile.encodeTape output).length := by rw [hpdef] at hip; omega
    obtain ⟨hi_lt, hne⟩ := Compile.encodeTape_interior_ne_endMark output hbit_out i hi hiEO
    have hi_TPr : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length := by
      rw [hTPr, List.length_append]; omega
    refine ⟨hi_TPr, ?_⟩
    rw [hleft i hi_TPr hi_lt]
    exact hne
  have h_residue_ne : ∀ i, p < i →
      i ≤ ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
        + (0 :: post').length →
      ∃ (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
          ++ (bit + 1) :: 0 :: post').length),
        (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, h⟩
          ≠ 3 := by
    intro i hip hiHD
    have hiEO : (Compile.encodeTape output).length ≤ i := by rw [hpdef] at hip; omega
    have hir : i - (Compile.encodeTape output).length < res_in.length := by
      rw [hHDlen, List.length_append] at hiHD; omega
    have hi_TPr : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length := by
      rw [hTPr, List.length_append]; omega
    refine ⟨hi_TPr, ?_⟩
    rw [hright i hi_TPr hiEO hir]
    exact (hres_in _ (List.getElem_mem _)).2
  have hp_pos : 0 < p := by rw [hpdef]; omega
  have hp_le : p ≤ ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
      + (0 :: post').length := by
    rw [hHDlen, List.length_append, hpdef, hEO_succ]; omega
  have hpost'_lt : ∀ x ∈ post', x < 4 := by
    intro x hx; rw [hpost', List.mem_append] at hx
    rcases hx with hx | hx
    · exact hpost_lt x hx
    · exact (hres_in x hx).1
  have hrun_g := AppendGadget.appendAt_twoPhaseRewind_run (bit + 1) h_ins dst [] sk bd post' p
    hlen_sk h_pre h_skip_sk hbd_ne hbd_lt hpost'_lt
    h_tp_lt hp_pos hp_le h_t0 h_term h_interior_ne h_residue_ne
  have htraj_g := AppendGadget.appendAt_twoPhaseRewind_no_early_halt (bit + 1) h_ins dst [] sk bd
    post' p hlen_sk h_pre h_skip_sk hbd_ne hbd_lt hpost'_lt
    h_tp_lt hp_pos hp_le h_t0 h_term h_interior_ne h_residue_ne
  rw [hsplitr, hTPr] at hrun_g
  rw [hsplitr] at htraj_g
  refine ⟨AppendGadget.appendAt_steps sk bd post' + 1
      + (((([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
          + (0 :: post').length) - p + 1) + 1 + (1 + 1 + p)), hrun_g.1, htraj_g, ?_⟩
  -- budget: ≤ 3·L_in + 8.
  have hstep_le : AppendGadget.appendAt_steps sk bd post'
      ≤ 2 * (Compile.encodeTape s ++ res_in).length + 3 := by
    have hb' := AppendGadget.appendAt_steps_le sk bd post'
    have hL : (AppendGadget.regBlocks sk ++ bd ++ 0 :: post').length
        = (Compile.encodeTape s ++ res_in).length := by rw [← hsplitr]; simp
    rw [hL] at hb'; exact hb'
  have hp_le' : p ≤ (Compile.encodeTape s ++ res_in).length := by rw [← hHDlen]; exact hp_le
  omega

/-- **Residue-tolerant per-op physical contract for the append op (Risk C2, step
1c — the substantive per-op proof).** The rewinding append op `opAppendBitRewind
(bit+1) … dst` run on `encodeTape s ++ res_in` (the previous fragment may leave a
`ValidResidue res_in`) halts at the unique exit with the **head rewound to `0`**
and the tape `encodeTape (output) ++ res_in` — the residue **passes through
unchanged** (`res_out = res_in`) since the insert grows `encodeTape s` by exactly
one cell — never halting earlier, in `≤ 3·inputTapeLen + 8` steps.

Mechanism: `rewindBracket_transport` (the general halt-demotion run transport) fed
by the proven two-phase append gadget run `appendAt_twoPhaseRewind_run`/
`_no_early_halt`. The `encodeTape` decomposition (sentinel-folded blocks `sk`/`bd`,
the real-terminator position `p = (encodeTape output).length − 1`, the residue
sitting past `p`) discharges the gadget's tape side-conditions from
`encodeTape_get_zero`/`_get_last`/`_interior_ne_endMark` and `ValidResidue res_in`.

The budget is `+8` (not the single-phase `appendBit_physical`'s `+6`): the
two-phase rewind costs two extra `Lmove`s — one to step off the residue side of
the real terminator, plus the boundary-phase setup. Still linear, so it composes
into the quadratic `Compile_run_physical_residue` total with constant slack. -/
theorem Compile.opAppendBit_physical_residue (bit : Nat) (hb : bit ≤ 1)
    (s : State) (dst : Var) (hbit : Compile.BitState s) (hdst : dst < s.length)
    (res_in : List Nat) (hres_in : Compile.ValidResidue res_in) :
    ∃ t : Nat,
      runFlatTM t (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M
          (initFlatConfig (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M
            [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opAppendBitRewind (bit + 1) (by omega) dst).exit,
                 tapes := [([], 0,
                   Compile.encodeTape (s.set dst (s.get dst ++ [bit])) ++ res_in)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M
              (initFlatConfig (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M
                [Compile.encodeTape s ++ res_in]) = some ck →
          ck.state_idx ≠ (Compile.opAppendBitRewind (bit + 1) (by omega) dst).exit ∧
          haltingStateReached (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M ck = false)
      ∧ t ≤ 3 * (Compile.encodeTape s ++ res_in).length + 8 := by
  have h_ins : bit + 1 < 4 := by omega
  -- === encodeTape decomposition (mirrors `appendBit_physical`) ===
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
  -- === residue extension: post' = post ++ res_in, terminator at p = |encodeTape output| - 1 ===
  set post' : List Nat := post ++ res_in with hpost'
  set p : Nat := (Compile.encodeTape output).length - 1 with hpdef
  -- start/exit tape equalities with the residue appended.
  have hsplitr : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post'
      = Compile.encodeTape s ++ res_in := by
    rw [hpost', show (0 : Nat) :: (post ++ res_in) = (0 :: post) ++ res_in from rfl,
        ← List.append_assoc, hsplit]
  have hTPr : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post'
      = Compile.encodeTape output ++ res_in := by
    rw [hpost', show (bit + 1 : Nat) :: 0 :: (post ++ res_in)
          = ((bit + 1) :: 0 :: post) ++ res_in from rfl,
        ← List.append_assoc, htape]
  -- length facts.
  have hEO_succ : (Compile.encodeTape output).length = (Compile.encodeTape s).length + 1 := by
    have hl1 := congrArg List.length htape
    have hl2 := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil] at hl1 hl2
    omega
  have hEO_pos : 0 < (Compile.encodeTape output).length := by omega
  have hEs_ge : 2 ≤ (Compile.encodeTape s).length := by rw [Compile.encodeTape_length]; omega
  -- `HD` (the head position = exit-tape length − 1) equals the input tape length.
  have hHDlen : ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
      + (0 :: post').length = (Compile.encodeTape s ++ res_in).length := by
    have h := congrArg List.length hsplitr
    simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega
  -- `get` transfer across `hTPr`, split into the `encodeTape output` part and the
  -- residue part (avoids a `Fin.val`-coercion mismatch in `getElem_append_*`).
  have hleft : ∀ i (hiL : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length)
      (hi_lt : i < (Compile.encodeTape output).length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, hiL⟩
        = (Compile.encodeTape output).get ⟨i, hi_lt⟩ := by
    intro i hiL hi_lt
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc := congrArg (fun l => l[i]?) hTPr
    simp only [] at hc
    rw [List.getElem?_eq_getElem hiL, List.getElem?_append_left hi_lt,
        List.getElem?_eq_getElem hi_lt] at hc
    exact Option.some.inj hc
  have hright : ∀ i (hiL : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length)
      (hi_ge : (Compile.encodeTape output).length ≤ i)
      (hir : i - (Compile.encodeTape output).length < res_in.length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, hiL⟩
        = res_in.get ⟨i - (Compile.encodeTape output).length, hir⟩ := by
    intro i hiL hi_ge hir
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc := congrArg (fun l => l[i]?) hTPr
    simp only [] at hc
    rw [List.getElem?_eq_getElem hiL, List.getElem?_append_right hi_ge,
        List.getElem?_eq_getElem hir] at hc
    exact Option.some.inj hc
  -- === the gadget side-conditions, via the `encodeTape output ++ res_in` structure ===
  have h_tp_lt : ∀ x ∈ ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
      ++ (bit + 1) :: 0 :: post', x < 4 := by
    intro x hx; rw [hTPr, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four output hbit_out x hx
    · exact (hres_in x hx).1
  have h_t0 : ∀ (h : 0 < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨0, h⟩
        = 3 := by
    intro h
    rw [hleft 0 h hEO_pos]
    exact Compile.encodeTape_get_zero output hEO_pos
  have h_term : ∀ (h : p < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨p, h⟩
        = 3 := by
    intro h
    have hpEO : p < (Compile.encodeTape output).length := by rw [hpdef]; omega
    rw [hleft p h hpEO]
    exact Compile.encodeTape_get_last output hpEO
  have h_interior_ne : ∀ i, 0 < i → i < p →
      ∃ (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
          ++ (bit + 1) :: 0 :: post').length),
        (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, h⟩
          ≠ 3 := by
    intro i hi hip
    have hiEO : i + 1 < (Compile.encodeTape output).length := by rw [hpdef] at hip; omega
    obtain ⟨hi_lt, hne⟩ := Compile.encodeTape_interior_ne_endMark output hbit_out i hi hiEO
    have hi_TPr : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length := by
      rw [hTPr, List.length_append]; omega
    refine ⟨hi_TPr, ?_⟩
    rw [hleft i hi_TPr hi_lt]
    exact hne
  have h_residue_ne : ∀ i, p < i →
      i ≤ ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
        + (0 :: post').length →
      ∃ (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
          ++ (bit + 1) :: 0 :: post').length),
        (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, h⟩
          ≠ 3 := by
    intro i hip hiHD
    -- HD = |encodeTape s ++ res_in|; i ≤ HD < |encodeTape output ++ res_in|.
    have hiEO : (Compile.encodeTape output).length ≤ i := by rw [hpdef] at hip; omega
    have hir : i - (Compile.encodeTape output).length < res_in.length := by
      rw [hHDlen, List.length_append] at hiHD; omega
    have hi_TPr : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length := by
      rw [hTPr, List.length_append]; omega
    refine ⟨hi_TPr, ?_⟩
    rw [hright i hi_TPr hiEO hir]
    exact (hres_in _ (List.getElem_mem _)).2
  -- positivity/range for the gadget's terminator position.
  have hp_pos : 0 < p := by rw [hpdef]; omega
  have hp_le : p ≤ ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
      + (0 :: post').length := by
    rw [hHDlen, List.length_append, hpdef, hEO_succ]; omega
  -- === run the two-phase append gadget ===
  have hrun_g := AppendGadget.appendAt_twoPhaseRewind_run (bit + 1) h_ins dst [] sk bd post' p
    hlen_sk h_pre h_skip_sk hbd_ne hbd_lt
    (by intro x hx; rw [hpost', List.mem_append] at hx
        rcases hx with hx | hx
        · exact hpost_lt x hx
        · exact (hres_in x hx).1)
    h_tp_lt hp_pos hp_le h_t0 h_term h_interior_ne h_residue_ne
  have htraj_g := AppendGadget.appendAt_twoPhaseRewind_no_early_halt (bit + 1) h_ins dst [] sk bd
    post' p hlen_sk h_pre h_skip_sk hbd_ne hbd_lt
    (by intro x hx; rw [hpost', List.mem_append] at hx
        rcases hx with hx | hx
        · exact hpost_lt x hx
        · exact (hres_in x hx).1)
    h_tp_lt hp_pos hp_le h_t0 h_term h_interior_ne h_residue_ne
  -- the gadget machine is defeq to the rewindBracket composite; rewrite tapes/state.
  simp only [AppendGadget.appendAtThenTwoPhaseRewindTM] at hrun_g htraj_g
  rw [hsplitr, hTPr, show (6 : Nat) + (AppendGadget.appendAtTM (bit + 1) dst).states
        = (AppendGadget.appendAtTM (bit + 1) dst).states + 6 from Nat.add_comm ..] at hrun_g
  rw [hsplitr] at htraj_g
  -- feed through the general transport lemma.
  have htrans := Compile.rewindBracket_transport (AppendGadget.appendAtTM (bit + 1) dst)
    (AppendGadget.appendAtTM_exit dst)
    (AppendGadget.appendAtTM_valid (bit + 1) (by omega) dst)
    (AppendGadget.appendAtTM_exit_lt (bit + 1) dst)
    (AppendGadget.appendAtTM_tapes (bit + 1) dst) (AppendGadget.appendAtTM_sig (bit + 1) dst)
    hrun_g.1 htraj_g
  -- align the start config with `initFlatConfig`.
  have hstart0 : (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M.start = 0 := by
    show (Compile.rewindBracket (AppendGadget.appendAtTM (bit + 1) dst) _ _ _ _ _).M.start = 0
    rw [Compile.rewindBracket_M, Compile.joinTwoHalts_start, composeFlatTM_start,
        AppendGadget.appendAtTM_start]
  have hinit : initFlatConfig (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M
        [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hstart0, List.map_cons, List.map_nil]
  refine ⟨AppendGadget.appendAt_steps sk bd post' + 1
      + (((([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
          + (0 :: post').length) - p + 1) + 1 + (1 + 1 + p)), ?_, ?_, ?_⟩
  · -- `opAppendBitRewind` is defeq to the `rewindBracket` of `htrans`; normalise the
    -- start config with `hinit` (head `[].length` is defeq `0`), then close by defeq.
    rw [hinit]; exact htrans.1
  · intro k hk ck hck
    rw [hinit] at hck
    exact htrans.2 k hk ck hck
  · -- budget: ≤ 3·L_in + 8.
    have hstep_le : AppendGadget.appendAt_steps sk bd post'
        ≤ 2 * (Compile.encodeTape s ++ res_in).length + 3 := by
      have hb' := AppendGadget.appendAt_steps_le sk bd post'
      have hL : (AppendGadget.regBlocks sk ++ bd ++ 0 :: post').length
          = (Compile.encodeTape s ++ res_in).length := by rw [← hsplitr]; simp
      rw [hL] at hb'; exact hb'
    have hp_le' : p ≤ (Compile.encodeTape s ++ res_in).length := by rw [← hHDlen]; exact hp_le
    omega

/-- The append ops' linear budget `3·tapeLen + 8` implies the per-op contract's
quadratic budget `9·tapeLen² + 9` (every encoded tape has `tapeLen ≥ 2`). Lets
the linear append cases discharge the (necessarily quadratic, for multi-cell ops)
`compileOp_sound_physical_residue` budget. -/
theorem Compile.linear_le_quadratic_tapeLen (s : State) (res_in : List Nat) :
    3 * (Compile.encodeTape s ++ res_in).length + 8
      ≤ 9 * (Compile.encodeTape s ++ res_in).length
          * (Compile.encodeTape s ++ res_in).length + 9 := by
  have hL : 2 ≤ (Compile.encodeTape s ++ res_in).length := by
    rw [List.length_append, Compile.encodeTape_length]; omega
  set L := (Compile.encodeTape s ++ res_in).length with hLdef
  have h1 : 9 * L ≤ 9 * L * L := by
    calc 9 * L = 9 * L * 1 := by rw [Nat.mul_one]
      _ ≤ 9 * L * L := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Uniform per-term bound on `loopBudget`.** If every iteration body and the
done branch each run in `≤ M` steps (counting the `+1` backward/leave bridge),
then the whole counted loop runs in `≤ (n+1)·M` steps. The clear loop instantiates
`M` with a linear-in-tape-length bound, giving the quadratic total. -/
theorem Compile.loopBudget_le (tIter : Nat → Nat) (tDone M : Nat) :
    ∀ n, (tDone + 1 ≤ M) → (∀ j, j < n → tIter j + 1 ≤ M) →
      loopBudget tIter tDone n ≤ (n + 1) * M
  | 0, hDone, _ => by simp only [loopBudget]; omega
  | n + 1, hDone, hIter => by
      have ih := Compile.loopBudget_le tIter tDone M n hDone
        (fun j hj => hIter j (Nat.lt_succ_of_lt hj))
      have hI : tIter n + 1 ≤ M := hIter n (Nat.lt_succ_self n)
      have hstep : loopBudget tIter tDone (n + 1) = tIter n + 1 + loopBudget tIter tDone n := rfl
      have hexp : (n + 1 + 1) * M = (n + 1) * M + M := by ring
      rw [hstep, hexp]
      omega

/-- **Clear-loop budget arithmetic.** The per-iteration linear bound `6·L+13`
summed over `n+1 ≤ L−1` terms is dominated by the quadratic `9·L²+9`. Proven by
substituting `L = n+2+d` (legal since `n+2 ≤ L`): the difference is a polynomial
with non-negative coefficients. -/
theorem Compile.clearBudget_arith (n L : Nat) (h : n + 2 ≤ L) :
    (n + 1) * (6 * L + 13) ≤ 9 * L * L + 9 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  nlinarith [Nat.zero_le n, Nat.zero_le d, Nat.zero_le (n * d)]

/-- **`clearRegionTM` run (Risk C2, step 5b).** Assembled from `loopTM_run`. The
loop deletes register `dst`'s `n = |s.get dst|` leading cells one per iteration
(`clearBody_delete_run`), then the done branch fires when `dst` is empty
(`clearBody_done_run`). The tape sequence is `T j = encodeTape (s.set dst (drop
(n−j))) ++ (res_in ++ replicate (n−j) 0)`: `T n = encodeTape s ++ res_in` (start)
and `T 0 = encodeTape (clear dst s) ++ (res_in ++ replicate n 0)` (end). Each
deleted cell becomes a `0` filler appended to the residue. The total step count
is bounded by `9·L²+9` where `L = |encodeTape s ++ res_in|` (every loop tape has
length `L`, each iteration is `O(L)`, and there are `≤ L` iterations). -/
theorem Compile.clearRegionTM_run (s : State) (dst : Var) (res_in : List Nat)
    (h : dst < s.length) (hbit : Compile.BitState s) (hres : Compile.ValidResidue res_in) :
    ∃ t, runFlatTM t (ClearGadget.clearRegionTM dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
      = some { state_idx := ClearGadget.clearRegionTM_exit dst,
               tapes := [([], 0, Compile.encodeTape (Op.eval (Op.clear dst) s)
                                  ++ (res_in ++ List.replicate (s.get dst).length 0))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (ClearGadget.clearRegionTM dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } = some ck →
          ck.state_idx ≠ ClearGadget.clearRegionTM_exit dst ∧
          haltingStateReached (ClearGadget.clearRegionTM dst) ck = false)
      ∧ t ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length + 9
      := by
  set n := (s.get dst).length with hn
  -- the loop's tape after `n − j` deletions of `dst`'s leading cells.
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 0, Compile.encodeTape (s.set dst ((s.get dst).drop (n - j)))
              ++ (res_in ++ List.replicate (n - j) 0)) with hTdef
  have hBstart : (ClearGadget.clearBodyRawTM dst).start = 0 := by
    show (branchComposeFlatTM _ _ _ _ _).start = 0
    rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start dst
  -- every drop of `dst`'s (bit-shaped) content keeps the state bit-shaped.
  have hbit_drop : ∀ k, Compile.BitState (s.set dst ((s.get dst).drop k)) := by
    intro k
    refine Compile.BitState_set s dst _ hbit h (fun x hx => ?_)
    have hmem : s.get dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem x (List.mem_of_mem_drop hx)
  -- all tape symbols of `T j` are `< 4`.
  have hT_lt : ∀ j x, x ∈ (T j).2.2 → x < 4 := by
    intro j x hx
    simp only [hTdef] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four _ (hbit_drop _) x hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hres x hx).1
      · rw [List.mem_replicate] at hx; omega
  have h_sym : ∀ m v, currentTapeSymbol (T m) = some v → v < (ClearGadget.clearBodyRawTM dst).sig := by
    intro m v hv
    have hsig : (ClearGadget.clearBodyRawTM dst).sig = 4 := by
      show (branchComposeFlatTM _ _ _ _ _).sig = 4
      rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig]; rfl
    rw [hsig]
    have hmem : v ∈ (T m).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_lt m v hmem
  -- **Budget bookkeeping.** Every loop tape `T j` (`j ≤ n`) has the same length
  -- `L = |encodeTape s ++ res_in|` (a delete frees a cell but adds a `0` filler),
  -- and the cleared register satisfies `n + 2 ≤ L`.
  have hTlen : ∀ j, j ≤ n →
      (T j).2.2.length = (Compile.encodeTape s ++ res_in).length := by
    intro j hj
    have hdroplen : ((s.get dst).drop (n - j)).length = j := by
      rw [List.length_drop, ← hn]; omega
    have hbal := Compile.encodeTape_set_length s dst ((s.get dst).drop (n - j)) h
    rw [hdroplen, ← hn] at hbal
    simp only [hTdef, List.length_append, List.length_replicate]
    omega
  have hnL : n + 2 ≤ (Compile.encodeTape s ++ res_in).length := by
    have hsize := State.size_set_add s dst ([] : List Nat)
    simp only [List.length_nil, Nat.add_zero] at hsize
    rw [List.length_append, Compile.encodeTape_length]
    omega
  -- done branch: at `T 0`, register `dst` is empty.
  have hdone := Compile.clearBody_done_run (s.set dst ((s.get dst).drop n)) dst
    (res_in ++ List.replicate n 0)
    (by rw [Compile.length_set s dst _ h]; exact h)
    (hbit_drop n)
    (by rw [Compile.get_set_eq s dst _ h, hn]; exact List.drop_length)
    (Compile.ValidResidue_append_replicate_zero res_in n hres)
  obtain ⟨tDone, hdr, hdt, hdb⟩ := hdone
  -- done-branch tape is `T 0` (length `L`), so its bound becomes `tDone + 1 ≤ 6·L+13`.
  have h_done_bnd : tDone + 1 ≤ 6 * (Compile.encodeTape s ++ res_in).length + 13 := by
    have hlen0 := hTlen 0 (Nat.zero_le n)
    simp only [hTdef, Nat.sub_zero] at hlen0
    rw [hlen0] at hdb
    omega
  have hT0 : T 0 = ([], 0, Compile.encodeTape (s.set dst ((s.get dst).drop n))
      ++ (res_in ++ List.replicate n 0)) := by simp only [hTdef, Nat.sub_zero]
  -- per-iteration delete: `T (j+1) → T j` for `j < n`.
  have hiter_ex : ∀ j, j < n → ∃ t,
      runFlatTM t (ClearGadget.clearBodyRawTM dst)
          { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T (j + 1)] }
        = some { state_idx := ClearGadget.clearBodyRawTM_exitLoop dst, tapes := [T j] } ∧
      (∀ k, k < t → ∀ ck,
        runFlatTM k (ClearGadget.clearBodyRawTM dst)
            { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T (j + 1)] } = some ck →
        ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitDone dst ∧
        ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitLoop dst ∧
        haltingStateReached (ClearGadget.clearBodyRawTM dst) ck = false) ∧
      t ≤ 6 * (Compile.encodeTape s ++ res_in).length + 12 := by
    intro j hj
    obtain ⟨t, hr, ht, hb⟩ := Compile.clearBody_delete_run
      (s.set dst ((s.get dst).drop (n - (j + 1)))) dst (res_in ++ List.replicate (n - (j + 1)) 0)
      (by rw [Compile.length_set s dst _ h]; exact h)
      (hbit_drop _)
      (by rw [Compile.get_set_eq s dst _ h]
          intro hc
          have hlen : ((s.get dst).drop (n - (j + 1))).length = 0 := by rw [hc]; rfl
          rw [List.length_drop] at hlen; omega)
      (Compile.ValidResidue_append_replicate_zero res_in (n - (j + 1)) hres)
    -- the input tape is `T (j+1)`, whose length is `L`; rewrite the bound to `L`.
    have hlenj := hTlen (j + 1) (by omega)
    simp only [hTdef] at hlenj
    rw [hlenj] at hb
    -- bridge the delete output to `T j`.
    have hstate_eq :
        (s.set dst ((s.get dst).drop (n - (j + 1)))).set dst
            (((s.set dst ((s.get dst).drop (n - (j + 1)))).get dst).tail)
          = s.set dst ((s.get dst).drop (n - j)) := by
      rw [Compile.get_set_eq s dst _ h, List.tail_drop, Compile.set_set s dst _ _ h,
          show n - (j + 1) + 1 = n - j from by omega]
    have hres_eq : (res_in ++ List.replicate (n - (j + 1)) 0) ++ [0]
        = res_in ++ List.replicate (n - j) 0 := by
      rw [List.append_assoc, ← List.replicate_succ', show n - (j + 1) + 1 = n - j from by omega]
    rw [hstate_eq, hres_eq] at hr
    refine ⟨t, ?_, ?_, hb⟩
    · rw [hBstart]; simp only [hTdef]; exact hr
    · rw [hBstart]; simp only [hTdef]; exact ht
  -- choose per-iteration step counts.
  set tIter : Nat → Nat := fun j => if hj : j < n then (hiter_ex j hj).choose else 0 with htIter
  have h_ne_loop : ClearGadget.clearBodyRawTM_exitDone dst ≠ ClearGadget.clearBodyRawTM_exitLoop dst := by
    show (ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindRawTM.states
          + ClearGadget.justRewindTM_exit
        ≠ (ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindTM_exit
    show _ + 19 + 1 ≠ _ + 17
    omega
  have h_done_full :
      runFlatTM tDone (ClearGadget.clearBodyRawTM dst)
          { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T 0] }
        = some { state_idx := ClearGadget.clearBodyRawTM_exitDone dst, tapes := [T 0] } ∧
      (∀ k, k < tDone → ∀ ck,
          runFlatTM k (ClearGadget.clearBodyRawTM dst)
              { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitDone dst ∧
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitLoop dst ∧
          haltingStateReached (ClearGadget.clearBodyRawTM dst) ck = false) := by
    refine ⟨?_, ?_⟩
    · rw [hBstart, hT0]; exact hdr
    · rw [hBstart, hT0]; exact hdt
  have h_iter_full : ∀ j, j < n →
      runFlatTM (tIter j) (ClearGadget.clearBodyRawTM dst)
          { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T (j + 1)] }
        = some { state_idx := ClearGadget.clearBodyRawTM_exitLoop dst, tapes := [T j] } ∧
      (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (ClearGadget.clearBodyRawTM dst)
              { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitDone dst ∧
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitLoop dst ∧
          haltingStateReached (ClearGadget.clearBodyRawTM dst) ck = false) := by
    intro j hj
    have hspec := (hiter_ex j hj).choose_spec
    simp only [htIter, dif_pos hj]
    exact ⟨hspec.1, hspec.2.1⟩
  -- per-iteration linear bound, extracted from the (now bound-carrying) existential.
  have h_iter_bnd : ∀ j, j < n →
      tIter j + 1 ≤ 6 * (Compile.encodeTape s ++ res_in).length + 13 := by
    intro j hj
    have hb := (hiter_ex j hj).choose_spec.2.2
    simp only [htIter, dif_pos hj]
    omega
  have hmain := loopTM_run (ClearGadget.clearBodyRawTM dst)
    (ClearGadget.clearBodyRawTM_exitDone dst) (ClearGadget.clearBodyRawTM_exitLoop dst)
    (ClearGadget.clearBodyRawTM_valid dst)
    (ClearGadget.clearBodyRawTM_exitDone_lt dst) (ClearGadget.clearBodyRawTM_exitLoop_lt dst)
    h_ne_loop T h_sym tIter tDone h_done_full n h_iter_full
  have hmain_traj := loopTM_no_early_halt (ClearGadget.clearBodyRawTM dst)
    (ClearGadget.clearBodyRawTM_exitDone dst) (ClearGadget.clearBodyRawTM_exitLoop dst)
    (ClearGadget.clearBodyRawTM_valid dst)
    (ClearGadget.clearBodyRawTM_exitDone_lt dst) (ClearGadget.clearBodyRawTM_exitLoop_lt dst)
    h_ne_loop T h_sym tIter tDone h_done_full n h_iter_full
  -- convert `T n`, `T 0`, `B.start`, `B.states` to the stated forms.
  have hTn : T n = ([], 0, Compile.encodeTape s ++ res_in) := by
    simp only [hTdef, Nat.sub_self, List.drop_zero, List.replicate_zero, List.append_nil]
    rw [Compile.set_get_self s dst h]
  rw [hBstart, hTn, hT0] at hmain
  rw [hBstart, hTn] at hmain_traj
  have hMeq : ClearGadget.clearRegionTM dst
      = loopTM (ClearGadget.clearBodyRawTM dst) (ClearGadget.clearBodyRawTM_exitDone dst)
          (ClearGadget.clearBodyRawTM_exitLoop dst) := rfl
  have hExeq : ClearGadget.clearRegionTM_exit dst = (ClearGadget.clearBodyRawTM dst).states := rfl
  have hEval : Op.eval (Op.clear dst) s = s.set dst ((s.get dst).drop n) := by
    have hdn : (s.get dst).drop n = [] := by rw [hn]; exact List.drop_length
    rw [hdn]; rfl
  refine ⟨loopBudget tIter tDone n, ?_, ?_, ?_⟩
  · rw [hMeq, hExeq, hEval]; exact hmain
  · intro k hk ck hck
    rw [hMeq] at hck
    have hh := hmain_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.opClear dst).exit_is_halt hh, hh⟩
  · -- budget: `loopBudget ≤ (n+1)·(6L+13) ≤ 9L²+9` (each tape length `L`, `n+2 ≤ L`).
    exact le_trans
      (Compile.loopBudget_le tIter tDone (6 * (Compile.encodeTape s ++ res_in).length + 13)
        n h_done_bnd h_iter_bnd)
      (Compile.clearBudget_arith n (Compile.encodeTape s ++ res_in).length hnL)

/-! ### The move-one-bit transfer gadget (Risk C2, Task 2 critical path)

`moveRegionTM src dst` transfers register `src`'s content, **one bit at a time**,
to the **end** of register `dst` (FIFO — order preserved), emptying `src`. It is
the single building block of every remaining cross-register op
(`copy`/`tail`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`): e.g. `copy dst src sc`
= move `src→sc` then move `sc→`(`src`&`dst`).

**Structure — mirrors `clearRegionTM` exactly, with the content branch doing a
read+append instead of a bare delete.** The loop body navigates to `src`; on the
content branch (src non-empty) it reads the front bit (`bitReadTM`), deletes that
cell and rewinds (`stepDeleteRewindRawTM`, exactly as `clear`), then appends the
bit (`+1`) to `dst` and two-phase-rewinds; on the delim branch (src empty) it just
rewinds and the loop stops.

**✅ Probe-validated end-to-end** (2026-06-05, `#eval` on real `encodeTape`s, both
`dst>src` and `dst<src`): `encodeTape [[1,0],[1]] → encodeTape [[],[1,1,0]] ++ [0,0]`
and `encodeTape [[1],[0,1]] → encodeTape [[1,0,1],[]] ++ [0,0]` (residue =
`replicate (#moved bits) 0`). The exit-state offsets below were read off the probe
and verified to make the `loopTM` continue/terminate correctly. -/

/-- Single-bit transfer engine for a fixed bit `b`: delete `src`'s front cell and
rewind (`stepDeleteRewindRawTM`), then append `b+1` to `dst` and two-phase-rewind. -/
def Compile.moveBitM2TM (b dst : Nat) : FlatTM :=
  composeFlatTM ClearGadget.stepDeleteRewindRawTM
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ClearGadget.stepDeleteRewindTM_exit

/-- The surviving (found) exit of `moveBitM2TM` (independent of `b`): the
`stepDeleteRewindRawTM` state count plus the append bracket's found exit
(`appendAtTM.states + 6`). -/
def Compile.moveBitM2_exit (dst : Nat) : Nat :=
  ClearGadget.stepDeleteRewindRawTM.states + ((AppendGadget.appendAtTM 1 dst).states + 6)

/-- Content branch (src non-empty): read the front bit, then run the matching
single-bit transfer engine. The two bit paths exit at distinct states
(`moveContentExit0`/`moveContentExit1`), merged by `joinTwoHalts` below. -/
def Compile.moveContentRawTM (dst : Nat) : FlatTM :=
  branchComposeFlatTM Compile.bitReadTM (Compile.moveBitM2TM 0 dst) (Compile.moveBitM2TM 1 dst)
    Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1

/-- Bit-0 path exit of `moveContentRawTM`. -/
def Compile.moveContentExit0 (dst : Nat) : Nat :=
  Compile.bitReadTM.states + Compile.moveBitM2_exit dst

/-- Bit-1 path exit of `moveContentRawTM` (shifted by the bit-0 engine's states). -/
def Compile.moveContentExit1 (dst : Nat) : Nat :=
  Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states + Compile.moveBitM2_exit dst

/-- Content branch with the two bit-exits merged into one (`moveContentExit0`). -/
def Compile.moveContentTM (dst : Nat) : FlatTM :=
  Compile.joinTwoHalts (Compile.moveContentRawTM dst)
    (Compile.moveContentExit0 dst) (Compile.moveContentExit1 dst)

/-- The loop body: navigate to `src`, branch content (move one bit) vs delim
(src empty → rewind & stop). -/
def Compile.moveBodyRawTM (src dst : Nat) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM src) (Compile.moveContentTM dst)
    ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content src) (ClearGadget.navigateAndTestTM_exit_delim src)

/-- The loop's "continue" exit (content branch fired: one bit moved). -/
def Compile.moveBodyRawTM_exitLoop (src dst : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + Compile.moveContentExit0 dst

/-- The loop's "done" exit (delim branch fired: src empty). -/
def Compile.moveBodyRawTM_exitDone (src dst : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
    + ClearGadget.justRewindTM_exit

/-- The full move gadget: loop the body until `src` empties. -/
def Compile.moveRegionTM (src dst : Nat) : FlatTM :=
  loopTM (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)

/-- The single halt state of `moveRegionTM` (the `loopTM` done-exit, at `B.states`). -/
def Compile.moveRegionTM_exit (src dst : Nat) : Nat := (Compile.moveBodyRawTM src dst).states

theorem Compile.moveBitM2TM_tapes (b dst : Nat) : (Compile.moveBitM2TM b dst).tapes = 1 := by
  rw [Compile.moveBitM2TM, composeFlatTM_tapes]; exact ClearGadget.stepDeleteRewindRawTM_tapes

theorem Compile.moveContentRawTM_tapes (dst : Nat) : (Compile.moveContentRawTM dst).tapes = 1 := by
  rw [Compile.moveContentRawTM, branchComposeFlatTM_tapes]; exact Compile.bitReadTM_tapes

theorem Compile.moveContentTM_tapes (dst : Nat) : (Compile.moveContentTM dst).tapes = 1 := by
  rw [Compile.moveContentTM, Compile.joinTwoHalts_tapes]; exact Compile.moveContentRawTM_tapes dst

theorem Compile.moveBodyRawTM_tapes (src dst : Nat) : (Compile.moveBodyRawTM src dst).tapes = 1 := by
  rw [Compile.moveBodyRawTM, branchComposeFlatTM_tapes]; exact ClearGadget.navigateAndTestTM_tapes src

theorem Compile.moveRegionTM_tapes (src dst : Nat) : (Compile.moveRegionTM src dst).tapes = 1 := by
  rw [Compile.moveRegionTM, loopTM_tapes]; exact Compile.moveBodyRawTM_tapes src dst

theorem Compile.moveRegionTM_start (src dst : Nat) : (Compile.moveRegionTM src dst).start = 0 := by
  show (Compile.moveBodyRawTM src dst).start = 0
  show (branchComposeFlatTM _ _ _ _ _).start = 0
  rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src

/-- The branch that reaches the **kept** exit `h1`: `joinTwoHalts` agrees with the
raw machine, reaching `h1` at step `T`; the trajectory never hits `h1` and never
halts. -/
theorem Compile.joinTwoHalts_reaches_kept (raw : FlatTM) (h1 h2 : Nat) (cfg0 : FlatTMConfig)
    (T : Nat) (tape : List Nat × Nat × List Nat)
    (hraw : runFlatTM T raw cfg0 = some { state_idx := h1, tapes := [tape] })
    (hraw_traj : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck →
        haltingStateReached raw ck = false)
    (hh1 : raw.halt[h1]? = some true) (hh2 : raw.halt[h2]? = some true) :
    runFlatTM T (joinTwoHalts raw h1 h2) cfg0 = some { state_idx := h1, tapes := [tape] } ∧
    (∀ k, k < T → ∀ ck, runFlatTM k (joinTwoHalts raw h1 h2) cfg0 = some ck →
        ck.state_idx ≠ h1 ∧ haltingStateReached (joinTwoHalts raw h1 h2) ck = false) := by
  have hnv : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck → ck.state_idx ≠ h2 :=
    fun k hk ck hck => ClearGadget.ne_of_not_halting hh2 (hraw_traj k hk ck hck)
  refine ⟨?_, ?_⟩
  · rw [joinTwoHalts_run_eq_weak raw h1 h2 T cfg0 hnv]; exact hraw
  · intro k hk ck hck
    rw [joinTwoHalts_run_eq_weak raw h1 h2 k cfg0
        (fun j hj cj hcj => hnv j (by omega) cj hcj)] at hck
    have hnh := hraw_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting hh1 hnh, Compile.joinTwoHalts_halting_false raw h1 h2 ck hnh⟩

/-- The branch that reaches the **demoted** exit `h2`: `joinTwoHalts` reaches `h2`
at step `T`, then bridges to the kept exit `h1` in one more step. -/
theorem Compile.joinTwoHalts_reaches_demoted (raw : FlatTM) (h1 h2 : Nat) (cfg0 : FlatTMConfig)
    (T : Nat) (left right : List Nat) (head : Nat)
    (hraw : runFlatTM T raw cfg0 = some { state_idx := h2, tapes := [(left, head, right)] })
    (hraw_traj : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck →
        haltingStateReached raw ck = false)
    (hh1 : raw.halt[h1]? = some true) (hh2 : raw.halt[h2]? = some true) (hne : h1 ≠ h2)
    (h_sym : ∀ v, currentTapeSymbol (left, head, right) = some v → v < raw.sig) :
    runFlatTM (T + 1) (joinTwoHalts raw h1 h2) cfg0
        = some { state_idx := h1, tapes := [(left, head, right)] } ∧
    (∀ k, k < T + 1 → ∀ ck, runFlatTM k (joinTwoHalts raw h1 h2) cfg0 = some ck →
        ck.state_idx ≠ h1 ∧ haltingStateReached (joinTwoHalts raw h1 h2) ck = false) := by
  have hnv : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck → ck.state_idx ≠ h2 :=
    fun k hk ck hck => ClearGadget.ne_of_not_halting hh2 (hraw_traj k hk ck hck)
  have hjoinT : runFlatTM T (joinTwoHalts raw h1 h2) cfg0
      = some { state_idx := h2, tapes := [(left, head, right)] } := by
    rw [joinTwoHalts_run_eq_weak raw h1 h2 T cfg0 hnv]; exact hraw
  have hjoinHalt_h2 : haltingStateReached (joinTwoHalts raw h1 h2)
      { state_idx := h2, tapes := [(left, head, right)] } = false := by
    show (raw.halt.set h2 false).getD h2 false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl]; split <;> rfl
  have hstep : stepFlatTM (joinTwoHalts raw h1 h2)
      { state_idx := h2, tapes := [(left, head, right)] }
      = some { state_idx := h1, tapes := [(left, head, right)] } :=
    joinTwoHalts_step_to_h1 raw h1 h2 left right head h_sym
  refine ⟨?_, ?_⟩
  · rw [runFlatTM_compose (joinTwoHalts raw h1 h2) T 1 cfg0 _ hjoinT]
    show (if haltingStateReached (joinTwoHalts raw h1 h2)
              { state_idx := h2, tapes := [(left, head, right)] } = true then _
          else match stepFlatTM (joinTwoHalts raw h1 h2)
              { state_idx := h2, tapes := [(left, head, right)] } with
            | none => _ | some c => runFlatTM 0 (joinTwoHalts raw h1 h2) c) = _
    rw [if_neg (by rw [hjoinHalt_h2]; decide), hstep]
    rfl
  · intro k hk ck hck
    rcases Nat.lt_or_ge k T with hkT | hkT
    · rw [joinTwoHalts_run_eq_weak raw h1 h2 k cfg0
          (fun j hj cj hcj => hnv j (by omega) cj hcj)] at hck
      have hnh := hraw_traj k hkT ck hck
      exact ⟨ClearGadget.ne_of_not_halting hh1 hnh, Compile.joinTwoHalts_halting_false raw h1 h2 ck hnh⟩
    · have hkeq : k = T := by omega
      subst hkeq
      rw [hjoinT] at hck
      obtain rfl := (Option.some.inj hck).symm
      exact ⟨Ne.symm hne, hjoinHalt_h2⟩

/-- `appendAtTM`'s state count is independent of the inserted symbol (`ins` only
enters via `insertCarryTM ins`, whose `states` field is the constant `6`). -/
theorem Compile.appendAtTM_states_eq (ins dst : Nat) :
    (AppendGadget.appendAtTM ins dst).states = (AppendGadget.appendAtTM 1 dst).states := by
  induction dst with
  | zero => rfl
  | succ d ih =>
      rw [show AppendGadget.appendAtTM ins (d + 1)
            = composeFlatTM (ScanPast.scanPastDelimTM 4 0) (AppendGadget.appendAtTM ins d) 1 from rfl,
          show AppendGadget.appendAtTM 1 (d + 1)
            = composeFlatTM (ScanPast.scanPastDelimTM 4 0) (AppendGadget.appendAtTM 1 d) 1 from rfl,
          composeFlatTM_states, composeFlatTM_states, ih]

/-- **The single-bit transfer engine run (Risk C2, Task 2).** Run from `src`'s
content start (head `1 + |encodeRegs (s.take src)|`) with `src`'s front bit `b`
(`s.get src = b :: cs`), `moveBitM2TM b dst` deletes that front cell, rewinds,
appends `b` to the end of `dst`, and two-phase-rewinds, landing at
`moveBitM2_exit dst` with the tape
`encodeTape ((s.set src cs).set dst (s.get dst ++ [b])) ++ (res ++ [0])` and head
`0`. Composes `stepDeleteRewind_run` (on `src`) with `appendBitTwoPhase_run` (on
the deleted state, appending to `dst`). -/
theorem Compile.moveBitM2_run (s : State) (src dst : Var) (b : Nat) (cs : List Nat)
    (hb : b ≤ 1) (hsd : src ≠ dst) (hsrc : src < s.length) (hdst : dst < s.length)
    (hbit : Compile.BitState s) (hcons : s.get src = b :: cs) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBitM2TM b dst)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBitM2_exit dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBitM2TM b dst)
            { state_idx := 0,
              tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.moveBitM2TM b dst) ck = false)
    ∧ t ≤ 7 * (Compile.encodeTape s ++ res).length + 18 := by
  have hne : s.get src ≠ [] := by rw [hcons]; exact List.cons_ne_nil _ _
  have htl : (s.get src).tail = cs := by rw [hcons, List.tail_cons]
  -- Phase 1: delete src's front cell + rewind.
  obtain ⟨t1, h_sdr, h_sdr_traj, h_t1_bnd⟩ :=
    Compile.stepDeleteRewind_run s src res hsrc hbit hne hres
  rw [htl] at h_sdr
  -- Phase 2 ingredients (on the post-delete state `s.set src cs`).
  have hbit1 : Compile.BitState (s.set src cs) := by
    have := Compile.BitState_set_tail s src hbit hsrc; rwa [htl] at this
  have hlen1 : (s.set src cs).length = s.length := Compile.length_set s src cs hsrc
  have hdst1 : dst < (s.set src cs).length := by rw [hlen1]; exact hdst
  have hres1 : Compile.ValidResidue (res ++ [0]) := by
    apply Compile.ValidResidue_append _ _ hres; intro x hx
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  obtain ⟨t2, h_app, h_app_traj, h_t2_bnd⟩ :=
    Compile.appendBitTwoPhase_run b hb (s.set src cs) dst hbit1 hdst1 (res ++ [0]) hres1
  have hgetdst : (s.set src cs).get dst = s.get dst :=
    Compile.get_set_ne s src cs dst hsrc (Ne.symm hsd)
  rw [hgetdst] at h_app
  -- length balance: deleting a bit and padding the residue with `[0]` keeps the length.
  have hLbal : (Compile.encodeTape (s.set src cs) ++ (res ++ [0])).length
      = (Compile.encodeTape s ++ res).length := by
    have hbalance := Compile.encodeTape_set_length s src cs hsrc
    rw [hcons] at hbalance
    simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil]
      at hbalance ⊢
    omega
  -- M₂ start (= 0).
  have hM2start : (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).start = 0 := by
    show (composeFlatTM (AppendGadget.appendAtTM (b + 1) dst) (ScanLeft.rewindTwoPhaseTM 4 3)
          (AppendGadget.appendAtTM_exit dst)).start = 0
    rw [composeFlatTM_start, AppendGadget.appendAtTM_start]
  set right₁ : List Nat := Compile.encodeTape (s.set src cs) ++ (res ++ [0]) with hr1
  -- shared compose inputs.
  have hvalid1 : validFlatTM ClearGadget.stepDeleteRewindRawTM := ClearGadget.stepDeleteRewindRawTM_valid
  have hvalid2 : validFlatTM (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) :=
    AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst
  have hexit_lt : ClearGadget.stepDeleteRewindTM_exit < ClearGadget.stepDeleteRewindRawTM.states := by
    show (17 : Nat) < ClearGadget.stepDeleteRewindRawTM.states
    show (17 : Nat) < 19; omega
  have hcfg0lt : (0 : Nat) < ClearGadget.stepDeleteRewindRawTM.states := by
    show (0 : Nat) < 19; omega
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, right₁) = some v →
      v < max ClearGadget.stepDeleteRewindRawTM.sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).sig := by
    intro v hv
    rw [hr1, show currentTapeSymbol (([] : List Nat), 0,
          Compile.encodeTape (s.set src cs) ++ (res ++ [0])) = some 3 from rfl] at hv
    rw [show max ClearGadget.stepDeleteRewindRawTM.sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).sig = 4 from by
        rw [AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl]
    have : v = 3 := (Option.some.inj hv).symm
    omega
  -- per-component trajectory hyps with the `≠ exit` part for M₁.
  have h_traj1 : ∀ k, k < t1 → ∀ ck,
      runFlatTM k ClearGadget.stepDeleteRewindRawTM
          { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                       Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.stepDeleteRewindTM_exit ∧
      haltingStateReached ClearGadget.stepDeleteRewindRawTM ck = false := by
    intro k hk ck hck
    have hh := h_sdr_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting ClearGadget.stepDeleteRewindRawTM_halt_seventeen hh, hh⟩
  have h_app_traj' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
          { state_idx := (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).start,
            tapes := [([], 0, right₁)] } = some ck →
      haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ck = false := by
    rw [hM2start, hr1]; exact h_app_traj
  -- h_halt2 (the M₂ exit halts).
  have h_halt2 : haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
      { state_idx := 6 + (AppendGadget.appendAtTM (b + 1) dst).states,
        tapes := [([], 0, Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                    ++ (res ++ [0]))] } = true := by
    rw [show (6 : Nat) + (AppendGadget.appendAtTM (b + 1) dst).states
          = (AppendGadget.appendAtTM (b + 1) dst).states + 6 from Nat.add_comm ..]
    exact Compile.haltingStateReached_of_halt
      (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst)
  have hmoveeq : Compile.moveBitM2TM b dst
      = composeFlatTM ClearGadget.stepDeleteRewindRawTM
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
          ClearGadget.stepDeleteRewindTM_exit := rfl
  have hstate_eq : Compile.moveBitM2_exit dst
      = (6 + (AppendGadget.appendAtTM (b + 1) dst).states)
          + ClearGadget.stepDeleteRewindRawTM.states := by
    show ClearGadget.stepDeleteRewindRawTM.states + ((AppendGadget.appendAtTM 1 dst).states + 6)
        = (6 + (AppendGadget.appendAtTM (b + 1) dst).states)
            + ClearGadget.stepDeleteRewindRawTM.states
    rw [Compile.appendAtTM_states_eq (b + 1) dst]; omega
  have hmain := composeFlatTM_run hvalid1 hvalid2 hexit_lt
    { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                 Compile.encodeTape s ++ res)] }
    hcfg0lt [] 0 right₁ hsym h_sdr h_traj1
    (by rw [hM2start]; exact h_app) h_halt2
  refine ⟨t1 + 1 + t2, ?_, ?_, ?_⟩
  · rw [hmoveeq, hstate_eq]; exact hmain.1
  · intro k hk ck hck
    rw [hmoveeq] at hck ⊢
    exact composeFlatTM_no_early_halt hvalid1 hvalid2 hexit_lt
      { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                   Compile.encodeTape s ++ res)] }
      hcfg0lt [] 0 right₁ hsym h_sdr h_traj1 h_app_traj' k hk ck hck
  · rw [hLbal] at h_t2_bnd
    omega

/-! #### `moveContent` scaffolding (the bit-read branch over the transfer engine). -/

theorem Compile.moveBitM2TM_sig (b dst : Nat) : (Compile.moveBitM2TM b dst).sig = 4 := by
  rw [Compile.moveBitM2TM, composeFlatTM_sig, AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl

theorem Compile.moveBitM2TM_valid (b dst : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.moveBitM2TM b dst) :=
  composeFlatTM_valid ClearGadget.stepDeleteRewindRawTM
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ClearGadget.stepDeleteRewindTM_exit
    ClearGadget.stepDeleteRewindRawTM_valid
    (AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst)
    (by show (17 : Nat) < ClearGadget.stepDeleteRewindRawTM.states; show (17 : Nat) < 19; omega)
    ClearGadget.stepDeleteRewindRawTM_tapes
    (AppendGadget.appendAtThenTwoPhaseRewindTM_tapes (b + 1) dst)

theorem Compile.moveBitM2_exit_is_halt (b dst : Nat) :
    (Compile.moveBitM2TM b dst).halt[Compile.moveBitM2_exit dst]? = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro ClearGadget.stepDeleteRewindRawTM
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ClearGadget.stepDeleteRewindTM_exit
    ((AppendGadget.appendAtTM (b + 1) dst).states + 6)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst)
  rw [Compile.appendAtTM_states_eq (b + 1) dst] at h
  exact h

theorem Compile.moveBitM2_exit_lt (b dst : Nat) :
    Compile.moveBitM2_exit dst < (Compile.moveBitM2TM b dst).states := by
  show ClearGadget.stepDeleteRewindRawTM.states + ((AppendGadget.appendAtTM 1 dst).states + 6)
      < (composeFlatTM ClearGadget.stepDeleteRewindRawTM
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
          ClearGadget.stepDeleteRewindTM_exit).states
  rw [composeFlatTM_states, AppendGadget.appendAtThenTwoPhaseRewindTM_states,
      Compile.appendAtTM_states_eq (b + 1) dst,
      show (ScanLeft.rewindTwoPhaseTM 4 3).states = 8 from rfl]
  omega

theorem Compile.moveContentRawTM_valid (dst : Nat) : validFlatTM (Compile.moveContentRawTM dst) :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.bitReadTM_valid
    (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide)
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide)
    Compile.bitReadTM_tapes (Compile.moveBitM2TM_tapes 0 dst) (Compile.moveBitM2TM_tapes 1 dst)

theorem Compile.moveContentRawTM_sig (dst : Nat) : (Compile.moveContentRawTM dst).sig = 4 := by
  rw [Compile.moveContentRawTM, branchComposeFlatTM_sig, Compile.bitReadTM_sig,
      Compile.moveBitM2TM_sig 0 dst, Compile.moveBitM2TM_sig 1 dst]; rfl

theorem Compile.moveContentExit0_is_halt (dst : Nat) :
    (Compile.moveContentRawTM dst).halt[Compile.moveContentExit0 dst]? = some true := by
  rw [Compile.moveContentExit0, Compile.moveContentRawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2_exit_lt 0 dst)
    (Compile.moveBitM2_exit_is_halt 0 dst)

theorem Compile.moveContentExit1_is_halt (dst : Nat) :
    (Compile.moveContentRawTM dst).halt[Compile.moveContentExit1 dst]? = some true := by
  rw [Compile.moveContentExit1, Compile.moveContentRawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2_exit_is_halt 1 dst)

theorem Compile.moveContentExit0_ne_exit1 (dst : Nat) :
    Compile.moveContentExit0 dst ≠ Compile.moveContentExit1 dst := by
  show Compile.bitReadTM.states + Compile.moveBitM2_exit dst
      ≠ Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states + Compile.moveBitM2_exit dst
  have h0 : 0 < (Compile.moveBitM2TM 0 dst).states := by
    have := Compile.moveBitM2_exit_lt 0 dst; omega
  omega

/-- **The content-branch run (Risk C2, Task 2).** Run from `src`'s content start
(head `H = 1 + |regBlocks (map shiftReg (s.take src))|`) with front bit `b`
(`s.get src = b :: cs`), `moveContentTM dst` reads the bit and runs the matching
single-bit transfer, the two bit-paths merging through `joinTwoHalts` into
`moveContentExit0 dst`. The tape becomes
`encodeTape ((s.set src cs).set dst (s.get dst ++ [b])) ++ (res ++ [0])`. Mirrors
`opInnerBit_run`. -/
theorem Compile.moveContent_run (s : State) (src dst : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd : src ≠ dst)
    (hbit : Compile.BitState s) (hsrc : src < s.length) (hdst : dst < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveContentTM dst)
        { state_idx := 0,
          tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveContentExit0 dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveContentTM dst)
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.moveContentExit0 dst ∧
        haltingStateReached (Compile.moveContentTM dst) ck = false)
    ∧ t ≤ 7 * (Compile.encodeTape s ++ res).length + 21 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.moveContentRawTM dst with hrawdef
  set h1 := Compile.moveContentExit0 dst with hh1def
  set h2 := Compile.moveContentExit1 dst with hh2def
  have hraweq : branchComposeFlatTM Compile.bitReadTM
      (Compile.moveBitM2TM 0 dst) (Compile.moveBitM2TM 1 dst)
      Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1 = raw := rfl
  have hMeq : Compile.moveContentTM dst = joinTwoHalts raw h1 h2 := rfl
  rw [hMeq]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hHeq : (1 : Nat) + (Compile.encodeRegs (s.take src)).length = H := by
    rw [hHdef, hskdef, Compile.regBlocks_map_shiftReg]
  -- length facts.
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  -- content decomposition (`src` nonempty).
  set tail' := Compile.shiftReg cs ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src hsrc
    rw [← hskdef] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg cs := by
      rw [hcons]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hHlt : H < (Compile.encodeTape s ++ res).length := by
    rw [hdecomp, hHdef]; simp only [List.length_cons, List.length_append]; omega
  have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = b + 1 := by
    have h? : (Compile.encodeTape s ++ res)[H]? = some (b + 1) := by
      rw [hdecomp, hHdef,
          show ((3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail'))
            = ((3 : Nat) :: AppendGadget.regBlocks skipped) ++ ((b + 1) :: tail') from by simp,
          List.getElem?_append_right (by simp only [List.length_cons]; omega),
          show 1 + (AppendGadget.regBlocks skipped).length
            - ((3 : Nat) :: AppendGadget.regBlocks skipped).length = 0 from by
              simp only [List.length_cons]; omega]
      rfl
    rw [List.getElem?_eq_getElem hHlt] at h?
    rw [List.get_eq_getElem]; exact Option.some.inj h?
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max Compile.bitReadTM.sig
          (max (Compile.moveBitM2TM 0 dst).sig (Compile.moveBitM2TM 1 dst).sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    rw [Compile.bitReadTM_sig]
    have : v < 4 := by have : v = b + 1 := (Option.some.inj hv).symm; omega
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < Compile.bitReadTM.states := by rw [Compile.bitReadTM_states]; omega
  have hexit_neq : Compile.bitReadTM_exit_b0 ≠ Compile.bitReadTM_exit_b1 := by decide
  have hep_lt : Compile.bitReadTM_exit_b0 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide
  have hen_lt : Compile.bitReadTM_exit_b1 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide
  have hh1_is := Compile.moveContentExit0_is_halt dst
  have hh2_is := Compile.moveContentExit1_is_halt dst
  have hh_ne := Compile.moveContentExit0_ne_exit1 dst
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  have htest_run := Compile.bitReadTM_run b hb [] (Compile.encodeTape s ++ res) H hHlt hcellH
  have htest_traj : ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.bitReadTM cfg0 = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧ ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧
      haltingStateReached Compile.bitReadTM ck = false := by
    intro k hk ck hck
    exact Compile.bitReadTM_no_early_halt [] (Compile.encodeTape s ++ res) H k hk ck hck
  interval_cases b
  · -- bit 0 (cell value 1): pos branch, transfer engine for bit 0; kept exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM2_run s src dst 0 cs (by omega) hsd hsrc hdst hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM2_exit_is_halt 0 dst))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM2_exit dst + Compile.bitReadTM.states = h1 := by
      rw [hh1def]; show Compile.moveBitM2_exit dst + Compile.bitReadTM.states
        = Compile.bitReadTM.states + Compile.moveBitM2_exit dst
      omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [0])) ++ (res ++ [0]))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega
  · -- bit 1 (cell value 2): neg branch, transfer engine for bit 1; demoted exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM2_run s src dst 1 cs (by omega) hsd hsrc hdst hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM2_exit_is_halt 1 dst))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM2_exit dst
        + (Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states) = h2 := by
      rw [hh2def]; show Compile.moveBitM2_exit dst
          + (Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states)
        = Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states + Compile.moveBitM2_exit dst
      omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [1])) ++ (res ++ [0])) 0
      hneg.1 (fun k hk ck hck => hneg_traj k hk ck hck) hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [1])) ++ (res ++ [0]))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.moveContentRawTM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega

/-! ### Residue-tolerant `navigateAndTest` reading (Class-A cross-register ops)

The Class-A cross-register ops (`nonEmpty`/`head`/`eqBit`: ≤ 1-cell output) all
start by reading register `src`'s first tape cell and branching. `ClearGadget`'s
`navigateAndTestTM_run_content`/`_run_delim` do exactly this, but are stated on a
clean tape `3 :: (regBlocks skipped ++ v :: tail')`. The lemmas below lift them to
the residue-tolerant `encodeTape s ++ res` shape (the input every compiled
fragment actually sees): register `src`'s slot sits between the leading sentinel
and the trailing terminator, so the residue (past the terminator) is irrelevant
to the read. The exit head lands on `src`'s first cell at index
`1 + |regBlocks (preceding registers)|`; the **content** exit means `src` is
non-empty (answer bit `1`), the **delim** exit means `src` is empty (answer bit
`0`). Reusable by every Class-A op. -/

/-- Helper bridge: `s.take src` mapped through `shiftReg` has length `src`. -/
private theorem Compile.skipped_length (s : State) (src : Var) (h : src < s.length) :
    ((s.take src).map Compile.shiftReg).length = src := by
  rw [List.length_map, List.length_take, Nat.min_eq_left (le_of_lt h)]

/-- The `h_skip` precondition: every preceding register block (`shiftReg` of a
`BitState` register) is delimiter-free and `< 4`. -/
private theorem Compile.skipped_ok (s : State) (src : Var) (hbit : Compile.BitState s) :
    ∀ b' ∈ (s.take src).map Compile.shiftReg, (∀ x ∈ b', x ≠ 0) ∧ (∀ x ∈ b', x < 4) := by
  intro b' hb'
  rw [List.mem_map] at hb'
  obtain ⟨reg, hreg, rfl⟩ := hb'
  have hregs : reg ∈ s := List.mem_of_mem_take hreg
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; omega
  · intro x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hbit reg hregs y hy; omega

/-- **Residue-tolerant `navigateAndTest` — content branch (`src` non-empty).** -/
theorem Compile.navTestReg_run_content (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hne : s.get src ≠ []) :
    runFlatTM (ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1)
        (ClearGadget.navigateAndTestTM src)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_content src,
               tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                          Compile.encodeTape s ++ res)] } := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  obtain ⟨b, r, hbr⟩ : ∃ b r, s.get src = b :: r := by
    cases hsr : s.get src with
    | nil => exact absurd hsr hne
    | cons b r => exact ⟨b, r, rfl⟩
  have hb1 : b ≤ 1 := by
    have hmem : s.get src ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem b (by simp [hbr])
  set tail' := Compile.shiftReg r ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg r := by
      rw [hbr]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hcontent := ClearGadget.navigateAndTestTM_run_content skipped (b + 1) tail'
    (Compile.skipped_ok s src hbit) (by omega) (by omega)
  rw [hskiplen] at hcontent
  rw [← hdecomp] at hcontent
  exact hcontent

/-- **Residue-tolerant `navigateAndTest` — delim branch (`src` empty).** -/
theorem Compile.navTestReg_run_delim (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = []) :
    runFlatTM (ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1)
        (ClearGadget.navigateAndTestTM src)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim src,
               tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                          Compile.encodeTape s ++ res)] } := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  set tail' := Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = [] := by
      rw [hempty]; rfl
    rw [hsr, List.append_nil] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hdelim := ClearGadget.navigateAndTestTM_run_delim skipped tail'
    (Compile.skipped_ok s src hbit)
  rw [hskiplen] at hdelim
  rw [← hdecomp] at hdelim
  exact hdelim

/-- Navtest no-early-halt trajectory (avoids *both* exits), content branch. -/
theorem Compile.navTestReg_traj_content (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hne : s.get src ≠ []) :
    ∀ k, k < ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  obtain ⟨b, r, hbr⟩ : ∃ b r, s.get src = b :: r := by
    cases hsr : s.get src with
    | nil => exact absurd hsr hne
    | cons b r => exact ⟨b, r, rfl⟩
  have hb1 : b ≤ 1 := by
    have hmem : s.get src ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem b (by simp [hbr])
  set tail' := Compile.shiftReg r ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg r := by
      rw [hbr]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  intro k hk ck hck
  have hsk_eq : ClearGadget.navigateAndTestTM src = ClearGadget.navigateAndTestTM skipped.length := by
    rw [hskiplen]
  rw [hsk_eq, hdecomp] at hck
  have hh := ClearGadget.navigateAndTestTM_no_early_halt skipped (b + 1) tail'
    (Compile.skipped_ok s src hbit) (by omega) k hk ck hck
  rw [← hsk_eq] at hh
  exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
         ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh, hh⟩

/-- Navtest no-early-halt trajectory (avoids *both* exits), delim branch. -/
theorem Compile.navTestReg_traj_delim (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = []) :
    ∀ k, k < ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  set tail' := Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = [] := by rw [hempty]; rfl
    rw [hsr, List.append_nil] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  intro k hk ck hck
  have hsk_eq : ClearGadget.navigateAndTestTM src = ClearGadget.navigateAndTestTM skipped.length := by
    rw [hskiplen]
  rw [hsk_eq, hdecomp] at hck
  have hh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail'
    (Compile.skipped_ok s src hbit) (by omega) k hk ck hck
  rw [← hsk_eq] at hh
  exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
         ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh, hh⟩

/-! #### `compileTestBit` run lemmas (Risk C2, bottom-up Task 2)

The micro-steps of `exactOneOneTM`, the inner-tester composition, the raw
three-leaf tester, and the two packaged contracts `Compile.testBitReg_run_pos` /
`Compile.testBitReg_run_neg` that the `compileIfBit` residue combinator consumes:
the tester reaches `exitPos` iff `s.get t = [1]`, with the head back at `0` and
the tape **unchanged** (the branch bodies then start from their own
`initFlatConfig`). -/

/-- `exactOneOneTM` step, state 0 on a `1` cell (bit 0): → NEG, stay. -/
private theorem Compile.exactOneOne_step0_b0 (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 1) :
    stepFlatTM Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 2, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym' : cfg.tapes.map currentTapeSymbol = [some 1] := by
    show [currentTapeSymbol (left, head, right)] = [some 1]
    rw [currentTapeSymbol_in_range h, hget]
  show Option.bind (Compile.exactOneOneTM.trans.find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
  have hMatch : entryMatchesConfig
      { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
    show ((0 : Nat) == cfg.state_idx &&
        decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
    rw [hSym']; rfl
  rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
        = some { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
                 dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
    show List.find? _ (_ :: _) = _
    rw [List.find?_cons, hMatch]]
  rfl

/-- `exactOneOneTM` step, state 0 on a `2` cell (bit 1): → state 1, right. -/
private theorem Compile.exactOneOne_step0_b1 (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 2) :
    stepFlatTM Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym' : cfg.tapes.map currentTapeSymbol = [some 2] := by
    show [currentTapeSymbol (left, head, right)] = [some 2]
    rw [currentTapeSymbol_in_range h, hget]
  show Option.bind (Compile.exactOneOneTM.trans.find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
  have hNo : entryMatchesConfig
      { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
        decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym']
    have h_ne : ([some 1] : List (Option Nat)) ≠ [some 2] := by decide
    simp [h_ne]
  have hMatch : entryMatchesConfig
      { src_state := 0, src_tape_vals := [some 2], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] } cfg = true := by
    show ((0 : Nat) == cfg.state_idx &&
        decide (([some 2] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
    rw [hSym']; rfl
  rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
        = some { src_state := 0, src_tape_vals := [some 2], dst_state := 1,
                 dst_write_vals := [none], move_dirs := [TMMove.Rmove] } from by
    show List.find? _ (_ :: _ :: _) = _
    rw [List.find?_cons, hNo, List.find?_cons, hMatch]]
  rfl

/-- `exactOneOneTM` step, state 1 on a cell `v ∈ {0, 1, 2}` (the block-end `0`
→ POS = 3; a bit cell → NEG = 2): stay. -/
private theorem Compile.exactOneOne_step1 (left right : List Nat) (head : Nat) (v : Nat)
    (hv : v ≤ 2) (h : head < right.length) (hget : right.get ⟨head, h⟩ = v) :
    stepFlatTM Compile.exactOneOneTM { state_idx := 1, tapes := [(left, head, right)] }
      = some { state_idx := if v = 0 then 3 else 2, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 1, tapes := [(left, head, right)] }
  have hSym' : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]
    rw [currentTapeSymbol_in_range h, hget]
  have hNo0 : ∀ (sv : List (Option Nat)) (d : Nat) (w : List (Option Nat)) (m : List TMMove),
      entryMatchesConfig
        { src_state := 0, src_tape_vals := sv, dst_state := d,
          dst_write_vals := w, move_dirs := m } cfg = false := by
    intro sv d w m
    show ((0 : Nat) == cfg.state_idx && _) = false
    rfl
  show Option.bind (Compile.exactOneOneTM.trans.find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
  interval_cases v
  · have hMatch : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 0] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
          = some { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
                   dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
      show List.find? _ (_ :: _ :: _ :: _) = _
      rw [List.find?_cons, hNo0, List.find?_cons, hNo0, List.find?_cons, hMatch]]
    rfl
  · have hNo2 : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 0] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
      rw [hSym']
      have h_ne : ([some 0] : List (Option Nat)) ≠ [some 1] := by decide
      simp [h_ne]
    have hMatch : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
          = some { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
                   dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
      show List.find? _ (_ :: _ :: _ :: _ :: _) = _
      rw [List.find?_cons, hNo0, List.find?_cons, hNo0, List.find?_cons, hNo2,
          List.find?_cons, hMatch]]
    rfl
  · have hNo2 : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 0] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
      rw [hSym']
      have h_ne : ([some 0] : List (Option Nat)) ≠ [some 2] := by decide
      simp [h_ne]
    have hNo3 : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
      rw [hSym']
      have h_ne : ([some 1] : List (Option Nat)) ≠ [some 2] := by decide
      simp [h_ne]
    have hMatch : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 2], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 2] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
          = some { src_state := 1, src_tape_vals := [some 2], dst_state := 2,
                   dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
      show List.find? _ (_ :: _ :: _ :: _ :: _) = _
      rw [List.find?_cons, hNo0, List.find?_cons, hNo0, List.find?_cons, hNo2,
          List.find?_cons, hNo3, List.find?_cons, hMatch]]
    rfl

/-- States `0`/`1` of `exactOneOneTM` are not halting. -/
private theorem Compile.exactOneOne_not_halting (tapes : List (List Nat × Nat × List Nat))
    (i : Nat) (hi : i ≤ 1) :
    haltingStateReached Compile.exactOneOneTM { state_idx := i, tapes := tapes } = false := by
  interval_cases i <;> rfl

/-- `exactOneOneTM` run, NEG via bit `0` first cell: 1 step. -/
private theorem Compile.exactOneOne_run_b0 (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 1) :
    runFlatTM 1 Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 2, tapes := [(left, head, right)] } := by
  show (if haltingStateReached Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.exactOneOneTM cfg') = _
  rw [show haltingStateReached Compile.exactOneOneTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.exactOneOne_step0_b0 left right head h hget]
  rfl

/-- `exactOneOneTM` run, two-cell read (`2` then `v ≤ 2`): 2 steps, head `+1`;
exit POS (`3`) iff the second cell is the block-end `0`. -/
private theorem Compile.exactOneOne_run_two (left right : List Nat) (head : Nat) (v : Nat)
    (hv : v ≤ 2) (h : head < right.length) (hget : right.get ⟨head, h⟩ = 2)
    (h1 : head + 1 < right.length) (hget1 : right.get ⟨head + 1, h1⟩ = v) :
    runFlatTM 2 Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := if v = 0 then 3 else 2,
               tapes := [(left, head + 1, right)] } := by
  show (if haltingStateReached Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 1 Compile.exactOneOneTM cfg') = _
  rw [show haltingStateReached Compile.exactOneOneTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.exactOneOne_step0_b1 left right head h hget]
  show (if haltingStateReached Compile.exactOneOneTM
            { state_idx := 1, tapes := [(left, head + 1, right)] } = true then _
        else match stepFlatTM Compile.exactOneOneTM
            { state_idx := 1, tapes := [(left, head + 1, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.exactOneOneTM cfg') = _
  rw [show haltingStateReached Compile.exactOneOneTM
        { state_idx := 1, tapes := [(left, head + 1, right)] } = false from rfl,
      Compile.exactOneOne_step1 left right (head + 1) v hv h1 hget1]
  rfl

/-- `exactOneOneTM` 1-step trajectory (avoids both exits, non-halting). -/
private theorem Compile.exactOneOne_traj_one (left right : List Nat) (head : Nat) :
    ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.exactOneOneTM
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ Compile.exactOneOneTM_exitPos ∧
      ck.state_idx ≠ Compile.exactOneOneTM_exitNeg ∧
      haltingStateReached Compile.exactOneOneTM ck = false := by
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  obtain rfl : ck = { state_idx := 0, tapes := [(left, head, right)] } :=
    (Option.some.inj hck).symm
  exact ⟨show (0 : Nat) ≠ 3 by omega, show (0 : Nat) ≠ 2 by omega, rfl⟩

/-- `exactOneOneTM` 2-step trajectory (avoids both exits, non-halting). -/
private theorem Compile.exactOneOne_traj_two (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 2) :
    ∀ k, k < 2 → ∀ ck,
      runFlatTM k Compile.exactOneOneTM
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ Compile.exactOneOneTM_exitPos ∧
      ck.state_idx ≠ Compile.exactOneOneTM_exitNeg ∧
      haltingStateReached Compile.exactOneOneTM ck = false := by
  intro k hk ck hck
  interval_cases k
  · obtain rfl : ck = { state_idx := 0, tapes := [(left, head, right)] } :=
      (Option.some.inj hck).symm
    exact ⟨show (0 : Nat) ≠ 3 by omega, show (0 : Nat) ≠ 2 by omega, rfl⟩
  · have hrun1 : runFlatTM 1 Compile.exactOneOneTM
        { state_idx := 0, tapes := [(left, head, right)] }
          = some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
      show (if haltingStateReached Compile.exactOneOneTM
                { state_idx := 0, tapes := [(left, head, right)] } = true then _
            else match stepFlatTM Compile.exactOneOneTM
                { state_idx := 0, tapes := [(left, head, right)] } with
              | none => _ | some cfg' => runFlatTM 0 Compile.exactOneOneTM cfg') = _
      rw [show haltingStateReached Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
          Compile.exactOneOne_step0_b1 left right head h hget]
      rfl
    rw [hrun1] at hck
    obtain rfl : ck = { state_idx := 1, tapes := [(left, head + 1, right)] } :=
      (Option.some.inj hck).symm
    exact ⟨show (1 : Nat) ≠ 3 by omega, show (1 : Nat) ≠ 2 by omega, rfl⟩

/-- The `testBitInnerTM` symbol bound at the branch seam: any read cell value
`< 4` is below the composed alphabet. -/
private theorem Compile.testBitInner_sym_bound (left rest : List Nat) (head : Nat)
    (hlt : head < (3 :: rest).length) (v0 : Nat) (hv0 : v0 < 4)
    (hget : (3 :: rest).get ⟨head, hlt⟩ = v0) :
    ∀ v, currentTapeSymbol (left, head, (3 : Nat) :: rest) = some v →
      v < max Compile.exactOneOneTM.sig
        (max ClearGadget.justRewindTM.sig ClearGadget.justRewindTM.sig) := by
  intro v hv
  rw [currentTapeSymbol_in_range hlt, hget] at hv
  obtain rfl : v0 = v := Option.some.inj hv
  calc v0 < 4 := hv0
    _ = Compile.exactOneOneTM.sig := Compile.exactOneOneTM_sig.symm
    _ ≤ _ := le_max_left _ _

/-- Inner tester, NEG via first bit `0` (cell `1`): rewinds and exits at
`testBitInner_exitNeg` in `1 + 1 + (head + 1)` steps, tape unchanged. -/
private theorem Compile.testBitInner_run_b0 (left rest : List Nat) (head : Nat)
    (hcell : (3 :: rest)[head]? = some 1)
    (hcells : ∀ i, i < head → ∃ (hh : i < rest.length),
      rest.get ⟨i, hh⟩ < 4 ∧ rest.get ⟨i, hh⟩ ≠ 3) :
    runFlatTM (1 + 1 + (head + 1)) Compile.testBitInnerTM
        { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
      = some { state_idx := Compile.testBitInner_exitNeg,
               tapes := [(left, 0, 3 :: rest)] }
    ∧ ∀ k, k < 1 + 1 + (head + 1) → ∀ ck,
        runFlatTM k Compile.testBitInnerTM
            { state_idx := 0, tapes := [(left, head, 3 :: rest)] } = some ck →
        ck.state_idx ≠ Compile.testBitInner_exitPos ∧
        ck.state_idx ≠ Compile.testBitInner_exitNeg ∧
        haltingStateReached Compile.testBitInnerTM ck = false := by
  have hlt : head < (3 :: rest).length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hcell
    exact absurd hcell (by simp)
  have hget : (3 :: rest).get ⟨head, hlt⟩ = 1 := by
    rw [List.get_eq_getElem]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hcell)
  have hle : head ≤ rest.length := by
    simp only [List.length_cons] at hlt; omega
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
  have hrun1 := Compile.exactOneOne_run_b0 left (3 :: rest) head hlt hget
  have htraj1 := Compile.exactOneOne_traj_one left (3 :: rest) head
  have hrew := ScanLeft.rewindToStart_run 4 3 left rest head hle hcells
  have hrew_traj := ScanLeft.rewindToStart_traj 4 3 left rest head hle hcells
  have hsym := Compile.testBitInner_sym_bound left rest head hlt 1 (by omega) hget
  have hneg := branchComposeFlatTM_run_neg (by decide)
    Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
    ClearGadget.justRewindTM_valid (by decide) (by decide)
    cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left head (3 :: rest) hsym hrun1 htraj1 hrew
    (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
  have hneg_traj := branchComposeFlatTM_no_early_halt_neg (by decide)
    Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
    ClearGadget.justRewindTM_valid (by decide) (by decide)
    cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left head (3 :: rest) hsym hrun1 htraj1
    (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
  refine ⟨hneg.1, ?_⟩
  intro k hk ck hck
  have hh := hneg_traj k hk ck hck
  exact ⟨ClearGadget.ne_of_not_halting Compile.testBitInner_exitPos_is_halt hh,
         ClearGadget.ne_of_not_halting Compile.testBitInner_exitNeg_is_halt hh, hh⟩

/-- Inner tester, two-cell read (`2` then `v`): POS (`v = 0`, register `= [1]`)
or NEG (`v ∈ {1,2}`), rewinding from `head + 1`; `2 + 1 + (head + 1 + 1)` steps. -/
private theorem Compile.testBitInner_run_two (left rest : List Nat) (head : Nat) (v : Nat)
    (hv : v ≤ 2)
    (hcell : (3 :: rest)[head]? = some 2)
    (hcell1 : (3 :: rest)[head + 1]? = some v)
    (hcells : ∀ i, i < head + 1 → ∃ (hh : i < rest.length),
      rest.get ⟨i, hh⟩ < 4 ∧ rest.get ⟨i, hh⟩ ≠ 3) :
    runFlatTM (2 + 1 + (head + 1 + 1)) Compile.testBitInnerTM
        { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
      = some { state_idx := if v = 0 then Compile.testBitInner_exitPos
                            else Compile.testBitInner_exitNeg,
               tapes := [(left, 0, 3 :: rest)] }
    ∧ ∀ k, k < 2 + 1 + (head + 1 + 1) → ∀ ck,
        runFlatTM k Compile.testBitInnerTM
            { state_idx := 0, tapes := [(left, head, 3 :: rest)] } = some ck →
        ck.state_idx ≠ Compile.testBitInner_exitPos ∧
        ck.state_idx ≠ Compile.testBitInner_exitNeg ∧
        haltingStateReached Compile.testBitInnerTM ck = false := by
  have hlt1 : head + 1 < (3 :: rest).length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hcell1
    exact absurd hcell1 (by simp)
  have hlt : head < (3 :: rest).length := by omega
  have hget : (3 :: rest).get ⟨head, hlt⟩ = 2 := by
    rw [List.get_eq_getElem]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hcell)
  have hget1 : (3 :: rest).get ⟨head + 1, hlt1⟩ = v := by
    rw [List.get_eq_getElem]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt1).symm.trans hcell1)
  have hle1 : head + 1 ≤ rest.length := by
    simp only [List.length_cons] at hlt1; omega
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
  have hrun1 := Compile.exactOneOne_run_two left (3 :: rest) head v hv hlt hget hlt1 hget1
  have htraj1 := Compile.exactOneOne_traj_two left (3 :: rest) head hlt hget
  have hrew := ScanLeft.rewindToStart_run 4 3 left rest (head + 1) hle1 hcells
  have hrew_traj := ScanLeft.rewindToStart_traj 4 3 left rest (head + 1) hle1 hcells
  have hsym := Compile.testBitInner_sym_bound left rest (head + 1) hlt1 v (by omega) hget1
  by_cases hv0 : v = 0
  · subst hv0
    rw [if_pos rfl] at hrun1 ⊢
    have hpos := branchComposeFlatTM_run_pos (by decide)
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1 hrew
      (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1
      (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
    refine ⟨hpos.1, ?_⟩
    intro k hk ck hck
    have hh := hpos_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting Compile.testBitInner_exitPos_is_halt hh,
           ClearGadget.ne_of_not_halting Compile.testBitInner_exitNeg_is_halt hh, hh⟩
  · rw [if_neg hv0] at hrun1 ⊢
    have hneg := branchComposeFlatTM_run_neg (by decide)
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1 hrew
      (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg (by decide)
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1
      (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
    refine ⟨hneg.1, ?_⟩
    intro k hk ck hck
    have hh := hneg_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting Compile.testBitInner_exitPos_is_halt hh,
           ClearGadget.ne_of_not_halting Compile.testBitInner_exitNeg_is_halt hh, hh⟩

/-- Interior-cell facts for the tester rewinds: with `encodeTape s ++ res
= 3 :: rest` and `bound + 1 < |encodeTape s|`, every `rest` cell below `bound`
is in range, `< 4` and sentinel-free (it lies strictly inside the encoded
region, left of the trailing terminator). -/
private theorem Compile.testBit_rewind_cells (s : State) (res : List Nat)
    (hbit : Compile.BitState s) (rest : List Nat)
    (hrest : Compile.encodeTape s ++ res = 3 :: rest) (bound : Nat)
    (hbound : bound + 1 < (Compile.encodeTape s).length) :
    ∀ i, i < bound → ∃ (hh : i < rest.length),
      rest.get ⟨i, hh⟩ < 4 ∧ rest.get ⟨i, hh⟩ ≠ 3 := by
  intro i hi
  have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
    have h := congrArg List.length hrest
    simp only [List.length_append, List.length_cons] at h
    omega
  have hh : i < rest.length := by omega
  refine ⟨hh, ?_⟩
  have hi1lt : i + 1 < (Compile.encodeTape s).length := by omega
  have hgetE : rest.get ⟨i, hh⟩ = (Compile.encodeTape s).get ⟨i + 1, hi1lt⟩ := by
    have h1 : (3 :: rest)[i + 1]? = some (rest.get ⟨i, hh⟩) := by
      rw [List.getElem?_cons_succ, List.getElem?_eq_getElem hh, List.get_eq_getElem]
    have h2 : (Compile.encodeTape s ++ res)[i + 1]?
        = some ((Compile.encodeTape s).get ⟨i + 1, hi1lt⟩) := by
      rw [List.getElem?_append_left hi1lt, List.getElem?_eq_getElem hi1lt,
          List.get_eq_getElem]
    rw [hrest] at h2
    exact Option.some.inj (h1.symm.trans h2)
  constructor
  · rw [hgetE]
    exact Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _)
  · rw [hgetE]
    obtain ⟨hi', hne⟩ :=
      Compile.encodeTape_interior_ne_endMark s hbit (i + 1) (by omega) (by omega)
    exact hne

/-- The head-`0` seam symbol of the joined tester is the leading sentinel `3`,
below the raw tester's alphabet. -/
private theorem Compile.testBitRaw_seam_sym (t : Var) (s : State) (res rest : List Nat)
    (hrest : Compile.encodeTape s ++ res = 3 :: rest) :
    ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < (Compile.testBitRawTM t).sig := by
  intro v hv
  rw [hrest] at hv
  rw [show currentTapeSymbol (([] : List Nat), 0, (3 : Nat) :: rest) = some 3 from rfl] at hv
  obtain rfl : (3 : Nat) = v := Option.some.inj hv
  rw [Compile.testBitRawTM_sig]
  omega

/-- **Tester contract — positive (`s.get t = [1]`).** `compileTestBit t` reaches
`exitPos` with the head back at `0` and the tape **unchanged**, visiting neither
exit nor any halt state before; within `3·L + 12` steps. -/
theorem Compile.testBitReg_run_pos (t : Var) (s : State) (res : List Nat)
    (ht : t < s.length) (hbit : Compile.BitState s) (hpos : s.get t = [1]) :
    ∃ T, runFlatTM T (compileTestBit t).M
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := (compileTestBit t).exitPos,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < T → ∀ ck,
        runFlatTM k (compileTestBit t).M
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ (compileTestBit t).exitPos ∧
        ck.state_idx ≠ (compileTestBit t).exitNeg ∧
        haltingStateReached (compileTestBit t).M ck = false)
    ∧ T ≤ 3 * (Compile.encodeTape s ++ res).length + 12 := by
  set skipped := (s.take t).map Compile.shiftReg with hsk
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set tail2 := Compile.encodeRegs (s.drop (t + 1)) ++ [Compile.endMark] ++ res with htail2
  set rest := AppendGadget.regBlocks skipped ++ 2 :: 0 :: tail2 with hrest_def
  have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
    have hsplit := Compile.encodeTape_split s t ht
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get t) = [2] := by rw [hpos]; rfl
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htail2]
    simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
  -- cell facts at H and H + 1.
  have hcell : (3 :: rest)[H]? = some 2 := by
    rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
          = (AppendGadget.regBlocks skipped).length + 1 from by omega,
        List.getElem?_cons_succ, hrest_def,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hcell1 : (3 :: rest)[H + 1]? = some 0 := by
    rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length + 1
          = ((AppendGadget.regBlocks skipped).length + 1) + 1 from by omega,
        List.getElem?_cons_succ, hrest_def,
        List.getElem?_append_right (Nat.le_succ_of_le (Nat.le_refl _)),
        show (AppendGadget.regBlocks skipped).length + 1
          - (AppendGadget.regBlocks skipped).length = 1 from by omega]
    rfl
  -- length bookkeeping.
  have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
    have h := congrArg List.length hdecomp
    simp only [List.length_append, List.length_cons] at h
    omega
  have hrest_len : rest.length
      = (AppendGadget.regBlocks skipped).length + 2 + tail2.length := by
    rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
  have htail2_len : tail2.length
      = (Compile.encodeRegs (s.drop (t + 1))).length + 1 + res.length := by
    rw [htail2]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hbound : H + 2 < (Compile.encodeTape s).length := by omega
  have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp (H + 1) (by omega)
  -- inner tester run (POS: cell 2 then block-end 0).
  have hinner := Compile.testBitInner_run_two [] rest H 0 (by omega) hcell hcell1 hcells
  rw [if_pos rfl] at hinner
  rw [← hdecomp] at hinner
  -- navtest run + trajectory.
  have hne_t : s.get t ≠ [] := by rw [hpos]; simp
  have hnav_run := Compile.navTestReg_run_content s t res ht hbit hne_t
  have hnav_traj := Compile.navTestReg_traj_content s t res ht hbit hne_t
  rw [← hsk, ← hHdef] at hnav_run
  rw [← hsk] at hnav_traj
  -- the outer branch composition.
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content t
      ≠ ClearGadget.navigateAndTestTM_exit_delim t := by
    show (ClearGadget.navigateToRegTM t).states + 1 ≠ (ClearGadget.navigateToRegTM t).states + 2
    omega
  have hHlt : H < (Compile.encodeTape s ++ res).length := by
    rw [hdecomp]; simp only [List.length_cons]; omega
  have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 2 := by
    rw [List.get_eq_getElem]
    have h2 : (Compile.encodeTape s ++ res)[H]? = some 2 := by rw [hdecomp]; exact hcell
    exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
  have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
      v < max (ClearGadget.navigateAndTestTM t).sig
        (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    obtain rfl : (2 : Nat) = v := Option.some.inj hv
    calc (2 : Nat) < 4 := by omega
      _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
      _ ≤ _ := le_max_left _ _
  have hpos' := branchComposeFlatTM_run_pos hexit_neq
    (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt t)
    (ClearGadget.navigateAndTestTM_exit_delim_lt t)
    cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
      rw [ClearGadget.navigateAndTestTM_states]; omega)
    [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hinner.1
    (Compile.haltingStateReached_of_halt Compile.testBitInner_exitPos_is_halt)
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt t)
    (ClearGadget.navigateAndTestTM_exit_delim_lt t)
    cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
      rw [ClearGadget.navigateAndTestTM_states]; omega)
    [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
    (fun k' hk' ck' hck' => (hinner.2 k' hk' ck' hck').2.2)
  have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
      Compile.testBitInnerTM ClearGadget.justRewindTM
      (ClearGadget.navigateAndTestTM_exit_content t)
      (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
  have hstate_eq : Compile.testBitInner_exitPos + (ClearGadget.navigateAndTestTM t).states
      = Compile.testBitRaw_exitPos t := by
    rw [Compile.testBitRaw_exitPos]; omega
  rw [hstate_eq, hraweq] at hpos'
  rw [hraweq] at hpos_traj
  -- join transport: the run never visits the demoted delim leaf.
  set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (2 + 1 + (H + 1 + 1)) with hTdef
  have hne12 : ∀ k, k ≤ T → ∀ ck, runFlatTM k (Compile.testBitRawTM t) cfg0 = some ck →
      ck.state_idx ≠ Compile.testBitRaw_exitNegDelim t := by
    intro k hk ck hck
    rcases Nat.lt_or_ge k T with hlt | hge
    · exact ClearGadget.ne_of_not_halting (Compile.testBitRaw_exitNegDelim_is_halt t)
        (hpos_traj k hlt ck hck)
    · have hkT : k = T := by omega
      subst hkT
      rw [hpos'.1] at hck
      obtain rfl := (Option.some.inj hck).symm
      show Compile.testBitRaw_exitPos t ≠ Compile.testBitRaw_exitNegDelim t
      rw [Compile.testBitRaw_exitPos, Compile.testBitRaw_exitNegDelim,
          Compile.testBitInnerTM_states]
      have h5 : Compile.testBitInner_exitPos = 5 := rfl
      have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
      omega
  refine ⟨T, ?_, ?_, ?_⟩
  · show runFlatTM T (Compile.joinTwoHalts (Compile.testBitRawTM t)
        (Compile.testBitRaw_exitNeg t) (Compile.testBitRaw_exitNegDelim t)) cfg0 = _
    rw [Compile.joinTwoHalts_run_eq _ _ _ T cfg0 hne12]
    exact hpos'.1
  · intro k hk ck hck
    have hck' : runFlatTM k (Compile.testBitRawTM t) cfg0 = some ck := by
      rw [← Compile.joinTwoHalts_run_eq (Compile.testBitRawTM t)
          (Compile.testBitRaw_exitNeg t) (Compile.testBitRaw_exitNegDelim t) k cfg0
          (fun j hj cj hcj => hne12 j (by omega) cj hcj)]
      exact hck
    have hnh := hpos_traj k hk ck hck'
    exact ⟨ClearGadget.ne_of_not_halting (Compile.testBitRaw_exitPos_is_halt t) hnh,
           ClearGadget.ne_of_not_halting (Compile.testBitRaw_exitNeg_is_halt t) hnh,
           Compile.joinTwoHalts_halting_false _ _ _ ck hnh⟩
  · have hnavle := ClearGadget.navSteps_le skipped
    have hLlen : (Compile.encodeTape s).length ≤ (Compile.encodeTape s ++ res).length := by
      rw [List.length_append]; omega
    omega

/-- Join transport for runs ending at the raw tester's kept NEG exit (`h1`):
the joined tester reproduces the run; the trajectory avoids both exits. -/
private theorem Compile.testBit_join_kept_neg (t : Var) (cfg0 : FlatTMConfig)
    (tape : List Nat) (T : Nat)
    (hraw : runFlatTM T (Compile.testBitRawTM t) cfg0
      = some { state_idx := Compile.testBitRaw_exitNeg t, tapes := [([], 0, tape)] })
    (htraj : ∀ k, k < T → ∀ ck, runFlatTM k (Compile.testBitRawTM t) cfg0 = some ck →
      haltingStateReached (Compile.testBitRawTM t) ck = false) :
    runFlatTM T (compileTestBit t).M cfg0
      = some { state_idx := (compileTestBit t).exitNeg, tapes := [([], 0, tape)] }
    ∧ (∀ k, k < T → ∀ ck, runFlatTM k (compileTestBit t).M cfg0 = some ck →
        ck.state_idx ≠ (compileTestBit t).exitPos ∧
        ck.state_idx ≠ (compileTestBit t).exitNeg ∧
        haltingStateReached (compileTestBit t).M ck = false) := by
  obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept
    (Compile.testBitRawTM t) (Compile.testBitRaw_exitNeg t)
    (Compile.testBitRaw_exitNegDelim t) cfg0 T ([], 0, tape) hraw htraj
    (Compile.testBitRaw_exitNeg_is_halt t) (Compile.testBitRaw_exitNegDelim_is_halt t)
  refine ⟨hjoin, ?_⟩
  intro k hk ck hck
  obtain ⟨hne1, hnh⟩ := hjoin_traj k hk ck hck
  exact ⟨ClearGadget.ne_of_not_halting (compileTestBit_exitPos_is_halt t) hnh, hne1, hnh⟩

/-- **Tester contract — negative (`s.get t ≠ [1]`).** `compileTestBit t` reaches
`exitNeg` with the head back at `0` and the tape **unchanged**, visiting neither
exit nor any halt state before; within `3·L + 12` steps. Three internal cases:
register empty (delim leaf), first bit `0`, or `≥ 2` bits. -/
theorem Compile.testBitReg_run_neg (t : Var) (s : State) (res : List Nat)
    (ht : t < s.length) (hbit : Compile.BitState s) (hneg : s.get t ≠ [1]) :
    ∃ T, runFlatTM T (compileTestBit t).M
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := (compileTestBit t).exitNeg,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < T → ∀ ck,
        runFlatTM k (compileTestBit t).M
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ (compileTestBit t).exitPos ∧
        ck.state_idx ≠ (compileTestBit t).exitNeg ∧
        haltingStateReached (compileTestBit t).M ck = false)
    ∧ T ≤ 3 * (Compile.encodeTape s ++ res).length + 12 := by
  set skipped := (s.take t).map Compile.shiftReg with hsk
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set tail2 := Compile.encodeRegs (s.drop (t + 1)) ++ [Compile.endMark] ++ res with htail2
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have htail2_len : tail2.length
      = (Compile.encodeRegs (s.drop (t + 1))).length + 1 + res.length := by
    rw [htail2]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content t
      ≠ ClearGadget.navigateAndTestTM_exit_delim t := by
    show (ClearGadget.navigateToRegTM t).states + 1 ≠ (ClearGadget.navigateToRegTM t).states + 2
    omega
  have hnavle := ClearGadget.navSteps_le skipped
  have hLlen : (Compile.encodeTape s).length ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append]; omega
  rcases hsgt : s.get t with _ | ⟨b, r⟩
  · -- Case A: register empty — the delim leaf (demoted), bridged to exitNeg.
    set rest := AppendGadget.regBlocks skipped ++ 0 :: tail2 with hrest_def
    have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
      have hsplit := Compile.encodeTape_split s t ht
      rw [← hsk] at hsplit
      have hsr : Compile.shiftReg (s.get t) = [] := by rw [hsgt]; rfl
      rw [hsr, List.append_nil] at hsplit
      rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htail2]
      simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
    have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
      have h := congrArg List.length hdecomp
      simp only [List.length_append, List.length_cons] at h
      omega
    have hrest_len : rest.length
        = (AppendGadget.regBlocks skipped).length + 1 + tail2.length := by
      rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
    have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp H (by omega)
    have hHle : H ≤ rest.length := by omega
    have hrew := ScanLeft.rewindToStart_run 4 3 [] rest H hHle hcells
    have hrew_traj := ScanLeft.rewindToStart_traj 4 3 [] rest H hHle hcells
    rw [← hdecomp] at hrew hrew_traj
    have hnav_run := Compile.navTestReg_run_delim s t res ht hbit hsgt
    have hnav_traj := Compile.navTestReg_traj_delim s t res ht hbit hsgt
    rw [← hsk, ← hHdef] at hnav_run
    rw [← hsk] at hnav_traj
    have hHlt : H < (Compile.encodeTape s ++ res).length := by
      rw [hdecomp]; simp only [List.length_cons]; omega
    have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 0 := by
      rw [List.get_eq_getElem]
      have h2 : (Compile.encodeTape s ++ res)[H]? = some 0 := by
        rw [hdecomp, hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
              = (AppendGadget.regBlocks skipped).length + 1 from by omega,
            List.getElem?_cons_succ, hrest_def,
            List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
    have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
        v < max (ClearGadget.navigateAndTestTM t).sig
          (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
      intro v hv
      rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
      obtain rfl : (0 : Nat) = v := Option.some.inj hv
      calc (0 : Nat) < 4 := by omega
        _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
        _ ≤ _ := le_max_left _ _
    have hneg' := branchComposeFlatTM_run_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt t)
      (ClearGadget.navigateAndTestTM_exit_delim_lt t)
      cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
        rw [ClearGadget.navigateAndTestTM_states]; omega)
      [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hrew
      (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt t)
      (ClearGadget.navigateAndTestTM_exit_delim_lt t)
      cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
        rw [ClearGadget.navigateAndTestTM_states]; omega)
      [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
      (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
    have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
        Compile.testBitInnerTM ClearGadget.justRewindTM
        (ClearGadget.navigateAndTestTM_exit_content t)
        (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
    have hstate_eq : (1 : Nat) + ((ClearGadget.navigateAndTestTM t).states
          + Compile.testBitInnerTM.states) = Compile.testBitRaw_exitNegDelim t := by
      rw [Compile.testBitRaw_exitNegDelim]
      have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
      omega
    rw [hstate_eq, hraweq] at hneg'
    rw [hraweq] at hneg_traj
    set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (H + 1) with hTdef
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted
      (Compile.testBitRawTM t) (Compile.testBitRaw_exitNeg t)
      (Compile.testBitRaw_exitNegDelim t) cfg0 T [] (Compile.encodeTape s ++ res) 0
      hneg'.1 (fun k hk ck hck => hneg_traj k hk ck hck)
      (Compile.testBitRaw_exitNeg_is_halt t) (Compile.testBitRaw_exitNegDelim_is_halt t)
      (by rw [Compile.testBitRaw_exitNeg, Compile.testBitRaw_exitNegDelim,
              Compile.testBitInnerTM_states]
          have h8 : Compile.testBitInner_exitNeg = 8 := rfl
          have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
          omega)
      (Compile.testBitRaw_seam_sym t s res rest hdecomp)
    refine ⟨T + 1, hjoin, ?_, ?_⟩
    · intro k hk ck hck
      obtain ⟨hne1, hnh⟩ := hjoin_traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting (compileTestBit_exitPos_is_halt t) hnh, hne1, hnh⟩
    · omega
  · -- register nonempty: first bit `b ≤ 1`.
    have hb1 : b ≤ 1 := by
      have hmem : s.get t ∈ s := by
        rw [State.get, List.getElem?_eq_getElem ht]; exact List.getElem_mem ht
      exact hbit _ hmem b (by simp [hsgt])
    have hne_t : s.get t ≠ [] := by rw [hsgt]; simp
    have hnav_run := Compile.navTestReg_run_content s t res ht hbit hne_t
    have hnav_traj := Compile.navTestReg_traj_content s t res ht hbit hne_t
    rw [← hsk, ← hHdef] at hnav_run
    rw [← hsk] at hnav_traj
    rcases hb : b with _ | b'
    · -- Case B: first bit `0` — NEG after one read.
      subst hb
      set tailp := Compile.shiftReg r ++ 0 :: tail2 with htailp
      set rest := AppendGadget.regBlocks skipped ++ 1 :: tailp with hrest_def
      have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
        have hsplit := Compile.encodeTape_split s t ht
        rw [← hsk] at hsplit
        have hsr : Compile.shiftReg (s.get t) = 1 :: Compile.shiftReg r := by
          rw [hsgt]; rfl
        rw [hsr] at hsplit
        rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htailp, htail2]
        simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
      have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
        have h := congrArg List.length hdecomp
        simp only [List.length_append, List.length_cons] at h
        omega
      have hrest_len : rest.length
          = (AppendGadget.regBlocks skipped).length + 1 + tailp.length := by
        rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
      have htailp_len : tailp.length = r.length + 1 + tail2.length := by
        rw [htailp]
        simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map]
        omega
      have hcell : (3 :: rest)[H]? = some 1 := by
        rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
              = (AppendGadget.regBlocks skipped).length + 1 from by omega,
            List.getElem?_cons_succ, hrest_def,
            List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp H (by omega)
      have hinner := Compile.testBitInner_run_b0 [] rest H hcell hcells
      rw [← hdecomp] at hinner
      have hHlt : H < (Compile.encodeTape s ++ res).length := by
        rw [hdecomp]; simp only [List.length_cons]; omega
      have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 1 := by
        rw [List.get_eq_getElem]
        have h2 : (Compile.encodeTape s ++ res)[H]? = some 1 := by rw [hdecomp]; exact hcell
        exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
      have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
          v < max (ClearGadget.navigateAndTestTM t).sig
            (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
        intro v hv
        rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
        obtain rfl : (1 : Nat) = v := Option.some.inj hv
        calc (1 : Nat) < 4 := by omega
          _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
          _ ≤ _ := le_max_left _ _
      have hpos' := branchComposeFlatTM_run_pos hexit_neq
        (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
        ClearGadget.justRewindTM_valid
        (ClearGadget.navigateAndTestTM_exit_content_lt t)
        (ClearGadget.navigateAndTestTM_exit_delim_lt t)
        cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
          rw [ClearGadget.navigateAndTestTM_states]; omega)
        [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hinner.1
        (Compile.haltingStateReached_of_halt Compile.testBitInner_exitNeg_is_halt)
      have hpos_traj := branchComposeFlatTM_no_early_halt_pos
        (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
        ClearGadget.justRewindTM_valid
        (ClearGadget.navigateAndTestTM_exit_content_lt t)
        (ClearGadget.navigateAndTestTM_exit_delim_lt t)
        cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
          rw [ClearGadget.navigateAndTestTM_states]; omega)
        [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
        (fun k' hk' ck' hck' => (hinner.2 k' hk' ck' hck').2.2)
      have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
          Compile.testBitInnerTM ClearGadget.justRewindTM
          (ClearGadget.navigateAndTestTM_exit_content t)
          (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
      have hstate_eq : Compile.testBitInner_exitNeg + (ClearGadget.navigateAndTestTM t).states
          = Compile.testBitRaw_exitNeg t := by
        rw [Compile.testBitRaw_exitNeg]; omega
      rw [hstate_eq, hraweq] at hpos'
      rw [hraweq] at hpos_traj
      set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (1 + 1 + (H + 1)) with hTdef
      obtain ⟨hjoin, hjoin_traj⟩ := Compile.testBit_join_kept_neg t cfg0
        (Compile.encodeTape s ++ res) T hpos'.1
        (fun k hk ck hck => hpos_traj k hk ck hck)
      exact ⟨T, hjoin, hjoin_traj, by omega⟩
    · -- Case C: first bit `1` and a second cell — NEG after two reads.
      subst hb
      rcases r with _ | ⟨c, r'⟩
      · -- register is exactly `[1]` — contradicts `hneg`.
        exfalso
        have hb'0 : b' = 0 := by omega
        subst hb'0
        exact hneg hsgt
      · have hb'0 : b' = 0 := by omega
        subst hb'0
        have hc1 : c ≤ 1 := by
          have hmem : s.get t ∈ s := by
            rw [State.get, List.getElem?_eq_getElem ht]; exact List.getElem_mem ht
          exact hbit _ hmem c (by simp [hsgt])
        set tailpp := Compile.shiftReg r' ++ 0 :: tail2 with htailpp
        set rest := AppendGadget.regBlocks skipped ++ 2 :: (c + 1) :: tailpp with hrest_def
        have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
          have hsplit := Compile.encodeTape_split s t ht
          rw [← hsk] at hsplit
          have hsr : Compile.shiftReg (s.get t) = 2 :: (c + 1) :: Compile.shiftReg r' := by
            rw [hsgt]; rfl
          rw [hsr] at hsplit
          rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htailpp, htail2]
          simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
        have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
          have h := congrArg List.length hdecomp
          simp only [List.length_append, List.length_cons] at h
          omega
        have hrest_len : rest.length
            = (AppendGadget.regBlocks skipped).length + 2 + tailpp.length := by
          rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
        have htailpp_len : tailpp.length = r'.length + 1 + tail2.length := by
          rw [htailpp]
          simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map]
          omega
        have hcell : (3 :: rest)[H]? = some 2 := by
          rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
                = (AppendGadget.regBlocks skipped).length + 1 from by omega,
              List.getElem?_cons_succ, hrest_def,
              List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        have hcell1 : (3 :: rest)[H + 1]? = some (c + 1) := by
          rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length + 1
                = ((AppendGadget.regBlocks skipped).length + 1) + 1 from by omega,
              List.getElem?_cons_succ, hrest_def,
              List.getElem?_append_right (Nat.le_succ_of_le (Nat.le_refl _)),
              show (AppendGadget.regBlocks skipped).length + 1
                - (AppendGadget.regBlocks skipped).length = 1 from by omega]
          rfl
        have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp (H + 1) (by omega)
        have hinner := Compile.testBitInner_run_two [] rest H (c + 1) (by omega)
          hcell hcell1 hcells
        rw [if_neg (by omega)] at hinner
        rw [← hdecomp] at hinner
        have hHlt : H < (Compile.encodeTape s ++ res).length := by
          rw [hdecomp]; simp only [List.length_cons]; omega
        have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 2 := by
          rw [List.get_eq_getElem]
          have h2 : (Compile.encodeTape s ++ res)[H]? = some 2 := by rw [hdecomp]; exact hcell
          exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
        have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
            v < max (ClearGadget.navigateAndTestTM t).sig
              (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
          intro v hv
          rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
          obtain rfl : (2 : Nat) = v := Option.some.inj hv
          calc (2 : Nat) < 4 := by omega
            _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
            _ ≤ _ := le_max_left _ _
        have hpos' := branchComposeFlatTM_run_pos hexit_neq
          (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
          ClearGadget.justRewindTM_valid
          (ClearGadget.navigateAndTestTM_exit_content_lt t)
          (ClearGadget.navigateAndTestTM_exit_delim_lt t)
          cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
            rw [ClearGadget.navigateAndTestTM_states]; omega)
          [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hinner.1
          (Compile.haltingStateReached_of_halt Compile.testBitInner_exitNeg_is_halt)
        have hpos_traj := branchComposeFlatTM_no_early_halt_pos
          (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
          ClearGadget.justRewindTM_valid
          (ClearGadget.navigateAndTestTM_exit_content_lt t)
          (ClearGadget.navigateAndTestTM_exit_delim_lt t)
          cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
            rw [ClearGadget.navigateAndTestTM_states]; omega)
          [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
          (fun k' hk' ck' hck' => (hinner.2 k' hk' ck' hck').2.2)
        have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
            Compile.testBitInnerTM ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content t)
            (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
        have hstate_eq : Compile.testBitInner_exitNeg + (ClearGadget.navigateAndTestTM t).states
            = Compile.testBitRaw_exitNeg t := by
          rw [Compile.testBitRaw_exitNeg]; omega
        rw [hstate_eq, hraweq] at hpos'
        rw [hraweq] at hpos_traj
        set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (2 + 1 + (H + 1 + 1)) with hTdef
        obtain ⟨hjoin, hjoin_traj⟩ := Compile.testBit_join_kept_neg t cfg0
          (Compile.encodeTape s ++ res) T hpos'.1
          (fun k hk ck hck => hpos_traj k hk ck hck)
        exact ⟨T, hjoin, hjoin_traj, by omega⟩

theorem Compile.moveContentExit0_lt (dst : Nat) :
    Compile.moveContentExit0 dst < (Compile.moveContentRawTM dst).states := by
  rw [Compile.moveContentExit0, Compile.moveContentRawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM2_exit_lt 0 dst; omega

theorem Compile.moveContentExit1_lt (dst : Nat) :
    Compile.moveContentExit1 dst < (Compile.moveContentRawTM dst).states := by
  rw [Compile.moveContentExit1, Compile.moveContentRawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM2_exit_lt 1 dst; omega

theorem Compile.moveContentTM_valid (dst : Nat) : validFlatTM (Compile.moveContentTM dst) :=
  joinTwoHalts_valid _ _ _ (Compile.moveContentRawTM_valid dst)
    (Compile.moveContentExit0_lt dst) (Compile.moveContentExit1_lt dst)
    (Compile.moveContentRawTM_tapes dst)

theorem Compile.moveContentTM_sig (dst : Nat) : (Compile.moveContentTM dst).sig = 4 := by
  rw [Compile.moveContentTM, joinTwoHalts_sig]; exact Compile.moveContentRawTM_sig dst

theorem Compile.moveContentTM_exit0_is_halt (dst : Nat) :
    (Compile.moveContentTM dst).halt[Compile.moveContentExit0 dst]? = some true :=
  joinTwoHalts_h1_is_halt _ _ _ (Compile.moveContentExit0_ne_exit1 dst)
    (Compile.moveContentExit0_is_halt dst)

theorem Compile.moveContentExit0_lt_states (dst : Nat) :
    Compile.moveContentExit0 dst < (Compile.moveContentTM dst).states := by
  rw [Compile.moveContentTM, joinTwoHalts_states]; exact Compile.moveContentExit0_lt dst

theorem Compile.moveBodyRawTM_valid (src dst : Nat) : validFlatTM (Compile.moveBodyRawTM src dst) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.navigateAndTestTM_valid src)
    (Compile.moveContentTM_valid dst) ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    (ClearGadget.navigateAndTestTM_tapes src) (Compile.moveContentTM_tapes dst)
    ClearGadget.justRewindTM_tapes

theorem Compile.moveBodyRawTM_exitLoop_is_halt (src dst : Nat) :
    (Compile.moveBodyRawTM src dst).halt[Compile.moveBodyRawTM_exitLoop src dst]? = some true := by
  rw [Compile.moveBodyRawTM_exitLoop, Compile.moveBodyRawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveContentTM_valid dst) (Compile.moveContentExit0_lt_states dst)
    (Compile.moveContentTM_exit0_is_halt dst)

theorem Compile.moveBodyRawTM_exitDone_is_halt (src dst : Nat) :
    (Compile.moveBodyRawTM src dst).halt[Compile.moveBodyRawTM_exitDone src dst]? = some true := by
  rw [Compile.moveBodyRawTM_exitDone, Compile.moveBodyRawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveContentTM_valid dst)
    (show ClearGadget.justRewindTM.halt[ClearGadget.justRewindTM_exit]? = some true from rfl)

theorem Compile.moveBodyRawTM_exitLoop_lt (src dst : Nat) :
    Compile.moveBodyRawTM_exitLoop src dst < (Compile.moveBodyRawTM src dst).states := by
  rw [Compile.moveBodyRawTM_exitLoop, Compile.moveBodyRawTM, branchComposeFlatTM_states]
  have := Compile.moveContentExit0_lt_states dst; omega

theorem Compile.moveBodyRawTM_exitDone_lt (src dst : Nat) :
    Compile.moveBodyRawTM_exitDone src dst < (Compile.moveBodyRawTM src dst).states := by
  rw [Compile.moveBodyRawTM_exitDone, Compile.moveBodyRawTM, branchComposeFlatTM_states]
  show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
      + ClearGadget.justRewindTM_exit
    < (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
      + ClearGadget.justRewindTM.states
  show _ + _ + 1 < _ + _ + 3; omega

theorem Compile.moveBodyRawTM_exitDone_ne_exitLoop (src dst : Nat) :
    Compile.moveBodyRawTM_exitDone src dst ≠ Compile.moveBodyRawTM_exitLoop src dst := by
  rw [Compile.moveBodyRawTM_exitDone, Compile.moveBodyRawTM_exitLoop]
  have := Compile.moveContentExit0_lt_states dst; omega

/-- **Validity of `moveRegionTM`.** Mirrors `clearRegionTM_valid`: a `loopTM` over
the valid `moveBodyRawTM` body with both exits in range and single-tape. Needed to
wire `moveRegionTM` into `composeFlatTM`/`branchComposeFlatTM` when assembling the
cross-register ops. -/
theorem Compile.moveRegionTM_valid (src dst : Nat) :
    validFlatTM (Compile.moveRegionTM src dst) :=
  loopTM_valid (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)
    (Compile.moveBodyRawTM_valid src dst)
    (Compile.moveBodyRawTM_exitDone_lt src dst) (Compile.moveBodyRawTM_exitLoop_lt src dst)
    (Compile.moveBodyRawTM_tapes src dst)

/-- The compiled-machine alphabet of `moveRegionTM` is the fixed `sig = 4`. -/
theorem Compile.moveRegionTM_sig (src dst : Nat) : (Compile.moveRegionTM src dst).sig = 4 := by
  rw [Compile.moveRegionTM, loopTM_sig]
  show (Compile.moveBodyRawTM src dst).sig = 4
  show (branchComposeFlatTM _ _ _ _ _).sig = 4
  rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig]
  show max 4 (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) = 4
  rw [Compile.moveContentTM_sig dst]
  rfl

/-! ### The dual-target *duplicating* move gadget `moveRegion2TM` (Risk C2)

`moveRegion2TM src dst1 dst2` transfers `src`'s content (FIFO, one bit/iter) to the
**end of BOTH** `dst1` and `dst2`, emptying `src`. It is the duplicating primitive
the `copy`/`tail`/`concat` ops need — a single-target move (`moveRegionTM`) cannot
duplicate data (the number of copies is invariant). The structure mirrors
`moveRegionTM` exactly; the content branch appends the read bit to **two** registers
instead of one (`moveBitM3TM = moveBitM2TM b dst1 ⨾ appendAtThenTwoPhaseRewind(b+1, dst2)`).
A TM-`#eval` probe confirms the dual-append body yields the exact `encodeTape`
(head→`0`, clean halt). Only the structural scaffolding (validity/halts) is built
here; the run lemma `moveRegion2TM_run` mirrors `moveRegionTM_run` (a three-register
coupled invariant) and is the next step. -/

/-- Single-bit dual-transfer engine for a fixed bit `b`: run `moveBitM2TM` (delete
`src`'s front, append `b+1` to `dst1`, rewind), then append `b+1` to `dst2` and
two-phase-rewind. -/
def Compile.moveBitM3TM (b dst1 dst2 : Nat) : FlatTM :=
  composeFlatTM (Compile.moveBitM2TM b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1)

/-- The surviving (found) exit of `moveBitM3TM` (b-independent: `moveBitM2TM`'s state
count and `appendAtTM`'s are both b-independent). -/
def Compile.moveBitM3_exit (dst1 dst2 : Nat) : Nat :=
  (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 6)

/-- `moveBitM2TM`'s state count does not depend on the bit `b`. -/
theorem Compile.moveBitM2TM_states_eq (b dst : Nat) :
    (Compile.moveBitM2TM b dst).states = (Compile.moveBitM2TM 0 dst).states := by
  show (composeFlatTM ClearGadget.stepDeleteRewindRawTM
        (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
        ClearGadget.stepDeleteRewindTM_exit).states
      = (composeFlatTM ClearGadget.stepDeleteRewindRawTM
        (AppendGadget.appendAtThenTwoPhaseRewindTM (0 + 1) dst)
        ClearGadget.stepDeleteRewindTM_exit).states
  rw [composeFlatTM_states, composeFlatTM_states,
      AppendGadget.appendAtThenTwoPhaseRewindTM_states,
      AppendGadget.appendAtThenTwoPhaseRewindTM_states,
      Compile.appendAtTM_states_eq (b + 1) dst, Compile.appendAtTM_states_eq (0 + 1) dst]

theorem Compile.moveBitM3TM_tapes (b dst1 dst2 : Nat) :
    (Compile.moveBitM3TM b dst1 dst2).tapes = 1 := by
  rw [Compile.moveBitM3TM, composeFlatTM_tapes]; exact Compile.moveBitM2TM_tapes b dst1

theorem Compile.moveBitM3TM_sig (b dst1 dst2 : Nat) :
    (Compile.moveBitM3TM b dst1 dst2).sig = 4 := by
  rw [Compile.moveBitM3TM, composeFlatTM_sig, Compile.moveBitM2TM_sig,
      AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl

theorem Compile.moveBitM3TM_valid (b dst1 dst2 : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.moveBitM3TM b dst1 dst2) :=
  composeFlatTM_valid (Compile.moveBitM2TM b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1)
    (Compile.moveBitM2TM_valid b dst1 hb)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst2)
    (Compile.moveBitM2_exit_lt b dst1)
    (Compile.moveBitM2TM_tapes b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_tapes (b + 1) dst2)

theorem Compile.moveBitM3_exit_is_halt (b dst1 dst2 : Nat) :
    (Compile.moveBitM3TM b dst1 dst2).halt[Compile.moveBitM3_exit dst1 dst2]? = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro (Compile.moveBitM2TM b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1)
    ((AppendGadget.appendAtTM (b + 1) dst2).states + 6)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst2)
  rw [Compile.appendAtTM_states_eq (b + 1) dst2, Compile.moveBitM2TM_states_eq b dst1] at h
  exact h

theorem Compile.moveBitM3_exit_lt (b dst1 dst2 : Nat) :
    Compile.moveBitM3_exit dst1 dst2 < (Compile.moveBitM3TM b dst1 dst2).states := by
  rw [Compile.moveBitM3TM, composeFlatTM_states, Compile.moveBitM2TM_states_eq b dst1,
      AppendGadget.appendAtThenTwoPhaseRewindTM_states, Compile.appendAtTM_states_eq (b + 1) dst2,
      show (ScanLeft.rewindTwoPhaseTM 4 3).states = 8 from rfl]
  show (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 6)
      < (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 8)
  omega

/-- **The single-bit DUAL-transfer engine run (Risk C2).** From `src`'s content
start with front bit `b` (`s.get src = b :: cs`), `moveBitM3TM b dst1 dst2` deletes
`src`'s front cell, appends `b` to the end of **both** `dst1` and `dst2`, and
two-phase-rewinds, landing at `moveBitM3_exit` with the tape
`encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
  ++ (res ++ [0])` and head `0`. Composes `moveBitM2_run` (delete + append to `dst1`)
with `appendBitTwoPhase_run` (append to `dst2`). -/
theorem Compile.moveBitM3_run (s : State) (src dst1 dst2 : Var) (b : Nat) (cs : List Nat)
    (hb : b ≤ 1) (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2) (hd12 : dst1 ≠ dst2)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (hbit : Compile.BitState s) (hcons : s.get src = b :: cs) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBitM3TM b dst1 dst2)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBitM3_exit dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBitM3TM b dst1 dst2)
            { state_idx := 0,
              tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.moveBitM3TM b dst1 dst2) ck = false)
    ∧ t ≤ 10 * (Compile.encodeTape s ++ res).length + 30 := by
  -- Phase A: moveBitM2TM b dst1 (delete src front, append b to dst1).
  obtain ⟨tA, hA, hA_traj, hA_bud⟩ :=
    Compile.moveBitM2_run s src dst1 b cs hb hsd1 hsrc hdst1 hbit hcons res hres
  -- Phase B ingredients (on `mid`, appending b to dst2).
  have hbitA : Compile.BitState (s.set src cs) := by
    have := Compile.BitState_set_tail s src hbit hsrc
    rwa [show (s.get src).tail = cs from by rw [hcons, List.tail_cons]] at this
  have hgd1 : (s.set src cs).get dst1 = s.get dst1 :=
    Compile.get_set_ne s src cs dst1 hsrc (Ne.symm hsd1)
  have hdst1A : dst1 < (s.set src cs).length := by
    rw [Compile.length_set s src cs hsrc]; exact hdst1
  have hbitmid : Compile.BitState ((s.set src cs).set dst1 (s.get dst1 ++ [b])) := by
    refine Compile.BitState_set _ dst1 _ hbitA hdst1A ?_
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.BitState_get _ dst1 hbitA hdst1A x (by rw [hgd1]; exact hx)
    · simp only [List.mem_singleton] at hx; subst hx; omega
  have hdst2mid : dst2 < ((s.set src cs).set dst1 (s.get dst1 ++ [b])).length := by
    rw [Compile.length_set _ dst1 _ hdst1A, Compile.length_set s src cs hsrc]; exact hdst2
  have hgd2 : ((s.set src cs).set dst1 (s.get dst1 ++ [b])).get dst2 = s.get dst2 := by
    rw [Compile.get_set_ne (s.set src cs) dst1 (s.get dst1 ++ [b]) dst2 hdst1A (Ne.symm hd12),
        Compile.get_set_ne s src cs dst2 hsrc (Ne.symm hsd2)]
  have hres1 : Compile.ValidResidue (res ++ [0]) := by
    apply Compile.ValidResidue_append _ _ hres; intro x hx
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  obtain ⟨tB, hB, hB_traj, hB_bud⟩ :=
    Compile.appendBitTwoPhase_run b hb ((s.set src cs).set dst1 (s.get dst1 ++ [b])) dst2
      hbitmid hdst2mid (res ++ [0]) hres1
  rw [hgd2] at hB
  -- length: phase A's exit tape is one cell longer than the input tape.
  have hmidlen : (Compile.encodeTape ((s.set src cs).set dst1 (s.get dst1 ++ [b])) ++ (res ++ [0])).length
      = (Compile.encodeTape s ++ res).length + 1 := by
    have e1 := Compile.encodeTape_set_length s src cs hsrc
    have e2 := Compile.encodeTape_set_length (s.set src cs) dst1 (s.get dst1 ++ [b]) hdst1A
    rw [hgd1] at e2
    rw [hcons] at e1
    simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at e1 e2 ⊢
    omega
  -- compose: moveBitM2TM b dst1 ⨾ appendAtThenTwoPhaseRewindTM (b+1) dst2.
  set right₁ : List Nat :=
    Compile.encodeTape ((s.set src cs).set dst1 (s.get dst1 ++ [b])) ++ (res ++ [0]) with hr1
  have hvalid1 : validFlatTM (Compile.moveBitM2TM b dst1) := Compile.moveBitM2TM_valid b dst1 hb
  have hvalid2 : validFlatTM (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) :=
    AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst2
  have hexit_lt : Compile.moveBitM2_exit dst1 < (Compile.moveBitM2TM b dst1).states :=
    Compile.moveBitM2_exit_lt b dst1
  have hcfg0lt : (0 : Nat) < (Compile.moveBitM2TM b dst1).states := by
    have := Compile.moveBitM2_exit_lt b dst1; omega
  have hM2start : (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).start = 0 := by
    show (composeFlatTM (AppendGadget.appendAtTM (b + 1) dst2) (ScanLeft.rewindTwoPhaseTM 4 3)
          (AppendGadget.appendAtTM_exit dst2)).start = 0
    rw [composeFlatTM_start, AppendGadget.appendAtTM_start]
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, right₁) = some v →
      v < max (Compile.moveBitM2TM b dst1).sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).sig := by
    intro v hv
    rw [hr1, show currentTapeSymbol (([] : List Nat), 0,
          Compile.encodeTape ((s.set src cs).set dst1 (s.get dst1 ++ [b])) ++ (res ++ [0]))
        = some 3 from rfl] at hv
    rw [show max (Compile.moveBitM2TM b dst1).sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).sig = 4 from by
        rw [Compile.moveBitM2TM_sig, AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl]
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_traj1 : ∀ k, k < tA → ∀ ck,
      runFlatTM k (Compile.moveBitM2TM b dst1)
          { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                       Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ Compile.moveBitM2_exit dst1 ∧
      haltingStateReached (Compile.moveBitM2TM b dst1) ck = false := by
    intro k hk ck hck
    have hh := hA_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBitM2_exit_is_halt b dst1) hh, hh⟩
  have h_app_traj' : ∀ k, k < tB → ∀ ck,
      runFlatTM k (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2)
          { state_idx := (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).start,
            tapes := [([], 0, right₁)] } = some ck →
      haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) ck = false := by
    rw [hM2start, hr1]; exact hB_traj
  have h_halt2 : haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2)
      { state_idx := 6 + (AppendGadget.appendAtTM (b + 1) dst2).states,
        tapes := [([], 0,
          Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
            ++ (res ++ [0]))] } = true := by
    rw [show (6 : Nat) + (AppendGadget.appendAtTM (b + 1) dst2).states
          = (AppendGadget.appendAtTM (b + 1) dst2).states + 6 from Nat.add_comm ..]
    exact Compile.haltingStateReached_of_halt
      (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst2)
  have hmoveeq : Compile.moveBitM3TM b dst1 dst2
      = composeFlatTM (Compile.moveBitM2TM b dst1)
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1) := rfl
  have hstate_eq : Compile.moveBitM3_exit dst1 dst2
      = (6 + (AppendGadget.appendAtTM (b + 1) dst2).states) + (Compile.moveBitM2TM b dst1).states := by
    show (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 6)
        = (6 + (AppendGadget.appendAtTM (b + 1) dst2).states) + (Compile.moveBitM2TM b dst1).states
    rw [Compile.moveBitM2TM_states_eq b dst1, Compile.appendAtTM_states_eq (b + 1) dst2]
    omega
  have hmain := composeFlatTM_run hvalid1 hvalid2 hexit_lt
    { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                 Compile.encodeTape s ++ res)] }
    hcfg0lt [] 0 right₁ hsym hA h_traj1
    (by rw [hM2start]; exact hB) h_halt2
  refine ⟨tA + 1 + tB, ?_, ?_, ?_⟩
  · rw [hmoveeq, hstate_eq]; exact hmain.1
  · intro k hk ck hck
    rw [hmoveeq] at hck ⊢
    exact composeFlatTM_no_early_halt hvalid1 hvalid2 hexit_lt
      { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                   Compile.encodeTape s ++ res)] }
      hcfg0lt [] 0 right₁ hsym hA h_traj1 h_app_traj' k hk ck hck
  · rw [hr1, hmidlen] at hB_bud
    omega

/-- Content branch (src non-empty): read the front bit, then run the matching
dual-bit transfer engine. The two bit paths exit at distinct states, merged by
`joinTwoHalts` below. -/
def Compile.moveContent2RawTM (dst1 dst2 : Nat) : FlatTM :=
  branchComposeFlatTM Compile.bitReadTM
    (Compile.moveBitM3TM 0 dst1 dst2) (Compile.moveBitM3TM 1 dst1 dst2)
    Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1

def Compile.moveContent2Exit0 (dst1 dst2 : Nat) : Nat :=
  Compile.bitReadTM.states + Compile.moveBitM3_exit dst1 dst2

def Compile.moveContent2Exit1 (dst1 dst2 : Nat) : Nat :=
  Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states + Compile.moveBitM3_exit dst1 dst2

/-- Content branch with the two bit-exits merged into one (`moveContent2Exit0`). -/
def Compile.moveContent2TM (dst1 dst2 : Nat) : FlatTM :=
  Compile.joinTwoHalts (Compile.moveContent2RawTM dst1 dst2)
    (Compile.moveContent2Exit0 dst1 dst2) (Compile.moveContent2Exit1 dst1 dst2)

theorem Compile.moveContent2RawTM_tapes (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).tapes = 1 := by
  rw [Compile.moveContent2RawTM, branchComposeFlatTM_tapes]; exact Compile.bitReadTM_tapes

theorem Compile.moveContent2TM_tapes (dst1 dst2 : Nat) :
    (Compile.moveContent2TM dst1 dst2).tapes = 1 := by
  rw [Compile.moveContent2TM, Compile.joinTwoHalts_tapes]
  exact Compile.moveContent2RawTM_tapes dst1 dst2

theorem Compile.moveContent2RawTM_sig (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).sig = 4 := by
  rw [Compile.moveContent2RawTM, branchComposeFlatTM_sig, Compile.bitReadTM_sig,
      Compile.moveBitM3TM_sig 0 dst1 dst2, Compile.moveBitM3TM_sig 1 dst1 dst2]; rfl

theorem Compile.moveContent2TM_sig (dst1 dst2 : Nat) :
    (Compile.moveContent2TM dst1 dst2).sig = 4 := by
  rw [Compile.moveContent2TM, joinTwoHalts_sig]; exact Compile.moveContent2RawTM_sig dst1 dst2

theorem Compile.moveContent2RawTM_valid (dst1 dst2 : Nat) :
    validFlatTM (Compile.moveContent2RawTM dst1 dst2) :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.bitReadTM_valid
    (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
    (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide)
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide)
    Compile.bitReadTM_tapes (Compile.moveBitM3TM_tapes 0 dst1 dst2)
    (Compile.moveBitM3TM_tapes 1 dst1 dst2)

theorem Compile.moveContent2Exit0_is_halt (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).halt[Compile.moveContent2Exit0 dst1 dst2]? = some true := by
  rw [Compile.moveContent2Exit0, Compile.moveContent2RawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide)) (Compile.moveBitM3_exit_lt 0 dst1 dst2)
    (Compile.moveBitM3_exit_is_halt 0 dst1 dst2)

theorem Compile.moveContent2Exit1_is_halt (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).halt[Compile.moveContent2Exit1 dst1 dst2]? = some true := by
  rw [Compile.moveContent2Exit1, Compile.moveContent2RawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide)) (Compile.moveBitM3_exit_is_halt 1 dst1 dst2)

theorem Compile.moveContent2Exit0_ne_exit1 (dst1 dst2 : Nat) :
    Compile.moveContent2Exit0 dst1 dst2 ≠ Compile.moveContent2Exit1 dst1 dst2 := by
  show Compile.bitReadTM.states + Compile.moveBitM3_exit dst1 dst2
      ≠ Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states
        + Compile.moveBitM3_exit dst1 dst2
  have h0 : 0 < (Compile.moveBitM3TM 0 dst1 dst2).states := by
    have := Compile.moveBitM3_exit_lt 0 dst1 dst2; omega
  omega

theorem Compile.moveContent2Exit0_lt (dst1 dst2 : Nat) :
    Compile.moveContent2Exit0 dst1 dst2 < (Compile.moveContent2RawTM dst1 dst2).states := by
  rw [Compile.moveContent2Exit0, Compile.moveContent2RawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM3_exit_lt 0 dst1 dst2; omega

theorem Compile.moveContent2Exit1_lt (dst1 dst2 : Nat) :
    Compile.moveContent2Exit1 dst1 dst2 < (Compile.moveContent2RawTM dst1 dst2).states := by
  rw [Compile.moveContent2Exit1, Compile.moveContent2RawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM3_exit_lt 1 dst1 dst2; omega

theorem Compile.moveContent2TM_valid (dst1 dst2 : Nat) :
    validFlatTM (Compile.moveContent2TM dst1 dst2) :=
  joinTwoHalts_valid _ _ _ (Compile.moveContent2RawTM_valid dst1 dst2)
    (Compile.moveContent2Exit0_lt dst1 dst2) (Compile.moveContent2Exit1_lt dst1 dst2)
    (Compile.moveContent2RawTM_tapes dst1 dst2)

theorem Compile.moveContent2TM_exit0_is_halt (dst1 dst2 : Nat) :
    (Compile.moveContent2TM dst1 dst2).halt[Compile.moveContent2Exit0 dst1 dst2]? = some true :=
  joinTwoHalts_h1_is_halt _ _ _ (Compile.moveContent2Exit0_ne_exit1 dst1 dst2)
    (Compile.moveContent2Exit0_is_halt dst1 dst2)

theorem Compile.moveContent2Exit0_lt_states (dst1 dst2 : Nat) :
    Compile.moveContent2Exit0 dst1 dst2 < (Compile.moveContent2TM dst1 dst2).states := by
  rw [Compile.moveContent2TM, joinTwoHalts_states]; exact Compile.moveContent2Exit0_lt dst1 dst2

/-- **The dual-target content-branch run (Risk C2).** Mirrors `moveContent_run`:
run from `src`'s content start (head `H`) with front bit `b` (`s.get src = b :: cs`),
`moveContent2TM dst1 dst2` reads the bit and runs the matching dual-bit transfer
(`moveBitM3_run`), the two bit-paths merging through `joinTwoHalts` into
`moveContent2Exit0`. The tape becomes
`encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
  ++ (res ++ [0])`. -/
theorem Compile.moveContent2_run (s : State) (src dst1 dst2 : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2)
    (hd12 : dst1 ≠ dst2) (hbit : Compile.BitState s)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveContent2TM dst1 dst2)
        { state_idx := 0,
          tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveContent2Exit0 dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveContent2TM dst1 dst2)
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.moveContent2Exit0 dst1 dst2 ∧
        haltingStateReached (Compile.moveContent2TM dst1 dst2) ck = false)
    ∧ t ≤ 10 * (Compile.encodeTape s ++ res).length + 33 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.moveContent2RawTM dst1 dst2 with hrawdef
  set h1 := Compile.moveContent2Exit0 dst1 dst2 with hh1def
  set h2 := Compile.moveContent2Exit1 dst1 dst2 with hh2def
  have hraweq : branchComposeFlatTM Compile.bitReadTM
      (Compile.moveBitM3TM 0 dst1 dst2) (Compile.moveBitM3TM 1 dst1 dst2)
      Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1 = raw := rfl
  have hMeq : Compile.moveContent2TM dst1 dst2 = joinTwoHalts raw h1 h2 := rfl
  rw [hMeq]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hHeq : (1 : Nat) + (Compile.encodeRegs (s.take src)).length = H := by
    rw [hHdef, hskdef, Compile.regBlocks_map_shiftReg]
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  set tail' := Compile.shiftReg cs ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src hsrc
    rw [← hskdef] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg cs := by
      rw [hcons]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hHlt : H < (Compile.encodeTape s ++ res).length := by
    rw [hdecomp, hHdef]; simp only [List.length_cons, List.length_append]; omega
  have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = b + 1 := by
    have h? : (Compile.encodeTape s ++ res)[H]? = some (b + 1) := by
      rw [hdecomp, hHdef,
          show ((3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail'))
            = ((3 : Nat) :: AppendGadget.regBlocks skipped) ++ ((b + 1) :: tail') from by simp,
          List.getElem?_append_right (by simp only [List.length_cons]; omega),
          show 1 + (AppendGadget.regBlocks skipped).length
            - ((3 : Nat) :: AppendGadget.regBlocks skipped).length = 0 from by
              simp only [List.length_cons]; omega]
      rfl
    rw [List.getElem?_eq_getElem hHlt] at h?
    rw [List.get_eq_getElem]; exact Option.some.inj h?
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max Compile.bitReadTM.sig
          (max (Compile.moveBitM3TM 0 dst1 dst2).sig (Compile.moveBitM3TM 1 dst1 dst2).sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    rw [Compile.bitReadTM_sig]
    have : v < 4 := by have : v = b + 1 := (Option.some.inj hv).symm; omega
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < Compile.bitReadTM.states := by rw [Compile.bitReadTM_states]; omega
  have hexit_neq : Compile.bitReadTM_exit_b0 ≠ Compile.bitReadTM_exit_b1 := by decide
  have hep_lt : Compile.bitReadTM_exit_b0 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide
  have hen_lt : Compile.bitReadTM_exit_b1 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide
  have hh1_is := Compile.moveContent2Exit0_is_halt dst1 dst2
  have hh2_is := Compile.moveContent2Exit1_is_halt dst1 dst2
  have hh_ne := Compile.moveContent2Exit0_ne_exit1 dst1 dst2
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  have htest_run := Compile.bitReadTM_run b hb [] (Compile.encodeTape s ++ res) H hHlt hcellH
  have htest_traj : ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.bitReadTM cfg0 = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧ ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧
      haltingStateReached Compile.bitReadTM ck = false := by
    intro k hk ck hck
    exact Compile.bitReadTM_no_early_halt [] (Compile.encodeTape s ++ res) H k hk ck hck
  interval_cases b
  · -- bit 0: pos branch, dual transfer engine for bit 0; kept exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM3_run s src dst1 dst2 0 cs (by omega) hsd1 hsd2 hd12 hsrc hdst1 hdst2 hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM3_exit_is_halt 0 dst1 dst2))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM3_exit dst1 dst2 + Compile.bitReadTM.states = h1 := by
      rw [hh1def]; show Compile.moveBitM3_exit dst1 dst2 + Compile.bitReadTM.states
        = Compile.bitReadTM.states + Compile.moveBitM3_exit dst1 dst2
      omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [0])).set dst2
            (s.get dst2 ++ [0])) ++ (res ++ [0]))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega
  · -- bit 1: neg branch, dual transfer engine for bit 1; demoted exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM3_run s src dst1 dst2 1 cs (by omega) hsd1 hsd2 hd12 hsrc hdst1 hdst2 hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM3_exit_is_halt 1 dst1 dst2))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM3_exit dst1 dst2
        + (Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states) = h2 := by
      rw [hh2def]; show Compile.moveBitM3_exit dst1 dst2
          + (Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states)
        = Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states
            + Compile.moveBitM3_exit dst1 dst2
      omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [1])).set dst2
            (s.get dst2 ++ [1])) ++ (res ++ [0])) 0
      hneg.1 (fun k hk ck hck => hneg_traj k hk ck hck) hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [1])).set dst2
                (s.get dst2 ++ [1])) ++ (res ++ [0]))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.moveContent2RawTM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega

/-- The loop body: navigate to `src`, branch content (move one bit to both targets)
vs delim (src empty → rewind & stop). -/
def Compile.moveBody2RawTM (src dst1 dst2 : Nat) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM src) (Compile.moveContent2TM dst1 dst2)
    ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content src) (ClearGadget.navigateAndTestTM_exit_delim src)

def Compile.moveBody2RawTM_exitLoop (src dst1 dst2 : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + Compile.moveContent2Exit0 dst1 dst2

def Compile.moveBody2RawTM_exitDone (src dst1 dst2 : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
    + ClearGadget.justRewindTM_exit

/-- The full dual-target move gadget: loop the body until `src` empties. -/
def Compile.moveRegion2TM (src dst1 dst2 : Nat) : FlatTM :=
  loopTM (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)

/-- The single halt state of `moveRegion2TM` (the `loopTM` done-exit). -/
def Compile.moveRegion2TM_exit (src dst1 dst2 : Nat) : Nat :=
  (Compile.moveBody2RawTM src dst1 dst2).states

theorem Compile.moveBody2RawTM_tapes (src dst1 dst2 : Nat) :
    (Compile.moveBody2RawTM src dst1 dst2).tapes = 1 := by
  rw [Compile.moveBody2RawTM, branchComposeFlatTM_tapes]
  exact ClearGadget.navigateAndTestTM_tapes src

theorem Compile.moveBody2RawTM_valid (src dst1 dst2 : Nat) :
    validFlatTM (Compile.moveBody2RawTM src dst1 dst2) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.navigateAndTestTM_valid src)
    (Compile.moveContent2TM_valid dst1 dst2) ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    (ClearGadget.navigateAndTestTM_tapes src) (Compile.moveContent2TM_tapes dst1 dst2)
    ClearGadget.justRewindTM_tapes

theorem Compile.moveBody2RawTM_exitLoop_is_halt (src dst1 dst2 : Nat) :
    (Compile.moveBody2RawTM src dst1 dst2).halt[Compile.moveBody2RawTM_exitLoop src dst1 dst2]?
      = some true := by
  rw [Compile.moveBody2RawTM_exitLoop, Compile.moveBody2RawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveContent2TM_valid dst1 dst2) (Compile.moveContent2Exit0_lt_states dst1 dst2)
    (Compile.moveContent2TM_exit0_is_halt dst1 dst2)

theorem Compile.moveBody2RawTM_exitDone_is_halt (src dst1 dst2 : Nat) :
    (Compile.moveBody2RawTM src dst1 dst2).halt[Compile.moveBody2RawTM_exitDone src dst1 dst2]?
      = some true := by
  rw [Compile.moveBody2RawTM_exitDone, Compile.moveBody2RawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveContent2TM_valid dst1 dst2)
    (show ClearGadget.justRewindTM.halt[ClearGadget.justRewindTM_exit]? = some true from rfl)

theorem Compile.moveBody2RawTM_exitLoop_lt (src dst1 dst2 : Nat) :
    Compile.moveBody2RawTM_exitLoop src dst1 dst2 < (Compile.moveBody2RawTM src dst1 dst2).states := by
  rw [Compile.moveBody2RawTM_exitLoop, Compile.moveBody2RawTM, branchComposeFlatTM_states]
  have := Compile.moveContent2Exit0_lt_states dst1 dst2; omega

theorem Compile.moveBody2RawTM_exitDone_lt (src dst1 dst2 : Nat) :
    Compile.moveBody2RawTM_exitDone src dst1 dst2 < (Compile.moveBody2RawTM src dst1 dst2).states := by
  rw [Compile.moveBody2RawTM_exitDone, Compile.moveBody2RawTM, branchComposeFlatTM_states]
  show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
      + ClearGadget.justRewindTM_exit
    < (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
      + ClearGadget.justRewindTM.states
  show _ + _ + 1 < _ + _ + 3; omega

theorem Compile.moveBody2RawTM_exitDone_ne_exitLoop (src dst1 dst2 : Nat) :
    Compile.moveBody2RawTM_exitDone src dst1 dst2 ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 := by
  rw [Compile.moveBody2RawTM_exitDone, Compile.moveBody2RawTM_exitLoop]
  have := Compile.moveContent2Exit0_lt_states dst1 dst2; omega

theorem Compile.moveRegion2TM_tapes (src dst1 dst2 : Nat) :
    (Compile.moveRegion2TM src dst1 dst2).tapes = 1 := by
  rw [Compile.moveRegion2TM, loopTM_tapes]; exact Compile.moveBody2RawTM_tapes src dst1 dst2

theorem Compile.moveRegion2TM_start (src dst1 dst2 : Nat) :
    (Compile.moveRegion2TM src dst1 dst2).start = 0 := by
  show (Compile.moveBody2RawTM src dst1 dst2).start = 0
  show (branchComposeFlatTM _ _ _ _ _).start = 0
  rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src

/-- **Validity of `moveRegion2TM`.** Mirrors `moveRegionTM_valid`: a `loopTM` over
the valid dual-target body. -/
theorem Compile.moveRegion2TM_valid (src dst1 dst2 : Nat) :
    validFlatTM (Compile.moveRegion2TM src dst1 dst2) :=
  loopTM_valid (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)
    (Compile.moveBody2RawTM_valid src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_lt src dst1 dst2) (Compile.moveBody2RawTM_exitLoop_lt src dst1 dst2)
    (Compile.moveBody2RawTM_tapes src dst1 dst2)

theorem Compile.moveRegion2TM_sig (src dst1 dst2 : Nat) :
    (Compile.moveRegion2TM src dst1 dst2).sig = 4 := by
  rw [Compile.moveRegion2TM, loopTM_sig]
  show (Compile.moveBody2RawTM src dst1 dst2).sig = 4
  show (branchComposeFlatTM _ _ _ _ _).sig = 4
  rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig]
  show max 4 (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) = 4
  rw [Compile.moveContent2TM_sig dst1 dst2]
  rfl

/-- **Dual-target move loop body — done branch (`src` empty).** Mirrors
`moveBody_done_run`: navigate to `src`, find the delimiter (empty), rewind to head
`0`, tape unchanged, landing at `moveBody2RawTM_exitDone`. -/
theorem Compile.moveBody2_done_run (s : State) (src dst1 dst2 : Var) (res : List Nat)
    (hsrc : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBody2RawTM src dst1 dst2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBody2RawTM_exitDone src dst1 dst2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s src hsrc
  have hbit_take : Compile.BitState (s.take src) :=
    fun reg hreg => hbit reg (List.mem_of_mem_take hreg)
  set skipped : List (List Nat) := (s.take src).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take src) :=
    Compile.regBlocks_map_shiftReg (s.take src)
  have hsklen : skipped.length = src := by
    rw [hskdef, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hsrc)]
  have hskip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    rw [hskdef]; intro b hb
    rw [List.mem_map] at hb
    obtain ⟨reg, hreg, rfl⟩ := hb
    have hregmem : reg ∈ s := List.mem_of_mem_take hreg
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; omega
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      have : y ≤ 1 := hbit reg hregmem y hy; omega
  set tail' : List Nat :=
    Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htaildef
  have htape_nav : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    rw [hs, hempty, hregBlocks, htaildef]
    simp [Compile.shiftReg, Compile.endMark, List.append_assoc]
  have h_rb_le : (AppendGadget.regBlocks skipped).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [htape_nav]; simp only [List.length_cons, List.length_append]; omega
  have h_nav_le : ClearGadget.navSteps skipped ≤ 2 * (AppendGadget.regBlocks skipped).length + 1 :=
    ClearGadget.navSteps_le skipped
  have hrb : ∀ x ∈ AppendGadget.regBlocks skipped, x < 4 ∧ x ≠ 3 := by
    rw [hregBlocks]; intro x hx
    exact ⟨Compile.encodeRegs_lt_four (s.take src) hbit_take x hx,
           Compile.encodeRegs_no_endMark (s.take src) hbit_take x hx⟩
  have hpref : ∀ x ∈ AppendGadget.regBlocks skipped ++ [0], x < 4 ∧ x ≠ 3 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrb x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  have hrestsplit : AppendGadget.regBlocks skipped ++ 0 :: tail'
      = (AppendGadget.regBlocks skipped ++ [0]) ++ tail' := by simp [List.append_assoc]
  have h_rewind := ScanLeft.rewindToStart_run 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind
  have h_rewind_traj := ScanLeft.rewindToStart_traj 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind_traj
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM src).sig
        (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContent2TM_sig]; rfl,
        (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim src,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_delim skipped tail' hskip
    rw [← htape_nav, hsklen] at hn; exact hn
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail' hskip
        (by decide) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh,
           hh⟩
  have h_ne : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1
        ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1
      + ((1 + (AppendGadget.regBlocks skipped).length) + 1), ?_, ?_, ?_⟩
  · rw [show Compile.moveBody2RawTM src dst1 dst2
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
            (Compile.moveContent2TM dst1 dst2) ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content src)
            (ClearGadget.navigateAndTestTM_exit_delim src) from rfl,
      show Compile.moveBody2RawTM_exitDone src dst1 dst2
        = ClearGadget.justRewindTM_exit
            + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states)
          from by
          show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
              + ClearGadget.justRewindTM_exit
            = ClearGadget.justRewindTM_exit
                + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states)
          omega]
    exact (branchComposeFlatTM_run_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1 h_rewind
      (Compile.haltingStateReached_of_halt (show ClearGadget.justRewindTM.halt[1]? = some true from rfl))).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (fun k' hk' ck' hck' => (h_rewind_traj k' hk' ck' hck').2)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitDone_is_halt src dst1 dst2) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitLoop_is_halt src dst1 dst2) hh, hh⟩
  · omega

/-- **Dual-target move loop body — delete branch (`src` non-empty, front bit `b`).**
Navigate to `src`, the content branch reads `b` and runs the dual-bit transfer
(`moveContent2_run`), landing at `moveBody2RawTM_exitLoop` with the tape
`encodeTape (((s.set src cs).set dst1 (d1++[b])).set dst2 (d2++[b])) ++ (res ++ [0])`. -/
theorem Compile.moveBody2_delete_run (s : State) (src dst1 dst2 : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2)
    (hd12 : dst1 ≠ dst2) (hbit : Compile.BitState s)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBody2RawTM src dst1 dst2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBody2RawTM_exitLoop src dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
                   ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false)
      ∧ t ≤ 12 * (Compile.encodeTape s ++ res).length + 38 := by
  have hne : s.get src ≠ [] := by rw [hcons]; exact List.cons_ne_nil _ _
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
    Compile.moveContent2_run s src dst1 dst2 b cs hcons hb hsd1 hsd2 hd12 hbit hsrc hdst1 hdst2 res hres
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) := by
    intro v hv
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContent2TM_sig]; rfl]
    have hmem : v ∈ Compile.encodeTape s ++ res := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact htape4 v hmem
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hpos := branchComposeFlatTM_run_pos hexit_neq
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne) hbody
    (Compile.haltingStateReached_of_halt (Compile.moveContent2TM_exit0_is_halt dst1 dst2))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne)
    (fun k hk ck hck => (hbody_traj k hk ck hck).2)
  have hstate_eq : Compile.moveContent2Exit0 dst1 dst2 + (ClearGadget.navigateAndTestTM src).states
      = Compile.moveBody2RawTM_exitLoop src dst1 dst2 := by
    rw [Compile.moveBody2RawTM_exitLoop]; omega
  have hmoveeq : Compile.moveBody2RawTM src dst1 dst2
      = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
          (Compile.moveContent2TM dst1 dst2) ClearGadget.justRewindTM
          (ClearGadget.navigateAndTestTM_exit_content src)
          (ClearGadget.navigateAndTestTM_exit_delim src) := rfl
  rw [hstate_eq] at hpos
  refine ⟨(ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [hmoveeq]; exact hpos.1
  · intro k hk ck hck
    rw [hmoveeq] at hck
    have hh := hpos_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitDone_is_halt src dst1 dst2) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitLoop_is_halt src dst1 dst2) hh, hh⟩
  · have hnav : ClearGadget.navSteps ((s.take src).map Compile.shiftReg)
        ≤ 2 * (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length + 1 :=
      ClearGadget.navSteps_le _
    have hrbL : (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length
        ≤ (Compile.encodeTape s ++ res).length := by
      have hsplit := congrArg List.length (Compile.encodeTape_split s src hsrc)
      simp only [List.length_append, List.length_cons, Compile.encodeRegs_length] at hsplit
      rw [List.length_append, Compile.encodeTape_length]
      omega
    omega

/-- **Move loop body — done branch (`src` empty).** Mirrors `clearBody_done_run`:
navigate to `src`, find the delimiter (empty), rewind to head `0`, tape unchanged,
landing at `moveBodyRawTM_exitDone`. The content machine `moveContentTM dst` is the
(unused) positive branch. -/
theorem Compile.moveBody_done_run (s : State) (src dst : Var) (res : List Nat)
    (hsrc : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBodyRawTM src dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBodyRawTM_exitDone src dst,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s src hsrc
  have hbit_take : Compile.BitState (s.take src) :=
    fun reg hreg => hbit reg (List.mem_of_mem_take hreg)
  set skipped : List (List Nat) := (s.take src).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take src) :=
    Compile.regBlocks_map_shiftReg (s.take src)
  have hsklen : skipped.length = src := by
    rw [hskdef, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hsrc)]
  have hskip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    rw [hskdef]; intro b hb
    rw [List.mem_map] at hb
    obtain ⟨reg, hreg, rfl⟩ := hb
    have hregmem : reg ∈ s := List.mem_of_mem_take hreg
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; omega
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      have : y ≤ 1 := hbit reg hregmem y hy; omega
  set tail' : List Nat :=
    Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htaildef
  have htape_nav : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    rw [hs, hempty, hregBlocks, htaildef]
    simp [Compile.shiftReg, Compile.endMark, List.append_assoc]
  have h_rb_le : (AppendGadget.regBlocks skipped).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [htape_nav]; simp only [List.length_cons, List.length_append]; omega
  have h_nav_le : ClearGadget.navSteps skipped ≤ 2 * (AppendGadget.regBlocks skipped).length + 1 :=
    ClearGadget.navSteps_le skipped
  have hrb : ∀ x ∈ AppendGadget.regBlocks skipped, x < 4 ∧ x ≠ 3 := by
    rw [hregBlocks]; intro x hx
    exact ⟨Compile.encodeRegs_lt_four (s.take src) hbit_take x hx,
           Compile.encodeRegs_no_endMark (s.take src) hbit_take x hx⟩
  have hpref : ∀ x ∈ AppendGadget.regBlocks skipped ++ [0], x < 4 ∧ x ≠ 3 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrb x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  have hrestsplit : AppendGadget.regBlocks skipped ++ 0 :: tail'
      = (AppendGadget.regBlocks skipped ++ [0]) ++ tail' := by simp [List.append_assoc]
  have h_rewind := ScanLeft.rewindToStart_run 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind
  have h_rewind_traj := ScanLeft.rewindToStart_traj 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind_traj
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM src).sig
        (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContentTM_sig]; rfl,
        (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim src,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_delim skipped tail' hskip
    rw [← htape_nav, hsklen] at hn; exact hn
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail' hskip
        (by decide) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh,
           hh⟩
  have h_ne : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1
        ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1
      + ((1 + (AppendGadget.regBlocks skipped).length) + 1), ?_, ?_, ?_⟩
  · rw [show Compile.moveBodyRawTM src dst
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
            (Compile.moveContentTM dst) ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content src)
            (ClearGadget.navigateAndTestTM_exit_delim src) from rfl,
      show Compile.moveBodyRawTM_exitDone src dst
        = ClearGadget.justRewindTM_exit
            + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states)
          from by
          show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
              + ClearGadget.justRewindTM_exit
            = ClearGadget.justRewindTM_exit
                + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states)
          omega]
    exact (branchComposeFlatTM_run_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1 h_rewind
      (Compile.haltingStateReached_of_halt (show ClearGadget.justRewindTM.halt[1]? = some true from rfl))).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (fun k' hk' ck' hck' => (h_rewind_traj k' hk' ck' hck').2)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitDone_is_halt src dst) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitLoop_is_halt src dst) hh, hh⟩
  · omega

/-- **Move loop body — delete branch (`src` non-empty, front bit `b`).** Navigate
to `src`, the content branch reads bit `b` and runs the single-bit transfer
(`moveContent_run`), landing at `moveBodyRawTM_exitLoop` with the tape
`encodeTape ((s.set src cs).set dst (s.get dst ++ [b])) ++ (res ++ [0])`. Mirrors
`opHead_run`'s content case. -/
theorem Compile.moveBody_delete_run (s : State) (src dst : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd : src ≠ dst)
    (hbit : Compile.BitState s) (hsrc : src < s.length) (hdst : dst < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBodyRawTM src dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBodyRawTM_exitLoop src dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                   ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false)
      ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length + 26 := by
  have hne : s.get src ≠ [] := by rw [hcons]; exact List.cons_ne_nil _ _
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
    Compile.moveContent_run s src dst b cs hcons hb hsd hbit hsrc hdst res hres
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) := by
    intro v hv
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContentTM_sig]; rfl]
    have hmem : v ∈ Compile.encodeTape s ++ res := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact htape4 v hmem
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hpos := branchComposeFlatTM_run_pos hexit_neq
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne) hbody
    (Compile.haltingStateReached_of_halt (Compile.moveContentTM_exit0_is_halt dst))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne)
    (fun k hk ck hck => (hbody_traj k hk ck hck).2)
  have hstate_eq : Compile.moveContentExit0 dst + (ClearGadget.navigateAndTestTM src).states
      = Compile.moveBodyRawTM_exitLoop src dst := by
    rw [Compile.moveBodyRawTM_exitLoop]; omega
  have hmoveeq : Compile.moveBodyRawTM src dst
      = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
          (Compile.moveContentTM dst) ClearGadget.justRewindTM
          (ClearGadget.navigateAndTestTM_exit_content src)
          (ClearGadget.navigateAndTestTM_exit_delim src) := rfl
  rw [hstate_eq] at hpos
  refine ⟨(ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [hmoveeq]; exact hpos.1
  · intro k hk ck hck
    rw [hmoveeq] at hck
    have hh := hpos_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitDone_is_halt src dst) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitLoop_is_halt src dst) hh, hh⟩
  · -- budget: navtest (≤ 2L+3) + bridge (1) + moveContent (≤ 7L+21) ≤ 9L+26.
    have hnav : ClearGadget.navSteps ((s.take src).map Compile.shiftReg)
        ≤ 2 * (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length + 1 :=
      ClearGadget.navSteps_le _
    have hrbL : (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length
        ≤ (Compile.encodeTape s ++ res).length := by
      have hsplit := congrArg List.length (Compile.encodeTape_split s src hsrc)
      simp only [List.length_append, List.length_cons, Compile.encodeRegs_length] at hsplit
      rw [List.length_append, Compile.encodeTape_length]
      omega
    omega

/-- **Move-loop budget arithmetic.** Each iteration is `O(L)` (a deletion + an
append, each one `O(current tape length) ≤ O(2·L)`), summed over `≤ L`
iterations — dominated by the quadratic `25·L²+25` (`n+2 ≤ L`). -/
theorem Compile.moveBudget_arith (n L : Nat) (h : n + 2 ≤ L) :
    (n + 1) * (18 * L + 27) ≤ 25 * L * L + 25 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  nlinarith [Nat.zero_le n, Nat.zero_le d, Nat.zero_le (n * d)]

/-- **The residue-tolerant move contract (Risk C2 — Task 2 critical path).**
Running `moveRegionTM src dst` on `encodeTape s ++ res_in` transfers `src`'s
content (FIFO) to the end of `dst`, empties `src`, rewinds the head to `0`, and
leaves the tape `encodeTape (moved s) ++ (res_in ++ replicate |s.get src| 0)`.
Assembled from `loopTM_run`; the per-iteration invariant `T j` couples BOTH
registers (`src = drop (n−j)` of `src₀`, `dst = dst₀ ++ first (n−j) bits`), and
the moved bit's value is threaded so `dst` gets the right bit. Unlike `clear`, the
tape **grows** one residue cell per iteration (`|T j| = L + (n−j)`), so the loop
budget is `25·L²+25` with `L = |encodeTape s ++ res_in|`. -/
theorem Compile.moveRegionTM_run (s : State) (src dst : Var) (res_in : List Nat)
    (hsd : src ≠ dst) (hsrc : src < s.length) (hdst : dst < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res_in) :
    ∃ t, runFlatTM t (Compile.moveRegionTM src dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
      = some { state_idx := Compile.moveRegionTM_exit src dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set dst (s.get dst ++ s.get src)).set src [])
                   ++ (res_in ++ List.replicate (s.get src).length 0))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveRegionTM src dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } = some ck →
          ck.state_idx ≠ Compile.moveRegionTM_exit src dst ∧
          haltingStateReached (Compile.moveRegionTM src dst) ck = false)
      ∧ t ≤ 25 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
              + 25 := by
  set n := (s.get src).length with hn
  set st : Nat → State := fun m =>
    (s.set dst (s.get dst ++ (s.get src).take m)).set src ((s.get src).drop m) with hstdef
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 0, Compile.encodeTape (st (n - j)) ++ (res_in ++ List.replicate (n - j) 0)) with hTdef
  set L := (Compile.encodeTape s ++ res_in).length with hLdef
  have hsrc' : src < (s.set dst (s.get dst ++ (s.get src).take 0)).length := by
    rw [Compile.length_set s dst _ hdst]; exact hsrc
  have hv_bit : ∀ x ∈ s.get src, x ≤ 1 := Compile.BitState_get s src hbit hsrc
  have hd_bit : ∀ x ∈ s.get dst, x ≤ 1 := Compile.BitState_get s dst hbit hdst
  have hBstart : (Compile.moveBodyRawTM src dst).start = 0 := by
    show (branchComposeFlatTM _ _ _ _ _).start = 0
    rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src
  -- structural facts about `st m`.
  have hsrc_in : ∀ m, src < (s.set dst (s.get dst ++ (s.get src).take m)).length := by
    intro m; rw [Compile.length_set s dst _ hdst]; exact hsrc
  have hbit_st : ∀ m, Compile.BitState (st m) := by
    intro m
    have hbase : Compile.BitState (s.set dst (s.get dst ++ (s.get src).take m)) := by
      refine Compile.BitState_set s dst _ hbit hdst ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hd_bit x hx
      · exact hv_bit x (List.mem_of_mem_take hx)
    exact Compile.BitState_set _ src _ hbase (hsrc_in m)
      (fun x hx => hv_bit x (List.mem_of_mem_drop hx))
  have hlen_st : ∀ m, (st m).length = s.length := by
    intro m; rw [hstdef, Compile.length_set _ src _ (hsrc_in m), Compile.length_set s dst _ hdst]
  have hget_src_st : ∀ m, (st m).get src = (s.get src).drop m := by
    intro m; rw [hstdef]; exact Compile.get_set_eq _ src _ (hsrc_in m)
  have hget_dst_st : ∀ m, (st m).get dst = s.get dst ++ (s.get src).take m := by
    intro m; rw [hstdef, Compile.get_set_ne _ src _ dst (hsrc_in m) (Ne.symm hsd),
      Compile.get_set_eq s dst _ hdst]
  -- size of `st m` equals `State.size s` (bits move within the state).
  have hsize_st : ∀ m, m ≤ n → State.size (st m) = State.size s := by
    intro m hm
    have h1 := State.size_set_add s dst (s.get dst ++ (s.get src).take m)
    have h2 := State.size_set_add (s.set dst (s.get dst ++ (s.get src).take m)) src
      ((s.get src).drop m)
    rw [Compile.get_set_ne s dst _ src hdst hsd] at h2
    rw [List.length_append] at h1
    have htake : ((s.get src).take m).length = m := by rw [List.length_take, ← hn]; omega
    have hdrop : ((s.get src).drop m).length = n - m := by rw [List.length_drop, ← hn]
    rw [htake] at h1
    rw [hdrop] at h2
    simp only [hstdef] at h2 ⊢
    rw [← hn] at h2
    omega
  -- tape length of `T j`: grows by `n − j` residue cells.
  have hTlen : ∀ j, j ≤ n → (T j).2.2.length = L + (n - j) := by
    intro j hj
    simp only [hTdef, List.length_append, List.length_replicate]
    rw [Compile.encodeTape_length, hsize_st (n - j) (Nat.sub_le n j), hlen_st,
        hLdef, List.length_append, Compile.encodeTape_length]
    omega
  have hnL : n + 2 ≤ L := by
    have hsize := State.size_set_add s src ([] : List Nat)
    simp only [List.length_nil, Nat.add_zero] at hsize
    rw [hLdef, List.length_append, Compile.encodeTape_length]
    omega
  -- all tape symbols of `T j` are `< 4`.
  have hT_lt : ∀ j x, x ∈ (T j).2.2 → x < 4 := by
    intro j x hx
    simp only [hTdef] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four _ (hbit_st _) x hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hres x hx).1
      · rw [List.mem_replicate] at hx; omega
  have h_sym : ∀ m v, currentTapeSymbol (T m) = some v → v < (Compile.moveBodyRawTM src dst).sig := by
    intro m v hv
    have hsig : (Compile.moveBodyRawTM src dst).sig = 4 := by
      show (branchComposeFlatTM _ _ _ _ _).sig = 4
      rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig, Compile.moveContentTM_sig]; rfl
    rw [hsig]
    have hmem : v ∈ (T m).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_lt m v hmem
  -- done branch: `T 0`, register `src` empty.
  have hdone := Compile.moveBody_done_run (st n) src dst (res_in ++ List.replicate n 0)
    (by rw [hlen_st]; exact hsrc) (hbit_st n)
    (by rw [hget_src_st, hn]; exact List.drop_length)
    (Compile.ValidResidue_append_replicate_zero res_in n hres)
  obtain ⟨tDone, hdr, hdt, hdb⟩ := hdone
  have hT0 : T 0 = ([], 0, Compile.encodeTape (st n) ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero]
  have h_done_bnd : tDone + 1 ≤ 18 * L + 27 := by
    have hlen0 := hTlen 0 (Nat.zero_le n)
    simp only [hTdef, Nat.sub_zero] at hlen0
    rw [hlen0] at hdb
    omega
  -- per-iteration move: `T (j+1) → T j` for `j < n`, moving one bit.
  have hiter_ex : ∀ j, j < n → ∃ t,
      runFlatTM t (Compile.moveBodyRawTM src dst)
          { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBodyRawTM_exitLoop src dst, tapes := [T j] } ∧
      (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBodyRawTM src dst)
            { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] } = some ck →
        ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
        ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
        haltingStateReached (Compile.moveBodyRawTM src dst) ck = false) ∧
      t ≤ 18 * L + 26 := by
    intro j hj
    set m := n - (j + 1) with hm
    have hmn : m < n := by omega
    have hm1 : m + 1 = n - j := by omega
    have hmlen : m < (s.get src).length := by rw [← hn]; exact hmn
    -- the front bit of `st m`'s src content.
    have hdc : (s.get src).drop m = (s.get src)[m] :: (s.get src).drop (m + 1) :=
      List.drop_eq_getElem_cons hmlen
    have hb1 : (s.get src)[m] ≤ 1 := hv_bit _ (List.getElem_mem hmlen)
    have hsrc_cons : (st m).get src = (s.get src)[m] :: (s.get src).drop (m + 1) := by
      rw [hget_src_st]; exact hdc
    obtain ⟨t, hr, ht, hbnd⟩ := Compile.moveBody_delete_run (st m) src dst ((s.get src)[m])
      ((s.get src).drop (m + 1)) hsrc_cons hb1 hsd (hbit_st m) (by rw [hlen_st]; exact hsrc)
      (by rw [hlen_st]; exact hdst) (res_in ++ List.replicate m 0)
      (Compile.ValidResidue_append_replicate_zero res_in m hres)
    -- bridge the move output to `T j`.
    have hstate_eq : ((st m).set src ((s.get src).drop (m + 1))).set dst
          ((st m).get dst ++ [(s.get src)[m]]) = st (n - j) := by
      rw [hget_dst_st, hstdef]
      rw [Compile.set_set _ src _ _ (hsrc_in m)]
      rw [Compile.set_comm (s.set dst (s.get dst ++ (s.get src).take m)) src dst _ _
            (hsrc_in m) (by rw [Compile.length_set s dst _ hdst]; exact hdst) hsd,
          Compile.set_set s dst _ _ hdst]
      rw [show (s.get dst ++ (s.get src).take m) ++ [(s.get src)[m]]
            = s.get dst ++ (s.get src).take (m + 1) from by
            rw [List.append_assoc, List.take_succ_eq_append_getElem hmlen],
          ← hm1]
    have hres_eq : (res_in ++ List.replicate m 0) ++ [0] = res_in ++ List.replicate (n - j) 0 := by
      rw [List.append_assoc, ← List.replicate_succ', hm1]
    rw [hstate_eq, hres_eq] at hr
    have hlenj := hTlen (j + 1) (by omega)
    simp only [hTdef] at hlenj
    rw [show n - (j + 1) = m from rfl] at hlenj
    rw [hlenj] at hbnd
    refine ⟨t, ?_, ?_, by omega⟩
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact hr
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact ht
  -- assemble the loop.
  set tIter : Nat → Nat := fun j => if hj : j < n then (hiter_ex j hj).choose else 0 with htIter
  have h_done_full :
      runFlatTM tDone (Compile.moveBodyRawTM src dst)
          { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T 0] }
        = some { state_idx := Compile.moveBodyRawTM_exitDone src dst, tapes := [T 0] } ∧
      (∀ k, k < tDone → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false) := by
    refine ⟨?_, ?_⟩
    · rw [hBstart, hT0]; exact hdr
    · rw [hBstart, hT0]; exact hdt
  have h_iter_full : ∀ j, j < n →
      runFlatTM (tIter j) (Compile.moveBodyRawTM src dst)
          { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBodyRawTM_exitLoop src dst, tapes := [T j] } ∧
      (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false) := by
    intro j hj
    have hspec := (hiter_ex j hj).choose_spec
    simp only [htIter, dif_pos hj]
    exact ⟨hspec.1, hspec.2.1⟩
  have h_iter_bnd : ∀ j, j < n → tIter j + 1 ≤ 18 * L + 27 := by
    intro j hj
    have hb := (hiter_ex j hj).choose_spec.2.2
    simp only [htIter, dif_pos hj]
    omega
  have hmain := loopTM_run (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)
    (Compile.moveBodyRawTM_valid src dst)
    (Compile.moveBodyRawTM_exitDone_lt src dst) (Compile.moveBodyRawTM_exitLoop_lt src dst)
    (Compile.moveBodyRawTM_exitDone_ne_exitLoop src dst) T h_sym tIter tDone h_done_full n h_iter_full
  have hmain_traj := loopTM_no_early_halt (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)
    (Compile.moveBodyRawTM_valid src dst)
    (Compile.moveBodyRawTM_exitDone_lt src dst) (Compile.moveBodyRawTM_exitLoop_lt src dst)
    (Compile.moveBodyRawTM_exitDone_ne_exitLoop src dst) T h_sym tIter tDone h_done_full n h_iter_full
  -- convert `T n` (start) and `T 0` (end) to the stated forms.
  have hTn : T n = ([], 0, Compile.encodeTape s ++ res_in) := by
    simp only [hTdef, Nat.sub_self]
    rw [hstdef]
    simp only [List.take_zero, List.drop_zero, List.append_nil, List.replicate_zero]
    rw [Compile.set_get_self s dst hdst, Compile.set_get_self s src hsrc]
  have hTfin : T 0 = ([], 0, Compile.encodeTape ((s.set dst (s.get dst ++ s.get src)).set src [])
      ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero, hstdef]
    rw [show (s.get src).take n = s.get src from by rw [hn]; exact List.take_length,
        show (s.get src).drop n = [] from by rw [hn]; exact List.drop_length]
  rw [hBstart, hTn, hTfin] at hmain
  rw [hBstart, hTn] at hmain_traj
  have hMeq : Compile.moveRegionTM src dst
      = loopTM (Compile.moveBodyRawTM src dst) (Compile.moveBodyRawTM_exitDone src dst)
          (Compile.moveBodyRawTM_exitLoop src dst) := rfl
  have hExeq : Compile.moveRegionTM_exit src dst = (Compile.moveBodyRawTM src dst).states := rfl
  have hexit_halt : (Compile.moveRegionTM src dst).halt[(Compile.moveBodyRawTM src dst).states]?
      = some true := by
    rw [hMeq]
    show (loopHalt (Compile.moveBodyRawTM src dst))[(Compile.moveBodyRawTM src dst).states]? = some true
    show (List.replicate (Compile.moveBodyRawTM src dst).states false ++ [true])[(Compile.moveBodyRawTM src dst).states]?
        = some true
    rw [List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  refine ⟨loopBudget tIter tDone n, ?_, ?_, ?_⟩
  · rw [hMeq, hExeq]; exact hmain
  · intro k hk ck hck
    rw [hMeq] at hck
    have hh := hmain_traj k hk ck hck
    refine ⟨?_, hh⟩
    rw [hExeq]
    rw [hMeq] at hexit_halt
    exact ClearGadget.ne_of_not_halting hexit_halt hh
  · -- budget: `loopBudget ≤ (n+1)·(18L+27) ≤ 25L²+25` (`n+2 ≤ L`).
    rw [hLdef] at hnL ⊢
    exact le_trans
      (Compile.loopBudget_le tIter tDone (18 * L + 27) n h_done_bnd h_iter_bnd)
      (by rw [← hLdef]; exact Compile.moveBudget_arith n L (by rw [hLdef]; exact hnL))

/-- **Dual-target move-loop budget arithmetic.** `(n+1)` iterations each `≤ 36L+39`
(per-iter tape `≤ L + 2(n−j) ≤ 3L`, two appends/bit), `n+1 ≤ L`, gives a cubic-free
quadratic total. -/
theorem Compile.moveBudget2_arith (n L : Nat) (h : n + 2 ≤ L) :
    (n + 1) * (36 * L + 39) ≤ 36 * L * L + 39 * L := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  nlinarith [Nat.zero_le n, Nat.zero_le d, Nat.zero_le (n * d)]

/-- **The dual-target duplicating move contract (Risk C2).** Running
`moveRegion2TM src dst1 dst2` on `encodeTape s ++ res_in` transfers `src`'s content
(FIFO) to the end of **both** `dst1` and `dst2`, empties `src`, rewinds the head to
`0`, leaving `encodeTape (moved s) ++ (res_in ++ replicate |s.get src| 0)`. Mirrors
`moveRegionTM_run`, but the per-iteration invariant couples **three** registers and
the state size grows (each bit is duplicated), so the per-iteration tape length is
`L + 2(n−j)` and the loop budget is `36·L²+39·L`. -/
theorem Compile.moveRegion2TM_run (s : State) (src dst1 dst2 : Var) (res_in : List Nat)
    (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2) (hd12 : dst1 ≠ dst2)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res_in) :
    ∃ t, runFlatTM t (Compile.moveRegion2TM src dst1 dst2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
      = some { state_idx := Compile.moveRegion2TM_exit src dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set dst1 (s.get dst1 ++ s.get src)).set dst2 (s.get dst2 ++ s.get src)).set src [])
                   ++ (res_in ++ List.replicate (s.get src).length 0))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveRegion2TM src dst1 dst2)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } = some ck →
          ck.state_idx ≠ Compile.moveRegion2TM_exit src dst1 dst2 ∧
          haltingStateReached (Compile.moveRegion2TM src dst1 dst2) ck = false)
      ∧ t ≤ 36 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
              + 39 * (Compile.encodeTape s ++ res_in).length := by
  set n := (s.get src).length with hn
  set st : Nat → State := fun m =>
    ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2 (s.get dst2 ++ (s.get src).take m)).set src
      ((s.get src).drop m) with hstdef
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 0, Compile.encodeTape (st (n - j)) ++ (res_in ++ List.replicate (n - j) 0)) with hTdef
  set L := (Compile.encodeTape s ++ res_in).length with hLdef
  have hv_bit : ∀ x ∈ s.get src, x ≤ 1 := Compile.BitState_get s src hbit hsrc
  have hd1_bit : ∀ x ∈ s.get dst1, x ≤ 1 := Compile.BitState_get s dst1 hbit hdst1
  have hd2_bit : ∀ x ∈ s.get dst2, x ≤ 1 := Compile.BitState_get s dst2 hbit hdst2
  have hBstart : (Compile.moveBody2RawTM src dst1 dst2).start = 0 := by
    show (branchComposeFlatTM _ _ _ _ _).start = 0
    rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src
  have hlenP : ∀ (m : Nat),
      (s.set dst1 (s.get dst1 ++ (s.get src).take m)).length = s.length :=
    fun m => Compile.length_set s dst1 _ hdst1
  have hlenQ : ∀ m, ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2
      (s.get dst2 ++ (s.get src).take m)).length = s.length :=
    fun m => by rw [Compile.length_set _ dst2 _ (by rw [hlenP]; exact hdst2), hlenP]
  have hlen_st : ∀ m, (st m).length = s.length := fun m => by
    simp only [hstdef]; rw [Compile.length_set _ src _ (by rw [hlenQ]; exact hsrc), hlenQ]
  have hget_src_st : ∀ m, (st m).get src = (s.get src).drop m := fun m => by
    simp only [hstdef]; exact Compile.get_set_eq _ src _ (by rw [hlenQ]; exact hsrc)
  have hget_dst1_st : ∀ m, (st m).get dst1 = s.get dst1 ++ (s.get src).take m := fun m => by
    simp only [hstdef]
    rw [Compile.get_set_ne _ src _ dst1 (by rw [hlenQ]; exact hsrc) (Ne.symm hsd1),
        Compile.get_set_ne _ dst2 _ dst1 (by rw [hlenP]; exact hdst2) hd12,
        Compile.get_set_eq s dst1 _ hdst1]
  have hget_dst2_st : ∀ m, (st m).get dst2 = s.get dst2 ++ (s.get src).take m := fun m => by
    simp only [hstdef]
    rw [Compile.get_set_ne _ src _ dst2 (by rw [hlenQ]; exact hsrc) (Ne.symm hsd2),
        Compile.get_set_eq _ dst2 _ (by rw [hlenP]; exact hdst2)]
  have hbit_st : ∀ m, Compile.BitState (st m) := fun m => by
    simp only [hstdef]
    refine Compile.BitState_set _ src _ ?_ (by rw [hlenQ]; exact hsrc)
      (fun x hx => hv_bit x (List.mem_of_mem_drop hx))
    refine Compile.BitState_set _ dst2 _ ?_ (by rw [hlenP]; exact hdst2) ?_
    · refine Compile.BitState_set s dst1 _ hbit hdst1 ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hd1_bit x hx
      · exact hv_bit x (List.mem_of_mem_take hx)
    · intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hd2_bit x hx
      · exact hv_bit x (List.mem_of_mem_take hx)
  -- size of `st m` grows by `m` (each moved bit is duplicated into dst1 and dst2).
  have hsize_st : ∀ m, m ≤ n → State.size (st m) = State.size s + m := by
    intro m hm
    have htake : ((s.get src).take m).length = m := by rw [List.length_take, ← hn]; omega
    have hdrop : ((s.get src).drop m).length = n - m := by rw [List.length_drop, ← hn]
    have e1 := State.size_set_add s dst1 (s.get dst1 ++ (s.get src).take m)
    have hP_d2 : (s.set dst1 (s.get dst1 ++ (s.get src).take m)).get dst2 = s.get dst2 :=
      Compile.get_set_ne s dst1 _ dst2 hdst1 (Ne.symm hd12)
    have e2 := State.size_set_add (s.set dst1 (s.get dst1 ++ (s.get src).take m)) dst2
      (s.get dst2 ++ (s.get src).take m)
    rw [hP_d2] at e2
    have hQ_src : ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2
        (s.get dst2 ++ (s.get src).take m)).get src = s.get src := by
      rw [Compile.get_set_ne _ dst2 _ src (by rw [hlenP]; exact hdst2) hsd2,
          Compile.get_set_ne s dst1 _ src hdst1 hsd1]
    have e3 := State.size_set_add ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2
      (s.get dst2 ++ (s.get src).take m)) src ((s.get src).drop m)
    rw [hQ_src] at e3
    simp only [hstdef, List.length_append, htake, hdrop] at e1 e2 e3 ⊢
    omega
  have hTlen : ∀ j, j ≤ n → (T j).2.2.length = L + 2 * (n - j) := by
    intro j hj
    simp only [hTdef, List.length_append, List.length_replicate]
    rw [Compile.encodeTape_length, hsize_st (n - j) (Nat.sub_le n j), hlen_st,
        hLdef, List.length_append, Compile.encodeTape_length]
    omega
  have hnL : n + 2 ≤ L := by
    have hsize := State.size_set_add s src ([] : List Nat)
    simp only [List.length_nil, Nat.add_zero] at hsize
    rw [hLdef, List.length_append, Compile.encodeTape_length]
    omega
  have hT_lt : ∀ j x, x ∈ (T j).2.2 → x < 4 := by
    intro j x hx
    simp only [hTdef] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four _ (hbit_st _) x hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hres x hx).1
      · rw [List.mem_replicate] at hx; omega
  have h_sym : ∀ m v, currentTapeSymbol (T m) = some v → v < (Compile.moveBody2RawTM src dst1 dst2).sig := by
    intro m v hv
    have hsig : (Compile.moveBody2RawTM src dst1 dst2).sig = 4 := by
      show (branchComposeFlatTM _ _ _ _ _).sig = 4
      rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig, Compile.moveContent2TM_sig]; rfl
    rw [hsig]
    have hmem : v ∈ (T m).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_lt m v hmem
  -- done branch: `T 0`, register `src` empty.
  have hdone := Compile.moveBody2_done_run (st n) src dst1 dst2 (res_in ++ List.replicate n 0)
    (by rw [hlen_st]; exact hsrc) (hbit_st n)
    (by rw [hget_src_st, hn]; exact List.drop_length)
    (Compile.ValidResidue_append_replicate_zero res_in n hres)
  obtain ⟨tDone, hdr, hdt, hdb⟩ := hdone
  have hT0 : T 0 = ([], 0, Compile.encodeTape (st n) ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero]
  have h_done_bnd : tDone + 1 ≤ 36 * L + 39 := by
    have hlen0 := hTlen 0 (Nat.zero_le n)
    simp only [hTdef, Nat.sub_zero] at hlen0
    rw [hlen0] at hdb
    have : n ≤ L := by omega
    omega
  -- per-iteration move: `T (j+1) → T j` for `j < n`, moving one bit to both dsts.
  have hiter_ex : ∀ j, j < n → ∃ t,
      runFlatTM t (Compile.moveBody2RawTM src dst1 dst2)
          { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBody2RawTM_exitLoop src dst1 dst2, tapes := [T j] } ∧
      (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
            { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] } = some ck →
        ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
        ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
        haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false) ∧
      t ≤ 36 * L + 38 := by
    intro j hj
    set m := n - (j + 1) with hm
    have hmn : m < n := by omega
    have hm1 : m + 1 = n - j := by omega
    have hmlen : m < (s.get src).length := by rw [← hn]; exact hmn
    have hdc : (s.get src).drop m = (s.get src)[m] :: (s.get src).drop (m + 1) :=
      List.drop_eq_getElem_cons hmlen
    have hb1 : (s.get src)[m] ≤ 1 := hv_bit _ (List.getElem_mem hmlen)
    have hsrc_cons : (st m).get src = (s.get src)[m] :: (s.get src).drop (m + 1) := by
      rw [hget_src_st]; exact hdc
    obtain ⟨t, hr, ht, hbnd⟩ := Compile.moveBody2_delete_run (st m) src dst1 dst2 ((s.get src)[m])
      ((s.get src).drop (m + 1)) hsrc_cons hb1 hsd1 hsd2 hd12 (hbit_st m)
      (by rw [hlen_st]; exact hsrc) (by rw [hlen_st]; exact hdst1) (by rw [hlen_st]; exact hdst2)
      (res_in ++ List.replicate m 0)
      (Compile.ValidResidue_append_replicate_zero res_in m hres)
    -- bridge the dual-move output to `T j` (3-register reshuffle).
    have hsrcQ : ∀ (m' : Nat), src < ((s.set dst1 (s.get dst1 ++ (s.get src).take m')).set dst2
        (s.get dst2 ++ (s.get src).take m')).length := fun m' => by rw [hlenQ]; exact hsrc
    have hstate_eq : (((st m).set src ((s.get src).drop (m + 1))).set dst1
          ((st m).get dst1 ++ [(s.get src)[m]])).set dst2 ((st m).get dst2 ++ [(s.get src)[m]])
        = st (n - j) := by
      rw [hget_dst1_st, hget_dst2_st, ← hm1,
          show (s.get dst1 ++ (s.get src).take m) ++ [(s.get src)[m]]
            = s.get dst1 ++ (s.get src).take (m + 1) from by
            rw [List.append_assoc, List.take_succ_eq_append_getElem hmlen],
          show (s.get dst2 ++ (s.get src).take m) ++ [(s.get src)[m]]
            = s.get dst2 ++ (s.get src).take (m + 1) from by
            rw [List.append_assoc, List.take_succ_eq_append_getElem hmlen]]
      simp only [hstdef]
      -- normalize LHS to `((s.set dst1 X).set dst2 Y).set src Z`.
      rw [Compile.set_set _ src _ _ (hsrcQ m)]
      rw [Compile.set_comm _ dst1 dst2 _ _ (by rw [Compile.length_set _ src _ (hsrcQ m), hlenQ]; exact hdst1)
            (by rw [Compile.length_set _ src _ (hsrcQ m), hlenQ]; exact hdst2) hd12]
      rw [Compile.set_comm _ src dst2 _ _ (hsrcQ m)
            (by rw [hlenQ]; exact hdst2) hsd2]
      rw [Compile.set_set _ dst2 _ _ (by rw [hlenP]; exact hdst2)]
      rw [Compile.set_comm _ src dst1 _ _ (by rw [Compile.length_set _ dst2 _ (by rw [hlenP]; exact hdst2), hlenP]; exact hsrc)
            (by rw [Compile.length_set _ dst2 _ (by rw [hlenP]; exact hdst2), hlenP]; exact hdst1) hsd1]
      rw [Compile.set_comm _ dst2 dst1 _ _ (by rw [hlenP]; exact hdst2)
            (by rw [hlenP]; exact hdst1) (Ne.symm hd12)]
      rw [Compile.set_set _ dst1 _ _ hdst1]
    have hres_eq : (res_in ++ List.replicate m 0) ++ [0] = res_in ++ List.replicate (n - j) 0 := by
      rw [List.append_assoc, ← List.replicate_succ', hm1]
    rw [hstate_eq, hres_eq] at hr
    have hlenj := hTlen (j + 1) (by omega)
    simp only [hTdef] at hlenj
    rw [show n - (j + 1) = m from rfl] at hlenj
    rw [hlenj] at hbnd
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact hr
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact ht
    · have : m ≤ n := by omega
      omega
  set tIter : Nat → Nat := fun j => if hj : j < n then (hiter_ex j hj).choose else 0 with htIter
  have h_done_full :
      runFlatTM tDone (Compile.moveBody2RawTM src dst1 dst2)
          { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T 0] }
        = some { state_idx := Compile.moveBody2RawTM_exitDone src dst1 dst2, tapes := [T 0] } ∧
      (∀ k, k < tDone → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false) := by
    refine ⟨?_, ?_⟩
    · rw [hBstart, hT0]; exact hdr
    · rw [hBstart, hT0]; exact hdt
  have h_iter_full : ∀ j, j < n →
      runFlatTM (tIter j) (Compile.moveBody2RawTM src dst1 dst2)
          { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBody2RawTM_exitLoop src dst1 dst2, tapes := [T j] } ∧
      (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false) := by
    intro j hj
    have hspec := (hiter_ex j hj).choose_spec
    simp only [htIter, dif_pos hj]
    exact ⟨hspec.1, hspec.2.1⟩
  have h_iter_bnd : ∀ j, j < n → tIter j + 1 ≤ 36 * L + 39 := by
    intro j hj
    have hb := (hiter_ex j hj).choose_spec.2.2
    simp only [htIter, dif_pos hj]
    omega
  have hmain := loopTM_run (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)
    (Compile.moveBody2RawTM_valid src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_lt src dst1 dst2) (Compile.moveBody2RawTM_exitLoop_lt src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_ne_exitLoop src dst1 dst2) T h_sym tIter tDone h_done_full n h_iter_full
  have hmain_traj := loopTM_no_early_halt (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)
    (Compile.moveBody2RawTM_valid src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_lt src dst1 dst2) (Compile.moveBody2RawTM_exitLoop_lt src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_ne_exitLoop src dst1 dst2) T h_sym tIter tDone h_done_full n h_iter_full
  have hTn : T n = ([], 0, Compile.encodeTape s ++ res_in) := by
    simp only [hTdef, Nat.sub_self]
    rw [hstdef]
    simp only [List.take_zero, List.drop_zero, List.append_nil, List.replicate_zero]
    rw [Compile.set_get_self s dst1 hdst1, Compile.set_get_self s dst2 hdst2,
        Compile.set_get_self s src hsrc]
  have hTfin : T 0 = ([], 0, Compile.encodeTape
      (((s.set dst1 (s.get dst1 ++ s.get src)).set dst2 (s.get dst2 ++ s.get src)).set src [])
      ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero, hstdef]
    rw [show (s.get src).take n = s.get src from by rw [hn]; exact List.take_length,
        show (s.get src).drop n = [] from by rw [hn]; exact List.drop_length]
  rw [hBstart, hTn, hTfin] at hmain
  rw [hBstart, hTn] at hmain_traj
  have hMeq : Compile.moveRegion2TM src dst1 dst2
      = loopTM (Compile.moveBody2RawTM src dst1 dst2) (Compile.moveBody2RawTM_exitDone src dst1 dst2)
          (Compile.moveBody2RawTM_exitLoop src dst1 dst2) := rfl
  have hExeq : Compile.moveRegion2TM_exit src dst1 dst2 = (Compile.moveBody2RawTM src dst1 dst2).states := rfl
  have hexit_halt : (Compile.moveRegion2TM src dst1 dst2).halt[(Compile.moveBody2RawTM src dst1 dst2).states]?
      = some true := by
    rw [hMeq]
    show (loopHalt (Compile.moveBody2RawTM src dst1 dst2))[(Compile.moveBody2RawTM src dst1 dst2).states]? = some true
    show (List.replicate (Compile.moveBody2RawTM src dst1 dst2).states false ++ [true])[(Compile.moveBody2RawTM src dst1 dst2).states]?
        = some true
    rw [List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  refine ⟨loopBudget tIter tDone n, ?_, ?_, ?_⟩
  · rw [hMeq, hExeq]; exact hmain
  · intro k hk ck hck
    rw [hMeq] at hck
    have hh := hmain_traj k hk ck hck
    refine ⟨?_, hh⟩
    rw [hExeq]
    rw [hMeq] at hexit_halt
    exact ClearGadget.ne_of_not_halting hexit_halt hh
  · rw [hLdef] at hnL ⊢
    exact le_trans
      (Compile.loopBudget_le tIter tDone (36 * L + 39) n h_done_bnd h_iter_bnd)
      (by rw [← hLdef]; exact Compile.moveBudget2_arith n L (by rw [hLdef]; exact hnL))

/-- **`clearAppendM` run + no-early-halt + budget.** From head `0` on
`encodeTape s ++ res`, clearing register `dst` then appending bit `bit` reaches
the unique exit at head `0` with tape `encodeTape (s.set dst [bit]) ++ res'`
(`res' = res ++ replicate |s.get dst| 0`). The tape length is preserved, so the
append's budget is `≤ 3·L + 8` and the total is `≤ 9·L² + 3·L + 18`. -/
theorem Compile.clearAppendM_run (s : State) (dst : Var) (bit : Nat) (hb : bit ≤ 1)
    (hdst : dst < s.length) (hbit : Compile.BitState s) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.clearAppendM dst (bit + 1) (by omega))
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.clearAppendM_exit dst (bit + 1) (by omega),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [bit])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.clearAppendM dst (bit + 1) (by omega))
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.clearAppendM dst (bit + 1) (by omega)) ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 3 * (Compile.encodeTape s ++ res).length + 18 := by
  set res' := res ++ List.replicate (s.get dst).length 0 with hres'def
  have hmid_bit : Compile.BitState (s.set dst []) :=
    Compile.BitState_set s dst [] hbit hdst (by intro x hx; cases hx)
  have hmid_len : dst < (s.set dst []).length := by
    rw [Compile.length_set s dst [] hdst]; exact hdst
  have hres' : Compile.ValidResidue res' :=
    Compile.ValidResidue_append_replicate_zero res _ hres
  have hget : (s.set dst []).get dst = [] := Compile.get_set_eq s dst [] hdst
  have hset : (s.set dst []).set dst [bit] = s.set dst [bit] := Compile.set_set s dst [] [bit] hdst
  -- tape length preserved across clear: |encodeTape (s.set dst []) ++ res'| = |encodeTape s ++ res|
  have hlen_eq : (Compile.encodeTape (s.set dst []) ++ res').length
      = (Compile.encodeTape s ++ res).length := by
    have hbal := Compile.encodeTape_set_length s dst [] hdst
    simp only [List.length_nil, Nat.add_zero] at hbal
    simp only [hres'def, List.length_append, List.length_replicate]
    omega
  obtain ⟨t1, hrun1, htraj1, hbud1⟩ := Compile.clearRegionTM_run s dst res hdst hbit hres
  obtain ⟨t2, hrun2, htraj2, hbud2⟩ :=
    Compile.opAppendBit_physical_residue bit hb (s.set dst []) dst hmid_bit hmid_len res' hres'
  -- clean the append output tape: (s.set dst []).set dst ([] ++ [bit]) = s.set dst [bit]
  rw [hget, List.nil_append, hset] at hrun2
  -- expose the explicit start config of `opAppendBitRewind` (initFlatConfig form)
  simp only [initFlatConfig, List.map_cons, List.map_nil] at hrun2
  -- `clearRegionTM`'s exit tape is `encodeTape (s.set dst []) ++ res'` (defeq Op.eval)
  have hmid_eval : Op.eval (Op.clear dst) s = s.set dst [] := rfl
  rw [hmid_eval] at hrun1
  -- symbol bound at the seam
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape (s.set dst []) ++ res')
      = some v → v < max (ClearGadget.clearRegionTM dst).sig
        (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M.sig := by
    intro v hv
    have hmax : max (ClearGadget.clearRegionTM dst).sig
        (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M.sig = 4 := by
      rw [ClearGadget.clearRegionTM_sig, (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M_sig]
      rfl
    rw [hmax]
    have hlt : 0 < (Compile.encodeTape (s.set dst []) ++ res').length := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have hcell : (Compile.encodeTape (s.set dst []) ++ res').get ⟨0, hlt⟩ = 3 := rfl
    rw [hcell] at hv
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_cfg_lt : (0 : Nat) < (ClearGadget.clearRegionTM dst).states := by
    rw [ClearGadget.clearRegionTM_states]; exact Nat.succ_pos _
  have hcompose := composeFlatTM_run (ClearGadget.clearRegionTM_valid dst)
    (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M_valid
    (Compile.clearRegionTM_exit_lt dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    h_cfg_lt
    [] 0 (Compile.encodeTape (s.set dst []) ++ res') h_sym
    hrun1
    (fun k hk ck hck => htraj1 k hk ck hck)
    hrun2
    (Compile.haltingStateReached_of_halt (Compile.opAppendBitRewind (bit + 1) (by omega) dst).exit_is_halt)
  have hcompose_traj := composeFlatTM_no_early_halt (ClearGadget.clearRegionTM_valid dst)
    (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M_valid
    (Compile.clearRegionTM_exit_lt dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    h_cfg_lt
    [] 0 (Compile.encodeTape (s.set dst []) ++ res') h_sym
    hrun1
    (fun k hk ck hck => htraj1 k hk ck hck)
    (fun k hk ck hck => (htraj2 k hk ck hck).2)
  refine ⟨t1 + 1 + t2, ?_, ?_, ?_⟩
  · rw [Compile.clearAppendM, Compile.clearAppendM_exit, Nat.add_comm (ClearGadget.clearRegionTM dst).states]
    exact hcompose.1
  · intro k hk ck hck
    rw [Compile.clearAppendM] at hck ⊢
    exact hcompose_traj k hk ck hck
  · -- budget: t1 ≤ 9L²+9, t2 ≤ 3L+8 (length preserved), total ≤ 9L²+3L+18
    have hb2' : t2 ≤ 3 * (Compile.encodeTape s ++ res).length + 8 := by
      rw [← hlen_eq]; exact hbud2
    omega

/-- **`nonEmptyBranchBody` run + no-early-halt + budget.** From the `navigateAndTest`
exit config (head on register `src`'s first cell), rewind to the leading sentinel,
then clear-and-append. Exits at head `0` with `encodeTape (s.set dst [bit]) ++ res'`. -/
theorem Compile.nonEmptyBranchBody_run (s : State) (dst src : Var) (bit : Nat) (hb : bit ≤ 1)
    (hdst : dst < s.length) (hsrc : src < s.length) (hbit : Compile.BitState s)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.nonEmptyBranchBody dst (bit + 1) (by omega))
          { state_idx := 0,
            tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst (bit + 1) (by omega),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [bit])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst (bit + 1) (by omega))
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst (bit + 1) (by omega)) ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 4 * (Compile.encodeTape s ++ res).length + 19 := by
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set rest := Compile.encodeRegs s ++ [Compile.endMark] ++ res with hrestdef
  have htape_cons : Compile.encodeTape s ++ res = (3 : Nat) :: rest := by
    rw [hrestdef, Compile.encodeTape]; simp only [Compile.endMark, List.cons_append, List.append_assoc]
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  -- rewind run + trajectory
  have hcells : ∀ i, i < H → ∃ (h : i < rest.length),
      rest.get ⟨i, h⟩ < 4 ∧ rest.get ⟨i, h⟩ ≠ 3 := by
    intro i hi
    have hi_regs : i < (Compile.encodeRegs s).length := lt_of_lt_of_le hi hH_le_regs
    have hi_rest : i < rest.length := by
      rw [hrestdef, List.length_append, List.length_append]; omega
    have hget : rest.get ⟨i, hi_rest⟩ = (Compile.encodeRegs s).get ⟨i, hi_regs⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      have hget? : rest[i]? = (Compile.encodeRegs s)[i]? := by
        conv_lhs => rw [hrestdef]
        rw [List.getElem?_append_left (by rw [List.length_append]; omega),
            List.getElem?_append_left hi_regs]
      rw [List.getElem?_eq_getElem hi_rest, List.getElem?_eq_getElem hi_regs] at hget?
      exact Option.some.inj hget?
    refine ⟨hi_rest, ?_, ?_⟩
    · rw [hget]; exact Compile.encodeRegs_lt_four s hbit _ (List.get_mem _ _)
    · rw [hget]; exact Compile.encodeRegs_no_endMark s hbit _ (List.get_mem _ _)
  have hH_le_rest : H ≤ rest.length := by
    rw [hrestdef, List.length_append, List.length_append]; omega
  -- `3 :: rest` is defeq `encodeTape s ++ res` (cons_append), so `hrw` plugs in directly.
  have hrw := ScanLeft.rewindToStart_run 4 3 [] rest H hH_le_rest hcells
  have hrw_traj := ScanLeft.rewindToStart_traj 4 3 [] rest H hH_le_rest hcells
  -- clearAppend run (head 0); convert its start to M₂.start form
  obtain ⟨t2, hca_run, hca_traj, hca_bud⟩ := Compile.clearAppendM_run s dst bit hb hdst hbit res hres
  have hca_start : (Compile.clearAppendM dst (bit + 1) (by omega)).start = 0 := by
    rw [Compile.clearAppendM, composeFlatTM_start]; exact ClearGadget.clearRegionTM_start dst
  have hca_run' : runFlatTM t2 (Compile.clearAppendM dst (bit + 1) (by omega))
      { state_idx := (Compile.clearAppendM dst (bit + 1) (by omega)).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.clearAppendM_exit dst (bit + 1) (by omega),
               tapes := [([], 0, Compile.encodeTape (s.set dst [bit])
                          ++ (res ++ List.replicate (s.get dst).length 0))] } := by
    rw [hca_start]; exact hca_run
  have hca_traj' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k (Compile.clearAppendM dst (bit + 1) (by omega))
        { state_idx := (Compile.clearAppendM dst (bit + 1) (by omega)).start,
          tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.clearAppendM dst (bit + 1) (by omega)) ck = false := by
    rw [hca_start]; exact hca_traj
  -- symbol bound at the rewind exit head (head 0 = leading sentinel)
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (ScanLeft.scanLeftUntilTM 4 3).sig
        (Compile.clearAppendM dst (bit + 1) (by omega)).sig := by
    intro v hv
    have hmax : max (ScanLeft.scanLeftUntilTM 4 3).sig
        (Compile.clearAppendM dst (bit + 1) (by omega)).sig = 4 := by
      rw [Compile.clearAppendM_sig]; rfl
    rw [hmax]
    have hlt : 0 < (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have hcell : (Compile.encodeTape s ++ res).get ⟨0, hlt⟩ = 3 := rfl
    rw [hcell] at hv
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_cfg_lt : (0 : Nat) < (ScanLeft.scanLeftUntilTM 4 3).states := by decide
  have hcompose := composeFlatTM_run (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (Compile.clearAppendM_valid dst (bit + 1) (by omega)) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck) hca_run'
    (Compile.haltingStateReached_of_halt (Compile.clearAppendM_exit_is_halt dst (bit + 1) (by omega)))
  have hcompose_traj := composeFlatTM_no_early_halt (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (Compile.clearAppendM_valid dst (bit + 1) (by omega)) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck)
    (fun k hk ck hck => hca_traj' k hk ck hck)
  refine ⟨(H + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [Compile.nonEmptyBranchBody, Compile.nonEmptyBranchBody_exit,
        Nat.add_comm (ScanLeft.scanLeftUntilTM 4 3).states]
    exact hcompose.1
  · intro k hk ck hck
    rw [Compile.nonEmptyBranchBody] at hck ⊢
    exact hcompose_traj k hk ck hck
  · -- budget: rewind H+1 ≤ L, clearAppend ≤ 9L²+3L+18 ⇒ total ≤ 9L²+4L+19
    have hH_le_L : H + 1 ≤ (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]
      have h1 := hH_le_regs
      have h2 := Compile.encodeRegs_length s
      omega
    omega

/-- **`opNonEmpty` run + trajectory + budget (the residue contract for `nonEmpty`).**
Navtest `src`; the answer bit (`1` if non-empty else `0`) is written to a freshly
cleared register `dst`; the two branches merge through `joinTwoHalts`. Correct for
`dst = src` (the read precedes the clear). -/
theorem Compile.opNonEmpty_run (s : State) (dst src : Var) (res_in : List Nat)
    (hbit : Compile.BitState s) (hdst : dst < s.length) (hsrc : src < s.length)
    (hres_in : Compile.ValidResidue res_in) :
    ∃ t,
      runFlatTM t (Compile.opNonEmpty dst src).M
          (initFlatConfig (Compile.opNonEmpty dst src).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opNonEmpty dst src).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval (Op.nonEmpty dst src) s)
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opNonEmpty dst src).M
            (initFlatConfig (Compile.opNonEmpty dst src).M [Compile.encodeTape s ++ res_in]) = some ck →
        ck.state_idx ≠ (Compile.opNonEmpty dst src).exit ∧
        haltingStateReached (Compile.opNonEmpty dst src).M ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
            + 9 * (Compile.encodeTape s ++ res_in).length + 30 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.nonEmptyRawM dst src with hrawdef
  set h1 := Compile.nonEmptyRawM_h1 dst src with hh1def
  set h2 := Compile.nonEmptyRawM_h2 dst src with hh2def
  have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
      (Compile.nonEmptyBranchBody dst 2 (by decide)) (Compile.nonEmptyBranchBody dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content src)
      (ClearGadget.navigateAndTestTM_exit_delim src) = raw := rfl
  -- machine boilerplate: init config, exit, M.
  have hMstart : (Compile.opNonEmpty dst src).M.start = 0 := by
    show (joinTwoHalts raw h1 h2).start = 0
    rw [joinTwoHalts_start, hrawdef, Compile.nonEmptyRawM, branchComposeFlatTM_start]
    exact ClearGadget.navigateAndTestTM_start src
  have hinit : initFlatConfig (Compile.opNonEmpty dst src).M [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hMstart, List.map_cons, List.map_nil]
  have hMeq : (Compile.opNonEmpty dst src).M = joinTwoHalts raw h1 h2 := rfl
  have hexit : (Compile.opNonEmpty dst src).exit = h1 := rfl
  rw [hinit, hMeq, hexit]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    with hcfg0
  -- length facts.
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res_in).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  have hnav_le : ClearGadget.navSteps skipped ≤ 2 * (Compile.encodeRegs s).length := by
    have := ClearGadget.navSteps_le skipped
    rw [hHdef] at hH_le_regs; omega
  -- the branch-tape symbol bound (head H lands inside `encodeTape s`).
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res_in)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.nonEmptyBranchBody dst 2 (by decide)).sig
            (Compile.nonEmptyBranchBody dst 1 (by decide)).sig) := by
    intro v hv
    have hHlt2 : H < (Compile.encodeTape s).length := by
      rw [Compile.encodeTape_length]
      have h := hH_le_regs
      rw [Compile.encodeRegs_length] at h
      omega
    have hHlt : H < (Compile.encodeTape s ++ res_in).length := by
      rw [List.length_append]; omega
    rw [currentTapeSymbol_in_range hHlt] at hv
    have hmem : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ ∈ Compile.encodeTape s := by
      rw [List.get_eq_getElem, List.getElem_append_left hHlt2]; exact List.getElem_mem hHlt2
    have hv4 : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ < 4 :=
      Compile.encodeTape_lt_four s hbit _ hmem
    have : v < (ClearGadget.navigateAndTestTM src).sig := by
      rw [ClearGadget.navigateAndTestTM_sig, ← Option.some.inj hv]; exact hv4
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hbstart : ∀ ins (h : ins < 4), (Compile.nonEmptyBranchBody dst ins h).start = 0 := by
    intro ins h; rw [Compile.nonEmptyBranchBody, composeFlatTM_start]; rfl
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hh1_is := Compile.nonEmptyRawM_h1_is_halt dst src
  have hh2_is := Compile.nonEmptyRawM_h2_is_halt dst src
  have hh_ne := Compile.nonEmptyRawM_h1_ne_h2 dst src
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  by_cases he : s.get src = []
  · -- DELIM: answer bit 0, Op.eval = s.set dst [0]; raw reaches h2, bridges to h1.
    have hisE : Op.eval (Op.nonEmpty dst src) s = s.set dst [0] := by
      show s.set dst (if (s.get src).isEmpty then [0] else [1]) = s.set dst [0]
      rw [he]; rfl
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 0 (by omega) hdst hsrc hbit res_in hres_in
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 1 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 1 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [0])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 1 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 1 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 1 (by decide)) ck = false := by
      rw [hbstart 1 (by decide)]; exact hbody_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 1 (by decide)))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody_traj'
    -- recognise the branch machine/state as raw/h2.
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 1 (by decide)
        + ((ClearGadget.navigateAndTestTM src).states
            + (Compile.nonEmptyBranchBody dst 2 (by decide)).states) = h2 := by
      rw [hh2def, Compile.nonEmptyRawM_h2]; omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (s.set dst [0]) ++ (res_in ++ List.replicate (s.get dst).length 0)) 0
      hneg.1
      (fun k hk ck hck => hneg_traj k hk ck hck)
      hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (s.set dst [0]) ++ (res_in ++ List.replicate (s.get dst).length 0))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.nonEmptyRawM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega
  · -- CONTENT: answer bit 1, Op.eval = s.set dst [1]; raw reaches h1 directly.
    have hisE : Op.eval (Op.nonEmpty dst src) s = s.set dst [1] := by
      show s.set dst (if (s.get src).isEmpty then [0] else [1]) = s.set dst [1]
      have : (s.get src).isEmpty = false := by
        cases hsr : s.get src with
        | nil => exact absurd hsr he
        | cons _ _ => rfl
      rw [this]; rfl
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 1 (by omega) hdst hsrc hbit res_in hres_in
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 2 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 2 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [1])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 2 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 2 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 2 (by decide)) ck = false := by
      rw [hbstart 2 (by decide)]; exact hbody_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 2 (by decide)))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody_traj'
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 2 (by decide)
        + (ClearGadget.navigateAndTestTM src).states = h1 := by
      rw [hh1def, Compile.nonEmptyRawM_h1]; omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (s.set dst [1]) ++ (res_in ++ List.replicate (s.get dst).length 0))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega

/-- **`clearOnlyBranchBody` run + no-early-halt + budget.** From the navtest exit
config (head on register `src`'s first cell), rewind to the leading sentinel, then
clear `dst`. Exits at head `0` with `encodeTape (s.set dst []) ++ res'`. Mirror of
`nonEmptyBranchBody_run` with `clearRegionTM` in place of `clearAppendM`. -/
theorem Compile.clearOnlyBranchBody_run (s : State) (dst src : Var)
    (hdst : dst < s.length) (hsrc : src < s.length) (hbit : Compile.BitState s)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.clearOnlyBranchBody dst)
          { state_idx := 0,
            tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.clearOnlyBranchBody_exit dst,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.clearOnlyBranchBody dst)
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.clearOnlyBranchBody dst) ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 4 * (Compile.encodeTape s ++ res).length + 19 := by
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set rest := Compile.encodeRegs s ++ [Compile.endMark] ++ res with hrestdef
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  have hcells : ∀ i, i < H → ∃ (h : i < rest.length),
      rest.get ⟨i, h⟩ < 4 ∧ rest.get ⟨i, h⟩ ≠ 3 := by
    intro i hi
    have hi_regs : i < (Compile.encodeRegs s).length := lt_of_lt_of_le hi hH_le_regs
    have hi_rest : i < rest.length := by
      rw [hrestdef, List.length_append, List.length_append]; omega
    have hget : rest.get ⟨i, hi_rest⟩ = (Compile.encodeRegs s).get ⟨i, hi_regs⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      have hget? : rest[i]? = (Compile.encodeRegs s)[i]? := by
        conv_lhs => rw [hrestdef]
        rw [List.getElem?_append_left (by rw [List.length_append]; omega),
            List.getElem?_append_left hi_regs]
      rw [List.getElem?_eq_getElem hi_rest, List.getElem?_eq_getElem hi_regs] at hget?
      exact Option.some.inj hget?
    refine ⟨hi_rest, ?_, ?_⟩
    · rw [hget]; exact Compile.encodeRegs_lt_four s hbit _ (List.get_mem _ _)
    · rw [hget]; exact Compile.encodeRegs_no_endMark s hbit _ (List.get_mem _ _)
  have hH_le_rest : H ≤ rest.length := by
    rw [hrestdef, List.length_append, List.length_append]; omega
  have hrw := ScanLeft.rewindToStart_run 4 3 [] rest H hH_le_rest hcells
  have hrw_traj := ScanLeft.rewindToStart_traj 4 3 [] rest H hH_le_rest hcells
  obtain ⟨t2, hcl_run, hcl_traj, hcl_bud⟩ := Compile.clearRegionTM_run s dst res hdst hbit hres
  have hcl_eval : Op.eval (Op.clear dst) s = s.set dst [] := rfl
  rw [hcl_eval] at hcl_run
  have hcl_start : (ClearGadget.clearRegionTM dst).start = 0 := ClearGadget.clearRegionTM_start dst
  have hcl_run' : runFlatTM t2 (ClearGadget.clearRegionTM dst)
      { state_idx := (ClearGadget.clearRegionTM dst).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.clearRegionTM_exit dst,
               tapes := [([], 0, Compile.encodeTape (s.set dst [])
                          ++ (res ++ List.replicate (s.get dst).length 0))] } := by
    rw [hcl_start]; exact hcl_run
  have hcl_traj' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k (ClearGadget.clearRegionTM dst)
        { state_idx := (ClearGadget.clearRegionTM dst).start,
          tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (ClearGadget.clearRegionTM dst) ck = false := by
    rw [hcl_start]; intro k hk ck hck; exact (hcl_traj k hk ck hck).2
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (ScanLeft.scanLeftUntilTM 4 3).sig (ClearGadget.clearRegionTM dst).sig := by
    intro v hv
    have hmax : max (ScanLeft.scanLeftUntilTM 4 3).sig (ClearGadget.clearRegionTM dst).sig = 4 := by
      rw [ClearGadget.clearRegionTM_sig]; rfl
    rw [hmax]
    have hlt : 0 < (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have hcell : (Compile.encodeTape s ++ res).get ⟨0, hlt⟩ = 3 := rfl
    rw [hcell] at hv
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_cfg_lt : (0 : Nat) < (ScanLeft.scanLeftUntilTM 4 3).states := by decide
  have hcompose := composeFlatTM_run (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (ClearGadget.clearRegionTM_valid dst) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck) hcl_run'
    (Compile.haltingStateReached_of_halt (Compile.opClear dst).exit_is_halt)
  have hcompose_traj := composeFlatTM_no_early_halt (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (ClearGadget.clearRegionTM_valid dst) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck)
    (fun k hk ck hck => hcl_traj' k hk ck hck)
  refine ⟨(H + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [Compile.clearOnlyBranchBody, Compile.clearOnlyBranchBody_exit,
        Nat.add_comm (ScanLeft.scanLeftUntilTM 4 3).states]
    exact hcompose.1
  · intro k hk ck hck
    rw [Compile.clearOnlyBranchBody] at hck ⊢
    exact hcompose_traj k hk ck hck
  · have hH_le_L : H + 1 ≤ (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]
      have h1 := hH_le_regs
      have h2 := Compile.encodeRegs_length s
      omega
    omega

/-- **`opInnerBit` run + trajectory + budget.** From the navtest content exit
(head on `src`'s first cell, value `b+1`), `bitReadTM` reads the bit and writes
`[b]` to a freshly-cleared `dst`. The two `bitReadTM` exits merge via
`joinTwoHalts`. Requires `src` non-empty (`s.get src = b :: r`). -/
theorem Compile.opInnerBit_run (s : State) (dst src : Var) (b : Nat) (r : List Nat)
    (hbr : s.get src = b :: r) (hb1 : b ≤ 1)
    (hbit : Compile.BitState s) (hdst : dst < s.length) (hsrc : src < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.opInnerBit dst).M
          { state_idx := 0,
            tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := (Compile.opInnerBit dst).exit,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [b])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opInnerBit dst).M
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ (Compile.opInnerBit dst).exit ∧
        haltingStateReached (Compile.opInnerBit dst).M ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 5 * (Compile.encodeTape s ++ res).length + 24 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.innerBitRawM dst with hrawdef
  set h1 := Compile.innerBitRawM_h1 dst with hh1def
  set h2 := Compile.innerBitRawM_h2 dst with hh2def
  have hraweq : branchComposeFlatTM Compile.bitReadTM
      (Compile.nonEmptyBranchBody dst 2 (by decide)) (Compile.nonEmptyBranchBody dst 1 (by decide))
      Compile.bitReadTM_exit_b1 Compile.bitReadTM_exit_b0 = raw := rfl
  have hMeq : (Compile.opInnerBit dst).M = joinTwoHalts raw h1 h2 := rfl
  have hexit : (Compile.opInnerBit dst).exit = h1 := rfl
  rw [hMeq, hexit]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    with hcfg0
  -- length facts.
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  -- content decomposition (`src` nonempty)
  set tail' := Compile.shiftReg r ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src hsrc
    rw [← hskdef] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg r := by
      rw [hbr]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hHlt : H < (Compile.encodeTape s ++ res).length := by
    rw [hdecomp, hHdef]; simp only [List.length_cons, List.length_append]; omega
  have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = b + 1 := by
    have h? : (Compile.encodeTape s ++ res)[H]? = some (b + 1) := by
      rw [hdecomp, hHdef,
          show ((3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail'))
            = ((3 : Nat) :: AppendGadget.regBlocks skipped) ++ ((b + 1) :: tail') from by simp,
          List.getElem?_append_right (by simp only [List.length_cons]; omega),
          show 1 + (AppendGadget.regBlocks skipped).length
            - ((3 : Nat) :: AppendGadget.regBlocks skipped).length = 0 from by
              simp only [List.length_cons]; omega]
      rfl
    rw [List.getElem?_eq_getElem hHlt] at h?
    rw [List.get_eq_getElem]; exact Option.some.inj h?
  -- symbol bound at head H (cell value `b+1 < 4`).
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max Compile.bitReadTM.sig
          (max (Compile.nonEmptyBranchBody dst 2 (by decide)).sig
            (Compile.nonEmptyBranchBody dst 1 (by decide)).sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    have : v = b + 1 := (Option.some.inj hv).symm
    rw [Compile.bitReadTM_sig]
    have : v < 4 := by omega
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < Compile.bitReadTM.states := by rw [Compile.bitReadTM_states]; omega
  have hbstart : ∀ ins (h : ins < 4), (Compile.nonEmptyBranchBody dst ins h).start = 0 := by
    intro ins h; rw [Compile.nonEmptyBranchBody, composeFlatTM_start]; rfl
  have hexit_neq : Compile.bitReadTM_exit_b1 ≠ Compile.bitReadTM_exit_b0 := by decide
  have hep_lt : Compile.bitReadTM_exit_b1 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide
  have hen_lt : Compile.bitReadTM_exit_b0 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide
  have hh1_is := Compile.innerBitRawM_h1_is_halt dst
  have hh2_is := Compile.innerBitRawM_h2_is_halt dst
  have hh_ne := Compile.innerBitRawM_h1_ne_h2 dst
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  -- the `bitReadTM` test run + trajectory (reads cell `b+1` at head H).
  have htest_run := Compile.bitReadTM_run b hb1 [] (Compile.encodeTape s ++ res) H hHlt hcellH
  have htest_traj : ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.bitReadTM cfg0 = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧ ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧
      haltingStateReached Compile.bitReadTM ck = false := by
    intro k hk ck hck
    obtain ⟨h0, h1', hh⟩ := Compile.bitReadTM_no_early_halt [] (Compile.encodeTape s ++ res) H k hk ck hck
    exact ⟨h1', h0, hh⟩
  interval_cases b
  · -- bit 0 (cell value 1): neg branch, body `dst 1` writes `[0]`; demoted exit.
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 0 (by omega) hdst hsrc hbit res hres
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 1 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 1 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [0])
                            ++ (res ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 1 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 1 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 1 (by decide)) ck = false := by
      rw [hbstart 1 (by decide)]; exact hbody_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 1 (by decide)))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody_traj'
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 1 (by decide)
        + (Compile.bitReadTM.states + (Compile.nonEmptyBranchBody dst 2 (by decide)).states) = h2 := by
      rw [hh2def, Compile.innerBitRawM_h2]; omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (s.set dst [0]) ++ (res ++ List.replicate (s.get dst).length 0)) 0
      hneg.1
      (fun k hk ck hck => hneg_traj k hk ck hck)
      hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (s.set dst [0]) ++ (res ++ List.replicate (s.get dst).length 0))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.innerBitRawM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hb := hbody_bud
    have hL := hLge
    omega
  · -- bit 1 (cell value 2): pos branch, body `dst 2` writes `[1]`; kept exit.
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 1 (by omega) hdst hsrc hbit res hres
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 2 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 2 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [1])
                            ++ (res ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 2 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 2 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 2 (by decide)) ck = false := by
      rw [hbstart 2 (by decide)]; exact hbody_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 2 (by decide)))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody_traj'
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 2 (by decide)
        + Compile.bitReadTM.states = h1 := by
      rw [hh1def, Compile.innerBitRawM_h1]; omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (s.set dst [1]) ++ (res ++ List.replicate (s.get dst).length 0))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hb := hbody_bud
    have hL := hLge
    omega

/-- **`opHead` run + trajectory + budget (the residue contract for `head`).**
Navtest `src`; on content, `opInnerBit` writes `[first bit]`; on delim,
`clearOnlyBranchBody` writes `[]`. The outer branches merge through `joinTwoHalts`. -/
theorem Compile.opHead_run (s : State) (dst src : Var) (res_in : List Nat)
    (hbit : Compile.BitState s) (hdst : dst < s.length) (hsrc : src < s.length)
    (hres_in : Compile.ValidResidue res_in) :
    ∃ t,
      runFlatTM t (Compile.opHead dst src).M
          (initFlatConfig (Compile.opHead dst src).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opHead dst src).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval (Op.head dst src) s)
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opHead dst src).M
            (initFlatConfig (Compile.opHead dst src).M [Compile.encodeTape s ++ res_in]) = some ck →
        ck.state_idx ≠ (Compile.opHead dst src).exit ∧
        haltingStateReached (Compile.opHead dst src).M ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
            + 9 * (Compile.encodeTape s ++ res_in).length + 30 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.headRawM dst src with hrawdef
  set h1 := Compile.headRawM_h1 dst src with hh1def
  set h2 := Compile.headRawM_h2 dst src with hh2def
  have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
      (Compile.opInnerBit dst).M (Compile.clearOnlyBranchBody dst)
      (ClearGadget.navigateAndTestTM_exit_content src)
      (ClearGadget.navigateAndTestTM_exit_delim src) = raw := rfl
  have hMstart : (Compile.opHead dst src).M.start = 0 := by
    show (joinTwoHalts raw h1 h2).start = 0
    rw [joinTwoHalts_start, hrawdef, Compile.headRawM, branchComposeFlatTM_start]
    exact ClearGadget.navigateAndTestTM_start src
  have hinit : initFlatConfig (Compile.opHead dst src).M [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hMstart, List.map_cons, List.map_nil]
  have hMeq : (Compile.opHead dst src).M = joinTwoHalts raw h1 h2 := rfl
  have hexit : (Compile.opHead dst src).exit = h1 := rfl
  rw [hinit, hMeq, hexit]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    with hcfg0
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res_in).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  have hnav_le : ClearGadget.navSteps skipped ≤ 2 * (Compile.encodeRegs s).length := by
    have := ClearGadget.navSteps_le skipped
    rw [hHdef] at hH_le_regs; omega
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res_in)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.opInnerBit dst).M.sig (Compile.clearOnlyBranchBody dst).sig) := by
    intro v hv
    have hHlt2 : H < (Compile.encodeTape s).length := by
      rw [Compile.encodeTape_length]
      have h := hH_le_regs
      rw [Compile.encodeRegs_length] at h
      omega
    have hHlt : H < (Compile.encodeTape s ++ res_in).length := by
      rw [List.length_append]; omega
    rw [currentTapeSymbol_in_range hHlt] at hv
    have hmem : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ ∈ Compile.encodeTape s := by
      rw [List.get_eq_getElem, List.getElem_append_left hHlt2]; exact List.getElem_mem hHlt2
    have hv4 : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ < 4 :=
      Compile.encodeTape_lt_four s hbit _ hmem
    have : v < (ClearGadget.navigateAndTestTM src).sig := by
      rw [ClearGadget.navigateAndTestTM_sig, ← Option.some.inj hv]; exact hv4
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hh1_is := Compile.headRawM_h1_is_halt dst src
  have hh2_is := Compile.headRawM_h2_is_halt dst src
  have hh_ne := Compile.headRawM_h1_ne_h2 dst src
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  by_cases he : s.get src = []
  · -- DELIM: Op.eval head = s.set dst []; raw reaches h2 (delim), bridges to h1.
    have hisE : Op.eval (Op.head dst src) s = s.set dst [] := by
      show s.set dst (match s.get src with | [] => [] | x :: _ => [x]) = s.set dst []
      rw [he]
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.clearOnlyBranchBody_run s dst src hdst hsrc hbit res_in hres_in
    have hbody' : runFlatTM t2 (Compile.clearOnlyBranchBody dst)
        { state_idx := (Compile.clearOnlyBranchBody dst).start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := Compile.clearOnlyBranchBody_exit dst,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [show (Compile.clearOnlyBranchBody dst).start = 0 from by
            rw [Compile.clearOnlyBranchBody, composeFlatTM_start]; rfl]
      exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.clearOnlyBranchBody dst)
          { state_idx := (Compile.clearOnlyBranchBody dst).start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.clearOnlyBranchBody dst) ck = false := by
      rw [show (Compile.clearOnlyBranchBody dst).start = 0 from by
            rw [Compile.clearOnlyBranchBody, composeFlatTM_start]; rfl]
      exact hbody_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.clearOnlyBranchBody_exit_is_halt dst))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody_traj'
    have hstate_eq : Compile.clearOnlyBranchBody_exit dst
        + ((ClearGadget.navigateAndTestTM src).states + (Compile.opInnerBit dst).M.states) = h2 := by
      rw [hh2def, Compile.headRawM_h2]; omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (s.set dst []) ++ (res_in ++ List.replicate (s.get dst).length 0)) 0
      hneg.1
      (fun k hk ck hck => hneg_traj k hk ck hck)
      hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (s.set dst []) ++ (res_in ++ List.replicate (s.get dst).length 0))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.headRawM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega
  · -- CONTENT: s.get src = b :: r; opInnerBit writes [b]; raw reaches h1 directly.
    obtain ⟨b, r, hbr⟩ : ∃ b r, s.get src = b :: r := by
      cases hsr : s.get src with
      | nil => exact absurd hsr he
      | cons b r => exact ⟨b, r, rfl⟩
    have hb1 : b ≤ 1 := by
      have hmem : s.get src ∈ s := by
        rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
      exact hbit _ hmem b (by simp [hbr])
    have hisE : Op.eval (Op.head dst src) s = s.set dst [b] := by
      show s.set dst (match s.get src with | [] => [] | x :: _ => [x]) = s.set dst [b]
      rw [hbr]
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.opInnerBit_run s dst src b r hbr hb1 hbit hdst hsrc res_in hres_in
    have hbody' : runFlatTM t2 (Compile.opInnerBit dst).M
        { state_idx := (Compile.opInnerBit dst).M.start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := (Compile.opInnerBit dst).exit,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [b])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [Compile.opInnerBit_start]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.opInnerBit dst).M
          { state_idx := (Compile.opInnerBit dst).M.start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.opInnerBit dst).M ck = false := by
      rw [Compile.opInnerBit_start]; intro k hk ck hck; exact (hbody_traj k hk ck hck).2
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.opInnerBit dst).exit_is_halt)
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody_traj'
    have hstate_eq : (Compile.opInnerBit dst).exit
        + (ClearGadget.navigateAndTestTM src).states = h1 := by
      rw [hh1def, Compile.headRawM_h1]; omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (s.set dst [b]) ++ (res_in ++ List.replicate (s.get dst).length 0))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega

/-! ### Cursor-copy run lemmas (`copy` op, Risk C2 — bottom-up task 1)

The lemma stack for the `#eval`-probe-validated cursor-copy machine
(`probes/CursorCopyProbe.lean`): step lemmas for the two custom machines, the
per-bit pipeline pass (`copyPipe_run`), the loop-body contracts in `loopTM_run`
form (`copyBody_run_iter`/`copyBody_run_done`), the loop (`copyLoop_run`), and
the per-op exact-residue lemma `opCopy_run` consumed by the contract case (and,
with its EXACT residue formula `res ++ replicate |dst₀| 0`, by the future
`compileForBnd` combinator — HANDOFF bottom-up task 2). -/

/-- `markBitTM` on a shifted bit `b+1`: write the mark `3` over it, step to
exit `1+b`, head unchanged. -/
theorem Compile.markBitTM_step (b : Nat) (hb : b ≤ 1) (left right : List Nat)
    (head : Nat) (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = b + 1) :
    stepFlatTM Compile.markBitTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1 + b,
               tapes := [(left, head, right.take head ++ 3 :: right.drop (head + 1))] } := by
  have hsym : currentTapeSymbol (left, head, right) = some (b + 1) := by
    rw [currentTapeSymbol_in_range hlt, hget]
  interval_cases b <;>
    simp_all [stepFlatTM, Compile.markBitTM, Compile.markBitEntry,
      entryMatchesConfig, applyTransitionEntry, tapeStep,
      writeCurrentTapeSymbol, moveTapeHead]

/-- `markBitTM_step` in `runFlatTM` form. -/
theorem Compile.markBitTM_run (b : Nat) (hb : b ≤ 1) (left right : List Nat)
    (head : Nat) (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = b + 1) :
    runFlatTM 1 Compile.markBitTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1 + b,
               tapes := [(left, head, right.take head ++ 3 :: right.drop (head + 1))] } := by
  show (if haltingStateReached Compile.markBitTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.markBitTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.markBitTM cfg') = _
  rw [show haltingStateReached Compile.markBitTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.markBitTM_step b hb left right head hlt hget]
  rfl

/-- `markBitTM` never halts before its single step (state `0` is non-halting). -/
theorem Compile.markBitTM_no_early_halt (left right : List Nat) (head : Nat) :
    ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.markBitTM
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      haltingStateReached Compile.markBitTM ck = false := by
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  simp [runFlatTM] at hck; subst hck; rfl

/-- `restoreStepTM b` at the mark: restore the shifted bit `b+1` and step right. -/
theorem Compile.restoreStepTM_step (b : Nat) (hb : b ≤ 1) (left right : List Nat)
    (head : Nat) (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = 3) :
    stepFlatTM (Compile.restoreStepTM b) { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1,
               tapes := [(left, head + 1,
                          right.take head ++ (b + 1) :: right.drop (head + 1))] } := by
  have hsym : currentTapeSymbol (left, head, right) = some 3 := by
    rw [currentTapeSymbol_in_range hlt, hget]
  interval_cases b <;>
    simp_all [stepFlatTM, Compile.restoreStepTM, Compile.restoreStepEntry,
      entryMatchesConfig, applyTransitionEntry, tapeStep, writeCurrentTapeSymbol,
      moveTapeHead]

/-- `restoreStepTM_step` in `runFlatTM` form. -/
theorem Compile.restoreStepTM_run (b : Nat) (hb : b ≤ 1) (left right : List Nat)
    (head : Nat) (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = 3) :
    runFlatTM 1 (Compile.restoreStepTM b) { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1,
               tapes := [(left, head + 1,
                          right.take head ++ (b + 1) :: right.drop (head + 1))] } := by
  show (if haltingStateReached (Compile.restoreStepTM b)
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM (Compile.restoreStepTM b)
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 0 (Compile.restoreStepTM b) cfg') = _
  rw [show haltingStateReached (Compile.restoreStepTM b)
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.restoreStepTM_step b hb left right head hlt hget]
  rfl

/-- `restoreStepTM` never halts before its single step. -/
theorem Compile.restoreStepTM_no_early_halt (b : Nat) (left right : List Nat) (head : Nat) :
    ∀ k, k < 1 → ∀ ck,
      runFlatTM k (Compile.restoreStepTM b)
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      haltingStateReached (Compile.restoreStepTM b) ck = false := by
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  simp [runFlatTM] at hck; subst hck; rfl

/-! #### Marked-tape structure helpers (cursor-copy lemma stack)

The cursor loop's working tape is `encodeTape (q.set src (w₁ ++ c :: w₂)) ++ res`
(`c = 2` is the mark — encoding to the cell `3` — and `c = b ≤ 1` the restored
bit). The helpers below pin its explicit list shape, length, the mark cell, the
off-mark cell agreement, the interior cell facts (`< 4`, `≠ 3`) the scans need,
and the take/drop re-marking bridge consumed by `markBitTM`/`restoreStepTM`. -/

/-- Explicit shape of the cursor tape with residue: an opaque prefix `X` of
length `1 + |encodeRegs (q.take src)| + |w₁|`, the (shifted) cursor cell
`c + 1`, and an opaque suffix `Z` (independent of `c`). Packaged this way so
`getElem?_append_left/right` rewrites are unambiguous. -/
private theorem Compile.encodeTape_set_cell_res (q : State) (src : Var)
    (hsrc : src < q.length) (w₁ w₂ : List Nat) (c : Nat) (res : List Nat) :
    Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res
      = ((3 : Nat) :: (Compile.encodeRegs (q.take src) ++ Compile.shiftReg w₁))
        ++ ((c + 1) :: (Compile.shiftReg w₂
              ++ (0 :: (Compile.encodeRegs (q.drop (src + 1)) ++ (3 :: res))))) := by
  rw [(Compile.encodeTape_reg_decomp_at q src hsrc).1 (w₁ ++ c :: w₂)]
  rw [show Compile.shiftReg (w₁ ++ c :: w₂)
        = Compile.shiftReg w₁ ++ (c + 1) :: Compile.shiftReg w₂ from by
      simp [Compile.shiftReg]]
  show (Compile.endMark :: _) ++ _ ++ _ = _
  simp [Compile.endMark, List.append_assoc]

/-- Length of the prefix up to the cursor cell. -/
private theorem Compile.cursorPrefix_length (q : State) (src : Var) (w₁ : List Nat) :
    ((3 : Nat) :: (Compile.encodeRegs (q.take src) ++ Compile.shiftReg w₁)).length
      = 1 + (Compile.encodeRegs (q.take src)).length + w₁.length := by
  simp only [List.length_cons, List.length_append, Compile.shiftReg, List.length_map]
  omega

/-- Length of the cursor tape (independent of the cursor cell value `c`). -/
private theorem Compile.encodeTape_set_cell_length (q : State) (src : Var)
    (hsrc : src < q.length) (w₁ w₂ : List Nat) (c : Nat) :
    (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂))).length
      = 1 + (Compile.encodeRegs (q.take src)).length + w₁.length
        + (w₂.length + (Compile.encodeRegs (q.drop (src + 1))).length + 3) := by
  have h := congrArg List.length
    (Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c [])
  rw [List.append_nil] at h
  rw [h]
  simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map,
    List.length_nil]
  omega

/-- The cursor cell itself: cell `1 + |encodeRegs (q.take src)| + |w₁|` of the
cursor tape is the shifted value `c + 1`. -/
private theorem Compile.markedTape_get_mark (q : State) (src : Var) (hsrc : src < q.length)
    (w₁ w₂ : List Nat) (c : Nat) (res : List Nat) :
    ∃ (h : 1 + (Compile.encodeRegs (q.take src)).length + w₁.length
        < (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).length),
      (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).get
          ⟨1 + (Compile.encodeRegs (q.take src)).length + w₁.length, h⟩ = c + 1 := by
  set P := 1 + (Compile.encodeRegs (q.take src)).length + w₁.length with hP
  set X := (3 : Nat) :: (Compile.encodeRegs (q.take src) ++ Compile.shiftReg w₁) with hX
  set Z := (c + 1) :: (Compile.shiftReg w₂
      ++ (0 :: (Compile.encodeRegs (q.drop (src + 1)) ++ (3 :: res)))) with hZ
  have hshape : Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res = X ++ Z :=
    Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c res
  have hXlen : X.length = P := Compile.cursorPrefix_length q src w₁
  have hkey : (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res)[P]?
      = some (c + 1) := by
    rw [hshape, List.getElem?_append_right (by omega), hXlen, Nat.sub_self, hZ,
        List.getElem?_cons_zero]
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hkey
  refine ⟨hlt, ?_⟩
  rw [List.get_eq_getElem]
  exact hget

/-- Off the cursor cell, the cursor tapes for any two cell values agree. -/
private theorem Compile.markedTape_getElem_off (q : State) (src : Var) (hsrc : src < q.length)
    (w₁ w₂ : List Nat) (c c' : Nat) (res : List Nat) :
    ∀ i, i ≠ 1 + (Compile.encodeRegs (q.take src)).length + w₁.length →
      (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res)[i]?
        = (Compile.encodeTape (State.set q src (w₁ ++ c' :: w₂)) ++ res)[i]? := by
  intro i hi
  set P := 1 + (Compile.encodeRegs (q.take src)).length + w₁.length with hP
  set X := (3 : Nat) :: (Compile.encodeRegs (q.take src) ++ Compile.shiftReg w₁) with hX
  set W := Compile.shiftReg w₂
      ++ (0 :: (Compile.encodeRegs (q.drop (src + 1)) ++ (3 :: res))) with hW
  have hXlen : X.length = P := Compile.cursorPrefix_length q src w₁
  rw [Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c res,
      Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c' res, ← hX, ← hW]
  rcases Nat.lt_or_ge i P with hlt | hge
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · have hgt : P < i := lt_of_le_of_ne hge (fun h => hi h.symm)
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hXlen]
    obtain ⟨j, hj⟩ : ∃ j, i - P = j + 1 := ⟨i - P - 1, by omega⟩
    rw [hj, List.getElem?_cons_succ, List.getElem?_cons_succ]

/-- **Re-marking bridge**: overwriting the cursor cell of the cursor tape with
`c' + 1` (the take/cons/drop form `markBitTM`/`restoreStepTM` produce) yields
the cursor tape for `c'`. -/
private theorem Compile.markedTape_take_drop (q : State) (src : Var) (hsrc : src < q.length)
    (w₁ w₂ : List Nat) (c c' : Nat) (res : List Nat) :
    (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).take
        (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
      ++ (c' + 1) :: (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).drop
        (1 + (Compile.encodeRegs (q.take src)).length + w₁.length + 1)
      = Compile.encodeTape (State.set q src (w₁ ++ c' :: w₂)) ++ res := by
  set P := 1 + (Compile.encodeRegs (q.take src)).length + w₁.length with hP
  set X := (3 : Nat) :: (Compile.encodeRegs (q.take src) ++ Compile.shiftReg w₁) with hX
  set W := Compile.shiftReg w₂
      ++ (0 :: (Compile.encodeRegs (q.drop (src + 1)) ++ (3 :: res))) with hW
  have hXlen : X.length = P := Compile.cursorPrefix_length q src w₁
  rw [Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c res,
      Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c' res, ← hX, ← hW]
  have htake : (X ++ (c + 1) :: W).take P = X := by
    rw [← hXlen]; exact List.take_left
  have hsplit2 : X ++ (c + 1) :: W = (X ++ [c + 1]) ++ W := by
    simp [List.append_assoc]
  have hdrop : (X ++ (c + 1) :: W).drop (P + 1) = W := by
    rw [hsplit2]
    exact List.drop_left' (by rw [List.length_append, hXlen]; rfl)
  rw [htake, hdrop]

/-- `appendAtTM_exit` in closed form. -/
private theorem Compile.appendAtTM_exit_eq :
    ∀ d, AppendGadget.appendAtTM_exit d = 8 + 3 * d
  | 0 => rfl
  | d + 1 => by
      show 3 + AppendGadget.appendAtTM_exit d = _
      rw [Compile.appendAtTM_exit_eq d]; omega

/-- Generic seam symbol bound: every cell `< 4` ⇒ the current symbol is `< 4`. -/
private theorem Compile.sym_bound_of_lt_four (tape : List Nat) (hall : ∀ x ∈ tape, x < 4)
    (hd : Nat) : ∀ v, currentTapeSymbol (([] : List Nat), hd, tape) = some v → v < 4 := by
  intro v hv
  by_cases hlt : hd < tape.length
  · rw [currentTapeSymbol_in_range hlt] at hv
    exact (Option.some_inj.mp hv) ▸ hall _ (List.get_mem tape ⟨hd, hlt⟩)
  · rw [show currentTapeSymbol (([] : List Nat), hd, tape) = none from dif_neg hlt] at hv
    exact absurd hv (by simp)

/-- A register write with `≤ 2`-valued content keeps every register `≤ 2`
(the marked-state analogue of `BitState_set`). -/
private theorem Compile.le_two_set (s : State) (dst : Var) (v : List Nat)
    (h : Compile.BitState s) (hdst : dst < s.length) (hv : ∀ x ∈ v, x ≤ 2) :
    ∀ reg ∈ State.set s dst v, ∀ x ∈ reg, x ≤ 2 := by
  rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst]
  intro reg hreg x hx
  simp only [List.mem_append, List.mem_cons] at hreg
  rcases hreg with hr | hr | hr
  · exact le_trans (h reg (List.mem_of_mem_take hr) x hx) (by omega)
  · subst hr; exact hv x hx
  · exact le_trans (h reg (List.mem_of_mem_drop hr) x hx) (by omega)

/-- `encodeRegs` of a `≤ 2`-valued state has all cells `< 4`. -/
private theorem Compile.encodeRegs_lt_four_le_two (t : State)
    (h : ∀ b ∈ t, ∀ x ∈ b, x ≤ 2) : ∀ y ∈ Compile.encodeRegs t, y < 4 := by
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

/-- All cells of `encodeTape t ++ res` for a `≤ 2`-valued `t` are `< 4`. -/
private theorem Compile.encodeTape_append_res_lt_four_le_two (t : State) (res : List Nat)
    (h : ∀ b ∈ t, ∀ x ∈ b, x ≤ 2) (hres : Compile.ValidResidue res) :
    ∀ x ∈ Compile.encodeTape t ++ res, x < 4 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rw [Compile.encodeTape, List.mem_cons, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · subst hx; decide
    · exact Compile.encodeRegs_lt_four_le_two t h x hx
    · subst hx; decide
  · exact (hres x hx).1

/-- **Interior cells of the cursor tape, off the cursor.** Every cell `0 < i`
that is neither the cursor cell nor in the trailing-terminator-plus-residue
region is `< 4` and `≠ 3` — it agrees with the corresponding cell of the
*unmarked* `encodeTape q ++ res`, whose interior is sentinel-free. -/
private theorem Compile.markedTape_interior_cell (q : State) (src : Var)
    (hsrc : src < q.length) (hbit : Compile.BitState q) (w₁ w₂ : List Nat) (b : Nat)
    (hsplit : State.get q src = w₁ ++ b :: w₂) (c : Nat) (res : List Nat) :
    ∀ i, 0 < i → i ≠ 1 + (Compile.encodeRegs (q.take src)).length + w₁.length →
      i + 1 < (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂))).length →
      ∃ (h : i < (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).length),
        (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).get ⟨i, h⟩ < 4 ∧
        (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).get ⟨i, h⟩ ≠ 3 := by
  intro i hi0 hiP hilen
  have hq : State.set q src (w₁ ++ b :: w₂) = q := by
    rw [← hsplit]; exact Compile.set_get_self q src hsrc
  have hlt : i < (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).length := by
    rw [List.length_append]; omega
  refine ⟨hlt, ?_⟩
  -- the cell agrees with the unmarked tape's cell `i`.
  have hoff := Compile.markedTape_getElem_off q src hsrc w₁ w₂ c b res i hiP
  rw [hq] at hoff
  -- length transfer marked ↔ unmarked.
  have hlen_eq : (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂))).length
      = (Compile.encodeTape q).length := by
    conv_rhs => rw [← hq]
    rw [Compile.encodeTape_set_cell_length q src hsrc w₁ w₂ c,
        Compile.encodeTape_set_cell_length q src hsrc w₁ w₂ b]
  have hilen' : i + 1 < (Compile.encodeTape q).length := by omega
  have hltq : i < (Compile.encodeTape q ++ res).length := by
    rw [List.length_append]; omega
  have hgetq : (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).get ⟨i, hlt⟩
      = (Compile.encodeTape q ++ res).get ⟨i, hltq⟩ := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact Option.some_inj.mp (by
      rw [← List.getElem?_eq_getElem hlt, ← List.getElem?_eq_getElem hltq]; exact hoff)
  rw [hgetq]
  -- the unmarked cell is inside `encodeTape q`'s interior.
  have hilt_e : i < (Compile.encodeTape q).length := by omega
  have hkey : (Compile.encodeTape q ++ res)[i]?
      = some ((Compile.encodeTape q).get ⟨i, hilt_e⟩) := by
    rw [List.getElem?_append_left hilt_e, List.getElem?_eq_getElem hilt_e,
        List.get_eq_getElem]
  have hgetin : (Compile.encodeTape q ++ res).get ⟨i, hltq⟩
      = (Compile.encodeTape q).get ⟨i, hilt_e⟩ := by
    rw [List.get_eq_getElem]
    exact Option.some_inj.mp ((List.getElem?_eq_getElem hltq).symm.trans hkey)
  rw [hgetin]
  obtain ⟨hi', hne3⟩ := Compile.encodeTape_interior_ne_endMark q hbit i hi0 hilen'
  refine ⟨Compile.encodeTape_lt_four q hbit _ (List.get_mem _ _), ?_⟩
  exact hne3

/-- **`appendAtTM` on an encoded tape with residue (cursor-copy stage 3).**
For a `≤ 2`-valued state `p` (the marked loop state) and a shifted symbol
`v + 1` (`v ≤ 2`), the gadget started at head `0` on `encodeTape p ++ res`
appends `v` to register `dst`, exits at its unique halt `appendAtTM_exit dst`
with the head on the LAST cell of the output tape (index
`|encodeTape p| + |res|`), never halting earlier, within `2·L + 3` steps
(`L` the input tape length). The leading sentinel is folded into the first
marker-free block exactly as in `appendBit_sound`; the residue rides in `post`
(its cells are `< 4`, which is all the gadget needs). -/
private theorem Compile.appendAt_encTape_run (v : Nat) (hv : v ≤ 2)
    (p : State) (dst : Var) (hdst : dst < p.length)
    (hp : ∀ reg ∈ p, ∀ x ∈ reg, x ≤ 2)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (AppendGadget.appendAtTM (v + 1) dst)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape p ++ res)] }
        = some { state_idx := AppendGadget.appendAtTM_exit dst,
                 tapes := [([], (Compile.encodeTape p).length + res.length,
                            Compile.encodeTape (State.set p dst (State.get p dst ++ [v]))
                              ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (AppendGadget.appendAtTM (v + 1) dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape p ++ res)] } = some ck →
          ck.state_idx ≠ AppendGadget.appendAtTM_exit dst ∧
          haltingStateReached (AppendGadget.appendAtTM (v + 1) dst) ck = false)
      ∧ t ≤ 2 * (Compile.encodeTape p ++ res).length + 3 := by
  have h_ins : v + 1 < 4 := by omega
  set post₀ : List Nat := Compile.encodeRegs (p.drop (dst + 1)) ++ [Compile.endMark]
    with hpost₀
  set post : List Nat := post₀ ++ res with hpost
  set skipped : List (List Nat) := (p.take dst).map Compile.shiftReg with hskip
  set body : List Nat := Compile.shiftReg (State.get p dst) with hbody
  have hget_mem : State.get p dst ∈ p := by
    rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
  have hshift_lt : ∀ (r : List Nat), (∀ x ∈ r, x ≤ 2) →
      ∀ x ∈ Compile.shiftReg r, x < 4 := by
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
    exact ⟨hshift_ne r, hshift_lt r (fun x hx => hp r (List.mem_of_mem_take hr) x hx)⟩
  have hbody_ne : ∀ x ∈ body, x ≠ 0 := by rw [hbody]; exact hshift_ne _
  have hbody_lt : ∀ x ∈ body, x < 4 := by
    rw [hbody]; exact hshift_lt _ (fun x hx => hp _ hget_mem x hx)
  have hpost_lt : ∀ x ∈ post, x < 4 := by
    rw [hpost, hpost₀]; intro x hx
    rw [List.mem_append, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact Compile.encodeRegs_lt_four_le_two _
        (fun b hbm y hy => hp b (List.mem_of_mem_drop hbm) y hy) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide
    · exact (hres x hx).1
  -- Fold the leading sentinel into the first marker-free block.
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
  -- The sentinel-free split, with the residue attached.
  have hsplit0 : AppendGadget.regBlocks skipped ++ body ++ 0 :: post₀
      = Compile.encodeRegs p ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost₀]; exact Compile.encodeTape_split p dst hdst
  have hsplit : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post
      = Compile.encodeTape p ++ res := by
    rw [Compile.encodeTape, List.nil_append, hsfold, hpost]
    rw [show Compile.endMark :: (AppendGadget.regBlocks skipped ++ body) ++ 0 :: (post₀ ++ res)
          = Compile.endMark :: ((AppendGadget.regBlocks skipped ++ body ++ 0 :: post₀) ++ res)
        from by simp [List.append_assoc], hsplit0]
    simp [List.append_assoc]
  -- The output tape with the inserted symbol.
  have htape0 : AppendGadget.regBlocks skipped ++ body ++ (v + 1) :: 0 :: post₀
      = Compile.encodeRegs (State.set p dst (State.get p dst ++ [v]))
          ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost₀, Compile.regBlocks_map_shiftReg]
    rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop p dst _ hdst,
        Compile.encodeRegs_append, Compile.encodeRegs_cons, Compile.shiftReg_append]
    simp [List.append_assoc]
  have htape : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (v + 1) :: 0 :: post
      = Compile.encodeTape (State.set p dst (State.get p dst ++ [v])) ++ res := by
    rw [Compile.encodeTape, List.nil_append, hsfold, hpost]
    rw [show Compile.endMark :: (AppendGadget.regBlocks skipped ++ body)
            ++ (v + 1) :: 0 :: (post₀ ++ res)
          = Compile.endMark
            :: ((AppendGadget.regBlocks skipped ++ body ++ (v + 1) :: 0 :: post₀) ++ res)
        from by simp [List.append_assoc], htape0]
    simp [List.append_assoc]
  -- The run, trajectory, and step bound.
  have hrun := AppendGadget.appendAt_run_exit (v + 1) h_ins dst [] sk bd post hlen_sk
    h_pre h_skip_sk hbd_ne hbd_lt hpost_lt
  have htraj := AppendGadget.appendAt_no_early_halt (v + 1) h_ins dst [] sk bd post hlen_sk
    h_pre h_skip_sk hbd_ne hbd_lt hpost_lt
  -- The exit head equals the input tape length.
  have hhead : ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
      + ((0 : Nat) :: post).length = (Compile.encodeTape p).length + res.length := by
    have hL := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil] at hL ⊢
    omega
  have hstep_le : AppendGadget.appendAt_steps sk bd post
      ≤ 2 * (Compile.encodeTape p ++ res).length + 3 := by
    have hb' := AppendGadget.appendAt_steps_le sk bd post
    have hL : (AppendGadget.regBlocks sk ++ bd ++ 0 :: post).length
        = (Compile.encodeTape p ++ res).length := by
      rw [show AppendGadget.regBlocks sk ++ bd ++ 0 :: post
            = ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post from by simp,
          hsplit]
    rw [hL] at hb'; exact hb'
  refine ⟨AppendGadget.appendAt_steps sk bd post, ?_, ?_, hstep_le⟩
  · rw [show ({ state_idx := 0, tapes := [([], 0, Compile.encodeTape p ++ res)] }
          : FlatTMConfig)
        = { state_idx := 0,
            tapes := [([], ([] : List Nat).length,
              ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post)] }
      from by rw [hsplit]; rfl]
    rw [hrun, htape, hhead]
  · intro k hk ck hck
    rw [show ({ state_idx := 0, tapes := [([], 0, Compile.encodeTape p ++ res)] }
          : FlatTMConfig)
        = { state_idx := 0,
            tapes := [([], ([] : List Nat).length,
              ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post)] }
      from by rw [hsplit]; rfl] at hck
    have hh := htraj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (AppendGadget.appendAtTM_exit_is_halt (v + 1) dst) hh,
           hh⟩

/-- The symbol under the cursor is below the body's alphabet bound `4`. -/
private theorem Compile.copyBody_sym_bound (dst : Nat) (H : Nat) (tape : List Nat)
    (hall : ∀ x ∈ tape, x < 4) :
    ∀ v, currentTapeSymbol (([] : List Nat), H, tape) = some v →
      v < max (ClearGadget.delimTestTM 4).sig
            (max (Compile.copyContentTM dst).sig Compile.idTM.sig) := by
  intro v hv
  have hmax : max (ClearGadget.delimTestTM 4).sig
      (max (Compile.copyContentTM dst).sig Compile.idTM.sig) = 4 := by
    rw [ClearGadget.delimTestTM_sig]
    show max 4 (max (Compile.copyContentRawTM dst).sig 4) = 4
    rw [Compile.copyContentRawTM_sig]
    rfl
  rw [hmax]
  by_cases hlt : H < tape.length
  · rw [currentTapeSymbol_in_range hlt] at hv
    exact (Option.some_inj.mp hv) ▸ hall _ (List.get_mem tape ⟨H, hlt⟩)
  · rw [show currentTapeSymbol (([] : List Nat), H, tape) = none from dif_neg hlt] at hv
    exact absurd hv (by simp)

/-- All cells of `encodeTape q ++ res` are `< 4` (bit state + valid residue). -/
private theorem Compile.encodeTape_append_res_lt_four (q : State) (res : List Nat)
    (hbit : Compile.BitState q) (hres : Compile.ValidResidue res) :
    ∀ x ∈ Compile.encodeTape q ++ res, x < 4 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact Compile.encodeTape_lt_four q hbit x h
  · exact (hres x h).1

/-- **Pipeline stages 1–2 (`copyRet1TM`) on the marked tape**: step left off the
mark, scan left through the (sentinel-free) prefix to the leading sentinel.
Exact step count `1 + 1 + P` (`P` the mark position), exit `3`, tape unchanged,
head `0`. -/
private theorem Compile.copyRet1_encTape_run (q : State) (src : Var) (hsrc : src < q.length)
    (hbit : Compile.BitState q) (w₁ w₂ : List Nat) (b : Nat)
    (hsplit : State.get q src = w₁ ++ b :: w₂)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    runFlatTM (1 + 1 + (1 + (Compile.encodeRegs (q.take src)).length + w₁.length))
        Compile.copyRet1TM
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                     Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
      = some { state_idx := 3,
               tapes := [([], 0,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    ∧ (∀ k, k < 1 + 1 + (1 + (Compile.encodeRegs (q.take src)).length + w₁.length) → ∀ ck,
        runFlatTM k Compile.copyRet1TM
            { state_idx := 0,
              tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                         Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
          = some ck →
        ck.state_idx ≠ 3 ∧ haltingStateReached Compile.copyRet1TM ck = false) := by
  obtain ⟨hPlt, hPget⟩ := Compile.markedTape_get_mark q src hsrc w₁ w₂ 2 res
  -- stage 1: one step left off the mark.
  have h1_run := ScanLeft.stepLeftTM_run 4 []
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length) hPlt
    (by rw [hPget]; decide)
  have h1_traj := ScanLeft.stepLeftTM_no_early_halt 4 []
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
  -- stage 2: scan left to the leading sentinel at index `0`.
  have h0 : 0 < (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res).length := by
    omega
  have htarget0 : (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res).get
      ⟨0, h0⟩ = 3 := by
    have hkey : (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)[0]?
        = some 3 := by
      rw [Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ 2 res]
      rfl
    rw [List.get_eq_getElem]
    exact Option.some_inj.mp ((List.getElem?_eq_getElem h0).symm.trans hkey)
  have hLM := Compile.encodeTape_set_cell_length q src hsrc w₁ w₂ 2
  have hcells : ∀ i, 0 < i →
      i ≤ 1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1 →
      ∃ (h : i < (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res).length),
        (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res).get ⟨i, h⟩ < 4 ∧
        (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res).get ⟨i, h⟩ ≠ 3 :=
    fun i hi0 hile =>
      Compile.markedTape_interior_cell q src hsrc hbit w₁ w₂ b hsplit 2 res i hi0
        (by omega) (by omega)
  have h2_run := ScanLeft.scanLeft_run 4 3 []
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res) h0 htarget0
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1) (by omega) hcells
  have h2_traj := ScanLeft.scanLeft_no_early_halt 4 3 []
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1) (by omega) hcells
  -- compose.
  have hsym : ∀ v, currentTapeSymbol
      ([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1,
        Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res) = some v →
      v < max (ScanLeft.stepLeftTM 4).sig (ScanLeft.scanLeftUntilTM 4 3).sig := by
    intro v hv
    have hlt4 : ∀ x ∈ Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res,
        x < 4 := by
      refine Compile.encodeTape_append_res_lt_four_le_two _ res ?_ hres
      refine Compile.le_two_set q src _ hbit hsrc ?_
      intro x hx
      have hw : ∀ y ∈ w₁ ++ b :: w₂, y ≤ 1 := by
        rw [← hsplit]
        intro y hy
        have hmem : State.get q src ∈ q := by
          rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
        exact hbit _ hmem y hy
      rcases List.mem_append.mp hx with h | h
      · exact le_trans (hw x (List.mem_append_left _ h)) (by omega)
      · rcases List.mem_cons.mp h with h0 | h0
        · omega
        · exact le_trans (hw x (List.mem_append_right _ (List.mem_cons_of_mem _ h0)))
            (by omega)
    exact Compile.sym_bound_of_lt_four _ hlt4 _ v hv
  have hcomp := composeFlatTM_run (ScanLeft.stepLeftTM_valid 4)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide)) (by decide)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (ScanLeft.stepLeftTM 4).states; decide) []
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1)
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    hsym h1_run h1_traj h2_run rfl
  have hcomp_traj := composeFlatTM_no_early_halt (ScanLeft.stepLeftTM_valid 4)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide)) (by decide)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (ScanLeft.stepLeftTM 4).states; decide) []
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1)
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    hsym h1_run h1_traj
    (fun k hk ck hck => (h2_traj k hk ck hck).2)
  have hsteps : 1 + 1 + (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
      = 1 + 1 + (1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1 + 1) := by
    omega
  refine ⟨?_, ?_⟩
  · rw [hsteps]; exact hcomp.1
  · intro k hk ck hck
    have hh := hcomp_traj k (by omega) ck hck
    exact ⟨ClearGadget.ne_of_not_halting
      (show Compile.copyRet1TM.halt[3]? = some true from rfl) hh, hh⟩

/-- **One cursor-copy pipeline pass (`copyPipeTM b dst`).** Started with the head
ON the freshly written mark (src's cell `i = |w₁|`, the only interior `3`), the
pipeline rewinds to the sentinel, appends `b` to `dst` (`appendAtTM (b+1)`),
returns to the mark via scan-left-from-the-end (trailing terminator, step left,
mark), restores `b+1` over the mark and steps right onto the next cursor cell.
`q` is the un-marked loop-invariant state; `dst ≠ src`; the marked tape is
`encodeTape (q.set src (w₁ ++ 2 :: w₂))` (cell value `2` encodes to the mark `3`).
The residue passes through untouched. Budget: `≤ 5·L + 16` over the *final*
tape (`L = |encodeTape (q.set dst …) ++ res|`, one cell longer than the input). -/
theorem Compile.copyPipe_run (b : Nat) (hb : b ≤ 1) (q : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < q.length) (hsrc : src < q.length)
    (hbit : Compile.BitState q) (w₁ w₂ : List Nat)
    (hsplit : State.get q src = w₁ ++ b :: w₂)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ T,
      runFlatTM T (Compile.copyPipeTM b dst)
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                       Compile.encodeTape (q.set src (w₁ ++ 2 :: w₂)) ++ res)] }
        = some { state_idx := Compile.copyPipeTM_exit dst,
                 tapes := [([],
                   1 + (Compile.encodeRegs ((q.set dst (State.get q dst ++ [b])).take src)).length
                     + w₁.length + 1,
                   Compile.encodeTape (q.set dst (State.get q dst ++ [b])) ++ res)] }
      ∧ (∀ k, k < T → ∀ ck,
          runFlatTM k (Compile.copyPipeTM b dst)
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                           Compile.encodeTape (q.set src (w₁ ++ 2 :: w₂)) ++ res)] } = some ck →
          ck.state_idx ≠ Compile.copyPipeTM_exit dst ∧
          haltingStateReached (Compile.copyPipeTM b dst) ck = false)
      ∧ T ≤ 5 * (Compile.encodeTape (q.set dst (State.get q dst ++ [b])) ++ res).length + 16 := by
  sorry

/-- **Cursor-loop body, ITERATE contract** (`loopTM_run`'s iteration shape).
From the un-marked cursor config (head ON src's cell `i = |w₁|`, a bit `b`),
`copyBodyTM dst` tests it (`delimTestTM`, content branch), marks it
(`markBitTM`), branch-bridges into `copyPipeTM b dst`, and (for `b = 1`, via
the extra `joinTwoHalts` bridge) lands at the merged iterate exit
`copyBody_exitLoop dst` on the next cursor config. -/
theorem Compile.copyBody_run_iter (q : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < q.length) (hsrc : src < q.length)
    (hbit : Compile.BitState q) (b : Nat) (hb : b ≤ 1) (w₁ w₂ : List Nat)
    (hsplit : State.get q src = w₁ ++ b :: w₂)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ T,
      runFlatTM T (Compile.copyBodyTM dst)
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                       Compile.encodeTape q ++ res)] }
        = some { state_idx := Compile.copyBody_exitLoop dst,
                 tapes := [([],
                   1 + (Compile.encodeRegs ((q.set dst (State.get q dst ++ [b])).take src)).length
                     + w₁.length + 1,
                   Compile.encodeTape (q.set dst (State.get q dst ++ [b])) ++ res)] }
      ∧ (∀ k, k < T → ∀ ck,
          runFlatTM k (Compile.copyBodyTM dst)
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                           Compile.encodeTape q ++ res)] } = some ck →
          ck.state_idx ≠ Compile.copyBody_exitDone dst ∧
          ck.state_idx ≠ Compile.copyBody_exitLoop dst ∧
          haltingStateReached (Compile.copyBodyTM dst) ck = false)
      ∧ T ≤ 5 * (Compile.encodeTape (q.set dst (State.get q dst ++ [b])) ++ res).length + 21 := by
  sorry

/-- **The cursor cell.** Cell `1 + |encodeRegs (q.take src)| + i` of
`encodeTape q ++ res` is register `src`'s cell `i`: the shifted bit
`(q.get src)[i] + 1` for `i < |q.get src|`, and the register's `0` delimiter
for `i = |q.get src|`. -/
private theorem Compile.cursor_cell (q : State) (src : Var) (hsrc : src < q.length)
    (res : List Nat) (i : Nat) (hi : i ≤ (State.get q src).length) :
    ∃ (hlt : 1 + (Compile.encodeRegs (q.take src)).length + i
        < (Compile.encodeTape q ++ res).length),
      (Compile.encodeTape q ++ res).get
          ⟨1 + (Compile.encodeRegs (q.take src)).length + i, hlt⟩
        = if h : i < (State.get q src).length then (State.get q src)[i] + 1 else 0 := by
  have hdec := (Compile.encodeTape_reg_decomp_at q src hsrc).2
  set A := Compile.encodeRegs (q.take src) with hA
  set u := State.get q src with hu
  set R := Compile.encodeRegs (q.drop (src + 1)) ++ [Compile.endMark] with hR
  have htape : Compile.encodeTape q ++ res
      = ((3 : Nat) :: A) ++ (Compile.shiftReg u ++ 0 :: (R ++ res)) := by
    rw [hdec]
    show (Compile.endMark :: A) ++ (Compile.shiftReg u ++ (0 :: R)) ++ res = _
    simp [Compile.endMark, List.append_assoc]
  have hslen : (Compile.shiftReg u).length = u.length := by
    rw [Compile.shiftReg, List.length_map]
  have hmidlen : i < (Compile.shiftReg u ++ 0 :: (R ++ res)).length := by
    simp only [List.length_append, List.length_cons, hslen]; omega
  have hprelen : ((3 : Nat) :: A).length = 1 + A.length := by
    simp [Nat.add_comm]
  have hlt : 1 + A.length + i < (Compile.encodeTape q ++ res).length := by
    rw [htape, List.length_append, hprelen]
    omega
  refine ⟨hlt, ?_⟩
  have hcell? : (Compile.encodeTape q ++ res)[1 + A.length + i]?
      = (Compile.shiftReg u ++ 0 :: (R ++ res))[i]? := by
    rw [htape, List.getElem?_append_right (by rw [hprelen]; omega), hprelen,
        show 1 + A.length + i - (1 + A.length) = i from by omega]
  have hmid : (Compile.shiftReg u ++ 0 :: (R ++ res))[i]?
      = some (if h : i < u.length then u[i] + 1 else 0) := by
    by_cases h : i < u.length
    · rw [List.getElem?_append_left (by rw [hslen]; exact h), dif_pos h]
      rw [Compile.shiftReg, List.getElem?_map, List.getElem?_eq_getElem h]
      rfl
    · have hieq : i = u.length := by omega
      rw [List.getElem?_append_right (by rw [hslen]; omega), dif_neg h, hslen, hieq,
          Nat.sub_self]
      rfl
  rw [List.get_eq_getElem]
  have h2 := hcell?.trans hmid
  rw [List.getElem?_eq_getElem hlt] at h2
  exact Option.some_inj.mp h2

/-- **Cursor-loop body, DONE contract.** With the cursor ON src's `0` delimiter
(`i = |src|` — src exhausted), `delimTestTM` reads `0` (1 step) and the branch
bridge lands on `idTM`'s start = the done exit (1 step); tape and head
unchanged. -/
theorem Compile.copyBody_run_done (q : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < q.length) (hsrc : src < q.length)
    (hbit : Compile.BitState q)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    runFlatTM 2 (Compile.copyBodyTM dst)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length
                          + (State.get q src).length,
                     Compile.encodeTape q ++ res)] }
      = some { state_idx := Compile.copyBody_exitDone dst,
               tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length
                              + (State.get q src).length,
                          Compile.encodeTape q ++ res)] }
    ∧ (∀ k, k < 2 → ∀ ck,
        runFlatTM k (Compile.copyBodyTM dst)
            { state_idx := 0,
              tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length
                              + (State.get q src).length,
                         Compile.encodeTape q ++ res)] } = some ck →
        ck.state_idx ≠ Compile.copyBody_exitDone dst ∧
        ck.state_idx ≠ Compile.copyBody_exitLoop dst ∧
        haltingStateReached (Compile.copyBodyTM dst) ck = false) := by
  set H := 1 + (Compile.encodeRegs (q.take src)).length + (State.get q src).length with hHdef
  set tape := Compile.encodeTape q ++ res with htapedef
  obtain ⟨hlt, hcell⟩ := Compile.cursor_cell q src hsrc res (State.get q src).length le_rfl
  rw [dif_neg (lt_irrefl _)] at hcell
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, tape)] } with hcfg0
  -- M₁ (delimTestTM) runs 1 step to the delimiter exit.
  have hrun1 : runFlatTM 1 (ClearGadget.delimTestTM 4) cfg0
      = some { state_idx := ClearGadget.delimTestTM_exit_delim, tapes := [([], H, tape)] } :=
    ClearGadget.delimTestTM_run_delim 4 (by decide) [] tape H hlt hcell
  have htraj1 : ∀ k, k < 1 → ∀ ck, runFlatTM k (ClearGadget.delimTestTM 4) cfg0 = some ck →
      ck.state_idx ≠ ClearGadget.delimTestTM_exit_content ∧
      ck.state_idx ≠ ClearGadget.delimTestTM_exit_delim ∧
      haltingStateReached (ClearGadget.delimTestTM 4) ck = false :=
    fun k hk ck hck => ClearGadget.delimTestTM_no_early_halt 4 [] tape H k hk ck hck
  -- M₃ (idTM) halts immediately.
  have hrun3 : runFlatTM 0 Compile.idTM
      { state_idx := Compile.idTM.start, tapes := [([], H, tape)] }
      = some { state_idx := 0, tapes := [([], H, tape)] } := rfl
  have hhalt3 : haltingStateReached Compile.idTM
      { state_idx := 0, tapes := [([], H, tape)] } = true := rfl
  have hsym := Compile.copyBody_sym_bound dst H tape
    (Compile.encodeTape_append_res_lt_four q res hbit hres)
  have hexitne : ClearGadget.delimTestTM_exit_content ≠ ClearGadget.delimTestTM_exit_delim := by
    decide
  have hcfg_lt : cfg0.state_idx < (ClearGadget.delimTestTM 4).states := by
    rw [ClearGadget.delimTestTM_states]; show 0 < 3; omega
  have hneg := branchComposeFlatTM_run_neg hexitne
    (ClearGadget.delimTestTM_valid 4 (by decide)) (Compile.copyContentTM_valid dst)
    Compile.idTM_valid
    (by rw [ClearGadget.delimTestTM_states]; decide)
    (by rw [ClearGadget.delimTestTM_states]; decide)
    cfg0 hcfg_lt [] H tape hsym hrun1 htraj1 hrun3 hhalt3
  have htrajneg := branchComposeFlatTM_no_early_halt_neg hexitne
    (ClearGadget.delimTestTM_valid 4 (by decide)) (Compile.copyContentTM_valid dst)
    Compile.idTM_valid
    (by rw [ClearGadget.delimTestTM_states]; decide)
    (by rw [ClearGadget.delimTestTM_states]; decide)
    cfg0 hcfg_lt [] H tape hsym (t₂ := 0) hrun1 htraj1
    (fun k hk ck hck => absurd hk (by omega))
  have hstate_eq : (0 : Nat) + ((ClearGadget.delimTestTM 4).states
      + (Compile.copyContentTM dst).states) = Compile.copyBody_exitDone dst := by
    rw [ClearGadget.delimTestTM_states, Compile.copyContentTM_states]
    show 0 + (3 + (51 + 6 * dst)) = 54 + 6 * dst; ring
  refine ⟨?_, ?_⟩
  · have h := hneg.1
    rw [hstate_eq] at h
    exact h
  · intro k hk ck hck
    have hh := htrajneg k (by omega) ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.copyBodyTM_exitDone_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (Compile.copyBodyTM_exitLoop_is_halt dst) hh, hh⟩

/-- **The cursor-copy loop (`copyLoopTM dst`), assembled by `loopTM_run`.**
Entered with `dst` already cleared and the head on src's first cell, the loop
copies src bit-by-bit and halts at its dedicated halt state with the head on
src's delimiter. Tape sequence `T j = ([], cursor (n−j), encodeTape (s.set dst
(u.take (n−j))) ++ res)` (`u = s.get src`, `n = |u|`). -/
theorem Compile.copyLoop_run (s : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < s.length) (hsrc : src < s.length)
    (hbit : Compile.BitState s) (hdst_empty : State.get s dst = [])
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ T,
      runFlatTM T (Compile.copyLoopTM dst)
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.copyLoopTM_exit dst,
                 tapes := [([],
                   1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
                     + (State.get s src).length,
                   Compile.encodeTape (s.set dst (State.get s src)) ++ res)] }
      ∧ (∀ k, k < T → ∀ ck,
          runFlatTM k (Compile.copyLoopTM dst)
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                           Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.copyLoopTM_exit dst ∧
          haltingStateReached (Compile.copyLoopTM dst) ck = false)
      ∧ T ≤ ((State.get s src).length + 1)
              * (5 * (Compile.encodeTape (s.set dst (State.get s src)) ++ res).length + 23) := by
  sorry

/-- **The `copy` op's exact-residue run lemma** (`dst ≠ src`): the full machine
`clear ⨾ navigate ⨾ cursor loop ⨾ rewind`, with the boundary halt demoted. The
residue formula is EXACT — `res_in ++ replicate |s.get dst| 0`, all of it from
the clear phase (the cursor loop adds none) — which is what the `compileForBnd`
combinator's tight W-invariant needs (HANDOFF bottom-up task 2). -/
theorem Compile.opCopy_run (s : State) (dst src : Var) (hne : dst ≠ src)
    (hdst : dst < s.length) (hsrc : src < s.length)
    (hbit : Compile.BitState s)
    (res_in : List Nat) (hres_in : Compile.ValidResidue res_in) :
    ∃ t,
      runFlatTM t (Compile.opCopy dst src).M
          (initFlatConfig (Compile.opCopy dst src).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opCopy dst src).exit,
                 tapes := [([], 0, Compile.encodeTape (s.set dst (State.get s src))
                            ++ (res_in ++ List.replicate (State.get s dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opCopy dst src).M
            (initFlatConfig (Compile.opCopy dst src).M [Compile.encodeTape s ++ res_in])
          = some ck →
        ck.state_idx ≠ (Compile.opCopy dst src).exit ∧
        haltingStateReached (Compile.opCopy dst src).M ck = false)
    ∧ t ≤ (9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
            + 9 * (Compile.encodeTape s ++ res_in).length + 30)
          * ((State.get s src).length + 2) := by
  sorry

/-- **Residue-tolerant per-op physical contract (Risk C2, step 1c).** The fix
for the unsatisfiable exact-tape contract: the exit tape is
`encodeTape (Op.eval o s) ++ res_out` where `res_out` is `ValidResidue`,
hiding the residue existentially. For growth ops (`appendOne`/`appendZero`)
`res_out = res_in` (the residue passes through unchanged); for deletion ops
`res_out = res_in ++ [0, …]` (filler cells appended by `deleteCarryTM`).
The residue stays terminator-free across composition (each gadget preserves
`ValidResidue`), and `decodeTape` ignores it (`decodeTape_encodeTape_append`).

Input: the start tape may carry residue (`res_in`), since the previous
fragment's exit tape may have residue. The contract is:
  exit tape = `encodeTape (Op.eval o s) ++ res_out` (where `res_out` is
  `ValidResidue`), head rewound to `0`, in ≤ `9·inputTapeLen² + 9` steps.

This is the replacement for `compileOp_sound_physical` (which demanded
exact tape `encodeTape output` and was **unsatisfiable** for deletion ops).
The `compileSeq_sound_physical_residue` combinator composes these directly.

**⚠ 2026-06-01 — budget is QUADRATIC, not linear.** The per-op budget was
`3·tapeLen + 8` (linear), which the append ops meet (one insert = one O(tapeLen)
pass). But every **multi-cell** op is inherently **Θ(tapeLen²)** on a single-tape
machine: `clear`/`tail`/`copy`/… must delete or move `Θ(tapeLen)` cells, and each
deletion/insertion shifts the suffix in a separate O(tapeLen) pass (a single head
cannot shift a block by a data-dependent distance in one pass — it would have to
carry that distance in finite state). So the linear bound is **unsatisfiable** for
them; the budget is loosened to the quadratic `9·tapeLen² + 9` (constant generous,
tunable when the gadgets land). This composes fine: `compileSeq_sound_physical`
uses the *additive* budget `t₁+1+t₂` (no linearity assumed), so summing per-op
quadratics over `≤ cost` fragments (each tape `≤` the global max) gives a
polynomial total — `toFrameworkWitness'` only needs `inOPoly`.

**⚠ 2026-06-11c — budget is COST-SCALED: `(9·L²+9·L+30)·(cost+1)`.** The
multi-cell ops are *compositions* of quadratic phases: `copy dst src` is
`clear dst` (whose own proven black-box bound is `9·L²+9`) plus a `|src|`-round
cursor loop (each round `O(L)`), so the unscaled `9·L²+9·L+30` is unprovable for
it (the clear phase alone exhausts it). Scaling by `Op.cost o s + 1` funds the
loop rounds (`cost = |src|+1` for `copy`/`tail`) and is free for the consumer:
`run_physical_residue_gen`'s ② discharge pays `physStepBudget`'s
`(9G²+9G+33)·(8·cost+8)`, and `(9G²+9G+30)·(cost+1)` sits under it termwise
(`#eval`-validated against the real machines in `probes/CursorCopyProbe.lean`). -/
theorem compileOp_sound_physical_residue (o : Op) (s : State) (res_in : List Nat)
    (hbit : Compile.BitState s) (hbnd : o.inBounds s)
    (hres_in : Compile.ValidResidue res_in) :
    ∃ (t : Nat) (res_out : List Nat),
      Compile.ValidResidue res_out ∧
      -- ① the **W-invariant** (joint size+residue grows by ≤ cost). Non-compounding;
      -- this is what keeps the residue polynomially bounded across the whole
      -- `Compile_run_physical_residue` induction (see `run_physical_residue_gen`).
      State.size (Op.eval o s) + res_out.length
          ≤ State.size s + res_in.length + Op.cost o s ∧
      runFlatTM t (compileOp o).M
          (initFlatConfig (compileOp o).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (compileOp o).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval o s) ++ res_out)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (compileOp o).M
              (initFlatConfig (compileOp o).M [Compile.encodeTape s ++ res_in]) = some ck →
          ck.state_idx ≠ (compileOp o).exit ∧
          haltingStateReached (compileOp o).M ck = false)
      ∧ t ≤ (9 * (Compile.encodeTape s ++ res_in).length
               * (Compile.encodeTape s ++ res_in).length
               + 9 * (Compile.encodeTape s ++ res_in).length + 30)
            * (Op.cost o s + 1) := by
  cases o with
  | appendOne dst =>
      -- `res_out = res_in`: the append grows `encodeTape s` by one cell; residue passes through.
      -- The append op meets the *linear* `3·L+8`; relax to the contract's quadratic.
      obtain ⟨t, hrun, htraj, hbudget⟩ :=
        Compile.opAppendBit_physical_residue 1 (by omega) s dst hbit hbnd res_in hres_in
      exact ⟨t, res_in, hres_in,
        (by have := Op.size_eval_le (Op.appendOne dst) s; omega), hrun, htraj,
        le_trans (le_trans hbudget (Compile.linear_le_quadratic_tapeLen s res_in))
          (by show _ ≤ _ * (1 + 1); omega)⟩
  | appendZero dst =>
      obtain ⟨t, hrun, htraj, hbudget⟩ :=
        Compile.opAppendBit_physical_residue 0 (by omega) s dst hbit hbnd res_in hres_in
      exact ⟨t, res_in, hres_in,
        (by have := Op.size_eval_le (Op.appendZero dst) s; omega), hrun, htraj,
        le_trans (le_trans hbudget (Compile.linear_le_quadratic_tapeLen s res_in))
          (by show _ ≤ _ * (1 + 1); omega)⟩
  -- The 9 cross-register stub ops still need their gadgets (`copyBlockTM`, see ROADMAP C2.c).
  | clear dst =>
      -- `clearRegionTM_run` (step 5b) provides the run + no-early-halt trajectory; the loop
      -- frees `|s.get dst|` cells, each becoming a `0` residue cell.
      -- res_out = res_in ++ replicate |s.get dst| 0.
      obtain ⟨t, hrun, htraj, hbud⟩ := Compile.clearRegionTM_run s dst res_in hbnd hbit hres_in
      have hstart0 : (compileOp (Op.clear dst)).M.start = 0 := ClearGadget.clearRegionTM_start dst
      have hinit : initFlatConfig (compileOp (Op.clear dst)).M [Compile.encodeTape s ++ res_in]
          = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
        simp only [initFlatConfig, hstart0, List.map_cons, List.map_nil]
      refine ⟨t, res_in ++ List.replicate (s.get dst).length 0,
        Compile.ValidResidue_append_replicate_zero res_in _ hres_in, ?_, ?_, ?_,
        le_trans hbud (by show _ ≤ _ * (1 + 1); omega)⟩
      · -- ① the freed `|dst|` cells move into the residue: `W` is unchanged (cost ≥ 0).
        have h := State.size_set_add s dst ([] : List Nat)
        simp only [List.length_nil, Nat.add_zero] at h
        simp only [Op.eval, Op.cost, List.length_append, List.length_replicate]
        omega
      · rw [hinit]; exact hrun
      · intro k hk ck hck
        rw [hinit] at hck
        exact htraj k hk ck hck
  | copy dst src =>
      by_cases hds : dst = src
      · -- compile-time no-op: `Op.eval` is the identity, the machine is the
        -- 1-state immediate halt (`compiledCmd_default`), `t = 0`.
        subst hds
        have hM : compileOp (Op.copy dst dst) = compiledCmd_default := by
          show Compile.opCopy dst dst = compiledCmd_default
          rw [Compile.opCopy, if_pos rfl]
        have heval : Op.eval (Op.copy dst dst) s = s := by
          show s.set dst (State.get s dst) = s
          exact Compile.set_get_self s dst hbnd.1
        refine ⟨0, res_in, hres_in, ?_, ?_, ?_, ?_⟩
        · rw [heval]; simp only [Op.cost]; omega
        · rw [hM, heval]
          show some _ = some _
          rfl
        · intro k hk ck hck; omega
        · omega
      · obtain ⟨t, hrun, htraj, hbud⟩ :=
          Compile.opCopy_run s dst src hds hbnd.1 hbnd.2 hbit res_in hres_in
        refine ⟨t, res_in ++ List.replicate (State.get s dst).length 0,
          Compile.ValidResidue_append_replicate_zero res_in _ hres_in, ?_, hrun, htraj, ?_⟩
        · -- ① the freed `|dst₀|` cells move to the residue; `dst` gains `|src|`.
          have h := State.size_set_add s dst (State.get s src)
          simp only [Op.eval, Op.cost, List.length_append, List.length_replicate]
          omega
        · -- budget: `(9L²+9L+30)·(|src|+2) = (9L²+9L+30)·(cost+1)`.
          exact hbud
  | tail dst src => sorry
  | head dst src =>
      obtain ⟨t, hrun, htraj, hbud⟩ :=
        Compile.opHead_run s dst src res_in hbit hbnd.1 hbnd.2 hres_in
      refine ⟨t, res_in ++ List.replicate (s.get dst).length 0,
        Compile.ValidResidue_append_replicate_zero res_in _ hres_in, ?_, hrun, htraj,
        le_trans hbud (by show _ ≤ _ * (1 + 1); omega)⟩
      · -- ① `head` writes `≤ 1` cell to `dst`; freed cells go to residue.
        rcases hsrc : s.get src with _ | ⟨x, xs⟩
        · have h := State.size_set_add s dst ([] : List Nat)
          simp only [Op.eval, Op.cost, hsrc, List.length_append, List.length_replicate,
            List.length_nil, Nat.add_zero] at h ⊢
          omega
        · have h := State.size_set_add s dst [x]
          simp only [Op.eval, Op.cost, hsrc, List.length_append, List.length_replicate,
            List.length_cons, List.length_nil] at h ⊢
          omega
  | eqBit dst src1 src2 => sorry
  | nonEmpty dst src =>
      obtain ⟨t, hrun, htraj, hbud⟩ :=
        Compile.opNonEmpty_run s dst src res_in hbit hbnd.1 hbnd.2 hres_in
      refine ⟨t, res_in ++ List.replicate (s.get dst).length 0,
        Compile.ValidResidue_append_replicate_zero res_in _ hres_in, ?_, hrun, htraj,
        le_trans hbud (by show _ ≤ _ * (1 + 1); omega)⟩
      · -- ① `nonEmpty` writes exactly `1` cell to `dst`; freed cells go to residue.
        have h := State.size_set_add s dst (if (s.get src).isEmpty then ([0] : List Nat) else [1])
        have hv : (if (s.get src).isEmpty then ([0] : List Nat) else [1]).length = 1 := by
          by_cases hb : (s.get src).isEmpty <;> simp [hb]
        rw [hv] at h
        simp only [Op.eval, Op.cost, List.length_append, List.length_replicate]
        omega
  | takeAt dst src lenReg => sorry
  | dropAt dst src lenReg => sorry
  | concat dst src1 src2 => sorry
  | consLen dst lenSrc src => sorry

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

/-! ### C2 design validation: the RESIDUE-TOLERANT contract composes

The exact-tape contract is unsatisfiable for length-decreasing ops (the tape
never shrinks — `Complexity/Complexity/TapeMono.lean`,
`Compile.clear_physical_unsatisfiable`). The recommended fix is a *residue-
tolerant* contract: a gadget run on `encodeTape s ++ residue` halts (head `0`)
with tape `encodeTape output ++ residue'`, where every residue is a
`Compile.ValidResidue` (only interior symbols `{0,1,2}` — `< 4` and `≠ endMark`,
the `0`-filler left-shifting writes and the interior cells append carries out).

Before anyone builds the delete gadget / two-phase rewind on this design, the
two lemmas below **validate that it composes** — i.e. that residue threads
mechanically through the one combinator the whole `Cmd` induction rests on
(`compileSeq`). They are the residue-tolerant generalisations of
`compileSeq_sound_physical` / `compileSeq_traj_physical`, and they go through by
the *same* proof: `compileSeq_compose_physical` is already polymorphic in the
inter-fragment tape, so the only new obligation is that the intermediate tape's
symbols stay `< 4` — discharged by `ValidResidue` on the residue and
`encodeTape_lt_four` on the content. This de-risks the redesign: composition
does **not** blow up. (The residue stays `ValidResidue` and polynomially bounded
— `|residue| ≤ physical tape length ≤ size + cost` — but those are per-gadget
obligations, not composition obligations.) -/

/-- **Residue-tolerant `compileSeq` composition (PROVEN — design validation).**
The residue-tolerant generalisation of `compileSeq_sound_physical`: given two
fragments satisfying the residue-tolerant contract (head-`0` exit, tape
`encodeTape output ++ residue`), `compileSeq r1 r2` satisfies it with additive
budget `t₁ + 1 + t₂`. The input residue `res0` is unconstrained; only the
*inter-fragment* residue `res1` must be `ValidResidue` (so the seam tape's
symbols stay `< 4`). -/
theorem compileSeq_sound_physical_residue
    (r1 r2 : CompiledCmd) (s mid final : State)
    (res0 res1 res2 : List Nat)
    (hbit_mid : Compile.BitState mid)
    (hres1 : Compile.ValidResidue res1)
    {t1 t2 : Nat}
    (h_run1 : runFlatTM t1 r1.M (initFlatConfig r1.M [Compile.encodeTape s ++ res0])
                = some { state_idx := r1.exit,
                         tapes := [([], 0, Compile.encodeTape mid ++ res1)] })
    (h_traj1 : ∀ k, k < t1 → ∀ ck,
        runFlatTM k r1.M (initFlatConfig r1.M [Compile.encodeTape s ++ res0]) = some ck →
        ck.state_idx ≠ r1.exit ∧ haltingStateReached r1.M ck = false)
    (h_run2 : runFlatTM t2 r2.M (initFlatConfig r2.M [Compile.encodeTape mid ++ res1])
                = some { state_idx := r2.exit,
                         tapes := [([], 0, Compile.encodeTape final ++ res2)] })
    (h_halt2 : haltingStateReached r2.M
        { state_idx := r2.exit,
          tapes := [([], 0, Compile.encodeTape final ++ res2)] } = true) :
    runFlatTM (t1 + 1 + t2) (compileSeq r1 r2).M
        (initFlatConfig (compileSeq r1 r2).M [Compile.encodeTape s ++ res0])
      = some { state_idx := (compileSeq r1 r2).exit,
               tapes := [([], 0, Compile.encodeTape final ++ res2)] } ∧
    haltingStateReached (compileSeq r1 r2).M
      { state_idx := (compileSeq r1 r2).exit,
        tapes := [([], 0, Compile.encodeTape final ++ res2)] } = true := by
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape mid ++ res1)
      = some v → v < 4 := by
    intro v hv
    simp only [currentTapeSymbol] at hv
    split at hv
    case isTrue h =>
      rw [Option.some.injEq] at hv; subst hv
      have hmem := List.getElem_mem h
      rw [List.mem_append] at hmem
      rcases hmem with hm | hr
      · exact Compile.encodeTape_lt_four mid hbit_mid _ hm
      · exact (hres1 _ hr).1
    case isFalse => exact absurd hv (by simp)
  have key := compileSeq_compose_physical r1 r2
    (Compile.encodeTape s ++ res0) (Compile.encodeTape mid ++ res1)
    h_sym h_run1 h_traj1 h_run2 h_halt2
  rw [show (compileSeq r1 r2).exit = r2.exit + r1.M.states from Nat.add_comm ..]
  exact key

/-- **Residue-tolerant `compileSeq` trajectory (PROVEN — design validation).**
The residue-tolerant generalisation of `compileSeq_traj_physical`: if both
fragments never halt before their exit on the residue-carrying tapes, neither
does the composition. -/
theorem compileSeq_traj_physical_residue
    (r1 r2 : CompiledCmd) (s mid : State)
    (res0 res1 : List Nat)
    (hbit_mid : Compile.BitState mid)
    (hres1 : Compile.ValidResidue res1)
    {t1 t2 : Nat}
    (h_run1 : runFlatTM t1 r1.M (initFlatConfig r1.M [Compile.encodeTape s ++ res0])
                = some { state_idx := r1.exit,
                         tapes := [([], 0, Compile.encodeTape mid ++ res1)] })
    (h_traj1 : ∀ k, k < t1 → ∀ ck,
        runFlatTM k r1.M (initFlatConfig r1.M [Compile.encodeTape s ++ res0]) = some ck →
        ck.state_idx ≠ r1.exit ∧ haltingStateReached r1.M ck = false)
    (h_traj2 : ∀ k, k < t2 → ∀ ck,
        runFlatTM k r2.M (initFlatConfig r2.M [Compile.encodeTape mid ++ res1]) = some ck →
        ck.state_idx ≠ r2.exit ∧ haltingStateReached r2.M ck = false) :
    ∀ k, k < t1 + 1 + t2 → ∀ ck,
      runFlatTM k (compileSeq r1 r2).M
          (initFlatConfig (compileSeq r1 r2).M [Compile.encodeTape s ++ res0]) = some ck →
      ck.state_idx ≠ (compileSeq r1 r2).exit ∧
      haltingStateReached (compileSeq r1 r2).M ck = false := by
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape mid ++ res1)
      = some v → v < max r1.M.sig r2.M.sig := by
    intro v hv
    rw [r1.M_sig, r2.M_sig]
    simp only [currentTapeSymbol] at hv
    split at hv
    case isTrue h =>
      rw [Option.some.injEq] at hv; subst hv
      have hmem := List.getElem_mem h
      rw [List.mem_append] at hmem
      rcases hmem with hm | hr
      · exact Compile.encodeTape_lt_four mid hbit_mid _ hm
      · exact (hres1 _ hr).1
    case isFalse => exact absurd hv (by simp)
  have h_traj2' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k r2.M
          { state_idx := r2.M.start, tapes := [([], 0, Compile.encodeTape mid ++ res1)] }
        = some ck → haltingStateReached r2.M ck = false := by
    intro k hk ck hck
    exact (h_traj2 k hk ck hck).2
  have h_nohalt := composeFlatTM_no_early_halt r1.M_valid r2.M_valid r1.exit_lt
    (initFlatConfig r1.M [Compile.encodeTape s ++ res0]) r1.M_valid.1
    [] 0 (Compile.encodeTape mid ++ res1) h_sym h_run1 h_traj1 h_traj2'
  intro k hk ck hck
  refine ⟨?_, h_nohalt k hk ck hck⟩
  intro heq
  have hnh : haltingStateReached (compileSeq r1 r2).M ck = false := h_nohalt k hk ck hck
  have hh : haltingStateReached (compileSeq r1 r2).M ck = true := by
    show (compileSeq r1 r2).M.halt.getD ck.state_idx false = true
    rw [heq]
    have := (compileSeq r1 r2).exit_is_halt
    simp only [List.getD, this, Option.getD]
  rw [hh] at hnh
  exact absurd hnh Bool.noConfusion

theorem Compile_exit_lt (sb : Nat) (c : Cmd) : Compile.exit sb c < (Compile sb c).states :=
  (compileCmd sb c).exit_lt

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

/-! ## ★ The C2 assembly toolkit (relocated upstream 2026-06-06 from PolyTime.lean)

Threading lemmas + the residue-induction assembly `run_physical_residue_gen`,
moved here so they sit BEFORE `Compile_run_physical_residue` and can discharge it
(they were downstream in PolyTime.lean). See HANDOFF.md. -/

/-- **`inBounds` from a static `UsesBelow` bound (the `inBounds`-threading
bridge; lives here because it relates `Op.UsesBelow` in `Frame` to `Op.inBounds`
in `Compile`).** An op that statically touches only registers `< k`, run on a
state of width `≥ k`, is in bounds. Combined with `Op.eval_length_ge` /
`Cmd.eval_length_ge` (the register count never shrinks) and `Cmd.UsesBelow`, this
supplies the `o.inBounds s` premise of `Op.eval_preserves_BitState` and of the
per-op gadgets at *every* fragment of the `Compile_run_physical_residue`
induction: fix `k ≤ s.length` with `Cmd.UsesBelow c k`, and every reached state
keeps width `≥ k`. -/
theorem Op.inBounds_of_UsesBelow (o : Op) (k : Nat) (s : State)
    (h : Op.UsesBelow o k) (hk : k ≤ s.length) : o.inBounds s := by
  cases o with
  | clear dst => exact Nat.lt_of_lt_of_le h hk
  | appendOne dst => exact Nat.lt_of_lt_of_le h hk
  | appendZero dst => exact Nat.lt_of_lt_of_le h hk
  | copy dst src => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  | tail dst src => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  | head dst src => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  | eqBit dst a b =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk,
             Nat.lt_of_lt_of_le h.2.2 hk⟩
  | nonEmpty dst src => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  | takeAt dst src l =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk,
             Nat.lt_of_lt_of_le h.2.2 hk⟩
  | dropAt dst src l =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk,
             Nat.lt_of_lt_of_le h.2.2 hk⟩
  | concat dst a b =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk,
             Nat.lt_of_lt_of_le h.2.2 hk⟩
  | consLen dst l src =>
      -- `Op.inBounds` orders consLen's last two as `src, lenSrc`; `UsesBelow` as
      -- `lenSrc, src` — so the second/third components swap.
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.2 hk,
             Nat.lt_of_lt_of_le h.2.1 hk⟩

/-- An op other than `consLen`. `consLen` is the unique op that can break
`BitState` (`Op.consLen_breaks_BitState`); this is the (temporary) syntactic
condition under which `BitState` preservation is unconditional. HANDOFF bottom-up Task 4 restates
`consLen` to write a unary block, after which the side-condition is discharged
for free and this predicate can be dropped. -/
def Op.NotConsLen : Op → Prop
  | .consLen _ _ _ => False
  | _ => True

/-- A `Cmd` with no `consLen` op anywhere. -/
def Cmd.NoConsLen : Cmd → Prop
  | .op o            => Op.NotConsLen o
  | .seq c1 c2       => Cmd.NoConsLen c1 ∧ Cmd.NoConsLen c2
  | .ifBit _ cT cE   => Cmd.NoConsLen cT ∧ Cmd.NoConsLen cE
  | .forBnd _ _ body => Cmd.NoConsLen body

/-- **`BitState` is preserved by a `consLen`-free `Cmd` (the residue induction's
invariant, validated end-to-end).** Threads the two per-op atoms
(`Op.eval_preserves_BitState` for `BitState`, `Op.inBounds_of_UsesBelow` for
`inBounds`) and register-count monotonicity (`Cmd.eval_length_ge`,
`State.set_length_ge`) through the full `Cmd` induction — including the `forBnd`
fold, whose invariant is `k ≤ width ∧ BitState`. This is exactly the
invariant-threading `Compile_run_physical_residue` performs, so proving it
standalone de-risks that induction: the `forBnd` counter-write (`BitState_set_pad`
+ width growth) and the `seq` width-carry both go through.

The `Cmd.UsesBelow c k`/`k ≤ s.length` pair is the wellformedness hypothesis the
obligation will carry; `NoConsLen` is the one piece HANDOFF bottom-up Task 4 removes (by restating
`consLen` unary). -/
theorem Cmd.eval_preserves_BitState (c : Cmd) (k : Nat) (s : State)
    (huses : Cmd.UsesBelow c k) (hk : k ≤ s.length)
    (hnc : Cmd.NoConsLen c) (hbit : Compile.BitState s) :
    Compile.BitState (c.eval s) := by
  induction c generalizing s with
  | op o =>
      refine Op.eval_preserves_BitState o s hbit
        (Op.inBounds_of_UsesBelow o k s huses hk) ?_
      intro dst lenSrc src heq
      subst heq
      simp only [Cmd.NoConsLen, Op.NotConsLen] at hnc
  | seq c1 c2 ih1 ih2 =>
      rw [Cmd.eval_seq]
      have hbit1 : Compile.BitState (c1.eval s) := ih1 s huses.1 hk hnc.1 hbit
      have hk1 : k ≤ (c1.eval s).length := Nat.le_trans hk (Cmd.eval_length_ge c1 s)
      exact ih2 (c1.eval s) huses.2 hk1 hnc.2 hbit1
  | ifBit t cT cE ihT ihE =>
      by_cases hb : s.get t = [1]
      · rw [Cmd.eval_ifBit_true t cT cE s hb]
        exact ihT s huses.2.1 hk hnc.1 hbit
      · rw [Cmd.eval_ifBit_false t cT cE s hb]
        exact ihE s huses.2.2 hk hnc.2 hbit
  | forBnd cnt bnd body ihbody =>
      obtain ⟨_, _, hbody⟩ := huses
      rw [Cmd.eval_forBnd]
      refine (Cmd.foldlState_range_induct body cnt (s.get bnd).length s
        (fun _ st => k ≤ st.length ∧ Compile.BitState st) ⟨hk, hbit⟩ ?_).2
      intro i st _ hM
      obtain ⟨hkst, hbst⟩ := hM
      have hset_bit : Compile.BitState (st.set cnt (List.replicate i 1)) :=
        Compile.BitState_set_pad st cnt _ hbst (by
          intro x hx; obtain ⟨-, rfl⟩ := List.mem_replicate.mp hx; exact Nat.le_refl 1)
      have hset_k : k ≤ (st.set cnt (List.replicate i 1)).length :=
        Nat.le_trans hkst (State.set_length_ge st cnt _)
      exact ⟨Nat.le_trans hset_k (Cmd.eval_length_ge body _),
        ihbody (st.set cnt (List.replicate i 1)) hbody hset_k hnc hset_bit⟩

/-! ## ★ TOP-DOWN ASSEMBLY DESIGN (2026-06-06) — the residue induction skeleton

This block is the **top-down** design of the proof of `Compile_run_physical_residue`
(`Compile.lean:8910`, the central C2 obligation). It pins the **shared interface**
between the two work streams (see `HANDOFF.md`): the four per-fragment
physical-residue contracts (op / seq / ifBit / forBnd) compose into the obligation
by induction on `Cmd`. The composition has been **validated by hand** (budget,
residue, defeq); the remaining work is mechanical (the W-invariant + budget Nat
arithmetic) plus the two `sorry`-bodied combinators below — which are gated on the
bottom-up stream building the real `compileForBnd` / `compileTestBit` machines (today
both are 0-transition stubs).

⚠ These lemmas live here (not in `Compile.lean`) because they call the threading
lemmas `Cmd.eval_preserves_BitState` / `Op.inBounds_of_UsesBelow` / `Cmd.NoConsLen`
which are defined above in this file — *downstream* of the obligation they must
discharge. **To actually close `Compile_run_physical_residue`, relocate those
threading lemmas (and this block) upstream into `Compile.lean`** (all their deps are
already available there). See HANDOFF.md "TOP-DOWN findings", GAP 3. -/

/-- **Compositional per-fragment TM-step budget.** A `Compile` fragment whose
physical tape stays `≤ G` cells and which runs `cost` layer-ops halts within
`(9·G² + 9·G + 33)·(8·cost + 8) + cost` steps: **8 budget units per cost item**
(each unit one `O(G²)` single-tape pass), plus `+cost` slack for `seq` control
steps.

Chosen because it is **exactly superadditive** under `seq`:
`physStepBudget G (1 + c₁ + c₂) = physStepBudget G c₁ + 1 + physStepBudget G c₂`.
The quadratic `Compile.overhead (·+1)²` fails this (ROADMAP Finding #3): summing
`~cost` per-op quadratics is cubic, and it dropped both the register count `s.length`
and the residue length. `inOPoly`/`monotonic` in both arguments, which is all the
downstream consumers (`toFrameworkWitness'`, `bitDecider_run`) need.

**⚠ Why 8 units per cost item, not 1 (2026-06-11 top-down finding — do not
re-tighten).** The `forBnd` machine must do per-iteration *bookkeeping* the layer
cost does not see: rebuild `counter := replicate i 1` from the scratch master
(one cursor-copy pass), maintain the remaining/done counts (`tail`/`appendOne`
passes), and run the loop test — ~5–6 `O(G²)` passes per iteration, plus
entry/exit snapshots. The loop's cost lump `iters²` grants `iters²` cost items
against `~6·iters` bookkeeping passes, which at 1 unit/item is **unsatisfiable
for `iters ≤ 5`** (machine-independent: `6·iters ≰ iters² + 2` at `iters = 1`).
With 8 units per item the worst case (`iters = 1`: 8 + bookkeeping ≤ 24 units)
clears with slack. Scaling the multiplier preserves exact superadditivity
(`U·(8a+8) + a + 1 + U·(8b+8) + b = U·(8(1+a+b)+8) + (1+a+b)`). -/
def Compile.physStepBudget (G cost : Nat) : Nat :=
  (9 * G * G + 9 * G + 33) * (8 * cost + 8) + cost

/-- **`physStepBudget` is exactly superadditive under `seq`.** The `seq`
control step (`+1`) plus the two fragments' budgets land exactly on the
composed budget — this is the algebraic fact that makes the `seq` case of
`Compile.run_physical_residue_gen` close (and that the quadratic `overhead`
failed, ROADMAP Finding #3). -/
theorem Compile.physStepBudget_seq (G a b : Nat) :
    Compile.physStepBudget G a + 1 + Compile.physStepBudget G b
      = Compile.physStepBudget G (1 + a + b) := by
  simp only [Compile.physStepBudget]; ring

/-- `physStepBudget` is monotone in both the tape bound and the op count. -/
theorem Compile.physStepBudget_mono {G G' cost cost' : Nat}
    (hG : G ≤ G') (hc : cost ≤ cost') :
    Compile.physStepBudget G cost ≤ Compile.physStepBudget G' cost' := by
  unfold Compile.physStepBudget; gcongr

/-- The diagonal of `physStepBudget` is a cubic, hence `inOPoly`. With
`physStepBudget_mono` this is the interface the budget restatement (GAP 4) feeds to
`toFrameworkWitness'` in place of `overhead_poly`/`overhead_mono`. -/
theorem Compile.physStepBudget_poly :
    inOPoly (fun m => Compile.physStepBudget m m) := by
  refine ⟨3, 817, 1, ?_⟩
  intro m hm
  show Compile.physStepBudget m m ≤ 817 * m ^ 3
  have hm1 : 1 ≤ m := hm
  have h0 : (1 : Nat) ≤ m ^ 3 := by
    calc (1 : Nat) = m ^ 0 := by simp
      _ ≤ m ^ 3 := Nat.pow_le_pow_right hm1 (by norm_num)
  have h1 : m ≤ m ^ 3 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 3 := Nat.pow_le_pow_right hm1 (by norm_num)
  have h2 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right hm1 (by norm_num)
  have e : Compile.physStepBudget m m = 72 * m ^ 3 + 144 * m ^ 2 + 337 * m + 264 := by
    simp only [Compile.physStepBudget]; ring
  rw [e]; omega

/-- **Residue-tolerant `compileIfBit` contract (GAP 1 — pinned interface, `sorry`).**
The incoming-residue generalisation of `compileIfBit_sound_physical`
(`Compile.lean:8565`), in the shape the `ifBit` case of `run_physical_residue_gen`
needs: the chosen branch's residue run, threaded through the tester (`+3` control
steps) and the `joinTwoHalts` rewind bracket. Gated on a real `compileTestBit`
(today a 0-transition stub). The `+3 ≤` one extra `physStepBudget` unit, so the
budget composes with room. -/
theorem compileIfBit_sound_physical_residue
    (t : Var) (rT rE : CompiledCmd)
    (evalT evalE : State → State) (costT costE : State → Nat)
    (G : Nat) (s : State) (res0 : List Nat)
    -- `ht`/`hG` (added 2026-06-11): the tester must physically navigate to
    -- register `t` (so it must exist), and its step count is linear in the tape
    -- length, so the budget needs the tape bound `G`. Both are available at the
    -- single call site (`run_physical_residue_gen`: `huses.1` + its own `hG`).
    (ht : t < s.length)
    (hbit : Compile.BitState s) (hres0 : Compile.ValidResidue res0)
    (hG : State.size s + s.length + res0.length + 2 ≤ G)
    (hT : s.get t = [1] →
      ∃ (tt : Nat) (res : List Nat),
        Compile.ValidResidue res ∧
        State.size (evalT s) + res.length ≤ State.size s + res0.length + costT s ∧
        runFlatTM tt rT.M (initFlatConfig rT.M [Compile.encodeTape s ++ res0])
          = some { state_idx := rT.exit,
                   tapes := [([], 0, Compile.encodeTape (evalT s) ++ res)] } ∧
        (∀ k, k < tt → ∀ ck,
            runFlatTM k rT.M (initFlatConfig rT.M [Compile.encodeTape s ++ res0]) = some ck →
            ck.state_idx ≠ rT.exit ∧ haltingStateReached rT.M ck = false) ∧
        tt ≤ Compile.physStepBudget G (costT s))
    (hE : s.get t ≠ [1] →
      ∃ (tt : Nat) (res : List Nat),
        Compile.ValidResidue res ∧
        State.size (evalE s) + res.length ≤ State.size s + res0.length + costE s ∧
        runFlatTM tt rE.M (initFlatConfig rE.M [Compile.encodeTape s ++ res0])
          = some { state_idx := rE.exit,
                   tapes := [([], 0, Compile.encodeTape (evalE s) ++ res)] } ∧
        (∀ k, k < tt → ∀ ck,
            runFlatTM k rE.M (initFlatConfig rE.M [Compile.encodeTape s ++ res0]) = some ck →
            ck.state_idx ≠ rE.exit ∧ haltingStateReached rE.M ck = false) ∧
        tt ≤ Compile.physStepBudget G (costE s)) :
    let chosen := if s.get t = [1] then evalT s else evalE s
    let chosenCost := if s.get t = [1] then costT s else costE s
    ∃ (tt : Nat) (res : List Nat),
      Compile.ValidResidue res ∧
      State.size chosen + res.length ≤ State.size s + res0.length + (1 + chosenCost) ∧
      runFlatTM tt (compileIfBit t rT rE).M
          (initFlatConfig (compileIfBit t rT rE).M [Compile.encodeTape s ++ res0])
        = some { state_idx := (compileIfBit t rT rE).exit,
                 tapes := [([], 0, Compile.encodeTape chosen ++ res)] } ∧
      (∀ k, k < tt → ∀ ck,
          runFlatTM k (compileIfBit t rT rE).M
              (initFlatConfig (compileIfBit t rT rE).M [Compile.encodeTape s ++ res0]) = some ck →
          ck.state_idx ≠ (compileIfBit t rT rE).exit ∧
          haltingStateReached (compileIfBit t rT rE).M ck = false) ∧
      tt ≤ Compile.physStepBudget G (1 + chosenCost) := by
  -- The tester is REAL now (`compileTestBit`, 2026-06-11): navigate + read +
  -- rewind, leaving the tape unchanged with the head at `0`, so the chosen
  -- branch literally starts from its own `initFlatConfig`.
  intro chosen chosenCost
  set tester := compileTestBit t with htester
  set branched := branchComposeFlatTM tester.M rT.M rE.M tester.exitPos tester.exitNeg
    with hbranched
  set haltE := tester.M.states + rT.M.states + rE.exit with hhaltE
  set haltT := tester.M.states + rT.exit with hhaltT
  have hMeq : (compileIfBit t rT rE).M = Compile.joinTwoHalts branched haltE haltT := rfl
  have hexit_eq : (compileIfBit t rT rE).exit = haltE := rfl
  have hstart : (compileIfBit t rT rE).M.start = 0 := by
    rw [hMeq, Compile.joinTwoHalts_start, hbranched, branchComposeFlatTM_start]
    exact compileTestBit_start t
  have hinit : initFlatConfig (compileIfBit t rT rE).M [Compile.encodeTape s ++ res0]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res0)] } := by
    simp only [initFlatConfig, hstart, List.map_cons, List.map_nil]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res0)] }
    with hcfg0
  have hLG : (Compile.encodeTape s ++ res0).length ≤ G := by
    rw [List.length_append, Compile.encodeTape_length]; omega
  have hbudget0 : Compile.physStepBudget G 0 = (9 * G * G + 9 * G + 33) * 8 := by
    simp only [Compile.physStepBudget]; omega
  have hcfg0_lt : (0 : Nat) < tester.M.states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) tester.exitPos_lt
  -- the seam symbol at head 0 is the leading sentinel `3`.
  have hsym3 : ∀ (s' : State) (res' : List Nat),
      currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s' ++ res') = some 3 := by
    intro s' res'
    rw [show Compile.encodeTape s' ++ res'
        = 3 :: (Compile.encodeRegs s' ++ [Compile.endMark] ++ res') from by
      rw [Compile.encodeTape]
      simp only [Compile.endMark, List.cons_append, List.append_assoc]]
    rfl
  have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res0) = some v →
      v < max tester.M.sig (max rT.M.sig rE.M.sig) := by
    intro v hv
    rw [hsym3 s res0] at hv
    obtain rfl : (3 : Nat) = v := Option.some.inj hv
    calc (3 : Nat) < 4 := by omega
      _ = tester.M.sig := tester.M_sig.symm
      _ ≤ _ := le_max_left _ _
  have hh1 : branched.halt[haltE]? = some true := by
    rw [hbranched, hhaltE]
    exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _ rT.M_valid rE.exit_is_halt
  have hh2 : branched.halt[haltT]? = some true := by
    rw [hbranched, hhaltT]
    exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _ rT.M_valid rT.exit_lt
      rT.exit_is_halt
  have hne : haltE ≠ haltT := by
    have := rT.exit_lt
    rw [hhaltE, hhaltT]
    omega
  by_cases hb : s.get t = [1]
  · -- TRUE branch: tester POS → `rT` → demoted `haltT` → bridge to `haltE`.
    obtain ⟨tt, res, hres, hW, hrun, htraj, hbud⟩ := hT hb
    obtain ⟨Tt, htest_run, htest_traj, htest_bud⟩ :=
      Compile.testBitReg_run_pos t s res0 ht hbit hb
    have hinitT : initFlatConfig rT.M [Compile.encodeTape s ++ res0]
        = { state_idx := rT.M.start, tapes := [([], 0, Compile.encodeTape s ++ res0)] } := by
      simp only [initFlatConfig, List.map_cons, List.map_nil]
    rw [hinitT] at hrun htraj
    have hraw := branchComposeFlatTM_run_pos tester.exit_distinct
      tester.M_valid rT.M_valid rE.M_valid tester.exitPos_lt tester.exitNeg_lt
      cfg0 hcfg0_lt [] 0 (Compile.encodeTape s ++ res0) hsymb
      htest_run htest_traj hrun
      (Compile.haltingStateReached_of_halt rT.exit_is_halt)
    have hraw_traj := branchComposeFlatTM_no_early_halt_pos
      tester.M_valid rT.M_valid rE.M_valid tester.exitPos_lt tester.exitNeg_lt
      cfg0 hcfg0_lt [] 0 (Compile.encodeTape s ++ res0) hsymb
      htest_run htest_traj
      (fun k hk ck hck => (htraj k hk ck hck).2)
    have hstate_eq : rT.exit + tester.M.states = haltT := by
      rw [hhaltT]; omega
    rw [hstate_eq] at hraw
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted branched haltE haltT
      cfg0 (Tt + 1 + tt) [] (Compile.encodeTape (evalT s) ++ res) 0
      hraw.1 (fun k hk ck hck => hraw_traj k hk ck hck) hh1 hh2 hne
      (by
        intro v hv
        rw [hsym3 (evalT s) res] at hv
        obtain rfl : (3 : Nat) = v := Option.some.inj hv
        rw [hbranched, branchComposeFlatTM_sig, tester.M_sig, rT.M_sig, rE.M_sig]
        decide)
    refine ⟨Tt + 1 + tt + 1, res, hres, ?_, ?_, ?_, ?_⟩
    · -- ① W-invariant.
      show State.size chosen + res.length ≤ State.size s + res0.length + (1 + chosenCost)
      simp only [chosen, chosenCost, if_pos hb]
      omega
    · -- run.
      rw [hinit, hMeq, hexit_eq]
      simp only [chosen, if_pos hb]
      exact hjoin
    · -- trajectory.
      intro k hk ck hck
      rw [hinit, hMeq] at hck
      obtain ⟨hne1, hnh⟩ := hjoin_traj k hk ck hck
      rw [hexit_eq, hMeq]
      exact ⟨hne1, hnh⟩
    · -- ② budget: tester (≤ 3·G+12) + bridges fit one extra `physStepBudget` unit.
      simp only [chosenCost, if_pos hb]
      rw [show (1 : Nat) + costT s = 1 + 0 + costT s from by omega,
          ← Compile.physStepBudget_seq G 0 (costT s)]
      omega
  · -- FALSE branch: tester NEG → `rE` → the kept `haltE` directly.
    obtain ⟨tt, res, hres, hW, hrun, htraj, hbud⟩ := hE hb
    obtain ⟨Tt, htest_run, htest_traj, htest_bud⟩ :=
      Compile.testBitReg_run_neg t s res0 ht hbit hb
    have hinitE : initFlatConfig rE.M [Compile.encodeTape s ++ res0]
        = { state_idx := rE.M.start, tapes := [([], 0, Compile.encodeTape s ++ res0)] } := by
      simp only [initFlatConfig, List.map_cons, List.map_nil]
    rw [hinitE] at hrun htraj
    have hraw := branchComposeFlatTM_run_neg tester.exit_distinct
      tester.M_valid rT.M_valid rE.M_valid tester.exitPos_lt tester.exitNeg_lt
      cfg0 hcfg0_lt [] 0 (Compile.encodeTape s ++ res0) hsymb
      htest_run htest_traj hrun
      (Compile.haltingStateReached_of_halt rE.exit_is_halt)
    have hraw_traj := branchComposeFlatTM_no_early_halt_neg tester.exit_distinct
      tester.M_valid rT.M_valid rE.M_valid tester.exitPos_lt tester.exitNeg_lt
      cfg0 hcfg0_lt [] 0 (Compile.encodeTape s ++ res0) hsymb
      htest_run htest_traj
      (fun k hk ck hck => (htraj k hk ck hck).2)
    have hstate_eq : rE.exit + (tester.M.states + rT.M.states) = haltE := by
      rw [hhaltE]; omega
    rw [hstate_eq] at hraw
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept branched haltE haltT
      cfg0 (Tt + 1 + tt) ([], 0, Compile.encodeTape (evalE s) ++ res)
      hraw.1 (fun k hk ck hck => hraw_traj k hk ck hck) hh1 hh2
    refine ⟨Tt + 1 + tt, res, hres, ?_, ?_, ?_, ?_⟩
    · show State.size chosen + res.length ≤ State.size s + res0.length + (1 + chosenCost)
      simp only [chosen, chosenCost, if_neg hb]
      omega
    · rw [hinit, hMeq, hexit_eq]
      simp only [chosen, if_neg hb]
      exact hjoin
    · intro k hk ck hck
      rw [hinit, hMeq] at hck
      obtain ⟨hne1, hnh⟩ := hjoin_traj k hk ck hck
      rw [hexit_eq, hMeq]
      exact ⟨hne1, hnh⟩
    · simp only [chosenCost, if_neg hb]
      rw [show (1 : Nat) + costE s = 1 + 0 + costE s from by omega,
          ← Compile.physStepBudget_seq G 0 (costE s)]
      omega

/-- **Residue-tolerant `compileForBnd` contract (GAP 1 — RE-PINNED 2026-06-11,
`sorry`).** The scratch-register fix for the snapshot-vs-clobber gap: the previous
pinning (no scratch interface) was **unprovable** — `Cmd.run` snapshots
`iters = |s.get bound|` at loop entry, the body may legally clobber `bound` AND
`counter` mid-loop, a TM cannot hold a runtime count in finite control, and no
tape region past the terminator survives a body run (the body contract's exit
residue is existential). The only sound storage is a register the body provably
never touches, so `compileForBnd` is now compiled at a **static scratch base
`sb`** with `K1 = sb` (remaining count, snapshotted from `bound` at entry) and
`K2 = sb + 1` (done count, an all-`1`s block — exactly the `replicate i 1` that
`counter` is re-materialised from each round). See `compileForBnd`'s docstring
for the pinned machine and the validated W-invariant/budget accounting.

Premises (mirroring what the `forBnd` case of `run_physical_residue_gen`
supplies):
- `hcnt`/`hbnd`: the program registers `counter`/`bound` lie below the scratch;
- `hlen`: the tape physically contains the scratch registers of this loop AND
  of every nested loop (`sb + 2 + 2·body.loopDepth ≤ s.length`);
- `hscratch`: all registers `≥ sb` are empty at entry (`K1`/`K2` start `[]`;
  the machine restores them to `[]` at exit — the exit tape is
  `encodeTape ((forBnd …).eval s) ++ res` and `(forBnd …).eval` never touches
  registers `≥ sb`, so emptiness at exit is forced by the contract shape);
- `hbody`: the body contract at scratch base `sb + 2`, quantified over every
  state with ITS scratch empty (the loop's fold states hold counts in `K1`/`K2 <
  sb + 2`, so they satisfy it) and its OWN per-call tape bound `G'` (the
  fold-state sizes grow, so a single fixed bound is dishonest). -/
theorem compileForBnd_sound_physical_residue
    (counter bound : Var) (sb : Nat) (rbody : CompiledCmd) (body : Cmd)
    (G : Nat) (s : State) (res0 : List Nat)
    (hbit : Compile.BitState s)
    (hcnt : counter < sb) (hbnd : bound < sb)
    (hlen : sb + 2 + 2 * body.loopDepth ≤ s.length)
    (hscratch : ∀ r, sb ≤ r → State.get s r = [])
    (hres0 : Compile.ValidResidue res0)
    (hbody : ∀ (s' : State) (res' : List Nat) (G' : Nat),
      Compile.BitState s' → sb + 2 + 2 * body.loopDepth ≤ s'.length →
      (∀ r, sb + 2 ≤ r → State.get s' r = []) →
      Compile.ValidResidue res' →
      State.size s' + s'.length + res'.length + body.cost s' + 2 ≤ G' →
      ∃ (tt : Nat) (res : List Nat),
        Compile.ValidResidue res ∧
        State.size (body.eval s') + res.length ≤ State.size s' + res'.length + body.cost s' ∧
        runFlatTM tt rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res'])
          = some { state_idx := rbody.exit,
                   tapes := [([], 0, Compile.encodeTape (body.eval s') ++ res)] } ∧
        (∀ kk, kk < tt → ∀ ck,
            runFlatTM kk rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res']) = some ck →
            ck.state_idx ≠ rbody.exit ∧ haltingStateReached rbody.M ck = false) ∧
        tt ≤ Compile.physStepBudget G' (body.cost s')) :
    ∃ (tt : Nat) (res : List Nat),
      Compile.ValidResidue res ∧
      State.size ((Cmd.forBnd counter bound body).eval s) + res.length
        ≤ State.size s + res0.length + (Cmd.forBnd counter bound body).cost s ∧
      runFlatTM tt (compileForBnd counter bound sb rbody).M
          (initFlatConfig (compileForBnd counter bound sb rbody).M [Compile.encodeTape s ++ res0])
        = some { state_idx := (compileForBnd counter bound sb rbody).exit,
                 tapes := [([], 0,
                   Compile.encodeTape ((Cmd.forBnd counter bound body).eval s) ++ res)] } ∧
      (∀ k, k < tt → ∀ ck,
          runFlatTM k (compileForBnd counter bound sb rbody).M
              (initFlatConfig (compileForBnd counter bound sb rbody).M
                [Compile.encodeTape s ++ res0]) = some ck →
          ck.state_idx ≠ (compileForBnd counter bound sb rbody).exit ∧
          haltingStateReached (compileForBnd counter bound sb rbody).M ck = false) ∧
      tt ≤ Compile.physStepBudget G ((Cmd.forBnd counter bound body).cost s) := by
  sorry  -- GAP 1+2 (bottom-up, gated on the cursor-copy/`tail` op gadgets):
         -- build the real `compileForBnd` per its docstring (loopTM skeleton,
         -- bookkeeping = cursor-copy/appendOne/tail-delete op gadgets), then
         -- loop induction over the iteration fold with the body contract.

/-- **★ The designed residue induction (the assembly of `Compile_run_physical_residue`).**
Carries an arbitrary incoming residue `res0` (live instance: `res0 = []`), a shared
tape bound `G` (`hG`), and the threading hyps. The conclusion bundles:
- **① the W-invariant** `State.size (c.eval s) + |res| ≤ State.size s + |res0| + c.cost s`
  (joint size+residue grows by ≤ cost; non-compounding — this is what keeps the
  residue polynomially bounded and lets one `G` bound every sub-fragment tape);
- the residue-tolerant physical run + trajectory;
- **② the budget** `t ≤ physStepBudget G (c.cost s)` (exactly superadditive).

**Proof design (induction on `c`):**
- `op o`: `compileOp_sound_physical_residue` (`hbnd` from `Op.inBounds_of_UsesBelow`);
  ① per-op from the residue formula (append/clear/head/nonEmpty: equality;
  the 7 sorry ops owe it — see HANDOFF top-down step 4); ② from `9·L²+9·L+30`, `L ≤ G`.
- `seq c1 c2`: IH₁ on `(s,res0)` → `(mid,res1)`; `BitState mid`,`k ≤ mid.length` via
  `Cmd.eval_preserves_BitState`/`Cmd.eval_length_ge`; IH₂ on `(mid,res1)`;
  `compileSeq_sound_physical_residue` (run+halt) + `compileSeq_traj_physical_residue`
  (trajectory). ① telescopes; ② is the exact `physStepBudget` superadditivity.
- `ifBit`/`forBnd`: dispatch to the two residue combinators above (their hyps are the IHs).

The `op`/`seq` cases are the structural heart; they reduce to PROVEN combinators.
Body is `sorry` pending the relocation upstream (GAP 3) + the two combinators. -/
theorem Compile.run_physical_residue_gen (c : Cmd) (k : Nat) (s : State)
    (res0 : List Nat) (G : Nat)
    (hbit : Compile.BitState s) (hk : k + 2 * c.loopDepth ≤ s.length)
    (huses : Cmd.UsesBelow c k)
    (hscratch : ∀ r, k ≤ r → State.get s r = [])
    (hnc : Cmd.NoConsLen c)
    (hres0 : Compile.ValidResidue res0)
    (hG : State.size s + s.length + res0.length + c.cost s + 2 ≤ G) :
    ∃ (t : Nat) (res : List Nat),
      Compile.ValidResidue res ∧
      State.size (c.eval s) + res.length ≤ State.size s + res0.length + c.cost s ∧
      runFlatTM t (Compile k c) (initFlatConfig (Compile k c) [Compile.encodeTape s ++ res0])
          = some { state_idx := Compile.exit k c,
                   tapes := [([], 0, Compile.encodeTape (c.eval s) ++ res)] } ∧
      (∀ k', k' < t → ∀ ck,
          runFlatTM k' (Compile k c)
              (initFlatConfig (Compile k c) [Compile.encodeTape s ++ res0]) = some ck →
          ck.state_idx ≠ Compile.exit k c ∧
          haltingStateReached (Compile k c) ck = false) ∧
      t ≤ Compile.physStepBudget G (c.cost s) := by
  induction c generalizing k s res0 G with
  | op o =>
      -- `op` reduces to the per-op residue contract. `inBounds` from the static bound.
      have hks : k ≤ s.length := by
        simp only [Cmd.loopDepth] at hk; omega
      have hbnd : o.inBounds s := Op.inBounds_of_UsesBelow o k s huses hks
      obtain ⟨t, res_out, hres, hW, hrun, htraj, hbud⟩ :=
        compileOp_sound_physical_residue o s res0 hbit hbnd hres0
      refine ⟨t, res_out, hres, hW, hrun, htraj, ?_⟩
      · -- ② budget: `(9·L²+9·L+30)·(cost+1) ≤ physStepBudget G (Op.cost o s)`, since
        -- `L ≤ G` and `(9G²+9G+30)·(cost+1)` sits termwise under `(9G²+9G+33)·(8·cost+8)`.
        -- Explicit `Nat.*` monotonicity terms throughout: `omega`/`gcongr` hit `whnf`
        -- timeouts on products of two-atom sums (the recorded gotcha).
        have hL : (Compile.encodeTape s ++ res0).length ≤ G := by
          rw [List.length_append, Compile.encodeTape_length]; omega
        set L := (Compile.encodeTape s ++ res0).length with hLdef
        have h1 : (9 * L * L + 9 * L + 30) * (Op.cost o s + 1)
                  ≤ (9 * G * G + 9 * G + 30) * (Op.cost o s + 1) :=
          Nat.mul_le_mul_right _
            (Nat.add_le_add
              (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 9 hL) hL)
                (Nat.mul_le_mul_left 9 hL)) (Nat.le_refl 30))
        have h2 : (9 * G * G + 9 * G + 30) * (Op.cost o s + 1)
                  ≤ (9 * G * G + 9 * G + 33) * (8 * Op.cost o s + 8) :=
          Nat.mul_le_mul (by omega) (by omega)
        show t ≤ Compile.physStepBudget G (Op.cost o s)
        rw [Compile.physStepBudget]
        exact le_trans (le_trans hbud (le_trans h1 h2)) (Nat.le_add_right _ _)
  | seq c1 c2 ih1 ih2 =>
      -- thread residue `res0 → res1 → res2` through both fragments.
      simp only [Cmd.loopDepth] at hk
      have hd1 : c1.loopDepth ≤ max c1.loopDepth c2.loopDepth := Nat.le_max_left _ _
      have hd2 : c2.loopDepth ≤ max c1.loopDepth c2.loopDepth := Nat.le_max_right _ _
      have hks : k ≤ s.length := by omega
      have hk1' : k + 2 * c1.loopDepth ≤ s.length := by omega
      have hG1 : State.size s + s.length + res0.length + c1.cost s + 2 ≤ G := by
        rw [Cmd.cost_seq] at hG; omega
      obtain ⟨t1, res1, hres1, hW1, hrun1, htraj1, hbud1⟩ :=
        ih1 k s res0 G hbit hk1' huses.1 hscratch hnc.1 hres0 hG1
      have hbit_mid : Compile.BitState (c1.eval s) :=
        Cmd.eval_preserves_BitState c1 k s huses.1 hks hnc.1 hbit
      have hmidge : s.length ≤ (c1.eval s).length := Cmd.eval_length_ge c1 s
      have hk2' : k + 2 * c2.loopDepth ≤ (c1.eval s).length := by omega
      have hmidlen : (c1.eval s).length ≤ s.length := by
        have := Cmd.eval_length_le c1 k huses.1 s; rwa [Nat.max_eq_left hks] at this
      have hscratch_mid : ∀ r, k ≤ r → State.get (c1.eval s) r = [] := fun r hr => by
        rw [Cmd.eval_get_frame c1 k huses.1 s r hr]; exact hscratch r hr
      have hG2 : State.size (c1.eval s) + (c1.eval s).length + res1.length
                    + c2.cost (c1.eval s) + 2 ≤ G := by
        rw [Cmd.cost_seq] at hG; omega
      obtain ⟨t2, res2, hres2, hW2, hrun2, htraj2, hbud2⟩ :=
        ih2 k (c1.eval s) res1 G hbit_mid hk2' huses.2 hscratch_mid hnc.2 hres1 hG2
      have hhalt2 : haltingStateReached (compileCmd k c2).M
          { state_idx := (compileCmd k c2).exit,
            tapes := [([], 0, Compile.encodeTape (c2.eval (c1.eval s)) ++ res2)] } = true := by
        have hex := (compileCmd k c2).exit_is_halt
        show (compileCmd k c2).M.halt.getD (compileCmd k c2).exit false = true
        simp only [List.getD, hex, Option.getD]
      obtain ⟨hrunseq, _⟩ := compileSeq_sound_physical_residue (compileCmd k c1) (compileCmd k c2)
        s (c1.eval s) (c2.eval (c1.eval s)) res0 res1 res2 hbit_mid hres1
        hrun1 htraj1 hrun2 hhalt2
      have htrajseq := compileSeq_traj_physical_residue (compileCmd k c1) (compileCmd k c2)
        s (c1.eval s) res0 res1 hbit_mid hres1 hrun1 htraj1 htraj2
      refine ⟨t1 + 1 + t2, res2, hres2, ?_, ?_, ?_, ?_⟩
      · -- ① telescopes from hW1, hW2.
        rw [Cmd.eval_seq, Cmd.cost_seq]; omega
      · -- run.
        rw [Cmd.eval_seq]; exact hrunseq
      · -- trajectory.
        exact htrajseq
      · -- ② exact `physStepBudget` superadditivity.
        rw [Cmd.cost_seq, ← Compile.physStepBudget_seq]; omega
  | ifBit tt cT cE ihT ihE =>
      -- dispatch to the residue branch combinator; the IHs supply the branch contracts.
      simp only [Cmd.loopDepth] at hk
      have hdT : cT.loopDepth ≤ max cT.loopDepth cE.loopDepth := Nat.le_max_left _ _
      have hdE : cE.loopDepth ≤ max cT.loopDepth cE.loopDepth := Nat.le_max_right _ _
      have hks : k ≤ s.length := by omega
      have hT : s.get tt = [1] → _ := fun htrue =>
        ihT k s res0 G hbit (by omega) huses.2.1 hscratch hnc.1 hres0 (by
          have hc := Cmd.cost_ifBit_true tt cT cE s htrue; rw [hc] at hG; omega)
      have hE : s.get tt ≠ [1] → _ := fun hfalse =>
        ihE k s res0 G hbit (by omega) huses.2.2 hscratch hnc.2 hres0 (by
          have hc := Cmd.cost_ifBit_false tt cT cE s hfalse; rw [hc] at hG; omega)
      have htlt : tt < s.length := Nat.lt_of_lt_of_le huses.1 hks
      have hG' : State.size s + s.length + res0.length + 2 ≤ G := by omega
      have hcomb := compileIfBit_sound_physical_residue tt (compileCmd k cT) (compileCmd k cE)
        cT.eval cE.eval cT.cost cE.cost G s res0 htlt hbit hres0 hG' hT hE
      have heval : (Cmd.ifBit tt cT cE).eval s
          = if s.get tt = [1] then cT.eval s else cE.eval s := by
        by_cases hb : s.get tt = [1]
        · rw [Cmd.eval_ifBit_true tt cT cE s hb, if_pos hb]
        · rw [Cmd.eval_ifBit_false tt cT cE s hb, if_neg hb]
      have hcost : (Cmd.ifBit tt cT cE).cost s
          = 1 + if s.get tt = [1] then cT.cost s else cE.cost s := by
        by_cases hb : s.get tt = [1]
        · rw [Cmd.cost_ifBit_true tt cT cE s hb, if_pos hb]
        · rw [Cmd.cost_ifBit_false tt cT cE s hb, if_neg hb]
      obtain ⟨t', res', hres', hW', hrun', htraj', hbud'⟩ := hcomb
      rw [← heval] at hW' hrun'
      rw [← hcost] at hW' hbud'
      exact ⟨t', res', hres', hW', hrun', htraj', hbud'⟩
  | forBnd cnt bnd body ihbody =>
      -- dispatch to the residue loop combinator; the IH supplies the body contract
      -- at scratch base `k + 2` (with its own per-call tape bound `G'`, as the
      -- loop's fold-states grow). `K1 = k`/`K2 = k + 1` emptiness is `hscratch`.
      simp only [Cmd.loopDepth] at hk
      exact compileForBnd_sound_physical_residue cnt bnd k (compileCmd (k + 2) body) body
        G s res0 hbit huses.1 huses.2.1 (by omega) hscratch hres0
        (fun s' res' G' hb hlen' hscr' hr hg =>
          ihbody (k + 2) s' res' G' hb hlen'
            (Cmd.UsesBelow_mono (by omega) huses.2.2) hscr' hnc hr hg)
/-- **★ The C2 obligation, residue-tolerant physical compiler contract (Risk C2),
PROVEN from the assembly** — the `res0 = []` instance of
`Compile.run_physical_residue_gen`. Accounts for the tape never shrinking: the
exit tape is `encodeTape (c.eval s) ++ res` for some `ValidResidue` residue `res`,
head rewound to `0`. Provable for ALL ops (including deletion ops like
`clear`/`tail`) because the residue absorbs the cells vacated by left-shifting.

The budget is `physStepBudget G (c.cost s)`, the **correct, provable** shape
(exactly superadditive under `seq`). The earlier `overhead (size + cost)` form was
unprovable — too small in both degree and the register count `s.length` (Finding A);
`physStepBudget`'s tape bound `G = State.size s + s.length + c.cost s + 2` carries
`s.length` explicitly. The threading hypotheses (`Cmd.UsesBelow c k` /
`k ≤ s.length` / `Cmd.NoConsLen c`) are what the bridge supplies (see the
register-count discussion in HANDOFF.md). Its proof body is `sorry`-free; the only
remaining gaps are the leaf gadgets (the 7 stub ops in
`compileOp_sound_physical_residue` + the 2 stub loop/branch machines feeding the
residue combinators).

The decider bridge (`bitDeciderTM`) reads the answer from register `0` via
`decodeTape`, which ignores the residue (`decodeTape_encodeTape_append`), so the
residue is invisible to the decider. -/
theorem Compile_run_physical_residue (c : Cmd) (k : Nat) (s : State)
    (hbit : Compile.BitState s) (hk : k + 2 * c.loopDepth ≤ s.length)
    (huses : Cmd.UsesBelow c k)
    (hscratch : ∀ r, k ≤ r → State.get s r = [])
    (hnc : Cmd.NoConsLen c) :
    ∃ (t : Nat) (res : List Nat),
      Compile.ValidResidue res ∧
      runFlatTM t (Compile k c) (initFlatConfig (Compile k c) [Compile.encodeTape s])
          = some { state_idx := Compile.exit k c,
                   tapes := [([], 0, Compile.encodeTape (c.eval s) ++ res)] } ∧
      (∀ k', k' < t → ∀ ck,
          runFlatTM k' (Compile k c)
              (initFlatConfig (Compile k c) [Compile.encodeTape s]) = some ck →
          ck.state_idx ≠ Compile.exit k c ∧
          haltingStateReached (Compile k c) ck = false) ∧
      t ≤ Compile.physStepBudget (State.size s + s.length + c.cost s + 2) (c.cost s) := by
  obtain ⟨t, res, hres, _hW, hrun, htraj, hbud⟩ :=
    Compile.run_physical_residue_gen c k s [] (State.size s + s.length + c.cost s + 2)
      hbit hk huses hscratch hnc Compile.ValidResidue_nil (by rw [List.length_nil]; omega)
  refine ⟨t, res, hres, ?_, ?_, hbud⟩
  · rw [List.append_nil] at hrun; exact hrun
  · intro k' hk' ck hck
    exact htraj k' hk' ck (by rw [List.append_nil]; exact hck)

/-- The compiled decider machine: run `Compile k c` (scratch base `k`), then the
bit-test gadget. The gadget converts register `0`'s answer (on the tape) into a
distinct halting *state*, as `DecidesBy` requires. -/
def Compile.bitDeciderTM (c : Cmd) (k : Nat) : FlatTM :=
  composeFlatTM (Compile k c) Compile.bitTestTM (Compile.exit k c)

theorem Compile.bitDeciderTM_valid (c : Cmd) (k : Nat) : validFlatTM (Compile.bitDeciderTM c k) :=
  composeFlatTM_valid (Compile k c) Compile.bitTestTM (Compile.exit k c)
    (Compile_valid k c) Compile.bitTestTM_valid (Compile_exit_lt k c)
    (Compile_tapes k c) Compile.bitTestTM_tapes

theorem Compile.bitDeciderTM_tapes (c : Cmd) (k : Nat) : (Compile.bitDeciderTM c k).tapes = 1 := by
  show (composeFlatTM (Compile k c) Compile.bitTestTM (Compile.exit k c)).tapes = 1
  rw [composeFlatTM_tapes, Compile_tapes]

/-- The canonical single-register tape `encodeTape [r]` has length `r.length + 3`
(the leading sentinel, the shifted register, the `0` delimiter, and the trailing
`endMark`). Used to bound the `DecidesBy.encode_size` of the canonical decider
bridge. -/
theorem Compile.encodeTape_singleton_length (r : List Nat) :
    (Compile.encodeTape [r]).length = r.length + 3 := by
  simp [Compile.encodeTape, Compile.encodeRegs, Compile.shiftReg]

/-- **C6 headline.** Running `bitDeciderTM c` on `encodeTape s` halts, within
`physStepBudget G (cost s) + 3` steps (`G = size s + s.length + cost s + 2`), in
state `1 + (Compile c).states` when register `0` of `c.eval s` is `[1]` (accept)
and `2 + (Compile c).states` when it is `[0]` (reject). Combines the physical run
contract of `Compile c` (`Compile_run_physical_residue'`, the residue/`physStepBudget`
form — the unprimed `overhead` form is the wrong budget shape and is unprovable,
Finding A) with the `sorry`-free gadget run lemma, via `composeFlatTM_run`. The
`UsesBelow`/`NoConsLen`/`k ≤ s.length` hypotheses are what the primed contract
threads; consumers (`DecidesLang(')`) supply them. (The `+3` is one bridge step
plus the two gadget steps — step past the leading sentinel, then read.) -/
theorem Compile.bitDecider_run (c : Cmd) (s : State) (b : Nat) (k : Nat)
    (hbitst : Compile.BitState s) (hk : k + 2 * c.loopDepth ≤ s.length)
    (huses : Cmd.UsesBelow c k)
    (hscratch : ∀ r, k ≤ r → State.get s r = [])
    (hnc : Cmd.NoConsLen c)
    (hbit : b = 0 ∨ b = 1) (h0 : (c.eval s).get 0 = [b]) :
    ∃ cfg,
      runFlatTM (Compile.physStepBudget (State.size s + s.length + c.cost s + 2)
            (c.cost s) + 3) (Compile.bitDeciderTM c k)
          (initFlatConfig (Compile.bitDeciderTM c k) [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (Compile.bitDeciderTM c k) cfg = true ∧
      cfg.state_idx = (if b = 1 then 1 else 2) + (Compile k c).states := by
  obtain ⟨tl0, htl0⟩ := Compile.encodeTape_eq_cons_of_get_zero (c.eval s) b h0
  obtain ⟨t1, res, _hres, hrun1, htraj1, ht1⟩ :=
    Compile_run_physical_residue c k s hbitst hk huses hscratch hnc
  -- Rewrite the physical exit tape via the encoding lemma (leading sentinel).
  -- The residue trails the encoded output; the gadget reads only positions 0–1,
  -- so fold the residue into the tail `tl := tl0 ++ res`.
  rw [htl0, List.cons_append, List.cons_append] at hrun1
  set tl : List Nat := tl0 ++ res with htl
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
      = some v → v < max (Compile k c).sig Compile.bitTestTM.sig := by
    intro v hv
    have : v = Compile.endMark := by simpa [currentTapeSymbol] using hv.symm
    subst this
    rw [Compile_sig, Compile.bitTestTM_sig]
    decide
  have hstate0 : (initFlatConfig (Compile k c) [Compile.encodeTape s]).state_idx
      < (Compile k c).states := (Compile_valid k c).1
  -- Compose.
  have hcomp := composeFlatTM_run (M₁ := Compile k c) (M₂ := Compile.bitTestTM)
    (exit := Compile.exit k c) (Compile_valid k c) Compile.bitTestTM_valid
    (Compile_exit_lt k c)
    (initFlatConfig (Compile k c) [Compile.encodeTape s]) hstate0
    [] 0 (Compile.endMark :: (b + 1) :: tl) hsym hrun1 htraj1 hrun2 hhalt2
  obtain ⟨hcrun, hchalt⟩ := hcomp
  -- Pad the run up to the stated budget.
  obtain ⟨kpad, hkpad⟩ := Nat.le.dest ht1
  refine ⟨{ state_idx := dst + (Compile k c).states,
            tapes := [([], 1, Compile.endMark :: (b + 1) :: tl)] }, ?_, ?_, ?_⟩
  · show runFlatTM (Compile.physStepBudget (State.size s + s.length + c.cost s + 2)
          (c.cost s) + 3) (Compile.bitDeciderTM c k)
        (initFlatConfig (Compile.bitDeciderTM c k) [Compile.encodeTape s]) = _
    have hbudget : Compile.physStepBudget (State.size s + s.length + c.cost s + 2)
        (c.cost s) + 3 = (t1 + 1 + 2) + kpad := by omega
    rw [hbudget]
    exact runFlatTM_extend (M := Compile.bitDeciderTM c k) hcrun hchalt
  · exact hchalt
  · show dst + (Compile k c).states = (if b = 1 then 1 else 2) + (Compile k c).states
    rw [hdst]

/-- Halt bits of `bitDeciderTM` past `(Compile k c).states` are exactly the
gadget's: the composed halt vector is `replicate (Compile k c).states false ++
bitTestTM.halt`. Gives the two accept/reject states' `halting_*` obligations. -/
theorem Compile.bitDeciderTM_halt_shift (c : Cmd) (k : Nat) (i : Nat) :
    (Compile.bitDeciderTM c k).halt.getD (i + (Compile k c).states) false
      = Compile.bitTestTM.halt.getD i false := by
  show (composedHalt (Compile k c) Compile.bitTestTM).getD (i + (Compile k c).states) false
      = Compile.bitTestTM.halt.getD i false
  rw [composedHalt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [List.length_replicate]; exact Nat.le_add_left _ _),
      List.length_replicate, Nat.add_sub_cancel]

/-! ## ★★ The WALL resolution — runtime register-width padding (2026-06-07)

`Compile_run_physical_residue` honestly requires `k ≤ s.length` (its per-op gadgets
assume the registers they touch already exist on the tape — `Op.inBounds`). But the
decider's *input* tape is narrow (`encodeState x = [enc x]`, width 1) while the
program touches `regBound > 1` registers, and the framework's tight
`DecidesBy.encode_size` (`2·size+4`) forbids pre-padding the *input* encoding.

**Resolution:** pad the tape *at runtime*. `padRegsTM k` grows a narrow tape
`encodeTape s` into `encodeTape (s ++ replicate k [])` (width `≥ k`) — the extra
registers are empty, so `c.eval` is unchanged register-wise (`Cmd.eval_agree`), and
the *input* encoding stays tight (`encode_size` unaffected). Prepended before the
decider, it discharges `k ≤ s'.length` for the whole run. This keeps
`Compile_run_physical_residue` and `bitDecider_run` exactly as they are.

⚠ **`padRegsTM` and its run/trajectory are the single pinned BOTTOM-UP gadget
obligation** replacing the *false* `DecidesLang'.reg_width`. A real construction:
`k`-fold `(stepRightTM ⨾ scanRightUntilTM 4 endMark ⨾ insertCarryTM 0 ⨾
rewindFromEndTM 4 endMark)` — each iteration inserts one `0` delimiter just before
the trailing `endMark`. Its validity/tapes/sig/exit are construction-shape facts;
only the behavioural `run`/`traj` are nontrivial. `Compile.paddedBitDecider_run`
below is PROVEN from this interface, validating the composition design end-to-end. -/

/-! ### Padding bookkeeping (sorry-free) -/

/-- Reading any register of `s ++ replicate k []` is reading it of `s` (the
appended blocks are empty, so out-of-range reads still return `[]`). -/
theorem Compile.get_append_replicate_nil (s : State) (k r : Nat) :
    (s ++ List.replicate k []).get r = s.get r := by
  unfold State.get
  by_cases hr : r < s.length
  · rw [List.getElem?_append_left hr]
  · have hr' : s.length ≤ r := Nat.le_of_not_lt hr
    rw [List.getElem?_append_right hr', List.getElem?_eq_none hr']
    rcases Nat.lt_or_ge (r - s.length) k with hr2 | hr2
    · simp [List.getElem?_replicate, hr2]
    · rw [List.getElem?_eq_none (by rw [List.length_replicate]; exact hr2)]

/-- Reading at or past the register count returns `[]` (`State.get` is
`getElem?`-based). With `get_append_replicate_nil` this discharges the
scratch-emptiness hypothesis for the runtime-padded states: every register
`≥ s.length` of `s ++ replicate m []` is `[]`. -/
theorem Compile.get_of_length_le (s : State) (r : Nat) (hr : s.length ≤ r) :
    State.get s r = [] := by
  unfold State.get
  rw [List.getElem?_eq_none hr]
  rfl

/-- Appending empty registers preserves `BitState`. -/
theorem Compile.BitState_append_replicate_nil (s : State) (k : Nat)
    (h : Compile.BitState s) : Compile.BitState (s ++ List.replicate k []) := by
  intro reg hreg x hx
  rcases List.mem_append.mp hreg with hs | hp
  · exact h reg hs x hx
  · obtain ⟨-, rfl⟩ := List.mem_replicate.mp hp; cases hx

/-- The aggregate size is unchanged by appending empty registers. -/
theorem Compile.size_append_replicate_nil (s : State) (k : Nat) :
    State.size (s ++ List.replicate k []) = State.size s := by
  have hz : ∀ m, (List.replicate m (0 : Nat)).foldr (· + ·) 0 = 0 := by
    intro m; induction m with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  unfold State.size
  rw [List.map_append, List.foldr_append, List.map_replicate, List.length_nil, hz]

/-- `s` and its empty-register padding agree on every register `< k`. -/
theorem Compile.agreeBelow_append_replicate_nil (s : State) (k : Nat) :
    AgreeBelow k s (s ++ List.replicate k []) :=
  fun r _ => (Compile.get_append_replicate_nil s k r).symm

/-! #### Foundational helpers for the WALL gadget proofs -/

/-- A trivial immediately-halting machine (the `k = 0` base of `padRegsTM`): one
state which is a halt state, `sig = 4`, single tape. `runFlatTM n` is the identity. -/
def Compile.haltTM : FlatTM where
  sig := 4; tapes := 1; states := 1; trans := []; start := 0; halt := [true]

theorem Compile.haltTM_valid : validFlatTM Compile.haltTM :=
  ⟨by decide, by decide, by intro e he; cases he⟩

theorem Compile.haltTM_halt {cfg : FlatTMConfig} (h : cfg.state_idx = 0) :
    haltingStateReached Compile.haltTM cfg = true := by
  show Compile.haltTM.halt.getD cfg.state_idx false = true; rw [h]; rfl

theorem Compile.haltTM_run (n : Nat) {cfg : FlatTMConfig} (h : cfg.state_idx = 0) :
    runFlatTM n Compile.haltTM cfg = some cfg := by
  cases n with
  | zero => rfl
  | succ m =>
      show (if haltingStateReached Compile.haltTM cfg then some cfg else _) = some cfg
      rw [if_pos (Compile.haltTM_halt h)]

/-- `encodeRegs` of `s` with one extra empty register appended is `encodeRegs s ++ [0]`
(the empty register contributes its lone `0` delimiter). -/
theorem Compile.encodeRegs_snoc_nil (s : State) :
    Compile.encodeRegs (s ++ [[]]) = Compile.encodeRegs s ++ [0] := by
  induction s with
  | nil => rfl
  | cons r s' ih =>
      rw [List.cons_append, Compile.encodeRegs_cons, Compile.encodeRegs_cons, ih]
      simp [List.append_assoc]

/-- One non-halting step unfolds `runFlatTM (n+1)`. -/
private theorem Compile.run_succ (M : FlatTM) (cfg c' : FlatTMConfig) (n : Nat)
    (hnh : haltingStateReached M cfg = false) (hstep : stepFlatTM M cfg = some c') :
    runFlatTM (n + 1) M cfg = runFlatTM n M c' := by
  show (if haltingStateReached M cfg then some cfg
        else match stepFlatTM M cfg with | none => some cfg | some c'' => runFlatTM n M c'') = _
  rw [if_neg (by rw [hnh]; decide), hstep]

/-- A cell read off a `< 4` tape (head track empty) is `< 4`. -/
private theorem Compile.curSym_lt {tp : List Nat} (hb : ∀ x ∈ tp, x < 4) (head : Nat) :
    ∀ v, currentTapeSymbol (([] : List Nat), head, tp) = some v → v < 4 := by
  intro v hv
  unfold currentTapeSymbol at hv
  by_cases h : head < tp.length
  · rw [dif_pos h] at hv; injection hv with hv'; subst hv'; exact hb _ (List.get_mem _ _)
  · rw [dif_neg h] at hv; exact absurd hv (by simp)

/-- **Scan-right partial trajectory.** From `{0, head}` on a tape whose cells
`head … head+gap-1` are in range and `≠ target`, after `j ≤ gap` steps
`scanRightUntilTM` is in state `0` with head at `head + j`. (The `j ≤ gap` prefix of
`scanRightUntilTM_run_found`; gives the missing `no_early_halt`.) -/
private theorem Compile.scanRight_partial
    (sig target : Nat) (left right : List Nat) (head gap : Nat)
    (hcells : ∀ k, k < gap → ∃ (h : head + k < right.length),
        right.get ⟨head + k, h⟩ < sig ∧ right.get ⟨head + k, h⟩ ≠ target) :
    ∀ j, j ≤ gap → runFlatTM j (scanRightUntilTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 0, tapes := [(left, head + j, right)] } := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      obtain ⟨hlt, hsymlt, hne⟩ := hcells j (by omega)
      have hstep := scanRightUntilTM_step_advance sig target left right (head + j) hlt hsymlt hne
      rw [runFlatTM_compose (scanRightUntilTM sig target) j 1 _ _ (ih (by omega)),
          Compile.run_succ (scanRightUntilTM sig target) _ _ 0 (by rfl) hstep]
      rfl

/-! #### The padding body `padBody` and its run/trajectory -/

/-- Insert-then-rewind: from the trailing terminator, insert one `0` before it and
rewind to the leading sentinel. -/
def Compile.padInner34 : FlatTM :=
  composeFlatTM (ShiftTape.insertCarryTM 0) (ScanLeft.rewindFromEndTM 4 3) 5

/-- Scan-right then `padInner34`. -/
def Compile.padInner234 : FlatTM :=
  composeFlatTM (scanRightUntilTM 4 3) Compile.padInner34 1

/-- **One padding-body iteration (the reusable core, REAL).** From head `0` on
`encodeTape s`: step right off the sentinel, scan right to the trailing terminator,
insert one `0` before it, rewind to the leading sentinel. Maps `encodeTape s` →
`encodeTape (s ++ [[]])`, head back to `0`, halting at state `padBodyExit = 14` in
exactly `2·|encodeTape s| + 7` steps (probe-validated). -/
def Compile.padBody : FlatTM :=
  composeFlatTM (ScanLeft.stepRightTM 4) Compile.padInner234 1

/-- `padBody`'s final halt state. -/
def Compile.padBodyExit : Nat := 14

theorem Compile.padBody_states : Compile.padBody.states = 16 := rfl
theorem Compile.padBody_tapes : Compile.padBody.tapes = 1 := rfl
theorem Compile.padBody_start : Compile.padBody.start = 0 := rfl

theorem Compile.padInner34_valid : validFlatTM Compile.padInner34 :=
  composeFlatTM_valid _ _ 5 (ShiftTape.insertCarryTM_valid 0 (by decide))
    (ScanLeft.rewindFromEndTM_valid 4 3 (by decide)) (by decide) rfl rfl

theorem Compile.padInner234_valid : validFlatTM Compile.padInner234 :=
  composeFlatTM_valid _ _ 1 (scanRightUntilTM_valid 4 3 (by decide))
    Compile.padInner34_valid (by decide) rfl rfl

theorem Compile.padBody_valid : validFlatTM Compile.padBody :=
  composeFlatTM_valid _ _ 1 (ScanLeft.stepRightTM_valid 4)
    Compile.padInner234_valid (by decide) rfl rfl

theorem Compile.padBody_halt {cfg : FlatTMConfig} (h : cfg.state_idx = 14) :
    haltingStateReached Compile.padBody cfg = true := by
  show Compile.padBody.halt.getD cfg.state_idx false = true; rw [h]; rfl

/-- The post-insert tape equals `encodeTape (s ++ [[]])`. -/
private theorem Compile.padBody_tape_eq (s : State) :
    ((3 :: Compile.encodeRegs s) ++ (0 : Nat) :: [3]) = Compile.encodeTape (s ++ [[]]) := by
  rw [Compile.encodeTape, Compile.encodeRegs_snoc_nil]
  show (3 :: Compile.encodeRegs s) ++ 0 :: [3]
      = Compile.endMark :: (Compile.encodeRegs s ++ [0] ++ [Compile.endMark])
  simp [Compile.endMark, List.append_assoc]

/-- `encodeTape s = (3 :: encodeRegs s) ++ [3]`. -/
private theorem Compile.encodeTape_cons_form (s : State) :
    Compile.encodeTape s = (3 :: Compile.encodeRegs s) ++ [3] := rfl

theorem Compile.padInner34_run (s : State) (hbit : Compile.BitState s) :
    runFlatTM ((Compile.encodeRegs s).length + 7) Compile.padInner34
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] }
      = some { state_idx := 9, tapes := [([], 0, Compile.encodeTape (s ++ [[]]))] } := by
  have hbit' : Compile.BitState (s ++ [[]]) := by
    have := Compile.BitState_append_replicate_nil s 1 hbit
    rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
  have hL : 1 + (Compile.encodeRegs s).length = (3 :: Compile.encodeRegs s).length := by simp [Nat.add_comm]
  have htape_s : Compile.encodeTape s = (3 :: Compile.encodeRegs s) ++ [3] := Compile.encodeTape_cons_form s
  have htape_s' : (3 :: Compile.encodeRegs s) ++ (0 : Nat) :: [3] = Compile.encodeTape (s ++ [[]]) :=
    Compile.padBody_tape_eq s
  have htplen : (Compile.encodeTape (s ++ [[]])).length = (Compile.encodeRegs s).length + 3 := by
    rw [Compile.encodeTape_length]
    have hsz : State.size (s ++ [[]]) = State.size s := by
      have := Compile.size_append_replicate_nil s 1
      rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
    have hwlen : (s ++ [[]]).length = s.length + 1 := by simp
    rw [hsz, hwlen, Compile.encodeRegs_length]; omega
  -- M₁ = insertCarryTM 0 : insert a `0` before the trailing terminator.
  have hins : runFlatTM 2 (ShiftTape.insertCarryTM 0)
        { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] }
      = some { state_idx := 5,
               tapes := [([], (Compile.encodeRegs s).length + 2, Compile.encodeTape (s ++ [[]]))] } := by
    have h := ShiftTape.insertCarryTM_run 0 [3] (3 :: Compile.encodeRegs s)
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; decide)
    rw [← hL, ← htape_s, htape_s'] at h
    rw [show (1 + (Compile.encodeRegs s).length + ([3] : List Nat).length)
          = (Compile.encodeRegs s).length + 2 by simp; omega] at h
    exact h
  -- M₂ = rewindFromEndTM 4 3 : rewind from the trailing terminator to the leading sentinel.
  have hrew : runFlatTM ((Compile.encodeRegs s).length + 4) (ScanLeft.rewindFromEndTM 4 3)
        { state_idx := 0, tapes := [([], (Compile.encodeRegs s).length + 2, Compile.encodeTape (s ++ [[]]))] }
      = some { state_idx := 3, tapes := [([], 0, Compile.encodeTape (s ++ [[]]))] } := by
    have h := ScanLeft.rewindFromEndTM_run 4 3 (by decide) [] (Compile.encodeTape (s ++ [[]]))
      ((Compile.encodeRegs s).length + 2) (by omega)
      (Compile.encodeTape_get_zero (s ++ [[]]) (by omega))
      (by omega) (by omega)
      (Compile.encodeTape_lt_four (s ++ [[]]) hbit' _ (List.get_mem _ _))
      (by
        intro i hi_pos hi_lt
        obtain ⟨hii, hne⟩ := Compile.encodeTape_interior_ne_endMark (s ++ [[]]) hbit' i hi_pos (by omega)
        exact ⟨hii, Compile.encodeTape_lt_four (s ++ [[]]) hbit' _ (List.get_mem _ _), hne⟩)
    rw [show (1 : Nat) + 1 + ((Compile.encodeRegs s).length + 2) = (Compile.encodeRegs s).length + 4 by omega] at h
    exact h
  -- sym bound at the bridge (head on the post-insert tape).
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), (Compile.encodeRegs s).length + 2,
        Compile.encodeTape (s ++ [[]])) = some v
      → v < max (ShiftTape.insertCarryTM 0).sig (ScanLeft.rewindFromEndTM 4 3).sig := by
    intro v hv
    rw [show max (ShiftTape.insertCarryTM 0).sig (ScanLeft.rewindFromEndTM 4 3).sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four (s ++ [[]]) hbit') _ v hv
  have hcomp := composeFlatTM_run (M₁ := ShiftTape.insertCarryTM 0)
    (M₂ := ScanLeft.rewindFromEndTM 4 3) (exit := 5)
    (ShiftTape.insertCarryTM_valid 0 (by decide)) (ScanLeft.rewindFromEndTM_valid 4 3 (by decide))
    (by decide)
    { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] }
    (by show (0 : Nat) < (ShiftTape.insertCarryTM 0).states; decide)
    [] ((Compile.encodeRegs s).length + 2) (Compile.encodeTape (s ++ [[]])) hsym
    hins
    (by
      intro k hk ck hck
      have hnh : haltingStateReached (ShiftTape.insertCarryTM 0) ck = false := by
        have := ShiftTape.insertCarryTM_no_early_halt 0 [3] (3 :: Compile.encodeRegs s)
          (by intro x hx; rcases List.mem_singleton.mp hx with rfl; decide) k (by simpa using hk) ck
        rw [← hL, ← htape_s] at this
        exact this hck
      refine ⟨fun h => ?_, hnh⟩
      have hb : haltingStateReached (ShiftTape.insertCarryTM 0) ck = true := by
        show (ShiftTape.insertCarryTM 0).halt.getD ck.state_idx false = true
        rw [h]; decide
      rw [hb] at hnh; exact absurd hnh (by decide))
    hrew (by show (ScanLeft.rewindFromEndTM 4 3).halt.getD 3 false = true; decide)
  obtain ⟨hrun, _⟩ := hcomp
  rw [show (Compile.encodeRegs s).length + 7 = 2 + 1 + ((Compile.encodeRegs s).length + 4) by omega]
  exact hrun

theorem Compile.padInner234_run (s : State) (hbit : Compile.BitState s) :
    runFlatTM (2 * (Compile.encodeRegs s).length + 9) Compile.padInner234
        { state_idx := 0, tapes := [([], 1, Compile.encodeTape s)] }
      = some { state_idx := 12, tapes := [([], 0, Compile.encodeTape (s ++ [[]]))] } := by
  have hlen : (Compile.encodeTape s).length = (Compile.encodeRegs s).length + 2 := by
    rw [Compile.encodeTape_length, Compile.encodeRegs_length]
  -- scanRightUntilTM run: from head 1, scan to the trailing terminator at index 1 + |R|.
  have hscan := scanRightUntilTM_run_found 4 3 [] (Compile.encodeTape s)
    (Compile.encodeRegs s).length 1 (by rw [hlen]; omega)
    (by
      have key : (Compile.encodeTape s)[1 + (Compile.encodeRegs s).length]? = some 3 := by
        rw [Compile.encodeTape,
            show 1 + (Compile.encodeRegs s).length = (Compile.encodeRegs s).length + 1 by omega,
            List.getElem?_cons_succ,
            List.getElem?_append_right (Nat.le_refl _)]
        simp [Compile.endMark]
      rw [List.get_eq_getElem]
      have hg := List.getElem?_eq_getElem
        (show 1 + (Compile.encodeRegs s).length < (Compile.encodeTape s).length by rw [hlen]; omega)
      rw [key] at hg
      exact (Option.some.inj hg).symm)
    (by
      intro k hk
      obtain ⟨hi, hne⟩ := Compile.encodeTape_interior_ne_endMark s hbit (1 + k) (by omega) (by rw [hlen]; omega)
      exact ⟨hi, Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _), hne⟩)
  -- sym bound at the bridge.
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 1 + (Compile.encodeRegs s).length,
        Compile.encodeTape s) = some v
      → v < max (scanRightUntilTM 4 3).sig Compile.padInner34.sig := by
    intro v hv
    rw [show max (scanRightUntilTM 4 3).sig Compile.padInner34.sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four s hbit) _ v hv
  have hcomp := composeFlatTM_run (M₁ := scanRightUntilTM 4 3) (M₂ := Compile.padInner34) (exit := 1)
    (scanRightUntilTM_valid 4 3 (by decide)) Compile.padInner34_valid (by decide)
    { state_idx := 0, tapes := [([], 1, Compile.encodeTape s)] }
    (by show (0 : Nat) < (scanRightUntilTM 4 3).states; decide)
    [] (1 + (Compile.encodeRegs s).length) (Compile.encodeTape s) hsym
    hscan
    (by
      intro k hk ck hck
      have hpart := Compile.scanRight_partial 4 3 [] (Compile.encodeTape s) 1 (Compile.encodeRegs s).length
        (by
          intro m hm
          obtain ⟨hi, hne⟩ := Compile.encodeTape_interior_ne_endMark s hbit (1 + m) (by omega) (by rw [hlen]; omega)
          exact ⟨hi, Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _), hne⟩)
        k (by omega)
      rw [hpart] at hck
      obtain rfl := Option.some.inj hck
      exact ⟨Nat.zero_ne_one, rfl⟩)
    (Compile.padInner34_run s hbit)
    (by show Compile.padInner34.halt.getD 9 false = true; decide)
  obtain ⟨hrun, _⟩ := hcomp
  rw [show 2 * (Compile.encodeRegs s).length + 9
        = ((Compile.encodeRegs s).length + 1) + 1 + ((Compile.encodeRegs s).length + 7) by omega]
  exact hrun

theorem Compile.padBody_run (s : State) (hbit : Compile.BitState s) :
    runFlatTM (2 * (Compile.encodeTape s).length + 7) Compile.padBody
        (initFlatConfig Compile.padBody [Compile.encodeTape s])
      = some { state_idx := Compile.padBodyExit,
               tapes := [([], 0, Compile.encodeTape (s ++ [[]]))] } := by
  have hlen : (Compile.encodeTape s).length = (Compile.encodeRegs s).length + 2 := by
    rw [Compile.encodeTape_length, Compile.encodeRegs_length]
  have hinit : initFlatConfig Compile.padBody [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := rfl
  rw [hinit]
  -- stepRightTM run: head 0 → 1 (off the leading sentinel).
  have hstep := ScanLeft.stepRightTM_run 4 [] (Compile.encodeTape s) 0 (by rw [hlen]; omega)
    (by rw [Compile.encodeTape_get_zero s (by rw [hlen]; omega)]; decide)
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 1, Compile.encodeTape s) = some v
      → v < max (ScanLeft.stepRightTM 4).sig Compile.padInner234.sig := by
    intro v hv
    rw [show max (ScanLeft.stepRightTM 4).sig Compile.padInner234.sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four s hbit) _ v hv
  have hcomp := composeFlatTM_run (M₁ := ScanLeft.stepRightTM 4) (M₂ := Compile.padInner234) (exit := 1)
    (ScanLeft.stepRightTM_valid 4) Compile.padInner234_valid (by decide)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] }
    (by show (0 : Nat) < (ScanLeft.stepRightTM 4).states; decide)
    [] 1 (Compile.encodeTape s) hsym
    hstep
    (fun k hk ck hck => ScanLeft.stepRightTM_no_early_halt 4 [] (Compile.encodeTape s) 0 k hk ck hck)
    (Compile.padInner234_run s hbit)
    (by show Compile.padInner234.halt.getD 12 false = true; decide)
  obtain ⟨hrun, _⟩ := hcomp
  rw [show 2 * (Compile.encodeTape s).length + 7
        = 1 + 1 + (2 * (Compile.encodeRegs s).length + 9) by omega]
  exact hrun

/-! #### The trajectory tower (no-early-halt), mirroring the run tower. -/

theorem Compile.padInner34_no_early_halt (s : State) (hbit : Compile.BitState s) :
    ∀ j, j < (Compile.encodeRegs s).length + 7 → ∀ ck,
      runFlatTM j Compile.padInner34
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] } = some ck →
      haltingStateReached Compile.padInner34 ck = false := by
  have hbit' : Compile.BitState (s ++ [[]]) := by
    have := Compile.BitState_append_replicate_nil s 1 hbit
    rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
  have hL : 1 + (Compile.encodeRegs s).length = (3 :: Compile.encodeRegs s).length := by
    simp [Nat.add_comm]
  have htape_s : Compile.encodeTape s = (3 :: Compile.encodeRegs s) ++ [3] := Compile.encodeTape_cons_form s
  have htplen : (Compile.encodeTape (s ++ [[]])).length = (Compile.encodeRegs s).length + 3 := by
    rw [Compile.encodeTape_length]
    have hsz : State.size (s ++ [[]]) = State.size s := by
      have := Compile.size_append_replicate_nil s 1
      rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
    have hwlen : (s ++ [[]]).length = s.length + 1 := by simp
    rw [hsz, hwlen, Compile.encodeRegs_length]; omega
  have hins : runFlatTM 2 (ShiftTape.insertCarryTM 0)
        { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] }
      = some { state_idx := 5,
               tapes := [([], (Compile.encodeRegs s).length + 2, Compile.encodeTape (s ++ [[]]))] } := by
    have h := ShiftTape.insertCarryTM_run 0 [3] (3 :: Compile.encodeRegs s)
      (by intro x hx; rcases List.mem_singleton.mp hx with rfl; decide)
    rw [← hL, ← htape_s, Compile.padBody_tape_eq s] at h
    rw [show (1 + (Compile.encodeRegs s).length + ([3] : List Nat).length)
          = (Compile.encodeRegs s).length + 2 by simp; omega] at h
    exact h
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), (Compile.encodeRegs s).length + 2,
        Compile.encodeTape (s ++ [[]])) = some v
      → v < max (ShiftTape.insertCarryTM 0).sig (ScanLeft.rewindFromEndTM 4 3).sig := by
    intro v hv
    rw [show max (ShiftTape.insertCarryTM 0).sig (ScanLeft.rewindFromEndTM 4 3).sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four (s ++ [[]]) hbit') _ v hv
  intro j hj ck hck
  refine composeFlatTM_no_early_halt (M₁ := ShiftTape.insertCarryTM 0)
    (M₂ := ScanLeft.rewindFromEndTM 4 3) (exit := 5)
    (t₂ := (Compile.encodeRegs s).length + 4)
    (ShiftTape.insertCarryTM_valid 0 (by decide)) (ScanLeft.rewindFromEndTM_valid 4 3 (by decide))
    (by decide)
    { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs s).length, Compile.encodeTape s)] }
    (by show (0 : Nat) < (ShiftTape.insertCarryTM 0).states; decide)
    [] ((Compile.encodeRegs s).length + 2) (Compile.encodeTape (s ++ [[]])) hsym
    hins
    (by
      intro k hk ck' hck'
      have hnh : haltingStateReached (ShiftTape.insertCarryTM 0) ck' = false := by
        have := ShiftTape.insertCarryTM_no_early_halt 0 [3] (3 :: Compile.encodeRegs s)
          (by intro x hx; rcases List.mem_singleton.mp hx with rfl; decide) k (by simpa using hk) ck'
        rw [← hL, ← htape_s] at this
        exact this hck'
      refine ⟨fun h => ?_, hnh⟩
      have hb : haltingStateReached (ShiftTape.insertCarryTM 0) ck' = true := by
        show (ShiftTape.insertCarryTM 0).halt.getD ck'.state_idx false = true
        rw [h]; decide
      rw [hb] at hnh; exact absurd hnh (by decide))
    (by
      have htraj := ScanLeft.rewindFromEndTM_no_early_halt 4 3 (by decide) []
        (Compile.encodeTape (s ++ [[]])) ((Compile.encodeRegs s).length + 2) (by omega)
        (Compile.encodeTape_get_zero (s ++ [[]]) (by omega)) (by omega) (by omega)
        (Compile.encodeTape_lt_four (s ++ [[]]) hbit' _ (List.get_mem _ _))
        (by
          intro i hi_pos hi_lt
          obtain ⟨hii, hne⟩ := Compile.encodeTape_interior_ne_endMark (s ++ [[]]) hbit' i hi_pos (by omega)
          exact ⟨hii, Compile.encodeTape_lt_four (s ++ [[]]) hbit' _ (List.get_mem _ _), hne⟩)
      intro k hk ck' hck'
      exact htraj k (by omega) ck' hck')
    j (by omega) ck hck

theorem Compile.padInner234_no_early_halt (s : State) (hbit : Compile.BitState s) :
    ∀ j, j < 2 * (Compile.encodeRegs s).length + 9 → ∀ ck,
      runFlatTM j Compile.padInner234
          { state_idx := 0, tapes := [([], 1, Compile.encodeTape s)] } = some ck →
      haltingStateReached Compile.padInner234 ck = false := by
  have hlen : (Compile.encodeTape s).length = (Compile.encodeRegs s).length + 2 := by
    rw [Compile.encodeTape_length, Compile.encodeRegs_length]
  have hscan := scanRightUntilTM_run_found 4 3 [] (Compile.encodeTape s)
    (Compile.encodeRegs s).length 1 (by rw [hlen]; omega)
    (by
      have key : (Compile.encodeTape s)[1 + (Compile.encodeRegs s).length]? = some 3 := by
        rw [Compile.encodeTape,
            show 1 + (Compile.encodeRegs s).length = (Compile.encodeRegs s).length + 1 by omega,
            List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _)]
        simp [Compile.endMark]
      rw [List.get_eq_getElem]
      have hg := List.getElem?_eq_getElem
        (show 1 + (Compile.encodeRegs s).length < (Compile.encodeTape s).length by rw [hlen]; omega)
      rw [key] at hg
      exact (Option.some.inj hg).symm)
    (by
      intro k hk
      obtain ⟨hi, hne⟩ := Compile.encodeTape_interior_ne_endMark s hbit (1 + k) (by omega) (by rw [hlen]; omega)
      exact ⟨hi, Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _), hne⟩)
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 1 + (Compile.encodeRegs s).length,
        Compile.encodeTape s) = some v
      → v < max (scanRightUntilTM 4 3).sig Compile.padInner34.sig := by
    intro v hv
    rw [show max (scanRightUntilTM 4 3).sig Compile.padInner34.sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four s hbit) _ v hv
  intro j hj ck hck
  refine composeFlatTM_no_early_halt (M₁ := scanRightUntilTM 4 3) (M₂ := Compile.padInner34) (exit := 1)
    (t₂ := (Compile.encodeRegs s).length + 7)
    (scanRightUntilTM_valid 4 3 (by decide)) Compile.padInner34_valid (by decide)
    { state_idx := 0, tapes := [([], 1, Compile.encodeTape s)] }
    (by show (0 : Nat) < (scanRightUntilTM 4 3).states; decide)
    [] (1 + (Compile.encodeRegs s).length) (Compile.encodeTape s) hsym
    hscan
    (by
      intro k hk ck' hck'
      have hpart := Compile.scanRight_partial 4 3 [] (Compile.encodeTape s) 1 (Compile.encodeRegs s).length
        (by
          intro m hm
          obtain ⟨hi, hne⟩ := Compile.encodeTape_interior_ne_endMark s hbit (1 + m) (by omega) (by rw [hlen]; omega)
          exact ⟨hi, Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _), hne⟩)
        k (by omega)
      rw [hpart] at hck'
      obtain rfl := Option.some.inj hck'
      exact ⟨Nat.zero_ne_one, rfl⟩)
    (fun k hk ck' hck' => Compile.padInner34_no_early_halt s hbit k (by omega) ck' hck')
    j (by omega) ck hck

theorem Compile.padBody_no_early_halt (s : State) (hbit : Compile.BitState s) :
    ∀ j, j < 2 * (Compile.encodeTape s).length + 7 → ∀ ck,
      runFlatTM j Compile.padBody (initFlatConfig Compile.padBody [Compile.encodeTape s]) = some ck →
      haltingStateReached Compile.padBody ck = false := by
  have hlen : (Compile.encodeTape s).length = (Compile.encodeRegs s).length + 2 := by
    rw [Compile.encodeTape_length, Compile.encodeRegs_length]
  have hinit : initFlatConfig Compile.padBody [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := rfl
  rw [hinit]
  have hstep := ScanLeft.stepRightTM_run 4 [] (Compile.encodeTape s) 0 (by rw [hlen]; omega)
    (by rw [Compile.encodeTape_get_zero s (by rw [hlen]; omega)]; decide)
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 1, Compile.encodeTape s) = some v
      → v < max (ScanLeft.stepRightTM 4).sig Compile.padInner234.sig := by
    intro v hv
    rw [show max (ScanLeft.stepRightTM 4).sig Compile.padInner234.sig = 4 from by decide]
    exact Compile.curSym_lt (Compile.encodeTape_lt_four s hbit) _ v hv
  intro j hj ck hck
  refine composeFlatTM_no_early_halt (M₁ := ScanLeft.stepRightTM 4) (M₂ := Compile.padInner234) (exit := 1)
    (t₂ := 2 * (Compile.encodeRegs s).length + 9)
    (ScanLeft.stepRightTM_valid 4) Compile.padInner234_valid (by decide)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] }
    (by show (0 : Nat) < (ScanLeft.stepRightTM 4).states; decide)
    [] 1 (Compile.encodeTape s) hsym
    hstep
    (fun k hk ck' hck' => ScanLeft.stepRightTM_no_early_halt 4 [] (Compile.encodeTape s) 0 k hk ck' hck')
    (fun k hk ck' hck' => Compile.padInner234_no_early_halt s hbit k (by omega) ck' hck')
    j (by omega) ck hck

/-- **Empty-register padding machine (REAL — the WALL gadget).** `padRegsTM k` is
the `k`-fold static composition of `padBody` (recursion on `k`), base `haltTM`
(the `k = 0` no-op). Grows `encodeTape s` into `encodeTape (s ++ replicate k [])`. -/
def Compile.padRegsTM : Nat → FlatTM
  | 0     => Compile.haltTM
  | k + 1 => composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit

/-- The padding machine's halt/exit state: `0` (base) shifted up by
`padBody.states = 16` per iteration, i.e. `16·k`. -/
def Compile.padRegsExit : Nat → Nat
  | 0     => 0
  | k + 1 => Compile.padRegsExit k + 16

theorem Compile.padRegsTM_tapes (k : Nat) : (Compile.padRegsTM k).tapes = 1 := by
  cases k with
  | zero => rfl
  | succ k =>
      show (composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit).tapes = 1
      rw [composeFlatTM_tapes, Compile.padBody_tapes]

theorem Compile.padRegsTM_sig (k : Nat) : (Compile.padRegsTM k).sig = 4 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit).sig = 4
      rw [composeFlatTM_sig, ih]; rfl

theorem Compile.padRegsTM_states (k : Nat) :
    (Compile.padRegsTM k).states = 1 + 16 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit).states
          = 1 + 16 * (k + 1)
      rw [composeFlatTM_states, Compile.padBody_states, ih]; ring

theorem Compile.padRegsTM_valid (k : Nat) : validFlatTM (Compile.padRegsTM k) := by
  induction k with
  | zero => exact Compile.haltTM_valid
  | succ k ih =>
      exact composeFlatTM_valid Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit
        Compile.padBody_valid ih (by rw [Compile.padBody_states]; decide)
        Compile.padBody_tapes (Compile.padRegsTM_tapes k)

theorem Compile.padRegsExit_lt (k : Nat) :
    Compile.padRegsExit k < (Compile.padRegsTM k).states := by
  induction k with
  | zero => show (0 : Nat) < Compile.haltTM.states; decide
  | succ k ih =>
      show Compile.padRegsExit k + 16
          < (composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit).states
      rw [composeFlatTM_states, Compile.padBody_states]; omega

/-- `padRegsExit k` is a halt index of `padRegsTM k`. -/
theorem Compile.padRegsTM_halt_idx (k : Nat) :
    (Compile.padRegsTM k).halt.getD (Compile.padRegsExit k) false = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (composeFlatTM Compile.padBody (Compile.padRegsTM k) Compile.padBodyExit).halt.getD
          (Compile.padRegsExit k + 16) false = true
      show (composedHalt Compile.padBody (Compile.padRegsTM k)).getD
          (Compile.padRegsExit k + 16) false = true
      rw [composedHalt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [List.length_replicate, Compile.padBody_states]; omega),
          List.length_replicate, Compile.padBody_states,
          show Compile.padRegsExit k + 16 - 16 = Compile.padRegsExit k by omega,
          ← List.getD_eq_getElem?_getD]
      exact ih

/-- `padRegsExit k` is a halt state of `padRegsTM k` (for any tape). -/
theorem Compile.padRegsTM_halt (k : Nat) {cfg : FlatTMConfig}
    (h : cfg.state_idx = Compile.padRegsExit k) :
    haltingStateReached (Compile.padRegsTM k) cfg = true := by
  show (Compile.padRegsTM k).halt.getD cfg.state_idx false = true
  rw [h]; exact Compile.padRegsTM_halt_idx k

/-- Step budget for `padRegsTM k` on `encodeTape s` — the **exact** step count
(recursion mirrors the machine). Each body is `2·|tape|+7` steps + 1 bridge; the
base is `0`. `padRegsTM_run`/`_traj` need the *exact* count (the trajectory must not
yet be at the exit), and `padBudget_le` bounds it by a clean polynomial for the
framework bridges. -/
def Compile.padBudget : Nat → State → Nat
  | 0, _     => 0
  | k + 1, s => (2 * (Compile.encodeTape s).length + 7) + 1 + Compile.padBudget k (s ++ [[]])

/-- `padBudget` is bounded by a clean polynomial in tape width and `k`. -/
theorem Compile.padBudget_le (k : Nat) (s : State) :
    Compile.padBudget k s ≤ k * (2 * State.size s + 2 * s.length + 2 * k + 12) := by
  induction k generalizing s with
  | zero => simp [Compile.padBudget]
  | succ k ih =>
      have hsize : State.size (s ++ [[]]) = State.size s := by
        have := Compile.size_append_replicate_nil s 1
        rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
      have hlen : (s ++ [[]]).length = s.length + 1 := by simp
      have hbody : (Compile.encodeTape s).length = State.size s + s.length + 2 :=
        Compile.encodeTape_length s
      have ihs := ih (s ++ [[]])
      rw [hsize, hlen] at ihs
      show (2 * (Compile.encodeTape s).length + 7) + 1 + Compile.padBudget k (s ++ [[]])
          ≤ (k + 1) * (2 * State.size s + 2 * s.length + 2 * (k + 1) + 12)
      rw [hbody]
      calc (2 * (State.size s + s.length + 2) + 7) + 1 + Compile.padBudget k (s ++ [[]])
          ≤ (2 * (State.size s + s.length + 2) + 7) + 1
              + k * (2 * State.size s + 2 * (s.length + 1) + 2 * k + 12) := by
            exact Nat.add_le_add_left ihs _
        _ ≤ (k + 1) * (2 * State.size s + 2 * s.length + 2 * (k + 1) + 12) := by ring_nf; omega

/-- **`padRegsTM` run.** From the narrow tape `encodeTape s`, reach the exit
`padRegsExit k` with tape `encodeTape (s ++ replicate k [])`, head rewound to `0`,
in exactly `padBudget k s` steps. Induction on `k` via `composeFlatTM_run`. -/
theorem Compile.padRegsTM_run (k : Nat) (s : State) (hbit : Compile.BitState s) :
    runFlatTM (Compile.padBudget k s) (Compile.padRegsTM k)
        (initFlatConfig (Compile.padRegsTM k) [Compile.encodeTape s])
      = some { state_idx := Compile.padRegsExit k,
               tapes := [([], 0, Compile.encodeTape (s ++ List.replicate k []))] } := by
  induction k generalizing s with
  | zero =>
      show runFlatTM 0 Compile.haltTM { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] }
          = some { state_idx := 0, tapes := [([], 0, Compile.encodeTape (s ++ List.replicate 0 []))] }
      rw [List.replicate_zero, List.append_nil]; rfl
  | succ k ih =>
      have hbit' : Compile.BitState (s ++ [[]]) := by
        have := Compile.BitState_append_replicate_nil s 1 hbit
        rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
      have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape (s ++ [[]])) = some v
          → v < max Compile.padBody.sig (Compile.padRegsTM k).sig := by
        intro v hv
        rw [show max Compile.padBody.sig (Compile.padRegsTM k).sig = 4 from by
              rw [Compile.padRegsTM_sig k]; decide]
        exact Compile.curSym_lt (Compile.encodeTape_lt_four (s ++ [[]]) hbit') _ v hv
      have hcomp := composeFlatTM_run (M₁ := Compile.padBody) (M₂ := Compile.padRegsTM k)
        (exit := Compile.padBodyExit)
        Compile.padBody_valid (Compile.padRegsTM_valid k)
        (by rw [Compile.padBody_states]; decide)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] }
        (by show (0 : Nat) < Compile.padBody.states; decide)
        [] 0 (Compile.encodeTape (s ++ [[]])) hsym
        (Compile.padBody_run s hbit)
        (by
          intro m hm cm hcm
          have hnh := Compile.padBody_no_early_halt s hbit m hm cm hcm
          refine ⟨fun h => ?_, hnh⟩
          have hb : haltingStateReached Compile.padBody cm = true := by
            show Compile.padBody.halt.getD cm.state_idx false = true
            rw [h]; decide
          rw [hb] at hnh; exact absurd hnh (by decide))
        (ih (s ++ [[]]) hbit')
        (Compile.padRegsTM_halt k rfl)
      obtain ⟨hrun, _⟩ := hcomp
      have htape : (s ++ [[]]) ++ List.replicate k [] = s ++ List.replicate (k + 1) [] := by
        rw [List.append_assoc]; simp [List.replicate_succ]
      rw [Compile.padBody_states] at hrun
      rw [← htape]
      exact hrun

/-- **`padRegsTM` trajectory.** It does not hit the exit or any halt state before
`padBudget k s`. Induction via `composeFlatTM_no_early_halt` + `padBody`'s trajectory. -/
theorem Compile.padRegsTM_traj (k : Nat) (s : State) (hbit : Compile.BitState s) :
    ∀ j, j < Compile.padBudget k s → ∀ ck,
      runFlatTM j (Compile.padRegsTM k)
          (initFlatConfig (Compile.padRegsTM k) [Compile.encodeTape s]) = some ck →
      ck.state_idx ≠ Compile.padRegsExit k ∧
      haltingStateReached (Compile.padRegsTM k) ck = false := by
  induction k generalizing s with
  | zero => intro j hj ck _; exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
      have hbit' : Compile.BitState (s ++ [[]]) := by
        have := Compile.BitState_append_replicate_nil s 1 hbit
        rwa [show List.replicate 1 ([] : List Nat) = [[]] from rfl] at this
      have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape (s ++ [[]])) = some v
          → v < max Compile.padBody.sig (Compile.padRegsTM k).sig := by
        intro v hv
        rw [show max Compile.padBody.sig (Compile.padRegsTM k).sig = 4 from by
              rw [Compile.padRegsTM_sig k]; decide]
        exact Compile.curSym_lt (Compile.encodeTape_lt_four (s ++ [[]]) hbit') _ v hv
      intro j hj ck hck
      have hnh := composeFlatTM_no_early_halt (M₁ := Compile.padBody) (M₂ := Compile.padRegsTM k)
        (exit := Compile.padBodyExit) (t₂ := Compile.padBudget k (s ++ [[]]))
        Compile.padBody_valid (Compile.padRegsTM_valid k)
        (by rw [Compile.padBody_states]; decide)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] }
        (by show (0 : Nat) < Compile.padBody.states; decide)
        [] 0 (Compile.encodeTape (s ++ [[]])) hsym
        (Compile.padBody_run s hbit)
        (by
          intro m hm cm hcm
          have hb := Compile.padBody_no_early_halt s hbit m hm cm hcm
          refine ⟨fun h => ?_, hb⟩
          have hh : haltingStateReached Compile.padBody cm = true := by
            show Compile.padBody.halt.getD cm.state_idx false = true
            rw [h]; decide
          rw [hh] at hb; exact absurd hb (by decide))
        (fun m hm cm hcm => (ih (s ++ [[]]) hbit' m hm cm hcm).2)
        j hj ck hck
      refine ⟨fun h => ?_, hnh⟩
      have hh : haltingStateReached (Compile.padRegsTM (k + 1)) ck = true :=
        Compile.padRegsTM_halt (k + 1) h
      have hnh' : haltingStateReached (Compile.padRegsTM (k + 1)) ck = false := hnh
      rw [hh] at hnh'; exact absurd hnh' (by decide)

/-! ### The padded decider — `padRegsTM ⨾ bitDeciderTM` -/

/-- The full decider with runtime width-padding: pad to `k + 2 * c.loopDepth`
registers — the program's `regBound = k` **plus the compiler's scratch block**
(`2 * c.loopDepth` registers at base `k`, which must physically exist on the
tape and start `[]`; the `padRegsTM` pad provides exactly that) — then run the
bit-decider at scratch base `k`. The input tape is the **narrow** `encodeTape s`. -/
def Compile.paddedBitDeciderTM (c : Cmd) (k : Nat) : FlatTM :=
  composeFlatTM (Compile.padRegsTM (k + 2 * c.loopDepth)) (Compile.bitDeciderTM c k)
    (Compile.padRegsExit (k + 2 * c.loopDepth))

theorem Compile.paddedBitDeciderTM_valid (c : Cmd) (k : Nat) :
    validFlatTM (Compile.paddedBitDeciderTM c k) :=
  composeFlatTM_valid (Compile.padRegsTM (k + 2 * c.loopDepth)) (Compile.bitDeciderTM c k)
    (Compile.padRegsExit (k + 2 * c.loopDepth))
    (Compile.padRegsTM_valid _) (Compile.bitDeciderTM_valid c k) (Compile.padRegsExit_lt _)
    (Compile.padRegsTM_tapes _) (Compile.bitDeciderTM_tapes c k)

theorem Compile.paddedBitDeciderTM_tapes (c : Cmd) (k : Nat) :
    (Compile.paddedBitDeciderTM c k).tapes = 1 := by
  show (composeFlatTM (Compile.padRegsTM (k + 2 * c.loopDepth)) (Compile.bitDeciderTM c k)
    (Compile.padRegsExit (k + 2 * c.loopDepth))).tapes = 1
  rw [composeFlatTM_tapes, Compile.padRegsTM_tapes]

/-- Halt bits of `paddedBitDeciderTM` past `(Compile k c).states + (padRegsTM …).states`
are the gadget's, shifted by both compositions. -/
theorem Compile.paddedBitDeciderTM_halt_shift (c : Cmd) (k i : Nat) :
    (Compile.paddedBitDeciderTM c k).halt.getD
        (i + (Compile k c).states + (Compile.padRegsTM (k + 2 * c.loopDepth)).states) false
      = Compile.bitTestTM.halt.getD i false := by
  show (composedHalt (Compile.padRegsTM (k + 2 * c.loopDepth)) (Compile.bitDeciderTM c k)).getD
      (i + (Compile k c).states + (Compile.padRegsTM (k + 2 * c.loopDepth)).states) false = _
  rw [composedHalt, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate]
  have he : i + (Compile k c).states + (Compile.padRegsTM (k + 2 * c.loopDepth)).states
      - (Compile.padRegsTM (k + 2 * c.loopDepth)).states = i + (Compile k c).states := by omega
  rw [he, ← List.getD_eq_getElem?_getD]
  exact Compile.bitDeciderTM_halt_shift c k i

/-- **★ The padded decider run (PROVEN from the `padRegsTM` interface +
`bitDecider_run`).** Runs `paddedBitDeciderTM c k` on the **narrow** input
`encodeTape s` — **no `k ≤ s.length` hypothesis** — and reaches the accept/reject
state. The pad makes `k + 2 * c.loopDepth ≤ (s ++ replicate (k + 2*c.loopDepth) []).length`
hold for the inner `bitDecider_run`, and `Cmd.eval_agree`/`cost_agree` transport the
answer/cost from the wide state back to `s`. This is the WALL resolution, validated.

`hwle : s.length ≤ k` is the **scratch-emptiness side** of the 2026-06-11 scratch
interface: the compiler's scratch block sits at registers `[k, k + 2·c.loopDepth)`,
which must be `[]` at machine start — true on the padded tape exactly when the
*input* does not itself extend past `k` (the bridges supply it from `width_le`). -/
theorem Compile.paddedBitDecider_run (c : Cmd) (s : State) (b : Nat) (k : Nat)
    (hbitst : Compile.BitState s) (hwle : s.length ≤ k)
    (huses : Cmd.UsesBelow c k) (hnc : Cmd.NoConsLen c)
    (hbit : b = 0 ∨ b = 1) (h0 : (c.eval s).get 0 = [b]) :
    ∃ cfg,
      runFlatTM (Compile.padBudget (k + 2 * c.loopDepth) s + 1 +
            (Compile.physStepBudget
              (State.size s + (s.length + (k + 2 * c.loopDepth)) + c.cost s + 2)
              (c.cost s) + 3))
          (Compile.paddedBitDeciderTM c k)
          (initFlatConfig (Compile.paddedBitDeciderTM c k) [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (Compile.paddedBitDeciderTM c k) cfg = true ∧
      cfg.state_idx
        = (if b = 1 then 1 else 2) + (Compile k c).states
          + (Compile.padRegsTM (k + 2 * c.loopDepth)).states := by
  set K : Nat := k + 2 * c.loopDepth with hK
  set wide : State := s ++ List.replicate K [] with hwide
  -- Facts about the widened state.
  have hbit_w : Compile.BitState wide := Compile.BitState_append_replicate_nil s K hbitst
  have hk_w : k + 2 * c.loopDepth ≤ wide.length := by
    rw [hwide, List.length_append, List.length_replicate]; omega
  have hagree : AgreeBelow k s wide :=
    fun r _ => (Compile.get_append_replicate_nil s K r).symm
  have hscratch_w : ∀ r, k ≤ r → State.get wide r = [] := by
    intro r hr
    rw [hwide, Compile.get_append_replicate_nil s K r]
    exact Compile.get_of_length_le s r (Nat.le_trans hwle hr)
  have heval0 : (c.eval s).get 0 = (c.eval wide).get 0 :=
    Cmd.eval_agree c k huses hagree 0 (Cmd.UsesBelow_pos huses)
  have h0_w : (c.eval wide).get 0 = [b] := by rw [← heval0]; exact h0
  have hcost : c.cost wide = c.cost s := (Cmd.cost_agree c k huses hagree).symm
  have hsize : State.size wide = State.size s := Compile.size_append_replicate_nil s K
  -- The inner decider run on the WIDE tape.
  obtain ⟨cfg2, hrun2, hhalt2, hstate2⟩ :=
    Compile.bitDecider_run c wide b k hbit_w hk_w huses hscratch_w hnc hbit h0_w
  -- Rewrite its budget in terms of the narrow state's size/cost.
  have hlenw : wide.length = s.length + K := by
    rw [hwide, List.length_append, List.length_replicate]
  rw [hcost, hsize, hlenw] at hrun2
  -- Compose: pad (M₁) then the decider (M₂), spliced at `padRegsExit`.
  have hstate0 : (initFlatConfig (Compile.padRegsTM K)
      [Compile.encodeTape s]).state_idx < (Compile.padRegsTM K).states :=
    (Compile.padRegsTM_valid K).1
  -- The intermediate tape symbol (leading `endMark`) is `< max sigs`.
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0,
      Compile.encodeTape wide) = some v →
        v < max (Compile.padRegsTM K).sig (Compile.bitDeciderTM c k).sig := by
    intro v hv
    have hces : currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape wide)
        = some Compile.endMark := rfl
    have hv2 : v = Compile.endMark := ((Option.some.injEq _ _).mp (hces.symm.trans hv)).symm
    subst hv2
    have hbd : (Compile.bitDeciderTM c k).sig = max (Compile k c).sig Compile.bitTestTM.sig := by
      show (composeFlatTM (Compile k c) Compile.bitTestTM (Compile.exit k c)).sig = _
      rw [composeFlatTM_sig]
    have h4 : (4 : Nat) ≤ max (Compile.padRegsTM K).sig (Compile.bitDeciderTM c k).sig := by
      refine Nat.le_trans ?_ (Nat.le_max_right _ _)
      rw [hbd, Compile_sig]; exact Nat.le_max_left _ _
    exact Nat.lt_of_lt_of_le (by decide : Compile.endMark < 4) h4
  have hcomp := composeFlatTM_run (M₁ := Compile.padRegsTM K) (M₂ := Compile.bitDeciderTM c k)
    (exit := Compile.padRegsExit K)
    (Compile.padRegsTM_valid K) (Compile.bitDeciderTM_valid c k) (Compile.padRegsExit_lt K)
    (initFlatConfig (Compile.padRegsTM K) [Compile.encodeTape s]) hstate0
    [] 0 (Compile.encodeTape wide) hsym
    (Compile.padRegsTM_run K s hbitst) (Compile.padRegsTM_traj K s hbitst)
    hrun2 hhalt2
  obtain ⟨hcrun, hchalt⟩ := hcomp
  refine ⟨{ state_idx := cfg2.state_idx + (Compile.padRegsTM K).states,
            tapes := cfg2.tapes }, hcrun, hchalt, ?_⟩
  rw [hstate2]

/-! ## ★ The padded *compute* run — the function-side WALL resolution (2026-06-08)

The reduction side (`PolyTimeComputableLang.toFrameworkWitness'` / `ComputesBy`) faces
the **same WALL** the decider side did: `Compile_run_physical_residue` carries
`k ≤ s.length`, unsatisfiable for a narrow reduction input whose program touches
`regBound > s.length` registers. The fix is the *same* runtime register-width padding:
`paddedComputeTM c k := padRegsTM k ⨾ Compile c` widens the tape first (exactly like
`paddedBitDeciderTM`), but keeps the **full output tape** (no bit-test gadget) so a
reduction can decode an arbitrary output register. `Cmd.eval_agree`/`cost_agree`
transport the result/cost from the wide state back to `s`.

This is the function-computation analogue of `Compile.paddedBitDecider_run`, PROVEN
from the same `padRegsTM` interface + `Compile_run_physical_residue` (residual sorrys
= the pinned leaf gadgets only). It is what the retargeted `toFrameworkWitness'`
consumes in place of the (wrong-budget) `Compile_sound`. -/

/-- The padded compute machine: pad the registers to width `≥ k`, then run `Compile c`. -/
def Compile.paddedComputeTM (c : Cmd) (k : Nat) : FlatTM :=
  composeFlatTM (Compile.padRegsTM (k + 2 * c.loopDepth)) (Compile k c)
    (Compile.padRegsExit (k + 2 * c.loopDepth))

theorem Compile.paddedComputeTM_valid (c : Cmd) (k : Nat) :
    validFlatTM (Compile.paddedComputeTM c k) :=
  composeFlatTM_valid (Compile.padRegsTM (k + 2 * c.loopDepth)) (Compile k c)
    (Compile.padRegsExit (k + 2 * c.loopDepth))
    (Compile.padRegsTM_valid _) (Compile_valid k c) (Compile.padRegsExit_lt _)
    (Compile.padRegsTM_tapes _) (Compile_tapes k c)

theorem Compile.paddedComputeTM_tapes (c : Cmd) (k : Nat) :
    (Compile.paddedComputeTM c k).tapes = 1 := by
  show (composeFlatTM (Compile.padRegsTM (k + 2 * c.loopDepth)) (Compile k c)
    (Compile.padRegsExit (k + 2 * c.loopDepth))).tapes = 1
  rw [composeFlatTM_tapes, Compile.padRegsTM_tapes]

/-- **★ The padded compute run (PROVEN from the `padRegsTM` interface +
`Compile_run_physical_residue`).** Runs `paddedComputeTM c k` on the **narrow** input
`encodeTape s` — **no `k ≤ s.length` hypothesis** — and halts at the compiler's exit
(shifted by the padder's state count) with the tape `encodeTape (c.eval wide) ++ res`
for the widened state `wide = s ++ replicate (k + 2*c.loopDepth) []` (program
registers `< k` plus the compiler's scratch block). The pad makes the register-width
and scratch-emptiness hypotheses of the inner `Compile_run_physical_residue` hold
(`hwle : s.length ≤ k` keeps the input out of the scratch block — the bridges supply
it from `width_le`); the caller transports the decoded output from `wide` back to `s`
with `Cmd.eval_agree`. Budget: `padBudget (k + 2*c.loopDepth) s + 1 +
physStepBudget G (c.cost s)`, both `inOPoly` (`padBudget_le` / `physStepBudget_poly`). -/
theorem Compile.paddedCompute_run (c : Cmd) (s : State) (k : Nat)
    (hbitst : Compile.BitState s) (hwle : s.length ≤ k)
    (huses : Cmd.UsesBelow c k) (hnc : Cmd.NoConsLen c) :
    ∃ (res : List Nat),
      Compile.ValidResidue res ∧
      runFlatTM (Compile.padBudget (k + 2 * c.loopDepth) s + 1 +
            Compile.physStepBudget
              (State.size s + (s.length + (k + 2 * c.loopDepth)) + c.cost s + 2) (c.cost s))
          (Compile.paddedComputeTM c k)
          (initFlatConfig (Compile.paddedComputeTM c k) [Compile.encodeTape s])
        = some { state_idx := Compile.exit k c
                   + (Compile.padRegsTM (k + 2 * c.loopDepth)).states,
                 tapes := [([], 0,
                   Compile.encodeTape (c.eval (s ++ List.replicate (k + 2 * c.loopDepth) []))
                     ++ res)] } ∧
      haltingStateReached (Compile.paddedComputeTM c k)
          { state_idx := Compile.exit k c
              + (Compile.padRegsTM (k + 2 * c.loopDepth)).states,
            tapes := [([], 0,
              Compile.encodeTape (c.eval (s ++ List.replicate (k + 2 * c.loopDepth) []))
                ++ res)] } = true := by
  set K : Nat := k + 2 * c.loopDepth with hK
  set wide : State := s ++ List.replicate K [] with hwide
  have hbit_w : Compile.BitState wide := Compile.BitState_append_replicate_nil s K hbitst
  have hk_w : k + 2 * c.loopDepth ≤ wide.length := by
    rw [hwide, List.length_append, List.length_replicate]; omega
  have hcost : c.cost wide = c.cost s :=
    (Cmd.cost_agree c k huses
      (fun r _ => (Compile.get_append_replicate_nil s K r).symm)).symm
  have hsize : State.size wide = State.size s := Compile.size_append_replicate_nil s K
  have hscratch_w : ∀ r, k ≤ r → State.get wide r = [] := by
    intro r hr
    rw [hwide, Compile.get_append_replicate_nil s K r]
    exact Compile.get_of_length_le s r (Nat.le_trans hwle hr)
  have hlenw : wide.length = s.length + K := by
    rw [hwide, List.length_append, List.length_replicate]
  -- inner residue run on the WIDE tape
  obtain ⟨t1, res, hres, hrun2, _htraj2, ht1⟩ :=
    Compile_run_physical_residue c k wide hbit_w hk_w huses hscratch_w hnc
  rw [hcost, hsize, hlenw] at ht1
  -- the inner exit is a halt state of `Compile k c`
  have hhalt2 : haltingStateReached (Compile k c)
      { state_idx := Compile.exit k c,
        tapes := [([], 0, Compile.encodeTape (c.eval wide) ++ res)] } = true := by
    show (Compile k c).halt.getD (Compile.exit k c) false = true
    have hex := (compileCmd k c).exit_is_halt
    show (compileCmd k c).M.halt.getD (compileCmd k c).exit false = true
    simp only [List.getD, hex, Option.getD]
  -- compose: pad (M₁) then `Compile k c` (M₂), spliced at `padRegsExit`.
  have hstate0 : (initFlatConfig (Compile.padRegsTM K)
      [Compile.encodeTape s]).state_idx < (Compile.padRegsTM K).states :=
    (Compile.padRegsTM_valid K).1
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0,
      Compile.encodeTape wide) = some v →
        v < max (Compile.padRegsTM K).sig (Compile k c).sig := by
    intro v hv
    have hces : currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape wide)
        = some Compile.endMark := rfl
    have hv2 : v = Compile.endMark := ((Option.some.injEq _ _).mp (hces.symm.trans hv)).symm
    subst hv2
    have h4 : (4 : Nat) ≤ max (Compile.padRegsTM K).sig (Compile k c).sig :=
      Nat.le_trans (Nat.le_of_eq (Compile_sig k c).symm) (Nat.le_max_right _ _)
    exact Nat.lt_of_lt_of_le (by decide : Compile.endMark < 4) h4
  have hcomp := composeFlatTM_run (M₁ := Compile.padRegsTM K) (M₂ := Compile k c)
    (exit := Compile.padRegsExit K)
    (Compile.padRegsTM_valid K) (Compile_valid k c) (Compile.padRegsExit_lt K)
    (initFlatConfig (Compile.padRegsTM K) [Compile.encodeTape s]) hstate0
    [] 0 (Compile.encodeTape wide) hsym
    (Compile.padRegsTM_run K s hbitst) (Compile.padRegsTM_traj K s hbitst)
    hrun2 hhalt2
  obtain ⟨hcrun, hchalt⟩ := hcomp
  refine ⟨res, hres, ?_, hchalt⟩
  -- pad the composed run out to the (poly) stated budget
  obtain ⟨kpad, hkpad⟩ := Nat.le.dest ht1
  have hbudget : Compile.padBudget K s + 1 +
      Compile.physStepBudget (State.size s + (s.length + K) + c.cost s + 2) (c.cost s)
      = (Compile.padBudget K s + 1 + t1) + kpad := by omega
  rw [hbudget]
  exact runFlatTM_extend (M := Compile.paddedComputeTM c k) hcrun hchalt
