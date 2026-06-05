import Complexity.Lang.Semantics
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

/-- Compile `Op.copy dst src`. **Stub.** -/
def Compile.opCopy (_dst _src : Var) : CompiledCmd := compiledCmd_default

/-- Compile `Op.tail dst src`. **Stub.** -/
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

/-- `composeFlatTM` inherits a unique halt from `M₂`'s unique halt. -/
theorem Compile.composeFlatTM_halt_unique (M₁ M₂ : FlatTM) (e₂ exit : Nat)
    (h2 : ∀ i, M₂.halt[i]? = some true → i = e₂) :
    ∀ i, (composeFlatTM M₁ M₂ exit).halt[i]? = some true → i = M₁.states + e₂ := by
  intro i hi
  obtain ⟨hge, hh⟩ := ScanLeft.composeFlatTM_halt_some_imp M₁ M₂ exit i hi
  have := h2 _ hh; omega

/-- `M₂`'s halt state shifts to a halt of `composeFlatTM` (intro). -/
theorem Compile.composeFlatTM_halt_intro (M₁ M₂ : FlatTM) (e₂ exit : Nat)
    (h : M₂.halt[e₂]? = some true) :
    (composeFlatTM M₁ M₂ exit).halt[M₁.states + e₂]? = some true :=
  ScanLeft.composeFlatTM_halt_some_intro M₁ M₂ exit e₂ h

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

/-- **`BitState` is preserved by every op except `consLen` (Task 1 — the
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
`≤ 1` cell is `0` or `1`), not invariant-breaking. So Task 1's unary restatement is
required for **correctness** only for `consLen`; for `takeAt`/`dropAt` it is
required only for **expressiveness**. The `hcons` hypothesis isolates exactly the
`consLen` obligation: once Task 1 restates `consLen` to write a unary block, the
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
is *not* a `BitState`. This is why Task 1 must restate `consLen` to a unary block;
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
         -- ⚠ THIS LEMMA IS UNSATISFIABLE for deletion ops (see
         -- `clear_physical_unsatisfiable`); use `compileOp_sound_physical_residue`.

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
polynomial total — `toFrameworkWitness'` only needs `inOPoly`. -/
theorem compileOp_sound_physical_residue (o : Op) (s : State) (res_in : List Nat)
    (hbit : Compile.BitState s) (hbnd : o.inBounds s)
    (hres_in : Compile.ValidResidue res_in) :
    ∃ (t : Nat) (res_out : List Nat),
      Compile.ValidResidue res_out ∧
      runFlatTM t (compileOp o).M
          (initFlatConfig (compileOp o).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (compileOp o).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval o s) ++ res_out)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (compileOp o).M
              (initFlatConfig (compileOp o).M [Compile.encodeTape s ++ res_in]) = some ck →
          ck.state_idx ≠ (compileOp o).exit ∧
          haltingStateReached (compileOp o).M ck = false)
      ∧ t ≤ 9 * (Compile.encodeTape s ++ res_in).length
              * (Compile.encodeTape s ++ res_in).length
              + 9 * (Compile.encodeTape s ++ res_in).length + 30 := by
  cases o with
  | appendOne dst =>
      -- `res_out = res_in`: the append grows `encodeTape s` by one cell; residue passes through.
      -- The append op meets the *linear* `3·L+8`; relax to the contract's quadratic.
      obtain ⟨t, hrun, htraj, hbudget⟩ :=
        Compile.opAppendBit_physical_residue 1 (by omega) s dst hbit hbnd res_in hres_in
      exact ⟨t, res_in, hres_in, hrun, htraj,
        le_trans (le_trans hbudget (Compile.linear_le_quadratic_tapeLen s res_in)) (by omega)⟩
  | appendZero dst =>
      obtain ⟨t, hrun, htraj, hbudget⟩ :=
        Compile.opAppendBit_physical_residue 0 (by omega) s dst hbit hbnd res_in hres_in
      exact ⟨t, res_in, hres_in, hrun, htraj,
        le_trans (le_trans hbudget (Compile.linear_le_quadratic_tapeLen s res_in)) (by omega)⟩
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
        Compile.ValidResidue_append_replicate_zero res_in _ hres_in, ?_, ?_, le_trans hbud (by omega)⟩
      · rw [hinit]; exact hrun
      · intro k hk ck hck
        rw [hinit] at hck
        exact htraj k hk ck hck
  | copy dst src => sorry
  | tail dst src => sorry
  | head dst src =>
      obtain ⟨t, hrun, htraj, hbud⟩ :=
        Compile.opHead_run s dst src res_in hbit hbnd.1 hbnd.2 hres_in
      exact ⟨t, res_in ++ List.replicate (s.get dst).length 0,
        Compile.ValidResidue_append_replicate_zero res_in _ hres_in, hrun, htraj, hbud⟩
  | eqBit dst src1 src2 => sorry
  | nonEmpty dst src =>
      obtain ⟨t, hrun, htraj, hbud⟩ :=
        Compile.opNonEmpty_run s dst src res_in hbit hbnd.1 hbnd.2 hres_in
      exact ⟨t, res_in ++ List.replicate (s.get dst).length 0,
        Compile.ValidResidue_append_replicate_zero res_in _ hres_in, hrun, htraj, hbud⟩
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
         -- ⚠ THIS EXACT-TAPE CONTRACT IS UNSATISFIABLE for commands that use
         -- length-decreasing ops. Use `Compile_run_physical_residue` below.

/-- **Residue-tolerant physical compiler contract (Risk C2).** The replacement
for `Compile_run_physical` that accounts for the tape never shrinking: the exit
tape is `encodeTape (c.eval s) ++ res` for some `ValidResidue` residue `res`,
head rewound to `0`. This is provable for ALL ops (including deletion ops like
`clear`/`tail`) because the residue absorbs the cells vacated by left-shifting.

Composes per-fragment via `compileSeq_sound_physical_residue` (proven), using
`compileOp_sound_physical_residue` for each `Op` fragment. The budget is
quadratic (`overhead`) in `size + cost`, covering the linear per-fragment
budgets summed over `~cost` fragments.

The decider bridge (`bitDeciderTM`) reads the answer from register `0` via
`decodeTape`, which ignores the residue (`decodeTape_encodeTape_append`),
so the residue is invisible to the decider. -/
theorem Compile_run_physical_residue (c : Cmd) (s : State) :
    ∃ (t : Nat) (res : List Nat),
      Compile.ValidResidue res ∧
      runFlatTM t (Compile c) (initFlatConfig (Compile c) [Compile.encodeTape s])
          = some { state_idx := Compile.exit c,
                   tapes := [([], 0, Compile.encodeTape (c.eval s) ++ res)] } ∧
      (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile c)
              (initFlatConfig (Compile c) [Compile.encodeTape s]) = some ck →
          ck.state_idx ≠ Compile.exit c ∧
          haltingStateReached (Compile c) ck = false) ∧
      t ≤ Compile.overhead (State.size s + c.cost s) := by
  sorry  -- TODO(C2): compose per-fragment via `compileSeq_sound_physical_residue`.
         -- Induction on `Cmd`; each `Op` case from `compileOp_sound_physical_residue`,
         -- `seq` from `compileSeq_sound_physical_residue`, `ifBit` and `forBnd`
         -- from their residue-tolerant siblings (to be stated).
         --
         -- ⚠ STRUCTURAL BLOCKER (Task 1): this statement LACKS the `(hbit :
         -- Compile.BitState s)` hypothesis that EVERY per-fragment lemma requires
         -- (`compileOp_sound_physical_residue` and the 10 lemmas at lines 2393/2554/
         -- 2901/3025/3160/3387/3535/3761/3823/4149 all take `hbit`). The induction
         -- cannot feed them without `hbit` here. Add it — and then the bridge must
         -- supply `BitState (encodeState x)` (the Option A/B fork in HANDOFF.md).
         --
         -- ⚠⚠ BUDGET IS WRONG AS STATED (deep feasibility pass 2026-06-04, Finding A).
         -- The per-op budget is QUADRATIC in tape length L (`9·L²+…`, since `clear`
         -- and the cross-register transfer ops do Θ(L) cell-moves each an O(L) pass),
         -- and `L = size + s.length + 2` includes the REGISTER COUNT. Summing ~`cost`
         -- such per-op quadratics ⇒ a CUBIC total in `size + s.length + cost`. The
         -- stated `overhead(size+cost)` with `overhead m = (m+1)²` is too small on
         -- BOTH counts (degree, and dropping `s.length`). FIX before proving this:
         -- restate as `overhead(State.size s + s.length + c.cost s)` with
         -- `Compile.overhead` bumped to CUBIC (e.g. `9·(m+1)³`). Downstream needs only
         -- `overhead_poly`/`overhead_mono` (degree-agnostic), so it ripples mechanically
         -- to `bitDecider_run`, the `DecidesBy` budgets, and `toFrameworkWitness'`.
         -- Stays poly on the live path (`encodeState x` = 1 reg; `s.length` ≤ const
         -- `regBound`). See HANDOFF.md "Deep feasibility pass".

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
  obtain ⟨tl0, htl0⟩ := Compile.encodeTape_eq_cons_of_get_zero (c.eval s) b h0
  obtain ⟨t1, res, _hres, hrun1, htraj1, ht1⟩ := Compile_run_physical_residue c s
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
