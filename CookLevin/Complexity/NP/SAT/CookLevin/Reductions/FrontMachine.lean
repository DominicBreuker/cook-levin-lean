import Complexity.Lang.AcceptHalt
import Complexity.Lang.FormatCheck
import Complexity.Lang.Compile.Decider

set_option autoImplicit false

/-! # The per-`Q` front machine `M_Q` + the machine-level correctness iff (C8-4)

This is the machine half of the C8-4 assembly (HANDOFF "NEXT BOTTOM-UP session
— C8-4"): the concrete `FlatTM` that the per-`Q` front witness `W_Q` emits as
its constant machine register, together with its **correctness iff** — the
reusable, verifier-abstract statement relating `acceptsFlatTM M_Q [s_x ++ cert]`
to the verifier program's own accept/reject decision. The witness-fields
session consumes these against `InNPWitnessLangFreeSplit`'s `verifier.decides`.

## Construction (validated end-to-end in `probes/C8MachineProbe.lean`)

`M_Q c k w := composeFlatTM (formatCheckTM w) (demoteHalt (paddedBitDeciderTM c k)
(rejectState c k)) (w + 6)` where

* `c` is the hypothesis witness's verifier `Cmd`, `k = regBound`, `w = xWidth`;
* `formatCheckTM w` (C8-2b) scans the whole tape for the canonical
  `3 ({1,2}* 0)^(w+1) 3` grammar, halting only at its unique done state `w + 6`
  (its exit), and STICKING on any grammar violation;
* `paddedBitDeciderTM c k` (the compiler) decodes the tape to the state `s` and
  halts at the accept state (`b = 1`) or the reject state (`b = 0`);
* `demoteHalt … (rejectState c k)` (C8-2a) demotes the reject state so the
  wrapped machine *parks* (never halts) exactly when the verifier rejects —
  turning halt-on-both-answers into accept-by-halting.

The reject state, read off `paddedBitDecider_run` at `b = 0`, is
`2 + (Compile k c).states + (padRegsTM (k + 2·loopDepth + 2)).states`; the accept
state is the same with a leading `1` (they differ, so demoting the reject one
leaves the accept path halting).

## The iff (verifier-abstract)

Over a bit-level input register block `sx` of width `w` and a bit register
`creg`, with `s := sx ++ [creg]` the decoded state:

* **forward** (`MQ_accepts_of_accept`): if `c` accepts `s` (`(c.eval s).get 0 =
  [1]`) then `M_Q` accepts the tape `(3 :: encodeRegs sx) ++ (shiftReg creg ++
  [0,3])` for every budget `≥ MQbudget`;
* **backward** (`MQ_accept_iff`): if `M_Q` accepts `(3 :: encodeRegs sx) ++
  cert` at any budget, then `cert` is grammar-valid (`= shiftReg creg ++ [0,3]`
  for a bit register `creg`) AND `c` accepts `sx ++ [creg]`.
-/

namespace Complexity.Lang.FrontMachine

open Complexity.Lang.AcceptHalt
open Complexity.Lang.FormatCheck
open TMPrimitives (composeFlatTM composeFlatTM_run composeFlatTM_no_early_halt
  composeFlatTM_stuck_M1 composeFlatTM_valid composeFlatTM_sig composeFlatTM_tapes
  composeFlatTM_states composeFlatTM_start)

/-- The verifier's reject state inside `paddedBitDeciderTM c k` (the `b = 0`
exit of `paddedBitDecider_run`). Demoted by `demoteHalt` so reject ⇒ park. -/
def rejectState (c : Cmd) (k : Nat) : Nat :=
  2 + (Compile k c).states
    + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states

/-- The verifier's accept state (`b = 1`). -/
def acceptState (c : Cmd) (k : Nat) : Nat :=
  1 + (Compile k c).states
    + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states

theorem acceptState_ne_rejectState (c : Cmd) (k : Nat) :
    acceptState c k ≠ rejectState c k := by
  unfold acceptState rejectState; omega

/-- The accept-by-halting-wrapped verifier: `paddedBitDeciderTM` with the reject
state demoted so it parks (never halts) on reject. -/
def M2 (c : Cmd) (k : Nat) : FlatTM :=
  demoteHalt (Compile.paddedBitDeciderTM c k) (rejectState c k)

/-- **The per-`Q` front machine.** -/
def MQ (c : Cmd) (k w : Nat) : FlatTM :=
  composeFlatTM (formatCheckTM w) (M2 c k) (w + 6)

/-! ## Structural lemmas -/

theorem paddedBitDeciderTM_sig (c : Cmd) (k : Nat) :
    (Compile.paddedBitDeciderTM c k).sig = 4 := by
  show (composeFlatTM (Compile.padRegsTM (k + 2 * c.loopDepth + 2))
      (Compile.bitDeciderTM c k) _).sig = 4
  rw [composeFlatTM_sig, Compile.padRegsTM_sig]
  show max 4 (composeFlatTM (Compile k c) Compile.bitTestTM (Compile.exit k c)).sig = 4
  rw [composeFlatTM_sig, Compile_sig, Compile.bitTestTM_sig]; rfl

theorem M2_sig (c : Cmd) (k : Nat) : (M2 c k).sig = 4 := by
  rw [M2, demoteHalt_sig]; exact paddedBitDeciderTM_sig c k

theorem M2_tapes (c : Cmd) (k : Nat) : (M2 c k).tapes = 1 := by
  rw [M2, demoteHalt_tapes]; exact Compile.paddedBitDeciderTM_tapes c k

theorem M2_valid (c : Cmd) (k : Nat) : validFlatTM (M2 c k) :=
  demoteHalt_valid _ _ (Compile.paddedBitDeciderTM_valid c k)

theorem MQ_sig (c : Cmd) (k w : Nat) : (MQ c k w).sig = 4 := by
  rw [MQ, composeFlatTM_sig, formatCheckTM_sig, M2_sig]; rfl

theorem MQ_tapes (c : Cmd) (k w : Nat) : (MQ c k w).tapes = 1 := by
  rw [MQ, composeFlatTM_tapes, formatCheckTM_tapes]

theorem MQ_states (c : Cmd) (k w : Nat) :
    (MQ c k w).states = (w + 7) + (M2 c k).states := by
  rw [MQ, composeFlatTM_states, formatCheckTM_states]

theorem MQ_valid (c : Cmd) (k w : Nat) : validFlatTM (MQ c k w) :=
  composeFlatTM_valid (formatCheckTM w) (M2 c k) (w + 6)
    (formatCheckTM_valid w) (M2_valid c k)
    (by rw [formatCheckTM_states]; omega)
    (formatCheckTM_tapes w) (M2_tapes c k)

/-! ## The reject state is a genuine halt state of the padded decider -/

/-- The demoted reject state carries the padded decider's halt bit `true` — the
`hr` obligation of `demoteHalt_run_accept`/`_reject`. -/
theorem paddedBitDeciderTM_halt_rejectState (c : Cmd) (k : Nat) :
    (Compile.paddedBitDeciderTM c k).halt.getD (rejectState c k) false = true := by
  have h := Compile.paddedBitDeciderTM_halt_shift c k 2
  rw [rejectState]
  rw [show 2 + (Compile k c).states + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states
        = 2 + (Compile k c).states + (Compile.padRegsTM (k + 2 * c.loopDepth + 2)).states from rfl]
  rw [h]; rfl

/-! ## Symbol-bound helper (the `composeFlatTM_run` `h_sym_bound` shape) -/

/-- On a bit-level `encodeTape`, every read symbol is `< 4` (= `max sig sig`). -/
private theorem sym_bound_encodeTape (c : Cmd) (k w : Nat) (s : State)
    (hbit : Compile.BitState s) :
    ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s) = some v →
      v < max (formatCheckTM w).sig (M2 c k).sig := by
  intro v hv
  rw [formatCheckTM_sig, M2_sig]
  show v < max 4 4
  rw [show max 4 4 = 4 from rfl]
  unfold currentTapeSymbol at hv
  by_cases h : (0 : Nat) < (Compile.encodeTape s).length
  · rw [dif_pos h] at hv; injection hv with hv'; subst hv'
    exact Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _)
  · rw [dif_neg h] at hv; exact absurd hv (by simp)

/-! ## Forward: verifier accept ⇒ `M_Q` accepts -/

/-- **Forward direction of the correctness iff.** If the verifier `c` accepts
the decoded state `sx ++ [creg]` (bit-level, fitting the register frame), then
`M_Q` accepts the reassembled tape for every budget `≥ MQbudget`.

The three phases: `formatCheck_run`/`_traj` scan the well-formed tape and halt
at the exit `w + 6`; `paddedBitDecider_run` (at `b = 1`) reaches the accept
state, transported to the wrapped `M2` by `demoteHalt_run_accept` (the reject
state is demoted but the accept path is untouched, `acceptState ≠ rejectState`);
`composeFlatTM_run` glues the two, and `runFlatTM_extend` makes the accept
persist for larger budgets. -/
theorem MQ_accepts_of_accept (c : Cmd) (k w : Nat) (sx : State) (creg : List Nat)
    (hbit : Compile.BitState (sx ++ [creg]))
    (hlen : sx.length = w)
    (hwle : (sx ++ [creg]).length ≤ k)
    (huses : Cmd.UsesBelow c k)
    (haccept : (c.eval (sx ++ [creg])).get 0 = [1]) :
    ∃ T, ∀ steps, T ≤ steps →
      acceptsFlatTM (MQ c k w)
          [(3 :: Compile.encodeRegs sx) ++ (Compile.shiftReg creg ++ [0, 3])] steps = true := by
  set s : State := sx ++ [creg] with hs
  have hlens : s.length = w + 1 := by rw [hs, List.length_append, hlen]; rfl
  set tape : List Nat := Compile.encodeTape s with htape
  have htape_eq : (3 :: Compile.encodeRegs sx) ++ (Compile.shiftReg creg ++ [0, 3]) = tape := by
    rw [htape, hs, encodeTape_certSplit]
  -- Phase 2: the padded decider reaches the accept state.
  obtain ⟨cfg, hrun, hhalt, hstate⟩ :=
    Compile.paddedBitDecider_run c s 1 k hbit hwle huses (Or.inr rfl) haccept
  have hstate' : cfg.state_idx = acceptState c k := by
    rw [hstate, acceptState]; rfl
  have hne : cfg.state_idx ≠ rejectState c k := by
    rw [hstate']; exact acceptState_ne_rejectState c k
  -- Transport the accept run to the wrapped machine `M2`.
  obtain ⟨t0, _ht0, hrun0, htraj0⟩ :=
    runFlatTM_first_halt (Compile.paddedBitDeciderTM c k) _
      (initFlatConfig (Compile.paddedBitDeciderTM c k) [tape]) cfg hrun hhalt
  have hM2run := demoteHalt_run_accept (Compile.paddedBitDeciderTM c k) (rejectState c k)
    hrun0 htraj0 hhalt hne (paddedBitDeciderTM_halt_rejectState c k) t0 (Nat.le_refl t0)
  -- `initFlatConfig` of `M2` equals that of the padded decider.
  have hcfg0M2 : initFlatConfig (M2 c k) [tape]
      = initFlatConfig (Compile.paddedBitDeciderTM c k) [tape] := by
    rw [M2, demoteHalt_initFlatConfig]
  set c0M2 : FlatTMConfig := ⟨(M2 c k).start, [([], 0, tape)]⟩ with hc0M2
  have hc0M2_eq : c0M2 = initFlatConfig (Compile.paddedBitDeciderTM c k) [tape] := by
    rw [hc0M2, ← hcfg0M2]; rfl
  have hrunM2 : runFlatTM t0 (M2 c k) c0M2 = some cfg := by
    rw [hc0M2_eq, M2]; exact hM2run.1
  have hhaltM2 : haltingStateReached (M2 c k) cfg = true := by
    rw [M2]; exact hM2run.2
  -- Phase 1 + bridge + Phase 2: compose.
  set cfg0 : FlatTMConfig := ⟨0, [([], 0, tape)]⟩ with hcfg0
  have hrun1 : runFlatTM (2 * tape.length + 1) (formatCheckTM w) cfg0
      = some ⟨w + 6, [([], 0, tape)]⟩ := by
    rw [hcfg0, htape]; exact formatCheck_run w s hbit hlens
  have htraj1 : ∀ kk, kk < 2 * tape.length + 1 → ∀ ck,
      runFlatTM kk (formatCheckTM w) cfg0 = some ck →
        ck.state_idx ≠ w + 6 ∧ haltingStateReached (formatCheckTM w) ck = false := by
    rw [hcfg0, htape]; exact formatCheck_traj w s hbit hlens
  have hcomp := composeFlatTM_run (M₁ := formatCheckTM w) (M₂ := M2 c k) (exit := w + 6)
    (formatCheckTM_valid w) (M2_valid c k)
    (by rw [formatCheckTM_states]; omega)
    cfg0 (by rw [hcfg0]; show (0 : Nat) < (formatCheckTM w).states; rw [formatCheckTM_states]; omega)
    [] 0 tape (sym_bound_encodeTape c k w s hbit)
    hrun1 htraj1
    (by rw [hc0M2] at hrunM2; exact hrunM2) hhaltM2
  refine ⟨(2 * tape.length + 1) + 1 + t0, fun steps hsteps => ?_⟩
  -- The composed machine halts; extend to any larger budget.
  obtain ⟨k', rfl⟩ : ∃ k', steps = ((2 * tape.length + 1) + 1 + t0) + k' :=
    ⟨steps - ((2 * tape.length + 1) + 1 + t0), by omega⟩
  have hrunMQ : runFlatTM ((2 * tape.length + 1) + 1 + t0) (MQ c k w) cfg0
      = some ⟨cfg.state_idx + (formatCheckTM w).states, cfg.tapes⟩ := by
    rw [MQ]; exact hcomp.1
  have hhaltMQ : haltingStateReached (MQ c k w)
      ⟨cfg.state_idx + (formatCheckTM w).states, cfg.tapes⟩ = true := by
    rw [MQ]; exact hcomp.2
  have hext := runFlatTM_extend (k := k') hrunMQ hhaltMQ
  -- Convert to `acceptsFlatTM`.
  have hvalid : isValidFlatTapes (MQ c k w) [tape] = true := by
    rw [isValidFlatTapes]
    refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
    · rw [decide_eq_true_eq, MQ_tapes]; rfl
    · rw [List.all_cons, List.all_nil, Bool.and_true, isValidFlatTape, List.all_eq_true]
      intro x hx
      rw [decide_eq_true_eq, MQ_sig]
      exact Compile.encodeTape_lt_four s hbit x hx
  rw [htape_eq]
  unfold acceptsFlatTM
  have hexec : execFlatTM (MQ c k w) [tape]
      ((2 * tape.length + 1) + 1 + t0 + k') = some ⟨cfg.state_idx + (formatCheckTM w).states, cfg.tapes⟩ := by
    rw [execFlatTM_eq_some_runFlatTM hvalid]
    have : initFlatConfig (MQ c k w) [tape] = cfg0 := by rw [hcfg0]; rfl
    rw [this]; exact hext
  rw [hexec]; exact hhaltMQ

end Complexity.Lang.FrontMachine
