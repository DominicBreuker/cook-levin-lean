import CookLevin.Basic.Definitions

/-!
# Accept by halting

`FlatSingleTMGenNP` accepts by halting, whereas a compiled decider halts on both answers.
`demoteHalt M r` removes the reject state `r` from the halt list and deletes its outgoing
transitions, so the wrapped machine gets stuck on a rejected input and halts exactly on an
accepted one. The run lemmas transfer the decider's trajectory to the wrapped machine.
-/

set_option autoImplicit false

namespace CookLevin.Lang.AcceptHalt

/-- Demote state `r` from the halt list and delete its outgoing transitions:
the wrapped machine treats `r` as a STUCK state (non-halting, no step). -/
def demoteHalt (M : FlatTM) (r : Nat) : FlatTM where
  sig := M.sig
  tapes := M.tapes
  states := M.states
  trans := M.trans.filter (fun e => e.src_state != r)
  start := M.start
  halt := M.halt.set r false

theorem demoteHalt_sig (M : FlatTM) (r : Nat) : (demoteHalt M r).sig = M.sig := rfl

theorem demoteHalt_tapes (M : FlatTM) (r : Nat) : (demoteHalt M r).tapes = M.tapes := rfl

/-- Validity transfers: the filtered transition table is a sub-table. -/
theorem demoteHalt_valid (M : FlatTM) (r : Nat) (h : validFlatTM M) :
    validFlatTM (demoteHalt M r) := by
  obtain ⟨hstart, hlen, htrans⟩ := h
  refine ⟨hstart, ?_, ?_⟩
  · show (M.halt.set r false).length = M.states
    rw [List.length_set]; exact hlen
  · intro e he
    exact htrans e (List.mem_filter.mp he).1

/-- The halt bit is unchanged away from `r`. -/
theorem demoteHalt_halting_eq (M : FlatTM) (r : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ r) :
    haltingStateReached (demoteHalt M r) cfg = haltingStateReached M cfg := by
  show (M.halt.set r false).getD cfg.state_idx false = M.halt.getD cfg.state_idx false
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (fun heq => h heq.symm)]

/-- At the demoted state the wrapped machine is never halting (whether or not
`r` is within the halt vector's range). -/
theorem demoteHalt_halting_at (M : FlatTM) (r : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx = r) :
    haltingStateReached (demoteHalt M r) cfg = false := by
  show (M.halt.set r false).getD cfg.state_idx false = false
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_set]
  split
  · split <;> rfl
  · next hn => exact absurd rfl hn

/-- `find?` commutes with dropping the source-`r` entries when the config is
not at `r` (dropped entries could not have matched). -/
private theorem find?_filter_eq (l : List FlatTMTransEntry) (r : Nat)
    (cfg : FlatTMConfig) (h : cfg.state_idx ≠ r) :
    (l.filter (fun e => e.src_state != r)).find?
        (fun e => entryMatchesConfig e cfg)
      = l.find? (fun e => entryMatchesConfig e cfg) := by
  induction l with
  | nil => rfl
  | cons e es ih =>
      by_cases hsrc : e.src_state = r
      · have hf : (e.src_state != r) = false := by simp [hsrc]
        have hnm : entryMatchesConfig e cfg = false := by
          simp only [entryMatchesConfig, Bool.and_eq_false_imp]
          intro hbeq
          rw [hsrc, beq_iff_eq] at hbeq
          exact absurd hbeq.symm h
        rw [List.filter_cons, hf]
        simp only [Bool.false_eq_true, if_false]
        rw [List.find?_cons, hnm]
        exact ih
      · have hf : (e.src_state != r) = true := by simp [hsrc]
        rw [List.filter_cons, hf]
        simp only [if_true]
        rw [List.find?_cons, List.find?_cons]
        cases hm : entryMatchesConfig e cfg
        · exact ih
        · rfl

/-- The step function is unchanged away from `r`. -/
theorem demoteHalt_step_eq (M : FlatTM) (r : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ r) :
    stepFlatTM (demoteHalt M r) cfg = stepFlatTM M cfg := by
  show ((M.trans.filter (fun e => e.src_state != r)).find?
        (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg)
    = (M.trans.find? (fun e => entryMatchesConfig e cfg)).bind
        (applyTransitionEntry cfg)
  rw [find?_filter_eq M.trans r cfg h]

/-- At the demoted state the wrapped machine has no step: it is stuck. -/
theorem demoteHalt_step_none (M : FlatTM) (r : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx = r) :
    stepFlatTM (demoteHalt M r) cfg = none := by
  have hfind : (M.trans.filter (fun e => e.src_state != r)).find?
      (fun e => entryMatchesConfig e cfg) = none := by
    rw [List.find?_eq_none]
    intro e he
    have hne : e.src_state ≠ r := by
      have := (List.mem_filter.mp he).2
      simpa using this
    simp only [entryMatchesConfig, Bool.not_eq_true, Bool.and_eq_false_imp]
    intro hbeq
    rw [beq_iff_eq] at hbeq
    exact absurd (hbeq.trans h) hne
  show ((M.trans.filter (fun e => e.src_state != r)).find?
        (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) = none
  rw [hfind]
  rfl

/-- **Run preservation.** If the `M`-run from `cfg0` never visits the demoted
state `r` within `t` steps, the wrapped machine produces the identical run.
Mirror of `Compile.joinTwoHalts_run_eq`. -/
theorem demoteHalt_run_eq (M : FlatTM) (r : Nat) :
    ∀ (t : Nat) (cfg0 : FlatTMConfig),
      (∀ k, k ≤ t → ∀ ck, runFlatTM k M cfg0 = some ck → ck.state_idx ≠ r) →
      runFlatTM t (demoteHalt M r) cfg0 = runFlatTM t M cfg0 := by
  intro t
  induction t with
  | zero => intro cfg0 _; rfl
  | succ n ih =>
      intro cfg0 hstate
      have h0 : cfg0.state_idx ≠ r := hstate 0 (Nat.zero_le _) cfg0 rfl
      have hhaltd : haltingStateReached (demoteHalt M r) cfg0
          = haltingStateReached M cfg0 := demoteHalt_halting_eq M r cfg0 h0
      have hstepd : stepFlatTM (demoteHalt M r) cfg0 = stepFlatTM M cfg0 :=
        demoteHalt_step_eq M r cfg0 h0
      by_cases hhalt : haltingStateReached M cfg0 = true
      · rw [runFlatTM_of_halting (demoteHalt M r) cfg0 (n + 1)
              (by rw [hhaltd]; exact hhalt),
            runFlatTM_of_halting M cfg0 (n + 1) hhalt]
      · cases hstep : stepFlatTM M cfg0 with
        | none =>
            rw [runFlatTM_stuck (demoteHalt M r) cfg0
                  (by rw [hhaltd]; exact Bool.not_eq_true _ ▸ hhalt)
                  (by rw [hstepd]; exact hstep),
                runFlatTM_stuck M cfg0 (Bool.not_eq_true _ ▸ hhalt) hstep]
        | some cfg' =>
            have hL : runFlatTM (n + 1) (demoteHalt M r) cfg0
                = runFlatTM n (demoteHalt M r) cfg' := by
              show (if haltingStateReached (demoteHalt M r) cfg0 = true then some cfg0
                    else match stepFlatTM (demoteHalt M r) cfg0 with
                      | none => some cfg0
                      | some c => runFlatTM n (demoteHalt M r) c) = _
              rw [if_neg (by rw [hhaltd]; exact hhalt), hstepd, hstep]
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

/-- **Weak run preservation**: only the configs *strictly before* step `t` must
avoid `r` (the step-`t` config may be `r` itself — the runs only diverge when
stepping *out of* `r`). Mirror of `Compile.joinTwoHalts_run_eq_weak`. -/
theorem demoteHalt_run_eq_weak (M : FlatTM) (r : Nat) :
    ∀ (t : Nat) (cfg0 : FlatTMConfig),
      (∀ k, k < t → ∀ ck, runFlatTM k M cfg0 = some ck → ck.state_idx ≠ r) →
      runFlatTM t (demoteHalt M r) cfg0 = runFlatTM t M cfg0 := by
  intro t
  induction t with
  | zero => intro cfg0 _; rfl
  | succ n ih =>
      intro cfg0 hstate
      have h0 : cfg0.state_idx ≠ r := hstate 0 (Nat.succ_pos n) cfg0 rfl
      have hhaltd : haltingStateReached (demoteHalt M r) cfg0
          = haltingStateReached M cfg0 := demoteHalt_halting_eq M r cfg0 h0
      have hstepd : stepFlatTM (demoteHalt M r) cfg0 = stepFlatTM M cfg0 :=
        demoteHalt_step_eq M r cfg0 h0
      by_cases hhalt : haltingStateReached M cfg0 = true
      · rw [runFlatTM_of_halting (demoteHalt M r) cfg0 (n + 1)
              (by rw [hhaltd]; exact hhalt),
            runFlatTM_of_halting M cfg0 (n + 1) hhalt]
      · cases hstep : stepFlatTM M cfg0 with
        | none =>
            rw [runFlatTM_stuck (demoteHalt M r) cfg0
                  (by rw [hhaltd]; exact Bool.not_eq_true _ ▸ hhalt)
                  (by rw [hstepd]; exact hstep),
                runFlatTM_stuck M cfg0 (Bool.not_eq_true _ ▸ hhalt) hstep]
        | some cfg' =>
            have hL : runFlatTM (n + 1) (demoteHalt M r) cfg0
                = runFlatTM n (demoteHalt M r) cfg' := by
              show (if haltingStateReached (demoteHalt M r) cfg0 = true then some cfg0
                    else match stepFlatTM (demoteHalt M r) cfg0 with
                      | none => some cfg0
                      | some c => runFlatTM n (demoteHalt M r) c) = _
              rw [if_neg (by rw [hhaltd]; exact hhalt), hstepd, hstep]
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

/-- **First-halt extraction.** `runFlatTM` freezes at the first halting
configuration it meets, so a bare `run ∧ halting` pair (the shape
`Compile.paddedBitDecider_run` exposes — it has no trajectory conjunct)
already yields a run to the SAME config with a no-early-halt trajectory.
This is what feeds the transport pair below from the compiled decider. -/
theorem runFlatTM_first_halt (M : FlatTM) :
    ∀ (T : Nat) (cfg0 cfg : FlatTMConfig),
      runFlatTM T M cfg0 = some cfg →
      haltingStateReached M cfg = true →
      ∃ t, t ≤ T ∧ runFlatTM t M cfg0 = some cfg ∧
        ∀ k, k < t → ∀ ck, runFlatTM k M cfg0 = some ck →
          haltingStateReached M ck = false
  | 0, cfg0, cfg, hrun, _ => by
      refine ⟨0, Nat.le_refl _, hrun, ?_⟩
      intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | T + 1, cfg0, cfg, hrun, hhalt => by
      by_cases h0 : haltingStateReached M cfg0 = true
      · have h1 : runFlatTM (T + 1) M cfg0 = some cfg0 :=
          runFlatTM_of_halting M cfg0 (T + 1) h0
        rw [h1] at hrun
        obtain rfl : cfg0 = cfg := Option.some.inj hrun
        refine ⟨0, Nat.zero_le _, rfl, ?_⟩
        intro k hk; exact absurd hk (Nat.not_lt_zero k)
      · have hunfold : ∀ (k : Nat) (c' : FlatTMConfig), stepFlatTM M cfg0 = some c' →
            runFlatTM (k + 1) M cfg0 = runFlatTM k M c' := by
          intro k c' hstep
          show (if haltingStateReached M cfg0 = true then some cfg0
                else match stepFlatTM M cfg0 with
                  | none => some cfg0
                  | some c => runFlatTM k M c) = _
          rw [if_neg h0, hstep]
        cases hstep : stepFlatTM M cfg0 with
        | none =>
            have h1 : runFlatTM (T + 1) M cfg0 = some cfg0 := by
              show (if haltingStateReached M cfg0 = true then some cfg0
                    else match stepFlatTM M cfg0 with
                      | none => some cfg0
                      | some c => runFlatTM T M c) = _
              rw [if_neg h0, hstep]
            rw [h1] at hrun
            obtain rfl : cfg0 = cfg := Option.some.inj hrun
            rw [hhalt] at h0
            exact absurd rfl h0
        | some cfg1 =>
            rw [hunfold T cfg1 hstep] at hrun
            obtain ⟨t, ht, hrun', htraj'⟩ :=
              runFlatTM_first_halt M T cfg1 cfg hrun hhalt
            refine ⟨t + 1, Nat.succ_le_succ ht, ?_, ?_⟩
            · rw [hunfold t cfg1 hstep]; exact hrun'
            · intro k hk ck hck
              cases k with
              | zero =>
                  obtain rfl : cfg0 = ck := Option.some.inj hck
                  exact Bool.not_eq_true _ ▸ h0
              | succ j =>
                  rw [hunfold j cfg1 hstep] at hck
                  exact htraj' j (Nat.lt_of_succ_lt_succ hk) ck hck

/-- **Accept transport (F4 forward).** An `M`-run that halts at a state `≠ r`
with no earlier halt is preserved by the wrapper, for every budget `≥ t`. -/
theorem demoteHalt_run_accept (M : FlatTM) (r : Nat) {t : Nat}
    {cfg0 cfg : FlatTMConfig}
    (hrun : runFlatTM t M cfg0 = some cfg)
    (htraj : ∀ k, k < t → ∀ ck, runFlatTM k M cfg0 = some ck →
        haltingStateReached M ck = false)
    (hhalt : haltingStateReached M cfg = true)
    (hne : cfg.state_idx ≠ r)
    (hr : M.halt.getD r false = true) :
    ∀ m, t ≤ m →
      runFlatTM m (demoteHalt M r) cfg0 = some cfg ∧
      haltingStateReached (demoteHalt M r) cfg = true := by
  have hnv : ∀ k, k ≤ t → ∀ ck, runFlatTM k M cfg0 = some ck →
      ck.state_idx ≠ r := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · intro hcontra
      have hnh : haltingStateReached M ck = false := htraj k hlt ck hck
      have hh : haltingStateReached M ck = true := by
        show M.halt.getD ck.state_idx false = true
        rw [hcontra]; exact hr
      rw [hh] at hnh
      exact Bool.noConfusion hnh
    · obtain rfl : ck = cfg := Option.some.inj (hck.symm.trans hrun)
      exact hne
  have hrund : runFlatTM t (demoteHalt M r) cfg0 = some cfg := by
    rw [demoteHalt_run_eq M r t cfg0 hnv]; exact hrun
  have hhaltd : haltingStateReached (demoteHalt M r) cfg = true := by
    rw [demoteHalt_halting_eq M r cfg hne]; exact hhalt
  intro m hm
  refine ⟨?_, hhaltd⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = t + k := ⟨m - t, by omega⟩
  exact runFlatTM_extend hrund hhaltd

/-- **Reject transport (F4 backward).** An `M`-run that halts AT `r` with no
earlier halt makes the wrapped machine non-halting forever: the wrapped run
parks at `r` (non-halting, stuck) and stays there. -/
theorem demoteHalt_run_reject (M : FlatTM) (r : Nat) {t : Nat}
    {cfg0 cfg : FlatTMConfig}
    (hrun : runFlatTM t M cfg0 = some cfg)
    (htraj : ∀ k, k < t → ∀ ck, runFlatTM k M cfg0 = some ck →
        haltingStateReached M ck = false)
    (hst : cfg.state_idx = r)
    (hr : M.halt.getD r false = true) :
    ∀ m cm, runFlatTM m (demoteHalt M r) cfg0 = some cm →
      haltingStateReached (demoteHalt M r) cm = false := by
  have hnv : ∀ k, k < t → ∀ ck, runFlatTM k M cfg0 = some ck →
      ck.state_idx ≠ r := by
    intro k hk ck hck hcontra
    have hnh : haltingStateReached M ck = false := htraj k hk ck hck
    have hh : haltingStateReached M ck = true := by
      show M.halt.getD ck.state_idx false = true
      rw [hcontra]; exact hr
    rw [hh] at hnh
    exact Bool.noConfusion hnh
  have hrund : runFlatTM t (demoteHalt M r) cfg0 = some cfg := by
    rw [demoteHalt_run_eq_weak M r t cfg0 hnv]; exact hrun
  have hnh_cfg : haltingStateReached (demoteHalt M r) cfg = false :=
    demoteHalt_halting_at M r cfg hst
  have hstuck : stepFlatTM (demoteHalt M r) cfg = none :=
    demoteHalt_step_none M r cfg hst
  intro m cm hcm
  rcases Nat.lt_or_ge m t with hlt | hge
  · have : runFlatTM m (demoteHalt M r) cfg0 = runFlatTM m M cfg0 :=
      demoteHalt_run_eq_weak M r m cfg0
        (fun k hk => hnv k (Nat.lt_trans hk hlt))
    rw [this] at hcm
    have hnh : haltingStateReached M cm = false := htraj m hlt cm hcm
    have hne : cm.state_idx ≠ r := hnv m hlt cm hcm
    rw [demoteHalt_halting_eq M r cm hne]
    exact hnh
  · obtain ⟨k, rfl⟩ : ∃ k, m = t + k := ⟨m - t, by omega⟩
    rw [runFlatTM_compose (demoteHalt M r) t k cfg0 cfg hrund,
        runFlatTM_stuck (demoteHalt M r) cfg hnh_cfg hstuck k] at hcm
    obtain rfl : cfg = cm := Option.some.inj hcm
    exact hnh_cfg

/-! ## `acceptsFlatTM`-level corollaries -/

theorem demoteHalt_initFlatConfig (M : FlatTM) (r : Nat)
    (tapes : List (List Nat)) :
    initFlatConfig (demoteHalt M r) tapes = initFlatConfig M tapes := rfl

end CookLevin.Lang.AcceptHalt
