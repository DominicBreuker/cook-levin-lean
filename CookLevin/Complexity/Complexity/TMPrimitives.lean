import Complexity.Complexity.Definitions
import Complexity.Complexity.MachineSemantics
import Complexity.Complexity.TMDecider
import Mathlib.Data.List.GetD
import Mathlib.Tactic

set_option autoImplicit false

/-! # TM combinator library (Part 2 Step 3+)

We build the minimum apparatus needed to construct concrete Turing
machines compositionally:

- **Step 3** — `composeFlatTM M₁ M₂ exit`, sequential composition.
  Run `M₁` until it reaches a designated `exit` state, then start
  `M₂` from that state (with the tapes left in place).
- **Step 4** — `acceptingTM`, `rejectingTM`, `ifSymbolTM` (added in a
  follow-up commit).
- **Step 5** — tape scanners and segment ops (added in a follow-up).

All machines built here are **single-tape** by convention. We will lift
to multi-tape only if a future decider needs it.
-/

namespace TMPrimitives

/-! ## Sequential composition

We compose two single-tape TMs `M₁` and `M₂` sharing the same alphabet
size and the same number of tapes (1). The composed machine has
`M₁.states + M₂.states` states:

- Indices `[0, M₁.states)` mirror `M₁`'s states.
- Indices `[M₁.states, M₁.states + M₂.states)` mirror `M₂`'s states,
  offset by `M₁.states`.

The `exit : Nat` parameter designates a state of `M₁` from which we
"hand off" to `M₂`. We assume `exit` is a halting state of `M₁` (the
typical usage), so `M₁` has no transitions out of it; we provide
explicit bridge transitions to `M₁.states + M₂.start` for every
possible current tape symbol.

The composed machine's halting states are exactly `M₂`'s halting
states (shifted): `M₁`'s halting bits become `false` everywhere, since
we no longer want to stop in `M₁` — `exit` now leads into `M₂`.
-/

/-- The "bridge" transitions: from state `srcState` for any tape-0
symbol (including `none`), move to state `dstState` without writing
or moving. Used to hand off control between two composed TMs.

`sig` here is the alphabet size: we enumerate `[0, sig)` plus `none`.
The write field is `[none]` everywhere, meaning the tape is never
modified by the bridge — only the state index changes. -/
def bridgeEntries (sig : Nat) (srcState dstState : Nat) :
    List FlatTMTransEntry :=
  let mk (v : Option Nat) : FlatTMTransEntry :=
    { src_state := srcState
      src_tape_vals := [v]
      dst_state := dstState
      dst_write_vals := [none]
      move_dirs := [TMMove.Nmove] }
  mk none :: (List.range sig).map (fun v => mk (some v))

/-- Shift a single transition entry by adding `offset` to its source
and destination state indices. -/
def shiftEntry (offset : Nat) (entry : FlatTMTransEntry) : FlatTMTransEntry :=
  { entry with
    src_state := entry.src_state + offset
    dst_state := entry.dst_state + offset }

/-- The halt-state vector of the composed machine: `M₁`'s halt bits
are all turned off (we don't stop in `M₁` anymore — `exit` leads into
`M₂`), then `M₂`'s halt vector is appended. -/
def composedHalt (M₁ M₂ : FlatTM) : List Bool :=
  List.replicate M₁.states false ++ M₂.halt

/-- Sequential composition of single-tape FlatTMs `M₁` and `M₂` with
exit state `exit`. -/
def composeFlatTM (M₁ M₂ : FlatTM) (exit : Nat) : FlatTM where
  sig := max M₁.sig M₂.sig
  tapes := M₁.tapes
  states := M₁.states + M₂.states
  trans :=
    bridgeEntries (max M₁.sig M₂.sig) exit (M₁.states + M₂.start) ++
    M₁.trans ++
    M₂.trans.map (shiftEntry M₁.states)
  start := M₁.start
  halt := composedHalt M₁ M₂

/-! ### Basic length / membership lemmas about composed machines -/

theorem composeFlatTM_states (M₁ M₂ : FlatTM) (exit : Nat) :
    (composeFlatTM M₁ M₂ exit).states = M₁.states + M₂.states := rfl

theorem composeFlatTM_start (M₁ M₂ : FlatTM) (exit : Nat) :
    (composeFlatTM M₁ M₂ exit).start = M₁.start := rfl

theorem composeFlatTM_tapes (M₁ M₂ : FlatTM) (exit : Nat) :
    (composeFlatTM M₁ M₂ exit).tapes = M₁.tapes := rfl

theorem composeFlatTM_sig (M₁ M₂ : FlatTM) (exit : Nat) :
    (composeFlatTM M₁ M₂ exit).sig = max M₁.sig M₂.sig := rfl

theorem composedHalt_length (M₁ M₂ : FlatTM) :
    (composedHalt M₁ M₂).length = M₁.states + M₂.halt.length := by
  show (List.replicate M₁.states false ++ M₂.halt).length = M₁.states + M₂.halt.length
  rw [List.length_append, List.length_replicate]

theorem composeFlatTM_halt_length (M₁ M₂ : FlatTM) (exit : Nat)
    (h₂ : validFlatTM M₂) :
    (composeFlatTM M₁ M₂ exit).halt.length = (composeFlatTM M₁ M₂ exit).states := by
  rw [composeFlatTM_states]
  show (composedHalt M₁ M₂).length = M₁.states + M₂.states
  rw [composedHalt_length, h₂.2.1]

/-! ### Validity of `composeFlatTM`

For the composed machine to satisfy `validFlatTM`, we need:
- `start < states`: inherited from M₁.
- `halt.length = states`: by `composeFlatTM_halt_length`.
- every transition is well-formed in the composed machine.

The third splits across three buckets: bridge transitions, M₁'s
original transitions (unmodified), and M₂'s shifted transitions. -/

/-- Every entry produced by `bridgeEntries` has source state
`srcState`, destination state `dstState`, and a single tape-symbol
slot that is either `none` or `some v` with `v < sig`. -/
theorem bridgeEntries_mem {sig srcState dstState : Nat} {e : FlatTMTransEntry}
    (h : e ∈ bridgeEntries sig srcState dstState) :
    e.src_state = srcState ∧ e.dst_state = dstState ∧
      e.src_tape_vals.length = 1 ∧ e.dst_write_vals.length = 1 ∧
      e.move_dirs.length = 1 ∧
      flatTMOptionSymbolsBounded sig e.src_tape_vals ∧
      flatTMOptionSymbolsBounded sig e.dst_write_vals := by
  unfold bridgeEntries at h
  -- h : e ∈ mk none :: (List.range sig).map (fun v => mk (some v))
  rcases List.mem_cons.mp h with h | h
  · -- e = mk none
    subst h
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx
      simp at hx
      subst hx
      trivial
    · intro x hx
      simp at hx
      subst hx
      trivial
  · rcases List.mem_map.mp h with ⟨v, hv, hmk⟩
    subst hmk
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx
      simp at hx
      subst hx
      exact List.mem_range.mp hv
    · intro x hx
      simp at hx
      subst hx
      trivial

/-- Validity bookkeeping for the composed machine.

Assumes both machines are valid, the exit state is a state of `M₁`,
and both machines are single-tape (this is our standing convention). -/
theorem composeFlatTM_valid (M₁ M₂ : FlatTM) (exit : Nat)
    (h₁ : validFlatTM M₁) (h₂ : validFlatTM M₂)
    (h_exit : exit < M₁.states)
    (h_t1 : M₁.tapes = 1) (h_t2 : M₂.tapes = 1) :
    validFlatTM (composeFlatTM M₁ M₂ exit) := by
  obtain ⟨h₁_start, h₁_halt, h₁_trans⟩ := h₁
  obtain ⟨h₂_start, h₂_halt, h₂_trans⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · -- start < states
    show M₁.start < M₁.states + M₂.states
    exact Nat.lt_of_lt_of_le h₁_start (Nat.le_add_right _ _)
  · -- halt.length = states
    show (composedHalt M₁ M₂).length = M₁.states + M₂.states
    rw [composedHalt_length, h₂_halt]
  · -- every transition is valid
    intro entry hentry
    -- entry is in bridge ++ M₁.trans ++ M₂.trans.map shift
    show flatTMTransEntryValid (composeFlatTM M₁ M₂ exit) entry
    have hsig_eq : (composeFlatTM M₁ M₂ exit).sig = max M₁.sig M₂.sig := rfl
    have hstates_eq : (composeFlatTM M₁ M₂ exit).states = M₁.states + M₂.states := rfl
    have htapes_eq : (composeFlatTM M₁ M₂ exit).tapes = M₁.tapes := rfl
    -- decompose membership
    have hentry' : entry ∈
        bridgeEntries (max M₁.sig M₂.sig) exit (M₁.states + M₂.start) ++
        M₁.trans ++
        M₂.trans.map (shiftEntry M₁.states) := hentry
    rcases List.mem_append.mp hentry' with hentry'' | hentry_m2
    · rcases List.mem_append.mp hentry'' with hentry_bridge | hentry_m1
      · -- bridge transition
        obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ :=
          bridgeEntries_mem hentry_bridge
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hsrc, hstates_eq]
          exact Nat.lt_of_lt_of_le h_exit (Nat.le_add_right _ _)
        · rw [hdst, hstates_eq]
          exact Nat.add_lt_add_left h₂_start M₁.states
        · rw [hsrcLen, htapes_eq, h_t1]
        · rw [hdstLen, htapes_eq, h_t1]
        · rw [hmovLen, htapes_eq, h_t1]
        · rw [hsig_eq]; exact hsymSrc
        · rw [hsig_eq]; exact hsymDst
      · -- original M₁ transition
        have hVal := h₁_trans entry hentry_m1
        obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ := hVal
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hstates_eq]
          exact Nat.lt_of_lt_of_le hsrc (Nat.le_add_right _ _)
        · rw [hstates_eq]
          exact Nat.lt_of_lt_of_le hdst (Nat.le_add_right _ _)
        · rw [htapes_eq]; exact hsrcLen
        · rw [htapes_eq]; exact hdstLen
        · rw [htapes_eq]; exact hmovLen
        · rw [hsig_eq]
          intro x hx
          have hbound : ∀ y, y < M₁.sig → y < max M₁.sig M₂.sig := fun y hy =>
            Nat.lt_of_lt_of_le hy (Nat.le_max_left _ _)
          cases x with
          | none => trivial
          | some v =>
              exact hbound v (hsymSrc (some v) hx)
        · rw [hsig_eq]
          intro x hx
          have hbound : ∀ y, y < M₁.sig → y < max M₁.sig M₂.sig := fun y hy =>
            Nat.lt_of_lt_of_le hy (Nat.le_max_left _ _)
          cases x with
          | none => trivial
          | some v =>
              exact hbound v (hsymDst (some v) hx)
    · -- shifted M₂ transition
      rcases List.mem_map.mp hentry_m2 with ⟨entry₀, hentry₀, hshift⟩
      subst hshift
      have hVal := h₂_trans entry₀ hentry₀
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ := hVal
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- (entry₀.src_state + M₁.states) < M₁.states + M₂.states
        show entry₀.src_state + M₁.states < M₁.states + M₂.states
        rw [Nat.add_comm entry₀.src_state M₁.states]
        exact Nat.add_lt_add_left hsrc M₁.states
      · show entry₀.dst_state + M₁.states < M₁.states + M₂.states
        rw [Nat.add_comm entry₀.dst_state M₁.states]
        exact Nat.add_lt_add_left hdst M₁.states
      · rw [htapes_eq, h_t1, ← h_t2]; exact hsrcLen
      · rw [htapes_eq, h_t1, ← h_t2]; exact hdstLen
      · rw [htapes_eq, h_t1, ← h_t2]; exact hmovLen
      · rw [hsig_eq]
        intro x hx
        have hbound : ∀ y, y < M₂.sig → y < max M₁.sig M₂.sig := fun y hy =>
          Nat.lt_of_lt_of_le hy (Nat.le_max_right _ _)
        cases x with
        | none => trivial
        | some v =>
            exact hbound v (hsymSrc (some v) hx)
      · rw [hsig_eq]
        intro x hx
        have hbound : ∀ y, y < M₂.sig → y < max M₁.sig M₂.sig := fun y hy =>
          Nat.lt_of_lt_of_le hy (Nat.le_max_right _ _)
        cases x with
        | none => trivial
        | some v =>
            exact hbound v (hsymDst (some v) hx)

/-! ## Step 11.0 — Operational correctness of `composeFlatTM`

`composeFlatTM_valid` (above) shows the composed machine is structurally
well-formed. This section adds the operational correctness lemma
`composeFlatTM_run`: if `M₁` halts at state `exit` in `t₁` steps
(without halting prematurely), and `M₂` then halts at some `c₂` in
`t₂` steps starting from `c₁.tapes`, then `composeFlatTM M₁ M₂ exit`
halts at the shifted `c₂` in `t₁ + 1 + t₂` steps.

The proof factors into seven small lemmas. -/

/-! ### Halt-bit lemmas -/

/-- On any M₁-state, the composed machine's halt-bit is `false`. -/
private theorem composeFlatTM_haltingStateReached_M1
    (M₁ M₂ : FlatTM) (exit : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx < M₁.states) :
    haltingStateReached (composeFlatTM M₁ M₂ exit) cfg = false := by
  show (composeFlatTM M₁ M₂ exit).halt.getD cfg.state_idx false = false
  show (composedHalt M₁ M₂).getD cfg.state_idx false = false
  show ((List.replicate M₁.states false ++ M₂.halt).getD cfg.state_idx false) = false
  rw [List.getD_append _ _ _ _ (by rw [List.length_replicate]; exact h)]
  exact List.getD_replicate false h

/-- On a shifted M₂-state `s + M₁.states`, the composed machine's
halt-bit equals `M₂`'s halt-bit at `s`. -/
private theorem composeFlatTM_haltingStateReached_M2
    (M₁ M₂ : FlatTM) (exit : Nat) (s : Nat) (tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (composeFlatTM M₁ M₂ exit)
        { state_idx := s + M₁.states, tapes := tapes } =
      haltingStateReached M₂ { state_idx := s, tapes := tapes } := by
  show (composeFlatTM M₁ M₂ exit).halt.getD (s + M₁.states) false =
       M₂.halt.getD s false
  show (composedHalt M₁ M₂).getD (s + M₁.states) false = _
  show ((List.replicate M₁.states false ++ M₂.halt).getD (s + M₁.states) false) = _
  rw [List.getD_append_right _ _ _ _ (by rw [List.length_replicate]; exact Nat.le_add_left _ _)]
  rw [List.length_replicate]
  show M₂.halt.getD (s + M₁.states - M₁.states) false = _
  rw [Nat.add_sub_cancel]

/-! ### M₁-phase step lemma -/

/-- Every bridge entry has `src_state = exit`. -/
private theorem bridgeEntries_src_state
    {sig srcState dstState : Nat} {e : FlatTMTransEntry}
    (h : e ∈ bridgeEntries sig srcState dstState) :
    e.src_state = srcState :=
  (bridgeEntries_mem h).1

/-- Every shifted M₂ entry has `src_state ≥ off`. -/
private theorem shiftEntry_src_state_ge
    (off : Nat) (e : FlatTMTransEntry) :
    (shiftEntry off e).src_state = e.src_state + off := rfl

/-- An entry whose `src_state` differs from `cfg.state_idx` does NOT
match `cfg`. (Note: uses the `_iff` characterisation defined below
under "Bridge step lemma".) -/
private theorem entryMatchesConfig_ne_true_of_state_ne
    {entry : FlatTMTransEntry} {cfg : FlatTMConfig}
    (h : entry.src_state ≠ cfg.state_idx) :
    ¬ entryMatchesConfig entry cfg = true := by
  intro heq
  apply h
  unfold entryMatchesConfig at heq
  rw [Bool.and_eq_true] at heq
  exact LawfulBEq.eq_of_beq heq.1

/-- On any cfg with state_idx ≠ exit, the bridge entries do not match. -/
private theorem bridgeEntries_find_eq_none
    {sig srcState dstState : Nat} {cfg : FlatTMConfig}
    (h : cfg.state_idx ≠ srcState) :
    (bridgeEntries sig srcState dstState).find?
        (fun e => entryMatchesConfig e cfg) = none := by
  rw [List.find?_eq_none]
  intro e he
  refine entryMatchesConfig_ne_true_of_state_ne ?_
  rw [bridgeEntries_src_state he]
  exact fun h' => h h'.symm

/-- On any cfg with state_idx < threshold, the shifted M₂ entries do
not match (because each has src_state ≥ threshold). -/
private theorem shiftEntries_find_eq_none
    (M₂ : FlatTM) (off : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx < off) :
    (M₂.trans.map (shiftEntry off)).find?
        (fun e => entryMatchesConfig e cfg) = none := by
  rw [List.find?_eq_none]
  intro e' he'
  rcases List.mem_map.mp he' with ⟨e, _, hshift⟩
  subst hshift
  refine entryMatchesConfig_ne_true_of_state_ne ?_
  rw [shiftEntry_src_state_ge]
  intro h_eq
  have h_lt : cfg.state_idx < e.src_state + off :=
    Nat.lt_of_lt_of_le h (Nat.le_add_left _ _)
  exact absurd h_eq (Nat.ne_of_lt h_lt).symm

/-- M₁-phase step: on a cfg in `M₁`'s state range and not equal to
`exit`, one composed step coincides with `M₁`'s one step. -/
private theorem stepFlatTM_composeFlatTM_M1
    (M₁ M₂ : FlatTM) (exit : Nat) (cfg : FlatTMConfig)
    (h_state_lt : cfg.state_idx < M₁.states)
    (h_state_ne : cfg.state_idx ≠ exit) :
    stepFlatTM (composeFlatTM M₁ M₂ exit) cfg = stepFlatTM M₁ cfg := by
  show ((composeFlatTM M₁ M₂ exit).trans.find?
          (fun e => entryMatchesConfig e cfg)).bind
        (applyTransitionEntry cfg) =
       (M₁.trans.find? (fun e => entryMatchesConfig e cfg)).bind
        (applyTransitionEntry cfg)
  have h_trans :
      (composeFlatTM M₁ M₂ exit).trans =
        bridgeEntries (max M₁.sig M₂.sig) exit (M₁.states + M₂.start) ++
        M₁.trans ++
        M₂.trans.map (shiftEntry M₁.states) := rfl
  rw [h_trans]
  rw [List.find?_append, List.find?_append]
  have h_bridge :
      (bridgeEntries (max M₁.sig M₂.sig) exit (M₁.states + M₂.start)).find?
          (fun e => entryMatchesConfig e cfg) = none :=
    bridgeEntries_find_eq_none h_state_ne
  have h_shifted :
      (M₂.trans.map (shiftEntry M₁.states)).find?
          (fun e => entryMatchesConfig e cfg) = none :=
    shiftEntries_find_eq_none M₂ M₁.states cfg h_state_lt
  rw [h_bridge, h_shifted, Option.none_or]
  -- Goal: ((M₁.trans.find? pred).or none).bind ... = (M₁.trans.find? pred).bind ...
  cases hF : M₁.trans.find? (fun e => entryMatchesConfig e cfg) with
  | none => rfl
  | some e => rfl

/-! ### Bridge step lemma -/

/-- Characterisation of `entryMatchesConfig`. -/
private theorem entryMatchesConfig_iff
    (entry : FlatTMTransEntry) (cfg : FlatTMConfig) :
    entryMatchesConfig entry cfg = true ↔
      entry.src_state = cfg.state_idx ∧
      entry.src_tape_vals = cfg.tapes.map currentTapeSymbol := by
  unfold entryMatchesConfig
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact LawfulBEq.eq_of_beq h1
    · exact of_decide_eq_true h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h1]; exact beq_self_eq_true _
    · exact decide_eq_true h2

/-- A positive matching helper: if the entry's source state and tape
values literally equal those of the config, the entry matches. -/
private theorem entryMatchesConfig_true_of
    {entry : FlatTMTransEntry} {cfg : FlatTMConfig}
    (h_state : entry.src_state = cfg.state_idx)
    (h_tape : entry.src_tape_vals = cfg.tapes.map currentTapeSymbol) :
    entryMatchesConfig entry cfg = true :=
  (entryMatchesConfig_iff entry cfg).mpr ⟨h_state, h_tape⟩

/-- Negative matching helper for tape mismatch. -/
private theorem entryMatchesConfig_ne_true_of_tape_ne
    {entry : FlatTMTransEntry} {cfg : FlatTMConfig}
    (h_tape : entry.src_tape_vals ≠ cfg.tapes.map currentTapeSymbol) :
    ¬ entryMatchesConfig entry cfg = true :=
  fun h => h_tape ((entryMatchesConfig_iff _ _).mp h).2

/-- The bridge entry whose `src_tape_vals = [sym]`. -/
private def bridgeMkEntry (srcState dstState : Nat) (sym : Option Nat) :
    FlatTMTransEntry :=
  { src_state := srcState, src_tape_vals := [sym],
    dst_state := dstState, dst_write_vals := [none],
    move_dirs := [TMMove.Nmove] }

/-- `bridgeEntries` factored through `bridgeMkEntry`. -/
private theorem bridgeEntries_eq_bridgeMkEntry (sig srcState dstState : Nat) :
    bridgeEntries sig srcState dstState =
      bridgeMkEntry srcState dstState none ::
        (List.range sig).map (fun v => bridgeMkEntry srcState dstState (some v)) := rfl

/-- Walk a `(range max_sig).map (fun w => bridgeMkEntry ... (some w))` list
to find the matching entry for `sym = some v` with `v < max_sig`. -/
private theorem find_bridgeRange_some
    (max_sig srcState dstState v : Nat) (h_v : v < max_sig)
    (cfg : FlatTMConfig)
    (h_state : cfg.state_idx = srcState)
    (h_tape : cfg.tapes.map currentTapeSymbol = [some v]) :
    ((List.range max_sig).map
        (fun w => bridgeMkEntry srcState dstState (some w))).find?
        (fun e => entryMatchesConfig e cfg) =
      some (bridgeMkEntry srcState dstState (some v)) := by
  have h_mem : v ∈ List.range max_sig := List.mem_range.mpr h_v
  -- For each candidate w, matching iff w = v.
  have h_match_iff : ∀ w,
      entryMatchesConfig (bridgeMkEntry srcState dstState (some w)) cfg = true ↔ w = v := by
    intro w
    rw [entryMatchesConfig_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, h_tape_eq⟩
      have h_eq : ([some w] : List (Option Nat)) = [some v] :=
        Eq.trans h_tape_eq h_tape
      injection h_eq with h_head _
      exact Option.some.inj h_head
    · intro h_eq
      rw [h_eq]
      refine ⟨h_state.symm, ?_⟩
      show ([some v] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol
      exact h_tape.symm
  -- Now walk: by induction on the list.
  suffices h_walk : ∀ (L : List Nat), v ∈ L →
      (L.map (fun w => bridgeMkEntry srcState dstState (some w))).find?
          (fun e => entryMatchesConfig e cfg) =
        some (bridgeMkEntry srcState dstState (some v)) from
    h_walk _ h_mem
  intro L hL
  induction L with
  | nil => cases hL
  | cons w ws ih =>
      have h_target_eq :
          (((w :: ws).map (fun w => bridgeMkEntry srcState dstState (some w)))).find?
            (fun e => entryMatchesConfig e cfg) =
          ((bridgeMkEntry srcState dstState (some w)) ::
            (ws.map (fun w => bridgeMkEntry srcState dstState (some w)))).find?
              (fun e => entryMatchesConfig e cfg) := rfl
      rw [h_target_eq]
      by_cases hwv : w = v
      · subst hwv
        have h_match : entryMatchesConfig
            (bridgeMkEntry srcState dstState (some w)) cfg = true :=
          (h_match_iff w).mpr rfl
        exact List.find?_cons_of_pos h_match
      · have h_no_match : ¬ entryMatchesConfig
            (bridgeMkEntry srcState dstState (some w)) cfg = true := by
          intro h; exact hwv ((h_match_iff w).mp h)
        have h_step :
            ((bridgeMkEntry srcState dstState (some w)) ::
              (ws.map (fun w => bridgeMkEntry srcState dstState (some w)))).find?
                (fun e => entryMatchesConfig e cfg) =
            (ws.map (fun w => bridgeMkEntry srcState dstState (some w))).find?
                (fun e => entryMatchesConfig e cfg) :=
          List.find?_cons_of_neg h_no_match
        rw [h_step]
        rcases List.mem_cons.mp hL with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws

/-- Applying any bridge entry to a single-tape configuration with
matching state index returns the bridge's destination state and an
unchanged tape (since the bridge writes `none` and moves `Nmove`). -/
private theorem applyBridgeMkEntry_singleTape
    (srcState dstState : Nat) (sym : Option Nat)
    (left right : List Nat) (head : Nat) :
    applyTransitionEntry
        { state_idx := srcState, tapes := [(left, head, right)] }
        (bridgeMkEntry srcState dstState sym) =
      some { state_idx := dstState, tapes := [(left, head, right)] } := rfl

/-- Bridge step: at state `exit` with a single-tape cfg, one composed
step jumps to `M₁.states + M₂.start` without modifying the tape. -/
private theorem stepFlatTM_composeFlatTM_bridge
    (M₁ M₂ : FlatTM) (exit : Nat)
    (left right : List Nat) (head : Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left, head, right) = some v →
                          v < max M₁.sig M₂.sig) :
    stepFlatTM (composeFlatTM M₁ M₂ exit)
        { state_idx := exit, tapes := [(left, head, right)] } =
      some { state_idx := M₁.states + M₂.start,
             tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := exit, tapes := [(left, head, right)] } with hcfg
  show ((composeFlatTM M₁ M₂ exit).trans.find?
          (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) = _
  have h_trans :
      (composeFlatTM M₁ M₂ exit).trans =
        bridgeEntries (max M₁.sig M₂.sig) exit (M₁.states + M₂.start) ++
        M₁.trans ++ M₂.trans.map (shiftEntry M₁.states) := rfl
  rw [h_trans, List.find?_append, List.find?_append]
  have h_tape_map :
      cfg.tapes.map currentTapeSymbol = [currentTapeSymbol (left, head, right)] := rfl
  have h_cfg_state : cfg.state_idx = exit := rfl
  rw [bridgeEntries_eq_bridgeMkEntry]
  -- The bridge find? returns either `mk none` (when sym = none) or `mk (some v)`
  -- (when sym = some v with v < max_sig). In both cases applying the entry gives
  -- the desired result. We extract the find? result and then apply.
  suffices h_bridge_find :
      ((bridgeMkEntry exit (M₁.states + M₂.start) none ::
          (List.range (max M₁.sig M₂.sig)).map
            (fun w => bridgeMkEntry exit (M₁.states + M₂.start) (some w))).find?
          (fun e => entryMatchesConfig e cfg)) =
        some (bridgeMkEntry exit (M₁.states + M₂.start)
          (currentTapeSymbol (left, head, right))) by
    rw [h_bridge_find]
    show ((some _).or _ |>.or _).bind _ = _
    simp only [Option.some_or]
    exact applyBridgeMkEntry_singleTape exit (M₁.states + M₂.start)
      (currentTapeSymbol (left, head, right)) left right head
  cases h_sym : currentTapeSymbol (left, head, right) with
  | none =>
      have h_match :
          entryMatchesConfig
            (bridgeMkEntry exit (M₁.states + M₂.start) none) cfg = true := by
        refine entryMatchesConfig_true_of rfl ?_
        show ([none] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol
        rw [h_tape_map, h_sym]
      exact List.find?_cons_of_pos h_match
  | some v =>
      have h_no_match : ¬ entryMatchesConfig
          (bridgeMkEntry exit (M₁.states + M₂.start) none) cfg = true := by
        intro h
        have h_tape_eq := ((entryMatchesConfig_iff _ _).mp h).2
        have h_eq : ([none] : List (Option Nat)) = [some v] := by
          calc ([none] : List (Option Nat))
              = (bridgeMkEntry exit (M₁.states + M₂.start) none).src_tape_vals := rfl
            _ = cfg.tapes.map currentTapeSymbol := h_tape_eq
            _ = [currentTapeSymbol (left, head, right)] := h_tape_map
            _ = [some v] := by rw [h_sym]
        injection h_eq with h1 _
        cases h1
      have h_step :
          ((bridgeMkEntry exit (M₁.states + M₂.start) none) ::
            (List.range (max M₁.sig M₂.sig)).map
              (fun w => bridgeMkEntry exit (M₁.states + M₂.start) (some w))).find?
              (fun e => entryMatchesConfig e cfg) =
          ((List.range (max M₁.sig M₂.sig)).map
              (fun w => bridgeMkEntry exit (M₁.states + M₂.start) (some w))).find?
              (fun e => entryMatchesConfig e cfg) :=
        List.find?_cons_of_neg h_no_match
      rw [h_step]
      have h_v_lt : v < max M₁.sig M₂.sig := h_sym_bound v h_sym
      exact find_bridgeRange_some (max M₁.sig M₂.sig) exit (M₁.states + M₂.start) v
        h_v_lt cfg h_cfg_state (by rw [h_tape_map, h_sym])

/-- **Generic bridge step.** If a machine's transition table begins with
`bridgeEntries M.sig srcState dstState`, then one step from `srcState` (with an
in-range head symbol, single tape) jumps to `dstState` leaving the tape
unchanged. `stepFlatTM_composeFlatTM_bridge` is the `composeFlatTM` instance;
this generic form also serves `joinTwoHalts` (whose `trans` is
`bridgeEntries sig h2 h1 ++ M.trans`). -/
theorem stepFlatTM_bridge_prefix
    (M : FlatTM) (srcState dstState : Nat) (rest : List FlatTMTransEntry)
    (htrans : M.trans = bridgeEntries M.sig srcState dstState ++ rest)
    (left right : List Nat) (head : Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left, head, right) = some v → v < M.sig) :
    stepFlatTM M { state_idx := srcState, tapes := [(left, head, right)] } =
      some { state_idx := dstState, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := srcState, tapes := [(left, head, right)] } with hcfg
  show (M.trans.find? (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) = _
  rw [htrans, List.find?_append]
  have h_tape_map : cfg.tapes.map currentTapeSymbol = [currentTapeSymbol (left, head, right)] := rfl
  have h_cfg_state : cfg.state_idx = srcState := rfl
  rw [bridgeEntries_eq_bridgeMkEntry]
  suffices h_bridge_find :
      ((bridgeMkEntry srcState dstState none ::
          (List.range M.sig).map (fun w => bridgeMkEntry srcState dstState (some w))).find?
          (fun e => entryMatchesConfig e cfg)) =
        some (bridgeMkEntry srcState dstState (currentTapeSymbol (left, head, right))) by
    rw [h_bridge_find]
    show ((some _).or _).bind _ = _
    simp only [Option.some_or]
    exact applyBridgeMkEntry_singleTape srcState dstState
      (currentTapeSymbol (left, head, right)) left right head
  cases h_sym : currentTapeSymbol (left, head, right) with
  | none =>
      have h_match : entryMatchesConfig (bridgeMkEntry srcState dstState none) cfg = true := by
        refine entryMatchesConfig_true_of rfl ?_
        show ([none] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol
        rw [h_tape_map, h_sym]
      exact List.find?_cons_of_pos h_match
  | some v =>
      have h_no_match : ¬ entryMatchesConfig (bridgeMkEntry srcState dstState none) cfg = true := by
        intro h
        have h_tape_eq := ((entryMatchesConfig_iff _ _).mp h).2
        have h_eq : ([none] : List (Option Nat)) = [some v] := by
          calc ([none] : List (Option Nat))
              = (bridgeMkEntry srcState dstState none).src_tape_vals := rfl
            _ = cfg.tapes.map currentTapeSymbol := h_tape_eq
            _ = [currentTapeSymbol (left, head, right)] := h_tape_map
            _ = [some v] := by rw [h_sym]
        injection h_eq with h1 _
        cases h1
      have h_step :
          ((bridgeMkEntry srcState dstState none ::
            (List.range M.sig).map (fun w => bridgeMkEntry srcState dstState (some w))).find?
              (fun e => entryMatchesConfig e cfg)) =
          ((List.range M.sig).map (fun w => bridgeMkEntry srcState dstState (some w))).find?
              (fun e => entryMatchesConfig e cfg) :=
        List.find?_cons_of_neg h_no_match
      rw [h_step]
      have h_v_lt : v < M.sig := h_sym_bound v h_sym
      exact find_bridgeRange_some M.sig srcState dstState v
        h_v_lt cfg h_cfg_state (by rw [h_tape_map, h_sym])

/-! ### M₂-phase step lemma -/

/-- Shifted M₂ entry's apply on a config equals the unshifted entry's
apply on the unshifted config, with the destination state shifted by
`M₁.states`. -/
private theorem applyTransitionEntry_shiftEntry
    (M₁_states : Nat) (entry : FlatTMTransEntry) (cfg : FlatTMConfig) :
    applyTransitionEntry cfg (shiftEntry M₁_states entry) =
      (applyTransitionEntry { state_idx := cfg.state_idx - M₁_states,
                              tapes := cfg.tapes } entry).map
        (fun c => { state_idx := c.state_idx + M₁_states, tapes := c.tapes }) := by
  show applyTransitionEntry cfg
        { entry with src_state := entry.src_state + M₁_states,
                     dst_state := entry.dst_state + M₁_states } =
      _
  by_cases h : cfg.tapes.length = entry.dst_write_vals.length ∧
               cfg.tapes.length = entry.move_dirs.length
  · -- Length check passes for both versions (lengths only depend on entry).
    show (if _ : cfg.tapes.length = entry.dst_write_vals.length ∧
                 cfg.tapes.length = entry.move_dirs.length then _ else none) = _
    rw [dif_pos h]
    show (some _ : Option FlatTMConfig) = _
    have h_inner :
        applyTransitionEntry { state_idx := cfg.state_idx - M₁_states,
                               tapes := cfg.tapes } entry =
          some { state_idx := entry.dst_state,
                 tapes := List.zipWith (fun tape payload =>
                   tapeStep tape payload.1 payload.2) cfg.tapes
                   (List.zip entry.dst_write_vals entry.move_dirs) } := by
      show (if _ : cfg.tapes.length = entry.dst_write_vals.length ∧
                   cfg.tapes.length = entry.move_dirs.length then _ else none) = _
      rw [dif_pos h]
    rw [h_inner]
    rfl
  · -- Length check fails on both sides.
    show (if _ : cfg.tapes.length = entry.dst_write_vals.length ∧
                 cfg.tapes.length = entry.move_dirs.length then _ else none) = _
    rw [dif_neg h]
    have h_inner :
        applyTransitionEntry { state_idx := cfg.state_idx - M₁_states,
                               tapes := cfg.tapes } entry = none := by
      show (if _ : cfg.tapes.length = entry.dst_write_vals.length ∧
                   cfg.tapes.length = entry.move_dirs.length then _ else none) = _
      rw [dif_neg h]
    rw [h_inner]
    rfl

/-- M₂-phase step: on a shifted M₂-state `s + M₁.states`, one composed
step coincides with `M₂`'s one step at the unshifted state `s`, with
the result state shifted by `M₁.states`. -/
private theorem stepFlatTM_composeFlatTM_M2
    (M₁ M₂ : FlatTM) (exit : Nat) (s : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (h_validM1 : validFlatTM M₁)
    (h_exit_lt : exit < M₁.states) :
    stepFlatTM (composeFlatTM M₁ M₂ exit)
        { state_idx := s + M₁.states, tapes := tapes } =
      (stepFlatTM M₂ { state_idx := s, tapes := tapes }).map
        (fun c => { state_idx := c.state_idx + M₁.states, tapes := c.tapes }) := by
  set cfg : FlatTMConfig := { state_idx := s + M₁.states, tapes := tapes } with hcfg
  set cfg2 : FlatTMConfig := { state_idx := s, tapes := tapes } with hcfg2
  show ((composeFlatTM M₁ M₂ exit).trans.find?
          (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) =
       ((M₂.trans.find?
          (fun e => entryMatchesConfig e cfg2)).bind (applyTransitionEntry cfg2)).map _
  have h_trans :
      (composeFlatTM M₁ M₂ exit).trans =
        bridgeEntries (max M₁.sig M₂.sig) exit (M₁.states + M₂.start) ++
        M₁.trans ++ M₂.trans.map (shiftEntry M₁.states) := rfl
  rw [h_trans, List.find?_append, List.find?_append]
  -- Bridge: src = exit < M₁.states ≤ s + M₁.states = cfg.state_idx, so doesn't match.
  have h_bridge_none :
      (bridgeEntries (max M₁.sig M₂.sig) exit (M₁.states + M₂.start)).find?
          (fun e => entryMatchesConfig e cfg) = none := by
    refine bridgeEntries_find_eq_none ?_
    show cfg.state_idx ≠ exit
    show s + M₁.states ≠ exit
    intro h_eq
    have h_lt : exit < s + M₁.states :=
      Nat.lt_of_lt_of_le h_exit_lt (Nat.le_add_left _ _)
    exact absurd h_eq.symm (Nat.ne_of_lt h_lt)
  -- M₁.trans: src < M₁.states ≤ cfg.state_idx, so doesn't match.
  have h_M1_none :
      M₁.trans.find? (fun e => entryMatchesConfig e cfg) = none := by
    rw [List.find?_eq_none]
    intro e he
    refine entryMatchesConfig_ne_true_of_state_ne ?_
    have h_src_lt : e.src_state < M₁.states := (h_validM1.2.2 e he).1
    show e.src_state ≠ cfg.state_idx
    show e.src_state ≠ s + M₁.states
    intro h_eq
    have h_lt' : e.src_state < s + M₁.states :=
      Nat.lt_of_lt_of_le h_src_lt (Nat.le_add_left _ _)
    exact absurd h_eq (Nat.ne_of_lt h_lt')
  rw [h_bridge_none, h_M1_none, Option.none_or, Option.none_or]
  -- Shifted M₂: rewrite via List.find?_map.
  rw [List.find?_map]
  -- Beta-reduce the composition `(fun e => entryMatchesConfig e cfg) ∘ shiftEntry M₁.states`
  -- into `fun e => entryMatchesConfig (shiftEntry M₁.states e) cfg`.
  show (Option.map (shiftEntry M₁.states)
          (M₂.trans.find?
            (fun e => entryMatchesConfig (shiftEntry M₁.states e) cfg))).bind
      (applyTransitionEntry cfg) =
       ((M₂.trans.find? (fun e => entryMatchesConfig e cfg2)).bind
          (applyTransitionEntry cfg2)).map _
  -- Predicate equivalence: matching the shifted entry against cfg = matching against cfg2.
  have h_pred_eq :
      (fun e => entryMatchesConfig (shiftEntry M₁.states e) cfg) =
      (fun e => entryMatchesConfig e cfg2) := by
    funext e
    by_cases h_match : entryMatchesConfig e cfg2 = true
    · have ⟨h_state2, h_tape2⟩ := (entryMatchesConfig_iff _ _).mp h_match
      have h_match_shifted : entryMatchesConfig (shiftEntry M₁.states e) cfg = true := by
        refine entryMatchesConfig_true_of ?_ h_tape2
        show e.src_state + M₁.states = s + M₁.states
        rw [h_state2]
      rw [h_match_shifted, h_match]
    · have h_match_neg : entryMatchesConfig e cfg2 = false := by
        cases h : entryMatchesConfig e cfg2 with
        | true => exact absurd h h_match
        | false => rfl
      have h_match_shifted_neg :
          entryMatchesConfig (shiftEntry M₁.states e) cfg = false := by
        cases h : entryMatchesConfig (shiftEntry M₁.states e) cfg with
        | true =>
            have ⟨h_state, h_tape⟩ := (entryMatchesConfig_iff _ _).mp h
            have h_state_eq : e.src_state + M₁.states = s + M₁.states := h_state
            have h_src_eq : e.src_state = s := Nat.add_right_cancel h_state_eq
            have h_match_pos : entryMatchesConfig e cfg2 = true :=
              entryMatchesConfig_true_of h_src_eq h_tape
            rw [h_match_pos] at h_match_neg
            cases h_match_neg
        | false => rfl
      rw [h_match_shifted_neg, h_match_neg]
  rw [h_pred_eq]
  cases hF : M₂.trans.find? (fun e => entryMatchesConfig e cfg2) with
  | none => rfl
  | some e =>
      show (some (shiftEntry M₁.states e)).bind (applyTransitionEntry cfg) =
        Option.map _ ((some e).bind (applyTransitionEntry cfg2))
      show applyTransitionEntry cfg (shiftEntry M₁.states e) =
        Option.map _ (applyTransitionEntry cfg2 e)
      have h_sub : cfg.state_idx - M₁.states = cfg2.state_idx := by
        show s + M₁.states - M₁.states = s
        exact Nat.add_sub_cancel _ _
      have h_cfg_eq : { state_idx := cfg.state_idx - M₁.states, tapes := cfg.tapes } = cfg2 := by
        rw [h_sub]
      rw [applyTransitionEntry_shiftEntry, h_cfg_eq]

/-- Halt bit on a shifted M₂-state: equals M₂'s halt bit. (Re-export with
the more usable form.) -/
private theorem composeFlatTM_haltingStateReached_M2_phase
    (M₁ M₂ : FlatTM) (exit : Nat) (cfg2 : FlatTMConfig) :
    haltingStateReached (composeFlatTM M₁ M₂ exit)
        { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } =
      haltingStateReached M₂ cfg2 :=
  composeFlatTM_haltingStateReached_M2 M₁ M₂ exit cfg2.state_idx cfg2.tapes

/-! ### State-index preservation under runFlatTM -/

/-- A single step of a valid FlatTM preserves the in-range state index. -/
private theorem state_idx_lt_states_of_step
    (M : FlatTM) (h_valid : validFlatTM M) (cfg cfg' : FlatTMConfig)
    (h_step : stepFlatTM M cfg = some cfg') :
    cfg'.state_idx < M.states := by
  unfold stepFlatTM at h_step
  cases h_find : M.trans.find? (fun e => entryMatchesConfig e cfg) with
  | none =>
      rw [h_find] at h_step
      cases h_step
  | some entry =>
      rw [h_find] at h_step
      have h_entry_mem : entry ∈ M.trans := List.mem_of_find?_eq_some h_find
      have h_entry_valid := h_valid.2.2 entry h_entry_mem
      have h_apply : applyTransitionEntry cfg entry = some cfg' := h_step
      unfold applyTransitionEntry at h_apply
      by_cases h_lc : cfg.tapes.length = entry.dst_write_vals.length ∧
                       cfg.tapes.length = entry.move_dirs.length
      · rw [dif_pos h_lc] at h_apply
        have h_eq : ({ state_idx := entry.dst_state,
                       tapes := List.zipWith
                         (fun tape payload => tapeStep tape payload.1 payload.2) cfg.tapes
                         (List.zip entry.dst_write_vals entry.move_dirs) }
                     : FlatTMConfig) = cfg' :=
          Option.some.inj h_apply
        rw [← h_eq]
        exact h_entry_valid.2.1
      · rw [dif_neg h_lc] at h_apply
        cases h_apply

/-- A run of any length of a valid FlatTM preserves the in-range state
index. -/
private theorem state_idx_lt_states_of_run
    (M : FlatTM) (h_valid : validFlatTM M) :
    ∀ (n : Nat) (cfg cfg' : FlatTMConfig),
      cfg.state_idx < M.states →
      runFlatTM n M cfg = some cfg' →
      cfg'.state_idx < M.states
  | 0, cfg, cfg', h_lt, h_run => by
      have h_eq : cfg = cfg' := Option.some.inj h_run
      rw [← h_eq]; exact h_lt
  | n + 1, cfg, cfg', h_lt, h_run => by
      by_cases h_halt : haltingStateReached M cfg = true
      · have h_run' : runFlatTM (n + 1) M cfg = some cfg :=
          runFlatTM_of_halting M cfg (n + 1) h_halt
        rw [h_run'] at h_run
        have h_eq : cfg = cfg' := Option.some.inj h_run
        rw [← h_eq]; exact h_lt
      · cases h_step : stepFlatTM M cfg with
        | none =>
            have h_stuck : runFlatTM (n + 1) M cfg = some cfg :=
              runFlatTM_stuck M cfg
              (by cases hh : haltingStateReached M cfg with
                  | true => exact absurd hh h_halt
                  | false => rfl) h_step (n + 1)
            rw [h_stuck] at h_run
            have h_eq : cfg = cfg' := Option.some.inj h_run
            rw [← h_eq]; exact h_lt
        | some cfg'' =>
            have h_step_unfold : runFlatTM (n + 1) M cfg = runFlatTM n M cfg'' := by
              show (if haltingStateReached M cfg = true then some cfg
                    else match stepFlatTM M cfg with
                      | none => some cfg
                      | some cfg' => runFlatTM n M cfg') = _
              rw [if_neg h_halt, h_step]
            rw [h_step_unfold] at h_run
            have h_cfg''_lt : cfg''.state_idx < M.states :=
              state_idx_lt_states_of_step M h_valid cfg cfg'' h_step
            exact state_idx_lt_states_of_run M h_valid n cfg'' cfg' h_cfg''_lt h_run
  termination_by n _ _ _ _ => n

/-! ### M₁-phase run lift -/

/-- Lift M₁'s `n`-step run to the composed machine, under the
"trajectory invariant" that M₁ doesn't halt and stays out of `exit`
through the first `n - 1` steps. Both the initial cfg and the
trajectory invariant are needed to apply `stepFlatTM_composeFlatTM_M1`. -/
private theorem runFlatTM_composeFlatTM_M1_phase
    (M₁ M₂ : FlatTM) (exit : Nat) (h_validM1 : validFlatTM M₁) :
    ∀ (n : Nat) (cfg : FlatTMConfig),
      cfg.state_idx < M₁.states →
      (∀ k, k < n → ∀ ck, runFlatTM k M₁ cfg = some ck →
         ck.state_idx ≠ exit ∧
         haltingStateReached M₁ ck = false) →
      runFlatTM n (composeFlatTM M₁ M₂ exit) cfg = runFlatTM n M₁ cfg
  | 0, _, _, _ => rfl
  | n + 1, cfg, h_state_lt, h_traj => by
      -- Trajectory at k=0 gives invariants on cfg.
      have h_k0 := h_traj 0 (Nat.zero_lt_succ _) cfg rfl
      have h_state_ne_cfg : cfg.state_idx ≠ exit := h_k0.1
      have h_halt_false_cfg : haltingStateReached M₁ cfg = false := h_k0.2
      have h_halt_composed_false : haltingStateReached (composeFlatTM M₁ M₂ exit) cfg = false :=
        composeFlatTM_haltingStateReached_M1 M₁ M₂ exit cfg h_state_lt
      -- Both runs at n+1 unfold via stepFlatTM (since neither halts).
      have h_step_eq :
          stepFlatTM (composeFlatTM M₁ M₂ exit) cfg = stepFlatTM M₁ cfg :=
        stepFlatTM_composeFlatTM_M1 M₁ M₂ exit cfg h_state_lt h_state_ne_cfg
      -- Unfold runFlatTM for both sides.
      have h_unfold_M1 :
          runFlatTM (n + 1) M₁ cfg =
            match stepFlatTM M₁ cfg with
            | none => some cfg
            | some cfg' => runFlatTM n M₁ cfg' := by
        show (if haltingStateReached M₁ cfg = true then some cfg
              else match stepFlatTM M₁ cfg with
                | none => some cfg
                | some cfg' => runFlatTM n M₁ cfg') = _
        rw [if_neg (by rw [h_halt_false_cfg]; decide)]
      have h_unfold_composed :
          runFlatTM (n + 1) (composeFlatTM M₁ M₂ exit) cfg =
            match stepFlatTM (composeFlatTM M₁ M₂ exit) cfg with
            | none => some cfg
            | some cfg' => runFlatTM n (composeFlatTM M₁ M₂ exit) cfg' := by
        show (if haltingStateReached (composeFlatTM M₁ M₂ exit) cfg = true then some cfg
              else match stepFlatTM (composeFlatTM M₁ M₂ exit) cfg with
                | none => some cfg
                | some cfg' => runFlatTM n (composeFlatTM M₁ M₂ exit) cfg') = _
        rw [if_neg (by rw [h_halt_composed_false]; decide)]
      rw [h_unfold_M1, h_unfold_composed, h_step_eq]
      cases h_step : stepFlatTM M₁ cfg with
      | none => rfl
      | some cfg' =>
          -- Apply IH to cfg' with shifted trajectory.
          have h_cfg'_lt : cfg'.state_idx < M₁.states :=
            state_idx_lt_states_of_step M₁ h_validM1 cfg cfg' h_step
          have h_traj_shift : ∀ k, k < n → ∀ ck,
              runFlatTM k M₁ cfg' = some ck →
              ck.state_idx ≠ exit ∧
              haltingStateReached M₁ ck = false := by
            intro k hk ck h_run
            -- runFlatTM (k+1) M₁ cfg = runFlatTM k M₁ cfg'
            have h_chain : runFlatTM (k + 1) M₁ cfg = some ck := by
              have h_unfold :
                  runFlatTM (k + 1) M₁ cfg =
                    match stepFlatTM M₁ cfg with
                    | none => some cfg
                    | some cfg'' => runFlatTM k M₁ cfg'' := by
                show (if haltingStateReached M₁ cfg = true then some cfg
                      else match stepFlatTM M₁ cfg with
                        | none => some cfg
                        | some cfg'' => runFlatTM k M₁ cfg'') = _
                rw [if_neg (by rw [h_halt_false_cfg]; decide)]
              rw [h_unfold, h_step]; exact h_run
            exact h_traj (k + 1) (Nat.succ_lt_succ hk) ck h_chain
          exact runFlatTM_composeFlatTM_M1_phase M₁ M₂ exit h_validM1 n cfg' h_cfg'_lt
            h_traj_shift
  termination_by n _ _ _ => n

/-! ### M₂-phase run lift -/

/-- Lift M₂'s `n`-step run from `cfg2` to the composed machine running
from the shifted config `{ state_idx := cfg2.state_idx + M₁.states,
tapes := cfg2.tapes }`. The result is the same config, with state
shifted by `M₁.states`. -/
private theorem runFlatTM_composeFlatTM_M2_phase
    (M₁ M₂ : FlatTM) (exit : Nat) (h_validM1 : validFlatTM M₁)
    (h_validM2 : validFlatTM M₂) (h_exit_lt : exit < M₁.states) :
    ∀ (n : Nat) (cfg2 : FlatTMConfig),
      cfg2.state_idx < M₂.states →
      runFlatTM n (composeFlatTM M₁ M₂ exit)
          { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } =
        (runFlatTM n M₂ cfg2).map
          (fun c => { state_idx := c.state_idx + M₁.states, tapes := c.tapes })
  | 0, cfg2, _ => rfl
  | n + 1, cfg2, h_state_lt => by
      have h_halt_eq :
          haltingStateReached (composeFlatTM M₁ M₂ exit)
              { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } =
            haltingStateReached M₂ cfg2 :=
        composeFlatTM_haltingStateReached_M2_phase M₁ M₂ exit cfg2
      by_cases h_halt : haltingStateReached M₂ cfg2 = true
      · -- M₂ halts immediately; both sides return the same config.
        have h_halt_c : haltingStateReached (composeFlatTM M₁ M₂ exit)
            { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } = true := by
          rw [h_halt_eq]; exact h_halt
        rw [runFlatTM_of_halting _ _ (n + 1) h_halt_c,
            runFlatTM_of_halting _ _ (n + 1) h_halt]
        rfl
      · have h_halt_false : haltingStateReached M₂ cfg2 = false := by
          cases h : haltingStateReached M₂ cfg2 with
          | true => exact absurd h h_halt
          | false => rfl
        have h_halt_c_false : haltingStateReached (composeFlatTM M₁ M₂ exit)
            { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } = false := by
          rw [h_halt_eq]; exact h_halt_false
        have h_step_eq :
            stepFlatTM (composeFlatTM M₁ M₂ exit)
                { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } =
              (stepFlatTM M₂ cfg2).map
                (fun c => { state_idx := c.state_idx + M₁.states, tapes := c.tapes }) := by
          have := stepFlatTM_composeFlatTM_M2 M₁ M₂ exit cfg2.state_idx cfg2.tapes
            h_validM1 h_exit_lt
          convert this using 2
        -- Unfold both runFlatTMs.
        have h_unfold_M2 :
            runFlatTM (n + 1) M₂ cfg2 =
              match stepFlatTM M₂ cfg2 with
              | none => some cfg2
              | some cfg2' => runFlatTM n M₂ cfg2' := by
          show (if haltingStateReached M₂ cfg2 = true then some cfg2
                else match stepFlatTM M₂ cfg2 with
                  | none => some cfg2
                  | some cfg2' => runFlatTM n M₂ cfg2') = _
          rw [if_neg (by rw [h_halt_false]; decide)]
        have h_unfold_C :
            runFlatTM (n + 1) (composeFlatTM M₁ M₂ exit)
                { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } =
              match stepFlatTM (composeFlatTM M₁ M₂ exit)
                  { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } with
              | none => some { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes }
              | some cfg' => runFlatTM n (composeFlatTM M₁ M₂ exit) cfg' := by
          show (if haltingStateReached (composeFlatTM M₁ M₂ exit)
                  { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } = true then
                  some { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes }
                else match stepFlatTM (composeFlatTM M₁ M₂ exit)
                    { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } with
                  | none => some { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes }
                  | some cfg' => runFlatTM n (composeFlatTM M₁ M₂ exit) cfg') = _
          rw [if_neg (by rw [h_halt_c_false]; decide)]
        rw [h_unfold_M2, h_unfold_C, h_step_eq]
        cases h_step : stepFlatTM M₂ cfg2 with
        | none => rfl
        | some cfg2' =>
            -- Apply IH at cfg2' (with shifted state still < M₂.states).
            have h_cfg2'_lt : cfg2'.state_idx < M₂.states :=
              state_idx_lt_states_of_step M₂ h_validM2 cfg2 cfg2' h_step
            show runFlatTM n (composeFlatTM M₁ M₂ exit)
                  { state_idx := cfg2'.state_idx + M₁.states, tapes := cfg2'.tapes } = _
            exact runFlatTM_composeFlatTM_M2_phase M₁ M₂ exit h_validM1 h_validM2 h_exit_lt
              n cfg2' h_cfg2'_lt
  termination_by n _ _ => n

/-! ### Final composition lemma -/

/-- **Operational correctness of `composeFlatTM`**.

If `M₁` (single-tape, valid) starts at `cfg0` and after `t₁` steps
reaches `c₁ = { state_idx := exit, tapes := [(left, head, right)] }`
without halting prematurely in any of the first `t₁` steps, and `M₂`
(single-tape, valid) starts at `{ state_idx := M₂.start, tapes := c₁.tapes }`
and after `t₂` steps halts at `c₂`, then the composed machine starting
at `cfg0` reaches the shifted `c₂` in exactly `t₁ + 1 + t₂` steps,
and that shifted config is a halting state of the composed machine.

This is the **load-bearing operational lemma** for Step 11. It lets us
build `evalCnfTM` (and `cliqueRelDecTM`) by composing small sub-TMs,
each with its own clean run lemma. -/
theorem composeFlatTM_run
    {M₁ M₂ : FlatTM} {exit : Nat}
    (h_validM1 : validFlatTM M₁) (h_validM2 : validFlatTM M₂)
    (h_exit_lt : exit < M₁.states)
    (cfg0 : FlatTMConfig) (h_cfg0_state_lt : cfg0.state_idx < M₁.states)
    (left₁ : List Nat) (head₁ : Nat) (right₁ : List Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left₁, head₁, right₁) = some v →
                          v < max M₁.sig M₂.sig)
    {t₁ t₂ : Nat} {c₂ : FlatTMConfig}
    (h_run1 : runFlatTM t₁ M₁ cfg0 =
              some { state_idx := exit, tapes := [(left₁, head₁, right₁)] })
    (h_traj1 : ∀ k, k < t₁ → ∀ ck, runFlatTM k M₁ cfg0 = some ck →
       ck.state_idx ≠ exit ∧
       haltingStateReached M₁ ck = false)
    (h_run2 : runFlatTM t₂ M₂
                { state_idx := M₂.start, tapes := [(left₁, head₁, right₁)] } = some c₂)
    (h_halt2 : haltingStateReached M₂ c₂ = true) :
    runFlatTM (t₁ + 1 + t₂) (composeFlatTM M₁ M₂ exit) cfg0 =
      some { state_idx := c₂.state_idx + M₁.states, tapes := c₂.tapes } ∧
    haltingStateReached (composeFlatTM M₁ M₂ exit)
      { state_idx := c₂.state_idx + M₁.states, tapes := c₂.tapes } = true := by
  refine ⟨?_, by rw [composeFlatTM_haltingStateReached_M2_phase]; exact h_halt2⟩
  -- Phase 1: lift M₁'s run.
  have h_phase1 :=
    runFlatTM_composeFlatTM_M1_phase M₁ M₂ exit h_validM1 t₁ cfg0 h_cfg0_state_lt h_traj1
  rw [← h_phase1] at h_run1
  -- Phase 2: bridge step.
  have h_bridge :=
    stepFlatTM_composeFlatTM_bridge M₁ M₂ exit left₁ right₁ head₁ h_sym_bound
  -- The bridge takes the composed run from c₁ in 1 step to
  -- { state_idx := M₁.states + M₂.start, tapes := same }.
  have h_phase12 :
      runFlatTM (t₁ + 1) (composeFlatTM M₁ M₂ exit) cfg0 =
        some { state_idx := M₁.states + M₂.start, tapes := [(left₁, head₁, right₁)] } := by
    -- t₁ steps takes cfg0 to c₁; then one more step is the bridge.
    apply runFlatTM_extend_by_step _ t₁ cfg0 _ _ h_run1 ?_ h_bridge
    -- Show that c₁ is non-halting in the composed machine.
    -- (state_idx = exit, exit < M₁.states, so composed.halt[exit] = false.)
    exact composeFlatTM_haltingStateReached_M1 M₁ M₂ exit _ h_exit_lt
  -- Phase 3: lift M₂'s run from cfg2_start = { state_idx := M₂.start, tapes := [..] }.
  set cfg2_start : FlatTMConfig := { state_idx := M₂.start, tapes := [(left₁, head₁, right₁)] }
  have h_M2_start_lt : M₂.start < M₂.states := h_validM2.1
  have h_phase3 :=
    runFlatTM_composeFlatTM_M2_phase M₁ M₂ exit h_validM1 h_validM2 h_exit_lt t₂ cfg2_start
      h_M2_start_lt
  rw [h_run2] at h_phase3
  -- The composed shifted start is { state_idx := M₂.start + M₁.states, tapes := [..] }
  -- = { state_idx := M₁.states + M₂.start, tapes := [..] } since add is commutative.
  have h_state_swap : M₂.start + M₁.states = M₁.states + M₂.start := Nat.add_comm _ _
  -- Combine via runFlatTM_compose.
  rw [show t₁ + 1 + t₂ = (t₁ + 1) + t₂ from rfl,
      runFlatTM_compose _ (t₁ + 1) t₂ _ _ h_phase12]
  -- Now we need: runFlatTM t₂ ... { state_idx := M₁.states + M₂.start, ... } = some shifted_c₂.
  -- The Option.map result from h_phase3 simplifies.
  have h_target :
      runFlatTM t₂ (composeFlatTM M₁ M₂ exit)
          { state_idx := M₁.states + M₂.start, tapes := [(left₁, head₁, right₁)] } =
        some { state_idx := c₂.state_idx + M₁.states, tapes := c₂.tapes } := by
    have h_eq : { state_idx := M₂.start + M₁.states, tapes := [(left₁, head₁, right₁)] } =
        ({ state_idx := M₁.states + M₂.start,
           tapes := [(left₁, head₁, right₁)] } : FlatTMConfig) := by
      rw [h_state_swap]
    rw [← h_eq]
    rw [h_phase3]
    rfl
  exact h_target

/-! ### No-early-halt trajectory of `composeFlatTM`

`composeFlatTM_run` proves the composite halts at the shifted `c₂` in
`t₁ + 1 + t₂` steps but *consumes* — rather than *emits* — a no-early-halt
trajectory. `composeFlatTM_no_early_halt` supplies the missing emitter: from the
two component trajectories it shows the composite never halts during any of the
first `t₁ + 1 + t₂` steps. This is exactly the `h_traj1` an *outer*
`composeFlatTM (composeFlatTM …) M exit` needs, so nests of `composeFlatTM`
(e.g. `AppendGadget.appendAtTM`) can be bracketed with a tail rewind. -/

/-- `runFlatTM` is total: it always returns some config (it idles on halt /
stuck states rather than failing). -/
private theorem runFlatTM_isSome (M : FlatTM) :
    ∀ (n : Nat) (cfg : FlatTMConfig), ∃ c, runFlatTM n M cfg = some c := by
  intro n
  induction n with
  | zero => intro cfg; exact ⟨cfg, rfl⟩
  | succ m ih =>
      intro cfg
      by_cases hh : haltingStateReached M cfg = true
      · refine ⟨cfg, ?_⟩
        show (if haltingStateReached M cfg = true then some cfg
              else match stepFlatTM M cfg with
                | none => some cfg
                | some c' => runFlatTM m M c') = some cfg
        rw [if_pos hh]
      · cases hs : stepFlatTM M cfg with
        | none =>
            refine ⟨cfg, ?_⟩
            show (if haltingStateReached M cfg = true then some cfg
                  else match stepFlatTM M cfg with
                    | none => some cfg
                    | some c' => runFlatTM m M c') = some cfg
            rw [if_neg hh, hs]
        | some c' =>
            obtain ⟨c, hc⟩ := ih c'
            refine ⟨c, ?_⟩
            show (if haltingStateReached M cfg = true then some cfg
                  else match stepFlatTM M cfg with
                    | none => some cfg
                    | some c'' => runFlatTM m M c'') = some c
            rw [if_neg hh, hs]; exact hc

/-- During the M₁ phase, the composite run coincides with `M₁`'s run, hence its
config's state stays `< M₁.states`. -/
private theorem composeFlatTM_state_lt_of_M1_phase
    (M₁ M₂ : FlatTM) (exit : Nat) (h_validM1 : validFlatTM M₁)
    (cfg0 : FlatTMConfig) (h_cfg0_state_lt : cfg0.state_idx < M₁.states)
    {t₁ : Nat}
    (h_traj1 : ∀ k, k < t₁ → ∀ ck, runFlatTM k M₁ cfg0 = some ck →
       ck.state_idx ≠ exit ∧ haltingStateReached M₁ ck = false) :
    ∀ k, k ≤ t₁ → ∀ ck,
      runFlatTM k M₁ cfg0 = some ck → ck.state_idx < M₁.states := by
  intro k
  induction k with
  | zero =>
      intro _ ck hck
      have : ck = cfg0 := (Option.some.inj hck).symm
      subst this; exact h_cfg0_state_lt
  | succ n ih =>
      intro hk ck hck
      have hn_le : n ≤ t₁ := Nat.le_of_succ_le hk
      have hn_lt : n < t₁ := hk
      -- The n-step config exists (runFlatTM is total).
      obtain ⟨cn, hcn⟩ : ∃ cn, runFlatTM n M₁ cfg0 = some cn := runFlatTM_isSome M₁ n cfg0
      have hcn_lt : cn.state_idx < M₁.states := ih hn_le cn hcn
      have hcn_nothalt : haltingStateReached M₁ cn = false :=
        (h_traj1 n hn_lt cn hcn).2
      -- One more step from cn gives ck.
      have hstep : runFlatTM (n + 1) M₁ cfg0 =
          match stepFlatTM M₁ cn with
          | none => some cn
          | some c' => runFlatTM 0 M₁ c' := by
        rw [runFlatTM_compose M₁ n 1 cfg0 cn hcn]
        show (if haltingStateReached M₁ cn = true then some cn
              else match stepFlatTM M₁ cn with
                | none => some cn
                | some c' => runFlatTM 0 M₁ c') = _
        rw [if_neg (by rw [hcn_nothalt]; decide)]
      rw [hstep] at hck
      cases hsc : stepFlatTM M₁ cn with
      | none => rw [hsc] at hck; simp only at hck;
                have : ck = cn := (Option.some.inj hck).symm
                subst this; exact hcn_lt
      | some c' =>
          rw [hsc] at hck
          show ck.state_idx < M₁.states
          have : ck = c' := (Option.some.inj hck).symm
          subst this
          exact state_idx_lt_states_of_step M₁ h_validM1 cn ck hsc

/-- **No-early-halt trajectory of `composeFlatTM`.** Same hypotheses as
`composeFlatTM_run`: from `M₁`'s run-to-`exit` + trajectory and `M₂`'s run-to-
halt + trajectory, the composite never reaches a halting state in any of the
first `t₁ + 1 + t₂` steps. -/
theorem composeFlatTM_no_early_halt
    {M₁ M₂ : FlatTM} {exit : Nat}
    (h_validM1 : validFlatTM M₁) (h_validM2 : validFlatTM M₂)
    (h_exit_lt : exit < M₁.states)
    (cfg0 : FlatTMConfig) (h_cfg0_state_lt : cfg0.state_idx < M₁.states)
    (left₁ : List Nat) (head₁ : Nat) (right₁ : List Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left₁, head₁, right₁) = some v →
                          v < max M₁.sig M₂.sig)
    {t₁ t₂ : Nat}
    (h_run1 : runFlatTM t₁ M₁ cfg0 =
              some { state_idx := exit, tapes := [(left₁, head₁, right₁)] })
    (h_traj1 : ∀ k, k < t₁ → ∀ ck, runFlatTM k M₁ cfg0 = some ck →
       ck.state_idx ≠ exit ∧
       haltingStateReached M₁ ck = false)
    (h_traj2 : ∀ k, k < t₂ → ∀ ck,
       runFlatTM k M₂ { state_idx := M₂.start, tapes := [(left₁, head₁, right₁)] }
         = some ck →
       haltingStateReached M₂ ck = false) :
    ∀ k, k < t₁ + 1 + t₂ → ∀ ck,
      runFlatTM k (composeFlatTM M₁ M₂ exit) cfg0 = some ck →
      haltingStateReached (composeFlatTM M₁ M₂ exit) ck = false := by
  intro k hk ck hck
  by_cases hkle : k ≤ t₁
  · -- M₁ phase: composite run = M₁ run.
    have h_traj1' : ∀ j, j < k → ∀ cj, runFlatTM j M₁ cfg0 = some cj →
        cj.state_idx ≠ exit ∧ haltingStateReached M₁ cj = false :=
      fun j hj cj hcj => h_traj1 j (Nat.lt_of_lt_of_le hj hkle) cj hcj
    have h_eq := runFlatTM_composeFlatTM_M1_phase M₁ M₂ exit h_validM1 k cfg0
      h_cfg0_state_lt h_traj1'
    rw [h_eq] at hck
    have hck_lt : ck.state_idx < M₁.states :=
      composeFlatTM_state_lt_of_M1_phase M₁ M₂ exit h_validM1 cfg0 h_cfg0_state_lt
        h_traj1 k hkle ck hck
    exact composeFlatTM_haltingStateReached_M1 M₁ M₂ exit ck hck_lt
  · -- M₂ phase: k = t₁ + 1 + j with j < t₂.
    push_neg at hkle
    -- k ≥ t₁ + 1, write k = (t₁ + 1) + j.
    obtain ⟨j, rfl⟩ : ∃ j, k = (t₁ + 1) + j := ⟨k - (t₁ + 1), by omega⟩
    have hj_lt : j < t₂ := by omega
    -- The composite reaches the shifted M₂ start in t₁+1 steps (from composeFlatTM_run's phase12).
    have h_phase1 :=
      runFlatTM_composeFlatTM_M1_phase M₁ M₂ exit h_validM1 t₁ cfg0 h_cfg0_state_lt h_traj1
    have h_run1' : runFlatTM t₁ (composeFlatTM M₁ M₂ exit) cfg0 =
        some { state_idx := exit, tapes := [(left₁, head₁, right₁)] } := by
      rw [h_phase1]; exact h_run1
    have h_bridge :=
      stepFlatTM_composeFlatTM_bridge M₁ M₂ exit left₁ right₁ head₁ h_sym_bound
    have h_phase12 :
        runFlatTM (t₁ + 1) (composeFlatTM M₁ M₂ exit) cfg0 =
          some { state_idx := M₁.states + M₂.start, tapes := [(left₁, head₁, right₁)] } := by
      apply runFlatTM_extend_by_step _ t₁ cfg0 _ _ h_run1' ?_ h_bridge
      exact composeFlatTM_haltingStateReached_M1 M₁ M₂ exit _ h_exit_lt
    -- runFlatTM ((t₁+1)+j) composite cfg0 = runFlatTM j composite (shifted start).
    rw [runFlatTM_compose _ (t₁ + 1) j cfg0 _ h_phase12] at hck
    -- Phase 3: lift M₂'s run.
    set cfg2_start : FlatTMConfig :=
      { state_idx := M₂.start, tapes := [(left₁, head₁, right₁)] }
    have h_M2_start_lt : M₂.start < M₂.states := h_validM2.1
    have h_phase_j :=
      runFlatTM_composeFlatTM_M2_phase M₁ M₂ exit h_validM1 h_validM2 h_exit_lt j cfg2_start
        h_M2_start_lt
    -- Rewrite: M₁.states + M₂.start ↔ M₂.start + M₁.states.
    have h_state_swap : M₂.start + M₁.states = M₁.states + M₂.start := Nat.add_comm _ _
    have h_cfg_eq :
        ({ state_idx := M₂.start + M₁.states,
           tapes := [(left₁, head₁, right₁)] } : FlatTMConfig) =
        { state_idx := M₁.states + M₂.start,
          tapes := [(left₁, head₁, right₁)] } := by
      rw [h_state_swap]
    rw [← h_cfg_eq, h_phase_j] at hck
    -- hck : (runFlatTM j M₂ cfg2_start).map (shift) = some ck.
    cases hjm : runFlatTM j M₂ cfg2_start with
    | none => rw [hjm] at hck; simp at hck
    | some cj =>
        rw [hjm] at hck
        simp only [Option.map_some] at hck
        have hck_eq : ck =
            { state_idx := cj.state_idx + M₁.states, tapes := cj.tapes } :=
          (Option.some.inj hck).symm
        have hcj_nothalt : haltingStateReached M₂ cj = false := h_traj2 j hj_lt cj hjm
        rw [hck_eq]
        rw [composeFlatTM_haltingStateReached_M2 M₁ M₂ exit cj.state_idx cj.tapes]
        exact hcj_nothalt


/-- **Stuck-`M₁` transfer (C8-2, 2026-07-05).** If `M₁`'s run from `cfg0`
never reaches its `exit` and never halts — e.g. a guard machine stuck on
malformed input (`FormatCheck.formatCheck_stuck`) — the composite never
reaches a halting state either, at ANY budget. This is the backward-direction
glue for guard-prefixed compositions under accept-by-halting: guard stuck ⇒
composite non-halting ⇒ `acceptsFlatTM = false`. (The symmetric `M₂`-stuck
case needs no new lemma: `composeFlatTM_no_early_halt` already covers it with
an arbitrary `t₂`.) -/
theorem composeFlatTM_stuck_M1
    {M₁ M₂ : FlatTM} {exit : Nat}
    (h_validM1 : validFlatTM M₁)
    (cfg0 : FlatTMConfig) (h_cfg0_state_lt : cfg0.state_idx < M₁.states)
    (h_traj1 : ∀ k, ∀ ck, runFlatTM k M₁ cfg0 = some ck →
       ck.state_idx ≠ exit ∧ haltingStateReached M₁ ck = false) :
    ∀ k, ∀ ck, runFlatTM k (composeFlatTM M₁ M₂ exit) cfg0 = some ck →
      haltingStateReached (composeFlatTM M₁ M₂ exit) ck = false := by
  intro k ck hck
  have h_traj1' : ∀ j, j < k → ∀ cj, runFlatTM j M₁ cfg0 = some cj →
      cj.state_idx ≠ exit ∧ haltingStateReached M₁ cj = false :=
    fun j _ cj hcj => h_traj1 j cj hcj
  have h_eq := runFlatTM_composeFlatTM_M1_phase M₁ M₂ exit h_validM1 k cfg0
    h_cfg0_state_lt h_traj1'
  rw [h_eq] at hck
  have hck_lt : ck.state_idx < M₁.states :=
    composeFlatTM_state_lt_of_M1_phase M₁ M₂ exit h_validM1 cfg0 h_cfg0_state_lt
      h_traj1' k (Nat.le_refl k) ck hck
  exact composeFlatTM_haltingStateReached_M1 M₁ M₂ exit ck hck_lt

/-! ## Step 11.5b — branching composition `branchComposeFlatTM`

A two-exit generalisation of `composeFlatTM`. Given three single-tape
machines `M₁`, `M₂`, `M₃` and two distinguished exit states `exit_pos`,
`exit_neg` of `M₁`, the composed machine runs `M₁` until it reaches
*one* of the two exits and then continues with the corresponding
branch:

- on `exit_pos`, hand off to `M₂` (starting at `M₂.start`);
- on `exit_neg`, hand off to `M₃` (starting at `M₃.start`).

This is the key primitive that lets the per-literal evaluator
(Step 11.5d) dispatch on the polarity bit (the sign byte `2` vs `3`
of a literal). It is needed because `composeFlatTM_run` only supports
a single exit state.

### State layout

`[0, M₁.states)`                       — M₁'s states
`[M₁.states, M₁.states + M₂.states)`   — M₂'s states (shifted by `+M₁.states`)
`[M₁.states + M₂.states, …)`           — M₃'s states (shifted by `+M₁.states + M₂.states`)

The composed machine has `M₁.states + M₂.states + M₃.states` states
in total.

### Halt vector

M₁'s halt bits are zeroed out (we don't stop in M₁ — both exits lead
elsewhere); M₂'s and M₃'s halt vectors are appended unchanged.

### Transition table (in `find?` order)

1. `bridgeEntries _ exit_pos (M₁.states + M₂.start)` — fires on
   `exit_pos`.
2. `bridgeEntries _ exit_neg (M₁.states + M₂.states + M₃.start)` —
   fires on `exit_neg`.
3. `M₁.trans` — unmodified.
4. `M₂.trans.map (shiftEntry M₁.states)` — shifted by `+M₁.states`.
5. `M₃.trans.map (shiftEntry (M₁.states + M₂.states))` — shifted by
   `+M₁.states + M₂.states`.

Bridges precede `M₁.trans` because `M₁` may itself have transitions
out of `exit_pos` / `exit_neg` (we do not require either exit to be
a halting state of `M₁` — only that the *trajectory* avoids halting
prematurely). Putting bridges first ensures the bridge fires before
any spurious M₁-transition would.

### Precondition: `exit_pos ≠ exit_neg`

If the two exits were equal, the find?-search would always return
the `exit_pos` bridge (it's first in the list), making the M₃ branch
unreachable. The run lemmas explicitly require `exit_pos ≠ exit_neg`. -/

/-- The halt-state vector of the branched-composed machine: M₁'s halt
bits are all turned off; M₂'s halt vector is appended; M₃'s halt
vector is appended. -/
def composedBranchHalt (M₁ M₂ M₃ : FlatTM) : List Bool :=
  List.replicate M₁.states false ++ M₂.halt ++ M₃.halt

/-- Branching composition of single-tape FlatTMs `M₁`, `M₂`, `M₃` with
two exit states. See the docstring above for the layout. -/
def branchComposeFlatTM (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat) : FlatTM where
  sig := max M₁.sig (max M₂.sig M₃.sig)
  tapes := M₁.tapes
  states := M₁.states + M₂.states + M₃.states
  trans :=
    bridgeEntries (max M₁.sig (max M₂.sig M₃.sig)) exit_pos (M₁.states + M₂.start) ++
    bridgeEntries (max M₁.sig (max M₂.sig M₃.sig)) exit_neg
        (M₁.states + M₂.states + M₃.start) ++
    M₁.trans ++
    M₂.trans.map (shiftEntry M₁.states) ++
    M₃.trans.map (shiftEntry (M₁.states + M₂.states))
  start := M₁.start
  halt := composedBranchHalt M₁ M₂ M₃

/-! ### Basic accessors -/

theorem branchComposeFlatTM_states (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat) :
    (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).states =
      M₁.states + M₂.states + M₃.states := rfl

theorem branchComposeFlatTM_start (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat) :
    (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).start = M₁.start := rfl

theorem branchComposeFlatTM_tapes (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat) :
    (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).tapes = M₁.tapes := rfl

theorem branchComposeFlatTM_sig (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat) :
    (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).sig =
      max M₁.sig (max M₂.sig M₃.sig) := rfl

theorem composedBranchHalt_length (M₁ M₂ M₃ : FlatTM) :
    (composedBranchHalt M₁ M₂ M₃).length =
      M₁.states + M₂.halt.length + M₃.halt.length := by
  show (List.replicate M₁.states false ++ M₂.halt ++ M₃.halt).length =
    M₁.states + M₂.halt.length + M₃.halt.length
  rw [List.length_append, List.length_append, List.length_replicate]

theorem branchComposeFlatTM_halt_length (M₁ M₂ M₃ : FlatTM)
    (exit_pos exit_neg : Nat)
    (h₂ : validFlatTM M₂) (h₃ : validFlatTM M₃) :
    (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).halt.length =
      (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).states := by
  rw [branchComposeFlatTM_states]
  show (composedBranchHalt M₁ M₂ M₃).length = M₁.states + M₂.states + M₃.states
  rw [composedBranchHalt_length, h₂.2.1, h₃.2.1]

/-! ### Validity of `branchComposeFlatTM` -/

theorem branchComposeFlatTM_valid (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat)
    (h₁ : validFlatTM M₁) (h₂ : validFlatTM M₂) (h₃ : validFlatTM M₃)
    (h_exit_pos : exit_pos < M₁.states)
    (h_exit_neg : exit_neg < M₁.states)
    (h_t1 : M₁.tapes = 1) (h_t2 : M₂.tapes = 1) (h_t3 : M₃.tapes = 1) :
    validFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) := by
  obtain ⟨h₁_start, h₁_halt, h₁_trans⟩ := h₁
  obtain ⟨h₂_start, h₂_halt, h₂_trans⟩ := h₂
  obtain ⟨h₃_start, h₃_halt, h₃_trans⟩ := h₃
  refine ⟨?_, ?_, ?_⟩
  · -- start < states
    show M₁.start < M₁.states + M₂.states + M₃.states
    have h1 : M₁.start < M₁.states + M₂.states :=
      Nat.lt_of_lt_of_le h₁_start (Nat.le_add_right _ _)
    exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
  · -- halt.length = states
    show (composedBranchHalt M₁ M₂ M₃).length =
      M₁.states + M₂.states + M₃.states
    rw [composedBranchHalt_length, h₂_halt, h₃_halt]
  · -- every transition is valid
    intro entry hentry
    show flatTMTransEntryValid (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) entry
    set sigC : Nat := max M₁.sig (max M₂.sig M₃.sig) with hsigC
    have hsig_eq : (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).sig = sigC := rfl
    have hstates_eq :
        (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).states =
          M₁.states + M₂.states + M₃.states := rfl
    have htapes_eq :
        (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).tapes = M₁.tapes := rfl
    have hentry' : entry ∈
        bridgeEntries sigC exit_pos (M₁.states + M₂.start) ++
        bridgeEntries sigC exit_neg (M₁.states + M₂.states + M₃.start) ++
        M₁.trans ++
        M₂.trans.map (shiftEntry M₁.states) ++
        M₃.trans.map (shiftEntry (M₁.states + M₂.states)) := hentry
    -- Bound helpers.
    have h_sig1_le : M₁.sig ≤ sigC := Nat.le_max_left _ _
    have h_sig2_le : M₂.sig ≤ sigC := by
      apply le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have h_sig3_le : M₃.sig ≤ sigC := by
      apply le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    -- Decompose membership through the four appends.
    rcases List.mem_append.mp hentry' with hLeft | h_m3
    rcases List.mem_append.mp hLeft with hLeft2 | h_m2
    rcases List.mem_append.mp hLeft2 with hLeft3 | h_m1
    rcases List.mem_append.mp hLeft3 with h_bridgePos | h_bridgeNeg
    · -- Bridge_pos
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ :=
        bridgeEntries_mem h_bridgePos
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsrc, hstates_eq]
        have h1 : exit_pos < M₁.states + M₂.states :=
          Nat.lt_of_lt_of_le h_exit_pos (Nat.le_add_right _ _)
        exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
      · rw [hdst, hstates_eq]
        -- M₁.states + M₂.start < M₁.states + M₂.states + M₃.states
        have h1 : M₁.states + M₂.start < M₁.states + M₂.states :=
          Nat.add_lt_add_left h₂_start M₁.states
        exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
      · rw [hsrcLen, htapes_eq, h_t1]
      · rw [hdstLen, htapes_eq, h_t1]
      · rw [hmovLen, htapes_eq, h_t1]
      · rw [hsig_eq]; exact hsymSrc
      · rw [hsig_eq]; exact hsymDst
    · -- Bridge_neg
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ :=
        bridgeEntries_mem h_bridgeNeg
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsrc, hstates_eq]
        have h1 : exit_neg < M₁.states + M₂.states :=
          Nat.lt_of_lt_of_le h_exit_neg (Nat.le_add_right _ _)
        exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
      · rw [hdst, hstates_eq]
        -- M₁.states + M₂.states + M₃.start < M₁.states + M₂.states + M₃.states
        exact Nat.add_lt_add_left h₃_start (M₁.states + M₂.states)
      · rw [hsrcLen, htapes_eq, h_t1]
      · rw [hdstLen, htapes_eq, h_t1]
      · rw [hmovLen, htapes_eq, h_t1]
      · rw [hsig_eq]; exact hsymSrc
      · rw [hsig_eq]; exact hsymDst
    · -- M₁'s original transition
      have hVal := h₁_trans entry h_m1
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ := hVal
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hstates_eq]
        have h1 : entry.src_state < M₁.states + M₂.states :=
          Nat.lt_of_lt_of_le hsrc (Nat.le_add_right _ _)
        exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
      · rw [hstates_eq]
        have h1 : entry.dst_state < M₁.states + M₂.states :=
          Nat.lt_of_lt_of_le hdst (Nat.le_add_right _ _)
        exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
      · rw [htapes_eq]; exact hsrcLen
      · rw [htapes_eq]; exact hdstLen
      · rw [htapes_eq]; exact hmovLen
      · rw [hsig_eq]
        intro x hx
        cases x with
        | none => trivial
        | some v => exact Nat.lt_of_lt_of_le (hsymSrc (some v) hx) h_sig1_le
      · rw [hsig_eq]
        intro x hx
        cases x with
        | none => trivial
        | some v => exact Nat.lt_of_lt_of_le (hsymDst (some v) hx) h_sig1_le
    · -- shifted M₂ transition
      rcases List.mem_map.mp h_m2 with ⟨entry₀, hentry₀, hshift⟩
      subst hshift
      have hVal := h₂_trans entry₀ hentry₀
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ := hVal
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show entry₀.src_state + M₁.states < M₁.states + M₂.states + M₃.states
        have h1 : entry₀.src_state + M₁.states < M₁.states + M₂.states := by
          rw [Nat.add_comm entry₀.src_state M₁.states]
          exact Nat.add_lt_add_left hsrc M₁.states
        exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
      · show entry₀.dst_state + M₁.states < M₁.states + M₂.states + M₃.states
        have h1 : entry₀.dst_state + M₁.states < M₁.states + M₂.states := by
          rw [Nat.add_comm entry₀.dst_state M₁.states]
          exact Nat.add_lt_add_left hdst M₁.states
        exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
      · rw [htapes_eq, h_t1, ← h_t2]; exact hsrcLen
      · rw [htapes_eq, h_t1, ← h_t2]; exact hdstLen
      · rw [htapes_eq, h_t1, ← h_t2]; exact hmovLen
      · rw [hsig_eq]
        intro x hx
        cases x with
        | none => trivial
        | some v => exact Nat.lt_of_lt_of_le (hsymSrc (some v) hx) h_sig2_le
      · rw [hsig_eq]
        intro x hx
        cases x with
        | none => trivial
        | some v => exact Nat.lt_of_lt_of_le (hsymDst (some v) hx) h_sig2_le
    · -- shifted M₃ transition
      rcases List.mem_map.mp h_m3 with ⟨entry₀, hentry₀, hshift⟩
      subst hshift
      have hVal := h₃_trans entry₀ hentry₀
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ := hVal
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show entry₀.src_state + (M₁.states + M₂.states) <
          M₁.states + M₂.states + M₃.states
        rw [Nat.add_comm entry₀.src_state (M₁.states + M₂.states)]
        exact Nat.add_lt_add_left hsrc (M₁.states + M₂.states)
      · show entry₀.dst_state + (M₁.states + M₂.states) <
          M₁.states + M₂.states + M₃.states
        rw [Nat.add_comm entry₀.dst_state (M₁.states + M₂.states)]
        exact Nat.add_lt_add_left hdst (M₁.states + M₂.states)
      · rw [htapes_eq, h_t1, ← h_t3]; exact hsrcLen
      · rw [htapes_eq, h_t1, ← h_t3]; exact hdstLen
      · rw [htapes_eq, h_t1, ← h_t3]; exact hmovLen
      · rw [hsig_eq]
        intro x hx
        cases x with
        | none => trivial
        | some v => exact Nat.lt_of_lt_of_le (hsymSrc (some v) hx) h_sig3_le
      · rw [hsig_eq]
        intro x hx
        cases x with
        | none => trivial
        | some v => exact Nat.lt_of_lt_of_le (hsymDst (some v) hx) h_sig3_le

/-! ### Halting state lemmas for `branchComposeFlatTM` -/

/-- At an M₁-state, the branched composed machine's halt bit is `false`. -/
private theorem branchComposeFlatTM_haltingStateReached_M1
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx < M₁.states) :
    haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg = false := by
  show (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).halt.getD cfg.state_idx false = false
  show (composedBranchHalt M₁ M₂ M₃).getD cfg.state_idx false = false
  show ((List.replicate M₁.states false ++ M₂.halt ++ M₃.halt).getD cfg.state_idx false) = false
  have h_left_lt :
      cfg.state_idx < (List.replicate M₁.states false ++ M₂.halt).length := by
    rw [List.length_append, List.length_replicate]
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
  rw [List.getD_append _ _ _ _ h_left_lt]
  have h_inner_lt : cfg.state_idx < (List.replicate M₁.states false).length := by
    rw [List.length_replicate]; exact h
  rw [List.getD_append _ _ _ _ h_inner_lt]
  exact List.getD_replicate false h

/-- On a shifted M₂-state `s + M₁.states` (with `s < M₂.states`), the
branched composed machine's halt bit equals `M₂`'s halt bit at `s`. -/
private theorem branchComposeFlatTM_haltingStateReached_M2
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat)
    (h₂ : validFlatTM M₂)
    (s : Nat) (h_s : s < M₂.states)
    (tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
        { state_idx := s + M₁.states, tapes := tapes } =
      haltingStateReached M₂ { state_idx := s, tapes := tapes } := by
  show (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).halt.getD
        (s + M₁.states) false = M₂.halt.getD s false
  show (composedBranchHalt M₁ M₂ M₃).getD (s + M₁.states) false = _
  show ((List.replicate M₁.states false ++ M₂.halt ++ M₃.halt).getD
        (s + M₁.states) false) = _
  have h_left_lt :
      s + M₁.states < (List.replicate M₁.states false ++ M₂.halt).length := by
    rw [List.length_append, List.length_replicate]
    -- s + M₁.states < M₁.states + M₂.halt.length
    rw [h₂.2.1]
    -- s + M₁.states < M₁.states + M₂.states
    rw [Nat.add_comm M₁.states M₂.states]
    exact Nat.add_lt_add_right h_s M₁.states
  rw [List.getD_append _ _ _ _ h_left_lt]
  have h_replicate_le :
      (List.replicate M₁.states false).length ≤ s + M₁.states := by
    rw [List.length_replicate]; exact Nat.le_add_left _ _
  rw [List.getD_append_right _ _ _ _ h_replicate_le]
  rw [List.length_replicate]
  show M₂.halt.getD (s + M₁.states - M₁.states) false = _
  rw [Nat.add_sub_cancel]

/-- On a shifted M₃-state `s + (M₁.states + M₂.states)`, the branched
composed machine's halt bit equals `M₃`'s halt bit at `s`. -/
private theorem branchComposeFlatTM_haltingStateReached_M3
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat)
    (h₂ : validFlatTM M₂)
    (s : Nat)
    (tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
        { state_idx := s + (M₁.states + M₂.states), tapes := tapes } =
      haltingStateReached M₃ { state_idx := s, tapes := tapes } := by
  show (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).halt.getD
        (s + (M₁.states + M₂.states)) false = M₃.halt.getD s false
  show (composedBranchHalt M₁ M₂ M₃).getD (s + (M₁.states + M₂.states)) false = _
  show ((List.replicate M₁.states false ++ M₂.halt ++ M₃.halt).getD
        (s + (M₁.states + M₂.states)) false) = _
  have h_left_le :
      (List.replicate M₁.states false ++ M₂.halt).length ≤ s + (M₁.states + M₂.states) := by
    rw [List.length_append, List.length_replicate, h₂.2.1]
    -- M₁.states + M₂.states ≤ s + (M₁.states + M₂.states)
    exact Nat.le_add_left _ _
  rw [List.getD_append_right _ _ _ _ h_left_le]
  rw [List.length_append, List.length_replicate, h₂.2.1]
  -- M₃.halt.getD (s + (M₁.states + M₂.states) - (M₁.states + M₂.states)) false
  rw [Nat.add_sub_cancel]

/-! ### M₁-phase step lemma for `branchComposeFlatTM` -/

/-- M₁-phase step: on a cfg in M₁'s state range and not equal to either
exit, one branched-composed step coincides with M₁'s one step. -/
private theorem stepFlatTM_branchComposeFlatTM_M1
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat) (cfg : FlatTMConfig)
    (h_state_lt : cfg.state_idx < M₁.states)
    (h_state_ne_pos : cfg.state_idx ≠ exit_pos)
    (h_state_ne_neg : cfg.state_idx ≠ exit_neg) :
    stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg = stepFlatTM M₁ cfg := by
  show ((branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).trans.find?
          (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) =
       (M₁.trans.find? (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg)
  have h_trans :
      (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).trans =
        bridgeEntries (max M₁.sig (max M₂.sig M₃.sig)) exit_pos (M₁.states + M₂.start) ++
        bridgeEntries (max M₁.sig (max M₂.sig M₃.sig)) exit_neg
            (M₁.states + M₂.states + M₃.start) ++
        M₁.trans ++
        M₂.trans.map (shiftEntry M₁.states) ++
        M₃.trans.map (shiftEntry (M₁.states + M₂.states)) := rfl
  rw [h_trans]
  rw [List.find?_append, List.find?_append, List.find?_append, List.find?_append]
  have h_bridge_pos :
      (bridgeEntries (max M₁.sig (max M₂.sig M₃.sig)) exit_pos
          (M₁.states + M₂.start)).find?
          (fun e => entryMatchesConfig e cfg) = none :=
    bridgeEntries_find_eq_none h_state_ne_pos
  have h_bridge_neg :
      (bridgeEntries (max M₁.sig (max M₂.sig M₃.sig)) exit_neg
          (M₁.states + M₂.states + M₃.start)).find?
          (fun e => entryMatchesConfig e cfg) = none :=
    bridgeEntries_find_eq_none h_state_ne_neg
  have h_shift2 :
      (M₂.trans.map (shiftEntry M₁.states)).find?
          (fun e => entryMatchesConfig e cfg) = none :=
    shiftEntries_find_eq_none M₂ M₁.states cfg h_state_lt
  have h_shift3 :
      (M₃.trans.map (shiftEntry (M₁.states + M₂.states))).find?
          (fun e => entryMatchesConfig e cfg) = none := by
    refine shiftEntries_find_eq_none M₃ (M₁.states + M₂.states) cfg ?_
    exact Nat.lt_of_lt_of_le h_state_lt (Nat.le_add_right _ _)
  rw [h_bridge_pos, h_bridge_neg, h_shift2, h_shift3]
  simp only [Option.none_or, Option.or_none]

/-! ### Bridge step lemmas for `branchComposeFlatTM` -/

/-- Bridge_pos step: at state `exit_pos` with a single-tape cfg, one
branched-composed step jumps to `M₁.states + M₂.start`. -/
private theorem stepFlatTM_branchComposeFlatTM_bridge_pos
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat)
    (left right : List Nat) (head : Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left, head, right) = some v →
                          v < max M₁.sig (max M₂.sig M₃.sig)) :
    stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
        { state_idx := exit_pos, tapes := [(left, head, right)] } =
      some { state_idx := M₁.states + M₂.start,
             tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := exit_pos, tapes := [(left, head, right)] }
    with hcfg
  show ((branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).trans.find?
          (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) = _
  set sigC : Nat := max M₁.sig (max M₂.sig M₃.sig)
  have h_trans :
      (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).trans =
        bridgeEntries sigC exit_pos (M₁.states + M₂.start) ++
        bridgeEntries sigC exit_neg (M₁.states + M₂.states + M₃.start) ++
        M₁.trans ++
        M₂.trans.map (shiftEntry M₁.states) ++
        M₃.trans.map (shiftEntry (M₁.states + M₂.states)) := rfl
  rw [h_trans]
  rw [List.find?_append, List.find?_append, List.find?_append, List.find?_append]
  -- Bridge_pos's find? returns some bridge_mk_entry for the current symbol.
  have h_tape_map :
      cfg.tapes.map currentTapeSymbol = [currentTapeSymbol (left, head, right)] := rfl
  have h_cfg_state : cfg.state_idx = exit_pos := rfl
  rw [bridgeEntries_eq_bridgeMkEntry]
  -- We need: the bridge_pos's find? = some (bridgeMkEntry exit_pos _ (current symbol)).
  suffices h_bridge_find :
      ((bridgeMkEntry exit_pos (M₁.states + M₂.start) none ::
          (List.range sigC).map
            (fun w => bridgeMkEntry exit_pos (M₁.states + M₂.start) (some w))).find?
          (fun e => entryMatchesConfig e cfg)) =
        some (bridgeMkEntry exit_pos (M₁.states + M₂.start)
          (currentTapeSymbol (left, head, right))) by
    rw [h_bridge_find]
    -- Goal: (((some _ ).or _).or _).or _).or _).bind apply = some {...}
    simp only [Option.some_or]
    exact applyBridgeMkEntry_singleTape exit_pos (M₁.states + M₂.start)
      (currentTapeSymbol (left, head, right)) left right head
  cases h_sym : currentTapeSymbol (left, head, right) with
  | none =>
      have h_match :
          entryMatchesConfig
            (bridgeMkEntry exit_pos (M₁.states + M₂.start) none) cfg = true := by
        refine entryMatchesConfig_true_of rfl ?_
        show ([none] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol
        rw [h_tape_map, h_sym]
      exact List.find?_cons_of_pos h_match
  | some v =>
      have h_no_match : ¬ entryMatchesConfig
          (bridgeMkEntry exit_pos (M₁.states + M₂.start) none) cfg = true := by
        intro h
        have h_tape_eq := ((entryMatchesConfig_iff _ _).mp h).2
        have h_eq : ([none] : List (Option Nat)) = [some v] := by
          calc ([none] : List (Option Nat))
              = (bridgeMkEntry exit_pos (M₁.states + M₂.start) none).src_tape_vals := rfl
            _ = cfg.tapes.map currentTapeSymbol := h_tape_eq
            _ = [currentTapeSymbol (left, head, right)] := h_tape_map
            _ = [some v] := by rw [h_sym]
        injection h_eq with h1 _
        cases h1
      have h_step :
          ((bridgeMkEntry exit_pos (M₁.states + M₂.start) none) ::
            (List.range sigC).map
              (fun w => bridgeMkEntry exit_pos (M₁.states + M₂.start) (some w))).find?
              (fun e => entryMatchesConfig e cfg) =
          ((List.range sigC).map
              (fun w => bridgeMkEntry exit_pos (M₁.states + M₂.start) (some w))).find?
              (fun e => entryMatchesConfig e cfg) :=
        List.find?_cons_of_neg h_no_match
      rw [h_step]
      have h_v_lt : v < sigC := h_sym_bound v h_sym
      exact find_bridgeRange_some sigC exit_pos (M₁.states + M₂.start) v
        h_v_lt cfg h_cfg_state (by rw [h_tape_map, h_sym])

/-- Bridge_neg step: at state `exit_neg` (with `exit_pos ≠ exit_neg`)
with a single-tape cfg, one branched-composed step jumps to
`M₁.states + M₂.states + M₃.start`. -/
private theorem stepFlatTM_branchComposeFlatTM_bridge_neg
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat)
    (h_exit_ne : exit_pos ≠ exit_neg)
    (left right : List Nat) (head : Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left, head, right) = some v →
                          v < max M₁.sig (max M₂.sig M₃.sig)) :
    stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
        { state_idx := exit_neg, tapes := [(left, head, right)] } =
      some { state_idx := M₁.states + M₂.states + M₃.start,
             tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := exit_neg, tapes := [(left, head, right)] }
    with hcfg
  show ((branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).trans.find?
          (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) = _
  set sigC : Nat := max M₁.sig (max M₂.sig M₃.sig)
  have h_trans :
      (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).trans =
        bridgeEntries sigC exit_pos (M₁.states + M₂.start) ++
        bridgeEntries sigC exit_neg (M₁.states + M₂.states + M₃.start) ++
        M₁.trans ++
        M₂.trans.map (shiftEntry M₁.states) ++
        M₃.trans.map (shiftEntry (M₁.states + M₂.states)) := rfl
  rw [h_trans]
  rw [List.find?_append, List.find?_append, List.find?_append, List.find?_append]
  -- Bridge_pos doesn't match (cfg.state_idx = exit_neg ≠ exit_pos).
  have h_state_ne : cfg.state_idx ≠ exit_pos := by
    show exit_neg ≠ exit_pos
    intro h_eq; exact h_exit_ne h_eq.symm
  have h_bridge_pos_none :
      (bridgeEntries sigC exit_pos (M₁.states + M₂.start)).find?
          (fun e => entryMatchesConfig e cfg) = none :=
    bridgeEntries_find_eq_none h_state_ne
  rw [h_bridge_pos_none]
  have h_tape_map :
      cfg.tapes.map currentTapeSymbol = [currentTapeSymbol (left, head, right)] := rfl
  have h_cfg_state : cfg.state_idx = exit_neg := rfl
  rw [bridgeEntries_eq_bridgeMkEntry]
  -- The bridge_neg's find? returns some bridge_mk_entry for the current symbol.
  suffices h_bridge_find :
      ((bridgeMkEntry exit_neg (M₁.states + M₂.states + M₃.start) none ::
          (List.range sigC).map
            (fun w => bridgeMkEntry exit_neg (M₁.states + M₂.states + M₃.start) (some w))).find?
          (fun e => entryMatchesConfig e cfg)) =
        some (bridgeMkEntry exit_neg (M₁.states + M₂.states + M₃.start)
          (currentTapeSymbol (left, head, right))) by
    rw [h_bridge_find]
    simp only [Option.none_or, Option.some_or]
    exact applyBridgeMkEntry_singleTape exit_neg (M₁.states + M₂.states + M₃.start)
      (currentTapeSymbol (left, head, right)) left right head
  cases h_sym : currentTapeSymbol (left, head, right) with
  | none =>
      have h_match :
          entryMatchesConfig
            (bridgeMkEntry exit_neg (M₁.states + M₂.states + M₃.start) none) cfg = true := by
        refine entryMatchesConfig_true_of rfl ?_
        show ([none] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol
        rw [h_tape_map, h_sym]
      exact List.find?_cons_of_pos h_match
  | some v =>
      have h_no_match : ¬ entryMatchesConfig
          (bridgeMkEntry exit_neg (M₁.states + M₂.states + M₃.start) none) cfg = true := by
        intro h
        have h_tape_eq := ((entryMatchesConfig_iff _ _).mp h).2
        have h_eq : ([none] : List (Option Nat)) = [some v] := by
          calc ([none] : List (Option Nat))
              = (bridgeMkEntry exit_neg (M₁.states + M₂.states + M₃.start)
                  none).src_tape_vals := rfl
            _ = cfg.tapes.map currentTapeSymbol := h_tape_eq
            _ = [currentTapeSymbol (left, head, right)] := h_tape_map
            _ = [some v] := by rw [h_sym]
        injection h_eq with h1 _
        cases h1
      have h_step :
          ((bridgeMkEntry exit_neg (M₁.states + M₂.states + M₃.start) none) ::
            (List.range sigC).map
              (fun w => bridgeMkEntry exit_neg (M₁.states + M₂.states + M₃.start)
                (some w))).find?
              (fun e => entryMatchesConfig e cfg) =
          ((List.range sigC).map
              (fun w => bridgeMkEntry exit_neg (M₁.states + M₂.states + M₃.start)
                (some w))).find?
              (fun e => entryMatchesConfig e cfg) :=
        List.find?_cons_of_neg h_no_match
      rw [h_step]
      have h_v_lt : v < sigC := h_sym_bound v h_sym
      exact find_bridgeRange_some sigC exit_neg (M₁.states + M₂.states + M₃.start) v
        h_v_lt cfg h_cfg_state (by rw [h_tape_map, h_sym])

/-! ### M₂-phase and M₃-phase step lemmas for `branchComposeFlatTM`

These follow the template of `stepFlatTM_composeFlatTM_M2`. The M₂
step is at offset `M₁.states`; the M₃ step is at offset
`M₁.states + M₂.states`. Each requires that the *other* shifted block
does not match (a small upper-bound argument on the unshifted state). -/

/-- Shifted-block entries don't match cfg.state_idx if their unshifted
src values stay strictly below `cfg.state_idx - off`. We use this in
the M₃-phase lemma to dismiss shifted M₂ entries (whose unshifted src
< M₂.states ≤ cfg.state_idx - M₁.states). -/
private theorem shiftEntries_find_eq_none_above
    (M : FlatTM) (h_valid : validFlatTM M) (off : Nat) (cfg : FlatTMConfig)
    (h : off + M.states ≤ cfg.state_idx) :
    (M.trans.map (shiftEntry off)).find?
        (fun e => entryMatchesConfig e cfg) = none := by
  rw [List.find?_eq_none]
  intro e' he'
  rcases List.mem_map.mp he' with ⟨e, he, hshift⟩
  subst hshift
  refine entryMatchesConfig_ne_true_of_state_ne ?_
  rw [shiftEntry_src_state_ge]
  have h_e_src_lt : e.src_state < M.states := (h_valid.2.2 e he).1
  have h_lt : e.src_state + off < cfg.state_idx := by
    have h1 : e.src_state + off < M.states + off := Nat.add_lt_add_right h_e_src_lt off
    have h2 : M.states + off = off + M.states := Nat.add_comm _ _
    exact Nat.lt_of_lt_of_le (h2 ▸ h1) h
  exact Nat.ne_of_lt h_lt

/-- M₂-phase step: on a shifted M₂-state `s + M₁.states` (with
`s < M₂.states`), one branched-composed step coincides with M₂'s one
step at the unshifted state `s`, with the result shifted by `+M₁.states`. -/
private theorem stepFlatTM_branchComposeFlatTM_M2
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat) (s : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (h_validM1 : validFlatTM M₁)
    (h_validM3 : validFlatTM M₃)
    (h_exit_pos_lt : exit_pos < M₁.states)
    (h_exit_neg_lt : exit_neg < M₁.states)
    (h_s_lt : s < M₂.states) :
    stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
        { state_idx := s + M₁.states, tapes := tapes } =
      (stepFlatTM M₂ { state_idx := s, tapes := tapes }).map
        (fun c => { state_idx := c.state_idx + M₁.states, tapes := c.tapes }) := by
  set cfg : FlatTMConfig := { state_idx := s + M₁.states, tapes := tapes } with hcfg
  set cfg2 : FlatTMConfig := { state_idx := s, tapes := tapes } with hcfg2
  show ((branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).trans.find?
          (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) =
       ((M₂.trans.find?
          (fun e => entryMatchesConfig e cfg2)).bind (applyTransitionEntry cfg2)).map _
  set sigC : Nat := max M₁.sig (max M₂.sig M₃.sig)
  have h_trans :
      (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).trans =
        bridgeEntries sigC exit_pos (M₁.states + M₂.start) ++
        bridgeEntries sigC exit_neg (M₁.states + M₂.states + M₃.start) ++
        M₁.trans ++
        M₂.trans.map (shiftEntry M₁.states) ++
        M₃.trans.map (shiftEntry (M₁.states + M₂.states)) := rfl
  rw [h_trans]
  rw [List.find?_append, List.find?_append, List.find?_append, List.find?_append]
  -- Both bridges: src = exit_* < M₁.states ≤ s + M₁.states = cfg.state_idx → none.
  have h_bridge_pos_none :
      (bridgeEntries sigC exit_pos (M₁.states + M₂.start)).find?
          (fun e => entryMatchesConfig e cfg) = none := by
    refine bridgeEntries_find_eq_none ?_
    show cfg.state_idx ≠ exit_pos
    show s + M₁.states ≠ exit_pos
    intro h_eq
    have h_lt : exit_pos < s + M₁.states :=
      Nat.lt_of_lt_of_le h_exit_pos_lt (Nat.le_add_left _ _)
    exact absurd h_eq.symm (Nat.ne_of_lt h_lt)
  have h_bridge_neg_none :
      (bridgeEntries sigC exit_neg (M₁.states + M₂.states + M₃.start)).find?
          (fun e => entryMatchesConfig e cfg) = none := by
    refine bridgeEntries_find_eq_none ?_
    show cfg.state_idx ≠ exit_neg
    show s + M₁.states ≠ exit_neg
    intro h_eq
    have h_lt : exit_neg < s + M₁.states :=
      Nat.lt_of_lt_of_le h_exit_neg_lt (Nat.le_add_left _ _)
    exact absurd h_eq.symm (Nat.ne_of_lt h_lt)
  -- M₁'s trans: src < M₁.states ≤ cfg.state_idx → none.
  have h_M1_none :
      M₁.trans.find? (fun e => entryMatchesConfig e cfg) = none := by
    rw [List.find?_eq_none]
    intro e he
    refine entryMatchesConfig_ne_true_of_state_ne ?_
    have h_src_lt : e.src_state < M₁.states := (h_validM1.2.2 e he).1
    show e.src_state ≠ cfg.state_idx
    show e.src_state ≠ s + M₁.states
    intro h_eq
    have h_lt' : e.src_state < s + M₁.states :=
      Nat.lt_of_lt_of_le h_src_lt (Nat.le_add_left _ _)
    exact absurd h_eq (Nat.ne_of_lt h_lt')
  -- Shifted M₃: src = e.src + (M₁.states + M₂.states) ≥ M₁.states + M₂.states > cfg.
  have h_M3_none :
      (M₃.trans.map (shiftEntry (M₁.states + M₂.states))).find?
          (fun e => entryMatchesConfig e cfg) = none := by
    refine shiftEntries_find_eq_none M₃ (M₁.states + M₂.states) cfg ?_
    -- cfg.state_idx = s + M₁.states < M₁.states + M₂.states
    show s + M₁.states < M₁.states + M₂.states
    rw [Nat.add_comm s M₁.states]
    exact Nat.add_lt_add_left h_s_lt M₁.states
  rw [h_bridge_pos_none, h_bridge_neg_none, h_M1_none, h_M3_none]
  simp only [Option.none_or, Option.or_none]
  -- Now we have: ((M₂.trans.map (shiftEntry M₁.states)).find? pred).bind apply on cfg.
  rw [List.find?_map]
  show (Option.map (shiftEntry M₁.states)
          (M₂.trans.find?
            (fun e => entryMatchesConfig (shiftEntry M₁.states e) cfg))).bind
        (applyTransitionEntry cfg) =
       ((M₂.trans.find? (fun e => entryMatchesConfig e cfg2)).bind
          (applyTransitionEntry cfg2)).map _
  have h_pred_eq :
      (fun e => entryMatchesConfig (shiftEntry M₁.states e) cfg) =
      (fun e => entryMatchesConfig e cfg2) := by
    funext e
    by_cases h_match : entryMatchesConfig e cfg2 = true
    · have ⟨h_state2, h_tape2⟩ := (entryMatchesConfig_iff _ _).mp h_match
      have h_match_shifted : entryMatchesConfig (shiftEntry M₁.states e) cfg = true := by
        refine entryMatchesConfig_true_of ?_ h_tape2
        show e.src_state + M₁.states = s + M₁.states
        rw [h_state2]
      rw [h_match_shifted, h_match]
    · have h_match_neg : entryMatchesConfig e cfg2 = false := by
        cases h : entryMatchesConfig e cfg2 with
        | true => exact absurd h h_match
        | false => rfl
      have h_match_shifted_neg :
          entryMatchesConfig (shiftEntry M₁.states e) cfg = false := by
        cases h : entryMatchesConfig (shiftEntry M₁.states e) cfg with
        | true =>
            have ⟨h_state, h_tape⟩ := (entryMatchesConfig_iff _ _).mp h
            have h_state_eq : e.src_state + M₁.states = s + M₁.states := h_state
            have h_src_eq : e.src_state = s := Nat.add_right_cancel h_state_eq
            have h_match_pos : entryMatchesConfig e cfg2 = true :=
              entryMatchesConfig_true_of h_src_eq h_tape
            rw [h_match_pos] at h_match_neg
            cases h_match_neg
        | false => rfl
      rw [h_match_shifted_neg, h_match_neg]
  rw [h_pred_eq]
  cases hF : M₂.trans.find? (fun e => entryMatchesConfig e cfg2) with
  | none => rfl
  | some e =>
      show (some (shiftEntry M₁.states e)).bind (applyTransitionEntry cfg) =
        Option.map _ ((some e).bind (applyTransitionEntry cfg2))
      show applyTransitionEntry cfg (shiftEntry M₁.states e) =
        Option.map _ (applyTransitionEntry cfg2 e)
      have h_sub : cfg.state_idx - M₁.states = cfg2.state_idx := by
        show s + M₁.states - M₁.states = s
        exact Nat.add_sub_cancel _ _
      have h_cfg_eq : { state_idx := cfg.state_idx - M₁.states, tapes := cfg.tapes } = cfg2 := by
        rw [h_sub]
      rw [applyTransitionEntry_shiftEntry, h_cfg_eq]

/-- M₃-phase step: on a shifted M₃-state `s + (M₁.states + M₂.states)`
(with `s < M₃.states`), one branched-composed step coincides with
M₃'s one step at the unshifted state `s`, with the result shifted by
`+(M₁.states + M₂.states)`. -/
private theorem stepFlatTM_branchComposeFlatTM_M3
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat) (s : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (h_validM1 : validFlatTM M₁)
    (h_validM2 : validFlatTM M₂)
    (h_exit_pos_lt : exit_pos < M₁.states)
    (h_exit_neg_lt : exit_neg < M₁.states) :
    stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
        { state_idx := s + (M₁.states + M₂.states), tapes := tapes } =
      (stepFlatTM M₃ { state_idx := s, tapes := tapes }).map
        (fun c => { state_idx := c.state_idx + (M₁.states + M₂.states),
                    tapes := c.tapes }) := by
  set cfg : FlatTMConfig := { state_idx := s + (M₁.states + M₂.states), tapes := tapes }
    with hcfg
  set cfg3 : FlatTMConfig := { state_idx := s, tapes := tapes } with hcfg3
  show ((branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).trans.find?
          (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) =
       ((M₃.trans.find?
          (fun e => entryMatchesConfig e cfg3)).bind (applyTransitionEntry cfg3)).map _
  set sigC : Nat := max M₁.sig (max M₂.sig M₃.sig)
  have h_trans :
      (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg).trans =
        bridgeEntries sigC exit_pos (M₁.states + M₂.start) ++
        bridgeEntries sigC exit_neg (M₁.states + M₂.states + M₃.start) ++
        M₁.trans ++
        M₂.trans.map (shiftEntry M₁.states) ++
        M₃.trans.map (shiftEntry (M₁.states + M₂.states)) := rfl
  rw [h_trans]
  rw [List.find?_append, List.find?_append, List.find?_append, List.find?_append]
  -- All non-M₃ entries don't match cfg.state_idx = s + (M₁.states + M₂.states):
  -- Bridge_pos: src = exit_pos < M₁.states ≤ M₁.states + M₂.states ≤ cfg → none.
  have h_M1M2_le : M₁.states ≤ s + (M₁.states + M₂.states) := by
    have h1 : M₁.states ≤ M₁.states + M₂.states := Nat.le_add_right _ _
    exact Nat.le_trans h1 (Nat.le_add_left _ _)
  have h_bridge_pos_none :
      (bridgeEntries sigC exit_pos (M₁.states + M₂.start)).find?
          (fun e => entryMatchesConfig e cfg) = none := by
    refine bridgeEntries_find_eq_none ?_
    show cfg.state_idx ≠ exit_pos
    show s + (M₁.states + M₂.states) ≠ exit_pos
    intro h_eq
    have h_lt : exit_pos < s + (M₁.states + M₂.states) :=
      Nat.lt_of_lt_of_le h_exit_pos_lt h_M1M2_le
    exact absurd h_eq.symm (Nat.ne_of_lt h_lt)
  have h_bridge_neg_none :
      (bridgeEntries sigC exit_neg (M₁.states + M₂.states + M₃.start)).find?
          (fun e => entryMatchesConfig e cfg) = none := by
    refine bridgeEntries_find_eq_none ?_
    show cfg.state_idx ≠ exit_neg
    show s + (M₁.states + M₂.states) ≠ exit_neg
    intro h_eq
    have h_lt : exit_neg < s + (M₁.states + M₂.states) :=
      Nat.lt_of_lt_of_le h_exit_neg_lt h_M1M2_le
    exact absurd h_eq.symm (Nat.ne_of_lt h_lt)
  -- M₁'s trans: src < M₁.states ≤ cfg → none.
  have h_M1_none :
      M₁.trans.find? (fun e => entryMatchesConfig e cfg) = none := by
    rw [List.find?_eq_none]
    intro e he
    refine entryMatchesConfig_ne_true_of_state_ne ?_
    have h_src_lt : e.src_state < M₁.states := (h_validM1.2.2 e he).1
    show e.src_state ≠ cfg.state_idx
    show e.src_state ≠ s + (M₁.states + M₂.states)
    intro h_eq
    have h_lt' : e.src_state < s + (M₁.states + M₂.states) :=
      Nat.lt_of_lt_of_le h_src_lt h_M1M2_le
    exact absurd h_eq (Nat.ne_of_lt h_lt')
  -- Shifted M₂: src = e.src + M₁.states < M₁.states + M₂.states ≤ cfg → none.
  have h_M2_none :
      (M₂.trans.map (shiftEntry M₁.states)).find?
          (fun e => entryMatchesConfig e cfg) = none := by
    refine shiftEntries_find_eq_none_above M₂ h_validM2 M₁.states cfg ?_
    show M₁.states + M₂.states ≤ s + (M₁.states + M₂.states)
    exact Nat.le_add_left _ _
  rw [h_bridge_pos_none, h_bridge_neg_none, h_M1_none, h_M2_none]
  simp only [Option.none_or, Option.or_none]
  -- Now we have: ((M₃.trans.map (shiftEntry (M₁.states + M₂.states))).find? pred).bind ...
  rw [List.find?_map]
  show (Option.map (shiftEntry (M₁.states + M₂.states))
          (M₃.trans.find?
            (fun e => entryMatchesConfig (shiftEntry (M₁.states + M₂.states) e) cfg))).bind
        (applyTransitionEntry cfg) =
       ((M₃.trans.find? (fun e => entryMatchesConfig e cfg3)).bind
          (applyTransitionEntry cfg3)).map _
  have h_pred_eq :
      (fun e => entryMatchesConfig (shiftEntry (M₁.states + M₂.states) e) cfg) =
      (fun e => entryMatchesConfig e cfg3) := by
    funext e
    by_cases h_match : entryMatchesConfig e cfg3 = true
    · have ⟨h_state3, h_tape3⟩ := (entryMatchesConfig_iff _ _).mp h_match
      have h_match_shifted :
          entryMatchesConfig (shiftEntry (M₁.states + M₂.states) e) cfg = true := by
        refine entryMatchesConfig_true_of ?_ h_tape3
        show e.src_state + (M₁.states + M₂.states) = s + (M₁.states + M₂.states)
        rw [h_state3]
      rw [h_match_shifted, h_match]
    · have h_match_neg : entryMatchesConfig e cfg3 = false := by
        cases h : entryMatchesConfig e cfg3 with
        | true => exact absurd h h_match
        | false => rfl
      have h_match_shifted_neg :
          entryMatchesConfig (shiftEntry (M₁.states + M₂.states) e) cfg = false := by
        cases h : entryMatchesConfig (shiftEntry (M₁.states + M₂.states) e) cfg with
        | true =>
            have ⟨h_state, h_tape⟩ := (entryMatchesConfig_iff _ _).mp h
            have h_state_eq :
                e.src_state + (M₁.states + M₂.states) =
                  s + (M₁.states + M₂.states) := h_state
            have h_src_eq : e.src_state = s := Nat.add_right_cancel h_state_eq
            have h_match_pos : entryMatchesConfig e cfg3 = true :=
              entryMatchesConfig_true_of h_src_eq h_tape
            rw [h_match_pos] at h_match_neg
            cases h_match_neg
        | false => rfl
      rw [h_match_shifted_neg, h_match_neg]
  rw [h_pred_eq]
  cases hF : M₃.trans.find? (fun e => entryMatchesConfig e cfg3) with
  | none => rfl
  | some e =>
      show (some (shiftEntry (M₁.states + M₂.states) e)).bind (applyTransitionEntry cfg) =
        Option.map _ ((some e).bind (applyTransitionEntry cfg3))
      show applyTransitionEntry cfg (shiftEntry (M₁.states + M₂.states) e) =
        Option.map _ (applyTransitionEntry cfg3 e)
      have h_sub : cfg.state_idx - (M₁.states + M₂.states) = cfg3.state_idx := by
        show s + (M₁.states + M₂.states) - (M₁.states + M₂.states) = s
        exact Nat.add_sub_cancel _ _
      have h_cfg_eq :
          { state_idx := cfg.state_idx - (M₁.states + M₂.states),
            tapes := cfg.tapes } = cfg3 := by
        rw [h_sub]
      rw [applyTransitionEntry_shiftEntry, h_cfg_eq]

/-- Halt bit on a shifted M₂-state, lifted to use a `cfg2 : FlatTMConfig`
form. (Re-export of `branchComposeFlatTM_haltingStateReached_M2` with
the more usable form.) -/
private theorem branchComposeFlatTM_haltingStateReached_M2_phase
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat)
    (h₂ : validFlatTM M₂) (cfg2 : FlatTMConfig)
    (h_s : cfg2.state_idx < M₂.states) :
    haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
        { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } =
      haltingStateReached M₂ cfg2 :=
  branchComposeFlatTM_haltingStateReached_M2 M₁ M₂ M₃ exit_pos exit_neg h₂
    cfg2.state_idx h_s cfg2.tapes

/-- Halt bit on a shifted M₃-state, lifted to use a `cfg3 : FlatTMConfig`
form. -/
private theorem branchComposeFlatTM_haltingStateReached_M3_phase
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat)
    (h₂ : validFlatTM M₂) (cfg3 : FlatTMConfig) :
    haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
        { state_idx := cfg3.state_idx + (M₁.states + M₂.states), tapes := cfg3.tapes } =
      haltingStateReached M₃ cfg3 :=
  branchComposeFlatTM_haltingStateReached_M3 M₁ M₂ M₃ exit_pos exit_neg h₂
    cfg3.state_idx cfg3.tapes

/-! ### M₁/M₂/M₃ phase run lemmas for `branchComposeFlatTM`

These lift the respective sub-TM's `n`-step run into the composed
machine's run. The M₁ phase requires a trajectory invariant: M₁
doesn't halt and doesn't pass through either exit during the first
`n - 1` steps. -/

/-- Lift M₁'s `n`-step run to the branched-composed machine. -/
private theorem runFlatTM_branchComposeFlatTM_M1_phase
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat) (h_validM1 : validFlatTM M₁) :
    ∀ (n : Nat) (cfg : FlatTMConfig),
      cfg.state_idx < M₁.states →
      (∀ k, k < n → ∀ ck, runFlatTM k M₁ cfg = some ck →
         ck.state_idx ≠ exit_pos ∧ ck.state_idx ≠ exit_neg ∧
         haltingStateReached M₁ ck = false) →
      runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg =
        runFlatTM n M₁ cfg
  | 0, _, _, _ => rfl
  | n + 1, cfg, h_state_lt, h_traj => by
      have h_k0 := h_traj 0 (Nat.zero_lt_succ _) cfg rfl
      have h_state_ne_pos_cfg : cfg.state_idx ≠ exit_pos := h_k0.1
      have h_state_ne_neg_cfg : cfg.state_idx ≠ exit_neg := h_k0.2.1
      have h_halt_false_cfg : haltingStateReached M₁ cfg = false := h_k0.2.2
      have h_halt_composed_false :
          haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg = false :=
        branchComposeFlatTM_haltingStateReached_M1 M₁ M₂ M₃ exit_pos exit_neg cfg h_state_lt
      have h_step_eq :
          stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg =
            stepFlatTM M₁ cfg :=
        stepFlatTM_branchComposeFlatTM_M1 M₁ M₂ M₃ exit_pos exit_neg cfg h_state_lt
          h_state_ne_pos_cfg h_state_ne_neg_cfg
      have h_unfold_M1 :
          runFlatTM (n + 1) M₁ cfg =
            match stepFlatTM M₁ cfg with
            | none => some cfg
            | some cfg' => runFlatTM n M₁ cfg' := by
        show (if haltingStateReached M₁ cfg = true then some cfg
              else match stepFlatTM M₁ cfg with
                | none => some cfg
                | some cfg' => runFlatTM n M₁ cfg') = _
        rw [if_neg (by rw [h_halt_false_cfg]; decide)]
      have h_unfold_composed :
          runFlatTM (n + 1) (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg =
            match stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg with
            | none => some cfg
            | some cfg' =>
                runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg' := by
        show (if haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg
                = true then some cfg
              else match stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg with
                | none => some cfg
                | some cfg' =>
                    runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg') = _
        rw [if_neg (by rw [h_halt_composed_false]; decide)]
      rw [h_unfold_M1, h_unfold_composed, h_step_eq]
      cases h_step : stepFlatTM M₁ cfg with
      | none => rfl
      | some cfg' =>
          have h_cfg'_lt : cfg'.state_idx < M₁.states :=
            state_idx_lt_states_of_step M₁ h_validM1 cfg cfg' h_step
          have h_traj_shift : ∀ k, k < n → ∀ ck,
              runFlatTM k M₁ cfg' = some ck →
              ck.state_idx ≠ exit_pos ∧ ck.state_idx ≠ exit_neg ∧
              haltingStateReached M₁ ck = false := by
            intro k hk ck h_run
            have h_chain : runFlatTM (k + 1) M₁ cfg = some ck := by
              have h_unfold :
                  runFlatTM (k + 1) M₁ cfg =
                    match stepFlatTM M₁ cfg with
                    | none => some cfg
                    | some cfg'' => runFlatTM k M₁ cfg'' := by
                show (if haltingStateReached M₁ cfg = true then some cfg
                      else match stepFlatTM M₁ cfg with
                        | none => some cfg
                        | some cfg'' => runFlatTM k M₁ cfg'') = _
                rw [if_neg (by rw [h_halt_false_cfg]; decide)]
              rw [h_unfold, h_step]; exact h_run
            exact h_traj (k + 1) (Nat.succ_lt_succ hk) ck h_chain
          exact runFlatTM_branchComposeFlatTM_M1_phase M₁ M₂ M₃ exit_pos exit_neg h_validM1
            n cfg' h_cfg'_lt h_traj_shift
  termination_by n _ _ _ => n

/-- Lift M₂'s `n`-step run from `cfg2` to the branched-composed machine
running from the shifted config `{ state_idx := cfg2.state_idx + M₁.states,
tapes := cfg2.tapes }`. -/
private theorem runFlatTM_branchComposeFlatTM_M2_phase
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat)
    (h_validM1 : validFlatTM M₁) (h_validM2 : validFlatTM M₂)
    (h_validM3 : validFlatTM M₃)
    (h_exit_pos_lt : exit_pos < M₁.states) (h_exit_neg_lt : exit_neg < M₁.states) :
    ∀ (n : Nat) (cfg2 : FlatTMConfig),
      cfg2.state_idx < M₂.states →
      runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
          { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } =
        (runFlatTM n M₂ cfg2).map
          (fun c => { state_idx := c.state_idx + M₁.states, tapes := c.tapes })
  | 0, cfg2, _ => rfl
  | n + 1, cfg2, h_state_lt => by
      have h_halt_eq :
          haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
              { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } =
            haltingStateReached M₂ cfg2 :=
        branchComposeFlatTM_haltingStateReached_M2_phase M₁ M₂ M₃ exit_pos exit_neg
          h_validM2 cfg2 h_state_lt
      by_cases h_halt : haltingStateReached M₂ cfg2 = true
      · have h_halt_c : haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
            { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } = true := by
          rw [h_halt_eq]; exact h_halt
        rw [runFlatTM_of_halting _ _ (n + 1) h_halt_c,
            runFlatTM_of_halting _ _ (n + 1) h_halt]
        rfl
      · have h_halt_false : haltingStateReached M₂ cfg2 = false := by
          cases h : haltingStateReached M₂ cfg2 with
          | true => exact absurd h h_halt
          | false => rfl
        have h_halt_c_false :
            haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
              { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } = false := by
          rw [h_halt_eq]; exact h_halt_false
        have h_step_eq :
            stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } =
              (stepFlatTM M₂ cfg2).map
                (fun c => { state_idx := c.state_idx + M₁.states, tapes := c.tapes }) := by
          have := stepFlatTM_branchComposeFlatTM_M2 M₁ M₂ M₃ exit_pos exit_neg cfg2.state_idx
            cfg2.tapes h_validM1 h_validM3 h_exit_pos_lt h_exit_neg_lt h_state_lt
          convert this using 2
        have h_unfold_M2 :
            runFlatTM (n + 1) M₂ cfg2 =
              match stepFlatTM M₂ cfg2 with
              | none => some cfg2
              | some cfg2' => runFlatTM n M₂ cfg2' := by
          show (if haltingStateReached M₂ cfg2 = true then some cfg2
                else match stepFlatTM M₂ cfg2 with
                  | none => some cfg2
                  | some cfg2' => runFlatTM n M₂ cfg2') = _
          rw [if_neg (by rw [h_halt_false]; decide)]
        have h_unfold_C :
            runFlatTM (n + 1) (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } =
              match stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                  { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } with
              | none => some { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes }
              | some cfg' =>
                  runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg' := by
          show (if haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                    { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } = true
                then some { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes }
                else match stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                    { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes } with
                  | none =>
                      some { state_idx := cfg2.state_idx + M₁.states, tapes := cfg2.tapes }
                  | some cfg' =>
                      runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg') = _
          rw [if_neg (by rw [h_halt_c_false]; decide)]
        rw [h_unfold_M2, h_unfold_C, h_step_eq]
        cases h_step : stepFlatTM M₂ cfg2 with
        | none => rfl
        | some cfg2' =>
            have h_cfg2'_lt : cfg2'.state_idx < M₂.states :=
              state_idx_lt_states_of_step M₂ h_validM2 cfg2 cfg2' h_step
            show runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                  { state_idx := cfg2'.state_idx + M₁.states, tapes := cfg2'.tapes } = _
            exact runFlatTM_branchComposeFlatTM_M2_phase M₁ M₂ M₃ exit_pos exit_neg
              h_validM1 h_validM2 h_validM3 h_exit_pos_lt h_exit_neg_lt
              n cfg2' h_cfg2'_lt
  termination_by n _ _ => n

/-- Lift M₃'s `n`-step run from `cfg3` to the branched-composed machine
running from the shifted config `{ state_idx := cfg3.state_idx +
(M₁.states + M₂.states), tapes := cfg3.tapes }`. -/
private theorem runFlatTM_branchComposeFlatTM_M3_phase
    (M₁ M₂ M₃ : FlatTM) (exit_pos exit_neg : Nat)
    (h_validM1 : validFlatTM M₁) (h_validM2 : validFlatTM M₂)
    (h_validM3 : validFlatTM M₃)
    (h_exit_pos_lt : exit_pos < M₁.states) (h_exit_neg_lt : exit_neg < M₁.states) :
    ∀ (n : Nat) (cfg3 : FlatTMConfig),
      runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
          { state_idx := cfg3.state_idx + (M₁.states + M₂.states), tapes := cfg3.tapes } =
        (runFlatTM n M₃ cfg3).map
          (fun c => { state_idx := c.state_idx + (M₁.states + M₂.states),
                      tapes := c.tapes })
  | 0, cfg3 => rfl
  | n + 1, cfg3 => by
      have h_halt_eq :
          haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
              { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
                tapes := cfg3.tapes } =
            haltingStateReached M₃ cfg3 :=
        branchComposeFlatTM_haltingStateReached_M3_phase M₁ M₂ M₃ exit_pos exit_neg
          h_validM2 cfg3
      by_cases h_halt : haltingStateReached M₃ cfg3 = true
      · have h_halt_c : haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
            { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
              tapes := cfg3.tapes } = true := by
          rw [h_halt_eq]; exact h_halt
        rw [runFlatTM_of_halting _ _ (n + 1) h_halt_c,
            runFlatTM_of_halting _ _ (n + 1) h_halt]
        rfl
      · have h_halt_false : haltingStateReached M₃ cfg3 = false := by
          cases h : haltingStateReached M₃ cfg3 with
          | true => exact absurd h h_halt
          | false => rfl
        have h_halt_c_false :
            haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
              { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
                tapes := cfg3.tapes } = false := by
          rw [h_halt_eq]; exact h_halt_false
        have h_step_eq :
            stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
                  tapes := cfg3.tapes } =
              (stepFlatTM M₃ cfg3).map
                (fun c => { state_idx := c.state_idx + (M₁.states + M₂.states),
                            tapes := c.tapes }) := by
          have := stepFlatTM_branchComposeFlatTM_M3 M₁ M₂ M₃ exit_pos exit_neg cfg3.state_idx
            cfg3.tapes h_validM1 h_validM2 h_exit_pos_lt h_exit_neg_lt
          convert this using 2
        have h_unfold_M3 :
            runFlatTM (n + 1) M₃ cfg3 =
              match stepFlatTM M₃ cfg3 with
              | none => some cfg3
              | some cfg3' => runFlatTM n M₃ cfg3' := by
          show (if haltingStateReached M₃ cfg3 = true then some cfg3
                else match stepFlatTM M₃ cfg3 with
                  | none => some cfg3
                  | some cfg3' => runFlatTM n M₃ cfg3') = _
          rw [if_neg (by rw [h_halt_false]; decide)]
        have h_unfold_C :
            runFlatTM (n + 1) (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
                  tapes := cfg3.tapes } =
              match stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                  { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
                    tapes := cfg3.tapes } with
              | none =>
                  some { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
                         tapes := cfg3.tapes }
              | some cfg' =>
                  runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg' := by
          show (if haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                    { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
                      tapes := cfg3.tapes } = true
                then some { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
                            tapes := cfg3.tapes }
                else match stepFlatTM (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                    { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
                      tapes := cfg3.tapes } with
                  | none =>
                      some { state_idx := cfg3.state_idx + (M₁.states + M₂.states),
                             tapes := cfg3.tapes }
                  | some cfg' =>
                      runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg') = _
          rw [if_neg (by rw [h_halt_c_false]; decide)]
        rw [h_unfold_M3, h_unfold_C, h_step_eq]
        cases h_step : stepFlatTM M₃ cfg3 with
        | none => rfl
        | some cfg3' =>
            show runFlatTM n (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
                  { state_idx := cfg3'.state_idx + (M₁.states + M₂.states),
                    tapes := cfg3'.tapes } = _
            exact runFlatTM_branchComposeFlatTM_M3_phase M₁ M₂ M₃ exit_pos exit_neg
              h_validM1 h_validM2 h_validM3 h_exit_pos_lt h_exit_neg_lt n cfg3'
  termination_by n _ => n

/-! ### Final composition lemmas for `branchComposeFlatTM` -/

/-- **Operational correctness of `branchComposeFlatTM` — positive
branch.**

If `M₁` (single-tape, valid) starts at `cfg0` and after `t₁` steps
reaches `c₁ = { state_idx := exit_pos, tapes := [(left, head, right)] }`
without halting prematurely *and without passing through `exit_neg`*
in any of the first `t₁` steps, and `M₂` (single-tape, valid) starts
at `{ state_idx := M₂.start, tapes := c₁.tapes }` and after `t₂` steps
halts at `c₂`, then `branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg`
starting at `cfg0` reaches the M₂-shifted `c₂` in exactly
`t₁ + 1 + t₂` steps and that shifted config is a halting state of the
composed machine. -/
theorem branchComposeFlatTM_run_pos
    {M₁ M₂ M₃ : FlatTM} {exit_pos exit_neg : Nat}
    (h_exit_neq : exit_pos ≠ exit_neg)
    (h_validM1 : validFlatTM M₁) (h_validM2 : validFlatTM M₂)
    (h_validM3 : validFlatTM M₃)
    (h_exit_pos_lt : exit_pos < M₁.states)
    (h_exit_neg_lt : exit_neg < M₁.states)
    (cfg0 : FlatTMConfig) (h_cfg0_state_lt : cfg0.state_idx < M₁.states)
    (left₁ : List Nat) (head₁ : Nat) (right₁ : List Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left₁, head₁, right₁) = some v →
                          v < max M₁.sig (max M₂.sig M₃.sig))
    {t₁ t₂ : Nat} {c₂ : FlatTMConfig}
    (h_run1 : runFlatTM t₁ M₁ cfg0 =
              some { state_idx := exit_pos, tapes := [(left₁, head₁, right₁)] })
    (h_traj1 : ∀ k, k < t₁ → ∀ ck, runFlatTM k M₁ cfg0 = some ck →
       ck.state_idx ≠ exit_pos ∧ ck.state_idx ≠ exit_neg ∧
       haltingStateReached M₁ ck = false)
    (h_run2 : runFlatTM t₂ M₂
                { state_idx := M₂.start,
                  tapes := [(left₁, head₁, right₁)] } = some c₂)
    (h_halt2 : haltingStateReached M₂ c₂ = true) :
    runFlatTM (t₁ + 1 + t₂) (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg0 =
      some { state_idx := c₂.state_idx + M₁.states, tapes := c₂.tapes } ∧
    haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
      { state_idx := c₂.state_idx + M₁.states, tapes := c₂.tapes } = true := by
  have h_c2_state_lt : c₂.state_idx < M₂.states :=
    state_idx_lt_states_of_run M₂ h_validM2 t₂ _ c₂ h_validM2.1 h_run2
  refine ⟨?_, ?_⟩
  · -- The shifted halt check.
    -- Phase 1: M₁ phase.
    have h_traj1' : ∀ k, k < t₁ → ∀ ck, runFlatTM k M₁ cfg0 = some ck →
        ck.state_idx ≠ exit_pos ∧ ck.state_idx ≠ exit_neg ∧
        haltingStateReached M₁ ck = false := h_traj1
    have h_phase1 :=
      runFlatTM_branchComposeFlatTM_M1_phase M₁ M₂ M₃ exit_pos exit_neg h_validM1
        t₁ cfg0 h_cfg0_state_lt h_traj1'
    rw [← h_phase1] at h_run1
    -- Phase 2: bridge step.
    have h_bridge :=
      stepFlatTM_branchComposeFlatTM_bridge_pos M₁ M₂ M₃ exit_pos exit_neg
        left₁ right₁ head₁ h_sym_bound
    have h_phase12 :
        runFlatTM (t₁ + 1) (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg0 =
          some { state_idx := M₁.states + M₂.start,
                 tapes := [(left₁, head₁, right₁)] } := by
      apply runFlatTM_extend_by_step _ t₁ cfg0 _ _ h_run1 ?_ h_bridge
      -- The exit_pos config is non-halting in the composed machine.
      exact branchComposeFlatTM_haltingStateReached_M1 M₁ M₂ M₃ exit_pos exit_neg _
        h_exit_pos_lt
    -- Phase 3: M₂ phase.
    set cfg2_start : FlatTMConfig :=
      { state_idx := M₂.start, tapes := [(left₁, head₁, right₁)] }
    have h_phase3 :=
      runFlatTM_branchComposeFlatTM_M2_phase M₁ M₂ M₃ exit_pos exit_neg
        h_validM1 h_validM2 h_validM3 h_exit_pos_lt h_exit_neg_lt t₂ cfg2_start
        h_validM2.1
    rw [h_run2] at h_phase3
    have h_state_swap : M₂.start + M₁.states = M₁.states + M₂.start := Nat.add_comm _ _
    rw [show t₁ + 1 + t₂ = (t₁ + 1) + t₂ from rfl,
        runFlatTM_compose _ (t₁ + 1) t₂ _ _ h_phase12]
    have h_target :
        runFlatTM t₂ (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
            { state_idx := M₁.states + M₂.start,
              tapes := [(left₁, head₁, right₁)] } =
          some { state_idx := c₂.state_idx + M₁.states, tapes := c₂.tapes } := by
      have h_eq : { state_idx := M₂.start + M₁.states,
                    tapes := [(left₁, head₁, right₁)] } =
          ({ state_idx := M₁.states + M₂.start,
             tapes := [(left₁, head₁, right₁)] } : FlatTMConfig) := by
        rw [h_state_swap]
      rw [← h_eq]
      rw [h_phase3]
      rfl
    exact h_target
  · -- Halt of the result.
    have := branchComposeFlatTM_haltingStateReached_M2_phase M₁ M₂ M₃ exit_pos exit_neg
      h_validM2 c₂ h_c2_state_lt
    rw [this]; exact h_halt2

/-- **Operational correctness of `branchComposeFlatTM` — negative
branch.**

Symmetric to `branchComposeFlatTM_run_pos`, but the M₁ trajectory
ends at `exit_neg` and the post-bridge phase runs `M₃` instead of
`M₂`. The result state is shifted by `M₁.states + M₂.states`. -/
theorem branchComposeFlatTM_run_neg
    {M₁ M₂ M₃ : FlatTM} {exit_pos exit_neg : Nat}
    (h_exit_neq : exit_pos ≠ exit_neg)
    (h_validM1 : validFlatTM M₁) (h_validM2 : validFlatTM M₂)
    (h_validM3 : validFlatTM M₃)
    (h_exit_pos_lt : exit_pos < M₁.states)
    (h_exit_neg_lt : exit_neg < M₁.states)
    (cfg0 : FlatTMConfig) (h_cfg0_state_lt : cfg0.state_idx < M₁.states)
    (left₁ : List Nat) (head₁ : Nat) (right₁ : List Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left₁, head₁, right₁) = some v →
                          v < max M₁.sig (max M₂.sig M₃.sig))
    {t₁ t₂ : Nat} {c₃ : FlatTMConfig}
    (h_run1 : runFlatTM t₁ M₁ cfg0 =
              some { state_idx := exit_neg, tapes := [(left₁, head₁, right₁)] })
    (h_traj1 : ∀ k, k < t₁ → ∀ ck, runFlatTM k M₁ cfg0 = some ck →
       ck.state_idx ≠ exit_pos ∧ ck.state_idx ≠ exit_neg ∧
       haltingStateReached M₁ ck = false)
    (h_run3 : runFlatTM t₂ M₃
                { state_idx := M₃.start,
                  tapes := [(left₁, head₁, right₁)] } = some c₃)
    (h_halt3 : haltingStateReached M₃ c₃ = true) :
    runFlatTM (t₁ + 1 + t₂) (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg0 =
      some { state_idx := c₃.state_idx + (M₁.states + M₂.states),
             tapes := c₃.tapes } ∧
    haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
      { state_idx := c₃.state_idx + (M₁.states + M₂.states),
        tapes := c₃.tapes } = true := by
  refine ⟨?_, ?_⟩
  · -- Phase 1: M₁ phase.
    have h_phase1 :=
      runFlatTM_branchComposeFlatTM_M1_phase M₁ M₂ M₃ exit_pos exit_neg h_validM1
        t₁ cfg0 h_cfg0_state_lt h_traj1
    rw [← h_phase1] at h_run1
    -- Phase 2: bridge step (neg).
    have h_bridge :=
      stepFlatTM_branchComposeFlatTM_bridge_neg M₁ M₂ M₃ exit_pos exit_neg h_exit_neq
        left₁ right₁ head₁ h_sym_bound
    have h_phase12 :
        runFlatTM (t₁ + 1) (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg0 =
          some { state_idx := M₁.states + M₂.states + M₃.start,
                 tapes := [(left₁, head₁, right₁)] } := by
      apply runFlatTM_extend_by_step _ t₁ cfg0 _ _ h_run1 ?_ h_bridge
      exact branchComposeFlatTM_haltingStateReached_M1 M₁ M₂ M₃ exit_pos exit_neg _
        h_exit_neg_lt
    -- Phase 3: M₃ phase.
    set cfg3_start : FlatTMConfig :=
      { state_idx := M₃.start, tapes := [(left₁, head₁, right₁)] }
    have h_phase3 :=
      runFlatTM_branchComposeFlatTM_M3_phase M₁ M₂ M₃ exit_pos exit_neg
        h_validM1 h_validM2 h_validM3 h_exit_pos_lt h_exit_neg_lt t₂ cfg3_start
    rw [h_run3] at h_phase3
    -- Note: M₃.start + (M₁.states + M₂.states) = M₁.states + M₂.states + M₃.start.
    have h_state_swap :
        M₃.start + (M₁.states + M₂.states) = M₁.states + M₂.states + M₃.start :=
      Nat.add_comm _ _
    rw [show t₁ + 1 + t₂ = (t₁ + 1) + t₂ from rfl,
        runFlatTM_compose _ (t₁ + 1) t₂ _ _ h_phase12]
    have h_target :
        runFlatTM t₂ (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg)
            { state_idx := M₁.states + M₂.states + M₃.start,
              tapes := [(left₁, head₁, right₁)] } =
          some { state_idx := c₃.state_idx + (M₁.states + M₂.states),
                 tapes := c₃.tapes } := by
      have h_eq : { state_idx := M₃.start + (M₁.states + M₂.states),
                    tapes := [(left₁, head₁, right₁)] } =
          ({ state_idx := M₁.states + M₂.states + M₃.start,
             tapes := [(left₁, head₁, right₁)] } : FlatTMConfig) := by
        rw [h_state_swap]
      rw [← h_eq]
      rw [h_phase3]
      rfl
    exact h_target
  · -- Halt of the result.
    have := branchComposeFlatTM_haltingStateReached_M3_phase M₁ M₂ M₃ exit_pos exit_neg
      h_validM2 c₃
    rw [this]; exact h_halt3

/-- **No-early-halt trajectory of `branchComposeFlatTM` — positive branch.** The
branch analogue of `composeFlatTM_no_early_halt`: from the two component
trajectories (M₁ never halts / hits an exit, M₂ never halts), the composite never
halts during the first `t₁ + 1 + t₂` steps when M₁ exits at `exit_pos` (so M₂
runs). The `h_traj1` consumed by an *outer* `loopTM`/composition. -/
theorem branchComposeFlatTM_no_early_halt_pos
    {M₁ M₂ M₃ : FlatTM} {exit_pos exit_neg : Nat}
    (h_validM1 : validFlatTM M₁) (h_validM2 : validFlatTM M₂) (h_validM3 : validFlatTM M₃)
    (h_exit_pos_lt : exit_pos < M₁.states) (h_exit_neg_lt : exit_neg < M₁.states)
    (cfg0 : FlatTMConfig) (h_cfg0_state_lt : cfg0.state_idx < M₁.states)
    (left₁ : List Nat) (head₁ : Nat) (right₁ : List Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left₁, head₁, right₁) = some v →
                          v < max M₁.sig (max M₂.sig M₃.sig))
    {t₁ t₂ : Nat}
    (h_run1 : runFlatTM t₁ M₁ cfg0 =
              some { state_idx := exit_pos, tapes := [(left₁, head₁, right₁)] })
    (h_traj1 : ∀ k, k < t₁ → ∀ ck, runFlatTM k M₁ cfg0 = some ck →
       ck.state_idx ≠ exit_pos ∧ ck.state_idx ≠ exit_neg ∧ haltingStateReached M₁ ck = false)
    (h_traj2 : ∀ k, k < t₂ → ∀ ck,
       runFlatTM k M₂ { state_idx := M₂.start, tapes := [(left₁, head₁, right₁)] } = some ck →
       haltingStateReached M₂ ck = false) :
    ∀ k, k < t₁ + 1 + t₂ → ∀ ck,
      runFlatTM k (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg0 = some ck →
      haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) ck = false := by
  intro k hk ck hck
  by_cases hkle : k ≤ t₁
  · have h_traj1' : ∀ j, j < k → ∀ cj, runFlatTM j M₁ cfg0 = some cj →
        cj.state_idx ≠ exit_pos ∧ cj.state_idx ≠ exit_neg ∧ haltingStateReached M₁ cj = false :=
      fun j hj cj hcj => h_traj1 j (Nat.lt_of_lt_of_le hj hkle) cj hcj
    have h_eq := runFlatTM_branchComposeFlatTM_M1_phase M₁ M₂ M₃ exit_pos exit_neg h_validM1 k cfg0
      h_cfg0_state_lt h_traj1'
    rw [h_eq] at hck
    have hck_lt : ck.state_idx < M₁.states :=
      state_idx_lt_states_of_run M₁ h_validM1 k cfg0 ck h_cfg0_state_lt hck
    exact branchComposeFlatTM_haltingStateReached_M1 M₁ M₂ M₃ exit_pos exit_neg ck hck_lt
  · push_neg at hkle
    obtain ⟨j, rfl⟩ : ∃ j, k = (t₁ + 1) + j := ⟨k - (t₁ + 1), by omega⟩
    have hj_lt : j < t₂ := by omega
    have h_phase1 := runFlatTM_branchComposeFlatTM_M1_phase M₁ M₂ M₃ exit_pos exit_neg h_validM1
      t₁ cfg0 h_cfg0_state_lt h_traj1
    have h_run1' : runFlatTM t₁ (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg0 =
        some { state_idx := exit_pos, tapes := [(left₁, head₁, right₁)] } := by
      rw [h_phase1]; exact h_run1
    have h_bridge := stepFlatTM_branchComposeFlatTM_bridge_pos M₁ M₂ M₃ exit_pos exit_neg
      left₁ right₁ head₁ h_sym_bound
    have h_phase12 : runFlatTM (t₁ + 1) (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg0 =
        some { state_idx := M₁.states + M₂.start, tapes := [(left₁, head₁, right₁)] } := by
      apply runFlatTM_extend_by_step _ t₁ cfg0 _ _ h_run1' ?_ h_bridge
      exact branchComposeFlatTM_haltingStateReached_M1 M₁ M₂ M₃ exit_pos exit_neg _ h_exit_pos_lt
    rw [runFlatTM_compose _ (t₁ + 1) j cfg0 _ h_phase12] at hck
    set cfg2_start : FlatTMConfig :=
      { state_idx := M₂.start, tapes := [(left₁, head₁, right₁)] }
    have h_phase_j := runFlatTM_branchComposeFlatTM_M2_phase M₁ M₂ M₃ exit_pos exit_neg
      h_validM1 h_validM2 h_validM3 h_exit_pos_lt h_exit_neg_lt j cfg2_start h_validM2.1
    have h_cfg_eq :
        ({ state_idx := M₂.start + M₁.states, tapes := [(left₁, head₁, right₁)] } : FlatTMConfig) =
        { state_idx := M₁.states + M₂.start, tapes := [(left₁, head₁, right₁)] } := by
      rw [Nat.add_comm M₂.start M₁.states]
    rw [← h_cfg_eq, h_phase_j] at hck
    cases hjm : runFlatTM j M₂ cfg2_start with
    | none => rw [hjm] at hck; simp at hck
    | some cj =>
        rw [hjm] at hck; simp only [Option.map_some] at hck
        have hck_eq : ck = { state_idx := cj.state_idx + M₁.states, tapes := cj.tapes } :=
          (Option.some.inj hck).symm
        have hcj_lt : cj.state_idx < M₂.states :=
          state_idx_lt_states_of_run M₂ h_validM2 j cfg2_start cj h_validM2.1 hjm
        have hcj_nothalt : haltingStateReached M₂ cj = false := h_traj2 j hj_lt cj hjm
        rw [hck_eq, branchComposeFlatTM_haltingStateReached_M2 M₁ M₂ M₃ exit_pos exit_neg
          h_validM2 cj.state_idx hcj_lt cj.tapes]
        exact hcj_nothalt

/-- **No-early-halt trajectory of `branchComposeFlatTM` — negative branch.** -/
theorem branchComposeFlatTM_no_early_halt_neg
    {M₁ M₂ M₃ : FlatTM} {exit_pos exit_neg : Nat}
    (h_exit_neq : exit_pos ≠ exit_neg)
    (h_validM1 : validFlatTM M₁) (h_validM2 : validFlatTM M₂) (h_validM3 : validFlatTM M₃)
    (h_exit_pos_lt : exit_pos < M₁.states) (h_exit_neg_lt : exit_neg < M₁.states)
    (cfg0 : FlatTMConfig) (h_cfg0_state_lt : cfg0.state_idx < M₁.states)
    (left₁ : List Nat) (head₁ : Nat) (right₁ : List Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left₁, head₁, right₁) = some v →
                          v < max M₁.sig (max M₂.sig M₃.sig))
    {t₁ t₂ : Nat}
    (h_run1 : runFlatTM t₁ M₁ cfg0 =
              some { state_idx := exit_neg, tapes := [(left₁, head₁, right₁)] })
    (h_traj1 : ∀ k, k < t₁ → ∀ ck, runFlatTM k M₁ cfg0 = some ck →
       ck.state_idx ≠ exit_pos ∧ ck.state_idx ≠ exit_neg ∧ haltingStateReached M₁ ck = false)
    (h_traj3 : ∀ k, k < t₂ → ∀ ck,
       runFlatTM k M₃ { state_idx := M₃.start, tapes := [(left₁, head₁, right₁)] } = some ck →
       haltingStateReached M₃ ck = false) :
    ∀ k, k < t₁ + 1 + t₂ → ∀ ck,
      runFlatTM k (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg0 = some ck →
      haltingStateReached (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) ck = false := by
  intro k hk ck hck
  by_cases hkle : k ≤ t₁
  · have h_traj1' : ∀ j, j < k → ∀ cj, runFlatTM j M₁ cfg0 = some cj →
        cj.state_idx ≠ exit_pos ∧ cj.state_idx ≠ exit_neg ∧ haltingStateReached M₁ cj = false :=
      fun j hj cj hcj => h_traj1 j (Nat.lt_of_lt_of_le hj hkle) cj hcj
    have h_eq := runFlatTM_branchComposeFlatTM_M1_phase M₁ M₂ M₃ exit_pos exit_neg h_validM1 k cfg0
      h_cfg0_state_lt h_traj1'
    rw [h_eq] at hck
    have hck_lt : ck.state_idx < M₁.states :=
      state_idx_lt_states_of_run M₁ h_validM1 k cfg0 ck h_cfg0_state_lt hck
    exact branchComposeFlatTM_haltingStateReached_M1 M₁ M₂ M₃ exit_pos exit_neg ck hck_lt
  · push_neg at hkle
    obtain ⟨j, rfl⟩ : ∃ j, k = (t₁ + 1) + j := ⟨k - (t₁ + 1), by omega⟩
    have hj_lt : j < t₂ := by omega
    have h_phase1 := runFlatTM_branchComposeFlatTM_M1_phase M₁ M₂ M₃ exit_pos exit_neg h_validM1
      t₁ cfg0 h_cfg0_state_lt h_traj1
    have h_run1' : runFlatTM t₁ (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg0 =
        some { state_idx := exit_neg, tapes := [(left₁, head₁, right₁)] } := by
      rw [h_phase1]; exact h_run1
    have h_bridge := stepFlatTM_branchComposeFlatTM_bridge_neg M₁ M₂ M₃ exit_pos exit_neg
      h_exit_neq left₁ right₁ head₁ h_sym_bound
    have h_phase12 : runFlatTM (t₁ + 1) (branchComposeFlatTM M₁ M₂ M₃ exit_pos exit_neg) cfg0 =
        some { state_idx := M₁.states + M₂.states + M₃.start, tapes := [(left₁, head₁, right₁)] } := by
      apply runFlatTM_extend_by_step _ t₁ cfg0 _ _ h_run1' ?_ h_bridge
      exact branchComposeFlatTM_haltingStateReached_M1 M₁ M₂ M₃ exit_pos exit_neg _ h_exit_neg_lt
    rw [runFlatTM_compose _ (t₁ + 1) j cfg0 _ h_phase12] at hck
    set cfg3_start : FlatTMConfig :=
      { state_idx := M₃.start, tapes := [(left₁, head₁, right₁)] }
    have h_phase_j := runFlatTM_branchComposeFlatTM_M3_phase M₁ M₂ M₃ exit_pos exit_neg
      h_validM1 h_validM2 h_validM3 h_exit_pos_lt h_exit_neg_lt j cfg3_start
    have h_cfg_eq :
        ({ state_idx := M₃.start + (M₁.states + M₂.states),
           tapes := [(left₁, head₁, right₁)] } : FlatTMConfig) =
        { state_idx := M₁.states + M₂.states + M₃.start, tapes := [(left₁, head₁, right₁)] } := by
      rw [Nat.add_comm M₃.start (M₁.states + M₂.states)]
    rw [← h_cfg_eq, h_phase_j] at hck
    cases hjm : runFlatTM j M₃ cfg3_start with
    | none => rw [hjm] at hck; simp at hck
    | some cj =>
        rw [hjm] at hck; simp only [Option.map_some] at hck
        have hck_eq : ck = { state_idx := cj.state_idx + (M₁.states + M₂.states), tapes := cj.tapes } :=
          (Option.some.inj hck).symm
        have hcj_nothalt : haltingStateReached M₃ cj = false := h_traj3 j hj_lt cj hjm
        rw [hck_eq, branchComposeFlatTM_haltingStateReached_M3 M₁ M₂ M₃ exit_pos exit_neg
          h_validM2 cj.state_idx cj.tapes]
        exact hcj_nothalt

/-! ## Step 4 — atomic Bool-output TMs

The simplest non-vacuous deciders: a TM that always halts in the
accept state, and one that always halts in the reject state. We use
them both for sanity checks of the framework and as building blocks
later (e.g. the two sides of a conditional jump).

We adopt a 3-state convention for these "verdict" machines so they
fit `DecidesBy`'s `acceptState ≠ rejectState` requirement:

- state 0 = start (non-halting).
- state 1 = accept-halt.
- state 2 = reject-halt.

A single bridge transition `(0, none) → (1, none, Nmove)` (or to `2`)
is enough because the standard encoding for these deciders is the
empty tape, so the current symbol is always `none`. -/

/-- A 3-state, single-tape FlatTM that on the empty tape steps once
from state 0 into either state 1 (`verdict = true`) or state 2
(`verdict = false`), and halts there. The alphabet is `sig`. -/
def verdictTM (sig : Nat) (verdict : Bool) : FlatTM where
  sig := sig
  tapes := 1
  states := 3
  trans := bridgeEntries sig 0 (if verdict then 1 else 2)
  start := 0
  halt := [false, true, true]

theorem verdictTM_valid (sig : Nat) (verdict : Bool) :
    validFlatTM (verdictTM sig verdict) := by
  refine ⟨?_, ?_, ?_⟩
  · -- start = 0 < 3
    show 0 < 3
    decide
  · -- halt.length = states
    show [false, true, true].length = 3
    rfl
  · -- every transition is valid
    intro entry hentry
    have hentry' : entry ∈ bridgeEntries sig 0 (if verdict then 1 else 2) := hentry
    obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ :=
      bridgeEntries_mem hentry'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- src_state = 0 < 3
      show entry.src_state < (verdictTM sig verdict).states
      rw [hsrc]
      show 0 < 3
      decide
    · -- dst_state = (if verdict then 1 else 2) < 3
      show entry.dst_state < (verdictTM sig verdict).states
      rw [hdst]
      show (if verdict then 1 else 2) < 3
      cases verdict with
      | false =>
          show 2 < 3
          decide
      | true =>
          show 1 < 3
          decide
    · show entry.src_tape_vals.length = (verdictTM sig verdict).tapes
      rw [hsrcLen]; rfl
    · show entry.dst_write_vals.length = (verdictTM sig verdict).tapes
      rw [hdstLen]; rfl
    · show entry.move_dirs.length = (verdictTM sig verdict).tapes
      rw [hmovLen]; rfl
    · show flatTMOptionSymbolsBounded (verdictTM sig verdict).sig entry.src_tape_vals
      exact hsymSrc
    · show flatTMOptionSymbolsBounded (verdictTM sig verdict).sig entry.dst_write_vals
      exact hsymDst

/-- The expected halting configuration after one step of `verdictTM`. -/
def verdictTM_finalConfig (verdict : Bool) : FlatTMConfig :=
  { state_idx := if verdict then 1 else 2
    tapes := [([], 0, [])] }

/-- One-step trace of `verdictTM` on the empty tape. -/
theorem verdictTM_run_one (sig : Nat) (verdict : Bool) :
    runFlatTM 1 (verdictTM sig verdict)
        (initFlatConfig (verdictTM sig verdict) [[]]) =
      some (verdictTM_finalConfig verdict) := by
  rfl

theorem verdictTM_finalConfig_state (verdict : Bool) :
    (verdictTM_finalConfig verdict).state_idx = (if verdict then 1 else 2) := rfl

theorem verdictTM_finalConfig_halting (sig : Nat) (verdict : Bool) :
    haltingStateReached (verdictTM sig verdict) (verdictTM_finalConfig verdict) = true := by
  cases verdict with
  | false => rfl
  | true => rfl

/-! ### Smoke tests: `DecidesBy` witnesses for `True` and `False`

These demonstrate that the new framework is non-vacuous: there is a
real `FlatTM`-backed decider for the trivially-true and trivially-false
predicates on any encodable type. They will be used in tests / asserts
but not on the Cook–Levin proof path. -/

/-- TM-backed decider for the constantly-true predicate. -/
def trueDecider (X : Type) [encodable X] :
    DecidesBy (fun _ : X => True) (fun _ => 1) where
  encode := fun _ => []
  encodeBound := fun _ => 0
  encodeBound_poly := inOPoly_const 0
  encodeBound_mono := fun _ _ _ => Nat.le_refl _
  encode_size := fun x => Nat.zero_le _
  M := verdictTM 1 true
  M_valid := verdictTM_valid 1 true
  M_tapes_pos := by decide
  acceptState := 1
  rejectState := 2
  halting_acc := rfl
  halting_rej := rfl
  accept_ne_reject := by decide
  decides_pos := fun _ _ =>
    ⟨verdictTM_finalConfig true, verdictTM_run_one 1 true,
      verdictTM_finalConfig_halting 1 true, rfl⟩
  decides_neg := fun _ h => absurd True.intro h

/-- TM-backed decider for the constantly-false predicate. -/
def falseDecider (X : Type) [encodable X] :
    DecidesBy (fun _ : X => False) (fun _ => 1) where
  encode := fun _ => []
  encodeBound := fun _ => 0
  encodeBound_poly := inOPoly_const 0
  encodeBound_mono := fun _ _ _ => Nat.le_refl _
  encode_size := fun x => Nat.zero_le _
  M := verdictTM 1 false
  M_valid := verdictTM_valid 1 false
  M_tapes_pos := by decide
  acceptState := 1
  rejectState := 2
  halting_acc := rfl
  halting_rej := rfl
  accept_ne_reject := by decide
  decides_pos := fun _ h => absurd h (fun h => h)
  decides_neg := fun _ _ =>
    ⟨verdictTM_finalConfig false, verdictTM_run_one 1 false,
      verdictTM_finalConfig_halting 1 false, rfl⟩

/-! ## Step 5 — Tape scanners

The deciders downstream need to walk the tape looking for delimiters
and to compare individual symbols. We build the smallest set of
single-tape scanning primitives we expect to need.

`scanRightUntilTM sig target` walks the head right until it sees the
symbol `some target`, at which point it halts in an `accept` state.
If it falls off the right end of the tape (current symbol is `none`),
it halts in a `reject` state.

The machine has three states:
- state 0 = scanning. For every symbol `v ≠ target` (including
  `none`-vs-target), transition `(0, [some v]) → (0, [some v], [Rmove])`.
  For symbol `target`, transition `(0, [some target]) → (1, [some target], [Nmove])`.
  For `none`, transition `(0, [none]) → (2, [none], [Nmove])`.
- state 1 = accept-halt (found target).
- state 2 = reject-halt (ran off the end). -/

/-- Transitions for `scanRightUntilTM`: enumerate every symbol below
`sig` and the `none` case, emitting a `Rmove` to continue scanning or
an `Nmove` to halt depending on whether the symbol matches. -/
def scanRightUntilTM_trans (sig target : Nat) : List FlatTMTransEntry :=
  let noneEntry : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [none]
      dst_state := 2
      dst_write_vals := [none]
      move_dirs := [TMMove.Nmove] }
  let mkContinue (v : Nat) : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [some v]
      dst_state := 0
      dst_write_vals := [none]
      move_dirs := [TMMove.Rmove] }
  let mkHalt : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [some target]
      dst_state := 1
      dst_write_vals := [none]
      move_dirs := [TMMove.Nmove] }
  -- Halt entry first so `find?` matches `target` before the catch-all.
  mkHalt :: noneEntry ::
    ((List.range sig).filter (fun v => decide (v ≠ target))).map mkContinue

/-- The scan-right-until-`target` TM. -/
def scanRightUntilTM (sig target : Nat) : FlatTM where
  sig := sig
  tapes := 1
  states := 3
  trans := scanRightUntilTM_trans sig target
  start := 0
  halt := [false, true, true]

theorem scanRightUntilTM_valid (sig target : Nat) (h_target : target < sig) :
    validFlatTM (scanRightUntilTM sig target) := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < 3; decide
  · show [false, true, true].length = 3; rfl
  · intro entry hentry
    -- entry is in: halt entry :: none entry :: filtered continue entries
    have hentry' : entry ∈ scanRightUntilTM_trans sig target := hentry
    unfold scanRightUntilTM_trans at hentry'
    rcases List.mem_cons.mp hentry' with hHalt | hRest
    · -- halt entry
      subst hHalt
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · show 0 < 3; decide
      · show 1 < 3; decide
      · intro x hx
        simp at hx
        subst hx
        exact h_target
      · intro x hx
        simp at hx
        subst hx
        trivial
    · rcases List.mem_cons.mp hRest with hNone | hCont
      · -- none entry
        subst hNone
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 3; decide
        · show 2 < 3; decide
        · intro x hx
          simp at hx
          subst hx
          trivial
        · intro x hx
          simp at hx
          subst hx
          trivial
      · -- continue entry for some v
        rcases List.mem_map.mp hCont with ⟨v, hv, hmk⟩
        subst hmk
        have hv' : v ∈ List.range sig := (List.mem_filter.mp hv).1
        have hvlt : v < sig := List.mem_range.mp hv'
        refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · show 0 < 3; decide
        · show 0 < 3; decide
        · intro x hx
          simp at hx
          subst hx
          exact hvlt
        · intro x hx
          simp at hx
          subst hx
          trivial

/-! ### Operational correctness for `scanRightUntilTM`

We prove three single-step lemmas (target match, in-range non-match,
out-of-range) and combine them into a full operational-correctness
statement: the machine, started at head position `head` of a tape
`right`, ends in state 1 at the first occurrence of `target` ≥ `head`,
or in state 2 past the right end if no such occurrence exists. -/

/-- The tape symbol at position `head` of a single-tape config is
`some (right.get …)` whenever the head is in range. -/
theorem currentTapeSymbol_in_range {left right : List Nat} {head : Nat}
    (h : head < right.length) :
    currentTapeSymbol (left, head, right) = some (right.get ⟨head, h⟩) := by
  show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) =
       some (right.get ⟨head, h⟩)
  rw [dif_pos h]

/-- The tape symbol at position `head` is `none` whenever the head is
past the right end. -/
theorem currentTapeSymbol_out_of_range {left right : List Nat} {head : Nat}
    (h : ¬ head < right.length) :
    currentTapeSymbol (left, head, right) = none := by
  show (if h' : head < right.length then some (right.get ⟨head, h'⟩) else none) = none
  rw [dif_neg h]

/-- Computation of `applyTransitionEntry` for a single-tape entry with
`dst_write_vals = [none]`: only the state index and head position
change. -/
private theorem applyEntry_singleTape
    (cfg_state_idx new_state : Nat) (left right : List Nat) (head : Nat)
    (sym : Option Nat) (move : TMMove) :
    applyTransitionEntry
        { state_idx := cfg_state_idx, tapes := [(left, head, right)] }
        { src_state := cfg_state_idx
          src_tape_vals := [sym]
          dst_state := new_state
          dst_write_vals := [none]
          move_dirs := [move] } =
      some { state_idx := new_state
             tapes := [moveTapeHead (left, head, right) move] } := rfl

/-- Symbol equality on a singleton list reduces to symbol equality. -/
private theorem singleOptionList_eq_iff (a b : Option Nat) :
    ([a] : List (Option Nat)) = [b] ↔ a = b := by
  constructor
  · intro h; exact List.head_eq_of_cons_eq h
  · intro h; rw [h]

/-- The three named transition entries of `scanRightUntilTM`. -/
private def haltEntry (target : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some target]
    dst_state := 1
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def noneEntry : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [none]
    dst_state := 2
    dst_write_vals := [none]
    move_dirs := [TMMove.Nmove] }

private def continueEntry (v : Nat) : FlatTMTransEntry :=
  { src_state := 0
    src_tape_vals := [some v]
    dst_state := 0
    dst_write_vals := [none]
    move_dirs := [TMMove.Rmove] }

theorem scanRightUntilTM_trans_eq (sig target : Nat) :
    (scanRightUntilTM sig target).trans =
      haltEntry target :: noneEntry ::
      ((List.range sig).filter (fun v => decide (v ≠ target))).map continueEntry := rfl

/-- Step lemma: on a target symbol, one step halts in state 1. -/
theorem scanRightUntilTM_step_match
    (sig target : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_get : right.get ⟨head, h_head_lt⟩ = target) :
    stepFlatTM (scanRightUntilTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 1, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] } with hcfg
  have hSym : currentTapeSymbol (left, head, right) = some target := by
    rw [currentTapeSymbol_in_range h_head_lt, h_get]
  have hMatch : entryMatchesConfig (haltEntry target) cfg = true := by
    show ((0 : Nat) == 0 &&
            decide (([some target] : List (Option Nat)) =
              [currentTapeSymbol (left, head, right)])) = true
    rw [hSym, decide_eq_true ((singleOptionList_eq_iff _ _).mpr rfl)]
    rfl
  show Option.bind ((scanRightUntilTM sig target).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [scanRightUntilTM_trans_eq, List.find?_cons, hMatch]
  show applyTransitionEntry cfg (haltEntry target) = _
  exact applyEntry_singleTape 0 1 left right head (some target) TMMove.Nmove

/-- Helper: among a list of `continueEntry` entries indexed by a
`List Nat`, `find?` of the config-match predicate returns
`continueEntry v` provided `v` is in the list and no earlier element
matches. -/
private theorem find_continueEntry_match
    (cfg : FlatTMConfig) (v : Nat) (L : List Nat)
    (h_cfg_state : cfg.state_idx = 0)
    (h_cfg_tape : cfg.tapes.map currentTapeSymbol = [some v])
    (h_mem : v ∈ L)
    (h_first : ∀ {w : Nat}, w ∈ L → w ≠ v →
      entryMatchesConfig (continueEntry w) cfg = false) :
    (L.map continueEntry).find?
        (fun entry => entryMatchesConfig entry cfg) =
      some (continueEntry v) := by
  induction L with
  | nil => cases h_mem
  | cons w ws ih =>
      show List.find? _ (continueEntry w :: ws.map continueEntry) = _
      rw [List.find?_cons]
      by_cases hwv : w = v
      · subst hwv
        have hMatch : entryMatchesConfig (continueEntry w) cfg = true := by
          show ((0 : Nat) == cfg.state_idx &&
                  decide (([some w] : List (Option Nat)) =
                    cfg.tapes.map currentTapeSymbol)) = true
          rw [h_cfg_state, h_cfg_tape]
          have h1 : ((0 : Nat) == 0) = true := rfl
          have h2 : decide (([some w] : List (Option Nat)) = [some w]) = true :=
            decide_eq_true rfl
          rw [h1, h2]; rfl
        rw [hMatch]
      · have hNot := h_first (List.mem_cons.mpr (Or.inl rfl)) hwv
        rw [hNot]
        rcases List.mem_cons.mp h_mem with hvw | hvws
        · exact absurd hvw.symm hwv
        · exact ih hvws (fun hw hne => h_first (List.mem_cons.mpr (Or.inr hw)) hne)

/-- One step on a non-target in-range symbol advances the head. -/
theorem scanRightUntilTM_step_advance
    (sig target : Nat) (left right : List Nat) (head : Nat)
    (h_head_lt : head < right.length)
    (h_sym_lt : right.get ⟨head, h_head_lt⟩ < sig)
    (h_ne : right.get ⟨head, h_head_lt⟩ ≠ target) :
    stepFlatTM (scanRightUntilTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 0, tapes := [(left, head + 1, right)] } := by
  let v := right.get ⟨head, h_head_lt⟩
  let cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym0 : currentTapeSymbol (left, head, right) = some v := by
    rw [currentTapeSymbol_in_range h_head_lt]
  have hSym : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]
    rw [hSym0]
  -- haltEntry does NOT match (target ≠ v).
  have hNotMatchHalt : entryMatchesConfig (haltEntry target) cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some target] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([some target] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      injection h1 with h2
      exact h_ne h2.symm
    simp [h_ne']
  -- noneEntry does NOT match.
  have hNotMatchNone : entryMatchesConfig noneEntry cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([none] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([none] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      cases h1
    simp [h_ne']
  -- v is in the filtered range list.
  have hvInFilter :
      v ∈ (List.range sig).filter (fun w => decide (w ≠ target)) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr h_sym_lt, ?_⟩
    show decide (v ≠ target) = true
    exact decide_eq_true h_ne
  -- find? on the filtered.map list returns continueEntry v.
  have hFindCont :
      (((List.range sig).filter (fun w => decide (w ≠ target))).map continueEntry).find?
          (fun entry => entryMatchesConfig entry cfg) =
        some (continueEntry v) := by
    refine find_continueEntry_match cfg v _ rfl hSym hvInFilter ?_
    intro w _ hwv
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some w] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne' : ([some w] : List (Option Nat)) ≠ [some v] := by
      intro h
      injection h with h1 _
      injection h1 with h2
      exact hwv h2
    simp [h_ne']
  -- Combine.
  show Option.bind ((scanRightUntilTM sig target).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [scanRightUntilTM_trans_eq]
  rw [List.find?_cons, hNotMatchHalt, List.find?_cons, hNotMatchNone, hFindCont]
  show applyTransitionEntry cfg (continueEntry v) = _
  exact applyEntry_singleTape 0 0 left right head (some v) TMMove.Rmove

/-- One step past the right end of the tape halts the scanner in
state 2. -/
theorem scanRightUntilTM_step_reject
    (sig target : Nat) (left right : List Nat) (head : Nat)
    (h_head_ge : ¬ head < right.length) :
    stepFlatTM (scanRightUntilTM sig target)
        { state_idx := 0, tapes := [(left, head, right)] } =
      some { state_idx := 2, tapes := [(left, head, right)] } := by
  let cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym0 : currentTapeSymbol (left, head, right) = none :=
    currentTapeSymbol_out_of_range h_head_ge
  have hSym : cfg.tapes.map currentTapeSymbol = [none] := by
    show [currentTapeSymbol (left, head, right)] = [none]
    rw [hSym0]
  -- haltEntry does NOT match (target vs none).
  have hNotMatchHalt : entryMatchesConfig (haltEntry target) cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([some target] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym]
    have h_ne : ([some target] : List (Option Nat)) ≠ [none] := by
      intro h
      injection h with h1 _
      cases h1
    simp [h_ne]
  -- noneEntry matches.
  have hMatchNone : entryMatchesConfig noneEntry cfg = true := by
    show ((0 : Nat) == cfg.state_idx &&
            decide (([none] : List (Option Nat)) =
              cfg.tapes.map currentTapeSymbol)) = true
    rw [hSym]
    have h1 : ((0 : Nat) == 0) = true := rfl
    have h2 : decide (([none] : List (Option Nat)) = [none]) = true :=
      decide_eq_true rfl
    rw [h1, h2]; rfl
  -- Combine.
  show Option.bind ((scanRightUntilTM sig target).trans.find?
        (fun entry => entryMatchesConfig entry cfg))
      (applyTransitionEntry cfg) = _
  rw [scanRightUntilTM_trans_eq]
  rw [List.find?_cons, hNotMatchHalt, List.find?_cons, hMatchNone]
  show applyTransitionEntry cfg noneEntry = _
  exact applyEntry_singleTape 0 2 left right head none TMMove.Nmove

/-- Halting check on a state-0 configuration of `scanRightUntilTM`: it
is NOT a halting state. -/
private theorem scanRightUntilTM_state0_not_halting
    (sig target : Nat) (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (scanRightUntilTM sig target)
        { state_idx := 0, tapes := cfg_tapes } = false := rfl

/-- A state-1 configuration of `scanRightUntilTM` IS a halting state. -/
private theorem scanRightUntilTM_state1_halting
    (sig target : Nat) (cfg_tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (scanRightUntilTM sig target)
        { state_idx := 1, tapes := cfg_tapes } = true := rfl

/-- One unfolding step of `runFlatTM` from a state-0 config that
takes one TM step to `cfg'`. -/
private theorem runFlatTM_state0_unfold
    (sig target : Nat) (n : Nat)
    (tapes : List (List Nat × Nat × List Nat))
    (cfg' : FlatTMConfig)
    (h_step : stepFlatTM (scanRightUntilTM sig target)
        { state_idx := 0, tapes := tapes } = some cfg') :
    runFlatTM (n + 1) (scanRightUntilTM sig target)
        { state_idx := 0, tapes := tapes } =
      runFlatTM n (scanRightUntilTM sig target) cfg' := by
  show (if haltingStateReached (scanRightUntilTM sig target)
            { state_idx := 0, tapes := tapes } = true then
          some { state_idx := 0, tapes := tapes }
        else
          match stepFlatTM (scanRightUntilTM sig target)
              { state_idx := 0, tapes := tapes } with
          | none => some { state_idx := 0, tapes := tapes }
          | some cfg' => runFlatTM n (scanRightUntilTM sig target) cfg') =
    runFlatTM n (scanRightUntilTM sig target) cfg'
  rw [scanRightUntilTM_state0_not_halting, h_step]
  rfl

/-- Main operational correctness for the "target found" case.

By induction on the gap `gap = target_pos - head`. -/
theorem scanRightUntilTM_run_found
    (sig target : Nat) (left right : List Nat) :
    ∀ (gap head : Nat) (h_in_range : head + gap < right.length),
      right.get ⟨head + gap, h_in_range⟩ = target →
      (∀ k, k < gap → ∃ (h : head + k < right.length),
        right.get ⟨head + k, h⟩ < sig ∧
          right.get ⟨head + k, h⟩ ≠ target) →
      runFlatTM (gap + 1) (scanRightUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 1, tapes := [(left, head + gap, right)] }
  | 0, head, h_in_range, h_get_target, _ => by
      have h_lt : head < right.length := by
        have := h_in_range; rwa [Nat.add_zero] at this
      have h_get : right.get ⟨head, h_lt⟩ = target := by
        have := h_get_target
        have heq : (⟨head + 0, h_in_range⟩ : Fin right.length) = ⟨head, h_lt⟩ :=
          Fin.eq_of_val_eq (Nat.add_zero head)
        rw [heq] at this
        exact this
      rw [runFlatTM_state0_unfold sig target 0 _ _
        (scanRightUntilTM_step_match sig target left right head h_lt h_get)]
      show (some { state_idx := 1, tapes := [(left, head, right)] } : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head + 0, right)] }
      rw [Nat.add_zero]
  | gap + 1, head, h_in_range, h_get_target, h_before => by
      -- First-step: advance from head to head+1.
      have h_head_lt : head < right.length :=
        Nat.lt_of_le_of_lt (Nat.le_add_right head (gap + 1)) h_in_range
      rcases h_before 0 (Nat.zero_lt_succ _) with ⟨h_kk, h_sym_lt, h_sym_ne⟩
      have heq0 : (⟨head + 0, h_kk⟩ : Fin right.length) = ⟨head, h_head_lt⟩ :=
        Fin.eq_of_val_eq (Nat.add_zero head)
      have h_get_head : right.get ⟨head, h_head_lt⟩ < sig := by
        rw [heq0] at h_sym_lt; exact h_sym_lt
      have h_get_head_ne : right.get ⟨head, h_head_lt⟩ ≠ target := by
        rw [heq0] at h_sym_ne; exact h_sym_ne
      -- Set up IH at head+1, gap.
      have h_succ : (head + 1) + gap = head + (gap + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 gap]
      have h_in_range' : (head + 1) + gap < right.length := by
        rw [h_succ]; exact h_in_range
      have h_get_target' :
          right.get ⟨(head + 1) + gap, h_in_range'⟩ = target := by
        have heq : (⟨(head + 1) + gap, h_in_range'⟩ : Fin right.length) =
            ⟨head + (gap + 1), h_in_range⟩ := Fin.eq_of_val_eq h_succ
        rw [heq]; exact h_get_target
      have h_before' :
          ∀ k, k < gap → ∃ (h : (head + 1) + k < right.length),
            right.get ⟨(head + 1) + k, h⟩ < sig ∧
              right.get ⟨(head + 1) + k, h⟩ ≠ target := by
        intro k hk
        rcases h_before (k + 1) (Nat.succ_lt_succ hk) with ⟨h_kk, h1, h2⟩
        have hShift : head + (k + 1) = (head + 1) + k := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        have h_kk' : (head + 1) + k < right.length := hShift ▸ h_kk
        refine ⟨h_kk', ?_, ?_⟩
        · have heq : (⟨(head + 1) + k, h_kk'⟩ : Fin right.length) =
              ⟨head + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
          rw [heq]; exact h1
        · have heq : (⟨(head + 1) + k, h_kk'⟩ : Fin right.length) =
              ⟨head + (k + 1), h_kk⟩ := Fin.eq_of_val_eq hShift.symm
          rw [heq]; exact h2
      have hih :=
        scanRightUntilTM_run_found sig target left right gap (head + 1)
          h_in_range' h_get_target' h_before'
      -- Unfold first step, apply step_advance, then IH.
      rw [runFlatTM_state0_unfold sig target (gap + 1) _ _
        (scanRightUntilTM_step_advance sig target left right head h_head_lt
          h_get_head h_get_head_ne)]
      rw [hih]
      show (some { state_idx := 1, tapes := [(left, (head + 1) + gap, right)] } : Option FlatTMConfig) =
        some { state_idx := 1, tapes := [(left, head + (gap + 1), right)] }
      rw [h_succ]
  termination_by gap _ _ _ _ => gap

/-- Main operational correctness for the "target not found" case.

The scanner, started at any position `head ≤ right.length` of a tape
whose symbols at `head, head+1, …` are all in-range and not equal to
`target`, runs off the right end after `right.length - head + 1`
steps, halting in state 2 at position `right.length`. -/
theorem scanRightUntilTM_run_not_found
    (sig target : Nat) (left right : List Nat) :
    ∀ (head : Nat),
      head ≤ right.length →
      (∀ k, head ≤ k → ∀ (h : k < right.length),
        right.get ⟨k, h⟩ < sig ∧ right.get ⟨k, h⟩ ≠ target) →
      runFlatTM (right.length - head + 1) (scanRightUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } =
        some { state_idx := 2, tapes := [(left, right.length, right)] }
  | head, h_le, h_all => by
      by_cases h_lt : head < right.length
      · -- Inductive step: advance one position.
        rcases h_all head (Nat.le_refl head) h_lt with ⟨h_sym_lt, h_sym_ne⟩
        have h_step :=
          scanRightUntilTM_step_advance sig target left right head h_lt h_sym_lt h_sym_ne
        have h_len_sub : right.length - head = (right.length - (head + 1)) + 1 := by
          have h_pos : 1 ≤ right.length - head := Nat.sub_pos_of_lt h_lt
          have hsub : right.length - (head + 1) = right.length - head - 1 := by
            rw [Nat.sub_add_eq]
          rw [hsub, Nat.sub_add_cancel h_pos]
        have h_le' : head + 1 ≤ right.length := h_lt
        have h_all' : ∀ k, head + 1 ≤ k → ∀ (h : k < right.length),
            right.get ⟨k, h⟩ < sig ∧ right.get ⟨k, h⟩ ≠ target := by
          intro k hk h_klt
          exact h_all k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self head) hk)) h_klt
        have hih :=
          scanRightUntilTM_run_not_found sig target left right (head + 1) h_le' h_all'
        -- runFlatTM (right.length - head + 1) = runFlatTM (((right.length - (head + 1)) + 1) + 1)
        rw [h_len_sub]
        rw [runFlatTM_state0_unfold sig target (right.length - (head + 1) + 1) _ _ h_step]
        exact hih
      · -- Base case: head = right.length.
        have h_eq : head = right.length :=
          Nat.le_antisymm h_le (Nat.le_of_not_lt h_lt)
        have h_step :=
          scanRightUntilTM_step_reject sig target left right head h_lt
        rw [h_eq] at h_step
        rw [h_eq]
        show runFlatTM (right.length - right.length + 1) _ _ = _
        rw [Nat.sub_self]
        -- runFlatTM 1
        rw [runFlatTM_state0_unfold sig target 0 _ _ h_step]
        rfl
  termination_by head _ _ => right.length - head

/-! ### Extending a halted run

`runFlatTM_extend` (padding lemma) moved to
`Complexity/Complexity/MachineSemantics.lean` in Part 2 Step 8
(so `Complexity/Complexity/NP.lean` can use it for
`DecidesBy.proj_left`). Existing references downstream resolve to the
new location transparently. -/

/-! ## Step 11.7 — counted-loop combinator `loopTM` (Risk C3 probe)

`loopTM B exitDone exitLoop` wraps a single black-box *iteration body*
machine `B` into a counted loop. `B` is a two-exit machine: from its
start it inspects the (encoded) counter region and either

- reaches `exitDone` (counter empty → the loop is finished), or
- reaches `exitLoop` (counter nonempty → it ran the user body and
  decremented the counter, leaving the tape ready for the next pass).

The wrapper adds a single dedicated halt state (index `B.states`) and
two bridge edges:

- `exitDone → haltState`  (forward — leave the loop), and
- `exitLoop → B.start`    (**backward** — re-enter the body; this is the
  genuinely new edge versus `composeFlatTM` / `branchComposeFlatTM`,
  whose every bridge goes *forward*).

This isolates the one structural unknown a loop adds over the proven
forward-only combinators: a backward bridge whose target (`B.start`) is
re-entered once per iteration, and whose `state_idx`-range and
no-early-halt trajectory must survive that re-entry. The user body, the
counter-empty guard, and the decrement gadget are folded into `B` and
treated as a black box satisfying the physical contract (head-`0`,
`encodeTape`-shaped exit, exact step, no-early-halt) — exactly the
contract `composeFlatTM_run` already validates for forward composition.

`exitDone` and `exitLoop` must be distinct states of `B`; the bridges
are placed *before* `B.trans` so they take precedence over any outgoing
`B`-transition from those states (mirroring `branchComposeFlatTM`). -/

/-- Halt vector of `loopTM B …`: every `B`-state is non-halting (we
re-enter `B` rather than stop in it), and a single dedicated halt state
sits at index `B.states`. -/
def loopHalt (B : FlatTM) : List Bool :=
  List.replicate B.states false ++ [true]

/-- The counted-loop wrapper around an iteration body `B` with two
designated exit states `exitDone` (leave) and `exitLoop` (re-enter). -/
def loopTM (B : FlatTM) (exitDone exitLoop : Nat) : FlatTM where
  sig := B.sig
  tapes := B.tapes
  states := B.states + 1
  trans :=
    bridgeEntries B.sig exitDone B.states ++
    bridgeEntries B.sig exitLoop B.start ++
    B.trans
  start := B.start
  halt := loopHalt B

/-! ### Basic accessors -/

theorem loopTM_states (B : FlatTM) (exitDone exitLoop : Nat) :
    (loopTM B exitDone exitLoop).states = B.states + 1 := rfl

theorem loopTM_start (B : FlatTM) (exitDone exitLoop : Nat) :
    (loopTM B exitDone exitLoop).start = B.start := rfl

theorem loopTM_tapes (B : FlatTM) (exitDone exitLoop : Nat) :
    (loopTM B exitDone exitLoop).tapes = B.tapes := rfl

theorem loopTM_sig (B : FlatTM) (exitDone exitLoop : Nat) :
    (loopTM B exitDone exitLoop).sig = B.sig := rfl

theorem loopHalt_length (B : FlatTM) :
    (loopHalt B).length = B.states + 1 := by
  show (List.replicate B.states false ++ [true]).length = B.states + 1
  rw [List.length_append, List.length_replicate]
  rfl

theorem loopTM_halt_length (B : FlatTM) (exitDone exitLoop : Nat) :
    (loopTM B exitDone exitLoop).halt.length =
      (loopTM B exitDone exitLoop).states := by
  rw [loopTM_states]
  show (loopHalt B).length = B.states + 1
  rw [loopHalt_length]

/-! ### Validity of `loopTM` -/

/-- `loopTM` of a valid body, with both exits in range and single-tape,
is a valid `FlatTM`. -/
theorem loopTM_valid (B : FlatTM) (exitDone exitLoop : Nat)
    (hB : validFlatTM B)
    (h_done : exitDone < B.states) (h_loop : exitLoop < B.states)
    (h_t : B.tapes = 1) :
    validFlatTM (loopTM B exitDone exitLoop) := by
  obtain ⟨hB_start, hB_halt, hB_trans⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · -- start < states
    show B.start < B.states + 1
    exact Nat.lt_succ_of_lt hB_start
  · -- halt.length = states
    show (loopHalt B).length = B.states + 1
    rw [loopHalt_length]
  · -- every transition is valid
    intro entry hentry
    show flatTMTransEntryValid (loopTM B exitDone exitLoop) entry
    have hsig_eq : (loopTM B exitDone exitLoop).sig = B.sig := rfl
    have hstates_eq : (loopTM B exitDone exitLoop).states = B.states + 1 := rfl
    have htapes_eq : (loopTM B exitDone exitLoop).tapes = B.tapes := rfl
    have hentry' : entry ∈
        bridgeEntries B.sig exitDone B.states ++
        bridgeEntries B.sig exitLoop B.start ++
        B.trans := hentry
    rcases List.mem_append.mp hentry' with hLeft | h_body
    rcases List.mem_append.mp hLeft with h_bridgeDone | h_bridgeLoop
    · -- exitDone bridge: src = exitDone < B.states, dst = B.states
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ :=
        bridgeEntries_mem h_bridgeDone
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsrc, hstates_eq]; exact Nat.lt_succ_of_lt h_done
      · rw [hdst, hstates_eq]; exact Nat.lt_succ_self _
      · rw [hsrcLen, htapes_eq, h_t]
      · rw [hdstLen, htapes_eq, h_t]
      · rw [hmovLen, htapes_eq, h_t]
      · rw [hsig_eq]; exact hsymSrc
      · rw [hsig_eq]; exact hsymDst
    · -- exitLoop bridge: src = exitLoop < B.states, dst = B.start < B.states
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ :=
        bridgeEntries_mem h_bridgeLoop
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsrc, hstates_eq]; exact Nat.lt_succ_of_lt h_loop
      · rw [hdst, hstates_eq]; exact Nat.lt_succ_of_lt hB_start
      · rw [hsrcLen, htapes_eq, h_t]
      · rw [hdstLen, htapes_eq, h_t]
      · rw [hmovLen, htapes_eq, h_t]
      · rw [hsig_eq]; exact hsymSrc
      · rw [hsig_eq]; exact hsymDst
    · -- original B transition: src, dst < B.states
      obtain ⟨hsrc, hdst, hsrcLen, hdstLen, hmovLen, hsymSrc, hsymDst⟩ :=
        hB_trans entry h_body
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hstates_eq]; exact Nat.lt_succ_of_lt hsrc
      · rw [hstates_eq]; exact Nat.lt_succ_of_lt hdst
      · rw [htapes_eq]; exact hsrcLen
      · rw [htapes_eq]; exact hdstLen
      · rw [htapes_eq]; exact hmovLen
      · rw [hsig_eq]; exact hsymSrc
      · rw [hsig_eq]; exact hsymDst

/-! ### Halt-bit lemmas for `loopTM` -/

/-- On any `B`-state, the loop machine's halt-bit is `false` (we
re-enter `B` rather than stop in it). -/
private theorem loopTM_haltingStateReached_inB
    (B : FlatTM) (exitDone exitLoop : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx < B.states) :
    haltingStateReached (loopTM B exitDone exitLoop) cfg = false := by
  show (loopHalt B).getD cfg.state_idx false = false
  show ((List.replicate B.states false ++ [true]).getD cfg.state_idx false) = false
  rw [List.getD_append _ _ _ _ (by rw [List.length_replicate]; exact h)]
  exact List.getD_replicate false h

/-- At the dedicated halt state `B.states`, the loop machine halts. -/
private theorem loopTM_haltingStateReached_halt
    (B : FlatTM) (exitDone exitLoop : Nat)
    (tapes : List (List Nat × Nat × List Nat)) :
    haltingStateReached (loopTM B exitDone exitLoop)
        { state_idx := B.states, tapes := tapes } = true := by
  show (loopHalt B).getD B.states false = true
  show ((List.replicate B.states false ++ [true]).getD B.states false) = true
  rw [List.getD_append_right _ _ _ _ (by rw [List.length_replicate])]
  rw [List.length_replicate, Nat.sub_self]
  rfl

/-! ### Bridge step lemmas for `loopTM`

The two bridge edges (`exitDone → halt`, `exitLoop → B.start`) share the
single-tape bridge-application pattern already used by
`stepFlatTM_composeFlatTM_bridge`. We first factor out the `find?` over a
single `bridgeEntries` block (it returns the matching `bridgeMkEntry`),
then assemble the two step lemmas. -/

/-- `find?` over a single `bridgeEntries` block whose source state equals
the config's state returns the matching `bridgeMkEntry` (for whatever the
current head symbol is). -/
private theorem bridgeEntries_find_eq_some
    (sig srcState dstState : Nat) (left right : List Nat) (head : Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left, head, right) = some v → v < sig) :
    (bridgeEntries sig srcState dstState).find?
        (fun e => entryMatchesConfig e
          { state_idx := srcState, tapes := [(left, head, right)] }) =
      some (bridgeMkEntry srcState dstState (currentTapeSymbol (left, head, right))) := by
  set cfg : FlatTMConfig := { state_idx := srcState, tapes := [(left, head, right)] } with hcfg
  have h_tape_map :
      cfg.tapes.map currentTapeSymbol = [currentTapeSymbol (left, head, right)] := rfl
  have h_cfg_state : cfg.state_idx = srcState := rfl
  rw [bridgeEntries_eq_bridgeMkEntry]
  cases h_sym : currentTapeSymbol (left, head, right) with
  | none =>
      have h_match :
          entryMatchesConfig (bridgeMkEntry srcState dstState none) cfg = true := by
        refine entryMatchesConfig_true_of rfl ?_
        show ([none] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol
        rw [h_tape_map, h_sym]
      exact List.find?_cons_of_pos h_match
  | some v =>
      have h_no_match :
          ¬ entryMatchesConfig (bridgeMkEntry srcState dstState none) cfg = true := by
        intro h
        have h_tape_eq := ((entryMatchesConfig_iff _ _).mp h).2
        have h_eq : ([none] : List (Option Nat)) = [some v] := by
          calc ([none] : List (Option Nat))
              = (bridgeMkEntry srcState dstState none).src_tape_vals := rfl
            _ = cfg.tapes.map currentTapeSymbol := h_tape_eq
            _ = [currentTapeSymbol (left, head, right)] := h_tape_map
            _ = [some v] := by rw [h_sym]
        injection h_eq with h1 _
        cases h1
      have h_step :
          (bridgeMkEntry srcState dstState none ::
            (List.range sig).map (fun w => bridgeMkEntry srcState dstState (some w))).find?
              (fun e => entryMatchesConfig e cfg) =
          ((List.range sig).map (fun w => bridgeMkEntry srcState dstState (some w))).find?
              (fun e => entryMatchesConfig e cfg) :=
        List.find?_cons_of_neg h_no_match
      rw [h_step]
      exact find_bridgeRange_some sig srcState dstState v (h_sym_bound v h_sym) cfg
        h_cfg_state (by rw [h_tape_map, h_sym])

/-- Backward bridge step: at `exitLoop` the loop machine jumps to
`B.start` without touching the tape. (Requires `exitDone ≠ exitLoop` so the
preceding `exitDone` bridge does not fire.) -/
private theorem stepFlatTM_loopTM_bridgeLoop
    (B : FlatTM) (exitDone exitLoop : Nat) (h_ne : exitDone ≠ exitLoop)
    (left right : List Nat) (head : Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left, head, right) = some v → v < B.sig) :
    stepFlatTM (loopTM B exitDone exitLoop)
        { state_idx := exitLoop, tapes := [(left, head, right)] } =
      some { state_idx := B.start, tapes := [(left, head, right)] } := by
  show ((loopTM B exitDone exitLoop).trans.find?
          (fun e => entryMatchesConfig e
            { state_idx := exitLoop, tapes := [(left, head, right)] })).bind
        (applyTransitionEntry { state_idx := exitLoop, tapes := [(left, head, right)] }) = _
  have h_trans : (loopTM B exitDone exitLoop).trans =
      bridgeEntries B.sig exitDone B.states ++
      bridgeEntries B.sig exitLoop B.start ++ B.trans := rfl
  rw [h_trans, List.find?_append, List.find?_append]
  have h_done_none :
      (bridgeEntries B.sig exitDone B.states).find?
        (fun e => entryMatchesConfig e
          { state_idx := exitLoop, tapes := [(left, head, right)] }) = none :=
    bridgeEntries_find_eq_none (fun heq => h_ne heq.symm)
  have h_loop_some :
      (bridgeEntries B.sig exitLoop B.start).find?
        (fun e => entryMatchesConfig e
          { state_idx := exitLoop, tapes := [(left, head, right)] }) =
        some (bridgeMkEntry exitLoop B.start (currentTapeSymbol (left, head, right))) :=
    bridgeEntries_find_eq_some B.sig exitLoop B.start left right head h_sym_bound
  rw [h_done_none, h_loop_some]
  simp only [Option.none_or, Option.some_or]
  exact applyBridgeMkEntry_singleTape exitLoop B.start
    (currentTapeSymbol (left, head, right)) left right head

/-- Forward bridge step: at `exitDone` the loop machine jumps to the
dedicated halt state `B.states` without touching the tape. -/
private theorem stepFlatTM_loopTM_bridgeDone
    (B : FlatTM) (exitDone exitLoop : Nat)
    (left right : List Nat) (head : Nat)
    (h_sym_bound : ∀ v, currentTapeSymbol (left, head, right) = some v → v < B.sig) :
    stepFlatTM (loopTM B exitDone exitLoop)
        { state_idx := exitDone, tapes := [(left, head, right)] } =
      some { state_idx := B.states, tapes := [(left, head, right)] } := by
  show ((loopTM B exitDone exitLoop).trans.find?
          (fun e => entryMatchesConfig e
            { state_idx := exitDone, tapes := [(left, head, right)] })).bind
        (applyTransitionEntry { state_idx := exitDone, tapes := [(left, head, right)] }) = _
  have h_trans : (loopTM B exitDone exitLoop).trans =
      bridgeEntries B.sig exitDone B.states ++
      bridgeEntries B.sig exitLoop B.start ++ B.trans := rfl
  rw [h_trans, List.find?_append, List.find?_append]
  have h_done_some :
      (bridgeEntries B.sig exitDone B.states).find?
        (fun e => entryMatchesConfig e
          { state_idx := exitDone, tapes := [(left, head, right)] }) =
        some (bridgeMkEntry exitDone B.states (currentTapeSymbol (left, head, right))) :=
    bridgeEntries_find_eq_some B.sig exitDone B.states left right head h_sym_bound
  rw [h_done_some]
  simp only [Option.some_or]
  exact applyBridgeMkEntry_singleTape exitDone B.states
    (currentTapeSymbol (left, head, right)) left right head

/-- Body-phase step: on a config in `B`'s state range that is neither
exit, one loop-machine step coincides with one `B` step (the two bridges
do not match, so `find?` falls through to `B.trans`). Mirror of
`stepFlatTM_composeFlatTM_M1`. -/
private theorem stepFlatTM_loopTM_B
    (B : FlatTM) (exitDone exitLoop : Nat) (cfg : FlatTMConfig)
    (h_state_lt : cfg.state_idx < B.states)
    (h_ne_done : cfg.state_idx ≠ exitDone)
    (h_ne_loop : cfg.state_idx ≠ exitLoop) :
    stepFlatTM (loopTM B exitDone exitLoop) cfg = stepFlatTM B cfg := by
  show ((loopTM B exitDone exitLoop).trans.find?
          (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) =
       (B.trans.find? (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg)
  have h_trans : (loopTM B exitDone exitLoop).trans =
      bridgeEntries B.sig exitDone B.states ++
      bridgeEntries B.sig exitLoop B.start ++ B.trans := rfl
  rw [h_trans, List.find?_append, List.find?_append]
  have h_done_none :
      (bridgeEntries B.sig exitDone B.states).find?
        (fun e => entryMatchesConfig e cfg) = none :=
    bridgeEntries_find_eq_none h_ne_done
  have h_loop_none :
      (bridgeEntries B.sig exitLoop B.start).find?
        (fun e => entryMatchesConfig e cfg) = none :=
    bridgeEntries_find_eq_none h_ne_loop
  rw [h_done_none, h_loop_none, Option.none_or, Option.none_or]

/-! ### Body-phase run lift for `loopTM`

The exact analogue of `runFlatTM_composeFlatTM_M1_phase`: while the body
`B` runs at a state `< B.states` that avoids both exits and does not halt
in `B`, the loop machine's run coincides with `B`'s run. The extra
"`≠ exitLoop`" obligation (versus the single forward exit of
`composeFlatTM`) is what the backward edge contributes. -/
private theorem runFlatTM_loopTM_B_phase
    (B : FlatTM) (exitDone exitLoop : Nat) (h_validB : validFlatTM B) :
    ∀ (n : Nat) (cfg : FlatTMConfig),
      cfg.state_idx < B.states →
      (∀ k, k < n → ∀ ck, runFlatTM k B cfg = some ck →
         ck.state_idx ≠ exitDone ∧ ck.state_idx ≠ exitLoop ∧
         haltingStateReached B ck = false) →
      runFlatTM n (loopTM B exitDone exitLoop) cfg = runFlatTM n B cfg
  | 0, _, _, _ => rfl
  | n + 1, cfg, h_state_lt, h_traj => by
      have h_k0 := h_traj 0 (Nat.zero_lt_succ _) cfg rfl
      have h_ne_done : cfg.state_idx ≠ exitDone := h_k0.1
      have h_ne_loop : cfg.state_idx ≠ exitLoop := h_k0.2.1
      have h_halt_false_cfg : haltingStateReached B cfg = false := h_k0.2.2
      have h_halt_loop_false :
          haltingStateReached (loopTM B exitDone exitLoop) cfg = false :=
        loopTM_haltingStateReached_inB B exitDone exitLoop cfg h_state_lt
      have h_step_eq :
          stepFlatTM (loopTM B exitDone exitLoop) cfg = stepFlatTM B cfg :=
        stepFlatTM_loopTM_B B exitDone exitLoop cfg h_state_lt h_ne_done h_ne_loop
      have h_unfold_B :
          runFlatTM (n + 1) B cfg =
            match stepFlatTM B cfg with
            | none => some cfg
            | some cfg' => runFlatTM n B cfg' := by
        show (if haltingStateReached B cfg = true then some cfg
              else match stepFlatTM B cfg with
                | none => some cfg
                | some cfg' => runFlatTM n B cfg') = _
        rw [if_neg (by rw [h_halt_false_cfg]; decide)]
      have h_unfold_loop :
          runFlatTM (n + 1) (loopTM B exitDone exitLoop) cfg =
            match stepFlatTM (loopTM B exitDone exitLoop) cfg with
            | none => some cfg
            | some cfg' => runFlatTM n (loopTM B exitDone exitLoop) cfg' := by
        show (if haltingStateReached (loopTM B exitDone exitLoop) cfg = true then some cfg
              else match stepFlatTM (loopTM B exitDone exitLoop) cfg with
                | none => some cfg
                | some cfg' => runFlatTM n (loopTM B exitDone exitLoop) cfg') = _
        rw [if_neg (by rw [h_halt_loop_false]; decide)]
      rw [h_unfold_B, h_unfold_loop, h_step_eq]
      cases h_step : stepFlatTM B cfg with
      | none => rfl
      | some cfg' =>
          have h_cfg'_lt : cfg'.state_idx < B.states :=
            state_idx_lt_states_of_step B h_validB cfg cfg' h_step
          have h_traj_shift : ∀ k, k < n → ∀ ck,
              runFlatTM k B cfg' = some ck →
              ck.state_idx ≠ exitDone ∧ ck.state_idx ≠ exitLoop ∧
              haltingStateReached B ck = false := by
            intro k hk ck h_run
            have h_chain : runFlatTM (k + 1) B cfg = some ck := by
              have h_unfold :
                  runFlatTM (k + 1) B cfg =
                    match stepFlatTM B cfg with
                    | none => some cfg
                    | some cfg'' => runFlatTM k B cfg'' := by
                show (if haltingStateReached B cfg = true then some cfg
                      else match stepFlatTM B cfg with
                        | none => some cfg
                        | some cfg'' => runFlatTM k B cfg'') = _
                rw [if_neg (by rw [h_halt_false_cfg]; decide)]
              rw [h_unfold, h_step]; exact h_run
            exact h_traj (k + 1) (Nat.succ_lt_succ hk) ck h_chain
          exact runFlatTM_loopTM_B_phase B exitDone exitLoop h_validB n cfg' h_cfg'_lt
            h_traj_shift
  termination_by n _ _ _ => n

/-! ### The counted-loop run lemma

`loopBudget` is the total step count: `tDone + 1` to do the final
empty-counter guard + leave, plus `tIter m + 1` per iteration (body +
backward bridge). The run lemma threads the physical contract (head-`0`,
`encodeTape`-shaped, single-tape config `T n`) through every iteration by
induction on the iteration count. The two contracts are exactly the shape
`composeFlatTM_run` already validated for one fragment — here applied once
per pass, with the backward bridge re-entering `B.start`. -/

/-- Total step budget of the counted loop. -/
def loopBudget (tIter : Nat → Nat) (tDone : Nat) : Nat → Nat
  | 0     => tDone + 1
  | n + 1 => tIter n + 1 + loopBudget tIter tDone n

/-- **Operational correctness of `loopTM`.** Given an iteration body `B`
that, on the single-tape head-`0` config `T (n+1)`, reaches `exitLoop` on
the decremented config `T n` (the iteration contract), and on the
empty-counter config `T 0` reaches `exitDone` leaving `T 0` (the done
contract) — both at explicit step counts along no-early-halt trajectories
— the loop machine, started at `B.start` on `T n`, halts at its dedicated
halt state on `T 0` in `loopBudget tIter tDone n` steps.

This is the load-bearing iteration lemma for the layer's `forBnd`. -/
theorem loopTM_run
    (B : FlatTM) (exitDone exitLoop : Nat)
    (h_validB : validFlatTM B)
    (h_done_lt : exitDone < B.states) (h_loop_lt : exitLoop < B.states)
    (h_ne : exitDone ≠ exitLoop)
    (T : Nat → List Nat × Nat × List Nat)
    (h_sym : ∀ n v, currentTapeSymbol (T n) = some v → v < B.sig)
    (tIter : Nat → Nat) (tDone : Nat)
    (h_done :
        runFlatTM tDone B { state_idx := B.start, tapes := [T 0] }
          = some { state_idx := exitDone, tapes := [T 0] } ∧
        (∀ k, k < tDone → ∀ ck,
            runFlatTM k B { state_idx := B.start, tapes := [T 0] } = some ck →
            ck.state_idx ≠ exitDone ∧ ck.state_idx ≠ exitLoop ∧
            haltingStateReached B ck = false)) :
    ∀ n,
      -- iteration contract, required only for the iterations actually run
      (∀ j, j < n →
        runFlatTM (tIter j) B { state_idx := B.start, tapes := [T (j + 1)] }
          = some { state_idx := exitLoop, tapes := [T j] } ∧
        (∀ k, k < tIter j → ∀ ck,
            runFlatTM k B { state_idx := B.start, tapes := [T (j + 1)] } = some ck →
            ck.state_idx ≠ exitDone ∧ ck.state_idx ≠ exitLoop ∧
            haltingStateReached B ck = false)) →
      runFlatTM (loopBudget tIter tDone n) (loopTM B exitDone exitLoop)
          { state_idx := B.start, tapes := [T n] }
        = some { state_idx := B.states, tapes := [T 0] } := by
  intro n
  induction n with
  | zero =>
      intro _
      have h_start_lt :
          ({ state_idx := B.start, tapes := [T 0] } : FlatTMConfig).state_idx < B.states :=
        h_validB.1
      have h_lift :=
        runFlatTM_loopTM_B_phase B exitDone exitLoop h_validB tDone
          { state_idx := B.start, tapes := [T 0] } h_start_lt h_done.2
      rw [h_done.1] at h_lift
      have h_bridge :
          stepFlatTM (loopTM B exitDone exitLoop)
              { state_idx := exitDone, tapes := [T 0] } =
            some { state_idx := B.states, tapes := [T 0] } :=
        stepFlatTM_loopTM_bridgeDone B exitDone exitLoop
          (T 0).1 (T 0).2.2 (T 0).2.1 (fun v hv => h_sym 0 v hv)
      have h_mid_not_halt :
          haltingStateReached (loopTM B exitDone exitLoop)
              { state_idx := exitDone, tapes := [T 0] } = false :=
        loopTM_haltingStateReached_inB B exitDone exitLoop _ h_done_lt
      show runFlatTM (tDone + 1) (loopTM B exitDone exitLoop)
          { state_idx := B.start, tapes := [T 0] }
        = some { state_idx := B.states, tapes := [T 0] }
      exact runFlatTM_extend_by_step (loopTM B exitDone exitLoop) tDone
        { state_idx := B.start, tapes := [T 0] }
        { state_idx := exitDone, tapes := [T 0] }
        { state_idx := B.states, tapes := [T 0] }
        h_lift h_mid_not_halt h_bridge
  | succ m ih =>
      intro h_iter
      have h_iter_m := h_iter m (Nat.lt_succ_self m)
      have ih' := ih (fun j hj => h_iter j (Nat.lt_succ_of_lt hj))
      have h_start_lt :
          ({ state_idx := B.start, tapes := [T (m + 1)] } : FlatTMConfig).state_idx < B.states :=
        h_validB.1
      have h_lift :=
        runFlatTM_loopTM_B_phase B exitDone exitLoop h_validB (tIter m)
          { state_idx := B.start, tapes := [T (m + 1)] } h_start_lt h_iter_m.2
      rw [h_iter_m.1] at h_lift
      have h_bridge :
          stepFlatTM (loopTM B exitDone exitLoop)
              { state_idx := exitLoop, tapes := [T m] } =
            some { state_idx := B.start, tapes := [T m] } :=
        stepFlatTM_loopTM_bridgeLoop B exitDone exitLoop h_ne
          (T m).1 (T m).2.2 (T m).2.1 (fun v hv => h_sym m v hv)
      have h_mid_not_halt :
          haltingStateReached (loopTM B exitDone exitLoop)
              { state_idx := exitLoop, tapes := [T m] } = false :=
        loopTM_haltingStateReached_inB B exitDone exitLoop _ h_loop_lt
      have h_step1 :
          runFlatTM (tIter m + 1) (loopTM B exitDone exitLoop)
              { state_idx := B.start, tapes := [T (m + 1)] }
            = some { state_idx := B.start, tapes := [T m] } :=
        runFlatTM_extend_by_step (loopTM B exitDone exitLoop) (tIter m)
          { state_idx := B.start, tapes := [T (m + 1)] }
          { state_idx := exitLoop, tapes := [T m] }
          { state_idx := B.start, tapes := [T m] }
          h_lift h_mid_not_halt h_bridge
      show runFlatTM (tIter m + 1 + loopBudget tIter tDone m) (loopTM B exitDone exitLoop)
          { state_idx := B.start, tapes := [T (m + 1)] }
        = some { state_idx := B.states, tapes := [T 0] }
      rw [runFlatTM_compose (loopTM B exitDone exitLoop) (tIter m + 1)
        (loopBudget tIter tDone m) _ _ h_step1]
      exact ih'

/-- **No-early-halt trajectory of `loopTM`.** Until the loop completes
(`k < loopBudget tIter tDone n`), the loop machine has not reached its dedicated
halt state `B.states` — every intermediate config sits at a `B`-state (`<
B.states`), which is non-halting in `loopTM`. The `h_traj` companion to
`loopTM_run`, needed by every counted-loop physical contract (e.g. the `clear`
gadget). Same hypotheses as `loopTM_run`. -/
theorem loopTM_no_early_halt
    (B : FlatTM) (exitDone exitLoop : Nat)
    (h_validB : validFlatTM B)
    (h_done_lt : exitDone < B.states) (h_loop_lt : exitLoop < B.states)
    (h_ne : exitDone ≠ exitLoop)
    (T : Nat → List Nat × Nat × List Nat)
    (h_sym : ∀ n v, currentTapeSymbol (T n) = some v → v < B.sig)
    (tIter : Nat → Nat) (tDone : Nat)
    (h_done :
        runFlatTM tDone B { state_idx := B.start, tapes := [T 0] }
          = some { state_idx := exitDone, tapes := [T 0] } ∧
        (∀ k, k < tDone → ∀ ck,
            runFlatTM k B { state_idx := B.start, tapes := [T 0] } = some ck →
            ck.state_idx ≠ exitDone ∧ ck.state_idx ≠ exitLoop ∧
            haltingStateReached B ck = false)) :
    ∀ n,
      (∀ j, j < n →
        runFlatTM (tIter j) B { state_idx := B.start, tapes := [T (j + 1)] }
          = some { state_idx := exitLoop, tapes := [T j] } ∧
        (∀ k, k < tIter j → ∀ ck,
            runFlatTM k B { state_idx := B.start, tapes := [T (j + 1)] } = some ck →
            ck.state_idx ≠ exitDone ∧ ck.state_idx ≠ exitLoop ∧
            haltingStateReached B ck = false)) →
      ∀ k, k < loopBudget tIter tDone n → ∀ ck,
        runFlatTM k (loopTM B exitDone exitLoop)
            { state_idx := B.start, tapes := [T n] } = some ck →
        haltingStateReached (loopTM B exitDone exitLoop) ck = false := by
  intro n
  induction n with
  | zero =>
      intro _ k hk ck hck
      have h_traj : ∀ j, j < k → ∀ cj,
          runFlatTM j B { state_idx := B.start, tapes := [T 0] } = some cj →
          cj.state_idx ≠ exitDone ∧ cj.state_idx ≠ exitLoop ∧ haltingStateReached B cj = false :=
        fun j hj cj hcj => h_done.2 j (by simp only [loopBudget] at hk; omega) cj hcj
      have h_phase := runFlatTM_loopTM_B_phase B exitDone exitLoop h_validB k
        { state_idx := B.start, tapes := [T 0] } h_validB.1 h_traj
      rw [h_phase] at hck
      exact loopTM_haltingStateReached_inB B exitDone exitLoop ck
        (state_idx_lt_states_of_run B h_validB k _ ck h_validB.1 hck)
  | succ m ih =>
      intro h_iter k hk ck hck
      have h_iter_m := h_iter m (Nat.lt_succ_self m)
      by_cases hkle : k < tIter m + 1
      · have h_traj : ∀ j, j < k → ∀ cj,
            runFlatTM j B { state_idx := B.start, tapes := [T (m + 1)] } = some cj →
            cj.state_idx ≠ exitDone ∧ cj.state_idx ≠ exitLoop ∧ haltingStateReached B cj = false :=
          fun j hj cj hcj => h_iter_m.2 j (by omega) cj hcj
        have h_phase := runFlatTM_loopTM_B_phase B exitDone exitLoop h_validB k
          { state_idx := B.start, tapes := [T (m + 1)] } h_validB.1 h_traj
        rw [h_phase] at hck
        exact loopTM_haltingStateReached_inB B exitDone exitLoop ck
          (state_idx_lt_states_of_run B h_validB k _ ck h_validB.1 hck)
      · push_neg at hkle
        obtain ⟨j', rfl⟩ : ∃ j', k = (tIter m + 1) + j' := ⟨k - (tIter m + 1), by omega⟩
        have hj'_lt : j' < loopBudget tIter tDone m := by simp only [loopBudget] at hk; omega
        have ih' := ih (fun j hj => h_iter j (Nat.lt_succ_of_lt hj))
        have h_lift := runFlatTM_loopTM_B_phase B exitDone exitLoop h_validB (tIter m)
          { state_idx := B.start, tapes := [T (m + 1)] } h_validB.1 h_iter_m.2
        rw [h_iter_m.1] at h_lift
        have h_bridge : stepFlatTM (loopTM B exitDone exitLoop)
            { state_idx := exitLoop, tapes := [T m] }
              = some { state_idx := B.start, tapes := [T m] } :=
          stepFlatTM_loopTM_bridgeLoop B exitDone exitLoop h_ne
            (T m).1 (T m).2.2 (T m).2.1 (fun v hv => h_sym m v hv)
        have h_step1 := runFlatTM_extend_by_step (loopTM B exitDone exitLoop) (tIter m)
          { state_idx := B.start, tapes := [T (m + 1)] }
          { state_idx := exitLoop, tapes := [T m] }
          { state_idx := B.start, tapes := [T m] }
          h_lift
          (loopTM_haltingStateReached_inB B exitDone exitLoop _ h_loop_lt)
          h_bridge
        rw [runFlatTM_compose (loopTM B exitDone exitLoop) (tIter m + 1) j' _ _ h_step1] at hck
        exact ih' j' hj'_lt ck hck

/-! ### `AllFalse` namespace: pre-work for a real `DecidesBy` example

We are building toward a complete `DecidesBy` witness for
`(fun bs : List Bool => ∀ b ∈ bs, b = false)`. This session contributes
the input encoding and the length/size lemmas; the membership-based
range bound; and a "first true position" extractor (to be wired up in
the next session).

The plan is to use `scanRightUntilTM 2 1` with `acceptState = 2`
(scanner ran off the end → no `true` found) and `rejectState = 1`
(scanner found `1` → at least one `true`). -/

namespace AllFalse

/-- Encoding: `false ↦ 0`, `true ↦ 1`. -/
def encode (bs : List Bool) : List Nat :=
  bs.map (fun b => if b then 1 else 0)

theorem encode_length (bs : List Bool) : (encode bs).length = bs.length := by
  simp [encode]

theorem encode_size_le (bs : List Bool) :
    (encode bs).length ≤ encodable.size bs + 1 := by
  rw [encode_length]
  have h_le_size : bs.length ≤ encodable.size bs := by
    induction bs with
    | nil => exact Nat.le_refl 0
    | cons b bs ih =>
        rw [encodable_size_list_cons, List.length_cons]
        have h1 : bs.length + 1 ≤ encodable.size bs + 1 := Nat.add_le_add_right ih 1
        have h2 : encodable.size bs + 1 ≤ encodable.size b + 1 + encodable.size bs := by
          rw [Nat.add_comm (encodable.size b + 1) (encodable.size bs)]
          exact Nat.add_le_add_left (Nat.le_add_left _ _) _
        exact Nat.le_trans h1 h2
  exact Nat.le_trans h_le_size (Nat.le_succ _)

/-- Every element of `encode bs` is `0` or `1`. -/
theorem encode_mem_zero_or_one {bs : List Bool} {n : Nat} (h : n ∈ encode bs) :
    n = 0 ∨ n = 1 := by
  unfold encode at h
  rcases List.mem_map.mp h with ⟨b, _, hb⟩
  cases b
  · left; rw [← hb]; rfl
  · right; rw [← hb]; rfl

/-- Every element of `encode bs` is `< 2`. -/
theorem encode_mem_lt_two {bs : List Bool} {n : Nat} (h : n ∈ encode bs) :
    n < 2 := by
  rcases encode_mem_zero_or_one h with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

/-- Test that `.get` and `[]` agree definitionally on `List`. -/
private example (l : List Nat) (k : Nat) (h : k < l.length) :
    l.get ⟨k, h⟩ = l[k]'h := rfl

/-- The encoded symbol at any position is `< 2`. -/
theorem encode_get_lt_two (bs : List Bool) (k : Nat) (h : k < (encode bs).length) :
    (encode bs).get ⟨k, h⟩ < 2 := by
  have hk : k < bs.length := by rw [encode_length] at h; exact h
  show (encode bs)[k]'h < 2
  show (bs.map (fun b => if b then 1 else 0))[k]'h < 2
  rw [List.getElem_map]
  cases bs[k]'hk
  · show 0 < 2; decide
  · show 1 < 2; decide

/-- If position `k` of `bs` is `false`, the encoded symbol there is `0`. -/
theorem encode_get_of_false (bs : List Bool) (k : Nat) (h : k < (encode bs).length)
    (hk : k < bs.length) (h_get : bs.get ⟨k, hk⟩ = false) :
    (encode bs).get ⟨k, h⟩ = 0 := by
  show (encode bs)[k]'h = 0
  show (bs.map (fun b => if b then 1 else 0))[k]'h = 0
  rw [List.getElem_map]
  show (if bs[k]'hk then 1 else 0) = 0
  have hf : bs[k]'hk = false := h_get
  rw [hf]
  decide

/-- If position `k` of `bs` is `true`, the encoded symbol there is `1`. -/
theorem encode_get_of_true (bs : List Bool) (k : Nat) (h : k < (encode bs).length)
    (hk : k < bs.length) (h_get : bs.get ⟨k, hk⟩ = true) :
    (encode bs).get ⟨k, h⟩ = 1 := by
  show (encode bs)[k]'h = 1
  show (bs.map (fun b => if b then 1 else 0))[k]'h = 1
  rw [List.getElem_map]
  show (if bs[k]'hk then 1 else 0) = 1
  have ht : bs[k]'hk = true := h_get
  rw [ht]
  decide

/-- If every element of `bs` is `false`, every encoded symbol is `0`
(in particular `< 2` and `≠ 1`). -/
theorem encode_all_zero_of_all_false (bs : List Bool)
    (h_all : ∀ b ∈ bs, b = false) :
    ∀ k (h : k < (encode bs).length),
      (encode bs).get ⟨k, h⟩ < 2 ∧ (encode bs).get ⟨k, h⟩ ≠ 1 := by
  intro k h
  refine ⟨encode_get_lt_two bs k h, ?_⟩
  have hk : k < bs.length := by rw [encode_length] at h; exact h
  have h_get_false : bs.get ⟨k, hk⟩ = false :=
    h_all _ (List.get_mem _ _)
  rw [encode_get_of_false bs k h hk h_get_false]
  decide

/-- Extract the first index of `bs` where the value is `true`, given
that some such index exists. -/
theorem exists_first_true (bs : List Bool)
    (h_exists : ∃ b ∈ bs, b ≠ false) :
    ∃ k_first, ∃ h_lt : k_first < bs.length,
      bs.get ⟨k_first, h_lt⟩ = true ∧
        ∀ j, ∀ (h_j : j < bs.length), j < k_first → bs.get ⟨j, h_j⟩ = false := by
  classical
  let P : Nat → Prop := fun k => ∃ h : k < bs.length, bs.get ⟨k, h⟩ = true
  have hP_dec : ∀ k, Decidable (P k) := by
    intro k
    by_cases hk : k < bs.length
    · cases hb : bs.get ⟨k, hk⟩ with
      | false =>
          apply isFalse
          rintro ⟨_, hb'⟩
          rw [hb] at hb'
          cases hb'
      | true =>
          exact isTrue ⟨hk, hb⟩
    · apply isFalse
      rintro ⟨h, _⟩
      exact hk h
  have hP_exists : ∃ k, P k := by
    rcases h_exists with ⟨b, hb_mem, hb_ne⟩
    have hb_true : b = true := by cases b <;> simp_all
    rcases List.mem_iff_get.mp hb_mem with ⟨⟨k, hk⟩, hkb⟩
    exact ⟨k, hk, by rw [hkb, hb_true]⟩
  let k_first := @Nat.find P (fun k => hP_dec k) hP_exists
  have h_first_P : P k_first := @Nat.find_spec P (fun k => hP_dec k) hP_exists
  have h_first_min : ∀ j, j < k_first → ¬ P j :=
    fun j hj => @Nat.find_min P (fun k => hP_dec k) hP_exists j hj
  rcases h_first_P with ⟨h_first_lt, h_first_eq⟩
  refine ⟨k_first, h_first_lt, h_first_eq, ?_⟩
  intro j h_j hj
  have h_not_P := h_first_min j hj
  -- h_not_P : ¬ ∃ h, bs.get ⟨j, h⟩ = true
  cases h_get_j : bs.get ⟨j, h_j⟩ with
  | false => rfl
  | true => exact absurd ⟨h_j, h_get_j⟩ h_not_P

/-- Complete TM-backed decider for "every element of a `List Bool` is `false`". -/
def decider : DecidesBy (fun bs : List Bool => ∀ b ∈ bs, b = false)
    (fun n => n + 2) where
  encode := encode
  encodeBound := fun n => n + 1
  encodeBound_poly := inOPoly_add inOPoly_id (inOPoly_const 1)
  encodeBound_mono := fun _ _ h => Nat.add_le_add_right h 1
  encode_size := fun bs => encode_size_le bs
  M := scanRightUntilTM 2 1
  M_valid := scanRightUntilTM_valid 2 1 (by decide)
  M_tapes_pos := by decide
  acceptState := 2
  rejectState := 1
  halting_acc := rfl
  halting_rej := rfl
  accept_ne_reject := by decide
  decides_pos := by
    intro bs h_all_false
    -- All symbols are 0 → scanner runs off the right end at state 2.
    have h_zero := encode_all_zero_of_all_false bs h_all_false
    have hrun := scanRightUntilTM_run_not_found 2 1 [] (encode bs) 0
      (Nat.zero_le _)
      (fun k _ h_klt => h_zero k h_klt)
    rw [Nat.sub_zero] at hrun
    -- Time bound: pad (encode bs).length + 1 up to encodable.size bs + 2.
    have h_le : (encode bs).length + 1 ≤ encodable.size bs + 2 := by
      have h_le1 : (encode bs).length ≤ encodable.size bs + 1 := encode_size_le bs
      calc (encode bs).length + 1
          ≤ (encodable.size bs + 1) + 1 := Nat.add_le_add_right h_le1 1
        _ = encodable.size bs + 2 := by rw [Nat.add_assoc]
    have h_padded :
        runFlatTM ((encode bs).length + 1 +
            (encodable.size bs + 2 - ((encode bs).length + 1)))
          (scanRightUntilTM 2 1)
          { state_idx := 0, tapes := [([], 0, encode bs)] } =
        some { state_idx := 2, tapes := [([], (encode bs).length, encode bs)] } :=
      runFlatTM_extend hrun rfl
    have h_eq :
        (encode bs).length + 1 + (encodable.size bs + 2 - ((encode bs).length + 1)) =
          encodable.size bs + 2 :=
      Nat.add_sub_cancel' h_le
    rw [h_eq] at h_padded
    exact ⟨_, h_padded, rfl, rfl⟩
  decides_neg := by
    intro bs h_not_all_false
    -- Some bit is `true`. Extract the first such index.
    have h_exists : ∃ b ∈ bs, b ≠ false := by
      classical
      by_contra h_none
      apply h_not_all_false
      intro b hb
      by_contra hbne
      exact h_none ⟨b, hb, hbne⟩
    rcases exists_first_true bs h_exists with
      ⟨k_first, h_first_lt, h_first_true, h_first_min⟩
    -- Encoded tape: position k_first holds `1`, earlier positions hold `0`.
    have h_first_lt' : k_first < (encode bs).length := by
      rw [encode_length]; exact h_first_lt
    have h_0k_lt : 0 + k_first < (encode bs).length := by
      rw [Nat.zero_add]; exact h_first_lt'
    have h_get_target :
        (encode bs).get ⟨0 + k_first, h_0k_lt⟩ = 1 := by
      have h_fin_eq : (⟨0 + k_first, h_0k_lt⟩ : Fin (encode bs).length) =
          ⟨k_first, h_first_lt'⟩ :=
        Fin.eq_of_val_eq (Nat.zero_add k_first)
      rw [h_fin_eq]
      exact encode_get_of_true bs k_first h_first_lt' h_first_lt h_first_true
    have h_get_before :
        ∀ k, k < k_first → ∃ (h : 0 + k < (encode bs).length),
          (encode bs).get ⟨0 + k, h⟩ < 2 ∧
            (encode bs).get ⟨0 + k, h⟩ ≠ 1 := by
      intro k hk
      have h_k_bs_lt : k < bs.length := Nat.lt_trans hk h_first_lt
      have h_k_enc_lt : k < (encode bs).length := by rw [encode_length]; exact h_k_bs_lt
      have h_0k_lt' : 0 + k < (encode bs).length := by rw [Nat.zero_add]; exact h_k_enc_lt
      have h_fin_eq : (⟨0 + k, h_0k_lt'⟩ : Fin (encode bs).length) =
          ⟨k, h_k_enc_lt⟩ :=
        Fin.eq_of_val_eq (Nat.zero_add k)
      refine ⟨h_0k_lt', ?_, ?_⟩
      · rw [h_fin_eq]; exact encode_get_lt_two bs k h_k_enc_lt
      · have h_get_k_false : bs.get ⟨k, h_k_bs_lt⟩ = false := h_first_min k h_k_bs_lt hk
        rw [h_fin_eq, encode_get_of_false bs k h_k_enc_lt h_k_bs_lt h_get_k_false]
        decide
    have hrun := scanRightUntilTM_run_found 2 1 [] (encode bs) k_first 0
      (by rw [Nat.zero_add]; exact h_first_lt') h_get_target h_get_before
    rw [Nat.zero_add] at hrun
    -- Time bound: pad k_first + 1 up to encodable.size bs + 2.
    have h_le : k_first + 1 ≤ encodable.size bs + 2 := by
      have h_le1 : k_first ≤ (encode bs).length := Nat.le_of_lt h_first_lt'
      have h_le2 : (encode bs).length ≤ encodable.size bs + 1 := encode_size_le bs
      calc k_first + 1
          ≤ (encode bs).length + 1 := Nat.add_le_add_right h_le1 1
        _ ≤ (encodable.size bs + 1) + 1 := Nat.add_le_add_right h_le2 1
        _ = encodable.size bs + 2 := by rw [Nat.add_assoc]
    have h_padded :
        runFlatTM (k_first + 1 + (encodable.size bs + 2 - (k_first + 1)))
          (scanRightUntilTM 2 1)
          { state_idx := 0, tapes := [([], 0, encode bs)] } =
        some { state_idx := 1, tapes := [([], k_first, encode bs)] } :=
      runFlatTM_extend hrun rfl
    have h_eq : k_first + 1 + (encodable.size bs + 2 - (k_first + 1)) =
        encodable.size bs + 2 :=
      Nat.add_sub_cancel' h_le
    rw [h_eq] at h_padded
    exact ⟨_, h_padded, rfl, rfl⟩

/-- The time bound `n ↦ n + 2` is polynomial. -/
theorem timeBound_inOPoly : inOPoly (fun n => n + 2) := by
  -- n + 2 ≤ 3 * n^1 for n ≥ 1.
  refine ⟨1, 3, 1, ?_⟩
  intro n hn
  show n + 2 ≤ 3 * n ^ 1
  rw [pow_one]
  -- n + 2 ≤ 3 * n iff 2 ≤ 2 * n iff 1 ≤ n.
  have h2n : 2 ≤ 2 * n := by
    have := Nat.mul_le_mul_left 2 hn
    simpa using this
  calc n + 2 ≤ n + 2 * n := Nat.add_le_add_left h2n n
    _ = 3 * n := by ring

/-- The time bound `n ↦ n + 2` is monotonic. -/
theorem timeBound_monotonic : monotonic (fun n => n + 2) := by
  intro a b h
  exact Nat.add_le_add_right h 2

/-- The predicate "every element of a `List Bool` is `false`" is in
TM-backed polynomial time. -/
theorem inTimePolyTM_allFalse :
    inTimePolyTM (fun bs : List Bool => ∀ b ∈ bs, b = false) :=
  ⟨fun n => n + 2, ⟨decider⟩, timeBound_inOPoly, timeBound_monotonic⟩

end AllFalse

/-! ### `ExistsTrue` namespace — the dual decider

Decides `(fun bs : List Bool => ∃ b ∈ bs, b = true)`. Reuses the same
`scanRightUntilTM 2 1` machine as `AllFalse`, but swaps the verdict
mapping: now state 1 (scanner found `1`) is `acceptState`, and state 2
(scanner ran off the right end) is `rejectState`.

This is a tiny variation in terms of code, but it demonstrates that
the framework supports BOTH polarities of a predicate using the same
underlying TM with different verdict bindings. -/

namespace ExistsTrue

open AllFalse (encode encode_length encode_size_le encode_get_lt_two
  encode_get_of_false encode_get_of_true encode_all_zero_of_all_false
  exists_first_true)

/-- TM-backed decider for "some element of a `List Bool` is `true`". -/
def decider : DecidesBy (fun bs : List Bool => ∃ b ∈ bs, b = true)
    (fun n => n + 2) where
  encode := encode
  encodeBound := fun n => n + 1
  encodeBound_poly := inOPoly_add inOPoly_id (inOPoly_const 1)
  encodeBound_mono := fun _ _ h => Nat.add_le_add_right h 1
  encode_size := fun bs => encode_size_le bs
  M := scanRightUntilTM 2 1
  M_valid := scanRightUntilTM_valid 2 1 (by decide)
  M_tapes_pos := by decide
  acceptState := 1
  rejectState := 2
  halting_acc := rfl
  halting_rej := rfl
  accept_ne_reject := by decide
  decides_pos := by
    intro bs h_exists
    -- Some bit is `true` → scanner finds the first `1` → state 1 (= accept).
    rcases h_exists with ⟨b, hb_mem, hb_true⟩
    have h_some_true : ∃ b ∈ bs, b ≠ false :=
      ⟨b, hb_mem, by rw [hb_true]; decide⟩
    rcases exists_first_true bs h_some_true with
      ⟨k_first, h_first_lt, h_first_true, h_first_min⟩
    have h_first_lt' : k_first < (encode bs).length := by
      rw [encode_length]; exact h_first_lt
    have h_0k_lt : 0 + k_first < (encode bs).length := by
      rw [Nat.zero_add]; exact h_first_lt'
    have h_get_target :
        (encode bs).get ⟨0 + k_first, h_0k_lt⟩ = 1 := by
      have h_fin_eq : (⟨0 + k_first, h_0k_lt⟩ : Fin (encode bs).length) =
          ⟨k_first, h_first_lt'⟩ :=
        Fin.eq_of_val_eq (Nat.zero_add k_first)
      rw [h_fin_eq]
      exact encode_get_of_true bs k_first h_first_lt' h_first_lt h_first_true
    have h_get_before :
        ∀ k, k < k_first → ∃ (h : 0 + k < (encode bs).length),
          (encode bs).get ⟨0 + k, h⟩ < 2 ∧
            (encode bs).get ⟨0 + k, h⟩ ≠ 1 := by
      intro k hk
      have h_k_bs_lt : k < bs.length := Nat.lt_trans hk h_first_lt
      have h_k_enc_lt : k < (encode bs).length := by rw [encode_length]; exact h_k_bs_lt
      have h_0k_lt' : 0 + k < (encode bs).length := by rw [Nat.zero_add]; exact h_k_enc_lt
      have h_fin_eq : (⟨0 + k, h_0k_lt'⟩ : Fin (encode bs).length) =
          ⟨k, h_k_enc_lt⟩ :=
        Fin.eq_of_val_eq (Nat.zero_add k)
      refine ⟨h_0k_lt', ?_, ?_⟩
      · rw [h_fin_eq]; exact encode_get_lt_two bs k h_k_enc_lt
      · have h_get_k_false : bs.get ⟨k, h_k_bs_lt⟩ = false := h_first_min k h_k_bs_lt hk
        rw [h_fin_eq, encode_get_of_false bs k h_k_enc_lt h_k_bs_lt h_get_k_false]
        decide
    have hrun := scanRightUntilTM_run_found 2 1 [] (encode bs) k_first 0
      h_0k_lt h_get_target h_get_before
    rw [Nat.zero_add] at hrun
    have h_le : k_first + 1 ≤ encodable.size bs + 2 := by
      have h_le1 : k_first ≤ (encode bs).length := Nat.le_of_lt h_first_lt'
      have h_le2 : (encode bs).length ≤ encodable.size bs + 1 := encode_size_le bs
      calc k_first + 1
          ≤ (encode bs).length + 1 := Nat.add_le_add_right h_le1 1
        _ ≤ (encodable.size bs + 1) + 1 := Nat.add_le_add_right h_le2 1
        _ = encodable.size bs + 2 := by rw [Nat.add_assoc]
    have h_padded :
        runFlatTM (k_first + 1 + (encodable.size bs + 2 - (k_first + 1)))
          (scanRightUntilTM 2 1)
          { state_idx := 0, tapes := [([], 0, encode bs)] } =
        some { state_idx := 1, tapes := [([], k_first, encode bs)] } :=
      runFlatTM_extend hrun rfl
    have h_eq : k_first + 1 + (encodable.size bs + 2 - (k_first + 1)) =
        encodable.size bs + 2 :=
      Nat.add_sub_cancel' h_le
    rw [h_eq] at h_padded
    exact ⟨_, h_padded, rfl, rfl⟩
  decides_neg := by
    intro bs h_no_true
    -- No `true` → all entries are `false` → scanner runs off the end → state 2 (= reject).
    have h_all_false : ∀ b ∈ bs, b = false := by
      intro b hb
      cases b
      · rfl
      · exact absurd ⟨true, hb, rfl⟩ h_no_true
    have h_zero := encode_all_zero_of_all_false bs h_all_false
    have hrun := scanRightUntilTM_run_not_found 2 1 [] (encode bs) 0
      (Nat.zero_le _)
      (fun k _ h_klt => h_zero k h_klt)
    rw [Nat.sub_zero] at hrun
    have h_le : (encode bs).length + 1 ≤ encodable.size bs + 2 := by
      have h_le1 : (encode bs).length ≤ encodable.size bs + 1 := encode_size_le bs
      calc (encode bs).length + 1
          ≤ (encodable.size bs + 1) + 1 := Nat.add_le_add_right h_le1 1
        _ = encodable.size bs + 2 := by rw [Nat.add_assoc]
    have h_padded :
        runFlatTM ((encode bs).length + 1 +
            (encodable.size bs + 2 - ((encode bs).length + 1)))
          (scanRightUntilTM 2 1)
          { state_idx := 0, tapes := [([], 0, encode bs)] } =
        some { state_idx := 2, tapes := [([], (encode bs).length, encode bs)] } :=
      runFlatTM_extend hrun rfl
    have h_eq :
        (encode bs).length + 1 + (encodable.size bs + 2 - ((encode bs).length + 1)) =
          encodable.size bs + 2 :=
      Nat.add_sub_cancel' h_le
    rw [h_eq] at h_padded
    exact ⟨_, h_padded, rfl, rfl⟩

/-- The predicate "some element of a `List Bool` is `true`" is in
TM-backed polynomial time. -/
theorem inTimePolyTM_existsTrue :
    inTimePolyTM (fun bs : List Bool => ∃ b ∈ bs, b = true) :=
  ⟨fun n => n + 2, ⟨decider⟩,
    AllFalse.timeBound_inOPoly, AllFalse.timeBound_monotonic⟩

end ExistsTrue

end TMPrimitives
