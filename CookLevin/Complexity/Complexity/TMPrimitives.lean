import Complexity.Complexity.Definitions
import Complexity.Complexity.MachineSemantics
import Complexity.Complexity.TMDecider

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

`sig` here is the alphabet size: we enumerate `[0, sig)` plus `none`. -/
def bridgeEntries (sig : Nat) (srcState dstState : Nat) :
    List FlatTMTransEntry :=
  let mk (v : Option Nat) : FlatTMTransEntry :=
    { src_state := srcState
      src_tape_vals := [v]
      dst_state := dstState
      dst_write_vals := [v]
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
      exact List.mem_range.mp hv

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
  encode_size := fun x => Nat.zero_le _
  M := verdictTM 1 true
  M_valid := verdictTM_valid 1 true
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
  encode_size := fun x => Nat.zero_le _
  M := verdictTM 1 false
  M_valid := verdictTM_valid 1 false
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
      dst_write_vals := [some v]
      move_dirs := [TMMove.Rmove] }
  let mkHalt : FlatTMTransEntry :=
    { src_state := 0
      src_tape_vals := [some target]
      dst_state := 1
      dst_write_vals := [some target]
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
        exact h_target
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
          exact hvlt

end TMPrimitives
