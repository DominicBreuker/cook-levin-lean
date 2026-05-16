import Complexity.Complexity.Definitions
import Complexity.Complexity.MachineSemantics
import Complexity.Complexity.TMDecider
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
  encode_size := encode_size_le
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
  encode_size := encode_size_le
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
