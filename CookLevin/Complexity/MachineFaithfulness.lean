import Batteries.Data.List.Lemmas
import Complexity.Complexity.Definitions
import Complexity.Complexity.TapeMono

set_option autoImplicit false

/-! # Is `FlatTM` a Turing machine? — the defining properties, proven

## Why this file exists (top-down, 2026-08-09)

After FINDING AZ, a reviewer of `SATStrComp.SATStr_NPcompleteStr'` has exactly
**one** irreducible model question left: *is `FlatTM`/`stepFlatTM` really the
transition relation of a Turing machine?* It appears in the **hardness**
conjunct — "the reduction is computed by a real `FlatTM` inside a real
`runFlatTM` bound" — and nothing inside the development can settle it, because
it is a claim about our definitions matching the literature's.

Until now the only answer was *read `Complexity/Complexity/MachineSemantics.lean`
carefully*, plus five point witnesses in `StatementMeaning.lean` §3 (three write
cases, the left wall, blank ≠ zero) which pin behaviour **at named
configurations** and say nothing about all the others. This file replaces that
reading obligation with theorems that are **universally quantified over
machines, tapes and positions**.

## The claim, and the direction that matters

A reviewer's worry is not symmetric. If our model were **weaker** than a Turing
machine, "the reduction is computable by a `FlatTM` in polynomial time" would be
a *stronger* statement than the textbook one, and Cook–Levin's hardness half
would still hold a fortiori. The danger is the other direction: a model that is
**stronger** than a Turing machine — one whose single step does more work than a
TM step — would make the polynomial bound cheap and the theorem hollow.

That direction is exactly what the theorems below close. A `stepFlatTM` step:

| §  | property                                                       | theorem |
|----|----------------------------------------------------------------|---------|
| §2 | reads **one** cell, and which one is the head                  | `currentTapeSymbol_eq_tapeCell` |
| §3 | changes **at most the head cell** — everything else is fixed   | `tapeCell_tapeStep_of_ne` |
| §3 | moves the head by **at most one** cell                         | `tapeStep_head_le`, `tapeStep_le_head` |
| §3 | grows the tape by **at most one** cell                         | `tapeStep_length_le_succ` |
| §4 | is chosen **only** by (current state, symbol read)             | `find?_congr_of_read` |
| §5 | works over a **finite alphabet**, and cannot leave it          | `tapeStep_bounded`, `stuck_of_symbol_ge_sig` |
| §6 | works over a **finite state set**, and cannot leave it         | `stepFlatTM_state_lt` |
| §7 | therefore uses **space ≤ time**, and its head cannot jump      | `runFlatTM_single_local` |

The first seven rows are the properties a textbook uses to *define* a
deterministic single-tape Turing machine; the eighth is the run-level consequence
the three locality rows force. None of them holds of a random-access machine, and
none of them can be arranged by a lucky choice of encoding: they are statements
about `stepFlatTM` for every machine and every configuration, and ten of them are
metered exact in `Complexity/GateSurfaceGate.lean` §2.

## ⚠ What this file does NOT establish, stated plainly

1. **It is not a simulation.** It does not exhibit a translation between
   `FlatTM` and an *independently specified* machine (Mathlib's `Turing.TM0`).
   Such a translation would let a reviewer replace "is this a Turing machine?"
   with "is Mathlib's `Turing.TM0` a Turing machine?", which is a better
   question to be left with. The go/no-go probe for it is written up in
   `probes/MachineFaithfulnessProbe.lean` and ROADMAP risk **S10**; the verdict
   is *feasible, and it would buy a second opinion rather than a new guarantee*,
   because the direction a reviewer needs — ours is not too strong — is what §§2–7
   already give.
2. **Our model is genuinely weaker than a textbook TM in one respect, and this
   file makes that visible rather than hiding it.** The tape is **append-only**:
   a write strictly beyond the frontier (`head > right.length`) is silently
   dropped (`tapeCell_write_head`, the `else` branch). A textbook TM would perform
   that write. So `FlatTM` cannot create a written cell separated from the
   written region by a blank. This is a *restriction*, it is deliberate — the
   definition it replaced was non-local and falsified `cookTableau_correct`
   (see the docstring on `writeCurrentTapeSymbol`) — and by the asymmetry above
   it is safe for the theorem. `probes/MachineFaithfulnessProbe.lean` §2
   exhibits the divergence concretely.
3. **It says nothing about `Cmd`, `Op.cost` or the compiler.** By FINDING AZ it
   does not have to: the conjunct that mentions `FlatTM` never mentions the cost
   model, and vice versa.
-/

namespace Complexity.MachineFaithfulness

/-! ## §1 · What a configuration is

`FlatTMConfig` is a state index plus a list of tapes, each a triple
`(left, head, right)`. Two things a reader should know before anything else.

**The `left` component is dead.** `initFlatConfig` sets it to `[]` and no tape
primitive ever writes it (`writeCurrentTapeSymbol` and `moveTapeHead` both
return `tape.1` unchanged). So a configuration is really *(state, head, right)*:
the content lives entirely in `right` and the head is a `Nat` index into it. It
survives in the type because the flattening of the Coq development's `tape` type
had it, and removing it is a large mechanical edit with no mathematical content.

**One head per tape, and every machine on the proof path is single-tape.**
`M.tapes` is a field, and `Compile` emits `tapes := 1` throughout; §7's run-level
statements are therefore stated for one tape. -/

theorem writeCurrentTapeSymbol_left (tape : List Nat × Nat × List Nat) (w : Option Nat) :
    (writeCurrentTapeSymbol tape w).1 = tape.1 := by
  obtain ⟨left, head, right⟩ := tape
  cases w with
  | none => rfl
  | some s =>
      simp only [writeCurrentTapeSymbol]
      by_cases h : head < right.length
      · rw [dif_pos h]
      · rw [dif_neg h]
        by_cases he : head = right.length
        · rw [if_pos he]
        · rw [if_neg he]

theorem moveTapeHead_left (tape : List Nat × Nat × List Nat) (m : TMMove) :
    (moveTapeHead tape m).1 = tape.1 := by cases m <;> rfl

/-- **The `left` component is inert.** One step never touches it. -/
theorem tapeStep_left (tape : List Nat × Nat × List Nat) (w : Option Nat) (m : TMMove) :
    (tapeStep tape w m).1 = tape.1 := by
  rw [tapeStep, moveTapeHead_left, writeCurrentTapeSymbol_left]

/-- …and it starts empty, so it is `[]` forever. -/
theorem initFlatConfig_left (M : FlatTM) (initTapes : List (List Nat))
    (tp : List Nat × Nat × List Nat) (h : tp ∈ (initFlatConfig M initTapes).tapes) :
    tp.1 = [] := by
  simp only [initFlatConfig, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-! ## §2 · The tape is a partial function whose domain is a prefix

`tapeCell tape p` is the symbol in cell `p`: `right[p]?`. Cells beyond the
written region read `none` — the **blank**, which is a value distinct from every
`some v`, so blank and the symbol `0` are not confused (`blank_ne_zero`).

The two facts that make this a *tape*: the head reads exactly the cell it is on
(`currentTapeSymbol_eq_tapeCell`), and the written cells are always an initial
segment (`written_prefix`). The second is the invariant the append-only write
rule maintains — see the module docstring's caveat 2. -/

/-- The symbol in cell `p` of a tape; `none` is the blank. -/
def tapeCell (tape : List Nat × Nat × List Nat) (p : Nat) : Option Nat := tape.2.2[p]?

/-- **The head reads exactly one cell, the one it is on.** -/
theorem currentTapeSymbol_eq_tapeCell (tape : List Nat × Nat × List Nat) :
    currentTapeSymbol tape = tapeCell tape tape.2.1 := by
  unfold currentTapeSymbol tapeCell
  split
  · next h => rw [List.getElem?_eq_getElem h]; rfl
  · next h => rw [List.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- A cell is blank exactly when it is at or beyond the frontier. -/
theorem tapeCell_eq_none_iff (tape : List Nat × Nat × List Nat) (p : Nat) :
    tapeCell tape p = none ↔ tape.2.2.length ≤ p :=
  List.getElem?_eq_none_iff

/-- **Blank is not a symbol.** The machine can tell an unwritten cell from a
cell holding `0`. -/
theorem blank_ne_zero : (none : Option Nat) ≠ some 0 := by decide

/-- **The written cells are always a prefix.** If cell `p` is written then so is
every cell to its left. This is the invariant that the append-only write rule of
`writeCurrentTapeSymbol` exists to maintain. -/
theorem written_prefix (tape : List Nat × Nat × List Nat) (p q : Nat) (hq : q < p)
    (hp : tapeCell tape p ≠ none) : tapeCell tape q ≠ none := by
  rw [Ne, tapeCell_eq_none_iff] at hp ⊢
  omega

/-! ## §3 · Locality — one step touches one cell and moves one place

This is the heart of the file and the reason a `FlatTM` step is not a
random-access step. `tapeStep` is `writeCurrentTapeSymbol` followed by
`moveTapeHead`, and:

* every cell other than the head's is **literally unchanged**;
* the head cell takes the written value — unless the head is strictly beyond the
  frontier, in which case the write is dropped and the cell stays blank
  (the append-only restriction; see the module docstring's caveat 2);
* the head index changes by at most one, and cannot go below `0` because it is a
  `Nat` — that is the one-way-infinite tape, with `Lmove` at `0` a no-op;
* the tape grows by at most one cell. -/

theorem tapeCell_moveTapeHead (tape : List Nat × Nat × List Nat) (m : TMMove) (p : Nat) :
    tapeCell (moveTapeHead tape m) p = tapeCell tape p := by
  unfold tapeCell
  rw [moveTapeHead_content]

/-- **Only the head cell can change.** Every other cell of the tape reads the
same before and after the write. -/
theorem tapeCell_write_of_ne (tape : List Nat × Nat × List Nat) (w : Option Nat)
    (p : Nat) (hp : p ≠ tape.2.1) :
    tapeCell (writeCurrentTapeSymbol tape w) p = tapeCell tape p := by
  obtain ⟨left, head, right⟩ := tape
  simp only at hp
  cases w with
  | none => rfl
  | some s =>
      simp only [writeCurrentTapeSymbol, tapeCell]
      by_cases h : head < right.length
      · rw [dif_pos h]
        simp only
        rw [← List.set_eq_take_cons_drop s h, List.getElem?_set_ne hp.symm]
      · rw [dif_neg h]
        by_cases he : head = right.length
        · rw [if_pos he]
          simp only
          subst he
          rcases Nat.lt_or_ge p right.length with hlt | hge
          · rw [List.getElem?_append_left hlt]
          · rw [List.getElem?_eq_none (by simp; omega),
                List.getElem?_eq_none (by omega)]
        · rw [if_neg he]

/-- **Only the head cell can change**, stated for a whole step (write, then
move). The move never touches content, so this is the previous lemma. -/
theorem tapeCell_tapeStep_of_ne (tape : List Nat × Nat × List Nat) (w : Option Nat)
    (m : TMMove) (p : Nat) (hp : p ≠ tape.2.1) :
    tapeCell (tapeStep tape w m) p = tapeCell tape p := by
  rw [tapeStep, tapeCell_moveTapeHead]
  exact tapeCell_write_of_ne tape w p hp

/-- **What the head cell becomes.** A `none`-write leaves it alone; a
`some s` write installs `s` when the head is at or before the frontier, and is
**dropped** when the head is strictly beyond it. -/
theorem tapeCell_write_head (tape : List Nat × Nat × List Nat) (s : Nat) :
    tapeCell (writeCurrentTapeSymbol tape (some s)) tape.2.1 =
      if tape.2.1 ≤ tape.2.2.length then some s else none := by
  obtain ⟨left, head, right⟩ := tape
  simp only [writeCurrentTapeSymbol, tapeCell]
  by_cases h : head < right.length
  · rw [dif_pos h, if_pos (Nat.le_of_lt h)]
    simp only
    rw [← List.set_eq_take_cons_drop s h, List.getElem?_set_self (by simpa using h)]
  · rw [dif_neg h]
    by_cases he : head = right.length
    · rw [if_pos he, if_pos (Nat.le_of_eq he)]
      simp only
      subst he
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    · rw [if_neg he, if_neg (by omega)]
      simp only
      exact List.getElem?_eq_none (by omega)

/-- A `none`-write is a no-op everywhere. -/
theorem write_none (tape : List Nat × Nat × List Nat) :
    writeCurrentTapeSymbol tape none = tape := rfl

/-- **The head moves at most one cell right.** -/
theorem tapeStep_head_le (tape : List Nat × Nat × List Nat) (w : Option Nat) (m : TMMove) :
    (tapeStep tape w m).2.1 ≤ tape.2.1 + 1 := by
  obtain ⟨left, head, right⟩ := tape
  have hw : (writeCurrentTapeSymbol (left, head, right) w).2.1 = head := by
    cases w with
    | none => rfl
    | some s =>
        simp only [writeCurrentTapeSymbol]
        by_cases h : head < right.length
        · rw [dif_pos h]
        · rw [dif_neg h]
          by_cases he : head = right.length
          · rw [if_pos he]
          · rw [if_neg he]
  rw [tapeStep]
  cases m <;> simp only [moveTapeHead, hw] <;> omega

/-- **The head moves at most one cell left**, and — because the head is a `Nat`
— it can never move left of cell `0`. The tape is one-way infinite. -/
theorem tapeStep_le_head (tape : List Nat × Nat × List Nat) (w : Option Nat) (m : TMMove) :
    tape.2.1 ≤ (tapeStep tape w m).2.1 + 1 := by
  obtain ⟨left, head, right⟩ := tape
  have hw : (writeCurrentTapeSymbol (left, head, right) w).2.1 = head := by
    cases w with
    | none => rfl
    | some s =>
        simp only [writeCurrentTapeSymbol]
        by_cases h : head < right.length
        · rw [dif_pos h]
        · rw [dif_neg h]
          by_cases he : head = right.length
          · rw [if_pos he]
          · rw [if_neg he]
  rw [tapeStep]
  cases m <;> simp only [moveTapeHead, hw] <;> omega

/-- **The left end is a wall.** `Lmove` at cell `0` leaves the head at `0`,
for every tape — the general form of `StatementMeaning.left_end_is_a_wall`. -/
theorem left_end_is_a_wall (tape : List Nat × Nat × List Nat) (h : tape.2.1 = 0) :
    (moveTapeHead tape TMMove.Lmove).2.1 = 0 := by
  simp only [moveTapeHead, h]

/-- **The tape grows by at most one cell per step.** With
`TapeMono.tapeStep_length_le` (it never shrinks) this pins the frontier: one
step moves it by `0` or `1`. -/
theorem tapeStep_length_le_succ (tape : List Nat × Nat × List Nat) (w : Option Nat) (m : TMMove) :
    (tapeStep tape w m).2.2.length ≤ tape.2.2.length + 1 := by
  obtain ⟨left, head, right⟩ := tape
  rw [tapeStep, moveTapeHead_content]
  cases w with
  | none => simp [writeCurrentTapeSymbol]
  | some s =>
      simp only [writeCurrentTapeSymbol]
      by_cases h : head < right.length
      · rw [dif_pos h]
        simp only [List.length_append, List.length_take, List.length_cons,
          List.length_drop, Nat.min_eq_left (Nat.le_of_lt h)]
        omega
      · rw [dif_neg h]
        by_cases he : head = right.length
        · rw [if_pos he]; simp
        · rw [if_neg he]; simp

/-! ## §4 · The step is chosen by (state, symbol read) and nothing else

`stepFlatTM` selects a transition entry with `M.trans.find?`, i.e. the **first**
entry matching the configuration, which is what makes the machine deterministic
given the table. What must also be true for it to be a *finite control* is that
the match consults only the current state and the symbols under the heads — not
the tape's length, not the head's position, not any cell away from the head.

`entryMatchesConfig` is `entry.src_state == cfg.state_idx && entry.src_tape_vals
= cfg.tapes.map currentTapeSymbol`, so this is visible by inspection; the theorem
states it as a congruence, which is the form that cannot rot.

⚠ **Read this as being about the entry SELECTED, not about the tape effect.**
Those two come apart here, and it is the one place where `FlatTM` is not
literally a textbook machine. A textbook TM's *effect* is a function of
`(state, symbol read)`: write `s`, move `d`. Ours is not — by caveat 2 of the
module docstring, at a blank cell the same write is performed at the frontier and
dropped one cell further right, and the machine cannot see which case it is in.
So the step consults one bit of information the finite control does not have:
where the frontier is.

That is a **restriction**, not extra power — the machine loses a write it would
otherwise have made — so it is safe in the direction that matters (see the module
docstring). But it must not be papered over: `FlatTM` is the class of
deterministic single-tape Turing machines **restricted to append-only tapes**,
not the full class. `probes/MachineFaithfulnessProbe.lean` §2 exhibits the two
configurations that separate them, in four lines. -/

theorem entryMatchesConfig_congr (entry : FlatTMTransEntry) (cfg₁ cfg₂ : FlatTMConfig)
    (hs : cfg₁.state_idx = cfg₂.state_idx)
    (ht : cfg₁.tapes.map currentTapeSymbol = cfg₂.tapes.map currentTapeSymbol) :
    entryMatchesConfig entry cfg₁ = entryMatchesConfig entry cfg₂ := by
  simp only [entryMatchesConfig, hs, ht]

/-- **The finite control reads only (state, symbols under the heads).** Two
configurations agreeing on those select the *same* transition entry — however
different their tapes are elsewhere. -/
theorem find?_congr_of_read (M : FlatTM) (cfg₁ cfg₂ : FlatTMConfig)
    (hs : cfg₁.state_idx = cfg₂.state_idx)
    (ht : cfg₁.tapes.map currentTapeSymbol = cfg₂.tapes.map currentTapeSymbol) :
    M.trans.find? (fun e => entryMatchesConfig e cfg₁) =
      M.trans.find? (fun e => entryMatchesConfig e cfg₂) := by
  congr 1
  funext e
  exact entryMatchesConfig_congr e cfg₁ cfg₂ hs ht

/-! ## §5 · A finite alphabet, and the machine cannot leave it

`M.sig` is the alphabet size. `validFlatTM` bounds both the symbols an entry
matches on and the symbols it writes; the two theorems below turn that into the
two statements a reader wants.

**Closure**: a valid machine started on a tape over `{0,…,sig-1}` keeps the tape
over `{0,…,sig-1}`. **Enforcement**: if a symbol `≥ sig` ever *does* appear
under the head — which `runFlatTM` permits, since unlike `execFlatTM` it does
not re-check `isValidFlatTapes` — a valid machine is **stuck**: no entry can
match it. So `sig` is a real alphabet bound and not a decorative field. -/

theorem writeCurrentTapeSymbol_bounded (sig : Nat) (tape : List Nat × Nat × List Nat)
    (w : Option Nat) (hw : ∀ v, w = some v → v < sig)
    (ht : tapeSymbolsBounded sig tape.2.2) :
    tapeSymbolsBounded sig (writeCurrentTapeSymbol tape w).2.2 := by
  obtain ⟨left, head, right⟩ := tape
  simp only at ht
  cases w with
  | none => exact ht
  | some s =>
      have hs : s < sig := hw s rfl
      simp only [writeCurrentTapeSymbol]
      by_cases h : head < right.length
      · rw [dif_pos h]
        intro x hx
        simp only [List.mem_append, List.mem_cons] at hx
        rcases hx with hx | hx | hx
        · exact ht x (List.mem_of_mem_take hx)
        · exact hx ▸ hs
        · exact ht x (List.mem_of_mem_drop hx)
      · rw [dif_neg h]
        by_cases he : head = right.length
        · rw [if_pos he]
          intro x hx
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx
          · exact ht x hx
          · exact hx ▸ hs
        · rw [if_neg he]
          exact ht

/-- **Alphabet closure for one step.** -/
theorem tapeStep_bounded (sig : Nat) (tape : List Nat × Nat × List Nat)
    (w : Option Nat) (m : TMMove) (hw : ∀ v, w = some v → v < sig)
    (ht : tapeSymbolsBounded sig tape.2.2) :
    tapeSymbolsBounded sig (tapeStep tape w m).2.2 := by
  rw [tapeStep]
  unfold tapeSymbolsBounded
  rw [moveTapeHead_content]
  exact writeCurrentTapeSymbol_bounded sig tape w hw ht

/-- **`sig` is enforced, not decorative.** If the symbol under some head is
`≥ M.sig`, a valid machine has no transition available: the step is `none`.
(`runFlatTM` then stalls at that configuration for any remaining budget —
`MachineSemantics.runFlatTM_stuck`.) -/
theorem stuck_of_symbol_ge_sig (M : FlatTM) (cfg : FlatTMConfig) (hM : validFlatTM M)
    (v : Nat) (hv : M.sig ≤ v) (hmem : some v ∈ cfg.tapes.map currentTapeSymbol) :
    stepFlatTM M cfg = none := by
  rcases hstep : stepFlatTM M cfg with _ | cfg'
  · rfl
  · exfalso
    obtain ⟨entry, hfind, -⟩ :
        ∃ entry, M.trans.find? (fun e => entryMatchesConfig e cfg) = some entry ∧
          applyTransitionEntry cfg entry = some cfg' := by
      simpa [stepFlatTM, Option.bind_eq_some_iff] using hstep
    have hmem_trans : entry ∈ M.trans := List.mem_of_find?_eq_some hfind
    have hmatch : entryMatchesConfig entry cfg = true :=
      List.find?_some (p := fun e => entryMatchesConfig e cfg) hfind
    have hvals : entry.src_tape_vals = cfg.tapes.map currentTapeSymbol := by
      simp only [entryMatchesConfig, Bool.and_eq_true, decide_eq_true_eq] at hmatch
      exact hmatch.2
    have hbound := (hM.2.2 entry hmem_trans).2.2.2.2.2.1
    have := hbound (some v) (hvals ▸ hmem)
    simp only at this
    omega

/-! ## §6 · A finite state set, and the machine cannot leave it

`M.states` is the number of states and `M.halt` is a bit per state. A valid
machine starts inside the state set and every transition lands inside it, so the
reachable control states are a subset of `Fin M.states` — a genuinely finite
control. -/

/-- Every step of a valid machine lands in a declared state. -/
theorem stepFlatTM_state_lt (M : FlatTM) (cfg cfg' : FlatTMConfig) (hM : validFlatTM M)
    (hstep : stepFlatTM M cfg = some cfg') : cfg'.state_idx < M.states := by
  obtain ⟨entry, hfind, happly⟩ :
      ∃ entry, M.trans.find? (fun e => entryMatchesConfig e cfg) = some entry ∧
        applyTransitionEntry cfg entry = some cfg' := by
    simpa [stepFlatTM, Option.bind_eq_some_iff] using hstep
  have hmem : entry ∈ M.trans := List.mem_of_find?_eq_some hfind
  have hstate : cfg'.state_idx = entry.dst_state := by
    unfold applyTransitionEntry at happly
    split at happly
    · rw [← Option.some.injEq _ _ |>.mp happly]
    · exact absurd happly (by simp)
  rw [hstate]
  exact (hM.2.2 entry hmem).2.1

/-- The initial state of a valid machine is a declared state. -/
theorem initFlatConfig_state_lt (M : FlatTM) (initTapes : List (List Nat))
    (hM : validFlatTM M) : (initFlatConfig M initTapes).state_idx < M.states := hM.1

/-- **Every reachable state of a valid machine is declared.** -/
theorem runFlatTM_state_lt (M : FlatTM) (hM : validFlatTM M) :
    ∀ (n : Nat) (cfg cfg' : FlatTMConfig), cfg.state_idx < M.states →
      runFlatTM n M cfg = some cfg' → cfg'.state_idx < M.states := by
  intro n
  induction n with
  | zero =>
      intro cfg cfg' hlt hrun
      simp only [runFlatTM, Option.some.injEq] at hrun
      exact hrun ▸ hlt
  | succ n ih =>
      intro cfg cfg' hlt hrun
      simp only [runFlatTM] at hrun
      by_cases hh : haltingStateReached M cfg = true
      · rw [if_pos hh, Option.some.injEq] at hrun
        exact hrun ▸ hlt
      · rw [if_neg hh] at hrun
        cases hstep : stepFlatTM M cfg with
        | none => rw [hstep, Option.some.injEq] at hrun; exact hrun ▸ hlt
        | some c =>
            rw [hstep] at hrun
            exact ih c cfg' (stepFlatTM_state_lt M cfg c hM hstep) hrun

/-! ## §7 · The run-level consequences: space ≤ time, and no jumping

Everything above is about one step. Iterating §3 gives the two facts a
complexity theorist actually uses about a machine model, and they are exactly
what would fail for a random-access model: after `n` steps the tape has grown by
at most `n` cells (**space ≤ time**) and the head has travelled at most `n`
cells (**no jumping**).

Stated for one tape, which is all `Compile` emits. Together with
`TapeMono.runFlatTM_single_length_le` (the tape never shrinks) they sandwich the
frontier along any run. -/

/-- **One step, packaged**: a one-tape configuration steps to a one-tape
configuration obtained by `tapeStep`, with the write and move taken from the
selected entry. Everything in this section is an induction over this lemma. -/
theorem stepFlatTM_single (M : FlatTM) (cfg cfg' : FlatTMConfig)
    (tp : List Nat × Nat × List Nat) (htape : cfg.tapes = [tp])
    (hstep : stepFlatTM M cfg = some cfg') :
    ∃ w m, cfg'.tapes = [tapeStep tp w m] := by
  obtain ⟨entry, -, happly⟩ :
      ∃ entry, M.trans.find? (fun e => entryMatchesConfig e cfg) = some entry ∧
        applyTransitionEntry cfg entry = some cfg' := by
    simpa [stepFlatTM, Option.bind_eq_some_iff] using hstep
  rw [applyTransitionEntry, htape] at happly
  simp only [List.length_singleton] at happly
  split at happly
  · next hg =>
      obtain ⟨hw, hm⟩ := hg
      obtain ⟨w, hwe⟩ := List.length_eq_one_iff.mp hw.symm
      obtain ⟨m, hme⟩ := List.length_eq_one_iff.mp hm.symm
      rw [hwe, hme] at happly
      simp only [List.zip_cons_cons, List.zip_nil_right, List.zipWith_cons_cons,
        List.zipWith_nil_right, Option.some.injEq] at happly
      exact ⟨w, m, by rw [← happly]⟩
  · exact absurd happly (by simp)

/-- **Space ≤ time, and the head cannot jump.** Along a run of `n` steps from a
one-tape configuration, the tape has grown by at most `n` cells and the head has
moved at most `n` cells to the right. (It cannot move left of `0` at all — see
`left_end_is_a_wall`.) -/
theorem runFlatTM_single_local (M : FlatTM) :
    ∀ (n : Nat) (cfg cfg' : FlatTMConfig) (tp : List Nat × Nat × List Nat),
      cfg.tapes = [tp] → runFlatTM n M cfg = some cfg' →
      ∃ tp', cfg'.tapes = [tp'] ∧
        tp'.2.2.length ≤ tp.2.2.length + n ∧ tp'.2.1 ≤ tp.2.1 + n := by
  intro n
  induction n with
  | zero =>
      intro cfg cfg' tp htape hrun
      simp only [runFlatTM, Option.some.injEq] at hrun
      exact ⟨tp, hrun ▸ htape, by omega, by omega⟩
  | succ n ih =>
      intro cfg cfg' tp htape hrun
      simp only [runFlatTM] at hrun
      by_cases hh : haltingStateReached M cfg = true
      · rw [if_pos hh, Option.some.injEq] at hrun
        exact ⟨tp, hrun ▸ htape, by omega, by omega⟩
      · rw [if_neg hh] at hrun
        cases hstep : stepFlatTM M cfg with
        | none =>
            rw [hstep, Option.some.injEq] at hrun
            exact ⟨tp, hrun ▸ htape, by omega, by omega⟩
        | some c =>
            rw [hstep] at hrun
            obtain ⟨w, m, hc⟩ := stepFlatTM_single M cfg c tp htape hstep
            obtain ⟨tp', hcfg', hlen, hhead⟩ := ih c cfg' (tapeStep tp w m) hc hrun
            refine ⟨tp', hcfg', ?_, ?_⟩
            · have := tapeStep_length_le_succ tp w m
              omega
            · have := tapeStep_head_le tp w m
              omega

/-- **The same, from the initial configuration.** After `n` steps on input
`input`, a single-tape machine has written at most `input.length + n` cells and
its head is within `n` of the left end. -/
theorem runFlatTM_init_local (M : FlatTM) (n : Nat) (input : List Nat)
    (cfg' : FlatTMConfig) (tp' : List Nat × Nat × List Nat)
    (hrun : runFlatTM n M (initFlatConfig M [input]) = some cfg')
    (htape' : cfg'.tapes = [tp']) :
    tp'.2.2.length ≤ input.length + n ∧ tp'.2.1 ≤ n := by
  have htape : (initFlatConfig M [input]).tapes = [([], 0, input)] := by
    simp [initFlatConfig]
  obtain ⟨tp'', hc, hlen, hhead⟩ :=
    runFlatTM_single_local M n _ cfg' ([], 0, input) htape hrun
  rw [hc, List.cons.injEq] at htape'
  obtain ⟨rfl, -⟩ := htape'
  exact ⟨by simpa using hlen, by simpa using hhead⟩

/-! ## §8 · Halting, and what a run returning `some` does and does not mean

Restated here for completeness, because "is this a Turing machine?" includes
"does it stop when it says it stops?". Both are proven in
`MachineSemantics.lean`; `StatementMeaning.lean` §4 exhibits the machine that
separates *stuck* from *halted*.

* `runFlatTM_of_halting` — a halting configuration is **absorbing**: further
  budget changes nothing. This is what makes a generous time bound sound.
* `runFlatTM_stuck` — a *stuck* configuration (non-halting, no matching entry)
  is absorbing too, and `runFlatTM` returns `some` for it. So `= some cfg` is
  **not** a halting claim; `haltingStateReached M cfg = true` is, and it is what
  `ComputesBy.computes` demands. -/

theorem halting_is_absorbing (M : FlatTM) (cfg : FlatTMConfig) (steps : Nat)
    (h : haltingStateReached M cfg = true) : runFlatTM steps M cfg = some cfg :=
  runFlatTM_of_halting M cfg steps h

theorem stuck_is_absorbing (M : FlatTM) (cfg : FlatTMConfig)
    (h_not_halt : haltingStateReached M cfg = false) (h_step : stepFlatTM M cfg = none)
    (m : Nat) : runFlatTM m M cfg = some cfg :=
  runFlatTM_stuck M cfg h_not_halt h_step m

end Complexity.MachineFaithfulness
