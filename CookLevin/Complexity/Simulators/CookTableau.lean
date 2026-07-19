import Complexity.Complexity.MachineSemantics
import Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP
import Mathlib.Tactic

set_option autoImplicit false

/-! # Cook tableau construction (Risk S1) — v2, the full card algebra

This file holds the **real** central Cook–Levin construction "a single-tape TM
accepts its input iff a 2D tableau is coverable" — the honest replacement for
the vacuous `FlatSingleTMGenNP ⪯p FlatTCC` stub. **v2 (2026-07-17)** replaces
the v1 feasibility probe after a risk review found v1's bijection
`cookTableau_correct` was *false as stated*, for four independent reasons:

1. **Non-local jump-writes (BLOCKING, fixed in `MachineSemantics.lean`).**
   The old flat write semantics zero-padded writes beyond the tape frontier, so
   one TM step could rewrite unboundedly many cells arbitrarily far from the
   head — inexpressible by *any* local 3-window card family. The semantics now
   make the tape append-only at the frontier (see the finding docstring on
   `writeCurrentTapeSymbol`); one step changes at most the head cell.
2. **Incomplete card families.** v1 had head-at-*center* transition windows
   only. A correct tableau needs cards for the head at all three window
   positions, *incoming-head* cards for the two windows the head enters
   (Rmove: head-first conc off an all-tape premise; Lmove: head-third), halt
   freeze at all three positions, and boundary-marker variants. Crucially there
   is **no all-tape-premise card with the head at the conc's second cell** —
   that absence is what blocks spurious heads materialising far from the real
   head (the completeness linchpin; see `step_of_validStep`).
3. **Left-edge detection.** `moveTapeHead` clamps `Lmove` at position `0`; a
   position-independent card cannot see "tape position 0", so rows now start
   with a **boundary marker** `bCell` and the clamp cards key on it.
4. **`write = none` bug.** v1's transition card wrote the *blank* for a
   `none`-write; the machine keeps the read symbol. The card writes are now
   computed by `wEff`, which also implements the frontier-sensitive void write
   (a `some`-write on a blank read lands beyond the frontier — detectable
   window-locally from a *blank left neighbour* — and leaves the cell blank).

Two further correctness prerequisites are handled by **normalising the
transition table** (`normTrans`): `validFlatTM` does not force key-uniqueness
(`stepFlatTM` uses `find?`, so cards from *shadowed duplicate* entries would
break completeness) and matching entries with malformed `dst` lists make
`applyTransitionEntry` return `none` (stuck) while a naive card would still
fire. `normTrans` keeps the first entry per `(src_state, src_tape_vals)` key,
then drops shape-malformed entries and entries out of halting states (the run
never fires those — `runFlatTM` checks halting first).

## Status

* `cookTableau` — genuine computable construction, **no if-on-the-answer**.
* `cookTableau_wellformed` — PROVEN.
* `cookTableau_correct` — **restated** (with the previously-missing
  `validFlatTM` / `tapes = 1` / alphabet hypotheses, without which even the
  trivial-machine cases are false) and **decomposed** into the skeleton below;
  the assembly from the sub-lemmas is PROVEN. **Direction (1a) is PROVEN
  (2026-07-18)**: `stepFlatTM_normM`, `ConfFits_step`, `validStep_of_step`,
  `validStep_of_halt`, and `satFinal_of_halt` are all closed, on the shared
  window machinery (`rowCell`/`rowX`/`confRow_window` + the per-family
  membership lemmas + `copy_window`). **`halt_of_satFinal` is PROVEN
  (2026-07-18-b)** on the cell-code disjointness algebra (`hCell_val_lb`/
  `_ub`, `tCell_ne_hCell`, `hCell_ne_bCell`, `tCell_ne_bCell`, `hCell_inj`/
  `tCell_inj` — also stage-(i) fodder for the (1b) inversion).
  **Directions (2) `cover_of_run` and (3) `run_of_cover` are PROVEN
  (2026-07-18-c)** on the trajectory inductions, and **the (1b) inversion
  `step_of_validStep` is PROVEN (2026-07-18-d)** — so `cookTableau_correct`
  is now **sorry-free**. The only remaining `sorry` in this file is
  `cookTableau_size_bound`.
* `cookTableau_correct_immediateHalt` — the constrained-case probe, PROVEN
  against the v2 cards (validates the redesigned families on the base case).
* `cookTableau_size_bound` — restated (degree 10, see the note) and `sorry`.
* **Certificate nondeterminism is NOT here yet**: this file is the
  *deterministic core* `acceptsFlatTM M [s] steps ↔ tableau coverable`. The
  full S1 reduction needs a *prelude/guess layer* on top (wildcard cells in
  the cert region of row 0, guess cards resolving them in the first covering
  step, budget `steps + 1`) — the Coq port's `preludeRules`. Design notes in
  `HANDOFF.md`.

Probe: `probes/S1TableauProbe.lean` (`#eval` window-coverage of consecutive
configuration rows against `cookCards` on concrete machines, including the
frontier/void-write paths). -/

namespace Complexity.Simulators

open FlatTCC TCC

/-! ## Alphabet

A tableau cell is one of:
* the **boundary marker** (top code `(M.sig+1)·(M.states+2)`), row position 0;
* a **tape cell** carrying a tape symbol from `Fin (M.sig + 1)` — the `+1` is
  an explicit blank (index `M.sig`) for positions at/beyond the tape frontier;
* a **head cell** carrying `(state, symbol-under-head)`, states in
  `Fin (M.states + 1)` (one overflow slot so the construction is total).

So `|Σ| = (M.sig + 1) · (M.states + 2) + 1`. Under the run invariant
(tape symbols `< M.sig`), an in-range tape cell is never the blank, so
**"cell = blank ⟺ position ≥ tape length"** — the frontier is window-locally
detectable, which `wEff` exploits. -/

/-- The tableau alphabet size. -/
def Sg (M : FlatTM) : Nat := (M.sig + 1) * (M.states + 2) + 1

theorem tCell_lt (M : FlatTM) (b : Fin (M.sig + 1)) : b.1 < Sg M := by
  have hb := b.2
  have : (M.sig + 1) ≤ (M.sig + 1) * (M.states + 2) :=
    Nat.le_mul_of_pos_right (M.sig + 1) (show 0 < M.states + 2 by omega)
  unfold Sg
  omega

theorem hCell_lt (M : FlatTM) (q : Fin (M.states + 1)) (b : Fin (M.sig + 1)) :
    (M.sig + 1) * (q.1 + 1) + b.1 < Sg M := by
  have hq := q.2
  have hb := b.2
  unfold Sg
  have hstep : (M.sig + 1) * (q.1 + 1) + (M.sig + 1) ≤ (M.sig + 1) * (M.states + 2) := by
    have : (M.sig + 1) * (q.1 + 1) + (M.sig + 1) = (M.sig + 1) * (q.1 + 2) := by ring
    rw [this]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- A tape cell. -/
def tCell (M : FlatTM) (b : Fin (M.sig + 1)) : Fin (Sg M) := ⟨b.1, tCell_lt M b⟩

/-- A head cell carrying `(state, symbol-under-head)`. -/
def hCell (M : FlatTM) (q : Fin (M.states + 1)) (b : Fin (M.sig + 1)) : Fin (Sg M) :=
  ⟨(M.sig + 1) * (q.1 + 1) + b.1, hCell_lt M q b⟩

/-- The boundary marker (row position 0). -/
def bCell (M : FlatTM) : Fin (Sg M) :=
  ⟨(M.sig + 1) * (M.states + 2), by unfold Sg; omega⟩

/-! ### Cell-code disjointness — the S1 code algebra

The three cell families occupy disjoint code bands: `tCell` codes are
`< M.sig + 1`, `hCell` codes lie in `[M.sig + 1, (M.sig + 1)·(M.states + 2))`,
and `bCell` is the top code `(M.sig + 1)·(M.states + 2)`. Consumed by
`halt_of_satFinal` (a final-pattern cell in `confRow` can only be the head
cell) and by stage (i) of the `step_of_validStep` inversion (classifying a
matched card by its premise cells). -/

theorem hCell_val_lb (M : FlatTM) (q : Fin (M.states + 1)) (b : Fin (M.sig + 1)) :
    M.sig + 1 ≤ (hCell M q b).1 := by
  show M.sig + 1 ≤ (M.sig + 1) * (q.1 + 1) + b.1
  have h1 : M.sig + 1 ≤ (M.sig + 1) * (q.1 + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem hCell_val_ub (M : FlatTM) (q : Fin (M.states + 1)) (b : Fin (M.sig + 1)) :
    (hCell M q b).1 < (M.sig + 1) * (M.states + 2) := by
  show (M.sig + 1) * (q.1 + 1) + b.1 < _
  have hb := b.2
  have hq := q.2
  have h1 : (M.sig + 1) * (q.1 + 2) ≤ (M.sig + 1) * (M.states + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp : (M.sig + 1) * (q.1 + 2)
      = (M.sig + 1) * (q.1 + 1) + (M.sig + 1) := by ring
  omega

theorem tCell_ne_hCell (M : FlatTM) (a b : Fin (M.sig + 1))
    (q : Fin (M.states + 1)) : tCell M a ≠ hCell M q b := by
  intro h
  have hv : a.1 = (M.sig + 1) * (q.1 + 1) + b.1 := congrArg Fin.val h
  have h1 := a.2
  have h2 : M.sig + 1 ≤ (M.sig + 1) * (q.1 + 1) + b.1 := hCell_val_lb M q b
  omega

theorem hCell_ne_bCell (M : FlatTM) (q : Fin (M.states + 1))
    (b : Fin (M.sig + 1)) : hCell M q b ≠ bCell M := by
  intro h
  have hv : (M.sig + 1) * (q.1 + 1) + b.1 = (M.sig + 1) * (M.states + 2) :=
    congrArg Fin.val h
  have h1 : (M.sig + 1) * (q.1 + 1) + b.1 < (M.sig + 1) * (M.states + 2) :=
    hCell_val_ub M q b
  omega

theorem tCell_ne_bCell (M : FlatTM) (a : Fin (M.sig + 1)) :
    tCell M a ≠ bCell M := by
  intro h
  have hv : a.1 = (M.sig + 1) * (M.states + 2) := congrArg Fin.val h
  have h1 := a.2
  have h2 : M.sig + 1 ≤ (M.sig + 1) * (M.states + 2) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem tCell_inj (M : FlatTM) {a b : Fin (M.sig + 1)}
    (h : tCell M a = tCell M b) : a = b := by
  have hv := congrArg Fin.val h
  exact Fin.ext hv

theorem hCell_inj (M : FlatTM) {q1 q2 : Fin (M.states + 1)}
    {b1 b2 : Fin (M.sig + 1)} (h : hCell M q1 b1 = hCell M q2 b2) :
    q1 = q2 ∧ b1 = b2 := by
  have hv : (M.sig + 1) * (q1.1 + 1) + b1.1
      = (M.sig + 1) * (q2.1 + 1) + b2.1 := congrArg Fin.val h
  have hb1 := b1.2
  have hb2 := b2.2
  have hq : q1.1 = q2.1 := by
    rcases Nat.lt_trichotomy q1.1 q2.1 with hlt | heq | hgt
    · exfalso
      have hle : (M.sig + 1) * (q1.1 + 1 + 1) ≤ (M.sig + 1) * (q2.1 + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hexp : (M.sig + 1) * (q1.1 + 1 + 1)
          = (M.sig + 1) * (q1.1 + 1) + (M.sig + 1) := by ring
      omega
    · exact heq
    · exfalso
      have hle : (M.sig + 1) * (q2.1 + 1 + 1) ≤ (M.sig + 1) * (q1.1 + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hexp : (M.sig + 1) * (q2.1 + 1 + 1)
          = (M.sig + 1) * (q2.1 + 1) + (M.sig + 1) := by ring
      omega
  refine ⟨Fin.ext hq, Fin.ext ?_⟩
  rw [hq] at hv
  omega

/-- The blank tape symbol (index `M.sig`). -/
def blankSym (M : FlatTM) : Fin (M.sig + 1) := ⟨M.sig, Nat.lt_succ_self _⟩

/-- Clamp a `Nat` into a tape symbol (the blank slot absorbs out-of-range). -/
def symOf (M : FlatTM) (n : Nat) : Fin (M.sig + 1) := ⟨min n M.sig, by omega⟩

/-- Clamp a `Nat` into the head-cell state range. -/
def stateOf (M : FlatTM) (n : Nat) : Fin (M.states + 1) := ⟨min n M.states, by omega⟩

/-- Encode the symbol read under the head (`none` = blank). -/
def optSym (M : FlatTM) : Option Nat → Fin (M.sig + 1)
  | none => blankSym M
  | some v => symOf M v

/-- A "left-context" cell: `none` is the boundary marker, `some a` a tape
cell. Card families that admit the boundary marker in a slot range over this. -/
def xCell (M : FlatTM) : Option (Fin (M.sig + 1)) → Fin (Sg M)
  | none => bCell M
  | some a => tCell M a

/-- All left-context choices. -/
def xOpts (M : FlatTM) : List (Option (Fin (M.sig + 1))) :=
  none :: (List.finRange (M.sig + 1)).map some

/-- Is this left-context choice the *blank* tape cell? A blank left neighbour
means the head is strictly beyond the tape frontier (under the run invariant
"in-range symbols `< M.sig`"), where `some`-writes are void. -/
def xIsBlank (M : FlatTM) (x : Option (Fin (M.sig + 1))) : Bool :=
  decide (x = some (blankSym M))

/-! ## Transition-table normalisation -/

/-- Same `(src_state, src_tape_vals)` key — `stepFlatTM`'s `find?` matches on
exactly these two fields, so two same-key entries shadow each other. -/
def sameKey (e1 e2 : FlatTMTransEntry) : Bool :=
  decide (e1.src_state = e2.src_state) && decide (e1.src_tape_vals = e2.src_tape_vals)

private def dedupGo (seen : List FlatTMTransEntry) :
    List FlatTMTransEntry → List FlatTMTransEntry
  | [] => []
  | e :: es =>
      if seen.any (fun p => sameKey p e) then dedupGo seen es
      else e :: dedupGo (e :: seen) es

/-- Keep the first entry per key (preserves `find?` for every config). -/
def dedupKeys (l : List FlatTMTransEntry) : List FlatTMTransEntry := dedupGo [] l

/-- An entry the single-tape run can actually fire: single-tape shape and a
non-halting source. (A matching entry with malformed `dst` lists makes
`applyTransitionEntry` return `none` — the run is stuck, same as no entry;
an entry out of a halting state never fires because `runFlatTM` checks
halting first. Dropping both after deduplication preserves the step
function on the run — `stepFlatTM_normM`.) -/
def entryOK (M : FlatTM) (e : FlatTMTransEntry) : Bool :=
  decide (e.src_tape_vals.length = 1) &&
  decide (e.dst_write_vals.length = 1) &&
  decide (e.move_dirs.length = 1) &&
  ! (M.halt.getD e.src_state false)

/-- The normalised transition table the cards are generated from:
key-unique, single-tape-shaped, non-halting sources. -/
def normTrans (M : FlatTM) : List FlatTMTransEntry :=
  (dedupKeys M.trans).filter (entryOK M)

/-- `M` with the normalised table. -/
def normM (M : FlatTM) : FlatTM := { M with trans := normTrans M }

/-- `entryMatchesConfig` depends only on the entry's key. -/
private theorem matches_congr_of_sameKey {e1 e2 : FlatTMTransEntry} (cfg : FlatTMConfig)
    (h : sameKey e1 e2 = true) :
    entryMatchesConfig e1 cfg = entryMatchesConfig e2 cfg := by
  simp only [sameKey, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [entryMatchesConfig, h.1, h.2]

/-- Two entries matching the same configuration share a key. -/
private theorem sameKey_of_matches {e1 e2 : FlatTMTransEntry} {cfg : FlatTMConfig}
    (h1 : entryMatchesConfig e1 cfg = true) (h2 : entryMatchesConfig e2 cfg = true) :
    sameKey e1 e2 = true := by
  simp only [entryMatchesConfig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 h2
  simp only [sameKey, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩

/-- Once a matcher is in `seen`, the dedup output contains no matcher at all. -/
private theorem dedupGo_no_match (cfg : FlatTMConfig) {p : FlatTMTransEntry}
    (hp : entryMatchesConfig p cfg = true) :
    ∀ (l seen : List FlatTMTransEntry), p ∈ seen →
      ∀ e' ∈ dedupGo seen l, entryMatchesConfig e' cfg = false := by
  intro l
  induction l with
  | nil => intro seen _ e' he'; simp [dedupGo] at he'
  | cons e es ih =>
    intro seen hpseen e' he'
    simp only [dedupGo] at he'
    by_cases hany : seen.any (fun q => sameKey q e) = true
    · rw [if_pos hany] at he'
      exact ih seen hpseen e' he'
    · rw [if_neg hany] at he'
      rcases List.mem_cons.1 he' with rfl | he'
      · by_contra hcontra
        rw [Bool.not_eq_false] at hcontra
        exact hany (List.any_eq_true.2 ⟨p, hpseen, sameKey_of_matches hp hcontra⟩)
      · exact ih (e :: seen) (List.mem_cons_of_mem _ hpseen) e' he'

/-- The combined dedup+filter `find?` characterisation: the normalised table's
first matcher is `M.trans`'s first matcher when the latter passes `entryOK`,
and nothing otherwise (dedup keeps at most one entry per key, so a filtered-out
first matcher is not shadowed by a later same-key entry). -/
private theorem dedupGo_filter_find? (M : FlatTM) (cfg : FlatTMConfig) :
    ∀ (l seen : List FlatTMTransEntry),
      (∀ p ∈ seen, entryMatchesConfig p cfg = false) →
      ((dedupGo seen l).filter (entryOK M)).find? (fun e => entryMatchesConfig e cfg)
        = (l.find? (fun e => entryMatchesConfig e cfg)).bind
            (fun e => if entryOK M e then some e else none) := by
  intro l
  induction l with
  | nil => intro seen _; simp [dedupGo]
  | cons e es ih =>
    intro seen hseen
    simp only [dedupGo]
    by_cases hany : seen.any (fun q => sameKey q e) = true
    · rw [if_pos hany]
      have hPe : entryMatchesConfig e cfg = false := by
        obtain ⟨p, hpseen, hpk⟩ := List.any_eq_true.1 hany
        rw [← matches_congr_of_sameKey cfg hpk]
        exact hseen p hpseen
      rw [List.find?_cons_of_neg (by simp [hPe]), ih seen hseen]
    · rw [if_neg hany]
      by_cases hq : entryOK M e = true
      · rw [List.filter_cons_of_pos hq]
        by_cases hPe : entryMatchesConfig e cfg = true
        · rw [List.find?_cons_of_pos (p := fun e => entryMatchesConfig e cfg) hPe,
            List.find?_cons_of_pos (p := fun e => entryMatchesConfig e cfg) hPe]
          simp [hq]
        · rw [List.find?_cons_of_neg (by simp [hPe]),
            List.find?_cons_of_neg (by simp [hPe])]
          exact ih (e :: seen) (by
            intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            · exact Bool.not_eq_true _ ▸ hPe  -- entryMatchesConfig e cfg = false
            · exact hseen p hp)
      · rw [List.filter_cons_of_neg hq]
        by_cases hPe : entryMatchesConfig e cfg = true
        · rw [List.find?_cons_of_pos (p := fun e => entryMatchesConfig e cfg) hPe]
          simp only [Option.bind_some, if_neg hq]
          rw [List.find?_eq_none]
          intro e' he'
          have he'' := (List.mem_filter.1 he').1
          simp [dedupGo_no_match cfg hPe es (e :: seen) (List.mem_cons_self) e' he'']
        · rw [List.find?_cons_of_neg (by simp [hPe])]
          exact ih (e :: seen) (by
            intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            · exact Bool.not_eq_true _ ▸ hPe
            · exact hseen p hp)

/-- **Normalisation is step-invisible on the run** (S1 direction 0).
For a single-tape, *non-halting* configuration the normalised machine steps
exactly like `M`: dedup keeps the first entry per key (which is what `find?`
returns), a first-per-key entry with malformed `dst` shape yields `none` on
both sides (`applyTransitionEntry` guard vs. no entry), and halting-source
entries are unreachable here by `hnh`. -/
theorem stepFlatTM_normM (M : FlatTM) (cfg : FlatTMConfig)
    (h1 : cfg.tapes.length = 1)
    (hnh : haltingStateReached M cfg = false) :
    stepFlatTM (normM M) cfg = stepFlatTM M cfg := by
  show ((normM M).trans.find? (fun e => entryMatchesConfig e cfg)).bind
      (applyTransitionEntry cfg)
    = (M.trans.find? (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg)
  have hnorm : (normM M).trans = (dedupGo [] M.trans).filter (entryOK M) := rfl
  rw [hnorm, dedupGo_filter_find? M cfg M.trans [] (by intro p hp; cases hp)]
  cases hfind : M.trans.find? (fun e => entryMatchesConfig e cfg) with
  | none => rfl
  | some e =>
    by_cases hq : entryOK M e = true
    · simp [hq]
    · simp only [Option.bind_some, if_neg hq, Option.bind_none]
      -- the found entry is malformed: `applyTransitionEntry` is `none` too
      have hPe := List.find?_some hfind
      simp only [entryMatchesConfig, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hPe
      have hsrcLen : e.src_tape_vals.length = 1 := by
        rw [hPe.2, List.length_map, h1]
      have hhaltbit : (M.halt.getD e.src_state false) = false := by
        rw [hPe.1]; exact hnh
      have hOK : ¬(e.dst_write_vals.length = 1 ∧ e.move_dirs.length = 1) := by
        intro ⟨hd1, hm1⟩
        apply hq
        simp [entryOK, hsrcLen, hd1, hm1, -List.getD_eq_getElem?_getD, hhaltbit]
      symm
      unfold applyTransitionEntry
      rw [dif_neg]
      rw [h1]
      intro ⟨ha, hb⟩
      exact hOK ⟨ha.symm, hb.symm⟩

/-! ## Rows -/

/-- Row width: boundary marker + `|s| + steps + 3` tape positions + the
**right** boundary marker (so the head — which starts at tape position 0 and
advances at most one per step — always has a full 3-window around it, and
the written region always has a blank cell after it inside the row). The
right marker guards the row's LAST cell: it is the 2026-07-18-c fix for the
machine-checked **phantom-head defect** — without it, `stepCardInL` (whose
premise cannot see the head arriving from outside the window) could
materialise a spurious head at the last cell, the only cell not contained
in a second, refuting window (`probes/S1TableauProbe.lean` §5). -/
def rowWidth (s : List Nat) (steps : Nat) : Nat := s.length + steps + 5

/-- Single-tape head projection (the model's `left` component is vestigial —
see `Compile.flattenTape`). -/
def cfgHead (cfg : FlatTMConfig) : Nat := (cfg.tapes.headD ([], 0, [])).2.1

/-- Single-tape content projection. -/
def cfgRight (cfg : FlatTMConfig) : List Nat := (cfg.tapes.headD ([], 0, [])).2.2

/-- The tableau symbol of tape position `p`: the written symbol in range, the
blank at/beyond the frontier. -/
def tapeSymAt (M : FlatTM) (right : List Nat) (p : Nat) : Fin (M.sig + 1) :=
  if p < right.length then symOf M (right.getD p 0) else blankSym M

/-- The row representation agrees with the machine's read at the head. -/
theorem tapeSymAt_head (M : FlatTM) (l r : List Nat) (h : Nat) :
    tapeSymAt M r h = optSym M (currentTapeSymbol (l, h, r)) := by
  unfold tapeSymAt currentTapeSymbol
  by_cases hlt : h < r.length
  · rw [if_pos hlt, dif_pos hlt]
    show symOf M (r.getD h 0) = optSym M (some (r.get ⟨h, hlt⟩))
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rfl
  · rw [if_neg hlt, dif_neg hlt]
    rfl

/-- The cell at tape position `p` of a configuration `(q, hd, right)`. -/
def confCell (M : FlatTM) (q hd : Nat) (right : List Nat) (p : Nat) : Fin (Sg M) :=
  if p = hd then hCell M (stateOf M q) (tapeSymAt M right p)
  else tCell M (tapeSymAt M right p)

/-- The tableau row of a configuration: the boundary marker, `n`
tape-position cells, and the **right** boundary marker (which guards the
last cell against phantom incoming heads — see `rowWidth`). -/
def confRow (M : FlatTM) (cfg : FlatTMConfig) (n : Nat) : List (Fin (Sg M)) :=
  bCell M ::
    (List.range n).map (confCell M cfg.state_idx (cfgHead cfg) (cfgRight cfg))
    ++ [bCell M]

theorem confRow_length (M : FlatTM) (cfg : FlatTMConfig) (n : Nat) :
    (confRow M cfg n).length = n + 2 := by
  simp [confRow]

/-- The initial tableau row: the start configuration on tape `s`. -/
def cookInit (M : FlatTM) (s : List Nat) (steps : Nat) : List (Fin (Sg M)) :=
  confRow M (initFlatConfig M [s]) (s.length + steps + 3)

/-- Final patterns: a halting state appearing anywhere as a head cell. -/
def cookFinal (M : FlatTM) : List (List (Fin (Sg M))) :=
  (List.finRange (M.states + 1)).flatMap (fun q =>
    if M.halt.getD q.1 false then
      (List.finRange (M.sig + 1)).map (fun b => [hCell M q b])
    else [])

/-! ## Cards (local 3-cell windows)

Window position conventions (head at row coordinate `h` = tape position + 1):
the *center* window is `drop (h-1)` (cells `h-1, h, h+1`), the *left-of*
window `drop h`, the *right-of* window `drop (h-2)`. The center window always
exists and carries the truth (its premise sees the left neighbour, hence the
frontier); edge windows carry all context-consistent variants and are pinned
by overlap with the center window's conclusion. -/

/-- A pure-copy card licensing an unchanged 3-window. -/
def copyCard (M : FlatTM) (x y z : Fin (Sg M)) : TCCCard (Fin (Sg M)) :=
  { prem := ⟨x, y, z⟩, conc := ⟨x, y, z⟩ }

/-- Identity away from the head: every 3-window of tape cells, with the
boundary marker admitted on the left slot. `Θ(|Σ|³)`. -/
def copyCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  (xOpts M).flatMap (fun x =>
    (List.finRange (M.sig + 1)).flatMap (fun b =>
      (List.finRange (M.sig + 1)).map (fun c =>
        copyCard M (xCell M x) (tCell M b) (tCell M c))))

/-- Identity at the row's rightmost window `(y, z, right-marker)`. This is
the ONLY family with the boundary marker in the third slot, and its
conclusion keeps all three cells — so the last cell of a row can never
change and never host an (incoming) head. Deliberately tape-only in the
first two slots: the head never reaches the right marker's window
(`cfgHead + 3 ≤ n`), so no head/marker variants are needed, and their
absence is what refutes phantom heads at the last cell in the (1b)
inversion. -/
def copyRightCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  (List.finRange (M.sig + 1)).flatMap (fun y =>
    (List.finRange (M.sig + 1)).map (fun z =>
      copyCard M (tCell M y) (tCell M z) (bCell M)))

/-- Halt freeze, head at the window's first cell. -/
def haltLeftCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  (List.finRange (M.states + 1)).flatMap (fun q =>
    if M.halt.getD q.1 false then
      (List.finRange (M.sig + 1)).flatMap (fun b =>
        (List.finRange (M.sig + 1)).flatMap (fun y =>
          (List.finRange (M.sig + 1)).map (fun z =>
            copyCard M (hCell M q b) (tCell M y) (tCell M z))))
    else [])

/-- Halt freeze, head at the window's center. -/
def haltCenterCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  (List.finRange (M.states + 1)).flatMap (fun q =>
    if M.halt.getD q.1 false then
      (List.finRange (M.sig + 1)).flatMap (fun b =>
        (xOpts M).flatMap (fun x =>
          (List.finRange (M.sig + 1)).map (fun z =>
            copyCard M (xCell M x) (hCell M q b) (tCell M z))))
    else [])

/-- Halt freeze, head at the window's third cell. -/
def haltRightCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  (List.finRange (M.states + 1)).flatMap (fun q =>
    if M.halt.getD q.1 false then
      (List.finRange (M.sig + 1)).flatMap (fun b =>
        (xOpts M).flatMap (fun x =>
          (List.finRange (M.sig + 1)).map (fun y =>
            copyCard M (xCell M x) (tCell M y) (hCell M q b))))
    else [])

/-- **The effective written symbol.** `m`/`w` are the entry's read/write
options; `xb` says whether the head's left neighbour is the blank cell —
under the run invariant that means the head is *strictly beyond* the
frontier, where `some`-writes are void (`writeCurrentTapeSymbol`). A
`none`-write keeps the read symbol. -/
def wEff (M : FlatTM) (m w : Option Nat) (xb : Bool) : Fin (M.sig + 1) :=
  match w with
  | none => optSym M m
  | some u => if m = none && xb then blankSym M else symOf M u

/-- Transition card, head at the window center. The premise sees the left
neighbour, so the conclusion computes the real write effect (`wEff`) and the
`Lmove` clamp at tape position 0 (left neighbour = boundary marker). -/
def stepCardCenter (M : FlatTM) (q q' : Fin (M.states + 1)) (m w : Option Nat)
    (mv : TMMove) (x : Option (Fin (M.sig + 1))) (z : Fin (M.sig + 1)) :
    TCCCard (Fin (Sg M)) :=
  let R := optSym M m
  let W := wEff M m w (xIsBlank M x)
  { prem := ⟨xCell M x, hCell M q R, tCell M z⟩,
    conc :=
      match mv, x with
      | TMMove.Nmove, _ => ⟨xCell M x, hCell M q' W, tCell M z⟩
      | TMMove.Rmove, _ => ⟨xCell M x, tCell M W, hCell M q' z⟩
      | TMMove.Lmove, none => ⟨bCell M, hCell M q' W, tCell M z⟩
      | TMMove.Lmove, some a => ⟨hCell M q' a, tCell M W, tCell M z⟩ }

/-- Transition cards, head at the window's first cell. The left context is
invisible, so both frontier variants (`xb`) are emitted, and `Lmove` emits
both the leave variant (head exits left, tape position > 0) and the clamp
variant (position 0); overlap with the center window selects the right one. -/
def stepCardsLeft (M : FlatTM) (q q' : Fin (M.states + 1)) (m w : Option Nat)
    (mv : TMMove) (xb : Bool) (y z : Fin (M.sig + 1)) :
    List (TCCCard (Fin (Sg M))) :=
  let R := optSym M m
  let W := wEff M m w xb
  match mv with
  | TMMove.Nmove =>
      [{ prem := ⟨hCell M q R, tCell M y, tCell M z⟩,
         conc := ⟨hCell M q' W, tCell M y, tCell M z⟩ }]
  | TMMove.Rmove =>
      [{ prem := ⟨hCell M q R, tCell M y, tCell M z⟩,
         conc := ⟨tCell M W, hCell M q' y, tCell M z⟩ }]
  | TMMove.Lmove =>
      [{ prem := ⟨hCell M q R, tCell M y, tCell M z⟩,
         conc := ⟨tCell M W, tCell M y, tCell M z⟩ },
       { prem := ⟨hCell M q R, tCell M y, tCell M z⟩,
         conc := ⟨hCell M q' W, tCell M y, tCell M z⟩ }]

/-- Transition card, head at the window's third cell (the left neighbour `y`
is visible, so the write effect is exact). -/
def stepCardRight (M : FlatTM) (q q' : Fin (M.states + 1)) (m w : Option Nat)
    (mv : TMMove) (x : Option (Fin (M.sig + 1))) (y : Fin (M.sig + 1)) :
    TCCCard (Fin (Sg M)) :=
  let R := optSym M m
  let W := wEff M m w (decide (y = blankSym M))
  match mv with
  | TMMove.Nmove =>
      { prem := ⟨xCell M x, tCell M y, hCell M q R⟩,
        conc := ⟨xCell M x, tCell M y, hCell M q' W⟩ }
  | TMMove.Rmove =>
      { prem := ⟨xCell M x, tCell M y, hCell M q R⟩,
        conc := ⟨xCell M x, tCell M y, tCell M W⟩ }
  | TMMove.Lmove =>
      { prem := ⟨xCell M x, tCell M y, hCell M q R⟩,
        conc := ⟨xCell M x, hCell M q' y, tCell M W⟩ }

/-- Incoming-head card for `Rmove`: the head enters this window's *first*
cell from the left. This is the only all-tape-premise family with a head in
its conclusion's first slot; there is deliberately **no** family with the
head in the conclusion's *second* slot off an all-tape premise — the head
can only move to a cell from an adjacent cell, and all three source
positions for a "head at second cell" conclusion lie inside the window, so
the premise would contain the head. That absence blocks spurious heads. -/
def stepCardInR (M : FlatTM) (q' : Fin (M.states + 1)) (y z u : Fin (M.sig + 1)) :
    TCCCard (Fin (Sg M)) :=
  { prem := ⟨tCell M y, tCell M z, tCell M u⟩,
    conc := ⟨hCell M q' y, tCell M z, tCell M u⟩ }

/-- Incoming-head card for `Lmove`: the head enters this window's *third*
cell from the right. -/
def stepCardInL (M : FlatTM) (q' : Fin (M.states + 1)) (x : Option (Fin (M.sig + 1)))
    (y c : Fin (M.sig + 1)) : TCCCard (Fin (Sg M)) :=
  { prem := ⟨xCell M x, tCell M y, tCell M c⟩,
    conc := ⟨xCell M x, tCell M y, hCell M q' c⟩ }

/-- All cards of one (normalised) transition entry. -/
def stepCardsOf (M : FlatTM) (e : FlatTMTransEntry) : List (TCCCard (Fin (Sg M))) :=
  let q := stateOf M e.src_state
  let q' := stateOf M e.dst_state
  let m := e.src_tape_vals.headD none
  let w := e.dst_write_vals.headD none
  let mv := e.move_dirs.headD TMMove.Nmove
  ((xOpts M).flatMap (fun x =>
    (List.finRange (M.sig + 1)).map (fun z => stepCardCenter M q q' m w mv x z))) ++
  ([false, true].flatMap (fun xb =>
    (List.finRange (M.sig + 1)).flatMap (fun y =>
      (List.finRange (M.sig + 1)).flatMap (fun z =>
        stepCardsLeft M q q' m w mv xb y z)))) ++
  ((xOpts M).flatMap (fun x =>
    (List.finRange (M.sig + 1)).map (fun y => stepCardRight M q q' m w mv x y))) ++
  (match mv with
   | TMMove.Rmove =>
       (List.finRange (M.sig + 1)).flatMap (fun y =>
         (List.finRange (M.sig + 1)).flatMap (fun z =>
           (List.finRange (M.sig + 1)).map (fun u => stepCardInR M q' y z u)))
   | TMMove.Lmove =>
       (xOpts M).flatMap (fun x =>
         (List.finRange (M.sig + 1)).flatMap (fun y =>
           (List.finRange (M.sig + 1)).map (fun c => stepCardInL M q' x y c)))
   | TMMove.Nmove => [])

/-- Transition cards, generated from the normalised table. -/
def stepCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  (normTrans M).flatMap (stepCardsOf M)

/-- All cards. -/
def cookCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  copyCards M ++ copyRightCards M ++ haltLeftCards M ++ haltCenterCards M ++
    haltRightCards M ++ stepCards M

/-! ## The construction -/

/-- The Cook tableau as a typed `TCC` instance. -/
def cookTableauTyped (M : FlatTM) (s : List Nat) (steps : Nat) : TCC where
  Sigma := Sg M
  init := cookInit M s steps
  cards := cookCards M
  final := cookFinal M
  steps := steps

/-- **The Cook 2D tableau as a `FlatTCC` instance.** A genuine, computable
function of `(M, s, steps)`: no `if` on the source predicate's truth. -/
def cookTableau (M : FlatTM) (s : List Nat) (steps : Nat) : FlatTCC :=
  FlatTCC.flattenTCC (cookTableauTyped M s steps)

/-! ## Well-formedness (PROVEN) -/

theorem cookInit_length (M : FlatTM) (s : List Nat) (steps : Nat) :
    (cookInit M s steps).length = rowWidth s steps := by
  unfold cookInit rowWidth
  rw [confRow_length]

theorem cookTableauTyped_wellformed (M : FlatTM) (s : List Nat) (steps : Nat) :
    TCC.wellformed (cookTableauTyped M s steps) := by
  unfold TCC.wellformed cookTableauTyped
  rw [cookInit_length]
  unfold rowWidth
  omega

/-- The tableau is a well-formed, validly-flattened `FlatTCC` instance. -/
theorem cookTableau_wellformed (M : FlatTM) (s : List Nat) (steps : Nat)
    (_hValid : validFlatTM M) :
    FlatTCC.FlatTCC_wellformed (cookTableau M s steps) ∧
    FlatTCC.isValidFlattening (cookTableau M s steps) := by
  refine ⟨?_, ?_⟩
  · exact FlatTCC.flattenTCC_wellformed (cookTableauTyped_wellformed M s steps)
  · exact FlatTCC.isValidFlattening_flattenTCC _

/-! ## Size bound (documented gap)

The card list dominates: `copyCards` is `Θ(|Σ|³)` cards of encoded size
`Θ(|Σ|)` each (`Θ(|Σ|⁴)` total), and each normalised entry contributes
`Θ(|Σ|³)` incoming-head cards (`Θ(|trans|·|Σ|⁴)` total). With
`|Σ| = (M.sig+1)(M.states+2)+1 ≤ n²` for
`n := s.length + steps + M.sig + M.states + M.trans.length + 2`, the total is
`O(n⁹)`; the degree-10 bound below has generous headroom. Still polynomial —
that is all `⪯p'` needs. Proving it is `~150–300` LOC of
foldl-over-`flatMap` `encodable.size` arithmetic (a clean bottom-up bite,
no design risk). -/
theorem cookTableau_size_bound (M : FlatTM) (s : List Nat) (steps : Nat) :
    encodable.size (cookTableau M s steps) ≤
      (s.length + steps + M.sig + M.states + M.trans.length + 2) ^ 10 := by
  sorry  -- mechanical foldl-over-flatMap size sum; see the note above.

/-! ## Correctness — the decomposed skeleton (S1)

The headline `cookTableau_correct` is **assembled below (PROVEN)** from the
following sorried sub-obligations:

* direction 0 — `stepFlatTM_normM` (normalisation agreement, above);
* direction 1a — `validStep_of_step` + `validStep_of_halt`
  (machine step / halt freeze ⟹ card-covered row transition);
* direction 1b — `step_of_validStep` (card-covered transition out of a
  configuration row ⟹ *the* machine step — the inversion heart);
* direction 2 — `cover_of_run` (accepting run ⟹ covering, by trajectory
  induction + halt-freeze padding to the exact budget);
* direction 3 — `run_of_cover` (covering ⟹ accepting run, by extraction);
* the `satFinal` bridge lemmas.

The run invariant `ConfFits` threads the facts every direction needs. -/

/-- The run invariant after `t` steps from `initFlatConfig M [s]`
(`base = s.length`): single-tape shape with a vestigial `left`, in-range
state, head at most `t`, content grown at most one cell per step, symbols
in the machine alphabet. -/
structure ConfFits (M : FlatTM) (base t : Nat) (cfg : FlatTMConfig) : Prop where
  tapes_eq : cfg.tapes = [([], cfgHead cfg, cfgRight cfg)]
  state_lt : cfg.state_idx < M.states
  head_le : cfgHead cfg ≤ t
  len_le : (cfgRight cfg).length ≤ base + t
  syms_lt : ∀ x ∈ cfgRight cfg, x < M.sig

theorem ConfFits_init (M : FlatTM) (s : List Nat)
    (hV : validFlatTM M) (hs : list_ofFlatType M.sig s) :
    ConfFits M s.length 0 (initFlatConfig M [s]) := by
  refine ⟨rfl, hV.1, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro x hx
  exact hs x hx

/-- `ConfFits` is monotone in the step counter (the bounds only loosen). -/
theorem ConfFits_mono (M : FlatTM) {base t t' : Nat} {cfg : FlatTMConfig}
    (htt : t ≤ t') (hfit : ConfFits M base t cfg) : ConfFits M base t' cfg :=
  ⟨hfit.tapes_eq, hfit.state_lt, Nat.le_trans hfit.head_le htt,
    Nat.le_trans hfit.len_le (by omega), hfit.syms_lt⟩

/-- Unfolded description of a successful machine step out of a single-tape
configuration: the fired entry (with its match and single-tape payload) and
the successor's explicit shape. -/
private theorem step_desc (M : FlatTM) {cfg cfg' : FlatTMConfig}
    (htapes : cfg.tapes = [([], cfgHead cfg, cfgRight cfg)])
    (hstep : stepFlatTM M cfg = some cfg') :
    ∃ e ∈ M.trans,
      entryMatchesConfig e cfg = true ∧
      e.src_state = cfg.state_idx ∧
      e.src_tape_vals = [currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)] ∧
      ∃ w mv, e.dst_write_vals = [w] ∧ e.move_dirs = [mv] ∧
        cfg' = ⟨e.dst_state, [tapeStep ([], cfgHead cfg, cfgRight cfg) w mv]⟩ := by
  have hstep' : (M.trans.find? (fun e => entryMatchesConfig e cfg)).bind
      (applyTransitionEntry cfg) = some cfg' := hstep
  cases hfind : M.trans.find? (fun e => entryMatchesConfig e cfg) with
  | none => rw [hfind] at hstep'; simp at hstep'
  | some e =>
    rw [hfind] at hstep'
    have happ : applyTransitionEntry cfg e = some cfg' := hstep'
    have hP := List.find?_some hfind
    have hPs := hP
    simp only [entryMatchesConfig, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hPs
    have h1 : cfg.tapes.length = 1 := by rw [htapes]; rfl
    unfold applyTransitionEntry at happ
    by_cases hlen : cfg.tapes.length = e.dst_write_vals.length ∧
        cfg.tapes.length = e.move_dirs.length
    · rw [dif_pos hlen] at happ
      obtain ⟨w, hw⟩ := List.length_eq_one_iff.1 (h1 ▸ hlen.1).symm
      obtain ⟨mv, hmv⟩ := List.length_eq_one_iff.1 (h1 ▸ hlen.2).symm
      refine ⟨e, List.mem_of_find?_eq_some hfind, hP, hPs.1, ?_, w, mv, hw, hmv, ?_⟩
      · rw [hPs.2, htapes]; rfl
      · rw [← Option.some_inj, ← happ]
        rw [htapes, hw, hmv]
        rfl
    · rw [dif_neg hlen] at happ
      simp at happ

/-- The write effect on the single-tape content, packaged: head and (empty)
left component preserved, length grows by at most one, symbols stay in the
machine alphabet, cells away from the head unchanged, and the head cell's
tableau symbol is exactly `wEff` at the strictly-beyond-frontier flag. -/
private theorem write_facts (M : FlatTM) (hd : Nat) (right : List Nat) (w : Option Nat)
    (hsig : ∀ x ∈ right, x < M.sig)
    (hw : match w with | none => True | some v => v < M.sig) :
    ∃ wr : List Nat,
      writeCurrentTapeSymbol ([], hd, right) w = ([], hd, wr) ∧
      right.length ≤ wr.length ∧ wr.length ≤ right.length + 1 ∧
      (∀ x ∈ wr, x < M.sig) ∧
      (∀ p, p ≠ hd → tapeSymAt M wr p = tapeSymAt M right p) ∧
      tapeSymAt M wr hd
        = wEff M (currentTapeSymbol ([], hd, right)) w (decide (right.length < hd)) := by
  cases w with
  | none =>
    refine ⟨right, rfl, Nat.le_refl _, by omega, hsig, fun _ _ => rfl, ?_⟩
    show tapeSymAt M right hd = optSym M (currentTapeSymbol ([], hd, right))
    exact tapeSymAt_head M [] right hd
  | some u =>
    have hu : u < M.sig := hw
    by_cases h1 : hd < right.length
    · -- in-range write: one cell replaced
      refine ⟨right.set hd u, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [writeCurrentTapeSymbol]
        rw [dif_pos h1, List.set_eq_take_append_cons_drop, if_pos h1]
      · rw [List.length_set]
      · rw [List.length_set]; omega
      · intro x hx
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact hsig x hx
        · exact hu
      · intro p hp
        unfold tapeSymAt
        rw [List.length_set]
        by_cases h2 : p < right.length
        · rw [if_pos h2, if_pos h2]
          congr 1
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_set_ne (Ne.symm hp)]
        · rw [if_neg h2, if_neg h2]
      · unfold tapeSymAt
        rw [List.length_set, if_pos h1]
        have hget : (right.set hd u).getD hd 0 = u := by
          simp [List.getD_eq_getElem?_getD, h1]
        rw [hget]
        unfold wEff currentTapeSymbol
        rw [dif_pos h1]
        simp
    · by_cases h2 : hd = right.length
      · -- frontier write: one cell appended
        refine ⟨right ++ [u], ?_, by simp, by simp, ?_, ?_, ?_⟩
        · simp only [writeCurrentTapeSymbol]
          rw [dif_neg h1, if_pos h2]
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hsig x hx
          · rw [List.mem_singleton.1 hx]; exact hu
        · intro p hp
          unfold tapeSymAt
          rw [List.length_append]
          by_cases h3 : p < right.length
          · rw [if_pos (by simp; omega), if_pos h3]
            congr 1
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_left h3]
          · rw [if_neg (by simp; omega), if_neg h3]
        · unfold tapeSymAt
          rw [List.length_append, if_pos (by simp; omega)]
          have hget : (right ++ [u]).getD hd 0 = u := by
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by omega), h2]
            simp
          rw [hget]
          unfold wEff currentTapeSymbol
          rw [dif_neg h1]
          have hxb : decide (right.length < hd) = false := by
            simp; omega
          rw [hxb]
          simp
      · -- strictly beyond the frontier: the write is VOID
        refine ⟨right, ?_, Nat.le_refl _, by omega, hsig, fun _ _ => rfl, ?_⟩
        · simp only [writeCurrentTapeSymbol]
          rw [dif_neg h1, if_neg h2]
        · unfold tapeSymAt
          rw [if_neg h1]
          unfold wEff currentTapeSymbol
          rw [dif_neg h1]
          have hxb : decide (right.length < hd) = true := by
            simp; omega
          rw [hxb]
          simp

/-- **Invariant preservation** (S1). The write keeps or appends one cell
(`write_facts`), the move changes the head by at most one, the written symbol
is bounded by `validFlatTM`'s `flatTMOptionSymbolsBounded`, the new state by
the entry's `dst_state` bound. -/
theorem ConfFits_step (M : FlatTM) {base t : Nat} {cfg cfg' : FlatTMConfig}
    (hV : validFlatTM M) (hfit : ConfFits M base t cfg)
    (hstep : stepFlatTM M cfg = some cfg') :
    ConfFits M base (t + 1) cfg' := by
  obtain ⟨e, heMem, hmatch, hsrc, hvals, w, mv, hw, hmv, hcfg'⟩ :=
    step_desc M hfit.tapes_eq hstep
  have hvalid := hV.2.2 e heMem
  have hwmem : w ∈ e.dst_write_vals := by
    rw [hw]; exact List.mem_singleton.2 rfl
  have hwbound := hvalid.2.2.2.2.2.2 w hwmem
  obtain ⟨wr, hwt, hlen1, hlen2, hsyms, hunch, hwrhd⟩ :=
    write_facts M (cfgHead cfg) (cfgRight cfg) w hfit.syms_lt hwbound
  obtain ⟨hd', hmv', hbnd⟩ : ∃ hd',
      moveTapeHead ([], cfgHead cfg, wr) mv = ([], hd', wr) ∧
      hd' ≤ cfgHead cfg + 1 := by
    cases mv
    · exact ⟨cfgHead cfg - 1, rfl, by omega⟩
    · exact ⟨cfgHead cfg + 1, rfl, by omega⟩
    · exact ⟨cfgHead cfg, rfl, by omega⟩
  have htape : tapeStep ([], cfgHead cfg, cfgRight cfg) w mv = ([], hd', wr) := by
    unfold tapeStep
    rw [hwt, hmv']
  subst hcfg'
  rw [htape]
  have hh := hfit.head_le
  have hl := hfit.len_le
  refine ⟨rfl, hvalid.2.1, ?_, ?_, hsyms⟩
  · show hd' ≤ t + 1
    omega
  · show wr.length ≤ base + (t + 1)
    omega

/-! ### Window machinery (shared by directions 1a/1a′ and, later, 1b)

Rows are addressed by *coordinates* (`0` = boundary marker, coordinate
`j ≥ 1` = tape position `j - 1`); the head of `cfg` sits at coordinate
`cfgHead cfg + 1`. `rowCell`/`rowX` compute a coordinate's cell, and
`confRow_window` exposes a 3-window as its three cells, so every covering
obligation reduces to three cell equations plus a card-membership fact. -/

private theorem dedupGo_subset :
    ∀ (l seen : List FlatTMTransEntry), ∀ e ∈ dedupGo seen l, e ∈ l := by
  intro l
  induction l with
  | nil => intro seen e he; simp [dedupGo] at he
  | cons a as ih =>
    intro seen e he
    simp only [dedupGo] at he
    by_cases hany : seen.any (fun q => sameKey q a) = true
    · rw [if_pos hany] at he
      exact List.mem_cons_of_mem _ (ih seen e he)
    · rw [if_neg hany] at he
      rcases List.mem_cons.1 he with rfl | he
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (a :: seen) e he)

theorem normTrans_subset (M : FlatTM) : ∀ e ∈ normTrans M, e ∈ M.trans := by
  intro e he
  exact dedupGo_subset M.trans [] e (List.mem_filter.1 he).1

/-- The first three cells of `l.drop i`, by `getElem`. -/
theorem take3_drop {α : Type*} (l : List α) (i : Nat) (h : i + 3 ≤ l.length) :
    (l.drop i).take 3
      = [l[i]'(by omega), l[i + 1]'(by omega), l[i + 2]'(by omega)] := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  rfl

/-- Covering a window is three cell equations on each side. -/
theorem coversHead_take3 {k : Nat} (card : TCCCard (Fin k))
    (a b : List (Fin k)) (i : Nat)
    (hp : (a.drop i).take 3 = (card.prem : List (Fin k)))
    (hc : (b.drop i).take 3 = (card.conc : List (Fin k))) :
    TCC.coversHead card (a.drop i) (b.drop i) :=
  ⟨⟨(a.drop i).drop 3, by rw [← hp]; exact (List.take_append_drop 3 _).symm⟩,
   ⟨(b.drop i).drop 3, by rw [← hc]; exact (List.take_append_drop 3 _).symm⟩⟩

/-- The cell at row coordinate `j`. -/
def rowCell (M : FlatTM) (cfg : FlatTMConfig) (j : Nat) : Fin (Sg M) :=
  if j = 0 then bCell M
  else confCell M cfg.state_idx (cfgHead cfg) (cfgRight cfg) (j - 1)

/-- The boundary-or-tape ("left context") view of coordinate `j`; the true
cell away from the head. -/
def rowX (M : FlatTM) (cfg : FlatTMConfig) (j : Nat) :
    Option (Fin (M.sig + 1)) :=
  if j = 0 then none else some (tapeSymAt M (cfgRight cfg) (j - 1))

theorem rowCell_zero (M : FlatTM) (cfg : FlatTMConfig) :
    rowCell M cfg 0 = bCell M := by
  unfold rowCell
  rw [if_pos rfl]

theorem rowCell_x (M : FlatTM) (cfg : FlatTMConfig) {j : Nat}
    (hne : j ≠ cfgHead cfg + 1) :
    rowCell M cfg j = xCell M (rowX M cfg j) := by
  unfold rowCell rowX
  by_cases h0 : j = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]
    unfold confCell
    rw [if_neg (show ¬(j - 1 = cfgHead cfg) by omega)]
    rfl

theorem rowCell_head (M : FlatTM) (cfg : FlatTMConfig) {j : Nat}
    (hj : j = cfgHead cfg + 1) :
    rowCell M cfg j
      = hCell M (stateOf M cfg.state_idx)
          (tapeSymAt M (cfgRight cfg) (cfgHead cfg)) := by
  subst hj
  unfold rowCell confCell
  rw [if_neg (by omega), if_pos (by omega)]
  simp

theorem rowCell_tape (M : FlatTM) (cfg : FlatTMConfig) {j : Nat}
    (h1 : 1 ≤ j) (hne : j ≠ cfgHead cfg + 1) :
    rowCell M cfg j = tCell M (tapeSymAt M (cfgRight cfg) (j - 1)) := by
  unfold rowCell confCell
  rw [if_neg (by omega), if_neg (by omega)]

theorem confRow_getElem (M : FlatTM) (cfg : FlatTMConfig) {n j : Nat}
    (hj : j ≤ n) (hlt : j < (confRow M cfg n).length) :
    (confRow M cfg n)[j]'hlt = rowCell M cfg j := by
  have hpre : j < (bCell M :: (List.range n).map
      (confCell M cfg.state_idx (cfgHead cfg) (cfgRight cfg))).length := by
    simp; omega
  show ((bCell M :: (List.range n).map
      (confCell M cfg.state_idx (cfgHead cfg) (cfgRight cfg))) ++ [bCell M])[j]'hlt
    = rowCell M cfg j
  rw [List.getElem_append_left hpre]
  cases j with
  | zero => rfl
  | succ k =>
    have hk : k < n := by omega
    simp [rowCell]

/-- The last cell (coordinate `n + 1`) is the right boundary marker. -/
theorem confRow_getElem_last (M : FlatTM) (cfg : FlatTMConfig) {n : Nat}
    (hlt : n + 1 < (confRow M cfg n).length) :
    (confRow M cfg n)[n + 1]'hlt = bCell M := by
  show ((bCell M :: (List.range n).map
      (confCell M cfg.state_idx (cfgHead cfg) (cfgRight cfg))) ++ [bCell M])[n + 1]'_
    = bCell M
  rw [List.getElem_append_right (by simp)]
  simp

/-- A 3-window of a configuration row, as its three coordinate cells. -/
theorem confRow_window (M : FlatTM) (cfg : FlatTMConfig) {n i : Nat}
    (h : i + 2 ≤ n) :
    ((confRow M cfg n).drop i).take 3
      = [rowCell M cfg i, rowCell M cfg (i + 1), rowCell M cfg (i + 2)] := by
  have hlen : i + 3 ≤ (confRow M cfg n).length := by rw [confRow_length]; omega
  rw [take3_drop _ i hlen,
    confRow_getElem M cfg (j := i) (by omega) (by rw [confRow_length]; omega),
    confRow_getElem M cfg (j := i + 1) (by omega) (by rw [confRow_length]; omega),
    confRow_getElem M cfg (j := i + 2) (by omega) (by rw [confRow_length]; omega)]

/-- The rightmost 3-window (`i + 1 = n`): two coordinate cells and the
right marker. -/
theorem confRow_window_last (M : FlatTM) (cfg : FlatTMConfig) {n i : Nat}
    (h : i + 1 = n) :
    ((confRow M cfg n).drop i).take 3
      = [rowCell M cfg i, rowCell M cfg (i + 1), bCell M] := by
  have hlen : i + 3 ≤ (confRow M cfg n).length := by rw [confRow_length]; omega
  have hcell3 : (confRow M cfg n)[i + 2]'(by rw [confRow_length]; omega)
      = bCell M := by
    have hq : (confRow M cfg n)[i + 2]? = some (bCell M) := by
      rw [show i + 2 = n + 1 from by omega,
        List.getElem?_eq_getElem (by rw [confRow_length]; omega),
        confRow_getElem_last M cfg]
    rw [List.getElem?_eq_getElem (by rw [confRow_length]; omega)] at hq
    exact Option.some.inj hq
  rw [take3_drop _ i hlen,
    confRow_getElem M cfg (j := i) (by omega) (by rw [confRow_length]; omega),
    confRow_getElem M cfg (j := i + 1) (by omega) (by rw [confRow_length]; omega),
    hcell3]

/-- Under the run invariant, a tape cell is the blank iff its position is
at/beyond the frontier — the window-local frontier detection. -/
theorem tapeSymAt_blank_iff (M : FlatTM) (right : List Nat) (p : Nat)
    (hsig : ∀ x ∈ right, x < M.sig) :
    decide (tapeSymAt M right p = blankSym M) = decide (right.length ≤ p) := by
  unfold tapeSymAt
  by_cases h : p < right.length
  · rw [if_pos h]
    have hmem : right.getD p 0 ∈ right := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      exact List.getElem_mem h
    have hval := hsig _ hmem
    have hne : symOf M (right.getD p 0) ≠ blankSym M := by
      intro hEq
      have hv := congrArg Fin.val hEq
      simp only [symOf, blankSym] at hv
      omega
    rw [decide_eq_false hne, decide_eq_false (show ¬right.length ≤ p by omega)]
  · rw [if_neg h]
    simp [show right.length ≤ p from by omega]

theorem xIsBlank_some (M : FlatTM) (a : Fin (M.sig + 1)) :
    xIsBlank M (some a) = decide (a = blankSym M) := by
  simp [xIsBlank]

/-- The head's left-context cell is blank iff the head is strictly beyond
the frontier (`wEff`'s `xb` flag is truthful on configuration rows). -/
theorem rowX_isBlank (M : FlatTM) (cfg : FlatTMConfig)
    (hsig : ∀ x ∈ cfgRight cfg, x < M.sig) :
    xIsBlank M (rowX M cfg (cfgHead cfg))
      = decide ((cfgRight cfg).length < cfgHead cfg) := by
  unfold rowX
  by_cases h0 : cfgHead cfg = 0
  · rw [if_pos h0, h0]
    simp [xIsBlank]
  · rw [if_neg h0, xIsBlank_some,
      tapeSymAt_blank_iff M _ _ hsig]
    exact decide_eq_decide.2 (by omega)

/-- A copy-shaped card licenses an unchanged window once its first three
cells match. -/
theorem coversHead_copy (M : FlatTM) (x y z : Fin (Sg M)) (l rest : List (Fin (Sg M)))
    (h : l = x :: y :: z :: rest) :
    TCC.coversHead (copyCard M x y z) l l := by
  refine ⟨⟨rest, ?_⟩, ⟨rest, ?_⟩⟩ <;>
    · show l = [x, y, z] ++ rest
      exact h

private theorem xOpts_mem (M : FlatTM) (x : Option (Fin (M.sig + 1))) :
    x ∈ xOpts M := by
  cases x with
  | none => simp [xOpts]
  | some a => simp [xOpts]

theorem copyCard_mem (M : FlatTM) (x : Option (Fin (M.sig + 1))) (b c : Fin (M.sig + 1)) :
    copyCard M (xCell M x) (tCell M b) (tCell M c) ∈ copyCards M := by
  unfold copyCards
  refine List.mem_flatMap.2 ⟨x, xOpts_mem M x, ?_⟩
  refine List.mem_flatMap.2 ⟨b, List.mem_finRange b, ?_⟩
  exact List.mem_map.2 ⟨c, List.mem_finRange c, rfl⟩

theorem copyRightCard_mem (M : FlatTM) (y z : Fin (M.sig + 1)) :
    copyCard M (tCell M y) (tCell M z) (bCell M) ∈ copyRightCards M := by
  unfold copyRightCards
  refine List.mem_flatMap.2 ⟨y, List.mem_finRange y, ?_⟩
  exact List.mem_map.2 ⟨z, List.mem_finRange z, rfl⟩

theorem haltLeftCard_mem (M : FlatTM) (q : Fin (M.states + 1)) (b y z : Fin (M.sig + 1))
    (hq : M.halt.getD q.1 false = true) :
    copyCard M (hCell M q b) (tCell M y) (tCell M z) ∈ haltLeftCards M := by
  unfold haltLeftCards
  refine List.mem_flatMap.2 ⟨q, List.mem_finRange q, ?_⟩
  rw [if_pos hq]
  refine List.mem_flatMap.2 ⟨b, List.mem_finRange b, ?_⟩
  refine List.mem_flatMap.2 ⟨y, List.mem_finRange y, ?_⟩
  exact List.mem_map.2 ⟨z, List.mem_finRange z, rfl⟩

theorem haltCenterCard_mem (M : FlatTM) (q : Fin (M.states + 1)) (b : Fin (M.sig + 1))
    (x : Option (Fin (M.sig + 1))) (z : Fin (M.sig + 1))
    (hq : M.halt.getD q.1 false = true) :
    copyCard M (xCell M x) (hCell M q b) (tCell M z) ∈ haltCenterCards M := by
  unfold haltCenterCards
  refine List.mem_flatMap.2 ⟨q, List.mem_finRange q, ?_⟩
  rw [if_pos hq]
  refine List.mem_flatMap.2 ⟨b, List.mem_finRange b, ?_⟩
  refine List.mem_flatMap.2 ⟨x, xOpts_mem M x, ?_⟩
  exact List.mem_map.2 ⟨z, List.mem_finRange z, rfl⟩

theorem haltRightCard_mem (M : FlatTM) (q : Fin (M.states + 1)) (b : Fin (M.sig + 1))
    (x : Option (Fin (M.sig + 1))) (y : Fin (M.sig + 1))
    (hq : M.halt.getD q.1 false = true) :
    copyCard M (xCell M x) (tCell M y) (hCell M q b) ∈ haltRightCards M := by
  unfold haltRightCards
  refine List.mem_flatMap.2 ⟨q, List.mem_finRange q, ?_⟩
  rw [if_pos hq]
  refine List.mem_flatMap.2 ⟨b, List.mem_finRange b, ?_⟩
  refine List.mem_flatMap.2 ⟨x, xOpts_mem M x, ?_⟩
  exact List.mem_map.2 ⟨y, List.mem_finRange y, rfl⟩

theorem copyCard_mem_cookCards (M : FlatTM) (x : Option (Fin (M.sig + 1)))
    (b c : Fin (M.sig + 1)) :
    copyCard M (xCell M x) (tCell M b) (tCell M c) ∈ cookCards M := by
  unfold cookCards
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (copyCard_mem M x b c)))))

theorem copyRightCard_mem_cookCards (M : FlatTM) (y z : Fin (M.sig + 1)) :
    copyCard M (tCell M y) (tCell M z) (bCell M) ∈ cookCards M := by
  unfold cookCards
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (copyRightCard_mem M y z)))))

theorem haltLeftCard_mem_cookCards (M : FlatTM) (q : Fin (M.states + 1))
    (b y z : Fin (M.sig + 1)) (hq : M.halt.getD q.1 false = true) :
    copyCard M (hCell M q b) (tCell M y) (tCell M z) ∈ cookCards M := by
  unfold cookCards
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr (haltLeftCard_mem M q b y z hq))))

theorem haltCenterCard_mem_cookCards (M : FlatTM) (q : Fin (M.states + 1))
    (b : Fin (M.sig + 1)) (x : Option (Fin (M.sig + 1))) (z : Fin (M.sig + 1))
    (hq : M.halt.getD q.1 false = true) :
    copyCard M (xCell M x) (hCell M q b) (tCell M z) ∈ cookCards M := by
  unfold cookCards
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr (haltCenterCard_mem M q b x z hq)))

theorem haltRightCard_mem_cookCards (M : FlatTM) (q : Fin (M.states + 1))
    (b : Fin (M.sig + 1)) (x : Option (Fin (M.sig + 1))) (y : Fin (M.sig + 1))
    (hq : M.halt.getD q.1 false = true) :
    copyCard M (xCell M x) (tCell M y) (hCell M q b) ∈ cookCards M := by
  unfold cookCards
  simp only [List.mem_append]
  exact Or.inl (Or.inr (haltRightCard_mem M q b x y hq))

theorem stepCard_mem_cookCards (M : FlatTM) {c : TCCCard (Fin (Sg M))}
    (hc : c ∈ stepCards M) : c ∈ cookCards M := by
  unfold cookCards
  simp only [List.mem_append]
  exact Or.inr hc

private theorem stepCardCenter_mem (M : FlatTM) {e : FlatTMTransEntry}
    (he : e ∈ normTrans M) (x : Option (Fin (M.sig + 1))) (z : Fin (M.sig + 1)) :
    stepCardCenter M (stateOf M e.src_state) (stateOf M e.dst_state)
      (e.src_tape_vals.headD none) (e.dst_write_vals.headD none)
      (e.move_dirs.headD TMMove.Nmove) x z ∈ stepCards M := by
  unfold stepCards
  refine List.mem_flatMap.2 ⟨e, he, ?_⟩
  simp only [stepCardsOf, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (List.mem_flatMap.2 ⟨x, xOpts_mem M x,
    List.mem_map.2 ⟨z, List.mem_finRange z, rfl⟩⟩)))

private theorem stepCardsLeft_mem (M : FlatTM) {e : FlatTMTransEntry}
    (he : e ∈ normTrans M) (xb : Bool) (y z : Fin (M.sig + 1))
    {c : TCCCard (Fin (Sg M))}
    (hc : c ∈ stepCardsLeft M (stateOf M e.src_state) (stateOf M e.dst_state)
      (e.src_tape_vals.headD none) (e.dst_write_vals.headD none)
      (e.move_dirs.headD TMMove.Nmove) xb y z) :
    c ∈ stepCards M := by
  unfold stepCards
  refine List.mem_flatMap.2 ⟨e, he, ?_⟩
  simp only [stepCardsOf, List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.2 ⟨xb, by cases xb <;> simp,
    List.mem_flatMap.2 ⟨y, List.mem_finRange y,
      List.mem_flatMap.2 ⟨z, List.mem_finRange z, hc⟩⟩⟩)))

private theorem stepCardRight_mem (M : FlatTM) {e : FlatTMTransEntry}
    (he : e ∈ normTrans M) (x : Option (Fin (M.sig + 1))) (y : Fin (M.sig + 1)) :
    stepCardRight M (stateOf M e.src_state) (stateOf M e.dst_state)
      (e.src_tape_vals.headD none) (e.dst_write_vals.headD none)
      (e.move_dirs.headD TMMove.Nmove) x y ∈ stepCards M := by
  unfold stepCards
  refine List.mem_flatMap.2 ⟨e, he, ?_⟩
  simp only [stepCardsOf, List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatMap.2 ⟨x, xOpts_mem M x,
    List.mem_map.2 ⟨y, List.mem_finRange y, rfl⟩⟩))

private theorem stepCardInR_mem (M : FlatTM) {e : FlatTMTransEntry}
    (he : e ∈ normTrans M)
    (hmv : e.move_dirs.headD TMMove.Nmove = TMMove.Rmove)
    (y z u : Fin (M.sig + 1)) :
    stepCardInR M (stateOf M e.dst_state) y z u ∈ stepCards M := by
  unfold stepCards
  refine List.mem_flatMap.2 ⟨e, he, ?_⟩
  simp only [stepCardsOf, hmv, List.mem_append]
  exact Or.inr (List.mem_flatMap.2 ⟨y, List.mem_finRange y,
    List.mem_flatMap.2 ⟨z, List.mem_finRange z,
      List.mem_map.2 ⟨u, List.mem_finRange u, rfl⟩⟩⟩)

private theorem stepCardInL_mem (M : FlatTM) {e : FlatTMTransEntry}
    (he : e ∈ normTrans M)
    (hmv : e.move_dirs.headD TMMove.Nmove = TMMove.Lmove)
    (x : Option (Fin (M.sig + 1))) (y c : Fin (M.sig + 1)) :
    stepCardInL M (stateOf M e.dst_state) x y c ∈ stepCards M := by
  unfold stepCards
  refine List.mem_flatMap.2 ⟨e, he, ?_⟩
  simp only [stepCardsOf, hmv, List.mem_append]
  exact Or.inr (List.mem_flatMap.2 ⟨x, xOpts_mem M x,
    List.mem_flatMap.2 ⟨y, List.mem_finRange y,
      List.mem_map.2 ⟨c, List.mem_finRange c, rfl⟩⟩⟩)

/-- A window whose three coordinates carry no head in either row and whose
tape symbols agree between the rows is covered by a copy card. -/
private theorem copy_window (M : FlatTM) (cfg cfgB : FlatTMConfig) {n i : Nat}
    (hi : i + 2 ≤ n)
    (hA : ∀ j, i ≤ j → j ≤ i + 2 → j ≠ cfgHead cfg + 1)
    (hB : ∀ j, i ≤ j → j ≤ i + 2 → j ≠ cfgHead cfgB + 1)
    (hsym : ∀ p, i ≤ p + 1 → p + 1 ≤ i + 2 →
      tapeSymAt M (cfgRight cfgB) p = tapeSymAt M (cfgRight cfg) p) :
    TCC.coversHeadList (cookCards M)
      ((confRow M cfg n).drop i) ((confRow M cfgB n).drop i) := by
  have hxeq : rowX M cfgB i = rowX M cfg i := by
    unfold rowX
    by_cases h0 : i = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0, hsym (i - 1) (by omega) (by omega)]
  refine ⟨copyCard M (xCell M (rowX M cfg i))
      (tCell M (tapeSymAt M (cfgRight cfg) i))
      (tCell M (tapeSymAt M (cfgRight cfg) (i + 1))),
    copyCard_mem_cookCards M _ _ _,
    coversHead_take3 _ _ _ i ?_ ?_⟩
  · rw [confRow_window M cfg hi,
      rowCell_x M cfg (hA i (by omega) (by omega)),
      rowCell_tape M cfg (j := i + 1) (by omega) (hA (i + 1) (by omega) (by omega)),
      rowCell_tape M cfg (j := i + 2) (by omega) (hA (i + 2) (by omega) (by omega))]
    simp only [show i + 1 - 1 = i from by omega, show i + 2 - 1 = i + 1 from by omega]
    rfl
  · rw [confRow_window M cfgB hi,
      rowCell_x M cfgB (hB i (by omega) (by omega)),
      rowCell_tape M cfgB (j := i + 1) (by omega) (hB (i + 1) (by omega) (by omega)),
      rowCell_tape M cfgB (j := i + 2) (by omega) (hB (i + 2) (by omega) (by omega)),
      hxeq]
    simp only [show i + 1 - 1 = i from by omega, show i + 2 - 1 = i + 1 from by omega]
    rw [hsym i (by omega) (by omega), hsym (i + 1) (by omega) (by omega)]
    rfl

/-- The rightmost window — two head-free, symbol-agreeing coordinates and
the right marker — is covered by a `copyRightCards` card. -/
private theorem copyRight_window (M : FlatTM) (cfg cfgB : FlatTMConfig) {n i : Nat}
    (h1 : 1 ≤ i) (hi : i + 1 = n)
    (hA : ∀ j, i ≤ j → j ≤ i + 1 → j ≠ cfgHead cfg + 1)
    (hB : ∀ j, i ≤ j → j ≤ i + 1 → j ≠ cfgHead cfgB + 1)
    (hsym : ∀ p, i ≤ p + 1 → p + 1 ≤ i + 1 →
      tapeSymAt M (cfgRight cfgB) p = tapeSymAt M (cfgRight cfg) p) :
    TCC.coversHeadList (cookCards M)
      ((confRow M cfg n).drop i) ((confRow M cfgB n).drop i) := by
  refine ⟨copyCard M (tCell M (tapeSymAt M (cfgRight cfg) (i - 1)))
      (tCell M (tapeSymAt M (cfgRight cfg) i))
      (bCell M),
    copyRightCard_mem_cookCards M _ _,
    coversHead_take3 _ _ _ i ?_ ?_⟩
  · rw [confRow_window_last M cfg hi,
      rowCell_tape M cfg (j := i) (by omega) (hA i (by omega) (by omega)),
      rowCell_tape M cfg (j := i + 1) (by omega) (hA (i + 1) (by omega) (by omega))]
    simp only [show i + 1 - 1 = i from by omega]
    rfl
  · rw [confRow_window_last M cfgB hi,
      rowCell_tape M cfgB (j := i) (by omega) (hB i (by omega) (by omega)),
      rowCell_tape M cfgB (j := i + 1) (by omega) (hB (i + 1) (by omega) (by omega))]
    simp only [show i + 1 - 1 = i from by omega]
    rw [hsym (i - 1) (by omega) (by omega), hsym i (by omega) (by omega)]
    rfl

/-- **(1a) Card soundness of a machine step**: a legal non-halting machine
step is a card-covered row transition. Window `i` is cased on its position
relative to the head's row coordinate `h = cfgHead cfg + 1`: `i = h-1`
center (the firing entry's `stepCardCenter`; the left-neighbour blankness
matches the frontier by the invariant, so `wEff` computes the write),
`i = h` left-of, `i = h-2` right-of, `i = h+1` (`Rmove` incoming) /
`i = h-3` (`Lmove` incoming), all other windows all-tape (`copyCards`;
window 0 via the boundary variants, the rightmost window via
`copyRightCards`). `hhead` demands `+ 4` head-room so the `Rmove` incoming
window never collides with the right-marker window. `stepFlatTM_normM`
replaces the fired entry by its normalised representative (whose cards are
the generated ones). -/
theorem validStep_of_step (M : FlatTM) (n : Nat) {base t : Nat}
    {cfg cfg' : FlatTMConfig}
    (hV : validFlatTM M) (hfit : ConfFits M base t cfg)
    (hhead : cfgHead cfg + 4 ≤ n)
    (_hlen : (cfgRight cfg).length + 2 ≤ n)
    (hnh : haltingStateReached M cfg = false)
    (hstep : stepFlatTM M cfg = some cfg') :
    TCC.validStep (cookCards M) (confRow M cfg n) (confRow M cfg' n) := by
  -- switch to the normalised machine: its entries generate the cards
  have h1tape : cfg.tapes.length = 1 := by rw [hfit.tapes_eq]; rfl
  have hstepN : stepFlatTM (normM M) cfg = some cfg' := by
    rw [stepFlatTM_normM M cfg h1tape hnh]; exact hstep
  obtain ⟨e, heN, hmatch, hsrc, hvals, w, mv, hw, hmv, hcfg'⟩ :=
    step_desc (normM M) hfit.tapes_eq hstepN
  have heNT : e ∈ normTrans M := heN
  have heM : e ∈ M.trans := normTrans_subset M e heNT
  have hvalid := hV.2.2 e heM
  -- entry-field views
  have hmhead : e.src_tape_vals.headD none
      = currentTapeSymbol ([], cfgHead cfg, cfgRight cfg) := by rw [hvals]; rfl
  have hwhead : e.dst_write_vals.headD none = w := by rw [hw]; rfl
  have hmvhead : e.move_dirs.headD TMMove.Nmove = mv := by rw [hmv]; rfl
  -- the write effect
  have hwbound := hvalid.2.2.2.2.2.2 w (by rw [hw]; exact List.mem_singleton.2 rfl)
  obtain ⟨wr, hwt, hlen1, hlen2, hsyms, hunch, hwrhd⟩ :=
    write_facts M (cfgHead cfg) (cfgRight cfg) w hfit.syms_lt hwbound
  -- successor projections (the head is per-move, below)
  have hBst : cfg'.state_idx = e.dst_state := by rw [hcfg']
  have hBright : cfgRight cfg' = wr := by
    rw [hcfg']
    show (tapeStep ([], cfgHead cfg, cfgRight cfg) w mv).2.2 = wr
    unfold tapeStep
    rw [hwt]
    cases mv <;> rfl
  have hrowXeq : ∀ j, j ≠ cfgHead cfg + 1 → rowX M cfg' j = rowX M cfg j := by
    intro j hj
    unfold rowX
    by_cases h0 : j = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0, hBright, hunch (j - 1) (by omega)]
  -- the machine-read and frontier bridges
  have hR : tapeSymAt M (cfgRight cfg) (cfgHead cfg)
      = optSym M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) :=
    tapeSymAt_head M [] (cfgRight cfg) (cfgHead cfg)
  have hxbC : xIsBlank M (rowX M cfg (cfgHead cfg))
      = decide ((cfgRight cfg).length < cfgHead cfg) :=
    rowX_isBlank M cfg hfit.syms_lt
  -- card membership at the configuration's own field values
  have hmemC : ∀ x z, stepCardCenter M (stateOf M cfg.state_idx) (stateOf M e.dst_state)
      (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w mv x z ∈ cookCards M := by
    intro x z
    have h0 := stepCardCenter_mem M heNT x z
    rw [hsrc, hmhead, hwhead, hmvhead] at h0
    exact stepCard_mem_cookCards M h0
  have hmemLft : ∀ (xb : Bool) (y z : Fin (M.sig + 1)) (c : TCCCard (Fin (Sg M))),
      c ∈ stepCardsLeft M (stateOf M cfg.state_idx) (stateOf M e.dst_state)
        (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w mv xb y z →
      c ∈ cookCards M := by
    intro xb y z c hc
    have h0 := stepCardsLeft_mem M heNT xb y z (c := c)
    rw [hsrc, hmhead, hwhead, hmvhead] at h0
    exact stepCard_mem_cookCards M (h0 hc)
  have hmemRgt : ∀ x y, stepCardRight M (stateOf M cfg.state_idx) (stateOf M e.dst_state)
      (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w mv x y ∈ cookCards M := by
    intro x y
    have h0 := stepCardRight_mem M heNT x y
    rw [hsrc, hmhead, hwhead, hmvhead] at h0
    exact stepCard_mem_cookCards M h0
  cases mv with
  | Nmove =>
    have htape : tapeStep ([], cfgHead cfg, cfgRight cfg) w TMMove.Nmove
        = ([], cfgHead cfg, wr) := by
      simp [tapeStep, moveTapeHead, hwt]
    have hBhd : cfgHead cfg' = cfgHead cfg := by
      rw [hcfg', htape]; rfl
    refine ⟨by rw [confRow_length, confRow_length], ?_⟩
    intro i hi
    rw [confRow_length] at hi
    have hcase : i = cfgHead cfg ∨ i = cfgHead cfg + 1 ∨
        (1 ≤ cfgHead cfg ∧ i = cfgHead cfg - 1) ∨
        (i + 2 < cfgHead cfg + 1 ∨ cfgHead cfg + 1 < i) := by omega
    rcases hcase with rfl | rfl | ⟨h1, heq⟩ | hout
    · -- center window
      refine ⟨stepCardCenter M (stateOf M cfg.state_idx) (stateOf M e.dst_state)
          (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w TMMove.Nmove
          (rowX M cfg (cfgHead cfg)) (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)),
        hmemC _ _, coversHead_take3 _ _ _ _ ?_ ?_⟩
      · rw [confRow_window M cfg (by omega),
          rowCell_x M cfg (j := cfgHead cfg) (by omega),
          rowCell_head M cfg (j := cfgHead cfg + 1) rfl,
          rowCell_tape M cfg (j := cfgHead cfg + 2) (by omega) (by omega)]
        simp only [show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega]
        rw [hR]
        rfl
      · rw [confRow_window M cfg' (by omega),
          rowCell_x M cfg' (j := cfgHead cfg) (by omega),
          rowCell_head M cfg' (j := cfgHead cfg + 1) (by rw [hBhd]),
          rowCell_tape M cfg' (j := cfgHead cfg + 2) (by omega) (by omega),
          hBst, hBright, hBhd, hrowXeq (cfgHead cfg) (by omega)]
        simp only [show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega]
        rw [hwrhd, hunch (cfgHead cfg + 1) (by omega), ← hxbC]
        rfl
    · -- left-of window
      refine ⟨⟨⟨hCell M (stateOf M cfg.state_idx)
            (optSym M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg))),
          tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)),
          tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2))⟩,
          ⟨hCell M (stateOf M e.dst_state)
            (wEff M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w
              (decide ((cfgRight cfg).length < cfgHead cfg))),
          tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)),
          tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2))⟩⟩,
        hmemLft (decide ((cfgRight cfg).length < cfgHead cfg))
          (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1))
          (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2)) _
          (by simp [stepCardsLeft]),
        coversHead_take3 _ _ _ _ ?_ ?_⟩
      · rw [confRow_window M cfg (by omega),
          rowCell_head M cfg (j := cfgHead cfg + 1) rfl,
          rowCell_tape M cfg (j := cfgHead cfg + 1 + 1) (by omega) (by omega),
          rowCell_tape M cfg (j := cfgHead cfg + 1 + 2) (by omega) (by omega)]
        simp only [show cfgHead cfg + 1 + 1 - 1 = cfgHead cfg + 1 from by omega,
          show cfgHead cfg + 1 + 2 - 1 = cfgHead cfg + 2 from by omega]
        rw [hR]
        rfl
      · rw [confRow_window M cfg' (by omega),
          rowCell_head M cfg' (j := cfgHead cfg + 1) (by rw [hBhd]),
          rowCell_tape M cfg' (j := cfgHead cfg + 1 + 1) (by omega) (by omega),
          rowCell_tape M cfg' (j := cfgHead cfg + 1 + 2) (by omega) (by omega),
          hBst, hBright, hBhd]
        simp only [show cfgHead cfg + 1 + 1 - 1 = cfgHead cfg + 1 from by omega,
          show cfgHead cfg + 1 + 2 - 1 = cfgHead cfg + 2 from by omega]
        rw [hwrhd, hunch (cfgHead cfg + 1) (by omega), hunch (cfgHead cfg + 2) (by omega)]
        rfl
    · -- right-of window
      subst heq
      have hxbR : decide (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1) = blankSym M)
          = decide ((cfgRight cfg).length < cfgHead cfg) := by
        rw [tapeSymAt_blank_iff M _ _ hfit.syms_lt]
        exact decide_eq_decide.2 (by omega)
      refine ⟨stepCardRight M (stateOf M cfg.state_idx) (stateOf M e.dst_state)
          (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w TMMove.Nmove
          (rowX M cfg (cfgHead cfg - 1)) (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1)),
        hmemRgt _ _, coversHead_take3 _ _ _ _ ?_ ?_⟩
      · rw [confRow_window M cfg (by omega),
          rowCell_x M cfg (j := cfgHead cfg - 1) (by omega),
          rowCell_tape M cfg (j := cfgHead cfg - 1 + 1) (by omega) (by omega),
          rowCell_head M cfg (j := cfgHead cfg - 1 + 2) (by omega)]
        simp only [show cfgHead cfg - 1 + 1 - 1 = cfgHead cfg - 1 from by omega]
        rw [hR]
        rfl
      · rw [confRow_window M cfg' (by omega),
          rowCell_x M cfg' (j := cfgHead cfg - 1) (by omega),
          rowCell_tape M cfg' (j := cfgHead cfg - 1 + 1) (by omega) (by omega),
          rowCell_head M cfg' (j := cfgHead cfg - 1 + 2) (by omega),
          hBst, hBright, hBhd, hrowXeq (cfgHead cfg - 1) (by omega)]
        simp only [show cfgHead cfg - 1 + 1 - 1 = cfgHead cfg - 1 from by omega]
        rw [hwrhd, hunch (cfgHead cfg - 1) (by omega), ← hxbR]
        rfl
    · -- pure copy
      by_cases hlast : i + 1 = n
      · exact copyRight_window M cfg cfg' (by omega) hlast
          (fun j hj1 hj2 => by omega)
          (fun j hj1 hj2 => by rw [hBhd]; omega)
          (fun p hp1 hp2 => by rw [hBright]; exact hunch p (by omega))
      · exact copy_window M cfg cfg' (by omega)
          (fun j hj1 hj2 => by omega)
          (fun j hj1 hj2 => by rw [hBhd]; omega)
          (fun p hp1 hp2 => by rw [hBright]; exact hunch p (by omega))
  | Rmove =>
    have htape : tapeStep ([], cfgHead cfg, cfgRight cfg) w TMMove.Rmove
        = ([], cfgHead cfg + 1, wr) := by
      simp [tapeStep, moveTapeHead, hwt]
    have hBhd : cfgHead cfg' = cfgHead cfg + 1 := by
      rw [hcfg', htape]; rfl
    refine ⟨by rw [confRow_length, confRow_length], ?_⟩
    intro i hi
    rw [confRow_length] at hi
    have hcase : i = cfgHead cfg ∨ i = cfgHead cfg + 1 ∨
        (1 ≤ cfgHead cfg ∧ i = cfgHead cfg - 1) ∨ i = cfgHead cfg + 2 ∨
        (i + 2 < cfgHead cfg + 1 ∨ cfgHead cfg + 2 < i) := by omega
    rcases hcase with rfl | rfl | ⟨h1, heq⟩ | rfl | hout
    · -- center window: the head moves right inside it
      refine ⟨stepCardCenter M (stateOf M cfg.state_idx) (stateOf M e.dst_state)
          (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w TMMove.Rmove
          (rowX M cfg (cfgHead cfg)) (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)),
        hmemC _ _, coversHead_take3 _ _ _ _ ?_ ?_⟩
      · rw [confRow_window M cfg (by omega),
          rowCell_x M cfg (j := cfgHead cfg) (by omega),
          rowCell_head M cfg (j := cfgHead cfg + 1) rfl,
          rowCell_tape M cfg (j := cfgHead cfg + 2) (by omega) (by omega)]
        simp only [show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega]
        rw [hR]
        rfl
      · rw [confRow_window M cfg' (by omega),
          rowCell_x M cfg' (j := cfgHead cfg) (by omega),
          rowCell_tape M cfg' (j := cfgHead cfg + 1) (by omega) (by omega),
          rowCell_head M cfg' (j := cfgHead cfg + 2) (by rw [hBhd]),
          hBst, hBright, hBhd, hrowXeq (cfgHead cfg) (by omega)]
        simp only [show cfgHead cfg + 1 - 1 = cfgHead cfg from by omega]
        rw [hwrhd, hunch (cfgHead cfg + 1) (by omega), ← hxbC]
        rfl
    · -- left-of window: the head leaves right, entering the second cell
      refine ⟨⟨⟨hCell M (stateOf M cfg.state_idx)
            (optSym M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg))),
          tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)),
          tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2))⟩,
          ⟨tCell M
            (wEff M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w
              (decide ((cfgRight cfg).length < cfgHead cfg))),
          hCell M (stateOf M e.dst_state) (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)),
          tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2))⟩⟩,
        hmemLft (decide ((cfgRight cfg).length < cfgHead cfg))
          (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1))
          (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2)) _
          (by simp [stepCardsLeft]),
        coversHead_take3 _ _ _ _ ?_ ?_⟩
      · rw [confRow_window M cfg (by omega),
          rowCell_head M cfg (j := cfgHead cfg + 1) rfl,
          rowCell_tape M cfg (j := cfgHead cfg + 1 + 1) (by omega) (by omega),
          rowCell_tape M cfg (j := cfgHead cfg + 1 + 2) (by omega) (by omega)]
        simp only [show cfgHead cfg + 1 + 1 - 1 = cfgHead cfg + 1 from by omega,
          show cfgHead cfg + 1 + 2 - 1 = cfgHead cfg + 2 from by omega]
        rw [hR]
        rfl
      · rw [confRow_window M cfg' (by omega),
          rowCell_tape M cfg' (j := cfgHead cfg + 1) (by omega) (by omega),
          rowCell_head M cfg' (j := cfgHead cfg + 1 + 1) (by rw [hBhd]),
          rowCell_tape M cfg' (j := cfgHead cfg + 1 + 2) (by omega) (by omega),
          hBst, hBright, hBhd]
        simp only [show cfgHead cfg + 1 - 1 = cfgHead cfg from by omega,
          show cfgHead cfg + 1 + 2 - 1 = cfgHead cfg + 2 from by omega]
        rw [hwrhd, hunch (cfgHead cfg + 1) (by omega), hunch (cfgHead cfg + 2) (by omega)]
        rfl
    · -- right-of window: the head leaves it rightward
      subst heq
      have hxbR : decide (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1) = blankSym M)
          = decide ((cfgRight cfg).length < cfgHead cfg) := by
        rw [tapeSymAt_blank_iff M _ _ hfit.syms_lt]
        exact decide_eq_decide.2 (by omega)
      refine ⟨stepCardRight M (stateOf M cfg.state_idx) (stateOf M e.dst_state)
          (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w TMMove.Rmove
          (rowX M cfg (cfgHead cfg - 1)) (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1)),
        hmemRgt _ _, coversHead_take3 _ _ _ _ ?_ ?_⟩
      · rw [confRow_window M cfg (by omega),
          rowCell_x M cfg (j := cfgHead cfg - 1) (by omega),
          rowCell_tape M cfg (j := cfgHead cfg - 1 + 1) (by omega) (by omega),
          rowCell_head M cfg (j := cfgHead cfg - 1 + 2) (by omega)]
        simp only [show cfgHead cfg - 1 + 1 - 1 = cfgHead cfg - 1 from by omega]
        rw [hR]
        rfl
      · rw [confRow_window M cfg' (by omega),
          rowCell_x M cfg' (j := cfgHead cfg - 1) (by omega),
          rowCell_tape M cfg' (j := cfgHead cfg - 1 + 1) (by omega) (by omega),
          rowCell_tape M cfg' (j := cfgHead cfg - 1 + 2) (by omega) (by omega),
          hBright, hrowXeq (cfgHead cfg - 1) (by omega)]
        simp only [show cfgHead cfg - 1 + 2 - 1 = cfgHead cfg - 1 + 1 from by omega,
          show cfgHead cfg - 1 + 1 = cfgHead cfg from by omega]
        rw [hwrhd, hunch (cfgHead cfg - 1) (by omega), ← hxbR]
        rfl
    · -- incoming window: the head enters its first cell from the left
      refine ⟨stepCardInR M (stateOf M e.dst_state)
          (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1))
          (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2))
          (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 3)),
        stepCard_mem_cookCards M (stepCardInR_mem M heNT hmvhead _ _ _),
        coversHead_take3 _ _ _ _ ?_ ?_⟩
      · rw [confRow_window M cfg (by omega),
          rowCell_tape M cfg (j := cfgHead cfg + 2) (by omega) (by omega),
          rowCell_tape M cfg (j := cfgHead cfg + 2 + 1) (by omega) (by omega),
          rowCell_tape M cfg (j := cfgHead cfg + 2 + 2) (by omega) (by omega)]
        simp only [show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega,
          show cfgHead cfg + 2 + 1 - 1 = cfgHead cfg + 2 from by omega,
          show cfgHead cfg + 2 + 2 - 1 = cfgHead cfg + 3 from by omega]
        rfl
      · rw [confRow_window M cfg' (by omega),
          rowCell_head M cfg' (j := cfgHead cfg + 2) (by rw [hBhd]),
          rowCell_tape M cfg' (j := cfgHead cfg + 2 + 1) (by omega) (by omega),
          rowCell_tape M cfg' (j := cfgHead cfg + 2 + 2) (by omega) (by omega),
          hBst, hBright, hBhd]
        simp only [show cfgHead cfg + 2 + 1 - 1 = cfgHead cfg + 2 from by omega,
          show cfgHead cfg + 2 + 2 - 1 = cfgHead cfg + 3 from by omega]
        rw [hunch (cfgHead cfg + 1) (by omega), hunch (cfgHead cfg + 2) (by omega),
          hunch (cfgHead cfg + 3) (by omega)]
        rfl
    · -- pure copy
      by_cases hlast : i + 1 = n
      · exact copyRight_window M cfg cfg' (by omega) hlast
          (fun j hj1 hj2 => by omega)
          (fun j hj1 hj2 => by rw [hBhd]; omega)
          (fun p hp1 hp2 => by rw [hBright]; exact hunch p (by omega))
      · exact copy_window M cfg cfg' (by omega)
          (fun j hj1 hj2 => by omega)
          (fun j hj1 hj2 => by rw [hBhd]; omega)
          (fun p hp1 hp2 => by rw [hBright]; exact hunch p (by omega))
  | Lmove =>
    have htape : tapeStep ([], cfgHead cfg, cfgRight cfg) w TMMove.Lmove
        = ([], cfgHead cfg - 1, wr) := by
      simp [tapeStep, moveTapeHead, hwt]
    have hBhd : cfgHead cfg' = cfgHead cfg - 1 := by
      rw [hcfg', htape]; rfl
    refine ⟨by rw [confRow_length, confRow_length], ?_⟩
    intro i hi
    rw [confRow_length] at hi
    by_cases h0 : cfgHead cfg = 0
    · -- clamp at the left edge: the head stays at position 0
      have hcase : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
      rcases hcase with rfl | rfl | h2i
      · -- center window (boundary, head, tape): the clamp card
        have hxb0 : xIsBlank M (none : Option (Fin (M.sig + 1)))
            = decide ((cfgRight cfg).length < cfgHead cfg) := by
          rw [h0]
          simp [xIsBlank]
        refine ⟨stepCardCenter M (stateOf M cfg.state_idx) (stateOf M e.dst_state)
            (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w TMMove.Lmove
            none (tapeSymAt M (cfgRight cfg) 1),
          hmemC _ _, coversHead_take3 _ _ _ _ ?_ ?_⟩
        · rw [confRow_window M cfg (by omega),
            rowCell_zero M cfg,
            rowCell_head M cfg (j := 1) (by omega),
            rowCell_tape M cfg (j := 2) (by omega) (by omega)]
          rw [hR]
          rfl
        · rw [confRow_window M cfg' (by omega),
            rowCell_zero M cfg',
            rowCell_head M cfg' (j := 1) (by omega),
            rowCell_tape M cfg' (j := 2) (by omega) (by omega),
            hBst, hBright, hBhd]
          simp only [show cfgHead cfg - 1 = cfgHead cfg from by omega]
          rw [hwrhd, hunch (2 - 1) (by omega), ← hxb0]
          rfl
      · -- left-of window: the clamp variant of the left family
        refine ⟨⟨⟨hCell M (stateOf M cfg.state_idx)
              (optSym M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg))),
            tCell M (tapeSymAt M (cfgRight cfg) 1),
            tCell M (tapeSymAt M (cfgRight cfg) 2)⟩,
            ⟨hCell M (stateOf M e.dst_state)
              (wEff M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w
                (decide ((cfgRight cfg).length < cfgHead cfg))),
            tCell M (tapeSymAt M (cfgRight cfg) 1),
            tCell M (tapeSymAt M (cfgRight cfg) 2)⟩⟩,
          hmemLft (decide ((cfgRight cfg).length < cfgHead cfg))
            (tapeSymAt M (cfgRight cfg) 1) (tapeSymAt M (cfgRight cfg) 2) _
            (by simp [stepCardsLeft]),
          coversHead_take3 _ _ _ _ ?_ ?_⟩
        · rw [confRow_window M cfg (by omega),
            rowCell_head M cfg (j := 1) (by omega),
            rowCell_tape M cfg (j := 2) (by omega) (by omega),
            rowCell_tape M cfg (j := 3) (by omega) (by omega)]
          rw [hR]
          rfl
        · rw [confRow_window M cfg' (by omega),
            rowCell_head M cfg' (j := 1) (by omega),
            rowCell_tape M cfg' (j := 2) (by omega) (by omega),
            rowCell_tape M cfg' (j := 3) (by omega) (by omega),
            hBst, hBright, hBhd]
          simp only [show cfgHead cfg - 1 = cfgHead cfg from by omega]
          rw [hwrhd, hunch (2 - 1) (by omega), hunch (3 - 1) (by omega)]
          rfl
      · -- pure copy right of the clamped head
        by_cases hlast : i + 1 = n
        · exact copyRight_window M cfg cfg' (by omega) hlast
            (fun j hj1 hj2 => by omega)
            (fun j hj1 hj2 => by rw [hBhd]; omega)
            (fun p hp1 hp2 => by rw [hBright]; exact hunch p (by omega))
        · exact copy_window M cfg cfg' (by omega)
            (fun j hj1 hj2 => by omega)
            (fun j hj1 hj2 => by rw [hBhd]; omega)
            (fun p hp1 hp2 => by rw [hBright]; exact hunch p (by omega))
    · -- interior left move
      have hxbL : xIsBlank M (some (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1)))
          = decide ((cfgRight cfg).length < cfgHead cfg) := by
        rw [xIsBlank_some, tapeSymAt_blank_iff M _ _ hfit.syms_lt]
        exact decide_eq_decide.2 (by omega)
      have hcase : i = cfgHead cfg ∨ i = cfgHead cfg + 1 ∨ i = cfgHead cfg - 1 ∨
          (2 ≤ cfgHead cfg ∧ i = cfgHead cfg - 2) ∨
          (i + 2 < cfgHead cfg ∨ cfgHead cfg + 1 < i) := by omega
      rcases hcase with rfl | rfl | heq | ⟨h2, heq⟩ | hout
      · -- center window: the head leaves left inside it
        refine ⟨stepCardCenter M (stateOf M cfg.state_idx) (stateOf M e.dst_state)
            (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w TMMove.Lmove
            (some (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1)))
            (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)),
          hmemC _ _, coversHead_take3 _ _ _ _ ?_ ?_⟩
        · rw [confRow_window M cfg (by omega),
            rowCell_tape M cfg (j := cfgHead cfg) (by omega) (by omega),
            rowCell_head M cfg (j := cfgHead cfg + 1) rfl,
            rowCell_tape M cfg (j := cfgHead cfg + 2) (by omega) (by omega)]
          simp only [show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega]
          rw [hR]
          rfl
        · rw [confRow_window M cfg' (by omega),
            rowCell_head M cfg' (j := cfgHead cfg) (by omega),
            rowCell_tape M cfg' (j := cfgHead cfg + 1) (by omega) (by omega),
            rowCell_tape M cfg' (j := cfgHead cfg + 2) (by omega) (by omega),
            hBst, hBright, hBhd]
          simp only [show cfgHead cfg + 1 - 1 = cfgHead cfg from by omega,
            show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega]
          rw [hwrhd, hunch (cfgHead cfg - 1) (by omega),
            hunch (cfgHead cfg + 1) (by omega), ← hxbL]
          rfl
      · -- left-of window: the head exits left (leave variant)
        refine ⟨⟨⟨hCell M (stateOf M cfg.state_idx)
              (optSym M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg))),
            tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)),
            tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2))⟩,
            ⟨tCell M
              (wEff M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w
                (decide ((cfgRight cfg).length < cfgHead cfg))),
            tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)),
            tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2))⟩⟩,
          hmemLft (decide ((cfgRight cfg).length < cfgHead cfg))
            (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1))
            (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2)) _
            (by simp [stepCardsLeft]),
          coversHead_take3 _ _ _ _ ?_ ?_⟩
        · rw [confRow_window M cfg (by omega),
            rowCell_head M cfg (j := cfgHead cfg + 1) rfl,
            rowCell_tape M cfg (j := cfgHead cfg + 1 + 1) (by omega) (by omega),
            rowCell_tape M cfg (j := cfgHead cfg + 1 + 2) (by omega) (by omega)]
          simp only [show cfgHead cfg + 1 + 1 - 1 = cfgHead cfg + 1 from by omega,
            show cfgHead cfg + 1 + 2 - 1 = cfgHead cfg + 2 from by omega]
          rw [hR]
          rfl
        · rw [confRow_window M cfg' (by omega),
            rowCell_tape M cfg' (j := cfgHead cfg + 1) (by omega) (by omega),
            rowCell_tape M cfg' (j := cfgHead cfg + 1 + 1) (by omega) (by omega),
            rowCell_tape M cfg' (j := cfgHead cfg + 1 + 2) (by omega) (by omega),
            hBright]
          simp only [show cfgHead cfg + 1 - 1 = cfgHead cfg from by omega,
            show cfgHead cfg + 1 + 1 - 1 = cfgHead cfg + 1 from by omega,
            show cfgHead cfg + 1 + 2 - 1 = cfgHead cfg + 2 from by omega]
          rw [hwrhd, hunch (cfgHead cfg + 1) (by omega), hunch (cfgHead cfg + 2) (by omega)]
          rfl
      · -- right-of window: the head enters its second cell
        subst heq
        have hxbR : decide (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1) = blankSym M)
            = decide ((cfgRight cfg).length < cfgHead cfg) := by
          rw [tapeSymAt_blank_iff M _ _ hfit.syms_lt]
          exact decide_eq_decide.2 (by omega)
        refine ⟨stepCardRight M (stateOf M cfg.state_idx) (stateOf M e.dst_state)
            (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w TMMove.Lmove
            (rowX M cfg (cfgHead cfg - 1)) (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1)),
          hmemRgt _ _, coversHead_take3 _ _ _ _ ?_ ?_⟩
        · rw [confRow_window M cfg (by omega),
            rowCell_x M cfg (j := cfgHead cfg - 1) (by omega),
            rowCell_tape M cfg (j := cfgHead cfg - 1 + 1) (by omega) (by omega),
            rowCell_head M cfg (j := cfgHead cfg - 1 + 2) (by omega)]
          simp only [show cfgHead cfg - 1 + 1 - 1 = cfgHead cfg - 1 from by omega]
          rw [hR]
          rfl
        · rw [confRow_window M cfg' (by omega),
            rowCell_x M cfg' (j := cfgHead cfg - 1) (by omega),
            rowCell_head M cfg' (j := cfgHead cfg - 1 + 1) (by rw [hBhd]),
            rowCell_tape M cfg' (j := cfgHead cfg - 1 + 2) (by omega) (by omega),
            hBst, hBright, hBhd, hrowXeq (cfgHead cfg - 1) (by omega)]
          simp only [show cfgHead cfg - 1 + 2 - 1 = cfgHead cfg from by omega]
          rw [hwrhd, hunch (cfgHead cfg - 1) (by omega), ← hxbR]
          rfl
      · -- incoming window: the head enters its third cell from the right
        subst heq
        refine ⟨stepCardInL M (stateOf M e.dst_state)
            (rowX M cfg (cfgHead cfg - 2))
            (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 2))
            (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1)),
          stepCard_mem_cookCards M (stepCardInL_mem M heNT hmvhead _ _ _),
          coversHead_take3 _ _ _ _ ?_ ?_⟩
        · rw [confRow_window M cfg (by omega),
            rowCell_x M cfg (j := cfgHead cfg - 2) (by omega),
            rowCell_tape M cfg (j := cfgHead cfg - 2 + 1) (by omega) (by omega),
            rowCell_tape M cfg (j := cfgHead cfg - 2 + 2) (by omega) (by omega)]
          simp only [show cfgHead cfg - 2 + 1 - 1 = cfgHead cfg - 2 from by omega,
            show cfgHead cfg - 2 + 2 - 1 = cfgHead cfg - 1 from by omega]
          rfl
        · rw [confRow_window M cfg' (by omega),
            rowCell_x M cfg' (j := cfgHead cfg - 2) (by omega),
            rowCell_tape M cfg' (j := cfgHead cfg - 2 + 1) (by omega) (by omega),
            rowCell_head M cfg' (j := cfgHead cfg - 2 + 2) (by omega),
            hBst, hBright, hBhd, hrowXeq (cfgHead cfg - 2) (by omega)]
          simp only [show cfgHead cfg - 2 + 1 - 1 = cfgHead cfg - 2 from by omega]
          rw [hunch (cfgHead cfg - 2) (by omega), hunch (cfgHead cfg - 1) (by omega)]
          rfl
      · -- pure copy
        by_cases hlast : i + 1 = n
        · exact copyRight_window M cfg cfg' (by omega) hlast
            (fun j hj1 hj2 => by omega)
            (fun j hj1 hj2 => by rw [hBhd]; omega)
            (fun p hp1 hp2 => by rw [hBright]; exact hunch p (by omega))
        · exact copy_window M cfg cfg' (by omega)
            (fun j hj1 hj2 => by omega)
            (fun j hj1 hj2 => by rw [hBhd]; omega)
            (fun p hp1 hp2 => by rw [hBright]; exact hunch p (by omega))

/-- **(1a′) Halt freeze**: a halting configuration's row covers itself —
the three head windows by the halt-freeze families, the rest by copy cards.
(Generalises the proven empty-input case `freeze_validStep`.) -/
theorem validStep_of_halt (M : FlatTM) (n : Nat) {base t : Nat}
    {cfg : FlatTMConfig}
    (hfit : ConfFits M base t cfg)
    (hhead : cfgHead cfg + 3 ≤ n)
    (hh : haltingStateReached M cfg = true) :
    TCC.validStep (cookCards M) (confRow M cfg n) (confRow M cfg n) := by
  have hstate := hfit.state_lt
  have hq : M.halt.getD (stateOf M cfg.state_idx).1 false = true := by
    have hqv : (stateOf M cfg.state_idx).1 = cfg.state_idx := by
      simp [stateOf]; omega
    rw [hqv]; exact hh
  refine ⟨rfl, ?_⟩
  intro i hi
  rw [confRow_length] at hi
  have hcase : i = cfgHead cfg ∨ i = cfgHead cfg + 1 ∨
      (1 ≤ cfgHead cfg ∧ i = cfgHead cfg - 1) ∨
      (i + 2 < cfgHead cfg + 1 ∨ cfgHead cfg + 1 < i) := by omega
  rcases hcase with rfl | rfl | ⟨h1, heq⟩ | hout
  · -- head at the window's second cell: halt-center
    refine ⟨copyCard M (xCell M (rowX M cfg (cfgHead cfg)))
        (hCell M (stateOf M cfg.state_idx) (tapeSymAt M (cfgRight cfg) (cfgHead cfg)))
        (tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1))),
      haltCenterCard_mem_cookCards M _ _ _ _ hq,
      coversHead_take3 _ _ _ _ ?_ ?_⟩ <;>
    · rw [confRow_window M cfg (by omega),
        rowCell_x M cfg (j := cfgHead cfg) (by omega),
        rowCell_head M cfg (j := cfgHead cfg + 1) rfl,
        rowCell_tape M cfg (j := cfgHead cfg + 2) (by omega) (by omega)]
      simp only [show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega]
      rfl
  · -- head at the window's first cell: halt-left
    refine ⟨copyCard M
        (hCell M (stateOf M cfg.state_idx) (tapeSymAt M (cfgRight cfg) (cfgHead cfg)))
        (tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)))
        (tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 2))),
      haltLeftCard_mem_cookCards M _ _ _ _ hq,
      coversHead_take3 _ _ _ _ ?_ ?_⟩ <;>
    · rw [confRow_window M cfg (by omega),
        rowCell_head M cfg (j := cfgHead cfg + 1) rfl,
        rowCell_tape M cfg (j := cfgHead cfg + 1 + 1) (by omega) (by omega),
        rowCell_tape M cfg (j := cfgHead cfg + 1 + 2) (by omega) (by omega)]
      simp only [show cfgHead cfg + 1 + 1 - 1 = cfgHead cfg + 1 from by omega,
        show cfgHead cfg + 1 + 2 - 1 = cfgHead cfg + 2 from by omega]
      rfl
  · -- head at the window's third cell: halt-right
    subst heq
    refine ⟨copyCard M (xCell M (rowX M cfg (cfgHead cfg - 1)))
        (tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1)))
        (hCell M (stateOf M cfg.state_idx) (tapeSymAt M (cfgRight cfg) (cfgHead cfg))),
      haltRightCard_mem_cookCards M _ _ _ _ hq,
      coversHead_take3 _ _ _ _ ?_ ?_⟩ <;>
    · rw [confRow_window M cfg (by omega),
        rowCell_x M cfg (j := cfgHead cfg - 1) (by omega),
        rowCell_tape M cfg (j := cfgHead cfg - 1 + 1) (by omega) (by omega),
        rowCell_head M cfg (j := cfgHead cfg - 1 + 2) (by omega)]
      simp only [show cfgHead cfg - 1 + 1 - 1 = cfgHead cfg - 1 from by omega]
      rfl
  · -- head nowhere in the window: pure copy
    by_cases hlast : i + 1 = n
    · exact copyRight_window M cfg cfg (by omega) hlast
        (fun j hj1 hj2 => by omega)
        (fun j hj1 hj2 => by omega)
        (fun p _ _ => rfl)
    · exact copy_window M cfg cfg (by omega)
        (fun j hj1 hj2 => by omega)
        (fun j hj1 hj2 => by omega)
        (fun p _ _ => rfl)

/-! ### Direction (1b) — inversion machinery

The converse of the window machinery: invert a covering fact into six cell
equations (`window_card`), classify the matched card by its premise cells
via the code bands (`cookCards_cases`/`stepCardsOf_cases` + the four shape
lemmas), and pin every coordinate of the successor row. `rowCellM` is the
total coordinate view including the right marker at `n + 1`. -/

/-- Total row-cell view: coordinate `n + 1` is the right boundary marker,
everything below is `rowCell`. -/
private def rowCellM (M : FlatTM) (cfg : FlatTMConfig) (n j : Nat) : Fin (Sg M) :=
  if j = n + 1 then bCell M else rowCell M cfg j

private theorem confRow_getElem' (M : FlatTM) (cfg : FlatTMConfig) {n j : Nat}
    (hlt : j < (confRow M cfg n).length) :
    (confRow M cfg n)[j]'hlt = rowCellM M cfg n j := by
  by_cases hj : j = n + 1
  · subst hj
    rw [confRow_getElem_last M cfg]
    unfold rowCellM
    rw [if_pos rfl]
  · have hle : j ≤ n := by rw [confRow_length] at hlt; omega
    rw [confRow_getElem M cfg hle hlt]
    unfold rowCellM
    rw [if_neg hj]

private theorem xCell_ne_hCell (M : FlatTM) (x : Option (Fin (M.sig + 1)))
    (q : Fin (M.states + 1)) (d : Fin (M.sig + 1)) : xCell M x ≠ hCell M q d := by
  cases x with
  | none => exact fun h => hCell_ne_bCell M q d h.symm
  | some a => exact tCell_ne_hCell M a d q

private theorem xCell_inj (M : FlatTM) {x y : Option (Fin (M.sig + 1))}
    (h : xCell M x = xCell M y) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b => exact absurd h.symm (tCell_ne_bCell M b)
  | some a =>
    cases y with
    | none => exact absurd h (tCell_ne_bCell M a)
    | some b => exact congrArg some (tCell_inj M h)

/-- Away from the head coordinate, a row cell is never a head cell. -/
private theorem rowCellM_ne_hCell (M : FlatTM) (cfg : FlatTMConfig) {n j : Nat}
    (hj : j ≠ cfgHead cfg + 1) (q : Fin (M.states + 1)) (d : Fin (M.sig + 1)) :
    rowCellM M cfg n j ≠ hCell M q d := by
  unfold rowCellM
  by_cases hlast : j = n + 1
  · rw [if_pos hlast]
    exact fun h => hCell_ne_bCell M q d h.symm
  · rw [if_neg hlast, rowCell_x M cfg hj]
    exact xCell_ne_hCell M _ q d

/-- One covered window of a configuration row, inverted into six cell
equations (the converse of `coversHead_take3`). -/
private theorem window_card (M : FlatTM) {cfg : FlatTMConfig} {n : Nat}
    {b : List (Fin (Sg M))}
    (hvs : TCC.validStep (cookCards M) (confRow M cfg n) b)
    {i : Nat} (hi : i + 3 ≤ n + 2) :
    ∃ card ∈ cookCards M,
      (card.prem.cardEl1 = rowCellM M cfg n i ∧
       card.prem.cardEl2 = rowCellM M cfg n (i + 1) ∧
       card.prem.cardEl3 = rowCellM M cfg n (i + 2)) ∧
      (b[i]? = some card.conc.cardEl1 ∧ b[i + 1]? = some card.conc.cardEl2 ∧
       b[i + 2]? = some card.conc.cardEl3) := by
  obtain ⟨hlenEq, hcov⟩ := hvs
  rw [confRow_length] at hlenEq
  obtain ⟨card, hmem, ⟨ra, hra⟩, ⟨rb, hrb⟩⟩ :=
    hcov i (by rw [confRow_length]; omega)
  refine ⟨card, hmem, ?_, ?_⟩
  · have htake : ((confRow M cfg n).drop i).take 3
        = [card.prem.cardEl1, card.prem.cardEl2, card.prem.cardEl3] := by
      rw [hra]; rfl
    rw [take3_drop _ i (by rw [confRow_length]; omega)] at htake
    simp only [List.cons.injEq, and_true] at htake
    obtain ⟨e1, e2, e3⟩ := htake
    exact ⟨by rw [← e1]; exact confRow_getElem' M cfg _,
           by rw [← e2]; exact confRow_getElem' M cfg _,
           by rw [← e3]; exact confRow_getElem' M cfg _⟩
  · have hlb : i + 3 ≤ b.length := by omega
    have htake : (b.drop i).take 3
        = [card.conc.cardEl1, card.conc.cardEl2, card.conc.cardEl3] := by
      rw [hrb]; rfl
    rw [take3_drop b i hlb] at htake
    simp only [List.cons.injEq, and_true] at htake
    obtain ⟨f1, f2, f3⟩ := htake
    exact ⟨by rw [List.getElem?_eq_getElem (by omega), f1],
           by rw [List.getElem?_eq_getElem (by omega), f2],
           by rw [List.getElem?_eq_getElem (by omega), f3]⟩

/-- Every `cookCards` member, by family. -/
private theorem cookCards_cases (M : FlatTM) {c : TCCCard (Fin (Sg M))}
    (hc : c ∈ cookCards M) :
    (∃ x y z, c = copyCard M (xCell M x) (tCell M y) (tCell M z)) ∨
    (∃ y z, c = copyCard M (tCell M y) (tCell M z) (bCell M)) ∨
    (∃ q d y z, M.halt.getD q.1 false = true ∧
      c = copyCard M (hCell M q d) (tCell M y) (tCell M z)) ∨
    (∃ q d x z, M.halt.getD q.1 false = true ∧
      c = copyCard M (xCell M x) (hCell M q d) (tCell M z)) ∨
    (∃ q d x y, M.halt.getD q.1 false = true ∧
      c = copyCard M (xCell M x) (tCell M y) (hCell M q d)) ∨
    (∃ e ∈ normTrans M, c ∈ stepCardsOf M e) := by
  unfold cookCards at hc
  simp only [List.mem_append] at hc
  rcases hc with ((((hc | hc) | hc) | hc) | hc) | hc
  · left
    unfold copyCards at hc
    obtain ⟨x, -, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨y, -, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨x, y, z, rfl⟩
  · right; left
    unfold copyRightCards at hc
    obtain ⟨y, -, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨y, z, rfl⟩
  · right; right; left
    unfold haltLeftCards at hc
    obtain ⟨q, -, hc⟩ := List.mem_flatMap.1 hc
    by_cases hq : M.halt.getD q.1 false = true
    · rw [if_pos hq] at hc
      obtain ⟨d, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨y, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hc
      exact ⟨q, d, y, z, hq, rfl⟩
    · rw [if_neg hq] at hc
      simp at hc
  · right; right; right; left
    unfold haltCenterCards at hc
    obtain ⟨q, -, hc⟩ := List.mem_flatMap.1 hc
    by_cases hq : M.halt.getD q.1 false = true
    · rw [if_pos hq] at hc
      obtain ⟨d, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨x, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hc
      exact ⟨q, d, x, z, hq, rfl⟩
    · rw [if_neg hq] at hc
      simp at hc
  · right; right; right; right; left
    unfold haltRightCards at hc
    obtain ⟨q, -, hc⟩ := List.mem_flatMap.1 hc
    by_cases hq : M.halt.getD q.1 false = true
    · rw [if_pos hq] at hc
      obtain ⟨d, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨x, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hc
      exact ⟨q, d, x, y, hq, rfl⟩
    · rw [if_neg hq] at hc
      simp at hc
  · right; right; right; right; right
    unfold stepCards at hc
    exact List.mem_flatMap.1 hc

/-- Every card of one entry's `stepCardsOf`, by family. -/
private theorem stepCardsOf_cases (M : FlatTM) (e : FlatTMTransEntry)
    {c : TCCCard (Fin (Sg M))} (hc : c ∈ stepCardsOf M e) :
    (∃ x z, c = stepCardCenter M (stateOf M e.src_state) (stateOf M e.dst_state)
        (e.src_tape_vals.headD none) (e.dst_write_vals.headD none)
        (e.move_dirs.headD TMMove.Nmove) x z) ∨
    (∃ xb y z, c ∈ stepCardsLeft M (stateOf M e.src_state) (stateOf M e.dst_state)
        (e.src_tape_vals.headD none) (e.dst_write_vals.headD none)
        (e.move_dirs.headD TMMove.Nmove) xb y z) ∨
    (∃ x y, c = stepCardRight M (stateOf M e.src_state) (stateOf M e.dst_state)
        (e.src_tape_vals.headD none) (e.dst_write_vals.headD none)
        (e.move_dirs.headD TMMove.Nmove) x y) ∨
    (e.move_dirs.headD TMMove.Nmove = TMMove.Rmove ∧
      ∃ y z u, c = stepCardInR M (stateOf M e.dst_state) y z u) ∨
    (e.move_dirs.headD TMMove.Nmove = TMMove.Lmove ∧
      ∃ x y u, c = stepCardInL M (stateOf M e.dst_state) x y u) := by
  simp only [stepCardsOf, List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · left
    obtain ⟨x, -, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨x, z, rfl⟩
  · right; left
    obtain ⟨xb, -, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨y, -, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨z, -, hc⟩ := List.mem_flatMap.1 hc
    exact ⟨xb, y, z, hc⟩
  · right; right; left
    obtain ⟨x, -, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨x, y, rfl⟩
  · split at hc
    · right; right; right; left
      refine ⟨by assumption, ?_⟩
      obtain ⟨y, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨z, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hc
      exact ⟨y, z, u, rfl⟩
    · right; right; right; right
      refine ⟨by assumption, ?_⟩
      obtain ⟨x, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨y, -, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hc
      exact ⟨x, y, u, rfl⟩
    · simp at hc

/-- **(1b) stage (i), middle slot.** A card whose premise contains no head
cell keeps its middle cell: the head-free-matching families are
copy/copyRight (conc = prem) and the two incoming-head families (which keep
slot 2). There is deliberately no head-at-second-slot family — this is the
no-spurious-heads linchpin. -/
private theorem card_headfree_middle (M : FlatTM) {c : TCCCard (Fin (Sg M))}
    (hc : c ∈ cookCards M)
    (h1 : ∀ q d, c.prem.cardEl1 ≠ hCell M q d)
    (h2 : ∀ q d, c.prem.cardEl2 ≠ hCell M q d)
    (h3 : ∀ q d, c.prem.cardEl3 ≠ hCell M q d) :
    c.conc.cardEl2 = c.prem.cardEl2 := by
  rcases cookCards_cases M hc with
    ⟨x, y, z, rfl⟩ | ⟨y, z, rfl⟩ | ⟨q, d, y, z, hq, rfl⟩ | ⟨q, d, x, z, hq, rfl⟩ |
      ⟨q, d, x, y, hq, rfl⟩ | ⟨e, heN, hcof⟩
  · rfl
  · rfl
  · exact absurd rfl (h1 q d)
  · exact absurd rfl (h2 q d)
  · exact absurd rfl (h3 q d)
  · rcases stepCardsOf_cases M e hcof with
      ⟨x, z, rfl⟩ | ⟨xb, y, z, hcl⟩ | ⟨x, y, rfl⟩ | ⟨hmv, y, z, u, rfl⟩ |
        ⟨hmv, x, y, u, rfl⟩
    · exact absurd rfl (h2 _ _)
    · cases hmv : e.move_dirs.headD TMMove.Nmove with
      | Nmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        subst hcl
        exact absurd rfl (h1 _ _)
      | Rmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        subst hcl
        exact absurd rfl (h1 _ _)
      | Lmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        rcases hcl with rfl | rfl <;> exact absurd rfl (h1 _ _)
    · cases hmv : e.move_dirs.headD TMMove.Nmove with
      | Nmove => rw [hmv] at h3; exact absurd rfl (h3 _ _)
      | Rmove => rw [hmv] at h3; exact absurd rfl (h3 _ _)
      | Lmove => rw [hmv] at h3; exact absurd rfl (h3 _ _)
    · rfl
    · rfl

/-- **(1b) stage (iii), left edge.** A card matching a boundary-marker first
slot keeps it. -/
private theorem card_bfirst (M : FlatTM) {c : TCCCard (Fin (Sg M))}
    (hc : c ∈ cookCards M) (hb : c.prem.cardEl1 = bCell M) :
    c.conc.cardEl1 = bCell M := by
  rcases cookCards_cases M hc with
    ⟨x, y, z, rfl⟩ | ⟨y, z, rfl⟩ | ⟨q, d, y, z, hq, rfl⟩ | ⟨q, d, x, z, hq, rfl⟩ |
      ⟨q, d, x, y, hq, rfl⟩ | ⟨e, heN, hcof⟩
  · exact hb
  · exact hb
  · exact hb
  · exact hb
  · exact hb
  · rcases stepCardsOf_cases M e hcof with
      ⟨x, z, rfl⟩ | ⟨xb, y, z, hcl⟩ | ⟨x, y, rfl⟩ | ⟨hmv, y, z, u, rfl⟩ |
        ⟨hmv, x, y, u, rfl⟩
    · have hx : x = none := xCell_inj M (show xCell M x = xCell M none from hb)
      subst hx
      cases hmv : e.move_dirs.headD TMMove.Nmove with
      | Nmove => rfl
      | Rmove => rfl
      | Lmove => rfl
    · cases hmv : e.move_dirs.headD TMMove.Nmove with
      | Nmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        subst hcl
        exact absurd hb (hCell_ne_bCell M _ _)
      | Rmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        subst hcl
        exact absurd hb (hCell_ne_bCell M _ _)
      | Lmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        rcases hcl with rfl | rfl <;> exact absurd hb (hCell_ne_bCell M _ _)
    · cases hmv : e.move_dirs.headD TMMove.Nmove with
      | Nmove => rw [hmv] at hb; exact hb
      | Rmove => rw [hmv] at hb; exact hb
      | Lmove => rw [hmv] at hb; exact hb
    · exact absurd hb (tCell_ne_bCell M y)
    · exact hb

/-- **(1b) stage (iii), right edge.** Only `copyRightCards` has the boundary
marker in the third premise slot — so the marker window is cell-preserving
(the 2026-07-18-c phantom-head fix, machine-checked side). -/
private theorem card_blast (M : FlatTM) {c : TCCCard (Fin (Sg M))}
    (hc : c ∈ cookCards M) (hb : c.prem.cardEl3 = bCell M) :
    c.conc = c.prem := by
  rcases cookCards_cases M hc with
    ⟨x, y, z, rfl⟩ | ⟨y, z, rfl⟩ | ⟨q, d, y, z, hq, rfl⟩ | ⟨q, d, x, z, hq, rfl⟩ |
      ⟨q, d, x, y, hq, rfl⟩ | ⟨e, heN, hcof⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases stepCardsOf_cases M e hcof with
      ⟨x, z, rfl⟩ | ⟨xb, y, z, hcl⟩ | ⟨x, y, rfl⟩ | ⟨hmv, y, z, u, rfl⟩ |
        ⟨hmv, x, y, u, rfl⟩
    · exact absurd hb (tCell_ne_bCell M z)
    · cases hmv : e.move_dirs.headD TMMove.Nmove with
      | Nmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        subst hcl
        exact absurd hb (tCell_ne_bCell M _)
      | Rmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        subst hcl
        exact absurd hb (tCell_ne_bCell M _)
      | Lmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        rcases hcl with rfl | rfl <;> exact absurd hb (tCell_ne_bCell M _)
    · cases hmv : e.move_dirs.headD TMMove.Nmove with
      | Nmove => rw [hmv] at hb; exact absurd hb (hCell_ne_bCell M _ _)
      | Rmove => rw [hmv] at hb; exact absurd hb (hCell_ne_bCell M _ _)
      | Lmove => rw [hmv] at hb; exact absurd hb (hCell_ne_bCell M _ _)
    · exact absurd hb (tCell_ne_bCell M u)
    · exact absurd hb (tCell_ne_bCell M u)

/-- **(1b) stage (ii), the center window.** A card whose premise carries a
head cell in its middle slot is either a halt-freeze card of that (halting)
state (conc = prem) or the center card of a normalised entry keyed on
exactly that (state, read) pair. -/
private theorem card_head_center (M : FlatTM) {c : TCCCard (Fin (Sg M))}
    {q : Fin (M.states + 1)} {R : Fin (M.sig + 1)}
    (hc : c ∈ cookCards M) (hh : c.prem.cardEl2 = hCell M q R) :
    (M.halt.getD q.1 false = true ∧ c.conc = c.prem) ∨
    (∃ e ∈ normTrans M, ∃ x z,
      stateOf M e.src_state = q ∧
      optSym M (e.src_tape_vals.headD none) = R ∧
      c = stepCardCenter M (stateOf M e.src_state) (stateOf M e.dst_state)
        (e.src_tape_vals.headD none) (e.dst_write_vals.headD none)
        (e.move_dirs.headD TMMove.Nmove) x z ∧
      c.prem.cardEl1 = xCell M x ∧ c.prem.cardEl3 = tCell M z) := by
  rcases cookCards_cases M hc with
    ⟨x, y, z, rfl⟩ | ⟨y, z, rfl⟩ | ⟨q', d, y, z, hq, rfl⟩ | ⟨q', d, x, z, hq, rfl⟩ |
      ⟨q', d, x, y, hq, rfl⟩ | ⟨e, heN, hcof⟩
  · exact absurd hh (tCell_ne_hCell M y R q)
  · exact absurd hh (tCell_ne_hCell M z R q)
  · exact absurd hh (tCell_ne_hCell M y R q)
  · obtain ⟨hq', -⟩ := hCell_inj M (show hCell M q' d = hCell M q R from hh)
    subst hq'
    exact Or.inl ⟨hq, rfl⟩
  · exact absurd hh (tCell_ne_hCell M y R q)
  · rcases stepCardsOf_cases M e hcof with
      ⟨x, z, rfl⟩ | ⟨xb, y, z, hcl⟩ | ⟨x, y, rfl⟩ | ⟨hmv, y, z, u, rfl⟩ |
        ⟨hmv, x, y, u, rfl⟩
    · obtain ⟨hq', hR⟩ := hCell_inj M
        (show hCell M (stateOf M e.src_state)
          (optSym M (e.src_tape_vals.headD none)) = hCell M q R from hh)
      exact Or.inr ⟨e, heN, x, z, hq', hR, rfl, rfl, rfl⟩
    · cases hmv : e.move_dirs.headD TMMove.Nmove with
      | Nmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        subst hcl
        exact absurd hh (tCell_ne_hCell M _ R q)
      | Rmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        subst hcl
        exact absurd hh (tCell_ne_hCell M _ R q)
      | Lmove =>
        rw [hmv] at hcl
        simp only [stepCardsLeft, List.mem_cons, List.not_mem_nil, or_false] at hcl
        rcases hcl with rfl | rfl <;> exact absurd hh (tCell_ne_hCell M _ R q)
    · cases hmv : e.move_dirs.headD TMMove.Nmove with
      | Nmove => rw [hmv] at hh; exact absurd hh (tCell_ne_hCell M _ R q)
      | Rmove => rw [hmv] at hh; exact absurd hh (tCell_ne_hCell M _ R q)
      | Lmove => rw [hmv] at hh; exact absurd hh (tCell_ne_hCell M _ R q)
    · exact absurd hh (tCell_ne_hCell M z R q)
    · exact absurd hh (tCell_ne_hCell M y R q)

/-! Key uniqueness of the normalised table: `dedupGo` output is pairwise
key-distinct, so a matching member IS the `find?` result. -/

/-- Entries surviving `dedupGo` share no key with the `seen` accumulator. -/
private theorem dedupGo_notin_seen :
    ∀ (l seen : List FlatTMTransEntry), ∀ e ∈ dedupGo seen l, ∀ p ∈ seen,
      sameKey p e = false
  | [], _ => by intro e he; simp [dedupGo] at he
  | a :: as, seen => by
      intro e he p hp
      simp only [dedupGo] at he
      by_cases hany : seen.any (fun q => sameKey q a) = true
      · rw [if_pos hany] at he
        exact dedupGo_notin_seen as seen e he p hp
      · rw [if_neg hany] at he
        rcases List.mem_cons.1 he with rfl | he'
        · by_contra hcon
          rw [Bool.not_eq_false] at hcon
          exact hany (List.any_eq_true.2 ⟨p, hp, hcon⟩)
        · exact dedupGo_notin_seen as (a :: seen) e he' p (List.mem_cons_of_mem _ hp)

/-- `dedupGo` output is pairwise key-distinct. -/
private theorem dedupGo_pairwise :
    ∀ (l seen : List FlatTMTransEntry),
      (dedupGo seen l).Pairwise (fun e1 e2 => sameKey e1 e2 = false)
  | [], _ => by simp [dedupGo]
  | a :: as, seen => by
      simp only [dedupGo]
      by_cases hany : seen.any (fun q => sameKey q a) = true
      · rw [if_pos hany]
        exact dedupGo_pairwise as seen
      · rw [if_neg hany]
        refine List.pairwise_cons.2 ⟨?_, dedupGo_pairwise as (a :: seen)⟩
        intro e he
        exact dedupGo_notin_seen as (a :: seen) e he a List.mem_cons_self

private theorem normTrans_pairwise (M : FlatTM) :
    (normTrans M).Pairwise (fun e1 e2 => sameKey e1 e2 = false) :=
  List.Pairwise.sublist List.filter_sublist (dedupGo_pairwise M.trans [])

/-- In a key-pairwise-distinct list, a matching member IS the `find?` result
(an earlier matcher would share its key). -/
private theorem find?_eq_of_pairwise (cfg : FlatTMConfig) :
    ∀ (l : List FlatTMTransEntry),
      l.Pairwise (fun e1 e2 => sameKey e1 e2 = false) →
      ∀ e ∈ l, entryMatchesConfig e cfg = true →
      l.find? (fun e' => entryMatchesConfig e' cfg) = some e
  | [] => by intro _ e he; simp at he
  | a :: as => by
      intro hpw e he hP
      rcases List.mem_cons.1 he with rfl | he'
      · rw [List.find?_cons_of_pos (p := fun e' => entryMatchesConfig e' cfg) hP]
      · have hkey := (List.pairwise_cons.1 hpw).1 e he'
        have hane : entryMatchesConfig a cfg = false := by
          by_contra hcon
          rw [Bool.not_eq_false] at hcon
          rw [sameKey_of_matches hcon hP] at hkey
          simp at hkey
        rw [List.find?_cons_of_neg (by simp [hane])]
        exact find?_eq_of_pairwise cfg as (List.pairwise_cons.1 hpw).2 e he' hP

/-- The normalised table's `find?` returns a given matching member. -/
private theorem normTrans_find?_eq (M : FlatTM) (cfg : FlatTMConfig)
    {e : FlatTMTransEntry} (he : e ∈ normTrans M)
    (hP : entryMatchesConfig e cfg = true) :
    (normTrans M).find? (fun e' => entryMatchesConfig e' cfg) = some e :=
  find?_eq_of_pairwise cfg (normTrans M) (normTrans_pairwise M) e he hP

/-- `stateOf` is injective below the state bound. -/
private theorem stateOf_inj_lt (M : FlatTM) {a b : Nat} (ha : a < M.states)
    (hb : b < M.states) (h : stateOf M a = stateOf M b) : a = b := by
  have hv := congrArg Fin.val h
  simp only [stateOf] at hv
  rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)] at hv
  exact hv

/-- `optSym` is injective on alphabet-valid option symbols (a valid
`some v` has `v < M.sig`, so it never collides with the blank). -/
private theorem optSym_inj_valid (M : FlatTM) {m m' : Option Nat}
    (hm : ∀ v, m = some v → v < M.sig)
    (hm' : ∀ v, m' = some v → v < M.sig)
    (h : optSym M m = optSym M m') : m = m' := by
  have hv := congrArg Fin.val h
  cases m with
  | none =>
    cases m' with
    | none => rfl
    | some v =>
      exfalso
      have hv' : v < M.sig := hm' v rfl
      simp only [optSym, blankSym, symOf] at hv
      rw [Nat.min_eq_left (by omega)] at hv
      omega
  | some u =>
    cases m' with
    | none =>
      exfalso
      have hu : u < M.sig := hm u rfl
      simp only [optSym, blankSym, symOf] at hv
      rw [Nat.min_eq_left (by omega)] at hv
      omega
    | some v =>
      have hu : u < M.sig := hm u rfl
      have hv' : v < M.sig := hm' v rfl
      simp only [optSym, symOf] at hv
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)] at hv
      exact congrArg some hv

/-! Coordinate pinning: the successor row's cells, one class at a time. -/

/-- Coordinate 0 of a covered successor is the left boundary marker. -/
private theorem validStep_zero (M : FlatTM) {cfg : FlatTMConfig} {n : Nat}
    {b : List (Fin (Sg M))} (hn : 1 ≤ n)
    (hvs : TCC.validStep (cookCards M) (confRow M cfg n) b) :
    b[0]? = some (bCell M) := by
  obtain ⟨card, hmem, ⟨hp1, -, -⟩, ⟨hc1, -, -⟩⟩ :=
    window_card M hvs (i := 0) (by omega)
  have hb : card.prem.cardEl1 = bCell M := by
    rw [hp1]
    unfold rowCellM
    rw [if_neg (by omega)]
    exact rowCell_zero M cfg
  rw [hc1, card_bfirst M hmem hb]

/-- The last coordinate (`n + 1`) of a covered successor is the right
marker (via `card_blast` — the phantom-head fix pays here). -/
private theorem validStep_last (M : FlatTM) {cfg : FlatTMConfig} {n : Nat}
    {b : List (Fin (Sg M))} (hn : 1 ≤ n)
    (hvs : TCC.validStep (cookCards M) (confRow M cfg n) b) :
    b[n + 1]? = some (bCell M) := by
  obtain ⟨card, hmem, ⟨-, -, hp3⟩, ⟨-, -, hc3⟩⟩ :=
    window_card M hvs (i := n - 1) (by omega)
  rw [show n - 1 + 2 = n + 1 from by omega] at hp3 hc3
  have hb : card.prem.cardEl3 = bCell M := by
    rw [hp3]
    unfold rowCellM
    rw [if_pos rfl]
  rw [hc3, card_blast M hmem hb, hb]

/-- **Stage (iii): no spurious changes away from the head.** A coordinate
outside the head's three-coordinate neighbourhood keeps its cell (the middle
slot of its head-free window, `card_headfree_middle`). -/
private theorem validStep_away (M : FlatTM) {cfg : FlatTMConfig} {n : Nat}
    {b : List (Fin (Sg M))}
    (hvs : TCC.validStep (cookCards M) (confRow M cfg n) b)
    {j : Nat} (h1 : 1 ≤ j) (hjn : j ≤ n)
    (hj1 : j ≠ cfgHead cfg) (hj2 : j ≠ cfgHead cfg + 1)
    (hj3 : j ≠ cfgHead cfg + 2) :
    b[j]? = some (rowCell M cfg j) := by
  obtain ⟨card, hmem, ⟨hp1, hp2, hp3⟩, ⟨-, hc2, -⟩⟩ :=
    window_card M hvs (i := j - 1) (by omega)
  rw [show j - 1 + 1 = j from by omega] at hp2 hc2
  rw [show j - 1 + 2 = j + 1 from by omega] at hp3
  have hmid := card_headfree_middle M hmem
    (fun q d => by rw [hp1]; exact rowCellM_ne_hCell M cfg (by omega) q d)
    (fun q d => by rw [hp2]; exact rowCellM_ne_hCell M cfg (by omega) q d)
    (fun q d => by rw [hp3]; exact rowCellM_ne_hCell M cfg (by omega) q d)
  rw [hc2, hmid, hp2]
  unfold rowCellM
  rw [if_neg (by omega)]

/-- Assemble a successor row from its pinned cells. -/
private theorem eq_confRow_of_cells (M : FlatTM) (cfg' : FlatTMConfig) {n : Nat}
    {b : List (Fin (Sg M))} (hlen : b.length = n + 2)
    (hcells : ∀ j, j < n + 2 → b[j]? = some (rowCellM M cfg' n j)) :
    b = confRow M cfg' n := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n + 2
  · rw [hcells j hj, List.getElem?_eq_getElem (by rw [confRow_length]; omega),
      confRow_getElem' M cfg' (by rw [confRow_length]; omega)]
  · rw [List.getElem?_eq_none (by omega),
      List.getElem?_eq_none (by rw [confRow_length]; omega)]

/-- **The (1b) assembly scaffold.** Given the three head-neighbourhood cells
of the successor row (as `rowCell` of a candidate successor configuration
whose head moved at most one coordinate and whose tape agrees away from the
source head), every other coordinate is pinned by
`validStep_zero`/`validStep_last`/`validStep_away`, so the covered row IS
the candidate's row. -/
private theorem assemble_row (M : FlatTM) {cfg : FlatTMConfig} {n : Nat}
    {b : List (Fin (Sg M))}
    (hvs : TCC.validStep (cookCards M) (confRow M cfg n) b)
    (hlenB : b.length = n + 2)
    (hhead : cfgHead cfg + 4 ≤ n)
    (cfgN : FlatTMConfig)
    (hBhd1 : cfgHead cfgN ≤ cfgHead cfg + 1)
    (hBhd2 : cfgHead cfg ≤ cfgHead cfgN + 1)
    (hsym : ∀ p, p ≠ cfgHead cfg →
      tapeSymAt M (cfgRight cfgN) p = tapeSymAt M (cfgRight cfg) p)
    (hA : b[cfgHead cfg]? = some (rowCell M cfgN (cfgHead cfg)))
    (hB : b[cfgHead cfg + 1]? = some (rowCell M cfgN (cfgHead cfg + 1)))
    (hC : b[cfgHead cfg + 2]? = some (rowCell M cfgN (cfgHead cfg + 2))) :
    b = confRow M cfgN n := by
  refine eq_confRow_of_cells M cfgN hlenB ?_
  intro j hj
  by_cases hj0 : j = 0
  · subst hj0
    rw [validStep_zero M (by omega) hvs]
    unfold rowCellM
    rw [if_neg (by omega), rowCell_zero]
  by_cases hjlast : j = n + 1
  · subst hjlast
    rw [validStep_last M (by omega) hvs]
    unfold rowCellM
    rw [if_pos rfl]
  by_cases hjA : j = cfgHead cfg
  · subst hjA
    rw [hA]
    unfold rowCellM
    rw [if_neg (by omega)]
  by_cases hjB : j = cfgHead cfg + 1
  · subst hjB
    rw [hB]
    unfold rowCellM
    rw [if_neg (by omega)]
  by_cases hjC : j = cfgHead cfg + 2
  · subst hjC
    rw [hC]
    unfold rowCellM
    rw [if_neg (by omega)]
  · rw [validStep_away M hvs (by omega) (by omega) hjA hjB hjC]
    unfold rowCellM
    rw [if_neg hjlast,
      rowCell_tape M cfg (j := j) (by omega) (by omega),
      rowCell_tape M cfgN (j := j) (by omega) (by omega),
      hsym (j - 1) (by omega)]

/-- **(1b) Card completeness — the inversion heart (PROVEN 2026-07-18-d).**
Any card-covered successor of a *configuration row* is forced: the frozen
row itself when halting, `confRow` of *the* unique machine step otherwise.
Proof structure:
(i) every window not containing the head has an all-tape/boundary premise,
and the only conclusions available off such premises keep the cells
(copy) or place a head at the first (Rmove-in) / third (Lmove-in) slot —
there is **no head-at-second-slot family**, so a head in `b` adjacent only
to unchanged tape cells on both sides is impossible; an Lmove-in head at
the row's LAST cell (the one cell with no second refuting window) is
blocked by the right marker: the last window's premise third slot is
`bCell`, which no `stepCardInL` premise carries and only `copyRightCards`
(cell-preserving) covers — hence `b` has no head away from the source
head's three-cell neighbourhood; (ii) the center
window's premise `(x, hCell q R, z)` matches only cards of entries keyed
`(q, m)` — unique after `normTrans` — or halt-freeze cards, never both
(`normTrans` drops halting sources); (iii) the matched card's conclusion
plus the overlapping windows determine every cell of `b` as `confRow` of
the stepped configuration (`wEff` matching `writeCurrentTapeSymbol` via the
frontier ⟺ blank-left-neighbour correspondence); (iv) if no entry matches
(stuck) no card covers the center window, contradicting `hvs`. -/
theorem step_of_validStep (M : FlatTM) (n : Nat) {base t : Nat}
    {cfg : FlatTMConfig}
    (hV : validFlatTM M) (hfit : ConfFits M base t cfg)
    (hhead : cfgHead cfg + 4 ≤ n)
    (_hlen : (cfgRight cfg).length + 2 ≤ n)
    (b : List (Fin (Sg M)))
    (hvs : TCC.validStep (cookCards M) (confRow M cfg n) b) :
    (haltingStateReached M cfg = true ∧ b = confRow M cfg n) ∨
    (haltingStateReached M cfg = false ∧
      ∃ cfg', stepFlatTM M cfg = some cfg' ∧ b = confRow M cfg' n) := by
  have hstate := hfit.state_lt
  have hlenB : b.length = n + 2 := by
    have hl := hvs.1
    rw [confRow_length] at hl
    omega
  -- the center window and its card
  obtain ⟨cc, hccMem, ⟨hp1, hp2, hp3⟩, ⟨hc1, hc2, hc3⟩⟩ :=
    window_card M hvs (i := cfgHead cfg) (by omega)
  have hp1' : cc.prem.cardEl1 = xCell M (rowX M cfg (cfgHead cfg)) := by
    rw [hp1]
    unfold rowCellM
    rw [if_neg (by omega), rowCell_x M cfg (j := cfgHead cfg) (by omega)]
  have hp2' : cc.prem.cardEl2
      = hCell M (stateOf M cfg.state_idx)
          (tapeSymAt M (cfgRight cfg) (cfgHead cfg)) := by
    rw [hp2]
    unfold rowCellM
    rw [if_neg (by omega), rowCell_head M cfg (j := cfgHead cfg + 1) rfl]
  have hp3' : cc.prem.cardEl3
      = tCell M (tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1)) := by
    rw [hp3]
    unfold rowCellM
    rw [if_neg (by omega),
      rowCell_tape M cfg (j := cfgHead cfg + 2) (by omega) (by omega)]
    simp only [show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega]
  rcases card_head_center M hccMem hp2' with ⟨hqhalt, hcp⟩ |
    ⟨e, heN, x, z, hqe, hRe, hcc, hpx, hpz⟩
  · -- HALTING: the freeze card keeps the row
    left
    have hsv : (stateOf M cfg.state_idx).1 = cfg.state_idx := by
      simp [stateOf]; omega
    have hhalt : haltingStateReached M cfg = true := by
      unfold haltingStateReached
      rw [← hsv]
      exact hqhalt
    have hA : b[cfgHead cfg]? = some (rowCell M cfg (cfgHead cfg)) := by
      rw [hc1, hcp, hp1]
      unfold rowCellM
      rw [if_neg (by omega)]
    have hB : b[cfgHead cfg + 1]? = some (rowCell M cfg (cfgHead cfg + 1)) := by
      rw [hc2, hcp, hp2]
      unfold rowCellM
      rw [if_neg (by omega)]
    have hC : b[cfgHead cfg + 2]? = some (rowCell M cfg (cfgHead cfg + 2)) := by
      rw [hc3, hcp, hp3]
      unfold rowCellM
      rw [if_neg (by omega)]
    exact ⟨hhalt, assemble_row M hvs hlenB hhead cfg (by omega) (by omega)
      (fun p _ => rfl) hA hB hC⟩
  · -- STEP: the center card's entry is the (unique) fired transition
    right
    have heM : e ∈ M.trans := normTrans_subset M e heN
    have hvalid := hV.2.2 e heM
    have hOK : entryOK M e = true := (List.mem_filter.1 heN).2
    simp only [entryOK, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at hOK
    obtain ⟨⟨⟨hsrcLen, hdstLen⟩, hmvLen⟩, hnhE⟩ := hOK
    obtain ⟨m0, hm0⟩ := List.length_eq_one_iff.1 hsrcLen
    obtain ⟨w0, hw0⟩ := List.length_eq_one_iff.1 hdstLen
    obtain ⟨mv0, hmv0⟩ := List.length_eq_one_iff.1 hmvLen
    have hmhead : e.src_tape_vals.headD none = m0 := by rw [hm0]; rfl
    have hwhead : e.dst_write_vals.headD none = w0 := by rw [hw0]; rfl
    have hmvhead : e.move_dirs.headD TMMove.Nmove = mv0 := by rw [hmv0]; rfl
    -- the card's read is the machine's read (valid symbols only)
    have hm0valid : ∀ v, m0 = some v → v < M.sig := by
      intro v hv
      have hb := hvalid.2.2.2.2.2.1 m0
        (by rw [hm0]; exact List.mem_singleton.2 rfl)
      rw [hv] at hb
      exact hb
    have hreadvalid : ∀ v,
        currentTapeSymbol ([], cfgHead cfg, cfgRight cfg) = some v →
        v < M.sig := by
      intro v hcur
      simp only [currentTapeSymbol] at hcur
      split at hcur
      · have hv := Option.some.inj hcur
        rw [← hv]
        exact hfit.syms_lt _ (List.get_mem _ _)
      · exact absurd hcur (by simp)
    have hR' : optSym M m0
        = optSym M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) := by
      rw [← hmhead, hRe, tapeSymAt_head M [] (cfgRight cfg) (cfgHead cfg)]
    have hm0read : m0 = currentTapeSymbol ([], cfgHead cfg, cfgRight cfg) :=
      optSym_inj_valid M hm0valid hreadvalid hR'
    -- the card's source state is the machine's state; it is non-halting
    have hsrcEq : e.src_state = cfg.state_idx :=
      stateOf_inj_lt M hvalid.1 hstate hqe
    have hnh : haltingStateReached M cfg = false := by
      unfold haltingStateReached
      rw [← hsrcEq]
      exact hnhE
    -- the entry matches and fires
    have hmatch : entryMatchesConfig e cfg = true := by
      simp only [entryMatchesConfig, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      refine ⟨hsrcEq, ?_⟩
      rw [hfit.tapes_eq, hm0]
      simp only [List.map_cons, List.map_nil]
      rw [hm0read]
    have h1tape : cfg.tapes.length = 1 := by rw [hfit.tapes_eq]; rfl
    have happly : applyTransitionEntry cfg e
        = some ⟨e.dst_state,
            [tapeStep ([], cfgHead cfg, cfgRight cfg) w0 mv0]⟩ := by
      unfold applyTransitionEntry
      rw [dif_pos ⟨by rw [h1tape, hw0]; rfl, by rw [h1tape, hmv0]; rfl⟩]
      rw [hfit.tapes_eq, hw0, hmv0]
      rfl
    have hstepN : stepFlatTM (normM M) cfg
        = some ⟨e.dst_state,
            [tapeStep ([], cfgHead cfg, cfgRight cfg) w0 mv0]⟩ := by
      show ((normM M).trans.find? (fun e' => entryMatchesConfig e' cfg)).bind
        (applyTransitionEntry cfg) = _
      rw [show (normM M).trans = normTrans M from rfl,
        normTrans_find?_eq M cfg heN hmatch]
      exact happly
    have hstep : stepFlatTM M cfg
        = some ⟨e.dst_state,
            [tapeStep ([], cfgHead cfg, cfgRight cfg) w0 mv0]⟩ := by
      rw [← stepFlatTM_normM M cfg h1tape hnh]
      exact hstepN
    -- the write effect
    have hwbound := hvalid.2.2.2.2.2.2 w0
      (by rw [hw0]; exact List.mem_singleton.2 rfl)
    obtain ⟨wr, hwt, hlen1, hlen2, hsyms, hunch, hwrhd⟩ :=
      write_facts M (cfgHead cfg) (cfgRight cfg) w0 hfit.syms_lt hwbound
    -- pin the card's window context to the row
    have hxx : x = rowX M cfg (cfgHead cfg) :=
      xCell_inj M (by rw [← hpx, hp1'])
    have hzz : z = tapeSymAt M (cfgRight cfg) (cfgHead cfg + 1) :=
      tCell_inj M (by rw [← hpz, hp3'])
    have hxbC : xIsBlank M x = decide ((cfgRight cfg).length < cfgHead cfg) := by
      rw [hxx]
      exact rowX_isBlank M cfg hfit.syms_lt
    have hW : wEff M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w0
        (xIsBlank M x) = tapeSymAt M wr (cfgHead cfg) := by
      rw [hxbC, hwrhd]
    rw [hmhead, hwhead, hmvhead, hm0read] at hcc
    cases mv0 with
    | Nmove =>
      have htape : tapeStep ([], cfgHead cfg, cfgRight cfg) w0 TMMove.Nmove
          = ([], cfgHead cfg, wr) := by
        simp [tapeStep, moveTapeHead, hwt]
      refine ⟨hnh, ⟨e.dst_state,
        [tapeStep ([], cfgHead cfg, cfgRight cfg) w0 TMMove.Nmove]⟩, hstep, ?_⟩
      rw [htape]
      set cfgN : FlatTMConfig := ⟨e.dst_state, [([], cfgHead cfg, wr)]⟩
        with hcfgN
      have hBhd : cfgHead cfgN = cfgHead cfg := rfl
      have hBright : cfgRight cfgN = wr := rfl
      have hBst : cfgN.state_idx = e.dst_state := rfl
      have hrowXeq : ∀ jj, jj ≠ cfgHead cfg + 1 →
          rowX M cfgN jj = rowX M cfg jj := by
        intro jj hjj
        unfold rowX
        by_cases hz : jj = 0
        · rw [if_pos hz, if_pos hz]
        · rw [if_neg hz, if_neg hz, hBright, hunch (jj - 1) (by omega)]
      have hA : b[cfgHead cfg]? = some (rowCell M cfgN (cfgHead cfg)) := by
        rw [hc1, show cc.conc.cardEl1 = xCell M x from (by rw [hcc]; rfl),
          hxx, ← hrowXeq (cfgHead cfg) (by omega),
          ← rowCell_x M cfgN (j := cfgHead cfg) (by omega)]
      have hB : b[cfgHead cfg + 1]? = some (rowCell M cfgN (cfgHead cfg + 1)) := by
        rw [hc2, show cc.conc.cardEl2 = hCell M (stateOf M e.dst_state)
              (wEff M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w0
                (xIsBlank M x)) from (by rw [hcc]; rfl),
          hW, rowCell_head M cfgN (j := cfgHead cfg + 1) (by rw [hBhd]),
          hBst, hBright, hBhd]
      have hC : b[cfgHead cfg + 2]? = some (rowCell M cfgN (cfgHead cfg + 2)) := by
        rw [hc3, show cc.conc.cardEl3 = tCell M z from (by rw [hcc]; rfl), hzz,
          rowCell_tape M cfgN (j := cfgHead cfg + 2) (by omega)
            (by omega),
          hBright]
        simp only [show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega]
        rw [hunch (cfgHead cfg + 1) (by omega)]
      exact assemble_row M hvs hlenB hhead cfgN (by omega)
        (by omega)
        (fun p hp => by rw [hBright]; exact hunch p hp) hA hB hC
    | Rmove =>
      have htape : tapeStep ([], cfgHead cfg, cfgRight cfg) w0 TMMove.Rmove
          = ([], cfgHead cfg + 1, wr) := by
        simp [tapeStep, moveTapeHead, hwt]
      refine ⟨hnh, ⟨e.dst_state,
        [tapeStep ([], cfgHead cfg, cfgRight cfg) w0 TMMove.Rmove]⟩, hstep, ?_⟩
      rw [htape]
      set cfgN : FlatTMConfig := ⟨e.dst_state, [([], cfgHead cfg + 1, wr)]⟩
        with hcfgN
      have hBhd : cfgHead cfgN = cfgHead cfg + 1 := rfl
      have hBright : cfgRight cfgN = wr := rfl
      have hBst : cfgN.state_idx = e.dst_state := rfl
      have hrowXeq : ∀ jj, jj ≠ cfgHead cfg + 1 →
          rowX M cfgN jj = rowX M cfg jj := by
        intro jj hjj
        unfold rowX
        by_cases hz : jj = 0
        · rw [if_pos hz, if_pos hz]
        · rw [if_neg hz, if_neg hz, hBright, hunch (jj - 1) (by omega)]
      have hA : b[cfgHead cfg]? = some (rowCell M cfgN (cfgHead cfg)) := by
        rw [hc1, show cc.conc.cardEl1 = xCell M x from (by rw [hcc]; rfl),
          hxx, ← hrowXeq (cfgHead cfg) (by omega),
          ← rowCell_x M cfgN (j := cfgHead cfg) (by omega)]
      have hB : b[cfgHead cfg + 1]? = some (rowCell M cfgN (cfgHead cfg + 1)) := by
        rw [hc2, show cc.conc.cardEl2 = tCell M
              (wEff M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w0
                (xIsBlank M x)) from (by rw [hcc]; rfl),
          hW, rowCell_tape M cfgN (j := cfgHead cfg + 1) (by omega)
            (by omega),
          hBright]
        simp only [show cfgHead cfg + 1 - 1 = cfgHead cfg from by omega]
      have hC : b[cfgHead cfg + 2]? = some (rowCell M cfgN (cfgHead cfg + 2)) := by
        rw [hc3, show cc.conc.cardEl3 = hCell M (stateOf M e.dst_state) z
              from (by rw [hcc]; rfl),
          hzz, rowCell_head M cfgN (j := cfgHead cfg + 2) (by rw [hBhd]),
          hBst, hBright, hBhd, hunch (cfgHead cfg + 1) (by omega)]
      exact assemble_row M hvs hlenB hhead cfgN (by omega)
        (by omega)
        (fun p hp => by rw [hBright]; exact hunch p hp) hA hB hC
    | Lmove =>
      have htape : tapeStep ([], cfgHead cfg, cfgRight cfg) w0 TMMove.Lmove
          = ([], cfgHead cfg - 1, wr) := by
        simp [tapeStep, moveTapeHead, hwt]
      refine ⟨hnh, ⟨e.dst_state,
        [tapeStep ([], cfgHead cfg, cfgRight cfg) w0 TMMove.Lmove]⟩, hstep, ?_⟩
      rw [htape]
      set cfgN : FlatTMConfig := ⟨e.dst_state, [([], cfgHead cfg - 1, wr)]⟩
        with hcfgN
      have hBhd : cfgHead cfgN = cfgHead cfg - 1 := rfl
      have hBright : cfgRight cfgN = wr := rfl
      have hBst : cfgN.state_idx = e.dst_state := rfl
      cases x with
      | none =>
        -- the clamp: the boundary marker is the left context, so the head
        -- is at tape position 0 and stays there
        have h0 : cfgHead cfg = 0 := by
          by_contra h0
          unfold rowX at hxx
          rw [if_neg h0] at hxx
          simp at hxx
        have hBhd' : cfgHead cfgN = cfgHead cfg := by rw [hBhd]; omega
        have hA : b[cfgHead cfg]? = some (rowCell M cfgN (cfgHead cfg)) := by
          rw [hc1, show cc.conc.cardEl1 = bCell M from (by rw [hcc]; rfl), h0,
            rowCell_zero]
        have hB : b[cfgHead cfg + 1]?
            = some (rowCell M cfgN (cfgHead cfg + 1)) := by
          rw [hc2, show cc.conc.cardEl2 = hCell M (stateOf M e.dst_state)
                (wEff M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w0
                  (xIsBlank M none)) from (by rw [hcc]; rfl),
            hW, rowCell_head M cfgN (j := cfgHead cfg + 1) (by rw [hBhd']),
            hBst, hBright, hBhd']
        have hC : b[cfgHead cfg + 2]?
            = some (rowCell M cfgN (cfgHead cfg + 2)) := by
          rw [hc3, show cc.conc.cardEl3 = tCell M z from (by rw [hcc]; rfl), hzz,
            rowCell_tape M cfgN (j := cfgHead cfg + 2) (by omega)
              (by omega),
            hBright]
          simp only [show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega]
          rw [hunch (cfgHead cfg + 1) (by omega)]
        exact assemble_row M hvs hlenB hhead cfgN (by omega)
          (by omega)
          (fun p hp => by rw [hBright]; exact hunch p hp) hA hB hC
      | some a0 =>
        -- interior left move: the head enters coordinate `cfgHead cfg`
        have hne0 : cfgHead cfg ≠ 0 := by
          intro h0
          rw [h0] at hxx
          unfold rowX at hxx
          rw [if_pos rfl] at hxx
          simp at hxx
        have ha0 : a0 = tapeSymAt M (cfgRight cfg) (cfgHead cfg - 1) := by
          unfold rowX at hxx
          rw [if_neg hne0] at hxx
          exact Option.some.inj hxx
        have hA : b[cfgHead cfg]? = some (rowCell M cfgN (cfgHead cfg)) := by
          rw [hc1, show cc.conc.cardEl1
                = hCell M (stateOf M e.dst_state) a0 from (by rw [hcc]; rfl),
            ha0, rowCell_head M cfgN (j := cfgHead cfg) (by omega),
            hBst, hBright, hBhd, hunch (cfgHead cfg - 1) (by omega)]
        have hB : b[cfgHead cfg + 1]?
            = some (rowCell M cfgN (cfgHead cfg + 1)) := by
          rw [hc2, show cc.conc.cardEl2 = tCell M
                (wEff M (currentTapeSymbol ([], cfgHead cfg, cfgRight cfg)) w0
                  (xIsBlank M (some a0))) from (by rw [hcc]; rfl),
            hW, rowCell_tape M cfgN (j := cfgHead cfg + 1) (by omega)
              (by omega),
            hBright]
          simp only [show cfgHead cfg + 1 - 1 = cfgHead cfg from by omega]
        have hC : b[cfgHead cfg + 2]?
            = some (rowCell M cfgN (cfgHead cfg + 2)) := by
          rw [hc3, show cc.conc.cardEl3 = tCell M z from (by rw [hcc]; rfl), hzz,
            rowCell_tape M cfgN (j := cfgHead cfg + 2) (by omega)
              (by omega),
            hBright]
          simp only [show cfgHead cfg + 2 - 1 = cfgHead cfg + 1 from by omega]
          rw [hunch (cfgHead cfg + 1) (by omega)]
        exact assemble_row M hvs hlenB hhead cfgN (by omega)
          (by omega)
          (fun p hp => by rw [hBright]; exact hunch p hp) hA hB hC

/-- A halting configuration's row satisfies the final patterns: the head
cell `hCell (stateOf q) (…)` occurs at row coordinate `cfgHead cfg + 1 ≤ n`,
and `stateOf` is the identity under `state_lt`. -/
theorem satFinal_of_halt (M : FlatTM) (n : Nat) {base t : Nat}
    {cfg : FlatTMConfig}
    (hfit : ConfFits M base t cfg)
    (hhead : cfgHead cfg < n)
    (hh : haltingStateReached M cfg = true) :
    TCC.satFinal (cookFinal M) (confRow M cfg n) := by
  have hstate := hfit.state_lt
  have hq : M.halt.getD (stateOf M cfg.state_idx).1 false = true := by
    have hqv : (stateOf M cfg.state_idx).1 = cfg.state_idx := by
      simp [stateOf]; omega
    rw [hqv]; exact hh
  refine ⟨[hCell M (stateOf M cfg.state_idx)
      (tapeSymAt M (cfgRight cfg) (cfgHead cfg))], ?_, ?_⟩
  · unfold cookFinal
    refine List.mem_flatMap.2 ⟨stateOf M cfg.state_idx, List.mem_finRange _, ?_⟩
    rw [if_pos hq]
    exact List.mem_map.2 ⟨_, List.mem_finRange _, rfl⟩
  · -- the head cell sits at list index `cfgHead cfg + 1`
    have hlt : cfgHead cfg + 1 < (confRow M cfg n).length := by
      rw [confRow_length]; omega
    refine ⟨(confRow M cfg n).take (cfgHead cfg + 1),
      (confRow M cfg n).drop (cfgHead cfg + 1 + 1), ?_⟩
    have h1 : confRow M cfg n
        = (confRow M cfg n).take (cfgHead cfg + 1)
          ++ (confRow M cfg n).drop (cfgHead cfg + 1) :=
      (List.take_append_drop _ _).symm
    rw [List.drop_eq_getElem_cons hlt,
      confRow_getElem M cfg (by omega) hlt, rowCell_head M cfg rfl] at h1
    conv_lhs => rw [h1]
    simp

/-- Only halting rows satisfy the final patterns: a final pattern is a
singleton halting head cell; head-cell codes are disjoint from tape and
boundary codes (the cell-code algebra), so its occurrence in `confRow` must
be the head cell, whose state is `stateOf cfg.state_idx = cfg.state_idx` by
`state_lt`. -/
theorem halt_of_satFinal (M : FlatTM) (n : Nat) {base t : Nat}
    {cfg : FlatTMConfig}
    (hfit : ConfFits M base t cfg)
    (hfin : TCC.satFinal (cookFinal M) (confRow M cfg n)) :
    haltingStateReached M cfg = true := by
  obtain ⟨subs, hmem, left, right, heq⟩ := hfin
  -- unpack the final pattern: a singleton halting head cell
  unfold cookFinal at hmem
  obtain ⟨q, -, hq⟩ := List.mem_flatMap.1 hmem
  cases hhalt : M.halt.getD q.1 false with
  | false => rw [hhalt] at hq; simp at hq
  | true =>
    rw [hhalt] at hq
    simp only [if_true] at hq
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hq
    -- the pattern cell occurs at row coordinate `left.length ≤ n + 1`
    have hlen : (confRow M cfg n).length = n + 2 := confRow_length M cfg n
    have hlen2 : left.length + (1 + right.length) = n + 2 := by
      have hl := congrArg List.length heq
      simp [hlen, List.length_append] at hl
      omega
    have hlt : left.length < (confRow M cfg n).length := by omega
    have hget? : (confRow M cfg n)[left.length]? = some (hCell M q b) := by
      rw [heq, List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self]
      rfl
    by_cases hlastc : left.length = n + 1
    · -- the last cell is the right marker, never a head cell
      exfalso
      rw [hlastc] at hget?
      rw [List.getElem?_eq_getElem (by omega), confRow_getElem_last M cfg] at hget?
      exact hCell_ne_bCell M q b (Option.some.inj hget?).symm
    have hle : left.length ≤ n := by omega
    have hrow : rowCell M cfg left.length = hCell M q b := by
      rw [List.getElem?_eq_getElem hlt] at hget?
      have hg := Option.some.inj hget?
      rw [confRow_getElem M cfg hle hlt] at hg
      exact hg
    -- classify the coordinate by the code bands
    by_cases h0 : left.length = 0
    · exfalso
      rw [h0, rowCell_zero] at hrow
      exact hCell_ne_bCell M q b hrow.symm
    by_cases hhd : left.length = cfgHead cfg + 1
    · -- the head cell: its state is halting
      rw [rowCell_head M cfg hhd] at hrow
      obtain ⟨hq', -⟩ := hCell_inj M hrow
      have hsv : (stateOf M cfg.state_idx).1 = cfg.state_idx := by
        have hstate := hfit.state_lt
        simp [stateOf]; omega
      have hqv : cfg.state_idx = q.1 := by
        rw [← hsv, hq']
      unfold haltingStateReached
      rw [hqv]
      exact hhalt
    · -- a tape cell cannot carry a head code
      exfalso
      rw [rowCell_tape M cfg (by omega) hhd] at hrow
      exact tCell_ne_hCell M _ b q hrow

/-- A single valid single-tape input. -/
theorem isValidFlatTapes_single (M : FlatTM) (s : List Nat)
    (hT : M.tapes = 1) (hs : list_ofFlatType M.sig s) :
    isValidFlatTapes M [s] = true := by
  unfold isValidFlatTapes
  simp only [List.length_singleton, hT, decide_true, List.all_cons, List.all_nil,
    Bool.and_true, Bool.true_and, isValidFlatTape, List.all_eq_true,
    decide_eq_true_eq]
  exact fun x hx => hs x hx

/-- **Run transport (the (2) induction).** A `k`-step machine run out of a
fitting configuration transports to a `k`-row card-covered chain: a halting
configuration freezes (`validStep_of_halt`), a live one advances
(`validStep_of_step`), and a stuck non-halting one ends the run non-halting
(no chain needed — the hypothesis `haltingStateReached cfg_f` is refuted).
The window-room invariants `t + k + 3 ≤ n` / `base + t + k + 3 ≤ n` are
preserved as `t` grows while `k` shrinks. -/
theorem relpower_of_run (M : FlatTM) (n : Nat) {base : Nat} (hV : validFlatTM M) :
    ∀ (k t : Nat) (cfg cfg_f : FlatTMConfig),
      ConfFits M base t cfg →
      t + k + 3 ≤ n →
      base + t + k + 3 ≤ n →
      runFlatTM k M cfg = some cfg_f →
      haltingStateReached M cfg_f = true →
      relpower (TCC.validStep (cookCards M)) k (confRow M cfg n) (confRow M cfg_f n) ∧
        ConfFits M base (t + k) cfg_f
  | 0, t, cfg, cfg_f, hfit, _hn, _hbn, hrun, _hh => by
      cases Option.some.inj hrun
      exact ⟨relpower.refl _, hfit⟩
  | k + 1, t, cfg, cfg_f, hfit, hn, hbn, hrun, hh => by
      have hhead3 : cfgHead cfg + 3 ≤ n := by
        have := hfit.head_le; omega
      by_cases hhalt : haltingStateReached M cfg = true
      · -- halted: the row freezes for the whole remaining budget
        have hfrz : runFlatTM (k + 1) M cfg = some cfg :=
          runFlatTM_of_halting M cfg (k + 1) hhalt
        rw [hrun] at hfrz
        cases Option.some.inj hfrz
        obtain ⟨hrel, hfit'⟩ := relpower_of_run M n hV k (t + 1) cfg cfg
          (ConfFits_mono M (Nat.le_succ t) hfit) (by omega) (by omega)
          (runFlatTM_of_halting M cfg k hhalt) hh
        exact ⟨relpower.step (validStep_of_halt M n hfit hhead3 hhalt) hrel,
          ConfFits_mono M (by omega) hfit'⟩
      · have hnh : haltingStateReached M cfg = false := by
          rwa [Bool.not_eq_true] at hhalt
        have hrunEq : runFlatTM (k + 1) M cfg
            = (match stepFlatTM M cfg with
               | none => some cfg
               | some cfg' => runFlatTM k M cfg') := by
          show (if haltingStateReached M cfg = true then some cfg else _) = _
          rw [if_neg hhalt]
          rfl
        cases hstep : stepFlatTM M cfg with
        | none =>
            -- stuck non-halting: the run ends non-halting, refuting `hh`
            rw [hstep] at hrunEq
            rw [hrunEq] at hrun
            cases Option.some.inj hrun
            simp [hnh] at hh
        | some cfg' =>
            rw [hstep] at hrunEq
            rw [hrunEq] at hrun
            have hhead4 : cfgHead cfg + 4 ≤ n := by
              have := hfit.head_le; omega
            have hlen2 : (cfgRight cfg).length + 2 ≤ n := by
              have := hfit.len_le; omega
            obtain ⟨hrel, hfitf⟩ := relpower_of_run M n hV k (t + 1) cfg' cfg_f
              (ConfFits_step M hV hfit hstep) (by omega) (by omega) hrun hh
            exact ⟨relpower.step
                (validStep_of_step M n hV hfit hhead4 hlen2 hnh hstep) hrel,
              ConfFits_mono M (by omega) hfitf⟩

/-- **(2) Run ⟹ covering**: an accepting run yields a covering of exactly
`steps` rows — `relpower_of_run` from the initial configuration
(`ConfFits_init`), closed by `satFinal_of_halt` on the final row. -/
theorem cover_of_run (M : FlatTM) (s : List Nat) (steps : Nat)
    (hV : validFlatTM M) (hT : M.tapes = 1) (hs : list_ofFlatType M.sig s)
    (hacc : acceptsFlatTM M [s] steps = true) :
    ∃ sf, relpower (TCC.validStep (cookCards M)) steps (cookInit M s steps) sf ∧
      TCC.satFinal (cookFinal M) sf := by
  rw [acceptsFlatTM_eq_true_iff] at hacc
  obtain ⟨cfg_f, hexec, hh⟩ := hacc
  rw [execFlatTM_eq_some_runFlatTM (isValidFlatTapes_single M s hT hs)] at hexec
  obtain ⟨hrel, hfitf⟩ := relpower_of_run M (s.length + steps + 3) hV steps 0
    (initFlatConfig M [s]) cfg_f (ConfFits_init M s hV hs) (by omega) (by omega)
    hexec hh
  exact ⟨confRow M cfg_f (s.length + steps + 3), hrel,
    satFinal_of_halt M _ hfitf (by have := hfitf.head_le; omega) hh⟩

/-- **Cover transport (the (3) induction).** A `k`-step card-covered chain
out of a fitting configuration row, ending in a final-pattern row, forces a
halting machine run: `step_of_validStep` classifies each covered step as
either the halt freeze (the machine has already accepted — close
immediately, ignoring the frozen remainder of the chain) or `confRow` of
the unique machine step (recurse); the base case converts the final
pattern back to a halting state via `halt_of_satFinal`. -/
theorem run_of_relpower (M : FlatTM) (n : Nat) {base : Nat} (hV : validFlatTM M) :
    ∀ (k t : Nat) (cfg : FlatTMConfig) (sf : List (Fin (Sg M))),
      ConfFits M base t cfg →
      t + k + 3 ≤ n →
      base + t + k + 3 ≤ n →
      relpower (TCC.validStep (cookCards M)) k (confRow M cfg n) sf →
      TCC.satFinal (cookFinal M) sf →
      ∃ cfg_f, runFlatTM k M cfg = some cfg_f ∧
        haltingStateReached M cfg_f = true
  | 0, t, cfg, sf, hfit, _hn, _hbn, hrel, hfin => by
      cases hrel with
      | refl => exact ⟨cfg, rfl, halt_of_satFinal M n hfit hfin⟩
  | k + 1, t, cfg, sf, hfit, hn, hbn, hrel, hfin => by
      cases hrel with
      | step hvs hrest =>
        have hhead4 : cfgHead cfg + 4 ≤ n := by have := hfit.head_le; omega
        have hlen2 : (cfgRight cfg).length + 2 ≤ n := by
          have := hfit.len_le; omega
        rcases step_of_validStep M n hV hfit hhead4 hlen2 _ hvs with
          ⟨hhalt, -⟩ | ⟨hnh, cfg', hstep, rfl⟩
        · -- already halted: accepted within any remaining budget
          exact ⟨cfg, runFlatTM_of_halting M cfg (k + 1) hhalt, hhalt⟩
        · obtain ⟨cfg_f, hrun, hh⟩ := run_of_relpower M n hV k (t + 1) cfg' sf
            (ConfFits_step M hV hfit hstep) (by omega) (by omega) hrest hfin
          refine ⟨cfg_f, ?_, hh⟩
          have hunfold : runFlatTM (k + 1) M cfg = runFlatTM k M cfg' := by
            show (if haltingStateReached M cfg = true then some cfg else _) = _
            rw [if_neg (by rw [hnh]; exact Bool.false_ne_true), hstep]
          rw [hunfold, hrun]

/-- **(3) Covering ⟹ run**: extract the accepting run — `run_of_relpower`
on the covering chain from the initial configuration. -/
theorem run_of_cover (M : FlatTM) (s : List Nat) (steps : Nat)
    (hV : validFlatTM M) (hT : M.tapes = 1) (hs : list_ofFlatType M.sig s)
    (sf : List (Fin (Sg M)))
    (hrel : relpower (TCC.validStep (cookCards M)) steps (cookInit M s steps) sf)
    (hfin : TCC.satFinal (cookFinal M) sf) :
    acceptsFlatTM M [s] steps = true := by
  obtain ⟨cfg_f, hrun, hh⟩ := run_of_relpower M (s.length + steps + 3) hV steps 0
    (initFlatConfig M [s]) sf (ConfFits_init M s hV hs) (by omega) (by omega)
    hrel hfin
  rw [acceptsFlatTM_eq_true_iff]
  exact ⟨cfg_f,
    by rw [execFlatTM_eq_some_runFlatTM (isValidFlatTapes_single M s hT hs)]
       exact hrun,
    hh⟩

/-- **Main bijection — restated (v2) and assembled from the skeleton.**
The v1 statement lacked the `validFlatTM`/`tapes = 1`/alphabet hypotheses
(without `hs`, `acceptsFlatTM` is `false` on alphabet-invalid input while
the tableau can still be coverable — e.g. an immediately-halting machine)
and was false outright under the pre-2026-07-17 jump-write semantics (see
the module docstring). The eventual S1 witness guards on exactly these
decidable hypotheses (guarded-map pattern) — instances failing them are
`FlatSingleTMGenNP` no-instances by definition. -/
theorem cookTableau_correct (M : FlatTM) (s : List Nat) (steps : Nat)
    (hV : validFlatTM M) (hT : M.tapes = 1) (hs : list_ofFlatType M.sig s) :
    acceptsFlatTM M [s] steps = true ↔
    FlatTCC.FlatTCCLang (cookTableau M s steps) := by
  constructor
  · intro hacc
    obtain ⟨sf, hrel, hfin⟩ := cover_of_run M s steps hV hT hs hacc
    have htcc : TCC.TCCLang (cookTableauTyped M s steps) :=
      ⟨cookTableauTyped_wellformed M s steps, sf, hrel, hfin⟩
    refine ⟨FlatTCC.flattenTCC_wellformed htcc.1,
      ⟨FlatTCC.isValidFlattening_flattenTCC _, ?_⟩⟩
    simpa [cookTableau, FlatTCC.unflatten_flattenTCC] using htcc
  · rintro ⟨-, hval, htcc⟩
    have heq : FlatTCC.unflattenTCC (cookTableau M s steps) hval
        = cookTableauTyped M s steps := FlatTCC.unflatten_flattenTCC _
    rw [heq] at htcc
    obtain ⟨-, sf, hrel, hfin⟩ := htcc
    exact run_of_cover M s steps hV hT hs sf hrel hfin

/-! ### Constrained-case bijection (PROVEN — the v2 card-family probe)

For an immediately-halting single-tape machine on empty input, the tableau
is coverable for every step budget, matching acceptance. Ported from v1;
now exercises the boundary marker (window 0 is `(#, head, blank)`) and the
halt-center/halt-left/copy families. -/

/-- The empty-input initial row: boundary marker, head cell, blanks, and
the right boundary marker. -/
theorem cookInit_nil (M : FlatTM) (steps : Nat) :
    cookInit M [] steps =
      bCell M :: hCell M (stateOf M M.start) (blankSym M) ::
        List.replicate (steps + 2) (tCell M (blankSym M)) ++ [bCell M] := by
  unfold cookInit confRow
  congr 1
  congr 1
  have hcell0 : confCell M (initFlatConfig M [[]]).state_idx
      (cfgHead (initFlatConfig M [[]])) (cfgRight (initFlatConfig M [[]])) 0
      = hCell M (stateOf M M.start) (blankSym M) := by
    simp [confCell, cfgHead, cfgRight, initFlatConfig, tapeSymAt]
  have hcellS : ∀ p : Nat, confCell M (initFlatConfig M [[]]).state_idx
      (cfgHead (initFlatConfig M [[]])) (cfgRight (initFlatConfig M [[]])) (p + 1)
      = tCell M (blankSym M) := by
    intro p
    simp [confCell, cfgHead, cfgRight, initFlatConfig, tapeSymAt]
  rw [show (List.nil).length + steps + 3 = (steps + 2) + 1 by simp,
    List.range_succ_eq_map, List.map_cons, hcell0, List.map_map]
  congr 1
  apply List.eq_replicate_iff.mpr
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [List.mem_map, List.mem_range, Function.comp_apply] at hc
  obtain ⟨p, -, hp⟩ := hc
  rw [← hp]
  exact hcellS p

/-- **Freeze step (the load-bearing window bookkeeping, v2).** A halting
machine's empty-input row covers itself: window 0 (boundary, head, blank)
by a halt-center card, window 1 (head, blank, blank) by a halt-left card,
all-blank windows by copy cards. -/
theorem freeze_validStep (M : FlatTM) (steps : Nat)
    (hHalt : M.halt.getD (stateOf M M.start).1 false = true) :
    TCC.validStep (cookCards M) (cookInit M [] steps) (cookInit M [] steps) := by
  refine ⟨rfl, ?_⟩
  intro i hi
  rw [cookInit_nil] at hi ⊢
  set H := hCell M (stateOf M M.start) (blankSym M) with hHdef
  set B := tCell M (blankSym M) with hBdef
  set Bd := bCell M with hBddef
  have hlen : (Bd :: H :: List.replicate (steps + 2) B ++ [Bd]).length
      = steps + 5 := by
    simp
  rw [hlen] at hi
  rcases i with _ | (_ | j)
  · -- window 0: (boundary, head, blank) — halt-center with x = none
    refine ⟨copyCard M Bd H B, ?_, ?_⟩
    · exact haltCenterCard_mem_cookCards M _ _ none _ hHalt
    · rw [List.drop_zero]
      exact coversHead_copy M Bd H B _ (List.replicate (steps + 1) B ++ [Bd]) rfl
  · -- window 1: (head, blank, blank) — halt-left
    refine ⟨copyCard M H B B, haltLeftCard_mem_cookCards M _ _ _ _ hHalt, ?_⟩
    exact coversHead_copy M H B B _ (List.replicate steps B ++ [Bd]) rfl
  · -- windows ≥ 2: all-blank interior, or the rightmost marker window
    have hj : j ≤ steps := by omega
    have hdrop : (Bd :: H :: List.replicate (steps + 2) B ++ [Bd]).drop (j + 2)
        = List.replicate (steps + 2 - j) B ++ [Bd] := by
      rw [show (Bd :: H :: List.replicate (steps + 2) B ++ [Bd]).drop (j + 2)
          = (List.replicate (steps + 2) B ++ [Bd]).drop j from rfl,
        List.drop_append_of_le_length (by rw [List.length_replicate]; omega),
        List.drop_replicate]
    by_cases hlastw : j = steps
    · -- the rightmost window: (blank, blank, right marker)
      subst hlastw
      refine ⟨copyCard M B B Bd, copyRightCard_mem_cookCards M _ _, ?_⟩
      rw [hdrop, show j + 2 - j = 2 from by omega]
      exact coversHead_copy M B B Bd _ [] rfl
    · -- all-blank interior window
      refine ⟨copyCard M B B B, copyCard_mem_cookCards M (some (blankSym M))
        (blankSym M) (blankSym M), ?_⟩
      obtain ⟨K, hK⟩ : ∃ K, steps + 2 - j = 3 + K := ⟨steps - j - 1, by omega⟩
      rw [hdrop, hK, List.replicate_add]
      exact coversHead_copy M B B B _ (List.replicate K B ++ [Bd]) rfl

theorem freeze_relpower (M : FlatTM) (steps : Nat)
    (hHalt : M.halt.getD (stateOf M M.start).1 false = true) :
    ∀ k, relpower (TCC.validStep (cookCards M)) k (cookInit M [] steps) (cookInit M [] steps)
  | 0 => relpower.refl _
  | k + 1 => relpower.step (freeze_validStep M steps hHalt) (freeze_relpower M steps hHalt k)

theorem freeze_satFinal (M : FlatTM) (steps : Nat)
    (hHalt : M.halt.getD (stateOf M M.start).1 false = true) :
    TCC.satFinal (cookFinal M) (cookInit M [] steps) := by
  refine ⟨[hCell M (stateOf M M.start) (blankSym M)], ?_, ?_⟩
  · unfold cookFinal
    refine List.mem_flatMap.2 ⟨stateOf M M.start, List.mem_finRange _, ?_⟩
    rw [if_pos hHalt]
    exact List.mem_map.2 ⟨blankSym M, List.mem_finRange _, rfl⟩
  · rw [cookInit_nil]
    exact ⟨[bCell M],
      List.replicate (steps + 2) (tCell M (blankSym M)) ++ [bCell M], rfl⟩

theorem cookTableau_lang (M : FlatTM) (steps : Nat)
    (hHalt : M.halt.getD (stateOf M M.start).1 false = true) :
    FlatTCC.FlatTCCLang (cookTableau M [] steps) := by
  have htccLang : TCC.TCCLang (cookTableauTyped M [] steps) :=
    ⟨cookTableauTyped_wellformed M [] steps,
      cookInit M [] steps,
      freeze_relpower M steps hHalt steps,
      freeze_satFinal M steps hHalt⟩
  refine ⟨FlatTCC.flattenTCC_wellformed htccLang.1,
    ⟨FlatTCC.isValidFlattening_flattenTCC _, ?_⟩⟩
  simpa [cookTableau, FlatTCC.unflatten_flattenTCC] using htccLang

theorem accepts_immediateHalt (M : FlatTM) (steps : Nat)
    (hTapes : M.tapes = 1) (hHalt : M.halt.getD M.start false = true) :
    acceptsFlatTM M [[]] steps = true := by
  have hvalid : isValidFlatTapes M [[]] = true := by
    simp [isValidFlatTapes, hTapes, isValidFlatTape]
  have hinit : haltingStateReached M (initFlatConfig M [[]]) = true := by
    show M.halt.getD M.start false = true
    exact hHalt
  rw [acceptsFlatTM_eq_true_iff]
  refine ⟨initFlatConfig M [[]], ?_, hinit⟩
  rw [execFlatTM_eq_some_runFlatTM hvalid]
  exact runFlatTM_of_halting M (initFlatConfig M [[]]) steps hinit

theorem cookTableau_correct_immediateHalt (M : FlatTM) (steps : Nat)
    (hTapes : M.tapes = 1) (hStart : M.start < M.states)
    (hHalt : M.halt.getD M.start false = true) :
    acceptsFlatTM M [[]] steps = true ↔
    FlatTCC.FlatTCCLang (cookTableau M [] steps) := by
  have hstate : (stateOf M M.start).1 = M.start := by
    simp [stateOf]; omega
  have hHalt' : M.halt.getD (stateOf M M.start).1 false = true := by rw [hstate]; exact hHalt
  exact ⟨fun _ => cookTableau_lang M steps hHalt',
    fun _ => accepts_immediateHalt M steps hTapes hHalt⟩

/-! ## Polynomial size-bound function (framework obligations)

Bumped from degree 3 to 10 to match the corrected `cookTableau_size_bound`. -/

def cookTableau_sizeBound (n : Nat) : Nat := (n + 1) ^ 10

theorem cookTableau_sizeBound_poly : inOPoly cookTableau_sizeBound := by
  refine ⟨10, ⟨1024, 1, ?_⟩⟩
  intro n hn
  unfold cookTableau_sizeBound
  have h1 : n + 1 ≤ 2 * n := by omega
  calc (n + 1) ^ 10 ≤ (2 * n) ^ 10 := Nat.pow_le_pow_left h1 10
    _ = 1024 * n ^ 10 := by ring

theorem cookTableau_sizeBound_mono : monotonic cookTableau_sizeBound := by
  intro x x' hxx'
  unfold cookTableau_sizeBound
  exact Nat.pow_le_pow_left (by omega) 10

end Complexity.Simulators
