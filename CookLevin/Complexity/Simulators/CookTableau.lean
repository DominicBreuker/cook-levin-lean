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
  the assembly from the sub-lemmas is PROVEN, the sub-lemmas are `sorry` with
  proof plans in their docstrings.
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

/-- Row width: boundary marker + `|s| + steps + 3` tape positions (so the
head — which starts at tape position 0 and advances at most one per step —
always has a full 3-window around it, and the written region always has a
blank cell after it inside the row). -/
def rowWidth (s : List Nat) (steps : Nat) : Nat := s.length + steps + 4

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

/-- The tableau row of a configuration: the boundary marker followed by `n`
tape-position cells. -/
def confRow (M : FlatTM) (cfg : FlatTMConfig) (n : Nat) : List (Fin (Sg M)) :=
  bCell M ::
    (List.range n).map (confCell M cfg.state_idx (cfgHead cfg) (cfgRight cfg))

theorem confRow_length (M : FlatTM) (cfg : FlatTMConfig) (n : Nat) :
    (confRow M cfg n).length = n + 1 := by
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
  copyCards M ++ haltLeftCards M ++ haltCenterCards M ++ haltRightCards M ++
    stepCards M

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

/-- **(1a) Card soundness of a machine step** (skeleton): a legal
non-halting machine step is a card-covered row transition. Proof plan: fix
window `i` and case on its position relative to the head's row coordinate
`h = cfgHead cfg + 1`: `i = h-1` center (the firing entry's
`stepCardCenter`; the left-neighbour blankness matches the frontier by the
invariant, so `wEff` computes the write), `i = h` left-of, `i = h-2`
right-of, `i = h+1` (`Rmove` incoming) / `i = h-3` (`Lmove` incoming), all
other windows all-tape (`copyCards`; window 0 via the boundary variants).
Requires `stepFlatTM_normM` to replace the fired entry by its normalised
representative (whose cards are the generated ones). -/
theorem validStep_of_step (M : FlatTM) (n : Nat) {base t : Nat}
    {cfg cfg' : FlatTMConfig}
    (hV : validFlatTM M) (hfit : ConfFits M base t cfg)
    (hhead : cfgHead cfg + 3 ≤ n)
    (hlen : (cfgRight cfg).length + 2 ≤ n)
    (hnh : haltingStateReached M cfg = false)
    (hstep : stepFlatTM M cfg = some cfg') :
    TCC.validStep (cookCards M) (confRow M cfg n) (confRow M cfg' n) := by
  sorry  -- S1 skeleton: step soundness (direction 1a). See docstring.

/-- **(1a′) Halt freeze** (skeleton): a halting configuration's row covers
itself — the three head windows by the halt-freeze families, the rest by
copy cards. (Generalises the proven empty-input case `freeze_validStep`.) -/
theorem validStep_of_halt (M : FlatTM) (n : Nat) {base t : Nat}
    {cfg : FlatTMConfig}
    (hfit : ConfFits M base t cfg)
    (hhead : cfgHead cfg + 3 ≤ n)
    (hh : haltingStateReached M cfg = true) :
    TCC.validStep (cookCards M) (confRow M cfg n) (confRow M cfg n) := by
  sorry  -- S1 skeleton: halt freeze (direction 1a′).

/-- **(1b) Card completeness — the inversion heart** (skeleton, the Coq
port's ~2K-line per-constructor analysis). Any card-covered successor of a
*configuration row* is forced: the frozen row itself when halting,
`confRow` of *the* unique machine step otherwise. Proof structure:
(i) every window not containing the head has an all-tape/boundary premise,
and the only conclusions available off such premises keep the cells
(copy) or place a head at the first (Rmove-in) / third (Lmove-in) slot —
there is **no head-at-second-slot family**, so a head in `b` adjacent only
to unchanged tape cells on both sides is impossible, hence `b` has no head
away from the source head's three-cell neighbourhood; (ii) the center
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
    (hhead : cfgHead cfg + 3 ≤ n)
    (hlen : (cfgRight cfg).length + 2 ≤ n)
    (b : List (Fin (Sg M)))
    (hvs : TCC.validStep (cookCards M) (confRow M cfg n) b) :
    (haltingStateReached M cfg = true ∧ b = confRow M cfg n) ∨
    (haltingStateReached M cfg = false ∧
      ∃ cfg', stepFlatTM M cfg = some cfg' ∧ b = confRow M cfg' n) := by
  sorry  -- S1 skeleton: inversion (direction 1b). See docstring.

/-- A halting configuration's row satisfies the final patterns (skeleton):
the head cell `hCell (stateOf q) (…)` occurs at row coordinate
`cfgHead cfg + 1 ≤ n`, and `stateOf` is the identity under `state_lt`. -/
theorem satFinal_of_halt (M : FlatTM) (n : Nat) {base t : Nat}
    {cfg : FlatTMConfig}
    (hfit : ConfFits M base t cfg)
    (hhead : cfgHead cfg < n)
    (hh : haltingStateReached M cfg = true) :
    TCC.satFinal (cookFinal M) (confRow M cfg n) := by
  sorry  -- S1 skeleton: satFinal, forward.

/-- Only halting rows satisfy the final patterns (skeleton): a final pattern
is a singleton halting head cell; head-cell codes are disjoint from tape and
boundary codes, so its occurrence in `confRow` must be the head cell, whose
state is `stateOf cfg.state_idx = cfg.state_idx` by `state_lt`. -/
theorem halt_of_satFinal (M : FlatTM) (n : Nat) {base t : Nat}
    {cfg : FlatTMConfig}
    (hfit : ConfFits M base t cfg)
    (hfin : TCC.satFinal (cookFinal M) (confRow M cfg n)) :
    haltingStateReached M cfg = true := by
  sorry  -- S1 skeleton: satFinal, backward.

/-- **(2) Run ⟹ covering** (skeleton): an accepting run yields a covering of
exactly `steps` rows. Proof plan: induction unfolding `runFlatTM` from
`initFlatConfig M [s]` (`ConfFits_init`/`ConfFits_step` thread the
invariant; `isValidFlatTapes` from `hT`/`hs`): a halting configuration
freezes for the remaining budget (`validStep_of_halt` iterated), a stepping
one advances (`validStep_of_step`), and a stuck non-halting configuration
contradicts `hacc` (the run then ends non-halting). Close with
`satFinal_of_halt` on the final row. -/
theorem cover_of_run (M : FlatTM) (s : List Nat) (steps : Nat)
    (hV : validFlatTM M) (hT : M.tapes = 1) (hs : list_ofFlatType M.sig s)
    (hacc : acceptsFlatTM M [s] steps = true) :
    ∃ sf, relpower (TCC.validStep (cookCards M)) steps (cookInit M s steps) sf ∧
      TCC.satFinal (cookFinal M) sf := by
  sorry  -- S1 skeleton: soundness assembly (direction 2). See docstring.

/-- **(3) Covering ⟹ run** (skeleton): extract the accepting run. Proof
plan: induction on the `relpower` chain from `cookInit` threading
`ConfFits` and "the current row is `confRow` of the current run
configuration" via `step_of_validStep`; on the halting branch the machine
stays halted (`runFlatTM_of_halting`) and acceptance follows once
`halt_of_satFinal` fires on the last row; window-room side conditions from
`ConfFits` bounds (`head ≤ t ≤ steps`, `len ≤ |s| + t`) against
`n = |s| + steps + 3`. -/
theorem run_of_cover (M : FlatTM) (s : List Nat) (steps : Nat)
    (hV : validFlatTM M) (hT : M.tapes = 1) (hs : list_ofFlatType M.sig s)
    (sf : List (Fin (Sg M)))
    (hrel : relpower (TCC.validStep (cookCards M)) steps (cookInit M s steps) sf)
    (hfin : TCC.satFinal (cookFinal M) sf) :
    acceptsFlatTM M [s] steps = true := by
  sorry  -- S1 skeleton: completeness assembly (direction 3). See docstring.

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

/-- The empty-input initial row: boundary marker, head cell, blanks. -/
theorem cookInit_nil (M : FlatTM) (steps : Nat) :
    cookInit M [] steps =
      bCell M :: hCell M (stateOf M M.start) (blankSym M) ::
        List.replicate (steps + 2) (tCell M (blankSym M)) := by
  unfold cookInit confRow
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

/-- A copy-shaped card licenses an unchanged window once its first three
cells match. -/
theorem coversHead_copy (M : FlatTM) (x y z : Fin (Sg M)) (l rest : List (Fin (Sg M)))
    (h : l = x :: y :: z :: rest) :
    TCC.coversHead (copyCard M x y z) l l := by
  refine ⟨⟨rest, ?_⟩, ⟨rest, ?_⟩⟩ <;>
    · show l = [x, y, z] ++ rest
      exact h

theorem copyCard_mem (M : FlatTM) (x : Option (Fin (M.sig + 1))) (b c : Fin (M.sig + 1)) :
    copyCard M (xCell M x) (tCell M b) (tCell M c) ∈ copyCards M := by
  unfold copyCards
  refine List.mem_flatMap.2 ⟨x, ?_, ?_⟩
  · cases x with
    | none => simp [xOpts]
    | some a => simp [xOpts]
  · refine List.mem_flatMap.2 ⟨b, List.mem_finRange b, ?_⟩
    exact List.mem_map.2 ⟨c, List.mem_finRange c, rfl⟩

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
  refine List.mem_flatMap.2 ⟨x, ?_, ?_⟩
  · cases x with
    | none => simp [xOpts]
    | some a => simp [xOpts]
  · exact List.mem_map.2 ⟨z, List.mem_finRange z, rfl⟩

theorem copyCard_mem_cookCards (M : FlatTM) (x : Option (Fin (M.sig + 1)))
    (b c : Fin (M.sig + 1)) :
    copyCard M (xCell M x) (tCell M b) (tCell M c) ∈ cookCards M := by
  unfold cookCards
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (copyCard_mem M x b c))))

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
  have hlen : (Bd :: H :: List.replicate (steps + 2) B).length = steps + 4 := by
    simp
  rw [hlen] at hi
  rcases i with _ | (_ | j)
  · -- window 0: (boundary, head, blank) — halt-center with x = none
    refine ⟨copyCard M Bd H B, ?_, ?_⟩
    · exact haltCenterCard_mem_cookCards M _ _ none _ hHalt
    · rw [List.drop_zero]
      apply coversHead_copy M Bd H B _
        (List.replicate (steps + 1) B)
      rw [show steps + 2 = (steps + 1) + 1 from rfl, List.replicate_succ]
  · -- window 1: (head, blank, blank) — halt-left
    refine ⟨copyCard M H B B, haltLeftCard_mem_cookCards M _ _ _ _ hHalt, ?_⟩
    show TCC.coversHead _ (H :: List.replicate (steps + 2) B)
      (H :: List.replicate (steps + 2) B)
    apply coversHead_copy M H B B _ (List.replicate steps B)
    rw [show steps + 2 = steps + 1 + 1 from rfl, List.replicate_succ,
      show steps + 1 = steps + 1 from rfl, List.replicate_succ]
  · -- windows ≥ 2: all-blank — copy with x = some blank
    refine ⟨copyCard M B B B, copyCard_mem_cookCards M (some (blankSym M))
      (blankSym M) (blankSym M), ?_⟩
    show TCC.coversHead _ ((List.replicate (steps + 2) B).drop j)
      ((List.replicate (steps + 2) B).drop j)
    rw [List.drop_replicate]
    apply coversHead_copy M B B B _ (List.replicate (steps + 2 - j - 3) B)
    generalize hK : steps + 2 - j - 3 = K
    rw [show steps + 2 - j = 3 + K from by omega, List.replicate_add]
    rfl

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
    exact ⟨[bCell M], List.replicate (steps + 2) (tCell M (blankSym M)), rfl⟩

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
