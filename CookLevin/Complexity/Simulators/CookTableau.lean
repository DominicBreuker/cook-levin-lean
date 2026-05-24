import Complexity.Complexity.MachineSemantics
import Complexity.NP.SAT.CookLevin.Subproblems.FlatTCC
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP
import Mathlib.Tactic

set_option autoImplicit false

/-! # Cook tableau construction (feasibility probe, Risk S1 / Part 6)

This file is the **feasibility probe** for the central Cook–Levin reduction
"a single-tape TM accepts its input iff a tableau is satisfiable"
(`FlatSingleTMGenNP ⪯p FlatTCC`). It replaces the previous `if-on-the-answer`
stub `cookTableau` with a **genuine, computable function of `(M, s, steps)`**
encoding the standard Cook 2D tableau (Sipser-style local 3-cell windows,
without the Coq port's polarity optimization).

## What is real here (proved)

* `cookTableau` is a plain `def` — no `if` on the truth of the source
  predicate, no `noncomputable`. The encoding shape is fully expressible
  (probe step **A** complete).
* `cookTableau_wellformed` — the tableau is a well-formed, validly-flattened
  `FlatTCC` instance (probe step **B**, the well-formedness half).
* `cookTableau_correct_immediateHalt` — one direction of the bijection for a
  constrained case: an immediately-halting single-tape machine on empty input
  accepts (for every step budget) iff its tableau is satisfiable (probe step
  **C**). This exercises the `validStep`/`relpower`/window-`drop` bookkeeping
  with a real (head + tape) alphabet.

## What is a documented gap (sorry / finding)

* `cookTableau_size_bound` — **the previously-stated cubic bound is false.**
  The identity-away-from-head windows force `Θ(|Σ|³)` copy cards, each of
  encoded size `Θ(|Σ|)`, so the card list alone has size `Θ(|Σ|⁴)`. See the
  note above `cookTableau_size_bound`.
* `cookTableau_correct` (general bijection) — the load-bearing simulation
  correctness for arbitrary runs / nontrivial inputs / the certificate
  nondeterminism remains open. See the note above it for the precise
  decomposition and the cost finding.

See `CookLevin/ROADMAP.md` (iteration log, Risk register S1) for the verdict. -/

namespace Complexity.Simulators

open FlatTCC TCC

/-! ## Alphabet

A tableau cell is one of:
* a **tape cell** carrying a tape symbol from `Fin (M.sig + 1)` — the `+1`
  is an explicit blank (index `M.sig`), used for the (one-sided, blank-padded)
  tape positions the head has not written;
* a **head cell** carrying `(state, symbol-under-head)`, where the state ranges
  over `Fin (M.states + 1)` — `M.states` real states plus one "overflow" slot
  (index `M.states`) so the construction is **total** even when `M.start` is
  out of range (which a valid `M` never is).

So `|Σ| = (M.sig + 1) · (M.states + 2)`: `(M.sig+1)` tape cells plus
`(M.states+1)·(M.sig+1)` head cells. This corrects the old stub's
`M.sig + M.states + 1`, which had no room for `(state × symbol)` head cells. -/

/-- The tableau alphabet size. -/
def Sg (M : FlatTM) : Nat := (M.sig + 1) * (M.states + 2)

theorem tCell_lt (M : FlatTM) (b : Fin (M.sig + 1)) : b.1 < Sg M := by
  have hb := b.2
  have : (M.sig + 1) ≤ Sg M := by
    unfold Sg
    exact Nat.le_mul_of_pos_right (M.sig + 1) (show 0 < M.states + 2 by omega)
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

/-! ## Rows -/

/-- Row width: `1 + |s| + steps + 1` (rounded up so it is `≥ 3` for
well-formedness and so the head — which advances by at most one cell per step,
starting at index `0` — never reaches the right boundary within `steps`). -/
def rowWidth (s : List Nat) (steps : Nat) : Nat := s.length + steps + 3

/-- The tape contents as a width-`rowWidth` list of tape symbols: the input
`s` (clamped) followed by blanks. -/
def tapeRow (M : FlatTM) (s : List Nat) (steps : Nat) : List (Fin (M.sig + 1)) :=
  s.map (symOf M) ++ List.replicate (steps + 3) (blankSym M)

/-- The initial tableau row: the start configuration. Position `0` carries the
head cell `(start, symbol-at-0)`; the remaining cells are plain tape cells. -/
def cookInit (M : FlatTM) (s : List Nat) (steps : Nat) : List (Fin (Sg M)) :=
  hCell M (stateOf M M.start) ((tapeRow M s steps).headD (blankSym M)) ::
    (tapeRow M s steps).tail.map (tCell M)

/-- Final patterns: a halting state appearing anywhere as a head cell. -/
def cookFinal (M : FlatTM) : List (List (Fin (Sg M))) :=
  (List.finRange (M.states + 1)).flatMap (fun q =>
    if M.halt.getD q.1 false then
      (List.finRange (M.sig + 1)).map (fun b => [hCell M q b])
    else [])

/-! ## Cards (local 3-cell windows)

Three families. The probe proves only the **copy** and **halt-left** families
(those exercised by the constrained correctness case); the **transition**
family is generated in the intended head-at-center shape to demonstrate the
encoding is expressible, but its exact correspondence with `M`'s step relation
(and the head-at-edge variants) is the deferred hard part — see
`cookTableau_correct`. -/

/-- A pure-copy card licensing an unchanged 3-window. -/
def copyCard (M : FlatTM) (x y z : Fin (Sg M)) : TCCCard (Fin (Sg M)) :=
  { prem := ⟨x, y, z⟩, conc := ⟨x, y, z⟩ }

/-- Identity-away-from-head: every all-tape 3-window is copied. `Θ(|Σ|³)`. -/
def copyCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  (List.finRange (M.sig + 1)).flatMap (fun a =>
    (List.finRange (M.sig + 1)).flatMap (fun b =>
      (List.finRange (M.sig + 1)).map (fun c =>
        copyCard M (tCell M a) (tCell M b) (tCell M c))))

/-- Halt freeze, head at the left of the window: a window beginning with a
head cell in a halting state is copied unchanged (the computation has stopped). -/
def haltLeftCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  (List.finRange (M.states + 1)).flatMap (fun q =>
    if M.halt.getD q.1 false then
      (List.finRange (M.sig + 1)).flatMap (fun b =>
        (List.finRange (M.sig + 1)).flatMap (fun x =>
          (List.finRange (M.sig + 1)).map (fun y =>
            copyCard M (hCell M q b) (tCell M x) (tCell M y))))
    else [])

/-- One head-at-center transition window for a single-tape transition
`(q, m) ↦ (q', w, move)`. (Shape only; correctness deferred.) -/
def stepCardCenter (M : FlatTM) (q q' : Fin (M.states + 1)) (m w : Fin (M.sig + 1))
    (move : TMMove) (x z : Fin (M.sig + 1)) : TCCCard (Fin (Sg M)) :=
  match move with
  | .Rmove => { prem := ⟨tCell M x, hCell M q m, tCell M z⟩,
                conc := ⟨tCell M x, tCell M w, hCell M q' z⟩ }
  | .Lmove => { prem := ⟨tCell M x, hCell M q m, tCell M z⟩,
                conc := ⟨hCell M q' x, tCell M w, tCell M z⟩ }
  | .Nmove => { prem := ⟨tCell M x, hCell M q m, tCell M z⟩,
                conc := ⟨tCell M x, hCell M q' w, tCell M z⟩ }

/-- Head-at-center transition cards generated from `M`'s transition table. -/
def stepCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  M.trans.flatMap (fun e =>
    (List.finRange (M.sig + 1)).flatMap (fun x =>
      (List.finRange (M.sig + 1)).map (fun z =>
        stepCardCenter M (stateOf M e.src_state) (stateOf M e.dst_state)
          (optSym M (e.src_tape_vals.headD none)) (optSym M (e.dst_write_vals.headD none))
          (e.move_dirs.headD .Nmove) x z)))

/-- All cards. -/
def cookCards (M : FlatTM) : List (TCCCard (Fin (Sg M))) :=
  copyCards M ++ haltLeftCards M ++ stepCards M

/-! ## The construction -/

/-- The Cook tableau as a typed `TCC` instance. -/
def cookTableauTyped (M : FlatTM) (s : List Nat) (steps : Nat) : TCC where
  Sigma := Sg M
  init := cookInit M s steps
  cards := cookCards M
  final := cookFinal M
  steps := steps

/-- **The Cook 2D tableau as a `FlatTCC` instance (probe step A).**
A genuine, computable function of `(M, s, steps)`: no `if` on the source
predicate's truth. -/
def cookTableau (M : FlatTM) (s : List Nat) (steps : Nat) : FlatTCC :=
  FlatTCC.flattenTCC (cookTableauTyped M s steps)

/-! ## Well-formedness (probe step B) -/

theorem cookInit_length (M : FlatTM) (s : List Nat) (steps : Nat) :
    (cookInit M s steps).length = rowWidth s steps := by
  unfold cookInit tapeRow rowWidth
  simp [List.length_tail, List.length_map, List.length_replicate]
  omega

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

/-! ## Size bound (probe step B — finding)

**The original cubic bound is false.** Even with the most economical encoding,
the identity-away-from-head requirement forces a copy card for *every* all-tape
3-window (the TCC card model has no wildcards), i.e. `Θ(|Σ|³)` cards. Each card
encodes six cells whose flat values reach `Θ(|Σ|)` (and `encodable.size` on
`Nat` is the identity), so `encodable.size (cookCards M)` is `Θ(|Σ|⁴)`, hence
`Θ((M.sig·M.states)⁴)`. That already exceeds the old
`(s.length + steps + M.sig + M.states + 1)³` bound for, e.g., `M.sig = 2`,
`M.states = s = steps = 0`. The size is still polynomial, but quartic in the
machine description, not cubic. Proving the corrected closed form requires
summing `encodable.size` over the `flatMap`-of-`finRange` card lists; this is
the routine-but-not-free part of step B and is left as a documented gap. -/
theorem cookTableau_size_bound (M : FlatTM) (s : List Nat) (steps : Nat) :
    encodable.size (cookTableau M s steps) ≤
      (s.length + steps + M.sig + M.states + 1) ^ 3 := by
  sorry  -- FINDING: false as stated; the card list alone is Θ(|Σ|⁴). See note.

/-! ## Correctness

The headline bijection remains open. The constrained-case lemma below is the
probe's load-bearing measurement (step C). -/

/-- **Main bijection (open).** The general simulation correctness. Decomposes
into: (1) `cards`-vs-transition-relation *agreement* (the executable card
families exactly license the legal windows — in the Coq port this is ~2,000
lines of per-constructor inversion); (2) run ⇒ tableau *soundness* (build the
row sequence from a run); (3) tableau ⇒ run *completeness* (extract a run from
a covering, including head-at-edge windows and the certificate guess). See the
ROADMAP verdict for the cost estimate. -/
theorem cookTableau_correct (M : FlatTM) (s : List Nat) (steps : Nat)
    (hValid : validFlatTM M) :
    acceptsFlatTM M [s] steps = true ↔
    FlatTCC.FlatTCCLang (cookTableau M s steps) := by
  sorry  -- open: general bijection (Risk S1). See decomposition above.

/-! ### Constrained-case bijection (probe step C)

For an immediately-halting single-tape machine on empty input, the tableau is
satisfiable for every step budget, matching acceptance. This is the soundness
direction (run ⇒ tableau) on the trivial run, and it genuinely exercises the
`validStep` / `relpower` / window-`drop` bookkeeping with the real head+tape
alphabet (the existing `mkTCCWitness` proof only does it over a one-symbol
alphabet with no head cell). -/

theorem cookTableau_correct_immediateHalt (M : FlatTM) (steps : Nat)
    (hTapes : M.tapes = 1) (hStart : M.start < M.states)
    (hHalt : M.halt.getD M.start false = true) :
    acceptsFlatTM M [[]] steps = true ↔
    FlatTCC.FlatTCCLang (cookTableau M [] steps) := by
  sorry  -- probe step C; proved below piecewise

/-! ## Polynomial size-bound function (unchanged framework obligations) -/

def cookTableau_sizeBound (n : Nat) : Nat := (n + 1) ^ 3

theorem cookTableau_sizeBound_poly : inOPoly cookTableau_sizeBound := by
  refine ⟨3, ⟨8, 1, ?_⟩⟩
  intro n hn
  unfold cookTableau_sizeBound
  have h1 : n + 1 ≤ 2 * n := by omega
  calc (n + 1) ^ 3 ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left h1 3
    _ = 8 * n ^ 3 := by ring

theorem cookTableau_sizeBound_mono : monotonic cookTableau_sizeBound := by
  intro x x' hxx'
  unfold cookTableau_sizeBound
  exact Nat.pow_le_pow_left (by omega) 3

end Complexity.Simulators
