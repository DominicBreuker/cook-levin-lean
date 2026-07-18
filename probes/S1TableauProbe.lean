import Complexity.Simulators.CookTableau

set_option autoImplicit false

/-! # S1 tableau probe (2026-07-17): the v2 card algebra vs. real runs

Probes, per the handoff plan for S1 session 1, **direction (1) agreement on
concrete machines**: every 3-window of consecutive configuration rows of a
real run is licensed by `cookCards`, halting rows freeze, and skipping a row
is *not* licensed (negative control).

Also pins the 2026-07-17 `writeCurrentTapeSymbol` semantics fix (writes
strictly beyond the tape frontier are void; append only at the frontier) and
demonstrates on `M2` why the fix was necessary: under the old zero-padding
semantics `M2` REJECTED (the padded `0` under the returning head matched no
entry — stuck), while any local card family must behave like the new
semantics, where the beyond-frontier write is void and `M2` ACCEPTS. One
machine, two different answers ⟹ the old semantics admitted no correct local
tableau (`cookTableau_correct` was false as stated).

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1TableauProbe.lean` -/

open Complexity.Simulators

/-! ## §0 The write-semantics pins -/

-- in-range write replaces
example : writeCurrentTapeSymbol ([], 0, [7]) (some 5) = ([], 0, [5]) := rfl
-- frontier write appends
example : writeCurrentTapeSymbol ([], 1, [7]) (some 5) = ([], 1, [7, 5]) := rfl
-- beyond-frontier write is VOID (old semantics: ([], 3, [7, 0, 5]))
example : writeCurrentTapeSymbol ([], 3, [7]) (some 5) = ([], 3, [7]) := rfl
-- none-write is a no-op
example : writeCurrentTapeSymbol ([], 3, [7]) none = ([], 3, [7]) := rfl

/-! ## §1 Machines

`M1` (sig 2, 5 states, input `[1,0]`): exercises an in-range write, a
`none`-write, `Rmove`, a frontier append off a blank read, `Lmove`, `Nmove`,
and halting. Run: `(q0,h0,[1,0]) → (q1,h1,[0,0]) → (q2,h2,[0,0]) →
(q3,h1,[0,0,1]) → (q4,h1,[0,0,1])` halt.

`M2` (sig 2, 6 states, input `[]`): wanders three cells past the frontier
reading blanks, then writes (VOID under the fixed semantics), returns left
still reading a blank, and accepts. Exercises the `wEff` beyond-frontier
(`xb = true`) card path. -/

def M1 : FlatTM :=
  { sig := 2, tapes := 1, states := 5,
    trans := [
      ⟨0, [some 1], 1, [some 0], [TMMove.Rmove]⟩,
      ⟨1, [some 0], 2, [none],   [TMMove.Rmove]⟩,
      ⟨2, [none],   3, [some 1], [TMMove.Lmove]⟩,
      ⟨3, [some 0], 4, [none],   [TMMove.Nmove]⟩],
    start := 0, halt := [false, false, false, false, true] }

def M2 : FlatTM :=
  { sig := 2, tapes := 1, states := 6,
    trans := [
      ⟨0, [none], 1, [none],   [TMMove.Rmove]⟩,
      ⟨1, [none], 2, [none],   [TMMove.Rmove]⟩,
      ⟨2, [none], 3, [none],   [TMMove.Rmove]⟩,
      ⟨3, [none], 4, [some 1], [TMMove.Lmove]⟩,  -- beyond-frontier write: VOID
      ⟨4, [none], 5, [none],   [TMMove.Nmove]⟩],
    start := 0, halt := [false, false, false, false, false, true] }

-- M1 accepts [1,0] in 4 steps; M2 accepts [] in 5 steps (fixed semantics!).
#eval acceptsFlatTM M1 [[1, 0]] 4   -- expect: true
#eval acceptsFlatTM M2 [[]] 5       -- expect: true (old semantics: false — stuck on the padded 0)
-- M2's tape stays [] throughout: the beyond-frontier write was void.
#eval (runFlatTM 5 M2 (initFlatConfig M2 [[]])).map (fun c => (c.state_idx, c.tapes))
-- expect: some (5, [([], 2, [])])

/-! ## §2 Executable window coverage -/

/-- Executable `TCC.coversHead` for a 3-cell card. -/
def coversHeadB {k : Nat} (card : TCCCard (Fin k)) (a b : List (Fin k)) : Bool :=
  decide (3 ≤ a.length) && decide (3 ≤ b.length) &&
  decide (a.take 3 = (card.prem : List (Fin k))) &&
  decide (b.take 3 = (card.conc : List (Fin k)))

/-- Executable `TCC.validStep`. -/
def validStepB {k : Nat} (cards : List (TCCCard (Fin k))) (a b : List (Fin k)) : Bool :=
  decide (a.length = b.length) &&
  (List.range a.length).all (fun i =>
    !(decide (i + 3 ≤ a.length)) ||
      cards.any (fun c => coversHeadB c (a.drop i) (b.drop i)))

/-- The configuration row after `t` steps. -/
def rowOf (M : FlatTM) (s : List Nat) (t n : Nat) : List (Fin (Sg M)) :=
  match runFlatTM t M (initFlatConfig M [s]) with
  | some cfg => confRow M cfg n
  | none => []

-- card-count sanity (the families are populated)
#eval (cookCards M1).length   -- expect: a few hundred
#eval (normTrans M1).length   -- expect: 4

-- M1: row rendering (blank = 2, boundary = 21, head cells ≥ 3)
#eval (List.range 5).map (fun t => (rowOf M1 [1, 0] t 9).map Fin.val)

/-! ### The agreement probe (direction 1a, empirical): every real step of M1
is a card-covered row transition, and the halting row freezes. -/

#eval (List.range 4).all (fun t =>
  validStepB (cookCards M1) (rowOf M1 [1, 0] t 9) (rowOf M1 [1, 0] (t + 1) 9))
-- expect: true

#eval validStepB (cookCards M1) (rowOf M1 [1, 0] 4 9) (rowOf M1 [1, 0] 4 9)
-- expect: true (halt freeze)

-- negative control: skipping a row is NOT licensed
#eval validStepB (cookCards M1) (rowOf M1 [1, 0] 0 9) (rowOf M1 [1, 0] 2 9)
-- expect: false

-- negative control: a non-halting row does NOT freeze (no self-cards for
-- live heads — the tableau cannot stall before halting)
#eval validStepB (cookCards M1) (rowOf M1 [1, 0] 0 9) (rowOf M1 [1, 0] 0 9)
-- expect: false

/-! ### M2: the beyond-frontier (`xb = true`) card path -/

#eval (List.range 5).map (fun t => (rowOf M2 [] t 8).map Fin.val)

#eval (List.range 5).all (fun t =>
  validStepB (cookCards M2) (rowOf M2 [] t 8) (rowOf M2 [] (t + 1) 8))
-- expect: true

#eval validStepB (cookCards M2) (rowOf M2 [] 5 8) (rowOf M2 [] 5 8)
-- expect: true (halt freeze)

/-! ### The final patterns -/

-- M1's halting row contains a final pattern (singleton halting head cell)
#eval (cookFinal M1).any (fun pat =>
  (rowOf M1 [1, 0] 4 9).any (fun c => decide (pat = [c])))
-- expect: true

-- ... and the initial row does not
#eval (cookFinal M1).any (fun pat =>
  (rowOf M1 [1, 0] 0 9).any (fun c => decide (pat = [c])))
-- expect: false

/-! ## §5 Phantom-head regression (2026-07-18-c — the RIGHT boundary marker)

The machine-checked counterexample that forced the right marker: `M4`
self-loops forever (never accepts) but carries an *unreachable* `Lmove`
entry into halting state 1. Under the left-marker-only v2 rows, a spurious
`stepCardInL` head at the row's LAST cell was card-licensed — the last cell
was the only cell contained in no second, refuting window (the
head-at-second-slot absence argument needs a window with the phantom in its
*second* slot, which does not exist at the row edge). The phantom froze
(halting state) and satisfied a final pattern, so
`FlatTCCLang (cookTableau M4 [] steps)` held while `acceptsFlatTM M4 [[]] k`
is false for every `k` — `cookTableau_correct`'s completeness direction was
FALSE. With the right marker, the last coordinate cell sits in the marker
window `(y, z, #)`, whose only covering family (`copyRightCards`) preserves
it — the phantom transition is no longer licensed. -/

def M4 : FlatTM :=
  { sig := 2, tapes := 1, states := 3,
    trans := [
      ⟨0, [none], 0, [none], [TMMove.Nmove]⟩,   -- run forever
      ⟨2, [none], 1, [none], [TMMove.Lmove]⟩],  -- unreachable, into halting 1
    start := 0, halt := [false, true, false] }

#eval (normTrans M4).length                                  -- expect: 2
#eval (List.range 8).map (fun k => acceptsFlatTM M4 [[]] k)  -- expect: all false

/-- Row 0 with a phantom halting head planted at coordinate `j`. -/
def phantomRow (n j : Nat) : List (Fin (Sg M4)) :=
  (rowOf M4 [] 0 n).set j (hCell M4 (stateOf M4 1) (blankSym M4))

-- sanity: the real (self-loop) step is licensed, incl. the marker window
#eval validStepB (cookCards M4) (rowOf M4 [] 0 8) (rowOf M4 [] 1 8)
-- expect: true

-- the phantom at the last coordinate cell is NOT licensed (was TRUE pre-fix)
#eval validStepB (cookCards M4) (rowOf M4 [] 0 8) (phantomRow 8 8)
-- expect: false

-- ... nor at the right marker itself, nor one cell in
#eval validStepB (cookCards M4) (rowOf M4 [] 0 8) (phantomRow 8 9)
-- expect: false
#eval validStepB (cookCards M4) (rowOf M4 [] 0 8) (phantomRow 8 7)
-- expect: false
