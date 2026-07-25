import Complexity.NP.SAT.CookLevin.Reductions.S1Cards

/-! # S1 probe — the stage-C **pure model** of the card stream

Machine-checks `S1Cards.cardBlocks M` (the `List.range`/arithmetic model the
emitter will iterate over) against the real, `Fin`-typed
`GuessTableau.guessCards M` — *before* the equality theorems are proven and
long before the emitter is written (project methodology: probe, then commit
engineering).

§1 the model = the definition, family by family, on six machines
   (valid, halting-state, multi-entry, duplicate keys, `sig = 0`, invalid);
§2 the whole stream, and the tableau's own card register;
§3 the scale: card counts and emitted stream lengths — the numbers that decide
   the emitter's loop structure and its cost ladder.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1CardModelProbe.lean`
-/

open Complexity.Lang Complexity.Simulators S1Cards

/-! ## Test machines -/

/-- The reference valid machine (one transition, state 1 halting). -/
def cM0 : FlatTM :=
  { sig := 2, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some 0],
                dst_state := 1, dst_write_vals := [some 1],
                move_dirs := [TMMove.Rmove] }] }

/-- Three entries, all three moves, a `none` read and a `none` write. -/
def cM1 : FlatTM :=
  { cM0 with
    states := 3, halt := [false, false, true],
    trans := [{ src_state := 0, src_tape_vals := [none],
                dst_state := 1, dst_write_vals := [some 1],
                move_dirs := [TMMove.Lmove] },
              { src_state := 1, src_tape_vals := [some 1],
                dst_state := 2, dst_write_vals := [none],
                move_dirs := [TMMove.Nmove] },
              { src_state := 1, src_tape_vals := [some 0],
                dst_state := 0, dst_write_vals := [some 0],
                move_dirs := [TMMove.Rmove] }] }

/-- Duplicate keys (entries 1 and 3 share `(src_state, src_tape_vals)`) plus an
entry out of a **halting** state — both must be dropped by `normTrans`. -/
def cM2 : FlatTM :=
  { cM1 with
    trans := cM1.trans ++
      [{ src_state := 0, src_tape_vals := [none],
         dst_state := 2, dst_write_vals := [some 0],
         move_dirs := [TMMove.Rmove] },
       { src_state := 2, src_tape_vals := [some 0],
         dst_state := 0, dst_write_vals := [some 0],
         move_dirs := [TMMove.Rmove] }] }

/-- Degenerate alphabet. -/
def cM3 : FlatTM := { cM0 with sig := 0, trans := [] }

/-- No halting state at all. -/
def cM4 : FlatTM := { cM0 with halt := [false, false] }

/-- **Invalid**: arity `2` against `tapes = 1`, an out-of-range `dst_state` and
an out-of-alphabet symbol. The model must still *agree with the definition*
(both are total functions); only the reduction's correctness needs the guard. -/
def cM5 : FlatTM :=
  { cM0 with
    trans := [{ src_state := 0, src_tape_vals := [some 7, none],
                dst_state := 9, dst_write_vals := [some 5, some 1],
                move_dirs := [TMMove.Lmove, TMMove.Nmove] }] }

def cMs : List FlatTM := [cM0, cM1, cM2, cM3, cM4, cM5]

/-! ## §1 — model = definition, family by family -/

def hb (M : FlatTM) : List Nat := M.halt.map S1Parse.bitOf

#eval cMs.map fun M => cardsFlat (copyCards M) == copyBlocks M.sig M.states
#eval cMs.map fun M => cardsFlat (copyRightCards M) == copyRightBlocks M.sig M.states
#eval cMs.map fun M => cardsFlat (haltLeftCards M) == haltLeftBlocks M.sig M.states (hb M)
#eval cMs.map fun M => cardsFlat (haltCenterCards M) == haltCenterBlocks M.sig M.states (hb M)
#eval cMs.map fun M => cardsFlat (haltRightCards M) == haltRightBlocks M.sig M.states (hb M)
#eval cMs.map fun M => cardsFlat (stepCards M) == (normTrans M).flatMap (entryBlocks M)
#eval cMs.map fun M =>
  cardsFlat (preludeCards M) == preludeBlocks M.sig M.states (min M.start M.states)

-- Per-entry, before the dedup/filter pass: the nine-number model of `stepCardsOf`.
#eval cMs.map fun M => M.trans.all fun e => cardsFlat (stepCardsOf M e) == entryBlocks M e

/-! ## §2 — the whole stream -/

#eval cMs.map fun M => cardsFlat (guessCards M) == cardBlocks M

-- Through the tableau: the `CARDS` register the S1 program must write.
#eval cMs.map fun M =>
  ((guessTableau M [1] 2 3).cards.flatMap FlatTCCFree.cardNats) == cardBlocks M

-- And its encoded form, `FlatTCCFree.encNats` of the model.
#eval cMs.map fun M =>
  FlatTCCFree.encCardsIn (guessTableau M [1] 2 3).cards
    == FlatTCCFree.encNats (cardBlocks M)

/-! ## §3 — scale

`(cards, cells)` per family: how many cards the emitter writes and how many
tape cells that is (`encNats`: `value + 1` cells per number). The card register
dwarfs every other output register — the emitter's loop structure, not its
constants, is what has to stay polynomial. -/

def stat (l : List Nat) : Nat × Nat := (l.length / 6, (FlatTCCFree.encNats l).length)

#eval cMs.map fun M => stat (copyBlocks M.sig M.states)
#eval cMs.map fun M => stat (haltCenterBlocks M.sig M.states (hb M))
#eval cMs.map fun M => stat ((normTrans M).flatMap (entryBlocks M))
#eval cMs.map fun M => stat (preludeBlocks M.sig M.states (min M.start M.states))
#eval cMs.map fun M => stat (cardBlocks M)

-- Growth of the whole stream in `sig` (states/trans fixed): the prelude's
-- `Θ(σ⁶)` cards dominate everything else.
#eval (List.range 6).map fun k =>
  stat (cardBlocks { cM0 with sig := k, trans := [] })

-- Growth in `states`.
def famQ (k : Nat) : FlatTM :=
  { cM0 with states := k + 1, halt := List.replicate (k + 1) true, trans := [] }

#eval (List.range 6).map fun k => stat (cardBlocks (famQ k))

-- Growth in the transition count (each entry adds `Θ(σ³)` cards).
def famTEntry (i : Nat) : FlatTMTransEntry :=
  { src_state := i, src_tape_vals := [some 0], dst_state := i + 1,
    dst_write_vals := [some 1], move_dirs := [TMMove.Rmove] }

def famT (k : Nat) : FlatTM :=
  { cM0 with states := k + 2, halt := List.replicate (k + 2) false,
             trans := (List.range (k + 1)).map famTEntry }

#eval (List.range 5).map fun k => stat (cardBlocks (famT k))

/-! ## §4 — the prelude's real order of growth

Only two of the `2σ+5` kinds (`star`, `initStar`) have more than one
resolution, so the prelude card count is `(Σₖ |resOf k|)³ = (4σ+5)³` *before*
the `contigOK` filter — **cubic in `σ`, not sextic**. `preludeCards_length_le`
(`(5+2σ)³·(σ+1)³`) is a very loose over-estimate; the emitter's nest is six
loops deep but does only cubic work. -/

def preludeCount (M : FlatTM) : Nat :=
  (preludeBlocks M.sig M.states (min M.start M.states)).length / 6

-- actual count vs the closed form `(4σ+5)³` (the pre-filter upper bound)
#eval (List.range 6).map fun k =>
  (preludeCount { cM0 with sig := k }, (4 * k + 5) ^ 3)

-- the count does not depend on `states` at all (the prelude band is Γ-free
-- except through `hv`), so the emitter's prelude nest is `σ`-only
#eval (List.range 4).map fun k => preludeCount (famQ k)
