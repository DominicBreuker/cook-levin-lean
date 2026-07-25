import Complexity.NP.SAT.CookLevin.Reductions.S1Parse
import Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC_free

set_option autoImplicit false
set_option maxRecDepth 4000

/-! # S1, part 4 — the **pure model of stage C** (the card emitter)

Stage C of `S1Witness.s1Program` must write

    FlatTCCFree.encCardsIn (flattenCard <$> GuessTableau.guessCards M)

into the `CARDS` register. `guessCards` is a `Fin`-typed, `finRange`-driven,
`filterMap`-filtered nest — *nothing* a `Cmd` can iterate over. This file
restates it as a **machine-shaped stream**: nested `flatMap`s over
`List.range`, every cell code given by linear/product arithmetic in the numbers
stage P already parsed (`sig`, `states`, `start`, the halt bit list, and the
five numbers of each transition entry).

Methodology (template: `mScan_eq_fsatToSat` in `NP/FSAT_to_SAT_pre.lean`):
**prove the machine folds compute a pure model, then close with model ≡
definition.** This file is the second half — the model and its equality with
the definition — written *before* the emitter, so the emitter is written once.
Numerically cross-checked in `probes/S1CardModelProbe.lean`.

## What the emitter has to iterate over

`cardBlocks M` is a concatenation of seven independent streams, in this order
(`σ = M.sig`, `Q = M.states`, `T = |M.trans|`):

| stream | loop nest | cards |
|---|---|---|
| `copyBlocks` | `x < σ+2`, `b < σ+1`, `c < σ+1` | `Θ(σ³)` |
| `copyRightBlocks` | `y,z < σ+1` | `Θ(σ²)` |
| `haltLeftBlocks` | `q < Q+1` (halting only), `b,y,z < σ+1` | `Θ(Q·σ³)` |
| `haltCenterBlocks` | `q`, `b < σ+1`, `x < σ+2`, `z < σ+1` | `Θ(Q·σ³)` |
| `haltRightBlocks` | `q`, `b`, `x`, `y` | `Θ(Q·σ³)` |
| `entryBlocks` per entry | four sub-nests, ≤ 3 deep | `Θ(σ³)` each |
| `preludeBlocks` | `k1,k2,k3 < 2σ+5`, then `pBody`'s three resolution loops | `≤ (4σ+5)³` |

Every block is six numbers `< PSg M ≈ σ·Q`, emitted as six bare unary blocks
(`FlatTCCFree.encNat` = `1^v 0`).

⚠ **The prelude is `Θ(σ³)`, not `Θ(σ⁶)`** (measured, `probes/S1CardModelProbe.lean`
§3–4): only two of the `2σ+5` kinds (`star`, `initStar`) have more than one
resolution, so the innermost count is `(Σₖ |resOf k|)³ = (4σ+5)³`. The existing
`GuessTableau.preludeCards_length_le` bound (`(5+2σ)³·(σ+1)³`) is a *very* loose
over-estimate; the emitter's real nest is six loops but only cubic work.
Total card count is therefore `Θ((1 + Q + T)·σ³)`.

## Cost consequences for the emitter (read before writing a single `Cmd`)

* **Never `concat` onto the card register.** `Op.cost (concat dst a b)
  = 2(|a|+|b|)+1` charges the *whole* register per append, which would make the
  emitter quadratic in its own `Θ(n⁵)` output. Emit with `appendOne`/
  `appendZero` (unit cost) inside a `forBnd` — the `emitConst`/`tallyReg`
  pattern of `Reductions/FrontPieces.lean`.
* **A unary block of value `v` costs `Θ(v²)`,** because `Cmd.run`'s `forBnd`
  charges `iters²` for materialising its counter. With `v < PSg ≈ σ·Q` and
  `Θ((1+Q+T)σ³)` cards that is `Θ(n⁴)` per block and `Θ(n⁸)` overall — inside
  the degree-10 `cost_bound`, but with only two orders of slack.
* **Hoist every product out of the inner loops.** `hv sig q b = (σ+1)(q+1)+b`
  must be maintained incrementally (append `1^(σ+1)` once per `q` iteration),
  never recomputed with `unaryMulLoop` per card.
* **If the ladder still does not fit, raise `cost_bound`.** It is a free
  polynomial choice: `PolyTimeComputableLang.cost_bound` must dominate the cost
  *and* the output size, and `S1Map.s1Map_size_le` composes with any bigger
  monotone polynomial. Do not contort the emitter to hit degree 10.

## The three design facts this file pins

1. **`emb` is a no-op on the flat encoding** (`cnats_embCard`): the emitter
   never applies `emb`, and the deterministic cards and the prelude cards are
   two *independent* streams (`cardBlocks_eq`, via `List.flatMap_append`).
2. **The prelude premise cell of kind index `k` is literally `Sg M + k`**
   (`pcellv`): the premise triple of a prelude card needs no case analysis at
   all — three counters offset by `Sg M`. The *conclusion* side runs over
   `resOf k`, which the emitter should materialise into a register per kind
   (values and class codes interleaved) and then scan three times — that turns
   the kind dispatch into one stream loop instead of seven branches.
3. **The step cards depend on the entry only through nine numbers**
   (`stepBlocks`): `sig`, `states`, `q`, `q'`, `mTag`, `mVal`, `wTag`, `wVal`,
   `mv` — exactly the fields `S1Parse`'s entry scan already walks past. The
   `Option Nat` fields enter as the `(tag, val)` pair of `HeadLayout.encOptN`,
   which is how they sit in the stream.

## The one gadget that is not a nested loop

`stepCards M = (normTrans M).flatMap (stepCardsOf M)` runs over
`normTrans M = (dedupKeys M.trans).filter (entryOK M)`, i.e. a **key-deduped,
filtered sub-stream**. `normModel`/`normModel_eq` below are its on-machine
specification (three-number keys, one halt-bit lookup); see the section note
there. -/

namespace S1Cards

open Complexity.Lang Complexity.Simulators HeadLayout

/-! ## Generic list plumbing

`cnats` is "the six numbers of a `Fin`-typed card"; `cardsFlat` maps it over a
card list. Everything below is `cardsFlat` pushed through the four list
combinators the definitions are built from. -/

/-- The six flat numbers of a typed card (`flattenCard` then `cardNats`). -/
def cnats {k : Nat} (c : TCCCard (Fin k)) : List Nat :=
  [c.prem.cardEl1.1, c.prem.cardEl2.1, c.prem.cardEl3.1,
   c.conc.cardEl1.1, c.conc.cardEl2.1, c.conc.cardEl3.1]

theorem cnats_eq {k : Nat} (c : TCCCard (Fin k)) :
    FlatTCCFree.cardNats (FlatTCC.flattenCard c) = cnats c := rfl

/-- A card list as one flat number stream. -/
def cardsFlat {k : Nat} (cs : List (TCCCard (Fin k))) : List Nat := cs.flatMap cnats

theorem cardsFlat_eq {k : Nat} (cs : List (TCCCard (Fin k))) :
    (cs.map FlatTCC.flattenCard).flatMap FlatTCCFree.cardNats = cardsFlat cs := by
  rw [List.flatMap_map]; rfl

theorem cardsFlat_append {k : Nat} (as bs : List (TCCCard (Fin k))) :
    cardsFlat (as ++ bs) = cardsFlat as ++ cardsFlat bs := List.flatMap_append ..

theorem cardsFlat_flatMap {α : Type} {k : Nat} (l : List α)
    (f : α → List (TCCCard (Fin k))) :
    cardsFlat (l.flatMap f) = l.flatMap (fun a => cardsFlat (f a)) := List.flatMap_assoc

theorem cardsFlat_map {α : Type} {k : Nat} (l : List α) (f : α → TCCCard (Fin k)) :
    cardsFlat (l.map f) = l.flatMap (fun a => cnats (f a)) := List.flatMap_map ..

theorem cardsFlat_filterMap {α : Type} {k : Nat} (l : List α)
    (f : α → Option (TCCCard (Fin k))) :
    cardsFlat (l.filterMap f) = l.flatMap (fun a => (f a).elim [] cnats) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases h : f a with
      | none => rw [List.filterMap_cons_none h]; simp [ih, h]
      | some b =>
          rw [List.filterMap_cons_some h]
          simp only [cardsFlat, List.flatMap_cons] at ih ⊢
          rw [ih, h]
          rfl

/-- `encNats` is a monoid homomorphism (the emitter appends block by block). -/
theorem encNats_append (xs ys : List Nat) :
    FlatTCCFree.encNats (xs ++ ys)
      = FlatTCCFree.encNats xs ++ FlatTCCFree.encNats ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      show FlatTCCFree.encNat x ++ FlatTCCFree.encNats (xs ++ ys)
        = (FlatTCCFree.encNat x ++ FlatTCCFree.encNats xs) ++ _
      rw [ih, List.append_assoc]

/-- The card register is `encNats` of the flat 6-nat blocks — no sentinels,
fixed arity. -/
theorem encCardsIn_eq_encNats (cs : List (TCCCard Nat)) :
    FlatTCCFree.encCardsIn cs
      = FlatTCCFree.encNats (cs.flatMap FlatTCCFree.cardNats) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show FlatTCCFree.encCardIn c ++ FlatTCCFree.encCardsIn cs = _
      rw [ih, List.flatMap_cons, encNats_append]
      rfl

/-- **The counter change of variables**: a `finRange` nest that only uses its
indices' values is a `List.range` nest. Every family below closes with this. -/
theorem flatMap_finRange {α : Type} (n : Nat) (g : Nat → List α) :
    (List.finRange n).flatMap (fun i => g i.1) = (List.range n).flatMap g := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]

/-! ## The cell codes, as arithmetic

`tCell M b = b`, `hCell M q b = (sig+1)·(q+1) + b`, `bCell M = (sig+1)·(states+2)`
and `Sg M = bCell M + 1` — all of them linear/product arithmetic in the two
parsed numbers, i.e. `unaryMulLoop_run` shapes (design fact 3 of
`S1Witness`). -/

/-- The boundary-marker code. -/
def bv (sig states : Nat) : Nat := (sig + 1) * (states + 2)

/-- The alphabet size of the deterministic core (`Sg`). -/
def sgv (sig states : Nat) : Nat := bv sig states + 1

/-- The head-cell code for state `q` reading symbol `b`. -/
def hv (sig q b : Nat) : Nat := (sig + 1) * (q + 1) + b

/-- The left-context code of `xOpts` index `x`: index `0` is the boundary
marker, index `i+1` the tape cell `i`. -/
def xv (sig states x : Nat) : Nat := if x = 0 then bv sig states else x - 1

/-- One card as six numbers, premise first. -/
def blk (p1 p2 p3 c1 c2 c3 : Nat) : List Nat := [p1, p2, p3, c1, c2, c3]

theorem bv_eq (M : FlatTM) : (bCell M).1 = bv M.sig M.states := rfl
theorem sgv_eq (M : FlatTM) : Sg M = sgv M.sig M.states := rfl
theorem hv_eq (M : FlatTM) (q : Fin (M.states + 1)) (b : Fin (M.sig + 1)) :
    (hCell M q b).1 = hv M.sig q.1 b.1 := rfl
theorem tv_eq (M : FlatTM) (b : Fin (M.sig + 1)) : (tCell M b).1 = b.1 := rfl

/-- The same change of variables for a `map` level. -/
theorem map_finRange_congr {α : Type} (n : Nat) (f : Fin n → α) (g : Nat → α)
    (h : ∀ i : Fin n, f i = g i.1) :
    (List.finRange n).map f = (List.range n).map g := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  exact List.map_congr_left (fun i _ => h i)

/-- Rewriting one `finRange` nest level into a `range` nest level. -/
theorem finRange_flatMap_congr {α : Type} (n : Nat) (f : Fin n → List α)
    (g : Nat → List α) (h : ∀ i : Fin n, f i = g i.1) :
    (List.finRange n).flatMap f = (List.range n).flatMap g := by
  rw [← flatMap_finRange n g]
  exact List.flatMap_congr (fun i _ => h i)

/-- The `xOpts` enumeration as a `List.range`: `xOpts M` has `sig+2` entries,
index `0` the boundary marker and index `i+1` the tape symbol `i`. The
"is the blank cell" flag (`xIsBlank`, i.e. "the head is past the frontier") is
then exactly "index `= sig+1`" and the boundary-marker case exactly
"index `= 0`" — the two tests the model's step families branch on. -/
theorem xOpts_flatMap {α : Type} (M : FlatTM) (f : Option (Fin (M.sig + 1)) → List α)
    (g : Nat → List α) (h0 : f none = g 0)
    (hs : ∀ a : Fin (M.sig + 1), f (some a) = g (a.1 + 1)) :
    (xOpts M).flatMap f = (List.range (M.sig + 2)).flatMap g := by
  rw [List.range_succ_eq_map]
  simp only [xOpts, List.flatMap_cons, List.flatMap_map, h0]
  congr 1
  exact finRange_flatMap_congr _ _ _ (fun a => hs a)

/-- The value/blank-flag pair at `xOpts` index `0`. -/
theorem xv_zero (sig states : Nat) : xv sig states 0 = bv sig states := rfl

/-- …and at index `a+1`. -/
theorem xv_succ (sig states a : Nat) : xv sig states (a + 1) = a := by simp [xv]

theorem xIsBlank_eq (M : FlatTM) (a : Fin (M.sig + 1)) :
    xIsBlank M (some a) = decide (a.1 + 1 = M.sig + 1) := by
  simp [xIsBlank, blankSym, Fin.ext_iff]

theorem xIsBlank_none (M : FlatTM) : xIsBlank M none = decide ((0 : Nat) = M.sig + 1) := by
  simp [xIsBlank]

/-! ## The deterministic families

One `def` per card family of `Simulators/CookTableau.lean`, each a `List.range`
nest over the parsed numbers, plus the equation identifying it with
`cardsFlat` of the family. -/

/-- `copyCards`: identity away from the head. -/
def copyBlocks (sig states : Nat) : List Nat :=
  (List.range (sig + 2)).flatMap (fun x =>
    (List.range (sig + 1)).flatMap (fun b =>
      (List.range (sig + 1)).flatMap (fun c =>
        blk (xv sig states x) b c (xv sig states x) b c)))

/-- `copyRightCards`: identity at the right boundary marker. -/
def copyRightBlocks (sig states : Nat) : List Nat :=
  (List.range (sig + 1)).flatMap (fun y =>
    (List.range (sig + 1)).flatMap (fun z =>
      blk y z (bv sig states) y z (bv sig states)))

/-- Is state `q` halting, read off the raw halt **bit list** (`S1Parse.PHALT`)?
`M.halt.map bitOf` and `M.halt` agree here for every `q`, in range or not
(`haltBit_eq`). -/
def haltBit (hbits : List Nat) (q : Nat) : Bool := decide (hbits.getD q 0 = 1)

/-- `haltLeftCards`: halt freeze, head at the window's first cell. -/
def haltLeftBlocks (sig states : Nat) (hbits : List Nat) : List Nat :=
  (List.range (states + 1)).flatMap (fun q =>
    if haltBit hbits q then
      (List.range (sig + 1)).flatMap (fun b =>
        (List.range (sig + 1)).flatMap (fun y =>
          (List.range (sig + 1)).flatMap (fun z =>
            blk (hv sig q b) y z (hv sig q b) y z)))
    else [])

/-- `haltCenterCards`: halt freeze, head at the window's center. -/
def haltCenterBlocks (sig states : Nat) (hbits : List Nat) : List Nat :=
  (List.range (states + 1)).flatMap (fun q =>
    if haltBit hbits q then
      (List.range (sig + 1)).flatMap (fun b =>
        (List.range (sig + 2)).flatMap (fun x =>
          (List.range (sig + 1)).flatMap (fun z =>
            blk (xv sig states x) (hv sig q b) z
                (xv sig states x) (hv sig q b) z)))
    else [])

/-- `haltRightCards`: halt freeze, head at the window's third cell. -/
def haltRightBlocks (sig states : Nat) (hbits : List Nat) : List Nat :=
  (List.range (states + 1)).flatMap (fun q =>
    if haltBit hbits q then
      (List.range (sig + 1)).flatMap (fun b =>
        (List.range (sig + 2)).flatMap (fun x =>
          (List.range (sig + 1)).flatMap (fun y =>
            blk (xv sig states x) y (hv sig q b)
                (xv sig states x) y (hv sig q b))))
    else [])

/-! ## The transition families

The nine numbers a step entry contributes: `sig`, `states`, the two clamped
states `q`/`q'`, the read option as `(mTag, mVal)`, the write option as
`(wTag, wVal)` (`HeadLayout.encOptN`: tag `0` = `none`, tag `1` = `some val`)
and the move code `mv` (`HeadLayout.encMoveN`: `0 = L`, `1 = R`, `2 = N`). -/

/-- The symbol read under the head (`optSym`). -/
def rOf (sig mTag mVal : Nat) : Nat := if mTag = 0 then sig else min mVal sig

/-- The effective written symbol (`wEff`); `xb` = "the head's left neighbour is
the blank cell", i.e. the head is strictly beyond the frontier, where
`some`-writes are void. -/
def wOf (sig mTag mVal wTag wVal : Nat) (xb : Bool) : Nat :=
  if wTag = 0 then rOf sig mTag mVal
  else if (decide (mTag = 0) && xb) then sig else min wVal sig

/-- `stepCardCenter` over all `(x, z)`. -/
def stepCenterBlocks (sig states q q' mTag mVal wTag wVal mv : Nat) : List Nat :=
  (List.range (sig + 2)).flatMap (fun x =>
    (List.range (sig + 1)).flatMap (fun z =>
      let X := xv sig states x
      let W := wOf sig mTag mVal wTag wVal (decide (x = sig + 1))
      let P1 := X
      let P2 := hv sig q (rOf sig mTag mVal)
      if mv = 2 then blk P1 P2 z X (hv sig q' W) z
      else if mv = 1 then blk P1 P2 z X W (hv sig q' z)
      else if x = 0 then blk P1 P2 z (bv sig states) (hv sig q' W) z
      else blk P1 P2 z (hv sig q' (x - 1)) W z))

/-- `stepCardsLeft` over both frontier variants and all `(y, z)`. -/
def stepLeftBlocks (sig q q' mTag mVal wTag wVal mv : Nat) : List Nat :=
  (List.range 2).flatMap (fun i =>
    (List.range (sig + 1)).flatMap (fun y =>
      (List.range (sig + 1)).flatMap (fun z =>
        let W := wOf sig mTag mVal wTag wVal (decide (i = 1))
        let P1 := hv sig q (rOf sig mTag mVal)
        if mv = 2 then blk P1 y z (hv sig q' W) y z
        else if mv = 1 then blk P1 y z W (hv sig q' y) z
        else blk P1 y z W y z ++ blk P1 y z (hv sig q' W) y z)))

/-- `stepCardRight` over all `(x, y)`. -/
def stepRightBlocks (sig states q q' mTag mVal wTag wVal mv : Nat) : List Nat :=
  (List.range (sig + 2)).flatMap (fun x =>
    (List.range (sig + 1)).flatMap (fun y =>
      let X := xv sig states x
      let W := wOf sig mTag mVal wTag wVal (decide (y = sig))
      let P3 := hv sig q (rOf sig mTag mVal)
      if mv = 2 then blk X y P3 X y (hv sig q' W)
      else if mv = 1 then blk X y P3 X y W
      else blk X y P3 X (hv sig q' y) W))

/-- The incoming-head families (`stepCardInR` / `stepCardInL`). -/
def stepInBlocks (sig states q' mv : Nat) : List Nat :=
  if mv = 1 then
    (List.range (sig + 1)).flatMap (fun y =>
      (List.range (sig + 1)).flatMap (fun z =>
        (List.range (sig + 1)).flatMap (fun u =>
          blk y z u (hv sig q' y) z u)))
  else if mv = 0 then
    (List.range (sig + 2)).flatMap (fun x =>
      (List.range (sig + 1)).flatMap (fun y =>
        (List.range (sig + 1)).flatMap (fun c =>
          blk (xv sig states x) y c (xv sig states x) y (hv sig q' c))))
  else []

/-- **All cards of one normalised transition entry**, as a function of the nine
numbers the entry contributes. -/
def stepBlocks (sig states q q' mTag mVal wTag wVal mv : Nat) : List Nat :=
  stepCenterBlocks sig states q q' mTag mVal wTag wVal mv ++
  stepLeftBlocks sig q q' mTag mVal wTag wVal mv ++
  stepRightBlocks sig states q q' mTag mVal wTag wVal mv ++
  stepInBlocks sig states q' mv

/-! ## The prelude family -/

/-- The resolution list of prelude kind index `k`: pairs `(Γ cell code,
resolution class)` with classes `0 = other`, `1 = live`, `2 = cut`. Only the
two star kinds have more than one resolution. -/
def resOf (sig states q0 k : Nat) : List (Nat × Nat) :=
  if k = 0 then [(bv sig states, 0)]
  else if k = 1 then [(sig, 0)]
  else if k = 2 then (List.range sig).map (fun j => (j, 1)) ++ [(sig, 2)]
  else if k = 3 then
    (List.range sig).map (fun j => (hv sig q0 j, 1)) ++ [(hv sig q0 sig, 2)]
  else if k = 4 then [(hv sig q0 sig, 0)]
  else if k < 5 + sig then [(k - 5, 0)]
  else [(hv sig q0 (k - 5 - sig), 0)]

/-- `contigOK` on class codes: no `cut` left of a `live`. -/
def contigB (c1 c2 c3 : Nat) : Bool :=
  !((decide (c1 = 2) && decide (c2 = 1)) || (decide (c1 = 2) && decide (c3 = 1))
    || (decide (c2 = 2) && decide (c3 = 1)))

/-- The prelude cards of one premise kind-index triple: the premise triple is
literally `(Sg+k1, Sg+k2, Sg+k3)`, the conclusions run over all
contiguity-respecting resolutions of the three kinds. -/
def pBody (sig states q0 k1 k2 k3 : Nat) : List Nat :=
  (resOf sig states q0 k1).flatMap (fun r1 =>
    (resOf sig states q0 k2).flatMap (fun r2 =>
      (resOf sig states q0 k3).flatMap (fun r3 =>
        if contigB r1.2 r2.2 r3.2 then
          blk (sgv sig states + k1) (sgv sig states + k2) (sgv sig states + k3)
              r1.1 r2.1 r3.1
        else [])))

/-- `preludeCards`: a triple loop over the kind indices, each innermost
iteration emitting `pBody`. -/
def preludeBlocks (sig states q0 : Nat) : List Nat :=
  (List.range (2 * sig + 5)).flatMap (fun k1 =>
    (List.range (2 * sig + 5)).flatMap (fun k2 =>
      (List.range (2 * sig + 5)).flatMap (pBody sig states q0 k1 k2)))

/-! ## The whole stream -/

/-- The tag of an `Option Nat` in the stream (`HeadLayout.encOptN`). -/
def oTag : Option Nat → Nat
  | none => 0
  | some _ => 1

/-- The payload of an `Option Nat` in the stream. -/
def oVal : Option Nat → Nat
  | none => 0
  | some v => v

/-- **`stepBlocks` at one entry's nine numbers** — the entry as the emitter
sees it: two clamped states, two `(tag, val)` option pairs and a move code. -/
def entryBlocks (M : FlatTM) (e : FlatTMTransEntry) : List Nat :=
  stepBlocks M.sig M.states (min e.src_state M.states) (min e.dst_state M.states)
    (oTag (e.src_tape_vals.headD none)) (oVal (e.src_tape_vals.headD none))
    (oTag (e.dst_write_vals.headD none)) (oVal (e.dst_write_vals.headD none))
    (encMoveN (e.move_dirs.headD TMMove.Nmove))

/-- **The stage-C target stream**: the six numbers of every card of
`guessCards M`, in order. -/
def cardBlocks (M : FlatTM) : List Nat :=
  copyBlocks M.sig M.states ++
  copyRightBlocks M.sig M.states ++
  haltLeftBlocks M.sig M.states (M.halt.map S1Parse.bitOf) ++
  haltCenterBlocks M.sig M.states (M.halt.map S1Parse.bitOf) ++
  haltRightBlocks M.sig M.states (M.halt.map S1Parse.bitOf) ++
  (normTrans M).flatMap (entryBlocks M) ++
  preludeBlocks M.sig M.states (min M.start M.states)

/-! ## Model = definition, family by family -/

theorem copyCards_flat (M : FlatTM) :
    cardsFlat (copyCards M) = copyBlocks M.sig M.states := by
  have key : ∀ X : Fin (Sg M),
      cardsFlat ((List.finRange (M.sig + 1)).flatMap (fun b =>
          (List.finRange (M.sig + 1)).map (fun c =>
            copyCard M X (tCell M b) (tCell M c))))
        = (List.range (M.sig + 1)).flatMap (fun b =>
            (List.range (M.sig + 1)).flatMap (fun c => blk X.1 b c X.1 b c)) := by
    intro X
    rw [cardsFlat_flatMap]
    refine finRange_flatMap_congr _ _ _ (fun b => ?_)
    rw [cardsFlat_map]
    exact finRange_flatMap_congr _ _ _ (fun c => rfl)
  unfold copyCards copyBlocks
  rw [cardsFlat_flatMap]
  refine xOpts_flatMap M _ _ ?_ (fun a => ?_)
  · rw [key]; rfl
  · rw [key]; rw [xv_succ]; rfl

theorem copyRightCards_flat (M : FlatTM) :
    cardsFlat (copyRightCards M) = copyRightBlocks M.sig M.states := by
  unfold copyRightCards copyRightBlocks
  rw [cardsFlat_flatMap]
  refine finRange_flatMap_congr _ _ _ (fun y => ?_)
  rw [cardsFlat_map]
  exact finRange_flatMap_congr _ _ _ (fun z => rfl)

/-- The raw halt **bit list** (`S1Parse.PHALT`) decides exactly what
`M.halt.getD` does — at every index, in range or not. -/
theorem haltBit_eq (M : FlatTM) (q : Nat) :
    haltBit (M.halt.map S1Parse.bitOf) q = M.halt.getD q false := by
  unfold haltBit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : M.halt[q]? with
  | none => rfl
  | some b => cases b <;> rfl

theorem haltLeftCards_flat (M : FlatTM) :
    cardsFlat (haltLeftCards M)
      = haltLeftBlocks M.sig M.states (M.halt.map S1Parse.bitOf) := by
  unfold haltLeftCards haltLeftBlocks
  rw [cardsFlat_flatMap]
  refine finRange_flatMap_congr _ _ _ (fun q => ?_)
  rw [haltBit_eq]
  by_cases h : M.halt.getD q.1 false <;> simp only [h, if_true, if_false]
  · rw [cardsFlat_flatMap]
    refine finRange_flatMap_congr _ _ _ (fun b => ?_)
    rw [cardsFlat_flatMap]
    refine finRange_flatMap_congr _ _ _ (fun y => ?_)
    rw [cardsFlat_map]
    exact finRange_flatMap_congr _ _ _ (fun z => rfl)
  · rfl

theorem haltCenterCards_flat (M : FlatTM) :
    cardsFlat (haltCenterCards M)
      = haltCenterBlocks M.sig M.states (M.halt.map S1Parse.bitOf) := by
  unfold haltCenterCards haltCenterBlocks
  rw [cardsFlat_flatMap]
  refine finRange_flatMap_congr _ _ _ (fun q => ?_)
  rw [haltBit_eq]
  by_cases h : M.halt.getD q.1 false <;> simp only [h, if_true, if_false]
  · rw [cardsFlat_flatMap]
    refine finRange_flatMap_congr _ _ _ (fun b => ?_)
    have key : ∀ X : Fin (Sg M),
        cardsFlat ((List.finRange (M.sig + 1)).map (fun z =>
            copyCard M X (hCell M q b) (tCell M z)))
          = (List.range (M.sig + 1)).flatMap (fun z =>
              blk X.1 (hv M.sig q.1 b.1) z X.1 (hv M.sig q.1 b.1) z) := by
      intro X
      rw [cardsFlat_map]
      exact finRange_flatMap_congr _ _ _ (fun z => rfl)
    rw [cardsFlat_flatMap]
    refine xOpts_flatMap M _ _ ?_ (fun a => ?_)
    · rw [key]; rfl
    · rw [key]; rw [xv_succ]; rfl
  · rfl

theorem haltRightCards_flat (M : FlatTM) :
    cardsFlat (haltRightCards M)
      = haltRightBlocks M.sig M.states (M.halt.map S1Parse.bitOf) := by
  unfold haltRightCards haltRightBlocks
  rw [cardsFlat_flatMap]
  refine finRange_flatMap_congr _ _ _ (fun q => ?_)
  rw [haltBit_eq]
  by_cases h : M.halt.getD q.1 false <;> simp only [h, if_true, if_false]
  · rw [cardsFlat_flatMap]
    refine finRange_flatMap_congr _ _ _ (fun b => ?_)
    have key : ∀ X : Fin (Sg M),
        cardsFlat ((List.finRange (M.sig + 1)).map (fun y =>
            copyCard M X (tCell M y) (hCell M q b)))
          = (List.range (M.sig + 1)).flatMap (fun y =>
              blk X.1 y (hv M.sig q.1 b.1) X.1 y (hv M.sig q.1 b.1)) := by
      intro X
      rw [cardsFlat_map]
      exact finRange_flatMap_congr _ _ _ (fun y => rfl)
    rw [cardsFlat_flatMap]
    refine xOpts_flatMap M _ _ ?_ (fun a => ?_)
    · rw [key]; rfl
    · rw [key]; rw [xv_succ]; rfl
  · rfl

/-! ### The transition families

`optSym`/`wEff` are the two arithmetic functions the emitter has to reproduce
from the `(tag, val)` pairs the stream carries. -/

theorem rOf_eq (M : FlatTM) (m : Option Nat) :
    rOf M.sig (oTag m) (oVal m) = (optSym M m).1 := by
  cases m <;> rfl

theorem wOf_eq (M : FlatTM) (m w : Option Nat) (xb : Bool) :
    wOf M.sig (oTag m) (oVal m) (oTag w) (oVal w) xb = (wEff M m w xb).1 := by
  cases w <;> cases m <;> cases xb <;> rfl

private theorem stepCenter_flat (M : FlatTM) (q q' : Fin (M.states + 1))
    (m w : Option Nat) (mv : TMMove) :
    cardsFlat ((xOpts M).flatMap (fun x =>
        (List.finRange (M.sig + 1)).map (fun z => stepCardCenter M q q' m w mv x z)))
      = stepCenterBlocks M.sig M.states q.1 q'.1 (oTag m) (oVal m) (oTag w) (oVal w)
          (encMoveN mv) := by
  unfold stepCenterBlocks
  rw [cardsFlat_flatMap]
  refine xOpts_flatMap M _ _ ?_ (fun a => ?_)
  · rw [cardsFlat_map]
    refine finRange_flatMap_congr _ _ _ (fun z => ?_)
    rw [rOf_eq, wOf_eq, ← xIsBlank_none M, xv_zero]
    cases mv <;> rfl
  · rw [cardsFlat_map]
    refine finRange_flatMap_congr _ _ _ (fun z => ?_)
    rw [rOf_eq, wOf_eq, ← xIsBlank_eq M a, xv_succ]
    cases mv <;> rfl

private theorem stepLeft_flat (M : FlatTM) (q q' : Fin (M.states + 1))
    (m w : Option Nat) (mv : TMMove) :
    cardsFlat ([false, true].flatMap (fun xb =>
        (List.finRange (M.sig + 1)).flatMap (fun y =>
          (List.finRange (M.sig + 1)).flatMap (fun z =>
            stepCardsLeft M q q' m w mv xb y z))))
      = stepLeftBlocks M.sig q.1 q'.1 (oTag m) (oVal m) (oTag w) (oVal w)
          (encMoveN mv) := by
  unfold stepLeftBlocks
  have inner : ∀ xb : Bool,
      cardsFlat ((List.finRange (M.sig + 1)).flatMap (fun y =>
          (List.finRange (M.sig + 1)).flatMap (fun z =>
            stepCardsLeft M q q' m w mv xb y z)))
        = (List.range (M.sig + 1)).flatMap (fun y =>
            (List.range (M.sig + 1)).flatMap (fun z =>
              let W := wOf M.sig (oTag m) (oVal m) (oTag w) (oVal w) xb
              let P1 := hv M.sig q.1 (rOf M.sig (oTag m) (oVal m))
              if encMoveN mv = 2 then blk P1 y z (hv M.sig q'.1 W) y z
              else if encMoveN mv = 1 then blk P1 y z W (hv M.sig q'.1 y) z
              else blk P1 y z W y z ++ blk P1 y z (hv M.sig q'.1 W) y z)) := by
    intro xb
    rw [cardsFlat_flatMap]
    refine finRange_flatMap_congr _ _ _ (fun y => ?_)
    rw [cardsFlat_flatMap]
    refine finRange_flatMap_congr _ _ _ (fun z => ?_)
    simp only [rOf_eq, wOf_eq]
    cases mv <;> rfl
  have hr2 : ∀ (g : Nat → List Nat), (List.range 2).flatMap g = g 0 ++ g 1 := by
    intro g; simp [List.range_succ]
  show cardsFlat (_ ++ (_ ++ [])) = _
  rw [cardsFlat_append, cardsFlat_append, hr2, inner false, inner true]
  simp [cardsFlat]

private theorem stepRight_flat (M : FlatTM) (q q' : Fin (M.states + 1))
    (m w : Option Nat) (mv : TMMove) :
    cardsFlat ((xOpts M).flatMap (fun x =>
        (List.finRange (M.sig + 1)).map (fun y => stepCardRight M q q' m w mv x y)))
      = stepRightBlocks M.sig M.states q.1 q'.1 (oTag m) (oVal m) (oTag w) (oVal w)
          (encMoveN mv) := by
  unfold stepRightBlocks
  have key : ∀ X : Option (Fin (M.sig + 1)), ∀ v : Nat, (xCell M X).1 = v →
      cardsFlat ((List.finRange (M.sig + 1)).map (fun y =>
          stepCardRight M q q' m w mv X y))
        = (List.range (M.sig + 1)).flatMap (fun y =>
            let W := wOf M.sig (oTag m) (oVal m) (oTag w) (oVal w) (decide (y = M.sig))
            let P3 := hv M.sig q.1 (rOf M.sig (oTag m) (oVal m))
            if encMoveN mv = 2 then blk v y P3 v y (hv M.sig q'.1 W)
            else if encMoveN mv = 1 then blk v y P3 v y W
            else blk v y P3 v (hv M.sig q'.1 y) W) := by
    intro X v hv0
    rw [cardsFlat_map]
    refine finRange_flatMap_congr _ _ _ (fun y => ?_)
    have hy : (decide (y = blankSym M)) = decide (y.1 = M.sig) := by
      simp [blankSym, Fin.ext_iff]
    subst hv0
    cases mv <;>
      simp only [stepCardRight, cnats, encMoveN, blk, tv_eq, hv_eq, hy,
        rOf_eq, wOf_eq, if_true, if_false, reduceIte]
    all_goals rfl
  rw [cardsFlat_flatMap]
  refine xOpts_flatMap M _ _ ?_ (fun a => ?_)
  · rw [key none (bv M.sig M.states) rfl, xv_zero]
  · rw [key (some a) a rfl, xv_succ]

private theorem stepIn_flat (M : FlatTM) (q' : Fin (M.states + 1)) (mv : TMMove) :
    cardsFlat (match mv with
      | TMMove.Rmove =>
          (List.finRange (M.sig + 1)).flatMap (fun y =>
            (List.finRange (M.sig + 1)).flatMap (fun z =>
              (List.finRange (M.sig + 1)).map (fun u => stepCardInR M q' y z u)))
      | TMMove.Lmove =>
          (xOpts M).flatMap (fun x =>
            (List.finRange (M.sig + 1)).flatMap (fun y =>
              (List.finRange (M.sig + 1)).map (fun c => stepCardInL M q' x y c)))
      | TMMove.Nmove => [])
      = stepInBlocks M.sig M.states q'.1 (encMoveN mv) := by
  unfold stepInBlocks
  cases mv with
  | Nmove => rfl
  | Rmove =>
      show cardsFlat _ = _
      simp only [encMoveN, if_true, reduceIte]
      rw [cardsFlat_flatMap]
      refine finRange_flatMap_congr _ _ _ (fun y => ?_)
      rw [cardsFlat_flatMap]
      refine finRange_flatMap_congr _ _ _ (fun z => ?_)
      rw [cardsFlat_map]
      exact finRange_flatMap_congr _ _ _ (fun u => rfl)
  | Lmove =>
      show cardsFlat _ = _
      simp only [encMoveN, if_false, reduceIte]
      have inner : ∀ X : Option (Fin (M.sig + 1)), ∀ v : Nat, (xCell M X).1 = v →
          cardsFlat ((List.finRange (M.sig + 1)).flatMap (fun y =>
              (List.finRange (M.sig + 1)).map (fun c => stepCardInL M q' X y c)))
            = (List.range (M.sig + 1)).flatMap (fun y =>
                (List.range (M.sig + 1)).flatMap (fun c =>
                  blk v y c v y (hv M.sig q'.1 c))) := by
        intro X v hv0
        subst hv0
        rw [cardsFlat_flatMap]
        refine finRange_flatMap_congr _ _ _ (fun y => ?_)
        rw [cardsFlat_map]
        exact finRange_flatMap_congr _ _ _ (fun c => rfl)
      rw [cardsFlat_flatMap]
      refine xOpts_flatMap M _ _ ?_ (fun a => ?_)
      · rw [inner none (bv M.sig M.states) rfl, xv_zero]
      · rw [inner (some a) a rfl, xv_succ]

/-- **One transition entry's cards are nine numbers of arithmetic.** No
validity hypothesis: `stepCardsOf` reads its fields with `headD`, so the
equation holds for malformed entries too (probe case `cM5`). -/
theorem stepCardsOf_flat (M : FlatTM) (e : FlatTMTransEntry) :
    cardsFlat (stepCardsOf M e) = entryBlocks M e := by
  unfold stepCardsOf entryBlocks stepBlocks
  rw [cardsFlat_append, cardsFlat_append, cardsFlat_append,
    stepCenter_flat, stepLeft_flat, stepRight_flat]
  congr 1
  exact stepIn_flat M (stateOf M e.dst_state) (e.move_dirs.headD TMMove.Nmove)

theorem stepCards_flat (M : FlatTM) :
    cardsFlat (stepCards M) = (normTrans M).flatMap (entryBlocks M) := by
  unfold stepCards
  rw [cardsFlat_flatMap]
  exact List.flatMap_congr (fun e _ => stepCardsOf_flat M e)

/-! ### The prelude family -/

/-- The index of a prelude cell kind in the emitter's enumeration. -/
def kindIdx (M : FlatTM) : PKind M → Nat
  | .delim => 0
  | .blank => 1
  | .star => 2
  | .initStar => 3
  | .initBlank => 4
  | .fixedSym j => 5 + j.1
  | .initFixedSym j => 5 + M.sig + j.1

/-- **Design fact 2**: the prelude premise cell of kind index `k` is literally
`Sg M + k`. -/
theorem pcellv (M : FlatTM) (k : PKind M) :
    (pCell M k).1 = sgv M.sig M.states + kindIdx M k := by
  cases k <;> simp [pCell, kindIdx, sgv, bv, pDelim, pBlank, pStar, pInitStar,
    pInitBlank, pSig, pInitSig, Sg] <;> omega

/-- The kind enumeration as a `List.range` over `2·sig + 5`. -/
theorem pKindList_flatMap {α : Type} (M : FlatTM) (g : Nat → List α) :
    (pKindList M).flatMap (fun k => g (kindIdx M k))
      = (List.range (2 * M.sig + 5)).flatMap g := by
  have hsplit : 2 * M.sig + 5 = 5 + M.sig + M.sig := by omega
  have hF : (List.finRange M.sig).flatMap (fun j => g (5 + j.1))
      = (List.range M.sig).flatMap (fun a => g (5 + a)) :=
    finRange_flatMap_congr _ _ _ (fun j => rfl)
  have hI : (List.finRange M.sig).flatMap (fun j => g (5 + M.sig + j.1))
      = (List.range M.sig).flatMap (fun a => g (5 + M.sig + a)) :=
    finRange_flatMap_congr _ _ _ (fun j => rfl)
  rw [hsplit, List.range_add, List.range_add,
    show List.range 5 = [0, 1, 2, 3, 4] from rfl]
  simp only [pKindList, List.flatMap_append, List.flatMap_map, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc, hF, hI, kindIdx]

/-- Resolution classes as codes. -/
def resCode : PRes → Nat
  | .other => 0
  | .live => 1
  | .cut => 2

theorem contigB_eq (r1 r2 r3 : PRes) :
    contigB (resCode r1) (resCode r2) (resCode r3) = contigOK r1 r2 r3 := by
  cases r1 <;> cases r2 <;> cases r3 <;> rfl

/-- The resolution list of a kind, flattened to `(value, class code)` pairs. -/
theorem resOf_eq (M : FlatTM) (k : PKind M) :
    (pResolutions M k).map (fun r => (r.1.1, resCode r.2))
      = resOf M.sig M.states (min M.start M.states) (kindIdx M k) := by
  cases k with
  | delim => rfl
  | blank => rfl
  | star =>
      show _ = resOf M.sig M.states _ 2
      simp only [resOf, reduceIte, pResolutions, List.map_append, List.map_map,
        List.map_cons, List.map_nil]
      congr 1
      exact map_finRange_congr _ _ _ (fun j => rfl)
  | initStar =>
      show _ = resOf M.sig M.states _ 3
      simp only [resOf, reduceIte, pResolutions, List.map_append, List.map_map,
        List.map_cons, List.map_nil]
      congr 1
      exact map_finRange_congr _ _ _ (fun j => rfl)
  | initBlank => rfl
  | fixedSym j =>
      show _ = resOf M.sig M.states _ (5 + j.1)
      have h1 : ¬ (5 + j.1 = 0) := by omega
      have h2 : ¬ (5 + j.1 = 1) := by omega
      have h3 : ¬ (5 + j.1 = 2) := by omega
      have h4 : ¬ (5 + j.1 = 3) := by omega
      have h5 : ¬ (5 + j.1 = 4) := by omega
      have h6 : 5 + j.1 < 5 + M.sig := by have := j.2; omega
      have hj : 5 + j.1 - 5 = j.1 := by omega
      simp only [resOf, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_pos h6, hj, pResolutions, List.map_cons, List.map_nil]
      rfl
  | initFixedSym j =>
      show _ = resOf M.sig M.states _ (5 + M.sig + j.1)
      have h1 : ¬ (5 + M.sig + j.1 = 0) := by omega
      have h2 : ¬ (5 + M.sig + j.1 = 1) := by omega
      have h3 : ¬ (5 + M.sig + j.1 = 2) := by omega
      have h4 : ¬ (5 + M.sig + j.1 = 3) := by omega
      have h5 : ¬ (5 + M.sig + j.1 = 4) := by omega
      have h6 : ¬ (5 + M.sig + j.1 < 5 + M.sig) := by omega
      have hj : 5 + M.sig + j.1 - 5 - M.sig = j.1 := by omega
      simp only [resOf, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_neg h6, hj, pResolutions, List.map_cons, List.map_nil]
      rfl

theorem preludeCardsOf_flat (M : FlatTM) (k1 k2 k3 : PKind M) :
    cardsFlat (preludeCardsOf M k1 k2 k3)
      = pBody M.sig M.states (min M.start M.states)
          (kindIdx M k1) (kindIdx M k2) (kindIdx M k3) := by
  unfold pBody
  rw [← resOf_eq, ← resOf_eq, ← resOf_eq]
  simp only [List.flatMap_map]
  unfold preludeCardsOf
  rw [cardsFlat_flatMap]
  refine List.flatMap_congr (fun r1 _ => ?_)
  rw [cardsFlat_flatMap]
  refine List.flatMap_congr (fun r2 _ => ?_)
  rw [cardsFlat_filterMap]
  refine List.flatMap_congr (fun r3 _ => ?_)
  rw [contigB_eq]
  by_cases h : contigOK r1.2 r2.2 r3.2 <;> simp only [h, if_true, if_false]
  · show cnats _ = _
    simp only [cnats, blk, pcellv, emb]
  · rfl

theorem preludeCards_flat (M : FlatTM) :
    cardsFlat (preludeCards M)
      = preludeBlocks M.sig M.states (min M.start M.states) := by
  have h3 : ∀ k1 k2 : PKind M,
      cardsFlat ((pKindList M).flatMap (fun k3 => preludeCardsOf M k1 k2 k3))
        = (List.range (2 * M.sig + 5)).flatMap
            (pBody M.sig M.states (min M.start M.states) (kindIdx M k1) (kindIdx M k2)) := by
    intro k1 k2
    rw [cardsFlat_flatMap, ← pKindList_flatMap M
      (pBody M.sig M.states (min M.start M.states) (kindIdx M k1) (kindIdx M k2))]
    exact List.flatMap_congr (fun k3 _ => preludeCardsOf_flat M k1 k2 k3)
  have h2 : ∀ k1 : PKind M,
      cardsFlat ((pKindList M).flatMap (fun k2 =>
          (pKindList M).flatMap (fun k3 => preludeCardsOf M k1 k2 k3)))
        = (List.range (2 * M.sig + 5)).flatMap (fun k2 =>
            (List.range (2 * M.sig + 5)).flatMap
              (pBody M.sig M.states (min M.start M.states) (kindIdx M k1) k2)) := by
    intro k1
    rw [cardsFlat_flatMap, ← pKindList_flatMap M (fun k2 =>
      (List.range (2 * M.sig + 5)).flatMap
        (pBody M.sig M.states (min M.start M.states) (kindIdx M k1) k2))]
    exact List.flatMap_congr (fun k2 _ => h3 k1 k2)
  unfold preludeCards preludeBlocks
  rw [cardsFlat_flatMap, ← pKindList_flatMap M (fun k1 =>
    (List.range (2 * M.sig + 5)).flatMap (fun k2 =>
      (List.range (2 * M.sig + 5)).flatMap
        (pBody M.sig M.states (min M.start M.states) k1 k2)))]
  exact List.flatMap_congr (fun k1 _ => h2 k1)


/-! ## The whole stream -/

/-- **Design fact 1: `emb` is a no-op on the flat encoding.** -/
theorem cnats_embCard (M : FlatTM) (c : TCCCard (Fin (Sg M))) :
    cnats (embCard M c) = cnats c := rfl

theorem cookCards_flat (M : FlatTM) :
    cardsFlat (cookCards M)
      = copyBlocks M.sig M.states ++
        copyRightBlocks M.sig M.states ++
        haltLeftBlocks M.sig M.states (M.halt.map S1Parse.bitOf) ++
        haltCenterBlocks M.sig M.states (M.halt.map S1Parse.bitOf) ++
        haltRightBlocks M.sig M.states (M.halt.map S1Parse.bitOf) ++
        (normTrans M).flatMap (entryBlocks M) := by
  unfold cookCards
  rw [cardsFlat_append, cardsFlat_append, cardsFlat_append, cardsFlat_append,
    cardsFlat_append, copyCards_flat, copyRightCards_flat, haltLeftCards_flat,
    haltCenterCards_flat, haltRightCards_flat, stepCards_flat]

/-- **The stage-C specification.** The card stream of the guess tableau is the
machine-shaped model — validated numerically in `probes/S1CardModelProbe.lean`
before it was proven. -/
theorem cardBlocks_eq (M : FlatTM) : cardsFlat (guessCards M) = cardBlocks M := by
  unfold guessCards cardBlocks
  rw [cardsFlat_append, cardsFlat_map, preludeCards_flat]
  simp only [cnats_embCard]
  rw [show ((cookCards M).flatMap cnats) = cardsFlat (cookCards M) from rfl,
    cookCards_flat]

/-! ## `normTrans` on the machine — the one gadget that is not a nested loop

`(normTrans M).flatMap (entryBlocks M)` is the only part of `cardBlocks` whose
*source list* is not a `List.range`: it walks the transition stream, keeps the
**first** entry per key, and drops entries out of halting states. This section
pins its on-machine shape, under the guard the S1 program has already decided
(`S1Parse.stagePG_run`'s flag). Two facts make it cheap:

* **the key is three numbers** (`sameKey_eq`): with `tapes = 1` guarded, an
  entry's `src_tape_vals` is a single `Option Nat`, so `sameKey` is
  `(src_state, tag, val)` equality — no list comparison. The "seen" set is one
  register holding those triples as a stream, scanned with the existing
  `readItem`/`ltCheck` machinery;
* **the filter is one halt-bit lookup** (`entryOK_eq`): with all three arities
  guarded to `1`, `entryOK` degenerates to `¬ halt[src_state]`, i.e. a random
  access at index `src_state` into `S1Parse.PHALT` — a `forBnd` bounded by
  `1^src_state` walking the raw bit list, exactly the shape stage F needs too.

Cost: the dedup pass is `|trans|` iterations each scanning `≤ |trans|` keys, so
`O(|trans|²)` iterations of constant-size work — far below the emitter's own
`Θ(cards)` and irrelevant to the budget. -/

/-- The dedup key of an entry as the three numbers the stream carries. -/
def keyOf (e : FlatTMTransEntry) : Nat × Nat × Nat :=
  (e.src_state, oTag (e.src_tape_vals.headD none), oVal (e.src_tape_vals.headD none))

theorem oTag_oVal_inj {a b : Option Nat} (h1 : oTag a = oTag b) (h2 : oVal a = oVal b) :
    a = b := by
  cases a <;> cases b <;> simp_all [oTag, oVal]

/-- **The key comparison is a three-number comparison** once `tapes = 1` is
guarded. -/
theorem sameKey_eq (e1 e2 : FlatTMTransEntry)
    (h1 : e1.src_tape_vals.length = 1) (h2 : e2.src_tape_vals.length = 1) :
    sameKey e1 e2 = decide (keyOf e1 = keyOf e2) := by
  obtain ⟨a, ha⟩ : ∃ a, e1.src_tape_vals = [a] := List.length_eq_one_iff.mp h1
  obtain ⟨b, hb⟩ : ∃ b, e2.src_tape_vals = [b] := List.length_eq_one_iff.mp h2
  simp only [sameKey, keyOf, ha, hb, List.headD_cons, Prod.mk.injEq]
  cases a <;> cases b <;> simp [oTag, oVal]

/-- **The filter is one halt-bit lookup** once all three arities are guarded. -/
theorem entryOK_eq (M : FlatTM) (e : FlatTMTransEntry)
    (h1 : e.src_tape_vals.length = 1) (h2 : e.dst_write_vals.length = 1)
    (h3 : e.move_dirs.length = 1) :
    entryOK M e = !haltBit (M.halt.map S1Parse.bitOf) e.src_state := by
  simp [entryOK, h1, h2, h3, haltBit_eq]

/-- The on-machine dedup: the "seen" set is a list of **keys**, not entries. -/
def dedupK (seen : List (Nat × Nat × Nat)) :
    List FlatTMTransEntry → List FlatTMTransEntry
  | [] => []
  | e :: es =>
      if seen.any (fun k => decide (k = keyOf e)) then dedupK seen es
      else e :: dedupK (keyOf e :: seen) es

theorem dedupK_subset (seen : List (Nat × Nat × Nat)) (es : List FlatTMTransEntry) :
    ∀ e ∈ dedupK seen es, e ∈ es := by
  induction es generalizing seen with
  | nil => intro e he; cases he
  | cons a es ih =>
      intro e he
      by_cases h : seen.any (fun k => decide (k = keyOf a))
      · rw [dedupK, if_pos h] at he
        exact List.mem_cons_of_mem _ (ih seen e he)
      · rw [dedupK, if_neg h] at he
        rcases List.mem_cons.1 he with rfl | he
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih _ e he)

private theorem any_key (a : FlatTMTransEntry) (ha : a.src_tape_vals.length = 1) :
    ∀ seen : List FlatTMTransEntry, (∀ p ∈ seen, p.src_tape_vals.length = 1) →
      (seen.any fun p => sameKey p a)
        = (seen.any fun p => decide (keyOf p = keyOf a)) := by
  intro seen
  induction seen with
  | nil => intro _; rfl
  | cons p ps ih =>
      intro h
      simp only [List.any_cons]
      rw [sameKey_eq p a (h p (List.mem_cons_self ..)) ha,
        ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem dedupGo_eq_dedupK :
    ∀ (seen es : List FlatTMTransEntry),
      (∀ p ∈ seen, p.src_tape_vals.length = 1) →
      (∀ e ∈ es, e.src_tape_vals.length = 1) →
      dedupGo seen es = dedupK (seen.map keyOf) es := by
  intro seen es
  induction es generalizing seen with
  | nil => intro _ _; rfl
  | cons a es ih =>
      intro hseen hes
      have ha : a.src_tape_vals.length = 1 := hes a (List.mem_cons_self ..)
      have hes' : ∀ e ∈ es, e.src_tape_vals.length = 1 :=
        fun e he => hes e (List.mem_cons_of_mem _ he)
      have hany : (seen.any fun p => sameKey p a)
          = ((seen.map keyOf).any fun k => decide (k = keyOf a)) := by
        rw [List.any_map]
        exact any_key a ha seen hseen
      show (if seen.any (fun p => sameKey p a) then _ else _) = _
      rw [hany, dedupK]
      by_cases h : ((seen.map keyOf).any fun k => decide (k = keyOf a))
      · rw [if_pos h, if_pos h]; exact ih seen hseen hes'
      · rw [if_neg h, if_neg h]
        rw [show ((keyOf a :: seen.map keyOf)) = ((a :: seen).map keyOf) from rfl,
          ← ih (a :: seen) (by
            intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            · exact ha
            · exact hseen p hp) hes']

/-- **The on-machine `normTrans`.** -/
def normModel (M : FlatTM) : List FlatTMTransEntry :=
  (dedupK [] M.trans).filter
    (fun e => !haltBit (M.halt.map S1Parse.bitOf) e.src_state)

/-- **`normModel` is `normTrans`** on every guarded instance — the emitter's
dedup pass specification. -/
theorem normModel_eq (M : FlatTM) (hV : validFlatTM M) (hT : M.tapes = 1) :
    normModel M = normTrans M := by
  have hlen : ∀ e ∈ M.trans, e.src_tape_vals.length = 1 := by
    intro e he; rw [(hV.2.2 e he).2.2.1, hT]
  unfold normModel normTrans dedupKeys
  rw [dedupGo_eq_dedupK [] M.trans (by intro p hp; cases hp) hlen, List.map_nil]
  refine (List.filter_congr (fun e he => ?_)).symm
  have heM : e ∈ M.trans := dedupK_subset [] M.trans e he
  exact entryOK_eq M e (by rw [(hV.2.2 e heM).2.2.1, hT])
    (by rw [(hV.2.2 e heM).2.2.2.1, hT]) (by rw [(hV.2.2 e heM).2.2.2.2.1, hT])

/-! ## Stage M's no-branch — closeable now

On the guard-false branch the program emits `S1Map.s1No`, whose
`FlatTCCFree.encodeIn` is six empty registers: five `clear`s on the output
registers `1`–`5` (register `0` already ends `[]` — `S1Parse.stagePG_run`). The
whole yes-branch (`Σ / I / C / F` and the multiplex) therefore sits under one
`Cmd.ifBit S1Parse.FLG`, which also means **stage C never runs on an invalid
machine**: its run lemma may assume the guard, and its cost on the no-branch is
a constant (`Cmd.run` charges only the taken branch). -/

/-- Stage M, guard-false branch. -/
def stageMNo : Cmd :=
  Cmd.op (.clear 1) ;; Cmd.op (.clear 2) ;; Cmd.op (.clear 3) ;;
    Cmd.op (.clear 4) ;; Cmd.op (.clear 5)

/-- The five output registers end empty — i.e. holding
`FlatTCCFree.encodeIn S1Map.s1No`'s registers `1`–`5`. -/
theorem stageMNo_run (s : State) (r : Var) (hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) :
    (stageMNo.eval s).get r = State.get (FlatTCCFree.encodeIn S1Map.s1No) r := by
  have hz : State.get (FlatTCCFree.encodeIn S1Map.s1No) r = [] := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hz]
  simp only [stageMNo, Cmd.eval_seq, Cmd.eval_op, Op.eval]
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]

/-- `stageMNo` touches nothing but the five output registers. -/
theorem stageMNo_frame (s : State) (r : Var) (hr : 6 ≤ r ∨ r = 0) :
    (stageMNo.eval s).get r = s.get r := by
  have key : ∀ k : Nat, k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 → r ≠ k := by
    rintro k hk rfl
    rcases hr with h | h <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      exact absurd h (by decide)
  have k1 : r ≠ 1 := key 1 (by decide)
  have k2 : r ≠ 2 := key 2 (by decide)
  have k3 : r ≠ 3 := key 3 (by decide)
  have k4 : r ≠ 4 := key 4 (by decide)
  have k5 : r ≠ 5 := key 5 (by decide)
  simp only [stageMNo, Cmd.eval_seq, Cmd.eval_op, Op.eval]
  rw [State.get_set_ne _ _ _ _ k5, State.get_set_ne _ _ _ _ k4,
    State.get_set_ne _ _ _ _ k3, State.get_set_ne _ _ _ _ k2,
    State.get_set_ne _ _ _ _ k1]

theorem stageMNo_usesBelow : Cmd.UsesBelow stageMNo 6 := by
  simp [stageMNo, Cmd.UsesBelow, Op.UsesBelow]

/-- **The `CARDS` register's target.** Stage C must leave
`FlatTCCFree.encNats (cardBlocks M)` in the card register: one bare unary block
per number of the model. -/
theorem encCards_eq (M : FlatTM) (s : List Nat) (maxSize steps : Nat) :
    FlatTCCFree.encCardsIn (guessTableau M s maxSize steps).cards
      = FlatTCCFree.encNats (cardBlocks M) := by
  have h : (guessTableau M s maxSize steps).cards
      = (guessCards M).map FlatTCC.flattenCard := rfl
  rw [h, encCardsIn_eq_encNats, cardsFlat_eq, cardBlocks_eq]

end S1Cards
