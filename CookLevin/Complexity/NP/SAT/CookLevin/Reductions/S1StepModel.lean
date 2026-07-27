import Complexity.NP.SAT.CookLevin.Reductions.S1PreludeEmit

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-! # S1, part 5e — stage **C**'s `stepBlocks` family, the emitter-shaped model

The prelude family is built (`S1PreludeEmit`); `stepBlocks` is stage C's last
family. This file does for it what `S1Prelude` did for the prelude: fix the
emitter's shape *before* any `Cmd` is written, so the build is execution rather
than discovery. Four findings, each a theorem below.

## Finding M — `stepBlocks` needs no on-machine comparison either

Every branch in `S1Cards.stepBlocks` that reads a loop counter is a
**last-iteration** test:

* `stepCenterBlocks` tests `x = σ+1` (the write is void beyond the frontier)
  and `x = 0` (the left neighbour is the boundary cell);
* `stepRightBlocks` tests `y = σ` (same frontier condition, on the *inner*
  loop);
* `stepLeftBlocks` tests `i = 1`, and its loop is `List.range 2`.

Splitting `List.range (n+1) = List.range n ++ [n]` and
`List.range (σ+2) = [0] ++ (List.range σ).map (·+1) ++ [σ+1]` makes each test a
compile-time constant of its segment (`range_last` / `range_first_last`), so —
exactly as for the prelude (`S1Prelude.range_seg`) — **stage C still needs no
unary comparison gadget**. That locked invariant now covers both open families.

## Finding N — three constants per entry, all hoistable

`S1Cards.rOf`/`wOf` depend on the entry only, and `wOf`'s `xb` argument takes
just two values, so an entry contributes exactly three symbol constants:
`rOf σ mT mV`, `wOf … false` and `wOf … true`. Every card cell is one of those,
a loop counter, or `hv` of one of them. The emitter computes all three in a
per-entry preamble — `S1Prelude.minReg` does the `min · σ` clamps, no
comparison gadget — and no loop body recomputes anything.

## Finding O — `mv` is entry-constant: one `ifBit` chain, not a test per cell

All four sub-families branch on the move code, and `stepInBlocks` is *empty*
when `mv = 2`. Since `mv` is fixed for the whole entry, one three-way `ifBit`
chain wraps the entry body and each of the three arms is straight-line. The
`cCard`/`lCard`/`rCard` cells below keep `mv` as a parameter so that one `_run`
lemma per family serves all three arms.

## Finding P — `hv` is a hoisted product plus a counter

`S1Cards.hv σ q v = (σ+1)(q+1) + v`, so each entry needs two hoisted
`unaryMulLoop`s (`1^((σ+1)(q+1))` and `1^((σ+1)(q'+1))`) and every `hv` cell is
one `S1CardEmit.emitBlk2` over `(base, counter)` — the atom stage C already
uses everywhere. `S1Prelude.minReg` supplies the two clamped states
`min e.src_state M.states` / `min e.dst_state M.states`.
-/

namespace S1Step

open Complexity.Lang Complexity.Simulators
open S1Cards

/-! ## The two range splits -/

theorem range_last {α : Type} (n : Nat) (g : Nat → List α) :
    (List.range (n + 1)).flatMap g = (List.range n).flatMap g ++ g n := by
  rw [List.range_succ, List.flatMap_append]
  simp

theorem range_first_last {α : Type} (σ : Nat) (g : Nat → List α) :
    (List.range (σ + 2)).flatMap g
      = g 0 ++ ((List.range σ).flatMap (fun d => g (d + 1)) ++ g (σ + 1)) := by
  rw [show σ + 2 = (σ + 1) + 1 from rfl, List.range_succ_eq_map,
    List.flatMap_cons, List.flatMap_map]
  refine congrArg _ ?_
  rw [range_last σ (fun d => g (Nat.succ d))]

/-! ## `stepCenterBlocks`

Three segments: `x = 0` (left neighbour is the boundary cell), the interior
`x = d+1` with `d < σ`, and `x = σ+1` (the head is beyond the frontier, so a
`some`-write is void and `W` switches). `X = xv σ st x` is the segment's
constant `bv σ st` / `d` / `σ`, and in the two non-zero segments `x - 1 = X`. -/

/-- One centre card, with the segment's `X`, its write symbol `W` and its
"is this the `x = 0` segment?" flag as constants. -/
def cCard (σ st q q' rvv W mv X : Nat) (xzero : Bool) (z : Nat) : List Nat :=
  if mv = 2 then blk X (hv σ q rvv) z X (hv σ q' W) z
  else if mv = 1 then blk X (hv σ q rvv) z X W (hv σ q' z)
  else if xzero then blk X (hv σ q rvv) z (bv σ st) (hv σ q' W) z
  else blk X (hv σ q rvv) z (hv σ q' X) W z

def stepCenterSeg (σ st q q' mT mV wT wV mv : Nat) : List Nat :=
  (List.range (σ + 1)).flatMap
      (fun z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) mv
        (bv σ st) true z)
  ++ ((List.range σ).flatMap (fun d => (List.range (σ + 1)).flatMap
        (fun z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) mv d false z))
      ++ (List.range (σ + 1)).flatMap
        (fun z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) mv σ false z))

theorem stepCenterBlocks_seg (σ st q q' mT mV wT wV mv : Nat) :
    stepCenterBlocks σ st q q' mT mV wT wV mv = stepCenterSeg σ st q q' mT mV wT wV mv := by
  unfold stepCenterBlocks stepCenterSeg
  rw [range_first_last]
  refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_)
  · refine List.flatMap_congr (fun z _ => ?_)
    have hx : xv σ st 0 = bv σ st := rfl
    have hd : decide ((0 : Nat) = σ + 1) = false := by simp
    simp only [hx, hd, cCard]
    simp
  · refine List.flatMap_congr (fun d hd => ?_)
    have hlt : d < σ := List.mem_range.1 hd
    refine List.flatMap_congr (fun z _ => ?_)
    have hx : xv σ st (d + 1) = d := by simp [xv]
    have hb : decide (d + 1 = σ + 1) = false := by simp; omega
    simp only [hx, hb, cCard]
    simp
  · refine List.flatMap_congr (fun z _ => ?_)
    have hx : xv σ st (σ + 1) = σ := by simp [xv]
    simp only [hx, cCard]
    simp

/-! ## `stepLeftBlocks` — two straight-line copies -/

/-- One left card. -/
def lCard (σ q q' rvv W mv y z : Nat) : List Nat :=
  if mv = 2 then blk (hv σ q rvv) y z (hv σ q' W) y z
  else if mv = 1 then blk (hv σ q rvv) y z W (hv σ q' y) z
  else blk (hv σ q rvv) y z W y z ++ blk (hv σ q rvv) y z (hv σ q' W) y z

def stepLeftSeg (σ q q' mT mV wT wV mv : Nat) : List Nat :=
  (List.range (σ + 1)).flatMap (fun y => (List.range (σ + 1)).flatMap
      (fun z => lCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) mv y z))
  ++ (List.range (σ + 1)).flatMap (fun y => (List.range (σ + 1)).flatMap
      (fun z => lCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) mv y z))

theorem stepLeftBlocks_seg (σ q q' mT mV wT wV mv : Nat) :
    stepLeftBlocks σ q q' mT mV wT wV mv = stepLeftSeg σ q q' mT mV wT wV mv := by
  unfold stepLeftBlocks stepLeftSeg
  rw [show (2 : Nat) = 1 + 1 from rfl, range_last, range_last]
  simp only [List.range_zero, List.flatMap_nil, List.nil_append]
  refine congrArg₂ _ ?_ ?_ <;>
    refine List.flatMap_congr (fun y _ => List.flatMap_congr (fun z _ => ?_)) <;>
    simp only [lCard] <;> norm_num

/-! ## `stepRightBlocks` — the split is on the INNER loop

`W` here depends on `y = σ`, so the `y` loop splits and the `x` loop stays a
plain `forBnd` (its `xv` is `S1CardEmit.loadX`, which is already built). -/

/-- One right card. -/
def rCard (σ q q' rvv W mv X y : Nat) : List Nat :=
  if mv = 2 then blk X y (hv σ q rvv) X y (hv σ q' W)
  else if mv = 1 then blk X y (hv σ q rvv) X y W
  else blk X y (hv σ q rvv) X (hv σ q' y) W

def stepRightSeg (σ st q q' mT mV wT wV mv : Nat) : List Nat :=
  (List.range (σ + 2)).flatMap (fun x =>
    (List.range σ).flatMap (fun y =>
        rCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) mv (xv σ st x) y)
    ++ rCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) mv (xv σ st x) σ)

theorem stepRightBlocks_seg (σ st q q' mT mV wT wV mv : Nat) :
    stepRightBlocks σ st q q' mT mV wT wV mv = stepRightSeg σ st q q' mT mV wT wV mv := by
  unfold stepRightBlocks stepRightSeg
  refine List.flatMap_congr (fun x _ => ?_)
  rw [range_last]
  refine congrArg₂ _ ?_ ?_
  · refine List.flatMap_congr (fun y hy => ?_)
    have hlt : y < σ := List.mem_range.1 hy
    have hb : decide (y = σ) = false := by simp; omega
    simp only [hb, rCard]
  · simp only [rCard]
    simp

/-! ## The whole family

`stepInBlocks` needs no reformulation: it branches only on `mv` (Finding O) and
reads no loop counter comparatively. -/

def stepSeg (σ st q q' mT mV wT wV mv : Nat) : List Nat :=
  stepCenterSeg σ st q q' mT mV wT wV mv ++ stepLeftSeg σ q q' mT mV wT wV mv ++
  stepRightSeg σ st q q' mT mV wT wV mv ++ stepInBlocks σ st q' mv

/-- **The reformulation is faithful.** -/
theorem stepBlocks_seg (σ st q q' mT mV wT wV mv : Nat) :
    stepBlocks σ st q q' mT mV wT wV mv = stepSeg σ st q q' mT mV wT wV mv := by
  unfold stepBlocks stepSeg
  rw [stepCenterBlocks_seg, stepLeftBlocks_seg, stepRightBlocks_seg]

/-- **The whole entry stream, in the emitter's shape.** -/
def entrySeg (M : FlatTM) (e : FlatTMTransEntry) : List Nat :=
  stepSeg M.sig M.states (min e.src_state M.states) (min e.dst_state M.states)
    (oTag (e.src_tape_vals.headD none)) (oVal (e.src_tape_vals.headD none))
    (oTag (e.dst_write_vals.headD none)) (oVal (e.dst_write_vals.headD none))
    (HeadLayout.encMoveN (e.move_dirs.headD TMMove.Nmove))

theorem entryBlocks_seg (M : FlatTM) (e : FlatTMTransEntry) :
    entryBlocks M e = entrySeg M e := by
  unfold entryBlocks entrySeg
  exact stepBlocks_seg ..

/-- **Stage C's `stepBlocks` summand, in the emitter's shape** — the target the
entry loop must meet. The dedup `normModel` is `S1Cards.normModel_eq`. -/
theorem stepSummand_seg (M : FlatTM) (hV : validFlatTM M) (hT : M.tapes = 1) :
    (normTrans M).flatMap (entryBlocks M) = (normModel M).flatMap (entrySeg M) := by
  rw [normModel_eq M hV hT]
  exact List.flatMap_congr (fun e _ => entryBlocks_seg M e)

end S1Step
