import Complexity.NP.SAT.CookLevin.Reductions.S1StepModel

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/-! # S1, part 5f — stage **C**'s `stepBlocks` family, the entry body

`S1StepModel` fixed the shape (`stepSeg`); this file writes the `Cmd` that emits
one *entry*'s cards and proves it, in the `S1Prelude.Emits`/`EmitsFr` style.

What is here is the **entry body**: given the nine numbers of a normalised
transition entry already published into registers, `stepEmit` appends
`encNats (stepSeg …)` to `EOUT_C`. The two remaining pieces of the family — the
per-entry preamble that fills those registers off `PTRANS`, and the dedup +
entry loop around it — are the next session's (see `stepIdx_seg` at the bottom,
which is the loop's pure specification).

## The shape

```
stepEmit = ifBit TFN bodyN (ifBit TFR bodyR bodyL)      -- Finding O
bodyM    = cenFam … ;; lefFam … ;; rigFam … ;; inFam…   -- Finding M's segments
```

Each `body` is a chain of `EmitsFr` segments; each segment is a `forBnd` nest
whose innermost body is ONE `emitCard` — a run of `S1CardEmit.emitBlk2`s over a
six-pair register list (`S1Prelude.emitList`). **Every cell of every step card
is the sum of two register lengths** (Finding P: `hv σ q b = |TQ| + b`), so the
whole family needs exactly one card atom and the four loop nests below.

## Finding Q — the three `mv` arms share their loop nests, not their cards

The four sub-families' *nesting* does not depend on `mv` at all; only the
six-pair list inside does. So `cenFam`/`lefFam`/`rigFam` take their card `Cmd`s
as parameters and each `_run` lemma is proven **once** and applied three times
— the same move `S1Prelude.pKindCmd` makes for the prelude's kind levels. That
is what keeps a 3 × 4 = 12-way case split down to four loop lemmas and eleven
one-line card definitions.

## Registers (inside `S1Program.CDirty`; FINDING E — the whole pool is ours)

```
14 CBV 1^(bv σ st)   18 CS1 1^(σ+1)   19 CS2 1^(σ+2)   27 CZ  []
20 TQ  1^((σ+1)(q+1))            23 TQ2 1^((σ+1)(q'+1))
24 TR  1^(rOf σ mT mV)           25 TW0 1^(wOf … false)   17 TW1 1^(wOf … true)
21 CX  1^(xv σ st x)             28/29/30 TJ1/TJ2/TJ3 loop counters
39 TFN "mv = 2"                  40 TFR "mv = 1"
42 EE  loadX's flag              46 EK1 the tally counter        34 EOUT_C
```

`CBV`/`CS1`/`CS2`/`CX`/`CZ`/`EE`/`EK1` are `S1CardEmit`'s registers, re-used
verbatim so that `S1CardEmit.loadX` serves the two families that need `xv`.

⚠ **Nested dirty lists (FINDING H again).** `SD3 ⊆ SD2 ⊆ SD1`: an inner loop's
frame must not claim the counter its *outer* loop owns, because the card reads
it. One global dirty list does not work here either.
-/

namespace S1Step

open Complexity.Lang Complexity.Simulators HeadLayout
open S1Emit S1CardEmit S1Prelude S1Cards

/-! ## The register frame -/

/-- `1^((σ+1)(q+1))` — the source state's head-cell base (Finding P). -/
def TQ  : Var := 20
/-- `1^((σ+1)(q'+1))` — the destination state's head-cell base. -/
def TQ2 : Var := 23
/-- `1^(rOf σ mT mV)` — the symbol read under the head. -/
def TR  : Var := 24
/-- `1^(wOf σ mT mV wT wV false)` — the written symbol, in range. -/
def TW0 : Var := 25
/-- `1^(wOf σ mT mV wT wV true)` — the written symbol beyond the frontier. -/
def TW1 : Var := 17
/-- The outermost loop counter (`x` / `y`). -/
def TJ1 : Var := 28
/-- The middle loop counter (`d` / `y`). -/
def TJ2 : Var := 29
/-- The innermost loop counter (`z` / `u` / `c`). -/
def TJ3 : Var := 30
/-- The `mv = 2` (no-move) flag. -/
def TFN : Var := 39
/-- The `mv = 1` (right-move) flag. -/
def TFR : Var := 40

/-- The innermost level's dirty list. -/
def SD3 : List Var := [TJ3, EK1]
/-- The middle level's dirty list. -/
def SD2 : List Var := [TJ2, TJ3, EK1]
/-- **Everything the entry body writes**, `EOUT_C` aside. -/
def SD1 : List Var := [CX, EE, TJ1, TJ2, TJ3, EK1]

/-! ## The per-entry frame

`SConst` are the machine-wide constants (the preamble builds them once);
`SEntry` are the nine numbers of one entry, as the emitter reads them. -/

/-- The machine-wide constants the entry body reads. -/
def SConst (σ st : Nat) (t : State) : Prop :=
  State.get t CBV = List.replicate (bv σ st) 1
  ∧ State.get t CS1 = List.replicate (σ + 1) 1
  ∧ State.get t CS2 = List.replicate (σ + 2) 1
  ∧ State.get t CZ = []
  ∧ State.get t S1Parse.PSIG = List.replicate σ 1

/-- One entry's nine numbers, as registers. `mv` enters only through the two
flags (Finding O). -/
def SEntry (σ q q' mT mV wT wV mv : Nat) (t : State) : Prop :=
  State.get t TQ = List.replicate (hv σ q 0) 1
  ∧ State.get t TQ2 = List.replicate (hv σ q' 0) 1
  ∧ State.get t TR = List.replicate (rOf σ mT mV) 1
  ∧ State.get t TW0 = List.replicate (wOf σ mT mV wT wV false) 1
  ∧ State.get t TW1 = List.replicate (wOf σ mT mV wT wV true) 1
  ∧ State.get t TFN = flagRep (decide (mv = 2))
  ∧ State.get t TFR = flagRep (decide (mv = 1))

/-- Every register `SConst`/`SEntry` names is outside `SD1`, so both survive
every frame the entry body's gadgets produce. -/
theorem SConst_frame {σ st : Nat} {w v : State} (h : SConst σ st w)
    (hfr : ∀ r : Var, r ≠ EOUT_C → r ∉ SD1 → State.get v r = State.get w r) :
    SConst σ st v := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨by rw [hfr CBV (by decide) (by decide)]; exact a,
    by rw [hfr CS1 (by decide) (by decide)]; exact b,
    by rw [hfr CS2 (by decide) (by decide)]; exact c,
    by rw [hfr CZ (by decide) (by decide)]; exact d,
    by rw [hfr S1Parse.PSIG (by decide) (by decide)]; exact e⟩

theorem SEntry_frame {σ q q' mT mV wT wV mv : Nat} {w v : State}
    (h : SEntry σ q q' mT mV wT wV mv w)
    (hfr : ∀ r : Var, r ≠ EOUT_C → r ∉ SD1 → State.get v r = State.get w r) :
    SEntry σ q q' mT mV wT wV mv v := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨by rw [hfr TQ (by decide) (by decide)]; exact a,
    by rw [hfr TQ2 (by decide) (by decide)]; exact b,
    by rw [hfr TR (by decide) (by decide)]; exact c,
    by rw [hfr TW0 (by decide) (by decide)]; exact d,
    by rw [hfr TW1 (by decide) (by decide)]; exact e,
    by rw [hfr TFN (by decide) (by decide)]; exact f,
    by rw [hfr TFR (by decide) (by decide)]; exact g⟩

/-! ## The card atom

Every step card is six cells, each the sum of two register lengths, so one
`S1Prelude.emitList` serves the whole family (`S1CardEmit.emitId` does **not** —
step cards are not identity cards). -/

/-- One step card: six two-source blocks appended to `EOUT_C`. -/
def emitCard (ps : List (Var × Var)) : Cmd := emitList EK1 EOUT_C ps

theorem card_run (D : List Var) (t : State) (ps : List (Var × Var)) (l : List Nat)
    (hEK : EK1 ∈ D)
    (hne : ∀ p ∈ ps, p.1 ≠ EOUT_C ∧ p.1 ≠ EK1 ∧ p.2 ≠ EOUT_C ∧ p.2 ≠ EK1)
    (hun : ∀ p ∈ ps, State.get t p.1 = List.replicate (State.get t p.1).length 1
        ∧ State.get t p.2 = List.replicate (State.get t p.2).length 1)
    (hl : ps.map (fun p => (State.get t p.1).length + (State.get t p.2).length) = l) :
    Emits D (emitCard ps) l t := by
  obtain ⟨hO, hF⟩ := emitList_run EK1 EOUT_C (fun r => (State.get t r).length)
    (by decide) ps t hne hun
  refine ⟨?_, fun r a b => hF r a (fun h => b (h ▸ hEK))⟩
  show State.get ((emitList EK1 EOUT_C ps).eval t) EOUT_C = _
  rw [hO, hl]

/-- **The workhorse.** Six explicit pairs with their values. -/
theorem card6_run (D : List Var) (t : State)
    (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Var)
    (va1 va2 vb1 vb2 vc1 vc2 vd1 vd2 ve1 ve2 vf1 vf2 : Nat)
    (hEK : EK1 ∈ D)
    (hne : ∀ r : Var, r ∈ ([a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, f1, f2] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (ha1 : State.get t a1 = List.replicate va1 1)
    (ha2 : State.get t a2 = List.replicate va2 1)
    (hb1 : State.get t b1 = List.replicate vb1 1)
    (hb2 : State.get t b2 = List.replicate vb2 1)
    (hc1 : State.get t c1 = List.replicate vc1 1)
    (hc2 : State.get t c2 = List.replicate vc2 1)
    (hd1 : State.get t d1 = List.replicate vd1 1)
    (hd2 : State.get t d2 = List.replicate vd2 1)
    (he1 : State.get t e1 = List.replicate ve1 1)
    (he2 : State.get t e2 = List.replicate ve2 1)
    (hf1 : State.get t f1 = List.replicate vf1 1)
    (hf2 : State.get t f2 = List.replicate vf2 1) :
    Emits D (emitCard [(a1, a2), (b1, b2), (c1, c2), (d1, d2), (e1, e2), (f1, f2)])
      (blk (va1 + va2) (vb1 + vb2) (vc1 + vc2) (vd1 + vd2) (ve1 + ve2) (vf1 + vf2)) t := by
  have hrep : ∀ (r : Var) (n : Nat), State.get t r = List.replicate n 1 →
      State.get t r = List.replicate (State.get t r).length 1 := by
    intro r n hr; rw [hr, List.length_replicate]
  refine card_run D t _ _ hEK ?_ ?_ ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨(hne _ (by simp)).1, (hne _ (by simp)).2, (hne _ (by simp)).1,
        (hne _ (by simp)).2⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hrep _ _ ha1, hrep _ _ ha2⟩
    · exact ⟨hrep _ _ hb1, hrep _ _ hb2⟩
    · exact ⟨hrep _ _ hc1, hrep _ _ hc2⟩
    · exact ⟨hrep _ _ hd1, hrep _ _ hd2⟩
    · exact ⟨hrep _ _ he1, hrep _ _ he2⟩
    · exact ⟨hrep _ _ hf1, hrep _ _ hf2⟩
  · simp only [List.map_cons, List.map_nil, ha1, ha2, hb1, hb2, hc1, hc2, hd1, hd2,
      he1, he2, hf1, hf2, List.length_replicate, blk]

/-! ## The loop principle, in emitter shape -/

/-- `S1CardEmit.emitLoop_run` repackaged as an `EmitsFr`: a `forBnd` whose body
emits `f i` at iteration `i` emits `(List.range n).flatMap f`. -/
theorem loopFr (cnt bnd : Var) (body : Cmd) (D : List Var) (f : Nat → List Nat)
    (n : Nat) (w : State) (hbnd : State.get w bnd = List.replicate n 1)
    (hbD : bnd ∉ D) (hbE : bnd ≠ EOUT_C) (hcd : cnt ≠ EOUT_C) (hcD : cnt ∈ D)
    (hstep : ∀ (i : Nat) (t : State), State.get t cnt = List.replicate i 1 →
        (∀ r : Var, r ≠ EOUT_C → r ∉ D → State.get t r = State.get w r) →
        Emits D body (f i) t) :
    EmitsFr D (Cmd.forBnd cnt bnd body) ((List.range n).flatMap f) w := by
  intro u hu
  refine emitLoop_run cnt bnd EOUT_C body D f n u ?_ hcd hcD ?_
  · rw [hu bnd hbE hbD]; exact hbnd
  · intro i t hti htfr
    exact hstep i t hti (fun r a b => by rw [htfr r a b]; exact hu r a b)

/-- `hv` splits into its hoisted base and the cell's low digit — the fact that
makes every head cell one `emitBlk2` (Finding P). -/
theorem hv_split (σ q b : Nat) : hv σ q b = hv σ q 0 + b := by simp [hv]


/-- `EmitsFr`'s missing congruence (`S1Prelude.Emits.congr_l` at the frame
level) — used only to re-associate the four sub-families' `++`. -/
theorem EmitsFr_congr {D : List Var} {c : Cmd} {l l' : List Nat} {w : State}
    (h : EmitsFr D c l w) (he : l = l') : EmitsFr D c l' w := he ▸ h

theorem SD3_SD1 : ∀ x ∈ SD3, x ∈ SD1 := by decide
theorem SD3_SD2 : ∀ x ∈ SD3, x ∈ SD2 := by decide
theorem SD2_SD1 : ∀ x ∈ SD2, x ∈ SD1 := by decide

/-! ## The eleven cards

One `def` and one `_run` per distinct six-pair list. `XR`/`YR`/`WR` are the
segment's constant registers, so each lemma is proven once and applied at every
segment that uses it. -/

def cardCN (XR WR : Var) : Cmd :=
  emitCard [(XR, CZ), (TQ, TR), (TJ3, CZ), (XR, CZ), (TQ2, WR), (TJ3, CZ)]
def cardCR (XR WR : Var) : Cmd :=
  emitCard [(XR, CZ), (TQ, TR), (TJ3, CZ), (XR, CZ), (WR, CZ), (TQ2, TJ3)]
def cardCL (XR WR : Var) : Cmd :=
  emitCard [(XR, CZ), (TQ, TR), (TJ3, CZ), (TQ2, XR), (WR, CZ), (TJ3, CZ)]
def cardLN (WR : Var) : Cmd :=
  emitCard [(TQ, TR), (TJ2, CZ), (TJ3, CZ), (TQ2, WR), (TJ2, CZ), (TJ3, CZ)]
def cardLR (WR : Var) : Cmd :=
  emitCard [(TQ, TR), (TJ2, CZ), (TJ3, CZ), (WR, CZ), (TQ2, TJ2), (TJ3, CZ)]
def cardLL (WR : Var) : Cmd :=
  emitCard [(TQ, TR), (TJ2, CZ), (TJ3, CZ), (WR, CZ), (TJ2, CZ), (TJ3, CZ)] ;; cardLN WR
def cardRN (YR WR : Var) : Cmd :=
  emitCard [(CX, CZ), (YR, CZ), (TQ, TR), (CX, CZ), (YR, CZ), (TQ2, WR)]
def cardRR (YR WR : Var) : Cmd :=
  emitCard [(CX, CZ), (YR, CZ), (TQ, TR), (CX, CZ), (YR, CZ), (WR, CZ)]
def cardRL (YR WR : Var) : Cmd :=
  emitCard [(CX, CZ), (YR, CZ), (TQ, TR), (CX, CZ), (TQ2, YR), (WR, CZ)]
def cardIR : Cmd :=
  emitCard [(TJ1, CZ), (TJ2, CZ), (TJ3, CZ), (TQ2, TJ1), (TJ2, CZ), (TJ3, CZ)]
def cardIL : Cmd :=
  emitCard [(CX, CZ), (TJ2, CZ), (TJ3, CZ), (CX, CZ), (TJ2, CZ), (TQ2, TJ3)]

section Cards

variable {σ q q' rvv X W y z : Nat} {v : State}

theorem cardCN_run (XR WR : Var)
    (hne : ∀ r : Var, r ∈ ([XR, CZ, TQ, TR, TJ3, CZ, XR, CZ, TQ2, WR, TJ3, CZ] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (hz : State.get v CZ = []) (hX : State.get v XR = List.replicate X 1)
    (hW : State.get v WR = List.replicate W 1)
    (hq : State.get v TQ = List.replicate (hv σ q 0) 1)
    (hq2 : State.get v TQ2 = List.replicate (hv σ q' 0) 1)
    (hr : State.get v TR = List.replicate rvv 1)
    (hj3 : State.get v TJ3 = List.replicate z 1) :
    Emits SD3 (cardCN XR WR) (blk X (hv σ q rvv) z X (hv σ q' W) z) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  refine (card6_run SD3 v XR CZ TQ TR TJ3 CZ XR CZ TQ2 WR TJ3 CZ
    X 0 (hv σ q 0) rvv z 0 X 0 (hv σ q' 0) W z 0 (by decide) hne
    hX hz' hq hr hj3 hz' hX hz' hq2 hW hj3 hz').congr_l ?_
  simp [blk, hv]

theorem cardCR_run (XR WR : Var)
    (hne : ∀ r : Var, r ∈ ([XR, CZ, TQ, TR, TJ3, CZ, XR, CZ, WR, CZ, TQ2, TJ3] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (hz : State.get v CZ = []) (hX : State.get v XR = List.replicate X 1)
    (hW : State.get v WR = List.replicate W 1)
    (hq : State.get v TQ = List.replicate (hv σ q 0) 1)
    (hq2 : State.get v TQ2 = List.replicate (hv σ q' 0) 1)
    (hr : State.get v TR = List.replicate rvv 1)
    (hj3 : State.get v TJ3 = List.replicate z 1) :
    Emits SD3 (cardCR XR WR) (blk X (hv σ q rvv) z X W (hv σ q' z)) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  refine (card6_run SD3 v XR CZ TQ TR TJ3 CZ XR CZ WR CZ TQ2 TJ3
    X 0 (hv σ q 0) rvv z 0 X 0 W 0 (hv σ q' 0) z (by decide) hne
    hX hz' hq hr hj3 hz' hX hz' hW hz' hq2 hj3).congr_l ?_
  simp [blk, hv]

theorem cardCL_run (XR WR : Var)
    (hne : ∀ r : Var, r ∈ ([XR, CZ, TQ, TR, TJ3, CZ, TQ2, XR, WR, CZ, TJ3, CZ] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (hz : State.get v CZ = []) (hX : State.get v XR = List.replicate X 1)
    (hW : State.get v WR = List.replicate W 1)
    (hq : State.get v TQ = List.replicate (hv σ q 0) 1)
    (hq2 : State.get v TQ2 = List.replicate (hv σ q' 0) 1)
    (hr : State.get v TR = List.replicate rvv 1)
    (hj3 : State.get v TJ3 = List.replicate z 1) :
    Emits SD3 (cardCL XR WR) (blk X (hv σ q rvv) z (hv σ q' X) W z) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  refine (card6_run SD3 v XR CZ TQ TR TJ3 CZ TQ2 XR WR CZ TJ3 CZ
    X 0 (hv σ q 0) rvv z 0 (hv σ q' 0) X W 0 z 0 (by decide) hne
    hX hz' hq hr hj3 hz' hq2 hX hW hz' hj3 hz').congr_l ?_
  simp [blk, hv]

theorem cardLN_run (WR : Var)
    (hne : ∀ r : Var, r ∈ ([TQ, TR, TJ2, CZ, TJ3, CZ, TQ2, WR, TJ2, CZ, TJ3, CZ] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (hz : State.get v CZ = []) (hW : State.get v WR = List.replicate W 1)
    (hq : State.get v TQ = List.replicate (hv σ q 0) 1)
    (hq2 : State.get v TQ2 = List.replicate (hv σ q' 0) 1)
    (hr : State.get v TR = List.replicate rvv 1)
    (hj2 : State.get v TJ2 = List.replicate y 1)
    (hj3 : State.get v TJ3 = List.replicate z 1) :
    Emits SD3 (cardLN WR) (blk (hv σ q rvv) y z (hv σ q' W) y z) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  refine (card6_run SD3 v TQ TR TJ2 CZ TJ3 CZ TQ2 WR TJ2 CZ TJ3 CZ
    (hv σ q 0) rvv y 0 z 0 (hv σ q' 0) W y 0 z 0 (by decide) hne
    hq hr hj2 hz' hj3 hz' hq2 hW hj2 hz' hj3 hz').congr_l ?_
  simp [blk, hv]

theorem cardLR_run (WR : Var)
    (hne : ∀ r : Var, r ∈ ([TQ, TR, TJ2, CZ, TJ3, CZ, WR, CZ, TQ2, TJ2, TJ3, CZ] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (hz : State.get v CZ = []) (hW : State.get v WR = List.replicate W 1)
    (hq : State.get v TQ = List.replicate (hv σ q 0) 1)
    (hq2 : State.get v TQ2 = List.replicate (hv σ q' 0) 1)
    (hr : State.get v TR = List.replicate rvv 1)
    (hj2 : State.get v TJ2 = List.replicate y 1)
    (hj3 : State.get v TJ3 = List.replicate z 1) :
    Emits SD3 (cardLR WR) (blk (hv σ q rvv) y z W (hv σ q' y) z) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  refine (card6_run SD3 v TQ TR TJ2 CZ TJ3 CZ WR CZ TQ2 TJ2 TJ3 CZ
    (hv σ q 0) rvv y 0 z 0 W 0 (hv σ q' 0) y z 0 (by decide) hne
    hq hr hj2 hz' hj3 hz' hW hz' hq2 hj2 hj3 hz').congr_l ?_
  simp [blk, hv]

theorem cardLL_run (WR : Var)
    (hne : ∀ r : Var, r ∈ ([TQ, TR, TJ2, CZ, TJ3, CZ, WR, CZ, TJ2, CZ, TJ3, CZ] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (hneN : ∀ r : Var, r ∈ ([TQ, TR, TJ2, CZ, TJ3, CZ, TQ2, WR, TJ2, CZ, TJ3, CZ] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (hz : State.get v CZ = []) (hW : State.get v WR = List.replicate W 1)
    (hq : State.get v TQ = List.replicate (hv σ q 0) 1)
    (hq2 : State.get v TQ2 = List.replicate (hv σ q' 0) 1)
    (hr : State.get v TR = List.replicate rvv 1)
    (hj2 : State.get v TJ2 = List.replicate y 1)
    (hj3 : State.get v TJ3 = List.replicate z 1) :
    Emits SD3 (cardLL WR)
      (blk (hv σ q rvv) y z W y z ++ blk (hv σ q rvv) y z (hv σ q' W) y z) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  obtain ⟨hWE, hWK⟩ := hne WR (by simp)
  have h1 : Emits [EK1]
      (emitCard [(TQ, TR), (TJ2, CZ), (TJ3, CZ), (WR, CZ), (TJ2, CZ), (TJ3, CZ)])
      (blk (hv σ q rvv) y z W y z) v := by
    refine (card6_run [EK1] v TQ TR TJ2 CZ TJ3 CZ WR CZ TJ2 CZ TJ3 CZ
      (hv σ q 0) rvv y 0 z 0 W 0 y 0 z 0 (by decide) hne
      hq hr hj2 hz' hj3 hz' hW hz' hj2 hz' hj3 hz').congr_l ?_
    simp [blk, hv]
  have hF := h1.2
  have hEK : ∀ x ∈ ([EK1] : List Var), x ∈ SD3 := by decide
  exact Emits.seq (h1.mono hEK) (cardLN_run WR hneN
    (by rw [hF CZ (by decide) (by decide)]; exact hz)
    (by rw [hF WR hWE (by simpa using hWK)]; exact hW)
    (by rw [hF TQ (by decide) (by decide)]; exact hq)
    (by rw [hF TQ2 (by decide) (by decide)]; exact hq2)
    (by rw [hF TR (by decide) (by decide)]; exact hr)
    (by rw [hF TJ2 (by decide) (by decide)]; exact hj2)
    (by rw [hF TJ3 (by decide) (by decide)]; exact hj3))

theorem cardRN_run (YR WR : Var)
    (hne : ∀ r : Var, r ∈ ([CX, CZ, YR, CZ, TQ, TR, CX, CZ, YR, CZ, TQ2, WR] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (hz : State.get v CZ = []) (hW : State.get v WR = List.replicate W 1)
    (hX : State.get v CX = List.replicate X 1)
    (hY : State.get v YR = List.replicate y 1)
    (hq : State.get v TQ = List.replicate (hv σ q 0) 1)
    (hq2 : State.get v TQ2 = List.replicate (hv σ q' 0) 1)
    (hr : State.get v TR = List.replicate rvv 1) :
    Emits SD3 (cardRN YR WR) (blk X y (hv σ q rvv) X y (hv σ q' W)) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  refine (card6_run SD3 v CX CZ YR CZ TQ TR CX CZ YR CZ TQ2 WR
    X 0 y 0 (hv σ q 0) rvv X 0 y 0 (hv σ q' 0) W (by decide) hne
    hX hz' hY hz' hq hr hX hz' hY hz' hq2 hW).congr_l ?_
  simp [blk, hv]

theorem cardRR_run (YR WR : Var)
    (hne : ∀ r : Var, r ∈ ([CX, CZ, YR, CZ, TQ, TR, CX, CZ, YR, CZ, WR, CZ] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (hz : State.get v CZ = []) (hW : State.get v WR = List.replicate W 1)
    (hX : State.get v CX = List.replicate X 1)
    (hY : State.get v YR = List.replicate y 1)
    (hq : State.get v TQ = List.replicate (hv σ q 0) 1)
    (hr : State.get v TR = List.replicate rvv 1) :
    Emits SD3 (cardRR YR WR) (blk X y (hv σ q rvv) X y W) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  refine (card6_run SD3 v CX CZ YR CZ TQ TR CX CZ YR CZ WR CZ
    X 0 y 0 (hv σ q 0) rvv X 0 y 0 W 0 (by decide) hne
    hX hz' hY hz' hq hr hX hz' hY hz' hW hz').congr_l ?_
  simp [blk, hv]

theorem cardRL_run (YR WR : Var)
    (hne : ∀ r : Var, r ∈ ([CX, CZ, YR, CZ, TQ, TR, CX, CZ, TQ2, YR, WR, CZ] : List Var) →
      r ≠ EOUT_C ∧ r ≠ EK1)
    (hz : State.get v CZ = []) (hW : State.get v WR = List.replicate W 1)
    (hX : State.get v CX = List.replicate X 1)
    (hY : State.get v YR = List.replicate y 1)
    (hq : State.get v TQ = List.replicate (hv σ q 0) 1)
    (hq2 : State.get v TQ2 = List.replicate (hv σ q' 0) 1)
    (hr : State.get v TR = List.replicate rvv 1) :
    Emits SD3 (cardRL YR WR) (blk X y (hv σ q rvv) X (hv σ q' y) W) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  refine (card6_run SD3 v CX CZ YR CZ TQ TR CX CZ TQ2 YR WR CZ
    X 0 y 0 (hv σ q 0) rvv X 0 (hv σ q' 0) y W 0 (by decide) hne
    hX hz' hY hz' hq hr hX hz' hq2 hY hW hz').congr_l ?_
  simp [blk, hv]

theorem cardIR_run
    (hz : State.get v CZ = [])
    (hj1 : State.get v TJ1 = List.replicate y 1)
    (hj2 : State.get v TJ2 = List.replicate z 1)
    (hj3 : State.get v TJ3 = List.replicate X 1)
    (hq2 : State.get v TQ2 = List.replicate (hv σ q' 0) 1) :
    Emits SD3 cardIR (blk y z X (hv σ q' y) z X) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  refine (card6_run SD3 v TJ1 CZ TJ2 CZ TJ3 CZ TQ2 TJ1 TJ2 CZ TJ3 CZ
    y 0 z 0 X 0 (hv σ q' 0) y z 0 X 0 (by decide) (by decide)
    hj1 hz' hj2 hz' hj3 hz' hq2 hj1 hj2 hz' hj3 hz').congr_l ?_
  simp [blk, hv]

theorem cardIL_run
    (hz : State.get v CZ = [])
    (hX : State.get v CX = List.replicate X 1)
    (hj2 : State.get v TJ2 = List.replicate y 1)
    (hj3 : State.get v TJ3 = List.replicate z 1)
    (hq2 : State.get v TQ2 = List.replicate (hv σ q' 0) 1) :
    Emits SD3 cardIL (blk X y z X y (hv σ q' z)) v := by
  have hz' : State.get v CZ = List.replicate 0 1 := hz
  refine (card6_run SD3 v CX CZ TJ2 CZ TJ3 CZ CX CZ TJ2 CZ TQ2 TJ3
    X 0 y 0 z 0 X 0 y 0 (hv σ q' 0) z (by decide) (by decide)
    hX hz' hj2 hz' hj3 hz' hX hz' hj2 hz' hq2 hj3).congr_l ?_
  simp [blk, hv]

end Cards

/-! ## The four sub-family loop nests

The nesting does not depend on `mv` (Finding Q), so each of these is proven
once and applied three times. `SFr w v` is "`v` agrees with `w` on everything
the entry body does not write". -/

/-- `v` agrees with `w` outside the entry body's dirty set. -/
def SFr (w v : State) : Prop :=
  ∀ r : Var, r ≠ EOUT_C → r ∉ SD1 → State.get v r = State.get w r

/-- `S1CardEmit.loadX` emits nothing and re-establishes `CX = 1^(xv σ st x)`. -/
theorem loadX_emits (cnt : Var) (σ st x : Nat) (t : State) (hcE : cnt ≠ EE)
    (hc : State.get t cnt = List.replicate x 1)
    (hbv : State.get t CBV = List.replicate (bv σ st) 1) :
    Emits SD1 (loadX cnt) [] t := by
  have hCXD : (CX : Var) ∈ SD1 := by decide
  have hEED : (EE : Var) ∈ SD1 := by decide
  obtain ⟨-, hF⟩ := loadX_run cnt σ st x t hcE hc hbv
  refine ⟨?_, fun r a b => hF r (fun h => b (h ▸ hCXD)) (fun h => b (h ▸ hEED))⟩
  rw [hF EOUT_C (by decide) (by decide), encNats_nil, List.append_nil]

/-- The centre family: three segments, each a `z` loop, the middle one inside a
`d` loop (`S1Step.stepCenterSeg`). -/
def cenFam (i1 i2 i3 : Cmd) : Cmd :=
  Cmd.forBnd TJ3 CS1 i1 ;;
  (Cmd.forBnd TJ2 S1Parse.PSIG (Cmd.forBnd TJ3 CS1 i2) ;; Cmd.forBnd TJ3 CS1 i3)

theorem cenFam_run (i1 i2 i3 : Cmd) (σ : Nat) (g1 g3 : Nat → List Nat)
    (g2 : Nat → Nat → List Nat) (w : State)
    (hs1 : State.get w CS1 = List.replicate (σ + 1) 1)
    (hsig : State.get w S1Parse.PSIG = List.replicate σ 1)
    (h1 : ∀ (z : Nat) (v : State), State.get v TJ3 = List.replicate z 1 → SFr w v →
        Emits SD3 i1 (g1 z) v)
    (h2 : ∀ (d z : Nat) (v : State), State.get v TJ2 = List.replicate d 1 →
        State.get v TJ3 = List.replicate z 1 → SFr w v → Emits SD3 i2 (g2 d z) v)
    (h3 : ∀ (z : Nat) (v : State), State.get v TJ3 = List.replicate z 1 → SFr w v →
        Emits SD3 i3 (g3 z) v) :
    EmitsFr SD1 (cenFam i1 i2 i3)
      ((List.range (σ + 1)).flatMap g1
        ++ ((List.range σ).flatMap (fun d => (List.range (σ + 1)).flatMap (g2 d))
            ++ (List.range (σ + 1)).flatMap g3)) w := by
  have A : EmitsFr SD1 (Cmd.forBnd TJ3 CS1 i1) ((List.range (σ + 1)).flatMap g1) w :=
    loopFr TJ3 CS1 i1 SD1 g1 (σ + 1) w hs1 (by decide) (by decide) (by decide) (by decide)
      (fun i t hti htfr => (h1 i t hti htfr).mono SD3_SD1)
  have C : EmitsFr SD1 (Cmd.forBnd TJ3 CS1 i3) ((List.range (σ + 1)).flatMap g3) w :=
    loopFr TJ3 CS1 i3 SD1 g3 (σ + 1) w hs1 (by decide) (by decide) (by decide) (by decide)
      (fun i t hti htfr => (h3 i t hti htfr).mono SD3_SD1)
  have B : EmitsFr SD1 (Cmd.forBnd TJ2 S1Parse.PSIG (Cmd.forBnd TJ3 CS1 i2))
      ((List.range σ).flatMap (fun d => (List.range (σ + 1)).flatMap (g2 d))) w := by
    refine loopFr TJ2 S1Parse.PSIG _ SD1 _ σ w hsig (by decide) (by decide) (by decide)
      (by decide) ?_
    intro d t htd htfr
    have hts1 : State.get t CS1 = List.replicate (σ + 1) 1 := by
      rw [htfr CS1 (by decide) (by decide)]; exact hs1
    refine Emits.mono SD3_SD1 (EmitsFr.here ?_)
    refine loopFr TJ3 CS1 i2 SD3 (g2 d) (σ + 1) t hts1 (by decide) (by decide) (by decide)
      (by decide) ?_
    intro z v hvz hvfr
    refine h2 d z v ?_ hvz (fun r a b => ?_)
    · rw [hvfr TJ2 (by decide) (by decide)]; exact htd
    · rw [hvfr r a (fun hm => b (SD3_SD1 r hm))]; exact htfr r a b
  exact A.seq (B.seq C)

/-- The left family: two `y × z` nests, one per frontier variant
(`S1Step.stepLeftSeg`). -/
def lefFam (i1 i2 : Cmd) : Cmd :=
  Cmd.forBnd TJ2 CS1 (Cmd.forBnd TJ3 CS1 i1) ;; Cmd.forBnd TJ2 CS1 (Cmd.forBnd TJ3 CS1 i2)

theorem lefFam_run (i1 i2 : Cmd) (σ : Nat) (g1 g2 : Nat → Nat → List Nat) (w : State)
    (hs1 : State.get w CS1 = List.replicate (σ + 1) 1)
    (h1 : ∀ (y z : Nat) (v : State), State.get v TJ2 = List.replicate y 1 →
        State.get v TJ3 = List.replicate z 1 → SFr w v → Emits SD3 i1 (g1 y z) v)
    (h2 : ∀ (y z : Nat) (v : State), State.get v TJ2 = List.replicate y 1 →
        State.get v TJ3 = List.replicate z 1 → SFr w v → Emits SD3 i2 (g2 y z) v) :
    EmitsFr SD1 (lefFam i1 i2)
      ((List.range (σ + 1)).flatMap (fun y => (List.range (σ + 1)).flatMap (g1 y))
        ++ (List.range (σ + 1)).flatMap (fun y => (List.range (σ + 1)).flatMap (g2 y))) w := by
  have dbl : ∀ (i : Cmd) (g : Nat → Nat → List Nat),
      (∀ (y z : Nat) (v : State), State.get v TJ2 = List.replicate y 1 →
        State.get v TJ3 = List.replicate z 1 → SFr w v → Emits SD3 i (g y z) v) →
      EmitsFr SD1 (Cmd.forBnd TJ2 CS1 (Cmd.forBnd TJ3 CS1 i))
        ((List.range (σ + 1)).flatMap (fun y => (List.range (σ + 1)).flatMap (g y))) w := by
    intro i g h
    refine loopFr TJ2 CS1 _ SD1 _ (σ + 1) w hs1 (by decide) (by decide) (by decide)
      (by decide) ?_
    intro y t hty htfr
    have hts1 : State.get t CS1 = List.replicate (σ + 1) 1 := by
      rw [htfr CS1 (by decide) (by decide)]; exact hs1
    refine Emits.mono SD3_SD1 (EmitsFr.here ?_)
    refine loopFr TJ3 CS1 i SD3 (g y) (σ + 1) t hts1 (by decide) (by decide) (by decide)
      (by decide) ?_
    intro z v hvz hvfr
    refine h y z v ?_ hvz (fun r a b => ?_)
    · rw [hvfr TJ2 (by decide) (by decide)]; exact hty
    · rw [hvfr r a (fun hm => b (SD3_SD1 r hm))]; exact htfr r a b
  exact (dbl i1 g1 h1).seq (dbl i2 g2 h2)

/-- The right family: an `x` loop rebuilding `CX`, then a `y` loop and the
`y = σ` card (`S1Step.stepRightSeg`). -/
def rigFam (i1 i2 : Cmd) : Cmd :=
  Cmd.forBnd TJ1 CS2 (loadX TJ1 ;; (Cmd.forBnd TJ2 S1Parse.PSIG i1 ;; i2))

theorem rigFam_run (i1 i2 : Cmd) (σ st : Nat) (g1 : Nat → Nat → List Nat)
    (g2 : Nat → List Nat) (w : State)
    (hbv : State.get w CBV = List.replicate (bv σ st) 1)
    (hs2 : State.get w CS2 = List.replicate (σ + 2) 1)
    (hsig : State.get w S1Parse.PSIG = List.replicate σ 1)
    (h1 : ∀ (x y : Nat) (v : State), State.get v CX = List.replicate (xv σ st x) 1 →
        State.get v TJ2 = List.replicate y 1 → SFr w v → Emits SD3 i1 (g1 x y) v)
    (h2 : ∀ (x : Nat) (v : State), State.get v CX = List.replicate (xv σ st x) 1 →
        SFr w v → Emits SD3 i2 (g2 x) v) :
    EmitsFr SD1 (rigFam i1 i2)
      ((List.range (σ + 2)).flatMap
        (fun x => (List.range σ).flatMap (g1 x) ++ g2 x)) w := by
  refine loopFr TJ1 CS2 _ SD1 _ (σ + 2) w hs2 (by decide) (by decide) (by decide)
    (by decide) ?_
  intro x t htx htfr
  have htbv : State.get t CBV = List.replicate (bv σ st) 1 := by
    rw [htfr CBV (by decide) (by decide)]; exact hbv
  have hL : Emits SD1 (loadX TJ1) [] t := loadX_emits TJ1 σ st x t (by decide) htx htbv
  obtain ⟨hLX, hLF⟩ := loadX_run TJ1 σ st x t (by decide) htx htbv
  have uX : State.get ((loadX TJ1).eval t) CX = List.replicate (xv σ st x) 1 := hLX
  have uFr : SFr w ((loadX TJ1).eval t) := by
    intro r a b
    rw [hLF r (fun h => b (h ▸ (by decide : (CX : Var) ∈ SD1)))
      (fun h => b (h ▸ (by decide : (EE : Var) ∈ SD1)))]
    exact htfr r a b
  have usig : State.get ((loadX TJ1).eval t) S1Parse.PSIG = List.replicate σ 1 := by
    rw [uFr S1Parse.PSIG (by decide) (by decide)]; exact hsig
  -- the `y` loop, kept at level 2 so that `CX` survives it
  have hY : Emits SD2 (Cmd.forBnd TJ2 S1Parse.PSIG i1) ((List.range σ).flatMap (g1 x))
      ((loadX TJ1).eval t) := by
    refine EmitsFr.here ?_
    refine loopFr TJ2 S1Parse.PSIG i1 SD2 (g1 x) σ _ usig (by decide) (by decide)
      (by decide) (by decide) ?_
    intro y v hvy hvfr
    refine (h1 x y v ?_ hvy (fun r a b => ?_)).mono SD3_SD2
    · rw [hvfr CX (by decide) (by decide)]; exact uX
    · rw [hvfr r a (fun hm => b (SD2_SD1 r hm))]; exact uFr r a b
  have hYF := hY.2
  have pX : State.get ((Cmd.forBnd TJ2 S1Parse.PSIG i1).eval ((loadX TJ1).eval t)) CX
      = List.replicate (xv σ st x) 1 := by
    rw [hYF CX (by decide) (by decide)]; exact uX
  have pFr : SFr w ((Cmd.forBnd TJ2 S1Parse.PSIG i1).eval ((loadX TJ1).eval t)) := by
    intro r a b
    rw [hYF r a (fun hm => b (SD2_SD1 r hm))]; exact uFr r a b
  refine Emits.congr_l (Emits.seq hL (Emits.seq (hY.mono SD2_SD1)
    ((h2 x _ pX pFr).mono SD3_SD1))) ?_
  simp

/-- The incoming-head family for `mv = 1` (`S1Cards.stepInBlocks`, right move). -/
def inFamR : Cmd := Cmd.forBnd TJ1 CS1 (Cmd.forBnd TJ2 CS1 (Cmd.forBnd TJ3 CS1 cardIR))

/-- The incoming-head family for `mv = 0` (left move); its `x` loop rebuilds
`CX` exactly as the right family's does. -/
def inFamL : Cmd :=
  Cmd.forBnd TJ1 CS2 (loadX TJ1 ;; Cmd.forBnd TJ2 CS1 (Cmd.forBnd TJ3 CS1 cardIL))

theorem inFamR_run (σ st q' : Nat) (w : State) (hc : SConst σ st w)
    (hq2 : State.get w TQ2 = List.replicate (hv σ q' 0) 1) :
    EmitsFr SD1 inFamR
      ((List.range (σ + 1)).flatMap (fun y => (List.range (σ + 1)).flatMap
        (fun z => (List.range (σ + 1)).flatMap (fun u => blk y z u (hv σ q' y) z u)))) w := by
  obtain ⟨-, hs1, -, hz, -⟩ := hc
  refine loopFr TJ1 CS1 _ SD1 _ (σ + 1) w hs1 (by decide) (by decide) (by decide)
    (by decide) ?_
  intro y t hty htfr
  have ts1 : State.get t CS1 = List.replicate (σ + 1) 1 := by
    rw [htfr CS1 (by decide) (by decide)]; exact hs1
  refine Emits.mono SD2_SD1 (EmitsFr.here ?_)
  refine loopFr TJ2 CS1 _ SD2 _ (σ + 1) t ts1 (by decide) (by decide) (by decide)
    (by decide) ?_
  intro z v hvz hvfr
  have vs1 : State.get v CS1 = List.replicate (σ + 1) 1 := by
    rw [hvfr CS1 (by decide) (by decide)]; exact ts1
  refine Emits.mono SD3_SD2 (EmitsFr.here ?_)
  refine loopFr TJ3 CS1 cardIR SD3 _ (σ + 1) v vs1 (by decide) (by decide) (by decide)
    (by decide) ?_
  intro u x hxu hxfr
  refine cardIR_run ?_ ?_ ?_ hxu ?_
  · rw [hxfr CZ (by decide) (by decide), hvfr CZ (by decide) (by decide),
      htfr CZ (by decide) (by decide)]; exact hz
  · rw [hxfr TJ1 (by decide) (by decide), hvfr TJ1 (by decide) (by decide)]; exact hty
  · rw [hxfr TJ2 (by decide) (by decide)]; exact hvz
  · rw [hxfr TQ2 (by decide) (by decide), hvfr TQ2 (by decide) (by decide),
      htfr TQ2 (by decide) (by decide)]; exact hq2

theorem inFamL_run (σ st q' : Nat) (w : State) (hc : SConst σ st w)
    (hq2 : State.get w TQ2 = List.replicate (hv σ q' 0) 1) :
    EmitsFr SD1 inFamL
      ((List.range (σ + 2)).flatMap (fun x => (List.range (σ + 1)).flatMap
        (fun y => (List.range (σ + 1)).flatMap
          (fun c => blk (xv σ st x) y c (xv σ st x) y (hv σ q' c))))) w := by
  obtain ⟨hbv, hs1, hs2, hz, -⟩ := hc
  refine loopFr TJ1 CS2 _ SD1 _ (σ + 2) w hs2 (by decide) (by decide) (by decide)
    (by decide) ?_
  intro x t htx htfr
  have htbv : State.get t CBV = List.replicate (bv σ st) 1 := by
    rw [htfr CBV (by decide) (by decide)]; exact hbv
  have hL : Emits SD1 (loadX TJ1) [] t := loadX_emits TJ1 σ st x t (by decide) htx htbv
  obtain ⟨hLX, hLF⟩ := loadX_run TJ1 σ st x t (by decide) htx htbv
  have uX : State.get ((loadX TJ1).eval t) CX = List.replicate (xv σ st x) 1 := hLX
  have uFr : SFr w ((loadX TJ1).eval t) := by
    intro r a b
    rw [hLF r (fun h => b (h ▸ (by decide : (CX : Var) ∈ SD1)))
      (fun h => b (h ▸ (by decide : (EE : Var) ∈ SD1)))]
    exact htfr r a b
  have us1 : State.get ((loadX TJ1).eval t) CS1 = List.replicate (σ + 1) 1 := by
    rw [uFr CS1 (by decide) (by decide)]; exact hs1
  have hBody : Emits SD1 (Cmd.forBnd TJ2 CS1 (Cmd.forBnd TJ3 CS1 cardIL))
      ((List.range (σ + 1)).flatMap (fun y => (List.range (σ + 1)).flatMap
        (fun c => blk (xv σ st x) y c (xv σ st x) y (hv σ q' c)))) ((loadX TJ1).eval t) := by
    refine Emits.mono SD2_SD1 (EmitsFr.here ?_)
    refine loopFr TJ2 CS1 _ SD2 _ (σ + 1) _ us1 (by decide) (by decide) (by decide)
      (by decide) ?_
    intro y v hvy hvfr
    have vs1 : State.get v CS1 = List.replicate (σ + 1) 1 := by
      rw [hvfr CS1 (by decide) (by decide)]; exact us1
    refine Emits.mono SD3_SD2 (EmitsFr.here ?_)
    refine loopFr TJ3 CS1 cardIL SD3 _ (σ + 1) v vs1 (by decide) (by decide) (by decide)
      (by decide) ?_
    intro c p hpc hpfr
    refine cardIL_run ?_ ?_ ?_ hpc ?_
    · rw [hpfr CZ (by decide) (by decide), hvfr CZ (by decide) (by decide),
        uFr CZ (by decide) (by decide)]
      exact hz
    · rw [hpfr CX (by decide) (by decide), hvfr CX (by decide) (by decide)]; exact uX
    · rw [hpfr TJ2 (by decide) (by decide)]; exact hvy
    · rw [hpfr TQ2 (by decide) (by decide), hvfr TQ2 (by decide) (by decide),
        uFr TQ2 (by decide) (by decide)]
      exact hq2
  exact Emits.congr_l (Emits.seq hL hBody) (by simp)

/-! ## The three `mv` arms and the entry body

`mv` is entry-constant (Finding O), so one three-way `ifBit` chain wraps the
whole body and each arm is straight-line. The arms share the four loop nests
above and differ only in their eleven card lists. -/

/-- Transport an `Emits` along an evaluation equation (the `ifBit` arms). -/
theorem Emits_of_eval {D : List Var} {c c' : Cmd} {l : List Nat} {u : State}
    (h : Emits D c' l u) (he : c.eval u = c'.eval u) : Emits D c l u := by
  obtain ⟨o, f⟩ := h
  exact ⟨by rw [he]; exact o, fun r a b => by rw [he]; exact f r a b⟩

/-- The `mv = 2` (no-move) arm. -/
def bodyN : Cmd :=
  cenFam (cardCN CBV TW0) (cardCN TJ2 TW0) (cardCN S1Parse.PSIG TW1) ;;
  (lefFam (cardLN TW0) (cardLN TW1) ;;
    (rigFam (cardRN TJ2 TW0) (cardRN S1Parse.PSIG TW1) ;;
      Cmd.op (.copy EOUT_C EOUT_C)))

/-- The `mv = 1` (right-move) arm. -/
def bodyR : Cmd :=
  cenFam (cardCR CBV TW0) (cardCR TJ2 TW0) (cardCR S1Parse.PSIG TW1) ;;
  (lefFam (cardLR TW0) (cardLR TW1) ;;
    (rigFam (cardRR TJ2 TW0) (cardRR S1Parse.PSIG TW1) ;; inFamR))

/-- The `mv = 0` (left-move) arm. -/
def bodyL : Cmd :=
  cenFam (cardCN CBV TW0) (cardCL TJ2 TW0) (cardCL S1Parse.PSIG TW1) ;;
  (lefFam (cardLL TW0) (cardLL TW1) ;;
    (rigFam (cardRL TJ2 TW0) (cardRL S1Parse.PSIG TW1) ;; inFamL))

section Arms

variable {σ st q q' mT mV wT wV : Nat} {w : State}

theorem bodyN_run (hc : SConst σ st w) (he : SEntry σ q q' mT mV wT wV 2 w) :
    EmitsFr SD1 bodyN (stepSeg σ st q q' mT mV wT wV 2) w := by
  obtain ⟨hbv, hs1, hs2, hz, hsig⟩ := hc
  obtain ⟨hq, hq2, hr, hW0, hW1, -, -⟩ := he
  have hC := cenFam_run (cardCN CBV TW0) (cardCN TJ2 TW0) (cardCN S1Parse.PSIG TW1) σ
    (fun z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 2 (bv σ st) true z)
    (fun z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) 2 σ false z)
    (fun d z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 2 d false z)
    w hs1 hsig
    (fun z v hz3 hfr => (cardCN_run CBV TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr CBV (by decide) (by decide)]; exact hbv)
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hz3).congr_l (by simp [cCard]))
    (fun d z v hd hz3 hfr => (cardCN_run TJ2 TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz) hd
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hz3).congr_l (by simp [cCard]))
    (fun z v hz3 hfr => (cardCN_run S1Parse.PSIG TW1 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr S1Parse.PSIG (by decide) (by decide)]; exact hsig)
      (by rw [hfr TW1 (by decide) (by decide)]; exact hW1)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hz3).congr_l (by simp [cCard]))
  have hL := lefFam_run (cardLN TW0) (cardLN TW1) σ
    (fun y z => lCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 2 y z)
    (fun y z => lCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) 2 y z)
    w hs1
    (fun y z v hy hz3 hfr => (cardLN_run TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hy hz3).congr_l (by simp [lCard]))
    (fun y z v hy hz3 hfr => (cardLN_run TW1 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW1 (by decide) (by decide)]; exact hW1)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hy hz3).congr_l (by simp [lCard]))
  have hR := rigFam_run (cardRN TJ2 TW0) (cardRN S1Parse.PSIG TW1) σ st
    (fun x y => rCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 2 (xv σ st x) y)
    (fun x => rCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) 2 (xv σ st x) σ)
    w hbv hs2 hsig
    (fun x y v hx hy hfr => (cardRN_run TJ2 TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0) hx hy
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr)).congr_l (by simp [rCard]))
    (fun x v hx hfr => (cardRN_run S1Parse.PSIG TW1 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW1 (by decide) (by decide)]; exact hW1) hx
      (by rw [hfr S1Parse.PSIG (by decide) (by decide)]; exact hsig)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr)).congr_l (by simp [rCard]))
  have hI : EmitsFr SD1 (Cmd.op (.copy EOUT_C EOUT_C)) [] w := fun u _ => Emits.nop SD1 u
  refine EmitsFr_congr (hC.seq (hL.seq (hR.seq hI))) ?_
  simp [stepSeg, stepCenterSeg, stepLeftSeg, stepRightSeg, stepInBlocks, List.append_assoc]

theorem bodyR_run (hc : SConst σ st w) (he : SEntry σ q q' mT mV wT wV 1 w) :
    EmitsFr SD1 bodyR (stepSeg σ st q q' mT mV wT wV 1) w := by
  obtain ⟨hbv, hs1, hs2, hz, hsig⟩ := hc
  obtain ⟨hq, hq2, hr, hW0, hW1, -, -⟩ := he
  have hC := cenFam_run (cardCR CBV TW0) (cardCR TJ2 TW0) (cardCR S1Parse.PSIG TW1) σ
    (fun z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 1 (bv σ st) true z)
    (fun z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) 1 σ false z)
    (fun d z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 1 d false z)
    w hs1 hsig
    (fun z v hz3 hfr => (cardCR_run CBV TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr CBV (by decide) (by decide)]; exact hbv)
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hz3).congr_l (by simp [cCard]))
    (fun d z v hd hz3 hfr => (cardCR_run TJ2 TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz) hd
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hz3).congr_l (by simp [cCard]))
    (fun z v hz3 hfr => (cardCR_run S1Parse.PSIG TW1 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr S1Parse.PSIG (by decide) (by decide)]; exact hsig)
      (by rw [hfr TW1 (by decide) (by decide)]; exact hW1)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hz3).congr_l (by simp [cCard]))
  have hL := lefFam_run (cardLR TW0) (cardLR TW1) σ
    (fun y z => lCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 1 y z)
    (fun y z => lCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) 1 y z)
    w hs1
    (fun y z v hy hz3 hfr => (cardLR_run TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hy hz3).congr_l (by simp [lCard]))
    (fun y z v hy hz3 hfr => (cardLR_run TW1 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW1 (by decide) (by decide)]; exact hW1)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hy hz3).congr_l (by simp [lCard]))
  have hR := rigFam_run (cardRR TJ2 TW0) (cardRR S1Parse.PSIG TW1) σ st
    (fun x y => rCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 1 (xv σ st x) y)
    (fun x => rCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) 1 (xv σ st x) σ)
    w hbv hs2 hsig
    (fun x y v hx hy hfr => (cardRR_run TJ2 TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0) hx hy
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TR (by decide) (by decide)]; exact hr)).congr_l (by simp [rCard]))
    (fun x v hx hfr => (cardRR_run S1Parse.PSIG TW1 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW1 (by decide) (by decide)]; exact hW1) hx
      (by rw [hfr S1Parse.PSIG (by decide) (by decide)]; exact hsig)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TR (by decide) (by decide)]; exact hr)).congr_l (by simp [rCard]))
  have hI := inFamR_run σ st q' w ⟨hbv, hs1, hs2, hz, hsig⟩ hq2
  refine EmitsFr_congr (hC.seq (hL.seq (hR.seq hI))) ?_
  simp [stepSeg, stepCenterSeg, stepLeftSeg, stepRightSeg, stepInBlocks, List.append_assoc]

theorem bodyL_run (hc : SConst σ st w) (he : SEntry σ q q' mT mV wT wV 0 w) :
    EmitsFr SD1 bodyL (stepSeg σ st q q' mT mV wT wV 0) w := by
  obtain ⟨hbv, hs1, hs2, hz, hsig⟩ := hc
  obtain ⟨hq, hq2, hr, hW0, hW1, -, -⟩ := he
  have hC := cenFam_run (cardCN CBV TW0) (cardCL TJ2 TW0) (cardCL S1Parse.PSIG TW1) σ
    (fun z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 0 (bv σ st) true z)
    (fun z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) 0 σ false z)
    (fun d z => cCard σ st q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 0 d false z)
    w hs1 hsig
    (fun z v hz3 hfr => (cardCN_run CBV TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr CBV (by decide) (by decide)]; exact hbv)
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hz3).congr_l (by simp [cCard]))
    (fun d z v hd hz3 hfr => (cardCL_run TJ2 TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz) hd
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hz3).congr_l (by simp [cCard]))
    (fun z v hz3 hfr => (cardCL_run S1Parse.PSIG TW1 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr S1Parse.PSIG (by decide) (by decide)]; exact hsig)
      (by rw [hfr TW1 (by decide) (by decide)]; exact hW1)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hz3).congr_l (by simp [cCard]))
  have hL := lefFam_run (cardLL TW0) (cardLL TW1) σ
    (fun y z => lCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 0 y z)
    (fun y z => lCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) 0 y z)
    w hs1
    (fun y z v hy hz3 hfr => (cardLL_run TW0 (by decide) (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hy hz3).congr_l (by simp [lCard]))
    (fun y z v hy hz3 hfr => (cardLL_run TW1 (by decide) (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW1 (by decide) (by decide)]; exact hW1)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr) hy hz3).congr_l (by simp [lCard]))
  have hR := rigFam_run (cardRL TJ2 TW0) (cardRL S1Parse.PSIG TW1) σ st
    (fun x y => rCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV false) 0 (xv σ st x) y)
    (fun x => rCard σ q q' (rOf σ mT mV) (wOf σ mT mV wT wV true) 0 (xv σ st x) σ)
    w hbv hs2 hsig
    (fun x y v hx hy hfr => (cardRL_run TJ2 TW0 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW0 (by decide) (by decide)]; exact hW0) hx hy
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr)).congr_l (by simp [rCard]))
    (fun x v hx hfr => (cardRL_run S1Parse.PSIG TW1 (by decide)
      (by rw [hfr CZ (by decide) (by decide)]; exact hz)
      (by rw [hfr TW1 (by decide) (by decide)]; exact hW1) hx
      (by rw [hfr S1Parse.PSIG (by decide) (by decide)]; exact hsig)
      (by rw [hfr TQ (by decide) (by decide)]; exact hq)
      (by rw [hfr TQ2 (by decide) (by decide)]; exact hq2)
      (by rw [hfr TR (by decide) (by decide)]; exact hr)).congr_l (by simp [rCard]))
  have hI := inFamL_run σ st q' w ⟨hbv, hs1, hs2, hz, hsig⟩ hq2
  refine EmitsFr_congr (hC.seq (hL.seq (hR.seq hI))) ?_
  simp [stepSeg, stepCenterSeg, stepLeftSeg, stepRightSeg, stepInBlocks, List.append_assoc]

end Arms

/-- **The entry body.** One three-way `ifBit` chain on the entry-constant move
code, wrapping the three straight-line arms (Finding O). -/
def stepEmit : Cmd := Cmd.ifBit TFN bodyN (Cmd.ifBit TFR bodyR bodyL)

/-- **The entry body is correct.** Given the machine-wide constants and one
entry's nine numbers in registers, `stepEmit` appends exactly that entry's
cards to `EOUT_C`, touching nothing outside `SD1`. -/
theorem stepEmit_run (σ st q q' mT mV wT wV mv : Nat) (w : State)
    (hmv : mv = 0 ∨ mv = 1 ∨ mv = 2)
    (hc : SConst σ st w) (he : SEntry σ q q' mT mV wT wV mv w) :
    EmitsFr SD1 stepEmit (stepSeg σ st q q' mT mV wT wV mv) w := by
  intro u hu
  have hcu : SConst σ st u := SConst_frame hc hu
  have heu : SEntry σ q q' mT mV wT wV mv u := SEntry_frame he hu
  have hcu' : SConst σ st u := hcu
  obtain ⟨-, -, -, -, -, hfn, hfr⟩ := heu
  rcases hmv with rfl | rfl | rfl
  · have t1 : State.get u TFN ≠ [1] := by rw [hfn]; simp [flagRep]
    have t2 : State.get u TFR ≠ [1] := by rw [hfr]; simp [flagRep]
    refine Emits_of_eval ((bodyL_run hcu' (SEntry_frame he hu)).here) ?_
    show (Cmd.ifBit TFN bodyN (Cmd.ifBit TFR bodyR bodyL)).eval u = _
    rw [Cmd.eval_ifBit_false _ _ _ _ t1, Cmd.eval_ifBit_false _ _ _ _ t2]
  · have t1 : State.get u TFN ≠ [1] := by rw [hfn]; simp [flagRep]
    have t2 : State.get u TFR = [1] := by rw [hfr]; rfl
    refine Emits_of_eval ((bodyR_run hcu' (SEntry_frame he hu)).here) ?_
    show (Cmd.ifBit TFN bodyN (Cmd.ifBit TFR bodyR bodyL)).eval u = _
    rw [Cmd.eval_ifBit_false _ _ _ _ t1, Cmd.eval_ifBit_true _ _ _ _ t2]
  · have t1 : State.get u TFN = [1] := by rw [hfn]; rfl
    refine Emits_of_eval ((bodyN_run hcu' (SEntry_frame he hu)).here) ?_
    show (Cmd.ifBit TFN bodyN (Cmd.ifBit TFR bodyR bodyL)).eval u = _
    rw [Cmd.eval_ifBit_true _ _ _ _ t1]

/-! ## The entry loop's specification

⚠ **FINDING R — `S1CardEmit.emitLoop_run` does NOT fit the entry loop.** Its
`hstep` pins the body's output to the *iteration index* alone, because the body
is quantified over every state agreeing with the loop's entry state outside `D`.
The entry loop is **cursor-driven**: what it emits at iteration `i` depends on
the transition stream still in `PTRANS` and on the keys already in the seen
register, both of which are inside `D`. So the entry loop needs a **stateful**
loop principle, `emitFold_run` below — `Cmd.foldlState_range_induct` with an
invariant that carries an abstract state. (The five built families and the whole
prelude nest are index-driven, which is why this only bites now.)

`stepGo` is the pure model the loop must meet: one pass over `M.trans`, keeping
**every** previous key in the seen set — `dedupK` only records fresh ones, but
`dedupK_congr` says the two agree, and appending unconditionally saves the
machine a branch. -/

/-- **The stateful emitter loop principle.** The body's output may depend on a
carried abstract state `a : α`, advanced by `nxt` once per iteration. -/
theorem emitFold_run {α : Type} (cnt bnd : Var) (body : Cmd) (D : List Var)
    (Inv : α → State → Prop) (nxt : α → α) (out : α → List Nat)
    (n : Nat) (a0 : α) (w : State)
    (hbnd : State.get w bnd = List.replicate n 1)
    (hcd : cnt ≠ EOUT_C) (hcD : cnt ∈ D) (hInv0 : Inv a0 w)
    (hcnt : ∀ (a : α) (t : State) (i : Nat), Inv a t →
        Inv a (State.set t cnt (List.replicate i 1)))
    (hstep : ∀ (a : α) (t : State) (i : Nat), Inv a t →
        State.get t cnt = List.replicate i 1 →
        Emits D body (out a) t ∧ Inv (nxt a) (body.eval t)) :
    Emits D (Cmd.forBnd cnt bnd body)
      ((List.range n).flatMap (fun i => out (nxt^[i] a0))) w := by
  set MI : Nat → State → Prop := fun i t =>
    Inv (nxt^[i] a0) t
    ∧ State.get t EOUT_C
        = State.get w EOUT_C
          ++ FlatTCCFree.encNats ((List.range i).flatMap (fun j => out (nxt^[j] a0)))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ D → State.get t r = State.get w r) with hMI
  have h0 : MI 0 w := by
    refine ⟨hInv0, ?_, fun _ _ _ => rfl⟩
    rw [List.range_zero, List.flatMap_nil, encNats_nil, List.append_nil]
  have hstep' : ∀ i t, i < n → MI i t →
      MI (i + 1) (body.eval (State.set t cnt (List.replicate i 1))) := by
    intro i t _ hM
    obtain ⟨hI, hO, hFr⟩ := hM
    have t0I : Inv (nxt^[i] a0) (State.set t cnt (List.replicate i 1)) := hcnt _ _ _ hI
    have t0C : State.get (State.set t cnt (List.replicate i 1)) cnt = List.replicate i 1 :=
      State.get_set_eq _ _ _
    have t0O : State.get (State.set t cnt (List.replicate i 1)) EOUT_C = State.get t EOUT_C :=
      State.get_set_ne _ _ _ _ (Ne.symm hcd)
    have t0Fr : ∀ r : Var, r ≠ EOUT_C → r ∉ D →
        State.get (State.set t cnt (List.replicate i 1)) r = State.get w r := by
      intro r a b
      rw [State.get_set_ne _ _ _ _ (fun h => b (by rw [h]; exact hcD))]
      exact hFr r a b
    obtain ⟨⟨sO, sFr⟩, sI⟩ := hstep _ _ i t0I t0C
    refine ⟨by rw [← Function.iterate_succ_apply' nxt i a0] at sI; exact sI, ?_,
      fun r a b => by rw [sFr r a b]; exact t0Fr r a b⟩
    rw [sO, t0O, hO, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, S1Cards.encNats_append, List.append_assoc]
  have key := Cmd.foldlState_range_induct body cnt n w MI h0 hstep'
  rw [Emits, Cmd.eval_forBnd, hbnd, List.length_replicate]
  exact ⟨key.2.1, key.2.2⟩

/-- `dedupK` reads its seen-set only through "is this key present". -/
theorem dedupK_congr : ∀ (es : List FlatTMTransEntry) (s1 s2 : List (Nat × Nat × Nat)),
    (∀ k, (s1.any fun j => decide (j = k)) = (s2.any fun j => decide (j = k))) →
    dedupK s1 es = dedupK s2 es := by
  intro es
  induction es with
  | nil => intro _ _ _; rfl
  | cons e es ih =>
      intro s1 s2 h
      rw [dedupK, dedupK, h (keyOf e)]
      by_cases hc : (s2.any fun j => decide (j = keyOf e)) = true
      · rw [if_pos hc, if_pos hc]; exact ih s1 s2 h
      · rw [if_neg hc, if_neg hc]
        refine congrArg _ (ih _ _ (fun k => ?_))
        simp only [List.any_cons, h k]

/-- **The entry loop's pure model.** One pass over `M.trans`; an entry is
emitted unless its key has already been seen or its source state halts. -/
def stepGo (M : FlatTM) (seen : List (Nat × Nat × Nat)) :
    List FlatTMTransEntry → List Nat
  | [] => []
  | e :: es =>
      (if (seen.any fun k => decide (k = keyOf e))
            || haltBit (M.halt.map S1Parse.bitOf) e.src_state
        then [] else entrySeg M e)
      ++ stepGo M (keyOf e :: seen) es

theorem stepGo_eq (M : FlatTM) : ∀ (es : List FlatTMTransEntry)
    (seen : List (Nat × Nat × Nat)),
    ((dedupK seen es).filter
        (fun e => !haltBit (M.halt.map S1Parse.bitOf) e.src_state)).flatMap (entrySeg M)
      = stepGo M seen es := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
      intro seen
      rw [dedupK, stepGo]
      by_cases hc : (seen.any fun k => decide (k = keyOf e)) = true
      · rw [if_pos hc, if_pos (by simp [hc])]
        rw [List.nil_append, ← ih (keyOf e :: seen)]
        refine congrArg _ (congrArg _ (dedupK_congr es seen (keyOf e :: seen) (fun k => ?_)))
        simp only [List.any_cons]
        rcases Decidable.em (keyOf e = k) with hk | hk
        · subst hk
          simp only [decide_true, Bool.true_or]
          simpa using hc
        · simp [hk]
      · rw [if_neg hc]
        by_cases hh : haltBit (M.halt.map S1Parse.bitOf) e.src_state = true
        · rw [if_pos (by simp [hh]), List.nil_append, List.filter_cons_of_neg (by simp [hh])]
          exact ih (keyOf e :: seen)
        · rw [if_neg (by simp [hc, hh]), List.filter_cons_of_pos (by simp [hh]),
            List.flatMap_cons, ih (keyOf e :: seen)]

/-- **The `stepBlocks` summand as the entry loop must produce it** — the
endpoint the next session builds against. -/
theorem stepSummand_go (M : FlatTM) (hV : validFlatTM M) (hT : M.tapes = 1) :
    (normTrans M).flatMap (entryBlocks M) = stepGo M [] M.trans := by
  rw [stepSummand_seg M hV hT]
  exact stepGo_eq M M.trans []

/-! ### `stepGo` in `emitFold_run`'s shape -/

/-- The loop's carried state: the keys already seen and the entries still to
come — exactly the seen register and the `PTRANS` cursor. -/
def stepSt : List (Nat × Nat × Nat) × List FlatTMTransEntry →
    List (Nat × Nat × Nat) × List FlatTMTransEntry
  | (seen, []) => (seen, [])
  | (seen, e :: es) => (keyOf e :: seen, es)

/-- What one iteration emits. -/
def stepOut (M : FlatTM) :
    List (Nat × Nat × Nat) × List FlatTMTransEntry → List Nat
  | (_, []) => []
  | (seen, e :: _) =>
      if (seen.any fun k => decide (k = keyOf e))
          || haltBit (M.halt.map S1Parse.bitOf) e.src_state
        then [] else entrySeg M e

theorem stepGo_iter (M : FlatTM) : ∀ (es : List FlatTMTransEntry)
    (seen : List (Nat × Nat × Nat)),
    (List.range es.length).flatMap (fun i => stepOut M (stepSt^[i] (seen, es)))
      = stepGo M seen es := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
      intro seen
      rw [show (e :: es).length = es.length + 1 from rfl, List.range_succ_eq_map,
        List.flatMap_cons, List.flatMap_map]
      refine congrArg₂ _ ?_ ?_
      · simp [stepOut]
      · rw [← ih (keyOf e :: seen)]
        refine List.flatMap_congr (fun i _ => ?_)
        rw [Function.iterate_succ_apply]
        rfl

/-- **The entry loop's obligation, fully explicit.** An `emitFold_run` with
`Inv (seen, es) t` = "the seen register holds `seen`'s keys and the cursor holds
`encSyms` of `es`'s remaining stream", `nxt = stepSt` and `out = stepOut M`,
run for `|M.trans|` iterations, emits exactly the `stepBlocks` summand. -/
theorem stepSummand_fold (M : FlatTM) (hV : validFlatTM M) (hT : M.tapes = 1) :
    (List.range M.trans.length).flatMap
        (fun i => stepOut M (stepSt^[i] ([], M.trans)))
      = (normTrans M).flatMap (entryBlocks M) := by
  rw [stepSummand_go M hV hT]
  exact stepGo_iter M M.trans []

/-! ## `UsesBelow`

The entry body stays inside `S1Program.s1RegBound = 48`; `stageC_usesBelow`
consumes this. Every card list is a six-element literal, so `simp only` unfolds
`emitList` completely and the leaves are `by decide` or a register hypothesis. -/

section Bounds

/-- The unfolding set every card's `UsesBelow` needs. -/
theorem cardCN_usesBelow (XR WR : Var) (hx : XR < 48) (hw : WR < 48) :
    Cmd.UsesBelow (cardCN XR WR) 48 := by
  simp only [cardCN, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> first | decide | assumption

theorem cardCR_usesBelow (XR WR : Var) (hx : XR < 48) (hw : WR < 48) :
    Cmd.UsesBelow (cardCR XR WR) 48 := by
  simp only [cardCR, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> first | decide | assumption

theorem cardCL_usesBelow (XR WR : Var) (hx : XR < 48) (hw : WR < 48) :
    Cmd.UsesBelow (cardCL XR WR) 48 := by
  simp only [cardCL, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> first | decide | assumption

theorem cardLN_usesBelow (WR : Var) (hw : WR < 48) : Cmd.UsesBelow (cardLN WR) 48 := by
  simp only [cardLN, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> first | decide | assumption

theorem cardLR_usesBelow (WR : Var) (hw : WR < 48) : Cmd.UsesBelow (cardLR WR) 48 := by
  simp only [cardLR, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> first | decide | assumption

theorem cardLL_usesBelow (WR : Var) (hw : WR < 48) : Cmd.UsesBelow (cardLL WR) 48 := by
  simp only [cardLL, cardLN, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> first | decide | assumption

theorem cardRN_usesBelow (YR WR : Var) (hy : YR < 48) (hw : WR < 48) :
    Cmd.UsesBelow (cardRN YR WR) 48 := by
  simp only [cardRN, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> first | decide | assumption

theorem cardRR_usesBelow (YR WR : Var) (hy : YR < 48) (hw : WR < 48) :
    Cmd.UsesBelow (cardRR YR WR) 48 := by
  simp only [cardRR, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> first | decide | assumption

theorem cardRL_usesBelow (YR WR : Var) (hy : YR < 48) (hw : WR < 48) :
    Cmd.UsesBelow (cardRL YR WR) 48 := by
  simp only [cardRL, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> first | decide | assumption

theorem cenFam_usesBelow (i1 i2 i3 : Cmd) (h1 : Cmd.UsesBelow i1 48)
    (h2 : Cmd.UsesBelow i2 48) (h3 : Cmd.UsesBelow i3 48) :
    Cmd.UsesBelow (cenFam i1 i2 i3) 48 := by
  simp only [cenFam, Cmd.UsesBelow]
  and_intros <;> first | decide | assumption

theorem lefFam_usesBelow (i1 i2 : Cmd) (h1 : Cmd.UsesBelow i1 48)
    (h2 : Cmd.UsesBelow i2 48) : Cmd.UsesBelow (lefFam i1 i2) 48 := by
  simp only [lefFam, Cmd.UsesBelow]
  and_intros <;> first | decide | assumption

theorem rigFam_usesBelow (i1 i2 : Cmd) (h1 : Cmd.UsesBelow i1 48)
    (h2 : Cmd.UsesBelow i2 48) : Cmd.UsesBelow (rigFam i1 i2) 48 := by
  simp only [rigFam, loadX, Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> first | decide | assumption

theorem inFamR_usesBelow : Cmd.UsesBelow inFamR 48 := by
  simp only [inFamR, cardIR, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> decide

theorem inFamL_usesBelow : Cmd.UsesBelow inFamL 48 := by
  simp only [inFamL, cardIL, loadX, emitCard, emitList, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> decide

theorem bodyN_usesBelow : Cmd.UsesBelow bodyN 48 := by
  refine ⟨cenFam_usesBelow _ _ _ (cardCN_usesBelow _ _ (by decide) (by decide))
      (cardCN_usesBelow _ _ (by decide) (by decide))
      (cardCN_usesBelow _ _ (by decide) (by decide)),
    lefFam_usesBelow _ _ (cardLN_usesBelow _ (by decide))
      (cardLN_usesBelow _ (by decide)),
    rigFam_usesBelow _ _ (cardRN_usesBelow _ _ (by decide) (by decide))
      (cardRN_usesBelow _ _ (by decide) (by decide)), ?_⟩
  show Op.UsesBelow (Op.copy EOUT_C EOUT_C) 48
  exact ⟨by decide, by decide⟩

theorem bodyR_usesBelow : Cmd.UsesBelow bodyR 48 :=
  ⟨cenFam_usesBelow _ _ _ (cardCR_usesBelow _ _ (by decide) (by decide))
      (cardCR_usesBelow _ _ (by decide) (by decide))
      (cardCR_usesBelow _ _ (by decide) (by decide)),
    lefFam_usesBelow _ _ (cardLR_usesBelow _ (by decide))
      (cardLR_usesBelow _ (by decide)),
    rigFam_usesBelow _ _ (cardRR_usesBelow _ _ (by decide) (by decide))
      (cardRR_usesBelow _ _ (by decide) (by decide)), inFamR_usesBelow⟩

theorem bodyL_usesBelow : Cmd.UsesBelow bodyL 48 :=
  ⟨cenFam_usesBelow _ _ _ (cardCN_usesBelow _ _ (by decide) (by decide))
      (cardCL_usesBelow _ _ (by decide) (by decide))
      (cardCL_usesBelow _ _ (by decide) (by decide)),
    lefFam_usesBelow _ _ (cardLL_usesBelow _ (by decide))
      (cardLL_usesBelow _ (by decide)),
    rigFam_usesBelow _ _ (cardRL_usesBelow _ _ (by decide) (by decide))
      (cardRL_usesBelow _ _ (by decide) (by decide)), inFamL_usesBelow⟩

/-- **The entry body stays inside the S1 register bound.** -/
theorem stepEmit_usesBelow : Cmd.UsesBelow stepEmit 48 :=
  ⟨by decide, bodyN_usesBelow, by decide, bodyR_usesBelow, bodyL_usesBelow⟩

end Bounds

end S1Step
