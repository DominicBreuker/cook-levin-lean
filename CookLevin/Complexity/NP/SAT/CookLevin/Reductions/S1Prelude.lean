import Complexity.NP.SAT.CookLevin.Reductions.S1CardEmit

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-! # S1, part 5c — stage **C**'s prelude family, the emitter-shaped model

`S1Cards.preludeBlocks` is `~96%` of the card register
(`probes/S1CardEmitProbe.lean` §3), so it is stage C's cost driver and the
family most likely to force a redesign. This file does the *model* work that
fixes the emitter's shape, before any `Cmd` is written:

```
preludeBlocks σ st q0
  = (range (2σ+5)).flatMap (fun k1 => (range (2σ+5)).flatMap (fun k2 =>
      (range (2σ+5)).flatMap (fun k3 => pBody σ st q0 k1 k2 k3)))
pBody … k1 k2 k3
  = (resOf … k1).flatMap (fun r1 => (resOf … k2).flatMap (fun r2 =>
      (resOf … k3).flatMap (fun r3 =>
        if contigB r1.2 r2.2 r3.2 then blk (sgv+k1) (sgv+k2) (sgv+k3) r1.1 r2.1 r3.1
        else [])))
```

Four findings drive the design; each is a theorem below.

## Finding 1 — the three kind loops are ALL OUTSIDE the three resolution loops

`preludeBlocks` nests `k1,k2,k3` and only then `r1,r2,r3`. An emitter that
interleaves them (`k1,r1,k2,r2,k3,r3`) emits a **permutation** of the target,
not the target — and `FlatTCCFree.encCardsIn` is order-sensitive, so the
`stageC_run` contract would be unmeetable. The kind levels must therefore hand
the resolution nest a *description* of each kind, in registers, which is what
`pKindLevel` below is.

## Finding 2 — `resOf` needs no pair-list register: a kind is 4 numbers

`S1Cards.resOf` is a `List (Nat × Nat)` whose length depends on `k`, which is
why the previous plan was to materialise it into a register and scan it. It is
not necessary. `resOf_special` / `resOf_tapeBand` / `resOf_headBand` show every
kind is one of exactly two shapes:

* **star** (`k = 2` or `k = 3`): resolutions `base, base+1, …, base+σ`, the
  first `σ` of class *live* and the last of class *cut*;
* **non-star** (every other `k`): the single resolution `base + add`, class
  *other*.

So a kind level only has to publish `(1^k, star?, 1^base, 1^add)` — four
registers — and the resolution level is one plain `forBnd` over `1^σ` plus one
extra block. No list scanning, no variable-length register.

## Finding 3 — the contiguity filter is ONE carried bit, not three class codes

`contigB` says "no *cut* strictly left of a *live*". `pBody_gate` re-expresses
the filter as a left-to-right propagation of a single boolean *"a cut has been
seen"*: at a level whose resolution is *live*, skip the whole subtree if the
bit is set; a *cut* sets it; an *other* leaves it. So the emitter carries one
flag register instead of three class codes, and the skip is one `ifBit` around
a whole loop rather than a test inside the innermost body.

## Finding 4 — the kind loop needs NO on-machine comparison

`range_seg` splits `range (2σ+5)` into the five special kinds `0,1,2,3,4` and
the two `σ`-long bands. Inside each of the seven segments the kind's shape is
*constant*, so the emitter never has to decide `k = 2`, `k < 5 + σ`, … on the
machine: seven straight-line segments replace a seven-way branch, and stage C
needs no unary comparison gadget at all.
-/

namespace S1Prelude

open Complexity.Lang Complexity.Simulators HeadLayout

/-! ## Finding 4 — the seven-segment split of a kind loop -/

/-- `range (2σ+5)` as the five special kinds followed by the two `σ`-long
bands. The emitter's kind level is exactly these seven segments. -/
theorem range_seg {α : Type} (σ : Nat) (g : Nat → List α) :
    (List.range (2 * σ + 5)).flatMap g
      = g 0 ++ (g 1 ++ (g 2 ++ (g 3 ++ (g 4 ++
          ((List.range σ).flatMap (fun d => g (5 + d)) ++
           (List.range σ).flatMap (fun d => g (5 + σ + d))))))) := by
  have hsplit : 2 * σ + 5 = 5 + σ + σ := by ring
  rw [hsplit, List.range_add, List.range_add]
  simp only [List.flatMap_append, List.flatMap_map]
  have h5 : (List.range 5).flatMap g = g 0 ++ (g 1 ++ (g 2 ++ (g 3 ++ g 4))) := by
    simp [List.range_succ]
  rw [h5]
  simp only [List.append_assoc]

/-! ## Finding 2 — a kind is four numbers

The `(star?, base, add)` triple of a kind index, with `hb` the head-cell base
`hv σ q0 0 = (σ+1)(q0+1)`. For a star kind `add` is unused (the resolution
loop supplies it); for a non-star kind the single resolution value is
`base + add`, which is what lets the emitter read *every* value off the same
two registers. -/

/-- Is `k` one of the two kinds with more than one resolution? -/
def pStar (k : Nat) : Bool := decide (k = 2) || decide (k = 3)

/-- The resolution list of a kind, in the two shapes the emitter implements.
Star kinds run `base + j` for `j < σ` at class *live* and `base + σ` at class
*cut*; every other kind is the single value `base + add` at class *other*. -/
def resShape (σ base add : Nat) (star : Bool) : List (Nat × Nat) :=
  if star then (List.range σ).map (fun j => (base + j, 1)) ++ [(base + σ, 2)]
  else [(base + add, 0)]

/-- **Finding 2.** Every kind index is one of the two shapes. Stated for the
five special kinds and the two bands separately (that is how `range_seg` hands
them to the emitter), so each clause is the exact contract of one segment. -/
theorem resOf_special (σ st q0 : Nat) :
    S1Cards.resOf σ st q0 0 = resShape σ (S1Cards.bv σ st) 0 false
    ∧ S1Cards.resOf σ st q0 1 = resShape σ 0 σ false
    ∧ S1Cards.resOf σ st q0 2 = resShape σ 0 0 true
    ∧ S1Cards.resOf σ st q0 3 = resShape σ (S1Cards.hv σ q0 0) 0 true
    ∧ S1Cards.resOf σ st q0 4 = resShape σ (S1Cards.hv σ q0 0) σ false := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [S1Cards.resOf, resShape, S1Cards.hv]

/-- The tape band `k = 5 + d`, `d < σ`: value `d`, class *other*. -/
theorem resOf_tapeBand (σ st q0 d : Nat) (hd : d < σ) :
    S1Cards.resOf σ st q0 (5 + d) = resShape σ 0 d false := by
  have h0 : ¬ (5 + d = 0) := by omega
  have h1 : ¬ (5 + d = 1) := by omega
  have h2 : ¬ (5 + d = 2) := by omega
  have h3 : ¬ (5 + d = 3) := by omega
  have h4 : ¬ (5 + d = 4) := by omega
  have h5 : 5 + d < 5 + σ := by omega
  simp only [S1Cards.resOf, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
    if_pos h5, resShape, if_neg (by decide : ¬ (false = true))]
  norm_num

/-- The head band `k = 5 + σ + d`, `d < σ`: value `hb + d`, class *other*. -/
theorem resOf_headBand (σ st q0 d : Nat) :
    S1Cards.resOf σ st q0 (5 + σ + d) = resShape σ (S1Cards.hv σ q0 0) d false := by
  have h0 : ¬ (5 + σ + d = 0) := by omega
  have h1 : ¬ (5 + σ + d = 1) := by omega
  have h2 : ¬ (5 + σ + d = 2) := by omega
  have h3 : ¬ (5 + σ + d = 3) := by omega
  have h4 : ¬ (5 + σ + d = 4) := by omega
  have h5 : ¬ (5 + σ + d < 5 + σ) := by omega
  have harg : 5 + σ + d - 5 - σ = d := by omega
  simp only [S1Cards.resOf, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
    if_neg h5, harg, resShape, if_neg (by decide : ¬ (false = true))]
  simp [S1Cards.hv]

/-! ## Finding 3 — the contiguity filter as one carried bit -/

/-- One resolution level of `pBody`, with the "a cut has been seen to the left"
bit carried in and out. A *live* resolution under a set bit contributes
nothing; a *cut* sets the bit for everything to its right. -/
def pGate (cs : Bool) (l : List (Nat × Nat)) (g : Nat → Bool → List Nat) : List Nat :=
  l.flatMap (fun r => if cs && decide (r.2 = 1) then [] else g r.1 (cs || decide (r.2 = 2)))

/-- The boolean identity behind `pBody_gate`: `contigB` is exactly "no level is
*live* under a bit set by a *cut* to its left". -/
theorem contigB_prop (c1 c2 c3 : Nat) :
    S1Cards.contigB c1 c2 c3
      = (!(decide (c1 = 2) && decide (c2 = 1))
          && !((decide (c1 = 2) || decide (c2 = 2)) && decide (c3 = 1))) := by
  unfold S1Cards.contigB
  cases hc1 : decide (c1 = 2) <;> cases hc2 : decide (c2 = 1) <;>
    cases hc3 : decide (c2 = 2) <;> cases hc4 : decide (c3 = 1) <;> rfl

/-- **Finding 3.** `pBody`'s three-class filter is a single propagated bit. -/
theorem pBody_gate (σ st q0 k1 k2 k3 : Nat) :
    S1Cards.pBody σ st q0 k1 k2 k3
      = pGate false (S1Cards.resOf σ st q0 k1) (fun v1 c1 =>
          pGate c1 (S1Cards.resOf σ st q0 k2) (fun v2 c2 =>
            pGate c2 (S1Cards.resOf σ st q0 k3) (fun v3 _ =>
              S1Cards.blk (S1Cards.sgv σ st + k1) (S1Cards.sgv σ st + k2)
                (S1Cards.sgv σ st + k3) v1 v2 v3))) := by
  unfold S1Cards.pBody pGate
  refine List.flatMap_congr (fun r1 _ => ?_)
  simp only [Bool.false_and, if_neg (by decide : ¬ (false = true)), Bool.false_or]
  refine List.flatMap_congr (fun r2 _ => ?_)
  by_cases hskip : (decide (r1.2 = 2) && decide (r2.2 = 1)) = true
  · -- the whole `r3` sub-list is filtered out on both sides
    rw [if_pos hskip]
    refine List.flatMap_eq_nil_iff.2 (fun r3 _ => ?_)
    have : S1Cards.contigB r1.2 r2.2 r3.2 = false := by
      rw [contigB_prop, hskip]; rfl
    rw [this]; rfl
  · rw [if_neg hskip]
    refine List.flatMap_congr (fun r3 _ => ?_)
    have hc : S1Cards.contigB r1.2 r2.2 r3.2
        = !((decide (r1.2 = 2) || decide (r2.2 = 2)) && decide (r3.2 = 1)) := by
      rw [contigB_prop, Bool.eq_false_iff.2 hskip]; rfl
    rw [hc]
    cases h : ((decide (r1.2 = 2) || decide (r2.2 = 2)) && decide (r3.2 = 1)) <;> rfl

/-! ## The emitter-shaped statement of the whole family

`preludeSeg` is `preludeBlocks` with all four findings applied: the kind loops
split into seven constant-shape segments (Finding 4), each kind reduced to
`(k, star?, base, add)` (Finding 2), and the resolution nest reduced to a
single carried bit (Finding 3). **This is the shape the emitter implements**,
one `Cmd` per structural constructor. -/

/-- One kind level: seven segments, each publishing a kind description to the
continuation `g` (which receives `k`, `star?`, `base`, `add`). -/
def pKindLevel {α : Type} (σ st q0 : Nat) (g : Nat → Bool → Nat → Nat → List α) :
    List α :=
  g 0 false (S1Cards.bv σ st) 0 ++
  (g 1 false 0 σ ++
   (g 2 true 0 0 ++
    (g 3 true (S1Cards.hv σ q0 0) 0 ++
     (g 4 false (S1Cards.hv σ q0 0) σ ++
      ((List.range σ).flatMap (fun d => g (5 + d) false 0 d) ++
       (List.range σ).flatMap (fun d => g (5 + σ + d) false (S1Cards.hv σ q0 0) d))))))

/-- A kind level equals the plain `range (2σ+5)` loop it stands for, as long as
the continuation only depends on `k` through its shape. -/
theorem pKindLevel_eq {α : Type} (σ st q0 : Nat) (g : Nat → Bool → Nat → Nat → List α)
    (G : Nat → List α)
    (hG : ∀ k star base add, S1Cards.resOf σ st q0 k = resShape σ base add star →
      G k = g k star base add) :
    (List.range (2 * σ + 5)).flatMap G = pKindLevel σ st q0 g := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := resOf_special σ st q0
  rw [range_seg σ G, hG 0 false _ 0 e0, hG 1 false 0 σ e1, hG 2 true 0 0 e2,
    hG 3 true _ 0 e3, hG 4 false _ σ e4]
  unfold pKindLevel
  refine congrArg _ (congrArg _ (congrArg _ (congrArg _ (congrArg _ ?_))))
  refine congrArg₂ _ (List.flatMap_congr (fun d hd => ?_)) (List.flatMap_congr (fun d _ => ?_))
  · exact hG _ false 0 d (resOf_tapeBand σ st q0 d (List.mem_range.1 hd))
  · exact hG _ false _ d (resOf_headBand σ st q0 d)

/-- One resolution level, in the two shapes `resShape` allows. -/
def pResLevel (σ base add : Nat) (star cs : Bool) (g : Nat → Bool → List Nat) :
    List Nat :=
  if star then
    (if cs then [] else (List.range σ).flatMap (fun j => g (base + j) false))
      ++ g (base + σ) true
  else g (base + add) cs

theorem pGate_resShape (σ base add : Nat) (star cs : Bool) (g : Nat → Bool → List Nat) :
    pGate cs (resShape σ base add star) g = pResLevel σ base add star cs g := by
  cases star with
  | false =>
      simp only [resShape, pResLevel, pGate, if_neg (by decide : ¬ (false = true))]
      simp
  | true =>
      simp only [resShape, pResLevel, pGate]
      cases cs <;> simp [List.flatMap_map]

/-- **The prelude family, in the emitter's shape.** Three kind levels, each
seven constant-shape segments, then three resolution levels carrying one bit. -/
def preludeSeg (σ st q0 : Nat) : List Nat :=
  pKindLevel σ st q0 (fun k1 s1 b1 a1 =>
    pKindLevel σ st q0 (fun k2 s2 b2 a2 =>
      pKindLevel σ st q0 (fun k3 s3 b3 a3 =>
        pResLevel σ b1 a1 s1 false (fun v1 c1 =>
          pResLevel σ b2 a2 s2 c1 (fun v2 c2 =>
            pResLevel σ b3 a3 s3 c2 (fun v3 _ =>
              S1Cards.blk (S1Cards.sgv σ st + k1) (S1Cards.sgv σ st + k2)
                (S1Cards.sgv σ st + k3) v1 v2 v3))))))

/-- **The reformulation is faithful.** -/
theorem preludeBlocks_seg (σ st q0 : Nat) :
    S1Cards.preludeBlocks σ st q0 = preludeSeg σ st q0 := by
  unfold S1Cards.preludeBlocks preludeSeg
  refine pKindLevel_eq σ st q0 _ _ (fun k1 s1 b1 a1 h1 => ?_)
  refine pKindLevel_eq σ st q0 _ _ (fun k2 s2 b2 a2 h2 => ?_)
  refine pKindLevel_eq σ st q0 _ _ (fun k3 s3 b3 a3 h3 => ?_)
  rw [pBody_gate]
  simp only [h1, h2, h3, pGate_resShape]


/-! ## The emitter's two new atoms

Both are needed by `stepBlocks` as well, so they live here rather than inside
the prelude's own section.

* **`emitList`** — a straight run of `emitBlk2`s over a *list* of source pairs.
  `S1CardEmit.emitId` is the special case "six blocks, `p₁p₂p₃p₁p₂p₃`"; the two
  remaining families both emit six *different* values, so the identity atom no
  longer serves and the general list form does.
* **`minReg`** — `dst := 1^(min a b)` by draining one unary register inside a
  loop bounded by the other. `S1Cards.preludeBlocks` is applied at
  `min M.start M.states` and `S1Cards.entryBlocks` clamps both of its states
  the same way, so every remaining piece of stage C needs it. No comparison
  gadget is involved: `nonEmpty` on the drain *is* the test. -/

open S1Emit S1CardEmit

/-- A straight run of two-source blocks: one `FlatTCCFree.encNat (|p.1|+|p.2|)`
appended per pair, in order. -/
def emitList (cnt dst : Var) : List (Var × Var) → Cmd
  | [] => Cmd.op (.copy dst dst)
  | p :: ps => emitBlk2 cnt p.1 p.2 dst ;; emitList cnt dst ps

/-- **The list emitter is correct.** `val` reads each source register's value,
so a register may safely appear in several pairs. -/
theorem emitList_run (cnt dst : Var) (val : Var → Nat) (hcd : cnt ≠ dst) :
    ∀ (ps : List (Var × Var)) (s : State),
      (∀ p ∈ ps, p.1 ≠ dst ∧ p.1 ≠ cnt ∧ p.2 ≠ dst ∧ p.2 ≠ cnt) →
      (∀ p ∈ ps, State.get s p.1 = List.replicate (val p.1) 1
        ∧ State.get s p.2 = List.replicate (val p.2) 1) →
      State.get ((emitList cnt dst ps).eval s) dst
          = State.get s dst
            ++ FlatTCCFree.encNats (ps.map (fun p => val p.1 + val p.2))
      ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
          State.get ((emitList cnt dst ps).eval s) r = State.get s r) := by
  intro ps
  induction ps with
  | nil =>
      intro s _ _
      refine ⟨?_, fun r _ _ => copy_self_get dst r s⟩
      show State.get ((Cmd.op (.copy dst dst)).eval s) dst = _
      rw [copy_self_get]
      simp [FlatTCCFree.encNats]
  | cons p ps ih =>
      intro s hne hval
      obtain ⟨hp1d, hp1c, hp2d, hp2c⟩ := hne p (List.mem_cons_self ..)
      obtain ⟨hv1, hv2⟩ := hval p (List.mem_cons_self ..)
      obtain ⟨hD, hF⟩ := emitBlk2_run cnt p.1 p.2 dst s (val p.1) (val p.2)
        hcd hp2d hp2c hv1 hv2
      set s1 := (emitBlk2 cnt p.1 p.2 dst).eval s with hs1
      clear_value s1
      obtain ⟨hD', hF'⟩ := ih s1
        (fun q hq => hne q (List.mem_cons_of_mem _ hq))
        (fun q hq => by
          obtain ⟨q1d, q1c, q2d, q2c⟩ := hne q (List.mem_cons_of_mem _ hq)
          obtain ⟨e1, e2⟩ := hval q (List.mem_cons_of_mem _ hq)
          exact ⟨by rw [hF q.1 q1d q1c]; exact e1, by rw [hF q.2 q2d q2c]; exact e2⟩)
      have hev : (emitList cnt dst (p :: ps)).eval s = (emitList cnt dst ps).eval s1 := by
        rw [hs1]; show (emitBlk2 cnt p.1 p.2 dst ;; emitList cnt dst ps).eval s = _
        rw [Cmd.eval_seq]
      refine ⟨?_, fun r a b => by rw [hev, hF' r a b]; exact hF r a b⟩
      rw [hev, hD', hD, List.map_cons]
      show _ = _ ++ (FlatTCCFree.encNat _ ++ _)
      rw [List.append_assoc]

/-! ### `minReg` -/

/-- One iteration: if the drain is non-empty, take one cell off it and add one
to the result. -/
def minBody (flag drain dst : Var) : Cmd :=
  Cmd.op (.nonEmpty flag drain) ;;
  Cmd.ifBit flag (Cmd.op (.appendOne dst) ;; Cmd.op (.tail drain drain))
    (Cmd.op (.copy dst dst))

/-- `dst := 1^(min |bnd| |drain|)`; `drain` is consumed. -/
def minReg (cnt flag bnd drain dst : Var) : Cmd :=
  Cmd.op (.clear dst) ;; Cmd.forBnd cnt bnd (minBody flag drain dst)

theorem minReg_run (cnt flag bnd drain dst : Var) (a b : Nat) (s : State)
    (hdc : dst ≠ cnt) (hdf : dst ≠ flag) (hdd : dst ≠ drain)
    (hrc : drain ≠ cnt) (hrf : drain ≠ flag)
    (hbnd : State.get s bnd = List.replicate a 1)
    (hdr : State.get s drain = List.replicate b 1) (hbd : bnd ≠ dst) :
    State.get ((minReg cnt flag bnd drain dst).eval s) dst
        = List.replicate (min a b) 1
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt → r ≠ flag → r ≠ drain →
        State.get ((minReg cnt flag bnd drain dst).eval s) r = State.get s r) := by
  set u := (Cmd.op (.clear dst)).eval s with hu
  have uD : State.get u dst = [] := by rw [hu, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]
  have uFr : ∀ r : Var, r ≠ dst → State.get u r = State.get s r := by
    intro r hr; rw [hu, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u
  have hrd : drain ≠ dst := Ne.symm hdd
  have uB : State.get u bnd = List.replicate a 1 := by rw [uFr bnd hbd]; exact hbnd
  have uR : State.get u drain = List.replicate b 1 := by rw [uFr drain hrd]; exact hdr
  set MI : Nat → State → Prop := fun i t =>
    State.get t dst = List.replicate (min i b) 1
    ∧ State.get t drain = List.replicate (b - i) 1
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt → r ≠ flag → r ≠ drain →
        State.get t r = State.get u r) with hMI
  have h0 : MI 0 u := ⟨by rw [uD, Nat.zero_min]; rfl, by rw [uR, Nat.sub_zero],
    fun _ _ _ _ _ => rfl⟩
  have hstep : ∀ i t, i < (State.get u bnd).length → MI i t →
      MI (i + 1) ((minBody flag drain dst).eval (t.set cnt (List.replicate i 1))) := by
    intro i t _ hM
    obtain ⟨pD, pR, pFr⟩ := hM
    set t0 := t.set cnt (List.replicate i 1) with ht0
    have q0D : State.get t0 dst = List.replicate (min i b) 1 := by
      rw [ht0, State.get_set_ne _ _ _ _ hdc]; exact pD
    have q0R : State.get t0 drain = List.replicate (b - i) 1 := by
      rw [ht0, State.get_set_ne _ _ _ _ hrc]; exact pR
    have q0Fr : ∀ r : Var, r ≠ dst → r ≠ cnt → r ≠ flag → r ≠ drain →
        State.get t0 r = State.get u r := by
      intro r a1 a2 a3 a4; rw [ht0, State.get_set_ne _ _ _ _ a2]; exact pFr r a1 a2 a3 a4
    clear_value t0
    set v1 := (Cmd.op (.nonEmpty flag drain)).eval t0 with hv1
    have v1F : State.get v1 flag
        = if (List.replicate (b - i) 1 : List Nat).isEmpty then [0] else [1] := by
      rw [hv1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, q0R]
    have v1Fr : ∀ r : Var, r ≠ flag → State.get v1 r = State.get t0 r := by
      intro r hr; rw [hv1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
    clear_value v1
    have hev : (minBody flag drain dst).eval t0
        = (Cmd.ifBit flag (Cmd.op (.appendOne dst) ;; Cmd.op (.tail drain drain))
            (Cmd.op (.copy dst dst))).eval v1 := by
      rw [hv1]; unfold minBody; rw [Cmd.eval_seq]
    by_cases hlt : i < b
    · -- the drain still has a cell: take it
      have hne : b - i = (b - i - 1) + 1 := by omega
      have htrue : State.get v1 flag = [1] := by
        rw [v1F, hne]; simp
      have vD : State.get v1 dst = List.replicate (min i b) 1 := by
        rw [v1Fr dst hdf]; exact q0D
      have vR : State.get v1 drain = List.replicate (b - i) 1 := by
        rw [v1Fr drain hrf]; exact q0R
      refine ⟨?_, ?_, ?_⟩
      · rw [hev, Cmd.eval_ifBit_true _ _ _ _ htrue, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
        simp only [Op.eval, State.get_set_ne _ _ _ _ hdd, State.get_set_eq, vD]
        rw [← List.replicate_succ']
        congr 1
        omega
      · rw [hev, Cmd.eval_ifBit_true _ _ _ _ htrue, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq, State.get_set_ne _ _ _ _ hrd, vR]
        rw [hne, List.replicate_succ, List.tail_cons,
          show b - i - 1 = b - (i + 1) from by omega]
      · intro r a1 a2 a3 a4
        rw [hev, Cmd.eval_ifBit_true _ _ _ _ htrue, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
        simp only [Op.eval, State.get_set_ne _ _ _ _ a4, State.get_set_ne _ _ _ _ a1]
        rw [v1Fr r a3]; exact q0Fr r a1 a2 a3 a4
    · -- the drain is empty: nothing left to take
      have hbi : b - i = 0 := by omega
      have hfalse : State.get v1 flag ≠ [1] := by
        rw [v1F, hbi]; simp
      have vD : State.get v1 dst = List.replicate (min i b) 1 := by
        rw [v1Fr dst hdf]; exact q0D
      have vR : State.get v1 drain = List.replicate (b - i) 1 := by
        rw [v1Fr drain hrf]; exact q0R
      refine ⟨?_, ?_, ?_⟩
      · rw [hev, Cmd.eval_ifBit_false _ _ _ _ hfalse, copy_self_get, vD]
        congr 1
        omega
      · rw [hev, Cmd.eval_ifBit_false _ _ _ _ hfalse, copy_self_get, vR]
        congr 1
        omega
      · intro r a1 a2 a3 a4
        rw [hev, Cmd.eval_ifBit_false _ _ _ _ hfalse, copy_self_get, v1Fr r a3]
        exact q0Fr r a1 a2 a3 a4
  have key := Cmd.foldlState_range_induct (minBody flag drain dst) cnt
    (State.get u bnd).length u MI h0 hstep
  rw [uB, List.length_replicate] at key
  obtain ⟨kD, -, kFr⟩ := key
  have hev : (minReg cnt flag bnd drain dst).eval s
      = (Cmd.forBnd cnt bnd (minBody flag drain dst)).eval u := by
    rw [hu]; unfold minReg; rw [Cmd.eval_seq]
  rw [hev, Cmd.eval_forBnd, uB, List.length_replicate]
  exact ⟨kD, fun r a1 a2 a3 a4 => by rw [kFr r a1 a2 a3 a4]; exact uFr r a1⟩

/-! ## The prelude emitter's register frame

Stage C's dirty licence `S1Program.CDirty` is the P/G scratch block `[14,32)`,
the shared emitter scratch `[37,48)` and `EOUT_C` — **30 registers**, and the
prelude family uses **all 30** (`ESG` and `EK1` keep their `S1Emit` /
`S1CardEmit` roles; `PCS3` deliberately re-uses `loadSg`'s scratch `EA`, which
is dead once the preamble has finished). `probes/S1PreludeProbe.lean` §3 prints
the licensed-but-unused set and it is **empty**. So there is no head-room left
inside stage C's licence: `stepBlocks` runs *before* the prelude and must reuse
this same pool rather than claim new registers — or `CDirty`, and with it
`S1Program.stageC_run` and `cFive_frame`, has to be widened.

```
14 PBV  1^(bv σ st)     19 PKV2 1^k₂    23 PKV3 1^k₃    28 PJ1  level 1's j
15 PKV1 1^k₁            20 PST2 star?   24 PST3 star?   29 PJ2  level 2's j
16 PST1 star?           21 PPA2 1^base  25 PPA3 1^base  30 PJ3  level 3's j
17 PPA1 1^base          22 PKC2 band    26 PKC3 band    31 PCS2 cut-seen ₂
18 PKC1 band counter    27 PZ   []                      38 PCS3 cut-seen ₃

37 ESG  1^(Sg M) = 1^sgv        43 PCN  preamble loop counter
39 PHB  1^(hv σ q0 0)           44 PA1  1^(q0+1)      46 EK1 the block tally
40 PB5  1^5                     45 PA2  1^(σ+1)       47 PFL preamble flag
41 PQ0  1^q0                    42 PDR  the min drain
```
-/

/-- `1^(bv σ st)` — the boundary-marker code (`ESG` minus its top cell). -/
def PBV  : Var := 14
/-- Level 1's kind index `1^k₁` (the first premise cell is `|ESG| + |PKV1|`). -/
def PKV1 : Var := 15
/-- Level 1's "is this a star kind?" flag. -/
def PST1 : Var := 16
/-- Level 1's resolution base. -/
def PPA1 : Var := 17
/-- Level 1's band-segment counter. -/
def PKC1 : Var := 18
def PKV2 : Var := 19
def PST2 : Var := 20
def PPA2 : Var := 21
def PKC2 : Var := 22
def PKV3 : Var := 23
def PST3 : Var := 24
def PPA3 : Var := 25
def PKC3 : Var := 26
/-- Permanently `[]` — the second source of every one-value block. -/
def PZ   : Var := 27
/-- Level 1's resolution counter, *and* the second source of its value cell. -/
def PJ1  : Var := 28
def PJ2  : Var := 29
def PJ3  : Var := 30
/-- The cut-seen bit entering level 2 (level 1's is always `false`). -/
def PCS2 : Var := 31
/-- The cut-seen bit entering level 3. -/
def PCS3 : Var := 38
/-- `1^(hv σ q0 0)` — the head band's base, `(σ+1)(q0+1)`. -/
def PHB  : Var := 39
/-- `1^5` — the head of the head band's kind index. -/
def PB5  : Var := 40
/-- `1^q0`, `q0 = min M.start M.states`. -/
def PQ0  : Var := 41
/-- The `minReg` drain. -/
def PDR  : Var := 42
/-- The preamble's loop counter. -/
def PCN  : Var := 43
/-- `1^(q0+1)` — the multiplication's bound. -/
def PA1  : Var := 44
/-- `1^(σ+1)` — the multiplication's source. -/
def PA2  : Var := 45
/-- The preamble's branch flag. -/
def PFL  : Var := 47

/-- Everything the preamble writes. -/
def PD : List Var :=
  [ESG, EA, PHB, PBV, PZ, PB5, PQ0, PDR, PCN, PA1, PA2, PFL]

/-- **The prelude emitter's constants.** Every register the kind and resolution
levels read but never write. -/
def PConst (σ st q0 : Nat) (t : State) : Prop :=
  State.get t ESG = List.replicate (S1Cards.sgv σ st) 1
  ∧ State.get t PBV = List.replicate (S1Cards.bv σ st) 1
  ∧ State.get t PZ = []
  ∧ State.get t PB5 = List.replicate 5 1
  ∧ State.get t PHB = List.replicate (S1Cards.hv σ q0 0) 1

/-! ## The preamble

`min M.start M.states` and the head-cell base `(σ+1)(q0+1)` are the only two
values stage C's last family needs that no earlier stage computes. The `min` is
`minReg` (no comparison gadget); the product is one `unaryMulLoop`, stage C's
second and last multiplication — both hoisted out of every loop. -/

def pB5Blk : Cmd :=
  Cmd.op (.clear PB5) ;; Cmd.op (.appendOne PB5) ;; Cmd.op (.appendOne PB5) ;;
  Cmd.op (.appendOne PB5) ;; Cmd.op (.appendOne PB5) ;; Cmd.op (.appendOne PB5)

def pConstBlk : Cmd :=
  Cmd.op (.tail PBV ESG) ;; Cmd.op (.clear PZ) ;; pB5Blk ;;
  Cmd.op (.copy PDR S1Parse.PSTATES)

def pMulBlk : Cmd :=
  Cmd.op (.copy PA1 PQ0) ;; Cmd.op (.appendOne PA1) ;;
  Cmd.op (.copy PA2 S1Parse.PSIG) ;; Cmd.op (.appendOne PA2) ;;
  Cmd.op (.clear PHB) ;;
  Cmd.forBnd PCN PA1 (Cmd.op (.concat PHB PHB PA2))

/-- **The prelude family's preamble.** -/
def pPre : Cmd :=
  S1Emit.loadSg ;; pConstBlk ;; minReg PCN PFL S1Parse.PSTART PDR PQ0 ;; pMulBlk

/-- **The preamble is correct.** -/
theorem pPre_run (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (hstart : State.get s S1Parse.PSTART = List.replicate M.start 1) :
    PConst M.sig M.states (min M.start M.states) (pPre.eval s)
    ∧ (∀ r : Var, r ∉ PD → State.get (pPre.eval s) r = State.get s r) := by
  -- Γ-band width
  obtain ⟨hSG, hFr⟩ := S1Emit.loadSg_run M s hsig hst
  set u := S1Emit.loadSg.eval s with hu
  have uFr : ∀ r : Var, r ∉ PD → State.get u r = State.get s r := by
    intro r hr
    rw [hu]
    exact hFr r (ne_of_nmem hr (by decide)) (ne_of_nmem hr (by decide))
      (ne_of_nmem hr (by decide)) (ne_of_nmem hr (by decide))
  have uSGv : State.get u ESG = List.replicate (S1Cards.sgv M.sig M.states) 1 := by
    rw [hSG, S1Cards.sgv_eq]
  clear_value u
  clear hSG hFr
  -- the straight-line constants
  set v := pConstBlk.eval u with hv
  have vSG : State.get v ESG = List.replicate (S1Cards.sgv M.sig M.states) 1 := by
    rw [hv]
    simp only [pConstBlk, pB5Blk, Cmd.eval_seq, Cmd.eval_op, Op.eval]
    repeat first
      | rw [State.get_set_ne _ _ _ _ (by decide : (ESG : Var) ≠ _)]
    exact uSGv
  have vBV : State.get v PBV = List.replicate (S1Cards.bv M.sig M.states) 1 := by
    rw [hv]
    simp only [pConstBlk, pB5Blk, Cmd.eval_seq, Cmd.eval_op, Op.eval]
    repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [uSGv]
    show (List.replicate (S1Cards.bv M.sig M.states + 1) 1).tail = _
    rw [List.replicate_succ, List.tail_cons]
  have vZ : State.get v PZ = [] := by
    rw [hv]
    simp only [pConstBlk, pB5Blk, Cmd.eval_seq, Cmd.eval_op, Op.eval]
    repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
  have vB5 : State.get v PB5 = List.replicate 5 1 := by
    rw [hv]
    simp only [pConstBlk, pB5Blk, Cmd.eval_seq, Cmd.eval_op, Op.eval]
    repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rfl
  have vDR : State.get v PDR = List.replicate M.states 1 := by
    rw [hv]
    simp only [pConstBlk, pB5Blk, Cmd.eval_seq, Cmd.eval_op, Op.eval]
    repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [uFr S1Parse.PSTATES (by decide)]; exact hst
  have vFr : ∀ r : Var, r ∉ PD → State.get v r = State.get u r := by
    intro r hr
    have n1 : r ≠ PBV := ne_of_nmem hr (by decide)
    have n2 : r ≠ PZ := ne_of_nmem hr (by decide)
    have n3 : r ≠ PB5 := ne_of_nmem hr (by decide)
    have n4 : r ≠ PDR := ne_of_nmem hr (by decide)
    rw [hv]
    simp only [pConstBlk, pB5Blk, Cmd.eval_seq, Cmd.eval_op, Op.eval]
    repeat first
      | rw [State.get_set_ne _ _ _ _ n1]
      | rw [State.get_set_ne _ _ _ _ n2]
      | rw [State.get_set_ne _ _ _ _ n3]
      | rw [State.get_set_ne _ _ _ _ n4]
  clear_value v
  -- q0 := min start states
  obtain ⟨wQ, wF⟩ := minReg_run PCN PFL S1Parse.PSTART PDR PQ0 M.start M.states v
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [vFr S1Parse.PSTART (by decide), uFr S1Parse.PSTART (by decide)]; exact hstart)
    vDR (by decide)
  set w := (minReg PCN PFL S1Parse.PSTART PDR PQ0).eval v with hw
  have wG : ∀ r : Var, r ∉ PD → State.get w r = State.get v r := fun r hr =>
    wF r (ne_of_nmem hr (by decide)) (ne_of_nmem hr (by decide))
      (ne_of_nmem hr (by decide)) (ne_of_nmem hr (by decide))
  have wSG : State.get w ESG = List.replicate (S1Cards.sgv M.sig M.states) 1 := by
    rw [wF ESG (by decide) (by decide) (by decide) (by decide)]; exact vSG
  have wBV : State.get w PBV = List.replicate (S1Cards.bv M.sig M.states) 1 := by
    rw [wF PBV (by decide) (by decide) (by decide) (by decide)]; exact vBV
  have wZ : State.get w PZ = [] := by
    rw [wF PZ (by decide) (by decide) (by decide) (by decide)]; exact vZ
  have wB5 : State.get w PB5 = List.replicate 5 1 := by
    rw [wF PB5 (by decide) (by decide) (by decide) (by decide)]; exact vB5
  have wSig : State.get w S1Parse.PSIG = List.replicate M.sig 1 := by
    rw [wG S1Parse.PSIG (by decide), vFr S1Parse.PSIG (by decide),
      uFr S1Parse.PSIG (by decide)]; exact hsig
  clear_value w
  -- the head-cell base
  have hev : pPre.eval s = pMulBlk.eval w := by
    rw [hw, hv, hu]; unfold pPre; rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  set x1 := (Cmd.op (.copy PA1 PQ0) ;; Cmd.op (.appendOne PA1) ;;
      Cmd.op (.copy PA2 S1Parse.PSIG) ;; Cmd.op (.appendOne PA2) ;;
      Cmd.op (.clear PHB)).eval w with hx1
  have x1A1 : State.get x1 PA1 = List.replicate (min M.start M.states + 1) 1 := by
    rw [hx1]
    simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [wQ, ← List.replicate_succ']
  have x1A2 : State.get x1 PA2 = List.replicate (M.sig + 1) 1 := by
    rw [hx1]
    simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [wSig, ← List.replicate_succ']
  have x1HB : State.get x1 PHB = [] := by
    rw [hx1]
    simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_eq]
  have x1Fr : ∀ r : Var, r ≠ PA1 → r ≠ PA2 → r ≠ PHB → State.get x1 r = State.get w r := by
    intro r a1 a2 a3
    rw [hx1]
    simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    repeat first
      | rw [State.get_set_ne _ _ _ _ a1]
      | rw [State.get_set_ne _ _ _ _ a2]
      | rw [State.get_set_ne _ _ _ _ a3]
  clear_value x1
  obtain ⟨mO, mF⟩ := BinaryCCFSATFree.unaryMulLoop_run PCN PA1 PA2 PHB x1
    (M.sig + 1) (min M.start M.states + 1)
    (by decide) (by decide) (by decide) x1A2 (by rw [x1A1, List.length_replicate]) x1HB
  have hev2 : pMulBlk.eval w = (Cmd.forBnd PCN PA1 (Cmd.op (.concat PHB PHB PA2))).eval x1 := by
    rw [hx1]; simp only [pMulBlk, Cmd.eval_seq]
  have hHB : (min M.start M.states + 1) * (M.sig + 1)
      = S1Cards.hv M.sig (min M.start M.states) 0 := by
    show _ = (M.sig + 1) * (min M.start M.states + 1) + 0
    exact Nat.mul_comm _ _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hev, hev2, mF ESG (by decide) (by decide), x1Fr ESG (by decide) (by decide) (by decide)]
    exact wSG
  · rw [hev, hev2, mF PBV (by decide) (by decide), x1Fr PBV (by decide) (by decide) (by decide)]
    exact wBV
  · rw [hev, hev2, mF PZ (by decide) (by decide), x1Fr PZ (by decide) (by decide) (by decide)]
    exact wZ
  · rw [hev, hev2, mF PB5 (by decide) (by decide), x1Fr PB5 (by decide) (by decide) (by decide)]
    exact wB5
  · rw [hev, hev2, mO, hHB]
  · intro r hr
    rw [hev, hev2, mF r (ne_of_nmem hr (by decide)) (ne_of_nmem hr (by decide)),
      x1Fr r (ne_of_nmem hr (by decide)) (ne_of_nmem hr (by decide))
        (ne_of_nmem hr (by decide)), wG r hr, vFr r hr]
    exact uFr r hr

/-- **The preamble stays inside the S1 register bound.** -/
theorem pPre_usesBelow : Cmd.UsesBelow pPre 48 := by
  unfold pPre
  refine ⟨S1Emit.loadSg_usesBelow, ?_, ?_, ?_⟩
  · simp [pConstBlk, pB5Blk, Cmd.UsesBelow, Op.UsesBelow, PBV, PZ, PB5, PDR, ESG,
      S1Parse.PSTATES]
  · simp [minReg, minBody, Cmd.UsesBelow, Op.UsesBelow, PCN, PFL, PDR, PQ0,
      S1Parse.PSTART]
  · simp [pMulBlk, Cmd.UsesBelow, Op.UsesBelow, PA1, PA2, PHB, PQ0, PCN,
      S1Parse.PSIG]

/-- **Every register the prelude family uses is inside stage C's licence** —
`S1Program.CDirty` is exactly `EScratch ∨ r = EOUT_C ∨ (14 ≤ r < 32)`, and the
right-hand disjunction below is what the family needs. Stated numerically
because `S1Program` imports *this* file's neighbour, not the other way round;
`S1Program.mem_AD_cases` is the same shape for `cFive`. -/
def PAll : List Var :=
  PD ++ [PKV1, PST1, PPA1, PKC1, PKV2, PST2, PPA2, PKC2,
    PKV3, PST3, PPA3, PKC3, PJ1, PJ2, PJ3, PCS2, PCS3, EK1]

theorem prelude_regs_cdirty {r : Var} (hr : r ∈ PAll) :
    (14 ≤ r ∧ r < 32) ∨ (37 ≤ r ∧ r < 48) := by
  simp only [PAll, PD] at hr
  fin_cases hr <;> decide

end S1Prelude
