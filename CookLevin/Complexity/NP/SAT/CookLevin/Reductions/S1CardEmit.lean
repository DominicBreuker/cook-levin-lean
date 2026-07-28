import Complexity.NP.SAT.CookLevin.Reductions.S1Emit

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-! # S1, part 5b — stage **C**'s copy and halt card families

The first five of stage C's seven card families (`S1Cards.cardBlocks`'s first
five summands), plus the two reusable atoms every family is built from and the
preamble that loads stage C's constants.

```
cardBlocks M = copyBlocks ++ copyRightBlocks
             ++ haltLeftBlocks ++ haltCenterBlocks ++ haltRightBlocks   -- HERE
             ++ (normTrans M).flatMap (entryBlocks M) ++ preludeBlocks  -- NEXT
```

## The two atoms

* **`emitList`** — a straight run of two-source blocks. Every value stage C
  emits is either one register's length or the *sum of two* (HANDOFF finding 3:
  the head-cell code `hv sig q b = (sig+1)(q+1) + b` is an incrementally
  maintained base plus the inner loop's own counter, never a product computed
  inside a loop). The permanently empty register `CZ` supplies the `0` for the
  one-source values, so a single atom serves both shapes.
* **`emitId`** — six blocks in the shape `p₁ p₂ p₃ p₁ p₂ p₃`. **All five
  families here emit identity cards** (copy = the identity away from the head,
  halt = the freeze), so this one lemma is their entire innermost body.

## The loop principle

**`emitLoop_run`** is the reusable `forBnd` invariant for an emitter: if the
body appends `encNats (f i)` at iteration `i` and touches only the registers in
a dirty list `D`, the loop appends `encNats ((List.range n).flatMap f)`. Every
family below is two to four applications of it. The dirty list is per-level and
deliberately small — the *point* is that the constants (`CS1`/`CS2`/`CQ1`/
`CBV`/`CZ`) and the outer counters are outside it, so their values transport
into the body for free.

## Findings of this session (2026-07-26-c)

1. **All five families are identity cards** — premise = conclusion, cell for
   cell. This is what collapses five innermost bodies into one `emitId_run`.
   (It will *not* hold for `stepBlocks`, whose conclusions move the head; that
   family needs a genuine six-value emitter.)
2. **A no-op `Cmd` exists and is needed**: `Cmd.op (.copy r r)` is a semantic
   identity on every register (`get_set_eq` on `r`, `get_set_ne` elsewhere) yet
   is *not* frame-visible as a write of anything but `r`. Taking `r := dst` gives
   an else-branch for `Cmd.ifBit` that the emitter's frame clause accepts
   verbatim — `S1Emit.enop` (which clears `EK1`) cannot be used here because
   `EK1` is stage C's block counter.
3. **`xv` is not incremental, so it is recomputed per iteration** —
   `xv sig states x` is the boundary code `bv` at `x = 0` and `x - 1` after,
   so the `x` loops rebuild `CX` from their own counter each time
   (`loadX`: one `nonEmpty` + one `ifBit` + one `tail`), instead of carrying a
   value register the way the head-cell base `CH` is carried.
4. **The halt gate is `stageFin`'s drain, reused verbatim** — `CD` drains
   `PHALT` one `head` cell per `q`, and a drained-empty `head` reads as *false*,
   which is exactly `M.halt.getD` out of range (`S1Emit`'s finding 1). So the
   halt families need no `|halt| = states` hypothesis either.

## The register frame (inside `S1Program.CDirty`)

Stage C owns the P/G scratch block `[14, 32)` on top of the shared emitter
scratch `[37, 48)`. The constants live in the former, the counters in the
latter.

```
14 CBV  1^(bv sig states)      21 CX  1^(xv sig states x)   43 EJ1  loop counter
18 CS1  1^(sig+1)              23 CH  1^((sig+1)(q+1))      44 EJ2  loop counter
19 CS2  1^(sig+2)              24 CD  the draining PHALT    45 EJ3  loop counter
20 CQ1  1^(states+1)           25 CE  the popped halt bit   46 EK1  block counter
27 CZ   [] (the zero source)   42 EE  loadX's branch flag   47 EK2  loop counter
```
-/

namespace S1CardEmit

open Complexity.Lang Complexity.Simulators HeadLayout S1Emit

/-! ## The register frame -/

/-- `1^(bv sig states)` — the boundary-marker cell code. -/
def CBV : Var := 14
/-- `1^(sig+1)` — the bound of every symbol loop. -/
def CS1 : Var := 18
/-- `1^(sig+2)` — the bound of every `xOpts` loop. -/
def CS2 : Var := 19
/-- `1^(states+1)` — the bound of the halt families' `q` loop. -/
def CQ1 : Var := 20
/-- `1^(xv sig states x)` — the current left-context cell, rebuilt per `x`. -/
def CX  : Var := 21
/-- `1^((sig+1)·(q+1))` — the head-cell base, advanced once per `q`. -/
def CH  : Var := 23
/-- The draining copy of `S1Parse.PHALT`. -/
def CD  : Var := 24
/-- The halt bit popped off `CD`. -/
def CE  : Var := 25
/-- Permanently `[]` — the second source of every one-value block. -/
def CZ  : Var := 27

/-- **Stage C's dirty list**: every register the five family emitters write
besides `S1Emit.EOUT_C`. All of it is inside `S1Program.CDirty`. -/
def HD : List Var := [CX, CH, CD, CE, EE, EJ1, EJ2, EJ3, EK1, EK2]

/-- What a halt family's *inner* nest may dirty: `HD` minus the gate's own
registers (`CH`/`CD`/`CE`) and the `q` counter (`EJ1`). Keeping these four out
is what lets the `q` loop carry the head-cell base and the drain across
iterations. -/
def ID : List Var := [CX, EE, EJ2, EJ3, EK1, EK2]

/-- The constants every family emitter reads. Preserved by all of them (none of
these registers is in `HD`). -/
def CConst (sg st : Nat) (t : State) : Prop :=
  State.get t CS1 = List.replicate (sg + 1) 1
  ∧ State.get t CS2 = List.replicate (sg + 2) 1
  ∧ State.get t CQ1 = List.replicate (st + 1) 1
  ∧ State.get t CBV = List.replicate (S1Cards.bv sg st) 1
  ∧ State.get t CZ = []

/-- Shrink a dirty list in a frame clause. `hsub` is `by decide`. -/
theorem nmem_sub {r : Var} {D D' : List Var} (hsub : ∀ x ∈ D, x ∈ D')
    (h : r ∉ D') : r ∉ D := fun hm => h (hsub r hm)

/-- Turn a dirty-list frame clause into the `≠` a per-gadget `_run` wants.
`hk` is `by decide`. -/
theorem ne_of_nmem {r : Var} {D : List Var} (h : r ∉ D) {k : Var} (hk : k ∈ D) :
    r ≠ k := fun he => h (by rw [he]; exact hk)

theorem CConst_frame {sg st : Nat} {t u : State} (h : CConst sg st t)
    (hfr : ∀ r : Var, r ≠ EOUT_C → r ∉ HD → State.get u r = State.get t r) :
    CConst sg st u := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [hfr CS1 (by decide) (by decide)]; exact h1,
    by rw [hfr CS2 (by decide) (by decide)]; exact h2,
    by rw [hfr CQ1 (by decide) (by decide)]; exact h3,
    by rw [hfr CBV (by decide) (by decide)]; exact h4,
    by rw [hfr CZ (by decide) (by decide)]; exact h5⟩

/-! ## The atoms -/

theorem encNats_nil : FlatTCCFree.encNats [] = [] := rfl

/-- **The emitter's no-op.** `copy dst dst` leaves every register's contents
unchanged, and its only write is `dst` — which every emitter frame clause
already excludes. -/
theorem copy_self_get (dst r : Var) (s : State) :
    State.get ((Cmd.op (.copy dst dst)).eval s) r = State.get s r := by
  rw [Cmd.eval_op]
  simp only [Op.eval]
  by_cases h : r = dst
  · subst h; rw [State.get_set_eq]
  · rw [State.get_set_ne _ _ _ _ h]

/-- **The two-source block atom.** Append `FlatTCCFree.encNat (v₁ + v₂)` to
`dst`, with the summands read as the lengths of `src1`/`src2`. Taking `src2` to
be the permanently empty `CZ` gives the one-source block. -/
def emitBlk2 (cnt src1 src2 dst : Var) : Cmd :=
  FrontPieces.tallyReg cnt src1 dst ;; FrontPieces.tallyReg cnt src2 dst ;;
  Cmd.op (.appendZero dst)

theorem emitBlk2_run (cnt src1 src2 dst : Var) (s : State) (v1 v2 : Nat)
    (hcd : cnt ≠ dst) (h2d : src2 ≠ dst) (h2c : src2 ≠ cnt)
    (hs1 : State.get s src1 = List.replicate v1 1)
    (hs2 : State.get s src2 = List.replicate v2 1) :
    State.get ((emitBlk2 cnt src1 src2 dst).eval s) dst
        = State.get s dst ++ FlatTCCFree.encNat (v1 + v2)
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
        State.get ((emitBlk2 cnt src1 src2 dst).eval s) r = State.get s r) := by
  obtain ⟨hD1, hF1, -⟩ := FrontPieces.tallyReg_run cnt src1 dst s hcd
  set a1 := (FrontPieces.tallyReg cnt src1 dst).eval s with ha1
  have a1D : State.get a1 dst = State.get s dst ++ List.replicate v1 1 := by
    rw [ha1, hD1, hs1, List.length_replicate]
  have a1S : State.get a1 src2 = List.replicate v2 1 := by
    rw [ha1, hF1 src2 h2d h2c]; exact hs2
  clear_value a1
  obtain ⟨hD2, hF2, -⟩ := FrontPieces.tallyReg_run cnt src2 dst a1 hcd
  set a2 := (FrontPieces.tallyReg cnt src2 dst).eval a1 with ha2
  have a2D : State.get a2 dst
      = State.get s dst ++ List.replicate v1 1 ++ List.replicate v2 1 := by
    rw [ha2, hD2, a1D, a1S, List.length_replicate]
  clear_value a2
  have hev : (emitBlk2 cnt src1 src2 dst).eval s
      = (Cmd.op (.appendZero dst)).eval a2 := by
    rw [ha2, ha1]; unfold emitBlk2; rw [Cmd.eval_seq, Cmd.eval_seq]
  refine ⟨?_, ?_⟩
  · rw [hev, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, a2D]
    simp only [FlatTCCFree.encNat, List.replicate_add, List.append_assoc]
  · intro r b1 b2
    rw [hev, Cmd.eval_op]
    simp only [Op.eval, State.get_set_ne _ _ _ _ b1]
    rw [hF2 r b1 b2]
    exact hF1 r b1 b2

/-- **The identity-card atom.** Six blocks in the shape `p₁ p₂ p₃ p₁ p₂ p₃` —
the innermost body of every copy and halt family. -/
def emitId (cnt a1 a2 b1 b2 c1 c2 dst : Var) : Cmd :=
  emitBlk2 cnt a1 a2 dst ;; emitBlk2 cnt b1 b2 dst ;; emitBlk2 cnt c1 c2 dst ;;
  emitBlk2 cnt a1 a2 dst ;; emitBlk2 cnt b1 b2 dst ;; emitBlk2 cnt c1 c2 dst

theorem emitId_run (cnt a1 a2 b1 b2 c1 c2 dst : Var) (s : State)
    (va1 va2 vb1 vb2 vc1 vc2 : Nat) (hcd : cnt ≠ dst)
    (hne : ∀ r : Var, r = a1 ∨ r = a2 ∨ r = b1 ∨ r = b2 ∨ r = c1 ∨ r = c2 →
      r ≠ dst ∧ r ≠ cnt)
    (ha1 : State.get s a1 = List.replicate va1 1)
    (ha2 : State.get s a2 = List.replicate va2 1)
    (hb1 : State.get s b1 = List.replicate vb1 1)
    (hb2 : State.get s b2 = List.replicate vb2 1)
    (hc1 : State.get s c1 = List.replicate vc1 1)
    (hc2 : State.get s c2 = List.replicate vc2 1) :
    State.get ((emitId cnt a1 a2 b1 b2 c1 c2 dst).eval s) dst
        = State.get s dst ++ FlatTCCFree.encNats
            (S1Cards.blk (va1 + va2) (vb1 + vb2) (vc1 + vc2)
              (va1 + va2) (vb1 + vb2) (vc1 + vc2))
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
        State.get ((emitId cnt a1 a2 b1 b2 c1 c2 dst).eval s) r = State.get s r) := by
  -- the six sources are all outside `{dst, cnt}`, so each survives to its read
  have pa1 := hne a1 (Or.inl rfl)
  have pa2 := hne a2 (Or.inr (Or.inl rfl))
  have pb1 := hne b1 (Or.inr (Or.inr (Or.inl rfl)))
  have pb2 := hne b2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have pc1 := hne c1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have pc2 := hne c2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  -- one step of the chain
  have step : ∀ (x1 x2 : Var) (w1 w2 : Nat) (t : State),
      x2 ≠ dst → x2 ≠ cnt →
      State.get t x1 = List.replicate w1 1 → State.get t x2 = List.replicate w2 1 →
      State.get ((emitBlk2 cnt x1 x2 dst).eval t) dst
          = State.get t dst ++ FlatTCCFree.encNat (w1 + w2)
      ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
          State.get ((emitBlk2 cnt x1 x2 dst).eval t) r = State.get t r) := by
    intro x1 x2 w1 w2 t h1 h2 e1 e2
    exact emitBlk2_run cnt x1 x2 dst t w1 w2 hcd h1 h2 e1 e2
  obtain ⟨d1, f1⟩ := step a1 a2 va1 va2 s pa2.1 pa2.2 ha1 ha2
  set s1 := (emitBlk2 cnt a1 a2 dst).eval s with hs1
  clear_value s1
  obtain ⟨d2, f2⟩ := step b1 b2 vb1 vb2 s1 pb2.1 pb2.2
    (by rw [f1 b1 pb1.1 pb1.2]; exact hb1) (by rw [f1 b2 pb2.1 pb2.2]; exact hb2)
  set s2 := (emitBlk2 cnt b1 b2 dst).eval s1 with hs2
  clear_value s2
  have g2 : ∀ r : Var, r ≠ dst → r ≠ cnt → State.get s2 r = State.get s r := by
    intro r x y; rw [f2 r x y, f1 r x y]
  obtain ⟨d3, f3⟩ := step c1 c2 vc1 vc2 s2 pc2.1 pc2.2
    (by rw [g2 c1 pc1.1 pc1.2]; exact hc1) (by rw [g2 c2 pc2.1 pc2.2]; exact hc2)
  set s3 := (emitBlk2 cnt c1 c2 dst).eval s2 with hs3
  clear_value s3
  have g3 : ∀ r : Var, r ≠ dst → r ≠ cnt → State.get s3 r = State.get s r := by
    intro r x y; rw [f3 r x y]; exact g2 r x y
  obtain ⟨d4, f4⟩ := step a1 a2 va1 va2 s3 pa2.1 pa2.2
    (by rw [g3 a1 pa1.1 pa1.2]; exact ha1) (by rw [g3 a2 pa2.1 pa2.2]; exact ha2)
  set s4 := (emitBlk2 cnt a1 a2 dst).eval s3 with hs4
  clear_value s4
  have g4 : ∀ r : Var, r ≠ dst → r ≠ cnt → State.get s4 r = State.get s r := by
    intro r x y; rw [f4 r x y]; exact g3 r x y
  obtain ⟨d5, f5⟩ := step b1 b2 vb1 vb2 s4 pb2.1 pb2.2
    (by rw [g4 b1 pb1.1 pb1.2]; exact hb1) (by rw [g4 b2 pb2.1 pb2.2]; exact hb2)
  set s5 := (emitBlk2 cnt b1 b2 dst).eval s4 with hs5
  clear_value s5
  have g5 : ∀ r : Var, r ≠ dst → r ≠ cnt → State.get s5 r = State.get s r := by
    intro r x y; rw [f5 r x y]; exact g4 r x y
  obtain ⟨d6, f6⟩ := step c1 c2 vc1 vc2 s5 pc2.1 pc2.2
    (by rw [g5 c1 pc1.1 pc1.2]; exact hc1) (by rw [g5 c2 pc2.1 pc2.2]; exact hc2)
  set s6 := (emitBlk2 cnt c1 c2 dst).eval s5 with hs6
  clear_value s6
  have hev : (emitId cnt a1 a2 b1 b2 c1 c2 dst).eval s = s6 := by
    rw [hs6, hs5, hs4, hs3, hs2, hs1]
    unfold emitId
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  refine ⟨?_, ?_⟩
  · rw [hev, d6, d5, d4, d3, d2, d1]
    show _ = _ ++ (FlatTCCFree.encNat _ ++ (FlatTCCFree.encNat _ ++
      (FlatTCCFree.encNat _ ++ (FlatTCCFree.encNat _ ++ (FlatTCCFree.encNat _ ++
        (FlatTCCFree.encNat _ ++ FlatTCCFree.encNats []))))))
    rw [encNats_nil]
    simp [List.append_assoc]
  · intro r x y; rw [hev, f6 r x y]; exact g5 r x y

/-! ## The loop principle -/

/-- **The emitter loop invariant.** A `forBnd` whose body appends
`encNats (f i)` to `dst` at iteration `i`, touching only `dst` and the registers
in `D`, appends `encNats ((List.range n).flatMap f)`.

`D` is a *list* rather than a predicate on purpose: `r ∉ D` at a concrete
register is `by decide`, and `nmem_sub (by decide)` moves a frame clause up a
level. -/
theorem emitLoop_run (cnt bnd dst : Var) (body : Cmd) (D : List Var)
    (f : Nat → List Nat) (n : Nat) (w : State)
    (hbnd : State.get w bnd = List.replicate n 1)
    (hcd : cnt ≠ dst) (hcD : cnt ∈ D)
    (hstep : ∀ (i : Nat) (t : State), State.get t cnt = List.replicate i 1 →
        (∀ r : Var, r ≠ dst → r ∉ D → State.get t r = State.get w r) →
        State.get (body.eval t) dst = State.get t dst ++ FlatTCCFree.encNats (f i)
        ∧ (∀ r : Var, r ≠ dst → r ∉ D →
            State.get (body.eval t) r = State.get t r)) :
    State.get ((Cmd.forBnd cnt bnd body).eval w) dst
        = State.get w dst ++ FlatTCCFree.encNats ((List.range n).flatMap f)
    ∧ (∀ r : Var, r ≠ dst → r ∉ D →
        State.get ((Cmd.forBnd cnt bnd body).eval w) r = State.get w r) := by
  set MI : Nat → State → Prop := fun i t =>
    State.get t dst = State.get w dst ++ FlatTCCFree.encNats ((List.range i).flatMap f)
    ∧ (∀ r : Var, r ≠ dst → r ∉ D → State.get t r = State.get w r) with hMI
  have h0 : MI 0 w := by
    refine ⟨?_, fun _ _ _ => rfl⟩
    rw [List.range_zero, List.flatMap_nil, encNats_nil, List.append_nil]
  have hstep' : ∀ i t, i < n → MI i t →
      MI (i + 1) (body.eval (t.set cnt (List.replicate i 1))) := by
    intro i t _ hM
    obtain ⟨hO, hFr⟩ := hM
    set t0 := t.set cnt (List.replicate i 1) with ht0
    have h0O : State.get t0 dst = State.get t dst := by
      rw [ht0]; exact State.get_set_ne _ _ _ _ (Ne.symm hcd)
    have h0C : State.get t0 cnt = List.replicate i 1 := by rw [ht0, State.get_set_eq]
    have h0Fr : ∀ r : Var, r ≠ dst → r ∉ D → State.get t0 r = State.get w r := by
      intro r a b
      rw [ht0, State.get_set_ne _ _ _ _ (fun h => b (by rw [h]; exact hcD))]
      exact hFr r a b
    clear_value t0
    obtain ⟨sO, sFr⟩ := hstep i t0 h0C h0Fr
    refine ⟨?_, ?_⟩
    · rw [sO, h0O, hO, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, S1Cards.encNats_append, List.append_assoc]
    · intro r a b; rw [sFr r a b]; exact h0Fr r a b
  have key := Cmd.foldlState_range_induct body cnt n w MI h0 hstep'
  rw [Cmd.eval_forBnd, hbnd, List.length_replicate]
  exact key

/-! ## `loadX` — the left-context cell

`xv sig states x` is the boundary code `bv` at `x = 0` and `x - 1` after, so it
is *not* incremental: each `x` iteration rebuilds `CX` from its own counter. -/

/-- `CX := 1^(xv sig states x)` off the loop counter `1^x`. -/
def loadX (cnt : Var) : Cmd :=
  Cmd.op (.nonEmpty EE cnt) ;;
  Cmd.ifBit EE (Cmd.op (.tail CX cnt)) (Cmd.op (.copy CX CBV))

theorem loadX_run (cnt : Var) (sg st x : Nat) (s : State)
    (hcE : cnt ≠ EE)
    (hc : State.get s cnt = List.replicate x 1)
    (hbv : State.get s CBV = List.replicate (S1Cards.bv sg st) 1) :
    State.get ((loadX cnt).eval s) CX = List.replicate (S1Cards.xv sg st x) 1
    ∧ (∀ r : Var, r ≠ CX → r ≠ EE →
        State.get ((loadX cnt).eval s) r = State.get s r) := by
  set t := (Cmd.op (.nonEmpty EE cnt)).eval s with ht
  have tE : State.get t EE = if (List.replicate x 1 : List Nat).isEmpty then [0] else [1] := by
    rw [ht, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, hc]
  have tFr : ∀ r : Var, r ≠ EE → State.get t r = State.get s r := by
    intro r hr; rw [ht, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value t
  have hev : (loadX cnt).eval s
      = (Cmd.ifBit EE (Cmd.op (.tail CX cnt)) (Cmd.op (.copy CX CBV))).eval t := by
    rw [ht]; unfold loadX; rw [Cmd.eval_seq]
  cases x with
  | zero =>
      have hfalse : State.get t EE ≠ [1] := by rw [tE]; decide
      have hb : State.get t CBV = List.replicate (S1Cards.bv sg st) 1 := by
        rw [tFr CBV (by decide)]; exact hbv
      refine ⟨?_, ?_⟩
      · rw [hev, Cmd.eval_ifBit_false _ _ _ _ hfalse, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq, hb, S1Cards.xv_zero]
      · intro r b1 b2
        rw [hev, Cmd.eval_ifBit_false _ _ _ _ hfalse, Cmd.eval_op]
        simp only [Op.eval, State.get_set_ne _ _ _ _ b1]
        exact tFr r b2
  | succ k =>
      have htrue : State.get t EE = [1] := by rw [tE]; rfl
      have hcv : State.get t cnt = List.replicate (k + 1) 1 := by
        rw [tFr cnt hcE]; exact hc
      refine ⟨?_, ?_⟩
      · rw [hev, Cmd.eval_ifBit_true _ _ _ _ htrue, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq, hcv, S1Cards.xv_succ]
        rw [List.replicate_succ, List.tail_cons]
      · intro r b1 b2
        rw [hev, Cmd.eval_ifBit_true _ _ _ _ htrue, Cmd.eval_op]
        simp only [Op.eval, State.get_set_ne _ _ _ _ b1]
        exact tFr r b2

/-! ## Family 1 — `copyCards` (the identity away from the head)

Three plain loops: `x` over `xOpts` (`sig+2` entries), then `b` and `c` over the
tape alphabet. No gating. -/

/-- The innermost body: the identity card `(X, b, c) → (X, b, c)`. -/
def copyInner : Cmd := emitId EK1 CX CZ EJ2 CZ EJ3 CZ EOUT_C

/-- The `c` loop. -/
def copyLoopC : Cmd := Cmd.forBnd EJ3 CS1 copyInner
/-- The `b` loop. -/
def copyLoopB : Cmd := Cmd.forBnd EJ2 CS1 copyLoopC
/-- One `x` iteration: rebuild the left-context cell, then the two inner loops. -/
def copyBodyX : Cmd := loadX EJ1 ;; copyLoopB

/-- **Family 1.** `EOUT_C ++= encNats (copyBlocks sig states)`. -/
def cCopy : Cmd := Cmd.forBnd EJ1 CS2 copyBodyX

private theorem copyLoopC_run (sg X b : Nat) (w : State)
    (hS1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hX : State.get w CX = List.replicate X 1)
    (hb : State.get w EJ2 = List.replicate b 1)
    (hZ : State.get w CZ = []) :
    State.get (copyLoopC.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun c => S1Cards.blk X b c X b c))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ3, EK1] →
        State.get (copyLoopC.eval w) r = State.get w r) := by
  unfold copyLoopC
  refine emitLoop_run EJ3 CS1 EOUT_C copyInner [EJ3, EK1] _ (sg + 1) w hS1
    (by decide) (by decide) (fun i t hcnt hfr => ?_)
  unfold copyInner
  have tX : State.get t CX = List.replicate X 1 := by
    rw [hfr CX (by decide) (by decide)]; exact hX
  have tb : State.get t EJ2 = List.replicate b 1 := by
    rw [hfr EJ2 (by decide) (by decide)]; exact hb
  have tZ : State.get t CZ = List.replicate 0 1 := by
    rw [hfr CZ (by decide) (by decide)]; exact hZ
  obtain ⟨hO, hF⟩ := emitId_run EK1 CX CZ EJ2 CZ EJ3 CZ EOUT_C t X 0 b 0 i 0
    (by decide) (by rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide, by decide⟩)
    tX tZ tb tZ hcnt tZ
  refine ⟨?_, fun r a1 a2 => hF r a1 (ne_of_nmem a2 (by decide))⟩
  rw [hO]
  simp

private theorem copyLoopB_run (sg X : Nat) (w : State)
    (hS1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hX : State.get w CX = List.replicate X 1)
    (hZ : State.get w CZ = []) :
    State.get (copyLoopB.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun b =>
              (List.range (sg + 1)).flatMap (fun c => S1Cards.blk X b c X b c)))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ2, EJ3, EK1] →
        State.get (copyLoopB.eval w) r = State.get w r) := by
  unfold copyLoopB
  refine emitLoop_run EJ2 CS1 EOUT_C copyLoopC [EJ2, EJ3, EK1] _ (sg + 1) w hS1
    (by decide) (by decide) (fun i t hcnt hfr => ?_)
  obtain ⟨hO, hF⟩ := copyLoopC_run sg X i t
    (by rw [hfr CS1 (by decide) (by decide)]; exact hS1)
    (by rw [hfr CX (by decide) (by decide)]; exact hX) hcnt
    (by rw [hfr CZ (by decide) (by decide)]; exact hZ)
  exact ⟨hO, fun r a1 a2 => hF r a1 (nmem_sub (by decide) a2)⟩

/-- **Family 1 is correct.** -/
theorem cCopy_run (sg st : Nat) (w : State) (hc : CConst sg st w) :
    State.get (cCopy.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats (S1Cards.copyBlocks sg st)
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ HD →
        State.get (cCopy.eval w) r = State.get w r) := by
  obtain ⟨hS1, hS2, -, hBV, hZ⟩ := hc
  have key : State.get (cCopy.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 2)).flatMap (fun x =>
              (List.range (sg + 1)).flatMap (fun b =>
                (List.range (sg + 1)).flatMap (fun c =>
                  S1Cards.blk (S1Cards.xv sg st x) b c (S1Cards.xv sg st x) b c))))
      ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ1, EJ2, EJ3, EK1, CX, EE] →
          State.get (cCopy.eval w) r = State.get w r) := by
    unfold cCopy
    refine emitLoop_run EJ1 CS2 EOUT_C copyBodyX [EJ1, EJ2, EJ3, EK1, CX, EE] _
      (sg + 2) w hS2 (by decide) (by decide) (fun i t hcnt hfr => ?_)
    obtain ⟨lX, lF⟩ := loadX_run EJ1 sg st i t (by decide) hcnt
      (by rw [hfr CBV (by decide) (by decide)]; exact hBV)
    set t1 := (loadX EJ1).eval t with ht1
    clear_value t1
    obtain ⟨hO, hF⟩ := copyLoopB_run sg (S1Cards.xv sg st i) t1
      (by rw [lF CS1 (by decide) (by decide), hfr CS1 (by decide) (by decide)]; exact hS1)
      lX (by rw [lF CZ (by decide) (by decide), hfr CZ (by decide) (by decide)]; exact hZ)
    have hev : copyBodyX.eval t = copyLoopB.eval t1 := by
      rw [ht1]; unfold copyBodyX; rw [Cmd.eval_seq]
    refine ⟨by rw [hev, hO, lF EOUT_C (by decide) (by decide)], fun r a1 a2 => ?_⟩
    have hrX : r ≠ CX := fun h => a2 (by rw [h]; decide)
    have hrE : r ≠ EE := fun h => a2 (by rw [h]; decide)
    rw [hev, hF r a1 (nmem_sub (by decide) a2)]
    exact lF r hrX hrE
  exact ⟨key.1, fun r a1 a2 => key.2 r a1 (nmem_sub (by decide) a2)⟩

/-! ## Family 2 — `copyRightCards` (the identity at the right boundary marker)

Two loops; the third premise cell is the constant boundary code, read straight
off `CBV`. -/

/-- The innermost body: the identity card `(y, z, bv) → (y, z, bv)`. -/
def rightInner : Cmd := emitId EK1 EJ1 CZ EJ2 CZ CBV CZ EOUT_C

/-- The `z` loop. -/
def rightLoopZ : Cmd := Cmd.forBnd EJ2 CS1 rightInner

/-- **Family 2.** `EOUT_C ++= encNats (copyRightBlocks sig states)`. -/
def cRight : Cmd := Cmd.forBnd EJ1 CS1 rightLoopZ

private theorem rightLoopZ_run (sg st y : Nat) (w : State)
    (hS1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hBV : State.get w CBV = List.replicate (S1Cards.bv sg st) 1)
    (hy : State.get w EJ1 = List.replicate y 1)
    (hZ : State.get w CZ = []) :
    State.get (rightLoopZ.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun z =>
              S1Cards.blk y z (S1Cards.bv sg st) y z (S1Cards.bv sg st)))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ2, EK1] →
        State.get (rightLoopZ.eval w) r = State.get w r) := by
  unfold rightLoopZ
  refine emitLoop_run EJ2 CS1 EOUT_C rightInner [EJ2, EK1] _ (sg + 1) w hS1
    (by decide) (by decide) (fun i t hcnt hfr => ?_)
  unfold rightInner
  have tY : State.get t EJ1 = List.replicate y 1 := by
    rw [hfr EJ1 (by decide) (by decide)]; exact hy
  have tB : State.get t CBV = List.replicate (S1Cards.bv sg st) 1 := by
    rw [hfr CBV (by decide) (by decide)]; exact hBV
  have tZ : State.get t CZ = List.replicate 0 1 := by
    rw [hfr CZ (by decide) (by decide)]; exact hZ
  obtain ⟨hO, hF⟩ := emitId_run EK1 EJ1 CZ EJ2 CZ CBV CZ EOUT_C t y 0 i 0
    (S1Cards.bv sg st) 0
    (by decide) (by rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide, by decide⟩)
    tY tZ hcnt tZ tB tZ
  refine ⟨?_, fun r a1 a2 => hF r a1 (ne_of_nmem a2 (by decide))⟩
  rw [hO]
  simp

/-- **Family 2 is correct.** -/
theorem cRight_run (sg st : Nat) (w : State) (hc : CConst sg st w) :
    State.get (cRight.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats (S1Cards.copyRightBlocks sg st)
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ HD →
        State.get (cRight.eval w) r = State.get w r) := by
  obtain ⟨hS1, -, -, hBV, hZ⟩ := hc
  have key : State.get (cRight.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun y =>
              (List.range (sg + 1)).flatMap (fun z =>
                S1Cards.blk y z (S1Cards.bv sg st) y z (S1Cards.bv sg st))))
      ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ1, EJ2, EK1] →
          State.get (cRight.eval w) r = State.get w r) := by
    unfold cRight
    refine emitLoop_run EJ1 CS1 EOUT_C rightLoopZ [EJ1, EJ2, EK1] _ (sg + 1) w hS1
      (by decide) (by decide) (fun i t hcnt hfr => ?_)
    obtain ⟨hO, hF⟩ := rightLoopZ_run sg st i t
      (by rw [hfr CS1 (by decide) (by decide)]; exact hS1)
      (by rw [hfr CBV (by decide) (by decide)]; exact hBV) hcnt
      (by rw [hfr CZ (by decide) (by decide)]; exact hZ)
    exact ⟨hO, fun r a1 a2 => hF r a1 (nmem_sub (by decide) a2)⟩
  exact ⟨key.1, fun r a1 a2 => key.2 r a1 (nmem_sub (by decide) a2)⟩

/-! ## The halt families' shared `q` loop

Identical in shape to `S1Emit.stageFin`: `CD` drains `S1Parse.PHALT` one `head`
cell per `q`, the gate is one `ifBit`, and the head-cell base `CH` advances by
`1^(sig+1)` per iteration. A drained-empty `head` reads as *false*, which is
exactly `M.halt.getD` out of range — so no `|halt| = states` hypothesis. -/

private theorem drop_cons {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    l.drop i = (l[i]'hi) :: l.drop (i + 1) := List.drop_eq_getElem_cons hi

private theorem tail_drop {α : Type} (l : List α) (i : Nat) :
    (l.drop i).tail = l.drop (i + 1) := by
  rw [← List.drop_one, List.drop_drop, Nat.add_comm]

private theorem getD_ge {α : Type} (l : List α) (i : Nat) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- One `q` iteration of a halt family. -/
def haltBody (inner : Cmd) : Cmd :=
  Cmd.op (.head CE CD) ;; Cmd.op (.tail CD CD) ;;
  Cmd.ifBit CE inner (Cmd.op (.copy EOUT_C EOUT_C)) ;;
  FrontPieces.tallyReg EK1 CS1 CH

/-- A whole halt family: (re)load the drain and the head-cell base, then the
`q` loop. -/
def haltFam (inner : Cmd) : Cmd :=
  Cmd.op (.copy CD S1Parse.PHALT) ;; Cmd.op (.copy CH CS1) ;;
  Cmd.forBnd EJ1 CQ1 (haltBody inner)

private theorem haltLoop_run (inner : Cmd) (F : Nat → List Nat) (sg st : Nat)
    (hb : List Nat) (u : State)
    (hconst : CConst sg st u)
    (hCH : State.get u CH = List.replicate (sg + 1) 1)
    (hCD : State.get u CD = hb)
    (hinner : ∀ (q : Nat) (t : State), CConst sg st t →
        State.get t CH = List.replicate ((sg + 1) * (q + 1)) 1 →
        State.get (inner.eval t) EOUT_C
            = State.get t EOUT_C ++ FlatTCCFree.encNats (F q)
        ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ ID →
            State.get (inner.eval t) r = State.get t r)) :
    State.get ((Cmd.forBnd EJ1 CQ1 (haltBody inner)).eval u) EOUT_C
        = State.get u EOUT_C ++ FlatTCCFree.encNats
            ((List.range (st + 1)).flatMap
              (fun q => if S1Cards.haltBit hb q then F q else []))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ HD →
        State.get ((Cmd.forBnd EJ1 CQ1 (haltBody inner)).eval u) r = State.get u r) := by
  have cS1 : State.get u CS1 = List.replicate (sg + 1) 1 := hconst.1
  have cQ1 : State.get u CQ1 = List.replicate (st + 1) 1 := hconst.2.2.1
  set g : Nat → List Nat := fun q => if S1Cards.haltBit hb q then F q else [] with hg
  set MO : Nat → State → Prop := fun i t =>
    State.get t EOUT_C
        = State.get u EOUT_C ++ FlatTCCFree.encNats ((List.range i).flatMap g)
    ∧ State.get t CH = List.replicate ((sg + 1) * (i + 1)) 1
    ∧ State.get t CD = hb.drop i
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ HD → State.get t r = State.get u r) with hMO
  have h0 : MO 0 u := by
    refine ⟨?_, by rw [hCH, Nat.mul_one], by rw [hCD, List.drop_zero], fun _ _ _ => rfl⟩
    rw [List.range_zero, List.flatMap_nil, encNats_nil, List.append_nil]
  have hstep : ∀ i t, i < (State.get u CQ1).length → MO i t →
      MO (i + 1) ((haltBody inner).eval (t.set EJ1 (List.replicate i 1))) := by
    intro i t _ hM
    obtain ⟨pO, pH, pD, pFr⟩ := hM
    set t0 := t.set EJ1 (List.replicate i 1) with ht0
    have q0O : State.get t0 EOUT_C
        = State.get u EOUT_C ++ FlatTCCFree.encNats ((List.range i).flatMap g) := by
      rw [ht0, State.get_set_ne _ _ _ _ (by decide : (EOUT_C : Var) ≠ EJ1)]; exact pO
    have q0H : State.get t0 CH = List.replicate ((sg + 1) * (i + 1)) 1 := by
      rw [ht0, State.get_set_ne _ _ _ _ (by decide : (CH : Var) ≠ EJ1)]; exact pH
    have q0D : State.get t0 CD = hb.drop i := by
      rw [ht0, State.get_set_ne _ _ _ _ (by decide : (CD : Var) ≠ EJ1)]; exact pD
    have q0Fr : ∀ r : Var, r ≠ EOUT_C → r ∉ HD → State.get t0 r = State.get u r := by
      intro r a1 a2
      rw [ht0, State.get_set_ne _ _ _ _ (ne_of_nmem a2 (by decide))]
      exact pFr r a1 a2
    clear_value t0
    -- pop the halt bit
    set v1 := (Cmd.op (.head CE CD)).eval t0 with hv1
    have v1E : State.get v1 CE = (match hb.drop i with | [] => [] | x :: _ => [x]) := by
      rw [hv1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, q0D]; rfl
    have v1Fr : ∀ r : Var, r ≠ CE → State.get v1 r = State.get t0 r := by
      intro r hr; rw [hv1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
    clear_value v1
    set v2 := (Cmd.op (.tail CD CD)).eval v1 with hv2
    have v2D : State.get v2 CD = (hb.drop i).tail := by
      rw [hv2, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, v1Fr CD (by decide), q0D]
    have v2Fr : ∀ r : Var, r ≠ CD → State.get v2 r = State.get v1 r := by
      intro r hr; rw [hv2, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
    clear_value v2
    have v2E : State.get v2 CE = (match hb.drop i with | [] => [] | x :: _ => [x]) := by
      rw [v2Fr CE (by decide)]; exact v1E
    have v2O : State.get v2 EOUT_C
        = State.get u EOUT_C ++ FlatTCCFree.encNats ((List.range i).flatMap g) := by
      rw [v2Fr EOUT_C (by decide), v1Fr EOUT_C (by decide)]; exact q0O
    have v2H : State.get v2 CH = List.replicate ((sg + 1) * (i + 1)) 1 := by
      rw [v2Fr CH (by decide), v1Fr CH (by decide)]; exact q0H
    have v2G : ∀ r : Var, r ≠ EOUT_C → r ∉ HD → State.get v2 r = State.get u r := by
      intro r a1 a2
      rw [v2Fr r (ne_of_nmem a2 (by decide)), v1Fr r (ne_of_nmem a2 (by decide))]
      exact q0Fr r a1 a2
    have v2C : CConst sg st v2 := CConst_frame hconst (fun r a1 a2 => v2G r a1 a2)
    -- the gate
    set v3 := (Cmd.ifBit CE inner (Cmd.op (.copy EOUT_C EOUT_C))).eval v2 with hv3
    have hgate : State.get v3 EOUT_C
          = State.get u EOUT_C ++ FlatTCCFree.encNats ((List.range i).flatMap g ++ g i)
        ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ ID → State.get v3 r = State.get v2 r) := by
      by_cases hi : i < hb.length
      · rw [drop_cons hb i hi] at v2E
        by_cases hx : hb[i]'hi = 1
        · have hgi : g i = F i := by
            rw [hg]
            simp only []
            rw [if_pos (show S1Cards.haltBit hb i = true by
              unfold S1Cards.haltBit; rw [List.getD_eq_getElem _ _ hi, hx]; rfl)]
          have htest : State.get v2 CE = [1] := by rw [v2E, hx]
          obtain ⟨iO, iF⟩ := hinner i v2 v2C v2H
          refine ⟨?_, ?_⟩
          · rw [hv3, Cmd.eval_ifBit_true _ _ _ _ htest, iO, v2O, hgi,
              S1Cards.encNats_append, List.append_assoc]
          · intro r a1 a2
            rw [hv3, Cmd.eval_ifBit_true _ _ _ _ htest]; exact iF r a1 a2
        · have hgi : g i = [] := by
            rw [hg]
            simp only []
            rw [if_neg (show ¬ (S1Cards.haltBit hb i = true) by
              unfold S1Cards.haltBit; rw [List.getD_eq_getElem _ _ hi]; simpa using hx)]
          have htest : State.get v2 CE ≠ [1] := by rw [v2E]; simpa using hx
          refine ⟨?_, ?_⟩
          · rw [hv3, Cmd.eval_ifBit_false _ _ _ _ htest, copy_self_get, v2O, hgi,
              List.append_nil]
          · intro r a1 _
            rw [hv3, Cmd.eval_ifBit_false _ _ _ _ htest, copy_self_get]
      · have hd : hb.drop i = [] := List.drop_eq_nil_of_le (Nat.le_of_not_lt hi)
        rw [hd] at v2E
        have hgi : g i = [] := by
          rw [hg]
          simp only []
          rw [if_neg (show ¬ (S1Cards.haltBit hb i = true) by
            unfold S1Cards.haltBit
            rw [getD_ge _ _ _ (Nat.le_of_not_lt hi)]; decide)]
        have htest : State.get v2 CE ≠ [1] := by rw [v2E]; decide
        refine ⟨?_, ?_⟩
        · rw [hv3, Cmd.eval_ifBit_false _ _ _ _ htest, copy_self_get, v2O, hgi,
            List.append_nil]
        · intro r a1 _
          rw [hv3, Cmd.eval_ifBit_false _ _ _ _ htest, copy_self_get]
    obtain ⟨v3O, v3Fr⟩ := hgate
    clear_value v3
    have v3H : State.get v3 CH = List.replicate ((sg + 1) * (i + 1)) 1 := by
      rw [v3Fr CH (by decide) (by decide)]; exact v2H
    have v3S : State.get v3 CS1 = List.replicate (sg + 1) 1 := by
      rw [v3Fr CS1 (by decide) (by decide)]; exact v2C.1
    have v3D : State.get v3 CD = hb.drop (i + 1) := by
      rw [v3Fr CD (by decide) (by decide), v2D, tail_drop]
    -- advance the head-cell base
    obtain ⟨tO, tF, -⟩ := FrontPieces.tallyReg_run EK1 CS1 CH v3 (by decide)
    have hev : (haltBody inner).eval t0 = (FrontPieces.tallyReg EK1 CS1 CH).eval v3 := by
      rw [hv3, hv2, hv1]; unfold haltBody
      rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hev, tF EOUT_C (by decide) (by decide), v3O, List.range_succ,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · have harith : (sg + 1) * (i + 1) + (sg + 1) = (sg + 1) * (i + 1 + 1) := by ring
      rw [hev, tO, v3H, v3S, List.length_replicate, ← List.replicate_add, harith]
    · rw [hev, tF CD (by decide) (by decide)]; exact v3D
    · intro r a1 a2
      rw [hev, tF r (ne_of_nmem a2 (by decide)) (ne_of_nmem a2 (by decide)),
        v3Fr r a1 (nmem_sub (by decide) a2)]
      exact v2G r a1 a2
  have key := Cmd.foldlState_range_induct (haltBody inner) EJ1
    (State.get u CQ1).length u MO h0 hstep
  rw [cQ1, List.length_replicate] at key
  obtain ⟨kO, -, -, kFr⟩ := key
  rw [Cmd.eval_forBnd, cQ1, List.length_replicate]
  exact ⟨kO, kFr⟩

/-- **The halt-family wrapper is correct.** -/
theorem haltFam_run (inner : Cmd) (F : Nat → List Nat) (sg st : Nat)
    (hb : List Nat) (s : State)
    (hconst : CConst sg st s)
    (hph : State.get s S1Parse.PHALT = hb)
    (hinner : ∀ (q : Nat) (t : State), CConst sg st t →
        State.get t CH = List.replicate ((sg + 1) * (q + 1)) 1 →
        State.get (inner.eval t) EOUT_C
            = State.get t EOUT_C ++ FlatTCCFree.encNats (F q)
        ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ ID →
            State.get (inner.eval t) r = State.get t r)) :
    State.get ((haltFam inner).eval s) EOUT_C
        = State.get s EOUT_C ++ FlatTCCFree.encNats
            ((List.range (st + 1)).flatMap
              (fun q => if S1Cards.haltBit hb q then F q else []))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ HD →
        State.get ((haltFam inner).eval s) r = State.get s r) := by
  set u1 := (Cmd.op (.copy CD S1Parse.PHALT)).eval s with hu1
  have u1D : State.get u1 CD = hb := by
    rw [hu1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; exact hph
  have u1Fr : ∀ r : Var, r ≠ CD → State.get u1 r = State.get s r := by
    intro r hr; rw [hu1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u1
  set u2 := (Cmd.op (.copy CH CS1)).eval u1 with hu2
  have u2H : State.get u2 CH = List.replicate (sg + 1) 1 := by
    rw [hu2, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, u1Fr CS1 (by decide)]
    exact hconst.1
  have u2Fr : ∀ r : Var, r ≠ CH → State.get u2 r = State.get u1 r := by
    intro r hr; rw [hu2, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u2
  have u2D : State.get u2 CD = hb := by rw [u2Fr CD (by decide)]; exact u1D
  have u2G : ∀ r : Var, r ≠ CD → r ≠ CH → State.get u2 r = State.get s r := by
    intro r a b; rw [u2Fr r b, u1Fr r a]
  have u2C : CConst sg st u2 :=
    CConst_frame hconst (fun r _ a2 =>
      u2G r (ne_of_nmem a2 (by decide)) (ne_of_nmem a2 (by decide)))
  obtain ⟨kO, kFr⟩ := haltLoop_run inner F sg st hb u2 u2C u2H u2D hinner
  have hev : (haltFam inner).eval s = (Cmd.forBnd EJ1 CQ1 (haltBody inner)).eval u2 := by
    rw [hu2, hu1]; unfold haltFam; rw [Cmd.eval_seq, Cmd.eval_seq]
  refine ⟨?_, fun r a1 a2 => ?_⟩
  · rw [hev, kO, u2G EOUT_C (by decide) (by decide)]
  · rw [hev, kFr r a1 a2]
    exact u2G r (ne_of_nmem a2 (by decide)) (ne_of_nmem a2 (by decide))

/-! ## Family 3 — `haltLeftCards` (head at the window's first cell)

Three inner loops (`b`, `y`, `z`) under the gate; the head-cell code is
`CH + EJ2`, i.e. the incrementally maintained base plus the `b` loop's own
counter (HANDOFF finding 3 — no multiplication inside any loop). -/

def hLeftInner : Cmd := emitId EK1 CH EJ2 EJ3 CZ EK2 CZ EOUT_C
def hLeftLoopZ : Cmd := Cmd.forBnd EK2 CS1 hLeftInner
def hLeftLoopY : Cmd := Cmd.forBnd EJ3 CS1 hLeftLoopZ
def hLeftNest  : Cmd := Cmd.forBnd EJ2 CS1 hLeftLoopY

/-- **Family 3.** -/
def cHaltLeft : Cmd := haltFam hLeftNest

private theorem hLeftLoopZ_run (sg q b y : Nat) (w : State)
    (hS1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hH : State.get w CH = List.replicate ((sg + 1) * (q + 1)) 1)
    (hb : State.get w EJ2 = List.replicate b 1)
    (hy : State.get w EJ3 = List.replicate y 1)
    (hZ : State.get w CZ = []) :
    State.get (hLeftLoopZ.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun z =>
              S1Cards.blk (S1Cards.hv sg q b) y z (S1Cards.hv sg q b) y z))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EK2, EK1] →
        State.get (hLeftLoopZ.eval w) r = State.get w r) := by
  unfold hLeftLoopZ
  refine emitLoop_run EK2 CS1 EOUT_C hLeftInner [EK2, EK1] _ (sg + 1) w hS1
    (by decide) (by decide) (fun i t hcnt hfr => ?_)
  unfold hLeftInner
  have tH : State.get t CH = List.replicate ((sg + 1) * (q + 1)) 1 := by
    rw [hfr CH (by decide) (by decide)]; exact hH
  have tb : State.get t EJ2 = List.replicate b 1 := by
    rw [hfr EJ2 (by decide) (by decide)]; exact hb
  have ty : State.get t EJ3 = List.replicate y 1 := by
    rw [hfr EJ3 (by decide) (by decide)]; exact hy
  have tZ : State.get t CZ = List.replicate 0 1 := by
    rw [hfr CZ (by decide) (by decide)]; exact hZ
  obtain ⟨hO, hF⟩ := emitId_run EK1 CH EJ2 EJ3 CZ EK2 CZ EOUT_C t
    ((sg + 1) * (q + 1)) b y 0 i 0
    (by decide) (by rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide, by decide⟩)
    tH tb ty tZ hcnt tZ
  refine ⟨?_, fun r a1 a2 => hF r a1 (ne_of_nmem a2 (by decide))⟩
  rw [hO]
  simp [S1Cards.hv]

private theorem hLeftLoopY_run (sg q b : Nat) (w : State)
    (hS1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hH : State.get w CH = List.replicate ((sg + 1) * (q + 1)) 1)
    (hb : State.get w EJ2 = List.replicate b 1)
    (hZ : State.get w CZ = []) :
    State.get (hLeftLoopY.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun y =>
              (List.range (sg + 1)).flatMap (fun z =>
                S1Cards.blk (S1Cards.hv sg q b) y z (S1Cards.hv sg q b) y z)))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ3, EK2, EK1] →
        State.get (hLeftLoopY.eval w) r = State.get w r) := by
  unfold hLeftLoopY
  refine emitLoop_run EJ3 CS1 EOUT_C hLeftLoopZ [EJ3, EK2, EK1] _ (sg + 1) w hS1
    (by decide) (by decide) (fun i t hcnt hfr => ?_)
  obtain ⟨hO, hF⟩ := hLeftLoopZ_run sg q b i t
    (by rw [hfr CS1 (by decide) (by decide)]; exact hS1)
    (by rw [hfr CH (by decide) (by decide)]; exact hH)
    (by rw [hfr EJ2 (by decide) (by decide)]; exact hb) hcnt
    (by rw [hfr CZ (by decide) (by decide)]; exact hZ)
  exact ⟨hO, fun r a1 a2 => hF r a1 (nmem_sub (by decide) a2)⟩

private theorem hLeftNest_run (sg q : Nat) (w : State)
    (hS1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hH : State.get w CH = List.replicate ((sg + 1) * (q + 1)) 1)
    (hZ : State.get w CZ = []) :
    State.get (hLeftNest.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun b =>
              (List.range (sg + 1)).flatMap (fun y =>
                (List.range (sg + 1)).flatMap (fun z =>
                  S1Cards.blk (S1Cards.hv sg q b) y z (S1Cards.hv sg q b) y z))))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ ID →
        State.get (hLeftNest.eval w) r = State.get w r) := by
  unfold hLeftNest
  have key : State.get ((Cmd.forBnd EJ2 CS1 hLeftLoopY).eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun b =>
              (List.range (sg + 1)).flatMap (fun y =>
                (List.range (sg + 1)).flatMap (fun z =>
                  S1Cards.blk (S1Cards.hv sg q b) y z (S1Cards.hv sg q b) y z))))
      ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ2, EJ3, EK2, EK1] →
          State.get ((Cmd.forBnd EJ2 CS1 hLeftLoopY).eval w) r = State.get w r) := by
    refine emitLoop_run EJ2 CS1 EOUT_C hLeftLoopY [EJ2, EJ3, EK2, EK1] _ (sg + 1) w hS1
      (by decide) (by decide) (fun i t hcnt hfr => ?_)
    obtain ⟨hO, hF⟩ := hLeftLoopY_run sg q i t
      (by rw [hfr CS1 (by decide) (by decide)]; exact hS1)
      (by rw [hfr CH (by decide) (by decide)]; exact hH) hcnt
      (by rw [hfr CZ (by decide) (by decide)]; exact hZ)
    exact ⟨hO, fun r a1 a2 => hF r a1 (nmem_sub (by decide) a2)⟩
  exact ⟨key.1, fun r a1 a2 => key.2 r a1 (nmem_sub (by decide) a2)⟩

/-- **Family 3 is correct.** -/
theorem cHaltLeft_run (sg st : Nat) (hb : List Nat) (s : State)
    (hconst : CConst sg st s) (hph : State.get s S1Parse.PHALT = hb) :
    State.get (cHaltLeft.eval s) EOUT_C
        = State.get s EOUT_C ++ FlatTCCFree.encNats (S1Cards.haltLeftBlocks sg st hb)
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ HD →
        State.get (cHaltLeft.eval s) r = State.get s r) :=
  haltFam_run hLeftNest _ sg st hb s hconst hph
    (fun q t hc hH => hLeftNest_run sg q t hc.1 hH hc.2.2.2.2)

/-! ## Families 4 and 5 — `haltCenterCards` / `haltRightCards`

Same gate, same three inner loops, but the `x` level runs over `xOpts`
(`sig + 2` entries) and rebuilds `CX` per iteration. -/

def hCenterInner : Cmd := emitId EK1 CX CZ CH EJ2 EK2 CZ EOUT_C
def hCenterLoopZ : Cmd := Cmd.forBnd EK2 CS1 hCenterInner
def hCenterBodyX : Cmd := loadX EJ3 ;; hCenterLoopZ
def hCenterLoopX : Cmd := Cmd.forBnd EJ3 CS2 hCenterBodyX
def hCenterNest  : Cmd := Cmd.forBnd EJ2 CS1 hCenterLoopX

/-- **Family 4.** -/
def cHaltCenter : Cmd := haltFam hCenterNest

private theorem hCenterLoopZ_run (sg q b X : Nat) (w : State)
    (hS1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hH : State.get w CH = List.replicate ((sg + 1) * (q + 1)) 1)
    (hbb : State.get w EJ2 = List.replicate b 1)
    (hX : State.get w CX = List.replicate X 1)
    (hZ : State.get w CZ = []) :
    State.get (hCenterLoopZ.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun z =>
              S1Cards.blk X (S1Cards.hv sg q b) z X (S1Cards.hv sg q b) z))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EK2, EK1] →
        State.get (hCenterLoopZ.eval w) r = State.get w r) := by
  unfold hCenterLoopZ
  refine emitLoop_run EK2 CS1 EOUT_C hCenterInner [EK2, EK1] _ (sg + 1) w hS1
    (by decide) (by decide) (fun i t hcnt hfr => ?_)
  unfold hCenterInner
  have tX : State.get t CX = List.replicate X 1 := by
    rw [hfr CX (by decide) (by decide)]; exact hX
  have tH : State.get t CH = List.replicate ((sg + 1) * (q + 1)) 1 := by
    rw [hfr CH (by decide) (by decide)]; exact hH
  have tb : State.get t EJ2 = List.replicate b 1 := by
    rw [hfr EJ2 (by decide) (by decide)]; exact hbb
  have tZ : State.get t CZ = List.replicate 0 1 := by
    rw [hfr CZ (by decide) (by decide)]; exact hZ
  obtain ⟨hO, hF⟩ := emitId_run EK1 CX CZ CH EJ2 EK2 CZ EOUT_C t
    X 0 ((sg + 1) * (q + 1)) b i 0
    (by decide) (by rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide, by decide⟩)
    tX tZ tH tb hcnt tZ
  refine ⟨?_, fun r a1 a2 => hF r a1 (ne_of_nmem a2 (by decide))⟩
  rw [hO]
  simp [S1Cards.hv]

private theorem hCenterLoopX_run (sg st q b : Nat) (w : State)
    (hS1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hS2 : State.get w CS2 = List.replicate (sg + 2) 1)
    (hBV : State.get w CBV = List.replicate (S1Cards.bv sg st) 1)
    (hH : State.get w CH = List.replicate ((sg + 1) * (q + 1)) 1)
    (hbb : State.get w EJ2 = List.replicate b 1)
    (hZ : State.get w CZ = []) :
    State.get (hCenterLoopX.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 2)).flatMap (fun x =>
              (List.range (sg + 1)).flatMap (fun z =>
                S1Cards.blk (S1Cards.xv sg st x) (S1Cards.hv sg q b) z
                  (S1Cards.xv sg st x) (S1Cards.hv sg q b) z)))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ3, EK2, EK1, CX, EE] →
        State.get (hCenterLoopX.eval w) r = State.get w r) := by
  unfold hCenterLoopX
  refine emitLoop_run EJ3 CS2 EOUT_C hCenterBodyX [EJ3, EK2, EK1, CX, EE] _
    (sg + 2) w hS2 (by decide) (by decide) (fun i t hcnt hfr => ?_)
  obtain ⟨lX, lF⟩ := loadX_run EJ3 sg st i t (by decide) hcnt
    (by rw [hfr CBV (by decide) (by decide)]; exact hBV)
  set t1 := (loadX EJ3).eval t with ht1
  clear_value t1
  obtain ⟨hO, hF⟩ := hCenterLoopZ_run sg q b (S1Cards.xv sg st i) t1
    (by rw [lF CS1 (by decide) (by decide), hfr CS1 (by decide) (by decide)]; exact hS1)
    (by rw [lF CH (by decide) (by decide), hfr CH (by decide) (by decide)]; exact hH)
    (by rw [lF EJ2 (by decide) (by decide), hfr EJ2 (by decide) (by decide)]; exact hbb)
    lX (by rw [lF CZ (by decide) (by decide), hfr CZ (by decide) (by decide)]; exact hZ)
  have hev : hCenterBodyX.eval t = hCenterLoopZ.eval t1 := by
    rw [ht1]; unfold hCenterBodyX; rw [Cmd.eval_seq]
  refine ⟨by rw [hev, hO, lF EOUT_C (by decide) (by decide)], fun r a1 a2 => ?_⟩
  have hrX : r ≠ CX := fun h => a2 (by rw [h]; decide)
  have hrE : r ≠ EE := fun h => a2 (by rw [h]; decide)
  rw [hev, hF r a1 (nmem_sub (by decide) a2)]
  exact lF r hrX hrE

private theorem hCenterNest_run (sg st q : Nat) (w : State)
    (hconst : CConst sg st w)
    (hH : State.get w CH = List.replicate ((sg + 1) * (q + 1)) 1) :
    State.get (hCenterNest.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun b =>
              (List.range (sg + 2)).flatMap (fun x =>
                (List.range (sg + 1)).flatMap (fun z =>
                  S1Cards.blk (S1Cards.xv sg st x) (S1Cards.hv sg q b) z
                    (S1Cards.xv sg st x) (S1Cards.hv sg q b) z))))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ ID →
        State.get (hCenterNest.eval w) r = State.get w r) := by
  obtain ⟨hS1, hS2, -, hBV, hZ⟩ := hconst
  unfold hCenterNest
  have key : State.get ((Cmd.forBnd EJ2 CS1 hCenterLoopX).eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun b =>
              (List.range (sg + 2)).flatMap (fun x =>
                (List.range (sg + 1)).flatMap (fun z =>
                  S1Cards.blk (S1Cards.xv sg st x) (S1Cards.hv sg q b) z
                    (S1Cards.xv sg st x) (S1Cards.hv sg q b) z))))
      ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ2, EJ3, EK2, EK1, CX, EE] →
          State.get ((Cmd.forBnd EJ2 CS1 hCenterLoopX).eval w) r = State.get w r) := by
    refine emitLoop_run EJ2 CS1 EOUT_C hCenterLoopX [EJ2, EJ3, EK2, EK1, CX, EE] _
      (sg + 1) w hS1 (by decide) (by decide) (fun i t hcnt hfr => ?_)
    obtain ⟨hO, hF⟩ := hCenterLoopX_run sg st q i t
      (by rw [hfr CS1 (by decide) (by decide)]; exact hS1)
      (by rw [hfr CS2 (by decide) (by decide)]; exact hS2)
      (by rw [hfr CBV (by decide) (by decide)]; exact hBV)
      (by rw [hfr CH (by decide) (by decide)]; exact hH) hcnt
      (by rw [hfr CZ (by decide) (by decide)]; exact hZ)
    exact ⟨hO, fun r a1 a2 => hF r a1 (nmem_sub (by decide) a2)⟩
  exact ⟨key.1, fun r a1 a2 => key.2 r a1 (nmem_sub (by decide) a2)⟩

/-- **Family 4 is correct.** -/
theorem cHaltCenter_run (sg st : Nat) (hb : List Nat) (s : State)
    (hconst : CConst sg st s) (hph : State.get s S1Parse.PHALT = hb) :
    State.get (cHaltCenter.eval s) EOUT_C
        = State.get s EOUT_C ++ FlatTCCFree.encNats (S1Cards.haltCenterBlocks sg st hb)
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ HD →
        State.get (cHaltCenter.eval s) r = State.get s r) :=
  haltFam_run hCenterNest _ sg st hb s hconst hph
    (fun q t hc hH => hCenterNest_run sg st q t hc hH)

def hRightInner : Cmd := emitId EK1 CX CZ EK2 CZ CH EJ2 EOUT_C
def hRightLoopY : Cmd := Cmd.forBnd EK2 CS1 hRightInner
def hRightBodyX : Cmd := loadX EJ3 ;; hRightLoopY
def hRightLoopX : Cmd := Cmd.forBnd EJ3 CS2 hRightBodyX
def hRightNest  : Cmd := Cmd.forBnd EJ2 CS1 hRightLoopX

/-- **Family 5.** -/
def cHaltRight : Cmd := haltFam hRightNest

private theorem hRightLoopY_run (sg q b X : Nat) (w : State)
    (hS1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hH : State.get w CH = List.replicate ((sg + 1) * (q + 1)) 1)
    (hbb : State.get w EJ2 = List.replicate b 1)
    (hX : State.get w CX = List.replicate X 1)
    (hZ : State.get w CZ = []) :
    State.get (hRightLoopY.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun y =>
              S1Cards.blk X y (S1Cards.hv sg q b) X y (S1Cards.hv sg q b)))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EK2, EK1] →
        State.get (hRightLoopY.eval w) r = State.get w r) := by
  unfold hRightLoopY
  refine emitLoop_run EK2 CS1 EOUT_C hRightInner [EK2, EK1] _ (sg + 1) w hS1
    (by decide) (by decide) (fun i t hcnt hfr => ?_)
  unfold hRightInner
  have tX : State.get t CX = List.replicate X 1 := by
    rw [hfr CX (by decide) (by decide)]; exact hX
  have tH : State.get t CH = List.replicate ((sg + 1) * (q + 1)) 1 := by
    rw [hfr CH (by decide) (by decide)]; exact hH
  have tb : State.get t EJ2 = List.replicate b 1 := by
    rw [hfr EJ2 (by decide) (by decide)]; exact hbb
  have tZ : State.get t CZ = List.replicate 0 1 := by
    rw [hfr CZ (by decide) (by decide)]; exact hZ
  obtain ⟨hO, hF⟩ := emitId_run EK1 CX CZ EK2 CZ CH EJ2 EOUT_C t
    X 0 i 0 ((sg + 1) * (q + 1)) b
    (by decide) (by rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by decide, by decide⟩)
    tX tZ hcnt tZ tH tb
  refine ⟨?_, fun r a1 a2 => hF r a1 (ne_of_nmem a2 (by decide))⟩
  rw [hO]
  simp [S1Cards.hv]

private theorem hRightLoopX_run (sg st q b : Nat) (w : State)
    (hS1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hS2 : State.get w CS2 = List.replicate (sg + 2) 1)
    (hBV : State.get w CBV = List.replicate (S1Cards.bv sg st) 1)
    (hH : State.get w CH = List.replicate ((sg + 1) * (q + 1)) 1)
    (hbb : State.get w EJ2 = List.replicate b 1)
    (hZ : State.get w CZ = []) :
    State.get (hRightLoopX.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 2)).flatMap (fun x =>
              (List.range (sg + 1)).flatMap (fun y =>
                S1Cards.blk (S1Cards.xv sg st x) y (S1Cards.hv sg q b)
                  (S1Cards.xv sg st x) y (S1Cards.hv sg q b))))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ3, EK2, EK1, CX, EE] →
        State.get (hRightLoopX.eval w) r = State.get w r) := by
  unfold hRightLoopX
  refine emitLoop_run EJ3 CS2 EOUT_C hRightBodyX [EJ3, EK2, EK1, CX, EE] _
    (sg + 2) w hS2 (by decide) (by decide) (fun i t hcnt hfr => ?_)
  obtain ⟨lX, lF⟩ := loadX_run EJ3 sg st i t (by decide) hcnt
    (by rw [hfr CBV (by decide) (by decide)]; exact hBV)
  set t1 := (loadX EJ3).eval t with ht1
  clear_value t1
  obtain ⟨hO, hF⟩ := hRightLoopY_run sg q b (S1Cards.xv sg st i) t1
    (by rw [lF CS1 (by decide) (by decide), hfr CS1 (by decide) (by decide)]; exact hS1)
    (by rw [lF CH (by decide) (by decide), hfr CH (by decide) (by decide)]; exact hH)
    (by rw [lF EJ2 (by decide) (by decide), hfr EJ2 (by decide) (by decide)]; exact hbb)
    lX (by rw [lF CZ (by decide) (by decide), hfr CZ (by decide) (by decide)]; exact hZ)
  have hev : hRightBodyX.eval t = hRightLoopY.eval t1 := by
    rw [ht1]; unfold hRightBodyX; rw [Cmd.eval_seq]
  refine ⟨by rw [hev, hO, lF EOUT_C (by decide) (by decide)], fun r a1 a2 => ?_⟩
  have hrX : r ≠ CX := fun h => a2 (by rw [h]; decide)
  have hrE : r ≠ EE := fun h => a2 (by rw [h]; decide)
  rw [hev, hF r a1 (nmem_sub (by decide) a2)]
  exact lF r hrX hrE

private theorem hRightNest_run (sg st q : Nat) (w : State)
    (hconst : CConst sg st w)
    (hH : State.get w CH = List.replicate ((sg + 1) * (q + 1)) 1) :
    State.get (hRightNest.eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun b =>
              (List.range (sg + 2)).flatMap (fun x =>
                (List.range (sg + 1)).flatMap (fun y =>
                  S1Cards.blk (S1Cards.xv sg st x) y (S1Cards.hv sg q b)
                    (S1Cards.xv sg st x) y (S1Cards.hv sg q b)))))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ ID →
        State.get (hRightNest.eval w) r = State.get w r) := by
  obtain ⟨hS1, hS2, -, hBV, hZ⟩ := hconst
  unfold hRightNest
  have key : State.get ((Cmd.forBnd EJ2 CS1 hRightLoopX).eval w) EOUT_C
        = State.get w EOUT_C ++ FlatTCCFree.encNats
            ((List.range (sg + 1)).flatMap (fun b =>
              (List.range (sg + 2)).flatMap (fun x =>
                (List.range (sg + 1)).flatMap (fun y =>
                  S1Cards.blk (S1Cards.xv sg st x) y (S1Cards.hv sg q b)
                    (S1Cards.xv sg st x) y (S1Cards.hv sg q b)))))
      ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ [EJ2, EJ3, EK2, EK1, CX, EE] →
          State.get ((Cmd.forBnd EJ2 CS1 hRightLoopX).eval w) r = State.get w r) := by
    refine emitLoop_run EJ2 CS1 EOUT_C hRightLoopX [EJ2, EJ3, EK2, EK1, CX, EE] _
      (sg + 1) w hS1 (by decide) (by decide) (fun i t hcnt hfr => ?_)
    obtain ⟨hO, hF⟩ := hRightLoopX_run sg st q i t
      (by rw [hfr CS1 (by decide) (by decide)]; exact hS1)
      (by rw [hfr CS2 (by decide) (by decide)]; exact hS2)
      (by rw [hfr CBV (by decide) (by decide)]; exact hBV)
      (by rw [hfr CH (by decide) (by decide)]; exact hH) hcnt
      (by rw [hfr CZ (by decide) (by decide)]; exact hZ)
    exact ⟨hO, fun r a1 a2 => hF r a1 (nmem_sub (by decide) a2)⟩
  exact ⟨key.1, fun r a1 a2 => key.2 r a1 (nmem_sub (by decide) a2)⟩

/-- **Family 5 is correct.** -/
theorem cHaltRight_run (sg st : Nat) (hb : List Nat) (s : State)
    (hconst : CConst sg st s) (hph : State.get s S1Parse.PHALT = hb) :
    State.get (cHaltRight.eval s) EOUT_C
        = State.get s EOUT_C ++ FlatTCCFree.encNats (S1Cards.haltRightBlocks sg st hb)
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ HD →
        State.get (cHaltRight.eval s) r = State.get s r) :=
  haltFam_run hRightNest _ sg st hb s hconst hph
    (fun q t hc hH => hRightNest_run sg st q t hc hH)

/-! ## The preamble and the five-family assembly

`cPre` loads stage C's constants and clears the output register; `cFive` is the
first five summands of `S1Cards.cardBlocks`, in order. The remaining two
families (`stepBlocks` off `normTrans`, and `preludeBlocks`) append after
`cFive` — that, plus `S1Program.stageC := cFive ;; …`, is what closes
`stageC_run`. -/

/-- The registers `cPre` writes (besides `S1Emit.EOUT_C`). -/
def PD : List Var := [CBV, CS1, CS2, CQ1, CZ, EA, EB, ESG, EJ1]

/-- Everything stage C's first five families touch, `EOUT_C` aside. -/
def AD : List Var :=
  [CBV, CS1, CS2, CQ1, CZ, CX, CH, CD, CE, EA, EB, ESG, EE, EJ1, EJ2, EJ3, EK1, EK2]

/-- **Stage C's preamble.** The Γ-band width comes from `S1Emit.loadSg`
(`Sg M = bv + 1`, so the boundary code is one `tail` away) — stage C's only
multiplication, paid once outside every loop. -/
def cPre : Cmd :=
  S1Emit.loadSg ;;
  Cmd.op (.tail CBV ESG) ;;
  Cmd.op (.copy CS1 S1Parse.PSIG) ;; Cmd.op (.appendOne CS1) ;;
  Cmd.op (.copy CS2 CS1) ;; Cmd.op (.appendOne CS2) ;;
  Cmd.op (.copy CQ1 S1Parse.PSTATES) ;; Cmd.op (.appendOne CQ1) ;;
  Cmd.op (.clear CZ) ;;
  Cmd.op (.clear EOUT_C)

theorem cPre_run (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1) :
    CConst M.sig M.states (cPre.eval s)
    ∧ State.get (cPre.eval s) EOUT_C = []
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ PD →
        State.get (cPre.eval s) r = State.get s r) := by
  obtain ⟨hSG, hFr⟩ := S1Emit.loadSg_run M s hsig hst
  set u := S1Emit.loadSg.eval s with hu
  have uSG : State.get u ESG = List.replicate (S1Cards.bv M.sig M.states + 1) 1 := hSG
  have uSig : State.get u S1Parse.PSIG = List.replicate M.sig 1 := by
    rw [hu, hFr S1Parse.PSIG (by decide) (by decide) (by decide) (by decide)]; exact hsig
  have uSt : State.get u S1Parse.PSTATES = List.replicate M.states 1 := by
    rw [hu, hFr S1Parse.PSTATES (by decide) (by decide) (by decide) (by decide)]; exact hst
  have uFr : ∀ r : Var, r ∉ PD → State.get u r = State.get s r := by
    intro r hr
    rw [hu]
    exact hFr r (ne_of_nmem hr (by decide)) (ne_of_nmem hr (by decide))
      (ne_of_nmem hr (by decide)) (ne_of_nmem hr (by decide))
  clear_value u
  have hev : cPre.eval s
      = (Cmd.op (.tail CBV ESG) ;;
          Cmd.op (.copy CS1 S1Parse.PSIG) ;; Cmd.op (.appendOne CS1) ;;
          Cmd.op (.copy CS2 CS1) ;; Cmd.op (.appendOne CS2) ;;
          Cmd.op (.copy CQ1 S1Parse.PSTATES) ;; Cmd.op (.appendOne CQ1) ;;
          Cmd.op (.clear CZ) ;;
          Cmd.op (.clear EOUT_C)).eval u := by
    rw [hu]; unfold cPre; rw [Cmd.eval_seq]
  rw [hev]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [uSig, ← List.replicate_succ']
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [uSig, ← List.replicate_succ', ← List.replicate_succ']
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [uSt, ← List.replicate_succ']
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
    rw [uSG, List.replicate_succ, List.tail_cons]
  · repeat first
      | rw [State.get_set_eq]
      | rw [State.get_set_ne _ _ _ _ (by decide)]
  · rw [State.get_set_eq]
  · intro r a1 a2
    have n1 : r ≠ CBV := ne_of_nmem a2 (by decide)
    have n2 : r ≠ CS1 := ne_of_nmem a2 (by decide)
    have n3 : r ≠ CS2 := ne_of_nmem a2 (by decide)
    have n4 : r ≠ CQ1 := ne_of_nmem a2 (by decide)
    have n5 : r ≠ CZ := ne_of_nmem a2 (by decide)
    repeat first
      | rw [State.get_set_ne _ _ _ _ a1]
      | rw [State.get_set_ne _ _ _ _ n1]
      | rw [State.get_set_ne _ _ _ _ n2]
      | rw [State.get_set_ne _ _ _ _ n3]
      | rw [State.get_set_ne _ _ _ _ n4]
      | rw [State.get_set_ne _ _ _ _ n5]
    exact uFr r a2

/-- **Stage C, families 1–5.** -/
def cFive : Cmd := cPre ;; cCopy ;; cRight ;; cHaltLeft ;; cHaltCenter ;; cHaltRight

/-- **The five families compose.** `EOUT_C` holds the first five summands of
`S1Cards.cardBlocks M`, in order. -/
theorem cFive_run (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (hph : State.get s S1Parse.PHALT = M.halt.map S1Parse.bitOf) :
    State.get (cFive.eval s) EOUT_C
        = FlatTCCFree.encNats
            (S1Cards.copyBlocks M.sig M.states ++
             S1Cards.copyRightBlocks M.sig M.states ++
             S1Cards.haltLeftBlocks M.sig M.states (M.halt.map S1Parse.bitOf) ++
             S1Cards.haltCenterBlocks M.sig M.states (M.halt.map S1Parse.bitOf) ++
             S1Cards.haltRightBlocks M.sig M.states (M.halt.map S1Parse.bitOf))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ AD →
        State.get (cFive.eval s) r = State.get s r) := by
  set hb := M.halt.map S1Parse.bitOf with hhb
  obtain ⟨c0, e0, f0⟩ := cPre_run M s hsig hst
  set s0 := cPre.eval s with hs0
  have p0 : State.get s0 S1Parse.PHALT = hb := by
    rw [f0 S1Parse.PHALT (by decide) (by decide)]; exact hph
  clear_value s0
  obtain ⟨e1, f1⟩ := cCopy_run M.sig M.states s0 c0
  set s1 := cCopy.eval s0 with hs1
  have c1 : CConst M.sig M.states s1 := CConst_frame c0 f1
  have p1 : State.get s1 S1Parse.PHALT = hb := by
    rw [f1 S1Parse.PHALT (by decide) (by decide)]; exact p0
  clear_value s1
  obtain ⟨e2, f2⟩ := cRight_run M.sig M.states s1 c1
  set s2 := cRight.eval s1 with hs2
  have c2 : CConst M.sig M.states s2 := CConst_frame c1 f2
  have p2 : State.get s2 S1Parse.PHALT = hb := by
    rw [f2 S1Parse.PHALT (by decide) (by decide)]; exact p1
  clear_value s2
  obtain ⟨e3, f3⟩ := cHaltLeft_run M.sig M.states hb s2 c2 p2
  set s3 := cHaltLeft.eval s2 with hs3
  have c3 : CConst M.sig M.states s3 := CConst_frame c2 f3
  have p3 : State.get s3 S1Parse.PHALT = hb := by
    rw [f3 S1Parse.PHALT (by decide) (by decide)]; exact p2
  clear_value s3
  obtain ⟨e4, f4⟩ := cHaltCenter_run M.sig M.states hb s3 c3 p3
  set s4 := cHaltCenter.eval s3 with hs4
  have c4 : CConst M.sig M.states s4 := CConst_frame c3 f4
  have p4 : State.get s4 S1Parse.PHALT = hb := by
    rw [f4 S1Parse.PHALT (by decide) (by decide)]; exact p3
  clear_value s4
  obtain ⟨e5, f5⟩ := cHaltRight_run M.sig M.states hb s4 c4 p4
  have hev : cFive.eval s = cHaltRight.eval s4 := by
    rw [hs4, hs3, hs2, hs1, hs0]
    unfold cFive
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  refine ⟨?_, ?_⟩
  · rw [hev, e5, e4, e3, e2, e1, e0]
    simp only [S1Cards.encNats_append, List.nil_append, List.append_assoc]
  · intro r a1 a2
    rw [hev, f5 r a1 (nmem_sub (by decide) a2), f4 r a1 (nmem_sub (by decide) a2),
      f3 r a1 (nmem_sub (by decide) a2), f2 r a1 (nmem_sub (by decide) a2),
      f1 r a1 (nmem_sub (by decide) a2)]
    exact f0 r a1 (nmem_sub (by decide) a2)

/-- **The five families leave stage C's constants standing.** `cPre` establishes
`CConst` and none of the five writes any of its registers, so the `stepBlocks`
family — which runs after `cFive` — needs **no preamble of its own** for
`CS1`/`CS2`/`CQ1`/`CBV`/`CZ`. -/
theorem cFive_const (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (hph : State.get s S1Parse.PHALT = M.halt.map S1Parse.bitOf) :
    CConst M.sig M.states (cFive.eval s) := by
  set hb := M.halt.map S1Parse.bitOf with hhb
  obtain ⟨c0, -, f0⟩ := cPre_run M s hsig hst
  set s0 := cPre.eval s with hs0
  have p0 : State.get s0 S1Parse.PHALT = hb := by
    rw [f0 S1Parse.PHALT (by decide) (by decide)]; exact hph
  clear_value s0
  obtain ⟨-, f1⟩ := cCopy_run M.sig M.states s0 c0
  set s1 := cCopy.eval s0 with hs1
  have c1 : CConst M.sig M.states s1 := CConst_frame c0 f1
  have p1 : State.get s1 S1Parse.PHALT = hb := by
    rw [f1 S1Parse.PHALT (by decide) (by decide)]; exact p0
  clear_value s1
  obtain ⟨-, f2⟩ := cRight_run M.sig M.states s1 c1
  set s2 := cRight.eval s1 with hs2
  have c2 : CConst M.sig M.states s2 := CConst_frame c1 f2
  have p2 : State.get s2 S1Parse.PHALT = hb := by
    rw [f2 S1Parse.PHALT (by decide) (by decide)]; exact p1
  clear_value s2
  obtain ⟨-, f3⟩ := cHaltLeft_run M.sig M.states hb s2 c2 p2
  set s3 := cHaltLeft.eval s2 with hs3
  have c3 : CConst M.sig M.states s3 := CConst_frame c2 f3
  have p3 : State.get s3 S1Parse.PHALT = hb := by
    rw [f3 S1Parse.PHALT (by decide) (by decide)]; exact p2
  clear_value s3
  obtain ⟨-, f4⟩ := cHaltCenter_run M.sig M.states hb s3 c3 p3
  set s4 := cHaltCenter.eval s3 with hs4
  have c4 : CConst M.sig M.states s4 := CConst_frame c3 f4
  have p4 : State.get s4 S1Parse.PHALT = hb := by
    rw [f4 S1Parse.PHALT (by decide) (by decide)]; exact p3
  clear_value s4
  obtain ⟨-, f5⟩ := cHaltRight_run M.sig M.states hb s4 c4 p4
  have hev : cFive.eval s = cHaltRight.eval s4 := by
    rw [hs4, hs3, hs2, hs1, hs0]
    unfold cFive
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  rw [hev]
  exact CConst_frame c4 f5

/-- The preamble stays inside the S1 register bound. -/
theorem cPre_usesBelow : Cmd.UsesBelow cPre 48 := by
  unfold cPre
  refine ⟨S1Emit.loadSg_usesBelow, ?_⟩
  simp [Cmd.UsesBelow, Op.UsesBelow, CBV, CS1, CS2, CQ1, CZ, ESG, EOUT_C,
    S1Parse.PSIG, S1Parse.PSTATES]

/-- **The five families stay inside the S1 register bound.** -/
theorem cFive_usesBelow : Cmd.UsesBelow cFive 48 := by
  unfold cFive
  refine ⟨cPre_usesBelow, ?_⟩
  simp [cCopy, cRight, cHaltLeft, cHaltCenter, cHaltRight,
    haltFam, haltBody, copyBodyX, copyLoopB, copyLoopC, copyInner,
    rightLoopZ, rightInner, hLeftNest, hLeftLoopY, hLeftLoopZ, hLeftInner,
    hCenterNest, hCenterLoopX, hCenterBodyX, hCenterLoopZ, hCenterInner,
    hRightNest, hRightLoopX, hRightBodyX, hRightLoopY, hRightInner,
    loadX, emitId, emitBlk2, FrontPieces.tallyReg,
    Cmd.UsesBelow, Op.UsesBelow,
    CBV, CS1, CS2, CQ1, CX, CH, CD, CE, CZ,
    EOUT_C, EE, EJ1, EJ2, EJ3, EK1, EK2, S1Parse.PHALT]

end S1CardEmit
