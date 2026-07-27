import Complexity.NP.SAT.CookLevin.Reductions.S1Prelude

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/-! # S1, part 5d — stage **C**'s prelude family, the `Cmd`

`S1Prelude` reformulated `S1Cards.preludeBlocks` as `preludeSeg`, the exact
nesting an emitter can implement. This file writes that emitter and proves it.

## ⚠ Finding G — `PJᵢ` cannot carry both the kind level's `add` and the
resolution level's counter

The pinned register table gave `PJᵢ` a double role: the *kind* level was to
publish a non-star kind's `add` into it, and the *resolution* level was to use
it as its `forBnd` counter. That does not frame: the resolution nest sits
**inside** all three kind levels, so it re-runs `7²` times under kind level 1
and `7` times under kind level 2, clobbering `PJ1`/`PJ2` between the moment the
kind level writes them and the moment the emit body reads them. Making the
frame conditional on `PSTᵢ` (the two writers are disjoint *per kind*) would
force every frame clause in the nest to carry a `star`-indexed side condition.

The fix costs nothing: fold `add` into the *base* register. A kind level
publishes **`PPAᵢ := 1^pav`** where `pav = base` for a star kind and
`base + add` for every other, and the resolution level owns `PJᵢ` outright —
`clear` in the non-star branch, the loop counter in the live branch, `1^σ` in
the cut branch. `pResLevel'`/`pKindSeg`/`preludeSeg'` below are `preludeSeg`
with that single change, and `preludeBlocks_seg'` is the faithfulness proof.

## Shape of the emitter

```
cPrelude = pPre ;; pKindCmd₁ (pKindCmd₂ (pKindCmd₃ resNest))
resNest  = pRes₁ (pRes₂ (pRes₃ pEmit))
```

`pKindCmd` and `pRes` are register-generic gadgets applied three times each, so
`next` occurs `7×` resp. `3×` in the *definition* but the `Cmd` is a small term
(a `def` applied to an argument — never unfold it) and each `_run` lemma is
proven once and applied three times.
-/

namespace S1Prelude

open Complexity.Lang Complexity.Simulators HeadLayout
open S1Emit S1CardEmit

/-! ## The model, with `add` folded into the base (Finding G) -/

/-- One resolution level, reading a single value register `1^pav`. -/
def pResLevel' (σ pav : Nat) (star cs : Bool) (g : Nat → Bool → List Nat) :
    List Nat :=
  if star then
    (if cs then [] else (List.range σ).flatMap (fun j => g (pav + j) false))
      ++ g (pav + σ) true
  else g pav cs

theorem pResLevel_eq' (σ base add : Nat) (star cs : Bool) (g : Nat → Bool → List Nat) :
    pResLevel σ base add star cs g
      = pResLevel' σ (if star then base else base + add) star cs g := by
  cases star <;> simp [pResLevel, pResLevel']

/-- One kind level's seven segments, each publishing `(k, star?, pav)`. -/
def pKindSeg {α : Type} (σ st q0 : Nat) (h : Nat → Bool → Nat → List α) : List α :=
  h 0 false (S1Cards.bv σ st) ++
  (h 1 false σ ++
   (h 2 true 0 ++
    (h 3 true (S1Cards.hv σ q0 0) ++
     (h 4 false (S1Cards.hv σ q0 0 + σ) ++
      ((List.range σ).flatMap (fun d => h (5 + d) false d) ++
       (List.range σ).flatMap (fun d => h (5 + σ + d) false (S1Cards.hv σ q0 0 + d)))))))

theorem pKindSeg_of {α : Type} (σ st q0 : Nat) (h : Nat → Bool → Nat → List α) :
    pKindLevel σ st q0 (fun k star base add => h k star (if star then base else base + add))
      = pKindSeg σ st q0 h := by
  simp [pKindLevel, pKindSeg]

/-- `pKindLevel_eq` in the folded coordinates: this is what the emitter's kind
level meets. -/
theorem pKindSeg_eq {α : Type} (σ st q0 : Nat) (h : Nat → Bool → Nat → List α)
    (G : Nat → List α)
    (hG : ∀ k star base add, S1Cards.resOf σ st q0 k = resShape σ base add star →
      G k = h k star (if star then base else base + add)) :
    (List.range (2 * σ + 5)).flatMap G = pKindSeg σ st q0 h := by
  rw [pKindLevel_eq σ st q0
    (fun k star base add => h k star (if star then base else base + add)) G hG]
  exact pKindSeg_of σ st q0 h

/-- **The prelude family in the emitter's coordinates.** -/
def preludeSeg' (σ st q0 : Nat) : List Nat :=
  pKindSeg σ st q0 (fun k1 s1 a1 =>
    pKindSeg σ st q0 (fun k2 s2 a2 =>
      pKindSeg σ st q0 (fun k3 s3 a3 =>
        pResLevel' σ a1 s1 false (fun v1 c1 =>
          pResLevel' σ a2 s2 c1 (fun v2 c2 =>
            pResLevel' σ a3 s3 c2 (fun v3 _ =>
              S1Cards.blk (S1Cards.sgv σ st + k1) (S1Cards.sgv σ st + k2)
                (S1Cards.sgv σ st + k3) v1 v2 v3))))))

/-- **The re-coordinatisation is faithful.** -/
theorem preludeBlocks_seg' (σ st q0 : Nat) :
    S1Cards.preludeBlocks σ st q0 = preludeSeg' σ st q0 := by
  unfold S1Cards.preludeBlocks preludeSeg'
  refine pKindSeg_eq σ st q0 _ _ (fun k1 s1 b1 a1 h1 => ?_)
  refine pKindSeg_eq σ st q0 _ _ (fun k2 s2 b2 a2 h2 => ?_)
  refine pKindSeg_eq σ st q0 _ _ (fun k3 s3 b3 a3 h3 => ?_)
  rw [pBody_gate]
  simp only [h1, h2, h3, pGate_resShape, pResLevel_eq']

/-! ## The emitter contract

Every gadget below appends to `EOUT_C` and touches nothing outside a static
register list `D`. Packaging that as one predicate keeps the three-level nest's
statements readable and gives sequencing a single lemma. -/

/-- `c` appends `encNats l` to `EOUT_C`, touching nothing outside `D ∪
{EOUT_C}`. `Emits D c [] w` is "`c` is invisible to the emitter". -/
def Emits (D : List Var) (c : Cmd) (l : List Nat) (w : State) : Prop :=
  State.get (c.eval w) EOUT_C = State.get w EOUT_C ++ FlatTCCFree.encNats l
  ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ D → State.get (c.eval w) r = State.get w r)

theorem Emits.seq {D : List Var} {c1 c2 : Cmd} {l1 l2 : List Nat} {w : State}
    (h1 : Emits D c1 l1 w) (h2 : Emits D c2 l2 (c1.eval w)) :
    Emits D (c1 ;; c2) (l1 ++ l2) w := by
  obtain ⟨o1, f1⟩ := h1
  obtain ⟨o2, f2⟩ := h2
  refine ⟨?_, fun r a b => by rw [Cmd.eval_seq, f2 r a b]; exact f1 r a b⟩
  rw [Cmd.eval_seq, o2, o1, S1Cards.encNats_append, List.append_assoc]

/-- The layer's no-op emits nothing. -/
theorem Emits.nop (D : List Var) (w : State) :
    Emits D (Cmd.op (.copy EOUT_C EOUT_C)) [] w := by
  refine ⟨?_, fun r _ _ => copy_self_get EOUT_C r w⟩
  rw [copy_self_get, encNats_nil, List.append_nil]

/-- Rewrite the emitted list of an `Emits`. -/
theorem Emits.congr_l {D : List Var} {c : Cmd} {l l' : List Nat} {w : State}
    (h : Emits D c l w) (he : l = l') : Emits D c l' w := he ▸ h

/-! ## Flags -/

/-- A `Bool` as the layer represents it in an `ifBit` test register. -/
def flagRep : Bool → List Nat
  | true => [1]
  | false => []

theorem flagRep_true_iff {b : Bool} : flagRep b = [1] ↔ b = true := by
  cases b <;> simp [flagRep]

def setTrue (r : Var) : Cmd := Cmd.op (.clear r) ;; Cmd.op (.appendOne r)

theorem setTrue_get (r : Var) (s : State) :
    State.get ((setTrue r).eval s) r = flagRep true := by
  simp only [setTrue, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq]
  rfl

theorem setTrue_frame (r : Var) (s : State) (q : Var) (h : q ≠ r) :
    State.get ((setTrue r).eval s) q = State.get s q := by
  simp only [setTrue, Cmd.eval_seq, Cmd.eval_op, Op.eval]
  rw [State.get_set_ne _ _ _ _ h, State.get_set_ne _ _ _ _ h]

/-! ## The resolution level

One register-generic gadget, used three times. `cinR` is read exactly once (by
the outer `ifBit`) and never again, which is what lets level 3 take
`cinR = coutR = PCS3`. -/

/-- One resolution level. `stR` = "is this a star kind?", `pjR` = the level's
own counter (owned outright — Finding G), `cinR`/`coutR` = the cut-seen bit in
and out. -/
def pRes (stR pjR cinR coutR : Var) (next : Cmd) : Cmd :=
  Cmd.ifBit stR
    (Cmd.ifBit cinR (Cmd.op (.copy EOUT_C EOUT_C))
        (Cmd.forBnd pjR S1Parse.PSIG (Cmd.op (.clear coutR) ;; next)) ;;
      Cmd.op (.copy pjR S1Parse.PSIG) ;; setTrue coutR ;; next)
    (Cmd.op (.clear pjR) ;; Cmd.op (.copy coutR cinR) ;; next)

/-- **The resolution level is correct.** -/
theorem pRes_run (stR pjR cinR coutR : Var) (next : Cmd) (D : List Var)
    (σ pav : Nat) (star cs : Bool) (g : Nat → Bool → List Nat) (w : State)
    (hpjD : pjR ∈ D) (hcoutD : coutR ∈ D)
    (hpjE : pjR ≠ EOUT_C) (hcoutE : coutR ≠ EOUT_C) (hpjc : pjR ≠ coutR)
    (hcinj : cinR ≠ pjR)
    (hstD : stR ∉ D) (hstE : stR ≠ EOUT_C)
    (hsigD : S1Parse.PSIG ∉ D) (hsigE : S1Parse.PSIG ≠ EOUT_C)
    (hsig : State.get w S1Parse.PSIG = List.replicate σ 1)
    (hst : State.get w stR = flagRep star)
    (hcin : State.get w cinR = flagRep cs)
    (hnext : ∀ (j : Nat) (c : Bool) (t : State),
        State.get t pjR = List.replicate j 1 →
        State.get t coutR = flagRep c →
        (∀ r : Var, r ≠ EOUT_C → r ∉ D → State.get t r = State.get w r) →
        Emits D next (g (pav + j) c) t) :
    Emits D (pRes stR pjR cinR coutR next) (pResLevel' σ pav star cs g) w := by
  have hcp : coutR ≠ pjR := Ne.symm hpjc
  cases star with
  | false =>
      -- the non-star branch: `clear pjR ;; copy coutR cinR ;; next`
      have hfalse : State.get w stR ≠ [1] := by rw [hst]; simp [flagRep]
      -- after `clear pjR`
      set u := (Cmd.op (Op.clear pjR)).eval w with hu
      have uJ : State.get u pjR = List.replicate 0 1 := by
        rw [hu, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; rfl
      have uFr : ∀ r : Var, r ≠ pjR → State.get u r = State.get w r := by
        intro r hr; rw [hu, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
      clear_value u
      -- after `copy coutR cinR`
      set v := (Cmd.op (Op.copy coutR cinR)).eval u with hv
      have vC : State.get v coutR = flagRep cs := by
        rw [hv, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq]
        rw [uFr cinR hcinj]; exact hcin
      have vJ : State.get v pjR = List.replicate 0 1 := by
        rw [hv, Cmd.eval_op]
        simp only [Op.eval, State.get_set_ne _ _ _ _ hpjc]
        exact uJ
      have vFr : ∀ r : Var, r ≠ pjR → r ≠ coutR → State.get v r = State.get w r := by
        intro r a b
        rw [hv, Cmd.eval_op]
        simp only [Op.eval, State.get_set_ne _ _ _ _ b]
        exact uFr r a
      clear_value v
      have hev : (pRes stR pjR cinR coutR next).eval w = next.eval v := by
        rw [hv, hu]
        show (Cmd.ifBit stR _ _).eval w = _
        rw [Cmd.eval_ifBit_false _ _ _ _ hfalse, Cmd.eval_seq, Cmd.eval_seq]
      obtain ⟨nO, nF⟩ := hnext 0 cs v vJ vC
        (fun r a b => vFr r (fun h => b (h ▸ hpjD)) (fun h => b (h ▸ hcoutD)))
      refine ⟨?_, ?_⟩
      · rw [hev, nO]
        have : State.get v EOUT_C = State.get w EOUT_C :=
          vFr EOUT_C (Ne.symm hpjE) (Ne.symm hcoutE)
        rw [this]
        simp only [pResLevel', if_neg (by decide : ¬ (false = true)), Nat.add_zero]
      · intro r a b
        rw [hev, nF r a b]
        exact vFr r (fun h => b (h ▸ hpjD)) (fun h => b (h ▸ hcoutD))
  | true =>
      -- the star branch
      have htrue : State.get w stR = [1] := by rw [hst]; rfl
      -- the gate `ifBit cinR nop loop` — call its result `u`
      set gate : Cmd := Cmd.ifBit cinR (Cmd.op (.copy EOUT_C EOUT_C))
        (Cmd.forBnd pjR S1Parse.PSIG (Cmd.op (.clear coutR) ;; next)) with hgate
      have hgateE : Emits D gate
          (if cs then [] else (List.range σ).flatMap (fun j => g (pav + j) false)) w := by
        cases cs with
        | true =>
            have : State.get w cinR = [1] := by rw [hcin]; rfl
            have he : gate.eval w = (Cmd.op (Op.copy EOUT_C EOUT_C)).eval w := by
              rw [hgate, Cmd.eval_ifBit_true _ _ _ _ this]
            show Emits D gate ([] : List Nat) w
            refine ⟨?_, fun r a b => ?_⟩
            · rw [he, copy_self_get, encNats_nil, List.append_nil]
            · rw [he]; exact copy_self_get EOUT_C r w
        | false =>
            have hne : State.get w cinR ≠ [1] := by rw [hcin]; simp [flagRep]
            have he : gate.eval w
                = (Cmd.forBnd pjR S1Parse.PSIG (Cmd.op (.clear coutR) ;; next)).eval w := by
              rw [hgate, Cmd.eval_ifBit_false _ _ _ _ hne]
            show Emits D gate ((List.range σ).flatMap (fun j => g (pav + j) false)) w
            rw [Emits, he]
            refine emitLoop_run pjR S1Parse.PSIG EOUT_C _ D _ σ w hsig
              hpjE hpjD ?_
            intro i t hti htFr
            -- one live iteration: `clear coutR ;; next`
            set z := (Cmd.op (Op.clear coutR)).eval t with hz
            have zC : State.get z coutR = flagRep false := by
              rw [hz, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; rfl
            have zFr : ∀ r : Var, r ≠ coutR → State.get z r = State.get t r := by
              intro r hr; rw [hz, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
            clear_value z
            have zJ : State.get z pjR = List.replicate i 1 := by
              rw [zFr pjR hpjc]; exact hti
            obtain ⟨nO, nF⟩ := hnext i false z zJ zC
              (fun r a b => by rw [zFr r (fun h => b (h ▸ hcoutD))]; exact htFr r a b)
            have hevz : (Cmd.op (Op.clear coutR) ;; next).eval t = next.eval z := by
              rw [hz, Cmd.eval_seq]
            refine ⟨?_, fun r a b => ?_⟩
            · rw [hevz, nO, zFr EOUT_C (Ne.symm hcoutE)]
            · rw [hevz, nF r a b]
              exact zFr r (fun h => b (h ▸ hcoutD))
      -- the cut tail: `copy pjR PSIG ;; setTrue coutR ;; next`
      obtain ⟨gO, gF⟩ := hgateE
      set u := gate.eval w with hu
      have uSig : State.get u S1Parse.PSIG = List.replicate σ 1 := by
        rw [hu, gF S1Parse.PSIG hsigE hsigD]; exact hsig
      clear_value u
      set p := (Cmd.op (Op.copy pjR S1Parse.PSIG)).eval u with hp
      have pJ : State.get p pjR = List.replicate σ 1 := by
        rw [hp, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; exact uSig
      have pFr : ∀ r : Var, r ≠ pjR → State.get p r = State.get u r := by
        intro r hr; rw [hp, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
      clear_value p
      set q := (setTrue coutR).eval p with hq
      have qC : State.get q coutR = flagRep true := by rw [hq]; exact setTrue_get coutR p
      have qJ : State.get q pjR = List.replicate σ 1 := by
        rw [hq, setTrue_frame coutR p pjR hpjc]; exact pJ
      have qFr : ∀ r : Var, r ≠ pjR → r ≠ coutR → State.get q r = State.get u r := by
        intro r a b; rw [hq, setTrue_frame coutR p r b]; exact pFr r a
      clear_value q
      obtain ⟨nO, nF⟩ := hnext σ true q qJ qC (fun r a b => by
        rw [qFr r (fun h => b (h ▸ hpjD)) (fun h => b (h ▸ hcoutD))]
        exact gF r a b)
      have hev : (pRes stR pjR cinR coutR next).eval w = next.eval q := by
        rw [hq, hp, hu, hgate]
        show (Cmd.ifBit stR _ _).eval w = _
        rw [Cmd.eval_ifBit_true _ _ _ _ htrue, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
      refine ⟨?_, ?_⟩
      · rw [hev, nO, qFr EOUT_C (Ne.symm hpjE) (Ne.symm hcoutE), gO]
        have hps : pResLevel' σ pav true cs g
            = (if cs then [] else (List.range σ).flatMap (fun j => g (pav + j) false))
              ++ g (pav + σ) true := rfl
        rw [hps, S1Cards.encNats_append, List.append_assoc]
      · intro r a b
        rw [hev, nF r a b, qFr r (fun h => b (h ▸ hpjD)) (fun h => b (h ▸ hcoutD))]
        exact gF r a b

/-! ## Value gadgets

`setLit` writes a compile-time constant, `loadSum` adds a list of registers'
lengths, `loadVal` is the two composed: `dst := 1^(n + Σ|srcs|)`. Every unary
value the kind level publishes is of that shape, so one gadget serves all
fourteen register writes (`1^k` and `1^pav` in each of the seven segments). -/

/-- `dst := 1^n` for a compile-time `n`. -/
def setLit (r : Var) : Nat → Cmd
  | 0 => Cmd.op (.clear r)
  | n + 1 => setLit r n ;; Cmd.op (.appendOne r)

theorem setLit_run (r : Var) : ∀ (n : Nat) (s : State),
    State.get ((setLit r n).eval s) r = List.replicate n 1
    ∧ (∀ q : Var, q ≠ r → State.get ((setLit r n).eval s) q = State.get s q) := by
  intro n
  induction n with
  | zero =>
      intro s
      refine ⟨?_, fun q hq => ?_⟩
      · show State.get ((Cmd.op (Op.clear r)).eval s) r = _
        rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; rfl
      · show State.get ((Cmd.op (Op.clear r)).eval s) q = _
        rw [Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hq
  | succ n ih =>
      intro s
      obtain ⟨hO, hF⟩ := ih s
      have hev : (setLit r (n + 1)).eval s
          = (Cmd.op (Op.appendOne r)).eval ((setLit r n).eval s) := by
        show (setLit r n ;; Cmd.op (Op.appendOne r)).eval s = _
        rw [Cmd.eval_seq]
      refine ⟨?_, fun q hq => ?_⟩
      · rw [hev, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq, hO]
        rw [← List.replicate_succ']
      · rw [hev, Cmd.eval_op]
        simp only [Op.eval, State.get_set_ne _ _ _ _ hq]
        exact hF q hq

/-- The total cell count of a register list — the value `loadSum` adds. -/
def sumLen (s : State) (srcs : List Var) : Nat :=
  (srcs.map (fun v => (State.get s v).length)).sum

theorem sumLen_congr {s t : State} {srcs : List Var}
    (h : ∀ v ∈ srcs, State.get t v = State.get s v) : sumLen t srcs = sumLen s srcs := by
  unfold sumLen
  exact congrArg List.sum (List.map_congr_left (fun v hv => by rw [h v hv]))

/-- `dst ++= 1^(Σ_{src ∈ srcs} |src|)`. -/
def loadSum (cnt dst : Var) : List Var → Cmd
  | [] => Cmd.op (.copy dst dst)
  | src :: rest => FrontPieces.tallyReg cnt src dst ;; loadSum cnt dst rest

theorem loadSum_run (cnt dst : Var) (hcd : cnt ≠ dst) :
    ∀ (srcs : List Var) (s : State), (∀ v ∈ srcs, v ≠ dst ∧ v ≠ cnt) →
      State.get ((loadSum cnt dst srcs).eval s) dst
          = State.get s dst ++ List.replicate (sumLen s srcs) 1
      ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
          State.get ((loadSum cnt dst srcs).eval s) r = State.get s r) := by
  intro srcs
  induction srcs with
  | nil =>
      intro s _
      refine ⟨?_, fun r _ _ => copy_self_get dst r s⟩
      show State.get ((Cmd.op (Op.copy dst dst)).eval s) dst = _
      rw [copy_self_get]
      simp [sumLen]
  | cons src rest ih =>
      intro s hne
      obtain ⟨hsd, hsc⟩ := hne src (List.mem_cons_self ..)
      obtain ⟨tD, tF, -⟩ := FrontPieces.tallyReg_run cnt src dst s hcd
      set s1 := (FrontPieces.tallyReg cnt src dst).eval s with hs1
      have s1D : State.get s1 dst = State.get s dst ++ List.replicate (State.get s src).length 1 := by
        rw [hs1]; exact tD
      have s1F : ∀ r : Var, r ≠ dst → r ≠ cnt → State.get s1 r = State.get s r := by
        intro r a b; rw [hs1]; exact tF r a b
      clear_value s1
      obtain ⟨rD, rF⟩ := ih s1 (fun v hv => hne v (List.mem_cons_of_mem _ hv))
      have hsum : sumLen s1 rest = sumLen s rest :=
        sumLen_congr (fun v hv => by
          obtain ⟨a, b⟩ := hne v (List.mem_cons_of_mem _ hv); exact s1F v a b)
      have hev : (loadSum cnt dst (src :: rest)).eval s = (loadSum cnt dst rest).eval s1 := by
        rw [hs1]
        show (FrontPieces.tallyReg cnt src dst ;; loadSum cnt dst rest).eval s = _
        rw [Cmd.eval_seq]
      refine ⟨?_, fun r a b => by rw [hev, rF r a b]; exact s1F r a b⟩
      rw [hev, rD, s1D, hsum, List.append_assoc, ← List.replicate_add]
      congr 2

/-- `dst := 1^(n + Σ|srcs|)`. -/
def loadVal (cnt dst : Var) (n : Nat) (srcs : List Var) : Cmd :=
  setLit dst n ;; loadSum cnt dst srcs

theorem loadVal_run (cnt dst : Var) (n : Nat) (srcs : List Var) (s : State)
    (hcd : cnt ≠ dst) (hsrc : ∀ v ∈ srcs, v ≠ dst ∧ v ≠ cnt) :
    State.get ((loadVal cnt dst n srcs).eval s) dst
        = List.replicate (n + sumLen s srcs) 1
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
        State.get ((loadVal cnt dst n srcs).eval s) r = State.get s r) := by
  obtain ⟨lO, lF⟩ := setLit_run dst n s
  set s1 := (setLit dst n).eval s with hs1
  clear_value s1
  obtain ⟨sO, sF⟩ := loadSum_run cnt dst hcd srcs s1 hsrc
  have hsum : sumLen s1 srcs = sumLen s srcs :=
    sumLen_congr (fun v hv => lF v (hsrc v hv).1)
  have hev : (loadVal cnt dst n srcs).eval s = (loadSum cnt dst srcs).eval s1 := by
    rw [hs1]; show (setLit dst n ;; loadSum cnt dst srcs).eval s = _; rw [Cmd.eval_seq]
  refine ⟨?_, fun r a b => by rw [hev, sF r a b]; exact lF r a⟩
  rw [hev, sO, lO, hsum, ← List.replicate_add]

/-- A `Bool` written into a test register. -/
def setFlag (r : Var) (b : Bool) : Cmd :=
  if b then setTrue r else Cmd.op (.clear r)

theorem setFlag_get (r : Var) (b : Bool) (s : State) :
    State.get ((setFlag r b).eval s) r = flagRep b := by
  cases b
  · show State.get ((Cmd.op (Op.clear r)).eval s) r = _
    rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; rfl
  · exact setTrue_get r s

theorem setFlag_frame (r : Var) (b : Bool) (s : State) (q : Var) (h : q ≠ r) :
    State.get ((setFlag r b).eval s) q = State.get s q := by
  cases b
  · show State.get ((Cmd.op (Op.clear r)).eval s) q = _
    rw [Cmd.eval_op]; exact State.get_set_ne _ _ _ _ h
  · exact setTrue_frame r s q h

/-! ## One kind-level segment -/

/-- Publish `(1^k, star?, 1^pav)` into the level's three registers and run
`next`. `k = klit + Σ|kvSrcs|` and `pav = Σ|paSrcs|`. -/
def pSeg (kvR stR paR : Var) (klit : Nat) (kvSrcs : List Var) (star : Bool)
    (paSrcs : List Var) (next : Cmd) : Cmd :=
  loadVal EK1 kvR klit kvSrcs ;; setFlag stR star ;;
  loadVal EK1 paR 0 paSrcs ;; next

theorem pSeg_run (kvR stR paR : Var) (klit : Nat) (kvSrcs : List Var) (star : Bool)
    (paSrcs : List Var) (next : Cmd) (D : List Var) (L : List Nat) (w : State)
    (hkvD : kvR ∈ D) (hstD : stR ∈ D) (hpaD : paR ∈ D) (hcntD : EK1 ∈ D)
    (hkvE : kvR ≠ EOUT_C) (hstE : stR ≠ EOUT_C) (hpaE : paR ≠ EOUT_C)
    (hkvc : EK1 ≠ kvR) (hpac : EK1 ≠ paR) (hkvpa : kvR ≠ paR)
    (hstc : stR ≠ EK1) (hstkv : stR ≠ kvR) (hstpa : stR ≠ paR)
    (hkvs : ∀ v ∈ kvSrcs, v ≠ kvR ∧ v ≠ EK1)
    (hpas : ∀ v ∈ paSrcs, v ≠ kvR ∧ v ≠ stR ∧ v ≠ paR ∧ v ≠ EK1)
    (hnext : ∀ t : State,
        State.get t kvR = List.replicate (klit + sumLen w kvSrcs) 1 →
        State.get t stR = flagRep star →
        State.get t paR = List.replicate (sumLen w paSrcs) 1 →
        (∀ r : Var, r ≠ EOUT_C → r ∉ D → State.get t r = State.get w r) →
        Emits D next L t) :
    Emits D (pSeg kvR stR paR klit kvSrcs star paSrcs next) L w := by
  -- `1^k` into `kvR`
  obtain ⟨aO, aF⟩ := loadVal_run EK1 kvR klit kvSrcs w hkvc hkvs
  set a := (loadVal EK1 kvR klit kvSrcs).eval w with ha
  clear_value a
  -- the star flag
  set b := (setFlag stR star).eval a with hb
  have bSt : State.get b stR = flagRep star := by rw [hb]; exact setFlag_get stR star a
  have bFr : ∀ r : Var, r ≠ stR → State.get b r = State.get a r := by
    intro r hr; rw [hb]; exact setFlag_frame stR star a r hr
  clear_value b
  have bKv : State.get b kvR = List.replicate (klit + sumLen w kvSrcs) 1 := by
    rw [bFr kvR (Ne.symm hstkv)]; exact aO
  -- `1^pav` into `paR`
  obtain ⟨cO, cF⟩ := loadVal_run EK1 paR 0 paSrcs b hpac
    (fun v hv => ⟨(hpas v hv).2.2.1, (hpas v hv).2.2.2⟩)
  set c := (loadVal EK1 paR 0 paSrcs).eval b with hc
  clear_value c
  have hsum : sumLen b paSrcs = sumLen w paSrcs :=
    sumLen_congr (fun v hv => by
      obtain ⟨n1, n2, -, n4⟩ := hpas v hv
      rw [bFr v n2]; exact aF v n1 n4)
  have cPa : State.get c paR = List.replicate (sumLen w paSrcs) 1 := by
    rw [cO, hsum, Nat.zero_add]
  have cKv : State.get c kvR = List.replicate (klit + sumLen w kvSrcs) 1 := by
    rw [cF kvR hkvpa (Ne.symm hkvc)]; exact bKv
  have cSt : State.get c stR = flagRep star := by
    rw [cF stR hstpa hstc]; exact bSt
  have cFr : ∀ r : Var, r ≠ EOUT_C → r ∉ D → State.get c r = State.get w r := by
    intro r a1 b1
    rw [cF r (fun h => b1 (h ▸ hpaD)) (fun h => b1 (h ▸ hcntD)),
      bFr r (fun h => b1 (h ▸ hstD))]
    exact aF r (fun h => b1 (h ▸ hkvD)) (fun h => b1 (h ▸ hcntD))
  have hev : (pSeg kvR stR paR klit kvSrcs star paSrcs next).eval w = next.eval c := by
    rw [hc, hb, ha]
    show (loadVal EK1 kvR klit kvSrcs ;; setFlag stR star ;;
      loadVal EK1 paR 0 paSrcs ;; next).eval w = _
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  have hcntE : (EK1 : Var) ≠ EOUT_C := by decide
  have cOut : State.get c EOUT_C = State.get w EOUT_C := by
    rw [cF EOUT_C (Ne.symm hpaE) (Ne.symm hcntE), bFr EOUT_C (Ne.symm hstE)]
    exact aF EOUT_C (Ne.symm hkvE) (Ne.symm hcntE)
  obtain ⟨nO, nF⟩ := hnext c cKv cSt cPa cFr
  refine ⟨?_, fun r a1 b1 => ?_⟩
  · rw [hev, nO, cOut]
  · rw [hev, nF r a1 b1]; exact cFr r a1 b1

/-- `c` emits `l` from **any** state agreeing with `w` outside `D`. Sequencing
a chain of these needs no intermediate-state bookkeeping. -/
def EmitsFr (D : List Var) (c : Cmd) (l : List Nat) (w : State) : Prop :=
  ∀ u : State, (∀ r : Var, r ≠ EOUT_C → r ∉ D → State.get u r = State.get w r) →
    Emits D c l u

theorem EmitsFr.seq {D : List Var} {c1 c2 : Cmd} {l1 l2 : List Nat} {w : State}
    (h1 : EmitsFr D c1 l1 w) (h2 : EmitsFr D c2 l2 w) :
    EmitsFr D (c1 ;; c2) (l1 ++ l2) w := by
  intro u hu
  refine Emits.seq (h1 u hu) (h2 _ (fun r a b => ?_))
  rw [(h1 u hu).2 r a b]; exact hu r a b

theorem EmitsFr.here {D : List Var} {c : Cmd} {l : List Nat} {w : State}
    (h : EmitsFr D c l w) : Emits D c l w := h w (fun _ _ _ => rfl)

/-! ## One kind level — seven constant-shape segments (Finding 4) -/

/-- One kind level: the five special kinds as straight-line segments and the two
`σ`-long bands as `forBnd` loops. `next` occurs seven times in this *definition*
— never unfold it; `pKindCmd_run` is proven once and applied three times. -/
def pKindCmd (kvR stR paR kcR : Var) (next : Cmd) : Cmd :=
  pSeg kvR stR paR 0 [] false [PBV] next ;;
  pSeg kvR stR paR 1 [] false [S1Parse.PSIG] next ;;
  pSeg kvR stR paR 2 [] true [] next ;;
  pSeg kvR stR paR 3 [] true [PHB] next ;;
  pSeg kvR stR paR 4 [] false [PHB, S1Parse.PSIG] next ;;
  Cmd.forBnd kcR S1Parse.PSIG (pSeg kvR stR paR 5 [kcR] false [kcR] next) ;;
  Cmd.forBnd kcR S1Parse.PSIG
    (pSeg kvR stR paR 5 [S1Parse.PSIG, kcR] false [PHB, kcR] next)

/-- **A kind level is correct.** -/
theorem pKindCmd_run (kvR stR paR kcR : Var) (next : Cmd) (D : List Var)
    (σ st q0 : Nat) (h : Nat → Bool → Nat → List Nat) (w : State)
    (hbv : State.get w PBV = List.replicate (S1Cards.bv σ st) 1)
    (hhb : State.get w PHB = List.replicate (S1Cards.hv σ q0 0) 1)
    (hsig : State.get w S1Parse.PSIG = List.replicate σ 1)
    (hkvD : kvR ∈ D) (hstD : stR ∈ D) (hpaD : paR ∈ D) (hkcD : kcR ∈ D)
    (hcntD : EK1 ∈ D)
    (hkvE : kvR ≠ EOUT_C) (hstE : stR ≠ EOUT_C) (hpaE : paR ≠ EOUT_C)
    (hkcE : kcR ≠ EOUT_C)
    (hkvc : EK1 ≠ kvR) (hpac : EK1 ≠ paR) (hkvpa : kvR ≠ paR)
    (hstc : stR ≠ EK1) (hstkv : stR ≠ kvR) (hstpa : stR ≠ paR)
    (hkckv : kcR ≠ kvR) (hkcst : kcR ≠ stR) (hkcpa : kcR ≠ paR) (hkcc : kcR ≠ EK1)
    (hcst : ∀ v ∈ ([PBV, PHB, S1Parse.PSIG] : List Var),
        v ∉ D ∧ v ≠ EOUT_C ∧ v ≠ kvR ∧ v ≠ stR ∧ v ≠ paR ∧ v ≠ EK1)
    (hnext : ∀ (k : Nat) (star : Bool) (pav : Nat) (t : State),
        State.get t kvR = List.replicate k 1 →
        State.get t stR = flagRep star →
        State.get t paR = List.replicate pav 1 →
        (∀ r : Var, r ≠ EOUT_C → r ∉ D → State.get t r = State.get w r) →
        Emits D next (h k star pav) t) :
    Emits D (pKindCmd kvR stR paR kcR next) (pKindSeg σ st q0 h) w := by
  obtain ⟨bD, bE, bkv, bst, bpa, bc⟩ := hcst PBV (by simp)
  obtain ⟨hD, hE, hkv, hst, hpa, hc⟩ := hcst PHB (by simp)
  obtain ⟨sD, sE, skv, sst, spa, sc⟩ := hcst S1Parse.PSIG (by simp)
  -- one segment, at an arbitrary state agreeing with `w` outside `D`
  have seg : ∀ (u : State) (klit : Nat) (kvSrcs : List Var) (star : Bool)
      (paSrcs : List Var) (k pav : Nat),
      (∀ r : Var, r ≠ EOUT_C → r ∉ D → State.get u r = State.get w r) →
      (∀ v ∈ kvSrcs, v ≠ kvR ∧ v ≠ EK1) →
      (∀ v ∈ paSrcs, v ≠ kvR ∧ v ≠ stR ∧ v ≠ paR ∧ v ≠ EK1) →
      klit + sumLen u kvSrcs = k → sumLen u paSrcs = pav →
      Emits D (pSeg kvR stR paR klit kvSrcs star paSrcs next) (h k star pav) u := by
    intro u klit kvSrcs star paSrcs k pav hufr hkvs hpas hk hpav
    refine pSeg_run kvR stR paR klit kvSrcs star paSrcs next D (h k star pav) u
      hkvD hstD hpaD hcntD hkvE hstE hpaE hkvc hpac hkvpa hstc hstkv hstpa hkvs hpas ?_
    intro t t1 t2 t3 t4
    rw [hk] at t1
    rw [hpav] at t3
    exact hnext k star pav t t1 t2 t3 (fun r a b => by rw [t4 r a b]; exact hufr r a b)
  -- the five special kinds
  have S0 : EmitsFr D (pSeg kvR stR paR 0 [] false [PBV] next)
      (h 0 false (S1Cards.bv σ st)) w := by
    intro u hu
    refine seg u 0 [] false [PBV] _ _ hu (by simp) (by simpa using ⟨bkv, bst, bpa, bc⟩)
      (by simp [sumLen]) ?_
    simp [sumLen, hu PBV bE bD, hbv]
  have G1 : EmitsFr D (pSeg kvR stR paR 1 [] false [S1Parse.PSIG] next)
      (h 1 false σ) w := by
    intro u hu
    refine seg u 1 [] false [S1Parse.PSIG] _ _ hu (by simp)
      (by simpa using ⟨skv, sst, spa, sc⟩) (by simp [sumLen]) ?_
    simp [sumLen, hu S1Parse.PSIG sE sD, hsig]
  have G2 : EmitsFr D (pSeg kvR stR paR 2 [] true [] next) (h 2 true 0) w := by
    intro u hu
    exact seg u 2 [] true [] _ _ hu (by simp) (by simp) (by simp [sumLen])
      (by simp [sumLen])
  have G3 : EmitsFr D (pSeg kvR stR paR 3 [] true [PHB] next)
      (h 3 true (S1Cards.hv σ q0 0)) w := by
    intro u hu
    refine seg u 3 [] true [PHB] _ _ hu (by simp) (by simpa using ⟨hkv, hst, hpa, hc⟩)
      (by simp [sumLen]) ?_
    simp [sumLen, hu PHB hE hD, hhb]
  have G4 : EmitsFr D (pSeg kvR stR paR 4 [] false [PHB, S1Parse.PSIG] next)
      (h 4 false (S1Cards.hv σ q0 0 + σ)) w := by
    intro u hu
    refine seg u 4 [] false [PHB, S1Parse.PSIG] _ _ hu (by simp) ?_ (by simp [sumLen]) ?_
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact ⟨hkv, hst, hpa, hc⟩
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact ⟨skv, sst, spa, sc⟩
        · cases hv
    · simp [sumLen, hu PHB hE hD, hu S1Parse.PSIG sE sD, hhb, hsig]
  -- the two bands
  have BT : EmitsFr D
      (Cmd.forBnd kcR S1Parse.PSIG (pSeg kvR stR paR 5 [kcR] false [kcR] next))
      ((List.range σ).flatMap (fun d => h (5 + d) false d)) w := by
    intro u hu
    refine emitLoop_run kcR S1Parse.PSIG EOUT_C _ D _ σ u
      (by rw [hu S1Parse.PSIG sE sD]; exact hsig) hkcE hkcD ?_
    intro i t hti htfr
    exact seg t 5 [kcR] false [kcR] (5 + i) i
      (fun r a b => by rw [htfr r a b]; exact hu r a b)
      (by simpa using ⟨hkckv, hkcc⟩) (by simpa using ⟨hkckv, hkcst, hkcpa, hkcc⟩)
      (by simp [sumLen, hti]) (by simp [sumLen, hti])
  have BH : EmitsFr D
      (Cmd.forBnd kcR S1Parse.PSIG
        (pSeg kvR stR paR 5 [S1Parse.PSIG, kcR] false [PHB, kcR] next))
      ((List.range σ).flatMap (fun d => h (5 + σ + d) false (S1Cards.hv σ q0 0 + d))) w := by
    intro u hu
    refine emitLoop_run kcR S1Parse.PSIG EOUT_C _ D _ σ u
      (by rw [hu S1Parse.PSIG sE sD]; exact hsig) hkcE hkcD ?_
    intro i t hti htfr
    have hfr : ∀ r : Var, r ≠ EOUT_C → r ∉ D → State.get t r = State.get w r :=
      fun r a b => by rw [htfr r a b]; exact hu r a b
    have tsig : State.get t S1Parse.PSIG = List.replicate σ 1 := by
      rw [hfr S1Parse.PSIG sE sD]; exact hsig
    have thb : State.get t PHB = List.replicate (S1Cards.hv σ q0 0) 1 := by
      rw [hfr PHB hE hD]; exact hhb
    refine seg t 5 [S1Parse.PSIG, kcR] false [PHB, kcR] (5 + σ + i)
      (S1Cards.hv σ q0 0 + i) hfr ?_ ?_ ?_ ?_
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact ⟨skv, sc⟩
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact ⟨hkckv, hkcc⟩
        · cases hv
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact ⟨hkv, hst, hpa, hc⟩
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact ⟨hkckv, hkcst, hkcpa, hkcc⟩
        · cases hv
    · simp only [sumLen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        tsig, hti, List.length_replicate]
      omega
    · simp only [sumLen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        thb, hti, List.length_replicate]
      omega
  exact (S0.seq (G1.seq (G2.seq (G3.seq (G4.seq (BT.seq BH)))))).here

/-! ## The innermost body and the resolution nest

⚠ The three resolution levels need **nested** dirty lists for the same reason
the kind levels do: level 3's frame must not claim `PJ1`/`PJ2` (which the emit
body reads) as dirty, even though level 1 owns them. -/

/-- Widen an `Emits`' dirty licence. -/
theorem Emits.mono {D D' : List Var} (hsub : ∀ x ∈ D, x ∈ D') {c : Cmd} {l : List Nat}
    {w : State} (hE : Emits D c l w) : Emits D' c l w :=
  ⟨hE.1, fun r a b => hE.2 r a (fun hm => b (hsub _ hm))⟩

/-- Level 3's dirty list. -/
def DR3 : List Var := [PJ3, PCS3, EK1]
/-- Level 2's dirty list. -/
def DR2 : List Var := [PJ2, PJ3, PCS3, EK1]
/-- The whole resolution nest's dirty list. -/
def DR1 : List Var := [PJ1, PJ2, PJ3, PCS2, PCS3, EK1]

/-- **The prelude card.** The three premise cells are `|ESG| + |PKVᵢ|` and the
three conclusion cells `|PPAᵢ| + |PJᵢ|`. -/
def pEmit : Cmd :=
  emitList EK1 EOUT_C [(ESG, PKV1), (ESG, PKV2), (ESG, PKV3),
    (PPA1, PJ1), (PPA2, PJ2), (PPA3, PJ3)]

theorem pEmit_run (sg k1 k2 k3 pav1 pav2 pav3 j1 j2 j3 : Nat) (t : State)
    (hesg : State.get t ESG = List.replicate sg 1)
    (e1 : State.get t PKV1 = List.replicate k1 1)
    (e2 : State.get t PKV2 = List.replicate k2 1)
    (e3 : State.get t PKV3 = List.replicate k3 1)
    (p1 : State.get t PPA1 = List.replicate pav1 1)
    (p2 : State.get t PPA2 = List.replicate pav2 1)
    (p3 : State.get t PPA3 = List.replicate pav3 1)
    (q1 : State.get t PJ1 = List.replicate j1 1)
    (q2 : State.get t PJ2 = List.replicate j2 1)
    (q3 : State.get t PJ3 = List.replicate j3 1) :
    Emits DR3 pEmit
      (S1Cards.blk (sg + k1) (sg + k2) (sg + k3)
        (pav1 + j1) (pav2 + j2) (pav3 + j3)) t := by
  have hrep : ∀ (r : Var) (n : Nat), State.get t r = List.replicate n 1 →
      State.get t r = List.replicate (State.get t r).length 1 := by
    intro r n hr; rw [hr, List.length_replicate]
  have hne : ∀ p ∈ ([(ESG, PKV1), (ESG, PKV2), (ESG, PKV3),
      (PPA1, PJ1), (PPA2, PJ2), (PPA3, PJ3)] : List (Var × Var)),
      p.1 ≠ EOUT_C ∧ p.1 ≠ EK1 ∧ p.2 ≠ EOUT_C ∧ p.2 ≠ EK1 := by decide
  have hval : ∀ p ∈ ([(ESG, PKV1), (ESG, PKV2), (ESG, PKV3),
      (PPA1, PJ1), (PPA2, PJ2), (PPA3, PJ3)] : List (Var × Var)),
      State.get t p.1 = List.replicate ((fun r => (State.get t r).length) p.1) 1
      ∧ State.get t p.2 = List.replicate ((fun r => (State.get t r).length) p.2) 1 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hrep _ _ hesg, hrep _ _ e1⟩
    · exact ⟨hrep _ _ hesg, hrep _ _ e2⟩
    · exact ⟨hrep _ _ hesg, hrep _ _ e3⟩
    · exact ⟨hrep _ _ p1, hrep _ _ q1⟩
    · exact ⟨hrep _ _ p2, hrep _ _ q2⟩
    · exact ⟨hrep _ _ p3, hrep _ _ q3⟩
  obtain ⟨hO, hF⟩ := emitList_run EK1 EOUT_C (fun r => (State.get t r).length)
    (by decide) _ t hne hval
  have hmap : List.map (fun p => (State.get t p.1).length + (State.get t p.2).length)
      ([(ESG, PKV1), (ESG, PKV2), (ESG, PKV3),
        (PPA1, PJ1), (PPA2, PJ2), (PPA3, PJ3)] : List (Var × Var))
      = S1Cards.blk (sg + k1) (sg + k2) (sg + k3)
        (pav1 + j1) (pav2 + j2) (pav3 + j3) := by
    simp only [List.map_cons, List.map_nil, hesg, e1, e2, e3, p1, p2, p3, q1, q2, q3,
      List.length_replicate, S1Cards.blk]
  refine ⟨?_, fun r a b => hF r a (fun hc => b (by rw [hc]; decide))⟩
  show State.get ((emitList EK1 EOUT_C _).eval t) EOUT_C = _
  rw [hO, hmap]

/-- **The resolution nest.** Level 1's gate reads `PZ` (permanently `[]`), so it
is always false; level 3's out-bit is dead and re-uses `PCS3`. -/
def resNest : Cmd :=
  pRes PST1 PJ1 PZ PCS2 (pRes PST2 PJ2 PCS2 PCS3 (pRes PST3 PJ3 PCS3 PCS3 pEmit))

/-- **The resolution nest is correct.** -/
theorem resNest_run (σ sg k1 k2 k3 pav1 pav2 pav3 : Nat) (s1 s2 s3 : Bool) (t : State)
    (hsig : State.get t S1Parse.PSIG = List.replicate σ 1)
    (hesg : State.get t ESG = List.replicate sg 1)
    (hz : State.get t PZ = [])
    (e1 : State.get t PKV1 = List.replicate k1 1)
    (e2 : State.get t PKV2 = List.replicate k2 1)
    (e3 : State.get t PKV3 = List.replicate k3 1)
    (p1 : State.get t PPA1 = List.replicate pav1 1)
    (p2 : State.get t PPA2 = List.replicate pav2 1)
    (p3 : State.get t PPA3 = List.replicate pav3 1)
    (t1 : State.get t PST1 = flagRep s1)
    (t2 : State.get t PST2 = flagRep s2)
    (t3 : State.get t PST3 = flagRep s3) :
    Emits DR1 resNest
      (pResLevel' σ pav1 s1 false (fun v1 c1 =>
        pResLevel' σ pav2 s2 c1 (fun v2 c2 =>
          pResLevel' σ pav3 s3 c2 (fun v3 _ =>
            S1Cards.blk (sg + k1) (sg + k2) (sg + k3) v1 v2 v3)))) t := by
  refine pRes_run PST1 PJ1 PZ PCS2 _ DR1 σ pav1 s1 false _ t
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hsig t1 (by rw [hz]; rfl) ?_
  intro j1 c1 u uJ uC uFr
  have uSig : State.get u S1Parse.PSIG = List.replicate σ 1 := by
    rw [uFr S1Parse.PSIG (by decide) (by decide)]; exact hsig
  refine Emits.mono (by decide) (D := DR2)
    (pRes_run PST2 PJ2 PCS2 PCS3 _ DR2 σ pav2 s2 c1 _ u
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) uSig
      (by rw [uFr PST2 (by decide) (by decide)]; exact t2) uC ?_)
  intro j2 c2 v vJ vC vFr
  have vSig : State.get v S1Parse.PSIG = List.replicate σ 1 := by
    rw [vFr S1Parse.PSIG (by decide) (by decide)]; exact uSig
  refine Emits.mono (by decide) (D := DR3)
    (pRes_run PST3 PJ3 PCS3 PCS3 _ DR3 σ pav3 s3 c2 _ v
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) vSig
      (by rw [vFr PST3 (by decide) (by decide),
        uFr PST3 (by decide) (by decide)]; exact t3) vC ?_)
  intro j3 c3 x xJ xC xFr
  have step : ∀ (r : Var), r ∉ DR3 → r ∉ DR2 → r ∉ DR1 → r ≠ EOUT_C →
      State.get x r = State.get t r := by
    intro r a b c d
    rw [xFr r d a, vFr r d b, uFr r d c]
  exact pEmit_run sg k1 k2 k3 pav1 pav2 pav3 j1 j2 j3 x
    (by rw [step ESG (by decide) (by decide) (by decide) (by decide)]; exact hesg)
    (by rw [step PKV1 (by decide) (by decide) (by decide) (by decide)]; exact e1)
    (by rw [step PKV2 (by decide) (by decide) (by decide) (by decide)]; exact e2)
    (by rw [step PKV3 (by decide) (by decide) (by decide) (by decide)]; exact e3)
    (by rw [step PPA1 (by decide) (by decide) (by decide) (by decide)]; exact p1)
    (by rw [step PPA2 (by decide) (by decide) (by decide) (by decide)]; exact p2)
    (by rw [step PPA3 (by decide) (by decide) (by decide) (by decide)]; exact p3)
    (by rw [xFr PJ1 (by decide) (by decide), vFr PJ1 (by decide) (by decide)]; exact uJ)
    (by rw [xFr PJ2 (by decide) (by decide)]; exact vJ)
    xJ

/-! ## The three kind levels and the whole family -/

/-- Kind level 3's dirty list. -/
def DK3 : List Var := [PKV3, PST3, PPA3, PKC3, PJ1, PJ2, PJ3, PCS2, PCS3, EK1]
/-- Kind level 2's dirty list. -/
def DK2 : List Var := [PKV2, PST2, PPA2, PKC2] ++ DK3
/-- The whole kind nest's dirty list. -/
def DK1 : List Var := [PKV1, PST1, PPA1, PKC1] ++ DK2

/-- **The three kind levels.** -/
def kindNest : Cmd :=
  pKindCmd PKV1 PST1 PPA1 PKC1
    (pKindCmd PKV2 PST2 PPA2 PKC2
      (pKindCmd PKV3 PST3 PPA3 PKC3 resNest))

/-- **The kind nest is correct.** -/
theorem kindNest_run (σ st q0 : Nat) (w : State)
    (hc : PConst σ st q0 w)
    (hsig : State.get w S1Parse.PSIG = List.replicate σ 1) :
    Emits DK1 kindNest (preludeSeg' σ st q0) w := by
  obtain ⟨hesg, hbv, hz, -, hhb⟩ := hc
  unfold kindNest preludeSeg'
  refine pKindCmd_run PKV1 PST1 PPA1 PKC1 _ DK1 σ st q0 _ w hbv hhb hsig
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  intro k1 s1 a1 t hkv1 hst1 hpa1 hfr1
  have tbv : State.get t PBV = List.replicate (S1Cards.bv σ st) 1 := by
    rw [hfr1 PBV (by decide) (by decide)]; exact hbv
  have thb : State.get t PHB = List.replicate (S1Cards.hv σ q0 0) 1 := by
    rw [hfr1 PHB (by decide) (by decide)]; exact hhb
  have tsig : State.get t S1Parse.PSIG = List.replicate σ 1 := by
    rw [hfr1 S1Parse.PSIG (by decide) (by decide)]; exact hsig
  refine Emits.mono (D := DK2) (by decide)
    (pKindCmd_run PKV2 PST2 PPA2 PKC2 _ DK2 σ st q0 _ t tbv thb tsig
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_)
  intro k2 s2 a2 u hkv2 hst2 hpa2 hfr2
  have ubv : State.get u PBV = List.replicate (S1Cards.bv σ st) 1 := by
    rw [hfr2 PBV (by decide) (by decide)]; exact tbv
  have uhb : State.get u PHB = List.replicate (S1Cards.hv σ q0 0) 1 := by
    rw [hfr2 PHB (by decide) (by decide)]; exact thb
  have usig : State.get u S1Parse.PSIG = List.replicate σ 1 := by
    rw [hfr2 S1Parse.PSIG (by decide) (by decide)]; exact tsig
  refine Emits.mono (D := DK3) (by decide)
    (pKindCmd_run PKV3 PST3 PPA3 PKC3 _ DK3 σ st q0 _ u ubv uhb usig
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_)
  intro k3 s3 a3 v hkv3 hst3 hpa3 hfr3
  have step2 : ∀ r : Var, r ≠ EOUT_C → r ∉ DK3 → r ∉ DK2 →
      State.get v r = State.get t r := by
    intro r a b c; rw [hfr3 r a b]; exact hfr2 r a c
  have step1 : ∀ r : Var, r ≠ EOUT_C → r ∉ DK3 → r ∉ DK2 → r ∉ DK1 →
      State.get v r = State.get w r := by
    intro r a b c d; rw [step2 r a b c]; exact hfr1 r a d
  refine Emits.mono (D := DR1) (by decide)
    (resNest_run σ (S1Cards.sgv σ st) k1 k2 k3 a1 a2 a3 s1 s2 s3 v
      (by rw [step1 S1Parse.PSIG (by decide) (by decide) (by decide) (by decide)]; exact hsig)
      (by rw [step1 ESG (by decide) (by decide) (by decide) (by decide)]; exact hesg)
      (by rw [step1 PZ (by decide) (by decide) (by decide) (by decide)]; exact hz)
      (by rw [step2 PKV1 (by decide) (by decide) (by decide)]; exact hkv1)
      (by rw [hfr3 PKV2 (by decide) (by decide)]; exact hkv2)
      hkv3
      (by rw [step2 PPA1 (by decide) (by decide) (by decide)]; exact hpa1)
      (by rw [hfr3 PPA2 (by decide) (by decide)]; exact hpa2)
      hpa3
      (by rw [step2 PST1 (by decide) (by decide) (by decide)]; exact hst1)
      (by rw [hfr3 PST2 (by decide) (by decide)]; exact hst2)
      hst3)

/-! ## Stage C's prelude family -/

/-- Everything the prelude family writes, `EOUT_C` aside. -/
def PDirty : List Var := PD ++ DK1

/-- **Stage C's prelude family.** -/
def cPrelude : Cmd := pPre ;; kindNest

/-- **The prelude family is correct.** -/
theorem cPrelude_run (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (hstart : State.get s S1Parse.PSTART = List.replicate M.start 1) :
    State.get (cPrelude.eval s) EOUT_C
        = State.get s EOUT_C
          ++ FlatTCCFree.encNats
              (S1Cards.preludeBlocks M.sig M.states (min M.start M.states))
    ∧ (∀ r : Var, r ≠ EOUT_C → r ∉ PDirty →
        State.get (cPrelude.eval s) r = State.get s r) := by
  obtain ⟨hconst, hfr⟩ := pPre_run M s hsig hst hstart
  set u := pPre.eval s with hu
  clear_value u
  have usig : State.get u S1Parse.PSIG = List.replicate M.sig 1 := by
    rw [hfr S1Parse.PSIG (by decide)]; exact hsig
  obtain ⟨kO, kF⟩ := kindNest_run M.sig M.states (min M.start M.states) u hconst usig
  have hev : cPrelude.eval s = kindNest.eval u := by
    rw [hu]; show (pPre ;; kindNest).eval s = _; rw [Cmd.eval_seq]
  refine ⟨?_, fun r a b => ?_⟩
  · rw [hev, kO, hfr EOUT_C (by decide), preludeBlocks_seg']
  · rw [hev, kF r a (fun hm => b (by simp only [PDirty, List.mem_append]; exact Or.inr hm))]
    exact hfr r (fun hm => b (by simp only [PDirty, List.mem_append]; exact Or.inl hm))

/-! ## `UsesBelow` -/

theorem setLit_usesBelow (r : Var) (hr : r < 48) :
    ∀ n : Nat, Cmd.UsesBelow (setLit r n) 48 := by
  intro n
  induction n with
  | zero => exact hr
  | succ n ih => exact ⟨ih, hr⟩

theorem loadSum_usesBelow (dst : Var) (hd : dst < 48) :
    ∀ srcs : List Var, (∀ v ∈ srcs, v < 48) → Cmd.UsesBelow (loadSum EK1 dst srcs) 48 := by
  intro srcs
  induction srcs with
  | nil => intro _; exact ⟨hd, hd⟩
  | cons a rest ih =>
      intro hv
      exact ⟨⟨by decide, hv a (List.mem_cons_self ..), hd⟩,
        ih (fun v hvm => hv v (List.mem_cons_of_mem _ hvm))⟩

theorem pSeg_usesBelow (kvR stR paR : Var) (klit : Nat) (kvSrcs : List Var) (star : Bool)
    (paSrcs : List Var) (next : Cmd)
    (hkv : kvR < 48) (hst : stR < 48) (hpa : paR < 48)
    (hkvs : ∀ v ∈ kvSrcs, v < 48) (hpas : ∀ v ∈ paSrcs, v < 48)
    (hn : Cmd.UsesBelow next 48) :
    Cmd.UsesBelow (pSeg kvR stR paR klit kvSrcs star paSrcs next) 48 := by
  refine ⟨⟨setLit_usesBelow kvR hkv klit, loadSum_usesBelow kvR hkv kvSrcs hkvs⟩, ?_,
    ⟨setLit_usesBelow paR hpa 0, loadSum_usesBelow paR hpa paSrcs hpas⟩, hn⟩
  cases star
  · exact hst
  · exact ⟨hst, hst⟩

theorem pKindCmd_usesBelow (kvR stR paR kcR : Var) (next : Cmd)
    (hkv : kvR < 48) (hst : stR < 48) (hpa : paR < 48) (hkc : kcR < 48)
    (hn : Cmd.UsesBelow next 48) :
    Cmd.UsesBelow (pKindCmd kvR stR paR kcR next) 48 := by
  have hb : (PBV : Var) < 48 := by decide
  have hh : (PHB : Var) < 48 := by decide
  have hs : (S1Parse.PSIG : Var) < 48 := by decide
  refine ⟨pSeg_usesBelow kvR stR paR 0 [] false [PBV] next hkv hst hpa (by simp)
      (by simp [hb]) hn,
    pSeg_usesBelow kvR stR paR 1 [] false [S1Parse.PSIG] next hkv hst hpa (by simp)
      (by simp [hs]) hn,
    pSeg_usesBelow kvR stR paR 2 [] true [] next hkv hst hpa (by simp) (by simp) hn,
    pSeg_usesBelow kvR stR paR 3 [] true [PHB] next hkv hst hpa (by simp)
      (by simp [hh]) hn,
    pSeg_usesBelow kvR stR paR 4 [] false [PHB, S1Parse.PSIG] next hkv hst hpa (by simp)
      (by simp [hh, hs]) hn,
    ⟨hkc, hs, pSeg_usesBelow kvR stR paR 5 [kcR] false [kcR] next hkv hst hpa
      (by simp [hkc]) (by simp [hkc]) hn⟩,
    hkc, hs, pSeg_usesBelow kvR stR paR 5 [S1Parse.PSIG, kcR] false [PHB, kcR] next
      hkv hst hpa (by simp [hs, hkc]) (by simp [hh, hkc]) hn⟩

theorem pRes_usesBelow (stR pjR cinR coutR : Var) (next : Cmd)
    (h1 : stR < 48) (h2 : pjR < 48) (h3 : cinR < 48) (h4 : coutR < 48)
    (hn : Cmd.UsesBelow next 48) :
    Cmd.UsesBelow (pRes stR pjR cinR coutR next) 48 := by
  simp only [pRes, setTrue, Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;>
    first
      | exact h1 | exact h2 | exact h3 | exact h4 | exact hn | decide

theorem pEmit_usesBelow : Cmd.UsesBelow pEmit 48 := by
  simp only [pEmit, emitList, emitBlk2, FrontPieces.tallyReg, Cmd.UsesBelow, Op.UsesBelow]
  and_intros <;> decide

theorem resNest_usesBelow : Cmd.UsesBelow resNest 48 :=
  pRes_usesBelow PST1 PJ1 PZ PCS2 _ (by decide) (by decide) (by decide) (by decide)
    (pRes_usesBelow PST2 PJ2 PCS2 PCS3 _ (by decide) (by decide) (by decide) (by decide)
      (pRes_usesBelow PST3 PJ3 PCS3 PCS3 _ (by decide) (by decide) (by decide) (by decide)
        pEmit_usesBelow))

theorem kindNest_usesBelow : Cmd.UsesBelow kindNest 48 :=
  pKindCmd_usesBelow PKV1 PST1 PPA1 PKC1 _ (by decide) (by decide) (by decide) (by decide)
    (pKindCmd_usesBelow PKV2 PST2 PPA2 PKC2 _ (by decide) (by decide) (by decide) (by decide)
      (pKindCmd_usesBelow PKV3 PST3 PPA3 PKC3 _ (by decide) (by decide) (by decide)
        (by decide) resNest_usesBelow))

/-- **The prelude family stays inside the S1 register bound.** -/
theorem cPrelude_usesBelow : Cmd.UsesBelow cPrelude 48 :=
  ⟨pPre_usesBelow, kindNest_usesBelow⟩

/-- **Every register the prelude family writes is inside stage C's licence**
(`S1Program.CDirty` = `EScratch ∨ r = EOUT_C ∨ 14 ≤ r < 32`). -/
theorem PDirty_cdirty {r : Var} (hr : r ∈ PDirty) :
    (14 ≤ r ∧ r < 32) ∨ (37 ≤ r ∧ r < 48) := by
  revert hr
  have hall : ∀ v ∈ PDirty, (14 ≤ v ∧ v < 32) ∨ (37 ≤ v ∧ v < 48) := by decide
  exact hall r

end S1Prelude
