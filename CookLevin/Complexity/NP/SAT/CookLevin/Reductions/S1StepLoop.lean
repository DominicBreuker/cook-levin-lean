import Complexity.NP.SAT.CookLevin.Reductions.S1StepEmit

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/-! # S1, part 5g — stage **C**'s `stepBlocks` family, the per-entry preamble
and the entry loop

`S1StepEmit` built the entry *body* (`stepEmit`: nine numbers in registers →
that entry's cards) and specified the *loop* (`emitFold_run`, `stepGo`,
`stepSummand_fold`). This file writes the two `Cmd`s in between:

* **`entryPre`** — the per-entry preamble. It pops one entry off a cursor over
  `encSyms (S1Parse.transFlat M)`, publishes `S1Step.SEntry`, decides "emit this
  entry?" into one flag, and pushes the entry's key onto the seen register.
* **`stepFam`** — `Cmd.forBnd SCNT PNTRANS (entryPre ;; ifBit SKP stepEmit nop)`,
  closed by `emitFold_run` at `α = List key × List entry` and finished with
  `stepSummand_fold`.

## FINDING T — the entry loop's body must be total, not just correct in range

`emitFold_run`'s `hstep` is quantified over **every** iteration index `i`, not
just `i < n`: the loop principle never learns that the cursor is non-empty. So
the body cannot be "correct for a real entry" only — it has to emit `[]` and
preserve the carried state when the cursor has run dry. Both loops here are
therefore wrapped in `nonEmpty`-guards on their own cursors (`entryBody`,
`scanBody`), which is one `Op` and removes the need for any relation between the
loop bound and the carried list. **Every future cursor loop wants this guard.**

## FINDING U — the seen-set is a *prepend* register, not an append register

`S1Step.stepSt` conses the new key (`keyOf e :: seen`), so the machine must
prepend too: `Cmd.op (.concat SSEEN item SSEEN)`, not `concat SSEEN SSEEN item`.
`concat dst a b` writes `get a ++ get b`, so prepending is free — and it keeps
the invariant a literal `encSyms (keyFlat seen)` instead of a `reverse`.

## FINDING V — the scan's loop bound may be the seen register itself

The membership scan must run at least `|seen|` times, and no register holds
`1^|seen|` (the licence is exactly full). It does not have to run *exactly*
`|seen|` times: with the cursor guard of FINDING T the extra iterations are
no-ops, so `Cmd.forBnd EK1 SSEEN …` — `|encSyms (keyFlat seen)| ≥ |seen|` — is a
legitimate bound. **A guarded cursor loop only needs an upper bound.**

## Registers — stage C's licence is now EXACTLY full

```
34 EOUT_C
SConst  14 CBV  18 CS1  19 CS2  27 CZ                    (+ 6 PSIG, read-only)
SEntry  20 TQ   23 TQ2  24 TR   25 TW0  17 TW1  39 TFN  40 TFR
SD1     21 CX   42 EE   28 TJ1  29 TJ2  30 TJ3  46 EK1   (stepEmit's scratch,
                                                          the preamble's too)
loop    41 SCUR   the PTRANS cursor        43 SSEEN  the seen-key stream
        44 SCNT   the loop counter         45 SKP    "emit this entry?"
        31 SKQ    src_state, then "mTag = 0"
        37 SKT / 38 SKV   the option (tag, val), read twice
        47 SAX    transient                22 SIX    readItem's index
        15/16/26  `CliqueRelTM.readNum`'s reserved trio
```
That is all 30 registers of `S1Program.CDirty`. `SConst`'s four are the only
ones outside `LD` (the loop's dirty list), which is exactly what
`SConst_of_cFive` needs.
-/

namespace S1Step

open Complexity.Lang Complexity.Simulators HeadLayout
open S1Emit S1CardEmit S1Prelude S1Cards

/-! ## The entry loop's register frame -/

/-- The cursor over `encSyms (S1Parse.transFlat M)`'s remaining entries. -/
def SCUR : Var := 41
/-- The seen-key stream, `encSyms` of three numbers per key. -/
def SSEEN : Var := 43
/-- The entry loop's counter. -/
def SCNT : Var := 44
/-- "Emit this entry?" — false if the key repeats or the source state halts. -/
def SKP : Var := 45
/-- The key's first component (`src_state`); after the push, the `mTag = 0`
flag. -/
def SKQ : Var := 31
/-- An option's tag, `1^(oTag o)`. -/
def SKT : Var := 37
/-- An option's payload, `1^(oVal o)`. -/
def SKV : Var := 38
/-- Transient scratch (an inner flag, the key item under construction). -/
def SAX : Var := 47
/-- `S1Parse.readItem`'s index register. -/
def SIX : Var := 22

/-- **Everything the entry loop's body may write.** -/
def LD : List Var :=
  [SCUR, SSEEN, SCNT, SKP, SKQ, SKT, SKV, SAX, SIX,
   TQ, TQ2, TR, TW0, TW1, TFN, TFR,
   CX, EE, TJ1, TJ2, TJ3, EK1,
   CliqueRelTM.HEAD, CliqueRelTM.INBLK, CliqueRelTM.SKIPR]

theorem SD1_LD : ∀ x ∈ SD1, x ∈ LD := by decide

/-- The gadget frame every step of the preamble is stated in. -/
def Keeps (c : Cmd) (w : State) : Prop :=
  ∀ r : Var, r ∉ LD → State.get (c.eval w) r = State.get w r

theorem Keeps.seq {c1 c2 : Cmd} {w : State} (h1 : Keeps c1 w)
    (h2 : Keeps c2 (c1.eval w)) : Keeps (c1 ;; c2) w := by
  intro r hr; rw [Cmd.eval_seq, h2 r hr]; exact h1 r hr

/-- Promote an op-level frame to `Keeps`. -/
theorem keeps_of_op {d : Var} (hd : d ∈ LD) (o : Op) (w : State)
    (ho : ∀ r : Var, r ≠ d → State.get ((Cmd.op o).eval w) r = State.get w r) :
    Keeps (Cmd.op o) w :=
  fun r hr => ho r (ne_of_nmem hr hd)

/-- **The frame workhorse.** A command whose syntactic write set sits inside
`LD` preserves everything outside it. Every use site is `by decide`; the finer
"which register *inside* `LD` survives this gadget?" questions are answered the
same way, by `Cmd.eval_get_of_not_writes … (by decide)` at a concrete
register. -/
theorem keeps_of_writes {c : Cmd} (h : ∀ x ∈ c.writes, x ∈ LD) (w : State) :
    Keeps c w :=
  fun r hr => Cmd.eval_get_of_not_writes c w r (nmem_sub h hr)

/-! ## The seen register's model -/

/-- The seen-key set as a `Nat` stream: three numbers per key. -/
def keyFlat (ks : List (Nat × Nat × Nat)) : List Nat :=
  ks.flatMap (fun k => [k.1, k.2.1, k.2.2])

theorem keyFlat_cons (k : Nat × Nat × Nat) (ks : List (Nat × Nat × Nat)) :
    keyFlat (k :: ks) = [k.1, k.2.1, k.2.2] ++ keyFlat ks := rfl

/-- The seen stream is at least as long as the seen list — the bound
FINDING V needs. -/
theorem keyFlat_len_le (ks : List (Nat × Nat × Nat)) :
    ks.length ≤ (encSyms (keyFlat ks)).length := by
  induction ks with
  | nil => simp [keyFlat, encSyms]
  | cons k ks ih =>
      rw [keyFlat_cons, encSyms_append, List.length_append, List.length_cons]
      have h : 1 ≤ (encSyms [k.1, k.2.1, k.2.2]).length := by
        rw [show ([k.1, k.2.1, k.2.2] : List Nat) = k.1 :: [k.2.1, k.2.2] from rfl,
          S1Parse.encSyms_cons]
        simp [S1Parse.itemOf]
      omega

/-! ## `Cmd`-level helpers -/

/-- The layer's no-op. -/
def snop : Cmd := Cmd.op (.copy EOUT_C EOUT_C)

theorem snop_get (r : Var) (w : State) : State.get (snop.eval w) r = State.get w r :=
  copy_self_get EOUT_C r w

/-- Drop `q` cells off `dst` — the random-access walk the halt lookup needs. -/
def dropLoop (cnt bnd dst : Var) : Cmd := Cmd.forBnd cnt bnd (Cmd.op (.tail dst dst))

theorem dropLoop_run (cnt bnd dst : Var) (q : Nat) (l : List Nat) (w : State)
    (hcd : cnt ≠ dst) (hbnd : State.get w bnd = List.replicate q 1)
    (hdst : State.get w dst = l) :
    State.get ((dropLoop cnt bnd dst).eval w) dst = l.drop q
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
        State.get ((dropLoop cnt bnd dst).eval w) r = State.get w r) := by
  have key := Cmd.foldlState_range_induct (Cmd.op (.tail dst dst)) cnt q w
    (fun i st => State.get st dst = l.drop i
      ∧ ∀ r : Var, r ≠ dst → r ≠ cnt → State.get st r = State.get w r)
    ⟨by rw [hdst, List.drop_zero], fun _ _ _ => rfl⟩
    (by
      intro i st _ hM
      obtain ⟨hD, hFr⟩ := hM
      refine ⟨?_, fun r a b => ?_⟩
      · rw [Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq]
        rw [State.get_set_ne _ _ _ _ (Ne.symm hcd), hD, List.tail_drop]
      · rw [Cmd.eval_op]
        simp only [Op.eval]
        rw [State.get_set_ne _ _ _ _ a, State.get_set_ne _ _ _ _ b]
        exact hFr r a b)
  unfold dropLoop
  rw [Cmd.eval_forBnd, hbnd, List.length_replicate]
  exact key

/-! ## The halt lookup

`haltBit hb q` is a random access into the raw bit list `PHALT`: drain `q`
cells, take the head, compare with `[1]`. The `[]` case (index out of range) is
exactly `getD _ 0 = 0 ≠ 1`, so no bounds check is needed. -/

theorem head_drop_iff (l : List Nat) (q : Nat) :
    (match l.drop q with | [] => ([] : List Nat) | x :: _ => [x]) = [1]
      ↔ haltBit l q = true := by
  have hd : (l.drop q)[0]? = l[q]? := by simp
  unfold haltBit
  rcases h : l.drop q with _ | ⟨x, xs⟩
  · rw [h] at hd
    have : l[q]? = none := by simpa using hd.symm
    simp [List.getD_eq_getElem?_getD, this]
  · rw [h] at hd
    have hx : l[q]? = some x := by simpa using hd.symm
    simp [List.getD_eq_getElem?_getD, hx]

/-- `SKP := ¬ (the source state halts)`. -/
def haltBlk : Cmd :=
  Cmd.op (.copy EE S1Parse.PHALT) ;;
  dropLoop TJ1 SKQ EE ;;
  Cmd.op (.head CX EE) ;;
  Cmd.op (.clear TJ2) ;; Cmd.op (.appendOne TJ2) ;;
  Cmd.op (.eqBit TJ3 CX TJ2) ;;
  Cmd.ifBit TJ3 (Cmd.op (.clear SKP)) (setTrue SKP)

theorem haltBlk_run (hb : List Nat) (q : Nat) (w : State)
    (hph : State.get w S1Parse.PHALT = hb)
    (hq : State.get w SKQ = List.replicate q 1) :
    State.get (haltBlk.eval w) SKP = flagRep (!haltBit hb q)
    ∧ Keeps haltBlk w := by
  -- `EE := PHALT`
  set u1 := (Cmd.op (.copy EE S1Parse.PHALT)).eval w with hu1
  have u1E : State.get u1 EE = hb := by
    rw [hu1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; exact hph
  have u1Fr : ∀ r : Var, r ≠ EE → State.get u1 r = State.get w r := by
    intro r hr; rw [hu1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u1
  -- drain `q` cells
  obtain ⟨u2E, u2Fr⟩ := dropLoop_run TJ1 SKQ EE q hb u1 (by decide)
    (by rw [u1Fr SKQ (by decide)]; exact hq) u1E
  set u2 := (dropLoop TJ1 SKQ EE).eval u1 with hu2
  clear_value u2
  -- head, the literal `[1]`, and the comparison
  set u3 := (Cmd.op (.head CX EE)).eval u2 with hu3
  have u3X : State.get u3 CX
      = (match State.get u2 EE with | [] => ([] : List Nat) | x :: _ => [x]) := by
    rw [hu3, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]
  have u3Fr : ∀ r : Var, r ≠ CX → State.get u3 r = State.get u2 r := by
    intro r hr; rw [hu3, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u3
  set u4 := (Cmd.op (.appendOne TJ2)).eval ((Cmd.op (.clear TJ2)).eval u3) with hu4
  have u4J : State.get u4 TJ2 = [1] := by
    rw [hu4, Cmd.eval_op, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq]
  have u4Fr : ∀ r : Var, r ≠ TJ2 → State.get u4 r = State.get u3 r := by
    intro r hr
    rw [hu4, Cmd.eval_op, Cmd.eval_op, State.get_set_ne _ _ _ _ hr,
      State.get_set_ne _ _ _ _ hr]
  clear_value u4
  set u5 := (Cmd.op (.eqBit TJ3 CX TJ2)).eval u4 with hu5
  have u5J : State.get u5 TJ3 = if State.get u4 CX = State.get u4 TJ2 then [1] else [0] := by
    rw [hu5, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]
  have u5Fr : ∀ r : Var, r ≠ TJ3 → State.get u5 r = State.get u4 r := by
    intro r hr; rw [hu5, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u5
  have hCX : State.get u4 CX
      = (match hb.drop q with | [] => ([] : List Nat) | x :: _ => [x]) := by
    rw [u4Fr CX (by decide), u3X, u2E]
  have hev : haltBlk.eval w
      = (Cmd.ifBit TJ3 (Cmd.op (.clear SKP)) (setTrue SKP)).eval u5 := by
    rw [hu5, hu4, hu3, hu2, hu1]
    unfold haltBlk
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq,
      Cmd.eval_seq]
  -- the frame, shared by both branches
  have baseFr : ∀ r : Var, r ∉ LD → State.get u5 r = State.get w r := by
    intro r hr
    rw [u5Fr r (ne_of_nmem hr (by decide)), u4Fr r (ne_of_nmem hr (by decide)),
      u3Fr r (ne_of_nmem hr (by decide)),
      u2Fr r (ne_of_nmem hr (by decide)) (ne_of_nmem hr (by decide)),
      u1Fr r (ne_of_nmem hr (by decide))]
  by_cases hh : haltBit hb q = true
  · have ht : State.get u5 TJ3 = [1] := by
      rw [u5J, hCX, u4J, if_pos ((head_drop_iff hb q).2 hh)]
    refine ⟨?_, fun r hr => ?_⟩
    · rw [hev, Cmd.eval_ifBit_true _ _ _ _ ht, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, hh]
      rfl
    · rw [hev, Cmd.eval_ifBit_true _ _ _ _ ht, Cmd.eval_op,
        State.get_set_ne _ _ _ _ (ne_of_nmem hr (by decide : SKP ∈ LD))]
      exact baseFr r hr
  · have ht : State.get u5 TJ3 ≠ [1] := by
      rw [u5J, hCX, u4J, if_neg (fun hc => hh ((head_drop_iff hb q).1 hc))]
      exact fun hc => by cases hc
    have hf : haltBit hb q = false := by
      cases hb' : haltBit hb q
      · rfl
      · exact absurd hb' hh
    refine ⟨?_, fun r hr => ?_⟩
    · rw [hev, Cmd.eval_ifBit_false _ _ _ _ ht, setTrue_get, hf]
      rfl
    · rw [hev, Cmd.eval_ifBit_false _ _ _ _ ht,
        setTrue_frame _ _ _ (ne_of_nmem hr (by decide : SKP ∈ LD))]
      exact baseFr r hr

/-! ## The option reader

One `encOptN` group off the cursor into `(SKT, SKV) = (1^(oTag o), 1^(oVal o))`.
This is the only variable-arity step of the entry parse. -/

def optRead : Cmd :=
  S1Parse.readItem SKT SCUR SIX ;;
  Cmd.op (.nonEmpty SAX SKT) ;;
  Cmd.ifBit SAX (S1Parse.readItem SKV SCUR SIX) (Cmd.op (.clear SKV))

theorem optRead_run (o : Option Nat) (rest : List Nat) (w : State)
    (hcur : State.get w SCUR = encSyms (encOptN o ++ rest)) :
    State.get (optRead.eval w) SKT = List.replicate (oTag o) 1
    ∧ State.get (optRead.eval w) SKV = List.replicate (oVal o) 1
    ∧ State.get (optRead.eval w) SCUR = encSyms rest := by
  have hev : optRead.eval w
      = (Cmd.ifBit SAX (S1Parse.readItem SKV SCUR SIX) (Cmd.op (.clear SKV))).eval
          ((Cmd.op (.nonEmpty SAX SKT)).eval ((S1Parse.readItem SKT SCUR SIX).eval w)) := by
    unfold optRead; rw [Cmd.eval_seq, Cmd.eval_seq]
  cases o with
  | none =>
      obtain ⟨hT, hC⟩ := S1Parse.readItem_run w 0 rest SKT SCUR SIX (by decide) hcur
      set u1 := (S1Parse.readItem SKT SCUR SIX).eval w with hu1
      clear_value u1
      set u2 := (Cmd.op (.nonEmpty SAX SKT)).eval u1 with hu2
      have u2A : State.get u2 SAX ≠ [1] := by
        rw [hu2, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq, hT]
        decide
      have u2Fr : ∀ r : Var, r ≠ SAX → State.get u2 r = State.get u1 r := by
        intro r hr; rw [hu2, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
      clear_value u2
      rw [hev, ← hu1, ← hu2, Cmd.eval_ifBit_false _ _ _ _ u2A, Cmd.eval_op]
      refine ⟨?_, ?_, ?_⟩
      · rw [State.get_set_ne _ _ _ _ (by decide : (SKT : Var) ≠ SKV),
          u2Fr SKT (by decide)]
        exact hT
      · simp only [Op.eval, State.get_set_eq]; rfl
      · rw [State.get_set_ne _ _ _ _ (by decide : (SCUR : Var) ≠ SKV),
          u2Fr SCUR (by decide)]
        exact hC
  | some v =>
      have hcur' : State.get w SCUR = encSyms (1 :: (v :: rest)) := hcur
      obtain ⟨hT, hC⟩ := S1Parse.readItem_run w 1 (v :: rest) SKT SCUR SIX (by decide) hcur'
      set u1 := (S1Parse.readItem SKT SCUR SIX).eval w with hu1
      clear_value u1
      set u2 := (Cmd.op (.nonEmpty SAX SKT)).eval u1 with hu2
      have u2A : State.get u2 SAX = [1] := by
        rw [hu2, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq, hT]
        rfl
      have u2Fr : ∀ r : Var, r ≠ SAX → State.get u2 r = State.get u1 r := by
        intro r hr; rw [hu2, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
      clear_value u2
      have u2C : State.get u2 SCUR = encSyms (v :: rest) := by
        rw [u2Fr SCUR (by decide)]; exact hC
      obtain ⟨hV2, hC2⟩ := S1Parse.readItem_run u2 v rest SKV SCUR SIX (by decide) u2C
      rw [hev, ← hu1, ← hu2, Cmd.eval_ifBit_true _ _ _ _ u2A]
      refine ⟨?_, hV2, hC2⟩
      rw [Cmd.eval_get_of_not_writes _ _ SKT (by decide), u2Fr SKT (by decide)]
      exact hT

/-! ## The two head-cell bases

`hv σ (min q states) 0 = (σ+1)(min q states + 1)`: one `minReg` (no comparison
gadget) and one hoisted `unaryMulLoop`, exactly `S1Prelude.pMulBlk`'s shape. -/

def hvBlk (src dst : Var) : Cmd :=
  Cmd.op (.copy TJ3 S1Parse.PSTATES) ;;
  minReg TJ1 TJ2 src TJ3 EE ;;
  Cmd.op (.appendOne EE) ;;
  Cmd.op (.copy CX CS1) ;;
  Cmd.op (.clear dst) ;;
  Cmd.forBnd TJ1 EE (Cmd.op (.concat dst dst CX))

theorem hvBlk_run (src dst : Var) (sg st v : Nat) (w : State)
    (hsrc : State.get w src = List.replicate v 1)
    (hs1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hst : State.get w S1Parse.PSTATES = List.replicate st 1)
    (h1 : src ≠ TJ3) (h2 : src ≠ EE) (h3 : dst ≠ TJ1) (h4 : dst ≠ CX) :
    State.get ((hvBlk src dst).eval w) dst = List.replicate (hv sg (min v st) 0) 1 := by
  -- the drain
  set u1 := (Cmd.op (.copy TJ3 S1Parse.PSTATES)).eval w with hu1
  have u1D : State.get u1 TJ3 = List.replicate st 1 := by
    rw [hu1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; exact hst
  have u1Fr : ∀ r : Var, r ≠ TJ3 → State.get u1 r = State.get w r := by
    intro r hr; rw [hu1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u1
  -- the min
  obtain ⟨u2E, u2Fr⟩ := minReg_run TJ1 TJ2 src TJ3 EE v st u1
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [u1Fr src h1]; exact hsrc) u1D (Ne.symm h2)
  set u2 := (minReg TJ1 TJ2 src TJ3 EE).eval u1 with hu2
  clear_value u2
  -- `+1`, then the chunk
  set u3 := (Cmd.op (.appendOne EE)).eval u2 with hu3
  have u3E : State.get u3 EE = List.replicate (min v st + 1) 1 := by
    rw [hu3, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, u2E, ← List.replicate_succ']
  have u3Fr : ∀ r : Var, r ≠ EE → State.get u3 r = State.get u2 r := by
    intro r hr; rw [hu3, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u3
  set u4 := (Cmd.op (.copy CX CS1)).eval u3 with hu4
  have u4X : State.get u4 CX = List.replicate (sg + 1) 1 := by
    rw [hu4, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq]
    rw [u3Fr CS1 (by decide), u2Fr CS1 (by decide) (by decide) (by decide) (by decide),
      u1Fr CS1 (by decide)]
    exact hs1
  have u4Fr : ∀ r : Var, r ≠ CX → State.get u4 r = State.get u3 r := by
    intro r hr; rw [hu4, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u4
  set u5 := (Cmd.op (.clear dst)).eval u4 with hu5
  have u5D : State.get u5 dst = [] := by
    rw [hu5, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]
  have u5Fr : ∀ r : Var, r ≠ dst → State.get u5 r = State.get u4 r := by
    intro r hr; rw [hu5, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u5
  -- the product
  have h5X : State.get u5 CX = List.replicate (sg + 1) 1 := by
    rw [u5Fr CX (Ne.symm h4)]; exact u4X
  have h5E : (State.get u5 EE).length = min v st + 1 := by
    rw [u5Fr EE (by
        intro he; exact h4 (by rw [he] at *; exact absurd rfl (by decide : (EE : Var) ≠ CX))),
      u4Fr EE (by decide), u3E, List.length_replicate]
  obtain ⟨mO, -⟩ := BinaryCCFSATFree.unaryMulLoop_run TJ1 EE CX dst u5
    (sg + 1) (min v st + 1) (Ne.symm h4) (Ne.symm h3) (by decide) h5X h5E u5D
  have hev : (hvBlk src dst).eval w
      = (Cmd.forBnd TJ1 EE (Cmd.op (.concat dst dst CX))).eval u5 := by
    rw [hu5, hu4, hu3, hu2, hu1]
    unfold hvBlk
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  rw [hev, mO]
  congr 1
  show (min v st + 1) * (sg + 1) = (sg + 1) * (min v st + 1) + 0
  omega

/-! ## The three symbol constants

`rOf`/`wOf` are the same gadget with a different "the tag is `0`" fallback
source, so one register-generic `optMin` serves `TR` and `TW0`; `TW1` adds the
`mTag = 0` test that `wOf`'s `xb = true` case makes (`SKQ` carries it). -/

def optMin (dst zsrc : Var) : Cmd :=
  Cmd.op (.nonEmpty SAX SKT) ;;
  Cmd.ifBit SAX
    (Cmd.op (.copy TJ3 S1Parse.PSIG) ;; minReg TJ1 TJ2 SKV TJ3 dst)
    (Cmd.op (.copy dst zsrc))

theorem optMin_run (dst zsrc : Var) (sg tg vl z : Nat) (w : State)
    (hT : State.get w SKT = List.replicate tg 1)
    (hV : State.get w SKV = List.replicate vl 1)
    (hsig : State.get w S1Parse.PSIG = List.replicate sg 1)
    (hz : State.get w zsrc = List.replicate z 1)
    (h1 : dst ≠ TJ1) (h2 : dst ≠ TJ2) (h3 : dst ≠ TJ3) (h4 : zsrc ≠ dst) :
    State.get ((optMin dst zsrc).eval w) dst
      = List.replicate (if tg = 0 then z else min vl sg) 1 := by
  set u1 := (Cmd.op (.nonEmpty SAX SKT)).eval w with hu1
  have u1A : State.get u1 SAX = if (List.replicate tg 1 : List Nat).isEmpty then [0] else [1] := by
    rw [hu1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, hT]
  have u1Fr : ∀ r : Var, r ≠ SAX → State.get u1 r = State.get w r := by
    intro r hr; rw [hu1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u1
  have hev : (optMin dst zsrc).eval w
      = (Cmd.ifBit SAX (Cmd.op (.copy TJ3 S1Parse.PSIG) ;; minReg TJ1 TJ2 SKV TJ3 dst)
          (Cmd.op (.copy dst zsrc))).eval u1 := by
    rw [hu1]; unfold optMin; rw [Cmd.eval_seq]
  cases tg with
  | zero =>
      have hfa : State.get u1 SAX ≠ [1] := by rw [u1A]; decide
      rw [hev, Cmd.eval_ifBit_false _ _ _ _ hfa, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, if_pos rfl]
      rw [State.get_set_ne _ _ _ _ h4, u1Fr zsrc (by
        intro he; rw [he] at hz; rw [u1A] at hfa; exact hfa (by simp)), hz]
  | succ n =>
      have htr : State.get u1 SAX = [1] := by rw [u1A]; simp
      rw [hev, Cmd.eval_ifBit_true _ _ _ _ htr, Cmd.eval_seq]
      set u2 := (Cmd.op (.copy TJ3 S1Parse.PSIG)).eval u1 with hu2
      have u2D : State.get u2 TJ3 = List.replicate sg 1 := by
        rw [hu2, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq]
        rw [u1Fr S1Parse.PSIG (by decide)]; exact hsig
      have u2V : State.get u2 SKV = List.replicate vl 1 := by
        rw [hu2, Cmd.eval_op, State.get_set_ne _ _ _ _ (by decide : (SKV : Var) ≠ TJ3),
          u1Fr SKV (by decide)]
        exact hV
      clear_value u2
      obtain ⟨mO, -⟩ := minReg_run TJ1 TJ2 SKV TJ3 dst vl sg u2
        h1 h2 h3 (by decide) (by decide) u2V u2D (by decide)
      rw [mO, if_neg (Nat.succ_ne_zero n)]

/-- `TW1` — `wOf`'s beyond-the-frontier case. `SKQ` carries "the read option's
tag is `0`". -/
def wBlk1 : Cmd :=
  Cmd.op (.nonEmpty SAX SKT) ;;
  Cmd.ifBit SAX
    (Cmd.ifBit SKQ (Cmd.op (.copy TW1 S1Parse.PSIG))
      (Cmd.op (.copy TJ3 S1Parse.PSIG) ;; minReg TJ1 TJ2 SKV TJ3 TW1))
    (Cmd.op (.copy TW1 TR))

theorem wBlk1_run (sg mt vl z : Nat) (mz : Bool) (w : State)
    (hT : State.get w SKT = List.replicate mt 1)
    (hV : State.get w SKV = List.replicate vl 1)
    (hsig : State.get w S1Parse.PSIG = List.replicate sg 1)
    (hQ : State.get w SKQ = flagRep mz)
    (hz : State.get w TR = List.replicate z 1) :
    State.get (wBlk1.eval w) TW1
      = List.replicate (if mt = 0 then z else if mz then sg else min vl sg) 1 := by
  set u1 := (Cmd.op (.nonEmpty SAX SKT)).eval w with hu1
  have u1A : State.get u1 SAX = if (List.replicate mt 1 : List Nat).isEmpty then [0] else [1] := by
    rw [hu1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, hT]
  have u1Fr : ∀ r : Var, r ≠ SAX → State.get u1 r = State.get w r := by
    intro r hr; rw [hu1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u1
  have hev : wBlk1.eval w
      = (Cmd.ifBit SAX
          (Cmd.ifBit SKQ (Cmd.op (.copy TW1 S1Parse.PSIG))
            (Cmd.op (.copy TJ3 S1Parse.PSIG) ;; minReg TJ1 TJ2 SKV TJ3 TW1))
          (Cmd.op (.copy TW1 TR))).eval u1 := by
    rw [hu1]; unfold wBlk1; rw [Cmd.eval_seq]
  cases mt with
  | zero =>
      have hfa : State.get u1 SAX ≠ [1] := by rw [u1A]; decide
      rw [hev, Cmd.eval_ifBit_false _ _ _ _ hfa, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, if_pos rfl]
      rw [u1Fr TR (by decide)]; exact hz
  | succ n =>
      have htr : State.get u1 SAX = [1] := by rw [u1A]; simp
      rw [hev, Cmd.eval_ifBit_true _ _ _ _ htr, if_neg (Nat.succ_ne_zero n)]
      cases mz with
      | true =>
          have hq : State.get u1 SKQ = [1] := by rw [u1Fr SKQ (by decide), hQ]; rfl
          rw [Cmd.eval_ifBit_true _ _ _ _ hq, Cmd.eval_op]
          simp only [Op.eval, State.get_set_eq, if_pos rfl]
          rw [u1Fr S1Parse.PSIG (by decide)]; exact hsig
      | false =>
          have hq : State.get u1 SKQ ≠ [1] := by
            rw [u1Fr SKQ (by decide), hQ]; exact fun h => by cases h
          rw [Cmd.eval_ifBit_false _ _ _ _ hq, Cmd.eval_seq]
          set u2 := (Cmd.op (.copy TJ3 S1Parse.PSIG)).eval u1 with hu2
          have u2D : State.get u2 TJ3 = List.replicate sg 1 := by
            rw [hu2, Cmd.eval_op]
            simp only [Op.eval, State.get_set_eq]
            rw [u1Fr S1Parse.PSIG (by decide)]; exact hsig
          have u2V : State.get u2 SKV = List.replicate vl 1 := by
            rw [hu2, Cmd.eval_op, State.get_set_ne _ _ _ _ (by decide : (SKV : Var) ≠ TJ3),
              u1Fr SKV (by decide)]
            exact hV
          clear_value u2
          obtain ⟨mO, -⟩ := minReg_run TJ1 TJ2 SKV TJ3 TW1 vl sg u2
            (by decide) (by decide) (by decide) (by decide) (by decide) u2V u2D (by decide)
          rw [mO]
          rfl

/-- `SKQ := (the read option's tag is `0`)` — the one bit of the source option
that survives past the key push. -/
def mzBlk : Cmd :=
  Cmd.op (.nonEmpty SAX SKT) ;;
  Cmd.ifBit SAX (Cmd.op (.clear SKQ)) (setTrue SKQ)

theorem mzBlk_run (tg : Nat) (w : State)
    (hT : State.get w SKT = List.replicate tg 1) :
    State.get (mzBlk.eval w) SKQ = flagRep (decide (tg = 0)) := by
  set u1 := (Cmd.op (.nonEmpty SAX SKT)).eval w with hu1
  have u1A : State.get u1 SAX = if (List.replicate tg 1 : List Nat).isEmpty then [0] else [1] := by
    rw [hu1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, hT]
  clear_value u1
  have hev : mzBlk.eval w
      = (Cmd.ifBit SAX (Cmd.op (.clear SKQ)) (setTrue SKQ)).eval u1 := by
    rw [hu1]; unfold mzBlk; rw [Cmd.eval_seq]
  cases tg with
  | zero =>
      have hfa : State.get u1 SAX ≠ [1] := by rw [u1A]; decide
      rw [hev, Cmd.eval_ifBit_false _ _ _ _ hfa, setTrue_get]
      rfl
  | succ n =>
      have htr : State.get u1 SAX = [1] := by rw [u1A]; simp
      rw [hev, Cmd.eval_ifBit_true _ _ _ _ htr, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq]
      rw [if_neg (Nat.succ_ne_zero n)]
      rfl

/-- The two move flags off `SAX = 1^mv`. `mv ≥ 2` is one `tail` + `nonEmpty`;
`mv = 1` is `mv ≥ 1` under `¬ (mv ≥ 2)`. -/
def mvBlk : Cmd :=
  Cmd.op (.tail EE SAX) ;;
  Cmd.op (.nonEmpty CX EE) ;;
  Cmd.ifBit CX (setTrue TFN) (Cmd.op (.clear TFN)) ;;
  Cmd.ifBit CX (Cmd.op (.clear TFR))
    (Cmd.op (.nonEmpty CX SAX) ;; Cmd.ifBit CX (setTrue TFR) (Cmd.op (.clear TFR)))

theorem mvBlk_run (mv : Nat) (w : State) (hmv : mv = 0 ∨ mv = 1 ∨ mv = 2)
    (hA : State.get w SAX = List.replicate mv 1) :
    State.get (mvBlk.eval w) TFN = flagRep (decide (mv = 2))
    ∧ State.get (mvBlk.eval w) TFR = flagRep (decide (mv = 1)) := by
  set u1 := (Cmd.op (.nonEmpty CX EE)).eval ((Cmd.op (.tail EE SAX)).eval w) with hu1
  have u1X : State.get u1 CX
      = if (List.replicate mv 1 : List Nat).tail.isEmpty then [0] else [1] := by
    rw [hu1, Cmd.eval_op, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, hA]
  have u1A : State.get u1 SAX = List.replicate mv 1 := by
    rw [hu1, Cmd.eval_op, Cmd.eval_op, State.get_set_ne _ _ _ _ (by decide : (SAX : Var) ≠ CX),
      State.get_set_ne _ _ _ _ (by decide : (SAX : Var) ≠ EE)]
    exact hA
  clear_value u1
  have hev : mvBlk.eval w
      = (Cmd.ifBit CX (Cmd.op (.clear TFR))
          (Cmd.op (.nonEmpty CX SAX) ;; Cmd.ifBit CX (setTrue TFR) (Cmd.op (.clear TFR)))).eval
        ((Cmd.ifBit CX (setTrue TFN) (Cmd.op (.clear TFN))).eval u1) := by
    rw [hu1]; unfold mvBlk; rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  rcases hmv with rfl | rfl | rfl
  · -- mv = 0
    have hx : State.get u1 CX ≠ [1] := by rw [u1X]; decide
    set v1 := (Cmd.op (.clear TFN)).eval u1 with hv1
    have v1X : State.get v1 CX ≠ [1] := by
      rw [hv1, Cmd.eval_op, State.get_set_ne _ _ _ _ (by decide : (CX : Var) ≠ TFN)]; exact hx
    have v1A : State.get v1 SAX = [] := by
      rw [hv1, Cmd.eval_op, State.get_set_ne _ _ _ _ (by decide : (SAX : Var) ≠ TFN)]
      exact u1A
    clear_value v1
    rw [hev, Cmd.eval_ifBit_false _ _ _ _ hx, ← hv1, Cmd.eval_ifBit_false _ _ _ _ v1X,
      Cmd.eval_seq]
    set v2 := (Cmd.op (.nonEmpty CX SAX)).eval v1 with hv2
    have v2X : State.get v2 CX ≠ [1] := by
      rw [hv2, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, v1A]; decide
    clear_value v2
    rw [Cmd.eval_ifBit_false _ _ _ _ v2X, Cmd.eval_op]
    refine ⟨?_, ?_⟩
    · rw [State.get_set_ne _ _ _ _ (by decide : (TFN : Var) ≠ TFR), hv2, Cmd.eval_op,
        State.get_set_ne _ _ _ _ (by decide : (TFN : Var) ≠ CX), hv1, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq]
      rfl
    · simp only [Op.eval, State.get_set_eq]; rfl
  · -- mv = 1
    have hx : State.get u1 CX ≠ [1] := by rw [u1X]; decide
    set v1 := (Cmd.op (.clear TFN)).eval u1 with hv1
    have v1X : State.get v1 CX ≠ [1] := by
      rw [hv1, Cmd.eval_op, State.get_set_ne _ _ _ _ (by decide : (CX : Var) ≠ TFN)]; exact hx
    have v1A : State.get v1 SAX = [1] := by
      rw [hv1, Cmd.eval_op, State.get_set_ne _ _ _ _ (by decide : (SAX : Var) ≠ TFN)]
      exact u1A
    have v1N : State.get v1 TFN = [] := by
      rw [hv1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]
    clear_value v1
    rw [hev, Cmd.eval_ifBit_false _ _ _ _ hx, ← hv1, Cmd.eval_ifBit_false _ _ _ _ v1X,
      Cmd.eval_seq]
    set v2 := (Cmd.op (.nonEmpty CX SAX)).eval v1 with hv2
    have v2X : State.get v2 CX = [1] := by
      rw [hv2, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, v1A]; rfl
    have v2N : State.get v2 TFN = [] := by
      rw [hv2, Cmd.eval_op, State.get_set_ne _ _ _ _ (by decide : (TFN : Var) ≠ CX)]
      exact v1N
    clear_value v2
    rw [Cmd.eval_ifBit_true _ _ _ _ v2X]
    exact ⟨by rw [setTrue_frame _ _ _ (by decide : (TFN : Var) ≠ TFR)]; exact v2N,
      by rw [setTrue_get]; rfl⟩
  · -- mv = 2
    have hx : State.get u1 CX = [1] := by rw [u1X]; rfl
    rw [hev, Cmd.eval_ifBit_true _ _ _ _ hx]
    set v1 := (setTrue TFN).eval u1 with hv1
    have v1X : State.get v1 CX = [1] := by
      rw [hv1, setTrue_frame _ _ _ (by decide : (CX : Var) ≠ TFN)]; exact hx
    have v1N : State.get v1 TFN = [1] := by rw [hv1, setTrue_get]; rfl
    clear_value v1
    rw [Cmd.eval_ifBit_true _ _ _ _ v1X, Cmd.eval_op]
    refine ⟨?_, ?_⟩
    · rw [State.get_set_ne _ _ _ _ (by decide : (TFN : Var) ≠ TFR)]; exact v1N
    · simp only [Op.eval, State.get_set_eq]; rfl

/-! ## The membership scan

A cursor loop over the seen register (FINDING R again: index-driven principles
do not fit). `scanBody` is guarded on its own cursor (FINDING T), so the bound
only has to be an **upper** bound on `|seen|` — and `SSEEN` itself is one
(FINDING V), which is what makes the scan fit the exhausted register licence. -/

/-- The layer's no-op *inside* `LD` (`snop` writes `EOUT_C`, which is outside
it). -/
def lnop : Cmd := Cmd.op (.copy CX CX)

theorem lnop_get (r : Var) (w : State) : State.get (lnop.eval w) r = State.get w r :=
  copy_self_get CX r w

/-- "Is `key` among `ks`?" — `stepOut`'s test, verbatim. -/
def seenHit (key : Nat × Nat × Nat) (ks : List (Nat × Nat × Nat)) : Bool :=
  ks.any (fun k => decide (k = key))

theorem seenHit_snoc (key k : Nat × Nat × Nat) (l : List (Nat × Nat × Nat)) :
    seenHit key (l ++ [k]) = (seenHit key l || decide (k = key)) := by
  simp [seenHit]

private theorem take_succ_nil {α : Type} (l : List α) (j : Nat) (h : l.drop j = []) :
    l.take (j + 1) = l.take j := by
  have hl : l.length ≤ j := List.drop_eq_nil_iff.mp h
  rw [List.take_of_length_le (by omega), List.take_of_length_le hl]

private theorem take_succ_cons {α : Type} (l : List α) (j : Nat) (k : α) (ks : List α)
    (h : l.drop j = k :: ks) : l.take (j + 1) = l.take j ++ [k] := by
  have hj : j < l.length := by
    by_contra hc
    rw [List.drop_eq_nil_iff.mpr (by omega)] at h
    cases h
  have hk : l[j] = k := by
    have hd := List.drop_eq_getElem_cons hj
    rw [hd] at h
    exact (List.cons_eq_cons.mp h).1
  rw [List.take_add_one, List.getElem?_eq_getElem hj, hk]
  rfl

def scanBody : Cmd :=
  Cmd.op (.nonEmpty CX EE) ;;
  Cmd.ifBit CX
    (S1Parse.readItem TJ1 EE SIX ;;
     S1Parse.readItem TJ2 EE SIX ;;
     S1Parse.readItem TJ3 EE SIX ;;
     Cmd.op (.eqBit CX SKQ TJ1) ;;
     Cmd.ifBit CX (Cmd.op (.eqBit CX SKT TJ2)) lnop ;;
     Cmd.ifBit CX (Cmd.op (.eqBit CX SKV TJ3)) lnop ;;
     Cmd.ifBit CX (Cmd.op (.clear SKP)) lnop)
    lnop

/-- The scan's carried invariant. -/
def SInv (key : Nat × Nat × Nat) (seen : List (Nat × Nat × Nat)) (b0 : Bool)
    (j : Nat) (t : State) : Prop :=
  State.get t EE = encSyms (keyFlat (seen.drop j))
  ∧ State.get t SKP = flagRep (b0 && !seenHit key (seen.take j))
  ∧ State.get t SKQ = List.replicate key.1 1
  ∧ State.get t SKT = List.replicate key.2.1 1
  ∧ State.get t SKV = List.replicate key.2.2 1

private theorem scanBody_step (key : Nat × Nat × Nat) (seen : List (Nat × Nat × Nat))
    (b0 : Bool) (j : Nat) (t : State) (h : SInv key seen b0 j t) :
    SInv key seen b0 (j + 1) (scanBody.eval (State.set t EK1 (List.replicate j 1))) := by
  obtain ⟨hE, hP, hQ, hT, hV⟩ := h
  set s0 := State.set t EK1 (List.replicate j 1) with hs0
  have s0Fr : ∀ r : Var, r ≠ EK1 → State.get s0 r = State.get t r := by
    intro r hr; rw [hs0]; exact State.get_set_ne _ _ _ _ hr
  clear_value s0
  have s0E : State.get s0 EE = encSyms (keyFlat (seen.drop j)) := by
    rw [s0Fr EE (by decide)]; exact hE
  have s0P : State.get s0 SKP = flagRep (b0 && !seenHit key (seen.take j)) := by
    rw [s0Fr SKP (by decide)]; exact hP
  have s0Q : State.get s0 SKQ = List.replicate key.1 1 := by
    rw [s0Fr SKQ (by decide)]; exact hQ
  have s0T : State.get s0 SKT = List.replicate key.2.1 1 := by
    rw [s0Fr SKT (by decide)]; exact hT
  have s0V : State.get s0 SKV = List.replicate key.2.2 1 := by
    rw [s0Fr SKV (by decide)]; exact hV
  set u1 := (Cmd.op (.nonEmpty CX EE)).eval s0 with hu1
  have u1X : State.get u1 CX
      = if (encSyms (keyFlat (seen.drop j))).isEmpty then [0] else [1] := by
    rw [hu1, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, s0E]
  have u1Fr : ∀ r : Var, r ≠ CX → State.get u1 r = State.get s0 r := by
    intro r hr; rw [hu1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u1
  have hev : scanBody.eval s0
      = (Cmd.ifBit CX
          (S1Parse.readItem TJ1 EE SIX ;;
           S1Parse.readItem TJ2 EE SIX ;;
           S1Parse.readItem TJ3 EE SIX ;;
           Cmd.op (.eqBit CX SKQ TJ1) ;;
           Cmd.ifBit CX (Cmd.op (.eqBit CX SKT TJ2)) lnop ;;
           Cmd.ifBit CX (Cmd.op (.eqBit CX SKV TJ3)) lnop ;;
           Cmd.ifBit CX (Cmd.op (.clear SKP)) lnop)
          lnop).eval u1 := by
    rw [hu1]; unfold scanBody; rw [Cmd.eval_seq]
  rcases hd : seen.drop j with _ | ⟨k, ks⟩
  · -- the cursor is exhausted: the guard makes the body a no-op
    have hx : State.get u1 CX ≠ [1] := by
      rw [u1X, hd]
      simp [keyFlat, encSyms]
    rw [hev, Cmd.eval_ifBit_false _ _ _ _ hx]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [lnop_get, u1Fr EE (by decide), s0E, ← List.tail_drop, hd]
      rfl
    · rw [lnop_get, u1Fr SKP (by decide), s0P, take_succ_nil seen j hd]
    · rw [lnop_get, u1Fr SKQ (by decide)]; exact s0Q
    · rw [lnop_get, u1Fr SKT (by decide)]; exact s0T
    · rw [lnop_get, u1Fr SKV (by decide)]; exact s0V
  · -- one key off the cursor
    have hstream : State.get u1 EE
        = encSyms (k.1 :: (k.2.1 :: (k.2.2 :: keyFlat ks))) := by
      rw [u1Fr EE (by decide), s0E, hd, keyFlat_cons]
      rfl
    have hx : State.get u1 CX = [1] := by
      rw [u1X, hd, keyFlat_cons]
      rw [show ([k.1, k.2.1, k.2.2] : List Nat) ++ keyFlat ks
          = k.1 :: (k.2.1 :: (k.2.2 :: keyFlat ks)) from rfl, S1Parse.encSyms_cons]
      simp [S1Parse.itemOf]
    rw [hev, Cmd.eval_ifBit_true _ _ _ _ hx, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq,
      Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
    -- the three reads
    obtain ⟨r1V, r1S⟩ := S1Parse.readItem_run u1 k.1 (k.2.1 :: (k.2.2 :: keyFlat ks))
      TJ1 EE SIX (by decide) hstream
    set a1 := (S1Parse.readItem TJ1 EE SIX).eval u1 with ha1
    clear_value a1
    obtain ⟨r2V, r2S⟩ := S1Parse.readItem_run a1 k.2.1 (k.2.2 :: keyFlat ks)
      TJ2 EE SIX (by decide) r1S
    set a2 := (S1Parse.readItem TJ2 EE SIX).eval a1 with ha2
    clear_value a2
    obtain ⟨r3V, r3S⟩ := S1Parse.readItem_run a2 k.2.2 (keyFlat ks)
      TJ3 EE SIX (by decide) r2S
    set a3 := (S1Parse.readItem TJ3 EE SIX).eval a2 with ha3
    clear_value a3
    -- the values that survive the three reads
    have a3Q : State.get a3 SKQ = List.replicate key.1 1 := by
      rw [ha3, Cmd.eval_get_of_not_writes _ _ SKQ (by decide),
        ha2, Cmd.eval_get_of_not_writes _ _ SKQ (by decide),
        ha1, Cmd.eval_get_of_not_writes _ _ SKQ (by decide), u1Fr SKQ (by decide)]
      exact s0Q
    have a3T : State.get a3 SKT = List.replicate key.2.1 1 := by
      rw [ha3, Cmd.eval_get_of_not_writes _ _ SKT (by decide),
        ha2, Cmd.eval_get_of_not_writes _ _ SKT (by decide),
        ha1, Cmd.eval_get_of_not_writes _ _ SKT (by decide), u1Fr SKT (by decide)]
      exact s0T
    have a3V : State.get a3 SKV = List.replicate key.2.2 1 := by
      rw [ha3, Cmd.eval_get_of_not_writes _ _ SKV (by decide),
        ha2, Cmd.eval_get_of_not_writes _ _ SKV (by decide),
        ha1, Cmd.eval_get_of_not_writes _ _ SKV (by decide), u1Fr SKV (by decide)]
      exact s0V
    have a3P : State.get a3 SKP = flagRep (b0 && !seenHit key (seen.take j)) := by
      rw [ha3, Cmd.eval_get_of_not_writes _ _ SKP (by decide),
        ha2, Cmd.eval_get_of_not_writes _ _ SKP (by decide),
        ha1, Cmd.eval_get_of_not_writes _ _ SKP (by decide), u1Fr SKP (by decide)]
      exact s0P
    have a3J1 : State.get a3 TJ1 = List.replicate k.1 1 := by
      rw [ha3, Cmd.eval_get_of_not_writes _ _ TJ1 (by decide),
        ha2, Cmd.eval_get_of_not_writes _ _ TJ1 (by decide)]
      exact r1V
    have a3J2 : State.get a3 TJ2 = List.replicate k.2.1 1 := by
      rw [ha3, Cmd.eval_get_of_not_writes _ _ TJ2 (by decide)]
      exact r2V
    -- the three comparisons, folded into one flag
    set b1 := (Cmd.op (.eqBit CX SKQ TJ1)).eval a3 with hb1
    have b1X : State.get b1 CX = if key.1 = k.1 then [1] else [0] := by
      rw [hb1, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, a3Q, a3J1]
      by_cases hc : key.1 = k.1
      · rw [if_pos hc, if_pos (by rw [hc])]
      · rw [if_neg hc, if_neg (fun he => hc (by
          have := congrArg List.length he
          simpa using this))]
    have b1Fr : ∀ r : Var, r ≠ CX → State.get b1 r = State.get a3 r := by
      intro r hr; rw [hb1, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
    clear_value b1
    set b2 := (Cmd.ifBit CX (Cmd.op (.eqBit CX SKT TJ2)) lnop).eval b1 with hb2
    have b2X : State.get b2 CX = if key.1 = k.1 ∧ key.2.1 = k.2.1 then [1] else [0] := by
      by_cases hc : key.1 = k.1
      · have ht : State.get b1 CX = [1] := by rw [b1X, if_pos hc]
        rw [hb2, Cmd.eval_ifBit_true _ _ _ _ ht, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq, b1Fr SKT (by decide), b1Fr TJ2 (by decide),
          a3T, a3J2]
        by_cases hc2 : key.2.1 = k.2.1
        · rw [if_pos (by rw [hc2]), if_pos ⟨hc, hc2⟩]
        · rw [if_neg (fun he => hc2 (by
            have := congrArg List.length he; simpa using this)),
            if_neg (fun hh => hc2 hh.2)]
      · have ht : State.get b1 CX ≠ [1] := by
          rw [b1X, if_neg hc]; exact fun h => by cases h
        rw [hb2, Cmd.eval_ifBit_false _ _ _ _ ht, lnop_get, b1X, if_neg hc,
          if_neg (fun hh => hc hh.1)]
    have b2Fr : ∀ r : Var, r ≠ CX → State.get b2 r = State.get b1 r := by
      intro r hr
      by_cases hc : State.get b1 CX = [1]
      · rw [hb2, Cmd.eval_ifBit_true _ _ _ _ hc, Cmd.eval_op]
        exact State.get_set_ne _ _ _ _ hr
      · rw [hb2, Cmd.eval_ifBit_false _ _ _ _ hc, lnop_get]
    clear_value b2
    have a3J3 : State.get a3 TJ3 = List.replicate k.2.2 1 := r3V
    set b3 := (Cmd.ifBit CX (Cmd.op (.eqBit CX SKV TJ3)) lnop).eval b2 with hb3
    have b3X : State.get b3 CX = if k = key then [1] else [0] := by
      have hkey : (k = key) ↔ (key.1 = k.1 ∧ key.2.1 = k.2.1 ∧ key.2.2 = k.2.2) := by
        obtain ⟨a, b, c⟩ := k; obtain ⟨x, y, z⟩ := key
        simp only [Prod.mk.injEq]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩
      by_cases hc : key.1 = k.1 ∧ key.2.1 = k.2.1
      · have ht : State.get b2 CX = [1] := by rw [b2X, if_pos hc]
        rw [hb3, Cmd.eval_ifBit_true _ _ _ _ ht, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq, b2Fr SKV (by decide), b1Fr SKV (by decide),
          b2Fr TJ3 (by decide), b1Fr TJ3 (by decide), a3V, a3J3]
        by_cases hc2 : key.2.2 = k.2.2
        · rw [if_pos (by rw [hc2]), if_pos (hkey.2 ⟨hc.1, hc.2, hc2⟩)]
        · rw [if_neg (fun he => hc2 (by
            have := congrArg List.length he; simpa using this)),
            if_neg (fun hh => hc2 (hkey.1 hh).2.2)]
      · have ht : State.get b2 CX ≠ [1] := by
          rw [b2X, if_neg hc]; exact fun h => by cases h
        rw [hb3, Cmd.eval_ifBit_false _ _ _ _ ht, lnop_get, b2X, if_neg hc,
          if_neg (fun hh => hc ⟨(hkey.1 hh).1, (hkey.1 hh).2.1⟩)]
    have b3Fr : ∀ r : Var, r ≠ CX → State.get b3 r = State.get b2 r := by
      intro r hr
      by_cases hc : State.get b2 CX = [1]
      · rw [hb3, Cmd.eval_ifBit_true _ _ _ _ hc, Cmd.eval_op]
        exact State.get_set_ne _ _ _ _ hr
      · rw [hb3, Cmd.eval_ifBit_false _ _ _ _ hc, lnop_get]
    clear_value b3
    have b3P : State.get b3 SKP = flagRep (b0 && !seenHit key (seen.take j)) := by
      rw [b3Fr SKP (by decide), b2Fr SKP (by decide), b1Fr SKP (by decide)]; exact a3P
    have b3E : State.get b3 EE = encSyms (keyFlat ks) := by
      rw [b3Fr EE (by decide), b2Fr EE (by decide), b1Fr EE (by decide)]; exact r3S
    have b3Q : State.get b3 SKQ = List.replicate key.1 1 := by
      rw [b3Fr SKQ (by decide), b2Fr SKQ (by decide), b1Fr SKQ (by decide)]; exact a3Q
    have b3T : State.get b3 SKT = List.replicate key.2.1 1 := by
      rw [b3Fr SKT (by decide), b2Fr SKT (by decide), b1Fr SKT (by decide)]; exact a3T
    have b3V : State.get b3 SKV = List.replicate key.2.2 1 := by
      rw [b3Fr SKV (by decide), b2Fr SKV (by decide), b1Fr SKV (by decide)]; exact a3V
    -- the update
    have hdrop : seen.drop (j + 1) = ks := by rw [← List.tail_drop, hd]; rfl
    have htake : seen.take (j + 1) = seen.take j ++ [k] := take_succ_cons seen j k ks hd
    by_cases hc : k = key
    · have ht : State.get b3 CX = [1] := by rw [b3X, if_pos hc]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [Cmd.eval_ifBit_true _ _ _ _ ht, Cmd.eval_op,
          State.get_set_ne _ _ _ _ (by decide : (EE : Var) ≠ SKP), hdrop]
        exact b3E
      · rw [Cmd.eval_ifBit_true _ _ _ _ ht, Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq, htake, seenHit_snoc, hc]
        simp [flagRep]
      · rw [Cmd.eval_ifBit_true _ _ _ _ ht, Cmd.eval_op,
          State.get_set_ne _ _ _ _ (by decide : (SKQ : Var) ≠ SKP)]
        exact b3Q
      · rw [Cmd.eval_ifBit_true _ _ _ _ ht, Cmd.eval_op,
          State.get_set_ne _ _ _ _ (by decide : (SKT : Var) ≠ SKP)]
        exact b3T
      · rw [Cmd.eval_ifBit_true _ _ _ _ ht, Cmd.eval_op,
          State.get_set_ne _ _ _ _ (by decide : (SKV : Var) ≠ SKP)]
        exact b3V
    · have ht : State.get b3 CX ≠ [1] := by
        rw [b3X, if_neg hc]; exact fun h => by cases h
      rw [Cmd.eval_ifBit_false _ _ _ _ ht]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [lnop_get, hdrop]; exact b3E
      · rw [lnop_get, htake, seenHit_snoc]
        simp only [hc, decide_false, Bool.or_false]
        exact b3P
      · rw [lnop_get]; exact b3Q
      · rw [lnop_get]; exact b3T
      · rw [lnop_get]; exact b3V

/-- **The membership scan.** -/
def scanSeen : Cmd := Cmd.op (.copy EE SSEEN) ;; Cmd.forBnd EK1 SSEEN scanBody

theorem scanSeen_run (key : Nat × Nat × Nat) (seen : List (Nat × Nat × Nat))
    (b0 : Bool) (w : State)
    (hS : State.get w SSEEN = encSyms (keyFlat seen))
    (hP : State.get w SKP = flagRep b0)
    (hQ : State.get w SKQ = List.replicate key.1 1)
    (hT : State.get w SKT = List.replicate key.2.1 1)
    (hV : State.get w SKV = List.replicate key.2.2 1) :
    State.get (scanSeen.eval w) SKP = flagRep (b0 && !seenHit key seen) := by
  set u := (Cmd.op (.copy EE SSEEN)).eval w with hu
  have uE : State.get u EE = encSyms (keyFlat seen) := by
    rw [hu, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; exact hS
  have uFr : ∀ r : Var, r ≠ EE → State.get u r = State.get w r := by
    intro r hr; rw [hu, Cmd.eval_op]; exact State.get_set_ne _ _ _ _ hr
  clear_value u
  have uS : State.get u SSEEN = encSyms (keyFlat seen) := by
    rw [uFr SSEEN (by decide)]; exact hS
  have h0 : SInv key seen b0 0 u :=
    ⟨by rw [uE, List.drop_zero],
     by rw [uFr SKP (by decide), hP, List.take_zero]; simp [seenHit],
     by rw [uFr SKQ (by decide)]; exact hQ,
     by rw [uFr SKT (by decide)]; exact hT,
     by rw [uFr SKV (by decide)]; exact hV⟩
  have key' := Cmd.foldlState_range_induct scanBody EK1
    (encSyms (keyFlat seen)).length u (SInv key seen b0) h0
    (fun i st _ hM => scanBody_step key seen b0 i st hM)
  have hev : scanSeen.eval w = (Cmd.forBnd EK1 SSEEN scanBody).eval u := by
    rw [hu]; unfold scanSeen; rw [Cmd.eval_seq]
  rw [hev, Cmd.eval_forBnd, uS]
  have hle : seen.length ≤ (encSyms (keyFlat seen)).length := keyFlat_len_le seen
  rw [key'.2.1, List.take_of_length_le hle]

/-! ## The key push (FINDING U — prepend, do not append) -/

def pushKey : Cmd :=
  Cmd.op (.clear SAX) ;; Cmd.op (.appendOne SAX) ;;
  Cmd.op (.concat SAX SAX SKQ) ;; Cmd.op (.appendZero SAX) ;;
  Cmd.op (.appendOne SAX) ;;
  Cmd.op (.concat SAX SAX SKT) ;; Cmd.op (.appendZero SAX) ;;
  Cmd.op (.appendOne SAX) ;;
  Cmd.op (.concat SAX SAX SKV) ;; Cmd.op (.appendZero SAX) ;;
  Cmd.op (.concat SSEEN SAX SSEEN)

theorem pushKey_run (key : Nat × Nat × Nat) (seen : List (Nat × Nat × Nat)) (w : State)
    (hS : State.get w SSEEN = encSyms (keyFlat seen))
    (hQ : State.get w SKQ = List.replicate key.1 1)
    (hT : State.get w SKT = List.replicate key.2.1 1)
    (hV : State.get w SKV = List.replicate key.2.2 1) :
    State.get (pushKey.eval w) SSEEN = encSyms (keyFlat (key :: seen)) := by
  have hitem : ∀ v : Nat, ([] ++ [1] ++ List.replicate v 1) ++ [0]
      = S1Parse.itemOf v := by
    intro v; simp [S1Parse.itemOf]
  unfold pushKey
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
    State.get_set_ne _ _ _ _ (by decide : (SKQ : Var) ≠ SAX),
    State.get_set_ne _ _ _ _ (by decide : (SKT : Var) ≠ SAX),
    State.get_set_ne _ _ _ _ (by decide : (SKV : Var) ≠ SAX),
    State.get_set_ne _ _ _ _ (by decide : (SSEEN : Var) ≠ SAX),
    hQ, hT, hV, hS]
  rw [keyFlat_cons,
    show ([key.1, key.2.1, key.2.2] : List Nat) ++ keyFlat seen
      = key.1 :: (key.2.1 :: (key.2.2 :: keyFlat seen)) from rfl,
    S1Parse.encSyms_cons, S1Parse.encSyms_cons, S1Parse.encSyms_cons]
  simp [S1Parse.itemOf]

/-! ## The per-entry preamble

Four phases. `SKP` carries the "emit this entry?" verdict from phase 1 (the halt
test) through phase 2 (the dedup test) to the end; `SKQ` is re-used after the
key push to carry the one bit of the source option that `wOf`'s
beyond-the-frontier case still needs. -/

/-- Phase 1 — the source state: its head-cell base and the halt test. -/
def preSrc : Cmd := S1Parse.readItem SKQ SCUR SIX ;; hvBlk SKQ TQ ;; haltBlk

theorem preSrc_run (sg st q : Nat) (hb : List Nat) (tl : List Nat) (w : State)
    (hcur : State.get w SCUR = encSyms (q :: tl))
    (hs1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hst : State.get w S1Parse.PSTATES = List.replicate st 1)
    (hph : State.get w S1Parse.PHALT = hb) :
    State.get (preSrc.eval w) SKQ = List.replicate q 1
    ∧ State.get (preSrc.eval w) SCUR = encSyms tl
    ∧ State.get (preSrc.eval w) TQ = List.replicate (hv sg (min q st) 0) 1
    ∧ State.get (preSrc.eval w) SKP = flagRep (!haltBit hb q) := by
  obtain ⟨hQ, hC⟩ := S1Parse.readItem_run w q tl SKQ SCUR SIX (by decide) hcur
  set s1 := (S1Parse.readItem SKQ SCUR SIX).eval w with hs1d
  have s1C : State.get s1 CS1 = List.replicate (sg + 1) 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ CS1 (by decide)]; exact hs1
  have s1S : State.get s1 S1Parse.PSTATES = List.replicate st 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSTATES (by decide)]; exact hst
  have s1P : State.get s1 S1Parse.PHALT = hb := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ S1Parse.PHALT (by decide)]; exact hph
  clear_value s1
  have hTQ := hvBlk_run SKQ TQ sg st q s1 hQ s1C s1S (by decide) (by decide)
    (by decide) (by decide)
  set s2 := (hvBlk SKQ TQ).eval s1 with hs2d
  have s2Q : State.get s2 SKQ = List.replicate q 1 := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ SKQ (by decide)]; exact hQ
  have s2C : State.get s2 SCUR = encSyms tl := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ SCUR (by decide)]; exact hC
  have s2P : State.get s2 S1Parse.PHALT = hb := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ S1Parse.PHALT (by decide)]; exact s1P
  clear_value s2
  obtain ⟨hKP, -⟩ := haltBlk_run hb q s2 s2P s2Q
  have hev : preSrc.eval w = haltBlk.eval s2 := by
    rw [hs2d, hs1d]; unfold preSrc; rw [Cmd.eval_seq, Cmd.eval_seq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hev, Cmd.eval_get_of_not_writes _ _ SKQ (by decide)]; exact s2Q
  · rw [hev, Cmd.eval_get_of_not_writes _ _ SCUR (by decide)]; exact s2C
  · rw [hev, Cmd.eval_get_of_not_writes _ _ TQ (by decide)]; exact hTQ
  · rw [hev]; exact hKP

/-- Phase 2 — the source option: the dedup decision, the key push, `TR`, and
the `mTag = 0` bit. -/
def preKey : Cmd :=
  S1Parse.readItem SAX SCUR SIX ;; optRead ;; scanSeen ;; pushKey ;;
  optMin TR S1Parse.PSIG ;; mzBlk

theorem preKey_run (sg q ar : Nat) (o : Option Nat) (b0 : Bool) (tl : List Nat)
    (seen : List (Nat × Nat × Nat)) (w : State)
    (hcur : State.get w SCUR = encSyms (ar :: (encOptN o ++ tl)))
    (hseen : State.get w SSEEN = encSyms (keyFlat seen))
    (hQ : State.get w SKQ = List.replicate q 1)
    (hP : State.get w SKP = flagRep b0)
    (hsig : State.get w S1Parse.PSIG = List.replicate sg 1) :
    State.get (preKey.eval w) SCUR = encSyms tl
    ∧ State.get (preKey.eval w) SSEEN
        = encSyms (keyFlat ((q, oTag o, oVal o) :: seen))
    ∧ State.get (preKey.eval w) SKP
        = flagRep (b0 && !seenHit (q, oTag o, oVal o) seen)
    ∧ State.get (preKey.eval w) TR = List.replicate (rOf sg (oTag o) (oVal o)) 1
    ∧ State.get (preKey.eval w) SKQ = flagRep (decide (oTag o = 0)) := by
  set key : Nat × Nat × Nat := (q, oTag o, oVal o) with hkey
  -- the arity item, discarded
  obtain ⟨-, hC1⟩ := S1Parse.readItem_run w ar (encOptN o ++ tl) SAX SCUR SIX
    (by decide) hcur
  set s1 := (S1Parse.readItem SAX SCUR SIX).eval w with hs1d
  have s1S : State.get s1 SSEEN = encSyms (keyFlat seen) := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ SSEEN (by decide)]; exact hseen
  have s1Q : State.get s1 SKQ = List.replicate q 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ SKQ (by decide)]; exact hQ
  have s1P : State.get s1 SKP = flagRep b0 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ SKP (by decide)]; exact hP
  have s1G : State.get s1 S1Parse.PSIG = List.replicate sg 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact hsig
  clear_value s1
  -- the option
  obtain ⟨hT2, hV2, hC2⟩ := optRead_run o tl s1 hC1
  set s2 := optRead.eval s1 with hs2d
  have s2S : State.get s2 SSEEN = encSyms (keyFlat seen) := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ SSEEN (by decide)]; exact s1S
  have s2Q : State.get s2 SKQ = List.replicate q 1 := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ SKQ (by decide)]; exact s1Q
  have s2P : State.get s2 SKP = flagRep b0 := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ SKP (by decide)]; exact s1P
  have s2G : State.get s2 S1Parse.PSIG = List.replicate sg 1 := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact s1G
  clear_value s2
  -- the scan
  have hscan := scanSeen_run key seen b0 s2 s2S s2P s2Q hT2 hV2
  set s3 := scanSeen.eval s2 with hs3d
  have s3S : State.get s3 SSEEN = encSyms (keyFlat seen) := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ SSEEN (by decide)]; exact s2S
  have s3Q : State.get s3 SKQ = List.replicate q 1 := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ SKQ (by decide)]; exact s2Q
  have s3T : State.get s3 SKT = List.replicate (oTag o) 1 := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ SKT (by decide)]; exact hT2
  have s3V : State.get s3 SKV = List.replicate (oVal o) 1 := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ SKV (by decide)]; exact hV2
  have s3C : State.get s3 SCUR = encSyms tl := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ SCUR (by decide)]; exact hC2
  have s3G : State.get s3 S1Parse.PSIG = List.replicate sg 1 := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact s2G
  clear_value s3
  -- the push
  have hpush := pushKey_run key seen s3 s3S s3Q s3T s3V
  set s4 := pushKey.eval s3 with hs4d
  have s4T : State.get s4 SKT = List.replicate (oTag o) 1 := by
    rw [hs4d, Cmd.eval_get_of_not_writes _ _ SKT (by decide)]; exact s3T
  have s4V : State.get s4 SKV = List.replicate (oVal o) 1 := by
    rw [hs4d, Cmd.eval_get_of_not_writes _ _ SKV (by decide)]; exact s3V
  have s4C : State.get s4 SCUR = encSyms tl := by
    rw [hs4d, Cmd.eval_get_of_not_writes _ _ SCUR (by decide)]; exact s3C
  have s4G : State.get s4 S1Parse.PSIG = List.replicate sg 1 := by
    rw [hs4d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact s3G
  have s4P : State.get s4 SKP = flagRep (b0 && !seenHit key seen) := by
    rw [hs4d, Cmd.eval_get_of_not_writes _ _ SKP (by decide)]; exact hscan
  clear_value s4
  -- `TR`
  have hTR := optMin_run TR S1Parse.PSIG sg (oTag o) (oVal o) sg s4 s4T s4V s4G s4G
    (by decide) (by decide) (by decide) (by decide)
  set s5 := (optMin TR S1Parse.PSIG).eval s4 with hs5d
  have s5T : State.get s5 SKT = List.replicate (oTag o) 1 := by
    rw [hs5d, Cmd.eval_get_of_not_writes _ _ SKT (by decide)]; exact s4T
  clear_value s5
  have hMZ := mzBlk_run (oTag o) s5 s5T
  have hev : preKey.eval w = mzBlk.eval s5 := by
    rw [hs5d, hs4d, hs3d, hs2d, hs1d]
    unfold preKey
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hev, Cmd.eval_get_of_not_writes _ _ SCUR (by decide), hs5d,
      Cmd.eval_get_of_not_writes _ _ SCUR (by decide)]
    exact s4C
  · rw [hev, Cmd.eval_get_of_not_writes _ _ SSEEN (by decide), hs5d,
      Cmd.eval_get_of_not_writes _ _ SSEEN (by decide)]
    exact hpush
  · rw [hev, Cmd.eval_get_of_not_writes _ _ SKP (by decide), hs5d,
      Cmd.eval_get_of_not_writes _ _ SKP (by decide)]
    exact s4P
  · rw [hev, Cmd.eval_get_of_not_writes _ _ TR (by decide), hTR]
    rfl
  · rw [hev]; exact hMZ

/-- Phase 3 — the destination state and the written option: `TQ2`, `TW0`,
`TW1`. -/
def preDst : Cmd :=
  S1Parse.readItem SAX SCUR SIX ;; hvBlk SAX TQ2 ;;
  S1Parse.readItem SAX SCUR SIX ;; optRead ;; optMin TW0 TR ;; wBlk1

theorem preDst_run (sg st q' ar rv : Nat) (mz : Bool) (o : Option Nat)
    (tl : List Nat) (w : State)
    (hcur : State.get w SCUR = encSyms (q' :: ar :: (encOptN o ++ tl)))
    (hs1 : State.get w CS1 = List.replicate (sg + 1) 1)
    (hst : State.get w S1Parse.PSTATES = List.replicate st 1)
    (hsig : State.get w S1Parse.PSIG = List.replicate sg 1)
    (hQ : State.get w SKQ = flagRep mz)
    (hTR : State.get w TR = List.replicate rv 1) :
    State.get (preDst.eval w) SCUR = encSyms tl
    ∧ State.get (preDst.eval w) TQ2 = List.replicate (hv sg (min q' st) 0) 1
    ∧ State.get (preDst.eval w) TW0
        = List.replicate (if oTag o = 0 then rv else min (oVal o) sg) 1
    ∧ State.get (preDst.eval w) TW1
        = List.replicate
            (if oTag o = 0 then rv else if mz then sg else min (oVal o) sg) 1 := by
  obtain ⟨hA1, hC1⟩ := S1Parse.readItem_run w q' (ar :: (encOptN o ++ tl))
    SAX SCUR SIX (by decide) hcur
  set s1 := (S1Parse.readItem SAX SCUR SIX).eval w with hs1d
  have s1C1 : State.get s1 CS1 = List.replicate (sg + 1) 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ CS1 (by decide)]; exact hs1
  have s1St : State.get s1 S1Parse.PSTATES = List.replicate st 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSTATES (by decide)]; exact hst
  have s1G : State.get s1 S1Parse.PSIG = List.replicate sg 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact hsig
  have s1Q : State.get s1 SKQ = flagRep mz := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ SKQ (by decide)]; exact hQ
  have s1R : State.get s1 TR = List.replicate rv 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ TR (by decide)]; exact hTR
  clear_value s1
  have hTQ2 := hvBlk_run SAX TQ2 sg st q' s1 hA1 s1C1 s1St (by decide) (by decide)
    (by decide) (by decide)
  set s2 := (hvBlk SAX TQ2).eval s1 with hs2d
  have s2C : State.get s2 SCUR = encSyms (ar :: (encOptN o ++ tl)) := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ SCUR (by decide)]; exact hC1
  have s2G : State.get s2 S1Parse.PSIG = List.replicate sg 1 := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact s1G
  have s2Q : State.get s2 SKQ = flagRep mz := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ SKQ (by decide)]; exact s1Q
  have s2R : State.get s2 TR = List.replicate rv 1 := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ TR (by decide)]; exact s1R
  clear_value s2
  obtain ⟨-, hC3⟩ := S1Parse.readItem_run s2 ar (encOptN o ++ tl) SAX SCUR SIX
    (by decide) s2C
  set s3 := (S1Parse.readItem SAX SCUR SIX).eval s2 with hs3d
  have s3G : State.get s3 S1Parse.PSIG = List.replicate sg 1 := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact s2G
  have s3Q : State.get s3 SKQ = flagRep mz := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ SKQ (by decide)]; exact s2Q
  have s3R : State.get s3 TR = List.replicate rv 1 := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ TR (by decide)]; exact s2R
  have s3T2 : State.get s3 TQ2 = List.replicate (hv sg (min q' st) 0) 1 := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ TQ2 (by decide)]; exact hTQ2
  clear_value s3
  obtain ⟨hT4, hV4, hC4⟩ := optRead_run o tl s3 hC3
  set s4 := optRead.eval s3 with hs4d
  have s4G : State.get s4 S1Parse.PSIG = List.replicate sg 1 := by
    rw [hs4d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact s3G
  have s4Q : State.get s4 SKQ = flagRep mz := by
    rw [hs4d, Cmd.eval_get_of_not_writes _ _ SKQ (by decide)]; exact s3Q
  have s4R : State.get s4 TR = List.replicate rv 1 := by
    rw [hs4d, Cmd.eval_get_of_not_writes _ _ TR (by decide)]; exact s3R
  have s4T2 : State.get s4 TQ2 = List.replicate (hv sg (min q' st) 0) 1 := by
    rw [hs4d, Cmd.eval_get_of_not_writes _ _ TQ2 (by decide)]; exact s3T2
  clear_value s4
  have hTW0 := optMin_run TW0 TR sg (oTag o) (oVal o) rv s4 hT4 hV4 s4G s4R
    (by decide) (by decide) (by decide) (by decide)
  set s5 := (optMin TW0 TR).eval s4 with hs5d
  have s5G : State.get s5 S1Parse.PSIG = List.replicate sg 1 := by
    rw [hs5d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact s4G
  have s5Q : State.get s5 SKQ = flagRep mz := by
    rw [hs5d, Cmd.eval_get_of_not_writes _ _ SKQ (by decide)]; exact s4Q
  have s5R : State.get s5 TR = List.replicate rv 1 := by
    rw [hs5d, Cmd.eval_get_of_not_writes _ _ TR (by decide)]; exact s4R
  have s5T : State.get s5 SKT = List.replicate (oTag o) 1 := by
    rw [hs5d, Cmd.eval_get_of_not_writes _ _ SKT (by decide)]; exact hT4
  have s5V : State.get s5 SKV = List.replicate (oVal o) 1 := by
    rw [hs5d, Cmd.eval_get_of_not_writes _ _ SKV (by decide)]; exact hV4
  have s5T2 : State.get s5 TQ2 = List.replicate (hv sg (min q' st) 0) 1 := by
    rw [hs5d, Cmd.eval_get_of_not_writes _ _ TQ2 (by decide)]; exact s4T2
  have s5C : State.get s5 SCUR = encSyms tl := by
    rw [hs5d, Cmd.eval_get_of_not_writes _ _ SCUR (by decide)]; exact hC4
  clear_value s5
  have hTW1 := wBlk1_run sg (oTag o) (oVal o) rv mz s5 s5T s5V s5G s5Q s5R
  have hev : preDst.eval w = wBlk1.eval s5 := by
    rw [hs5d, hs4d, hs3d, hs2d, hs1d]
    unfold preDst
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  refine ⟨?_, ?_, ?_, hev ▸ hTW1⟩
  · rw [hev, Cmd.eval_get_of_not_writes _ _ SCUR (by decide)]; exact s5C
  · rw [hev, Cmd.eval_get_of_not_writes _ _ TQ2 (by decide)]; exact s5T2
  · rw [hev, Cmd.eval_get_of_not_writes _ _ TW0 (by decide)]; exact hTW0

/-- Phase 4 — the move code. -/
def preMv : Cmd :=
  S1Parse.readItem SAX SCUR SIX ;; S1Parse.readItem SAX SCUR SIX ;; mvBlk

theorem preMv_run (ar mv : Nat) (tl : List Nat) (w : State)
    (hmv : mv = 0 ∨ mv = 1 ∨ mv = 2)
    (hcur : State.get w SCUR = encSyms (ar :: mv :: tl)) :
    State.get (preMv.eval w) SCUR = encSyms tl
    ∧ State.get (preMv.eval w) TFN = flagRep (decide (mv = 2))
    ∧ State.get (preMv.eval w) TFR = flagRep (decide (mv = 1)) := by
  obtain ⟨-, hC1⟩ := S1Parse.readItem_run w ar (mv :: tl) SAX SCUR SIX (by decide) hcur
  set s1 := (S1Parse.readItem SAX SCUR SIX).eval w with hs1d
  clear_value s1
  obtain ⟨hA2, hC2⟩ := S1Parse.readItem_run s1 mv tl SAX SCUR SIX (by decide) hC1
  set s2 := (S1Parse.readItem SAX SCUR SIX).eval s1 with hs2d
  clear_value s2
  obtain ⟨hN, hR⟩ := mvBlk_run mv s2 hmv hA2
  have hev : preMv.eval w = mvBlk.eval s2 := by
    rw [hs2d, hs1d]; unfold preMv; rw [Cmd.eval_seq, Cmd.eval_seq]
  exact ⟨by rw [hev, Cmd.eval_get_of_not_writes _ _ SCUR (by decide)]; exact hC2,
    hev ▸ hN, hev ▸ hR⟩

/-! ### The preamble -/

/-- One entry's stream, under the guard's three arity facts. -/
theorem flattenEntry_shape (e : FlatTMTransEntry) (rest : List Nat)
    (h1 : e.src_tape_vals.length = 1) (h2 : e.dst_write_vals.length = 1)
    (h3 : e.move_dirs.length = 1) :
    flattenEntry e ++ rest
      = e.src_state :: 1 :: (encOptN (e.src_tape_vals.headD none)
          ++ (e.dst_state :: 1 :: (encOptN (e.dst_write_vals.headD none)
            ++ (1 :: encMoveN (e.move_dirs.headD TMMove.Nmove) :: rest)))) := by
  obtain ⟨a, ha⟩ : ∃ a, e.src_tape_vals = [a] := List.length_eq_one_iff.mp h1
  obtain ⟨b, hb⟩ : ∃ b, e.dst_write_vals = [b] := List.length_eq_one_iff.mp h2
  obtain ⟨c, hc⟩ : ∃ c, e.move_dirs = [c] := List.length_eq_one_iff.mp h3
  rw [S1Parse.flattenEntry_eq, ha, hb, hc]
  simp [S1Parse.optsFlat]

theorem wOf_false_eq (sg mT mV wT wV : Nat) :
    wOf sg mT mV wT wV false = if wT = 0 then rOf sg mT mV else min wV sg := by
  unfold wOf; simp

theorem wOf_true_eq (sg mT mV wT wV : Nat) :
    wOf sg mT mV wT wV true
      = if wT = 0 then rOf sg mT mV else if decide (mT = 0) then sg else min wV sg := by
  unfold wOf
  by_cases hw : wT = 0
  · simp [hw]
  · by_cases hm : mT = 0 <;> simp [hw, hm]

/-- **The per-entry preamble.** -/
def entryPre : Cmd := preSrc ;; preKey ;; preDst ;; preMv

theorem entryPre_run (M : flatTM) (e : FlatTMTransEntry) (rest : List Nat)
    (seen : List (Nat × Nat × Nat)) (w : State)
    (h1 : e.src_tape_vals.length = 1) (h2 : e.dst_write_vals.length = 1)
    (h3 : e.move_dirs.length = 1)
    (hcur : State.get w SCUR = encSyms (flattenEntry e ++ rest))
    (hseen : State.get w SSEEN = encSyms (keyFlat seen))
    (hconst : SConst M.sig M.states w)
    (hst : State.get w S1Parse.PSTATES = List.replicate M.states 1)
    (hph : State.get w S1Parse.PHALT = M.halt.map S1Parse.bitOf) :
    SEntry M.sig (min e.src_state M.states) (min e.dst_state M.states)
        (oTag (e.src_tape_vals.headD none)) (oVal (e.src_tape_vals.headD none))
        (oTag (e.dst_write_vals.headD none)) (oVal (e.dst_write_vals.headD none))
        (encMoveN (e.move_dirs.headD TMMove.Nmove)) (entryPre.eval w)
    ∧ State.get (entryPre.eval w) SCUR = encSyms rest
    ∧ State.get (entryPre.eval w) SSEEN = encSyms (keyFlat (keyOf e :: seen))
    ∧ State.get (entryPre.eval w) SKP
        = flagRep (!(seenHit (keyOf e) seen
            || haltBit (M.halt.map S1Parse.bitOf) e.src_state)) := by
  obtain ⟨-, hCS1, -, -, hsig⟩ := hconst
  set o := e.src_tape_vals.headD none with hodef
  set p := e.dst_write_vals.headD none with hpdef
  set mv := encMoveN (e.move_dirs.headD TMMove.Nmove) with hmvdef
  have hmv : mv = 0 ∨ mv = 1 ∨ mv = 2 := by
    rw [hmvdef]; cases e.move_dirs.headD TMMove.Nmove <;> simp [encMoveN]
  have hcur' : State.get w SCUR
      = encSyms (e.src_state :: (1 :: (encOptN o
          ++ (e.dst_state :: 1 :: (encOptN p ++ (1 :: mv :: rest)))))) := by
    rw [hcur, flattenEntry_shape e rest h1 h2 h3]
  -- phase 1
  obtain ⟨p1Q, p1C, p1TQ, p1P⟩ := preSrc_run M.sig M.states e.src_state
    (M.halt.map S1Parse.bitOf) _ w hcur' hCS1 hst hph
  set s1 := preSrc.eval w with hs1d
  have s1S : State.get s1 SSEEN = encSyms (keyFlat seen) := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ SSEEN (by decide)]; exact hseen
  have s1G : State.get s1 S1Parse.PSIG = List.replicate M.sig 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact hsig
  have s1C1 : State.get s1 CS1 = List.replicate (M.sig + 1) 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ CS1 (by decide)]; exact hCS1
  have s1St : State.get s1 S1Parse.PSTATES = List.replicate M.states 1 := by
    rw [hs1d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSTATES (by decide)]; exact hst
  clear_value s1
  -- phase 2
  obtain ⟨p2C, p2S, p2P, p2R, p2Q⟩ := preKey_run M.sig e.src_state 1 o
    (!haltBit (M.halt.map S1Parse.bitOf) e.src_state) _ seen s1 p1C s1S p1Q p1P s1G
  set s2 := preKey.eval s1 with hs2d
  have s2G : State.get s2 S1Parse.PSIG = List.replicate M.sig 1 := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSIG (by decide)]; exact s1G
  have s2C1 : State.get s2 CS1 = List.replicate (M.sig + 1) 1 := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ CS1 (by decide)]; exact s1C1
  have s2St : State.get s2 S1Parse.PSTATES = List.replicate M.states 1 := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ S1Parse.PSTATES (by decide)]; exact s1St
  have s2TQ : State.get s2 TQ = List.replicate (hv M.sig (min e.src_state M.states) 0) 1 := by
    rw [hs2d, Cmd.eval_get_of_not_writes _ _ TQ (by decide)]; exact p1TQ
  clear_value s2
  -- phase 3
  obtain ⟨p3C, p3TQ2, p3W0, p3W1⟩ := preDst_run M.sig M.states e.dst_state 1
    (rOf M.sig (oTag o) (oVal o)) (decide (oTag o = 0)) p _ s2 p2C s2C1 s2St s2G p2Q p2R
  set s3 := preDst.eval s2 with hs3d
  have s3TQ : State.get s3 TQ = List.replicate (hv M.sig (min e.src_state M.states) 0) 1 := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ TQ (by decide)]; exact s2TQ
  have s3R : State.get s3 TR = List.replicate (rOf M.sig (oTag o) (oVal o)) 1 := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ TR (by decide)]; exact p2R
  have s3S : State.get s3 SSEEN = encSyms (keyFlat ((e.src_state, oTag o, oVal o) :: seen)) := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ SSEEN (by decide)]; exact p2S
  have s3P : State.get s3 SKP
      = flagRep ((!haltBit (M.halt.map S1Parse.bitOf) e.src_state)
          && !seenHit (e.src_state, oTag o, oVal o) seen) := by
    rw [hs3d, Cmd.eval_get_of_not_writes _ _ SKP (by decide)]; exact p2P
  clear_value s3
  -- phase 4
  obtain ⟨p4C, p4N, p4R⟩ := preMv_run 1 mv rest s3 hmv p3C
  have hev : entryPre.eval w = preMv.eval s3 := by
    rw [hs3d, hs2d, hs1d]; unfold entryPre; rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  have hkey : keyOf e = (e.src_state, oTag o, oVal o) := rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hev ▸ p4N, hev ▸ p4R⟩, ?_, ?_, ?_⟩
  · rw [hev, Cmd.eval_get_of_not_writes _ _ TQ (by decide)]; exact s3TQ
  · rw [hev, Cmd.eval_get_of_not_writes _ _ TQ2 (by decide)]; exact p3TQ2
  · rw [hev, Cmd.eval_get_of_not_writes _ _ TR (by decide)]; exact s3R
  · rw [hev, Cmd.eval_get_of_not_writes _ _ TW0 (by decide), p3W0, wOf_false_eq]
  · rw [hev, Cmd.eval_get_of_not_writes _ _ TW1 (by decide), p3W1, wOf_true_eq]
  · rw [hev]; exact p4C
  · rw [hev, Cmd.eval_get_of_not_writes _ _ SSEEN (by decide), hkey]; exact s3S
  · rw [hev, Cmd.eval_get_of_not_writes _ _ SKP (by decide), s3P, hkey]
    congr 1
    cases haltBit (M.halt.map S1Parse.bitOf) e.src_state <;>
      cases seenHit (e.src_state, oTag o, oVal o) seen <;> rfl

end S1Step
