import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT
import Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC_free
import Complexity.Lang.PolyTime

set_option autoImplicit false

/-! # `BinaryCC ⪯p' FSAT` as a free `PolyTimeComputableLang` witness — FOUNDATION

Top-down target #2 (HANDOFF/ROADMAP): re-express the Tseytin transform
`BinaryCC_to_FSAT_instance` (`Reductions/BinaryCC_to_FSAT.lean`, ~1K-LOC formula
builder) as a free layer witness. This is the **expensive tail item**, budgeted
at ~2 sessions. This file is **session 1's deliverable**: the proven
serialization foundation + the pinned input/output encodings + the validated
emitter building blocks. The program assembly and its run/cost lemmas are
session 2 (see the DESIGN + NEXT-SESSION block at the bottom, and
`probes/FSATSerProbe.lean` for the end-to-end `#eval` validation of everything
here).

## The crux resolution (design question (b), HANDOFF)

Every prior free-witness output (SAT `cnf`, `BinaryCC`) is a FLAT record of
lists; the FSAT output `formula` is a **nested inductive TREE**. Resolution:
serialize the tree in **prefix (Polish) order** as a self-delimiting bit-list in
ONE output register, and build it with **forward `forBnd` loops** emitting
tokens. The enabling algebraic fact:

    listAnd [f₁,…,fₙ] = fand f₁ (fand f₂ (… ftrue))
  ⇒ serF (listAnd fs) = (⋃ᵢ (fandTag ++ serF fᵢ)) ++ ftrueTag

i.e. a forward append loop (operator-tag-then-child per element, base tag once at
the end). Same for `listOr`. The tree's nesting collapses into token-emission
ORDER — exactly what the DSL's counted loops produce.
-/

namespace BinaryCCFSATFree

open Complexity.Lang
open BinaryCCToFSAT

/-! ## 1. Prefix (Polish) serialization of `formula` — the output codec

Prefix-free bit code (decode reads 2 bits, then 1 more when they are `11`):
`ftrue = [0,0]`, `fand = [0,1]`, `forr = [1,0]`, `fneg = [1,1,0]`,
`fvar v = [1,1,1] ++ 1^v ++ [0]`. All cells `∈ {0,1}` (BitState-clean, so the
output register is a legal machine register). -/

def serF : formula → List Nat
  | .ftrue     => [0, 0]
  | .fand a b  => [0, 1] ++ serF a ++ serF b
  | .forr a b  => [1, 0] ++ serF a ++ serF b
  | .fneg a    => [1, 1, 0] ++ serF a
  | .fvar v    => [1, 1, 1] ++ List.replicate v 1 ++ [0]

/-- Read a leading unary `1`-block, returning `(count, suffix-after-0)`. -/
def readUnary : List Nat → Nat × List Nat
  | [] => (0, [])
  | 0 :: rest => (0, rest)
  | _ :: rest => let (v, r) := readUnary rest; (v + 1, r)

/-- Fuel-driven Polish parser: `(formula, unconsumed suffix)`. -/
def deserF : Nat → List Nat → Option (formula × List Nat)
  | 0, _ => none
  | _, 0 :: 0 :: rest => some (.ftrue, rest)
  | fuel + 1, 0 :: 1 :: rest =>
      match deserF fuel rest with
      | some (a, r1) => match deserF fuel r1 with
                        | some (b, r2) => some (.fand a b, r2)
                        | none => none
      | none => none
  | fuel + 1, 1 :: 0 :: rest =>
      match deserF fuel rest with
      | some (a, r1) => match deserF fuel r1 with
                        | some (b, r2) => some (.forr a b, r2)
                        | none => none
      | none => none
  | fuel + 1, 1 :: 1 :: 0 :: rest =>
      match deserF fuel rest with
      | some (a, r1) => some (.fneg a, r1)
      | none => none
  | _ + 1, 1 :: 1 :: 1 :: rest =>
      let (v, r) := readUnary rest
      some (.fvar v, r)
  | _, _ => none

/-- Full decode: parse with fuel = length + 1 (always enough, `formula_size_le_serF`). -/
def decodeF (bits : List Nat) : Option formula :=
  (deserF (bits.length + 1) bits).map Prod.fst

/-! ### The round-trip: `decodeF ∘ serF = id` (injectivity backbone of `decodeOut`) -/

theorem readUnary_replicate (v : Nat) (rest : List Nat) :
    readUnary (List.replicate v 1 ++ (0 :: rest)) = (v, rest) := by
  induction v with
  | zero => simp [readUnary]
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [readUnary, ih]

theorem deserF_serF (f : formula) :
    ∀ (fuel : Nat) (rest : List Nat), formula_size f ≤ fuel →
      deserF fuel (serF f ++ rest) = some (f, rest) := by
  induction f with
  | ftrue =>
      intro fuel rest h
      cases fuel with
      | zero => simp [formula_size] at h
      | succ n => rfl
  | fvar v =>
      intro fuel rest h
      cases fuel with
      | zero => simp [formula_size] at h
      | succ n =>
          simp only [serF, List.append_assoc]
          show deserF (n+1) (1 :: 1 :: 1 :: (List.replicate v 1 ++ (0 :: rest))) = _
          simp only [deserF, readUnary_replicate]
  | fand a b iha ihb =>
      intro fuel rest h
      cases fuel with
      | zero => simp [formula_size] at h
      | succ n =>
          have ha : formula_size a ≤ n := by simp [formula_size] at h; omega
          have hb : formula_size b ≤ n := by simp [formula_size] at h; omega
          show deserF (n+1) (0 :: 1 :: (serF a ++ serF b ++ rest)) = _
          simp only [deserF]
          rw [show serF a ++ serF b ++ rest = serF a ++ (serF b ++ rest) by simp]
          simp only [iha n (serF b ++ rest) ha, ihb n rest hb]
  | forr a b iha ihb =>
      intro fuel rest h
      cases fuel with
      | zero => simp [formula_size] at h
      | succ n =>
          have ha : formula_size a ≤ n := by simp [formula_size] at h; omega
          have hb : formula_size b ≤ n := by simp [formula_size] at h; omega
          show deserF (n+1) (1 :: 0 :: (serF a ++ serF b ++ rest)) = _
          simp only [deserF]
          rw [show serF a ++ serF b ++ rest = serF a ++ (serF b ++ rest) by simp]
          simp only [iha n (serF b ++ rest) ha, ihb n rest hb]
  | fneg a iha =>
      intro fuel rest h
      cases fuel with
      | zero => simp [formula_size] at h
      | succ n =>
          have ha : formula_size a ≤ n := by simp [formula_size] at h; omega
          show deserF (n+1) (1 :: 1 :: 0 :: (serF a ++ rest)) = _
          simp only [deserF]
          simp only [iha n rest ha]

theorem formula_size_le_serF (f : formula) : formula_size f ≤ (serF f).length := by
  induction f with
  | ftrue => simp [serF, formula_size]
  | fvar v => simp [serF, formula_size]
  | fand a b iha ihb =>
      simp only [serF, formula_size, List.length_append, List.length_cons, List.length_nil]; omega
  | forr a b iha ihb =>
      simp only [serF, formula_size, List.length_append, List.length_cons, List.length_nil]; omega
  | fneg a iha =>
      simp only [serF, formula_size, List.length_append, List.length_cons, List.length_nil]; omega

/-- **The output codec is injective** (`decodeF` inverts `serF`). This is what
`decode_agree`/`computes` will lean on: the program writes `serF (f x)` into the
output register, and `decodeOut` reads it back exactly. Axiom-clean. -/
theorem decodeF_serF (f : formula) : decodeF (serF f) = some f := by
  unfold decodeF
  have h := deserF_serF f ((serF f).length + 1) [] (by have := formula_size_le_serF f; omega)
  rw [List.append_nil] at h
  rw [h]; rfl

/-! ## 2. The input/output register layout (design question (c), pinned to the seam)

The composite `FlatTCC → … → BinaryCC` witness exits with the intermediate
`BinaryCC` in registers (see `FlatCCBinFree.encKeyB` / the live seam
`FlatTCCBinComp`):

    17 offset (1^offset)   18 width (1^width)   19 init (bit-list)
    20 cards (sentinel stream)   21 final (sentinel stream)   5 steps (1^steps)

`encodeIn` below is pinned to THAT frame so the future seam
(`BinaryCC_to_FSAT_comp.lean`) is a near-pure scrub (seam discipline). The
sentinel-stream formats for cards/final are `FlatCCBinFree`'s `encCardsOut` /
`encFinal`; here we mirror them via the reduction's own bit views. The single
formula output goes to `FOUT`. -/

/-- Input register indices (pinned to the BinaryCC exit frame). -/
def OFFSET : Nat := 17
def WIDTH  : Nat := 18
def INIT   : Nat := 19
def CARDS  : Nat := 20
def FINAL  : Nat := 21
def STEPS  : Nat := 5
/-- The output register holding `serF (BinaryCC_to_FSAT_instance C)`. -/
def FOUT   : Nat := 0

/-- Read the serialized formula out of `FOUT` and decode it. On a well-formed run
the register holds `serF (f C)`, so this returns `f C` by `decodeF_serF`; the
`getD .ftrue` fallback is never hit on real outputs. -/
def decodeOut (s : State) : formula := (decodeF (s.get FOUT)).getD .ftrue

/-- `decodeOut` recovers a formula from its serialization (the core fact the
witness's `computes` obligation reduces to once the program is shown to write
`serF (f C)` into `FOUT`). -/
theorem decodeOut_of_serF (s : State) (f : formula) (h : s.get FOUT = serF f) :
    decodeOut s = f := by
  simp only [decodeOut, h, decodeF_serF, Option.getD_some]

/-! ## 3. The reduction program `buildFSAT` (VALIDATED end-to-end, session 2)

The full `Cmd` computing `serF (BinaryCC_to_FSAT_instance C)` into `FOUT`,
`#eval`-validated end-to-end in `probes/FSATSerProbe.lean` against the pure
`serF ∘ encodeTableau` (wellformed) and `serF falseFml` (non-wellformed) on real
`BinaryCC` instances (`checkFull`). Still pure `Cmd`/`State` DATA — the run/cost
lemmas and the `PolyTimeComputableLang` witness are the remaining work (see the
NEXT-SESSION block at the bottom).

The Polish emission collapses `encodeTableau`'s tree into token-emission ORDER
(HANDOFF design fact): `serF (listAnd fs) = (⋃ᵢ [0,1]++serF fᵢ) ++ [0,0]`, so
each `listAnd`/`listOr` fold is one `forBnd`. Absolute variable indices
`line*L + step*offset (+i)` are built UNARY from the loop counters via
`concat`/mul-loops (`L = init.length`). The wellformedness guard is reproduced
on-machine (`computeWF`) so non-wellformed inputs emit `serF falseFml`.

Working registers (all `≥ 22`, above the pinned input frame 5/17/18/19/20/21). -/
def OUT    : Nat := 22   -- serialized-formula accumulator (copied to FOUT at the end)
def SCAN   : Nat := 23   -- consumable copy of a stream being iterated
def LREG   : Nat := 24   -- 1^L  (L = init.length)
def LINEL  : Nat := 25   -- 1^(line*L)
def STEPO  : Nat := 26   -- 1^(step*offset)
def STARTA : Nat := 27   -- 1^(line*L + step*offset)
def STARTB : Nat := 28   -- 1^((line+1)*L + step*offset)
def WREG   : Nat := 29   -- 1^(absolute variable index)
def TFLG   : Nat := 30   -- bit/branch flag
def DONE   : Nat := 31   -- sentinel-stream terminator flag
def SUMW   : Nat := 32   -- 1^(step*offset + width) for the step guard
def GFLG   : Nat := 33   -- step/final bound guard flag
def REM    : Nat := 34   -- truncated-subtraction remainder scratch
def SCANF  : Nat := 35   -- final-stream consumable copy
def FSTART : Nat := 36   -- 1^(steps*L + step*offset)
def BLEN   : Nat := 37   -- 1^(bits.length) of a final string
def STEPSL : Nat := 38   -- 1^(steps*L)
def EMARK  : Nat := 39   -- sentinel element-vs-terminator marker
def KLINE  : Nat := 40   -- forBnd counters (distinct per nesting level)
def KSTEP  : Nat := 41
def KCARD  : Nat := 42
def KBIT   : Nat := 43
def KFS    : Nat := 44
def KFSTEP : Nat := 45
def KTMP   : Nat := 46
def KTMP2  : Nat := 47
def LREG1  : Nat := 48   -- 1^(L+1)  (step-loop bound)
def FBITS  : Nat := 49   -- one parsed final string as a bit-list
def GWF    : Nat := 50   -- wellformedness flag
def MREM   : Nat := 51   -- guard scratch
def MCHK   : Nat := 52
def MGE    : Nat := 53
def SCANW  : Nat := 54   -- card-stream copy for the length check
def CLEN   : Nat := 55   -- parsed prem/conc length
def ZERO   : Nat := 56   -- always-empty base (var index 0) / no-op sink

/-- The register frame width: the program touches only registers `< regFrame`. -/
def regFrame : Nat := 57

/-! ### Literal-tag emitters (append fixed bits to `OUT`). -/
def emit0 : Cmd := Cmd.op (.appendZero OUT)
def emit1 : Cmd := Cmd.op (.appendOne OUT)
def emitFtrue    : Cmd := emit0 ;; emit0                        -- serF ftrue = [0,0]
def emitFandTag  : Cmd := emit0 ;; emit1                        -- fand node = [0,1]
def emitForrTag  : Cmd := emit1 ;; emit0                        -- forr node = [1,0]
def emitFalse    : Cmd := emit1 ;; emit1 ;; emit0 ;; emit0 ;; emit0  -- serF falseFml = [1,1,0,0,0]

/-- Emit `serF (fvar w)` where `WREG = 1^w`: `[1,1,1] ++ 1^w ++ [0]`. -/
def emitVarW : Cmd :=
  emit1 ;; emit1 ;; emit1 ;; Cmd.op (.concat OUT OUT WREG) ;; emit0

/-- Emit the literal for a bit `b` (in `TFLG`) at absolute index `WREG`:
`b=1 → serF (fvar w)`, `b=0 → serF (fneg (fvar w)) = [1,1,0] ++ serF (fvar w)`. -/
def emitLitAt : Cmd :=
  Cmd.ifBit TFLG emitVarW (emit1 ;; emit1 ;; emit0 ;; emitVarW)

/-! ### Run lemmas for the literal-tag emitters (session 3, step 2 — the crux)

`litFor`/`bitsPrefix` mirror `BinaryCCToFSAT.encodeBitsAt`'s unfolding one bit
at a time, matching the loop order `emitBitsFromScan`/`emitBitsFromSent`
actually emit in. -/

/-- The literal for bit `b` at variable index `v` — matches
`encodeBitsAt`'s `if b then .fvar start else .fneg (.fvar start)` exactly
(`encodeBitsAt_cons` below is `rfl`). -/
def litFor (b : Bool) (v : Nat) : formula := if b then .fvar v else .fneg (.fvar v)

theorem encodeBitsAt_cons (start : Nat) (b : Bool) (bs : List Bool) :
    BinaryCCToFSAT.encodeBitsAt start (b :: bs)
      = .fand (litFor b start) (BinaryCCToFSAT.encodeBitsAt (start + 1) bs) := rfl

/-- The tag+literal serialization of a bit-list starting at variable `start`,
**without** the closing `ftrue` tag — the loop's accumulated `OUT` after `i`
iterations is `OUT₀ ++ bitsPrefix start (bits.take i)`. -/
def bitsPrefix (start : Nat) : List Bool → List Nat
  | [] => []
  | b :: bs => [0, 1] ++ serF (litFor b start) ++ bitsPrefix (start + 1) bs

/-- Closing the accumulated prefix with `ftrue`'s tag gives exactly
`serF (encodeBitsAt start bits)` — the algebraic fact powering `buildFSAT_run`'s
final `emitFtrue`. -/
theorem serF_encodeBitsAt (start : Nat) (bits : List Bool) :
    serF (BinaryCCToFSAT.encodeBitsAt start bits) = bitsPrefix start bits ++ [0, 0] := by
  induction bits generalizing start with
  | nil => rfl
  | cons b bs ih =>
      rw [encodeBitsAt_cons]
      show serF (.fand (litFor b start) (BinaryCCToFSAT.encodeBitsAt (start + 1) bs)) = _
      simp only [serF, bitsPrefix, ih (start + 1), List.append_assoc]

/-- `bitsPrefix` splits over list append, shifting the start index by the
prefix's length — the accumulation law behind the loop invariant (the
"`_snoc`" step, specialized to a singleton `ys` in `bitsPrefix_take_succ`). -/
theorem bitsPrefix_append (start : Nat) (xs ys : List Bool) :
    bitsPrefix start (xs ++ ys) = bitsPrefix start xs ++ bitsPrefix (start + xs.length) ys := by
  induction xs generalizing start with
  | nil => simp [bitsPrefix]
  | cons b xs ih =>
      have hstart : start + 1 + xs.length = start + (b :: xs).length := by
        simp; omega
      simp only [List.cons_append, bitsPrefix, List.length_cons]
      rw [ih (start + 1), hstart]
      simp [List.append_assoc]

/-- The loop-invariant snoc step: extending the processed prefix by one more
bit appends exactly one `[0,1] ++ serF (litFor · ·)` block. -/
theorem bitsPrefix_take_succ (start : Nat) (bits : List Bool) (i : Nat) (hi : i < bits.length) :
    bitsPrefix start (bits.take (i + 1))
      = bitsPrefix start (bits.take i) ++ [0, 1] ++ serF (litFor bits[i] (start + i)) := by
  have htake : bits.take (i + 1) = bits.take i ++ [bits[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  rw [htake, bitsPrefix_append, List.length_take, Nat.min_eq_left (le_of_lt hi)]
  simp [bitsPrefix, List.append_assoc]

private theorem emit0_run (s : State) : emit0.eval s = s.set OUT (s.get OUT ++ [0]) := rfl
private theorem emit1_run (s : State) : emit1.eval s = s.set OUT (s.get OUT ++ [1]) := rfl

private theorem emitFtrue_run (s : State) :
    emitFtrue.eval s = s.set OUT (s.get OUT ++ [0, 0]) := by
  simp only [emitFtrue, Cmd.eval_seq, emit0_run, State.get_set_eq, State.set_set,
    List.append_assoc]
  rfl

private theorem emitFandTag_run (s : State) :
    emitFandTag.eval s = s.set OUT (s.get OUT ++ [0, 1]) := by
  simp only [emitFandTag, Cmd.eval_seq, emit0_run, emit1_run, State.get_set_eq, State.set_set,
    List.append_assoc]
  rfl

private theorem emitVarW_run (s : State) (v : Nat)
    (hW : State.get s WREG = List.replicate v 1) :
    emitVarW.eval s = s.set OUT (s.get OUT ++ serF (.fvar v)) := by
  simp only [emitVarW, Cmd.eval_seq, emit0_run, emit1_run, Cmd.eval_op, Op.eval,
    State.get_set_eq, State.get_set_ne _ _ _ _ (show WREG ≠ OUT by decide), hW, State.set_set,
    List.append_assoc, serF]
  rfl

private theorem emitLitAt_run (s : State) (b : Bool) (v : Nat)
    (hT : State.get s TFLG = if b then [1] else [0])
    (hW : State.get s WREG = List.replicate v 1) :
    emitLitAt.eval s = s.set OUT (s.get OUT ++ serF (litFor b v)) := by
  unfold emitLitAt
  cases b with
  | true =>
      have hTFLG : State.get s TFLG = [1] := by rw [hT]; decide
      rw [Cmd.eval_ifBit_true _ _ _ _ hTFLG, emitVarW_run s v hW]
      rfl
  | false =>
      have hTFLG : State.get s TFLG ≠ [1] := by rw [hT]; decide
      rw [Cmd.eval_ifBit_false _ _ _ _ hTFLG]
      have e1 : (emit1 ;; emit1 ;; emit0 ;; emitVarW).eval s
          = emitVarW.eval (s.set OUT (s.get OUT ++ [1, 1, 0])) := by
        simp only [Cmd.eval_seq, emit0_run, emit1_run, State.get_set_eq, State.set_set,
          List.append_assoc]
        rfl
      rw [e1]
      have hW' : State.get (s.set OUT (s.get OUT ++ [1, 1, 0])) WREG = List.replicate v 1 := by
        rw [State.get_set_ne _ _ _ _ (show WREG ≠ OUT by decide)]; exact hW
      rw [emitVarW_run _ v hW']
      simp only [State.get_set_eq, State.set_set, List.append_assoc]
      rfl

/-- Every literal-tag emitter above touches only `OUT` — the frame half of
each `_run` lemma, needed so the fold invariants below can track `SCAN`/
`TFLG`/`WREG`/`KBIT` through `emitFandTag`/`emitLitAt` untouched. -/
private theorem emitFtrue_frame (s : State) (r : Var) (hr : r ≠ OUT) :
    State.get (emitFtrue.eval s) r = State.get s r := by
  simp only [emitFtrue, Cmd.eval_seq, emit0_run, State.get_set_ne _ _ _ _ hr]

private theorem emitFandTag_frame (s : State) (r : Var) (hr : r ≠ OUT) :
    State.get (emitFandTag.eval s) r = State.get s r := by
  simp only [emitFandTag, Cmd.eval_seq, emit0_run, emit1_run, State.get_set_ne _ _ _ _ hr]

private theorem emitVarW_frame (s : State) (r : Var) (hr : r ≠ OUT) :
    State.get (emitVarW.eval s) r = State.get s r := by
  simp only [emitVarW, Cmd.eval_seq, emit0_run, emit1_run, Cmd.eval_op, Op.eval,
    State.get_set_ne _ _ _ _ hr]

private theorem emitLitAt_frame (s : State) (r : Var) (hr : r ≠ OUT) :
    State.get (emitLitAt.eval s) r = State.get s r := by
  unfold emitLitAt
  by_cases hb : State.get s TFLG = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hb, emitVarW_frame s r hr]
  · rw [Cmd.eval_ifBit_false _ _ _ _ hb]
    simp only [Cmd.eval_seq, emit0_run, emit1_run, State.get_set_ne _ _ _ _ hr,
      emitVarW_frame _ r hr]

/-- `serF (encodeBitsAt start bits)` reading `bound`-many bits off `SCAN` (a bit
register); bit `i`'s index is `concat(BASE, 1^i)` = `1^(start+i)`. -/
def emitBitsFromScan (BASE bound : Nat) : Cmd :=
  Cmd.forBnd KBIT bound
    ( Cmd.op (.head TFLG SCAN) ;;
      Cmd.op (.tail SCAN SCAN) ;;
      Cmd.op (.concat WREG BASE KBIT) ;;
      emitFandTag ;;
      emitLitAt ) ;;
  emitFtrue

/-! ### `emitBitsFromScan_run` — the direct (unencoded) bit-list leaf lemma

The first "session 3, step 2" crux lemma: the loop unrolls exactly the
`bitsPrefix` accumulation (`bitsPrefix_take_succ`), so `OUT` after the loop is
`OUT₀ ++ bitsPrefix start bits`, and closing with `emitFtrue` gives
`serF (encodeBitsAt start bits)` via `serF_encodeBitsAt`. -/

/-- Fold invariant: after `i` iterations, `SCAN` holds the remaining bits and
`OUT` the tag+literal prefix processed so far; every other register (in
particular `BASE`, assumed disjoint from the loop's scratch set) is frozen. -/
private def BSInv (BASE start : Nat) (bits : List Bool) (u : State) (i : Nat)
    (st : State) : Prop :=
  State.get st SCAN = FlatCCBinFree.bitsNat (bits.drop i)
  ∧ State.get st OUT = State.get u OUT ++ bitsPrefix start (bits.take i)
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
      State.get st r = State.get u r)

private theorem BSInv_step (BASE start : Nat) (bits : List Bool) (u : State)
    (hBS : BASE ≠ SCAN) (hBO : BASE ≠ OUT) (hBW : BASE ≠ WREG) (hBT : BASE ≠ TFLG)
    (hBK : BASE ≠ KBIT) (hB : State.get u BASE = List.replicate start 1)
    (i : Nat) (hi : i < bits.length) (st : State) (h : BSInv BASE start bits u i st) :
    BSInv BASE start bits u (i + 1)
      (( Cmd.op (.head TFLG SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
         Cmd.op (.concat WREG BASE KBIT) ;; emitFandTag ;; emitLitAt
       ).eval (st.set KBIT (List.replicate i 1))) := by
  obtain ⟨hSCAN, hOUT, hframe⟩ := h
  set w := st.set KBIT (List.replicate i 1) with hw
  have hwframe : ∀ r : Var, r ≠ KBIT → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwK : State.get w KBIT = List.replicate i 1 := State.get_set_eq _ _ _
  have hwSCAN : State.get w SCAN = FlatCCBinFree.bitsNat (bits.drop i) := by
    rw [hwframe SCAN (by decide)]; exact hSCAN
  have hwOUT : State.get w OUT = State.get u OUT ++ bitsPrefix start (bits.take i) := by
    rw [hwframe OUT (by decide)]; exact hOUT
  have hwBASE : State.get w BASE = List.replicate start 1 := by
    rw [hwframe BASE hBK, hframe BASE hBS hBO hBW hBT hBK]; exact hB
  clear_value w
  have hdrop : bits.drop i = bits[i] :: bits.drop (i + 1) := List.drop_eq_getElem_cons hi
  have htake : bits.take (i + 1) = bits.take i ++ [bits[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  set b := bits[i] with hb
  clear_value b
  have hSCANw : State.get w SCAN
      = (cond b 1 0) :: FlatCCBinFree.bitsNat (bits.drop (i + 1)) := by
    rw [hwSCAN, hdrop]; rfl
  -- step 1: head TFLG SCAN
  have e1 : (Cmd.op (.head TFLG SCAN)).eval w = w.set TFLG [cond b 1 0] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hSCANw]
  set w1 := w.set TFLG [cond b 1 0] with hw1
  have hw1frame : ∀ r : Var, r ≠ TFLG → State.get w1 r = State.get w r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1T : State.get w1 TFLG = [cond b 1 0] := State.get_set_eq _ _ _
  have hw1SCAN : State.get w1 SCAN = State.get w SCAN := hw1frame SCAN (by decide)
  have hw1OUT : State.get w1 OUT = State.get w OUT := hw1frame OUT (by decide)
  have hw1BASE : State.get w1 BASE = State.get w BASE := hw1frame BASE hBT
  have hw1K : State.get w1 KBIT = State.get w KBIT := hw1frame KBIT (by decide)
  clear_value w1
  -- step 2: tail SCAN SCAN
  have e2 : (Cmd.op (.tail SCAN SCAN)).eval w1
      = w1.set SCAN (FlatCCBinFree.bitsNat (bits.drop (i + 1))) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw1SCAN, hSCANw, List.tail_cons]
  set w2 := w1.set SCAN (FlatCCBinFree.bitsNat (bits.drop (i + 1))) with hw2
  have hw2frame : ∀ r : Var, r ≠ SCAN → State.get w2 r = State.get w1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw2SCAN : State.get w2 SCAN = FlatCCBinFree.bitsNat (bits.drop (i + 1)) :=
    State.get_set_eq _ _ _
  have hw2T : State.get w2 TFLG = [cond b 1 0] := by
    rw [hw2frame TFLG (by decide)]; exact hw1T
  have hw2OUT : State.get w2 OUT = State.get w OUT := by
    rw [hw2frame OUT (by decide)]; exact hw1OUT
  have hw2BASE : State.get w2 BASE = List.replicate start 1 := by
    rw [hw2frame BASE hBS, hw1BASE]; exact hwBASE
  have hw2K : State.get w2 KBIT = List.replicate i 1 := by
    rw [hw2frame KBIT (by decide), hw1K]; exact hwK
  clear_value w2
  -- step 3: concat WREG BASE KBIT
  have e3 : (Cmd.op (.concat WREG BASE KBIT)).eval w2
      = w2.set WREG (List.replicate (start + i) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hw2BASE, hw2K]
    congr 1
    rw [List.replicate_add]
  set w3 := w2.set WREG (List.replicate (start + i) 1) with hw3
  have hw3frame : ∀ r : Var, r ≠ WREG → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3W : State.get w3 WREG = List.replicate (start + i) 1 := State.get_set_eq _ _ _
  have hw3SCAN : State.get w3 SCAN = FlatCCBinFree.bitsNat (bits.drop (i + 1)) := by
    rw [hw3frame SCAN (by decide)]; exact hw2SCAN
  have hw3T : State.get w3 TFLG = [cond b 1 0] := by
    rw [hw3frame TFLG (by decide)]; exact hw2T
  have hw3OUT : State.get w3 OUT = State.get w OUT := by
    rw [hw3frame OUT (by decide)]; exact hw2OUT
  clear_value w3
  -- step 4: emitFandTag
  set w4 := emitFandTag.eval w3 with hw4
  have e4OUT : State.get w4 OUT = State.get w3 OUT ++ [0, 1] := by
    rw [hw4, emitFandTag_run]; exact State.get_set_eq _ _ _
  have e4SCAN : State.get w4 SCAN = State.get w3 SCAN :=
    emitFandTag_frame w3 SCAN (by decide)
  have e4T : State.get w4 TFLG = State.get w3 TFLG :=
    emitFandTag_frame w3 TFLG (by decide)
  have e4W : State.get w4 WREG = State.get w3 WREG :=
    emitFandTag_frame w3 WREG (by decide)
  clear_value w4
  -- step 5: emitLitAt
  have hTb : State.get w4 TFLG = if b then [1] else [0] := by
    rw [e4T, hw3T]; cases b <;> rfl
  have hWb : State.get w4 WREG = List.replicate (start + i) 1 := by
    rw [e4W, hw3W]
  set w5 := emitLitAt.eval w4 with hw5
  have e5OUT : State.get w5 OUT = State.get w4 OUT ++ serF (litFor b (start + i)) := by
    rw [hw5, emitLitAt_run w4 b (start + i) hTb hWb]; exact State.get_set_eq _ _ _
  have e5SCAN : State.get w5 SCAN = State.get w4 SCAN := emitLitAt_frame _ SCAN (by decide)
  have e5frame : ∀ r : Var, r ≠ OUT → State.get w5 r = State.get w4 r :=
    fun r hr => emitLitAt_frame _ r hr
  clear_value w5
  have heval : (( Cmd.op (.head TFLG SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
      Cmd.op (.concat WREG BASE KBIT) ;; emitFandTag ;; emitLitAt
    ).eval w) = w5 := by
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq, ← hw4, ← hw5]
  rw [heval]
  refine ⟨?_, ?_, ?_⟩
  · rw [e5SCAN, e4SCAN, hw3SCAN]
  · rw [e5OUT, e4OUT, hw3OUT, hwOUT, htake, bitsPrefix_append, List.length_take,
      Nat.min_eq_left (le_of_lt hi)]
    simp [bitsPrefix, List.append_assoc]
  · intro r hrS hrO hrW hrT hrK
    rw [e5frame r hrO, hw4, emitFandTag_frame _ r hrO, hw3frame r hrW, hw2frame r hrS,
      hw1frame r hrT, hwframe r hrK, hframe r hrS hrO hrW hrT hrK]

/-- **`emitBitsFromScan` is correct**: it consumes `bits.length`-many bits off
`SCAN` (`bound`'s length) and appends `serF (encodeBitsAt start bits)` to
`OUT`, leaving `SCAN` empty. `BASE` (a fixed constant elsewhere, e.g. `ZERO`
or `FSTART`) must sit outside the loop's scratch set `{SCAN,OUT,WREG,TFLG,
KBIT}`. -/
theorem emitBitsFromScan_run (BASE bound start : Nat) (bits : List Bool) (u : State)
    (hBS : BASE ≠ SCAN) (hBO : BASE ≠ OUT) (hBW : BASE ≠ WREG) (hBT : BASE ≠ TFLG)
    (hBK : BASE ≠ KBIT) (hB : State.get u BASE = List.replicate start 1)
    (hbnd : (State.get u bound).length = bits.length)
    (hSC : State.get u SCAN = FlatCCBinFree.bitsNat bits) :
    State.get ((emitBitsFromScan BASE bound).eval u) SCAN = []
    ∧ State.get ((emitBitsFromScan BASE bound).eval u) OUT
        = State.get u OUT ++ serF (BinaryCCToFSAT.encodeBitsAt start bits) := by
  have hbase : BSInv BASE start bits u 0 u := by
    refine ⟨by rw [List.drop_zero]; exact hSC,
      by rw [List.take_zero]; simp [bitsPrefix], fun r _ _ _ _ _ => rfl⟩
  have hInv : BSInv BASE start bits u bits.length
      (Cmd.foldlState
        ( Cmd.op (.head TFLG SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
          Cmd.op (.concat WREG BASE KBIT) ;; emitFandTag ;; emitLitAt )
        KBIT (List.range bits.length) u) :=
    Cmd.foldlState_range_induct _ KBIT bits.length u (BSInv BASE start bits u) hbase
      (fun i st hi hM => BSInv_step BASE start bits u hBS hBO hBW hBT hBK hB i hi st hM)
  obtain ⟨hSCANl, hOUTl, -⟩ := hInv
  have heval : (Cmd.forBnd KBIT bound
        ( Cmd.op (.head TFLG SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
          Cmd.op (.concat WREG BASE KBIT) ;; emitFandTag ;; emitLitAt )).eval u
      = Cmd.foldlState
          ( Cmd.op (.head TFLG SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
            Cmd.op (.concat WREG BASE KBIT) ;; emitFandTag ;; emitLitAt )
          KBIT (List.range bits.length) u := by
    rw [Cmd.eval_forBnd, hbnd]
  show State.get (emitFtrue.eval ((Cmd.forBnd KBIT bound _).eval u)) SCAN = []
    ∧ State.get (emitFtrue.eval ((Cmd.forBnd KBIT bound _).eval u)) OUT = _
  rw [heval]
  refine ⟨?_, ?_⟩
  · rw [emitFtrue_frame _ SCAN (by decide), hSCANl, List.drop_eq_nil_of_le (le_refl bits.length)]
    rfl
  · rw [emitFtrue_run, State.get_set_eq, hOUTl, List.take_of_length_le (le_refl bits.length),
      List.append_assoc, ← serF_encodeBitsAt]

/-- One iteration of the sentinel-stream bit emitter (the body of
`emitBitsFromSent`'s loop, factored out so its run lemma can name it): idle
when `DONE` is set; otherwise read the item marker off `SCAN` — an element
`1 1^b 0` emits its literal (and consumes `b+2` cells), the bare terminator
`0` sets `DONE`. -/
def sentBitBody (BASE : Nat) : Cmd :=
  Cmd.ifBit DONE
    (Cmd.op (.clear ZERO))
    ( Cmd.op (.head EMARK SCAN) ;;
      Cmd.ifBit EMARK
        ( Cmd.op (.tail SCAN SCAN) ;;
          Cmd.op (.head TFLG SCAN) ;;
          Cmd.op (.concat WREG BASE KBIT) ;;
          emitFandTag ;;
          emitLitAt ;;
          Cmd.ifBit TFLG
            (Cmd.op (.tail SCAN SCAN) ;; Cmd.op (.tail SCAN SCAN))
            (Cmd.op (.tail SCAN SCAN)) )
        ( Cmd.op (.tail SCAN SCAN) ;;
          Cmd.op (.clear DONE) ;; Cmd.op (.appendOne DONE) ) )

/-- `serF (encodeBitsAt start bits)` reading one `encSList` of bits off `SCAN`
(elements `1 1^b 0`, terminator bare `0`), leaving `SCAN` after the terminator.
`BASE = 1^start`; bit `i`'s index is `concat(BASE, 1^i)`. -/
def emitBitsFromSent (BASE : Nat) : Cmd :=
  Cmd.op (.clear DONE) ;;
  Cmd.forBnd KBIT SCAN (sentBitBody BASE) ;;
  emitFtrue

/-! ### `emitBitsFromSent_run` — the sentinel-stream bit-list leaf lemma

Same conclusion as `emitBitsFromScan_run` plus the extra clause the HANDOFF
plan calls for: `SCAN` ends up **past the terminator** (at the trailing
`rest`), so the caller (`emitCardsAt`) can chain two invocations (prem, conc)
off one card stream. The invariant is two-phase, split at `bits.length`:
before the terminator, iteration `i` consumes bit `i`'s sentinel element
(`DONE` clear, `SCAN` mid-stream); at `i = bits.length` the bare `0` flips
`DONE`; after it, iterations idle (re-clearing the always-empty `ZERO`, hence
the `ZERO` entry hypothesis and exit clause). -/

/-- The two-phase fold invariant for `sentBitBody`. -/
private def SBInv (BASE start : Nat) (bits : List Bool) (rest : List Nat)
    (u : State) (i : Nat) (st : State) : Prop :=
  (i ≤ bits.length →
      State.get st DONE = []
      ∧ State.get st SCAN
          = FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop i)) ++ rest
      ∧ State.get st OUT = State.get u OUT ++ bitsPrefix start (bits.take i))
  ∧ (bits.length < i →
      State.get st DONE = [1]
      ∧ State.get st SCAN = rest
      ∧ State.get st OUT = State.get u OUT ++ bitsPrefix start bits)
  ∧ State.get st ZERO = []
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
      r ≠ DONE → r ≠ EMARK → r ≠ ZERO → State.get st r = State.get u r)

private theorem SBInv_step (BASE start : Nat) (bits : List Bool) (rest : List Nat)
    (u : State)
    (hBS : BASE ≠ SCAN) (hBO : BASE ≠ OUT) (hBW : BASE ≠ WREG) (hBT : BASE ≠ TFLG)
    (hBK : BASE ≠ KBIT) (hBD : BASE ≠ DONE) (hBE : BASE ≠ EMARK) (hBZ : BASE ≠ ZERO)
    (hB : State.get u BASE = List.replicate start 1)
    (i : Nat) (st : State) (h : SBInv BASE start bits rest u i st) :
    SBInv BASE start bits rest u (i + 1)
      ((sentBitBody BASE).eval (st.set KBIT (List.replicate i 1))) := by
  obtain ⟨hph1, hph2, hZERO, hframe⟩ := h
  rcases Nat.lt_trichotomy i bits.length with hi | hi | hi
  · -- live bit iteration: consume one sentinel element, emit one tagged literal
    obtain ⟨hDONE, hSCAN, hOUT⟩ := hph1 (le_of_lt hi)
    set w := st.set KBIT (List.replicate i 1) with hw
    have hwframe : ∀ r : Var, r ≠ KBIT → State.get w r = State.get st r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwK : State.get w KBIT = List.replicate i 1 := State.get_set_eq _ _ _
    have hwD : State.get w DONE = [] := by
      rw [hwframe DONE (by decide)]; exact hDONE
    have hwZ : State.get w ZERO = [] := by
      rw [hwframe ZERO (by decide)]; exact hZERO
    have hwOUT : State.get w OUT = State.get u OUT ++ bitsPrefix start (bits.take i) := by
      rw [hwframe OUT (by decide)]; exact hOUT
    have hwBASE : State.get w BASE = List.replicate start 1 := by
      rw [hwframe BASE hBK, hframe BASE hBS hBO hBW hBT hBK hBD hBE hBZ]; exact hB
    have hdrop : bits.drop i = bits[i] :: bits.drop (i + 1) := List.drop_eq_getElem_cons hi
    have htake : bits.take (i + 1) = bits.take i ++ [bits[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
    set b := bits[i] with hb
    clear_value b
    set T := FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop (i + 1))) ++ rest
      with hT
    have hSCANw : State.get w SCAN = 1 :: (List.replicate (cond b 1 0) 1 ++ 0 :: T) := by
      rw [hwframe SCAN (by decide), hSCAN, hdrop, hT]
      show (FlatTCCFree.encSElem (cond b 1 0)
          ++ FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop (i + 1)))) ++ rest = _
      rw [List.append_assoc, FlatTCCFree.encSElem_append]
    clear_value w
    have hDONEne : State.get w DONE ≠ [1] := by rw [hwD]; decide
    -- step 1: head EMARK SCAN  (the element marker `1`)
    have e1 : (Cmd.op (.head EMARK SCAN)).eval w = w.set EMARK [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hSCANw]
    set w1 := w.set EMARK [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ EMARK → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1E : State.get w1 EMARK = [1] := State.get_set_eq _ _ _
    have hw1SCAN : State.get w1 SCAN = 1 :: (List.replicate (cond b 1 0) 1 ++ 0 :: T) := by
      rw [hw1frame SCAN (by decide)]; exact hSCANw
    clear_value w1
    -- step 2: tail SCAN SCAN  (drop the marker)
    have e2 : (Cmd.op (.tail SCAN SCAN)).eval w1
        = w1.set SCAN (List.replicate (cond b 1 0) 1 ++ 0 :: T) := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw1SCAN, List.tail_cons]
    set w2 := w1.set SCAN (List.replicate (cond b 1 0) 1 ++ 0 :: T) with hw2
    have hw2frame : ∀ r : Var, r ≠ SCAN → State.get w2 r = State.get w1 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw2SCAN : State.get w2 SCAN = List.replicate (cond b 1 0) 1 ++ 0 :: T :=
      State.get_set_eq _ _ _
    clear_value w2
    -- step 3: head TFLG SCAN  (the bit)
    have e3 : (Cmd.op (.head TFLG SCAN)).eval w2 = w2.set TFLG [cond b 1 0] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, hw2SCAN]
      cases b <;> rfl
    set w3 := w2.set TFLG [cond b 1 0] with hw3
    have hw3frame : ∀ r : Var, r ≠ TFLG → State.get w3 r = State.get w2 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw3T : State.get w3 TFLG = [cond b 1 0] := State.get_set_eq _ _ _
    have hw3SCAN : State.get w3 SCAN = List.replicate (cond b 1 0) 1 ++ 0 :: T := by
      rw [hw3frame SCAN (by decide)]; exact hw2SCAN
    have hw3BASE : State.get w3 BASE = List.replicate start 1 := by
      rw [hw3frame BASE hBT, hw2frame BASE hBS, hw1frame BASE hBE]; exact hwBASE
    have hw3K : State.get w3 KBIT = List.replicate i 1 := by
      rw [hw3frame KBIT (by decide), hw2frame KBIT (by decide),
        hw1frame KBIT (by decide)]; exact hwK
    have hw3OUT : State.get w3 OUT = State.get w OUT := by
      rw [hw3frame OUT (by decide), hw2frame OUT (by decide), hw1frame OUT (by decide)]
    clear_value w3
    -- step 4: concat WREG BASE KBIT  (the absolute var index `1^(start+i)`)
    have e4 : (Cmd.op (.concat WREG BASE KBIT)).eval w3
        = w3.set WREG (List.replicate (start + i) 1) := by
      rw [Cmd.eval_op]
      simp only [Op.eval, hw3BASE, hw3K]
      congr 1
      rw [List.replicate_add]
    set w4 := w3.set WREG (List.replicate (start + i) 1) with hw4
    have hw4frame : ∀ r : Var, r ≠ WREG → State.get w4 r = State.get w3 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw4W : State.get w4 WREG = List.replicate (start + i) 1 := State.get_set_eq _ _ _
    clear_value w4
    -- step 5: emitFandTag
    set w5 := emitFandTag.eval w4 with hw5
    have hw5frame : ∀ r : Var, r ≠ OUT → State.get w5 r = State.get w4 r := by
      intro r hr; rw [hw5]; exact emitFandTag_frame w4 r hr
    have e5OUT : State.get w5 OUT = State.get w4 OUT ++ [0, 1] := by
      rw [hw5, emitFandTag_run]; exact State.get_set_eq _ _ _
    clear_value w5
    -- step 6: emitLitAt
    have hw5T : State.get w5 TFLG = [cond b 1 0] := by
      rw [hw5frame TFLG (by decide), hw4frame TFLG (by decide)]; exact hw3T
    have hTb : State.get w5 TFLG = if b then [1] else [0] := by
      rw [hw5T]; cases b <;> rfl
    have hw5W : State.get w5 WREG = List.replicate (start + i) 1 := by
      rw [hw5frame WREG (by decide)]; exact hw4W
    set w6 := emitLitAt.eval w5 with hw6
    have hw6frame : ∀ r : Var, r ≠ OUT → State.get w6 r = State.get w5 r := by
      intro r hr; rw [hw6]; exact emitLitAt_frame w5 r hr
    have e6OUT : State.get w6 OUT = State.get w5 OUT ++ serF (litFor b (start + i)) := by
      rw [hw6, emitLitAt_run w5 b (start + i) hTb hw5W]; exact State.get_set_eq _ _ _
    clear_value w6
    have hw6SCAN : State.get w6 SCAN = List.replicate (cond b 1 0) 1 ++ 0 :: T := by
      rw [hw6frame SCAN (by decide), hw5frame SCAN (by decide),
        hw4frame SCAN (by decide)]; exact hw3SCAN
    have hw6T : State.get w6 TFLG = [cond b 1 0] := by
      rw [hw6frame TFLG (by decide)]; exact hw5T
    -- step 7: consume the element's `1^b ++ [0]` cells (two tails or one)
    have eF : (Cmd.ifBit TFLG (Cmd.op (.tail SCAN SCAN) ;; Cmd.op (.tail SCAN SCAN))
        (Cmd.op (.tail SCAN SCAN))).eval w6 = w6.set SCAN T := by
      cases b with
      | true =>
          have hT1 : State.get w6 TFLG = [1] := hw6T
          have hS1 : State.get w6 SCAN = 1 :: 0 :: T := hw6SCAN
          rw [Cmd.eval_ifBit_true _ _ _ _ hT1]
          have et1 : (Cmd.op (.tail SCAN SCAN)).eval w6 = w6.set SCAN (0 :: T) := by
            rw [Cmd.eval_op]; simp only [Op.eval, hS1, List.tail_cons]
          rw [Cmd.eval_seq, et1, Cmd.eval_op]
          simp only [Op.eval, State.get_set_eq, List.tail_cons, State.set_set]
      | false =>
          have hT0 : State.get w6 TFLG ≠ [1] := by rw [hw6T]; decide
          have hS0 : State.get w6 SCAN = 0 :: T := hw6SCAN
          rw [Cmd.eval_ifBit_false _ _ _ _ hT0, Cmd.eval_op]
          simp only [Op.eval, hS0, List.tail_cons]
    set wF := w6.set SCAN T with hwF
    have hwFframe : ∀ r : Var, r ≠ SCAN → State.get wF r = State.get w6 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwFSCAN : State.get wF SCAN = T := State.get_set_eq _ _ _
    have heval : (sentBitBody BASE).eval w = wF := by
      unfold sentBitBody
      rw [Cmd.eval_ifBit_false _ _ _ _ hDONEne, Cmd.eval_seq, e1,
        Cmd.eval_ifBit_true _ _ _ _ hw1E, Cmd.eval_seq, e2, Cmd.eval_seq, e3,
        Cmd.eval_seq, e4, Cmd.eval_seq, ← hw5, Cmd.eval_seq, ← hw6, eF]
    rw [heval]
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun hlt => absurd hlt (by omega), ?_, ?_⟩
    · rw [hwFframe DONE (by decide), hw6frame DONE (by decide),
        hw5frame DONE (by decide), hw4frame DONE (by decide),
        hw3frame DONE (by decide), hw2frame DONE (by decide),
        hw1frame DONE (by decide)]
      exact hwD
    · rw [hwFSCAN]
    · rw [hwFframe OUT (by decide), e6OUT, e5OUT, hw4frame OUT (by decide),
        hw3OUT, hwOUT, htake, bitsPrefix_append, List.length_take,
        Nat.min_eq_left (le_of_lt hi)]
      simp [bitsPrefix, List.append_assoc]
    · rw [hwFframe ZERO (by decide), hw6frame ZERO (by decide),
        hw5frame ZERO (by decide), hw4frame ZERO (by decide),
        hw3frame ZERO (by decide), hw2frame ZERO (by decide),
        hw1frame ZERO (by decide)]
      exact hwZ
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      rw [hwFframe r h1, hw6frame r h2, hw5frame r h2, hw4frame r h3,
        hw3frame r h4, hw2frame r h1, hw1frame r h7, hwframe r h5,
        hframe r h1 h2 h3 h4 h5 h6 h7 h8]
  · -- terminator iteration: consume the bare `0`, set DONE
    subst hi
    obtain ⟨hDONE, hSCAN, hOUT⟩ := hph1 (le_refl _)
    rw [List.take_of_length_le (le_refl bits.length)] at hOUT
    set w := st.set KBIT (List.replicate bits.length 1) with hw
    have hwframe : ∀ r : Var, r ≠ KBIT → State.get w r = State.get st r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwD : State.get w DONE = [] := by
      rw [hwframe DONE (by decide)]; exact hDONE
    have hwZ : State.get w ZERO = [] := by
      rw [hwframe ZERO (by decide)]; exact hZERO
    have hwOUT : State.get w OUT = State.get u OUT ++ bitsPrefix start bits := by
      rw [hwframe OUT (by decide)]; exact hOUT
    have hSCANw : State.get w SCAN = 0 :: rest := by
      rw [hwframe SCAN (by decide), hSCAN, List.drop_eq_nil_of_le (le_refl bits.length)]
      rfl
    clear_value w
    have hDONEne : State.get w DONE ≠ [1] := by rw [hwD]; decide
    have e1 : (Cmd.op (.head EMARK SCAN)).eval w = w.set EMARK [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hSCANw]
    set w1 := w.set EMARK [0] with hw1
    have hw1frame : ∀ r : Var, r ≠ EMARK → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1E : State.get w1 EMARK = [0] := State.get_set_eq _ _ _
    have hw1SCAN : State.get w1 SCAN = 0 :: rest := by
      rw [hw1frame SCAN (by decide)]; exact hSCANw
    clear_value w1
    have hw1Ene : State.get w1 EMARK ≠ [1] := by rw [hw1E]; decide
    have e2 : (Cmd.op (.tail SCAN SCAN)).eval w1 = w1.set SCAN rest := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw1SCAN, List.tail_cons]
    set w2 := w1.set SCAN rest with hw2
    have hw2frame : ∀ r : Var, r ≠ SCAN → State.get w2 r = State.get w1 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw2SCAN : State.get w2 SCAN = rest := State.get_set_eq _ _ _
    clear_value w2
    have e3 : (Cmd.op (.clear DONE)).eval w2 = w2.set DONE [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    set w3 := w2.set DONE [] with hw3
    have hw3frame : ∀ r : Var, r ≠ DONE → State.get w3 r = State.get w2 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw3D : State.get w3 DONE = [] := State.get_set_eq _ _ _
    clear_value w3
    have e4 : (Cmd.op (.appendOne DONE)).eval w3 = w3.set DONE [1] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, hw3D]
      rfl
    set wF := w3.set DONE [1] with hwF
    have hwFframe : ∀ r : Var, r ≠ DONE → State.get wF r = State.get w3 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have heval : (sentBitBody BASE).eval w = wF := by
      unfold sentBitBody
      rw [Cmd.eval_ifBit_false _ _ _ _ hDONEne, Cmd.eval_seq, e1,
        Cmd.eval_ifBit_false _ _ _ _ hw1Ene, Cmd.eval_seq, e2, Cmd.eval_seq, e3, e4]
    rw [heval]
    refine ⟨fun hle => absurd hle (by omega), fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hwF]; exact State.get_set_eq _ _ _
    · rw [hwFframe SCAN (by decide), hw3frame SCAN (by decide)]; exact hw2SCAN
    · rw [hwFframe OUT (by decide), hw3frame OUT (by decide),
        hw2frame OUT (by decide), hw1frame OUT (by decide)]
      exact hwOUT
    · rw [hwFframe ZERO (by decide), hw3frame ZERO (by decide),
        hw2frame ZERO (by decide), hw1frame ZERO (by decide)]
      exact hwZ
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      rw [hwFframe r h6, hw3frame r h6, hw2frame r h1, hw1frame r h7,
        hwframe r h5, hframe r h1 h2 h3 h4 h5 h6 h7 h8]
  · -- idle iteration: DONE set, only ZERO is (re-)cleared
    obtain ⟨hDONE, hSCAN, hOUT⟩ := hph2 hi
    set w := st.set KBIT (List.replicate i 1) with hw
    have hwframe : ∀ r : Var, r ≠ KBIT → State.get w r = State.get st r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwD : State.get w DONE = [1] := by
      rw [hwframe DONE (by decide)]; exact hDONE
    clear_value w
    have heval : (sentBitBody BASE).eval w = w.set ZERO [] := by
      unfold sentBitBody
      rw [Cmd.eval_ifBit_true _ _ _ _ hwD, Cmd.eval_op]
      simp only [Op.eval]
    rw [heval]
    refine ⟨fun hle => absurd hle (by omega), fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [State.get_set_ne _ _ _ _ (show DONE ≠ ZERO by decide)]; exact hwD
    · rw [State.get_set_ne _ _ _ _ (show SCAN ≠ ZERO by decide),
        hwframe SCAN (by decide)]
      exact hSCAN
    · rw [State.get_set_ne _ _ _ _ (show OUT ≠ ZERO by decide),
        hwframe OUT (by decide)]
      exact hOUT
    · exact State.get_set_eq _ _ _
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      rw [State.get_set_ne _ _ _ _ h8, hwframe r h5,
        hframe r h1 h2 h3 h4 h5 h6 h7 h8]

/-- **`emitBitsFromSent` is correct**: it consumes ONE sentinel-encoded
bit-list off the front of `SCAN` and appends `serF (encodeBitsAt start bits)`
to `OUT`, leaving `SCAN` **past the terminator** (at `rest`) — the extra
clause `emitBitsFromScan_run` does not need, and what lets `emitCardsAt`
chain the prem and conc emitters off one card stream. Surplus loop iterations
idle on `DONE` (re-clearing the always-empty `ZERO`, hence that entry
hypothesis and exit clause). `BASE` (e.g. `STARTA`/`STARTB`) must sit outside
the loop's scratch set `{SCAN,OUT,WREG,TFLG,KBIT,DONE,EMARK,ZERO}`. -/
theorem emitBitsFromSent_run (BASE start : Nat) (bits : List Bool) (rest : List Nat)
    (u : State)
    (hBS : BASE ≠ SCAN) (hBO : BASE ≠ OUT) (hBW : BASE ≠ WREG) (hBT : BASE ≠ TFLG)
    (hBK : BASE ≠ KBIT) (hBD : BASE ≠ DONE) (hBE : BASE ≠ EMARK) (hBZ : BASE ≠ ZERO)
    (hB : State.get u BASE = List.replicate start 1)
    (hZ : State.get u ZERO = [])
    (hSC : State.get u SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest) :
    State.get ((emitBitsFromSent BASE).eval u) SCAN = rest
    ∧ State.get ((emitBitsFromSent BASE).eval u) OUT
        = State.get u OUT ++ serF (BinaryCCToFSAT.encodeBitsAt start bits)
    ∧ State.get ((emitBitsFromSent BASE).eval u) ZERO = []
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
        r ≠ DONE → r ≠ EMARK → r ≠ ZERO →
        State.get ((emitBitsFromSent BASE).eval u) r = State.get u r) := by
  have e0 : (Cmd.op (.clear DONE)).eval u = u.set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u1 := u.set DONE [] with hu1
  have hu1frame : ∀ r : Var, r ≠ DONE → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1D : State.get u1 DONE = [] := State.get_set_eq _ _ _
  have hu1SC : State.get u1 SCAN
      = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest := by
    rw [hu1frame SCAN (by decide)]; exact hSC
  have hu1Z : State.get u1 ZERO = [] := by
    rw [hu1frame ZERO (by decide)]; exact hZ
  have hu1OUT : State.get u1 OUT = State.get u OUT := hu1frame OUT (by decide)
  clear_value u1
  have hN : bits.length + 1 ≤ (State.get u1 SCAN).length := by
    rw [hu1SC, List.length_append, FlatTCCFree.encSList_length,
      show (FlatCCBinFree.bitsNat bits).length = bits.length from List.length_map _]
    omega
  have hbase : SBInv BASE start bits rest u 0 u1 := by
    refine ⟨fun _ => ⟨hu1D, by rw [List.drop_zero]; exact hu1SC, ?_⟩,
      fun hlt => absurd hlt (Nat.not_lt_zero _), hu1Z,
      fun r _ _ _ _ _ hrD _ _ => hu1frame r hrD⟩
    rw [List.take_zero, show bitsPrefix start [] = [] from rfl, List.append_nil]
    exact hu1OUT
  have hInv : SBInv BASE start bits rest u (State.get u1 SCAN).length
      (Cmd.foldlState (sentBitBody BASE) KBIT
        (List.range (State.get u1 SCAN).length) u1) :=
    Cmd.foldlState_range_induct _ KBIT _ u1 (SBInv BASE start bits rest u) hbase
      (fun i st _ hM =>
        SBInv_step BASE start bits rest u hBS hBO hBW hBT hBK hBD hBE hBZ hB i st hM)
  obtain ⟨-, hph2, hZf, hframef⟩ := hInv
  obtain ⟨-, hSCf, hOUTf⟩ := hph2 (by omega)
  have heval : (emitBitsFromSent BASE).eval u
      = emitFtrue.eval (Cmd.foldlState (sentBitBody BASE) KBIT
          (List.range (State.get u1 SCAN).length) u1) := by
    show emitFtrue.eval ((Cmd.forBnd KBIT SCAN (sentBitBody BASE)).eval
      ((Cmd.op (.clear DONE)).eval u)) = _
    rw [e0, Cmd.eval_forBnd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval, emitFtrue_frame _ SCAN (by decide)]; exact hSCf
  · rw [heval, emitFtrue_run, State.get_set_eq, hOUTf, List.append_assoc,
      ← serF_encodeBitsAt]
  · rw [heval, emitFtrue_frame _ ZERO (by decide)]; exact hZf
  · intro r h1 h2 h3 h4 h5 h6 h7 h8
    rw [heval, emitFtrue_frame _ r h2, hframef r h1 h2 h3 h4 h5 h6 h7 h8]

/-- `serF (encodeCardsAt C startA startB)` = `listOr` over cards, consuming a
copy of the card stream. `STARTA = 1^startA`, `STARTB = 1^startB` pre-set. -/
def emitCardsAt : Cmd :=
  Cmd.op (.copy SCAN CARDS) ;;
  Cmd.forBnd KCARD CARDS
    ( Cmd.op (.nonEmpty TFLG SCAN) ;;
      Cmd.ifBit TFLG
        ( emitForrTag ;; emitFandTag ;;
          emitBitsFromSent STARTA ;;
          emitBitsFromSent STARTB )
        (Cmd.op (.clear KTMP)) ) ;;
  emitFalse

/-- Precompute `LREG = 1^L`, `LREG1 = 1^(L+1)` from the init bit-list. -/
def precompLen : Cmd :=
  Cmd.op (.clear LREG) ;;
  Cmd.forBnd KTMP INIT (Cmd.op (.appendOne LREG)) ;;
  Cmd.op (.copy LREG1 LREG) ;; Cmd.op (.appendOne LREG1)

/-- One step constraint at `(line, step)`: guarded cards or `ftrue`. Assumes
`LINEL = 1^(line*L)`, `KSTEP = 1^step`; uses `OFFSET`/`WIDTH`/`LREG`. -/
def stepBody : Cmd :=
  Cmd.op (.clear STEPO) ;;
  Cmd.forBnd KTMP KSTEP (Cmd.op (.concat STEPO STEPO OFFSET)) ;;
  Cmd.op (.concat STARTA LINEL STEPO) ;;
  Cmd.op (.concat STARTB STARTA LREG) ;;
  Cmd.op (.concat SUMW STEPO WIDTH) ;;
  Cmd.op (.copy REM SUMW) ;;
  Cmd.forBnd KTMP LREG (Cmd.op (.tail REM REM)) ;;
  Cmd.op (.nonEmpty TFLG REM) ;;
  Cmd.ifBit TFLG
    (Cmd.op (.clear GFLG))
    (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG)) ;;
  Cmd.ifBit GFLG emitCardsAt emitFtrue

/-- `serF (encodeAllStepConstraints C)` = `listAnd` over lines of
(`listAnd` over steps of `encodeStepConstraint`). -/
def emitAllSteps : Cmd :=
  Cmd.forBnd KLINE STEPS
    ( emitFandTag ;;
      Cmd.op (.clear LINEL) ;;
      Cmd.forBnd KTMP2 KLINE (Cmd.op (.concat LINEL LINEL LREG)) ;;
      Cmd.forBnd KSTEP LREG1 (emitFandTag ;; stepBody) ;;
      emitFtrue ) ;;
  emitFtrue

/-- Consume one `encSList` of bits off `SCANF` into `FBITS` (bit-list) and
`BLEN` (`1^length`). -/
def readOneFinal : Cmd :=
  Cmd.op (.clear FBITS) ;; Cmd.op (.clear BLEN) ;; Cmd.op (.clear DONE) ;;
  Cmd.forBnd KTMP SCANF
    ( Cmd.ifBit DONE
        (Cmd.op (.clear KTMP2))
        ( Cmd.op (.head EMARK SCANF) ;;
          Cmd.ifBit EMARK
            ( Cmd.op (.tail SCANF SCANF) ;;
              Cmd.op (.head TFLG SCANF) ;;
              Cmd.ifBit TFLG
                (Cmd.op (.appendOne FBITS) ;; Cmd.op (.tail SCANF SCANF) ;; Cmd.op (.tail SCANF SCANF))
                (Cmd.op (.appendZero FBITS) ;; Cmd.op (.tail SCANF SCANF)) ;;
              Cmd.op (.appendOne BLEN) )
            ( Cmd.op (.tail SCANF SCANF) ;;
              Cmd.op (.clear DONE) ;; Cmd.op (.appendOne DONE) ) ) )

/-- `serF (encodeFinalConstraint C)` = `listOr` over final strings of
(`listOr` over steps of `encodeFinalAtStep`). -/
def emitFinal : Cmd :=
  Cmd.op (.clear STEPSL) ;;
  Cmd.forBnd KTMP STEPS (Cmd.op (.concat STEPSL STEPSL LREG)) ;;
  Cmd.op (.copy SCANF FINAL) ;;
  Cmd.forBnd KFS FINAL
    ( Cmd.op (.nonEmpty TFLG SCANF) ;;
      Cmd.ifBit TFLG
        ( emitForrTag ;;
          readOneFinal ;;
          Cmd.forBnd KFSTEP LREG1
            ( emitForrTag ;;
              Cmd.op (.clear STEPO) ;;
              Cmd.forBnd KTMP2 KFSTEP (Cmd.op (.concat STEPO STEPO OFFSET)) ;;
              Cmd.op (.concat SUMW STEPO BLEN) ;;
              Cmd.op (.copy REM SUMW) ;;
              Cmd.forBnd KTMP2 LREG (Cmd.op (.tail REM REM)) ;;
              Cmd.op (.nonEmpty TFLG REM) ;;
              Cmd.ifBit TFLG
                (Cmd.op (.clear GFLG))
                (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG)) ;;
              Cmd.op (.concat FSTART STEPSL STEPO) ;;
              Cmd.ifBit GFLG
                (Cmd.op (.copy SCAN FBITS) ;; emitBitsFromScan FSTART FBITS)
                emitFalse ) ;;
          emitFalse )
        (Cmd.op (.clear KTMP)) ) ;;
  emitFalse

/-! ### The wellformedness guard (reproduce `BinaryCC_wellformed` on-machine). -/

/-- AND `(bit in FLG)` into `GWF`. -/
def andFlag (FLG : Nat) : Cmd :=
  Cmd.ifBit FLG (Cmd.op (.clear ZERO)) (Cmd.op (.clear GWF))

/-- `TFLG := [1]` iff `|X| ≤ |Y|` (truncated subtraction). -/
def leCheck (X Y : Nat) : Cmd :=
  Cmd.op (.copy MREM X) ;;
  Cmd.forBnd MGE Y (Cmd.op (.tail MREM MREM)) ;;
  Cmd.op (.nonEmpty TFLG MREM) ;;
  Cmd.ifBit TFLG (Cmd.op (.clear TFLG)) (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))

/-- `TFLG := [1]` iff `|D|` divides `|X|` (`D>0`), via `X mod D` by truncated
repeated subtraction. -/
def dvdCheck (X D : Nat) : Cmd :=
  Cmd.op (.copy MREM X) ;;
  Cmd.forBnd KTMP X
    ( Cmd.op (.copy MCHK D) ;;
      Cmd.forBnd KTMP2 MREM (Cmd.op (.tail MCHK MCHK)) ;;
      Cmd.op (.nonEmpty MGE MCHK) ;;
      Cmd.ifBit MGE
        (Cmd.op (.clear ZERO))
        (Cmd.forBnd KTMP2 D (Cmd.op (.tail MREM MREM))) ) ;;
  Cmd.op (.nonEmpty TFLG MREM) ;;
  Cmd.ifBit TFLG (Cmd.op (.clear TFLG)) (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))

/-- Per-item length parse (prem or conc): consume one `encSList` off `SCANW`,
count its bits into `CLEN`, and AND `1^len = 1^width` into `GWF`. -/
def cardLenItem : Cmd :=
  Cmd.op (.clear CLEN) ;; Cmd.op (.clear DONE) ;;
  Cmd.forBnd KBIT SCANW
    ( Cmd.ifBit DONE (Cmd.op (.clear ZERO))
        ( Cmd.op (.head EMARK SCANW) ;;
          Cmd.ifBit EMARK
            ( Cmd.op (.tail SCANW SCANW) ;; Cmd.op (.head TFLG SCANW) ;;
              Cmd.ifBit TFLG (Cmd.op (.tail SCANW SCANW) ;; Cmd.op (.tail SCANW SCANW))
                             (Cmd.op (.tail SCANW SCANW)) ;;
              Cmd.op (.appendOne CLEN) )
            ( Cmd.op (.tail SCANW SCANW) ;;
              Cmd.op (.clear DONE) ;; Cmd.op (.appendOne DONE) ) ) ) ;;
  Cmd.op (.eqBit TFLG CLEN WIDTH) ;; andFlag TFLG

/-- Every card's prem and conc length `= width`, ANDed into `GWF`. -/
def cardLenCheck : Cmd :=
  Cmd.op (.copy SCANW CARDS) ;;
  Cmd.forBnd KCARD CARDS
    ( Cmd.op (.nonEmpty TFLG SCANW) ;;
      Cmd.ifBit TFLG
        (cardLenItem ;; cardLenItem)
        (Cmd.op (.clear KTMP)) )

/-- The full wellformedness flag into `GWF` (assumes `precompLen` ran). -/
def computeWF : Cmd :=
  Cmd.op (.clear GWF) ;; Cmd.op (.appendOne GWF) ;;
  Cmd.op (.nonEmpty TFLG WIDTH) ;; andFlag TFLG ;;         -- width > 0
  Cmd.op (.nonEmpty TFLG OFFSET) ;; andFlag TFLG ;;        -- offset > 0
  leCheck WIDTH LREG ;; andFlag TFLG ;;                    -- width ≤ L
  dvdCheck WIDTH OFFSET ;; andFlag TFLG ;;                 -- offset | width
  dvdCheck LREG OFFSET ;; andFlag TFLG ;;                  -- offset | L
  cardLenCheck                                             -- ∀ card, |prem|=|conc|=width

/-! ### The input encoding (pinned to the BinaryCC exit frame) and the program. -/

/-- `encodeIn C` on the pinned frame (regs 5/17/18/19/20/21), formats matching
`FlatCCBinFree`'s outputs so the future seam is a scrub. -/
def encodeIn (C : BinaryCC) : State :=
  ((((((List.replicate regFrame ([] : List Nat)).set STEPS (List.replicate C.steps 1)).set
    OFFSET (List.replicate C.offset 1)).set
    WIDTH (List.replicate C.width 1)).set
    INIT (FlatCCBinFree.bitsNat C.init)).set
    CARDS (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))).set
    FINAL (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat))

/-! ## 2b. `encodeIn_size` — the input encoding is linear (session 3, step 1)

`encodeIn` writes six fields into an otherwise-empty `regFrame`-register frame;
`State.size` is additive over `State.set` on a fresh (all-`[]`) register
(`State.size_set_add`), so the total is exactly the sum of the six field
lengths. Each of `offset`/`width`/`steps` contributes its own value (unary),
`init` contributes its bit length, and `cards`/`final` contribute their
sentinel-encoded lengths, bounded via the *generic* `encCardsOut_length_le`/
`encFinal_length_le` (`FlatCC_to_BinaryCC_free.lean`/`FlatTCC_to_FlatCC_free.lean`)
composed with the fact that `bitsNat`/`cardNat` (`Bool → Nat`, `CCCard Bool →
CCCard Nat`) preserve `encodable.size` exactly (0/1 values have the same size
as `Bool`). -/

private theorem list_length_le_size {α : Type} [encodable α] :
    ∀ xs : List α, xs.length ≤ encodable.size xs
  | [] => by simp [encodable.size]
  | x :: xs => by
      have ih := list_length_le_size xs
      rw [encodable_size_list_cons]
      simp only [List.length_cons]
      omega

theorem encodable_size_bitsNat (bs : List Bool) :
    encodable.size (FlatCCBinFree.bitsNat bs) = encodable.size bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      show encodable.size (cond b 1 0 :: FlatCCBinFree.bitsNat bs)
          = encodable.size (b :: bs)
      rw [encodable_size_list_cons, encodable_size_list_cons, ih]
      cases b <;> rfl

theorem encodable_size_cardNat (c : CCCard Bool) :
    encodable.size (FlatCCBinFree.cardNat c) = encodable.size c := by
  show encodable.size (FlatCCBinFree.bitsNat c.prem)
      + encodable.size (FlatCCBinFree.bitsNat c.conc) + 1
      = encodable.size c.prem + encodable.size c.conc + 1
  rw [encodable_size_bitsNat, encodable_size_bitsNat]

theorem encodable_size_map_cardNat (cs : List (CCCard Bool)) :
    encodable.size (cs.map FlatCCBinFree.cardNat) = encodable.size cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show encodable.size (FlatCCBinFree.cardNat c :: cs.map FlatCCBinFree.cardNat)
          = encodable.size (c :: cs)
      rw [encodable_size_list_cons, encodable_size_list_cons, ih, encodable_size_cardNat]

theorem encodable_size_map_bitsNat (fss : List (List Bool)) :
    encodable.size (fss.map FlatCCBinFree.bitsNat) = encodable.size fss := by
  induction fss with
  | nil => rfl
  | cons s fss ih =>
      show encodable.size (FlatCCBinFree.bitsNat s :: fss.map FlatCCBinFree.bitsNat)
          = encodable.size (s :: fss)
      rw [encodable_size_list_cons, encodable_size_list_cons, ih, encodable_size_bitsNat]

private theorem replicate_nil_size_gen :
    ∀ n : Nat, State.size (List.replicate n ([] : List Nat)) = 0
  | 0 => rfl
  | n + 1 => by
      show List.length ([] : List Nat) + State.size (List.replicate n ([] : List Nat)) = 0
      simp [replicate_nil_size_gen n]

private theorem regFrame_replicate_size :
    State.size (List.replicate regFrame ([] : List Nat)) = 0 :=
  replicate_nil_size_gen regFrame

private theorem regFrame_replicate_get (v : Nat) (h : v < regFrame) :
    State.get (List.replicate regFrame ([] : List Nat)) v = [] := by
  unfold State.get
  rw [List.getElem?_eq_getElem (by simpa using h), List.getElem_replicate]
  rfl

/-- A `.set` on a not-yet-touched (`[]`) register adds exactly the new
register's length to `State.size` — the additive bookkeeping step reused six
times below (once per `encodeIn` field). -/
private theorem fresh_set_size (s : State) (dst : Var) (v : List Nat)
    (h : State.get s dst = []) :
    State.size (s.set dst v) = State.size s + v.length := by
  have hh := State.size_set_add s dst v
  rw [h, List.length_nil] at hh
  omega

/-- If `r` is untouched in `s` and `r ≠ dst`, it stays untouched after `s.set
dst val` — the one-step frame fact chained (2/3/4/5 times) below to reach back
to the all-`[]` base for each of the six `encodeIn` fields. -/
private theorem get_unset_of_ne (s : State) (dst : Var) (val : List Nat) (r : Var)
    (hr : r ≠ dst) (h : State.get s r = []) : State.get (s.set dst val) r = [] :=
  (State.get_set_ne s dst val r hr).trans h

/-! The six-stage `.set` chain making up `encodeIn`, named so the size/frame
bookkeeping below can refer to each intermediate frame (`abbrev`, so `rfl`/
`show` sees through them to match `encodeIn`'s own definition). -/
private abbrev s0C : State := List.replicate regFrame ([] : List Nat)
private abbrev s1C (C : BinaryCC) : State := s0C.set STEPS (List.replicate C.steps 1)
private abbrev s2C (C : BinaryCC) : State := (s1C C).set OFFSET (List.replicate C.offset 1)
private abbrev s3C (C : BinaryCC) : State := (s2C C).set WIDTH (List.replicate C.width 1)
private abbrev s4C (C : BinaryCC) : State := (s3C C).set INIT (FlatCCBinFree.bitsNat C.init)
private abbrev s5C (C : BinaryCC) : State :=
  (s4C C).set CARDS (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))

/-- **`encodeIn`'s size is linear** in the instance size (no doubling). -/
theorem encodeIn_size_le (C : BinaryCC) :
    State.size (encodeIn C) ≤ 2 * encodable.size C + 1 := by
  have hC : encodable.size C
      = C.offset + C.width + encodable.size C.init + encodable.size C.cards
        + encodable.size C.final + C.steps + 1 := rfl
  have hget0 : ∀ v : Nat, v < regFrame → State.get s0C v = [] := regFrame_replicate_get
  have e1 : State.size (s1C C) = C.steps := by
    rw [fresh_set_size s0C STEPS (List.replicate C.steps 1) (hget0 STEPS (by decide)),
      regFrame_replicate_size, List.length_replicate]
    omega
  have hget1 : State.get (s1C C) OFFSET = [] :=
    get_unset_of_ne s0C STEPS (List.replicate C.steps 1) OFFSET (by decide)
      (hget0 OFFSET (by decide))
  have e2 : State.size (s2C C) = C.steps + C.offset := by
    rw [fresh_set_size (s1C C) OFFSET (List.replicate C.offset 1) hget1, e1,
      List.length_replicate]
  have hget2 : State.get (s2C C) WIDTH = [] :=
    get_unset_of_ne (s1C C) OFFSET (List.replicate C.offset 1) WIDTH (by decide)
      (get_unset_of_ne s0C STEPS (List.replicate C.steps 1) WIDTH (by decide)
        (hget0 WIDTH (by decide)))
  have e3 : State.size (s3C C) = C.steps + C.offset + C.width := by
    rw [fresh_set_size (s2C C) WIDTH (List.replicate C.width 1) hget2, e2,
      List.length_replicate]
  have hget3 : State.get (s3C C) INIT = [] :=
    get_unset_of_ne (s2C C) WIDTH (List.replicate C.width 1) INIT (by decide)
      (get_unset_of_ne (s1C C) OFFSET (List.replicate C.offset 1) INIT (by decide)
        (get_unset_of_ne s0C STEPS (List.replicate C.steps 1) INIT (by decide)
          (hget0 INIT (by decide))))
  have e4 : State.size (s4C C) = C.steps + C.offset + C.width
      + (FlatCCBinFree.bitsNat C.init).length := by
    rw [fresh_set_size (s3C C) INIT (FlatCCBinFree.bitsNat C.init) hget3, e3]
  have hget4 : State.get (s4C C) CARDS = [] :=
    get_unset_of_ne (s3C C) INIT (FlatCCBinFree.bitsNat C.init) CARDS (by decide)
      (get_unset_of_ne (s2C C) WIDTH (List.replicate C.width 1) CARDS (by decide)
        (get_unset_of_ne (s1C C) OFFSET (List.replicate C.offset 1) CARDS (by decide)
          (get_unset_of_ne s0C STEPS (List.replicate C.steps 1) CARDS (by decide)
            (hget0 CARDS (by decide)))))
  have e5 : State.size (s5C C) = C.steps + C.offset + C.width
      + (FlatCCBinFree.bitsNat C.init).length
      + (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length := by
    rw [fresh_set_size (s4C C) CARDS
      (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) hget4, e4]
  have hget5 : State.get (s5C C) FINAL = [] :=
    get_unset_of_ne (s4C C) CARDS
      (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) FINAL (by decide)
      (get_unset_of_ne (s3C C) INIT (FlatCCBinFree.bitsNat C.init) FINAL (by decide)
        (get_unset_of_ne (s2C C) WIDTH (List.replicate C.width 1) FINAL (by decide)
          (get_unset_of_ne (s1C C) OFFSET (List.replicate C.offset 1) FINAL (by decide)
            (get_unset_of_ne s0C STEPS (List.replicate C.steps 1) FINAL (by decide)
              (hget0 FINAL (by decide))))))
  have e6 : State.size (encodeIn C) = C.steps + C.offset + C.width
      + (FlatCCBinFree.bitsNat C.init).length
      + (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length
      + (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length := by
    show State.size ((s5C C).set FINAL
        (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat))) = _
    rw [fresh_set_size (s5C C) FINAL
      (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)) hget5, e5]
  have hinit_len : (FlatCCBinFree.bitsNat C.init).length ≤ encodable.size C.init := by
    rw [show (FlatCCBinFree.bitsNat C.init).length = C.init.length from
      List.length_map _]
    exact list_length_le_size C.init
  have hcards_len : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length
      ≤ 2 * encodable.size C.cards := by
    rw [← encodable_size_map_cardNat C.cards]
    exact FlatCCBinFree.encCardsOut_length_le _
  have hfinal_len : (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length
      ≤ 2 * encodable.size C.final := by
    rw [← encodable_size_map_bitsNat C.final]
    exact FlatTCCFree.encFinal_length_le _
  omega


/-- **The reduction program**: precompute lengths, compute the wellformedness
flag, and either serialize the tableau (`fand init (fand steps final)`) or write
`serF falseFml`, into `FOUT`. -/
def buildFSAT : Cmd :=
  precompLen ;;
  computeWF ;;
  Cmd.op (.clear OUT) ;;
  Cmd.ifBit GWF
    ( emitFandTag ;;
      Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
      emitBitsFromScan ZERO INIT ;;
      emitFandTag ;;
      emitAllSteps ;;
      emitFinal )
    emitFalse ;;
  Cmd.op (.copy FOUT OUT)

/-! ## DESIGN COMPLETE — NEXT-SESSION PLAN (top-down session 3): the run/cost proofs

Session 2 delivered the **fully `#eval`-validated program** `buildFSAT` +
`encodeIn` (probe `checkFull`, wellformed & non-wellformed instances). Design is
GO on every count: the tree serialization, the unary var-index arithmetic
(`line*L + step*offset (+i)` via `concat`/mul-loops), and the on-machine guard
(`computeWF`) all reproduce `BinaryCC_to_FSAT_instance` exactly. What remains is
the `PolyTimeComputableLang BinaryCC_to_FSAT_instance` witness — pure proof work,
no design risk. Ordered (templates in `FlatCC_to_BinaryCC_free.lean`):

1. **`encodeIn_size ≤ 2·size+1`** — all unary/bit, no doubling. `State.size` of
   the pinned frame; mirror `flatCCBin_reductionLang.encodeIn_size`. Needs a
   length lemma for `encCardsOut`/`encFinal` (reuse `encCardsOut_length_le`/
   `encFinal_length_le`).
2. **Run lemmas bottom-up** — the crux. Prove, mirroring `sentStep_run`/
   `initStep_run` fold invariants:
   - `emitBitsFromScan_run` / `emitBitsFromSent_run`: after the loop,
     `OUT = OUT₀ ++ serF (encodeBitsAt start bits)` and (for `_Sent`) `SCAN`
     advanced past the terminator. Fold invariant on the bit index `i`.
   - `emitCardsAt_run`, `emitAllSteps_run`, `readOneFinal_run`, `emitFinal_run`:
     compose the leaf lemmas over the `listAnd`/`listOr` folds, using the
     algebraic `serF (listAnd/​listOr …)` identities.
   - `computeWF_run`: `(computeWF.eval …).get GWF = if BinaryCC_wellformed C
     then [1] else []`. Needs `dvdCheck`/`leCheck`/`cardLenCheck` correctness
     (unary modulo ⇔ `∣`; `1^a = 1^b ↔ a = b`). Guard-necessity is real:
     `encodeTableau_correct` assumes `hWf`, so `computes` needs the guard.
   - `buildFSAT_run : (buildFSAT.eval (encodeIn C)).get FOUT =
     serF (BinaryCC_to_FSAT_instance C)` — assemble the above + `computeWF_run`
     branch. `computes` = `decodeOut_of_serF` + `buildFSAT_run`.
3. **`cost_le`** — a low-degree polynomial (nested-loop product). Confirm the
   degree with a `cost_forBnd_le` accounting pass (cf. CliqueRel quartic→quintic,
   and `binBudget_le_poly`). The unary var-index mul-loops are `Θ(index)` with
   `Θ(steps·L)` indices, so the honest bound is a fixed-degree polynomial.
   `output_size_le` reuses `BinaryCC_to_FSAT_instance_size_bound`.
4. **`enc_bit`/`usesBelow`/`width_le`/`decode_agree`** — mechanical
   (`regBound := regFrame + 2·buildFSAT.loopDepth`; copy the discharge in
   `flatCCBin_reductionLang`). Then `reducesPolyMO'_of_langFree …
   BinaryCC_to_FSAT_instance_correct` gives `BinaryCC ⪯p' FSAT`.
5. **The seam** `Reductions/BinaryCC_to_FSAT_comp.lean` (copy
   `FlatTCC_to_BinaryCC_comp.lean`): a scrub joining `flatTCC_to_binaryCC`'s exit
   frame to `encodeIn` here → the whole sound tail `FlatTCC → … → FSAT` as ONE
   composed live `⪯p'`. `encodeIn` is already pinned to that exit frame, so the
   seam is near-pure.
-/

end BinaryCCFSATFree
