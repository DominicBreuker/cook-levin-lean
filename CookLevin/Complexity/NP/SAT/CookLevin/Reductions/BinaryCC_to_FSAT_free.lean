import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT
import Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC_free
import Complexity.Lang.PolyTime
import Complexity.Lang.CostFlat

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

private theorem emitForrTag_run (s : State) :
    emitForrTag.eval s = s.set OUT (s.get OUT ++ [1, 0]) := by
  simp only [emitForrTag, Cmd.eval_seq, emit0_run, emit1_run, State.get_set_eq, State.set_set,
    List.append_assoc]
  rfl

private theorem emitFalse_run (s : State) :
    emitFalse.eval s = s.set OUT (s.get OUT ++ [1, 1, 0, 0, 0]) := by
  simp only [emitFalse, Cmd.eval_seq, emit0_run, emit1_run, State.get_set_eq, State.set_set,
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

private theorem emitForrTag_frame (s : State) (r : Var) (hr : r ≠ OUT) :
    State.get (emitForrTag.eval s) r = State.get s r := by
  simp only [emitForrTag, Cmd.eval_seq, emit0_run, emit1_run, State.get_set_ne _ _ _ _ hr]

private theorem emitFalse_frame (s : State) (r : Var) (hr : r ≠ OUT) :
    State.get (emitFalse.eval s) r = State.get s r := by
  simp only [emitFalse, Cmd.eval_seq, emit0_run, emit1_run, State.get_set_ne _ _ _ _ hr]

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
        = State.get u OUT ++ serF (BinaryCCToFSAT.encodeBitsAt start bits)
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
        State.get ((emitBitsFromScan BASE bound).eval u) r = State.get u r) := by
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
  obtain ⟨hSCANl, hOUTl, hframel⟩ := hInv
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
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
        State.get (emitFtrue.eval ((Cmd.forBnd KBIT bound _).eval u)) r = State.get u r)
  rw [heval]
  refine ⟨?_, ?_, ?_⟩
  · rw [emitFtrue_frame _ SCAN (by decide), hSCANl, List.drop_eq_nil_of_le (le_refl bits.length)]
    rfl
  · rw [emitFtrue_run, State.get_set_eq, hOUTl, List.take_of_length_le (le_refl bits.length),
      List.append_assoc, ← serF_encodeBitsAt]
  · intro r h1 h2 h3 h4 h5
    rw [emitFtrue_frame _ r h2, hframel r h1 h2 h3 h4 h5]

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

/-- One iteration of the card loop (the body of `emitCardsAt`'s loop, factored
out so its run lemma can name it): if the card stream copy `SCAN` is nonempty,
emit one card's `forr`-tag + `encodeCardAt` (its two bit-lists via the two
sentinel emitters); idle otherwise. -/
def cardEmitBody : Cmd :=
  Cmd.op (.nonEmpty TFLG SCAN) ;;
  Cmd.ifBit TFLG
    ( emitForrTag ;; emitFandTag ;;
      emitBitsFromSent STARTA ;;
      emitBitsFromSent STARTB )
    (Cmd.op (.clear KTMP))

/-- `serF (encodeCardsAt C startA startB)` = `listOr` over cards, consuming a
copy of the card stream. `STARTA = 1^startA`, `STARTB = 1^startB` pre-set. -/
def emitCardsAt : Cmd :=
  Cmd.op (.copy SCAN CARDS) ;;
  Cmd.forBnd KCARD CARDS cardEmitBody ;;
  emitFalse

/-! ### `emitCardsAt_run` — the per-position card disjunction

The `listOr`-over-cards analogue of the `bitsPrefix` stack, one level up:
`cardsPrefix` is the tag-then-card unrolling of `serF (listOr (cards.map
(encodeCardAt sA sB)))` **without** the closing `falseFml`, accumulated one
card per live loop iteration off the sentinel card stream; `emitFalse` closes
it (`serF_encodeCardsAt`). The inner emitters are the black-boxed
`emitBitsFromSent_run` — its past-the-terminator `SCAN` clause is exactly what
lets the two calls (prem, conc) chain. -/

/-- The tag+card serialization prefix at fixed positions (no closing
`falseFml`) — `OUT`'s accumulation after a processed card-list prefix. -/
def cardsPrefix (sA sB : Nat) : List (CCCard Bool) → List Nat
  | [] => []
  | c :: cs => [1, 0] ++ serF (encodeCardAt sA sB c) ++ cardsPrefix sA sB cs

theorem cardsPrefix_append (sA sB : Nat) (xs ys : List (CCCard Bool)) :
    cardsPrefix sA sB (xs ++ ys) = cardsPrefix sA sB xs ++ cardsPrefix sA sB ys := by
  induction xs with
  | nil => simp [cardsPrefix]
  | cons c cs ih =>
      simp only [List.cons_append, cardsPrefix, ih, List.append_assoc]

/-- Closing the accumulated card prefix with `falseFml` gives exactly the
serialized card disjunction — `emitCardsAt`'s algebraic target
(`encodeCardsAt C sA sB` is `listOr (C.cards.map (encodeCardAt sA sB))`). -/
theorem serF_encodeCardsAt (sA sB : Nat) (cs : List (CCCard Bool)) :
    serF (listOr (cs.map (encodeCardAt sA sB)))
      = cardsPrefix sA sB cs ++ serF falseFml := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show serF (.forr (encodeCardAt sA sB c) (listOr (cs.map (encodeCardAt sA sB)))) = _
      simp [serF, cardsPrefix, ih, List.append_assoc]

/-- The card stream's cons view: one card contributes its two sentinel
bit-lists (prem then conc), pre-associated for the two chained emitters. -/
private theorem encCardsOut_cons (c : CCCard Bool) (cs : List (CCCard Bool)) :
    FlatTCCFree.encCardsOut ((c :: cs).map FlatCCBinFree.cardNat)
      = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
        ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc)
          ++ FlatTCCFree.encCardsOut (cs.map FlatCCBinFree.cardNat)) := by
  show (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
      ++ FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc))
      ++ FlatTCCFree.encCardsOut (cs.map FlatCCBinFree.cardNat) = _
  rw [List.append_assoc]

/-- A sentinel list is never empty (element marker `1` or bare terminator
`0`) — what fires the card loop's `nonEmpty` guard. -/
private theorem encSList_append_isEmpty (xs A : List Nat) :
    (FlatTCCFree.encSList xs ++ A).isEmpty = false := by
  cases xs with
  | nil => rfl
  | cons v vs => rfl

/-- The card stream is at least as long as the card count (each card occupies
≥ 2 cells) — the loop bound `CARDS` covers every card. -/
private theorem length_le_encCardsOut (cs : List (CCCard Bool)) :
    cs.length ≤ (FlatTCCFree.encCardsOut (cs.map FlatCCBinFree.cardNat)).length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      rw [encCardsOut_cons, List.length_cons, List.length_append, List.length_append]
      have h1 := FlatTCCFree.encSList_length_pos (FlatCCBinFree.bitsNat c.prem)
      omega

/-- The card-loop fold invariant: `SCAN` holds the unprocessed card stream,
`OUT` the serialized card prefix; `ZERO` stays empty for the inner emitters. -/
private def CAInv (sA sB : Nat) (cards : List (CCCard Bool)) (u : State) (j : Nat)
    (st : State) : Prop :=
  State.get st SCAN
      = FlatTCCFree.encCardsOut ((cards.drop j).map FlatCCBinFree.cardNat)
  ∧ State.get st OUT = State.get u OUT ++ cardsPrefix sA sB (cards.take j)
  ∧ State.get st ZERO = []
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
      r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KCARD →
      State.get st r = State.get u r)

private theorem CAInv_step (sA sB : Nat) (cards : List (CCCard Bool)) (u : State)
    (hSA : State.get u STARTA = List.replicate sA 1)
    (hSB : State.get u STARTB = List.replicate sB 1)
    (j : Nat) (st : State) (h : CAInv sA sB cards u j st) :
    CAInv sA sB cards u (j + 1)
      (cardEmitBody.eval (st.set KCARD (List.replicate j 1))) := by
  obtain ⟨hSCAN, hOUT, hZERO, hframe⟩ := h
  set w := st.set KCARD (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KCARD → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSCAN : State.get w SCAN
      = FlatTCCFree.encCardsOut ((cards.drop j).map FlatCCBinFree.cardNat) := by
    rw [hwframe SCAN (by decide)]; exact hSCAN
  have hwOUT : State.get w OUT = State.get u OUT ++ cardsPrefix sA sB (cards.take j) := by
    rw [hwframe OUT (by decide)]; exact hOUT
  have hwZ : State.get w ZERO = [] := by
    rw [hwframe ZERO (by decide)]; exact hZERO
  have hwSA : State.get w STARTA = List.replicate sA 1 := by
    rw [hwframe STARTA (by decide), hframe STARTA (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hSA
  have hwSB : State.get w STARTB = List.replicate sB 1 := by
    rw [hwframe STARTB (by decide), hframe STARTB (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hSB
  clear_value w
  by_cases hj : j < cards.length
  · -- live iteration: one card off the stream
    have hdrop : cards.drop j = cards[j] :: cards.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    have htake : cards.take (j + 1) = cards.take j ++ [cards[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    set c := cards[j] with hc
    clear_value c
    set REST := FlatTCCFree.encCardsOut ((cards.drop (j + 1)).map FlatCCBinFree.cardNat)
      with hREST
    have hSCANw : State.get w SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
          ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hwSCAN, hdrop, encCardsOut_cons, hREST]
    have hne : (State.get w SCAN).isEmpty = false := by
      rw [hSCANw]; exact encSList_append_isEmpty _ _
    have e1 : (Cmd.op (.nonEmpty TFLG SCAN)).eval w = w.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w1 := w.set TFLG [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ TFLG → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1T : State.get w1 TFLG = [1] := State.get_set_eq _ _ _
    have hw1OUT : State.get w1 OUT
        = State.get u OUT ++ cardsPrefix sA sB (cards.take j) := by
      rw [hw1frame OUT (by decide)]; exact hwOUT
    clear_value w1
    set w2 := emitForrTag.eval w1 with hw2
    have hw2frame : ∀ r : Var, r ≠ OUT → State.get w2 r = State.get w1 r := by
      intro r hr; rw [hw2]; exact emitForrTag_frame w1 r hr
    have hw2OUT : State.get w2 OUT = State.get w1 OUT ++ [1, 0] := by
      rw [hw2, emitForrTag_run]; exact State.get_set_eq _ _ _
    clear_value w2
    set w3 := emitFandTag.eval w2 with hw3
    have hw3frame : ∀ r : Var, r ≠ OUT → State.get w3 r = State.get w2 r := by
      intro r hr; rw [hw3]; exact emitFandTag_frame w2 r hr
    have hw3OUT : State.get w3 OUT = State.get w2 OUT ++ [0, 1] := by
      rw [hw3, emitFandTag_run]; exact State.get_set_eq _ _ _
    clear_value w3
    have hw3SCAN : State.get w3 SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
          ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hw3frame SCAN (by decide), hw2frame SCAN (by decide),
        hw1frame SCAN (by decide)]
      exact hSCANw
    have hw3Z : State.get w3 ZERO = [] := by
      rw [hw3frame ZERO (by decide), hw2frame ZERO (by decide),
        hw1frame ZERO (by decide)]
      exact hwZ
    have hw3SA : State.get w3 STARTA = List.replicate sA 1 := by
      rw [hw3frame STARTA (by decide), hw2frame STARTA (by decide),
        hw1frame STARTA (by decide)]
      exact hwSA
    have hw3SB : State.get w3 STARTB = List.replicate sB 1 := by
      rw [hw3frame STARTB (by decide), hw2frame STARTB (by decide),
        hw1frame STARTB (by decide)]
      exact hwSB
    -- the prem emitter
    obtain ⟨h4SCAN, h4OUT, h4Z, h4frame⟩ :=
      emitBitsFromSent_run STARTA sA c.prem
        (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) w3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) hw3SA hw3Z hw3SCAN
    set w4 := (emitBitsFromSent STARTA).eval w3 with hw4
    have hw4SB : State.get w4 STARTB = List.replicate sB 1 := by
      rw [h4frame STARTB (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
      exact hw3SB
    clear_value w4
    -- the conc emitter
    obtain ⟨h5SCAN, h5OUT, h5Z, h5frame⟩ :=
      emitBitsFromSent_run STARTB sB c.conc REST w4
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) hw4SB h4Z h4SCAN
    set w5 := (emitBitsFromSent STARTB).eval w4 with hw5
    clear_value w5
    have heval : cardEmitBody.eval w = w5 := by
      unfold cardEmitBody
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_true _ _ _ _ hw1T, Cmd.eval_seq, ← hw2,
        Cmd.eval_seq, ← hw3, Cmd.eval_seq, ← hw4, ← hw5]
    rw [heval]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h5SCAN]
    · rw [h5OUT, h4OUT, hw3OUT, hw2OUT, hw1OUT, htake, cardsPrefix_append]
      simp [cardsPrefix, encodeCardAt, serF, List.append_assoc]
    · exact h5Z
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rw [h5frame r h1 h2 h3 h4 h5 h6 h7 h8, h4frame r h1 h2 h3 h4 h5 h6 h7 h8,
        hw3frame r h2, hw2frame r h2, hw1frame r h4, hwframe r h10,
        hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]
  · -- idle iteration: stream exhausted, `nonEmpty` guard falls through
    have hlen : cards.length ≤ j := Nat.le_of_not_lt hj
    have hSCANw : State.get w SCAN = [] := by
      rw [hwSCAN, List.drop_eq_nil_of_le hlen]
      rfl
    have hne : (State.get w SCAN).isEmpty = true := by rw [hSCANw]; rfl
    have e1 : (Cmd.op (.nonEmpty TFLG SCAN)).eval w = w.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w1 := w.set TFLG [0] with hw1
    have hw1T : State.get w1 TFLG ≠ [1] := by
      rw [hw1, State.get_set_eq]; decide
    have e2 : (Cmd.op (.clear KTMP)).eval w1 = w1.set KTMP [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    set wF := w1.set KTMP [] with hwF
    have heval : cardEmitBody.eval w = wF := by
      unfold cardEmitBody
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_false _ _ _ _ hw1T, e2]
    have hgetF : ∀ r : Var, r ≠ TFLG → r ≠ KTMP → State.get wF r = State.get w r := by
      intro r h1 h2
      rw [hwF, State.get_set_ne _ _ _ _ h2, hw1, State.get_set_ne _ _ _ _ h1]
    rw [heval]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hgetF SCAN (by decide) (by decide), hwSCAN, List.drop_eq_nil_of_le hlen,
        List.drop_eq_nil_of_le (by omega)]
    · rw [hgetF OUT (by decide) (by decide), hwOUT, List.take_of_length_le hlen,
        List.take_of_length_le (by omega)]
    · rw [hgetF ZERO (by decide) (by decide)]; exact hwZ
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rw [hgetF r h4 h9, hwframe r h10, hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]

/-- **`emitCardsAt` is correct**: with `STARTA = 1^sA`, `STARTB = 1^sB` and
the pinned card stream in `CARDS`, it appends `serF (encodeCardsAt C sA sB)`
to `OUT` (consuming a scratch copy of the stream, so `CARDS` itself is
untouched — it is outside the scratch set). -/
theorem emitCardsAt_run (sA sB : Nat) (C : BinaryCC) (u : State)
    (hSA : State.get u STARTA = List.replicate sA 1)
    (hSB : State.get u STARTB = List.replicate sB 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = []) :
    State.get (emitCardsAt.eval u) OUT
        = State.get u OUT ++ serF (encodeCardsAt C sA sB)
    ∧ State.get (emitCardsAt.eval u) ZERO = []
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
        r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KCARD →
        State.get (emitCardsAt.eval u) r = State.get u r) := by
  have e0 : (Cmd.op (.copy SCAN CARDS)).eval u
      = u.set SCAN (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hCARDS]
  set u1 := u.set SCAN (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    with hu1
  have hu1frame : ∀ r : Var, r ≠ SCAN → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1SC : State.get u1 SCAN
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    State.get_set_eq _ _ _
  have hu1SA : State.get u1 STARTA = List.replicate sA 1 := by
    rw [hu1frame STARTA (by decide)]; exact hSA
  have hu1SB : State.get u1 STARTB = List.replicate sB 1 := by
    rw [hu1frame STARTB (by decide)]; exact hSB
  have hu1Z : State.get u1 ZERO = [] := by
    rw [hu1frame ZERO (by decide)]; exact hZ
  have hu1OUT : State.get u1 OUT = State.get u OUT := hu1frame OUT (by decide)
  have hu1CARDS : State.get u1 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [hu1frame CARDS (by decide)]; exact hCARDS
  clear_value u1
  have hN : C.cards.length ≤ (State.get u1 CARDS).length := by
    rw [hu1CARDS]; exact length_le_encCardsOut C.cards
  have hbase : CAInv sA sB C.cards u 0 u1 := by
    refine ⟨by rw [List.drop_zero]; exact hu1SC, ?_, hu1Z,
      fun r h1 _ _ _ _ _ _ _ _ _ => hu1frame r h1⟩
    rw [List.take_zero, show cardsPrefix sA sB [] = [] from rfl, List.append_nil]
    exact hu1OUT
  have hInv : CAInv sA sB C.cards u (State.get u1 CARDS).length
      (Cmd.foldlState cardEmitBody KCARD
        (List.range (State.get u1 CARDS).length) u1) :=
    Cmd.foldlState_range_induct _ KCARD _ u1 (CAInv sA sB C.cards u) hbase
      (fun j st _ hM => CAInv_step sA sB C.cards u hSA hSB j st hM)
  obtain ⟨hSCf, hOUTf, hZf, hframef⟩ := hInv
  have heval : emitCardsAt.eval u
      = emitFalse.eval (Cmd.foldlState cardEmitBody KCARD
          (List.range (State.get u1 CARDS).length) u1) := by
    unfold emitCardsAt
    rw [Cmd.eval_seq, Cmd.eval_seq, e0, Cmd.eval_forBnd]
  refine ⟨?_, ?_, ?_⟩
  · rw [heval, emitFalse_run, State.get_set_eq, hOUTf, List.take_of_length_le hN,
      List.append_assoc,
      show serF (encodeCardsAt C sA sB)
          = cardsPrefix sA sB C.cards ++ serF falseFml
        from serF_encodeCardsAt sA sB C.cards]
    rfl
  · rw [heval, emitFalse_frame _ ZERO (by decide)]; exact hZf
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    rw [heval, emitFalse_frame _ r h2, hframef r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]

/-! ### Generic unary-arithmetic loops (register-parametric)

`FlatCCBinFree.mulLoop_run` is pinned to `IDXO`/`SIGMA`; the var-index sites
here multiply and subtract at several different register triples
(`STEPO`/`LINEL`/`STEPSL`/`REM`, bounds `KSTEP`/`KLINE`/`STEPS`/`LREG`), so
state the two loop shapes once, register-generically. -/

/-- Unary product: `forBnd cnt bnd (concat dst dst src)` on `dst = []`,
`src = 1^k`, `|bnd| = m` leaves `dst = 1^(m·k)`; only `dst`/`cnt` change. -/
theorem unaryMulLoop_run (cnt bnd src dst : Var) (s : State) (k m : Nat)
    (hds : dst ≠ src) (hdc : dst ≠ cnt) (hsc : src ≠ cnt)
    (hsrc : State.get s src = List.replicate k 1)
    (hbnd : (State.get s bnd).length = m)
    (hdst : State.get s dst = []) :
    State.get ((Cmd.forBnd cnt bnd (Cmd.op (.concat dst dst src))).eval s) dst
        = List.replicate (m * k) 1
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
        State.get ((Cmd.forBnd cnt bnd (Cmd.op (.concat dst dst src))).eval s) r
          = State.get s r) := by
  have hM : ∀ i st, i < m →
      (State.get st dst = List.replicate (i * k) 1
        ∧ ∀ r : Var, r ≠ dst → r ≠ cnt → State.get st r = State.get s r) →
      (State.get ((Cmd.op (.concat dst dst src)).eval
            (st.set cnt (List.replicate i 1))) dst
          = List.replicate ((i + 1) * k) 1
        ∧ ∀ r : Var, r ≠ dst → r ≠ cnt →
            State.get ((Cmd.op (.concat dst dst src)).eval
              (st.set cnt (List.replicate i 1))) r = State.get s r) := by
    intro i st _ h
    obtain ⟨hD, hF⟩ := h
    set w := st.set cnt (List.replicate i 1) with hw
    have hwD : State.get w dst = List.replicate (i * k) 1 := by
      rw [hw, State.get_set_ne _ _ _ _ hdc]; exact hD
    have hwS : State.get w src = List.replicate k 1 := by
      rw [hw, State.get_set_ne _ _ _ _ hsc, hF src (Ne.symm hds) hsc]; exact hsrc
    have he : (Cmd.op (.concat dst dst src)).eval w
        = w.set dst (List.replicate (i * k) 1 ++ List.replicate k 1) := by
      rw [Cmd.eval_op]; simp only [Op.eval, hwD, hwS]
    constructor
    · rw [he, State.get_set_eq, ← List.replicate_add]
      congr 1
      ring
    · intro r hr1 hr2
      rw [he, State.get_set_ne _ _ _ _ hr1, hw, State.get_set_ne _ _ _ _ hr2,
        hF r hr1 hr2]
  have hInv := Cmd.foldlState_range_induct (Cmd.op (.concat dst dst src)) cnt m s
    (fun i st => State.get st dst = List.replicate (i * k) 1
      ∧ ∀ r : Var, r ≠ dst → r ≠ cnt → State.get st r = State.get s r)
    ⟨by rw [hdst, Nat.zero_mul]; rfl, fun r _ _ => rfl⟩ hM
  have heval : (Cmd.forBnd cnt bnd (Cmd.op (.concat dst dst src))).eval s
      = Cmd.foldlState (Cmd.op (.concat dst dst src)) cnt (List.range m) s := by
    rw [Cmd.eval_forBnd, hbnd]
  exact ⟨by rw [heval]; exact hInv.1, fun r h1 h2 => by rw [heval]; exact hInv.2 r h1 h2⟩

/-- Truncated unary subtraction: `forBnd cnt bnd (tail dst dst)` on
`dst = 1^a`, `|bnd| = m` leaves `dst = 1^(a − m)`; only `dst`/`cnt` change. -/
theorem unarySubLoop_run (cnt bnd dst : Var) (s : State) (a m : Nat)
    (hdc : dst ≠ cnt)
    (hbnd : (State.get s bnd).length = m)
    (hdst : State.get s dst = List.replicate a 1) :
    State.get ((Cmd.forBnd cnt bnd (Cmd.op (.tail dst dst))).eval s) dst
        = List.replicate (a - m) 1
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
        State.get ((Cmd.forBnd cnt bnd (Cmd.op (.tail dst dst))).eval s) r
          = State.get s r) := by
  have hM : ∀ i st, i < m →
      (State.get st dst = List.replicate (a - i) 1
        ∧ ∀ r : Var, r ≠ dst → r ≠ cnt → State.get st r = State.get s r) →
      (State.get ((Cmd.op (.tail dst dst)).eval
            (st.set cnt (List.replicate i 1))) dst
          = List.replicate (a - (i + 1)) 1
        ∧ ∀ r : Var, r ≠ dst → r ≠ cnt →
            State.get ((Cmd.op (.tail dst dst)).eval
              (st.set cnt (List.replicate i 1))) r = State.get s r) := by
    intro i st _ h
    obtain ⟨hD, hF⟩ := h
    set w := st.set cnt (List.replicate i 1) with hw
    have hwD : State.get w dst = List.replicate (a - i) 1 := by
      rw [hw, State.get_set_ne _ _ _ _ hdc]; exact hD
    have he : (Cmd.op (.tail dst dst)).eval w
        = w.set dst (List.replicate (a - i) 1).tail := by
      rw [Cmd.eval_op]; simp only [Op.eval, hwD]
    have htail : (List.replicate (a - i) 1).tail = List.replicate (a - (i + 1)) 1 := by
      rw [List.tail_replicate, Nat.sub_sub]
    constructor
    · rw [he, State.get_set_eq, htail]
    · intro r hr1 hr2
      rw [he, State.get_set_ne _ _ _ _ hr1, hw, State.get_set_ne _ _ _ _ hr2,
        hF r hr1 hr2]
  have hInv := Cmd.foldlState_range_induct (Cmd.op (.tail dst dst)) cnt m s
    (fun i st => State.get st dst = List.replicate (a - i) 1
      ∧ ∀ r : Var, r ≠ dst → r ≠ cnt → State.get st r = State.get s r)
    ⟨by rw [hdst, Nat.sub_zero], fun r _ _ => rfl⟩ hM
  have heval : (Cmd.forBnd cnt bnd (Cmd.op (.tail dst dst))).eval s
      = Cmd.foldlState (Cmd.op (.tail dst dst)) cnt (List.range m) s := by
    rw [Cmd.eval_forBnd, hbnd]
  exact ⟨by rw [heval]; exact hInv.1, fun r h1 h2 => by rw [heval]; exact hInv.2 r h1 h2⟩

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

/-! ### `stepBody_run` — one step constraint

The var-index arithmetic (`STEPO = 1^(step·offset)` via `unaryMulLoop_run`,
`STARTA`/`STARTB`/`SUMW` by `concat`) plus the on-machine bound guard
(`REM = 1^(step·offset+width−L)` via `unarySubLoop_run`; empty ⟺
`step·offset+width ≤ L`) reproduce `encodeStepConstraint`'s dite exactly:
guard-pass emits `serF (encodeCardsAt …)` (black-boxed `emitCardsAt_run`),
guard-fail emits `serF ftrue`. -/
theorem stepBody_run (C : BinaryCC) (line step : Nat) (u : State)
    (hLINEL : State.get u LINEL = List.replicate (line * C.init.length) 1)
    (hKSTEP : State.get u KSTEP = List.replicate step 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hWID : State.get u WIDTH = List.replicate C.width 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = []) :
    State.get (stepBody.eval u) OUT
        = State.get u OUT ++ serF (encodeStepConstraint C line step)
    ∧ State.get (stepBody.eval u) ZERO = []
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
        r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KCARD →
        r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
        State.get (stepBody.eval u) r = State.get u r) := by
  -- w1: clear STEPO
  have e1 : (Cmd.op (.clear STEPO)).eval u = u.set STEPO [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w1 := u.set STEPO [] with hw1
  have hw1frame : ∀ r : Var, r ≠ STEPO → State.get w1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1STEPO : State.get w1 STEPO = [] := State.get_set_eq _ _ _
  have hw1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hw1frame OFFSET (by decide)]; exact hOFF
  have hw1KSTEPlen : (State.get w1 KSTEP).length = step := by
    rw [hw1frame KSTEP (by decide), hKSTEP, List.length_replicate]
  clear_value w1
  -- w2: the STEPO mul loop
  obtain ⟨h2STEPO, h2frame⟩ :=
    unaryMulLoop_run KTMP KSTEP OFFSET STEPO w1 C.offset step
      (by decide) (by decide) (by decide) hw1OFF hw1KSTEPlen hw1STEPO
  set w2 := (Cmd.forBnd KTMP KSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).eval w1
    with hw2
  clear_value w2
  have hw2LINEL : State.get w2 LINEL = List.replicate (line * C.init.length) 1 := by
    rw [h2frame LINEL (by decide) (by decide), hw1frame LINEL (by decide)]
    exact hLINEL
  -- w3: STARTA := LINEL ++ STEPO
  have e3 : (Cmd.op (.concat STARTA LINEL STEPO)).eval w2
      = w2.set STARTA (List.replicate (line * C.init.length + step * C.offset) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hw2LINEL, h2STEPO]
    congr 1
    rw [List.replicate_add]
  set w3 := w2.set STARTA (List.replicate (line * C.init.length + step * C.offset) 1)
    with hw3
  have hw3frame : ∀ r : Var, r ≠ STARTA → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3SA : State.get w3 STARTA
      = List.replicate (line * C.init.length + step * C.offset) 1 :=
    State.get_set_eq _ _ _
  have hw3LREG : State.get w3 LREG = List.replicate C.init.length 1 := by
    rw [hw3frame LREG (by decide), h2frame LREG (by decide) (by decide),
      hw1frame LREG (by decide)]
    exact hLREG
  clear_value w3
  -- w4: STARTB := STARTA ++ LREG
  have e4 : (Cmd.op (.concat STARTB STARTA LREG)).eval w3
      = w3.set STARTB (List.replicate
          (line * C.init.length + step * C.offset + C.init.length) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hw3SA, hw3LREG]
    congr 1
    rw [← List.replicate_add]
  set w4 := w3.set STARTB (List.replicate
      (line * C.init.length + step * C.offset + C.init.length) 1) with hw4
  have hw4frame : ∀ r : Var, r ≠ STARTB → State.get w4 r = State.get w3 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw4SB : State.get w4 STARTB
      = List.replicate (line * C.init.length + step * C.offset + C.init.length) 1 :=
    State.get_set_eq _ _ _
  have hw4STEPO : State.get w4 STEPO = List.replicate (step * C.offset) 1 := by
    rw [hw4frame STEPO (by decide), hw3frame STEPO (by decide)]; exact h2STEPO
  have hw4WID : State.get w4 WIDTH = List.replicate C.width 1 := by
    rw [hw4frame WIDTH (by decide), hw3frame WIDTH (by decide),
      h2frame WIDTH (by decide) (by decide), hw1frame WIDTH (by decide)]
    exact hWID
  clear_value w4
  -- w5: SUMW := STEPO ++ WIDTH
  have e5 : (Cmd.op (.concat SUMW STEPO WIDTH)).eval w4
      = w4.set SUMW (List.replicate (step * C.offset + C.width) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hw4STEPO, hw4WID]
    congr 1
    rw [List.replicate_add]
  set w5 := w4.set SUMW (List.replicate (step * C.offset + C.width) 1) with hw5
  have hw5frame : ∀ r : Var, r ≠ SUMW → State.get w5 r = State.get w4 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw5SUMW : State.get w5 SUMW = List.replicate (step * C.offset + C.width) 1 :=
    State.get_set_eq _ _ _
  clear_value w5
  -- w6: REM := copy SUMW
  have e6 : (Cmd.op (.copy REM SUMW)).eval w5
      = w5.set REM (List.replicate (step * C.offset + C.width) 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw5SUMW]
  set w6 := w5.set REM (List.replicate (step * C.offset + C.width) 1) with hw6
  have hw6frame : ∀ r : Var, r ≠ REM → State.get w6 r = State.get w5 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw6REM : State.get w6 REM = List.replicate (step * C.offset + C.width) 1 :=
    State.get_set_eq _ _ _
  have hw6LREGlen : (State.get w6 LREG).length = C.init.length := by
    rw [hw6frame LREG (by decide), hw5frame LREG (by decide),
      hw4frame LREG (by decide), hw3LREG, List.length_replicate]
  clear_value w6
  -- w7: the truncated-subtraction loop
  obtain ⟨h7REM, h7frame⟩ :=
    unarySubLoop_run KTMP LREG REM w6 (step * C.offset + C.width) C.init.length
      (by decide) hw6LREGlen hw6REM
  set w7 := (Cmd.forBnd KTMP LREG (Cmd.op (.tail REM REM))).eval w6 with hw7
  clear_value w7
  -- registers threaded to w7 (used by both guard branches)
  have h7chain : ∀ r : Var, r ≠ STEPO → r ≠ KTMP → r ≠ STARTA → r ≠ STARTB →
      r ≠ SUMW → r ≠ REM → State.get w7 r = State.get u r := by
    intro r h1 h2 h3 h4 h5 h6
    rw [h7frame r h6 h2, hw6frame r h6, hw5frame r h5, hw4frame r h4,
      hw3frame r h3, h2frame r h1 h2, hw1frame r h1]
  have h7OUT : State.get w7 OUT = State.get u OUT :=
    h7chain OUT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h7Z : State.get w7 ZERO = [] := by
    rw [h7chain ZERO (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hZ
  have h7CARDS : State.get w7 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [h7chain CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hCARDS
  have h7SA : State.get w7 STARTA
      = List.replicate (line * C.init.length + step * C.offset) 1 := by
    rw [h7frame STARTA (by decide) (by decide), hw6frame STARTA (by decide),
      hw5frame STARTA (by decide), hw4frame STARTA (by decide)]
    exact hw3SA
  have h7SB : State.get w7 STARTB
      = List.replicate (line * C.init.length + step * C.offset + C.init.length) 1 := by
    rw [h7frame STARTB (by decide) (by decide), hw6frame STARTB (by decide),
      hw5frame STARTB (by decide)]
    exact hw4SB
  by_cases hguard : step * C.offset + C.width ≤ C.init.length
  · -- guard passes: REM empty → GFLG := [1] → emitCardsAt
    have hREM0 : State.get w7 REM = [] := by
      rw [h7REM, Nat.sub_eq_zero_of_le hguard]
      rfl
    have hne : (State.get w7 REM).isEmpty = true := by rw [hREM0]; rfl
    have e8 : (Cmd.op (.nonEmpty TFLG REM)).eval w7 = w7.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w8 := w7.set TFLG [0] with hw8
    have hw8frame : ∀ r : Var, r ≠ TFLG → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8Tne : State.get w8 TFLG ≠ [1] := by
      rw [hw8, State.get_set_eq]; decide
    clear_value w8
    have ec : (Cmd.op (.clear GFLG)).eval w8 = w8.set GFLG [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    have ea : (Cmd.op (.appendOne GFLG)).eval (w8.set GFLG []) = w8.set GFLG [1] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, State.set_set, List.nil_append]
    have e9 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w8
        = w8.set GFLG [1] := by
      rw [Cmd.eval_ifBit_false _ _ _ _ hw8Tne, Cmd.eval_seq, ec, ea]
    set w9 := w8.set GFLG [1] with hw9
    have hw9frame : ∀ r : Var, r ≠ GFLG → State.get w9 r = State.get w8 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw9G : State.get w9 GFLG = [1] := State.get_set_eq _ _ _
    clear_value w9
    have h9SA : State.get w9 STARTA
        = List.replicate (line * C.init.length + step * C.offset) 1 := by
      rw [hw9frame STARTA (by decide), hw8frame STARTA (by decide)]; exact h7SA
    have h9SB : State.get w9 STARTB
        = List.replicate (line * C.init.length + step * C.offset + C.init.length) 1 := by
      rw [hw9frame STARTB (by decide), hw8frame STARTB (by decide)]; exact h7SB
    have h9CARDS : State.get w9 CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
      rw [hw9frame CARDS (by decide), hw8frame CARDS (by decide)]; exact h7CARDS
    have h9Z : State.get w9 ZERO = [] := by
      rw [hw9frame ZERO (by decide), hw8frame ZERO (by decide)]; exact h7Z
    have h9OUT : State.get w9 OUT = State.get u OUT := by
      rw [hw9frame OUT (by decide), hw8frame OUT (by decide)]; exact h7OUT
    obtain ⟨hFOUT, hFZ, hFframe⟩ :=
      emitCardsAt_run (line * C.init.length + step * C.offset)
        (line * C.init.length + step * C.offset + C.init.length) C w9
        h9SA h9SB h9CARDS h9Z
    set wF := emitCardsAt.eval w9 with hwF
    clear_value wF
    have hstep : encodeStepConstraint C line step
        = encodeCardsAt C (line * C.init.length + step * C.offset)
            (line * C.init.length + step * C.offset + C.init.length) := by
      unfold encodeStepConstraint
      rw [dif_pos hguard]
      congr 1
      rw [Nat.succ_mul]
      omega
    have heval : stepBody.eval u = wF := by
      unfold stepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, ← hw7, Cmd.eval_seq, e8,
        Cmd.eval_seq, e9, Cmd.eval_ifBit_true _ _ _ _ hw9G, ← hwF]
    refine ⟨?_, ?_, ?_⟩
    · rw [heval, hFOUT, h9OUT, hstep]
    · rw [heval]; exact hFZ
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      rw [heval, hFframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, hw9frame r h16,
        hw8frame r h4, h7frame r h15 h9, hw6frame r h15, hw5frame r h14,
        hw4frame r h13, hw3frame r h12, h2frame r h11 h9, hw1frame r h11]
  · -- guard fails: REM nonempty → GFLG := [] → emitFtrue
    obtain ⟨k, hk⟩ : ∃ k, step * C.offset + C.width - C.init.length = k + 1 :=
      ⟨step * C.offset + C.width - C.init.length - 1, by omega⟩
    have hne : (State.get w7 REM).isEmpty = false := by
      rw [h7REM, hk]
      rfl
    have e8 : (Cmd.op (.nonEmpty TFLG REM)).eval w7 = w7.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w8 := w7.set TFLG [1] with hw8
    have hw8frame : ∀ r : Var, r ≠ TFLG → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8T : State.get w8 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w8
    have e9 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w8
        = w8.set GFLG [] := by
      rw [Cmd.eval_ifBit_true _ _ _ _ hw8T, Cmd.eval_op]
      simp only [Op.eval]
    set w9 := w8.set GFLG [] with hw9
    have hw9frame : ∀ r : Var, r ≠ GFLG → State.get w9 r = State.get w8 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw9Gne : State.get w9 GFLG ≠ [1] := by
      rw [hw9, State.get_set_eq]; decide
    clear_value w9
    have h9OUT : State.get w9 OUT = State.get u OUT := by
      rw [hw9frame OUT (by decide), hw8frame OUT (by decide)]; exact h7OUT
    have h9Z : State.get w9 ZERO = [] := by
      rw [hw9frame ZERO (by decide), hw8frame ZERO (by decide)]; exact h7Z
    have hstep : encodeStepConstraint C line step = .ftrue := by
      unfold encodeStepConstraint
      rw [dif_neg hguard]
    have heval : stepBody.eval u = emitFtrue.eval w9 := by
      unfold stepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, ← hw7, Cmd.eval_seq, e8,
        Cmd.eval_seq, e9, Cmd.eval_ifBit_false _ _ _ _ hw9Gne]
    refine ⟨?_, ?_, ?_⟩
    · rw [heval, emitFtrue_run, State.get_set_eq, h9OUT, hstep]
      rfl
    · rw [heval, emitFtrue_frame _ ZERO (by decide)]; exact h9Z
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      rw [heval, emitFtrue_frame _ r h2, hw9frame r h16, hw8frame r h4,
        h7frame r h15 h9, hw6frame r h15, hw5frame r h14, hw4frame r h13,
        hw3frame r h12, h2frame r h11 h9, hw1frame r h11]

/-- One inner iteration of `emitAllSteps`: the `fand` spine node, then one
step constraint (named so `emitAllSteps_run`'s fold invariant can refer to
it). -/
def stepIterBody : Cmd := emitFandTag ;; stepBody

/-- One line of `emitAllSteps`: spine node, `LINEL := 1^(line·L)` (clear +
mul-loop off the `KLINE` counter), the inner step loop over `LREG1 =
1^(L+1)`, and the closing `ftrue`. -/
def lineBody : Cmd :=
  emitFandTag ;;
  Cmd.op (.clear LINEL) ;;
  Cmd.forBnd KTMP2 KLINE (Cmd.op (.concat LINEL LINEL LREG)) ;;
  Cmd.forBnd KSTEP LREG1 stepIterBody ;;
  emitFtrue

/-- `serF (encodeAllStepConstraints C)` = `listAnd` over lines of
(`listAnd` over steps of `encodeStepConstraint`). -/
def emitAllSteps : Cmd :=
  Cmd.forBnd KLINE STEPS lineBody ;;
  emitFtrue

/-! ### `emitAllSteps_run` — every step constraint (the two-level `listAnd` fold)

`andPrefix` is the `fand`-tag serialization prefix of a formula list (no
closing `ftrue`) — the `listAnd` analogue of `cardsPrefix`, stated ONCE
generically so it serves both levels (steps within a line, lines within the
tableau); `serF_listAnd` closes it. The inner level accumulates
`encodeStepConstraint C line` over `List.range (L+1)` (each iteration one
black-boxed `stepBody_run` — the loop bound is exact, no idle iterations);
the outer level re-derives `LINEL = 1^(line·L)` per line via
`unaryMulLoop_run` and accumulates `encodeLineConstraints C` over
`List.range C.steps`. -/

/-- The `fand`-tag serialization prefix of a formula list (no closing
`ftrue`) — `OUT`'s accumulation state mid-`listAnd`, at either level. -/
def andPrefix : List formula → List Nat
  | [] => []
  | f :: fs => [0, 1] ++ serF f ++ andPrefix fs

theorem andPrefix_append (xs ys : List formula) :
    andPrefix (xs ++ ys) = andPrefix xs ++ andPrefix ys := by
  induction xs with
  | nil => simp [andPrefix]
  | cons f fs ih =>
      simp only [List.cons_append, andPrefix, ih, List.append_assoc]

/-- Closing the accumulated `fand` prefix with `ftrue` gives exactly the
serialized conjunction — the `listAnd` analogue of `serF_encodeCardsAt`. -/
theorem serF_listAnd (fs : List formula) :
    serF (listAnd fs) = andPrefix fs ++ serF .ftrue := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      show serF (.fand f (listAnd fs)) = _
      simp [serF, andPrefix, ih, List.append_assoc]

/-- The inner (per-line) fold invariant: `OUT` accumulates the tag-then-step
prefix, `ZERO` stays empty, and everything outside `stepIterBody`'s scratch
set (= `stepBody`'s ∪ {`KSTEP`}) is untouched — the per-line registers
(`LINEL`/`OFFSET`/`WIDTH`/`LREG`/`CARDS`) are recovered through the frame
clause. -/
private def ASInv (C : BinaryCC) (line : Nat) (u : State) (i : Nat)
    (st : State) : Prop :=
  State.get st OUT = State.get u OUT
      ++ andPrefix ((List.range i).map (encodeStepConstraint C line))
  ∧ State.get st ZERO = []
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
      r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KCARD →
      r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
      r ≠ KSTEP → State.get st r = State.get u r)

private theorem ASInv_step (C : BinaryCC) (line : Nat) (u : State)
    (hLINEL : State.get u LINEL = List.replicate (line * C.init.length) 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hWID : State.get u WIDTH = List.replicate C.width 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (i : Nat) (st : State) (h : ASInv C line u i st) :
    ASInv C line u (i + 1) (stepIterBody.eval (st.set KSTEP (List.replicate i 1))) := by
  obtain ⟨hOUT, hZ, hframe⟩ := h
  set w := st.set KSTEP (List.replicate i 1) with hw
  have hwframe : ∀ r : Var, r ≠ KSTEP → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwK : State.get w KSTEP = List.replicate i 1 := State.get_set_eq _ _ _
  clear_value w
  -- w1: the step's spine node
  set w1 := emitFandTag.eval w with hw1
  have hw1frame : ∀ r : Var, r ≠ OUT → State.get w1 r = State.get w r := by
    intro r hr; rw [hw1]; exact emitFandTag_frame w r hr
  have hw1OUT : State.get w1 OUT = State.get w OUT ++ [0, 1] := by
    rw [hw1, emitFandTag_run]; exact State.get_set_eq _ _ _
  clear_value w1
  -- registers threaded to w1 for `stepBody_run`
  have h1K : State.get w1 KSTEP = List.replicate i 1 := by
    rw [hw1frame KSTEP (by decide)]; exact hwK
  have h1LINEL : State.get w1 LINEL = List.replicate (line * C.init.length) 1 := by
    rw [hw1frame LINEL (by decide), hwframe LINEL (by decide),
      hframe LINEL (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hLINEL
  have h1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hw1frame OFFSET (by decide), hwframe OFFSET (by decide),
      hframe OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hOFF
  have h1WID : State.get w1 WIDTH = List.replicate C.width 1 := by
    rw [hw1frame WIDTH (by decide), hwframe WIDTH (by decide),
      hframe WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hWID
  have h1LREG : State.get w1 LREG = List.replicate C.init.length 1 := by
    rw [hw1frame LREG (by decide), hwframe LREG (by decide),
      hframe LREG (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hLREG
  have h1CARDS : State.get w1 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [hw1frame CARDS (by decide), hwframe CARDS (by decide),
      hframe CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hCARDS
  have h1Z : State.get w1 ZERO = [] := by
    rw [hw1frame ZERO (by decide), hwframe ZERO (by decide)]; exact hZ
  -- w2: the step constraint (black-boxed)
  obtain ⟨h2OUT, h2Z, h2frame⟩ :=
    stepBody_run C line i w1 h1LINEL h1K h1OFF h1WID h1LREG h1CARDS h1Z
  set w2 := stepBody.eval w1 with hw2
  clear_value w2
  have heval : stepIterBody.eval w = w2 := by
    unfold stepIterBody
    rw [Cmd.eval_seq, ← hw1, ← hw2]
  refine ⟨?_, ?_, ?_⟩
  · rw [heval, h2OUT, hw1OUT, hwframe OUT (by decide), hOUT, List.range_succ,
      List.map_append, andPrefix_append]
    simp [andPrefix, List.append_assoc]
  · rw [heval]; exact h2Z
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rw [heval, h2frame r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16,
      hw1frame r h2, hwframe r h17,
      hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17]

/-- The inner step loop: appends the full per-line tag-then-step prefix
(`List.range (L+1)` matches `encodeLineConstraints`'
`List.range (C.init.length + 1)`). -/
private theorem innerSteps_run (C : BinaryCC) (line : Nat) (u : State)
    (hLINEL : State.get u LINEL = List.replicate (line * C.init.length) 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hWID : State.get u WIDTH = List.replicate C.width 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u LREG1 = List.replicate (C.init.length + 1) 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = []) :
    State.get ((Cmd.forBnd KSTEP LREG1 stepIterBody).eval u) OUT
        = State.get u OUT ++ andPrefix
            ((List.range (C.init.length + 1)).map (encodeStepConstraint C line))
    ∧ State.get ((Cmd.forBnd KSTEP LREG1 stepIterBody).eval u) ZERO = []
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
        r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KCARD →
        r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
        r ≠ KSTEP →
        State.get ((Cmd.forBnd KSTEP LREG1 stepIterBody).eval u) r
          = State.get u r) := by
  have hlen : (State.get u LREG1).length = C.init.length + 1 := by
    rw [hLREG1, List.length_replicate]
  have hbase : ASInv C line u 0 u := by
    refine ⟨?_, hZ, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    simp [andPrefix]
  have hInv : ASInv C line u (C.init.length + 1)
      (Cmd.foldlState stepIterBody KSTEP (List.range (C.init.length + 1)) u) :=
    Cmd.foldlState_range_induct stepIterBody KSTEP (C.init.length + 1) u
      (ASInv C line u) hbase
      (fun i st _ hM => ASInv_step C line u hLINEL hOFF hWID hLREG hCARDS i st hM)
  have heval : (Cmd.forBnd KSTEP LREG1 stepIterBody).eval u
      = Cmd.foldlState stepIterBody KSTEP (List.range (C.init.length + 1)) u := by
    rw [Cmd.eval_forBnd, hlen]
  obtain ⟨h1, h2, h3⟩ := hInv
  exact ⟨by rw [heval]; exact h1, by rw [heval]; exact h2,
    fun r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 => by
      rw [heval]
      exact h3 r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17⟩

/-- The outer (per-tableau) fold invariant: `lineBody`'s scratch set =
`stepIterBody`'s ∪ {`LINEL`, `KLINE`, `KTMP2`}. -/
private def ALInv (C : BinaryCC) (u : State) (j : Nat) (st : State) : Prop :=
  State.get st OUT = State.get u OUT
      ++ andPrefix ((List.range j).map (encodeLineConstraints C))
  ∧ State.get st ZERO = []
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
      r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KCARD →
      r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
      r ≠ KSTEP → r ≠ LINEL → r ≠ KLINE → r ≠ KTMP2 →
      State.get st r = State.get u r)

private theorem ALInv_step (C : BinaryCC) (u : State)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hWID : State.get u WIDTH = List.replicate C.width 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u LREG1 = List.replicate (C.init.length + 1) 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (j : Nat) (st : State) (h : ALInv C u j st) :
    ALInv C u (j + 1) (lineBody.eval (st.set KLINE (List.replicate j 1))) := by
  obtain ⟨hOUT, hZ, hframe⟩ := h
  set w := st.set KLINE (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KLINE → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwK : State.get w KLINE = List.replicate j 1 := State.get_set_eq _ _ _
  clear_value w
  -- w1: the line's spine node
  set w1 := emitFandTag.eval w with hw1
  have hw1frame : ∀ r : Var, r ≠ OUT → State.get w1 r = State.get w r := by
    intro r hr; rw [hw1]; exact emitFandTag_frame w r hr
  have hw1OUT : State.get w1 OUT = State.get w OUT ++ [0, 1] := by
    rw [hw1, emitFandTag_run]; exact State.get_set_eq _ _ _
  clear_value w1
  -- w2: clear LINEL
  have e2 : (Cmd.op (.clear LINEL)).eval w1 = w1.set LINEL [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w2 := w1.set LINEL [] with hw2
  have hw2frame : ∀ r : Var, r ≠ LINEL → State.get w2 r = State.get w1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw2LINEL : State.get w2 LINEL = [] := State.get_set_eq _ _ _
  have h2chain : ∀ r : Var, r ≠ LINEL → r ≠ OUT → r ≠ KLINE →
      State.get w2 r = State.get st r := by
    intro r hr1 hr2 hr3
    rw [hw2frame r hr1, hw1frame r hr2, hwframe r hr3]
  have h2LREG : State.get w2 LREG = List.replicate C.init.length 1 := by
    rw [h2chain LREG (by decide) (by decide) (by decide),
      hframe LREG (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    exact hLREG
  have h2KLINE : (State.get w2 KLINE).length = j := by
    rw [hw2frame KLINE (by decide), hw1frame KLINE (by decide), hwK,
      List.length_replicate]
  clear_value w2
  -- w3: LINEL := 1^(j·L)
  obtain ⟨h3LINEL, h3frame⟩ :=
    unaryMulLoop_run KTMP2 KLINE LREG LINEL w2 C.init.length j
      (by decide) (by decide) (by decide) h2LREG h2KLINE hw2LINEL
  set w3 := (Cmd.forBnd KTMP2 KLINE (Cmd.op (.concat LINEL LINEL LREG))).eval w2
    with hw3
  clear_value w3
  have h3chain : ∀ r : Var, r ≠ LINEL → r ≠ KTMP2 → r ≠ OUT → r ≠ KLINE →
      State.get w3 r = State.get st r := by
    intro hr r1 r2 r3 r4
    rw [h3frame hr r1 r2, h2chain hr r1 r3 r4]
  have h3chainU : ∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG →
      r ≠ KBIT → r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KCARD →
      r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
      r ≠ KSTEP → r ≠ LINEL → r ≠ KLINE → r ≠ KTMP2 →
      State.get w3 r = State.get u r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    rw [h3chain r h18 h20 h2 h19,
      hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20]
  have h3OFF : State.get w3 OFFSET = List.replicate C.offset 1 := by
    rw [h3chainU OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hOFF
  have h3WID : State.get w3 WIDTH = List.replicate C.width 1 := by
    rw [h3chainU WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hWID
  have h3LREG : State.get w3 LREG = List.replicate C.init.length 1 := by
    rw [h3chainU LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG
  have h3LREG1 : State.get w3 LREG1 = List.replicate (C.init.length + 1) 1 := by
    rw [h3chainU LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG1
  have h3CARDS : State.get w3 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [h3chainU CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hCARDS
  have h3Z : State.get w3 ZERO = [] := by
    rw [h3chain ZERO (by decide) (by decide) (by decide) (by decide)]; exact hZ
  have h3OUT : State.get w3 OUT
      = State.get u OUT ++ andPrefix ((List.range j).map (encodeLineConstraints C))
        ++ [0, 1] := by
    rw [h3frame OUT (by decide) (by decide), hw2frame OUT (by decide), hw1OUT,
      hwframe OUT (by decide), hOUT]
  -- w4: the inner step loop
  obtain ⟨h4OUT, h4Z, h4frame⟩ :=
    innerSteps_run C j w3 h3LINEL h3OFF h3WID h3LREG h3LREG1 h3CARDS h3Z
  set w4 := (Cmd.forBnd KSTEP LREG1 stepIterBody).eval w3 with hw4
  clear_value w4
  have heval : lineBody.eval w = emitFtrue.eval w4 := by
    unfold lineBody
    rw [Cmd.eval_seq, ← hw1, Cmd.eval_seq, e2, Cmd.eval_seq, ← hw3, Cmd.eval_seq,
      ← hw4]
  refine ⟨?_, ?_, ?_⟩
  · -- unroll the RHS in isolation: the goal's LHS also contains a
    -- `List.range (·+1)` (the inner step range), so a bare `rw
    -- [List.range_succ]` would pick the wrong occurrence
    have hsnoc : andPrefix ((List.range (j + 1)).map (encodeLineConstraints C))
        = andPrefix ((List.range j).map (encodeLineConstraints C))
          ++ ([0, 1] ++ serF (encodeLineConstraints C j)) := by
      rw [List.range_succ, List.map_append, andPrefix_append]
      simp [andPrefix]
    rw [heval, emitFtrue_run, State.get_set_eq, h4OUT, h3OUT, hsnoc,
      show serF (encodeLineConstraints C j)
          = andPrefix
              ((List.range (C.init.length + 1)).map (encodeStepConstraint C j))
            ++ serF .ftrue from serF_listAnd _]
    simp [serF, List.append_assoc]
  · rw [heval, emitFtrue_frame _ ZERO (by decide)]; exact h4Z
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    rw [heval, emitFtrue_frame _ r h2,
      h4frame r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17,
      h3chain r h18 h20 h2 h19,
      hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20]

/-- **`emitAllSteps` is correct**: with the loop/length registers pre-set
(`STEPS`/`LREG`/`LREG1` from `encodeIn`+`precompLen`, `OFFSET`/`WIDTH`/`CARDS`
pinned by `encodeIn`), it appends `serF (encodeAllStepConstraints C)` to
`OUT`. `CARDS` itself is untouched (consumed via scratch copies only). -/
theorem emitAllSteps_run (C : BinaryCC) (u : State)
    (hSTEPS : State.get u STEPS = List.replicate C.steps 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hWID : State.get u WIDTH = List.replicate C.width 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u LREG1 = List.replicate (C.init.length + 1) 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = []) :
    State.get (emitAllSteps.eval u) OUT
        = State.get u OUT ++ serF (encodeAllStepConstraints C)
    ∧ State.get (emitAllSteps.eval u) ZERO = []
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
        r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KCARD →
        r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
        r ≠ KSTEP → r ≠ LINEL → r ≠ KLINE → r ≠ KTMP2 →
        State.get (emitAllSteps.eval u) r = State.get u r) := by
  have hlen : (State.get u STEPS).length = C.steps := by
    rw [hSTEPS, List.length_replicate]
  have hbase : ALInv C u 0 u := by
    refine ⟨?_, hZ, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    simp [andPrefix]
  have hInv : ALInv C u C.steps
      (Cmd.foldlState lineBody KLINE (List.range C.steps) u) :=
    Cmd.foldlState_range_induct lineBody KLINE C.steps u (ALInv C u) hbase
      (fun j st _ hM => ALInv_step C u hOFF hWID hLREG hLREG1 hCARDS j st hM)
  obtain ⟨hOUTf, hZf, hframef⟩ := hInv
  have heval : emitAllSteps.eval u
      = emitFtrue.eval (Cmd.foldlState lineBody KLINE (List.range C.steps) u) := by
    unfold emitAllSteps
    rw [Cmd.eval_seq, Cmd.eval_forBnd, hlen]
  refine ⟨?_, ?_, ?_⟩
  · rw [heval, emitFtrue_run, State.get_set_eq, hOUTf]
    simp [encodeAllStepConstraints, serF_listAnd, serF, List.append_assoc]
  · rw [heval, emitFtrue_frame _ ZERO (by decide)]; exact hZf
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    rw [heval, emitFtrue_frame _ r h2,
      hframef r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20]

/-- One iteration of `readOneFinal`'s parse loop (named so the run lemma can
refer to it): consume one sentinel element off `SCANF` into `FBITS`/`BLEN`,
flip `DONE` on the bare terminator, idle after. -/
def readFinBody : Cmd :=
  Cmd.ifBit DONE
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
          Cmd.op (.clear DONE) ;; Cmd.op (.appendOne DONE) ) )

/-- Consume one `encSList` of bits off `SCANF` into `FBITS` (bit-list) and
`BLEN` (`1^length`). -/
def readOneFinal : Cmd :=
  Cmd.op (.clear FBITS) ;; Cmd.op (.clear BLEN) ;; Cmd.op (.clear DONE) ;;
  Cmd.forBnd KTMP SCANF readFinBody

/-! ### `readOneFinal_run` — the sentinel-stream *parse* leaf lemma

`SBInv`'s decode half without the re-emitting: the same two-phase invariant
(split at `bits.length`, terminator flips `DONE`, surplus iterations idle on
`DONE` re-clearing the scratch counter `KTMP2`), but the per-element output is
the raw bit cell appended to `FBITS` plus a `1` on `BLEN`, and there is no
`OUT`/`BASE`/`WREG` traffic at all. Like `emitBitsFromSent_run`, the exit
leaves `SCANF` **past the terminator** (at `rest`), so `emitFinal`'s outer
loop can chain one `readOneFinal` per final string off one stream copy. -/

/-- The two-phase fold invariant for `readFinBody`. -/
private def RFInv (bits : List Bool) (rest : List Nat) (u : State) (i : Nat)
    (st : State) : Prop :=
  (i ≤ bits.length →
      State.get st DONE = []
      ∧ State.get st SCANF
          = FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop i)) ++ rest
      ∧ State.get st FBITS = FlatCCBinFree.bitsNat (bits.take i)
      ∧ State.get st BLEN = List.replicate i 1)
  ∧ (bits.length < i →
      State.get st DONE = [1]
      ∧ State.get st SCANF = rest
      ∧ State.get st FBITS = FlatCCBinFree.bitsNat bits
      ∧ State.get st BLEN = List.replicate bits.length 1)
  ∧ (∀ r : Var, r ≠ SCANF → r ≠ FBITS → r ≠ BLEN → r ≠ DONE → r ≠ EMARK →
      r ≠ TFLG → r ≠ KTMP → r ≠ KTMP2 → State.get st r = State.get u r)

private theorem RFInv_step (bits : List Bool) (rest : List Nat) (u : State)
    (i : Nat) (st : State) (h : RFInv bits rest u i st) :
    RFInv bits rest u (i + 1)
      (readFinBody.eval (st.set KTMP (List.replicate i 1))) := by
  obtain ⟨hph1, hph2, hframe⟩ := h
  rcases Nat.lt_trichotomy i bits.length with hi | hi | hi
  · -- live iteration: consume one sentinel element into FBITS/BLEN
    obtain ⟨hDONE, hSCAN, hFB, hBL⟩ := hph1 (le_of_lt hi)
    set w := st.set KTMP (List.replicate i 1) with hw
    have hwframe : ∀ r : Var, r ≠ KTMP → State.get w r = State.get st r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwD : State.get w DONE = [] := by
      rw [hwframe DONE (by decide)]; exact hDONE
    have hwFB : State.get w FBITS = FlatCCBinFree.bitsNat (bits.take i) := by
      rw [hwframe FBITS (by decide)]; exact hFB
    have hwBL : State.get w BLEN = List.replicate i 1 := by
      rw [hwframe BLEN (by decide)]; exact hBL
    have hdrop : bits.drop i = bits[i] :: bits.drop (i + 1) :=
      List.drop_eq_getElem_cons hi
    have htake : bits.take (i + 1) = bits.take i ++ [bits[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
    set b := bits[i] with hb
    clear_value b
    set T := FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop (i + 1))) ++ rest
      with hT
    have hSCANw : State.get w SCANF = 1 :: (List.replicate (cond b 1 0) 1 ++ 0 :: T) := by
      rw [hwframe SCANF (by decide), hSCAN, hdrop, hT]
      show (FlatTCCFree.encSElem (cond b 1 0)
          ++ FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop (i + 1)))) ++ rest = _
      rw [List.append_assoc, FlatTCCFree.encSElem_append]
    clear_value w
    have hDONEne : State.get w DONE ≠ [1] := by rw [hwD]; decide
    -- step 1: head EMARK SCANF  (the element marker `1`)
    have e1 : (Cmd.op (.head EMARK SCANF)).eval w = w.set EMARK [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hSCANw]
    set w1 := w.set EMARK [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ EMARK → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1E : State.get w1 EMARK = [1] := State.get_set_eq _ _ _
    have hw1SCAN : State.get w1 SCANF = 1 :: (List.replicate (cond b 1 0) 1 ++ 0 :: T) := by
      rw [hw1frame SCANF (by decide)]; exact hSCANw
    clear_value w1
    -- step 2: tail SCANF  (drop the marker)
    have e2 : (Cmd.op (.tail SCANF SCANF)).eval w1
        = w1.set SCANF (List.replicate (cond b 1 0) 1 ++ 0 :: T) := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw1SCAN, List.tail_cons]
    set w2 := w1.set SCANF (List.replicate (cond b 1 0) 1 ++ 0 :: T) with hw2
    have hw2frame : ∀ r : Var, r ≠ SCANF → State.get w2 r = State.get w1 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw2SCAN : State.get w2 SCANF = List.replicate (cond b 1 0) 1 ++ 0 :: T :=
      State.get_set_eq _ _ _
    clear_value w2
    -- step 3: head TFLG SCANF  (the bit)
    have e3 : (Cmd.op (.head TFLG SCANF)).eval w2 = w2.set TFLG [cond b 1 0] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, hw2SCAN]
      cases b <;> rfl
    set w3 := w2.set TFLG [cond b 1 0] with hw3
    have hw3frame : ∀ r : Var, r ≠ TFLG → State.get w3 r = State.get w2 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw3T : State.get w3 TFLG = [cond b 1 0] := State.get_set_eq _ _ _
    have hw3SCAN : State.get w3 SCANF = List.replicate (cond b 1 0) 1 ++ 0 :: T := by
      rw [hw3frame SCANF (by decide)]; exact hw2SCAN
    have hw3FB : State.get w3 FBITS = FlatCCBinFree.bitsNat (bits.take i) := by
      rw [hw3frame FBITS (by decide), hw2frame FBITS (by decide),
        hw1frame FBITS (by decide)]
      exact hwFB
    clear_value w3
    -- step 4: append the bit to FBITS, consume the element's `1^b ++ [0]` cells
    have eF : (Cmd.ifBit TFLG
        (Cmd.op (.appendOne FBITS) ;; Cmd.op (.tail SCANF SCANF) ;;
          Cmd.op (.tail SCANF SCANF))
        (Cmd.op (.appendZero FBITS) ;; Cmd.op (.tail SCANF SCANF))).eval w3
        = (w3.set FBITS (State.get w3 FBITS ++ [cond b 1 0])).set SCANF T := by
      cases b with
      | true =>
          have hT1 : State.get w3 TFLG = [1] := hw3T
          rw [Cmd.eval_ifBit_true _ _ _ _ hT1]
          have ea : (Cmd.op (.appendOne FBITS)).eval w3
              = w3.set FBITS (State.get w3 FBITS ++ [1]) := by
            rw [Cmd.eval_op]; simp only [Op.eval]
          have hS1 : State.get (w3.set FBITS (State.get w3 FBITS ++ [1])) SCANF
              = 1 :: 0 :: T := by
            rw [State.get_set_ne _ _ _ _ (show SCANF ≠ FBITS by decide)]
            exact hw3SCAN
          have et1 : (Cmd.op (.tail SCANF SCANF)).eval
                (w3.set FBITS (State.get w3 FBITS ++ [1]))
              = (w3.set FBITS (State.get w3 FBITS ++ [1])).set SCANF (0 :: T) := by
            rw [Cmd.eval_op]; simp only [Op.eval, hS1, List.tail_cons]
          rw [Cmd.eval_seq, ea, Cmd.eval_seq, et1, Cmd.eval_op]
          simp only [Op.eval, State.get_set_eq, List.tail_cons, State.set_set]
          rfl
      | false =>
          have hT0 : State.get w3 TFLG ≠ [1] := by rw [hw3T]; decide
          rw [Cmd.eval_ifBit_false _ _ _ _ hT0]
          have ea : (Cmd.op (.appendZero FBITS)).eval w3
              = w3.set FBITS (State.get w3 FBITS ++ [0]) := by
            rw [Cmd.eval_op]; simp only [Op.eval]
          have hS0 : State.get (w3.set FBITS (State.get w3 FBITS ++ [0])) SCANF
              = 0 :: T := by
            rw [State.get_set_ne _ _ _ _ (show SCANF ≠ FBITS by decide)]
            exact hw3SCAN
          rw [Cmd.eval_seq, ea, Cmd.eval_op]
          simp only [Op.eval, hS0, List.tail_cons]
          rfl
    set w4 := (w3.set FBITS (State.get w3 FBITS ++ [cond b 1 0])).set SCANF T with hw4
    have hw4frame : ∀ r : Var, r ≠ FBITS → r ≠ SCANF →
        State.get w4 r = State.get w3 r := by
      intro r h1 h2
      rw [hw4, State.get_set_ne _ _ _ _ h2, State.get_set_ne _ _ _ _ h1]
    have hw4SCAN : State.get w4 SCANF = T := by
      rw [hw4]; exact State.get_set_eq _ _ _
    have hw4FB : State.get w4 FBITS
        = FlatCCBinFree.bitsNat (bits.take i) ++ [cond b 1 0] := by
      rw [hw4, State.get_set_ne _ _ _ _ (show FBITS ≠ SCANF by decide),
        State.get_set_eq, hw3FB]
    have hw4BL : State.get w4 BLEN = List.replicate i 1 := by
      rw [hw4frame BLEN (by decide) (by decide), hw3frame BLEN (by decide),
        hw2frame BLEN (by decide), hw1frame BLEN (by decide)]
      exact hwBL
    clear_value w4
    -- step 5: appendOne BLEN
    have eB : (Cmd.op (.appendOne BLEN)).eval w4
        = w4.set BLEN (List.replicate (i + 1) 1) := by
      rw [Cmd.eval_op]
      simp only [Op.eval, hw4BL]
      congr 1
      rw [List.replicate_succ']
    set wF := w4.set BLEN (List.replicate (i + 1) 1) with hwF
    have hwFframe : ∀ r : Var, r ≠ BLEN → State.get wF r = State.get w4 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwFBL : State.get wF BLEN = List.replicate (i + 1) 1 := State.get_set_eq _ _ _
    have heval : readFinBody.eval w = wF := by
      unfold readFinBody
      rw [Cmd.eval_ifBit_false _ _ _ _ hDONEne, Cmd.eval_seq, e1,
        Cmd.eval_ifBit_true _ _ _ _ hw1E, Cmd.eval_seq, e2, Cmd.eval_seq, e3,
        Cmd.eval_seq, eF, eB]
    rw [heval]
    refine ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, fun hlt => absurd hlt (by omega), ?_⟩
    · rw [hwFframe DONE (by decide), hw4frame DONE (by decide) (by decide),
        hw3frame DONE (by decide), hw2frame DONE (by decide),
        hw1frame DONE (by decide)]
      exact hwD
    · rw [hwFframe SCANF (by decide), hw4SCAN]
    · rw [hwFframe FBITS (by decide), hw4FB, htake, FlatCCBinFree.bitsNat_append]
      rfl
    · exact hwFBL
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      rw [hwFframe r h3, hw4frame r h2 h1, hw3frame r h6, hw2frame r h1,
        hw1frame r h5, hwframe r h7, hframe r h1 h2 h3 h4 h5 h6 h7 h8]
  · -- terminator iteration: consume the bare `0`, set DONE
    subst hi
    obtain ⟨hDONE, hSCAN, hFB, hBL⟩ := hph1 (le_refl _)
    rw [List.take_of_length_le (le_refl bits.length)] at hFB
    set w := st.set KTMP (List.replicate bits.length 1) with hw
    have hwframe : ∀ r : Var, r ≠ KTMP → State.get w r = State.get st r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwD : State.get w DONE = [] := by
      rw [hwframe DONE (by decide)]; exact hDONE
    have hwFB : State.get w FBITS = FlatCCBinFree.bitsNat bits := by
      rw [hwframe FBITS (by decide)]; exact hFB
    have hwBL : State.get w BLEN = List.replicate bits.length 1 := by
      rw [hwframe BLEN (by decide)]; exact hBL
    have hSCANw : State.get w SCANF = 0 :: rest := by
      rw [hwframe SCANF (by decide), hSCAN,
        List.drop_eq_nil_of_le (le_refl bits.length)]
      rfl
    clear_value w
    have hDONEne : State.get w DONE ≠ [1] := by rw [hwD]; decide
    have e1 : (Cmd.op (.head EMARK SCANF)).eval w = w.set EMARK [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hSCANw]
    set w1 := w.set EMARK [0] with hw1
    have hw1frame : ∀ r : Var, r ≠ EMARK → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1E : State.get w1 EMARK = [0] := State.get_set_eq _ _ _
    have hw1SCAN : State.get w1 SCANF = 0 :: rest := by
      rw [hw1frame SCANF (by decide)]; exact hSCANw
    clear_value w1
    have hw1Ene : State.get w1 EMARK ≠ [1] := by rw [hw1E]; decide
    have e2 : (Cmd.op (.tail SCANF SCANF)).eval w1 = w1.set SCANF rest := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw1SCAN, List.tail_cons]
    set w2 := w1.set SCANF rest with hw2
    have hw2frame : ∀ r : Var, r ≠ SCANF → State.get w2 r = State.get w1 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw2SCAN : State.get w2 SCANF = rest := State.get_set_eq _ _ _
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
    have heval : readFinBody.eval w = wF := by
      unfold readFinBody
      rw [Cmd.eval_ifBit_false _ _ _ _ hDONEne, Cmd.eval_seq, e1,
        Cmd.eval_ifBit_false _ _ _ _ hw1Ene, Cmd.eval_seq, e2, Cmd.eval_seq, e3, e4]
    rw [heval]
    refine ⟨fun hle => absurd hle (by omega), fun _ => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hwF]; exact State.get_set_eq _ _ _
    · rw [hwFframe SCANF (by decide), hw3frame SCANF (by decide)]; exact hw2SCAN
    · rw [hwFframe FBITS (by decide), hw3frame FBITS (by decide),
        hw2frame FBITS (by decide), hw1frame FBITS (by decide)]
      exact hwFB
    · rw [hwFframe BLEN (by decide), hw3frame BLEN (by decide),
        hw2frame BLEN (by decide), hw1frame BLEN (by decide)]
      exact hwBL
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      rw [hwFframe r h4, hw3frame r h4, hw2frame r h1, hw1frame r h5,
        hwframe r h7, hframe r h1 h2 h3 h4 h5 h6 h7 h8]
  · -- idle iteration: DONE set, only the scratch counter is (re-)cleared
    obtain ⟨hDONE, hSCAN, hFB, hBL⟩ := hph2 hi
    set w := st.set KTMP (List.replicate i 1) with hw
    have hwframe : ∀ r : Var, r ≠ KTMP → State.get w r = State.get st r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwD : State.get w DONE = [1] := by
      rw [hwframe DONE (by decide)]; exact hDONE
    clear_value w
    have heval : readFinBody.eval w = w.set KTMP2 [] := by
      unfold readFinBody
      rw [Cmd.eval_ifBit_true _ _ _ _ hwD, Cmd.eval_op]
      simp only [Op.eval]
    rw [heval]
    refine ⟨fun hle => absurd hle (by omega), fun _ => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [State.get_set_ne _ _ _ _ (show DONE ≠ KTMP2 by decide)]; exact hwD
    · rw [State.get_set_ne _ _ _ _ (show SCANF ≠ KTMP2 by decide),
        hwframe SCANF (by decide)]
      exact hSCAN
    · rw [State.get_set_ne _ _ _ _ (show FBITS ≠ KTMP2 by decide),
        hwframe FBITS (by decide)]
      exact hFB
    · rw [State.get_set_ne _ _ _ _ (show BLEN ≠ KTMP2 by decide),
        hwframe BLEN (by decide)]
      exact hBL
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      rw [State.get_set_ne _ _ _ _ h8, hwframe r h7,
        hframe r h1 h2 h3 h4 h5 h6 h7 h8]

/-- **`readOneFinal` is correct**: it consumes ONE sentinel-encoded bit-list
off the front of `SCANF`, leaving the raw bit cells in `FBITS`, the unary
length in `BLEN`, and `SCANF` **past the terminator** (at `rest`) — so
`emitFinal`'s outer loop can chain one call per final string. Surplus loop
iterations idle on `DONE` (re-clearing the scratch counter `KTMP2`). -/
theorem readOneFinal_run (bits : List Bool) (rest : List Nat) (u : State)
    (hSC : State.get u SCANF
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest) :
    State.get (readOneFinal.eval u) SCANF = rest
    ∧ State.get (readOneFinal.eval u) FBITS = FlatCCBinFree.bitsNat bits
    ∧ State.get (readOneFinal.eval u) BLEN = List.replicate bits.length 1
    ∧ (∀ r : Var, r ≠ SCANF → r ≠ FBITS → r ≠ BLEN → r ≠ DONE → r ≠ EMARK →
        r ≠ TFLG → r ≠ KTMP → r ≠ KTMP2 →
        State.get (readOneFinal.eval u) r = State.get u r) := by
  have e01 : (Cmd.op (.clear FBITS)).eval u = u.set FBITS [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u1 := u.set FBITS [] with hu1
  have hu1frame : ∀ r : Var, r ≠ FBITS → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1FB : State.get u1 FBITS = [] := State.get_set_eq _ _ _
  clear_value u1
  have e02 : (Cmd.op (.clear BLEN)).eval u1 = u1.set BLEN [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u2 := u1.set BLEN [] with hu2
  have hu2frame : ∀ r : Var, r ≠ BLEN → State.get u2 r = State.get u1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu2BL : State.get u2 BLEN = [] := State.get_set_eq _ _ _
  clear_value u2
  have e03 : (Cmd.op (.clear DONE)).eval u2 = u2.set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u3 := u2.set DONE [] with hu3
  have hu3frame : ∀ r : Var, r ≠ DONE → State.get u3 r = State.get u2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu3D : State.get u3 DONE = [] := State.get_set_eq _ _ _
  have hu3SC : State.get u3 SCANF
      = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest := by
    rw [hu3frame SCANF (by decide), hu2frame SCANF (by decide),
      hu1frame SCANF (by decide)]
    exact hSC
  have hu3FB : State.get u3 FBITS = [] := by
    rw [hu3frame FBITS (by decide), hu2frame FBITS (by decide)]; exact hu1FB
  have hu3BL : State.get u3 BLEN = [] := by
    rw [hu3frame BLEN (by decide)]; exact hu2BL
  clear_value u3
  have hN : bits.length + 1 ≤ (State.get u3 SCANF).length := by
    rw [hu3SC, List.length_append, FlatTCCFree.encSList_length,
      show (FlatCCBinFree.bitsNat bits).length = bits.length from List.length_map _]
    omega
  have hbase : RFInv bits rest u 0 u3 := by
    refine ⟨fun _ => ⟨hu3D, by rw [List.drop_zero]; exact hu3SC,
        by rw [List.take_zero]; exact hu3FB, hu3BL⟩,
      fun hlt => absurd hlt (Nat.not_lt_zero _), ?_⟩
    intro r h1 h2 h3 h4 _ _ _ _
    rw [hu3frame r h4, hu2frame r h3, hu1frame r h2]
  have hInv : RFInv bits rest u (State.get u3 SCANF).length
      (Cmd.foldlState readFinBody KTMP (List.range (State.get u3 SCANF).length) u3) :=
    Cmd.foldlState_range_induct _ KTMP _ u3 (RFInv bits rest u) hbase
      (fun i st _ hM => RFInv_step bits rest u i st hM)
  obtain ⟨-, hph2, hframef⟩ := hInv
  obtain ⟨-, hSCf, hFBf, hBLf⟩ := hph2 (by omega)
  have heval : readOneFinal.eval u
      = Cmd.foldlState readFinBody KTMP (List.range (State.get u3 SCANF).length) u3 := by
    unfold readOneFinal
    rw [Cmd.eval_seq, e01, Cmd.eval_seq, e02, Cmd.eval_seq, e03, Cmd.eval_forBnd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval]; exact hSCf
  · rw [heval]; exact hFBf
  · rw [heval]; exact hBLf
  · intro r h1 h2 h3 h4 h5 h6 h7 h8
    rw [heval, hframef r h1 h2 h3 h4 h5 h6 h7 h8]

/-- One step of one final string: `STEPO := 1^(step·offset)` (mul-loop off
`KFSTEP`), the on-machine bound guard `step·offset + |bits| ≤ L` (`REM` via
truncated subtraction, `BLEN = 1^|bits|`), `FSTART := 1^(steps·L + step·offset)`,
then either the literal block (`emitBitsFromScan` off a fresh `FBITS` copy) or
`falseFml` — reproduces `encodeFinalAtStep C step bits`'s dite exactly. -/
def finalStepBody : Cmd :=
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
    emitFalse

/-- One inner iteration of `emitFinal`'s step loop: the `forr` spine node then
one final-step constraint. -/
def finalStepIterBody : Cmd := emitForrTag ;; finalStepBody

/-- One final string: parse it off `SCANF` (`readOneFinal`) then the step
disjunction (`listOr` over offsets), closed with `falseFml`. -/
def finalStringBody : Cmd :=
  Cmd.op (.nonEmpty TFLG SCANF) ;;
  Cmd.ifBit TFLG
    ( emitForrTag ;;
      readOneFinal ;;
      Cmd.forBnd KFSTEP LREG1 finalStepIterBody ;;
      emitFalse )
    (Cmd.op (.clear KTMP))

/-- `serF (encodeFinalConstraint C)` = `listOr` over final strings of
(`listOr` over steps of `encodeFinalAtStep`). -/
def emitFinal : Cmd :=
  Cmd.op (.clear STEPSL) ;;
  Cmd.forBnd KTMP STEPS (Cmd.op (.concat STEPSL STEPSL LREG)) ;;
  Cmd.op (.copy SCANF FINAL) ;;
  Cmd.forBnd KFS FINAL finalStringBody ;;
  emitFalse

/-! ### `emitFinal_run` — the accepting-substring disjunction (the two-level
`listOr` fold)

Mirror of `emitAllSteps_run`'s two-level `listAnd` fold, one tag up (`[1,0]`
`forr` nodes, `falseFml`-closed rather than `[0,1]`/`ftrue`). `orPrefix` is the
`forr`-tag serialization prefix of a formula list, stated once so it serves
both levels (offsets within one final string, strings within the tableau);
`serF_listOr` closes it with `falseFml`. The inner (per-string) level
accumulates `encodeFinalAtStep C step bits` over `List.range (L+1)` (each
iteration one black-boxed `finalStepBody_run`); the outer level parses one
final string off the sentinel stream per iteration (`readOneFinal_run`) and
accumulates `encodeFinalString C bits`. -/

/-- The `forr`-tag serialization prefix of a formula list (no closing
`falseFml`) — the `listOr` analogue of `andPrefix`, at either level. -/
def orPrefix : List formula → List Nat
  | [] => []
  | f :: fs => [1, 0] ++ serF f ++ orPrefix fs

theorem orPrefix_append (xs ys : List formula) :
    orPrefix (xs ++ ys) = orPrefix xs ++ orPrefix ys := by
  induction xs with
  | nil => simp [orPrefix]
  | cons f fs ih =>
      simp only [List.cons_append, orPrefix, ih, List.append_assoc]

/-- Closing the accumulated `forr` prefix with `falseFml` gives exactly the
serialized disjunction — the `listOr` analogue of `serF_listAnd`. -/
theorem serF_listOr (fs : List formula) :
    serF (listOr fs) = orPrefix fs ++ serF falseFml := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      show serF (.forr f (listOr fs)) = _
      simp [serF, orPrefix, ih, List.append_assoc]

/-- **`finalStepBody` is correct**: with `STEPSL = 1^(steps·L)`, `KFSTEP =
1^step`, `OFFSET = 1^offset`, `BLEN = 1^|bits|`, `LREG = 1^L`, `FBITS =
bitsNat bits`, it appends `serF (encodeFinalAtStep C step bits)` to `OUT`
(guard-pass ⇒ the literal block off a fresh `FBITS` copy; guard-fail ⇒
`falseFml`). -/
theorem finalStepBody_run (C : BinaryCC) (step : Nat) (bits : List Bool) (u : State)
    (hSTEPSL : State.get u STEPSL = List.replicate (C.steps * C.init.length) 1)
    (hKFSTEP : State.get u KFSTEP = List.replicate step 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hBLEN : State.get u BLEN = List.replicate bits.length 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hFBITS : State.get u FBITS = FlatCCBinFree.bitsNat bits)
    (hZ : State.get u ZERO = []) :
    State.get (finalStepBody.eval u) OUT
        = State.get u OUT ++ serF (encodeFinalAtStep C step bits)
    ∧ State.get (finalStepBody.eval u) ZERO = []
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
        r ≠ ZERO → r ≠ KTMP2 → r ≠ STEPO → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
        r ≠ FSTART → State.get (finalStepBody.eval u) r = State.get u r) := by
  -- w1: clear STEPO
  have e1 : (Cmd.op (.clear STEPO)).eval u = u.set STEPO [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w1 := u.set STEPO [] with hw1
  have hw1frame : ∀ r : Var, r ≠ STEPO → State.get w1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1STEPO : State.get w1 STEPO = [] := State.get_set_eq _ _ _
  have hw1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hw1frame OFFSET (by decide)]; exact hOFF
  have hw1KFSTEPlen : (State.get w1 KFSTEP).length = step := by
    rw [hw1frame KFSTEP (by decide), hKFSTEP, List.length_replicate]
  clear_value w1
  -- w2: STEPO := 1^(step·offset)
  obtain ⟨h2STEPO, h2frame⟩ :=
    unaryMulLoop_run KTMP2 KFSTEP OFFSET STEPO w1 C.offset step
      (by decide) (by decide) (by decide) hw1OFF hw1KFSTEPlen hw1STEPO
  set w2 := (Cmd.forBnd KTMP2 KFSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).eval w1
    with hw2
  clear_value w2
  have hw2BLEN : State.get w2 BLEN = List.replicate bits.length 1 := by
    rw [h2frame BLEN (by decide) (by decide), hw1frame BLEN (by decide)]; exact hBLEN
  -- w3: SUMW := STEPO ++ BLEN
  have e3 : (Cmd.op (.concat SUMW STEPO BLEN)).eval w2
      = w2.set SUMW (List.replicate (step * C.offset + bits.length) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, h2STEPO, hw2BLEN]
    congr 1
    rw [List.replicate_add]
  set w3 := w2.set SUMW (List.replicate (step * C.offset + bits.length) 1) with hw3
  have hw3frame : ∀ r : Var, r ≠ SUMW → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3SUMW : State.get w3 SUMW = List.replicate (step * C.offset + bits.length) 1 :=
    State.get_set_eq _ _ _
  clear_value w3
  -- w4: REM := copy SUMW
  have e4 : (Cmd.op (.copy REM SUMW)).eval w3
      = w3.set REM (List.replicate (step * C.offset + bits.length) 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw3SUMW]
  set w4 := w3.set REM (List.replicate (step * C.offset + bits.length) 1) with hw4
  have hw4frame : ∀ r : Var, r ≠ REM → State.get w4 r = State.get w3 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw4REM : State.get w4 REM = List.replicate (step * C.offset + bits.length) 1 :=
    State.get_set_eq _ _ _
  have hw4LREGlen : (State.get w4 LREG).length = C.init.length := by
    rw [hw4frame LREG (by decide), hw3frame LREG (by decide),
      h2frame LREG (by decide) (by decide), hw1frame LREG (by decide), hLREG,
      List.length_replicate]
  clear_value w4
  -- w5: the truncated-subtraction loop
  obtain ⟨h5REM, h5frame⟩ :=
    unarySubLoop_run KTMP2 LREG REM w4 (step * C.offset + bits.length) C.init.length
      (by decide) hw4LREGlen hw4REM
  set w5 := (Cmd.forBnd KTMP2 LREG (Cmd.op (.tail REM REM))).eval w4 with hw5
  clear_value w5
  -- registers threaded to w5 (used by both guard branches)
  have h5chain : ∀ r : Var, r ≠ STEPO → r ≠ KTMP2 → r ≠ SUMW → r ≠ REM →
      State.get w5 r = State.get u r := by
    intro r h1 h2 h3 h4
    rw [h5frame r h4 h2, hw4frame r h4, hw3frame r h3, h2frame r h1 h2, hw1frame r h1]
  have h5OUT : State.get w5 OUT = State.get u OUT :=
    h5chain OUT (by decide) (by decide) (by decide) (by decide)
  have h5Z : State.get w5 ZERO = [] := by
    rw [h5chain ZERO (by decide) (by decide) (by decide) (by decide)]; exact hZ
  have h5STEPO : State.get w5 STEPO = List.replicate (step * C.offset) 1 := by
    rw [h5frame STEPO (by decide) (by decide), hw4frame STEPO (by decide),
      hw3frame STEPO (by decide)]
    exact h2STEPO
  have h5STEPSL : State.get w5 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
    rw [h5chain STEPSL (by decide) (by decide) (by decide) (by decide)]; exact hSTEPSL
  have h5FBITS : State.get w5 FBITS = FlatCCBinFree.bitsNat bits := by
    rw [h5chain FBITS (by decide) (by decide) (by decide) (by decide)]; exact hFBITS
  by_cases hguard : step * C.offset + bits.length ≤ C.init.length
  · -- guard passes: REM empty → GFLG := [1] → the literal block
    have hREM0 : State.get w5 REM = [] := by
      rw [h5REM, Nat.sub_eq_zero_of_le hguard]; rfl
    have hne : (State.get w5 REM).isEmpty = true := by rw [hREM0]; rfl
    have e6 : (Cmd.op (.nonEmpty TFLG REM)).eval w5 = w5.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    set w6 := w5.set TFLG [0] with hw6
    have hw6frame : ∀ r : Var, r ≠ TFLG → State.get w6 r = State.get w5 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw6Tne : State.get w6 TFLG ≠ [1] := by rw [hw6, State.get_set_eq]; decide
    clear_value w6
    have ec : (Cmd.op (.clear GFLG)).eval w6 = w6.set GFLG [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    have ea : (Cmd.op (.appendOne GFLG)).eval (w6.set GFLG []) = w6.set GFLG [1] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, State.set_set, List.nil_append]
    have e7 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w6
        = w6.set GFLG [1] := by
      rw [Cmd.eval_ifBit_false _ _ _ _ hw6Tne, Cmd.eval_seq, ec, ea]
    set w7 := w6.set GFLG [1] with hw7
    have hw7frame : ∀ r : Var, r ≠ GFLG → State.get w7 r = State.get w6 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw7G : State.get w7 GFLG = [1] := State.get_set_eq _ _ _
    clear_value w7
    have h7STEPSL : State.get w7 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
      rw [hw7frame STEPSL (by decide), hw6frame STEPSL (by decide)]; exact h5STEPSL
    have h7STEPO : State.get w7 STEPO = List.replicate (step * C.offset) 1 := by
      rw [hw7frame STEPO (by decide), hw6frame STEPO (by decide)]; exact h5STEPO
    -- w8: FSTART := STEPSL ++ STEPO
    have e8 : (Cmd.op (.concat FSTART STEPSL STEPO)).eval w7
        = w7.set FSTART (List.replicate (C.steps * C.init.length + step * C.offset) 1) := by
      rw [Cmd.eval_op]
      simp only [Op.eval, h7STEPSL, h7STEPO]
      congr 1
      rw [List.replicate_add]
    set w8 := w7.set FSTART (List.replicate (C.steps * C.init.length + step * C.offset) 1)
      with hw8
    have hw8frame : ∀ r : Var, r ≠ FSTART → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8FSTART : State.get w8 FSTART
        = List.replicate (C.steps * C.init.length + step * C.offset) 1 :=
      State.get_set_eq _ _ _
    have h8G : State.get w8 GFLG = [1] := by rw [hw8frame GFLG (by decide)]; exact hw7G
    have h8FBITS : State.get w8 FBITS = FlatCCBinFree.bitsNat bits := by
      rw [hw8frame FBITS (by decide), hw7frame FBITS (by decide),
        hw6frame FBITS (by decide)]
      exact h5FBITS
    have h8OUT : State.get w8 OUT = State.get u OUT := by
      rw [hw8frame OUT (by decide), hw7frame OUT (by decide), hw6frame OUT (by decide)]
      exact h5OUT
    clear_value w8
    -- w9: copy SCAN FBITS
    have e9 : (Cmd.op (.copy SCAN FBITS)).eval w8
        = w8.set SCAN (FlatCCBinFree.bitsNat bits) := by
      rw [Cmd.eval_op]; simp only [Op.eval, h8FBITS]
    set w9 := w8.set SCAN (FlatCCBinFree.bitsNat bits) with hw9
    have hw9frame : ∀ r : Var, r ≠ SCAN → State.get w9 r = State.get w8 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw9SCAN : State.get w9 SCAN = FlatCCBinFree.bitsNat bits := State.get_set_eq _ _ _
    have h9FSTART : State.get w9 FSTART
        = List.replicate (C.steps * C.init.length + step * C.offset) 1 := by
      rw [hw9frame FSTART (by decide)]; exact hw8FSTART
    have h9FBITSlen : (State.get w9 FBITS).length = bits.length := by
      rw [hw9frame FBITS (by decide), h8FBITS,
        show (FlatCCBinFree.bitsNat bits).length = bits.length from List.length_map _]
    have h9OUT : State.get w9 OUT = State.get u OUT := by
      rw [hw9frame OUT (by decide)]; exact h8OUT
    clear_value w9
    obtain ⟨hEmitSCAN, hEmitOUT, hEmitFrame⟩ :=
      emitBitsFromScan_run FSTART FBITS (C.steps * C.init.length + step * C.offset) bits w9
        (by decide) (by decide) (by decide) (by decide) (by decide) h9FSTART h9FBITSlen
        hw9SCAN
    set wF := (emitBitsFromScan FSTART FBITS).eval w9 with hwF
    clear_value wF
    have hstep : encodeFinalAtStep C step bits
        = BinaryCCToFSAT.encodeBitsAt (C.steps * C.init.length + step * C.offset) bits := by
      unfold encodeFinalAtStep
      rw [dif_pos hguard]
    have heval : finalStepBody.eval u = wF := by
      unfold finalStepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, ← hw5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq, e8,
        Cmd.eval_ifBit_true _ _ _ _ h8G, Cmd.eval_seq, e9, ← hwF]
    refine ⟨?_, ?_, ?_⟩
    · rw [heval, hEmitOUT, h9OUT, hstep]
    · rw [heval, hEmitFrame ZERO (by decide) (by decide) (by decide) (by decide) (by decide)]
      rw [hw9frame ZERO (by decide), hw8frame ZERO (by decide), hw7frame ZERO (by decide),
        hw6frame ZERO (by decide)]
      exact h5Z
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      rw [heval, hEmitFrame r h1 h2 h3 h4 h5, hw9frame r h1, hw8frame r h12,
        hw7frame r h11, hw6frame r h4, h5frame r h10 h7, hw4frame r h10,
        hw3frame r h9, h2frame r h8 h7, hw1frame r h8]
  · -- guard fails: REM nonempty → GFLG := [] → falseFml
    obtain ⟨k, hk⟩ : ∃ k, step * C.offset + bits.length - C.init.length = k + 1 :=
      ⟨step * C.offset + bits.length - C.init.length - 1, by omega⟩
    have hne : (State.get w5 REM).isEmpty = false := by rw [h5REM, hk]; rfl
    have e6 : (Cmd.op (.nonEmpty TFLG REM)).eval w5 = w5.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    set w6 := w5.set TFLG [1] with hw6
    have hw6frame : ∀ r : Var, r ≠ TFLG → State.get w6 r = State.get w5 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw6T : State.get w6 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w6
    have e7 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w6
        = w6.set GFLG [] := by
      rw [Cmd.eval_ifBit_true _ _ _ _ hw6T, Cmd.eval_op]
      simp only [Op.eval]
    set w7 := w6.set GFLG [] with hw7
    have hw7frame : ∀ r : Var, r ≠ GFLG → State.get w7 r = State.get w6 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw7Gne : State.get w7 GFLG ≠ [1] := by rw [hw7, State.get_set_eq]; decide
    clear_value w7
    have h7STEPSL : State.get w7 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
      rw [hw7frame STEPSL (by decide), hw6frame STEPSL (by decide)]; exact h5STEPSL
    have h7STEPO : State.get w7 STEPO = List.replicate (step * C.offset) 1 := by
      rw [hw7frame STEPO (by decide), hw6frame STEPO (by decide)]; exact h5STEPO
    -- w8: FSTART := STEPSL ++ STEPO (value unused, but the op still runs)
    have e8 : (Cmd.op (.concat FSTART STEPSL STEPO)).eval w7
        = w7.set FSTART (List.replicate (C.steps * C.init.length + step * C.offset) 1) := by
      rw [Cmd.eval_op]
      simp only [Op.eval, h7STEPSL, h7STEPO]
      congr 1
      rw [List.replicate_add]
    set w8 := w7.set FSTART (List.replicate (C.steps * C.init.length + step * C.offset) 1)
      with hw8
    have hw8frame : ∀ r : Var, r ≠ FSTART → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have h8Gne : State.get w8 GFLG ≠ [1] := by rw [hw8frame GFLG (by decide)]; exact hw7Gne
    have h8OUT : State.get w8 OUT = State.get u OUT := by
      rw [hw8frame OUT (by decide), hw7frame OUT (by decide), hw6frame OUT (by decide)]
      exact h5OUT
    have h8Z : State.get w8 ZERO = [] := by
      rw [hw8frame ZERO (by decide), hw7frame ZERO (by decide), hw6frame ZERO (by decide)]
      exact h5Z
    clear_value w8
    have hstep : encodeFinalAtStep C step bits = falseFml := by
      unfold encodeFinalAtStep
      rw [dif_neg hguard]
    have heval : finalStepBody.eval u = emitFalse.eval w8 := by
      unfold finalStepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, ← hw5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq, e8,
        Cmd.eval_ifBit_false _ _ _ _ h8Gne]
    refine ⟨?_, ?_, ?_⟩
    · rw [heval, emitFalse_run, State.get_set_eq, h8OUT, hstep]; rfl
    · rw [heval, emitFalse_frame _ ZERO (by decide)]; exact h8Z
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      rw [heval, emitFalse_frame _ r h2, hw8frame r h12, hw7frame r h11, hw6frame r h4,
        h5frame r h10 h7, hw4frame r h10, hw3frame r h9, h2frame r h8 h7, hw1frame r h8]

/-- The inner (per-final-string) fold invariant: `OUT` accumulates the
tag-then-step `orPrefix`, `ZERO` stays empty, and everything outside
`finalStepIterBody`'s scratch set (= `finalStepBody`'s ∪ {`KFSTEP`}) is
untouched — the per-string registers (`STEPSL`/`OFFSET`/`BLEN`/`LREG`/`FBITS`)
are recovered through the frame clause. -/
private def FSInv (C : BinaryCC) (bits : List Bool) (u : State) (i : Nat)
    (st : State) : Prop :=
  State.get st OUT = State.get u OUT
      ++ orPrefix ((List.range i).map (fun step => encodeFinalAtStep C step bits))
  ∧ State.get st ZERO = []
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
      r ≠ ZERO → r ≠ KTMP2 → r ≠ STEPO → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
      r ≠ FSTART → r ≠ KFSTEP → State.get st r = State.get u r)

private theorem FSInv_step (C : BinaryCC) (bits : List Bool) (u : State)
    (hSTEPSL : State.get u STEPSL = List.replicate (C.steps * C.init.length) 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hBLEN : State.get u BLEN = List.replicate bits.length 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hFBITS : State.get u FBITS = FlatCCBinFree.bitsNat bits)
    (i : Nat) (st : State) (h : FSInv C bits u i st) :
    FSInv C bits u (i + 1)
      (finalStepIterBody.eval (st.set KFSTEP (List.replicate i 1))) := by
  obtain ⟨hOUT, hZ, hframe⟩ := h
  set w := st.set KFSTEP (List.replicate i 1) with hw
  have hwframe : ∀ r : Var, r ≠ KFSTEP → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwK : State.get w KFSTEP = List.replicate i 1 := State.get_set_eq _ _ _
  clear_value w
  -- w1: the step's forr spine node
  set w1 := emitForrTag.eval w with hw1
  have hw1frame : ∀ r : Var, r ≠ OUT → State.get w1 r = State.get w r := by
    intro r hr; rw [hw1]; exact emitForrTag_frame w r hr
  have hw1OUT : State.get w1 OUT = State.get w OUT ++ [1, 0] := by
    rw [hw1, emitForrTag_run]; exact State.get_set_eq _ _ _
  clear_value w1
  -- registers threaded to w1 for `finalStepBody_run`
  have h1STEPSL : State.get w1 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
    rw [hw1frame STEPSL (by decide), hwframe STEPSL (by decide),
      hframe STEPSL (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hSTEPSL
  have h1KFSTEP : State.get w1 KFSTEP = List.replicate i 1 := by
    rw [hw1frame KFSTEP (by decide)]; exact hwK
  have h1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hw1frame OFFSET (by decide), hwframe OFFSET (by decide),
      hframe OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hOFF
  have h1BLEN : State.get w1 BLEN = List.replicate bits.length 1 := by
    rw [hw1frame BLEN (by decide), hwframe BLEN (by decide),
      hframe BLEN (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hBLEN
  have h1LREG : State.get w1 LREG = List.replicate C.init.length 1 := by
    rw [hw1frame LREG (by decide), hwframe LREG (by decide),
      hframe LREG (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hLREG
  have h1FBITS : State.get w1 FBITS = FlatCCBinFree.bitsNat bits := by
    rw [hw1frame FBITS (by decide), hwframe FBITS (by decide),
      hframe FBITS (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hFBITS
  have h1Z : State.get w1 ZERO = [] := by
    rw [hw1frame ZERO (by decide), hwframe ZERO (by decide)]; exact hZ
  -- w2: the final-step constraint (black-boxed)
  obtain ⟨h2OUT, h2Z, h2frame⟩ :=
    finalStepBody_run C i bits w1 h1STEPSL h1KFSTEP h1OFF h1BLEN h1LREG h1FBITS h1Z
  set w2 := finalStepBody.eval w1 with hw2
  clear_value w2
  have heval : finalStepIterBody.eval w = w2 := by
    unfold finalStepIterBody
    rw [Cmd.eval_seq, ← hw1, ← hw2]
  refine ⟨?_, ?_, ?_⟩
  · rw [heval, h2OUT, hw1OUT, hwframe OUT (by decide), hOUT, List.range_succ,
      List.map_append, orPrefix_append]
    simp [orPrefix, List.append_assoc]
  · rw [heval]; exact h2Z
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    rw [heval, h2frame r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12,
      hw1frame r h2, hwframe r h13,
      hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13]

/-- The inner step loop of `emitFinal`: appends the full per-string tag-then-step
`orPrefix` (`List.range (L+1)` matches `encodeFinalString`'s range). -/
private theorem innerFinalSteps_run (C : BinaryCC) (bits : List Bool) (u : State)
    (hSTEPSL : State.get u STEPSL = List.replicate (C.steps * C.init.length) 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hBLEN : State.get u BLEN = List.replicate bits.length 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u LREG1 = List.replicate (C.init.length + 1) 1)
    (hFBITS : State.get u FBITS = FlatCCBinFree.bitsNat bits)
    (hZ : State.get u ZERO = []) :
    State.get ((Cmd.forBnd KFSTEP LREG1 finalStepIterBody).eval u) OUT
        = State.get u OUT ++ orPrefix
            ((List.range (C.init.length + 1)).map (fun step => encodeFinalAtStep C step bits))
    ∧ State.get ((Cmd.forBnd KFSTEP LREG1 finalStepIterBody).eval u) ZERO = []
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
        r ≠ ZERO → r ≠ KTMP2 → r ≠ STEPO → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
        r ≠ FSTART → r ≠ KFSTEP →
        State.get ((Cmd.forBnd KFSTEP LREG1 finalStepIterBody).eval u) r
          = State.get u r) := by
  have hlen : (State.get u LREG1).length = C.init.length + 1 := by
    rw [hLREG1, List.length_replicate]
  have hbase : FSInv C bits u 0 u := by
    refine ⟨?_, hZ, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    simp [orPrefix]
  have hInv : FSInv C bits u (C.init.length + 1)
      (Cmd.foldlState finalStepIterBody KFSTEP (List.range (C.init.length + 1)) u) :=
    Cmd.foldlState_range_induct finalStepIterBody KFSTEP (C.init.length + 1) u
      (FSInv C bits u) hbase
      (fun i st _ hM => FSInv_step C bits u hSTEPSL hOFF hBLEN hLREG hFBITS i st hM)
  have heval : (Cmd.forBnd KFSTEP LREG1 finalStepIterBody).eval u
      = Cmd.foldlState finalStepIterBody KFSTEP (List.range (C.init.length + 1)) u := by
    rw [Cmd.eval_forBnd, hlen]
  obtain ⟨h1, h2, h3⟩ := hInv
  exact ⟨by rw [heval]; exact h1, by rw [heval]; exact h2,
    fun r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 => by
      rw [heval]
      exact h3 r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13⟩

/-- The final stream's cons view: one string contributes its sentinel
bit-list, pre-associated for the parse. -/
private theorem encFinal_cons (s : List Bool) (fss : List (List Bool)) :
    FlatTCCFree.encFinal ((s :: fss).map FlatCCBinFree.bitsNat)
      = FlatTCCFree.encSList (FlatCCBinFree.bitsNat s)
        ++ FlatTCCFree.encFinal (fss.map FlatCCBinFree.bitsNat) := rfl

/-- The final stream is at least as long as the string count (each string
occupies ≥ 1 cell) — the loop bound `FINAL` covers every string. -/
private theorem length_le_encFinal (fss : List (List Bool)) :
    fss.length ≤ (FlatTCCFree.encFinal (fss.map FlatCCBinFree.bitsNat)).length := by
  induction fss with
  | nil => simp
  | cons s fss ih =>
      rw [encFinal_cons, List.length_cons, List.length_append]
      have h1 := FlatTCCFree.encSList_length_pos (FlatCCBinFree.bitsNat s)
      omega

/-- The outer (per-tableau) fold invariant: `SCANF` holds the unprocessed final
stream, `OUT` the serialized string `orPrefix`; `ZERO` stays empty. The frozen
per-tableau registers (`STEPSL`/`OFFSET`/`LREG`/`LREG1`) are recovered through
the frame clause; `BLEN`/`FBITS` are (re)set each iteration by `readOneFinal`. -/
private def FFInv (C : BinaryCC) (u : State) (j : Nat) (st : State) : Prop :=
  State.get st SCANF
      = FlatTCCFree.encFinal ((C.final.drop j).map FlatCCBinFree.bitsNat)
  ∧ State.get st OUT = State.get u OUT
      ++ orPrefix ((C.final.take j).map (encodeFinalString C))
  ∧ State.get st ZERO = []
  ∧ (∀ r : Var, r ≠ SCANF → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
      r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KTMP2 → r ≠ FBITS →
      r ≠ BLEN → r ≠ SCAN → r ≠ STEPO → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
      r ≠ FSTART → r ≠ KFSTEP → r ≠ KFS → State.get st r = State.get u r)

private theorem FFInv_step (C : BinaryCC) (u : State)
    (hSTEPSL : State.get u STEPSL = List.replicate (C.steps * C.init.length) 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u LREG1 = List.replicate (C.init.length + 1) 1)
    (j : Nat) (st : State) (h : FFInv C u j st) :
    FFInv C u (j + 1) (finalStringBody.eval (st.set KFS (List.replicate j 1))) := by
  obtain ⟨hSCAN, hOUT, hZERO, hframe⟩ := h
  set w := st.set KFS (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KFS → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSCAN : State.get w SCANF
      = FlatTCCFree.encFinal ((C.final.drop j).map FlatCCBinFree.bitsNat) := by
    rw [hwframe SCANF (by decide)]; exact hSCAN
  have hwOUT : State.get w OUT
      = State.get u OUT ++ orPrefix ((C.final.take j).map (encodeFinalString C)) := by
    rw [hwframe OUT (by decide)]; exact hOUT
  have hwZ : State.get w ZERO = [] := by rw [hwframe ZERO (by decide)]; exact hZERO
  -- the frozen per-tableau registers, recovered on `w`
  have hwchain : ∀ r : Var, r ≠ SCANF → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
      r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KTMP2 → r ≠ FBITS →
      r ≠ BLEN → r ≠ SCAN → r ≠ STEPO → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
      r ≠ FSTART → r ≠ KFSTEP → r ≠ KFS → State.get w r = State.get u r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    rw [hwframe r h20,
      hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20]
  have hwSTEPSL : State.get w STEPSL = List.replicate (C.steps * C.init.length) 1 := by
    rw [hwchain STEPSL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hSTEPSL
  have hwOFF : State.get w OFFSET = List.replicate C.offset 1 := by
    rw [hwchain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hOFF
  have hwLREG : State.get w LREG = List.replicate C.init.length 1 := by
    rw [hwchain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG
  have hwLREG1 : State.get w LREG1 = List.replicate (C.init.length + 1) 1 := by
    rw [hwchain LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG1
  clear_value w
  by_cases hj : j < C.final.length
  · -- live iteration: one final string off the stream
    have hdrop : C.final.drop j = C.final[j] :: C.final.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    have htake : C.final.take (j + 1) = C.final.take j ++ [C.final[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    set bits := C.final[j] with hbits
    clear_value bits
    set REST := FlatTCCFree.encFinal ((C.final.drop (j + 1)).map FlatCCBinFree.bitsNat)
      with hREST
    have hSCANw : State.get w SCANF
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ REST := by
      rw [hwSCAN, hdrop, encFinal_cons, ← hREST]
    have hne : (State.get w SCANF).isEmpty = false := by
      rw [hSCANw]; exact encSList_append_isEmpty _ _
    -- w1: nonEmpty TFLG SCANF
    have e1 : (Cmd.op (.nonEmpty TFLG SCANF)).eval w = w.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    set w1 := w.set TFLG [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ TFLG → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1T : State.get w1 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w1
    -- w2: the forr spine node
    set w2 := emitForrTag.eval w1 with hw2
    have hw2frame : ∀ r : Var, r ≠ OUT → State.get w2 r = State.get w1 r := by
      intro r hr; rw [hw2]; exact emitForrTag_frame w1 r hr
    have hw2OUT : State.get w2 OUT = State.get w1 OUT ++ [1, 0] := by
      rw [hw2, emitForrTag_run]; exact State.get_set_eq _ _ _
    clear_value w2
    have h2SCANF : State.get w2 SCANF
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ REST := by
      rw [hw2frame SCANF (by decide), hw1frame SCANF (by decide)]; exact hSCANw
    -- w3: parse one final string
    obtain ⟨h3SCANF, h3FBITS, h3BLEN, h3frame⟩ := readOneFinal_run bits REST w2 h2SCANF
    set w3 := readOneFinal.eval w2 with hw3
    clear_value w3
    have h3chain : ∀ r : Var, r ≠ SCANF → r ≠ FBITS → r ≠ BLEN → r ≠ DONE →
        r ≠ EMARK → r ≠ TFLG → r ≠ KTMP → r ≠ KTMP2 → r ≠ OUT →
        State.get w3 r = State.get w r := by
      intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [h3frame r h1 h2 h3 h4 h5 h6 h7 h8, hw2frame r h9, hw1frame r h6]
    have h3STEPSL : State.get w3 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
      rw [h3chain STEPSL (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwSTEPSL
    have h3OFF : State.get w3 OFFSET = List.replicate C.offset 1 := by
      rw [h3chain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwOFF
    have h3LREG : State.get w3 LREG = List.replicate C.init.length 1 := by
      rw [h3chain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwLREG
    have h3LREG1 : State.get w3 LREG1 = List.replicate (C.init.length + 1) 1 := by
      rw [h3chain LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwLREG1
    have h3Z : State.get w3 ZERO = [] := by
      rw [h3chain ZERO (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwZ
    have h3OUT : State.get w3 OUT = State.get u OUT
        ++ orPrefix ((C.final.take j).map (encodeFinalString C)) ++ [1, 0] := by
      rw [h3frame OUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hw2OUT, hw1frame OUT (by decide), hwOUT]
    -- w4: the inner step disjunction
    obtain ⟨h4OUT, h4Z, h4frame⟩ :=
      innerFinalSteps_run C bits w3 h3STEPSL h3OFF h3BLEN h3LREG h3LREG1 h3FBITS h3Z
    set w4 := (Cmd.forBnd KFSTEP LREG1 finalStepIterBody).eval w3 with hw4
    clear_value w4
    have h4SCANF : State.get w4 SCANF = REST := by
      rw [h4frame SCANF (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
      exact h3SCANF
    -- w5: close the inner listOr with falseFml
    set w5 := emitFalse.eval w4 with hw5
    have hw5frame : ∀ r : Var, r ≠ OUT → State.get w5 r = State.get w4 r := by
      intro r hr; rw [hw5]; exact emitFalse_frame w4 r hr
    have hw5OUT : State.get w5 OUT = State.get w4 OUT ++ [1, 1, 0, 0, 0] := by
      rw [hw5, emitFalse_run]; exact State.get_set_eq _ _ _
    clear_value w5
    have heval : finalStringBody.eval w = w5 := by
      unfold finalStringBody
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_true _ _ _ _ hw1T, Cmd.eval_seq, ← hw2,
        Cmd.eval_seq, ← hw3, Cmd.eval_seq, ← hw4, ← hw5]
    rw [heval]
    have hstr : serF (encodeFinalString C bits)
        = orPrefix ((List.range (C.init.length + 1)).map
            (fun step => encodeFinalAtStep C step bits)) ++ serF falseFml := by
      show serF (listOr _) = _
      rw [serF_listOr]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hw5frame SCANF (by decide), h4SCANF, hREST]
    · have hsnoc : orPrefix ((C.final.take (j + 1)).map (encodeFinalString C))
          = orPrefix ((C.final.take j).map (encodeFinalString C))
            ++ ([1, 0] ++ serF (encodeFinalString C bits)) := by
        rw [htake, List.map_append, orPrefix_append]
        simp [orPrefix]
      rw [hw5OUT, h4OUT, h3OUT, hsnoc, hstr,
        show serF falseFml = [1, 1, 0, 0, 0] from rfl]
      simp [List.append_assoc]
    · rw [hw5frame ZERO (by decide)]; exact h4Z
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
      rw [hw5frame r h2,
        h4frame r h13 h2 h3 h4 h5 h8 h10 h14 h15 h16 h17 h18 h19,
        h3chain r h1 h11 h12 h6 h7 h4 h9 h10 h2, hwframe r h20,
        hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20]
  · -- idle iteration: stream exhausted, `nonEmpty` falls through
    have hlen : C.final.length ≤ j := Nat.le_of_not_lt hj
    have hSCANw : State.get w SCANF = [] := by
      rw [hwSCAN, List.drop_eq_nil_of_le hlen]; rfl
    have hne : (State.get w SCANF).isEmpty = true := by rw [hSCANw]; rfl
    have e1 : (Cmd.op (.nonEmpty TFLG SCANF)).eval w = w.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    set w1 := w.set TFLG [0] with hw1
    have hw1Tne : State.get w1 TFLG ≠ [1] := by rw [hw1, State.get_set_eq]; decide
    have e2 : (Cmd.op (.clear KTMP)).eval w1 = w1.set KTMP [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    set wF := w1.set KTMP [] with hwF
    have heval : finalStringBody.eval w = wF := by
      unfold finalStringBody
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_false _ _ _ _ hw1Tne, e2]
    have hgetF : ∀ r : Var, r ≠ TFLG → r ≠ KTMP → State.get wF r = State.get w r := by
      intro r h1 h2
      rw [hwF, State.get_set_ne _ _ _ _ h2, hw1, State.get_set_ne _ _ _ _ h1]
    rw [heval]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hgetF SCANF (by decide) (by decide), hwSCAN, List.drop_eq_nil_of_le hlen,
        List.drop_eq_nil_of_le (by omega)]
    · rw [hgetF OUT (by decide) (by decide), hwOUT, List.take_of_length_le hlen,
        List.take_of_length_le (by omega)]
    · rw [hgetF ZERO (by decide) (by decide)]; exact hwZ
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
      rw [hgetF r h4 h9, hwframe r h20,
        hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20]

/-- Closing the accumulated string prefix with `falseFml` gives exactly the
serialized final constraint (`encodeFinalConstraint C` is `listOr
(C.final.map (encodeFinalString C))`). -/
theorem serF_encodeFinalConstraint (C : BinaryCC) :
    serF (encodeFinalConstraint C)
      = orPrefix (C.final.map (encodeFinalString C)) ++ serF falseFml := by
  show serF (listOr _) = _
  rw [serF_listOr]

/-- **`emitFinal` is correct**: with `STEPS`/`LREG`/`LREG1` (from
`encodeIn`+`precompLen`), `OFFSET` (pinned by `encodeIn`) and the final stream
in `FINAL`, it computes `STEPSL := 1^(steps·L)`, copies the stream into a
scratch, and appends `serF (encodeFinalConstraint C)` to `OUT` (consuming the
copy, so `FINAL` itself is untouched). -/
theorem emitFinal_run (C : BinaryCC) (u : State)
    (hSTEPS : State.get u STEPS = List.replicate C.steps 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u LREG1 = List.replicate (C.init.length + 1) 1)
    (hFINAL : State.get u FINAL = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat))
    (hZ : State.get u ZERO = []) :
    State.get (emitFinal.eval u) OUT
        = State.get u OUT ++ serF (encodeFinalConstraint C)
    ∧ State.get (emitFinal.eval u) ZERO = []
    ∧ (∀ r : Var, r ≠ SCANF → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
        r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KTMP2 → r ≠ FBITS →
        r ≠ BLEN → r ≠ SCAN → r ≠ STEPO → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
        r ≠ FSTART → r ≠ KFSTEP → r ≠ KFS → r ≠ STEPSL →
        State.get (emitFinal.eval u) r = State.get u r) := by
  -- u0: clear STEPSL
  have e0clear : (Cmd.op (.clear STEPSL)).eval u = u.set STEPSL [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u0 := u.set STEPSL [] with hu0
  have hu0frame : ∀ r : Var, r ≠ STEPSL → State.get u0 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu0STEPSL : State.get u0 STEPSL = [] := State.get_set_eq _ _ _
  have hu0LREG : State.get u0 LREG = List.replicate C.init.length 1 := by
    rw [hu0frame LREG (by decide)]; exact hLREG
  have hu0STEPSlen : (State.get u0 STEPS).length = C.steps := by
    rw [hu0frame STEPS (by decide), hSTEPS, List.length_replicate]
  clear_value u0
  -- u1: STEPSL := 1^(steps·L)
  obtain ⟨h1STEPSL, h1mulframe⟩ :=
    unaryMulLoop_run KTMP STEPS LREG STEPSL u0 C.init.length C.steps
      (by decide) (by decide) (by decide) hu0LREG hu0STEPSlen hu0STEPSL
  set u1 := (Cmd.forBnd KTMP STEPS (Cmd.op (.concat STEPSL STEPSL LREG))).eval u0 with hu1
  clear_value u1
  have h1FINAL : State.get u1 FINAL
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := by
    rw [h1mulframe FINAL (by decide) (by decide), hu0frame FINAL (by decide)]; exact hFINAL
  -- u2: copy SCANF FINAL
  have e2copy : (Cmd.op (.copy SCANF FINAL)).eval u1
      = u1.set SCANF (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, h1FINAL]
  set u2 := u1.set SCANF (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)) with hu2
  have hu2frame : ∀ r : Var, r ≠ SCANF → State.get u2 r = State.get u1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu2SCANF : State.get u2 SCANF
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := State.get_set_eq _ _ _
  clear_value u2
  have hu2chain : ∀ r : Var, r ≠ SCANF → r ≠ STEPSL → r ≠ KTMP →
      State.get u2 r = State.get u r := by
    intro r h1 h2 h3
    rw [hu2frame r h1, h1mulframe r h2 h3, hu0frame r h2]
  have h2STEPSL : State.get u2 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
    rw [hu2frame STEPSL (by decide)]; exact h1STEPSL
  have h2OFF : State.get u2 OFFSET = List.replicate C.offset 1 := by
    rw [hu2chain OFFSET (by decide) (by decide) (by decide)]; exact hOFF
  have h2LREG : State.get u2 LREG = List.replicate C.init.length 1 := by
    rw [hu2chain LREG (by decide) (by decide) (by decide)]; exact hLREG
  have h2LREG1 : State.get u2 LREG1 = List.replicate (C.init.length + 1) 1 := by
    rw [hu2chain LREG1 (by decide) (by decide) (by decide)]; exact hLREG1
  have h2Z : State.get u2 ZERO = [] := by
    rw [hu2chain ZERO (by decide) (by decide) (by decide)]; exact hZ
  have h2OUT : State.get u2 OUT = State.get u OUT :=
    hu2chain OUT (by decide) (by decide) (by decide)
  have h2FINAL : State.get u2 FINAL
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := by
    rw [hu2frame FINAL (by decide)]; exact h1FINAL
  have hN : C.final.length ≤ (State.get u2 FINAL).length := by
    rw [h2FINAL]; exact length_le_encFinal C.final
  have hbase : FFInv C u2 0 u2 := by
    refine ⟨by rw [List.drop_zero]; exact hu2SCANF, ?_, h2Z,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    rw [List.take_zero, List.map_nil, show orPrefix [] = [] from rfl, List.append_nil]
  have hInv : FFInv C u2 (State.get u2 FINAL).length
      (Cmd.foldlState finalStringBody KFS
        (List.range (State.get u2 FINAL).length) u2) :=
    Cmd.foldlState_range_induct _ KFS _ u2 (FFInv C u2) hbase
      (fun j st _ hM => FFInv_step C u2 h2STEPSL h2OFF h2LREG h2LREG1 j st hM)
  obtain ⟨hSCf, hOUTf, hZf, hframef⟩ := hInv
  have heval : emitFinal.eval u
      = emitFalse.eval (Cmd.foldlState finalStringBody KFS
          (List.range (State.get u2 FINAL).length) u2) := by
    unfold emitFinal
    rw [Cmd.eval_seq, e0clear, Cmd.eval_seq, ← hu1, Cmd.eval_seq, e2copy, Cmd.eval_seq,
      Cmd.eval_forBnd]
  refine ⟨?_, ?_, ?_⟩
  · rw [heval, emitFalse_run, State.get_set_eq, hOUTf, List.take_of_length_le hN, h2OUT,
      List.append_assoc, serF_encodeFinalConstraint]
    rfl
  · rw [heval, emitFalse_frame _ ZERO (by decide)]; exact hZf
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
    rw [heval, emitFalse_frame _ r h2,
      hframef r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20,
      hu2chain r h1 h21 h9]

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

/-- The outer-loop body of `dvdCheck`: one `X mod D` subtraction round. -/
def dvdBody (D : Var) : Cmd :=
  Cmd.op (.copy MCHK D) ;;
  Cmd.forBnd KTMP2 MREM (Cmd.op (.tail MCHK MCHK)) ;;
  Cmd.op (.nonEmpty MGE MCHK) ;;
  Cmd.ifBit MGE
    (Cmd.op (.clear ZERO))
    (Cmd.forBnd KTMP2 D (Cmd.op (.tail MREM MREM)))

/-- `TFLG := [1]` iff `|D|` divides `|X|`, via `X mod D` by truncated
repeated subtraction. -/
def dvdCheck (X D : Nat) : Cmd :=
  Cmd.op (.copy MREM X) ;;
  Cmd.forBnd KTMP X (dvdBody D) ;;
  Cmd.op (.nonEmpty TFLG MREM) ;;
  Cmd.ifBit TFLG (Cmd.op (.clear TFLG)) (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))

/-- Element-parse body: consume one `encSElem` off `SCANW`, `appendOne CLEN`. -/
def cardLenElemBody : Cmd :=
  Cmd.ifBit DONE (Cmd.op (.clear ZERO))
    ( Cmd.op (.head EMARK SCANW) ;;
      Cmd.ifBit EMARK
        ( Cmd.op (.tail SCANW SCANW) ;; Cmd.op (.head TFLG SCANW) ;;
          Cmd.ifBit TFLG (Cmd.op (.tail SCANW SCANW) ;; Cmd.op (.tail SCANW SCANW))
                         (Cmd.op (.tail SCANW SCANW)) ;;
          Cmd.op (.appendOne CLEN) )
        ( Cmd.op (.tail SCANW SCANW) ;;
          Cmd.op (.clear DONE) ;; Cmd.op (.appendOne DONE) ) )

/-- Per-item length parse (prem or conc): consume one `encSList` off `SCANW`,
count its bits into `CLEN`, and AND `1^len = 1^width` into `GWF`. -/
def cardLenItem : Cmd :=
  Cmd.op (.clear CLEN) ;; Cmd.op (.clear DONE) ;;
  Cmd.forBnd KBIT SCANW cardLenElemBody ;;
  Cmd.op (.eqBit TFLG CLEN WIDTH) ;; andFlag TFLG

/-- Per-card body of `cardLenCheck`: if the stream is non-empty, parse prem then
conc; otherwise idle. -/
def cardLenCardBody : Cmd :=
  Cmd.op (.nonEmpty TFLG SCANW) ;;
  Cmd.ifBit TFLG (cardLenItem ;; cardLenItem) (Cmd.op (.clear KTMP))

/-- Every card's prem and conc length `= width`, ANDed into `GWF`. -/
def cardLenCheck : Cmd :=
  Cmd.op (.copy SCANW CARDS) ;;
  Cmd.forBnd KCARD CARDS cardLenCardBody

/-- The full wellformedness flag into `GWF` (assumes `precompLen` ran). -/
def computeWF : Cmd :=
  Cmd.op (.clear GWF) ;; Cmd.op (.appendOne GWF) ;;
  Cmd.op (.nonEmpty TFLG WIDTH) ;; andFlag TFLG ;;         -- width > 0
  Cmd.op (.nonEmpty TFLG OFFSET) ;; andFlag TFLG ;;        -- offset > 0
  leCheck WIDTH LREG ;; andFlag TFLG ;;                    -- width ≤ L
  dvdCheck WIDTH OFFSET ;; andFlag TFLG ;;                 -- offset | width
  dvdCheck LREG OFFSET ;; andFlag TFLG ;;                  -- offset | L
  cardLenCheck                                             -- ∀ card, |prem|=|conc|=width

/-! ### `computeWF` correctness — run lemmas for the guard checks. -/

/-- `leCheck X Y` sets `TFLG = [1]` iff `a ≤ b` (where `X = 1^a`, `|Y| = b`),
touching only `MREM`/`MGE`/`TFLG`. -/
theorem leCheck_run (X Y : Var) (a b : Nat) (s : State)
    (hYM : Y ≠ MREM)
    (hX : State.get s X = List.replicate a 1)
    (hY : (State.get s Y).length = b) :
    State.get ((leCheck X Y).eval s) TFLG = (if a ≤ b then [1] else [])
    ∧ (∀ r : Var, r ≠ MREM → r ≠ MGE → r ≠ TFLG →
        State.get ((leCheck X Y).eval s) r = State.get s r) := by
  -- step 1: copy MREM X
  have e1 : (Cmd.op (.copy MREM X)).eval s = s.set MREM (List.replicate a 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hX]
  set w1 := s.set MREM (List.replicate a 1) with hw1
  have hw1frame : ∀ r : Var, r ≠ MREM → State.get w1 r = State.get s r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1M : State.get w1 MREM = List.replicate a 1 := State.get_set_eq _ _ _
  have hw1Y : (State.get w1 Y).length = b := by rw [hw1frame Y hYM]; exact hY
  clear_value w1
  -- step 2: subtract loop  MREM := 1^(a-b)
  obtain ⟨hsubM, hsubF⟩ := unarySubLoop_run MGE Y MREM w1 a b (by decide) hw1Y hw1M
  set w2 := (Cmd.forBnd MGE Y (Cmd.op (.tail MREM MREM))).eval w1 with hw2
  have hw2frame : ∀ r : Var, r ≠ MREM → r ≠ MGE → State.get w2 r = State.get w1 r := hsubF
  have hw2M : State.get w2 MREM = List.replicate (a - b) 1 := hsubM
  clear_value w2
  -- step 3: nonEmpty TFLG MREM
  have e3 : (Cmd.op (.nonEmpty TFLG MREM)).eval w2
      = w2.set TFLG (if (List.replicate (a-b) 1 : List Nat).isEmpty then [0] else [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw2M]
  set w3 := w2.set TFLG (if (List.replicate (a-b) 1 : List Nat).isEmpty then [0] else [1]) with hw3
  have hw3frame : ∀ r : Var, r ≠ TFLG → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3T : State.get w3 TFLG = (if (List.replicate (a-b) 1 : List Nat).isEmpty then [0] else [1]) :=
    State.get_set_eq _ _ _
  clear_value w3
  -- step 4: ifBit flip
  have heval : (leCheck X Y).eval s = (Cmd.ifBit TFLG (Cmd.op (.clear TFLG))
      (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))).eval w3 := by
    unfold leCheck
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3]
  by_cases hab : a ≤ b
  · -- a ≤ b : a - b = 0, MREM empty, TFLG=[0], flip to [1]
    have hz : a - b = 0 := Nat.sub_eq_zero_of_le hab
    have hTne : State.get w3 TFLG ≠ [1] := by rw [hw3T, hz]; decide
    have e4 : (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG)).eval w3 = w3.set TFLG [1] := by
      rw [Cmd.eval_seq, Cmd.eval_op]
      simp only [Op.eval]
      rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, State.set_set, List.nil_append]
    constructor
    · rw [heval, Cmd.eval_ifBit_false _ _ _ _ hTne, e4, State.get_set_eq, if_pos hab]
    · intro r h1 h2 h3
      rw [heval, Cmd.eval_ifBit_false _ _ _ _ hTne, e4, State.get_set_ne _ _ _ _ h3,
        hw3frame r h3, hw2frame r h1 h2, hw1frame r h1]
  · -- a > b : a - b > 0, MREM nonempty, TFLG=[1], flip to []
    have hz : a - b ≠ 0 := by omega
    have hTe : State.get w3 TFLG = [1] := by
      obtain ⟨k, hk⟩ : ∃ k, a - b = k + 1 := ⟨a - b - 1, by omega⟩
      rw [hw3T, hk]; simp only [List.replicate_succ, List.isEmpty_cons, Bool.false_eq_true,
        if_false]
    have e4 : (Cmd.op (.clear TFLG)).eval w3 = w3.set TFLG [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    constructor
    · rw [heval, Cmd.eval_ifBit_true _ _ _ _ hTe, e4, State.get_set_eq, if_neg hab]
    · intro r h1 h2 h3
      rw [heval, Cmd.eval_ifBit_true _ _ _ _ hTe, e4, State.get_set_ne _ _ _ _ h3,
        hw3frame r h3, hw2frame r h1 h2, hw1frame r h1]

namespace DvdArith
def subMod (a d : Nat) : Nat → Nat
  | 0 => a
  | i + 1 => if d ≤ subMod a d i then subMod a d i - d else subMod a d i
theorem subMod_succ (a d i : Nat) :
    subMod a d (i+1) = if d ≤ subMod a d i then subMod a d i - d else subMod a d i := rfl
theorem subMod_le (a d : Nat) : ∀ i, subMod a d i ≤ a
  | 0 => Nat.le_refl a
  | i + 1 => by
      unfold subMod; split
      · exact Nat.le_trans (Nat.sub_le _ _) (subMod_le a d i)
      · exact subMod_le a d i
theorem subMod_dvd (a d : Nat) : ∀ i, d ∣ (a - subMod a d i)
  | 0 => by simp [subMod]
  | i + 1 => by
      have ih := subMod_dvd a d i
      have hle := subMod_le a d i
      unfold subMod; split
      · rename_i h
        have he : a - (subMod a d i - d) = (a - subMod a d i) + d := by omega
        rw [he]; exact Nat.dvd_add ih (dvd_refl d)
      · exact ih
theorem subMod_lt (a d : Nat) (hd : 1 ≤ d) : ∀ i, subMod a d i < d ∨ subMod a d i ≤ a - i
  | 0 => Or.inr (by simp [subMod])
  | i + 1 => by
      rcases subMod_lt a d hd i with h | h
      · left; unfold subMod; split
        · rename_i hge; omega
        · exact h
      · unfold subMod; split
        · rename_i hge; right; omega
        · rename_i hlt; left; omega
theorem subMod_eq_mod (a d : Nat) : subMod a d a = a % d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hz : ∀ i, subMod a 0 i = a := by
      intro i; induction i with
      | zero => rfl
      | succ i ih => unfold subMod; rw [ih]; simp
    rw [hz]; simp
  · have hlt : subMod a d a < d := by
      rcases subMod_lt a d hd a with h | h
      · exact h
      · omega
    have hdvd := subMod_dvd a d a
    have hle := subMod_le a d a
    obtain ⟨k, hk⟩ := hdvd
    set r := subMod a d a with hr
    have hak : a = r + d * k := by omega
    rw [hak, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
end DvdArith

/-- Loop invariant: after `j` iterations, `MREM = 1^(subMod a d j)`. -/
private def DInv (a d : Nat) (u : State) (j : Nat) (st : State) : Prop :=
  State.get st MREM = List.replicate (DvdArith.subMod a d j) 1
  ∧ State.get st ZERO = []
  ∧ (∀ r : Var, r ≠ MREM → r ≠ MCHK → r ≠ MGE → r ≠ KTMP → r ≠ KTMP2 → r ≠ ZERO →
       State.get st r = State.get u r)

private theorem dvdBody_step (a d : Nat) (D : Var) (u : State)
    (hDM : D ≠ MREM) (hDC : D ≠ MCHK) (hDG : D ≠ MGE) (hDK : D ≠ KTMP)
    (hDK2 : D ≠ KTMP2) (hDZ : D ≠ ZERO)
    (hUD : State.get u D = List.replicate d 1)
    (j : Nat) (st : State) (h : DInv a d u j st) :
    DInv a d u (j + 1) ((dvdBody D).eval (st.set KTMP (List.replicate j 1))) := by
  obtain ⟨hMREM, hZ, hframe⟩ := h
  set w := st.set KTMP (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KTMP → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwM : State.get w MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hwframe MREM (by decide)]; exact hMREM
  have hwZ : State.get w ZERO = [] := by rw [hwframe ZERO (by decide)]; exact hZ
  have hwD : State.get w D = List.replicate d 1 := by
    rw [hwframe D hDK, hframe D hDM hDC hDG hDK hDK2 hDZ]; exact hUD
  clear_value w
  -- step 1: copy MCHK D
  have e1 : (Cmd.op (.copy MCHK D)).eval w = w.set MCHK (List.replicate d 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hwD]
  set w1 := w.set MCHK (List.replicate d 1) with hw1
  have hw1frame : ∀ r : Var, r ≠ MCHK → State.get w1 r = State.get w r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1C : State.get w1 MCHK = List.replicate d 1 := State.get_set_eq _ _ _
  have hw1M : State.get w1 MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hw1frame MREM (by decide)]; exact hwM
  have hw1D : State.get w1 D = List.replicate d 1 := by
    rw [hw1frame D hDC]; exact hwD
  have hw1Z : State.get w1 ZERO = [] := by rw [hw1frame ZERO (by decide)]; exact hwZ
  clear_value w1
  -- step 2: inner sub loop  MCHK := 1^(d - subMod)
  have hw1Mlen : (State.get w1 MREM).length = DvdArith.subMod a d j := by
    rw [hw1M, List.length_replicate]
  obtain ⟨hsubC, hsubF⟩ := unarySubLoop_run KTMP2 MREM MCHK w1 d (DvdArith.subMod a d j)
    (by decide) hw1Mlen hw1C
  set w2 := (Cmd.forBnd KTMP2 MREM (Cmd.op (.tail MCHK MCHK))).eval w1 with hw2
  have hw2C : State.get w2 MCHK = List.replicate (d - DvdArith.subMod a d j) 1 := hsubC
  have hw2frame : ∀ r : Var, r ≠ MCHK → r ≠ KTMP2 → State.get w2 r = State.get w1 r := hsubF
  have hw2M : State.get w2 MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hw2frame MREM (by decide) (by decide)]; exact hw1M
  have hw2D : State.get w2 D = List.replicate d 1 := by
    rw [hw2frame D hDC hDK2]; exact hw1D
  have hw2Z : State.get w2 ZERO = [] := by
    rw [hw2frame ZERO (by decide) (by decide)]; exact hw1Z
  clear_value w2
  -- step 3: nonEmpty MGE MCHK
  have e3 : (Cmd.op (.nonEmpty MGE MCHK)).eval w2
      = w2.set MGE (if (List.replicate (d - DvdArith.subMod a d j) 1 : List Nat).isEmpty
          then [0] else [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw2C]
  set w3 := w2.set MGE (if (List.replicate (d - DvdArith.subMod a d j) 1 : List Nat).isEmpty
      then [0] else [1]) with hw3
  have hw3frame : ∀ r : Var, r ≠ MGE → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3M : State.get w3 MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hw3frame MREM (by decide)]; exact hw2M
  have hw3D : State.get w3 D = List.replicate d 1 := by
    rw [hw3frame D hDG]; exact hw2D
  have hw3Z : State.get w3 ZERO = [] := by rw [hw3frame ZERO (by decide)]; exact hw2Z
  have hw3G : State.get w3 MGE = (if (List.replicate (d - DvdArith.subMod a d j) 1 : List Nat).isEmpty
      then [0] else [1]) := State.get_set_eq _ _ _
  clear_value w3
  have heval : (dvdBody D).eval w
      = (Cmd.ifBit MGE (Cmd.op (.clear ZERO))
          (Cmd.forBnd KTMP2 D (Cmd.op (.tail MREM MREM)))).eval w3 := by
    unfold dvdBody
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3]
  by_cases hcmp : d ≤ DvdArith.subMod a d j
  · -- subtract branch: d ≤ subMod, MGE ≠ [1] (MCHK empty), MREM -= d
    have hsub_eq : DvdArith.subMod a d (j+1) = DvdArith.subMod a d j - d := by
      rw [DvdArith.subMod_succ, if_pos hcmp]
    have hempty : (List.replicate (d - DvdArith.subMod a d j) 1 : List Nat).isEmpty = true := by
      have : d - DvdArith.subMod a d j = 0 := by omega
      rw [this]; rfl
    have hGne : State.get w3 MGE ≠ [1] := by rw [hw3G, hempty]; decide
    -- inner subtract MREM -= |D|=d
    have hw3Dlen : (State.get w3 D).length = d := by rw [hw3D, List.length_replicate]
    obtain ⟨hs2M, hs2F⟩ := unarySubLoop_run KTMP2 D MREM w3 (DvdArith.subMod a d j) d
      (by decide) hw3Dlen hw3M
    set w4 := (Cmd.forBnd KTMP2 D (Cmd.op (.tail MREM MREM))).eval w3 with hw4
    have heval2 : (dvdBody D).eval w = w4 := by
      rw [heval, Cmd.eval_ifBit_false _ _ _ _ hGne, ← hw4]
    refine ⟨?_, ?_, ?_⟩
    · rw [heval2, hs2M, hsub_eq]
    · rw [heval2, hs2F ZERO (by decide) (by decide)]; exact hw3Z
    · intro r h1 h2 h3 h4 h5 h6
      rw [heval2, hs2F r h1 h5, hw3frame r h3, hw2frame r h2 h5, hw1frame r h2,
        hwframe r h4, hframe r h1 h2 h3 h4 h5 h6]
  · -- no-op branch: d > subMod, MGE = [1], MREM unchanged
    have hsub_eq : DvdArith.subMod a d (j+1) = DvdArith.subMod a d j := by
      rw [DvdArith.subMod_succ, if_neg hcmp]
    have hpos : 0 < d - DvdArith.subMod a d j := by omega
    have hne : (List.replicate (d - DvdArith.subMod a d j) 1 : List Nat).isEmpty = false := by
      obtain ⟨k, hk⟩ : ∃ k, d - DvdArith.subMod a d j = k + 1 := ⟨d - DvdArith.subMod a d j - 1, by omega⟩
      rw [hk]; simp [List.replicate_succ]
    have hGe : State.get w3 MGE = [1] := by rw [hw3G, hne]; simp only [Bool.false_eq_true, if_false]
    have e4 : (Cmd.op (.clear ZERO)).eval w3 = w3.set ZERO [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    have heval2 : (dvdBody D).eval w = w3.set ZERO [] := by
      rw [heval, Cmd.eval_ifBit_true _ _ _ _ hGe, e4]
    refine ⟨?_, ?_, ?_⟩
    · rw [heval2, State.get_set_ne _ _ _ _ (show MREM ≠ ZERO by decide), hw3M, hsub_eq]
    · rw [heval2]; exact State.get_set_eq _ _ _
    · intro r h1 h2 h3 h4 h5 h6
      rw [heval2, State.get_set_ne _ _ _ _ h6, hw3frame r h3, hw2frame r h2 h5,
        hw1frame r h2, hwframe r h4, hframe r h1 h2 h3 h4 h5 h6]

/-- `dvdCheck X D` sets `TFLG = [1]` iff `d ∣ a` (where `X = 1^a`, `D = 1^d`). -/
theorem dvdCheck_run (X D : Var) (a d : Nat) (s : State)
    (hXM : X ≠ MREM)
    (hDM : D ≠ MREM) (hDC : D ≠ MCHK) (hDG : D ≠ MGE) (hDK : D ≠ KTMP)
    (hDK2 : D ≠ KTMP2) (hDZ : D ≠ ZERO)
    (hX : State.get s X = List.replicate a 1)
    (hD : State.get s D = List.replicate d 1)
    (hZ : State.get s ZERO = []) :
    State.get ((dvdCheck X D).eval s) TFLG
        = (if d ∣ a then [1] else [])
    ∧ State.get ((dvdCheck X D).eval s) ZERO = []
    ∧ (∀ r : Var, r ≠ MREM → r ≠ MCHK → r ≠ MGE → r ≠ KTMP → r ≠ KTMP2 →
        r ≠ ZERO → r ≠ TFLG →
        State.get ((dvdCheck X D).eval s) r
          = State.get s r) := by
  -- step 1: copy MREM X
  have e1 : (Cmd.op (.copy MREM X)).eval s = s.set MREM (List.replicate a 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hX]
  set u := s.set MREM (List.replicate a 1) with hu
  have huframe : ∀ r : Var, r ≠ MREM → State.get u r = State.get s r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have huM : State.get u MREM = List.replicate a 1 := State.get_set_eq _ _ _
  have huD : State.get u D = List.replicate d 1 := by rw [huframe D hDM]; exact hD
  have huZ : State.get u ZERO = [] := by rw [huframe ZERO (by decide)]; exact hZ
  have huX : State.get u X = List.replicate a 1 := by rw [huframe X hXM]; exact hX
  clear_value u
  -- outer loop
  have hbase : DInv a d u 0 u := by
    refine ⟨by rw [huM]; rfl, huZ, fun r _ _ _ _ _ _ => rfl⟩
  have hInv : DInv a d u (State.get u X).length
      (Cmd.foldlState (dvdBody D) KTMP (List.range (State.get u X).length) u) :=
    Cmd.foldlState_range_induct _ KTMP _ u (DInv a d u) hbase
      (fun j st _ hM => dvdBody_step a d D u hDM hDC hDG hDK hDK2 hDZ huD j st hM)
  obtain ⟨hLM, hLZ, hLframe⟩ := hInv
  rw [huX, List.length_replicate] at hLM hLZ hLframe
  rw [DvdArith.subMod_eq_mod] at hLM
  set w2 := Cmd.foldlState (dvdBody D) KTMP (List.range a) u with hw2
  clear_value w2
  -- step 3: nonEmpty TFLG MREM
  have e3 : (Cmd.op (.nonEmpty TFLG MREM)).eval w2
      = w2.set TFLG (if (List.replicate (a % d) 1 : List Nat).isEmpty then [0] else [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hLM]
  set w3 := w2.set TFLG (if (List.replicate (a % d) 1 : List Nat).isEmpty then [0] else [1]) with hw3
  have hw3frame : ∀ r : Var, r ≠ TFLG → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3T : State.get w3 TFLG = (if (List.replicate (a % d) 1 : List Nat).isEmpty then [0] else [1]) :=
    State.get_set_eq _ _ _
  clear_value w3
  have heval : (dvdCheck X D).eval s
      = (Cmd.ifBit TFLG (Cmd.op (.clear TFLG))
          (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))).eval w3 := by
    unfold dvdCheck
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, Cmd.eval_forBnd, huX, List.length_replicate,
      ← hw2, Cmd.eval_seq, e3]
  by_cases hdvd : d ∣ a
  · -- d ∣ a : a % d = 0, MREM empty, TFLG=[0], flip to [1]
    have hz : a % d = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
    have hTne : State.get w3 TFLG ≠ [1] := by rw [hw3T, hz]; decide
    have e4 : (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG)).eval w3 = w3.set TFLG [1] := by
      rw [Cmd.eval_seq, Cmd.eval_op]; simp only [Op.eval]
      rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, State.set_set, List.nil_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [heval, Cmd.eval_ifBit_false _ _ _ _ hTne, e4, State.get_set_eq, if_pos hdvd]
    · rw [heval, Cmd.eval_ifBit_false _ _ _ _ hTne, e4,
        State.get_set_ne _ _ _ _ (show ZERO ≠ TFLG by decide), hw3frame ZERO (by decide)]
      exact hLZ
    · intro r h1 h2 h3 h4 h5 h6 h7
      rw [heval, Cmd.eval_ifBit_false _ _ _ _ hTne, e4, State.get_set_ne _ _ _ _ h7,
        hw3frame r h7, hLframe r h1 h2 h3 h4 h5 h6, huframe r h1]
  · -- ¬ d ∣ a : a % d > 0, MREM nonempty, TFLG=[1], flip to []
    have hz : a % d ≠ 0 := fun h => hdvd (Nat.dvd_iff_mod_eq_zero.mpr h)
    have hTe : State.get w3 TFLG = [1] := by
      obtain ⟨k, hk⟩ : ∃ k, a % d = k + 1 := ⟨a % d - 1, by omega⟩
      rw [hw3T, hk]; simp only [List.replicate_succ, List.isEmpty_cons, Bool.false_eq_true, if_false]
    have e4 : (Cmd.op (.clear TFLG)).eval w3 = w3.set TFLG [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    refine ⟨?_, ?_, ?_⟩
    · rw [heval, Cmd.eval_ifBit_true _ _ _ _ hTe, e4, State.get_set_eq, if_neg hdvd]
    · rw [heval, Cmd.eval_ifBit_true _ _ _ _ hTe, e4,
        State.get_set_ne _ _ _ _ (show ZERO ≠ TFLG by decide), hw3frame ZERO (by decide)]
      exact hLZ
    · intro r h1 h2 h3 h4 h5 h6 h7
      rw [heval, Cmd.eval_ifBit_true _ _ _ _ hTe, e4, State.get_set_ne _ _ _ _ h7,
        hw3frame r h7, hLframe r h1 h2 h3 h4 h5 h6, huframe r h1]


def cardLenOK (c : CCCard Bool) (w : Nat) : Bool :=
  decide (c.prem.length = w) && decide (c.conc.length = w)
def cardsOKB (cs : List (CCCard Bool)) (w : Nat) : Bool := cs.all (cardLenOK · w)
theorem cardsOKB_snoc (cs : List (CCCard Bool)) (c : CCCard Bool) (w : Nat) :
    cardsOKB (cs ++ [c]) w = (cardsOKB cs w && cardLenOK c w) := by
  simp [cardsOKB, List.all_append]
/-- Fold one card's two length checks into the running flag. -/
theorem gwf_card_step (P Q : Prop) [Decidable P] [Decidable Q] (b : Bool) (g0 : List Nat) :
    (if Q then (if P then (bif b then g0 else []) else []) else [])
      = (bif (b && (decide P && decide Q)) then g0 else []) := by
  by_cases hP : P <;> by_cases hQ : Q <;> cases b <;> simp [hP, hQ]

private def CEInv (bs : List Bool) (rest : List Nat) (u : State) (i : Nat)
    (st : State) : Prop :=
  (i ≤ bs.length →
      State.get st DONE = []
      ∧ State.get st SCANW = FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bs.drop i)) ++ rest
      ∧ State.get st CLEN = List.replicate i 1)
  ∧ (bs.length < i →
      State.get st DONE = [1]
      ∧ State.get st SCANW = rest
      ∧ State.get st CLEN = List.replicate bs.length 1)
  ∧ (∀ r : Var, r ≠ SCANW → r ≠ CLEN → r ≠ DONE → r ≠ EMARK →
      r ≠ TFLG → r ≠ KBIT → r ≠ ZERO → State.get st r = State.get u r)

private theorem CEInv_step (bs : List Bool) (rest : List Nat) (u : State)
    (i : Nat) (st : State) (h : CEInv bs rest u i st) :
    CEInv bs rest u (i + 1)
      (cardLenElemBody.eval (st.set KBIT (List.replicate i 1))) := by
  obtain ⟨hph1, hph2, hframe⟩ := h
  rcases Nat.lt_trichotomy i bs.length with hi | hi | hi
  · -- live: consume one element, appendOne CLEN
    obtain ⟨hDONE, hSCAN, hCL⟩ := hph1 (le_of_lt hi)
    set w := st.set KBIT (List.replicate i 1) with hw
    have hwframe : ∀ r : Var, r ≠ KBIT → State.get w r = State.get st r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwD : State.get w DONE = [] := by rw [hwframe DONE (by decide)]; exact hDONE
    have hwCL : State.get w CLEN = List.replicate i 1 := by
      rw [hwframe CLEN (by decide)]; exact hCL
    have hdrop : bs.drop i = bs[i] :: bs.drop (i + 1) := List.drop_eq_getElem_cons hi
    set b := bs[i] with hb
    clear_value b
    set T := FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bs.drop (i + 1))) ++ rest with hT
    have hSCANw : State.get w SCANW = 1 :: (List.replicate (cond b 1 0) 1 ++ 0 :: T) := by
      rw [hwframe SCANW (by decide), hSCAN, hdrop, hT]
      show (FlatTCCFree.encSElem (cond b 1 0) ++ FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bs.drop (i + 1)))) ++ rest = _
      rw [List.append_assoc, FlatTCCFree.encSElem_append]
    clear_value w
    have hDONEne : State.get w DONE ≠ [1] := by rw [hwD]; decide
    have e1 : (Cmd.op (.head EMARK SCANW)).eval w = w.set EMARK [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hSCANw]
    set w1 := w.set EMARK [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ EMARK → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1E : State.get w1 EMARK = [1] := State.get_set_eq _ _ _
    have hw1SCAN : State.get w1 SCANW = 1 :: (List.replicate (cond b 1 0) 1 ++ 0 :: T) := by
      rw [hw1frame SCANW (by decide)]; exact hSCANw
    clear_value w1
    have e2 : (Cmd.op (.tail SCANW SCANW)).eval w1
        = w1.set SCANW (List.replicate (cond b 1 0) 1 ++ 0 :: T) := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw1SCAN, List.tail_cons]
    set w2 := w1.set SCANW (List.replicate (cond b 1 0) 1 ++ 0 :: T) with hw2
    have hw2frame : ∀ r : Var, r ≠ SCANW → State.get w2 r = State.get w1 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw2SCAN : State.get w2 SCANW = List.replicate (cond b 1 0) 1 ++ 0 :: T :=
      State.get_set_eq _ _ _
    clear_value w2
    have e3 : (Cmd.op (.head TFLG SCANW)).eval w2 = w2.set TFLG [cond b 1 0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw2SCAN]; cases b <;> rfl
    set w3 := w2.set TFLG [cond b 1 0] with hw3
    have hw3frame : ∀ r : Var, r ≠ TFLG → State.get w3 r = State.get w2 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw3T : State.get w3 TFLG = [cond b 1 0] := State.get_set_eq _ _ _
    have hw3SCAN : State.get w3 SCANW = List.replicate (cond b 1 0) 1 ++ 0 :: T := by
      rw [hw3frame SCANW (by decide)]; exact hw2SCAN
    have hw3CL : State.get w3 CLEN = List.replicate i 1 := by
      rw [hw3frame CLEN (by decide), hw2frame CLEN (by decide), hw1frame CLEN (by decide)]
      exact hwCL
    clear_value w3
    -- consume element cells
    have eF : (Cmd.ifBit TFLG
        (Cmd.op (.tail SCANW SCANW) ;; Cmd.op (.tail SCANW SCANW))
        (Cmd.op (.tail SCANW SCANW))).eval w3 = w3.set SCANW T := by
      cases b with
      | true =>
          rw [Cmd.eval_ifBit_true _ _ _ _ (show State.get w3 TFLG = [1] from hw3T)]
          have hS1 : State.get w3 SCANW = 1 :: 0 :: T := by rw [hw3SCAN]; rfl
          have et1 : (Cmd.op (.tail SCANW SCANW)).eval w3 = w3.set SCANW (0 :: T) := by
            rw [Cmd.eval_op]; simp only [Op.eval, hS1, List.tail_cons]
          rw [Cmd.eval_seq, et1, Cmd.eval_op]
          simp only [Op.eval, State.get_set_eq, List.tail_cons, State.set_set]
      | false =>
          have hT0 : State.get w3 TFLG ≠ [1] := by rw [hw3T]; decide
          rw [Cmd.eval_ifBit_false _ _ _ _ hT0]
          have hS0 : State.get w3 SCANW = 0 :: T := by rw [hw3SCAN]; rfl
          rw [Cmd.eval_op]; simp only [Op.eval, hS0, List.tail_cons]
    set w4 := w3.set SCANW T with hw4
    have hw4frame : ∀ r : Var, r ≠ SCANW → State.get w4 r = State.get w3 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw4SCAN : State.get w4 SCANW = T := State.get_set_eq _ _ _
    have hw4CL : State.get w4 CLEN = List.replicate i 1 := by
      rw [hw4frame CLEN (by decide)]; exact hw3CL
    clear_value w4
    have eC : (Cmd.op (.appendOne CLEN)).eval w4 = w4.set CLEN (List.replicate (i + 1) 1) := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw4CL]; congr 1; rw [List.replicate_succ']
    set wF := w4.set CLEN (List.replicate (i + 1) 1) with hwF
    have hwFframe : ∀ r : Var, r ≠ CLEN → State.get wF r = State.get w4 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwFCL : State.get wF CLEN = List.replicate (i + 1) 1 := State.get_set_eq _ _ _
    have heval : cardLenElemBody.eval w = wF := by
      unfold cardLenElemBody
      rw [Cmd.eval_ifBit_false _ _ _ _ hDONEne, Cmd.eval_seq, e1,
        Cmd.eval_ifBit_true _ _ _ _ hw1E, Cmd.eval_seq, e2, Cmd.eval_seq, e3,
        Cmd.eval_seq, eF, eC]
    rw [heval]
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun hlt => absurd hlt (by omega), ?_⟩
    · rw [hwFframe DONE (by decide), hw4frame DONE (by decide), hw3frame DONE (by decide),
        hw2frame DONE (by decide), hw1frame DONE (by decide)]; exact hwD
    · rw [hwFframe SCANW (by decide)]; exact hw4SCAN
    · rw [hwFCL]
    · intro r h1 h2 h3 h4 h5 h6 h7
      rw [hwFframe r h2, hw4frame r h1, hw3frame r h5, hw2frame r h1, hw1frame r h4,
        hwframe r h6, hframe r h1 h2 h3 h4 h5 h6 h7]
  · -- terminator: consume bare `0`, set DONE
    subst hi
    obtain ⟨hDONE, hSCAN, hCL⟩ := hph1 (le_refl _)
    set w := st.set KBIT (List.replicate bs.length 1) with hw
    have hwframe : ∀ r : Var, r ≠ KBIT → State.get w r = State.get st r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwD : State.get w DONE = [] := by rw [hwframe DONE (by decide)]; exact hDONE
    have hwCL : State.get w CLEN = List.replicate bs.length 1 := by
      rw [hwframe CLEN (by decide)]; exact hCL
    have hSCANw : State.get w SCANW = 0 :: rest := by
      rw [hwframe SCANW (by decide), hSCAN, List.drop_eq_nil_of_le (le_refl bs.length)]; rfl
    clear_value w
    have hDONEne : State.get w DONE ≠ [1] := by rw [hwD]; decide
    have e1 : (Cmd.op (.head EMARK SCANW)).eval w = w.set EMARK [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hSCANw]
    set w1 := w.set EMARK [0] with hw1
    have hw1frame : ∀ r : Var, r ≠ EMARK → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1E : State.get w1 EMARK ≠ [1] := by rw [hw1, State.get_set_eq]; decide
    have hw1SCAN : State.get w1 SCANW = 0 :: rest := by rw [hw1frame SCANW (by decide)]; exact hSCANw
    clear_value w1
    have e2 : (Cmd.op (.tail SCANW SCANW)).eval w1 = w1.set SCANW rest := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw1SCAN, List.tail_cons]
    set w2 := w1.set SCANW rest with hw2
    have hw2frame : ∀ r : Var, r ≠ SCANW → State.get w2 r = State.get w1 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw2SCAN : State.get w2 SCANW = rest := State.get_set_eq _ _ _
    clear_value w2
    have e3 : (Cmd.op (.clear DONE)).eval w2 = w2.set DONE [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    set w3 := w2.set DONE [] with hw3
    have hw3frame : ∀ r : Var, r ≠ DONE → State.get w3 r = State.get w2 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw3D : State.get w3 DONE = [] := State.get_set_eq _ _ _
    clear_value w3
    have e4 : (Cmd.op (.appendOne DONE)).eval w3 = w3.set DONE [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw3D]; rfl
    set wF := w3.set DONE [1] with hwF
    have hwFframe : ∀ r : Var, r ≠ DONE → State.get wF r = State.get w3 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have heval : cardLenElemBody.eval w = wF := by
      unfold cardLenElemBody
      rw [Cmd.eval_ifBit_false _ _ _ _ hDONEne, Cmd.eval_seq, e1,
        Cmd.eval_ifBit_false _ _ _ _ hw1E, Cmd.eval_seq, e2, Cmd.eval_seq, e3, e4]
    rw [heval]
    refine ⟨fun hle => absurd hle (by omega), fun _ => ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hwF]; exact State.get_set_eq _ _ _
    · rw [hwFframe SCANW (by decide), hw3frame SCANW (by decide)]; exact hw2SCAN
    · rw [hwFframe CLEN (by decide), hw3frame CLEN (by decide), hw2frame CLEN (by decide),
        hw1frame CLEN (by decide)]; exact hwCL
    · intro r h1 h2 h3 h4 h5 h6 h7
      rw [hwFframe r h3, hw3frame r h3, hw2frame r h1, hw1frame r h4, hwframe r h6,
        hframe r h1 h2 h3 h4 h5 h6 h7]
  · -- idle: DONE set, clear ZERO
    obtain ⟨hDONE, hSCAN, hCL⟩ := hph2 hi
    set w := st.set KBIT (List.replicate i 1) with hw
    have hwframe : ∀ r : Var, r ≠ KBIT → State.get w r = State.get st r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hwD : State.get w DONE = [1] := by rw [hwframe DONE (by decide)]; exact hDONE
    clear_value w
    have heval : cardLenElemBody.eval w = w.set ZERO [] := by
      unfold cardLenElemBody
      rw [Cmd.eval_ifBit_true _ _ _ _ hwD, Cmd.eval_op]; simp only [Op.eval]
    rw [heval]
    refine ⟨fun hle => absurd hle (by omega), fun _ => ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [State.get_set_ne _ _ _ _ (show DONE ≠ ZERO by decide)]; exact hwD
    · rw [State.get_set_ne _ _ _ _ (show SCANW ≠ ZERO by decide), hwframe SCANW (by decide)]; exact hSCAN
    · rw [State.get_set_ne _ _ _ _ (show CLEN ≠ ZERO by decide), hwframe CLEN (by decide)]; exact hCL
    · intro r h1 h2 h3 h4 h5 h6 h7
      rw [State.get_set_ne _ _ _ _ h7, hwframe r h6, hframe r h1 h2 h3 h4 h5 h6 h7]

/-- `cardLenItem` parses one `FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs)` off `SCANW`, leaving `SCANW`
past the terminator, and ANDs `bs.length = width` into `GWF`. -/
theorem cardLenItem_run (bs : List Bool) (rest : List Nat) (width : Nat) (g : List Nat)
    (u : State)
    (hSC : State.get u SCANW = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs) ++ rest)
    (hW : State.get u WIDTH = List.replicate width 1)
    (hG : State.get u GWF = g) :
    State.get (cardLenItem.eval u) SCANW = rest
    ∧ State.get (cardLenItem.eval u) GWF
          = (if bs.length = width then g else [])
    ∧ (∀ r : Var, r ≠ SCANW → r ≠ CLEN → r ≠ DONE → r ≠ EMARK → r ≠ TFLG →
        r ≠ KBIT → r ≠ ZERO → r ≠ GWF →
        State.get (cardLenItem.eval u) r = State.get u r) := by
  have e01 : (Cmd.op (.clear CLEN)).eval u = u.set CLEN [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u1 := u.set CLEN [] with hu1
  have hu1frame : ∀ r : Var, r ≠ CLEN → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  clear_value u1
  have e02 : (Cmd.op (.clear DONE)).eval u1 = u1.set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u2 := u1.set DONE [] with hu2
  have hu2frame : ∀ r : Var, r ≠ DONE → State.get u2 r = State.get u1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu2SC : State.get u2 SCANW = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs) ++ rest := by
    rw [hu2frame SCANW (by decide), hu1frame SCANW (by decide)]; exact hSC
  have hu2CL : State.get u2 CLEN = [] := by
    rw [hu2frame CLEN (by decide), hu1]; exact State.get_set_eq _ _ _
  have hu2D : State.get u2 DONE = [] := State.get_set_eq _ _ _
  clear_value u2
  have hN : bs.length < (State.get u2 SCANW).length := by
    rw [hu2SC, List.length_append, FlatTCCFree.encSList_length,
      show (FlatCCBinFree.bitsNat bs).length = bs.length from List.length_map _]
    omega
  have hbase : CEInv bs rest u2 0 u2 := by
    refine ⟨fun _ => ⟨hu2D, by rw [List.drop_zero]; exact hu2SC, hu2CL⟩,
      fun hlt => absurd hlt (Nat.not_lt_zero _), fun r _ _ _ _ _ _ _ => rfl⟩
  have hInv : CEInv bs rest u2 (State.get u2 SCANW).length
      (Cmd.foldlState cardLenElemBody KBIT (List.range (State.get u2 SCANW).length) u2) :=
    Cmd.foldlState_range_induct _ KBIT _ u2 (CEInv bs rest u2) hbase
      (fun i st _ hM => CEInv_step bs rest u2 i st hM)
  obtain ⟨-, hph2, hLframe⟩ := hInv
  obtain ⟨-, hLSC, hLCL⟩ := hph2 hN
  set w2 := Cmd.foldlState cardLenElemBody KBIT (List.range (State.get u2 SCANW).length) u2 with hw2
  clear_value w2
  -- eqBit TFLG CLEN WIDTH
  have hw2W : State.get w2 WIDTH = List.replicate width 1 := by
    rw [hLframe WIDTH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hu2frame WIDTH (by decide), hu1frame WIDTH (by decide)]; exact hW
  have hw2G : State.get w2 GWF = g := by
    rw [hLframe GWF (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hu2frame GWF (by decide), hu1frame GWF (by decide)]; exact hG
  have e3 : (Cmd.op (.eqBit TFLG CLEN WIDTH)).eval w2
      = w2.set TFLG (if bs.length = width then [1] else [0]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hLCL, hw2W]
    by_cases hbw : bs.length = width
    · rw [hbw]; simp
    · rw [if_neg hbw, if_neg]
      intro heq
      exact hbw (by have := congrArg List.length heq; simpa using this)
  set w3 := w2.set TFLG (if bs.length = width then [1] else [0]) with hw3
  have hw3frame : ∀ r : Var, r ≠ TFLG → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3T : State.get w3 TFLG = (if bs.length = width then [1] else [0]) := State.get_set_eq _ _ _
  have hw3G : State.get w3 GWF = g := by rw [hw3frame GWF (by decide)]; exact hw2G
  have hw3SC : State.get w3 SCANW = rest := by rw [hw3frame SCANW (by decide)]; exact hLSC
  clear_value w3
  have heval : cardLenItem.eval u = (andFlag TFLG).eval w3 := by
    unfold cardLenItem
    rw [Cmd.eval_seq, e01, Cmd.eval_seq, e02, Cmd.eval_seq, Cmd.eval_forBnd, ← hw2,
      Cmd.eval_seq, e3]
  -- andFlag TFLG
  by_cases hbw : bs.length = width
  · have hTe : State.get w3 TFLG = [1] := by rw [hw3T, if_pos hbw]
    have e4 : (andFlag TFLG).eval w3 = w3.set ZERO [] := by
      unfold andFlag; rw [Cmd.eval_ifBit_true _ _ _ _ hTe, Cmd.eval_op]; simp only [Op.eval]
    refine ⟨?_, ?_, ?_⟩
    · rw [heval, e4, State.get_set_ne _ _ _ _ (show SCANW ≠ ZERO by decide)]; exact hw3SC
    · rw [heval, e4, State.get_set_ne _ _ _ _ (show GWF ≠ ZERO by decide), hw3G, if_pos hbw]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      rw [heval, e4, State.get_set_ne _ _ _ _ h7, hw3frame r h5,
        hLframe r h1 h2 h3 h4 h5 h6 h7, hu2frame r h3, hu1frame r h2]
  · have hTne : State.get w3 TFLG ≠ [1] := by rw [hw3T, if_neg hbw]; decide
    have e4 : (andFlag TFLG).eval w3 = w3.set GWF [] := by
      unfold andFlag; rw [Cmd.eval_ifBit_false _ _ _ _ hTne, Cmd.eval_op]; simp only [Op.eval]
    refine ⟨?_, ?_, ?_⟩
    · rw [heval, e4, State.get_set_ne _ _ _ _ (show SCANW ≠ GWF by decide)]; exact hw3SC
    · rw [heval, e4, State.get_set_eq, if_neg hbw]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      rw [heval, e4, State.get_set_ne _ _ _ _ h8, hw3frame r h5,
        hLframe r h1 h2 h3 h4 h5 h6 h7, hu2frame r h3, hu1frame r h2]

private def CLInv (C : BinaryCC) (width : Nat) (g0 : List Nat) (u : State) (j : Nat)
    (st : State) : Prop :=
  State.get st SCANW = FlatTCCFree.encCardsOut ((C.cards.drop j).map FlatCCBinFree.cardNat)
  ∧ State.get st GWF = (bif cardsOKB (C.cards.take j) width then g0 else [])
  ∧ State.get st WIDTH = List.replicate width 1
  ∧ (∀ r : Var, r ≠ SCANW → r ≠ CLEN → r ≠ DONE → r ≠ EMARK → r ≠ TFLG →
      r ≠ KBIT → r ≠ ZERO → r ≠ GWF → r ≠ KTMP → r ≠ KCARD →
      State.get st r = State.get u r)

private theorem CLInv_step (C : BinaryCC) (width : Nat) (g0 : List Nat) (u : State)
    (j : Nat) (st : State) (h : CLInv C width g0 u j st) :
    CLInv C width g0 u (j + 1) (cardLenCardBody.eval (st.set KCARD (List.replicate j 1))) := by
  obtain ⟨hSCAN, hGWF, hWID, hframe⟩ := h
  set w := st.set KCARD (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KCARD → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSCAN : State.get w SCANW = FlatTCCFree.encCardsOut ((C.cards.drop j).map FlatCCBinFree.cardNat) := by
    rw [hwframe SCANW (by decide)]; exact hSCAN
  have hwGWF : State.get w GWF = (bif cardsOKB (C.cards.take j) width then g0 else []) := by
    rw [hwframe GWF (by decide)]; exact hGWF
  have hwWID : State.get w WIDTH = List.replicate width 1 := by
    rw [hwframe WIDTH (by decide)]; exact hWID
  clear_value w
  by_cases hj : j < C.cards.length
  · -- live: parse prem then conc
    have hdrop : C.cards.drop j = C.cards[j] :: C.cards.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    have htake : C.cards.take (j + 1) = C.cards.take j ++ [C.cards[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    set c := C.cards[j] with hc
    clear_value c
    set REST := FlatTCCFree.encCardsOut ((C.cards.drop (j + 1)).map FlatCCBinFree.cardNat) with hREST
    have hwSCANc : State.get w SCANW
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem) ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hwSCAN, hdrop, encCardsOut_cons, hREST]
    have hne : (State.get w SCANW).isEmpty = false := by
      rw [hwSCANc]; exact encSList_append_isEmpty _ _
    have e1 : (Cmd.op (.nonEmpty TFLG SCANW)).eval w = w.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    set w1 := w.set TFLG [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ TFLG → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1T : State.get w1 TFLG = [1] := State.get_set_eq _ _ _
    have hw1SCAN : State.get w1 SCANW
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem) ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hw1frame SCANW (by decide)]; exact hwSCANc
    have hw1GWF : State.get w1 GWF = (bif cardsOKB (C.cards.take j) width then g0 else []) := by
      rw [hw1frame GWF (by decide)]; exact hwGWF
    have hw1WID : State.get w1 WIDTH = List.replicate width 1 := by
      rw [hw1frame WIDTH (by decide)]; exact hwWID
    clear_value w1
    -- first cardLenItem (prem)
    obtain ⟨hp1SC, hp1G, hp1F⟩ := cardLenItem_run c.prem (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST)
      width (bif cardsOKB (C.cards.take j) width then g0 else []) w1 hw1SCAN hw1WID hw1GWF
    set w2 := cardLenItem.eval w1 with hw2
    have hw2SC : State.get w2 SCANW = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST := hp1SC
    have hw2G : State.get w2 GWF
        = (if c.prem.length = width then (bif cardsOKB (C.cards.take j) width then g0 else []) else []) := hp1G
    have hw2F : ∀ r : Var, r ≠ SCANW → r ≠ CLEN → r ≠ DONE → r ≠ EMARK → r ≠ TFLG →
        r ≠ KBIT → r ≠ ZERO → r ≠ GWF → State.get w2 r = State.get w1 r := hp1F
    have hw2WID : State.get w2 WIDTH = List.replicate width 1 := by
      rw [hw2F WIDTH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hw1WID
    clear_value w2
    -- second cardLenItem (conc)
    obtain ⟨hp2SC, hp2G, hp2F⟩ := cardLenItem_run c.conc REST width
      (if c.prem.length = width then (bif cardsOKB (C.cards.take j) width then g0 else []) else [])
      w2 hw2SC hw2WID hw2G
    set w3 := cardLenItem.eval w2 with hw3
    have hw3SC : State.get w3 SCANW = REST := hp2SC
    have hw3G : State.get w3 GWF
        = (if c.conc.length = width then
            (if c.prem.length = width then (bif cardsOKB (C.cards.take j) width then g0 else []) else [])
            else []) := hp2G
    have hw3F : ∀ r : Var, r ≠ SCANW → r ≠ CLEN → r ≠ DONE → r ≠ EMARK → r ≠ TFLG →
        r ≠ KBIT → r ≠ ZERO → r ≠ GWF → State.get w3 r = State.get w2 r := hp2F
    clear_value w3
    have heval : cardLenCardBody.eval w = w3 := by
      unfold cardLenCardBody
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_true _ _ _ _ hw1T, Cmd.eval_seq, ← hw2, ← hw3]
    rw [heval]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hw3SC
    · rw [hw3G, htake, cardsOKB_snoc, cardLenOK]
      exact gwf_card_step _ _ _ _
    · rw [hw3F WIDTH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hw2WID
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rw [hw3F r h1 h2 h3 h4 h5 h6 h7 h8, hw2F r h1 h2 h3 h4 h5 h6 h7 h8,
        hw1frame r h5, hwframe r h10, hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]
  · -- idle: SCANW empty
    have hlen : C.cards.length ≤ j := Nat.le_of_not_lt hj
    have hwSCANe : State.get w SCANW = [] := by
      rw [hwSCAN, List.drop_eq_nil_of_le hlen]; rfl
    have hne : (State.get w SCANW).isEmpty = true := by rw [hwSCANe]; rfl
    have e1 : (Cmd.op (.nonEmpty TFLG SCANW)).eval w = w.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    set w1 := w.set TFLG [0] with hw1
    have hw1Tne : State.get w1 TFLG ≠ [1] := by rw [hw1, State.get_set_eq]; decide
    have e2 : (Cmd.op (.clear KTMP)).eval w1 = w1.set KTMP [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    have heval : cardLenCardBody.eval w = w1.set KTMP [] := by
      unfold cardLenCardBody
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_false _ _ _ _ hw1Tne, e2]
    have hgetF : ∀ r : Var, r ≠ TFLG → r ≠ KTMP → State.get (w1.set KTMP []) r = State.get w r := by
      intro r hh1 hh2
      rw [State.get_set_ne _ _ _ _ hh2, hw1, State.get_set_ne _ _ _ _ hh1]
    rw [heval]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hgetF SCANW (by decide) (by decide), hwSCAN, List.drop_eq_nil_of_le hlen,
        List.drop_eq_nil_of_le (by omega)]
    · rw [hgetF GWF (by decide) (by decide), hwGWF, List.take_of_length_le hlen,
        List.take_of_length_le (by omega)]
    · rw [hgetF WIDTH (by decide) (by decide)]; exact hwWID
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rw [hgetF r h5 h9, hwframe r h10, hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]

/-- `cardLenCheck` ANDs `∀ card, |prem|=|conc|=width` into `GWF`. -/
theorem cardLenCheck_run (C : BinaryCC) (width : Nat) (g0 : List Nat) (u : State)
    (hCARDS : State.get u CARDS = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hW : State.get u WIDTH = List.replicate width 1)
    (hG : State.get u GWF = g0) :
    State.get (cardLenCheck.eval u) GWF
        = (bif cardsOKB C.cards width then g0 else [])
    ∧ (∀ r : Var, r ≠ SCANW → r ≠ CLEN → r ≠ DONE → r ≠ EMARK → r ≠ TFLG →
        r ≠ KBIT → r ≠ ZERO → r ≠ GWF → r ≠ KTMP → r ≠ KCARD →
        State.get (cardLenCheck.eval u) r = State.get u r) := by
  have e0 : (Cmd.op (.copy SCANW CARDS)).eval u
      = u.set SCANW (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hCARDS]
  set u1 := u.set SCANW (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) with hu1
  have hu1frame : ∀ r : Var, r ≠ SCANW → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1SC : State.get u1 SCANW = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := State.get_set_eq _ _ _
  have hu1W : State.get u1 WIDTH = List.replicate width 1 := by
    rw [hu1frame WIDTH (by decide)]; exact hW
  have hu1G : State.get u1 GWF = g0 := by rw [hu1frame GWF (by decide)]; exact hG
  have hu1CARDS : State.get u1 CARDS = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [hu1frame CARDS (by decide)]; exact hCARDS
  clear_value u1
  have hN : C.cards.length ≤ (State.get u1 CARDS).length := by
    rw [hu1CARDS]; exact length_le_encCardsOut C.cards
  have hbase : CLInv C width g0 u1 0 u1 := by
    refine ⟨by rw [List.drop_zero]; exact hu1SC, ?_, hu1W, fun r _ _ _ _ _ _ _ _ _ _ => rfl⟩
    rw [List.take_zero]; rw [hu1G]; rfl
  have hInv : CLInv C width g0 u1 (State.get u1 CARDS).length
      (Cmd.foldlState cardLenCardBody KCARD (List.range (State.get u1 CARDS).length) u1) :=
    Cmd.foldlState_range_induct _ KCARD _ u1 (CLInv C width g0 u1) hbase
      (fun j st _ hM => CLInv_step C width g0 u1 j st hM)
  obtain ⟨-, hGf, -, hframef⟩ := hInv
  rw [List.take_of_length_le hN] at hGf
  have heval : cardLenCheck.eval u
      = Cmd.foldlState cardLenCardBody KCARD (List.range (State.get u1 CARDS).length) u1 := by
    unfold cardLenCheck
    rw [Cmd.eval_seq, e0, Cmd.eval_forBnd]
  refine ⟨?_, ?_⟩
  · rw [heval]; exact hGf
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    rw [heval, hframef r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, hu1frame r h1]



/-! ### `computeWF_run` — the guard reproduces `BinaryCC_wellformed`. -/

/-- `andFlag TFLG` ANDs the boolean `TFLG = [1]` (reflecting `P`) into `GWF`. -/
theorem andFlag_run (P : Prop) [Decidable P] (g : List Nat) (s : State)
    (hT : State.get s TFLG = [1] ↔ P) (hG : State.get s GWF = g)
    (hZin : State.get s ZERO = []) :
    State.get ((andFlag TFLG).eval s) GWF = (if P then g else [])
    ∧ State.get ((andFlag TFLG).eval s) ZERO = []
    ∧ (∀ r : Var, r ≠ ZERO → r ≠ GWF → State.get ((andFlag TFLG).eval s) r = State.get s r) := by
  unfold andFlag
  by_cases hp : P
  · have hTe : State.get s TFLG = [1] := hT.mpr hp
    rw [Cmd.eval_ifBit_true _ _ _ _ hTe]
    refine ⟨?_, ?_, ?_⟩
    · rw [Cmd.eval_op]; simp only [Op.eval,
        State.get_set_ne _ _ _ _ (show GWF ≠ ZERO by decide), hG, if_pos hp]
    · rw [Cmd.eval_op]; simp only [Op.eval]; exact State.get_set_eq _ _ _
    · intro r h1 h2; rw [Cmd.eval_op]; simp only [Op.eval]; exact State.get_set_ne _ _ _ _ h1
  · have hTne : State.get s TFLG ≠ [1] := fun h => hp (hT.mp h)
    rw [Cmd.eval_ifBit_false _ _ _ _ hTne]
    refine ⟨?_, ?_, ?_⟩
    · rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, if_neg hp]
    · rw [Cmd.eval_op]; simp only [Op.eval,
        State.get_set_ne _ _ _ _ (show ZERO ≠ GWF by decide)]; exact hZin
    · intro r h1 h2; rw [Cmd.eval_op]; simp only [Op.eval]; exact State.get_set_ne _ _ _ _ h2

/-- `nonEmpty TFLG R` sets `TFLG = [1]` iff `R` is non-empty. -/
theorem nonEmptyTFLG_run (R : Var) (k : Nat) (s : State)
    (hR : State.get s R = List.replicate k 1) :
    (State.get ((Cmd.op (.nonEmpty TFLG R)).eval s) TFLG = [1] ↔ 0 < k)
    ∧ (∀ r : Var, r ≠ TFLG → State.get ((Cmd.op (.nonEmpty TFLG R)).eval s) r = State.get s r) := by
  have hev : (Cmd.op (.nonEmpty TFLG R)).eval s
      = s.set TFLG (if (List.replicate k 1 : List Nat).isEmpty then [0] else [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hR]
  refine ⟨?_, ?_⟩
  · rw [hev, State.get_set_eq]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      subst hm; simp [List.replicate_succ]
  · intro r hr; rw [hev]; exact State.get_set_ne _ _ _ _ hr

theorem cardsOKB_iff (cs : List (CCCard Bool)) (w : Nat) :
    cardsOKB cs w = true ↔ ∀ c ∈ cs, c.prem.length = w ∧ c.conc.length = w := by
  unfold cardsOKB
  rw [List.all_eq_true]
  constructor
  · intro h c hc
    have := h c hc; unfold cardLenOK at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this
  · intro h c hc
    have := h c hc; unfold cardLenOK
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact this

/-- The on-machine conjunction equals `BinaryCC_wellformed`. -/
theorem wf_iff (C : BinaryCC) :
    (0 < C.width ∧ 0 < C.offset ∧ C.width ≤ C.init.length ∧ C.offset ∣ C.width
      ∧ C.offset ∣ C.init.length ∧ cardsOKB C.cards C.width = true)
      ↔ BinaryCC_wellformed C := by
  unfold BinaryCC_wellformed
  rw [cardsOKB_iff]
  constructor
  · rintro ⟨hw, ho, hle, hdw, hdl, hc⟩
    obtain ⟨k, hk⟩ := hdw
    obtain ⟨m, hm⟩ := hdl
    refine ⟨hw, ho, ⟨k, ?_, ?_⟩, hle, hc, ⟨m, ?_⟩⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at hk; omega
      · exact h
    · rw [hk]; ring
    · rw [hm]; ring
  · rintro ⟨hw, ho, ⟨k, _, hkw⟩, hle, hc, ⟨m, hm⟩⟩
    exact ⟨hw, ho, hle, ⟨k, by rw [hkw]; ring⟩, ⟨m, by rw [hm]; ring⟩, hc⟩

/-- **`computeWF` reproduces the wellformedness predicate on-machine.** -/
theorem computeWF_run (C : BinaryCC) (u : State)
    [Decidable (BinaryCC_wellformed C)]
    (hW : State.get u WIDTH = List.replicate C.width 1)
    (hO : State.get u OFFSET = List.replicate C.offset 1)
    (hL : State.get u LREG = List.replicate C.init.length 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = []) :
    State.get (computeWF.eval u) GWF = (if BinaryCC_wellformed C then [1] else [])
    ∧ (∀ r : Var, r ≠ GWF → r ≠ TFLG → r ≠ ZERO → r ≠ MREM → r ≠ MCHK → r ≠ MGE →
        r ≠ KTMP → r ≠ KTMP2 → r ≠ SCANW → r ≠ CLEN → r ≠ DONE → r ≠ EMARK →
        r ≠ KBIT → r ≠ KCARD →
        State.get (computeWF.eval u) r = State.get u r) := by
  unfold computeWF
  -- t0 : clear GWF
  rw [Cmd.eval_seq]
  set t0 := (Cmd.op (.clear GWF)).eval u with ht0
  have ht0f : ∀ r : Var, r ≠ GWF → State.get t0 r = State.get u r :=
    fun r hr => by rw [ht0, Cmd.eval_op]; simp only [Op.eval]; exact State.get_set_ne _ _ _ _ hr
  have ht0Gnil : State.get t0 GWF = [] := by
    rw [ht0, Cmd.eval_op]; simp only [Op.eval]; exact State.get_set_eq _ _ _
  clear_value t0
  -- t1 : appendOne GWF
  rw [Cmd.eval_seq]
  set t1 := (Cmd.op (.appendOne GWF)).eval t0 with ht1
  have ht1G : State.get t1 GWF = [1] := by
    rw [ht1, Cmd.eval_op]; simp only [Op.eval, ht0Gnil, List.nil_append, State.get_set_eq]
  have ht1f : ∀ r : Var, r ≠ GWF → State.get t1 r = State.get u r := by
    intro r hr; rw [ht1, Cmd.eval_op]; simp only [Op.eval, State.get_set_ne _ _ _ _ hr]
    exact ht0f r hr
  have ht1W := (ht1f WIDTH (by decide)).trans hW
  have ht1O := (ht1f OFFSET (by decide)).trans hO
  have ht1L := (ht1f LREG (by decide)).trans hL
  have ht1C := (ht1f CARDS (by decide)).trans hCARDS
  have ht1Z := (ht1f ZERO (by decide)).trans hZ
  clear_value t1
  -- P1 : nonEmpty TFLG WIDTH ;; andFlag TFLG   (0 < width)
  rw [Cmd.eval_seq]
  obtain ⟨hne1, hnf1⟩ := nonEmptyTFLG_run WIDTH C.width t1 ht1W
  set t2 := (Cmd.op (.nonEmpty TFLG WIDTH)).eval t1 with ht2
  have ht2G := (hnf1 GWF (by decide)).trans ht1G
  have ht2W := (hnf1 WIDTH (by decide)).trans ht1W
  have ht2O := (hnf1 OFFSET (by decide)).trans ht1O
  have ht2L := (hnf1 LREG (by decide)).trans ht1L
  have ht2C := (hnf1 CARDS (by decide)).trans ht1C
  have ht2Z := (hnf1 ZERO (by decide)).trans ht1Z
  clear_value t2
  rw [Cmd.eval_seq]
  obtain ⟨haf1G, haf1Z, haf1F⟩ := andFlag_run (0 < C.width) [1] t2 hne1 ht2G ht2Z
  set t3 := (andFlag TFLG).eval t2 with ht3
  have ht3W := (haf1F WIDTH (by decide) (by decide)).trans ht2W
  have ht3O := (haf1F OFFSET (by decide) (by decide)).trans ht2O
  have ht3L := (haf1F LREG (by decide) (by decide)).trans ht2L
  have ht3C := (haf1F CARDS (by decide) (by decide)).trans ht2C
  clear_value t3
  -- P2 : nonEmpty TFLG OFFSET ;; andFlag TFLG   (0 < offset)
  rw [Cmd.eval_seq]
  obtain ⟨hne2, hnf2⟩ := nonEmptyTFLG_run OFFSET C.offset t3 ht3O
  set t4 := (Cmd.op (.nonEmpty TFLG OFFSET)).eval t3 with ht4
  have ht4G := (hnf2 GWF (by decide)).trans haf1G
  have ht4W := (hnf2 WIDTH (by decide)).trans ht3W
  have ht4O := (hnf2 OFFSET (by decide)).trans ht3O
  have ht4L := (hnf2 LREG (by decide)).trans ht3L
  have ht4C := (hnf2 CARDS (by decide)).trans ht3C
  have ht4Z := (hnf2 ZERO (by decide)).trans haf1Z
  clear_value t4
  rw [Cmd.eval_seq]
  obtain ⟨haf2G, haf2Z, haf2F⟩ := andFlag_run (0 < C.offset) _ t4 hne2 ht4G ht4Z
  set t5 := (andFlag TFLG).eval t4 with ht5
  have ht5W := (haf2F WIDTH (by decide) (by decide)).trans ht4W
  have ht5O := (haf2F OFFSET (by decide) (by decide)).trans ht4O
  have ht5L := (haf2F LREG (by decide) (by decide)).trans ht4L
  have ht5C := (haf2F CARDS (by decide) (by decide)).trans ht4C
  clear_value t5
  -- P3 : leCheck WIDTH LREG ;; andFlag TFLG   (width ≤ L)
  rw [Cmd.eval_seq]
  obtain ⟨hle3T, hle3F⟩ := leCheck_run WIDTH LREG C.width C.init.length t5 (by decide)
    ht5W (by rw [ht5L]; simp)
  set t6 := (leCheck WIDTH LREG).eval t5 with ht6
  have ht6Tiff : State.get t6 TFLG = [1] ↔ C.width ≤ C.init.length := by
    rw [hle3T]; by_cases h : C.width ≤ C.init.length <;> simp [h]
  have ht6G := (hle3F GWF (by decide) (by decide) (by decide)).trans haf2G
  have ht6W := (hle3F WIDTH (by decide) (by decide) (by decide)).trans ht5W
  have ht6O := (hle3F OFFSET (by decide) (by decide) (by decide)).trans ht5O
  have ht6L := (hle3F LREG (by decide) (by decide) (by decide)).trans ht5L
  have ht6C := (hle3F CARDS (by decide) (by decide) (by decide)).trans ht5C
  have ht6Z := (hle3F ZERO (by decide) (by decide) (by decide)).trans haf2Z
  clear_value t6
  rw [Cmd.eval_seq]
  obtain ⟨haf3G, haf3Z, haf3F⟩ := andFlag_run (C.width ≤ C.init.length) _ t6 ht6Tiff ht6G ht6Z
  set t7 := (andFlag TFLG).eval t6 with ht7
  have ht7W := (haf3F WIDTH (by decide) (by decide)).trans ht6W
  have ht7O := (haf3F OFFSET (by decide) (by decide)).trans ht6O
  have ht7L := (haf3F LREG (by decide) (by decide)).trans ht6L
  have ht7C := (haf3F CARDS (by decide) (by decide)).trans ht6C
  clear_value t7
  -- P4 : dvdCheck WIDTH OFFSET ;; andFlag TFLG   (offset ∣ width)
  rw [Cmd.eval_seq]
  obtain ⟨hdv4T, hdv4Z, hdv4F⟩ := dvdCheck_run WIDTH OFFSET C.width C.offset t7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ht7W ht7O haf3Z
  set t8 := (dvdCheck WIDTH OFFSET).eval t7 with ht8
  have ht8Tiff : State.get t8 TFLG = [1] ↔ C.offset ∣ C.width := by
    rw [hdv4T]; by_cases h : C.offset ∣ C.width <;> simp [h]
  have ht8G := (hdv4F GWF (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans haf3G
  have ht8W := (hdv4F WIDTH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht7W
  have ht8O := (hdv4F OFFSET (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht7O
  have ht8L := (hdv4F LREG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht7L
  have ht8C := (hdv4F CARDS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht7C
  clear_value t8
  rw [Cmd.eval_seq]
  obtain ⟨haf4G, haf4Z, haf4F⟩ := andFlag_run (C.offset ∣ C.width) _ t8 ht8Tiff ht8G hdv4Z
  set t9 := (andFlag TFLG).eval t8 with ht9
  have ht9W := (haf4F WIDTH (by decide) (by decide)).trans ht8W
  have ht9O := (haf4F OFFSET (by decide) (by decide)).trans ht8O
  have ht9L := (haf4F LREG (by decide) (by decide)).trans ht8L
  have ht9C := (haf4F CARDS (by decide) (by decide)).trans ht8C
  clear_value t9
  -- P5 : dvdCheck LREG OFFSET ;; andFlag TFLG   (offset ∣ L)
  rw [Cmd.eval_seq]
  obtain ⟨hdv5T, hdv5Z, hdv5F⟩ := dvdCheck_run LREG OFFSET C.init.length C.offset t9
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ht9L ht9O haf4Z
  set t10 := (dvdCheck LREG OFFSET).eval t9 with ht10
  have ht10Tiff : State.get t10 TFLG = [1] ↔ C.offset ∣ C.init.length := by
    rw [hdv5T]; by_cases h : C.offset ∣ C.init.length <;> simp [h]
  have ht10G := (hdv5F GWF (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans haf4G
  have ht10W := (hdv5F WIDTH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht9W
  have ht10C := (hdv5F CARDS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht9C
  clear_value t10
  rw [Cmd.eval_seq]
  obtain ⟨haf5G, haf5Z, haf5F⟩ := andFlag_run (C.offset ∣ C.init.length) _ t10 ht10Tiff ht10G hdv5Z
  set t11 := (andFlag TFLG).eval t10 with ht11
  have ht11W := (haf5F WIDTH (by decide) (by decide)).trans ht10W
  have ht11C := (haf5F CARDS (by decide) (by decide)).trans ht10C
  clear_value t11
  -- P6 : cardLenCheck   (all cards ok)
  obtain ⟨hclG, hclF⟩ := cardLenCheck_run C C.width
    (if C.offset ∣ C.init.length then (if C.offset ∣ C.width then
      (if C.width ≤ C.init.length then (if 0 < C.offset then (if 0 < C.width then ([1] : List Nat) else []) else []) else []) else []) else [])
    t11 ht11C ht11W haf5G
  refine ⟨?_, ?_⟩
  · rw [hclG]
    -- collapse the nested guards and match wellformedness
    rw [show (bif cardsOKB C.cards C.width then
        (if C.offset ∣ C.init.length then (if C.offset ∣ C.width then
          (if C.width ≤ C.init.length then (if 0 < C.offset then (if 0 < C.width then ([1] : List Nat) else []) else []) else []) else []) else []) else [])
        = (if (0 < C.width ∧ 0 < C.offset ∧ C.width ≤ C.init.length ∧ C.offset ∣ C.width
            ∧ C.offset ∣ C.init.length ∧ cardsOKB C.cards C.width = true) then [1] else [])
        from by
          by_cases h1 : 0 < C.width <;> by_cases h2 : 0 < C.offset <;>
          by_cases h3 : C.width ≤ C.init.length <;> by_cases h4 : C.offset ∣ C.width <;>
          by_cases h5 : C.offset ∣ C.init.length <;> cases hb : cardsOKB C.cards C.width <;>
          simp [h1, h2, h3, h4, h5]]
    exact if_congr (wf_iff C) rfl rfl
  · -- the frame: walk the 13-component chain back to `u`
    intro r hG hT hZr hMR hMC hMG hK1 hK2 hSW hCL hDN hEM hKB hKC
    rw [hclF r hSW hCL hDN hEM hT hKB hZr hG hK1 hKC,
      haf5F r hZr hG, hdv5F r hMR hMC hMG hK1 hK2 hZr hT,
      haf4F r hZr hG, hdv4F r hMR hMC hMG hK1 hK2 hZr hT,
      haf3F r hZr hG, hle3F r hMR hMG hT,
      haf2F r hZr hG, hnf2 r hT,
      haf1F r hZr hG, hnf1 r hT,
      ht1f r hG]

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

/-! ## 3. `buildFSAT_run` — the assembly (session 3, the last big run lemma)

`precompLen_run` (the length precomputation), then the whole program:
`computeWF_run` decides the branch, the emitters (each black-boxed by its own
`_run` lemma) produce `serF (encodeTableau C)` piecewise on the guard-pass
branch, `emitFalse` produces `serF falseFml` on the guard-fail branch, and the
final `copy` lands it in `FOUT`. -/

/-- **`precompLen` is correct**: with `INIT` holding a bit string, it computes
`LREG := 1^L` and `LREG1 := 1^(L+1)` (`L` the string length), touching only
`LREG`/`LREG1`/scratch `KTMP`. -/
theorem precompLen_run (bs : List Bool) (u : State)
    (hINIT : State.get u INIT = FlatCCBinFree.bitsNat bs) :
    State.get (precompLen.eval u) LREG = List.replicate bs.length 1
    ∧ State.get (precompLen.eval u) LREG1 = List.replicate (bs.length + 1) 1
    ∧ (∀ r : Var, r ≠ LREG → r ≠ LREG1 → r ≠ KTMP →
        State.get (precompLen.eval u) r = State.get u r) := by
  -- w1 : clear LREG
  have e1 : (Cmd.op (.clear LREG)).eval u = u.set LREG [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w1 := u.set LREG [] with hw1
  have hw1f : ∀ r : Var, r ≠ LREG → State.get w1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1L : State.get w1 LREG = [] := State.get_set_eq _ _ _
  have hw1I : (State.get w1 INIT).length = bs.length := by
    rw [hw1f INIT (by decide), hINIT]
    exact List.length_map _
  clear_value w1
  -- w2 : the unary-length loop  LREG := 1^L
  have hInv := Cmd.foldlState_range_induct (Cmd.op (.appendOne LREG)) KTMP bs.length w1
    (fun i st => State.get st LREG = List.replicate i 1
      ∧ ∀ r : Var, r ≠ LREG → r ≠ KTMP → State.get st r = State.get w1 r)
    ⟨by rw [hw1L, List.replicate_zero], fun r _ _ => rfl⟩
    (fun i st _ hM => by
      obtain ⟨hL, hF⟩ := hM
      have hL' : State.get (st.set KTMP (List.replicate i 1)) LREG
          = List.replicate i 1 := by
        rw [State.get_set_ne _ _ _ _ (by decide : LREG ≠ KTMP)]
        exact hL
      refine ⟨?_, ?_⟩
      · rw [Cmd.eval_op]
        simp only [Op.eval, hL', State.get_set_eq]
        show List.replicate i 1 ++ List.replicate 1 1 = _
        rw [← List.replicate_add]
      · intro r hr hk
        rw [Cmd.eval_op]
        simp only [Op.eval]
        rw [State.get_set_ne _ _ _ _ hr, State.get_set_ne _ _ _ _ hk]
        exact hF r hr hk)
  obtain ⟨h2L, h2F⟩ := hInv
  have heval0 : (Cmd.forBnd KTMP INIT (Cmd.op (.appendOne LREG))).eval w1
      = Cmd.foldlState (Cmd.op (.appendOne LREG)) KTMP (List.range bs.length) w1 := by
    rw [Cmd.eval_forBnd, hw1I]
  set w2 := Cmd.foldlState (Cmd.op (.appendOne LREG)) KTMP (List.range bs.length) w1 with hw2
  clear_value w2
  -- w3 : copy LREG1 LREG
  have e3 : (Cmd.op (.copy LREG1 LREG)).eval w2
      = w2.set LREG1 (List.replicate bs.length 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, h2L]
  set w3 := w2.set LREG1 (List.replicate bs.length 1) with hw3
  have hw3f : ∀ r : Var, r ≠ LREG1 → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3L1 : State.get w3 LREG1 = List.replicate bs.length 1 := State.get_set_eq _ _ _
  clear_value w3
  -- w4 : appendOne LREG1
  have e4 : (Cmd.op (.appendOne LREG1)).eval w3
      = w3.set LREG1 (List.replicate (bs.length + 1) 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw3L1]
    rw [show (List.replicate bs.length 1 ++ [1] : List Nat)
        = List.replicate (bs.length + 1) 1 from by
      show List.replicate bs.length 1 ++ List.replicate 1 1 = _
      rw [← List.replicate_add]]
  have heval : precompLen.eval u = (Cmd.op (.appendOne LREG1)).eval w3 := by
    unfold precompLen
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, heval0, Cmd.eval_seq, e3]
  refine ⟨?_, ?_, ?_⟩
  · rw [heval, e4, State.get_set_ne _ _ _ _ (by decide : LREG ≠ LREG1),
      hw3f LREG (by decide)]
    exact h2L
  · rw [heval, e4]
    exact State.get_set_eq _ _ _
  · intro r h1 h2 h3
    rw [heval, e4, State.get_set_ne _ _ _ _ h2, hw3f r h2, h2F r h1 h3, hw1f r h1]

/-- **`buildFSAT` is correct**: on the pinned input frame `encodeIn C` it
writes exactly the serialized reduction image `serF (BinaryCC_to_FSAT_instance
C)` into `FOUT` — the `computes` crux of the `BinaryCC ⪯p' FSAT` witness
(compose with `decodeOut_of_serF`). -/
theorem buildFSAT_run (C : BinaryCC) :
    State.get (buildFSAT.eval (encodeIn C)) FOUT
      = serF (BinaryCC_to_FSAT_instance C) := by
  classical
  -- the pinned input frame (`encodeIn C`), field by field (all definitional)
  have h0STEPS : State.get (encodeIn C) STEPS = List.replicate C.steps 1 := rfl
  have h0OFF : State.get (encodeIn C) OFFSET = List.replicate C.offset 1 := rfl
  have h0WID : State.get (encodeIn C) WIDTH = List.replicate C.width 1 := rfl
  have h0INIT : State.get (encodeIn C) INIT = FlatCCBinFree.bitsNat C.init := rfl
  have h0CARDS : State.get (encodeIn C) CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := rfl
  have h0FINAL : State.get (encodeIn C) FINAL
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := rfl
  have h0ZERO : State.get (encodeIn C) ZERO = [] := rfl
  -- u1 : precompLen (LREG := 1^L, LREG1 := 1^(L+1))
  obtain ⟨hpL, hpL1, hpF⟩ := precompLen_run C.init (encodeIn C) h0INIT
  set u1 := precompLen.eval (encodeIn C) with hu1
  have h1STEPS := (hpF STEPS (by decide) (by decide) (by decide)).trans h0STEPS
  have h1OFF := (hpF OFFSET (by decide) (by decide) (by decide)).trans h0OFF
  have h1WID := (hpF WIDTH (by decide) (by decide) (by decide)).trans h0WID
  have h1INIT := (hpF INIT (by decide) (by decide) (by decide)).trans h0INIT
  have h1CARDS := (hpF CARDS (by decide) (by decide) (by decide)).trans h0CARDS
  have h1FINAL := (hpF FINAL (by decide) (by decide) (by decide)).trans h0FINAL
  have h1ZERO := (hpF ZERO (by decide) (by decide) (by decide)).trans h0ZERO
  clear_value u1
  -- u2 : computeWF (GWF := the wellformedness flag)
  obtain ⟨hwG, hwF⟩ := computeWF_run C u1 h1WID h1OFF hpL h1CARDS h1ZERO
  set u2 := computeWF.eval u1 with hu2
  have h2STEPS := (hwF STEPS (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1STEPS
  have h2OFF := (hwF OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1OFF
  have h2WID := (hwF WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1WID
  have h2INIT := (hwF INIT (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1INIT
  have h2CARDS := (hwF CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1CARDS
  have h2FINAL := (hwF FINAL (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1FINAL
  have h2LREG := (hwF LREG (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hpL
  have h2LREG1 := (hwF LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hpL1
  clear_value u2
  -- u3 : clear OUT
  have e3 : (Cmd.op (.clear OUT)).eval u2 = u2.set OUT [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u3 := u2.set OUT [] with hu3
  have h3f : ∀ r : Var, r ≠ OUT → State.get u3 r = State.get u2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have h3OUT : State.get u3 OUT = [] := State.get_set_eq _ _ _
  have h3GWF : State.get u3 GWF = (if BinaryCC_wellformed C then [1] else []) :=
    (h3f GWF (by decide)).trans hwG
  have h3STEPS := (h3f STEPS (by decide)).trans h2STEPS
  have h3OFF := (h3f OFFSET (by decide)).trans h2OFF
  have h3WID := (h3f WIDTH (by decide)).trans h2WID
  have h3INIT := (h3f INIT (by decide)).trans h2INIT
  have h3CARDS := (h3f CARDS (by decide)).trans h2CARDS
  have h3FINAL := (h3f FINAL (by decide)).trans h2FINAL
  have h3LREG := (h3f LREG (by decide)).trans h2LREG
  have h3LREG1 := (h3f LREG1 (by decide)).trans h2LREG1
  clear_value u3
  -- peel the program down to the branch on `GWF`
  have hevalPre : buildFSAT.eval (encodeIn C)
      = (Cmd.op (.copy FOUT OUT)).eval
          ((Cmd.ifBit GWF
            ( emitFandTag ;;
              Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
              emitBitsFromScan ZERO INIT ;;
              emitFandTag ;;
              emitAllSteps ;;
              emitFinal )
            emitFalse).eval u3) := by
    unfold buildFSAT
    rw [Cmd.eval_seq, ← hu1, Cmd.eval_seq, ← hu2, Cmd.eval_seq, e3, Cmd.eval_seq]
  rw [hevalPre, Cmd.eval_op]
  simp only [Op.eval]
  rw [State.get_set_eq]
  by_cases hWf : BinaryCC_wellformed C
  · -- wellformed: the emitter branch produces `serF (encodeTableau C)`
    have hGeq : State.get u3 GWF = [1] := by rw [h3GWF, if_pos hWf]
    rw [Cmd.eval_ifBit_true _ _ _ _ hGeq]
    -- v1 : emitFandTag (the outer `fand` tag)
    have e_v1 : emitFandTag.eval u3 = u3.set OUT [0, 1] := by
      rw [emitFandTag_run, h3OUT, List.nil_append]
    set v1 := u3.set OUT [0, 1] with hv1
    have hv1f : ∀ r : Var, r ≠ OUT → State.get v1 r = State.get u3 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv1OUT : State.get v1 OUT = [0, 1] := State.get_set_eq _ _ _
    clear_value v1
    -- v2 : clear ZERO
    have e_v2 : (Cmd.op (.clear ZERO)).eval v1 = v1.set ZERO [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    set v2 := v1.set ZERO [] with hv2
    have hv2f : ∀ r : Var, r ≠ ZERO → State.get v2 r = State.get v1 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv2ZERO : State.get v2 ZERO = [] := State.get_set_eq _ _ _
    clear_value v2
    -- v3 : copy SCAN INIT
    have h2INITv : State.get v2 INIT = FlatCCBinFree.bitsNat C.init := by
      rw [hv2f INIT (by decide), hv1f INIT (by decide)]; exact h3INIT
    have e_v3 : (Cmd.op (.copy SCAN INIT)).eval v2
        = v2.set SCAN (FlatCCBinFree.bitsNat C.init) := by
      rw [Cmd.eval_op]; simp only [Op.eval, h2INITv]
    set v3 := v2.set SCAN (FlatCCBinFree.bitsNat C.init) with hv3
    have hv3f : ∀ r : Var, r ≠ SCAN → State.get v3 r = State.get v2 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv3SCAN : State.get v3 SCAN = FlatCCBinFree.bitsNat C.init :=
      State.get_set_eq _ _ _
    clear_value v3
    -- v4 : emitBitsFromScan ZERO INIT (the `encodeBitsAt 0 init` block)
    have h3ZEROv : State.get v3 ZERO = List.replicate 0 1 := by
      rw [hv3f ZERO (by decide)]; exact hv2ZERO
    have h3INITlen : (State.get v3 INIT).length = C.init.length := by
      rw [hv3f INIT (by decide), h2INITv]
      exact List.length_map _
    obtain ⟨h4SCAN, h4OUT, h4F⟩ := emitBitsFromScan_run ZERO INIT 0 C.init v3
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h3ZEROv h3INITlen hv3SCAN
    set v4 := (emitBitsFromScan ZERO INIT).eval v3 with hv4
    have h4OUTval : State.get v4 OUT = [0, 1] ++ serF (encodeBitsAt 0 C.init) := by
      rw [h4OUT, hv3f OUT (by decide), hv2f OUT (by decide), hv1OUT]
    clear_value v4
    -- v5 : emitFandTag (the inner `fand` tag)
    have e_v5 : emitFandTag.eval v4
        = v4.set OUT (([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1]) := by
      rw [emitFandTag_run, h4OUTval]
    set v5 := v4.set OUT (([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1]) with hv5
    have hv5f : ∀ r : Var, r ≠ OUT → State.get v5 r = State.get v4 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv5OUT : State.get v5 OUT
        = ([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1] := State.get_set_eq _ _ _
    clear_value v5
    -- register threading u3 → v5 (v1/v2/v3/v4/v5 touch OUT/ZERO/SCAN + emitter scratch)
    have hv5chain : ∀ r : Var, r ≠ OUT → r ≠ ZERO → r ≠ SCAN → r ≠ WREG → r ≠ TFLG →
        r ≠ KBIT → State.get v5 r = State.get u3 r := by
      intro r h1 h2 h3 h4 h5 h6
      rw [hv5f r h1, h4F r h3 h1 h4 h5 h6, hv3f r h3, hv2f r h2, hv1f r h1]
    have h5STEPS := (hv5chain STEPS (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3STEPS
    have h5OFF := (hv5chain OFFSET (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3OFF
    have h5WID := (hv5chain WIDTH (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3WID
    have h5CARDS := (hv5chain CARDS (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3CARDS
    have h5FINAL := (hv5chain FINAL (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3FINAL
    have h5LREG := (hv5chain LREG (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3LREG
    have h5LREG1 := (hv5chain LREG1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3LREG1
    have h5ZERO : State.get v5 ZERO = [] := by
      rw [hv5f ZERO (by decide), h4F ZERO (by decide) (by decide) (by decide) (by decide)
        (by decide), hv3f ZERO (by decide)]
      exact hv2ZERO
    -- v6 : emitAllSteps (the step-constraint block)
    obtain ⟨h6OUT, h6ZERO, h6F⟩ := emitAllSteps_run C v5
      h5STEPS h5OFF h5WID h5LREG h5LREG1 h5CARDS h5ZERO
    set v6 := emitAllSteps.eval v5 with hv6
    have h6STEPS := (h6F STEPS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5STEPS
    have h6OFF := (h6F OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5OFF
    have h6LREG := (h6F LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5LREG
    have h6LREG1 := (h6F LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5LREG1
    have h6FINAL := (h6F FINAL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5FINAL
    clear_value v6
    -- v7 : emitFinal (the final-constraint block)
    obtain ⟨h7OUT, h7ZERO, h7F⟩ := emitFinal_run C v6
      h6STEPS h6OFF h6LREG h6LREG1 h6FINAL h6ZERO
    -- assemble the branch and the output
    rw [show (emitFandTag ;;
        Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
        emitBitsFromScan ZERO INIT ;;
        emitFandTag ;;
        emitAllSteps ;;
        emitFinal).eval u3 = emitFinal.eval v6 from by
      rw [Cmd.eval_seq, e_v1, Cmd.eval_seq, e_v2, Cmd.eval_seq, e_v3, Cmd.eval_seq,
        ← hv4, Cmd.eval_seq, e_v5, Cmd.eval_seq, ← hv6]]
    rw [h7OUT, h6OUT, hv5OUT]
    unfold BinaryCC_to_FSAT_instance
    rw [dif_pos hWf]
    show _ = serF (.fand (encodeBitsAt 0 C.init)
      (.fand (encodeAllStepConstraints C) (encodeFinalConstraint C)))
    simp only [serF, List.append_assoc, List.cons_append, List.nil_append]
  · -- not wellformed: the `emitFalse` branch produces `serF falseFml`
    have hGne : State.get u3 GWF ≠ [1] := by
      rw [h3GWF, if_neg hWf]; decide
    rw [Cmd.eval_ifBit_false _ _ _ _ hGne, emitFalse_run, State.get_set_eq, h3OUT]
    unfold BinaryCC_to_FSAT_instance
    rw [dif_neg hWf]
    rfl

/-! ## DESIGN COMPLETE — NEXT-SESSION PLAN (top-down session 3): the run/cost proofs

Session 2 delivered the **fully `#eval`-validated program** `buildFSAT` +
`encodeIn` (probe `checkFull`, wellformed & non-wellformed instances). Design is
GO on every count: the tree serialization, the unary var-index arithmetic
(`line*L + step*offset (+i)` via `concat`/mul-loops), and the on-machine guard
(`computeWF`) all reproduce `BinaryCC_to_FSAT_instance` exactly. What remains is
the `PolyTimeComputableLang BinaryCC_to_FSAT_instance` witness — pure proof work,
no design risk. Ordered (templates in `FlatCC_to_BinaryCC_free.lean`):

1. **`encodeIn_size ≤ 2·size+1` — ✅ DONE (session 3 part 1).**
2. **Run lemmas bottom-up** — the crux. Prove, mirroring `sentStep_run`/
   `initStep_run` fold invariants:
   - ✅ `emitBitsFromScan_run` / `emitBitsFromSent_run` — DONE (parts 1–2):
     `OUT = OUT₀ ++ serF (encodeBitsAt start bits)`; `_Sent` additionally
     leaves `SCAN` past the terminator (two-phase `SBInv`).
   - ✅ `emitCardsAt_run` — DONE (part 2b): `cardsPrefix`/`serF_encodeCardsAt`
     algebra + single-phase guarded `CAInv`.
   - ✅ `stepBody_run` — DONE (part 2c), with the register-generic
     `unaryMulLoop_run`/`unarySubLoop_run`; matches `encodeStepConstraint`'s
     dite exactly.
   - ✅ `emitAllSteps_run` — DONE (part 3): the two-level `listAnd` fold.
     ONE generic `andPrefix`/`serF_listAnd` serves both levels (instead of
     the sketched `stepsPrefix`/`linesPrefix` pair); invariants `ASInv`
     (inner, black-boxed `stepBody_run` per iteration, exact loop bound so
     no idle case) and `ALInv` (outer, per-line `LINEL` re-derivation via
     `unaryMulLoop_run`); loop bodies named `stepIterBody`/`lineBody`.
     Gotcha hit: `rw [List.range_succ]` picks the INNER `range (L+1)` when
     both ranges are in the goal — unroll the outer one in an isolated
     `have hsnoc` first.
   - ✅ `readOneFinal_run` — DONE (part 4): the sentinel-stream *parse*
     (`RFInv` = `SBInv`'s decode half; outputs `FBITS` raw bits + `BLEN`
     unary length, `SCANF` past the terminator; loop body named
     `readFinBody`). Both `_run` lemma halves of the pattern now exist:
     re-emit (`SBInv`) and parse (`RFInv`).
   - ✅ `emitFinal_run` — DONE (part 5): the `listOr`-over-`listOr` unroll,
     sorry-free & axiom-clean (`[propext, Quot.sound]`). `emitFinal` was
     REFACTORED into named defeq sub-bodies (`finalStepBody`/
     `finalStepIterBody`/`finalStringBody`) mirroring `emitAllSteps`'s
     `stepBody`/`stepIterBody`/`lineBody` — do this before any monolithic
     emitter's run lemma (probe stays green, it is defeq). ONE generic
     `orPrefix`/`orPrefix_append`/`serF_listOr` serves both `listOr` levels
     (mirror of `andPrefix`/`serF_listAnd`). Leaf `finalStepBody_run` copies
     `stepBody_run`'s dite shape (`STEPO` mul `KFSTEP`, `SUMW = STEPO ++ BLEN`,
     `REM` via `unarySubLoop_run`, guard ⇔ `encodeFinalAtStep`'s dite,
     `FSTART = STEPSL ++ STEPO`, guard-pass `emitBitsFromScan_run` off a fresh
     `SCAN := FBITS`, guard-fail `emitFalse`). Middle loop `FSInv`/
     `innerFinalSteps_run` copies `ASInv`/`innerSteps_run` (exact bound over
     `LREG1`). Outer `FFInv`/`FFInv_step` copies `CAInv`
     (`nonEmpty`-guarded stream loop) but each live iteration runs
     `readOneFinal_run` + `innerFinalSteps_run` + `emitFalse`; prelude
     `STEPSL := 1^(steps·L)` is one `unaryMulLoop_run` (bound `STEPS`, src
     `LREG`). **`emitBitsFromScan_run` was strengthened with a frame clause**
     (was `SCAN`/`OUT` only) — `buildFSAT_run` needs it too. Gotcha:
     `set w9 := w8.set SCAN v` auto-folds the RHS of the earlier `e9 : … =
     w8.set SCAN v`, so drop the redundant `← hw9` from the `heval` chain; and
     a residual `serF falseFml` literal needs `rw [show serF falseFml =
     [1,1,0,0,0] from rfl]` before `simp`.
   - ✅ `computeWF_run` — DONE: `(computeWF.eval …).get GWF = if
     BinaryCC_wellformed C then [1] else []`, sorry-free & axiom-clean
     (`[propext, Classical.choice, Quot.sound]`). The three checks
     `leCheck_run` (truncated-subtraction ≤), `dvdCheck_run` (unary `X mod D`
     by repeated subtraction — pure-arithmetic `DvdArith.subMod` reaching
     `a % d`, machine fold `dvdBody_step`), `cardLenCheck_run` (guarded card
     stream `CLInv` mirroring `CAInv`, per-item sentinel parse
     `cardLenItem_run`/`CEInv` mirroring `readOneFinal`/`RFInv`) plus
     `andFlag_run`/`nonEmptyTFLG_run` are all landed. The 6 machine checks ⇔
     `BinaryCC_wellformed` via `wf_iff` (`∃k,k>0∧width=k*offset ↔ offset∣width`
     under `width>0,offset>0`; `cardsOKB_iff`). `dvdCheck_run` exposes
     `ZERO=[]` for the next `dvdCheck`; `andFlag_run` threads it. Needs
     `hZ : u.get ZERO = []` (holds — encodeIn/precompLen leave reg 56 empty).
     ⚠ Loop bodies were factored to named defs first (`dvdBody`,
     `cardLenElemBody`, `cardLenCardBody`) — probe stays green (defeq).
   - ✅ `buildFSAT_run` — DONE (part 7): `(buildFSAT.eval (encodeIn C)).get
     FOUT = serF (BinaryCC_to_FSAT_instance C)`, sorry-free & axiom-clean.
     `computeWF_run` was strengthened with a frame clause (its 14-register
     write set: GWF/TFLG/ZERO/MREM/MCHK/MGE/KTMP/KTMP2/SCANW/CLEN/DONE/EMARK/
     KBIT/KCARD); new `precompLen_run` (LREG/LREG1 off INIT). Gotchas:
     `encodeIn`'s `.set` chain elaborates to `List.set` (receiver type is the
     unfolded abbrev), so `State.get_set_ne` does NOT rewrite it — but every
     `State.get (encodeIn C) R` is definitional, close with `rfl`. ZERO is
     dirty after `computeWF` (no ZERO clause in its conclusion); the branch
     re-clears it before the emitters, so thread `hv2ZERO`, not a u2-fact.
     `computes` = `decodeOut_of_serF` + `buildFSAT_run`. **Exit layout for the
     seam**: `FOUT` (reg 0) = the serialized formula; regs 5/17–21 (STEPS +
     the five inputs) still hold `encodeIn` values; everything else in
     1..regFrame−1 is potentially dirty (OUT 22 holds a copy of the output;
     emitter/guard scratch 23–56) — the FSAT_to_SAT seam should copy `FOUT`
     and scrub the rest.
3. **`cost_le` (NEXT)** — a low-degree polynomial (nested-loop product).
   Cost-magnitude probe (2026-07-10, scratch): `Cmd.cost buildFSAT (encodeIn
   C)` at `steps=k, L=2k` for `k=2,4,8,16` gives `38978 / 606470 / 18752958 /
   882117294` — fixed-degree growth (ratio ≈ 32–47 per doubling ⇒ degree ~5–6
   in `k`), NO structural risk. Do a `cost_forBnd_le` accounting pass
   (cf. CliqueRel quartic→quintic, and `binBudget_le_poly`); none of the
   emitters carries a cost lemma yet — bound each bottom-up mirroring the run
   lemmas' structure (leaf gadgets → `stepBody`/`finalStepBody` → the loops →
   `computeWF` → assembly). The unary var-index mul-loops are `Θ(index²)`
   (concat re-reads the accumulator) with `Θ(steps·L)` indices.
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

/-! ## 4. `cost_le` — the cost accounting (session 4)

Per-loop cost bounds via `Cmd.cost_forBnd_le`, reusing the run invariants
(`BSInv`/`SBInv`/`CAInv`/…) and their `_step` lemmas as the loop motive
(extended by a `WREG`-length clause where the body reads scratch), and bounding
each loop-free body by the generic `Cmd.cost_le_flat` (`Lang/CostFlat.lean`).
Every lemma takes ONE ceiling parameter `Ω` with hypotheses stating what it
dominates; `OUT` ceilings chain through `serF`-length bounds
(`serF_length_le_size` + `listAnd`/`listOr` membership monotonicity) against
the final output, whose size `BinaryCC_to_FSAT_instance_size_bound` bounds.
Constants stay SYMBOLIC (`def`s over `Cmd.flatK`) — only `inOPoly` matters. -/

/-! ### Serialization length bounds -/

theorem serF_length_le_size (f : formula) : (serF f).length ≤ 4 * encodable.size f := by
  induction f with
  | ftrue => simp [serF]
  | fvar v =>
      simp only [serF, encodable_size_formula_fvar, List.length_append,
        List.length_cons, List.length_replicate, List.length_nil]
      omega
  | fand a b iha ihb =>
      simp only [serF, encodable_size_formula_fand, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | forr a b iha ihb =>
      simp only [serF, encodable_size_formula_forr, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | fneg a iha =>
      simp only [serF, encodable_size_formula_fneg, List.length_append,
        List.length_cons, List.length_nil]
      omega

/-- A conjunct's serialization is no longer than the whole `listAnd`'s. -/
theorem serF_length_le_of_mem_listAnd {f : formula} {fs : List formula}
    (h : f ∈ fs) : (serF f).length ≤ (serF (listAnd fs)).length := by
  induction fs with
  | nil => cases h
  | cons g gs ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · show _ ≤ (serF (.fand f (listAnd gs))).length
        simp [serF]; omega
      · refine le_trans (ih h') ?_
        show _ ≤ (serF (.fand g (listAnd gs))).length
        simp [serF]; omega

/-- A disjunct's serialization is no longer than the whole `listOr`'s. -/
theorem serF_length_le_of_mem_listOr {f : formula} {fs : List formula}
    (h : f ∈ fs) : (serF f).length ≤ (serF (listOr fs)).length := by
  induction fs with
  | nil => cases h
  | cons g gs ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · show _ ≤ (serF (.forr f (listOr gs))).length
        simp [serF]; omega
      · refine le_trans (ih h') ?_
        show _ ≤ (serF (.forr g (listOr gs))).length
        simp [serF]; omega

/-- Mid-loop `OUT` ceiling, `listAnd` level: any processed-prefix `andPrefix`
is bounded by the closed serialization. -/
theorem andPrefix_take_length_le (fs : List formula) (i : Nat) :
    (andPrefix (fs.take i)).length ≤ (serF (listAnd fs)).length := by
  rw [serF_listAnd]
  calc (andPrefix (fs.take i)).length
      ≤ (andPrefix (fs.take i)).length + (andPrefix (fs.drop i)).length :=
        Nat.le_add_right _ _
    _ = (andPrefix (fs.take i ++ fs.drop i)).length := by
        rw [andPrefix_append, List.length_append]
    _ = (andPrefix fs).length := by rw [List.take_append_drop]
    _ ≤ (andPrefix fs ++ serF .ftrue).length := by simp

/-- Mid-loop `OUT` ceiling, `listOr` level. -/
theorem orPrefix_take_length_le (fs : List formula) (i : Nat) :
    (orPrefix (fs.take i)).length ≤ (serF (listOr fs)).length := by
  rw [serF_listOr]
  calc (orPrefix (fs.take i)).length
      ≤ (orPrefix (fs.take i)).length + (orPrefix (fs.drop i)).length :=
        Nat.le_add_right _ _
    _ = (orPrefix (fs.take i ++ fs.drop i)).length := by
        rw [orPrefix_append, List.length_append]
    _ = (orPrefix fs).length := by rw [List.take_append_drop]
    _ ≤ _ := by simp

/-- Mid-loop `OUT` ceiling, bit level. -/
theorem bitsPrefix_take_length_le (start : Nat) (bits : List Bool) (i : Nat) :
    (bitsPrefix start (bits.take i)).length
      ≤ (serF (BinaryCCToFSAT.encodeBitsAt start bits)).length := by
  rw [serF_encodeBitsAt]
  calc (bitsPrefix start (bits.take i)).length
      ≤ (bitsPrefix start (bits.take i)).length
        + (bitsPrefix (start + (bits.take i).length) (bits.drop i)).length :=
        Nat.le_add_right _ _
    _ = (bitsPrefix start (bits.take i ++ bits.drop i)).length := by
        rw [bitsPrefix_append, List.length_append]
    _ = (bitsPrefix start bits).length := by rw [List.take_append_drop]
    _ ≤ _ := by simp

/-- Mid-loop `OUT` ceiling, card level. -/
theorem cardsPrefix_take_length_le (sA sB : Nat) (cs : List (CCCard Bool)) (j : Nat) :
    (cardsPrefix sA sB (cs.take j)).length
      ≤ (serF (listOr (cs.map (encodeCardAt sA sB)))).length := by
  rw [serF_encodeCardsAt]
  calc (cardsPrefix sA sB (cs.take j)).length
      ≤ (cardsPrefix sA sB (cs.take j)).length
        + (cardsPrefix sA sB (cs.drop j)).length := Nat.le_add_right _ _
    _ = (cardsPrefix sA sB (cs.take j ++ cs.drop j)).length := by
        rw [cardsPrefix_append, List.length_append]
    _ = (cardsPrefix sA sB cs).length := by rw [List.take_append_drop]
    _ ≤ _ := by simp

/-- Dropping bits only shortens the sentinel stream. -/
private theorem encSList_drop_length_le (l : List Nat) (i : Nat) :
    (FlatTCCFree.encSList (l.drop i)).length ≤ (FlatTCCFree.encSList l).length := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
      cases l with
      | nil => simp
      | cons v xs =>
          rw [List.drop_succ_cons]
          refine (ih xs).trans ?_
          show _ ≤ (FlatTCCFree.encSElem v ++ FlatTCCFree.encSList xs).length
          simp

/-- Dropping cards only shortens the card stream. -/
private theorem encCardsOut_drop_length_le (cs : List (CCCard Nat)) (j : Nat) :
    (FlatTCCFree.encCardsOut (cs.drop j)).length
      ≤ (FlatTCCFree.encCardsOut cs).length := by
  induction j generalizing cs with
  | zero => simp
  | succ j ih =>
      cases cs with
      | nil => simp
      | cons c cs =>
          rw [List.drop_succ_cons]
          refine (ih cs).trans ?_
          show _ ≤ (FlatTCCFree.encCardOut c ++ FlatTCCFree.encCardsOut cs).length
          simp

/-- Dropping final strings only shortens the final stream. -/
private theorem encFinal_drop_length_le (fss : List (List Nat)) (j : Nat) :
    (FlatTCCFree.encFinal (fss.drop j)).length
      ≤ (FlatTCCFree.encFinal fss).length := by
  induction j generalizing fss with
  | zero => simp
  | succ j ih =>
      cases fss with
      | nil => simp
      | cons s fss =>
          rw [List.drop_succ_cons]
          refine (ih fss).trans ?_
          show _ ≤ (FlatTCCFree.encSList s ++ FlatTCCFree.encFinal fss).length
          simp

/-! ### Constant-cost facts for the literal-tag emitters -/

private theorem emitFtrue_cost (s : State) : emitFtrue.cost s = 3 := rfl
private theorem emitFandTag_cost (s : State) : emitFandTag.cost s = 3 := rfl
private theorem emitForrTag_cost (s : State) : emitForrTag.cost s = 3 := rfl
private theorem emitFalse_cost (s : State) : emitFalse.cost s = 9 := rfl

/-! ### The scan-driven bit emitter: cost -/

/-- The loop body of `emitBitsFromScan`, named for the cost pass. -/
private def bsBody (BASE : Nat) : Cmd :=
  Cmd.op (.head TFLG SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
  Cmd.op (.concat WREG BASE KBIT) ;; emitFandTag ;; emitLitAt

private theorem emitBitsFromScan_eq (BASE bound : Nat) :
    emitBitsFromScan BASE bound = (Cmd.forBnd KBIT bound (bsBody BASE) ;; emitFtrue) := rfl

/-- `bsBody`'s only `WREG` write is `WREG := BASE ++ counter`. -/
private theorem bsBody_WREG (BASE : Nat) (w : State)
    (hBT : BASE ≠ TFLG) (hBS : BASE ≠ SCAN) :
    State.get ((bsBody BASE).eval w) WREG = State.get w BASE ++ State.get w KBIT := by
  unfold bsBody
  rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq,
    Cmd.eval_get_of_not_writes _ _ WREG (by decide), Cmd.eval_op]
  simp only [Op.eval, State.get_set_eq, Cmd.eval_op]
  rw [State.get_set_ne _ _ _ _ hBS, State.get_set_ne _ _ _ _ hBT,
    State.get_set_ne _ _ _ _ (show KBIT ≠ SCAN by decide),
    State.get_set_ne _ _ _ _ (show KBIT ≠ TFLG by decide)]

/-- **`emitBitsFromScan` cost**: quadratic in the ceiling `Ω`. `Ω` must dominate
the entry `OUT` plus the full emission, the entry `WREG`, and `start + |bits|`. -/
theorem emitBitsFromScan_cost (BASE bound start : Nat) (bits : List Bool) (u : State)
    (Ω : Nat)
    (hBS : BASE ≠ SCAN) (hBO : BASE ≠ OUT) (hBW : BASE ≠ WREG) (hBT : BASE ≠ TFLG)
    (hBK : BASE ≠ KBIT)
    (hB : State.get u BASE = List.replicate start 1)
    (hbnd : (State.get u bound).length = bits.length)
    (hSC : State.get u SCAN = FlatCCBinFree.bitsNat bits)
    (hΩO : (State.get u OUT).length
        + (serF (BinaryCCToFSAT.encodeBitsAt start bits)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩs : start + bits.length ≤ Ω) :
    (emitBitsFromScan BASE bound).cost u
      ≤ (Cmd.flatK (bsBody 0) + 6) * ((Ω + 1) * (Ω + 1)) := by
  rw [emitBitsFromScan_eq, Cmd.cost_seq, emitFtrue_cost]
  have hloop := Cmd.cost_forBnd_le KBIT bound (bsBody BASE) u
    (Cmd.flatK (bsBody 0) * (Ω + 1))
    (fun i st => BSInv BASE start bits u i st ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨by rw [List.drop_zero]; exact hSC,
      by rw [List.take_zero]; simp [bitsPrefix], fun r _ _ _ _ _ => rfl⟩, hΩW⟩
    (fun i st hi hM => by
      obtain ⟨hInv, _⟩ := hM
      have hi' : i < bits.length := by rw [hbnd] at hi; exact hi
      refine ⟨BSInv_step BASE start bits u hBS hBO hBW hBT hBK hB i hi' st hInv, ?_⟩
      rw [bsBody_WREG BASE _ hBT hBS]
      have hstB : State.get st BASE = List.replicate start 1 := by
        rw [hInv.2.2 BASE hBS hBO hBW hBT hBK]; exact hB
      rw [State.get_set_ne _ _ _ _ hBK, State.get_set_eq, hstB]
      simp only [List.length_append, List.length_replicate]
      omega)
    (fun i st hi hM => by
      obtain ⟨⟨hSCANi, hOUTi, hframei⟩, hWl⟩ := hM
      have hi' : i < bits.length := by rw [hbnd] at hi; exact hi
      have hread : ∀ r ∈ Cmd.costReads (bsBody BASE),
          (State.get (st.set KBIT (List.replicate i 1)) r).length ≤ Ω := by
        intro r hr
        have hlist : Cmd.costReads (bsBody BASE)
            = [SCAN, BASE, KBIT, OUT, WREG, OUT, WREG] := rfl
        rw [hlist] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hS' : (State.get (st.set KBIT (List.replicate i 1)) SCAN).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show SCAN ≠ KBIT by decide), hSCANi]
          have hd : (FlatCCBinFree.bitsNat (bits.drop i)).length ≤ bits.length := by
            rw [show (FlatCCBinFree.bitsNat (bits.drop i)).length
                = (bits.drop i).length from List.length_map _]
            rw [List.length_drop]
            omega
          omega
        have hB' : (State.get (st.set KBIT (List.replicate i 1)) BASE).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ hBK,
            hframei BASE hBS hBO hBW hBT hBK, hB, List.length_replicate]
          omega
        have hK' : (State.get (st.set KBIT (List.replicate i 1)) KBIT).length ≤ Ω := by
          rw [State.get_set_eq, List.length_replicate]
          omega
        have hO' : (State.get (st.set KBIT (List.replicate i 1)) OUT).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show OUT ≠ KBIT by decide), hOUTi,
            List.length_append]
          have := bitsPrefix_take_length_le start bits i
          omega
        have hW' : (State.get (st.set KBIT (List.replicate i 1)) WREG).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show WREG ≠ KBIT by decide)]
          exact hWl
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hS', hB', hK', hO', hW', hO', hW']
      exact (Cmd.cost_le_flat (bsBody BASE) rfl
        (st.set KBIT (List.replicate i 1)) Ω hread).1)
  -- close the arithmetic
  have hlen : (State.get u bound).length ≤ Ω := by rw [hbnd]; omega
  set K := Cmd.flatK (bsBody 0) with hK
  set A := K * (Ω + 1) with hA
  set len := (State.get u bound).length with hlenDef
  have h1 : len * A ≤ (Ω + 1) * A := Nat.mul_le_mul_right A (by omega)
  have h2 : len * len ≤ Ω * Ω := Nat.mul_le_mul hlen hlen
  have h3 : (Ω + 1) * A = K * ((Ω + 1) * (Ω + 1)) := by rw [hA]; ring
  have h4 : (K + 6) * ((Ω + 1) * (Ω + 1))
      = K * ((Ω + 1) * (Ω + 1)) + 6 * ((Ω + 1) * (Ω + 1)) := by ring
  have h5 : (Ω + 1) * (Ω + 1) = Ω * Ω + 2 * Ω + 1 := by ring
  omega

/-! ### The sentinel-driven bit emitter: cost -/

/-- `sentBitBody` either leaves `WREG` alone or writes `BASE ++ counter`. -/
private theorem sentBitBody_WREG (BASE : Nat) (w : State)
    (hBT : BASE ≠ TFLG) (hBS : BASE ≠ SCAN) (hBE : BASE ≠ EMARK) :
    (State.get ((sentBitBody BASE).eval w) WREG).length
      ≤ max (State.get w WREG).length
          ((State.get w BASE).length + (State.get w KBIT).length) := by
  unfold sentBitBody
  by_cases hD : State.get w DONE = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hD, Cmd.eval_op]
    simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ (show WREG ≠ ZERO by decide)]
    exact Nat.le_max_left _ _
  · rw [Cmd.eval_ifBit_false _ _ _ _ hD, Cmd.eval_seq]
    set w1 := (Cmd.op (.head EMARK SCAN)).eval w with hw1
    have hw1f : ∀ r : Var, r ≠ EMARK → State.get w1 r = State.get w r := by
      intro r hr
      rw [hw1, Cmd.eval_op]
      exact Op.eval_get_ne_writesTo _ _ _ hr
    by_cases hE : State.get w1 EMARK = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hE]
      rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq,
        Cmd.eval_get_of_not_writes _ _ WREG (by decide), Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, Cmd.eval_op]
      rw [State.get_set_ne _ _ _ _ hBT, State.get_set_ne _ _ _ _ hBS,
        State.get_set_ne _ _ _ _ (show KBIT ≠ TFLG by decide),
        State.get_set_ne _ _ _ _ (show KBIT ≠ SCAN by decide),
        hw1f BASE hBE, hw1f KBIT (by decide)]
      rw [List.length_append]
      exact Nat.le_max_right _ _
    · rw [Cmd.eval_ifBit_false _ _ _ _ hE,
        Cmd.eval_get_of_not_writes _ _ WREG (by decide),
        hw1f WREG (by decide)]
      exact Nat.le_max_left _ _

/-- **`emitBitsFromSent` cost**: quadratic in the ceiling `Ω`. `Ω` must dominate
the entry `OUT` plus the full emission, the entry `WREG`, and
`start + |SCAN stream|`. -/
theorem emitBitsFromSent_cost (BASE start : Nat) (bits : List Bool) (rest : List Nat)
    (u : State) (Ω : Nat)
    (hBS : BASE ≠ SCAN) (hBO : BASE ≠ OUT) (hBW : BASE ≠ WREG) (hBT : BASE ≠ TFLG)
    (hBK : BASE ≠ KBIT) (hBD : BASE ≠ DONE) (hBE : BASE ≠ EMARK) (hBZ : BASE ≠ ZERO)
    (hB : State.get u BASE = List.replicate start 1)
    (hZ : State.get u ZERO = [])
    (hSC : State.get u SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest)
    (hΩO : (State.get u OUT).length
        + (serF (BinaryCCToFSAT.encodeBitsAt start bits)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩs : start + (State.get u SCAN).length ≤ Ω) :
    (emitBitsFromSent BASE).cost u
      ≤ (Cmd.flatK (sentBitBody 0) + 8) * ((Ω + 1) * (Ω + 1)) := by
  have heq : emitBitsFromSent BASE
      = (Cmd.op (.clear DONE) ;; (Cmd.forBnd KBIT SCAN (sentBitBody BASE) ;; emitFtrue)) := rfl
  rw [heq, Cmd.cost_seq, Cmd.cost_seq, emitFtrue_cost, Cmd.cost_op]
  simp only [Op.cost]
  have e0 : (Cmd.op (.clear DONE)).eval u = u.set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  rw [e0]
  set u1 := u.set DONE [] with hu1
  have hu1f : ∀ r : Var, r ≠ DONE → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1D : State.get u1 DONE = [] := State.get_set_eq _ _ _
  have hu1SC : State.get u1 SCAN
      = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest := by
    rw [hu1f SCAN (by decide)]; exact hSC
  have hu1SClen : (State.get u1 SCAN).length = (State.get u SCAN).length := by
    rw [hu1f SCAN (by decide)]
  clear_value u1
  have hsuffix : ∀ i : Nat,
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop i))).length + rest.length
        ≤ Ω := by
    intro i
    have h1 : (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop i))).length
        ≤ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length := by
      rw [show FlatCCBinFree.bitsNat (bits.drop i)
          = (FlatCCBinFree.bitsNat bits).drop i from List.map_drop ..]
      exact encSList_drop_length_le _ i
    have h2 : (State.get u SCAN).length
        = (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length + rest.length := by
      rw [hSC, List.length_append]
    omega
  have hloop := Cmd.cost_forBnd_le KBIT SCAN (sentBitBody BASE) u1
    (Cmd.flatK (sentBitBody 0) * (Ω + 1))
    (fun i st => SBInv BASE start bits rest u1 i st
      ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨fun _ => ⟨hu1D, by rw [List.drop_zero]; exact hu1SC,
        by rw [List.take_zero]; simp [bitsPrefix]⟩,
      fun h => absurd h (by omega),
      by rw [hu1f ZERO (by decide)]; exact hZ,
      fun r _ _ _ _ _ _ _ _ => rfl⟩,
      by rw [hu1f WREG (by decide)]; exact hΩW⟩
    (fun i st hi hM => by
      obtain ⟨hInv, hWprev⟩ := hM
      refine ⟨SBInv_step BASE start bits rest u1 hBS hBO hBW hBT hBK hBD hBE hBZ
        (by rw [hu1f BASE hBD]; exact hB) i st hInv, ?_⟩
      refine le_trans (sentBitBody_WREG BASE _ hBT hBS hBE) ?_
      have hstB : State.get st BASE = List.replicate start 1 := by
        rw [hInv.2.2.2 BASE hBS hBO hBW hBT hBK hBD hBE hBZ, hu1f BASE hBD]
        exact hB
      rw [State.get_set_ne _ _ _ _ hBK, State.get_set_eq, hstB, List.length_replicate,
        State.get_set_ne _ _ _ _ (show WREG ≠ KBIT by decide)]
      have hiΩ : i < (State.get u1 SCAN).length := hi
      simp only [List.length_replicate]
      rw [hu1SClen] at hiΩ
      omega)
    (fun i st hi hM => by
      obtain ⟨⟨hph1, hph2, hZERO, hframei⟩, hWl⟩ := hM
      have hread : ∀ r ∈ Cmd.costReads (sentBitBody BASE),
          (State.get (st.set KBIT (List.replicate i 1)) r).length ≤ Ω := by
        intro r hr
        have hlist : Cmd.costReads (sentBitBody BASE)
            = [SCAN, BASE, KBIT, OUT, WREG, OUT, WREG,
               SCAN, SCAN, SCAN, SCAN] := rfl
        rw [hlist] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hSCANce : (State.get st SCAN).length ≤ Ω := by
          by_cases hile : i ≤ bits.length
          · obtain ⟨_, hS, _⟩ := hph1 hile
            rw [hS, List.length_append]
            exact hsuffix i
          · obtain ⟨_, hS, _⟩ := hph2 (by omega)
            rw [hS]
            have := hsuffix 0
            omega
        have hOUTce : (State.get st OUT).length ≤ Ω := by
          by_cases hile : i ≤ bits.length
          · obtain ⟨_, _, hO⟩ := hph1 hile
            rw [hO, List.length_append, hu1f OUT (by decide)]
            have := bitsPrefix_take_length_le start bits i
            omega
          · obtain ⟨_, _, hO⟩ := hph2 (by omega)
            rw [hO, List.length_append, hu1f OUT (by decide)]
            have h1 := bitsPrefix_take_length_le start bits bits.length
            rw [List.take_length] at h1
            omega
        have hS' : (State.get (st.set KBIT (List.replicate i 1)) SCAN).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show SCAN ≠ KBIT by decide)]
          exact hSCANce
        have hB' : (State.get (st.set KBIT (List.replicate i 1)) BASE).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ hBK,
            hframei BASE hBS hBO hBW hBT hBK hBD hBE hBZ, hu1f BASE hBD, hB,
            List.length_replicate]
          omega
        have hK' : (State.get (st.set KBIT (List.replicate i 1)) KBIT).length ≤ Ω := by
          rw [State.get_set_eq, List.length_replicate]
          have hiΩ : i < (State.get u1 SCAN).length := hi
          rw [hu1SClen] at hiΩ
          omega
        have hO' : (State.get (st.set KBIT (List.replicate i 1)) OUT).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show OUT ≠ KBIT by decide)]
          exact hOUTce
        have hW' : (State.get (st.set KBIT (List.replicate i 1)) WREG).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show WREG ≠ KBIT by decide)]
          exact hWl
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hS', hB', hK', hO', hW', hO', hW', hS', hS', hS', hS']
      exact (Cmd.cost_le_flat (sentBitBody BASE) rfl
        (st.set KBIT (List.replicate i 1)) Ω hread).1)
  -- close the arithmetic
  have hlen : (State.get u1 SCAN).length ≤ Ω := by rw [hu1SClen]; omega
  set K := Cmd.flatK (sentBitBody 0) with hK
  set A := K * (Ω + 1) with hA
  set len := (State.get u1 SCAN).length with hlenDef
  have h1 : len * A ≤ (Ω + 1) * A := Nat.mul_le_mul_right A (by omega)
  have h2 : len * len ≤ Ω * Ω := Nat.mul_le_mul hlen hlen
  have h3 : (Ω + 1) * A = K * ((Ω + 1) * (Ω + 1)) := by rw [hA]; ring
  have h4 : (K + 8) * ((Ω + 1) * (Ω + 1))
      = K * ((Ω + 1) * (Ω + 1)) + 8 * ((Ω + 1) * (Ω + 1)) := by ring
  have h5 : (Ω + 1) * (Ω + 1) = Ω * Ω + 2 * Ω + 1 := by ring
  omega

/-! ### The final-string parse: cost -/

/-- **`readOneFinal` cost**: quadratic in the ceiling `Ω ≥ |SCANF|`. -/
theorem readOneFinal_cost (bits : List Bool) (rest : List Nat) (u : State) (Ω : Nat)
    (hSC : State.get u SCANF
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest)
    (hΩS : (State.get u SCANF).length ≤ Ω) :
    readOneFinal.cost u
      ≤ (Cmd.flatK readFinBody + 10) * ((Ω + 1) * (Ω + 1)) := by
  have heq : readOneFinal
      = (Cmd.op (.clear FBITS) ;; (Cmd.op (.clear BLEN) ;; (Cmd.op (.clear DONE) ;;
        Cmd.forBnd KTMP SCANF readFinBody))) := rfl
  rw [heq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op,
    Cmd.cost_op]
  simp only [Op.cost]
  have e1 : (Cmd.op (.clear FBITS)).eval u = u.set FBITS [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e2 : (Cmd.op (.clear BLEN)).eval (u.set FBITS [])
      = (u.set FBITS []).set BLEN [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e3 : (Cmd.op (.clear DONE)).eval ((u.set FBITS []).set BLEN [])
      = ((u.set FBITS []).set BLEN []).set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  rw [e1, e2, e3]
  have hu3f : ∀ r : Var, r ≠ FBITS → r ≠ BLEN → r ≠ DONE →
      State.get (((u.set FBITS []).set BLEN []).set DONE []) r = State.get u r := by
    intro r h1 h2 h3
    rw [State.get_set_ne _ _ _ _ h3, State.get_set_ne _ _ _ _ h2,
      State.get_set_ne _ _ _ _ h1]
  set u3 := ((u.set FBITS []).set BLEN []).set DONE [] with hu3
  have hu3D : State.get u3 DONE = [] := State.get_set_eq _ _ _
  have hu3B : State.get u3 BLEN = [] := by
    rw [hu3, State.get_set_ne _ _ _ _ (show BLEN ≠ DONE by decide), State.get_set_eq]
  have hu3F : State.get u3 FBITS = [] := by
    rw [hu3, State.get_set_ne _ _ _ _ (show FBITS ≠ DONE by decide),
      State.get_set_ne _ _ _ _ (show FBITS ≠ BLEN by decide), State.get_set_eq]
  have hu3SC : State.get u3 SCANF
      = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest := by
    rw [hu3]
    rw [hu3f SCANF (by decide) (by decide) (by decide)]
    exact hSC
  have hu3SClen : (State.get u3 SCANF).length = (State.get u SCANF).length := by
    rw [hu3SC, hSC]
  clear_value u3
  have hsuffix : ∀ i : Nat,
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop i))).length + rest.length
        ≤ Ω := by
    intro i
    have h1 : (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop i))).length
        ≤ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length := by
      rw [show FlatCCBinFree.bitsNat (bits.drop i)
          = (FlatCCBinFree.bitsNat bits).drop i from List.map_drop ..]
      exact encSList_drop_length_le _ i
    have h2 : (State.get u SCANF).length
        = (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length + rest.length := by
      rw [hSC, List.length_append]
    omega
  have hbase : RFInv bits rest u3 0 u3 :=
    ⟨fun _ => ⟨hu3D, by rw [List.drop_zero]; exact hu3SC,
        by rw [List.take_zero]; exact hu3F,
        by rw [List.replicate_zero]; exact hu3B⟩,
      fun h => absurd h (by omega),
      fun r _ _ _ _ _ _ _ _ => rfl⟩
  have hloop := Cmd.cost_forBnd_le KTMP SCANF readFinBody u3
    (Cmd.flatK readFinBody * (Ω + 1))
    (RFInv bits rest u3) hbase
    (fun i st _ hM => RFInv_step bits rest u3 i st hM)
    (fun i st hi hM => by
      obtain ⟨hph1, hph2, hframei⟩ := hM
      have hread : ∀ r ∈ Cmd.costReads readFinBody,
          (State.get (st.set KTMP (List.replicate i 1)) r).length ≤ Ω := by
        intro r hr
        have hlist : Cmd.costReads readFinBody
            = [SCANF, SCANF, SCANF, SCANF, SCANF] := rfl
        rw [hlist] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hSCANce : (State.get st SCANF).length ≤ Ω := by
          by_cases hile : i ≤ bits.length
          · obtain ⟨_, hS, _⟩ := hph1 hile
            rw [hS, List.length_append]
            exact hsuffix i
          · obtain ⟨_, hS, _⟩ := hph2 (by omega)
            rw [hS]
            have := hsuffix 0
            omega
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          (rw [State.get_set_ne _ _ _ _ (show SCANF ≠ KTMP by decide)]; exact hSCANce)
      exact (Cmd.cost_le_flat readFinBody rfl
        (st.set KTMP (List.replicate i 1)) Ω hread).1)
  -- close the arithmetic
  have hlen : (State.get u3 SCANF).length ≤ Ω := by rw [hu3SClen]; omega
  set K := Cmd.flatK readFinBody with hK
  set A := K * (Ω + 1) with hA
  set len := (State.get u3 SCANF).length with hlenDef
  have h1 : len * A ≤ (Ω + 1) * A := Nat.mul_le_mul_right A (by omega)
  have h2 : len * len ≤ Ω * Ω := Nat.mul_le_mul hlen hlen
  have h3 : (Ω + 1) * A = K * ((Ω + 1) * (Ω + 1)) := by rw [hA]; ring
  have h4 : (K + 10) * ((Ω + 1) * (Ω + 1))
      = K * ((Ω + 1) * (Ω + 1)) + 10 * ((Ω + 1) * (Ω + 1)) := by ring
  have h5 : (Ω + 1) * (Ω + 1) = Ω * Ω + 2 * Ω + 1 := by ring
  omega


/-! ### `emitCardsAt`: cost -/

/-- `emitBitsFromSent` never grows `WREG` beyond `max(entry, start + |SCAN|)`
(each loop write is `BASE ++ counter`). Membership hypothesis dischargeable by
`decide` at concrete `BASE`. -/
private theorem emitBitsFromSent_WREG (BASE : Nat) (u : State) (W : Nat)
    (hBT : BASE ≠ TFLG) (hBS : BASE ≠ SCAN) (hBE : BASE ≠ EMARK) (hBK : BASE ≠ KBIT)
    (hBD : BASE ≠ DONE)
    (hBmem : BASE ∉ Cmd.writes (sentBitBody BASE))
    (hW : (State.get u WREG).length ≤ W)
    (hBSc : (State.get u BASE).length + (State.get u SCAN).length ≤ W) :
    (State.get ((emitBitsFromSent BASE).eval u) WREG).length ≤ W := by
  have heq : emitBitsFromSent BASE
      = (Cmd.op (.clear DONE) ;;
          (Cmd.forBnd KBIT SCAN (sentBitBody BASE) ;; emitFtrue)) := rfl
  rw [heq, Cmd.eval_seq, Cmd.eval_seq, emitFtrue_frame _ WREG (by decide)]
  have e0 : (Cmd.op (.clear DONE)).eval u = u.set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  rw [e0]
  set u1 := u.set DONE [] with hu1
  have hu1W : (State.get u1 WREG).length ≤ W := by
    rw [hu1, State.get_set_ne _ _ _ _ (show WREG ≠ DONE by decide)]; exact hW
  have hu1B : State.get u1 BASE = State.get u BASE := by
    rw [hu1, State.get_set_ne _ _ _ _ hBD]
  have hu1SC : State.get u1 SCAN = State.get u SCAN := by
    rw [hu1, State.get_set_ne _ _ _ _ (show SCAN ≠ DONE by decide)]
  clear_value u1
  rw [Cmd.eval_forBnd]
  have hInv := Cmd.foldlState_range_induct (sentBitBody BASE) KBIT
    (State.get u1 SCAN).length u1
    (fun _ st => (State.get st WREG).length ≤ W
      ∧ State.get st BASE = State.get u1 BASE)
    ⟨hu1W, rfl⟩
    (fun i st hi hM => by
      obtain ⟨hWl, hBf⟩ := hM
      constructor
      · refine le_trans (sentBitBody_WREG BASE _ hBT hBS hBE) ?_
        rw [State.get_set_ne _ _ _ _ (show WREG ≠ KBIT by decide),
          State.get_set_ne _ _ _ _ hBK, State.get_set_eq, hBf, hu1B,
          List.length_replicate]
        have hilt : i < (State.get u1 SCAN).length := hi
        rw [hu1SC] at hilt
        exact Nat.max_le.mpr ⟨hWl, by omega⟩
      · rw [Cmd.eval_get_of_not_writes _ _ BASE hBmem,
          State.get_set_ne _ _ _ _ hBK]
        exact hBf)
  exact hInv.1

/-- Per-iteration effect of the card loop: cost bound + `WREG` stays `≤ Ω`. -/
private theorem cardEmitBody_effect (sA sB : Nat) (C : BinaryCC) (u1 : State) (Ω : Nat)
    (hSA1 : State.get u1 STARTA = List.replicate sA 1)
    (hSB1 : State.get u1 STARTB = List.replicate sB 1)
    (hΩO : (State.get u1 OUT).length + (serF (encodeCardsAt C sA sB)).length ≤ Ω)
    (hΩA : sA + (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length ≤ Ω)
    (hΩB : sB + (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length ≤ Ω)
    (j : Nat) (st : State)
    (hInv : CAInv sA sB C.cards u1 j st)
    (hW : (State.get st WREG).length ≤ Ω) :
    cardEmitBody.cost (st.set KCARD (List.replicate j 1))
        ≤ 12 + 2 * ((Cmd.flatK (sentBitBody 0) + 8) * ((Ω + 1) * (Ω + 1)))
    ∧ (State.get (cardEmitBody.eval (st.set KCARD (List.replicate j 1))) WREG).length
        ≤ Ω := by
  obtain ⟨hSCAN, hOUT, hZERO, hframe⟩ := hInv
  set w := st.set KCARD (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KCARD → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSCAN : State.get w SCAN
      = FlatTCCFree.encCardsOut ((C.cards.drop j).map FlatCCBinFree.cardNat) := by
    rw [hwframe SCAN (by decide)]; exact hSCAN
  have hwOUT : State.get w OUT
      = State.get u1 OUT ++ cardsPrefix sA sB (C.cards.take j) := by
    rw [hwframe OUT (by decide)]; exact hOUT
  have hwZ : State.get w ZERO = [] := by
    rw [hwframe ZERO (by decide)]; exact hZERO
  have hwSA : State.get w STARTA = List.replicate sA 1 := by
    rw [hwframe STARTA (by decide), hframe STARTA (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hSA1
  have hwSB : State.get w STARTB = List.replicate sB 1 := by
    rw [hwframe STARTB (by decide), hframe STARTB (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hSB1
  have hwW : (State.get w WREG).length ≤ Ω := by
    rw [hwframe WREG (by decide)]; exact hW
  -- the drop-stream ceiling
  have hstream : (FlatTCCFree.encCardsOut ((C.cards.drop j).map FlatCCBinFree.cardNat)).length
      ≤ (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length := by
    rw [show (C.cards.drop j).map FlatCCBinFree.cardNat
        = (C.cards.map FlatCCBinFree.cardNat).drop j from List.map_drop ..]
    exact encCardsOut_drop_length_le _ j
  clear_value w
  by_cases hj : j < C.cards.length
  · -- live iteration
    have hdrop : C.cards.drop j = C.cards[j] :: C.cards.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    have htake : C.cards.take (j + 1) = C.cards.take j ++ [C.cards[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    set c := C.cards[j] with hc
    clear_value c
    set REST := FlatTCCFree.encCardsOut ((C.cards.drop (j + 1)).map FlatCCBinFree.cardNat)
      with hREST
    have hSCANw : State.get w SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
          ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hwSCAN, hdrop, encCardsOut_cons, hREST]
    have hne : (State.get w SCAN).isEmpty = false := by
      rw [hSCANw]; exact encSList_append_isEmpty _ _
    have e1 : (Cmd.op (.nonEmpty TFLG SCAN)).eval w = w.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w1 := w.set TFLG [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ TFLG → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1T : State.get w1 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w1
    set w2 := emitForrTag.eval w1 with hw2
    have hw2frame : ∀ r : Var, r ≠ OUT → State.get w2 r = State.get w1 r := by
      intro r hr; rw [hw2]; exact emitForrTag_frame w1 r hr
    have hw2OUT : State.get w2 OUT = State.get w1 OUT ++ [1, 0] := by
      rw [hw2, emitForrTag_run]; exact State.get_set_eq _ _ _
    clear_value w2
    set w3 := emitFandTag.eval w2 with hw3
    have hw3frame : ∀ r : Var, r ≠ OUT → State.get w3 r = State.get w2 r := by
      intro r hr; rw [hw3]; exact emitFandTag_frame w2 r hr
    have hw3OUT : State.get w3 OUT = State.get w2 OUT ++ [0, 1] := by
      rw [hw3, emitFandTag_run]; exact State.get_set_eq _ _ _
    clear_value w3
    have hchain : ∀ r : Var, r ≠ OUT → r ≠ TFLG → State.get w3 r = State.get w r := by
      intro r h1 h2
      rw [hw3frame r h1, hw2frame r h1, hw1frame r h2]
    have hw3SCAN : State.get w3 SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
          ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hchain SCAN (by decide) (by decide)]; exact hSCANw
    have hw3Z : State.get w3 ZERO = [] := by
      rw [hchain ZERO (by decide) (by decide)]; exact hwZ
    have hw3SA : State.get w3 STARTA = List.replicate sA 1 := by
      rw [hchain STARTA (by decide) (by decide)]; exact hwSA
    have hw3SB : State.get w3 STARTB = List.replicate sB 1 := by
      rw [hchain STARTB (by decide) (by decide)]; exact hwSB
    have hw3W : (State.get w3 WREG).length ≤ Ω := by
      rw [hchain WREG (by decide) (by decide)]; exact hwW
    have hw3OUTfull : State.get w3 OUT
        = State.get u1 OUT ++ cardsPrefix sA sB (C.cards.take j) ++ [1, 0] ++ [0, 1] := by
      rw [hw3OUT, hw2OUT, hw1frame OUT (by decide), hwOUT]
    -- OUT/prefix bookkeeping
    have hexp : cardsPrefix sA sB (C.cards.take (j + 1))
        = cardsPrefix sA sB (C.cards.take j)
          ++ ([1, 0] ++ ([0, 1] ++ (serF (encodeBitsAt sA c.prem)
              ++ serF (encodeBitsAt sB c.conc)))) := by
      rw [htake, cardsPrefix_append]
      simp [cardsPrefix, encodeCardAt, serF, List.append_assoc]
    have hcpj1 : (cardsPrefix sA sB (C.cards.take (j + 1))).length
        ≤ (serF (encodeCardsAt C sA sB)).length :=
      cardsPrefix_take_length_le sA sB C.cards (j + 1)
    have hlenexp : (cardsPrefix sA sB (C.cards.take (j + 1))).length
        = (cardsPrefix sA sB (C.cards.take j)).length + 4
          + (serF (encodeBitsAt sA c.prem)).length
          + (serF (encodeBitsAt sB c.conc)).length := by
      rw [hexp]
      simp [List.length_append]
      omega
    -- the SCAN ceilings
    have hw3SCANlen : (State.get w3 SCAN).length
        ≤ (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length := by
      rw [hw3SCAN, hREST, ← encCardsOut_cons, ← hdrop]
      exact hstream
    -- the prem emitter: cost + run facts
    have hcostA := emitBitsFromSent_cost STARTA sA c.prem
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) w3 Ω
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hw3SA hw3Z hw3SCAN
      (by rw [hw3OUTfull]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)
      hw3W
      (by rw [hw3SCAN] at hw3SCANlen ⊢
          omega)
    obtain ⟨h4SCAN, h4OUT, h4Z, h4frame⟩ :=
      emitBitsFromSent_run STARTA sA c.prem
        (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) w3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) hw3SA hw3Z hw3SCAN
    have hWREG4 : (State.get ((emitBitsFromSent STARTA).eval w3) WREG).length ≤ Ω :=
      emitBitsFromSent_WREG STARTA w3 Ω (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hw3W
        (by rw [hw3SA, List.length_replicate, hw3SCAN] at *
            rw [hw3SCAN] at hw3SCANlen
            omega)
    set w4 := (emitBitsFromSent STARTA).eval w3 with hw4
    have hw4SB : State.get w4 STARTB = List.replicate sB 1 := by
      rw [hw4, h4frame STARTB (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
      exact hw3SB
    have hw4SCAN : State.get w4 SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST := by
      rw [hw4]; exact h4SCAN
    have hw4Z : State.get w4 ZERO = [] := by rw [hw4]; exact h4Z
    have hw4OUT : State.get w4 OUT
        = State.get w3 OUT ++ serF (encodeBitsAt sA c.prem) := by
      rw [hw4]; exact h4OUT
    have hw4W : (State.get w4 WREG).length ≤ Ω := by rw [hw4]; exact hWREG4
    have hw4SCANlen : (State.get w4 SCAN).length
        ≤ (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length := by
      rw [hw4SCAN]
      have : (State.get w3 SCAN).length
          = (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)).length
            + (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST).length := by
        rw [hw3SCAN, List.length_append]
      omega
    clear_value w4
    -- the conc emitter: cost
    have hcostB := emitBitsFromSent_cost STARTB sB c.conc REST w4 Ω
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hw4SB hw4Z hw4SCAN
      (by rw [hw4OUT, hw3OUTfull]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)
      hw4W
      (by rw [hw4SCAN] at hw4SCANlen ⊢
          omega)
    -- WREG at exit
    have hWREG5 : (State.get ((emitBitsFromSent STARTB).eval w4) WREG).length ≤ Ω :=
      emitBitsFromSent_WREG STARTB w4 Ω (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hw4W
        (by rw [hw4SB, List.length_replicate]
            rw [hw4SCAN] at hw4SCANlen
            rw [hw4SCAN]
            omega)
    -- assemble cost and eval
    have hcost : cardEmitBody.cost w
        = 1 + 1 + (1 + (1 + 3 + (1 + 3 + (1 + (emitBitsFromSent STARTA).cost w3
            + (emitBitsFromSent STARTB).cost w4)))) := by
      show (Cmd.op (.nonEmpty TFLG SCAN) ;; _).cost w = _
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_true _ _ _ _ hw1T,
        Cmd.cost_seq, emitForrTag_cost, ← hw2, Cmd.cost_seq, emitFandTag_cost,
        ← hw3, Cmd.cost_seq, ← hw4]
      simp only [Op.cost]
    have heval : cardEmitBody.eval w = (emitBitsFromSent STARTB).eval w4 := by
      unfold cardEmitBody
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_true _ _ _ _ hw1T, Cmd.eval_seq, ← hw2,
        Cmd.eval_seq, ← hw3, Cmd.eval_seq, ← hw4]
    constructor
    · rw [hcost]
      set KK := (Cmd.flatK (sentBitBody 0) + 8) * ((Ω + 1) * (Ω + 1)) with hKK
      clear_value KK
      omega
    · rw [heval]
      exact hWREG5
  · -- idle iteration
    have hlen : C.cards.length ≤ j := Nat.le_of_not_lt hj
    have hSCANw : State.get w SCAN = [] := by
      rw [hwSCAN, List.drop_eq_nil_of_le hlen]
      rfl
    have hne : (State.get w SCAN).isEmpty = true := by rw [hSCANw]; rfl
    have e1 : (Cmd.op (.nonEmpty TFLG SCAN)).eval w = w.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    have hw1T : State.get (w.set TFLG [0]) TFLG ≠ [1] := by
      rw [State.get_set_eq]; decide
    constructor
    · have hcost : cardEmitBody.cost w = 1 + 1 + (1 + 1) := by
        show (Cmd.op (.nonEmpty TFLG SCAN) ;; _).cost w = _
        rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_false _ _ _ _ hw1T,
          Cmd.cost_op]
        simp only [Op.cost]
      rw [hcost]
      omega
    · have heval : cardEmitBody.eval w = (w.set TFLG [0]).set KTMP [] := by
        unfold cardEmitBody
        rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_false _ _ _ _ hw1T, Cmd.eval_op]
        simp only [Op.eval]
      rw [heval, State.get_set_ne _ _ _ _ (show WREG ≠ KTMP by decide),
        State.get_set_ne _ _ _ _ (show WREG ≠ TFLG by decide)]
      exact hwW

/-- **`emitCardsAt` cost**: cubic in the ceiling `Ω`. -/
theorem emitCardsAt_cost (sA sB : Nat) (C : BinaryCC) (u : State) (Ω : Nat)
    (hSA : State.get u STARTA = List.replicate sA 1)
    (hSB : State.get u STARTB = List.replicate sB 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length + (serF (encodeCardsAt C sA sB)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩA : sA + (State.get u CARDS).length ≤ Ω)
    (hΩB : sB + (State.get u CARDS).length ≤ Ω) :
    emitCardsAt.cost u
      ≤ (2 * Cmd.flatK (sentBitBody 0) + 44)
          * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) := by
  have heq : emitCardsAt = (Cmd.op (.copy SCAN CARDS) ;;
      (Cmd.forBnd KCARD CARDS cardEmitBody ;; emitFalse)) := rfl
  rw [heq, Cmd.cost_seq, Cmd.cost_seq, emitFalse_cost, Cmd.cost_op]
  simp only [Op.cost]
  have e0 : (Cmd.op (.copy SCAN CARDS)).eval u
      = u.set SCAN (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hCARDS]
  rw [e0]
  set u1 := u.set SCAN (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    with hu1
  have hu1f : ∀ r : Var, r ≠ SCAN → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1SC : State.get u1 SCAN
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    State.get_set_eq _ _ _
  have hu1CARDSlen : (State.get u1 CARDS).length = (State.get u CARDS).length := by
    rw [hu1f CARDS (by decide)]
  clear_value u1
  have hcards_le : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length
      = (State.get u CARDS).length := by rw [hCARDS]
  have hloop := Cmd.cost_forBnd_le KCARD CARDS cardEmitBody u1
    (12 + 2 * ((Cmd.flatK (sentBitBody 0) + 8) * ((Ω + 1) * (Ω + 1))))
    (fun j st => CAInv sA sB C.cards u1 j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨by rw [List.drop_zero]; exact hu1SC,
      by rw [List.take_zero]; simp [cardsPrefix],
      by rw [hu1f ZERO (by decide)]; exact hZ,
      fun r _ _ _ _ _ _ _ _ _ _ => rfl⟩,
      by rw [hu1f WREG (by decide)]; exact hΩW⟩
    (fun j st hj hM => by
      refine ⟨CAInv_step sA sB C.cards u1
        (by rw [hu1f STARTA (by decide)]; exact hSA)
        (by rw [hu1f STARTB (by decide)]; exact hSB) j st hM.1, ?_⟩
      exact (cardEmitBody_effect sA sB C u1 Ω
        (by rw [hu1f STARTA (by decide)]; exact hSA)
        (by rw [hu1f STARTB (by decide)]; exact hSB)
        (by rw [hu1f OUT (by decide)]; exact hΩO)
        (by rw [← hcards_le] at hΩA; exact hΩA)
        (by rw [← hcards_le] at hΩB; exact hΩB)
        j st hM.1 hM.2).2)
    (fun j st hj hM =>
      (cardEmitBody_effect sA sB C u1 Ω
        (by rw [hu1f STARTA (by decide)]; exact hSA)
        (by rw [hu1f STARTB (by decide)]; exact hSB)
        (by rw [hu1f OUT (by decide)]; exact hΩO)
        (by rw [← hcards_le] at hΩA; exact hΩA)
        (by rw [← hcards_le] at hΩB; exact hΩB)
        j st hM.1 hM.2).1)
  -- close the arithmetic
  have hΩcards : (State.get u CARDS).length ≤ Ω := by omega
  set K := Cmd.flatK (sentBitBody 0) with hK
  set len := (State.get u1 CARDS).length with hlenDef
  have hlenΩ : len ≤ Ω := by omega
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  set B := 12 + 2 * ((K + 8) * P2) with hB
  have hBle : B ≤ (2 * K + 28) * P2 := by
    rw [hB]
    have h12 : 12 ≤ 12 * P2 := by
      have : 1 ≤ P2 := by rw [hP2]; nlinarith
      omega
    have hexp2 : 2 * ((K + 8) * P2) + 12 * P2 = (2 * K + 28) * P2 := by ring
    omega
  have hlB : len * B ≤ (Ω + 1) * ((2 * K + 28) * P2) :=
    Nat.mul_le_mul (by omega) hBle
  have h3 : (Ω + 1) * ((2 * K + 28) * P2) = (2 * K + 28) * ((Ω + 1) * P2) := by ring
  have h2 : len * len ≤ Ω * Ω := Nat.mul_le_mul hlenΩ hlenΩ
  have h4 : (2 * K + 44) * ((Ω + 1) * P2)
      = (2 * K + 28) * ((Ω + 1) * P2) + 16 * ((Ω + 1) * P2) := by ring
  have h5 : (Ω + 1) * P2 = Ω * Ω * Ω + 3 * (Ω * Ω) + 3 * Ω + 1 := by
    rw [hP2]; ring
  have h6 : Ω * Ω * Ω + 3 * (Ω * Ω) + 3 * Ω + 1 ≥ Ω * Ω + Ω + 1 := by nlinarith
  have hcopy : (State.get u CARDS).length + 1 ≤ Ω + 1 := by omega
  omega

/-! ### `stepBody`: cost -/

private theorem one_le_P (Ω : Nat) : 1 ≤ (Ω + 1) * (Ω + 1) :=
  Nat.mul_pos (Nat.succ_pos Ω) (Nat.succ_pos Ω)

private theorem le_scale (Ω x : Nat) : x ≤ (Ω + 1) * x :=
  Nat.le_mul_of_pos_left x (Nat.succ_pos Ω)

private theorem mulLoopClose (k m Ω : Nat) (hk : k ≤ Ω) (hm : m ≤ Ω) (hmk : m * k ≤ Ω) :
    1 + m * (2 * (0 + m * k + k) + 1) + m * m ≤ 7 * ((Ω + 1) * (Ω + 1)) := by
  nlinarith

private theorem subLoopClose (a m Ω : Nat) (ha : a ≤ Ω) (hm : m ≤ Ω) :
    1 + m * (a + 1) + m * m ≤ 3 * ((Ω + 1) * (Ω + 1)) := by
  nlinarith

/-- `emitCardsAt` keeps `WREG ≤ Ω` (loop-exit version of the per-iteration
clause in `cardEmitBody_effect`). -/
private theorem emitCardsAt_WREG (sA sB : Nat) (C : BinaryCC) (u : State) (Ω : Nat)
    (hSA : State.get u STARTA = List.replicate sA 1)
    (hSB : State.get u STARTB = List.replicate sB 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length + (serF (encodeCardsAt C sA sB)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩA : sA + (State.get u CARDS).length ≤ Ω)
    (hΩB : sB + (State.get u CARDS).length ≤ Ω) :
    (State.get (emitCardsAt.eval u) WREG).length ≤ Ω := by
  have heq : emitCardsAt = (Cmd.op (.copy SCAN CARDS) ;;
      (Cmd.forBnd KCARD CARDS cardEmitBody ;; emitFalse)) := rfl
  rw [heq, Cmd.eval_seq, Cmd.eval_seq, emitFalse_frame _ WREG (by decide)]
  have e0 : (Cmd.op (.copy SCAN CARDS)).eval u
      = u.set SCAN (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hCARDS]
  rw [e0]
  set u1 := u.set SCAN (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    with hu1
  have hu1f : ∀ r : Var, r ≠ SCAN → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1SC : State.get u1 SCAN
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    State.get_set_eq _ _ _
  have hcards_le : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length
      = (State.get u CARDS).length := by rw [hCARDS]
  clear_value u1
  rw [Cmd.eval_forBnd]
  have hInv := Cmd.foldlState_range_induct cardEmitBody KCARD
    (State.get u1 CARDS).length u1
    (fun j st => CAInv sA sB C.cards u1 j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨by rw [List.drop_zero]; exact hu1SC,
      by rw [List.take_zero]; simp [cardsPrefix],
      by rw [hu1f ZERO (by decide)]; exact hZ,
      fun r _ _ _ _ _ _ _ _ _ _ => rfl⟩,
      by rw [hu1f WREG (by decide)]; exact hΩW⟩
    (fun j st hj hM => by
      refine ⟨CAInv_step sA sB C.cards u1
        (by rw [hu1f STARTA (by decide)]; exact hSA)
        (by rw [hu1f STARTB (by decide)]; exact hSB) j st hM.1, ?_⟩
      exact (cardEmitBody_effect sA sB C u1 Ω
        (by rw [hu1f STARTA (by decide)]; exact hSA)
        (by rw [hu1f STARTB (by decide)]; exact hSB)
        (by rw [hu1f OUT (by decide)]; exact hΩO)
        (by rw [← hcards_le] at hΩA; exact hΩA)
        (by rw [← hcards_le] at hΩB; exact hΩB)
        j st hM.1 hM.2).2)
  exact hInv.2

/-- **`stepBody` cost**: cubic in the ceiling `Ω`, plus the `WREG ≤ Ω` exit
fact the enclosing loop needs. -/
theorem stepBody_cost (C : BinaryCC) (line step : Nat) (u : State) (Ω : Nat)
    (hLINEL : State.get u LINEL = List.replicate (line * C.init.length) 1)
    (hKSTEP : State.get u KSTEP = List.replicate step 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hWID : State.get u WIDTH = List.replicate C.width 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length
        + (serF (encodeStepConstraint C line step)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩidx : (line + 1) * C.init.length + step * C.offset + step + C.offset
        + C.width + C.init.length + (State.get u CARDS).length ≤ Ω) :
    stepBody.cost u
        ≤ (2 * Cmd.flatK (sentBitBody 0) + 100) * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))
    ∧ (State.get (stepBody.eval u) WREG).length ≤ Ω := by
  -- index arithmetic, upfront
  have hsucc : (line + 1) * C.init.length
      = line * C.init.length + C.init.length := by ring
  have hlineL : line * C.init.length + step * C.offset ≤ Ω := by
    rw [hsucc] at hΩidx; omega
  -- w1: clear STEPO
  have e1 : (Cmd.op (.clear STEPO)).eval u = u.set STEPO [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w1 := u.set STEPO [] with hw1
  have hw1frame : ∀ r : Var, r ≠ STEPO → State.get w1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1STEPO : State.get w1 STEPO = [] := State.get_set_eq _ _ _
  have hw1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hw1frame OFFSET (by decide)]; exact hOFF
  have hw1KSTEPlen : (State.get w1 KSTEP).length = step := by
    rw [hw1frame KSTEP (by decide), hKSTEP, List.length_replicate]
  clear_value w1
  -- w2: the STEPO mul loop (run + cost)
  have hcMul := cost_mulLoop_le KTMP KSTEP STEPO OFFSET w1 0 C.offset step
    (by decide) (by decide) (by decide)
    (by rw [hw1STEPO]; exact Nat.le_refl 0)
    (by rw [hw1OFF, List.length_replicate])
    hw1KSTEPlen
  obtain ⟨h2STEPO, h2frame⟩ :=
    unaryMulLoop_run KTMP KSTEP OFFSET STEPO w1 C.offset step
      (by decide) (by decide) (by decide) hw1OFF hw1KSTEPlen hw1STEPO
  set w2 := (Cmd.forBnd KTMP KSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).eval w1
    with hw2
  clear_value w2
  have hw2LINEL : State.get w2 LINEL = List.replicate (line * C.init.length) 1 := by
    rw [h2frame LINEL (by decide) (by decide), hw1frame LINEL (by decide)]
    exact hLINEL
  -- w3: STARTA := LINEL ++ STEPO
  have e3 : (Cmd.op (.concat STARTA LINEL STEPO)).eval w2
      = w2.set STARTA (List.replicate (line * C.init.length + step * C.offset) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hw2LINEL, h2STEPO]
    congr 1
    rw [List.replicate_add]
  have hc3 : Op.cost (.concat STARTA LINEL STEPO) w2
      = 2 * (line * C.init.length + step * C.offset) + 1 := by
    show 2 * ((State.get w2 LINEL).length + (State.get w2 STEPO).length) + 1 = _
    rw [hw2LINEL, h2STEPO, List.length_replicate, List.length_replicate]
  set w3 := w2.set STARTA (List.replicate (line * C.init.length + step * C.offset) 1)
    with hw3
  have hw3frame : ∀ r : Var, r ≠ STARTA → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3SA : State.get w3 STARTA
      = List.replicate (line * C.init.length + step * C.offset) 1 :=
    State.get_set_eq _ _ _
  have hw3LREG : State.get w3 LREG = List.replicate C.init.length 1 := by
    rw [hw3frame LREG (by decide), h2frame LREG (by decide) (by decide),
      hw1frame LREG (by decide)]
    exact hLREG
  clear_value w3
  -- w4: STARTB := STARTA ++ LREG
  have e4 : (Cmd.op (.concat STARTB STARTA LREG)).eval w3
      = w3.set STARTB (List.replicate
          (line * C.init.length + step * C.offset + C.init.length) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hw3SA, hw3LREG]
    congr 1
    rw [← List.replicate_add]
  have hc4 : Op.cost (.concat STARTB STARTA LREG) w3
      = 2 * (line * C.init.length + step * C.offset + C.init.length) + 1 := by
    show 2 * ((State.get w3 STARTA).length + (State.get w3 LREG).length) + 1 = _
    rw [hw3SA, hw3LREG, List.length_replicate, List.length_replicate]
  set w4 := w3.set STARTB (List.replicate
      (line * C.init.length + step * C.offset + C.init.length) 1) with hw4
  have hw4frame : ∀ r : Var, r ≠ STARTB → State.get w4 r = State.get w3 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw4SB : State.get w4 STARTB
      = List.replicate (line * C.init.length + step * C.offset + C.init.length) 1 :=
    State.get_set_eq _ _ _
  have hw4STEPO : State.get w4 STEPO = List.replicate (step * C.offset) 1 := by
    rw [hw4frame STEPO (by decide), hw3frame STEPO (by decide)]; exact h2STEPO
  have hw4WID : State.get w4 WIDTH = List.replicate C.width 1 := by
    rw [hw4frame WIDTH (by decide), hw3frame WIDTH (by decide),
      h2frame WIDTH (by decide) (by decide), hw1frame WIDTH (by decide)]
    exact hWID
  clear_value w4
  -- w5: SUMW := STEPO ++ WIDTH
  have e5 : (Cmd.op (.concat SUMW STEPO WIDTH)).eval w4
      = w4.set SUMW (List.replicate (step * C.offset + C.width) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hw4STEPO, hw4WID]
    congr 1
    rw [List.replicate_add]
  have hc5 : Op.cost (.concat SUMW STEPO WIDTH) w4
      = 2 * (step * C.offset + C.width) + 1 := by
    show 2 * ((State.get w4 STEPO).length + (State.get w4 WIDTH).length) + 1 = _
    rw [hw4STEPO, hw4WID, List.length_replicate, List.length_replicate]
  set w5 := w4.set SUMW (List.replicate (step * C.offset + C.width) 1) with hw5
  have hw5frame : ∀ r : Var, r ≠ SUMW → State.get w5 r = State.get w4 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw5SUMW : State.get w5 SUMW = List.replicate (step * C.offset + C.width) 1 :=
    State.get_set_eq _ _ _
  clear_value w5
  -- w6: REM := copy SUMW
  have e6 : (Cmd.op (.copy REM SUMW)).eval w5
      = w5.set REM (List.replicate (step * C.offset + C.width) 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw5SUMW]
  have hc6 : Op.cost (.copy REM SUMW) w5 = step * C.offset + C.width + 1 := by
    show (State.get w5 SUMW).length + 1 = _
    rw [hw5SUMW, List.length_replicate]
  set w6 := w5.set REM (List.replicate (step * C.offset + C.width) 1) with hw6
  have hw6frame : ∀ r : Var, r ≠ REM → State.get w6 r = State.get w5 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw6REM : State.get w6 REM = List.replicate (step * C.offset + C.width) 1 :=
    State.get_set_eq _ _ _
  have hw6LREGlen : (State.get w6 LREG).length = C.init.length := by
    rw [hw6frame LREG (by decide), hw5frame LREG (by decide),
      hw4frame LREG (by decide), hw3LREG, List.length_replicate]
  clear_value w6
  -- w7: the truncated-subtraction loop (run + cost)
  have hcSub := cost_tailLoop_le KTMP LREG REM w6 (step * C.offset + C.width)
    C.init.length (by decide)
    (by rw [hw6REM, List.length_replicate]) hw6LREGlen
  obtain ⟨h7REM, h7frame⟩ :=
    unarySubLoop_run KTMP LREG REM w6 (step * C.offset + C.width) C.init.length
      (by decide) hw6LREGlen hw6REM
  set w7 := (Cmd.forBnd KTMP LREG (Cmd.op (.tail REM REM))).eval w6 with hw7
  clear_value w7
  have h7chain : ∀ r : Var, r ≠ STEPO → r ≠ KTMP → r ≠ STARTA → r ≠ STARTB →
      r ≠ SUMW → r ≠ REM → State.get w7 r = State.get u r := by
    intro r h1 h2 h3 h4 h5 h6
    rw [h7frame r h6 h2, hw6frame r h6, hw5frame r h5, hw4frame r h4,
      hw3frame r h3, h2frame r h1 h2, hw1frame r h1]
  have h7OUT : State.get w7 OUT = State.get u OUT :=
    h7chain OUT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h7Z : State.get w7 ZERO = [] := by
    rw [h7chain ZERO (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hZ
  have h7CARDS : State.get w7 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [h7chain CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hCARDS
  have h7CARDSlen : (State.get w7 CARDS).length = (State.get u CARDS).length := by
    rw [h7chain CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  have h7WREG : State.get w7 WREG = State.get u WREG :=
    h7chain WREG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h7SA : State.get w7 STARTA
      = List.replicate (line * C.init.length + step * C.offset) 1 := by
    rw [h7frame STARTA (by decide) (by decide), hw6frame STARTA (by decide),
      hw5frame STARTA (by decide), hw4frame STARTA (by decide)]
    exact hw3SA
  have h7SB : State.get w7 STARTB
      = List.replicate (line * C.init.length + step * C.offset + C.init.length) 1 := by
    rw [h7frame STARTB (by decide) (by decide), hw6frame STARTB (by decide),
      hw5frame STARTB (by decide)]
    exact hw4SB
  by_cases hguard : step * C.offset + C.width ≤ C.init.length
  · -- guard passes → emitCardsAt
    have hREM0 : State.get w7 REM = [] := by
      rw [h7REM, Nat.sub_eq_zero_of_le hguard]
      rfl
    have hne : (State.get w7 REM).isEmpty = true := by rw [hREM0]; rfl
    have e8 : (Cmd.op (.nonEmpty TFLG REM)).eval w7 = w7.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w8 := w7.set TFLG [0] with hw8
    have hw8frame : ∀ r : Var, r ≠ TFLG → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8Tne : State.get w8 TFLG ≠ [1] := by
      rw [hw8, State.get_set_eq]; decide
    clear_value w8
    have ec : (Cmd.op (.clear GFLG)).eval w8 = w8.set GFLG [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    have ea : (Cmd.op (.appendOne GFLG)).eval (w8.set GFLG []) = w8.set GFLG [1] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, State.set_set, List.nil_append]
    have e9 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w8
        = w8.set GFLG [1] := by
      rw [Cmd.eval_ifBit_false _ _ _ _ hw8Tne, Cmd.eval_seq, ec, ea]
    have hc9 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).cost w8 = 4 := by
      rw [Cmd.cost_ifBit_false _ _ _ _ hw8Tne, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op,
        ec]
      simp only [Op.cost]
    set w9 := w8.set GFLG [1] with hw9
    have hw9frame : ∀ r : Var, r ≠ GFLG → State.get w9 r = State.get w8 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw9G : State.get w9 GFLG = [1] := State.get_set_eq _ _ _
    clear_value w9
    have h9SA : State.get w9 STARTA
        = List.replicate (line * C.init.length + step * C.offset) 1 := by
      rw [hw9frame STARTA (by decide), hw8frame STARTA (by decide)]; exact h7SA
    have h9SB : State.get w9 STARTB
        = List.replicate (line * C.init.length + step * C.offset + C.init.length) 1 := by
      rw [hw9frame STARTB (by decide), hw8frame STARTB (by decide)]; exact h7SB
    have h9CARDS : State.get w9 CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
      rw [hw9frame CARDS (by decide), hw8frame CARDS (by decide)]; exact h7CARDS
    have h9CARDSlen : (State.get w9 CARDS).length = (State.get u CARDS).length := by
      rw [hw9frame CARDS (by decide), hw8frame CARDS (by decide)]; exact h7CARDSlen
    have h9Z : State.get w9 ZERO = [] := by
      rw [hw9frame ZERO (by decide), hw8frame ZERO (by decide)]; exact h7Z
    have h9OUT : State.get w9 OUT = State.get u OUT := by
      rw [hw9frame OUT (by decide), hw8frame OUT (by decide)]; exact h7OUT
    have h9WREG : State.get w9 WREG = State.get u WREG := by
      rw [hw9frame WREG (by decide), hw8frame WREG (by decide)]; exact h7WREG
    have hstep : encodeStepConstraint C line step
        = encodeCardsAt C (line * C.init.length + step * C.offset)
            (line * C.init.length + step * C.offset + C.init.length) := by
      unfold encodeStepConstraint
      rw [dif_pos hguard]
      congr 1
      rw [Nat.succ_mul]
      omega
    have hΩO9 : (State.get w9 OUT).length
        + (serF (encodeCardsAt C (line * C.init.length + step * C.offset)
            (line * C.init.length + step * C.offset + C.init.length))).length ≤ Ω := by
      rw [h9OUT, ← hstep]
      exact hΩO
    have hΩW9 : (State.get w9 WREG).length ≤ Ω := by rw [h9WREG]; exact hΩW
    have hΩA9 : line * C.init.length + step * C.offset
        + (State.get w9 CARDS).length ≤ Ω := by
      rw [h9CARDSlen]
      rw [hsucc] at hΩidx
      omega
    have hΩB9 : line * C.init.length + step * C.offset + C.init.length
        + (State.get w9 CARDS).length ≤ Ω := by
      rw [h9CARDSlen]
      rw [hsucc] at hΩidx
      omega
    have hcCA := emitCardsAt_cost (line * C.init.length + step * C.offset)
      (line * C.init.length + step * C.offset + C.init.length) C w9 Ω
      h9SA h9SB h9CARDS h9Z hΩO9 hΩW9 hΩA9 hΩB9
    have hWCA := emitCardsAt_WREG (line * C.init.length + step * C.offset)
      (line * C.init.length + step * C.offset + C.init.length) C w9 Ω
      h9SA h9SB h9CARDS h9Z hΩO9 hΩW9 hΩA9 hΩB9
    -- assemble
    have hcost : stepBody.cost u
        = 1 + 1 + (1 + (Cmd.forBnd KTMP KSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).cost w1
          + (1 + Op.cost (.concat STARTA LINEL STEPO) w2
          + (1 + Op.cost (.concat STARTB STARTA LREG) w3
          + (1 + Op.cost (.concat SUMW STEPO WIDTH) w4
          + (1 + Op.cost (.copy REM SUMW) w5
          + (1 + (Cmd.forBnd KTMP LREG (Cmd.op (.tail REM REM))).cost w6
          + (1 + 1
          + (1 + 4
          + (1 + emitCardsAt.cost w9))))))))) := by
      unfold stepBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq,
        Cmd.cost_op, e3, Cmd.cost_seq, Cmd.cost_op, e4, Cmd.cost_seq, Cmd.cost_op,
        e5, Cmd.cost_seq, Cmd.cost_op, e6, Cmd.cost_seq, ← hw7, Cmd.cost_seq,
        Cmd.cost_op, e8, Cmd.cost_seq, hc9, e9, Cmd.cost_ifBit_true _ _ _ _ hw9G]
      simp only [Op.cost]
    have heval : stepBody.eval u = emitCardsAt.eval w9 := by
      unfold stepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, ← hw7, Cmd.eval_seq, e8,
        Cmd.eval_seq, e9, Cmd.eval_ifBit_true _ _ _ _ hw9G]
    constructor
    · rw [hcost, hc3, hc4, hc5, hc6]
      -- collapse everything against the ceiling
      have hoff : C.offset ≤ Ω := by omega
      have hsteple : step ≤ Ω := by omega
      have hso : step * C.offset ≤ Ω := by omega
      have hwid : C.width ≤ Ω := by omega
      have hL : C.init.length ≤ Ω := by omega
      have hsb : line * C.init.length + step * C.offset + C.init.length ≤ Ω := by
        rw [hsucc] at hΩidx
        omega
      have hMulle := le_trans hcMul (mulLoopClose C.offset step Ω hoff hsteple hso)
      have hSuble := le_trans hcSub
        (subLoopClose (step * C.offset + C.width) C.init.length Ω (by omega) hL)
      set K := Cmd.flatK (sentBitBody 0) with hK
      set P2 := (Ω + 1) * (Ω + 1) with hP2
      set P3 := (Ω + 1) * P2 with hP3
      have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
      have hP23 : P2 ≤ P3 := by
        rw [hP3]
        exact Nat.le_mul_of_pos_left P2 (by omega)
      have hcCA' : emitCardsAt.cost w9 ≤ (2 * K + 44) * P3 := hcCA
      have h44_100 : (2 * K + 44) * P3 + 56 * P3 = (2 * K + 100) * P3 := by ring
      omega
    · rw [heval]
      exact hWCA
  · -- guard fails → emitFtrue
    obtain ⟨k, hk⟩ : ∃ k, step * C.offset + C.width - C.init.length = k + 1 :=
      ⟨step * C.offset + C.width - C.init.length - 1, by omega⟩
    have hne : (State.get w7 REM).isEmpty = false := by
      rw [h7REM, hk]
      rfl
    have e8 : (Cmd.op (.nonEmpty TFLG REM)).eval w7 = w7.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w8 := w7.set TFLG [1] with hw8
    have hw8frame : ∀ r : Var, r ≠ TFLG → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8T : State.get w8 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w8
    have e9 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w8
        = w8.set GFLG [] := by
      rw [Cmd.eval_ifBit_true _ _ _ _ hw8T, Cmd.eval_op]
      simp only [Op.eval]
    have hc9 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).cost w8 = 2 := by
      rw [Cmd.cost_ifBit_true _ _ _ _ hw8T, Cmd.cost_op]
      simp only [Op.cost]
    set w9 := w8.set GFLG [] with hw9
    have hw9frame : ∀ r : Var, r ≠ GFLG → State.get w9 r = State.get w8 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw9Gne : State.get w9 GFLG ≠ [1] := by
      rw [hw9, State.get_set_eq]; decide
    clear_value w9
    have h9WREG : State.get w9 WREG = State.get u WREG := by
      rw [hw9frame WREG (by decide), hw8frame WREG (by decide)]; exact h7WREG
    have hcost : stepBody.cost u
        = 1 + 1 + (1 + (Cmd.forBnd KTMP KSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).cost w1
          + (1 + Op.cost (.concat STARTA LINEL STEPO) w2
          + (1 + Op.cost (.concat STARTB STARTA LREG) w3
          + (1 + Op.cost (.concat SUMW STEPO WIDTH) w4
          + (1 + Op.cost (.copy REM SUMW) w5
          + (1 + (Cmd.forBnd KTMP LREG (Cmd.op (.tail REM REM))).cost w6
          + (1 + 1
          + (1 + 2
          + (1 + 3))))))))) := by
      unfold stepBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq,
        Cmd.cost_op, e3, Cmd.cost_seq, Cmd.cost_op, e4, Cmd.cost_seq, Cmd.cost_op,
        e5, Cmd.cost_seq, Cmd.cost_op, e6, Cmd.cost_seq, ← hw7, Cmd.cost_seq,
        Cmd.cost_op, e8, Cmd.cost_seq, hc9, e9, Cmd.cost_ifBit_false _ _ _ _ hw9Gne,
        emitFtrue_cost]
      simp only [Op.cost]
    have heval : stepBody.eval u = emitFtrue.eval w9 := by
      unfold stepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, ← hw7, Cmd.eval_seq, e8,
        Cmd.eval_seq, e9, Cmd.eval_ifBit_false _ _ _ _ hw9Gne]
    constructor
    · rw [hcost, hc3, hc4, hc5, hc6]
      have hoff : C.offset ≤ Ω := by omega
      have hsteple : step ≤ Ω := by omega
      have hso : step * C.offset ≤ Ω := by omega
      have hwid : C.width ≤ Ω := by omega
      have hL : C.init.length ≤ Ω := by omega
      have hsb : line * C.init.length + step * C.offset + C.init.length ≤ Ω := by
        rw [hsucc] at hΩidx
        omega
      have hMulle := le_trans hcMul (mulLoopClose C.offset step Ω hoff hsteple hso)
      have hSuble := le_trans hcSub
        (subLoopClose (step * C.offset + C.width) C.init.length Ω (by omega) hL)
      set K := Cmd.flatK (sentBitBody 0) with hK
      set P2 := (Ω + 1) * (Ω + 1) with hP2
      set P3 := (Ω + 1) * P2 with hP3
      have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
      have hP23 : P2 ≤ P3 := by
        rw [hP3]
        exact Nat.le_mul_of_pos_left P2 (by omega)
      have hKP3 : 0 ≤ (2 * K + 44) * P3 := Nat.zero_le _
      have h44_100 : (2 * K + 44) * P3 + 56 * P3 = (2 * K + 100) * P3 := by ring
      omega
    · rw [heval, emitFtrue_frame _ WREG (by decide), h9WREG]
      exact hΩW

/-! ### `emitAllSteps`: cost -/

private theorem andPrefix_range_succ (g : Nat → formula) (n : Nat) :
    andPrefix ((List.range (n + 1)).map g)
      = andPrefix ((List.range n).map g) ++ ([0, 1] ++ serF (g n)) := by
  rw [List.range_succ, List.map_append, andPrefix_append]
  simp [andPrefix]

private theorem andPrefix_range_le (g : Nat → formula) (k m : Nat) (h : k ≤ m) :
    (andPrefix ((List.range k).map g)).length
      ≤ (serF (listAnd ((List.range m).map g))).length := by
  have he : (List.range k).map g = ((List.range m).map g).take k := by
    rw [← List.map_take, List.take_range, Nat.min_eq_left h]
  rw [he]
  exact andPrefix_take_length_le _ k

/-- Per-iteration effect of the inner step loop: cost + `WREG ≤ Ω`.
`u3` is the inner loop's entry state (`LINEL` freshly rebuilt). -/
private theorem stepIterBody_effect (C : BinaryCC) (line : Nat) (u3 : State) (Ω : Nat)
    (hLINEL : State.get u3 LINEL = List.replicate (line * C.init.length) 1)
    (hOFF : State.get u3 OFFSET = List.replicate C.offset 1)
    (hWID : State.get u3 WIDTH = List.replicate C.width 1)
    (hLREG : State.get u3 LREG = List.replicate C.init.length 1)
    (hCARDS : State.get u3 CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hΩOL : (State.get u3 OUT).length
        + (serF (encodeLineConstraints C line)).length ≤ Ω)
    (hΩidxL : (line + 1) * C.init.length + C.init.length * C.offset
        + C.init.length + C.offset + C.width + C.init.length
        + (State.get u3 CARDS).length ≤ Ω)
    (i : Nat) (hi : i < C.init.length + 1) (st : State)
    (hInv : ASInv C line u3 i st) (hW : (State.get st WREG).length ≤ Ω) :
    stepIterBody.cost (st.set KSTEP (List.replicate i 1))
        ≤ 4 + (2 * Cmd.flatK (sentBitBody 0) + 100)
            * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))
    ∧ (State.get (stepIterBody.eval (st.set KSTEP (List.replicate i 1))) WREG).length
        ≤ Ω := by
  obtain ⟨hOUT, hZ, hframe⟩ := hInv
  set w := st.set KSTEP (List.replicate i 1) with hw
  have hwframe : ∀ r : Var, r ≠ KSTEP → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwK : State.get w KSTEP = List.replicate i 1 := State.get_set_eq _ _ _
  clear_value w
  set w1 := emitFandTag.eval w with hw1
  have hw1frame : ∀ r : Var, r ≠ OUT → State.get w1 r = State.get w r := by
    intro r hr; rw [hw1]; exact emitFandTag_frame w r hr
  have hw1OUT : State.get w1 OUT = State.get w OUT ++ [0, 1] := by
    rw [hw1, emitFandTag_run]; exact State.get_set_eq _ _ _
  clear_value w1
  -- thread the stepBody entry facts to w1
  have hchain : ∀ r : Var, r ≠ OUT → r ≠ KSTEP →
      r ≠ SCAN → r ≠ WREG → r ≠ TFLG → r ≠ KBIT → r ≠ DONE → r ≠ EMARK → r ≠ ZERO →
      r ≠ KTMP → r ≠ KCARD → r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW →
      r ≠ REM → r ≠ GFLG → State.get w1 r = State.get u3 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rw [hw1frame r h1, hwframe r h2,
      hframe r h3 h1 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h2]
  have h1LINEL : State.get w1 LINEL = List.replicate (line * C.init.length) 1 := by
    rw [hchain LINEL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hLINEL
  have h1KSTEP : State.get w1 KSTEP = List.replicate i 1 := by
    rw [hw1frame KSTEP (by decide)]; exact hwK
  have h1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hchain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hOFF
  have h1WID : State.get w1 WIDTH = List.replicate C.width 1 := by
    rw [hchain WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hWID
  have h1LREG : State.get w1 LREG = List.replicate C.init.length 1 := by
    rw [hchain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hLREG
  have h1CARDS : State.get w1 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [hchain CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hCARDS
  have h1CARDSlen : (State.get w1 CARDS).length = (State.get u3 CARDS).length := by
    rw [h1CARDS, ← hCARDS]
  have h1Z : State.get w1 ZERO = [] := by
    rw [hw1frame ZERO (by decide), hwframe ZERO (by decide)]; exact hZ
  have h1W : (State.get w1 WREG).length ≤ Ω := by
    rw [hw1frame WREG (by decide), hwframe WREG (by decide)]; exact hW
  -- the OUT ceiling at w1
  have h1OUTfull : State.get w1 OUT = State.get u3 OUT
      ++ andPrefix ((List.range i).map (encodeStepConstraint C line)) ++ [0, 1] := by
    rw [hw1OUT, hwframe OUT (by decide), hOUT]
  have hΩO1 : (State.get w1 OUT).length
      + (serF (encodeStepConstraint C line i)).length ≤ Ω := by
    have hsucc := andPrefix_range_succ (encodeStepConstraint C line) i
    have hle := andPrefix_range_le (encodeStepConstraint C line) (i + 1)
      (C.init.length + 1) hi
    have hlineC : serF (encodeLineConstraints C line)
        = serF (listAnd ((List.range (C.init.length + 1)).map
            (encodeStepConstraint C line))) := rfl
    rw [hlineC] at hΩOL
    rw [h1OUTfull]
    have hlen : (andPrefix ((List.range (i + 1)).map (encodeStepConstraint C line))).length
        = (andPrefix ((List.range i).map (encodeStepConstraint C line))).length
          + (2 + (serF (encodeStepConstraint C line i)).length) := by
      rw [hsucc]
      simp [List.length_append]
      omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hΩidxi : (line + 1) * C.init.length + i * C.offset + i + C.offset
      + C.width + C.init.length + (State.get w1 CARDS).length ≤ Ω := by
    have hiL : i ≤ C.init.length := by omega
    have hio : i * C.offset ≤ C.init.length * C.offset :=
      Nat.mul_le_mul_right _ hiL
    rw [h1CARDSlen]
    omega
  have hSB := stepBody_cost C line i w1 Ω h1LINEL h1KSTEP h1OFF h1WID h1LREG
    h1CARDS h1Z hΩO1 h1W hΩidxi
  have hcost : stepIterBody.cost w = 1 + 3 + stepBody.cost w1 := by
    unfold stepIterBody
    rw [Cmd.cost_seq, emitFandTag_cost, ← hw1]
  have heval : stepIterBody.eval w = stepBody.eval w1 := by
    unfold stepIterBody
    rw [Cmd.eval_seq, ← hw1]
  constructor
  · rw [hcost]
    have h1 := hSB.1
    set B := (2 * Cmd.flatK (sentBitBody 0) + 100) * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))
      with hB
    clear_value B
    omega
  · rw [heval]
    exact hSB.2

/-- Per-iteration effect of the line loop: cost + `WREG ≤ Ω`. `u0` is the
`emitAllSteps` entry state. -/
private theorem lineBody_effect (C : BinaryCC) (u0 : State) (Ω : Nat)
    (hOFF : State.get u0 OFFSET = List.replicate C.offset 1)
    (hWID : State.get u0 WIDTH = List.replicate C.width 1)
    (hLREG : State.get u0 LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u0 LREG1 = List.replicate (C.init.length + 1) 1)
    (hCARDS : State.get u0 CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hΩO : (State.get u0 OUT).length
        + (serF (encodeAllStepConstraints C)).length ≤ Ω)
    (hΩidx : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.offset + C.width + C.init.length + C.steps
        + (State.get u0 CARDS).length ≤ Ω)
    (j : Nat) (hj : j < C.steps) (st : State)
    (hInv : ALInv C u0 j st) (hW : (State.get st WREG).length ≤ Ω) :
    lineBody.cost (st.set KLINE (List.replicate j 1))
        ≤ (2 * Cmd.flatK (sentBitBody 0) + 140)
            * ((Ω + 1) * ((Ω + 1) * ((Ω + 1) * (Ω + 1))))
    ∧ (State.get (lineBody.eval (st.set KLINE (List.replicate j 1))) WREG).length
        ≤ Ω := by
  obtain ⟨hOUT, hZ, hframe⟩ := hInv
  set w := st.set KLINE (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KLINE → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwK : State.get w KLINE = List.replicate j 1 := State.get_set_eq _ _ _
  clear_value w
  set w1 := emitFandTag.eval w with hw1
  have hw1frame : ∀ r : Var, r ≠ OUT → State.get w1 r = State.get w r := by
    intro r hr; rw [hw1]; exact emitFandTag_frame w r hr
  have hw1OUT : State.get w1 OUT = State.get w OUT ++ [0, 1] := by
    rw [hw1, emitFandTag_run]; exact State.get_set_eq _ _ _
  clear_value w1
  -- w2: clear LINEL
  have e2 : (Cmd.op (.clear LINEL)).eval w1 = w1.set LINEL [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w2 := w1.set LINEL [] with hw2
  have hw2frame : ∀ r : Var, r ≠ LINEL → State.get w2 r = State.get w1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw2LINEL : State.get w2 LINEL = [] := State.get_set_eq _ _ _
  clear_value w2
  have h2chain : ∀ r : Var, r ≠ LINEL → r ≠ OUT → r ≠ KLINE →
      r ≠ SCAN → r ≠ WREG → r ≠ TFLG → r ≠ KBIT → r ≠ DONE → r ≠ EMARK → r ≠ ZERO →
      r ≠ KTMP → r ≠ KCARD → r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW →
      r ≠ REM → r ≠ GFLG → r ≠ KSTEP → r ≠ KTMP2 →
      State.get w2 r = State.get u0 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    rw [hw2frame r h1, hw1frame r h2, hwframe r h3,
      hframe r h4 h2 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h1 h3 h20]
  have h2LREG : State.get w2 LREG = List.replicate C.init.length 1 := by
    rw [h2chain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG
  have h2KLINElen : (State.get w2 KLINE).length = j := by
    rw [hw2frame KLINE (by decide), hw1frame KLINE (by decide), hwK,
      List.length_replicate]
  -- w3: LINEL := 1^(j·L) (run + cost)
  have hcMul := cost_mulLoop_le KTMP2 KLINE LINEL LREG w2 0 C.init.length j
    (by decide) (by decide) (by decide)
    (by rw [hw2LINEL]; exact Nat.le_refl 0)
    (by rw [h2LREG, List.length_replicate])
    h2KLINElen
  obtain ⟨h3LINEL, h3frame⟩ :=
    unaryMulLoop_run KTMP2 KLINE LREG LINEL w2 C.init.length j
      (by decide) (by decide) (by decide) h2LREG h2KLINElen hw2LINEL
  set w3 := (Cmd.forBnd KTMP2 KLINE (Cmd.op (.concat LINEL LINEL LREG))).eval w2
    with hw3
  clear_value w3
  have h3LINEL' : State.get w3 LINEL = List.replicate (j * C.init.length) 1 := by
    rw [h3LINEL]
  have h3chain : ∀ r : Var, r ≠ LINEL → r ≠ KTMP2 → r ≠ OUT → r ≠ KLINE →
      r ≠ SCAN → r ≠ WREG → r ≠ TFLG → r ≠ KBIT → r ≠ DONE → r ≠ EMARK → r ≠ ZERO →
      r ≠ KTMP → r ≠ KCARD → r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW →
      r ≠ REM → r ≠ GFLG → r ≠ KSTEP →
      State.get w3 r = State.get u0 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    rw [h3frame r h1 h2,
      h2chain r h1 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h2]
  have h3OFF : State.get w3 OFFSET = List.replicate C.offset 1 := by
    rw [h3chain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hOFF
  have h3WID : State.get w3 WIDTH = List.replicate C.width 1 := by
    rw [h3chain WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hWID
  have h3LREG : State.get w3 LREG = List.replicate C.init.length 1 := by
    rw [h3frame LREG (by decide) (by decide)]
    exact h2LREG
  have h3LREG1 : State.get w3 LREG1 = List.replicate (C.init.length + 1) 1 := by
    rw [h3chain LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG1
  have h3LREG1len : (State.get w3 LREG1).length = C.init.length + 1 := by
    rw [h3LREG1, List.length_replicate]
  have h3CARDS : State.get w3 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [h3chain CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hCARDS
  have h3CARDSlen : (State.get w3 CARDS).length = (State.get u0 CARDS).length := by
    rw [h3CARDS, ← hCARDS]
  have h3Z : State.get w3 ZERO = [] := by
    rw [h3frame ZERO (by decide) (by decide), hw2frame ZERO (by decide),
      hw1frame ZERO (by decide), hwframe ZERO (by decide)]
    exact hZ
  have h3W : (State.get w3 WREG).length ≤ Ω := by
    rw [h3frame WREG (by decide) (by decide), hw2frame WREG (by decide),
      hw1frame WREG (by decide), hwframe WREG (by decide)]
    exact hW
  have h3OUT : State.get w3 OUT = State.get u0 OUT
      ++ andPrefix ((List.range j).map (encodeLineConstraints C)) ++ [0, 1] := by
    rw [h3frame OUT (by decide) (by decide), hw2frame OUT (by decide), hw1OUT,
      hwframe OUT (by decide), hOUT]
  -- the line-level OUT ceiling at w3
  have hΩOL3 : (State.get w3 OUT).length
      + (serF (encodeLineConstraints C j)).length ≤ Ω := by
    have hsucc := andPrefix_range_succ (encodeLineConstraints C) j
    have hle := andPrefix_range_le (encodeLineConstraints C) (j + 1) C.steps hj
    have hallC : serF (encodeAllStepConstraints C)
        = serF (listAnd ((List.range C.steps).map (encodeLineConstraints C))) := rfl
    rw [hallC] at hΩO
    rw [h3OUT]
    have hlen : (andPrefix ((List.range (j + 1)).map (encodeLineConstraints C))).length
        = (andPrefix ((List.range j).map (encodeLineConstraints C))).length
          + (2 + (serF (encodeLineConstraints C j)).length) := by
      rw [hsucc]
      simp [List.length_append]
      omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hΩidxL3 : (j + 1) * C.init.length + C.init.length * C.offset
      + C.init.length + C.offset + C.width + C.init.length
      + (State.get w3 CARDS).length ≤ Ω := by
    have hjs : j + 1 ≤ C.steps := hj
    have hjL : (j + 1) * C.init.length ≤ C.steps * C.init.length :=
      Nat.mul_le_mul_right _ hjs
    rw [h3CARDSlen]
    omega
  -- the inner step loop (cost + run + WREG)
  have hasBase : ASInv C j w3 0 w3 :=
    ⟨by simp [andPrefix], h3Z,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  have hcInner := Cmd.cost_forBnd_le KSTEP LREG1 stepIterBody w3
    (4 + (2 * Cmd.flatK (sentBitBody 0) + 100) * ((Ω + 1) * ((Ω + 1) * (Ω + 1))))
    (fun i stt => ASInv C j w3 i stt ∧ (State.get stt WREG).length ≤ Ω)
    ⟨hasBase, h3W⟩
    (fun i stt hi hM => by
      refine ⟨ASInv_step C j w3 h3LINEL' h3OFF h3WID h3LREG h3CARDS i stt hM.1, ?_⟩
      exact (stepIterBody_effect C j w3 Ω h3LINEL' h3OFF h3WID h3LREG h3CARDS
        hΩOL3 hΩidxL3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).2)
    (fun i stt hi hM =>
      (stepIterBody_effect C j w3 Ω h3LINEL' h3OFF h3WID h3LREG h3CARDS
        hΩOL3 hΩidxL3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).1)
  have hwInner := Cmd.foldlState_range_induct stepIterBody KSTEP
    (State.get w3 LREG1).length w3
    (fun i stt => ASInv C j w3 i stt ∧ (State.get stt WREG).length ≤ Ω)
    ⟨hasBase, h3W⟩
    (fun i stt hi hM => by
      refine ⟨ASInv_step C j w3 h3LINEL' h3OFF h3WID h3LREG h3CARDS i stt hM.1, ?_⟩
      exact (stepIterBody_effect C j w3 Ω h3LINEL' h3OFF h3WID h3LREG h3CARDS
        hΩOL3 hΩidxL3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).2)
  set w4 := (Cmd.forBnd KSTEP LREG1 stepIterBody).eval w3 with hw4
  have hw4eval : w4 = Cmd.foldlState stepIterBody KSTEP
      (List.range (State.get w3 LREG1).length) w3 := by
    rw [hw4, Cmd.eval_forBnd]
  have h4W : (State.get w4 WREG).length ≤ Ω := by
    rw [hw4eval]
    exact hwInner.2
  clear_value w4
  -- assemble lineBody
  have hcost : lineBody.cost w
      = 1 + 3 + (1 + 1
        + (1 + (Cmd.forBnd KTMP2 KLINE (Cmd.op (.concat LINEL LINEL LREG))).cost w2
        + (1 + (Cmd.forBnd KSTEP LREG1 stepIterBody).cost w3 + 3))) := by
    unfold lineBody
    rw [Cmd.cost_seq, emitFandTag_cost, ← hw1, Cmd.cost_seq, Cmd.cost_op, e2,
      Cmd.cost_seq, ← hw3, Cmd.cost_seq, ← hw4, emitFtrue_cost]
    simp only [Op.cost]
  have heval : lineBody.eval w = emitFtrue.eval w4 := by
    unfold lineBody
    rw [Cmd.eval_seq, ← hw1, Cmd.eval_seq, e2, Cmd.eval_seq, ← hw3, Cmd.eval_seq,
      ← hw4]
  constructor
  · rw [hcost]
    -- arithmetic
    have hjs : j ≤ C.steps := le_of_lt hj
    have hjL : j * C.init.length ≤ C.steps * C.init.length :=
      Nat.mul_le_mul_right _ hjs
    have hL : C.init.length ≤ Ω := by omega
    have hjΩ : j ≤ Ω := by omega
    have hjLΩ : j * C.init.length ≤ Ω := by omega
    have hMulle := le_trans hcMul (mulLoopClose C.init.length j Ω hL hjΩ hjLΩ)
    have hiters : (State.get w3 LREG1).length ≤ Ω + 1 := by
      rw [h3LREG1len]; omega
    set K := Cmd.flatK (sentBitBody 0) with hK
    clear_value K
    set P2 := (Ω + 1) * (Ω + 1) with hP2
    set P3 := (Ω + 1) * P2 with hP3
    set P4 := (Ω + 1) * P3 with hP4
    set B := 4 + (2 * K + 100) * P3 with hB
    have hBle : B ≤ (2 * K + 104) * P3 := by
      rw [hB]
      have h1P3 : 1 ≤ P3 := by
        rw [hP3, hP2]
        exact le_trans (one_le_P Ω) (Nat.mul_le_mul_left _ (le_scale Ω (Ω + 1)))
      have h4P3 : 4 + (2 * K + 100) * P3 ≤ 4 * P3 + (2 * K + 100) * P3 := by omega
      have he : 4 * P3 + (2 * K + 100) * P3 = (2 * K + 104) * P3 := by ring
      omega
    have hlB : (State.get w3 LREG1).length * B ≤ (Ω + 1) * ((2 * K + 104) * P3) :=
      Nat.mul_le_mul hiters hBle
    have he4 : (Ω + 1) * ((2 * K + 104) * P3) = (2 * K + 104) * P4 := by
      rw [hP4]; ring
    have hii : (State.get w3 LREG1).length * (State.get w3 LREG1).length
        ≤ (Ω + 1) * (Ω + 1) := Nat.mul_le_mul hiters hiters
    have hP24 : P2 ≤ P4 := by
      rw [hP4, hP3]
      exact le_trans (le_scale Ω P2) (Nat.mul_le_mul_left _ (le_scale Ω P2))
    have hfin : (2 * K + 140) * P4 = (2 * K + 104) * P4 + 36 * P4 := by ring
    have h1P4 : 1 ≤ P4 := by
      rw [hP4, hP3, hP2]
      exact Nat.mul_pos (Nat.succ_pos Ω) (Nat.mul_pos (Nat.succ_pos Ω)
        (Nat.mul_pos (Nat.succ_pos Ω) (Nat.succ_pos Ω)))
    omega
  · rw [heval, emitFtrue_frame _ WREG (by decide)]
    exact h4W

/-- **`emitAllSteps` cost**: quintic in the ceiling `Ω`, plus `WREG ≤ Ω` exit. -/
theorem emitAllSteps_cost (C : BinaryCC) (u : State) (Ω : Nat)
    (hSTEPS : State.get u STEPS = List.replicate C.steps 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hWID : State.get u WIDTH = List.replicate C.width 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u LREG1 = List.replicate (C.init.length + 1) 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length
        + (serF (encodeAllStepConstraints C)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩidx : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.offset + C.width + C.init.length + C.steps
        + (State.get u CARDS).length ≤ Ω) :
    emitAllSteps.cost u
        ≤ (2 * Cmd.flatK (sentBitBody 0) + 160)
            * ((Ω + 1) * ((Ω + 1) * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))))
    ∧ (State.get (emitAllSteps.eval u) WREG).length ≤ Ω := by
  have heq : emitAllSteps = (Cmd.forBnd KLINE STEPS lineBody ;; emitFtrue) := rfl
  have hSTEPSlen : (State.get u STEPS).length = C.steps := by
    rw [hSTEPS, List.length_replicate]
  have hloop := Cmd.cost_forBnd_le KLINE STEPS lineBody u
    ((2 * Cmd.flatK (sentBitBody 0) + 140)
      * ((Ω + 1) * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))))
    (fun j st => ALInv C u j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨by simp [andPrefix], hZ,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩, hΩW⟩
    (fun j st hj hM => by
      refine ⟨ALInv_step C u hOFF hWID hLREG hLREG1 hCARDS j st hM.1, ?_⟩
      exact (lineBody_effect C u Ω hOFF hWID hLREG hLREG1 hCARDS hΩO hΩidx j
        (by rw [hSTEPSlen] at hj; exact hj) st hM.1 hM.2).2)
    (fun j st hj hM =>
      (lineBody_effect C u Ω hOFF hWID hLREG hLREG1 hCARDS hΩO hΩidx j
        (by rw [hSTEPSlen] at hj; exact hj) st hM.1 hM.2).1)
  have hwLoop := Cmd.foldlState_range_induct lineBody KLINE
    (State.get u STEPS).length u
    (fun j st => ALInv C u j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨by simp [andPrefix], hZ,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩, hΩW⟩
    (fun j st hj hM => by
      refine ⟨ALInv_step C u hOFF hWID hLREG hLREG1 hCARDS j st hM.1, ?_⟩
      exact (lineBody_effect C u Ω hOFF hWID hLREG hLREG1 hCARDS hΩO hΩidx j
        (by rw [hSTEPSlen] at hj; exact hj) st hM.1 hM.2).2)
  rw [heq, Cmd.cost_seq, emitFtrue_cost]
  constructor
  · -- arithmetic
    have hsteps : C.steps ≤ Ω := by omega
    set K := Cmd.flatK (sentBitBody 0) with hK
    clear_value K
    set P2 := (Ω + 1) * (Ω + 1) with hP2
    set P3 := (Ω + 1) * P2 with hP3
    set P4 := (Ω + 1) * P3 with hP4
    set P5 := (Ω + 1) * P4 with hP5
    rw [hSTEPSlen] at hloop
    have hlB : C.steps * ((2 * K + 140) * P4) ≤ (Ω + 1) * ((2 * K + 140) * P4) :=
      Nat.mul_le_mul_right _ (by omega)
    have he5 : (Ω + 1) * ((2 * K + 140) * P4) = (2 * K + 140) * P5 := by
      rw [hP5]; ring
    have hss : C.steps * C.steps ≤ Ω * Ω := Nat.mul_le_mul hsteps hsteps
    have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
    have hP25 : P2 ≤ P5 := by
      rw [hP5, hP4, hP3]
      exact le_trans (le_scale Ω P2) (Nat.mul_le_mul_left _
        (le_trans (le_scale Ω P2) (Nat.mul_le_mul_left _ (le_scale Ω P2))))
    have hfin : (2 * K + 160) * P5 = (2 * K + 140) * P5 + 20 * P5 := by ring
    have h1P5 : 1 ≤ P5 := by
      rw [hP5, hP4, hP3, hP2]
      exact Nat.mul_pos (Nat.succ_pos Ω) (Nat.mul_pos (Nat.succ_pos Ω)
        (Nat.mul_pos (Nat.succ_pos Ω) (Nat.mul_pos (Nat.succ_pos Ω) (Nat.succ_pos Ω))))
    omega
  · rw [Cmd.eval_seq, emitFtrue_frame _ WREG (by decide), Cmd.eval_forBnd]
    exact hwLoop.2

/-! ### `emitFinal`: cost -/

private theorem orPrefix_range_succ (g : Nat → formula) (n : Nat) :
    orPrefix ((List.range (n + 1)).map g)
      = orPrefix ((List.range n).map g) ++ ([1, 0] ++ serF (g n)) := by
  rw [List.range_succ, List.map_append, orPrefix_append]
  simp [orPrefix]

private theorem orPrefix_range_le (g : Nat → formula) (k m : Nat) (h : k ≤ m) :
    (orPrefix ((List.range k).map g)).length
      ≤ (serF (listOr ((List.range m).map g))).length := by
  have he : (List.range k).map g = ((List.range m).map g).take k := by
    rw [← List.map_take, List.take_range, Nat.min_eq_left h]
  rw [he]
  exact orPrefix_take_length_le _ k

private theorem encSList_length_ge (l : List Nat) :
    l.length ≤ (FlatTCCFree.encSList l).length := by
  induction l with
  | nil => simp [FlatTCCFree.encSList]
  | cons v xs ih =>
      show _ ≤ (FlatTCCFree.encSElem v ++ FlatTCCFree.encSList xs).length
      simp only [List.length_append, List.length_cons, FlatTCCFree.encSElem,
        List.length_replicate]
      omega

/-- `emitBitsFromScan` never grows `WREG` beyond `max(entry, start + |bits|)`. -/
private theorem emitBitsFromScan_WREG (BASE bound : Nat) (u : State) (W : Nat)
    (hBT : BASE ≠ TFLG) (hBS : BASE ≠ SCAN) (hBK : BASE ≠ KBIT)
    (hBmem : BASE ∉ Cmd.writes (bsBody BASE))
    (hW : (State.get u WREG).length ≤ W)
    (hBb : (State.get u BASE).length + (State.get u bound).length ≤ W) :
    (State.get ((emitBitsFromScan BASE bound).eval u) WREG).length ≤ W := by
  rw [emitBitsFromScan_eq, Cmd.eval_seq, emitFtrue_frame _ WREG (by decide),
    Cmd.eval_forBnd]
  have hInv := Cmd.foldlState_range_induct (bsBody BASE) KBIT
    (State.get u bound).length u
    (fun i st => (State.get st WREG).length ≤ W
      ∧ State.get st BASE = State.get u BASE)
    ⟨hW, rfl⟩
    (fun i st hi hM => by
      obtain ⟨hWl, hBf⟩ := hM
      constructor
      · rw [bsBody_WREG BASE _ hBT hBS,
          State.get_set_ne _ _ _ _ hBK, State.get_set_eq, hBf,
          List.length_append, List.length_replicate]
        omega
      · rw [Cmd.eval_get_of_not_writes _ _ BASE hBmem,
          State.get_set_ne _ _ _ _ hBK]
        exact hBf)
  exact hInv.1

/-- **`finalStepBody` cost**: quadratic in `Ω`, plus the `WREG ≤ Ω` exit fact. -/
theorem finalStepBody_cost (C : BinaryCC) (step : Nat) (bits : List Bool) (u : State)
    (Ω : Nat)
    (hSTEPSL : State.get u STEPSL = List.replicate (C.steps * C.init.length) 1)
    (hKFSTEP : State.get u KFSTEP = List.replicate step 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hBLEN : State.get u BLEN = List.replicate bits.length 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hFBITS : State.get u FBITS = FlatCCBinFree.bitsNat bits)
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length
        + (serF (encodeFinalAtStep C step bits)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩidx : C.steps * C.init.length + step * C.offset + step + C.offset
        + bits.length + C.init.length ≤ Ω) :
    finalStepBody.cost u
        ≤ (Cmd.flatK (bsBody 0) + 60) * ((Ω + 1) * (Ω + 1))
    ∧ (State.get (finalStepBody.eval u) WREG).length ≤ Ω := by
  -- w1: clear STEPO
  have e1 : (Cmd.op (.clear STEPO)).eval u = u.set STEPO [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w1 := u.set STEPO [] with hw1
  have hw1frame : ∀ r : Var, r ≠ STEPO → State.get w1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1STEPO : State.get w1 STEPO = [] := State.get_set_eq _ _ _
  have hw1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hw1frame OFFSET (by decide)]; exact hOFF
  have hw1KFSTEPlen : (State.get w1 KFSTEP).length = step := by
    rw [hw1frame KFSTEP (by decide), hKFSTEP, List.length_replicate]
  clear_value w1
  -- w2: STEPO mul loop
  have hcMul := cost_mulLoop_le KTMP2 KFSTEP STEPO OFFSET w1 0 C.offset step
    (by decide) (by decide) (by decide)
    (by rw [hw1STEPO]; exact Nat.le_refl 0)
    (by rw [hw1OFF, List.length_replicate])
    hw1KFSTEPlen
  obtain ⟨h2STEPO, h2frame⟩ :=
    unaryMulLoop_run KTMP2 KFSTEP OFFSET STEPO w1 C.offset step
      (by decide) (by decide) (by decide) hw1OFF hw1KFSTEPlen hw1STEPO
  set w2 := (Cmd.forBnd KTMP2 KFSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).eval w1
    with hw2
  clear_value w2
  have hw2BLEN : State.get w2 BLEN = List.replicate bits.length 1 := by
    rw [h2frame BLEN (by decide) (by decide), hw1frame BLEN (by decide)]
    exact hBLEN
  -- w3: SUMW := STEPO ++ BLEN
  have e3 : (Cmd.op (.concat SUMW STEPO BLEN)).eval w2
      = w2.set SUMW (List.replicate (step * C.offset + bits.length) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, h2STEPO, hw2BLEN]
    congr 1
    rw [List.replicate_add]
  have hc3 : Op.cost (.concat SUMW STEPO BLEN) w2
      = 2 * (step * C.offset + bits.length) + 1 := by
    show 2 * ((State.get w2 STEPO).length + (State.get w2 BLEN).length) + 1 = _
    rw [h2STEPO, hw2BLEN, List.length_replicate, List.length_replicate]
  set w3 := w2.set SUMW (List.replicate (step * C.offset + bits.length) 1) with hw3
  have hw3frame : ∀ r : Var, r ≠ SUMW → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3SUMW : State.get w3 SUMW
      = List.replicate (step * C.offset + bits.length) 1 := State.get_set_eq _ _ _
  clear_value w3
  -- w4: REM := copy SUMW
  have e4 : (Cmd.op (.copy REM SUMW)).eval w3
      = w3.set REM (List.replicate (step * C.offset + bits.length) 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw3SUMW]
  have hc4 : Op.cost (.copy REM SUMW) w3 = step * C.offset + bits.length + 1 := by
    show (State.get w3 SUMW).length + 1 = _
    rw [hw3SUMW, List.length_replicate]
  set w4 := w3.set REM (List.replicate (step * C.offset + bits.length) 1) with hw4
  have hw4frame : ∀ r : Var, r ≠ REM → State.get w4 r = State.get w3 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw4REM : State.get w4 REM
      = List.replicate (step * C.offset + bits.length) 1 := State.get_set_eq _ _ _
  have hw4LREGlen : (State.get w4 LREG).length = C.init.length := by
    rw [hw4frame LREG (by decide), hw3frame LREG (by decide),
      h2frame LREG (by decide) (by decide), hw1frame LREG (by decide),
      hLREG, List.length_replicate]
  clear_value w4
  -- w5: the truncated-subtraction loop
  have hcSub := cost_tailLoop_le KTMP2 LREG REM w4 (step * C.offset + bits.length)
    C.init.length (by decide)
    (by rw [hw4REM, List.length_replicate]) hw4LREGlen
  obtain ⟨h5REM, h5frame⟩ :=
    unarySubLoop_run KTMP2 LREG REM w4 (step * C.offset + bits.length) C.init.length
      (by decide) hw4LREGlen hw4REM
  set w5 := (Cmd.forBnd KTMP2 LREG (Cmd.op (.tail REM REM))).eval w4 with hw5
  clear_value w5
  have h5chain : ∀ r : Var, r ≠ STEPO → r ≠ KTMP2 → r ≠ SUMW → r ≠ REM →
      State.get w5 r = State.get u r := by
    intro r h1 h2 h3 h4
    rw [h5frame r h4 h2, hw4frame r h4, hw3frame r h3, h2frame r h1 h2,
      hw1frame r h1]
  have h5OUT : State.get w5 OUT = State.get u OUT :=
    h5chain OUT (by decide) (by decide) (by decide) (by decide)
  have h5WREG : State.get w5 WREG = State.get u WREG :=
    h5chain WREG (by decide) (by decide) (by decide) (by decide)
  have h5STEPSL : State.get w5 STEPSL
      = List.replicate (C.steps * C.init.length) 1 := by
    rw [h5chain STEPSL (by decide) (by decide) (by decide) (by decide)]
    exact hSTEPSL
  have h5STEPO : State.get w5 STEPO = List.replicate (step * C.offset) 1 := by
    rw [h5frame STEPO (by decide) (by decide), hw4frame STEPO (by decide),
      hw3frame STEPO (by decide)]
    exact h2STEPO
  have h5FBITS : State.get w5 FBITS = FlatCCBinFree.bitsNat bits := by
    rw [h5chain FBITS (by decide) (by decide) (by decide) (by decide)]
    exact hFBITS
  -- w6: nonEmpty TFLG REM, w7: the GFLG bit
  by_cases hguard : step * C.offset + bits.length ≤ C.init.length
  · have hREM0 : State.get w5 REM = [] := by
      rw [h5REM, Nat.sub_eq_zero_of_le hguard]
      rfl
    have hne : (State.get w5 REM).isEmpty = true := by rw [hREM0]; rfl
    have e6 : (Cmd.op (.nonEmpty TFLG REM)).eval w5 = w5.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w6 := w5.set TFLG [0] with hw6
    have hw6frame : ∀ r : Var, r ≠ TFLG → State.get w6 r = State.get w5 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw6Tne : State.get w6 TFLG ≠ [1] := by
      rw [hw6, State.get_set_eq]; decide
    clear_value w6
    have ec : (Cmd.op (.clear GFLG)).eval w6 = w6.set GFLG [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    have ea : (Cmd.op (.appendOne GFLG)).eval (w6.set GFLG []) = w6.set GFLG [1] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, State.set_set, List.nil_append]
    have e7 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w6
        = w6.set GFLG [1] := by
      rw [Cmd.eval_ifBit_false _ _ _ _ hw6Tne, Cmd.eval_seq, ec, ea]
    have hc7 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).cost w6 = 4 := by
      rw [Cmd.cost_ifBit_false _ _ _ _ hw6Tne, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op,
        ec]
      simp only [Op.cost]
    set w7 := w6.set GFLG [1] with hw7
    have hw7frame : ∀ r : Var, r ≠ GFLG → State.get w7 r = State.get w6 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw7G : State.get w7 GFLG = [1] := State.get_set_eq _ _ _
    clear_value w7
    have h7STEPSL : State.get w7 STEPSL
        = List.replicate (C.steps * C.init.length) 1 := by
      rw [hw7frame STEPSL (by decide), hw6frame STEPSL (by decide)]; exact h5STEPSL
    have h7STEPO : State.get w7 STEPO = List.replicate (step * C.offset) 1 := by
      rw [hw7frame STEPO (by decide), hw6frame STEPO (by decide)]; exact h5STEPO
    -- w8: FSTART := STEPSL ++ STEPO
    have e8 : (Cmd.op (.concat FSTART STEPSL STEPO)).eval w7
        = w7.set FSTART (List.replicate
            (C.steps * C.init.length + step * C.offset) 1) := by
      rw [Cmd.eval_op]
      simp only [Op.eval, h7STEPSL, h7STEPO]
      congr 1
      rw [List.replicate_add]
    have hc8 : Op.cost (.concat FSTART STEPSL STEPO) w7
        = 2 * (C.steps * C.init.length + step * C.offset) + 1 := by
      show 2 * ((State.get w7 STEPSL).length + (State.get w7 STEPO).length) + 1 = _
      rw [h7STEPSL, h7STEPO, List.length_replicate, List.length_replicate]
    set w8 := w7.set FSTART (List.replicate
        (C.steps * C.init.length + step * C.offset) 1) with hw8
    have hw8frame : ∀ r : Var, r ≠ FSTART → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8F : State.get w8 FSTART
        = List.replicate (C.steps * C.init.length + step * C.offset) 1 :=
      State.get_set_eq _ _ _
    have hw8FBITS : State.get w8 FBITS = FlatCCBinFree.bitsNat bits := by
      rw [hw8frame FBITS (by decide), hw7frame FBITS (by decide),
        hw6frame FBITS (by decide)]
      exact h5FBITS
    have hw8OUT : State.get w8 OUT = State.get u OUT := by
      rw [hw8frame OUT (by decide), hw7frame OUT (by decide),
        hw6frame OUT (by decide)]
      exact h5OUT
    have hw8WREG : State.get w8 WREG = State.get u WREG := by
      rw [hw8frame WREG (by decide), hw7frame WREG (by decide),
        hw6frame WREG (by decide)]
      exact h5WREG
    have hw8G : State.get w8 GFLG = [1] := by
      rw [hw8frame GFLG (by decide)]; exact hw7G
    clear_value w8
    -- w9: copy SCAN FBITS
    have e9 : (Cmd.op (.copy SCAN FBITS)).eval w8
        = w8.set SCAN (FlatCCBinFree.bitsNat bits) := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw8FBITS]
    have hc9 : Op.cost (.copy SCAN FBITS) w8 = bits.length + 1 := by
      show (State.get w8 FBITS).length + 1 = _
      rw [hw8FBITS]
      exact congrArg (· + 1) (List.length_map _)
    set w9 := w8.set SCAN (FlatCCBinFree.bitsNat bits) with hw9
    have hw9frame : ∀ r : Var, r ≠ SCAN → State.get w9 r = State.get w8 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw9SCAN : State.get w9 SCAN = FlatCCBinFree.bitsNat bits :=
      State.get_set_eq _ _ _
    have hw9F : State.get w9 FSTART
        = List.replicate (C.steps * C.init.length + step * C.offset) 1 := by
      rw [hw9frame FSTART (by decide)]; exact hw8F
    have hw9FBITSlen : (State.get w9 FBITS).length = bits.length := by
      rw [hw9frame FBITS (by decide), hw8FBITS]
      exact List.length_map _
    have hw9OUT : State.get w9 OUT = State.get u OUT := by
      rw [hw9frame OUT (by decide)]; exact hw8OUT
    have hw9WREG : State.get w9 WREG = State.get u WREG := by
      rw [hw9frame WREG (by decide)]; exact hw8WREG
    clear_value w9
    have hstep : encodeFinalAtStep C step bits
        = encodeBitsAt (C.steps * C.init.length + step * C.offset) bits := by
      unfold encodeFinalAtStep
      rw [dif_pos hguard]
    have hcScan := emitBitsFromScan_cost FSTART FBITS
      (C.steps * C.init.length + step * C.offset) bits w9 Ω
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw9F hw9FBITSlen hw9SCAN
      (by rw [hw9OUT, ← hstep]; exact hΩO)
      (by rw [hw9WREG]; exact hΩW)
      (by omega)
    have hWScan := emitBitsFromScan_WREG FSTART FBITS w9 Ω
      (by decide) (by decide) (by decide) (by decide)
      (by rw [hw9WREG]; exact hΩW)
      (by rw [hw9F, List.length_replicate, hw9FBITSlen]; omega)
    have hcost : finalStepBody.cost u
        = 1 + 1 + (1 + (Cmd.forBnd KTMP2 KFSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).cost w1
          + (1 + Op.cost (.concat SUMW STEPO BLEN) w2
          + (1 + Op.cost (.copy REM SUMW) w3
          + (1 + (Cmd.forBnd KTMP2 LREG (Cmd.op (.tail REM REM))).cost w4
          + (1 + 1
          + (1 + 4
          + (1 + Op.cost (.concat FSTART STEPSL STEPO) w7
          + (1 + (1 + Op.cost (.copy SCAN FBITS) w8
              + (emitBitsFromScan FSTART FBITS).cost w9))))))))) := by
      unfold finalStepBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq,
        Cmd.cost_op, e3, Cmd.cost_seq, Cmd.cost_op, e4, Cmd.cost_seq, ← hw5,
        Cmd.cost_seq, Cmd.cost_op, e6, Cmd.cost_seq, hc7, e7, Cmd.cost_seq,
        Cmd.cost_op, e8, Cmd.cost_ifBit_true _ _ _ _ hw8G, Cmd.cost_seq,
        Cmd.cost_op, e9]
      simp only [Op.cost]
    have heval : finalStepBody.eval u = (emitBitsFromScan FSTART FBITS).eval w9 := by
      unfold finalStepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, ← hw5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq, e8,
        Cmd.eval_ifBit_true _ _ _ _ hw8G, Cmd.eval_seq, e9]
    constructor
    · rw [hcost, hc3, hc4, hc8, hc9]
      have hoff : C.offset ≤ Ω := by omega
      have hsteple : step ≤ Ω := by omega
      have hso : step * C.offset ≤ Ω := by omega
      have hbl : bits.length ≤ Ω := by omega
      have hL : C.init.length ≤ Ω := by omega
      have hsl : C.steps * C.init.length + step * C.offset ≤ Ω := by omega
      have hMulle := le_trans hcMul (mulLoopClose C.offset step Ω hoff hsteple hso)
      have hSuble := le_trans hcSub
        (subLoopClose (step * C.offset + bits.length) C.init.length Ω (by omega) hL)
      have hScanle := hcScan
      set K := Cmd.flatK (bsBody 0) with hK
      clear_value K
      set P2 := (Ω + 1) * (Ω + 1) with hP2
      have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
      have hfin : (K + 60) * P2 = (K + 6) * P2 + 54 * P2 := by ring
      omega
    · rw [heval]
      exact hWScan
  · -- guard fails → emitFalse
    obtain ⟨k, hk⟩ : ∃ k, step * C.offset + bits.length - C.init.length = k + 1 :=
      ⟨step * C.offset + bits.length - C.init.length - 1, by omega⟩
    have hne : (State.get w5 REM).isEmpty = false := by
      rw [h5REM, hk]
      rfl
    have e6 : (Cmd.op (.nonEmpty TFLG REM)).eval w5 = w5.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w6 := w5.set TFLG [1] with hw6
    have hw6frame : ∀ r : Var, r ≠ TFLG → State.get w6 r = State.get w5 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw6T : State.get w6 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w6
    have e7 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w6
        = w6.set GFLG [] := by
      rw [Cmd.eval_ifBit_true _ _ _ _ hw6T, Cmd.eval_op]
      simp only [Op.eval]
    have hc7 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).cost w6 = 2 := by
      rw [Cmd.cost_ifBit_true _ _ _ _ hw6T, Cmd.cost_op]
      simp only [Op.cost]
    set w7 := w6.set GFLG [] with hw7
    have hw7frame : ∀ r : Var, r ≠ GFLG → State.get w7 r = State.get w6 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw7Gne : State.get w7 GFLG ≠ [1] := by
      rw [hw7, State.get_set_eq]; decide
    clear_value w7
    have h7STEPSL : State.get w7 STEPSL
        = List.replicate (C.steps * C.init.length) 1 := by
      rw [hw7frame STEPSL (by decide), hw6frame STEPSL (by decide)]; exact h5STEPSL
    have h7STEPO : State.get w7 STEPO = List.replicate (step * C.offset) 1 := by
      rw [hw7frame STEPO (by decide), hw6frame STEPO (by decide)]; exact h5STEPO
    have e8 : (Cmd.op (.concat FSTART STEPSL STEPO)).eval w7
        = w7.set FSTART (List.replicate
            (C.steps * C.init.length + step * C.offset) 1) := by
      rw [Cmd.eval_op]
      simp only [Op.eval, h7STEPSL, h7STEPO]
      congr 1
      rw [List.replicate_add]
    have hc8 : Op.cost (.concat FSTART STEPSL STEPO) w7
        = 2 * (C.steps * C.init.length + step * C.offset) + 1 := by
      show 2 * ((State.get w7 STEPSL).length + (State.get w7 STEPO).length) + 1 = _
      rw [h7STEPSL, h7STEPO, List.length_replicate, List.length_replicate]
    set w8 := w7.set FSTART (List.replicate
        (C.steps * C.init.length + step * C.offset) 1) with hw8
    have hw8frame : ∀ r : Var, r ≠ FSTART → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8Gne : State.get w8 GFLG ≠ [1] := by
      rw [hw8frame GFLG (by decide)]; exact hw7Gne
    have hw8WREG : State.get w8 WREG = State.get u WREG := by
      rw [hw8frame WREG (by decide), hw7frame WREG (by decide),
        hw6frame WREG (by decide)]
      exact h5WREG
    clear_value w8
    have hcost : finalStepBody.cost u
        = 1 + 1 + (1 + (Cmd.forBnd KTMP2 KFSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).cost w1
          + (1 + Op.cost (.concat SUMW STEPO BLEN) w2
          + (1 + Op.cost (.copy REM SUMW) w3
          + (1 + (Cmd.forBnd KTMP2 LREG (Cmd.op (.tail REM REM))).cost w4
          + (1 + 1
          + (1 + 2
          + (1 + Op.cost (.concat FSTART STEPSL STEPO) w7
          + (1 + 9)))))))) := by
      unfold finalStepBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq,
        Cmd.cost_op, e3, Cmd.cost_seq, Cmd.cost_op, e4, Cmd.cost_seq, ← hw5,
        Cmd.cost_seq, Cmd.cost_op, e6, Cmd.cost_seq, hc7, e7, Cmd.cost_seq,
        Cmd.cost_op, e8, Cmd.cost_ifBit_false _ _ _ _ hw8Gne, emitFalse_cost]
      simp only [Op.cost]
    have heval : finalStepBody.eval u = emitFalse.eval w8 := by
      unfold finalStepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, ← hw5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq, e8,
        Cmd.eval_ifBit_false _ _ _ _ hw8Gne]
    constructor
    · rw [hcost, hc3, hc4, hc8]
      have hoff : C.offset ≤ Ω := by omega
      have hsteple : step ≤ Ω := by omega
      have hso : step * C.offset ≤ Ω := by omega
      have hbl : bits.length ≤ Ω := by omega
      have hL : C.init.length ≤ Ω := by omega
      have hsl : C.steps * C.init.length + step * C.offset ≤ Ω := by omega
      have hMulle := le_trans hcMul (mulLoopClose C.offset step Ω hoff hsteple hso)
      have hSuble := le_trans hcSub
        (subLoopClose (step * C.offset + bits.length) C.init.length Ω (by omega) hL)
      set K := Cmd.flatK (bsBody 0) with hK
      clear_value K
      set P2 := (Ω + 1) * (Ω + 1) with hP2
      have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
      have hKP2 : 0 ≤ K * P2 := Nat.zero_le _
      have hfin : (K + 60) * P2 = K * P2 + 60 * P2 := by ring
      omega
    · rw [heval, emitFalse_frame _ WREG (by decide), hw8WREG]
      exact hΩW

/-- Per-iteration effect of the inner final-step loop: cost + `WREG ≤ Ω`.
`u3` is the inner loop's entry state (one parsed final string in
`FBITS`/`BLEN`). Direct mirror of `stepIterBody_effect` one tag over. -/
private theorem finalStepIterBody_effect (C : BinaryCC) (bits : List Bool)
    (u3 : State) (Ω : Nat)
    (hSTEPSL : State.get u3 STEPSL = List.replicate (C.steps * C.init.length) 1)
    (hOFF : State.get u3 OFFSET = List.replicate C.offset 1)
    (hBLEN : State.get u3 BLEN = List.replicate bits.length 1)
    (hLREG : State.get u3 LREG = List.replicate C.init.length 1)
    (hFBITS : State.get u3 FBITS = FlatCCBinFree.bitsNat bits)
    (hΩOS : (State.get u3 OUT).length
        + (serF (encodeFinalString C bits)).length ≤ Ω)
    (hΩidxS : C.steps * C.init.length + C.init.length * C.offset
        + C.init.length + C.offset + bits.length + C.init.length ≤ Ω)
    (i : Nat) (hi : i < C.init.length + 1) (st : State)
    (hInv : FSInv C bits u3 i st) (hW : (State.get st WREG).length ≤ Ω) :
    finalStepIterBody.cost (st.set KFSTEP (List.replicate i 1))
        ≤ 4 + (Cmd.flatK (bsBody 0) + 60) * ((Ω + 1) * (Ω + 1))
    ∧ (State.get (finalStepIterBody.eval (st.set KFSTEP (List.replicate i 1))) WREG).length
        ≤ Ω := by
  obtain ⟨hOUT, hZ, hframe⟩ := hInv
  set w := st.set KFSTEP (List.replicate i 1) with hw
  have hwframe : ∀ r : Var, r ≠ KFSTEP → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwK : State.get w KFSTEP = List.replicate i 1 := State.get_set_eq _ _ _
  clear_value w
  set w1 := emitForrTag.eval w with hw1
  have hw1frame : ∀ r : Var, r ≠ OUT → State.get w1 r = State.get w r := by
    intro r hr; rw [hw1]; exact emitForrTag_frame w r hr
  have hw1OUT : State.get w1 OUT = State.get w OUT ++ [1, 0] := by
    rw [hw1, emitForrTag_run]; exact State.get_set_eq _ _ _
  clear_value w1
  -- thread the finalStepBody entry facts to w1
  have hchain : ∀ r : Var, r ≠ OUT → r ≠ KFSTEP →
      r ≠ SCAN → r ≠ WREG → r ≠ TFLG → r ≠ KBIT → r ≠ ZERO → r ≠ KTMP2 →
      r ≠ STEPO → r ≠ SUMW → r ≠ REM → r ≠ GFLG → r ≠ FSTART →
      State.get w1 r = State.get u3 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    rw [hw1frame r h1, hwframe r h2,
      hframe r h3 h1 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h2]
  have h1STEPSL : State.get w1 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
    rw [hchain STEPSL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hSTEPSL
  have h1KFSTEP : State.get w1 KFSTEP = List.replicate i 1 := by
    rw [hw1frame KFSTEP (by decide)]; exact hwK
  have h1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hchain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hOFF
  have h1BLEN : State.get w1 BLEN = List.replicate bits.length 1 := by
    rw [hchain BLEN (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hBLEN
  have h1LREG : State.get w1 LREG = List.replicate C.init.length 1 := by
    rw [hchain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hLREG
  have h1FBITS : State.get w1 FBITS = FlatCCBinFree.bitsNat bits := by
    rw [hchain FBITS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hFBITS
  have h1Z : State.get w1 ZERO = [] := by
    rw [hw1frame ZERO (by decide), hwframe ZERO (by decide)]; exact hZ
  have h1W : (State.get w1 WREG).length ≤ Ω := by
    rw [hw1frame WREG (by decide), hwframe WREG (by decide)]; exact hW
  -- the OUT ceiling at w1
  have h1OUTfull : State.get w1 OUT = State.get u3 OUT
      ++ orPrefix ((List.range i).map (fun step => encodeFinalAtStep C step bits))
      ++ [1, 0] := by
    rw [hw1OUT, hwframe OUT (by decide), hOUT]
  have hΩO1 : (State.get w1 OUT).length
      + (serF (encodeFinalAtStep C i bits)).length ≤ Ω := by
    have hsucc := orPrefix_range_succ (fun step => encodeFinalAtStep C step bits) i
    have hle := orPrefix_range_le (fun step => encodeFinalAtStep C step bits) (i + 1)
      (C.init.length + 1) hi
    have hstrC : serF (encodeFinalString C bits)
        = serF (listOr ((List.range (C.init.length + 1)).map
            (fun step => encodeFinalAtStep C step bits))) := rfl
    rw [hstrC] at hΩOS
    rw [h1OUTfull]
    have hlen : (orPrefix ((List.range (i + 1)).map
          (fun step => encodeFinalAtStep C step bits))).length
        = (orPrefix ((List.range i).map
            (fun step => encodeFinalAtStep C step bits))).length
          + (2 + (serF (encodeFinalAtStep C i bits)).length) := by
      rw [hsucc]
      simp [List.length_append]
      omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hΩidxi : C.steps * C.init.length + i * C.offset + i + C.offset
      + bits.length + C.init.length ≤ Ω := by
    have hiL : i ≤ C.init.length := by omega
    have hio : i * C.offset ≤ C.init.length * C.offset :=
      Nat.mul_le_mul_right _ hiL
    omega
  have hFB := finalStepBody_cost C i bits w1 Ω h1STEPSL h1KFSTEP h1OFF h1BLEN
    h1LREG h1FBITS h1Z hΩO1 h1W hΩidxi
  have hcost : finalStepIterBody.cost w = 1 + 3 + finalStepBody.cost w1 := by
    unfold finalStepIterBody
    rw [Cmd.cost_seq, emitForrTag_cost, ← hw1]
  have heval : finalStepIterBody.eval w = finalStepBody.eval w1 := by
    unfold finalStepIterBody
    rw [Cmd.eval_seq, ← hw1]
  constructor
  · rw [hcost]
    have h1 := hFB.1
    set B := (Cmd.flatK (bsBody 0) + 60) * ((Ω + 1) * (Ω + 1)) with hB
    clear_value B
    omega
  · rw [heval]
    exact hFB.2

/-- Per-iteration effect of the final-string loop: cost + `WREG ≤ Ω`. `u2` is
the loop's entry state (the final stream copied into `SCANF`). Mirror of
`lineBody_effect` with `cardEmitBody_effect`'s live/idle split over `FFInv`. -/
private theorem finalStringBody_effect (C : BinaryCC) (u2 : State) (Ω : Nat)
    (hSTEPSL : State.get u2 STEPSL = List.replicate (C.steps * C.init.length) 1)
    (hOFF : State.get u2 OFFSET = List.replicate C.offset 1)
    (hLREG : State.get u2 LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u2 LREG1 = List.replicate (C.init.length + 1) 1)
    (hΩO : (State.get u2 OUT).length
        + (serF (encodeFinalConstraint C)).length ≤ Ω)
    (hΩidx : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.init.length
        + (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length ≤ Ω)
    (j : Nat) (st : State)
    (hInv : FFInv C u2 j st) (hW : (State.get st WREG).length ≤ Ω) :
    finalStringBody.cost (st.set KFS (List.replicate j 1))
        ≤ (Cmd.flatK (bsBody 0) + Cmd.flatK readFinBody + 100)
            * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))
    ∧ (State.get (finalStringBody.eval (st.set KFS (List.replicate j 1))) WREG).length
        ≤ Ω := by
  obtain ⟨hSCAN, hOUT, hZERO, hframe⟩ := hInv
  set w := st.set KFS (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KFS → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSCAN : State.get w SCANF
      = FlatTCCFree.encFinal ((C.final.drop j).map FlatCCBinFree.bitsNat) := by
    rw [hwframe SCANF (by decide)]; exact hSCAN
  have hwOUT : State.get w OUT
      = State.get u2 OUT ++ orPrefix ((C.final.take j).map (encodeFinalString C)) := by
    rw [hwframe OUT (by decide)]; exact hOUT
  have hwZ : State.get w ZERO = [] := by
    rw [hwframe ZERO (by decide)]; exact hZERO
  have hwW : (State.get w WREG).length ≤ Ω := by
    rw [hwframe WREG (by decide)]; exact hW
  -- the frozen per-tableau registers, recovered on `w`
  have hwchain : ∀ r : Var, r ≠ SCANF → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
      r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KTMP2 → r ≠ FBITS →
      r ≠ BLEN → r ≠ SCAN → r ≠ STEPO → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
      r ≠ FSTART → r ≠ KFSTEP → r ≠ KFS → State.get w r = State.get u2 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    rw [hwframe r h20,
      hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20]
  have hwSTEPSL : State.get w STEPSL = List.replicate (C.steps * C.init.length) 1 := by
    rw [hwchain STEPSL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hSTEPSL
  have hwOFF : State.get w OFFSET = List.replicate C.offset 1 := by
    rw [hwchain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hOFF
  have hwLREG : State.get w LREG = List.replicate C.init.length 1 := by
    rw [hwchain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG
  have hwLREG1 : State.get w LREG1 = List.replicate (C.init.length + 1) 1 := by
    rw [hwchain LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG1
  -- the drop-stream ceiling
  have hstream : (FlatTCCFree.encFinal ((C.final.drop j).map FlatCCBinFree.bitsNat)).length
      ≤ (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length := by
    rw [show (C.final.drop j).map FlatCCBinFree.bitsNat
        = (C.final.map FlatCCBinFree.bitsNat).drop j from List.map_drop ..]
    exact encFinal_drop_length_le _ j
  clear_value w
  by_cases hj : j < C.final.length
  · -- live iteration: parse one string, emit its step disjunction
    have hdrop : C.final.drop j = C.final[j] :: C.final.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    have htake : C.final.take (j + 1) = C.final.take j ++ [C.final[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    set bits := C.final[j] with hbits
    clear_value bits
    set REST := FlatTCCFree.encFinal ((C.final.drop (j + 1)).map FlatCCBinFree.bitsNat)
      with hREST
    have hSCANw : State.get w SCANF
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ REST := by
      rw [hwSCAN, hdrop, encFinal_cons, ← hREST]
    have hne : (State.get w SCANF).isEmpty = false := by
      rw [hSCANw]; exact encSList_append_isEmpty _ _
    -- the SCANF length ceiling (for readOneFinal's cost)
    have hSCANlen : (State.get w SCANF).length
        ≤ (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length := by
      rw [hwSCAN]
      exact hstream
    -- the parsed string's length ceiling
    have hbl : bits.length
        ≤ (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length := by
      have h1 : bits.length ≤ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length := by
        have h := encSList_length_ge (FlatCCBinFree.bitsNat bits)
        rw [show (FlatCCBinFree.bitsNat bits).length = bits.length from
          List.length_map _] at h
        exact h
      have h2 : (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length
          ≤ (State.get w SCANF).length := by
        rw [hSCANw, List.length_append]
        omega
      omega
    -- w1: nonEmpty TFLG SCANF
    have e1 : (Cmd.op (.nonEmpty TFLG SCANF)).eval w = w.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    set w1 := w.set TFLG [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ TFLG → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1T : State.get w1 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w1
    -- w2: the forr spine node
    set w2 := emitForrTag.eval w1 with hw2
    have hw2frame : ∀ r : Var, r ≠ OUT → State.get w2 r = State.get w1 r := by
      intro r hr; rw [hw2]; exact emitForrTag_frame w1 r hr
    have hw2OUT : State.get w2 OUT = State.get w1 OUT ++ [1, 0] := by
      rw [hw2, emitForrTag_run]; exact State.get_set_eq _ _ _
    clear_value w2
    have h2SCANF : State.get w2 SCANF
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ REST := by
      rw [hw2frame SCANF (by decide), hw1frame SCANF (by decide)]; exact hSCANw
    have h2SCANFlen : (State.get w2 SCANF).length ≤ Ω := by
      rw [h2SCANF, ← hSCANw]
      omega
    -- w3: parse one final string (run + cost)
    have hcRead := readOneFinal_cost bits REST w2 Ω h2SCANF h2SCANFlen
    obtain ⟨h3SCANF, h3FBITS, h3BLEN, h3frame⟩ := readOneFinal_run bits REST w2 h2SCANF
    set w3 := readOneFinal.eval w2 with hw3
    clear_value w3
    have h3chain : ∀ r : Var, r ≠ SCANF → r ≠ FBITS → r ≠ BLEN → r ≠ DONE →
        r ≠ EMARK → r ≠ TFLG → r ≠ KTMP → r ≠ KTMP2 → r ≠ OUT →
        State.get w3 r = State.get w r := by
      intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [h3frame r h1 h2 h3 h4 h5 h6 h7 h8, hw2frame r h9, hw1frame r h6]
    have h3STEPSL : State.get w3 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
      rw [h3chain STEPSL (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwSTEPSL
    have h3OFF : State.get w3 OFFSET = List.replicate C.offset 1 := by
      rw [h3chain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwOFF
    have h3LREG : State.get w3 LREG = List.replicate C.init.length 1 := by
      rw [h3chain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwLREG
    have h3LREG1 : State.get w3 LREG1 = List.replicate (C.init.length + 1) 1 := by
      rw [h3chain LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwLREG1
    have h3LREG1len : (State.get w3 LREG1).length = C.init.length + 1 := by
      rw [h3LREG1, List.length_replicate]
    have h3Z : State.get w3 ZERO = [] := by
      rw [h3chain ZERO (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwZ
    have h3W : (State.get w3 WREG).length ≤ Ω := by
      rw [h3chain WREG (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwW
    have h3OUT : State.get w3 OUT = State.get u2 OUT
        ++ orPrefix ((C.final.take j).map (encodeFinalString C)) ++ [1, 0] := by
      rw [h3frame OUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hw2OUT, hw1frame OUT (by decide), hwOUT]
    -- the string-level OUT ceiling at w3
    have hΩOS3 : (State.get w3 OUT).length
        + (serF (encodeFinalString C bits)).length ≤ Ω := by
      have hsnoc : orPrefix ((C.final.take (j + 1)).map (encodeFinalString C))
          = orPrefix ((C.final.take j).map (encodeFinalString C))
            ++ ([1, 0] ++ serF (encodeFinalString C bits)) := by
        rw [htake, List.map_append, orPrefix_append]
        simp [orPrefix]
      have htklen : (orPrefix ((C.final.take (j + 1)).map (encodeFinalString C))).length
          ≤ (serF (encodeFinalConstraint C)).length := by
        rw [show (C.final.take (j + 1)).map (encodeFinalString C)
            = (C.final.map (encodeFinalString C)).take (j + 1) from List.map_take ..]
        exact orPrefix_take_length_le _ (j + 1)
      have hlen : (orPrefix ((C.final.take (j + 1)).map (encodeFinalString C))).length
          = (orPrefix ((C.final.take j).map (encodeFinalString C))).length
            + (2 + (serF (encodeFinalString C bits)).length) := by
        rw [hsnoc]
        simp [List.length_append]
        omega
      rw [h3OUT]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hΩidxS3 : C.steps * C.init.length + C.init.length * C.offset
        + C.init.length + C.offset + bits.length + C.init.length ≤ Ω := by
      omega
    -- the inner step loop (cost + run + WREG)
    have hfsBase : FSInv C bits w3 0 w3 :=
      ⟨by simp [orPrefix], h3Z,
        fun r _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    have hcInner := Cmd.cost_forBnd_le KFSTEP LREG1 finalStepIterBody w3
      (4 + (Cmd.flatK (bsBody 0) + 60) * ((Ω + 1) * (Ω + 1)))
      (fun i stt => FSInv C bits w3 i stt ∧ (State.get stt WREG).length ≤ Ω)
      ⟨hfsBase, h3W⟩
      (fun i stt hi hM => by
        refine ⟨FSInv_step C bits w3 h3STEPSL h3OFF h3BLEN h3LREG h3FBITS i stt hM.1, ?_⟩
        exact (finalStepIterBody_effect C bits w3 Ω h3STEPSL h3OFF h3BLEN h3LREG
          h3FBITS hΩOS3 hΩidxS3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).2)
      (fun i stt hi hM =>
        (finalStepIterBody_effect C bits w3 Ω h3STEPSL h3OFF h3BLEN h3LREG
          h3FBITS hΩOS3 hΩidxS3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).1)
    have hwInner := Cmd.foldlState_range_induct finalStepIterBody KFSTEP
      (State.get w3 LREG1).length w3
      (fun i stt => FSInv C bits w3 i stt ∧ (State.get stt WREG).length ≤ Ω)
      ⟨hfsBase, h3W⟩
      (fun i stt hi hM => by
        refine ⟨FSInv_step C bits w3 h3STEPSL h3OFF h3BLEN h3LREG h3FBITS i stt hM.1, ?_⟩
        exact (finalStepIterBody_effect C bits w3 Ω h3STEPSL h3OFF h3BLEN h3LREG
          h3FBITS hΩOS3 hΩidxS3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).2)
    set w4 := (Cmd.forBnd KFSTEP LREG1 finalStepIterBody).eval w3 with hw4
    have hw4eval : w4 = Cmd.foldlState finalStepIterBody KFSTEP
        (List.range (State.get w3 LREG1).length) w3 := by
      rw [hw4, Cmd.eval_forBnd]
    have h4W : (State.get w4 WREG).length ≤ Ω := by
      rw [hw4eval]
      exact hwInner.2
    clear_value w4
    -- w5: close the inner listOr with falseFml
    set w5 := emitFalse.eval w4 with hw5
    have hw5W : (State.get w5 WREG).length ≤ Ω := by
      rw [hw5, emitFalse_frame _ WREG (by decide)]
      exact h4W
    clear_value w5
    -- assemble cost and eval
    have hcost : finalStringBody.cost w
        = 1 + 1 + (1 + (1 + 3 + (1 + readOneFinal.cost w2
            + (1 + (Cmd.forBnd KFSTEP LREG1 finalStepIterBody).cost w3 + 9)))) := by
      unfold finalStringBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_true _ _ _ _ hw1T,
        Cmd.cost_seq, emitForrTag_cost, ← hw2, Cmd.cost_seq, ← hw3, Cmd.cost_seq,
        ← hw4, emitFalse_cost]
      simp only [Op.cost]
    have heval : finalStringBody.eval w = w5 := by
      unfold finalStringBody
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_true _ _ _ _ hw1T, Cmd.eval_seq, ← hw2,
        Cmd.eval_seq, ← hw3, Cmd.eval_seq, ← hw4, ← hw5]
    constructor
    · rw [hcost]
      -- arithmetic
      have hLΩ : C.init.length ≤ Ω := by omega
      have hiters : (State.get w3 LREG1).length ≤ Ω + 1 := by
        rw [h3LREG1len]; omega
      set Kb := Cmd.flatK (bsBody 0) with hKb
      clear_value Kb
      set Kr := Cmd.flatK readFinBody with hKr
      clear_value Kr
      set P2 := (Ω + 1) * (Ω + 1) with hP2
      set P3 := (Ω + 1) * P2 with hP3
      set B := 4 + (Kb + 60) * P2 with hB
      have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
      have hBle : B ≤ (Kb + 64) * P2 := by
        rw [hB]
        have h4 : 4 ≤ 4 * P2 := by omega
        have he : 4 * P2 + (Kb + 60) * P2 = (Kb + 64) * P2 := by ring
        omega
      have hlB : (State.get w3 LREG1).length * B ≤ (Ω + 1) * ((Kb + 64) * P2) :=
        Nat.mul_le_mul hiters hBle
      have he3 : (Ω + 1) * ((Kb + 64) * P2) = (Kb + 64) * P3 := by
        rw [hP3]; ring
      have hii : (State.get w3 LREG1).length * (State.get w3 LREG1).length
          ≤ P2 := by
        rw [hP2]; exact Nat.mul_le_mul hiters hiters
      have hP23 : P2 ≤ P3 := by
        rw [hP3]; exact le_scale Ω P2
      have h1P3 : 1 ≤ P3 := le_trans h1P2 hP23
      have hrle : (Kr + 10) * P2 ≤ (Kr + 10) * P3 := Nat.mul_le_mul_left _ hP23
      have hfin : (Kb + Kr + 100) * P3
          = (Kb + 64) * P3 + (Kr + 10) * P3 + 26 * P3 := by ring
      omega
    · rw [heval]
      exact hw5W
  · -- idle iteration: stream exhausted, `nonEmpty` falls through
    have hlen : C.final.length ≤ j := Nat.le_of_not_lt hj
    have hSCANw : State.get w SCANF = [] := by
      rw [hwSCAN, List.drop_eq_nil_of_le hlen]; rfl
    have hne : (State.get w SCANF).isEmpty = true := by rw [hSCANw]; rfl
    have e1 : (Cmd.op (.nonEmpty TFLG SCANF)).eval w = w.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    have hw1Tne : State.get (w.set TFLG [0]) TFLG ≠ [1] := by
      rw [State.get_set_eq]; decide
    constructor
    · have hcost : finalStringBody.cost w = 1 + 1 + (1 + 1) := by
        unfold finalStringBody
        rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_false _ _ _ _ hw1Tne,
          Cmd.cost_op]
        simp only [Op.cost]
      rw [hcost]
      have h1P3 : 1 ≤ (Ω + 1) * ((Ω + 1) * (Ω + 1)) :=
        Nat.mul_pos (Nat.succ_pos Ω) (Nat.mul_pos (Nat.succ_pos Ω) (Nat.succ_pos Ω))
      calc 1 + 1 + (1 + 1) ≤ 100 * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) := by omega
        _ ≤ (Cmd.flatK (bsBody 0) + Cmd.flatK readFinBody + 100)
            * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) :=
          Nat.mul_le_mul_right _ (by omega)
    · have heval : finalStringBody.eval w = (w.set TFLG [0]).set KTMP [] := by
        unfold finalStringBody
        rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_false _ _ _ _ hw1Tne, Cmd.eval_op]
        simp only [Op.eval]
      rw [heval, State.get_set_ne _ _ _ _ (show WREG ≠ KTMP by decide),
        State.get_set_ne _ _ _ _ (show WREG ≠ TFLG by decide)]
      exact hwW

/-- **`emitFinal` cost**: quartic in the ceiling `Ω`, plus the `WREG ≤ Ω` exit
fact. `Ω` must dominate the entry `OUT` plus the full final-constraint
emission, the entry `WREG`, and the index/stream sums. -/
theorem emitFinal_cost (C : BinaryCC) (u : State) (Ω : Nat)
    (hSTEPS : State.get u STEPS = List.replicate C.steps 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u LREG1 = List.replicate (C.init.length + 1) 1)
    (hFINAL : State.get u FINAL
        = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat))
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length
        + (serF (encodeFinalConstraint C)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩidx : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.init.length + C.steps
        + (State.get u FINAL).length ≤ Ω) :
    emitFinal.cost u
        ≤ (Cmd.flatK (bsBody 0) + Cmd.flatK readFinBody + 140)
            * ((Ω + 1) * ((Ω + 1) * ((Ω + 1) * (Ω + 1))))
    ∧ (State.get (emitFinal.eval u) WREG).length ≤ Ω := by
  -- u0: clear STEPSL
  have e0clear : (Cmd.op (.clear STEPSL)).eval u = u.set STEPSL [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u0 := u.set STEPSL [] with hu0
  have hu0frame : ∀ r : Var, r ≠ STEPSL → State.get u0 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu0STEPSL : State.get u0 STEPSL = [] := State.get_set_eq _ _ _
  have hu0LREG : State.get u0 LREG = List.replicate C.init.length 1 := by
    rw [hu0frame LREG (by decide)]; exact hLREG
  have hu0STEPSlen : (State.get u0 STEPS).length = C.steps := by
    rw [hu0frame STEPS (by decide), hSTEPS, List.length_replicate]
  clear_value u0
  -- u1: STEPSL := 1^(steps·L) (run + cost)
  have hcMul := cost_mulLoop_le KTMP STEPS STEPSL LREG u0 0 C.init.length C.steps
    (by decide) (by decide) (by decide)
    (by rw [hu0STEPSL]; exact Nat.le_refl 0)
    (by rw [hu0LREG, List.length_replicate])
    hu0STEPSlen
  obtain ⟨h1STEPSL, h1mulframe⟩ :=
    unaryMulLoop_run KTMP STEPS LREG STEPSL u0 C.init.length C.steps
      (by decide) (by decide) (by decide) hu0LREG hu0STEPSlen hu0STEPSL
  set u1 := (Cmd.forBnd KTMP STEPS (Cmd.op (.concat STEPSL STEPSL LREG))).eval u0 with hu1
  clear_value u1
  have h1FINAL : State.get u1 FINAL
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := by
    rw [h1mulframe FINAL (by decide) (by decide), hu0frame FINAL (by decide)]
    exact hFINAL
  have h1FINALlen : (State.get u1 FINAL).length = (State.get u FINAL).length := by
    rw [h1FINAL, hFINAL]
  -- u2: copy SCANF FINAL (run + cost)
  have e2copy : (Cmd.op (.copy SCANF FINAL)).eval u1
      = u1.set SCANF (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, h1FINAL]
  have hc2 : Op.cost (.copy SCANF FINAL) u1 = (State.get u FINAL).length + 1 := by
    show (State.get u1 FINAL).length + 1 = _
    rw [h1FINALlen]
  set u2 := u1.set SCANF (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)) with hu2
  have hu2frame : ∀ r : Var, r ≠ SCANF → State.get u2 r = State.get u1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu2SCANF : State.get u2 SCANF
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := State.get_set_eq _ _ _
  clear_value u2
  have hu2chain : ∀ r : Var, r ≠ SCANF → r ≠ STEPSL → r ≠ KTMP →
      State.get u2 r = State.get u r := by
    intro r h1 h2 h3
    rw [hu2frame r h1, h1mulframe r h2 h3, hu0frame r h2]
  have h2STEPSL : State.get u2 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
    rw [hu2frame STEPSL (by decide)]; exact h1STEPSL
  have h2OFF : State.get u2 OFFSET = List.replicate C.offset 1 := by
    rw [hu2chain OFFSET (by decide) (by decide) (by decide)]; exact hOFF
  have h2LREG : State.get u2 LREG = List.replicate C.init.length 1 := by
    rw [hu2chain LREG (by decide) (by decide) (by decide)]; exact hLREG
  have h2LREG1 : State.get u2 LREG1 = List.replicate (C.init.length + 1) 1 := by
    rw [hu2chain LREG1 (by decide) (by decide) (by decide)]; exact hLREG1
  have h2Z : State.get u2 ZERO = [] := by
    rw [hu2chain ZERO (by decide) (by decide) (by decide)]; exact hZ
  have h2OUT : State.get u2 OUT = State.get u OUT :=
    hu2chain OUT (by decide) (by decide) (by decide)
  have h2WREG : State.get u2 WREG = State.get u WREG :=
    hu2chain WREG (by decide) (by decide) (by decide)
  have h2FINAL : State.get u2 FINAL
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := by
    rw [hu2frame FINAL (by decide)]; exact h1FINAL
  have h2FINALlen : (State.get u2 FINAL).length = (State.get u FINAL).length := by
    rw [h2FINAL, hFINAL]
  have hΩO2 : (State.get u2 OUT).length
      + (serF (encodeFinalConstraint C)).length ≤ Ω := by
    rw [h2OUT]; exact hΩO
  have hΩW2 : (State.get u2 WREG).length ≤ Ω := by
    rw [h2WREG]; exact hΩW
  have hΩidx2 : C.steps * C.init.length + C.init.length * C.offset + C.init.length
      + C.offset + C.init.length
      + (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length ≤ Ω := by
    rw [← hFINAL]; omega
  -- the string loop (cost + WREG)
  have hffBase : FFInv C u2 0 u2 := by
    refine ⟨by rw [List.drop_zero]; exact hu2SCANF, ?_, h2Z,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    rw [List.take_zero, List.map_nil, show orPrefix [] = [] from rfl, List.append_nil]
  have hloop := Cmd.cost_forBnd_le KFS FINAL finalStringBody u2
    ((Cmd.flatK (bsBody 0) + Cmd.flatK readFinBody + 100)
      * ((Ω + 1) * ((Ω + 1) * (Ω + 1))))
    (fun j st => FFInv C u2 j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨hffBase, hΩW2⟩
    (fun j st hj hM => by
      refine ⟨FFInv_step C u2 h2STEPSL h2OFF h2LREG h2LREG1 j st hM.1, ?_⟩
      exact (finalStringBody_effect C u2 Ω h2STEPSL h2OFF h2LREG h2LREG1
        hΩO2 hΩidx2 j st hM.1 hM.2).2)
    (fun j st hj hM =>
      (finalStringBody_effect C u2 Ω h2STEPSL h2OFF h2LREG h2LREG1
        hΩO2 hΩidx2 j st hM.1 hM.2).1)
  have hwLoop := Cmd.foldlState_range_induct finalStringBody KFS
    (State.get u2 FINAL).length u2
    (fun j st => FFInv C u2 j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨hffBase, hΩW2⟩
    (fun j st hj hM => by
      refine ⟨FFInv_step C u2 h2STEPSL h2OFF h2LREG h2LREG1 j st hM.1, ?_⟩
      exact (finalStringBody_effect C u2 Ω h2STEPSL h2OFF h2LREG h2LREG1
        hΩO2 hΩidx2 j st hM.1 hM.2).2)
  -- assemble cost and eval
  have hcost : emitFinal.cost u
      = 1 + 1 + (1 + (Cmd.forBnd KTMP STEPS (Cmd.op (.concat STEPSL STEPSL LREG))).cost u0
        + (1 + Op.cost (.copy SCANF FINAL) u1
        + (1 + (Cmd.forBnd KFS FINAL finalStringBody).cost u2 + 9))) := by
    unfold emitFinal
    rw [Cmd.cost_seq, Cmd.cost_op, e0clear, Cmd.cost_seq, ← hu1, Cmd.cost_seq,
      Cmd.cost_op, e2copy, Cmd.cost_seq, emitFalse_cost]
    simp only [Op.cost]
  have heval : emitFinal.eval u
      = emitFalse.eval (Cmd.foldlState finalStringBody KFS
          (List.range (State.get u2 FINAL).length) u2) := by
    unfold emitFinal
    rw [Cmd.eval_seq, e0clear, Cmd.eval_seq, ← hu1, Cmd.eval_seq, e2copy, Cmd.eval_seq,
      Cmd.eval_forBnd]
  constructor
  · rw [hcost, hc2]
    -- arithmetic
    have hlenΩ : (State.get u FINAL).length ≤ Ω := by omega
    have hL : C.init.length ≤ Ω := by omega
    have hsteps : C.steps ≤ Ω := by omega
    have hsL : C.steps * C.init.length ≤ Ω := by omega
    have hMulle := le_trans hcMul (mulLoopClose C.init.length C.steps Ω hL hsteps hsL)
    have hlen2 : (State.get u2 FINAL).length ≤ Ω := by
      rw [h2FINALlen]; omega
    set Kb := Cmd.flatK (bsBody 0) with hKb
    clear_value Kb
    set Kr := Cmd.flatK readFinBody with hKr
    clear_value Kr
    set P2 := (Ω + 1) * (Ω + 1) with hP2
    set P3 := (Ω + 1) * P2 with hP3
    set P4 := (Ω + 1) * P3 with hP4
    have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
    have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
    have hP34 : P3 ≤ P4 := by rw [hP4]; exact le_scale Ω P3
    have h1P4 : 1 ≤ P4 := le_trans h1P2 (le_trans hP23 hP34)
    have hlB : (State.get u2 FINAL).length * ((Kb + Kr + 100) * P3)
        ≤ (Ω + 1) * ((Kb + Kr + 100) * P3) :=
      Nat.mul_le_mul_right _ (by omega)
    have he4 : (Ω + 1) * ((Kb + Kr + 100) * P3) = (Kb + Kr + 100) * P4 := by
      rw [hP4]; ring
    have hll : (State.get u2 FINAL).length * (State.get u2 FINAL).length
        ≤ Ω * Ω := Nat.mul_le_mul hlen2 hlen2
    have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
    have hMul4 : 7 * P2 ≤ 7 * P4 :=
      Nat.mul_le_mul_left _ (le_trans hP23 hP34)
    have hΩ1P4 : Ω + 1 ≤ P4 := by
      calc Ω + 1 = (Ω + 1) * 1 := by ring
        _ ≤ (Ω + 1) * P3 := Nat.mul_le_mul_left _ (le_trans h1P2 hP23)
        _ = P4 := by rw [hP4]
    have hP24 : P2 ≤ P4 := le_trans hP23 hP34
    have hfin : (Kb + Kr + 140) * P4 = (Kb + Kr + 100) * P4 + 40 * P4 := by ring
    omega
  · rw [heval, emitFalse_frame _ WREG (by decide)]
    exact hwLoop.2

/-! ### The wellformedness guard: cost -/

private theorem andFlag_cost (FLG : Nat) (s : State) : (andFlag FLG).cost s = 2 := by
  unfold andFlag
  by_cases hT : State.get s FLG = [1]
  · rw [Cmd.cost_ifBit_true _ _ _ _ hT, Cmd.cost_op]
    simp only [Op.cost]
  · rw [Cmd.cost_ifBit_false _ _ _ _ hT, Cmd.cost_op]
    simp only [Op.cost]

/-- `andFlag` writes only `ZERO`/`GWF` — the hypothesis-free frame fact. -/
private theorem andFlag_frame' (FLG : Nat) (s : State) (r : Var)
    (h1 : r ≠ ZERO) (h2 : r ≠ GWF) :
    State.get ((andFlag FLG).eval s) r = State.get s r := by
  unfold andFlag
  by_cases hT : State.get s FLG = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hT, Cmd.eval_op]
    simp only [Op.eval]
    exact State.get_set_ne _ _ _ _ h1
  · rw [Cmd.eval_ifBit_false _ _ _ _ hT, Cmd.eval_op]
    simp only [Op.eval]
    exact State.get_set_ne _ _ _ _ h2

/-- `andFlag` keeps `ZERO` empty (either branch). -/
private theorem andFlag_ZERO (FLG : Nat) (s : State) (h : State.get s ZERO = []) :
    State.get ((andFlag FLG).eval s) ZERO = [] := by
  unfold andFlag
  by_cases hT : State.get s FLG = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hT, Cmd.eval_op]
    simp only [Op.eval]
    exact State.get_set_eq _ _ _
  · rw [Cmd.eval_ifBit_false _ _ _ _ hT, Cmd.eval_op]
    simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ (show ZERO ≠ GWF by decide)]
    exact h

/-- The final `TFLG`-flip of `leCheck`/`dvdCheck` costs at most 4. -/
private theorem tflgFlip_cost_le (s : State) :
    (Cmd.ifBit TFLG (Cmd.op (.clear TFLG))
      (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))).cost s ≤ 4 := by
  by_cases hT : State.get s TFLG = [1]
  · rw [Cmd.cost_ifBit_true _ _ _ _ hT, Cmd.cost_op]
    simp only [Op.cost]
    omega
  · rw [Cmd.cost_ifBit_false _ _ _ _ hT, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
    simp only [Op.cost]
    omega

/-- **`leCheck` cost**: quadratic in the ceiling `Ω ≥ a, b`. -/
theorem leCheck_cost (X Y : Var) (a b : Nat) (s : State) (Ω : Nat)
    (hYM : Y ≠ MREM)
    (hX : State.get s X = List.replicate a 1)
    (hY : (State.get s Y).length = b)
    (hΩa : a ≤ Ω) (hΩb : b ≤ Ω) :
    (leCheck X Y).cost s ≤ 12 * ((Ω + 1) * (Ω + 1)) := by
  have e1 : (Cmd.op (.copy MREM X)).eval s = s.set MREM (List.replicate a 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hX]
  have hc1 : Op.cost (.copy MREM X) s = a + 1 := by
    show (State.get s X).length + 1 = _
    rw [hX, List.length_replicate]
  set w1 := s.set MREM (List.replicate a 1) with hw1
  have hw1M : State.get w1 MREM = List.replicate a 1 := State.get_set_eq _ _ _
  have hw1Y : (State.get w1 Y).length = b := by
    rw [State.get_set_ne _ _ _ _ hYM]; exact hY
  clear_value w1
  have hcSub := cost_tailLoop_le MGE Y MREM w1 a b (by decide)
    (by rw [hw1M, List.length_replicate]) hw1Y
  set w2 := (Cmd.forBnd MGE Y (Cmd.op (.tail MREM MREM))).eval w1 with hw2
  clear_value w2
  set w3 := (Cmd.op (.nonEmpty TFLG MREM)).eval w2 with hw3
  clear_value w3
  have hc4 := tflgFlip_cost_le w3
  have hcost : (leCheck X Y).cost s
      = 1 + Op.cost (.copy MREM X) s
        + (1 + (Cmd.forBnd MGE Y (Cmd.op (.tail MREM MREM))).cost w1
        + (1 + (Cmd.op (.nonEmpty TFLG MREM)).cost w2
        + (Cmd.ifBit TFLG (Cmd.op (.clear TFLG))
            (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))).cost w3)) := by
    unfold leCheck
    rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq, ← hw3]
  have hc3 : (Cmd.op (.nonEmpty TFLG MREM)).cost w2 = 1 := by
    rw [Cmd.cost_op]
    simp only [Op.cost]
  have hSuble := le_trans hcSub (subLoopClose a b Ω hΩa hΩb)
  rw [hcost, hc1, hc3]
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
  have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
  omega

/-- Per-iteration cost of `dvdCheck`'s outer loop: quadratic in `Ω ≥ a, d`. -/
private theorem dvdBody_effect (a d : Nat) (D : Var) (u : State) (Ω : Nat)
    (hDM : D ≠ MREM) (hDC : D ≠ MCHK) (hDG : D ≠ MGE) (hDK : D ≠ KTMP)
    (hDK2 : D ≠ KTMP2) (hDZ : D ≠ ZERO)
    (hUD : State.get u D = List.replicate d 1)
    (hΩa : a ≤ Ω) (hΩd : d ≤ Ω)
    (j : Nat) (st : State) (h : DInv a d u j st) :
    (dvdBody D).cost (st.set KTMP (List.replicate j 1))
      ≤ 12 * ((Ω + 1) * (Ω + 1)) := by
  obtain ⟨hMREM, hZ, hframe⟩ := h
  set w := st.set KTMP (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KTMP → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwM : State.get w MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hwframe MREM (by decide)]; exact hMREM
  have hwD : State.get w D = List.replicate d 1 := by
    rw [hwframe D hDK, hframe D hDM hDC hDG hDK hDK2 hDZ]; exact hUD
  clear_value w
  have hsub_le : DvdArith.subMod a d j ≤ a := DvdArith.subMod_le a d j
  -- step 1: copy MCHK D
  have e1 : (Cmd.op (.copy MCHK D)).eval w = w.set MCHK (List.replicate d 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hwD]
  have hc1 : Op.cost (.copy MCHK D) w = d + 1 := by
    show (State.get w D).length + 1 = _
    rw [hwD, List.length_replicate]
  set w1 := w.set MCHK (List.replicate d 1) with hw1
  have hw1frame : ∀ r : Var, r ≠ MCHK → State.get w1 r = State.get w r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1C : State.get w1 MCHK = List.replicate d 1 := State.get_set_eq _ _ _
  have hw1M : State.get w1 MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hw1frame MREM (by decide)]; exact hwM
  clear_value w1
  -- step 2: inner sub loop  MCHK -= |MREM|
  have hcSub1 := cost_tailLoop_le KTMP2 MREM MCHK w1 d (DvdArith.subMod a d j)
    (by decide)
    (by rw [hw1C, List.length_replicate])
    (by rw [hw1M, List.length_replicate])
  obtain ⟨hsubC, hsubF⟩ := unarySubLoop_run KTMP2 MREM MCHK w1 d
    (DvdArith.subMod a d j) (by decide)
    (by rw [hw1M, List.length_replicate]) hw1C
  set w2 := (Cmd.forBnd KTMP2 MREM (Cmd.op (.tail MCHK MCHK))).eval w1 with hw2
  have hw2M : State.get w2 MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hsubF MREM (by decide) (by decide)]; exact hw1M
  have hw2D : State.get w2 D = List.replicate d 1 := by
    rw [hsubF D hDC hDK2, hw1frame D hDC]; exact hwD
  clear_value w2
  -- step 3: nonEmpty MGE MCHK
  have e3 : (Cmd.op (.nonEmpty MGE MCHK)).eval w2
      = w2.set MGE (if (List.replicate (d - DvdArith.subMod a d j) 1 : List Nat).isEmpty
          then [0] else [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hsubC]
  set w3 := w2.set MGE (if (List.replicate (d - DvdArith.subMod a d j) 1 : List Nat).isEmpty
      then [0] else [1]) with hw3
  have hw3frame : ∀ r : Var, r ≠ MGE → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3M : State.get w3 MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hw3frame MREM (by decide)]; exact hw2M
  have hw3D : State.get w3 D = List.replicate d 1 := by
    rw [hw3frame D hDG]; exact hw2D
  clear_value w3
  -- step 4: the branch
  have hcBranch : (Cmd.ifBit MGE (Cmd.op (.clear ZERO))
      (Cmd.forBnd KTMP2 D (Cmd.op (.tail MREM MREM)))).cost w3
      ≤ 1 + 3 * ((Ω + 1) * (Ω + 1)) := by
    by_cases hG : State.get w3 MGE = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ hG, Cmd.cost_op]
      simp only [Op.cost]
      have h1P2 : 1 ≤ (Ω + 1) * (Ω + 1) := one_le_P Ω
      omega
    · rw [Cmd.cost_ifBit_false _ _ _ _ hG]
      have hcSub2 := cost_tailLoop_le KTMP2 D MREM w3 (DvdArith.subMod a d j) d
        (by decide)
        (by rw [hw3M, List.length_replicate])
        (by rw [hw3D, List.length_replicate])
      exact Nat.add_le_add_left
        (le_trans hcSub2 (subLoopClose (DvdArith.subMod a d j) d Ω (by omega) hΩd)) 1
  have hcost : (dvdBody D).cost w
      = 1 + Op.cost (.copy MCHK D) w
        + (1 + (Cmd.forBnd KTMP2 MREM (Cmd.op (.tail MCHK MCHK))).cost w1
        + (1 + (Cmd.op (.nonEmpty MGE MCHK)).cost w2
        + (Cmd.ifBit MGE (Cmd.op (.clear ZERO))
            (Cmd.forBnd KTMP2 D (Cmd.op (.tail MREM MREM)))).cost w3)) := by
    unfold dvdBody
    rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq, e3]
  have hc3 : (Cmd.op (.nonEmpty MGE MCHK)).cost w2 = 1 := by
    rw [Cmd.cost_op]
    simp only [Op.cost]
  have hSuble1 := le_trans hcSub1 (subLoopClose d (DvdArith.subMod a d j) Ω hΩd (by omega))
  rw [hcost, hc1, hc3]
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
  have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
  omega

/-- **`dvdCheck` cost**: cubic in the ceiling `Ω ≥ a, d`. -/
theorem dvdCheck_cost (X D : Var) (a d : Nat) (s : State) (Ω : Nat)
    (hXM : X ≠ MREM)
    (hDM : D ≠ MREM) (hDC : D ≠ MCHK) (hDG : D ≠ MGE) (hDK : D ≠ KTMP)
    (hDK2 : D ≠ KTMP2) (hDZ : D ≠ ZERO)
    (hX : State.get s X = List.replicate a 1)
    (hD : State.get s D = List.replicate d 1)
    (hZ : State.get s ZERO = [])
    (hΩa : a ≤ Ω) (hΩd : d ≤ Ω) :
    (dvdCheck X D).cost s ≤ 30 * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) := by
  have e1 : (Cmd.op (.copy MREM X)).eval s = s.set MREM (List.replicate a 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hX]
  have hc1 : Op.cost (.copy MREM X) s = a + 1 := by
    show (State.get s X).length + 1 = _
    rw [hX, List.length_replicate]
  set u := s.set MREM (List.replicate a 1) with hu
  have huframe : ∀ r : Var, r ≠ MREM → State.get u r = State.get s r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have huM : State.get u MREM = List.replicate a 1 := State.get_set_eq _ _ _
  have huD : State.get u D = List.replicate d 1 := by rw [huframe D hDM]; exact hD
  have huZ : State.get u ZERO = [] := by rw [huframe ZERO (by decide)]; exact hZ
  have huX : State.get u X = List.replicate a 1 := by rw [huframe X hXM]; exact hX
  have huXlen : (State.get u X).length = a := by rw [huX, List.length_replicate]
  clear_value u
  have hbase : DInv a d u 0 u := by
    refine ⟨by rw [huM]; rfl, huZ, fun r _ _ _ _ _ _ => rfl⟩
  have hloop := Cmd.cost_forBnd_le KTMP X (dvdBody D) u
    (12 * ((Ω + 1) * (Ω + 1)))
    (DInv a d u) hbase
    (fun j st _ hM => dvdBody_step a d D u hDM hDC hDG hDK hDK2 hDZ huD j st hM)
    (fun j st _ hM => dvdBody_effect a d D u Ω hDM hDC hDG hDK hDK2 hDZ huD
      hΩa hΩd j st hM)
  set w2 := (Cmd.forBnd KTMP X (dvdBody D)).eval u with hw2
  clear_value w2
  set w3 := (Cmd.op (.nonEmpty TFLG MREM)).eval w2 with hw3
  clear_value w3
  have hc4 := tflgFlip_cost_le w3
  have hcost : (dvdCheck X D).cost s
      = 1 + Op.cost (.copy MREM X) s
        + (1 + (Cmd.forBnd KTMP X (dvdBody D)).cost u
        + (1 + (Cmd.op (.nonEmpty TFLG MREM)).cost w2
        + (Cmd.ifBit TFLG (Cmd.op (.clear TFLG))
            (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))).cost w3)) := by
    unfold dvdCheck
    rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq, ← hw3]
  have hc3 : (Cmd.op (.nonEmpty TFLG MREM)).cost w2 = 1 := by
    rw [Cmd.cost_op]
    simp only [Op.cost]
  rw [hcost, hc1, hc3]
  rw [huXlen] at hloop
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  set P3 := (Ω + 1) * P2 with hP3
  have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
  have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
  have haB : a * (12 * P2) ≤ (Ω + 1) * (12 * P2) :=
    Nat.mul_le_mul_right _ (by omega)
  have he3 : (Ω + 1) * (12 * P2) = 12 * P3 := by rw [hP3]; ring
  have haa : a * a ≤ Ω * Ω := Nat.mul_le_mul hΩa hΩa
  have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
  have h1P3 : 1 ≤ P3 := le_trans h1P2 hP23
  omega

/-! ### `cardLenCheck`: cost -/

/-- **`cardLenItem` cost**: quadratic in `Ω ≥ |SCANW|, width`. -/
theorem cardLenItem_cost (bs : List Bool) (rest : List Nat) (width : Nat)
    (u : State) (Ω : Nat)
    (hSC : State.get u SCANW = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs) ++ rest)
    (hW : State.get u WIDTH = List.replicate width 1)
    (hΩS : (State.get u SCANW).length ≤ Ω)
    (hΩw : width ≤ Ω) :
    cardLenItem.cost u
      ≤ (Cmd.flatK cardLenElemBody + 20) * ((Ω + 1) * (Ω + 1)) := by
  have e01 : (Cmd.op (.clear CLEN)).eval u = u.set CLEN [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u1 := u.set CLEN [] with hu1
  have hu1frame : ∀ r : Var, r ≠ CLEN → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  clear_value u1
  have e02 : (Cmd.op (.clear DONE)).eval u1 = u1.set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u2 := u1.set DONE [] with hu2
  have hu2frame : ∀ r : Var, r ≠ DONE → State.get u2 r = State.get u1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu2SC : State.get u2 SCANW
      = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs) ++ rest := by
    rw [hu2frame SCANW (by decide), hu1frame SCANW (by decide)]; exact hSC
  have hu2CL : State.get u2 CLEN = [] := by
    rw [hu2frame CLEN (by decide), hu1]; exact State.get_set_eq _ _ _
  have hu2D : State.get u2 DONE = [] := State.get_set_eq _ _ _
  have hu2W : State.get u2 WIDTH = List.replicate width 1 := by
    rw [hu2frame WIDTH (by decide), hu1frame WIDTH (by decide)]; exact hW
  have hu2SClen : (State.get u2 SCANW).length = (State.get u SCANW).length := by
    rw [hu2SC, hSC]
  clear_value u2
  have hN : bs.length < (State.get u2 SCANW).length := by
    rw [hu2SC, List.length_append, FlatTCCFree.encSList_length,
      show (FlatCCBinFree.bitsNat bs).length = bs.length from List.length_map _]
    omega
  -- the SCANW ceiling in both parse phases
  have hsuffix : ∀ i : Nat,
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bs.drop i))).length + rest.length
        ≤ Ω := by
    intro i
    have h1 : (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bs.drop i))).length
        ≤ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs)).length := by
      rw [show FlatCCBinFree.bitsNat (bs.drop i)
          = (FlatCCBinFree.bitsNat bs).drop i from List.map_drop ..]
      exact encSList_drop_length_le _ i
    have h2 : (State.get u SCANW).length
        = (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs)).length + rest.length := by
      rw [hSC, List.length_append]
    omega
  have hbase : CEInv bs rest u2 0 u2 := by
    refine ⟨fun _ => ⟨hu2D, by rw [List.drop_zero]; exact hu2SC, hu2CL⟩,
      fun hlt => absurd hlt (Nat.not_lt_zero _), fun r _ _ _ _ _ _ _ => rfl⟩
  -- the loop: cost + exit facts
  have hloop := Cmd.cost_forBnd_le KBIT SCANW cardLenElemBody u2
    (Cmd.flatK cardLenElemBody * (Ω + 1))
    (CEInv bs rest u2) hbase
    (fun i st _ hM => CEInv_step bs rest u2 i st hM)
    (fun i st hi hM => by
      obtain ⟨hph1, hph2, hframei⟩ := hM
      have hread : ∀ r ∈ Cmd.costReads cardLenElemBody,
          (State.get (st.set KBIT (List.replicate i 1)) r).length ≤ Ω := by
        intro r hr
        have hlist : Cmd.costReads cardLenElemBody
            = [SCANW, SCANW, SCANW, SCANW, SCANW] := rfl
        rw [hlist] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hSCANce : (State.get st SCANW).length ≤ Ω := by
          by_cases hile : i ≤ bs.length
          · obtain ⟨-, hS, -⟩ := hph1 hile
            rw [hS, List.length_append]
            exact hsuffix i
          · obtain ⟨-, hS, -⟩ := hph2 (by omega)
            rw [hS]
            have := hsuffix 0
            omega
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          (rw [State.get_set_ne _ _ _ _ (show SCANW ≠ KBIT by decide)]; exact hSCANce)
      exact (Cmd.cost_le_flat cardLenElemBody rfl
        (st.set KBIT (List.replicate i 1)) Ω hread).1)
  have hInv : CEInv bs rest u2 (State.get u2 SCANW).length
      (Cmd.foldlState cardLenElemBody KBIT
        (List.range (State.get u2 SCANW).length) u2) :=
    Cmd.foldlState_range_induct _ KBIT _ u2 (CEInv bs rest u2) hbase
      (fun i st _ hM => CEInv_step bs rest u2 i st hM)
  obtain ⟨-, hph2, hLframe⟩ := hInv
  obtain ⟨-, -, hLCL⟩ := hph2 hN
  set w2 := Cmd.foldlState cardLenElemBody KBIT
      (List.range (State.get u2 SCANW).length) u2 with hw2
  clear_value w2
  have hw2W : State.get w2 WIDTH = List.replicate width 1 := by
    rw [hLframe WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hu2W
  -- eqBit cost off the exit lengths
  have hc3 : Op.cost (.eqBit TFLG CLEN WIDTH) w2 = bs.length + width + 1 := by
    show (State.get w2 CLEN).length + (State.get w2 WIDTH).length + 1 = _
    rw [hLCL, hw2W, List.length_replicate, List.length_replicate]
  set w3 := (Cmd.op (.eqBit TFLG CLEN WIDTH)).eval w2 with hw3
  clear_value w3
  have hc4 := andFlag_cost TFLG w3
  have hloopeval : (Cmd.forBnd KBIT SCANW cardLenElemBody).eval u2 = w2 := by
    rw [Cmd.eval_forBnd, hw2]
  have hcost : cardLenItem.cost u
      = 1 + 1 + (1 + 1 + (1 + (Cmd.forBnd KBIT SCANW cardLenElemBody).cost u2
        + (1 + Op.cost (.eqBit TFLG CLEN WIDTH) w2 + (andFlag TFLG).cost w3))) := by
    unfold cardLenItem
    rw [Cmd.cost_seq, Cmd.cost_op, e01, Cmd.cost_seq, Cmd.cost_op, e02, Cmd.cost_seq,
      Cmd.cost_seq, Cmd.cost_op, hloopeval, ← hw3]
    simp only [Op.cost]
  rw [hcost, hc3, hc4]
  -- close the arithmetic
  have hblen : bs.length ≤ Ω := by
    have := hN
    rw [hu2SClen] at this
    omega
  have hlen : (State.get u2 SCANW).length ≤ Ω := by rw [hu2SClen]; omega
  set K := Cmd.flatK cardLenElemBody with hK
  clear_value K
  set A := K * (Ω + 1) with hA
  set len := (State.get u2 SCANW).length with hlenDef
  have h1 : len * A ≤ (Ω + 1) * A := Nat.mul_le_mul_right A (by omega)
  have h2 : len * len ≤ Ω * Ω := Nat.mul_le_mul hlen hlen
  have h3 : (Ω + 1) * A = K * ((Ω + 1) * (Ω + 1)) := by rw [hA]; ring
  have h4 : (K + 20) * ((Ω + 1) * (Ω + 1))
      = K * ((Ω + 1) * (Ω + 1)) + 20 * ((Ω + 1) * (Ω + 1)) := by ring
  have h5 : (Ω + 1) * (Ω + 1) = Ω * Ω + 2 * Ω + 1 := by ring
  omega

/-- Per-iteration cost of `cardLenCheck`'s card loop. -/
private theorem cardLenCardBody_effect (C : BinaryCC) (width : Nat) (g0 : List Nat)
    (u1 : State) (Ω : Nat)
    (hΩS : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length ≤ Ω)
    (hΩw : width ≤ Ω)
    (j : Nat) (st : State) (hInv : CLInv C width g0 u1 j st) :
    cardLenCardBody.cost (st.set KCARD (List.replicate j 1))
      ≤ 6 + 2 * ((Cmd.flatK cardLenElemBody + 20) * ((Ω + 1) * (Ω + 1))) := by
  obtain ⟨hSCAN, hGWF, hWID, hframe⟩ := hInv
  set w := st.set KCARD (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KCARD → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSCAN : State.get w SCANW
      = FlatTCCFree.encCardsOut ((C.cards.drop j).map FlatCCBinFree.cardNat) := by
    rw [hwframe SCANW (by decide)]; exact hSCAN
  have hwWID : State.get w WIDTH = List.replicate width 1 := by
    rw [hwframe WIDTH (by decide)]; exact hWID
  -- the drop-stream ceiling
  have hstream : (FlatTCCFree.encCardsOut ((C.cards.drop j).map FlatCCBinFree.cardNat)).length
      ≤ (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length := by
    rw [show (C.cards.drop j).map FlatCCBinFree.cardNat
        = (C.cards.map FlatCCBinFree.cardNat).drop j from List.map_drop ..]
    exact encCardsOut_drop_length_le _ j
  clear_value w
  by_cases hj : j < C.cards.length
  · -- live: parse prem then conc
    have hdrop : C.cards.drop j = C.cards[j] :: C.cards.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    set c := C.cards[j] with hc
    clear_value c
    set REST := FlatTCCFree.encCardsOut ((C.cards.drop (j + 1)).map FlatCCBinFree.cardNat)
      with hREST
    have hwSCANc : State.get w SCANW
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
          ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hwSCAN, hdrop, encCardsOut_cons, hREST]
    have hne : (State.get w SCANW).isEmpty = false := by
      rw [hwSCANc]; exact encSList_append_isEmpty _ _
    have hwSCANlen : (State.get w SCANW).length ≤ Ω := by
      rw [hwSCAN]
      omega
    have e1 : (Cmd.op (.nonEmpty TFLG SCANW)).eval w = w.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    set w1 := w.set TFLG [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ TFLG → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1T : State.get w1 TFLG = [1] := State.get_set_eq _ _ _
    have hw1SCAN : State.get w1 SCANW
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
          ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hw1frame SCANW (by decide)]; exact hwSCANc
    have hw1WID : State.get w1 WIDTH = List.replicate width 1 := by
      rw [hw1frame WIDTH (by decide)]; exact hwWID
    have hw1SCANlen : (State.get w1 SCANW).length ≤ Ω := by
      rw [hw1SCAN, ← hwSCANc]
      exact hwSCANlen
    clear_value w1
    -- the prem item: cost + run
    have hcost1 := cardLenItem_cost c.prem
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) width w1 Ω
      hw1SCAN hw1WID hw1SCANlen hΩw
    obtain ⟨hp1SC, -, hp1F⟩ := cardLenItem_run c.prem
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST)
      width (State.get w1 GWF) w1 hw1SCAN hw1WID rfl
    set w2 := cardLenItem.eval w1 with hw2
    have hw2SC : State.get w2 SCANW
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST := hp1SC
    have hw2WID : State.get w2 WIDTH = List.replicate width 1 := by
      rw [hp1F WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
      exact hw1WID
    have hw2SClen : (State.get w2 SCANW).length ≤ Ω := by
      rw [hw2SC]
      have : (State.get w1 SCANW).length
          = (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)).length
            + (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST).length := by
        rw [hw1SCAN, List.length_append]
      omega
    clear_value w2
    -- the conc item: cost
    have hcost2 := cardLenItem_cost c.conc REST width w2 Ω hw2SC hw2WID hw2SClen hΩw
    have hcost : cardLenCardBody.cost w
        = 1 + 1 + (1 + (1 + cardLenItem.cost w1 + cardLenItem.cost w2)) := by
      unfold cardLenCardBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_true _ _ _ _ hw1T,
        Cmd.cost_seq, ← hw2]
      simp only [Op.cost]
    rw [hcost]
    set KK := (Cmd.flatK cardLenElemBody + 20) * ((Ω + 1) * (Ω + 1)) with hKK
    clear_value KK
    omega
  · -- idle: stream exhausted
    have hlen : C.cards.length ≤ j := Nat.le_of_not_lt hj
    have hwSCANe : State.get w SCANW = [] := by
      rw [hwSCAN, List.drop_eq_nil_of_le hlen]; rfl
    have hne : (State.get w SCANW).isEmpty = true := by rw [hwSCANe]; rfl
    have e1 : (Cmd.op (.nonEmpty TFLG SCANW)).eval w = w.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    have hw1Tne : State.get (w.set TFLG [0]) TFLG ≠ [1] := by
      rw [State.get_set_eq]; decide
    have hcost : cardLenCardBody.cost w = 1 + 1 + (1 + 1) := by
      unfold cardLenCardBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_false _ _ _ _ hw1Tne,
        Cmd.cost_op]
      simp only [Op.cost]
    rw [hcost]
    omega

/-- **`cardLenCheck` cost**: cubic in `Ω ≥ |CARDS|, width`. -/
theorem cardLenCheck_cost (C : BinaryCC) (u : State) (Ω : Nat)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hW : State.get u WIDTH = List.replicate C.width 1)
    (hΩS : (State.get u CARDS).length ≤ Ω)
    (hΩw : C.width ≤ Ω) :
    cardLenCheck.cost u
      ≤ (2 * Cmd.flatK cardLenElemBody + 60)
          * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) := by
  have e0 : (Cmd.op (.copy SCANW CARDS)).eval u
      = u.set SCANW (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hCARDS]
  have hc0 : Op.cost (.copy SCANW CARDS) u = (State.get u CARDS).length + 1 := by
    show (State.get u CARDS).length + 1 = _
    rfl
  set u1 := u.set SCANW (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    with hu1
  have hu1frame : ∀ r : Var, r ≠ SCANW → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1SC : State.get u1 SCANW
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    State.get_set_eq _ _ _
  have hu1W : State.get u1 WIDTH = List.replicate C.width 1 := by
    rw [hu1frame WIDTH (by decide)]; exact hW
  have hu1CARDSlen : (State.get u1 CARDS).length = (State.get u CARDS).length := by
    rw [hu1frame CARDS (by decide)]
  clear_value u1
  have hcards_le : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length
      = (State.get u CARDS).length := by rw [hCARDS]
  have hbase : CLInv C C.width (State.get u1 GWF) u1 0 u1 := by
    refine ⟨by rw [List.drop_zero]; exact hu1SC, ?_, hu1W,
      fun r _ _ _ _ _ _ _ _ _ _ => rfl⟩
    rw [List.take_zero]; rfl
  have hloop := Cmd.cost_forBnd_le KCARD CARDS cardLenCardBody u1
    (6 + 2 * ((Cmd.flatK cardLenElemBody + 20) * ((Ω + 1) * (Ω + 1))))
    (CLInv C C.width (State.get u1 GWF) u1) hbase
    (fun j st _ hM => CLInv_step C C.width (State.get u1 GWF) u1 j st hM)
    (fun j st _ hM => cardLenCardBody_effect C C.width (State.get u1 GWF) u1 Ω
      (by omega) hΩw j st hM)
  have hcost : cardLenCheck.cost u
      = 1 + Op.cost (.copy SCANW CARDS) u
        + (Cmd.forBnd KCARD CARDS cardLenCardBody).cost u1 := by
    unfold cardLenCheck
    rw [Cmd.cost_seq, Cmd.cost_op, e0]
  rw [hcost, hc0]
  rw [hu1CARDSlen] at hloop
  -- close the arithmetic
  set K := Cmd.flatK cardLenElemBody with hK
  clear_value K
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  set P3 := (Ω + 1) * P2 with hP3
  set len := (State.get u CARDS).length with hlenDef
  have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
  have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
  have h1P3 : 1 ≤ P3 := le_trans h1P2 hP23
  set B := 6 + 2 * ((K + 20) * P2) with hB
  have hBle : B ≤ (2 * K + 46) * P2 := by
    rw [hB]
    have h6 : 6 ≤ 6 * P2 := by omega
    have he : 2 * ((K + 20) * P2) + 6 * P2 = (2 * K + 46) * P2 := by ring
    omega
  have hlB : len * B ≤ (Ω + 1) * ((2 * K + 46) * P2) :=
    Nat.mul_le_mul (by omega) hBle
  have he3 : (Ω + 1) * ((2 * K + 46) * P2) = (2 * K + 46) * P3 := by
    rw [hP3]; ring
  have hll : len * len ≤ Ω * Ω := Nat.mul_le_mul hΩS hΩS
  have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
  have hfin : (2 * K + 60) * P3 = (2 * K + 46) * P3 + 14 * P3 := by ring
  omega

/-- **`computeWF` cost**: cubic in the ceiling `Ω`, which must dominate the
four scalar inputs (`width`/`offset`/`L`/`|CARDS|`). Straight-line walk of
`computeWF_run`'s spine. -/
theorem computeWF_cost (C : BinaryCC) (u : State) (Ω : Nat)
    (hW : State.get u WIDTH = List.replicate C.width 1)
    (hO : State.get u OFFSET = List.replicate C.offset 1)
    (hL : State.get u LREG = List.replicate C.init.length 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = [])
    (hΩ : C.width + C.offset + C.init.length + (State.get u CARDS).length ≤ Ω) :
    computeWF.cost u
      ≤ (2 * Cmd.flatK cardLenElemBody + 160)
          * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) := by
  -- the spine states
  set t0 := (Cmd.op (.clear GWF)).eval u with ht0
  set t1 := (Cmd.op (.appendOne GWF)).eval t0 with ht1
  set t2 := (Cmd.op (.nonEmpty TFLG WIDTH)).eval t1 with ht2
  set t3 := (andFlag TFLG).eval t2 with ht3
  set t4 := (Cmd.op (.nonEmpty TFLG OFFSET)).eval t3 with ht4
  set t5 := (andFlag TFLG).eval t4 with ht5
  set t6 := (leCheck WIDTH LREG).eval t5 with ht6
  set t7 := (andFlag TFLG).eval t6 with ht7
  set t8 := (dvdCheck WIDTH OFFSET).eval t7 with ht8
  set t9 := (andFlag TFLG).eval t8 with ht9
  set t10 := (dvdCheck LREG OFFSET).eval t9 with ht10
  set t11 := (andFlag TFLG).eval t10 with ht11
  -- per-fragment frames
  have ht0f : ∀ r : Var, r ≠ GWF → State.get t0 r = State.get u r := by
    intro r hr; rw [ht0, Cmd.eval_op]; exact Op.eval_get_ne_writesTo _ _ _ hr
  have ht1f : ∀ r : Var, r ≠ GWF → State.get t1 r = State.get t0 r := by
    intro r hr; rw [ht1, Cmd.eval_op]; exact Op.eval_get_ne_writesTo _ _ _ hr
  have ht2f : ∀ r : Var, r ≠ TFLG → State.get t2 r = State.get t1 r := by
    intro r hr; rw [ht2, Cmd.eval_op]; exact Op.eval_get_ne_writesTo _ _ _ hr
  have ht4f : ∀ r : Var, r ≠ TFLG → State.get t4 r = State.get t3 r := by
    intro r hr; rw [ht4, Cmd.eval_op]; exact Op.eval_get_ne_writesTo _ _ _ hr
  -- registers threaded to t5
  have hchain5 : ∀ r : Var, r ≠ GWF → r ≠ TFLG → r ≠ ZERO →
      State.get t5 r = State.get u r := by
    intro r h1 h2 h3
    rw [ht5, andFlag_frame' TFLG t4 r h3 h1, ht4f r h2, ht3,
      andFlag_frame' TFLG t2 r h3 h1, ht2f r h2, ht1f r h1, ht0f r h1]
  have ht5W : State.get t5 WIDTH = List.replicate C.width 1 :=
    (hchain5 WIDTH (by decide) (by decide) (by decide)).trans hW
  have ht5O : State.get t5 OFFSET = List.replicate C.offset 1 :=
    (hchain5 OFFSET (by decide) (by decide) (by decide)).trans hO
  have ht5L : State.get t5 LREG = List.replicate C.init.length 1 :=
    (hchain5 LREG (by decide) (by decide) (by decide)).trans hL
  have ht5C : State.get t5 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    (hchain5 CARDS (by decide) (by decide) (by decide)).trans hCARDS
  have ht5Llen : (State.get t5 LREG).length = C.init.length := by
    rw [ht5L, List.length_replicate]
  have ht5Z : State.get t5 ZERO = [] := by
    rw [ht5]
    refine andFlag_ZERO TFLG t4 ?_
    rw [ht4f ZERO (by decide), ht3]
    refine andFlag_ZERO TFLG t2 ?_
    rw [ht2f ZERO (by decide), ht1f ZERO (by decide), ht0f ZERO (by decide)]
    exact hZ
  -- through leCheck (write set is register-concrete)
  have ht6f : ∀ r : Var, r ∉ Cmd.writes (leCheck WIDTH LREG) →
      State.get t6 r = State.get t5 r := by
    intro r hr; rw [ht6]; exact Cmd.eval_get_of_not_writes _ _ _ hr
  have ht6W : State.get t6 WIDTH = List.replicate C.width 1 :=
    (ht6f WIDTH (by decide)).trans ht5W
  have ht6O : State.get t6 OFFSET = List.replicate C.offset 1 :=
    (ht6f OFFSET (by decide)).trans ht5O
  have ht6L : State.get t6 LREG = List.replicate C.init.length 1 :=
    (ht6f LREG (by decide)).trans ht5L
  have ht6C : State.get t6 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    (ht6f CARDS (by decide)).trans ht5C
  have ht6Z : State.get t6 ZERO = [] := (ht6f ZERO (by decide)).trans ht5Z
  -- t7 = andFlag
  have ht7W : State.get t7 WIDTH = List.replicate C.width 1 := by
    rw [ht7, andFlag_frame' TFLG t6 WIDTH (by decide) (by decide)]; exact ht6W
  have ht7O : State.get t7 OFFSET = List.replicate C.offset 1 := by
    rw [ht7, andFlag_frame' TFLG t6 OFFSET (by decide) (by decide)]; exact ht6O
  have ht7L : State.get t7 LREG = List.replicate C.init.length 1 := by
    rw [ht7, andFlag_frame' TFLG t6 LREG (by decide) (by decide)]; exact ht6L
  have ht7C : State.get t7 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [ht7, andFlag_frame' TFLG t6 CARDS (by decide) (by decide)]; exact ht6C
  have ht7Z : State.get t7 ZERO = [] := by
    rw [ht7]; exact andFlag_ZERO TFLG t6 ht6Z
  -- t8 = dvdCheck WIDTH OFFSET
  obtain ⟨-, hdv1Z, hdv1F⟩ := dvdCheck_run WIDTH OFFSET C.width C.offset t7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ht7W ht7O ht7Z
  have ht8f : ∀ r : Var, r ≠ MREM → r ≠ MCHK → r ≠ MGE → r ≠ KTMP → r ≠ KTMP2 →
      r ≠ ZERO → r ≠ TFLG → State.get t8 r = State.get t7 r := by
    intro r h1 h2 h3 h4 h5 h6 h7; rw [ht8]; exact hdv1F r h1 h2 h3 h4 h5 h6 h7
  have ht8Z : State.get t8 ZERO = [] := by rw [ht8]; exact hdv1Z
  have ht8W : State.get t8 WIDTH = List.replicate C.width 1 :=
    (ht8f WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht7W
  have ht8O : State.get t8 OFFSET = List.replicate C.offset 1 :=
    (ht8f OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht7O
  have ht8L : State.get t8 LREG = List.replicate C.init.length 1 :=
    (ht8f LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht7L
  have ht8C : State.get t8 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    (ht8f CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht7C
  -- t9 = andFlag
  have ht9O : State.get t9 OFFSET = List.replicate C.offset 1 := by
    rw [ht9, andFlag_frame' TFLG t8 OFFSET (by decide) (by decide)]; exact ht8O
  have ht9L : State.get t9 LREG = List.replicate C.init.length 1 := by
    rw [ht9, andFlag_frame' TFLG t8 LREG (by decide) (by decide)]; exact ht8L
  have ht9W : State.get t9 WIDTH = List.replicate C.width 1 := by
    rw [ht9, andFlag_frame' TFLG t8 WIDTH (by decide) (by decide)]; exact ht8W
  have ht9C : State.get t9 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [ht9, andFlag_frame' TFLG t8 CARDS (by decide) (by decide)]; exact ht8C
  have ht9Z : State.get t9 ZERO = [] := by
    rw [ht9]; exact andFlag_ZERO TFLG t8 ht8Z
  -- t10 = dvdCheck LREG OFFSET
  obtain ⟨-, -, hdv2F⟩ := dvdCheck_run LREG OFFSET C.init.length C.offset t9
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ht9L ht9O ht9Z
  have ht10f : ∀ r : Var, r ≠ MREM → r ≠ MCHK → r ≠ MGE → r ≠ KTMP → r ≠ KTMP2 →
      r ≠ ZERO → r ≠ TFLG → State.get t10 r = State.get t9 r := by
    intro r h1 h2 h3 h4 h5 h6 h7; rw [ht10]; exact hdv2F r h1 h2 h3 h4 h5 h6 h7
  have ht10W : State.get t10 WIDTH = List.replicate C.width 1 :=
    (ht10f WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht9W
  have ht10C : State.get t10 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    (ht10f CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht9C
  -- t11 = andFlag
  have ht11W : State.get t11 WIDTH = List.replicate C.width 1 := by
    rw [ht11, andFlag_frame' TFLG t10 WIDTH (by decide) (by decide)]; exact ht10W
  have ht11C : State.get t11 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [ht11, andFlag_frame' TFLG t10 CARDS (by decide) (by decide)]; exact ht10C
  have ht11Clen : (State.get t11 CARDS).length ≤ Ω := by
    rw [ht11C, ← hCARDS]; omega
  -- the four check costs
  have hle := leCheck_cost WIDTH LREG C.width C.init.length t5 Ω (by decide)
    ht5W ht5Llen (by omega) (by omega)
  have hdv1 := dvdCheck_cost WIDTH OFFSET C.width C.offset t7 Ω (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ht7W ht7O ht7Z (by omega) (by omega)
  have hdv2 := dvdCheck_cost LREG OFFSET C.init.length C.offset t9 Ω (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ht9L ht9O ht9Z (by omega) (by omega)
  have hcl := cardLenCheck_cost C t11 Ω ht11C ht11W ht11Clen (by omega)
  -- assemble the cost
  have hcost : computeWF.cost u
      = 1 + 1 + (1 + 1 + (1 + 1 + (1 + (andFlag TFLG).cost t2
        + (1 + 1 + (1 + (andFlag TFLG).cost t4
        + (1 + (leCheck WIDTH LREG).cost t5
        + (1 + (andFlag TFLG).cost t6
        + (1 + (dvdCheck WIDTH OFFSET).cost t7
        + (1 + (andFlag TFLG).cost t8
        + (1 + (dvdCheck LREG OFFSET).cost t9
        + (1 + (andFlag TFLG).cost t10
        + cardLenCheck.cost t11))))))))))) := by
    unfold computeWF
    rw [Cmd.cost_seq, Cmd.cost_op, ← ht0, Cmd.cost_seq, Cmd.cost_op, ← ht1,
      Cmd.cost_seq, Cmd.cost_op, ← ht2, Cmd.cost_seq, ← ht3,
      Cmd.cost_seq, Cmd.cost_op, ← ht4, Cmd.cost_seq, ← ht5,
      Cmd.cost_seq, ← ht6, Cmd.cost_seq, ← ht7, Cmd.cost_seq, ← ht8,
      Cmd.cost_seq, ← ht9, Cmd.cost_seq, ← ht10, Cmd.cost_seq, ← ht11]
    simp only [Op.cost]
  rw [hcost, andFlag_cost TFLG t2, andFlag_cost TFLG t4, andFlag_cost TFLG t6,
    andFlag_cost TFLG t8, andFlag_cost TFLG t10]
  -- close the arithmetic
  have hleB := hle
  have hdv1B := hdv1
  have hdv2B := hdv2
  have hclB := hcl
  set K := Cmd.flatK cardLenElemBody with hK
  clear_value K
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  set P3 := (Ω + 1) * P2 with hP3
  set c5 := (leCheck WIDTH LREG).cost t5 with hc5
  clear_value c5
  set c7 := (dvdCheck WIDTH OFFSET).cost t7 with hc7
  clear_value c7
  set c9 := (dvdCheck LREG OFFSET).cost t9 with hc9
  clear_value c9
  set c11 := cardLenCheck.cost t11 with hc11
  clear_value c11
  have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
  have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
  have h1P3 : 1 ≤ P3 := le_trans h1P2 hP23
  have h12 : 12 * P2 ≤ 12 * P3 := Nat.mul_le_mul_left _ hP23
  have hfin : (2 * K + 160) * P3 = (2 * K + 60) * P3 + 100 * P3 := by ring
  omega

/-! ### The `buildFSAT` cost assembly — the witness's `cost_le` obligation -/

/-- **`precompLen` cost**: quadratic in `Ω ≥ L`. -/
theorem precompLen_cost (bs : List Bool) (u : State) (Ω : Nat)
    (hINIT : State.get u INIT = FlatCCBinFree.bitsNat bs)
    (hΩ : bs.length ≤ Ω) :
    precompLen.cost u ≤ 8 * ((Ω + 1) * (Ω + 1)) := by
  have e1 : (Cmd.op (.clear LREG)).eval u = u.set LREG [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w1 := u.set LREG [] with hw1
  have hw1L : State.get w1 LREG = [] := State.get_set_eq _ _ _
  have hw1I : (State.get w1 INIT).length = bs.length := by
    rw [State.get_set_ne _ _ _ _ (show INIT ≠ LREG by decide), hINIT]
    exact List.length_map _
  clear_value w1
  have hcLoop := cost_constLoop_le KTMP INIT (Cmd.op (.appendOne LREG)) rfl rfl w1
    bs.length hw1I
  have hKop : Cmd.flatK (Cmd.op (.appendOne LREG)) = 5 := rfl
  rw [hKop] at hcLoop
  -- LREG length at loop exit (for the copy's cost)
  have hInv := Cmd.foldlState_range_induct (Cmd.op (.appendOne LREG)) KTMP bs.length w1
    (fun i st => (State.get st LREG).length ≤ i)
    (by show (State.get w1 LREG).length ≤ 0; simp [hw1L])
    (fun i st _ hM => by
      show (State.get ((Cmd.op (.appendOne LREG)).eval
        (st.set KTMP (List.replicate i 1))) LREG).length ≤ i + 1
      rw [Cmd.eval_op]
      simp only [Op.eval]
      rw [State.get_set_eq,
        State.get_set_ne _ _ _ _ (show LREG ≠ KTMP by decide),
        List.length_append]
      simpa using hM)
  have heval0 : (Cmd.forBnd KTMP INIT (Cmd.op (.appendOne LREG))).eval w1
      = Cmd.foldlState (Cmd.op (.appendOne LREG)) KTMP (List.range bs.length) w1 := by
    rw [Cmd.eval_forBnd, hw1I]
  set w2 := (Cmd.forBnd KTMP INIT (Cmd.op (.appendOne LREG))).eval w1 with hw2
  have hw2Llen : (State.get w2 LREG).length ≤ bs.length := by
    rw [heval0]; exact hInv
  clear_value w2
  have hc3 : Op.cost (.copy LREG1 LREG) w2 ≤ bs.length + 1 := by
    show (State.get w2 LREG).length + 1 ≤ _
    omega
  set w3 := (Cmd.op (.copy LREG1 LREG)).eval w2 with hw3
  clear_value w3
  have hcost : precompLen.cost u
      = 1 + 1 + (1 + (Cmd.forBnd KTMP INIT (Cmd.op (.appendOne LREG))).cost w1
        + (1 + Op.cost (.copy LREG1 LREG) w2 + 1)) := by
    unfold precompLen
    rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq,
      Cmd.cost_op, ← hw3, Cmd.cost_op]
    simp only [Op.cost]
  rw [hcost]
  have hP2exp : (Ω + 1) * (Ω + 1) = Ω * Ω + 2 * Ω + 1 := by ring
  have hbb : bs.length * bs.length ≤ Ω * Ω := Nat.mul_le_mul hΩ hΩ
  omega

/-- The master cost ceiling (`n := encodable.size C`): dominates the serialized
output length (`≤ 4·(500·n⁶+500)` via `serF_length_le_size` +
`BinaryCC_to_FSAT_instance_size_bound`), every variable index, every stream
length, and every per-emitter index sum on `encodeIn C`. -/
def masterOmega (n : Nat) : Nat := 2000 * (n + 1) ^ 6

/-- The total symbolic cost coefficient of `buildFSAT` (never evaluate the
`flatK` numerals — only `inOPoly` matters). -/
def buildFSATK : Nat :=
  2 * Cmd.flatK (sentBitBody 0) + 2 * Cmd.flatK (bsBody 0)
    + Cmd.flatK readFinBody + 2 * Cmd.flatK cardLenElemBody + 1000

/-- The witness's `cost_bound`: `buildFSATK · (masterOmega n + 1)^5`. -/
def buildFSATBound (n : Nat) : Nat :=
  buildFSATK * ((masterOmega n + 1) * ((masterOmega n + 1) * ((masterOmega n + 1)
    * ((masterOmega n + 1) * (masterOmega n + 1)))))

theorem buildFSATBound_poly : inOPoly buildFSATBound := by
  refine ⟨30, ⟨buildFSATK * 128064 ^ 5, 1, ?_⟩⟩
  intro n hn
  have h1 : masterOmega n + 1 ≤ 128064 * n ^ 6 := by
    unfold masterOmega
    have h2 : (n + 1) ^ 6 ≤ (2 * n) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have h3 : (2 * n) ^ 6 = 64 * n ^ 6 := by ring
    have h4 : 1 ≤ n ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  calc buildFSATBound n
      ≤ buildFSATK * ((128064 * n ^ 6) * ((128064 * n ^ 6) * ((128064 * n ^ 6)
          * ((128064 * n ^ 6) * (128064 * n ^ 6))))) := by
        unfold buildFSATBound
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 (Nat.mul_le_mul h1
          (Nat.mul_le_mul h1 (Nat.mul_le_mul h1 h1))))
    _ = buildFSATK * 128064 ^ 5 * n ^ 30 := by ring

theorem buildFSATBound_mono : monotonic buildFSATBound := by
  intro a b h
  unfold buildFSATBound
  have hm : masterOmega a + 1 ≤ masterOmega b + 1 := by
    unfold masterOmega
    have := Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 6
    omega
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hm (Nat.mul_le_mul hm
    (Nat.mul_le_mul hm (Nat.mul_le_mul hm hm))))

/-- The output size is dominated by the cost bound (the witness's
`output_size_le`). -/
theorem buildFSATBound_output (C : BinaryCC) :
    encodable.size (BinaryCC_to_FSAT_instance C)
      ≤ buildFSATBound (encodable.size C) := by
  set n := encodable.size C with hn
  have h1 := BinaryCC_to_FSAT_instance_size_bound C
  rw [← hn] at h1
  have hle : n ^ 6 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have h1p : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h3 : 500 * n ^ 6 + 500 ≤ masterOmega n := by
    unfold masterOmega
    omega
  have h4 : masterOmega n ≤ buildFSATBound n := by
    unfold buildFSATBound
    have hK : 1000 ≤ buildFSATK := by unfold buildFSATK; omega
    have hrest : masterOmega n + 1
        ≤ (masterOmega n + 1) * ((masterOmega n + 1) * ((masterOmega n + 1)
          * ((masterOmega n + 1) * (masterOmega n + 1)))) := by
      have h1p : 1 ≤ (masterOmega n + 1) * ((masterOmega n + 1)
          * ((masterOmega n + 1) * (masterOmega n + 1))) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _)
          (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      calc masterOmega n + 1 = (masterOmega n + 1) * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h1p
    calc masterOmega n ≤ 1 * (masterOmega n + 1) := by omega
      _ ≤ buildFSATK * ((masterOmega n + 1) * ((masterOmega n + 1)
          * ((masterOmega n + 1) * ((masterOmega n + 1) * (masterOmega n + 1))))) :=
        Nat.mul_le_mul (by omega) hrest
  omega

set_option maxRecDepth 4000 in
/-- **`buildFSAT` cost is polynomial** — the `cost_le` crux of the
`BinaryCC ⪯p' FSAT` witness. The whole accounting is instantiated at the ONE
master ceiling `Ω := masterOmega (encodable.size C)`. -/
theorem buildFSAT_cost_le (C : BinaryCC) :
    buildFSAT.cost (encodeIn C) ≤ buildFSATBound (encodable.size C) := by
  classical
  set n := encodable.size C with hn
  set Ω := masterOmega n with hΩdef
  -- component bounds off the instance size
  have hCsz : n = C.offset + C.width + encodable.size C.init
      + encodable.size C.cards + encodable.size C.final + C.steps + 1 := rfl
  have hLn : C.init.length ≤ n :=
    le_trans (list_length_le_size C.init) (by omega)
  have hoffn : C.offset ≤ n := by omega
  have hwidn : C.width ≤ n := by omega
  have hstepsn : C.steps ≤ n := by omega
  have hcardsn : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length
      ≤ 2 * n := by
    have h := FlatCCBinFree.encCardsOut_length_le (C.cards.map FlatCCBinFree.cardNat)
    rw [encodable_size_map_cardNat] at h
    omega
  have hfinaln : (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length
      ≤ 2 * n := by
    have h := FlatTCCFree.encFinal_length_le (C.final.map FlatCCBinFree.bitsNat)
    rw [encodable_size_map_bitsNat] at h
    omega
  have hsLn : C.steps * C.init.length ≤ n * n := Nat.mul_le_mul hstepsn hLn
  have hLon : C.init.length * C.offset ≤ n * n := Nat.mul_le_mul hLn hoffn
  -- `n ≤ n*n` lets omega bridge the linear and quadratic index terms
  have hn_nn : n ≤ n * n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left n h
  -- the quadratic dominator (generous: every index sum is `≤ 20·n²`)
  have hΩquad : 20 * (n * n) ≤ Ω := by
    rw [hΩdef]
    unfold masterOmega
    have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    omega
  -- the serF split of the tableau
  have hserFsplit : serF (encodeTableau C)
      = [0, 1] ++ (serF (encodeBitsAt 0 C.init)
        ++ ([0, 1] ++ (serF (encodeAllStepConstraints C)
          ++ serF (encodeFinalConstraint C)))) := by
    show serF (.fand (encodeBitsAt 0 C.init)
        (.fand (encodeAllStepConstraints C) (encodeFinalConstraint C))) = _
    simp [serF, List.append_assoc]
  have hserFlen : (serF (encodeTableau C)).length
      = 4 + (serF (encodeBitsAt 0 C.init)).length
        + (serF (encodeAllStepConstraints C)).length
        + (serF (encodeFinalConstraint C)).length := by
    rw [hserFsplit]
    simp [List.length_append]
    omega
  -- the pinned input frame (definitional)
  have h0STEPS : State.get (encodeIn C) STEPS = List.replicate C.steps 1 := rfl
  have h0OFF : State.get (encodeIn C) OFFSET = List.replicate C.offset 1 := rfl
  have h0WID : State.get (encodeIn C) WIDTH = List.replicate C.width 1 := rfl
  have h0INIT : State.get (encodeIn C) INIT = FlatCCBinFree.bitsNat C.init := rfl
  have h0CARDS : State.get (encodeIn C) CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := rfl
  have h0FINAL : State.get (encodeIn C) FINAL
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := rfl
  have h0ZERO : State.get (encodeIn C) ZERO = [] := rfl
  have h0WREG : State.get (encodeIn C) WREG = [] := rfl
  -- u1 : precompLen (run + cost)
  have hcPre := precompLen_cost C.init (encodeIn C) Ω h0INIT (by omega)
  obtain ⟨hpL, hpL1, hpF⟩ := precompLen_run C.init (encodeIn C) h0INIT
  set u1 := precompLen.eval (encodeIn C) with hu1
  have h1STEPS := (hpF STEPS (by decide) (by decide) (by decide)).trans h0STEPS
  have h1OFF := (hpF OFFSET (by decide) (by decide) (by decide)).trans h0OFF
  have h1WID := (hpF WIDTH (by decide) (by decide) (by decide)).trans h0WID
  have h1INIT := (hpF INIT (by decide) (by decide) (by decide)).trans h0INIT
  have h1CARDS := (hpF CARDS (by decide) (by decide) (by decide)).trans h0CARDS
  have h1FINAL := (hpF FINAL (by decide) (by decide) (by decide)).trans h0FINAL
  have h1ZERO := (hpF ZERO (by decide) (by decide) (by decide)).trans h0ZERO
  have h1WREG := (hpF WREG (by decide) (by decide) (by decide)).trans h0WREG
  clear_value u1
  -- u2 : computeWF (run + cost)
  have hcWF := computeWF_cost C u1 Ω h1WID h1OFF hpL h1CARDS h1ZERO
    (by rw [h1CARDS]; omega)
  obtain ⟨hwG, hwF⟩ := computeWF_run C u1 h1WID h1OFF hpL h1CARDS h1ZERO
  set u2 := computeWF.eval u1 with hu2
  have h2STEPS := (hwF STEPS (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1STEPS
  have h2OFF := (hwF OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1OFF
  have h2WID := (hwF WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1WID
  have h2INIT := (hwF INIT (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1INIT
  have h2CARDS := (hwF CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1CARDS
  have h2FINAL := (hwF FINAL (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1FINAL
  have h2LREG := (hwF LREG (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hpL
  have h2LREG1 := (hwF LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hpL1
  have h2WREG := (hwF WREG (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1WREG
  clear_value u2
  -- u3 : clear OUT
  have e3 : (Cmd.op (.clear OUT)).eval u2 = u2.set OUT [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u3 := u2.set OUT [] with hu3
  have h3f : ∀ r : Var, r ≠ OUT → State.get u3 r = State.get u2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have h3OUT : State.get u3 OUT = [] := State.get_set_eq _ _ _
  have h3GWF : State.get u3 GWF = (if BinaryCC_wellformed C then [1] else []) :=
    (h3f GWF (by decide)).trans hwG
  have h3STEPS := (h3f STEPS (by decide)).trans h2STEPS
  have h3OFF := (h3f OFFSET (by decide)).trans h2OFF
  have h3WID := (h3f WIDTH (by decide)).trans h2WID
  have h3INIT := (h3f INIT (by decide)).trans h2INIT
  have h3CARDS := (h3f CARDS (by decide)).trans h2CARDS
  have h3FINAL := (h3f FINAL (by decide)).trans h2FINAL
  have h3LREG := (h3f LREG (by decide)).trans h2LREG
  have h3LREG1 := (h3f LREG1 (by decide)).trans h2LREG1
  have h3WREG := (h3f WREG (by decide)).trans h2WREG
  clear_value u3
  -- peel the top-level cost down to the branch
  set vIf := (Cmd.ifBit GWF
      ( emitFandTag ;;
        Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
        emitBitsFromScan ZERO INIT ;;
        emitFandTag ;;
        emitAllSteps ;;
        emitFinal )
      emitFalse).eval u3 with hvIf
  have hcost : buildFSAT.cost (encodeIn C)
      = 1 + precompLen.cost (encodeIn C)
      + (1 + computeWF.cost u1
      + (1 + 1
      + (1 + (Cmd.ifBit GWF
          ( emitFandTag ;;
            Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
            emitBitsFromScan ZERO INIT ;;
            emitFandTag ;;
            emitAllSteps ;;
            emitFinal )
          emitFalse).cost u3
      + ((State.get vIf OUT).length + 1)))) := by
    unfold buildFSAT
    rw [Cmd.cost_seq, ← hu1, Cmd.cost_seq, ← hu2, Cmd.cost_seq, Cmd.cost_op, e3,
      Cmd.cost_seq, ← hvIf, Cmd.cost_op]
    simp only [Op.cost]
  rw [hcost]
  by_cases hWf : BinaryCC_wellformed C
  · -- wellformed: the emitter branch
    have hGeq : State.get u3 GWF = [1] := by rw [h3GWF, if_pos hWf]
    -- the serialization-length dominator (needed by every emitter's OUT ceiling)
    have hTabΩ : (serF (encodeTableau C)).length ≤ Ω := by
      have hEq : BinaryCC_to_FSAT_instance C = encodeTableau C := by
        unfold BinaryCC_to_FSAT_instance; rw [dif_pos hWf]
      have hlen := serF_length_le_size (BinaryCC_to_FSAT_instance C)
      rw [hEq] at hlen
      have hsz := BinaryCC_to_FSAT_instance_size_bound C
      rw [hEq, ← hn] at hsz
      have hle6 : n ^ 6 < (n + 1) ^ 6 :=
        Nat.pow_lt_pow_left (show n < n + 1 by omega) (by norm_num)
      rw [hΩdef]; unfold masterOmega
      omega
    -- the three top-level serF parts each fit under Ω (via the split + hTabΩ)
    have hTabΩsplit : 4 + (serF (encodeBitsAt 0 C.init)).length
        + (serF (encodeAllStepConstraints C)).length
        + (serF (encodeFinalConstraint C)).length ≤ Ω := by
      rw [← hserFlen]; exact hTabΩ
    have hbitsΩ : (serF (encodeBitsAt 0 C.init)).length ≤ Ω := by omega
    have hstepsΩ : (serF (encodeAllStepConstraints C)).length ≤ Ω := by omega
    have hfinalΩ : (serF (encodeFinalConstraint C)).length ≤ Ω := by omega
    -- v1 : emitFandTag
    have e_v1 : emitFandTag.eval u3 = u3.set OUT [0, 1] := by
      rw [emitFandTag_run, h3OUT, List.nil_append]
    set v1 := u3.set OUT [0, 1] with hv1
    have hv1f : ∀ r : Var, r ≠ OUT → State.get v1 r = State.get u3 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv1OUT : State.get v1 OUT = [0, 1] := State.get_set_eq _ _ _
    clear_value v1
    -- v2 : clear ZERO
    have e_v2 : (Cmd.op (.clear ZERO)).eval v1 = v1.set ZERO [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    set v2 := v1.set ZERO [] with hv2
    have hv2f : ∀ r : Var, r ≠ ZERO → State.get v2 r = State.get v1 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv2ZERO : State.get v2 ZERO = [] := State.get_set_eq _ _ _
    clear_value v2
    -- v3 : copy SCAN INIT
    have h2INITv : State.get v2 INIT = FlatCCBinFree.bitsNat C.init := by
      rw [hv2f INIT (by decide), hv1f INIT (by decide)]; exact h3INIT
    have e_v3 : (Cmd.op (.copy SCAN INIT)).eval v2
        = v2.set SCAN (FlatCCBinFree.bitsNat C.init) := by
      rw [Cmd.eval_op]; simp only [Op.eval, h2INITv]
    have hc_v3 : Op.cost (.copy SCAN INIT) v2 = C.init.length + 1 := by
      show (State.get v2 INIT).length + 1 = _
      rw [h2INITv]
      exact congrArg (· + 1) (List.length_map _)
    set v3 := v2.set SCAN (FlatCCBinFree.bitsNat C.init) with hv3
    have hv3f : ∀ r : Var, r ≠ SCAN → State.get v3 r = State.get v2 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv3SCAN : State.get v3 SCAN = FlatCCBinFree.bitsNat C.init :=
      State.get_set_eq _ _ _
    clear_value v3
    -- v4 : emitBitsFromScan (run + cost + WREG)
    have h3ZEROv : State.get v3 ZERO = List.replicate 0 1 := by
      rw [hv3f ZERO (by decide)]; exact hv2ZERO
    have h3INITlen : (State.get v3 INIT).length = C.init.length := by
      rw [hv3f INIT (by decide), h2INITv]
      exact List.length_map _
    have h3OUTv : State.get v3 OUT = [0, 1] := by
      rw [hv3f OUT (by decide), hv2f OUT (by decide)]; exact hv1OUT
    have h3WREGv : State.get v3 WREG = [] := by
      rw [hv3f WREG (by decide), hv2f WREG (by decide), hv1f WREG (by decide)]
      exact h3WREG
    have hcScan := emitBitsFromScan_cost ZERO INIT 0 C.init v3 Ω
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h3ZEROv h3INITlen hv3SCAN
      (by rw [h3OUTv]
          simp only [List.length_cons, List.length_nil]
          omega)
      (by rw [h3WREGv]; exact Nat.zero_le Ω)
      (by omega)
    have hWScan := emitBitsFromScan_WREG ZERO INIT v3 Ω
      (by decide) (by decide) (by decide) (by decide)
      (by rw [h3WREGv]; exact Nat.zero_le Ω)
      (by rw [h3ZEROv, h3INITlen]
          simp only [List.length_replicate]
          omega)
    obtain ⟨h4SCAN, h4OUT, h4F⟩ := emitBitsFromScan_run ZERO INIT 0 C.init v3
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h3ZEROv h3INITlen hv3SCAN
    set v4 := (emitBitsFromScan ZERO INIT).eval v3 with hv4
    have h4OUTval : State.get v4 OUT = [0, 1] ++ serF (encodeBitsAt 0 C.init) := by
      rw [h4OUT, h3OUTv]
    have h4WREG : (State.get v4 WREG).length ≤ Ω := hWScan
    clear_value v4
    -- v5 : emitFandTag
    have e_v5 : emitFandTag.eval v4
        = v4.set OUT (([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1]) := by
      rw [emitFandTag_run, h4OUTval]
    set v5 := v4.set OUT (([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1]) with hv5
    have hv5f : ∀ r : Var, r ≠ OUT → State.get v5 r = State.get v4 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv5OUT : State.get v5 OUT
        = ([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1] := State.get_set_eq _ _ _
    clear_value v5
    -- register threading u3 → v5
    have hv5chain : ∀ r : Var, r ≠ OUT → r ≠ ZERO → r ≠ SCAN → r ≠ WREG → r ≠ TFLG →
        r ≠ KBIT → State.get v5 r = State.get u3 r := by
      intro r h1 h2 h3 h4 h5 h6
      rw [hv5f r h1, h4F r h3 h1 h4 h5 h6, hv3f r h3, hv2f r h2, hv1f r h1]
    have h5STEPS := (hv5chain STEPS (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3STEPS
    have h5OFF := (hv5chain OFFSET (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3OFF
    have h5WID := (hv5chain WIDTH (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3WID
    have h5CARDS := (hv5chain CARDS (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3CARDS
    have h5FINAL := (hv5chain FINAL (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3FINAL
    have h5LREG := (hv5chain LREG (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3LREG
    have h5LREG1 := (hv5chain LREG1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3LREG1
    have h5ZERO : State.get v5 ZERO = [] := by
      rw [hv5f ZERO (by decide), h4F ZERO (by decide) (by decide) (by decide)
        (by decide) (by decide), hv3f ZERO (by decide)]
      exact hv2ZERO
    have h5WREG : (State.get v5 WREG).length ≤ Ω := by
      rw [hv5f WREG (by decide)]; exact h4WREG
    -- v6 : emitAllSteps (run + cost + WREG exit)
    have hΩO5 : (State.get v5 OUT).length
        + (serF (encodeAllStepConstraints C)).length ≤ Ω := by
      rw [hv5OUT]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hΩidx5 : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.offset + C.width + C.init.length + C.steps
        + (State.get v5 CARDS).length ≤ Ω := by
      rw [h5CARDS]
      omega
    have hcAS := emitAllSteps_cost C v5 Ω h5STEPS h5OFF h5WID h5LREG h5LREG1
      h5CARDS h5ZERO hΩO5 h5WREG hΩidx5
    obtain ⟨h6OUT, h6ZERO, h6F⟩ := emitAllSteps_run C v5
      h5STEPS h5OFF h5WID h5LREG h5LREG1 h5CARDS h5ZERO
    set v6 := emitAllSteps.eval v5 with hv6
    have h6WREG : (State.get v6 WREG).length ≤ Ω := hcAS.2
    have h6OUTval : State.get v6 OUT
        = (([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1])
          ++ serF (encodeAllStepConstraints C) := by
      rw [h6OUT, hv5OUT]
    have h6STEPS := (h6F STEPS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5STEPS
    have h6OFF := (h6F OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5OFF
    have h6LREG := (h6F LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5LREG
    have h6LREG1 := (h6F LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5LREG1
    have h6FINAL := (h6F FINAL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5FINAL
    clear_value v6
    -- v7 : emitFinal (run + cost)
    have hΩO6 : (State.get v6 OUT).length
        + (serF (encodeFinalConstraint C)).length ≤ Ω := by
      rw [h6OUTval]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hΩidx6 : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.init.length + C.steps + (State.get v6 FINAL).length ≤ Ω := by
      rw [h6FINAL]
      omega
    have hcFin := emitFinal_cost C v6 Ω h6STEPS h6OFF h6LREG h6LREG1 h6FINAL h6ZERO
      hΩO6 h6WREG hΩidx6
    obtain ⟨h7OUT, h7ZERO, h7F⟩ := emitFinal_run C v6
      h6STEPS h6OFF h6LREG h6LREG1 h6FINAL h6ZERO
    set v7 := emitFinal.eval v6 with hv7
    have h7OUTval : State.get v7 OUT
        = ((([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1])
            ++ serF (encodeAllStepConstraints C))
          ++ serF (encodeFinalConstraint C) := by
      rw [h7OUT, h6OUTval]
    clear_value v7
    -- the branch's eval and cost
    have hbranchEval : (emitFandTag ;;
        Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
        emitBitsFromScan ZERO INIT ;;
        emitFandTag ;;
        emitAllSteps ;;
        emitFinal).eval u3 = v7 := by
      rw [Cmd.eval_seq, e_v1, Cmd.eval_seq, e_v2, Cmd.eval_seq, e_v3, Cmd.eval_seq,
        ← hv4, Cmd.eval_seq, e_v5, Cmd.eval_seq, ← hv6, ← hv7]
    have hvIfval : vIf = v7 := by
      rw [hvIf, Cmd.eval_ifBit_true _ _ _ _ hGeq, hbranchEval]
    have hbranchCost : (emitFandTag ;;
        Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
        emitBitsFromScan ZERO INIT ;;
        emitFandTag ;;
        emitAllSteps ;;
        emitFinal).cost u3
        = 1 + 3 + (1 + 1 + (1 + Op.cost (.copy SCAN INIT) v2
          + (1 + (emitBitsFromScan ZERO INIT).cost v3
          + (1 + 3 + (1 + emitAllSteps.cost v5 + emitFinal.cost v6))))) := by
      rw [Cmd.cost_seq, emitFandTag_cost, e_v1, Cmd.cost_seq, Cmd.cost_op, e_v2,
        Cmd.cost_seq, Cmd.cost_op, e_v3, Cmd.cost_seq, ← hv4, Cmd.cost_seq,
        emitFandTag_cost, e_v5, Cmd.cost_seq, ← hv6]
      simp only [Op.cost]
    have hcIf : (Cmd.ifBit GWF
        ( emitFandTag ;;
          Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
          emitBitsFromScan ZERO INIT ;;
          emitFandTag ;;
          emitAllSteps ;;
          emitFinal )
        emitFalse).cost u3
        = 1 + (1 + 3 + (1 + 1 + (1 + Op.cost (.copy SCAN INIT) v2
          + (1 + (emitBitsFromScan ZERO INIT).cost v3
          + (1 + 3 + (1 + emitAllSteps.cost v5 + emitFinal.cost v6)))))) := by
      rw [Cmd.cost_ifBit_true _ _ _ _ hGeq, hbranchCost]
    -- the final copy's length
    have hvIfOUT : (State.get vIf OUT).length = (serF (encodeTableau C)).length := by
      rw [hvIfval, h7OUTval, hserFlen]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hcIf, hc_v3, hvIfOUT]
    -- gather the bounds and close
    have hAS := hcAS.1
    have hFin := hcFin.1
    set Ks := Cmd.flatK (sentBitBody 0) with hKs
    clear_value Ks
    set Kb := Cmd.flatK (bsBody 0) with hKb
    clear_value Kb
    set Kr := Cmd.flatK readFinBody with hKr
    clear_value Kr
    set Ke := Cmd.flatK cardLenElemBody with hKe
    clear_value Ke
    set P2 := (Ω + 1) * (Ω + 1) with hP2
    set P3 := (Ω + 1) * P2 with hP3
    set P4 := (Ω + 1) * P3 with hP4
    set P5 := (Ω + 1) * P4 with hP5
    set cPre := precompLen.cost (encodeIn C) with hcPreDef
    clear_value cPre
    set cWF := computeWF.cost u1 with hcWFDef
    clear_value cWF
    set cScan := (emitBitsFromScan ZERO INIT).cost v3 with hcScanDef
    clear_value cScan
    set cAS := emitAllSteps.cost v5 with hcASDef
    clear_value cAS
    set cFin := emitFinal.cost v6 with hcFinDef
    clear_value cFin
    have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
    have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
    have hP34 : P3 ≤ P4 := by rw [hP4]; exact le_scale Ω P3
    have hP45 : P4 ≤ P5 := by rw [hP5]; exact le_scale Ω P4
    have h1P5 : 1 ≤ P5 := le_trans h1P2 (le_trans hP23 (le_trans hP34 hP45))
    have hΩP5 : Ω + 1 ≤ P5 := by
      calc Ω + 1 = (Ω + 1) * 1 := by ring
        _ ≤ (Ω + 1) * P4 := Nat.mul_le_mul_left _ (le_trans h1P2 (le_trans hP23 hP34))
        _ = P5 := by rw [hP5]
    have hPre5 : 8 * P2 ≤ 8 * P5 :=
      Nat.mul_le_mul_left _ (le_trans hP23 (le_trans hP34 hP45))
    have hWF5 : (2 * Ke + 160) * P3 ≤ (2 * Ke + 160) * P5 :=
      Nat.mul_le_mul_left _ (le_trans hP34 hP45)
    have hScan5 : (Kb + 6) * P2 ≤ (Kb + 6) * P5 :=
      Nat.mul_le_mul_left _ (le_trans hP23 (le_trans hP34 hP45))
    have hFin5 : (Kb + Kr + 140) * P4 ≤ (Kb + Kr + 140) * P5 :=
      Nat.mul_le_mul_left _ hP45
    have hLΩ : C.init.length ≤ Ω := by omega
    have hfin : (2 * Ks + 2 * Kb + Kr + 2 * Ke + 1000) * P5
        = (2 * Ks + 160) * P5 + (Kb + Kr + 140) * P5 + (2 * Ke + 160) * P5
          + (Kb + 6) * P5 + 8 * P5 + 526 * P5 := by ring
    have hgoal : buildFSATBound n
        = (2 * Ks + 2 * Kb + Kr + 2 * Ke + 1000) * P5 := by
      rw [buildFSATBound, buildFSATK, ← hKs, ← hKb, ← hKr, ← hKe, ← hΩdef,
        ← hP2, ← hP3, ← hP4, ← hP5]
    rw [hgoal]
    omega
  · -- not wellformed: the `emitFalse` branch
    have hGne : State.get u3 GWF ≠ [1] := by
      rw [h3GWF, if_neg hWf]; decide
    have hvIfval : vIf = emitFalse.eval u3 := by
      rw [hvIf, Cmd.eval_ifBit_false _ _ _ _ hGne]
    have hvIfOUT : (State.get vIf OUT).length = 5 := by
      rw [hvIfval, emitFalse_run, State.get_set_eq, h3OUT]
      rfl
    have hcIf : (Cmd.ifBit GWF
        ( emitFandTag ;;
          Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
          emitBitsFromScan ZERO INIT ;;
          emitFandTag ;;
          emitAllSteps ;;
          emitFinal )
        emitFalse).cost u3 = 1 + 9 := by
      rw [Cmd.cost_ifBit_false _ _ _ _ hGne, emitFalse_cost]
    rw [hcIf, hvIfOUT]
    set Ks := Cmd.flatK (sentBitBody 0) with hKs
    clear_value Ks
    set Kb := Cmd.flatK (bsBody 0) with hKb
    clear_value Kb
    set Kr := Cmd.flatK readFinBody with hKr
    clear_value Kr
    set Ke := Cmd.flatK cardLenElemBody with hKe
    clear_value Ke
    set P2 := (Ω + 1) * (Ω + 1) with hP2
    set P3 := (Ω + 1) * P2 with hP3
    set P4 := (Ω + 1) * P3 with hP4
    set P5 := (Ω + 1) * P4 with hP5
    set cPre := precompLen.cost (encodeIn C) with hcPreDef
    clear_value cPre
    set cWF := computeWF.cost u1 with hcWFDef
    clear_value cWF
    have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
    have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
    have hP34 : P3 ≤ P4 := by rw [hP4]; exact le_scale Ω P3
    have hP45 : P4 ≤ P5 := by rw [hP5]; exact le_scale Ω P4
    have h1P5 : 1 ≤ P5 := le_trans h1P2 (le_trans hP23 (le_trans hP34 hP45))
    have hPre5 : 8 * P2 ≤ 8 * P5 :=
      Nat.mul_le_mul_left _ (le_trans hP23 (le_trans hP34 hP45))
    have hWF5 : (2 * Ke + 160) * P3 ≤ (2 * Ke + 160) * P5 :=
      Nat.mul_le_mul_left _ (le_trans hP34 hP45)
    have hfin : (2 * Ks + 2 * Kb + Kr + 2 * Ke + 1000) * P5
        = (2 * Ke + 160) * P5 + (2 * Ks + 2 * Kb + Kr + 840) * P5 := by ring
    have hslack : 8 * P5 + 21 ≤ (2 * Ks + 2 * Kb + Kr + 840) * P5 := by
      have h1 : 840 * P5 ≤ (2 * Ks + 2 * Kb + Kr + 840) * P5 :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : 8 * P5 + 21 ≤ 840 * P5 := by omega
      omega
    have hgoal : buildFSATBound n
        = (2 * Ks + 2 * Kb + Kr + 2 * Ke + 1000) * P5 := by
      rw [buildFSATBound, buildFSATK, ← hKs, ← hKb, ← hKr, ← hKe, ← hΩdef,
        ← hP2, ← hP3, ← hP4, ← hP5]
    rw [hgoal]
    omega

end BinaryCCFSATFree
