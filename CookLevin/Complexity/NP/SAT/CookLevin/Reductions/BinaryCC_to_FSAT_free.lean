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

/-- `serF (encodeBitsAt start bits)` reading one `encSList` of bits off `SCAN`
(elements `1 1^b 0`, terminator bare `0`), leaving `SCAN` after the terminator.
`BASE = 1^start`; bit `i`'s index is `concat(BASE, 1^i)`. -/
def emitBitsFromSent (BASE : Nat) : Cmd :=
  Cmd.op (.clear DONE) ;;
  Cmd.forBnd KBIT SCAN
    ( Cmd.ifBit DONE
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
              Cmd.op (.clear DONE) ;; Cmd.op (.appendOne DONE) ) ) ) ;;
  emitFtrue

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
