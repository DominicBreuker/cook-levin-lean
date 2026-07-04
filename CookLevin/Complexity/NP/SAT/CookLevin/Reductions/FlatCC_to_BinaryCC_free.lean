import Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC
import Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC_free
import Complexity.Complexity.Deciders.CliqueRelTM

set_option autoImplicit false

/-! # `FlatCC_to_BinaryCC` as a free layer witness — the third live `⪯p'`
(S3 migration, top-down target #2, item 1)

This file re-proves the sound-tail reduction `FlatCC → BinaryCC` as a **free
`PolyTimeComputableLang` witness** (template:
`Reductions/FlatTCC_to_FlatCC_free.lean`), giving
`flatCC_reducesPolyMO' : FlatCCLang ⪯p' BinaryCCLang`.

**Design decision (risk-based, probe `probes/FlatCCBinProbe.lean`): the
`isValidFlattening` guard can NOT be dropped here** — unlike
`flatTCC_to_flatCC`, where the map preserves `Sigma` and symbol content so
invalidity transfers backward. The binary image ERASES the alphabet bound:
the invalid `C = ⟨Sigma:=1, offset:=1, width:=1, init:=[1], cards:=[],
final:=[[1]], steps:=0⟩` (symbol `1 ≥ Sigma`) maps under the unguarded
per-symbol block encoding to `init = [false,true]`, `final = [[false,true]]`
— a *wellformed* BinaryCC yes-instance (`init.length = 2 = 2·offset`,
`satFinal` at step `0`), while `FlatCCLang C` is false. No pure per-symbol
encoding can avoid this. The witness therefore computes the **guarded**
`FlatCC_to_BinaryCC_instance`, with the guard realized **on-machine**: every
unary symbol is checked `< Sigma` (truncated unary subtraction, the `ltBit`
design), the verdicts are ANDed into a flag, and a final branch writes the
all-empty no-instance when the check fails. The guard is a decidable property
of the *input* — legitimate for a many-one reduction (unlike S1's
if-on-the-answer).

**The layouts.** Input (`encodeIn`) = the `flatTCC_reductionLang` EXIT layout
(seam discipline — the first live `SeamData` in
`FlatTCC_to_BinaryCC_comp.lean` then only scrubs scratch): reg 1 `Sigma`
(unary), reg 2 `init` (bare blocks `1^v 0`), reg 4 `final` (sentinel lists),
reg 5 `steps` (unary), reg 6 `offset` (unary), reg 7 `width` (unary), reg 8
`cards` (per card two sentinel lists) — reg 3 empty. Output (`encKeyB`, the
natural BinaryCC layout `decodeOut` inverts): `offset`/`width` unary in regs
17/18, `init` as raw bits in reg 19, `cards` as per-card sentinel bit-lists
in reg 20, `final` as sentinel bit-lists in reg 21, `steps` **shared-layout**
in reg 5 (the map is the identity on it).

**⚠ Honesty discipline** (HANDOFF standing risk 1): `encodeIn` is the natural
layout of the *input* `FlatCC` (numbers unary, symbols as unary blocks),
`decodeOut = Function.invFun encKeyB` inverts the natural injective layout of
the *output* `BinaryCC`, and all expansion work (unary multiplication
`Sigma·offset`, per-symbol block expansion `v ↦ 0^v 1 0^(Sigma−v−1)`, the
validity check) happens in the `Cmd`. -/

namespace FlatCCBinFree

open Complexity.Lang
open FlatTCCFree (encNat encNats encSElem encSList encCardsOut encFinal
  encCardOut encNat_length encNat_append encSElem_length encSElem_append
  encNats_append encCardsOut_append encNats_length encSList_length
  encNats_bit encSList_bit encFinal_bit encCardsOut_injective
  encFinal_injective encFinal_length_le)

/-! ## Registers

Input layout pinned to `flatTCC_reductionLang`'s exit frame (regs 1–8, reg 3
empty); outputs at 17–21; scratch at 9–14, 23–25. `CliqueRelTM.readNum` pins
`HEAD = 15`, `INBLK = 16`, `SKIPR = 26` (`cSkip`). Reg 22 unused. -/

def SIGMA  : Var := 1
def INIT   : Var := 2
def FINAL  : Var := 4
def STEPS  : Var := 5
def OFFSET : Var := 6
def WIDTH  : Var := 7
def CARDS  : Var := 8
def SCAN   : Var := 9
def VALX   : Var := 10
def FLAG   : Var := 11
def IDXO   : Var := 12
def IDXR   : Var := 13
def REM    : Var := 14
def BOFF   : Var := 17
def BWID   : Var := 18
def BINIT  : Var := 19
def BCARDS : Var := 20
def BFINAL : Var := 21
def TFLG   : Var := 23
def IDX2   : Var := 24
def BOUT   : Var := 25

/-! ## The flat-level image of the map

The program computes these `Nat`-bit functions; the correspondence lemmas
below identify them with the real map's `Bool`-level encodings. -/

/-- Bit expansion of one flat symbol: `0^v 1 0^(k−v−1)` (`Nat` bits). Total —
for an invalid `v ≥ k` this is `0^v 1` (discarded by the guard). -/
def expandSym (k v : Nat) : List Nat :=
  List.replicate v 0 ++ 1 :: List.replicate (k - v - 1) 0

/-- Bit expansion of a flat string. -/
def expandStr (k : Nat) : List Nat → List Nat
  | [] => []
  | v :: xs => expandSym k v ++ expandStr k xs

/-- Bit expansion of a flat card. -/
def expandCard (k : Nat) (c : CCCard Nat) : CCCard Nat :=
  ⟨expandStr k c.prem, expandStr k c.conc⟩

/-- `Bool` bits as `Nat` bits (the register image of a `List Bool`). -/
def bitsNat (bs : List Bool) : List Nat := bs.map (fun b => cond b 1 0)

/-- A binary card as a `Nat`-bit card. -/
def cardNat (c : CCCard Bool) : CCCard Nat := ⟨bitsNat c.prem, bitsNat c.conc⟩

/-- Boolean validity of a flat string (`list_ofFlatType`, reflected). -/
def allLtB (k : Nat) (xs : List Nat) : Bool := xs.all (fun v => decide (v < k))

/-- Boolean validity of the three symbol streams (what the program's flag
computes). -/
def okB (k : Nat) (xs : List Nat) (cs : List (CCCard Nat))
    (fss : List (List Nat)) : Bool :=
  allLtB k xs
    && cs.all (fun c => allLtB k c.prem && allLtB k c.conc)
    && fss.all (allLtB k)

/-- Boolean validity of `isValidFlattening` (reflected). -/
def validB (C : FlatCC) : Bool := okB C.Sigma C.init C.cards C.final

/-! ## Encodings -/

/-- The natural FlatCC input layout, on the flatTCC witness's exit frame. -/
def encodeIn (C : FlatCC) : State :=
  [[], List.replicate C.Sigma 1, encNats C.init, [], encFinal C.final,
   List.replicate C.steps 1, List.replicate C.offset 1,
   List.replicate C.width 1, encCardsOut C.cards]

/-- The natural BinaryCC output layout, as the 6-register key `decodeOut`
inverts: `[offset, width, init, cards, final, steps]`. -/
def encKeyB (B : BinaryCC) : List (List Nat) :=
  [List.replicate B.offset 1, List.replicate B.width 1, bitsNat B.init,
   encCardsOut (B.cards.map cardNat), encFinal (B.final.map bitsNat),
   List.replicate B.steps 1]

/-- The output registers, in `encKeyB` order. -/
def extractKeyB (s : State) : List (List Nat) :=
  [State.get s BOFF, State.get s BWID, State.get s BINIT,
   State.get s BCARDS, State.get s BFINAL, State.get s STEPS]

/-! ## The program -/

/-- `FLAG := [0]` (validity reject; constant cost). -/
def setInvalid : Cmd := Cmd.op (.clear FLAG) ;; Cmd.op (.appendZero FLAG)

/-- Validity check + remainder: assumes `VALX = 1^v`, `SIGMA = 1^k`. Leaves
`REM = 1^(k−v−1)` (truncated) and ANDs `v < k` into `FLAG` (the
truncated-subtraction trick from `ltBit`'s design: `1^(k−v)` is non-empty iff
`v < k`). -/
def remCheck : Cmd :=
  Cmd.op (.copy REM SIGMA) ;;
  Cmd.forBnd IDX2 VALX (Cmd.op (.tail REM REM)) ;;
  Cmd.op (.nonEmpty TFLG REM) ;;
  Cmd.ifBit TFLG CliqueRelTM.cSkip setInvalid ;;
  Cmd.op (.tail REM REM)

/-- Append the bare-bit expansion `expandSym k v` of symbol `v` (`VALX = 1^v`)
to `BINIT`. -/
def expandBare : Cmd :=
  Cmd.forBnd IDX2 VALX (Cmd.op (.appendZero BINIT)) ;;
  Cmd.op (.appendOne BINIT) ;;
  remCheck ;;
  Cmd.forBnd IDX2 REM (Cmd.op (.appendZero BINIT))

/-- Append the sentinel-format expansion of symbol `v` to `BOUT`: the `k` bits
of the block, each as a sentinel element (`0 ↦ [1,0]`, `1 ↦ [1,1,0]`). -/
def expandSent : Cmd :=
  Cmd.forBnd IDX2 VALX (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT)) ;;
  Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendOne BOUT) ;;
  Cmd.op (.appendZero BOUT) ;;
  remCheck ;;
  Cmd.forBnd IDX2 REM (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT))

/-- Consume one bare block off `SCAN`, appending its bit expansion to `BINIT`;
idle when exhausted. -/
def initStep : Cmd :=
  Cmd.op (.nonEmpty TFLG SCAN) ;;
  Cmd.ifBit TFLG
    (CliqueRelTM.readNum VALX SCAN IDXR ;; expandBare)
    CliqueRelTM.cSkip

/-- Consume one sentinel-stream item off `SCAN` (element `1 1^v 0` or list
terminator `0`), appending its expansion to `BOUT`; idle when exhausted. -/
def sentStep : Cmd :=
  Cmd.op (.nonEmpty TFLG SCAN) ;;
  Cmd.ifBit TFLG
    (Cmd.op (.head TFLG SCAN) ;;
     Cmd.op (.tail SCAN SCAN) ;;
     Cmd.ifBit TFLG
       (CliqueRelTM.readNum VALX SCAN IDXR ;; expandSent)
       (Cmd.op (.appendZero BOUT)))
    CliqueRelTM.cSkip

/-- **The reduction program**: set the validity flag, build the two unary
products, expand the three symbol streams (validity-checking every symbol on
the way), and finally either keep the outputs or write the no-instance. The
sentinel-stream loops share the scratch output `BOUT` (copied out after each),
so one loop lemma covers both. Loop bounds are the streams' entry lengths
(≥ the item counts); surplus iterations idle. -/
def binConvert : Cmd :=
  Cmd.op (.clear FLAG) ;; Cmd.op (.appendOne FLAG) ;;
  Cmd.op (.clear BOFF) ;;
  Cmd.forBnd IDXO OFFSET (Cmd.op (.concat BOFF BOFF SIGMA)) ;;
  Cmd.op (.clear BWID) ;;
  Cmd.forBnd IDXO WIDTH (Cmd.op (.concat BWID BWID SIGMA)) ;;
  Cmd.op (.clear BINIT) ;;
  Cmd.op (.copy SCAN INIT) ;;
  Cmd.forBnd IDXO INIT initStep ;;
  Cmd.op (.clear BOUT) ;;
  Cmd.op (.copy SCAN CARDS) ;;
  Cmd.forBnd IDXO CARDS sentStep ;;
  Cmd.op (.copy BCARDS BOUT) ;;
  Cmd.op (.clear BOUT) ;;
  Cmd.op (.copy SCAN FINAL) ;;
  Cmd.forBnd IDXO FINAL sentStep ;;
  Cmd.op (.copy BFINAL BOUT) ;;
  Cmd.ifBit FLAG CliqueRelTM.cSkip
    (Cmd.op (.clear BOFF) ;; Cmd.op (.clear BWID) ;; Cmd.op (.clear BINIT) ;;
     Cmd.op (.clear BCARDS) ;; Cmd.op (.clear BFINAL) ;; Cmd.op (.clear STEPS))

/-! ## The item view of sentinel streams

Both `encCardsOut` and `encFinal` are concatenations of ITEMS — sentinel
elements `1 1^v 0` (`some v`) and list terminators `0` (`none`). The sentinel
loop consumes one item per iteration, so its invariant lives on the item
list; the lemmas here convert between the item view and the two card/final
encodings. -/

/-- One stream item: a sentinel element or a list terminator. -/
def encItem : Option Nat → List Nat
  | some v => 1 :: (List.replicate v 1 ++ [0])
  | none => [0]

def encItems : List (Option Nat) → List Nat
  | [] => []
  | it :: its => encItem it ++ encItems its

/-- The items of one sentinel list. -/
def sitemsOf (xs : List Nat) : List (Option Nat) := xs.map some ++ [none]

/-- The items of a card stream. -/
def citemsOf (cs : List (CCCard Nat)) : List (Option Nat) :=
  cs.flatMap (fun c => sitemsOf c.prem ++ sitemsOf c.conc)

/-- The items of a final stream. -/
def fitemsOf (fss : List (List Nat)) : List (Option Nat) :=
  fss.flatMap sitemsOf

/-- Sentinel elements of a list, without the terminator. -/
def encSElems : List Nat → List Nat
  | [] => []
  | v :: xs => encSElem v ++ encSElems xs

/-- What the sentinel loop appends per item. -/
def expandItem (k : Nat) : Option Nat → List Nat
  | some v => encSElems (expandSym k v)
  | none => [0]

def expandItems (k : Nat) : List (Option Nat) → List Nat
  | [] => []
  | it :: its => expandItem k it ++ expandItems k its

/-- Boolean validity of one item. -/
def itemOkB (k : Nat) : Option Nat → Bool
  | some v => decide (v < k)
  | none => true

def itemsOkB (k : Nat) (its : List (Option Nat)) : Bool := its.all (itemOkB k)

theorem encItems_append (a b : List (Option Nat)) :
    encItems (a ++ b) = encItems a ++ encItems b := by
  induction a with
  | nil => rfl
  | cons it a ih => rw [List.cons_append, encItems, encItems, ih,
      List.append_assoc]

theorem encSElems_append (a b : List Nat) :
    encSElems (a ++ b) = encSElems a ++ encSElems b := by
  induction a with
  | nil => rfl
  | cons v a ih => rw [List.cons_append, encSElems, encSElems, ih,
      List.append_assoc]

theorem expandItems_append (k : Nat) (a b : List (Option Nat)) :
    expandItems k (a ++ b) = expandItems k a ++ expandItems k b := by
  induction a with
  | nil => rfl
  | cons it a ih => rw [List.cons_append, expandItems, expandItems, ih,
      List.append_assoc]

/-- `encSList` = elements + terminator. -/
theorem encSList_eq_elems (xs : List Nat) :
    encSList xs = encSElems xs ++ [0] := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
      show encSElem v ++ encSList xs = (encSElem v ++ encSElems xs) ++ [0]
      rw [ih, List.append_assoc]

theorem encItems_sitemsOf (xs : List Nat) :
    encItems (sitemsOf xs) = encSList xs := by
  show encItems (xs.map some ++ [none]) = encSList xs
  induction xs with
  | nil => rfl
  | cons v xs ih =>
      rw [List.map_cons, List.cons_append, encItems, ih]
      rfl

theorem encItems_citemsOf (cs : List (CCCard Nat)) :
    encItems (citemsOf cs) = encCardsOut cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show encItems ((sitemsOf c.prem ++ sitemsOf c.conc) ++ citemsOf cs) = _
      rw [encItems_append, encItems_append, encItems_sitemsOf,
        encItems_sitemsOf, ih]
      show _ = (encSList c.prem ++ encSList c.conc) ++ encCardsOut cs
      rw [List.append_assoc]

theorem encItems_fitemsOf (fss : List (List Nat)) :
    encItems (fitemsOf fss) = encFinal fss := by
  induction fss with
  | nil => rfl
  | cons s fss ih =>
      show encItems (sitemsOf s ++ fitemsOf fss) = _
      rw [encItems_append, encItems_sitemsOf, ih]
      rfl

/-- Item-wise expansion of one sentinel list is the sentinel list of the
expanded string. -/
theorem expandItems_sitemsOf (k : Nat) (xs : List Nat) :
    expandItems k (sitemsOf xs) = encSList (expandStr k xs) := by
  show expandItems k (xs.map some ++ [none]) = _
  induction xs with
  | nil => rfl
  | cons v xs ih =>
      rw [List.map_cons, List.cons_append, expandItems, ih]
      show encSElems (expandSym k v) ++ encSList (expandStr k xs)
          = encSList (expandSym k v ++ expandStr k xs)
      rw [encSList_eq_elems, encSList_eq_elems, encSElems_append,
        List.append_assoc]

theorem expandItems_citemsOf (k : Nat) (cs : List (CCCard Nat)) :
    expandItems k (citemsOf cs) = encCardsOut (cs.map (expandCard k)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show expandItems k ((sitemsOf c.prem ++ sitemsOf c.conc) ++ citemsOf cs) = _
      rw [expandItems_append, expandItems_append, expandItems_sitemsOf,
        expandItems_sitemsOf, ih]
      rfl

theorem expandItems_fitemsOf (k : Nat) (fss : List (List Nat)) :
    expandItems k (fitemsOf fss) = encFinal (fss.map (expandStr k)) := by
  induction fss with
  | nil => rfl
  | cons s fss ih =>
      show expandItems k (sitemsOf s ++ fitemsOf fss) = _
      rw [expandItems_append, expandItems_sitemsOf, ih]
      rfl

theorem itemsOkB_append (k : Nat) (a b : List (Option Nat)) :
    itemsOkB k (a ++ b) = (itemsOkB k a && itemsOkB k b) := by
  simp [itemsOkB, List.all_append]

theorem itemsOkB_sitemsOf (k : Nat) (xs : List Nat) :
    itemsOkB k (sitemsOf xs) = allLtB k xs := by
  show itemsOkB k (xs.map some ++ [none]) = _
  rw [itemsOkB_append]
  have h1 : itemsOkB k (xs.map some) = allLtB k xs := by
    simp [itemsOkB, allLtB, List.all_map, Function.comp_def, itemOkB]
  have h2 : itemsOkB k [none] = true := rfl
  rw [h1, h2, Bool.and_true]

theorem itemsOkB_citemsOf (k : Nat) (cs : List (CCCard Nat)) :
    itemsOkB k (citemsOf cs)
      = cs.all (fun c => allLtB k c.prem && allLtB k c.conc) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show itemsOkB k ((sitemsOf c.prem ++ sitemsOf c.conc) ++ citemsOf cs) = _
      rw [itemsOkB_append, itemsOkB_append, itemsOkB_sitemsOf,
        itemsOkB_sitemsOf, ih, List.all_cons]

theorem itemsOkB_fitemsOf (k : Nat) (fss : List (List Nat)) :
    itemsOkB k (fitemsOf fss) = fss.all (allLtB k) := by
  induction fss with
  | nil => rfl
  | cons s fss ih =>
      show itemsOkB k (sitemsOf s ++ fitemsOf fss) = _
      rw [itemsOkB_append, itemsOkB_sitemsOf, ih, List.all_cons]

/-! ## Length accounting -/

theorem encItem_length_pos (it : Option Nat) : 1 ≤ (encItem it).length := by
  cases it <;> simp [encItem]

theorem encItems_length (its : List (Option Nat)) :
    its.length ≤ (encItems its).length := by
  induction its with
  | nil => simp
  | cons it its ih =>
      rw [encItems, List.length_append, List.length_cons]
      have := encItem_length_pos it
      omega

theorem expandSym_length (k v : Nat) :
    (expandSym k v).length = v + 1 + (k - v - 1) := by
  simp [expandSym]
  omega

/-- Per item the sentinel expansion is at most `3·(k + |encItem it|)` cells
(each expanded bit is a 2- or 3-cell sentinel element; there are at most
`v + k + 1 ≤ |encItem it| + k` of them). -/
theorem expandItem_length_le (k : Nat) (it : Option Nat) :
    (expandItem k it).length ≤ 3 * (k + (encItem it).length) := by
  cases it with
  | none =>
      simp [expandItem, encItem]
      omega
  | some v =>
      show (encSElems (expandSym k v)).length ≤ _
      have hgen : ∀ bs : List Nat, (∀ x ∈ bs, x ≤ 1) →
          (encSElems bs).length ≤ 3 * bs.length := by
        intro bs
        induction bs with
        | nil => intro _; simp [encSElems]
        | cons b bs ih =>
            intro hb
            rw [encSElems, List.length_append, encSElem_length,
              List.length_cons]
            have hble : b ≤ 1 := hb b (by simp)
            have := ih (fun x hx => hb x (by simp [hx]))
            omega
      have hbits : ∀ x ∈ expandSym k v, x ≤ 1 := by
        intro x hx
        simp only [expandSym, List.mem_append, List.mem_cons,
          List.mem_replicate] at hx
        rcases hx with ⟨-, rfl⟩ | rfl | ⟨-, rfl⟩ <;> omega
      have h1 := hgen (expandSym k v) hbits
      rw [expandSym_length] at h1
      simp only [encItem, List.length_cons, List.length_append,
        List.length_replicate]
      omega

/-! ## Bit-level cells (`enc_bit` for the input layout) -/

theorem encCardsOut_bit (cs : List (CCCard Nat)) :
    ∀ x ∈ encCardsOut cs, x ≤ 1 := by
  induction cs with
  | nil => intro x h; cases h
  | cons c cs ih =>
      intro x h
      rw [encCardsOut] at h
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact encSList_bit _ x h
        · exact encSList_bit _ x h
      · exact ih x h

/-! ## Injectivity of the output key -/

theorem bitsNat_injective : Function.Injective bitsNat := by
  intro a b hab
  have : Function.Injective (fun b : Bool => cond b 1 0) := by
    intro x y hxy
    cases x <;> cases y <;> simp_all
  exact List.map_injective_iff.mpr this hab

theorem cardNat_injective : Function.Injective cardNat := by
  intro a b hab
  cases a; cases b
  simp only [cardNat, CCCard.mk.injEq] at hab ⊢
  exact ⟨bitsNat_injective hab.1, bitsNat_injective hab.2⟩

theorem replicate_one_inj {a b : Nat}
    (h : List.replicate a 1 = List.replicate b (1 : Nat)) : a = b := by
  have := congrArg List.length h
  simpa using this

theorem encKeyB_injective : Function.Injective encKeyB := by
  intro A B hAB
  cases A; cases B
  simp only [encKeyB, List.cons.injEq, and_true] at hAB
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hAB
  simp only [BinaryCC.mk.injEq]
  refine ⟨replicate_one_inj h1, replicate_one_inj h2, bitsNat_injective h3,
    ?_, ?_, replicate_one_inj h6⟩
  · exact List.map_injective_iff.mpr cardNat_injective
      (encCardsOut_injective h4)
  · exact List.map_injective_iff.mpr bitsNat_injective
      (encFinal_injective h5)

/-! ## Correspondence with the real map

The program computes the flat-level `expand*` functions; on VALID inputs these
are exactly the `Nat`-bit images of `CC_to_BinaryCC ∘ unflattenCC`. -/

theorem bitsNat_encodeSymbol {k : Nat} (x : Fin k) :
    bitsNat (encodeSymbol x) = expandSym k x.1 := by
  simp [bitsNat, encodeSymbol, expandSym, List.append_assoc]

theorem bitsNat_append (a b : List Bool) :
    bitsNat (a ++ b) = bitsNat a ++ bitsNat b := List.map_append ..

theorem bitsNat_encodeString {k : Nat} :
    ∀ (xs : List Nat) (h : list_ofFlatType k xs),
      bitsNat (encodeString (unflattenList k xs h)) = expandStr k xs
  | [], _ => rfl
  | x :: xs, h => by
      have hxs : list_ofFlatType k xs := fun y hy => h y (by simp [hy])
      show bitsNat (encodeString
          ((⟨x, h x (by simp)⟩ : Fin k) :: unflattenList k xs hxs)) = _
      rw [encodeString, bitsNat_append, bitsNat_encodeSymbol,
        bitsNat_encodeString xs hxs]
      rfl

theorem cardNat_encodeCard {k : Nat} (c : CCCard Nat)
    (h : CCCard_ofFlatType c k) :
    cardNat (encodeCard (unflattenCard k c h)) = expandCard k c := by
  cases c with
  | mk prem conc =>
      show CCCard.mk (bitsNat (encodeString (unflattenList k prem h.1)))
          (bitsNat (encodeString (unflattenList k conc h.2))) = _
      rw [bitsNat_encodeString prem h.1, bitsNat_encodeString conc h.2]
      rfl

theorem cardsNat_encodeCards {k : Nat} :
    ∀ (cs : List (CCCard Nat)) (h : isValidFlatCards cs k),
      ((unflattenCards k cs h).map encodeCard).map cardNat
        = cs.map (expandCard k)
  | [], _ => rfl
  | c :: cs, h => by
      have hc : CCCard_ofFlatType c k := h c (by simp)
      have hcs : isValidFlatCards cs k := fun c' hc' => h c' (by simp [hc'])
      show cardNat (encodeCard (unflattenCard k c hc))
          :: ((unflattenCards k cs hcs).map encodeCard).map cardNat = _
      rw [cardNat_encodeCard c hc, cardsNat_encodeCards cs hcs]
      rfl

theorem finalNat_encodeFinal {k : Nat} :
    ∀ (fss : List (List Nat)) (h : isValidFlatFinal fss k),
      (encodeFinal (unflattenFinal k fss h)).map bitsNat
        = fss.map (expandStr k)
  | [], _ => rfl
  | s :: fss, h => by
      have hs : list_ofFlatType k s := h s (by simp)
      have hfss : isValidFlatFinal fss k := fun s' hs' => h s' (by simp [hs'])
      show bitsNat (encodeString (unflattenList k s hs))
          :: (encodeFinal (unflattenFinal k fss hfss)).map bitsNat = _
      rw [bitsNat_encodeString s hs, finalNat_encodeFinal fss hfss]
      rfl

/-- The Boolean validity check reflects `isValidFlattening`. -/
theorem validB_iff (C : FlatCC) : validB C = true ↔ isValidFlattening C := by
  constructor
  · intro h
    simp only [validB, okB, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨⟨hinit, hcards⟩, hfinal⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have := hinit
      simp only [allLtB, List.all_eq_true, decide_eq_true_eq] at this
      exact this x hx
    · intro s hs x hx
      have := hfinal s hs
      simp only [allLtB, List.all_eq_true, decide_eq_true_eq] at this
      exact this x hx
    · intro c hc
      have := hcards c hc
      simp only [allLtB, List.all_eq_true, decide_eq_true_eq] at this
      exact ⟨fun x hx => this.1 x hx, fun x hx => this.2 x hx⟩
  · rintro ⟨hinit, hfinal, hcards⟩
    simp only [validB, okB, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [allLtB, List.all_eq_true, decide_eq_true_eq]
      exact fun x hx => hinit x hx
    · intro c hc
      obtain ⟨hp, hcn⟩ := hcards c hc
      simp only [allLtB, List.all_eq_true, decide_eq_true_eq]
      exact ⟨fun x hx => hp x hx, fun x hx => hcn x hx⟩
    · intro s hs
      simp only [allLtB, List.all_eq_true, decide_eq_true_eq]
      exact fun x hx => hfinal s hs x hx

/-! ## The inner gadgets: run + cost

Each gadget lemma follows the template pattern: exact output register
contents, a frame over the untouched registers, and a per-run cost bound. -/

/-- Zero-pad loop: `forBnd IDX2 bnd (appendZero BINIT)` appends `0^m` to
`BINIT`, where `m` is the unary value of the bound register. -/
theorem zeroPad_run (bnd : Var) (s : State) (m : Nat)
    (hbnd : State.get s bnd = List.replicate m 1) :
    State.get ((Cmd.forBnd IDX2 bnd (Cmd.op (.appendZero BINIT))).eval s) BINIT
      = State.get s BINIT ++ List.replicate m 0
    ∧ (∀ r : Var, r ≠ BINIT → r ≠ IDX2 →
        State.get ((Cmd.forBnd IDX2 bnd (Cmd.op (.appendZero BINIT))).eval s) r
          = State.get s r)
    ∧ (Cmd.forBnd IDX2 bnd (Cmd.op (.appendZero BINIT))).cost s
        ≤ 1 + m + m * m := by
  have hlen : (State.get s bnd).length = m := by
    rw [hbnd, List.length_replicate]
  have hstep : ∀ i st, i < m →
      (State.get st BINIT = State.get s BINIT ++ List.replicate i 0
        ∧ ∀ r : Var, r ≠ BINIT → r ≠ IDX2 → State.get st r = State.get s r) →
      (State.get ((Cmd.op (.appendZero BINIT)).eval
            (st.set IDX2 (List.replicate i 1))) BINIT
          = State.get s BINIT ++ List.replicate (i + 1) 0
        ∧ ∀ r : Var, r ≠ BINIT → r ≠ IDX2 →
            State.get ((Cmd.op (.appendZero BINIT)).eval
              (st.set IDX2 (List.replicate i 1))) r = State.get s r) := by
    intro i st _ ⟨hB, hF⟩
    have he : (Cmd.op (.appendZero BINIT)).eval (st.set IDX2 (List.replicate i 1))
        = (st.set IDX2 (List.replicate i 1)).set BINIT
            (State.get (st.set IDX2 (List.replicate i 1)) BINIT ++ [0]) := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    have hwB : State.get (st.set IDX2 (List.replicate i 1)) BINIT
        = State.get s BINIT ++ List.replicate i 0 := by
      rw [State.get_set_ne _ _ _ _ (by decide), hB]
    constructor
    · rw [he, State.get_set_eq, hwB, List.append_assoc,
        ← List.replicate_succ']
    · intro r h1 h2
      rw [he, State.get_set_ne _ _ _ _ h1, State.get_set_ne _ _ _ _ h2]
      exact hF r h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [Cmd.eval_forBnd, hlen]
    exact (Cmd.foldlState_range_induct _ IDX2 m s
      (fun i st => State.get st BINIT = State.get s BINIT ++ List.replicate i 0
        ∧ ∀ r : Var, r ≠ BINIT → r ≠ IDX2 → State.get st r = State.get s r)
      ⟨by simp, fun r _ _ => rfl⟩ hstep).1
  · intro r h1 h2
    rw [Cmd.eval_forBnd, hlen]
    exact (Cmd.foldlState_range_induct _ IDX2 m s
      (fun i st => State.get st BINIT = State.get s BINIT ++ List.replicate i 0
        ∧ ∀ r : Var, r ≠ BINIT → r ≠ IDX2 → State.get st r = State.get s r)
      ⟨by simp, fun r _ _ => rfl⟩ hstep).2 r h1 h2
  · have h := Cmd.cost_forBnd_le IDX2 bnd (Cmd.op (.appendZero BINIT)) s 1
      (fun i st => State.get st BINIT = State.get s BINIT ++ List.replicate i 0
        ∧ ∀ r : Var, r ≠ BINIT → r ≠ IDX2 → State.get st r = State.get s r)
      ⟨by simp, fun r _ _ => rfl⟩
      (fun i st hi hM => hstep i st (by omega) hM)
      (fun i st _ _ => by rw [Cmd.cost_op]; exact le_refl 1)
    rw [hlen] at h
    omega

/-- Element-pad loop: `forBnd IDX2 bnd (appendOne BOUT ;; appendZero BOUT)`
appends `m` zero-bit sentinel elements (`encSElems 0^m`) to `BOUT`. -/
theorem elemPad_run (bnd : Var) (s : State) (m : Nat)
    (hbnd : State.get s bnd = List.replicate m 1) :
    State.get ((Cmd.forBnd IDX2 bnd
        (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT))).eval s) BOUT
      = State.get s BOUT ++ encSElems (List.replicate m 0)
    ∧ (∀ r : Var, r ≠ BOUT → r ≠ IDX2 →
        State.get ((Cmd.forBnd IDX2 bnd
          (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT))).eval s) r
          = State.get s r)
    ∧ (Cmd.forBnd IDX2 bnd
        (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT))).cost s
        ≤ 1 + 3 * m + m * m := by
  have hlen : (State.get s bnd).length = m := by
    rw [hbnd, List.length_replicate]
  have hsucc : ∀ i : Nat, encSElems (List.replicate (i + 1) 0)
      = encSElems (List.replicate i 0) ++ [1, 0] := by
    intro i
    rw [List.replicate_succ', encSElems_append]
    rfl
  have hstep : ∀ i st, i < m →
      (State.get st BOUT = State.get s BOUT ++ encSElems (List.replicate i 0)
        ∧ ∀ r : Var, r ≠ BOUT → r ≠ IDX2 → State.get st r = State.get s r) →
      (State.get ((Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT)).eval
            (st.set IDX2 (List.replicate i 1))) BOUT
          = State.get s BOUT ++ encSElems (List.replicate (i + 1) 0)
        ∧ ∀ r : Var, r ≠ BOUT → r ≠ IDX2 →
            State.get ((Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT)).eval
              (st.set IDX2 (List.replicate i 1))) r = State.get s r) := by
    intro i st _ ⟨hB, hF⟩
    set w := st.set IDX2 (List.replicate i 1) with hw
    have hwB : State.get w BOUT = State.get s BOUT ++ encSElems (List.replicate i 0) := by
      rw [hw, State.get_set_ne _ _ _ _ (by decide), hB]
    have he : (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT)).eval w
        = (w.set BOUT (State.get w BOUT ++ [1])).set BOUT
            ((State.get w BOUT ++ [1]) ++ [0]) := by
      rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq]
    constructor
    · rw [he, State.get_set_eq, hwB, hsucc i, List.append_assoc,
        List.append_assoc]
      rfl
    · intro r h1 h2
      rw [he, State.get_set_ne _ _ _ _ h1, State.get_set_ne _ _ _ _ h1,
        hw, State.get_set_ne _ _ _ _ h2]
      exact hF r h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [Cmd.eval_forBnd, hlen]
    exact (Cmd.foldlState_range_induct _ IDX2 m s
      (fun i st => State.get st BOUT = State.get s BOUT ++ encSElems (List.replicate i 0)
        ∧ ∀ r : Var, r ≠ BOUT → r ≠ IDX2 → State.get st r = State.get s r)
      ⟨by simp [encSElems], fun r _ _ => rfl⟩ hstep).1
  · intro r h1 h2
    rw [Cmd.eval_forBnd, hlen]
    exact (Cmd.foldlState_range_induct _ IDX2 m s
      (fun i st => State.get st BOUT = State.get s BOUT ++ encSElems (List.replicate i 0)
        ∧ ∀ r : Var, r ≠ BOUT → r ≠ IDX2 → State.get st r = State.get s r)
      ⟨by simp [encSElems], fun r _ _ => rfl⟩ hstep).2 r h1 h2
  · have h := Cmd.cost_forBnd_le IDX2 bnd
      (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT)) s 3
      (fun i st => State.get st BOUT = State.get s BOUT ++ encSElems (List.replicate i 0)
        ∧ ∀ r : Var, r ≠ BOUT → r ≠ IDX2 → State.get st r = State.get s r)
      ⟨by simp [encSElems], fun r _ _ => rfl⟩
      (fun i st hi hM => hstep i st (by omega) hM)
      (fun i st _ _ => by
        rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
        exact le_refl 3)
    rw [hlen] at h
    omega

/-- Drain loop: `forBnd IDX2 VALX (tail REM REM)` on `VALX = 1^v`,
`REM = 1^K` leaves `REM = 1^(K−v)` (truncated subtraction). -/
theorem remDrain_run (s : State) (v K : Nat)
    (hVAL : State.get s VALX = List.replicate v 1)
    (hREM : State.get s REM = List.replicate K 1) :
    State.get ((Cmd.forBnd IDX2 VALX (Cmd.op (.tail REM REM))).eval s) REM
      = List.replicate (K - v) 1
    ∧ (∀ r : Var, r ≠ REM → r ≠ IDX2 →
        State.get ((Cmd.forBnd IDX2 VALX (Cmd.op (.tail REM REM))).eval s) r
          = State.get s r)
    ∧ (Cmd.forBnd IDX2 VALX (Cmd.op (.tail REM REM))).cost s
        ≤ 1 + v * (K + 1) + v * v := by
  have hlen : (State.get s VALX).length = v := by
    rw [hVAL, List.length_replicate]
  have hstep : ∀ i st, i < v →
      (State.get st REM = List.replicate (K - i) 1
        ∧ ∀ r : Var, r ≠ REM → r ≠ IDX2 → State.get st r = State.get s r) →
      (State.get ((Cmd.op (.tail REM REM)).eval
            (st.set IDX2 (List.replicate i 1))) REM
          = List.replicate (K - (i + 1)) 1
        ∧ ∀ r : Var, r ≠ REM → r ≠ IDX2 →
            State.get ((Cmd.op (.tail REM REM)).eval
              (st.set IDX2 (List.replicate i 1))) r = State.get s r) := by
    intro i st _ ⟨hR, hF⟩
    have hwR : State.get (st.set IDX2 (List.replicate i 1)) REM
        = List.replicate (K - i) 1 := by
      rw [State.get_set_ne _ _ _ _ (by decide), hR]
    have he : (Cmd.op (.tail REM REM)).eval (st.set IDX2 (List.replicate i 1))
        = (st.set IDX2 (List.replicate i 1)).set REM
            (List.replicate (K - i) 1).tail := by
      rw [Cmd.eval_op]; simp only [Op.eval, hwR]
    constructor
    · rw [he, State.get_set_eq, List.tail_replicate]
      congr 1
    · intro r h1 h2
      rw [he, State.get_set_ne _ _ _ _ h1, State.get_set_ne _ _ _ _ h2]
      exact hF r h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [Cmd.eval_forBnd, hlen]
    have := (Cmd.foldlState_range_induct _ IDX2 v s
      (fun i st => State.get st REM = List.replicate (K - i) 1
        ∧ ∀ r : Var, r ≠ REM → r ≠ IDX2 → State.get st r = State.get s r)
      ⟨by simp [hREM], fun r _ _ => rfl⟩ hstep).1
    exact this
  · intro r h1 h2
    rw [Cmd.eval_forBnd, hlen]
    exact (Cmd.foldlState_range_induct _ IDX2 v s
      (fun i st => State.get st REM = List.replicate (K - i) 1
        ∧ ∀ r : Var, r ≠ REM → r ≠ IDX2 → State.get st r = State.get s r)
      ⟨by simp [hREM], fun r _ _ => rfl⟩ hstep).2 r h1 h2
  · have h := Cmd.cost_forBnd_le IDX2 VALX (Cmd.op (.tail REM REM)) s (K + 1)
      (fun i st => State.get st REM = List.replicate (K - i) 1
        ∧ ∀ r : Var, r ≠ REM → r ≠ IDX2 → State.get st r = State.get s r)
      ⟨by simp [hREM], fun r _ _ => rfl⟩
      (fun i st hi hM => hstep i st (by omega) hM)
      (fun i st _ hM => by
        rw [Cmd.cost_op]
        show (State.get (st.set IDX2 (List.replicate i 1)) REM).length + 1 ≤ K + 1
        rw [State.get_set_ne _ _ _ _ (by decide), hM.1, List.length_replicate]
        omega)
    rw [hlen] at h
    omega

/-- **`remCheck` is correct**: on `VALX = 1^v`, `SIGMA = 1^k` it leaves
`REM = 1^(k−v−1)` and ANDs the verdict `v < k` into `FLAG`. -/
theorem remCheck_run (s : State) (v k : Nat) (b : Bool)
    (hVAL : State.get s VALX = List.replicate v 1)
    (hSIG : State.get s SIGMA = List.replicate k 1)
    (hFLAG : State.get s FLAG = cond b [1] [0]) :
    State.get (remCheck.eval s) REM = List.replicate (k - v - 1) 1
    ∧ State.get (remCheck.eval s) FLAG = cond (b && decide (v < k)) [1] [0]
    ∧ (∀ r : Var, r ≠ REM → r ≠ TFLG → r ≠ FLAG → r ≠ IDX2 →
        r ≠ CliqueRelTM.SKIPR → State.get (remCheck.eval s) r = State.get s r)
    ∧ remCheck.cost s ≤ v * k + v * v + v + 2 * k + 12 := by
  -- stage 1: copy SIGMA into REM
  have e1 : (Cmd.op (.copy REM SIGMA)).eval s
      = s.set REM (List.replicate k 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hSIG]
  set s1 := s.set REM (List.replicate k 1) with hs1
  have hs1VAL : State.get s1 VALX = List.replicate v 1 := by
    rw [hs1, State.get_set_ne _ _ _ _ (by decide), hVAL]
  have hs1REM : State.get s1 REM = List.replicate k 1 := State.get_set_eq _ _ _
  -- stage 2: drain v cells
  obtain ⟨hR2, hF2, hC2⟩ := remDrain_run s1 v k hs1VAL hs1REM
  set s2 := (Cmd.forBnd IDX2 VALX (Cmd.op (.tail REM REM))).eval s1 with hs2
  have hs2FLAG : State.get s2 FLAG = cond b [1] [0] := by
    rw [hF2 FLAG (by decide) (by decide), hs1,
      State.get_set_ne _ _ _ _ (by decide), hFLAG]
  -- stage 3: the verdict
  have e3 : (Cmd.op (.nonEmpty TFLG REM)).eval s2
      = s2.set TFLG (if (List.replicate (k - v) 1).isEmpty then [0] else [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hR2]
  rcases Nat.lt_or_ge v k with hvk | hvk
  · -- v < k : the check passes; the branch is `cSkip`
    have hne : (List.replicate (k - v) 1).isEmpty = false := by
      have : k - v ≠ 0 := by omega
      simp [this]
    set s3 := s2.set TFLG [1] with hs3
    have e3' : (Cmd.op (.nonEmpty TFLG REM)).eval s2 = s3 := by
      rw [e3, hne]
      simp only [Bool.false_eq_true, if_false]
      exact hs3.symm
    have hs3TFLG : State.get s3 TFLG = [1] := State.get_set_eq _ _ _
    have e4 : (Cmd.ifBit TFLG CliqueRelTM.cSkip setInvalid).eval s3
        = s3.set CliqueRelTM.SKIPR [1] := by
      rw [Cmd.eval_ifBit_true _ _ _ _ hs3TFLG, CliqueRelTM.cSkip_eval]
    set s4 := s3.set CliqueRelTM.SKIPR [1] with hs4
    have hs4REM : State.get s4 REM = List.replicate (k - v) 1 := by
      rw [hs4, State.get_set_ne _ _ _ _ (by decide), hs3,
        State.get_set_ne _ _ _ _ (by decide), hR2]
    have e5 : (Cmd.op (.tail REM REM)).eval s4
        = s4.set REM (List.replicate (k - v - 1) 1) := by
      rw [Cmd.eval_op]
      simp only [Op.eval, hs4REM, List.tail_replicate]
    have heval : remCheck.eval s = s4.set REM (List.replicate (k - v - 1) 1) := by
      show ((Cmd.op (.copy REM SIGMA)) ;; _).eval s = _
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hs2, Cmd.eval_seq, e3',
        Cmd.eval_seq, e4, e5]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [heval, State.get_set_eq]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide), hs4,
        State.get_set_ne _ _ _ _ (by decide), hs3,
        State.get_set_ne _ _ _ _ (by decide), hs2FLAG]
      have : decide (v < k) = true := decide_eq_true hvk
      rw [this, Bool.and_true]
    · intro r h1 h2 h3 h4 h5
      rw [heval, State.get_set_ne _ _ _ _ h1, hs4,
        State.get_set_ne _ _ _ _ h5, hs3, State.get_set_ne _ _ _ _ h2,
        hF2 r h1 h4, hs1, State.get_set_ne _ _ _ _ h1]
    · show ((Cmd.op (.copy REM SIGMA)) ;; _).cost s ≤ _
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hs2, Cmd.cost_seq,
        Cmd.cost_op, e3', Cmd.cost_seq, Cmd.cost_ifBit_true _ _ _ _ hs3TFLG,
        e4, Cmd.cost_op]
      simp only [Op.cost, hSIG, List.length_replicate,
        CliqueRelTM.cSkip_cost, hs4REM]
      have hd : k - v ≤ k := Nat.sub_le _ _
      have hvk1 : v * (k + 1) = v * k + v := by ring
      omega
  · -- v ≥ k : the check fails; the branch is `setInvalid`
    have hne : (List.replicate (k - v) 1).isEmpty = true := by
      have : k - v = 0 := by omega
      simp [this]
    set s3 := s2.set TFLG [0] with hs3
    have e3' : (Cmd.op (.nonEmpty TFLG REM)).eval s2 = s3 := by
      rw [e3, hne]
      simp only [if_true]
      exact hs3.symm
    have hs3TFLG : State.get s3 TFLG ≠ [1] := by
      rw [State.get_set_eq]; decide
    have e4 : (Cmd.ifBit TFLG CliqueRelTM.cSkip setInvalid).eval s3
        = (s3.set FLAG []).set FLAG [0] := by
      rw [Cmd.eval_ifBit_false _ _ _ _ hs3TFLG]
      show (Cmd.op (.clear FLAG) ;; Cmd.op (.appendZero FLAG)).eval s3 = _
      rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, List.nil_append]
    set s4 := (s3.set FLAG []).set FLAG [0] with hs4
    have hs4REM : State.get s4 REM = List.replicate (k - v) 1 := by
      rw [hs4, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hs3,
        State.get_set_ne _ _ _ _ (by decide), hR2]
    have e5 : (Cmd.op (.tail REM REM)).eval s4
        = s4.set REM (List.replicate (k - v - 1) 1) := by
      rw [Cmd.eval_op]
      simp only [Op.eval, hs4REM, List.tail_replicate]
    have heval : remCheck.eval s = s4.set REM (List.replicate (k - v - 1) 1) := by
      show ((Cmd.op (.copy REM SIGMA)) ;; _).eval s = _
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hs2, Cmd.eval_seq, e3',
        Cmd.eval_seq, e4, e5]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [heval, State.get_set_eq]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide), hs4, State.get_set_eq]
      have : decide (v < k) = false := decide_eq_false (by omega)
      rw [this, Bool.and_false]
      rfl
    · intro r h1 h2 h3 h4 h5
      rw [heval, State.get_set_ne _ _ _ _ h1, hs4,
        State.get_set_ne _ _ _ _ h3, State.get_set_ne _ _ _ _ h3, hs3,
        State.get_set_ne _ _ _ _ h2, hF2 r h1 h4, hs1,
        State.get_set_ne _ _ _ _ h1]
    · have hcSetInv : setInvalid.cost s3 = 3 := by
        show (Cmd.op (.clear FLAG) ;; Cmd.op (.appendZero FLAG)).cost s3 = 3
        rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
        rfl
      show ((Cmd.op (.copy REM SIGMA)) ;; _).cost s ≤ _
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hs2, Cmd.cost_seq,
        Cmd.cost_op, e3', Cmd.cost_seq, Cmd.cost_ifBit_false _ _ _ _ hs3TFLG,
        e4, Cmd.cost_op]
      simp only [Op.cost, hSIG, List.length_replicate, hcSetInv, hs4REM]
      have hd : k - v ≤ k := Nat.sub_le _ _
      have hvk1 : v * (k + 1) = v * k + v := by ring
      omega

/-- **`expandBare` is correct**: appends `expandSym k v` (raw bits) to `BINIT`
and ANDs the validity verdict into `FLAG`. -/
theorem expandBare_run (s : State) (v k : Nat) (b : Bool)
    (hVAL : State.get s VALX = List.replicate v 1)
    (hSIG : State.get s SIGMA = List.replicate k 1)
    (hFLAG : State.get s FLAG = cond b [1] [0]) :
    State.get (expandBare.eval s) BINIT = State.get s BINIT ++ expandSym k v
    ∧ State.get (expandBare.eval s) FLAG = cond (b && decide (v < k)) [1] [0]
    ∧ (∀ r : Var, r ≠ BINIT → r ≠ REM → r ≠ TFLG → r ≠ FLAG → r ≠ IDX2 →
        r ≠ CliqueRelTM.SKIPR → State.get (expandBare.eval s) r = State.get s r)
    ∧ expandBare.cost s ≤ 2 * (v * v) + v * k + k * k + 3 * v + 3 * k + 22 := by
  -- stage 1: v zeros
  obtain ⟨hB1, hF1, hC1⟩ := zeroPad_run VALX s v hVAL
  set s1 := (Cmd.forBnd IDX2 VALX (Cmd.op (.appendZero BINIT))).eval s with hs1
  -- stage 2: the one
  have e2 : (Cmd.op (.appendOne BINIT)).eval s1
      = s1.set BINIT ((State.get s BINIT ++ List.replicate v 0) ++ [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hB1]
  set s2 := s1.set BINIT ((State.get s BINIT ++ List.replicate v 0) ++ [1]) with hs2
  have hs2VAL : State.get s2 VALX = List.replicate v 1 := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide),
      hF1 VALX (by decide) (by decide), hVAL]
  have hs2SIG : State.get s2 SIGMA = List.replicate k 1 := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide),
      hF1 SIGMA (by decide) (by decide), hSIG]
  have hs2FLAG : State.get s2 FLAG = cond b [1] [0] := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide),
      hF1 FLAG (by decide) (by decide), hFLAG]
  -- stage 3: the check
  obtain ⟨hR3, hFL3, hF3, hC3⟩ := remCheck_run s2 v k b hs2VAL hs2SIG hs2FLAG
  set s3 := remCheck.eval s2 with hs3
  have hs3BIN : State.get s3 BINIT
      = (State.get s BINIT ++ List.replicate v 0) ++ [1] := by
    rw [hF3 BINIT (by decide) (by decide) (by decide) (by decide) (by decide),
      hs2, State.get_set_eq]
  -- stage 4: the k−v−1 zeros
  obtain ⟨hB4, hF4, hC4⟩ := zeroPad_run REM s3 (k - v - 1) hR3
  have heval : expandBare.eval s
      = (Cmd.forBnd IDX2 REM (Cmd.op (.appendZero BINIT))).eval s3 := by
    show ((Cmd.forBnd IDX2 VALX (Cmd.op (.appendZero BINIT))) ;; _).eval s = _
    rw [Cmd.eval_seq, ← hs1, Cmd.eval_seq, e2, Cmd.eval_seq, ← hs3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval, hB4, hs3BIN]
    simp [expandSym, List.append_assoc]
  · rw [heval, hF4 FLAG (by decide) (by decide), hFL3]
  · intro r h1 h2 h3 h4 h5 h6
    rw [heval, hF4 r h1 h5, hF3 r h2 h3 h4 h5 h6, hs2,
      State.get_set_ne _ _ _ _ h1, hF1 r h1 h5]
  · have hcost : expandBare.cost s
        = 1 + (Cmd.forBnd IDX2 VALX (Cmd.op (.appendZero BINIT))).cost s
          + (1 + 1 + (1 + remCheck.cost s2
            + (Cmd.forBnd IDX2 REM (Cmd.op (.appendZero BINIT))).cost s3)) := by
      show ((Cmd.forBnd IDX2 VALX (Cmd.op (.appendZero BINIT))) ;; _).cost s = _
      rw [Cmd.cost_seq, Cmd.cost_seq, ← hs1, Cmd.cost_op, e2, Cmd.cost_seq,
        ← hs3]
      simp only [Op.cost]
    rw [hcost]
    have hd : k - v - 1 ≤ k := by omega
    have hC4' : (Cmd.forBnd IDX2 REM (Cmd.op (.appendZero BINIT))).cost s3
        ≤ 1 + k + k * k := by
      have hsq : (k - v - 1) * (k - v - 1) ≤ k * k := Nat.mul_le_mul hd hd
      omega
    omega

/-- **`expandSent` is correct**: appends the sentinel-format expansion
`encSElems (expandSym k v)` to `BOUT` and ANDs the verdict into `FLAG`. -/
theorem expandSent_run (s : State) (v k : Nat) (b : Bool)
    (hVAL : State.get s VALX = List.replicate v 1)
    (hSIG : State.get s SIGMA = List.replicate k 1)
    (hFLAG : State.get s FLAG = cond b [1] [0]) :
    State.get (expandSent.eval s) BOUT
      = State.get s BOUT ++ encSElems (expandSym k v)
    ∧ State.get (expandSent.eval s) FLAG = cond (b && decide (v < k)) [1] [0]
    ∧ (∀ r : Var, r ≠ BOUT → r ≠ REM → r ≠ TFLG → r ≠ FLAG → r ≠ IDX2 →
        r ≠ CliqueRelTM.SKIPR → State.get (expandSent.eval s) r = State.get s r)
    ∧ expandSent.cost s ≤ 2 * (v * v) + v * k + k * k + 5 * v + 5 * k + 30 := by
  -- stage 1: v zero-bit elements
  obtain ⟨hB1, hF1, hC1⟩ := elemPad_run VALX s v hVAL
  set s1 := (Cmd.forBnd IDX2 VALX
    (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT))).eval s with hs1
  -- stage 2: the one-bit element [1,1,0]
  have e2 : (Cmd.op (.appendOne BOUT)).eval s1
      = s1.set BOUT ((State.get s BOUT ++ encSElems (List.replicate v 0)) ++ [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hB1]
  set s2a := s1.set BOUT ((State.get s BOUT ++ encSElems (List.replicate v 0)) ++ [1]) with hs2a
  have hs2aBOUT : State.get s2a BOUT
      = (State.get s BOUT ++ encSElems (List.replicate v 0)) ++ [1] := by
    rw [hs2a]; exact State.get_set_eq _ _ _
  have e2b : (Cmd.op (.appendOne BOUT)).eval s2a
      = s2a.set BOUT (((State.get s BOUT ++ encSElems (List.replicate v 0)) ++ [1]) ++ [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hs2aBOUT]
  set s2b := s2a.set BOUT (((State.get s BOUT ++ encSElems (List.replicate v 0)) ++ [1]) ++ [1]) with hs2b
  have hs2bBOUT : State.get s2b BOUT
      = ((State.get s BOUT ++ encSElems (List.replicate v 0)) ++ [1]) ++ [1] := by
    rw [hs2b]; exact State.get_set_eq _ _ _
  have e2c : (Cmd.op (.appendZero BOUT)).eval s2b
      = s2b.set BOUT ((((State.get s BOUT ++ encSElems (List.replicate v 0)) ++ [1]) ++ [1]) ++ [0]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hs2bBOUT]
  set s2 := s2b.set BOUT ((((State.get s BOUT ++ encSElems (List.replicate v 0)) ++ [1]) ++ [1]) ++ [0]) with hs2
  have hs2get : ∀ r : Var, r ≠ BOUT → r ≠ IDX2 →
      State.get s2 r = State.get s r := by
    intro r h1 h2
    rw [hs2, State.get_set_ne _ _ _ _ h1, hs2b, State.get_set_ne _ _ _ _ h1,
      hs2a, State.get_set_ne _ _ _ _ h1, hF1 r h1 h2]
  have hs2VAL : State.get s2 VALX = List.replicate v 1 := by
    rw [hs2get VALX (by decide) (by decide), hVAL]
  have hs2SIG : State.get s2 SIGMA = List.replicate k 1 := by
    rw [hs2get SIGMA (by decide) (by decide), hSIG]
  have hs2FLAG : State.get s2 FLAG = cond b [1] [0] := by
    rw [hs2get FLAG (by decide) (by decide), hFLAG]
  -- stage 3: the check
  obtain ⟨hR3, hFL3, hF3, hC3⟩ := remCheck_run s2 v k b hs2VAL hs2SIG hs2FLAG
  set s3 := remCheck.eval s2 with hs3
  have hs3BOUT : State.get s3 BOUT
      = (((State.get s BOUT ++ encSElems (List.replicate v 0)) ++ [1]) ++ [1]) ++ [0] := by
    rw [hF3 BOUT (by decide) (by decide) (by decide) (by decide) (by decide),
      hs2, State.get_set_eq]
  -- stage 4: the k−v−1 zero-bit elements
  obtain ⟨hB4, hF4, hC4⟩ := elemPad_run REM s3 (k - v - 1) hR3
  have heval : expandSent.eval s
      = (Cmd.forBnd IDX2 REM
          (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT))).eval s3 := by
    show ((Cmd.forBnd IDX2 VALX _) ;; _).eval s = _
    rw [Cmd.eval_seq, ← hs1, Cmd.eval_seq, e2, Cmd.eval_seq, e2b, Cmd.eval_seq,
      e2c, Cmd.eval_seq, ← hs3]
  have hdecomp : encSElems (expandSym k v)
      = (encSElems (List.replicate v 0) ++ [1, 1, 0])
        ++ encSElems (List.replicate (k - v - 1) 0) := by
    show encSElems (List.replicate v 0 ++ 1 :: List.replicate (k - v - 1) 0) = _
    rw [show (1 : Nat) :: List.replicate (k - v - 1) 0
        = [1] ++ List.replicate (k - v - 1) 0 from rfl,
      encSElems_append, encSElems_append]
    simp [encSElems, encSElem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval, hB4, hs3BOUT, hdecomp]
    simp [List.append_assoc]
  · rw [heval, hF4 FLAG (by decide) (by decide), hFL3]
  · intro r h1 h2 h3 h4 h5 h6
    rw [heval, hF4 r h1 h5, hF3 r h2 h3 h4 h5 h6, hs2get r h1 h5]
  · have hcost : expandSent.cost s
        = 1 + (Cmd.forBnd IDX2 VALX
            (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT))).cost s
          + (1 + 1 + (1 + 1 + (1 + 1 + (1 + remCheck.cost s2
            + (Cmd.forBnd IDX2 REM
                (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT))).cost s3)))) := by
      show ((Cmd.forBnd IDX2 VALX _) ;; _).cost s = _
      rw [Cmd.cost_seq, Cmd.cost_seq, ← hs1, Cmd.cost_op, e2, Cmd.cost_seq,
        Cmd.cost_op, e2b, Cmd.cost_seq, Cmd.cost_op, e2c, Cmd.cost_seq, ← hs3]
      simp only [Op.cost]
    rw [hcost]
    have hd : k - v - 1 ≤ k := by omega
    have hC4' : (Cmd.forBnd IDX2 REM
        (Cmd.op (.appendOne BOUT) ;; Cmd.op (.appendZero BOUT))).cost s3
        ≤ 1 + 3 * k + k * k := by
      have hsq : (k - v - 1) * (k - v - 1) ≤ k * k := Nat.mul_le_mul hd hd
      omega
    omega

/-! ## Stream-suffix helpers for the loop invariants -/

theorem expandStr_append (k : Nat) (a b : List Nat) :
    expandStr k (a ++ b) = expandStr k a ++ expandStr k b := by
  induction a with
  | nil => rfl
  | cons v a ih => rw [List.cons_append, expandStr, expandStr, ih,
      List.append_assoc]

theorem expandStr_snoc (k : Nat) (a : List Nat) (v : Nat) :
    expandStr k (a ++ [v]) = expandStr k a ++ expandSym k v := by
  rw [expandStr_append]
  simp [expandStr]

theorem allLtB_snoc (k : Nat) (a : List Nat) (v : Nat) :
    allLtB k (a ++ [v]) = (allLtB k a && decide (v < k)) := by
  simp [allLtB, List.all_append]

theorem expandItems_snoc (k : Nat) (a : List (Option Nat)) (it : Option Nat) :
    expandItems k (a ++ [it]) = expandItems k a ++ expandItem k it := by
  rw [expandItems_append]
  simp [expandItems]

theorem itemsOkB_snoc (k : Nat) (a : List (Option Nat)) (it : Option Nat) :
    itemsOkB k (a ++ [it]) = (itemsOkB k a && itemOkB k it) := by
  simp [itemsOkB, List.all_append]

theorem encNats_drop_le (xs : List Nat) (i : Nat) :
    (encNats (xs.drop i)).length ≤ (encNats xs).length := by
  conv_rhs => rw [← List.take_append_drop i xs]
  rw [encNats_append, List.length_append]
  omega

theorem encItems_drop_le (its : List (Option Nat)) (i : Nat) :
    (encItems (its.drop i)).length ≤ (encItems its).length := by
  conv_rhs => rw [← List.take_append_drop i its]
  rw [encItems_append, List.length_append]
  omega

theorem encItem_some_append (v : Nat) (X : List Nat) :
    encItem (some v) ++ X = 1 :: (List.replicate v 1 ++ 0 :: X) := by
  simp [encItem]

theorem encItem_none_append (X : List Nat) :
    encItem none ++ X = 0 :: X := rfl

/-- Total length of the expanded sentinel stream (for the copy-out cost). -/
theorem expandItems_length_le (k : Nat) (its : List (Option Nat)) :
    (expandItems k its).length
      ≤ 3 * (k * its.length + (encItems its).length) := by
  induction its with
  | nil => simp [expandItems]
  | cons it its ih =>
      rw [expandItems, List.length_append, encItems, List.length_append,
        List.length_cons]
      have h1 := expandItem_length_le k it
      have hmul : k * (its.length + 1) = k * its.length + k := by ring
      omega

/-! ## The per-block gadget for `init`: run + cost -/

/-- Uniform per-iteration budget for the `init` loop. -/
def initStepBound (S K : Nat) : Nat :=
  4 * (S * S) + S * K + K * K + 10 * S + 3 * K + 40

/-- `initStep`, block case: `SCAN` starts with a bare block `1^v 0`. Consumes
it, appends `expandSym k v` to `BINIT`, and ANDs the verdict into `FLAG`. -/
theorem initStep_block (s : State) (v : Nat) (X : List Nat) (k : Nat)
    (b : Bool) (S : Nat)
    (hSC : State.get s SCAN = encNat v ++ X)
    (hSIG : State.get s SIGMA = List.replicate k 1)
    (hFLAG : State.get s FLAG = cond b [1] [0])
    (hS : (State.get s SCAN).length ≤ S) :
    State.get (initStep.eval s) SCAN = X
    ∧ State.get (initStep.eval s) BINIT = State.get s BINIT ++ expandSym k v
    ∧ State.get (initStep.eval s) FLAG = cond (b && decide (v < k)) [1] [0]
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ BINIT → r ≠ VALX → r ≠ REM → r ≠ TFLG →
        r ≠ FLAG → r ≠ IDX2 → r ≠ IDXR → r ≠ CliqueRelTM.HEAD →
        r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
        State.get (initStep.eval s) r = State.get s r)
    ∧ initStep.cost s ≤ initStepBound S k := by
  have hv : v + 1 ≤ S := by
    have : (State.get s SCAN).length = v + 1 + X.length := by
      rw [hSC, List.length_append, encNat_length]
    omega
  have hne : (State.get s SCAN).isEmpty = false := by
    rw [hSC, encNat_append]
    cases v <;> simp [List.replicate_succ]
  have e0 : (Cmd.op (.nonEmpty TFLG SCAN)).eval s = s.set TFLG [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hne]
    rfl
  set w := s.set TFLG [1] with hw
  have hwTFLG : State.get w TFLG = [1] := State.get_set_eq _ _ _
  have hwSC : State.get w SCAN = List.replicate v 1 ++ 0 :: X := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide), hSC, encNat_append]
  -- drain the block
  obtain ⟨hVAL, hSC2, hF2⟩ := CliqueRelTM.readNum_run w v X VALX SCAN IDXR
    hwSC (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  set u1 := (CliqueRelTM.readNum VALX SCAN IDXR).eval w with hu1
  have hu1SIG : State.get u1 SIGMA = List.replicate k 1 := by
    rw [hF2 SIGMA (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hw, State.get_set_ne _ _ _ _ (by decide), hSIG]
  have hu1FLAG : State.get u1 FLAG = cond b [1] [0] := by
    rw [hF2 FLAG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hw, State.get_set_ne _ _ _ _ (by decide), hFLAG]
  -- expand
  obtain ⟨hB3, hFL3, hF3, hC3⟩ := expandBare_run u1 v k b hVAL hu1SIG hu1FLAG
  set u2 := expandBare.eval u1 with hu2
  have heval : initStep.eval s = u2 := by
    show ((Cmd.op (.nonEmpty TFLG SCAN)) ;; _).eval s = _
    rw [Cmd.eval_seq, e0, Cmd.eval_ifBit_true _ _ _ _ hwTFLG, Cmd.eval_seq,
      ← hu1, ← hu2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [heval, hF3 SCAN (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hSC2
  · rw [heval, hB3, hF2 BINIT (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hw, State.get_set_ne _ _ _ _ (by decide)]
  · rw [heval, hFL3]
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    rw [heval, hF3 r h2 h4 h5 h6 h7 h11, hF2 r h1 h3 h10 h9 h11 h8, hw,
      State.get_set_ne _ _ _ _ h5]
  · have hrn := CliqueRelTM.readNum_cost w VALX SCAN IDXR (by decide)
      (by decide) (by decide) (by decide) (by decide)
    have hwSlen : (State.get w SCAN).length ≤ S := by
      rw [hw, State.get_set_ne _ _ _ _ (by decide)]
      exact hS
    have hrn' : (CliqueRelTM.readNum VALX SCAN IDXR).cost w
        ≤ 2 * (S * S) + 7 * S + 7 := by
      set L := (State.get w SCAN).length with hL
      have h2LL : 2 * L * L ≤ 2 * (S * S) := by
        calc 2 * L * L = 2 * (L * L) := by ring
          _ ≤ 2 * (S * S) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hwSlen hwSlen)
      omega
    have hcost : initStep.cost s
        = 1 + 1 + (1 + (1 + (CliqueRelTM.readNum VALX SCAN IDXR).cost w
            + expandBare.cost u1)) := by
      show ((Cmd.op (.nonEmpty TFLG SCAN)) ;; _).cost s = _
      rw [Cmd.cost_seq, Cmd.cost_op, e0, Cmd.cost_ifBit_true _ _ _ _ hwTFLG,
        Cmd.cost_seq, ← hu1]
      rfl
    rw [hcost]
    have hvS : v ≤ S := by omega
    have hC3' : expandBare.cost u1
        ≤ 2 * (S * S) + S * k + k * k + 3 * S + 3 * k + 22 := by
      have hvv : v * v ≤ S * S := Nat.mul_le_mul hvS hvS
      have hvk : v * k ≤ S * k := Nat.mul_le_mul_right k hvS
      omega
    show _ ≤ initStepBound S k
    unfold initStepBound
    omega

/-- `initStep`, idle case: `SCAN` is exhausted. -/
theorem initStep_idle (s : State) (hSC : State.get s SCAN = []) :
    initStep.eval s = (s.set TFLG [0]).set CliqueRelTM.SKIPR [1]
    ∧ initStep.cost s = 6 := by
  have hne : (State.get s SCAN).isEmpty = true := by rw [hSC]; rfl
  have e0 : (Cmd.op (.nonEmpty TFLG SCAN)).eval s = s.set TFLG [0] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hne]
    rfl
  have hwTFLG : State.get (s.set TFLG [0]) TFLG ≠ [1] := by
    rw [State.get_set_eq]; decide
  constructor
  · show ((Cmd.op (.nonEmpty TFLG SCAN)) ;; _).eval s = _
    rw [Cmd.eval_seq, e0, Cmd.eval_ifBit_false _ _ _ _ hwTFLG,
      CliqueRelTM.cSkip_eval]
  · show ((Cmd.op (.nonEmpty TFLG SCAN)) ;; _).cost s = _
    rw [Cmd.cost_seq, Cmd.cost_op, e0, Cmd.cost_ifBit_false _ _ _ _ hwTFLG,
      CliqueRelTM.cSkip_cost]
    rfl

/-! ## The `init` loop: invariant + step + run -/

/-- The init-loop fold invariant: after `i` iterations the stream holds the
remaining blocks, `BINIT` the expanded prefix, and `FLAG` the ANDed validity
of the processed prefix. Beyond `|xs|` the loop idles (`drop`/`take` clamp). -/
def IInv (xs : List Nat) (k : Nat) (b0 : Bool) (u : State) (i : Nat)
    (st : State) : Prop :=
  State.get st SCAN = encNats (xs.drop i)
  ∧ State.get st BINIT = expandStr k (xs.take i)
  ∧ State.get st FLAG = cond (b0 && allLtB k (xs.take i)) [1] [0]
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ BINIT → r ≠ VALX → r ≠ REM → r ≠ TFLG →
      r ≠ FLAG → r ≠ IDX2 → r ≠ IDXR → r ≠ IDXO → r ≠ CliqueRelTM.HEAD →
      r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
      State.get st r = State.get u r)

/-- One `initStep` iteration preserves `IInv`, within the uniform budget. -/
theorem initStep_step (xs : List Nat) (k : Nat) (b0 : Bool) (u : State)
    (S : Nat) (hS : (encNats xs).length ≤ S)
    (hSIG : State.get u SIGMA = List.replicate k 1)
    (i : Nat) (st : State) (h : IInv xs k b0 u i st) :
    IInv xs k b0 u (i + 1) (initStep.eval (st.set IDXO (List.replicate i 1)))
    ∧ initStep.cost (st.set IDXO (List.replicate i 1)) ≤ initStepBound S k := by
  obtain ⟨hSCAN, hBIN, hFLG, hframe⟩ := h
  set w := st.set IDXO (List.replicate i 1) with hw
  have hwframe : ∀ r : Var, r ≠ IDXO → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSIG : State.get w SIGMA = List.replicate k 1 := by
    rw [hwframe SIGMA (by decide), hframe SIGMA (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hSIG]
  by_cases hi : i < xs.length
  · -- block iteration
    have hdrop : xs.drop i = xs[i] :: xs.drop (i + 1) := List.drop_eq_getElem_cons hi
    have htake : xs.take (i + 1) = xs.take i ++ [xs[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
    have hSCw : State.get w SCAN = encNat xs[i] ++ encNats (xs.drop (i + 1)) := by
      rw [hwframe SCAN (by decide), hSCAN, hdrop]
      rfl
    have hSw : (State.get w SCAN).length ≤ S := by
      rw [hwframe SCAN (by decide), hSCAN]
      exact le_trans (encNats_drop_le xs i) hS
    have hFLGw : State.get w FLAG = cond (b0 && allLtB k (xs.take i)) [1] [0] := by
      rw [hwframe FLAG (by decide), hFLG]
    obtain ⟨hA, hB, hC, hF, hCost⟩ := initStep_block w xs[i] _ k
      (b0 && allLtB k (xs.take i)) S hSCw hwSIG hFLGw hSw
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hCost⟩
    · rw [hA]
    · rw [hB, hwframe BINIT (by decide), hBIN, htake, expandStr_snoc]
    · rw [hC, htake, allLtB_snoc, Bool.and_assoc]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      rw [hF r h1 h2 h3 h4 h5 h6 h7 h8 h10 h11 h12, hwframe r h9,
        hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12]
  · -- idle iteration
    have hlen : xs.length ≤ i := Nat.le_of_not_lt hi
    have hSCw : State.get w SCAN = [] := by
      rw [hwframe SCAN (by decide), hSCAN, List.drop_eq_nil_of_le hlen]
      rfl
    obtain ⟨heval, hcost⟩ := initStep_idle w hSCw
    have hbudget : (6 : Nat) ≤ initStepBound S k := by
      unfold initStepBound; omega
    refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega⟩
    · rw [heval, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hwframe SCAN (by decide), hSCAN,
        List.drop_eq_nil_of_le hlen, List.drop_eq_nil_of_le (by omega)]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hwframe BINIT (by decide), hBIN,
        List.take_of_length_le hlen, List.take_of_length_le (by omega)]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hwframe FLAG (by decide), hFLG,
        List.take_of_length_le hlen, List.take_of_length_le (by omega)]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      rw [heval, State.get_set_ne _ _ _ _ h12, State.get_set_ne _ _ _ _ h5,
        hwframe r h9, hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12]

/-- **The `init` loop is correct**: on `SCAN = encNats xs` (with the loop
bound register `bnd` at least as long as the stream) it writes
`expandStr k xs` to `BINIT` and ANDs the whole stream's validity into `FLAG`. -/
theorem initLoop_run (xs : List Nat) (k : Nat) (b0 : Bool) (u : State)
    (bnd : Var) (S : Nat)
    (hSlen : (State.get u bnd).length = S)
    (hS : (encNats xs).length ≤ S)
    (hSC : State.get u SCAN = encNats xs)
    (hSIG : State.get u SIGMA = List.replicate k 1)
    (hFLAG : State.get u FLAG = cond b0 [1] [0])
    (hBIN : State.get u BINIT = []) :
    State.get ((Cmd.forBnd IDXO bnd initStep).eval u) BINIT = expandStr k xs
    ∧ State.get ((Cmd.forBnd IDXO bnd initStep).eval u) FLAG
        = cond (b0 && allLtB k xs) [1] [0]
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ BINIT → r ≠ VALX → r ≠ REM → r ≠ TFLG →
        r ≠ FLAG → r ≠ IDX2 → r ≠ IDXR → r ≠ IDXO → r ≠ CliqueRelTM.HEAD →
        r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
        State.get ((Cmd.forBnd IDXO bnd initStep).eval u) r = State.get u r)
    ∧ (Cmd.forBnd IDXO bnd initStep).cost u
        ≤ 1 + S * initStepBound S k + S * S := by
  have hxslen : xs.length ≤ S := by
    have h1 : xs.length ≤ (encNats xs).length := by
      rw [encNats_length]
      exact list_length_le_size xs
    omega
  have hbase : IInv xs k b0 u 0 u := by
    refine ⟨by rw [List.drop_zero]; exact hSC, by rw [List.take_zero]; exact hBIN,
      ?_, fun r _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    rw [List.take_zero]
    show State.get u FLAG = cond (b0 && allLtB k []) [1] [0]
    rw [show allLtB k [] = true from rfl, Bool.and_true]
    exact hFLAG
  have hInv : IInv xs k b0 u S
      (Cmd.foldlState initStep IDXO (List.range S) u) :=
    Cmd.foldlState_range_induct initStep IDXO S u (IInv xs k b0 u) hbase
      (fun i st _ hM => (initStep_step xs k b0 u S hS hSIG i st hM).1)
  obtain ⟨-, hBOUT, hFLG, hframe⟩ := hInv
  have heval : (Cmd.forBnd IDXO bnd initStep).eval u
      = Cmd.foldlState initStep IDXO (List.range S) u := by
    rw [Cmd.eval_forBnd, hSlen]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval, hBOUT, List.take_of_length_le hxslen]
  · rw [heval, hFLG, List.take_of_length_le hxslen]
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    rw [heval]
    exact hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  · have h := Cmd.cost_forBnd_le IDXO bnd initStep u (initStepBound S k)
      (IInv xs k b0 u) hbase
      (fun i st hi hM => (initStep_step xs k b0 u S hS hSIG i st hM).1)
      (fun i st hi hM => (initStep_step xs k b0 u S hS hSIG i st hM).2)
    rw [hSlen] at h
    exact h

/-! ## The per-item gadget for sentinel streams: run + cost -/

/-- Uniform per-iteration budget for the sentinel-stream loops. -/
def sentStepBound (S K : Nat) : Nat :=
  4 * (S * S) + S * K + K * K + 14 * S + 5 * K + 50

/-- `sentStep`, element case: `SCAN` starts with a sentinel element `1 1^v 0`.
Consumes it, appends the expansion to `BOUT`, ANDs the verdict into `FLAG`. -/
theorem sentStep_elem (s : State) (v : Nat) (X : List Nat) (k : Nat)
    (b : Bool) (S : Nat)
    (hSC : State.get s SCAN = encItem (some v) ++ X)
    (hSIG : State.get s SIGMA = List.replicate k 1)
    (hFLAG : State.get s FLAG = cond b [1] [0])
    (hS : (State.get s SCAN).length ≤ S) :
    State.get (sentStep.eval s) SCAN = X
    ∧ State.get (sentStep.eval s) BOUT
        = State.get s BOUT ++ expandItem k (some v)
    ∧ State.get (sentStep.eval s) FLAG = cond (b && decide (v < k)) [1] [0]
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ BOUT → r ≠ VALX → r ≠ REM → r ≠ TFLG →
        r ≠ FLAG → r ≠ IDX2 → r ≠ IDXR → r ≠ CliqueRelTM.HEAD →
        r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
        State.get (sentStep.eval s) r = State.get s r)
    ∧ sentStep.cost s ≤ sentStepBound S k := by
  have hlenSC : (State.get s SCAN).length = v + 2 + X.length := by
    rw [hSC, List.length_append]
    simp [encItem]
  have hv : v + 2 ≤ S := by omega
  have hSCcons : State.get s SCAN = 1 :: (List.replicate v 1 ++ 0 :: X) := by
    rw [hSC, encItem_some_append]
  have hne : (State.get s SCAN).isEmpty = false := by
    rw [hSCcons]; rfl
  have e0 : (Cmd.op (.nonEmpty TFLG SCAN)).eval s = s.set TFLG [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hne]
    rfl
  set w := s.set TFLG [1] with hw
  have hwTFLG : State.get w TFLG = [1] := State.get_set_eq _ _ _
  have hwSC : State.get w SCAN = 1 :: (List.replicate v 1 ++ 0 :: X) := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide), hSCcons]
  -- read the sentinel
  have e1 : (Cmd.op (.head TFLG SCAN)).eval w = w.set TFLG [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hwSC]
  set w1 := w.set TFLG [1] with hw1
  have hw1TFLG : State.get w1 TFLG = [1] := State.get_set_eq _ _ _
  have hw1SC : State.get w1 SCAN = 1 :: (List.replicate v 1 ++ 0 :: X) := by
    rw [hw1, State.get_set_ne _ _ _ _ (by decide), hwSC]
  -- drop the sentinel
  have e2 : (Cmd.op (.tail SCAN SCAN)).eval w1
      = w1.set SCAN (List.replicate v 1 ++ 0 :: X) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw1SC, List.tail_cons]
  set w2 := w1.set SCAN (List.replicate v 1 ++ 0 :: X) with hw2
  have hw2TFLG : State.get w2 TFLG = [1] := by
    rw [hw2, State.get_set_ne _ _ _ _ (by decide), hw1TFLG]
  have hw2SC : State.get w2 SCAN = List.replicate v 1 ++ 0 :: X :=
    State.get_set_eq _ _ _
  -- drain the block
  obtain ⟨hVAL, hSC3, hF3⟩ := CliqueRelTM.readNum_run w2 v X VALX SCAN IDXR
    hw2SC (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  set u1 := (CliqueRelTM.readNum VALX SCAN IDXR).eval w2 with hu1
  have hu1get : ∀ r : Var, r ≠ SCAN → r ≠ VALX → r ≠ TFLG →
      r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.SKIPR →
      r ≠ IDXR → State.get u1 r = State.get s r := by
    intro r h1 h2 h3 h4 h5 h6 h7
    rw [hF3 r h1 h2 h4 h5 h6 h7, hw2, State.get_set_ne _ _ _ _ h1, hw1,
      State.get_set_ne _ _ _ _ h3, hw, State.get_set_ne _ _ _ _ h3]
  have hu1SIG : State.get u1 SIGMA = List.replicate k 1 := by
    rw [hu1get SIGMA (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hSIG]
  have hu1FLAG : State.get u1 FLAG = cond b [1] [0] := by
    rw [hu1get FLAG (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hFLAG]
  -- expand
  obtain ⟨hB4, hFL4, hF4, hC4⟩ := expandSent_run u1 v k b hVAL hu1SIG hu1FLAG
  set u2 := expandSent.eval u1 with hu2
  have heval : sentStep.eval s = u2 := by
    show ((Cmd.op (.nonEmpty TFLG SCAN)) ;; _).eval s = _
    rw [Cmd.eval_seq, e0, Cmd.eval_ifBit_true _ _ _ _ hwTFLG, Cmd.eval_seq,
      e1, Cmd.eval_seq, e2, Cmd.eval_ifBit_true _ _ _ _ hw2TFLG, Cmd.eval_seq,
      ← hu1, ← hu2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [heval, hF4 SCAN (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hSC3
  · rw [heval, hB4, hu1get BOUT (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    rfl
  · rw [heval, hFL4]
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    rw [heval, hF4 r h2 h4 h5 h6 h7 h11, hu1get r h1 h3 h5 h10 h9 h11 h8]
  · -- cost
    have hrn := CliqueRelTM.readNum_cost w2 VALX SCAN IDXR (by decide)
      (by decide) (by decide) (by decide) (by decide)
    have hw2Slen : (State.get w2 SCAN).length ≤ S := by
      rw [hw2SC]
      simp only [List.length_append, List.length_replicate, List.length_cons]
      omega
    have hrn' : (CliqueRelTM.readNum VALX SCAN IDXR).cost w2
        ≤ 2 * (S * S) + 7 * S + 7 := by
      set L := (State.get w2 SCAN).length with hL
      have h2LL : 2 * L * L ≤ 2 * (S * S) := by
        calc 2 * L * L = 2 * (L * L) := by ring
          _ ≤ 2 * (S * S) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hw2Slen hw2Slen)
      omega
    have hw1Slen : (State.get w1 SCAN).length ≤ S := by
      rw [hw1SC]
      simp only [List.length_cons, List.length_append, List.length_replicate,
        List.length_cons]
      omega
    have hcost : sentStep.cost s
        = 1 + 1 + (1 + (1 + 1 + (1 + ((State.get w1 SCAN).length + 1)
            + (1 + (1 + (CliqueRelTM.readNum VALX SCAN IDXR).cost w2
              + expandSent.cost u1))))) := by
      show ((Cmd.op (.nonEmpty TFLG SCAN)) ;; _).cost s = _
      rw [Cmd.cost_seq, Cmd.cost_op, e0, Cmd.cost_ifBit_true _ _ _ _ hwTFLG,
        Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, Cmd.cost_op, e2,
        Cmd.cost_ifBit_true _ _ _ _ hw2TFLG, Cmd.cost_seq, ← hu1]
      simp only [Op.cost, hw1SC]
    rw [hcost]
    have hvS : v ≤ S := by omega
    have hC4' : expandSent.cost u1
        ≤ 2 * (S * S) + S * k + k * k + 5 * S + 5 * k + 30 := by
      have hvv : v * v ≤ S * S := Nat.mul_le_mul hvS hvS
      have hvk : v * k ≤ S * k := Nat.mul_le_mul_right k hvS
      omega
    show _ ≤ sentStepBound S k
    unfold sentStepBound
    omega

/-- `sentStep`, terminator case: `SCAN` starts with a list terminator `0`.
Consumes it and copies it to `BOUT`. -/
theorem sentStep_term (s : State) (X : List Nat) (S : Nat)
    (hSC : State.get s SCAN = encItem none ++ X)
    (hS : (State.get s SCAN).length ≤ S) :
    State.get (sentStep.eval s) SCAN = X
    ∧ State.get (sentStep.eval s) BOUT = State.get s BOUT ++ [0]
    ∧ State.get (sentStep.eval s) FLAG = State.get s FLAG
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ BOUT → r ≠ TFLG →
        State.get (sentStep.eval s) r = State.get s r)
    ∧ sentStep.cost s ≤ S + 12 := by
  have hSCcons : State.get s SCAN = 0 :: X := by
    rw [hSC, encItem_none_append]
  have hne : (State.get s SCAN).isEmpty = false := by
    rw [hSCcons]; rfl
  have e0 : (Cmd.op (.nonEmpty TFLG SCAN)).eval s = s.set TFLG [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hne]
    rfl
  set w := s.set TFLG [1] with hw
  have hwTFLG : State.get w TFLG = [1] := State.get_set_eq _ _ _
  have hwSC : State.get w SCAN = 0 :: X := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide), hSCcons]
  have e1 : (Cmd.op (.head TFLG SCAN)).eval w = w.set TFLG [0] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hwSC]
  set w1 := w.set TFLG [0] with hw1
  have hw1TFLG : State.get w1 TFLG = [0] := State.get_set_eq _ _ _
  have hw1SC : State.get w1 SCAN = 0 :: X := by
    rw [hw1, State.get_set_ne _ _ _ _ (by decide), hwSC]
  have e2 : (Cmd.op (.tail SCAN SCAN)).eval w1 = w1.set SCAN X := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw1SC, List.tail_cons]
  set w2 := w1.set SCAN X with hw2
  have hw2TFLG : State.get w2 TFLG ≠ [1] := by
    rw [hw2, State.get_set_ne _ _ _ _ (by decide), hw1TFLG]
    decide
  have hw2BOUT : State.get w2 BOUT = State.get s BOUT := by
    rw [hw2, State.get_set_ne _ _ _ _ (by decide), hw1,
      State.get_set_ne _ _ _ _ (by decide), hw,
      State.get_set_ne _ _ _ _ (by decide)]
  have e3 : (Cmd.op (.appendZero BOUT)).eval w2
      = w2.set BOUT (State.get s BOUT ++ [0]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw2BOUT]
  have heval : sentStep.eval s = w2.set BOUT (State.get s BOUT ++ [0]) := by
    show ((Cmd.op (.nonEmpty TFLG SCAN)) ;; _).eval s = _
    rw [Cmd.eval_seq, e0, Cmd.eval_ifBit_true _ _ _ _ hwTFLG, Cmd.eval_seq,
      e1, Cmd.eval_seq, e2, Cmd.eval_ifBit_false _ _ _ _ hw2TFLG, e3]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [heval, State.get_set_ne _ _ _ _ (by decide), hw2, State.get_set_eq]
  · rw [heval, State.get_set_eq]
  · rw [heval, State.get_set_ne _ _ _ _ (by decide), hw2,
      State.get_set_ne _ _ _ _ (by decide), hw1,
      State.get_set_ne _ _ _ _ (by decide), hw,
      State.get_set_ne _ _ _ _ (by decide)]
  · intro r h1 h2 h3
    rw [heval, State.get_set_ne _ _ _ _ h2, hw2,
      State.get_set_ne _ _ _ _ h1, hw1, State.get_set_ne _ _ _ _ h3, hw,
      State.get_set_ne _ _ _ _ h3]
  · have hcost : sentStep.cost s
        = 1 + 1 + (1 + (1 + 1 + (1 + ((State.get w1 SCAN).length + 1)
            + (1 + 1)))) := by
      show ((Cmd.op (.nonEmpty TFLG SCAN)) ;; _).cost s = _
      rw [Cmd.cost_seq, Cmd.cost_op, e0, Cmd.cost_ifBit_true _ _ _ _ hwTFLG,
        Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, Cmd.cost_op, e2,
        Cmd.cost_ifBit_false _ _ _ _ hw2TFLG, Cmd.cost_op]
      rfl
    rw [hcost]
    have hlen : (State.get w1 SCAN).length ≤ S := by
      have hX : (State.get s SCAN).length = X.length + 1 := by
        rw [hSCcons]
        rfl
      rw [hw1SC]
      simp only [List.length_cons]
      omega
    omega

/-- `sentStep`, idle case: `SCAN` is exhausted. -/
theorem sentStep_idle (s : State) (hSC : State.get s SCAN = []) :
    sentStep.eval s = (s.set TFLG [0]).set CliqueRelTM.SKIPR [1]
    ∧ sentStep.cost s = 6 := by
  have hne : (State.get s SCAN).isEmpty = true := by rw [hSC]; rfl
  have e0 : (Cmd.op (.nonEmpty TFLG SCAN)).eval s = s.set TFLG [0] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hne]
    rfl
  have hwTFLG : State.get (s.set TFLG [0]) TFLG ≠ [1] := by
    rw [State.get_set_eq]; decide
  constructor
  · show ((Cmd.op (.nonEmpty TFLG SCAN)) ;; _).eval s = _
    rw [Cmd.eval_seq, e0, Cmd.eval_ifBit_false _ _ _ _ hwTFLG,
      CliqueRelTM.cSkip_eval]
  · show ((Cmd.op (.nonEmpty TFLG SCAN)) ;; _).cost s = _
    rw [Cmd.cost_seq, Cmd.cost_op, e0, Cmd.cost_ifBit_false _ _ _ _ hwTFLG,
      CliqueRelTM.cSkip_cost]
    rfl

/-! ## The sentinel-stream loop: invariant + step + run -/

/-- The sentinel-loop fold invariant (shared by the cards and final loops via
the item view). -/
def SInv (its : List (Option Nat)) (k : Nat) (b0 : Bool) (u : State) (i : Nat)
    (st : State) : Prop :=
  State.get st SCAN = encItems (its.drop i)
  ∧ State.get st BOUT = expandItems k (its.take i)
  ∧ State.get st FLAG = cond (b0 && itemsOkB k (its.take i)) [1] [0]
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ BOUT → r ≠ VALX → r ≠ REM → r ≠ TFLG →
      r ≠ FLAG → r ≠ IDX2 → r ≠ IDXR → r ≠ IDXO → r ≠ CliqueRelTM.HEAD →
      r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
      State.get st r = State.get u r)

/-- One `sentStep` iteration preserves `SInv`, within the uniform budget. -/
theorem sentStep_step (its : List (Option Nat)) (k : Nat) (b0 : Bool)
    (u : State) (S : Nat) (hS : (encItems its).length ≤ S)
    (hSIG : State.get u SIGMA = List.replicate k 1)
    (i : Nat) (st : State) (h : SInv its k b0 u i st) :
    SInv its k b0 u (i + 1) (sentStep.eval (st.set IDXO (List.replicate i 1)))
    ∧ sentStep.cost (st.set IDXO (List.replicate i 1)) ≤ sentStepBound S k := by
  obtain ⟨hSCAN, hBOUT, hFLG, hframe⟩ := h
  set w := st.set IDXO (List.replicate i 1) with hw
  have hwframe : ∀ r : Var, r ≠ IDXO → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSIG : State.get w SIGMA = List.replicate k 1 := by
    rw [hwframe SIGMA (by decide), hframe SIGMA (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hSIG]
  have hSw : (State.get w SCAN).length ≤ S := by
    rw [hwframe SCAN (by decide), hSCAN]
    exact le_trans (encItems_drop_le its i) hS
  by_cases hi : i < its.length
  · have hdrop : its.drop i = its[i] :: its.drop (i + 1) :=
      List.drop_eq_getElem_cons hi
    have htake : its.take (i + 1) = its.take i ++ [its[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
    have hSCw : State.get w SCAN
        = encItem its[i] ++ encItems (its.drop (i + 1)) := by
      rw [hwframe SCAN (by decide), hSCAN, hdrop]
      rfl
    have hFLGw : State.get w FLAG
        = cond (b0 && itemsOkB k (its.take i)) [1] [0] := by
      rw [hwframe FLAG (by decide), hFLG]
    cases hit : its[i] with
    | some v =>
        rw [hit] at hSCw
        obtain ⟨hA, hB, hC, hF, hCost⟩ := sentStep_elem w v _ k
          (b0 && itemsOkB k (its.take i)) S hSCw hwSIG hFLGw hSw
        refine ⟨⟨?_, ?_, ?_, ?_⟩, hCost⟩
        · rw [hA]
        · rw [hB, hwframe BOUT (by decide), hBOUT, htake, expandItems_snoc,
            hit]
        · rw [hC, htake, itemsOkB_snoc, hit, Bool.and_assoc]
          rfl
        · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
          rw [hF r h1 h2 h3 h4 h5 h6 h7 h8 h10 h11 h12, hwframe r h9,
            hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12]
    | none =>
        rw [hit] at hSCw
        obtain ⟨hA, hB, hC, hF, hCost⟩ := sentStep_term w _ S hSCw hSw
        have hbudget : S + 12 ≤ sentStepBound S k := by
          unfold sentStepBound
          omega
        refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega⟩
        · rw [hA]
        · rw [hB, hwframe BOUT (by decide), hBOUT, htake, expandItems_snoc,
            hit]
          rfl
        · rw [hC, hwframe FLAG (by decide), hFLG, htake, itemsOkB_snoc, hit,
            show itemOkB k none = true from rfl, Bool.and_true]
        · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
          rw [hF r h1 h2 h5, hwframe r h9,
            hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12]
  · have hlen : its.length ≤ i := Nat.le_of_not_lt hi
    have hSCw : State.get w SCAN = [] := by
      rw [hwframe SCAN (by decide), hSCAN, List.drop_eq_nil_of_le hlen]
      rfl
    obtain ⟨heval, hcost⟩ := sentStep_idle w hSCw
    have hbudget : (6 : Nat) ≤ sentStepBound S k := by
      unfold sentStepBound; omega
    refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega⟩
    · rw [heval, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hwframe SCAN (by decide), hSCAN,
        List.drop_eq_nil_of_le hlen, List.drop_eq_nil_of_le (by omega)]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hwframe BOUT (by decide), hBOUT,
        List.take_of_length_le hlen, List.take_of_length_le (by omega)]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hwframe FLAG (by decide), hFLG,
        List.take_of_length_le hlen, List.take_of_length_le (by omega)]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      rw [heval, State.get_set_ne _ _ _ _ h12, State.get_set_ne _ _ _ _ h5,
        hwframe r h9, hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12]

/-- **The sentinel-stream loop is correct** (instantiated twice: cards and
final). -/
theorem sentLoop_run (its : List (Option Nat)) (k : Nat) (b0 : Bool)
    (u : State) (bnd : Var) (S : Nat)
    (hSlen : (State.get u bnd).length = S)
    (hS : (encItems its).length ≤ S)
    (hSC : State.get u SCAN = encItems its)
    (hSIG : State.get u SIGMA = List.replicate k 1)
    (hFLAG : State.get u FLAG = cond b0 [1] [0])
    (hBOUT : State.get u BOUT = []) :
    State.get ((Cmd.forBnd IDXO bnd sentStep).eval u) BOUT
        = expandItems k its
    ∧ State.get ((Cmd.forBnd IDXO bnd sentStep).eval u) FLAG
        = cond (b0 && itemsOkB k its) [1] [0]
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ BOUT → r ≠ VALX → r ≠ REM → r ≠ TFLG →
        r ≠ FLAG → r ≠ IDX2 → r ≠ IDXR → r ≠ IDXO → r ≠ CliqueRelTM.HEAD →
        r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
        State.get ((Cmd.forBnd IDXO bnd sentStep).eval u) r = State.get u r)
    ∧ (Cmd.forBnd IDXO bnd sentStep).cost u
        ≤ 1 + S * sentStepBound S k + S * S := by
  have hitslen : its.length ≤ S := le_trans (encItems_length its) hS
  have hbase : SInv its k b0 u 0 u := by
    refine ⟨by rw [List.drop_zero]; exact hSC,
      by rw [List.take_zero]; exact hBOUT, ?_,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    rw [List.take_zero]
    show State.get u FLAG = cond (b0 && itemsOkB k []) [1] [0]
    rw [show itemsOkB k [] = true from rfl, Bool.and_true]
    exact hFLAG
  have hInv : SInv its k b0 u S
      (Cmd.foldlState sentStep IDXO (List.range S) u) :=
    Cmd.foldlState_range_induct sentStep IDXO S u (SInv its k b0 u) hbase
      (fun i st _ hM => (sentStep_step its k b0 u S hS hSIG i st hM).1)
  obtain ⟨-, hBOUT', hFLG, hframe⟩ := hInv
  have heval : (Cmd.forBnd IDXO bnd sentStep).eval u
      = Cmd.foldlState sentStep IDXO (List.range S) u := by
    rw [Cmd.eval_forBnd, hSlen]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval, hBOUT', List.take_of_length_le hitslen]
  · rw [heval, hFLG, List.take_of_length_le hitslen]
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    rw [heval]
    exact hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  · have h := Cmd.cost_forBnd_le IDXO bnd sentStep u (sentStepBound S k)
      (SInv its k b0 u) hbase
      (fun i st hi hM => (sentStep_step its k b0 u S hS hSIG i st hM).1)
      (fun i st hi hM => (sentStep_step its k b0 u S hS hSIG i st hM).2)
    rw [hSlen] at h
    exact h

/-! ## The unary-multiplication loop: run + cost -/

/-- **The unary product loop is correct**: `forBnd IDXO bnd (concat dst dst
SIGMA)` on `dst = []`, `SIGMA = 1^k`, `|bnd| = m` leaves `dst = 1^(m·k)`. -/
theorem mulLoop_run (dst bnd : Var) (s : State) (k m : Nat)
    (hSIG : State.get s SIGMA = List.replicate k 1)
    (hbnd : State.get s bnd = List.replicate m 1)
    (hdst : State.get s dst = [])
    (hd1 : dst ≠ SIGMA) (hd2 : dst ≠ IDXO) :
    State.get ((Cmd.forBnd IDXO bnd (Cmd.op (.concat dst dst SIGMA))).eval s)
        dst = List.replicate (m * k) 1
    ∧ (∀ r : Var, r ≠ dst → r ≠ IDXO →
        State.get ((Cmd.forBnd IDXO bnd (Cmd.op (.concat dst dst SIGMA))).eval s)
          r = State.get s r)
    ∧ (Cmd.forBnd IDXO bnd (Cmd.op (.concat dst dst SIGMA))).cost s
        ≤ 1 + m * (2 * (m * k + k) + 1) + m * m := by
  have hlen : (State.get s bnd).length = m := by
    rw [hbnd, List.length_replicate]
  have hstep : ∀ i st, i < m →
      (State.get st dst = List.replicate (i * k) 1
        ∧ ∀ r : Var, r ≠ dst → r ≠ IDXO → State.get st r = State.get s r) →
      (State.get ((Cmd.op (.concat dst dst SIGMA)).eval
            (st.set IDXO (List.replicate i 1))) dst
          = List.replicate ((i + 1) * k) 1
        ∧ ∀ r : Var, r ≠ dst → r ≠ IDXO →
            State.get ((Cmd.op (.concat dst dst SIGMA)).eval
              (st.set IDXO (List.replicate i 1))) r = State.get s r) := by
    intro i st _ ⟨hD, hF⟩
    set w := st.set IDXO (List.replicate i 1) with hw
    have hwD : State.get w dst = List.replicate (i * k) 1 := by
      rw [hw, State.get_set_ne _ _ _ _ hd2, hD]
    have hwSIG : State.get w SIGMA = List.replicate k 1 := by
      rw [hw, State.get_set_ne _ _ _ _ (by decide), hF SIGMA (Ne.symm hd1)
        (by decide), hSIG]
    have he : (Cmd.op (.concat dst dst SIGMA)).eval w
        = w.set dst (List.replicate (i * k) 1 ++ List.replicate k 1) := by
      rw [Cmd.eval_op]; simp only [Op.eval, hwD, hwSIG]
    constructor
    · rw [he, State.get_set_eq, ← List.replicate_add]
      congr 1
      ring
    · intro r h1 h2
      rw [he, State.get_set_ne _ _ _ _ h1, hw, State.get_set_ne _ _ _ _ h2]
      exact hF r h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [Cmd.eval_forBnd, hlen]
    have := (Cmd.foldlState_range_induct _ IDXO m s
      (fun i st => State.get st dst = List.replicate (i * k) 1
        ∧ ∀ r : Var, r ≠ dst → r ≠ IDXO → State.get st r = State.get s r)
      ⟨by simpa using hdst, fun r _ _ => rfl⟩ hstep).1
    exact this
  · intro r h1 h2
    rw [Cmd.eval_forBnd, hlen]
    exact (Cmd.foldlState_range_induct _ IDXO m s
      (fun i st => State.get st dst = List.replicate (i * k) 1
        ∧ ∀ r : Var, r ≠ dst → r ≠ IDXO → State.get st r = State.get s r)
      ⟨by simpa using hdst, fun r _ _ => rfl⟩ hstep).2 r h1 h2
  · have h := Cmd.cost_forBnd_le IDXO bnd (Cmd.op (.concat dst dst SIGMA)) s
      (2 * (m * k + k) + 1)
      (fun i st => State.get st dst = List.replicate (i * k) 1
        ∧ ∀ r : Var, r ≠ dst → r ≠ IDXO → State.get st r = State.get s r)
      ⟨by simpa using hdst, fun r _ _ => rfl⟩
      (fun i st hi hM => hstep i st (by omega) hM)
      (fun i st hi hM => by
        rw [Cmd.cost_op]
        show 2 * ((State.get (st.set IDXO (List.replicate i 1)) dst).length
            + (State.get (st.set IDXO (List.replicate i 1)) SIGMA).length) + 1 ≤ _
        rw [State.get_set_ne _ _ _ _ hd2, hM.1,
          State.get_set_ne _ _ _ _ (by decide), hM.2 SIGMA (Ne.symm hd1)
            (by decide), hSIG, List.length_replicate, List.length_replicate]
        have hik : i * k ≤ m * k := by
          have : i ≤ m := by omega
          exact Nat.mul_le_mul_right k this
        omega)
    rw [hlen] at h
    exact h

/-! ## The whole program: run + cost -/

/-- Budget for one `binConvert` run, in `Sigma`/`offset`/`width` and the three
input-stream lengths. -/
def binBudget (K O W LI LC LF : Nat) : Nat :=
  (1 + O * (2 * (O * K + K) + 1) + O * O)
  + (1 + W * (2 * (W * K + K) + 1) + W * W)
  + (1 + LI * initStepBound LI K + LI * LI)
  + (1 + LC * sentStepBound LC K + LC * LC)
  + (1 + LF * sentStepBound LF K + LF * LF)
  + (LI + LC + LF)
  + 3 * (K * LC + LC) + 3 * (K * LF + LF)
  + 60

/-- The budget arithmetic, in a clean context (`omega` whnf-times-out when run
inside `binConvert_run`'s large state-tracking context). -/
private theorem binBudget_arith
    (L1 L2 L3 P1 P2 P3 P4 P5 Q1 Q2 Q3 Q4 Q5 R1 R2 A1 A2 A3 A4 A5 A6 BC BF : Nat)
    (h1 : A1 ≤ 1 + P1 + Q1) (h2 : A2 ≤ 1 + P2 + Q2)
    (h3 : A3 ≤ 1 + P3 + Q3) (h4 : A4 ≤ 1 + P4 + Q4) (h5 : A5 ≤ 1 + P5 + Q5)
    (h6 : A6 ≤ 12) (h7 : BC ≤ R1) (h8 : BF ≤ R2) :
    1 + 1 + (1 + 1 + (1 + 1 + (1 + A1 + (1 + 1 + (1 + A2 + (1 + 1 + (1 + (L1 + 1) + (1 + A3 + (1 + 1 + (1 + (L2 + 1) + (1 + A4 + (1 + (BC + 1) + (1 + 1 + (1 + (L3 + 1) + (1 + A5 + (1 + (BF + 1) + A6))))))))))))))))
      ≤ (1 + P1 + Q1) + (1 + P2 + Q2) + (1 + P3 + Q3) + (1 + P4 + Q4)
        + (1 + P5 + Q5) + (L1 + L2 + L3) + R1 + R2 + 60 := by
  linarith

/-- **`binConvert` computes the guarded conversion.** On any state carrying the
FlatCC input layout it writes the BinaryCC layout of the mapped instance to
the output registers when every symbol is `< Sigma`, and the all-empty
no-instance layout otherwise; the shared input registers `0–8` (except
`STEPS` in the invalid case) are untouched. -/
theorem binConvert_run (k o w : Nat) (xs : List Nat) (cs : List (CCCard Nat))
    (fss : List (List Nat)) (s0 : State)
    (hSIG : State.get s0 SIGMA = List.replicate k 1)
    (hINIT : State.get s0 INIT = encNats xs)
    (hFINAL : State.get s0 FINAL = encFinal fss)
    (hOFF : State.get s0 OFFSET = List.replicate o 1)
    (hWID : State.get s0 WIDTH = List.replicate w 1)
    (hCARDS : State.get s0 CARDS = encCardsOut cs) :
    State.get (binConvert.eval s0) BOFF
        = cond (okB k xs cs fss) (List.replicate (o * k) 1) []
    ∧ State.get (binConvert.eval s0) BWID
        = cond (okB k xs cs fss) (List.replicate (w * k) 1) []
    ∧ State.get (binConvert.eval s0) BINIT
        = cond (okB k xs cs fss) (expandStr k xs) []
    ∧ State.get (binConvert.eval s0) BCARDS
        = cond (okB k xs cs fss) (encCardsOut (cs.map (expandCard k))) []
    ∧ State.get (binConvert.eval s0) BFINAL
        = cond (okB k xs cs fss) (encFinal (fss.map (expandStr k))) []
    ∧ State.get (binConvert.eval s0) STEPS
        = cond (okB k xs cs fss) (State.get s0 STEPS) []
    ∧ (∀ r : Var, r < 9 → r ≠ STEPS →
        State.get (binConvert.eval s0) r = State.get s0 r)
    ∧ binConvert.cost s0
        ≤ binBudget k o w (encNats xs).length (encCardsOut cs).length
            (encFinal fss).length := by
  set LI := (encNats xs).length with hLI
  set LC := (encCardsOut cs).length with hLC
  set LF := (encFinal fss).length with hLF
  -- stage 1–2: FLAG := [1]
  have e1 : (Cmd.op (.clear FLAG)).eval s0 = s0.set FLAG [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u1 := s0.set FLAG [] with hu1
  have hu1FLAG : State.get u1 FLAG = [] := State.get_set_eq _ _ _
  have e2 : (Cmd.op (.appendOne FLAG)).eval u1 = u1.set FLAG [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hu1FLAG, List.nil_append]
  set u2 := u1.set FLAG [1] with hu2
  have hu2get : ∀ r : Var, r ≠ FLAG → State.get u2 r = State.get s0 r := by
    intro r hr
    rw [hu2, State.get_set_ne _ _ _ _ hr, hu1, State.get_set_ne _ _ _ _ hr]
  -- stage 3–4: BOFF := offset · Sigma
  have e3 : (Cmd.op (.clear BOFF)).eval u2 = u2.set BOFF [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u3 := u2.set BOFF [] with hu3
  have hu3get : ∀ r : Var, r ≠ FLAG → r ≠ BOFF →
      State.get u3 r = State.get s0 r := by
    intro r h1 h2
    rw [hu3, State.get_set_ne _ _ _ _ h2, hu2get r h1]
  obtain ⟨hB4, hF4, hC4⟩ := mulLoop_run BOFF OFFSET u3 k o
    (by rw [hu3get SIGMA (by decide) (by decide)]; exact hSIG)
    (by rw [hu3get OFFSET (by decide) (by decide)]; exact hOFF)
    (by rw [hu3]; exact State.get_set_eq _ _ _) (by decide) (by decide)
  set u4 := (Cmd.forBnd IDXO OFFSET (Cmd.op (.concat BOFF BOFF SIGMA))).eval u3
    with hu4
  have hu4get : ∀ r : Var, r ≠ FLAG → r ≠ BOFF → r ≠ IDXO →
      State.get u4 r = State.get s0 r := by
    intro r h1 h2 h3
    rw [hF4 r h2 h3, hu3get r h1 h2]
  -- stage 5–6: BWID := width · Sigma
  have e5 : (Cmd.op (.clear BWID)).eval u4 = u4.set BWID [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u5 := u4.set BWID [] with hu5
  have hu5get : ∀ r : Var, r ≠ FLAG → r ≠ BOFF → r ≠ IDXO → r ≠ BWID →
      State.get u5 r = State.get s0 r := by
    intro r h1 h2 h3 h4
    rw [hu5, State.get_set_ne _ _ _ _ h4, hu4get r h1 h2 h3]
  obtain ⟨hB6, hF6, hC6⟩ := mulLoop_run BWID WIDTH u5 k w
    (by rw [hu5get SIGMA (by decide) (by decide) (by decide) (by decide)]
        exact hSIG)
    (by rw [hu5get WIDTH (by decide) (by decide) (by decide) (by decide)]
        exact hWID)
    (by rw [hu5]; exact State.get_set_eq _ _ _) (by decide) (by decide)
  set u6 := (Cmd.forBnd IDXO WIDTH (Cmd.op (.concat BWID BWID SIGMA))).eval u5
    with hu6
  have hu6get : ∀ r : Var, r ≠ FLAG → r ≠ BOFF → r ≠ IDXO → r ≠ BWID →
      State.get u6 r = State.get s0 r := by
    intro r h1 h2 h3 h4
    rw [hF6 r h4 h3, hu5get r h1 h2 h3 h4]
  have hu6BOFF : State.get u6 BOFF = List.replicate (o * k) 1 := by
    rw [hF6 BOFF (by decide) (by decide), hu5,
      State.get_set_ne _ _ _ _ (by decide), hB4]
  -- stage 7–9: BINIT := expandStr, FLAG &&= allLtB
  have e7 : (Cmd.op (.clear BINIT)).eval u6 = u6.set BINIT [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u7 := u6.set BINIT [] with hu7
  have hu7INIT : State.get u7 INIT = encNats xs := by
    rw [hu7, State.get_set_ne _ _ _ _ (by decide),
      hu6get INIT (by decide) (by decide) (by decide) (by decide), hINIT]
  have e8 : (Cmd.op (.copy SCAN INIT)).eval u7 = u7.set SCAN (encNats xs) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hu7INIT]
  set u8 := u7.set SCAN (encNats xs) with hu8
  have hu8get : ∀ r : Var, r ≠ FLAG → r ≠ BOFF → r ≠ IDXO → r ≠ BWID →
      r ≠ BINIT → r ≠ SCAN → State.get u8 r = State.get s0 r := by
    intro r h1 h2 h3 h4 h5 h6
    rw [hu8, State.get_set_ne _ _ _ _ h6, hu7, State.get_set_ne _ _ _ _ h5,
      hu6get r h1 h2 h3 h4]
  have hu8INIT : State.get u8 INIT = encNats xs := by
    rw [hu8get INIT (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hINIT]
  have hu8SIG : State.get u8 SIGMA = List.replicate k 1 := by
    rw [hu8get SIGMA (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hSIG]
  have hu8FLAG : State.get u8 FLAG = cond true [1] [0] := by
    rw [hu8, State.get_set_ne _ _ _ _ (by decide), hu7,
      State.get_set_ne _ _ _ _ (by decide), hF6 FLAG (by decide) (by decide),
      hu5, State.get_set_ne _ _ _ _ (by decide), hF4 FLAG (by decide)
      (by decide), hu3, State.get_set_ne _ _ _ _ (by decide), hu2]
    exact State.get_set_eq _ _ _
  have hu8SCAN : State.get u8 SCAN = encNats xs := by
    rw [hu8]; exact State.get_set_eq _ _ _
  have hu8BINIT : State.get u8 BINIT = [] := by
    rw [hu8, State.get_set_ne _ _ _ _ (by decide), hu7]
    exact State.get_set_eq _ _ _
  obtain ⟨hB9, hFL9, hF9, hC9⟩ := initLoop_run xs k true u8 INIT LI
    (by rw [hu8INIT]) (le_of_eq rfl) hu8SCAN hu8SIG hu8FLAG hu8BINIT
  rw [Bool.true_and] at hFL9
  set u9 := (Cmd.forBnd IDXO INIT initStep).eval u8 with hu9
  have hu9low : ∀ r : Var, r < 9 → State.get u9 r = State.get s0 r := by
    intro r hr
    have hge : ∀ m : Nat, 9 ≤ m → r ≠ m :=
      fun m hm => Nat.ne_of_lt (Nat.lt_of_lt_of_le hr hm)
    rw [hF9 r (hge 9 (by omega)) (hge 19 (by omega)) (hge 10 (by omega))
      (hge 14 (by omega)) (hge 23 (by omega)) (hge 11 (by omega))
      (hge 24 (by omega)) (hge 13 (by omega)) (hge 12 (by omega))
      (hge 15 (by omega)) (hge 16 (by omega)) (hge 26 (by omega)),
      hu8get r (hge 11 (by omega)) (hge 17 (by omega)) (hge 12 (by omega))
      (hge 18 (by omega)) (hge 19 (by omega)) (hge 9 (by omega))]
  have hu9BOFF : State.get u9 BOFF = List.replicate (o * k) 1 := by
    rw [hF9 BOFF (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hu8, State.get_set_ne _ _ _ _ (by decide), hu7,
      State.get_set_ne _ _ _ _ (by decide), hu6BOFF]
  have hu9BWID : State.get u9 BWID = List.replicate (w * k) 1 := by
    rw [hF9 BWID (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hu8, State.get_set_ne _ _ _ _ (by decide), hu7,
      State.get_set_ne _ _ _ _ (by decide), hB6]
  -- stage 10–13: BCARDS := expanded card stream, FLAG &&= cards ok
  have e10 : (Cmd.op (.clear BOUT)).eval u9 = u9.set BOUT [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u10 := u9.set BOUT [] with hu10
  have hu10CARDS : State.get u10 CARDS = encCardsOut cs := by
    rw [hu10, State.get_set_ne _ _ _ _ (by decide), hu9low CARDS (by decide),
      hCARDS]
  have e11 : (Cmd.op (.copy SCAN CARDS)).eval u10
      = u10.set SCAN (encCardsOut cs) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hu10CARDS]
  set u11 := u10.set SCAN (encCardsOut cs) with hu11
  have hu11get : ∀ r : Var, r ≠ BOUT → r ≠ SCAN →
      State.get u11 r = State.get u9 r := by
    intro r h1 h2
    rw [hu11, State.get_set_ne _ _ _ _ h2, hu10, State.get_set_ne _ _ _ _ h1]
  have hu11CARDS : State.get u11 CARDS = encCardsOut cs := by
    rw [hu11get CARDS (by decide) (by decide), hu9low CARDS (by decide), hCARDS]
  have hu11SIG : State.get u11 SIGMA = List.replicate k 1 := by
    rw [hu11get SIGMA (by decide) (by decide), hu9low SIGMA (by decide), hSIG]
  have hu11FLAG : State.get u11 FLAG = cond (allLtB k xs) [1] [0] := by
    rw [hu11get FLAG (by decide) (by decide), hFL9]
  have hu11SCAN : State.get u11 SCAN = encItems (citemsOf cs) := by
    rw [hu11, State.get_set_eq, encItems_citemsOf]
  have hu11BOUT : State.get u11 BOUT = [] := by
    rw [hu11, State.get_set_ne _ _ _ _ (by decide), hu10]
    exact State.get_set_eq _ _ _
  obtain ⟨hB12, hFL12, hF12, hC12⟩ := sentLoop_run (citemsOf cs) k
    (allLtB k xs) u11 CARDS LC (by rw [hu11CARDS])
    (le_of_eq (by rw [encItems_citemsOf])) hu11SCAN hu11SIG hu11FLAG hu11BOUT
  set u12 := (Cmd.forBnd IDXO CARDS sentStep).eval u11 with hu12
  have hu12BOUT : State.get u12 BOUT = expandItems k (citemsOf cs) := hB12
  have e13 : (Cmd.op (.copy BCARDS BOUT)).eval u12
      = u12.set BCARDS (expandItems k (citemsOf cs)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hu12BOUT]
  set u13 := u12.set BCARDS (expandItems k (citemsOf cs)) with hu13
  have hu13get : ∀ r : Var, r ≠ SCAN → r ≠ BOUT → r ≠ BCARDS → r ≠ VALX →
      r ≠ REM → r ≠ TFLG → r ≠ FLAG → r ≠ IDX2 → r ≠ IDXR → r ≠ IDXO →
      r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
      State.get u13 r = State.get u9 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    rw [hu13, State.get_set_ne _ _ _ _ h3,
      hF12 r h1 h2 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13, hu11get r h2 h1]
  -- stage 14–17: BFINAL := expanded final stream, FLAG &&= final ok
  have e14 : (Cmd.op (.clear BOUT)).eval u13 = u13.set BOUT [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u14 := u13.set BOUT [] with hu14
  have hu14FINAL : State.get u14 FINAL = encFinal fss := by
    rw [hu14, State.get_set_ne _ _ _ _ (by decide), hu13get FINAL (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hu9low FINAL (by decide), hFINAL]
  have e15 : (Cmd.op (.copy SCAN FINAL)).eval u14
      = u14.set SCAN (encFinal fss) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hu14FINAL]
  set u15 := u14.set SCAN (encFinal fss) with hu15
  have hu15get : ∀ r : Var, r ≠ BOUT → r ≠ SCAN →
      State.get u15 r = State.get u13 r := by
    intro r h1 h2
    rw [hu15, State.get_set_ne _ _ _ _ h2, hu14, State.get_set_ne _ _ _ _ h1]
  have hu15FINAL : State.get u15 FINAL = encFinal fss := by
    rw [hu15get FINAL (by decide) (by decide), hu13get FINAL (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hu9low FINAL (by decide), hFINAL]
  have hu15SIG : State.get u15 SIGMA = List.replicate k 1 := by
    rw [hu15get SIGMA (by decide) (by decide), hu13get SIGMA (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hu9low SIGMA (by decide), hSIG]
  have hu15FLAG : State.get u15 FLAG
      = cond (allLtB k xs && itemsOkB k (citemsOf cs)) [1] [0] := by
    rw [hu15get FLAG (by decide) (by decide), hu13,
      State.get_set_ne _ _ _ _ (by decide), hFL12]
  have hu15SCAN : State.get u15 SCAN = encItems (fitemsOf fss) := by
    rw [hu15, State.get_set_eq, encItems_fitemsOf]
  have hu15BOUT : State.get u15 BOUT = [] := by
    rw [hu15, State.get_set_ne _ _ _ _ (by decide), hu14]
    exact State.get_set_eq _ _ _
  obtain ⟨hB16, hFL16, hF16, hC16⟩ := sentLoop_run (fitemsOf fss) k
    (allLtB k xs && itemsOkB k (citemsOf cs)) u15 FINAL LF
    (by rw [hu15FINAL])
    (le_of_eq (by rw [encItems_fitemsOf])) hu15SCAN hu15SIG hu15FLAG hu15BOUT
  set u16 := (Cmd.forBnd IDXO FINAL sentStep).eval u15 with hu16
  have hu16BOUT : State.get u16 BOUT = expandItems k (fitemsOf fss) := hB16
  have e17 : (Cmd.op (.copy BFINAL BOUT)).eval u16
      = u16.set BFINAL (expandItems k (fitemsOf fss)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hu16BOUT]
  set u17 := u16.set BFINAL (expandItems k (fitemsOf fss)) with hu17
  -- the state before the guard: all registers accounted for
  have hu17get : ∀ r : Var, r ≠ SCAN → r ≠ BOUT → r ≠ BCARDS → r ≠ BFINAL →
      r ≠ VALX → r ≠ REM → r ≠ TFLG → r ≠ FLAG → r ≠ IDX2 → r ≠ IDXR →
      r ≠ IDXO → r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.INBLK →
      r ≠ CliqueRelTM.SKIPR → State.get u17 r = State.get u9 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    rw [hu17, State.get_set_ne _ _ _ _ h4,
      hF16 r h1 h2 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14, hu15get r h2 h1,
      hu13get r h1 h2 h3 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14]
  have hu17low : ∀ r : Var, r < 9 → State.get u17 r = State.get s0 r := by
    intro r hr
    have hge : ∀ m : Nat, 9 ≤ m → r ≠ m :=
      fun m hm => Nat.ne_of_lt (Nat.lt_of_lt_of_le hr hm)
    rw [hu17get r (hge 9 (by omega)) (hge 25 (by omega)) (hge 20 (by omega))
      (hge 21 (by omega)) (hge 10 (by omega)) (hge 14 (by omega))
      (hge 23 (by omega)) (hge 11 (by omega)) (hge 24 (by omega))
      (hge 13 (by omega)) (hge 12 (by omega)) (hge 15 (by omega))
      (hge 16 (by omega)) (hge 26 (by omega)), hu9low r hr]
  have hu17BOFF : State.get u17 BOFF = List.replicate (o * k) 1 := by
    rw [hu17get BOFF (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hu9BOFF]
  have hu17BWID : State.get u17 BWID = List.replicate (w * k) 1 := by
    rw [hu17get BWID (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hu9BWID]
  have hu17BINIT : State.get u17 BINIT = expandStr k xs := by
    rw [hu17get BINIT (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hB9]
  have hu17BCARDS : State.get u17 BCARDS = expandItems k (citemsOf cs) := by
    rw [hu17, State.get_set_ne _ _ _ _ (by decide), hF16 BCARDS (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
      hu15get BCARDS (by decide) (by decide), hu13]
    exact State.get_set_eq _ _ _
  have hu17BFINAL : State.get u17 BFINAL = expandItems k (fitemsOf fss) := by
    rw [hu17]; exact State.get_set_eq _ _ _
  have hu17FLAG : State.get u17 FLAG = cond (okB k xs cs fss) [1] [0] := by
    rw [hu17, State.get_set_ne _ _ _ _ (by decide), hFL16, Bool.and_assoc,
      ← Bool.and_assoc, itemsOkB_citemsOf, itemsOkB_fitemsOf]
    rfl
  have hu17STEPS : State.get u17 STEPS = State.get s0 STEPS :=
    hu17low STEPS (by decide)
  -- assemble the eval chain up to the guard
  have hevalPre : ∀ tail : Cmd,
      ((Cmd.op (.clear FLAG)) ;; (Cmd.op (.appendOne FLAG)) ;;
        (Cmd.op (.clear BOFF)) ;;
        (Cmd.forBnd IDXO OFFSET (Cmd.op (.concat BOFF BOFF SIGMA))) ;;
        (Cmd.op (.clear BWID)) ;;
        (Cmd.forBnd IDXO WIDTH (Cmd.op (.concat BWID BWID SIGMA))) ;;
        (Cmd.op (.clear BINIT)) ;; (Cmd.op (.copy SCAN INIT)) ;;
        (Cmd.forBnd IDXO INIT initStep) ;;
        (Cmd.op (.clear BOUT)) ;; (Cmd.op (.copy SCAN CARDS)) ;;
        (Cmd.forBnd IDXO CARDS sentStep) ;;
        (Cmd.op (.copy BCARDS BOUT)) ;;
        (Cmd.op (.clear BOUT)) ;; (Cmd.op (.copy SCAN FINAL)) ;;
        (Cmd.forBnd IDXO FINAL sentStep) ;;
        (Cmd.op (.copy BFINAL BOUT)) ;; tail).eval s0 = tail.eval u17 := by
    intro tail
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq,
      ← hu4, Cmd.eval_seq, e5, Cmd.eval_seq, ← hu6, Cmd.eval_seq, e7,
      Cmd.eval_seq, e8, Cmd.eval_seq, ← hu9, Cmd.eval_seq, e10, Cmd.eval_seq,
      e11, Cmd.eval_seq, ← hu12, Cmd.eval_seq, e13, Cmd.eval_seq, e14,
      Cmd.eval_seq, e15, Cmd.eval_seq, ← hu16, Cmd.eval_seq, e17]
  -- the cost bound (independent of the guard's verdict)
  have hlenBC : (expandItems k (citemsOf cs)).length ≤ 3 * (k * LC + LC) := by
    have h := expandItems_length_le k (citemsOf cs)
    have h2 : (citemsOf cs).length ≤ LC := by
      rw [hLC, ← encItems_citemsOf]
      exact encItems_length _
    have h3 : k * (citemsOf cs).length ≤ k * LC := Nat.mul_le_mul_left k h2
    have h4 : (encItems (citemsOf cs)).length = LC := by
      rw [encItems_citemsOf]
    omega
  have hlenBF : (expandItems k (fitemsOf fss)).length ≤ 3 * (k * LF + LF) := by
    have h := expandItems_length_le k (fitemsOf fss)
    have h2 : (fitemsOf fss).length ≤ LF := by
      rw [hLF, ← encItems_fitemsOf]
      exact encItems_length _
    have h3 : k * (fitemsOf fss).length ≤ k * LF := Nat.mul_le_mul_left k h2
    have h4 : (encItems (fitemsOf fss)).length = LF := by
      rw [encItems_fitemsOf]
    omega
  set A6 := (Cmd.ifBit FLAG CliqueRelTM.cSkip
      (Cmd.op (.clear BOFF) ;; Cmd.op (.clear BWID) ;; Cmd.op (.clear BINIT) ;;
       Cmd.op (.clear BCARDS) ;; Cmd.op (.clear BFINAL) ;;
       Cmd.op (.clear STEPS))).cost u17 with hA6
  have hGuard : A6 ≤ 12 := by
    rw [hA6]
    by_cases hf : State.get u17 FLAG = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ hf, CliqueRelTM.cSkip_cost]
      omega
    · rw [Cmd.cost_ifBit_false _ _ _ _ hf]
      have : (Cmd.op (.clear BOFF) ;; Cmd.op (.clear BWID) ;;
          Cmd.op (.clear BINIT) ;; Cmd.op (.clear BCARDS) ;;
          Cmd.op (.clear BFINAL) ;; Cmd.op (.clear STEPS)).cost u17 = 11 := by
        simp only [Cmd.cost_seq, Cmd.cost_op, Op.cost]
      omega
  have hcost : binConvert.cost s0
      ≤ binBudget k o w LI LC LF := by
    -- fold the five loop costs and the two copy lengths into opaque atoms
    -- (`omega` whnf-times-out on the underlying state terms otherwise)
    set A1 := (Cmd.forBnd IDXO OFFSET
      (Cmd.op (.concat BOFF BOFF SIGMA))).cost u3 with hA1
    set A2 := (Cmd.forBnd IDXO WIDTH
      (Cmd.op (.concat BWID BWID SIGMA))).cost u5 with hA2
    set A3 := (Cmd.forBnd IDXO INIT initStep).cost u8 with hA3
    set A4 := (Cmd.forBnd IDXO CARDS sentStep).cost u11 with hA4
    set A5 := (Cmd.forBnd IDXO FINAL sentStep).cost u15 with hA5
    set BC := (expandItems k (citemsOf cs)).length with hBC
    set BF := (expandItems k (fitemsOf fss)).length with hBF
    show ((Cmd.op (.clear FLAG)) ;; _).cost s0 ≤ _
    rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, Cmd.cost_op, e2,
      Cmd.cost_seq, Cmd.cost_op, e3, Cmd.cost_seq, ← hu4, Cmd.cost_seq,
      Cmd.cost_op, e5, Cmd.cost_seq, ← hu6, Cmd.cost_seq, Cmd.cost_op, e7,
      Cmd.cost_seq, Cmd.cost_op, e8, Cmd.cost_seq, ← hu9, Cmd.cost_seq,
      Cmd.cost_op, e10, Cmd.cost_seq, Cmd.cost_op, e11, Cmd.cost_seq, ← hu12,
      Cmd.cost_seq, Cmd.cost_op, e13, Cmd.cost_seq, Cmd.cost_op, e14,
      Cmd.cost_seq, Cmd.cost_op, e15, Cmd.cost_seq, ← hu16, Cmd.cost_seq,
      Cmd.cost_op, e17, ← hA1, ← hA2, ← hA3, ← hA4, ← hA5, ← hA6]
    simp only [Op.cost, hu7INIT, hu10CARDS, hu12BOUT, hu14FINAL, hu16BOUT,
      ← hBC, ← hBF]
    unfold binBudget
    clear_value A1 A2 A3 A4 A5 A6 BC BF
    clear hA1 hA2 hA3 hA4 hA5 hA6 hBC hBF
    exact binBudget_arith LI LC LF
      (o * (2 * (o * k + k) + 1)) (w * (2 * (w * k + k) + 1))
      (LI * initStepBound LI k) (LC * sentStepBound LC k)
      (LF * sentStepBound LF k) (o * o) (w * w) (LI * LI) (LC * LC) (LF * LF)
      (3 * (k * LC + LC)) (3 * (k * LF + LF)) A1 A2 A3 A4 A5 A6 BC BF
      hC4 hC6 hC9 hC12 hC16 hGuard hlenBC hlenBF
  -- the guard, by validity
  cases hOK : okB k xs cs fss
  · -- invalid: the else branch clears the six output registers
    simp only [Bool.cond_false]
    have hFL : State.get u17 FLAG ≠ [1] := by
      rw [hu17FLAG, hOK]
      decide
    set z := (((((u17.set BOFF []).set BWID []).set BINIT []).set
        BCARDS []).set BFINAL []).set STEPS [] with hz
    have eG : (Cmd.ifBit FLAG CliqueRelTM.cSkip
        (Cmd.op (.clear BOFF) ;; Cmd.op (.clear BWID) ;; Cmd.op (.clear BINIT) ;;
         Cmd.op (.clear BCARDS) ;; Cmd.op (.clear BFINAL) ;;
         Cmd.op (.clear STEPS))).eval u17 = z := by
      rw [Cmd.eval_ifBit_false _ _ _ _ hFL]
      rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
        Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
        Cmd.eval_op]
      simp only [Op.eval]
      exact hz.symm
    have heval : binConvert.eval s0 = z := by
      show ((Cmd.op (.clear FLAG)) ;; _).eval s0 = z
      rw [hevalPre, eG]
    have hzlow : ∀ r : Var, r ≠ STEPS → r ≠ BOFF → r ≠ BWID → r ≠ BINIT →
        r ≠ BCARDS → r ≠ BFINAL → State.get z r = State.get u17 r := by
      intro r h1 h2 h3 h4 h5 h6
      rw [hz, State.get_set_ne _ _ _ _ h1, State.get_set_ne _ _ _ _ h6,
        State.get_set_ne _ _ _ _ h5, State.get_set_ne _ _ _ _ h4,
        State.get_set_ne _ _ _ _ h3, State.get_set_ne _ _ _ _ h2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hcost⟩
    · rw [heval, hz, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
    · rw [heval, hz, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
    · rw [heval, hz, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
    · rw [heval, hz, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
    · rw [heval, hz, State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
    · rw [heval, hz, State.get_set_eq]
    · intro r hr h5
      have hge : ∀ m : Nat, 9 ≤ m → r ≠ m :=
        fun m hm => Nat.ne_of_lt (Nat.lt_of_lt_of_le hr hm)
      rw [heval, hzlow r h5 (hge 17 (by omega)) (hge 18 (by omega))
        (hge 19 (by omega)) (hge 20 (by omega)) (hge 21 (by omega)),
        hu17low r hr]
  · -- valid: the guard is a `cSkip`
    simp only [Bool.cond_true]
    have hFL : State.get u17 FLAG = [1] := by
      rw [hu17FLAG, hOK]
      rfl
    have eG : (Cmd.ifBit FLAG CliqueRelTM.cSkip
        (Cmd.op (.clear BOFF) ;; Cmd.op (.clear BWID) ;; Cmd.op (.clear BINIT) ;;
         Cmd.op (.clear BCARDS) ;; Cmd.op (.clear BFINAL) ;;
         Cmd.op (.clear STEPS))).eval u17 = u17.set CliqueRelTM.SKIPR [1] := by
      rw [Cmd.eval_ifBit_true _ _ _ _ hFL, CliqueRelTM.cSkip_eval]
    have heval : binConvert.eval s0 = u17.set CliqueRelTM.SKIPR [1] := by
      show ((Cmd.op (.clear FLAG)) ;; _).eval s0 = _
      rw [hevalPre, eG]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hcost⟩
    · rw [heval, State.get_set_ne _ _ _ _ (by decide), hu17BOFF]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide), hu17BWID]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide), hu17BINIT]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide), hu17BCARDS,
        expandItems_citemsOf]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide), hu17BFINAL,
        expandItems_fitemsOf]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide), hu17STEPS]
    · intro r hr _
      have hge : ∀ m : Nat, 9 ≤ m → r ≠ m :=
        fun m hm => Nat.ne_of_lt (Nat.lt_of_lt_of_le hr hm)
      rw [heval,
        State.get_set_ne _ CliqueRelTM.SKIPR _ _ (hge 26 (by omega)),
        hu17low r hr]

/-! ## Structural fields (frame, `consLen`-freedom, op-supportedness) -/

theorem binConvert_usesBelow : Cmd.UsesBelow binConvert 27 := by
  simp [binConvert, initStep, sentStep, expandBare, expandSent, remCheck,
    setInvalid, CliqueRelTM.readNum, CliqueRelTM.cSkip, Cmd.UsesBelow,
    Op.UsesBelow, SIGMA, INIT, FINAL, STEPS, OFFSET, WIDTH, CARDS, SCAN,
    VALX, FLAG, IDXO, IDXR, REM, BOFF, BWID, BINIT, BCARDS, BFINAL, TFLG,
    IDX2, BOUT, CliqueRelTM.HEAD, CliqueRelTM.INBLK, CliqueRelTM.SKIPR]


/-! ## Size accounting for the input layout -/

theorem encCardsOut_length_le (cs : List (CCCard Nat)) :
    (encCardsOut cs).length ≤ 2 * encodable.size cs := by
  induction cs with
  | nil =>
      rw [show encCardsOut ([] : List (CCCard Nat)) = [] from rfl]
      simp
  | cons c cs ih =>
      have hp := list_length_le_size c.prem
      have hc := list_length_le_size c.conc
      have hcard : encodable.size c
          = encodable.size c.prem + encodable.size c.conc + 1 := rfl
      rw [show encCardsOut (c :: cs) = encCardOut c ++ encCardsOut cs from rfl,
        List.length_append, encodable_size_list_cons,
        show (encCardOut c).length
          = (encSList c.prem).length + (encSList c.conc).length from by
            rw [FlatTCCFree.encCardOut, List.length_append],
        encSList_length, encSList_length]
      omega

/-! ## Budget domination -/

/-- `binBudget` on inputs bounded by the instance size is dominated by one
cubic (clean-context arithmetic; `omega` hits a performance cliff here, so
the products are bounded stepwise and `linarith` closes). -/
private theorem binBudget_le_poly (n K O W LI LC LF : Nat)
    (hK : K ≤ n) (hO : O ≤ n) (hW : W ≤ n) (hLI : LI ≤ n)
    (hLC : LC ≤ 2 * n) (hLF : LF ≤ 2 * n) :
    binBudget K O W LI LC LF ≤ 4000 * (n + 1) ^ 3 := by
  have hOK : O * K ≤ n * n := Nat.mul_le_mul hO hK
  have hWK : W * K ≤ n * n := Nat.mul_le_mul hW hK
  have hOO : O * O ≤ n * n := Nat.mul_le_mul hO hO
  have hWW : W * W ≤ n * n := Nat.mul_le_mul hW hW
  have hO1 : O * (2 * (O * K + K) + 1) ≤ n * (2 * (n * n + n) + 1) :=
    Nat.mul_le_mul hO (by omega)
  have hW1 : W * (2 * (W * K + K) + 1) ≤ n * (2 * (n * n + n) + 1) :=
    Nat.mul_le_mul hW (by omega)
  have hOe : n * (2 * (n * n + n) + 1) = 2 * (n * n * n) + 2 * (n * n) + n := by
    ring
  have hLILI : LI * LI ≤ n * n := Nat.mul_le_mul hLI hLI
  have hLIK : LI * K ≤ n * n := Nat.mul_le_mul hLI hK
  have hKK : K * K ≤ n * n := Nat.mul_le_mul hK hK
  have hIB : initStepBound LI K ≤ 6 * (n * n) + 13 * n + 40 := by
    unfold initStepBound
    omega
  have hI1 : LI * initStepBound LI K ≤ n * (6 * (n * n) + 13 * n + 40) :=
    Nat.mul_le_mul hLI hIB
  have hIe : n * (6 * (n * n) + 13 * n + 40)
      = 6 * (n * n * n) + 13 * (n * n) + 40 * n := by ring
  have hLCLC : LC * LC ≤ 4 * (n * n) := by
    have := Nat.mul_le_mul hLC hLC
    have he : 2 * n * (2 * n) = 4 * (n * n) := by ring
    omega
  have hLCK : LC * K ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul hLC hK
    have he : 2 * n * n = 2 * (n * n) := by ring
    omega
  have hSBC : sentStepBound LC K ≤ 19 * (n * n) + 33 * n + 50 := by
    unfold sentStepBound
    omega
  have hC1 : LC * sentStepBound LC K ≤ 2 * n * (19 * (n * n) + 33 * n + 50) :=
    Nat.mul_le_mul hLC hSBC
  have hCe : 2 * n * (19 * (n * n) + 33 * n + 50)
      = 38 * (n * n * n) + 66 * (n * n) + 100 * n := by ring
  have hLFLF : LF * LF ≤ 4 * (n * n) := by
    have := Nat.mul_le_mul hLF hLF
    have he : 2 * n * (2 * n) = 4 * (n * n) := by ring
    omega
  have hLFK : LF * K ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul hLF hK
    have he : 2 * n * n = 2 * (n * n) := by ring
    omega
  have hSBF : sentStepBound LF K ≤ 19 * (n * n) + 33 * n + 50 := by
    unfold sentStepBound
    omega
  have hF1 : LF * sentStepBound LF K ≤ 2 * n * (19 * (n * n) + 33 * n + 50) :=
    Nat.mul_le_mul hLF hSBF
  have hKLC : K * LC ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul hK hLC
    have he : n * (2 * n) = 2 * (n * n) := by ring
    omega
  have hKLF : K * LF ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul hK hLF
    have he : n * (2 * n) = 2 * (n * n) := by ring
    omega
  have hpoly : 4000 * (n + 1) ^ 3
      = 4000 * (n * n * n) + 12000 * (n * n) + 12000 * n + 4000 := by ring
  have mid : binBudget K O W LI LC LF ≤
      (1 + n * (2 * (n * n + n) + 1) + n * n)
      + (1 + n * (2 * (n * n + n) + 1) + n * n)
      + (1 + n * (6 * (n * n) + 13 * n + 40) + n * n)
      + (1 + 2 * n * (19 * (n * n) + 33 * n + 50) + 4 * (n * n))
      + (1 + 2 * n * (19 * (n * n) + 33 * n + 50) + 4 * (n * n))
      + (n + 2 * n + 2 * n)
      + 3 * (2 * (n * n) + 2 * n) + 3 * (2 * (n * n) + 2 * n)
      + 60 := by
    unfold binBudget
    gcongr
  refine le_trans mid ?_
  have he : (1 + n * (2 * (n * n + n) + 1) + n * n)
      + (1 + n * (2 * (n * n + n) + 1) + n * n)
      + (1 + n * (6 * (n * n) + 13 * n + 40) + n * n)
      + (1 + 2 * n * (19 * (n * n) + 33 * n + 50) + 4 * (n * n))
      + (1 + 2 * n * (19 * (n * n) + 33 * n + 50) + 4 * (n * n))
      + (n + 2 * n + 2 * n)
      + 3 * (2 * (n * n) + 2 * n) + 3 * (2 * (n * n) + 2 * n)
      + 60 = 86 * (n * n * n) + 172 * (n * n) + 259 * n + 65 := by ring
  rw [he, hpoly]
  omega

/-! ## The free witness -/

private instance : Nonempty BinaryCC := ⟨binaryCCNoInstance⟩

/-- **The reduction `FlatCC_to_BinaryCC_instance` as a concrete layer
program** — the free `PolyTimeComputableLang` witness (template:
`flatTCC_reductionLang`). `decodeOut` inverts the injective 6-register output
key. -/
noncomputable def flatCCBin_reductionLang :
    PolyTimeComputableLang FlatCC_to_BinaryCC_instance where
  c := binConvert
  encodeIn := encodeIn
  decodeOut := fun s => Function.invFun encKeyB (extractKeyB s)
  cost_bound := fun n => 4000 * (n + 1) ^ 3
  cost_bound_poly := by
    refine ⟨3, ⟨32000, 1, ?_⟩⟩
    intro n hn
    calc 4000 * (n + 1) ^ 3
        ≤ 4000 * (2 * n) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      _ = 32000 * n ^ 3 := by ring
  cost_bound_mono := fun a b h =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 3)
  encBound := fun n => 2 * n + 1
  encBound_poly :=
    inOPoly_add (inOPoly_mul (inOPoly_const 2) inOPoly_id) (inOPoly_const 1)
  encBound_mono := fun a b h => Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1
  encodeIn_size := fun C => by
    have h1 := encCardsOut_length_le C.cards
    have h2 := encFinal_length_le C.final
    have hC : encodable.size C
        = C.Sigma + C.offset + C.width + encodable.size C.init
          + encodable.size C.cards + encodable.size C.final + C.steps + 1 := rfl
    show State.size [[], List.replicate C.Sigma 1, encNats C.init, [],
      encFinal C.final, List.replicate C.steps 1, List.replicate C.offset 1,
      List.replicate C.width 1, encCardsOut C.cards] ≤ _
    simp only [State.size, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil, List.length_replicate, List.length_nil, encNats_length]
    omega
  computes := fun C => by
    obtain ⟨hBOFF, hBWID, hBINIT, hBCARDS, hBFINAL, hSTEPS, -, -⟩ :=
      binConvert_run C.Sigma C.offset C.width C.init C.cards C.final
        (encodeIn C) rfl rfl rfl rfl rfl rfl
    show Function.invFun encKeyB (extractKeyB (binConvert.eval (encodeIn C))) = _
    have hkey : extractKeyB (binConvert.eval (encodeIn C))
        = encKeyB (FlatCC_to_BinaryCC_instance C) := by
      by_cases h : isValidFlattening C
      · have hok : okB C.Sigma C.init C.cards C.final = true :=
          (validB_iff C).mpr h
        rw [hok] at hBOFF hBWID hBINIT hBCARDS hBFINAL hSTEPS
        simp only [Bool.cond_true] at hBOFF hBWID hBINIT hBCARDS hBFINAL hSTEPS
        simp only [extractKeyB]
        rw [hBOFF, hBWID, hBINIT, hBCARDS, hBFINAL, hSTEPS]
        rw [FlatCC_to_BinaryCC_instance, dif_pos h]
        show _ = [List.replicate (C.Sigma * C.offset) 1,
          List.replicate (C.Sigma * C.width) 1,
          bitsNat (encodeString (unflattenList C.Sigma C.init h.1)),
          encCardsOut (((unflattenCards C.Sigma C.cards h.2.2).map
            encodeCard).map cardNat),
          encFinal ((encodeFinal (unflattenFinal C.Sigma C.final h.2.1)).map
            bitsNat),
          List.replicate C.steps 1]
        rw [bitsNat_encodeString, cardsNat_encodeCards,
          finalNat_encodeFinal, Nat.mul_comm C.Sigma C.offset,
          Nat.mul_comm C.Sigma C.width]
        rfl
      · have hok : okB C.Sigma C.init C.cards C.final = false := by
          rcases Bool.eq_false_or_eq_true
              (okB C.Sigma C.init C.cards C.final) with hb | hb
          · exact absurd ((validB_iff C).mp hb) h
          · exact hb
        rw [hok] at hBOFF hBWID hBINIT hBCARDS hBFINAL hSTEPS
        simp only [Bool.cond_false] at hBOFF hBWID hBINIT hBCARDS hBFINAL hSTEPS
        simp only [extractKeyB]
        rw [hBOFF, hBWID, hBINIT, hBCARDS, hBFINAL, hSTEPS,
          FlatCC_to_BinaryCC_instance, dif_neg h]
        rfl
    rw [hkey]
    exact Function.leftInverse_invFun encKeyB_injective _
  cost_le := fun C => by
    obtain ⟨-, -, -, -, -, -, -, hc⟩ :=
      binConvert_run C.Sigma C.offset C.width C.init C.cards C.final
        (encodeIn C) rfl rfl rfl rfl rfl rfl
    have hC : encodable.size C
        = C.Sigma + C.offset + C.width + encodable.size C.init
          + encodable.size C.cards + encodable.size C.final + C.steps + 1 := rfl
    have h1 := encCardsOut_length_le C.cards
    have h2 := encFinal_length_le C.final
    have hLIn : (encNats C.init).length ≤ encodable.size C := by
      rw [encNats_length]
      omega
    refine le_trans hc (binBudget_le_poly (encodable.size C) _ _ _ _ _ _
      (by omega) (by omega) (by omega) hLIn (by omega) (by omega))
  output_size_le := fun C => by
    have h1 := FlatCC_to_BinaryCC_instance_size_bound C
    have hpoly : 4000 * (encodable.size C + 1) ^ 3
        = 4000 * (encodable.size C * encodable.size C * encodable.size C)
          + 12000 * (encodable.size C * encodable.size C)
          + 12000 * encodable.size C + 4000 := by ring
    have h2 : 50 * encodable.size C * encodable.size C
        = 50 * (encodable.size C * encodable.size C) := by ring
    omega
  enc_bit := fun C => by
    intro reg hreg x hx
    simp only [encodeIn, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with h | h | h | h | h | h | h | h | h <;> subst h
    · cases hx
    · rw [List.eq_of_mem_replicate hx]
    · exact encNats_bit _ x hx
    · cases hx
    · exact encFinal_bit _ x hx
    · rw [List.eq_of_mem_replicate hx]
    · rw [List.eq_of_mem_replicate hx]
    · rw [List.eq_of_mem_replicate hx]
    · exact encCardsOut_bit _ x hx
  regBound := 27
  usesBelow := binConvert_usesBelow
  width_le := fun C => by
    show (encodeIn C).length ≤ 27
    simp [encodeIn]
  decode_agree := fun C m => by
    have hpad : ∀ r : Var,
        State.get (encodeIn C ++ List.replicate m []) r
          = State.get (encodeIn C) r :=
      fun r => State.get_append_replicate_nil (encodeIn C) m r
    obtain ⟨hBOFF1, hBWID1, hBINIT1, hBCARDS1, hBFINAL1, hSTEPS1, -, -⟩ :=
      binConvert_run C.Sigma C.offset C.width C.init C.cards C.final
        (encodeIn C ++ List.replicate m [])
        (by rw [hpad]; rfl) (by rw [hpad]; rfl) (by rw [hpad]; rfl)
        (by rw [hpad]; rfl) (by rw [hpad]; rfl) (by rw [hpad]; rfl)
    obtain ⟨hBOFF2, hBWID2, hBINIT2, hBCARDS2, hBFINAL2, hSTEPS2, -, -⟩ :=
      binConvert_run C.Sigma C.offset C.width C.init C.cards C.final
        (encodeIn C) rfl rfl rfl rfl rfl rfl
    show Function.invFun encKeyB _ = Function.invFun encKeyB _
    have hext : extractKeyB (binConvert.eval (encodeIn C ++ List.replicate m []))
        = extractKeyB (binConvert.eval (encodeIn C)) := by
      simp only [extractKeyB]
      rw [hBOFF1, hBOFF2, hBWID1, hBWID2, hBINIT1, hBINIT2, hBCARDS1,
        hBCARDS2, hBFINAL1, hBFINAL2, hSTEPS1, hSTEPS2, hpad STEPS]
    rw [hext]

/-! ## Correctness of the guarded map (extracted from `FlatCC_to_BinaryCC_poly`) -/

/-- **The guarded map is a correct reduction**: `FlatCCLang C ↔
BinaryCCLang (FlatCC_to_BinaryCC_instance C)`. On valid flattenings this is
the block-encoding equivalence (`CC_to_BinaryCC_lang`/`BinaryCC_to_CC_lang`);
on invalid ones both sides are false (the guard emits the no-instance —
required here, per the probe finding: the unguarded map is NOT correct). -/
theorem flatCC_to_binaryCC_correct (C : FlatCC) :
    FlatCCLang C ↔ BinaryCCLang (FlatCC_to_BinaryCC_instance C) := by
  constructor
  · intro hFlat
    rcases hFlat with ⟨_, hflat, hlang⟩
    simpa [FlatCC_to_BinaryCC_instance, hflat] using
      CC_to_BinaryCC_lang (unflattenCC C hflat) hlang
  · intro hBC
    by_cases hflat : isValidFlattening C
    · have hcc : CC.CCLang (unflattenCC C hflat) := by
        have hbc' : BinaryCCLang (CC_to_BinaryCC (unflattenCC C hflat)) := by
          simpa [FlatCC_to_BinaryCC_instance, hflat] using hBC
        exact BinaryCC_to_CC_lang (unflattenCC C hflat) hbc'
      refine ⟨?_, ⟨hflat, hcc⟩⟩
      simpa [flatten_unflattenCC C hflat] using
        flattenCC_wellformed (C := unflattenCC C hflat) hcc.1
    · exfalso
      have : BinaryCCLang binaryCCNoInstance := by
        simpa [FlatCC_to_BinaryCC_instance, hflat] using hBC
      exact binaryCCNoInstance_not_lang this

/-! ## The headline: the third live honest `⪯p'` on the real chain -/

/-- **`FlatCC ⪯p' BinaryCC`** — the third live honest TM-backed reduction on
the real chain (after `kSAT3_reducesPolyMO'` and `flatTCC_reducesPolyMO'`),
and the first with an on-machine input-validity guard.
Axiom-clean: `[propext, Classical.choice, Quot.sound]`. -/
theorem flatCC_reducesPolyMO' : FlatCCLang ⪯p' BinaryCCLang :=
  reducesPolyMO'_of_langFree flatCCBin_reductionLang flatCC_to_binaryCC_correct

end FlatCCBinFree
