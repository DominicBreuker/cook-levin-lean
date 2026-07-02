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

/-! ## Structural fields (frame, `consLen`-freedom, op-supportedness) -/

theorem binConvert_usesBelow : Cmd.UsesBelow binConvert 27 := by
  simp [binConvert, initStep, sentStep, expandBare, expandSent, remCheck,
    setInvalid, CliqueRelTM.readNum, CliqueRelTM.cSkip, Cmd.UsesBelow,
    Op.UsesBelow, SIGMA, INIT, FINAL, STEPS, OFFSET, WIDTH, CARDS, SCAN,
    VALX, FLAG, IDXO, IDXR, REM, BOFF, BWID, BINIT, BCARDS, BFINAL, TFLG,
    IDX2, BOUT, CliqueRelTM.HEAD, CliqueRelTM.INBLK, CliqueRelTM.SKIPR]

theorem binConvert_noConsLen : Cmd.NoConsLen binConvert := by
  simp only [binConvert, initStep, sentStep, expandBare, expandSent, remCheck,
    setInvalid, CliqueRelTM.readNum, CliqueRelTM.cSkip, Cmd.NoConsLen,
    Op.NotConsLen]
  trivial

theorem binConvert_allOpsSupported : Cmd.AllOpsSupported binConvert := by
  simp only [binConvert, initStep, sentStep, expandBare, expandSent, remCheck,
    setInvalid, CliqueRelTM.readNum, CliqueRelTM.cSkip, Cmd.AllOpsSupported,
    Op.IsSupported]
  trivial

end FlatCCBinFree
