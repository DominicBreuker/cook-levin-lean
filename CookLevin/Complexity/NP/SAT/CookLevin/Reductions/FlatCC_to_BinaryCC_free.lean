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

/-- Boolean validity of `isValidFlattening` (reflected). -/
def validB (C : FlatCC) : Bool :=
  allLtB C.Sigma C.init
    && C.cards.all (fun c => allLtB C.Sigma c.prem && allLtB C.Sigma c.conc)
    && C.final.all (allLtB C.Sigma)

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
    simp only [validB, Bool.and_eq_true, List.all_eq_true] at h
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
    simp only [validB, Bool.and_eq_true, List.all_eq_true]
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
