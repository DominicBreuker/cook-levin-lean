import Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC
import Complexity.Complexity.Deciders.CliqueRelTM

set_option autoImplicit false

/-! # `flatTCC_to_flatCC` as a free layer witness — the second live `⪯p'`
(S3 migration, top-down target #2.1)

This file re-proves the first sound-tail reduction `FlatTCC → FlatCC` as a
**free `PolyTimeComputableLang` witness** (template:
`NP/kSAT_to_SAT_free.lean`), giving the second live honest TM-backed reduction
on the real chain: `flatTCC_reducesPolyMO' : FlatTCC.FlatTCCLang ⪯p' FlatCCLang`.

**Design decision (risk-based): the witness computes the UNGUARDED structural
map `flatTCC_to_flatCC`, not the `isValidFlattening`-guarded
`FlatTCC_to_FlatCC_instance`.** The guard is a legitimate input test but it is
*unnecessary for correctness*: an invalid `FlatTCC` maps to an equally invalid
`FlatCC` (same `Sigma`, same symbol content), so both sides of the reduction
iff are false (`flatTCC_to_flatCC_isValidFlattening` below gives the backward
validity transfer, and `flatTCC_to_flatCC_correct` the unconditional iff).
Dropping the guard removes every on-machine `< Sigma` comparison, so the
program is a pure stream re-formatter. The old guarded `⪯p` reduction
(`FlatTCC_to_FlatCC_poly`) is untouched; the chain swaps to this witness when
the S3 re-typing lands.

**The layouts.** Input (`encodeIn`, the natural FlatTCC layout, numbers UNARY):
reg 1 `Sigma` (unary), reg 2 `init` (bare unary blocks `1^v 0`), reg 3 `cards`
(6 bare blocks per card, prem-first), reg 4 `final` (sentinel-list strings),
reg 5 `steps` (unary). Output (`encKey`, the natural FlatCC layout `decodeOut`
inverts): `Sigma`/`init`/`final`/`steps` **shared-layout** in regs 1/2/4/5
(the map is the identity on them — the honest program for an identity field
costs nothing), `offset` reg 6, `width` reg 7, `cards` reg 8 (per card: two
sentinel-delimited `0`-terminated 3-element lists, the natural `CCCard` layout
— arbitrary-length lists need per-element sentinels for injectivity, exactly
like `EvalCnfCmd.encodeCnf`). The program's real work is the card-stream
re-format (the content of the triple→list coercion) plus writing the two new
constant fields; design `#eval`-validated in `probes/FlatTCCConvertProbe.lean`.

**⚠ Honesty discipline** (HANDOFF standing risk 1): `encodeIn` is the natural
layout of the *input* (bare fixed-arity blocks for the 6-tuples — NOT the
output's sentinel format), `decodeOut = Function.invFun encKey` inverts the
natural injective layout of the *output*, and all re-formatting happens in the
`Cmd`. -/

namespace FlatTCCFree

open Complexity.Lang

/-! ## Registers

Input layout in 1–5, output-only fields in 6–8, scratch at 9–13.
`CliqueRelTM.readNum` pins `HEAD = 15`, `INBLK = 16`, `SKIPR = 26` (`cSkip`). -/

def SIGMA  : Var := 1
def INIT   : Var := 2
def CARDS  : Var := 3
def FINAL  : Var := 4
def STEPS  : Var := 5
def OFFSET : Var := 6
def WIDTH  : Var := 7
def OUT    : Var := 8
def SCAN   : Var := 9
def VALX   : Var := 10
def FLAG   : Var := 11
def IDXO   : Var := 12
def IDXR   : Var := 13

/-! ## Encodings -/

/-- Bare unary block: `1^v 0` (self-delimiting, prefix-free). -/
def encNat (v : Nat) : List Nat := List.replicate v 1 ++ [0]

/-- A `List Nat` as a stream of bare blocks. -/
def encNats : List Nat → List Nat
  | [] => []
  | v :: xs => encNat v ++ encNats xs

/-- Sentinel element `1 :: 1^v 0`: the leading `1` distinguishes an element
from a list terminator `0`, making *nested* lists decodable. -/
def encSElem (v : Nat) : List Nat := 1 :: (List.replicate v 1 ++ [0])

/-- A `List Nat` as a sentinel-delimited, `0`-terminated list (nestable). -/
def encSList : List Nat → List Nat
  | [] => [0]
  | v :: xs => encSElem v ++ encSList xs

/-- The 6 nats of a TCC card, prem-first. -/
def cardNats (c : TCCCard Nat) : List Nat :=
  [c.prem.cardEl1, c.prem.cardEl2, c.prem.cardEl3,
   c.conc.cardEl1, c.conc.cardEl2, c.conc.cardEl3]

/-- Input card: 6 bare blocks (fixed arity needs no sentinels). -/
def encCardIn (c : TCCCard Nat) : List Nat := encNats (cardNats c)

def encCardsIn : List (TCCCard Nat) → List Nat
  | [] => []
  | c :: cs => encCardIn c ++ encCardsIn cs

/-- Output card: the two `CCCard` lists, each sentinel-encoded. -/
def encCardOut (c : CCCard Nat) : List Nat := encSList c.prem ++ encSList c.conc

def encCardsOut : List (CCCard Nat) → List Nat
  | [] => []
  | c :: cs => encCardOut c ++ encCardsOut cs

def encFinal : List (List Nat) → List Nat
  | [] => []
  | s :: fss => encSList s ++ encFinal fss

/-- The natural FlatTCC input layout. -/
def encodeIn (C : FlatTCC) : State :=
  [[], List.replicate C.Sigma 1, encNats C.init, encCardsIn C.cards,
   encFinal C.final, List.replicate C.steps 1]

/-- The natural FlatCC output layout, as the 7-register key `decodeOut`
inverts: `[Sigma, offset, width, init, cards, final, steps]`. -/
def encKey (P : FlatCC) : List (List Nat) :=
  [List.replicate P.Sigma 1, List.replicate P.offset 1,
   List.replicate P.width 1, encNats P.init, encCardsOut P.cards,
   encFinal P.final, List.replicate P.steps 1]

/-- The output registers, in `encKey` order. -/
def extractKey (s : State) : List (List Nat) :=
  [State.get s SIGMA, State.get s OFFSET, State.get s WIDTH,
   State.get s INIT, State.get s OUT, State.get s FINAL, State.get s STEPS]

/-! ## The program -/

/-- Move one bare block off `SCAN` onto `OUT` as a sentinel element:
append the `1` sentinel, drain the block into `VALX` (`readNum`), append it,
close with `0`. -/
def blockMove : Cmd :=
  Cmd.op (.appendOne OUT) ;;
  CliqueRelTM.readNum VALX SCAN IDXR ;;
  Cmd.op (.concat OUT OUT VALX) ;;
  Cmd.op (.appendZero OUT)

/-- Three blocks plus the list terminator: one `CCCard` component. -/
def halfMove : Cmd :=
  blockMove ;; blockMove ;; blockMove ;; Cmd.op (.appendZero OUT)

/-- Consume one card (6 blocks) off `SCAN`, appending its `CCCard` layout to
`OUT`; idle when `SCAN` is exhausted. -/
def cardStep : Cmd :=
  Cmd.op (.nonEmpty FLAG SCAN) ;;
  Cmd.ifBit FLAG (halfMove ;; halfMove) CliqueRelTM.cSkip

/-- **The reduction program**: copy the card stream to scratch, write the two
constant fields (`offset := 1`, `width := 3`), and re-format the stream card by
card. The loop bound is the stream's entry length (≥ the card count — each
card occupies ≥ 6 cells); surplus iterations idle. -/
def cardConvert : Cmd :=
  Cmd.op (.copy SCAN CARDS) ;;
  Cmd.op (.clear OUT) ;;
  Cmd.op (.clear OFFSET) ;; Cmd.op (.appendOne OFFSET) ;;
  Cmd.op (.clear WIDTH) ;;
  Cmd.op (.appendOne WIDTH) ;; Cmd.op (.appendOne WIDTH) ;;
  Cmd.op (.appendOne WIDTH) ;;
  Cmd.forBnd IDXO SCAN cardStep

/-! ## Encoding structure lemmas -/

theorem encNat_length (v : Nat) : (encNat v).length = v + 1 := by
  simp [encNat]

theorem encNat_append (v : Nat) (A : List Nat) :
    encNat v ++ A = List.replicate v 1 ++ 0 :: A := by
  simp [encNat]

theorem encSElem_length (v : Nat) : (encSElem v).length = v + 2 := by
  simp [encSElem]

theorem encSElem_append (v : Nat) (A : List Nat) :
    encSElem v ++ A = 1 :: (List.replicate v 1 ++ 0 :: A) := by
  simp [encSElem]

theorem encNats_append (xs ys : List Nat) :
    encNats (xs ++ ys) = encNats xs ++ encNats ys := by
  induction xs with
  | nil => rfl
  | cons v xs ih => rw [List.cons_append, encNats, encNats, ih, List.append_assoc]

theorem encCardsIn_append (as bs : List (TCCCard Nat)) :
    encCardsIn (as ++ bs) = encCardsIn as ++ encCardsIn bs := by
  induction as with
  | nil => rfl
  | cons c as ih => rw [List.cons_append, encCardsIn, encCardsIn, ih,
      List.append_assoc]

theorem encCardsOut_append (as bs : List (CCCard Nat)) :
    encCardsOut (as ++ bs) = encCardsOut as ++ encCardsOut bs := by
  induction as with
  | nil => rfl
  | cons c as ih => rw [List.cons_append, encCardsOut, encCardsOut, ih,
      List.append_assoc]

/-- The input card stream splits into the two card halves. -/
theorem encCardIn_eq (c : TCCCard Nat) :
    encCardIn c
      = encNats [c.prem.cardEl1, c.prem.cardEl2, c.prem.cardEl3]
        ++ encNats [c.conc.cardEl1, c.conc.cardEl2, c.conc.cardEl3] := by
  show encNats ([c.prem.cardEl1, c.prem.cardEl2, c.prem.cardEl3]
      ++ [c.conc.cardEl1, c.conc.cardEl2, c.conc.cardEl3]) = _
  exact encNats_append _ _

/-- The output card layout is the two sentinel 3-lists of the flat card. -/
theorem encCardOut_conv (c : TCCCard Nat) :
    encCardOut (flatTCCCard_to_CCCard c)
      = encSList [c.prem.cardEl1, c.prem.cardEl2, c.prem.cardEl3]
        ++ encSList [c.conc.cardEl1, c.conc.cardEl2, c.conc.cardEl3] := rfl

theorem encSList_three (a b c : Nat) :
    encSList [a, b, c] = encSElem a ++ (encSElem b ++ (encSElem c ++ [0])) := by
  simp [encSList]

theorem encNats_three (a b c : Nat) :
    encNats [a, b, c] = encNat a ++ (encNat b ++ (encNat c ++ [])) := by
  simp [encNats]

/-! ### Length accounting -/

theorem encNats_length (xs : List Nat) :
    (encNats xs).length = encodable.size xs := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
      rw [encNats, List.length_append, encNat_length, ih,
        encodable_size_list_cons]
      show v + 1 + encodable.size xs = v + 1 + encodable.size xs
      rfl

theorem encSList_length (xs : List Nat) :
    (encSList xs).length = encodable.size xs + xs.length + 1 := by
  induction xs with
  | nil => simp [encSList, encodable_size_list_nil]
  | cons v xs ih =>
      rw [encSList, List.length_append, encSElem_length, ih,
        encodable_size_list_cons, List.length_cons]
      show v + 2 + (encodable.size xs + xs.length + 1)
          = v + 1 + encodable.size xs + (xs.length + 1) + 1
      omega

theorem encCardIn_length (c : TCCCard Nat) :
    (encCardIn c).length
      = c.prem.cardEl1 + c.prem.cardEl2 + c.prem.cardEl3
        + c.conc.cardEl1 + c.conc.cardEl2 + c.conc.cardEl3 + 6 := by
  show (encNats (cardNats c)).length = _
  rw [encNats_length]
  show encodable.size [c.prem.cardEl1, c.prem.cardEl2, c.prem.cardEl3,
    c.conc.cardEl1, c.conc.cardEl2, c.conc.cardEl3] = _
  simp only [encodable_size_list_cons, encodable_size_list_nil]
  show c.prem.cardEl1 + 1 + (c.prem.cardEl2 + 1 + (c.prem.cardEl3 + 1
      + (c.conc.cardEl1 + 1 + (c.conc.cardEl2 + 1 + (c.conc.cardEl3 + 1 + 0)))))
      = _
  omega

theorem encCardOut_conv_length (c : TCCCard Nat) :
    (encCardOut (flatTCCCard_to_CCCard c)).length
      = c.prem.cardEl1 + c.prem.cardEl2 + c.prem.cardEl3
        + c.conc.cardEl1 + c.conc.cardEl2 + c.conc.cardEl3 + 14 := by
  rw [encCardOut_conv, List.length_append, encSList_length, encSList_length]
  simp only [encodable_size_list_cons, encodable_size_list_nil,
    List.length_cons, List.length_nil]
  show c.prem.cardEl1 + 1 + (c.prem.cardEl2 + 1 + (c.prem.cardEl3 + 1 + 0))
        + (0 + 1 + 1 + 1) + 1
      + (c.conc.cardEl1 + 1 + (c.conc.cardEl2 + 1 + (c.conc.cardEl3 + 1 + 0))
        + (0 + 1 + 1 + 1) + 1) = _
  omega

/-- Per card, the output layout is at most 4× the input layout. -/
theorem encCardOut_conv_le (c : TCCCard Nat) :
    (encCardOut (flatTCCCard_to_CCCard c)).length ≤ 4 * (encCardIn c).length := by
  rw [encCardOut_conv_length, encCardIn_length]
  omega

theorem encCardsOut_map_le (cs : List (TCCCard Nat)) :
    (encCardsOut (cs.map flatTCCCard_to_CCCard)).length
      ≤ 4 * (encCardsIn cs).length := by
  induction cs with
  | nil => simp [encCardsOut, encCardsIn]
  | cons c cs ih =>
      rw [List.map_cons, encCardsOut, encCardsIn, List.length_append,
        List.length_append]
      have := encCardOut_conv_le c
      omega

theorem length_le_encCardsIn (cs : List (TCCCard Nat)) :
    cs.length ≤ (encCardsIn cs).length := by
  induction cs with
  | nil => simp [encCardsIn]
  | cons c cs ih =>
      rw [List.length_cons, encCardsIn, List.length_append, encCardIn_length]
      omega

theorem encCardsIn_take_le (cs : List (TCCCard Nat)) (i : Nat) :
    (encCardsIn (cs.take i)).length ≤ (encCardsIn cs).length := by
  conv_rhs => rw [← List.take_append_drop i cs]
  rw [encCardsIn_append, List.length_append]
  exact Nat.le_add_right _ _

theorem encCardsIn_drop_le (cs : List (TCCCard Nat)) (i : Nat) :
    (encCardsIn (cs.drop i)).length ≤ (encCardsIn cs).length := by
  conv_rhs => rw [← List.take_append_drop i cs]
  rw [encCardsIn_append, List.length_append]
  exact Nat.le_add_left _ _

theorem encCardsIn_length_le (cs : List (TCCCard Nat)) :
    (encCardsIn cs).length ≤ 2 * encodable.size cs := by
  induction cs with
  | nil => simp [encCardsIn, encodable_size_list_nil]
  | cons c cs ih =>
      rw [encCardsIn, List.length_append, encodable_size_list_cons,
        encCardIn_length]
      have hsz : c.prem.cardEl1 + c.prem.cardEl2 + c.prem.cardEl3
          + c.conc.cardEl1 + c.conc.cardEl2 + c.conc.cardEl3 + 3
          = encodable.size c := by
        show _ = encodable.size c.prem + encodable.size c.conc + 1
        show _ = (c.prem.cardEl1 + c.prem.cardEl2 + c.prem.cardEl3 + 1)
            + (c.conc.cardEl1 + c.conc.cardEl2 + c.conc.cardEl3 + 1) + 1
        omega
      omega

theorem encFinal_length_le (fss : List (List Nat)) :
    (encFinal fss).length ≤ 2 * encodable.size fss := by
  induction fss with
  | nil => simp [encFinal, encodable_size_list_nil]
  | cons s fss ih =>
      rw [encFinal, List.length_append, encodable_size_list_cons,
        encSList_length]
      have hlen : s.length ≤ encodable.size s := by
        induction s with
        | nil => simp [encodable_size_list_nil]
        | cons x s ihs =>
            rw [List.length_cons, encodable_size_list_cons]
            omega
      omega

/-! ### Bit-level cells (`enc_bit`) -/

theorem encNat_bit (v : Nat) : ∀ x ∈ encNat v, x ≤ 1 := by
  intro x hx
  rw [encNat] at hx
  rcases List.mem_append.mp hx with h | h
  · rw [List.eq_of_mem_replicate h]
  · simp only [List.mem_singleton] at h
    omega

theorem encNats_bit (xs : List Nat) : ∀ x ∈ encNats xs, x ≤ 1 := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons v xs ih =>
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact encNat_bit v x h
      · exact ih x h

theorem encCardsIn_bit (cs : List (TCCCard Nat)) : ∀ x ∈ encCardsIn cs, x ≤ 1 := by
  induction cs with
  | nil => intro x hx; cases hx
  | cons c cs ih =>
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact encNats_bit _ x h
      · exact ih x h

theorem encSList_bit (xs : List Nat) : ∀ x ∈ encSList xs, x ≤ 1 := by
  induction xs with
  | nil =>
      intro x hx
      simp only [encSList, List.mem_singleton] at hx
      omega
  | cons v xs ih =>
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · rw [encSElem] at h
        rcases List.mem_cons.mp h with h | h
        · omega
        · rcases List.mem_append.mp h with h | h
          · rw [List.eq_of_mem_replicate h]
          · simp only [List.mem_singleton] at h
            omega
      · exact ih x h

theorem encFinal_bit (fss : List (List Nat)) : ∀ x ∈ encFinal fss, x ≤ 1 := by
  induction fss with
  | nil => intro x hx; cases hx
  | cons s fss ih =>
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact encSList_bit s x h
      · exact ih x h

/-! ### Injectivity (for `decodeOut := Function.invFun encKey`) -/

private theorem replicate_block_inj : ∀ {v v' : Nat} {x y : List Nat},
    List.replicate v 1 ++ 0 :: x = List.replicate v' 1 ++ 0 :: y →
    v = v' ∧ x = y
  | 0, 0, x, y, h => by simpa using h
  | 0, v' + 1, x, y, h => by simp [List.replicate_succ] at h
  | v + 1, 0, x, y, h => by simp [List.replicate_succ] at h
  | v + 1, v' + 1, x, y, h => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq,
        true_and] at h
      obtain ⟨hv, hxy⟩ := replicate_block_inj h
      exact ⟨by omega, hxy⟩

private theorem encNat_append_inj {v v' : Nat} {A B : List Nat}
    (h : encNat v ++ A = encNat v' ++ B) : v = v' ∧ A = B := by
  rw [encNat_append, encNat_append] at h
  exact replicate_block_inj h

theorem encNats_injective : Function.Injective encNats := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          exfalso
          rw [show encNats [] = [] from rfl, encNats] at h
          have hlen := congrArg List.length h
          rw [List.length_nil, List.length_append, encNat_length] at hlen
          omega
  | cons x xs ih =>
      cases ys with
      | nil =>
          exfalso
          rw [show encNats [] = [] from rfl, encNats] at h
          have hlen := congrArg List.length h
          rw [List.length_nil, List.length_append, encNat_length] at hlen
          omega
      | cons y ys =>
          rw [encNats, encNats] at h
          obtain ⟨hv, hrest⟩ := encNat_append_inj h
          rw [hv, ih hrest]

private theorem encSElem_append_inj {v v' : Nat} {A B : List Nat}
    (h : encSElem v ++ A = encSElem v' ++ B) : v = v' ∧ A = B := by
  rw [encSElem_append, encSElem_append] at h
  simp only [List.cons.injEq, true_and] at h
  exact replicate_block_inj h

private theorem encSList_append_inj : ∀ {xs ys : List Nat} {A B : List Nat},
    encSList xs ++ A = encSList ys ++ B → xs = ys ∧ A = B
  | [], [], A, B, h => ⟨rfl, by simpa [encSList] using h⟩
  | [], y :: ys, A, B, h => by
      exfalso
      rw [show encSList [] = [0] from rfl, encSList, encSElem_append] at h
      simp at h
  | x :: xs, [], A, B, h => by
      exfalso
      rw [show encSList [] = [0] from rfl, encSList, encSElem_append] at h
      simp at h
  | x :: xs, y :: ys, A, B, h => by
      rw [encSList, encSList, List.append_assoc, List.append_assoc] at h
      obtain ⟨hv, hrest⟩ := encSElem_append_inj h
      obtain ⟨hxs, hAB⟩ := encSList_append_inj hrest
      exact ⟨by rw [hv, hxs], hAB⟩

theorem encSList_length_pos (xs : List Nat) : 1 ≤ (encSList xs).length := by
  rw [encSList_length]
  omega

theorem encCardsOut_injective : Function.Injective encCardsOut := by
  intro cs cs' h
  induction cs generalizing cs' with
  | nil =>
      cases cs' with
      | nil => rfl
      | cons c' cs' =>
          exfalso
          rw [show encCardsOut [] = [] from rfl, encCardsOut, encCardOut,
            List.append_assoc] at h
          have hlen := congrArg List.length h
          rw [List.length_nil, List.length_append] at hlen
          have := encSList_length_pos c'.prem
          omega
  | cons c cs ih =>
      cases cs' with
      | nil =>
          exfalso
          rw [show encCardsOut [] = [] from rfl, encCardsOut, encCardOut,
            List.append_assoc] at h
          have hlen := congrArg List.length h
          rw [List.length_nil, List.length_append] at hlen
          have := encSList_length_pos c.prem
          omega
      | cons c' cs' =>
          rw [encCardsOut, encCardsOut, encCardOut, encCardOut,
            List.append_assoc, List.append_assoc] at h
          obtain ⟨hprem, hrest⟩ := encSList_append_inj h
          obtain ⟨hconc, hrest2⟩ := encSList_append_inj hrest
          have hcard : c = c' := by
            cases c; cases c'
            simp_all
          rw [hcard, ih hrest2]

theorem encFinal_injective : Function.Injective encFinal := by
  intro fss fss' h
  induction fss generalizing fss' with
  | nil =>
      cases fss' with
      | nil => rfl
      | cons s' fss' =>
          exfalso
          rw [show encFinal [] = [] from rfl, encFinal] at h
          have hlen := congrArg List.length h
          rw [List.length_nil, List.length_append] at hlen
          have := encSList_length_pos s'
          omega
  | cons s fss ih =>
      cases fss' with
      | nil =>
          exfalso
          rw [show encFinal [] = [] from rfl, encFinal] at h
          have hlen := congrArg List.length h
          rw [List.length_nil, List.length_append] at hlen
          have := encSList_length_pos s
          omega
      | cons s' fss' =>
          rw [encFinal, encFinal] at h
          obtain ⟨hs, hrest⟩ := encSList_append_inj h
          rw [hs, ih hrest]

theorem encKey_injective : Function.Injective encKey := by
  intro P Q h
  cases P with
  | mk PS PO PW PI PC PF PT =>
      cases Q with
      | mk QS QO QW QI QC QF QT =>
          simp only [encKey, List.cons.injEq, and_true] at h
          obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
          simp only [FlatCC.mk.injEq]
          exact ⟨CliqueRelTM.replicate_one_eq_iff.mp h1,
            CliqueRelTM.replicate_one_eq_iff.mp h2,
            CliqueRelTM.replicate_one_eq_iff.mp h3,
            encNats_injective h4, encCardsOut_injective h5,
            encFinal_injective h6, CliqueRelTM.replicate_one_eq_iff.mp h7⟩

/-! ## The block gadget: run + cost -/

/-- **`blockMove` is correct**: on `SCAN = 1^v 0 ++ X` it consumes the block
and appends the sentinel element `1 1^v 0` to `OUT`. -/
theorem blockMove_run (s : State) (v : Nat) (X : List Nat) (S T : Nat)
    (hSC : State.get s SCAN = encNat v ++ X)
    (hS : (State.get s SCAN).length ≤ S)
    (hT : (State.get s OUT).length ≤ T) :
    State.get (blockMove.eval s) SCAN = X
    ∧ State.get (blockMove.eval s) OUT = State.get s OUT ++ encSElem v
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ VALX → r ≠ IDXR →
        r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
        State.get (blockMove.eval s) r = State.get s r)
    ∧ blockMove.cost s ≤ 2 * (S * S) + 9 * S + 2 * T + 15 := by
  have hvS : v + 1 + X.length ≤ S := by
    have : (State.get s SCAN).length = v + 1 + X.length := by
      rw [hSC, List.length_append, encNat_length]
    omega
  -- stage 1: the sentinel
  have e1 : (Cmd.op (.appendOne OUT)).eval s
      = s.set OUT (State.get s OUT ++ [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set s1 := s.set OUT (State.get s OUT ++ [1]) with hs1
  have hs1SCAN : State.get s1 SCAN = List.replicate v 1 ++ 0 :: X := by
    rw [State.get_set_ne _ _ _ _ (by decide), hSC, encNat_append]
  have hs1OUT : State.get s1 OUT = State.get s OUT ++ [1] :=
    State.get_set_eq _ _ _
  -- stage 2: drain the block
  obtain ⟨hVAL, hSC2, hF2⟩ := CliqueRelTM.readNum_run s1 v X VALX SCAN IDXR
    hs1SCAN (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  set s2 := (CliqueRelTM.readNum VALX SCAN IDXR).eval s1 with hs2
  have hs2OUT : State.get s2 OUT = State.get s OUT ++ [1] := by
    rw [hF2 OUT (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hs1OUT
  -- stage 3: append the payload
  have e3 : (Cmd.op (.concat OUT OUT VALX)).eval s2
      = s2.set OUT ((State.get s OUT ++ [1]) ++ List.replicate v 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hs2OUT, hVAL]
  set s3 := s2.set OUT ((State.get s OUT ++ [1]) ++ List.replicate v 1) with hs3
  have hs3OUT : State.get s3 OUT
      = (State.get s OUT ++ [1]) ++ List.replicate v 1 := by
    rw [hs3]; exact State.get_set_eq _ _ _
  -- stage 4: close the element
  have e4 : (Cmd.op (.appendZero OUT)).eval s3
      = s3.set OUT ((State.get s OUT ++ [1]) ++ List.replicate v 1 ++ [0]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hs3OUT]
  have heval : blockMove.eval s
      = s3.set OUT ((State.get s OUT ++ [1]) ++ List.replicate v 1 ++ [0]) := by
    show ((Cmd.op (.appendOne OUT)) ;; _).eval s = _
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hs2, Cmd.eval_seq, e3, e4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval, State.get_set_ne _ _ _ _ (by decide), hs3,
      State.get_set_ne _ _ _ _ (by decide)]
    exact hSC2
  · rw [heval, State.get_set_eq, encSElem]
    simp [List.append_assoc]
  · intro r h1 h2 h3 h4 h5 h6 h7
    rw [heval, State.get_set_ne _ _ _ _ h2, hs3, State.get_set_ne _ _ _ _ h2,
      hF2 r h1 h3 h6 h5 h7 h4, hs1, State.get_set_ne _ _ _ _ h2]
  · -- cost accounting
    have hrn := CliqueRelTM.readNum_cost s1 VALX SCAN IDXR
      (by decide) (by decide) (by decide) (by decide) (by decide)
    have hlen1 : (State.get s1 SCAN).length ≤ S := by
      rw [hs1SCAN, List.length_append, List.length_replicate, List.length_cons]
      omega
    have hrn' : (CliqueRelTM.readNum VALX SCAN IDXR).cost s1
        ≤ 2 * (S * S) + 7 * S + 7 := by
      set L := (State.get s1 SCAN).length with hL
      have hsq : L * L ≤ S * S := Nat.mul_le_mul hlen1 hlen1
      have h2LL : 2 * L * L ≤ 2 * (S * S) := by
        calc 2 * L * L = 2 * (L * L) := by ring
          _ ≤ 2 * (S * S) := Nat.mul_le_mul_left 2 hsq
      omega
    have hcost : blockMove.cost s
        = 1 + 1 + (1 + (CliqueRelTM.readNum VALX SCAN IDXR).cost s1
            + (1 + (2 * ((State.get s OUT ++ [1]).length
                + (List.replicate v 1).length) + 1) + 1)) := by
      show ((Cmd.op (.appendOne OUT)) ;; _).cost s = _
      rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_seq, e1, Cmd.cost_seq, ← hs2,
        Cmd.cost_op, Cmd.cost_op, e3]
      simp only [Op.cost, hs2OUT, hVAL]
    rw [hcost, List.length_append, List.length_replicate]
    simp only [List.length_cons, List.length_nil]
    omega

/-! ## The half-card gadget: run + cost -/

/-- **`halfMove` is correct**: consumes three blocks and appends the sentinel
3-list (one `CCCard` component) to `OUT`. -/
theorem halfMove_run (s : State) (a b c : Nat) (X : List Nat) (S T : Nat)
    (hSC : State.get s SCAN = encNats [a, b, c] ++ X)
    (hS : (State.get s SCAN).length ≤ S)
    (hT : (State.get s OUT).length + (a + b + c) + 7 ≤ T) :
    State.get (halfMove.eval s) SCAN = X
    ∧ State.get (halfMove.eval s) OUT = State.get s OUT ++ encSList [a, b, c]
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ VALX → r ≠ IDXR →
        r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
        State.get (halfMove.eval s) r = State.get s r)
    ∧ halfMove.cost s ≤ 6 * (S * S) + 27 * S + 6 * T + 50 := by
  have hSC1 : State.get s SCAN = encNat a ++ (encNat b ++ (encNat c ++ X)) := by
    rw [hSC, encNats_three]
    simp [List.append_assoc]
  have hlenSC : (State.get s SCAN).length
      = (a + 1) + ((b + 1) + ((c + 1) + X.length)) := by
    rw [hSC1]
    simp only [List.length_append, encNat_length]
  -- block a
  obtain ⟨hA1, hB1, hF1, hC1⟩ := blockMove_run s a (encNat b ++ (encNat c ++ X))
    S T hSC1 hS (by omega)
  set s1 := blockMove.eval s with hs1
  have hS1 : (State.get s1 SCAN).length ≤ S := by
    rw [hA1]
    simp only [List.length_append, encNat_length]
    omega
  have hT1 : (State.get s1 OUT).length ≤ T := by
    rw [hB1, List.length_append, encSElem_length]
    omega
  -- block b
  obtain ⟨hA2, hB2, hF2, hC2⟩ := blockMove_run s1 b (encNat c ++ X) S T hA1
    hS1 hT1
  set s2 := blockMove.eval s1 with hs2
  have hS2 : (State.get s2 SCAN).length ≤ S := by
    rw [hA2]
    simp only [List.length_append, encNat_length]
    omega
  have hT2 : (State.get s2 OUT).length ≤ T := by
    rw [hB2, hB1, List.length_append, List.length_append, encSElem_length,
      encSElem_length]
    omega
  -- block c
  obtain ⟨hA3, hB3, hF3, hC3⟩ := blockMove_run s2 c X S T hA2 hS2 hT2
  set s3 := blockMove.eval s2 with hs3
  -- the terminator
  have e4 : (Cmd.op (.appendZero OUT)).eval s3
      = s3.set OUT (State.get s3 OUT ++ [0]) := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have heval : halfMove.eval s = s3.set OUT (State.get s3 OUT ++ [0]) := by
    show (blockMove ;; _).eval s = _
    rw [Cmd.eval_seq, ← hs1, Cmd.eval_seq, ← hs2, Cmd.eval_seq, ← hs3, e4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval, State.get_set_ne _ _ _ _ (by decide)]
    exact hA3
  · rw [heval, State.get_set_eq, hB3, hB2, hB1, encSList_three]
    simp [List.append_assoc]
  · intro r h1 h2 h3 h4 h5 h6 h7
    rw [heval, State.get_set_ne _ _ _ _ h2, hF3 r h1 h2 h3 h4 h5 h6 h7,
      hF2 r h1 h2 h3 h4 h5 h6 h7, hF1 r h1 h2 h3 h4 h5 h6 h7]
  · have hcost : halfMove.cost s
        = 1 + blockMove.cost s + (1 + blockMove.cost s1
            + (1 + blockMove.cost s2 + 1)) := by
      show (blockMove ;; _).cost s = _
      rw [Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, ← hs1, ← hs2, Cmd.cost_op]
      simp only [Op.cost]
    rw [hcost]
    omega

/-! ## The per-card gadget: run + cost -/

/-- `cardStep`, card case: `SCAN` starts with a full card. Consumes it and
appends the `CCCard` layout to `OUT`. -/
theorem cardStep_card (s : State) (c : TCCCard Nat) (X : List Nat) (S T : Nat)
    (hSC : State.get s SCAN = encCardIn c ++ X)
    (hS : (State.get s SCAN).length ≤ S)
    (hT : (State.get s OUT).length
        + (encCardOut (flatTCCCard_to_CCCard c)).length ≤ T) :
    State.get (cardStep.eval s) SCAN = X
    ∧ State.get (cardStep.eval s) OUT
        = State.get s OUT ++ encCardOut (flatTCCCard_to_CCCard c)
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ VALX → r ≠ FLAG → r ≠ IDXR →
        r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
        State.get (cardStep.eval s) r = State.get s r)
    ∧ cardStep.cost s ≤ 12 * (S * S) + 54 * S + 12 * T + 110 := by
  have hCOlen := encCardOut_conv_length c
  -- the nonEmpty test fires
  have hne : (State.get s SCAN).isEmpty = false := by
    rw [hSC, encCardIn_eq, encNats_three]
    cases c.prem.cardEl1 <;> simp [encNat, List.replicate_succ]
  have e0 : (Cmd.op (.nonEmpty FLAG SCAN)).eval s = s.set FLAG [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hne]
    rfl
  set w := s.set FLAG [1] with hw
  have hwFLAG : State.get w FLAG = [1] := State.get_set_eq _ _ _
  have hwSCAN : State.get w SCAN = State.get s SCAN :=
    State.get_set_ne _ _ _ _ (by decide)
  have hwOUT : State.get w OUT = State.get s OUT :=
    State.get_set_ne _ _ _ _ (by decide)
  -- first half
  have hSCw : State.get w SCAN
      = encNats [c.prem.cardEl1, c.prem.cardEl2, c.prem.cardEl3]
        ++ (encNats [c.conc.cardEl1, c.conc.cardEl2, c.conc.cardEl3] ++ X) := by
    rw [hwSCAN, hSC, encCardIn_eq, List.append_assoc]
  have hSw : (State.get w SCAN).length ≤ S := by rw [hwSCAN]; exact hS
  have hTw : (State.get w OUT).length
      + (c.prem.cardEl1 + c.prem.cardEl2 + c.prem.cardEl3) + 7 ≤ T := by
    rw [hwOUT]
    omega
  obtain ⟨hA1, hB1, hF1, hC1⟩ := halfMove_run w c.prem.cardEl1 c.prem.cardEl2
    c.prem.cardEl3 _ S T hSCw hSw hTw
  set u1 := halfMove.eval w with hu1
  -- second half
  have hSu1 : (State.get u1 SCAN).length ≤ S := by
    rw [hA1]
    have : (State.get w SCAN).length
        = (encNats [c.prem.cardEl1, c.prem.cardEl2, c.prem.cardEl3]).length
          + ((encNats [c.conc.cardEl1, c.conc.cardEl2, c.conc.cardEl3]
              ++ X)).length := by
      rw [hSCw, List.length_append]
    omega
  have hTu1 : (State.get u1 OUT).length
      + (c.conc.cardEl1 + c.conc.cardEl2 + c.conc.cardEl3) + 7 ≤ T := by
    rw [hB1, List.length_append, encSList_length]
    simp only [encodable_size_list_cons, encodable_size_list_nil,
      List.length_cons, List.length_nil]
    rw [hwOUT]
    have hsz : ∀ n : Nat, encodable.size n = n := fun n => rfl
    rw [hsz, hsz, hsz]
    omega
  obtain ⟨hA2, hB2, hF2, hC2⟩ := halfMove_run u1 c.conc.cardEl1 c.conc.cardEl2
    c.conc.cardEl3 X S T hA1 hSu1 hTu1
  set u2 := halfMove.eval u1 with hu2
  have heval : cardStep.eval s = u2 := by
    show ((Cmd.op (.nonEmpty FLAG SCAN)) ;; _).eval s = _
    rw [Cmd.eval_seq, e0, Cmd.eval_ifBit_true _ _ _ _ hwFLAG, Cmd.eval_seq,
      ← hu1, ← hu2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval]
    exact hA2
  · rw [heval, hB2, hB1, hwOUT, encCardOut_conv, List.append_assoc]
  · intro r h1 h2 h3 h4 h5 h6 h7 h8
    rw [heval, hF2 r h1 h2 h3 h5 h6 h7 h8, hF1 r h1 h2 h3 h5 h6 h7 h8, hw,
      State.get_set_ne _ _ _ _ h4]
  · have hcost : cardStep.cost s
        = 1 + 1 + (1 + (1 + halfMove.cost w + halfMove.cost u1)) := by
      show ((Cmd.op (.nonEmpty FLAG SCAN)) ;; _).cost s = _
      rw [Cmd.cost_seq, Cmd.cost_op, e0,
        Cmd.cost_ifBit_true _ _ _ _ hwFLAG, Cmd.cost_seq, ← hu1]
      simp only [Op.cost]
    rw [hcost]
    omega

/-- `cardStep`, idle case: `SCAN` is exhausted; the step is a `cSkip`. -/
theorem cardStep_idle (s : State) (hSC : State.get s SCAN = []) :
    cardStep.eval s = (s.set FLAG [0]).set CliqueRelTM.SKIPR [1]
    ∧ cardStep.cost s = 6 := by
  have hne : (State.get s SCAN).isEmpty = true := by rw [hSC]; rfl
  have e0 : (Cmd.op (.nonEmpty FLAG SCAN)).eval s = s.set FLAG [0] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hne]
    rfl
  have hwFLAG : State.get (s.set FLAG [0]) FLAG ≠ [1] := by
    rw [State.get_set_eq]; decide
  constructor
  · show ((Cmd.op (.nonEmpty FLAG SCAN)) ;; _).eval s = _
    rw [Cmd.eval_seq, e0, Cmd.eval_ifBit_false _ _ _ _ hwFLAG,
      CliqueRelTM.cSkip_eval]
  · show ((Cmd.op (.nonEmpty FLAG SCAN)) ;; _).cost s = _
    rw [Cmd.cost_seq, Cmd.cost_op, e0, Cmd.cost_ifBit_false _ _ _ _ hwFLAG,
      CliqueRelTM.cSkip_cost]
    rfl

/-! ## The outer loop: invariant + step -/

/-- The card-loop fold invariant: after `i` iterations the stream holds the
remaining cards and `OUT` the converted prefix. Beyond `|cs|` the loop idles
(`drop`/`take` clamp, so one uniform statement covers both phases). -/
def CInv (cs : List (TCCCard Nat)) (s0 : State) (i : Nat) (st : State) : Prop :=
  State.get st SCAN = encCardsIn (cs.drop i)
  ∧ State.get st OUT = encCardsOut ((cs.take i).map flatTCCCard_to_CCCard)
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ VALX → r ≠ FLAG → r ≠ IDXO →
      r ≠ IDXR → r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.INBLK →
      r ≠ CliqueRelTM.SKIPR → State.get st r = State.get s0 r)

/-- One `cardStep` iteration preserves `CInv`, within the uniform budget. -/
theorem cardStep_step (cs : List (TCCCard Nat)) (s0 : State) (S : Nat)
    (hS : (encCardsIn cs).length ≤ S)
    (i : Nat) (st : State) (h : CInv cs s0 i st) :
    CInv cs s0 (i + 1) (cardStep.eval (st.set IDXO (List.replicate i 1)))
    ∧ cardStep.cost (st.set IDXO (List.replicate i 1))
        ≤ 12 * (S * S) + 102 * S + 110 := by
  obtain ⟨hSCAN, hOUT, hframe⟩ := h
  set w := st.set IDXO (List.replicate i 1) with hw
  have hwSCAN : State.get w SCAN = State.get st SCAN :=
    State.get_set_ne _ _ _ _ (by decide)
  have hwOUT : State.get w OUT = State.get st OUT :=
    State.get_set_ne _ _ _ _ (by decide)
  have hwframe : ∀ r : Var, r ≠ IDXO → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  by_cases hi : i < cs.length
  · -- card iteration
    have hdrop : cs.drop i = cs[i] :: cs.drop (i + 1) := List.drop_eq_getElem_cons hi
    -- (hoisted before any run/cost fact enters the context — `l[i]` gotcha)
    have htake : encCardsOut ((cs.take (i + 1)).map flatTCCCard_to_CCCard)
        = encCardsOut ((cs.take i).map flatTCCCard_to_CCCard)
          ++ encCardOut (flatTCCCard_to_CCCard cs[i]) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
        List.map_append, encCardsOut_append]
      simp [encCardsOut]
    have htakeIn : encCardsIn (cs.take (i + 1))
        = encCardsIn (cs.take i) ++ encCardIn cs[i] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
        encCardsIn_append]
      simp [encCardsIn]
    have hSCw : State.get w SCAN = encCardIn cs[i] ++ encCardsIn (cs.drop (i + 1)) := by
      rw [hwSCAN, hSCAN, hdrop, encCardsIn]
    have hSw : (State.get w SCAN).length ≤ S := by
      rw [hwSCAN, hSCAN]
      exact le_trans (encCardsIn_drop_le cs i) hS
    have hTw : (State.get w OUT).length
        + (encCardOut (flatTCCCard_to_CCCard cs[i])).length ≤ 4 * S := by
      rw [hwOUT, hOUT, ← List.length_append, ← htake]
      calc (encCardsOut ((cs.take (i + 1)).map flatTCCCard_to_CCCard)).length
          ≤ 4 * (encCardsIn (cs.take (i + 1))).length := encCardsOut_map_le _
        _ ≤ 4 * (encCardsIn cs).length :=
            Nat.mul_le_mul_left 4 (encCardsIn_take_le cs (i + 1))
        _ ≤ 4 * S := Nat.mul_le_mul_left 4 hS
    obtain ⟨hA, hB, hF, hC⟩ := cardStep_card w cs[i] _ S (4 * S) hSCw hSw hTw
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hA]
    · rw [hB, hwOUT, hOUT, htake]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [hF r h1 h2 h3 h4 h6 h7 h8 h9, hwframe r h5,
        hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9]
    · calc cardStep.cost w
          ≤ 12 * (S * S) + 54 * S + 12 * (4 * S) + 110 := hC
        _ ≤ 12 * (S * S) + 102 * S + 110 := by omega
  · -- idle iteration
    have hlen : cs.length ≤ i := Nat.le_of_not_lt hi
    have hSCw : State.get w SCAN = [] := by
      rw [hwSCAN, hSCAN, List.drop_eq_nil_of_le hlen]
      rfl
    obtain ⟨heval, hcost⟩ := cardStep_idle w hSCw
    refine ⟨⟨?_, ?_, ?_⟩, by omega⟩
    · rw [heval, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hwSCAN, hSCAN,
        List.drop_eq_nil_of_le hlen, List.drop_eq_nil_of_le (by omega)]
    · rw [heval, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hwOUT, hOUT,
        List.take_of_length_le hlen, List.take_of_length_le (by omega)]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [heval, State.get_set_ne _ _ _ _ h9, State.get_set_ne _ _ _ _ h4,
        hwframe r h5, hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9]

/-! ## The whole program: run + cost -/

/-- Budget for one `cardConvert` run, in the card-stream length `S`. -/
def convBudget (S : Nat) : Nat :=
  12 * (S * S * S) + 105 * (S * S) + 115 * S + 30

/-- The state after `cardConvert`'s 8-op initialisation prefix. -/
def convInit (s0 : State) (E : List Nat) : State :=
  (((((((s0.set SCAN E).set OUT []).set OFFSET []).set OFFSET [1]).set WIDTH
      []).set WIDTH [1]).set WIDTH [1, 1]).set WIDTH [1, 1, 1]

theorem convInit_get_SCAN (s0 : State) (E : List Nat) :
    State.get (convInit s0 E) SCAN = E := by
  unfold convInit
  rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]

theorem convInit_get_OUT (s0 : State) (E : List Nat) :
    State.get (convInit s0 E) OUT = [] := by
  unfold convInit
  rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_eq]

theorem convInit_get_OFFSET (s0 : State) (E : List Nat) :
    State.get (convInit s0 E) OFFSET = [1] := by
  unfold convInit
  rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_eq]

theorem convInit_get_WIDTH (s0 : State) (E : List Nat) :
    State.get (convInit s0 E) WIDTH = [1, 1, 1] :=
  State.get_set_eq _ _ _

theorem convInit_frame (s0 : State) (E : List Nat) :
    ∀ r : Var, r ≠ SCAN → r ≠ OUT → r ≠ OFFSET → r ≠ WIDTH →
      State.get (convInit s0 E) r = State.get s0 r := by
  intro r h1 h2 h3 h4
  unfold convInit
  rw [State.get_set_ne _ _ _ _ h4, State.get_set_ne _ _ _ _ h4,
    State.get_set_ne _ _ _ _ h4, State.get_set_ne _ _ _ _ h4,
    State.get_set_ne _ _ _ _ h3, State.get_set_ne _ _ _ _ h3,
    State.get_set_ne _ _ _ _ h2, State.get_set_ne _ _ _ _ h1]

/-- **`cardConvert` computes the card conversion.** On any state carrying
`CARDS = encCardsIn cs` it writes the converted stream to `OUT`, the constants
to `OFFSET`/`WIDTH`, leaves every register `< OFFSET` (the shared input/output
fields 0–5) untouched, and runs within `convBudget |encCardsIn cs|`. -/
theorem cardConvert_run (cs : List (TCCCard Nat)) (s0 : State)
    (hCARDS : State.get s0 CARDS = encCardsIn cs) :
    State.get (cardConvert.eval s0) OUT
        = encCardsOut (cs.map flatTCCCard_to_CCCard)
    ∧ State.get (cardConvert.eval s0) OFFSET = [1]
    ∧ State.get (cardConvert.eval s0) WIDTH = [1, 1, 1]
    ∧ (∀ r : Var, r < OFFSET →
        State.get (cardConvert.eval s0) r = State.get s0 r)
    ∧ cardConvert.cost s0 ≤ convBudget (encCardsIn cs).length := by
  set S := (encCardsIn cs).length with hSdef
  -- the 8-op initialisation prefix
  have e1 : (Cmd.op (.copy SCAN CARDS)).eval s0
      = s0.set SCAN (encCardsIn cs) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hCARDS]
  have e2 : (Cmd.op (.clear OUT)).eval (s0.set SCAN (encCardsIn cs))
      = (s0.set SCAN (encCardsIn cs)).set OUT [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e3 : (Cmd.op (.clear OFFSET)).eval
        ((s0.set SCAN (encCardsIn cs)).set OUT [])
      = ((s0.set SCAN (encCardsIn cs)).set OUT []).set OFFSET [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e4 : (Cmd.op (.appendOne OFFSET)).eval
        (((s0.set SCAN (encCardsIn cs)).set OUT []).set OFFSET [])
      = (((s0.set SCAN (encCardsIn cs)).set OUT []).set OFFSET []).set OFFSET
          [1] := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, List.nil_append]
  have e5 : (Cmd.op (.clear WIDTH)).eval
        ((((s0.set SCAN (encCardsIn cs)).set OUT []).set OFFSET []).set OFFSET
          [1])
      = ((((s0.set SCAN (encCardsIn cs)).set OUT []).set OFFSET []).set OFFSET
          [1]).set WIDTH [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e6 : (Cmd.op (.appendOne WIDTH)).eval
        (((((s0.set SCAN (encCardsIn cs)).set OUT []).set OFFSET []).set OFFSET
          [1]).set WIDTH [])
      = (((((s0.set SCAN (encCardsIn cs)).set OUT []).set OFFSET []).set OFFSET
          [1]).set WIDTH []).set WIDTH [1] := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, List.nil_append]
  have e7 : (Cmd.op (.appendOne WIDTH)).eval
        ((((((s0.set SCAN (encCardsIn cs)).set OUT []).set OFFSET []).set OFFSET
          [1]).set WIDTH []).set WIDTH [1])
      = ((((((s0.set SCAN (encCardsIn cs)).set OUT []).set OFFSET []).set OFFSET
          [1]).set WIDTH []).set WIDTH [1]).set WIDTH [1, 1] := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, List.cons_append, List.nil_append]
  have e8 : (Cmd.op (.appendOne WIDTH)).eval
        (((((((s0.set SCAN (encCardsIn cs)).set OUT []).set OFFSET []).set
          OFFSET [1]).set WIDTH []).set WIDTH [1]).set WIDTH [1, 1])
      = convInit s0 (encCardsIn cs) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, List.cons_append, List.nil_append]
    rfl
  set u := convInit s0 (encCardsIn cs) with hu
  have huSCAN := convInit_get_SCAN s0 (encCardsIn cs)
  have huOUT := convInit_get_OUT s0 (encCardsIn cs)
  have huOFFSET := convInit_get_OFFSET s0 (encCardsIn cs)
  have huWIDTH := convInit_get_WIDTH s0 (encCardsIn cs)
  have huframe := convInit_frame s0 (encCardsIn cs)
  -- the loop
  have hbase : CInv cs u 0 u := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [huSCAN, List.drop_zero]
    · rw [huOUT]
      rfl
  have hloop_eval : (Cmd.forBnd IDXO SCAN cardStep).eval u
      = Cmd.foldlState cardStep IDXO (List.range S) u := by
    rw [Cmd.eval_forBnd, huSCAN, ← hSdef]
  set z := Cmd.foldlState cardStep IDXO (List.range S) u with hz
  have hInv : CInv cs u S z := by
    rw [hz]
    exact Cmd.foldlState_range_induct cardStep IDXO S u (CInv cs u) hbase
      (fun i st _ hM => (cardStep_step cs u S (le_of_eq hSdef.symm) i st hM).1)
  obtain ⟨hzSCAN, hzOUT, hzframe⟩ := hInv
  have hcsS : cs.length ≤ S := by rw [hSdef]; exact length_le_encCardsIn cs
  have hzOUT' : State.get z OUT = encCardsOut (cs.map flatTCCCard_to_CCCard) := by
    rw [hzOUT, List.take_of_length_le hcsS]
  have heval : cardConvert.eval s0 = z := by
    show ((Cmd.op (.copy SCAN CARDS)) ;; _).eval s0 = _
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
      Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq, e8,
      hloop_eval]
  -- cost of the loop
  have hcostLoop : (Cmd.forBnd IDXO SCAN cardStep).cost u
      ≤ 1 + S * (12 * (S * S) + 102 * S + 110) + S * S := by
    have h := Cmd.cost_forBnd_le IDXO SCAN cardStep u
      (12 * (S * S) + 102 * S + 110) (CInv cs u) hbase
      (fun i st hi hM => (cardStep_step cs u S (le_of_eq hSdef.symm) i st hM).1)
      (fun i st hi hM => (cardStep_step cs u S (le_of_eq hSdef.symm) i st hM).2)
    rw [huSCAN, ← hSdef] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [heval]
    exact hzOUT'
  · rw [heval, hzframe OFFSET (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact huOFFSET
  · rw [heval, hzframe WIDTH (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact huWIDTH
  · intro r hr
    have h6 : (r : Nat) < 6 := hr
    have hge : ∀ k : Nat, 6 ≤ k → r ≠ k :=
      fun k hk => Nat.ne_of_lt (Nat.lt_of_lt_of_le h6 hk)
    rw [heval,
      hzframe r (hge 9 (by omega)) (hge 8 (by omega)) (hge 10 (by omega))
        (hge 11 (by omega)) (hge 12 (by omega)) (hge 13 (by omega))
        (hge 15 (by omega)) (hge 16 (by omega)) (hge 26 (by omega)),
      huframe r (hge 9 (by omega)) (hge 8 (by omega)) (hge 6 (by omega))
        (hge 7 (by omega))]
  · have hcost : cardConvert.cost s0
        = 1 + (S + 1) + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1
            + (1 + 1 + (Cmd.forBnd IDXO SCAN cardStep).cost u))))))) := by
      show ((Cmd.op (.copy SCAN CARDS)) ;; _).cost s0 = _
      simp only [Cmd.cost_seq, Cmd.cost_op]
      rw [e1, e2, e3, e4, e5, e6, e7, e8]
      simp only [Op.cost, hCARDS]
      rw [hSdef]
    rw [hcost]
    have hS2 : S * (12 * (S * S) + 102 * S + 110)
        = 12 * (S * S * S) + 102 * (S * S) + 110 * S := by ring
    show _ ≤ 12 * (S * S * S) + 105 * (S * S) + 115 * S + 30
    omega

/-! ## Structural fields (frame, `consLen`-freedom, op-supportedness) -/

theorem cardConvert_usesBelow : Cmd.UsesBelow cardConvert 27 := by
  simp [cardConvert, cardStep, halfMove, blockMove, CliqueRelTM.readNum,
    CliqueRelTM.cSkip, Cmd.UsesBelow, Op.UsesBelow, CARDS, OFFSET, WIDTH, OUT,
    SCAN, VALX, FLAG, IDXO, IDXR, CliqueRelTM.HEAD, CliqueRelTM.INBLK,
    CliqueRelTM.SKIPR]


/-! ## Budget arithmetic -/

private theorem convBudget_mono {a b : Nat} (h : a ≤ b) :
    convBudget a ≤ convBudget b := by
  unfold convBudget
  have h2 : a * a ≤ b * b := Nat.mul_le_mul h h
  have h3 : a * a * a ≤ b * b * b := Nat.mul_le_mul h2 h
  omega

private theorem convBudget_le_poly (n : Nat) :
    convBudget (2 * n) ≤ 800 * (n + 1) ^ 3 := by
  have ekey : convBudget (2 * n)
      = 96 * (n * n * n) + 420 * (n * n) + 230 * n + 30 := by
    unfold convBudget; ring
  have epoly : 800 * (n + 1) ^ 3
      = 800 * (n * n * n) + 2400 * (n * n) + 2400 * n + 800 := by ring
  omega

/-! ## The free witness -/

private instance : Nonempty FlatCC := ⟨flatCCNoInstance⟩

/-- **The reduction `flatTCC_to_flatCC` as a concrete layer program** — the
free `PolyTimeComputableLang` witness (template: `kSAT3_reductionLang`).
`decodeOut` inverts the injective 7-register output key. -/
noncomputable def flatTCC_reductionLang :
    PolyTimeComputableLang flatTCC_to_flatCC where
  c := cardConvert
  encodeIn := encodeIn
  decodeOut := fun s => Function.invFun encKey (extractKey s)
  cost_bound := fun n => 800 * (n + 1) ^ 3
  cost_bound_poly := by
    refine ⟨3, ⟨6400, 1, ?_⟩⟩
    intro n hn
    calc 800 * (n + 1) ^ 3
        ≤ 800 * (2 * n) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      _ = 6400 * n ^ 3 := by ring
  cost_bound_mono := fun a b h =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 3)
  encodeIn_size := fun C => by
    have h1 := encCardsIn_length_le C.cards
    have h2 := encFinal_length_le C.final
    have hC : encodable.size C
        = C.Sigma + encodable.size C.init + encodable.size C.cards
          + encodable.size C.final + C.steps + 1 := rfl
    show State.size [[], List.replicate C.Sigma 1, encNats C.init,
      encCardsIn C.cards, encFinal C.final, List.replicate C.steps 1] ≤ _
    simp only [State.size, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil, List.length_replicate, List.length_nil,
      encNats_length]
    omega
  computes := fun C => by
    obtain ⟨hOUT, hOFF, hWID, hFrame, -⟩ := cardConvert_run C.cards (encodeIn C) rfl
    show Function.invFun encKey (extractKey (cardConvert.eval (encodeIn C))) = _
    have hkey : extractKey (cardConvert.eval (encodeIn C))
        = encKey (flatTCC_to_flatCC C) := by
      simp only [extractKey]
      rw [hFrame SIGMA (by decide), hFrame INIT (by decide),
        hFrame FINAL (by decide), hFrame STEPS (by decide), hOUT, hOFF, hWID]
      rfl
    rw [hkey]
    exact Function.leftInverse_invFun encKey_injective _
  cost_le := fun C => by
    obtain ⟨-, -, -, -, hc⟩ := cardConvert_run C.cards (encodeIn C) rfl
    have hCle : encodable.size C.cards ≤ encodable.size C := by
      have hC : encodable.size C
          = C.Sigma + encodable.size C.init + encodable.size C.cards
            + encodable.size C.final + C.steps + 1 := rfl
      omega
    refine le_trans hc (le_trans (convBudget_mono ?_) (convBudget_le_poly _))
    have := encCardsIn_length_le C.cards
    omega
  output_size_le := fun C => by
    have h1 := flatTCC_to_flatCC_size_bound C
    have h2 : encodable.size C + 1 ≤ (encodable.size C + 1) ^ 3 :=
      Nat.le_self_pow (by norm_num) _
    have h3 : (encodable.size C + 1) ^ 3 ≤ 800 * (encodable.size C + 1) ^ 3 := by
      omega
    omega
  enc_bit := fun C => by
    intro reg hreg x hx
    simp only [encodeIn, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with h | h | h | h | h | h <;> subst h
    · cases hx
    · rw [List.eq_of_mem_replicate hx]
    · exact encNats_bit _ x hx
    · exact encCardsIn_bit _ x hx
    · exact encFinal_bit _ x hx
    · rw [List.eq_of_mem_replicate hx]
  regBound := 27
  usesBelow := cardConvert_usesBelow
  width_le := fun C => by
    show (encodeIn C).length ≤ 27
    simp [encodeIn]
  decode_agree := fun C m => by
    have hlen : (3 : Nat) < (encodeIn C).length := by simp [encodeIn]
    have hpad : State.get (encodeIn C ++ List.replicate m []) CARDS
        = encCardsIn C.cards := by
      show ((encodeIn C ++ List.replicate m [])[(3 : Nat)]?).getD [] = _
      rw [List.getElem?_append_left hlen]
      rfl
    have hpadget : ∀ r : Var, r < 6 →
        State.get (encodeIn C ++ List.replicate m []) r
          = State.get (encodeIn C) r := by
      intro r hr
      show ((encodeIn C ++ List.replicate m [])[r]?).getD []
          = ((encodeIn C)[r]?).getD []
      rw [List.getElem?_append_left (show r < (encodeIn C).length by
        simp only [encodeIn, List.length_cons, List.length_nil]
        omega)]
    obtain ⟨hOUT1, hOFF1, hWID1, hF1, -⟩ := cardConvert_run C.cards _ hpad
    obtain ⟨hOUT2, hOFF2, hWID2, hF2, -⟩ := cardConvert_run C.cards (encodeIn C) rfl
    show Function.invFun encKey _ = Function.invFun encKey _
    have hext : extractKey (cardConvert.eval (encodeIn C ++ List.replicate m []))
        = extractKey (cardConvert.eval (encodeIn C)) := by
      simp only [extractKey]
      rw [hOUT1, hOUT2, hOFF1, hOFF2, hWID1, hWID2,
        hF1 SIGMA (by decide), hF2 SIGMA (by decide),
        hF1 INIT (by decide), hF2 INIT (by decide),
        hF1 FINAL (by decide), hF2 FINAL (by decide),
        hF1 STEPS (by decide), hF2 STEPS (by decide),
        hpadget SIGMA (by decide), hpadget INIT (by decide),
        hpadget FINAL (by decide), hpadget STEPS (by decide)]
    rw [hext]

/-! ## Correctness of the UNGUARDED map -/

/-- Backward validity transfer: a valid flattening of the mapped `FlatCC` is a
valid flattening of the source `FlatTCC` (the map preserves `Sigma` and all
symbol content, so validity cannot be created by the map). This is what makes
the input guard of `FlatTCC_to_FlatCC_instance` unnecessary. -/
theorem flatTCC_to_flatCC_isValidFlattening (C : FlatTCC)
    (h : isValidFlattening (flatTCC_to_flatCC C)) :
    FlatTCC.isValidFlattening C := by
  obtain ⟨hinit, hfinal, hcards⟩ := h
  refine ⟨hinit, hfinal, ?_⟩
  intro card hcard
  have hcc : CCCard_ofFlatType (flatTCCCard_to_CCCard card) C.Sigma := by
    apply hcards
    show flatTCCCard_to_CCCard card ∈ (flatTCC_to_flatCC C).cards
    exact List.mem_map.mpr ⟨card, hcard, rfl⟩
  obtain ⟨hprem, hconc⟩ := hcc
  constructor
  · exact ⟨hprem card.prem.cardEl1 (by simp [flatTCCCard_to_CCCard, TCCCardP.toList]),
      hprem card.prem.cardEl2 (by simp [flatTCCCard_to_CCCard, TCCCardP.toList]),
      hprem card.prem.cardEl3 (by simp [flatTCCCard_to_CCCard, TCCCardP.toList])⟩
  · exact ⟨hconc card.conc.cardEl1 (by simp [flatTCCCard_to_CCCard, TCCCardP.toList]),
      hconc card.conc.cardEl2 (by simp [flatTCCCard_to_CCCard, TCCCardP.toList]),
      hconc card.conc.cardEl3 (by simp [flatTCCCard_to_CCCard, TCCCardP.toList])⟩

/-- **The unguarded map is a correct reduction**: `FlatTCCLang C ↔
FlatCCLang (flatTCC_to_flatCC C)`, with *no* `isValidFlattening` guard. On
valid inputs this is the existing window/cover equivalence
(`FlatTCC_to_FlatCC_poly`'s content); on invalid inputs both sides are false
(`flatTCC_to_flatCC_isValidFlattening`). -/
theorem flatTCC_to_flatCC_correct (C : FlatTCC) :
    FlatTCC.FlatTCCLang C ↔ FlatCCLang (flatTCC_to_flatCC C) := by
  constructor
  · rintro ⟨_, hflat, hlang⟩
    have hEq := flatTCC_to_flatCC_eq C hflat
    rw [hEq]
    refine ⟨flattenCC_wellformed
        (C := TCC_to_CC (FlatTCC.unflattenTCC C hflat)) (TCC_to_CC_lang _ hlang).1,
      ⟨isValidFlattening_flattenCC _, ?_⟩⟩
    simpa [unflatten_flattenCC] using
      TCC_to_CC_lang (FlatTCC.unflattenTCC C hflat) hlang
  · intro hFlat
    have hflat : FlatTCC.isValidFlattening C := by
      obtain ⟨-, hccflat, -⟩ := hFlat
      exact flatTCC_to_flatCC_isValidFlattening C hccflat
    have hEq := flatTCC_to_flatCC_eq C hflat
    rw [hEq] at hFlat
    rcases hFlat with ⟨_, hccflat, hlang⟩
    refine ⟨?_, ⟨hflat, ?_⟩⟩
    · simpa [FlatTCC.flatten_unflattenTCC C hflat] using
        FlatTCC.flattenTCC_wellformed (C := FlatTCC.unflattenTCC C hflat)
          (CC_to_TCC_lang (FlatTCC.unflattenTCC C hflat) (by
            simpa [unflatten_flattenCC] using hlang)).1
    · simpa using
        CC_to_TCC_lang (FlatTCC.unflattenTCC C hflat) (by
          simpa [unflatten_flattenCC] using hlang)

/-! ## The headline: the second live honest `⪯p'` on the real chain -/

/-- **`FlatTCC ⪯p' FlatCC`** — the second live honest TM-backed reduction on
the real chain (after `kSAT3_reducesPolyMO'`), and the first *sound-tail* step
carried by a concrete layer program.
Axiom-clean: `[propext, Classical.choice, Quot.sound]`. -/
theorem flatTCC_reducesPolyMO' : FlatTCC.FlatTCCLang ⪯p' FlatCCLang :=
  reducesPolyMO'_of_langFree flatTCC_reductionLang flatTCC_to_flatCC_correct

end FlatTCCFree
