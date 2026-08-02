import Complexity.NP.SAT.CookLevin.Reductions.Front_to_S1_comp
import Complexity.NP.SAT.CookLevin.Reductions.SAT_to_SATStr_free

set_option autoImplicit false

/-! # The SIXTH seam: the whole chain ⨾ `SAT → SATStr` — `NPcompleteStr SATStr`

Bottom-up item 1, second half. `SAT_to_SATStr_free.lean` gives the witness for
`satToStr : cnf → List Bool`; this file hangs it off the **tail** of the honest
chain and reads off

```
NPhardStr SATStr        (satStr_NPhardStr)
NPcompleteStr SATStr    (SATStr_NPcompleteStr)
```

— an NP-completeness statement with `List Bool` on **both** sides of the arrow.

## Why extending at the tail is a new obligation, and what discharges it

By FINDING AK the honesty surface of a `comp`-built witness is its **leftmost
`encodeIn`** and its **rightmost `decodeOut`**. Extending the chain at the tail
*moves the rightmost `decodeOut`*: it is no longer `FSATSATFree.decodeOut`
(`Serialize cnf`) but `SATToSATStr.decodeOut` (`Serialize (List Bool)`). That
new function is a fresh honesty obligation and it is discharged the way the
standing discipline says: by a `Serialize` instance, not a hand-written inverse
(`Lang/SerializeStr.lean`). `Complexity/HonestyGate.lean` pins it.

## What the seam has to know, and the one thing that was missing

`comp`'s `bridge` needs the left witness's **exit register content**, and
`PolyTimeComputableLang.computes` does not give it: it says
`Serialize.decodeD [] (get s CNFOUT) = N`, which is compatible with `get s
CNFOUT` being junk that happens to parse to `N`. The chain's own run lemma
(`FSATSATFree.buildSAT_run`) does give it — but only for the *innermost*
witness, and the composite's `.c` is four `comp`s deep.

`ExitsOnCNFOUT` below is that missing statement, and it **composes**: a seam
transports it from the right witness to the composite in one line
(`exitsOnCNFOUT_comp`), because `comp`'s `bridge` already says the composed
program reaches the right witness's own input layout. Four applications carry
`buildSAT_run` from the last sound-tail step out to the whole chain
(`front_exitsOnCNFOUT`). This is a genuinely reusable piece: **any** future
tail extension needs exactly this and nothing else.

⚠ `comp_exit` / `exitsOnCNFOUT_comp` / `lt_comp_regBound` are stated here rather
than in `Lang/PolyTime.lean` on purpose (project convention: copy first, factor
when a third consumer appears). They mention nothing specific to this chain
except `CNFOUT`; move them up when a second tail extension lands.

## The seam itself

The left composite exits with `encodeCnf N` on `CNFOUT = 2`
("Composed-chain layouts — PINNED", tail exit). The right witness's whole frame
is **one register** (`regBound = 1`), so the seam owes exactly one register and
`mfc` is a single `copy 0 2` — no scrub at all, by FINDING AE. This is the
cheapest of the six seams.
-/

namespace SATStrComp

open Complexity.Lang
open EvalCnfCmd (encodeCnf)

/-! ## The exit-layout property, and how it composes -/

/-- **The exit contract a tail extension needs**: after running, the witness's
program leaves the canonical CNF stream of its own output on `CNFOUT`.

Strictly stronger than `computes` (which only says the register *parses* to the
output) and it is what a seam's `bridge` consumes. -/
def ExitsOnCNFOUT {X : Type} [encodable X] {F : X → cnf}
    (V : PolyTimeComputableLang F) : Prop :=
  ∀ x, State.get (V.c.eval (V.encodeIn x)) FSATSATFree.CNFOUT = encodeCnf (F x)

/-- A composite's exit state agrees with the **right** witness's own exit state
on the right witness's whole frame. This is `comp`'s `bridge` pushed through
`Cmd.eval_agree` — the same step `comp.computes` takes, kept as a register-level
fact instead of being consumed by `decodeOut`. -/
theorem comp_exit {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    {f : X → Y} {g : Y → Z}
    (Wf : PolyTimeComputableLang f) (Wg : PolyTimeComputableLang g)
    (S : Wf.SeamData Wg) (x : X) (r : Var) (hr : r < Wg.regBound) :
    State.get ((Wf.comp Wg S).c.eval ((Wf.comp Wg S).encodeIn x)) r
      = State.get (Wg.c.eval (Wg.encodeIn (f x))) r := by
  show State.get ((Wf.c ;; (S.mfc ;; Wg.c)).eval (Wf.encodeIn x)) r = _
  rw [Cmd.eval_seq, Cmd.eval_seq]
  exact Cmd.eval_agree Wg.c Wg.regBound Wg.usesBelow (S.bridge x) r hr

/-- A composite's frame contains the right witness's. -/
theorem lt_comp_regBound {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    {f : X → Y} {g : Y → Z}
    (Wf : PolyTimeComputableLang f) (Wg : PolyTimeComputableLang g)
    (S : Wf.SeamData Wg) (r : Var) (hr : r < Wg.regBound) :
    r < (Wf.comp Wg S).regBound :=
  Nat.lt_of_lt_of_le hr (Nat.le_max_right _ _)

/-- **`ExitsOnCNFOUT` transports along a seam.** One line, and it is why the
whole chain's exit layout costs four `exact`s instead of an unfolding of a
four-deep composite program. -/
theorem exitsOnCNFOUT_comp {X Y : Type} [encodable X] [encodable Y]
    {f : X → Y} {g : Y → cnf}
    (Wf : PolyTimeComputableLang f) (Wg : PolyTimeComputableLang g)
    (S : Wf.SeamData Wg) (hg : ExitsOnCNFOUT Wg)
    (hr : FSATSATFree.CNFOUT < Wg.regBound) :
    ExitsOnCNFOUT (Wf.comp Wg S) :=
  fun x => (comp_exit Wf Wg S x FSATSATFree.CNFOUT hr).trans (hg (f x))

/-! ## …carried from `buildSAT_run` out to the whole chain -/

/-- The innermost fact: the last sound-tail step's own run lemma. -/
theorem fsat_exitsOnCNFOUT : ExitsOnCNFOUT FSATSATFree.fsatSAT_reductionLang :=
  fun f => (FSATSATFree.buildSAT_run f).1

theorem cnfout_lt_fsat : FSATSATFree.CNFOUT < FSATSATFree.fsatSAT_reductionLang.regBound := by
  show FSATSATFree.CNFOUT < FSATSATFree.FRAME
  decide

/-- …through the sound tail composite `FlatTCC → SAT`. -/
theorem tail_exitsOnCNFOUT : ExitsOnCNFOUT FSATSATComp.flatTCC_to_SAT_witness :=
  exitsOnCNFOUT_comp _ _ _ fsat_exitsOnCNFOUT cnfout_lt_fsat

theorem cnfout_lt_tail :
    FSATSATFree.CNFOUT < FSATSATComp.flatTCC_to_SAT_witness.regBound :=
  lt_comp_regBound _ _ _ _ cnfout_lt_fsat

/-- …through the S1 seam. -/
theorem s1_exitsOnCNFOUT : ExitsOnCNFOUT S1SATComp.s1_to_SAT_witness :=
  exitsOnCNFOUT_comp _ _ _ tail_exitsOnCNFOUT cnfout_lt_tail

theorem cnfout_lt_s1 : FSATSATFree.CNFOUT < S1SATComp.s1_to_SAT_witness.regBound :=
  lt_comp_regBound _ _ _ _ cnfout_lt_tail

section Front

variable {X : Type} [encodable X] {Q : X → Prop}

/-- **…and out to the whole honest chain.** The composite reduction for an
arbitrary NP problem `Q` exits with the canonical CNF stream of the SAT instance
it produced. -/
theorem front_exitsOnCNFOUT (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    ExitsOnCNFOUT (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds) :=
  exitsOnCNFOUT_comp _ _ _ s1_exitsOnCNFOUT cnfout_lt_s1

theorem cnfout_lt_front (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    FSATSATFree.CNFOUT < (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).regBound :=
  lt_comp_regBound _ _ _ _ cnfout_lt_s1

/-! ## The sixth seam -/

/-- The seam's re-encoder: move the CNF stream from the tail's output register
to the string witness's single register. No scrub — the right frame is one
register wide (FINDING AE). -/
def strMfc : Cmd := Cmd.op (.copy SATToSATStr.OUT FSATSATFree.CNFOUT)

theorem strMfc_get (s : State) :
    State.get (strMfc.eval s) SATToSATStr.OUT = State.get s FSATSATFree.CNFOUT := by
  show State.get (State.set s SATToSATStr.OUT (State.get s FSATSATFree.CNFOUT))
      SATToSATStr.OUT = _
  exact State.get_set_eq _ _ _

theorem strMfc_cost (s : State) :
    strMfc.cost s = (State.get s FSATSATFree.CNFOUT).length + 1 := rfl

set_option maxHeartbeats 1000000 in
/-- **The sixth live seam**: the whole chain into `SAT → SATStr`. -/
noncomputable def front_to_SATStr_seam (W : InNPWitnessLangFreeSplit Q)
    (cm km dm cs ks ds : Nat) :
    (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).SeamData
      SATToSATStr.satToStr_reductionLang where
  mfc := strMfc
  bridge := fun x r hr => by
    have hr1 : r < 1 := hr
    have hr0 : r = SATToSATStr.OUT := by
      show r = 0
      omega
    subst hr0
    rw [strMfc_get, front_exitsOnCNFOUT W cm km dm cs ks ds x]
    exact (SATToSATStr.encodeIn_get _).symm
  decode_frame := fun s t hst => by
    show SATToSATStr.decodeOut s = SATToSATStr.decodeOut t
    unfold SATToSATStr.decodeOut
    rw [hst SATToSATStr.OUT (by show (0 : Nat) < 1; omega)]
  mfcBound := fun n =>
    5 * (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).cost_bound n + 1
  mfcBound_poly :=
    inOPoly_add (inOPoly_mul (inOPoly_const 5)
      (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).cost_bound_poly)
      (inOPoly_const 1)
  mfcBound_mono := fun a b hab => by
    have h := (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).cost_bound_mono a b hab
    have h5 := Nat.mul_le_mul_left 5 h
    show 5 * _ + 1 ≤ 5 * _ + 1
    omega
  mfc_cost := fun x => by
    rw [strMfc_cost, front_exitsOnCNFOUT W cm km dm cs ks ds x]
    have h1 := EvalCnfCmd.encodeCnf_length
      ((FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).decodeOut
        ((FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).c.eval
          ((FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).encodeIn x)))
    rw [(FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).computes x] at h1
    have h2 := (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).output_size_le x
    have h3 := Nat.mul_le_mul_left 5 h2
    show _ + 1 ≤ 5 * _ + 1
    omega
  mfc_usesBelow := by
    have h0 : SATToSATStr.OUT
        < max (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).regBound
            SATToSATStr.satToStr_reductionLang.regBound :=
      Nat.lt_of_lt_of_le (show (0 : Nat) < 1 by omega) (Nat.le_max_right _ _)
    have h2 : FSATSATFree.CNFOUT
        < max (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).regBound
            SATToSATStr.satToStr_reductionLang.regBound :=
      Nat.lt_of_lt_of_le (cnfout_lt_front W cm km dm cs ks ds) (Nat.le_max_left _ _)
    exact ⟨h0, h2⟩

/-- **The whole honest chain as ONE free layer witness**: `Q → SATStr`. Six
seams, `List Bool` in and `List Bool` out. -/
noncomputable def front_to_SATStr_witness (W : InNPWitnessLangFreeSplit Q)
    (cm km dm cs ks ds : Nat) :=
  PolyTimeComputableLang.comp (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds)
    SATToSATStr.satToStr_reductionLang (front_to_SATStr_seam W cm km dm cs ks ds)

/-- **`Q ⪯p' SATStr`** for every NP problem presented with a split free-line
verifier witness. -/
theorem front_to_SATStr_reducesPolyMO' (W : InNPWitnessLangFreeSplit Q) :
    Q ⪯p' SATStr.SATStr := by
  obtain ⟨cm, km, dm, cs, ks, ds, hmax, hsteps⟩ := FrontWitness.exists_front_constants W
  refine reducesPolyMO'_of_langFree (front_to_SATStr_witness W cm km dm cs ks ds)
    (fun x => ?_)
  have hfront : FlatSingleTMGenNP
      (FrontLifting.fQ W (FrontWitness.MmaxF W cm km dm)
        (FrontWitness.MstepF W cs ks ds) x) ↔ Q x :=
    FrontLifting.fQ_correct W (FrontWitness.MmaxF W cm km dm)
      (FrontWitness.MstepF W cs ks ds) hmax hsteps x
  have hchain := S1SATComp.s1_to_SAT_correct
    (FrontLifting.fQ W (FrontWitness.MmaxF W cm km dm)
      (FrontWitness.MstepF W cs ks ds) x)
  exact (hfront.symm.trans hchain).trans
    (SATToSATStr.satStr_satToStr _).symm

end Front

/-! ## The endpoints -/

/-- **`NPhardStr SATStr`** — every NP string language reduces to `SATStr` by a
real `Cmd`-backed polynomial-time reduction. -/
theorem satStr_NPhardStr : NPhardStr SATStr.SATStr := by
  intro P hP
  obtain ⟨W⟩ := hP
  exact front_to_SATStr_reducesPolyMO' W.toInNPWitnessLangFreeSplit

/-- **`NPcompleteStr' SATStr`** — ★★ **THE STATEMENT TO QUOTE.** NP-completeness
with `List Bool` on both sides of the arrow, and with **both** conjuncts pinned
to the canonical layout.

Hardness is the whole chain with one more seam on its tail; membership is
`SATStr.satStrWitness` (2026-08-04), an `InNPWitnessStr` — so its input layout
is `certState x`, the raw bit string, fixed by the statement rather than chosen
by us.

The distinction from `SATStr_NPcompleteStr` below is not cosmetic. That one
states membership as `inNPLangFreeSplit`, a class whose witness still carries a
free layout `encX` and which is therefore inhabited by **every** string
language, undecidable ones included (`probes/HonestyAuditProbe.lean` §7c). Its
membership conjunct is true of everything and so says nothing; this one's does
not and is not. Found by the S8 audit, 2026-08-07. -/
theorem SATStr_NPcompleteStr' : NPcompleteStr' SATStr.SATStr :=
  ⟨satStr_NPhardStr, SATStr.inNPStr_SATStr⟩

/-- **`NPcompleteStr SATStr`** — the same theorem with the weaker membership
conjunct, kept because the earlier literature of this repository (README,
ROADMAP, `NonVacuity`) quotes it. Prefer `SATStr_NPcompleteStr'`. -/
theorem SATStr_NPcompleteStr : NPcompleteStr SATStr.SATStr :=
  NPcompleteStr'_to_NPcompleteStr SATStr_NPcompleteStr'

end SATStrComp
