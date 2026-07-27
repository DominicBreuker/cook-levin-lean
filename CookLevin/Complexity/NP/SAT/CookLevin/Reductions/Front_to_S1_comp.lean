import Complexity.NP.SAT.CookLevin.Reductions.S1_to_FlatTCC_comp
import Complexity.NP.SAT.CookLevin.Reductions.FrontWitness

set_option autoImplicit false
set_option maxRecDepth 8000

/-! # C8-5 — the FIFTH seam: `W_Q ⨾ (S1 ⨾ the sound tail)` — `Q ⪯p' SAT`

(S3 migration, top-down; item 2 of the HANDOFF "NEXT TOP-DOWN" plan, and the
last structural interface of the whole chain.)

This file joins the per-`Q` front witness
(`Complexity.Lang.FrontWitness.WQ`, `Q → FlatSingleTMGenNP`) to the composed
`FlatSingleTMGenNP → SAT` witness of
`Reductions/S1_to_FlatTCC_comp.lean` at the `Cmd` level. With it,

```
Q ⪯p' FlatSingleTMGenNP ⪯p' FlatTCC ⪯p' FlatCC ⪯p' BinaryCC ⪯p' FSAT ⪯p' SAT
```

is ONE free layer witness and ONE `⪯p'`, and `NPhard'' SAT` follows.

## Why this seam is a pure scrub too

The interface is the **frozen head layout** `HeadLayout.headEncodeIn`
(`headRegBound = 5`, frozen 2026-07-18) and it was frozen precisely so that
this seam would be trivial: `FrontProgram.frontProgram_run` already delivers
registers `0`–`4` in exactly that layout, register for register. So `mfc`

* keeps registers `0`–`4` — they *are* `headEncodeIn (fQ … x)`;
* erases `[5, 57)` — `W_Q`'s scratch (which starts at `BwidthQ W ≥ 5`,
  including the extra unary size register the front witness's `encodeIn`
  carries at index `xWidth`) and everything up to the right composite's
  frame `57`.

Note the scrub reaches `57`, not `48`: the right witness here is the
*composite* `S1SATComp.s1_to_SAT_witness`, whose `regBound` is
`max s1RegBound 57 = 57`. That also means the endpoint is produced by two
`comp`s in the order `W_Q ⨾ (S1 ⨾ tail)` — the right-nested order, which
keeps every bridge a statement about a **plain** witness's `encodeIn` and
avoids the stacked-seam unfolding of `Reductions/BinaryCC_to_FSAT_comp.lean`.

## Risk note

`frontBridge` below is **axiom-clean** — it mentions neither `s1Program` nor
any composite, only `W_Q`'s program and the frozen layout. The endpoint
theorems inherit `sorryAx` solely through `S1Witness.s1_reductionLang`
(stage C's placeholder `def` and the open `cost_le`).
-/

namespace FrontS1Comp

open Complexity.Lang Complexity.Lang.FrontWitness Complexity.Lang.FrontLifting
open Complexity.Lang.FrontMachine HeadLayout S1SATComp

/-! ## The re-encoder -/

/-- C8-5's re-encoder: keep the frozen head layout's five registers, erase
everything from `headRegBound = 5` up to the right composite's frame `57`. -/
def headScrub : Cmd := clearRange 5 51

theorem headScrub_get (t : State) (r : Nat) :
    State.get (headScrub.eval t) r
      = if 5 ≤ r ∧ r ≤ 56 then [] else State.get t r := by
  unfold headScrub
  rw [clearRange_get]

theorem headScrub_cost (t : State) : headScrub.cost t ≤ 110 := by
  have h := clearRange_cost 51 5 t
  have : (headScrub.cost t) = (clearRange 5 51).cost t := rfl
  omega

theorem headScrub_usesBelow : Cmd.UsesBelow headScrub 57 :=
  clearRange_usesBelow 51 5 57 (by omega)

/-! ## The bridge -/

variable {X : Type} [encodable X] {Q : X → Prop}

/-- The frozen head layout, spelled out (a small `rfl` — do NOT let the
elaborator whnf `headEncodeIn (fQ …)` against a register value directly: the
machine constant `M_Q` sits inside, and defeq-checking through
`flattenTM (MQ …)` blows the heartbeat budget). -/
theorem headEncodeIn_eq (M : FlatTM) (s : List Nat) (a b : Nat) :
    headEncodeIn (M, s, a, b)
      = [[], encSyms (flattenTM M), encSyms s,
         List.replicate a 1, List.replicate b 1] := rfl

/-! ⚠ Read the five head registers off the *literal* five-element layout with
these (all `rfl` on opaque variables). Never let `exact` unify a register
value against `State.get (headEncodeIn (fQ …)) k` directly: the unifier
happily starts evaluating `flattenTM (MQ …)` — the whole per-`Q` front
machine — and burns the heartbeat budget. -/
private theorem get5_0 (a b c d e : List Nat) : State.get [a, b, c, d, e] 0 = a := rfl
private theorem get5_1 (a b c d e : List Nat) : State.get [a, b, c, d, e] 1 = b := rfl
private theorem get5_2 (a b c d e : List Nat) : State.get [a, b, c, d, e] 2 = c := rfl
private theorem get5_3 (a b c d e : List Nat) : State.get [a, b, c, d, e] 3 = d := rfl
private theorem get5_4 (a b c d e : List Nat) : State.get [a, b, c, d, e] 4 = e := rfl
private theorem len5 (a b c d e : List Nat) :
    ([a, b, c, d, e] : State).length = 5 := rfl

set_option maxHeartbeats 1000000 in
/-- **C8-5's bridge.** `frontProgram_run` gives registers `0`–`4` and they
*are* the frozen head layout of `fQ … x`; the scrub erases `[5, 57)`, where
the head layout has no registers at all. Axiom-clean. -/
theorem frontBridge (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat)
    (x : X) :
    AgreeBelow 57
      (headScrub.eval ((cQ W cm km dm cs ks ds).eval (encodeInQ W x)))
      (headEncodeIn
        (fQ W (fun x => MmaxF cm km dm x) (fun x => MstepF cs ks ds x) x)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ :=
    FrontProgram.frontProgram_run (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds
      (encodeInQ W x) (encodable.size x) (BwidthQ_ge5 W) (xWidth_lt_BwidthQ W)
      (fun v hv => encSyms_bit _ v hv) (encodeInQ_size_reg W x) (encodeInQ_bits W x)
  rw [map_range_encX W x] at h2
  -- keep every big constant behind its own name
  have hfq : fQ W (fun x => MmaxF cm km dm x) (fun x => MstepF cs ks ds x) x
      = (MmachineQ W, 3 :: Compile.encodeRegs (W.encX x),
         MmaxF cm km dm x, MstepF cs ks ds x) := rfl
  have hM : MconstQ W = encSyms (flattenTM (MmachineQ W)) := rfl
  rw [hM] at h1
  intro r hr
  rw [headScrub_get, hfq, headEncodeIn_eq]
  rcases Nat.lt_or_ge r 5 with h5 | h5
  · -- the frozen head layout, register for register
    rw [if_neg (by omega)]
    interval_cases r
    · rw [get5_0]; exact h0
    · rw [get5_1]; exact h1
    · rw [get5_2]; exact h2
    · rw [get5_3]; exact h3
    · rw [get5_4]; exact h4
  · -- `W_Q`'s scratch: erased here, absent there
    rw [if_pos ⟨h5, by omega⟩]
    refine (get_nil_of_len_le _ _ ?_).symm
    rw [len5]
    omega

/-! ## The seam, the composed witness, and the endpoint -/

set_option maxHeartbeats 1000000 in
/-- **The fifth live seam** — the per-`Q` front into the composed
`FlatSingleTMGenNP → SAT` witness, on the frozen head layout. -/
noncomputable def front_to_SAT_seam (W : InNPWitnessLangFreeSplit Q)
    (cm km dm cs ks ds : Nat) :
    (WQ W cm km dm cs ks ds).SeamData S1SATComp.s1_to_SAT_witness where
  mfc := headScrub
  bridge := frontBridge W cm km dm cs ks ds
  decode_frame := fun s t hst => by
    show FSATSATFree.decodeOut s = FSATSATFree.decodeOut t
    unfold FSATSATFree.decodeOut
    rw [hst FSATSATFree.CNFOUT (by decide)]
  mfcBound := fun _ => 110
  mfcBound_poly := inOPoly_const 110
  mfcBound_mono := fun _ _ _ => le_refl 110
  mfc_cost := fun _ => headScrub_cost _
  mfc_usesBelow := by
    refine Cmd.UsesBelow_mono ?_ headScrub_usesBelow
    exact le_trans (Nat.le_max_right S1Program.s1RegBound 57)
      (Nat.le_max_right (BwidthQ W + 9) _)

/-- **The whole honest chain as ONE free layer witness**: `Q → SAT`. -/
noncomputable def front_to_SAT_witness (W : InNPWitnessLangFreeSplit Q)
    (cm km dm cs ks ds : Nat) :
    PolyTimeComputableLang
      (((FSATSATFree.fsatToSat
          ∘ (BinaryCCToFSAT.BinaryCC_to_FSAT_instance
            ∘ (FlatCC_to_BinaryCC_instance ∘ flatTCC_to_flatCC))) ∘ S1Map.s1Map)
        ∘ (fQ W (fun x => MmaxF cm km dm x) (fun x => MstepF cs ks ds x))) :=
  PolyTimeComputableLang.comp (WQ W cm km dm cs ks ds)
    S1SATComp.s1_to_SAT_witness (front_to_SAT_seam W cm km dm cs ks ds)

/-- **`Q ⪯p' SAT` for every NP problem presented with a split free-line
verifier witness** — the whole chain, front and tail, as one composed live
honest `⪯p'`. -/
theorem front_to_SAT_reducesPolyMO' (W : InNPWitnessLangFreeSplit Q) :
    Q ⪯p' SAT := by
  obtain ⟨cm, km, dm, hmB⟩ := inOPoly_monomial_bound (maxSizeOf_poly W)
  obtain ⟨cs, ks, ds, hsB⟩ := inOPoly_monomial_bound (stepsOf_poly W)
  refine reducesPolyMO'_of_langFree (front_to_SAT_witness W cm km dm cs ks ds)
    (fun x => ?_)
  have hfront : FlatSingleTMGenNP
      (fQ W (fun x => MmaxF cm km dm x) (fun x => MstepF cs ks ds x) x) ↔ Q x :=
    fQ_correct W (fun x => MmaxF cm km dm x) (fun x => MstepF cs ks ds x)
      (fun x => hmB (encodable.size x))
      (fun x c _hrel hsize => le_trans (MQbudget_le W x c hsize) (hsB (encodable.size x)))
      x
  exact hfront.symm.trans
    (S1SATComp.s1_to_SAT_correct
      (fQ W (fun x => MmaxF cm km dm x) (fun x => MstepF cs ks ds x) x))

/-- **`NPhard'' SAT`** — the honest migrated hardness statement, over NP
problems presented with a split free-line verifier witness. -/
theorem SAT_NPhard'' : NPhard'' SAT :=
  fun _Y _eY _Q hQ => by
    obtain ⟨W⟩ := hQ
    exact front_to_SAT_reducesPolyMO' W

end FrontS1Comp
