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
        (fQ W (MmaxF W cm km dm) (MstepF W cs ks ds) x)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ :=
    FrontProgram.frontProgram_run (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds
      (encodeInQ W x) (State.size (W.encX x)) (BwidthQ_ge5 W) (xWidth_lt_BwidthQ W)
      (fun v hv => encSyms_bit _ v hv) (encodeInQ_tally W x) (encodeInQ_bits W x)
  rw [map_range_encX W x] at h2
  -- keep every big constant behind its own name
  have hfq : fQ W (MmaxF W cm km dm) (MstepF W cs ks ds) x
      = (MmachineQ W, 3 :: Compile.encodeRegs (W.encX x),
         MmaxF W cm km dm x, MstepF W cs ks ds x) := rfl
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

/-! The seam, the composed witness and the endpoint are all stated **over the
S1 program parameter** first (`…Of` / `…_of_S1`) and instantiated at the real
program afterwards. The `…Of` forms are axiom-clean, so `SAT_NPhard''_of_S1`
is a machine-checked statement of exactly what is left of Cook–Levin's
hardness half: *one* program meeting *three* contracts. -/

set_option maxHeartbeats 1000000 in
/-- **The fifth live seam** — the per-`Q` front into the composed
`FlatSingleTMGenNP → SAT` witness, on the frozen head layout. -/
noncomputable def front_to_SAT_seamOf (c : Cmd)
    (hcomputes : ∀ x : flatTM × List Nat × Nat × Nat,
      S1Program.s1Extract (c.eval (headEncodeIn x)) = S1Program.s1Key (S1Map.s1Map x))
    (huses : Cmd.UsesBelow c S1Program.s1RegBound)
    (hcost : S1Witness.S1CostBound c)
    (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    (WQ W cm km dm cs ks ds).SeamData
      (S1SATComp.s1_to_SAT_witnessOf c hcomputes huses hcost) where
  mfc := headScrub
  bridge := frontBridge W cm km dm cs ks ds
  decode_frame := fun s t hst => by
    show FSATSATFree.decodeOut s = FSATSATFree.decodeOut t
    unfold FSATSATFree.decodeOut
    have h57 : FSATSATFree.CNFOUT
        < (S1SATComp.s1_to_SAT_witnessOf c hcomputes huses hcost).regBound := by
      rw [S1SATComp.s1_to_SAT_witnessOf_regBound]
      decide
    rw [hst FSATSATFree.CNFOUT h57]
  mfcBound := fun _ => 110
  mfcBound_poly := inOPoly_const 110
  mfcBound_mono := fun _ _ _ => le_refl 110
  mfc_cost := fun _ => headScrub_cost _
  mfc_usesBelow := by
    refine Cmd.UsesBelow_mono ?_ headScrub_usesBelow
    exact le_trans (Nat.le_max_right S1Program.s1RegBound 57)
      (Nat.le_max_right (BwidthQ W + 10) _)

/-- **The whole honest chain as ONE free layer witness**: `Q → SAT`. -/
noncomputable def front_to_SAT_witnessOf (c : Cmd)
    (hcomputes : ∀ x : flatTM × List Nat × Nat × Nat,
      S1Program.s1Extract (c.eval (headEncodeIn x)) = S1Program.s1Key (S1Map.s1Map x))
    (huses : Cmd.UsesBelow c S1Program.s1RegBound)
    (hcost : S1Witness.S1CostBound c)
    (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    PolyTimeComputableLang
      (((FSATSATFree.fsatToSat
          ∘ (BinaryCCToFSAT.BinaryCC_to_FSAT_instance
            ∘ (FlatCC_to_BinaryCC_instance ∘ flatTCC_to_flatCC))) ∘ S1Map.s1Map)
        ∘ (fQ W (MmaxF W cm km dm) (MstepF W cs ks ds))) :=
  PolyTimeComputableLang.comp (WQ W cm km dm cs ks ds)
    (S1SATComp.s1_to_SAT_witnessOf c hcomputes huses hcost)
    (front_to_SAT_seamOf c hcomputes huses hcost W cm km dm cs ks ds)

/-- **`Q ⪯p' SAT` for every NP problem presented with a split free-line
verifier witness** — the whole chain, front and tail, as one composed live
honest `⪯p'`. -/
theorem front_to_SAT_reducesPolyMO'_of (c : Cmd)
    (hcomputes : ∀ x : flatTM × List Nat × Nat × Nat,
      S1Program.s1Extract (c.eval (headEncodeIn x)) = S1Program.s1Key (S1Map.s1Map x))
    (huses : Cmd.UsesBelow c S1Program.s1RegBound)
    (hcost : S1Witness.S1CostBound c)
    (W : InNPWitnessLangFreeSplit Q) :
    Q ⪯p' SAT := by
  obtain ⟨cm, km, dm, cs, ks, ds, hmax, hsteps⟩ := exists_front_constants W
  refine reducesPolyMO'_of_langFree
    (front_to_SAT_witnessOf c hcomputes huses hcost W cm km dm cs ks ds)
    (fun x => ?_)
  have hfront : FlatSingleTMGenNP
      (fQ W (MmaxF W cm km dm) (MstepF W cs ks ds) x) ↔ Q x :=
    fQ_correct W (MmaxF W cm km dm) (MstepF W cs ks ds) hmax hsteps x
  exact hfront.symm.trans
    (S1SATComp.s1_to_SAT_correct
      (fQ W (MmaxF W cm km dm) (MstepF W cs ks ds) x))

/-- **`NPhard'' SAT` from the three S1 contracts alone — AXIOM-CLEAN.**

This is the whole hardness half of Cook–Levin reduced to one interface: give
a `Cmd` that (1) lays `S1Program.s1Key (s1Map x)` on registers `1`–`5` of the
frozen head layout, (2) stays inside `s1RegBound = 48`, and (3) costs at most
`S1Map.s1Bound`. Nothing else is missing — not the front, not the tail, not
either seam. Note in particular that this path does **not** go through
`GenNP_is_hard.hasDeciderClassical`: the legacy hardness `sorry` is bypassed,
not inherited. -/
theorem SAT_NPhard''_of_S1 (c : Cmd)
    (hcomputes : ∀ x : flatTM × List Nat × Nat × Nat,
      S1Program.s1Extract (c.eval (headEncodeIn x)) = S1Program.s1Key (S1Map.s1Map x))
    (huses : Cmd.UsesBelow c S1Program.s1RegBound)
    (hcost : S1Witness.S1CostBound c) :
    NPhard'' SAT :=
  fun _Y _eY _Q hQ => by
    obtain ⟨W⟩ := hQ
    exact front_to_SAT_reducesPolyMO'_of c hcomputes huses hcost W

/-! ## …at the real program -/

/-- **The fifth live seam** at the real S1 program. -/
noncomputable def front_to_SAT_seam (W : InNPWitnessLangFreeSplit Q)
    (cm km dm cs ks ds : Nat) :
    (WQ W cm km dm cs ks ds).SeamData S1SATComp.s1_to_SAT_witness :=
  front_to_SAT_seamOf S1Program.s1Program S1Program.s1Program_computes
    S1Program.s1Program_usesBelow S1Witness.s1Program_costBound W cm km dm cs ks ds

/-- **The whole honest chain as ONE free layer witness**: `Q → SAT`. -/
noncomputable def front_to_SAT_witness (W : InNPWitnessLangFreeSplit Q)
    (cm km dm cs ks ds : Nat) :
    PolyTimeComputableLang
      (((FSATSATFree.fsatToSat
          ∘ (BinaryCCToFSAT.BinaryCC_to_FSAT_instance
            ∘ (FlatCC_to_BinaryCC_instance ∘ flatTCC_to_flatCC))) ∘ S1Map.s1Map)
        ∘ (fQ W (MmaxF W cm km dm) (MstepF W cs ks ds))) :=
  front_to_SAT_witnessOf S1Program.s1Program S1Program.s1Program_computes
    S1Program.s1Program_usesBelow S1Witness.s1Program_costBound W cm km dm cs ks ds

/-- **`Q ⪯p' SAT`** for every NP problem presented with a split free-line
verifier witness. -/
theorem front_to_SAT_reducesPolyMO' (W : InNPWitnessLangFreeSplit Q) :
    Q ⪯p' SAT :=
  front_to_SAT_reducesPolyMO'_of S1Program.s1Program S1Program.s1Program_computes
    S1Program.s1Program_usesBelow S1Witness.s1Program_costBound W

/-- **`NPhard'' SAT`** — the honest migrated hardness statement, over NP
problems presented with a split free-line verifier witness. Conditional only
on the three S1 contracts (see `SAT_NPhard''_of_S1`). -/
theorem SAT_NPhard'' : NPhard'' SAT :=
  SAT_NPhard''_of_S1 S1Program.s1Program S1Program.s1Program_computes
    S1Program.s1Program_usesBelow S1Witness.s1Program_costBound

end FrontS1Comp
