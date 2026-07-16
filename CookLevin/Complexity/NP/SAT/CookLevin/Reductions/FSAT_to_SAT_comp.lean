import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_comp
import Complexity.NP.SAT.CookLevin.Reductions.FSAT_to_SAT_free

set_option autoImplicit false
set_option maxRecDepth 4000

/-! # The third live `SeamData`: `flatTCC_to_FSAT_witness ⨾
fsatSAT_reductionLang` — `FlatTCC ⪯p' SAT`

(S3 migration, top-down; the seam item of the HANDOFF "NEXT TOP-DOWN" plan —
the LAST tail seam.)

This file joins the composed `FlatTCC → FSAT` witness
(`BinaryCCFSATComp.flatTCC_to_FSAT_witness`, itself two stacked seams) with
the `FSAT → SAT` witness (`FSATSATFree.fsatSAT_reductionLang`) at the `Cmd`
level, giving the WHOLE sound tail
`FlatTCC → FlatCC → BinaryCC → FSAT → SAT` as ONE free layer witness and the
composed live `⪯p'`:
`flatTCC_to_SAT_reducesPolyMO' : FlatTCC.FlatTCCLang ⪯p' SAT`.

**The seam is the cheapest yet** (seam discipline, HANDOFF):
`fsatSAT_reductionLang.encodeIn f = [serF f]` was pinned to the left
composite's exit frame — its `FOUT` (register 0) *is* the right witness's
`SERF` (register 0) — so the re-encoder `mfc` is a pure scrub of registers
1–26. Unlike the previous seam, the RIGHT frame (27) is NARROWER than the
left one (57): the bridge only quantifies over registers `< 27`, so the left
residue in 27–56 needs no scrubbing at all (the previous seam's
wider-right-frame length argument is unneeded). Design `#eval`-validated
end-to-end in `probes/SATSeamProbe.lean` (`checkBridge27` on the real
tableau path + both guard paths, `checkEndToEnd` on the small streams). -/

namespace FSATSATComp

open Complexity.Lang
open BinaryCCToFSAT

/-- The seam re-encoder: clear every register `1 ≤ r < 27`. Register 0 (the
left `FOUT` = the right `SERF`) carries the serialized formula through; the
scrubbed registers land on the missing (`[]`-reading) remainder of
`FSATSATFree.encodeIn`'s one-register state. -/
def scrub3 : Cmd :=
  Cmd.op (.clear 1) ;; Cmd.op (.clear 2) ;; Cmd.op (.clear 3) ;;
  Cmd.op (.clear 4) ;; Cmd.op (.clear 5) ;; Cmd.op (.clear 6) ;;
  Cmd.op (.clear 7) ;; Cmd.op (.clear 8) ;; Cmd.op (.clear 9) ;;
  Cmd.op (.clear 10) ;; Cmd.op (.clear 11) ;; Cmd.op (.clear 12) ;;
  Cmd.op (.clear 13) ;; Cmd.op (.clear 14) ;; Cmd.op (.clear 15) ;;
  Cmd.op (.clear 16) ;; Cmd.op (.clear 17) ;; Cmd.op (.clear 18) ;;
  Cmd.op (.clear 19) ;; Cmd.op (.clear 20) ;; Cmd.op (.clear 21) ;;
  Cmd.op (.clear 22) ;; Cmd.op (.clear 23) ;; Cmd.op (.clear 24) ;;
  Cmd.op (.clear 25) ;; Cmd.op (.clear 26)

/-- `scrub3` as one nested-set state. -/
theorem scrub3_eval (t : State) :
    scrub3.eval t
      = (((((((((((((((((((((((((t.set 1 []).set 2 []).set 3 []).set 4
          []).set 5 []).set 6 []).set 7 []).set 8 []).set 9 []).set 10 []).set
          11 []).set 12 []).set 13 []).set 14 []).set 15 []).set 16 []).set 17
          []).set 18 []).set 19 []).set 20 []).set 21 []).set 22 []).set 23
          []).set 24 []).set 25 []).set 26 [] := by
  show (Cmd.op (.clear 1) ;; _).eval t = _
  rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_op]
  simp only [Op.eval]

/-- `scrub3` costs the constant 51 on every state (26 unit clears +
25 seams). -/
theorem scrub3_cost (t : State) : scrub3.cost t ≤ 60 := by
  show (Cmd.op (.clear 1) ;; _).cost t ≤ 60
  simp only [Cmd.cost_seq, Cmd.cost_op, Op.cost]
  omega

theorem scrub3_usesBelow : Cmd.UsesBelow scrub3 27 := by
  simp [scrub3, Cmd.UsesBelow, Op.UsesBelow]

set_option maxHeartbeats 1000000 in
/-- **The third live seam** — the LAST tail seam. The bridge pushes the
second seam's bridge through `buildFSAT` (`Cmd.eval_agree`), reads the exit
key off `buildFSAT_run` (register 0 = `serF` of the intermediate formula),
and scrubs registers 1–26; the right frame stops at 27, so the left residue
above it is out of scope. -/
noncomputable def fsat_to_SAT_seam :
    BinaryCCFSATComp.flatTCC_to_FSAT_witness.SeamData
      FSATSATFree.fsatSAT_reductionLang where
  mfc := scrub3
  bridge := fun C => by
    intro r hr
    have hr' : r < 27 := hr
    show State.get (scrub3.eval
        (BinaryCCFSATComp.flatTCC_to_FSAT_witness.c.eval
          (BinaryCCFSATComp.flatTCC_to_FSAT_witness.encodeIn C))) r
      = State.get (FSATSATFree.encodeIn
          (BinaryCC_to_FSAT_instance
            (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)))) r
    -- Unfold the composed left witness's program into its stages.
    have heval : BinaryCCFSATComp.flatTCC_to_FSAT_witness.c.eval
        (BinaryCCFSATComp.flatTCC_to_FSAT_witness.encodeIn C)
        = BinaryCCFSATFree.buildFSAT.eval (BinaryCCFSATComp.scrub2.eval
            (FlatTCCBinComp.flatTCC_to_binaryCC_witness.c.eval
              (FlatTCCBinComp.flatTCC_to_binaryCC_witness.encodeIn C))) := by
      show (FlatTCCBinComp.flatTCC_to_binaryCC_witness.c ;;
          (BinaryCCFSATComp.scrub2 ;; BinaryCCFSATFree.buildFSAT)).eval
          (FlatTCCBinComp.flatTCC_to_binaryCC_witness.encodeIn C) = _
      rw [Cmd.eval_seq, Cmd.eval_seq]
    -- The second seam's bridge, pushed through `buildFSAT`.
    have hAg : AgreeBelow BinaryCCFSATFree.regFrame
        (BinaryCCFSATFree.buildFSAT.eval (BinaryCCFSATComp.scrub2.eval
          (FlatTCCBinComp.flatTCC_to_binaryCC_witness.c.eval
            (FlatTCCBinComp.flatTCC_to_binaryCC_witness.encodeIn C))))
        (BinaryCCFSATFree.buildFSAT.eval
          (BinaryCCFSATFree.encodeIn
            (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)))) :=
      Cmd.eval_agree BinaryCCFSATFree.buildFSAT BinaryCCFSATFree.regFrame
        BinaryCCFSATFree.buildFSAT_usesBelow
        (BinaryCCFSATComp.binaryCC_to_FSAT_seam.bridge C)
    -- `buildFSAT`'s exit key at the literal register 0 (safe defeq
    -- ascription: `FOUT` unfolds).
    have h0 : State.get (BinaryCCFSATFree.buildFSAT.eval
        (BinaryCCFSATFree.encodeIn
          (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)))) 0
        = BinaryCCFSATFree.serF (BinaryCC_to_FSAT_instance
            (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C))) :=
      BinaryCCFSATFree.buildFSAT_run
        (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C))
    rw [heval, scrub3_eval]
    interval_cases r
    -- 0: the carried stream (the left FOUT = the right SERF)
    · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
      rw [hAg 0 (by decide), h0]
      rfl
    -- 1–26: scrubbed; the right encoding reads `[]` there (missing register)
    all_goals
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
  decode_frame := fun s t hst => by
    show FSATSATFree.decodeOut s = FSATSATFree.decodeOut t
    unfold FSATSATFree.decodeOut
    rw [hst FSATSATFree.CNFOUT (by decide)]
  mfcBound := fun _ => 60
  mfcBound_poly := inOPoly_const 60
  mfcBound_mono := fun _ _ _ => le_refl 60
  mfc_cost := fun _ => scrub3_cost _
  mfc_usesBelow := by
    refine Cmd.UsesBelow_mono ?_ scrub3_usesBelow
    show 27 ≤ max (max (max 27 27) BinaryCCFSATFree.regFrame) FSATSATFree.FRAME
    decide

/-- **The composed witness for the WHOLE sound tail
`FlatTCC → FlatCC → BinaryCC → FSAT → SAT`** as ONE free layer witness. -/
noncomputable def flatTCC_to_SAT_witness :
    PolyTimeComputableLang
      (FSATSATFree.fsatToSat
        ∘ (BinaryCC_to_FSAT_instance
          ∘ (FlatCC_to_BinaryCC_instance ∘ flatTCC_to_flatCC))) :=
  PolyTimeComputableLang.comp BinaryCCFSATComp.flatTCC_to_FSAT_witness
    FSATSATFree.fsatSAT_reductionLang fsat_to_SAT_seam

/-- **`FlatTCC ⪯p' SAT`** — the whole sound tail as ONE composed live honest
`⪯p'`, produced by three chained `SeamData`/`comp` instances and ONE
application of the bridge. Axiom-clean:
`[propext, Classical.choice, Quot.sound]`. -/
theorem flatTCC_to_SAT_reducesPolyMO' :
    FlatTCC.FlatTCCLang ⪯p' SAT :=
  reducesPolyMO'_of_langFree flatTCC_to_SAT_witness
    (fun C => (FlatTCCFree.flatTCC_to_flatCC_correct C).trans
      ((FlatCCBinFree.flatCC_to_binaryCC_correct (flatTCC_to_flatCC C)).trans
        ((BinaryCC_to_FSAT_instance_correct
          (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C))).trans
          (FSATSATFree.fsatToSat_correct
            (BinaryCC_to_FSAT_instance
              (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)))))))

end FSATSATComp
