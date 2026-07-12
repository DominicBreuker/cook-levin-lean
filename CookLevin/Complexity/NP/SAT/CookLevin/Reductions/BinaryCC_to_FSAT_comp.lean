import Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_BinaryCC_comp
import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_free

set_option autoImplicit false
set_option maxRecDepth 4000

/-! # The second live `SeamData`: `flatTCC_to_binaryCC_witness ⨾
binaryCCFSAT_reductionLang` — `FlatTCC ⪯p' FSAT`

(S3 migration, top-down; the seam item of the 2026-07-11 plan.)

This file joins the composed `FlatTCC → BinaryCC` witness
(`FlatTCCBinComp.flatTCC_to_binaryCC_witness`, itself the first live
`SeamData`/`comp` instance) with the `BinaryCC → FSAT` witness
(`BinaryCCFSATFree.binaryCCFSAT_reductionLang`) at the `Cmd` level, giving the
whole sound-tail prefix `FlatTCC → FlatCC → BinaryCC → FSAT` as ONE free layer
witness and the composed live `⪯p'`:
`flatTCC_to_FSAT_reducesPolyMO' : FlatTCC.FlatTCCLang ⪯p' FSAT`.

**The seam is cheap by design** (seam discipline, HANDOFF):
`binaryCCFSAT_reductionLang.encodeIn` was pinned to the BinaryCC exit frame
(inputs at regs 5 `steps`/17 `offset`/18 `width`/19 `init`/20 `cards`/21
`final`, in exactly `binConvert`'s output formats), so the re-encoder `mfc` is
a pure **scrub** of the left composite's residue: the intermediate FlatCC
inputs (regs 1/2/4/6/7/8) and all scratch (0/3, 9–16, 22–26). This is the
first seam whose RIGHT frame (57) is WIDER than the left one (27): registers
27–56 are handled by a length argument — the left composite never grows the
state past its 27-register frame (`Cmd.eval_length_le`), and `State.get` of a
missing register is `[]`, matching the all-`[]` upper frame of
`BinaryCCFSATFree.encodeIn`. Design `#eval`-validated end-to-end in
`probes/FSATSeamProbe.lean` (`checkBridge57`, valid + invalid + empty-stream
instances). -/

namespace BinaryCCFSATComp

open Complexity.Lang
open BinaryCCToFSAT

/-- The seam re-encoder: clear every register `< 27` except the pinned
BinaryCC input frame 5/17/18/19/20/21. The scrubbed registers land on the
all-`[]` remainder of `BinaryCCFSATFree.encodeIn`'s frame. -/
def scrub2 : Cmd :=
  Cmd.op (.clear 0) ;; Cmd.op (.clear 1) ;; Cmd.op (.clear 2) ;;
  Cmd.op (.clear 3) ;; Cmd.op (.clear 4) ;; Cmd.op (.clear 6) ;;
  Cmd.op (.clear 7) ;; Cmd.op (.clear 8) ;; Cmd.op (.clear 9) ;;
  Cmd.op (.clear 10) ;; Cmd.op (.clear 11) ;; Cmd.op (.clear 12) ;;
  Cmd.op (.clear 13) ;; Cmd.op (.clear 14) ;; Cmd.op (.clear 15) ;;
  Cmd.op (.clear 16) ;; Cmd.op (.clear 22) ;; Cmd.op (.clear 23) ;;
  Cmd.op (.clear 24) ;; Cmd.op (.clear 25) ;; Cmd.op (.clear 26)

/-- `scrub2` as one nested-set state. -/
theorem scrub2_eval (t : State) :
    scrub2.eval t
      = ((((((((((((((((((((t.set 0 []).set 1 []).set 2 []).set 3 []).set
          4 []).set 6 []).set 7 []).set 8 []).set 9 []).set 10 []).set
          11 []).set 12 []).set 13 []).set 14 []).set 15 []).set 16 []).set
          22 []).set 23 []).set 24 []).set 25 []).set 26 [] := by
  show (Cmd.op (.clear 0) ;; _).eval t = _
  rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_op]
  simp only [Op.eval]

/-- `scrub2` costs the constant 41 on every state (21 unit clears +
20 seams). -/
theorem scrub2_cost (t : State) : scrub2.cost t ≤ 44 := by
  show (Cmd.op (.clear 0) ;; _).cost t ≤ 44
  simp only [Cmd.cost_seq, Cmd.cost_op, Op.cost]
  omega

theorem scrub2_usesBelow : Cmd.UsesBelow scrub2 27 := by
  simp [scrub2, Cmd.UsesBelow, Op.UsesBelow]

/-- `State.get` of a register at or past the state's length is `[]`. -/
private theorem get_nil_of_len_le (s : State) (r : Var) (h : s.length ≤ r) :
    State.get s r = [] := by
  unfold State.get
  rw [List.getElem?_eq_none h]
  rfl

/-- `binConvert`'s exit key on its own input encoding IS the encoded
`FlatCC_to_BinaryCC_instance` — the register-level content of the right
bridge. (Extracted from `flatCCBin_reductionLang.computes`'s inline `hkey`;
same proof, kept local to avoid touching the witness file.) -/
private theorem binConvert_key (C : FlatCC) :
    FlatCCBinFree.extractKeyB
        (FlatCCBinFree.binConvert.eval (FlatCCBinFree.encodeIn C))
      = FlatCCBinFree.encKeyB (FlatCC_to_BinaryCC_instance C) := by
  obtain ⟨hBOFF, hBWID, hBINIT, hBCARDS, hBFINAL, hSTEPS, -, -⟩ :=
    FlatCCBinFree.binConvert_run C.Sigma C.offset C.width C.init C.cards
      C.final (FlatCCBinFree.encodeIn C) rfl rfl rfl rfl rfl rfl
  by_cases h : isValidFlattening C
  · have hok : FlatCCBinFree.okB C.Sigma C.init C.cards C.final = true :=
      (FlatCCBinFree.validB_iff C).mpr h
    rw [hok] at hBOFF hBWID hBINIT hBCARDS hBFINAL hSTEPS
    simp only [Bool.cond_true] at hBOFF hBWID hBINIT hBCARDS hBFINAL hSTEPS
    simp only [FlatCCBinFree.extractKeyB]
    rw [hBOFF, hBWID, hBINIT, hBCARDS, hBFINAL, hSTEPS]
    rw [FlatCC_to_BinaryCC_instance, dif_pos h]
    show _ = [List.replicate (C.Sigma * C.offset) 1,
      List.replicate (C.Sigma * C.width) 1,
      FlatCCBinFree.bitsNat (encodeString (unflattenList C.Sigma C.init h.1)),
      FlatTCCFree.encCardsOut (((unflattenCards C.Sigma C.cards h.2.2).map
        encodeCard).map FlatCCBinFree.cardNat),
      FlatTCCFree.encFinal ((encodeFinal (unflattenFinal C.Sigma C.final
        h.2.1)).map FlatCCBinFree.bitsNat),
      List.replicate C.steps 1]
    rw [FlatCCBinFree.bitsNat_encodeString, FlatCCBinFree.cardsNat_encodeCards,
      FlatCCBinFree.finalNat_encodeFinal, Nat.mul_comm C.Sigma C.offset,
      Nat.mul_comm C.Sigma C.width]
    rfl
  · have hok : FlatCCBinFree.okB C.Sigma C.init C.cards C.final = false := by
      rcases Bool.eq_false_or_eq_true
          (FlatCCBinFree.okB C.Sigma C.init C.cards C.final) with hb | hb
      · exact absurd ((FlatCCBinFree.validB_iff C).mp hb) h
      · exact hb
    rw [hok] at hBOFF hBWID hBINIT hBCARDS hBFINAL hSTEPS
    simp only [Bool.cond_false] at hBOFF hBWID hBINIT hBCARDS hBFINAL hSTEPS
    simp only [FlatCCBinFree.extractKeyB]
    rw [hBOFF, hBWID, hBINIT, hBCARDS, hBFINAL, hSTEPS,
      FlatCC_to_BinaryCC_instance, dif_neg h]
    rfl

set_option maxHeartbeats 1000000 in
/-- **The second live seam.** The bridge pushes the FIRST seam's bridge
through `binConvert` (`Cmd.eval_agree`), reads the exit key off
`binConvert_key`, scrubs the residue, and closes registers 27–56 with the
`Cmd.eval_length_le` length argument (the left composite never leaves its
27-register frame; a missing register reads `[]`).

⚠ Gotcha (cost a bisect): do NOT split `hkey` with `injection` — in this
context it whnf-TIMES-OUT symbolically executing the reduction programs
(`Cmd.run`/`Op.eval` at ~800K `Nat.rec` unfoldings). The
`simp only [List.cons.injEq, and_true]` + `obtain` route below is cheap. -/
noncomputable def binaryCC_to_FSAT_seam :
    FlatTCCBinComp.flatTCC_to_binaryCC_witness.SeamData
      BinaryCCFSATFree.binaryCCFSAT_reductionLang where
  mfc := scrub2
  bridge := fun C => by
    intro r hr
    have hr' : r < 57 := hr
    show State.get (scrub2.eval
        (FlatTCCBinComp.flatTCC_to_binaryCC_witness.c.eval
          (FlatTCCBinComp.flatTCC_to_binaryCC_witness.encodeIn C))) r
      = State.get (BinaryCCFSATFree.encodeIn
          (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C))) r
    -- Unfold the composed left witness's program into its three stages.
    have heval : FlatTCCBinComp.flatTCC_to_binaryCC_witness.c.eval
        (FlatTCCBinComp.flatTCC_to_binaryCC_witness.encodeIn C)
        = FlatCCBinFree.binConvert.eval (FlatTCCBinComp.scrub.eval
            (FlatTCCFree.flatTCC_reductionLang.c.eval
              (FlatTCCFree.flatTCC_reductionLang.encodeIn C))) := by
      show (FlatTCCFree.flatTCC_reductionLang.c ;; (FlatTCCBinComp.scrub ;;
          FlatCCBinFree.binConvert)).eval
          (FlatTCCFree.flatTCC_reductionLang.encodeIn C) = _
      rw [Cmd.eval_seq, Cmd.eval_seq]
    -- The first seam's bridge, pushed through `binConvert`.
    have hAg : AgreeBelow 27
        (FlatCCBinFree.binConvert.eval (FlatTCCBinComp.scrub.eval
          (FlatTCCFree.flatTCC_reductionLang.c.eval
            (FlatTCCFree.flatTCC_reductionLang.encodeIn C))))
        (FlatCCBinFree.binConvert.eval
          (FlatCCBinFree.encodeIn (flatTCC_to_flatCC C))) :=
      Cmd.eval_agree FlatCCBinFree.binConvert 27
        FlatCCBinFree.binConvert_usesBelow
        (FlatTCCBinComp.flatTCC_to_binaryCC_seam.bridge C)
    -- `binConvert`'s exit key on the intermediate FlatCC, per register.
    have hkey := binConvert_key (flatTCC_to_flatCC C)
    simp only [FlatCCBinFree.extractKeyB, FlatCCBinFree.encKeyB] at hkey
    simp only [List.cons.injEq, and_true] at hkey
    obtain ⟨hB17, hB18, hB19, hB20, hB21, hB5⟩ := hkey
    -- Literal-register restatements (`rw` matches registers syntactically).
    have h17 : State.get (FlatCCBinFree.binConvert.eval
        (FlatCCBinFree.encodeIn (flatTCC_to_flatCC C))) 17
        = List.replicate
            (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)).offset 1 := hB17
    have h18 : State.get (FlatCCBinFree.binConvert.eval
        (FlatCCBinFree.encodeIn (flatTCC_to_flatCC C))) 18
        = List.replicate
            (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)).width 1 := hB18
    have h19 : State.get (FlatCCBinFree.binConvert.eval
        (FlatCCBinFree.encodeIn (flatTCC_to_flatCC C))) 19
        = FlatCCBinFree.bitsNat
            (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)).init := hB19
    have h20 : State.get (FlatCCBinFree.binConvert.eval
        (FlatCCBinFree.encodeIn (flatTCC_to_flatCC C))) 20
        = FlatTCCFree.encCardsOut
            ((FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)).cards.map
              FlatCCBinFree.cardNat) := hB20
    have h21 : State.get (FlatCCBinFree.binConvert.eval
        (FlatCCBinFree.encodeIn (flatTCC_to_flatCC C))) 21
        = FlatTCCFree.encFinal
            ((FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)).final.map
              FlatCCBinFree.bitsNat) := hB21
    have h5 : State.get (FlatCCBinFree.binConvert.eval
        (FlatCCBinFree.encodeIn (flatTCC_to_flatCC C))) 5
        = List.replicate
            (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)).steps 1 := hB5
    -- The left composite never grows past its 27-register frame.
    have hlenT : (FlatCCBinFree.binConvert.eval (FlatTCCBinComp.scrub.eval
        (FlatTCCFree.flatTCC_reductionLang.c.eval
          (FlatTCCFree.flatTCC_reductionLang.encodeIn C)))).length ≤ 27 := by
      refine le_trans (Cmd.eval_length_le _ 27
        FlatCCBinFree.binConvert_usesBelow _) (max_le ?_ (le_refl 27))
      refine le_trans (Cmd.eval_length_le _ 27
        FlatTCCBinComp.scrub_usesBelow _) (max_le ?_ (le_refl 27))
      refine le_trans (Cmd.eval_length_le _ 27
        FlatTCCFree.flatTCC_reductionLang.usesBelow _) (max_le ?_ (le_refl 27))
      exact FlatTCCFree.flatTCC_reductionLang.width_le C
    rw [heval]
    rcases Nat.lt_or_ge r 27 with h27 | h27
    · -- On the left frame: scrubbed registers go to `[]`; the pinned
      -- 5/17–21 carry `binConvert`'s outputs.
      rw [scrub2_eval]
      interval_cases r
      -- 0–4: scrubbed
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      -- 5: steps (shared-layout input)
      · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
        rw [hAg 5 (by decide), h5]
        rfl
      -- 6–16: scrubbed
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      -- 17–21: the pinned BinaryCC outputs
      · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
        rw [hAg 17 (by decide), h17]
        rfl
      · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
        rw [hAg 18 (by decide), h18]
        rfl
      · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
        rw [hAg 19 (by decide), h19]
        rfl
      · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
        rw [hAg 20 (by decide), h20]
        rfl
      · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
        rw [hAg 21 (by decide), h21]
        rfl
      -- 22–26: scrubbed
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
      · repeat first
          | rw [State.get_set_eq]
          | rw [State.get_set_ne _ _ _ _ (by decide)]
        rfl
    · -- 27 ≤ r < 57: above the left frame — the state is too short, `get`
      -- reads `[]`, matching `encodeIn`'s all-`[]` upper frame.
      have hlenS : (scrub2.eval (FlatCCBinFree.binConvert.eval
          (FlatTCCBinComp.scrub.eval
            (FlatTCCFree.flatTCC_reductionLang.c.eval
              (FlatTCCFree.flatTCC_reductionLang.encodeIn C))))).length ≤ 27 :=
        le_trans (Cmd.eval_length_le _ 27 scrub2_usesBelow _)
          (max_le hlenT (le_refl 27))
      rw [get_nil_of_len_le _ _ (le_trans hlenS h27)]
      interval_cases r <;> rfl
  decode_frame := fun s t hst => by
    show BinaryCCFSATFree.decodeOut s = BinaryCCFSATFree.decodeOut t
    unfold BinaryCCFSATFree.decodeOut
    rw [hst BinaryCCFSATFree.FOUT (by decide)]
  mfcBound := fun _ => 44
  mfcBound_poly := inOPoly_const 44
  mfcBound_mono := fun _ _ _ => le_refl 44
  mfc_cost := fun _ => scrub2_cost _
  mfc_usesBelow := by
    refine Cmd.UsesBelow_mono ?_ scrub2_usesBelow
    show 27 ≤ max (max 27 27) BinaryCCFSATFree.regFrame
    decide

/-- **The composed witness for the whole sound-tail prefix
`FlatTCC → FlatCC → BinaryCC → FSAT`** as ONE free layer witness. -/
noncomputable def flatTCC_to_FSAT_witness :
    PolyTimeComputableLang
      (BinaryCC_to_FSAT_instance
        ∘ (FlatCC_to_BinaryCC_instance ∘ flatTCC_to_flatCC)) :=
  PolyTimeComputableLang.comp FlatTCCBinComp.flatTCC_to_binaryCC_witness
    BinaryCCFSATFree.binaryCCFSAT_reductionLang binaryCC_to_FSAT_seam

/-- **`FlatTCC ⪯p' FSAT`** — the sound tail down to FSAT as ONE composed live
honest `⪯p'`, produced by two chained `SeamData`/`comp` instances and ONE
application of the bridge. Axiom-clean:
`[propext, Classical.choice, Quot.sound]`. -/
theorem flatTCC_to_FSAT_reducesPolyMO' :
    FlatTCC.FlatTCCLang ⪯p' FSAT :=
  reducesPolyMO'_of_langFree flatTCC_to_FSAT_witness
    (fun C => (FlatTCCFree.flatTCC_to_flatCC_correct C).trans
      ((FlatCCBinFree.flatCC_to_binaryCC_correct (flatTCC_to_flatCC C)).trans
        (BinaryCC_to_FSAT_instance_correct
          (FlatCC_to_BinaryCC_instance (flatTCC_to_flatCC C)))))

end BinaryCCFSATComp
