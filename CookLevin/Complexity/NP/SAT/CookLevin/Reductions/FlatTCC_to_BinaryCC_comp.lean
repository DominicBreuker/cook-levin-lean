import Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC_free

set_option autoImplicit false

/-! # The FIRST LIVE `SeamData`: `flatTCC_reductionLang ⨾ flatCCBin_reductionLang`
(S3 migration, top-down target #2, item 2 — validates the settled `NPhard'`
endgame design on real witnesses)

This file joins the two live sound-tail witnesses at the `Cmd` level via
`PolyTimeComputableLang.SeamData`/`comp` — the honest replacement for
`⪯p'`-transitivity (settled design, 2026-07-02). It is the first concrete
instantiation of the chain-composition engine on real witnesses, giving one
composed witness for `FlatCC_to_BinaryCC_instance ∘ flatTCC_to_flatCC` and
the first COMPOSED live `⪯p'`:
`flatTCC_to_binaryCC_reducesPolyMO' : FlatTCC.FlatTCCLang ⪯p' BinaryCCLang`.

**The seam is cheap by design** (seam discipline, HANDOFF): the FlatCC→BinaryCC
witness's input layout was pinned to `flatTCC_reductionLang`'s EXIT frame
(shared registers 1/2/4/5 + outputs 6/7/8), so the re-encoder `mfc` is a pure
**scrub** — it clears the left witness's input-card residue (reg 3) and all
scratch (regs 9–26), making the state agree with `FlatCCBinFree.encodeIn` on
the whole 27-register frame. The bridge proof is a `cardConvert_run` frame
argument plus 18 unit-cost clears; the seam budget is the constant 40.
Design `#eval`-validated end-to-end in `probes/FlatCCBinProbe.lean`
(`checkBridge`/`checkComposite`). -/

namespace FlatTCCBinComp

open Complexity.Lang

/-- The seam re-encoder: scrub the flatTCC witness's card-input residue
(reg 3) and every scratch register (9–26). The surviving registers 0–8 are
exactly `FlatCCBinFree.encodeIn`'s layout of the intermediate `FlatCC`. -/
def scrub : Cmd :=
  Cmd.op (.clear 3) ;; Cmd.op (.clear 9) ;; Cmd.op (.clear 10) ;;
  Cmd.op (.clear 11) ;; Cmd.op (.clear 12) ;; Cmd.op (.clear 13) ;;
  Cmd.op (.clear 14) ;; Cmd.op (.clear 15) ;; Cmd.op (.clear 16) ;;
  Cmd.op (.clear 17) ;; Cmd.op (.clear 18) ;; Cmd.op (.clear 19) ;;
  Cmd.op (.clear 20) ;; Cmd.op (.clear 21) ;; Cmd.op (.clear 22) ;;
  Cmd.op (.clear 23) ;; Cmd.op (.clear 24) ;; Cmd.op (.clear 25) ;;
  Cmd.op (.clear 26)

/-- `scrub` as one nested-set state. -/
theorem scrub_eval (t : State) :
    scrub.eval t
      = ((((((((((((((((((t.set 3 []).set 9 []).set 10 []).set 11 []).set
          12 []).set 13 []).set 14 []).set 15 []).set 16 []).set 17 []).set
          18 []).set 19 []).set 20 []).set 21 []).set 22 []).set 23 []).set
          24 []).set 25 []).set 26 [] := by
  show (Cmd.op (.clear 3) ;; _).eval t = _
  rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op,
    Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
    Cmd.eval_op, Cmd.eval_op]
  simp only [Op.eval]

/-- `scrub` costs the constant 37 on every state (18 unit clears + 18 seams). -/
theorem scrub_cost (t : State) : scrub.cost t ≤ 40 := by
  show (Cmd.op (.clear 3) ;; _).cost t ≤ 40
  simp only [Cmd.cost_seq, Cmd.cost_op, Op.cost]
  omega

theorem scrub_usesBelow : Cmd.UsesBelow scrub 27 := by
  simp [scrub, Cmd.UsesBelow, Op.UsesBelow]

theorem scrub_noConsLen : Cmd.NoConsLen scrub := by
  simp only [scrub, Cmd.NoConsLen, Op.NotConsLen]
  trivial

theorem scrub_allOpsSupported : Cmd.AllOpsSupported scrub := by
  simp only [scrub, Cmd.AllOpsSupported, Op.IsSupported]
  trivial

/-- **The first live seam.** The bridge is a `cardConvert_run` frame argument:
after `cardConvert ;; scrub`, every register below 27 agrees with the
FlatCC→BinaryCC witness's own encoding of the intermediate instance. -/
noncomputable def flatTCC_to_binaryCC_seam :
    FlatTCCFree.flatTCC_reductionLang.SeamData
      FlatCCBinFree.flatCCBin_reductionLang where
  mfc := scrub
  bridge := fun C => by
    intro r hr
    show State.get (scrub.eval (FlatTCCFree.cardConvert.eval
        (FlatTCCFree.encodeIn C))) r
      = State.get (FlatCCBinFree.encodeIn (flatTCC_to_flatCC C)) r
    obtain ⟨hOUT, hOFF, hWID, hFrame, -⟩ :=
      FlatTCCFree.cardConvert_run C.cards (FlatTCCFree.encodeIn C) rfl
    rw [scrub_eval]
    set T := FlatTCCFree.cardConvert.eval (FlatTCCFree.encodeIn C) with hT
    have hOUT' : State.get T 8 = FlatTCCFree.encCardsOut
        (C.cards.map flatTCCCard_to_CCCard) := hOUT
    have hOFF' : State.get T 6 = [1] := hOFF
    have hWID' : State.get T 7 = [1, 1, 1] := hWID
    have h27 : r < 27 := hr
    interval_cases r
    -- 0–2: shared inputs, below the scrub and `cardConvert`'s frame
    · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
      rw [hFrame 0 (by decide)]
      rfl
    · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
      rw [hFrame 1 (by decide)]
      rfl
    · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
      rw [hFrame 2 (by decide)]
      rfl
    -- 3: the card-input residue, scrubbed
    · repeat first
        | rw [State.get_set_eq]
        | rw [State.get_set_ne _ _ _ _ (by decide)]
      rfl
    -- 4–5: shared inputs
    · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
      rw [hFrame 4 (by decide)]
      rfl
    · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
      rw [hFrame 5 (by decide)]
      rfl
    -- 6–8: the left witness's outputs (offset/width/cards)
    · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
      rw [hOFF']
      rfl
    · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
      rw [hWID']
      rfl
    · repeat rw [State.get_set_ne _ _ _ _ (by decide)]
      rw [hOUT']
      rfl
    -- 9–26: scratch, scrubbed to the right witness's empty registers
    all_goals
      repeat first
        | rw [State.get_set_eq]
        | rw [State.get_set_ne _ _ _ _ (by decide)]
    all_goals rfl
  decode_frame := fun s t hst => by
    show Function.invFun FlatCCBinFree.encKeyB (FlatCCBinFree.extractKeyB s)
      = Function.invFun FlatCCBinFree.encKeyB (FlatCCBinFree.extractKeyB t)
    have hext : FlatCCBinFree.extractKeyB s = FlatCCBinFree.extractKeyB t := by
      simp only [FlatCCBinFree.extractKeyB]
      rw [hst FlatCCBinFree.BOFF (by decide), hst FlatCCBinFree.BWID (by decide),
        hst FlatCCBinFree.BINIT (by decide), hst FlatCCBinFree.BCARDS (by decide),
        hst FlatCCBinFree.BFINAL (by decide), hst FlatCCBinFree.STEPS (by decide)]
    rw [hext]
  mfcBound := fun _ => 40
  mfcBound_poly := inOPoly_const 40
  mfcBound_mono := fun _ _ _ => le_refl 40
  mfc_cost := fun C => scrub_cost _
  mfc_usesBelow := scrub_usesBelow
  mfc_noConsLen := scrub_noConsLen
  mfc_allOpsSupported := scrub_allOpsSupported

/-- **The first composed live witness**: the whole
`FlatTCC → FlatCC → BinaryCC` prefix of the sound tail as ONE free layer
witness, produced by the chain-composition engine. -/
noncomputable def flatTCC_to_binaryCC_witness :
    PolyTimeComputableLang (FlatCC_to_BinaryCC_instance ∘ flatTCC_to_flatCC) :=
  PolyTimeComputableLang.comp FlatTCCFree.flatTCC_reductionLang
    FlatCCBinFree.flatCCBin_reductionLang flatTCC_to_binaryCC_seam

/-- **`FlatTCC ⪯p' BinaryCC`** — the first COMPOSED live honest `⪯p'`,
obtained from the two chain-step witnesses via `SeamData`/`comp` and ONE
application of the bridge (the settled `NPhard'` endgame pattern).
Axiom-clean: `[propext, Classical.choice, Quot.sound]`. -/
theorem flatTCC_to_binaryCC_reducesPolyMO' :
    FlatTCC.FlatTCCLang ⪯p' BinaryCCLang :=
  reducesPolyMO'_of_langFree flatTCC_to_binaryCC_witness
    (fun C => (FlatTCCFree.flatTCC_to_flatCC_correct C).trans
      (FlatCCBinFree.flatCC_to_binaryCC_correct (flatTCC_to_flatCC C)))

end FlatTCCBinComp
