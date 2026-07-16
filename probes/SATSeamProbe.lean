import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_comp
import Complexity.NP.SAT.CookLevin.Reductions.FSAT_to_SAT_free

/-! # Probe: the `FSAT → SAT` seam (`flatTCC_to_FSAT_witness ⨾
fsatSAT_reductionLang`)

`#eval`-validates the THIRD seam's bridge before it is proven
(`Reductions/FSAT_to_SAT_comp.lean`): after the composed left witness
(`FlatTCC → FlatCC → BinaryCC → FSAT`) exits with `serF (formula)` in
register 0 (its `FOUT`), the candidate re-encoder `scrub3` (clear registers
1–26 — the right frame is only 27 wide, so the left residue ABOVE 27 needs no
scrubbing) must land register-exactly on `FSATSATFree.encodeIn` of the
intermediate formula. Also runs the whole composed 4-step pipeline end-to-end:
the final `CNFOUT`/`TALLY` must equal the pure map's `encodeCnf (fsatToSat f)`
where `f` is decoded (`decodeF`) from the machine's own intermediate stream —
no noncomputable clones needed.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/SATSeamProbe.lean` -/

namespace SATSeamProbe

open Complexity.Lang

/-- The candidate seam re-encoder (must mirror
`Reductions/FSAT_to_SAT_comp.lean`): clear every register `1 ≤ r < 27`;
register 0 (the left `FOUT` = the right `SERF`) carries through. -/
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

def mkCardT (a b c d e f : Nat) : TCCCard Nat := ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩

/-- Valid / invalid / degenerate instances (from `FSATSeamProbe`). -/
def T1 : FlatTCC := ⟨3, [0, 1, 2], [mkCardT 1 0 2 2 0 1], [[2, 1], [0]], 2⟩
def T2 : FlatTCC := ⟨2, [0, 5], [mkCardT 1 0 1 0 0 1], [[1]], 1⟩
def T3 : FlatTCC := ⟨2, [1, 0], [], [], 1⟩

/-- The composed `FlatTCC → FSAT` witness's exit state (its program is
`(cardConvert ;; (scrub ;; binConvert)) ;; (scrub2 ;; buildFSAT)`). -/
def satLeftExit (T : FlatTCC) : State :=
  BinaryCCFSATFree.buildFSAT.eval (BinaryCCFSATComp.scrub2.eval
    (FlatCCBinFree.binConvert.eval (FlatTCCBinComp.scrub.eval
      (FlatTCCFree.cardConvert.eval (FlatTCCFree.encodeIn T)))))

/-- The intermediate formula, decoded from the machine's OWN stream (reg 0). -/
def midF (T : FlatTCC) : Option formula :=
  BinaryCCFSATFree.decodeF (State.get (satLeftExit T) 0)

/-- **The bridge obligation**: after `scrub3`, all registers `< 27` (the RIGHT
frame) agree with `FSATSATFree.encodeIn` of the intermediate formula. -/
def checkBridge27 (T : FlatTCC) : Bool :=
  match midF T with
  | none => false
  | some f =>
      let mid := scrub3.eval (satLeftExit T)
      (List.range 27).all (fun r =>
        State.get mid r == State.get (FSATSATFree.encodeIn f) r)

/-- **End-to-end**: the whole composed 4-step pipeline's `CNFOUT`/`TALLY`
equal the pure map (`encodeCnf (fsatToSat f)` / its tally). -/
def checkEndToEnd (T : FlatTCC) : Bool :=
  match midF T with
  | none => false
  | some f =>
      let out := FSATSATFree.buildSAT.eval (scrub3.eval (satLeftExit T))
      State.get out FSATSATFree.CNFOUT
          == EvalCnfCmd.encodeCnf (FSATSATFree.fsatToSat f)
        && State.get out FSATSATFree.TALLY
          == List.replicate (FSATSATFree.fsatToSat f).length 1

#eval checkBridge27 T1  -- expect true (real tableau path, 1756-bit stream)
#eval checkBridge27 T2  -- expect true (guard path: falseFml)
#eval checkBridge27 T3  -- expect true (guard path: falseFml)
-- End-to-end only on the small streams: interpreting `buildSAT` on T1's
-- 1756-bit stream is out of `#eval` budget (the budget scan is cubic); T1's
-- end-to-end is covered by `checkBridge27` + the PROVEN `buildSAT_run`
-- (itself `#eval`-validated on real streams in `probes/FSATPreProbe.lean`).
#eval checkEndToEnd T2  -- expect true
#eval checkEndToEnd T3  -- expect true

-- Everything at once.
#eval [T1, T2, T3].all checkBridge27 && [T2, T3].all checkEndToEnd

end SATSeamProbe
