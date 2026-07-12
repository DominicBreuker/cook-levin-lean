import Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_BinaryCC_comp
import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_free

set_option autoImplicit false

/-! # End-to-end probe for the `BinaryCC → FSAT` SEAM
(`Reductions/BinaryCC_to_FSAT_comp.lean`)

Validates the second live `SeamData` before proving it: run the composed
`FlatTCC → BinaryCC` witness program (`cardConvert ;; scrub ;; binConvert`),
apply the candidate seam re-encoder `scrub2` (clear everything `< 27` except
the pinned inputs 5/17–21), and check `AgreeBelow 57` against
`BinaryCCFSATFree.encodeIn` of the intermediate BinaryCC — the exact `bridge`
obligation of the seam.

The intermediate `FlatCC_to_BinaryCC_instance` is `noncomputable` only because
`isValidFlattening` carries no `Decidable` instance; `instClone` supplies one
via `validB_iff` so the whole check is `#eval`-able. -/

namespace FSATSeamProbe

open Complexity.Lang

/-- The candidate seam re-encoder (must mirror the one in
`Reductions/BinaryCC_to_FSAT_comp.lean`): clear every register `< 27` except
the pinned BinaryCC frame 5/17/18/19/20/21. -/
def scrub2 : Cmd :=
  Cmd.op (.clear 0) ;; Cmd.op (.clear 1) ;; Cmd.op (.clear 2) ;;
  Cmd.op (.clear 3) ;; Cmd.op (.clear 4) ;; Cmd.op (.clear 6) ;;
  Cmd.op (.clear 7) ;; Cmd.op (.clear 8) ;; Cmd.op (.clear 9) ;;
  Cmd.op (.clear 10) ;; Cmd.op (.clear 11) ;; Cmd.op (.clear 12) ;;
  Cmd.op (.clear 13) ;; Cmd.op (.clear 14) ;; Cmd.op (.clear 15) ;;
  Cmd.op (.clear 16) ;; Cmd.op (.clear 22) ;; Cmd.op (.clear 23) ;;
  Cmd.op (.clear 24) ;; Cmd.op (.clear 25) ;; Cmd.op (.clear 26)

/-- Computable clone of `FlatCC_to_BinaryCC_instance` (same `dite`, decidable
via `validB_iff`). -/
def instClone (C : FlatCC) : BinaryCC :=
  have : Decidable (isValidFlattening C) :=
    decidable_of_iff _ (FlatCCBinFree.validB_iff C)
  if h : isValidFlattening C then CC_to_BinaryCC (unflattenCC C h)
  else binaryCCNoInstance

def mkCardT (a b c d e f : Nat) : TCCCard Nat := ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩

/-- Valid instance (from `FlatCCBinProbe`). -/
def T1 : FlatTCC := ⟨3, [0, 1, 2], [mkCardT 1 0 2 2 0 1], [[2, 1], [0]], 2⟩

/-- Invalid instance (symbol `5 ≥ Sigma`) — must bridge onto the
no-instance's (all-`[]`) encoding. -/
def T2 : FlatTCC := ⟨2, [0, 5], [mkCardT 1 0 1 0 0 1], [[1]], 1⟩

/-- Extra valid instance: empty cards/final streams. -/
def T3 : FlatTCC := ⟨2, [1, 0], [], [], 1⟩

/-- The composed left witness's exit state (its program is
`cardConvert ;; (scrub ;; binConvert)`). -/
def leftExit (T : FlatTCC) : State :=
  FlatCCBinFree.binConvert.eval (FlatTCCBinComp.scrub.eval
    (FlatTCCFree.cardConvert.eval (FlatTCCFree.encodeIn T)))

/-- **The bridge obligation**: after `scrub2`, ALL registers `< 57` agree with
`BinaryCCFSATFree.encodeIn` of the intermediate BinaryCC. -/
def checkBridge57 (T : FlatTCC) : Bool :=
  let mid := scrub2.eval (leftExit T)
  (List.range 57).all (fun r =>
    State.get mid r
      == State.get (BinaryCCFSATFree.encodeIn (instClone (flatTCC_to_flatCC T))) r)

#eval checkBridge57 T1  -- expect true
#eval checkBridge57 T2  -- expect true
#eval checkBridge57 T3  -- expect true

-- Everything at once.
#eval [T1, T2, T3].all checkBridge57

end FSATSeamProbe
