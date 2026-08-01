import Complexity.Meta.AxiomGate
import Complexity.NP.SAT.CookLevin.CookLevinHonest
import Complexity.NP.SAT.CookLevin.Reductions.Front_to_S1_comp

set_option autoImplicit false

/-! # The honesty gate — the two audited functions, pinned BY `lake build`

`Complexity/SoundnessGate.lean` makes "no `sorry`, no bespoke axiom" a build
error. That is necessary and nowhere near sufficient: the deepest unsoundness
this project ever had (S1's if-on-the-answer reduction, S2's dummy bridges) was
`sorry`-free and axiom-clean. What makes the theorem *mean* something is risk
**S5** — that the reduction's work lives in its `Cmd` and not in its encoding —
and by the audit's structural result (FINDING AK) that reduces to **two
functions**:

> for a witness built by `PolyTimeComputableLang.comp`, `encodeIn` is the
> **leftmost** witness's and `decodeOut` is the **rightmost** witness's, and
> `toFrameworkWitness'` hands exactly those two to `ComputesBy`.

Those facts, and what the two functions are, used to be `rfl`s in
`probes/HonestyAuditProbe.lean` — which `lake build` never elaborates. So a
refactor of `comp`, of `toFrameworkWitness'`, or of a chain end's layout could
silently falsify the README while the build stayed green. This file closes that:
every theorem below is a `rfl` (or one rewrite), it is part of the default build
target, and it is gated.

## What this file does NOT do

It pins *what the two functions are*. It cannot pin that they are **honest** —
that `certState` is a faithful encoding of a bit string, that `Serialize cnf` is
a faithful CNF layout beyond `dec_enc`. Those are readings, and they are the
readings the README's reviewer checklist asks for. The point of this file is
that the list of things to read cannot grow behind your back.

The negative controls stay in `probes/HonestyAuditProbe.lean` (§6, §7, §7b) and
must **never** move here: they are constructions that are *supposed* to
typecheck, and a reader who found them in the library would rightly read them as
claims.
-/

namespace Complexity.HonestyGate

open Complexity.Lang

/-! ## 1 — the honesty surface is exactly two functions

All five seams and all six intermediate layouts drop out of the two fields
honesty depends on. Checked at both nesting levels. -/

section Composite
variable {X : Type} [encodable X] {Q : X → Prop}

/-- The composite's input layout is the **front** witness's, verbatim. -/
theorem composite_encodeIn (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).encodeIn
      = FrontWitness.encodeInQ W := rfl

/-- The composite's output decoder is the **last** witness's, verbatim. -/
theorem composite_decodeOut (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).decodeOut
      = FSATSATFree.decodeOut := rfl

theorem s1Composite_encodeIn :
    S1SATComp.s1_to_SAT_witness.encodeIn = HeadLayout.headEncodeIn := rfl

theorem s1Composite_decodeOut :
    S1SATComp.s1_to_SAT_witness.decodeOut = FSATSATFree.decodeOut := rfl

/-! ## 2 — the head: the input encoding IS the hypothesis's own layout

Since 2026-08-02 there is no register the reduction is handed and no formula to
judge: the front program counts its own input's cells (`FrontPieces.tallyCells`,
licensed by `InNPWitnessLangFreeSplit.sizeLB`). -/

theorem head_encodeIn_eq_encX (W : InNPWitnessLangFreeSplit Q) (x : X) :
    FrontWitness.encodeInQ W x = W.encX x := rfl

end Composite

/-! ## 3 — the head under the published statement: the raw input string

`NPhardStr` pins the layout to `certState`, so the composite reduction's
`ComputesBy.encode` is the raw bit string in one register, one cell per bit.
**This is the whole head-side audit.** -/

theorem str_encodeIn_eq_certState (Q : List Bool → Prop) (W : InNPWitnessStr Q)
    (cm km dm cs ks ds : Nat) (x : List Bool) :
    (FrontS1Comp.front_to_SAT_witness W.toInNPWitnessLangFreeSplit cm km dm cs ks ds).encodeIn x
      = certState x := W.encX_canonical x

/-- …and the canonical layout is one cell per bit, nothing else. -/
theorem certState_size (x : List Bool) : State.size (certState x) = x.length :=
  State.size_certState x

/-! ## 4 — the tail: the output decoder is a PARSER of one register

Not `Function.invFun` (unconstrained off the image), not a hand-written inverse:
`Serialize.dec` of the designated output register, with `dec_enc` proven. -/

theorem tail_decodeOut_is_parser (s : State) :
    FSATSATFree.decodeOut s
      = Serialize.decodeD ([] : cnf) (State.get s FSATSATFree.CNFOUT) := rfl

theorem tail_outputRegister : FSATSATFree.CNFOUT = 2 := rfl

/-- The parser is a genuine left inverse of the encoder — the law the whole tail
verdict rests on. -/
theorem tail_parser_left_inverse (N : cnf) :
    CnfSerialize.decCnf (EvalCnfCmd.encodeCnf N) = some N :=
  CnfSerialize.decCnf_encodeCnf N

/-! ## The gate -/

#assert_axioms_clean
  Complexity.HonestyGate.composite_encodeIn
  Complexity.HonestyGate.composite_decodeOut
  Complexity.HonestyGate.s1Composite_encodeIn
  Complexity.HonestyGate.s1Composite_decodeOut
  Complexity.HonestyGate.head_encodeIn_eq_encX
  Complexity.HonestyGate.str_encodeIn_eq_certState
  Complexity.HonestyGate.certState_size
  Complexity.HonestyGate.tail_decodeOut_is_parser
  Complexity.HonestyGate.tail_outputRegister
  Complexity.HonestyGate.tail_parser_left_inverse

end Complexity.HonestyGate
