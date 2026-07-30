import Complexity.Complexity.Deciders.EvalCnfSplit
import Complexity.NP.SAT.CookLevin.Reductions.Front_to_S1_comp

set_option autoImplicit false

/-! # The honest Cook–Levin headline — `NPcomplete'' SAT`

`NPcomplete'' SAT = NPhard'' SAT ∧ inNPLangFreeSplit SAT`, the statement the
whole free line was built for: hardness quantified over NP problems *presented
with a real verifier program* (`InNPWitnessLangFreeSplit`, so it cannot be
satisfied by the cheating encoder — standing risk #6), and membership *by* such
a witness.

**Both halves are DONE.** `CookLevin''` below is `sorry`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

* **hardness** — `FrontS1Comp.SAT_NPhard''` (2026-07-29-b): the C8 per-`Q`
  front, the S1 reduction program and the whole sound tail, composed by five
  live seams.
* **membership** — `EvalCnfSplit.SAT_inNPLangFreeSplit` (2026-07-30-b): the
  split layout, `xWidth = 3`, the characteristic-vector certificate relation
  and its linear bound, and the decoder `certDecode` with all three of its
  contracts proven (`CertBridge` from the `_run` lemma
  `EvalCnfSplit.certDecode_decodesAssgn`; cost and frame by `decide`).

The `_of_*` lemmas below are kept: they are the *program-generic* entry points
(a different certificate decoder plugs into `CookLevin''_of_decoder` without
touching anything else), and they are what made the endgame's remaining gap a
machine-checked statement rather than a believed one while it was still open
(standing risk #7).

⚠ The legacy `CookLevin : NPcomplete SAT` in `CookLevin.lean` still depends on
`sorryAx` through the legacy hardness front. That is a *legacy* fact, not a gap
in the mathematics — there is deliberately no `NPcomplete'' → NPcomplete` bridge
(the honest statement does not imply the vacuous one), and retiring the legacy
front is top-down demolition work. **Quote `CookLevin''`, not `CookLevin`.** -/

namespace CookLevinHonest

open Complexity.Lang

/-- **The honest Cook–Levin theorem, from any certificate decoder.** Given a
`Cmd` meeting the three decoder contracts, SAT is NP-complete in the honest
sense. AXIOM-CLEAN — nothing else is missing: not the hardness chain, not the
front, not either seam, not the verifier. -/
theorem CookLevin''_of_decoder (dec : Cmd) (rb : Nat) (hrb : 16 ≤ rb)
    (hbridge : EvalCnfSplit.CertBridge dec) (hcost : EvalCnfSplit.CertCostBound dec)
    (huses : Cmd.UsesBelow dec rb) : NPcomplete'' SAT :=
  ⟨FrontS1Comp.SAT_NPhard'',
    EvalCnfSplit.SAT_inNPLangFreeSplit_of dec rb hrb hbridge hcost huses⟩

/-- **The whole remaining Cook–Levin obligation, in ONE lemma.** At the pinned
candidate decoder `EvalCnfSplit.certDecode` the cost and frame contracts are
already proven (`by decide` through `Cmd.chk`), so the honest headline follows
from the decoder's `_run` lemma alone. AXIOM-CLEAN. -/
theorem CookLevin''_of_bridge
    (hbridge : EvalCnfSplit.CertBridge EvalCnfSplit.certDecode) :
    NPcomplete'' SAT :=
  ⟨FrontS1Comp.SAT_NPhard'', EvalCnfSplit.SAT_inNPLangFreeSplit_of_bridge hbridge⟩

/-- **The whole of Cook–Levin, honest, in ONE register equation.**

```
∀ N c, State.get (certDecode.eval (satEIn (N, c))) ASSGN = encodeAssgn (decodeBits c)
```

`certDecode` is an 11-op program (one `forBnd` over a cursor); `satEIn` is a
four-register literal. That equation — a single `_run` lemma — is all that stands
between this development and `NPcomplete'' SAT`. AXIOM-CLEAN. -/
theorem CookLevin''_of_decodesAssgn
    (h : EvalCnfSplit.DecodesAssgn EvalCnfSplit.certDecode) : NPcomplete'' SAT :=
  ⟨FrontS1Comp.SAT_NPhard'',
    EvalCnfSplit.SAT_inNPLangFreeSplit_of_decodesAssgn h⟩

/-- **COOK–LEVIN, honest and unconditional: `SAT` is NP-complete.**

`NPcomplete'' SAT = NPhard'' SAT ∧ inNPLangFreeSplit SAT`:

* every NP problem *presented with a real split verifier program* reduces to
  SAT by a real `Cmd`-backed poly-time reduction (`⪯p'`), and
* SAT itself is verified by a real `Cmd` program against a `List Bool`
  certificate inside a real polynomial cost bound.

`sorry`-free and axiom-clean. This — not the legacy `CookLevin` — is the
theorem this development proves. -/
theorem CookLevin'' : NPcomplete'' SAT :=
  ⟨FrontS1Comp.SAT_NPhard'', EvalCnfSplit.SAT_inNPLangFreeSplit⟩

/-- The hardness half, unbundled. -/
theorem SAT_NPhard'' : NPhard'' SAT := FrontS1Comp.SAT_NPhard''

/-- The membership half, unbundled. -/
theorem SAT_inNPLangFreeSplit : inNPLangFreeSplit SAT :=
  EvalCnfSplit.SAT_inNPLangFreeSplit

end CookLevinHonest
