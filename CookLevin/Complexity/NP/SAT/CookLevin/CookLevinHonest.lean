import Complexity.Complexity.Deciders.EvalCnfSplit
import Complexity.NP.SAT.CookLevin.Reductions.Front_to_S1_comp

set_option autoImplicit false

/-! # The honest Cook–Levin headline — `NPcomplete'' SAT`

`NPcomplete'' SAT = NPhard'' SAT ∧ inNPLangFreeSplit SAT`, the statement the
whole free line was built for: hardness quantified over NP problems *presented
with a real verifier program* (`InNPWitnessLangFreeSplit`, so it cannot be
satisfied by the cheating encoder — standing risk #6), and membership *by* such
a witness.

Its two halves are in very different states:

* **hardness — DONE.** `FrontS1Comp.SAT_NPhard''` is proven, `sorry`-free and
  axiom-clean (`[propext, Classical.choice, Quot.sound]`).
* **membership — one machine obligation left.**
  `EvalCnfSplit.SAT_inNPLangFreeSplit_of_bridge` reduces `inNPLangFreeSplit SAT`
  to a single `EvalCnfSplit.CertBridge EvalCnfSplit.certDecode`: the `_run` lemma
  of an 11-op program that re-encodes the raw certificate bits at register
  `ASSGN` into the live verifier's `encodeAssgn` layout. Everything else — the
  split layout, `xWidth`, the certificate relation and its polynomial bound, the
  decoder's cost (`by decide` through `Cmd.chk`), its frame, and all four
  composite bounds — is discharged.

So `CookLevin''_of_bridge` below is the **whole** remaining Cook–Levin
obligation, on the honest statement, in one lemma. It is axiom-clean, which is
what makes that claim machine-checked rather than believed (standing risk #7 —
the theorem quantifies over the missing proof instead of mentioning a
`sorry`-backed placeholder).

⚠ The legacy `CookLevin : NPcomplete SAT` in `CookLevin.lean` stays as it is
until the decoder lands; there is deliberately no `NPcomplete'' → NPcomplete`
bridge (the honest statement does not imply the vacuous one). -/

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

/-- The same, unbundled: `NPhard'' SAT` is already unconditional. -/
theorem SAT_NPhard'' : NPhard'' SAT := FrontS1Comp.SAT_NPhard''

end CookLevinHonest
