import Complexity.NP.SAT.CookLevin.CookLevinHonest

set_option autoImplicit false

/-! # Cook–Levin — where the theorem lives

**The theorem is `CookLevinHonest.CookLevin'' : NPcomplete'' SAT`**
(`NP/SAT/CookLevin/CookLevinHonest.lean`), `sorry`-free and axiom-clean.

This file used to hold a second, *legacy* headline `CookLevin : NPcomplete SAT`,
transported along a chain of `⪯p` (`reducesPolyMO`) reductions from `GenNP`. It
was **deleted, not proved** (2026-07-30-c), together with everything that fed it:

| deleted | why |
|---|---|
| `CookLevin0` / `CookLevin` / `Clique_complete` and the `GenNP ⪯p … ⪯p SAT` chain | `⪯p` bounds only the reduction's *output size*, never its runtime, so `NPcomplete` is a vacuous notion — the honest `NPcomplete''` was built to replace it, and there is deliberately no `NPcomplete'' → NPcomplete` bridge |
| `Complexity/GenNP_is_hard.lean` (`NPhard_GenNP`, `hasDeciderClassical`) | `hasDeciderClassical` asserted a `DecidesBy` for *any* predicate. It was the last `sorryAx` on the legacy headline and it is **unclosable honestly**: closing it is exactly the cheat that makes `inTimePoly`/`inNP` true for every predicate (standing risk #6). Its honest replacement is `NPhard''`, which quantifies over `InNPWitnessLangFreeSplit` — NP problems presented with a real verifier program |
| `L_to_LM.lean`, `LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean`, `NP/TM/IntermediateProblems.lean` | the S2 bridges: a 1-state `bridgeMachine` with no transitions that accepts everything, so the TM-acceptance conjuncts carried no information. The `Cmd` layer is single-tape by construction, so there is no multi-tape detour left to bridge |
| `Simulators/MultiToSingle.lean` | dead code for the same reason (3 `sorry`s) |
| `Complexity/NP.lean`'s `red_inNP` | its `inTimePoly` half was a `sorry` closable only through the same cheat. The honest, live replacement is `Lang.red_inNP_of_langFree` |

Deleting all of it removed the development's last five `sorry`s. Nothing on the
`CookLevin''` path ever routed through any of them — see `probes/AxiomProbe.lean`.

The honest chain that replaced it:

```
Q ⪯p' FlatSingleTMGenNP ⪯p' FlatTCC ⪯p' FlatCC ⪯p' BinaryCC ⪯p' FSAT ⪯p' SAT
└─ C8 front ─┘└─ S1 ─┘└──────────────── the sound tail ───────────────────┘
```

for every `Q` presented with a split free-line verifier witness — one composed
`PolyTimeComputableLang` witness, five `SeamData`/`comp` seams, and
`FrontS1Comp.SAT_NPhard''`. -/
