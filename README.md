# Cook–Levin in Lean 4

A Lean 4 formalisation targeting the **Cook–Levin theorem** (SAT is
NP-complete), structured as a port of the Coq development by Forster, Kunze,
Roth et al. (<https://github.com/uds-psl/cook-levin>, mirrored under `coqdoc/`).

**Work in progress — the theorem typechecks but is NOT yet a faithful proof.**
`CookLevin/Complexity/NP/SAT/CookLevin.lean` declares `theorem CookLevin :
NPcomplete SAT` and `lake build` accepts it, but the term is **conditional** on
both `sorry`-backed gaps and `sorry`-free *vacuous* definitions. Read
[`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md) for the plan and the full risk
register before working.

## Honest status (verified 2026-05)

| | |
|---|---|
| `lake build` | ✅ green (3356 jobs) |
| `#print axioms CookLevin` | **`[propext, sorryAx, Classical.choice, Quot.sound]`** — the headline theorem **does depend on `sorryAx`** (both the hardness and the in-NP halves reach a `sorry`). |
| `axiom` declarations | **0** (project policy: `def`+`sorry` over `axiom`) |
| Genuine `sorry`s on the proof path | ~31 (Group C — completion) |
| `sorry`-**free** but **vacuous** defs on the proof path | several (Group S — soundness: S1, S2, the size-0 hardness reduction) — invisible to `#print axioms` |
| Proof-path size | ~18K LOC under `CookLevin/` (a further ~15K parked, not built) |
| Estimated work remaining to a real, unconditional proof | **~15–25K LOC** (see ROADMAP) |

> **The `sorry` count is not the soundness metric.** The deepest unsoundness
> (S1/S2, and the size-only `⪯p`) is `sorry`-free and invisible to
> `#print axioms`. Closing every `sorry` would **not** by itself make
> `CookLevin` faithful. Track **Group S** (soundness) and **Group C**
> (completion) separately.

## What is sound vs. what is not

NP-hardness is transported from a universal NP source down to SAT along a chain
of `⪯p` (poly-time many-one) reductions:

```
GenNP ⪯p … ⪯p FlatSingleTMGenNP ⪯p FlatTCC ⪯p FlatCC ⪯p BinaryCC ⪯p FSAT ⪯p SAT
└──────────── front: NOT sound ────────────┘└──────────── tail: SOUND ───────────┘
```

**Sound (genuine mathematics, ~3K LOC, `sorry`-free, do not touch):** the tail
`FlatTCC → FlatCC → BinaryCC → FSAT → SAT` (window/cover equivalence, unary
block encoding, tableau CNF, a full Tseytin transform), plus `kSAT_to_SAT` and
`kSAT_to_FlatClique`. These reductions are real constructions; their
input-guarded `if isValidFlattening …` branches test a *decidable property of
the input* (legitimate), not the answer. The `FlatTM` model, the
`encodable`/`inOPoly` machinery, the `DecidesBy`/`inTimePoly` interface, and the
`composeFlatTM`/`loopTM` combinator family are also sound. Cook–Levin *after* a
TM run is encoded as a `FlatTCC` is essentially in place.

**Not sound — three independent reasons the theorem is currently vacuous:**

- **S3 (the enabling weakness, definitional).** `⪯p` (`reducesPolyMO`) is
  licensed only by `polyTimeComputable`, which bounds **output size**, not
  runtime (`NP.lean`, `PolyTimeComputableWitness.bound_valid`). The reduction
  function may even be noncomputable. So `NPhard`/`NPcomplete` as currently
  *defined* are too weak: the headline statement, even with every `sorry`
  closed, would assert a vacuous notion of NP-completeness. The honest target
  `polyTimeComputable'` (`Lang/PolyTime.lean`, `ComputesBy`: a real TM halting
  within a polynomial *time* bound) **is faithful** — confirmed — and extends
  the old witness, so retiring S3 is a strengthening, not a rewrite. But it
  forces every reduction to carry a real program (S1/S2 then *stop
  typechecking*).
- **S1 (front reduction).** `FlatSingleTMGenNP ⪯p FlatTCC`
  (`Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`) is literally
  `if (source is yes-instance) then yesInst else noInst`, where `yesInst` is an
  all-zeros 1-symbol tableau that **never simulates the source machine `M`**.
  Sorry-free but vacuous; licensed by S3. Real fix = the Cook 2D tableau.
- **S2 (bridges).** `LM_to_mTM` / `mTM_to_singleTapeTM` use a 1-state
  `bridgeMachine` with empty transitions that **accepts everything**; the
  TM-acceptance conjuncts carry no information. Sorry-free but vacuous.
- **Hardness foundation also reaches a `sorry`.** `NPhard_GenNP`
  (`GenNP_is_hard.lean`) builds its reduction with output-size bound `fun _ =>
  0` (vacuous over the size-0 `instEncodableDefault`) **and** relies on
  `hasDeciderClassical`, a flat `sorry` asserting a `DecidesBy` for *any*
  predicate. The in-NP half is conditional too: `SAT_inNP` routes through the
  layer verifier `evalCnfCmd`, whose `decides`/`cost_bound` are `sorry`.

## The strategy: a higher-level computable layer

Building verifiers/reductions directly as `FlatTM`s overran budget ~10× and was
abandoned (parked under `parked/`, ~15K LOC). The pivot: a small structured
while-language `Cmd`/`Op` with explicit **cost** semantics, compiled **once** to
`FlatTM` (`Compile`). Every downstream verifier/reduction is then a short DSL
program. This is the Lean analogue of the L-calculus the Coq port uses — and,
being single-tape by construction, it is also why the S2 multi-tape detour is
unnecessary.

The layer's structural unknowns are **probed**: per-primitive compilation (C1),
composition (C2), and the counted loop (C3) all have proven *combinators*
(`compileSeq_compose_physical`, `loopTM_run`, `bitTestTM`, and a ~1.6K-LOC
sorry-free gadget library: `appendAt_run`, `scanLeft_run`, `insertCarryTM_run`,
…). The S3 layer→framework bridge is built (`toFrameworkWitness'`,
`inNPLang`/`red_inNPLang`, the decider bridge `inNPLang_to_inNP`, `LangEncodable`
+ `map_fst`/`swap`/`map_snd`/`forBnd` toolkit), all sorry-free **modulo one
compiler obligation** (`Compile_run_physical` / `Compile_sound`, Risk C2).

**Caveat surfaced (do not under-estimate C2):** 10 of 12 `compileOp`s are still
`compiledCmd_default` stubs, and — sharper — **`compileOp_sound` is false as
stated**: its budget `Compile.overhead (State.size s + cost)` ignores the
register count, but `appendAtTM`'s cost grows with the tape length
`State.size s + #registers + 1` (witness: `replicate 6 []` has `State.size 0`,
budget `4`, but the op first halts at step 10). The fix is a tape-length budget
plus threading the program's `regBound`. Two new sorry-free, axiom-clean lemmas
(`Lang/Compile.lean`) de-risk this: `compileOp_appendOne_behavioural` (the
`encodeTape`/`decodeTape` seam composes with the gadget library) and
`compileOp_appendOne_zero_sound` (the corrected tape-length budget is
achievable). See ROADMAP Risk C2.

## Development methodology: skeleton-first, risk-driven

(do not deviate without reason — full rationale in the ROADMAP)

1. **Skeleton first** — the whole proof path compiles with `sorry`s before any
   single proof is closed; this exposes every downstream obligation.
2. **Refine the highest-risk gap next** (per the Risk register), not in phase
   order.
3. **Decompose `sorry`s, don't elaborate them** — each split is a structural
   decision that typechecks (right shape) or fails (gap found).
4. **Prefer `def` + `sorry` over `axiom`** (axiom count is a metric to minimise;
   currently 0). New results must be `#print axioms`-clean (only `propext` /
   `Quot.sound` / `Classical.choice`).
5. **Probe before committing engineering** — for a big unknown, run a time-boxed
   go/no-go probe and give a verdict (feasible / feasible-but-expensive /
   trigger-fallback).
6. **Build green between commits; record gaps in commit messages.**

## Repository layout

```
CookLevin/
├── ROADMAP.md                       -- strategy + ordered plan + Risk register (read first)
├── Complexity/
│   ├── Complexity/
│   │   ├── Definitions.lean         -- encodable, inOPoly, monotonic, instEncodableDefault (Part 0.1)
│   │   ├── MachineSemantics.lean    -- FlatTM, stepFlatTM, runFlatTM
│   │   ├── NP.lean                  -- DecidesBy, inTimePoly, ⪯p, NPhard, red_inNP (S3 lives here)
│   │   ├── TMPrimitives.lean        -- composeFlatTM / branchComposeFlatTM / loopTM (~4K LOC, sound)
│   │   └── Deciders/                -- SAT / FlatClique verifier interfaces (C7, sorry bodies)
│   ├── Lang/                        -- the layer: Syntax, Semantics, Compile (C1/C2/C6),
│   │   │                               Frame, PolyTime (S3/C4 bridges), gadgets (sound)
│   │   └── …
│   ├── Simulators/                  -- CookTableau (S1, real, 2 sorries); MultiToSingle (dead code)
│   ├── GenNP_is_hard.lean           -- NPhard_GenNP via hasDeciderClassical (C8 sorry)
│   ├── L_to_LM / LM_to_mTM / mTM_to_singleTapeTM.lean  -- bridges (S2, vacuous)
│   └── NP/
│       ├── SAT.lean / kSAT.lean / FSAT.lean / FlatClique.lean
│       ├── FSAT_to_SAT.lean         -- Tseytin (~700 LOC, sound)
│       └── SAT/CookLevin.lean + CookLevin/Reductions/ + Subproblems/
parked/                              -- paused hand-rolled work (~15K LOC, not built)
coqdoc/                              -- local mirror of the Coq port
```

## Building

`mathlib` is the only dependency. From the repo root:

```
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

First build from a clean checkout is slow (mathlib cache). Lake's `lean_lib`
root is `CookLevin/`, so `parked/` is not built. Axiom check (lean-lsp's LSP
cannot find `lake`, so use a scratch file):

```
env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean   # `#print axioms <name>`
```

## Where to look first

- **The plan and risks:** [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md).
- **Real mathematics:** `NP/SAT/CookLevin/Subproblems/FlatTCC.lean` and the
  `Reductions/FlatTCC_to_FlatCC.lean → … → BinaryCC_to_FSAT.lean` chain, then
  `NP/FSAT_to_SAT.lean`.
- **The framework:** `Complexity/NP.lean` (`⪯p`, `DecidesBy`, `red_inNP`).
- **The layer:** `Complexity/Lang/Compile.lean`, `Complexity/Lang/PolyTime.lean`.
- **What must be replaced:** the S1/S2/S3 entries in the ROADMAP Risk register.

## References

- Coq source: <https://github.com/uds-psl/cook-levin>; mirror `coqdoc/`.
- Roadmap / plan / Risk register: [`CookLevin/ROADMAP.md`](CookLevin/ROADMAP.md).
- Parked work: [`parked/README.md`](parked/README.md).
