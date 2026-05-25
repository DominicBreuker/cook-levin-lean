# Cook–Levin in Lean 4 — Roadmap

The strategy and **ordered plan** for `theorem CookLevin : NPcomplete SAT`.
Written for agents working on the project: it states where the proof stands,
what is known, and what to do next to make the theorem unconditional. This is
a living plan, not a history — findings are recorded only where they keep a
future agent from re-deriving a decision.

**Orientation.** The theorem typechecks but is **conditional**. The
combinatorial heart of Cook–Levin (a TM run → tableau → CNF → SAT) is real and
done. The *front* of the proof (universal NP source → single-tape TM) is a
compiling skeleton plus a few `sorry`-free but **vacuous** reductions. The plan
to make it real is the **computable layer**: a small while-language (`Cmd`)
with explicit cost semantics, compiled once to `FlatTM` (`Compile`), so every
verifier and reduction is a short DSL program instead of a hand-rolled Turing
machine.

**Next topic: Risk C9** (canonical layer encoding) — the one remaining design
prerequisite; see *The plan from here*.

---

## Status snapshot

| | |
|---|---|
| `lake build` | ✅ green |
| Project axioms | **0** (only `propext` / `Classical.choice` / `Quot.sound`) |
| Proof-path size | ~11K LOC under `CookLevin/` (a further ~14K parked, not built) |
| `sorry`s on the proof path | ~29, all `TODO(...)`-tagged (Group C) |
| `sorry`-**free** vacuous defs on the proof path | ≥ 4 (Risks S1/S2 — the deepest gaps; invisible to `#print axioms`) |
| Structural unknowns remaining | **none** — all probed; what's left is bounded engineering + one bounded design item (C9) |
| Headline | `CookLevin : NPcomplete SAT` typechecks, **conditional** on Group C **and** S1/S2/S3 |

> **The `sorry` count is not the soundness metric.** The deepest unsoundness
> (S1/S2) is `sorry`-free and invisible to `#print axioms`. Track **Group S**
> (soundness) and **Group C** (completion) separately; closing every `sorry`
> does **not** by itself make `CookLevin` unconditional.

---

## The proof path

```
GenNP                          universal NP source
  ⪯p LMGenNP                   L_to_LM.lean              (identity bridge)
  ⪯p LMtoMTMTarget             LM_to_mTM.lean            (DUMMY bridge — S2)
  ⪯p TMGenNP_fixed             mTM_to_singleTapeTM.lean  (DUMMY bridge — S2)
  ⪯p FlatSingleTMGenNP         CookLevin.lean
  ⪯p FlatTCC                   Reductions/FlatSingleTMGenNP_to_FlatTCC.lean
                                                         (IF-ON-THE-ANSWER — S1)
  ⪯p FlatCC ⪯p BinaryCC ⪯p FSAT ⪯p SAT/3SAT/FlatClique  ← SOUND, done
```

NP-hardness is transported from `GenNP` along this chain via `red_NPhard`,
giving `CookLevin : NPcomplete SAT` in `Complexity/NP/SAT/CookLevin.lean`.
`inNP SAT` additionally needs a real SAT verifier (the layer's `evalCnfCmd`, C7).

**Sound (genuine mathematics, ~3K LOC, sorry-free, do not touch):** the tail
`FlatTCC → FlatCC → BinaryCC → FSAT → SAT` (window/cover equivalence, unary
block encoding, tableau CNF, Tseytin), plus `kSAT_to_SAT`, `kSAT_to_FlatClique`.
The `FlatTM` model, the `encodable`/`inOPoly` machinery, the
`DecidesBy`/`inTimePoly` interface, and the `composeFlatTM` combinator family
are also sound. Cook–Levin *after* a TM run is encoded as a `FlatTCC` is
essentially in place.

**Not sound (the front, `GenNP → FlatTCC`):** dummy TM bridges (S2) and an
if-on-the-answer reduction (S1), both licensed by the size-only
`polyTimeComputable` (S3). These three are the targets of the plan below.

---

## What we know (validated foundations)

The layer pivot and the deepest soundness questions have been de-risked by
time-boxed go/no-go probes (methodology below). The findings:

- **The layer compiles — C1/C2/C3 validated.**
  - *C1 (per-`Op`):* primitives are hundreds of LOC, not ~50, but the cost
    front-loads into a reusable gadget library (`insertCarryTM`, the `scan*`
    family, `appendAtTM`) that amortises; `appendOne/Zero` compile end-to-end.
    Length-*decreasing* ops hit a tape-model wall (tape content never shrinks),
    resolved by the **sentinel alphabet** (`endMark = 3`, `sig = 4`, plus a
    leading sentinel for head-rewind).
  - *C2 (composition):* `compileSeq_compose_physical` — fragments compose under
    a **physical contract** (halt at `exit`, head rewound to `0`, tape =
    `encodeTape output`, exact step, no early halt). The contract, not just the
    gadget, is what `composeFlatTM_run` needs.
  - *C3 (`loopTM`):* the counted-loop combinator + full run lemma `loopTM_run`
    is ~500 LOC *marginal* on the composition machinery (vs ~1000 LOC/loop-site
    hand-rolled, paid once), sorry-free and axiom-clean. Use a **non-shrinking
    (marker-overwrite) counter** encoding.

- **S3 is retireable — probed feasible but expensive.** The size-only
  `polyTimeComputable` is the weakness that lets S1/S2 typecheck. The honest
  TM-backed witness now exists additively in `Lang/PolyTime.lean` (sorry-free
  modulo the assumed `Compile_sound`):
  - `PolyTimeComputableWitness'` **extends** the old witness, so
    `polyTimeComputable' f → polyTimeComputable f` is immediate — the upgrade
    is a pure *strengthening*, and every size-bound lemma in `NP.lean`
    (`reducesPolyMO_transitive`, `red_inNP`'s `polyCertRel` half) survives a
    migration verbatim.
  - The real bridge `PolyTimeComputableLang.toFrameworkWitness'` goes through
    **cleanly** (machine = `Compile W.c`, budget = `Compile.overhead`).
  - **Forcing function confirmed** (`s1_witness_forces_decider`): a TM-backed
    witness for an if-on-the-answer map yields a polynomial-cost *decider* for
    the NP source — so S1/S2 **stop typechecking** under the upgrade. The
    upgrade is real.
  - Difficulty concentrates in **composition**, which needs a shared encoding
    → **Risk C9** (see plan). `red_inNP` cannot be discharged additively (it is
    stated over the size-only `⪯p`); it is part of the migration.

- **S2 needs no simulator — probed.** The multi-tape→single-tape simulator
  (`Simulators/MultiToSingle.lean`) is a Coq-porting artifact with **zero
  footprint**: `TM σ n` is `abbrev`-ed to `FlatTM` (the tape count is an erased
  phantom — `TM_tapecount_phantom : TM Bool 2 = TM Bool 1` by `rfl`), the
  `*GenNP_fixed` predicates ignore the machine, and the bridge machine accepts
  everything (`bridgeMachine_accepts_any`). `LMGenNP` reduces *directly* to the
  single-tape target (`LMGenNP_to_TMGenNP_singleTM_direct`), skipping the mTM
  node. **Retiring S2 folds into C8** (bind the predicates to the single-tape
  layer decider); do **not** build a simulator. `MultiToSingle.lean` is dead
  code → park or delete.

- **S1 is feasible but expensive — probed.** The real Cook 2D tableau
  (`Simulators/CookTableau.lean`) is a genuine computable construction (no
  if-on-the-answer) with the constrained-case bijection proved. Estimate
  ~6–11K LOC, bijection-dominated. Findings: alphabet `|Σ|=(M.sig+1)(M.states+2)`;
  tableau size is **quartic** in `|Σ|` (the earlier cubic bound was false);
  the wildcard-free TCC card model forces `Θ(|Σ|³)` identity cards (a pervasive
  cost multiplier).

---

## The plan from here

Two honest destinations. The probes have shown the unconditional one (A) is
**open** — proceed there; (B) remains the documented escape hatch.

### Destination A — real, unconditional `CookLevin`

Ordered by dependency. Each step is bounded engineering except where noted.

1. **C9 — canonical layer encoding (next topic).** Give `Cmd` programs a
   shared per-type state encoding (a `LangEncodable`-style class with
   `decode ∘ encode = id` and register-layout lemmas) so that one program's
   output state *is* the next program's input state. This unblocks
   `PolyTimeComputableLang.comp`, `red_inNP_via_lang`, and `red_inNP` — all
   currently unstatable without it. `comp_computes_of_bridge` (in
   `Lang/PolyTime.lean`) already shows the rest is definitional once the
   encoding aligns. Bounded *design*, not research.

2. **Retire S3 — migrate `⪯p` to the TM-backed witness.** Replace
   `ReductionWitness.reduction_poly`'s `polyTimeComputable` with
   `polyTimeComputable'` (already built by the S3 probe; the strengthening
   lemma keeps the size-bound lemmas working). This is the soundness gate: it forces every
   reduction to carry a real computation. Ripple cost: the **sound tail** must
   each gain a `Cmd` — `flatTCC_to_flatCC` cheap (its `if isValidFlattening`
   guard is a *decidable input* check, expressible), `FlatCC_to_BinaryCC`
   medium, **`BinaryCC_to_FSAT` (Tseytin, `500n⁶`) the expensive item** (a
   ~1K-LOC `formula` builder re-expressed as a `Cmd`, likely needing new `Op`s
   — see C5).

3. **Finish the layer → `Compile_sound`.** Land the per-`Op` gadgets (C1) + the
   `compileForBnd` guard/decrement wiring (C3) + the bit-test tester (C6). Then
   the layer verifier `evalCnfCmd` (C7) gives `inNP SAT`.

4. **Real front reductions.** With S3 retired and the layer real: build the
   S1 Cook tableau (expensive-but-feasible) and the C8 universal-source decider
   (single-tape via `Lang.DecidesLang` — this **subsumes the old S2 simulator**).

5. **Encodable sweep (Part 0.1).** Replace the size-0 `instEncodableDefault` on
   every chain intermediate (TCC/CC/BinaryCC/formula/…) with a real
   `encodable.size`. Required because over a size-0 type even
   `toFrameworkWitness'` is vacuous (`bound 0`). Pervasive but mechanical.

**Cost shape.** Post-C1/C2/C3 and the S3 bridge, everything is *bounded*
engineering except the S1 tableau (expensive-but-feasible) and the
Tseytin-as-`Cmd` tail item. No remaining step is a structural unknown.

### Destination B — honest conditional theorem (fallback)

If C9 or the S3 migration's tail ripple proves intractable for a side project,
state `CookLevin` conditionally on a **documented axiomatic `inTimePoly` / `⪯p`
interface**, keep the sound combinatorial tail, and stop. The code is ~80%
there for this scope. Trigger if step 1 or 2 overruns its estimate ~3×.

---

## Risk register

Two groups. **Group S** (soundness) determines *what the conditional theorem
currently means* — several entries are `sorry`-free. **Group C** (completion)
is the compiling-skeleton engineering. Refine the highest-ranked open item next.

### Group S — soundness gaps (mostly `sorry`-free)

| # | Gap | Location | Status / what closing it needs |
|---|-----|----------|--------------------------------|
| **S3** | `polyTimeComputable` bounds **output size only** — the enabling weakness that lets S1/S2 typecheck. | `Complexity/NP.lean`, `Lang/PolyTime.lean` | **Probed: feasible but expensive.** Honest witness `PolyTimeComputableWitness'` + bridge `toFrameworkWitness'` built (sorry-free modulo `Compile_sound`); forcing function confirmed. Execute via plan steps 1–2: needs **C9**, then migrate `⪯p`. |
| **S1** | **if-on-the-answer reduction** `FlatSingleTMGenNP ⪯p FlatTCC` (`if yes-inst then yesInst else noInst`). Deepest unsoundness. | `Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`, `.../TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean` | **Probed: feasible but expensive (~6–11K LOC).** Real fix = the Cook 2D tableau (`Simulators/CookTableau.lean`). Gated on S3 (dead until then) — plan step 4. |
| **S2** | **dummy TM bridges** — `bridgeMachine` discards `M`; `*GenNP_fixed` ignore `M`. | `LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean`, `TMGenNP_fixed_mTM.lean` | **Probed: no simulator needed** (Coq-porting artifact; tape count erased; predicates ignore `M`). Fix = collapse the phantom bridges and bind the predicates to the single-tape layer decider → **folds into C8**. Gated on S3. |
| **S4** | **orphan constructions.** | `Simulators/CookTableau.lean`, `Simulators/MultiToSingle.lean` | `cookTableau` (real, 2 `sorry`s): wire into S1 after S3 (plan step 4). `multiToSingle` (3-`sorry` stub): **dead code** per the S2 probe → park/delete. |

**Companion (Part 0.1) — a hard requirement.** `instEncodableDefault`
(`Definitions.lean`) gives `size = 0` to any type lacking an explicit
`encodable`. Over a size-0 type even the real `toFrameworkWitness'` is vacuous
(`≤ bound 0`), so retiring S3 in earnest requires real `encodable.size`
instances on every chain intermediate. Plan step 5.

### Group C — completion risks (the compiling skeleton)

| # | Gap | Status |
|---|-----|--------|
| **C9** | **canonical layer encoding** (surfaced by the S3 probe). `PolyTimeComputableLang.encodeIn`/`decodeOut` are free functions, so layer composition cannot be stated. Needs a per-type `LangEncodable` class. | **Open — the next topic.** Bounded design; `comp_computes_of_bridge` isolates exactly what's missing. Prerequisite for C4-composition, `red_inNP`, and the S3 migration. |
| **C4** | **layer → framework bridge** (`Lang/PolyTime.lean`'s 4 bridges, `NP.lean`'s `red_inNP`). | **Bridge B done** (`toFrameworkWitness'`, sorry-free modulo `Compile_sound`). The composition bridges (`comp`, `red_inNP_via_lang`) and `red_inNP` remain `sorry`, blocked on **C9** (not on `Compile_sound`). |
| **C1** | **per-`Op` compilation** (`compileOp` + `compileOp_sound`). | ✅ **validated.** Remaining: physical `compileOp_sound` per op + length-decreasing ops (use `endMark` sentinel). Bounded eng (~1.5–2.5K LOC for all 8 ops). |
| **C2** | **composition** (`compileSeq_sound`). | ✅ **validated** (`compileSeq_compose_physical`). Bounded eng. |
| **C3** | **`loopTM` counted loop** (`compileForBnd` + `_sound`). | ✅ **validated** (`loopTM` + `loopTM_run`, sorry-free). Remaining: guard + marker-overwrite decrement gadget, wire `compileForBnd`, instantiate `loopTM_run`. Bounded eng. |
| **C5** | **DSL expressiveness** — `evalCnfCmd` / the Tseytin-as-`Cmd` map (plan step 2) want a guarded loop and a constant-comparison primitive. | Add primitives only when one materially shortens a verifier/reduction (each new `Op` = another soundness proof). |
| **C6** | **`compileIfBit` tester** — structure done (`branchComposeFlatTM` + `joinTwoHalts`); the real bit-test + `compileIfBit_sound` remain. | Same flavour as C1. |
| **C7** | **verifier bodies** — `evalCnfCmd` (SAT), `cliqueRelCmd` (`Deciders/`). | DSL engineering; gated on C3+C5, dead until C4 makes the layer→`DecidesBy` bridge real. Plan step 3. |
| **C8** | **real `NPhard_GenNP`** (`hasDeciderClassical`, `GenNP_is_hard.lean`). | Last proof-path `sorry`; the universal-source decider, single-tape via `Lang.DecidesLang` (subsumes S2). Needs C4. Plan step 4. |

---

## How we work — skeleton-first, risk-driven

The methodology, learned the hard way in the May 2026 pivot (the hand-rolled
Part 2 blew up ~10× because structural issues were invisible until attempted).
**Do not deviate without an explicit reason.**

1. **Skeleton first, then refine.** The whole proof path compiles (with
   `sorry`s) before any single proof is closed. A compiling skeleton exposes
   every downstream obligation; an isolated proof exposes nothing.
2. **Refine the highest-risk gap next** (per the Risk register), not in phase
   order. Each refinement either validates a committed shape or surfaces a gap.
3. **Decompose `sorry`s, don't elaborate them.** Split a big `sorry` into
   focused sub-`sorry`s; each split is a structural decision that typechecks
   (right shape) or fails (gap found).
4. **Prefer concrete `def` + `sorry` over `axiom`.** Axiom count is a metric to
   minimise (currently 0).
5. **Probe before committing engineering.** For a big unknown, run a time-boxed
   go/no-go probe (assume lower layers, validate the structure additively,
   measure, give a verdict: feasible / feasible-but-expensive / trigger-fallback).
   C1/C2/C3, S1, S3, and S2 all followed this.
6. **Build green between commits; record gaps in commit messages**, not private
   notes.

---

## Why the layer (and why not hand-rolled TMs)

Building a useful algorithm directly from `FlatTM`s, even with good
combinators, ran ~10× over budget; continuing projected Parts 2–6 at
~100–150K LOC. The lessons (for anyone tempted to hand-roll again):

1. **Per-state lemmas don't amortise across primitives** — each primitive needs
   its own step/scan/run lemmas. The layer pays TM construction *once*, in the
   compiler.
2. **Iteration bookkeeping was the dominant cost** (~1000 LOC/loop site). The
   layer pays it once in `loopTM` (C3).
3. **Single-tape with a delimiter scratch is the only economical shape** for
   composition — multi-tape composition needs `(sig+1)^k` bridge entries. The
   compiler is single-tape; this is also why the S2 multi-tape detour is
   unnecessary.
4. **The layer needs *cost* in its semantics, not just behaviour** — mathlib's
   `Computable`/`Partrec` handles computability but not complexity.

The Coq port avoids the blow-up by extracting TMs from the L-calculus; the
layer is the Lean analogue (smaller: a total structured while-language vs a
general λ-calculus). Parked hand-rolled work (~14K LOC) lives under `parked/`.

---

## References

- Coq source: <https://github.com/uds-psl/cook-levin>; local mirror `coqdoc/`.
- Status / orientation: root [`README.md`](../README.md).
- Completed probe brief (S3, archived): [`S3_RETIREMENT_EXPLORATION.md`](S3_RETIREMENT_EXPLORATION.md).
- Parked work: `parked/README.md`, `parked/PART2.md`.
