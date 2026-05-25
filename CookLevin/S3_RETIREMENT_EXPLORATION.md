# Agent brief: retire Risk S3 — make `polyTimeComputable` TM-backed

> **Handoff document.** Self-contained brief for the agent picking up the
> single biggest *unvalidated* risk to a faithful, **unconditional**
> Cook–Levin in this codebase. Assumes no prior context. Read it top to
> bottom, then read the files in §3 before writing code. This is a
> **time-boxed go/no-go probe** in the same style as the completed
> `loopTM` (C3), `compileSeq` (C2), and Cook-tableau (S1) probes.

## 1. Mission

`theorem CookLevin : NPcomplete SAT` typechecks but is **conditional** —
deepest of all on **Risk S3**: the framework's `polyTimeComputable f`
requires only that `f`'s *output size* is polynomially bounded, not that
any machine computes `f`. Your job:

> **Validate whether `polyTimeComputable` can be upgraded to a real
> (layer-/TM-backed) witness — the one change that makes the entire layer
> effort meaningful and exposes the deepest unsoundness — or whether that
> upgrade explodes and forces the documented fallback.**

A clean "yes — here is the TM-backed witness, the bridge that builds it
(given `Compile_sound`), the framework lemmas re-proved against it, and a
migration-cost estimate" and a clean "no — here is precisely where it
explodes, trigger the fallback" are **both successful outcomes.** Do not
try to close everything; do not break the live `CookLevin`.

## 2. Why this is *the* biggest risk

The headline theorem is conditional on three classes of gap (see the
ROADMAP Risk register). The layer probes (C1/C2/C3) de-risked the *layer*
— but the layer is a means to an end. The end hinges on **S3**:

- **S3 is the enabling weakness.** `PolyTimeComputableWitness f` requires
  only `encodable.size (f x) ≤ bound (encodable.size x)`. The reduction
  relation `⪯p` (`ReductionWitness.reduction_poly`) uses this weak
  predicate, so a `noncomputable` map whose output is always one of two
  fixed instances trivially satisfies it.
- **S3 licenses the deepest unsoundness (S1 + S2).** The
  `if (source is yes-instance) then yesInst else noInst` reductions (S1)
  and the dummy `bridgeMachine`s that discard the source TM (S2) typecheck
  **only because** of S3. They are `sorry`-free and invisible to
  `#print axioms` — the genuinely unsound core of the project. Until S3 is
  retired there is no forcing function that makes them be real.
- **S3 is the payoff gate for the whole layer.** C1 (per-primitive), C2
  (composition), C3 (`loopTM`) are all validated and exist to back
  `inTimePoly` / `polyTimeComputable`. If the bridge from the layer to a
  TM-backed `polyTimeComputable` can't be built faithfully, the layer
  backs nothing and the pivot fails.
- **S3 blocks a live proof-path `sorry`.** `red_inNP` (`NP.lean`, the
  `P ⪯p Q → inNP Q → inNP P` composition) is `sorry`; its own TODO says
  the fix is "give `PolyTimeComputableWitness` a real layer program for
  the reduction." Same for the four bridges in `Lang/PolyTime.lean`.
- **S3 is the unconditional-vs-fallback decision point.** Retiring S3
  forces *every* `⪯p` in the chain — including the sound combinatorial
  tail (FlatTCC→…→SAT) — to carry a real computation of its map. Whether
  that ripple is tractable is **the** question the layer was built to
  answer, and it has never been tested end-to-end. This probe answers it.

Everything downstream (the real Cook tableau S1, the multi-tape simulator
S2/S4, real `NPhard_GenNP` C8) is **gated on S3**: the vacuous versions
typecheck until S3 retires, so there is no point building the real
versions first.

## 3. Read these first (in order)

1. `CookLevin/ROADMAP.md` — Status snapshot, the **Risk register**
   (Group S = soundness, esp. **S3**, S1, S2; Group C = completion), and
   "How we work (skeleton-first)".
2. `CookLevin/Complexity/Complexity/NP.lean` —
   - `PolyTimeComputableWitness` / `polyTimeComputable` (~lines 8–16):
     **the S3 definition** (output-size bound only);
   - `DecidesBy` / `inTimePoly` (~51–94): the *real* TM-backed interface
     that already exists for decision problems — your model for what a
     TM-backed witness looks like;
   - `ReductionWitness` / `⪯p` (~199–209): where the weak witness leaks
     into the reduction relation;
   - `red_inNP` (~255) — the live `sorry`; **read its TODO**, it specifies
     the intended fix exactly;
   - `red_NPhard`, `reducesPolyMO_transitive` — the lemmas that must still
     compose after the upgrade.
3. `CookLevin/Complexity/Lang/PolyTime.lean` — the layer-side analogues
   and the four bridge `sorry`s:
   - `PolyTimeComputableLang` (carries a real `Cmd` + `computes` +
     `cost_le` — the layer already has the real content);
   - **`PolyTimeComputableLang.toFrameworkWitness` (~104)** — this is the
     S3 *leak* made explicit: it discards `computes`/`cost_le` and proves
     the framework witness from `output_size_le` alone. The real version
     of this is your deliverable;
   - `DecidesLang.toDecidesBy`, `inTimePolyLang_to_inTimePoly`,
     `PolyTimeComputableLang.comp`, `red_inNP_via_lang` — all reduce to
     `Compile_sound`.
4. `CookLevin/Complexity/Lang/Compile.lean` — `Compile_sound`,
   `compileForBnd_sound` (still `sorry`; **assume them** — landing them is
   separate bounded engineering, not your job), and `Compile.overhead`.
   The C3 result `TMPrimitives.loopTM_run` is the validated iteration
   lemma the eventual `compileForBnd_sound` will use.
5. The reductions S3 currently licenses (to test the forcing function):
   `.../Reductions/FlatSingleTMGenNP_to_FlatTCC.lean` and
   `.../Reductions/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean`
   (the `if-source then yesInst else noInst` maps), and
   `LM_to_mTM.lean` / `mTM_to_singleTapeTM.lean` (the dummy bridges).
6. The sound tail (the migration-ripple cost): the reduction maps in
   `.../Reductions/FlatTCC_to_FlatCC.lean`, `FlatCC_to_BinaryCC.lean`,
   `BinaryCC_to_FSAT.lean`, `NP/FSAT_to_SAT.lean` — these are *real* maps
   but currently only size-bounded; under a TM-backed `⪯p` they would each
   need a layer program. Gauge how hard each is as a `Cmd`.

## 4. The work plan — cheapest first, STOP when you have an answer

Additive throughout: define the new witness *alongside* the existing one
so the live `CookLevin` keeps compiling. Assume `Compile_sound` (use it as
a hypothesis or leave its `sorry`). Commit green between steps.

**(A) Design the TM-backed witness.** Define `PolyTimeComputableWitness'`
(or extend the existing one with a new field) that carries a *real*
computation, not just `output_size_le`. Recommended shape (layer-native,
since the pivot is committed): bundle a `Lang.PolyTimeComputableLang f`
(a `Cmd` with `computes : decodeOut (c.eval (encodeIn x)) = f x` and a
polynomial `cost_le`). The bridge to an actual `FlatTM` is then `Compile`.
*This alone is valuable*: it pins down the honest interface every reduction
must meet.

**(B) Build the real bridge.** Prove `toFrameworkWitness'` :
`PolyTimeComputableLang f → PolyTimeComputableWitness' f`, *assuming
`Compile_sound`*. This is the content the current `toFrameworkWitness`
fakes. Measure: does it go through cleanly given `Compile_sound`, or does
the TM-backed obligation need more than the layer provides?

**(C) Re-prove composition against the new witness.** Discharge the live
`red_inNP` `sorry` (its TODO is the recipe: compose `f`'s program with the
verifier via `Cmd.seq`, bridge via `inTimePolyLang_to_inTimePoly`), and
check `reducesPolyMO_transitive` / `red_NPhard` still compose with the
TM-backed `⪯p`. Lean: this needs `PolyTimeComputableLang.comp` (sequencing
two layer programs) — validate that too, or record exactly where it
sticks. Measure which sub-lemmas dominate.

**(D) Confirm it actually retires S3 (the forcing-function test).** Show
that the if-on-the-answer map (S1) does **not** satisfy the new witness:
its `reduction_poly'` obligation would require a `Cmd` that *decides the
source predicate* in polynomial cost, which is exactly what a many-one
reduction may not do. You need not break the live build — demonstrate on
one S1 map that the TM-backed obligation is unprovable (or would require a
decider for an NP predicate). This is the key evidence the upgrade is real.

**(E) Estimate the migration ripple (the decisive cost question).**
Upgrading `⪯p` to the TM-backed witness forces every reduction in the
chain — **including the sound tail** (FlatTCC→FlatCC→BinaryCC→FSAT→SAT) —
to supply a layer program computing its map. Survey those maps: how many,
and how hard is each as a `Cmd`? The tail maps are structural list/encoding
transforms; judge whether the layer compiles them cheaply (→ proceed) or
whether re-expressing the whole chain in the DSL is the explosion point
(→ fallback). Note any new DSL primitives needed (Risk C5).

> **Companion gotcha (Part 0.1 / `instEncodableDefault`).** A TM-backed
> witness over a type whose `encodable.size` is constantly `0`
> (`Definitions.lean`'s low-priority default instance) is *still* vacuous —
> the polynomial bound `≤ bound 0` says nothing. Retiring S3 fully also
> needs real `encodable` instances on the chain's intermediate types. Flag
> any size-0 type you hit; you don't have to fix them all, but the verdict
> must account for them.

## 5. What to deliver (the verdict)

A short written report (final message and/or appended to `ROADMAP.md`'s
"Validated so far" / iteration digest):

1. **Is the upgrade tractable?** Did A–D go through (given `Compile_sound`)?
   Where did difficulty concentrate — the bridge (B)? the composition
   lemmas (C)? did D confirm S1/S2 stop typechecking?
2. **Migration ripple (E).** How many reductions need layer programs;
   realistic LOC to re-express the chain (esp. the sound tail) in the DSL;
   any new DSL primitives required. Plus the encodable-instance work.
3. **Recommendation**, one of: (i) **feasible — proceed**: the witness
   upgrades cleanly, composes, and retires S3; here is the order for the
   real-reduction work it unblocks (S1 Cook tableau, S2 multi-tape
   simulator, C8 `NPhard_GenNP`). (ii) feasible but expensive — proceed
   after X. (iii) **intractable as scoped — trigger the fallback**: state
   `CookLevin` conditionally on a documented axiomatic `inTimePoly`/`⪯p`
   interface, keep the sound combinatorial tail, and stop sinking
   engineering. All three are legitimate; this probe exists to make the
   call on evidence.
4. Any new structural gaps for the Risk register.

## 6. Workflow & guardrails

- **Build:** `export PATH="$HOME/.elan/bin:$PATH" && lake build`. First
  build is slow (mathlib); start it early. Green between commits.
- **Additive only.** Define the new witness/bridge alongside the existing
  ones; **do not** migrate the live `⪯p` / break `CookLevin` in this probe
  (that is the *execution* of the verdict, not the probe). Keep the
  existing `sorry`s untouched except where you discharge `red_inNP`.
- **Assume `Compile_sound` / `compileForBnd_sound`.** Landing them is
  separate bounded engineering (per-`Op` gadgets + the guard/decrement for
  `loopTM`). Use them as hypotheses; the probe is about the *bridge above*
  them, not the layer below.
- **No new `axiom`s; axiom-clean** (only `propext` / `Classical.choice` /
  `Quot.sound`). Skeleton-first: if a bridge resists, decompose its `sorry`
  into focused sub-lemmas and record the gap rather than grinding.
- **Git:** commit to your assigned feature branch; clear messages; create a
  PR only if asked.
