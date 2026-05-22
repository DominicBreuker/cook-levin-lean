# Cook–Levin in Lean 4 — Roadmap to a Faithful Proof

This document is a candid assessment of the Lean 4 Cook–Levin
formalisation under `CookLevin/`, together with a phased plan for
turning it into an honest, mathematically rigorous proof.

> **Read [Status update — May 2026](#status-update--may-2026) first.**
> The roadmap was rewritten mid-Part-2 to reflect a strategic pivot
> after the original "hand-roll each verifier as a flat Turing
> machine" approach overran its budget by an order of magnitude. The
> original Parts 2–6 are preserved as
> [Appendix C](#appendix-c--original-parts-26-plan-archival).

---

## Status update — May 2026

### Where we are

| Phase | Description                                                | Status |
|-------|------------------------------------------------------------|--------|
| 1     | Foundational hygiene, small-`sorry` cleanup                | ✅ done |
| 2 (framework) | TM-backed `DecidesBy` + `inTimePoly`               | ✅ done |
| 2 (content)   | Hand-rolled `EvalCnfTM` / `CliqueRelTM` verifiers  | ⏸ paused mid-stream |
| 3–7   | TM-backed reductions, simulators, Cook tableau             | rescoped (see below) |

- Repository size: **~25.7K LOC** of Lean.
- Build state: **`lake build` is green** with exactly **four labelled
  `sorry`s** ([detailed below](#the-four-open-sorrys)).
- `theorem CookLevin : NPcomplete SAT` typechecks against the strengthened
  framework but still inherits the weaknesses captured by the four
  `sorry`s and by Part 0.

### Why the pivot

The Part 2 *framework* migration (Steps 1–10 of `PART2.md`) landed
cleanly: `inTimePoly` is now backed by a real `FlatTM`-valued
`DecidesBy` structure, and `sat_NP` / `FlatClique_in_NP` rebuild
against it. That portion of the project is in good shape.

The Part 2 *content* (Step 11 of `PART2.md`: build a real TM that
verifies SAT) blew up dramatically:

| Item                                  | Original estimate | Actual / projected |
|---------------------------------------|-------------------|--------------------|
| Part 2 total                          | ~1,500 LOC        | ~14,500 LOC so far |
| `EvalCnfTM.decider` (closes 1 sorry) | (~600 LOC)        | ~8,100 LOC, ~30% done |
| Remaining Part 2 (Phase G + H)        | —                 | +~7,000 LOC projected |

The cause is structural, not accidental. Building a useful
algorithm out of `FlatTM`s — even via the `composeFlatTM` /
`branchComposeFlatTM` / `loopTM` combinators we developed — requires
per-state step lemmas, phase scan lemmas, and iteration lemmas for
each primitive. Each primitive lands in the 1,000–2,500-LOC range,
and amortisation across primitives is weak.

If the same overrun ratio applies to Parts 3–6 (each of which builds
*more* and *larger* Turing machines than Part 2), the project as
originally scoped projects to **~100,000–150,000 LOC**. That is
multi-year work for a side project and not the right shape of
investment for the mathematics involved: the combinatorial heart of
Cook–Levin (the `FlatTCC → FlatCC → BinaryCC → FSAT` chain) is already
in place at ~3,000 LOC.

The Coq port we are based on side-steps this entire problem by
extracting Turing machines from the L calculus / `computableTime'`
API: programs are written in a higher-level language and a one-time
extractor produces TM code, so each verifier proof is ~50–100 LOC of
L-level code rather than thousands of LOC of TM bookkeeping. Our
original ROADMAP (Part 4.1) explicitly declined to port L. **That
decision was the wrong one, and this revision reverses it.**

### The pivot

Pause the hand-rolled Part 2 finish. Build a small higher-level
computable layer ("the layer") with explicit cost semantics. Define
`inTimePoly` and `polyTimeComputable` through the layer. Pay the
"compile to `FlatTM`" cost *once*; every downstream verifier and
reduction is then a short program in the layer plus a short
correctness proof.

The layer is the new Part 3 of this roadmap. The old Parts 3–6 are
re-cast as content to be built on top of the layer (Parts 4–7).

The 14.5K LOC of existing Part 2 work is **not** wholly thrown away:

- `Complexity/Complexity/TMPrimitives.lean` (~3.5K LOC) — the
  `composeFlatTM` / `branchComposeFlatTM` family and the
  `runFlatTM_compose` / `runFlatTM_extend` machinery is the natural
  glue for the compiler's output. **Keep.**
- `Complexity/Complexity/TMEncoding.lean`, `TMDecider.lean`,
  `NP.lean` framework deltas. **Keep.**
- `Complexity/Complexity/Deciders/EvalCnfTM/Primitives.lean`,
  `CopyUnary.lean`, `CompareUnary.lean` (~8K LOC) —
  hand-rolled SAT-verifier primitives. **Retire.** Replaced by the
  layer.
- `Complexity/Complexity/Deciders/SAT_TM.lean` (~6.3K LOC) — the
  "demonstration deciders" Phase-C work, kept as a pattern library
  but never on the proof path. **Retire** (or relocate to `archive/`).

After the pivot lands, the `EvalCnfTM.decider` and `CliqueRelTM.decider`
sorrys close via the layer, not via hand-rolled `FlatTM`s.

### Fallback

If the pivot itself turns out to be too expensive (the layer
estimate is ~10–20K LOC; if it triples we hit a similar wall), the
fallback is option 3 of the May 2026 strategic review: state
Cook–Levin **conditionally** on a documented TM-construction
interface, treat the construction obligations as `axiom`-level
assumptions, and finish the combinatorial chain only. The current
code is already ~80% there for that scope.

---

## How we work — skeleton-first, risk-driven refinement

See the [`Development strategy`](../README.md#development-strategy-skeleton-first-risk-driven-refinement)
section of the root README for the full principles. The short
version:

- **The skeleton comes first.** The whole proof path compiles —
  with `sorry`s — before any Part is "done". This is already in
  place: see [Current skeleton state](#current-skeleton-state).
- **Refinement is risk-driven, not phase-sequential.** The Parts
  below describe the *target shape* of each area at completion;
  they do **not** prescribe an execution order. The order is
  determined by the [Risk register](#risk-register) — refine the
  highest-risk gap next, regardless of which Part it sits in.
- **Each iteration either validates a piece of the skeleton or
  surfaces a new gap.** Both outcomes are progress. Record gaps in
  the risk register and in commit messages, not in private notes.
- **Prefer concrete `def` + `sorry` over `axiom`.** Axiom count is
  a metric to minimise (see Current skeleton state).
- **Decompose sorrys, don't elaborate them.** Splitting a single
  large sorry into several focused ones is structural progress;
  starting to prove a single sorry without that decomposition risks
  hours of work on the wrong shape.

This methodology emerged from the May 2026 pivot (see
[Why the pivot](#why-the-pivot)). The original ROADMAP described
Parts 1–7 as sequential implementation phases with LOC estimates;
Part 2 blew up ~10× because its proof obligations had structural
issues that weren't visible until they were attempted. Skeleton-
first surfaces those issues before we commit the engineering
hours.

---

## Current skeleton state

Snapshot of where the compiling skeleton stands. **Update on every
iteration.**

| Metric                                | Value             | Trend |
|---------------------------------------|-------------------|-------|
| `lake build`                          | ✅ green (~3350 jobs) | unchanged |
| Axiom count (Lang layer)              | **0**             | unchanged |
| Tactical sorrys                       | ~28               | ↑ +5 (decomposition of risk #1) |
| `theorem CookLevin : NPcomplete SAT` | typechecks        | unchanged since pre-pivot |

Sorry distribution at the current snapshot (May 2026):

| File                                       | Sorrys | What they are |
|--------------------------------------------|--------|---------------|
| `Lang/Compile.lean`                        | 7      | `decodeTape_encodeTape`, `compileOp_sound`, `compileSeq_sound`, `compileIfBit_sound`, `compileForBnd_sound`, `Compile_sound`, `Compile_polyBound` |
| `Lang/PolyTime.lean`                       | 4      | `DecidesLang.toDecidesBy`, `inTimePolyLang_to_inTimePoly`, `PolyTimeComputableLang.comp`, `red_inNP_via_lang` |
| `Complexity/NP.lean`                       | 1      | `red_inNP` TM-composition (sorry #3 of the original four) |
| `GenNP_is_hard.lean`                       | 1      | `hasDeciderClassical` (sorry #4) |
| `Simulators/MultiToSingle.lean`            | 3      | step-bound poly/mono + acceptance |
| `Simulators/CookTableau.lean`              | 5      | wellformedness + bijection + size bound |
| `Deciders/EvalCnfTM.lean`                  | 1      | `encodeIn_size` (`5·n + 20 ≤ (n+1)^3`) |
| `Deciders/CliqueRelTM.lean`                | 3      | still-fully-stubbed `cliqueRelCmd` + encoding + lemmas |
| `Deciders/EvalCnfCmd.lean`                 | 7      | `processOneClause`/`processOneLiteral`/`memberCheck` + size lemmas + correctness + cost |

---

## Risk register

The next iteration's priority list, ranked by **structural risk**
(impact × likelihood-of-surfacing-a-gap). **Refine the highest-
ranked item first.** Update after every iteration: items that get
validated drop off, items that surface new gaps may climb or
split.

| # | Gap                                   | Location                              | Why this is high-risk |
|---|---------------------------------------|---------------------------------------|-----------------------|
| 1a | Per-constructor compiler helpers (compileOp / compileIfBit / compileForBnd; **compileSeq concretized**) | `Lang/Compile.lean` | The single `Compile := fun _ => …` stub has been **decomposed** (May 2026 iteration) and `compileSeq` has been **concretized** via `composeFlatTM`. Three helpers remain stubbed to `compiledCmd_default`: `compileOp`, `compileIfBit`, `compileForBnd`. The remaining structural risk is the per-`Op` TM design — most opaque is the per-`Op` head-movement / insert-symbol bookkeeping under the 3-symbol alphabet convention (`{0=delim, 1=shifted 0, 2=shifted 1}`). |
| 1b | `loopTM` combinator missing from `TMPrimitives.lean` | `Complexity/TMPrimitives.lean` | `compileForBnd` cannot be filled in without a `loopTM (body : FlatTM) → FlatTM` combinator analogous to `composeFlatTM` / `branchComposeFlatTM`. Design: counter on the same tape (in unary) or on a dedicated tape (then the layer needs multi-tape support and Part 5's simulator). The single-tape design is preferred but the bookkeeping has not been validated. |
| 1c | `compileIfBit` two-exit tester       | `Lang/Compile.lean`                   | `branchComposeFlatTM` requires `exit_pos ≠ exit_neg`. The tester TM (reads register `t`, dispatches to one of two exit states) is not yet designed. Trivial-looking but exposes the head-position invariant after the tester runs — does the head return to a canonical position before the bridge fires? |
| 2 | DSL expressiveness — missing primitives | `Lang/Syntax.lean`                    | Writing `evalCnfCmd` already surfaced two needs: no conditional/guarded loop (`Cmd.while`); no constant-comparison primitive (`Op.headEqVal`). Their type/cost shapes must be decided before downstream Cmd bookkeeping starts, or that work will be redone. |
| 3 | `PolyTimeComputableLang` ↔ framework integration | `Lang/PolyTime.lean`, `Complexity/NP.lean` | The framework's `polyTimeComputable` doesn't carry a Lang witness, so `red_inNP` can't compose at the layer level. Sorry #3 in `NP.lean` is blocked on this structural change — either upgrade `PolyTimeComputableWitness` or introduce a parallel `PolyTimeComputableTM` and migrate. |
| 4 | Cook tableau encoding                 | `Simulators/CookTableau.lean`         | `cookTableau M s steps` returns a `FlatTCC` with all fields `[]`. The encoding's `init`/`cards`/`final` triple has not been validated against `FlatTCC_wellformed` or `FlatTCCLang`. The size-bound polynomial's degree is also unjustified. |
| 5 | Multi-tape simulator design           | `Simulators/MultiToSingle.lean`       | Alphabet extension (delimiter + head-marker symbols) and the single-step simulation gadget haven't been designed; structurally similar to (1a). |
| 6 | `evalCnfCmd` inner bodies             | `Deciders/EvalCnfCmd.lean`            | Per-clause / per-literal / member-check are sorried Cmds. *Engineering* work, mostly dull, but each may surface another DSL gap. **Wait until (2) lands** so we don't write these twice. |
| 7 | `cliqueRelCmd`                        | `Deciders/CliqueRelTM.lean`           | Same shape as (6). Strictly downstream of (2) and ideally (6). |
| 8 | `hasDeciderClassical`                 | `GenNP_is_hard.lean`                  | Tractable once (3) lands. Last sorry to close. |

**Risk grading convention:** items 1a–3 are *structural* — they
either validate or surface gaps that change downstream type
signatures. Items 4–5 are *medium* — they need design decisions
but the surrounding types are stable. Items 6–8 are *engineering*
— mostly mechanical once their dependencies are validated.

### Iteration log

- **May 2026 — Risk #1 decomposed.** `Lang/Compile.lean` was
  refactored from the single `Compile := fun _ => validFlatTM_default`
  stub into a structural recursion `compileCmd : Cmd → CompiledCmd`
  with four per-constructor helpers (`compileOp`, `compileSeq`,
  `compileIfBit`, `compileForBnd`), all still stubbed but with
  focused sorrys. **Structural commitments made** (any future
  implementation must respect these):
  1. `CompiledCmd` records an explicit `exit` state — bare
     `FlatTM` is not enough for `composeFlatTM`-style composition.
  2. Alphabet is fixed at `sig = 3` (delim, shifted 0, shifted 1).
     This restricts the layer's inputs to bit-strings.
  3. `Compile.overhead`'s argument is now `State.size s + cost c s`
     rather than `State.size s` — honestly accounting for tape
     growth during execution.
  4. Each compiled fragment is single-tape (`tapes = 1`).
  **New sub-gaps surfaced**: 1a (per-Op TM design), 1b (`loopTM`
  combinator missing from `TMPrimitives.lean`), 1c (two-exit
  tester for `compileIfBit`). The `Compile_sound` sorry was split
  into four per-constructor sorrys plus the assembly. Net sorry
  count: +5 (3 → 7 in `Compile.lean`). Build remains green.

- **May 2026 — `compileSeq` concretized.** The `compileSeq` helper
  in `Lang/Compile.lean` was changed from the `compiledCmd_default`
  stub to a real `composeFlatTM`-based construction. All
  `CompiledCmd` invariants (`exit_lt`, `exit_is_halt`, `M_valid`,
  `M_tapes`, `M_sig`) discharge cleanly using the existing
  `composeFlatTM_*` lemmas. **Gap surfaced**: `composeFlatTM_run`'s
  trajectory precondition (`h_traj1`) requires M₁ to avoid halting
  prematurely, but `CompiledCmd` only guarantees the exit state
  *is* a halt state — not that it is the *unique* halt state.
  Compositional soundness (the still-`sorry`-bodied
  `compileSeq_sound`) will need either a strengthened
  `halt_unique` invariant on `CompiledCmd` or a per-helper
  operational invariant. Documented inline in `compileSeq`'s
  docstring. Sorry count unchanged at 7 in `Compile.lean`; build
  remains green; Lang layer still axiom-free.

---

## How to read the Parts below

The Parts describe the **target shape** of each area at the end of
the project. They do **not** prescribe an execution order. Read
them as "what success looks like for this area" plus a
decomposition into sub-steps that may be useful.

The execution order is determined by the [Risk register](#risk-register).
Parts can be partially advanced in any order; the dependencies
that matter are noted in each Part's text and in the risk
register's "Why this is high-risk" column.

The notation `Part 3.1`, `Part 4.2`, etc. is used in `TODO(...)`
tags throughout the source as a pointer to the area / sub-step,
not as a time marker.

---

## Part 0 — Honest assessment of the original state

This part is preserved from the original ROADMAP as the diagnosis
that motivated all subsequent work. Items marked ✅ have been
addressed by Parts 1–2; items marked ⏸ are paused by the May 2026
pivot; items marked ⏳ are still open and addressed by the revised
plan below.

The repository currently establishes
`theorem CookLevin : NPcomplete SAT`, but the term it produces is
**not** a faithful proof of the Cook–Levin theorem. Five separate
classes of issues, listed in roughly increasing difficulty to fix:

### 0.1 The complexity framework does not constrain runtime ✅ partly

- `PolyTimeComputableWitness f` only requires
  `encodable.size (f x) ≤ bound (encodable.size x)`. This bounds the
  *output size*, not the *running time*. (Still open — addressed in
  new Part 4.)
- `HasDecider X P f := ∃ dec : X → Bool, ∀ x, P x ↔ dec x = true`
  with `f : Nat → Nat` unused. (✅ Removed in Part 2, replaced with
  the TM-backed `DecidesBy`.)
- `inTimePoly P` inherits the weakness of `HasDecider`. (✅ Replaced
  in Part 2 with `∃ f, Nonempty (DecidesBy P f) ∧ inOPoly f ∧ monotonic f`.)

### 0.2 `NPhard_GenNP` is vacuous ⏳

`Complexity/GenNP_is_hard.lean` line 9 introduces

```
theorem hasDeciderClassical (P : X → Prop) (timeBound : Nat → Nat) :
    HasDecider X P timeBound := by
  classical
  refine ⟨fun x => if P x then true else false, ?_⟩
  …
```

This is used in `genNPInstance` and `NPhard_GenNP`. In Part 2 the
theorem was **retyped** to `Nonempty (DecidesBy …)` so the rest of
the chain typechecks against the strengthened framework, but its
body remains a labelled `sorry` (`TODO(Part6:hasDeciderClassical)`).
The real version requires Parts 3–6 to be in place so the verifier
TM can be drawn from `InNPWitness`. Closed in new Part 7.

### 0.3 The TM bridge layers are dummies ⏳

- `Complexity/LM_to_mTM.lean`: `bridgeMachine` is a 1-state,
  0-transition flat TM that starts in a halting state.
- `Complexity/mTM_to_singleTapeTM.lean`: same pattern with a 1-tape
  variant. The multi-tape machine `M` is passed in and immediately
  discarded.
- `Complexity/L_to_LM.lean`: a definitional repackaging — there is
  no TM at all.
- `…/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.lean`:
  `noncomputable def f inst := if TMGenNP_fixed M inst then yesInst
  else noInst`. The map's value depends on the answer to the source
  language.
- `…/FlatSingleTMGenNP_to_FlatTCC.lean`: same `if`-on-the-answer
  pattern.

Addressed in new Parts 5 (mTM → 1-tape via the layer) and Part 6
(Cook tableau via the layer).

### 0.4 Definitional smells ⏳ partly

- `instEncodableDefault` (`Definitions.lean:14`) silently defaults to
  `size := 0`. Still present. (Low priority; the consumers that
  relied on `size = 0` are now mostly placeholder TM-bridge layers.)
- `abbrev TM (_σ : Type) (_ : Nat) := FlatTM` — phantom parameters.
  Still present.
- `computableTime'` in `MachineSemantics.lean:186` — leftover Coq
  port hook. Will be **superseded** by the new layer's cost
  semantics (new Part 3).

### 0.5 Outstanding `sorry`s (original) ✅ all closed in Part 1

```
Complexity/NP/SAT.lean:206              compressAssignment_size_bound
Complexity/NP/FSAT_to_SAT.lean:706      FSAT_to_SAT_size_le
Complexity/NP/FlatClique.lean:38        clique_size_bound
Complexity/NP/kSAT_to_FlatClique.lean:63 polynomial-time bound
Complexity/NP/kSAT_to_FlatClique.lean:64 reduction correctness
```

All closed in Part 1.

### The four open `sorry`s after Part 2's framework migration

After the framework migration the codebase has exactly four labelled
`sorry`s, all flagged with `TODO(...)` tags pointing at the roadmap
phase that closes them:

| # | Location                                          | Tag                                  | Closes at |
|---|---------------------------------------------------|--------------------------------------|-----------|
| 1 | `…/Deciders/EvalCnfTM.lean:58`                    | `TODO(Part2-followup:EvalCnfTM)`     | New Part 3.5 |
| 2 | `…/Deciders/CliqueRelTM.lean:66`                  | `TODO(Part2-followup:CliqueRelTM)`   | New Part 3.5 |
| 3 | `Complexity/Complexity/NP.lean:270`               | `TODO(Part3:red_inNP_TMcompose)`     | New Part 4 |
| 4 | `Complexity/GenNP_is_hard.lean:23`                | `TODO(Part6:hasDeciderClassical)`    | New Part 7 |

### What is already sound and should not be touched

- `Complexity/Complexity/MachineSemantics.lean` — `FlatTM` semantics
  and `runFlatTM` are real.
- `Complexity/Complexity/Definitions.lean` — `encodable`,
  `inOPoly`, `monotonic`, polynomial composition (`inOPoly_comp`).
- `Complexity/Complexity/NP.lean` — reduction calculus
  (`reducesPolyMO_reflexive/_transitive`, `red_inNP`, `red_NPhard`).
- `Complexity/Complexity/TMPrimitives.lean` — `composeFlatTM`,
  `branchComposeFlatTM`, `runFlatTM_extend`, `runFlatTM_compose`,
  `scanRightUntilTM`, `verdictTM` (~3.5K LOC, fully proved). This is
  the natural target language of the new layer's compiler.
- The combinatorial core
  `FlatTCC_to_FlatCC ⋅ FlatCC_to_BinaryCC ⋅ BinaryCC_to_FSAT`:
  ~3,000 LOC of fully proved, computable reductions with real size
  bounds (`5n+5`, `50n² + 50n + 1`, `500n⁶ + 500`).
- `Complexity/NP/SAT.lean`, `kSAT.lean`, `kSAT_to_SAT.lean`,
  `FSAT.lean`, `FSAT_to_SAT.lean` (Tseytin), `FlatClique.lean`,
  `kSAT_to_FlatClique.lean`.

---

## Part 1 — Foundational hygiene ✅ done

All five sub-items of P1.1–P1.5 from the original ROADMAP landed.
The original five "small" `sorry`s are closed. `Subtypes.lean` is
still present but empty (low-priority cleanup; not on the critical
path).

---

## Part 2 — TM-backed `inTimePoly` framework ✅ done; content ⏸ paused

The Part 2 *framework* (Steps 1–10 of [`PART2.md`](../parked/PART2.md))
landed in good shape:

- `Complexity/Complexity/NP.lean` gained the `DecidesBy` structure
  and a TM-backed `inTimePoly`.
- `Complexity/Complexity/TMDecider.lean` — `inTimePolyTM`,
  `DecidesBy.decideFn` + soundness, `.negate`, `.iff` combinators.
- `Complexity/Complexity/TMEncoding.lean` — list-level encoding
  helpers.
- `Complexity/Complexity/TMPrimitives.lean` — the `composeFlatTM`
  combinator family (`branchComposeFlatTM` for polarity dispatch,
  `runFlatTM_compose` for chaining, `runFlatTM_extend` for time-bound
  padding).
- `sat_NP` and `FlatClique_in_NP` rebuilt against the new framework
  (modulo their `DecidesBy` witnesses, which are sorrys #1 and #2).
- `red_inNP` and `P_NP_incl` rebuilt against the new framework
  (modulo sorry #3, the TM-composition gap).
- `hasDeciderClassical` retyped to produce `Nonempty (DecidesBy …)`
  (body is sorry #4).

The Part 2 *content* — closing sorrys #1 and #2 by constructing
actual SAT-verifier and FlatClique-verifier `FlatTM`s by hand —
is **paused** mid-stream. The detailed history of what was built
is in [`PART2.md`](../parked/PART2.md) (now treated as archival once the
pivot lands). Two primitives (`copyUnaryTM`, `compareUnaryAtMarkerTM`)
were fully closed; the per-literal / per-clause / per-CNF loops were
not, and the `CliqueRelTM` analogue was never started.

---

## Part 3 — Higher-level computable layer (NEW, the pivot)

Build a small total computation language ("the layer") with explicit
cost semantics, and a one-time compiler from the layer to `FlatTM`.
This is the central infrastructure investment of the May 2026 pivot.

### 3.1 Choose the language

Recommended: a small **structured while-language** with bounded
loops, fixed-arity primitive operations on `List Nat`, and an
explicit cost annotation per primitive. This is enough to express
every verifier and reduction we need.

Candidate shape:

```lean
inductive Cmd : Type where
  | skip   : Cmd
  | seq    : Cmd → Cmd → Cmd
  | assign : Var → Expr → Cmd
  | if_    : BExpr → Cmd → Cmd → Cmd
  | for_   : Var → Expr → Cmd → Cmd     -- counted loop, bound = Expr
```

Cost is the sum over `Cmd` of a fixed constant per node, plus the
iteration count of each `for_`. We commit to *total* cost (the bound
must always be evaluable) so the cost function is a closed-form
expression in input size.

An alternative is **μ-recursive with cost** (closer to the Coq L
calculus); the trade-off is that it puts more weight on the
compiler. The decision lands in 3.1.

### 3.2 Define `inTimePoly` and `polyTimeComputable` via the layer

```lean
def inTimePoly {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ (p : Cmd) (f : Nat → Nat),
    inOPoly f ∧ monotonic f ∧
    (∀ x, cost p (encode x) ≤ f (encodable.size x)) ∧
    (∀ x, eval p (encode x) = decide (P x))

def polyTimeComputable {X Y : Type} [encodable X] [encodable Y]
    (h : X → Y) : Prop := …    -- analogous
```

Replacing `DecidesBy` with this is a pure interface swap inside
`NP.lean`; downstream theorems (`sat_NP`, `FlatClique_in_NP`,
`red_inNP`, `red_NPhard`) keep their signatures.

### 3.3 Build the compiler `Compile : Cmd → FlatTM`

One-time engineering. Each `Cmd` constructor compiles to a small
gadget over `FlatTM` using the existing `composeFlatTM` /
`branchComposeFlatTM` combinators:

- `skip` → 1-state halt
- `seq c₁ c₂` → `composeFlatTM (Compile c₁) (Compile c₂)`
- `if_ b c₁ c₂` → `branchComposeFlatTM (CompileB b) (Compile c₁) (Compile c₂)`
- `for_` → a `loopTM` instance (the third combinator planned in
  PART2.md §11.5c, now landed here)
- primitives → small hand-rolled TMs (~50 LOC each, but a finite
  fixed set, e.g. ~10 primitives total)

**Estimated size: ~5,000 LOC.** Most of it is per-primitive
correctness lemmas; the inductive cases use the combinators as black
boxes.

### 3.4 Soundness theorem

The main extraction lemma:

```lean
theorem Compile_sound (p : Cmd) (input : List Nat) :
    ∃ cfg,
      runFlatTM (cost p input + compileOverhead) (Compile p)
          (initFlatConfig (Compile p) [input]) = some cfg ∧
      haltingStateReached (Compile p) cfg = true ∧
      readTape cfg = eval p input
```

Plus a corollary "if `cost p` is polynomial in input size, then
`runFlatTM` halts within a polynomial step budget". This is the
bridge that makes the layer-level `inTimePoly` imply the
`FlatTM`-level `DecidesBy`.

**Estimated size: ~1,500 LOC.**

### 3.5 Close sorrys #1 and #2 via the layer

Write `evalCnfCmd : Cmd` (~50 LOC) and `cliqueRelCmd : Cmd` (~80 LOC)
in the layer, prove their cost bounds (~100 LOC each), prove their
correctness against `satisfiesCnf` / `cliqueRel` (~150 LOC each),
and instantiate the bridge to close sorrys #1 and #2.

**Estimated size: ~800 LOC total, replacing the projected ~10K LOC
of hand-rolled work in Phases G+H of PART2.md.**

After Part 3, two of the four open sorrys are closed and the layer
exists as reusable infrastructure for Parts 4–7.

---

## Part 4 — `polyTimeComputable` via the layer

Migrate the `polyTimeComputable` witnesses for every reduction in
the chain to use the layer.

### 4.1 Replace the placeholder witnesses

Each reduction in `Complexity/NP/SAT/CookLevin/Reductions/` and the
Tseytin transformation currently provides a `PolyTimeComputableWitness`
that bounds only the output size. Replace each with a layer-level
program whose `cost` is polynomial in input size.

The reductions in scope:

- `kSAT_to_SAT_reduction` (trivial, ~30 LOC in the layer)
- `FSAT_to_SAT_tseytin` — already explicitly computable, the layer
  implementation is mostly transcribing the existing recursion (~300 LOC)
- `kSAT_to_FlatClique_instance` (~150 LOC)
- `flatTCC_to_flatCC`, `FlatCC_to_BinaryCC_instance`,
  `BinaryCC_to_FSAT_instance` (~100 LOC each)

### 4.2 Re-prove `red_inNP`

With the layer in place, the composition obligation that is sorry #3
(`TODO(Part3:red_inNP_TMcompose)`) is a straightforward
`Cmd.seq`-style composition: run the reduction's layer program on
the input, then the verifier's layer program on the result. The
cost composes via `inOPoly_comp`, which already exists.

**Estimated size: ~1,500 LOC.** Closes sorry #3.

After Part 4, three of the four open sorrys are closed and every
`⪯p` arrow in the chain is real.

---

## Part 5 — Multi-tape → single-tape via the layer

Replace the dummy bridges in `LM_to_mTM.lean` and
`mTM_to_singleTapeTM.lean` with the standard textbook construction,
expressed in the layer.

### 5.1 Decide the source-language model

Per the original ROADMAP P4.1, recommendation (a): drop L entirely.
Treat `GenNPInput` / `LMGenNP` as abstract NP-source formulations
and collapse the "L → LM → mTM" tower into a single
"GenNP → mTMGenNP_fixed" reduction.

### 5.2 Multi-tape → single-tape simulator

Standard construction: encode the `k` tapes with delimiters and a
head-marker extension of the alphabet. Each source step costs O(L)
target steps where L is the total tape length. The simulator
itself is **~150 LOC in the layer** plus a ~200-LOC correctness
proof.

### 5.3 GenNP → mTM reduction

Construct a (non-deterministic) multi-tape TM that guesses a
certificate and runs the verifier. With Part 4's layer-level
verifiers in hand, this is ~200 LOC.

**Estimated total for Part 5: ~1,000 LOC** (vs. the original ROADMAP's
~3,000 LOC for the same content in hand-rolled form).

---

## Part 6 — Cook tableau via the layer

The actual heart of Cook–Levin: the Cook 2D tableau. Currently
faked by `if FlatSingleTMGenNP inst then trivial-yes else trivial-no`.

### 6.1 Implement the tableau construction

For a TM `M` on input `s` with step budget `steps`, build a
`FlatTCC` instance whose
- `init` is the start configuration encoded as a row of width
  `1 + |s| + steps + 1`,
- `cards` encode the local 3-cell transitions of `M`,
- `final` matches iff a halting state appears somewhere in the
  final row,
- `Sigma` is `M`'s alphabet plus state symbols plus a head marker.

This is the classical 2D tableau. The construction is a *function*
on `M, s, steps` (no TM execution involved), so it lives at the
mathematical level — the layer is only needed for its cost bound,
not its definition.

**Estimated size: ~1,000 LOC** for the construction (vs the
original ROADMAP's ~3,000 LOC).

### 6.2 Prove the bijection

`FlatSingleTMGenNP (M, s, maxSize, steps) ↔ FlatTCC (encode M s steps)`,
both directions, via the standard tableau-to-run bijection.

**Estimated size: ~1,500 LOC.**

### 6.3 Prove the size bound

Linear in `(|s| + steps) · |Σ|`.

**Estimated size: ~200 LOC.**

After Part 6, the "M accepts s in `steps` steps" → "the FlatTCC
tableau is satisfiable" link is real, and the FlatTCC → FSAT → SAT
chain (already sound) finishes the proof.

---

## Part 7 — Real `NPhard_GenNP` and final assembly

### 7.1 Delete `hasDeciderClassical`

Replace its use in `genNPInstance` with the real verifier coming
from `InNPWitness`'s (now layer-backed) `inTimePoly`.

### 7.2 Re-state `NPhard_GenNP`

The proof goes through mechanically once the framework is sound.
Closes sorry #4.

### 7.3 Audit `CanEnumTerm`

The `boollists_enum_term` encoding is currently a size-only
encoding (not an injection). Replace with a proper binary encoding
`Y → List Bool`. Mathlib's `Encodable` / `Denumerable` may be
reusable.

### 7.4 End-to-end test

`theorem CookLevin : NPcomplete SAT` rebuilds against the new
definitions. Verify build is sorry-free, axiom-free beyond the
standard set (`propext`, `Classical.choice`, `Quot.sound`),
reproduces.

### 7.5 `#print axioms CookLevin`

Add a small file. Document the surviving axioms.

### 7.6 CI target

Fail the build if any new `sorry` or `hasDeciderClassical`-style
classical shortcut creeps in.

### 7.7 Documentation pass

Update READMEs and the "axioms used" appendix.

---

## Rough effort estimate (lower-confidence)

⚠ **Under the skeleton-first methodology, these are upper-bound
estimates we re-evaluate per iteration, not commitments.** The
original ROADMAP gave LOC estimates that turned out to be ~10× too
low because the proof obligations had unsurfaced structural
issues. The numbers below are best-effort upper bounds *given the
skeleton we have today*; they will change as the risk register
shrinks.

| Part  | Area                                                 | Estimate     | Original estimate | Status |
|-------|------------------------------------------------------|--------------|-------------------|--------|
| 1     | Cleanup & `sorry` discharge                          |  ~500 LOC    |  ~500 LOC         | ✅ done |
| 2     | TM-backed `inTimePoly` *framework*                   | ~1,500 LOC   | (subset of 1,500) | ✅ done |
| 2c    | Hand-rolled deciders *(retired)*                     | n/a          | n/a               | ⏸ retired in favour of Part 3 |
| 3     | Higher-level computable layer (skeleton landed)      | ~7,000 LOC   | n/a               | 🟡 skeleton; refining |
| 4     | `polyTimeComputable` via the layer                   | ~1,500 LOC   | ~4,000 LOC        | 🟡 skeleton; refining |
| 5     | Multi-tape → 1-tape simulator via the layer          | ~1,000 LOC   | ~3,000 LOC        | 🟡 skeleton; refining |
| 6     | Cook tableau (TM → FlatTCC) via the layer            | ~2,700 LOC   | ~3,000 LOC        | 🟡 skeleton; refining |
| 7     | Real `NPhard_GenNP`, axiom check, CI, docs           |  ~600 LOC    |  ~600 LOC         | 🟡 skeleton; refining |

**Rough remaining LOC:** ~13,000 across Parts 3–7. The skeleton
already in place means the *types and theorem statements* are
done; the LOC estimates above are for filling in the proof
bodies, with the higher-risk items more likely to overrun (see
[Risk register](#risk-register)).

### Iteration cadence

Not a fixed sequence — the risk register is the source of truth.
The shape of each iteration:

1. Pick the top item in the [Risk register](#risk-register).
2. Try to concretize it: replace the axiom with a `def`, or the
   single sorry with several smaller sorrys, or fill in a proof.
3. If it typechecks: validation. The risk register entry drops
   off or moves down.
4. If a structural gap surfaces: stop, document the gap, possibly
   add a new risk register entry, decide whether to fix the
   structure now or work around it.
5. Always commit + push with `lake build` green. The build state
   is the source of truth for "the skeleton is still coherent".
6. Update the [Current skeleton state](#current-skeleton-state)
   snapshot (axiom count, sorry count, build status).

Items 1–5 are typically one session. Item 6 is one paragraph.

---

## Things NOT to break

Every iteration must preserve the build and keep the existing
real mathematics compiling:

- `FlatTM` semantics in `MachineSemantics.lean`.
- `inOPoly`, `inOPoly_add`, `inOPoly_comp` in `Definitions.lean`.
- The combinator library in `TMPrimitives.lean`
  (`composeFlatTM`, `branchComposeFlatTM`, `runFlatTM_compose`,
  `runFlatTM_extend`). The new layer's compiler emits into this
  library.
- The full Tseytin transformation in `FSAT_to_SAT.lean`.
- The 3-level tableau core
  `FlatTCC_to_FlatCC`, `FlatCC_to_BinaryCC`, `BinaryCC_to_FSAT`.
- `SAT_inNP.sat_NP`, `FlatClique_in_NP` — the *interfaces* are
  stable; only the `DecidesBy` witnesses change underneath.
- The reduction calculus (`⪯p`, `red_NPhard`, `red_inNP`).

When introducing the layer in Part 3, add it as a new namespace
(e.g., `Complexity.Lang`) and migrate `DecidesBy` consumers one at
a time. The hand-rolled `EvalCnfTM` / `CliqueRelTM` primitives can
be retired in a single sweep at the end of Part 3.

---

## Fallback plan: if the layer also overruns

If Part 3 lands meaningfully over its ~7,000 LOC estimate (say, by
3× or more), the next pivot is to **scope-restrict the headline**:

- Define `inTimePoly` axiomatically (an interface specifying the
  operations a TM-computable predicate must support: closure under
  Boolean operations, composition, polynomial time-bounded
  iteration). Mark it as a documented assumption rather than
  proving it via a concrete TM model.
- Finish the combinatorial chain (FlatTCC → FlatCC → BinaryCC →
  FSAT → SAT) — already in place.
- State `CookLevin : NPcomplete SAT` conditionally on the
  `inTimePoly`-interface assumption, with a clearly documented
  list of obligations that a future TM model must discharge.

This gives an *honest conditional theorem* in a few weeks rather
than a *real unconditional theorem* in years. It is not as
satisfying, but it is more useful than indefinitely paused work.

---

## Appendix A — Lessons from the hand-rolled Part 2

The May 2026 pivot was driven by hard-won experience. These notes
are for anyone considering a similar approach in a different
formalisation.

1. **Per-state lemmas don't amortise across primitives.** Every
   new primitive needs its own per-state step lemmas, per-state
   run-unfold helpers, and phase scan lemmas. Reusable infrastructure
   helps the *chaining* (via `composeFlatTM_run`), but the inside of
   each primitive is fresh work each time.

2. **Iteration bookkeeping is the dominant cost.** ~600 LOC per
   loop site to thread tape state through the iteration count,
   plus another ~400 LOC of post-loop cleanup. `copyUnaryTM` and
   `compareUnaryAtMarkerTM` paid this cost twice for what are
   conceptually 5–9 state machines.

3. **A unified `loopTM` combinator helps but doesn't rescue you.**
   PART2.md Optimisation O2 (`loopTM`) was planned as the
   amortisation lever. It still only saves the iteration bookkeeping
   *between* primitives, not the per-state bookkeeping *inside*
   each primitive's body.

4. **Multi-tape vs single-tape is a real cost driver.** The
   `entryMatchesConfig` lookup has no wildcard, so a `k`-tape
   composition needs `(sig+1)^k` bridge entries per composition.
   Single-tape with a delimiter scratch is the only economical
   shape for hand-rolled TM composition. The layer's compiler
   should respect this constraint.

5. **The layer needs *cost* in its semantics, not just behaviour.**
   Mathlib's `Computable`/`Partrec` infrastructure handles
   computability but not complexity; using it as-is would close
   sorry #1 only by replacing "TM construction" with "Computable
   construction", which doesn't help unless cost annotations are
   added.

---

## Appendix B — Why the L calculus (Coq's choice) inspired the pivot

The Coq Cook–Levin port writes verifiers and reductions in the L
calculus (a small untyped lambda calculus over numerals) and uses
the `computableTime'` tactic to extract Turing machines with proved
time bounds. The L calculus itself is ~3,000 lines of Coq
infrastructure; each downstream verifier or reduction is then ~50–100
lines of L-level code.

We declined to port L in the original ROADMAP P4.1 because we
believed a Lean port should be self-contained and that the L
calculus was a "Coq-port artifact". After ~14K LOC of hand-rolled
Part 2 work, the empirical evidence is that the Coq team's
abstraction is essentially load-bearing for the whole proof, not a
local choice: any informal Cook–Levin proof spends most of its
words describing a generic polynomial-time TM, and any formalisation
must therefore commit to *some* abstraction that lets you talk
about a generic polynomial-time TM without writing it out.

The new layer (Part 3) is the Lean analogue of L. It is smaller
and weaker than L (structured while-language vs general lambda
calculus; total vs partial), but it is enough for Cook–Levin.

---

## Appendix C — Original Parts 2–6 plan (archival)

This appendix preserves the original Parts 2–6 plan from the
pre-pivot ROADMAP. It is **superseded** by Parts 3–7 above. Read
this only if you are doing historical archaeology on the project's
proof strategy.

### (Original) Part 2 — Strengthen the framework to a real `inTimePoly`

Replace `HasDecider` with a TM-backed `DecidesBy` structure, then
re-prove `sat_NP`, `FlatClique_in_NP`, `red_inNP`, `P_NP_incl`.

**Status:** Framework portion ✅ done in Steps 1–10 of PART2.md.
Content portion (hand-rolled `EvalCnfTM` / `CliqueRelTM` deciders)
⏸ paused mid-Step-11, superseded by new Part 3.

### (Original) Part 3 — Strengthen `polyTimeComputable`

Replace the output-size-only `PolyTimeComputableWitness` with a TM
that *computes* `f`, and re-prove every `_poly` theorem in the chain.

**Status:** Superseded by new Part 4 (uses the layer instead of
hand-rolled TM constructions).

### (Original) Part 4 — Replace the dummy TM bridges

Build a real multi-tape → single-tape simulator; build a real
GenNP → mTM reduction.

**Status:** Superseded by new Part 5 (uses the layer).

### (Original) Part 5 — Replace the FlatSingleTMGenNP → FlatTCC reduction

Implement the Cook 2D tableau construction.

**Status:** Superseded by new Part 6 (uses the layer for the cost
side of the construction).

### (Original) Part 6 — Replace `NPhard_GenNP`

Delete `hasDeciderClassical`, re-state `NPhard_GenNP` against the
strengthened framework.

**Status:** Superseded by new Part 7.

### (Original) Part 7 — Final assembly and CI

End-to-end test, `#print axioms`, CI target, documentation pass.

**Status:** Folded into new Part 7.
