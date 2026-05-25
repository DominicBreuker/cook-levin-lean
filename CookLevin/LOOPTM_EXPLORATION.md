# Agent brief: validate the `loopTM` combinator + run lemma (Risk C3)

> **Handoff document.** This is a self-contained brief for an agent picking up
> the single biggest *unvalidated* risk to a faithful, unconditional Cook–Levin
> proof in this codebase. It assumes no prior context. Read it top to bottom,
> then read the files in §3 before writing any code.

## 1. Mission

This project formalizes Cook–Levin in Lean 4
(`theorem CookLevin : NPcomplete SAT`). The theorem typechecks but is
**conditional** — on ~29 skeleton `sorry`s *and* on several `sorry`-free
vacuous reductions. The strategy for making it real is the **higher-level
computable layer**: a small while-language (`Cmd`) with cost semantics, which
is **compiled once** to a `FlatTM` (`Compile`), so every verifier and reduction
is written as a `Cmd` instead of hand-rolling Turing machines. Whether that
strategy *converges* hinges on one unbuilt, untouched piece:

> **`loopTM` — the counted-loop combinator over `FlatTM`s, and its run lemma.**

Your job is a **time-boxed go/no-go probe** (exactly like the recently-completed
Cook-tableau probe — see the ROADMAP iteration log). Build enough of `loopTM`
to answer one question with evidence:

> **Is `loopTM` + its run lemma tractable to formalize in this codebase at a
> cost comparable to the per-primitive / composition work already done — or
> does it balloon the way the abandoned hand-rolled approach did?**

A clean "yes, here is a worked combinator + run lemma + a constrained
`compileForBnd_sound` slice, and a realistic estimate" and a clean "no, here is
precisely where it explodes, recommend the fallback" are **both successful
outcomes**. Do not try to close everything.

### Why this is *the* biggest current risk

- **It gates the entire layer.** Every layer→framework bridge in
  `Lang/PolyTime.lean` (`DecidesLang.toDecidesBy`, `inTimePolyLang_to_inTimePoly`,
  …) reduces to `Compile_sound`. `Compile_sound` is assembled from four
  per-constructor lemmas, one of which is `compileForBnd_sound`, which is
  `sorry` *"land `loopTM` first, then apply its run lemma."* No `loopTM` ⇒ no
  `Compile_sound` ⇒ no real (TM-backed) `inTimePoly` ⇒ the framework's
  `polyTimeComputable` stays the **output-size-only** version (Risk **S3**),
  which is exactly the weakness that lets the vacuous reductions (Risks **S1**,
  **S2**) typecheck. So `loopTM` is upstream of retiring S3, which is upstream
  of forcing S1/S2 to become real reductions.
- **Every verifier needs it.** The SAT verifier (`Deciders/EvalCnfCmd.lean`)
  and the clique reduction iterate clauses × literals via `Cmd.forBnd`.
- **It was the dominant cost of the approach we abandoned.** Per ROADMAP
  Appendix A, the hand-rolled iteration bookkeeping was **~600 + ~400 LOC per
  loop site**. The whole point of the pivot was to pay that *once* in `loopTM`.
  Nobody has tried. C1 (per-primitive) and C2 (composition) are validated;
  `loopTM` is the last structural unknown. If it is ≲ the per-op cost, the
  layer's cost model is fully validated and the rest of Group C is bounded
  engineering. If it balloons, that is the signal to trigger the **Fallback
  plan** *before* building the verifiers.

## 2. Background: what is real, what you are unblocking

The compiler maps each `Cmd` constructor to a TM combinator:

| `Cmd` constructor | Compiles to                                          | status |
|-------------------|------------------------------------------------------|--------|
| `op o`            | a small per-op TM                                    | `appendOne`/`appendZero` real; 6 ops stubbed |
| `seq c1 c2`       | `composeFlatTM r1.M r2.M r1.exit`                    | **real; composition proven** (C2) |
| `ifBit t cT cE`   | `branchComposeFlatTM tester rT rE e_pos e_neg`       | structure done; tester stubbed |
| `forBnd c b body` | **`loopTM rb.M` with a counter / bound thread**      | **STUB — your target** |

- **The physical contract (your foundation).** C2 established — and *proved* in
  `compileSeq_compose_physical` (`Lang/Compile.lean`, ~line 1050) — the contract
  under which compiled fragments compose: a fragment, run on
  `initFlatConfig M [encodeTape s]`, halts at its `exit` state at an **explicit
  step `t`**, with the **head rewound to index `0`** and tape **exactly
  `encodeTape (output)`**, along a **no-early-halt trajectory** (it does not hit
  `exit` or any halting state before step `t`). With head `0`, a fragment's exit
  config *is* literally `initFlatConfig` of the next fragment — which is exactly
  what makes both `composeFlatTM_run` and (you will argue) a loop body's
  iteration plug together. **Build `loopTM`'s run lemma against this same
  contract**, treating the loop body `rbody` as a black box that satisfies it.
- **The template.** `composeFlatTM_run` (`Complexity/TMPrimitives.lean`, from
  ~line 268) is the model proof: it lifts `M₁`'s run, then the bridge edge, then
  `M₂`'s run into the composed machine via per-phase `stepFlatTM_*` lemmas and a
  `state_idx`-range invariant. `loopTM`'s run lemma is the **iterated** analogue
  — induct on the iteration count, with the body phase + decrement + loop-back
  bridge per iteration. Expect it to be the bulk of the work (composeFlatTM_run
  alone is a large share of TMPrimitives' ~3,460 lines).
- **You are NOT finishing the verifiers, the bridges, or S3.** You are
  validating the one combinator they all wait on. Leave `compileForBnd_sound`'s
  full statement as a `sorry` if you only prove a slice; the build must stay
  green and the existing skeleton unchanged except additively.

## 3. Read these first (in order)

1. `CookLevin/ROADMAP.md` — "Status update", the **Risk register** (Group **S**
   for *why this matters* — esp. S3; Group **C** where you are **C3**), the
   **"Reordered ranking (post-C1/C2)"** note, **Appendix A** (the loop-cost
   lesson), and the **Fallback plan** (your recommendation (iii)). Also read and
   follow the **"Development strategy: skeleton-first"** discipline (root README).
2. `CookLevin/Complexity/Lang/Semantics.lean` — the **`forBnd` semantics**
   (`Cmd.run`, lines 78–86): iterate `(s.get bound).length` times; on iteration
   `i` set `counter := List.replicate i 1` (a **unary** loop index), run `body`,
   fold `(state, cost)`. Your `loopTM` must realize exactly this.
3. `CookLevin/Complexity/Lang/Compile.lean` — the target and its contract:
   - the file header §"Skeleton status" point **5** (loopTM gap);
   - `compileForBnd` (the `compiledCmd_default` stub, ~line 672) and
     `compileCmd`/`Compile` (~680–690);
   - **`compileForBnd_sound`** (~line 1109) — the exact obligation, including
     the `folded` fold you must reproduce, and the step budget
     `Compile.overhead (State.size s + 1 + folded.2 + iters)`;
   - **`compileSeq_compose_physical`** (~line 1050) — your contract + the
     `composeFlatTM_run` application pattern to imitate;
   - the encoding: `Compile.endMark = 3`, `sig = 4`, `Compile.encodeTape` /
     `Compile.decodeTape` (~lines 744–930) and `Compile.overhead` (~970).
4. `CookLevin/Complexity/Complexity/TMPrimitives.lean` — `composeFlatTM` (~80),
   `composeFlatTM_valid` (~167), and the **`composeFlatTM_run`** proof
   architecture (~268 onward: the `stepFlatTM_composeFlatTM_{M1,bridge,M2}`
   phase lemmas, `state_idx_lt_states_of_run`, the phase-lift lemmas). This is
   the technique you will reuse/adapt. Also look at how `branchComposeFlatTM` is
   built (the two-exit branch machine) — a conditional is half of a loop.
5. `CookLevin/Complexity/Lang/Syntax.lean` — `Cmd`, `Op`, `Var`, `State`
   (`State.get`/`State.set`/`State.size`), and the `forBnd counter bound body`
   constructor.
6. `CookLevin/Complexity/Lang/PolyTime.lean` — see how `Compile_sound` flows up
   into `DecidesLang.toDecidesBy` etc., so you understand what landing
   `compileForBnd_sound` unblocks (this is the S3 retirement path).
7. **Coq reference** for the iteration pattern (port, don't invent): the L /
   `LM` loop and the multi-step relation lemmas under `coqdoc/` (search the
   `…CookLevin…` and `…TM_single…` dumps for `loop` / `relpower` /
   `loop_relpower_agree` — the single-tape file `…Subproblems.TM_single.txt`
   has the `relpower`↔`loop` agreement that motivates the inductive shape).

## 4. The construction you are building

A single-tape, unary-counter counted loop. Standard shape (mirror
`branchComposeFlatTM` for the guard, `composeFlatTM` for the body wiring):

```
loopTM body :=
  guard:  test whether the counter region is empty
            ├─ empty  → exit
            └─ nonempty → body ⨾ decrement-counter ⨾ (loop back to guard)
```

- **Counter.** The `forBnd` index is `List.replicate i 1` in a designated
  `counter` register; the iteration count is `(s.get bound).length`. The natural
  TM realization: initialize the counter region from `bound`, then "while
  counter nonempty: run `body`; remove one mark from the counter." Decide and
  document the exact register layout (you own `sig = 4`; reuse `endMark`/the
  leading sentinel from C1/C2 for navigation, don't add alphabet symbols
  casually — see subtlety (d)).
- **States.** Like `composeFlatTM`, you must designate an `exit` state and keep
  `halt.length = states`, `tapes = 1`, `sig = 4`. The loop-back is a bridge edge
  from the end of one iteration to the guard (the new wrinkle vs. `composeFlatTM`,
  whose only bridge goes *forward*).
- **Run lemma (the heart).** State it against the physical contract: *if `body`,
  from any `initFlatConfig body.M [encodeTape s']`, halts at `body.exit` with
  head `0` and tape `encodeTape (evalBody s')` at step `t(s')` along a
  no-early-halt trajectory, then `loopTM body`, from `initFlatConfig … [encodeTape s]`,
  halts at its `exit` with head `0` and tape `encodeTape (folded.1)` at the
  summed step budget, no-early-halt.* Prove by **induction on `iters`** (or on
  the counter length), each step = one body phase + decrement + loop-back, lifted
  into `loopTM`'s state space exactly as `composeFlatTM_run` lifts its phases.

## 5. The work plan — cheapest experiments first, STOP when you have an answer

Do these in order. After each, **commit (green build) and record findings.**
You may stop after step C with a verdict.

**(A) Define `loopTM` as a real, total `FlatTM` combinator** (+ the structural
lemmas: `states`/`start`/`sig`/`tapes`/`halt.length`, and `_valid`). Mirror
`composeFlatTM` + `branchComposeFlatTM`. *This alone is valuable*: it proves the
loop's shape (guard + body + decrement + loop-back, single exit) is expressible
and valid. Expect the loop-back bridge edge to be the one genuinely new piece.

**(B) Prove the run lemma for the trivial iteration counts.** `iters = 0`
(counter empty ⇒ guard exits immediately, state unchanged) and **`iters = 1`**
(one body phase, then decrement empties the counter, then exit). `iters = 1` is
the real signal: it exercises the body phase-lift, the decrement, *and* one
loop-back/guard cycle. Measure: how many phase lemmas, how painful is the
loop-back edge vs. the forward bridge in `composeFlatTM_run`?

**(C) Prove the general run lemma by induction on `iters`** — *or*, if that is
where it explodes, a constrained slice (e.g. `body = identity`/no-op, so
`evalBody = id` and the per-iteration tape is invariant, isolating the
loop-control bookkeeping from the body's tape effects). Then discharge a
matching slice of **`compileForBnd_sound`** (e.g. `iters = 0`, or the
identity-body case). Measure LOC and which sub-lemmas dominate.

**Then write the verdict** (§7). Do **not** push on to wiring `loopTM` into a
real `compileForBnd`, the verifiers, or `Compile_sound` unless A–C went smoothly
and you have budget.

## 6. Known subtleties / likely gotchas — resolve from the existing code, don't guess

- **(a) The loop-back bridge edge.** `composeFlatTM_run` only ever bridges
  *forward* (M₁.exit → M₂.start). A loop adds a *backward* edge (end-of-iteration
  → guard). The `state_idx`-range invariant and the no-early-halt trajectory
  argument must survive re-entry into the guard. This is the main new proof
  obligation; budget for it.
- **(b) Termination / induction measure.** The run lemma's induction is on the
  iteration count (counter length), which *decreases* by one per iteration —
  not on a `Cmd`. Make sure the decrement gadget provably shrinks the counter
  region so the induction is well-founded and the step budget sums correctly.
- **(c) Threading the physical contract through iterations.** Each iteration
  starts from a head-`0`, `encodeTape`-shaped config (so it *is* an
  `initFlatConfig` for the body) and must end the same way *with the counter
  decremented*. The body's contract gives head-`0`/`encodeTape` for the *body's*
  registers; you must show the decrement preserves the contract for the counter
  region and re-establishes head `0` for the next guard test. Reuse the
  `scanLeftUntilTM` head-rewind gadget (`Lang/ScanLeft.lean`).
- **(d) Alphabet discipline.** `sig` is fixed at 4 (`0` delim, `1`/`2` shifted
  bits, `3` = `endMark`). Realize the counter/guard with the existing symbols
  and the leading-sentinel convention; adding a symbol ripples through every
  `_sig`/`_valid` lemma and the encoding. If you genuinely need one, record it
  as a finding (cf. Risk C5) rather than quietly widening `sig`.
- **(e) Cost/step accounting.** `compileForBnd_sound`'s budget is
  `Compile.overhead (State.size s + 1 + folded.2 + iters)`. Your run lemma's
  explicit step count must be ≤ this. The `+ iters` is the per-iteration loop
  overhead; make sure your decrement+guard cost is `O(L)` per iteration so it
  fits. If the real per-iteration cost is super-linear, that is a finding.
- **(f) Don't wire it in destructively.** Land `loopTM` + lemmas additively in
  `TMPrimitives.lean` (and, if you slice `compileForBnd_sound`, keep the full
  `sorry` untouched alongside the slice). The downstream sound chain and the
  build must stay green.

## 7. What to deliver (the verdict)

A short written report (final message and/or appended to `ROADMAP.md`'s
iteration log) answering:

1. **Is it tractable?** Did A–C go through? Where, precisely, did difficulty
   concentrate (the loop-back bridge? the induction/termination? threading the
   physical contract + counter decrement? the no-early-halt trajectory across
   re-entry?).
2. **Realistic cost.** Your revised LOC estimate for a complete `loopTM` +
   run lemma + `compileForBnd_sound`, calibrated against what you saw and
   against `composeFlatTM_run`'s actual size. (Appendix A's prior data point:
   ~1,000 LOC per loop site hand-rolled; the layer should pay it *once* — is
   that holding?)
3. **Recommendation.** One of: (i) feasible — proceed, the layer's cost model
   is validated, here is the order for the remaining Group C; (ii) feasible but
   expensive — proceed only after X; (iii) intractable as scoped — **trigger the
   Fallback plan** (state Cook–Levin conditionally on a documented `inTimePoly`
   axiom interface) rather than sinking the engineering. All three are
   legitimate; this probe exists to make that call on evidence.
4. Any new structural gaps for the Risk register.

## 8. Workflow & guardrails

- **Build:** `export PATH="$HOME/.elan/bin:$PATH" && lake build`. First build is
  slow (mathlib) — start it in the background early. Build green between commits.
- **Scope of edits:** primarily `Complexity/TMPrimitives.lean` (the `loopTM`
  combinator + run lemma) and `Lang/Compile.lean` (wire `compileForBnd`, slice
  its `_sound`). Small new helper files under `Lang/` are fine. **Do not modify**
  the proven downstream (`FlatTCC.lean` semantics … `BinaryCC_to_FSAT.lean`) or
  the framework (`MachineSemantics.lean`, `Definitions.lean`) except additively.
- **No new `axiom`s and no shortcuts.** `loopTM` must be a genuine, total,
  valid `FlatTM`. Keep proofs axiom-clean (only `propext` / `Classical.choice` /
  `Quot.sound`); verify with the Lean LSP `lean_verify` tool if available.
- **Methodology:** skeleton-first / decompose-don't-elaborate. If the run lemma
  resists, split its `sorry` into per-phase sub-lemmas (as `composeFlatTM_run`
  does) and record the gap rather than grinding.
- **Git:** commit to your assigned feature branch (do not push to `main`); clear
  messages; follow the repo's commit conventions; create a PR only if asked.
- **Reference, don't reinvent:** mirror `composeFlatTM_run`'s phase technique and
  the Coq `loop`/`relpower` agreement; this is a port of a known construction.
