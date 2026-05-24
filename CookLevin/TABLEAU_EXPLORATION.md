# Agent brief: explore the feasibility of the Cook tableau (Risk S1)

> **Handoff document.** This is a self-contained brief for an agent picking up
> the Cook-tableau feasibility probe. It assumes no prior context. Read it
> top to bottom, then read the files in §3 before writing any code.

## 1. Mission

This project formalizes the Cook–Levin theorem in Lean 4
(`theorem CookLevin : NPcomplete SAT`). The theorem currently typechecks but
is **not a faithful proof**: the central reduction "a Turing machine accepts
its input iff a tableau is satisfiable" is **faked** by a case split on the
answer. Your job is **not** to finish that reduction. Your job is a
**time-boxed feasibility probe**: build enough of the real Cook tableau
construction to answer one question with evidence —

> **Is the tableau construction + its correctness bijection tractable to
> formalize rigorously in this codebase, and roughly at what cost?**

This is the single biggest *unvalidated* risk in the project. The
"higher-level computable layer" (the other big workstream) has already been
load-tested and looks viable; the tableau has not been touched on the proof
path. We want to know if it is feasible **before** investing thousands more
lines elsewhere. A clean "yes, here is a worked slice and a realistic
estimate" or a clean "no, here is precisely where it breaks" are **both
successful outcomes**. Do not try to close everything.

## 2. Background: where the fake is, and what the real target is

The proof reduces along a chain. The **second half is real, proven
mathematics** and you must not break it:

```
FlatSingleTMGenNP  ⪯p  FlatTCC  ⪯p  FlatCC  ⪯p  BinaryCC  ⪯p  FSAT  ⪯p  SAT
       ^^^^^^^^^^^^^^^^^^^^^^^^                  (all of this is sound, proved)
       THIS ARROW IS FAKED (Risk S1)
```

- **`FlatTCC`** is a 2D "tiling / covering" problem (a flattened *Three-Cell
  Covering* instance). Its language `FlatTCC.FlatTCCLang` and the downstream
  chain `FlatTCC → FlatCC → BinaryCC → FSAT → SAT` are fully proved. You are
  producing **inputs** to this sound machinery.
- The faked arrow lives in
  `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`.
  Its reduction map `FlatSingleTMGenNP_to_FlatTCC_instance` is literally
  `if FlatSingleTMGenNP x then (a trivial all-zero tableau) else (a no-instance)`.
  The output depends on the *truth* of the source predicate, which a real
  many-one reduction may not do. This is why the theorem is currently vacuous
  on this segment.
- The **real target already has a skeleton** (orphaned, 5 `sorry`s,
  referenced by nothing yet):
  `CookLevin/Complexity/Simulators/CookTableau.lean`. It declares
  - `cookTableau (M : FlatTM) (s : List Nat) (steps : Nat) : FlatTCC` — the
    construction (currently a stub with empty fields),
  - `cookTableau_correct : acceptsFlatTM M [s] steps = true ↔ FlatTCC.FlatTCCLang (cookTableau M s steps)`
    — **the bijection (the heart)**,
  - `cookTableau_wellformed`, `cookTableau_size_bound` (+ poly/mono).

  Your work builds on / replaces this file.

## 3. Read these first (in order)

1. `CookLevin/ROADMAP.md` — sections "Status update", "Risk register"
   (Groups **S** and **C**; you are exploring **S1**), and **Part 6** (the
   intended tableau plan). Also read the **"Development strategy:
   skeleton-first"** discipline and follow it.
2. `CookLevin/Complexity/Simulators/CookTableau.lean` (78 lines) — your
   target file.
3. `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/FlatTCC.lean` — the
   covering semantics you must satisfy. Key defs (in `namespace TCC`, around
   lines 7–23):
   - `coversHead card a b := isPrefix card.prem a ∧ isPrefix card.conc b`
   - `validStep cards a b := a.length = b.length ∧ ∀ i, i + 3 ≤ a.length → ∃ card ∈ cards, coversHead card (a.drop i) (b.drop i)`
     — i.e. **every length-3 window of two consecutive rows is licensed by
     some card**.
   - `TCCLang C := wellformed C ∧ ∃ sf, relpower (validStep C.cards) C.steps C.init sf ∧ satFinal C.final sf`
     — start from the fixed `init` row, take `steps` covering-steps to some
     final row `sf`, which must contain a `final` pattern as a substring.
   - `FlatTCC.FlatTCCLang` (line 209) and the `flattenTCC` / `unflattenTCC`
     bridge between `TCC` (typed `Fin Σ`) and `FlatTCC` (flat `Nat`).
     **Tip:** define your construction at the typed `TCC` level and reuse
     `flattenTCC` + `flattenTCC_wellformed` + `isValidFlattening_flattenTCC`,
     exactly as the existing fake does with `mkTCCWitness`.
4. The structures `TCCCardP`, `TCCCard`, `FlatTCC`, `TCC` in
   `CookLevin/Complexity/Complexity/Definitions.lean:163–276`. A `TCCCard` is
   `{ prem conc : TCCCardP α }`, each `TCCCardP` is a triple
   `(cardEl1, cardEl2, cardEl3)`. Cards are **3-cell → 3-cell** rewrite
   windows.
5. `CookLevin/Complexity/Complexity/MachineSemantics.lean:142–151` —
   `execFlatTM` / `acceptsFlatTM` (the LHS of the bijection). Also skim
   `runFlatTM`, `stepFlatTM`, `FlatTMConfig` (a config is
   `{ state_idx, tapes }`; single tape `(left, head, right)`, `left = []`,
   `head` is an index into `right`).
6. `CookLevin/Complexity/NP/SAT/CookLevin/Subproblems/SingleTMGenNP.lean` —
   the source predicate:
   `FlatSingleTMGenNP (M, s, maxSize, steps) := … ∃ cert, isValidCert maxSize cert ∧ acceptsFlatTM M [s ++ cert] steps = true`.
   **Note the existential certificate** — see subtlety (c) below.
7. **The Coq reference** (this construction is already worked out there):
   `coqdoc/Complexity.NP.SAT.CookLevin.Reductions.SingleTMGenNP_to_TCC.txt`,
   plus `…PTCC_Preludes.txt` and `…Subproblems.TM_single.txt`. Mirror its
   design decisions; you are porting, not inventing.

## 4. The construction you are building (standard Cook tableau)

Encode a TM computation as rows of a tableau; a covering step = one TM step;
local 3-cell consistency = the transition relation.

- **Alphabet Σ.** Tape symbols, plus "head-marked" cells carrying
  `(state, symbol)`. The current stub uses `M.sig + M.states + 1`, which is
  almost certainly **too small** — you likely need room for
  `(state × symbol)` pairs (e.g. on the order of
  `M.sig + M.sig * (M.states + 1)` or a tagged union). Sizing Σ correctly is
  the first real design decision; copy the Coq encoding.
- **Row width.** A configuration as a row of fixed width `W` (the standard
  choice is `W = 1 + |s| + steps + 1` or similar, so the head never runs off
  the encoded tape within `steps` steps). All rows share width `W`.
- **`init`.** The start configuration as a row: head-marked first cell with
  `M.start`, then `s`, then blanks up to width `W`. (`wellformed` only needs
  `init.length ≥ 3`.)
- **`cards`.** All 3-cell windows `(a,b,c) ↦ (a',b',c')` that are consistent
  with `M`'s transition table — identity away from the head, and the local
  effect of a step around the head. This is the bulk of the construction.
- **`final`.** Patterns (substrings) that witness a halting state appearing
  in the final row.
- **`steps` = steps.**

`validStep`/`relpower`/`satFinal` then say exactly "there is a sequence of
`steps` rows from `init`, each consecutive pair locally consistent, ending in
a row that shows acceptance" — which is the run of `M`.

## 5. The work plan — cheapest experiments first, STOP when you have an answer

Do these in order. After each, **commit (green build) and record findings**.
You are measuring tractability; you may stop after step C with a verdict.

**(A) Make `cookTableau` a real, computable `def` (no `if`-on-answer).**
Fill in `Sigma`, `init`, `cards`, `final` with the real encoding (§4). It must
be a plain function of `(M, s, steps)`. Get it to typecheck. *This alone is
valuable*: it proves the encoding shape is expressible. Expect to also fix
`Sigma`'s size.

**(B) Prove `cookTableau_size_bound` (+ `_wellformed`).**
This is the easy end (the roadmap budgets ~200 LOC). It validates that the
encoding is polynomial-size and well-formed, and forces you to nail down
widths/Σ concretely. If this is hard, that itself is a finding.

**(C) Attempt ONE direction of the bijection `cookTableau_correct`, on a
constrained case.**
This is the load-bearing proof and the real feasibility signal. Recommended:
the **"run ⇒ tableau" (soundness) direction** — from an accepting run of `M`,
build the witnessing row sequence `sf` and show each `validStep` holds. Even
doing this for a **trivial machine** (e.g. a 1- or 2-state machine that halts
immediately, or with `steps = 0/1`) tells you whether the
`relpower`/`validStep`/window bookkeeping is manageable. Measure: how many
LOC, what infrastructure lemmas appear, do the `drop i`/window indices become
painful?

**Then write the verdict** (see §7). Do **not** push on to the full
bijection, the certificate-nondeterminism, or wiring the reduction unless
steps A–C went smoothly and you have time budget.

## 6. Known subtleties / likely gotchas — resolve these from the Coq port, don't guess

- **(a) Σ sizing & head-marker encoding.** The stub's `M.sig + M.states + 1`
  is suspect. Decide the symbol set explicitly (tape symbols + head-marked
  `(state,symbol)` cells). Get this right before B.
- **(b) Typed vs flat.** Build at the `TCC` (`Fin Σ`) level and `flattenTCC`
  it, reusing the existing flatten lemmas — that is how the fake
  `mkTCCWitness` does it and it avoids re-deriving `isValidFlattening`.
- **(c) Certificate nondeterminism.** The source is
  `∃ cert, M accepts (s ++ cert)`. The tableau must make this existential
  correspond to `TCCLang`'s `∃ sf` (choice of row sequence). In the standard
  construction the certificate cells in the initial region are "guessed" by
  the covering. **Check exactly how the Coq port handles the cert region** —
  this is the trickiest modeling point and is easy to get subtly wrong. For
  the *exploration*, you may first prove the bijection for the
  **no-certificate / `maxSize = 0`** case to sidestep this, and only note what
  the cert case needs.
- **(d) Single tape only.** `cookTableau_correct` is stated for `[s]` (one
  tape). Good — stay single-tape; do not entangle with the multi-tape
  simulator (a separate orphan, `Simulators/MultiToSingle.lean`).
- **(e) Off-by-one / width.** The window condition is `i + 3 ≤ a.length`; the
  head must not reach the row boundary within `steps`. Pick `W` so this holds
  and the `final` substring search works.
- **(f) Don't wire it in yet.** Leave
  `Reductions/FlatSingleTMGenNP_to_FlatTCC.lean` (the fake) untouched for now.
  Replacing it is the *completion* task; you are *exploring*. The build must
  stay green and the downstream sound chain unchanged.

## 7. What to deliver (the verdict)

A short written report (in your final message and/or appended to
`ROADMAP.md`'s iteration log) answering:

1. **Is it tractable?** Did A–C go through? Where, precisely, did difficulty
   concentrate (Σ encoding? card enumeration? the window/`drop i` bookkeeping
   in `validStep`? the cert nondeterminism)?
2. **Realistic cost.** Your revised LOC estimate for the full `cookTableau` +
   `cookTableau_correct` + size bound, given what you saw. (The roadmap's
   guess is ~2,700 LOC; the project has historically underestimated ~10×, so
   calibrate honestly.)
3. **Recommendation.** One of: (i) feasible — proceed and here is the order;
   (ii) feasible but expensive — proceed only after X; (iii) intractable as
   scoped — recommend the documented-axiom **fallback** (state Cook–Levin
   conditionally on a tableau/`inTimePoly` interface). All three are
   legitimate.
4. Any new structural gaps to add to the Risk register.

## 8. Workflow & guardrails

- **Build:** `export PATH="$HOME/.elan/bin:$PATH" && lake build`. The first
  build is slow (mathlib) — run it in the background early. Build green
  between commits.
- **Scope of edits:** primarily `Simulators/CookTableau.lean` (and small new
  helper files under `Complexity/Simulators/` or near `FlatTCC.lean` if
  needed). **Do not modify** the proven downstream (`FlatTCC.lean` semantics,
  `FlatTCC_to_FlatCC.lean`, … `BinaryCC_to_FSAT.lean`, the Tseytin transform)
  or the framework (`MachineSemantics.lean`, `Definitions.lean`) except
  additively.
- **No new `axiom`s and no `if`-on-the-answer.** The construction must be a
  genuine computable function. Keep proofs axiom-clean (only
  `propext`/`Classical.choice`/`Quot.sound`); verify with the Lean LSP
  `lean_verify` tool if available.
- **Methodology:** skeleton-first / decompose-don't-elaborate (see README
  "Development strategy"). If a piece resists, split its `sorry` into smaller
  ones and record the gap rather than grinding.
- **Git:** commit to the feature branch you are assigned (do not push to
  `main`/`master`); clear messages; follow the repo's existing commit-message
  conventions; create a PR only if explicitly asked.
- **Reference, don't reinvent:** the Coq file in §3.7 is the source of truth
  for the encoding; port its choices.
