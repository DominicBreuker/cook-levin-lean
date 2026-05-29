# Cook–Levin in Lean 4 — Roadmap

The strategy, **ordered plan**, and **risk register** for making `theorem
CookLevin : NPcomplete SAT` real and unconditional. Written for agents: it
states where the proof stands and what to do next. A living plan, not a history.

**Orientation.** The theorem typechecks but is **conditional**. The
combinatorial heart of Cook–Levin (a TM run → tableau → CNF → SAT) is real and
done (the *sound tail*). The *front* (universal NP source → single-tape TM) is a
compiling skeleton plus `sorry`-free but **vacuous** reductions. The plan to
make it real is the **computable layer**: a small while-language (`Cmd`) with
explicit cost semantics, compiled once to `FlatTM` (`Compile`), so every
verifier and reduction is a short DSL program instead of a hand-rolled TM.

---

## Status snapshot (verified 2026-05)

| | |
|---|---|
| `lake build` | ✅ green (3356 jobs) |
| `#print axioms CookLevin` | `[propext, sorryAx, Classical.choice, Quot.sound]` — **depends on `sorryAx`** |
| `axiom` declarations | **0** |
| Genuine `sorry`s (Group C) | ~31 |
| `sorry`-free **vacuous** defs (Group S) | several (S1, S2, size-0 hardness reduction) — invisible to `#print axioms` |
| Proof-path size | ~18K LOC under `CookLevin/`; ~15K parked |
| Remaining to a real proof | **~15–25K LOC** (breakdown below) |

> **The `sorry` count is not the soundness metric.** Closing every `sorry`
> leaves S1/S2/S3 intact. Track Group S (soundness) and Group C (completion)
> separately.

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
giving `CookLevin : NPcomplete SAT`. The in-NP half needs a real SAT verifier
(the layer's `evalCnfCmd`, C7 — currently `sorry`).

---

## What we know (validated foundations + this-session findings)

- **The sound tail is genuine.** `FlatTCC → FlatCC → BinaryCC → FSAT → SAT`,
  `kSAT_to_SAT`, `kSAT_to_FlatClique` are real reductions with real correctness
  proofs (audited). Their `if isValidFlattening …` guards test a decidable
  property of the *input*, which is legitimate. Do not touch their content; the
  only future change is re-threading the witness type (S3 migration).

- **The S3 target is faithful.** `polyTimeComputable'` (`ComputesBy`: a real
  `FlatTM` halting within a polynomial *time* bound and decoding to `f x`)
  captures genuine poly-time computation, and *extends* the size-only witness
  (`polyTimeComputable'_to_polyTimeComputable`), so the size-bound lemmas in
  `NP.lean` survive verbatim. The forcing function is confirmed
  (`s1_witness_forces_decider`): an honest witness for an if-on-the-answer map
  yields a poly-time decider for the NP source, which a many-one reduction may
  not have — so S1/S2 *stop typechecking* under the upgrade.

- **The layer composes (C9, C4, C6 — done, sorry-free modulo C2).**
  `LangEncodable` (canonical per-type single-register encoding) +
  `PolyTimeComputableLang'` (canonical normal form) + `comp` +
  verifier-composition `precompose`/`ofReduction` + the layer-native NP class
  `inNPLang`/`red_inNPLang` + the framework decider bridge `inNPLang_to_inNP`
  (via the `bitTestTM` tape→state gadget). Concrete witnesses: `id`,
  `constTrueBool`, `swap`, `map_fst`, `map_snd`; the `forBnd` loop toolkit
  (`eval_forBnd`, `foldlState_range_induct`, `cost_forBnd_le`). All
  `#print axioms`-clean except where the assumed `Compile_sound` enters.

- **S2 needs no simulator.** `TM σ n` erases the tape count (`TM_tapecount_phantom
  : TM Bool 2 = TM Bool 1` by `rfl`), the predicates ignore the machine, and
  `bridgeMachine` accepts everything. `LMGenNP` reduces *directly* to the
  single-tape target (`LMGenNP_to_TMGenNP_singleTM_direct`). Retiring S2 =
  collapse the phantom bridges and bind the predicates to the single-tape layer
  decider; **folds into C8**. `Simulators/MultiToSingle.lean` is dead code.

- **S1 is feasible but expensive.** The real Cook 2D tableau
  (`Simulators/CookTableau.lean`, 2 `sorry`s) is a genuine computable
  construction (no if-on-the-answer). Estimate ~6–11K LOC, bijection-dominated.
  Alphabet `|Σ|=(M.sig+1)(M.states+2)`; tableau size is **quartic** in `|Σ|`.

- **C2 is the linchpin — and is under-built (this session's headline finding).**
  Everything (both the reduction side `toFrameworkWitness'` and the decider side
  `inNPLang_to_inNP`) routes through `Compile_sound` / `Compile_run_physical`.
  The *combinators* are proven (`compileSeq_compose_physical`, `loopTM_run`,
  `bitTestTM`) and a ~1.6K-LOC gadget library is sorry-free. **But:**
  - 10 of 12 `compileOp`s are `compiledCmd_default` stubs; only
    `appendOne`/`appendZero` have real TM bodies.
  - All `compileOp_sound` / `compileSeq_sound` / `compileForBnd_sound` /
    `compileIfBit_sound` and the `Compile_sound` assembly are `sorry`.
  - **The gadget run-lemmas leave the step count *existential*** ("a step bound
    is a separate concern"). The polynomial step-bound accounting that
    `Compile.overhead (size + cost)` needs is essentially **unbuilt** — this is
    a distinct, sizeable obligation that prior estimates folded into "bounded
    engineering".
  - **Progress this session:** `compileOp_appendOne_behavioural`
    (`Lang/Compile.lean`, sorry-free, axiom-clean) proves the *behavioural* half
    of `compileOp_sound` for `appendOne` end-to-end — `Compile.opAppendOne dst`
    on `encodeTape s` decodes to `Op.eval (appendOne dst) s`. This is the first
    demonstration that the `encodeTape`/`decodeTape` contract and the gadget
    library compose (the encoding seam is sound), and it isolates the residual
    per-op gap to **purely the step bound**.

---

## The plan from here

Two destinations. The probes show the unconditional one (A) is **open** —
proceed there; (B) is the documented escape hatch.

### Destination A — real, unconditional `CookLevin`

Ordered by dependency. The two highest-risk items are **C2** (the compiler, now
known to need step-bound machinery) and **S1** (the Cook tableau).

1. **Finish the compiler `Compile_sound` (C2 — highest completion risk).**
   a. Build a **step-bound** layer over the gadget library: give each gadget
      run-lemma an explicit (or polynomial) step count, not just an existential.
      This is the newly-recognised bulk of C2. Recommended: state a per-fragment
      *physical contract* (head rewound to `0`, tape `= encodeTape output`,
      explicit halt step `t`, no-early-halt trajectory, `t ≤ overhead(...)`),
      and re-derive `appendOne`'s contract from `appendAt_run` + a step count —
      i.e. upgrade `compileOp_appendOne_behavioural` to the budgeted
      `compileOp_sound` shape.
   b. Concretise the 10 stub `compileOp`s from the gadget library (`opClear`,
      `opCopy`, `opTail`, `opHead`, `opEqBit`, `opNonEmpty`, and the four
      length-as-value ops), each with its budgeted `compileOp_sound`.
   c. Assemble `compileSeq_sound` from `compileSeq_compose_physical`,
      `compileForBnd_sound` from `loopTM_run`, `compileIfBit_sound` from
      `branchComposeFlatTM_run`; then `Compile_sound` / `Compile_run_physical` by
      induction. This discharges the one obligation the whole S3 bridge sits on.
   *Estimate ~3–5K LOC. No remaining structural unknown — the encoding seam is
   validated — but the step-bound accounting is real work.*

2. **Retire S3 — migrate `⪯p` to `polyTimeComputable'`.** Swap
   `ReductionWitness.reduction_poly` to the TM-backed witness (the strengthening
   lemma keeps size-bound lemmas valid). Infrastructure is built (`⪯p'`,
   `reducesPolyMO'_of_lang`, generic `LangEncodable (List α)` so chain types like
   `cnf = List (List (Bool × Nat))` derive automatically). The work is building
   *honest* `PolyTimeComputableLang'` witnesses:
   - **`map`-over-lists** (gates the whole sound tail; near-complete draft at
     `parked/MapNatList_WIP.lean`, two hard parts already sorry-free). Then the
     sound-tail reductions as `Cmd`s — `flatTCC_to_flatCC` cheap,
     `FlatCC_to_BinaryCC` medium, **`BinaryCC_to_FSAT` (Tseytin) the expensive
     tail item** (~1K-LOC formula builder re-expressed as a `Cmd`).
   - At this point **S1 and S2 stop typechecking**; the conditional theorem
     breaks until they are honest.
   *Estimate ~2–4K LOC.*

3. **Real front reductions.** Build the **S1 Cook tableau**
   (`Simulators/CookTableau.lean`, ~6–11K LOC) and the **C8** universal-source
   decider (single-tape via `Lang.DecidesLang`, which **subsumes the old S2
   simulator** — collapse the phantom bridges here).

4. **In-NP verifiers (C7).** `evalCnfCmd` (SAT) and `cliqueRelCmd`, as `Cmd`s,
   give `inNP SAT` / `FlatClique`. Gated on C2 making the layer→`DecidesBy`
   bridge real. *Estimate ~1–2K LOC.*

5. **Encodable sweep (Part 0.1).** Replace the size-0 `instEncodableDefault` on
   every chain intermediate (TCC/CC/BinaryCC/formula/GenNPInput/…) with a real
   `encodable.size`. Required because over a size-0 type even the honest
   `toFrameworkWitness'` is vacuous (`bound 0`), and the hardness reduction's
   `fun _ => 0` bound is only "valid" because of it. Pervasive but mechanical,
   *~0.5–1K LOC.*

**Total rough estimate: ~15–25K LOC**, dominated by the S1 tableau (3) and the
compiler step-bound machinery (1).

### Destination B — honest conditional theorem (fallback)

If C2 or the S3 tail ripple proves intractable for a side project, state
`CookLevin` conditionally on a **documented axiomatic `inTimePoly` / `⪯p`
interface**, keep the sound combinatorial tail, and stop. Trigger if step 1 or 2
overruns its estimate ~3×.

---

## Risk register

Two groups. **Group S** (soundness) determines *what the conditional theorem
currently means* — several entries are `sorry`-free. **Group C** (completion) is
the compiling-skeleton engineering. Refine the highest-ranked open item next.

### Group S — soundness gaps (mostly `sorry`-free, invisible to `#print axioms`)

| # | Gap | Location | Status / fix |
|---|-----|----------|--------------|
| **S3** | `⪯p` bounds **output size only** — the enabling weakness that lets S1/S2 typecheck and makes `NPcomplete` too weak to be faithful. | `NP.lean`, `Lang/PolyTime.lean` | **Probed feasible.** Honest target `polyTimeComputable'` built (sorry-free modulo C2). Execute via plan step 2. |
| **S1** | **if-on-the-answer** `FlatSingleTMGenNP ⪯p FlatTCC` (all-zeros tableau, never simulates `M`). Deepest unsoundness. | `Reductions/FlatSingleTMGenNP_to_FlatTCC.lean` | **Probed feasible but expensive (~6–11K LOC).** Real fix = Cook 2D tableau (`Simulators/CookTableau.lean`). Gated on S3 (plan step 3). |
| **S2** | **dummy TM bridges** — `bridgeMachine` discards `M`; predicates ignore `M`. | `LM_to_mTM.lean`, `mTM_to_singleTapeTM.lean` | **No simulator needed** (probed). Collapse phantom bridges; **folds into C8**. |
| **S0** | **hardness reduction is vacuous** — `NPhard_GenNP` uses output-size bound `fun _ => 0` (only "valid" via size-0 `instEncodableDefault`) and `hasDeciderClassical` (`sorry`). | `GenNP_is_hard.lean` | Closes with C8 (real universal decider) + Part 0.1 (real `encodable.size`). |
| **Part 0.1** | `instEncodableDefault` gives `size = 0`; over a size-0 type even honest bounds are vacuous. | `Definitions.lean` | Hard requirement; plan step 5. Pervasive but mechanical. |

### Group C — completion risks (the compiling skeleton)

| # | Gap | Status |
|---|-----|--------|
| **C2** | **compiler soundness** `Compile_sound` / `Compile_run_physical`. | ⚠ **Highest completion risk, under-built.** Combinators proven; gadget library sorry-free; encoding seam validated this session (`compileOp_appendOne_behavioural`). **Open:** 10/12 `compileOp` stubs, all `compileOp_sound`, and — newly recognised — the **polynomial step-bound accounting** (gadget steps are existential). Plan step 1. |
| **C1** | **per-`Op` compilation** (`compileOp` + soundness). | Only `appendOne`/`appendZero` have real TMs; behavioural soundness of `appendOne` proven. Rest stubbed. Part of C2. |
| **C3** | **`loopTM` counted loop** (`compileForBnd` + soundness). | `loopTM`/`loopTM_run` proven; behavioural `forBnd` toolkit (`Lang/Frame.lean`) proven. Wiring `compileForBnd` + its step bound is part of C2. |
| **C4** | **layer → framework bridge.** | ✅ Engine done (`toFrameworkWitness'`, `inNPLang`/`red_inNPLang`, `inNPLang_to_inNP`, capstones `reducesPolyMO_of_lang`/`red_inNP_of_lang`), sorry-free modulo C2. Remaining: honest layer reductions (S1) + discharge C2. |
| **C6** | **bit-test tester.** | ✅ `bitTestTM` (tape→state, register 0) sorry-free, used by the decider bridge. General `compileTestBit t` (arbitrary register) still a stub (part of C1). |
| **C7** | **verifier bodies** — `evalCnfCmd` (SAT, gates `inNP SAT`), `cliqueRelCmd`. | `def := sorry` stubs + `sorry` proofs. DSL engineering; gated on C2. Plan step 4. |
| **C8** | **real `NPhard_GenNP`** (`hasDeciderClassical`). | The universal-source decider, single-tape via `Lang.DecidesLang` (subsumes S2). Needs C4+C2. Plan step 3. |
| **C5/C5a/C9** | DSL expressiveness; `map_fst`; canonical encoding. | ✅ Done (`map_fst`/`swap`/`map_snd`, `LangEncodable`, `forBnd` toolkit). Add new `Op`s only when one materially shortens a verifier (each new `Op` = another soundness proof). |

---

## How we work — skeleton-first, risk-driven

Learned the hard way in the May 2026 pivot (the hand-rolled Part 2 blew up ~10×
because structural issues were invisible until attempted). **Do not deviate
without an explicit reason.**

1. **Skeleton first, then refine.** A compiling skeleton exposes every
   downstream obligation; an isolated proof exposes nothing.
2. **Refine the highest-risk gap next** (per the register), not in phase order.
3. **Decompose `sorry`s, don't elaborate them.** Each split is a structural
   decision that typechecks (right shape) or fails (gap found). The
   behavioural/cost split of `compileOp_sound` this session is an example.
4. **Prefer concrete `def` + `sorry` over `axiom`** (currently 0).
5. **Probe before committing engineering.** Time-boxed go/no-go: assume lower
   layers, validate the structure additively, measure, verdict.
6. **Build green between commits; record gaps in commit messages.**

### Hard-won gotchas (you WILL hit these)

- **`omega` cannot see through `Var := Nat` for *variables*.** A register
  `r : Var` (or a literal ascribed `(0 : Var)`) is opaque to `omega` (`↑`
  coercions, "no usable constraints"). Restate at `Nat` or use explicit
  `Nat.*` lemmas (`Nat.min_eq_left`, `Nat.lt_of_le_of_ne`, …). `omega` *does*
  work on genuinely-`Nat` terms (`regBound`, cost/size bounds).
- **Avoid nested `set`/`let` chains over `State.set`/`State.get`** — `isDefEq`
  blows up exponentially (×8 per level). Flatten with one
  `simp only [Cmd.eval_op, Op.eval]`.
- **`.get` mis-resolves on `State` *literals*** (picks `List.get`, wants `Fin`).
  Write `State.get s r` explicitly on literals.
- **`set` lives only in `PolyTime.lean`, not `Frame.lean`** (the latter is
  core-only, no Mathlib tactics).

---

## Why the layer (and why not hand-rolled TMs)

Building a useful algorithm directly from `FlatTM`s ran ~10× over budget;
continuing projected Parts 2–6 at ~100–150K LOC. The lessons:

1. **Per-state lemmas don't amortise across primitives** — each primitive needs
   its own step/scan/run lemmas. The layer pays TM construction *once*.
2. **Iteration bookkeeping was the dominant cost** (~1000 LOC/loop site). The
   layer pays it once in `loopTM`.
3. **Single-tape with a delimiter scratch is the only economical shape** for
   composition (multi-tape needs `(sig+1)^k` bridge entries). This is also why
   the S2 multi-tape detour is unnecessary.
4. **The layer needs *cost* in its semantics, not just behaviour** — mathlib's
   `Computable`/`Partrec` handles computability but not complexity.

The Coq port avoids the blow-up by extracting TMs from the L-calculus; the layer
is the Lean analogue (a total structured while-language vs a general
λ-calculus). Parked hand-rolled work (~15K LOC) lives under `parked/`.

---

## References

- Coq source: <https://github.com/uds-psl/cook-levin>; local mirror `coqdoc/`.
- Status / orientation: root [`README.md`](../README.md).
- Parked work: `parked/README.md`, `parked/PART2.md`.
