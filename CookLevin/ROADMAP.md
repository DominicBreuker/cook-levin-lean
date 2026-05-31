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
| `lake build` | ✅ green (3357 jobs) |
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
  - The gadget run-lemmas *do* carry explicit step counts at the lower level
    (`scanInsert_run`, `insertCarryTM_run`: `body.length + … + post.length + …`);
    only the top-level `appendAt_run` existentializes them. So step counts are
    recoverable — but they expose a **cost-model bug** (next bullet).
  - **`compileOp_sound` is FALSE as stated** — and there are now **three
    independent reasons** (reasons 1–2 below; the third, the *budget shape*, is
    the May-2026 finding recorded after these).
    1. *(register-count bug, prior session)* Its budget `Compile.overhead
       (State.size s + cost)` uses `State.size`, which counts register *contents*
       but **ignores the register count**, whereas `appendAtTM`'s step count grows
       with the **tape length** `(encodeTape s).length = State.size s + s.length +
       1`. Witness: `s = List.replicate 6 []` has `State.size s = 0`, budget
       `overhead 1 = 4`, but `opAppendOne 0` first halts at **step 10**. Partial
       fix: the per-op budget over the **tape length**
       `Compile.overhead ((encodeTape s).length + cost)`. **This is now PROVEN for
       the real ops** — see "Progress this session".
    2. **(cost-model gap — now FIXED).** The original ops were **unit cost**
       (`Op.cost _ _ = 1`), but `concat`/`copy`/`tail`/`takeAt`/`dropAt`/`consLen`
       can grow `State.size` **multiplicatively** in one step. So a unit-cost
       program could have **output size exponential in its layer cost** (evaluated:
       `doubler := forBnd 2 1 (op (concat 0 0 0))` at `n = 10` → output length 1047
       vs even the corrected budget 676; at `n = 19`, 524329 vs 1936). **No
       fixed-degree budget polynomial could bound `Compile c`** — the unit-cost
       model was not a faithful proxy for TM time. **Fix implemented (the chosen
       option, Coq-L-calculus-aligned):** `Op.cost` now charges the size-increasing
       ops for their source data, so `State.size (Op.eval o s) ≤ State.size s +
       Op.cost o s` (`Op.size_eval_le`, proven; it was *false* under unit cost).
       *Options weighed:* (a) a separate per-witness size/weight bound and (c)
       removing size-increasing ops were both rejected — there is **no global
       `weight ≤ poly(unitCost, size)`** (size-doubling has weight exponential in
       op count), so the realistic single cost notion is necessary and lowest in
       permanent complexity; (c) is mathematically identical but needs surgery on
       the `Op` inductive. The concrete witnesses' cost bounds were re-derived
       (`id`, `swap`, `map_fst`), since their unit-cost bounds certified the wrong
       quantity. The **Cmd-level** residual (the `forBnd` counter) is **now CLOSED**
       — see reason 3 / Progress.
    3. **(budget shape — NEW, May 2026; the per-fragment budgets cannot compose).**
       The corrected per-op budget was loosened to the **quadratic** `overhead
       (tapeLen + cost) = (·+1)²`. But a quadratic is **not superadditive**, so
       summing `~cost` per-op quadratics gives a **cubic** — the per-fragment
       budgets in `compileSeq_sound`/`compileIfBit_sound`/`compileForBnd_sound` (and
       hence `Compile_sound`) are too weak to imply their composed conclusions:
       worst case `overhead(a) + 1 + overhead(a + c₂) ≤ overhead(a + 1 + c₂)` is
       **false for `a ≥ 2`** (`a = 3, c₂ = 1` → `42 ≰ 36`; gap grows with `a`). So
       **these four lemmas are unprovable as stated.** Fix: per-fragment budgets
       must be **LINEAR** in tape length — the gadgets prove it
       (`appendAt_steps_le: ≤ 2·tapeLen+3`), and linear bounds *do* compose into a
       quadratic total (`Σ_{~cost} O(tapeLen) ≤ O(cost·(size+cost+regBound)) =
       O((size+cost)²)` as `cost ≤ size+cost`). The **total** `Compile_run_physical`
       budget then needs a quadratic with constant/`regBound` slack (the tight
       `(size+cost+1)²` cannot cover constants; safe — `toFrameworkWitness'` only
       needs `inOPoly`). See the finding block above `compileSeq_sound` in
       `Compile.lean`.
  - **Progress** (`Lang/AppendGadget.lean`, `Lang/Compile.lean`, `Lang/Semantics.lean`,
    `Lang/Frame.lean`, `Lang/PolyTime.lean`; all sorry-free & axiom-clean):
    `appendAt_run_steps` re-proves `appendAt_run` with an **explicit step count**
    (`appendAt_steps`), `appendAt_steps_le` bounds it by `2·tapeLen + 3`, and
    `compileOp_appendOne_sound`/`compileOp_appendZero_sound` discharge the
    behavioural part of `compileOp_sound` for the two real ops at **general `dst`**
    (reason #1 closed for them, modulo the budget-shape restatement in reason #3).
    The **realistic cost model** (reason #2) is implemented: `Op.cost` size-aware,
    `State.size_set_add` + `Op.size_eval_le`, `Op.cost_agree`/`Cmd.cost_agree`
    generalized, witnesses re-derived. **The Cmd-level size bound (reason #2
    residual) is now PROVEN:** `Cmd.size_eval_le : State.size (c.eval s) ≤
    State.size s + c.cost s`, by charging the `forBnd` counter (`Cmd.run` adds
    `iters*iters`) — clean and depth-constant-free, replacing the proposed
    register-exclusion route. **Surfaced reason #3** (budget shape) by checking the
    arithmetic of the sorried per-fragment lemmas.

---

## The plan from here

Two destinations. The probes show the unconditional one (A) is **open** —
proceed there; (B) is the documented escape hatch.

### Destination A — real, unconditional `CookLevin`

Ordered by dependency. The two highest-risk items are **C2** (the compiler, now
known to need step-bound machinery) and **S1** (the Cook tableau).

1. **Finish the compiler `Compile_sound` (C2 — highest completion risk).**
   a. **Cost model — DONE.** `Op.cost` is size-aware (`Op.size_eval_le`), and the
      **Cmd-level size bound is now proven**: `Cmd.size_eval_le : State.size
      (c.eval s) ≤ State.size s + c.cost s` (`Lang/Semantics.lean`), sorry-free and
      axiom-clean. The clean bound *was* false for `forBnd` (the unary loop counter
      is uncharged size); rather than the register-exclusion route (depth-dependent
      constant), it was fixed by **charging the counter in the cost model** — the
      same faithfulness principle as the size-aware `Op.cost` (materialising
      `replicate i 1` costs Θ(i) TM steps). `Cmd.run`'s `forBnd` now adds
      `iters*iters` (closed-form lump ≥ Σ_{i<iters} i, kept outside the fold so the
      frame/locality lemmas are untouched). Ripples were contained:
      `Cmd.cost_forBnd_le` (+ `iters*iters`, no external consumers) and
      `Cmd.cost_agree`. This gives `maxIntermediateTapeLen ≤ O(size + cost +
      regBound)` (linear, no depth constant). **The linear tape-length bound is
      now PROVEN:** `Cmd.encodeTape_eval_length_le : (encodeTape (c.eval s)).length
      ≤ State.size s + c.cost s + max s.length k + 1` (`Lang/PolyTime.lean`), built
      from `Compile.encodeTape_length` (tape = contents + count + 1),
      `Cmd.size_eval_le` (contents), and `Cmd.eval_length_le` (register count ≤
      `max start regBound`, `Lang/Frame.lean`). **Remaining (1a):** thread this
      *per-fragment output* bound through the actual run as a **max over fragment
      boundaries** (needs the physical run structure from 1b/1d), then restate
      `PolyTime.toFrameworkWitness'`'s time budget.
   b. **⚠ Budget shape — FINDING (do not prove the four `compile*_sound` lemmas as
      stated).** The per-op budget had been loosened to the **quadratic**
      `Compile.overhead ((encodeTape s).length + cost) = (·+1)²`. That is the
      **wrong direction**: quadratics are not superadditive, so summing `~cost`
      per-op quadratics gives a **cubic**, and
      `compileSeq_sound`/`compileIfBit_sound`/`compileForBnd_sound`/`Compile_sound`
      are **unprovable as stated** — worst case `overhead(a)+1+overhead(a+c₂) ≤
      overhead(a+1+c₂)` is false for `a≥2` (numerically: `a=3,c₂=1` → `42 ≰ 36`).
      Fix: state each per-fragment budget **LINEAR** in tape length — the gadgets
      prove it (`AppendGadget.appendAt_steps_le: steps ≤ 2·tapeLen+3`), and the
      append ops **now carry that linear budget** (`compileOp_appendOne_sound` /
      `compileOp_appendZero_sound`, the `decodeTape`-equality form). Linear bounds
      compose: `Σ_{~cost frags} O(tapeLen) ≤ O(cost·(size+cost+regBound)) =
      O((size+cost)²)` since `cost ≤ size+cost`. Then the **total**
      `Compile_run_physical` budget must be a quadratic **with constant/`regBound`
      slack** (e.g. `C·(size+cost+regBound)²` or a cubic) — the tight
      `(size+cost+1)²` cannot cover the constants; safe since `toFrameworkWitness'`
      only needs `inOPoly`. Thread the register count (≤ `regBound`) and give each
      gadget a per-fragment *physical contract* (head rewound to `0`, tape
      `= encodeTape output`, explicit halt step `t`, no-early-halt trajectory,
      `t ≤ linear(tapeLen)`). See the finding block above `compileSeq_sound`.

      **2026-05-29 — left-sentinel finding + migration (DONE).** The physical
      contract's "head rewound to `0`" was **not implementable on the old
      encoding**: `composeFlatTM_run` (verified) *preserves* the head across the
      seam, so each fragment must rewind itself; but a TM head clamps at `0`
      under `Lmove` *without detecting it*, so rewinding needs a
      uniquely-detectable left sentinel at index `0`, which `encodeRegs s ++
      [endMark]` lacked. The rewind *lemmas* already existed (`scanLeft_run`,
      packaged as `ScanLeft.rewindToStart_run`/`_traj`). **✅ The leading-sentinel
      encoding migration (step 1b-0) is now DONE:** `encodeTape s = endMark ::
      (encodeRegs s ++ [endMark])` (reuse `3`, `sig` stays `4`); `decodeTape`
      drops the leading sentinel; `appendBit_sound` folds the sentinel into the
      first marker-free block (so the append op still runs from head `0`, no
      head-bridge); `bitTestTM` reworked to step past the sentinel then read;
      `bitDecider_run` budget `+2→+3`; framework `DecidesBy.encode_size` loosened
      `2·size+3→2·size+4`. `lake build` green (3356), axiom-clean.

      **2026-05-30 — rewind finding + per-op physical contract (1b-2 DONE for the
      append op).** ⚠ The gadget exits with its head **on the trailing
      terminator** (`endMark = 3`, the *last* tape cell — `insertCarryTM_run`
      ends there), **not** "left of" it. Verified by `#eval`. So a bare
      `scanLeftUntilTM 4 3`/`rewindToStart_run` started there **halts immediately**
      (reads its target on the first cell) and never rewinds. Fix shipped (all
      sorry-free, axiom-clean): `ScanLeft.rewindFromEndTM = composeFlatTM
      stepLeftTM scanLeftUntilTM` (one unconditional `Lmove` off the terminator,
      then scan left to the leading sentinel; `rewindFromEndTM_run`/
      `_no_early_halt`); `AppendGadget.appendAtThenRewindTM` +
      `appendAt_rewind_run`/`_no_early_halt` (gadget-level physical contract,
      head→`0`); and `Compile.appendBit_physical` (the `encodeTape`-level
      contract: head-`0` exit, tape = `encodeTape output`, trajectory, **linear**
      budget `t ≤ 3·tapeLen + 6`) with reusable `encodeTape` structure lemmas
      (`encodeTape_get_zero`/`_lt_four`/`_interior_ne_endMark`).

      **2026-05-31 — ⚠⚠ BLOCKING FINDING: the physical tape never shrinks; the
      exact-tape contract is unsatisfiable for length-DECREASING ops (do NOT
      follow the `appendBit_physical` pattern for `opClear`/etc.).** Machine-
      checked in `Complexity/Complexity/TapeMono.lean`: `writeCurrentTapeSymbol`
      keeps `right` the same length (in-range) or grows it (pad), `moveTapeHead`
      never touches `right`, so `right.length` is monotone non-decreasing along
      every run (`runFlatTM_single_length_le`, `runFlatTM_initFlatConfig_no_shrink`,
      axiom-clean). But `compileOp_sound_physical` demands the exit tape be
      *exactly* `encodeTape (Op.eval o s)`; for `clear`/`tail`/shrinking
      `copy`/`head`/`eqBit`/`nonEmpty`/length-ops that is a **shorter** list than
      the input, which **no run can produce** (concrete proof:
      `Compile.clear_physical_unsatisfiable`). Only `appendOne`/`appendZero`
      (pure growth) fit. **Resolution (validated, not yet built): a residue-
      tolerant contract** — exit tape `encodeTape output ++ residue` with
      `residue` terminator-free, hidden existentially in a `TapeOK` relation so
      composition needs no residue bookkeeping. Already proved this session:
      `Compile.decodeTape_encodeTape_append` (decode ignores residue + head — the
      foundation). Still to build: (i) a **two-phase rewind** (scan-left to the
      real terminator, step left, scan-left to the leading sentinel — both are
      `3`, distinguished by the terminator-free interior/residue); (ii) the
      missing **`deleteCarryTM`** left-shift primitive (mirror `insertCarryTM`,
      filling vacated cells with `0`); (iii) restate the four
      `compile*_sound_physical` with `TapeOK`. **Next:** items (i)–(iii), then
      the 10 stub ops (1c), then assemble (1b-3/1b-4/1d). See HANDOFF
      "THE FINDING" + "Next step".
   c. Concretise the 10 stub `compileOp`s from the gadget library (`opClear`,
      `opCopy`, `opTail`, `opHead`, `opEqBit`, `opNonEmpty`, and the four
      length-as-value ops), each with its **linear-budget** `compileOp_sound`.
   d. Assemble `compileSeq_sound` from `compileSeq_compose_physical`,
      `compileForBnd_sound` from `loopTM_run`, `compileIfBit_sound` from
      `branchComposeFlatTM_run`; then `Compile_sound` / `Compile_run_physical` by
      induction. This discharges the one obligation the whole S3 bridge sits on.
   *Estimate ~3–5K LOC. One structural prerequisite remains — the
   leading-sentinel encoding migration (1b-0) — after which the step-bound
   accounting (linear-then-quadratic) and rewind-bracketing is real but
   structural-unknown-free work.*

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
| **C2** | **compiler soundness** `Compile_sound` / `Compile_run_physical`. | ⚠ **Highest completion risk.** Combinators proven; gadget library sorry-free; behavioural per-op soundness **proven for `appendOne`/`appendZero` at general `dst`** (`compileOp_appendOne_sound`, `appendAt_run_steps`). **Cost-model gap FIXED** (`Op.cost` size-aware, `Op.size_eval_le`) **and the Cmd-level size bound is now PROVEN** (`Cmd.size_eval_le : size (c.eval s) ≤ size s + c.cost s`, by charging the `forBnd` counter — depth-constant-free; replaced the register-exclusion route). ⚠ **NEW finding — budget shape:** the per-fragment `overhead` budgets are **quadratic and don't compose** (summing `~cost` quadratics → cubic), so `compileSeq_sound`/`compileIfBit_sound`/`compileForBnd_sound`/`Compile_sound` are **unprovable as stated** (`a=3,c₂=1` → `42 ≰ 36`). Must restate per-fragment budgets **LINEAR** (gadgets prove `≤ 2·tapeLen+3`) → quadratic total with slack. The **linear tape-length bound is now PROVEN** (`Cmd.encodeTape_eval_length_le`, via `Compile.encodeTape_length` + `Cmd.eval_length_le`), and the **append ops now carry the linear budget** `2·tapeLen+3` (`compileOp_appendOne_sound`/`appendZero`, was quadratic `overhead`). **2026-05-29 — left-sentinel finding + migration DONE:** the physical contract's "head rewound to `0`" was **not implementable on the old encoding** (`composeFlatTM_run` preserves head across the seam; a TM head clamps at `0` but can't *detect* it, so rewind needs a unique left sentinel that the old `encodeTape` lacked). Rewind *lemmas* already existed (`scanLeft_run`/`ScanLeft.rewindToStart_run/_traj`). **✅ Leading-sentinel encoding migrated** (`encodeTape s = endMark :: encodeRegs s ++ [endMark]`, sig stays 4): `decodeTape` drops the leading sentinel; `appendBit_sound` folds it into the first block (append still runs from head `0`); `bitTestTM` steps past it then reads; `bitDecider_run` `+2→+3`; framework `encode_size` `2·size+3→2·size+4`. Green, axiom-clean. **2026-05-31 — ⚠⚠ BLOCKING FINDING:** the physical tape **never shrinks** (`TapeMono.lean`, machine-checked), so the exact-tape `compileOp_sound_physical` (`exit tape = encodeTape output`) is **unsatisfiable for every length-DECREASING op** (`clear`/`tail`/shrinking `copy`/`head`/`eqBit`/`nonEmpty`/length-ops) — `encodeTape output` is *shorter* than the input (`Compile.clear_physical_unsatisfiable`). Only `appendOne`/`appendZero` (growth) fit. **Resolution = residue-tolerant contract** (`exit tape = encodeTape output ++ terminator-free residue`, in a `TapeOK` relation); decode-correctness already proved (`Compile.decodeTape_encodeTape_append`). **Open (next):** (i) two-phase rewind (real terminator → leading sentinel); (ii) **`deleteCarryTM`** left-shift primitive (mirror `insertCarryTM`); (iii) restate the four `compile*_sound_physical` with `TapeOK`; then 10/12 `compileOp` stubs; assemble. See HANDOFF "THE FINDING". Plan step 1. |
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
