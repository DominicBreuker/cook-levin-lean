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
| `#print axioms CookLevin` | `[propext, sorryAx, Classical.choice, Quot.sound]` — **depends on `sorryAx`, now only via the hardness half** |
| `#print axioms SAT_inNP.sat_NP` | `[propext, Classical.choice, Quot.sound]` — **in-NP half sorry-free** (Route A, 2026-06-28) |
| `#print axioms FlatClique_in_NP` | `[propext, Classical.choice, Quot.sound]` — **FlatClique in-NP half sorry-free & axiom-clean** (2026-07-01; `cliqueRelDecidesLang` complete) |
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
giving `CookLevin : NPcomplete SAT`. The in-NP half is **done**: the layer's
`evalCnfCmd` verifier is sorry-free and `SAT_inNP.sat_NP` is axiom-clean (Route A,
2026-06-28). The remaining `sorryAx` on `CookLevin` is wholly hardness-side.

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
   c. Concretise the stub `compileOp`s, each with its residue contract.
      **✅ 2026-06-03 — the `clear` op is now FULLY proven** (run + trajectory +
      the quadratic budget `t ≤ 9·tapeLen²+9`) in
      `compileOp_sound_physical_residue`, joining `appendOne`/`appendZero`. The
      step-bound was threaded through the whole clear chain (each run lemma gained
      a `∧ t ≤ linear` conjunct) and assembled with the reusable
      `Compile.loopBudget_le` + `Compile.clearBudget_arith`. **⚠ Budget-constant
      risk surfaced:** `9·tapeLen²+9` is *tight* (needs `n+2 ≤ tapeLen` and tight
      per-iter constants); since each cross-register op internally composes
      `clear ⨾ copyBlock ⨾ transform` (each `Θ(L²)`), expect to **bump the
      statement constant to a larger quadratic** (update 3 sites — statement +
      append cases + clear case; `inOPoly` is all `toFrameworkWitness'` needs).
      **⚠ 2026-06-01 finding (do not "copy the in-place append
      template"):** the remaining 9 are **cross-register** — `tail`/`copy`/
      `head`/`eqBit`/`nonEmpty`/`takeAt`/`dropAt`/`concat`/`consLen` all read
      register `src` and write register `dst` (`Op.eval`: `s.set dst (f (s.get
      src))`), and the real witnesses use `dst ≠ src` (`PolyTime.lean`:
      `Op.head 1 0`, `Op.tail 2 0`, `Op.takeAt 3 2 1`). The gadget library has
      **no data-transport gadget** (only scan / insert-one-symbol / delete-one-
      cell), so the missing critical-path primitive is a single-tape **block-move
      gadget `copyBlockTM`** (carry `src` content to `dst`, resizing the slot).
      Once it exists, every cross-register op = (clear dst) ⨾ (copyBlock src→dst)
      ⨾ (in-place transform on dst). Only `clear dst` (no source) and the two
      append ops are genuinely in-place. **Order:** probe `copyBlockTM` go/no-go
      (verify the exit head lands in residue past the terminator, as the append
      op needed), prove its run/`_no_early_halt`, then per-op contracts via the
      `opAppendBit_physical_residue` template + `rewindBracket`. New bookkeeping
      lemmas landed (axiom-clean): `Compile.encodeTape_set_length` (tape-length
      balance for a register write), `Compile.ValidResidue_append_replicate_zero`,
      and `Compile.clear_block_decomp` — the `clear` gadget's proven spec bridge
      (clearing `dst` deletes exactly the `shiftReg (s.get dst)` block; gives the
      input/output target for a future `clearRegionTM_run`). Note clearing `dst`'s
      old slot is a shared prerequisite for *every* cross-register op, so the
      `clear`/delete-region machinery is foundational. **2026-06-01(b) — budget
      finding:** `compileOp_sound_physical_residue`'s budget was loosened from the
      linear `3·tapeLen+8` to the **quadratic `9·tapeLen²+9`**: multi-cell ops are
      inherently Θ(tapeLen²) on a single-tape machine (deleting/moving Θ(tapeLen)
      cells, each its own O(tapeLen) shift pass), so the linear bound was
      unsatisfiable for them. This composes — `compileSeq_sound_physical` is
      additive (`t₁+1+t₂`), so per-op quadratics sum to a polynomial total
      (`inOPoly` suffices). Append cases relax via `linear_le_quadratic_tapeLen`.
      See HANDOFF.md "the previous plan was wrong" + "budget is now QUADRATIC".
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
| **C2** | **compiler soundness** `Compile_sound` / `Compile_run_physical_residue`. | ⚠ **Highest completion risk.** Combinators proven; gadget library sorry-free; behavioural per-op soundness **proven for `appendOne`/`appendZero`**. Cost-model and Cmd-level size bound PROVEN (`Cmd.size_eval_le`). Budget must use **linear** per-fragment budgets (quadratics don't compose). Leading-sentinel encoding migrated (✅). **2026-05-31 — tape non-shrink finding + residue infrastructure DONE:** the physical tape never shrinks (`TapeMono.lean`), making exact-tape contracts unsatisfiable for deletion ops. **Resolution: residue-tolerant contract** (`exit tape = encodeTape output ++ ValidResidue residue`). Infrastructure complete: `TapeOK`/`ValidResidue` definitions + helpers; `compileSeq_sound_physical_residue` (PROVEN); `decodeTape_encodeTape_append` (PROVEN); `rewindTwoPhaseTM` (PROVEN); `deleteCarryTM` run + `_no_early_halt` (PROVEN); `compileOp_sound_physical_residue` + `Compile_run_physical_residue` (correctly stated, sorry'd). `bitDecider_run` now uses the residue contract (✅). **2026-05-31(b) — two-phase append rewind PROVEN + halt-uniqueness BLOCKER surfaced:** `appendAt_twoPhaseRewind_run/_no_early_halt` (residue-tolerant append+rewind, machine `appendAtThenTwoPhaseRewindTM`) are proven & axiom-clean — residue follows the trailing terminator so every rewinding op needs the *two-phase* rewind (the single-phase pattern is wrong). **halt-uniqueness obstacle RESOLVED (2026-05-31c):** rewinding op machines have **two halt states** (left-scan found + boundary; `#eval`-verified), so a bare rewinding machine violates `halt_unique`. **Fixed generally:** `joinTwoHalts_run_eq` (run-preservation: a run never visiting the demoted state is preserved — also unblocks `compileIfBit_sound`), the rewind halt characterization (`rewindTwoPhaseTM_halt_only/_six/_seven`), and the reusable `rewindBracket` builder + `rewindBracket_transport` (wrap any `compute` machine with the two-phase rewind, demote the boundary halt → unique-exit `CompiledCmd` with its run/trajectory transported). `opAppendBitRewind := rewindBracket (appendAtTM …)` is the live append instance. All axiom-clean. **2026-06-01 — step (i) DONE (append per-op residue contract + `compileOp` wired):** `opAppendBit_physical_residue` (the **template for every rewinding op**: `rewindBracket_transport` fed by `appendAt_twoPhaseRewind_run` + the `encodeTape`+residue decomposition; `res_out = res_in`) is PROVEN & axiom-clean. `compileOp`'s `appendOne`/`appendZero` now dispatch to the head-rewinding `opAppendBitRewind`, and the **append cases of `compileOp_sound_physical_residue` are PROVEN**. Two findings folded in: the per-op budget is **`3·L+8`** (two-phase rewind costs 2 more steps than single-phase `+6`); and `appendAt_twoPhaseRewind_run/_no_early_halt` were loosened `p<HD → p≤HD` to cover the no-residue case. **2026-06-01 — ⚠ cross-register finding (corrects the prior "do `opTail` next" plan):** the 9 non-`clear` stub ops are **cross-register** (`tail`/`copy`/`head`/… `= s.set dst (f (s.get src))`, read `src` write `dst`; real witnesses use `dst ≠ src`, e.g. `Op.tail 2 0`). An in-place `navigate ⨾ deleteCarryTM` does **not** implement them; the gadget library has no data-transport primitive. **Real critical path: a single-tape block-move gadget `copyBlockTM`**, after which every cross-register op = (clear dst) ⨾ (copyBlock src→dst) ⨾ (in-place transform). Only `clear`/append are in-place. Bookkeeping lemmas landed (axiom-clean): `encodeTape_set_length`, `ValidResidue_append_replicate_zero`. **Open (ordered):** (ii) probe + build `copyBlockTM`, then the cross-register ops via the `opAppendBit_physical_residue` template; (iii) `compileIfBit`/`compileForBnd` residue + assemble `Compile_run_physical_residue`. **2026-06-03 — the `clear` op is now FULLY PROVEN** (in-place `loopTM`-delete; run + trajectory + quadratic budget `t ≤ 9·L²+9`; `res_out = res_in ++ replicate |old| 0`), via threaded linear per-iteration step bounds + reusable `Compile.loopBudget_le`/`clearBudget_arith`. **⚠⚠ 2026-06-03 BLOCKING FINDING + decision (supersedes the cross-register sub-plan above):** scoping the verifiers surfaced that the compiler is **`BitState`-only** (`sig=4`) but the `LangEncodable` encodings are Nat-valued (`enc(Nat)=[n]`, product length-prefix cell), so `Compile_sound` (stated without a `BitState` hypothesis) is vacuous for the non-bit states the *live* in-NP path (`sat_NP → evalCnfCmd → Compile`) feeds it. **Owner-approved fix: option B — everything bit-level, numbers UNARY.** Numbers as unary `1`-blocks keep `sig=4`/`BitState` (so the proven gadgets stay valid) and make a unary length register a **loop counter** ⇒ **counter+rotation = non-destructive block copy with NO marking**, so every cross-register op is a counted loop reusing `loopBudget_le` (the `sig=6 copyBlockTM` sketch is dropped). Tasks: (1) add `BitState` to `Compile_sound` + `LangEncodable` guarantees it; (2) re-encode `Nat`/product unary, restate `takeAt`/`dropAt`/`consLen` (only `swapCmd`/`mapFstCmd`/`mapSndCmd` use them); (3) the ops as counted-loop gadgets; (4) assemble. **2026-06-04 — ✅ `nonEmpty` op FULLY PROVEN (axiom-clean), first cross-register op done.** Machine `Compile.opNonEmpty` (navtest `src` first, then per-branch rewind/clear `dst`/append answer-bit, two branch exits merged by `joinTwoHalts`; correct for `dst=src`). Built the **reusable branch-merge engine** (`joinTwoHalts_reaches_kept`/`_reaches_demoted`, `joinTwoHalts_step_to_h1`, `stepFlatTM_bridge_prefix`, branch halt-characterization) + `clearAppendM_run`/`nonEmptyBranchBody_run`/`navTestReg_traj_*`. Per-op budget bumped to `9·L²+9·L+30`. **2026-06-04(b) — ✅ `head` op FULLY PROVEN (axiom-clean), second cross-register op done.** Built `Compile.bitReadTM` (the bit-*value* test navtest lacks: cell `1`→bit 0, `2`→bit 1) and realised the 3-way branch as **two nested `joinTwoHalts`-merged 2-way branches** (outer `navigateAndTestTM` empty/content → `opInnerBit` / `clearOnlyBranchBody`); `Compile.opHead`/`opHead_run` is the template for any nested/3-way branching op. **7 cross-register ops left** (`copy`/`tail`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`). **2026-06-04(c) — deep feasibility pass (verdict: FEASIBLE).** (B) The block ops need **no length counter**: a two-phase **transfer** (move `src`→`sc` until `src` empties, then `sc`→`src`&`dst` until `sc` empties) is two `clear`-style `loopTM`s built from already-proven gadgets (`bitReadTM`⨾`deleteCarryTM`⨾`appendAtTM`); only an empty scratch operand `sc` is needed (fold into Task 2). (A) **⚠ blocking budget inconsistency:** the stated top-level budget `overhead(size+cost)` with `overhead m=(m+1)²` is unprovable — per-op budgets are `Θ(L²)` (multi-cell ops) and `L` includes the register count `s.length`, so the honest total is **cubic in `size+s.length+cost`**; `overhead`'s "`O(L)`/op ⇒ quadratic" doc (Compile.lean ~L2037) holds only for the append ops. **Fix before Task 4:** restate as `overhead(size+s.length+cost)` with `overhead` **cubic**; downstream needs only `inOPoly`/`monotonic` (preserved), so it ripples mechanically through `bitDecider_run`/`DecidesBy`/`toFrameworkWitness'`. **2026-06-05 — ✅ transfer-gadget design PROBE-VALIDATED (GO) + ⚠ sequencing corrected + ★ BitState design fork surfaced.** `#eval` probes confirm the counter-free two-phase transfer (move-one-bit = `navigateAndTestTM ⨾ bitReadTM ⨾ deleteCarryTM ⨾ rewind ⨾ appendAtTM(bit+1) ⨾ rewind`, reusing only proven gadgets) works for `dst>src` and `dst<src` (append symbol is `bit+1`, not `bit`). **Corrected sequencing (the prior "build ops before Tasks 1+2" was self-contradictory):** all 7 ops are gated on Task 2 — `takeAt`/`dropAt`/`consLen` need the unary length restatement (current `.headD 0` is meaningless under `BitState`), `copy`/`tail`/`concat`/`eqBit` need the scratch operand, and `swapCmd` is tied to the current product encoding (adding scratch alone would force a double-rewrite). So **Task 2 (coupled batch) must precede the ops**; only the raw-tape transfer gadget is buildable beforehand. **★ Blocking design fork (owner):** the 3 top-level obligations lack the `BitState s` hypothesis every per-fragment lemma needs (Task 1); adding it forces the bridge to supply `BitState (encodeState x)` — via a global `LangEncodable.enc_bit` field (Option A, widest, breaks `List Nat = id`) or a localized `BitEncodable` on compiled types only (Option B, recommended; only `cnf × assgn` is compiled live). **2026-06-05 — ✅ fork SETTLED (design review): Option B′.** B's *mechanism* is kept (don't bundle into `LangEncodable`) but its *justification* was a misconception: the bit-level encoding work is **systemic, not localizable** (every chain type is compiled in the endgame; the value-as-length ops `consLen`/`takeAt`/`dropAt` + the `swap`/`mapFst` product toolkit are non-`BitState` and must be rebuilt unary regardless), and the **live `sat_NP` path uses the free-encoding `DecidesLang` with the bespoke non-`BitState` `EvalCnfCmd.encodeState`** (cells `v+3`/`2`), *not* a `LangEncodable` instance. B′: attach `enc_bit : ∀ x, BitState (encodeIn x)` as a **field on the witness structures** (covers the live free path) + a reusable `BitEncodable` mixin for the canonical types; make the canonical encodings bit-level; re-lay `EvalCnfCmd.encodeState` unary. No owner sign-off needed (`sig=4` already settled). **See HANDOFF.md — the authoritative, corrected C2 plan.** **2026-06-12 — ✅ the `copy` op MACHINE is REAL (`Compile.opCopy`: clear ⨾ navigate ⨾ marking cursor-loop ⨾ rewind; in-place mark `3`/restore — the design probe-validated end-to-end in `probes/CursorCopyProbe.lean`), the per-op budget is cost-scaled `(9L²+9L+30)·(cost+1)` (unscaled was unprovable for `copy`), and the contract's `copy` case is DISCHARGED onto the pinned `opCopy_run`. **2026-06-12b — ✅ the `copy` op is FULLY PROVEN:** the whole run-lemma stack (`copyPipe_run → copyBody_run_iter → copyLoop_run → opCopy_run`) is proven & axiom-clean, with exact residue `res ++ replicate |dst₀| 0` and a reusable marked-tape toolkit (see HANDOFF session block). **2026-06-12c — ✅ the `tail` op is FULLY PROVEN:** real `Compile.opTail` (in-place = joined `clearBodyRawTM` ⨾ `idTM` halt-zeroing seam; `dst ≠ src` = clear ⨾ nav ⨾ (skipRead ⨠ copyLoop/idTM) ⨾ rewind) + the full stack `tailLoop_run → tailBranch_run → opTailSelf_run_done/_delete + opTail_run`, contract case discharged, axiom-clean. **7/12 ops done; `compileForBnd` is fully UNGATED** — see HANDOFF bottom-up task 1. **2026-06-13 — ✅ the `forBnd` per-iteration chain is PROVEN:** `Compile.forBndIterate` (the body `copy cnt K2 ⨾ rbody ⨾ appendOne K2 ⨾ tail K1 K1` via `compileSeq`) + `forBndIterate_run` (exact-residue run, W-invariant ①, cubic budget; takes the verbatim `compileForBnd_sound` body contract), axiom-clean. Surfaced: the loop body's content branch must rewind before the work chain (navtest leaves the head in the interior). **2026-06-13b — ✅ the `forBnd` loop MACHINE + `loopTM` done contract are PROVEN:** `Compile.forBndContentTM`/`forBndBodyTM` (`= branchComposeFlatTM (navigateAndTestTM sb) forBndContentTM justRewindTM`, the `clearBodyRawTM` shape) + `forBndLoopTM := loopTM …` + full structural-lemma family, and `forBndBody_done_run` (the `loopTM_run` done contract, near-copy of `clearBody_done_run`); all axiom-clean + probe-validated. **2026-06-13c — ✅ the `loopTM` ITERATE contract `forBndBody_iterate_run`, all five fold invariants `forBndIterateState_{get_sb,get_sb1,scratch,length_ge,bitState}` + the fold-invariant induction `forBndLoop_invariant` (gives `BitState`/scratch/length/`|K1_i|=iters−i`/`|K2_i|=i`), AND a BUDGET FIX (keep the copy source `|K2|` explicit so the loop sum `Σ(i+2)~iters²/2` fits `physStepBudget`'s `8·iters²` headroom — the loose `(G+2)` factor overdrew at `iters>8`) are PROVEN & axiom-clean.** Remaining for `compileForBnd`: the ASSEMBLY — the `.choose` loop run via `loopTM_run` (mirror `clearRegionTM_run`) + entry `opCopy`/exit `opClear` wiring, done INSIDE `compileForBnd_sound` after the def-reordering (the W-invariant/budget intertwine with `(forBnd …).cost`/`eval` + the `clear K2` step). HANDOFF bottom-up task 1. **2026-06-14 — ✅ `compileForBnd` is now a REAL `CompiledCmd` + the semantic core is PROVEN.** Def-reorder DONE: the `forBnd*` machine defs moved above `compileCmd`, `forBndLoopTM` wrapped as `Compile.forBndLoopCmd` (mirrors `opClear`), and `compileForBnd := compileSeq (opCopy sb bound) (compileSeq forBndLoopCmd (opClear (sb+1)))`. The keystone semantic fact **`Compile.forBndLoop_eval`** (machine fold, K2-cleared, `= (forBnd).eval s`) is PROVEN & axiom-clean via a joint `AgreeBelow`/K2/length induction tying `A i` to `foldlState` (`Cmd.eval_forBnd`) + `List.ext_getElem` (helpers: `Cmd.foldlState_length`, `forBndIterateState_{get_below,length_eq}`). Remaining for the `compileForBnd_sound_physical_residue` sorry: the TM loop run (`.choose` residue fold + `loopTM_run`, mirror `clearRegionTM_run`) + W/budget telescoping + the 3× `compileSeq` stitch (mechanical — all contracts proven). **2026-06-14 — ✅ `compileForBnd_sound_physical_residue` FULLY PROVEN & axiom-clean — the forBnd counted loop is CLOSED.** **⚠⚠ 2026-06-21b — BLOCKING `eqBit` FINDING:** the d2 `compareRegsTM` stack (complete & axiom-clean) addresses scratch by the runtime index `s.length` (grow-at-end), but `compileOp` builds a machine fixed by `dst/src1/src2` only — so it is **un-instantiable** into `opEqBit`. Fix = **Resolution B**: thread a scratch base into `compileOp` and use pre-existing PADDED scratch (mirror `forBnd`), reserving eqBit's 2 registers in `padRegsTM`. The hard consume-loop core (`compareLoop_run`/`copyEmpty_run`/`eqVerdictM`) is reused verbatim; `growTwoEmpty`/`shrinkTwoEmpty` become dead. Design is the next TOP-DOWN task (0b); see HANDOFF. **2026-06-25 — ✅ `eqBit` op DONE (BU-C2-15): the no-grow `opEqBitNG` was relocated above `compileOp` (in-file block move — a clean module split is impossible since the eqBit run lemmas consume copy/tail run lemmas defined *after* `compileOp`), wired via `Compile.opEqBit := opEqBitNG`, and the `eqBit` case of `compileOp_sound_physical_residue` discharged directly from `opEqBitNG_run` (budget `exact hbud`, W-① an equality). 8/12 ops proven; the `compareRegsTM`/grow-shrink scaffolding is now dead code. ⚠⚠ FINDING: this did NOT make `sat_NP` sorry-free — the live chain uses the *generic* `compileOp_sound_physical_residue` whose body still has the 4 stub-op sorries, so `#print axioms SAT_inNP.sat_NP` is still `[…, sorryAx, …]`. The SAT-in-NP soundness win now needs the top-down `Op.IsSupported`/`Cmd.AllOpsSupported` threading (HANDOFF top-down Task 0) — NOT more gadgets. **2026-06-28 — ✅ `concat` op FULLY PROVEN (9/12).** `Compile.opConcat` (Cmd.lean) = aliasing-safe 4-stage scratch chain `opCopy sb src1 ⨾ opCopyAppend sb src2 ⨾ opCopy dst sb ⨾ clear sb`; discharged by `Compile.opConcat_run` (OpSound) chaining the four stages through `compileSeq_sound_physical_residue`/`_traj` (moved above the op contract) with the budget cert `concat_budget_arith` (nlinarith-over-ℤ; four per-stage budgets over tapes `L`,`L+V`,`L+V`,`L+2V` compose to the contract bound). `Op.cost concat` bumped to `2(|src1|+|src2|)+1` (scratch round-trip dumps ~2|V| residue); ripple: product-toolkit bounds `swapCmd 12n+22`, `mapFstCmd 7g+18n+31`. New reusable gadget `opCopyAppend` (`opCopy` minus the clear). Build green (3370); `opConcat_run` axiom-clean. **Remaining ops `takeAt`/`dropAt`/`consLen` are gated on the unary migration — the next bottom-up batch.** **2026-06-28(c) — ✅ Route A DONE: `SAT_inNP.sat_NP` is SORRY-FREE & axiom-clean** (`[propext, Classical.choice, Quot.sound]`). Added an op-supportedness wall `Op.IsSupported`/`Cmd.AllOpsSupported` (Syntax.lean) + field `allOpsSupported` on `DecidesLang`/`PolyTimeComputableLang`, threaded parallel to `NoConsLen` through `compileOp_sound_physical_residue` (`hsupp`; trio cases discharge by `simp only [Op.IsSupported] at hsupp`) → `run_physical_residue_gen` → `Compile_run_physical_residue` → `bitDecider_run` → `paddedBitDecider_run`/`paddedCompute_run`. The live trio-free `evalCnfCmd` supplies the real `evalCnfCmd_allOpsSupported` (mirrors `evalCnfCmd_noConsLen`); reduction-side `c_allOpsSupported` are sorry placeholders (same status as `c_noConsLen`). Headline `CookLevin` still `sorryAx` via the hardness half only. Reuse the wall for CliqueRelTM; delete it in Route B once the trio is proven. **2026-06-28(b) — ✅ unary-migration design PROBE-VALIDATED + ★ FINDING (`probes/UnaryMigrationProbe.lean`, axiom-free).** Validated bit-level product encoding `replicate |encx| 1 ++ [0] ++ encx ++ ency` (round-trips, `BitState`-clean) + new trio semantics (count = register's unary length; `consLen` writes a unary block, now `BitState`-preserving). ★ The handoff's "just re-derive swap" under-estimated: product *unpacking* must recover `|encx|` from the unary prefix, which the current op set CANNOT do. Two `#eval`-validated routes: **Option L (recommended)** = a DSL `forBnd` subroutine `extractLeadingOnes` over EXISTING ops (no new op, op count stays 12; correctness = a fold invariant like the proven `memberCheck`); **Option H** = a new `headOnes` op (cleaner swap, +1 op/gadget). The migration is one **atomic batch** (trio `Op.eval` breaks `swapCmd`+`mapFstCmd` together; toolkit has no external consumers) — restate trio + new product `enc`/`dec` + `BitEncodable (X×Y)` (discharges the `enc_bit := sorry`s at `PolyTime.lean:1321`,`:1733`) + rewrite `swap`/`mapFst`/`mapSnd`; only `extractLeadingOnes` (step 2a) lands as its own commit. ⚠ `BitEncodable (List Nat)` is FALSE under `id` — generic witnesses don't need it; migrating `List Nat` bit-level is a separate later ripple. See HANDOFF bottom-up step 2. **2026-06-28(d) — ✅ unary-migration step 2a DONE: `extractLeadingOnes` PROVEN** (`Lang/ExtractOnes.lean`, axiom-clean). The leading-ones extractor (Option L: existing ops + one `forBnd`, no new op) recovers the unary length prefix `L = leadingOnes src` as `replicate L 1`, via a `forBnd` DONE-flag fold invariant (`extractLeadingOnes_get_dst` + `_usesBelow`). It is the product-unpacking primitive `swap`/`mapFst`/`mapSnd` consume in step 2d. Remaining migration = the atomic batch 2b–2e. **⚠⚠ 2026-06-29 — BLOCKING: the unary product encoding is SIZE-UNSOUND; the migration is BLOCKED pending an encoding-design decision.** Machine-checked (`probes/UnaryProductSizeProbe.lean`, axiom-free `#eval`): `enc(x,y) = replicate \|enc x\| 1 ++ [0] ++ enc x ++ enc y` has `\|enc(x,y)\| = 2·\|enc x\|+1+\|enc y\|`, so the first component **doubles per nesting level** (depth-`d`: `\|enc\| = 2^d·(m+1)−1` while `encodable.size = m+d`). The generic `LangEncodable (X×Y)`.`enc_size : ≤ 2·size+1` obligation needs `B(a+b+1) ≥ 2B(a)+B(b)`, which has only exponential solutions — **no polynomial bound exists**, the field is *false*, the generic instance cannot be built. The 2026-06-28 `UnaryMigrationProbe` checked round-trip + `BitState` but not `enc_size`. Bit-level + poly-size + generic-nestable is unachievable with any inline self-delimiting prefix; the only `O(log)` bit-level option is a **binary/Elias length prefix** (forces `enc_size` → quadratic + a binary→unary count gadget). Since `sat_NP` is already sorry-free (Route A) and the trio only buys cosmetic Route B, the recommended path is to **decouple** (build the future S3 chain on bespoke bit-level free encodings, as EvalCnf does — verify the generic trio is even needed) and meanwhile do **TOP-DOWN (CliqueRelTM)**. Full options in HANDOFF bottom-up step 2. No code changed (atomic batch; a partial rewrite would be discarded). |
| **C1** | **per-`Op` compilation** (`compileOp` + soundness). | Real TMs + cases FULLY PROVEN & axiom-clean: `appendOne`/`appendZero`/`clear`/`nonEmpty`/`head`/`copy`/`tail`/`eqBit`/`concat` (**9/12; `concat` assembled as the aliasing-safe 4-stage scratch chain `opConcat` + discharged via `opConcat_run`, 2026-06-28; `Op.cost concat` bumped to `2(|src1|+|src2|)+1`**). Still stubbed: `takeAt`/`dropAt`/`consLen` (the value-as-length trio, gated on the unary migration). None of the 3 is on the live `sat_NP` path. Part of C2. |
| **C3** | **`loopTM` counted loop** (`compileForBnd` + soundness). | `loopTM`/`loopTM_run` proven; behavioural `forBnd` toolkit (`Lang/Frame.lean`) proven. ✅ 2026-06-11b: the snapshot-vs-clobber gap is closed at the interface — `compileCmd` assigns **static scratch registers** (`K1/K2` per nesting level, `Cmd.loopDepth`), the contract is re-pinned + probe-validated (`probes/ForBndSkeletonProbe.lean`), `physStepBudget` re-pinned ×8 to fund the loop bookkeeping. Machine build is UNGATED, gated only on the cursor-copy/`tail` op gadgets; see HANDOFF bottom-up tasks 1–2. |
| **C4** | **layer → framework bridge.** | ✅ Engine done (`toFrameworkWitness'`, `inNPLang`/`red_inNPLang`, `inNPLang_to_inNP`, capstones `reducesPolyMO_of_lang`/`red_inNP_of_lang`), sorry-free modulo C2. Remaining: honest layer reductions (S1) + discharge C2. |
| **C6** | **bit-test tester.** | ✅ DONE (2026-06-11): `bitTestTM` (tape→state, register 0) AND the general `compileTestBit t` tester are real & sorry-free; `compileIfBit_sound_physical_residue` PROVEN (the `ifBit` combinator is closed). |
| **C7** | **verifier bodies** — `evalCnfCmd` (SAT, gates `inNP SAT`), `cliqueRelCmd`. | **EvalCnf: ✅ DONE (2026-06-10)** — `EvalCnfCmd.lean` sorry-free; `evalCnfDecidesLang` axiom-clean (budget quartic `200000·(n+1)^4`, `regBound 16`). **CliqueRel: ENCODING + PROGRAM + STRUCTURAL FIELDS ✅ DONE (2026-06-29)** — `cliqueRelEncode` concrete + bit-level + probe-validated; `cliqueRelCmd` is the concrete probe-validated 5-check verifier (`checkWf`/`checkOfType`/`checkLen`/`checkNodup`/`checkClique`, trio-free), and the structural `DecidesLang` fields `usesBelow`/`noConsLen`/`allOpsSupported` join the 4 encoding fields PROVEN & axiom-clean (quartic `timeBound`, `regBound 32`). Probes: `CliqueRelProbe` + `CliqueLtProbe`. **2026-06-30: ⚠ found+fixed a BUG in `ltBit`** (it guarded its consume-loop with `Cmd.ifBit`, which tests `= [1]` *exactly*, not nonemptiness, so it mis-decided operands `> 1`); **fixed to the unconditional-drain form and PROVED `ltBit_run` (axiom-clean).** **2026-06-30b: ✅ proved the keystone leaf `readNum_run` + 3/5 per-check run-lemmas (all axiom-clean).** **2026-06-30c: ✅ proved the remaining checks `memberEdge_run`/`checkNodup_run` (double `forBnd`)/`checkClique_run` (depth-4, calls `memberEdge`), AND the `decides` field (`cliqueRelCmd_decides` + bridge `cliqueRel_iff_checks`) — all axiom-clean.** The nested-loop pattern (inner-run lemma proven by `foldlState_range_induct`, called inside the outer step; outer counter survives as a frame fact) is established. **2026-07-01: ✅ `cost_bound` PROVEN — `cliqueRelDecidesLang` sorry-free & `FlatClique_in_NP` AXIOM-CLEAN** (`[propext, Classical.choice, Quot.sound]`). The full cost-lemma stack (`readNum_cost` → per-check `_cost` lemmas → `cliqueRelCmd_cost_bound`) uses **length-only loop invariants** for the `hC` uniform body-cost bound (reusing the behavioural `*_step` for `hM`). ★ FINDING: `timeBound` bumped quartic→**quintic** `(n+1)^5` — uniform-bound accounting makes the depth-4 `checkClique` nest degree 5 (innermost `readNum` is `Θ(S²)` under three `forBnd`s); the true TM cost is quartic but amortisation is invisible to `cost_forBnd_le`. **CliqueRel C7 is now COMPLETE.** Both in-NP verifiers (SAT + FlatClique) axiom-clean; all remaining `sorryAx` on `CookLevin`/`Clique_complete` is hardness-side. |
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
