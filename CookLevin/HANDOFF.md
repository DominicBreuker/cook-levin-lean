# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first; they
are the authoritative, up-to-date status and plan. This file is a short pointer,
not a log.

## Where things stand

- `lake build` ✅ green (3356 jobs). `#print axioms CookLevin` =
  `[propext, sorryAx, Classical.choice, Quot.sound]` — the headline theorem is
  **conditional** (depends on `sorryAx`) and, separately, **vacuous** (S1/S2/S3,
  see ROADMAP risk register).
- The **S3 migration engine** is built and sorry-free *modulo* the one compiler
  obligation `Compile_run_physical` / `Compile_sound` (Risk **C2**).
- **The leading-sentinel encoding migration (step 1b-0) is DONE** (latest
  session): `encodeTape s = endMark :: (encodeRegs s ++ [endMark])`, `sig` stays
  `4`. The head-rewind primitive (`rewindToStart_run/_traj`) is now *applicable*.
  All real consumers were re-proven green & axiom-clean. The next step is
  rewind-bracketing each gadget into the physical contract (step 1b-1). See
  "Recommended next step".

## Latest session (2026-05-29) — head-rewind primitive + the assembly blocker

All sorry-free, `#print axioms`-clean; `CookLevin` axiom profile unchanged.
`lake build` ✅ green (3356 jobs).

**(0a) The head-rewind primitive is call-ready** (`Lang/ScanLeft.lean`).
Added `rewindToStart_run` / `rewindToStart_traj`: on a tape `m :: rest` whose
sentinel `m` occurs only at index `0`, `scanLeftUntilTM sig m` returns the head
from any interior position to index `0`, in the exact `h_run1`/`h_traj1` shapes
`composeFlatTM_run` consumes. These are thin specialisations of the existing
`scanLeft_run`/`scanLeft_no_early_halt`.

**(0b) ⚠ KEY CLARIFICATION — the prior handoff mis-scoped the next step.** The
prior note said "add head-rewind + trajectory lemmas to the gadget library."
But those lemmas **already existed** (`scanLeft_run`/`scanLeft_no_early_halt`,
now packaged as `rewindToStart_*`). The *actual* blocker for assembling the
physical contract is **structural, not a missing lemma**:

  - `composeFlatTM_run` (verified) **preserves the head position across the
    seam** — it does *not* reset it. The next fragment resumes on M₁'s exit
    head. But every per-`Op`/per-`Cmd` soundness statement assumes the head
    starts at `0` (`initFlatConfig`), and `bitTestTM` reads the answer at the
    head. So **each fragment must halt with the head rewound to a canonical
    position** for composition + the decider bridge to work.
  - Rewinding requires a **uniquely-detectable left sentinel** at index `0`
    (the head clamps at `0` under `Lmove` but cannot *detect* it; `endMark = 3`
    only marks the right end). The current `encodeTape s = encodeRegs s ++
    [endMark]` has **no left sentinel** — position `0` is a delimiter `0` or a
    shifted bit `{1,2}`, not unique. So no rewind is implementable on the
    current encoding.
  - **Fix (already anticipated in the `ScanLeft.lean` header):** migrate to the
    **leading-sentinel encoding** `encodeTape s = endMark :: encodeRegs s ++
    [endMark]` (reuse `3`; `sig` stays `4`). Then `scanLeftUntilTM 4 3`
    (= `rewindToStart_run` with `m = 3`) rewinds, since the interior carries
    only `{0,1,2}`. This is an encoding+contract migration, **not just a lemma to
    add**.

**(0c) ✅ STEP 1b-0 DONE — the leading-sentinel encoding migration landed.**
`Compile.encodeTape s = Compile.endMark :: (Compile.encodeRegs s ++
[Compile.endMark])` (`Lang/Compile.lean`), `sig` stays `4`. All real consumers
re-proven, `lake build` green (3356 jobs), `#print axioms`-clean (no `sorryAx`
except the pre-existing `Compile_run_physical` stub), `CookLevin` profile
unchanged. Concretely:
  - `encodeTape_length` → `size + regCount + 2`; `decodeTape` drops the leading
    sentinel (`flat.tail.takeWhile …`); round trip `decodeTape_encodeTape`
    re-proven; `encodeTape_eq_cons_of_get_zero` now `endMark :: (b+1) :: …`.
  - `appendBit_sound` (the real per-op lemma): the leading sentinel is **folded
    into the first marker-free block** (into `body` when `dst=0`, into the first
    skipped register when `dst≥1`) via a `key` existential, so the gadget still
    runs from head `0` — **no head-bridge needed**. `encodeTape_split` restated
    to give the sentinel-free registers part.
  - `bitTestTM` reworked: 4 states, **steps right past the leading sentinel**
    (state `0` reads `3` → R → state `3`) then reads the answer (`2`→accept,
    `1`→reject). `bitDecider_run` budget `+2 → +3` (one bridge + two gadget
    steps). The framework `DecidesBy.encode_size` bound loosened `2·size+3 →
    2·size+4` (`NP.lean`; the sentinel adds one cell), `budget_ge`/`toDecidesBy`/
    `toInTimePoly` constants bumped to match.
  - Removed two superseded probe lemmas (`compileOp_appendOne_behavioural`,
    `compileOp_appendOne_zero_sound`) — unused, replaced by `appendBit_sound`.

## Earlier session's work (recorded in ROADMAP)

All sorry-free, `#print axioms`-clean (`propext`/`Quot.sound` only); `CookLevin`
axiom profile unchanged.

**(1) The Cmd-level size bound — plan step 1a, now PROVEN.**
`Cmd.size_eval_le : State.size (c.eval s) ≤ State.size s + c.cost s`
(`Lang/Semantics.lean`). This is the clean linear invariant the compiler's
tape-length budget rests on (every intermediate tape in a `Compile c` run is
`encodeTape` of a sub-evaluation, whose size this bounds).
- The clean bound was **false for `forBnd`** (the unary loop counter
  `set counter (replicate i 1)`, size `i`, is uncharged size). The handoff's
  proposed *register-excluding* route gives a depth-dependent constant. Instead
  I **charged the counter in the cost model** — the *same* faithfulness
  principle as the prior size-aware `Op.cost` fix (writing `i` unary cells costs
  Θ(i) TM steps). `Cmd.run`'s `forBnd` now adds `iters * iters` (a closed-form
  lump ≥ Σ_{i<iters} i, kept **outside** the fold so every frame/locality lemma
  is untouched). Result: clean, depth-constant-free, and cost stays polynomial.
- Ripples were contained: `Cmd.cost_forBnd_le` gains `+ iters*iters` (no
  external consumers) and `Cmd.cost_agree`'s `forBnd` case threads the
  (agreement-stable) lump.

**(2) ⚠ NEW FINDING — the per-fragment compiler budgets cannot compose.**
While checking the next step (threading the budget), I found that the four
sorried budget lemmas are **unprovable as stated**: `compileSeq_sound`,
`compileIfBit_sound`, `compileForBnd_sound`, and the `Compile_sound` assembly
take each sub-machine's budget as the **quadratic** `Compile.overhead =(·+1)²`
and claim a quadratic-of-the-sum for the composite. But a quadratic is **not
superadditive** — summing `~cost` per-op quadratics gives a **cubic**. Worst
case `overhead(a) + 1 + overhead(a+c₂) ≤ overhead(a+1+c₂)` is **false for
`a ≥ 2`** (`a=3, c₂=1` → `42 ≰ 36`; gap grows with `a`). The fix: per-fragment
budgets must be **LINEAR** in tape length (the gadgets already prove
`appendAt_steps_le : ≤ 2·tapeLen+3`), which *do* compose into a quadratic total.
A prominent finding block now sits above `compileSeq_sound` in `Compile.lean`;
full writeup in ROADMAP Risk C2 / plan step 1b.

**(3) The linear tape-length bound — plan step 1b ingredient, now PROVEN.**
The corrected per-fragment budget must be linear in the tape length; this
supplies the analytic fact:
`Cmd.encodeTape_eval_length_le : (Compile.encodeTape (c.eval s)).length ≤
State.size s + c.cost s + max s.length k + 1` (`Lang/PolyTime.lean`), for any `c`
with `Cmd.UsesBelow c k`. Built from three reusable pieces:
- `Compile.encodeTape_length : (encodeTape s).length = State.size s + s.length +
  2` (+ `encodeRegs_length`; the `+2` is the two sentinels post-migration) —
  `Lang/Compile.lean`.
- `Cmd.size_eval_le` (contents bound, prior session).
- `Cmd.eval_length_le : (c.eval s).length ≤ max s.length k` (register count never
  exceeds `regBound`), with helpers `State.set_length_le` /
  `State.set_length_le_of_lt` / `Op.eval_length_le` — `Lang/Frame.lean`.

## Recommended next step — bracket each gadget into the physical contract (1b-1)

**Step 1b-0 (the leading-sentinel encoding migration) is DONE** — see (0c)
above. The encoding now supports head-rewind. What remains is to thread the
rewind through each gadget's exit and assemble `Compile_run_physical` /
`Compile_sound`.

**Step 1b-1 — bracket each gadget with a tail rewind (canonical head `0`).**
Canonical input/exit head = **index `0` (on the leading sentinel)**. The append
op's *behavioural* run already starts at head `0` (the sentinel is folded into
the first marker-free block — see `appendBit_sound`'s `key`), so **no leading
step-right is needed**. Only a **tail rewind** is needed so the head returns to
`0`: each compiled fragment's TM becomes `composeFlatTM gadget
(scanLeftUntilTM 4 3) exit`, and the exit config (head back at `0`) feeds the
next fragment / `bitTestTM`.

⚠ **Rewind caveat (important, found this session):** the canonical tape is
`endMark :: <interior, only {0,1,2}> :: endMark` — it has **two** `endMark = 3`
cells (leading sentinel AND trailing terminator). So `rewindToStart_run`'s
hypothesis `∀ x ∈ rest, x ≠ m` is **too strong** (the trailing `3` violates it).
Scanning left from an interior head only ever reads cells `1 … head`, all of
which are interior `{0,1,2}` (the trailing `3` is to the *right* of the head and
never scanned). So **use `ScanLeft.scanLeft_run` / `scanLeft_no_early_halt`
directly** (their hypothesis is head-relative: `∀ i, 0 < i → i ≤ head → …`), or
first **relax `rewindToStart_run`/`_traj`** to a head-relative hypothesis
(constrain only `rest.take head`, not all of `rest`). The wrapper as committed
is only correct for single-sentinel tapes; fix it before use.

The intermediate gadget exit head is existential in `appendAt_run_steps`, but
the rewind works from *any* interior head, so the existential is fine — you only
need that all cells strictly left of the exit head are `≠ 3`, which holds (they
are the encoded interior).

**Step 1b-2 — per-fragment physical contract, LINEAR budget.** With the rewind
bracket, each gadget's contract is: halts at its `exit` state, head back at the
sentinel (`0`), tape `= encodeTape output`, at step
`t ≤ A·(encodeTape s).length + B·cost + C` (the gadget's `2·tapeLen+3` plus the
rewind's `tapeLen+1` plus the bracket steps — still linear), with the
no-early-halt trajectory (gadget trajectory ∘ bridge ∘ rewind trajectory). The
exit *state* is recoverable from `appendAtTM_halt_unique` +
`appendAtTM_exit_is_halt` (the unique halt state is `appendAtTM_exit dst`).

**Step 1b-3 — lift the per-fragment output bound to a max-over-fragments bound.**
`Cmd.encodeTape_eval_length_le` (done) bounds each fragment boundary's tape;
thread it through the run so every intermediate tape is `≤ size + cost +
regBound + 2` (the `+2` is the two sentinels under the new encoding).

**Step 1b-4 — set the total budget with slack.** Define `Compile_run_physical`'s
total as a quadratic-with-constant — concretely `Q(size,cost) ≈ C·cost·(size+
cost+regBound+1)`, which composes for `seq` (superadditive:
`Q(a,c1)+Q(a+c1,c2)+1 ≤ Q(a,1+c1+c2)`, the `-C·c1·c2` cross term gives the
slack) and for `forBnd` (the loop sums cost·tape over iterations ≤ total cost ×
max tape). The tight `(size+cost+1)²` cannot absorb the per-fragment constants.
Safe: `toFrameworkWitness'` only needs `inOPoly`/`monotonic` — so replace
`Compile.overhead`'s use here with `Q` (or a cubic) and re-thread
`PolyTime.toFrameworkWitness'` / `Compile.bitDecider_run`.

**Step 1c — concretise the 10 stub `compileOp`s** from the gadget library, each
with its **linear-budget** physical `compileOp_sound` (rewind-bracketed as in
1b-1).

**Step 1d — assemble** `compileSeq_sound` from `compileSeq_compose_physical`,
`compileForBnd_sound` from `loopTM_run`, `compileIfBit_sound` from
`branchComposeFlatTM_run`; then `Compile_sound`/`Compile_run_physical` by
induction.

(Alternatively, the cheaper `map`-over-lists witness — ROADMAP step 2,
`parked/MapNatList_WIP.lean` — keeps the S3 migration moving while C2 is built.)

## Conventions

- Commit per logical step with a **green build**; record gaps in commit messages.
- New results must be `#print axioms`-clean (only `propext` / `Quot.sound` /
  `Classical.choice`). **No new axioms.** Decompose `sorry`s; don't elaborate.
- Axiom check (lean-lsp's LSP has no `lake` on PATH):
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean` with
  `#print axioms <name>`.
- See ROADMAP "Hard-won gotchas" (the `omega`/`Var` trap, nested `set` blowup,
  `State.get` literal mis-resolution). **New gotcha this session:** `set` and
  other Mathlib tactics are **unavailable in `Lang/Semantics.lean` and
  `Lang/Frame.lean`** (core-only files); write folds out explicitly or factor a
  helper lemma (see `Cmd.size_run_foldl_le`).
