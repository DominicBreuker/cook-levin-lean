# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first for the
authoritative status and plan. This file says exactly what to do next.

## Where things stand

- `lake build` ✅ green (3358 jobs). First build is slow (mathlib); one module
  rebuilds in ~10s after. `lake` is **not on PATH** —
  `export PATH="$HOME/.elan/bin:$PATH"`.
- **Risk C2 (compiler soundness) is the focus.** In the residue-tolerant per-op
  contract `compileOp_sound_physical_residue` (`Compile.lean`), the **`clear`
  case is now FULLY proven** (run + trajectory + the quadratic budget `t ≤
  9·tapeLen²+9`), joining the two `appendOne`/`appendZero` cases. The **9
  cross-register ops** (`copy`/`tail`/`head`/`eqBit`/`nonEmpty`/`takeAt`/`dropAt`/
  `concat`/`consLen`) are still `sorry`. After them comes the assembly
  (`compileIfBit`/`compileForBnd` residue + `Compile_run_physical_residue`).

## Proven this session (sorry-free, axiom-clean: propext/Classical.choice/Quot.sound)

- **Step 6 — the clear-loop quadratic budget.** Threaded an **explicit
  linear-in-tape-length step bound** through the whole clear run-lemma chain
  (each existential gained a `∧ t ≤ <linear>` conjunct): bottom-up
  `encodeTape_residue_twoPhaseRewind` (`≤ tapeLen+3`) → `stepDeleteRewind_run`
  (`≤ 4·L+9`) → `clearBody_delete_run` / `clearBody_done_run` (`≤ 6·L+12`) →
  `clearRegionTM_run` (`≤ 9·L²+9`). Then the `clear` case of
  `compileOp_sound_physical_residue` just forwards `clearRegionTM_run`'s bound.
- **Reusable budget helpers** (`Compile.lean`, just before `clearRegionTM_run`):
  - `Compile.loopBudget_le : (tDone+1 ≤ M) → (∀ j<n, tIter j+1 ≤ M) →
    loopBudget tIter tDone n ≤ (n+1)·M`. **Every `loopTM`-based gadget reuses
    this** to turn a per-iteration linear bound into the `(n+1)·M` total.
  - `Compile.clearBudget_arith : n+2 ≤ L → (n+1)·(6·L+13) ≤ 9·L²+9` (proven by
    substituting `L = n+2+d`, `nlinarith`).
- **`ClearGadget.navSteps_le : navSteps skipped ≤ 2·|regBlocks skipped|+1`** (the
  linear navigation-step bound).
- Inside `clearRegionTM_run`: **`hTlen`** (every loop tape `T j` has the *same*
  length `L = |encodeTape s ++ res_in|` — a delete frees a cell but appends a `0`
  filler) and **`hnL : n+2 ≤ L`** (via `State.size_set_add s dst []`; the cleared
  register's `n` bits sit inside the encoded tape).

## ⚠ Risk surfaced this session — the per-op budget constant `9·L²+9` is TIGHT

The clear budget closes only because of the **tight** `n+2 ≤ L` (not just `n ≤ L`)
and **carefully-bounded** per-iteration constants (`6·L+13`); a naive per-iter
bound *fails the inequality at small `L`*. **This matters for the cross-register
ops:** each one compiles to a *single* machine that internally does
`clear dst ⨾ copyBlock src→dst ⨾ transform` — each phase is itself `Θ(L²)` on a
single tape. Their **sum may exceed `9·L²+9`**, making the current statement
constant unsatisfiable. Plan for it: **you will likely bump the `9·L²+9` in
`compileOp_sound_physical_residue`'s statement to a larger quadratic** (e.g.
`C·L²+C`; `toFrameworkWitness'` only needs `inOPoly`, so any constant is fine).
If you do, update **three sites consistently**: (1) the statement; (2) the two
append cases (currently relax linear → `9·L²+9` via
`Compile.linear_le_quadratic_tapeLen`; add a `le_trans` to the new constant); (3)
the `clear` case (forwards `clearRegionTM_run`'s `9·L²+9`; add a `le_trans` to the
new constant). `clearRegionTM_run` itself can keep `9·L²+9`.

## NEXT TASK (ordered)

### 1. The block-move gadget `copyBlockTM` (the missing critical-path primitive)
The gadget library has only **single-cell** carries (`ShiftTape.insertCarryTM` /
`deleteCarryTM`) — **no data transport** between two register slots on the same
tape. Every cross-register op needs one: `Op.eval` is `s.set dst (f (s.get src))`
(reads `src`, writes `dst`; the real witnesses use `dst ≠ src`, e.g. `Op.tail 2
0`). So each op = `clear dst` (now DONE, reuse `clearRegionTM_run`) ⨾
`copyBlock src→dst` ⨾ `in-place transform on dst`.
- **Probe first (`#eval`, go/no-go).** Build `copyBlockTM` and verify *end-to-end*
  that it carries `src`'s content into `dst`'s (resized) slot and **exits with the
  head in residue past the trailing terminator** — exactly the architecture-bug
  class that bit the append and clear gadgets (invisible to validity proofs;
  `#eval`-probe via `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/probe.lean`).
- It will almost certainly be a **`loopTM`** (ferry one bit per iteration). When you
  prove its run lemma, give each iteration a **linear** `∧ t ≤ c·L+d` bound and
  feed `Compile.loopBudget_le` + a `clearBudget_arith`-style closer — the **exact
  template `clearRegionTM_run` now provides** (copy it).
- Then per-op contracts via the `opAppendBit_physical_residue` template +
  `rewindBracket`. The `clear` machinery (`clearRegionTM_run`, `loopTM_no_early_halt`,
  the budget threading) is the reusable model.

### 2. Assemble `Compile_run_physical_residue`
`compileIfBit`/`compileForBnd` residue contracts
(`branchComposeFlatTM_run` / `loopTM_run` + `loopTM_no_early_halt`), then the
`Compile_run_physical_residue` induction (`sorry` in `Compile.lean`). Then S3
migration (ROADMAP step 2).

## How the budget threading works (reuse this exactly)

To bound an opaque `Classical.choose` step count, you **must** carry the bound in
the existential — there is no shortcut. Pattern, bottom-up:
1. Add `∧ t ≤ <linear in input tape length>` to each run lemma's `∃ t, …`.
2. The witness is already explicit (`refine ⟨<expr>, …⟩`); add one `?_` goal and
   close it with `omega`, having first established the sub-lemma's bound (`obtain
   ⟨…, hb⟩`) and the **tape-length bridges** (e.g. `hLinTout`, `hTlen`).
3. **`omega` + cons/append lengths:** `rw [List.length_cons]` fires on the
   **first** `(_::_).length` — which may be a `pre = endMark :: …` you didn't mean.
   Use **`simp [List.length_append, List.length_cons]`** (full simp normalises the
   Nat arithmetic and avoids the wrong-cons trap) instead of a hand `rw` chain.
4. For the `loopTM` total: `Compile.loopBudget_le` (per-term `M`) then the
   `clearBudget_arith` quadratic closer (substitute `L = n+2+d`, `nlinarith`).

## Gotchas (still live)
- **`#eval`-probe a built machine end-to-end before proving its run lemma.** Both
  `clearRegionTM` architecture bugs (a prior session) were invisible to validity
  proofs; one probe surfaced them. The append/clear gadgets all **exit on the
  trailing terminator**, head in residue — design `copyBlockTM` the same way and
  bracket it with the **two-phase** rewind (`rewindBracket`).
- **For `∃ t, A ∧ B ∧ (t ≤ …)` sharing one `t`:** give the **explicit witness**
  (`refine ⟨<expr>, ?_, ?_, ?_⟩`); the witness is read off the run term, so the
  bound goal is fully determined for `omega`.
- **`_no_early_halt` mirrors `_run` exactly** (same args up to the trajectory
  inputs, each sub-`_run` replaced by its `_no_early_halt`).
- **`omega` can't see through record projections / `def`-constants** — `show` the
  reduced/`Nat` form first.
- **`set x := e with h`** makes `x` defeq `e`; `Classical.choose`'s value is
  proof-irrelevant, so `simp only [hx, dif_pos hj]` exposes `(…).choose` for
  `choose_spec` (and `.choose_spec.2.2` is the bound conjunct).
- **MCP `lean-lsp` / `#print axioms` can't find `lake`.** Axiom-check via a scratch
  file: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean` with
  `import Complexity.Lang.Compile` + `#print axioms <FULLY.QUALIFIED.name>`. Want
  only `propext`/`Classical.choice`/`Quot.sound`; **no `sorryAx`**.

## Key files & exact locations

| File | Contents |
|------|----------|
| `Lang/ClearGadget.lean` | clear machines; validity; halt facts; `navSteps` + **`navSteps_le`** (loop-count math); `ne_of_not_halting` |
| `Lang/Compile.lean` | compiler; residue infra; append + **clear** ops done; **budget helpers `loopBudget_le`/`clearBudget_arith`** (before `clearRegionTM_run`); clear run-lemma chain (`stepDeleteRewind_run`, `clearBody_delete_run`/`_done_run`, `clearRegionTM_run` — all carry a `∧ t ≤ linear/quadratic` bound); `compileOp_sound_physical_residue` (**append + clear cases done**; 9 cross-register `sorry`s); `Compile_run_physical_residue` (`sorry`) |
| `Lang/ScanLeft.lean` | `stepLeft/RightTM`, `scanLeftUntilTM`, `rewindToStart_run`/`_traj`, `rewindTwoPhaseTM` (+`_run`/`_no_early_halt`) |
| `Lang/ShiftTape.lean` | `deleteCarryTM` / `insertCarryTM` (+`_run`/`_no_early_halt`) — **single-cell only; `copyBlockTM` must be built here** |
| `Complexity/TMPrimitives.lean` | `composeFlatTM`/`branchComposeFlatTM`/`loopTM` + `_run`/`_no_early_halt`; `loopBudget`; `loopTM_no_early_halt` |

## Conventions
- Build `lake build` (or `lake build Complexity.Lang.X`); commit per logical step
  with a **green build**; new finished lemmas must be `#print axioms`-clean (only
  `propext`/`Classical.choice`/`Quot.sound`; **no `sorryAx`**).
- See ROADMAP "Hard-won gotchas" and "How we work" for full methodology.
