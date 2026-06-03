# Handoff — current state and next step

Read [`../README.md`](../README.md) and [`ROADMAP.md`](ROADMAP.md) first for the
authoritative status and plan. This file says exactly what to do next.

## Where things stand

- `lake build` ✅ green (3358 jobs). First build is slow (mathlib); one module
  rebuilds in ~5–10s after. `lake` is **not on PATH** —
  `export PATH="$HOME/.elan/bin:$PATH"`.
- **Risk C2 (compiler soundness) is the focus.** The `clear` op has a **real TM
  machine** (`clearRegionTM` in `ClearGadget.lean`), wired into `compileOp`.
  Its **full run lemma is now PROVEN** (`Compile.clearRegionTM_run`): from head `0`
  on `encodeTape s ++ res_in` it reaches `clearRegionTM_exit dst` with head `0`,
  tape `encodeTape (clear dst s) ++ (res_in ++ replicate |s.get dst| 0)`, **and a
  no-early-halt trajectory**. In `compileOp_sound_physical_residue` the **`clear`
  case's run + trajectory are discharged**; the **only remaining `clear` gap is
  the quadratic budget** `t ≤ 9·tapeLen²+9` (one isolated `sorry`, see NEXT TASK).
  The 9 cross-register ops (`copy`/`tail`/`head`/…) are still `sorry`.

## Proven this session (sorry-free, axiom-clean: propext/Classical.choice/Quot.sound)

- **Step 5a — delete-body trajectory cascade.** `encodeTape_residue_twoPhaseRewind`,
  `stepDeleteRewind_run`, `clearBody_delete_run`, `clearBody_done_run` now each
  return **`∃ t, run ∧ no-early-halt traj`** (loopTM's per-iteration contract needs
  both at the same `t`). Built by mirroring each `composeFlatTM_run` /
  `branchComposeFlatTM_run_pos/_neg` with its `_no_early_halt` analogue. The two
  `clearBody` lemmas' traj is the full loopTM shape `≠exitDone ∧ ≠exitLoop ∧ ¬halt`
  (the `≠`s via `ne_of_not_halting` + `clearBodyRawTM_exitDone/Loop_is_halt`).
- **`loopTM_no_early_halt`** (`TMPrimitives.lean`, just after `loopTM_run`): the
  reusable companion — the counted loop never reaches its halt state `B.states`
  before completion (`k < loopBudget`). Proven by the same induction as
  `loopTM_run`, using `runFlatTM_loopTM_B_phase` + `loopTM_haltingStateReached_inB`.
  **`compileForBnd` will reuse this.**
- **Step 5b — `Compile.clearRegionTM_run`** (`Compile.lean`, just before
  `compileOp_sound_physical_residue`): assembles the loop via `loopTM_run` +
  `loopTM_no_early_halt`. Tape sequence `T j = encodeTape (s.set dst (drop (n−j)))
  ++ (res_in ++ replicate (n−j) 0)`, `n = |s.get dst|`; `T n = encodeTape s ++
  res_in`, `T 0 = encodeTape (clear dst s) ++ (res_in ++ replicate n 0)`. Per
  iteration applies `clearBody_delete_run` at `s.set dst (drop (n−j−1))`; the
  state bridge is `get_set_eq`+`tail_drop`+`set_set`, the residue bridge is
  `replicate_succ'`. `tIter` is `Classical.choose` of the per-`j` existential.
- **Step 6 (partial)** — `clear` case of `compileOp_sound_physical_residue`:
  `res_out = res_in ++ replicate |s.get dst| 0` (`ValidResidue_append_replicate_zero`),
  run + traj via `clearRegionTM_run` (after `initFlatConfig` normalisation with
  `clearRegionTM_start`). New general helpers: `Compile.BitState_set`,
  `Compile.length_set`.

## NEXT TASK (ordered)

### 1. Close the `clear` budget `t ≤ 9·tapeLen²+9` (the one remaining `clear` sorry)
`t = loopBudget tIter tDone n` with `tIter`/`tDone` currently **opaque**
(`Classical.choose`). To bound it you must make the step counts **explicit**:
thread an extra `∧ t ≤ <linear-in-tapeLen>` conjunct through the existentials of
(bottom-up) `encodeTape_residue_twoPhaseRewind` → `stepDeleteRewind_run` →
`clearBody_delete_run` / `clearBody_done_run`, then a `loopBudget` bound through
`clearRegionTM_run`. The explicit counts already exist inside the proofs:
- rewind `t_rw = (head−p+1)+1+(1+1+p)` with `head = Tout.length−1`,
  `p = (encodeTape (s.set dst cs)).length−1` — so `t_rw ≤ 2·Tout.length`.
- `stepDeleteRewind` `t = 1+1+((3·(tt::suf).length+1)+1+(1+1+t_rw))`,
  `(tt::suf).length = midSuf.length < tapeLen` ⇒ `O(tapeLen)`.
- `clearBody_delete` `t = (navSteps skipped+1+1)+1+t2`; `navSteps skipped` is
  `Σ (block.len+1) + 1 ≤ |regBlocks skipped|+|skipped|+1 ≤ tapeLen`
  (`navSteps`/`navSteps_append_singleton` in `ClearGadget.lean`).
- loop: `n = |s.get dst| ≤ tapeLen` (the shifted `dst` block sits in `encodeTape s`),
  each iteration `O(tapeLen)`, so `loopBudget ≤ O(tapeLen²) ≤ 9·tapeLen²+9`
  (the `9` is generous; `omega` after the per-iteration linear bound + `n ≤ tapeLen`).
  Key length facts needed: relate `midSuf`/`regBlocks skipped`/`(s.get dst).length`
  to `(encodeTape s ++ res_in).length` (use `encodeTape_length`,
  `encodeTape_reg_decomp_at`). **Watch for `Σ` over `j<n` of a per-iter linear
  bound — `loopBudget` recursion + `n ≤ tapeLen` gives the quadratic.**
*Estimate ~150–300 LOC of arithmetic threading; structural-unknown-free.*

### 2. Cross-register ops (`copy`/`tail`/`head`/`eqBit`/`nonEmpty`/`takeAt`/`dropAt`/`concat`/`consLen`)
**The missing critical-path primitive is a single-tape block-move gadget
`copyBlockTM`** (carry `src` content to `dst`, resizing the slot); the gadget
library has scan / insert-one / delete-one but **no data transport**. Then every
cross-register op = `(clear dst) ⨾ (copyBlock src→dst) ⨾ (in-place transform)`.
Order: probe `copyBlockTM` go/no-go (`#eval` end-to-end — verify the exit head
lands in residue past the terminator, like the append op needed) **before**
proving its run/`_no_early_halt`; then per-op contracts via the
`opAppendBit_physical_residue` template + `rewindBracket`. The `clear` machinery
(`clearRegionTM_run`, `loopTM_no_early_halt`) is the reusable model for any
`loopTM`-based gadget. See ROADMAP C2.c.

### 3. Assemble `Compile_run_physical_residue`
`compileIfBit`/`compileForBnd` residue contracts (`branchComposeFlatTM_run` /
`loopTM_run` + `loopTM_no_early_halt`), then the `Compile_run_physical_residue`
induction (`sorry` in `Compile.lean`). Then S3 migration (ROADMAP step 2).

## Gotchas (still live)
- **`#eval`-probe a built machine end-to-end before proving its run lemma.** Both
  `clearRegionTM` architecture bugs (last session) were invisible to validity
  proofs; one probe surfaced them.
- **For `∃ t, A ∧ B` sharing one `t`:** give the **explicit witness**
  (`refine ⟨<expr>, ?_, ?_⟩`) or `exact ⟨_, term_A, term_B⟩` with *concrete* terms
  (the witness is read off `term_A`). `refine ⟨_, ?_, ?_⟩` (postponed `_` witness)
  fails to synthesize. Computing the explicit total = `t₁ + 1 + t₂` from the
  combinator (`composeFlatTM`/`branchComposeFlatTM`/`loopBudget`) makes both bullets'
  goals fully determined.
- **`_no_early_halt` mirrors `_run` exactly:** same args up to `h_traj2`/`h_traj3`,
  replacing each sub-`_run` with its `_no_early_halt`; `composeFlatTM_no_early_halt`'s
  `h_traj1` wants `≠exit ∧ ¬halt` (use `stepRight/LeftTM_no_early_halt`,
  `deleteCarryTM_no_early_halt`+`ne_of_not_halting`, etc.).
- **`loopTM`/`clearBody` start is provably (not always defeq) `0`** — `rw [hBstart]`
  (`= (branchComposeFlatTM …).start`, `branchComposeFlatTM_start`,
  `navigateAndTestTM_start`) to bridge `{B.start, …}` ↔ `{0, …}`.
- **`List.drop_length` takes no explicit arg** (`l.drop l.length = []`, `l` implicit);
  `rw [hn]` (where `n := (s.get dst).length`) first to expose the pattern.
- `omega` can't see through record projections / `def`-constants — `show` the
  reduced/`Nat` form first (e.g. `show _ + 19 + 1 ≠ _ + 17`).
- **`set x := e with h`** makes `x` defeq `e`; unfold `x j` in goals with
  `simp only [h]` (beta-reduces). `Classical.choose`'s value is proof-irrelevant,
  so `simp only [htIter, dif_pos hj]` exposes `(hiter_ex j hj).choose` for `choose_spec`.
- **MCP `lean-lsp` / `#print axioms` can't find `lake`.** Axiom-check via a scratch
  file: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean` with
  `import Complexity.Lang.Compile` + `#print axioms <FULLY.QUALIFIED.name>` (the
  `clear` run lemmas live in `Complexity.Lang.Compile.…`, `loopTM_no_early_halt` in
  `TMPrimitives.…`). Want only `propext`/`Classical.choice`/`Quot.sound`; **no `sorryAx`**.

## Key files & exact locations

| File | Contents |
|------|----------|
| `Lang/ClearGadget.lean` | `navigateToRegTM`/`navigateAndTestTM`/`deleteRewindRawTM`/`clearBodyRawTM`/`clearRegionTM`; validity; run-lemma steps 1–2; halt facts; `navSteps` (loop-count math); `ne_of_not_halting` |
| `Lang/Compile.lean` | compiler; residue infra; append op done; **clear run lemma steps 3–5b** (`stepDeleteRewind_run`, `clearBody_delete_run`/`_done_run` — all `run ∧ traj`; `clearRegionTM_run` `run ∧ traj`); helpers `BitState_set`/`length_set`/`set_tail_iterate`/`iterate_tail_clear`/`set_get_self`/`set_set`; `compileOp_sound_physical_residue` (**`clear` case: run+traj done, budget `sorry`**; 9 cross-register `sorry`s); `Compile_run_physical_residue` (`sorry`) |
| `Lang/ScanLeft.lean` | `stepLeft/RightTM` (+`_run`/`_no_early_halt`), `scanLeftUntilTM`, `rewindToStart_run`/`_traj`, `rewindTwoPhaseTM` (+`_run`/`_no_early_halt`) |
| `Lang/ShiftTape.lean` | `deleteCarryTM` (+`_run`/`_no_early_halt`), `insertCarryTM` |
| `Complexity/TMPrimitives.lean` | `composeFlatTM`/`branchComposeFlatTM`/`loopTM` + `_run`/`_no_early_halt`/`_valid`; **`loopTM_no_early_halt`** (new, after `loopTM_run` @~3887); `loopBudget` |

## Conventions
- Build `lake build` (or `lake build Complexity.Lang.X`); commit per logical step
  with a **green build**; new finished lemmas must be `#print axioms`-clean (only
  `propext`/`Classical.choice`/`Quot.sound`; **no `sorryAx`**).
- Probe `#eval` files via `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/probe.lean`.
- See ROADMAP "Hard-won gotchas" and "How we work" for full methodology.
