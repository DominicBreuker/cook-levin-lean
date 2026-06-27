# Handoff — refactoring the compiler (`Compile.lean`)

Working plan for the **compiler refactor**, run as its own multi-session stream
(parallel to the compiler *implementation* stream in [`HANDOFF.md`](HANDOFF.md)).
Same workflow: build green between commits, keep this doc compact and
forward-looking, hand off to the next refactoring agent.

**Goal (achieved + now in proof-perf phase).** `Compile.lean` had grown to a
single **26.5K-line / 1.5 MB Lean module** — the build's long pole and
unmaintainable. It is now a **DAG of `Compile/*` modules** (parallel compilation,
edits rebuild only the touched module + dependents). The structural split is
complete; the current focus is **Phase 4 — proof performance** (taming slow
tactics inside the now-isolated modules).

**Coordinate with `HANDOFF.md`.** Both streams edit the compiler. The split is
done, so the op stream lands its next op **in the relevant submodule**: per-op
contract + stub ops in `Compile/OpSound`; op machines in `Compile/OpMachines`;
run lemmas in the per-gadget `Compile/Run*` modules (see below).

---

## Current module structure (build green, 3370 jobs, 2026-06-27)

`Compile.lean` is a **39-line pure facade** (imports only). The DAG, under
`CookLevin/Complexity/Lang/Compile/`, with per-module compile time (★ = updated
this session):

```
(primitives: Syntax Semantics Frame Navigate ScanPast ScanLeft ShiftTape
             AppendGadget ClearGadget; TMPrimitives, TapeMono)
      │
  Core (524)          CompiledCmd, joinTwoHalts, rewindBracket, combinators
      ├───────────────┐
  Encoding (708)      encodeTape/decodeTape, BitState, ValidResidue, structure lemmas
      │               │
  OpMachines (3621, ★7.7s) every per-Op TM machine *def* + shape lemmas
      │
  Cmd (950, 3.4s)     compileOp/Seq/IfBit/TestBit + forBnd machines + compileCmd
      │
  ── RunLemmas DAG (chain Clear → Move → CopyTail → EqBit) ──
  RunClear (2358, 6.9s)     append per-op soundness, compileSeq_compose_physical,
      │                     shared ValidResidue/TapeOK residue toolkit, clear stack
  RunMove (4382, 11s)       move-one-bit / dual-target transfer gadgets,
      │                     navTestReg reading, compileTestBit run lemmas
  RunCopyTail (3471, ★~11s)  cursor-copy (copy) + tail run stacks; step lemmas
      │                     de-simp_all'd this session — now structurally bound
  RunEqBit (4011, 13s)      eqBit no-grow consume-loop run stack (opEqBitNG_run)
      │
      │   RunLemmas (2.3s)  ★ no-content facade — now imported ONLY by Compile.lean
      │   (off path)        (OpSound/Assembly/Decider import the 4 Run mods direct)
      │
  OpSound (558, 3.4s)       compileOp_sound_physical_residue (8 ops ✓, 4 stub sorries)
      │
  Assembly (2740, ~10s)     C6 bitTestTM, assembly toolkit, compileIfBit/compileForBnd
      │                     soundness + forBnd loop run stack, Compile_run_physical_residue
  Decider (991, 5.8s)       the WALL: padRegsTM / paddedBitDecider / paddedCompute
      │
  Compile.lean (39)         facade (imports Decider + RunLemmas)
```

Axiom invariant (unchanged): `#print axioms` of
`Complexity.Lang.compileOp_sound_physical_residue` /
`Compile.paddedBitDecider_run` / `Compile.paddedCompute_run`
= `[propext, sorryAx, Classical.choice, Quot.sound]` (the `sorryAx` = the 4 stub
ops in the contract, none on the live `sat_NP` path).

---

## What's left (recommended next steps, priority order)

The structural split is done; **proof-perf is the remaining lever.** The cheap
big wins are largely spent: the slow `simp_all`/`nlinarith` calls and the
`_`-underscore unification blowups have been killed across `RunEqBit`,
`RunCopyTail`, and `OpMachines`. **Every Compile module now profiles with no
single tactic over ~0.3s except: `Decider` (2 structural `isDefEq` exacts) and
`Assembly` (one `nlinarith` interpreter load).** Remaining work is harder /
lower-value.

### 1. Phase 4 — `Decider` `paddedBitDecider_run` / `paddedCompute_run` (~3.4s).

The only remaining big single-tactic costs in the DAG: a `refine ⟨…⟩` (1.7s,
`paddedBitDecider_run` L796) and `exact runFlatTM_extend (M := …) hcrun hchalt`
(1.8s, `paddedCompute_run` L990). These are **big-term `isDefEq`/elaboration**
(matching `runFlatTM <big budget Nat> (paddedComputeTM c k)` against the
composed-run hypothesis whose machine is the unfolded `composeFlatTM …`), **not**
`simp`/`nlinarith`. The explicit-args trick (§Method 3c) does **not** apply
(`M` is already explicit). **TRIED & FAILED (2026-06-27c):** `set N := <budget>`
before the `exact` (to stop re-elaborating the big budget Nat) gave **no change**
(still 1.7s/1.8s) — so the cost is **not** the budget but the **machine defeq**
`paddedComputeTM c k ≡ composeFlatTM (padRegsTM K) (Compile k c) (padRegsExit K)`,
which compares the *built* transition tables of two big composed machines
(traversing `Compile k c`). **Also TRIED & FAILED (2026-06-27d):** the one-shot
`rfl`-bridge `have hM : paddedComputeTM c k = composeFlatTM (padRegsTM K)
(Compile k c) (padRegsExit K) := rfl; rw [hM]` (to make the machine match `hcrun`
syntactically) — `exact` **still 1.72s**, so the cost is **not** the machine
defeq either; it is the intrinsic elaboration of the big goal type (the result
config carries `encodeTape (c.eval (s ++ replicate K []))`). Both cheap angles
are exhausted; a real win needs deep restructuring (e.g. making the composed
machines genuinely opaque/irreducible throughout — ripples through many proofs).
Modest payoff (~1.7s on a 5.8s module, 2.3s of which is fixed import). **Likely
not worth it.**

### 2. Phase 4 — `Assembly` `nlinarith` (~10s) — almost certainly not worth it.

`Assembly`'s only >0.3s cost is `interpretation of …nlinarith…_boxed` (1.2s) —
the **fixed nlinarith interpreter load**, paid once because `forBndBudget_arith`'s
`core` carries the module's lone `nlinarith`. Its goal genuinely needs nonlinear
reasoning (`q = iters²−iters` binds the negative `iters` terms; manual case-split
is painful). Removing it is the only way under ~9s but the cost/risk is poor.

### 3. (Optional) split the largest Run* modules further — low value.

Only if the ~11–15s modules become a felt bottleneck. Clean two-way cuts
(verified earlier): **RunCopyTail** → `copy` (L27–2348) vs `tail` (L2349–EOF);
**RunMove** → cut at `moveRegion2TM` (L1742); **RunEqBit** → consume-loop helpers
(L212–1756) vs `testMachine`/`compareLoopTM` (L1757–EOF). These modules import
each other (a chain), so the parallelism gain is modest.

### 4. Cleanup (cheap, do alongside).

- Stale `probes/*Probe.lean` at the **repo root** (not built). Some reference
  Phase-0-deleted symbols; but `CursorCopyProbe`/`ForBndSkeletonProbe`/
  `EqBitNoGrowProbe`/`CopyEmptyProbe` are **cited by name in ROADMAP/HANDOFF** as
  validation evidence — grep-confirm before pruning those.
- Minimal-imports prune on the Run* modules (cosmetic).
- `push_neg` deprecation: two remain in `Complexity/Complexity/TMPrimitives.lean`
  (L2738/4006) — out of scope but trivial if touched.

---

## Method

### Splitting a module (reuse for §3)

1. Pick a cut at a `/-! ### …` section boundary (a `theorem` moves whole).
2. Static dependency scan: every cross-cut reference must go **forward** in
   dependency order (bucket decls by line range, flag any reference to a
   later-defined name; filter doc-comment noise). Section order is the dep order.
3. Strip `private` on decls referenced across the cut (widening visibility never
   breaks exports; check no two privates share a name).
4. New `Compile/<Name>.lean`: standard import header (primitives + prior Run
   modules) + `set_option autoImplicit false` + `namespace Complexity.Lang` +
   `open TMPrimitives` + `open scoped BigOperators`, then the moved block. Keep
   the old module as a facade importing the new one (downstream imports untouched).

### Proof-perf (Phase 4 — used this session)

1. **Profile a module:** `lake env lean -Dprofiler=true CookLevin/Complexity/Lang/Compile/<Mod>.lean`.
   Sort `took …s` lines; the per-tactic `interpretation of …nlinarith…` / `simp took …`
   entries pinpoint hot spots. Map nlinarith costs to sites by **source order**
   (the profiler emits in elaboration order; cross-reference `grep -n nlinarith`).
2. **Cost model (learned this session):** a module's `nlinarith` cost ≈ a fixed
   per-module **interpreter load** (paid once if *any* `nlinarith` is present) +
   each call's **genuine search**. So the wins are (a) kill a genuinely-slow
   search — the 11s `key` call was the whole RunEqBit win; (b) to recover the
   load itself, remove **every** `nlinarith` from the module. Removing *some* does
   nothing.
3. **Replace patterns:** an exact-cancellation inequality → `ring` split + one
   monotonicity + `omega`; a quadratic budget → explicit `Nat.mul_le_mul(_right)`
   monotonicity (`hA`/`hB`) + a `ring` identity + `linarith` (keep everything
   linear over the monomial atoms — `linarith`/`omega` treat `L*L`, `L*(a+b)` as
   atoms; `omega` even abstracts a nonlinear subterm as a nonneg atom after you
   `rw` it into view). A sum-of-budgets `nlinarith` → `linarith`.
3b. **`simp_all` → plain `simp` for goal-directed step lemmas (2026-06-27b
   win).** The per-step TM-simulation lemmas (`stepFlatTM … = some {…}`) were
   proven with `simp_all [stepFlatTM, …]`, which re-simplifies *every* hypothesis
   to a fixpoint — ~0.9s each. They only need the goal rewritten by the symbol
   fact (`hsym`) and (when the entry writes a symbol) `dif_pos` discharged from
   `hlt`. **Fix:** `simp [hsym, hlt, <same step defs>]` — plain `simp` (goal-only)
   keeps simp's automatic `decide`/length/`find?` handling (so no fragile
   `simp only` lemma list) but skips the hypothesis fixpoint. Dropped 7 calls from
   6.4s to ~0.1s reported. Omit `hlt` when the entry's `dst_write_vals` is `[none]`
   (no `writeCurrentTapeSymbol` branch — the unused-simp-arg linter flags it).
3c. **Explicit args kill `_`-underscore unification blowups (2026-06-27c win).**
   The `*_is_halt`/`*_halt_only` lemmas applied a `branchComposeFlatTM_*` halt
   lemma with ALL machine/index args as `_` (`exact lemma _ _ _ _ _ _ (h2v) …`),
   after a `rw […machineDef]` that unfolds the goal to a big composed-machine
   term. Lean then infers the 6–8 metavars by **unifying the lemma conclusion
   against that big term** — `compareBodyTM_exitDone_is_halt` cost **4.1s** this
   way. **Fix:** pass the machine and exit-index args **explicitly** (read them
   off the machine's `def`: e.g. `branchComposeFlatTM_M3_halt_intro (testMachine …)
   (iterTailsTM …) idTM (exit_iter …) (exit_done …) 0 (h2v) (h)`). With the
   metavars pre-assigned there is no search; the three OpMachines calls dropped
   from ~7.4s combined to <0.3s each (module 9.7s → 7.7s). **Caveat:** this does
   NOT help when the slow defeq is over a *budget Nat* with the machine already
   explicit (the Decider `runFlatTM_extend` exacts — §1).
4. **Iterate fast** on a self-contained pure-`Nat` lemma in a scratch file with
   `import Mathlib.Tactic.Linarith`/`.Ring` (≈4s/build) instead of the full
   `import Mathlib` (≈50s) or the module rebuild — but the **module rebuild is the
   final oracle** (scratch can't reproduce the per-module interpreter-load cost).
5. **Tooling:** `export PATH="$HOME/.elan/bin:$PATH"` (lake/lean not on PATH — also
   why most MCP/LSP features fail). `LEAN_PATH=$(lake env printenv LEAN_PATH)` for
   scratch builds. Per-module: `lake build Complexity.Lang.Compile.<Mod>`.
6. **Axiom-clean check** after each phase: `env LEAN_PATH=$(lake env printenv
   LEAN_PATH) lean /tmp/chk.lean` with `#print axioms
   Complexity.Lang.compileOp_sound_physical_residue` /
   `Complexity.Lang.Compile.paddedBitDecider_run` / `…paddedCompute_run` — must
   stay the 4-axiom set (no *new* `sorryAx`).
7. Commit per coherent change (green), module name(s) in the message.

### Build-graph perf (orthogonal to proof-perf)

8. **A no-content facade on the critical path is a pure import gate — bypass it.**
   `RunLemmas` only re-imports the four Run modules. As a node *on* the serial
   `RunEqBit → OpSound → … → Decider` chain it cost ~2.3s (load all four Run
   oleans, emit an empty olean) for zero elaboration. **Fix:** point the internal
   consumers (`OpSound`/`Assembly`/`Decider`) at the four Run modules **directly**
   (same transitive scope ⇒ strictly safe); keep the facade only for the public
   `Compile.lean` import (which is past `Decider`, the long pole, so the facade is
   off the path). Generalises: any pure re-export facade sitting between two heavy
   modules is removable from the critical path this way. (Cannot do this for
   `Compile.lean` itself — `PolyTime` imports the facade by contract, README.)

- `autoImplicit false` / `relaxedAutoImplicit false` are package-wide
  (`lakefile.lean`); new modules inherit them — don't re-add `relaxedAutoImplicit`.
- `⨾`/`composeFlatTM`/`branchComposeFlatTM`/`loopTM` come from
  `Complexity.Complexity.TMPrimitives` — every gadget module needs it imported.
- **Don't double-background builds.** Use the harness `run_in_background` *or* a
  shell `&`, never both. Redirect to a logfile and poll for
  `"completed successfully"`. First full build from a clean container is slow
  (~minutes); kick it off early.
- Foreground `sleep` is killed by the harness at 2 min — poll in short loops.
- Don't touch `PolyTime.lean`'s import (it imports the `Compile` facade).

---

## Status

- [x] **Phase 0** — dead-code deletion (2,415 lines / 101 dead decls).
- [x] **Phase 1** — leaf modules: `Core`, `Encoding`, `OpMachines`.
- [x] **Phase 2** — compiler defs: `Cmd`.
- [x] **Phase 3** — run lemmas + soundness + assembly + decider + facade.
      Monolith reduction: 26,493 → 39 lines.
- [x] **Phase 1-refinement** — split `RunLemmas` (14,150 lines) into
      `RunClear`/`RunMove`/`RunCopyTail`/`RunEqBit` (2026-06-26).
- [x] **Phase 4 (2026-06-27a)** — proof-perf: killed the slow budget
      `nlinarith`s. **RunEqBit 18s → 13s** (the ~11s `key` cancellation call +
      `eqBit_budget_arith` rewritten to explicit `Nat` steps; module now has zero
      `nlinarith`). `Assembly` budget `nlinarith`s simplified. Build green,
      axioms unchanged.
- [x] **Phase 4 (2026-06-27b)** — proof-perf: **`RunCopyTail` step lemmas
      de-`simp_all`'d.** The 7 per-step TM-sim `simp_all` calls (`markBitTM_step`,
      `restoreStepTM_step`, `skipReadTM_step_delim/_bit`) → goal-directed plain
      `simp [hsym, hlt, …]`. Reported simp 6.4s → ~0.1s; module now has **no
      tactic over ~0.2s** (structurally bound, like `RunMove`). Build green
      (3370 jobs), axioms unchanged.
- [x] **Phase 4 (2026-06-27c)** — proof-perf: **`OpMachines` halt lemmas
      de-`_`'d.** Three halt-characterization `exact`s (`compareBodyTM_exitDone_is_halt`
      4.1s, `testMachineRawM_done_is_halt` 1.7s, `testMachineRawM_halt_only` 1.6s)
      passed all `branchComposeFlatTM_*` machine/index args as `_`, forcing big-term
      metavar unification. Made them explicit → all three <0.3s; **OpMachines
      9.7s → 7.7s** (upstream of everything ⇒ shortens the serial critical path).
      Build green (3370 jobs), axioms unchanged.
- [x] **Phase 4 (2026-06-27d)** — build-graph: **bypassed the `RunLemmas`
      facade** on the critical path (OpSound/Assembly/Decider now import the four
      Run modules directly; RunLemmas kept only for `Compile.lean`). Removes a
      ~2.3s import-only serial gate between `RunEqBit` and `OpSound`. Build green
      (3370 jobs), axioms unchanged.
- [ ] **Phase 4 (continue) — essentially spent.** Remaining big single-tactic
      costs are only **`Decider`** (~3.4s structural `isDefEq` `refine`/`exact`;
      §1 — **two cheap fixes TRIED & FAILED**: budget-`set` and the `composeFlatTM`
      `rfl`-bridge, both no-change, so it needs risky deep restructuring) and
      **`Assembly`** (1.2s fixed `nlinarith` load; §2 — goal is genuinely
      nonlinear, confirmed by hand, not worth it). Every other Compile module is
      structurally bound (no tactic >0.3s) and the one removable facade gate is
      gone. Further build-time gains need either accepting risk on the Decider
      assembly proofs or out-of-scope work (mathlib import surface).
