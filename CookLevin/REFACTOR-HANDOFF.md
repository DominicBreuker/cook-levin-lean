# Handoff — refactoring the compiler (`Compile.lean`)

Working plan for the **compiler refactor**, run as its own multi-session stream
(parallel to the compiler *implementation* stream in [`HANDOFF.md`](HANDOFF.md)).
Same workflow: build green between commits, keep this doc compact and
forward-looking, hand off to the next refactoring agent.

**Goal (achieved).** `Compile.lean` had grown to a single **26.5K-line / 1.5 MB
Lean module** — the build's long pole (no intra-file parallelism) and
unmaintainable (any one-line edit recompiled all 26K lines + the whole downstream
proof). It is now a **DAG of `Compile/*` modules**, so compilation parallelises
and edits rebuild only the touched module + its dependents. The single 14K-line
pole (`RunLemmas`) was the last remnant — **now split too** (2026-06-26). No
module exceeds ~16s to compile.

**Coordinate with `HANDOFF.md`.** Both streams edit the compiler. The split is
done, so the op stream should land its next op (`concat`, the stub-op threading,
etc.) **in the relevant submodule** — the per-op contract + stub ops live in
`Compile/OpSound`; the op machines in `Compile/OpMachines`; run lemmas in the
`Compile/Run*` modules (per gadget — see below). Edits there no longer rebuild
the rest of the compiler.

---

## Current module structure (build green, 3370 jobs, 2026-06-26)

`Compile.lean` is a **39-line pure facade** (imports only; `PolyTime.lean` still
`import`s `Complexity.Lang.Compile` and gets everything). The DAG, under
`CookLevin/Complexity/Lang/Compile/`, with per-module compile time:

```
(primitives: Syntax Semantics Frame Navigate ScanPast ScanLeft ShiftTape
             AppendGadget ClearGadget; TMPrimitives, TapeMono)
      │
  Core (524)          CompiledCmd, joinTwoHalts, rewindBracket, combinators
      ├───────────────┐
  Encoding (708)      encodeTape/decodeTape, BitState, ValidResidue, structure lemmas
      │               │   (sibling of Core; primitives only)
  OpMachines (3621)   every per-Op TM machine *def* + shape lemmas
      │
  Cmd (950, 3.4s)     compileOp/Seq/IfBit/TestBit + forBnd machines + compileCmd
      │
  ── RunLemmas DAG (was one 14,150-line module; split 2026-06-26) ──
  RunClear (2358, 6.9s)     append per-op soundness, compileSeq_compose_physical,
      │                     the shared ValidResidue/TapeOK residue toolkit, clear stack
  RunMove (4382, 11s)       move-one-bit / dual-target transfer gadgets,
      │                     navTestReg reading (skipped_*), compileTestBit run lemmas
  RunCopyTail (3471, 14s)   cursor-copy (copy) + tail run stacks
      │
  RunEqBit (4011, 16s)      eqBit no-grow consume-loop run stack (opEqBitNG_run)
      │
  RunLemmas (25, 2.3s)      facade: imports the four Run* modules (downstream
      │                     OpSound/Assembly/Decider import this, unchanged)
  OpSound (558, 3.4s)       compileOp_sound_physical_residue (8 ops ✓, 4 stub sorries)
      │                     + compileSeq physical/residue soundness
  Assembly (2740, 10s)      C6 bitTestTM, assembly toolkit, compileIfBit/compileForBnd
      │                     soundness + forBnd loop run stack, Compile_run_physical_residue,
      │                     bitDeciderTM/bitDecider_run
  Decider (991, 5.8s)       the WALL: padRegsTM / paddedBitDecider / paddedCompute
      │
  Compile.lean (39)         facade: imports all of the above
```

Run* dependency order is a **chain** Clear → Move → CopyTail → EqBit (EqBit
reuses copy/tail; copy/tail use the cursor/`navTestReg` helpers; the residue
toolkit in RunClear is shared by all).

Axiom invariant (unchanged throughout): `#print axioms
Complexity.Lang.compileOp_sound_physical_residue` /
`Compile.paddedBitDecider_run` / `Compile.paddedCompute_run`
= `[propext, sorryAx, Classical.choice, Quot.sound]` (the `sorryAx` is the 4 stub
ops in the contract — `concat`/`takeAt`/`dropAt`/`consLen`, none on the live
`sat_NP` path).

---

## What's left (recommended next steps, in priority order)

The **structural split is essentially complete** — there is no longer a single
build pole; the longest module compiles in ~16s and the Run* modules are
~11–16s, well balanced. Remaining work has diminishing structural returns; the
highest-leverage item is now proof-perf, not more splitting.

### 1. Phase 4 — tame slow proofs. ★ now the highest-value refactor lever

With modules isolated, profile the slowest (`lean --profile`, or
`mcp__lean-lsp__lean_profile_proof` — note LSP/MCP can't find `lake`, so use a
scratch file with `env LEAN_PATH=$(lake env printenv LEAN_PATH)`). Known hot
spots: `nlinarith`/`omega` on quadratic budgets (`eqBit_budget_arith`,
`forBndBudget_arith`), big `simp`. Replace with explicit `Nat.*` term steps where
they dominate. The 16s `RunEqBit` / 14s `RunCopyTail` are the modules to profile
first.

### 2. (Optional) Split the largest Run* modules further — low value

Only worth it if the ~11–16s modules become a felt bottleneck. Clean section
boundaries (verified 2026-06-26; same method as before):

- **RunCopyTail (3471)** → cleanest two-way: `copy` (the cursor-copy stack,
  lines 27–2348) vs `tail` (2349–EOF). Independent gadgets.
- **RunMove (4382)** → cut at the dual-target gadget `moveRegion2TM` (line 1742):
  the move-one-bit + navTestReg + `compileTestBit` block (28–1741) vs
  `moveRegion2TM` (1742–EOF, ~2640 lines).
- **RunEqBit (4011)** → the consume-loop helper machines (`navTestRewindM`/
  `readBitRewindM`/`eqVerdictM`/`bitCompareM`/`bothNonemptyM`, lines 212–1756) vs
  `testMachine`/`compareBodyTM`/`compareLoopTM` + the relocated no-grow run stack
  (1757–EOF). Note the helpers form a chain, so the win is modest.

Expect each cut to balance against the chain (these modules import each other),
so the parallelism gain is smaller than the original `RunLemmas` split.

### 3. Cleanup (cheap, do alongside)

- Stale `probes/*Probe.lean` at the **repo root** (not under `CookLevin/`; not in
  the build — `lean_lib` roots are `Basic`/`Complexity`). Some reference symbols
  deleted in Phase 0 (`GrowEmpty`/`ShrinkEmpty`/`CompareRegs*`). **Caution:**
  several others (`CursorCopyProbe`, `ForBndSkeletonProbe`, `EqBitNoGrowProbe`,
  `CopyEmptyProbe`) are cited **by name in `ROADMAP.md`/`HANDOFF.md`** as
  probe-validation evidence — deleting them removes referenced documentation.
  Prune the genuinely-stale ones, keep (or grep-confirm-unreferenced before
  removing) the cited ones.
- Minimal-imports prune: each Run* module imports the full primitive list; could
  be trimmed to actual deps (cosmetic).
- `push_neg` deprecation: fixed in `Compile/Cmd.lean` (2026-06-26); two remain in
  `Complexity/Complexity/TMPrimitives.lean` (L2738/4006) — out of the compiler
  refactor's scope but trivial if touched.

---

## Method (used for every split this stream — reuse it)

1. **Pick a cut at a section boundary** (`/-! ### …`), not mid-decl. A `theorem`
   moves whole.
2. **Dependency scan** (static, before building): the block must only reference
   decls in already-imported modules + itself, i.e. all cross-cut references go
   **forward** in dependency order. A quick Python check works well: bucket every
   decl by block (line range), then flag any line in block B that references a
   name defined in a *later* block (filter doc-comment noise like `below`, header
   refs). The `RunLemmas` split had **zero** real backward refs once comments were
   filtered — confirming the section order *is* the dependency order.
3. **Scan `private` decls referenced across the cut** → strip `private` (widening
   visibility never breaks exports; check no two privates share a name first).
   The `RunLemmas` split widened 7 (`BitState_get`/`_set_tail`, `appendBit_sound`,
   `skipped_length`/`_ok`, `sym_bound_of_lt_four`,
   `encodeTape_append_res_lt_four`); the other 42 privates stayed local.
4. Create `Compile/<Name>.lean`: the standard import header (primitives + the
   prior Run modules) + `set_option autoImplicit false` + `namespace
   Complexity.Lang` + `open TMPrimitives` + `open scoped BigOperators`, then the
   moved block. Keep `RunLemmas.lean` as the **facade** (import the new module),
   so downstream imports are untouched.
5. **Build is the oracle** (`export PATH="$HOME/.elan/bin:$PATH"; lake build` —
   lake is **not** on PATH, which is also why most MCP/LSP features fail). First
   full build from a clean container is slow (~minutes); kick it off in the
   background early. Per-module: `lake build Complexity.Lang.Compile.<Name>` only
   compiles that module + its (cached) deps — use it to iterate fast, then one
   full `lake build` at the end for the facade + downstream.
6. **Axiom-clean check** after each phase via a scratch file
   (`env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean`,
   `#print axioms …`) — must stay the 4-axiom set above (no *new* `sorryAx`). Use
   fully-qualified names: `Complexity.Lang.compileOp_sound_physical_residue`,
   `Complexity.Lang.Compile.paddedBitDecider_run`/`paddedCompute_run`.
7. Commit per module (green), module name in the message.

### Gotchas

- `set_option autoImplicit false` / `relaxedAutoImplicit false` are package-wide
  (`lakefile.lean`); new modules inherit them — don't re-add `relaxedAutoImplicit`
  (the Run modules add only `autoImplicit false`, matching the prior style).
- `⨾` / `composeFlatTM` / `branchComposeFlatTM` / `loopTM` come from
  `Complexity.Complexity.TMPrimitives` — every gadget module needs it imported.
- **Don't double-background builds.** Use the harness's `run_in_background`
  *or* a shell `&`, never both (it detaches the wrapper and you lose the exit
  code; a stray `pkill` then shows up as exit 137/144, not a real error). Tip:
  redirect to a logfile and poll it (`grep -q "completed successfully"`).
- Don't touch `PolyTime.lean`'s import — it imports `Complexity.Lang.Compile`
  (the facade); keep that working.

---

## Status

- [x] **Phase 0 — dead-code deletion** (2,415 lines / 101 dead decls).
- [x] **Phase 1 — leaf modules:** `Core`, `Encoding`, `OpMachines`.
- [x] **Phase 2 — compiler defs:** `Cmd`.
- [x] **Phase 3 — run lemmas + soundness + assembly + decider + facade:**
      `RunLemmas`, `OpSound`, `Assembly`, `Decider`; `Compile.lean` → 39-line
      facade. Whole-stream monolith reduction: 26,493 → 39 lines.
- [x] **Phase 1-refinement — split `RunLemmas`** (14,150 lines) into
      `RunClear`/`RunMove`/`RunCopyTail`/`RunEqBit` (2026-06-26). Build green
      (3370 jobs), axioms unchanged, longest module now ~16s (was a single 14K
      pole). `push_neg`→`push Not` cleanup in `Cmd` folded in.
- [ ] **Phase 4 (optional)** — proof-perf (profile `RunEqBit`/`RunCopyTail`).
      **← recommended next; structural splitting has hit diminishing returns.**
