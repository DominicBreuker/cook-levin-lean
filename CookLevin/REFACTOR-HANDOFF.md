# Handoff — refactoring the compiler (`Compile.lean`)

Working plan for the **compiler refactor**, run as its own multi-session stream
(parallel to the compiler *implementation* stream in [`HANDOFF.md`](HANDOFF.md)).
Same workflow: build green between commits, keep this doc compact and
forward-looking, hand off to the next refactoring agent.

**Goal (achieved for the structural split).** `Compile.lean` had grown to a
single **26.5K-line / 1.5 MB Lean module** — the build's long pole (no intra-file
parallelism) and unmaintainable (any one-line edit recompiled all 26K lines + the
whole downstream proof). It is now split into a **DAG of `Compile/*` modules**, so
compilation parallelises and edits rebuild only the touched module + its
dependents.

**Coordinate with `HANDOFF.md`.** Both streams edit the compiler. The split is now
done, so the op stream should land its next op (`concat`, the stub-op threading,
etc.) **in the relevant submodule** — the per-op contract + stub ops live in
`Compile/OpSound`; the op machines in `Compile/OpMachines`; run lemmas in
`Compile/RunLemmas`. Edits there no longer rebuild the rest of the compiler.

---

## Current module structure (build green, 3366 jobs, 2026-06-25)

`Compile.lean` is now a **39-line pure facade** (imports only; `PolyTime.lean`
still `import`s `Complexity.Lang.Compile` and gets everything). The DAG, under
`CookLevin/Complexity/Lang/Compile/`:

```
(primitives: Syntax Semantics Frame Navigate ScanPast ScanLeft ShiftTape
             AppendGadget ClearGadget; TMPrimitives, TapeMono)
      │
  Core (524)          CompiledCmd, joinTwoHalts, rewindBracket, combinators
      ├───────────────┐
  Encoding (708)      encodeTape/decodeTape, BitState, ValidResidue, structure lemmas
      │               │   (sibling of Core; primitives only)
  OpMachines (3621)   every per-Op TM machine *def* + shape lemmas (the
      │               whole "before compileOp" region)
  Cmd (950)           compileOp/Seq/IfBit/TestBit + forBnd machines + compileCmd
      │
  RunLemmas (14150)   ★ every per-op *run/behaviour* lemma + residue toolkit
      │               (append soundness, clear, move×2, copy, tail, eqBit, testBit)
  OpSound (558)       compileOp_sound_physical_residue (8 ops ✓, 4 stub sorries)
      │               + compileSeq physical/residue soundness
  Assembly (2740)     C6 bitTestTM, assembly toolkit (physStepBudget, NoConsLen,
      │               eval_preserves_BitState), compileIfBit/compileForBnd soundness
      │               + forBnd loop run stack, run_physical_residue_gen,
      │               Compile_run_physical_residue, bitDeciderTM/bitDecider_run
  Decider (991)       the WALL: padRegsTM / paddedBitDecider / paddedCompute
      │
  Compile.lean (39)   facade: imports all of the above
```

Axiom invariant (unchanged throughout): `#print axioms
compileOp_sound_physical_residue` / `paddedBitDecider_run` / `paddedCompute_run`
= `[propext, sorryAx, Classical.choice, Quot.sound]` (the `sorryAx` is the 4 stub
ops in the contract — `concat`/`takeAt`/`dropAt`/`consLen`, none on the live
`sat_NP` path).

---

## What's left (recommended next steps, in priority order)

### 1. Split `RunLemmas` (14,150 lines) — the only remaining build pole. ★ highest value

Everything else is ≤ 3.6K. `RunLemmas` is now the single longest compile. Its run
lemmas are independent per gadget and split along clean section boundaries (line
ranges in `Compile/RunLemmas.lean`, 2026-06-25):

| Lines | Block | Suggested module |
|---|---|---|
| 36–392 | `appendOne`/`appendZero` per-op soundness | `RunClear` (or shared base) |
| 393–432 | `compileSeq_compose_physical` (uses `compileSeq`) | `RunClear` |
| 433–657 | residue toolkit (`ValidResidue`/`TapeOK` helpers, `set_*`/`BitState_*`) — **shared** | base of `RunClear` |
| 658–2366 | `clear` run stack + `clearRegionTM_run` | `RunClear` |
| 2367–4080 | move-one-bit transfer gadget + `navTestReg` reading | `RunMove` |
| 4081–6721 | dual-target `moveRegion2TM` | `RunMove` |
| 6722–9043 | cursor-copy (`copy`) run stack | `RunCopyTail` |
| 9044–10166 | `tail` run stack | `RunCopyTail` |
| 10167–EOF | `eqBit` no-grow consume-loop stack (ends `opEqBitNG_run`) | `RunEqBit` |

Dependency order **Clear → Move → CopyTail → EqBit** (eqBit reuses copy/tail
machinery; copy/tail use the cursor/`navTestReg` helpers; the residue toolkit is
shared by all). Mechanics are the same as the splits already done (see method
below). This buys real parallelism: a `copy` edit no longer rebuilds the `eqBit`
stack, etc. Estimate 4 modules, ~1 build each.

### 2. Phase 4 (optional) — tame slow proofs

With modules isolated, profile the slowest (`lean --profile`, or
`mcp__lean-lsp__lean_profile_proof`). Known hot spots: `nlinarith`/`omega` on
quadratic budgets (`eqBit_budget_arith`, `forBndBudget_arith`), big `simp`.
Replace with explicit `Nat.*` term steps where they dominate. Lower priority than
the `RunLemmas` split.

### 3. Cleanup (cheap, do alongside)

- Stale `probes/*Probe.lean` (`GrowEmpty`/`ShrinkEmpty`/`CompareRegs*`/`EqBit*`…)
  reference symbols deleted in Phase 0; **not in the build** (`lean_lib` roots are
  `Basic`/`Complexity`), so harmless but dead — delete them.
- `push_neg` deprecation warnings in `Compile/Cmd.lean` (L126/462/469): prefer
  `push Not`.
- Minimal-imports prune: each new module imports the full primitive list; could be
  trimmed to actual deps (cosmetic).

---

## Method (used for every split this stream — reuse it)

1. **Pick a cut at a section boundary** (`/-! ### …`), not mid-decl. A `theorem`
   moves whole.
2. **Dependency scan** (static, before building): the block must only reference
   decls in already-imported modules + itself. Compute
   `{Compile|Op|Cmd|State}.X` referenced − defined-in-block − (imported modules) =
   ∅ (modulo comments — most stray refs are in doc comments; spot-check with
   `sed -n`). Also check **unqualified** lemma names. (`comm -12` of sorted
   ref/def lists is the quick check.)
3. **Scan for `private` decls used outside the block** → strip `private` (widening
   visibility never breaks exports). E.g. `haltingStateReached_of_halt` had to go
   public when `RunLemmas` was carved out.
4. Create `Compile/<Name>.lean`: the standard import header (primitives + the
   prior modules) + `namespace Complexity.Lang` + `open TMPrimitives` +
   `open scoped BigOperators`, then the moved block. Import it into the next
   module / facade; delete the moved range from the source.
5. **Build is the oracle** (`export PATH="$HOME/.elan/bin:$PATH"; lake build` —
   lake is **not** on PATH, which is also why most MCP/LSP features fail). First
   build is slow; kick it off in the background early. Per-module:
   `lake build Complexity.Lang.Compile.<Name>`.
6. **Axiom-clean check** after each phase via a scratch file
   (`env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean`,
   `#print axioms …`) — must stay the 4-axiom set above (no *new* `sorryAx`).
7. Commit per module (green), module name in the message.

### Gotchas

- `set_option autoImplicit false` / `relaxedAutoImplicit false` are package-wide
  (`lakefile.lean`); new modules inherit them — don't re-add.
- `⨾` / `composeFlatTM` / `branchComposeFlatTM` / `loopTM` come from
  `Complexity.Complexity.TMPrimitives` — every gadget module needs it imported.
- **Don't double-background builds.** Use the harness's `run_in_background`
  *or* a shell `&`, never both (it detaches the wrapper and you lose the exit
  code; a stray `pkill` then shows up as exit 137/144, not a real error).
- Don't touch `PolyTime.lean`'s import — it imports `Complexity.Lang.Compile`
  (the facade); keep that working.

---

## Status

- [x] **Phase 0 — dead-code deletion** (L24079→EOF, 2,415 lines / 101 dead decls).
- [x] **Phase 1 — leaf modules:** `Core`, `Encoding`, `OpMachines`.
- [x] **Phase 2 — compiler defs:** `Cmd` (compileOp/Seq/IfBit/TestBit + forBnd
      machines + compileCmd).
- [x] **Phase 3 — run lemmas + soundness + assembly + decider + facade:**
      `RunLemmas`, `OpSound`, `Assembly`, `Decider`; `Compile.lean` reduced to a
      39-line facade. Monolith 18,407 → 39 lines this session (whole-stream:
      26,493 → 39). Build green (3366 jobs), axioms unchanged.
- [ ] **Phase 1-refinement — split `RunLemmas`** into `RunClear`/`RunMove`/
      `RunCopyTail`/`RunEqBit` (see "What's left #1"). **← recommended next.**
- [ ] **Phase 4 (optional)** — proof-perf.
