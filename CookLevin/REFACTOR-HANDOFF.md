# Handoff — refactoring the compiler (`Compile.lean`)

This is the **working plan for the compiler refactor**, run as its own
multi-session stream (parallel to the compiler *implementation* stream in
[`HANDOFF.md`](HANDOFF.md)). Same workflow: build green between commits, keep this
doc compact and forward-looking, hand off to the next refactoring agent.

**Goal.** `Compile.lean` has grown to **26.5K lines / 1.5 MB in a single Lean
module**. Lean compiles a module as one unit, so this file is (a) the build's
long pole — `lake build` spends the bulk of its wall-clock compiling this one
file, with zero intra-file parallelism — and (b) unmaintainable: any one-line
edit recompiles all 26K lines *and* everything downstream (`PolyTime.lean` + the
whole proof). The bottom-up op work edits this file constantly. **Split it into a
DAG of ~1–3K-line modules** so compilation parallelises and edits rebuild only
the touched module + its dependents. Delete the dead code along the way.

**Coordinate with `HANDOFF.md`.** Both streams edit `Compile.lean`, so they will
conflict. **Recommendation: land the refactor's Phase 0 + Phase 1 before the next
op (`concat`) is implemented**, so new ops land in clean modules. If an op session
must run first, it should rebase onto the latest refactor branch.

---

## The key finding that makes the split tractable

The HANDOFF previously recorded that a *clean module split was impossible* because
"the eqBit run lemmas depend on copy/tail run lemmas that sit after `compileOp`."
That is true **for an in-file move** but **false for a multi-file split**, and this
is the crux of the whole refactor:

- `compileOp` (the def, L4168) and `compileCmd` (L5055) reference the op machine
  **defs** (which already sit *above* them).
- The op **run lemmas** (`opCopy_run` L14276, `opTail_run` L15428, `opEqBitNG_run`
  L19653, …) sit *after* `compileOp` in the file **but do not reference `compileOp`
  or `compileCmd`** (verified: the only refs to those names between L4170 and the
  per-op contract are the `compileCmd` def itself + comments). They were appended
  chronologically, not for any dependency reason.

So the real dependency graph is a clean DAG; the file is just **topologically
mis-sorted**. In separate modules, a gadget's def + shape lemmas + run lemmas all
live together in one module that depends only on the combinators + lower
primitives; `compileOp` imports those modules; the per-op *soundness* contract
imports `compileOp` + the gadget modules. No cycle. (This also retroactively
explains why the eqBit in-file relocation in BU-C2-15 was so painful — a module
split would have avoided it entirely.)

---

## Review: current `Compile.lean` structure (line ranges, 2026-06-25)

1035 declarations. Logical blocks (current line order; **note the interleaving** —
e.g. op run lemmas are far below their defs, and the per-op *contract* L19926 sits
in the middle of the eqBit run-lemma block):

| Lines | Block | Target module |
|---|---|---|
| 80–644 | `CompiledCmd` record, `joinTwoHalts`, `rewindBracket`, combinators | `Compile/Core` |
| 644–1873 | `copy`/`tail` cursor-copy machine **defs** + shapes | `Compile/CopyTail` |
| 1874–2467 | `nonEmpty`, `head` machine defs | `Compile/NonEmptyHead` |
| 2468–4167 | `eqBit` (`compareRegsNoGrowM` tree) machine **defs** + shapes | `Compile/EqBit` |
| 4168–4273 | **`compileOp`** dispatch | `Compile/Op` |
| 4274–4699 | `compileIfBit` + `compileTestBit` | `Compile/Op` |
| 4700–5037 | `forBnd` loop machines | `Compile/Op` |
| 5038–5079 | `compileCmd`, `Compile`, `Compile.exit` | `Compile/Cmd` |
| 5081–5434 | `encodeTape`/`decodeTape` + round-trip lemmas | `Compile/Core` |
| 5435–5757 | cost notes + encoding-seam helpers | `Compile/Core` |
| 5757–6113 | append-op soundness | `Compile/OpSound` |
| 6114–6378 | `compileSeq_sound_physical_residue` (composition) | `Compile/OpSound` |
| 6379–8087 | `clear` run lemmas | `Compile/ClearRun` (or `CopyTail`) |
| 8088–9801 | move-one-bit transfer gadget | `Compile/Move` |
| 9802–12442 | `moveRegion2TM` dual-target move | `Compile/Move` |
| 12443–14764 | cursor-copy **run** lemmas (`copy`) | `Compile/CopyTail` |
| 14765–15887 | `tail` op **run** lemmas | `Compile/CopyTail` |
| 15888–19925 | `eqBit` consume-loop body machines + **run** lemmas | `Compile/EqBit` |
| 19926–20269 | **`compileOp_sound_physical_residue`** (per-op contract; 4 stub sorries L20142–45) | `Compile/OpSound` |
| 20270–20486 | residue-composition validation + `bitTestTM` (C6) | `Compile/Assembly` |
| 20487–21118 | C2 assembly toolkit + `run_physical_residue_gen` + ifBit/forBnd contracts | `Compile/Assembly` |
| 21119–23116 | `forBnd` fold invariants + loop run | `Compile/Assembly` |
| 23117–24078 | the WALL: `padRegsTM`, `paddedBitDecider`, `paddedCompute` | `Compile/Decider` |
| **24079–26493** | **DEAD** grow/shrink/`compareRegsTM` scaffolding (101 decls) + orphan comments | **delete** |

### Dead code (verified, 2026-06-25)

The grow/shrink/`compareRegsTM` scaffolding from the *superseded* eqBit Resolution-A
(replaced by the no-grow Resolution B that is now live above `compileOp`): the whole
tail **L24079→EOF (L26493), 101 declarations, ~2.4K lines**. Verified deletable: all
of `growEmptyTM`/`growTwoEmptyM`/`growScanInsM`/`growInsertM`/`shrinkEmptyTM`/
`shrinkTwoEmptyM`/`shrinkComputeM`/`compareCleanupM`/`compareRegsPrefixM`/
`compareRegsTM`/`compareBranchM` (+ the dead `copyEmptyTM` variant) are referenced
**only within that block and in comments** — zero live-code references (the live
no-grow path uses `copyEmptyRawTM`/`cmpNGPrefixM`/`clearAppendM`, all defined above
`compileOp`). The trailing L26445–26493 are orphaned section-comments whose defs were
relocated in BU-C2-15. Deleting to EOF leaves the file ending at `paddedCompute_run`,
still inside `namespace Complexity.Lang` (the only open namespace; `namespace Compile`
is opened+closed at L210/575, everything else is fully-qualified `Compile.X`).

---

## Target module DAG

Files live under `CookLevin/Complexity/Lang/Compile/` (Lean allows both a
`Compile.lean` facade *and* a `Compile/` subdir). Each module re-opens
`namespace Complexity.Lang`, imports its deps, and uses fully-qualified `Compile.X`
names (matching today's style — no `namespace Compile` block needed except for the
combinator section that currently uses one).

```
(existing primitives: Syntax Semantics Frame Navigate ScanPast ScanLeft
                      ShiftTape AppendGadget ClearGadget; + TMPrimitives, TapeMono)
        │
   Compile/Core      CompiledCmd, joinTwoHalts, rewindBracket, combinators,
        │            encodeTape/decodeTape + round-trip, cost/seam helpers
        ├────────────────────────┬───────────────────────┐
   Compile/Move            Compile/NonEmptyHead      (Core-only gadgets)
        │                        │
   Compile/CopyTail  ←───────────┘   (copy/tail defs+shapes+runs; clear runs)
        │
   Compile/EqBit     (compareRegsNoGrowM tree + opEqBitNG; imports CopyTail —
        │             eqBit run lemmas reuse copy/tail run lemmas)
   Compile/Op        compileOp + compileIfBit/testBit + forBnd machines
        │            (imports CopyTail, NonEmptyHead, EqBit, Move)
   Compile/Cmd       compileCmd, Compile, exit
        │
   Compile/OpSound   append/clear soundness, compileSeq composition,
        │            compileOp_sound_physical_residue  ← the 4 stub ops live here
   Compile/Assembly  run_physical_residue_gen, ifBit/forBnd contracts,
        │            forBnd loop run, bitTestTM, assembly toolkit
   Compile/Decider   padRegsTM (WALL), paddedBitDecider, paddedCompute
        │
   Compile.lean      thin facade: `import`s all of the above (PolyTime imports this)
```

Each module targets ~1–3K lines. Biggest single module will be `Compile/EqBit`
(the consume-loop tree is large) and `Compile/Assembly`.

---

## The plan (sequenced, build-green between every step)

**Phase 0 — delete dead code.** Remove L24079→EOF. ~2.4K lines gone, ~9% smaller,
zero risk. One `lake build` to confirm green + `#print axioms` on
`Compile.compileOp_sound_physical_residue` and `Compile.paddedBitDecider_run`
unchanged. **← DO THIS FIRST. (Status: see bottom.)**

**Phase 1 — carve off the leaf gadget modules**, one per build, in dependency
order. For each: create `Compile/<Name>.lean` with the imports + namespace header,
**move both** the def/shape block *and* the run-lemma block (they're far apart in
the current file — grab both ranges), `import Complexity.Lang.Compile.<Name>` into
`Compile.lean` at the top, delete the moved ranges from `Compile.lean`, build the
new module alone (`lake build Complexity.Lang.Compile.<Name>`), then the facade.
Order: `Core` → `Move` → `NonEmptyHead` → `CopyTail` → `EqBit`.

**Phase 2 — `Op` and `Cmd`.** Move `compileOp`/`compileIfBit`/`compileTestBit`/
`forBnd` machines into `Compile/Op`, then `compileCmd`/`Compile`/`exit` into
`Compile/Cmd`.

**Phase 3 — soundness + assembly + decider.** Move `compileOp_sound_physical_residue`
(+ append/clear/seq soundness) into `Compile/OpSound`; `run_physical_residue_gen` +
the loop/branch contracts + assembly toolkit into `Compile/Assembly`; the WALL into
`Compile/Decider`. `Compile.lean` becomes a pure facade (imports only).

**Phase 4 (optional, bonus) — tame slow proofs.** With modules isolated, profile
the slowest (`lean --profile`, or `mcp__lean-lsp__lean_profile_proof`). Known
hot spots from the implementation HANDOFF: `nlinarith`/`omega` on quadratic-times-
cost budgets (`eqBit_budget_arith`, `forBndBudget_arith`), big `simp` calls. Replace
with explicit `Nat.*` term-mode steps where they dominate. Lower priority than the
split itself; the parallelism + incremental win is the main build speedup.

---

## Gotchas for the refactoring agent

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (lake is **not** on
  PATH; most MCP/LSP features can't find it). **First build is slow** — kick it off
  as a background job early. Per-module: `lake build Complexity.Lang.Compile.<Name>`.
- **Verify each move with a real build** — the deps were derived by static analysis,
  but Lean will catch any missed shape lemma. Expect ~2–3 build iterations per
  module (a missing helper surfaces as an unknown-identifier error → move it too).
  Method: compute the qualified-`Compile.X` reference closure of the block you're
  moving; pull every referenced decl not already in an imported module.
- **Move defs and their run lemmas together** — they're in separate file regions
  today (see the table). A `theorem` must move whole; don't split mid-proof.
- **Namespace:** open `namespace Complexity.Lang` at the top of each new module.
  The combinator block (`Compile/Core`) is the only part that currently uses an
  explicit `namespace Compile … end Compile` (L210–575) — preserve it there.
- **`set_option autoImplicit false` / `relaxedAutoImplicit false`** are set
  package-wide in `lakefile.lean`, so new modules inherit them — don't re-add.
- **`⨾` / `composeFlatTM` / `branchComposeFlatTM` / `loopTM`** come from
  `Complexity.Complexity.TMPrimitives`; make sure each gadget module imports it.
- **Axiom-clean check** after each phase: `#print axioms Compile.<key lemma>` via a
  scratch file (`env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean`) —
  must stay `[propext, Classical.choice, Quot.sound]` (no new `sorryAx` beyond the
  4 known stub ops in `compileOp_sound_physical_residue`).
- **Don't touch `PolyTime.lean`'s import** beyond pointing it at the facade — it
  imports `Complexity.Lang.Compile` today; keep that working.
- Commit per module (green), with the module name in the message. Easy to bisect.

---

## Status

- [x] **Phase 0 — dead-code deletion (L24079→EOF) — DONE (2026-06-25).** Removed
      2,415 lines (101 dead decls + orphan comments); `Compile.lean` 26,493 → 24,078
      lines. `lake build` green (3358 jobs); `#print axioms
      Compile.paddedBitDecider_run` unchanged (`[propext, sorryAx, Classical.choice,
      Quot.sound]` — `sorryAx` from the 4 stub ops only, as before). ⚠ The
      now-obsolete `probes/{GrowEmpty,ShrinkEmpty,CompareRegs*,CompareBody,EqBit*}Probe.lean`
      still reference deleted symbols — they are **not in the build** (`lean_lib`
      roots are `Basic`/`Complexity`), so harmless, but stale; delete them in a
      cleanup pass. Two stale comment mentions of `compareRegsTM` remain in
      `Compile.lean` (L18611, L19915) — harmless.
- [ ] Phase 1 — leaf gadget modules.
- [ ] Phase 2 — `Op`, `Cmd`.
- [ ] Phase 3 — soundness/assembly/decider; facade.
- [ ] Phase 4 — proof-perf (optional).
</content>
