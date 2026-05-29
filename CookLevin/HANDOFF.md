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
  obligation `Compile_run_physical` / `Compile_sound` (Risk **C2**):
  `LangEncodable`, `PolyTimeComputableLang'`, `inNPLang`/`red_inNPLang`,
  `inNPLang_to_inNP`, `bitTestTM`, `map_fst`/`swap`/`map_snd`, the `forBnd`
  toolkit, `⪯p'` + `reducesPolyMO'_of_lang`, generic `LangEncodable (List α)`.

## This session's finding (recorded in ROADMAP)

The **C2 compiler is the highest-risk completion item and is under-built**: the
proven gadget run-lemmas give *behavioural* correctness but leave the **step
count existential**, so the polynomial step-bound accounting `Compile.overhead`
needs is largely unbuilt; 10 of 12 `compileOp`s are `compiledCmd_default` stubs.

New, sorry-free, axiom-clean: **`compileOp_appendOne_behavioural`**
(`Lang/Compile.lean`) — the first end-to-end proof that the
`encodeTape`/`decodeTape` contract composes with the gadget library
(`appendAt_run`) for a real op. It isolates the residual per-op gap to **purely
the step bound**.

## Recommended next step

Per ROADMAP plan step 1 (highest risk): **upgrade
`compileOp_appendOne_behavioural` to the budgeted `compileOp_sound` shape** by
adding a step count to `appendAt_run` and bounding it by
`Compile.overhead (size + 1)`. That establishes the step-bound pattern; then
concretise the 10 stub ops and assemble `Compile_sound`. (Alternatively, the
cheaper-but-lower-risk `map`-over-lists witness — ROADMAP step 2,
`parked/MapNatList_WIP.lean` — keeps the S3 migration moving while C2 is built.)

## Conventions

- Commit per logical step with a **green build**; record gaps in commit messages.
- New results must be `#print axioms`-clean (only `propext` / `Quot.sound` /
  `Classical.choice`). **No new axioms.** Decompose `sorry`s; don't elaborate.
- Axiom check (lean-lsp's LSP has no `lake` on PATH):
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean` with
  `#print axioms <name>`.
- See ROADMAP "Hard-won gotchas" (the `omega`/`Var` trap, nested `set` blowup,
  `State.get` literal mis-resolution).
