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

## This session's findings (recorded in ROADMAP)

1. **`compileOp_sound` is FALSE as stated** — its budget
   `Compile.overhead (State.size s + cost)` ignores the register count, but
   `appendAtTM`'s step count grows with the tape length
   `(encodeTape s).length = State.size s + s.length + 1`. Counterexample
   (evaluated): `s = List.replicate 6 []` has `State.size 0`, budget `4`, but
   `opAppendOne 0` first halts at step 10. **Fix the budget to tape length**
   (`Compile.overhead ((encodeTape s).length + cost)`) and thread the register
   count (≤ `regBound`) in the `Compile_sound` assembly.
2. The gadget step counts are recoverable (the lower-level lemmas
   `scanInsert_run`/`insertCarryTM_run` are explicit; only `appendAt_run`
   existentializes).

New, sorry-free, axiom-clean (`Lang/Compile.lean`):
- **`compileOp_appendOne_behavioural`** — behavioural soundness of `appendOne`
  end-to-end (general `dst`): the `encodeTape`/`decodeTape` seam composes with
  the gadget library.
- **`compileOp_appendOne_zero_sound`** — the **corrected tape-length budget is
  achievable** (`dst = 0`, from `scanInsert_run`'s explicit step count).

## Recommended next step

Per ROADMAP plan step 1: **(a) fix the per-op budget definition to tape length**
and restate `Compile_sound` to carry `regBound`; **(b) upgrade
`compileOp_appendOne_behavioural` to general-`dst` budgeted soundness** by
re-proving `appendAt_run` with an explicit step count (lower-level lemmas
already have them). Then concretise the 10 stub ops and assemble `Compile_sound`.
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
  `State.get` literal mis-resolution).
