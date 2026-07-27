import Complexity.NP.SAT.CookLevin.Reductions.S1PreludeEmit
import Complexity.NP.SAT.CookLevin.Reductions.S1Program

/-! # S1 probe — stage C's prelude family, the `Cmd`

`Reductions/S1PreludeEmit.lean` builds and proves `cPrelude`. What a proof
cannot say is what the emitter actually *does* on a machine, so this probe runs
it end to end and prints the numbers the still-open cost ladder needs.

§1 the re-coordinatised model (`preludeSeg'`, Finding G) agrees with the target
   on a spread of `(σ, states, q0)`, including the degenerate `σ = 0` corner;
§2 **the emitter runs**: `cPrelude` on a minimal state produces exactly
   `encNats (preludeBlocks σ states (min start states))` — the `cPrelude_run`
   contract, checked numerically rather than assumed;
§3 the frame: registers outside `PDirty ∪ {EOUT_C}` are untouched, and every
   register of `PDirty` is inside `S1Program.CDirty`;
§4 **what is left for `stepBlocks`**. `stepBlocks` emits *before* the prelude
   and `pPre` re-establishes every constant the kind nest reads, so the whole
   30-register licence is available to it — this prints that set;
§5 the cost of the real `cPrelude` next to `S1Map.s1Bound`.

⚠ The emitter appends cell by cell, so `#eval`-ing it is quadratic in the
output length: only `σ ≤ 1` is run end to end (`σ = 2` already emits `11598`
numbers, i.e. `~10^5` tape cells; the whole probe takes ~6 min as it is). §1
covers the larger shapes at the model level.

Measured 2026-07-27-c: §2/§3 all green, and `cPrelude.cost` is
`(2.8e5, 4.3e5, 9.5e6, 1.2e7)` on the four instances against an `S1Map.s1Bound`
of `1.0e13` at `n = 7` — seven orders of magnitude of head-room on the family
that dominates the whole program.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1PreludeEmitProbe.lean`
-/

open Complexity.Lang Complexity.Simulators S1Program S1Prelude

/-! ## §1 — the re-coordinatised model equals the target -/

def eTriples : List (Nat × Nat × Nat) :=
  [(0, 0, 0), (0, 3, 0), (1, 1, 0), (2, 2, 0), (2, 2, 1), (3, 3, 2), (4, 2, 1), (2, 5, 3)]

#eval eTriples.map (fun p =>
  decide (S1Cards.preludeBlocks p.1 p.2.1 p.2.2 = preludeSeg' p.1 p.2.1 p.2.2))
  -- expect all true

/-! ⚠ `preludeSeg` (the pinned 2026-07-27-b shape) and `preludeSeg'` (with
`add` folded into the base — Finding G) must agree: the fold is a change of
register coordinates, not of the emitted stream. -/
#eval eTriples.map (fun p =>
  decide (preludeSeg p.1 p.2.1 p.2.2 = preludeSeg' p.1 p.2.1 p.2.2))
  -- expect all true

#eval eTriples.map (fun p => (S1Cards.preludeBlocks p.1 p.2.1 p.2.2).length)

/-! ## §2 — the emitter, end to end

`cPrelude` reads exactly three registers of the parse frame, so the probe can
feed it a minimal state instead of running the whole program. -/

/-! ⚠ `State.set` **must** be named explicitly below: `State` is an `abbrev`
for `List (List Nat)`, so `s.set` resolves to `List.set`, which is a silent
no-op on a short list. The first draft of this probe did exactly that and
reported a uniform "σ = states = 0" run for every instance — the emitter was
fine, the harness was not. -/

/-- The instances small enough to run interpreted. `(1,2,5)` has an
out-of-range `start`, so the `minReg` clamp is exercised. -/
def eSmall : List (Nat × Nat × Nat) := [(0, 0, 0), (0, 3, 0), (1, 1, 0), (1, 2, 5)]

def mkS (σ st start : Nat) : State :=
  State.set (State.set (State.set ([] : State)
    S1Parse.PSIG (List.replicate σ 1))
    S1Parse.PSTATES (List.replicate st 1))
    S1Parse.PSTART (List.replicate start 1)

#eval eSmall.map (fun p =>
  ((State.get (mkS p.1 p.2.1 p.2.2) S1Parse.PSIG).length,
   (State.get (mkS p.1 p.2.1 p.2.2) S1Parse.PSTATES).length,
   (State.get (mkS p.1 p.2.1 p.2.2) S1Parse.PSTART).length))

#eval eSmall.map (fun p =>
  decide (State.get (cPrelude.eval (mkS p.1 p.2.1 p.2.2)) S1Emit.EOUT_C
    = FlatTCCFree.encNats
        (S1Cards.preludeBlocks p.1 p.2.1 (min p.2.2 p.2.1))))
  -- expect all true

/-! ⚠ Emitted cell count vs. block count — the emitter never uses `concat`, so
these are the numbers the cost ladder charges against. -/
#eval eSmall.map (fun p =>
  ((S1Cards.preludeBlocks p.1 p.2.1 (min p.2.2 p.2.1)).length,
   (State.get (cPrelude.eval (mkS p.1 p.2.1 p.2.2)) S1Emit.EOUT_C).length))

/-! ## §3 — the frame -/

/-! ⚠ Nothing outside `PDirty ∪ {EOUT_C}` moves. Checked against every register
below `S1Program.s1RegBound`, including the parse outputs the later stages
still need. -/
#eval eSmall.map (fun p =>
  let s := mkS p.1 p.2.1 p.2.2
  decide ((List.range 48).all (fun r =>
    decide (r ∈ PDirty) || decide (r = S1Emit.EOUT_C)
      || decide (State.get (cPrelude.eval s) r = State.get s r))))
  -- expect all true

/-! ⚠ …and every register `PDirty` claims is inside stage C's licence, so
`stageC_run`'s frame clause stays meetable (`PDirty_cdirty` is the proof; this
is the numeric cross-check). -/
#eval decide (PDirty.all (fun r => decide (CDirty r)))   -- expect true

#eval (PDirty.length, PDirty.eraseDups.length)

/-! ## §4 — the pool `stepBlocks` inherits

⚠ **The 2026-07-27-b reading of "the licence is exactly full" is too
pessimistic.** `cardBlocks` order is `cFive ;; stepBlocks ;; prelude`, and the
prelude's own preamble `pPre` rebuilds every constant its nest reads (`ESG`,
`PBV`, `PZ`, `PB5`, `PHB`) from the parse frame. So `stepBlocks` runs *before*
anything the prelude needs exists and may use the **whole** 30-register licence
— nothing has to be preserved across it except registers outside `CDirty`
(the input layout `1`–`5`, the parse outputs, `EOUT_S`/`EOUT_I`). The list
below is what it can claim. -/
#eval ((List.range 48).filter (fun r => decide (CDirty r)))

/-! What `stepBlocks` must *not* touch (it is read by the prelude's preamble or
by stage M-yes). -/
#eval ((List.range 48).filter (fun r => ¬ decide (CDirty r)))

/-! ## §5 — cost

The real `cPrelude.cost` on the instances small enough to run, next to
`S1Map.s1Bound` at a comparable input size. The ladder is a slack argument
(finding F); this is the first measurement of the *dominant* family. -/
#eval eSmall.map (fun p => cPrelude.cost (mkS p.1 p.2.1 p.2.2))

#eval [7, 22, 30, 35].map (fun n => (n, S1Map.s1Bound n))
