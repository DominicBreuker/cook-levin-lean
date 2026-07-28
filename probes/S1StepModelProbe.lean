import Complexity.NP.SAT.CookLevin.Reductions.S1StepModel

/-! # S1 probe — stage C's `stepBlocks` family, the emitter-shaped model

`Reductions/S1StepModel.lean` re-states `S1Cards.stepBlocks` in the shape the
emitter will implement (three findings M/N/O/P, each a theorem). This probe is
the numeric cross-check the proofs cannot express: it sweeps the whole
parameter cube, *including* the corners a "realistic" instance never reaches.

§1 the four segment reformulations agree with their targets on every
   `(σ, states, q, q', mTag, mVal, wTag, wVal, mv)` in a spread that covers
   **σ = 0** (both bands of the `x`/`y` splits empty), `mv ∈ {0,1,2}` (the
   `stepInBlocks`-is-empty corner), `mTag/wTag ∈ {0,1}` (the `none`/`some`
   read/write codes) and out-of-range `mVal`/`wVal` (the `min · σ` clamps);
§2 the three per-entry constants (finding N) really are only three — the
   number of distinct symbol values a whole entry contributes;
§3 block counts per family, so the entry loop's cost is on the record before
   the ladder is attempted.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1StepModelProbe.lean`
-/

open Complexity.Lang Complexity.Simulators S1Cards S1Step

/-- `(σ, states, q, q', mTag, mVal, wTag, wVal, mv)`. -/
abbrev Nine := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

def sweep : List Nine :=
  ((([0, 1, 2, 3] : List Nat).flatMap (fun σ =>
    ([0, 2] : List Nat).flatMap (fun st =>
      ([0, 1, 2] : List Nat).flatMap (fun mv =>
        ([0, 1] : List Nat).flatMap (fun mT =>
          ([0, 1] : List Nat).flatMap (fun wT =>
            ([0, 5] : List Nat).map (fun v =>
              (σ, st, min 1 st, st, mT, v, wT, v, mv))))))))
  ++ [(0, 0, 0, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 1, 0, 1, 0, 1),
      (1, 1, 1, 0, 1, 1, 1, 0, 2), (2, 3, 3, 1, 0, 9, 1, 9, 0)])

#eval sweep.length

/-! ## §1 — each reformulation is faithful -/

#eval decide (sweep.all (fun p =>
  decide (stepCenterBlocks p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2
    = stepCenterSeg p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)))
  -- expect true

#eval decide (sweep.all (fun p =>
  decide (stepLeftBlocks p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2
    = stepLeftSeg p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)))
  -- expect true

#eval decide (sweep.all (fun p =>
  decide (stepRightBlocks p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2
    = stepRightSeg p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)))
  -- expect true

#eval decide (sweep.all (fun p =>
  decide (stepBlocks p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2
    = stepSeg p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)))
  -- expect true

/-! ## §2 — finding N: an entry contributes exactly three symbol constants

⚠ `rOf` and both `wOf` variants, and nothing else: everything a card cell holds
is one of these three, a loop counter, `bv`, or `hv` of one of them. If this
ever printed more than `3`, the per-entry preamble would need another register.
-/
#eval sweep.map (fun p =>
  ([rOf p.1 p.2.2.2.2.1 p.2.2.2.2.2.1,
    wOf p.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 false,
    wOf p.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 true]
    : List Nat).eraseDups.length) |>.eraseDups
  -- expect a sublist of [1, 2, 3] — never more than 3

/-! ⚠ …and every one of them is `≤ σ`, i.e. a legal Γ symbol, on every corner
of the sweep including out-of-range `mVal`/`wVal` (the `min · σ` clamp). -/
#eval decide (sweep.all (fun p =>
  decide (rOf p.1 p.2.2.2.2.1 p.2.2.2.2.2.1 ≤ p.1)
    && decide (wOf p.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1
        p.2.2.2.2.2.2.2.1 false ≤ p.1)
    && decide (wOf p.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1
        p.2.2.2.2.2.2.2.1 true ≤ p.1)))
  -- expect true

/-! ## §3 — block counts per sub-family

`(center, left, right, in)` at `σ = 0,1,2,3` with `mv = 0` (the branch that
emits the most: `stepLeftBlocks` doubles and `stepInBlocks` is non-empty). -/
#eval ([0, 1, 2, 3] : List Nat).map (fun σ =>
  (σ, (stepCenterBlocks σ 2 1 2 1 0 1 0 0).length,
      (stepLeftBlocks σ 1 2 1 0 1 0 0).length,
      (stepRightBlocks σ 2 1 2 1 0 1 0 0).length,
      (stepInBlocks σ 2 2 0).length))
