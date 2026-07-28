import Complexity.NP.SAT.CookLevin.Reductions.S1Program

/-! # S1 probe — stage C end to end, the whole program, and the cost ladder

`Reductions/S1StepLoop.lean` closed the `stepBlocks` family and
`Reductions/S1Program.lean`'s `stageC` is now a real `Cmd`, so for the **first
time in the project** `s1Program` can be `#eval`-ed end to end (a `sorry` inside
a `def` blocks `#eval` even down an untaken branch — that is why every earlier
probe had to inject stage C's output by hand).

§1 **stage C's output is exactly `encNats (cardBlocks M)`** — full equality, not
   the prefix check `probes/S1CardEmitProbe.lean` §1 could only do — plus its
   frame;
§2 **the whole program**: `s1Extract (s1Program.eval (headEncodeIn x))
   = s1Key (S1Map.s1Map x)`, on and off the guard;
§3 the entry loop's own claims: the seen register really ends up holding every
   key (prepended — FINDING U), and the emitted summand really is the
   `normTrans` dedup's cards;
§4 **the cost ladder's raw numbers** — `s1Program.cost (headEncodeIn x)` against
   `S1Map.s1Bound (encodable.size x)`. This is what the LAST open S1 obligation
   (`S1Witness.s1Program_cost_le`) has to be argued from, and it could not be
   measured before this session.

⚠ **Keep every instance tiny.** `#eval` of the emitter is quadratic in its own
output (it appends cell by cell), and `cardBlocks` is already `768` cells at the
*trivial* machine and `12120` at `sig = 2, states = 2` — interpreting the latter
is `~10^10` steps. Everything below stays at `sig ≤ 1, states ≤ 2`; the model-only
checks (`§0`) are cheap and may use anything.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1StepLoopProbe.lean`
-/

open Complexity.Lang Complexity.Simulators S1Program

/-! ## Test instances -/

def rE (q q' : Nat) (mv : TMMove) : FlatTMTransEntry :=
  { src_state := q, src_tape_vals := [none], dst_state := q',
    dst_write_vals := [none], move_dirs := [mv] }

/-- `sig = 0`, one state, one transition. -/
def rM0 : FlatTM :=
  { sig := 0, tapes := 1, states := 1, start := 0, halt := [false],
    trans := [rE 0 0 TMMove.Rmove] }

/-- Two entries with the **same key** (the dedup must drop the second) and one
whose source state **halts** (the filter must drop it). -/
def rMdup : FlatTM :=
  { sig := 0, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [rE 0 1 TMMove.Rmove, rE 0 0 TMMove.Lmove, rE 1 0 TMMove.Nmove] }

/-- `sig = 1` — the first instance with a non-degenerate alphabet. -/
def rM1 : FlatTM :=
  { sig := 1, tapes := 1, states := 1, start := 0, halt := [false],
    trans := [rE 0 0 TMMove.Nmove] }

/-- Off guard: `halt.length ≠ states`. -/
def rMbad : FlatTM := { rM0 with states := 4 }

def rIn (x : FlatTM × List Nat × Nat × Nat) : State := HeadLayout.headEncodeIn x

/-- The state stage C sees: after P + G, Σ and I. -/
def rPre (x : FlatTM × List Nat × Nat × Nat) : State :=
  S1Emit.stageInit.eval (S1Emit.stageSig.eval (S1Parse.stagePG.eval (rIn x)))

/-! ## §0 — model-only scale (cheap; the numbers that fix the probe's budget) -/

#eval [rM0, rMdup, rM1].map
  (fun M => ((S1Cards.cardBlocks M).length, (S1Cards.cardBlocks M).sum))

-- the dedup + halt filter, on the machine built to exercise both: expect (1, 3)
#eval ((normTrans rMdup).length, rMdup.trans.length)

/-! ## §1 — stage C's output is the whole card register, not a prefix -/

def cardOK (x : FlatTM × List Nat × Nat × Nat) : Bool :=
  State.get (stageC.eval (rPre x)) S1Emit.EOUT_C
    == FlatTCCFree.encNats (S1Cards.cardBlocks x.1)

#eval cardOK (rM0, [], 0, 0)                 -- expect true
#eval cardOK (rMdup, [], 1, 1)               -- expect true

/-- Stage C must leave every register the later stages read alone. -/
def cardFrameOK (x : FlatTM × List Nat × Nat × Nat) : Bool :=
  let s := rPre x
  let t := stageC.eval s
  ([1, 2, 3, 4, 5, S1Parse.PSIG, S1Parse.PSTATES, S1Parse.PHALT,
    S1Emit.EOUT_S, S1Emit.EOUT_I] : List Var).all
      (fun r => State.get t r == State.get s r)

#eval cardFrameOK (rM0, [], 0, 0)            -- expect true
#eval cardFrameOK (rMdup, [], 1, 1)          -- expect true

/-! ## §2 — the whole program, end to end (NEW: previously impossible) -/

def progOK (x : FlatTM × List Nat × Nat × Nat) : Bool :=
  s1Extract (s1Program.eval (rIn x)) == s1Key (S1Map.s1Map x)

#eval progOK (rM0, [], 0, 0)                 -- expect true
#eval progOK (rMdup, [], 1, 2)               -- expect true
#eval progOK (rMbad, [], 1, 1)               -- expect true (the off-guard branch)

/-! ## §3 — the entry loop's own claims -/

/-- The seen register after the family has run holds every key of `M.trans`,
newest first (FINDING U: the machine PREPENDS). -/
def seenOK (M : FlatTM) : Bool :=
  let t := S1Step.stepFam.eval (S1CardEmit.cFive.eval (rPre (M, [], 0, 0)))
  State.get t S1Step.SSEEN
    == HeadLayout.encSyms (S1Step.keyFlat (M.trans.reverse.map S1Cards.keyOf))

#eval seenOK rM0                             -- expect true
#eval seenOK rMdup                           -- expect true

/-- The family's emitted summand is exactly the `normTrans` dedup's cards. -/
def stepSummandOK (M : FlatTM) : Bool :=
  let s := S1CardEmit.cFive.eval (rPre (M, [], 0, 0))
  State.get (S1Step.stepFam.eval s) S1Emit.EOUT_C
    == State.get s S1Emit.EOUT_C
      ++ FlatTCCFree.encNats ((normTrans M).flatMap (S1Cards.entryBlocks M))

#eval stepSummandOK rM0                      -- expect true
#eval stepSummandOK rMdup                    -- expect true

/-! ## §4 — the cost ladder's raw numbers

`S1Witness.s1Program_cost_le` must show `s1Program.cost (headEncodeIn x) ≤
S1Map.s1Bound (encodable.size x)`. These are the two sides, measured, plus the
head-room ratio. -/

def costPair (x : FlatTM × List Nat × Nat × Nat) : Nat × Nat :=
  (s1Program.cost (rIn x), S1Map.s1Bound (encodable.size x))

#eval costPair (rM0, [], 0, 0)
#eval costPair (rMdup, [], 1, 2)

-- the verdict: budget met, and by how many orders of magnitude
#eval ([(rM0, [], 0, 0), (rMdup, [], 1, 2)] :
    List (FlatTM × List Nat × Nat × Nat)).map
  (fun x => let p := costPair x; (decide (p.1 ≤ p.2), p.2 / (p.1 + 1)))

-- `sig = 1` — one step up, to see how the two sides scale against each other
#eval costPair (rM1, [], 0, 0)
#eval (decide (S1Program.s1Program.cost (rIn (rM1, [], 0, 0))
  ≤ S1Map.s1Bound (encodable.size (rM1, ([] : List Nat), 0, 0))))

/-! ## §5 — how the two sides SCALE (model-only, so it reaches real `σ`)

The measured ratio in §4 *drops* from `3.1e9` at `σ = 0` to `2.1e8` at `σ = 1`:
the card register grows in `σ` much faster than `encodable.size` does. The
question the cost ladder has to answer is whether that ever catches up. It does
not — `cardBlocks` is `Θ(σ⁴·|trans|)` cells while the budget is degree `10` in a
size that already contains `σ` — but the crossover is what matters in practice,
so here is the leaf-cost proxy against the budget for `σ = 0 … 11`.

`S1Emit.emitBlk_cost` is `≤ 3 + 5v + v²` per emitted cell of value `v`, so
`Σ (3 + 5v + v²)` over `cardBlocks` is the emitter's leaf cost — the quantity
`Cmd.cost_forBnd_le` sits above. -/

def leafCost (M : FlatTM) : Nat :=
  ((S1Cards.cardBlocks M).map (fun v => 3 + 5 * v + v * v)).sum

def scaleRow (sg : Nat) : Nat × Nat × Nat × Nat :=
  let M : FlatTM :=
    { sig := sg, tapes := 1, states := 2, start := 0, halt := [false, true],
      trans := [rE 0 1 TMMove.Rmove] }
  let x : FlatTM × List Nat × Nat × Nat := (M, [], 0, 0)
  (sg, leafCost M, S1Map.s1Bound (encodable.size x),
    S1Map.s1Bound (encodable.size x) / (leafCost M + 1))

-- (σ, leaf cost, budget, head-room ratio) — the ratio must never reach 1.
-- ⚠ it DECAYS at first: `encodable.size` grows by 1 per `σ` while the card
-- register grows like `σ⁴`. Measured, the decay FLATTENS — the per-step factor
-- rises `0.78 → 0.92` across `σ = 6 … 11` — and degree 10 beats degree ~4, so
-- it turns around in the teens. The floor is `> 6·10^8`, i.e. the ladder is a
-- slack argument by eight orders of magnitude. Do not engineer for degree.
#eval (List.range 12).map scaleRow
