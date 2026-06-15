import Complexity.Lang.Compile
open Complexity.Lang

/-! # `eqBit` budget measurement probe (bottom-up, 2026-06-14c)

**The open question (HANDOFF d2a):** does **design (A)** for `eqBit`
(`compareRegsTM` = grow 2 scratch ⨾ copy `src1`→`sc1` ⨾ copy `src2`→`sc2` ⨾
consume-loop ⨾ verdict ⨾ clear+shrink) fit the `cost=1` per-op contract budget
`(9L²+9L+30)·(cost+1) = (9L²+9L+30)·2 ≈ 18L²`, or is a cost bump forced?

**The prior session's worry** (HANDOFF "design (A) … likely needs a cost bump"):
the two copies were assumed to cost `~9L²` *each* — busting `18L²` — because the
only copy run-lemma considered was `Compile.opCopy_run`, whose budget is the
**loose** `(9L²+9L+30)·(|src|+2)` (a re-wrap to the per-op CONTRACT's quadratic
shape, NOT the copy's real cost).

**The resolution (this probe):** the copy's *real* cost is `Θ(|src|·L)` (linear
per bit), and the **tight** budget is already PROVEN in `Compile.copyLoop_run`:
`(|src|+1)·(5L+23)`. Reusing **`copyLoop_run`** (not `opCopy_run`), two copies
cost `≤ (|src1|+|src2|+2)·(5L+23) ≤ ~5L²`, leaving ~13L² for the consume loop
(itself `Θ(L²)`, a few passes/bit on shrinking registers). **Design (A) fits
`cost=1` faithfully** — no cost bump, no new copy-budget lemma.

`cost=1` is the FAITHFUL choice: `eqBit` is genuinely a `Θ(L²)` operation (like
`clear`/`nonEmpty`/`head`, all `cost=1`). A data-aware `Op.cost eqBit` would
OVER-charge it to `Θ(L³)` — the actual hack — and re-open EvalCnf's quartic cost
proof (`eqBit BLOCK_ACC LIT_VAR` compares `Θ(n)` unary var-indices in nested
`forBnd` loops). -/

namespace CompareRegsBudgetProbe

/-- Count steps until `M` reaches a halting state (or `fuel` exhausted). -/
partial def stepsToHalt (M : FlatTM) (cfg : FlatTMConfig) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
      if haltingStateReached M cfg then 0
      else match stepFlatTM M cfg with
        | none => 0
        | some cfg' => stepsToHalt M cfg' fuel + 1

/-- A state with register 0 = `replicate len 1` (a `len`-bit unary block) and
`nregs-1` empty registers. -/
def mkState (len nregs : Nat) : State :=
  List.replicate len 1 :: List.replicate (nregs - 1) []

/-- Measure one `opCopy 1 0` (copy reg0 into empty reg1). Returns
`(realSteps, L, 18L² [eqBit cost=1 budget],
  opCopy_run budget = (9L²+9L+30)(len+2) [LOOSE],
  copyLoop_run budget = (len+1)(5L+23) [TIGHT/faithful])`. -/
def measureCopy (len nregs : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let s := mkState len nregs
  let M := (Compile.opCopy 1 0).M
  let cfg := initFlatConfig M [Compile.encodeTape s]
  let L := (Compile.encodeTape s).length
  let steps := stepsToHalt M cfg (200 * (L + 2) * (L + 2))
  (steps, L, 18 * L * L, (9 * L * L + 9 * L + 30) * (len + 2), (len + 1) * (5 * L + 23))

/-! ## opCopy real steps vs the loose `opCopy_run` budget vs the tight
`copyLoop_run` budget vs the `cost=1` eqBit budget `18L²`.

Columns: `(realSteps, L, 18L², opCopy_run [loose], copyLoop_run [tight])`. -/

#eval measureCopy 2 4
#eval measureCopy 4 4
#eval measureCopy 6 6
#eval measureCopy 8 6
#eval measureCopy 10 8

/-- **The verdict.** Two copies via the TIGHT `copyLoop_run` budget, leaving
≥ half of `18L²` for the consume loop ⇒ design (A) fits `cost=1`. `true` = fits. -/
def twoTightCopiesFitHalfBudget (len nregs : Nat) : Bool :=
  let (_, _, b18, _, tight) := measureCopy len nregs
  2 * tight ≤ b18      -- 2 copies (tight) ≤ half the eqBit budget (rest = consume loop)

#eval twoTightCopiesFitHalfBudget 4 4
#eval twoTightCopiesFitHalfBudget 8 6
#eval twoTightCopiesFitHalfBudget 10 8

/-- For contrast: reusing `opCopy_run` (loose) for the copies does NOT fit — this
is the trap the prior session hit. `true` = busts the budget. -/
def looseCopyBustsBudget (len nregs : Nat) : Bool :=
  let (_, _, b18, loose, _) := measureCopy len nregs
  loose > b18

#eval looseCopyBustsBudget 4 4
#eval looseCopyBustsBudget 8 6
#eval looseCopyBustsBudget 10 8

/-- Steps `opTail src src` (in-place delete-first-bit) spends on register `src`
(length `len`) at index `idx` — the consume loop's per-iteration delete. Linear
in `L`, confirming the consume loop is `Θ(L²)` (a few passes/bit). -/
def measureTail (len idx nregs : Nat) : Nat × Nat :=
  let s : State := (List.replicate idx []) ++ [List.replicate len 1]
      ++ List.replicate (nregs - idx - 1) []
  let M := (Compile.opTail idx idx).M
  let cfg := initFlatConfig M [Compile.encodeTape s]
  let L := (Compile.encodeTape s).length
  (stepsToHalt M cfg (200 * (L + 2) * (L + 2)), L)

#eval measureTail 4 1 4
#eval measureTail 8 2 6
#eval measureTail 10 3 8

end CompareRegsBudgetProbe
