import Complexity.Lang.Compile
open Complexity.Lang
open TMPrimitives

/-! # `copyEmptyTM` probe (bottom-up, 2026-06-19)

The `compareRegsTM` (eqBit d2) assembly needs a head-`0`→head-`0` "copy register
`src` into the EMPTY register `dst`" gadget whose budget is the TIGHT
`copyLoop_run` cost (`≈5L²`), NOT `opCopy`'s `clear ⨾ …` (whose two clears alone
cost `≈18L²` — see `CompareRegsBudgetProbe`). So we drop the clear phase:

  `copyEmptyTM dst src = navigateToRegTM src ⨾ copyLoopTM dst ⨾ justRewindTM`

(`opCopy = clearRegionTM dst ⨾ navigateToRegTM src ⨾ copyLoopTM dst ⨾ justRewindTM`,
i.e. `copyEmptyTM` = `opCopy`'s phases 2–4.) This probe validates, by `#eval`,
that with `dst` initially empty the machine lands head `0` with
`encodeTape (s.set dst (s.get src))` and the expected step count. -/

namespace CopyEmptyProbe

/-- The clear-free copy machine = `opCopy` minus phase 1. NOW PROVEN in
`Compile.lean` as `Compile.copyEmptyRawTM` + `Compile.copyEmpty_run`
(axiom-clean, tight budget `(|src|+1)(5L+23) + 3L + 4`); this probe stays as the
end-to-end `#eval` regression check. -/
abbrev copyEmptyTM (dst src : Var) : FlatTM := Compile.copyEmptyRawTM dst src

/-- The kept "found" exit (justRewind's found halt, shifted past nav⨾loop). -/
abbrev copyEmptyTM_exit (dst src : Var) : Nat := Compile.copyEmptyRawTM_exit dst src

partial def runToHalt (M : FlatTM) (cfg : FlatTMConfig) (fuel : Nat) :
    Option (Nat × FlatTMConfig) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if haltingStateReached M cfg then some (0, cfg)
      else match stepFlatTM M cfg with
        | none => none
        | some cfg' => (runToHalt M cfg' fuel).map (fun (n, c) => (n + 1, c))

/-- `src=0`, `dst=1` (empty), reg0 = `replicate len 1`; nregs registers.
Returns `(steps, exitState, expectedExit, tapeMatches, L, tightBudget)`. -/
def measure (len nregs : Nat) : Nat × Nat × Nat × Bool × Nat × Nat :=
  let s : State := List.replicate len 1 :: List.replicate (nregs - 1) []
  let M := copyEmptyTM 1 0
  let cfg := initFlatConfig M [Compile.encodeTape s]
  let L := (Compile.encodeTape s).length
  match runToHalt M cfg (300 * (L + 2) * (L + 2)) with
  | none => (0, 0, copyEmptyTM_exit 1 0, false, L, 0)
  | some (steps, c) =>
      let expectTape := Compile.encodeTape (s.set 1 (State.get s 0))
      let tapeOk := (c.tapes.headD ([], 0, [])).2.1 = 0 &&
                    decide ((c.tapes.headD ([], 0, [])).2.2 = expectTape)
      (steps, c.state_idx, copyEmptyTM_exit 1 0, tapeOk, L, (len + 1) * (5 * L + 23))

#eval measure 2 4
#eval measure 4 4
#eval measure 3 6
#eval measure 5 6

/-- Does the real step count fit the tight `copyLoop_run` budget? (`true` = fits.) -/
def fitsTight (len nregs : Nat) : Bool :=
  let (steps, _, _, _, _, tight) := measure len nregs
  steps ≤ tight

#eval fitsTight 2 4
#eval fitsTight 4 4
#eval fitsTight 5 6

/-- Does the exit state match the predicted `copyEmptyTM_exit`, and tape match? -/
def exitOk (len nregs : Nat) : Bool :=
  let (_, st, ex, tapeOk, _, _) := measure len nregs
  decide (st = ex) && tapeOk

#eval exitOk 2 4
#eval exitOk 4 4
#eval exitOk 3 6
#eval exitOk 5 6

end CopyEmptyProbe
