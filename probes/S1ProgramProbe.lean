import Complexity.NP.SAT.CookLevin.Reductions.S1Program

/-! # S1 probe — the assembled program's two branches

`Reductions/S1Program.lean` proves the guard-false half of `computes` outright
and the guard-true half modulo two `sorry`-ed stage contracts (`stageC_run`,
`stageMYes_run`). A sorried contract can be stated *wrongly* and still let the
assembly typecheck, so the contracts themselves are what this probe checks —
numerically, on the real frozen head layout rather than a hand-made state.

§1 the guard decides correctly on `headEncodeIn` (both branches);
§2 the guard-false branch really emits `s1Key S1Map.s1No` (five empties);
§3 **stage M-yes's hypotheses really are the output key** — running the built
   part of the yes branch (`stagePG ;; stageSig ;; stageInit ;; stageFin`) from
   `headEncodeIn` leaves registers `EOUT_S`/`EOUT_I`/`EOUT_F` equal to
   `s1Key (guessTableau …)`'s entries `1`, `2` and `4`;
§4 **stage C's stated target** is the key's entry `3`, and **`STEPS` carries the
   `+1`** (`guessTableauTyped.steps = steps + 1`, not a copy of register `4`);
§5 scale: the four emitted register lengths on a real instance.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1ProgramProbe.lean`
-/

open Complexity.Lang Complexity.Simulators S1Program

/-! ## Test instances -/

/-- A guard-satisfying machine (valid, single tape, symbols in range). -/
def pM0 : FlatTM :=
  { sig := 2, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some 0],
                dst_state := 1, dst_write_vals := [some 1],
                move_dirs := [TMMove.Rmove] }] }

/-- Same machine, three states / three symbols. -/
def pM1 : FlatTM :=
  { pM0 with sig := 3, states := 3, halt := [false, true, true] }

/-- **Off guard**: `halt.length ≠ states`. -/
def pMbad : FlatTM := { pM0 with states := 4 }

/-- Yes-instances: `(M, s, maxSize, steps)`, every symbol of `s` below `M.sig`. -/
def pCases : List (FlatTM × List Nat × Nat × Nat) :=
  [(pM0, [], 0, 0), (pM0, [1, 0], 2, 3), (pM0, [0], 0, 1),
   (pM1, [2, 1, 0], 1, 2), (pM1, [], 3, 0)]

def pIn (x : FlatTM × List Nat × Nat × Nat) : State := HeadLayout.headEncodeIn x

/-! ## §1 — the guard, on the frozen head layout -/

def guardFlag (x : FlatTM × List Nat × Nat × Nat) : List Nat :=
  State.get (S1Parse.stagePG.eval (pIn x)) S1Parse.FLG

#eval pCases.map (fun x => guardFlag x == [1])   -- expect all true
#eval guardFlag (pMbad, [1], 1, 1) == []         -- expect true (off guard)

/-! ## §2 — the guard-false branch

⚠ `#eval` of `s1Program` itself is impossible while `stageC`/`stageMYes` are
`sorry` — the evaluator refuses any expression depending on `sorryAx`, even
down a branch it never takes. So the no-branch is probed as the composition the
proof reduces it to (`Cmd.eval_ifBit_false` + `stageMNo_run`); this is
sorry-free and executable. Re-point it at `s1Program` once the two stages
land. -/

def noBranch : Cmd := S1Parse.stagePG ;; S1Cards.stageMNo

def noBranchOK (x : FlatTM × List Nat × Nat × Nat) : Bool :=
  s1Extract (noBranch.eval (pIn x)) == s1Key S1Map.s1No

#eval noBranchOK (pMbad, [1], 1, 1)              -- expect true
#eval s1Key S1Map.s1No                           -- expect [[], [], [], [], []]

/-! ## §3 — stage M-yes's hypotheses ARE the output key

This is the contract `stageMYes_run` assumes and cannot yet prove. Running the
built prefix of the yes branch from the real input layout must leave the three
emitter outputs equal to entries `1`, `2` and `4` of `s1Key`. -/

def builtPrefix : Cmd :=
  S1Parse.stagePG ;; S1Emit.stageSig ;; S1Emit.stageInit ;; S1Emit.stageFin

def keyOf (x : FlatTM × List Nat × Nat × Nat) : List (List Nat) :=
  s1Key (guessTableau x.1 x.2.1 x.2.2.1 x.2.2.2)

def prefixOK (x : FlatTM × List Nat × Nat × Nat) : Bool × Bool × Bool :=
  let t := builtPrefix.eval (pIn x)
  let k := keyOf x
  (State.get t S1Emit.EOUT_S == k.getD 0 [],
   State.get t S1Emit.EOUT_I == k.getD 1 [],
   State.get t S1Emit.EOUT_F == k.getD 3 [])

#eval pCases.map prefixOK      -- expect all (true, true, true)

/-- The head layout's register `4` (`1^steps`) must SURVIVE all four stages —
stage M-yes builds `1^(steps+1)` from it, so anything that clobbered it would
be caught here and nowhere else. -/
def stepsRegSurvives (x : FlatTM × List Nat × Nat × Nat) : Bool :=
  State.get (builtPrefix.eval (pIn x)) S1Emit.HSTP
    == List.replicate x.2.2.2 1

#eval pCases.map stepsRegSurvives             -- expect all true

/-! ## §4 — stage C's target, and the `+ 1` on `STEPS` -/

/-- `stageC_run`'s stated conclusion (`EOUT_C = encNats (cardBlocks M)`) is the
key's entry `3`. Proven by `S1Cards.encCards_eq`; checked here because it is the
one place a wrong `stageC_run` statement would hide. -/
def cardTargetOK (x : FlatTM × List Nat × Nat × Nat) : Bool :=
  FlatTCCFree.encNats (S1Cards.cardBlocks x.1) == (keyOf x).getD 2 []

#eval pCases.map cardTargetOK                 -- expect all true

/-- ⚠ `guessTableauTyped.steps = steps + 1`. If this printed `1^steps` the
five-copies reading of stage M-yes would be right — it is not. -/
def stepsTargetOK (x : FlatTM × List Nat × Nat × Nat) : Bool × Bool :=
  ((keyOf x).getD 4 [] == List.replicate (x.2.2.2 + 1) 1,
   (keyOf x).getD 4 [] == List.replicate x.2.2.2 1)

#eval pCases.map stepsTargetOK   -- expect (true, false) on EVERY case, steps = 0 included

/-! ## §5 — scale (the cost ladder's raw numbers) -/

#eval pCases.map (fun x =>
  let k := keyOf x
  ((k.getD 0 []).length, (k.getD 1 []).length, (k.getD 2 []).length,
   (k.getD 3 []).length, (k.getD 4 []).length))
