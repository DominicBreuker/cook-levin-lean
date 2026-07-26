import Complexity.NP.SAT.CookLevin.Reductions.S1Program

/-! # S1 probe — stage M-yes, and stage C's first five card families

`Reductions/S1Program.lean`'s `stageMYes` and `Reductions/S1CardEmit.lean`'s
`cFive` are both built and `sorry`-free, so unlike the skeleton phase they can
be `#eval`-ed end to end. What this probe adds beyond the proofs:

§1 **the five families really are a PREFIX of `S1Cards.cardBlocks`** — the
   proofs say `cFive` emits `copy ++ copyRight ++ haltLeft ++ haltCenter ++
   haltRight`; only a numeric check says that list is the *start* of the stage-C
   target, i.e. that the next session's two families are exactly the suffix;
§2 **stage M-yes end to end**: run the whole yes branch with stage C's output
   injected by hand and compare the five output registers with
   `s1Key (guessTableau …)`;
§3 scale — what fraction of the card register the five families are, and how
   big the remaining two are (the cost ladder's raw numbers);
§4 corner instances: the trivial machine, `sig = 0`, empty transition table
   (the "probe the empty/zero instance of every size claim" invariant).

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1CardEmitProbe.lean`
-/

open Complexity.Lang Complexity.Simulators S1Program

/-! ## Test instances (the `S1ProgramProbe` machines, plus two corners) -/

def qM0 : FlatTM :=
  { sig := 2, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some 0],
                dst_state := 1, dst_write_vals := [some 1],
                move_dirs := [TMMove.Rmove] }] }

def qM1 : FlatTM :=
  { qM0 with sig := 3, states := 3, halt := [false, true, true] }

/-- The trivial machine: one state, no symbols, no transitions. -/
def qMtriv : FlatTM :=
  { sig := 0, tapes := 1, states := 0, start := 0, halt := [true], trans := [] }

/-- A machine whose halt list is SHORTER than `states` — the halt gate must read
the missing bits as `false` (the drained-empty `head`). -/
def qMshort : FlatTM := { qM0 with states := 3, halt := [false] }

def qCases : List (FlatTM × List Nat × Nat × Nat) :=
  [(qM0, [], 0, 0), (qM0, [1, 0], 2, 3), (qM0, [0], 0, 1),
   (qM1, [2, 1, 0], 1, 2), (qM1, [], 3, 0),
   (qMtriv, [], 0, 0), (qMshort, [1], 1, 1)]

def qIn (x : FlatTM × List Nat × Nat × Nat) : State := HeadLayout.headEncodeIn x

/-- Everything before stage C: parse + guard, then Σ and I. -/
def preC : Cmd := S1Parse.stagePG ;; S1Emit.stageSig ;; S1Emit.stageInit

/-! ## §1 — the five families are a prefix of the stage-C target -/

def fiveOut (x : FlatTM × List Nat × Nat × Nat) : List Nat :=
  State.get (S1CardEmit.cFive.eval (preC.eval (qIn x))) S1Emit.EOUT_C

def cardTarget (x : FlatTM × List Nat × Nat × Nat) : List Nat :=
  FlatTCCFree.encNats (S1Cards.cardBlocks x.1)

/-! ⚠ The load-bearing check: `cFive`'s output must be a genuine PREFIX of the
whole card register. If a later family were inserted before one of these five,
or the order inside `cardBlocks` changed, this is the only thing that would
notice. -/
#eval qCases.map (fun x => (fiveOut x).isPrefixOf (cardTarget x))   -- expect all true

/-! …and the five families are *not* the whole thing: the next session's two
families are non-empty on every instance, the trivial machine included. -/
#eval qCases.map (fun x => decide ((fiveOut x).length < (cardTarget x).length))

/-! ## §2 — stage M-yes, end to end

Stage C is still a placeholder, so its output register is injected by hand; the
other four registers come from the real emitter stages. -/

def yesState (x : FlatTM × List Nat × Nat × Nat) : State :=
  let t := (preC ;; S1Emit.stageFin).eval (qIn x)
  State.set t S1Emit.EOUT_C (cardTarget x)

def keyOf' (x : FlatTM × List Nat × Nat × Nat) : List (List Nat) :=
  s1Key (guessTableau x.1 x.2.1 x.2.2.1 x.2.2.2)

/-! The whole output multiplex: all five registers at once. -/
#eval qCases.map (fun x => s1Extract (stageMYes.eval (yesState x)) == keyOf' x)

/-! Per-register, so a failure says which one. -/
#eval qCases.map (fun x =>
  let e := s1Extract (stageMYes.eval (yesState x))
  let k := keyOf' x
  (e.getD 0 [] == k.getD 0 [], e.getD 1 [] == k.getD 1 [],
   e.getD 2 [] == k.getD 2 [], e.getD 3 [] == k.getD 3 [],
   e.getD 4 [] == k.getD 4 []))

/-! ⚠ `STEPS` carries the `+ 1` (`guessTableauTyped.steps = steps + 1`). If
stage M-yes had been five copies, the second component would be `true`. -/
#eval qCases.map (fun x =>
  let e := s1Extract (stageMYes.eval (yesState x))
  (e.getD 4 [] == List.replicate (x.2.2.2 + 1) 1,
   e.getD 4 [] == List.replicate x.2.2.2 1))

/-! ## §3 — scale: how much of the card register the five families are -/

#eval qCases.map (fun x =>
  ((fiveOut x).length, (cardTarget x).length))

/-! ⚠ **The split of what is left.** `(five, step, prelude)` cell counts: the
five families built here are a *small* minority of the card register — the two
still open (`stepBlocks` off `normTrans`, and `preludeBlocks`) carry the bulk,
so they, not these, are what the cost ladder must bound. -/
#eval qCases.map (fun x =>
  let M := x.1
  ((fiveOut x).length,
   (FlatTCCFree.encNats ((normTrans M).flatMap (S1Cards.entryBlocks M))).length,
   (FlatTCCFree.encNats
      (S1Cards.preludeBlocks M.sig M.states (min M.start M.states))).length))

/-! ## §4 — the corners

The trivial machine and the short halt list are the instances a "realistic"
probe would miss (locked invariant: probe the empty/zero instance of every
claim). Both are already in `qCases`; these are the raw values. -/

#eval (fiveOut (qMtriv, [], 0, 0)).length
#eval (cardTarget (qMtriv, [], 0, 0)).length
#eval (fiveOut (qMshort, [1], 1, 1)).isPrefixOf (cardTarget (qMshort, [1], 1, 1))

/-! The stage-C constants after the preamble, on the trivial machine: `CS1`,
`CS2`, `CQ1`, `CBV`, `CZ` (lengths). -/
#eval
  let t := S1CardEmit.cPre.eval (preC.eval (qIn (qMtriv, [], 0, 0)))
  ((State.get t S1CardEmit.CS1).length, (State.get t S1CardEmit.CS2).length,
   (State.get t S1CardEmit.CQ1).length, (State.get t S1CardEmit.CBV).length,
   (State.get t S1CardEmit.CZ).length)
