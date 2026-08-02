import Complexity.Complexity.Deciders.SATStr

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # `SATStr` — the measurements behind SAT as a STRING language

Bottom-up item 2 (2026-08-04). This file was written **before** the modules it
probes and is kept as their intent pin: every check here ran green on the model
first, and the proofs in `Complexity/Complexity/Deciders/CnfWellFormed.lean` and
`.../SATStr.lean` were written against exactly these statements (FINDING AI).

Everything below imports the **real** definitions — there are no local copies,
so a change to the program or to the scanner shows up here.

## What it measures

* **§1/§2 — the scanner is the grammar.** `CnfWellFormed.wfCnfB` accepts a
  `0`/`1` stream **iff** `CnfSerialize.decCnf` returns a CNF whose encoding is
  that stream, exhaustively over every stream of length `≤ 8`; and the same pass
  counts the clauses. (Proven: `wfCnfB_iff`, `cnfCount_eq_length`.)
* **§3 — the builder meets the bridge.** `AgreeBelow 19` against
  `EvalCnfSplit.satEIn (cnfOf x, c)`, exhaustively at length `≤ 7`. (Proven:
  `satStrBuild_bridge`.)
* **§4 — the composite decides the language**, machine against model,
  exhaustively at length `≤ 6`.
* **§5 — the language is a real one**: malformed strings rejected on every
  certificate; a *well-formed* encoding of an unsatisfiable formula also
  rejected, so the two failure modes are distinguished.
* **§6 — the loop invariant at every index** — the `_run` lemma's motive as a
  `Bool` function, which is what made `scanBody_run` mechanical.
* **§7 — cost.** `Cmd.chk` accepts the re-encoder, so the whole `cost_le`
  obligation is one `by decide`.

## The finding this file produced

The HANDOFF scoped this item as "an on-machine parser `Cmd` from a
self-delimiting bit format into the twelve-register layout". §1 measured that
there is **nothing to parse**: `EvalCnfCmd.encodeCnf` is already a flat `0`/`1`
stream and `certState x` is already one register of `0`/`1` cells, so
`CNF_STREAM` is a *copy of the input register*. The only derived field is
`CLAUSE_TALLY`, which the same validating scan counts. One `forBnd`, 11 ops.
-/

namespace SATStrProbe

open Complexity.Lang EvalCnfCmd CnfWellFormed SATStr

/-! ## §1 — the scanner accepts exactly the encodings, and counts their clauses -/

def sampleCnfs : List cnf :=
  [ []
  , [[]]
  , [[(true, 0)]]
  , [[(true, 0)], [(false, 0)]]
  , [[(true, 0), (false, 1)], [(true, 2)], []]
  , [[(false, 3), (true, 0), (true, 1)], [(false, 0), (false, 2)]] ]

/-! Every sample encoding validates, the count is the clause count, and the
parse round-trips. **Expect `true`.** -/

#eval sampleCnfs.all (fun N =>
  wfCnfB (encodeCnf N) && (cnfCount (encodeCnf N) == N.length)
    && (parseTotal (encodeCnf N) == N))

/-! ## §2 — …and nothing else

Exhaustive over every `0`/`1` stream of length `≤ 8`: the scanner accepts a
stream **iff** the canonical parser returns a CNF whose encoding is that stream.
This is `CnfWellFormed.wfCnfB_iff`, measured. **Expect `true`.** -/

def allStreams : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (allStreams n).flatMap (fun l => [l, 0 :: l, 1 :: l])

#eval (allStreams 8).all (fun l =>
  wfCnfB l == (match CnfSerialize.decCnf l with
               | some N => encodeCnf N == l
               | none => false))

/-! …and on a validating stream the counter is the clause count
(`cnfCount_eq_length`). **Expect `true`.** -/

#eval (allStreams 8).all (fun l =>
  !(wfCnfB l) || (cnfCount l == (parseTotal l).length))

/-! The `pending` bit is load-bearing: a literal run with no clause terminator
must be rejected. **Expect `[false, false, false, false]`.** -/

#eval [wfCnfB [1], wfCnfB [1, 1], wfCnfB [1, 1, 0], wfCnfB [1, 1, 1]]

/-! ## §3 — the builder meets the bridge -/

def agreeBelow (k : Nat) (s t : State) : Bool :=
  (List.range k).all (fun r => State.get s r == State.get t r)

def buildOK (x c : List Bool) : Bool :=
  agreeBelow 19 (satStrBuild.eval (strEIn (x, c)))
    (EvalCnfSplit.satEIn (cnfOf x, c))

def allBools : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBools n).flatMap (fun l => [l, false :: l, true :: l])

/-! Exhaustive over every input of length `≤ 7`, at a fixed certificate — the
well-formed and the malformed branch alike. **Expect `true`.** -/

#eval (allBools 7).all (fun x => buildOK x [true, false])

/-! …and over a spread of certificates. **Expect `true`.** -/

#eval (allBools 4).all (fun x =>
  [[], [false], [true], [true, false], [false, true, true]].all (fun c => buildOK x c))

/-! ## §4 — the composite decides the language -/

def machineSays (x c : List Bool) : Bool := (satStrCmd.eval (strEIn (x, c))).isAccept

def modelSays (x c : List Bool) : Bool :=
  evalCnf (EvalCnfSplit.decodeBits c) (cnfOf x)

/-! Machine against model, exhaustively at input length `≤ 6`, three
certificates — accept AND reject, so there is no third verdict.
**Expect `true`.** -/

#eval (allBools 6).all (fun x =>
  [[], [true], [true, false]].all (fun c =>
    (machineSays x c == modelSays x c)
      && ((satStrCmd.eval (strEIn (x, c))).isReject == !(modelSays x c))))

/-! ## §5 — the language is a real one

`[true]` is not an encoding: rejected on every certificate up to length 4.
**Expect `true`.** -/

#eval (allBools 4).all (fun c => !(machineSays [true] c))

/-! `encodeCnf [[(true,0)]]` = `x₀`: accepted with `c = [true]`, rejected with
`c = [false]`. **Expect `(true, false)`.** -/

#eval (machineSays [true, true, false, false] [true],
       machineSays [true, true, false, false] [false])

/-! `encodeCnf [[(true,0)],[(false,0)]]` = `x₀ ∧ ¬x₀` — a *well-formed* encoding
of an unsatisfiable formula, rejected on every certificate up to length 4. This
is what separates "is not an encoding" from "is not satisfiable".
**Expect `true`.** -/

#eval (allBools 4).all (fun c =>
  !(machineSays [true, true, false, false, true, false, false, false] c))

/-! ## §6 — the loop invariant, at every index (FINDING AI)

`scanBody_run`'s motive as a `Bool` function. Keep this in sync with the
theorem: if the invariant changes, this is the cheapest place to find out. -/

def invAt (x : List Bool) (i : Nat) : Bool :=
  let st := Cmd.foldlState scanBody WIDX (List.range i) (satStrPre.eval (strEIn (x, [])))
  let m := scanTake (strBits x) i
  (State.get st WCUR == (strBits x).drop i) &&
  (State.get st WSA == flagOf m.1) &&
  (State.get st WSB == flagOf m.2.1) &&
  (State.get st WTAL == List.replicate m.2.2 1)

/-! **Expect `true`** — at every index `0 … |x|`, for every input of length
`≤ 8`. -/

#eval (allBools 8).all (fun x => (List.range (x.length + 1)).all (fun i => invAt x i))

/-! ## §7 — cost

The scan is one pass with a shrinking cursor, so the re-encoder is quadratic.
Printed at `n = 20` and `n = 40`; what the witness needs is the line below it. -/

#eval (satStrMfc.cost (strEIn (List.replicate 20 true, List.replicate 20 true)),
       satStrMfc.cost (strEIn (List.replicate 40 true, List.replicate 40 true)))

/-! `Cmd.chk` accepts the re-encoder, which is the whole `cost_le` obligation
(`satStrMfc_chk`, `by decide`, ~5 s). **Expect `true`.** -/

#eval (satStrMfc.chk strRegs).1

end SATStrProbe
