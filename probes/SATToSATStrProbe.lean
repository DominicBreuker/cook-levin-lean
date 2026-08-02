import Complexity.NP.SAT.CookLevin.Reductions.SAT_to_SATStr_comp

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # `SAT ⪯p' SATStr` and the sixth seam — the measurements

Bottom-up item 1 (2026-08-05). Everything here imports the **real** definitions
(no local copies), so it is a genuine regression gate for
`Reductions/SAT_to_SATStr_free.lean`, `Reductions/SAT_to_SATStr_comp.lean` and
`Lang/SerializeStr.lean`. Runtime ~5 s.

## What it measures

* **§1 — FINDING AT, measured.** The reason `Serialize`'s no-compression law had
  to become a *polynomial* law: `encodable.size` on `List Bool` exceeds the
  canonical layout's cell count. This is the **negative control** — if §1 ever
  prints `false`, the identity form has become satisfiable and the class change
  should be revisited.
* **§2 — the two canonical serializations coincide.** `strBits (satToStr N)`
  against `encodeCnf N`, on samples and exhaustively over short streams.
  (Proven: `SATToSATStr.strBits_satToStr`.)
* **§3 — the round trips.** `decBits ∘ strBits = some` and
  `strBits ∘ boolsOf = id` on bit streams — and `boolsOf` really does need the
  bit hypothesis (a second negative control).
* **§4 — the reduction is correct as a language equality**, decidably: the image
  of `satToStr` validates the CNF grammar and parses back to the source CNF, so
  `SATStr (satToStr N)` and `SAT N` are the same question. (Proven:
  `SATToSATStr.satStr_satToStr` — whose `⇒` half additionally needs
  `encodeCnf`'s injectivity.)
* **§5 — the program and the seam actually run.** The no-op `Cmd`, its cost, and
  the seam's `copy 0 2` on a synthetic exit state.
* **§6 — the composite verifier accepts the image.** The full `SATStr` verifier
  `Cmd` (scan + SAT verifier) run on `satToStr N` with a real certificate: the
  round trip `SAT N → SATStr (satToStr N)` end to end, on the machine.

## What it deliberately does NOT measure

The chain-level exit lemma (`SATStrComp.front_exitsOnCNFOUT`) cannot be
`#eval`ed — the composite program is the whole Cook–Levin chain. It is proven by
transport from `FSATSATFree.buildSAT_run`, and `probes/SATSeamProbe.lean`
already exercises that end.
-/

namespace SATToSATStrProbe

open Complexity.Lang EvalCnfCmd CnfWellFormed
open SATToSATStr (satToStr)

def sampleCnfs : List cnf :=
  [ []
  , [[]]
  , [[(true, 0)]]
  , [[(true, 0)], [(false, 0)]]
  , [[(true, 0), (false, 1)], [(true, 2)], []]
  , [[(false, 3), (true, 0), (true, 1)], [(false, 0), (false, 2)]] ]

def allBools : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBools n).flatMap (fun l => [l, false :: l, true :: l])

/-! ## §1 — FINDING AT: why the no-compression law is a polynomial law

`Serialize.size_le_enc_length` used to read `encodable.size x ≤ (enc x).length`.
For the canonical bit-string layout that is **false**, and this is the whole
evidence: the strings below have `encodable.size` strictly greater than their
cell count. Nothing is compressed — `strBits` is a bijection onto `{0,1}^n` —
`encodable.size` simply charges 2 for a `true` and 1 for a `false`.

**Expect `true`** — i.e. the identity form is unsatisfiable here. If this ever
prints `false`, the class change should be revisited. -/

#eval (allBools 3).any (fun x => decide (encodable.size x > (strBits x).length))

/-! The witness at length one, spelled out: `(size, |enc|)`.
**Expect `(2, 1)`.** -/

#eval (encodable.size ([true] : List Bool), (strBits [true]).length)

/-! …and the law the instance actually carries holds everywhere.
**Expect `true`.** -/

#eval (allBools 6).all (fun x => decide (encodable.size x ≤ 2 * (strBits x).length))

/-! ## §2 — the two canonical serializations coincide

This is the entire computational content of `SAT ⪯p' SATStr`: the bit string
`satToStr N` has, cell for cell, the CNF's own canonical stream.
**Expect `true`.** -/

#eval sampleCnfs.all (fun N => strBits (satToStr N) == encodeCnf N)

/-! …and, exhaustively, over every CNF the grammar admits at stream length `≤ 8`
(i.e. every `N` in the image of `parseTotal` on a validating stream).
**Expect `true`.** -/

def allStreams : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (allStreams n).flatMap (fun l => [l, 0 :: l, 1 :: l])

#eval ((allStreams 8).filter (fun l => wfCnfB l)).all (fun l =>
  strBits (satToStr (parseTotal l)) == l)

/-! ## §3 — the round trips, and that `boolsOf` needs its hypothesis

`decBits ∘ strBits = some` (proven: `decBits_strBits`) and
`strBits ∘ boolsOf = id` **on bit streams** (proven: `strBits_boolsOf`).
**Expect `true`.** -/

#eval (allBools 8).all (fun x => decBits (strBits x) == some x)

#eval (allStreams 8).all (fun l => strBits (boolsOf l) == l)

/-! The negative control for `strBits_boolsOf`'s hypothesis: a cell that is not
a bit is not recovered, and `decBits` refuses it outright.
**Expect `([0], [1], false)`** — `2` collapses to `false`/`0`, and the parser
returns `none`. -/

#eval (strBits (boolsOf [2]), strBits (boolsOf [1]), (decBits [2]).isSome)

/-! ## §4 — the reduction is correct, decidably

`SATStr (satToStr N) ↔ SAT N` is a statement about satisfiability, which is not
decidable at this level — but its *content* is: the image validates the grammar
and parses back to `N`, so both sides ask about the same CNF. The remaining step
(`encodeCnf` is injective) is `CnfSerialize.decCnf_encodeCnf`.
**Expect `true`.** -/

#eval sampleCnfs.all (fun N =>
  wfCnfB (strBits (satToStr N)) && (SATStr.cnfOf (satToStr N) == N))

/-! ## §5 — the program and the seam run

The witness's `Cmd` is the layer's no-op, so the exit register **is** the input
register; its cost is `|encodeCnf N| + 1`. **Expect `true`.** -/

#eval sampleCnfs.all (fun N =>
  (State.get (SATToSATStr.strCmd.eval (SATToSATStr.encodeIn N)) SATToSATStr.OUT
      == encodeCnf N)
    && (SATToSATStr.decodeOut (SATToSATStr.strCmd.eval (SATToSATStr.encodeIn N))
      == satToStr N)
    && (SATToSATStr.strCmd.cost (SATToSATStr.encodeIn N) == (encodeCnf N).length + 1))

/-! The seam's `mfc` on a synthetic left-exit state: the tail leaves
`encodeCnf N` on register `2` with junk elsewhere, and `strMfc` must put it on
register `0` — which is the whole `AgreeBelow 1` bridge.
**Expect `true`.** -/

def fakeExit (N : cnf) : State :=
  [[1, 1, 1], List.replicate N.length 1, encodeCnf N, [0, 1, 0], [1]]

#eval sampleCnfs.all (fun N =>
  State.get (SATStrComp.strMfc.eval (fakeExit N)) SATToSATStr.OUT
    == State.get (SATToSATStr.encodeIn N) SATToSATStr.OUT)

/-! …and its cost, which is what `mfcBound` must dominate: `|encodeCnf N| + 1`.
**Expect `true`.** -/

#eval sampleCnfs.all (fun N =>
  SATStrComp.strMfc.cost (fakeExit N) == (encodeCnf N).length + 1)

/-! ## §6 — the composite verifier accepts the image, end to end

The loop closes on the machine: take a satisfiable CNF, map it with `satToStr`,
hand the result and a real certificate to the **`SATStr` verifier `Cmd`** of
`Deciders/SATStr.lean`, and it accepts — while the same input with a
non-satisfying certificate is rejected.

`phi = x₀ ∧ (¬x₀ ∨ x₁)`. The certificate is the characteristic vector of the
true variables: `[true, true]` sets `x₀, x₁` and satisfies both clauses;
`[true, false]` sets only `x₀`, leaving the second clause false.
**Expect `(true, false)`.** -/

def phi : cnf := [[(true, 0)], [(false, 0), (true, 1)]]

#eval ((SATStr.satStrCmd.eval (SATStr.strEIn (satToStr phi, [true, true]))).isAccept,
       (SATStr.satStrCmd.eval (SATStr.strEIn (satToStr phi, [true, false]))).isAccept)

/-! …and an UNSATISFIABLE CNF's image is rejected on every certificate of length
`≤ 4` — the reduction does not accidentally send everything into the language.
**Expect `true`.** -/

def psi : cnf := [[(true, 0)], [(false, 0)]]

#eval (allBools 4).all (fun c =>
  !(SATStr.satStrCmd.eval (SATStr.strEIn (satToStr psi, c))).isAccept)

end SATToSATStrProbe
