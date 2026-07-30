import Complexity.Complexity.Deciders.EvalCnfSplit

/-! # Probe: does the live SAT verifier factor as an `InNPWitnessLangFreeSplit`?

This probe validates the **design** of `inNPLangFreeSplit SAT` (the last piece of
`NPcomplete'' SAT`) numerically, before any of it is proven.

The three questions, in the order in which they can kill the design:

**§1 — the layout.** `InNPWitnessLangFreeSplit` demands
`verifier.encodeIn (N, c) = encX N ++ certState c` with `(encX N).length` a
per-witness CONSTANT. The live verifier's `EvalCnfCmd.encodeState` is a
12-register literal whose certificate (`ASSGN = 3`) sits *before* 8 trailing
scratch `[]`s, so it does not factor verbatim. But `precomposeFree` lets us
CHOOSE the composite's `encodeIn`, and `State.get` reads unset registers as
`[]`, so
```
satEncX N = [[], 1^|N|, encodeCnf N]     (xWidth = 3)
satEIn (N, c) = satEncX N ++ certState c
```
puts the certificate register exactly at `ASSGN`, and registers `4`–`15` read
`[]` on both sides. §1 checks that: `satEIn (N,c)` already agrees with
`encodeState (N, a)` on all of `[0,16)` **except** register 3. So the whole gap
is one register, and the trailing-`[]` worry is a non-issue.

**§2 — the decoder.** Register 3 holds the raw certificate bits; the verifier
wants `encodeAssgn a`. The certificate semantics is the textbook characteristic
vector: `decodeBits c` = the indices at which `c` is `true` (`bitsToAssgn`).
`certDecode` is the candidate re-encoder `Cmd`: one `forBnd` over a cursor copy
of the bits, emitting `[1] ++ 1^i ++ [0]` at each `true`. §2 checks
`AgreeBelow 16 (certDecode.eval (satEIn (N,c))) (encodeState (N, decodeBits c))`
— the `FreePrecomposeData.bridge` obligation verbatim.

**§3 — end to end.** The composite `certDecode ;; evalCnfCmd` accepts `(N,c)`
iff `satisfiesCnf (decodeBits c) N`, on satisfying, non-satisfying and
garbage/short/over-long certificates.

**§4 — completeness of the certificate relation.** The pure obligation
`polyCertRel SAT rel`: for a satisfiable `N`, the canonical certificate
`satCert N a = (List.range (size N)).map (· ∈ a)` decodes to an assignment that
still satisfies `N`, and its size is bounded by `size N`.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/SATSplitProbe.lean` -/

namespace SATSplitProbe

open Complexity.Lang

/-! ## Under test — the PINNED library definitions

The probe deliberately imports `EvalCnfSplit` rather than re-declaring the
program: a drifted copy would validate nothing. Every name below is the one the
proof depends on.
-/

open EvalCnfSplit (bitsToAssgn decodeBits satCert satEncX satEIn
  DCUR DIDX DHD decodeBody certDecode decRegs cbits loopStart)

/-! ## §1 — the layout gap is exactly one register -/

/-- `satEIn (N,c)` agrees with `encodeState (N, a)` on `[0,16) \ {ASSGN}`, for
every `a`: the trailing-scratch mismatch is invisible to `State.get`. -/
def checkLayout (N : cnf) (c : List Bool) (a : assgn) : Bool :=
  (List.range 16).all (fun r =>
    r == EvalCnfCmd.ASSGN ||
      State.get (satEIn (N, c)) r == State.get (EvalCnfCmd.encodeState (N, a)) r)

/-- ... and register 3 of `satEIn` is exactly the raw bit list. -/
def checkCertReg (N : cnf) (c : List Bool) : Bool :=
  State.get (satEIn (N, c)) EvalCnfCmd.ASSGN
    == c.map (fun b => if b then 1 else 0)

/-- `xWidth = 3` for every `N`. -/
def checkWidth (N : cnf) : Bool := (satEncX N).length == 3

/-! ## §2 — the bridge obligation -/

/-- `FreePrecomposeData.bridge`, verbatim. -/
def checkBridge (N : cnf) (c : List Bool) : Bool :=
  let s := certDecode.eval (satEIn (N, c))
  (List.range 16).all (fun r =>
    State.get s r == State.get (EvalCnfCmd.encodeState (N, decodeBits c)) r)

/-- The decoder's own model, register by register (what the bottom-up `_run`
lemma will have to state): `ASSGN = encodeAssgn (decodeBits c)`, cursor drained.
-/
def checkDecodeModel (N : cnf) (c : List Bool) : Bool :=
  let s := certDecode.eval (satEIn (N, c))
  (State.get s EvalCnfCmd.ASSGN == EvalCnfCmd.encodeAssgn (decodeBits c))
    && (State.get s DCUR == [])

/-! ## §3 — end to end -/

/-- The composite decides `fun (N,c) => satisfiesCnf (decodeBits c) N`. -/
def checkE2E (N : cnf) (c : List Bool) : Bool :=
  let s := EvalCnfCmd.evalCnfCmd.eval (certDecode.eval (satEIn (N, c)))
  (State.get s 0 == if evalCnf (decodeBits c) N then [1] else [0])

/-! ## §4 — the certificate relation -/

/-- Completeness: the canonical certificate of a satisfying assignment decodes
to an assignment that still satisfies `N`. -/
def checkComplete (N : cnf) (a : assgn) : Bool :=
  !(evalCnf a N) || evalCnf (decodeBits (satCert N a)) N

/-- The certificate size bound: `encodable.size (satCert N a) ≤ 2 * size N`. -/
def checkCertSize (N : cnf) (a : assgn) : Bool :=
  decide (encodable.size (satCert N a) ≤ 2 * encodable.size N)

/-! ## §5 — the loop invariant, prefix by prefix

This is the invariant `EvalCnfSplit.certDecode_decodesAssgn` feeds to
`Cmd.foldlState_range_induct`, checked at EVERY `i ≤ |c|`. It was written
*before* the proof and is what made the proof mechanical; it is kept as a
regression on `decodeBody`, on `certDecode`'s prologue and on the trip count.

```
ASSGN = encodeAssgn (decodeBits (c.take i))     DCUR = cbits (c.drop i)
registers 0-2 untouched                        registers 4-15 still []
```

`prefState i` is `certDecode`'s state after the loop's first `i` iterations,
built exactly as `Cmd.eval_forBnd` unfolds it. ⚠ `loopStart` and `cbits` are the
**library's** (`EvalCnfSplit.loopStart` / `.cbits`, opened above) — a drifted
copy here would validate nothing. -/

/-- The state after the loop's first `i` iterations. -/
def prefState (N : cnf) (c : List Bool) (i : Nat) : State :=
  Cmd.foldlState decodeBody DIDX (List.range i) (loopStart N c)

def checkInv (N : cnf) (c : List Bool) (i : Nat) : Bool :=
  let s := prefState N c i
  (State.get s EvalCnfCmd.ASSGN
      == EvalCnfCmd.encodeAssgn (decodeBits (c.take i)))
    && (State.get s DCUR == cbits (c.drop i))
    && (List.range 3).all (fun r => State.get s r == State.get (satEIn (N, c)) r)
    && ((List.range 16).drop 4).all (fun r => State.get s r == [])

/-- The invariant at every prefix length, plus the fact that the loop's trip
count really is `|c|` (`forBnd` samples `DCUR` once at entry). -/
def checkInvAll (N : cnf) (c : List Bool) : Bool :=
  (List.range (c.length + 1)).all (checkInv N c)
    && (State.get (loopStart N c) DCUR).length == c.length
    && (prefState N c c.length == certDecode.eval (satEIn (N, c)))

/-! ## Instances

`N1` is satisfiable, `N2` is a contradiction, `N3` is empty (trivially SAT),
`N4` has a clause with no literals (unsatisfiable), `N5` uses a variable index
larger than the clause count (checks that `xWidth` really is `|N|`-independent).
-/

def N1 : cnf := [[(true, 0), (false, 1)], [(true, 1)]]
def N2 : cnf := [[(true, 0)], [(false, 0)]]
def N3 : cnf := []
def N4 : cnf := [[]]
def N5 : cnf := [[(true, 4)], [(false, 2), (true, 4)]]

/-- Certificates: correct, wrong, empty, over-long (trailing junk beyond every
variable of `N`), all-true, all-false. -/
def certs : List (List Bool) :=
  [ [], [true], [false], [true, true], [true, false], [false, true]
  , [false, true, true], [true, true, true, true, true]
  , [false, false, false, false, true], [true, false, true, false, true] ]

def assgns : List assgn := [[], [0], [1], [0, 1], [4], [2, 4], [0, 1, 2, 4]]

def cnfs : List cnf := [N1, N2, N3, N4, N5]

/-! ### §1 -/
#eval cnfs.all checkWidth
#eval cnfs.all (fun N => certs.all (fun c => assgns.all (checkLayout N c)))
#eval cnfs.all (fun N => certs.all (checkCertReg N))

/-! ### §2 -/
#eval cnfs.all (fun N => certs.all (checkDecodeModel N))
#eval cnfs.all (fun N => certs.all (checkBridge N))

/-! ### §3 -/
#eval cnfs.all (fun N => certs.all (checkE2E N))

/-! ### §5 -/
#eval cnfs.all (fun N => certs.all (checkInvAll N))

/-! ### §4 -/
#eval cnfs.all (fun N => assgns.all (checkComplete N))
#eval cnfs.all (fun N => assgns.all (checkCertSize N))

/-! ### Diagnostics — the numbers the design depends on -/
#eval (satEncX N1).length                                   -- xWidth
#eval State.size (satEncX N5)                               -- encX_size's LHS
#eval encodable.size N5                                     -- ... vs size N
#eval certDecode.cost (satEIn (N1, [true, false, true]))     -- decoder cost
#eval (certDecode.eval (satEIn (N1, [true, false, true]))).length
#eval certDecode.loopDepth
#eval encodable.size (decodeBits [true, true, true, true, true])  -- |decode| ≤ |c|²

/-! ### Everything at once -/
#eval cnfs.all checkWidth
  && cnfs.all (fun N => certs.all (fun c => assgns.all (checkLayout N c)))
  && cnfs.all (fun N => certs.all (checkCertReg N))
  && cnfs.all (fun N => certs.all (checkDecodeModel N))
  && cnfs.all (fun N => certs.all (checkBridge N))
  && cnfs.all (fun N => certs.all (checkE2E N))
  && cnfs.all (fun N => certs.all (checkInvAll N))
  && cnfs.all (fun N => assgns.all (checkComplete N))
  && cnfs.all (fun N => assgns.all (checkCertSize N))

end SATSplitProbe
