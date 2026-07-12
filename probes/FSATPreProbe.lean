import Complexity.NP.SAT.CookLevin.Reductions.FSAT_to_SAT_free

open Complexity.Lang

/-! # `FSAT → SAT` free-witness design probe (top-down, 2026-07-12)

GO/NO-GO for the HANDOFF's ⚠ tree-recursion design risk: the reduction must
*traverse* a formula tree, but the machine input is the Polish `serF` stream
and the DSL has only counted `forBnd` loops. This probes **design (a)** —
positional-index Tseytin, no stack:

* the map is `PreTseytin.preTseytin b f` (pre-order positional Tseytin over the
  FULL grammar — `tseytinOr` handles `forr`, no `eliminateOR` pass), with the
  machine-friendly base `b := (serF f).length`;
* a node's variable is `b + (pre-order token index)`; the right child of a
  binary node at index `k` sits at `k + 1 + t` where `t` = token count of the
  first complete subtree of the remaining stream — recovered by the
  **arity-budget scan** (budget 1; leaf −1, binary +1, `fneg` 0; stop at 0).

Three checks, all `#eval` → expect `true`:

1. `checkScan` — a PURE positional-scan model (`mScan`, mirroring the machine
   loop bit-for-bit: single forward token scan + budget scan for right-child
   indices) reproduces the tree-recursive `preTseytin (serF f).length f`
   exactly, on a diverse formula battery. Validates the positional design and
   the emission ORDER (gadget-before-children = flat scan order).
2. `checkSat` — brute-force `FSAT f ↔ SAT (preTseytin b f)` on small formulas
   (all assignments over the clauses' var range), for both `b = maxVar+1` and
   the witness's `b = |serF f|`. Validates the MATH before the repr proof.
3. `checkCmd` — the REAL `Cmd` (`FSATSATFree.buildSAT`) on `[serF f]` writes
   exactly `encodeCnf (preTseytin (serF f).length f)` into `CNFOUT` and
   `replicate |N| 1` into `TALLY`. Validates DSL expressibility end-to-end
   (tokenizer, budget scan, unary var arithmetic, clause emission).

**VERDICT (recorded in HANDOFF): GO** — all three checks green. -/

namespace FSATPreProbe

open PreTseytin
open FSATSATFree
open BinaryCCFSATFree (serF readUnary)
open EvalCnfCmd (encodeCnf)

/-! ## 1. The pure positional-scan model (the machine loop, bit-for-bit) -/

/-- One budget-scan step over `(bits, budget, tokens)`. -/
def budgetStep : List Nat × Nat × Nat → List Nat × Nat × Nat
  | (bits, bud, t) =>
    if bud = 0 then (bits, bud, t) else
    match bits with
    | 0 :: 0 :: r => (r, bud - 1, t + 1)             -- ftrue: leaf
    | 0 :: 1 :: r => (r, bud + 1, t + 1)             -- fand: binary
    | 1 :: 0 :: r => (r, bud + 1, t + 1)             -- forr: binary
    | 1 :: 1 :: 0 :: r => (r, bud, t + 1)            -- fneg: unary
    | 1 :: 1 :: 1 :: r => ((readUnary r).2, bud - 1, t + 1)  -- fvar: leaf
    | _ => (bits, 0, t)

/-- Token count of the first complete subtree of `bits` (arity-budget scan,
`|bits|` iterations — the machine's `subtreeScan`). -/
def subtreeTok (bits : List Nat) : Nat :=
  ((List.range bits.length).foldl (fun st _ => budgetStep st) (bits, 1, 0)).2.2

/-- The positional clause emitter: scan tokens left to right, emit each node's
gadget at its token position (the machine's outer loop). -/
def scanClauses (b : Nat) : Nat → Nat → List Nat → cnf
  | 0, _, _ => []
  | fuel + 1, k, bits =>
    match bits with
    | 0 :: 0 :: r => tseytinTrue (b + k) ++ scanClauses b fuel (k + 1) r
    | 0 :: 1 :: r =>
        tseytinAnd (b + k) (b + k + 1) (b + k + 1 + subtreeTok r) ++
          scanClauses b fuel (k + 1) r
    | 1 :: 0 :: r =>
        tseytinOr (b + k) (b + k + 1) (b + k + 1 + subtreeTok r) ++
          scanClauses b fuel (k + 1) r
    | 1 :: 1 :: 0 :: r => tseytinNot (b + k) (b + k + 1) ++ scanClauses b fuel (k + 1) r
    | 1 :: 1 :: 1 :: r =>
        let (v, r') := readUnary r
        tseytinEquiv v (b + k) ++ scanClauses b fuel (k + 1) r'
    | _ => []

/-- The full scan model of the map (`b := |bits|`, top clause first). -/
def mScan (bits : List Nat) : cnf :=
  [(true, bits.length), (true, bits.length), (true, bits.length)] ::
    scanClauses bits.length (bits.length + 1) 0 bits

/-! ## The formula battery -/

def f1 : formula := .ftrue
def f2 : formula := .fvar 3
def f3 : formula := .fand (.fvar 0) (.fvar 1)
def f4 : formula := .forr (.fneg (.fvar 2)) .ftrue
def f5 : formula := .fneg (.forr (.fand (.fvar 0) (.fneg (.fvar 1))) (.forr .ftrue (.fvar 5)))
def f6 : formula := .fand (.fand (.fvar 2) (.fvar 2)) (.forr (.fvar 0) (.fand .ftrue (.fneg (.fvar 7))))
def f7 : formula := .fneg (.fneg (.fneg (.fvar 0)))
def f8 : formula := .fand (.fand (.fand (.fvar 0) (.fvar 1)) (.fvar 2)) (.fvar 3)
def f9 : formula := .forr (.fvar 0) (.forr (.fvar 1) (.forr (.fvar 2) (.fvar 3)))
def f10 : formula := .fvar 0
def f11 : formula := .forr (.fand (.fvar 1) (.fneg (.fvar 1))) (.fneg .ftrue)  -- UNSAT
def f12 : formula := .fneg .ftrue                                              -- UNSAT
def f13 : formula := .fand (.fvar 0) (.fneg (.fvar 0))                         -- UNSAT

def battery : List formula := [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13]

/-! ## Check 1: scan model ≡ tree recursion -/

def checkScan : Bool :=
  battery.all (fun f => mScan (serF f) == preTseytin (serF f).length f)

#eval checkScan  -- expect true

/-! ## Check 2: brute-force sat-equivalence (small formulas) -/

def fsatB (f : formula) : Bool :=
  (allAssignments (formula_maxVar f + 1)).any (fun a => evalFormula a f)

def satB (N : cnf) (nv : Nat) : Bool :=
  (allAssignments nv).any (fun a => evalCnf a N)

/-- `FSAT f ↔ SAT (preTseytin b f)` brute-forced over `b + formula_size f`
variables (every clause var is below that). -/
def satEquivAt (b : Nat) (f : formula) : Bool :=
  fsatB f == satB (preTseytin b f) (b + formula_size f)

-- small formulas at the tight base b = maxVar+1 (keeps the var range small)
def checkSat : Bool :=
  [f1, f3, f4, f7, f10, f12, f13].all (fun f => satEquivAt (formula_maxVar f + 1) f)
  -- and the witness's base b = |serF f| on the tiniest ones
  && [f1, f10, f12].all (fun f => satEquivAt (serF f).length f)

#eval checkSat  -- expect true

/-! ## Check 3: the real `Cmd`, end-to-end -/

def checkCmdOne (f : formula) : Bool :=
  let s := buildSAT.eval [serF f]
  let N := preTseytin (serF f).length f
  State.get s CNFOUT == encodeCnf N
    && State.get s TALLY == List.replicate N.length 1
    && State.get s SERF == serF f  -- the input register is preserved

def checkCmd : Bool := battery.all checkCmdOne

#eval checkCmd  -- expect true

#eval [checkScan, checkSat, checkCmd]  -- expect [true, true, true]

end FSATPreProbe
