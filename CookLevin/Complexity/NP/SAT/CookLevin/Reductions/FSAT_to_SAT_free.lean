import Complexity.NP.FSAT_to_SAT_pre
import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_free
import Complexity.Complexity.Deciders.EvalCnfCmd

set_option autoImplicit false

/-! # `FSAT → SAT` as a free `PolyTimeComputableLang` witness — the program

The LAST sound-tail reduction (HANDOFF "NEXT TOP-DOWN"). The map is the
machine-friendly **pre-order positional Tseytin** `PreTseytin.preTseytin b f`
with `b := (serF f).length` (`Complexity/NP/FSAT_to_SAT_pre.lean` — design (a)
of the HANDOFF brief, probed GO in `probes/FSATPreProbe.lean`).

**Input layout (pinned to the composite tail exit frame, HANDOFF):**
`encodeIn f = [serF f]` — register 0 (= the predecessor's `FOUT`) holds the
Polish bit-serialization of the formula, everything else `[]`. Every `formula`
is a valid instance, so the map is UNGUARDED (`FlatTCC_to_FlatCC_free` pattern).

**Output layout (the SAT verifier's stream layout, `EvalCnfCmd.encodeState`
registers 1/2):** `TALLY` (reg 1) = `replicate |N| 1`, `CNFOUT` (reg 2) =
`encodeCnf N` where `N = preTseytin (serF f).length f`. `decodeOut` inverts the
injective `encodeCnf` on reg 2 (`Function.invFun`, the `kSAT3_reductionLang`
pattern). Honesty: input/output layouts are the natural ones; ALL reduction
work happens in the `Cmd` below.

**The algorithm** (one forward scan, no stack — the Polish stream is the
pre-order token sequence):

* Phase 0: `B := 1^(serF f).length` (the fresh-var base, one length loop);
  emit the top clause `[(true, b)]×3`.
* Outer loop (one iteration per *bit* of the input, idling once the scan is
  exhausted — tokens ≤ bits): consume one token off `SCAN`, dispatch on its
  tag, emit the node's gadget clauses with variables `VA = 1^(b+k)`,
  `VL = 1^(b+k+1)` (`k` = token index, maintained in `K`), and for the two
  binary tags compute the right child's index `k+1+t` via the **arity-budget
  scan** (`subtreeScan`): `t` = token count of the first complete subtree of
  the remaining stream, found by scanning a copy with a unary budget register
  (start 1; leaf −1, binary +1, `fneg` 0; stop at 0).

This file is pure `Cmd`/`State` DATA plus the witness-layout definitions —
`#eval`-validated end-to-end in `probes/FSATPreProbe.lean` (`checkCmd`) against
`encodeCnf (preTseytin (serF f).length f)`. The run/cost lemmas and the
`PolyTimeComputableLang`/seam instances are the next sessions' work (see
HANDOFF "NEXT TOP-DOWN"). -/

namespace FSATSATFree

open Complexity.Lang
open PreTseytin
open BinaryCCFSATFree (serF)
open EvalCnfCmd (encodeCnf encodeClause encodeLit)

/-! ## Register layout -/

/-- Input: the Polish serialization `serF f` (the predecessor's `FOUT`). -/
def SERF   : Var := 0
/-- Output: `replicate |N| 1` — the SAT verifier's `CLAUSE_TALLY` register. -/
def TALLY  : Var := 1
/-- Output: `encodeCnf N` — the SAT verifier's `CNF_STREAM` register. -/
def CNFOUT : Var := 2
-- Scratch (all cleared-on-entry semantics not required; the program writes
-- before reading each):
def B      : Var := 3   -- 1^b, the fresh-var base (b = |serF f|)
def K      : Var := 4   -- 1^k, current token index
def SCAN   : Var := 5   -- remaining input stream (consumed token by token)
def H1     : Var := 6   -- tag bit 1
def H2     : Var := 7   -- tag bit 2
def H3     : Var := 8   -- tag bit 3 / drain head scratch
def VA     : Var := 9   -- 1^(b+k)   (this node's variable)
def VL     : Var := 10  -- 1^(b+k+1) (left child's variable)
def VR     : Var := 11  -- 1^(b+k+1+t) (right child's variable)
def VREG   : Var := 12  -- 1^v (an fvar leaf's original variable)
def DN     : Var := 13  -- drain-done flag (outer fvar drain)
def SC2    : Var := 14  -- budget-scan stream copy
def BUD    : Var := 15  -- budget (unary; scan stops when empty)
def T      : Var := 16  -- 1^t, token count of the first subtree of SCAN
def NE     : Var := 17  -- outer nonEmpty guard scratch
def SKIP   : Var := 18  -- no-op target
def IDX0   : Var := 19  -- phase-0 loop counter
def IDX1   : Var := 20  -- outer loop counter
def IDX2   : Var := 21  -- budget loop counter
def IDX3   : Var := 22  -- drain loop counter (outer fvar drain + budget drain)
def H1B    : Var := 23  -- budget-scan tag bit 1
def H2B    : Var := 24  -- budget-scan tag bit 2
def NEB    : Var := 25  -- budget nonEmpty guard scratch
def DN2    : Var := 26  -- budget drain-done flag

/-- The register frame: the program touches only registers `< 27`. -/
def FRAME : Nat := 27

/-- One-op no-op (the idle branch of guarded loops). -/
def nop : Cmd := Cmd.op (.clear SKIP)

/-! ## Emission helpers -/

/-- Append `encodeLit (pol, v)` (`1 :: polBit :: 1^v ++ [0]`) to `CNFOUT`,
reading the variable's unary from register `v`. -/
def emitLit (pol : Bool) (v : Var) : Cmd :=
  Cmd.op (.appendOne CNFOUT) ;;
  Cmd.op (if pol then .appendOne CNFOUT else .appendZero CNFOUT) ;;
  Cmd.op (.concat CNFOUT CNFOUT v) ;;
  Cmd.op (.appendZero CNFOUT)

/-- Close the current clause (`0` end marker) and grow the tally. -/
def endClause : Cmd :=
  Cmd.op (.appendZero CNFOUT) ;; Cmd.op (.appendOne TALLY)

/-- `tseytinTrue (b+k)` — vars from `VA`. -/
def emitTrueG : Cmd :=
  emitLit true VA ;; emitLit true VA ;; emitLit true VA ;; endClause

/-- `tseytinEquiv v (b+k)` — vars from `VREG`/`VA`. -/
def emitEquivG : Cmd :=
  emitLit false VREG ;; emitLit true VA ;; emitLit true VA ;; endClause ;;
  emitLit false VA ;; emitLit true VREG ;; emitLit true VREG ;; endClause

/-- `tseytinAnd (b+k) (b+k+1) (b+k+1+t)` — vars from `VA`/`VL`/`VR`. -/
def emitAndG : Cmd :=
  emitLit false VA ;; emitLit true VL ;; emitLit true VL ;; endClause ;;
  emitLit false VA ;; emitLit true VR ;; emitLit true VR ;; endClause ;;
  emitLit false VL ;; emitLit false VR ;; emitLit true VA ;; endClause

/-- `tseytinOr (b+k) (b+k+1) (b+k+1+t)` — vars from `VA`/`VL`/`VR`. -/
def emitOrG : Cmd :=
  emitLit false VA ;; emitLit true VL ;; emitLit true VR ;; endClause ;;
  emitLit false VL ;; emitLit true VA ;; emitLit true VA ;; endClause ;;
  emitLit false VR ;; emitLit true VA ;; emitLit true VA ;; endClause

/-- `tseytinNot (b+k) (b+k+1)` — vars from `VA`/`VL`. -/
def emitNotG : Cmd :=
  emitLit false VA ;; emitLit false VL ;; emitLit false VL ;; endClause ;;
  emitLit true VA ;; emitLit true VL ;; emitLit true VL ;; endClause

/-! ## The arity-budget scan (right-child index recovery) -/

/-- Skip one unary block through its `0` terminator off `SC2`
(an fvar token's payload inside the budget scan). `DN2` must be `[]` at entry. -/
def drainSkipBody : Cmd :=
  Cmd.ifBit DN2 nop
    (Cmd.op (.head H3 SC2) ;; Cmd.op (.tail SC2 SC2) ;;
     Cmd.ifBit H3 nop (Cmd.op (.clear DN2) ;; Cmd.op (.appendOne DN2)))

/-- The budget-scan body once the `nonEmpty NEB BUD` guard has fired: consume
one token off `SC2`, count it in `T`, adjust `BUD` by the token's arity − 1
(factored out so the run lemmas can name it — the `budgetBody_enter` peel). -/
def budgetBodyInner : Cmd :=
  Cmd.op (.head H1B SC2) ;; Cmd.op (.tail SC2 SC2) ;;
  Cmd.op (.head H2B SC2) ;; Cmd.op (.tail SC2 SC2) ;;
  Cmd.op (.appendOne T) ;;
  Cmd.ifBit H1B
    (Cmd.ifBit H2B
       (-- 11x: read the third bit
        Cmd.op (.head H2B SC2) ;; Cmd.op (.tail SC2 SC2) ;;
        Cmd.ifBit H2B
          (-- 111 fvar: skip the unary payload; leaf ⇒ budget −1
           Cmd.op (.clear DN2) ;;
           Cmd.forBnd IDX3 SC2 drainSkipBody ;;
           Cmd.op (.tail BUD BUD))
          (-- 110 fneg: arity 1 ⇒ budget unchanged
           nop))
       (-- 10 forr: arity 2 ⇒ budget +1
        Cmd.op (.appendOne BUD)))
    (Cmd.ifBit H2B
       (-- 01 fand: arity 2 ⇒ budget +1
        Cmd.op (.appendOne BUD))
       (-- 00 ftrue: leaf ⇒ budget −1
        Cmd.op (.tail BUD BUD)))

/-- One budget-scan step: if the budget is non-empty, run `budgetBodyInner`. -/
def budgetBody : Cmd :=
  Cmd.op (.nonEmpty NEB BUD) ;; Cmd.ifBit NEB budgetBodyInner nop

/-- `T := 1^(token count of the first complete subtree of SCAN)`; `SCAN` is
read through a copy (`SC2`) and left untouched. The loop bound `SCAN` (its
remaining bit length) dominates the subtree's token count. -/
def subtreeScan : Cmd :=
  Cmd.op (.copy SC2 SCAN) ;;
  Cmd.op (.clear BUD) ;; Cmd.op (.appendOne BUD) ;;
  Cmd.op (.clear T) ;;
  Cmd.forBnd IDX2 SCAN budgetBody

/-! ## The outer token loop -/

/-- Drain the current fvar token's unary payload off `SCAN` into `VREG`
(through the `0` terminator). `VREG`/`DN` must be `[]` at entry. -/
def drainVarBody : Cmd :=
  Cmd.ifBit DN nop
    (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
     Cmd.ifBit H3 (Cmd.op (.appendOne VREG))
       (Cmd.op (.clear DN) ;; Cmd.op (.appendOne DN)))

/-- Process one token: compute this node's variables, dispatch on the tag,
emit the gadget, advance `K`. Idles once `SCAN` is exhausted. -/
def tokenBody : Cmd :=
  Cmd.op (.nonEmpty NE SCAN) ;;
  Cmd.ifBit NE
    (Cmd.op (.concat VA B K) ;;
     Cmd.op (.copy VL VA) ;; Cmd.op (.appendOne VL) ;;
     Cmd.op (.head H1 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
     Cmd.op (.head H2 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
     Cmd.ifBit H1
       (Cmd.ifBit H2
          (-- 11x: read the third bit
           Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
           Cmd.ifBit H3
             (-- 111 fvar v: drain 1^v ++ [0] into VREG, emit the equiv gadget
              Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
              Cmd.forBnd IDX3 SCAN drainVarBody ;;
              emitEquivG)
             (-- 110 fneg: child at k+1
              emitNotG))
          (-- 10 forr: right child at k+1+t
           subtreeScan ;;
           Cmd.op (.concat VR VL T) ;;
           emitOrG))
       (Cmd.ifBit H2
          (-- 01 fand: right child at k+1+t
           subtreeScan ;;
           Cmd.op (.concat VR VL T) ;;
           emitAndG)
          (-- 00 ftrue
           emitTrueG)) ;;
     Cmd.op (.appendOne K))
    nop

/-- **The reduction program.** From `[serF f]`, computes the SAT verifier's
stream layout of `preTseytin (serF f).length f` into `TALLY`/`CNFOUT`. -/
def buildSAT : Cmd :=
  Cmd.op (.clear B) ;;
  Cmd.forBnd IDX0 SERF (Cmd.op (.appendOne B)) ;;
  Cmd.op (.copy SCAN SERF) ;;
  Cmd.op (.clear K) ;;
  Cmd.op (.clear TALLY) ;; Cmd.op (.clear CNFOUT) ;;
  Cmd.op (.copy VA B) ;;
  emitLit true VA ;; emitLit true VA ;; emitLit true VA ;; endClause ;;
  Cmd.forBnd IDX1 SERF tokenBody

/-! ## The witness-layout definitions (the pinned seam contract) -/

/-- The pinned input layout: the composite tail witness's exit frame after the
scrub — `FOUT` (reg 0) holds `serF f`, everything else `[]`. -/
def encodeIn (f : formula) : State := [serF f]

/-- Decode the output cnf from the verifier-layout stream register
(`Function.invFun` of the injective `encodeCnf` — the `kSAT3_reductionLang`
pattern; `KSat3Free.encodeCnf_injective`). -/
noncomputable def decodeOut (s : State) : cnf :=
  Function.invFun encodeCnf (State.get s CNFOUT)

/-- The map the witness computes. -/
def fsatToSat (f : formula) : cnf := preTseytin (serF f).length f

/-- The machine-friendly fresh-variable base is valid: every original variable
is below the serialization length (an `fvar v` token alone carries `v + 4`
bits). This is what replaces the on-machine max computation. -/
theorem formula_maxVar_lt_serF_length (f : formula) :
    formula_maxVar f < (serF f).length := by
  -- NB: `omega`-hostile terrain — the `fvar` payload is `var`-typed (carrier
  -- opaque to omega) and `formula_maxVar` is a `Nat.max` (an omega atom), so
  -- the leaf/max steps are closed by term lemmas (HANDOFF `Var := Nat` gotcha)
  induction f with
  | ftrue => simp [BinaryCCFSATFree.serF, formula_maxVar]
  | fvar v =>
      simp only [BinaryCCFSATFree.serF, formula_maxVar, List.length_append,
        List.length_cons, List.length_replicate, List.length_nil]
      exact Nat.lt_succ_of_le (Nat.le_add_left v 3)
  | fand f₁ f₂ ih₁ ih₂ =>
      simp only [BinaryCCFSATFree.serF, formula_maxVar, List.length_append,
        List.length_cons]
      exact Nat.max_lt.mpr ⟨by omega, by omega⟩
  | forr f₁ f₂ ih₁ ih₂ =>
      simp only [BinaryCCFSATFree.serF, formula_maxVar, List.length_append,
        List.length_cons]
      exact Nat.max_lt.mpr ⟨by omega, by omega⟩
  | fneg f₁ ih =>
      simp only [BinaryCCFSATFree.serF, formula_maxVar, List.length_append,
        List.length_cons]
      omega

/-- **The chain-step correctness**: the map the machine computes is a correct
`FSAT → SAT` reduction (axiom-clean; the `⪯p'` witness's `correct` field). -/
theorem fsatToSat_correct (f : formula) : FSAT f ↔ SAT (fsatToSat f) :=
  preTseytin_correct f _ (formula_maxVar_lt_serF_length f)

/-! ## The pure positional-scan model (promoted from `probes/FSATPreProbe.lean`)

The machine's outer token loop and budget scan, as pure Lean functions — the
run-lemma blueprint (HANDOFF "NEXT TOP-DOWN" step 1(i)). These mirror the `Cmd`
loops (`tokenBody`/`budgetBody`) bit-for-bit, so the eventual machine ↔ model
reduction (step 1(ii)) black-boxes the tree recursion entirely: it need only
prove the machine folds compute these functions, then `mScan_eq_fsatToSat`
closes the gap. The probe only `#eval`-validated the equivalence; here it is a
THEOREM (`mScan_eq_fsatToSat`), axiom-clean. -/

open BinaryCCFSATFree (readUnary readUnary_replicate formula_size_le_serF)

/-- One budget-scan step over `(bits, budget, tokens)` — the machine's
`budgetBody`. Freezes once the budget hits `0`. -/
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
gadget at its token position (the machine's `tokenBody` outer loop). -/
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

/-! ### The budget scan ≡ `formula_size` (right-child index recovery) -/

theorem budgetStep_ftrue (r : List Nat) (bud t : Nat) (h : bud ≠ 0) :
    budgetStep (0 :: 0 :: r, bud, t) = (r, bud - 1, t + 1) := by
  simp only [budgetStep, if_neg h]

theorem budgetStep_fand (r : List Nat) (bud t : Nat) (h : bud ≠ 0) :
    budgetStep (0 :: 1 :: r, bud, t) = (r, bud + 1, t + 1) := by
  simp only [budgetStep, if_neg h]

theorem budgetStep_forr (r : List Nat) (bud t : Nat) (h : bud ≠ 0) :
    budgetStep (1 :: 0 :: r, bud, t) = (r, bud + 1, t + 1) := by
  simp only [budgetStep, if_neg h]

theorem budgetStep_fneg (r : List Nat) (bud t : Nat) (h : bud ≠ 0) :
    budgetStep (1 :: 1 :: 0 :: r, bud, t) = (r, bud, t + 1) := by
  simp only [budgetStep, if_neg h]

theorem budgetStep_fvar (r : List Nat) (bud t : Nat) (h : bud ≠ 0) :
    budgetStep (1 :: 1 :: 1 :: r, bud, t) = ((readUnary r).2, bud - 1, t + 1) := by
  simp only [budgetStep, if_neg h]

theorem budgetStep_freeze (bits : List Nat) (t : Nat) :
    budgetStep (bits, 0, t) = (bits, 0, t) := by
  simp [budgetStep]

theorem budgetStep_iterate_freeze (m : Nat) (bits : List Nat) (t : Nat) :
    budgetStep^[m] (bits, 0, t) = (bits, 0, t) := by
  induction m with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, budgetStep_freeze, ih]

/-- **The core budget-scan invariant.** Processing exactly the `formula_size g`
tokens of `serF g` (with a positive budget) consumes the subtree `g`, pays off
one budget obligation, and adds `formula_size g` to the token count. -/
theorem budgetStep_iterate_subtree (g : formula) :
    ∀ (rest : List Nat) (bud t : Nat),
      budgetStep^[formula_size g] (serF g ++ rest, bud + 1, t)
        = (rest, bud, t + formula_size g) := by
  induction g with
  | ftrue =>
      intro rest bud t
      rw [formula_size, Function.iterate_one]
      show budgetStep (0 :: 0 :: rest, bud + 1, t) = _
      rw [budgetStep_ftrue rest (bud + 1) t (by omega)]
      simp
  | fvar v =>
      intro rest bud t
      rw [formula_size, Function.iterate_one]
      have hr : serF (formula.fvar v) ++ rest
          = 1 :: 1 :: 1 :: (List.replicate v 1 ++ (0 :: rest)) := by
        simp [BinaryCCFSATFree.serF]
      rw [hr, budgetStep_fvar _ (bud + 1) t (by omega), readUnary_replicate]
      simp
  | fand a b iha ihb =>
      intro rest bud t
      simp only [formula_size]
      rw [Function.iterate_succ_apply]
      show budgetStep^[formula_size a + formula_size b]
            (budgetStep (0 :: 1 :: ((serF a ++ serF b) ++ rest), bud + 1, t)) = _
      rw [budgetStep_fand _ (bud + 1) t (by omega), List.append_assoc,
          Nat.add_comm (formula_size a) (formula_size b), Function.iterate_add_apply,
          iha (serF b ++ rest) (bud + 1) (t + 1),
          ihb rest bud (t + 1 + formula_size a)]
      have : t + 1 + formula_size a + formula_size b
          = t + (formula_size b + formula_size a + 1) := by omega
      rw [this]
  | forr a b iha ihb =>
      intro rest bud t
      simp only [formula_size]
      rw [Function.iterate_succ_apply]
      show budgetStep^[formula_size a + formula_size b]
            (budgetStep (1 :: 0 :: ((serF a ++ serF b) ++ rest), bud + 1, t)) = _
      rw [budgetStep_forr _ (bud + 1) t (by omega), List.append_assoc,
          Nat.add_comm (formula_size a) (formula_size b), Function.iterate_add_apply,
          iha (serF b ++ rest) (bud + 1) (t + 1),
          ihb rest bud (t + 1 + formula_size a)]
      have : t + 1 + formula_size a + formula_size b
          = t + (formula_size b + formula_size a + 1) := by omega
      rw [this]
  | fneg a iha =>
      intro rest bud t
      simp only [formula_size]
      rw [Function.iterate_succ_apply]
      show budgetStep^[formula_size a]
            (budgetStep (1 :: 1 :: 0 :: (serF a ++ rest), bud + 1, t)) = _
      rw [budgetStep_fneg _ (bud + 1) t (by omega), iha rest bud (t + 1)]
      have : t + 1 + formula_size a = t + (formula_size a + 1) := by omega
      rw [this]

theorem foldl_range_budgetStep (n : Nat) (init : List Nat × Nat × Nat) :
    (List.range n).foldl (fun st _ => budgetStep st) init = budgetStep^[n] init := by
  induction n generalizing init with
  | zero => rfl
  | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih]
      show budgetStep (budgetStep^[m] init) = budgetStep^[m + 1] init
      rw [Function.iterate_succ_apply']

/-- **Lemma A**: the arity-budget scan of `serF g ++ rest` recovers exactly the
token count `formula_size g` of the first subtree. -/
theorem subtreeTok_serF (g : formula) (rest : List Nat) :
    subtreeTok (serF g ++ rest) = formula_size g := by
  have key : budgetStep^[formula_size g] (serF g ++ rest, 1, 0)
      = (rest, 0, formula_size g) := by
    simpa using budgetStep_iterate_subtree g rest 0 0
  unfold subtreeTok
  rw [foldl_range_budgetStep]
  obtain ⟨m, hm⟩ : ∃ m, (serF g ++ rest).length = m + formula_size g := by
    have h1 := formula_size_le_serF g
    rw [List.length_append]
    exact ⟨(serF g).length - formula_size g + rest.length, by omega⟩
  rw [hm, Function.iterate_add_apply, key, budgetStep_iterate_freeze]

/-! ### The scan emitter ≡ the tree recursion -/

theorem scanClauses_nil (b fuel k : Nat) : scanClauses b fuel k [] = [] := by
  cases fuel <;> simp [scanClauses]

/-- **Lemma B**: scanning `serF f ++ rest` emits exactly `ptseytin (b+k) f`,
then continues on `rest` with the token counter advanced by `formula_size f`. -/
theorem scanClauses_serF (b : Nat) (f : formula) :
    ∀ (fuel k : Nat) (rest : List Nat), formula_size f ≤ fuel →
      scanClauses b fuel k (serF f ++ rest) =
        ptseytin (b + k) f ++
          scanClauses b (fuel - formula_size f) (k + formula_size f) rest := by
  induction f with
  | ftrue =>
      intro fuel k rest h
      obtain ⟨fuel', rfl⟩ : ∃ m, fuel = m + 1 :=
        ⟨fuel - 1, by simp only [formula_size] at h; omega⟩
      show scanClauses b (fuel' + 1) k (0 :: 0 :: rest) = _
      simp only [scanClauses, ptseytin, formula_size, Nat.add_sub_cancel]
  | fvar v =>
      intro fuel k rest h
      obtain ⟨fuel', rfl⟩ : ∃ m, fuel = m + 1 :=
        ⟨fuel - 1, by simp only [formula_size] at h; omega⟩
      have hr : serF (formula.fvar v) ++ rest
          = 1 :: 1 :: 1 :: (List.replicate v 1 ++ (0 :: rest)) := by
        simp [BinaryCCFSATFree.serF]
      rw [hr]
      simp only [scanClauses, readUnary_replicate, ptseytin, formula_size, Nat.add_sub_cancel]
  | fand f₁ f₂ ih₁ ih₂ =>
      intro fuel k rest h
      obtain ⟨fuel', rfl⟩ : ∃ m, fuel = m + 1 :=
        ⟨fuel - 1, by simp only [formula_size] at h; omega⟩
      have ha : formula_size f₁ ≤ fuel' := by simp only [formula_size] at h; omega
      have hb : formula_size f₂ ≤ fuel' - formula_size f₁ := by
        simp only [formula_size] at h; omega
      show scanClauses b (fuel' + 1) k (0 :: 1 :: ((serF f₁ ++ serF f₂) ++ rest)) = _
      rw [List.append_assoc]
      simp only [scanClauses]
      rw [subtreeTok_serF f₁ (serF f₂ ++ rest),
          ih₁ fuel' (k + 1) (serF f₂ ++ rest) ha,
          ih₂ (fuel' - formula_size f₁) (k + 1 + formula_size f₁) rest hb]
      simp only [ptseytin, formula_size]
      rw [show b + (k + 1) = b + k + 1 from by omega,
          show b + (k + 1 + formula_size f₁) = b + k + 1 + formula_size f₁ from by omega,
          show fuel' - formula_size f₁ - formula_size f₂
              = fuel' + 1 - (formula_size f₁ + formula_size f₂ + 1) from by omega,
          show k + 1 + formula_size f₁ + formula_size f₂
              = k + (formula_size f₁ + formula_size f₂ + 1) from by omega]
      simp only [List.append_assoc]
  | forr f₁ f₂ ih₁ ih₂ =>
      intro fuel k rest h
      obtain ⟨fuel', rfl⟩ : ∃ m, fuel = m + 1 :=
        ⟨fuel - 1, by simp only [formula_size] at h; omega⟩
      have ha : formula_size f₁ ≤ fuel' := by simp only [formula_size] at h; omega
      have hb : formula_size f₂ ≤ fuel' - formula_size f₁ := by
        simp only [formula_size] at h; omega
      show scanClauses b (fuel' + 1) k (1 :: 0 :: ((serF f₁ ++ serF f₂) ++ rest)) = _
      rw [List.append_assoc]
      simp only [scanClauses]
      rw [subtreeTok_serF f₁ (serF f₂ ++ rest),
          ih₁ fuel' (k + 1) (serF f₂ ++ rest) ha,
          ih₂ (fuel' - formula_size f₁) (k + 1 + formula_size f₁) rest hb]
      simp only [ptseytin, formula_size]
      rw [show b + (k + 1) = b + k + 1 from by omega,
          show b + (k + 1 + formula_size f₁) = b + k + 1 + formula_size f₁ from by omega,
          show fuel' - formula_size f₁ - formula_size f₂
              = fuel' + 1 - (formula_size f₁ + formula_size f₂ + 1) from by omega,
          show k + 1 + formula_size f₁ + formula_size f₂
              = k + (formula_size f₁ + formula_size f₂ + 1) from by omega]
      simp only [List.append_assoc]
  | fneg f₁ ih₁ =>
      intro fuel k rest h
      obtain ⟨fuel', rfl⟩ : ∃ m, fuel = m + 1 :=
        ⟨fuel - 1, by simp only [formula_size] at h; omega⟩
      have ha : formula_size f₁ ≤ fuel' := by simp only [formula_size] at h; omega
      show scanClauses b (fuel' + 1) k (1 :: 1 :: 0 :: (serF f₁ ++ rest)) = _
      simp only [scanClauses]
      rw [ih₁ fuel' (k + 1) rest ha]
      simp only [ptseytin, formula_size]
      rw [show b + (k + 1) = b + k + 1 from by omega,
          show fuel' - formula_size f₁ = fuel' + 1 - (formula_size f₁ + 1) from by omega,
          show k + 1 + formula_size f₁ = k + (formula_size f₁ + 1) from by omega]
      simp only [List.append_assoc]

/-- **The pure model equals the tree-recursive map** (`fsatToSat`). This is the
theorem the probe only `#eval`-checked; with it, the run-lemma proof (step
1(ii)) reduces to "the machine folds compute `mScan (serF f)`" — no tree
recursion on the machine side. -/
theorem mScan_eq_fsatToSat (f : formula) : mScan (serF f) = fsatToSat f := by
  have hf : formula_size f ≤ (serF f).length + 1 := by
    have := formula_size_le_serF f; omega
  have key := scanClauses_serF (serF f).length f ((serF f).length + 1) 0 [] hf
  rw [List.append_nil] at key
  unfold mScan fsatToSat preTseytin
  rw [key, scanClauses_nil, List.append_nil, Nat.add_zero]

/-! ### The one-token unfold of `scanClauses` (the `tokenBody`/outer-loop bridge)

`tokHead`/`tokRem` name the clause group and remaining stream produced by
consuming exactly one Polish token — the machine's `tokenBody` step. For a
binary node the right-child offset is `formula_size` of the left child (recovered
on the machine by `subtreeScan`, in the model by `subtreeTok_serF`). -/

/-- The clause group one `tokenBody` step emits (this node's Tseytin gadget). -/
def tokHead (b k : Nat) : formula → cnf
  | .ftrue    => tseytinTrue (b + k)
  | .fvar v   => tseytinEquiv v (b + k)
  | .fand a _ => tseytinAnd (b + k) (b + k + 1) (b + k + 1 + formula_size a)
  | .forr a _ => tseytinOr (b + k) (b + k + 1) (b + k + 1 + formula_size a)
  | .fneg _   => tseytinNot (b + k) (b + k + 1)

/-- The stream remaining after one `tokenBody` step (children pushed onto the
forest for compound nodes; the whole token consumed for leaves). -/
def tokRem : formula → List Nat → List Nat
  | .ftrue,   tail => tail
  | .fvar _,  tail => tail
  | .fand a b', tail => serF a ++ serF b' ++ tail
  | .forr a b', tail => serF a ++ serF b' ++ tail
  | .fneg a,  tail => serF a ++ tail

/-- **One-token unfold**: `scanClauses` on `serF g₀ ++ tail` emits `g₀`'s gadget
then continues on `tokRem g₀ tail` with the token counter advanced by one. -/
theorem scanClauses_tok (b fuel k : Nat) (g₀ : formula) (tail : List Nat) :
    scanClauses b (fuel + 1) k (serF g₀ ++ tail)
      = tokHead b k g₀ ++ scanClauses b fuel (k + 1) (tokRem g₀ tail) := by
  cases g₀ with
  | ftrue => simp [BinaryCCFSATFree.serF, scanClauses, tokHead, tokRem]
  | fvar v =>
      have hr : serF (formula.fvar v) ++ tail
          = 1 :: 1 :: 1 :: (List.replicate v 1 ++ (0 :: tail)) := by
        simp [BinaryCCFSATFree.serF]
      rw [hr]
      simp only [scanClauses, readUnary_replicate, tokHead, tokRem]
  | fand a b' =>
      have hr : serF (formula.fand a b') ++ tail
          = 0 :: 1 :: (serF a ++ (serF b' ++ tail)) := by
        simp [BinaryCCFSATFree.serF, List.append_assoc]
      rw [hr]
      simp only [scanClauses, tokHead, tokRem]
      rw [subtreeTok_serF a (serF b' ++ tail), List.append_assoc]
  | forr a b' =>
      have hr : serF (formula.forr a b') ++ tail
          = 1 :: 0 :: (serF a ++ (serF b' ++ tail)) := by
        simp [BinaryCCFSATFree.serF, List.append_assoc]
      rw [hr]
      simp only [scanClauses, tokHead, tokRem]
      rw [subtreeTok_serF a (serF b' ++ tail), List.append_assoc]
  | fneg a =>
      have hr : serF (formula.fneg a) ++ tail = 1 :: 1 :: 0 :: (serF a ++ tail) := by
        simp [BinaryCCFSATFree.serF]
      rw [hr]
      simp only [scanClauses, tokHead, tokRem]

/-- The Dyck forest after one token: children pushed for compound nodes. -/
def tokForest : formula → List formula → List formula
  | .ftrue,   hs => hs
  | .fvar _,  hs => hs
  | .fand a b', hs => a :: b' :: hs
  | .forr a b', hs => a :: b' :: hs
  | .fneg a,  hs => a :: hs

theorem tokForest_flatten (g₀ : formula) (hs : List formula) :
    ((tokForest g₀ hs).map serF).flatten = tokRem g₀ ((hs.map serF).flatten) := by
  cases g₀ <;>
    simp [tokForest, tokRem, List.map_cons, List.flatten_cons, List.append_assoc]

theorem tokForest_sum (g₀ : formula) (hs : List formula) :
    ((tokForest g₀ hs).map formula_size).sum + 1
      = (hs.map formula_size).sum + formula_size g₀ := by
  cases g₀ <;>
    simp [tokForest, formula_size, List.map_cons, List.sum_cons] <;> omega


/-! ## Run lemmas — step 1(ii): the machine folds compute `mScan (serF f)`

Foundational algebra + the emit-gadget projection lemmas (HANDOFF "NEXT TOP-DOWN"
step 1(ii), prerequisite (a)). Each gadget's `Cmd` writes exactly its
`encodeCnf (tseytin…)` onto `CNFOUT` and `numClauses` ones onto `TALLY`; frames
come free from the write-set (`Cmd.eval_get_of_not_writes`). -/

/-! ## Foundational algebra: `encodeCnf` distributes over `++` -/

theorem encodeCnf_cons (C : clause) (M : cnf) :
    encodeCnf (C :: M) = encodeClause C ++ encodeCnf M := rfl

theorem encodeCnf_append (M N : cnf) :
    encodeCnf (M ++ N) = encodeCnf M ++ encodeCnf N := by
  induction M with
  | nil => rfl
  | cons C M ih =>
      rw [List.cons_append, encodeCnf_cons, encodeCnf_cons, ih, List.append_assoc]

/-! ## Emit-gadget projection lemmas -/

theorem emitLit_cnfout (pol : Bool) (v : Var) (s : State) (vv : Nat)
    (hv : State.get s v = List.replicate vv 1) (hvc : v ≠ CNFOUT) :
    State.get ((emitLit pol v).eval s) CNFOUT
      = State.get s CNFOUT ++ encodeLit (pol, vv) := by
  cases pol <;>
    simp [emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
      State.get_set_eq, State.get_set_ne _ _ _ _ hvc, hv, encodeLit,
      List.append_assoc]

theorem emitLit_frame (pol : Bool) (v r : Var) (s : State) (hr : r ≠ CNFOUT) :
    State.get ((emitLit pol v).eval s) r = State.get s r := by
  cases pol <;>
    simp [emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
      State.get_set_ne _ _ _ _ hr]

/-- Full-state form: `emitLit` only ever writes `CNFOUT`. -/
theorem emitLit_run (pol : Bool) (v : Var) (s : State) (vv : Nat)
    (hv : State.get s v = List.replicate vv 1) (hvc : v ≠ CNFOUT) :
    (emitLit pol v).eval s
      = s.set CNFOUT (State.get s CNFOUT ++ encodeLit (pol, vv)) := by
  cases pol <;>
    simp [emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
      State.get_set_eq, State.get_set_ne _ _ _ _ hvc, hv, encodeLit,
      State.set_set, List.append_assoc]

/-- `endClause` writes `[0]` onto `CNFOUT` and `[1]` onto `TALLY`. -/
theorem endClause_run (s : State) :
    endClause.eval s
      = (s.set CNFOUT (State.get s CNFOUT ++ [0])).set TALLY
          (State.get s TALLY ++ [1]) := by
  simp [endClause, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    State.get_set_ne _ _ _ _ (show TALLY ≠ CNFOUT by decide)]

/-- The giant-simp lemma bundle for reading `CNFOUT` off an emitted gadget:
peel each nested `.set` (`CNFOUT` via `get_set_eq`, `TALLY` via `CNFOUT≠TALLY`,
the var registers via their `≠ CNFOUT`/`≠ TALLY`), unfold both the machine ops
and `encodeCnf`, and align the two right-nested appends. -/
theorem emitTrueG_cnfout (s : State) (va : Nat)
    (hva : State.get s VA = List.replicate va 1) :
    State.get (emitTrueG.eval s) CNFOUT
      = State.get s CNFOUT ++ encodeCnf (tseytinTrue va) := by
  simp only [emitTrueG, endClause, emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reduceIte, Bool.false_eq_true, if_false, State.get_set_eq,
    State.get_set_ne _ _ _ _ (show VA ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VA ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show CNFOUT ≠ TALLY by decide), hva,
    tseytinTrue, encodeCnf, encodeClause, encodeLit, List.foldr_cons, List.foldr_nil,
    List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]

theorem emitEquivG_cnfout (s : State) (vr va : Nat)
    (hvr : State.get s VREG = List.replicate vr 1)
    (hva : State.get s VA = List.replicate va 1) :
    State.get (emitEquivG.eval s) CNFOUT
      = State.get s CNFOUT ++ encodeCnf (tseytinEquiv vr va) := by
  simp only [emitEquivG, endClause, emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reduceIte, Bool.false_eq_true, if_false, State.get_set_eq,
    State.get_set_ne _ _ _ _ (show VREG ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VREG ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show VA ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VA ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show CNFOUT ≠ TALLY by decide), hvr, hva,
    tseytinEquiv, encodeCnf, encodeClause, encodeLit, List.foldr_cons, List.foldr_nil,
    List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]

theorem emitAndG_cnfout (s : State) (va vl vr : Nat)
    (hva : State.get s VA = List.replicate va 1)
    (hvl : State.get s VL = List.replicate vl 1)
    (hvr : State.get s VR = List.replicate vr 1) :
    State.get (emitAndG.eval s) CNFOUT
      = State.get s CNFOUT ++ encodeCnf (tseytinAnd va vl vr) := by
  simp only [emitAndG, endClause, emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reduceIte, Bool.false_eq_true, if_false, State.get_set_eq,
    State.get_set_ne _ _ _ _ (show VA ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VA ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show VL ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VL ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show VR ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VR ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show CNFOUT ≠ TALLY by decide), hva, hvl, hvr,
    tseytinAnd, encodeCnf, encodeClause, encodeLit, List.foldr_cons, List.foldr_nil,
    List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]

theorem emitOrG_cnfout (s : State) (va vl vr : Nat)
    (hva : State.get s VA = List.replicate va 1)
    (hvl : State.get s VL = List.replicate vl 1)
    (hvr : State.get s VR = List.replicate vr 1) :
    State.get (emitOrG.eval s) CNFOUT
      = State.get s CNFOUT ++ encodeCnf (tseytinOr va vl vr) := by
  simp only [emitOrG, endClause, emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reduceIte, Bool.false_eq_true, if_false, State.get_set_eq,
    State.get_set_ne _ _ _ _ (show VA ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VA ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show VL ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VL ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show VR ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VR ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show CNFOUT ≠ TALLY by decide), hva, hvl, hvr,
    tseytinOr, encodeCnf, encodeClause, encodeLit, List.foldr_cons, List.foldr_nil,
    List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]

theorem emitNotG_cnfout (s : State) (va vl : Nat)
    (hva : State.get s VA = List.replicate va 1)
    (hvl : State.get s VL = List.replicate vl 1) :
    State.get (emitNotG.eval s) CNFOUT
      = State.get s CNFOUT ++ encodeCnf (tseytinNot va vl) := by
  simp only [emitNotG, endClause, emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reduceIte, Bool.false_eq_true, if_false, State.get_set_eq,
    State.get_set_ne _ _ _ _ (show VA ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VA ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show VL ≠ CNFOUT by decide),
    State.get_set_ne _ _ _ _ (show VL ≠ TALLY by decide),
    State.get_set_ne _ _ _ _ (show CNFOUT ≠ TALLY by decide), hva, hvl,
    tseytinNot, encodeCnf, encodeClause, encodeLit, List.foldr_cons, List.foldr_nil,
    List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]

/-! ### `TALLY` projections: each gadget appends `numClauses` ones. -/

theorem emitTrueG_tally (s : State) :
    State.get (emitTrueG.eval s) TALLY = State.get s TALLY ++ List.replicate 1 1 := by
  simp only [emitTrueG, endClause, emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reduceIte, Bool.false_eq_true, if_false, State.get_set_eq,
    State.get_set_ne _ _ _ _ (show TALLY ≠ CNFOUT by decide), List.replicate]

theorem emitEquivG_tally (s : State) :
    State.get (emitEquivG.eval s) TALLY = State.get s TALLY ++ List.replicate 2 1 := by
  simp only [emitEquivG, endClause, emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reduceIte, Bool.false_eq_true, if_false, State.get_set_eq,
    State.get_set_ne _ _ _ _ (show TALLY ≠ CNFOUT by decide), List.replicate,
    List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]

theorem emitAndG_tally (s : State) :
    State.get (emitAndG.eval s) TALLY = State.get s TALLY ++ List.replicate 3 1 := by
  simp only [emitAndG, endClause, emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reduceIte, Bool.false_eq_true, if_false, State.get_set_eq,
    State.get_set_ne _ _ _ _ (show TALLY ≠ CNFOUT by decide), List.replicate,
    List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]

theorem emitOrG_tally (s : State) :
    State.get (emitOrG.eval s) TALLY = State.get s TALLY ++ List.replicate 3 1 := by
  simp only [emitOrG, endClause, emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reduceIte, Bool.false_eq_true, if_false, State.get_set_eq,
    State.get_set_ne _ _ _ _ (show TALLY ≠ CNFOUT by decide), List.replicate,
    List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]

theorem emitNotG_tally (s : State) :
    State.get (emitNotG.eval s) TALLY = State.get s TALLY ++ List.replicate 2 1 := by
  simp only [emitNotG, endClause, emitLit, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reduceIte, Bool.false_eq_true, if_false, State.get_set_eq,
    State.get_set_ne _ _ _ _ (show TALLY ≠ CNFOUT by decide), List.replicate,
    List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]

/-! ### Generic gadget frame (via the write-set): the gadgets touch only
`CNFOUT`/`TALLY`. -/

theorem emitTrueG_frame (s : State) (r : Var) (h1 : r ≠ CNFOUT) (h2 : r ≠ TALLY) :
    State.get (emitTrueG.eval s) r = State.get s r :=
  Cmd.eval_get_of_not_writes _ s r (by simp [emitTrueG, endClause, emitLit, Cmd.writes,
    Op.writesTo, h1, h2])

theorem emitEquivG_frame (s : State) (r : Var) (h1 : r ≠ CNFOUT) (h2 : r ≠ TALLY) :
    State.get (emitEquivG.eval s) r = State.get s r :=
  Cmd.eval_get_of_not_writes _ s r (by simp [emitEquivG, endClause, emitLit, Cmd.writes,
    Op.writesTo, h1, h2])

theorem emitAndG_frame (s : State) (r : Var) (h1 : r ≠ CNFOUT) (h2 : r ≠ TALLY) :
    State.get (emitAndG.eval s) r = State.get s r :=
  Cmd.eval_get_of_not_writes _ s r (by simp [emitAndG, endClause, emitLit, Cmd.writes,
    Op.writesTo, h1, h2])

theorem emitOrG_frame (s : State) (r : Var) (h1 : r ≠ CNFOUT) (h2 : r ≠ TALLY) :
    State.get (emitOrG.eval s) r = State.get s r :=
  Cmd.eval_get_of_not_writes _ s r (by simp [emitOrG, endClause, emitLit, Cmd.writes,
    Op.writesTo, h1, h2])

theorem emitNotG_frame (s : State) (r : Var) (h1 : r ≠ CNFOUT) (h2 : r ≠ TALLY) :
    State.get (emitNotG.eval s) r = State.get s r :=
  Cmd.eval_get_of_not_writes _ s r (by simp [emitNotG, endClause, emitLit, Cmd.writes,
    Op.writesTo, h1, h2])



/-! ## The drain-skip inner loop (`subtreeScan`'s fvar payload skip) -/

/-- Frame set for `drainSkipBody`: it writes only `H3`, `SC2`, `DN2`, `SKIP`. -/
theorem drainSkipBody_frame (s : State) (r : Var)
    (h : r ≠ H3) (h1 : r ≠ SC2) (h2 : r ≠ DN2) (h3 : r ≠ SKIP) :
    State.get (drainSkipBody.eval s) r = State.get s r :=
  Cmd.eval_get_of_not_writes _ s r (by
    simp [drainSkipBody, nop, Cmd.writes, Op.writesTo, h, h1, h2, h3])

/-- `drainSkipBody` once, already done (`DN2 = [1]`): a pure freeze (only `SKIP`). -/
theorem drainSkipBody_done (s : State) (h : State.get s DN2 = [1]) :
    drainSkipBody.eval s = s.set SKIP [] := by
  rw [drainSkipBody, Cmd.eval_ifBit_true _ _ _ _ h, nop, Cmd.eval_op, Op.eval]

/-- `drainSkipBody` once, peeling a `1` (`DN2 = []`, `SC2 = 1::r`). -/
theorem drainSkipBody_one (s : State) (r : List Nat)
    (hDN : State.get s DN2 = []) (hSC : State.get s SC2 = 1 :: r) :
    drainSkipBody.eval s = ((s.set H3 [1]).set SC2 r).set SKIP [] := by
  have hne : State.get s DN2 ≠ [1] := by rw [hDN]; decide
  rw [drainSkipBody, Cmd.eval_ifBit_false _ _ _ _ hne]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval,
    State.get_set_ne _ _ _ _ (show SC2 ≠ H3 by decide), hSC, List.tail_cons]
  rw [Cmd.eval_ifBit_true _ _ _ _
    (by rw [State.get_set_ne _ _ _ _ (show H3 ≠ SC2 by decide), State.get_set_eq]),
    nop, Cmd.eval_op, Op.eval]

/-- `drainSkipBody` once, hitting the `0` terminator (`DN2 = []`, `SC2 = 0::r`):
consumes the `0` and sets the done flag. -/
theorem drainSkipBody_zero (s : State) (r : List Nat)
    (hDN : State.get s DN2 = []) (hSC : State.get s SC2 = 0 :: r) :
    drainSkipBody.eval s = ((s.set H3 [0]).set SC2 r).set DN2 [1] := by
  have hne : State.get s DN2 ≠ [1] := by rw [hDN]; decide
  rw [drainSkipBody, Cmd.eval_ifBit_false _ _ _ _ hne]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval,
    State.get_set_ne _ _ _ _ (show SC2 ≠ H3 by decide), hSC, List.tail_cons]
  rw [Cmd.eval_ifBit_false _ _ _ _
    (by rw [State.get_set_ne _ _ _ _ (show H3 ≠ SC2 by decide), State.get_set_eq]; decide)]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set,
    List.nil_append]

/-- The fvar-payload skip loop: `SC2 = 1^v ++ 0::rest`, `DN2 = []` ⇒ after
`forBnd IDX3 SC2 drainSkipBody` (which runs `|SC2|` iterations), `SC2 = rest`,
`DN2 = [1]`, everything else outside `{SC2,DN2,H3,SKIP,IDX3}` preserved. -/
theorem drainSkip_run (u : State) (v : Nat) (rest : List Nat)
    (hSC2 : State.get u SC2 = List.replicate v 1 ++ 0 :: rest)
    (hDN2 : State.get u DN2 = []) :
    State.get ((Cmd.forBnd IDX3 SC2 drainSkipBody).eval u) SC2 = rest
    ∧ State.get ((Cmd.forBnd IDX3 SC2 drainSkipBody).eval u) DN2 = [1]
    ∧ (∀ r : Var, r ≠ SC2 → r ≠ DN2 → r ≠ H3 → r ≠ SKIP → r ≠ IDX3 →
        State.get ((Cmd.forBnd IDX3 SC2 drainSkipBody).eval u) r = State.get u r) := by
  set M : Nat → State → Prop := fun i st =>
    (if i ≤ v
      then State.get st DN2 = [] ∧ State.get st SC2 = List.replicate (v - i) 1 ++ 0 :: rest
      else State.get st DN2 = [1] ∧ State.get st SC2 = rest)
    ∧ (∀ r : Var, r ≠ SC2 → r ≠ DN2 → r ≠ H3 → r ≠ SKIP → r ≠ IDX3 →
        State.get st r = State.get u r) with hMdef
  have h0 : M 0 u := by
    refine ⟨?_, fun r _ _ _ _ _ => rfl⟩
    simp only [hMdef, Nat.zero_le, if_true, Nat.sub_zero, hDN2, hSC2, and_self]
  have hstep : ∀ i st, i < (State.get u SC2).length → M i st →
      M (i + 1) (drainSkipBody.eval (st.set IDX3 (List.replicate i 1))) := by
    intro i st _ hM
    obtain ⟨hmain, hframe⟩ := hM
    set w := st.set IDX3 (List.replicate i 1) with hw
    have hwDN2 : State.get w DN2 = State.get st DN2 := State.get_set_ne _ _ _ _ (by decide)
    have hwSC2 : State.get w SC2 = State.get st SC2 := State.get_set_ne _ _ _ _ (by decide)
    refine ⟨?_, ?_⟩
    · by_cases hiv : i ≤ v
      · have hmain' := hmain; rw [if_pos hiv] at hmain'
        obtain ⟨hDN, hSC⟩ := hmain'
        have hDNw : State.get w DN2 = [] := by rw [hwDN2, hDN]
        by_cases hiv' : i + 1 ≤ v
        · -- peel a `1`
          rw [if_pos hiv']
          have hSCw : State.get w SC2 = 1 :: (List.replicate (v - (i + 1)) 1 ++ 0 :: rest) := by
            rw [hwSC2, hSC, show v - i = (v - (i + 1)) + 1 from by omega, List.replicate_succ,
              List.cons_append]
          rw [drainSkipBody_one w _ hDNw hSCw]
          refine ⟨?_, ?_⟩
          · rw [State.get_set_ne _ _ _ _ (show DN2 ≠ SKIP by decide),
              State.get_set_ne _ _ _ _ (show DN2 ≠ SC2 by decide),
              State.get_set_ne _ _ _ _ (show DN2 ≠ H3 by decide), hDNw]
          · rw [State.get_set_ne _ _ _ _ (show SC2 ≠ SKIP by decide), State.get_set_eq]
        · -- hit the `0`
          rw [if_neg hiv']
          have hiveq : i = v := by omega
          subst hiveq
          have hSCw : State.get w SC2 = 0 :: rest := by rw [hwSC2, hSC]; simp
          rw [drainSkipBody_zero w _ hDNw hSCw]
          refine ⟨State.get_set_eq _ _ _, ?_⟩
          rw [State.get_set_ne _ _ _ _ (show SC2 ≠ DN2 by decide), State.get_set_eq]
      · -- done: freeze
        rw [if_neg (show ¬ (i + 1 ≤ v) from by omega)]
        have hmain' := hmain; rw [if_neg hiv] at hmain'
        obtain ⟨hDN, hSC⟩ := hmain'
        have hDNw : State.get w DN2 = [1] := by rw [hwDN2, hDN]
        rw [drainSkipBody_done w hDNw]
        exact ⟨by rw [State.get_set_ne _ _ _ _ (show DN2 ≠ SKIP by decide), hDNw],
          by rw [State.get_set_ne _ _ _ _ (show SC2 ≠ SKIP by decide), hwSC2, hSC]⟩
    · intro r hr1 hr2 hr3 hr4 hr5
      rw [drainSkipBody_frame _ r hr3 hr1 hr2 hr4, hw, State.get_set_ne _ _ _ _ hr5]
      exact hframe r hr1 hr2 hr3 hr4 hr5
  have hInv := Cmd.foldlState_range_induct drainSkipBody IDX3 (State.get u SC2).length u M h0 hstep
  rw [Cmd.eval_forBnd]
  have hfin : ¬ ((State.get u SC2).length ≤ v) := by
    rw [hSC2]; simp only [List.length_append, List.length_replicate, List.length_cons]; omega
  obtain ⟨hmain, hframe⟩ := hInv
  rw [if_neg hfin] at hmain
  exact ⟨hmain.2, hmain.1, hframe⟩

/-! ## The fvar-payload drain loop (`tokenBody`'s fvar read into `VREG`) -/

theorem drainVarBody_frame (s : State) (r : Var)
    (h : r ≠ H3) (h1 : r ≠ SCAN) (h2 : r ≠ VREG) (h3 : r ≠ DN) (h4 : r ≠ SKIP) :
    State.get (drainVarBody.eval s) r = State.get s r :=
  Cmd.eval_get_of_not_writes _ s r (by
    simp [drainVarBody, nop, Cmd.writes, Op.writesTo, h, h1, h2, h3, h4])

theorem drainVarBody_done (s : State) (h : State.get s DN = [1]) :
    drainVarBody.eval s = s.set SKIP [] := by
  rw [drainVarBody, Cmd.eval_ifBit_true _ _ _ _ h, nop, Cmd.eval_op, Op.eval]

theorem drainVarBody_one (s : State) (r : List Nat)
    (hDN : State.get s DN = []) (hSC : State.get s SCAN = 1 :: r) :
    drainVarBody.eval s
      = ((s.set H3 [1]).set SCAN r).set VREG (State.get s VREG ++ [1]) := by
  have hne : State.get s DN ≠ [1] := by rw [hDN]; decide
  rw [drainVarBody, Cmd.eval_ifBit_false _ _ _ _ hne]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval,
    State.get_set_ne _ _ _ _ (show SCAN ≠ H3 by decide), hSC, List.tail_cons]
  rw [Cmd.eval_ifBit_true _ _ _ _
    (by rw [State.get_set_ne _ _ _ _ (show H3 ≠ SCAN by decide), State.get_set_eq])]
  simp only [Cmd.eval_op, Op.eval,
    State.get_set_ne _ _ _ _ (show VREG ≠ SCAN by decide),
    State.get_set_ne _ _ _ _ (show VREG ≠ H3 by decide)]

theorem drainVarBody_zero (s : State) (r : List Nat)
    (hDN : State.get s DN = []) (hSC : State.get s SCAN = 0 :: r) :
    drainVarBody.eval s = ((s.set H3 [0]).set SCAN r).set DN [1] := by
  have hne : State.get s DN ≠ [1] := by rw [hDN]; decide
  rw [drainVarBody, Cmd.eval_ifBit_false _ _ _ _ hne]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval,
    State.get_set_ne _ _ _ _ (show SCAN ≠ H3 by decide), hSC, List.tail_cons]
  rw [Cmd.eval_ifBit_false _ _ _ _
    (by rw [State.get_set_ne _ _ _ _ (show H3 ≠ SCAN by decide), State.get_set_eq]; decide)]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set,
    List.nil_append]

/-- The fvar-payload read loop: `SCAN = 1^v ++ 0::rest`, `VREG = []`, `DN = []`
⇒ after `forBnd IDX3 SCAN drainVarBody`, `SCAN = rest`, `VREG = 1^v`, `DN = [1]`,
everything else outside `{SCAN,VREG,DN,H3,SKIP,IDX3}` preserved. -/
theorem drainVar_run (u : State) (v : Nat) (rest : List Nat)
    (hSCAN : State.get u SCAN = List.replicate v 1 ++ 0 :: rest)
    (hVREG : State.get u VREG = [])
    (hDN : State.get u DN = []) :
    State.get ((Cmd.forBnd IDX3 SCAN drainVarBody).eval u) SCAN = rest
    ∧ State.get ((Cmd.forBnd IDX3 SCAN drainVarBody).eval u) VREG = List.replicate v 1
    ∧ State.get ((Cmd.forBnd IDX3 SCAN drainVarBody).eval u) DN = [1]
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ VREG → r ≠ DN → r ≠ H3 → r ≠ SKIP → r ≠ IDX3 →
        State.get ((Cmd.forBnd IDX3 SCAN drainVarBody).eval u) r = State.get u r) := by
  set M : Nat → State → Prop := fun i st =>
    (if i ≤ v
      then State.get st DN = [] ∧ State.get st SCAN = List.replicate (v - i) 1 ++ 0 :: rest
            ∧ State.get st VREG = List.replicate i 1
      else State.get st DN = [1] ∧ State.get st SCAN = rest
            ∧ State.get st VREG = List.replicate v 1)
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ VREG → r ≠ DN → r ≠ H3 → r ≠ SKIP → r ≠ IDX3 →
        State.get st r = State.get u r) with hMdef
  have h0 : M 0 u := by
    refine ⟨?_, fun r _ _ _ _ _ _ => rfl⟩
    simp only [hMdef, Nat.zero_le, if_true, Nat.sub_zero, hDN, hSCAN, hVREG,
      List.replicate, and_self]
  have hstep : ∀ i st, i < (State.get u SCAN).length → M i st →
      M (i + 1) (drainVarBody.eval (st.set IDX3 (List.replicate i 1))) := by
    intro i st _ hM
    obtain ⟨hmain, hframe⟩ := hM
    set w := st.set IDX3 (List.replicate i 1) with hw
    have hwDN : State.get w DN = State.get st DN := State.get_set_ne _ _ _ _ (by decide)
    have hwSCAN : State.get w SCAN = State.get st SCAN := State.get_set_ne _ _ _ _ (by decide)
    have hwVREG : State.get w VREG = State.get st VREG := State.get_set_ne _ _ _ _ (by decide)
    refine ⟨?_, ?_⟩
    · by_cases hiv : i ≤ v
      · have hmain' := hmain; rw [if_pos hiv] at hmain'
        obtain ⟨hDNst, hSCst, hVst⟩ := hmain'
        have hDNw : State.get w DN = [] := by rw [hwDN, hDNst]
        have hVw : State.get w VREG = List.replicate i 1 := by rw [hwVREG, hVst]
        by_cases hiv' : i + 1 ≤ v
        · rw [if_pos hiv']
          have hSCw : State.get w SCAN = 1 :: (List.replicate (v - (i + 1)) 1 ++ 0 :: rest) := by
            rw [hwSCAN, hSCst, show v - i = (v - (i + 1)) + 1 from by omega, List.replicate_succ,
              List.cons_append]
          rw [drainVarBody_one w _ hDNw hSCw]
          refine ⟨?_, ?_, ?_⟩
          · rw [State.get_set_ne _ _ _ _ (show DN ≠ VREG by decide),
              State.get_set_ne _ _ _ _ (show DN ≠ SCAN by decide),
              State.get_set_ne _ _ _ _ (show DN ≠ H3 by decide), hDNw]
          · rw [State.get_set_ne _ _ _ _ (show SCAN ≠ VREG by decide), State.get_set_eq]
          · rw [State.get_set_eq, hVw, ← List.replicate_succ']
        · rw [if_neg hiv']
          have hiveq : i = v := by omega
          subst hiveq
          have hSCw : State.get w SCAN = 0 :: rest := by rw [hwSCAN, hSCst]; simp
          rw [drainVarBody_zero w _ hDNw hSCw]
          refine ⟨State.get_set_eq _ _ _, ?_, ?_⟩
          · rw [State.get_set_ne _ _ _ _ (show SCAN ≠ DN by decide), State.get_set_eq]
          · rw [State.get_set_ne _ _ _ _ (show VREG ≠ DN by decide),
              State.get_set_ne _ _ _ _ (show VREG ≠ SCAN by decide),
              State.get_set_ne _ _ _ _ (show VREG ≠ H3 by decide), hVw]
      · rw [if_neg (show ¬ (i + 1 ≤ v) from by omega)]
        have hmain' := hmain; rw [if_neg hiv] at hmain'
        obtain ⟨hDNst, hSCst, hVst⟩ := hmain'
        have hDNw : State.get w DN = [1] := by rw [hwDN, hDNst]
        rw [drainVarBody_done w hDNw]
        refine ⟨?_, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (show DN ≠ SKIP by decide), hDNw]
        · rw [State.get_set_ne _ _ _ _ (show SCAN ≠ SKIP by decide), hwSCAN, hSCst]
        · rw [State.get_set_ne _ _ _ _ (show VREG ≠ SKIP by decide), hwVREG, hVst]
    · intro r hr1 hr2 hr3 hr4 hr5 hr6
      rw [drainVarBody_frame _ r hr4 hr1 hr2 hr3 hr5, hw, State.get_set_ne _ _ _ _ hr6]
      exact hframe r hr1 hr2 hr3 hr4 hr5 hr6
  have hInv := Cmd.foldlState_range_induct drainVarBody IDX3 (State.get u SCAN).length u M h0 hstep
  rw [Cmd.eval_forBnd]
  have hfin : ¬ ((State.get u SCAN).length ≤ v) := by
    rw [hSCAN]; simp only [List.length_append, List.length_replicate, List.length_cons]; omega
  obtain ⟨hmain, hframe⟩ := hInv
  rw [if_neg hfin] at hmain
  exact ⟨hmain.2.1, hmain.2.2, hmain.1, hframe⟩


/-! ## The per-shape `budgetBody` step lemmas (machine ⇒ pure `budgetStep`) -/

/-- Frame set for `budgetBody`: it writes only
`{NEB, H1B, H2B, T, SC2, BUD, DN2, SKIP, IDX3}`. -/
theorem budgetBody_frame (s : State) (r : Var)
    (hNEB : r ≠ NEB) (hH1B : r ≠ H1B) (hH2B : r ≠ H2B) (hT : r ≠ T)
    (hSC2 : r ≠ SC2) (hBUD : r ≠ BUD) (hDN2 : r ≠ DN2) (hSKIP : r ≠ SKIP)
    (hIDX3 : r ≠ IDX3) (hH3 : r ≠ H3) :
    State.get (budgetBody.eval s) r = State.get s r :=
  Cmd.eval_get_of_not_writes _ s r (by
    simp [budgetBody, budgetBodyInner, drainSkipBody, nop, Cmd.writes, Op.writesTo,
      hNEB, hH1B, hH2B, hT, hSC2, hBUD, hDN2, hSKIP, hIDX3, hH3])

/-- The `nonEmpty NEB BUD` guard fires (enters the body) when `BUD = 1^bud`,
`bud ≠ 0`. Peels `budgetBody` to its body evaluated on `s.set NEB [1]`. -/
theorem budgetBody_enter (s : State) (bud : Nat) (hbud : bud ≠ 0)
    (hBUD : State.get s BUD = List.replicate bud 1) :
    budgetBody.eval s = budgetBodyInner.eval (s.set NEB [1]) := by
  rw [budgetBody, Cmd.eval_seq]
  have e0 : (Cmd.op (.nonEmpty NEB BUD)).eval s = s.set NEB [1] := by
    rw [Cmd.eval_op, Op.eval, hBUD]
    cases bud with | zero => omega | succ n => simp
  rw [e0, Cmd.eval_ifBit_true _ _ _ _ (by rw [State.get_set_eq])]

/-- `(replicate (n+1) a).tail = replicate n a`. -/
theorem tail_replicate_succ {α : Type} (n : Nat) (a : α) :
    (List.replicate (n + 1) a).tail = List.replicate n a := by
  rw [List.replicate_succ, List.tail_cons]

/-- Empty budget (`BUD = []`): the `nonEmpty` guard fails ⇒ `budgetBody` is a
no-op on `SC2`/`BUD`/`T` (the pure `budgetStep` freeze). The complement of the
five token lemmas — together they characterise `budgetBody` on every state, the
ingredient the `subtreeScan_run` loop's `bud = 0` case needs. -/
theorem budgetBody_freeze (s : State) (r : Var)
    (hr1 : r ≠ SKIP) (hr2 : r ≠ NEB) (hBUD : State.get s BUD = []) :
    State.get (budgetBody.eval s) r = State.get s r := by
  rw [budgetBody, Cmd.eval_seq]
  have e0 : (Cmd.op (.nonEmpty NEB BUD)).eval s = s.set NEB [0] := by
    rw [Cmd.eval_op, Op.eval, hBUD]; rfl
  rw [e0, Cmd.eval_ifBit_false _ _ _ _ (by rw [State.get_set_eq]; decide),
    nop, Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ hr1,
    State.get_set_ne _ _ _ _ hr2]

/-- ftrue token (`SC2 = 0::0::r`, leaf): `SC2 → r`, `BUD → 1^(bud-1)`,
`T → 1^(t+1)`. -/
theorem budgetBody_ftrue (s : State) (r : List Nat) (bud t : Nat) (hbud : bud ≠ 0)
    (hBUD : State.get s BUD = List.replicate bud 1)
    (hSC : State.get s SC2 = 0 :: 0 :: r)
    (hT : State.get s T = List.replicate t 1) :
    State.get (budgetBody.eval s) SC2 = r
    ∧ State.get (budgetBody.eval s) BUD = List.replicate (bud - 1) 1
    ∧ State.get (budgetBody.eval s) T = List.replicate (t + 1) 1 := by
  obtain ⟨bud', rfl⟩ : ∃ m, bud = m + 1 := ⟨bud - 1, by omega⟩
  rw [budgetBody_enter s (bud' + 1) hbud hBUD, budgetBodyInner]
  set w := s.set NEB [1] with hw
  have hwSC : State.get w SC2 = 0 :: 0 :: r := by
    rw [hw, State.get_set_ne _ _ _ _ (show SC2 ≠ NEB by decide), hSC]
  have hwBUD : State.get w BUD = List.replicate (bud' + 1) 1 := by
    rw [hw, State.get_set_ne _ _ _ _ (show BUD ≠ NEB by decide), hBUD]
  have hwT : State.get w T = List.replicate t 1 := by
    rw [hw, State.get_set_ne _ _ _ _ (show T ≠ NEB by decide), hT]
  -- evaluate the straight-line prefix in place, leaving `ifBitchain.eval P`
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, hwSC, hwT,
    State.get_set_ne _ _ _ _ (show SC2 ≠ H1B by decide),
    State.get_set_ne _ _ _ _ (show SC2 ≠ H2B by decide),
    State.get_set_ne _ _ _ _ (show T ≠ SC2 by decide),
    State.get_set_ne _ _ _ _ (show T ≠ H2B by decide),
    State.get_set_ne _ _ _ _ (show T ≠ H1B by decide),
    State.get_set_eq, List.tail_cons]
  set P := ((((w.set H1B [0]).set SC2 (0 :: r)).set H2B [0]).set SC2 r).set T
      (List.replicate t 1 ++ [1]) with hPdef
  have hPH1B : State.get P H1B = [0] := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H1B ≠ T by decide),
      State.get_set_ne _ _ _ _ (show H1B ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show H1B ≠ H2B by decide)]
  have hPH2B : State.get P H2B = [0] := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H2B ≠ T by decide),
      State.get_set_ne _ _ _ _ (show H2B ≠ SC2 by decide)]
  have hPBUD : State.get P BUD = List.replicate (bud' + 1) 1 := by
    simp only [hPdef,
      State.get_set_ne _ _ _ _ (show BUD ≠ T by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H2B by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H1B by decide), hwBUD]
  rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hPH1B]; decide),
      Cmd.eval_ifBit_false _ _ _ _ (by rw [hPH2B]; decide),
      Cmd.eval_op, Op.eval, hPBUD]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show SC2 ≠ BUD by decide),
      State.get_set_ne _ _ _ _ (show SC2 ≠ T by decide)]
  · rw [State.get_set_eq, tail_replicate_succ]; simp
  · simp only [State.get_set_ne _ _ _ _ (show T ≠ BUD by decide), hPdef, State.get_set_eq]
    rw [← List.replicate_succ']

/-- fand token (`SC2 = 0::1::r`, binary): `SC2 → r`, `BUD → 1^(bud+1)`,
`T → 1^(t+1)`. -/
theorem budgetBody_fand (s : State) (r : List Nat) (bud t : Nat) (hbud : bud ≠ 0)
    (hBUD : State.get s BUD = List.replicate bud 1)
    (hSC : State.get s SC2 = 0 :: 1 :: r)
    (hT : State.get s T = List.replicate t 1) :
    State.get (budgetBody.eval s) SC2 = r
    ∧ State.get (budgetBody.eval s) BUD = List.replicate (bud + 1) 1
    ∧ State.get (budgetBody.eval s) T = List.replicate (t + 1) 1 := by
  rw [budgetBody_enter s bud hbud hBUD, budgetBodyInner]
  set w := s.set NEB [1] with hw
  have hwSC : State.get w SC2 = 0 :: 1 :: r := by
    rw [hw, State.get_set_ne _ _ _ _ (show SC2 ≠ NEB by decide), hSC]
  have hwBUD : State.get w BUD = List.replicate bud 1 := by
    rw [hw, State.get_set_ne _ _ _ _ (show BUD ≠ NEB by decide), hBUD]
  have hwT : State.get w T = List.replicate t 1 := by
    rw [hw, State.get_set_ne _ _ _ _ (show T ≠ NEB by decide), hT]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, hwSC, hwT,
    State.get_set_ne _ _ _ _ (show SC2 ≠ H1B by decide),
    State.get_set_ne _ _ _ _ (show SC2 ≠ H2B by decide),
    State.get_set_ne _ _ _ _ (show T ≠ SC2 by decide),
    State.get_set_ne _ _ _ _ (show T ≠ H2B by decide),
    State.get_set_ne _ _ _ _ (show T ≠ H1B by decide),
    State.get_set_eq, List.tail_cons]
  set P := ((((w.set H1B [0]).set SC2 (1 :: r)).set H2B [1]).set SC2 r).set T
      (List.replicate t 1 ++ [1]) with hPdef
  have hPH1B : State.get P H1B = [0] := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H1B ≠ T by decide),
      State.get_set_ne _ _ _ _ (show H1B ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show H1B ≠ H2B by decide)]
  have hPH2B : State.get P H2B = [1] := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H2B ≠ T by decide),
      State.get_set_ne _ _ _ _ (show H2B ≠ SC2 by decide)]
  have hPBUD : State.get P BUD = List.replicate bud 1 := by
    simp only [hPdef,
      State.get_set_ne _ _ _ _ (show BUD ≠ T by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H2B by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H1B by decide), hwBUD]
  rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hPH1B]; decide),
      Cmd.eval_ifBit_true _ _ _ _ hPH2B, Cmd.eval_op, Op.eval, hPBUD]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show SC2 ≠ BUD by decide),
      State.get_set_ne _ _ _ _ (show SC2 ≠ T by decide)]
  · rw [State.get_set_eq, ← List.replicate_succ']
  · simp only [State.get_set_ne _ _ _ _ (show T ≠ BUD by decide), hPdef, State.get_set_eq]
    rw [← List.replicate_succ']

/-- forr token (`SC2 = 1::0::r`, binary): `SC2 → r`, `BUD → 1^(bud+1)`,
`T → 1^(t+1)`. -/
theorem budgetBody_forr (s : State) (r : List Nat) (bud t : Nat) (hbud : bud ≠ 0)
    (hBUD : State.get s BUD = List.replicate bud 1)
    (hSC : State.get s SC2 = 1 :: 0 :: r)
    (hT : State.get s T = List.replicate t 1) :
    State.get (budgetBody.eval s) SC2 = r
    ∧ State.get (budgetBody.eval s) BUD = List.replicate (bud + 1) 1
    ∧ State.get (budgetBody.eval s) T = List.replicate (t + 1) 1 := by
  rw [budgetBody_enter s bud hbud hBUD, budgetBodyInner]
  set w := s.set NEB [1] with hw
  have hwSC : State.get w SC2 = 1 :: 0 :: r := by
    rw [hw, State.get_set_ne _ _ _ _ (show SC2 ≠ NEB by decide), hSC]
  have hwBUD : State.get w BUD = List.replicate bud 1 := by
    rw [hw, State.get_set_ne _ _ _ _ (show BUD ≠ NEB by decide), hBUD]
  have hwT : State.get w T = List.replicate t 1 := by
    rw [hw, State.get_set_ne _ _ _ _ (show T ≠ NEB by decide), hT]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, hwSC, hwT,
    State.get_set_ne _ _ _ _ (show SC2 ≠ H1B by decide),
    State.get_set_ne _ _ _ _ (show SC2 ≠ H2B by decide),
    State.get_set_ne _ _ _ _ (show T ≠ SC2 by decide),
    State.get_set_ne _ _ _ _ (show T ≠ H2B by decide),
    State.get_set_ne _ _ _ _ (show T ≠ H1B by decide),
    State.get_set_eq, List.tail_cons]
  set P := ((((w.set H1B [1]).set SC2 (0 :: r)).set H2B [0]).set SC2 r).set T
      (List.replicate t 1 ++ [1]) with hPdef
  have hPH1B : State.get P H1B = [1] := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H1B ≠ T by decide),
      State.get_set_ne _ _ _ _ (show H1B ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show H1B ≠ H2B by decide)]
  have hPH2B : State.get P H2B = [0] := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H2B ≠ T by decide),
      State.get_set_ne _ _ _ _ (show H2B ≠ SC2 by decide)]
  have hPBUD : State.get P BUD = List.replicate bud 1 := by
    simp only [hPdef,
      State.get_set_ne _ _ _ _ (show BUD ≠ T by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H2B by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H1B by decide), hwBUD]
  rw [Cmd.eval_ifBit_true _ _ _ _ hPH1B,
      Cmd.eval_ifBit_false _ _ _ _ (by rw [hPH2B]; decide), Cmd.eval_op, Op.eval, hPBUD]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show SC2 ≠ BUD by decide),
      State.get_set_ne _ _ _ _ (show SC2 ≠ T by decide)]
  · rw [State.get_set_eq, ← List.replicate_succ']
  · simp only [State.get_set_ne _ _ _ _ (show T ≠ BUD by decide), hPdef, State.get_set_eq]
    rw [← List.replicate_succ']

/-- fneg token (`SC2 = 1::1::0::r`, unary): `SC2 → r`, `BUD → 1^bud`,
`T → 1^(t+1)`. -/
theorem budgetBody_fneg (s : State) (r : List Nat) (bud t : Nat) (hbud : bud ≠ 0)
    (hBUD : State.get s BUD = List.replicate bud 1)
    (hSC : State.get s SC2 = 1 :: 1 :: 0 :: r)
    (hT : State.get s T = List.replicate t 1) :
    State.get (budgetBody.eval s) SC2 = r
    ∧ State.get (budgetBody.eval s) BUD = List.replicate bud 1
    ∧ State.get (budgetBody.eval s) T = List.replicate (t + 1) 1 := by
  rw [budgetBody_enter s bud hbud hBUD, budgetBodyInner]
  set w := s.set NEB [1] with hw
  have hwSC : State.get w SC2 = 1 :: 1 :: 0 :: r := by
    rw [hw, State.get_set_ne _ _ _ _ (show SC2 ≠ NEB by decide), hSC]
  have hwBUD : State.get w BUD = List.replicate bud 1 := by
    rw [hw, State.get_set_ne _ _ _ _ (show BUD ≠ NEB by decide), hBUD]
  have hwT : State.get w T = List.replicate t 1 := by
    rw [hw, State.get_set_ne _ _ _ _ (show T ≠ NEB by decide), hT]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, hwSC, hwT,
    State.get_set_ne _ _ _ _ (show SC2 ≠ H1B by decide),
    State.get_set_ne _ _ _ _ (show SC2 ≠ H2B by decide),
    State.get_set_ne _ _ _ _ (show T ≠ SC2 by decide),
    State.get_set_ne _ _ _ _ (show T ≠ H2B by decide),
    State.get_set_ne _ _ _ _ (show T ≠ H1B by decide),
    State.get_set_eq, List.tail_cons]
  set P := ((((w.set H1B [1]).set SC2 (1 :: 0 :: r)).set H2B [1]).set SC2 (0 :: r)).set T
      (List.replicate t 1 ++ [1]) with hPdef
  have hPH1B : State.get P H1B = [1] := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H1B ≠ T by decide),
      State.get_set_ne _ _ _ _ (show H1B ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show H1B ≠ H2B by decide)]
  have hPH2B : State.get P H2B = [1] := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H2B ≠ T by decide),
      State.get_set_ne _ _ _ _ (show H2B ≠ SC2 by decide)]
  rw [Cmd.eval_ifBit_true _ _ _ _ hPH1B, Cmd.eval_ifBit_true _ _ _ _ hPH2B]
  -- read the 3rd bit: head H2B SC2 (P SC2 = 0::r → [0]), tail SC2 (→ r)
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval,
    State.get_set_ne _ _ _ _ (show SC2 ≠ H2B by decide),
    show State.get P SC2 = 0 :: r from by
      simp only [hPdef, State.get_set_eq,
        State.get_set_ne _ _ _ _ (show SC2 ≠ T by decide)],
    List.tail_cons]
  set P2 := (P.set H2B [0]).set SC2 r with hP2def
  have hP2H2B : State.get P2 H2B = [0] := by
    simp only [hP2def, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H2B ≠ SC2 by decide)]
  rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hP2H2B]; decide), nop, Cmd.eval_op, Op.eval]
  refine ⟨?_, ?_, ?_⟩
  · rw [State.get_set_ne _ _ _ _ (show SC2 ≠ SKIP by decide), hP2def, State.get_set_eq]
  · rw [State.get_set_ne _ _ _ _ (show BUD ≠ SKIP by decide), hP2def,
      State.get_set_ne _ _ _ _ (show BUD ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H2B by decide), hPdef,
      State.get_set_ne _ _ _ _ (show BUD ≠ T by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H2B by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H1B by decide), hwBUD]
  · rw [State.get_set_ne _ _ _ _ (show T ≠ SKIP by decide), hP2def,
      State.get_set_ne _ _ _ _ (show T ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show T ≠ H2B by decide), hPdef, State.get_set_eq,
      ← List.replicate_succ']

/-- fvar token (`SC2 = 1::1::1::(1^v ++ 0::r)`, leaf): `SC2 → r`,
`BUD → 1^(bud-1)`, `T → 1^(t+1)` (the payload is drained via `drainSkip_run`). -/
theorem budgetBody_fvar (s : State) (v : Nat) (r : List Nat) (bud t : Nat) (hbud : bud ≠ 0)
    (hBUD : State.get s BUD = List.replicate bud 1)
    (hSC : State.get s SC2 = 1 :: 1 :: 1 :: (List.replicate v 1 ++ 0 :: r))
    (hT : State.get s T = List.replicate t 1) :
    State.get (budgetBody.eval s) SC2 = r
    ∧ State.get (budgetBody.eval s) BUD = List.replicate (bud - 1) 1
    ∧ State.get (budgetBody.eval s) T = List.replicate (t + 1) 1 := by
  obtain ⟨bud', rfl⟩ : ∃ m, bud = m + 1 := ⟨bud - 1, by omega⟩
  rw [budgetBody_enter s (bud' + 1) hbud hBUD, budgetBodyInner]
  set w := s.set NEB [1] with hw
  have hwSC : State.get w SC2 = 1 :: 1 :: 1 :: (List.replicate v 1 ++ 0 :: r) := by
    rw [hw, State.get_set_ne _ _ _ _ (show SC2 ≠ NEB by decide), hSC]
  have hwBUD : State.get w BUD = List.replicate (bud' + 1) 1 := by
    rw [hw, State.get_set_ne _ _ _ _ (show BUD ≠ NEB by decide), hBUD]
  have hwT : State.get w T = List.replicate t 1 := by
    rw [hw, State.get_set_ne _ _ _ _ (show T ≠ NEB by decide), hT]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, hwSC, hwT,
    State.get_set_ne _ _ _ _ (show SC2 ≠ H1B by decide),
    State.get_set_ne _ _ _ _ (show SC2 ≠ H2B by decide),
    State.get_set_ne _ _ _ _ (show T ≠ SC2 by decide),
    State.get_set_ne _ _ _ _ (show T ≠ H2B by decide),
    State.get_set_ne _ _ _ _ (show T ≠ H1B by decide),
    State.get_set_eq, List.tail_cons]
  set P := ((((w.set H1B [1]).set SC2 (1 :: 1 :: (List.replicate v 1 ++ 0 :: r))).set H2B
      [1]).set SC2 (1 :: (List.replicate v 1 ++ 0 :: r))).set T
      (List.replicate t 1 ++ [1]) with hPdef
  have hPH1B : State.get P H1B = [1] := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H1B ≠ T by decide),
      State.get_set_ne _ _ _ _ (show H1B ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show H1B ≠ H2B by decide)]
  have hPH2B : State.get P H2B = [1] := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H2B ≠ T by decide),
      State.get_set_ne _ _ _ _ (show H2B ≠ SC2 by decide)]
  have hPSC : State.get P SC2 = 1 :: (List.replicate v 1 ++ 0 :: r) := by
    simp only [hPdef, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show SC2 ≠ T by decide)]
  rw [Cmd.eval_ifBit_true _ _ _ _ hPH1B, Cmd.eval_ifBit_true _ _ _ _ hPH2B]
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval,
    State.get_set_ne _ _ _ _ (show SC2 ≠ H2B by decide), hPSC, List.tail_cons]
  set P2 := (P.set H2B [1]).set SC2 (List.replicate v 1 ++ 0 :: r) with hP2def
  have hP2H2B : State.get P2 H2B = [1] := by
    simp only [hP2def, State.get_set_eq,
      State.get_set_ne _ _ _ _ (show H2B ≠ SC2 by decide)]
  rw [Cmd.eval_ifBit_true _ _ _ _ hP2H2B, Cmd.eval_seq, Cmd.eval_seq,
    show (Cmd.op (Op.clear DN2)).eval P2 = P2.set DN2 [] from by rw [Cmd.eval_op, Op.eval]]
  -- clear DN2, then the drain loop, then tail BUD BUD
  set P3 := P2.set DN2 [] with hP3def
  have hP3SC : State.get P3 SC2 = List.replicate v 1 ++ 0 :: r := by
    rw [hP3def, State.get_set_ne _ _ _ _ (show SC2 ≠ DN2 by decide), hP2def, State.get_set_eq]
  have hP3DN : State.get P3 DN2 = [] := by rw [hP3def, State.get_set_eq]
  obtain ⟨hRSC, hRDN, hRframe⟩ := drainSkip_run P3 v r hP3SC hP3DN
  set R := (Cmd.forBnd IDX3 SC2 drainSkipBody).eval P3 with hRdef
  rw [Cmd.eval_op, Op.eval]
  have hRBUD : State.get R BUD = List.replicate (bud' + 1) 1 := by
    rw [hRframe BUD (by decide) (by decide) (by decide) (by decide) (by decide),
      hP3def, State.get_set_ne _ _ _ _ (show BUD ≠ DN2 by decide), hP2def,
      State.get_set_ne _ _ _ _ (show BUD ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H2B by decide), hPdef,
      State.get_set_ne _ _ _ _ (show BUD ≠ T by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H2B by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show BUD ≠ H1B by decide), hwBUD]
  have hRT : State.get R T = List.replicate t 1 ++ [1] := by
    rw [hRframe T (by decide) (by decide) (by decide) (by decide) (by decide),
      hP3def, State.get_set_ne _ _ _ _ (show T ≠ DN2 by decide), hP2def,
      State.get_set_ne _ _ _ _ (show T ≠ SC2 by decide),
      State.get_set_ne _ _ _ _ (show T ≠ H2B by decide), hPdef, State.get_set_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [State.get_set_ne _ _ _ _ (show SC2 ≠ BUD by decide), hRSC]
  · rw [State.get_set_eq, hRBUD, tail_replicate_succ]; simp
  · rw [State.get_set_ne _ _ _ _ (show T ≠ BUD by decide), hRT, ← List.replicate_succ']

/-! ## The budget-scan loop assembly (`subtreeScan_run`, the Dyck-invariant fold) -/

/-- **The arity-budget scan loop.** Starting from `SCAN = serF g ++ rest`,
`subtreeScan` sets `T := 1^(formula_size g)` — the token count of the first
complete subtree (`= subtreeTok (serF g ++ rest)` via `subtreeTok_serF`). `SCAN`
is preserved (the scan runs off a copy in `SC2`); everything below the frame is
scratch. The fold carries a **Dyck well-formedness invariant** (`∃ gs`, a forest
of pending subtrees) rather than a raw `budgetStep^[i]` invariant, because
`budgetBody` disagrees with `budgetStep` on malformed streams — the invariant
keeps the machine on the well-formed trajectory, so the malformed branch is never
reached while the budget is positive. -/
theorem subtreeScan_run (u : State) (g : formula) (rest : List Nat)
    (hSCAN : State.get u SCAN = serF g ++ rest) :
    State.get (subtreeScan.eval u) T = List.replicate (formula_size g) 1
    ∧ State.get (subtreeScan.eval u) SCAN = serF g ++ rest
    ∧ (∀ r : Var, r ≠ SC2 → r ≠ BUD → r ≠ T → r ≠ NEB → r ≠ H1B → r ≠ H2B →
        r ≠ DN2 → r ≠ SKIP → r ≠ IDX3 → r ≠ H3 → r ≠ IDX2 →
        State.get (subtreeScan.eval u) r = State.get u r) := by
  -- The post-prefix state: `SC2 = SCAN`, `BUD = 1`, `T = 0`.
  set P0 : State := ((u.set SC2 (serF g ++ rest)).set BUD [1]).set T [] with hP0
  have hpre : subtreeScan.eval u = (Cmd.forBnd IDX2 SCAN budgetBody).eval P0 := by
    unfold subtreeScan
    rw [Cmd.eval_seq, Cmd.eval_op, Op.eval, hSCAN, Cmd.eval_seq, Cmd.eval_op, Op.eval,
      Cmd.eval_seq, Cmd.eval_op, Op.eval, Cmd.eval_seq, Cmd.eval_op, Op.eval]
    congr 1
    rw [hP0]
    simp only [State.get_set_eq, List.nil_append, State.set_set]
  have hP0SC2 : State.get P0 SC2 = serF g ++ rest := by
    rw [hP0, State.get_set_ne _ _ _ _ (show SC2 ≠ T by decide),
      State.get_set_ne _ _ _ _ (show SC2 ≠ BUD by decide), State.get_set_eq]
  have hP0BUD : State.get P0 BUD = [1] := by
    rw [hP0, State.get_set_ne _ _ _ _ (show BUD ≠ T by decide), State.get_set_eq]
  have hP0T : State.get P0 T = [] := by rw [hP0, State.get_set_eq]
  have hP0SCAN : State.get P0 SCAN = serF g ++ rest := by
    rw [hP0, State.get_set_ne _ _ _ _ (show SCAN ≠ T by decide),
      State.get_set_ne _ _ _ _ (show SCAN ≠ BUD by decide),
      State.get_set_ne _ _ _ _ (show SCAN ≠ SC2 by decide), hSCAN]
  have hP0frame : ∀ r : Var, r ≠ SC2 → r ≠ BUD → r ≠ T →
      State.get P0 r = State.get u r := by
    intro r h1 h2 h3
    rw [hP0, State.get_set_ne _ _ _ _ h3, State.get_set_ne _ _ _ _ h2,
      State.get_set_ne _ _ _ _ h1]
  clear_value P0
  -- The Dyck invariant: `gs` = the forest of pending subtrees.
  set M : Nat → State → Prop := fun i st =>
    (∃ gs : List formula,
        State.get st SC2 = (gs.map serF).flatten ++ rest
      ∧ State.get st BUD = List.replicate gs.length 1
      ∧ State.get st T = List.replicate (min i (formula_size g)) 1
      ∧ (gs.map formula_size).sum + min i (formula_size g) = formula_size g)
    ∧ (∀ r : Var, r ≠ SC2 → r ≠ BUD → r ≠ T → r ≠ NEB → r ≠ H1B → r ≠ H2B →
        r ≠ DN2 → r ≠ SKIP → r ≠ IDX3 → r ≠ H3 → r ≠ IDX2 →
        State.get st r = State.get P0 r) with hMdef
  have h0 : M 0 P0 := by
    refine ⟨⟨[g], ?_, ?_, ?_, ?_⟩, fun r _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [hP0SC2]; simp [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
    · rw [hP0BUD]; rfl
    · rw [hP0T]; simp
    · simp [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hstep : ∀ i st, i < (serF g ++ rest).length → M i st →
      M (i + 1) (budgetBody.eval (st.set IDX2 (List.replicate i 1))) := by
    intro i st _ hM
    obtain ⟨⟨gs, hSC2, hBUD, hT, hcons⟩, hframe⟩ := hM
    set w := st.set IDX2 (List.replicate i 1) with hw
    have hwSC2 : State.get w SC2 = State.get st SC2 := State.get_set_ne _ _ _ _ (by decide)
    have hwBUD : State.get w BUD = State.get st BUD := State.get_set_ne _ _ _ _ (by decide)
    have hwT : State.get w T = State.get st T := State.get_set_ne _ _ _ _ (by decide)
    have hframe' : ∀ r : Var, r ≠ SC2 → r ≠ BUD → r ≠ T → r ≠ NEB → r ≠ H1B → r ≠ H2B →
        r ≠ DN2 → r ≠ SKIP → r ≠ IDX3 → r ≠ H3 → r ≠ IDX2 →
        State.get (budgetBody.eval w) r = State.get P0 r := by
      intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      rw [budgetBody_frame w r h4 h5 h6 h3 h1 h2 h7 h8 h9 h10, hw,
        State.get_set_ne _ _ _ _ h11]
      exact hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    refine ⟨?_, hframe'⟩
    cases gs with
    | nil =>
        have hBUDe : State.get w BUD = [] := by rw [hwBUD, hBUD]; rfl
        have hcons' : min i (formula_size g) = formula_size g := by
          simp only [List.map_nil, List.sum_nil, Nat.zero_add] at hcons; omega
        refine ⟨[], ?_, ?_, ?_, ?_⟩
        · rw [budgetBody_freeze w SC2 (by decide) (by decide) hBUDe, hwSC2, hSC2]
        · rw [budgetBody_freeze w BUD (by decide) (by decide) hBUDe, hBUDe]; rfl
        · rw [budgetBody_freeze w T (by decide) (by decide) hBUDe, hwT, hT]
          congr 1; omega
        · simp only [List.map_nil, List.sum_nil, Nat.zero_add]; omega
    | cons g₀ gs' =>
        have hwBUD' : State.get w BUD = List.replicate (gs'.length + 1) 1 := by
          rw [hwBUD, hBUD, List.length_cons]
        have hbudne : gs'.length + 1 ≠ 0 := by omega
        have hg0pos : 1 ≤ formula_size g₀ := formula_size_pos g₀
        have hsumdecomp : ((g₀ :: gs').map formula_size).sum
            = formula_size g₀ + (gs'.map formula_size).sum := by
          simp [List.map_cons, List.sum_cons]
        have hmin : min i (formula_size g) = i := by omega
        have hmin1 : min (i + 1) (formula_size g) = i + 1 := by omega
        have hwT' : State.get w T = List.replicate (min i (formula_size g)) 1 := by rw [hwT, hT]
        have hSCtail : State.get w SC2 = serF g₀ ++ ((gs'.map serF).flatten ++ rest) := by
          rw [hwSC2, hSC2]; simp [List.map_cons, List.flatten_cons, List.append_assoc]
        cases g₀ with
        | ftrue =>
            have hSCt : State.get w SC2 = 0 :: 0 :: ((gs'.map serF).flatten ++ rest) := by
              rw [hSCtail]; rfl
            obtain ⟨hbSC, hbBUD, hbT⟩ :=
              budgetBody_ftrue w _ (gs'.length + 1) (min i (formula_size g)) hbudne hwBUD' hSCt hwT'
            refine ⟨gs', ?_, ?_, ?_, ?_⟩
            · exact hbSC
            · rw [hbBUD, Nat.add_sub_cancel]
            · rw [hbT, hmin, hmin1]
            · rw [hmin1]; simp only [List.map_cons, List.sum_cons, formula_size] at hcons ⊢; omega
        | fvar v =>
            have hSCt : State.get w SC2
                = 1 :: 1 :: 1 :: (List.replicate v 1 ++ 0 :: ((gs'.map serF).flatten ++ rest)) := by
              rw [hSCtail]; simp [BinaryCCFSATFree.serF, List.append_assoc]
            obtain ⟨hbSC, hbBUD, hbT⟩ :=
              budgetBody_fvar w v _ (gs'.length + 1) (min i (formula_size g)) hbudne hwBUD' hSCt hwT'
            refine ⟨gs', ?_, ?_, ?_, ?_⟩
            · exact hbSC
            · rw [hbBUD, Nat.add_sub_cancel]
            · rw [hbT, hmin, hmin1]
            · rw [hmin1]; simp only [List.map_cons, List.sum_cons, formula_size] at hcons ⊢; omega
        | fand a b =>
            have hSCt : State.get w SC2
                = 0 :: 1 :: (serF a ++ serF b ++ ((gs'.map serF).flatten ++ rest)) := by
              rw [hSCtail]; simp [BinaryCCFSATFree.serF, List.append_assoc]
            obtain ⟨hbSC, hbBUD, hbT⟩ :=
              budgetBody_fand w _ (gs'.length + 1) (min i (formula_size g)) hbudne hwBUD' hSCt hwT'
            refine ⟨a :: b :: gs', ?_, ?_, ?_, ?_⟩
            · rw [hbSC]; simp [List.map_cons, List.flatten_cons, List.append_assoc]
            · rw [hbBUD, List.length_cons, List.length_cons]
            · rw [hbT, hmin, hmin1]
            · rw [hmin1]; simp only [List.map_cons, List.sum_cons, formula_size] at hcons ⊢; omega
        | forr a b =>
            have hSCt : State.get w SC2
                = 1 :: 0 :: (serF a ++ serF b ++ ((gs'.map serF).flatten ++ rest)) := by
              rw [hSCtail]; simp [BinaryCCFSATFree.serF, List.append_assoc]
            obtain ⟨hbSC, hbBUD, hbT⟩ :=
              budgetBody_forr w _ (gs'.length + 1) (min i (formula_size g)) hbudne hwBUD' hSCt hwT'
            refine ⟨a :: b :: gs', ?_, ?_, ?_, ?_⟩
            · rw [hbSC]; simp [List.map_cons, List.flatten_cons, List.append_assoc]
            · rw [hbBUD, List.length_cons, List.length_cons]
            · rw [hbT, hmin, hmin1]
            · rw [hmin1]; simp only [List.map_cons, List.sum_cons, formula_size] at hcons ⊢; omega
        | fneg a =>
            have hSCt : State.get w SC2
                = 1 :: 1 :: 0 :: (serF a ++ ((gs'.map serF).flatten ++ rest)) := by
              rw [hSCtail]; simp [BinaryCCFSATFree.serF, List.append_assoc]
            obtain ⟨hbSC, hbBUD, hbT⟩ :=
              budgetBody_fneg w _ (gs'.length + 1) (min i (formula_size g)) hbudne hwBUD' hSCt hwT'
            refine ⟨a :: gs', ?_, ?_, ?_, ?_⟩
            · rw [hbSC]; simp [List.map_cons, List.flatten_cons, List.append_assoc]
            · rw [hbBUD, List.length_cons]
            · rw [hbT, hmin, hmin1]
            · rw [hmin1]; simp only [List.map_cons, List.sum_cons, formula_size] at hcons ⊢; omega
  have hInv := Cmd.foldlState_range_induct budgetBody IDX2 (serF g ++ rest).length P0 M h0 hstep
  rw [hpre, Cmd.eval_forBnd, hP0SCAN]
  obtain ⟨⟨_, _, _, hTf, _⟩, hframef⟩ := hInv
  have hnge : formula_size g ≤ (serF g ++ rest).length := by
    rw [List.length_append]; have := formula_size_le_serF g; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hTf, show min (serF g ++ rest).length (formula_size g) = formula_size g from by omega]
  · rw [hframef SCAN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hP0SCAN]
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    rw [hframef r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, hP0frame r h1 h2 h3]

/-! ## The outer-loop token step (`tokenBody_run`) -/

/-- **One `tokenBody` iteration = one `scanClauses` token.** For `SCAN` beginning
with a valid token `serF g₀ ++ tail`, `tokenBody` emits `g₀`'s Tseytin gadget
(`tokHead b k g₀`, the right-child offset recovered by `subtreeScan_run` for
binary nodes) onto `CNFOUT`, grows `TALLY` by its clause count, advances the
token index `K`, and leaves `SCAN = tokRem g₀ tail`. `B` and every non-written
register are preserved (`Cmd.eval_get_of_not_writes`). -/
theorem tokenBody_run (s : State) (g₀ : formula) (b k : Nat) (tail : List Nat)
    (hSCAN : State.get s SCAN = serF g₀ ++ tail)
    (hB : State.get s B = List.replicate b 1)
    (hK : State.get s K = List.replicate k 1) :
    State.get (tokenBody.eval s) CNFOUT
        = State.get s CNFOUT ++ encodeCnf (tokHead b k g₀)
    ∧ State.get (tokenBody.eval s) TALLY
        = State.get s TALLY ++ List.replicate (tokHead b k g₀).length 1
    ∧ State.get (tokenBody.eval s) SCAN = tokRem g₀ tail
    ∧ State.get (tokenBody.eval s) K = List.replicate (k + 1) 1
    ∧ State.get (tokenBody.eval s) B = List.replicate b 1
    ∧ (∀ r : Var, r ∉ tokenBody.writes → State.get (tokenBody.eval s) r = State.get s r) := by
  -- guard fires (SCAN nonempty)
  have hguard : (Cmd.op (Op.nonEmpty NE SCAN)).eval s = s.set NE [1] := by
    rw [Cmd.eval_op, Op.eval, hSCAN]; cases g₀ <;> simp [BinaryCCFSATFree.serF]
  set s1 := s.set NE [1] with hs1
  have hs1B : State.get s1 B = List.replicate b 1 := by
    rw [hs1, State.get_set_ne _ _ _ _ (show B ≠ NE by decide), hB]
  have hs1K : State.get s1 K = List.replicate k 1 := by
    rw [hs1, State.get_set_ne _ _ _ _ (show K ≠ NE by decide), hK]
  have hs1SC : State.get s1 SCAN = serF g₀ ++ tail := by
    rw [hs1, State.get_set_ne _ _ _ _ (show SCAN ≠ NE by decide), hSCAN]
  -- common prefix: concat VA B K ;; copy VL VA ;; appendOne VL
  set c1 := s1.set VA (List.replicate (b + k) 1) with hc1
  have e1 : (Cmd.op (Op.concat VA B K)).eval s1 = c1 := by
    rw [Cmd.eval_op, Op.eval, hs1B, hs1K, ← List.replicate_add, hc1]
  set c3 := c1.set VL (List.replicate (b + k + 1) 1) with hc3
  have e2 : (Cmd.op (Op.copy VL VA)).eval c1 = c1.set VL (List.replicate (b + k) 1) := by
    rw [Cmd.eval_op, Op.eval, hc1, State.get_set_eq]
  have e3 : (Cmd.op (Op.appendOne VL)).eval (c1.set VL (List.replicate (b + k) 1)) = c3 := by
    rw [Cmd.eval_op, Op.eval, State.get_set_eq, hc3, State.set_set, ← List.replicate_succ']
  have hc3SC : State.get c3 SCAN = serF g₀ ++ tail := by
    rw [hc3, State.get_set_ne _ _ _ _ (show SCAN ≠ VL by decide), hc1,
      State.get_set_ne _ _ _ _ (show SCAN ≠ VA by decide), hs1SC]
  have hc3VA : State.get c3 VA = List.replicate (b + k) 1 := by
    rw [hc3, State.get_set_ne _ _ _ _ (show VA ≠ VL by decide), hc1, State.get_set_eq]
  have hc3VL : State.get c3 VL = List.replicate (b + k + 1) 1 := by rw [hc3, State.get_set_eq]
  have hc3K : State.get c3 K = List.replicate k 1 := by
    rw [hc3, State.get_set_ne _ _ _ _ (show K ≠ VL by decide), hc1,
      State.get_set_ne _ _ _ _ (show K ≠ VA by decide), hs1K]
  have hc3CNF : State.get c3 CNFOUT = State.get s CNFOUT := by
    rw [hc3, State.get_set_ne _ _ _ _ (show CNFOUT ≠ VL by decide), hc1,
      State.get_set_ne _ _ _ _ (show CNFOUT ≠ VA by decide), hs1,
      State.get_set_ne _ _ _ _ (show CNFOUT ≠ NE by decide)]
  have hc3TAL : State.get c3 TALLY = State.get s TALLY := by
    rw [hc3, State.get_set_ne _ _ _ _ (show TALLY ≠ VL by decide), hc1,
      State.get_set_ne _ _ _ _ (show TALLY ≠ VA by decide), hs1,
      State.get_set_ne _ _ _ _ (show TALLY ≠ NE by decide)]
  -- the frame + B are case-independent
  have hframe : ∀ r : Var, r ∉ tokenBody.writes → State.get (tokenBody.eval s) r = State.get s r :=
    fun r hr => Cmd.eval_get_of_not_writes _ _ _ hr
  have hBout : State.get (tokenBody.eval s) B = List.replicate b 1 := by
    rw [hframe B (by decide), hB]
  have hmain : State.get (tokenBody.eval s) CNFOUT
        = State.get s CNFOUT ++ encodeCnf (tokHead b k g₀)
      ∧ State.get (tokenBody.eval s) TALLY
        = State.get s TALLY ++ List.replicate (tokHead b k g₀).length 1
      ∧ State.get (tokenBody.eval s) SCAN = tokRem g₀ tail
      ∧ State.get (tokenBody.eval s) K = List.replicate (k + 1) 1 := by
    cases g₀ with
    | ftrue =>
        have hSC : State.get c3 SCAN = 0 :: 0 :: tail := by rw [hc3SC]; rfl
        set c5 := (c3.set H1 [0]).set SCAN (0 :: tail) with hc5
        have e4 : (Cmd.op (Op.head H1 SCAN)).eval c3 = c3.set H1 [0] := by
          rw [Cmd.eval_op, Op.eval, hSC]
        have e5 : (Cmd.op (Op.tail SCAN SCAN)).eval (c3.set H1 [0]) = c5 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H1 by decide), hSC,
            List.tail_cons, hc5]
        have hc5SC : State.get c5 SCAN = 0 :: tail := by rw [hc5, State.get_set_eq]
        set c7 := (c5.set H2 [0]).set SCAN tail with hc7
        have e6 : (Cmd.op (Op.head H2 SCAN)).eval c5 = c5.set H2 [0] := by
          rw [Cmd.eval_op, Op.eval, hc5SC]
        have e7 : (Cmd.op (Op.tail SCAN SCAN)).eval (c5.set H2 [0]) = c7 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H2 by decide), hc5SC,
            List.tail_cons, hc7]
        have hc7H1 : State.get c7 H1 = [0] := by
          rw [hc7, State.get_set_ne _ _ _ _ (show H1 ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show H1 ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show H1 ≠ SCAN by decide), State.get_set_eq]
        have hc7H2 : State.get c7 H2 = [0] := by
          rw [hc7, State.get_set_ne _ _ _ _ (show H2 ≠ SCAN by decide), State.get_set_eq]
        have hc7VA : State.get c7 VA = List.replicate (b + k) 1 := by
          rw [hc7, State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H1 by decide), hc3VA]
        have hc7CNF : State.get c7 CNFOUT = State.get s CNFOUT := by
          rw [hc7, State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H1 by decide), hc3CNF]
        have hc7TAL : State.get c7 TALLY = State.get s TALLY := by
          rw [hc7, State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H1 by decide), hc3TAL]
        have hc7K : State.get c7 K = List.replicate k 1 := by
          rw [hc7, State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H1 by decide), hc3K]
        have hc7SCo : State.get c7 SCAN = tail := by rw [hc7, State.get_set_eq]
        have heval : tokenBody.eval s = (Cmd.op (Op.appendOne K)).eval (emitTrueG.eval c7) := by
          unfold tokenBody
          rw [Cmd.eval_seq, hguard, Cmd.eval_ifBit_true _ _ _ _ (by rw [State.get_set_eq]),
            Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
            Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq,
            Cmd.eval_ifBit_false _ _ _ _ (by rw [hc7H1]; decide),
            Cmd.eval_ifBit_false _ _ _ _ (by rw [hc7H2]; decide)]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ K by decide),
            emitTrueG_cnfout c7 (b + k) hc7VA, hc7CNF]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show TALLY ≠ K by decide),
            emitTrueG_tally c7, hc7TAL]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show SCAN ≠ K by decide),
            emitTrueG_frame c7 SCAN (by decide) (by decide), hc7SCo]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval, State.get_set_eq,
            emitTrueG_frame c7 K (by decide) (by decide), hc7K, ← List.replicate_succ']
    | fneg a =>
        have hSC : State.get c3 SCAN = 1 :: 1 :: 0 :: (serF a ++ tail) := by
          rw [hc3SC]; simp [BinaryCCFSATFree.serF]
        set c5 := (c3.set H1 [1]).set SCAN (1 :: 0 :: (serF a ++ tail)) with hc5
        have e4 : (Cmd.op (Op.head H1 SCAN)).eval c3 = c3.set H1 [1] := by
          rw [Cmd.eval_op, Op.eval, hSC]
        have e5 : (Cmd.op (Op.tail SCAN SCAN)).eval (c3.set H1 [1]) = c5 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H1 by decide), hSC,
            List.tail_cons, hc5]
        have hc5SC : State.get c5 SCAN = 1 :: 0 :: (serF a ++ tail) := by
          rw [hc5, State.get_set_eq]
        set c7 := (c5.set H2 [1]).set SCAN (0 :: (serF a ++ tail)) with hc7
        have e6 : (Cmd.op (Op.head H2 SCAN)).eval c5 = c5.set H2 [1] := by
          rw [Cmd.eval_op, Op.eval, hc5SC]
        have e7 : (Cmd.op (Op.tail SCAN SCAN)).eval (c5.set H2 [1]) = c7 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H2 by decide), hc5SC,
            List.tail_cons, hc7]
        have hc7SC : State.get c7 SCAN = 0 :: (serF a ++ tail) := by rw [hc7, State.get_set_eq]
        have hc7H1 : State.get c7 H1 = [1] := by
          rw [hc7, State.get_set_ne _ _ _ _ (show H1 ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show H1 ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show H1 ≠ SCAN by decide), State.get_set_eq]
        have hc7H2 : State.get c7 H2 = [1] := by
          rw [hc7, State.get_set_ne _ _ _ _ (show H2 ≠ SCAN by decide), State.get_set_eq]
        -- read H3 = [0], SCAN → serF a ++ tail
        set c9 := (c7.set H3 [0]).set SCAN (serF a ++ tail) with hc9
        have e8 : (Cmd.op (Op.head H3 SCAN)).eval c7 = c7.set H3 [0] := by
          rw [Cmd.eval_op, Op.eval, hc7SC]
        have e9 : (Cmd.op (Op.tail SCAN SCAN)).eval (c7.set H3 [0]) = c9 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H3 by decide), hc7SC,
            List.tail_cons, hc9]
        have hc9H3 : State.get c9 H3 = [0] := by
          rw [hc9, State.get_set_ne _ _ _ _ (show H3 ≠ SCAN by decide), State.get_set_eq]
        have hc9VA : State.get c9 VA = List.replicate (b + k) 1 := by
          rw [hc9, State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H3 by decide), hc7,
            State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H1 by decide), hc3VA]
        have hc9VL : State.get c9 VL = List.replicate (b + k + 1) 1 := by
          rw [hc9, State.get_set_ne _ _ _ _ (show VL ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VL ≠ H3 by decide), hc7,
            State.get_set_ne _ _ _ _ (show VL ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VL ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show VL ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VL ≠ H1 by decide), hc3VL]
        have hc9CNF : State.get c9 CNFOUT = State.get s CNFOUT := by
          rw [hc9, State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H3 by decide), hc7,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H1 by decide), hc3CNF]
        have hc9TAL : State.get c9 TALLY = State.get s TALLY := by
          rw [hc9, State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H3 by decide), hc7,
            State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H1 by decide), hc3TAL]
        have hc9K : State.get c9 K = List.replicate k 1 := by
          rw [hc9, State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H3 by decide), hc7,
            State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H1 by decide), hc3K]
        have hc9SCo : State.get c9 SCAN = serF a ++ tail := by rw [hc9, State.get_set_eq]
        have heval : tokenBody.eval s = (Cmd.op (Op.appendOne K)).eval (emitNotG.eval c9) := by
          unfold tokenBody
          rw [Cmd.eval_seq, hguard, Cmd.eval_ifBit_true _ _ _ _ (by rw [State.get_set_eq]),
            Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
            Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq,
            Cmd.eval_ifBit_true _ _ _ _ hc7H1, Cmd.eval_ifBit_true _ _ _ _ hc7H2,
            Cmd.eval_seq, e8, Cmd.eval_seq, e9,
            Cmd.eval_ifBit_false _ _ _ _ (by rw [hc9H3]; decide)]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ K by decide),
            emitNotG_cnfout c9 (b + k) (b + k + 1) hc9VA hc9VL, hc9CNF]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show TALLY ≠ K by decide), emitNotG_tally c9, hc9TAL]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show SCAN ≠ K by decide),
            emitNotG_frame c9 SCAN (by decide) (by decide), hc9SCo]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval, State.get_set_eq,
            emitNotG_frame c9 K (by decide) (by decide), hc9K, ← List.replicate_succ']
    | fand a b' =>
        have hSC : State.get c3 SCAN = 0 :: 1 :: (serF a ++ serF b' ++ tail) := by
          rw [hc3SC]; simp [BinaryCCFSATFree.serF, List.append_assoc]
        set c5 := (c3.set H1 [0]).set SCAN (1 :: (serF a ++ serF b' ++ tail)) with hc5
        have e4 : (Cmd.op (Op.head H1 SCAN)).eval c3 = c3.set H1 [0] := by
          rw [Cmd.eval_op, Op.eval, hSC]
        have e5 : (Cmd.op (Op.tail SCAN SCAN)).eval (c3.set H1 [0]) = c5 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H1 by decide), hSC,
            List.tail_cons, hc5]
        have hc5SC : State.get c5 SCAN = 1 :: (serF a ++ serF b' ++ tail) := by
          rw [hc5, State.get_set_eq]
        set c7 := (c5.set H2 [1]).set SCAN (serF a ++ serF b' ++ tail) with hc7
        have e6 : (Cmd.op (Op.head H2 SCAN)).eval c5 = c5.set H2 [1] := by
          rw [Cmd.eval_op, Op.eval, hc5SC]
        have e7 : (Cmd.op (Op.tail SCAN SCAN)).eval (c5.set H2 [1]) = c7 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H2 by decide), hc5SC,
            List.tail_cons, hc7]
        have hc7H1 : State.get c7 H1 = [0] := by
          rw [hc7, State.get_set_ne _ _ _ _ (show H1 ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show H1 ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show H1 ≠ SCAN by decide), State.get_set_eq]
        have hc7H2 : State.get c7 H2 = [1] := by
          rw [hc7, State.get_set_ne _ _ _ _ (show H2 ≠ SCAN by decide), State.get_set_eq]
        have hc7SCo : State.get c7 SCAN = serF a ++ serF b' ++ tail := by
          rw [hc7, State.get_set_eq]
        have hc7VA : State.get c7 VA = List.replicate (b + k) 1 := by
          rw [hc7, State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H1 by decide), hc3VA]
        have hc7VL : State.get c7 VL = List.replicate (b + k + 1) 1 := by
          rw [hc7, State.get_set_ne _ _ _ _ (show VL ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VL ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show VL ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VL ≠ H1 by decide), hc3VL]
        have hc7CNF : State.get c7 CNFOUT = State.get s CNFOUT := by
          rw [hc7, State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H1 by decide), hc3CNF]
        have hc7TAL : State.get c7 TALLY = State.get s TALLY := by
          rw [hc7, State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H1 by decide), hc3TAL]
        have hc7K : State.get c7 K = List.replicate k 1 := by
          rw [hc7, State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H1 by decide), hc3K]
        -- subtreeScan on the children stream
        obtain ⟨hST, hSSCAN, hSframe⟩ := subtreeScan_run c7 a (serF b' ++ tail)
          (by rw [hc7SCo, List.append_assoc])
        set cS := subtreeScan.eval c7 with hcS
        have hcSVL : State.get cS VL = List.replicate (b + k + 1) 1 := by
          rw [hSframe VL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hc7VL]
        have hcSVA : State.get cS VA = List.replicate (b + k) 1 := by
          rw [hSframe VA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hc7VA]
        have hcSCNF : State.get cS CNFOUT = State.get s CNFOUT := by
          rw [hSframe CNFOUT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hc7CNF]
        have hcSTAL : State.get cS TALLY = State.get s TALLY := by
          rw [hSframe TALLY (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hc7TAL]
        have hcSK : State.get cS K = List.replicate k 1 := by
          rw [hSframe K (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hc7K]
        set cV := cS.set VR (List.replicate (b + k + 1 + formula_size a) 1) with hcV
        have eVR : (Cmd.op (Op.concat VR VL T)).eval cS = cV := by
          rw [Cmd.eval_op, Op.eval, hcSVL, hST, ← List.replicate_add, hcV]
        have hcVVA : State.get cV VA = List.replicate (b + k) 1 := by
          rw [hcV, State.get_set_ne _ _ _ _ (show VA ≠ VR by decide), hcSVA]
        have hcVVL : State.get cV VL = List.replicate (b + k + 1) 1 := by
          rw [hcV, State.get_set_ne _ _ _ _ (show VL ≠ VR by decide), hcSVL]
        have hcVVR : State.get cV VR = List.replicate (b + k + 1 + formula_size a) 1 := by
          rw [hcV, State.get_set_eq]
        have hcVCNF : State.get cV CNFOUT = State.get s CNFOUT := by
          rw [hcV, State.get_set_ne _ _ _ _ (show CNFOUT ≠ VR by decide), hcSCNF]
        have hcVTAL : State.get cV TALLY = State.get s TALLY := by
          rw [hcV, State.get_set_ne _ _ _ _ (show TALLY ≠ VR by decide), hcSTAL]
        have hcVK : State.get cV K = List.replicate k 1 := by
          rw [hcV, State.get_set_ne _ _ _ _ (show K ≠ VR by decide), hcSK]
        have hcVSC : State.get cV SCAN = serF a ++ (serF b' ++ tail) := by
          rw [hcV, State.get_set_ne _ _ _ _ (show SCAN ≠ VR by decide), hSSCAN]
        have heval : tokenBody.eval s = (Cmd.op (Op.appendOne K)).eval (emitAndG.eval cV) := by
          unfold tokenBody
          rw [Cmd.eval_seq, hguard, Cmd.eval_ifBit_true _ _ _ _ (by rw [State.get_set_eq]),
            Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
            Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq,
            Cmd.eval_ifBit_false _ _ _ _ (by rw [hc7H1]; decide),
            Cmd.eval_ifBit_true _ _ _ _ hc7H2, Cmd.eval_seq, ← hcS, Cmd.eval_seq, eVR]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ K by decide),
            emitAndG_cnfout cV (b + k) (b + k + 1) (b + k + 1 + formula_size a)
              hcVVA hcVVL hcVVR, hcVCNF]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show TALLY ≠ K by decide), emitAndG_tally cV, hcVTAL]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show SCAN ≠ K by decide),
            emitAndG_frame cV SCAN (by decide) (by decide), hcVSC]
          simp [tokRem, List.append_assoc]
        · rw [heval, Cmd.eval_op, Op.eval, State.get_set_eq,
            emitAndG_frame cV K (by decide) (by decide), hcVK, ← List.replicate_succ']
    | forr a b' =>
        have hSC : State.get c3 SCAN = 1 :: 0 :: (serF a ++ serF b' ++ tail) := by
          rw [hc3SC]; simp [BinaryCCFSATFree.serF, List.append_assoc]
        set c5 := (c3.set H1 [1]).set SCAN (0 :: (serF a ++ serF b' ++ tail)) with hc5
        have e4 : (Cmd.op (Op.head H1 SCAN)).eval c3 = c3.set H1 [1] := by
          rw [Cmd.eval_op, Op.eval, hSC]
        have e5 : (Cmd.op (Op.tail SCAN SCAN)).eval (c3.set H1 [1]) = c5 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H1 by decide), hSC,
            List.tail_cons, hc5]
        have hc5SC : State.get c5 SCAN = 0 :: (serF a ++ serF b' ++ tail) := by
          rw [hc5, State.get_set_eq]
        set c7 := (c5.set H2 [0]).set SCAN (serF a ++ serF b' ++ tail) with hc7
        have e6 : (Cmd.op (Op.head H2 SCAN)).eval c5 = c5.set H2 [0] := by
          rw [Cmd.eval_op, Op.eval, hc5SC]
        have e7 : (Cmd.op (Op.tail SCAN SCAN)).eval (c5.set H2 [0]) = c7 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H2 by decide), hc5SC,
            List.tail_cons, hc7]
        have hc7H1 : State.get c7 H1 = [1] := by
          rw [hc7, State.get_set_ne _ _ _ _ (show H1 ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show H1 ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show H1 ≠ SCAN by decide), State.get_set_eq]
        have hc7H2 : State.get c7 H2 = [0] := by
          rw [hc7, State.get_set_ne _ _ _ _ (show H2 ≠ SCAN by decide), State.get_set_eq]
        have hc7SCo : State.get c7 SCAN = serF a ++ serF b' ++ tail := by
          rw [hc7, State.get_set_eq]
        have hc7VA : State.get c7 VA = List.replicate (b + k) 1 := by
          rw [hc7, State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H1 by decide), hc3VA]
        have hc7VL : State.get c7 VL = List.replicate (b + k + 1) 1 := by
          rw [hc7, State.get_set_ne _ _ _ _ (show VL ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VL ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show VL ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VL ≠ H1 by decide), hc3VL]
        have hc7CNF : State.get c7 CNFOUT = State.get s CNFOUT := by
          rw [hc7, State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H1 by decide), hc3CNF]
        have hc7TAL : State.get c7 TALLY = State.get s TALLY := by
          rw [hc7, State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H1 by decide), hc3TAL]
        have hc7K : State.get c7 K = List.replicate k 1 := by
          rw [hc7, State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H1 by decide), hc3K]
        obtain ⟨hST, hSSCAN, hSframe⟩ := subtreeScan_run c7 a (serF b' ++ tail)
          (by rw [hc7SCo, List.append_assoc])
        set cS := subtreeScan.eval c7 with hcS
        have hcSVL : State.get cS VL = List.replicate (b + k + 1) 1 := by
          rw [hSframe VL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hc7VL]
        have hcSVA : State.get cS VA = List.replicate (b + k) 1 := by
          rw [hSframe VA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hc7VA]
        have hcSCNF : State.get cS CNFOUT = State.get s CNFOUT := by
          rw [hSframe CNFOUT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hc7CNF]
        have hcSTAL : State.get cS TALLY = State.get s TALLY := by
          rw [hSframe TALLY (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hc7TAL]
        have hcSK : State.get cS K = List.replicate k 1 := by
          rw [hSframe K (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hc7K]
        set cV := cS.set VR (List.replicate (b + k + 1 + formula_size a) 1) with hcV
        have eVR : (Cmd.op (Op.concat VR VL T)).eval cS = cV := by
          rw [Cmd.eval_op, Op.eval, hcSVL, hST, ← List.replicate_add, hcV]
        have hcVVA : State.get cV VA = List.replicate (b + k) 1 := by
          rw [hcV, State.get_set_ne _ _ _ _ (show VA ≠ VR by decide), hcSVA]
        have hcVVL : State.get cV VL = List.replicate (b + k + 1) 1 := by
          rw [hcV, State.get_set_ne _ _ _ _ (show VL ≠ VR by decide), hcSVL]
        have hcVVR : State.get cV VR = List.replicate (b + k + 1 + formula_size a) 1 := by
          rw [hcV, State.get_set_eq]
        have hcVCNF : State.get cV CNFOUT = State.get s CNFOUT := by
          rw [hcV, State.get_set_ne _ _ _ _ (show CNFOUT ≠ VR by decide), hcSCNF]
        have hcVTAL : State.get cV TALLY = State.get s TALLY := by
          rw [hcV, State.get_set_ne _ _ _ _ (show TALLY ≠ VR by decide), hcSTAL]
        have hcVK : State.get cV K = List.replicate k 1 := by
          rw [hcV, State.get_set_ne _ _ _ _ (show K ≠ VR by decide), hcSK]
        have hcVSC : State.get cV SCAN = serF a ++ (serF b' ++ tail) := by
          rw [hcV, State.get_set_ne _ _ _ _ (show SCAN ≠ VR by decide), hSSCAN]
        have heval : tokenBody.eval s = (Cmd.op (Op.appendOne K)).eval (emitOrG.eval cV) := by
          unfold tokenBody
          rw [Cmd.eval_seq, hguard, Cmd.eval_ifBit_true _ _ _ _ (by rw [State.get_set_eq]),
            Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
            Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq,
            Cmd.eval_ifBit_true _ _ _ _ hc7H1,
            Cmd.eval_ifBit_false _ _ _ _ (by rw [hc7H2]; decide),
            Cmd.eval_seq, ← hcS, Cmd.eval_seq, eVR]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ K by decide),
            emitOrG_cnfout cV (b + k) (b + k + 1) (b + k + 1 + formula_size a)
              hcVVA hcVVL hcVVR, hcVCNF]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show TALLY ≠ K by decide), emitOrG_tally cV, hcVTAL]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show SCAN ≠ K by decide),
            emitOrG_frame cV SCAN (by decide) (by decide), hcVSC]
          simp [tokRem, List.append_assoc]
        · rw [heval, Cmd.eval_op, Op.eval, State.get_set_eq,
            emitOrG_frame cV K (by decide) (by decide), hcVK, ← List.replicate_succ']
    | fvar v =>
        have hSC : State.get c3 SCAN
            = 1 :: 1 :: 1 :: (List.replicate v 1 ++ 0 :: tail) := by
          rw [hc3SC]; simp [BinaryCCFSATFree.serF]
        set c5 := (c3.set H1 [1]).set SCAN (1 :: 1 :: (List.replicate v 1 ++ 0 :: tail)) with hc5
        have e4 : (Cmd.op (Op.head H1 SCAN)).eval c3 = c3.set H1 [1] := by
          rw [Cmd.eval_op, Op.eval, hSC]
        have e5 : (Cmd.op (Op.tail SCAN SCAN)).eval (c3.set H1 [1]) = c5 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H1 by decide), hSC,
            List.tail_cons, hc5]
        have hc5SC : State.get c5 SCAN = 1 :: 1 :: (List.replicate v 1 ++ 0 :: tail) := by
          rw [hc5, State.get_set_eq]
        set c7 := (c5.set H2 [1]).set SCAN (1 :: (List.replicate v 1 ++ 0 :: tail)) with hc7
        have e6 : (Cmd.op (Op.head H2 SCAN)).eval c5 = c5.set H2 [1] := by
          rw [Cmd.eval_op, Op.eval, hc5SC]
        have e7 : (Cmd.op (Op.tail SCAN SCAN)).eval (c5.set H2 [1]) = c7 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H2 by decide), hc5SC,
            List.tail_cons, hc7]
        have hc7SC : State.get c7 SCAN = 1 :: (List.replicate v 1 ++ 0 :: tail) := by
          rw [hc7, State.get_set_eq]
        have hc7H1 : State.get c7 H1 = [1] := by
          rw [hc7, State.get_set_ne _ _ _ _ (show H1 ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show H1 ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show H1 ≠ SCAN by decide), State.get_set_eq]
        have hc7H2 : State.get c7 H2 = [1] := by
          rw [hc7, State.get_set_ne _ _ _ _ (show H2 ≠ SCAN by decide), State.get_set_eq]
        set c9 := (c7.set H3 [1]).set SCAN (List.replicate v 1 ++ 0 :: tail) with hc9
        have e8 : (Cmd.op (Op.head H3 SCAN)).eval c7 = c7.set H3 [1] := by
          rw [Cmd.eval_op, Op.eval, hc7SC]
        have e9 : (Cmd.op (Op.tail SCAN SCAN)).eval (c7.set H3 [1]) = c9 := by
          rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H3 by decide), hc7SC,
            List.tail_cons, hc9]
        have hc9H3 : State.get c9 H3 = [1] := by
          rw [hc9, State.get_set_ne _ _ _ _ (show H3 ≠ SCAN by decide), State.get_set_eq]
        have hc9VA : State.get c9 VA = List.replicate (b + k) 1 := by
          rw [hc9, State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H3 by decide), hc7,
            State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show VA ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ H1 by decide), hc3VA]
        have hc9SCo : State.get c9 SCAN = List.replicate v 1 ++ 0 :: tail := by
          rw [hc9, State.get_set_eq]
        -- clear VREG, clear DN, then drain the payload into VREG
        set cclr := (c9.set VREG []).set DN [] with hcclr
        have e10 : (Cmd.op (Op.clear VREG)).eval c9 = c9.set VREG [] := by
          rw [Cmd.eval_op, Op.eval]
        have e11 : (Cmd.op (Op.clear DN)).eval (c9.set VREG []) = cclr := by
          rw [Cmd.eval_op, Op.eval, hcclr]
        have hcclrSC : State.get cclr SCAN = List.replicate v 1 ++ 0 :: tail := by
          rw [hcclr, State.get_set_ne _ _ _ _ (show SCAN ≠ DN by decide),
            State.get_set_ne _ _ _ _ (show SCAN ≠ VREG by decide), hc9SCo]
        have hcclrVREG : State.get cclr VREG = [] := by
          rw [hcclr, State.get_set_ne _ _ _ _ (show VREG ≠ DN by decide), State.get_set_eq]
        have hcclrDN : State.get cclr DN = [] := by rw [hcclr, State.get_set_eq]
        obtain ⟨hDSCAN, hDVREG, _hDDN, hDframe⟩ :=
          drainVar_run cclr v tail hcclrSC hcclrVREG hcclrDN
        set cD := (Cmd.forBnd IDX3 SCAN drainVarBody).eval cclr with hcD
        have hcDVA : State.get cD VA = List.replicate (b + k) 1 := by
          rw [hDframe VA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hcclr, State.get_set_ne _ _ _ _ (show VA ≠ DN by decide),
            State.get_set_ne _ _ _ _ (show VA ≠ VREG by decide), hc9VA]
        have hcDCNF : State.get cD CNFOUT = State.get s CNFOUT := by
          rw [hDframe CNFOUT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hcclr, State.get_set_ne _ _ _ _ (show CNFOUT ≠ DN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ VREG by decide), hc9,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H3 by decide), hc7,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ H1 by decide), hc3CNF]
        have hcDTAL : State.get cD TALLY = State.get s TALLY := by
          rw [hDframe TALLY (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hcclr, State.get_set_ne _ _ _ _ (show TALLY ≠ DN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ VREG by decide), hc9,
            State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H3 by decide), hc7,
            State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show TALLY ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ H1 by decide), hc3TAL]
        have hcDK : State.get cD K = List.replicate k 1 := by
          rw [hDframe K (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hcclr, State.get_set_ne _ _ _ _ (show K ≠ DN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ VREG by decide), hc9,
            State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H3 by decide), hc7,
            State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H2 by decide), hc5,
            State.get_set_ne _ _ _ _ (show K ≠ SCAN by decide),
            State.get_set_ne _ _ _ _ (show K ≠ H1 by decide), hc3K]
        have heval : tokenBody.eval s = (Cmd.op (Op.appendOne K)).eval (emitEquivG.eval cD) := by
          unfold tokenBody
          rw [Cmd.eval_seq, hguard, Cmd.eval_ifBit_true _ _ _ _ (by rw [State.get_set_eq]),
            Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
            Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq,
            Cmd.eval_ifBit_true _ _ _ _ hc7H1, Cmd.eval_ifBit_true _ _ _ _ hc7H2,
            Cmd.eval_seq, e8, Cmd.eval_seq, e9, Cmd.eval_ifBit_true _ _ _ _ hc9H3,
            Cmd.eval_seq, e10, Cmd.eval_seq, e11, Cmd.eval_seq, ← hcD]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ K by decide),
            emitEquivG_cnfout cD v (b + k) hDVREG hcDVA, hcDCNF]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show TALLY ≠ K by decide), emitEquivG_tally cD, hcDTAL]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval,
            State.get_set_ne _ _ _ _ (show SCAN ≠ K by decide),
            emitEquivG_frame cD SCAN (by decide) (by decide), hDSCAN]
          rfl
        · rw [heval, Cmd.eval_op, Op.eval, State.get_set_eq,
            emitEquivG_frame cD K (by decide) (by decide), hcDK, ← List.replicate_succ']
  exact ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2, hBout, hframe⟩

/-! ## The outer token loop (`outerLoop_run`) -/

/-- **The outer `forBnd IDX1 SERF tokenBody` loop.** Folds `tokenBody_run` over
the Dyck forest of remaining subtrees (starting `[f]`): after all `|serF f|`
iterations, `CNFOUT`/`TALLY` hold the encoding of `scanClauses` over the whole
stream (the body of `mScan`, sans the top clause). The idle tail iterations
(stream exhausted) freeze the invariant via the guard. -/
theorem outerLoop_run (u : State) (f : formula) (C0 T0 : List Nat)
    (hSCAN : State.get u SCAN = serF f)
    (hK : State.get u K = [])
    (hCNF : State.get u CNFOUT = C0)
    (hTAL : State.get u TALLY = T0)
    (hB : State.get u B = List.replicate (serF f).length 1)
    (hbound : State.get u SERF = serF f) :
    State.get ((Cmd.forBnd IDX1 SERF tokenBody).eval u) CNFOUT
        = C0 ++ encodeCnf (scanClauses (serF f).length ((serF f).length + 1) 0 (serF f))
    ∧ State.get ((Cmd.forBnd IDX1 SERF tokenBody).eval u) TALLY
        = T0 ++ List.replicate
            (scanClauses (serF f).length ((serF f).length + 1) 0 (serF f)).length 1 := by
  -- idle behaviour on an exhausted stream
  have hidle : ∀ t : State, State.get t SCAN = [] →
      tokenBody.eval t = (t.set NE [0]).set SKIP [] := by
    intro t ht
    unfold tokenBody
    have e0 : (Cmd.op (Op.nonEmpty NE SCAN)).eval t = t.set NE [0] := by
      rw [Cmd.eval_op, Op.eval, ht]; rfl
    rw [Cmd.eval_seq, e0, Cmd.eval_ifBit_false _ _ _ _ (by rw [State.get_set_eq]; decide),
      nop, Cmd.eval_op, Op.eval]
  set L := (serF f).length with hL
  have hfsL : formula_size f ≤ L := by rw [hL]; exact formula_size_le_serF f
  set M : Nat → State → Prop := fun i st =>
    (∃ (hs : List formula) (done : cnf),
        State.get st SCAN = (hs.map serF).flatten
      ∧ State.get st K = List.replicate (min i (formula_size f)) 1
      ∧ State.get st CNFOUT = C0 ++ encodeCnf done
      ∧ State.get st TALLY = T0 ++ List.replicate done.length 1
      ∧ State.get st B = List.replicate L 1
      ∧ (hs.map formula_size).sum + min i (formula_size f) = formula_size f
      ∧ scanClauses L (L + 1) 0 (serF f)
          = done ++ scanClauses L (L + 1 - min i (formula_size f))
              (min i (formula_size f)) ((hs.map serF).flatten)) with hMdef
  have h0 : M 0 u := by
    refine ⟨[f], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSCAN]; simp [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
    · rw [hK]; simp
    · rw [hCNF]; simp [encodeCnf]
    · rw [hTAL]; simp
    · rw [hB]
    · simp [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    · simp [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
  have hstep : ∀ i st, i < (State.get u SERF).length → M i st →
      M (i + 1) (tokenBody.eval (st.set IDX1 (List.replicate i 1))) := by
    intro i st _ hM
    obtain ⟨hs, done, hSC, hKi, hCN, hTL, hBi, hcons, hscan⟩ := hM
    set w := st.set IDX1 (List.replicate i 1) with hw
    have hwSC : State.get w SCAN = (hs.map serF).flatten := by
      rw [hw, State.get_set_ne _ _ _ _ (show SCAN ≠ IDX1 by decide), hSC]
    have hwK : State.get w K = List.replicate (min i (formula_size f)) 1 := by
      rw [hw, State.get_set_ne _ _ _ _ (show K ≠ IDX1 by decide), hKi]
    have hwCN : State.get w CNFOUT = C0 ++ encodeCnf done := by
      rw [hw, State.get_set_ne _ _ _ _ (show CNFOUT ≠ IDX1 by decide), hCN]
    have hwTL : State.get w TALLY = T0 ++ List.replicate done.length 1 := by
      rw [hw, State.get_set_ne _ _ _ _ (show TALLY ≠ IDX1 by decide), hTL]
    have hwB : State.get w B = List.replicate L 1 := by
      rw [hw, State.get_set_ne _ _ _ _ (show B ≠ IDX1 by decide), hBi]
    cases hs with
    | nil =>
        -- exhausted: idle step, invariant frozen
        have hSCnil : State.get w SCAN = [] := by rw [hwSC]; simp
        have hmineq : min i (formula_size f) = formula_size f := by
          simp only [List.map_nil, List.sum_nil, Nat.zero_add] at hcons; omega
        rw [hidle w hSCnil]
        refine ⟨[], done, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (show SCAN ≠ SKIP by decide),
            State.get_set_ne _ _ _ _ (show SCAN ≠ NE by decide), hwSC]
        · rw [State.get_set_ne _ _ _ _ (show K ≠ SKIP by decide),
            State.get_set_ne _ _ _ _ (show K ≠ NE by decide), hwK]
          congr 1; omega
        · rw [State.get_set_ne _ _ _ _ (show CNFOUT ≠ SKIP by decide),
            State.get_set_ne _ _ _ _ (show CNFOUT ≠ NE by decide), hwCN]
        · rw [State.get_set_ne _ _ _ _ (show TALLY ≠ SKIP by decide),
            State.get_set_ne _ _ _ _ (show TALLY ≠ NE by decide), hwTL]
        · rw [State.get_set_ne _ _ _ _ (show B ≠ SKIP by decide),
            State.get_set_ne _ _ _ _ (show B ≠ NE by decide), hwB]
        · simp only [List.map_nil, List.sum_nil, Nat.zero_add]; omega
        · rw [show min (i + 1) (formula_size f) = formula_size f from by omega]
          rw [show min i (formula_size f) = formula_size f from hmineq] at hscan
          exact hscan
    | cons g₀ hs' =>
        have hg0pos : 1 ≤ formula_size g₀ := formula_size_pos g₀
        have hsumdec : ((g₀ :: hs').map formula_size).sum
            = formula_size g₀ + (hs'.map formula_size).sum := by
          simp [List.map_cons, List.sum_cons]
        have hi_lt : i < formula_size f := by omega
        have hmin : min i (formula_size f) = i := by omega
        have hmin1 : min (i + 1) (formula_size f) = i + 1 := by omega
        have hmle : min i (formula_size f) ≤ L := by omega
        have hwSC' : State.get w SCAN = serF g₀ ++ (hs'.map serF).flatten := by
          rw [hwSC]; simp [List.map_cons, List.flatten_cons]
        obtain ⟨hbCN, hbTL, hbSC, hbK, hbB, _⟩ :=
          tokenBody_run w g₀ L (min i (formula_size f)) ((hs'.map serF).flatten) hwSC' hwB hwK
        refine ⟨tokForest g₀ hs', done ++ tokHead L (min i (formula_size f)) g₀,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hbSC, tokForest_flatten]
        · rw [hbK, hmin, hmin1]
        · rw [hbCN, hwCN, encodeCnf_append, List.append_assoc]
        · rw [hbTL, hwTL, List.length_append, List.append_assoc,
            ← List.replicate_add]
        · rw [hbB]
        · rw [hmin1]
          have := tokForest_sum g₀ hs'; simp only [hsumdec] at hcons ⊢; omega
        · rw [hmin] at hscan
          rw [hmin, hmin1, hscan,
            show (List.map serF (g₀ :: hs')).flatten = serF g₀ ++ (hs'.map serF).flatten from by
              simp [List.map_cons, List.flatten_cons],
            show L + 1 - i = (L - i) + 1 from by omega,
            scanClauses_tok L (L - i) i g₀ ((hs'.map serF).flatten),
            tokForest_flatten, show L + 1 - (i + 1) = L - i from by omega, List.append_assoc]
  have hInv := Cmd.foldlState_range_induct tokenBody IDX1 (State.get u SERF).length u M h0 hstep
  rw [Cmd.eval_forBnd]
  rw [hbound] at hInv ⊢
  obtain ⟨hs, done, hSC, hKi, hCN, hTL, hBi, hcons, hscan⟩ := hInv
  -- at i = L, min L (fs f) = fs f, so hs = []
  have hmineq : min L (formula_size f) = formula_size f := by omega
  have hsum0 : (hs.map formula_size).sum = 0 := by rw [hmineq] at hcons; omega
  have hnil : hs = [] := by
    cases hs with
    | nil => rfl
    | cons g₀ hs' =>
        exfalso
        have := formula_size_pos g₀
        simp [List.map_cons, List.sum_cons] at hsum0; omega
  subst hnil
  rw [hmineq] at hscan
  simp only [List.map_nil, List.flatten_nil] at hscan
  rw [scanClauses_nil, List.append_nil] at hscan
  refine ⟨?_, ?_⟩
  · rw [hCN, hscan]
  · rw [hTL, hscan]

end FSATSATFree
