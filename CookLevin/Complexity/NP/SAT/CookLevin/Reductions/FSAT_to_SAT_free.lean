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

end FSATSATFree
