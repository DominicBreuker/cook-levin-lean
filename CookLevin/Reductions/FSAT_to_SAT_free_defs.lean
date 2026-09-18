import CookLevin.SAT.FSAT_to_SAT_pre
import CookLevin.Reductions.BinaryCC_to_FSAT_free_defs
import CookLevin.SAT.EvalCnfCmd
import CookLevin.Lang.NumGadgets
import CookLevin.SAT.EvalCnfTM
import CookLevin.SAT.FSAT_to_SAT
import CookLevin.SAT.CnfSerialize

/-!
# FSAT to SAT: the program

`buildSAT` reads the serialized formula `serF f` from its input register and writes the
CNF `PreTseytin.preTseytin b f` (`SAT/FSAT_to_SAT_pre.lean`) in the encoding `encodeCnf`
into its output register, in one left-to-right pass with a positional variable counter.
`fsatToSat_correct` restates the correctness of the map on the serialized input.
-/

set_option autoImplicit false

namespace FSATSATFree

open CookLevin.Lang
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

/-- Decode the output cnf from the verifier-layout stream register.

It is `Serialize.dec` of one designated register, i.e. the canonical CNF parser
`CnfSerialize.decCnf`; it does not look at the input and the fallback `[]` is a constant. -/
def decodeOut (s : State) : cnf :=
  Serialize.decodeD ([] : cnf) (State.get s CNFOUT)

/-- The map the witness computes. -/
def fsatToSat (f : formula) : cnf := preTseytin (serF f).length f

/-- The machine-friendly fresh-variable base is valid: every original variable
is below the serialization length (an `fvar v` token alone carries `v + 4`
bits). This is what replaces the on-machine max computation. -/
theorem formula_maxVar_lt_serF_length (f : formula) :
    formula_maxVar f < (serF f).length := by
  -- NB: `omega`-hostile terrain — the `fvar` payload is `var`-typed (carrier
  -- opaque to omega) and `formula_maxVar` is a `Nat.max` (an omega atom), so
  -- the leaf/max steps are closed by term lemmas
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
`FSAT → SAT` reduction (axiom-clean; the `⪯p` witness's `correct` field). -/
theorem fsatToSat_correct (f : formula) : FSAT f ↔ SAT (fsatToSat f) :=
  preTseytin_correct f _ (formula_maxVar_lt_serF_length f)

/-! ## The pure positional-scan model

The machine's outer token loop and budget scan, as pure Lean functions. These mirror the
`Cmd` loops (`tokenBody`/`budgetBody`), so the run lemmas need only prove that the
machine folds compute these functions; `mScan_eq_fsatToSat` closes the gap. -/

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

/-- **The pure model equals the tree-recursive map** (`fsatToSat`). With it, the
run-lemma proof reduces to "the machine folds compute `mScan (serF f)`" — no tree
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

end FSATSATFree
