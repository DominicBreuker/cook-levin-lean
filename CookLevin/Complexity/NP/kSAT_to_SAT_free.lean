import Complexity.NP.kSAT_to_SAT
import Complexity.Complexity.Deciders.CliqueRelTM

set_option autoImplicit false

/-! # `inNP (kSAT 3)` through the FREE layer engine — the concrete re-encoder
(S3 linchpin, top-down target #1)

This file closes the first **live** `red_inNP` through the free-encoding layer
engine (`red_inNP_of_langFree`, `PolyTime.lean`): it supplies the engine's two
per-reduction inputs for the reduction `kSAT 3 → SAT`
(`kSAT_to_SAT_reduction 3`), both carried by ONE concrete `Cmd`:

1. **The re-encoder (`FreePrecomposeData`, blocker (a)).** `kCnf3Check` runs the
   reduction *on-machine* over the SAT verifier's bespoke input layout
   (`EvalCnfCmd.encodeState`): it parses the encoded CNF stream clause by
   clause (draining each literal's unary block with `CliqueRelTM.readNum`),
   counts each clause's literals in unary against `THREE = [1,1,1]`, and — if
   some clause fails `|C| = 3` — rewrites registers 1/2 to the layout of the
   canonical no-instance `[[]]`. The `bridge` law (register agreement below the
   verifier frame 16 with `encodeState (kSAT_to_SAT_reduction 3 N, a)`) is
   proven from the run lemma; design `#eval`-validated in
   `probes/KCnf3ReencoderProbe.lean`.

2. **The reduction as a program (`PolyTimeComputableLang`, blocker (b)).** The
   *same* `kCnf3Check` on the minimal 3-register layout
   `[[], replicate |N| 1, encodeCnf N]` is a free `PolyTimeComputableLang`
   witness for `kSAT_to_SAT_reduction 3` (the run lemma is stated over any
   base state carrying registers 1/2, so it serves both layouts).

The headline `inNP_kSAT3_free : inNP (kSAT 3)` is then one application of
`red_inNP_of_langFree`.

**⚠ Honesty discipline (risk note).** `FreePrecomposeData.eIn` and
`PolyTimeComputableLang.decodeOut` are *unconstrained functions*, so both
structures are trivially populatable by hiding the reduction inside the
encoding (`eIn := D.encodeIn ∘ gmap`, `mfc := no-op`) — the same
encoding-hides-computation weakness as S3 itself, one level up. This file
deliberately takes the honest instantiation: `eIn` is the verifier's own
natural pair layout (`encodeState`), `Wf.encodeIn` is the minimal natural
stream layout, and ALL reduction work (the `kCNF 3` decision and the
conditional rewrite) happens in the `Cmd`. Keep that discipline for every
future `FreePrecomposeData` until encodings are canonicalised. -/

namespace KSat3Free

open Complexity.Lang
open EvalCnfCmd (encodeLit encodeClause encodeCnf encodeAssgn encodeState
  CLAUSE_TALLY CNF_STREAM)

/-! ## Scratch registers

The verifier frame is `< 16`; all our scratch lives at `≥ 17` except the three
registers `CliqueRelTM.readNum`/`cSkip` pin: `HEAD = 15`, `INBLK = 16`,
`SKIPR = 26`. `HEAD` is the single below-16 register the program dirties; the
final `clear` scrubs it. -/

def SCAN  : Var := 17
def OK    : Var := 18
def THREE : Var := 19
def LCNT  : Var := 20
def CDONE : Var := 21
def RES   : Var := 22
def HEADC : Var := 23
def VALX  : Var := 24
def IDXO  : Var := 25
def IDXI  : Var := 27
def IDXV  : Var := 28

/-! ## The program -/

/-- One inner-loop iteration: consume one literal block (or the clause-end `0`)
off `SCAN`. Idles once `CDONE = [1]`. A literal is
`1 :: polBit :: replicate v 1 ++ [0]`: the leading `1` sentinel and the polarity
bit are dropped by two `tail`s, the unary block + terminator by
`CliqueRelTM.readNum`; then the literal count `LCNT` grows by one. -/
def litScan : Cmd :=
  Cmd.ifBit CDONE
    CliqueRelTM.cSkip
    (Cmd.op (.head HEADC SCAN) ;;
     Cmd.op (.tail SCAN SCAN) ;;
     Cmd.ifBit HEADC
       (Cmd.op (.tail SCAN SCAN) ;;
        CliqueRelTM.readNum VALX SCAN IDXV ;;
        Cmd.op (.appendOne LCNT))
       (Cmd.op (.clear CDONE) ;; Cmd.op (.appendOne CDONE)))

/-- Consume one encoded clause off `SCAN`, then AND `|C| = 3` into `OK`.
The loop bound is `SCAN`'s entry length (generous — one iteration per literal
plus one for the clause-end marker; the rest idle on `CDONE`). -/
def clauseScan : Cmd :=
  Cmd.op (.clear LCNT) ;;
  Cmd.op (.clear CDONE) ;;
  Cmd.forBnd IDXI SCAN litScan ;;
  Cmd.op (.eqBit RES LCNT THREE) ;;
  Cmd.ifBit RES CliqueRelTM.cSkip
    (Cmd.op (.clear OK) ;; Cmd.op (.appendZero OK))

/-- **The re-encoder.** Computes `kSAT_to_SAT_reduction 3` in place on any
state carrying `CLAUSE_TALLY = replicate |N| 1` (reg 1) and
`CNF_STREAM = encodeCnf N` (reg 2): parses a scratch copy of the stream, and on
a failed `kCNF 3` check rewrites regs 1/2 to encode `[[]]`
(`CLAUSE_TALLY := [1]`, `CNF_STREAM := [0]`). Finally scrubs the one below-16
scratch register (`CliqueRelTM.HEAD = 15`). -/
def kCnf3Check : Cmd :=
  Cmd.op (.copy SCAN CNF_STREAM) ;;
  Cmd.op (.clear OK) ;; Cmd.op (.appendOne OK) ;;
  Cmd.op (.clear THREE) ;;
  Cmd.op (.appendOne THREE) ;; Cmd.op (.appendOne THREE) ;;
  Cmd.op (.appendOne THREE) ;;
  Cmd.forBnd IDXO CLAUSE_TALLY clauseScan ;;
  Cmd.ifBit OK
    CliqueRelTM.cSkip
    (Cmd.op (.clear CLAUSE_TALLY) ;; Cmd.op (.appendOne CLAUSE_TALLY) ;;
     Cmd.op (.clear CNF_STREAM) ;; Cmd.op (.appendZero CNF_STREAM)) ;;
  Cmd.op (.clear CliqueRelTM.HEAD)

/-! ## Encoding structure lemmas -/

theorem encodeCnf_cons (C : clause) (N : cnf) :
    encodeCnf (C :: N) = encodeClause C ++ encodeCnf N := rfl

theorem encodeClause_cons (l : literal) (C : clause) :
    encodeClause (l :: C) = encodeLit l ++ encodeClause C := by
  simp only [encodeClause, List.foldr_cons, List.append_assoc]

theorem encodeClause_nil : encodeClause [] = [0] := rfl

theorem encodeLit_eq (pol : Bool) (v : Nat) :
    encodeLit (pol, v)
      = 1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0]) := rfl

theorem encodeLit_length (l : literal) : (encodeLit l).length = l.2 + 3 := by
  rcases l with ⟨pol, v⟩
  simp [encodeLit_eq]

theorem encodeClause_length_ge (C : clause) :
    C.length + 1 ≤ (encodeClause C).length := by
  induction C with
  | nil => simp [encodeClause_nil]
  | cons l C ih =>
      rw [encodeClause_cons, List.length_append, encodeLit_length, List.length_cons]
      omega

theorem encodeCnf_append (N₁ N₂ : cnf) :
    encodeCnf (N₁ ++ N₂) = encodeCnf N₁ ++ encodeCnf N₂ := by
  induction N₁ with
  | nil => rfl
  | cons C N ih => rw [List.cons_append, encodeCnf_cons, encodeCnf_cons, ih,
      List.append_assoc]

/-- Each clause contributes at least one cell, so the clause count is bounded
by the stream length. -/
theorem length_le_encodeCnf_length (N : cnf) :
    N.length ≤ (encodeCnf N).length := by
  induction N with
  | nil => simp [encodeCnf]
  | cons C N ih =>
      rw [encodeCnf_cons, List.length_append, List.length_cons]
      have := encodeClause_length_ge C
      omega

theorem encodeCnf_drop_length_le (N : cnf) (i : Nat) :
    (encodeCnf (N.drop i)).length ≤ (encodeCnf N).length := by
  conv_rhs => rw [← List.take_append_drop i N]
  rw [encodeCnf_append, List.length_append]
  exact Nat.le_add_left _ _

theorem encodeClause_drop_length_le (C : clause) (i : Nat) :
    (encodeClause (C.drop i)).length ≤ (encodeClause C).length := by
  conv_rhs => rw [← List.take_append_drop i C]
  generalize C.take i = P
  generalize C.drop i = D
  induction P with
  | nil => simp
  | cons l P ih =>
      rw [List.cons_append, encodeClause_cons, List.length_append]
      omega

/-! ## The inner (per-clause) loop: run lemmas -/

/-- `litScan`, literal case: `CDONE` is not set and `SCAN` starts with a
literal block. Consumes exactly the block, appends one `1` to `LCNT`, and costs
at most `2·S² + 9·S + 20` for any `S ≥ |SCAN|`. -/
theorem litScan_lit (s : State) (pol : Bool) (v : Nat) (X : List Nat) (S : Nat)
    (hCD : State.get s CDONE ≠ [1])
    (hSC : State.get s SCAN = encodeLit (pol, v) ++ X)
    (hS : (State.get s SCAN).length ≤ S) :
    State.get (litScan.eval s) SCAN = X
    ∧ State.get (litScan.eval s) LCNT = State.get s LCNT ++ [1]
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ LCNT → r ≠ HEADC → r ≠ VALX →
        r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
        r ≠ IDXV → State.get (litScan.eval s) r = State.get s r)
    ∧ litScan.cost s ≤ 2 * (S * S) + 9 * S + 20 := by
  -- decompose the stream head
  have hSC' : State.get s SCAN
      = 1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: X) := by
    rw [hSC, encodeLit_eq]
    simp [List.append_assoc]
  -- the four evaluation stages
  have e1 : (Cmd.op (.head HEADC SCAN)).eval s = s.set HEADC [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hSC']
  set s1 := s.set HEADC [1] with hs1
  have hs1SCAN : State.get s1 SCAN = State.get s SCAN :=
    State.get_set_ne _ _ _ _ (by decide)
  have e2 : (Cmd.op (.tail SCAN SCAN)).eval s1
      = s1.set SCAN ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: X)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hs1SCAN, hSC', List.tail_cons]
  set s2 := s1.set SCAN ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: X))
    with hs2
  have hs2HEADC : State.get s2 HEADC = [1] := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
  have hs2SCAN : State.get s2 SCAN
      = (if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: X) :=
    State.get_set_eq _ _ _
  have e3 : (Cmd.op (.tail SCAN SCAN)).eval s2
      = s2.set SCAN (List.replicate v 1 ++ 0 :: X) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hs2SCAN, List.tail_cons]
  set s3 := s2.set SCAN (List.replicate v 1 ++ 0 :: X) with hs3
  have hs3SCAN : State.get s3 SCAN = List.replicate v 1 ++ 0 :: X :=
    State.get_set_eq _ _ _
  -- readNum on the unary block
  obtain ⟨hVALX, hSCAN4, hRNframe⟩ := CliqueRelTM.readNum_run s3 v X VALX SCAN IDXV
    hs3SCAN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s4 := (CliqueRelTM.readNum VALX SCAN IDXV).eval s3 with hs4
  have e5 : (Cmd.op (.appendOne LCNT)).eval s4
      = s4.set LCNT (State.get s4 LCNT ++ [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  -- the whole evaluation
  have heval : litScan.eval s = s4.set LCNT (State.get s4 LCNT ++ [1]) := by
    show (Cmd.ifBit CDONE _ _).eval s = _
    rw [Cmd.eval_ifBit_false _ _ _ _ hCD, Cmd.eval_seq, e1, Cmd.eval_seq, e2,
      Cmd.eval_ifBit_true _ _ _ _ hs2HEADC, Cmd.eval_seq, e3, Cmd.eval_seq,
      ← hs4, e5]
  -- LCNT through the stages
  have hs4LCNT : State.get s4 LCNT = State.get s LCNT := by
    rw [hRNframe LCNT (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval, State.get_set_ne _ _ _ _ (by decide), hSCAN4]
  · rw [heval, State.get_set_eq, hs4LCNT]
  · intro r hrS hrL hrH hrV hrHd hrI hrSk hrIx
    rw [heval, State.get_set_ne _ _ _ _ hrL,
      hRNframe r hrS hrV hrI hrHd hrSk hrIx,
      State.get_set_ne _ _ _ _ hrS, State.get_set_ne _ _ _ _ hrS,
      State.get_set_ne _ _ _ _ hrH]
  · -- cost accounting
    have hlen1 : (State.get s1 SCAN).length ≤ S := by rw [hs1SCAN]; exact hS
    have hlen2 : (State.get s2 SCAN).length ≤ S := by
      rw [hs2SCAN]
      have : (State.get s SCAN).length
          = ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: X)).length + 1 := by
        rw [hSC']; rfl
      omega
    have hlen3 : (State.get s3 SCAN).length ≤ S := by
      rw [hs3SCAN]
      have h2 : (State.get s2 SCAN).length
          = (List.replicate v 1 ++ 0 :: X).length + 1 := by rw [hs2SCAN]; rfl
      omega
    have hrn := CliqueRelTM.readNum_cost s3 VALX SCAN IDXV
      (by decide) (by decide) (by decide) (by decide) (by decide)
    set L := (State.get s3 SCAN).length with hL
    have hrn' : (CliqueRelTM.readNum VALX SCAN IDXV).cost s3
        ≤ 2 * (S * S) + 7 * S + 7 := by
      have hLS : L ≤ S := hlen3
      have hsq : L * L ≤ S * S := Nat.mul_le_mul hLS hLS
      have : 2 * L * L ≤ 2 * (S * S) := by
        calc 2 * L * L = 2 * (L * L) := by ring
          _ ≤ 2 * (S * S) := Nat.mul_le_mul_left 2 hsq
      omega
    have hcost : litScan.cost s
        = 1 + (1 + 1 + (1 + ((State.get s1 SCAN).length + 1)
            + (1 + (1 + ((State.get s2 SCAN).length + 1)
              + (1 + (CliqueRelTM.readNum VALX SCAN IDXV).cost s3 + 1))))) := by
      show (Cmd.ifBit CDONE _ _).cost s = _
      rw [Cmd.cost_ifBit_false _ _ _ _ hCD, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_seq,
        e1, Cmd.cost_op, Cmd.cost_ifBit_true _ _ _ _ (by rw [e2]; exact hs2HEADC),
        e2, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_seq, e3, Cmd.cost_op]
      simp only [Op.cost]
    rw [hcost]
    omega

/-- `litScan`, clause-end case: `CDONE` not set, `SCAN` starts with the
clause-end `0`. Consumes the `0` and raises `CDONE`. -/
theorem litScan_end (s : State) (X : List Nat)
    (hCD : State.get s CDONE ≠ [1])
    (hSC : State.get s SCAN = 0 :: X) :
    State.get (litScan.eval s) SCAN = X
    ∧ State.get (litScan.eval s) CDONE = [1]
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ CDONE → r ≠ HEADC →
        State.get (litScan.eval s) r = State.get s r)
    ∧ litScan.cost s ≤ (State.get s SCAN).length + 10 := by
  have e1 : (Cmd.op (.head HEADC SCAN)).eval s = s.set HEADC [0] := by
    rw [Cmd.eval_op]; simp only [Op.eval, hSC]
  set s1 := s.set HEADC [0] with hs1
  have hs1SCAN : State.get s1 SCAN = 0 :: X := by
    rw [State.get_set_ne _ _ _ _ (by decide)]; exact hSC
  have e2 : (Cmd.op (.tail SCAN SCAN)).eval s1 = s1.set SCAN X := by
    rw [Cmd.eval_op]; simp only [Op.eval, hs1SCAN, List.tail_cons]
  set s2 := s1.set SCAN X with hs2
  have hs2HEADC : State.get s2 HEADC = [0] := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
  have hs2HEADC' : State.get s2 HEADC ≠ [1] := by rw [hs2HEADC]; decide
  have e3 : ((Cmd.op (.clear CDONE)) ;; Cmd.op (.appendOne CDONE)).eval s2
      = s2.set CDONE [1] := by
    rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, List.nil_append, State.set_set]
  have heval : litScan.eval s = s2.set CDONE [1] := by
    show (Cmd.ifBit CDONE _ _).eval s = _
    rw [Cmd.eval_ifBit_false _ _ _ _ hCD, Cmd.eval_seq, e1, Cmd.eval_seq, e2,
      Cmd.eval_ifBit_false _ _ _ _ hs2HEADC', e3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval, State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
  · rw [heval, State.get_set_eq]
  · intro r hrS hrC hrH
    rw [heval, State.get_set_ne _ _ _ _ hrC, State.get_set_ne _ _ _ _ hrS,
      State.get_set_ne _ _ _ _ hrH]
  · have hcost : litScan.cost s
        = 1 + (1 + 1 + (1 + ((State.get s1 SCAN).length + 1)
            + (1 + (1 + 1 + 1)))) := by
      show (Cmd.ifBit CDONE _ _).cost s = _
      rw [Cmd.cost_ifBit_false _ _ _ _ hCD, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_seq,
        e1, Cmd.cost_op, Cmd.cost_ifBit_false _ _ _ _ (by rw [e2]; exact hs2HEADC'),
        e2, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
      simp only [Op.cost]
    have : (State.get s1 SCAN).length = (State.get s SCAN).length := by
      rw [hs1SCAN, hSC]
    rw [hcost]
    omega

/-- `litScan`, idle case: `CDONE = [1]`. A `cSkip` (touches only `SKIPR`). -/
theorem litScan_idle (s : State) (hCD : State.get s CDONE = [1]) :
    litScan.eval s = s.set CliqueRelTM.SKIPR [1] ∧ litScan.cost s = 4 := by
  constructor
  · show (Cmd.ifBit CDONE _ _).eval s = _
    rw [Cmd.eval_ifBit_true _ _ _ _ hCD, CliqueRelTM.cSkip_eval]
  · show (Cmd.ifBit CDONE _ _).cost s = _
    rw [Cmd.cost_ifBit_true _ _ _ _ hCD, CliqueRelTM.cSkip_cost]

/-- The per-clause fold invariant: through iteration `|C|` the loop consumes
one literal block per iteration into the unary tally `LCNT`; at iteration
`|C|` it consumes the clause-end `0` and raises `CDONE`; afterwards it idles. -/
def CSInv (C : clause) (rest : List Nat) (s0 : State) (i : Nat) (s : State) :
    Prop :=
  (if i ≤ C.length then
      State.get s SCAN = encodeClause (C.drop i) ++ rest
      ∧ State.get s LCNT = List.replicate i 1
      ∧ State.get s CDONE = []
    else
      State.get s SCAN = rest
      ∧ State.get s LCNT = List.replicate C.length 1
      ∧ State.get s CDONE = [1])
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ LCNT → r ≠ CDONE → r ≠ HEADC → r ≠ VALX →
      r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.INBLK → r ≠ CliqueRelTM.SKIPR →
      r ≠ IDXV → r ≠ IDXI → State.get s r = State.get s0 r)

/-- One `litScan` iteration preserves `CSInv` (and costs at most the uniform
bound `2·S² + 9·S + 20` when `S` bounds the whole clause-plus-rest block). -/
theorem litScan_step (C : clause) (rest : List Nat) (s0 : State) (S : Nat)
    (hS : (encodeClause C ++ rest).length ≤ S)
    (i : Nat) (s : State) (h : CSInv C rest s0 i s) :
    CSInv C rest s0 (i + 1) (litScan.eval (s.set IDXI (List.replicate i 1)))
    ∧ litScan.cost (s.set IDXI (List.replicate i 1)) ≤ 2 * (S * S) + 9 * S + 20 := by
  obtain ⟨hphase, hframe⟩ := h
  set w := s.set IDXI (List.replicate i 1) with hw
  have hwSCAN : State.get w SCAN = State.get s SCAN :=
    State.get_set_ne _ _ _ _ (by decide)
  have hwLCNT : State.get w LCNT = State.get s LCNT :=
    State.get_set_ne _ _ _ _ (by decide)
  have hwCDONE : State.get w CDONE = State.get s CDONE :=
    State.get_set_ne _ _ _ _ (by decide)
  have hwframe : ∀ r : Var, r ≠ IDXI → State.get w r = State.get s r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  -- the stream never grows along the phases, so `S` bounds it at every i
  have hSCANlen : ∀ i' , (encodeClause (C.drop i') ++ rest).length ≤ S := by
    intro i'
    have : (encodeClause (C.drop i')).length + rest.length ≤ S := by
      have hle : (encodeClause (C.drop i')).length ≤ (encodeClause C).length := by
        conv_rhs => rw [← List.take_append_drop i' C]
        clear hS hphase hframe hwframe
        generalize C.take i' = P
        induction P with
        | nil => exact Nat.le_refl _
        | cons l P ih =>
            rw [List.cons_append, encodeClause_cons, List.length_append]
            omega
      rw [List.length_append] at hS
      omega
    rw [List.length_append]
    exact this
  rcases Nat.lt_trichotomy i C.length with hi | hi | hi
  · -- literal iteration
    rw [if_pos (Nat.le_of_lt hi)] at hphase
    obtain ⟨hSC, hLC, hCD⟩ := hphase
    have hdrop : C.drop i = C[i] :: C.drop (i + 1) := List.drop_eq_getElem_cons hi
    rcases hCi : C[i] with ⟨pol, v⟩
    have hSCw : State.get w SCAN
        = encodeLit (pol, v) ++ (encodeClause (C.drop (i + 1)) ++ rest) := by
      rw [hwSCAN, hSC, hdrop, hCi, encodeClause_cons, List.append_assoc]
    have hCDw : State.get w CDONE ≠ [1] := by rw [hwCDONE, hCD]; decide
    have hSw : (State.get w SCAN).length ≤ S := by
      rw [hwSCAN, hSC]
      calc (encodeClause (C.drop i) ++ rest).length
          ≤ (encodeClause C ++ rest).length := by
            rw [List.length_append, List.length_append]
            exact Nat.add_le_add_right (encodeClause_drop_length_le C i) _
        _ ≤ S := hS
    obtain ⟨hS', hL', hF', hC'⟩ := litScan_lit w pol v _ S hCDw hSCw hSw
    refine ⟨⟨?_, ?_⟩, hC'⟩
    · rw [if_pos (Nat.succ_le_of_lt hi)]
      refine ⟨hS', ?_, ?_⟩
      · rw [hL', hwLCNT, hLC, CliqueRelTM.replicate_one_snoc]
      · rw [hF' CDONE (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), hwCDONE, hCD]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rw [hF' r h1 h2 h4 h5 h6 h7 h8 h9, hwframe r h10]
      exact hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · -- clause-end iteration
    rw [if_pos (Nat.le_of_eq hi)] at hphase
    obtain ⟨hSC, hLC, hCD⟩ := hphase
    have hSCw : State.get w SCAN = 0 :: rest := by
      rw [hwSCAN, hSC, hi, List.drop_length, encodeClause_nil, List.singleton_append]
    have hCDw : State.get w CDONE ≠ [1] := by rw [hwCDONE, hCD]; decide
    obtain ⟨hS', hD', hF', hC'⟩ := litScan_end w rest hCDw hSCw
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [if_neg (by omega : ¬ i + 1 ≤ C.length)]
      refine ⟨hS', ?_, hD'⟩
      rw [hF' LCNT (by decide) (by decide) (by decide), hwLCNT, hLC, hi]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rw [hF' r h1 h3 h4, hwframe r h10]
      exact hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    · have hlenw : (State.get w SCAN).length ≤ S := by
        rw [hSCw]
        rw [List.length_append] at hS
        have h2 := encodeClause_length_ge C
        simp only [List.length_cons]
        omega
      omega
  · -- idle iteration
    rw [if_neg (by omega : ¬ i ≤ C.length)] at hphase
    obtain ⟨hSC, hLC, hCD⟩ := hphase
    have hCDw : State.get w CDONE = [1] := by rw [hwCDONE]; exact hCD
    obtain ⟨heval, hcost⟩ := litScan_idle w hCDw
    refine ⟨⟨?_, ?_⟩, by omega⟩
    · rw [if_neg (by omega : ¬ i + 1 ≤ C.length), heval]
      refine ⟨?_, ?_, ?_⟩
      · rw [State.get_set_ne _ _ _ _ (by decide), hwSCAN]; exact hSC
      · rw [State.get_set_ne _ _ _ _ (by decide), hwLCNT]; exact hLC
      · rw [State.get_set_ne _ _ _ _ (by decide), hwCDONE]; exact hCD
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rw [heval, State.get_set_ne _ _ _ _ h8, hwframe r h10]
      exact hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

/-! ## The per-clause gadget: run + cost -/

/-- **`clauseScan` is correct.** On `SCAN = encodeClause C ++ rest` it consumes
exactly the clause, ANDs `|C| = 3` into `OK`, and costs `O(S³)` for any
`S ≥ |SCAN|`. -/
theorem clauseScan_run (C : clause) (rest : List Nat) (b : Bool) (s : State)
    (S : Nat)
    (hscan : State.get s SCAN = encodeClause C ++ rest)
    (hok : State.get s OK = [if b then 1 else 0])
    (hthree : State.get s THREE = List.replicate 3 1)
    (hS : (State.get s SCAN).length ≤ S) :
    State.get (clauseScan.eval s) SCAN = rest
    ∧ State.get (clauseScan.eval s) OK
        = [if b && (C.length == 3) then 1 else 0]
    ∧ (∀ r : Var, r ≠ SCAN → r ≠ OK → r ≠ LCNT → r ≠ CDONE → r ≠ RES →
        r ≠ HEADC → r ≠ VALX → r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.INBLK →
        r ≠ CliqueRelTM.SKIPR → r ≠ IDXI → r ≠ IDXV →
        State.get (clauseScan.eval s) r = State.get s r)
    ∧ clauseScan.cost s ≤ 2 * (S * S * S) + 10 * (S * S) + 25 * S + 20 := by
  have hlenCS : (encodeClause C ++ rest).length ≤ S := by rw [← hscan]; exact hS
  -- init: clear LCNT, clear CDONE
  have e1 : (Cmd.op (.clear LCNT)).eval s = s.set LCNT [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set s1 := s.set LCNT [] with hs1
  have e2 : (Cmd.op (.clear CDONE)).eval s1 = s1.set CDONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set s2 := s1.set CDONE [] with hs2
  have hs2SCAN : State.get s2 SCAN = encodeClause C ++ rest := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide)]
    exact hscan
  have hs2LCNT : State.get s2 LCNT = [] := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
  have hs2CDONE : State.get s2 CDONE = [] := State.get_set_eq _ _ _
  have hs2frame : ∀ r : Var, r ≠ LCNT → r ≠ CDONE →
      State.get s2 r = State.get s r := by
    intro r h1 h2
    rw [State.get_set_ne _ _ _ _ h2, State.get_set_ne _ _ _ _ h1]
  -- the loop
  set n := (State.get s2 SCAN).length with hn
  have hnS : n ≤ S := by rw [hn, hs2SCAN]; exact hlenCS
  have hbase : CSInv C rest s2 0 s2 := by
    refine ⟨?_, fun r _ _ _ _ _ _ _ _ _ _ => rfl⟩
    rw [if_pos (Nat.zero_le _)]
    exact ⟨by rw [hs2SCAN, List.drop_zero], hs2LCNT, hs2CDONE⟩
  have hInv : CSInv C rest s2 n (Cmd.foldlState litScan IDXI (List.range n) s2) :=
    Cmd.foldlState_range_induct litScan IDXI n s2 (CSInv C rest s2) hbase
      (fun i st _ hM => (litScan_step C rest s2 S hlenCS i st hM).1)
  set s3 := Cmd.foldlState litScan IDXI (List.range n) s2 with hs3
  have hloop_eval : (Cmd.forBnd IDXI SCAN litScan).eval s2 = s3 := by
    rw [Cmd.eval_forBnd, ← hn, hs3]
  have hnC : C.length + 1 ≤ n := by
    rw [hn, hs2SCAN, List.length_append]
    have := encodeClause_length_ge C
    omega
  obtain ⟨hphase, hframe3⟩ := hInv
  rw [if_neg (by omega : ¬ n ≤ C.length)] at hphase
  obtain ⟨hSC3, hLC3, hCD3⟩ := hphase
  have hTHREE3 : State.get s3 THREE = List.replicate 3 1 := by
    rw [hframe3 THREE (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide),
      hs2frame THREE (by decide) (by decide), hthree]
  have hOK3 : State.get s3 OK = [if b then 1 else 0] := by
    rw [hframe3 OK (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide),
      hs2frame OK (by decide) (by decide), hok]
  -- eqBit on the tallies
  have e4 : (Cmd.op (.eqBit RES LCNT THREE)).eval s3
      = s3.set RES [if C.length = 3 then 1 else 0] := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hLC3, hTHREE3, CliqueRelTM.eqBit_replicate]
  set s4 := s3.set RES [if C.length = 3 then 1 else 0] with hs4
  have hs4SCAN : State.get s4 SCAN = rest := by
    rw [State.get_set_ne _ _ _ _ (by decide)]; exact hSC3
  have hs4OK : State.get s4 OK = [if b then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide)]; exact hOK3
  have hs4frame : ∀ r : Var, r ≠ RES → State.get s4 r = State.get s3 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  -- cost of the loop
  have hcostLoop : (Cmd.forBnd IDXI SCAN litScan).cost s2
      ≤ 1 + n * (2 * (S * S) + 9 * S + 20) + n * n := by
    have h := Cmd.cost_forBnd_le IDXI SCAN litScan s2 (2 * (S * S) + 9 * S + 20)
      (CSInv C rest s2) hbase
      (fun i st _ hM => (litScan_step C rest s2 S hlenCS i st hM).1)
      (fun i st _ hM => (litScan_step C rest s2 S hlenCS i st hM).2)
    rw [← hn] at h
    exact h
  have hloopS : (Cmd.forBnd IDXI SCAN litScan).cost s2
      ≤ 1 + (2 * (S * S * S) + 9 * (S * S) + 20 * S) + S * S := by
    have h1 : n * (2 * (S * S) + 9 * S + 20)
        ≤ S * (2 * (S * S) + 9 * S + 20) := Nat.mul_le_mul_right _ hnS
    have h2 : S * (2 * (S * S) + 9 * S + 20)
        = 2 * (S * S * S) + 9 * (S * S) + 20 * S := by ring
    have h3 : n * n ≤ S * S := Nat.mul_le_mul hnS hnS
    omega
  -- assemble, splitting on the verdict
  have hCle : C.length ≤ S := by
    rw [List.length_append] at hlenCS
    have := encodeClause_length_ge C
    omega
  by_cases hC3 : C.length = 3
  · -- clause has exactly 3 literals: cSkip branch
    have hRES : State.get s4 RES = [1] := by
      rw [hs4, State.get_set_eq, if_pos hC3]
    have heval : clauseScan.eval s = s4.set CliqueRelTM.SKIPR [1] := by
      show ((Cmd.op (.clear LCNT)) ;; _).eval s = _
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, hloop_eval,
        Cmd.eval_seq, e4, Cmd.eval_ifBit_true _ _ _ _ hRES,
        CliqueRelTM.cSkip_eval]
    have hbeq : (C.length == 3) = true := by simp [hC3]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [heval, State.get_set_ne _ _ _ _ (by decide)]; exact hs4SCAN
    · rw [heval, State.get_set_ne _ _ _ _ (by decide), hs4OK, hbeq, Bool.and_true]
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      rw [heval, State.get_set_ne _ _ _ _ h10, hs4frame r h5,
        hframe3 r h1 h3 h4 h6 h7 h8 h9 h10 h12 h11, hs2frame r h3 h4]
    · have hcost : clauseScan.cost s
          = 1 + 1 + (1 + 1 + (1 + (Cmd.forBnd IDXI SCAN litScan).cost s2
              + (1 + (C.length + 3 + 1) + (1 + 3)))) := by
        show ((Cmd.op (.clear LCNT)) ;; _).cost s = _
        rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_seq, e1, Cmd.cost_op,
          Cmd.cost_seq, e2, Cmd.cost_seq, hloop_eval, Cmd.cost_op,
          Cmd.cost_ifBit_true _ _ _ _ (by rw [e4]; exact hRES), e4,
          CliqueRelTM.cSkip_cost]
        simp only [Op.cost, hLC3, hTHREE3, List.length_replicate]
      rw [hcost]
      omega
  · -- clause length ≠ 3: OK := [0]
    have hRES : State.get s4 RES = [0] := by
      rw [hs4, State.get_set_eq, if_neg hC3]
    have hRES' : State.get s4 RES ≠ [1] := by rw [hRES]; decide
    have e5 : ((Cmd.op (.clear OK)) ;; Cmd.op (.appendZero OK)).eval s4
        = s4.set OK [0] := by
      rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, List.nil_append, State.set_set]
    have heval : clauseScan.eval s = s4.set OK [0] := by
      show ((Cmd.op (.clear LCNT)) ;; _).eval s = _
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, hloop_eval,
        Cmd.eval_seq, e4, Cmd.eval_ifBit_false _ _ _ _ hRES', e5]
    have hbeq : (C.length == 3) = false := by simp [hC3]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [heval, State.get_set_ne _ _ _ _ (by decide)]; exact hs4SCAN
    · rw [heval, State.get_set_eq, hbeq, Bool.and_false]
      rfl
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      rw [heval, State.get_set_ne _ _ _ _ h2, hs4frame r h5,
        hframe3 r h1 h3 h4 h6 h7 h8 h9 h10 h12 h11, hs2frame r h3 h4]
    · have hcost : clauseScan.cost s
          = 1 + 1 + (1 + 1 + (1 + (Cmd.forBnd IDXI SCAN litScan).cost s2
              + (1 + (C.length + 3 + 1) + (1 + (1 + 1 + 1))))) := by
        show ((Cmd.op (.clear LCNT)) ;; _).cost s = _
        rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_seq, e1, Cmd.cost_op,
          Cmd.cost_seq, e2, Cmd.cost_seq, hloop_eval, Cmd.cost_op,
          Cmd.cost_ifBit_false _ _ _ _ (by rw [e4]; exact hRES'), e4,
          Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
        simp only [Op.cost, hLC3, hTHREE3, List.length_replicate]
      rw [hcost]
      omega

/-! ## The outer (per-CNF) loop -/

/-- The outer fold invariant: after `i` clauses, `SCAN` holds the remaining
stream and `OK` the running AND of the per-clause `|C| = 3` checks. -/
def KInv (N : cnf) (s0 : State) (i : Nat) (s : State) : Prop :=
  State.get s SCAN = encodeCnf (N.drop i)
  ∧ State.get s OK = [if (N.take i).all (fun C => C.length == 3) then 1 else 0]
  ∧ (∀ r : Var, r ≠ SCAN → r ≠ OK → r ≠ LCNT → r ≠ CDONE → r ≠ RES →
      r ≠ HEADC → r ≠ VALX → r ≠ CliqueRelTM.HEAD → r ≠ CliqueRelTM.INBLK →
      r ≠ CliqueRelTM.SKIPR → r ≠ IDXO → r ≠ IDXI → r ≠ IDXV →
      State.get s r = State.get s0 r)

/-- One `clauseScan` iteration preserves `KInv` (and costs at most the uniform
per-clause bound). -/
theorem clauseScan_step (N : cnf) (s0 : State) (S : Nat)
    (hthree0 : State.get s0 THREE = List.replicate 3 1)
    (hS : (encodeCnf N).length ≤ S)
    (i : Nat) (hi : i < N.length) (s : State) (h : KInv N s0 i s) :
    KInv N s0 (i + 1) (clauseScan.eval (s.set IDXO (List.replicate i 1)))
    ∧ clauseScan.cost (s.set IDXO (List.replicate i 1))
        ≤ 2 * (S * S * S) + 10 * (S * S) + 25 * S + 20 := by
  obtain ⟨hSC, hOK, hframe⟩ := h
  set w := s.set IDXO (List.replicate i 1) with hw
  have hwSCAN : State.get w SCAN = State.get s SCAN :=
    State.get_set_ne _ _ _ _ (by decide)
  have hwOK : State.get w OK = State.get s OK :=
    State.get_set_ne _ _ _ _ (by decide)
  have hwTHREE : State.get w THREE = State.get s THREE :=
    State.get_set_ne _ _ _ _ (by decide)
  have hsTHREE : State.get s THREE = List.replicate 3 1 := by
    rw [hframe THREE (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hthree0]
  have hdrop : N.drop i = N[i] :: N.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hSCw : State.get w SCAN
      = encodeClause N[i] ++ encodeCnf (N.drop (i + 1)) := by
    rw [hwSCAN, hSC, hdrop, encodeCnf_cons]
  have hSw : (State.get w SCAN).length ≤ S := by
    rw [hwSCAN, hSC]
    exact le_trans (encodeCnf_drop_length_le N i) hS
  -- NB `hbool` must be established BEFORE `clauseScan_run`'s cost conclusion
  -- enters the context: elaborating `N[i]` afterwards sends `assumption`
  -- (inside `get_elem_tactic`) into a defeq check against the `Cmd.cost`
  -- hypothesis, which `whnf`-unfolds the whole program (heartbeat blowup).
  have hbool : (N.take (i + 1)).all (fun C => C.length == 3)
      = ((N.take i).all (fun C => C.length == 3) && (N[i].length == 3)) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    rw [Option.toList_some, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true]
  obtain ⟨hS', hOK', hF', hC'⟩ := clauseScan_run N[i] (encodeCnf (N.drop (i + 1)))
    ((N.take i).all (fun C => C.length == 3)) w S hSCw
    (by rw [hwOK]; exact hOK) (by rw [hwTHREE]; exact hsTHREE) hSw
  refine ⟨⟨hS', ?_, ?_⟩, hC'⟩
  · rw [hbool]
    exact hOK'
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    rw [hF' r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12 h13,
      State.get_set_ne _ _ _ _ h11]
    exact hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

/-! ## The whole re-encoder: run + cost -/

/-- Budget polynomial for one `kCnf3Check` run, in the stream length `S`. -/
def kCheckBudget (S : Nat) : Nat :=
  2 * (S * S * S * S) + 10 * (S * S * S) + 30 * (S * S) + 30 * S + 30

/-- The state after `kCnf3Check`'s 7-op initialisation prefix (uncollapsed
`set` chain: scan copy, `OK := [1]`, `THREE := [1,1,1]`). -/
def initState (s0 : State) (E : List Nat) : State :=
  ((((((s0.set SCAN E).set OK []).set OK [1]).set THREE []).set THREE
      [1]).set THREE [1, 1]).set THREE [1, 1, 1]

theorem initState_get_SCAN (s0 : State) (E : List Nat) :
    State.get (initState s0 E) SCAN = E := by
  unfold initState
  rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_eq]

theorem initState_get_OK (s0 : State) (E : List Nat) :
    State.get (initState s0 E) OK = [1] := by
  unfold initState
  rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
    State.get_set_eq]

theorem initState_get_THREE (s0 : State) (E : List Nat) :
    State.get (initState s0 E) THREE = List.replicate 3 1 :=
  State.get_set_eq _ _ _

theorem initState_frame (s0 : State) (E : List Nat) :
    ∀ r : Var, r ≠ SCAN → r ≠ OK → r ≠ THREE →
      State.get (initState s0 E) r = State.get s0 r := by
  intro r h1 h2 h3
  unfold initState
  rw [State.get_set_ne _ _ _ _ h3, State.get_set_ne _ _ _ _ h3,
    State.get_set_ne _ _ _ _ h3, State.get_set_ne _ _ _ _ h3,
    State.get_set_ne _ _ _ _ h2, State.get_set_ne _ _ _ _ h2,
    State.get_set_ne _ _ _ _ h1]

/-- **`kCnf3Check` computes the reduction.** On any state carrying
`CLAUSE_TALLY = replicate |N| 1` and `CNF_STREAM = encodeCnf N`, the program
rewrites those two registers to the encoding of `kSAT_to_SAT_reduction 3 N`,
leaves every other register `< SCAN` (except its scratch `HEAD`/`INBLK`)
untouched, scrubs `HEAD`, and runs within `kCheckBudget |encodeCnf N|`.
Stated over an arbitrary base state so it serves BOTH the `FreePrecomposeData`
bridge (base `encodeState (N, a)`) and the `PolyTimeComputableLang` witness
(base `[[], replicate |N| 1, encodeCnf N]`, possibly padded). -/
theorem kCnf3Check_run (N : cnf) (s0 : State)
    (htally : State.get s0 CLAUSE_TALLY = List.replicate N.length 1)
    (hstream : State.get s0 CNF_STREAM = encodeCnf N) :
    State.get (kCnf3Check.eval s0) CLAUSE_TALLY
        = List.replicate (kSAT_to_SAT_reduction 3 N).length 1
    ∧ State.get (kCnf3Check.eval s0) CNF_STREAM
        = encodeCnf (kSAT_to_SAT_reduction 3 N)
    ∧ State.get (kCnf3Check.eval s0) CliqueRelTM.HEAD = []
    ∧ (∀ r : Var, r ≠ CLAUSE_TALLY → r ≠ CNF_STREAM → r ≠ CliqueRelTM.HEAD →
        r ≠ CliqueRelTM.INBLK → r < SCAN →
        State.get (kCnf3Check.eval s0) r = State.get s0 r)
    ∧ kCnf3Check.cost s0 ≤ kCheckBudget (encodeCnf N).length := by
  set S := (encodeCnf N).length with hSdef
  -- the 7-op initialisation prefix
  have e1 : (Cmd.op (.copy SCAN CNF_STREAM)).eval s0 = s0.set SCAN (encodeCnf N) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hstream]
  have e2 : (Cmd.op (.clear OK)).eval (s0.set SCAN (encodeCnf N))
      = (s0.set SCAN (encodeCnf N)).set OK [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e3 : (Cmd.op (.appendOne OK)).eval ((s0.set SCAN (encodeCnf N)).set OK [])
      = ((s0.set SCAN (encodeCnf N)).set OK []).set OK [1] := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, List.nil_append]
  have e4 : (Cmd.op (.clear THREE)).eval
        (((s0.set SCAN (encodeCnf N)).set OK []).set OK [1])
      = (((s0.set SCAN (encodeCnf N)).set OK []).set OK [1]).set THREE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e5 : (Cmd.op (.appendOne THREE)).eval
        ((((s0.set SCAN (encodeCnf N)).set OK []).set OK [1]).set THREE [])
      = ((((s0.set SCAN (encodeCnf N)).set OK []).set OK [1]).set THREE
          []).set THREE [1] := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, List.nil_append]
  have e6 : (Cmd.op (.appendOne THREE)).eval
        (((((s0.set SCAN (encodeCnf N)).set OK []).set OK [1]).set THREE
          []).set THREE [1])
      = (((((s0.set SCAN (encodeCnf N)).set OK []).set OK [1]).set THREE
          []).set THREE [1]).set THREE [1, 1] := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, List.cons_append, List.nil_append]
  have e7 : (Cmd.op (.appendOne THREE)).eval
        ((((((s0.set SCAN (encodeCnf N)).set OK []).set OK [1]).set THREE
          []).set THREE [1]).set THREE [1, 1])
      = initState s0 (encodeCnf N) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, List.cons_append, List.nil_append]
    rfl
  set u := initState s0 (encodeCnf N) with hu
  have huSCAN := initState_get_SCAN s0 (encodeCnf N)
  have huOK := initState_get_OK s0 (encodeCnf N)
  have huTHREE := initState_get_THREE s0 (encodeCnf N)
  have huframe := initState_frame s0 (encodeCnf N)
  have hbound : State.get u CLAUSE_TALLY = List.replicate N.length 1 := by
    rw [huframe CLAUSE_TALLY (by decide) (by decide) (by decide)]; exact htally
  -- the loop
  have hbase : KInv N u 0 u := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [huSCAN, List.drop_zero]
    · rw [huOK]; simp
  have hloop_eval : (Cmd.forBnd IDXO CLAUSE_TALLY clauseScan).eval u
      = Cmd.foldlState clauseScan IDXO (List.range N.length) u := by
    rw [Cmd.eval_forBnd, hbound, List.length_replicate]
  set z := Cmd.foldlState clauseScan IDXO (List.range N.length) u with hz
  have hInv : KInv N u N.length z := by
    rw [hz]
    exact Cmd.foldlState_range_induct clauseScan IDXO N.length u (KInv N u) hbase
      (fun i st hi hM =>
        (clauseScan_step N u S huTHREE (le_of_eq hSdef.symm) i hi st hM).1)
  obtain ⟨hzSCAN, hzOK, hzframe⟩ := hInv
  have hzOK' : State.get z OK = [if kCNF_decb 3 N then 1 else 0] := by
    rw [hzOK, List.take_length]
    rfl
  have hzTALLY : State.get z CLAUSE_TALLY = List.replicate N.length 1 := by
    rw [hzframe CLAUSE_TALLY (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    exact hbound
  have hzSTREAM : State.get z CNF_STREAM = encodeCnf N := by
    rw [hzframe CNF_STREAM (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),
      huframe CNF_STREAM (by decide) (by decide) (by decide)]
    exact hstream
  -- cost of the loop
  have hmS : N.length ≤ S := by rw [hSdef]; exact length_le_encodeCnf_length N
  have hcostLoop : (Cmd.forBnd IDXO CLAUSE_TALLY clauseScan).cost u
      ≤ 1 + (2 * (S * S * S * S) + 10 * (S * S * S) + 25 * (S * S) + 20 * S)
        + S * S := by
    have h := Cmd.cost_forBnd_le IDXO CLAUSE_TALLY clauseScan u
      (2 * (S * S * S) + 10 * (S * S) + 25 * S + 20) (KInv N u) hbase
      (fun i st hi hM =>
        (clauseScan_step N u S huTHREE (le_of_eq hSdef.symm) i
          (by rwa [hbound, List.length_replicate] at hi) st hM).1)
      (fun i st hi hM =>
        (clauseScan_step N u S huTHREE (le_of_eq hSdef.symm) i
          (by rwa [hbound, List.length_replicate] at hi) st hM).2)
    rw [hbound, List.length_replicate] at h
    have h1 : N.length * (2 * (S * S * S) + 10 * (S * S) + 25 * S + 20)
        ≤ S * (2 * (S * S * S) + 10 * (S * S) + 25 * S + 20) :=
      Nat.mul_le_mul_right _ hmS
    have h2 : S * (2 * (S * S * S) + 10 * (S * S) + 25 * S + 20)
        = 2 * (S * S * S * S) + 10 * (S * S * S) + 25 * (S * S) + 20 * S := by
      ring
    have h3 : N.length * N.length ≤ S * S := Nat.mul_le_mul hmS hmS
    omega
  -- shared cost prefix: everything except the ifBit branch cost
  have hcost_pre : ∀ IFC : Nat,
      (Cmd.ifBit OK CliqueRelTM.cSkip
          (Cmd.op (.clear CLAUSE_TALLY) ;; Cmd.op (.appendOne CLAUSE_TALLY) ;;
           Cmd.op (.clear CNF_STREAM) ;; Cmd.op (.appendZero CNF_STREAM))).cost z
        = IFC →
      kCnf3Check.cost s0
        = 1 + (S + 1) + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1
            + (1 + (Cmd.forBnd IDXO CLAUSE_TALLY clauseScan).cost u
              + (1 + IFC + 1)))))))) := by
    intro IFC hIFC
    show ((Cmd.op (.copy SCAN CNF_STREAM)) ;; _).cost s0 = _
    simp only [Cmd.cost_seq, Cmd.cost_op]
    rw [e1, e2, e3, e4, e5, e6, e7, hloop_eval, hIFC]
    simp only [Op.cost, hstream]
    rw [hSdef]
  -- split on the verdict
  by_cases hdec : kCNF_decb 3 N = true
  · -- kCNF 3 N holds: the reduction is the identity
    have hOKz : State.get z OK = [1] := by rw [hzOK', if_pos hdec]
    have hred : kSAT_to_SAT_reduction 3 N = N := by
      unfold kSAT_to_SAT_reduction
      rw [if_pos ⟨by norm_num, (kCNF_decb_iff 3 N).mp hdec⟩]
    have heval : kCnf3Check.eval s0
        = (z.set CliqueRelTM.SKIPR [1]).set CliqueRelTM.HEAD [] := by
      show ((Cmd.op (.copy SCAN CNF_STREAM)) ;; _).eval s0 = _
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, e7,
        Cmd.eval_seq, hloop_eval,
        Cmd.eval_seq, Cmd.eval_ifBit_true _ _ _ _ hOKz, CliqueRelTM.cSkip_eval,
        Cmd.eval_op]
      simp only [Op.eval]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [heval, hred, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hzTALLY]
    · rw [heval, hred, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hzSTREAM]
    · rw [heval, State.get_set_eq]
    · intro r hr1 hr2 hr3 hr4 hr5
      have h17 : (r : Nat) < 17 := hr5
      have hge : ∀ k : Nat, 17 ≤ k → r ≠ k :=
        fun k hk => Nat.ne_of_lt (Nat.lt_of_lt_of_le h17 hk)
      rw [heval, State.get_set_ne _ _ _ _ hr3,
        State.get_set_ne _ _ _ _ (by exact hge 26 (by omega)),
        hzframe r (hge 17 (by omega)) (hge 18 (by omega)) (hge 20 (by omega))
          (hge 21 (by omega)) (hge 22 (by omega)) (hge 23 (by omega))
          (hge 24 (by omega)) hr3 hr4 (hge 26 (by omega)) (hge 25 (by omega))
          (hge 27 (by omega)) (hge 28 (by omega)),
        huframe r (hge 17 (by omega)) (hge 18 (by omega)) (hge 19 (by omega))]
    · have hIFC : (Cmd.ifBit OK CliqueRelTM.cSkip
          (Cmd.op (.clear CLAUSE_TALLY) ;; Cmd.op (.appendOne CLAUSE_TALLY) ;;
           Cmd.op (.clear CNF_STREAM) ;; Cmd.op (.appendZero CNF_STREAM))).cost z
          = 1 + 3 := by
        rw [Cmd.cost_ifBit_true _ _ _ _ hOKz, CliqueRelTM.cSkip_cost]
      rw [hcost_pre (1 + 3) hIFC]
      have := hcostLoop
      show _ ≤ 2 * (S * S * S * S) + 10 * (S * S * S) + 30 * (S * S) + 30 * S + 30
      omega
  · -- some clause fails the check: the reduction collapses to `[[]]`
    have hOKz : State.get z OK = [0] := by
      rw [hzOK', if_neg hdec]
    have hOKz' : State.get z OK ≠ [1] := by rw [hOKz]; decide
    have hred : kSAT_to_SAT_reduction 3 N = [[]] := by
      unfold kSAT_to_SAT_reduction
      rw [if_neg (fun h => hdec ((kCNF_decb_iff 3 N).mpr h.2))]
      rfl
    have e_else : ((Cmd.op (.clear CLAUSE_TALLY)) ;; Cmd.op (.appendOne CLAUSE_TALLY) ;;
        Cmd.op (.clear CNF_STREAM) ;; Cmd.op (.appendZero CNF_STREAM)).eval z
        = (((z.set CLAUSE_TALLY []).set CLAUSE_TALLY [1]).set CNF_STREAM
            []).set CNF_STREAM [0] := by
      rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq, Cmd.eval_op, Cmd.eval_seq,
        Cmd.eval_op, Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, List.nil_append]
    have heval : kCnf3Check.eval s0
        = ((((z.set CLAUSE_TALLY []).set CLAUSE_TALLY [1]).set CNF_STREAM
            []).set CNF_STREAM [0]).set CliqueRelTM.HEAD [] := by
      show ((Cmd.op (.copy SCAN CNF_STREAM)) ;; _).eval s0 = _
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, e7,
        Cmd.eval_seq, hloop_eval,
        Cmd.eval_seq, Cmd.eval_ifBit_false _ _ _ _ hOKz', e_else, Cmd.eval_op]
      simp only [Op.eval]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [heval, hred, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
        State.get_set_eq]
      rfl
    · rw [heval, hred, State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
      rfl
    · rw [heval, State.get_set_eq]
    · intro r hr1 hr2 hr3 hr4 hr5
      have h17 : (r : Nat) < 17 := hr5
      have hge : ∀ k : Nat, 17 ≤ k → r ≠ k :=
        fun k hk => Nat.ne_of_lt (Nat.lt_of_lt_of_le h17 hk)
      rw [heval, State.get_set_ne _ _ _ _ hr3, State.get_set_ne _ _ _ _ hr2,
        State.get_set_ne _ _ _ _ hr2, State.get_set_ne _ _ _ _ hr1,
        State.get_set_ne _ _ _ _ hr1,
        hzframe r (hge 17 (by omega)) (hge 18 (by omega)) (hge 20 (by omega))
          (hge 21 (by omega)) (hge 22 (by omega)) (hge 23 (by omega))
          (hge 24 (by omega)) hr3 hr4 (hge 26 (by omega)) (hge 25 (by omega))
          (hge 27 (by omega)) (hge 28 (by omega)),
        huframe r (hge 17 (by omega)) (hge 18 (by omega)) (hge 19 (by omega))]
    · have hIFC : (Cmd.ifBit OK CliqueRelTM.cSkip
          (Cmd.op (.clear CLAUSE_TALLY) ;; Cmd.op (.appendOne CLAUSE_TALLY) ;;
           Cmd.op (.clear CNF_STREAM) ;; Cmd.op (.appendZero CNF_STREAM))).cost z
          = 1 + 7 := by
        rw [Cmd.cost_ifBit_false _ _ _ _ hOKz', Cmd.cost_seq, Cmd.cost_op,
          Cmd.cost_seq, Cmd.cost_op, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
        simp only [Op.cost]
      rw [hcost_pre (1 + 7) hIFC]
      have := hcostLoop
      show _ ≤ 2 * (S * S * S * S) + 10 * (S * S * S) + 30 * (S * S) + 30 * S + 30
      omega

/-! ## Structural fields (register frame, `consLen`-freedom, op-supportedness) -/

theorem kCnf3Check_usesBelow : Cmd.UsesBelow kCnf3Check 29 := by
  simp [kCnf3Check, clauseScan, litScan, CliqueRelTM.readNum, CliqueRelTM.cSkip,
    Cmd.UsesBelow, Op.UsesBelow, SCAN, OK, THREE, LCNT, CDONE, RES, HEADC, VALX,
    IDXO, IDXI, IDXV, EvalCnfCmd.CLAUSE_TALLY, EvalCnfCmd.CNF_STREAM,
    CliqueRelTM.HEAD, CliqueRelTM.INBLK, CliqueRelTM.SKIPR]

theorem kCnf3Check_noConsLen : Cmd.NoConsLen kCnf3Check := by
  simp only [kCnf3Check, clauseScan, litScan, CliqueRelTM.readNum,
    CliqueRelTM.cSkip, Cmd.NoConsLen, Op.NotConsLen]
  trivial

theorem kCnf3Check_allOpsSupported : Cmd.AllOpsSupported kCnf3Check := by
  simp only [kCnf3Check, clauseScan, litScan, CliqueRelTM.readNum,
    CliqueRelTM.cSkip, Cmd.AllOpsSupported, Op.IsSupported]
  trivial

/-! ## The bridge: register agreement with the verifier's canonical input -/

/-- **The re-encoding law** (`FreePrecomposeData.bridge`): running `kCnf3Check`
on the verifier's own layout of `(N, a)` produces a state agreeing, on the
verifier frame `< 16`, with the layout of `(kSAT_to_SAT_reduction 3 N, a)`. -/
theorem kCnf3Check_bridge (N : cnf) (a : assgn) :
    AgreeBelow 16 (kCnf3Check.eval (EvalCnfCmd.encodeState (N, a)))
      (EvalCnfCmd.encodeState (kSAT_to_SAT_reduction 3 N, a)) := by
  obtain ⟨hT, hS, hH, hF, -⟩ :=
    kCnf3Check_run N (EvalCnfCmd.encodeState (N, a)) rfl rfl
  intro r hr
  interval_cases r
  · exact hF 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hT
  · exact hS
  · exact hF 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 6 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 7 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 8 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 10 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 11 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 12 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 13 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hF 14 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hH

/-! ## Size accounting (tight bounds for the `PolyTimeComputableLang` layout) -/

private theorem foldl_size_acc {α : Type} [encodable α] :
    ∀ (acc : Nat) (xs : List α),
      xs.foldl (fun a x => a + encodable.size x + 1) acc
        = acc + xs.foldr (fun x s => encodable.size x + 1 + s) 0
  | acc, [] => by simp
  | acc, x :: xs => by
      simp only [List.foldl_cons, List.foldr_cons]
      rw [foldl_size_acc (acc + encodable.size x + 1) xs]
      omega

private theorem size_list_cons {α : Type} [encodable α] (x : α) (xs : List α) :
    encodable.size (x :: xs) = encodable.size x + 1 + encodable.size xs := by
  show (x :: xs).foldl (fun a x => a + encodable.size x + 1) 0 = _
  show List.foldl _ _ _ = _ + 1 + xs.foldl (fun a x => a + encodable.size x + 1) 0
  rw [foldl_size_acc, foldl_size_acc]
  simp only [List.foldr_cons]
  omega

/-- Tight per-clause bound: the encoded clause (plus its 1-cell tally share)
fits in twice the clause's `encodable.size` share. -/
private theorem encodeClause_length_tight (C : clause) :
    (encodeClause C).length + 1 ≤ 2 * (encodable.size C + 1) := by
  induction C with
  | nil => simp [encodeClause_nil]
  | cons l C ih =>
      rcases l with ⟨p, v⟩
      -- retype the variable index at `Nat`: `omega` cannot use `var`-typed atoms
      obtain ⟨w, hw⟩ : ∃ w : Nat, w = v := ⟨v, rfl⟩
      subst hw
      rw [encodeClause_cons, List.length_append, size_list_cons]
      have hlen : (encodeLit (p, w)).length = w + 3 := by
        rw [encodeLit_eq]; simp
      have hl : w + 1 ≤ encodable.size ((p, w) : literal) := by
        cases p
        · show w + 1 ≤ 0 + w + 1
          omega
        · show w + 1 ≤ 1 + w + 1
          omega
      omega

/-- The stream plus the clause tally fit in `2 · size` — this is what makes the
tight `PolyTimeComputableLang.encodeIn_size` (`≤ 2·size + 1`) satisfiable for
the natural 3-register layout. (The learned `5·size` bound on `encodeCnf` alone
is loose.) -/
theorem encodeCnf_tally_tight (N : cnf) :
    (encodeCnf N).length + N.length ≤ 2 * encodable.size N := by
  induction N with
  | nil => simp [encodeCnf]
  | cons C N ih =>
      rw [encodeCnf_cons, List.length_append, List.length_cons, size_list_cons]
      have := encodeClause_length_tight C
      omega

/-- Size of the reduction's output (standalone form of the bound inside
`kSAT_to_SAT`). -/
theorem reduction_size_le (N : cnf) :
    encodable.size (kSAT_to_SAT_reduction 3 N) ≤ encodable.size N + 2 := by
  unfold kSAT_to_SAT_reduction emptyClauseCnf
  split_ifs with h
  · omega
  · have h2 : encodable.size ([[]] : cnf) = 1 := by
      simp [encodable_size_list_cons, encodable_size_list_nil]
    show encodable.size ([[]] : cnf) ≤ encodable.size N + 2
    omega

/-! ## Injectivity of the stream encoding (for `decodeOut`) -/

private theorem replicate_block_inj : ∀ {v v' : Nat} {x y : List Nat},
    List.replicate v 1 ++ 0 :: x = List.replicate v' 1 ++ 0 :: y →
    v = v' ∧ x = y
  | 0, 0, x, y, h => by simpa using h
  | 0, v' + 1, x, y, h => by simp [List.replicate_succ] at h
  | v + 1, 0, x, y, h => by simp [List.replicate_succ] at h
  | v + 1, v' + 1, x, y, h => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq,
        true_and] at h
      obtain ⟨hv, hxy⟩ := replicate_block_inj h
      exact ⟨by omega, hxy⟩

private theorem encodeLit_append_inj {l l' : literal} {x y : List Nat}
    (h : encodeLit l ++ x = encodeLit l' ++ y) : l = l' ∧ x = y := by
  rcases l with ⟨p, v⟩
  rcases l' with ⟨p', v'⟩
  rw [encodeLit_eq, encodeLit_eq] at h
  simp only [List.cons_append, List.append_assoc, List.cons.injEq,
    true_and] at h
  obtain ⟨hp, hblock⟩ := h
  obtain ⟨hv, hxy⟩ := replicate_block_inj hblock
  have hpp : p = p' := by cases p <;> cases p' <;> simp_all
  exact ⟨by rw [hpp, hv], hxy⟩

private theorem encodeClause_append_inj : ∀ {C C' : clause} {x y : List Nat},
    encodeClause C ++ x = encodeClause C' ++ y → C = C' ∧ x = y
  | [], [], x, y, h => ⟨rfl, by simpa [encodeClause_nil] using h⟩
  | [], (p', v') :: C', x, y, h => by
      rw [encodeClause_nil, encodeClause_cons, encodeLit_eq] at h
      simp at h
  | (p, v) :: C, [], x, y, h => by
      rw [encodeClause_cons, encodeClause_nil, encodeLit_eq] at h
      simp at h
  | l :: C, l' :: C', x, y, h => by
      rw [encodeClause_cons, encodeClause_cons, List.append_assoc,
        List.append_assoc] at h
      obtain ⟨hl, hrest⟩ := encodeLit_append_inj h
      obtain ⟨hC, hxy⟩ := encodeClause_append_inj hrest
      exact ⟨by rw [hl, hC], hxy⟩

theorem encodeCnf_injective : Function.Injective encodeCnf := by
  intro N N' h
  induction N generalizing N' with
  | nil =>
      cases N' with
      | nil => rfl
      | cons C' N' =>
          exfalso
          rw [show encodeCnf ([] : cnf) = [] from rfl, encodeCnf_cons] at h
          have hlen := congrArg List.length h
          simp only [List.length_nil, List.length_append] at hlen
          have := encodeClause_length_ge C'
          omega
  | cons C N ih =>
      cases N' with
      | nil =>
          exfalso
          rw [show encodeCnf ([] : cnf) = [] from rfl, encodeCnf_cons] at h
          have hlen := congrArg List.length h
          simp only [List.length_nil, List.length_append] at hlen
          have := encodeClause_length_ge C
          omega
      | cons C' N' =>
          rw [encodeCnf_cons, encodeCnf_cons] at h
          obtain ⟨hC, hrest⟩ := encodeClause_append_inj h
          rw [hC, ih hrest]

/-! ## Budget arithmetic -/

private theorem kCheckBudget_mono {a b : Nat} (h : a ≤ b) :
    kCheckBudget a ≤ kCheckBudget b := by
  unfold kCheckBudget
  have h2 : a * a ≤ b * b := Nat.mul_le_mul h h
  have h3 : a * a * a ≤ b * b * b := Nat.mul_le_mul h2 h
  have h4 : a * a * a * a ≤ b * b * b * b := Nat.mul_le_mul h3 h
  omega

private theorem kCheckBudget_le_poly (n : Nat) :
    kCheckBudget (5 * n) ≤ 3500 * (n + 1) ^ 4 := by
  have ekey : kCheckBudget (5 * n)
      = 1250 * (n*n*n*n) + 1250 * (n*n*n) + 750 * (n*n) + 150 * n + 30 := by
    unfold kCheckBudget; ring
  have epoly : 3500 * (n + 1) ^ 4
      = 3500 * (n*n*n*n) + 14000 * (n*n*n) + 21000 * (n*n) + 14000 * n + 3500 := by
    ring
  omega

/-! ## Blocker (b): the reduction as a free `PolyTimeComputableLang` witness -/

/-- **The reduction `kSAT_to_SAT_reduction 3` as a concrete layer program** —
the same `kCnf3Check`, on the natural 3-register layout
`[[], replicate |N| 1, encodeCnf N]` (register numbering shared with the
verifier layout, which is what lets one program serve both witnesses).
`decodeOut` inverts the injective stream encoding. -/
noncomputable def kSAT3_reductionLang :
    PolyTimeComputableLang (kSAT_to_SAT_reduction 3) where
  c := kCnf3Check
  encodeIn := fun N => [[], List.replicate N.length 1, encodeCnf N]
  decodeOut := fun s => Function.invFun encodeCnf (State.get s CNF_STREAM)
  cost_bound := fun n => 3500 * (n + 1) ^ 4
  cost_bound_poly := by
    refine ⟨4, ⟨56000, 1, ?_⟩⟩
    intro n hn
    calc 3500 * (n + 1) ^ 4
        ≤ 3500 * (2 * n) ^ 4 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
      _ = 56000 * n ^ 4 := by ring
  cost_bound_mono := fun a b h =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 4)
  encodeIn_size := fun N => by
    have h := encodeCnf_tally_tight N
    show State.size [[], List.replicate N.length 1, encodeCnf N] ≤ _
    simp only [State.size, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil, List.length_replicate, List.length_nil]
    omega
  computes := fun N => by
    obtain ⟨-, hS, -, -, -⟩ :=
      kCnf3Check_run N [[], List.replicate N.length 1, encodeCnf N] rfl rfl
    show Function.invFun encodeCnf
        (State.get (kCnf3Check.eval _) CNF_STREAM) = _
    rw [hS]
    exact Function.leftInverse_invFun encodeCnf_injective _
  cost_le := fun N => by
    obtain ⟨-, -, -, -, hc⟩ :=
      kCnf3Check_run N [[], List.replicate N.length 1, encodeCnf N] rfl rfl
    refine le_trans hc (le_trans (kCheckBudget_mono ?_) (kCheckBudget_le_poly _))
    have := EvalCnfCmd.encodeCnf_length N
    omega
  output_size_le := fun N => by
    have h1 := reduction_size_le N
    have h2 : encodable.size N + 1 ≤ (encodable.size N + 1) ^ 4 :=
      Nat.le_self_pow (by norm_num) _
    have h3 : (encodable.size N + 1) ^ 4 ≤ 3500 * (encodable.size N + 1) ^ 4 := by
      omega
    omega
  enc_bit := fun N => by
    intro reg hreg x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with h | h | h <;> subst h
    · simp at hx
    · simp only [List.mem_replicate] at hx; omega
    · exact EvalCnfCmd.encodeCnf_bit N x hx
  regBound := 29
  usesBelow := kCnf3Check_usesBelow
  width_le := fun N => by
    show ([[], List.replicate N.length 1, encodeCnf N] : State).length ≤ 29
    simp
  noConsLen := kCnf3Check_noConsLen
  allOpsSupported := kCnf3Check_allOpsSupported
  decode_agree := fun N m => by
    have hlen3 : (1 : Nat) < ([[], List.replicate N.length 1, encodeCnf N] : State).length := by
      simp
    have hlen3' : (2 : Nat) < ([[], List.replicate N.length 1, encodeCnf N] : State).length := by
      simp
    have hpad1 : State.get
        (([[], List.replicate N.length 1, encodeCnf N] : State)
          ++ List.replicate m []) CLAUSE_TALLY = List.replicate N.length 1 := by
      show ((([[], List.replicate N.length 1, encodeCnf N] : State)
          ++ List.replicate m [])[(1 : Nat)]?).getD [] = _
      rw [List.getElem?_append_left hlen3]
      rfl
    have hpad2 : State.get
        (([[], List.replicate N.length 1, encodeCnf N] : State)
          ++ List.replicate m []) CNF_STREAM = encodeCnf N := by
      show ((([[], List.replicate N.length 1, encodeCnf N] : State)
          ++ List.replicate m [])[(2 : Nat)]?).getD [] = _
      rw [List.getElem?_append_left hlen3']
      rfl
    obtain ⟨-, hS1, -, -, -⟩ := kCnf3Check_run N
      (([[], List.replicate N.length 1, encodeCnf N] : State)
        ++ List.replicate m []) hpad1 hpad2
    obtain ⟨-, hS2, -, -, -⟩ :=
      kCnf3Check_run N [[], List.replicate N.length 1, encodeCnf N] rfl rfl
    show Function.invFun encodeCnf _ = Function.invFun encodeCnf _
    rw [hS1, hS2]

/-! ## Blocker (a): the concrete re-encoder bundle -/

/-- **The concrete `FreePrecomposeData` for `kSAT 3 → SAT`** — the first live
re-encoder. `eIn` is the SAT verifier's OWN natural pair layout
(`EvalCnfCmd.encodeState`, NOT `encodeIn ∘ gmap` — see the honesty note in the
file header); `mfc = kCnf3Check` does all the reduction work on-machine. -/
noncomputable def kSAT3_precomposeData :
    EvalCnfTM.evalCnfDecidesLang.FreePrecomposeData
      (fun xc : cnf × assgn => (kSAT_to_SAT_reduction 3 xc.1, xc.2)) where
  mfc := kCnf3Check
  eIn := EvalCnfCmd.encodeState
  newBound := fun n => 1000000 * (n + 3) ^ 4
  newBound_poly := by
    refine ⟨4, ⟨256000000, 1, ?_⟩⟩
    intro n hn
    calc 1000000 * (n + 3) ^ 4
        ≤ 1000000 * (4 * n) ^ 4 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
      _ = 256000000 * n ^ 4 := by ring
  newBound_mono := fun a b h =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  bridge := fun v => by
    rcases v with ⟨N, a⟩
    exact kCnf3Check_bridge N a
  encodeIn_size := fun v => by
    have h := EvalCnfCmd.encodeState_size_bound v
    have h2 : encodable.size v + 3 ≤ (encodable.size v + 3) ^ 4 :=
      Nat.le_self_pow (by norm_num) _
    have h3 : (encodable.size v + 3) ^ 4 ≤ 1000000 * (encodable.size v + 3) ^ 4 := by
      omega
    omega
  cost_bound := fun v => by
    rcases v with ⟨N, a⟩
    set n := encodable.size ((N, a) : cnf × assgn) with hn
    show (kCnf3Check ;; EvalCnfCmd.evalCnfCmd).cost (EvalCnfCmd.encodeState (N, a))
        ≤ 1000000 * (n + 3) ^ 4
    rw [Cmd.cost_seq]
    -- the re-encoder's own cost
    obtain ⟨-, -, -, -, hc1⟩ :=
      kCnf3Check_run N (EvalCnfCmd.encodeState (N, a)) rfl rfl
    have hNn : encodable.size N ≤ n := by
      rw [hn]
      show _ ≤ encodable.size N + encodable.size a + 1
      omega
    have hc1' : kCnf3Check.cost (EvalCnfCmd.encodeState (N, a))
        ≤ kCheckBudget (5 * n) := by
      refine le_trans hc1 (kCheckBudget_mono ?_)
      have := EvalCnfCmd.encodeCnf_length N
      omega
    -- the verifier's cost on the re-encoded state, via the bridge + cost_agree
    have hc2eq : EvalCnfCmd.evalCnfCmd.cost
          (kCnf3Check.eval (EvalCnfCmd.encodeState (N, a)))
        = EvalCnfCmd.evalCnfCmd.cost
          (EvalCnfCmd.encodeState (kSAT_to_SAT_reduction 3 N, a)) :=
      Cmd.cost_agree _ 16 EvalCnfCmd.evalCnfCmd_usesBelow (kCnf3Check_bridge N a)
    have hsize : encodable.size ((kSAT_to_SAT_reduction 3 N, a) : cnf × assgn)
        ≤ n + 2 := by
      have := reduction_size_le N
      show encodable.size (kSAT_to_SAT_reduction 3 N) + encodable.size a + 1
          ≤ n + 2
      rw [hn]
      show _ ≤ encodable.size N + encodable.size a + 1 + 2
      omega
    have hc2 : EvalCnfCmd.evalCnfCmd.cost
          (kCnf3Check.eval (EvalCnfCmd.encodeState (N, a)))
        ≤ EvalCnfTM.timeBound (n + 2) := by
      rw [hc2eq]
      exact le_trans (EvalCnfCmd.evalCnfCmd_cost_bound _)
        (EvalCnfTM.timeBound_monotonic _ _ hsize)
    -- arithmetic: 1 + kCheckBudget (5n) + timeBound (n+2) ≤ 1000000·(n+3)⁴
    have ekey : kCheckBudget (5 * n)
        = 1250 * (n*n*n*n) + 1250 * (n*n*n) + 750 * (n*n) + 150 * n + 30 := by
      unfold kCheckBudget; ring
    have etb : EvalCnfTM.timeBound (n + 2) = 200000 * (n + 3) ^ 4 := by
      show 200000 * (n + 2 + 1) ^ 4 = 200000 * (n + 3) ^ 4
      ring
    have e1 : 1000000 * (n + 3) ^ 4
        = 1000000 * (n*n*n*n) + 12000000 * (n*n*n) + 54000000 * (n*n)
          + 108000000 * n + 81000000 := by ring
    have e2 : 200000 * (n + 3) ^ 4
        = 200000 * (n*n*n*n) + 2400000 * (n*n*n) + 10800000 * (n*n)
          + 21600000 * n + 16200000 := by ring
    omega
  enc_bit := EvalCnfCmd.encodeState_bit
  regBound := 29
  usesBelow :=
    ⟨kCnf3Check_usesBelow,
     Cmd.UsesBelow_mono (by omega) EvalCnfCmd.evalCnfCmd_usesBelow⟩
  width_le := fun v => by
    rcases v with ⟨N, a⟩
    show (EvalCnfCmd.encodeState (N, a)).length ≤ 29
    simp only [EvalCnfCmd.encodeState, List.length_cons, List.length_nil]
    omega
  noConsLen := ⟨kCnf3Check_noConsLen, EvalCnfCmd.evalCnfCmd_noConsLen⟩
  allOpsSupported :=
    ⟨kCnf3Check_allOpsSupported, EvalCnfCmd.evalCnfCmd_allOpsSupported⟩

/-! ## The headline: a live `red_inNP` through the free engine -/

/-- **`inNP (kSAT 3)`, routed through the free-encoding layer engine** — the
first live application of `red_inNP_of_langFree`, with BOTH per-reduction
obligations discharged by concrete, honest programs (re-encoder
`kSAT3_precomposeData` + reduction witness `kSAT3_reductionLang`). Parallel to
the framework-level `inNP_kSAT` (which routes through the opaque `red_inNP`);
this one preserves a recoverable verifier `Cmd` end to end.
Axiom-clean: `[propext, Classical.choice, Quot.sound]`. -/
theorem inNP_kSAT3_free : inNP (kSAT 3) :=
  red_inNP_of_langFree EvalCnfTM.SAT_inNPWitnessLangFree kSAT3_reductionLang
    kSAT3_precomposeData (kSAT_to_SAT_correct 3)

/-- **The first live honest `⪯p'` on the real chain: `kSAT 3 ⪯p' SAT`.** The
TM-backed reduction witness comes from the same free layer witness
`kSAT3_reductionLang` via `reducesPolyMO'_of_langFree` — demonstrating that the
`⪯p` → `⪯p'` re-typing (ROADMAP step 2) needs nothing beyond a free
`PolyTimeComputableLang` per chain step (no canonical encoding, no product
trio). Axiom-clean: `[propext, Classical.choice, Quot.sound]`. -/
theorem kSAT3_reducesPolyMO' : kSAT 3 ⪯p' SAT :=
  reducesPolyMO'_of_langFree kSAT3_reductionLang (kSAT_to_SAT_correct 3)

end KSat3Free
