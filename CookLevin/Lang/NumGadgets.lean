import CookLevin.Lang.PolyTime

/-!
# Unary number gadgets

Programs on unary registers: `readNum` copies the length of a prefix of a register into a
unary register, `cSkip` skips over a block and `ltBit` compares two unary numbers, each with
its run and cost lemma.
-/

set_option autoImplicit false

namespace NumGadgets

open CookLevin.Lang

/-! ## Register conventions

Numbers are unary `1`-blocks terminated by a `0`; a list of numbers is a stream of such
blocks, and its length is kept in a separate unary tally register that serves as a loop
bound. The gadgets use the scratch registers `HEAD`, `INBLK`, `LT_B` and `SKIPR`. -/

def HEAD        : Var := 15
def INBLK       : Var := 16
def LT_B        : Var := 22
def SKIPR       : Var := 26

/-- Constant-cost no-op (`SKIPR := [1]`), the idle branch of guarded bodies.
`clear ⨾ appendOne` so the cost is state-independent (mirrors `EvalCnfCmd.mcSkip`,
needed since `eqBit` is size-aware). -/
def cSkip : Cmd := Cmd.op (.clear SKIPR) ;; Cmd.op (.appendOne SKIPR)

/-- Read one terminated unary block `replicate v 1 ++ [0]` off the front of
`stream` into `dst` (as `replicate v 1`), consuming the block + terminator from
`stream`. `idx` is the loop counter; the loop bound is `stream`'s entry length
(generous — once the block's `0` terminator clears `INBLK`, the remaining
iterations idle). Mirrors `EvalCnfCmd.varExtractBody`. -/
def readNum (dst stream idx : Var) : Cmd :=
  Cmd.op (.clear dst) ;;
  Cmd.op (.clear INBLK) ;; Cmd.op (.appendOne INBLK) ;;
  Cmd.forBnd idx stream
    (Cmd.ifBit INBLK
      (Cmd.op (.head HEAD stream) ;;
       Cmd.op (.tail stream stream) ;;
       Cmd.ifBit HEAD
         (Cmd.op (.appendOne dst))
         (Cmd.op (.clear INBLK)))
      cSkip)

/-- **Unary strict-less-than**: `dst := [1]` if the
unary value in `A` is `< ` the unary value in `B`, else `[0]`.


**Correct (and simpler) realization** — `tail []` is `[]`, so an *unconditional*
lockstep drain needs no guard: copy `B` into `LT_B`, then `tail LT_B` once per
cell of `A` (`|A| = a` iterations). After `a` iterations `LT_B = replicate (b−a) 1`
(truncated subtraction), so `LT_B` is non-empty iff `b > a` iff `a < b`. Read the
verdict with one `nonEmpty`. (`A` is the loop *bound* — `forBnd` reads its length
once at entry, so `A` is never consumed; only `LT_B`, `idx`, `dst` are written.)
Proven in `ltBit_run`. -/
def ltBit (dst A B idx : Var) : Cmd :=
  Cmd.op (.copy LT_B B) ;;
  Cmd.forBnd idx A (Cmd.op (.tail LT_B LT_B)) ;;
  Cmd.op (.nonEmpty dst LT_B)

/-! ### Structural fields -/

/-! ### Leaf run-lemmas for the verifier checks

The correctness lemma of each gadget. -/

/-- `(replicate n 1).tail = replicate (n-1) 1` (the loop step of `ltBit`'s
drain). -/
private theorem tail_replicate_one (n : Nat) :
    (List.replicate n (1 : Nat)).tail = List.replicate (n - 1) 1 := by
  cases n with
  | zero => rfl
  | succ m => rfl

/-- `(replicate n 1).isEmpty = decide (n = 0)` (the verdict read of `ltBit`). -/
private theorem isEmpty_replicate_one (n : Nat) :
    (List.replicate n (1 : Nat)).isEmpty = decide (n = 0) := by
  cases n with
  | zero => rfl
  | succ m => rfl

/-- **The unary strict-less-than gadget is correct.** If `A` holds `replicate a 1`
and `B` holds `replicate b 1`, and the scratch register `LT_B`, the loop counter
`idx` and the output `dst` are disjoint from the operands, then `ltBit dst A B
idx` writes `[if a < b then 1 else 0]` to `dst` and leaves every register outside
`{LT_B, idx, dst}` untouched.

The loop drains `LT_B` (a copy of `B`) once per cell of `A` (`a` iterations);
after the loop `LT_B = replicate (b − a) 1`, non-empty iff `b > a`. -/
theorem ltBit_run (st : State) (a b : Nat) (dst A B idx : Var)
    (hA : State.get st A = List.replicate a 1)
    (hB : State.get st B = List.replicate b 1)
    (hALT : A ≠ LT_B) (hidxLT : idx ≠ LT_B) :
    State.get ((ltBit dst A B idx).eval st) dst = [if a < b then 1 else 0]
    ∧ (∀ r : Var, r ≠ LT_B → r ≠ idx → r ≠ dst →
        State.get ((ltBit dst A B idx).eval st) r = State.get st r) := by
  -- Phase 1 — the copy `LT_B := B`.
  have hcopy : (Cmd.op (.copy LT_B B)).eval st = State.set st LT_B (List.replicate b 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hB]
  -- Unfold `ltBit` into `loop ;; nonEmpty` over the post-copy state `st1`.
  have heval : (ltBit dst A B idx).eval st
      = (Cmd.op (.nonEmpty dst LT_B)).eval
          ((Cmd.forBnd idx A (Cmd.op (.tail LT_B LT_B))).eval
            (State.set st LT_B (List.replicate b 1))) := by
    simp only [ltBit]; rw [Cmd.eval_seq, Cmd.eval_seq, hcopy]
  rw [heval]
  -- The loop is a `foldlState` over `List.range a` (the bound `A`'s length).
  rw [Cmd.eval_forBnd]
  have hAlen : (State.get (State.set st LT_B (List.replicate b 1)) A).length = a := by
    rw [State.get_set_ne _ _ _ _ hALT, hA, List.length_replicate]
  rw [hAlen]
  -- Loop invariant: after `i` iterations `LT_B = replicate (b − i) 1`, and every
  -- register outside `{LT_B, idx}` is unchanged from the post-copy state.
  obtain ⟨hLT2, hfr2⟩ :
      State.get (Cmd.foldlState (Cmd.op (.tail LT_B LT_B)) idx (List.range a)
          (State.set st LT_B (List.replicate b 1))) LT_B = List.replicate (b - a) 1
      ∧ (∀ r : Var, r ≠ LT_B → r ≠ idx →
          State.get (Cmd.foldlState (Cmd.op (.tail LT_B LT_B)) idx (List.range a)
            (State.set st LT_B (List.replicate b 1))) r
            = State.get (State.set st LT_B (List.replicate b 1)) r) := by
    refine Cmd.foldlState_range_induct (Cmd.op (.tail LT_B LT_B)) idx a
      (State.set st LT_B (List.replicate b 1))
      (fun i s => State.get s LT_B = List.replicate (b - i) 1
        ∧ ∀ r : Var, r ≠ LT_B → r ≠ idx →
            State.get s r = State.get (State.set st LT_B (List.replicate b 1)) r)
      ⟨by rw [State.get_set_eq, Nat.sub_zero], fun _ _ _ => rfl⟩ ?_
    intro i s _ hM
    obtain ⟨hLT, hfr⟩ := hM
    refine ⟨?_, ?_⟩
    · rw [Cmd.eval_op]; simp only [Op.eval]
      rw [State.get_set_eq, State.get_set_ne _ _ _ _ (Ne.symm hidxLT), hLT,
        tail_replicate_one, Nat.sub_sub]
    · intro r hrLT hridx
      rw [Cmd.eval_op]; simp only [Op.eval]
      rw [State.get_set_ne _ _ _ _ hrLT, State.get_set_ne _ _ _ _ hridx]
      exact hfr r hrLT hridx
  -- Phase 3 — read the verdict with `nonEmpty dst LT_B`.
  refine ⟨?_, ?_⟩
  · rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, hLT2, isEmpty_replicate_one,
      decide_eq_true_eq]
    by_cases hab : a < b
    · rw [if_neg (show ¬ (b - a = 0) by omega), if_pos hab]
    · rw [if_pos (show b - a = 0 by omega), if_neg hab]
  · intro r hrLT hridx hrdst
    rw [Cmd.eval_op]; simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ hrdst, hfr2 r hrLT hridx,
      State.get_set_ne _ _ _ _ hrLT]

/-! ### `readNum`: the unary-block reader (keystone leaf, used by all 5 checks)

`readNum dst stream idx` reads one terminated unary block `replicate v 1 ++ [0]`
off the front of `stream` into `dst` (as `replicate v 1`), consuming the block and
its terminator from `stream`. The structure mirrors the
`EvalCnfCmd.varExtractBody` loop (`LVInv`/`LVInv_step`/`processOneLiteral_main`),
generalised so `dst`/`stream`/`idx` are *parameters* — hence the explicit
register-distinctness hypotheses (the EvalCnf proof used `by decide` on fixed
register `def`s). Callers discharge them by `decide` on the concrete registers
(`dst ∈ {17..20}`, `stream ∈ {11..14}`, `idx ∈ {8,9,10}`, `HEAD = 15`,
`INBLK = 16`, `SKIPR = 26` pairwise distinct). -/

theorem cSkip_eval (s : State) : cSkip.eval s = s.set SKIPR [1] := by
  show ((Cmd.op (.clear SKIPR)) ;; Cmd.op (.appendOne SKIPR)).eval s = _
  rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
  simp only [Op.eval, State.get_set_eq, List.nil_append, State.set_set]

theorem cSkip_cost (s : State) : cSkip.cost s = 3 := by
  show ((Cmd.op (.clear SKIPR)) ;; Cmd.op (.appendOne SKIPR)).cost s = _
  rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]; rfl

theorem replicate_one_snoc (n : Nat) :
    List.replicate n (1 : Nat) ++ [1] = List.replicate (n + 1) 1 :=
  List.replicate_succ'.symm

theorem replicate_one_eq_iff {a b : Nat} :
    (List.replicate a (1 : Nat) = List.replicate b 1) ↔ a = b := by
  constructor
  · intro h; have := congrArg List.length h; simpa using this
  · rintro rfl; rfl

/-- The `readNum` loop invariant (cf. `EvalCnfCmd.LVInv`). Through iteration `v`
the loop consumes the unary block (one cell/iteration) into `dst`; at iteration
`v` it consumes the `0` terminator and clears `INBLK`; afterwards it idles. The
frame is relative to `st`, the loop-entry (post-init) state. -/
private def RNInv (v : Nat) (rest : List Nat) (dst stream idx : Var) (st : State)
    (i : Nat) (s : State) : Prop :=
  (if i ≤ v then
    s.get INBLK = [1] ∧ s.get dst = List.replicate i 1
      ∧ s.get stream = List.replicate (v - i) 1 ++ 0 :: rest
  else
    s.get INBLK = [] ∧ s.get dst = List.replicate v 1
      ∧ s.get stream = rest)
  ∧ ∀ r : Var, r ≠ stream → r ≠ dst → r ≠ INBLK → r ≠ HEAD → r ≠ SKIPR →
      r ≠ idx → s.get r = st.get r

/-- The `readNum` body shape (the `forBnd` iteration body). -/
private def readNumBody (dst stream : Var) : Cmd :=
  Cmd.ifBit INBLK
    (Cmd.op (.head HEAD stream) ;;
     Cmd.op (.tail stream stream) ;;
     Cmd.ifBit HEAD (Cmd.op (.appendOne dst)) (Cmd.op (.clear INBLK)))
    cSkip

private theorem readNum_step (v : Nat) (rest : List Nat) (dst stream idx : Var)
    (st : State)
    (hsd : stream ≠ dst) (hsi : stream ≠ idx) (hdi : dst ≠ idx)
    (hsHead : stream ≠ HEAD) (hsInbk : stream ≠ INBLK) (hsSkip : stream ≠ SKIPR)
    (hdHead : dst ≠ HEAD) (hdInbk : dst ≠ INBLK) (hdSkip : dst ≠ SKIPR)
    (hiHead : idx ≠ HEAD) (hiInbk : idx ≠ INBLK) (hiSkip : idx ≠ SKIPR)
    (i : Nat) (s : State) (h : RNInv v rest dst stream idx st i s) :
    RNInv v rest dst stream idx st (i + 1)
      ((readNumBody dst stream).eval (s.set idx (List.replicate i 1))) := by
  obtain ⟨hphase, hframe⟩ := h
  by_cases hiv : i ≤ v
  · rw [if_pos hiv] at hphase
    obtain ⟨hIB, hDS, hCS⟩ := hphase
    have hIB' : (s.set idx (List.replicate i 1)).get INBLK = [1] := by
      rw [State.get_set_ne _ _ _ _ hiInbk.symm]; exact hIB
    have hCS' : (s.set idx (List.replicate i 1)).get stream
        = List.replicate (v - i) 1 ++ 0 :: rest := by
      rw [State.get_set_ne _ _ _ _ hsi]; exact hCS
    have hDS' : (s.set idx (List.replicate i 1)).get dst
        = List.replicate i 1 := by
      rw [State.get_set_ne _ _ _ _ hdi]; exact hDS
    have heval : (readNumBody dst stream).eval (s.set idx (List.replicate i 1))
        = (Cmd.op (.head HEAD stream) ;;
           Cmd.op (.tail stream stream) ;;
           Cmd.ifBit HEAD (Cmd.op (.appendOne dst))
             (Cmd.op (.clear INBLK))).eval
            (s.set idx (List.replicate i 1)) := by
      show (Cmd.ifBit INBLK _ _).eval _ = _
      rw [Cmd.eval_ifBit_true _ _ _ _ hIB']
    by_cases hiv2 : i < v
    · -- interior `1` cell of the unary block
      have hsplit : List.replicate (v - i) (1 : Nat) ++ 0 :: rest
          = 1 :: (List.replicate (v - (i + 1)) 1 ++ 0 :: rest) := by
        have hvi : v - i = (v - (i + 1)) + 1 := by omega
        rw [hvi, List.replicate_succ, List.cons_append]
      rw [hsplit] at hCS'
      have e1 : (Cmd.op (.head HEAD stream)).eval
          (s.set idx (List.replicate i 1))
          = (s.set idx (List.replicate i 1)).set HEAD [1] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hCS']
      have e2 : (Cmd.op (.tail stream stream)).eval
          ((s.set idx (List.replicate i 1)).set HEAD [1])
          = ((s.set idx (List.replicate i 1)).set HEAD [1]).set
              stream (List.replicate (v - (i + 1)) 1 ++ 0 :: rest) := by
        rw [Cmd.eval_op]; simp only [Op.eval]
        rw [State.get_set_ne _ _ _ _ hsHead, hCS', List.tail_cons]
      have hHC : (((s.set idx (List.replicate i 1)).set HEAD [1]).set
          stream (List.replicate (v - (i + 1)) 1 ++ 0 :: rest)).get HEAD
          = [1] := by
        rw [State.get_set_ne _ _ _ _ hsHead.symm, State.get_set_eq]
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_ifBit_true _ _ _ _ hHC,
        Cmd.eval_op] at heval
      simp only [Op.eval] at heval
      rw [State.get_set_ne _ _ _ _ hsd.symm,
        State.get_set_ne _ _ _ _ hdHead,
        State.get_set_ne _ _ _ _ hdi, hDS, replicate_one_snoc] at heval
      rw [heval]
      constructor
      · rw [if_pos (by omega : i + 1 ≤ v)]
        refine ⟨?_, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ hdInbk.symm,
            State.get_set_ne _ _ _ _ hsInbk.symm,
            State.get_set_ne _ _ _ _ (by decide : (INBLK : Var) ≠ HEAD),
            State.get_set_ne _ _ _ _ hiInbk.symm]
          exact hIB
        · rw [State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ hsd, State.get_set_eq]
      · intro r hrs hrd hri hrh hrsk hridx
        rw [State.get_set_ne _ _ _ _ hrd, State.get_set_ne _ _ _ _ hrs,
          State.get_set_ne _ _ _ _ hrh, State.get_set_ne _ _ _ _ hridx]
        exact hframe r hrs hrd hri hrh hrsk hridx
    · -- the `0` terminator (`i = v`)
      have hiv3 : i = v := by omega
      subst hiv3
      have hsplit : List.replicate (i - i) (1 : Nat) ++ 0 :: rest
          = 0 :: rest := by
        rw [Nat.sub_self]; rfl
      rw [hsplit] at hCS'
      have e1 : (Cmd.op (.head HEAD stream)).eval
          (s.set idx (List.replicate i 1))
          = (s.set idx (List.replicate i 1)).set HEAD [0] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hCS']
      have e2 : (Cmd.op (.tail stream stream)).eval
          ((s.set idx (List.replicate i 1)).set HEAD [0])
          = ((s.set idx (List.replicate i 1)).set HEAD [0]).set
              stream rest := by
        rw [Cmd.eval_op]; simp only [Op.eval]
        rw [State.get_set_ne _ _ _ _ hsHead, hCS', List.tail_cons]
      have hHC : (((s.set idx (List.replicate i 1)).set HEAD [0]).set
          stream rest).get HEAD ≠ [1] := by
        rw [State.get_set_ne _ _ _ _ hsHead.symm, State.get_set_eq]; decide
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_ifBit_false _ _ _ _ hHC,
        Cmd.eval_op] at heval
      simp only [Op.eval] at heval
      rw [heval]
      constructor
      · rw [if_neg (by omega : ¬ i + 1 ≤ i)]
        refine ⟨?_, ?_, ?_⟩
        · rw [State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ hdInbk,
            State.get_set_ne _ _ _ _ hsd.symm,
            State.get_set_ne _ _ _ _ hdHead,
            State.get_set_ne _ _ _ _ hdi]
          exact hDS
        · rw [State.get_set_ne _ _ _ _ hsInbk, State.get_set_eq]
      · intro r hrs hrd hri hrh hrsk hridx
        rw [State.get_set_ne _ _ _ _ hri, State.get_set_ne _ _ _ _ hrs,
          State.get_set_ne _ _ _ _ hrh, State.get_set_ne _ _ _ _ hridx]
        exact hframe r hrs hrd hri hrh hrsk hridx
  · -- idle phase
    rw [if_neg hiv] at hphase
    obtain ⟨hIB, hDS, hCS⟩ := hphase
    have hIB' : (s.set idx (List.replicate i 1)).get INBLK ≠ [1] := by
      rw [State.get_set_ne _ _ _ _ hiInbk.symm, hIB]; decide
    have heval : (readNumBody dst stream).eval (s.set idx (List.replicate i 1))
        = (s.set idx (List.replicate i 1)).set SKIPR [1] := by
      show (Cmd.ifBit INBLK _ _).eval _ = _
      rw [Cmd.eval_ifBit_false _ _ _ _ hIB', cSkip_eval]
    rw [heval]
    constructor
    · rw [if_neg (by omega : ¬ i + 1 ≤ v)]
      refine ⟨?_, ?_, ?_⟩
      · rw [State.get_set_ne _ _ _ _ (by decide : (INBLK : Var) ≠ SKIPR),
          State.get_set_ne _ _ _ _ hiInbk.symm]
        exact hIB
      · rw [State.get_set_ne _ _ _ _ hdSkip,
          State.get_set_ne _ _ _ _ hdi]
        exact hDS
      · rw [State.get_set_ne _ _ _ _ hsSkip,
          State.get_set_ne _ _ _ _ hsi]
        exact hCS
    · intro r hrs hrd hri hrh hrsk hridx
      rw [State.get_set_ne _ _ _ _ hrsk, State.get_set_ne _ _ _ _ hridx]
      exact hframe r hrs hrd hri hrh hrsk hridx

/-- **The unary-block reader is correct.** With one terminated unary block
`replicate v 1 ++ [0] ++ rest` at the head of `stream`, `readNum dst stream idx`
writes `replicate v 1` into `dst`, advances `stream` past the block to `rest`, and
leaves every register outside `{stream, dst, INBLK, HEAD, SKIPR, idx}` untouched. -/
theorem readNum_run (st : State) (v : Nat) (rest : List Nat)
    (dst stream idx : Var)
    (hstream : st.get stream = List.replicate v 1 ++ 0 :: rest)
    (hsd : stream ≠ dst) (hsi : stream ≠ idx) (hdi : dst ≠ idx)
    (hsHead : stream ≠ HEAD) (hsInbk : stream ≠ INBLK) (hsSkip : stream ≠ SKIPR)
    (hdHead : dst ≠ HEAD) (hdInbk : dst ≠ INBLK) (hdSkip : dst ≠ SKIPR)
    (hiHead : idx ≠ HEAD) (hiInbk : idx ≠ INBLK) (hiSkip : idx ≠ SKIPR) :
    ((readNum dst stream idx).eval st).get dst = List.replicate v 1
    ∧ ((readNum dst stream idx).eval st).get stream = rest
    ∧ (∀ r : Var, r ≠ stream → r ≠ dst → r ≠ INBLK → r ≠ HEAD → r ≠ SKIPR →
        r ≠ idx → ((readNum dst stream idx).eval st).get r = st.get r) := by
  -- evaluate the `clear dst ;; clear INBLK ;; appendOne INBLK` init prefix
  have e1 : (Cmd.op (.clear dst)).eval st = st.set dst [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e2 : (Cmd.op (.clear INBLK)).eval (st.set dst [])
      = (st.set dst []).set INBLK [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e3 : (Cmd.op (.appendOne INBLK)).eval ((st.set dst []).set INBLK [])
      = ((st.set dst []).set INBLK []).set INBLK [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [State.get_set_eq, List.nil_append]
  have eP : (readNum dst stream idx).eval st
      = (Cmd.forBnd idx stream (readNumBody dst stream)).eval
          (((st.set dst []).set INBLK []).set INBLK [1]) := by
    show (Cmd.eval (_ ;; _ ;; _ ;; _) st) = _
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3]
    rfl
  have hslen : ((((st.set dst []).set INBLK []).set INBLK [1]).get stream).length
      = v + 1 + rest.length := by
    rw [State.get_set_ne _ _ _ _ hsInbk, State.get_set_ne _ _ _ _ hsInbk,
      State.get_set_ne _ _ _ _ hsd, hstream]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  have hbase : RNInv v rest dst stream idx
      (((st.set dst []).set INBLK []).set INBLK [1]) 0
      (((st.set dst []).set INBLK []).set INBLK [1]) := by
    refine ⟨?_, fun r _ _ _ _ _ _ => rfl⟩
    rw [if_pos (Nat.zero_le v)]
    refine ⟨?_, ?_, ?_⟩
    · rw [State.get_set_eq]
    · show _ = List.replicate 0 1
      rw [State.get_set_ne _ _ _ _ hdInbk, State.get_set_ne _ _ _ _ hdInbk,
        State.get_set_eq]
      rfl
    · rw [Nat.sub_zero, State.get_set_ne _ _ _ _ hsInbk,
        State.get_set_ne _ _ _ _ hsInbk, State.get_set_ne _ _ _ _ hsd, hstream]
  have hInv : RNInv v rest dst stream idx
      (((st.set dst []).set INBLK []).set INBLK [1]) (v + 1 + rest.length)
      ((readNum dst stream idx).eval st) := by
    rw [eP, Cmd.eval_forBnd, hslen]
    exact Cmd.foldlState_range_induct (readNumBody dst stream) idx
      (v + 1 + rest.length) (((st.set dst []).set INBLK []).set INBLK [1])
      (RNInv v rest dst stream idx (((st.set dst []).set INBLK []).set INBLK [1]))
      hbase
      (fun i s _ h => readNum_step v rest dst stream idx
        (((st.set dst []).set INBLK []).set INBLK [1])
        hsd hsi hdi hsHead hsInbk hsSkip hdHead hdInbk hdSkip
        hiHead hiInbk hiSkip i s h)
  obtain ⟨hphase, hframe⟩ := hInv
  rw [if_neg (by omega : ¬ (v + 1 + rest.length ≤ v))] at hphase
  obtain ⟨_, hDSfin, hSTfin⟩ := hphase
  refine ⟨hDSfin, hSTfin, ?_⟩
  intro r hrs hrd hri hrh hrsk hridx
  rw [hframe r hrs hrd hri hrh hrsk hridx,
    State.get_set_ne _ _ _ _ hri, State.get_set_ne _ _ _ _ hri,
    State.get_set_ne _ _ _ _ hrd]

/-! ### Per-check run-lemmas (AND-into-`OUTPUT`)

Each check ANDs its predicate into `OUTPUT`: starting from `OUTPUT = [if b then 1
else 0]`, after the check `OUTPUT = [if b && decide P then 1 else 0]` (the check
only ever *rejects*, never accepts), and the read-only input registers (1–6) are
preserved. The assembly (`cliqueRelCmd`) starts `OUTPUT = [1]` and chains them, so
the final bit is the conjunction of all five predicates = `cliqueRel`. -/

/-! ### `memberEdge`: the edge-membership FOUND-flag leaf (clique inner)

`memberEdge` sets `FOUND := [1]` iff the ordered pair `(va, vb)` (held unary in
`VALA`/`VALB`) occurs in the edge stream. A single `forBnd` over the edge tally
whose body reads both unary endpoints (`VALC`/`VALD`) and `eqBit`s them against
`VALA`/`VALB`. Unlike the AND-into-`OUTPUT` checks this is an OR-style
accumulator (set on match), so the invariant is phase-free. -/

/-! ### `checkNodup`: the duplicate-free check (nested loop, counter reads) -/

/-! ### `checkClique`: the clique-adjacency check (depth-4 nested loop) -/

/-! ### `decides` assembly — the 5 checks chained into `OUTPUT` -/

/-! ### Cost lemmas

Mirrors `EvalCnfCmd`'s `_cost` quartet. **Key simplification: the
cost proofs use *length-only* loop invariants** (`M i s := (s.get reg).length ≤ …`)
rather than the behavioural invariants (`RNInv`/`COInv`/…) the run-lemmas use.
Body cost depends only on the register *lengths* it touches, and those lengths are
non-increasing through every loop here (streams are consumed by `tail`, scratch
copies only shrink), so a length bound is preserved by `hM` regardless of the
control-flow branch — no need to track the exact stream contents or the accumulated
predicate. Each loop is closed by `Cmd.cost_forBnd_le` with `B` = a uniform
per-iteration body-cost bound. -/

/-- `readNumBody` never grows `stream` and costs at most `S + 7` when
`|stream| ≤ S`. The uniform per-iteration ingredient for `readNum_cost`. -/
theorem readNumBody_effect (dst stream : Var) (S : Nat) (w : State)
    (hsd : stream ≠ dst) (hsHead : stream ≠ HEAD) (hsInbk : stream ≠ INBLK)
    (hsSkip : stream ≠ SKIPR) (hw : (State.get w stream).length ≤ S) :
    (State.get ((readNumBody dst stream).eval w) stream).length ≤ S
    ∧ (readNumBody dst stream).cost w ≤ S + 7 := by
  -- the inner `ifBit HEAD (appendOne dst) (clear INBLK)` never touches `stream`,
  -- and costs at most `2`
  have hif_frame : ∀ t : State,
      State.get ((Cmd.ifBit HEAD (Cmd.op (.appendOne dst))
          (Cmd.op (.clear INBLK))).eval t) stream = State.get t stream := by
    intro t
    by_cases hh : State.get t HEAD = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hh, Cmd.eval_op]; simp only [Op.eval]
      rw [State.get_set_ne _ _ _ _ hsd]
    · rw [Cmd.eval_ifBit_false _ _ _ _ hh, Cmd.eval_op]; simp only [Op.eval]
      rw [State.get_set_ne _ _ _ _ hsInbk]
  have hif_cost : ∀ t : State,
      (Cmd.ifBit HEAD (Cmd.op (.appendOne dst)) (Cmd.op (.clear INBLK))).cost t ≤ 2 := by
    intro t
    by_cases hh : State.get t HEAD = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ hh]; simp [Cmd.cost_op, Op.cost]
    · rw [Cmd.cost_ifBit_false _ _ _ _ hh]; simp [Cmd.cost_op, Op.cost]
  by_cases hIB : State.get w INBLK = [1]
  · -- active branch: head ;; tail stream ;; ifBit
    have hhead : State.get ((Cmd.op (.head HEAD stream)).eval w) stream
        = State.get w stream := by
      rw [Cmd.eval_op]; simp only [Op.eval]; rw [State.get_set_ne _ _ _ _ hsHead]
    have htail : State.get ((Cmd.op (.tail stream stream)).eval
        ((Cmd.op (.head HEAD stream)).eval w)) stream
        = (State.get w stream).tail := by
      rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; rw [hhead]
    constructor
    · -- length
      have heval : (readNumBody dst stream).eval w
          = (Cmd.ifBit HEAD (Cmd.op (.appendOne dst)) (Cmd.op (.clear INBLK))).eval
              ((Cmd.op (.tail stream stream)).eval ((Cmd.op (.head HEAD stream)).eval w)) := by
        show (Cmd.ifBit INBLK _ _).eval w = _
        rw [Cmd.eval_ifBit_true _ _ _ _ hIB, Cmd.eval_seq, Cmd.eval_seq]
      rw [heval, hif_frame, htail, List.length_tail]
      omega
    · -- cost
      have hcost : (readNumBody dst stream).cost w
          = 1 + (Cmd.op (.head HEAD stream) ;; Cmd.op (.tail stream stream) ;;
              Cmd.ifBit HEAD (Cmd.op (.appendOne dst)) (Cmd.op (.clear INBLK))).cost w := by
        show (Cmd.ifBit INBLK _ _).cost w = _
        rw [Cmd.cost_ifBit_true _ _ _ _ hIB]
      rw [hcost, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_seq, Cmd.cost_op]
      have htlcost : Op.cost (.tail stream stream) ((Cmd.op (.head HEAD stream)).eval w)
          = (State.get w stream).length + 1 := by
        show (State.get ((Cmd.op (.head HEAD stream)).eval w) stream).length + 1 = _
        rw [hhead]
      rw [htlcost]
      have hile := hif_cost ((Cmd.op (.tail stream stream)).eval
        ((Cmd.op (.head HEAD stream)).eval w))
      simp only [Op.cost]
      omega
  · -- idle branch: cSkip
    have heval : (readNumBody dst stream).eval w = w.set SKIPR [1] := by
      show (Cmd.ifBit INBLK _ _).eval w = _
      rw [Cmd.eval_ifBit_false _ _ _ _ hIB, cSkip_eval]
    have hcost : (readNumBody dst stream).cost w = 1 + 3 := by
      show (Cmd.ifBit INBLK _ _).cost w = _
      rw [Cmd.cost_ifBit_false _ _ _ _ hIB, cSkip_cost]
    constructor
    · rw [heval, State.get_set_ne _ _ _ _ hsSkip]; exact hw
    · omega

/-- **`readNum` cost bound.** Reading (draining) `stream` costs `≤ 2·S² + 7·S + 7`
where `S = |stream|` at entry. No block-form hypothesis: the bound holds for any
stream content (the loop drains one cell/iteration, each a `tail` of cost `≤ S`). -/
theorem readNum_cost (st : State) (dst stream idx : Var)
    (hsd : stream ≠ dst) (hsi : stream ≠ idx)
    (hsHead : stream ≠ HEAD) (hsInbk : stream ≠ INBLK) (hsSkip : stream ≠ SKIPR) :
    (readNum dst stream idx).cost st
      ≤ 2 * (State.get st stream).length * (State.get st stream).length
          + 7 * (State.get st stream).length + 7 := by
  set S := (State.get st stream).length with hS
  have hstreamlen : (State.get st stream).length = S := hS.symm
  -- init prefix evaluation
  have e1 : (Cmd.op (.clear dst)).eval st = st.set dst [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e2 : (Cmd.op (.clear INBLK)).eval (st.set dst [])
      = (st.set dst []).set INBLK [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e3 : (Cmd.op (.appendOne INBLK)).eval ((st.set dst []).set INBLK [])
      = ((st.set dst []).set INBLK []).set INBLK [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [State.get_set_eq, List.nil_append]
  set s0 := ((st.set dst []).set INBLK []).set INBLK [1] with hs0
  have hcost_eq : (readNum dst stream idx).cost st
      = 6 + (Cmd.forBnd idx stream (readNumBody dst stream)).cost s0 := by
    show (Cmd.cost (_ ;; _ ;; _ ;; _) st) = _
    rw [Cmd.cost_seq, e1, Cmd.cost_seq, e2, Cmd.cost_seq, e3, Cmd.cost_op,
      Cmd.cost_op, Cmd.cost_op]
    simp only [Op.cost, readNumBody]; omega
  have hs0stream : State.get s0 stream = State.get st stream := by
    rw [State.get_set_ne _ _ _ _ hsInbk, State.get_set_ne _ _ _ _ hsInbk,
      State.get_set_ne _ _ _ _ hsd]
  have hbound : (State.get s0 stream).length = S := by rw [hs0stream, hstreamlen]
  have hloop : (Cmd.forBnd idx stream (readNumBody dst stream)).cost s0
      ≤ 1 + S * (S + 7) + S * S := by
    have h := Cmd.cost_forBnd_le idx stream (readNumBody dst stream) s0 (S + 7)
      (fun _ s => (State.get s stream).length ≤ S)
      hbound.le
      (fun i s _ hM => (readNumBody_effect dst stream S (s.set idx (List.replicate i 1))
          hsd hsHead hsInbk hsSkip
          (by rw [State.get_set_ne _ _ _ _ hsi]; exact hM)).1)
      (fun i s _ hM => (readNumBody_effect dst stream S (s.set idx (List.replicate i 1))
          hsd hsHead hsInbk hsSkip
          (by rw [State.get_set_ne _ _ _ _ hsi]; exact hM)).2)
    rw [hbound] at h; exact h
  rw [hcost_eq]
  have hr1 : S * (S + 7) = S * S + 7 * S := by ring
  have hr2 : 2 * S * S = S * S + S * S := by ring
  omega

/-! ### The cost bound assembly -/

end NumGadgets

