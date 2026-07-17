import Complexity.NP.SAT.CookLevin.Reductions.FSAT_to_SAT_free_run

set_option autoImplicit false

/-! # `FSAT → SAT` — cost accounting, the free witness, the headline `⪯p'`

Third module of the build-health split (2026-07-17, see `_run`'s header):
the cost ladder (`tokenBody_cost` → `outerLoop_cost` → `buildSAT_cost_le`,
`satBound = O(n⁸)`), `fsatSAT_reductionLang`, and
`fsatSAT_reducesPolyMO' : FSAT ⪯p' SAT`. Downstream imports of
`…Reductions.FSAT_to_SAT_free` are unchanged (this module transitively
re-exports `_run` and `_defs`). NOTE: the cost proofs consume the run lemmas,
so `_run` → this module is inherently SERIAL. -/

namespace FSATSATFree

open Complexity.Lang
open PreTseytin
open BinaryCCFSATFree (serF)
open EvalCnfCmd (encodeCnf encodeClause encodeLit)
open BinaryCCFSATFree (readUnary readUnary_replicate formula_size_le_serF)

/-! ## Cost accounting — leaf loop cost lemmas -/

/-- Preservation helper: `drainVarBody` never grows `SCAN`. -/
theorem drainVarBody_SCAN_le (st : State) (m0 : Nat)
    (h : (State.get st SCAN).length ≤ m0) :
    (State.get (drainVarBody.eval st) SCAN).length ≤ m0 := by
  unfold drainVarBody
  by_cases hDN : State.get st DN = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hDN, nop, Cmd.eval_op, Op.eval,
      State.get_set_ne _ _ _ _ (show SCAN ≠ SKIP by decide)]
    exact h
  · rw [Cmd.eval_ifBit_false _ _ _ _ hDN, Cmd.eval_seq, Cmd.eval_seq]
    set s0 := (Cmd.op (Op.head H3 SCAN)).eval st with hs0
    set s1 := (Cmd.op (Op.tail SCAN SCAN)).eval s0 with hs1
    have hs0SCAN : State.get s0 SCAN = State.get st SCAN := by
      rw [hs0, Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ H3 by decide)]
    have hSCAN1 : (State.get s1 SCAN).length ≤ m0 := by
      rw [hs1, Cmd.eval_op, Op.eval, State.get_set_eq, List.length_tail, hs0SCAN]; omega
    by_cases hH3 : State.get s1 H3 = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hH3, Cmd.eval_op, Op.eval,
        State.get_set_ne _ _ _ _ (show SCAN ≠ VREG by decide)]
      exact hSCAN1
    · rw [Cmd.eval_ifBit_false _ _ _ _ hH3, Cmd.eval_seq, Cmd.eval_op, Op.eval,
        Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SCAN ≠ DN by decide),
        State.get_set_ne _ _ _ _ (show SCAN ≠ DN by decide)]
      exact hSCAN1

/-- Cost of the outer-fvar drain loop `forBnd IDX3 SCAN drainVarBody`:
`≤ 1 + m·(1560·(m+1)) + m²` where `m = |SCAN|`. -/
theorem drainVar_cost (s : State) (m : Nat) (hm : (State.get s SCAN).length = m) :
    (Cmd.forBnd IDX3 SCAN drainVarBody).cost s
      ≤ 1 + m * (drainVarBody.flatK * (m + 1)) + m * m := by
  have h := Cmd.cost_forBnd_flat_le IDX3 SCAN drainVarBody (by decide) s m
    (fun _ st => (State.get st SCAN).length ≤ m)
    (le_of_eq hm)
    (fun i st _ hM => by
      have := drainVarBody_SCAN_le (st.set IDX3 (List.replicate i 1)) m
        (by rw [State.get_set_ne _ _ _ _ (show SCAN ≠ IDX3 by decide)]; exact hM)
      exact this)
    (fun i st _ hM r hr => by
      rw [show drainVarBody.costReads = [SCAN] from rfl] at hr
      simp only [List.mem_singleton] at hr
      subst hr
      rw [State.get_set_ne _ _ _ _ (show SCAN ≠ IDX3 by decide)]
      exact hM)
  rw [hm] at h
  exact h

/-- Cost of the budget-fvar skip loop `forBnd IDX3 SC2 drainSkipBody`:
`≤ 1 + m·(1560·(m+1)) + m²` where `m = |SC2|`. -/
theorem drainSkipBody_SC2_le (st : State) (m0 : Nat)
    (h : (State.get st SC2).length ≤ m0) :
    (State.get (drainSkipBody.eval st) SC2).length ≤ m0 := by
  unfold drainSkipBody
  by_cases hDN2 : State.get st DN2 = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hDN2, nop, Cmd.eval_op, Op.eval,
      State.get_set_ne _ _ _ _ (show SC2 ≠ SKIP by decide)]
    exact h
  · rw [Cmd.eval_ifBit_false _ _ _ _ hDN2, Cmd.eval_seq, Cmd.eval_seq]
    set s0 := (Cmd.op (Op.head H3 SC2)).eval st with hs0
    set s1 := (Cmd.op (Op.tail SC2 SC2)).eval s0 with hs1
    have hs0SC2 : State.get s0 SC2 = State.get st SC2 := by
      rw [hs0, Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SC2 ≠ H3 by decide)]
    have hSC21 : (State.get s1 SC2).length ≤ m0 := by
      rw [hs1, Cmd.eval_op, Op.eval, State.get_set_eq, List.length_tail, hs0SC2]; omega
    by_cases hH3 : State.get s1 H3 = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hH3, nop, Cmd.eval_op, Op.eval,
        State.get_set_ne _ _ _ _ (show SC2 ≠ SKIP by decide)]
      exact hSC21
    · rw [Cmd.eval_ifBit_false _ _ _ _ hH3, Cmd.eval_seq, Cmd.eval_op, Op.eval,
        Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show SC2 ≠ DN2 by decide),
        State.get_set_ne _ _ _ _ (show SC2 ≠ DN2 by decide)]
      exact hSC21

theorem drainSkip_cost (s : State) (m : Nat) (hm : (State.get s SC2).length = m) :
    (Cmd.forBnd IDX3 SC2 drainSkipBody).cost s
      ≤ 1 + m * (drainSkipBody.flatK * (m + 1)) + m * m := by
  have h := Cmd.cost_forBnd_flat_le IDX3 SC2 drainSkipBody (by decide) s m
    (fun _ st => (State.get st SC2).length ≤ m)
    (le_of_eq hm)
    (fun i st _ hM => by
      have := drainSkipBody_SC2_le (st.set IDX3 (List.replicate i 1)) m
        (by rw [State.get_set_ne _ _ _ _ (show SC2 ≠ IDX3 by decide)]; exact hM)
      exact this)
    (fun i st _ hM r hr => by
      rw [show drainSkipBody.costReads = [SC2] from rfl] at hr
      simp only [List.mem_singleton] at hr
      subst hr
      rw [State.get_set_ne _ _ _ _ (show SC2 ≠ IDX3 by decide)]
      exact hM)
  rw [hm] at h
  exact h

/-- Cost of the phase-0 length loop `forBnd IDX0 SERF (appendOne B)`:
`≤ 1 + m·5 + m²` where `m = |SERF|`. -/
theorem Bloop_cost (s : State) (m : Nat) (hm : (State.get s SERF).length = m) :
    (Cmd.forBnd IDX0 SERF (Cmd.op (Op.appendOne B))).cost s
      ≤ 1 + m * (Cmd.op (Op.appendOne B)).flatK + m * m :=
  cost_constLoop_le IDX0 SERF (Cmd.op (Op.appendOne B)) (by decide) rfl s m hm

/-! ## Cost accounting — the budget-scan step (`budgetBody`) -/

/-- `ifBit` cost is bounded by the sum of both branch costs (no need to know the
guard). -/
theorem cost_ifBit_le (t : Var) (cT cE : Cmd) (s : State) :
    (Cmd.ifBit t cT cE).cost s ≤ 1 + cT.cost s + cE.cost s := by
  by_cases h : State.get s t = [1]
  · rw [Cmd.cost_ifBit_true _ _ _ _ h]; omega
  · rw [Cmd.cost_ifBit_false _ _ _ _ h]; omega

/-- The drainSkip loop preserves `BUD` (unconditionally — write-set frame). -/
theorem drainSkipLoop_BUD (s : State) :
    State.get ((Cmd.forBnd IDX3 SC2 drainSkipBody).eval s) BUD = State.get s BUD :=
  Cmd.eval_get_of_not_writes _ s BUD (by decide)

/-- generous drainSkip-loop cost bound in terms of a uniform `M ≥ |SC2|`. -/
theorem drainSkip_cost_le (s : State) (M : Nat) (h : (State.get s SC2).length ≤ M) :
    (Cmd.forBnd IDX3 SC2 drainSkipBody).cost s ≤ 1600 * (M + 1) * (M + 1) := by
  have hc := drainSkip_cost s (State.get s SC2).length rfl
  set m := (State.get s SC2).length with hm
  -- drainSkipBody.flatK = 1560
  have hk : drainSkipBody.flatK = 1560 := rfl
  rw [hk] at hc
  have : 1 + m * (1560 * (m + 1)) + m * m ≤ 1600 * (M + 1) * (M + 1) := by
    have hmM : m ≤ M := h
    nlinarith [hmM, Nat.zero_le m, Nat.zero_le M]
  omega

/-- **`budgetBodyInner` cost bound**, uniform in `M ≥ |SC2|` and `Mb ≥ |BUD|`. -/
theorem budgetBodyInner_cost (st : State) (M Mb : Nat)
    (hSC2 : (State.get st SC2).length ≤ M) (hBUD : (State.get st BUD).length ≤ Mb) :
    budgetBodyInner.cost st ≤ 1600 * (M + 1) * (M + 1) + 2 * Mb + 3 * M + 60 := by
  -- generic op-eval get helpers
  have getne : ∀ (o : Op) (s : State) (r : Var), r ≠ o.writesTo →
      State.get ((Cmd.op o).eval s) r = State.get s r := by
    intro o s r hr; rw [Cmd.eval_op]; exact Op.eval_get_ne_writesTo o s r hr
  -- prefix states
  unfold budgetBodyInner
  rw [Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq]
  set a1 := (Cmd.op (Op.head H1B SC2)).eval st with ha1
  set a2 := (Cmd.op (Op.tail SC2 SC2)).eval a1 with ha2
  set a3 := (Cmd.op (Op.head H2B SC2)).eval a2 with ha3
  set a4 := (Cmd.op (Op.tail SC2 SC2)).eval a3 with ha4
  set a5 := (Cmd.op (Op.appendOne T)).eval a4 with ha5
  -- SC2 lengths through the prefix
  have hSC2a1 : State.get a1 SC2 = State.get st SC2 := getne _ _ _ (by decide)
  have hSC2a2 : State.get a2 SC2 = (State.get a1 SC2).tail := by
    rw [ha2, Cmd.eval_op, Op.eval, State.get_set_eq]
  have hSC2a3 : State.get a3 SC2 = State.get a2 SC2 := getne _ _ _ (by decide)
  have hSC2a4 : State.get a4 SC2 = (State.get a3 SC2).tail := by
    rw [ha4, Cmd.eval_op, Op.eval, State.get_set_eq]
  have hSC2a5 : State.get a5 SC2 = State.get a4 SC2 := getne _ _ _ (by decide)
  have hla1 : (State.get a1 SC2).length ≤ M := by rw [hSC2a1]; exact hSC2
  have hla5 : (State.get a5 SC2).length ≤ M := by
    rw [hSC2a5, hSC2a4, List.length_tail, hSC2a3, hSC2a2, List.length_tail, hSC2a1]; omega
  -- BUD through the prefix
  have hBUDa5 : State.get a5 BUD = State.get st BUD := by
    rw [ha5, getne _ _ _ (by decide), ha4, getne _ _ _ (by decide), ha3,
      getne _ _ _ (by decide), ha2, getne _ _ _ (by decide), ha1, getne _ _ _ (by decide)]
  have hlBUDa5 : (State.get a5 BUD).length ≤ Mb := by rw [hBUDa5]; exact hBUD
  -- prefix op costs
  have hcost_head1 : (Cmd.op (Op.head H1B SC2)).cost st = 1 := by rw [Cmd.cost_op]; rfl
  have hcost_tail1 : (Cmd.op (Op.tail SC2 SC2)).cost a1 = (State.get a1 SC2).length + 1 := by
    rw [Cmd.cost_op]; rfl
  have hcost_head2 : (Cmd.op (Op.head H2B SC2)).cost a2 = 1 := by rw [Cmd.cost_op]; rfl
  have hcost_tail2 : (Cmd.op (Op.tail SC2 SC2)).cost a3 = (State.get a3 SC2).length + 1 := by
    rw [Cmd.cost_op]; rfl
  have hcost_app : (Cmd.op (Op.appendOne T)).cost a4 = 1 := by rw [Cmd.cost_op]; rfl
  have hla3 : (State.get a3 SC2).length ≤ M := by
    rw [hSC2a3, hSC2a2, List.length_tail, hSC2a1]; omega
  -- the outer ifBit ≤ sum of branches at a5
  have hbranch : (Cmd.ifBit H1B
      (Cmd.ifBit H2B
        (Cmd.op (Op.head H2B SC2) ;; Cmd.op (Op.tail SC2 SC2) ;;
          Cmd.ifBit H2B
            (Cmd.op (Op.clear DN2) ;; Cmd.forBnd IDX3 SC2 drainSkipBody ;;
              Cmd.op (Op.tail BUD BUD)) nop)
        (Cmd.op (Op.appendOne BUD)))
      (Cmd.ifBit H2B (Cmd.op (Op.appendOne BUD)) (Cmd.op (Op.tail BUD BUD)))).cost a5
      ≤ 1600 * (M + 1) * (M + 1) + 2 * Mb + M + 50 := by
    refine le_trans (cost_ifBit_le _ _ _ _) ?_
    -- 11x branch
    have h11x : (Cmd.ifBit H2B
        (Cmd.op (Op.head H2B SC2) ;; Cmd.op (Op.tail SC2 SC2) ;;
          Cmd.ifBit H2B
            (Cmd.op (Op.clear DN2) ;; Cmd.forBnd IDX3 SC2 drainSkipBody ;;
              Cmd.op (Op.tail BUD BUD)) nop)
        (Cmd.op (Op.appendOne BUD))).cost a5
        ≤ 1600 * (M + 1) * (M + 1) + Mb + M + 30 := by
      refine le_trans (cost_ifBit_le _ _ _ _) ?_
      -- the fvar/fneg inner block
      rw [Cmd.cost_seq, Cmd.cost_seq]
      set b1 := (Cmd.op (Op.head H2B SC2)).eval a5 with hb1
      set b2 := (Cmd.op (Op.tail SC2 SC2)).eval b1 with hb2
      have hSC2b1 : State.get b1 SC2 = State.get a5 SC2 := getne _ _ _ (by decide)
      have hlb1 : (State.get b1 SC2).length ≤ M := by rw [hSC2b1]; exact hla5
      have hSC2b2 : State.get b2 SC2 = (State.get b1 SC2).tail := by
        rw [hb2, Cmd.eval_op, Op.eval, State.get_set_eq]
      have hlb2 : (State.get b2 SC2).length ≤ M := by
        rw [hSC2b2, List.length_tail]; omega
      have hBUDb2 : State.get b2 BUD = State.get a5 BUD := by
        rw [hb2, getne _ _ _ (by decide), hb1, getne _ _ _ (by decide)]
      have hlBUDb2 : (State.get b2 BUD).length ≤ Mb := by rw [hBUDb2]; exact hlBUDa5
      have hcb1 : (Cmd.op (Op.head H2B SC2)).cost a5 = 1 := by rw [Cmd.cost_op]; rfl
      have hcb2 : (Cmd.op (Op.tail SC2 SC2)).cost b1 = (State.get b1 SC2).length + 1 := by
        rw [Cmd.cost_op]; rfl
      -- inner ifBit H2B (fvar) nop ≤ fvar + nop
      have hinner : (Cmd.ifBit H2B
          (Cmd.op (Op.clear DN2) ;; Cmd.forBnd IDX3 SC2 drainSkipBody ;;
            Cmd.op (Op.tail BUD BUD)) nop).cost b2
          ≤ 1600 * (M + 1) * (M + 1) + Mb + 20 := by
        refine le_trans (cost_ifBit_le _ _ _ _) ?_
        -- fvar block cost
        rw [Cmd.cost_seq, Cmd.cost_seq]
        set c1 := (Cmd.op (Op.clear DN2)).eval b2 with hc1
        have hSC2c1 : State.get c1 SC2 = State.get b2 SC2 := getne _ _ _ (by decide)
        have hlc1 : (State.get c1 SC2).length ≤ M := by rw [hSC2c1]; exact hlb2
        have hBUDc1 : State.get c1 BUD = State.get b2 BUD := getne _ _ _ (by decide)
        have hcc1 : (Cmd.op (Op.clear DN2)).cost b2 = 1 := by rw [Cmd.cost_op]; rfl
        -- drainSkip loop cost
        have hloop := drainSkip_cost_le c1 M hlc1
        -- tail BUD BUD after the loop
        have hBUDloop : State.get ((Cmd.forBnd IDX3 SC2 drainSkipBody).eval c1) BUD
            = State.get c1 BUD := drainSkipLoop_BUD c1
        have hct : (Cmd.op (Op.tail BUD BUD)).cost
            ((Cmd.forBnd IDX3 SC2 drainSkipBody).eval c1)
            = (State.get ((Cmd.forBnd IDX3 SC2 drainSkipBody).eval c1) BUD).length + 1 := by
          rw [Cmd.cost_op]; rfl
        have hlBUDloop : (State.get ((Cmd.forBnd IDX3 SC2 drainSkipBody).eval c1) BUD).length
            ≤ Mb := by rw [hBUDloop, hBUDc1, hBUDb2]; exact hlBUDa5
        -- nop cost
        have hnop : nop.cost b2 = 1 := by rw [nop, Cmd.cost_op]; rfl
        rw [hcc1, hct, hnop]
        omega
      have hcE1 : (Cmd.op (Op.appendOne BUD)).cost a5 = 1 := by rw [Cmd.cost_op]; rfl
      rw [hcb1, hcb2, hcE1]
      omega
    -- 0x branch
    have h0x : (Cmd.ifBit H2B (Cmd.op (Op.appendOne BUD)) (Cmd.op (Op.tail BUD BUD))).cost a5
        ≤ Mb + 10 := by
      refine le_trans (cost_ifBit_le _ _ _ _) ?_
      have hca : (Cmd.op (Op.appendOne BUD)).cost a5 = 1 := by rw [Cmd.cost_op]; rfl
      have hct : (Cmd.op (Op.tail BUD BUD)).cost a5 = (State.get a5 BUD).length + 1 := by
        rw [Cmd.cost_op]; rfl
      rw [hca, hct]
      omega
    omega
  rw [hcost_head1, hcost_tail1, hcost_head2, hcost_tail2, hcost_app]
  have hkey := hbranch
  generalize 1600 * (M + 1) * (M + 1) = Q at hkey ⊢
  omega

/-- **`budgetBody` cost bound**, uniform in `M ≥ |SC2|` and `Mb ≥ |BUD|`. -/
theorem budgetBody_cost (st : State) (M Mb : Nat)
    (hSC2 : (State.get st SC2).length ≤ M) (hBUD : (State.get st BUD).length ≤ Mb) :
    budgetBody.cost st ≤ 1600 * (M + 1) * (M + 1) + 2 * Mb + 3 * M + 70 := by
  unfold budgetBody
  rw [Cmd.cost_seq]
  set st1 := (Cmd.op (Op.nonEmpty NEB BUD)).eval st with hst1
  have hSC21 : State.get st1 SC2 = State.get st SC2 := by
    rw [hst1, Cmd.eval_op]; exact Op.eval_get_ne_writesTo _ _ _ (by decide)
  have hBUD1 : State.get st1 BUD = State.get st BUD := by
    rw [hst1, Cmd.eval_op]; exact Op.eval_get_ne_writesTo _ _ _ (by decide)
  have hcost_ne : (Cmd.op (Op.nonEmpty NEB BUD)).cost st = 1 := by rw [Cmd.cost_op]; rfl
  have hif : (Cmd.ifBit NEB budgetBodyInner nop).cost st1
      ≤ 1600 * (M + 1) * (M + 1) + 2 * Mb + 3 * M + 62 := by
    refine le_trans (cost_ifBit_le _ _ _ _) ?_
    have hi := budgetBodyInner_cost st1 M Mb (by rw [hSC21]; exact hSC2) (by rw [hBUD1]; exact hBUD)
    have hnop : nop.cost st1 = 1 := by rw [nop, Cmd.cost_op]; rfl
    rw [hnop]
    generalize 1600 * (M + 1) * (M + 1) = Q at hi ⊢
    omega
  rw [hcost_ne]
  generalize 1600 * (M + 1) * (M + 1) = Q at hif ⊢
  omega

/-! ## Cost accounting — the arity-budget scan (`subtreeScan`) -/

private theorem getne (o : Op) (s : State) (r : Var) (hr : r ≠ o.writesTo) :
    State.get ((Cmd.op o).eval s) r = State.get s r := by
  rw [Cmd.eval_op]; exact Op.eval_get_ne_writesTo o s r hr

/-- The drainSkip loop never grows `SC2`. -/
theorem drainSkipLoop_SC2_le (s : State) :
    (State.get ((Cmd.forBnd IDX3 SC2 drainSkipBody).eval s) SC2).length
      ≤ (State.get s SC2).length := by
  rw [Cmd.eval_forBnd]
  exact Cmd.foldlState_range_induct drainSkipBody IDX3 (State.get s SC2).length s
    (fun _ st => (State.get st SC2).length ≤ (State.get s SC2).length) (le_refl _)
    (fun i st _ hM => drainSkipBody_SC2_le (st.set IDX3 (List.replicate i 1))
      (State.get s SC2).length
      (by rw [State.get_set_ne _ _ _ _ (show SC2 ≠ IDX3 by decide)]; exact hM))

/-- `budgetBodyInner` never grows `SC2`. -/
theorem budgetBodyInner_SC2_le (w : State) :
    (State.get (budgetBodyInner.eval w) SC2).length ≤ (State.get w SC2).length := by
  unfold budgetBodyInner
  rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  set a1 := (Cmd.op (Op.head H1B SC2)).eval w with ha1
  set a2 := (Cmd.op (Op.tail SC2 SC2)).eval a1 with ha2
  set a3 := (Cmd.op (Op.head H2B SC2)).eval a2 with ha3
  set a4 := (Cmd.op (Op.tail SC2 SC2)).eval a3 with ha4
  set a5 := (Cmd.op (Op.appendOne T)).eval a4 with ha5
  have hla5 : (State.get a5 SC2).length ≤ (State.get w SC2).length := by
    rw [ha5, getne _ _ _ (by decide), ha4, Cmd.eval_op, Op.eval, State.get_set_eq,
      List.length_tail, ha3, getne _ _ _ (by decide), ha2, Cmd.eval_op, Op.eval,
      State.get_set_eq, List.length_tail, ha1, getne _ _ _ (by decide)]
    omega
  refine le_trans ?_ hla5
  -- branch: SC2 only shrinks or stays
  by_cases hH1B : State.get a5 H1B = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hH1B]
    by_cases hH2B : State.get a5 H2B = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hH2B, Cmd.eval_seq, Cmd.eval_seq]
      set b1 := (Cmd.op (Op.head H2B SC2)).eval a5 with hb1
      set b2 := (Cmd.op (Op.tail SC2 SC2)).eval b1 with hb2
      have hlb2 : (State.get b2 SC2).length ≤ (State.get a5 SC2).length := by
        rw [hb2, Cmd.eval_op, Op.eval, State.get_set_eq, List.length_tail, hb1,
          getne _ _ _ (by decide)]; omega
      by_cases hH2B' : State.get b2 H2B = [1]
      · rw [Cmd.eval_ifBit_true _ _ _ _ hH2B', Cmd.eval_seq, Cmd.eval_seq]
        set c1 := (Cmd.op (Op.clear DN2)).eval b2 with hc1
        have hSC2c1 : State.get c1 SC2 = State.get b2 SC2 := getne _ _ _ (by decide)
        -- tail BUD BUD doesn't touch SC2; drainSkip loop shrinks SC2
        rw [getne _ _ _ (show SC2 ≠ (Op.tail BUD BUD).writesTo by decide)]
        refine le_trans (drainSkipLoop_SC2_le c1) ?_
        rw [hSC2c1]; exact hlb2
      · rw [Cmd.eval_ifBit_false _ _ _ _ hH2B', nop, getne _ _ _ (by decide)]; exact hlb2
    · rw [Cmd.eval_ifBit_false _ _ _ _ hH2B, getne _ _ _ (by decide)]
  · rw [Cmd.eval_ifBit_false _ _ _ _ hH1B]
    by_cases hH2B : State.get a5 H2B = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hH2B, getne _ _ _ (by decide)]
    · rw [Cmd.eval_ifBit_false _ _ _ _ hH2B, getne _ _ _ (by decide)]

/-- `budgetBodyInner` grows `BUD` by at most one. -/
theorem budgetBodyInner_BUD_le (w : State) :
    (State.get (budgetBodyInner.eval w) BUD).length ≤ (State.get w BUD).length + 1 := by
  unfold budgetBodyInner
  rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  set a1 := (Cmd.op (Op.head H1B SC2)).eval w with ha1
  set a2 := (Cmd.op (Op.tail SC2 SC2)).eval a1 with ha2
  set a3 := (Cmd.op (Op.head H2B SC2)).eval a2 with ha3
  set a4 := (Cmd.op (Op.tail SC2 SC2)).eval a3 with ha4
  set a5 := (Cmd.op (Op.appendOne T)).eval a4 with ha5
  have hBUDa5 : State.get a5 BUD = State.get w BUD := by
    rw [ha5, getne _ _ _ (by decide), ha4, getne _ _ _ (by decide), ha3,
      getne _ _ _ (by decide), ha2, getne _ _ _ (by decide), ha1, getne _ _ _ (by decide)]
  rw [← hBUDa5]
  by_cases hH1B : State.get a5 H1B = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hH1B]
    by_cases hH2B : State.get a5 H2B = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hH2B, Cmd.eval_seq, Cmd.eval_seq]
      set b1 := (Cmd.op (Op.head H2B SC2)).eval a5 with hb1
      set b2 := (Cmd.op (Op.tail SC2 SC2)).eval b1 with hb2
      have hBUDb2 : State.get b2 BUD = State.get a5 BUD := by
        rw [hb2, getne _ _ _ (by decide), hb1, getne _ _ _ (by decide)]
      by_cases hH2B' : State.get b2 H2B = [1]
      · rw [Cmd.eval_ifBit_true _ _ _ _ hH2B', Cmd.eval_seq, Cmd.eval_seq]
        set c1 := (Cmd.op (Op.clear DN2)).eval b2 with hc1
        have hBUDc1 : State.get c1 BUD = State.get b2 BUD := getne _ _ _ (by decide)
        -- tail BUD BUD: shrinks; drainSkip loop preserves BUD
        rw [Cmd.eval_op, Op.eval, State.get_set_eq, drainSkipLoop_BUD, hBUDc1, hBUDb2,
          List.length_tail]
        omega
      · rw [Cmd.eval_ifBit_false _ _ _ _ hH2B', nop, getne _ _ _ (by decide), hBUDb2]; omega
    · rw [Cmd.eval_ifBit_false _ _ _ _ hH2B, Cmd.eval_op, Op.eval, State.get_set_eq,
        List.length_append, List.length_singleton]
  · rw [Cmd.eval_ifBit_false _ _ _ _ hH1B]
    by_cases hH2B : State.get a5 H2B = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hH2B, Cmd.eval_op, Op.eval, State.get_set_eq,
        List.length_append, List.length_singleton]
    · rw [Cmd.eval_ifBit_false _ _ _ _ hH2B, Cmd.eval_op, Op.eval, State.get_set_eq,
        List.length_tail]; omega

/-- `budgetBody` never grows `SC2`. -/
theorem budgetBody_SC2_le (w : State) :
    (State.get (budgetBody.eval w) SC2).length ≤ (State.get w SC2).length := by
  unfold budgetBody
  rw [Cmd.eval_seq]
  set w1 := (Cmd.op (Op.nonEmpty NEB BUD)).eval w with hw1
  have hSC2w1 : State.get w1 SC2 = State.get w SC2 := getne _ _ _ (by decide)
  by_cases h : State.get w1 NEB = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ h]
    refine le_trans (budgetBodyInner_SC2_le w1) ?_; rw [hSC2w1]
  · rw [Cmd.eval_ifBit_false _ _ _ _ h, nop, getne _ _ _ (by decide), hSC2w1]

/-- `budgetBody` grows `BUD` by at most one. -/
theorem budgetBody_BUD_le (w : State) :
    (State.get (budgetBody.eval w) BUD).length ≤ (State.get w BUD).length + 1 := by
  unfold budgetBody
  rw [Cmd.eval_seq]
  set w1 := (Cmd.op (Op.nonEmpty NEB BUD)).eval w with hw1
  have hBUDw1 : State.get w1 BUD = State.get w BUD := getne _ _ _ (by decide)
  by_cases h : State.get w1 NEB = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ h]
    refine le_trans (budgetBodyInner_BUD_le w1) ?_; rw [hBUDw1]
  · rw [Cmd.eval_ifBit_false _ _ _ _ h, nop, getne _ _ _ (by decide), hBUDw1]; omega

set_option maxHeartbeats 1000000 in
/-- **`subtreeScan` cost bound** — `O(m³)` where `m = |SCAN|` (the budget loop
runs `m` times, each `budgetBody` costs `O(m²)`). -/
theorem subtreeScan_cost (u : State) :
    subtreeScan.cost u ≤ 2000 * ((State.get u SCAN).length + 1) ^ 3 := by
  set m := (State.get u SCAN).length with hm
  unfold subtreeScan
  rw [Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq]
  set p1 := (Cmd.op (Op.copy SC2 SCAN)).eval u with hp1
  set p2 := (Cmd.op (Op.clear BUD)).eval p1 with hp2
  set p3 := (Cmd.op (Op.appendOne BUD)).eval p2 with hp3
  set P0 := (Cmd.op (Op.clear T)).eval p3 with hP0
  -- prefix costs
  have hc_copy : (Cmd.op (Op.copy SC2 SCAN)).cost u = m + 1 := by rw [Cmd.cost_op]; rfl
  have hc_cb : (Cmd.op (Op.clear BUD)).cost p1 = 1 := by rw [Cmd.cost_op]; rfl
  have hc_ab : (Cmd.op (Op.appendOne BUD)).cost p2 = 1 := by rw [Cmd.cost_op]; rfl
  have hc_ct : (Cmd.op (Op.clear T)).cost p3 = 1 := by rw [Cmd.cost_op]; rfl
  -- P0 register facts
  have hSCAN_P0 : State.get P0 SCAN = State.get u SCAN := by
    rw [hP0, getne _ _ _ (by decide), hp3, getne _ _ _ (by decide), hp2,
      getne _ _ _ (by decide), hp1, getne _ _ _ (by decide)]
  have hSC2_P0 : State.get P0 SC2 = State.get u SCAN := by
    rw [hP0, getne _ _ _ (by decide), hp3, getne _ _ _ (by decide), hp2,
      getne _ _ _ (by decide), hp1, Cmd.eval_op, Op.eval, State.get_set_eq]
  have hBUD_P0 : State.get P0 BUD = [1] := by
    rw [hP0, getne _ _ _ (by decide), hp3, Cmd.eval_op, Op.eval, State.get_set_eq, hp2,
      Cmd.eval_op, Op.eval, State.get_set_eq, List.nil_append]
  set B := 1600 * (m + 1) * (m + 1) + 2 * (m + 1) + 3 * m + 70 with hB
  have h0 : (State.get P0 SC2).length ≤ m ∧ (State.get P0 BUD).length ≤ 1 + 0 := by
    rw [hSC2_P0, hBUD_P0]; exact ⟨le_refl _, by decide⟩
  have hloop := Cmd.cost_forBnd_le IDX2 SCAN budgetBody P0 B
    (fun i st => (State.get st SC2).length ≤ m ∧ (State.get st BUD).length ≤ 1 + i)
    h0
    (fun i st _ hM => by
      obtain ⟨h1, h2⟩ := hM
      have e1 : State.get (st.set IDX2 (List.replicate i 1)) SC2 = State.get st SC2 :=
        State.get_set_ne _ _ _ _ (by decide)
      have e2 : State.get (st.set IDX2 (List.replicate i 1)) BUD = State.get st BUD :=
        State.get_set_ne _ _ _ _ (by decide)
      refine ⟨?_, ?_⟩
      · refine le_trans (budgetBody_SC2_le _) ?_; rw [e1]; exact h1
      · refine le_trans (budgetBody_BUD_le _) ?_; rw [e2]; omega)
    (fun i st hi hM => by
      obtain ⟨h1, h2⟩ := hM
      have e1 : State.get (st.set IDX2 (List.replicate i 1)) SC2 = State.get st SC2 :=
        State.get_set_ne _ _ _ _ (by decide)
      have e2 : State.get (st.set IDX2 (List.replicate i 1)) BUD = State.get st BUD :=
        State.get_set_ne _ _ _ _ (by decide)
      rw [hSCAN_P0] at hi
      exact le_trans (budgetBody_cost _ m (m + 1) (by rw [e1]; exact h1)
        (by rw [e2]; omega)) (by rw [hB]))
  rw [hSCAN_P0] at hloop
  rw [hc_copy, hc_cb, hc_ab, hc_ct]
  -- combine: prefix (m+8) + loop (1 + m*B + m²) ≤ 2000(m+1)³
  have hfin : 1 + (m + 1) + (1 + 1 + (1 + 1 + (1 + 1 + (1 + m * B + m * m))))
      ≤ 2000 * (m + 1) ^ 3 := by
    rw [hB]
    nlinarith [Nat.zero_le m, sq_nonneg m, Nat.mul_le_mul_left m (Nat.le_refl (m+1))]
  refine le_trans ?_ hfin
  gcongr

/-! ## Cost accounting — gadget cost constant + token-count (`T`) effect -/

/-- A single opaque constant dominating every gadget/prefix `flatK` used in the
`tokenBody` cost. -/
def tokFK : Nat :=
  100000 + emitTrueG.flatK + emitEquivG.flatK + emitAndG.flatK + emitOrG.flatK
    + emitNotG.flatK

theorem emitTrueG_flatK_le : emitTrueG.flatK ≤ tokFK := by unfold tokFK; omega
theorem emitEquivG_flatK_le : emitEquivG.flatK ≤ tokFK := by unfold tokFK; omega
theorem emitAndG_flatK_le : emitAndG.flatK ≤ tokFK := by unfold tokFK; omega
theorem emitOrG_flatK_le : emitOrG.flatK ≤ tokFK := by unfold tokFK; omega
theorem emitNotG_flatK_le : emitNotG.flatK ≤ tokFK := by unfold tokFK; omega

/-- `budgetBodyInner` appends exactly one to `T`. -/
theorem budgetBodyInner_T_le (w : State) :
    (State.get (budgetBodyInner.eval w) T).length ≤ (State.get w T).length + 1 := by
  unfold budgetBodyInner
  rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq,
    Cmd.eval_get_of_not_writes _ _ T (by decide)]
  -- goal: |T (appendOne T .eval a4)| ≤ |T w| + 1
  rw [Cmd.eval_op, Op.eval, State.get_set_eq, List.length_append, List.length_singleton,
    getne _ _ _ (by decide), getne _ _ _ (by decide), getne _ _ _ (by decide),
    getne _ _ _ (by decide)]

/-- `budgetBody` grows `T` by at most one. -/
theorem budgetBody_T_le (w : State) :
    (State.get (budgetBody.eval w) T).length ≤ (State.get w T).length + 1 := by
  unfold budgetBody
  rw [Cmd.eval_seq]
  set w1 := (Cmd.op (Op.nonEmpty NEB BUD)).eval w with hw1
  have hTw1 : State.get w1 T = State.get w T := getne _ _ _ (by decide)
  by_cases h : State.get w1 NEB = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ h]
    refine le_trans (budgetBodyInner_T_le w1) ?_; rw [hTw1]
  · rw [Cmd.eval_ifBit_false _ _ _ _ h, nop, getne _ _ _ (by decide), hTw1]; omega

/-- `subtreeScan` sets `T` to length `≤ |SCAN|`. -/
theorem subtreeScan_T_le (s : State) :
    (State.get (subtreeScan.eval s) T).length ≤ (State.get s SCAN).length := by
  unfold subtreeScan
  rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  set p1 := (Cmd.op (Op.copy SC2 SCAN)).eval s with hp1
  set p2 := (Cmd.op (Op.clear BUD)).eval p1 with hp2
  set p3 := (Cmd.op (Op.appendOne BUD)).eval p2 with hp3
  set P0 := (Cmd.op (Op.clear T)).eval p3 with hP0
  have hSCAN_P0 : State.get P0 SCAN = State.get s SCAN := by
    rw [hP0, getne _ _ _ (by decide), hp3, getne _ _ _ (by decide), hp2,
      getne _ _ _ (by decide), hp1, getne _ _ _ (by decide)]
  have hT_P0 : State.get P0 T = [] := by
    rw [hP0, Cmd.eval_op, Op.eval, State.get_set_eq]
  rw [Cmd.eval_forBnd]
  have h0 : (State.get P0 T).length ≤ 0 := by rw [hT_P0]; simp
  have hInv := Cmd.foldlState_range_induct budgetBody IDX2 (State.get P0 SCAN).length P0
    (fun i st => (State.get st T).length ≤ i)
    h0
    (fun i st _ hM => by
      have e : State.get (st.set IDX2 (List.replicate i 1)) T = State.get st T :=
        State.get_set_ne _ _ _ _ (by decide)
      refine le_trans (budgetBody_T_le _) ?_; rw [e]; omega)
  rw [hSCAN_P0] at hInv ⊢
  exact hInv

/-! ## Cost accounting — emit-gadget bound helper + VREG effect -/

private theorem getne' (o : Op) (s : State) (r : Var) (hr : r ≠ o.writesTo) :
    State.get ((Cmd.op o).eval s) r = State.get s r := by
  rw [Cmd.eval_op]; exact Op.eval_get_ne_writesTo o s r hr

/-- A loop-free gadget with all `costReads ≤ E+3N+1` costs `≤ g.flatK · X`
where `X = (E+N+3)³`. -/
private theorem gad_le (g : Cmd) (hlf : g.loopFree = true) (E N : Nat) (s' : State)
    (h : ∀ r ∈ g.costReads, (State.get s' r).length ≤ E + 3 * N + 1) :
    g.cost s' ≤ g.flatK * (E + N + 3) ^ 3 := by
  refine le_trans (Cmd.cost_le_flat g hlf s' (E + 3 * N + 1) h).1 ?_
  refine Nat.mul_le_mul_left _ ?_
  have hy : (3 : Nat) ≤ E + N + 3 := by omega
  have hsq : 9 ≤ (E + N + 3) * (E + N + 3) := by nlinarith [hy]
  have hcube : 3 * (E + N + 3) ≤ (E + N + 3) * (E + N + 3) * (E + N + 3) := by
    nlinarith [hy, hsq]
  calc E + 3 * N + 1 + 1 ≤ 3 * (E + N + 3) := by omega
    _ ≤ (E + N + 3) * (E + N + 3) * (E + N + 3) := hcube
    _ = (E + N + 3) ^ 3 := by ring

/-- `drainVarBody` grows `VREG` by at most one. -/
theorem drainVarBody_VREG_le (w : State) :
    (State.get (drainVarBody.eval w) VREG).length ≤ (State.get w VREG).length + 1 := by
  unfold drainVarBody
  by_cases hDN : State.get w DN = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hDN, nop, getne' _ _ _ (by decide)]; omega
  · rw [Cmd.eval_ifBit_false _ _ _ _ hDN, Cmd.eval_seq, Cmd.eval_seq]
    set s0 := (Cmd.op (Op.head H3 SCAN)).eval w with hs0
    set s1 := (Cmd.op (Op.tail SCAN SCAN)).eval s0 with hs1
    have hVREGs1 : State.get s1 VREG = State.get w VREG := by
      rw [hs1, getne' _ _ _ (by decide), hs0, getne' _ _ _ (by decide)]
    by_cases hH3 : State.get s1 H3 = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hH3, Cmd.eval_op, Op.eval, State.get_set_eq,
        List.length_append, List.length_singleton, hVREGs1]
    · rw [Cmd.eval_ifBit_false _ _ _ _ hH3, Cmd.eval_seq, Cmd.eval_op, Op.eval,
        Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ (show VREG ≠ DN by decide),
        State.get_set_ne _ _ _ _ (show VREG ≠ DN by decide), hVREGs1]; omega

/-- The `drainVar` loop leaves `VREG` no longer than `|VREG| + |SCAN|`. -/
theorem drainVar_VREG_le (s : State) :
    (State.get ((Cmd.forBnd IDX3 SCAN drainVarBody).eval s) VREG).length
      ≤ (State.get s VREG).length + (State.get s SCAN).length := by
  rw [Cmd.eval_forBnd]
  have h0 : (State.get s VREG).length ≤ (State.get s VREG).length + 0 := by omega
  have hInv := Cmd.foldlState_range_induct drainVarBody IDX3 (State.get s SCAN).length s
    (fun i st => (State.get st VREG).length ≤ (State.get s VREG).length + i) h0
    (fun i st _ hM => by
      have e : State.get (st.set IDX3 (List.replicate i 1)) VREG = State.get st VREG :=
        State.get_set_ne _ _ _ _ (by decide)
      refine le_trans (drainVarBody_VREG_le _) ?_; rw [e]; omega)
  exact hInv


/-! ## Cost accounting — `tokenBody` (the per-token cost ceiling)

The growing-buffer worry is a NON-ISSUE (HANDOFF key finding): within one
`tokenBody`, `CNFOUT` is touched only by the single emit gadget of the taken
branch, so the gadget's entry `|CNFOUT|` is `tokenBody`'s entry `|CNFOUT| ≤ E`;
`gad_le` absorbs the growth *inside* the gadget. Perf discipline (the
2026-07-15-b finding): loop frame facts precomputed as `private` one-liners
(each `by decide` over a loop write-set evaluated ONCE), the five tag branches
as separate `private` lemmas, `clear_value` on every `set` state. -/

/-- `X := (E+N+3)³` dominates the linear junk: `N ≤ X` and `27 ≤ X`. -/
private theorem X_facts (E N : Nat) : N ≤ (E + N + 3) ^ 3 ∧ 27 ≤ (E + N + 3) ^ 3 := by
  have h1 : E + N + 3 ≤ (E + N + 3) ^ 3 := Nat.le_self_pow (by omega) _
  have h27 : (3 : Nat) ^ 3 ≤ (E + N + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  omega

/-- `(N+1)² ≤ X` (funds the `drainVar` loop bound). -/
private theorem sq_le_X (E N : Nat) : (N + 1) * (N + 1) ≤ (E + N + 3) ^ 3 := by
  have h2 : (N + 1) * (N + 1) ≤ (E + N + 3) * (E + N + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : (E + N + 3) * (E + N + 3) ≤ (E + N + 3) ^ 3 := by
    have he : (E + N + 3) ^ 3 = (E + N + 3) * (E + N + 3) * (E + N + 3) := by ring
    rw [he]
    exact Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- Precomputed frame facts for `subtreeScan` (write-set `decide` done once). -/
private theorem subtreeScan_fr_CNFOUT (s : State) :
    State.get (subtreeScan.eval s) CNFOUT = State.get s CNFOUT :=
  Cmd.eval_get_of_not_writes _ s CNFOUT (by decide)

private theorem subtreeScan_fr_VA (s : State) :
    State.get (subtreeScan.eval s) VA = State.get s VA :=
  Cmd.eval_get_of_not_writes _ s VA (by decide)

private theorem subtreeScan_fr_VL (s : State) :
    State.get (subtreeScan.eval s) VL = State.get s VL :=
  Cmd.eval_get_of_not_writes _ s VL (by decide)

/-- Precomputed frame facts for the `drainVar` loop. -/
private theorem drainVarLoop_fr_CNFOUT (s : State) :
    State.get ((Cmd.forBnd IDX3 SCAN drainVarBody).eval s) CNFOUT = State.get s CNFOUT :=
  Cmd.eval_get_of_not_writes _ s CNFOUT (by decide)

private theorem drainVarLoop_fr_VA (s : State) :
    State.get ((Cmd.forBnd IDX3 SCAN drainVarBody).eval s) VA = State.get s VA :=
  Cmd.eval_get_of_not_writes _ s VA (by decide)

/-- Uniform-ceiling `drainVar` loop cost (mirror of `drainSkip_cost_le`). -/
private theorem drainVar_cost_le (s : State) (M : Nat)
    (h : (State.get s SCAN).length ≤ M) :
    (Cmd.forBnd IDX3 SCAN drainVarBody).cost s ≤ 1600 * (M + 1) * (M + 1) := by
  have hc := drainVar_cost s (State.get s SCAN).length rfl
  set m := (State.get s SCAN).length with hm
  have hk : drainVarBody.flatK = 1560 := rfl
  rw [hk] at hc
  have : 1 + m * (1560 * (m + 1)) + m * m ≤ 1600 * (M + 1) * (M + 1) := by
    have hmM : m ≤ M := h
    nlinarith [hmM, Nat.zero_le m, Nat.zero_le M]
  omega

/-- ftrue branch: one `emitTrueG` gadget. -/
private theorem brTrue_cost (st : State) (E N : Nat)
    (hCNF : (State.get st CNFOUT).length ≤ E)
    (hVA : (State.get st VA).length ≤ 2 * N) :
    emitTrueG.cost st ≤ emitTrueG.flatK * (E + N + 3) ^ 3 := by
  refine gad_le _ rfl E N st ?_
  intro r hr
  have e : emitTrueG.costReads = [CNFOUT, VA, CNFOUT, VA, CNFOUT, VA] := rfl
  rw [e] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- fand/forr branch payload: `subtreeScan ;; concat VR VL T ;; emitG`
(`emitG ∈ {emitAndG, emitOrG}` — abstracted over the gadget through its
`costReads` membership). -/
private theorem brBin_cost (emitG : Cmd) (hlf : emitG.loopFree = true)
    (hreads : ∀ r ∈ emitG.costReads, r = CNFOUT ∨ r = VA ∨ r = VL ∨ r = VR)
    (st : State) (E N : Nat)
    (hCNF : (State.get st CNFOUT).length ≤ E)
    (hSCAN : (State.get st SCAN).length ≤ N)
    (hVA : (State.get st VA).length ≤ 2 * N)
    (hVL : (State.get st VL).length ≤ 2 * N + 1) :
    (subtreeScan ;; Cmd.op (.concat VR VL T) ;; emitG).cost st
      ≤ (2010 + emitG.flatK) * (E + N + 3) ^ 3 := by
  obtain ⟨hNX, h27X⟩ := X_facts E N
  rw [Cmd.cost_seq, Cmd.cost_seq]
  -- subtreeScan cost
  have hss : subtreeScan.cost st ≤ 2000 * (E + N + 3) ^ 3 :=
    le_trans (subtreeScan_cost st)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  -- state after subtreeScan
  set s1 := subtreeScan.eval st with hs1
  have hT1 : (State.get s1 T).length ≤ N := le_trans (subtreeScan_T_le st) hSCAN
  have hVL1 : (State.get s1 VL).length ≤ 2 * N + 1 := by
    rw [hs1, subtreeScan_fr_VL]; exact hVL
  have hVA1 : (State.get s1 VA).length ≤ 2 * N := by
    rw [hs1, subtreeScan_fr_VA]; exact hVA
  have hCNF1 : (State.get s1 CNFOUT).length ≤ E := by
    rw [hs1, subtreeScan_fr_CNFOUT]; exact hCNF
  clear_value s1
  -- concat cost + state after concat
  have hcc : (Cmd.op (Op.concat VR VL T)).cost s1
      = 2 * ((State.get s1 VL).length + (State.get s1 T).length) + 1 := by
    rw [Cmd.cost_op]; rfl
  set s2 := (Cmd.op (Op.concat VR VL T)).eval s1 with hs2
  have hVR2 : (State.get s2 VR).length ≤ 3 * N + 1 := by
    rw [hs2, Cmd.eval_op]
    show (State.get (s1.set VR (State.get s1 VL ++ State.get s1 T)) VR).length ≤ _
    rw [State.get_set_eq, List.length_append]
    omega
  have hCNF2 : (State.get s2 CNFOUT).length ≤ E := by
    rw [hs2, getne' _ _ _ (by decide)]; exact hCNF1
  have hVA2 : (State.get s2 VA).length ≤ 2 * N := by
    rw [hs2, getne' _ _ _ (by decide)]; exact hVA1
  have hVL2 : (State.get s2 VL).length ≤ 2 * N + 1 := by
    rw [hs2, getne' _ _ _ (by decide)]; exact hVL1
  clear_value s2
  -- the gadget
  have hg : emitG.cost s2 ≤ emitG.flatK * (E + N + 3) ^ 3 := by
    refine gad_le _ hlf E N s2 ?_
    intro r hr
    rcases hreads r hr with rfl | rfl | rfl | rfl <;> omega
  -- combine
  rw [Nat.add_mul]
  set css := subtreeScan.cost st with hcss
  clear_value css
  set cg := emitG.cost s2 with hcg
  clear_value cg
  set P := emitG.flatK * (E + N + 3) ^ 3 with hP
  clear_value P
  set X := (E + N + 3) ^ 3 with hX
  clear_value X
  omega

/-- fvar branch payload: drain the unary payload into `VREG`, emit the equiv
gadget. -/
private theorem brVar_cost (st : State) (E N : Nat)
    (hCNF : (State.get st CNFOUT).length ≤ E)
    (hSCAN : (State.get st SCAN).length ≤ N)
    (hVA : (State.get st VA).length ≤ 2 * N) :
    (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
       Cmd.forBnd IDX3 SCAN drainVarBody ;; emitEquivG).cost st
      ≤ (1620 + emitEquivG.flatK) * (E + N + 3) ^ 3 := by
  obtain ⟨hNX, h27X⟩ := X_facts E N
  rw [Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq]
  have hc1 : (Cmd.op (Op.clear VREG)).cost st = 1 := by rw [Cmd.cost_op]; rfl
  set q1 := (Cmd.op (Op.clear VREG)).eval st with hq1
  have hVREG1 : State.get q1 VREG = [] := by
    rw [hq1, Cmd.eval_op]
    show State.get (st.set VREG []) VREG = []
    rw [State.get_set_eq]
  have hSCAN1 : (State.get q1 SCAN).length ≤ N := by
    rw [hq1, getne' _ _ _ (by decide)]; exact hSCAN
  have hCNF1 : (State.get q1 CNFOUT).length ≤ E := by
    rw [hq1, getne' _ _ _ (by decide)]; exact hCNF
  have hVA1 : (State.get q1 VA).length ≤ 2 * N := by
    rw [hq1, getne' _ _ _ (by decide)]; exact hVA
  clear_value q1
  have hc2 : (Cmd.op (Op.clear DN)).cost q1 = 1 := by rw [Cmd.cost_op]; rfl
  set q2 := (Cmd.op (Op.clear DN)).eval q1 with hq2
  have hVREG2 : State.get q2 VREG = [] := by
    rw [hq2, getne' _ _ _ (by decide)]; exact hVREG1
  have hSCAN2 : (State.get q2 SCAN).length ≤ N := by
    rw [hq2, getne' _ _ _ (by decide)]; exact hSCAN1
  have hCNF2 : (State.get q2 CNFOUT).length ≤ E := by
    rw [hq2, getne' _ _ _ (by decide)]; exact hCNF1
  have hVA2 : (State.get q2 VA).length ≤ 2 * N := by
    rw [hq2, getne' _ _ _ (by decide)]; exact hVA1
  clear_value q2
  -- the drain loop
  have hloop : (Cmd.forBnd IDX3 SCAN drainVarBody).cost q2 ≤ 1600 * (E + N + 3) ^ 3 := by
    refine le_trans (drainVar_cost_le q2 N hSCAN2) ?_
    have := sq_le_X E N
    calc 1600 * (N + 1) * (N + 1) = 1600 * ((N + 1) * (N + 1)) := by ring
      _ ≤ 1600 * (E + N + 3) ^ 3 := Nat.mul_le_mul_left _ this
  set q3 := (Cmd.forBnd IDX3 SCAN drainVarBody).eval q2 with hq3
  have hVREG3 : (State.get q3 VREG).length ≤ N := by
    rw [hq3]
    refine le_trans (drainVar_VREG_le q2) ?_
    rw [hVREG2]
    simpa using hSCAN2
  have hCNF3 : (State.get q3 CNFOUT).length ≤ E := by
    rw [hq3, drainVarLoop_fr_CNFOUT]; exact hCNF2
  have hVA3 : (State.get q3 VA).length ≤ 2 * N := by
    rw [hq3, drainVarLoop_fr_VA]; exact hVA2
  clear_value q3
  -- the gadget
  have hg : emitEquivG.cost q3 ≤ emitEquivG.flatK * (E + N + 3) ^ 3 := by
    refine gad_le _ rfl E N q3 ?_
    intro r hr
    have e : emitEquivG.costReads
        = [CNFOUT, VREG, CNFOUT, VA, CNFOUT, VA, CNFOUT, VA,
           CNFOUT, VREG, CNFOUT, VREG] := rfl
    rw [e] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      omega
  -- combine
  rw [hc1, hc2, Nat.add_mul]
  set cl := (Cmd.forBnd IDX3 SCAN drainVarBody).cost q2 with hcl
  clear_value cl
  set cg := emitEquivG.cost q3 with hcg
  clear_value cg
  set P := emitEquivG.flatK * (E + N + 3) ^ 3 with hP
  clear_value P
  set X := (E + N + 3) ^ 3 with hX
  clear_value X
  omega

/-- The 11x sub-tree: read the third tag bit, dispatch fvar/fneg. -/
private theorem brTag11_cost (st : State) (E N : Nat)
    (hCNF : (State.get st CNFOUT).length ≤ E)
    (hSCAN : (State.get st SCAN).length ≤ N)
    (hVA : (State.get st VA).length ≤ 2 * N)
    (hVL : (State.get st VL).length ≤ 2 * N + 1) :
    (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
     Cmd.ifBit H3
       (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
        Cmd.forBnd IDX3 SCAN drainVarBody ;;
        emitEquivG)
       emitNotG).cost st
      ≤ (1640 + emitEquivG.flatK + emitNotG.flatK) * (E + N + 3) ^ 3 := by
  obtain ⟨hNX, h27X⟩ := X_facts E N
  rw [Cmd.cost_seq, Cmd.cost_seq]
  have hc1 : (Cmd.op (Op.head H3 SCAN)).cost st = 1 := by rw [Cmd.cost_op]; rfl
  set s1 := (Cmd.op (Op.head H3 SCAN)).eval st with hs1
  have hSCAN1 : (State.get s1 SCAN).length ≤ N := by
    rw [hs1, getne' _ _ _ (by decide)]; exact hSCAN
  have hCNF1 : (State.get s1 CNFOUT).length ≤ E := by
    rw [hs1, getne' _ _ _ (by decide)]; exact hCNF
  have hVA1 : (State.get s1 VA).length ≤ 2 * N := by
    rw [hs1, getne' _ _ _ (by decide)]; exact hVA
  have hVL1 : (State.get s1 VL).length ≤ 2 * N + 1 := by
    rw [hs1, getne' _ _ _ (by decide)]; exact hVL
  clear_value s1
  have hc2 : (Cmd.op (Op.tail SCAN SCAN)).cost s1 = (State.get s1 SCAN).length + 1 := by
    rw [Cmd.cost_op]; rfl
  set s2 := (Cmd.op (Op.tail SCAN SCAN)).eval s1 with hs2
  have hSCAN2 : (State.get s2 SCAN).length ≤ N := by
    rw [hs2, Cmd.eval_op]
    show (State.get (s1.set SCAN (State.get s1 SCAN).tail) SCAN).length ≤ _
    rw [State.get_set_eq, List.length_tail]
    omega
  have hCNF2 : (State.get s2 CNFOUT).length ≤ E := by
    rw [hs2, getne' _ _ _ (by decide)]; exact hCNF1
  have hVA2 : (State.get s2 VA).length ≤ 2 * N := by
    rw [hs2, getne' _ _ _ (by decide)]; exact hVA1
  have hVL2 : (State.get s2 VL).length ≤ 2 * N + 1 := by
    rw [hs2, getne' _ _ _ (by decide)]; exact hVL1
  clear_value s2
  -- the dispatch: both branches
  have hvar := brVar_cost s2 E N hCNF2 hSCAN2 hVA2
  have hneg : emitNotG.cost s2 ≤ emitNotG.flatK * (E + N + 3) ^ 3 := by
    refine gad_le _ rfl E N s2 ?_
    intro r hr
    have e : emitNotG.costReads
        = [CNFOUT, VA, CNFOUT, VL, CNFOUT, VL, CNFOUT, VA, CNFOUT, VL, CNFOUT, VL] := rfl
    rw [e] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      omega
  have hif := cost_ifBit_le H3
    (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
      Cmd.forBnd IDX3 SCAN drainVarBody ;; emitEquivG) emitNotG s2
  -- combine
  rw [hc1, hc2, Nat.add_mul, Nat.add_mul]
  rw [Nat.add_mul] at hvar
  set cv := (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
      Cmd.forBnd IDX3 SCAN drainVarBody ;; emitEquivG).cost s2 with hcv
  clear_value cv
  set cn := emitNotG.cost s2 with hcn
  clear_value cn
  set cif := (Cmd.ifBit H3
      (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
        Cmd.forBnd IDX3 SCAN drainVarBody ;; emitEquivG) emitNotG).cost s2 with hcif
  clear_value cif
  set PE := emitEquivG.flatK * (E + N + 3) ^ 3 with hPE
  clear_value PE
  set PN := emitNotG.flatK * (E + N + 3) ^ 3 with hPN
  clear_value PN
  set X := (E + N + 3) ^ 3 with hX
  clear_value X
  omega

/-- The whole tag-dispatch tree: `ifBit H1 (ifBit H2 (11x) (10)) (ifBit H2 (01) (00))`,
bounded by the SUM of all five branch payloads (`cost_ifBit_le` needs no guard
knowledge). -/
private theorem tree_cost (st : State) (E N : Nat)
    (hCNF : (State.get st CNFOUT).length ≤ E)
    (hSCAN : (State.get st SCAN).length ≤ N)
    (hVA : (State.get st VA).length ≤ 2 * N)
    (hVL : (State.get st VL).length ≤ 2 * N + 1) :
    (Cmd.ifBit H1
       (Cmd.ifBit H2
          (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
           Cmd.ifBit H3
             (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
              Cmd.forBnd IDX3 SCAN drainVarBody ;;
              emitEquivG)
             emitNotG)
          (subtreeScan ;;
           Cmd.op (.concat VR VL T) ;;
           emitOrG))
       (Cmd.ifBit H2
          (subtreeScan ;;
           Cmd.op (.concat VR VL T) ;;
           emitAndG)
          emitTrueG)).cost st
      ≤ (5700 + emitTrueG.flatK + emitEquivG.flatK + emitAndG.flatK
          + emitOrG.flatK + emitNotG.flatK) * (E + N + 3) ^ 3 := by
  obtain ⟨hNX, h27X⟩ := X_facts E N
  have h11 := brTag11_cost st E N hCNF hSCAN hVA hVL
  have hor := brBin_cost emitOrG rfl
    (by
      intro r hr
      have e : emitOrG.costReads
          = [CNFOUT, VA, CNFOUT, VL, CNFOUT, VR, CNFOUT, VL, CNFOUT, VA, CNFOUT, VA,
             CNFOUT, VR, CNFOUT, VA, CNFOUT, VA] := rfl
      rw [e] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    st E N hCNF hSCAN hVA hVL
  have hand := brBin_cost emitAndG rfl
    (by
      intro r hr
      have e : emitAndG.costReads
          = [CNFOUT, VA, CNFOUT, VL, CNFOUT, VL, CNFOUT, VA, CNFOUT, VR, CNFOUT, VR,
             CNFOUT, VL, CNFOUT, VR, CNFOUT, VA] := rfl
      rw [e] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    st E N hCNF hSCAN hVA hVL
  have htrue := brTrue_cost st E N hCNF hVA
  -- fold the two inner ifBits then the outer one
  have hifA := cost_ifBit_le H2
    (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
     Cmd.ifBit H3
       (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
        Cmd.forBnd IDX3 SCAN drainVarBody ;;
        emitEquivG)
       emitNotG)
    (subtreeScan ;; Cmd.op (.concat VR VL T) ;; emitOrG) st
  have hifB := cost_ifBit_le H2
    (subtreeScan ;; Cmd.op (.concat VR VL T) ;; emitAndG) emitTrueG st
  have hifTop := cost_ifBit_le H1
    (Cmd.ifBit H2
       (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
        Cmd.ifBit H3
          (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
           Cmd.forBnd IDX3 SCAN drainVarBody ;;
           emitEquivG)
          emitNotG)
       (subtreeScan ;; Cmd.op (.concat VR VL T) ;; emitOrG))
    (Cmd.ifBit H2
       (subtreeScan ;; Cmd.op (.concat VR VL T) ;; emitAndG) emitTrueG) st
  -- distribute the coefficient sums and close linearly
  rw [Nat.add_mul, Nat.add_mul] at h11
  rw [Nat.add_mul] at hor
  rw [Nat.add_mul] at hand
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  set c11 := (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
     Cmd.ifBit H3
       (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
        Cmd.forBnd IDX3 SCAN drainVarBody ;;
        emitEquivG)
       emitNotG).cost st with hc11
  clear_value c11
  set cor := (subtreeScan ;; Cmd.op (.concat VR VL T) ;; emitOrG).cost st with hcor
  clear_value cor
  set cand := (subtreeScan ;; Cmd.op (.concat VR VL T) ;; emitAndG).cost st with hcand
  clear_value cand
  set ctrue := emitTrueG.cost st with hctrue
  clear_value ctrue
  set cifA := (Cmd.ifBit H2
       (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
        Cmd.ifBit H3
          (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
           Cmd.forBnd IDX3 SCAN drainVarBody ;;
           emitEquivG)
          emitNotG)
       (subtreeScan ;; Cmd.op (.concat VR VL T) ;; emitOrG)).cost st with hcifA
  clear_value cifA
  set cifB := (Cmd.ifBit H2
       (subtreeScan ;; Cmd.op (.concat VR VL T) ;; emitAndG) emitTrueG).cost st with hcifB
  clear_value cifB
  set PT := emitTrueG.flatK * (E + N + 3) ^ 3 with hPT
  clear_value PT
  set PE := emitEquivG.flatK * (E + N + 3) ^ 3 with hPE
  clear_value PE
  set PA := emitAndG.flatK * (E + N + 3) ^ 3 with hPA
  clear_value PA
  set PO := emitOrG.flatK * (E + N + 3) ^ 3 with hPO
  clear_value PO
  set PN := emitNotG.flatK * (E + N + 3) ^ 3 with hPN
  clear_value PN
  set X := (E + N + 3) ^ 3 with hX
  clear_value X
  omega

set_option maxHeartbeats 800000 in
/-- **The per-token cost ceiling** (HANDOFF "NEXT TOP-DOWN" step 3): with the
emit buffer `≤ E` and the working registers `≤ N` at entry, one `tokenBody`
iteration costs `≤ tokFK·(E+N+3)³`. -/
theorem tokenBody_cost (s : State) (E N : Nat)
    (hCNF : (State.get s CNFOUT).length ≤ E)
    (hSCAN : (State.get s SCAN).length ≤ N)
    (hB : (State.get s B).length ≤ N)
    (hK : (State.get s K).length ≤ N) :
    tokenBody.cost s ≤ tokFK * (E + N + 3) ^ 3 := by
  obtain ⟨hNX, h27X⟩ := X_facts E N
  unfold tokenBody
  rw [Cmd.cost_seq]
  have hc0 : (Cmd.op (Op.nonEmpty NE SCAN)).cost s = 1 := by rw [Cmd.cost_op]; rfl
  set s1 := (Cmd.op (Op.nonEmpty NE SCAN)).eval s with hs1
  have hCNF1 : (State.get s1 CNFOUT).length ≤ E := by
    rw [hs1, getne' _ _ _ (by decide)]; exact hCNF
  have hSCAN1 : (State.get s1 SCAN).length ≤ N := by
    rw [hs1, getne' _ _ _ (by decide)]; exact hSCAN
  have hB1 : (State.get s1 B).length ≤ N := by
    rw [hs1, getne' _ _ _ (by decide)]; exact hB
  have hK1 : (State.get s1 K).length ≤ N := by
    rw [hs1, getne' _ _ _ (by decide)]; exact hK
  clear_value s1
  -- the guarded big body: peel the straight-line prefix
  have hbig : (Cmd.op (.concat VA B K) ;;
      Cmd.op (.copy VL VA) ;; Cmd.op (.appendOne VL) ;;
      Cmd.op (.head H1 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
      Cmd.op (.head H2 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
      Cmd.ifBit H1
        (Cmd.ifBit H2
           (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
            Cmd.ifBit H3
              (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
               Cmd.forBnd IDX3 SCAN drainVarBody ;;
               emitEquivG)
              emitNotG)
           (subtreeScan ;;
            Cmd.op (.concat VR VL T) ;;
            emitOrG))
        (Cmd.ifBit H2
           (subtreeScan ;;
            Cmd.op (.concat VR VL T) ;;
            emitAndG)
           emitTrueG) ;;
      Cmd.op (.appendOne K)).cost s1
      ≤ (5750 + emitTrueG.flatK + emitEquivG.flatK + emitAndG.flatK
          + emitOrG.flatK + emitNotG.flatK) * (E + N + 3) ^ 3 + 9 * N + 20 := by
    rw [Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq,
      Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq]
    -- a1: concat VA B K
    have hca1 : (Cmd.op (Op.concat VA B K)).cost s1
        = 2 * ((State.get s1 B).length + (State.get s1 K).length) + 1 := by
      rw [Cmd.cost_op]; rfl
    set a1 := (Cmd.op (Op.concat VA B K)).eval s1 with ha1
    have hVAa1 : (State.get a1 VA).length ≤ 2 * N := by
      rw [ha1, Cmd.eval_op]
      show (State.get (s1.set VA (State.get s1 B ++ State.get s1 K)) VA).length ≤ _
      rw [State.get_set_eq, List.length_append]
      omega
    have hCNFa1 : (State.get a1 CNFOUT).length ≤ E := by
      rw [ha1, getne' _ _ _ (by decide)]; exact hCNF1
    have hSCANa1 : (State.get a1 SCAN).length ≤ N := by
      rw [ha1, getne' _ _ _ (by decide)]; exact hSCAN1
    clear_value a1
    -- a2: copy VL VA
    have hca2 : (Cmd.op (Op.copy VL VA)).cost a1 = (State.get a1 VA).length + 1 := by
      rw [Cmd.cost_op]; rfl
    set a2 := (Cmd.op (Op.copy VL VA)).eval a1 with ha2
    have hVLa2 : (State.get a2 VL).length ≤ 2 * N := by
      rw [ha2, Cmd.eval_op]
      show (State.get (a1.set VL (State.get a1 VA)) VL).length ≤ _
      rw [State.get_set_eq]
      exact hVAa1
    have hVAa2 : (State.get a2 VA).length ≤ 2 * N := by
      rw [ha2, getne' _ _ _ (by decide)]; exact hVAa1
    have hCNFa2 : (State.get a2 CNFOUT).length ≤ E := by
      rw [ha2, getne' _ _ _ (by decide)]; exact hCNFa1
    have hSCANa2 : (State.get a2 SCAN).length ≤ N := by
      rw [ha2, getne' _ _ _ (by decide)]; exact hSCANa1
    clear_value a2
    -- a3: appendOne VL
    have hca3 : (Cmd.op (Op.appendOne VL)).cost a2 = 1 := by rw [Cmd.cost_op]; rfl
    set a3 := (Cmd.op (Op.appendOne VL)).eval a2 with ha3
    have hVLa3 : (State.get a3 VL).length ≤ 2 * N + 1 := by
      rw [ha3, Cmd.eval_op]
      show (State.get (a2.set VL (State.get a2 VL ++ [1])) VL).length ≤ _
      rw [State.get_set_eq, List.length_append]
      simp only [List.length_singleton]
      omega
    have hVAa3 : (State.get a3 VA).length ≤ 2 * N := by
      rw [ha3, getne' _ _ _ (by decide)]; exact hVAa2
    have hCNFa3 : (State.get a3 CNFOUT).length ≤ E := by
      rw [ha3, getne' _ _ _ (by decide)]; exact hCNFa2
    have hSCANa3 : (State.get a3 SCAN).length ≤ N := by
      rw [ha3, getne' _ _ _ (by decide)]; exact hSCANa2
    clear_value a3
    -- a4: head H1 SCAN
    have hca4 : (Cmd.op (Op.head H1 SCAN)).cost a3 = 1 := by rw [Cmd.cost_op]; rfl
    set a4 := (Cmd.op (Op.head H1 SCAN)).eval a3 with ha4
    have hVLa4 : (State.get a4 VL).length ≤ 2 * N + 1 := by
      rw [ha4, getne' _ _ _ (by decide)]; exact hVLa3
    have hVAa4 : (State.get a4 VA).length ≤ 2 * N := by
      rw [ha4, getne' _ _ _ (by decide)]; exact hVAa3
    have hCNFa4 : (State.get a4 CNFOUT).length ≤ E := by
      rw [ha4, getne' _ _ _ (by decide)]; exact hCNFa3
    have hSCANa4 : (State.get a4 SCAN).length ≤ N := by
      rw [ha4, getne' _ _ _ (by decide)]; exact hSCANa3
    clear_value a4
    -- a5: tail SCAN SCAN
    have hca5 : (Cmd.op (Op.tail SCAN SCAN)).cost a4 = (State.get a4 SCAN).length + 1 := by
      rw [Cmd.cost_op]; rfl
    set a5 := (Cmd.op (Op.tail SCAN SCAN)).eval a4 with ha5
    have hSCANa5 : (State.get a5 SCAN).length ≤ N := by
      rw [ha5, Cmd.eval_op]
      show (State.get (a4.set SCAN (State.get a4 SCAN).tail) SCAN).length ≤ _
      rw [State.get_set_eq, List.length_tail]
      omega
    have hVLa5 : (State.get a5 VL).length ≤ 2 * N + 1 := by
      rw [ha5, getne' _ _ _ (by decide)]; exact hVLa4
    have hVAa5 : (State.get a5 VA).length ≤ 2 * N := by
      rw [ha5, getne' _ _ _ (by decide)]; exact hVAa4
    have hCNFa5 : (State.get a5 CNFOUT).length ≤ E := by
      rw [ha5, getne' _ _ _ (by decide)]; exact hCNFa4
    clear_value a5
    -- a6: head H2 SCAN
    have hca6 : (Cmd.op (Op.head H2 SCAN)).cost a5 = 1 := by rw [Cmd.cost_op]; rfl
    set a6 := (Cmd.op (Op.head H2 SCAN)).eval a5 with ha6
    have hSCANa6 : (State.get a6 SCAN).length ≤ N := by
      rw [ha6, getne' _ _ _ (by decide)]; exact hSCANa5
    have hVLa6 : (State.get a6 VL).length ≤ 2 * N + 1 := by
      rw [ha6, getne' _ _ _ (by decide)]; exact hVLa5
    have hVAa6 : (State.get a6 VA).length ≤ 2 * N := by
      rw [ha6, getne' _ _ _ (by decide)]; exact hVAa5
    have hCNFa6 : (State.get a6 CNFOUT).length ≤ E := by
      rw [ha6, getne' _ _ _ (by decide)]; exact hCNFa5
    clear_value a6
    -- a7: tail SCAN SCAN
    have hca7 : (Cmd.op (Op.tail SCAN SCAN)).cost a6 = (State.get a6 SCAN).length + 1 := by
      rw [Cmd.cost_op]; rfl
    set a7 := (Cmd.op (Op.tail SCAN SCAN)).eval a6 with ha7
    have hSCANa7 : (State.get a7 SCAN).length ≤ N := by
      rw [ha7, Cmd.eval_op]
      show (State.get (a6.set SCAN (State.get a6 SCAN).tail) SCAN).length ≤ _
      rw [State.get_set_eq, List.length_tail]
      omega
    have hVLa7 : (State.get a7 VL).length ≤ 2 * N + 1 := by
      rw [ha7, getne' _ _ _ (by decide)]; exact hVLa6
    have hVAa7 : (State.get a7 VA).length ≤ 2 * N := by
      rw [ha7, getne' _ _ _ (by decide)]; exact hVAa6
    have hCNFa7 : (State.get a7 CNFOUT).length ≤ E := by
      rw [ha7, getne' _ _ _ (by decide)]; exact hCNFa6
    clear_value a7
    -- the tree ;; appendOne K (already peeled by the seq chain above)
    have htree := tree_cost a7 E N hCNFa7 hSCANa7 hVAa7 hVLa7
    have hck : (Cmd.op (Op.appendOne K)).cost
        ((Cmd.ifBit H1
          (Cmd.ifBit H2
             (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
              Cmd.ifBit H3
                (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
                 Cmd.forBnd IDX3 SCAN drainVarBody ;;
                 emitEquivG)
                emitNotG)
             (subtreeScan ;;
              Cmd.op (.concat VR VL T) ;;
              emitOrG))
          (Cmd.ifBit H2
             (subtreeScan ;;
              Cmd.op (.concat VR VL T) ;;
              emitAndG)
             emitTrueG)).eval a7) = 1 := by
      rw [Cmd.cost_op]; rfl
    rw [hca1, hca2, hca3, hca4, hca5, hca6, hca7, hck]
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul] at htree ⊢
    set ct := (Cmd.ifBit H1
          (Cmd.ifBit H2
             (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
              Cmd.ifBit H3
                (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
                 Cmd.forBnd IDX3 SCAN drainVarBody ;;
                 emitEquivG)
                emitNotG)
             (subtreeScan ;;
              Cmd.op (.concat VR VL T) ;;
              emitOrG))
          (Cmd.ifBit H2
             (subtreeScan ;;
              Cmd.op (.concat VR VL T) ;;
              emitAndG)
             emitTrueG)).cost a7 with hct
    clear_value ct
    set PT := emitTrueG.flatK * (E + N + 3) ^ 3 with hPT
    clear_value PT
    set PE := emitEquivG.flatK * (E + N + 3) ^ 3 with hPE
    clear_value PE
    set PA := emitAndG.flatK * (E + N + 3) ^ 3 with hPA
    clear_value PA
    set PO := emitOrG.flatK * (E + N + 3) ^ 3 with hPO
    clear_value PO
    set PN := emitNotG.flatK * (E + N + 3) ^ 3 with hPN
    clear_value PN
    set X := (E + N + 3) ^ 3 with hX
    clear_value X
    omega
  -- assemble: guard + ifBit + nop
  have hif := cost_ifBit_le NE
    (Cmd.op (.concat VA B K) ;;
      Cmd.op (.copy VL VA) ;; Cmd.op (.appendOne VL) ;;
      Cmd.op (.head H1 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
      Cmd.op (.head H2 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
      Cmd.ifBit H1
        (Cmd.ifBit H2
           (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
            Cmd.ifBit H3
              (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
               Cmd.forBnd IDX3 SCAN drainVarBody ;;
               emitEquivG)
              emitNotG)
           (subtreeScan ;;
            Cmd.op (.concat VR VL T) ;;
            emitOrG))
        (Cmd.ifBit H2
           (subtreeScan ;;
            Cmd.op (.concat VR VL T) ;;
            emitAndG)
           emitTrueG) ;;
      Cmd.op (.appendOne K)) nop s1
  have hnop : nop.cost s1 = 1 := by rw [nop, Cmd.cost_op]; rfl
  rw [hc0]
  have htokeq : tokFK = 100000 + emitTrueG.flatK + emitEquivG.flatK + emitAndG.flatK
      + emitOrG.flatK + emitNotG.flatK := rfl
  rw [htokeq, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul] at hbig
  rw [hnop] at hif
  set cbig := (Cmd.op (.concat VA B K) ;;
      Cmd.op (.copy VL VA) ;; Cmd.op (.appendOne VL) ;;
      Cmd.op (.head H1 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
      Cmd.op (.head H2 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
      Cmd.ifBit H1
        (Cmd.ifBit H2
           (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
            Cmd.ifBit H3
              (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
               Cmd.forBnd IDX3 SCAN drainVarBody ;;
               emitEquivG)
              emitNotG)
           (subtreeScan ;;
            Cmd.op (.concat VR VL T) ;;
            emitOrG))
        (Cmd.ifBit H2
           (subtreeScan ;;
            Cmd.op (.concat VR VL T) ;;
            emitAndG)
           emitTrueG) ;;
      Cmd.op (.appendOne K)).cost s1 with hcbig
  clear_value cbig
  set cif := (Cmd.ifBit NE
      (Cmd.op (.concat VA B K) ;;
        Cmd.op (.copy VL VA) ;; Cmd.op (.appendOne VL) ;;
        Cmd.op (.head H1 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
        Cmd.op (.head H2 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
        Cmd.ifBit H1
          (Cmd.ifBit H2
             (Cmd.op (.head H3 SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
              Cmd.ifBit H3
                (Cmd.op (.clear VREG) ;; Cmd.op (.clear DN) ;;
                 Cmd.forBnd IDX3 SCAN drainVarBody ;;
                 emitEquivG)
                emitNotG)
             (subtreeScan ;;
              Cmd.op (.concat VR VL T) ;;
              emitOrG))
          (Cmd.ifBit H2
             (subtreeScan ;;
              Cmd.op (.concat VR VL T) ;;
              emitAndG)
             emitTrueG) ;;
        Cmd.op (.appendOne K)) nop).cost s1 with hcif
  clear_value cif
  set PT := emitTrueG.flatK * (E + N + 3) ^ 3 with hPT
  clear_value PT
  set PE := emitEquivG.flatK * (E + N + 3) ^ 3 with hPE
  clear_value PE
  set PA := emitAndG.flatK * (E + N + 3) ^ 3 with hPA
  clear_value PA
  set PO := emitOrG.flatK * (E + N + 3) ^ 3 with hPO
  clear_value PO
  set PN := emitNotG.flatK * (E + N + 3) ^ 3 with hPN
  clear_value PN
  set X := (E + N + 3) ^ 3 with hX
  clear_value X
  omega


/-! ## Cost accounting — the outer token loop (`outerLoop_cost`)

`Cmd.cost_forBnd_le` over `outerLoop_run`'s semantic invariant (augmented with
a `|SCAN| ≤ L` length clause): the invariant pins `CNFOUT = C0 ++ encodeCnf
done` with `done` a *prefix* of the full clause list (the split equation), so
the emit buffer stays `≤ |C0| + |encodeCnf (fsatToSat f)| ≤ E` at every
iteration — the uniform ceiling `tokenBody_cost` needs. -/

/-- One token step never grows the stream. -/
private theorem tokRem_length_le (g : formula) (rest : List Nat) :
    (tokRem g rest).length ≤ (serF g ++ rest).length := by
  cases g <;> simp [tokRem, BinaryCCFSATFree.serF] <;> omega

set_option maxHeartbeats 1000000 in
/-- **The outer-loop cost bound**: with the loop entry laid out as in
`outerLoop_run` and `E` dominating `|C0| + |encodeCnf (fsatToSat f)|`, the
whole `forBnd IDX1 SERF tokenBody` costs `≤ 1 + L·(tokFK·(E+L+3)³) + L²`. -/
theorem outerLoop_cost (u : State) (f : formula) (C0 T0 : List Nat) (E : Nat)
    (hSCAN : State.get u SCAN = serF f)
    (hK : State.get u K = [])
    (hCNF : State.get u CNFOUT = C0)
    (hTAL : State.get u TALLY = T0)
    (hB : State.get u B = List.replicate (serF f).length 1)
    (hbound : State.get u SERF = serF f)
    (hE : C0.length + (encodeCnf (fsatToSat f)).length ≤ E) :
    (Cmd.forBnd IDX1 SERF tokenBody).cost u
      ≤ 1 + (serF f).length * (tokFK * (E + (serF f).length + 3) ^ 3)
        + (serF f).length * (serF f).length := by
  -- idle behaviour on an exhausted stream (as in `outerLoop_run`)
  have hidle : ∀ t : State, State.get t SCAN = [] →
      tokenBody.eval t = (t.set NE [0]).set SKIP [] := by
    intro t ht
    unfold tokenBody
    have e0 : (Cmd.op (Op.nonEmpty NE SCAN)).eval t = t.set NE [0] := by
      rw [Cmd.eval_op, Op.eval, ht]; rfl
    rw [Cmd.eval_seq, e0, Cmd.eval_ifBit_false _ _ _ _ (by rw [State.get_set_eq]; decide),
      nop, Cmd.eval_op, Op.eval]
  set L := (serF f).length with hL
  have hfsL : formula_size f ≤ L := by rw [hL]; exact BinaryCCFSATFree.formula_size_le_serF f
  -- the scan tail of `fsatToSat f` (the top-clause split, as in `buildSAT_run`)
  have htop : tseytinTrue L ++ scanClauses L (L + 1) 0 (serF f) = fsatToSat f := by
    rw [← mScan_eq_fsatToSat]; rfl
  have hscanlen : (encodeCnf (scanClauses L (L + 1) 0 (serF f))).length
      ≤ (encodeCnf (fsatToSat f)).length := by
    rw [← htop, encodeCnf_append, List.length_append]; omega
  set M : Nat → State → Prop := fun i st =>
    (State.get st SCAN).length ≤ L
    ∧ (∃ (hs : List formula) (done : cnf),
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
    refine ⟨by rw [hSCAN], [f], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    obtain ⟨hlen, hs, done, hSC, hKi, hCN, hTL, hBi, hcons, hscan⟩ := hM
    set w := st.set IDX1 (List.replicate i 1) with hw
    have hwSC : State.get w SCAN = (hs.map serF).flatten := by
      rw [hw, State.get_set_ne _ _ _ _ (show SCAN ≠ IDX1 by decide), hSC]
    have hwlen : (State.get w SCAN).length ≤ L := by
      rw [hw, State.get_set_ne _ _ _ _ (show SCAN ≠ IDX1 by decide)]; exact hlen
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
        refine ⟨?_, [], done, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (show SCAN ≠ SKIP by decide),
            State.get_set_ne _ _ _ _ (show SCAN ≠ NE by decide)]
          exact hwlen
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
        have hwSC' : State.get w SCAN = serF g₀ ++ (hs'.map serF).flatten := by
          rw [hwSC]; simp [List.map_cons, List.flatten_cons]
        obtain ⟨hbCN, hbTL, hbSC, hbK, hbB, _⟩ :=
          tokenBody_run w g₀ L (min i (formula_size f)) ((hs'.map serF).flatten) hwSC' hwB hwK
        refine ⟨?_, tokForest g₀ hs', done ++ tokHead L (min i (formula_size f)) g₀,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hbSC]
          refine le_trans (tokRem_length_le g₀ ((hs'.map serF).flatten)) ?_
          rw [← hwSC']
          exact hwlen
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
  -- the per-iteration cost ceiling
  have hCost : ∀ i st, i < (State.get u SERF).length → M i st →
      tokenBody.cost (st.set IDX1 (List.replicate i 1)) ≤ tokFK * (E + L + 3) ^ 3 := by
    intro i st _ hM
    obtain ⟨hlen, hs, done, hSC, hKi, hCN, hTL, hBi, hcons, hscan⟩ := hM
    set w := st.set IDX1 (List.replicate i 1) with hw
    have hwCN : (State.get w CNFOUT).length ≤ E := by
      rw [hw, State.get_set_ne _ _ _ _ (show CNFOUT ≠ IDX1 by decide), hCN,
        List.length_append]
      have hdone : (encodeCnf done).length
          ≤ (encodeCnf (scanClauses L (L + 1) 0 (serF f))).length := by
        rw [hscan, encodeCnf_append, List.length_append]; omega
      omega
    have hwSC : (State.get w SCAN).length ≤ L := by
      rw [hw, State.get_set_ne _ _ _ _ (show SCAN ≠ IDX1 by decide)]; exact hlen
    have hwB : (State.get w B).length ≤ L := by
      rw [hw, State.get_set_ne _ _ _ _ (show B ≠ IDX1 by decide), hBi,
        List.length_replicate]
    have hwK : (State.get w K).length ≤ L := by
      rw [hw, State.get_set_ne _ _ _ _ (show K ≠ IDX1 by decide), hKi,
        List.length_replicate]
      omega
    exact tokenBody_cost w E L hwCN hwSC hwB hwK
  have h := Cmd.cost_forBnd_le IDX1 SERF tokenBody u (tokFK * (E + L + 3) ^ 3) M h0 hstep hCost
  rw [hbound] at h
  rw [← hL] at h
  exact h


/-! ## Cost accounting — the assembly (`buildSAT_cost_le`) and the witness's
`cost_bound` (`satBound`) -/

/-- The witness's master size parameter: dominates the emit-buffer ceiling
(`|C0| + |encodeCnf (fsatToSat f)| ≤ 1600·(n+1)²`) plus the stream length
(`L ≤ 4n`), so `E + L + 3 ≤ satOmega n`. -/
def satOmega (n : Nat) : Nat := 1700 * (n + 1) ^ 2

/-- The symbolic cost coefficient (never evaluate the `flatK` numerals). -/
def satK : Nat := tokFK + 12 * (emitLit true VA).flatK + 100

/-- The witness's `cost_bound`: `satK · (satOmega n + 1)⁴` — `O(n⁸)`. -/
def satBound (n : Nat) : Nat :=
  satK * ((satOmega n + 1) * ((satOmega n + 1) * ((satOmega n + 1) * (satOmega n + 1))))

theorem satBound_poly : inOPoly satBound := by
  refine ⟨8, ⟨satK * 6801 ^ 4, 1, ?_⟩⟩
  intro n hn
  have h1 : satOmega n + 1 ≤ 6801 * n ^ 2 := by
    unfold satOmega
    have h2 : (n + 1) ^ 2 ≤ (2 * n) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
    have h4 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  calc satBound n
      ≤ satK * ((6801 * n ^ 2) * ((6801 * n ^ 2) * ((6801 * n ^ 2) * (6801 * n ^ 2)))) := by
        unfold satBound
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 (Nat.mul_le_mul h1
          (Nat.mul_le_mul h1 h1)))
    _ = satK * 6801 ^ 4 * n ^ 8 := by ring

theorem satBound_mono : monotonic satBound := by
  intro a b h
  unfold satBound
  have hm : satOmega a + 1 ≤ satOmega b + 1 := by
    unfold satOmega
    have := Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2
    omega
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hm (Nat.mul_le_mul hm
    (Nat.mul_le_mul hm hm)))

/-- The output size is dominated by the cost bound (`output_size_le`). -/
theorem satBound_output (f : formula) :
    encodable.size (fsatToSat f) ≤ satBound (encodable.size f) := by
  set n := encodable.size f with hn
  have h1 := fsatToSat_size_le f
  rw [← hn] at h1
  have h2 : 300 * (n + 1) ^ 2 ≤ satOmega n + 1 := by unfold satOmega; omega
  have hK : 1 ≤ satK := by
    have : (100000 : Nat) ≤ tokFK := by unfold tokFK; omega
    unfold satK; omega
  have h3 : satOmega n + 1 ≤ satBound n := by
    unfold satBound
    calc satOmega n + 1
        = 1 * ((satOmega n + 1) * (1 * (1 * 1))) := by ring
      _ ≤ satK * ((satOmega n + 1)
            * ((satOmega n + 1) * ((satOmega n + 1) * (satOmega n + 1)))) := by
          gcongr <;> omega
  omega

/-- `|encodeLit (pol, v)| = v + 3`. -/
private theorem encodeLit_length (pol : Bool) (v : Nat) :
    (encodeLit (pol, v)).length = v + 3 := by
  simp [EvalCnfCmd.encodeLit]

set_option maxHeartbeats 1000000 in
/-- **The witness's `cost_le`**: `buildSAT` runs within `satBound` on every
input (prefix ops exactly, the top-clause emitters by the flat bound, the
outer loop by `outerLoop_cost` at `E := 1600·(n+1)²`). -/
theorem buildSAT_cost_le (f : formula) :
    buildSAT.cost (encodeIn f) ≤ satBound (encodable.size f) := by
  set n := encodable.size f with hn
  set L := (serF f).length with hL
  have hLn : L ≤ 4 * n := by
    rw [hL, hn]; exact BinaryCCFSATFree.serF_length_le_size f
  -- ===== the straight-line prefix state chain (mirror `buildSAT_run`) =====
  have hu0SERF : State.get (encodeIn f) SERF = serF f := rfl
  have hu0B : State.get (encodeIn f) B = [] := rfl
  set c_a := (encodeIn f).set B [] with hca
  have e_clearB : (Cmd.op (Op.clear B)).eval (encodeIn f) = c_a := by
    rw [Cmd.eval_op, Op.eval, hca]
  have hcaB : State.get c_a B = [] := by rw [hca, State.get_set_eq]
  have hcaSERF : State.get c_a SERF = serF f := by
    rw [hca, State.get_set_ne _ _ _ _ (show SERF ≠ B by decide), hu0SERF]
  obtain ⟨hcBB, hcBfr⟩ := Bloop_run c_a hcaB
  set cB := (Cmd.forBnd IDX0 SERF (Cmd.op (Op.appendOne B))).eval c_a with hcB
  rw [hcaSERF] at hcBB
  have hcBSERF : State.get cB SERF = serF f := by
    rw [hcBfr SERF (by decide) (by decide), hcaSERF]
  set c_scan := cB.set SCAN (serF f) with hcscan
  have e_copySCAN : (Cmd.op (Op.copy SCAN SERF)).eval cB = c_scan := by
    rw [Cmd.eval_op, Op.eval, hcBSERF, hcscan]
  set c_k := c_scan.set K [] with hck
  have e_clearK : (Cmd.op (Op.clear K)).eval c_scan = c_k := by rw [Cmd.eval_op, Op.eval, hck]
  set c_tal := c_k.set TALLY [] with hctal
  have e_clearTAL : (Cmd.op (Op.clear TALLY)).eval c_k = c_tal := by
    rw [Cmd.eval_op, Op.eval, hctal]
  set c_cnf := c_tal.set CNFOUT [] with hccnf
  have e_clearCNF : (Cmd.op (Op.clear CNFOUT)).eval c_tal = c_cnf := by
    rw [Cmd.eval_op, Op.eval, hccnf]
  have hccnfB : State.get c_cnf B = List.replicate (serF f).length 1 := by
    rw [hccnf, State.get_set_ne _ _ _ _ (show B ≠ CNFOUT by decide), hctal,
      State.get_set_ne _ _ _ _ (show B ≠ TALLY by decide), hck,
      State.get_set_ne _ _ _ _ (show B ≠ K by decide), hcscan,
      State.get_set_ne _ _ _ _ (show B ≠ SCAN by decide), hcBB]
  set c_va := c_cnf.set VA (List.replicate (serF f).length 1) with hcva
  have e_copyVA : (Cmd.op (Op.copy VA B)).eval c_cnf = c_va := by
    rw [Cmd.eval_op, Op.eval, hccnfB, hcva]
  -- register facts at c_va
  have hcvaVA : State.get c_va VA = List.replicate (serF f).length 1 := by
    rw [hcva, State.get_set_eq]
  have hcvaSCAN : State.get c_va SCAN = serF f := by
    rw [hcva, State.get_set_ne _ _ _ _ (show SCAN ≠ VA by decide), hccnf,
      State.get_set_ne _ _ _ _ (show SCAN ≠ CNFOUT by decide), hctal,
      State.get_set_ne _ _ _ _ (show SCAN ≠ TALLY by decide), hck,
      State.get_set_ne _ _ _ _ (show SCAN ≠ K by decide), hcscan, State.get_set_eq]
  have hcvaK : State.get c_va K = [] := by
    rw [hcva, State.get_set_ne _ _ _ _ (show K ≠ VA by decide), hccnf,
      State.get_set_ne _ _ _ _ (show K ≠ CNFOUT by decide), hctal,
      State.get_set_ne _ _ _ _ (show K ≠ TALLY by decide), hck, State.get_set_eq]
  have hcvaCNF : State.get c_va CNFOUT = [] := by
    rw [hcva, State.get_set_ne _ _ _ _ (show CNFOUT ≠ VA by decide), hccnf, State.get_set_eq]
  have hcvaTAL : State.get c_va TALLY = [] := by
    rw [hcva, State.get_set_ne _ _ _ _ (show TALLY ≠ VA by decide), hccnf,
      State.get_set_ne _ _ _ _ (show TALLY ≠ CNFOUT by decide), hctal, State.get_set_eq]
  have hcvaB : State.get c_va B = List.replicate (serF f).length 1 := by
    rw [hcva, State.get_set_ne _ _ _ _ (show B ≠ VA by decide), hccnfB]
  have hcvaSERF : State.get c_va SERF = serF f := by
    rw [hcva, State.get_set_ne _ _ _ _ (show SERF ≠ VA by decide), hccnf,
      State.get_set_ne _ _ _ _ (show SERF ≠ CNFOUT by decide), hctal,
      State.get_set_ne _ _ _ _ (show SERF ≠ TALLY by decide), hck,
      State.get_set_ne _ _ _ _ (show SERF ≠ K by decide), hcscan,
      State.get_set_ne _ _ _ _ (show SERF ≠ SCAN by decide), hcBSERF]
  -- ===== the top-clause emit chain (exact states via emitLit_run) =====
  set e1 := c_va.set CNFOUT (State.get c_va CNFOUT ++ encodeLit (true, L)) with he1
  have e_lit1 : (emitLit true VA).eval c_va = e1 :=
    emitLit_run true VA c_va L (by rw [hcvaVA, hL]) (by decide)
  have he1CNF : State.get e1 CNFOUT = encodeLit (true, L) := by
    rw [he1, State.get_set_eq, hcvaCNF, List.nil_append]
  have he1VA : State.get e1 VA = List.replicate L 1 := by
    rw [he1, State.get_set_ne _ _ _ _ (show VA ≠ CNFOUT by decide), hcvaVA, hL]
  set e2 := e1.set CNFOUT (State.get e1 CNFOUT ++ encodeLit (true, L)) with he2
  have e_lit2 : (emitLit true VA).eval e1 = e2 :=
    emitLit_run true VA e1 L (by rw [he1VA]) (by decide)
  have he2CNF : State.get e2 CNFOUT = encodeLit (true, L) ++ encodeLit (true, L) := by
    rw [he2, State.get_set_eq, he1CNF]
  have he2VA : State.get e2 VA = List.replicate L 1 := by
    rw [he2, State.get_set_ne _ _ _ _ (show VA ≠ CNFOUT by decide), he1VA]
  set e3 := e2.set CNFOUT (State.get e2 CNFOUT ++ encodeLit (true, L)) with he3
  have e_lit3 : (emitLit true VA).eval e2 = e3 :=
    emitLit_run true VA e2 L (by rw [he2VA]) (by decide)
  have he3CNF : State.get e3 CNFOUT
      = encodeLit (true, L) ++ encodeLit (true, L) ++ encodeLit (true, L) := by
    rw [he3, State.get_set_eq, he2CNF]
  set e4 := (e3.set CNFOUT (State.get e3 CNFOUT ++ [0])).set TALLY
      (State.get e3 TALLY ++ [1]) with he4
  have e_end : endClause.eval e3 = e4 := endClause_run e3
  have he4CNFlen : (State.get e4 CNFOUT).length = 3 * L + 10 := by
    rw [he4, State.get_set_ne _ _ _ _ (show CNFOUT ≠ TALLY by decide), State.get_set_eq,
      he3CNF]
    simp only [List.length_append, encodeLit_length, List.length_singleton]
    omega
  -- registers the loop needs, at e4 (framed through the four sets)
  have hframe : ∀ r : Var, r ≠ CNFOUT → r ≠ TALLY → State.get e4 r = State.get c_va r := by
    intro r h1 h2
    rw [he4, State.get_set_ne _ _ _ _ h2, State.get_set_ne _ _ _ _ h1, he3,
      State.get_set_ne _ _ _ _ h1, he2, State.get_set_ne _ _ _ _ h1, he1,
      State.get_set_ne _ _ _ _ h1]
  have he4SCAN : State.get e4 SCAN = serF f := by
    rw [hframe SCAN (by decide) (by decide), hcvaSCAN]
  have he4K : State.get e4 K = [] := by
    rw [hframe K (by decide) (by decide), hcvaK]
  have he4B : State.get e4 B = List.replicate (serF f).length 1 := by
    rw [hframe B (by decide) (by decide), hcvaB]
  have he4SERF : State.get e4 SERF = serF f := by
    rw [hframe SERF (by decide) (by decide), hcvaSERF]
  -- ===== the outer-loop cost at E := 1600·(n+1)² =====
  have hsq : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have hcnflen : (encodeCnf (fsatToSat f)).length ≤ 1500 * (n + 1) ^ 2 := by
    have h1 := EvalCnfCmd.encodeCnf_length (fsatToSat f)
    have h2 := fsatToSat_size_le f
    rw [← hn] at h2
    calc (encodeCnf (fsatToSat f)).length ≤ 5 * encodable.size (fsatToSat f) := h1
      _ ≤ 5 * (300 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ h2
      _ = 1500 * (n + 1) ^ 2 := by ring
  have hE : (State.get e4 CNFOUT).length + (encodeCnf (fsatToSat f)).length
      ≤ 1600 * (n + 1) ^ 2 := by
    rw [he4CNFlen]
    have : 3 * L + 10 ≤ 100 * (n + 1) ^ 2 := by rw [hsq]; omega
    omega
  have hloop := outerLoop_cost e4 f (State.get e4 CNFOUT) (State.get e4 TALLY)
    (1600 * (n + 1) ^ 2) he4SCAN he4K rfl rfl he4B he4SERF hE
  rw [← hL] at hloop
  -- ===== the prefix op costs =====
  have hc_clearB : (Cmd.op (Op.clear B)).cost (encodeIn f) = 1 := by rw [Cmd.cost_op]; rfl
  have hc_Bloop : (Cmd.forBnd IDX0 SERF (Cmd.op (Op.appendOne B))).cost c_a
      ≤ 1 + L * 5 + L * L := by
    have h := Bloop_cost c_a L (by rw [hcaSERF, hL])
    have hk5 : (Cmd.op (Op.appendOne B)).flatK = 5 := rfl
    rw [hk5] at h
    exact h
  have hc_copySCAN : (Cmd.op (Op.copy SCAN SERF)).cost cB = L + 1 := by
    rw [Cmd.cost_op]
    show (State.get cB SERF).length + 1 = L + 1
    rw [hcBSERF, hL]
  have hc_clearK : (Cmd.op (Op.clear K)).cost c_scan = 1 := by rw [Cmd.cost_op]; rfl
  have hc_clearTAL : (Cmd.op (Op.clear TALLY)).cost c_k = 1 := by rw [Cmd.cost_op]; rfl
  have hc_clearCNF : (Cmd.op (Op.clear CNFOUT)).cost c_tal = 1 := by rw [Cmd.cost_op]; rfl
  have hc_copyVA : (Cmd.op (Op.copy VA B)).cost c_cnf = L + 1 := by
    rw [Cmd.cost_op]
    show (State.get c_cnf B).length + 1 = L + 1
    rw [hccnfB, List.length_replicate, hL]
  -- ===== the emitter costs (flat bounds at exact entry lengths) =====
  have hreads : (emitLit true VA).costReads = [CNFOUT, VA] := rfl
  have hc_lit1 : (emitLit true VA).cost c_va ≤ (emitLit true VA).flatK * (L + 1) := by
    refine (Cmd.cost_le_flat _ rfl c_va L ?_).1
    intro r hr
    rw [hreads] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hcvaCNF]; simp
    · rw [hcvaVA, List.length_replicate, hL]
  have hc_lit2 : (emitLit true VA).cost e1 ≤ (emitLit true VA).flatK * (2 * L + 4) := by
    refine (Cmd.cost_le_flat _ rfl e1 (2 * L + 3) ?_).1
    intro r hr
    rw [hreads] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [he1CNF, encodeLit_length]; omega
    · rw [he1VA, List.length_replicate]; omega
  have hc_lit3 : (emitLit true VA).cost e2 ≤ (emitLit true VA).flatK * (3 * L + 7) := by
    refine (Cmd.cost_le_flat _ rfl e2 (3 * L + 6) ?_).1
    intro r hr
    rw [hreads] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [he2CNF]
      simp only [List.length_append, encodeLit_length]
      omega
    · rw [he2VA, List.length_replicate]; omega
  have hc_end : endClause.cost e3 = 3 := rfl
  -- ===== peel the seq spine and combine =====
  unfold buildSAT
  rw [Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq,
    Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq,
    e_clearB, ← hcB, e_copySCAN, e_clearK, e_clearTAL, e_clearCNF, e_copyVA,
    e_lit1, e_lit2, e_lit3, e_end]
  rw [hc_clearB, hc_copySCAN, hc_clearK, hc_clearTAL, hc_clearCNF, hc_copyVA, hc_end]
  -- the master arithmetic: everything ≤ satK · (satOmega n + 1)⁴
  set Q := satOmega n + 1 with hQ
  have hsatK : satK = tokFK + 12 * (emitLit true VA).flatK + 100 := rfl
  have hQval : Q = 1700 * (n + 1) ^ 2 + 1 := by rw [hQ]; rfl
  have hLQ : L + 1 ≤ Q := by rw [hQval, hsq]; omega
  -- the loop term: L·(tokFK·(E+L+3)³) ≤ tokFK·Q⁴
  have hEL3 : 1600 * (n + 1) ^ 2 + L + 3 ≤ Q := by rw [hQval, hsq]; omega
  have hcube : (1600 * (n + 1) ^ 2 + L + 3) ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left hEL3 3
  have hmain : L * (tokFK * (1600 * (n + 1) ^ 2 + L + 3) ^ 3)
      ≤ tokFK * (Q * (Q * (Q * Q))) := by
    calc L * (tokFK * (1600 * (n + 1) ^ 2 + L + 3) ^ 3)
        ≤ Q * (tokFK * Q ^ 3) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hcube)
      _ = tokFK * (Q * (Q * (Q * Q))) := by ring
  -- the emitter junk: KE·(L+1) + KE·(2L+4) + KE·(3L+7) ≤ 12·KE·Q⁴
  have hemit : (emitLit true VA).flatK * (L + 1) + (emitLit true VA).flatK * (2 * L + 4)
      + (emitLit true VA).flatK * (3 * L + 7)
      ≤ 12 * (emitLit true VA).flatK * (Q * (Q * (Q * Q))) := by
    have h1 : (L + 1) + (2 * L + 4) + (3 * L + 7) ≤ 12 * Q := by
      have : L + 1 ≤ Q := hLQ
      omega
    have hQ4 : Q ≤ Q * (Q * (Q * Q)) := by
      have h1Q : 1 ≤ Q * (Q * Q) :=
        Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
      calc Q = Q * 1 := by ring
        _ ≤ Q * (Q * (Q * Q)) := Nat.mul_le_mul_left _ (by
            calc 1 ≤ Q * (Q * Q) := h1Q
              _ ≤ Q * (Q * Q) := le_refl _)
    calc (emitLit true VA).flatK * (L + 1) + (emitLit true VA).flatK * (2 * L + 4)
        + (emitLit true VA).flatK * (3 * L + 7)
        = (emitLit true VA).flatK * ((L + 1) + (2 * L + 4) + (3 * L + 7)) := by ring
      _ ≤ (emitLit true VA).flatK * (12 * Q) := Nat.mul_le_mul_left _ h1
      _ ≤ (emitLit true VA).flatK * (12 * (Q * (Q * (Q * Q)))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hQ4)
      _ = 12 * (emitLit true VA).flatK * (Q * (Q * (Q * Q))) := by ring
  -- the remaining polynomial junk: 2L² + 10L + 25 ≤ 100·Q⁴
  have hjunk : 2 * (L * L) + 10 * L + 25 ≤ 100 * (Q * (Q * (Q * Q))) := by
    have hQ1 : 1 ≤ Q := by rw [hQval]; omega
    have hLQ' : L ≤ Q := by omega
    have h2 : L * L ≤ Q * Q := Nat.mul_le_mul hLQ' hLQ'
    have hQQ4 : Q * Q ≤ Q * (Q * (Q * Q)) := by
      calc Q * Q = (Q * Q) * 1 := by ring
        _ ≤ (Q * Q) * (Q * Q) := Nat.mul_le_mul_left _ (Nat.mul_pos (by omega) (by omega))
        _ = Q * (Q * (Q * Q)) := by ring
    have hQge : Q ≤ Q * (Q * (Q * Q)) := by
      calc Q = Q * 1 := by ring
        _ ≤ Q * (Q * (Q * Q)) := Nat.mul_le_mul_left _
            (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
    omega
  -- assemble
  show 1 + 1 + (1 + _ + (1 + (L + 1) + (1 + 1 + (1 + 1 + (1 + 1 + (1 + (L + 1)
      + (1 + _ + (1 + _ + (1 + _ + (1 + 3 + _)))))))))) ≤ satBound n
  have hsb : satBound n = tokFK * (Q * (Q * (Q * Q)))
      + 12 * (emitLit true VA).flatK * (Q * (Q * (Q * Q)))
      + 100 * (Q * (Q * (Q * Q))) := by
    rw [show satBound n = satK * (Q * (Q * (Q * Q))) from rfl, hsatK]
    ring
  rw [hsb]
  set KE := (emitLit true VA).flatK with hKE
  clear_value KE
  set Q4 := Q * (Q * (Q * Q)) with hQ4d
  clear_value Q4
  set P := tokFK * Q4 with hP
  clear_value P
  set c1 := (emitLit true VA).cost c_va with hc1v
  clear_value c1
  set c2 := (emitLit true VA).cost e1 with hc2v
  clear_value c2
  set c3 := (emitLit true VA).cost e2 with hc3v
  clear_value c3
  set cbl := (Cmd.forBnd IDX0 SERF (Cmd.op (Op.appendOne B))).cost c_a with hcblv
  clear_value cbl
  set clp := (Cmd.forBnd IDX1 SERF tokenBody).cost e4 with hclpv
  clear_value clp
  set W := L * (tokFK * (1600 * (n + 1) ^ 2 + L + 3) ^ 3) with hW
  clear_value W
  omega


/-! ## The free witness and the headline `⪯p'` -/

/-- **`fsatToSat` as a concrete layer program** — the free
`PolyTimeComputableLang` witness for the LAST sound-tail step (template:
`binaryCCFSAT_reductionLang`). `decodeOut` inverts the injective `encodeCnf`
on the SAT verifier's stream register. -/
noncomputable def fsatSAT_reductionLang : PolyTimeComputableLang fsatToSat where
  c := buildSAT
  encodeIn := encodeIn
  decodeOut := decodeOut
  cost_bound := satBound
  cost_bound_poly := satBound_poly
  cost_bound_mono := satBound_mono
  encBound := fun n => 4 * n
  encBound_poly := inOPoly_mul (inOPoly_const 4) inOPoly_id
  encBound_mono := fun _ _ h => Nat.mul_le_mul_left 4 h
  encodeIn_size := encodeIn_size_le
  computes := buildSAT_computes
  cost_le := buildSAT_cost_le
  output_size_le := satBound_output
  enc_bit := encodeIn_bitState
  regBound := FRAME
  usesBelow := buildSAT_usesBelow
  width_le := encodeIn_width
  decode_agree := buildSAT_decode_agree

/-- **`FSAT ⪯p' SAT`** — the LAST sound-tail step as a live honest TM-backed
reduction. Axiom-clean: `[propext, Classical.choice, Quot.sound]`. -/
theorem fsatSAT_reducesPolyMO' : FSAT ⪯p' SAT :=
  reducesPolyMO'_of_langFree fsatSAT_reductionLang fsatToSat_correct

end FSATSATFree
