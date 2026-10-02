import CookLevin.Simulation.Program
import CookLevin.MachineFaithfulness

set_option autoImplicit false

namespace CookLevin.Sim

open CookLevin.Lang FrontPieces CookLevin.Lang.FrontWitness

/-- A closed-form bound for `powCost`. -/
theorem powCost_le' (m a : Nat) : ∀ k, powCost m a k ≤ (k + 1) * (5 * a + 8) * (m + 1) ^ (k + 1)
  | 0 => by simp [powCost]; nlinarith
  | k + 1 => by
      have ih := powCost_le' m a k
      have hX : m ^ k ≤ (m + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ m) k
      have hY : 1 ≤ (m + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos m)
      set Y := (m + 1) ^ k with hYdef
      have e1 : (m + 1) ^ (k + 1) = Y * (m + 1) := by rw [pow_succ]
      have e2 : (m + 1) ^ (k + 1 + 1) = Y * (m + 1) * (m + 1) := by rw [pow_succ, pow_succ]
      rw [e1] at ih
      rw [e2]
      unfold powCost
      set X := m ^ k
      have h1 : m * (a * X) ≤ (m + 1) * (a * Y) := Nat.mul_le_mul (Nat.le_succ m) (Nat.mul_le_mul_left _ hX)
      have h2 : m * (m * (a * X)) ≤ (m + 1) * ((m + 1) * (a * Y)) := Nat.mul_le_mul (Nat.le_succ m) h1
      have h3 : a * X ≤ a * Y := Nat.mul_le_mul_left _ hX
      nlinarith [Nat.zero_le a, Nat.zero_le m, Nat.zero_le k, Nat.zero_le (a*Y), Nat.zero_le (m * Y)]

theorem cost_seq_le {c1 c2 : Cmd} {s : State} {A B : Nat} (h1 : c1.cost s ≤ A)
    (h2 : c2.cost (c1.eval s) ≤ B) : (c1 ;; c2).cost s ≤ 1 + A + B := by
  rw [Cmd.cost_seq]; omega

theorem emitConst_cost (dst : Var) (bits : List Nat) (s : State) :
    (emitConst dst bits).cost s = 1 + 2 * bits.length := (emitConst_run dst bits s).2.2

theorem appendC_cost (dst : Var) (bits : List Nat) (s : State) :
    (appendC dst bits).cost s = 1 + 2 * bits.length := by
  rw [show appendC dst bits = appendConst nop dst bits from rfl,
    (appendConst_run dst bits nop s).2.2]
  rfl

theorem clearList_cost : ∀ (l : List Var) (s : State), (clearList l).cost s = 2 * l.length + 1
  | [], _ => rfl
  | r :: l, s => by
      show 1 + 1 + (clearList l).cost _ = _
      rw [clearList_cost l, List.length_cons]; omega

/-! ## Phase 1 -/

theorem failBody_facts (st : State) :
    failBody.cost st ≤ (State.get st SCAN).length + 6
    ∧ (State.get (failBody.eval st) SCAN).length ≤ (State.get st SCAN).length := by
  unfold failBody
  rw [Cmd.cost_seq, Cmd.eval_seq, Cmd.cost_op, Cmd.eval_op]
  simp only [Op.eval, Op.cost]
  set st1 := st.set SB (if (State.get st SCAN).isEmpty then [0] else [1]) with hst1
  have hS : State.get st1 SCAN = State.get st SCAN := State.get_set_ne _ _ _ _ (by decide)
  by_cases hb : State.get st1 SB = [1]
  · rw [Cmd.cost_ifBit_true _ _ _ _ hb, Cmd.eval_ifBit_true _ _ _ _ hb, Cmd.cost_op,
      Cmd.eval_op]
    simp only [Op.eval, Op.cost, State.get_set_eq, hS, List.length_tail]
    omega
  · rw [Cmd.cost_ifBit_false _ _ _ _ hb, Cmd.eval_ifBit_false _ _ _ _ hb, emitConst_cost,
      emit_frame _ _ _ _ (by decide), hS]
    simp

/-- The cost bound of phase 1 in the lengths `mx = |x|`, `mc = |c|`. -/
def lenBound (a k b mx mc : Nat) : Nat :=
  30 + 5 * mx + mx * mx + 2 * a + (k + 1) * (5 * a + 8) * (mx + 1) ^ (k + 1) + 2 * b
    + (a * mx ^ k + b) + mc * (a * mx ^ k + b + 6) + mc * mc

theorem lenCode_cost (a k b : Nat) (s : State) :
    (lenCode a k b).cost s
      ≤ lenBound a k b (State.get s XO).length (State.get s CI).length := by
  set mx := (State.get s XO).length with hmx
  set mc := (State.get s CI).length with hmc
  unfold lenCode
  -- the states, as in `lenCode_run`
  obtain ⟨y1, y2⟩ := tallyCells_run CNT TL [XO] s (by decide) (by decide)
  set s1 := (tallyCells CNT TL [XO]).eval s with hs1
  have hTL : State.get s1 TL = List.replicate mx 1 := by rw [y1]; simp [hmx]
  have c1 : (tallyCells CNT TL [XO]).cost s ≤ 1 + tallyRegCost mx := by
    have := tallyCells_cost CNT TL [XO] s (by decide) (by decide)
    simpa [hmx] using this
  set s2 := (emitConst PL (List.replicate a 1)).eval s1 with hs2
  have hPL2 : State.get s2 PL = List.replicate a 1 := emit_get _ _ _ (replicate_one_bits _)
  have f2 : ∀ r, r ≠ PL → State.get s2 r = State.get s1 r := fun r hr => emit_frame _ _ _ r hr
  obtain ⟨p1, p2, p3⟩ := powLoop_run CNT TL PTMP PL k s2 mx a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [f2 _ (by decide), hTL]) hPL2
  set s3 := (powLoop CNT TL PTMP PL k).eval s2 with hs3
  obtain ⟨q1, q2⟩ := appendC_run PL (List.replicate b 1) s3 (by decide) (replicate_one_bits _)
  set s4 := (appendC PL (List.replicate b 1)).eval s3 with hs4
  have hPL4 : State.get s4 PL = List.replicate (a * mx ^ k + b) 1 := by
    rw [q1, p1, List.replicate_add]
  set s5 := (Cmd.op (.copy SCAN PL)).eval s4 with hs5
  have hS5 : State.get s5 SCAN = List.replicate (a * mx ^ k + b) 1 := by
    rw [hs5, Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, hPL4]
  set s6 := (emitConst FAIL [0]).eval s5 with hs6
  have hS6 : (State.get s6 SCAN).length = a * mx ^ k + b := by
    rw [hs6, emit_frame _ _ _ _ (by decide), hS5, List.length_replicate]
  have hCI6 : (State.get s6 CI).length = mc := by
    rw [hs6, emit_frame _ _ _ _ (by decide), hs5, Cmd.eval_op]
    simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ (by decide), q2 _ (by decide) (by decide),
      p2 _ (by decide) (by decide) (by decide), f2 _ (by decide), y2 _ (by decide) (by decide)]
  have c7 := Cmd.cost_forBnd_le CNT CI failBody s6 (a * mx ^ k + b + 6)
    (fun _ st => (State.get st SCAN).length ≤ a * mx ^ k + b) (le_of_eq hS6)
    (fun i st _ hst => by
      have := (failBody_facts (st.set CNT (List.replicate i 1))).2
      rw [State.get_set_ne _ _ _ _ (by decide)] at this
      exact le_trans this hst)
    (fun i st _ hst => by
      have := (failBody_facts (st.set CNT (List.replicate i 1))).1
      rw [State.get_set_ne _ _ _ _ (by decide)] at this
      omega)
  rw [hCI6] at c7
  have c5 : (Cmd.op (.copy SCAN PL)).cost s4 = a * mx ^ k + b + 1 := by
    rw [Cmd.cost_op]; simp only [Op.cost, hPL4, List.length_replicate]
  have hpow := powCost_le' mx a k
  refine cost_seq_le c1 (cost_seq_le (le_of_eq (emitConst_cost _ _ _))
    (cost_seq_le (le_trans p3 hpow) (cost_seq_le (le_of_eq (appendC_cost _ _ _))
      (cost_seq_le (le_of_eq c5) (cost_seq_le (le_of_eq (emitConst_cost _ _ _)) c7))))) |>.trans ?_
  simp only [List.length_replicate, List.length_singleton, lenBound, tallyRegCost]
  nlinarith

/-! ## Phase 2 -/

def timerBound (ct kt dt mx mc : Nat) : Nat :=
  2 + tallyRegCost mx + tallyRegCost mc + monoUB ct kt dt (mx + mc)

theorem timerCode_cost (ct kt dt : Nat) (s : State) :
    (timerCode ct kt dt).cost s
      ≤ timerBound ct kt dt (State.get s XO).length (State.get s CI).length := by
  unfold timerCode
  have c1 := tallyCells_cost CNT TL [XO, CI] s (by decide) (by decide)
  obtain ⟨y1, -⟩ := tallyCells_run CNT TL [XO, CI] s (by decide) (by decide)
  have hTL : State.get ((tallyCells CNT TL [XO, CI]).eval s) TL
      = List.replicate ((State.get s XO).length + (State.get s CI).length) 1 := by
    rw [y1]; simp
  obtain ⟨-, -, u3⟩ := unaryMonomial_run ct kt dt CNT BASE PTMP TL TIMER _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hTL
  refine (cost_seq_le c1 (le_trans u3 (monomialCost_le_monoUB _ _ _ _))).trans ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, timerBound]
  omega

/-! ## Phase 3 -/

theorem blk_length_le (W v : Nat) : (blk W v).length ≤ W + v := by
  simp [blk]; omega

theorem bitBody_facts (W : Nat) (st : State) :
    (bitBody W).cost st ≤ (State.get st SCAN).length + 2 * W + 10
    ∧ (State.get ((bitBody W).eval st) SCAN).length ≤ (State.get st SCAN).length := by
  unfold bitBody
  rw [Cmd.cost_seq, Cmd.eval_seq, Cmd.cost_op, Cmd.eval_op, Cmd.cost_seq, Cmd.eval_seq,
    Cmd.cost_op, Cmd.eval_op, op_head_eval]
  simp only [Op.eval, Op.cost]
  set st1 := st.set SB ((State.get st SCAN).take 1) with hst1
  have hS1 : State.get st1 SCAN = State.get st SCAN := State.get_set_ne _ _ _ _ (by decide)
  set st2 := st1.set SCAN (State.get st1 SCAN).tail with hst2
  have hS2 : State.get st2 SCAN = (State.get st SCAN).tail := by
    rw [hst2, State.get_set_eq, hS1]
  have hb2 := blk_length_le W 2
  have hb1 := blk_length_le W 1
  by_cases hb : State.get st2 SB = [1]
  · rw [Cmd.cost_ifBit_true _ _ _ _ hb, Cmd.eval_ifBit_true _ _ _ _ hb, appendC_cost,
      (appendC_run RT (blk W 2) st2 (by decide) (blk_bits W 2)).2 _ (by decide) (by decide),
      hS2, hS1, List.length_tail]
    omega
  · rw [Cmd.cost_ifBit_false _ _ _ _ hb, Cmd.eval_ifBit_false _ _ _ _ hb, appendC_cost,
      (appendC_run RT (blk W 1) st2 (by decide) (blk_bits W 1)).2 _ (by decide) (by decide),
      hS2, hS1, List.length_tail]
    omega

/-- The cost bound of `bitLoop` on a source of length `m`. -/
def bitBound (W m : Nat) : Nat := m + 3 + m * (m + 2 * W + 10) + m * m

theorem bitLoop_cost (W : Nat) (src : Var) (s : State) :
    (bitLoop W src).cost s ≤ bitBound W (State.get s src).length := by
  unfold bitLoop
  rw [Cmd.cost_seq, Cmd.cost_op, Cmd.eval_op]
  simp only [Op.cost, Op.eval]
  set m := (State.get s src).length with hm
  set s1 := s.set SCAN (State.get s src) with hs1
  have hS : (State.get s1 SCAN).length = m := by rw [hs1, State.get_set_eq]
  have c := Cmd.cost_forBnd_le CNT SCAN (bitBody W) s1 (m + 2 * W + 10)
    (fun _ st => (State.get st SCAN).length ≤ m) (le_of_eq hS)
    (fun i st _ hst => by
      have := (bitBody_facts W (st.set CNT (List.replicate i 1))).2
      rw [State.get_set_ne _ _ _ _ (by decide)] at this
      exact le_trans this hst)
    (fun i st _ hst => by
      have := (bitBody_facts W (st.set CNT (List.replicate i 1))).1
      rw [State.get_set_ne _ _ _ _ (by decide)] at this
      omega)
  rw [hS] at c
  unfold bitBound
  omega

def initBound (W start mx mc : Nat) : Nat :=
  60 + 10 * W + 2 * start + bitBound W mx + bitBound W mc

theorem initCode_cost (M : FlatTM) (x c : List Bool) (s : State)
    (hx : State.get s XO = bitsOf x) (hc : State.get s CI = bitsOf c) :
    (initCode M).cost s ≤ initBound (wid M) M.start x.length c.length := by
  set W := wid M with hW
  have hxl : (bitsOf x).length = x.length := by simp [bitsOf]
  have hcl : (bitsOf c).length = c.length := by simp [bitsOf]
  unfold initCode
  set s1 := (Cmd.op (.clear LT)).eval s with hs1
  set s2 := (Cmd.op (.clear EX)).eval s1 with hs2
  set s3 := (emitConst RT (blk W 3)).eval s2 with hs3
  have hX3 : State.get s3 XO = bitsOf x := by
    rw [hs3, emit_frame _ _ _ _ (by decide), hs2, hs1]
    simp only [Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide), hx]
  have hC3 : State.get s3 CI = bitsOf c := by
    rw [hs3, emit_frame _ _ _ _ (by decide), hs2, hs1]
    simp only [Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide), hc]
  set s4 := (bitLoop W XO).eval s3 with hs4
  have hC4 : State.get s4 CI = bitsOf c := by
    rw [hs4, (bitLoop_run W XO x s3 hX3).2 _ (by decide) (by decide) (by decide) (by decide)
      (by decide), hC3]
  set s5 := (appendC RT (blk W 0)).eval s4 with hs5
  have hC5 : State.get s5 CI = bitsOf c := by
    rw [hs5, (appendC_run RT (blk W 0) s4 (by decide) (blk_bits W 0)).2 _ (by decide)
      (by decide), hC4]
  have k4 := bitLoop_cost W XO s3
  rw [hX3, hxl] at k4
  have k6 := bitLoop_cost W CI s5
  rw [hC5, hcl] at k6
  have e3 := blk_length_le W 3
  have e0 := blk_length_le W 0
  have cl : ∀ (r : Var) (st : State), (Cmd.op (.clear r)).cost st ≤ 1 := fun _ _ => le_refl _
  have h := cost_seq_le (cl LT s)
    (cost_seq_le (cl EX _)
    (cost_seq_le (le_of_eq (emitConst_cost RT (blk W 3) _))
    (cost_seq_le k4
    (cost_seq_le (le_of_eq (appendC_cost RT (blk W 0) _))
    (cost_seq_le k6
    (cost_seq_le (le_of_eq (appendC_cost RT (blk W 0 ++ blk W 3) _))
    (cost_seq_le (le_of_eq (emitConst_cost ST (List.replicate M.start 1) _))
    (cost_seq_le (le_of_eq (emitConst_cost HL [haltBit M M.start] _))
    (le_of_eq (clearList_cost tempRegs _))))))))))
  refine h.trans ?_
  simp only [List.length_append, List.length_replicate, initBound,
    tempRegs, List.length_cons, List.length_nil]
  omega

/-! ## Phase 5 -/

theorem verdict_cost (acc : Nat) (s : State) :
    (verdict acc).cost s ≤ 3 * acc + (State.get s ST).length + 10 := by
  unfold verdict
  set s1 := (emitConst CK (List.replicate acc 1)).eval s with hs1
  have hST : State.get s1 ST = State.get s ST := emit_frame _ _ _ _ (by decide)
  have hCK : State.get s1 CK = List.replicate acc 1 := emit_get _ _ _ (replicate_one_bits _)
  set s2 := (Cmd.op (.eqBit XO ST CK)).eval s1 with hs2
  have c2 : (Cmd.op (.eqBit XO ST CK)).cost s1 = (State.get s ST).length + acc + 1 := by
    rw [Cmd.cost_op]; simp only [Op.cost, hST, hCK, List.length_replicate]
  have c3 : (Cmd.ifBit FAIL (emitConst XO [0]) nop).cost s2 ≤ 4 := by
    by_cases hF : State.get s2 FAIL = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ hF, emitConst_cost]; simp
    · rw [Cmd.cost_ifBit_false _ _ _ _ hF]
      have : nop.cost s2 = 1 := rfl
      omega
  have := cost_seq_le (le_of_eq (emitConst_cost CK (List.replicate acc 1) s))
    (cost_seq_le (le_of_eq c2) c3)
  simp only [List.length_replicate] at this
  omega

/-! ## Phase 4 -/

/-- The registers whose lengths a program's cost depends on are registers it uses. -/
theorem costReads_lt {k : Nat} : ∀ {c : Cmd}, Cmd.UsesBelow c k → ∀ r ∈ c.costReads, r < k := by
  intro c
  induction c with
  | op o =>
      intro h r hr
      cases o <;> simp_all [Cmd.costReads, Op.costReads, Cmd.UsesBelow, Op.UsesBelow]
      all_goals (obtain ⟨-, h1, h2⟩ := h; rcases hr with rfl | rfl <;> assumption)
  | seq c1 c2 ih1 ih2 =>
      intro h r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact ih1 h.1 r hr
      · exact ih2 h.2 r hr
  | ifBit t cT cE ihT ihE =>
      intro h r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact ihT h.2.1 r hr
      · exact ihE h.2.2 r hr
  | forBnd cnt bnd body ih =>
      intro h r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact h.2.1
      · exact ih h.2.2 r hr

theorem appendConst_lf (dst : Var) : ∀ (bits : List Nat) (c0 : Cmd), c0.loopFree = true →
    (appendConst c0 dst bits).loopFree = true
  | [], _, h => h
  | b :: bs, c0, h => by
      show (appendConst (c0 ;; appendBit dst b) dst bs).loopFree = true
      refine appendConst_lf dst bs _ ?_
      simp only [Cmd.loopFree, h, appendBit, Bool.true_and]

theorem emitConst_lf (dst : Var) (bits : List Nat) : (emitConst dst bits).loopFree = true :=
  appendConst_lf dst bits _ rfl

theorem takeRep_lf (dst : Var) : ∀ n, (takeRep n dst).loopFree = true
  | 0 => rfl
  | n + 1 => by simp [takeRep, Cmd.loopFree, takeRep_lf dst n]

theorem dropRep_lf (r : Var) : ∀ n, (dropRep n r).loopFree = true
  | 0 => rfl
  | n + 1 => by simp [dropRep, Cmd.loopFree, dropRep_lf r n]

theorem chainCode_lf (M : FlatTM) (W : Nat) : ∀ es, (chainCode M W es).loopFree = true
  | [] => rfl
  | e :: es => by
      have hw : (writeCode W (wrSym e)).loopFree = true := by
        cases wrSym e <;> simp [writeCode, Cmd.loopFree, nop, dropRep_lf, emitConst_lf]
      have hm : (moveCode W (mvDir e)).loopFree = true := by
        cases mvDir e <;>
          simp [moveCode, Cmd.loopFree, nop, takeTo, takeRep_lf, dropRep_lf]
      simp [chainCode, testCode, applyCode, Cmd.loopFree, emitConst_lf, hw, hm,
        chainCode_lf M W es]

theorem clearList_lf : ∀ l, (clearList l).loopFree = true
  | [] => rfl
  | r :: l => by simp only [clearList, Cmd.loopFree, clearList_lf l, Bool.and_true]

theorem loopBody_lf (M : FlatTM) : (loopBody M).loopFree = true := by
  simp [loopBody, guardedStep, stepCode, Cmd.loopFree, nop, takeTo, takeRep_lf, chainCode_lf,
    clearTemps, clearList_lf]

/-- One step grows the written region and the head position by at most one and keeps the
state declared. -/
theorem stepCfg_growth (M : FlatTM) (hM : validFlatTM M) (h1 : M.tapes = 1)
    (cfg : FlatTMConfig) (l : List Nat) (h : Nat) (r : List Nat)
    (ht : cfg.tapes = [(l, h, r)]) (hq : cfg.state_idx < M.states) :
    ∃ l' h' r', (stepCfg M cfg).tapes = [(l', h', r')] ∧ r'.length ≤ r.length + 1
      ∧ h' ≤ h + 1 ∧ (stepCfg M cfg).state_idx < M.states := by
  unfold stepCfg
  split_ifs with hh
  · exact ⟨l, h, r, ht, by omega, by omega, hq⟩
  · cases hs : stepFlatTM M cfg with
    | none => exact ⟨l, h, r, ht, by omega, by omega, hq⟩
    | some cfg' =>
        simp only [Option.getD_some]
        have hlt := MachineFaithfulness.stepFlatTM_state_lt M cfg cfg' hM hs
        obtain ⟨e, hfind, happly⟩ :
            ∃ e, M.trans.find? (fun e => entryMatchesConfig e cfg) = some e ∧
              applyTransitionEntry cfg e = some cfg' := by
          simpa [stepFlatTM, Option.bind_eq_some_iff] using hs
        have he := hM.2.2 e (List.mem_of_find?_eq_some hfind)
        rw [applyTransitionEntry_one h1 he cfg l h r ht] at happly
        cases happly
        refine ⟨_, _, _, rfl, ?_, ?_, hlt⟩
        · exact MachineFaithfulness.tapeStep_length_le_succ (l, h, r) _ _
        · exact MachineFaithfulness.tapeStep_head_le (l, h, r) _ _

theorem iterate_growth (M : FlatTM) (hM : validFlatTM M) (h1 : M.tapes = 1)
    (cfg : FlatTMConfig) (l : List Nat) (h : Nat) (r : List Nat)
    (ht : cfg.tapes = [(l, h, r)]) (hq : cfg.state_idx < M.states) :
    ∀ i, ∃ l' h' r', ((stepCfg M)^[i] cfg).tapes = [(l', h', r')] ∧ r'.length ≤ r.length + i
      ∧ h' ≤ h + i ∧ ((stepCfg M)^[i] cfg).state_idx < M.states
  | 0 => ⟨l, h, r, ht, by omega, by omega, hq⟩
  | i + 1 => by
      obtain ⟨l1, h1', r1, ht1, hr1, hh1, hq1⟩ := iterate_growth M hM h1 cfg l h r ht hq i
      obtain ⟨l2, h2, r2, ht2, hr2, hh2, hq2⟩ := stepCfg_growth M hM h1 _ l1 h1' r1 ht1 hq1
      rw [Function.iterate_succ_apply']
      exact ⟨l2, h2, r2, ht2, by omega, by omega, hq2⟩

/-- The register lengths of a represented configuration. -/
theorem repr_lengths (M : FlatTM) (cfg : FlatTMConfig) (s : State) (hR : Repr M cfg s)
    (l : List Nat) (h : Nat) (r : List Nat) (ht : cfg.tapes = [(l, h, r)]) :
    (State.get s LT).length ≤ wid M * r.length ∧ (State.get s RT).length ≤ wid M * r.length
    ∧ (State.get s EX).length ≤ h ∧ (State.get s ST).length = cfg.state_idx
    ∧ (State.get s HL).length = 1 := by
  obtain ⟨l', h', r', ht', hb, ⟨hL, hR', hE⟩, hS, hH⟩ := hR
  rw [ht] at ht'
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at ht'
  obtain ⟨-, rfl, rfl⟩ := ht'
  have hz := zip_bounded (h := h) hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hL, blocks_length _ _ hz.1]
    apply Nat.mul_le_mul_left
    simp [zip]
  · rw [hR', blocks_length _ _ hz.2]
    apply Nat.mul_le_mul_left
    simp [zip]
  · rw [hE]; simp [zip]
  · rw [hS]; simp
  · rw [hH]; rfl

theorem mainLoop_cost (M : FlatTM) (hM : validFlatTM M) (h1 : M.tapes = 1)
    (cfg : FlatTMConfig) (s : State) (hR : Repr M cfg s)
    (htemp : ∀ r ∈ tempRegs, State.get s r = [])
    (l : List Nat) (h : Nat) (r : List Nat) (ht : cfg.tapes = [(l, h, r)])
    (hq : cfg.state_idx < M.states) :
    (mainLoop M).cost s
      ≤ 1 + (State.get s TIMER).length * ((loopBody M).flatK
          * (wid M * (r.length + (State.get s TIMER).length) + h + (State.get s TIMER).length
              + M.states + 1 + 1))
        + (State.get s TIMER).length * (State.get s TIMER).length := by
  set T := (State.get s TIMER).length with hT
  unfold mainLoop
  refine Cmd.cost_forBnd_flat_le CNT TIMER (loopBody M) (loopBody_lf M) s
    (wid M * (r.length + T) + h + T + M.states + 1)
    (fun i st => Repr M ((stepCfg M)^[i] cfg) st ∧ ∀ q ∈ tempRegs, State.get st q = [])
    ⟨hR, htemp⟩ ?_ ?_
  · intro i st _ ⟨hi, _⟩
    have hi' : Repr M ((stepCfg M)^[i] cfg) (st.set CNT (List.replicate i 1)) :=
      hi.frame fun r hr => State.get_set_ne _ _ _ _ (by
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    unfold loopBody
    rw [Cmd.eval_seq, Function.iterate_succ_apply']
    exact ⟨(guardedStep_run M hM h1 _ _ hi').clearTemps, fun q hq => clearTemps_temp _ q hq⟩
  · intro i st hiT ⟨hi, htm⟩ q hqr
    have hqK : q < KB := costReads_lt (loopBody_ub M) q hqr
    rw [State.get_set_ne _ _ _ _ (Nat.ne_of_lt (show q < CNT from hqK))]
    obtain ⟨l', h', r', ht', hr', hh', hq'⟩ := iterate_growth M hM h1 cfg l h r ht hq i
    obtain ⟨b1, b2, b3, b4, b5⟩ := repr_lengths M _ st hi l' h' r' ht'
    have hW1 : wid M * r'.length ≤ wid M * (r.length + T) :=
      Nat.mul_le_mul_left _ (by omega)
    rcases below_KB q hqK with rfl | rfl | rfl | rfl | rfl | hqt
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [htm q hqt]; simp

end CookLevin.Sim
