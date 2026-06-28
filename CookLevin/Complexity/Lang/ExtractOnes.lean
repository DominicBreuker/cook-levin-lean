import Complexity.Lang.Frame
import Mathlib.Tactic

/-! # `extractLeadingOnes` — recover a unary length prefix (bottom-up, Risk C2)

The **unary migration** (HANDOFF bottom-up step 2) re-lays the product encoding
bit-level as `enc(x,y) = replicate |enc x| 1 ++ [0] ++ enc x ++ enc y`. *Unpacking*
a product needs to recover `L = |enc x|` from the leading 1-run — which the
existing op set cannot do directly (`head` peels one cell; `takeAt`/`dropAt` need
the very count they seek). This module supplies the missing primitive as a **DSL
subroutine** built from existing ops + one `forBnd` loop (Option L of the
probe-validated design — no new op, op count stays 12):

```
extractLeadingOnes dst src SC HD DONE NOOP CNT :=
  copy SC src ⨾ clear dst ⨾ clear DONE ⨾
  forBnd CNT src (
    head HD SC ⨾
    ifBit DONE (clear NOOP) (ifBit HD (appendOne dst) (appendOne DONE)) ⨾
    tail SC SC)
```

After running, `dst = replicate L 1` where `L = leadingOnes (src)` is the length
of the leading 1-run of `src` (`extractLeadingOnes_get_dst`). Correctness is a
`forBnd` fold invariant (the `DONE` flag), the same pattern as the proven
`EvalCnfCmd.memberCheck`. Reusable by `swap`/`mapFst`/`mapSnd` once the product
encoding is migrated (HANDOFF bottom-up step 2d). -/

namespace Complexity.Lang

/-- The leading 1-run length of a register: the count consumers need (`= |enc x|`
under the migrated product encoding). -/
def leadingOnes (l : List Nat) : Nat := (l.takeWhile (· == 1)).length

theorem leadingOnes_le (l : List Nat) : leadingOnes l ≤ l.length := by
  induction l with
  | nil => simp [leadingOnes]
  | cons a t ih =>
    simp only [leadingOnes, List.takeWhile_cons] at ih ⊢
    by_cases ha : a = 1
    · subst ha; simp only [beq_self_eq_true, if_true, List.length_cons]; omega
    · rw [if_neg (by simpa using ha)]; simp

/-- For an index strictly inside the leading 1-run, the cell there is `1`. -/
private theorem head_drop_lt_leadingOnes (l : List Nat) :
    ∀ (i : Nat), i < leadingOnes l → (l.drop i).head? = some 1 := by
  induction l with
  | nil => intro i h; simp [leadingOnes] at h
  | cons a t ih =>
    intro i h
    simp only [leadingOnes, List.takeWhile_cons] at h
    by_cases ha : a = 1
    · subst ha
      cases i with
      | zero => simp
      | succ j =>
        simp only [beq_self_eq_true, if_true, List.length_cons] at h
        rw [List.drop_succ_cons]
        exact ih j (by simp only [leadingOnes]; omega)
    · rw [if_neg (by simpa using ha)] at h; simp at h

/-- At the first index past the leading 1-run (when it exists), the cell is not `1`. -/
private theorem head_drop_leadingOnes_ne_one (l : List Nat) :
    leadingOnes l < l.length →
      ∀ c, (l.drop (leadingOnes l)).head? = some c → c ≠ 1 := by
  induction l with
  | nil => intro h; simp [leadingOnes] at h
  | cons a t ih =>
    intro h c hc
    simp only [leadingOnes, List.takeWhile_cons] at h hc
    by_cases ha : a = 1
    · subst ha
      simp only [beq_self_eq_true, if_true, List.length_cons] at h hc
      rw [List.drop_succ_cons] at hc
      exact ih (by simp only [leadingOnes]; omega) c hc
    · rw [if_neg (by simpa using ha)] at h hc
      simp only [List.length_nil, List.drop_zero, List.head?_cons, Option.some.injEq] at hc
      subst hc; simpa using ha

/-- The loop body, named for the invariant proof. -/
private def eloBody (dst SC HD DONE NOOP : Var) : Cmd :=
  Cmd.op (.head HD SC) ;;
  Cmd.ifBit DONE (Cmd.op (.clear NOOP))
    (Cmd.ifBit HD (Cmd.op (.appendOne dst)) (Cmd.op (.appendOne DONE))) ;;
  Cmd.op (.tail SC SC)

/-- The leading-ones extractor (Option L). -/
def extractLeadingOnes (dst src SC HD DONE NOOP CNT : Var) : Cmd :=
  Cmd.op (.copy SC src) ;;
  Cmd.op (.clear dst) ;;
  Cmd.op (.clear DONE) ;;
  Cmd.forBnd CNT src (eloBody dst SC HD DONE NOOP)

/-- **One loop iteration preserves the invariant.** `st.get SC = orig.drop i`,
`st.get DONE` records whether the first non-`1` has been seen, and `st.get dst`
holds the leading 1s seen so far. -/
private theorem eloBody_step
    (dst SC HD DONE NOOP CNT : Var) (orig : List Nat) (i : Nat) (st : State)
    (hi : i < orig.length)
    (hSC : st.get SC = orig.drop i)
    (hDONE : st.get DONE = (if leadingOnes orig < i then [1] else []))
    (hdst : st.get dst = List.replicate (min i (leadingOnes orig)) 1)
    -- distinctness facts (each `read ≠ written` used in the proof)
    (hSC_CNT : SC ≠ CNT) (hDONE_CNT : DONE ≠ CNT) (hdst_CNT : dst ≠ CNT)
    (hDONE_HD : DONE ≠ HD) (hdst_HD : dst ≠ HD) (hSC_HD : SC ≠ HD)
    (hSC_dst : SC ≠ dst) (hSC_DONE : SC ≠ DONE) (hSC_NOOP : SC ≠ NOOP)
    (hDONE_dst : DONE ≠ dst) (hDONE_NOOP : DONE ≠ NOOP) (hdst_NOOP : dst ≠ NOOP) :
    ((eloBody dst SC HD DONE NOOP).eval (st.set CNT (List.replicate i 1))).get SC
        = orig.drop (i + 1)
    ∧ ((eloBody dst SC HD DONE NOOP).eval (st.set CNT (List.replicate i 1))).get DONE
        = (if leadingOnes orig < i + 1 then [1] else [])
    ∧ ((eloBody dst SC HD DONE NOOP).eval (st.set CNT (List.replicate i 1))).get dst
        = List.replicate (min (i + 1) (leadingOnes orig)) 1 := by
  set L := leadingOnes orig with hL
  set st1 := st.set CNT (List.replicate i 1) with hst1
  -- the counter set does not touch the tracked registers
  have e_SC1 : st1.get SC = orig.drop i := by
    rw [hst1, State.get_set_ne _ _ _ _ hSC_CNT]; exact hSC
  have e_DONE1 : st1.get DONE = (if L < i then [1] else []) := by
    rw [hst1, State.get_set_ne _ _ _ _ hDONE_CNT]; exact hDONE
  have e_dst1 : st1.get dst = List.replicate (min i L) 1 := by
    rw [hst1, State.get_set_ne _ _ _ _ hdst_CNT]; exact hdst
  -- SC is nonempty at index i, so `head` reads its first cell `c`
  have hnil : orig.drop i ≠ [] := by
    have : 0 < (orig.drop i).length := by rw [List.length_drop]; omega
    exact List.ne_nil_of_length_pos this
  obtain ⟨c, rest, hcons⟩ := List.exists_cons_of_ne_nil hnil
  have hhead? : (orig.drop i).head? = some c := by rw [hcons]; rfl
  -- head HD SC  ⟶  sa
  have e_head : (Cmd.op (.head HD SC)).eval st1 = st1.set HD [c] := by
    rw [Cmd.eval_op]; simp only [Op.eval, e_SC1, hcons]
  set sa := st1.set HD [c] with hsa
  have a_SC : sa.get SC = orig.drop i := by
    rw [hsa, State.get_set_ne _ _ _ _ hSC_HD]; exact e_SC1
  have a_DONE : sa.get DONE = (if L < i then [1] else []) := by
    rw [hsa, State.get_set_ne _ _ _ _ hDONE_HD]; exact e_DONE1
  have a_dst : sa.get dst = List.replicate (min i L) 1 := by
    rw [hsa, State.get_set_ne _ _ _ _ hdst_HD]; exact e_dst1
  have a_HD : sa.get HD = [c] := by rw [hsa, State.get_set_eq]
  -- per-branch: compute `sb`, then `tail` and read off the three conjuncts.
  by_cases hLi : L < i
  · -- DONE already set: branch = clear NOOP
    have hbr : (Cmd.ifBit DONE (Cmd.op (.clear NOOP))
        (Cmd.ifBit HD (Cmd.op (.appendOne dst)) (Cmd.op (.appendOne DONE)))).eval sa
        = sa.set NOOP [] := by
      rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [a_DONE, if_pos hLi]), Cmd.eval_op]; rfl
    set sb := sa.set NOOP [] with hsb
    have b_SC : sb.get SC = orig.drop i := by
      rw [hsb, State.get_set_ne _ _ _ _ hSC_NOOP]; exact a_SC
    have b_DONE : sb.get DONE = [1] := by
      rw [hsb, State.get_set_ne _ _ _ _ hDONE_NOOP, a_DONE, if_pos hLi]
    have b_dst : sb.get dst = List.replicate (min i L) 1 := by
      rw [hsb, State.get_set_ne _ _ _ _ hdst_NOOP]; exact a_dst
    have hEval : (eloBody dst SC HD DONE NOOP).eval st1 = sb.set SC (orig.drop (i + 1)) := by
      simp only [eloBody, Cmd.eval_seq, e_head, hbr, Cmd.eval_op]
      show sb.set SC (sb.get SC).tail = _
      rw [b_SC, List.tail_drop]
    refine ⟨?_, ?_, ?_⟩
    · rw [hEval, State.get_set_eq]
    · rw [hEval, State.get_set_ne _ _ _ _ hSC_DONE.symm, b_DONE, if_pos (by omega)]
    · rw [hEval, State.get_set_ne _ _ _ _ hSC_dst.symm, b_dst]
      congr 1; omega
  · -- DONE empty: inner ifBit HD on the head bit `c`
    have hDONE_empty : sa.get DONE = [] := by rw [a_DONE, if_neg hLi]
    have hiL : i ≤ L := by omega
    -- characterise `c` from the index position
    have hc_lt : i < L → c = 1 := by
      intro hlt
      have hh := head_drop_lt_leadingOnes orig i hlt
      rw [hhead?] at hh; simpa using hh
    have hc_eq : i = L → c ≠ 1 := by
      intro heq
      have hLlen : L < orig.length := by omega
      have hdrop : (orig.drop L).head? = some c := by rw [← heq]; exact hhead?
      exact head_drop_leadingOnes_ne_one orig hLlen c hdrop
    by_cases hc1 : c = 1
    · -- count this leading 1: appendOne dst
      have hiltL : i < L := by
        rcases Nat.lt_or_ge i L with h | h
        · exact h
        · exact absurd hc1 (hc_eq (by omega))
      have hbr : (Cmd.ifBit DONE (Cmd.op (.clear NOOP))
          (Cmd.ifBit HD (Cmd.op (.appendOne dst)) (Cmd.op (.appendOne DONE)))).eval sa
          = sa.set dst (sa.get dst ++ [1]) := by
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [a_DONE, if_neg hLi]; simp)]
        rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [a_HD, hc1]), Cmd.eval_op]; rfl
      set sb := sa.set dst (sa.get dst ++ [1]) with hsb
      have b_SC : sb.get SC = orig.drop i := by
        rw [hsb, State.get_set_ne _ _ _ _ hSC_dst]; exact a_SC
      have b_DONE : sb.get DONE = [] := by
        rw [hsb, State.get_set_ne _ _ _ _ hDONE_dst, a_DONE, if_neg hLi]
      have b_dst : sb.get dst = List.replicate (i + 1) 1 := by
        rw [hsb, State.get_set_eq, a_dst, show min i L = i by omega, ← List.replicate_succ']
      have hEval : (eloBody dst SC HD DONE NOOP).eval st1
          = sb.set SC (orig.drop (i + 1)) := by
        simp only [eloBody, Cmd.eval_seq, e_head, hbr, Cmd.eval_op]
        show sb.set SC (sb.get SC).tail = _
        rw [b_SC, List.tail_drop]
      refine ⟨?_, ?_, ?_⟩
      · rw [hEval, State.get_set_eq]
      · rw [hEval, State.get_set_ne _ _ _ _ hSC_DONE.symm, b_DONE, if_neg (by omega)]
      · rw [hEval, State.get_set_ne _ _ _ _ hSC_dst.symm, b_dst, show min (i + 1) L = i + 1 by omega]
    · -- first non-1: set DONE
      have hieqL : i = L := by
        rcases Nat.lt_or_ge i L with h | h
        · exact absurd (hc_lt h) hc1
        · omega
      have hbr : (Cmd.ifBit DONE (Cmd.op (.clear NOOP))
          (Cmd.ifBit HD (Cmd.op (.appendOne dst)) (Cmd.op (.appendOne DONE)))).eval sa
          = sa.set DONE (sa.get DONE ++ [1]) := by
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [a_DONE, if_neg hLi]; simp)]
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [a_HD]; simpa using hc1), Cmd.eval_op]; rfl
      set sb := sa.set DONE (sa.get DONE ++ [1]) with hsb
      have b_SC : sb.get SC = orig.drop i := by
        rw [hsb, State.get_set_ne _ _ _ _ hSC_DONE]; exact a_SC
      have b_DONE : sb.get DONE = [1] := by
        rw [hsb, State.get_set_eq, hDONE_empty]; rfl
      have b_dst : sb.get dst = List.replicate (min i L) 1 := by
        rw [hsb, State.get_set_ne _ _ _ _ hDONE_dst.symm]; exact a_dst
      have hEval : (eloBody dst SC HD DONE NOOP).eval st1
          = sb.set SC (orig.drop (i + 1)) := by
        simp only [eloBody, Cmd.eval_seq, e_head, hbr, Cmd.eval_op]
        show sb.set SC (sb.get SC).tail = _
        rw [b_SC, List.tail_drop]
      refine ⟨?_, ?_, ?_⟩
      · rw [hEval, State.get_set_eq]
      · rw [hEval, State.get_set_ne _ _ _ _ hSC_DONE.symm, b_DONE, if_pos (by omega)]
      · rw [hEval, State.get_set_ne _ _ _ _ hSC_dst.symm, b_dst]
        congr 1; omega

/-- **`extractLeadingOnes` writes the leading 1-run length in unary to `dst`.** -/
theorem extractLeadingOnes_get_dst
    (dst src SC HD DONE NOOP CNT : Var) (s : State)
    (hND : ([dst, src, SC, HD, DONE, NOOP, CNT] : List Var).Nodup) :
    ((extractLeadingOnes dst src SC HD DONE NOOP CNT).eval s).get dst
      = List.replicate (leadingOnes (s.get src)) 1 := by
  -- unpack the pairwise distinctness
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, not_false_eq_true] at hND
  obtain ⟨⟨h_ds, h_dSC, h_dHD, h_dDO, h_dNO, h_dCN⟩,
          ⟨h_sSC, h_sHD, h_sDO, h_sNO, h_sCN⟩,
          ⟨h_SCHD, h_SCDO, h_SCNO, h_SCCN⟩,
          ⟨h_HDDO, h_HDNO, h_HDCN⟩,
          ⟨h_DONO, h_DOCN⟩, h_NOCN⟩ := hND
  set orig := s.get src with horig
  -- evaluate the three prep ops to reach the loop-entry state `s0`
  set s0 := ((s.set SC orig).set dst []).set DONE [] with hs0
  have hentry : (extractLeadingOnes dst src SC HD DONE NOOP CNT).eval s
      = (Cmd.forBnd CNT src (eloBody dst SC HD DONE NOOP)).eval s0 := by
    simp only [extractLeadingOnes, Cmd.eval_seq, Cmd.eval_op, Op.eval, hs0, horig]
  have h0_src : s0.get src = orig := by
    rw [hs0, State.get_set_ne _ _ _ _ h_sDO, State.get_set_ne _ _ _ _ (Ne.symm h_ds),
      State.get_set_ne _ _ _ _ h_sSC]
  have h0_SC : s0.get SC = orig := by
    rw [hs0, State.get_set_ne _ _ _ _ h_SCDO, State.get_set_ne _ _ _ _ (Ne.symm h_dSC),
      State.get_set_eq]
  have h0_dst : s0.get dst = [] := by
    rw [hs0, State.get_set_ne _ _ _ _ h_dDO, State.get_set_eq]
  have h0_DONE : s0.get DONE = [] := by rw [hs0, State.get_set_eq]
  rw [hentry, Cmd.eval_forBnd, h0_src]
  -- the loop invariant
  set L := leadingOnes orig with hL
  have hkey := Cmd.foldlState_range_induct (eloBody dst SC HD DONE NOOP) CNT orig.length s0
    (fun i st => st.get SC = orig.drop i
      ∧ st.get DONE = (if L < i then [1] else [])
      ∧ st.get dst = List.replicate (min i L) 1)
    (by refine ⟨?_, ?_, ?_⟩
        · rw [h0_SC]; simp
        · rw [h0_DONE]; simp
        · rw [h0_dst]; simp)
    (by rintro i st hi ⟨hSC, hDONE, hdst⟩
        exact eloBody_step dst SC HD DONE NOOP CNT orig i st hi hSC hDONE hdst
          h_SCCN h_DOCN h_dCN (Ne.symm h_HDDO) h_dHD h_SCHD (Ne.symm h_dSC) h_SCDO h_SCNO
          (Ne.symm h_dDO) h_DONO h_dNO)
  obtain ⟨_, _, hdst_final⟩ := hkey
  rw [hdst_final, show min orig.length L = L by have := leadingOnes_le orig; omega]

/-- `extractLeadingOnes` touches only its named registers — the register-frame
fact consumers (`swap`/`mapFst`/`mapSnd`) need to compile it. -/
theorem extractLeadingOnes_usesBelow (dst src SC HD DONE NOOP CNT k : Var)
    (hdst : dst < k) (hsrc : src < k) (hSC : SC < k) (hHD : HD < k)
    (hDONE : DONE < k) (hNOOP : NOOP < k) (hCNT : CNT < k) :
    Cmd.UsesBelow (extractLeadingOnes dst src SC HD DONE NOOP CNT) k := by
  simp only [extractLeadingOnes, eloBody, Cmd.UsesBelow, Op.UsesBelow]
  repeat' apply And.intro
  all_goals assumption

end Complexity.Lang
