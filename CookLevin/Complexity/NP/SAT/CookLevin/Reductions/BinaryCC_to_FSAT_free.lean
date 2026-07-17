import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_free_run

set_option autoImplicit false

/-! # `BinaryCC ⪯p' FSAT` — cost accounting, the free witness, the headline `⪯p'`

Third module of the build-health split (2026-07-17, see `_run`'s header):
the `cost_le` ladder, `binaryCCFSAT_reductionLang`, and
`binaryCC_reducesPolyMO' : BinaryCC ⪯p' FSAT`. Downstream imports of
`…Reductions.BinaryCC_to_FSAT_free` are unchanged (this module transitively
re-exports `_run` and `_defs`). NOTE: the cost proofs consume the run lemmas,
so `_run` → this module is inherently SERIAL — the split's wall-clock win is
the `_defs` extraction (FSAT ∥ BinaryCC), not run∥cost. -/

namespace BinaryCCFSATFree

open Complexity.Lang
open BinaryCCToFSAT

/-! ## 4. `cost_le` — the cost accounting (session 4)

Per-loop cost bounds via `Cmd.cost_forBnd_le`, reusing the run invariants
(`BSInv`/`SBInv`/`CAInv`/…) and their `_step` lemmas as the loop motive
(extended by a `WREG`-length clause where the body reads scratch), and bounding
each loop-free body by the generic `Cmd.cost_le_flat` (`Lang/CostFlat.lean`).
Every lemma takes ONE ceiling parameter `Ω` with hypotheses stating what it
dominates; `OUT` ceilings chain through `serF`-length bounds
(`serF_length_le_size` + `listAnd`/`listOr` membership monotonicity) against
the final output, whose size `BinaryCC_to_FSAT_instance_size_bound` bounds.
Constants stay SYMBOLIC (`def`s over `Cmd.flatK`) — only `inOPoly` matters. -/

/-! ### Serialization length bounds (`serF_length_le_size` itself lives in `_defs`) -/

/-- A conjunct's serialization is no longer than the whole `listAnd`'s. -/
theorem serF_length_le_of_mem_listAnd {f : formula} {fs : List formula}
    (h : f ∈ fs) : (serF f).length ≤ (serF (listAnd fs)).length := by
  induction fs with
  | nil => cases h
  | cons g gs ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · show _ ≤ (serF (.fand f (listAnd gs))).length
        simp [serF]; omega
      · refine le_trans (ih h') ?_
        show _ ≤ (serF (.fand g (listAnd gs))).length
        simp [serF]; omega

/-- A disjunct's serialization is no longer than the whole `listOr`'s. -/
theorem serF_length_le_of_mem_listOr {f : formula} {fs : List formula}
    (h : f ∈ fs) : (serF f).length ≤ (serF (listOr fs)).length := by
  induction fs with
  | nil => cases h
  | cons g gs ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · show _ ≤ (serF (.forr f (listOr gs))).length
        simp [serF]; omega
      · refine le_trans (ih h') ?_
        show _ ≤ (serF (.forr g (listOr gs))).length
        simp [serF]; omega

/-- Mid-loop `OUT` ceiling, `listAnd` level: any processed-prefix `andPrefix`
is bounded by the closed serialization. -/
theorem andPrefix_take_length_le (fs : List formula) (i : Nat) :
    (andPrefix (fs.take i)).length ≤ (serF (listAnd fs)).length := by
  rw [serF_listAnd]
  calc (andPrefix (fs.take i)).length
      ≤ (andPrefix (fs.take i)).length + (andPrefix (fs.drop i)).length :=
        Nat.le_add_right _ _
    _ = (andPrefix (fs.take i ++ fs.drop i)).length := by
        rw [andPrefix_append, List.length_append]
    _ = (andPrefix fs).length := by rw [List.take_append_drop]
    _ ≤ (andPrefix fs ++ serF .ftrue).length := by simp

/-- Mid-loop `OUT` ceiling, `listOr` level. -/
theorem orPrefix_take_length_le (fs : List formula) (i : Nat) :
    (orPrefix (fs.take i)).length ≤ (serF (listOr fs)).length := by
  rw [serF_listOr]
  calc (orPrefix (fs.take i)).length
      ≤ (orPrefix (fs.take i)).length + (orPrefix (fs.drop i)).length :=
        Nat.le_add_right _ _
    _ = (orPrefix (fs.take i ++ fs.drop i)).length := by
        rw [orPrefix_append, List.length_append]
    _ = (orPrefix fs).length := by rw [List.take_append_drop]
    _ ≤ _ := by simp

/-- Mid-loop `OUT` ceiling, bit level. -/
theorem bitsPrefix_take_length_le (start : Nat) (bits : List Bool) (i : Nat) :
    (bitsPrefix start (bits.take i)).length
      ≤ (serF (BinaryCCToFSAT.encodeBitsAt start bits)).length := by
  rw [serF_encodeBitsAt]
  calc (bitsPrefix start (bits.take i)).length
      ≤ (bitsPrefix start (bits.take i)).length
        + (bitsPrefix (start + (bits.take i).length) (bits.drop i)).length :=
        Nat.le_add_right _ _
    _ = (bitsPrefix start (bits.take i ++ bits.drop i)).length := by
        rw [bitsPrefix_append, List.length_append]
    _ = (bitsPrefix start bits).length := by rw [List.take_append_drop]
    _ ≤ _ := by simp

/-- Mid-loop `OUT` ceiling, card level. -/
theorem cardsPrefix_take_length_le (sA sB : Nat) (cs : List (CCCard Bool)) (j : Nat) :
    (cardsPrefix sA sB (cs.take j)).length
      ≤ (serF (listOr (cs.map (encodeCardAt sA sB)))).length := by
  rw [serF_encodeCardsAt]
  calc (cardsPrefix sA sB (cs.take j)).length
      ≤ (cardsPrefix sA sB (cs.take j)).length
        + (cardsPrefix sA sB (cs.drop j)).length := Nat.le_add_right _ _
    _ = (cardsPrefix sA sB (cs.take j ++ cs.drop j)).length := by
        rw [cardsPrefix_append, List.length_append]
    _ = (cardsPrefix sA sB cs).length := by rw [List.take_append_drop]
    _ ≤ _ := by simp

/-- Dropping bits only shortens the sentinel stream. -/
private theorem encSList_drop_length_le (l : List Nat) (i : Nat) :
    (FlatTCCFree.encSList (l.drop i)).length ≤ (FlatTCCFree.encSList l).length := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
      cases l with
      | nil => simp
      | cons v xs =>
          rw [List.drop_succ_cons]
          refine (ih xs).trans ?_
          show _ ≤ (FlatTCCFree.encSElem v ++ FlatTCCFree.encSList xs).length
          simp

/-- Dropping cards only shortens the card stream. -/
private theorem encCardsOut_drop_length_le (cs : List (CCCard Nat)) (j : Nat) :
    (FlatTCCFree.encCardsOut (cs.drop j)).length
      ≤ (FlatTCCFree.encCardsOut cs).length := by
  induction j generalizing cs with
  | zero => simp
  | succ j ih =>
      cases cs with
      | nil => simp
      | cons c cs =>
          rw [List.drop_succ_cons]
          refine (ih cs).trans ?_
          show _ ≤ (FlatTCCFree.encCardOut c ++ FlatTCCFree.encCardsOut cs).length
          simp

/-- Dropping final strings only shortens the final stream. -/
private theorem encFinal_drop_length_le (fss : List (List Nat)) (j : Nat) :
    (FlatTCCFree.encFinal (fss.drop j)).length
      ≤ (FlatTCCFree.encFinal fss).length := by
  induction j generalizing fss with
  | zero => simp
  | succ j ih =>
      cases fss with
      | nil => simp
      | cons s fss =>
          rw [List.drop_succ_cons]
          refine (ih fss).trans ?_
          show _ ≤ (FlatTCCFree.encSList s ++ FlatTCCFree.encFinal fss).length
          simp

/-! ### Constant-cost facts for the literal-tag emitters -/

private theorem emitFtrue_cost (s : State) : emitFtrue.cost s = 3 := rfl
private theorem emitFandTag_cost (s : State) : emitFandTag.cost s = 3 := rfl
private theorem emitForrTag_cost (s : State) : emitForrTag.cost s = 3 := rfl
private theorem emitFalse_cost (s : State) : emitFalse.cost s = 9 := rfl

/-! ### The scan-driven bit emitter: cost -/

/-- The loop body of `emitBitsFromScan`, named for the cost pass. -/
private def bsBody (BASE : Nat) : Cmd :=
  Cmd.op (.head TFLG SCAN) ;; Cmd.op (.tail SCAN SCAN) ;;
  Cmd.op (.concat WREG BASE KBIT) ;; emitFandTag ;; emitLitAt

private theorem emitBitsFromScan_eq (BASE bound : Nat) :
    emitBitsFromScan BASE bound = (Cmd.forBnd KBIT bound (bsBody BASE) ;; emitFtrue) := rfl

/-- `bsBody`'s only `WREG` write is `WREG := BASE ++ counter`. -/
private theorem bsBody_WREG (BASE : Nat) (w : State)
    (hBT : BASE ≠ TFLG) (hBS : BASE ≠ SCAN) :
    State.get ((bsBody BASE).eval w) WREG = State.get w BASE ++ State.get w KBIT := by
  unfold bsBody
  rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq,
    Cmd.eval_get_of_not_writes _ _ WREG (by decide), Cmd.eval_op]
  simp only [Op.eval, State.get_set_eq, Cmd.eval_op]
  rw [State.get_set_ne _ _ _ _ hBS, State.get_set_ne _ _ _ _ hBT,
    State.get_set_ne _ _ _ _ (show KBIT ≠ SCAN by decide),
    State.get_set_ne _ _ _ _ (show KBIT ≠ TFLG by decide)]

/-- **`emitBitsFromScan` cost**: quadratic in the ceiling `Ω`. `Ω` must dominate
the entry `OUT` plus the full emission, the entry `WREG`, and `start + |bits|`. -/
theorem emitBitsFromScan_cost (BASE bound start : Nat) (bits : List Bool) (u : State)
    (Ω : Nat)
    (hBS : BASE ≠ SCAN) (hBO : BASE ≠ OUT) (hBW : BASE ≠ WREG) (hBT : BASE ≠ TFLG)
    (hBK : BASE ≠ KBIT)
    (hB : State.get u BASE = List.replicate start 1)
    (hbnd : (State.get u bound).length = bits.length)
    (hSC : State.get u SCAN = FlatCCBinFree.bitsNat bits)
    (hΩO : (State.get u OUT).length
        + (serF (BinaryCCToFSAT.encodeBitsAt start bits)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩs : start + bits.length ≤ Ω) :
    (emitBitsFromScan BASE bound).cost u
      ≤ (Cmd.flatK (bsBody 0) + 6) * ((Ω + 1) * (Ω + 1)) := by
  rw [emitBitsFromScan_eq, Cmd.cost_seq, emitFtrue_cost]
  have hloop := Cmd.cost_forBnd_le KBIT bound (bsBody BASE) u
    (Cmd.flatK (bsBody 0) * (Ω + 1))
    (fun i st => BSInv BASE start bits u i st ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨by rw [List.drop_zero]; exact hSC,
      by rw [List.take_zero]; simp [bitsPrefix], fun r _ _ _ _ _ => rfl⟩, hΩW⟩
    (fun i st hi hM => by
      obtain ⟨hInv, _⟩ := hM
      have hi' : i < bits.length := by rw [hbnd] at hi; exact hi
      refine ⟨BSInv_step BASE start bits u hBS hBO hBW hBT hBK hB i hi' st hInv, ?_⟩
      rw [bsBody_WREG BASE _ hBT hBS]
      have hstB : State.get st BASE = List.replicate start 1 := by
        rw [hInv.2.2 BASE hBS hBO hBW hBT hBK]; exact hB
      rw [State.get_set_ne _ _ _ _ hBK, State.get_set_eq, hstB]
      simp only [List.length_append, List.length_replicate]
      omega)
    (fun i st hi hM => by
      obtain ⟨⟨hSCANi, hOUTi, hframei⟩, hWl⟩ := hM
      have hi' : i < bits.length := by rw [hbnd] at hi; exact hi
      have hread : ∀ r ∈ Cmd.costReads (bsBody BASE),
          (State.get (st.set KBIT (List.replicate i 1)) r).length ≤ Ω := by
        intro r hr
        have hlist : Cmd.costReads (bsBody BASE)
            = [SCAN, BASE, KBIT, OUT, WREG, OUT, WREG] := rfl
        rw [hlist] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hS' : (State.get (st.set KBIT (List.replicate i 1)) SCAN).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show SCAN ≠ KBIT by decide), hSCANi]
          have hd : (FlatCCBinFree.bitsNat (bits.drop i)).length ≤ bits.length := by
            rw [show (FlatCCBinFree.bitsNat (bits.drop i)).length
                = (bits.drop i).length from List.length_map _]
            rw [List.length_drop]
            omega
          omega
        have hB' : (State.get (st.set KBIT (List.replicate i 1)) BASE).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ hBK,
            hframei BASE hBS hBO hBW hBT hBK, hB, List.length_replicate]
          omega
        have hK' : (State.get (st.set KBIT (List.replicate i 1)) KBIT).length ≤ Ω := by
          rw [State.get_set_eq, List.length_replicate]
          omega
        have hO' : (State.get (st.set KBIT (List.replicate i 1)) OUT).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show OUT ≠ KBIT by decide), hOUTi,
            List.length_append]
          have := bitsPrefix_take_length_le start bits i
          omega
        have hW' : (State.get (st.set KBIT (List.replicate i 1)) WREG).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show WREG ≠ KBIT by decide)]
          exact hWl
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hS', hB', hK', hO', hW', hO', hW']
      exact (Cmd.cost_le_flat (bsBody BASE) rfl
        (st.set KBIT (List.replicate i 1)) Ω hread).1)
  -- close the arithmetic
  have hlen : (State.get u bound).length ≤ Ω := by rw [hbnd]; omega
  set K := Cmd.flatK (bsBody 0) with hK
  set A := K * (Ω + 1) with hA
  set len := (State.get u bound).length with hlenDef
  have h1 : len * A ≤ (Ω + 1) * A := Nat.mul_le_mul_right A (by omega)
  have h2 : len * len ≤ Ω * Ω := Nat.mul_le_mul hlen hlen
  have h3 : (Ω + 1) * A = K * ((Ω + 1) * (Ω + 1)) := by rw [hA]; ring
  have h4 : (K + 6) * ((Ω + 1) * (Ω + 1))
      = K * ((Ω + 1) * (Ω + 1)) + 6 * ((Ω + 1) * (Ω + 1)) := by ring
  have h5 : (Ω + 1) * (Ω + 1) = Ω * Ω + 2 * Ω + 1 := by ring
  omega

/-! ### The sentinel-driven bit emitter: cost -/

/-- `sentBitBody` either leaves `WREG` alone or writes `BASE ++ counter`. -/
private theorem sentBitBody_WREG (BASE : Nat) (w : State)
    (hBT : BASE ≠ TFLG) (hBS : BASE ≠ SCAN) (hBE : BASE ≠ EMARK) :
    (State.get ((sentBitBody BASE).eval w) WREG).length
      ≤ max (State.get w WREG).length
          ((State.get w BASE).length + (State.get w KBIT).length) := by
  unfold sentBitBody
  by_cases hD : State.get w DONE = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hD, Cmd.eval_op]
    simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ (show WREG ≠ ZERO by decide)]
    exact Nat.le_max_left _ _
  · rw [Cmd.eval_ifBit_false _ _ _ _ hD, Cmd.eval_seq]
    set w1 := (Cmd.op (.head EMARK SCAN)).eval w with hw1
    have hw1f : ∀ r : Var, r ≠ EMARK → State.get w1 r = State.get w r := by
      intro r hr
      rw [hw1, Cmd.eval_op]
      exact Op.eval_get_ne_writesTo _ _ _ hr
    by_cases hE : State.get w1 EMARK = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hE]
      rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq,
        Cmd.eval_get_of_not_writes _ _ WREG (by decide), Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, Cmd.eval_op]
      rw [State.get_set_ne _ _ _ _ hBT, State.get_set_ne _ _ _ _ hBS,
        State.get_set_ne _ _ _ _ (show KBIT ≠ TFLG by decide),
        State.get_set_ne _ _ _ _ (show KBIT ≠ SCAN by decide),
        hw1f BASE hBE, hw1f KBIT (by decide)]
      rw [List.length_append]
      exact Nat.le_max_right _ _
    · rw [Cmd.eval_ifBit_false _ _ _ _ hE,
        Cmd.eval_get_of_not_writes _ _ WREG (by decide),
        hw1f WREG (by decide)]
      exact Nat.le_max_left _ _

/-- **`emitBitsFromSent` cost**: quadratic in the ceiling `Ω`. `Ω` must dominate
the entry `OUT` plus the full emission, the entry `WREG`, and
`start + |SCAN stream|`. -/
theorem emitBitsFromSent_cost (BASE start : Nat) (bits : List Bool) (rest : List Nat)
    (u : State) (Ω : Nat)
    (hBS : BASE ≠ SCAN) (hBO : BASE ≠ OUT) (hBW : BASE ≠ WREG) (hBT : BASE ≠ TFLG)
    (hBK : BASE ≠ KBIT) (hBD : BASE ≠ DONE) (hBE : BASE ≠ EMARK) (hBZ : BASE ≠ ZERO)
    (hB : State.get u BASE = List.replicate start 1)
    (hZ : State.get u ZERO = [])
    (hSC : State.get u SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest)
    (hΩO : (State.get u OUT).length
        + (serF (BinaryCCToFSAT.encodeBitsAt start bits)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩs : start + (State.get u SCAN).length ≤ Ω) :
    (emitBitsFromSent BASE).cost u
      ≤ (Cmd.flatK (sentBitBody 0) + 8) * ((Ω + 1) * (Ω + 1)) := by
  have heq : emitBitsFromSent BASE
      = (Cmd.op (.clear DONE) ;; (Cmd.forBnd KBIT SCAN (sentBitBody BASE) ;; emitFtrue)) := rfl
  rw [heq, Cmd.cost_seq, Cmd.cost_seq, emitFtrue_cost, Cmd.cost_op]
  simp only [Op.cost]
  have e0 : (Cmd.op (.clear DONE)).eval u = u.set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  rw [e0]
  set u1 := u.set DONE [] with hu1
  have hu1f : ∀ r : Var, r ≠ DONE → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1D : State.get u1 DONE = [] := State.get_set_eq _ _ _
  have hu1SC : State.get u1 SCAN
      = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest := by
    rw [hu1f SCAN (by decide)]; exact hSC
  have hu1SClen : (State.get u1 SCAN).length = (State.get u SCAN).length := by
    rw [hu1f SCAN (by decide)]
  clear_value u1
  have hsuffix : ∀ i : Nat,
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop i))).length + rest.length
        ≤ Ω := by
    intro i
    have h1 : (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop i))).length
        ≤ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length := by
      rw [show FlatCCBinFree.bitsNat (bits.drop i)
          = (FlatCCBinFree.bitsNat bits).drop i from List.map_drop ..]
      exact encSList_drop_length_le _ i
    have h2 : (State.get u SCAN).length
        = (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length + rest.length := by
      rw [hSC, List.length_append]
    omega
  have hloop := Cmd.cost_forBnd_le KBIT SCAN (sentBitBody BASE) u1
    (Cmd.flatK (sentBitBody 0) * (Ω + 1))
    (fun i st => SBInv BASE start bits rest u1 i st
      ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨fun _ => ⟨hu1D, by rw [List.drop_zero]; exact hu1SC,
        by rw [List.take_zero]; simp [bitsPrefix]⟩,
      fun h => absurd h (by omega),
      by rw [hu1f ZERO (by decide)]; exact hZ,
      fun r _ _ _ _ _ _ _ _ => rfl⟩,
      by rw [hu1f WREG (by decide)]; exact hΩW⟩
    (fun i st hi hM => by
      obtain ⟨hInv, hWprev⟩ := hM
      refine ⟨SBInv_step BASE start bits rest u1 hBS hBO hBW hBT hBK hBD hBE hBZ
        (by rw [hu1f BASE hBD]; exact hB) i st hInv, ?_⟩
      refine le_trans (sentBitBody_WREG BASE _ hBT hBS hBE) ?_
      have hstB : State.get st BASE = List.replicate start 1 := by
        rw [hInv.2.2.2 BASE hBS hBO hBW hBT hBK hBD hBE hBZ, hu1f BASE hBD]
        exact hB
      rw [State.get_set_ne _ _ _ _ hBK, State.get_set_eq, hstB, List.length_replicate,
        State.get_set_ne _ _ _ _ (show WREG ≠ KBIT by decide)]
      have hiΩ : i < (State.get u1 SCAN).length := hi
      simp only [List.length_replicate]
      rw [hu1SClen] at hiΩ
      omega)
    (fun i st hi hM => by
      obtain ⟨⟨hph1, hph2, hZERO, hframei⟩, hWl⟩ := hM
      have hread : ∀ r ∈ Cmd.costReads (sentBitBody BASE),
          (State.get (st.set KBIT (List.replicate i 1)) r).length ≤ Ω := by
        intro r hr
        have hlist : Cmd.costReads (sentBitBody BASE)
            = [SCAN, BASE, KBIT, OUT, WREG, OUT, WREG,
               SCAN, SCAN, SCAN, SCAN] := rfl
        rw [hlist] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hSCANce : (State.get st SCAN).length ≤ Ω := by
          by_cases hile : i ≤ bits.length
          · obtain ⟨_, hS, _⟩ := hph1 hile
            rw [hS, List.length_append]
            exact hsuffix i
          · obtain ⟨_, hS, _⟩ := hph2 (by omega)
            rw [hS]
            have := hsuffix 0
            omega
        have hOUTce : (State.get st OUT).length ≤ Ω := by
          by_cases hile : i ≤ bits.length
          · obtain ⟨_, _, hO⟩ := hph1 hile
            rw [hO, List.length_append, hu1f OUT (by decide)]
            have := bitsPrefix_take_length_le start bits i
            omega
          · obtain ⟨_, _, hO⟩ := hph2 (by omega)
            rw [hO, List.length_append, hu1f OUT (by decide)]
            have h1 := bitsPrefix_take_length_le start bits bits.length
            rw [List.take_length] at h1
            omega
        have hS' : (State.get (st.set KBIT (List.replicate i 1)) SCAN).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show SCAN ≠ KBIT by decide)]
          exact hSCANce
        have hB' : (State.get (st.set KBIT (List.replicate i 1)) BASE).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ hBK,
            hframei BASE hBS hBO hBW hBT hBK hBD hBE hBZ, hu1f BASE hBD, hB,
            List.length_replicate]
          omega
        have hK' : (State.get (st.set KBIT (List.replicate i 1)) KBIT).length ≤ Ω := by
          rw [State.get_set_eq, List.length_replicate]
          have hiΩ : i < (State.get u1 SCAN).length := hi
          rw [hu1SClen] at hiΩ
          omega
        have hO' : (State.get (st.set KBIT (List.replicate i 1)) OUT).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show OUT ≠ KBIT by decide)]
          exact hOUTce
        have hW' : (State.get (st.set KBIT (List.replicate i 1)) WREG).length ≤ Ω := by
          rw [State.get_set_ne _ _ _ _ (show WREG ≠ KBIT by decide)]
          exact hWl
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [hS', hB', hK', hO', hW', hO', hW', hS', hS', hS', hS']
      exact (Cmd.cost_le_flat (sentBitBody BASE) rfl
        (st.set KBIT (List.replicate i 1)) Ω hread).1)
  -- close the arithmetic
  have hlen : (State.get u1 SCAN).length ≤ Ω := by rw [hu1SClen]; omega
  set K := Cmd.flatK (sentBitBody 0) with hK
  set A := K * (Ω + 1) with hA
  set len := (State.get u1 SCAN).length with hlenDef
  have h1 : len * A ≤ (Ω + 1) * A := Nat.mul_le_mul_right A (by omega)
  have h2 : len * len ≤ Ω * Ω := Nat.mul_le_mul hlen hlen
  have h3 : (Ω + 1) * A = K * ((Ω + 1) * (Ω + 1)) := by rw [hA]; ring
  have h4 : (K + 8) * ((Ω + 1) * (Ω + 1))
      = K * ((Ω + 1) * (Ω + 1)) + 8 * ((Ω + 1) * (Ω + 1)) := by ring
  have h5 : (Ω + 1) * (Ω + 1) = Ω * Ω + 2 * Ω + 1 := by ring
  omega

/-! ### The final-string parse: cost -/

/-- **`readOneFinal` cost**: quadratic in the ceiling `Ω ≥ |SCANF|`. -/
theorem readOneFinal_cost (bits : List Bool) (rest : List Nat) (u : State) (Ω : Nat)
    (hSC : State.get u SCANF
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest)
    (hΩS : (State.get u SCANF).length ≤ Ω) :
    readOneFinal.cost u
      ≤ (Cmd.flatK readFinBody + 10) * ((Ω + 1) * (Ω + 1)) := by
  have heq : readOneFinal
      = (Cmd.op (.clear FBITS) ;; (Cmd.op (.clear BLEN) ;; (Cmd.op (.clear DONE) ;;
        Cmd.forBnd KTMP SCANF readFinBody))) := rfl
  rw [heq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op,
    Cmd.cost_op]
  simp only [Op.cost]
  have e1 : (Cmd.op (.clear FBITS)).eval u = u.set FBITS [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e2 : (Cmd.op (.clear BLEN)).eval (u.set FBITS [])
      = (u.set FBITS []).set BLEN [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e3 : (Cmd.op (.clear DONE)).eval ((u.set FBITS []).set BLEN [])
      = ((u.set FBITS []).set BLEN []).set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  rw [e1, e2, e3]
  have hu3f : ∀ r : Var, r ≠ FBITS → r ≠ BLEN → r ≠ DONE →
      State.get (((u.set FBITS []).set BLEN []).set DONE []) r = State.get u r := by
    intro r h1 h2 h3
    rw [State.get_set_ne _ _ _ _ h3, State.get_set_ne _ _ _ _ h2,
      State.get_set_ne _ _ _ _ h1]
  set u3 := ((u.set FBITS []).set BLEN []).set DONE [] with hu3
  have hu3D : State.get u3 DONE = [] := State.get_set_eq _ _ _
  have hu3B : State.get u3 BLEN = [] := by
    rw [hu3, State.get_set_ne _ _ _ _ (show BLEN ≠ DONE by decide), State.get_set_eq]
  have hu3F : State.get u3 FBITS = [] := by
    rw [hu3, State.get_set_ne _ _ _ _ (show FBITS ≠ DONE by decide),
      State.get_set_ne _ _ _ _ (show FBITS ≠ BLEN by decide), State.get_set_eq]
  have hu3SC : State.get u3 SCANF
      = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ rest := by
    rw [hu3]
    rw [hu3f SCANF (by decide) (by decide) (by decide)]
    exact hSC
  have hu3SClen : (State.get u3 SCANF).length = (State.get u SCANF).length := by
    rw [hu3SC, hSC]
  clear_value u3
  have hsuffix : ∀ i : Nat,
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop i))).length + rest.length
        ≤ Ω := by
    intro i
    have h1 : (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bits.drop i))).length
        ≤ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length := by
      rw [show FlatCCBinFree.bitsNat (bits.drop i)
          = (FlatCCBinFree.bitsNat bits).drop i from List.map_drop ..]
      exact encSList_drop_length_le _ i
    have h2 : (State.get u SCANF).length
        = (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length + rest.length := by
      rw [hSC, List.length_append]
    omega
  have hbase : RFInv bits rest u3 0 u3 :=
    ⟨fun _ => ⟨hu3D, by rw [List.drop_zero]; exact hu3SC,
        by rw [List.take_zero]; exact hu3F,
        by rw [List.replicate_zero]; exact hu3B⟩,
      fun h => absurd h (by omega),
      fun r _ _ _ _ _ _ _ _ => rfl⟩
  have hloop := Cmd.cost_forBnd_le KTMP SCANF readFinBody u3
    (Cmd.flatK readFinBody * (Ω + 1))
    (RFInv bits rest u3) hbase
    (fun i st _ hM => RFInv_step bits rest u3 i st hM)
    (fun i st hi hM => by
      obtain ⟨hph1, hph2, hframei⟩ := hM
      have hread : ∀ r ∈ Cmd.costReads readFinBody,
          (State.get (st.set KTMP (List.replicate i 1)) r).length ≤ Ω := by
        intro r hr
        have hlist : Cmd.costReads readFinBody
            = [SCANF, SCANF, SCANF, SCANF, SCANF] := rfl
        rw [hlist] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hSCANce : (State.get st SCANF).length ≤ Ω := by
          by_cases hile : i ≤ bits.length
          · obtain ⟨_, hS, _⟩ := hph1 hile
            rw [hS, List.length_append]
            exact hsuffix i
          · obtain ⟨_, hS, _⟩ := hph2 (by omega)
            rw [hS]
            have := hsuffix 0
            omega
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          (rw [State.get_set_ne _ _ _ _ (show SCANF ≠ KTMP by decide)]; exact hSCANce)
      exact (Cmd.cost_le_flat readFinBody rfl
        (st.set KTMP (List.replicate i 1)) Ω hread).1)
  -- close the arithmetic
  have hlen : (State.get u3 SCANF).length ≤ Ω := by rw [hu3SClen]; omega
  set K := Cmd.flatK readFinBody with hK
  set A := K * (Ω + 1) with hA
  set len := (State.get u3 SCANF).length with hlenDef
  have h1 : len * A ≤ (Ω + 1) * A := Nat.mul_le_mul_right A (by omega)
  have h2 : len * len ≤ Ω * Ω := Nat.mul_le_mul hlen hlen
  have h3 : (Ω + 1) * A = K * ((Ω + 1) * (Ω + 1)) := by rw [hA]; ring
  have h4 : (K + 10) * ((Ω + 1) * (Ω + 1))
      = K * ((Ω + 1) * (Ω + 1)) + 10 * ((Ω + 1) * (Ω + 1)) := by ring
  have h5 : (Ω + 1) * (Ω + 1) = Ω * Ω + 2 * Ω + 1 := by ring
  omega


/-! ### `emitCardsAt`: cost -/

/-- `emitBitsFromSent` never grows `WREG` beyond `max(entry, start + |SCAN|)`
(each loop write is `BASE ++ counter`). Membership hypothesis dischargeable by
`decide` at concrete `BASE`. -/
private theorem emitBitsFromSent_WREG (BASE : Nat) (u : State) (W : Nat)
    (hBT : BASE ≠ TFLG) (hBS : BASE ≠ SCAN) (hBE : BASE ≠ EMARK) (hBK : BASE ≠ KBIT)
    (hBD : BASE ≠ DONE)
    (hBmem : BASE ∉ Cmd.writes (sentBitBody BASE))
    (hW : (State.get u WREG).length ≤ W)
    (hBSc : (State.get u BASE).length + (State.get u SCAN).length ≤ W) :
    (State.get ((emitBitsFromSent BASE).eval u) WREG).length ≤ W := by
  have heq : emitBitsFromSent BASE
      = (Cmd.op (.clear DONE) ;;
          (Cmd.forBnd KBIT SCAN (sentBitBody BASE) ;; emitFtrue)) := rfl
  rw [heq, Cmd.eval_seq, Cmd.eval_seq, emitFtrue_frame _ WREG (by decide)]
  have e0 : (Cmd.op (.clear DONE)).eval u = u.set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  rw [e0]
  set u1 := u.set DONE [] with hu1
  have hu1W : (State.get u1 WREG).length ≤ W := by
    rw [hu1, State.get_set_ne _ _ _ _ (show WREG ≠ DONE by decide)]; exact hW
  have hu1B : State.get u1 BASE = State.get u BASE := by
    rw [hu1, State.get_set_ne _ _ _ _ hBD]
  have hu1SC : State.get u1 SCAN = State.get u SCAN := by
    rw [hu1, State.get_set_ne _ _ _ _ (show SCAN ≠ DONE by decide)]
  clear_value u1
  rw [Cmd.eval_forBnd]
  have hInv := Cmd.foldlState_range_induct (sentBitBody BASE) KBIT
    (State.get u1 SCAN).length u1
    (fun _ st => (State.get st WREG).length ≤ W
      ∧ State.get st BASE = State.get u1 BASE)
    ⟨hu1W, rfl⟩
    (fun i st hi hM => by
      obtain ⟨hWl, hBf⟩ := hM
      constructor
      · refine le_trans (sentBitBody_WREG BASE _ hBT hBS hBE) ?_
        rw [State.get_set_ne _ _ _ _ (show WREG ≠ KBIT by decide),
          State.get_set_ne _ _ _ _ hBK, State.get_set_eq, hBf, hu1B,
          List.length_replicate]
        have hilt : i < (State.get u1 SCAN).length := hi
        rw [hu1SC] at hilt
        exact Nat.max_le.mpr ⟨hWl, by omega⟩
      · rw [Cmd.eval_get_of_not_writes _ _ BASE hBmem,
          State.get_set_ne _ _ _ _ hBK]
        exact hBf)
  exact hInv.1

/-- Per-iteration effect of the card loop: cost bound + `WREG` stays `≤ Ω`. -/
private theorem cardEmitBody_effect (sA sB : Nat) (C : BinaryCC) (u1 : State) (Ω : Nat)
    (hSA1 : State.get u1 STARTA = List.replicate sA 1)
    (hSB1 : State.get u1 STARTB = List.replicate sB 1)
    (hΩO : (State.get u1 OUT).length + (serF (encodeCardsAt C sA sB)).length ≤ Ω)
    (hΩA : sA + (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length ≤ Ω)
    (hΩB : sB + (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length ≤ Ω)
    (j : Nat) (st : State)
    (hInv : CAInv sA sB C.cards u1 j st)
    (hW : (State.get st WREG).length ≤ Ω) :
    cardEmitBody.cost (st.set KCARD (List.replicate j 1))
        ≤ 12 + 2 * ((Cmd.flatK (sentBitBody 0) + 8) * ((Ω + 1) * (Ω + 1)))
    ∧ (State.get (cardEmitBody.eval (st.set KCARD (List.replicate j 1))) WREG).length
        ≤ Ω := by
  obtain ⟨hSCAN, hOUT, hZERO, hframe⟩ := hInv
  set w := st.set KCARD (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KCARD → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSCAN : State.get w SCAN
      = FlatTCCFree.encCardsOut ((C.cards.drop j).map FlatCCBinFree.cardNat) := by
    rw [hwframe SCAN (by decide)]; exact hSCAN
  have hwOUT : State.get w OUT
      = State.get u1 OUT ++ cardsPrefix sA sB (C.cards.take j) := by
    rw [hwframe OUT (by decide)]; exact hOUT
  have hwZ : State.get w ZERO = [] := by
    rw [hwframe ZERO (by decide)]; exact hZERO
  have hwSA : State.get w STARTA = List.replicate sA 1 := by
    rw [hwframe STARTA (by decide), hframe STARTA (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hSA1
  have hwSB : State.get w STARTB = List.replicate sB 1 := by
    rw [hwframe STARTB (by decide), hframe STARTB (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hSB1
  have hwW : (State.get w WREG).length ≤ Ω := by
    rw [hwframe WREG (by decide)]; exact hW
  -- the drop-stream ceiling
  have hstream : (FlatTCCFree.encCardsOut ((C.cards.drop j).map FlatCCBinFree.cardNat)).length
      ≤ (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length := by
    rw [show (C.cards.drop j).map FlatCCBinFree.cardNat
        = (C.cards.map FlatCCBinFree.cardNat).drop j from List.map_drop ..]
    exact encCardsOut_drop_length_le _ j
  clear_value w
  by_cases hj : j < C.cards.length
  · -- live iteration
    have hdrop : C.cards.drop j = C.cards[j] :: C.cards.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    have htake : C.cards.take (j + 1) = C.cards.take j ++ [C.cards[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    set c := C.cards[j] with hc
    clear_value c
    set REST := FlatTCCFree.encCardsOut ((C.cards.drop (j + 1)).map FlatCCBinFree.cardNat)
      with hREST
    have hSCANw : State.get w SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
          ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hwSCAN, hdrop, encCardsOut_cons, hREST]
    have hne : (State.get w SCAN).isEmpty = false := by
      rw [hSCANw]; exact encSList_append_isEmpty _ _
    have e1 : (Cmd.op (.nonEmpty TFLG SCAN)).eval w = w.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w1 := w.set TFLG [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ TFLG → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1T : State.get w1 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w1
    set w2 := emitForrTag.eval w1 with hw2
    have hw2frame : ∀ r : Var, r ≠ OUT → State.get w2 r = State.get w1 r := by
      intro r hr; rw [hw2]; exact emitForrTag_frame w1 r hr
    have hw2OUT : State.get w2 OUT = State.get w1 OUT ++ [1, 0] := by
      rw [hw2, emitForrTag_run]; exact State.get_set_eq _ _ _
    clear_value w2
    set w3 := emitFandTag.eval w2 with hw3
    have hw3frame : ∀ r : Var, r ≠ OUT → State.get w3 r = State.get w2 r := by
      intro r hr; rw [hw3]; exact emitFandTag_frame w2 r hr
    have hw3OUT : State.get w3 OUT = State.get w2 OUT ++ [0, 1] := by
      rw [hw3, emitFandTag_run]; exact State.get_set_eq _ _ _
    clear_value w3
    have hchain : ∀ r : Var, r ≠ OUT → r ≠ TFLG → State.get w3 r = State.get w r := by
      intro r h1 h2
      rw [hw3frame r h1, hw2frame r h1, hw1frame r h2]
    have hw3SCAN : State.get w3 SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
          ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hchain SCAN (by decide) (by decide)]; exact hSCANw
    have hw3Z : State.get w3 ZERO = [] := by
      rw [hchain ZERO (by decide) (by decide)]; exact hwZ
    have hw3SA : State.get w3 STARTA = List.replicate sA 1 := by
      rw [hchain STARTA (by decide) (by decide)]; exact hwSA
    have hw3SB : State.get w3 STARTB = List.replicate sB 1 := by
      rw [hchain STARTB (by decide) (by decide)]; exact hwSB
    have hw3W : (State.get w3 WREG).length ≤ Ω := by
      rw [hchain WREG (by decide) (by decide)]; exact hwW
    have hw3OUTfull : State.get w3 OUT
        = State.get u1 OUT ++ cardsPrefix sA sB (C.cards.take j) ++ [1, 0] ++ [0, 1] := by
      rw [hw3OUT, hw2OUT, hw1frame OUT (by decide), hwOUT]
    -- OUT/prefix bookkeeping
    have hexp : cardsPrefix sA sB (C.cards.take (j + 1))
        = cardsPrefix sA sB (C.cards.take j)
          ++ ([1, 0] ++ ([0, 1] ++ (serF (encodeBitsAt sA c.prem)
              ++ serF (encodeBitsAt sB c.conc)))) := by
      rw [htake, cardsPrefix_append]
      simp [cardsPrefix, encodeCardAt, serF, List.append_assoc]
    have hcpj1 : (cardsPrefix sA sB (C.cards.take (j + 1))).length
        ≤ (serF (encodeCardsAt C sA sB)).length :=
      cardsPrefix_take_length_le sA sB C.cards (j + 1)
    have hlenexp : (cardsPrefix sA sB (C.cards.take (j + 1))).length
        = (cardsPrefix sA sB (C.cards.take j)).length + 4
          + (serF (encodeBitsAt sA c.prem)).length
          + (serF (encodeBitsAt sB c.conc)).length := by
      rw [hexp]
      simp [List.length_append]
      omega
    -- the SCAN ceilings
    have hw3SCANlen : (State.get w3 SCAN).length
        ≤ (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length := by
      rw [hw3SCAN, hREST, ← encCardsOut_cons, ← hdrop]
      exact hstream
    -- the prem emitter: cost + run facts
    have hcostA := emitBitsFromSent_cost STARTA sA c.prem
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) w3 Ω
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hw3SA hw3Z hw3SCAN
      (by rw [hw3OUTfull]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)
      hw3W
      (by rw [hw3SCAN] at hw3SCANlen ⊢
          omega)
    obtain ⟨h4SCAN, h4OUT, h4Z, h4frame⟩ :=
      emitBitsFromSent_run STARTA sA c.prem
        (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) w3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) hw3SA hw3Z hw3SCAN
    have hWREG4 : (State.get ((emitBitsFromSent STARTA).eval w3) WREG).length ≤ Ω :=
      emitBitsFromSent_WREG STARTA w3 Ω (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hw3W
        (by rw [hw3SA, List.length_replicate, hw3SCAN] at *
            rw [hw3SCAN] at hw3SCANlen
            omega)
    set w4 := (emitBitsFromSent STARTA).eval w3 with hw4
    have hw4SB : State.get w4 STARTB = List.replicate sB 1 := by
      rw [hw4, h4frame STARTB (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
      exact hw3SB
    have hw4SCAN : State.get w4 SCAN
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST := by
      rw [hw4]; exact h4SCAN
    have hw4Z : State.get w4 ZERO = [] := by rw [hw4]; exact h4Z
    have hw4OUT : State.get w4 OUT
        = State.get w3 OUT ++ serF (encodeBitsAt sA c.prem) := by
      rw [hw4]; exact h4OUT
    have hw4W : (State.get w4 WREG).length ≤ Ω := by rw [hw4]; exact hWREG4
    have hw4SCANlen : (State.get w4 SCAN).length
        ≤ (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length := by
      rw [hw4SCAN]
      have : (State.get w3 SCAN).length
          = (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)).length
            + (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST).length := by
        rw [hw3SCAN, List.length_append]
      omega
    clear_value w4
    -- the conc emitter: cost
    have hcostB := emitBitsFromSent_cost STARTB sB c.conc REST w4 Ω
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hw4SB hw4Z hw4SCAN
      (by rw [hw4OUT, hw3OUTfull]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)
      hw4W
      (by rw [hw4SCAN] at hw4SCANlen ⊢
          omega)
    -- WREG at exit
    have hWREG5 : (State.get ((emitBitsFromSent STARTB).eval w4) WREG).length ≤ Ω :=
      emitBitsFromSent_WREG STARTB w4 Ω (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hw4W
        (by rw [hw4SB, List.length_replicate]
            rw [hw4SCAN] at hw4SCANlen
            rw [hw4SCAN]
            omega)
    -- assemble cost and eval
    have hcost : cardEmitBody.cost w
        = 1 + 1 + (1 + (1 + 3 + (1 + 3 + (1 + (emitBitsFromSent STARTA).cost w3
            + (emitBitsFromSent STARTB).cost w4)))) := by
      show (Cmd.op (.nonEmpty TFLG SCAN) ;; _).cost w = _
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_true _ _ _ _ hw1T,
        Cmd.cost_seq, emitForrTag_cost, ← hw2, Cmd.cost_seq, emitFandTag_cost,
        ← hw3, Cmd.cost_seq, ← hw4]
      simp only [Op.cost]
    have heval : cardEmitBody.eval w = (emitBitsFromSent STARTB).eval w4 := by
      unfold cardEmitBody
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_true _ _ _ _ hw1T, Cmd.eval_seq, ← hw2,
        Cmd.eval_seq, ← hw3, Cmd.eval_seq, ← hw4]
    constructor
    · rw [hcost]
      set KK := (Cmd.flatK (sentBitBody 0) + 8) * ((Ω + 1) * (Ω + 1)) with hKK
      clear_value KK
      omega
    · rw [heval]
      exact hWREG5
  · -- idle iteration
    have hlen : C.cards.length ≤ j := Nat.le_of_not_lt hj
    have hSCANw : State.get w SCAN = [] := by
      rw [hwSCAN, List.drop_eq_nil_of_le hlen]
      rfl
    have hne : (State.get w SCAN).isEmpty = true := by rw [hSCANw]; rfl
    have e1 : (Cmd.op (.nonEmpty TFLG SCAN)).eval w = w.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    have hw1T : State.get (w.set TFLG [0]) TFLG ≠ [1] := by
      rw [State.get_set_eq]; decide
    constructor
    · have hcost : cardEmitBody.cost w = 1 + 1 + (1 + 1) := by
        show (Cmd.op (.nonEmpty TFLG SCAN) ;; _).cost w = _
        rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_false _ _ _ _ hw1T,
          Cmd.cost_op]
        simp only [Op.cost]
      rw [hcost]
      omega
    · have heval : cardEmitBody.eval w = (w.set TFLG [0]).set KTMP [] := by
        unfold cardEmitBody
        rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_false _ _ _ _ hw1T, Cmd.eval_op]
        simp only [Op.eval]
      rw [heval, State.get_set_ne _ _ _ _ (show WREG ≠ KTMP by decide),
        State.get_set_ne _ _ _ _ (show WREG ≠ TFLG by decide)]
      exact hwW

/-- **`emitCardsAt` cost**: cubic in the ceiling `Ω`. -/
theorem emitCardsAt_cost (sA sB : Nat) (C : BinaryCC) (u : State) (Ω : Nat)
    (hSA : State.get u STARTA = List.replicate sA 1)
    (hSB : State.get u STARTB = List.replicate sB 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length + (serF (encodeCardsAt C sA sB)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩA : sA + (State.get u CARDS).length ≤ Ω)
    (hΩB : sB + (State.get u CARDS).length ≤ Ω) :
    emitCardsAt.cost u
      ≤ (2 * Cmd.flatK (sentBitBody 0) + 44)
          * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) := by
  have heq : emitCardsAt = (Cmd.op (.copy SCAN CARDS) ;;
      (Cmd.forBnd KCARD CARDS cardEmitBody ;; emitFalse)) := rfl
  rw [heq, Cmd.cost_seq, Cmd.cost_seq, emitFalse_cost, Cmd.cost_op]
  simp only [Op.cost]
  have e0 : (Cmd.op (.copy SCAN CARDS)).eval u
      = u.set SCAN (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hCARDS]
  rw [e0]
  set u1 := u.set SCAN (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    with hu1
  have hu1f : ∀ r : Var, r ≠ SCAN → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1SC : State.get u1 SCAN
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    State.get_set_eq _ _ _
  have hu1CARDSlen : (State.get u1 CARDS).length = (State.get u CARDS).length := by
    rw [hu1f CARDS (by decide)]
  clear_value u1
  have hcards_le : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length
      = (State.get u CARDS).length := by rw [hCARDS]
  have hloop := Cmd.cost_forBnd_le KCARD CARDS cardEmitBody u1
    (12 + 2 * ((Cmd.flatK (sentBitBody 0) + 8) * ((Ω + 1) * (Ω + 1))))
    (fun j st => CAInv sA sB C.cards u1 j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨by rw [List.drop_zero]; exact hu1SC,
      by rw [List.take_zero]; simp [cardsPrefix],
      by rw [hu1f ZERO (by decide)]; exact hZ,
      fun r _ _ _ _ _ _ _ _ _ _ => rfl⟩,
      by rw [hu1f WREG (by decide)]; exact hΩW⟩
    (fun j st hj hM => by
      refine ⟨CAInv_step sA sB C.cards u1
        (by rw [hu1f STARTA (by decide)]; exact hSA)
        (by rw [hu1f STARTB (by decide)]; exact hSB) j st hM.1, ?_⟩
      exact (cardEmitBody_effect sA sB C u1 Ω
        (by rw [hu1f STARTA (by decide)]; exact hSA)
        (by rw [hu1f STARTB (by decide)]; exact hSB)
        (by rw [hu1f OUT (by decide)]; exact hΩO)
        (by rw [← hcards_le] at hΩA; exact hΩA)
        (by rw [← hcards_le] at hΩB; exact hΩB)
        j st hM.1 hM.2).2)
    (fun j st hj hM =>
      (cardEmitBody_effect sA sB C u1 Ω
        (by rw [hu1f STARTA (by decide)]; exact hSA)
        (by rw [hu1f STARTB (by decide)]; exact hSB)
        (by rw [hu1f OUT (by decide)]; exact hΩO)
        (by rw [← hcards_le] at hΩA; exact hΩA)
        (by rw [← hcards_le] at hΩB; exact hΩB)
        j st hM.1 hM.2).1)
  -- close the arithmetic
  have hΩcards : (State.get u CARDS).length ≤ Ω := by omega
  set K := Cmd.flatK (sentBitBody 0) with hK
  set len := (State.get u1 CARDS).length with hlenDef
  have hlenΩ : len ≤ Ω := by omega
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  set B := 12 + 2 * ((K + 8) * P2) with hB
  have hBle : B ≤ (2 * K + 28) * P2 := by
    rw [hB]
    have h12 : 12 ≤ 12 * P2 := by
      have : 1 ≤ P2 := by rw [hP2]; nlinarith
      omega
    have hexp2 : 2 * ((K + 8) * P2) + 12 * P2 = (2 * K + 28) * P2 := by ring
    omega
  have hlB : len * B ≤ (Ω + 1) * ((2 * K + 28) * P2) :=
    Nat.mul_le_mul (by omega) hBle
  have h3 : (Ω + 1) * ((2 * K + 28) * P2) = (2 * K + 28) * ((Ω + 1) * P2) := by ring
  have h2 : len * len ≤ Ω * Ω := Nat.mul_le_mul hlenΩ hlenΩ
  have h4 : (2 * K + 44) * ((Ω + 1) * P2)
      = (2 * K + 28) * ((Ω + 1) * P2) + 16 * ((Ω + 1) * P2) := by ring
  have h5 : (Ω + 1) * P2 = Ω * Ω * Ω + 3 * (Ω * Ω) + 3 * Ω + 1 := by
    rw [hP2]; ring
  have h6 : Ω * Ω * Ω + 3 * (Ω * Ω) + 3 * Ω + 1 ≥ Ω * Ω + Ω + 1 := by nlinarith
  have hcopy : (State.get u CARDS).length + 1 ≤ Ω + 1 := by omega
  omega

/-! ### `stepBody`: cost -/

private theorem one_le_P (Ω : Nat) : 1 ≤ (Ω + 1) * (Ω + 1) :=
  Nat.mul_pos (Nat.succ_pos Ω) (Nat.succ_pos Ω)

private theorem le_scale (Ω x : Nat) : x ≤ (Ω + 1) * x :=
  Nat.le_mul_of_pos_left x (Nat.succ_pos Ω)

private theorem mulLoopClose (k m Ω : Nat) (hk : k ≤ Ω) (hm : m ≤ Ω) (hmk : m * k ≤ Ω) :
    1 + m * (2 * (0 + m * k + k) + 1) + m * m ≤ 7 * ((Ω + 1) * (Ω + 1)) := by
  nlinarith

private theorem subLoopClose (a m Ω : Nat) (ha : a ≤ Ω) (hm : m ≤ Ω) :
    1 + m * (a + 1) + m * m ≤ 3 * ((Ω + 1) * (Ω + 1)) := by
  nlinarith

/-- `emitCardsAt` keeps `WREG ≤ Ω` (loop-exit version of the per-iteration
clause in `cardEmitBody_effect`). -/
private theorem emitCardsAt_WREG (sA sB : Nat) (C : BinaryCC) (u : State) (Ω : Nat)
    (hSA : State.get u STARTA = List.replicate sA 1)
    (hSB : State.get u STARTB = List.replicate sB 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length + (serF (encodeCardsAt C sA sB)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩA : sA + (State.get u CARDS).length ≤ Ω)
    (hΩB : sB + (State.get u CARDS).length ≤ Ω) :
    (State.get (emitCardsAt.eval u) WREG).length ≤ Ω := by
  have heq : emitCardsAt = (Cmd.op (.copy SCAN CARDS) ;;
      (Cmd.forBnd KCARD CARDS cardEmitBody ;; emitFalse)) := rfl
  rw [heq, Cmd.eval_seq, Cmd.eval_seq, emitFalse_frame _ WREG (by decide)]
  have e0 : (Cmd.op (.copy SCAN CARDS)).eval u
      = u.set SCAN (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hCARDS]
  rw [e0]
  set u1 := u.set SCAN (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    with hu1
  have hu1f : ∀ r : Var, r ≠ SCAN → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1SC : State.get u1 SCAN
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    State.get_set_eq _ _ _
  have hcards_le : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length
      = (State.get u CARDS).length := by rw [hCARDS]
  clear_value u1
  rw [Cmd.eval_forBnd]
  have hInv := Cmd.foldlState_range_induct cardEmitBody KCARD
    (State.get u1 CARDS).length u1
    (fun j st => CAInv sA sB C.cards u1 j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨by rw [List.drop_zero]; exact hu1SC,
      by rw [List.take_zero]; simp [cardsPrefix],
      by rw [hu1f ZERO (by decide)]; exact hZ,
      fun r _ _ _ _ _ _ _ _ _ _ => rfl⟩,
      by rw [hu1f WREG (by decide)]; exact hΩW⟩
    (fun j st hj hM => by
      refine ⟨CAInv_step sA sB C.cards u1
        (by rw [hu1f STARTA (by decide)]; exact hSA)
        (by rw [hu1f STARTB (by decide)]; exact hSB) j st hM.1, ?_⟩
      exact (cardEmitBody_effect sA sB C u1 Ω
        (by rw [hu1f STARTA (by decide)]; exact hSA)
        (by rw [hu1f STARTB (by decide)]; exact hSB)
        (by rw [hu1f OUT (by decide)]; exact hΩO)
        (by rw [← hcards_le] at hΩA; exact hΩA)
        (by rw [← hcards_le] at hΩB; exact hΩB)
        j st hM.1 hM.2).2)
  exact hInv.2

/-- **`stepBody` cost**: cubic in the ceiling `Ω`, plus the `WREG ≤ Ω` exit
fact the enclosing loop needs. -/
theorem stepBody_cost (C : BinaryCC) (line step : Nat) (u : State) (Ω : Nat)
    (hLINEL : State.get u LINEL = List.replicate (line * C.init.length) 1)
    (hKSTEP : State.get u KSTEP = List.replicate step 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hWID : State.get u WIDTH = List.replicate C.width 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length
        + (serF (encodeStepConstraint C line step)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩidx : (line + 1) * C.init.length + step * C.offset + step + C.offset
        + C.width + C.init.length + (State.get u CARDS).length ≤ Ω) :
    stepBody.cost u
        ≤ (2 * Cmd.flatK (sentBitBody 0) + 100) * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))
    ∧ (State.get (stepBody.eval u) WREG).length ≤ Ω := by
  -- index arithmetic, upfront
  have hsucc : (line + 1) * C.init.length
      = line * C.init.length + C.init.length := by ring
  have hlineL : line * C.init.length + step * C.offset ≤ Ω := by
    rw [hsucc] at hΩidx; omega
  -- w1: clear STEPO
  have e1 : (Cmd.op (.clear STEPO)).eval u = u.set STEPO [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w1 := u.set STEPO [] with hw1
  have hw1frame : ∀ r : Var, r ≠ STEPO → State.get w1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1STEPO : State.get w1 STEPO = [] := State.get_set_eq _ _ _
  have hw1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hw1frame OFFSET (by decide)]; exact hOFF
  have hw1KSTEPlen : (State.get w1 KSTEP).length = step := by
    rw [hw1frame KSTEP (by decide), hKSTEP, List.length_replicate]
  clear_value w1
  -- w2: the STEPO mul loop (run + cost)
  have hcMul := cost_mulLoop_le KTMP KSTEP STEPO OFFSET w1 0 C.offset step
    (by decide) (by decide) (by decide)
    (by rw [hw1STEPO]; exact Nat.le_refl 0)
    (by rw [hw1OFF, List.length_replicate])
    hw1KSTEPlen
  obtain ⟨h2STEPO, h2frame⟩ :=
    unaryMulLoop_run KTMP KSTEP OFFSET STEPO w1 C.offset step
      (by decide) (by decide) (by decide) hw1OFF hw1KSTEPlen hw1STEPO
  set w2 := (Cmd.forBnd KTMP KSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).eval w1
    with hw2
  clear_value w2
  have hw2LINEL : State.get w2 LINEL = List.replicate (line * C.init.length) 1 := by
    rw [h2frame LINEL (by decide) (by decide), hw1frame LINEL (by decide)]
    exact hLINEL
  -- w3: STARTA := LINEL ++ STEPO
  have e3 : (Cmd.op (.concat STARTA LINEL STEPO)).eval w2
      = w2.set STARTA (List.replicate (line * C.init.length + step * C.offset) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hw2LINEL, h2STEPO]
    congr 1
    rw [List.replicate_add]
  have hc3 : Op.cost (.concat STARTA LINEL STEPO) w2
      = 2 * (line * C.init.length + step * C.offset) + 1 := by
    show 2 * ((State.get w2 LINEL).length + (State.get w2 STEPO).length) + 1 = _
    rw [hw2LINEL, h2STEPO, List.length_replicate, List.length_replicate]
  set w3 := w2.set STARTA (List.replicate (line * C.init.length + step * C.offset) 1)
    with hw3
  have hw3frame : ∀ r : Var, r ≠ STARTA → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3SA : State.get w3 STARTA
      = List.replicate (line * C.init.length + step * C.offset) 1 :=
    State.get_set_eq _ _ _
  have hw3LREG : State.get w3 LREG = List.replicate C.init.length 1 := by
    rw [hw3frame LREG (by decide), h2frame LREG (by decide) (by decide),
      hw1frame LREG (by decide)]
    exact hLREG
  clear_value w3
  -- w4: STARTB := STARTA ++ LREG
  have e4 : (Cmd.op (.concat STARTB STARTA LREG)).eval w3
      = w3.set STARTB (List.replicate
          (line * C.init.length + step * C.offset + C.init.length) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hw3SA, hw3LREG]
    congr 1
    rw [← List.replicate_add]
  have hc4 : Op.cost (.concat STARTB STARTA LREG) w3
      = 2 * (line * C.init.length + step * C.offset + C.init.length) + 1 := by
    show 2 * ((State.get w3 STARTA).length + (State.get w3 LREG).length) + 1 = _
    rw [hw3SA, hw3LREG, List.length_replicate, List.length_replicate]
  set w4 := w3.set STARTB (List.replicate
      (line * C.init.length + step * C.offset + C.init.length) 1) with hw4
  have hw4frame : ∀ r : Var, r ≠ STARTB → State.get w4 r = State.get w3 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw4SB : State.get w4 STARTB
      = List.replicate (line * C.init.length + step * C.offset + C.init.length) 1 :=
    State.get_set_eq _ _ _
  have hw4STEPO : State.get w4 STEPO = List.replicate (step * C.offset) 1 := by
    rw [hw4frame STEPO (by decide), hw3frame STEPO (by decide)]; exact h2STEPO
  have hw4WID : State.get w4 WIDTH = List.replicate C.width 1 := by
    rw [hw4frame WIDTH (by decide), hw3frame WIDTH (by decide),
      h2frame WIDTH (by decide) (by decide), hw1frame WIDTH (by decide)]
    exact hWID
  clear_value w4
  -- w5: SUMW := STEPO ++ WIDTH
  have e5 : (Cmd.op (.concat SUMW STEPO WIDTH)).eval w4
      = w4.set SUMW (List.replicate (step * C.offset + C.width) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hw4STEPO, hw4WID]
    congr 1
    rw [List.replicate_add]
  have hc5 : Op.cost (.concat SUMW STEPO WIDTH) w4
      = 2 * (step * C.offset + C.width) + 1 := by
    show 2 * ((State.get w4 STEPO).length + (State.get w4 WIDTH).length) + 1 = _
    rw [hw4STEPO, hw4WID, List.length_replicate, List.length_replicate]
  set w5 := w4.set SUMW (List.replicate (step * C.offset + C.width) 1) with hw5
  have hw5frame : ∀ r : Var, r ≠ SUMW → State.get w5 r = State.get w4 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw5SUMW : State.get w5 SUMW = List.replicate (step * C.offset + C.width) 1 :=
    State.get_set_eq _ _ _
  clear_value w5
  -- w6: REM := copy SUMW
  have e6 : (Cmd.op (.copy REM SUMW)).eval w5
      = w5.set REM (List.replicate (step * C.offset + C.width) 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw5SUMW]
  have hc6 : Op.cost (.copy REM SUMW) w5 = step * C.offset + C.width + 1 := by
    show (State.get w5 SUMW).length + 1 = _
    rw [hw5SUMW, List.length_replicate]
  set w6 := w5.set REM (List.replicate (step * C.offset + C.width) 1) with hw6
  have hw6frame : ∀ r : Var, r ≠ REM → State.get w6 r = State.get w5 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw6REM : State.get w6 REM = List.replicate (step * C.offset + C.width) 1 :=
    State.get_set_eq _ _ _
  have hw6LREGlen : (State.get w6 LREG).length = C.init.length := by
    rw [hw6frame LREG (by decide), hw5frame LREG (by decide),
      hw4frame LREG (by decide), hw3LREG, List.length_replicate]
  clear_value w6
  -- w7: the truncated-subtraction loop (run + cost)
  have hcSub := cost_tailLoop_le KTMP LREG REM w6 (step * C.offset + C.width)
    C.init.length (by decide)
    (by rw [hw6REM, List.length_replicate]) hw6LREGlen
  obtain ⟨h7REM, h7frame⟩ :=
    unarySubLoop_run KTMP LREG REM w6 (step * C.offset + C.width) C.init.length
      (by decide) hw6LREGlen hw6REM
  set w7 := (Cmd.forBnd KTMP LREG (Cmd.op (.tail REM REM))).eval w6 with hw7
  clear_value w7
  have h7chain : ∀ r : Var, r ≠ STEPO → r ≠ KTMP → r ≠ STARTA → r ≠ STARTB →
      r ≠ SUMW → r ≠ REM → State.get w7 r = State.get u r := by
    intro r h1 h2 h3 h4 h5 h6
    rw [h7frame r h6 h2, hw6frame r h6, hw5frame r h5, hw4frame r h4,
      hw3frame r h3, h2frame r h1 h2, hw1frame r h1]
  have h7OUT : State.get w7 OUT = State.get u OUT :=
    h7chain OUT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h7Z : State.get w7 ZERO = [] := by
    rw [h7chain ZERO (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hZ
  have h7CARDS : State.get w7 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [h7chain CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hCARDS
  have h7CARDSlen : (State.get w7 CARDS).length = (State.get u CARDS).length := by
    rw [h7chain CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  have h7WREG : State.get w7 WREG = State.get u WREG :=
    h7chain WREG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h7SA : State.get w7 STARTA
      = List.replicate (line * C.init.length + step * C.offset) 1 := by
    rw [h7frame STARTA (by decide) (by decide), hw6frame STARTA (by decide),
      hw5frame STARTA (by decide), hw4frame STARTA (by decide)]
    exact hw3SA
  have h7SB : State.get w7 STARTB
      = List.replicate (line * C.init.length + step * C.offset + C.init.length) 1 := by
    rw [h7frame STARTB (by decide) (by decide), hw6frame STARTB (by decide),
      hw5frame STARTB (by decide)]
    exact hw4SB
  by_cases hguard : step * C.offset + C.width ≤ C.init.length
  · -- guard passes → emitCardsAt
    have hREM0 : State.get w7 REM = [] := by
      rw [h7REM, Nat.sub_eq_zero_of_le hguard]
      rfl
    have hne : (State.get w7 REM).isEmpty = true := by rw [hREM0]; rfl
    have e8 : (Cmd.op (.nonEmpty TFLG REM)).eval w7 = w7.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w8 := w7.set TFLG [0] with hw8
    have hw8frame : ∀ r : Var, r ≠ TFLG → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8Tne : State.get w8 TFLG ≠ [1] := by
      rw [hw8, State.get_set_eq]; decide
    clear_value w8
    have ec : (Cmd.op (.clear GFLG)).eval w8 = w8.set GFLG [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    have ea : (Cmd.op (.appendOne GFLG)).eval (w8.set GFLG []) = w8.set GFLG [1] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, State.set_set, List.nil_append]
    have e9 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w8
        = w8.set GFLG [1] := by
      rw [Cmd.eval_ifBit_false _ _ _ _ hw8Tne, Cmd.eval_seq, ec, ea]
    have hc9 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).cost w8 = 4 := by
      rw [Cmd.cost_ifBit_false _ _ _ _ hw8Tne, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op,
        ec]
      simp only [Op.cost]
    set w9 := w8.set GFLG [1] with hw9
    have hw9frame : ∀ r : Var, r ≠ GFLG → State.get w9 r = State.get w8 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw9G : State.get w9 GFLG = [1] := State.get_set_eq _ _ _
    clear_value w9
    have h9SA : State.get w9 STARTA
        = List.replicate (line * C.init.length + step * C.offset) 1 := by
      rw [hw9frame STARTA (by decide), hw8frame STARTA (by decide)]; exact h7SA
    have h9SB : State.get w9 STARTB
        = List.replicate (line * C.init.length + step * C.offset + C.init.length) 1 := by
      rw [hw9frame STARTB (by decide), hw8frame STARTB (by decide)]; exact h7SB
    have h9CARDS : State.get w9 CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
      rw [hw9frame CARDS (by decide), hw8frame CARDS (by decide)]; exact h7CARDS
    have h9CARDSlen : (State.get w9 CARDS).length = (State.get u CARDS).length := by
      rw [hw9frame CARDS (by decide), hw8frame CARDS (by decide)]; exact h7CARDSlen
    have h9Z : State.get w9 ZERO = [] := by
      rw [hw9frame ZERO (by decide), hw8frame ZERO (by decide)]; exact h7Z
    have h9OUT : State.get w9 OUT = State.get u OUT := by
      rw [hw9frame OUT (by decide), hw8frame OUT (by decide)]; exact h7OUT
    have h9WREG : State.get w9 WREG = State.get u WREG := by
      rw [hw9frame WREG (by decide), hw8frame WREG (by decide)]; exact h7WREG
    have hstep : encodeStepConstraint C line step
        = encodeCardsAt C (line * C.init.length + step * C.offset)
            (line * C.init.length + step * C.offset + C.init.length) := by
      unfold encodeStepConstraint
      rw [dif_pos hguard]
      congr 1
      rw [Nat.succ_mul]
      omega
    have hΩO9 : (State.get w9 OUT).length
        + (serF (encodeCardsAt C (line * C.init.length + step * C.offset)
            (line * C.init.length + step * C.offset + C.init.length))).length ≤ Ω := by
      rw [h9OUT, ← hstep]
      exact hΩO
    have hΩW9 : (State.get w9 WREG).length ≤ Ω := by rw [h9WREG]; exact hΩW
    have hΩA9 : line * C.init.length + step * C.offset
        + (State.get w9 CARDS).length ≤ Ω := by
      rw [h9CARDSlen]
      rw [hsucc] at hΩidx
      omega
    have hΩB9 : line * C.init.length + step * C.offset + C.init.length
        + (State.get w9 CARDS).length ≤ Ω := by
      rw [h9CARDSlen]
      rw [hsucc] at hΩidx
      omega
    have hcCA := emitCardsAt_cost (line * C.init.length + step * C.offset)
      (line * C.init.length + step * C.offset + C.init.length) C w9 Ω
      h9SA h9SB h9CARDS h9Z hΩO9 hΩW9 hΩA9 hΩB9
    have hWCA := emitCardsAt_WREG (line * C.init.length + step * C.offset)
      (line * C.init.length + step * C.offset + C.init.length) C w9 Ω
      h9SA h9SB h9CARDS h9Z hΩO9 hΩW9 hΩA9 hΩB9
    -- assemble
    have hcost : stepBody.cost u
        = 1 + 1 + (1 + (Cmd.forBnd KTMP KSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).cost w1
          + (1 + Op.cost (.concat STARTA LINEL STEPO) w2
          + (1 + Op.cost (.concat STARTB STARTA LREG) w3
          + (1 + Op.cost (.concat SUMW STEPO WIDTH) w4
          + (1 + Op.cost (.copy REM SUMW) w5
          + (1 + (Cmd.forBnd KTMP LREG (Cmd.op (.tail REM REM))).cost w6
          + (1 + 1
          + (1 + 4
          + (1 + emitCardsAt.cost w9))))))))) := by
      unfold stepBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq,
        Cmd.cost_op, e3, Cmd.cost_seq, Cmd.cost_op, e4, Cmd.cost_seq, Cmd.cost_op,
        e5, Cmd.cost_seq, Cmd.cost_op, e6, Cmd.cost_seq, ← hw7, Cmd.cost_seq,
        Cmd.cost_op, e8, Cmd.cost_seq, hc9, e9, Cmd.cost_ifBit_true _ _ _ _ hw9G]
      simp only [Op.cost]
    have heval : stepBody.eval u = emitCardsAt.eval w9 := by
      unfold stepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, ← hw7, Cmd.eval_seq, e8,
        Cmd.eval_seq, e9, Cmd.eval_ifBit_true _ _ _ _ hw9G]
    constructor
    · rw [hcost, hc3, hc4, hc5, hc6]
      -- collapse everything against the ceiling
      have hoff : C.offset ≤ Ω := by omega
      have hsteple : step ≤ Ω := by omega
      have hso : step * C.offset ≤ Ω := by omega
      have hwid : C.width ≤ Ω := by omega
      have hL : C.init.length ≤ Ω := by omega
      have hsb : line * C.init.length + step * C.offset + C.init.length ≤ Ω := by
        rw [hsucc] at hΩidx
        omega
      have hMulle := le_trans hcMul (mulLoopClose C.offset step Ω hoff hsteple hso)
      have hSuble := le_trans hcSub
        (subLoopClose (step * C.offset + C.width) C.init.length Ω (by omega) hL)
      set K := Cmd.flatK (sentBitBody 0) with hK
      set P2 := (Ω + 1) * (Ω + 1) with hP2
      set P3 := (Ω + 1) * P2 with hP3
      have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
      have hP23 : P2 ≤ P3 := by
        rw [hP3]
        exact Nat.le_mul_of_pos_left P2 (by omega)
      have hcCA' : emitCardsAt.cost w9 ≤ (2 * K + 44) * P3 := hcCA
      have h44_100 : (2 * K + 44) * P3 + 56 * P3 = (2 * K + 100) * P3 := by ring
      omega
    · rw [heval]
      exact hWCA
  · -- guard fails → emitFtrue
    obtain ⟨k, hk⟩ : ∃ k, step * C.offset + C.width - C.init.length = k + 1 :=
      ⟨step * C.offset + C.width - C.init.length - 1, by omega⟩
    have hne : (State.get w7 REM).isEmpty = false := by
      rw [h7REM, hk]
      rfl
    have e8 : (Cmd.op (.nonEmpty TFLG REM)).eval w7 = w7.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w8 := w7.set TFLG [1] with hw8
    have hw8frame : ∀ r : Var, r ≠ TFLG → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8T : State.get w8 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w8
    have e9 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w8
        = w8.set GFLG [] := by
      rw [Cmd.eval_ifBit_true _ _ _ _ hw8T, Cmd.eval_op]
      simp only [Op.eval]
    have hc9 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).cost w8 = 2 := by
      rw [Cmd.cost_ifBit_true _ _ _ _ hw8T, Cmd.cost_op]
      simp only [Op.cost]
    set w9 := w8.set GFLG [] with hw9
    have hw9frame : ∀ r : Var, r ≠ GFLG → State.get w9 r = State.get w8 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw9Gne : State.get w9 GFLG ≠ [1] := by
      rw [hw9, State.get_set_eq]; decide
    clear_value w9
    have h9WREG : State.get w9 WREG = State.get u WREG := by
      rw [hw9frame WREG (by decide), hw8frame WREG (by decide)]; exact h7WREG
    have hcost : stepBody.cost u
        = 1 + 1 + (1 + (Cmd.forBnd KTMP KSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).cost w1
          + (1 + Op.cost (.concat STARTA LINEL STEPO) w2
          + (1 + Op.cost (.concat STARTB STARTA LREG) w3
          + (1 + Op.cost (.concat SUMW STEPO WIDTH) w4
          + (1 + Op.cost (.copy REM SUMW) w5
          + (1 + (Cmd.forBnd KTMP LREG (Cmd.op (.tail REM REM))).cost w6
          + (1 + 1
          + (1 + 2
          + (1 + 3))))))))) := by
      unfold stepBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq,
        Cmd.cost_op, e3, Cmd.cost_seq, Cmd.cost_op, e4, Cmd.cost_seq, Cmd.cost_op,
        e5, Cmd.cost_seq, Cmd.cost_op, e6, Cmd.cost_seq, ← hw7, Cmd.cost_seq,
        Cmd.cost_op, e8, Cmd.cost_seq, hc9, e9, Cmd.cost_ifBit_false _ _ _ _ hw9Gne,
        emitFtrue_cost]
      simp only [Op.cost]
    have heval : stepBody.eval u = emitFtrue.eval w9 := by
      unfold stepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, e5, Cmd.eval_seq, e6, Cmd.eval_seq, ← hw7, Cmd.eval_seq, e8,
        Cmd.eval_seq, e9, Cmd.eval_ifBit_false _ _ _ _ hw9Gne]
    constructor
    · rw [hcost, hc3, hc4, hc5, hc6]
      have hoff : C.offset ≤ Ω := by omega
      have hsteple : step ≤ Ω := by omega
      have hso : step * C.offset ≤ Ω := by omega
      have hwid : C.width ≤ Ω := by omega
      have hL : C.init.length ≤ Ω := by omega
      have hsb : line * C.init.length + step * C.offset + C.init.length ≤ Ω := by
        rw [hsucc] at hΩidx
        omega
      have hMulle := le_trans hcMul (mulLoopClose C.offset step Ω hoff hsteple hso)
      have hSuble := le_trans hcSub
        (subLoopClose (step * C.offset + C.width) C.init.length Ω (by omega) hL)
      set K := Cmd.flatK (sentBitBody 0) with hK
      set P2 := (Ω + 1) * (Ω + 1) with hP2
      set P3 := (Ω + 1) * P2 with hP3
      have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
      have hP23 : P2 ≤ P3 := by
        rw [hP3]
        exact Nat.le_mul_of_pos_left P2 (by omega)
      have hKP3 : 0 ≤ (2 * K + 44) * P3 := Nat.zero_le _
      have h44_100 : (2 * K + 44) * P3 + 56 * P3 = (2 * K + 100) * P3 := by ring
      omega
    · rw [heval, emitFtrue_frame _ WREG (by decide), h9WREG]
      exact hΩW

/-! ### `emitAllSteps`: cost -/

private theorem andPrefix_range_succ (g : Nat → formula) (n : Nat) :
    andPrefix ((List.range (n + 1)).map g)
      = andPrefix ((List.range n).map g) ++ ([0, 1] ++ serF (g n)) := by
  rw [List.range_succ, List.map_append, andPrefix_append]
  simp [andPrefix]

private theorem andPrefix_range_le (g : Nat → formula) (k m : Nat) (h : k ≤ m) :
    (andPrefix ((List.range k).map g)).length
      ≤ (serF (listAnd ((List.range m).map g))).length := by
  have he : (List.range k).map g = ((List.range m).map g).take k := by
    rw [← List.map_take, List.take_range, Nat.min_eq_left h]
  rw [he]
  exact andPrefix_take_length_le _ k

/-- Per-iteration effect of the inner step loop: cost + `WREG ≤ Ω`.
`u3` is the inner loop's entry state (`LINEL` freshly rebuilt). -/
private theorem stepIterBody_effect (C : BinaryCC) (line : Nat) (u3 : State) (Ω : Nat)
    (hLINEL : State.get u3 LINEL = List.replicate (line * C.init.length) 1)
    (hOFF : State.get u3 OFFSET = List.replicate C.offset 1)
    (hWID : State.get u3 WIDTH = List.replicate C.width 1)
    (hLREG : State.get u3 LREG = List.replicate C.init.length 1)
    (hCARDS : State.get u3 CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hΩOL : (State.get u3 OUT).length
        + (serF (encodeLineConstraints C line)).length ≤ Ω)
    (hΩidxL : (line + 1) * C.init.length + C.init.length * C.offset
        + C.init.length + C.offset + C.width + C.init.length
        + (State.get u3 CARDS).length ≤ Ω)
    (i : Nat) (hi : i < C.init.length + 1) (st : State)
    (hInv : ASInv C line u3 i st) (hW : (State.get st WREG).length ≤ Ω) :
    stepIterBody.cost (st.set KSTEP (List.replicate i 1))
        ≤ 4 + (2 * Cmd.flatK (sentBitBody 0) + 100)
            * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))
    ∧ (State.get (stepIterBody.eval (st.set KSTEP (List.replicate i 1))) WREG).length
        ≤ Ω := by
  obtain ⟨hOUT, hZ, hframe⟩ := hInv
  set w := st.set KSTEP (List.replicate i 1) with hw
  have hwframe : ∀ r : Var, r ≠ KSTEP → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwK : State.get w KSTEP = List.replicate i 1 := State.get_set_eq _ _ _
  clear_value w
  set w1 := emitFandTag.eval w with hw1
  have hw1frame : ∀ r : Var, r ≠ OUT → State.get w1 r = State.get w r := by
    intro r hr; rw [hw1]; exact emitFandTag_frame w r hr
  have hw1OUT : State.get w1 OUT = State.get w OUT ++ [0, 1] := by
    rw [hw1, emitFandTag_run]; exact State.get_set_eq _ _ _
  clear_value w1
  -- thread the stepBody entry facts to w1
  have hchain : ∀ r : Var, r ≠ OUT → r ≠ KSTEP →
      r ≠ SCAN → r ≠ WREG → r ≠ TFLG → r ≠ KBIT → r ≠ DONE → r ≠ EMARK → r ≠ ZERO →
      r ≠ KTMP → r ≠ KCARD → r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW →
      r ≠ REM → r ≠ GFLG → State.get w1 r = State.get u3 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rw [hw1frame r h1, hwframe r h2,
      hframe r h3 h1 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h2]
  have h1LINEL : State.get w1 LINEL = List.replicate (line * C.init.length) 1 := by
    rw [hchain LINEL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hLINEL
  have h1KSTEP : State.get w1 KSTEP = List.replicate i 1 := by
    rw [hw1frame KSTEP (by decide)]; exact hwK
  have h1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hchain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hOFF
  have h1WID : State.get w1 WIDTH = List.replicate C.width 1 := by
    rw [hchain WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hWID
  have h1LREG : State.get w1 LREG = List.replicate C.init.length 1 := by
    rw [hchain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hLREG
  have h1CARDS : State.get w1 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [hchain CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hCARDS
  have h1CARDSlen : (State.get w1 CARDS).length = (State.get u3 CARDS).length := by
    rw [h1CARDS, ← hCARDS]
  have h1Z : State.get w1 ZERO = [] := by
    rw [hw1frame ZERO (by decide), hwframe ZERO (by decide)]; exact hZ
  have h1W : (State.get w1 WREG).length ≤ Ω := by
    rw [hw1frame WREG (by decide), hwframe WREG (by decide)]; exact hW
  -- the OUT ceiling at w1
  have h1OUTfull : State.get w1 OUT = State.get u3 OUT
      ++ andPrefix ((List.range i).map (encodeStepConstraint C line)) ++ [0, 1] := by
    rw [hw1OUT, hwframe OUT (by decide), hOUT]
  have hΩO1 : (State.get w1 OUT).length
      + (serF (encodeStepConstraint C line i)).length ≤ Ω := by
    have hsucc := andPrefix_range_succ (encodeStepConstraint C line) i
    have hle := andPrefix_range_le (encodeStepConstraint C line) (i + 1)
      (C.init.length + 1) hi
    have hlineC : serF (encodeLineConstraints C line)
        = serF (listAnd ((List.range (C.init.length + 1)).map
            (encodeStepConstraint C line))) := rfl
    rw [hlineC] at hΩOL
    rw [h1OUTfull]
    have hlen : (andPrefix ((List.range (i + 1)).map (encodeStepConstraint C line))).length
        = (andPrefix ((List.range i).map (encodeStepConstraint C line))).length
          + (2 + (serF (encodeStepConstraint C line i)).length) := by
      rw [hsucc]
      simp [List.length_append]
      omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hΩidxi : (line + 1) * C.init.length + i * C.offset + i + C.offset
      + C.width + C.init.length + (State.get w1 CARDS).length ≤ Ω := by
    have hiL : i ≤ C.init.length := by omega
    have hio : i * C.offset ≤ C.init.length * C.offset :=
      Nat.mul_le_mul_right _ hiL
    rw [h1CARDSlen]
    omega
  have hSB := stepBody_cost C line i w1 Ω h1LINEL h1KSTEP h1OFF h1WID h1LREG
    h1CARDS h1Z hΩO1 h1W hΩidxi
  have hcost : stepIterBody.cost w = 1 + 3 + stepBody.cost w1 := by
    unfold stepIterBody
    rw [Cmd.cost_seq, emitFandTag_cost, ← hw1]
  have heval : stepIterBody.eval w = stepBody.eval w1 := by
    unfold stepIterBody
    rw [Cmd.eval_seq, ← hw1]
  constructor
  · rw [hcost]
    have h1 := hSB.1
    set B := (2 * Cmd.flatK (sentBitBody 0) + 100) * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))
      with hB
    clear_value B
    omega
  · rw [heval]
    exact hSB.2

/-- Per-iteration effect of the line loop: cost + `WREG ≤ Ω`. `u0` is the
`emitAllSteps` entry state. -/
private theorem lineBody_effect (C : BinaryCC) (u0 : State) (Ω : Nat)
    (hOFF : State.get u0 OFFSET = List.replicate C.offset 1)
    (hWID : State.get u0 WIDTH = List.replicate C.width 1)
    (hLREG : State.get u0 LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u0 LREG1 = List.replicate (C.init.length + 1) 1)
    (hCARDS : State.get u0 CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hΩO : (State.get u0 OUT).length
        + (serF (encodeAllStepConstraints C)).length ≤ Ω)
    (hΩidx : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.offset + C.width + C.init.length + C.steps
        + (State.get u0 CARDS).length ≤ Ω)
    (j : Nat) (hj : j < C.steps) (st : State)
    (hInv : ALInv C u0 j st) (hW : (State.get st WREG).length ≤ Ω) :
    lineBody.cost (st.set KLINE (List.replicate j 1))
        ≤ (2 * Cmd.flatK (sentBitBody 0) + 140)
            * ((Ω + 1) * ((Ω + 1) * ((Ω + 1) * (Ω + 1))))
    ∧ (State.get (lineBody.eval (st.set KLINE (List.replicate j 1))) WREG).length
        ≤ Ω := by
  obtain ⟨hOUT, hZ, hframe⟩ := hInv
  set w := st.set KLINE (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KLINE → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwK : State.get w KLINE = List.replicate j 1 := State.get_set_eq _ _ _
  clear_value w
  set w1 := emitFandTag.eval w with hw1
  have hw1frame : ∀ r : Var, r ≠ OUT → State.get w1 r = State.get w r := by
    intro r hr; rw [hw1]; exact emitFandTag_frame w r hr
  have hw1OUT : State.get w1 OUT = State.get w OUT ++ [0, 1] := by
    rw [hw1, emitFandTag_run]; exact State.get_set_eq _ _ _
  clear_value w1
  -- w2: clear LINEL
  have e2 : (Cmd.op (.clear LINEL)).eval w1 = w1.set LINEL [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w2 := w1.set LINEL [] with hw2
  have hw2frame : ∀ r : Var, r ≠ LINEL → State.get w2 r = State.get w1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw2LINEL : State.get w2 LINEL = [] := State.get_set_eq _ _ _
  clear_value w2
  have h2chain : ∀ r : Var, r ≠ LINEL → r ≠ OUT → r ≠ KLINE →
      r ≠ SCAN → r ≠ WREG → r ≠ TFLG → r ≠ KBIT → r ≠ DONE → r ≠ EMARK → r ≠ ZERO →
      r ≠ KTMP → r ≠ KCARD → r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW →
      r ≠ REM → r ≠ GFLG → r ≠ KSTEP → r ≠ KTMP2 →
      State.get w2 r = State.get u0 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    rw [hw2frame r h1, hw1frame r h2, hwframe r h3,
      hframe r h4 h2 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h1 h3 h20]
  have h2LREG : State.get w2 LREG = List.replicate C.init.length 1 := by
    rw [h2chain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG
  have h2KLINElen : (State.get w2 KLINE).length = j := by
    rw [hw2frame KLINE (by decide), hw1frame KLINE (by decide), hwK,
      List.length_replicate]
  -- w3: LINEL := 1^(j·L) (run + cost)
  have hcMul := cost_mulLoop_le KTMP2 KLINE LINEL LREG w2 0 C.init.length j
    (by decide) (by decide) (by decide)
    (by rw [hw2LINEL]; exact Nat.le_refl 0)
    (by rw [h2LREG, List.length_replicate])
    h2KLINElen
  obtain ⟨h3LINEL, h3frame⟩ :=
    unaryMulLoop_run KTMP2 KLINE LREG LINEL w2 C.init.length j
      (by decide) (by decide) (by decide) h2LREG h2KLINElen hw2LINEL
  set w3 := (Cmd.forBnd KTMP2 KLINE (Cmd.op (.concat LINEL LINEL LREG))).eval w2
    with hw3
  clear_value w3
  have h3LINEL' : State.get w3 LINEL = List.replicate (j * C.init.length) 1 := by
    rw [h3LINEL]
  have h3chain : ∀ r : Var, r ≠ LINEL → r ≠ KTMP2 → r ≠ OUT → r ≠ KLINE →
      r ≠ SCAN → r ≠ WREG → r ≠ TFLG → r ≠ KBIT → r ≠ DONE → r ≠ EMARK → r ≠ ZERO →
      r ≠ KTMP → r ≠ KCARD → r ≠ STEPO → r ≠ STARTA → r ≠ STARTB → r ≠ SUMW →
      r ≠ REM → r ≠ GFLG → r ≠ KSTEP →
      State.get w3 r = State.get u0 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    rw [h3frame r h1 h2,
      h2chain r h1 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h2]
  have h3OFF : State.get w3 OFFSET = List.replicate C.offset 1 := by
    rw [h3chain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hOFF
  have h3WID : State.get w3 WIDTH = List.replicate C.width 1 := by
    rw [h3chain WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hWID
  have h3LREG : State.get w3 LREG = List.replicate C.init.length 1 := by
    rw [h3frame LREG (by decide) (by decide)]
    exact h2LREG
  have h3LREG1 : State.get w3 LREG1 = List.replicate (C.init.length + 1) 1 := by
    rw [h3chain LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG1
  have h3LREG1len : (State.get w3 LREG1).length = C.init.length + 1 := by
    rw [h3LREG1, List.length_replicate]
  have h3CARDS : State.get w3 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [h3chain CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hCARDS
  have h3CARDSlen : (State.get w3 CARDS).length = (State.get u0 CARDS).length := by
    rw [h3CARDS, ← hCARDS]
  have h3Z : State.get w3 ZERO = [] := by
    rw [h3frame ZERO (by decide) (by decide), hw2frame ZERO (by decide),
      hw1frame ZERO (by decide), hwframe ZERO (by decide)]
    exact hZ
  have h3W : (State.get w3 WREG).length ≤ Ω := by
    rw [h3frame WREG (by decide) (by decide), hw2frame WREG (by decide),
      hw1frame WREG (by decide), hwframe WREG (by decide)]
    exact hW
  have h3OUT : State.get w3 OUT = State.get u0 OUT
      ++ andPrefix ((List.range j).map (encodeLineConstraints C)) ++ [0, 1] := by
    rw [h3frame OUT (by decide) (by decide), hw2frame OUT (by decide), hw1OUT,
      hwframe OUT (by decide), hOUT]
  -- the line-level OUT ceiling at w3
  have hΩOL3 : (State.get w3 OUT).length
      + (serF (encodeLineConstraints C j)).length ≤ Ω := by
    have hsucc := andPrefix_range_succ (encodeLineConstraints C) j
    have hle := andPrefix_range_le (encodeLineConstraints C) (j + 1) C.steps hj
    have hallC : serF (encodeAllStepConstraints C)
        = serF (listAnd ((List.range C.steps).map (encodeLineConstraints C))) := rfl
    rw [hallC] at hΩO
    rw [h3OUT]
    have hlen : (andPrefix ((List.range (j + 1)).map (encodeLineConstraints C))).length
        = (andPrefix ((List.range j).map (encodeLineConstraints C))).length
          + (2 + (serF (encodeLineConstraints C j)).length) := by
      rw [hsucc]
      simp [List.length_append]
      omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hΩidxL3 : (j + 1) * C.init.length + C.init.length * C.offset
      + C.init.length + C.offset + C.width + C.init.length
      + (State.get w3 CARDS).length ≤ Ω := by
    have hjs : j + 1 ≤ C.steps := hj
    have hjL : (j + 1) * C.init.length ≤ C.steps * C.init.length :=
      Nat.mul_le_mul_right _ hjs
    rw [h3CARDSlen]
    omega
  -- the inner step loop (cost + run + WREG)
  have hasBase : ASInv C j w3 0 w3 :=
    ⟨by simp [andPrefix], h3Z,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  have hcInner := Cmd.cost_forBnd_le KSTEP LREG1 stepIterBody w3
    (4 + (2 * Cmd.flatK (sentBitBody 0) + 100) * ((Ω + 1) * ((Ω + 1) * (Ω + 1))))
    (fun i stt => ASInv C j w3 i stt ∧ (State.get stt WREG).length ≤ Ω)
    ⟨hasBase, h3W⟩
    (fun i stt hi hM => by
      refine ⟨ASInv_step C j w3 h3LINEL' h3OFF h3WID h3LREG h3CARDS i stt hM.1, ?_⟩
      exact (stepIterBody_effect C j w3 Ω h3LINEL' h3OFF h3WID h3LREG h3CARDS
        hΩOL3 hΩidxL3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).2)
    (fun i stt hi hM =>
      (stepIterBody_effect C j w3 Ω h3LINEL' h3OFF h3WID h3LREG h3CARDS
        hΩOL3 hΩidxL3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).1)
  have hwInner := Cmd.foldlState_range_induct stepIterBody KSTEP
    (State.get w3 LREG1).length w3
    (fun i stt => ASInv C j w3 i stt ∧ (State.get stt WREG).length ≤ Ω)
    ⟨hasBase, h3W⟩
    (fun i stt hi hM => by
      refine ⟨ASInv_step C j w3 h3LINEL' h3OFF h3WID h3LREG h3CARDS i stt hM.1, ?_⟩
      exact (stepIterBody_effect C j w3 Ω h3LINEL' h3OFF h3WID h3LREG h3CARDS
        hΩOL3 hΩidxL3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).2)
  set w4 := (Cmd.forBnd KSTEP LREG1 stepIterBody).eval w3 with hw4
  have hw4eval : w4 = Cmd.foldlState stepIterBody KSTEP
      (List.range (State.get w3 LREG1).length) w3 := by
    rw [hw4, Cmd.eval_forBnd]
  have h4W : (State.get w4 WREG).length ≤ Ω := by
    rw [hw4eval]
    exact hwInner.2
  clear_value w4
  -- assemble lineBody
  have hcost : lineBody.cost w
      = 1 + 3 + (1 + 1
        + (1 + (Cmd.forBnd KTMP2 KLINE (Cmd.op (.concat LINEL LINEL LREG))).cost w2
        + (1 + (Cmd.forBnd KSTEP LREG1 stepIterBody).cost w3 + 3))) := by
    unfold lineBody
    rw [Cmd.cost_seq, emitFandTag_cost, ← hw1, Cmd.cost_seq, Cmd.cost_op, e2,
      Cmd.cost_seq, ← hw3, Cmd.cost_seq, ← hw4, emitFtrue_cost]
    simp only [Op.cost]
  have heval : lineBody.eval w = emitFtrue.eval w4 := by
    unfold lineBody
    rw [Cmd.eval_seq, ← hw1, Cmd.eval_seq, e2, Cmd.eval_seq, ← hw3, Cmd.eval_seq,
      ← hw4]
  constructor
  · rw [hcost]
    -- arithmetic
    have hjs : j ≤ C.steps := le_of_lt hj
    have hjL : j * C.init.length ≤ C.steps * C.init.length :=
      Nat.mul_le_mul_right _ hjs
    have hL : C.init.length ≤ Ω := by omega
    have hjΩ : j ≤ Ω := by omega
    have hjLΩ : j * C.init.length ≤ Ω := by omega
    have hMulle := le_trans hcMul (mulLoopClose C.init.length j Ω hL hjΩ hjLΩ)
    have hiters : (State.get w3 LREG1).length ≤ Ω + 1 := by
      rw [h3LREG1len]; omega
    set K := Cmd.flatK (sentBitBody 0) with hK
    clear_value K
    set P2 := (Ω + 1) * (Ω + 1) with hP2
    set P3 := (Ω + 1) * P2 with hP3
    set P4 := (Ω + 1) * P3 with hP4
    set B := 4 + (2 * K + 100) * P3 with hB
    have hBle : B ≤ (2 * K + 104) * P3 := by
      rw [hB]
      have h1P3 : 1 ≤ P3 := by
        rw [hP3, hP2]
        exact le_trans (one_le_P Ω) (Nat.mul_le_mul_left _ (le_scale Ω (Ω + 1)))
      have h4P3 : 4 + (2 * K + 100) * P3 ≤ 4 * P3 + (2 * K + 100) * P3 := by omega
      have he : 4 * P3 + (2 * K + 100) * P3 = (2 * K + 104) * P3 := by ring
      omega
    have hlB : (State.get w3 LREG1).length * B ≤ (Ω + 1) * ((2 * K + 104) * P3) :=
      Nat.mul_le_mul hiters hBle
    have he4 : (Ω + 1) * ((2 * K + 104) * P3) = (2 * K + 104) * P4 := by
      rw [hP4]; ring
    have hii : (State.get w3 LREG1).length * (State.get w3 LREG1).length
        ≤ (Ω + 1) * (Ω + 1) := Nat.mul_le_mul hiters hiters
    have hP24 : P2 ≤ P4 := by
      rw [hP4, hP3]
      exact le_trans (le_scale Ω P2) (Nat.mul_le_mul_left _ (le_scale Ω P2))
    have hfin : (2 * K + 140) * P4 = (2 * K + 104) * P4 + 36 * P4 := by ring
    have h1P4 : 1 ≤ P4 := by
      rw [hP4, hP3, hP2]
      exact Nat.mul_pos (Nat.succ_pos Ω) (Nat.mul_pos (Nat.succ_pos Ω)
        (Nat.mul_pos (Nat.succ_pos Ω) (Nat.succ_pos Ω)))
    omega
  · rw [heval, emitFtrue_frame _ WREG (by decide)]
    exact h4W

/-- **`emitAllSteps` cost**: quintic in the ceiling `Ω`, plus `WREG ≤ Ω` exit. -/
theorem emitAllSteps_cost (C : BinaryCC) (u : State) (Ω : Nat)
    (hSTEPS : State.get u STEPS = List.replicate C.steps 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hWID : State.get u WIDTH = List.replicate C.width 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u LREG1 = List.replicate (C.init.length + 1) 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length
        + (serF (encodeAllStepConstraints C)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩidx : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.offset + C.width + C.init.length + C.steps
        + (State.get u CARDS).length ≤ Ω) :
    emitAllSteps.cost u
        ≤ (2 * Cmd.flatK (sentBitBody 0) + 160)
            * ((Ω + 1) * ((Ω + 1) * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))))
    ∧ (State.get (emitAllSteps.eval u) WREG).length ≤ Ω := by
  have heq : emitAllSteps = (Cmd.forBnd KLINE STEPS lineBody ;; emitFtrue) := rfl
  have hSTEPSlen : (State.get u STEPS).length = C.steps := by
    rw [hSTEPS, List.length_replicate]
  have hloop := Cmd.cost_forBnd_le KLINE STEPS lineBody u
    ((2 * Cmd.flatK (sentBitBody 0) + 140)
      * ((Ω + 1) * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))))
    (fun j st => ALInv C u j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨by simp [andPrefix], hZ,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩, hΩW⟩
    (fun j st hj hM => by
      refine ⟨ALInv_step C u hOFF hWID hLREG hLREG1 hCARDS j st hM.1, ?_⟩
      exact (lineBody_effect C u Ω hOFF hWID hLREG hLREG1 hCARDS hΩO hΩidx j
        (by rw [hSTEPSlen] at hj; exact hj) st hM.1 hM.2).2)
    (fun j st hj hM =>
      (lineBody_effect C u Ω hOFF hWID hLREG hLREG1 hCARDS hΩO hΩidx j
        (by rw [hSTEPSlen] at hj; exact hj) st hM.1 hM.2).1)
  have hwLoop := Cmd.foldlState_range_induct lineBody KLINE
    (State.get u STEPS).length u
    (fun j st => ALInv C u j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨⟨by simp [andPrefix], hZ,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩, hΩW⟩
    (fun j st hj hM => by
      refine ⟨ALInv_step C u hOFF hWID hLREG hLREG1 hCARDS j st hM.1, ?_⟩
      exact (lineBody_effect C u Ω hOFF hWID hLREG hLREG1 hCARDS hΩO hΩidx j
        (by rw [hSTEPSlen] at hj; exact hj) st hM.1 hM.2).2)
  rw [heq, Cmd.cost_seq, emitFtrue_cost]
  constructor
  · -- arithmetic
    have hsteps : C.steps ≤ Ω := by omega
    set K := Cmd.flatK (sentBitBody 0) with hK
    clear_value K
    set P2 := (Ω + 1) * (Ω + 1) with hP2
    set P3 := (Ω + 1) * P2 with hP3
    set P4 := (Ω + 1) * P3 with hP4
    set P5 := (Ω + 1) * P4 with hP5
    rw [hSTEPSlen] at hloop
    have hlB : C.steps * ((2 * K + 140) * P4) ≤ (Ω + 1) * ((2 * K + 140) * P4) :=
      Nat.mul_le_mul_right _ (by omega)
    have he5 : (Ω + 1) * ((2 * K + 140) * P4) = (2 * K + 140) * P5 := by
      rw [hP5]; ring
    have hss : C.steps * C.steps ≤ Ω * Ω := Nat.mul_le_mul hsteps hsteps
    have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
    have hP25 : P2 ≤ P5 := by
      rw [hP5, hP4, hP3]
      exact le_trans (le_scale Ω P2) (Nat.mul_le_mul_left _
        (le_trans (le_scale Ω P2) (Nat.mul_le_mul_left _ (le_scale Ω P2))))
    have hfin : (2 * K + 160) * P5 = (2 * K + 140) * P5 + 20 * P5 := by ring
    have h1P5 : 1 ≤ P5 := by
      rw [hP5, hP4, hP3, hP2]
      exact Nat.mul_pos (Nat.succ_pos Ω) (Nat.mul_pos (Nat.succ_pos Ω)
        (Nat.mul_pos (Nat.succ_pos Ω) (Nat.mul_pos (Nat.succ_pos Ω) (Nat.succ_pos Ω))))
    omega
  · rw [Cmd.eval_seq, emitFtrue_frame _ WREG (by decide), Cmd.eval_forBnd]
    exact hwLoop.2

/-! ### `emitFinal`: cost -/

private theorem orPrefix_range_succ (g : Nat → formula) (n : Nat) :
    orPrefix ((List.range (n + 1)).map g)
      = orPrefix ((List.range n).map g) ++ ([1, 0] ++ serF (g n)) := by
  rw [List.range_succ, List.map_append, orPrefix_append]
  simp [orPrefix]

private theorem orPrefix_range_le (g : Nat → formula) (k m : Nat) (h : k ≤ m) :
    (orPrefix ((List.range k).map g)).length
      ≤ (serF (listOr ((List.range m).map g))).length := by
  have he : (List.range k).map g = ((List.range m).map g).take k := by
    rw [← List.map_take, List.take_range, Nat.min_eq_left h]
  rw [he]
  exact orPrefix_take_length_le _ k

private theorem encSList_length_ge (l : List Nat) :
    l.length ≤ (FlatTCCFree.encSList l).length := by
  induction l with
  | nil => simp [FlatTCCFree.encSList]
  | cons v xs ih =>
      show _ ≤ (FlatTCCFree.encSElem v ++ FlatTCCFree.encSList xs).length
      simp only [List.length_append, List.length_cons, FlatTCCFree.encSElem,
        List.length_replicate]
      omega

/-- `emitBitsFromScan` never grows `WREG` beyond `max(entry, start + |bits|)`. -/
private theorem emitBitsFromScan_WREG (BASE bound : Nat) (u : State) (W : Nat)
    (hBT : BASE ≠ TFLG) (hBS : BASE ≠ SCAN) (hBK : BASE ≠ KBIT)
    (hBmem : BASE ∉ Cmd.writes (bsBody BASE))
    (hW : (State.get u WREG).length ≤ W)
    (hBb : (State.get u BASE).length + (State.get u bound).length ≤ W) :
    (State.get ((emitBitsFromScan BASE bound).eval u) WREG).length ≤ W := by
  rw [emitBitsFromScan_eq, Cmd.eval_seq, emitFtrue_frame _ WREG (by decide),
    Cmd.eval_forBnd]
  have hInv := Cmd.foldlState_range_induct (bsBody BASE) KBIT
    (State.get u bound).length u
    (fun i st => (State.get st WREG).length ≤ W
      ∧ State.get st BASE = State.get u BASE)
    ⟨hW, rfl⟩
    (fun i st hi hM => by
      obtain ⟨hWl, hBf⟩ := hM
      constructor
      · rw [bsBody_WREG BASE _ hBT hBS,
          State.get_set_ne _ _ _ _ hBK, State.get_set_eq, hBf,
          List.length_append, List.length_replicate]
        omega
      · rw [Cmd.eval_get_of_not_writes _ _ BASE hBmem,
          State.get_set_ne _ _ _ _ hBK]
        exact hBf)
  exact hInv.1

/-- **`finalStepBody` cost**: quadratic in `Ω`, plus the `WREG ≤ Ω` exit fact. -/
theorem finalStepBody_cost (C : BinaryCC) (step : Nat) (bits : List Bool) (u : State)
    (Ω : Nat)
    (hSTEPSL : State.get u STEPSL = List.replicate (C.steps * C.init.length) 1)
    (hKFSTEP : State.get u KFSTEP = List.replicate step 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hBLEN : State.get u BLEN = List.replicate bits.length 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hFBITS : State.get u FBITS = FlatCCBinFree.bitsNat bits)
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length
        + (serF (encodeFinalAtStep C step bits)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩidx : C.steps * C.init.length + step * C.offset + step + C.offset
        + bits.length + C.init.length ≤ Ω) :
    finalStepBody.cost u
        ≤ (Cmd.flatK (bsBody 0) + 60) * ((Ω + 1) * (Ω + 1))
    ∧ (State.get (finalStepBody.eval u) WREG).length ≤ Ω := by
  -- w1: clear STEPO
  have e1 : (Cmd.op (.clear STEPO)).eval u = u.set STEPO [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w1 := u.set STEPO [] with hw1
  have hw1frame : ∀ r : Var, r ≠ STEPO → State.get w1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1STEPO : State.get w1 STEPO = [] := State.get_set_eq _ _ _
  have hw1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hw1frame OFFSET (by decide)]; exact hOFF
  have hw1KFSTEPlen : (State.get w1 KFSTEP).length = step := by
    rw [hw1frame KFSTEP (by decide), hKFSTEP, List.length_replicate]
  clear_value w1
  -- w2: STEPO mul loop
  have hcMul := cost_mulLoop_le KTMP2 KFSTEP STEPO OFFSET w1 0 C.offset step
    (by decide) (by decide) (by decide)
    (by rw [hw1STEPO]; exact Nat.le_refl 0)
    (by rw [hw1OFF, List.length_replicate])
    hw1KFSTEPlen
  obtain ⟨h2STEPO, h2frame⟩ :=
    unaryMulLoop_run KTMP2 KFSTEP OFFSET STEPO w1 C.offset step
      (by decide) (by decide) (by decide) hw1OFF hw1KFSTEPlen hw1STEPO
  set w2 := (Cmd.forBnd KTMP2 KFSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).eval w1
    with hw2
  clear_value w2
  have hw2BLEN : State.get w2 BLEN = List.replicate bits.length 1 := by
    rw [h2frame BLEN (by decide) (by decide), hw1frame BLEN (by decide)]
    exact hBLEN
  -- w3: SUMW := STEPO ++ BLEN
  have e3 : (Cmd.op (.concat SUMW STEPO BLEN)).eval w2
      = w2.set SUMW (List.replicate (step * C.offset + bits.length) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, h2STEPO, hw2BLEN]
    congr 1
    rw [List.replicate_add]
  have hc3 : Op.cost (.concat SUMW STEPO BLEN) w2
      = 2 * (step * C.offset + bits.length) + 1 := by
    show 2 * ((State.get w2 STEPO).length + (State.get w2 BLEN).length) + 1 = _
    rw [h2STEPO, hw2BLEN, List.length_replicate, List.length_replicate]
  set w3 := w2.set SUMW (List.replicate (step * C.offset + bits.length) 1) with hw3
  have hw3frame : ∀ r : Var, r ≠ SUMW → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3SUMW : State.get w3 SUMW
      = List.replicate (step * C.offset + bits.length) 1 := State.get_set_eq _ _ _
  clear_value w3
  -- w4: REM := copy SUMW
  have e4 : (Cmd.op (.copy REM SUMW)).eval w3
      = w3.set REM (List.replicate (step * C.offset + bits.length) 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hw3SUMW]
  have hc4 : Op.cost (.copy REM SUMW) w3 = step * C.offset + bits.length + 1 := by
    show (State.get w3 SUMW).length + 1 = _
    rw [hw3SUMW, List.length_replicate]
  set w4 := w3.set REM (List.replicate (step * C.offset + bits.length) 1) with hw4
  have hw4frame : ∀ r : Var, r ≠ REM → State.get w4 r = State.get w3 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw4REM : State.get w4 REM
      = List.replicate (step * C.offset + bits.length) 1 := State.get_set_eq _ _ _
  have hw4LREGlen : (State.get w4 LREG).length = C.init.length := by
    rw [hw4frame LREG (by decide), hw3frame LREG (by decide),
      h2frame LREG (by decide) (by decide), hw1frame LREG (by decide),
      hLREG, List.length_replicate]
  clear_value w4
  -- w5: the truncated-subtraction loop
  have hcSub := cost_tailLoop_le KTMP2 LREG REM w4 (step * C.offset + bits.length)
    C.init.length (by decide)
    (by rw [hw4REM, List.length_replicate]) hw4LREGlen
  obtain ⟨h5REM, h5frame⟩ :=
    unarySubLoop_run KTMP2 LREG REM w4 (step * C.offset + bits.length) C.init.length
      (by decide) hw4LREGlen hw4REM
  set w5 := (Cmd.forBnd KTMP2 LREG (Cmd.op (.tail REM REM))).eval w4 with hw5
  clear_value w5
  have h5chain : ∀ r : Var, r ≠ STEPO → r ≠ KTMP2 → r ≠ SUMW → r ≠ REM →
      State.get w5 r = State.get u r := by
    intro r h1 h2 h3 h4
    rw [h5frame r h4 h2, hw4frame r h4, hw3frame r h3, h2frame r h1 h2,
      hw1frame r h1]
  have h5OUT : State.get w5 OUT = State.get u OUT :=
    h5chain OUT (by decide) (by decide) (by decide) (by decide)
  have h5WREG : State.get w5 WREG = State.get u WREG :=
    h5chain WREG (by decide) (by decide) (by decide) (by decide)
  have h5STEPSL : State.get w5 STEPSL
      = List.replicate (C.steps * C.init.length) 1 := by
    rw [h5chain STEPSL (by decide) (by decide) (by decide) (by decide)]
    exact hSTEPSL
  have h5STEPO : State.get w5 STEPO = List.replicate (step * C.offset) 1 := by
    rw [h5frame STEPO (by decide) (by decide), hw4frame STEPO (by decide),
      hw3frame STEPO (by decide)]
    exact h2STEPO
  have h5FBITS : State.get w5 FBITS = FlatCCBinFree.bitsNat bits := by
    rw [h5chain FBITS (by decide) (by decide) (by decide) (by decide)]
    exact hFBITS
  -- w6: nonEmpty TFLG REM, w7: the GFLG bit
  by_cases hguard : step * C.offset + bits.length ≤ C.init.length
  · have hREM0 : State.get w5 REM = [] := by
      rw [h5REM, Nat.sub_eq_zero_of_le hguard]
      rfl
    have hne : (State.get w5 REM).isEmpty = true := by rw [hREM0]; rfl
    have e6 : (Cmd.op (.nonEmpty TFLG REM)).eval w5 = w5.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w6 := w5.set TFLG [0] with hw6
    have hw6frame : ∀ r : Var, r ≠ TFLG → State.get w6 r = State.get w5 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw6Tne : State.get w6 TFLG ≠ [1] := by
      rw [hw6, State.get_set_eq]; decide
    clear_value w6
    have ec : (Cmd.op (.clear GFLG)).eval w6 = w6.set GFLG [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    have ea : (Cmd.op (.appendOne GFLG)).eval (w6.set GFLG []) = w6.set GFLG [1] := by
      rw [Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, State.set_set, List.nil_append]
    have e7 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w6
        = w6.set GFLG [1] := by
      rw [Cmd.eval_ifBit_false _ _ _ _ hw6Tne, Cmd.eval_seq, ec, ea]
    have hc7 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).cost w6 = 4 := by
      rw [Cmd.cost_ifBit_false _ _ _ _ hw6Tne, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op,
        ec]
      simp only [Op.cost]
    set w7 := w6.set GFLG [1] with hw7
    have hw7frame : ∀ r : Var, r ≠ GFLG → State.get w7 r = State.get w6 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw7G : State.get w7 GFLG = [1] := State.get_set_eq _ _ _
    clear_value w7
    have h7STEPSL : State.get w7 STEPSL
        = List.replicate (C.steps * C.init.length) 1 := by
      rw [hw7frame STEPSL (by decide), hw6frame STEPSL (by decide)]; exact h5STEPSL
    have h7STEPO : State.get w7 STEPO = List.replicate (step * C.offset) 1 := by
      rw [hw7frame STEPO (by decide), hw6frame STEPO (by decide)]; exact h5STEPO
    -- w8: FSTART := STEPSL ++ STEPO
    have e8 : (Cmd.op (.concat FSTART STEPSL STEPO)).eval w7
        = w7.set FSTART (List.replicate
            (C.steps * C.init.length + step * C.offset) 1) := by
      rw [Cmd.eval_op]
      simp only [Op.eval, h7STEPSL, h7STEPO]
      congr 1
      rw [List.replicate_add]
    have hc8 : Op.cost (.concat FSTART STEPSL STEPO) w7
        = 2 * (C.steps * C.init.length + step * C.offset) + 1 := by
      show 2 * ((State.get w7 STEPSL).length + (State.get w7 STEPO).length) + 1 = _
      rw [h7STEPSL, h7STEPO, List.length_replicate, List.length_replicate]
    set w8 := w7.set FSTART (List.replicate
        (C.steps * C.init.length + step * C.offset) 1) with hw8
    have hw8frame : ∀ r : Var, r ≠ FSTART → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8F : State.get w8 FSTART
        = List.replicate (C.steps * C.init.length + step * C.offset) 1 :=
      State.get_set_eq _ _ _
    have hw8FBITS : State.get w8 FBITS = FlatCCBinFree.bitsNat bits := by
      rw [hw8frame FBITS (by decide), hw7frame FBITS (by decide),
        hw6frame FBITS (by decide)]
      exact h5FBITS
    have hw8OUT : State.get w8 OUT = State.get u OUT := by
      rw [hw8frame OUT (by decide), hw7frame OUT (by decide),
        hw6frame OUT (by decide)]
      exact h5OUT
    have hw8WREG : State.get w8 WREG = State.get u WREG := by
      rw [hw8frame WREG (by decide), hw7frame WREG (by decide),
        hw6frame WREG (by decide)]
      exact h5WREG
    have hw8G : State.get w8 GFLG = [1] := by
      rw [hw8frame GFLG (by decide)]; exact hw7G
    clear_value w8
    -- w9: copy SCAN FBITS
    have e9 : (Cmd.op (.copy SCAN FBITS)).eval w8
        = w8.set SCAN (FlatCCBinFree.bitsNat bits) := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw8FBITS]
    have hc9 : Op.cost (.copy SCAN FBITS) w8 = bits.length + 1 := by
      show (State.get w8 FBITS).length + 1 = _
      rw [hw8FBITS]
      exact congrArg (· + 1) (List.length_map _)
    set w9 := w8.set SCAN (FlatCCBinFree.bitsNat bits) with hw9
    have hw9frame : ∀ r : Var, r ≠ SCAN → State.get w9 r = State.get w8 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw9SCAN : State.get w9 SCAN = FlatCCBinFree.bitsNat bits :=
      State.get_set_eq _ _ _
    have hw9F : State.get w9 FSTART
        = List.replicate (C.steps * C.init.length + step * C.offset) 1 := by
      rw [hw9frame FSTART (by decide)]; exact hw8F
    have hw9FBITSlen : (State.get w9 FBITS).length = bits.length := by
      rw [hw9frame FBITS (by decide), hw8FBITS]
      exact List.length_map _
    have hw9OUT : State.get w9 OUT = State.get u OUT := by
      rw [hw9frame OUT (by decide)]; exact hw8OUT
    have hw9WREG : State.get w9 WREG = State.get u WREG := by
      rw [hw9frame WREG (by decide)]; exact hw8WREG
    clear_value w9
    have hstep : encodeFinalAtStep C step bits
        = encodeBitsAt (C.steps * C.init.length + step * C.offset) bits := by
      unfold encodeFinalAtStep
      rw [dif_pos hguard]
    have hcScan := emitBitsFromScan_cost FSTART FBITS
      (C.steps * C.init.length + step * C.offset) bits w9 Ω
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw9F hw9FBITSlen hw9SCAN
      (by rw [hw9OUT, ← hstep]; exact hΩO)
      (by rw [hw9WREG]; exact hΩW)
      (by omega)
    have hWScan := emitBitsFromScan_WREG FSTART FBITS w9 Ω
      (by decide) (by decide) (by decide) (by decide)
      (by rw [hw9WREG]; exact hΩW)
      (by rw [hw9F, List.length_replicate, hw9FBITSlen]; omega)
    have hcost : finalStepBody.cost u
        = 1 + 1 + (1 + (Cmd.forBnd KTMP2 KFSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).cost w1
          + (1 + Op.cost (.concat SUMW STEPO BLEN) w2
          + (1 + Op.cost (.copy REM SUMW) w3
          + (1 + (Cmd.forBnd KTMP2 LREG (Cmd.op (.tail REM REM))).cost w4
          + (1 + 1
          + (1 + 4
          + (1 + Op.cost (.concat FSTART STEPSL STEPO) w7
          + (1 + (1 + Op.cost (.copy SCAN FBITS) w8
              + (emitBitsFromScan FSTART FBITS).cost w9))))))))) := by
      unfold finalStepBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq,
        Cmd.cost_op, e3, Cmd.cost_seq, Cmd.cost_op, e4, Cmd.cost_seq, ← hw5,
        Cmd.cost_seq, Cmd.cost_op, e6, Cmd.cost_seq, hc7, e7, Cmd.cost_seq,
        Cmd.cost_op, e8, Cmd.cost_ifBit_true _ _ _ _ hw8G, Cmd.cost_seq,
        Cmd.cost_op, e9]
      simp only [Op.cost]
    have heval : finalStepBody.eval u = (emitBitsFromScan FSTART FBITS).eval w9 := by
      unfold finalStepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, ← hw5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq, e8,
        Cmd.eval_ifBit_true _ _ _ _ hw8G, Cmd.eval_seq, e9]
    constructor
    · rw [hcost, hc3, hc4, hc8, hc9]
      have hoff : C.offset ≤ Ω := by omega
      have hsteple : step ≤ Ω := by omega
      have hso : step * C.offset ≤ Ω := by omega
      have hbl : bits.length ≤ Ω := by omega
      have hL : C.init.length ≤ Ω := by omega
      have hsl : C.steps * C.init.length + step * C.offset ≤ Ω := by omega
      have hMulle := le_trans hcMul (mulLoopClose C.offset step Ω hoff hsteple hso)
      have hSuble := le_trans hcSub
        (subLoopClose (step * C.offset + bits.length) C.init.length Ω (by omega) hL)
      have hScanle := hcScan
      set K := Cmd.flatK (bsBody 0) with hK
      clear_value K
      set P2 := (Ω + 1) * (Ω + 1) with hP2
      have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
      have hfin : (K + 60) * P2 = (K + 6) * P2 + 54 * P2 := by ring
      omega
    · rw [heval]
      exact hWScan
  · -- guard fails → emitFalse
    obtain ⟨k, hk⟩ : ∃ k, step * C.offset + bits.length - C.init.length = k + 1 :=
      ⟨step * C.offset + bits.length - C.init.length - 1, by omega⟩
    have hne : (State.get w5 REM).isEmpty = false := by
      rw [h5REM, hk]
      rfl
    have e6 : (Cmd.op (.nonEmpty TFLG REM)).eval w5 = w5.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]
      rfl
    set w6 := w5.set TFLG [1] with hw6
    have hw6frame : ∀ r : Var, r ≠ TFLG → State.get w6 r = State.get w5 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw6T : State.get w6 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w6
    have e7 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).eval w6
        = w6.set GFLG [] := by
      rw [Cmd.eval_ifBit_true _ _ _ _ hw6T, Cmd.eval_op]
      simp only [Op.eval]
    have hc7 : (Cmd.ifBit TFLG (Cmd.op (.clear GFLG))
        (Cmd.op (.clear GFLG) ;; Cmd.op (.appendOne GFLG))).cost w6 = 2 := by
      rw [Cmd.cost_ifBit_true _ _ _ _ hw6T, Cmd.cost_op]
      simp only [Op.cost]
    set w7 := w6.set GFLG [] with hw7
    have hw7frame : ∀ r : Var, r ≠ GFLG → State.get w7 r = State.get w6 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw7Gne : State.get w7 GFLG ≠ [1] := by
      rw [hw7, State.get_set_eq]; decide
    clear_value w7
    have h7STEPSL : State.get w7 STEPSL
        = List.replicate (C.steps * C.init.length) 1 := by
      rw [hw7frame STEPSL (by decide), hw6frame STEPSL (by decide)]; exact h5STEPSL
    have h7STEPO : State.get w7 STEPO = List.replicate (step * C.offset) 1 := by
      rw [hw7frame STEPO (by decide), hw6frame STEPO (by decide)]; exact h5STEPO
    have e8 : (Cmd.op (.concat FSTART STEPSL STEPO)).eval w7
        = w7.set FSTART (List.replicate
            (C.steps * C.init.length + step * C.offset) 1) := by
      rw [Cmd.eval_op]
      simp only [Op.eval, h7STEPSL, h7STEPO]
      congr 1
      rw [List.replicate_add]
    have hc8 : Op.cost (.concat FSTART STEPSL STEPO) w7
        = 2 * (C.steps * C.init.length + step * C.offset) + 1 := by
      show 2 * ((State.get w7 STEPSL).length + (State.get w7 STEPO).length) + 1 = _
      rw [h7STEPSL, h7STEPO, List.length_replicate, List.length_replicate]
    set w8 := w7.set FSTART (List.replicate
        (C.steps * C.init.length + step * C.offset) 1) with hw8
    have hw8frame : ∀ r : Var, r ≠ FSTART → State.get w8 r = State.get w7 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw8Gne : State.get w8 GFLG ≠ [1] := by
      rw [hw8frame GFLG (by decide)]; exact hw7Gne
    have hw8WREG : State.get w8 WREG = State.get u WREG := by
      rw [hw8frame WREG (by decide), hw7frame WREG (by decide),
        hw6frame WREG (by decide)]
      exact h5WREG
    clear_value w8
    have hcost : finalStepBody.cost u
        = 1 + 1 + (1 + (Cmd.forBnd KTMP2 KFSTEP (Cmd.op (.concat STEPO STEPO OFFSET))).cost w1
          + (1 + Op.cost (.concat SUMW STEPO BLEN) w2
          + (1 + Op.cost (.copy REM SUMW) w3
          + (1 + (Cmd.forBnd KTMP2 LREG (Cmd.op (.tail REM REM))).cost w4
          + (1 + 1
          + (1 + 2
          + (1 + Op.cost (.concat FSTART STEPSL STEPO) w7
          + (1 + 9)))))))) := by
      unfold finalStepBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq,
        Cmd.cost_op, e3, Cmd.cost_seq, Cmd.cost_op, e4, Cmd.cost_seq, ← hw5,
        Cmd.cost_seq, Cmd.cost_op, e6, Cmd.cost_seq, hc7, e7, Cmd.cost_seq,
        Cmd.cost_op, e8, Cmd.cost_ifBit_false _ _ _ _ hw8Gne, emitFalse_cost]
      simp only [Op.cost]
    have heval : finalStepBody.eval u = emitFalse.eval w8 := by
      unfold finalStepBody
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hw2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
        Cmd.eval_seq, ← hw5, Cmd.eval_seq, e6, Cmd.eval_seq, e7, Cmd.eval_seq, e8,
        Cmd.eval_ifBit_false _ _ _ _ hw8Gne]
    constructor
    · rw [hcost, hc3, hc4, hc8]
      have hoff : C.offset ≤ Ω := by omega
      have hsteple : step ≤ Ω := by omega
      have hso : step * C.offset ≤ Ω := by omega
      have hbl : bits.length ≤ Ω := by omega
      have hL : C.init.length ≤ Ω := by omega
      have hsl : C.steps * C.init.length + step * C.offset ≤ Ω := by omega
      have hMulle := le_trans hcMul (mulLoopClose C.offset step Ω hoff hsteple hso)
      have hSuble := le_trans hcSub
        (subLoopClose (step * C.offset + bits.length) C.init.length Ω (by omega) hL)
      set K := Cmd.flatK (bsBody 0) with hK
      clear_value K
      set P2 := (Ω + 1) * (Ω + 1) with hP2
      have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
      have hKP2 : 0 ≤ K * P2 := Nat.zero_le _
      have hfin : (K + 60) * P2 = K * P2 + 60 * P2 := by ring
      omega
    · rw [heval, emitFalse_frame _ WREG (by decide), hw8WREG]
      exact hΩW

/-- Per-iteration effect of the inner final-step loop: cost + `WREG ≤ Ω`.
`u3` is the inner loop's entry state (one parsed final string in
`FBITS`/`BLEN`). Direct mirror of `stepIterBody_effect` one tag over. -/
private theorem finalStepIterBody_effect (C : BinaryCC) (bits : List Bool)
    (u3 : State) (Ω : Nat)
    (hSTEPSL : State.get u3 STEPSL = List.replicate (C.steps * C.init.length) 1)
    (hOFF : State.get u3 OFFSET = List.replicate C.offset 1)
    (hBLEN : State.get u3 BLEN = List.replicate bits.length 1)
    (hLREG : State.get u3 LREG = List.replicate C.init.length 1)
    (hFBITS : State.get u3 FBITS = FlatCCBinFree.bitsNat bits)
    (hΩOS : (State.get u3 OUT).length
        + (serF (encodeFinalString C bits)).length ≤ Ω)
    (hΩidxS : C.steps * C.init.length + C.init.length * C.offset
        + C.init.length + C.offset + bits.length + C.init.length ≤ Ω)
    (i : Nat) (hi : i < C.init.length + 1) (st : State)
    (hInv : FSInv C bits u3 i st) (hW : (State.get st WREG).length ≤ Ω) :
    finalStepIterBody.cost (st.set KFSTEP (List.replicate i 1))
        ≤ 4 + (Cmd.flatK (bsBody 0) + 60) * ((Ω + 1) * (Ω + 1))
    ∧ (State.get (finalStepIterBody.eval (st.set KFSTEP (List.replicate i 1))) WREG).length
        ≤ Ω := by
  obtain ⟨hOUT, hZ, hframe⟩ := hInv
  set w := st.set KFSTEP (List.replicate i 1) with hw
  have hwframe : ∀ r : Var, r ≠ KFSTEP → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwK : State.get w KFSTEP = List.replicate i 1 := State.get_set_eq _ _ _
  clear_value w
  set w1 := emitForrTag.eval w with hw1
  have hw1frame : ∀ r : Var, r ≠ OUT → State.get w1 r = State.get w r := by
    intro r hr; rw [hw1]; exact emitForrTag_frame w r hr
  have hw1OUT : State.get w1 OUT = State.get w OUT ++ [1, 0] := by
    rw [hw1, emitForrTag_run]; exact State.get_set_eq _ _ _
  clear_value w1
  -- thread the finalStepBody entry facts to w1
  have hchain : ∀ r : Var, r ≠ OUT → r ≠ KFSTEP →
      r ≠ SCAN → r ≠ WREG → r ≠ TFLG → r ≠ KBIT → r ≠ ZERO → r ≠ KTMP2 →
      r ≠ STEPO → r ≠ SUMW → r ≠ REM → r ≠ GFLG → r ≠ FSTART →
      State.get w1 r = State.get u3 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    rw [hw1frame r h1, hwframe r h2,
      hframe r h3 h1 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h2]
  have h1STEPSL : State.get w1 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
    rw [hchain STEPSL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hSTEPSL
  have h1KFSTEP : State.get w1 KFSTEP = List.replicate i 1 := by
    rw [hw1frame KFSTEP (by decide)]; exact hwK
  have h1OFF : State.get w1 OFFSET = List.replicate C.offset 1 := by
    rw [hchain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hOFF
  have h1BLEN : State.get w1 BLEN = List.replicate bits.length 1 := by
    rw [hchain BLEN (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hBLEN
  have h1LREG : State.get w1 LREG = List.replicate C.init.length 1 := by
    rw [hchain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hLREG
  have h1FBITS : State.get w1 FBITS = FlatCCBinFree.bitsNat bits := by
    rw [hchain FBITS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hFBITS
  have h1Z : State.get w1 ZERO = [] := by
    rw [hw1frame ZERO (by decide), hwframe ZERO (by decide)]; exact hZ
  have h1W : (State.get w1 WREG).length ≤ Ω := by
    rw [hw1frame WREG (by decide), hwframe WREG (by decide)]; exact hW
  -- the OUT ceiling at w1
  have h1OUTfull : State.get w1 OUT = State.get u3 OUT
      ++ orPrefix ((List.range i).map (fun step => encodeFinalAtStep C step bits))
      ++ [1, 0] := by
    rw [hw1OUT, hwframe OUT (by decide), hOUT]
  have hΩO1 : (State.get w1 OUT).length
      + (serF (encodeFinalAtStep C i bits)).length ≤ Ω := by
    have hsucc := orPrefix_range_succ (fun step => encodeFinalAtStep C step bits) i
    have hle := orPrefix_range_le (fun step => encodeFinalAtStep C step bits) (i + 1)
      (C.init.length + 1) hi
    have hstrC : serF (encodeFinalString C bits)
        = serF (listOr ((List.range (C.init.length + 1)).map
            (fun step => encodeFinalAtStep C step bits))) := rfl
    rw [hstrC] at hΩOS
    rw [h1OUTfull]
    have hlen : (orPrefix ((List.range (i + 1)).map
          (fun step => encodeFinalAtStep C step bits))).length
        = (orPrefix ((List.range i).map
            (fun step => encodeFinalAtStep C step bits))).length
          + (2 + (serF (encodeFinalAtStep C i bits)).length) := by
      rw [hsucc]
      simp [List.length_append]
      omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hΩidxi : C.steps * C.init.length + i * C.offset + i + C.offset
      + bits.length + C.init.length ≤ Ω := by
    have hiL : i ≤ C.init.length := by omega
    have hio : i * C.offset ≤ C.init.length * C.offset :=
      Nat.mul_le_mul_right _ hiL
    omega
  have hFB := finalStepBody_cost C i bits w1 Ω h1STEPSL h1KFSTEP h1OFF h1BLEN
    h1LREG h1FBITS h1Z hΩO1 h1W hΩidxi
  have hcost : finalStepIterBody.cost w = 1 + 3 + finalStepBody.cost w1 := by
    unfold finalStepIterBody
    rw [Cmd.cost_seq, emitForrTag_cost, ← hw1]
  have heval : finalStepIterBody.eval w = finalStepBody.eval w1 := by
    unfold finalStepIterBody
    rw [Cmd.eval_seq, ← hw1]
  constructor
  · rw [hcost]
    have h1 := hFB.1
    set B := (Cmd.flatK (bsBody 0) + 60) * ((Ω + 1) * (Ω + 1)) with hB
    clear_value B
    omega
  · rw [heval]
    exact hFB.2

/-- Per-iteration effect of the final-string loop: cost + `WREG ≤ Ω`. `u2` is
the loop's entry state (the final stream copied into `SCANF`). Mirror of
`lineBody_effect` with `cardEmitBody_effect`'s live/idle split over `FFInv`. -/
private theorem finalStringBody_effect (C : BinaryCC) (u2 : State) (Ω : Nat)
    (hSTEPSL : State.get u2 STEPSL = List.replicate (C.steps * C.init.length) 1)
    (hOFF : State.get u2 OFFSET = List.replicate C.offset 1)
    (hLREG : State.get u2 LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u2 LREG1 = List.replicate (C.init.length + 1) 1)
    (hΩO : (State.get u2 OUT).length
        + (serF (encodeFinalConstraint C)).length ≤ Ω)
    (hΩidx : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.init.length
        + (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length ≤ Ω)
    (j : Nat) (st : State)
    (hInv : FFInv C u2 j st) (hW : (State.get st WREG).length ≤ Ω) :
    finalStringBody.cost (st.set KFS (List.replicate j 1))
        ≤ (Cmd.flatK (bsBody 0) + Cmd.flatK readFinBody + 100)
            * ((Ω + 1) * ((Ω + 1) * (Ω + 1)))
    ∧ (State.get (finalStringBody.eval (st.set KFS (List.replicate j 1))) WREG).length
        ≤ Ω := by
  obtain ⟨hSCAN, hOUT, hZERO, hframe⟩ := hInv
  set w := st.set KFS (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KFS → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSCAN : State.get w SCANF
      = FlatTCCFree.encFinal ((C.final.drop j).map FlatCCBinFree.bitsNat) := by
    rw [hwframe SCANF (by decide)]; exact hSCAN
  have hwOUT : State.get w OUT
      = State.get u2 OUT ++ orPrefix ((C.final.take j).map (encodeFinalString C)) := by
    rw [hwframe OUT (by decide)]; exact hOUT
  have hwZ : State.get w ZERO = [] := by
    rw [hwframe ZERO (by decide)]; exact hZERO
  have hwW : (State.get w WREG).length ≤ Ω := by
    rw [hwframe WREG (by decide)]; exact hW
  -- the frozen per-tableau registers, recovered on `w`
  have hwchain : ∀ r : Var, r ≠ SCANF → r ≠ OUT → r ≠ WREG → r ≠ TFLG → r ≠ KBIT →
      r ≠ DONE → r ≠ EMARK → r ≠ ZERO → r ≠ KTMP → r ≠ KTMP2 → r ≠ FBITS →
      r ≠ BLEN → r ≠ SCAN → r ≠ STEPO → r ≠ SUMW → r ≠ REM → r ≠ GFLG →
      r ≠ FSTART → r ≠ KFSTEP → r ≠ KFS → State.get w r = State.get u2 r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
    rw [hwframe r h20,
      hframe r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20]
  have hwSTEPSL : State.get w STEPSL = List.replicate (C.steps * C.init.length) 1 := by
    rw [hwchain STEPSL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hSTEPSL
  have hwOFF : State.get w OFFSET = List.replicate C.offset 1 := by
    rw [hwchain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hOFF
  have hwLREG : State.get w LREG = List.replicate C.init.length 1 := by
    rw [hwchain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG
  have hwLREG1 : State.get w LREG1 = List.replicate (C.init.length + 1) 1 := by
    rw [hwchain LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hLREG1
  -- the drop-stream ceiling
  have hstream : (FlatTCCFree.encFinal ((C.final.drop j).map FlatCCBinFree.bitsNat)).length
      ≤ (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length := by
    rw [show (C.final.drop j).map FlatCCBinFree.bitsNat
        = (C.final.map FlatCCBinFree.bitsNat).drop j from List.map_drop ..]
    exact encFinal_drop_length_le _ j
  clear_value w
  by_cases hj : j < C.final.length
  · -- live iteration: parse one string, emit its step disjunction
    have hdrop : C.final.drop j = C.final[j] :: C.final.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    have htake : C.final.take (j + 1) = C.final.take j ++ [C.final[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    set bits := C.final[j] with hbits
    clear_value bits
    set REST := FlatTCCFree.encFinal ((C.final.drop (j + 1)).map FlatCCBinFree.bitsNat)
      with hREST
    have hSCANw : State.get w SCANF
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ REST := by
      rw [hwSCAN, hdrop, encFinal_cons, ← hREST]
    have hne : (State.get w SCANF).isEmpty = false := by
      rw [hSCANw]; exact encSList_append_isEmpty _ _
    -- the SCANF length ceiling (for readOneFinal's cost)
    have hSCANlen : (State.get w SCANF).length
        ≤ (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length := by
      rw [hwSCAN]
      exact hstream
    -- the parsed string's length ceiling
    have hbl : bits.length
        ≤ (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length := by
      have h1 : bits.length ≤ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length := by
        have h := encSList_length_ge (FlatCCBinFree.bitsNat bits)
        rw [show (FlatCCBinFree.bitsNat bits).length = bits.length from
          List.length_map _] at h
        exact h
      have h2 : (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits)).length
          ≤ (State.get w SCANF).length := by
        rw [hSCANw, List.length_append]
        omega
      omega
    -- w1: nonEmpty TFLG SCANF
    have e1 : (Cmd.op (.nonEmpty TFLG SCANF)).eval w = w.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    set w1 := w.set TFLG [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ TFLG → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1T : State.get w1 TFLG = [1] := State.get_set_eq _ _ _
    clear_value w1
    -- w2: the forr spine node
    set w2 := emitForrTag.eval w1 with hw2
    have hw2frame : ∀ r : Var, r ≠ OUT → State.get w2 r = State.get w1 r := by
      intro r hr; rw [hw2]; exact emitForrTag_frame w1 r hr
    have hw2OUT : State.get w2 OUT = State.get w1 OUT ++ [1, 0] := by
      rw [hw2, emitForrTag_run]; exact State.get_set_eq _ _ _
    clear_value w2
    have h2SCANF : State.get w2 SCANF
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bits) ++ REST := by
      rw [hw2frame SCANF (by decide), hw1frame SCANF (by decide)]; exact hSCANw
    have h2SCANFlen : (State.get w2 SCANF).length ≤ Ω := by
      rw [h2SCANF, ← hSCANw]
      omega
    -- w3: parse one final string (run + cost)
    have hcRead := readOneFinal_cost bits REST w2 Ω h2SCANF h2SCANFlen
    obtain ⟨h3SCANF, h3FBITS, h3BLEN, h3frame⟩ := readOneFinal_run bits REST w2 h2SCANF
    set w3 := readOneFinal.eval w2 with hw3
    clear_value w3
    have h3chain : ∀ r : Var, r ≠ SCANF → r ≠ FBITS → r ≠ BLEN → r ≠ DONE →
        r ≠ EMARK → r ≠ TFLG → r ≠ KTMP → r ≠ KTMP2 → r ≠ OUT →
        State.get w3 r = State.get w r := by
      intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [h3frame r h1 h2 h3 h4 h5 h6 h7 h8, hw2frame r h9, hw1frame r h6]
    have h3STEPSL : State.get w3 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
      rw [h3chain STEPSL (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwSTEPSL
    have h3OFF : State.get w3 OFFSET = List.replicate C.offset 1 := by
      rw [h3chain OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwOFF
    have h3LREG : State.get w3 LREG = List.replicate C.init.length 1 := by
      rw [h3chain LREG (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwLREG
    have h3LREG1 : State.get w3 LREG1 = List.replicate (C.init.length + 1) 1 := by
      rw [h3chain LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwLREG1
    have h3LREG1len : (State.get w3 LREG1).length = C.init.length + 1 := by
      rw [h3LREG1, List.length_replicate]
    have h3Z : State.get w3 ZERO = [] := by
      rw [h3chain ZERO (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwZ
    have h3W : (State.get w3 WREG).length ≤ Ω := by
      rw [h3chain WREG (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hwW
    have h3OUT : State.get w3 OUT = State.get u2 OUT
        ++ orPrefix ((C.final.take j).map (encodeFinalString C)) ++ [1, 0] := by
      rw [h3frame OUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), hw2OUT, hw1frame OUT (by decide), hwOUT]
    -- the string-level OUT ceiling at w3
    have hΩOS3 : (State.get w3 OUT).length
        + (serF (encodeFinalString C bits)).length ≤ Ω := by
      have hsnoc : orPrefix ((C.final.take (j + 1)).map (encodeFinalString C))
          = orPrefix ((C.final.take j).map (encodeFinalString C))
            ++ ([1, 0] ++ serF (encodeFinalString C bits)) := by
        rw [htake, List.map_append, orPrefix_append]
        simp [orPrefix]
      have htklen : (orPrefix ((C.final.take (j + 1)).map (encodeFinalString C))).length
          ≤ (serF (encodeFinalConstraint C)).length := by
        rw [show (C.final.take (j + 1)).map (encodeFinalString C)
            = (C.final.map (encodeFinalString C)).take (j + 1) from List.map_take ..]
        exact orPrefix_take_length_le _ (j + 1)
      have hlen : (orPrefix ((C.final.take (j + 1)).map (encodeFinalString C))).length
          = (orPrefix ((C.final.take j).map (encodeFinalString C))).length
            + (2 + (serF (encodeFinalString C bits)).length) := by
        rw [hsnoc]
        simp [List.length_append]
        omega
      rw [h3OUT]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hΩidxS3 : C.steps * C.init.length + C.init.length * C.offset
        + C.init.length + C.offset + bits.length + C.init.length ≤ Ω := by
      omega
    -- the inner step loop (cost + run + WREG)
    have hfsBase : FSInv C bits w3 0 w3 :=
      ⟨by simp [orPrefix], h3Z,
        fun r _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    have hcInner := Cmd.cost_forBnd_le KFSTEP LREG1 finalStepIterBody w3
      (4 + (Cmd.flatK (bsBody 0) + 60) * ((Ω + 1) * (Ω + 1)))
      (fun i stt => FSInv C bits w3 i stt ∧ (State.get stt WREG).length ≤ Ω)
      ⟨hfsBase, h3W⟩
      (fun i stt hi hM => by
        refine ⟨FSInv_step C bits w3 h3STEPSL h3OFF h3BLEN h3LREG h3FBITS i stt hM.1, ?_⟩
        exact (finalStepIterBody_effect C bits w3 Ω h3STEPSL h3OFF h3BLEN h3LREG
          h3FBITS hΩOS3 hΩidxS3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).2)
      (fun i stt hi hM =>
        (finalStepIterBody_effect C bits w3 Ω h3STEPSL h3OFF h3BLEN h3LREG
          h3FBITS hΩOS3 hΩidxS3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).1)
    have hwInner := Cmd.foldlState_range_induct finalStepIterBody KFSTEP
      (State.get w3 LREG1).length w3
      (fun i stt => FSInv C bits w3 i stt ∧ (State.get stt WREG).length ≤ Ω)
      ⟨hfsBase, h3W⟩
      (fun i stt hi hM => by
        refine ⟨FSInv_step C bits w3 h3STEPSL h3OFF h3BLEN h3LREG h3FBITS i stt hM.1, ?_⟩
        exact (finalStepIterBody_effect C bits w3 Ω h3STEPSL h3OFF h3BLEN h3LREG
          h3FBITS hΩOS3 hΩidxS3 i (by rw [h3LREG1len] at hi; exact hi) stt hM.1 hM.2).2)
    set w4 := (Cmd.forBnd KFSTEP LREG1 finalStepIterBody).eval w3 with hw4
    have hw4eval : w4 = Cmd.foldlState finalStepIterBody KFSTEP
        (List.range (State.get w3 LREG1).length) w3 := by
      rw [hw4, Cmd.eval_forBnd]
    have h4W : (State.get w4 WREG).length ≤ Ω := by
      rw [hw4eval]
      exact hwInner.2
    clear_value w4
    -- w5: close the inner listOr with falseFml
    set w5 := emitFalse.eval w4 with hw5
    have hw5W : (State.get w5 WREG).length ≤ Ω := by
      rw [hw5, emitFalse_frame _ WREG (by decide)]
      exact h4W
    clear_value w5
    -- assemble cost and eval
    have hcost : finalStringBody.cost w
        = 1 + 1 + (1 + (1 + 3 + (1 + readOneFinal.cost w2
            + (1 + (Cmd.forBnd KFSTEP LREG1 finalStepIterBody).cost w3 + 9)))) := by
      unfold finalStringBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_true _ _ _ _ hw1T,
        Cmd.cost_seq, emitForrTag_cost, ← hw2, Cmd.cost_seq, ← hw3, Cmd.cost_seq,
        ← hw4, emitFalse_cost]
      simp only [Op.cost]
    have heval : finalStringBody.eval w = w5 := by
      unfold finalStringBody
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_true _ _ _ _ hw1T, Cmd.eval_seq, ← hw2,
        Cmd.eval_seq, ← hw3, Cmd.eval_seq, ← hw4, ← hw5]
    constructor
    · rw [hcost]
      -- arithmetic
      have hLΩ : C.init.length ≤ Ω := by omega
      have hiters : (State.get w3 LREG1).length ≤ Ω + 1 := by
        rw [h3LREG1len]; omega
      set Kb := Cmd.flatK (bsBody 0) with hKb
      clear_value Kb
      set Kr := Cmd.flatK readFinBody with hKr
      clear_value Kr
      set P2 := (Ω + 1) * (Ω + 1) with hP2
      set P3 := (Ω + 1) * P2 with hP3
      set B := 4 + (Kb + 60) * P2 with hB
      have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
      have hBle : B ≤ (Kb + 64) * P2 := by
        rw [hB]
        have h4 : 4 ≤ 4 * P2 := by omega
        have he : 4 * P2 + (Kb + 60) * P2 = (Kb + 64) * P2 := by ring
        omega
      have hlB : (State.get w3 LREG1).length * B ≤ (Ω + 1) * ((Kb + 64) * P2) :=
        Nat.mul_le_mul hiters hBle
      have he3 : (Ω + 1) * ((Kb + 64) * P2) = (Kb + 64) * P3 := by
        rw [hP3]; ring
      have hii : (State.get w3 LREG1).length * (State.get w3 LREG1).length
          ≤ P2 := by
        rw [hP2]; exact Nat.mul_le_mul hiters hiters
      have hP23 : P2 ≤ P3 := by
        rw [hP3]; exact le_scale Ω P2
      have h1P3 : 1 ≤ P3 := le_trans h1P2 hP23
      have hrle : (Kr + 10) * P2 ≤ (Kr + 10) * P3 := Nat.mul_le_mul_left _ hP23
      have hfin : (Kb + Kr + 100) * P3
          = (Kb + 64) * P3 + (Kr + 10) * P3 + 26 * P3 := by ring
      omega
    · rw [heval]
      exact hw5W
  · -- idle iteration: stream exhausted, `nonEmpty` falls through
    have hlen : C.final.length ≤ j := Nat.le_of_not_lt hj
    have hSCANw : State.get w SCANF = [] := by
      rw [hwSCAN, List.drop_eq_nil_of_le hlen]; rfl
    have hne : (State.get w SCANF).isEmpty = true := by rw [hSCANw]; rfl
    have e1 : (Cmd.op (.nonEmpty TFLG SCANF)).eval w = w.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    have hw1Tne : State.get (w.set TFLG [0]) TFLG ≠ [1] := by
      rw [State.get_set_eq]; decide
    constructor
    · have hcost : finalStringBody.cost w = 1 + 1 + (1 + 1) := by
        unfold finalStringBody
        rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_false _ _ _ _ hw1Tne,
          Cmd.cost_op]
        simp only [Op.cost]
      rw [hcost]
      have h1P3 : 1 ≤ (Ω + 1) * ((Ω + 1) * (Ω + 1)) :=
        Nat.mul_pos (Nat.succ_pos Ω) (Nat.mul_pos (Nat.succ_pos Ω) (Nat.succ_pos Ω))
      calc 1 + 1 + (1 + 1) ≤ 100 * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) := by omega
        _ ≤ (Cmd.flatK (bsBody 0) + Cmd.flatK readFinBody + 100)
            * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) :=
          Nat.mul_le_mul_right _ (by omega)
    · have heval : finalStringBody.eval w = (w.set TFLG [0]).set KTMP [] := by
        unfold finalStringBody
        rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_false _ _ _ _ hw1Tne, Cmd.eval_op]
        simp only [Op.eval]
      rw [heval, State.get_set_ne _ _ _ _ (show WREG ≠ KTMP by decide),
        State.get_set_ne _ _ _ _ (show WREG ≠ TFLG by decide)]
      exact hwW

/-- **`emitFinal` cost**: quartic in the ceiling `Ω`, plus the `WREG ≤ Ω` exit
fact. `Ω` must dominate the entry `OUT` plus the full final-constraint
emission, the entry `WREG`, and the index/stream sums. -/
theorem emitFinal_cost (C : BinaryCC) (u : State) (Ω : Nat)
    (hSTEPS : State.get u STEPS = List.replicate C.steps 1)
    (hOFF : State.get u OFFSET = List.replicate C.offset 1)
    (hLREG : State.get u LREG = List.replicate C.init.length 1)
    (hLREG1 : State.get u LREG1 = List.replicate (C.init.length + 1) 1)
    (hFINAL : State.get u FINAL
        = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat))
    (hZ : State.get u ZERO = [])
    (hΩO : (State.get u OUT).length
        + (serF (encodeFinalConstraint C)).length ≤ Ω)
    (hΩW : (State.get u WREG).length ≤ Ω)
    (hΩidx : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.init.length + C.steps
        + (State.get u FINAL).length ≤ Ω) :
    emitFinal.cost u
        ≤ (Cmd.flatK (bsBody 0) + Cmd.flatK readFinBody + 140)
            * ((Ω + 1) * ((Ω + 1) * ((Ω + 1) * (Ω + 1))))
    ∧ (State.get (emitFinal.eval u) WREG).length ≤ Ω := by
  -- u0: clear STEPSL
  have e0clear : (Cmd.op (.clear STEPSL)).eval u = u.set STEPSL [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u0 := u.set STEPSL [] with hu0
  have hu0frame : ∀ r : Var, r ≠ STEPSL → State.get u0 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu0STEPSL : State.get u0 STEPSL = [] := State.get_set_eq _ _ _
  have hu0LREG : State.get u0 LREG = List.replicate C.init.length 1 := by
    rw [hu0frame LREG (by decide)]; exact hLREG
  have hu0STEPSlen : (State.get u0 STEPS).length = C.steps := by
    rw [hu0frame STEPS (by decide), hSTEPS, List.length_replicate]
  clear_value u0
  -- u1: STEPSL := 1^(steps·L) (run + cost)
  have hcMul := cost_mulLoop_le KTMP STEPS STEPSL LREG u0 0 C.init.length C.steps
    (by decide) (by decide) (by decide)
    (by rw [hu0STEPSL]; exact Nat.le_refl 0)
    (by rw [hu0LREG, List.length_replicate])
    hu0STEPSlen
  obtain ⟨h1STEPSL, h1mulframe⟩ :=
    unaryMulLoop_run KTMP STEPS LREG STEPSL u0 C.init.length C.steps
      (by decide) (by decide) (by decide) hu0LREG hu0STEPSlen hu0STEPSL
  set u1 := (Cmd.forBnd KTMP STEPS (Cmd.op (.concat STEPSL STEPSL LREG))).eval u0 with hu1
  clear_value u1
  have h1FINAL : State.get u1 FINAL
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := by
    rw [h1mulframe FINAL (by decide) (by decide), hu0frame FINAL (by decide)]
    exact hFINAL
  have h1FINALlen : (State.get u1 FINAL).length = (State.get u FINAL).length := by
    rw [h1FINAL, hFINAL]
  -- u2: copy SCANF FINAL (run + cost)
  have e2copy : (Cmd.op (.copy SCANF FINAL)).eval u1
      = u1.set SCANF (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, h1FINAL]
  have hc2 : Op.cost (.copy SCANF FINAL) u1 = (State.get u FINAL).length + 1 := by
    show (State.get u1 FINAL).length + 1 = _
    rw [h1FINALlen]
  set u2 := u1.set SCANF (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)) with hu2
  have hu2frame : ∀ r : Var, r ≠ SCANF → State.get u2 r = State.get u1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu2SCANF : State.get u2 SCANF
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := State.get_set_eq _ _ _
  clear_value u2
  have hu2chain : ∀ r : Var, r ≠ SCANF → r ≠ STEPSL → r ≠ KTMP →
      State.get u2 r = State.get u r := by
    intro r h1 h2 h3
    rw [hu2frame r h1, h1mulframe r h2 h3, hu0frame r h2]
  have h2STEPSL : State.get u2 STEPSL = List.replicate (C.steps * C.init.length) 1 := by
    rw [hu2frame STEPSL (by decide)]; exact h1STEPSL
  have h2OFF : State.get u2 OFFSET = List.replicate C.offset 1 := by
    rw [hu2chain OFFSET (by decide) (by decide) (by decide)]; exact hOFF
  have h2LREG : State.get u2 LREG = List.replicate C.init.length 1 := by
    rw [hu2chain LREG (by decide) (by decide) (by decide)]; exact hLREG
  have h2LREG1 : State.get u2 LREG1 = List.replicate (C.init.length + 1) 1 := by
    rw [hu2chain LREG1 (by decide) (by decide) (by decide)]; exact hLREG1
  have h2Z : State.get u2 ZERO = [] := by
    rw [hu2chain ZERO (by decide) (by decide) (by decide)]; exact hZ
  have h2OUT : State.get u2 OUT = State.get u OUT :=
    hu2chain OUT (by decide) (by decide) (by decide)
  have h2WREG : State.get u2 WREG = State.get u WREG :=
    hu2chain WREG (by decide) (by decide) (by decide)
  have h2FINAL : State.get u2 FINAL
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := by
    rw [hu2frame FINAL (by decide)]; exact h1FINAL
  have h2FINALlen : (State.get u2 FINAL).length = (State.get u FINAL).length := by
    rw [h2FINAL, hFINAL]
  have hΩO2 : (State.get u2 OUT).length
      + (serF (encodeFinalConstraint C)).length ≤ Ω := by
    rw [h2OUT]; exact hΩO
  have hΩW2 : (State.get u2 WREG).length ≤ Ω := by
    rw [h2WREG]; exact hΩW
  have hΩidx2 : C.steps * C.init.length + C.init.length * C.offset + C.init.length
      + C.offset + C.init.length
      + (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length ≤ Ω := by
    rw [← hFINAL]; omega
  -- the string loop (cost + WREG)
  have hffBase : FFInv C u2 0 u2 := by
    refine ⟨by rw [List.drop_zero]; exact hu2SCANF, ?_, h2Z,
      fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    rw [List.take_zero, List.map_nil, show orPrefix [] = [] from rfl, List.append_nil]
  have hloop := Cmd.cost_forBnd_le KFS FINAL finalStringBody u2
    ((Cmd.flatK (bsBody 0) + Cmd.flatK readFinBody + 100)
      * ((Ω + 1) * ((Ω + 1) * (Ω + 1))))
    (fun j st => FFInv C u2 j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨hffBase, hΩW2⟩
    (fun j st hj hM => by
      refine ⟨FFInv_step C u2 h2STEPSL h2OFF h2LREG h2LREG1 j st hM.1, ?_⟩
      exact (finalStringBody_effect C u2 Ω h2STEPSL h2OFF h2LREG h2LREG1
        hΩO2 hΩidx2 j st hM.1 hM.2).2)
    (fun j st hj hM =>
      (finalStringBody_effect C u2 Ω h2STEPSL h2OFF h2LREG h2LREG1
        hΩO2 hΩidx2 j st hM.1 hM.2).1)
  have hwLoop := Cmd.foldlState_range_induct finalStringBody KFS
    (State.get u2 FINAL).length u2
    (fun j st => FFInv C u2 j st ∧ (State.get st WREG).length ≤ Ω)
    ⟨hffBase, hΩW2⟩
    (fun j st hj hM => by
      refine ⟨FFInv_step C u2 h2STEPSL h2OFF h2LREG h2LREG1 j st hM.1, ?_⟩
      exact (finalStringBody_effect C u2 Ω h2STEPSL h2OFF h2LREG h2LREG1
        hΩO2 hΩidx2 j st hM.1 hM.2).2)
  -- assemble cost and eval
  have hcost : emitFinal.cost u
      = 1 + 1 + (1 + (Cmd.forBnd KTMP STEPS (Cmd.op (.concat STEPSL STEPSL LREG))).cost u0
        + (1 + Op.cost (.copy SCANF FINAL) u1
        + (1 + (Cmd.forBnd KFS FINAL finalStringBody).cost u2 + 9))) := by
    unfold emitFinal
    rw [Cmd.cost_seq, Cmd.cost_op, e0clear, Cmd.cost_seq, ← hu1, Cmd.cost_seq,
      Cmd.cost_op, e2copy, Cmd.cost_seq, emitFalse_cost]
    simp only [Op.cost]
  have heval : emitFinal.eval u
      = emitFalse.eval (Cmd.foldlState finalStringBody KFS
          (List.range (State.get u2 FINAL).length) u2) := by
    unfold emitFinal
    rw [Cmd.eval_seq, e0clear, Cmd.eval_seq, ← hu1, Cmd.eval_seq, e2copy, Cmd.eval_seq,
      Cmd.eval_forBnd]
  constructor
  · rw [hcost, hc2]
    -- arithmetic
    have hlenΩ : (State.get u FINAL).length ≤ Ω := by omega
    have hL : C.init.length ≤ Ω := by omega
    have hsteps : C.steps ≤ Ω := by omega
    have hsL : C.steps * C.init.length ≤ Ω := by omega
    have hMulle := le_trans hcMul (mulLoopClose C.init.length C.steps Ω hL hsteps hsL)
    have hlen2 : (State.get u2 FINAL).length ≤ Ω := by
      rw [h2FINALlen]; omega
    set Kb := Cmd.flatK (bsBody 0) with hKb
    clear_value Kb
    set Kr := Cmd.flatK readFinBody with hKr
    clear_value Kr
    set P2 := (Ω + 1) * (Ω + 1) with hP2
    set P3 := (Ω + 1) * P2 with hP3
    set P4 := (Ω + 1) * P3 with hP4
    have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
    have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
    have hP34 : P3 ≤ P4 := by rw [hP4]; exact le_scale Ω P3
    have h1P4 : 1 ≤ P4 := le_trans h1P2 (le_trans hP23 hP34)
    have hlB : (State.get u2 FINAL).length * ((Kb + Kr + 100) * P3)
        ≤ (Ω + 1) * ((Kb + Kr + 100) * P3) :=
      Nat.mul_le_mul_right _ (by omega)
    have he4 : (Ω + 1) * ((Kb + Kr + 100) * P3) = (Kb + Kr + 100) * P4 := by
      rw [hP4]; ring
    have hll : (State.get u2 FINAL).length * (State.get u2 FINAL).length
        ≤ Ω * Ω := Nat.mul_le_mul hlen2 hlen2
    have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
    have hMul4 : 7 * P2 ≤ 7 * P4 :=
      Nat.mul_le_mul_left _ (le_trans hP23 hP34)
    have hΩ1P4 : Ω + 1 ≤ P4 := by
      calc Ω + 1 = (Ω + 1) * 1 := by ring
        _ ≤ (Ω + 1) * P3 := Nat.mul_le_mul_left _ (le_trans h1P2 hP23)
        _ = P4 := by rw [hP4]
    have hP24 : P2 ≤ P4 := le_trans hP23 hP34
    have hfin : (Kb + Kr + 140) * P4 = (Kb + Kr + 100) * P4 + 40 * P4 := by ring
    omega
  · rw [heval, emitFalse_frame _ WREG (by decide)]
    exact hwLoop.2

/-! ### The wellformedness guard: cost -/

private theorem andFlag_cost (FLG : Nat) (s : State) : (andFlag FLG).cost s = 2 := by
  unfold andFlag
  by_cases hT : State.get s FLG = [1]
  · rw [Cmd.cost_ifBit_true _ _ _ _ hT, Cmd.cost_op]
    simp only [Op.cost]
  · rw [Cmd.cost_ifBit_false _ _ _ _ hT, Cmd.cost_op]
    simp only [Op.cost]

/-- `andFlag` writes only `ZERO`/`GWF` — the hypothesis-free frame fact. -/
private theorem andFlag_frame' (FLG : Nat) (s : State) (r : Var)
    (h1 : r ≠ ZERO) (h2 : r ≠ GWF) :
    State.get ((andFlag FLG).eval s) r = State.get s r := by
  unfold andFlag
  by_cases hT : State.get s FLG = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hT, Cmd.eval_op]
    simp only [Op.eval]
    exact State.get_set_ne _ _ _ _ h1
  · rw [Cmd.eval_ifBit_false _ _ _ _ hT, Cmd.eval_op]
    simp only [Op.eval]
    exact State.get_set_ne _ _ _ _ h2

/-- `andFlag` keeps `ZERO` empty (either branch). -/
private theorem andFlag_ZERO (FLG : Nat) (s : State) (h : State.get s ZERO = []) :
    State.get ((andFlag FLG).eval s) ZERO = [] := by
  unfold andFlag
  by_cases hT : State.get s FLG = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hT, Cmd.eval_op]
    simp only [Op.eval]
    exact State.get_set_eq _ _ _
  · rw [Cmd.eval_ifBit_false _ _ _ _ hT, Cmd.eval_op]
    simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ (show ZERO ≠ GWF by decide)]
    exact h

/-- The final `TFLG`-flip of `leCheck`/`dvdCheck` costs at most 4. -/
private theorem tflgFlip_cost_le (s : State) :
    (Cmd.ifBit TFLG (Cmd.op (.clear TFLG))
      (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))).cost s ≤ 4 := by
  by_cases hT : State.get s TFLG = [1]
  · rw [Cmd.cost_ifBit_true _ _ _ _ hT, Cmd.cost_op]
    simp only [Op.cost]
    omega
  · rw [Cmd.cost_ifBit_false _ _ _ _ hT, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
    simp only [Op.cost]
    omega

/-- **`leCheck` cost**: quadratic in the ceiling `Ω ≥ a, b`. -/
theorem leCheck_cost (X Y : Var) (a b : Nat) (s : State) (Ω : Nat)
    (hYM : Y ≠ MREM)
    (hX : State.get s X = List.replicate a 1)
    (hY : (State.get s Y).length = b)
    (hΩa : a ≤ Ω) (hΩb : b ≤ Ω) :
    (leCheck X Y).cost s ≤ 12 * ((Ω + 1) * (Ω + 1)) := by
  have e1 : (Cmd.op (.copy MREM X)).eval s = s.set MREM (List.replicate a 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hX]
  have hc1 : Op.cost (.copy MREM X) s = a + 1 := by
    show (State.get s X).length + 1 = _
    rw [hX, List.length_replicate]
  set w1 := s.set MREM (List.replicate a 1) with hw1
  have hw1M : State.get w1 MREM = List.replicate a 1 := State.get_set_eq _ _ _
  have hw1Y : (State.get w1 Y).length = b := by
    rw [State.get_set_ne _ _ _ _ hYM]; exact hY
  clear_value w1
  have hcSub := cost_tailLoop_le MGE Y MREM w1 a b (by decide)
    (by rw [hw1M, List.length_replicate]) hw1Y
  set w2 := (Cmd.forBnd MGE Y (Cmd.op (.tail MREM MREM))).eval w1 with hw2
  clear_value w2
  set w3 := (Cmd.op (.nonEmpty TFLG MREM)).eval w2 with hw3
  clear_value w3
  have hc4 := tflgFlip_cost_le w3
  have hcost : (leCheck X Y).cost s
      = 1 + Op.cost (.copy MREM X) s
        + (1 + (Cmd.forBnd MGE Y (Cmd.op (.tail MREM MREM))).cost w1
        + (1 + (Cmd.op (.nonEmpty TFLG MREM)).cost w2
        + (Cmd.ifBit TFLG (Cmd.op (.clear TFLG))
            (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))).cost w3)) := by
    unfold leCheck
    rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq, ← hw3]
  have hc3 : (Cmd.op (.nonEmpty TFLG MREM)).cost w2 = 1 := by
    rw [Cmd.cost_op]
    simp only [Op.cost]
  have hSuble := le_trans hcSub (subLoopClose a b Ω hΩa hΩb)
  rw [hcost, hc1, hc3]
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
  have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
  omega

/-- Per-iteration cost of `dvdCheck`'s outer loop: quadratic in `Ω ≥ a, d`. -/
private theorem dvdBody_effect (a d : Nat) (D : Var) (u : State) (Ω : Nat)
    (hDM : D ≠ MREM) (hDC : D ≠ MCHK) (hDG : D ≠ MGE) (hDK : D ≠ KTMP)
    (hDK2 : D ≠ KTMP2) (hDZ : D ≠ ZERO)
    (hUD : State.get u D = List.replicate d 1)
    (hΩa : a ≤ Ω) (hΩd : d ≤ Ω)
    (j : Nat) (st : State) (h : DInv a d u j st) :
    (dvdBody D).cost (st.set KTMP (List.replicate j 1))
      ≤ 12 * ((Ω + 1) * (Ω + 1)) := by
  obtain ⟨hMREM, hZ, hframe⟩ := h
  set w := st.set KTMP (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KTMP → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwM : State.get w MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hwframe MREM (by decide)]; exact hMREM
  have hwD : State.get w D = List.replicate d 1 := by
    rw [hwframe D hDK, hframe D hDM hDC hDG hDK hDK2 hDZ]; exact hUD
  clear_value w
  have hsub_le : DvdArith.subMod a d j ≤ a := DvdArith.subMod_le a d j
  -- step 1: copy MCHK D
  have e1 : (Cmd.op (.copy MCHK D)).eval w = w.set MCHK (List.replicate d 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hwD]
  have hc1 : Op.cost (.copy MCHK D) w = d + 1 := by
    show (State.get w D).length + 1 = _
    rw [hwD, List.length_replicate]
  set w1 := w.set MCHK (List.replicate d 1) with hw1
  have hw1frame : ∀ r : Var, r ≠ MCHK → State.get w1 r = State.get w r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw1C : State.get w1 MCHK = List.replicate d 1 := State.get_set_eq _ _ _
  have hw1M : State.get w1 MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hw1frame MREM (by decide)]; exact hwM
  clear_value w1
  -- step 2: inner sub loop  MCHK -= |MREM|
  have hcSub1 := cost_tailLoop_le KTMP2 MREM MCHK w1 d (DvdArith.subMod a d j)
    (by decide)
    (by rw [hw1C, List.length_replicate])
    (by rw [hw1M, List.length_replicate])
  obtain ⟨hsubC, hsubF⟩ := unarySubLoop_run KTMP2 MREM MCHK w1 d
    (DvdArith.subMod a d j) (by decide)
    (by rw [hw1M, List.length_replicate]) hw1C
  set w2 := (Cmd.forBnd KTMP2 MREM (Cmd.op (.tail MCHK MCHK))).eval w1 with hw2
  have hw2M : State.get w2 MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hsubF MREM (by decide) (by decide)]; exact hw1M
  have hw2D : State.get w2 D = List.replicate d 1 := by
    rw [hsubF D hDC hDK2, hw1frame D hDC]; exact hwD
  clear_value w2
  -- step 3: nonEmpty MGE MCHK
  have e3 : (Cmd.op (.nonEmpty MGE MCHK)).eval w2
      = w2.set MGE (if (List.replicate (d - DvdArith.subMod a d j) 1 : List Nat).isEmpty
          then [0] else [1]) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hsubC]
  set w3 := w2.set MGE (if (List.replicate (d - DvdArith.subMod a d j) 1 : List Nat).isEmpty
      then [0] else [1]) with hw3
  have hw3frame : ∀ r : Var, r ≠ MGE → State.get w3 r = State.get w2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hw3M : State.get w3 MREM = List.replicate (DvdArith.subMod a d j) 1 := by
    rw [hw3frame MREM (by decide)]; exact hw2M
  have hw3D : State.get w3 D = List.replicate d 1 := by
    rw [hw3frame D hDG]; exact hw2D
  clear_value w3
  -- step 4: the branch
  have hcBranch : (Cmd.ifBit MGE (Cmd.op (.clear ZERO))
      (Cmd.forBnd KTMP2 D (Cmd.op (.tail MREM MREM)))).cost w3
      ≤ 1 + 3 * ((Ω + 1) * (Ω + 1)) := by
    by_cases hG : State.get w3 MGE = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ hG, Cmd.cost_op]
      simp only [Op.cost]
      have h1P2 : 1 ≤ (Ω + 1) * (Ω + 1) := one_le_P Ω
      omega
    · rw [Cmd.cost_ifBit_false _ _ _ _ hG]
      have hcSub2 := cost_tailLoop_le KTMP2 D MREM w3 (DvdArith.subMod a d j) d
        (by decide)
        (by rw [hw3M, List.length_replicate])
        (by rw [hw3D, List.length_replicate])
      exact Nat.add_le_add_left
        (le_trans hcSub2 (subLoopClose (DvdArith.subMod a d j) d Ω (by omega) hΩd)) 1
  have hcost : (dvdBody D).cost w
      = 1 + Op.cost (.copy MCHK D) w
        + (1 + (Cmd.forBnd KTMP2 MREM (Cmd.op (.tail MCHK MCHK))).cost w1
        + (1 + (Cmd.op (.nonEmpty MGE MCHK)).cost w2
        + (Cmd.ifBit MGE (Cmd.op (.clear ZERO))
            (Cmd.forBnd KTMP2 D (Cmd.op (.tail MREM MREM)))).cost w3)) := by
    unfold dvdBody
    rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq, e3]
  have hc3 : (Cmd.op (.nonEmpty MGE MCHK)).cost w2 = 1 := by
    rw [Cmd.cost_op]
    simp only [Op.cost]
  have hSuble1 := le_trans hcSub1 (subLoopClose d (DvdArith.subMod a d j) Ω hΩd (by omega))
  rw [hcost, hc1, hc3]
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
  have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
  omega

/-- **`dvdCheck` cost**: cubic in the ceiling `Ω ≥ a, d`. -/
theorem dvdCheck_cost (X D : Var) (a d : Nat) (s : State) (Ω : Nat)
    (hXM : X ≠ MREM)
    (hDM : D ≠ MREM) (hDC : D ≠ MCHK) (hDG : D ≠ MGE) (hDK : D ≠ KTMP)
    (hDK2 : D ≠ KTMP2) (hDZ : D ≠ ZERO)
    (hX : State.get s X = List.replicate a 1)
    (hD : State.get s D = List.replicate d 1)
    (hZ : State.get s ZERO = [])
    (hΩa : a ≤ Ω) (hΩd : d ≤ Ω) :
    (dvdCheck X D).cost s ≤ 30 * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) := by
  have e1 : (Cmd.op (.copy MREM X)).eval s = s.set MREM (List.replicate a 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hX]
  have hc1 : Op.cost (.copy MREM X) s = a + 1 := by
    show (State.get s X).length + 1 = _
    rw [hX, List.length_replicate]
  set u := s.set MREM (List.replicate a 1) with hu
  have huframe : ∀ r : Var, r ≠ MREM → State.get u r = State.get s r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have huM : State.get u MREM = List.replicate a 1 := State.get_set_eq _ _ _
  have huD : State.get u D = List.replicate d 1 := by rw [huframe D hDM]; exact hD
  have huZ : State.get u ZERO = [] := by rw [huframe ZERO (by decide)]; exact hZ
  have huX : State.get u X = List.replicate a 1 := by rw [huframe X hXM]; exact hX
  have huXlen : (State.get u X).length = a := by rw [huX, List.length_replicate]
  clear_value u
  have hbase : DInv a d u 0 u := by
    refine ⟨by rw [huM]; rfl, huZ, fun r _ _ _ _ _ _ => rfl⟩
  have hloop := Cmd.cost_forBnd_le KTMP X (dvdBody D) u
    (12 * ((Ω + 1) * (Ω + 1)))
    (DInv a d u) hbase
    (fun j st _ hM => dvdBody_step a d D u hDM hDC hDG hDK hDK2 hDZ huD j st hM)
    (fun j st _ hM => dvdBody_effect a d D u Ω hDM hDC hDG hDK hDK2 hDZ huD
      hΩa hΩd j st hM)
  set w2 := (Cmd.forBnd KTMP X (dvdBody D)).eval u with hw2
  clear_value w2
  set w3 := (Cmd.op (.nonEmpty TFLG MREM)).eval w2 with hw3
  clear_value w3
  have hc4 := tflgFlip_cost_le w3
  have hcost : (dvdCheck X D).cost s
      = 1 + Op.cost (.copy MREM X) s
        + (1 + (Cmd.forBnd KTMP X (dvdBody D)).cost u
        + (1 + (Cmd.op (.nonEmpty TFLG MREM)).cost w2
        + (Cmd.ifBit TFLG (Cmd.op (.clear TFLG))
            (Cmd.op (.clear TFLG) ;; Cmd.op (.appendOne TFLG))).cost w3)) := by
    unfold dvdCheck
    rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq, ← hw3]
  have hc3 : (Cmd.op (.nonEmpty TFLG MREM)).cost w2 = 1 := by
    rw [Cmd.cost_op]
    simp only [Op.cost]
  rw [hcost, hc1, hc3]
  rw [huXlen] at hloop
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  set P3 := (Ω + 1) * P2 with hP3
  have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
  have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
  have haB : a * (12 * P2) ≤ (Ω + 1) * (12 * P2) :=
    Nat.mul_le_mul_right _ (by omega)
  have he3 : (Ω + 1) * (12 * P2) = 12 * P3 := by rw [hP3]; ring
  have haa : a * a ≤ Ω * Ω := Nat.mul_le_mul hΩa hΩa
  have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
  have h1P3 : 1 ≤ P3 := le_trans h1P2 hP23
  omega

/-! ### `cardLenCheck`: cost -/

/-- **`cardLenItem` cost**: quadratic in `Ω ≥ |SCANW|, width`. -/
theorem cardLenItem_cost (bs : List Bool) (rest : List Nat) (width : Nat)
    (u : State) (Ω : Nat)
    (hSC : State.get u SCANW = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs) ++ rest)
    (hW : State.get u WIDTH = List.replicate width 1)
    (hΩS : (State.get u SCANW).length ≤ Ω)
    (hΩw : width ≤ Ω) :
    cardLenItem.cost u
      ≤ (Cmd.flatK cardLenElemBody + 20) * ((Ω + 1) * (Ω + 1)) := by
  have e01 : (Cmd.op (.clear CLEN)).eval u = u.set CLEN [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u1 := u.set CLEN [] with hu1
  have hu1frame : ∀ r : Var, r ≠ CLEN → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  clear_value u1
  have e02 : (Cmd.op (.clear DONE)).eval u1 = u1.set DONE [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u2 := u1.set DONE [] with hu2
  have hu2frame : ∀ r : Var, r ≠ DONE → State.get u2 r = State.get u1 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu2SC : State.get u2 SCANW
      = FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs) ++ rest := by
    rw [hu2frame SCANW (by decide), hu1frame SCANW (by decide)]; exact hSC
  have hu2CL : State.get u2 CLEN = [] := by
    rw [hu2frame CLEN (by decide), hu1]; exact State.get_set_eq _ _ _
  have hu2D : State.get u2 DONE = [] := State.get_set_eq _ _ _
  have hu2W : State.get u2 WIDTH = List.replicate width 1 := by
    rw [hu2frame WIDTH (by decide), hu1frame WIDTH (by decide)]; exact hW
  have hu2SClen : (State.get u2 SCANW).length = (State.get u SCANW).length := by
    rw [hu2SC, hSC]
  clear_value u2
  have hN : bs.length < (State.get u2 SCANW).length := by
    rw [hu2SC, List.length_append, FlatTCCFree.encSList_length,
      show (FlatCCBinFree.bitsNat bs).length = bs.length from List.length_map _]
    omega
  -- the SCANW ceiling in both parse phases
  have hsuffix : ∀ i : Nat,
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bs.drop i))).length + rest.length
        ≤ Ω := by
    intro i
    have h1 : (FlatTCCFree.encSList (FlatCCBinFree.bitsNat (bs.drop i))).length
        ≤ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs)).length := by
      rw [show FlatCCBinFree.bitsNat (bs.drop i)
          = (FlatCCBinFree.bitsNat bs).drop i from List.map_drop ..]
      exact encSList_drop_length_le _ i
    have h2 : (State.get u SCANW).length
        = (FlatTCCFree.encSList (FlatCCBinFree.bitsNat bs)).length + rest.length := by
      rw [hSC, List.length_append]
    omega
  have hbase : CEInv bs rest u2 0 u2 := by
    refine ⟨fun _ => ⟨hu2D, by rw [List.drop_zero]; exact hu2SC, hu2CL⟩,
      fun hlt => absurd hlt (Nat.not_lt_zero _), fun r _ _ _ _ _ _ _ => rfl⟩
  -- the loop: cost + exit facts
  have hloop := Cmd.cost_forBnd_le KBIT SCANW cardLenElemBody u2
    (Cmd.flatK cardLenElemBody * (Ω + 1))
    (CEInv bs rest u2) hbase
    (fun i st _ hM => CEInv_step bs rest u2 i st hM)
    (fun i st hi hM => by
      obtain ⟨hph1, hph2, hframei⟩ := hM
      have hread : ∀ r ∈ Cmd.costReads cardLenElemBody,
          (State.get (st.set KBIT (List.replicate i 1)) r).length ≤ Ω := by
        intro r hr
        have hlist : Cmd.costReads cardLenElemBody
            = [SCANW, SCANW, SCANW, SCANW, SCANW] := rfl
        rw [hlist] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hSCANce : (State.get st SCANW).length ≤ Ω := by
          by_cases hile : i ≤ bs.length
          · obtain ⟨-, hS, -⟩ := hph1 hile
            rw [hS, List.length_append]
            exact hsuffix i
          · obtain ⟨-, hS, -⟩ := hph2 (by omega)
            rw [hS]
            have := hsuffix 0
            omega
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          (rw [State.get_set_ne _ _ _ _ (show SCANW ≠ KBIT by decide)]; exact hSCANce)
      exact (Cmd.cost_le_flat cardLenElemBody rfl
        (st.set KBIT (List.replicate i 1)) Ω hread).1)
  have hInv : CEInv bs rest u2 (State.get u2 SCANW).length
      (Cmd.foldlState cardLenElemBody KBIT
        (List.range (State.get u2 SCANW).length) u2) :=
    Cmd.foldlState_range_induct _ KBIT _ u2 (CEInv bs rest u2) hbase
      (fun i st _ hM => CEInv_step bs rest u2 i st hM)
  obtain ⟨-, hph2, hLframe⟩ := hInv
  obtain ⟨-, -, hLCL⟩ := hph2 hN
  set w2 := Cmd.foldlState cardLenElemBody KBIT
      (List.range (State.get u2 SCANW).length) u2 with hw2
  clear_value w2
  have hw2W : State.get w2 WIDTH = List.replicate width 1 := by
    rw [hLframe WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hu2W
  -- eqBit cost off the exit lengths
  have hc3 : Op.cost (.eqBit TFLG CLEN WIDTH) w2 = bs.length + width + 1 := by
    show (State.get w2 CLEN).length + (State.get w2 WIDTH).length + 1 = _
    rw [hLCL, hw2W, List.length_replicate, List.length_replicate]
  set w3 := (Cmd.op (.eqBit TFLG CLEN WIDTH)).eval w2 with hw3
  clear_value w3
  have hc4 := andFlag_cost TFLG w3
  have hloopeval : (Cmd.forBnd KBIT SCANW cardLenElemBody).eval u2 = w2 := by
    rw [Cmd.eval_forBnd, hw2]
  have hcost : cardLenItem.cost u
      = 1 + 1 + (1 + 1 + (1 + (Cmd.forBnd KBIT SCANW cardLenElemBody).cost u2
        + (1 + Op.cost (.eqBit TFLG CLEN WIDTH) w2 + (andFlag TFLG).cost w3))) := by
    unfold cardLenItem
    rw [Cmd.cost_seq, Cmd.cost_op, e01, Cmd.cost_seq, Cmd.cost_op, e02, Cmd.cost_seq,
      Cmd.cost_seq, Cmd.cost_op, hloopeval, ← hw3]
    simp only [Op.cost]
  rw [hcost, hc3, hc4]
  -- close the arithmetic
  have hblen : bs.length ≤ Ω := by
    have := hN
    rw [hu2SClen] at this
    omega
  have hlen : (State.get u2 SCANW).length ≤ Ω := by rw [hu2SClen]; omega
  set K := Cmd.flatK cardLenElemBody with hK
  clear_value K
  set A := K * (Ω + 1) with hA
  set len := (State.get u2 SCANW).length with hlenDef
  have h1 : len * A ≤ (Ω + 1) * A := Nat.mul_le_mul_right A (by omega)
  have h2 : len * len ≤ Ω * Ω := Nat.mul_le_mul hlen hlen
  have h3 : (Ω + 1) * A = K * ((Ω + 1) * (Ω + 1)) := by rw [hA]; ring
  have h4 : (K + 20) * ((Ω + 1) * (Ω + 1))
      = K * ((Ω + 1) * (Ω + 1)) + 20 * ((Ω + 1) * (Ω + 1)) := by ring
  have h5 : (Ω + 1) * (Ω + 1) = Ω * Ω + 2 * Ω + 1 := by ring
  omega

/-- Per-iteration cost of `cardLenCheck`'s card loop. -/
private theorem cardLenCardBody_effect (C : BinaryCC) (width : Nat) (g0 : List Nat)
    (u1 : State) (Ω : Nat)
    (hΩS : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length ≤ Ω)
    (hΩw : width ≤ Ω)
    (j : Nat) (st : State) (hInv : CLInv C width g0 u1 j st) :
    cardLenCardBody.cost (st.set KCARD (List.replicate j 1))
      ≤ 6 + 2 * ((Cmd.flatK cardLenElemBody + 20) * ((Ω + 1) * (Ω + 1))) := by
  obtain ⟨hSCAN, hGWF, hWID, hframe⟩ := hInv
  set w := st.set KCARD (List.replicate j 1) with hw
  have hwframe : ∀ r : Var, r ≠ KCARD → State.get w r = State.get st r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hwSCAN : State.get w SCANW
      = FlatTCCFree.encCardsOut ((C.cards.drop j).map FlatCCBinFree.cardNat) := by
    rw [hwframe SCANW (by decide)]; exact hSCAN
  have hwWID : State.get w WIDTH = List.replicate width 1 := by
    rw [hwframe WIDTH (by decide)]; exact hWID
  -- the drop-stream ceiling
  have hstream : (FlatTCCFree.encCardsOut ((C.cards.drop j).map FlatCCBinFree.cardNat)).length
      ≤ (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length := by
    rw [show (C.cards.drop j).map FlatCCBinFree.cardNat
        = (C.cards.map FlatCCBinFree.cardNat).drop j from List.map_drop ..]
    exact encCardsOut_drop_length_le _ j
  clear_value w
  by_cases hj : j < C.cards.length
  · -- live: parse prem then conc
    have hdrop : C.cards.drop j = C.cards[j] :: C.cards.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    set c := C.cards[j] with hc
    clear_value c
    set REST := FlatTCCFree.encCardsOut ((C.cards.drop (j + 1)).map FlatCCBinFree.cardNat)
      with hREST
    have hwSCANc : State.get w SCANW
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
          ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hwSCAN, hdrop, encCardsOut_cons, hREST]
    have hne : (State.get w SCANW).isEmpty = false := by
      rw [hwSCANc]; exact encSList_append_isEmpty _ _
    have hwSCANlen : (State.get w SCANW).length ≤ Ω := by
      rw [hwSCAN]
      omega
    have e1 : (Cmd.op (.nonEmpty TFLG SCANW)).eval w = w.set TFLG [1] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    set w1 := w.set TFLG [1] with hw1
    have hw1frame : ∀ r : Var, r ≠ TFLG → State.get w1 r = State.get w r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hw1T : State.get w1 TFLG = [1] := State.get_set_eq _ _ _
    have hw1SCAN : State.get w1 SCANW
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)
          ++ (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) := by
      rw [hw1frame SCANW (by decide)]; exact hwSCANc
    have hw1WID : State.get w1 WIDTH = List.replicate width 1 := by
      rw [hw1frame WIDTH (by decide)]; exact hwWID
    have hw1SCANlen : (State.get w1 SCANW).length ≤ Ω := by
      rw [hw1SCAN, ← hwSCANc]
      exact hwSCANlen
    clear_value w1
    -- the prem item: cost + run
    have hcost1 := cardLenItem_cost c.prem
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST) width w1 Ω
      hw1SCAN hw1WID hw1SCANlen hΩw
    obtain ⟨hp1SC, -, hp1F⟩ := cardLenItem_run c.prem
      (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST)
      width (State.get w1 GWF) w1 hw1SCAN hw1WID rfl
    set w2 := cardLenItem.eval w1 with hw2
    have hw2SC : State.get w2 SCANW
        = FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST := hp1SC
    have hw2WID : State.get w2 WIDTH = List.replicate width 1 := by
      rw [hp1F WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
      exact hw1WID
    have hw2SClen : (State.get w2 SCANW).length ≤ Ω := by
      rw [hw2SC]
      have : (State.get w1 SCANW).length
          = (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.prem)).length
            + (FlatTCCFree.encSList (FlatCCBinFree.bitsNat c.conc) ++ REST).length := by
        rw [hw1SCAN, List.length_append]
      omega
    clear_value w2
    -- the conc item: cost
    have hcost2 := cardLenItem_cost c.conc REST width w2 Ω hw2SC hw2WID hw2SClen hΩw
    have hcost : cardLenCardBody.cost w
        = 1 + 1 + (1 + (1 + cardLenItem.cost w1 + cardLenItem.cost w2)) := by
      unfold cardLenCardBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_true _ _ _ _ hw1T,
        Cmd.cost_seq, ← hw2]
      simp only [Op.cost]
    rw [hcost]
    set KK := (Cmd.flatK cardLenElemBody + 20) * ((Ω + 1) * (Ω + 1)) with hKK
    clear_value KK
    omega
  · -- idle: stream exhausted
    have hlen : C.cards.length ≤ j := Nat.le_of_not_lt hj
    have hwSCANe : State.get w SCANW = [] := by
      rw [hwSCAN, List.drop_eq_nil_of_le hlen]; rfl
    have hne : (State.get w SCANW).isEmpty = true := by rw [hwSCANe]; rfl
    have e1 : (Cmd.op (.nonEmpty TFLG SCANW)).eval w = w.set TFLG [0] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hne]; rfl
    have hw1Tne : State.get (w.set TFLG [0]) TFLG ≠ [1] := by
      rw [State.get_set_eq]; decide
    have hcost : cardLenCardBody.cost w = 1 + 1 + (1 + 1) := by
      unfold cardLenCardBody
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_ifBit_false _ _ _ _ hw1Tne,
        Cmd.cost_op]
      simp only [Op.cost]
    rw [hcost]
    omega

/-- **`cardLenCheck` cost**: cubic in `Ω ≥ |CARDS|, width`. -/
theorem cardLenCheck_cost (C : BinaryCC) (u : State) (Ω : Nat)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hW : State.get u WIDTH = List.replicate C.width 1)
    (hΩS : (State.get u CARDS).length ≤ Ω)
    (hΩw : C.width ≤ Ω) :
    cardLenCheck.cost u
      ≤ (2 * Cmd.flatK cardLenElemBody + 60)
          * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) := by
  have e0 : (Cmd.op (.copy SCANW CARDS)).eval u
      = u.set SCANW (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hCARDS]
  have hc0 : Op.cost (.copy SCANW CARDS) u = (State.get u CARDS).length + 1 := by
    show (State.get u CARDS).length + 1 = _
    rfl
  set u1 := u.set SCANW (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    with hu1
  have hu1frame : ∀ r : Var, r ≠ SCANW → State.get u1 r = State.get u r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have hu1SC : State.get u1 SCANW
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    State.get_set_eq _ _ _
  have hu1W : State.get u1 WIDTH = List.replicate C.width 1 := by
    rw [hu1frame WIDTH (by decide)]; exact hW
  have hu1CARDSlen : (State.get u1 CARDS).length = (State.get u CARDS).length := by
    rw [hu1frame CARDS (by decide)]
  clear_value u1
  have hcards_le : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length
      = (State.get u CARDS).length := by rw [hCARDS]
  have hbase : CLInv C C.width (State.get u1 GWF) u1 0 u1 := by
    refine ⟨by rw [List.drop_zero]; exact hu1SC, ?_, hu1W,
      fun r _ _ _ _ _ _ _ _ _ _ => rfl⟩
    rw [List.take_zero]; rfl
  have hloop := Cmd.cost_forBnd_le KCARD CARDS cardLenCardBody u1
    (6 + 2 * ((Cmd.flatK cardLenElemBody + 20) * ((Ω + 1) * (Ω + 1))))
    (CLInv C C.width (State.get u1 GWF) u1) hbase
    (fun j st _ hM => CLInv_step C C.width (State.get u1 GWF) u1 j st hM)
    (fun j st _ hM => cardLenCardBody_effect C C.width (State.get u1 GWF) u1 Ω
      (by omega) hΩw j st hM)
  have hcost : cardLenCheck.cost u
      = 1 + Op.cost (.copy SCANW CARDS) u
        + (Cmd.forBnd KCARD CARDS cardLenCardBody).cost u1 := by
    unfold cardLenCheck
    rw [Cmd.cost_seq, Cmd.cost_op, e0]
  rw [hcost, hc0]
  rw [hu1CARDSlen] at hloop
  -- close the arithmetic
  set K := Cmd.flatK cardLenElemBody with hK
  clear_value K
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  set P3 := (Ω + 1) * P2 with hP3
  set len := (State.get u CARDS).length with hlenDef
  have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
  have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
  have h1P3 : 1 ≤ P3 := le_trans h1P2 hP23
  set B := 6 + 2 * ((K + 20) * P2) with hB
  have hBle : B ≤ (2 * K + 46) * P2 := by
    rw [hB]
    have h6 : 6 ≤ 6 * P2 := by omega
    have he : 2 * ((K + 20) * P2) + 6 * P2 = (2 * K + 46) * P2 := by ring
    omega
  have hlB : len * B ≤ (Ω + 1) * ((2 * K + 46) * P2) :=
    Nat.mul_le_mul (by omega) hBle
  have he3 : (Ω + 1) * ((2 * K + 46) * P2) = (2 * K + 46) * P3 := by
    rw [hP3]; ring
  have hll : len * len ≤ Ω * Ω := Nat.mul_le_mul hΩS hΩS
  have hP2exp : P2 = Ω * Ω + 2 * Ω + 1 := by rw [hP2]; ring
  have hfin : (2 * K + 60) * P3 = (2 * K + 46) * P3 + 14 * P3 := by ring
  omega

/-- **`computeWF` cost**: cubic in the ceiling `Ω`, which must dominate the
four scalar inputs (`width`/`offset`/`L`/`|CARDS|`). Straight-line walk of
`computeWF_run`'s spine. -/
theorem computeWF_cost (C : BinaryCC) (u : State) (Ω : Nat)
    (hW : State.get u WIDTH = List.replicate C.width 1)
    (hO : State.get u OFFSET = List.replicate C.offset 1)
    (hL : State.get u LREG = List.replicate C.init.length 1)
    (hCARDS : State.get u CARDS
        = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat))
    (hZ : State.get u ZERO = [])
    (hΩ : C.width + C.offset + C.init.length + (State.get u CARDS).length ≤ Ω) :
    computeWF.cost u
      ≤ (2 * Cmd.flatK cardLenElemBody + 160)
          * ((Ω + 1) * ((Ω + 1) * (Ω + 1))) := by
  -- the spine states
  set t0 := (Cmd.op (.clear GWF)).eval u with ht0
  set t1 := (Cmd.op (.appendOne GWF)).eval t0 with ht1
  set t2 := (Cmd.op (.nonEmpty TFLG WIDTH)).eval t1 with ht2
  set t3 := (andFlag TFLG).eval t2 with ht3
  set t4 := (Cmd.op (.nonEmpty TFLG OFFSET)).eval t3 with ht4
  set t5 := (andFlag TFLG).eval t4 with ht5
  set t6 := (leCheck WIDTH LREG).eval t5 with ht6
  set t7 := (andFlag TFLG).eval t6 with ht7
  set t8 := (dvdCheck WIDTH OFFSET).eval t7 with ht8
  set t9 := (andFlag TFLG).eval t8 with ht9
  set t10 := (dvdCheck LREG OFFSET).eval t9 with ht10
  set t11 := (andFlag TFLG).eval t10 with ht11
  -- per-fragment frames
  have ht0f : ∀ r : Var, r ≠ GWF → State.get t0 r = State.get u r := by
    intro r hr; rw [ht0, Cmd.eval_op]; exact Op.eval_get_ne_writesTo _ _ _ hr
  have ht1f : ∀ r : Var, r ≠ GWF → State.get t1 r = State.get t0 r := by
    intro r hr; rw [ht1, Cmd.eval_op]; exact Op.eval_get_ne_writesTo _ _ _ hr
  have ht2f : ∀ r : Var, r ≠ TFLG → State.get t2 r = State.get t1 r := by
    intro r hr; rw [ht2, Cmd.eval_op]; exact Op.eval_get_ne_writesTo _ _ _ hr
  have ht4f : ∀ r : Var, r ≠ TFLG → State.get t4 r = State.get t3 r := by
    intro r hr; rw [ht4, Cmd.eval_op]; exact Op.eval_get_ne_writesTo _ _ _ hr
  -- registers threaded to t5
  have hchain5 : ∀ r : Var, r ≠ GWF → r ≠ TFLG → r ≠ ZERO →
      State.get t5 r = State.get u r := by
    intro r h1 h2 h3
    rw [ht5, andFlag_frame' TFLG t4 r h3 h1, ht4f r h2, ht3,
      andFlag_frame' TFLG t2 r h3 h1, ht2f r h2, ht1f r h1, ht0f r h1]
  have ht5W : State.get t5 WIDTH = List.replicate C.width 1 :=
    (hchain5 WIDTH (by decide) (by decide) (by decide)).trans hW
  have ht5O : State.get t5 OFFSET = List.replicate C.offset 1 :=
    (hchain5 OFFSET (by decide) (by decide) (by decide)).trans hO
  have ht5L : State.get t5 LREG = List.replicate C.init.length 1 :=
    (hchain5 LREG (by decide) (by decide) (by decide)).trans hL
  have ht5C : State.get t5 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    (hchain5 CARDS (by decide) (by decide) (by decide)).trans hCARDS
  have ht5Llen : (State.get t5 LREG).length = C.init.length := by
    rw [ht5L, List.length_replicate]
  have ht5Z : State.get t5 ZERO = [] := by
    rw [ht5]
    refine andFlag_ZERO TFLG t4 ?_
    rw [ht4f ZERO (by decide), ht3]
    refine andFlag_ZERO TFLG t2 ?_
    rw [ht2f ZERO (by decide), ht1f ZERO (by decide), ht0f ZERO (by decide)]
    exact hZ
  -- through leCheck (write set is register-concrete)
  have ht6f : ∀ r : Var, r ∉ Cmd.writes (leCheck WIDTH LREG) →
      State.get t6 r = State.get t5 r := by
    intro r hr; rw [ht6]; exact Cmd.eval_get_of_not_writes _ _ _ hr
  have ht6W : State.get t6 WIDTH = List.replicate C.width 1 :=
    (ht6f WIDTH (by decide)).trans ht5W
  have ht6O : State.get t6 OFFSET = List.replicate C.offset 1 :=
    (ht6f OFFSET (by decide)).trans ht5O
  have ht6L : State.get t6 LREG = List.replicate C.init.length 1 :=
    (ht6f LREG (by decide)).trans ht5L
  have ht6C : State.get t6 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    (ht6f CARDS (by decide)).trans ht5C
  have ht6Z : State.get t6 ZERO = [] := (ht6f ZERO (by decide)).trans ht5Z
  -- t7 = andFlag
  have ht7W : State.get t7 WIDTH = List.replicate C.width 1 := by
    rw [ht7, andFlag_frame' TFLG t6 WIDTH (by decide) (by decide)]; exact ht6W
  have ht7O : State.get t7 OFFSET = List.replicate C.offset 1 := by
    rw [ht7, andFlag_frame' TFLG t6 OFFSET (by decide) (by decide)]; exact ht6O
  have ht7L : State.get t7 LREG = List.replicate C.init.length 1 := by
    rw [ht7, andFlag_frame' TFLG t6 LREG (by decide) (by decide)]; exact ht6L
  have ht7C : State.get t7 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [ht7, andFlag_frame' TFLG t6 CARDS (by decide) (by decide)]; exact ht6C
  have ht7Z : State.get t7 ZERO = [] := by
    rw [ht7]; exact andFlag_ZERO TFLG t6 ht6Z
  -- t8 = dvdCheck WIDTH OFFSET
  obtain ⟨-, hdv1Z, hdv1F⟩ := dvdCheck_run WIDTH OFFSET C.width C.offset t7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ht7W ht7O ht7Z
  have ht8f : ∀ r : Var, r ≠ MREM → r ≠ MCHK → r ≠ MGE → r ≠ KTMP → r ≠ KTMP2 →
      r ≠ ZERO → r ≠ TFLG → State.get t8 r = State.get t7 r := by
    intro r h1 h2 h3 h4 h5 h6 h7; rw [ht8]; exact hdv1F r h1 h2 h3 h4 h5 h6 h7
  have ht8Z : State.get t8 ZERO = [] := by rw [ht8]; exact hdv1Z
  have ht8W : State.get t8 WIDTH = List.replicate C.width 1 :=
    (ht8f WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht7W
  have ht8O : State.get t8 OFFSET = List.replicate C.offset 1 :=
    (ht8f OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht7O
  have ht8L : State.get t8 LREG = List.replicate C.init.length 1 :=
    (ht8f LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht7L
  have ht8C : State.get t8 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    (ht8f CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht7C
  -- t9 = andFlag
  have ht9O : State.get t9 OFFSET = List.replicate C.offset 1 := by
    rw [ht9, andFlag_frame' TFLG t8 OFFSET (by decide) (by decide)]; exact ht8O
  have ht9L : State.get t9 LREG = List.replicate C.init.length 1 := by
    rw [ht9, andFlag_frame' TFLG t8 LREG (by decide) (by decide)]; exact ht8L
  have ht9W : State.get t9 WIDTH = List.replicate C.width 1 := by
    rw [ht9, andFlag_frame' TFLG t8 WIDTH (by decide) (by decide)]; exact ht8W
  have ht9C : State.get t9 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [ht9, andFlag_frame' TFLG t8 CARDS (by decide) (by decide)]; exact ht8C
  have ht9Z : State.get t9 ZERO = [] := by
    rw [ht9]; exact andFlag_ZERO TFLG t8 ht8Z
  -- t10 = dvdCheck LREG OFFSET
  obtain ⟨-, -, hdv2F⟩ := dvdCheck_run LREG OFFSET C.init.length C.offset t9
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ht9L ht9O ht9Z
  have ht10f : ∀ r : Var, r ≠ MREM → r ≠ MCHK → r ≠ MGE → r ≠ KTMP → r ≠ KTMP2 →
      r ≠ ZERO → r ≠ TFLG → State.get t10 r = State.get t9 r := by
    intro r h1 h2 h3 h4 h5 h6 h7; rw [ht10]; exact hdv2F r h1 h2 h3 h4 h5 h6 h7
  have ht10W : State.get t10 WIDTH = List.replicate C.width 1 :=
    (ht10f WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht9W
  have ht10C : State.get t10 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) :=
    (ht10f CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht9C
  -- t11 = andFlag
  have ht11W : State.get t11 WIDTH = List.replicate C.width 1 := by
    rw [ht11, andFlag_frame' TFLG t10 WIDTH (by decide) (by decide)]; exact ht10W
  have ht11C : State.get t11 CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := by
    rw [ht11, andFlag_frame' TFLG t10 CARDS (by decide) (by decide)]; exact ht10C
  have ht11Clen : (State.get t11 CARDS).length ≤ Ω := by
    rw [ht11C, ← hCARDS]; omega
  -- the four check costs
  have hle := leCheck_cost WIDTH LREG C.width C.init.length t5 Ω (by decide)
    ht5W ht5Llen (by omega) (by omega)
  have hdv1 := dvdCheck_cost WIDTH OFFSET C.width C.offset t7 Ω (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ht7W ht7O ht7Z (by omega) (by omega)
  have hdv2 := dvdCheck_cost LREG OFFSET C.init.length C.offset t9 Ω (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ht9L ht9O ht9Z (by omega) (by omega)
  have hcl := cardLenCheck_cost C t11 Ω ht11C ht11W ht11Clen (by omega)
  -- assemble the cost
  have hcost : computeWF.cost u
      = 1 + 1 + (1 + 1 + (1 + 1 + (1 + (andFlag TFLG).cost t2
        + (1 + 1 + (1 + (andFlag TFLG).cost t4
        + (1 + (leCheck WIDTH LREG).cost t5
        + (1 + (andFlag TFLG).cost t6
        + (1 + (dvdCheck WIDTH OFFSET).cost t7
        + (1 + (andFlag TFLG).cost t8
        + (1 + (dvdCheck LREG OFFSET).cost t9
        + (1 + (andFlag TFLG).cost t10
        + cardLenCheck.cost t11))))))))))) := by
    unfold computeWF
    rw [Cmd.cost_seq, Cmd.cost_op, ← ht0, Cmd.cost_seq, Cmd.cost_op, ← ht1,
      Cmd.cost_seq, Cmd.cost_op, ← ht2, Cmd.cost_seq, ← ht3,
      Cmd.cost_seq, Cmd.cost_op, ← ht4, Cmd.cost_seq, ← ht5,
      Cmd.cost_seq, ← ht6, Cmd.cost_seq, ← ht7, Cmd.cost_seq, ← ht8,
      Cmd.cost_seq, ← ht9, Cmd.cost_seq, ← ht10, Cmd.cost_seq, ← ht11]
    simp only [Op.cost]
  rw [hcost, andFlag_cost TFLG t2, andFlag_cost TFLG t4, andFlag_cost TFLG t6,
    andFlag_cost TFLG t8, andFlag_cost TFLG t10]
  -- close the arithmetic
  have hleB := hle
  have hdv1B := hdv1
  have hdv2B := hdv2
  have hclB := hcl
  set K := Cmd.flatK cardLenElemBody with hK
  clear_value K
  set P2 := (Ω + 1) * (Ω + 1) with hP2
  set P3 := (Ω + 1) * P2 with hP3
  set c5 := (leCheck WIDTH LREG).cost t5 with hc5
  clear_value c5
  set c7 := (dvdCheck WIDTH OFFSET).cost t7 with hc7
  clear_value c7
  set c9 := (dvdCheck LREG OFFSET).cost t9 with hc9
  clear_value c9
  set c11 := cardLenCheck.cost t11 with hc11
  clear_value c11
  have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
  have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
  have h1P3 : 1 ≤ P3 := le_trans h1P2 hP23
  have h12 : 12 * P2 ≤ 12 * P3 := Nat.mul_le_mul_left _ hP23
  have hfin : (2 * K + 160) * P3 = (2 * K + 60) * P3 + 100 * P3 := by ring
  omega

/-! ### The `buildFSAT` cost assembly — the witness's `cost_le` obligation -/

/-- **`precompLen` cost**: quadratic in `Ω ≥ L`. -/
theorem precompLen_cost (bs : List Bool) (u : State) (Ω : Nat)
    (hINIT : State.get u INIT = FlatCCBinFree.bitsNat bs)
    (hΩ : bs.length ≤ Ω) :
    precompLen.cost u ≤ 8 * ((Ω + 1) * (Ω + 1)) := by
  have e1 : (Cmd.op (.clear LREG)).eval u = u.set LREG [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set w1 := u.set LREG [] with hw1
  have hw1L : State.get w1 LREG = [] := State.get_set_eq _ _ _
  have hw1I : (State.get w1 INIT).length = bs.length := by
    rw [State.get_set_ne _ _ _ _ (show INIT ≠ LREG by decide), hINIT]
    exact List.length_map _
  clear_value w1
  have hcLoop := cost_constLoop_le KTMP INIT (Cmd.op (.appendOne LREG)) rfl rfl w1
    bs.length hw1I
  have hKop : Cmd.flatK (Cmd.op (.appendOne LREG)) = 5 := rfl
  rw [hKop] at hcLoop
  -- LREG length at loop exit (for the copy's cost)
  have hInv := Cmd.foldlState_range_induct (Cmd.op (.appendOne LREG)) KTMP bs.length w1
    (fun i st => (State.get st LREG).length ≤ i)
    (by show (State.get w1 LREG).length ≤ 0; simp [hw1L])
    (fun i st _ hM => by
      show (State.get ((Cmd.op (.appendOne LREG)).eval
        (st.set KTMP (List.replicate i 1))) LREG).length ≤ i + 1
      rw [Cmd.eval_op]
      simp only [Op.eval]
      rw [State.get_set_eq,
        State.get_set_ne _ _ _ _ (show LREG ≠ KTMP by decide),
        List.length_append]
      simpa using hM)
  have heval0 : (Cmd.forBnd KTMP INIT (Cmd.op (.appendOne LREG))).eval w1
      = Cmd.foldlState (Cmd.op (.appendOne LREG)) KTMP (List.range bs.length) w1 := by
    rw [Cmd.eval_forBnd, hw1I]
  set w2 := (Cmd.forBnd KTMP INIT (Cmd.op (.appendOne LREG))).eval w1 with hw2
  have hw2Llen : (State.get w2 LREG).length ≤ bs.length := by
    rw [heval0]; exact hInv
  clear_value w2
  have hc3 : Op.cost (.copy LREG1 LREG) w2 ≤ bs.length + 1 := by
    show (State.get w2 LREG).length + 1 ≤ _
    omega
  set w3 := (Cmd.op (.copy LREG1 LREG)).eval w2 with hw3
  clear_value w3
  have hcost : precompLen.cost u
      = 1 + 1 + (1 + (Cmd.forBnd KTMP INIT (Cmd.op (.appendOne LREG))).cost w1
        + (1 + Op.cost (.copy LREG1 LREG) w2 + 1)) := by
    unfold precompLen
    rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hw2, Cmd.cost_seq,
      Cmd.cost_op, ← hw3, Cmd.cost_op]
    simp only [Op.cost]
  rw [hcost]
  have hP2exp : (Ω + 1) * (Ω + 1) = Ω * Ω + 2 * Ω + 1 := by ring
  have hbb : bs.length * bs.length ≤ Ω * Ω := Nat.mul_le_mul hΩ hΩ
  omega

/-- The master cost ceiling (`n := encodable.size C`): dominates the serialized
output length (`≤ 4·(500·n⁶+500)` via `serF_length_le_size` +
`BinaryCC_to_FSAT_instance_size_bound`), every variable index, every stream
length, and every per-emitter index sum on `encodeIn C`. -/
def masterOmega (n : Nat) : Nat := 2000 * (n + 1) ^ 6

/-- The total symbolic cost coefficient of `buildFSAT` (never evaluate the
`flatK` numerals — only `inOPoly` matters). -/
def buildFSATK : Nat :=
  2 * Cmd.flatK (sentBitBody 0) + 2 * Cmd.flatK (bsBody 0)
    + Cmd.flatK readFinBody + 2 * Cmd.flatK cardLenElemBody + 1000

/-- The witness's `cost_bound`: `buildFSATK · (masterOmega n + 1)^5`. -/
def buildFSATBound (n : Nat) : Nat :=
  buildFSATK * ((masterOmega n + 1) * ((masterOmega n + 1) * ((masterOmega n + 1)
    * ((masterOmega n + 1) * (masterOmega n + 1)))))

theorem buildFSATBound_poly : inOPoly buildFSATBound := by
  refine ⟨30, ⟨buildFSATK * 128064 ^ 5, 1, ?_⟩⟩
  intro n hn
  have h1 : masterOmega n + 1 ≤ 128064 * n ^ 6 := by
    unfold masterOmega
    have h2 : (n + 1) ^ 6 ≤ (2 * n) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have h3 : (2 * n) ^ 6 = 64 * n ^ 6 := by ring
    have h4 : 1 ≤ n ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  calc buildFSATBound n
      ≤ buildFSATK * ((128064 * n ^ 6) * ((128064 * n ^ 6) * ((128064 * n ^ 6)
          * ((128064 * n ^ 6) * (128064 * n ^ 6))))) := by
        unfold buildFSATBound
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 (Nat.mul_le_mul h1
          (Nat.mul_le_mul h1 (Nat.mul_le_mul h1 h1))))
    _ = buildFSATK * 128064 ^ 5 * n ^ 30 := by ring

theorem buildFSATBound_mono : monotonic buildFSATBound := by
  intro a b h
  unfold buildFSATBound
  have hm : masterOmega a + 1 ≤ masterOmega b + 1 := by
    unfold masterOmega
    have := Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 6
    omega
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hm (Nat.mul_le_mul hm
    (Nat.mul_le_mul hm (Nat.mul_le_mul hm hm))))

/-- The output size is dominated by the cost bound (the witness's
`output_size_le`). -/
theorem buildFSATBound_output (C : BinaryCC) :
    encodable.size (BinaryCC_to_FSAT_instance C)
      ≤ buildFSATBound (encodable.size C) := by
  set n := encodable.size C with hn
  have h1 := BinaryCC_to_FSAT_instance_size_bound C
  rw [← hn] at h1
  have hle : n ^ 6 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have h1p : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h3 : 500 * n ^ 6 + 500 ≤ masterOmega n := by
    unfold masterOmega
    omega
  have h4 : masterOmega n ≤ buildFSATBound n := by
    unfold buildFSATBound
    have hK : 1000 ≤ buildFSATK := by unfold buildFSATK; omega
    have hrest : masterOmega n + 1
        ≤ (masterOmega n + 1) * ((masterOmega n + 1) * ((masterOmega n + 1)
          * ((masterOmega n + 1) * (masterOmega n + 1)))) := by
      have h1p : 1 ≤ (masterOmega n + 1) * ((masterOmega n + 1)
          * ((masterOmega n + 1) * (masterOmega n + 1))) :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _)
          (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      calc masterOmega n + 1 = (masterOmega n + 1) * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h1p
    calc masterOmega n ≤ 1 * (masterOmega n + 1) := by omega
      _ ≤ buildFSATK * ((masterOmega n + 1) * ((masterOmega n + 1)
          * ((masterOmega n + 1) * ((masterOmega n + 1) * (masterOmega n + 1))))) :=
        Nat.mul_le_mul (by omega) hrest
  omega

set_option maxRecDepth 4000 in
/-- **`buildFSAT` cost is polynomial** — the `cost_le` crux of the
`BinaryCC ⪯p' FSAT` witness. The whole accounting is instantiated at the ONE
master ceiling `Ω := masterOmega (encodable.size C)`. -/
theorem buildFSAT_cost_le (C : BinaryCC) :
    buildFSAT.cost (encodeIn C) ≤ buildFSATBound (encodable.size C) := by
  classical
  set n := encodable.size C with hn
  set Ω := masterOmega n with hΩdef
  -- component bounds off the instance size
  have hCsz : n = C.offset + C.width + encodable.size C.init
      + encodable.size C.cards + encodable.size C.final + C.steps + 1 := rfl
  have hLn : C.init.length ≤ n :=
    le_trans (list_length_le_size C.init) (by omega)
  have hoffn : C.offset ≤ n := by omega
  have hwidn : C.width ≤ n := by omega
  have hstepsn : C.steps ≤ n := by omega
  have hcardsn : (FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat)).length
      ≤ 2 * n := by
    have h := FlatCCBinFree.encCardsOut_length_le (C.cards.map FlatCCBinFree.cardNat)
    rw [encodable_size_map_cardNat] at h
    omega
  have hfinaln : (FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat)).length
      ≤ 2 * n := by
    have h := FlatTCCFree.encFinal_length_le (C.final.map FlatCCBinFree.bitsNat)
    rw [encodable_size_map_bitsNat] at h
    omega
  have hsLn : C.steps * C.init.length ≤ n * n := Nat.mul_le_mul hstepsn hLn
  have hLon : C.init.length * C.offset ≤ n * n := Nat.mul_le_mul hLn hoffn
  -- `n ≤ n*n` lets omega bridge the linear and quadratic index terms
  have hn_nn : n ≤ n * n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left n h
  -- the quadratic dominator (generous: every index sum is `≤ 20·n²`)
  have hΩquad : 20 * (n * n) ≤ Ω := by
    rw [hΩdef]
    unfold masterOmega
    have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    omega
  -- the serF split of the tableau
  have hserFsplit : serF (encodeTableau C)
      = [0, 1] ++ (serF (encodeBitsAt 0 C.init)
        ++ ([0, 1] ++ (serF (encodeAllStepConstraints C)
          ++ serF (encodeFinalConstraint C)))) := by
    show serF (.fand (encodeBitsAt 0 C.init)
        (.fand (encodeAllStepConstraints C) (encodeFinalConstraint C))) = _
    simp [serF, List.append_assoc]
  have hserFlen : (serF (encodeTableau C)).length
      = 4 + (serF (encodeBitsAt 0 C.init)).length
        + (serF (encodeAllStepConstraints C)).length
        + (serF (encodeFinalConstraint C)).length := by
    rw [hserFsplit]
    simp [List.length_append]
    omega
  -- the pinned input frame (definitional)
  have h0STEPS : State.get (encodeIn C) STEPS = List.replicate C.steps 1 := rfl
  have h0OFF : State.get (encodeIn C) OFFSET = List.replicate C.offset 1 := rfl
  have h0WID : State.get (encodeIn C) WIDTH = List.replicate C.width 1 := rfl
  have h0INIT : State.get (encodeIn C) INIT = FlatCCBinFree.bitsNat C.init := rfl
  have h0CARDS : State.get (encodeIn C) CARDS
      = FlatTCCFree.encCardsOut (C.cards.map FlatCCBinFree.cardNat) := rfl
  have h0FINAL : State.get (encodeIn C) FINAL
      = FlatTCCFree.encFinal (C.final.map FlatCCBinFree.bitsNat) := rfl
  have h0ZERO : State.get (encodeIn C) ZERO = [] := rfl
  have h0WREG : State.get (encodeIn C) WREG = [] := rfl
  -- u1 : precompLen (run + cost)
  have hcPre := precompLen_cost C.init (encodeIn C) Ω h0INIT (by omega)
  obtain ⟨hpL, hpL1, hpF⟩ := precompLen_run C.init (encodeIn C) h0INIT
  set u1 := precompLen.eval (encodeIn C) with hu1
  have h1STEPS := (hpF STEPS (by decide) (by decide) (by decide)).trans h0STEPS
  have h1OFF := (hpF OFFSET (by decide) (by decide) (by decide)).trans h0OFF
  have h1WID := (hpF WIDTH (by decide) (by decide) (by decide)).trans h0WID
  have h1INIT := (hpF INIT (by decide) (by decide) (by decide)).trans h0INIT
  have h1CARDS := (hpF CARDS (by decide) (by decide) (by decide)).trans h0CARDS
  have h1FINAL := (hpF FINAL (by decide) (by decide) (by decide)).trans h0FINAL
  have h1ZERO := (hpF ZERO (by decide) (by decide) (by decide)).trans h0ZERO
  have h1WREG := (hpF WREG (by decide) (by decide) (by decide)).trans h0WREG
  clear_value u1
  -- u2 : computeWF (run + cost)
  have hcWF := computeWF_cost C u1 Ω h1WID h1OFF hpL h1CARDS h1ZERO
    (by rw [h1CARDS]; omega)
  obtain ⟨hwG, hwF⟩ := computeWF_run C u1 h1WID h1OFF hpL h1CARDS h1ZERO
  set u2 := computeWF.eval u1 with hu2
  have h2STEPS := (hwF STEPS (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1STEPS
  have h2OFF := (hwF OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1OFF
  have h2WID := (hwF WIDTH (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1WID
  have h2INIT := (hwF INIT (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1INIT
  have h2CARDS := (hwF CARDS (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1CARDS
  have h2FINAL := (hwF FINAL (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1FINAL
  have h2LREG := (hwF LREG (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hpL
  have h2LREG1 := (hwF LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hpL1
  have h2WREG := (hwF WREG (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans h1WREG
  clear_value u2
  -- u3 : clear OUT
  have e3 : (Cmd.op (.clear OUT)).eval u2 = u2.set OUT [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set u3 := u2.set OUT [] with hu3
  have h3f : ∀ r : Var, r ≠ OUT → State.get u3 r = State.get u2 r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  have h3OUT : State.get u3 OUT = [] := State.get_set_eq _ _ _
  have h3GWF : State.get u3 GWF = (if BinaryCC_wellformed C then [1] else []) :=
    (h3f GWF (by decide)).trans hwG
  have h3STEPS := (h3f STEPS (by decide)).trans h2STEPS
  have h3OFF := (h3f OFFSET (by decide)).trans h2OFF
  have h3WID := (h3f WIDTH (by decide)).trans h2WID
  have h3INIT := (h3f INIT (by decide)).trans h2INIT
  have h3CARDS := (h3f CARDS (by decide)).trans h2CARDS
  have h3FINAL := (h3f FINAL (by decide)).trans h2FINAL
  have h3LREG := (h3f LREG (by decide)).trans h2LREG
  have h3LREG1 := (h3f LREG1 (by decide)).trans h2LREG1
  have h3WREG := (h3f WREG (by decide)).trans h2WREG
  clear_value u3
  -- peel the top-level cost down to the branch
  set vIf := (Cmd.ifBit GWF
      ( emitFandTag ;;
        Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
        emitBitsFromScan ZERO INIT ;;
        emitFandTag ;;
        emitAllSteps ;;
        emitFinal )
      emitFalse).eval u3 with hvIf
  have hcost : buildFSAT.cost (encodeIn C)
      = 1 + precompLen.cost (encodeIn C)
      + (1 + computeWF.cost u1
      + (1 + 1
      + (1 + (Cmd.ifBit GWF
          ( emitFandTag ;;
            Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
            emitBitsFromScan ZERO INIT ;;
            emitFandTag ;;
            emitAllSteps ;;
            emitFinal )
          emitFalse).cost u3
      + ((State.get vIf OUT).length + 1)))) := by
    unfold buildFSAT
    rw [Cmd.cost_seq, ← hu1, Cmd.cost_seq, ← hu2, Cmd.cost_seq, Cmd.cost_op, e3,
      Cmd.cost_seq, ← hvIf, Cmd.cost_op]
    simp only [Op.cost]
  rw [hcost]
  by_cases hWf : BinaryCC_wellformed C
  · -- wellformed: the emitter branch
    have hGeq : State.get u3 GWF = [1] := by rw [h3GWF, if_pos hWf]
    -- the serialization-length dominator (needed by every emitter's OUT ceiling)
    have hTabΩ : (serF (encodeTableau C)).length ≤ Ω := by
      have hEq : BinaryCC_to_FSAT_instance C = encodeTableau C := by
        unfold BinaryCC_to_FSAT_instance; rw [dif_pos hWf]
      have hlen := serF_length_le_size (BinaryCC_to_FSAT_instance C)
      rw [hEq] at hlen
      have hsz := BinaryCC_to_FSAT_instance_size_bound C
      rw [hEq, ← hn] at hsz
      have hle6 : n ^ 6 < (n + 1) ^ 6 :=
        Nat.pow_lt_pow_left (show n < n + 1 by omega) (by norm_num)
      rw [hΩdef]; unfold masterOmega
      omega
    -- the three top-level serF parts each fit under Ω (via the split + hTabΩ)
    have hTabΩsplit : 4 + (serF (encodeBitsAt 0 C.init)).length
        + (serF (encodeAllStepConstraints C)).length
        + (serF (encodeFinalConstraint C)).length ≤ Ω := by
      rw [← hserFlen]; exact hTabΩ
    have hbitsΩ : (serF (encodeBitsAt 0 C.init)).length ≤ Ω := by omega
    have hstepsΩ : (serF (encodeAllStepConstraints C)).length ≤ Ω := by omega
    have hfinalΩ : (serF (encodeFinalConstraint C)).length ≤ Ω := by omega
    -- v1 : emitFandTag
    have e_v1 : emitFandTag.eval u3 = u3.set OUT [0, 1] := by
      rw [emitFandTag_run, h3OUT, List.nil_append]
    set v1 := u3.set OUT [0, 1] with hv1
    have hv1f : ∀ r : Var, r ≠ OUT → State.get v1 r = State.get u3 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv1OUT : State.get v1 OUT = [0, 1] := State.get_set_eq _ _ _
    clear_value v1
    -- v2 : clear ZERO
    have e_v2 : (Cmd.op (.clear ZERO)).eval v1 = v1.set ZERO [] := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    set v2 := v1.set ZERO [] with hv2
    have hv2f : ∀ r : Var, r ≠ ZERO → State.get v2 r = State.get v1 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv2ZERO : State.get v2 ZERO = [] := State.get_set_eq _ _ _
    clear_value v2
    -- v3 : copy SCAN INIT
    have h2INITv : State.get v2 INIT = FlatCCBinFree.bitsNat C.init := by
      rw [hv2f INIT (by decide), hv1f INIT (by decide)]; exact h3INIT
    have e_v3 : (Cmd.op (.copy SCAN INIT)).eval v2
        = v2.set SCAN (FlatCCBinFree.bitsNat C.init) := by
      rw [Cmd.eval_op]; simp only [Op.eval, h2INITv]
    have hc_v3 : Op.cost (.copy SCAN INIT) v2 = C.init.length + 1 := by
      show (State.get v2 INIT).length + 1 = _
      rw [h2INITv]
      exact congrArg (· + 1) (List.length_map _)
    set v3 := v2.set SCAN (FlatCCBinFree.bitsNat C.init) with hv3
    have hv3f : ∀ r : Var, r ≠ SCAN → State.get v3 r = State.get v2 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv3SCAN : State.get v3 SCAN = FlatCCBinFree.bitsNat C.init :=
      State.get_set_eq _ _ _
    clear_value v3
    -- v4 : emitBitsFromScan (run + cost + WREG)
    have h3ZEROv : State.get v3 ZERO = List.replicate 0 1 := by
      rw [hv3f ZERO (by decide)]; exact hv2ZERO
    have h3INITlen : (State.get v3 INIT).length = C.init.length := by
      rw [hv3f INIT (by decide), h2INITv]
      exact List.length_map _
    have h3OUTv : State.get v3 OUT = [0, 1] := by
      rw [hv3f OUT (by decide), hv2f OUT (by decide)]; exact hv1OUT
    have h3WREGv : State.get v3 WREG = [] := by
      rw [hv3f WREG (by decide), hv2f WREG (by decide), hv1f WREG (by decide)]
      exact h3WREG
    have hcScan := emitBitsFromScan_cost ZERO INIT 0 C.init v3 Ω
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h3ZEROv h3INITlen hv3SCAN
      (by rw [h3OUTv]
          simp only [List.length_cons, List.length_nil]
          omega)
      (by rw [h3WREGv]; exact Nat.zero_le Ω)
      (by omega)
    have hWScan := emitBitsFromScan_WREG ZERO INIT v3 Ω
      (by decide) (by decide) (by decide) (by decide)
      (by rw [h3WREGv]; exact Nat.zero_le Ω)
      (by rw [h3ZEROv, h3INITlen]
          simp only [List.length_replicate]
          omega)
    obtain ⟨h4SCAN, h4OUT, h4F⟩ := emitBitsFromScan_run ZERO INIT 0 C.init v3
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h3ZEROv h3INITlen hv3SCAN
    set v4 := (emitBitsFromScan ZERO INIT).eval v3 with hv4
    have h4OUTval : State.get v4 OUT = [0, 1] ++ serF (encodeBitsAt 0 C.init) := by
      rw [h4OUT, h3OUTv]
    have h4WREG : (State.get v4 WREG).length ≤ Ω := hWScan
    clear_value v4
    -- v5 : emitFandTag
    have e_v5 : emitFandTag.eval v4
        = v4.set OUT (([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1]) := by
      rw [emitFandTag_run, h4OUTval]
    set v5 := v4.set OUT (([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1]) with hv5
    have hv5f : ∀ r : Var, r ≠ OUT → State.get v5 r = State.get v4 r :=
      fun r hr => State.get_set_ne _ _ _ _ hr
    have hv5OUT : State.get v5 OUT
        = ([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1] := State.get_set_eq _ _ _
    clear_value v5
    -- register threading u3 → v5
    have hv5chain : ∀ r : Var, r ≠ OUT → r ≠ ZERO → r ≠ SCAN → r ≠ WREG → r ≠ TFLG →
        r ≠ KBIT → State.get v5 r = State.get u3 r := by
      intro r h1 h2 h3 h4 h5 h6
      rw [hv5f r h1, h4F r h3 h1 h4 h5 h6, hv3f r h3, hv2f r h2, hv1f r h1]
    have h5STEPS := (hv5chain STEPS (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3STEPS
    have h5OFF := (hv5chain OFFSET (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3OFF
    have h5WID := (hv5chain WIDTH (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3WID
    have h5CARDS := (hv5chain CARDS (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3CARDS
    have h5FINAL := (hv5chain FINAL (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3FINAL
    have h5LREG := (hv5chain LREG (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3LREG
    have h5LREG1 := (hv5chain LREG1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h3LREG1
    have h5ZERO : State.get v5 ZERO = [] := by
      rw [hv5f ZERO (by decide), h4F ZERO (by decide) (by decide) (by decide)
        (by decide) (by decide), hv3f ZERO (by decide)]
      exact hv2ZERO
    have h5WREG : (State.get v5 WREG).length ≤ Ω := by
      rw [hv5f WREG (by decide)]; exact h4WREG
    -- v6 : emitAllSteps (run + cost + WREG exit)
    have hΩO5 : (State.get v5 OUT).length
        + (serF (encodeAllStepConstraints C)).length ≤ Ω := by
      rw [hv5OUT]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hΩidx5 : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.offset + C.width + C.init.length + C.steps
        + (State.get v5 CARDS).length ≤ Ω := by
      rw [h5CARDS]
      omega
    have hcAS := emitAllSteps_cost C v5 Ω h5STEPS h5OFF h5WID h5LREG h5LREG1
      h5CARDS h5ZERO hΩO5 h5WREG hΩidx5
    obtain ⟨h6OUT, h6ZERO, h6F⟩ := emitAllSteps_run C v5
      h5STEPS h5OFF h5WID h5LREG h5LREG1 h5CARDS h5ZERO
    set v6 := emitAllSteps.eval v5 with hv6
    have h6WREG : (State.get v6 WREG).length ≤ Ω := hcAS.2
    have h6OUTval : State.get v6 OUT
        = (([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1])
          ++ serF (encodeAllStepConstraints C) := by
      rw [h6OUT, hv5OUT]
    have h6STEPS := (h6F STEPS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5STEPS
    have h6OFF := (h6F OFFSET (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5OFF
    have h6LREG := (h6F LREG (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5LREG
    have h6LREG1 := (h6F LREG1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5LREG1
    have h6FINAL := (h6F FINAL (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans h5FINAL
    clear_value v6
    -- v7 : emitFinal (run + cost)
    have hΩO6 : (State.get v6 OUT).length
        + (serF (encodeFinalConstraint C)).length ≤ Ω := by
      rw [h6OUTval]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hΩidx6 : C.steps * C.init.length + C.init.length * C.offset + C.init.length
        + C.offset + C.init.length + C.steps + (State.get v6 FINAL).length ≤ Ω := by
      rw [h6FINAL]
      omega
    have hcFin := emitFinal_cost C v6 Ω h6STEPS h6OFF h6LREG h6LREG1 h6FINAL h6ZERO
      hΩO6 h6WREG hΩidx6
    obtain ⟨h7OUT, h7ZERO, h7F⟩ := emitFinal_run C v6
      h6STEPS h6OFF h6LREG h6LREG1 h6FINAL h6ZERO
    set v7 := emitFinal.eval v6 with hv7
    have h7OUTval : State.get v7 OUT
        = ((([0, 1] ++ serF (encodeBitsAt 0 C.init)) ++ [0, 1])
            ++ serF (encodeAllStepConstraints C))
          ++ serF (encodeFinalConstraint C) := by
      rw [h7OUT, h6OUTval]
    clear_value v7
    -- the branch's eval and cost
    have hbranchEval : (emitFandTag ;;
        Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
        emitBitsFromScan ZERO INIT ;;
        emitFandTag ;;
        emitAllSteps ;;
        emitFinal).eval u3 = v7 := by
      rw [Cmd.eval_seq, e_v1, Cmd.eval_seq, e_v2, Cmd.eval_seq, e_v3, Cmd.eval_seq,
        ← hv4, Cmd.eval_seq, e_v5, Cmd.eval_seq, ← hv6, ← hv7]
    have hvIfval : vIf = v7 := by
      rw [hvIf, Cmd.eval_ifBit_true _ _ _ _ hGeq, hbranchEval]
    have hbranchCost : (emitFandTag ;;
        Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
        emitBitsFromScan ZERO INIT ;;
        emitFandTag ;;
        emitAllSteps ;;
        emitFinal).cost u3
        = 1 + 3 + (1 + 1 + (1 + Op.cost (.copy SCAN INIT) v2
          + (1 + (emitBitsFromScan ZERO INIT).cost v3
          + (1 + 3 + (1 + emitAllSteps.cost v5 + emitFinal.cost v6))))) := by
      rw [Cmd.cost_seq, emitFandTag_cost, e_v1, Cmd.cost_seq, Cmd.cost_op, e_v2,
        Cmd.cost_seq, Cmd.cost_op, e_v3, Cmd.cost_seq, ← hv4, Cmd.cost_seq,
        emitFandTag_cost, e_v5, Cmd.cost_seq, ← hv6]
      simp only [Op.cost]
    have hcIf : (Cmd.ifBit GWF
        ( emitFandTag ;;
          Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
          emitBitsFromScan ZERO INIT ;;
          emitFandTag ;;
          emitAllSteps ;;
          emitFinal )
        emitFalse).cost u3
        = 1 + (1 + 3 + (1 + 1 + (1 + Op.cost (.copy SCAN INIT) v2
          + (1 + (emitBitsFromScan ZERO INIT).cost v3
          + (1 + 3 + (1 + emitAllSteps.cost v5 + emitFinal.cost v6)))))) := by
      rw [Cmd.cost_ifBit_true _ _ _ _ hGeq, hbranchCost]
    -- the final copy's length
    have hvIfOUT : (State.get vIf OUT).length = (serF (encodeTableau C)).length := by
      rw [hvIfval, h7OUTval, hserFlen]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hcIf, hc_v3, hvIfOUT]
    -- gather the bounds and close
    have hAS := hcAS.1
    have hFin := hcFin.1
    set Ks := Cmd.flatK (sentBitBody 0) with hKs
    clear_value Ks
    set Kb := Cmd.flatK (bsBody 0) with hKb
    clear_value Kb
    set Kr := Cmd.flatK readFinBody with hKr
    clear_value Kr
    set Ke := Cmd.flatK cardLenElemBody with hKe
    clear_value Ke
    set P2 := (Ω + 1) * (Ω + 1) with hP2
    set P3 := (Ω + 1) * P2 with hP3
    set P4 := (Ω + 1) * P3 with hP4
    set P5 := (Ω + 1) * P4 with hP5
    set cPre := precompLen.cost (encodeIn C) with hcPreDef
    clear_value cPre
    set cWF := computeWF.cost u1 with hcWFDef
    clear_value cWF
    set cScan := (emitBitsFromScan ZERO INIT).cost v3 with hcScanDef
    clear_value cScan
    set cAS := emitAllSteps.cost v5 with hcASDef
    clear_value cAS
    set cFin := emitFinal.cost v6 with hcFinDef
    clear_value cFin
    have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
    have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
    have hP34 : P3 ≤ P4 := by rw [hP4]; exact le_scale Ω P3
    have hP45 : P4 ≤ P5 := by rw [hP5]; exact le_scale Ω P4
    have h1P5 : 1 ≤ P5 := le_trans h1P2 (le_trans hP23 (le_trans hP34 hP45))
    have hΩP5 : Ω + 1 ≤ P5 := by
      calc Ω + 1 = (Ω + 1) * 1 := by ring
        _ ≤ (Ω + 1) * P4 := Nat.mul_le_mul_left _ (le_trans h1P2 (le_trans hP23 hP34))
        _ = P5 := by rw [hP5]
    have hPre5 : 8 * P2 ≤ 8 * P5 :=
      Nat.mul_le_mul_left _ (le_trans hP23 (le_trans hP34 hP45))
    have hWF5 : (2 * Ke + 160) * P3 ≤ (2 * Ke + 160) * P5 :=
      Nat.mul_le_mul_left _ (le_trans hP34 hP45)
    have hScan5 : (Kb + 6) * P2 ≤ (Kb + 6) * P5 :=
      Nat.mul_le_mul_left _ (le_trans hP23 (le_trans hP34 hP45))
    have hFin5 : (Kb + Kr + 140) * P4 ≤ (Kb + Kr + 140) * P5 :=
      Nat.mul_le_mul_left _ hP45
    have hLΩ : C.init.length ≤ Ω := by omega
    have hfin : (2 * Ks + 2 * Kb + Kr + 2 * Ke + 1000) * P5
        = (2 * Ks + 160) * P5 + (Kb + Kr + 140) * P5 + (2 * Ke + 160) * P5
          + (Kb + 6) * P5 + 8 * P5 + 526 * P5 := by ring
    have hgoal : buildFSATBound n
        = (2 * Ks + 2 * Kb + Kr + 2 * Ke + 1000) * P5 := by
      rw [buildFSATBound, buildFSATK, ← hKs, ← hKb, ← hKr, ← hKe, ← hΩdef,
        ← hP2, ← hP3, ← hP4, ← hP5]
    rw [hgoal]
    omega
  · -- not wellformed: the `emitFalse` branch
    have hGne : State.get u3 GWF ≠ [1] := by
      rw [h3GWF, if_neg hWf]; decide
    have hvIfval : vIf = emitFalse.eval u3 := by
      rw [hvIf, Cmd.eval_ifBit_false _ _ _ _ hGne]
    have hvIfOUT : (State.get vIf OUT).length = 5 := by
      rw [hvIfval, emitFalse_run, State.get_set_eq, h3OUT]
      rfl
    have hcIf : (Cmd.ifBit GWF
        ( emitFandTag ;;
          Cmd.op (.clear ZERO) ;; Cmd.op (.copy SCAN INIT) ;;
          emitBitsFromScan ZERO INIT ;;
          emitFandTag ;;
          emitAllSteps ;;
          emitFinal )
        emitFalse).cost u3 = 1 + 9 := by
      rw [Cmd.cost_ifBit_false _ _ _ _ hGne, emitFalse_cost]
    rw [hcIf, hvIfOUT]
    set Ks := Cmd.flatK (sentBitBody 0) with hKs
    clear_value Ks
    set Kb := Cmd.flatK (bsBody 0) with hKb
    clear_value Kb
    set Kr := Cmd.flatK readFinBody with hKr
    clear_value Kr
    set Ke := Cmd.flatK cardLenElemBody with hKe
    clear_value Ke
    set P2 := (Ω + 1) * (Ω + 1) with hP2
    set P3 := (Ω + 1) * P2 with hP3
    set P4 := (Ω + 1) * P3 with hP4
    set P5 := (Ω + 1) * P4 with hP5
    set cPre := precompLen.cost (encodeIn C) with hcPreDef
    clear_value cPre
    set cWF := computeWF.cost u1 with hcWFDef
    clear_value cWF
    have h1P2 : 1 ≤ P2 := by rw [hP2]; exact one_le_P Ω
    have hP23 : P2 ≤ P3 := by rw [hP3]; exact le_scale Ω P2
    have hP34 : P3 ≤ P4 := by rw [hP4]; exact le_scale Ω P3
    have hP45 : P4 ≤ P5 := by rw [hP5]; exact le_scale Ω P4
    have h1P5 : 1 ≤ P5 := le_trans h1P2 (le_trans hP23 (le_trans hP34 hP45))
    have hPre5 : 8 * P2 ≤ 8 * P5 :=
      Nat.mul_le_mul_left _ (le_trans hP23 (le_trans hP34 hP45))
    have hWF5 : (2 * Ke + 160) * P3 ≤ (2 * Ke + 160) * P5 :=
      Nat.mul_le_mul_left _ (le_trans hP34 hP45)
    have hfin : (2 * Ks + 2 * Kb + Kr + 2 * Ke + 1000) * P5
        = (2 * Ke + 160) * P5 + (2 * Ks + 2 * Kb + Kr + 840) * P5 := by ring
    have hslack : 8 * P5 + 21 ≤ (2 * Ks + 2 * Kb + Kr + 840) * P5 := by
      have h1 : 840 * P5 ≤ (2 * Ks + 2 * Kb + Kr + 840) * P5 :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : 8 * P5 + 21 ≤ 840 * P5 := by omega
      omega
    have hgoal : buildFSATBound n
        = (2 * Ks + 2 * Kb + Kr + 2 * Ke + 1000) * P5 := by
      rw [buildFSATBound, buildFSATK, ← hKs, ← hKb, ← hKr, ← hKe, ← hΩdef,
        ← hP2, ← hP3, ← hP4, ← hP5]
    rw [hgoal]
    omega

/-! ### The mechanical witness fields -/

/-- `buildFSAT` touches only registers `< regFrame` (= 57): every register
constant is `≤ 56` (`ZERO`). -/
theorem buildFSAT_usesBelow : Cmd.UsesBelow buildFSAT regFrame := by
  simp only [buildFSAT, precompLen, computeWF, andFlag, leCheck, dvdBody, dvdCheck,
    cardLenElemBody, cardLenItem, cardLenCardBody, cardLenCheck,
    emit0, emit1, emitFtrue, emitFandTag, emitForrTag, emitFalse, emitVarW, emitLitAt,
    emitBitsFromScan, bsBody, emitBitsFromSent, sentBitBody,
    emitCardsAt, cardEmitBody, emitAllSteps, stepBody, stepIterBody, lineBody,
    readOneFinal, readFinBody, emitFinal, finalStepBody, finalStepIterBody,
    finalStringBody,
    Cmd.UsesBelow, Op.UsesBelow,
    FOUT, OUT, SCAN, LREG, LINEL, STEPO, STARTA, STARTB, WREG, TFLG, DONE, SUMW,
    GFLG, REM, SCANF, FSTART, BLEN, STEPSL, EMARK, KLINE, KSTEP, KCARD, KBIT, KFS,
    KFSTEP, KTMP, KTMP2, LREG1, FBITS, GWF, MREM, MCHK, MGE, SCANW, CLEN, ZERO,
    OFFSET, WIDTH, INIT, CARDS, FINAL, STEPS, regFrame]
  simp

/-- Every value written into `encodeIn C`'s registers is bit-valued. -/
theorem encodeIn_bitState (C : BinaryCC) : Compile.BitState (encodeIn C) := by
  have hbitsNat : ∀ (bs : List Bool) x, x ∈ FlatCCBinFree.bitsNat bs → x ≤ 1 := by
    intro bs x hx
    simp only [FlatCCBinFree.bitsNat, List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    cases b <;> simp
  have hset : ∀ (s : State) (i : Nat) (v : List Nat),
      Compile.BitState s → (∀ x ∈ v, x ≤ 1) → Compile.BitState (List.set s i v) := by
    intro s i v hs hv reg hreg x hx
    rcases List.mem_or_eq_of_mem_set hreg with hmem | rfl
    · exact hs reg hmem x hx
    · exact hv x hx
  have hbase : Compile.BitState (List.replicate regFrame ([] : List Nat)) := by
    intro reg hreg x hx
    rw [List.eq_of_mem_replicate hreg] at hx
    cases hx
  unfold encodeIn
  exact hset _ _ _ (hset _ _ _ (hset _ _ _ (hset _ _ _ (hset _ _ _
    (hset _ _ _ hbase
      (fun x hx => le_of_eq (List.eq_of_mem_replicate hx)))
      (fun x hx => le_of_eq (List.eq_of_mem_replicate hx)))
      (fun x hx => le_of_eq (List.eq_of_mem_replicate hx)))
      (hbitsNat C.init))
      (FlatCCBinFree.encCardsOut_bit _))
      (FlatTCCFree.encFinal_bit _)

/-! ## 5. The free witness and the headline `⪯p'` -/

/-- **`BinaryCC_to_FSAT_instance` as a concrete layer program** — the free
`PolyTimeComputableLang` witness (template: `flatCCBin_reductionLang`).
`decodeOut` inverts the injective prefix serialization (`decodeF_serF`). -/
noncomputable def binaryCCFSAT_reductionLang :
    PolyTimeComputableLang BinaryCC_to_FSAT_instance where
  c := buildFSAT
  encodeIn := encodeIn
  decodeOut := decodeOut
  cost_bound := buildFSATBound
  cost_bound_poly := buildFSATBound_poly
  cost_bound_mono := buildFSATBound_mono
  encBound := fun n => 2 * n + 1
  encBound_poly :=
    inOPoly_add (inOPoly_mul (inOPoly_const 2) inOPoly_id) (inOPoly_const 1)
  encBound_mono := fun a b h => Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1
  encodeIn_size := encodeIn_size_le
  computes := fun C => decodeOut_of_serF _ _ (buildFSAT_run C)
  cost_le := buildFSAT_cost_le
  output_size_le := buildFSATBound_output
  enc_bit := encodeIn_bitState
  regBound := regFrame
  usesBelow := buildFSAT_usesBelow
  width_le := fun C => by
    show (encodeIn C).length ≤ regFrame
    simp [encodeIn, List.length_set, List.length_replicate]
  decode_agree := fun C m => by
    have hagree : AgreeBelow regFrame (encodeIn C ++ List.replicate m []) (encodeIn C) :=
      fun r _ => State.get_append_replicate_nil (encodeIn C) m r
    have h := Cmd.eval_agree buildFSAT regFrame buildFSAT_usesBelow hagree FOUT
      (by decide)
    simp only [decodeOut]
    rw [h]

/-- **`BinaryCC ⪯p' FSAT`** — the next live honest TM-backed reduction on the
sound tail (after `flatCC_reducesPolyMO'`), the expensive Tseytin/tableau step
as a free-line witness. Axiom-clean: `[propext, Classical.choice, Quot.sound]`. -/
theorem binaryCC_reducesPolyMO' : BinaryCCLang ⪯p' FSAT :=
  reducesPolyMO'_of_langFree binaryCCFSAT_reductionLang BinaryCC_to_FSAT_instance_correct

end BinaryCCFSATFree
