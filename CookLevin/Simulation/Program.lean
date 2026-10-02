import CookLevin.Simulation.Step

set_option autoImplicit false

/-! # The register program simulating a verifier machine

`simTM M acc a k b ct kt dt` runs on the input layout `[bits x, bits c]` and decides

    |c| ≤ a·|x|^k + b  ∧  M, run for T(|x| + |c|) steps on `pairTape x c`, is in state `acc`

where `T n = ct·(n+1)^kt + dt`. It consists of five phases:

1. `lenCode`: `FAIL := [1]` iff `|c| > a·|x|^k + b`;
2. `timerCode`: `TIMER := 1^(T(|x|+|c|))`;
3. `initCode`: the registers represent the initial configuration on `pairTape x c`;
4. `mainLoop`: `TIMER` times `guardedStep M` (`Simulation/Step.lean`), then clear the scratch
   registers;
5. `verdict`: `XO := [1]` iff the state is `acc` and `FAIL` is not set, else `[0]`.

`simTM_get` states the result.
-/

namespace CookLevin.Sim

open CookLevin.Lang FrontPieces

/-! ## Registers outside the step -/

def CNT : Var := 17
def TIMER : Var := 18
def TL : Var := 19
def BASE : Var := 20
def PTMP : Var := 21
def PL : Var := 22
def FAIL : Var := 23
def SCAN : Var := 24
def SB : Var := 25
/-- Every register of `simTM` is below `REGS`. -/
def REGS : Nat := 26

/-! ## Small pieces -/

/-- Append constant bits to `dst`. -/
def appendC (dst : Var) (bits : List Nat) : Cmd := appendConst nop dst bits

theorem appendC_run (dst : Var) (bits : List Nat) (s : State) (hd : dst ≠ JK)
    (hb : ∀ x ∈ bits, x ≤ 1) :
    State.get ((appendC dst bits).eval s) dst = State.get s dst ++ bits
    ∧ ∀ r, r ≠ dst → r ≠ JK → State.get ((appendC dst bits).eval s) r = State.get s r := by
  obtain ⟨h1, h2, -⟩ := appendConst_run dst bits nop s
  refine ⟨?_, ?_⟩
  · rw [show appendC dst bits = appendConst nop dst bits from rfl, h1, nop_get s dst hd,
      map_bitVal_of_bits bits hb]
  · intro r r1 r2
    rw [show appendC dst bits = appendConst nop dst bits from rfl, h2 r r1, nop_get s r r2]

/-- Clear a list of registers. -/
def clearList : List Var → Cmd
  | [] => nop
  | r :: rs => .op (.clear r) ;; clearList rs

theorem clearList_run : ∀ (l : List Var) (s : State),
    (∀ r, r ∈ l → State.get ((clearList l).eval s) r = [])
    ∧ ∀ r, r ∉ l → r ≠ JK → State.get ((clearList l).eval s) r = State.get s r
  | [], s => by
      refine ⟨fun _ h => absurd h List.not_mem_nil, fun r _ hr => nop_get s r hr⟩
  | a :: l, s => by
      obtain ⟨h1, h2⟩ := clearList_run l ((Cmd.op (.clear a)).eval s)
      refine ⟨?_, ?_⟩
      · intro r hr
        show State.get ((clearList l).eval ((Cmd.op (.clear a)).eval s)) r = []
        by_cases hrl : r ∈ l
        · exact h1 r hrl
        · have hra : r = a := by simpa [hrl] using hr
          by_cases hj : r = JK
          · -- `JK` is cleared by the final `nop`
            subst hj
            have : ∀ (l : List Var) (s : State), State.get ((clearList l).eval s) JK = [] := by
              intro l
              induction l with
              | nil => intro s; exact State.get_set_eq _ _ _
              | cons b l ih => intro s; exact ih _
            exact this l _
          · rw [h2 r hrl hj, hra]; exact State.get_set_eq _ _ _
      · intro r hr hj
        show State.get ((clearList l).eval ((Cmd.op (.clear a)).eval s)) r = _
        rw [h2 r (fun h => hr (List.mem_cons_of_mem _ h)) hj]
        exact State.get_set_ne _ _ _ _ (fun h => hr (by simp [h]))

/-- The scratch registers below `KB`. -/
def tempRegs : List Var := [XO, CI, SY, CK, T1, T2, TT, TM, HB, FL, BK, JK]

def clearTemps : Cmd := clearList tempRegs

/-- Every register below `KB` is one of the five representation registers or scratch. -/
theorem below_KB (r : Var) (hr : r < KB) :
    r = LT ∨ r = RT ∨ r = EX ∨ r = ST ∨ r = HL ∨ r ∈ tempRegs := by
  simp only [KB] at hr
  interval_cases r <;> decide

theorem clearTemps_temp (s : State) (r : Var) (hr : r ∈ tempRegs) :
    State.get (clearTemps.eval s) r = [] := (clearList_run tempRegs s).1 r hr

theorem clearTemps_frame (s : State) (r : Var) (hr : r ∉ tempRegs) :
    State.get (clearTemps.eval s) r = State.get s r :=
  (clearList_run tempRegs s).2 r hr (fun h => hr (by simp [h, tempRegs]))

theorem not_temp_main : LT ∉ tempRegs ∧ RT ∉ tempRegs ∧ EX ∉ tempRegs ∧ ST ∉ tempRegs
    ∧ HL ∉ tempRegs := by decide

theorem Repr.frame {M : FlatTM} {cfg : FlatTMConfig} {s s' : State} (hR : Repr M cfg s)
    (hfr : ∀ r, r = LT ∨ r = RT ∨ r = EX ∨ r = ST ∨ r = HL → State.get s' r = State.get s r) :
    Repr M cfg s' := by
  obtain ⟨l, h, rt, ht, hc⟩ := hR
  exact ⟨l, h, rt, ht, hc.frame hfr⟩

theorem Repr.clearTemps {M : FlatTM} {cfg : FlatTMConfig} {s : State} (hR : Repr M cfg s) :
    Repr M cfg (clearTemps.eval s) :=
  hR.frame fun r hr => clearTemps_frame s r (by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)

/-! ## Phase 1: the certificate length test -/

def failBody : Cmd :=
  .op (.nonEmpty SB SCAN) ;; .ifBit SB (.op (.tail SCAN SCAN)) (emitConst FAIL [1])

def lenCode (a k b : Nat) : Cmd :=
  tallyCells CNT TL [XO] ;; emitConst PL (List.replicate a 1) ;;
  powLoop CNT TL PTMP PL k ;; appendC PL (List.replicate b 1) ;;
  .op (.copy SCAN PL) ;; emitConst FAIL [0] ;; .forBnd CNT CI failBody

/-- The registers `lenCode` writes. -/
def lenRegs : List Var := [CNT, TL, PL, PTMP, SCAN, SB, FAIL, JK]

theorem failLoop_run (P : Nat) (s : State) (hS : State.get s SCAN = List.replicate P 1)
    (hF : State.get s FAIL = [0]) :
    State.get ((Cmd.forBnd CNT CI failBody).eval s) FAIL
        = (if (State.get s CI).length ≤ P then [0] else [1])
    ∧ ∀ r, r ≠ CNT → r ≠ SCAN → r ≠ SB → r ≠ FAIL →
        State.get ((Cmd.forBnd CNT CI failBody).eval s) r = State.get s r := by
  rw [Cmd.eval_forBnd]
  have key := Cmd.foldlState_range_induct failBody CNT (State.get s CI).length s
    (fun i st => State.get st SCAN = List.replicate (P - i) 1
      ∧ State.get st FAIL = (if i ≤ P then [0] else [1])
      ∧ ∀ r, r ≠ CNT → r ≠ SCAN → r ≠ SB → r ≠ FAIL → State.get st r = State.get s r)
    ⟨by simpa using hS, by simpa using hF, fun _ _ _ _ _ => rfl⟩
    (by
      intro i st _ ⟨h1, h2, h3⟩
      set st' := st.set CNT (List.replicate i 1) with hst'
      have g1 : State.get st' SCAN = List.replicate (P - i) 1 := by
        rw [hst', State.get_set_ne _ _ _ _ (by decide), h1]
      have g2 : State.get st' FAIL = (if i ≤ P then [0] else [1]) := by
        rw [hst', State.get_set_ne _ _ _ _ (by decide), h2]
      unfold failBody
      simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
      set st2 := st'.set SB (if (State.get st' SCAN).isEmpty then [0] else [1]) with hst2
      by_cases hiP : i < P
      · have hSB : State.get st2 SB = [1] := by
          rw [hst2, State.get_set_eq, g1]
          obtain ⟨j, hj⟩ : ∃ j, P - i = j + 1 := ⟨P - i - 1, by omega⟩
          rw [hj]; simp
        rw [Cmd.eval_ifBit_true _ _ _ _ hSB]
        simp only [Cmd.eval_op, Op.eval]
        refine ⟨?_, ?_, ?_⟩
        · rw [State.get_set_eq, hst2, State.get_set_ne _ _ _ _ (by decide), g1,
            List.tail_replicate]
          (congr 1; try omega)
        · rw [State.get_set_ne _ _ _ _ (by decide), hst2, State.get_set_ne _ _ _ _ (by decide),
            g2, if_pos (by omega), if_pos (by omega)]
        · intro r r1 r2 r3 r4
          rw [State.get_set_ne _ _ _ _ r2, hst2, State.get_set_ne _ _ _ _ r3, hst',
            State.get_set_ne _ _ _ _ r1, h3 r r1 r2 r3 r4]
      · have hSB : State.get st2 SB ≠ [1] := by
          rw [hst2, State.get_set_eq, g1, show P - i = 0 by omega]; simp
        rw [Cmd.eval_ifBit_false _ _ _ _ hSB]
        refine ⟨?_, ?_, ?_⟩
        · rw [emit_frame _ _ _ _ (by decide), hst2, State.get_set_ne _ _ _ _ (by decide), g1]
          congr 1; omega
        · rw [emit_get _ _ _ (by simp), if_neg (by omega)]
        · intro r r1 r2 r3 r4
          rw [emit_frame _ _ _ _ r4, hst2, State.get_set_ne _ _ _ _ r3, hst',
            State.get_set_ne _ _ _ _ r1, h3 r r1 r2 r3 r4])
  exact ⟨key.2.1, key.2.2⟩

theorem lenCode_run (a k b : Nat) (s : State) :
    State.get ((lenCode a k b).eval s) FAIL
        = (if (State.get s CI).length ≤ a * (State.get s XO).length ^ k + b then [0] else [1])
    ∧ ∀ r, r ∉ lenRegs → State.get ((lenCode a k b).eval s) r = State.get s r := by
  unfold lenCode
  simp only [Cmd.eval_seq]
  -- tally
  obtain ⟨y1, y2⟩ := tallyCells_run CNT TL [XO] s (by decide) (by decide)
  set s1 := (tallyCells CNT TL [XO]).eval s with hs1
  have hTL : State.get s1 TL = List.replicate (State.get s XO).length 1 := by
    rw [y1]; simp
  -- seed
  set s2 := (emitConst PL (List.replicate a 1)).eval s1 with hs2
  have hPL2 : State.get s2 PL = List.replicate a 1 := emit_get _ _ _ (replicate_one_bits _)
  have f2 : ∀ r, r ≠ PL → State.get s2 r = State.get s1 r := fun r hr => emit_frame _ _ _ r hr
  -- power
  obtain ⟨p1, p2, -⟩ := powLoop_run CNT TL PTMP PL k s2 (State.get s XO).length a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [f2 _ (by decide), hTL]) hPL2
  set s3 := (powLoop CNT TL PTMP PL k).eval s2 with hs3
  -- append
  obtain ⟨q1, q2⟩ := appendC_run PL (List.replicate b 1) s3 (by decide) (replicate_one_bits _)
  set s4 := (appendC PL (List.replicate b 1)).eval s3 with hs4
  have hPL4 : State.get s4 PL
      = List.replicate (a * (State.get s XO).length ^ k + b) 1 := by
    rw [q1, p1, List.replicate_add]
  simp only [Cmd.eval_op, Op.eval]
  set s5 := s4.set SCAN (State.get s4 PL) with hs5
  set s6 := (emitConst FAIL [0]).eval s5 with hs6
  have hS6 : State.get s6 SCAN = List.replicate (a * (State.get s XO).length ^ k + b) 1 := by
    rw [hs6, emit_frame _ _ _ _ (by decide), hs5, State.get_set_eq, hPL4]
  obtain ⟨l1, l2⟩ := failLoop_run _ s6 hS6 (emit_get _ _ _ (by simp))
  -- frame through the phases
  have fr : ∀ r, r ∉ lenRegs → State.get s6 r = State.get s r := by
    intro r hr
    simp only [lenRegs, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hr
    rw [hs6, emit_frame _ _ _ _ r7, hs5, State.get_set_ne _ _ _ _ r5, q2 r r3 r8,
      p2 r r3 r4 r1, f2 r r3, y2 r r2 r1]
  have hCI : State.get s6 CI = State.get s CI := fr CI (by decide)
  refine ⟨?_, ?_⟩
  · rw [l1, hCI]
  · intro r hr
    have hr' := hr
    simp only [lenRegs, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr'
    obtain ⟨r1, -, -, -, r5, r6, r7, -⟩ := hr'
    rw [l2 r r1 r5 r6 r7, fr r hr]

/-! ## Phase 2: the time budget -/

/-- `T n = ct·(n+1)^kt + dt`. -/
def budget (ct kt dt n : Nat) : Nat := ct * (n + 1) ^ kt + dt

def timerCode (ct kt dt : Nat) : Cmd :=
  tallyCells CNT TL [XO, CI] ;; unaryMonomial ct kt dt CNT BASE PTMP TL TIMER

def timerRegs : List Var := [CNT, TL, BASE, PTMP, TIMER]

theorem timerCode_run (ct kt dt : Nat) (s : State) :
    State.get ((timerCode ct kt dt).eval s) TIMER
        = List.replicate (budget ct kt dt ((State.get s XO).length + (State.get s CI).length)) 1
    ∧ ∀ r, r ∉ timerRegs → State.get ((timerCode ct kt dt).eval s) r = State.get s r := by
  unfold timerCode
  rw [Cmd.eval_seq]
  obtain ⟨y1, y2⟩ := tallyCells_run CNT TL [XO, CI] s (by decide) (by decide)
  have hTL : State.get ((tallyCells CNT TL [XO, CI]).eval s) TL
      = List.replicate ((State.get s XO).length + (State.get s CI).length) 1 := by
    rw [y1]; simp
  obtain ⟨u1, u2, -⟩ := unaryMonomial_run ct kt dt CNT BASE PTMP TL TIMER _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hTL
  refine ⟨u1, ?_⟩
  intro r hr
  simp only [timerRegs, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
  obtain ⟨r1, r2, r3, r4, r5⟩ := hr
  rw [u2 r r5 r3 r4 r1, y2 r r2 r1]

/-! ## Phase 3: the initial configuration -/

def bitBody (W : Nat) : Cmd :=
  .op (.head SB SCAN) ;; .op (.tail SCAN SCAN) ;;
  .ifBit SB (appendC RT (blk W 2)) (appendC RT (blk W 1))

/-- Append the blocks of `symbolsOf x` to `RT`, where `src` holds the bits of `x`. -/
def bitLoop (W : Nat) (src : Var) : Cmd :=
  .op (.copy SCAN src) ;; .forBnd CNT SCAN (bitBody W)

/-- The bits of a string as register cells. -/
def bitsOf (x : List Bool) : List Nat := x.map (fun b => if b then 1 else 0)

theorem blocks_append (W : Nat) (l₁ l₂ : List Nat) :
    blocks W (l₁ ++ l₂) = blocks W l₁ ++ blocks W l₂ := by
  simp [blocks, List.flatMap_append]

theorem bitLoop_run (W : Nat) (src : Var) (x : List Bool) (s : State)
    (hsrc : State.get s src = bitsOf x) :
    State.get ((bitLoop W src).eval s) RT = State.get s RT ++ blocks W (symbolsOf x)
    ∧ ∀ r, r ≠ RT → r ≠ SCAN → r ≠ SB → r ≠ CNT → r ≠ JK →
        State.get ((bitLoop W src).eval s) r = State.get s r := by
  unfold bitLoop
  rw [Cmd.eval_seq, Cmd.eval_op]
  simp only [Op.eval]
  set s1 := s.set SCAN (State.get s src) with hs1
  have hlen : (State.get s1 SCAN).length = x.length := by
    rw [hs1, State.get_set_eq, hsrc, bitsOf, List.length_map]
  rw [Cmd.eval_forBnd, hlen]
  have key := Cmd.foldlState_range_induct (bitBody W) CNT x.length s1
    (fun i st => i ≤ x.length ∧ State.get st SCAN = bitsOf (x.drop i)
      ∧ State.get st RT = State.get s RT ++ blocks W (symbolsOf (x.take i))
      ∧ ∀ r, r ≠ RT → r ≠ SCAN → r ≠ SB → r ≠ CNT → r ≠ JK → State.get st r = State.get s1 r)
    ⟨Nat.zero_le _, by rw [hs1, State.get_set_eq, hsrc]; rfl,
     by rw [hs1, State.get_set_ne _ _ _ _ (by decide)]; simp [symbolsOf],
     fun _ _ _ _ _ _ => rfl⟩
    (by
      intro i st hi ⟨_, h1, h2, h3⟩
      set st' := st.set CNT (List.replicate i 1) with hst'
      have hd : x.drop i = x[i] :: x.drop (i + 1) := List.drop_eq_getElem_cons hi
      have g1 : State.get st' SCAN = (if x[i] then 1 else 0) :: bitsOf (x.drop (i + 1)) := by
        rw [hst', State.get_set_ne _ _ _ _ (by decide), h1, hd]; rfl
      have g2 : State.get st' RT = State.get s RT ++ blocks W (symbolsOf (x.take i)) := by
        rw [hst', State.get_set_ne _ _ _ _ (by decide), h2]
      have htk : symbolsOf (x.take (i + 1)) = symbolsOf (x.take i) ++ [if x[i] then 2 else 1] := by
        simp only [symbolsOf]
        rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
          List.map_singleton]
      unfold bitBody
      simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, g1]
      set st2 := (st'.set SB [if x[i] then 1 else 0]).set SCAN
        (State.get (st'.set SB [if x[i] then 1 else 0]) SCAN).tail with hst2
      have e2SCAN : State.get st2 SCAN = bitsOf (x.drop (i + 1)) := by
        rw [hst2, State.get_set_eq, State.get_set_ne _ _ _ _ (by decide), g1]; rfl
      have e2RT : State.get st2 RT = State.get s RT ++ blocks W (symbolsOf (x.take i)) := by
        rw [hst2, State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide), g2]
      have e2fr : ∀ r, r ≠ RT → r ≠ SCAN → r ≠ SB → r ≠ CNT → r ≠ JK →
          State.get st2 r = State.get s1 r := by
        intro r r1 r2 r3 r4 r5
        rw [hst2, State.get_set_ne _ _ _ _ r2, State.get_set_ne _ _ _ _ r3, hst',
          State.get_set_ne _ _ _ _ r4, h3 r r1 r2 r3 r4 r5]
      have hSB : State.get st2 SB = [if x[i] then 1 else 0] := by
        rw [hst2, State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
      by_cases hx : x[i] = true
      · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hSB, if_pos hx])]
        obtain ⟨a1, a2⟩ := appendC_run RT (blk W 2) st2 (by decide) (blk_bits W 2)
        refine ⟨hi, ?_, ?_, ?_⟩
        · rw [a2 _ (by decide) (by decide), e2SCAN]
        · rw [a1, e2RT, htk, if_pos hx, blocks_append, List.append_assoc]
          simp [blocks]
        · intro r r1 r2 r3 r4 r5
          rw [a2 r r1 r5, e2fr r r1 r2 r3 r4 r5]
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hSB, if_neg hx]; simp)]
        obtain ⟨a1, a2⟩ := appendC_run RT (blk W 1) st2 (by decide) (blk_bits W 1)
        refine ⟨hi, ?_, ?_, ?_⟩
        · rw [a2 _ (by decide) (by decide), e2SCAN]
        · rw [a1, e2RT, htk, if_neg hx, blocks_append, List.append_assoc]
          simp [blocks]
        · intro r r1 r2 r3 r4 r5
          rw [a2 r r1 r5, e2fr r r1 r2 r3 r4 r5])
  obtain ⟨-, -, k2, k3⟩ := key
  refine ⟨?_, ?_⟩
  · rw [k2, List.take_of_length_le (le_refl _)]
  · intro r r1 r2 r3 r4 r5
    rw [k3 r r1 r2 r3 r4 r5, hs1, State.get_set_ne _ _ _ _ r2]

def initCode (M : FlatTM) : Cmd :=
  .op (.clear LT) ;; .op (.clear EX) ;; emitConst RT (blk (wid M) 3) ;;
  bitLoop (wid M) XO ;; appendC RT (blk (wid M) 0) ;; bitLoop (wid M) CI ;;
  appendC RT (blk (wid M) 0 ++ blk (wid M) 3) ;;
  emitConst ST (List.replicate M.start 1) ;; emitConst HL [haltBit M M.start] ;; clearTemps

def initRegs : List Var := [LT, EX, RT, SCAN, SB, CNT, ST, HL] ++ tempRegs

theorem symbolsOf_bound (y : List Bool) : ∀ v ∈ symbolsOf y, v < 4 := by
  intro v hv
  simp only [symbolsOf, List.mem_map] at hv
  obtain ⟨b, _, rfl⟩ := hv
  cases b <;> decide

theorem pairTape_bound (x c : List Bool) : ∀ v ∈ pairTape x c, v < 4 := by
  intro v hv
  simp only [pairTape, List.mem_cons, List.mem_append] at hv
  rcases hv with h | ((h | h) | h) | h
  · omega
  · exact symbolsOf_bound x v h
  · simp at h; omega
  · exact symbolsOf_bound c v h
  · simp at h; omega

theorem initCode_run (M : FlatTM) (x c : List Bool) (s : State)
    (hx : State.get s XO = bitsOf x) (hc : State.get s CI = bitsOf c) :
    Repr M (initFlatConfig M [pairTape x c]) ((initCode M).eval s)
    ∧ (∀ r ∈ tempRegs, State.get ((initCode M).eval s) r = [])
    ∧ ∀ r, r ∉ initRegs → State.get ((initCode M).eval s) r = State.get s r := by
  set W := wid M with hW
  unfold initCode
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
  set s1 := (s.set LT []).set EX [] with hs1
  set s2 := (emitConst RT (blk W 3)).eval s1 with hs2
  have f2 : ∀ r, r ≠ RT → State.get s2 r = State.get s1 r := fun r hr => emit_frame _ _ _ r hr
  have hR2 : State.get s2 RT = blk W 3 := emit_get _ _ _ (blk_bits W 3)
  obtain ⟨b1, b2⟩ := bitLoop_run W XO x s2 (by
    rw [f2 _ (by decide), hs1, State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide), hx])
  set s3 := (bitLoop W XO).eval s2 with hs3
  obtain ⟨a1, a2⟩ := appendC_run RT (blk W 0) s3 (by decide) (blk_bits W 0)
  set s4 := (appendC RT (blk W 0)).eval s3 with hs4
  obtain ⟨c1, c2⟩ := bitLoop_run W CI c s4 (by
    rw [a2 _ (by decide) (by decide), b2 _ (by decide) (by decide) (by decide) (by decide)
      (by decide), f2 _ (by decide), hs1, State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide), hc])
  set s5 := (bitLoop W CI).eval s4 with hs5
  obtain ⟨d1, d2⟩ := appendC_run RT (blk W 0 ++ blk W 3) s5 (by decide)
    (fun v hv => by
      rcases List.mem_append.mp hv with hv | hv
      · exact blk_bits W 0 v hv
      · exact blk_bits W 3 v hv)
  set s6 := (appendC RT (blk W 0 ++ blk W 3)).eval s5 with hs6
  have hRT6 : State.get s6 RT = blocks W (pairTape x c) := by
    rw [d1, c1, a1, b1, hR2]
    simp [pairTape, blocks]
  set s7 := (emitConst ST (List.replicate M.start 1)).eval s6 with hs7
  set s8 := (emitConst HL [haltBit M M.start]).eval s7 with hs8
  -- the frame of phases s1 … s8, for a register outside `initRegs`
  have fr8 : ∀ r, r ≠ LT → r ≠ EX → r ≠ RT → r ≠ SCAN → r ≠ SB → r ≠ CNT → r ≠ JK → r ≠ ST →
      r ≠ HL → State.get s8 r = State.get s r := by
    intro r r1 r2 r3 r4 r5 r6 r7 r8 r9
    rw [hs8, emit_frame _ _ _ _ r9, hs7, emit_frame _ _ _ _ r8, d2 r r3 r7,
      c2 r r3 r4 r5 r6 r7, a2 r r3 r7, b2 r r3 r4 r5 r6 r7, f2 r r3, hs1,
      State.get_set_ne _ _ _ _ r2, State.get_set_ne _ _ _ _ r1]
  have hR8 : Repr M (initFlatConfig M [pairTape x c]) s8 := by
    refine ⟨[], 0, pairTape x c, rfl, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro v hv; have := pairTape_bound x c v hv; unfold wid; omega
    · rw [hs8, emit_frame _ _ _ _ (by decide), hs7, emit_frame _ _ _ _ (by decide),
        d2 _ (by decide) (by decide), c2 _ (by decide) (by decide) (by decide) (by decide)
        (by decide), a2 _ (by decide) (by decide), b2 _ (by decide) (by decide) (by decide)
        (by decide) (by decide), f2 _ (by decide), hs1, State.get_set_ne _ _ _ _ (by decide),
        State.get_set_eq]
      rfl
    · rw [hs8, emit_frame _ _ _ _ (by decide), hs7, emit_frame _ _ _ _ (by decide), hRT6]
      rfl
    · rw [hs8, emit_frame _ _ _ _ (by decide), hs7, emit_frame _ _ _ _ (by decide),
        d2 _ (by decide) (by decide), c2 _ (by decide) (by decide) (by decide) (by decide)
        (by decide), a2 _ (by decide) (by decide), b2 _ (by decide) (by decide) (by decide)
        (by decide) (by decide), f2 _ (by decide), hs1, State.get_set_eq]
      simp [zip]
    · rw [hs8, emit_frame _ _ _ _ (by decide), hs7]
      exact emit_get _ _ _ (replicate_one_bits _)
    · rw [hs8]
      exact emit_get _ _ _ (haltBit_bits M _)
  refine ⟨hR8.clearTemps, fun r hr => clearTemps_temp s8 r hr, ?_⟩
  intro r hr
  have hr' : r ∉ tempRegs := fun h => hr (List.mem_append_right _ h)
  rw [clearTemps_frame s8 r hr']
  simp only [initRegs, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
    not_or] at hr
  obtain ⟨⟨r1, r2, r3, r4, r5, r6, r7, r8⟩, -⟩ := hr
  exact fr8 r r1 r2 r3 r4 r5 r6 (fun h => hr' (by simp [h, tempRegs])) r7 r8

/-! ## Phase 4: the main loop -/

def loopBody (M : FlatTM) : Cmd := guardedStep M ;; clearTemps

def mainLoop (M : FlatTM) : Cmd := .forBnd CNT TIMER (loopBody M)

theorem mainLoop_run (M : FlatTM) (hM : validFlatTM M) (h1 : M.tapes = 1)
    (cfg : FlatTMConfig) (s : State) (hR : Repr M cfg s) :
    Repr M ((stepCfg M)^[(State.get s TIMER).length] cfg) ((mainLoop M).eval s) := by
  unfold mainLoop
  rw [Cmd.eval_forBnd]
  refine Cmd.foldlState_range_induct (loopBody M) CNT _ s
    (fun i st => Repr M ((stepCfg M)^[i] cfg) st) hR ?_
  intro i st _ hi
  have hi' : Repr M ((stepCfg M)^[i] cfg) (st.set CNT (List.replicate i 1)) :=
    hi.frame fun r hr => State.get_set_ne _ _ _ _ (by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  unfold loopBody
  rw [Cmd.eval_seq, Function.iterate_succ_apply']
  exact (guardedStep_run M hM h1 _ _ hi').clearTemps

/-! ## Phase 5: the verdict -/

def verdict (acc : Nat) : Cmd :=
  emitConst CK (List.replicate acc 1) ;; .op (.eqBit XO ST CK) ;;
  .ifBit FAIL (emitConst XO [0]) nop

theorem verdict_run (acc q : Nat) (fail : Bool) (s : State)
    (hST : State.get s ST = List.replicate q 1)
    (hF : State.get s FAIL = (if fail then [1] else [0])) :
    State.get ((verdict acc).eval s) XO = (if q = acc ∧ fail = false then [1] else [0]) := by
  unfold verdict
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
  set s1 := (emitConst CK (List.replicate acc 1)).eval s with hs1
  set s2 := s1.set XO (if State.get s1 ST = State.get s1 CK then [1] else [0]) with hs2
  have hX : State.get s2 XO = if q = acc then [1] else [0] := by
    rw [hs2, State.get_set_eq, hs1, emit_frame _ _ _ _ (by decide), hST,
      emit_get _ _ _ (replicate_one_bits _)]
    by_cases h : q = acc
    · simp [h]
    · rw [if_neg (fun h' => h (replicate_one_inj h')), if_neg h]
  have hF2 : State.get s2 FAIL = (if fail then [1] else [0]) := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide), hs1, emit_frame _ _ _ _ (by decide), hF]
  cases fail with
  | true =>
      rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hF2]; rfl), emit_get _ _ _ (by simp)]
      simp
  | false =>
      rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hF2]; simp), nop_get _ _ (by decide), hX]
      simp

/-- The simulation program. -/
def simTM (M : FlatTM) (acc a k b ct kt dt : Nat) : Cmd :=
  lenCode a k b ;; timerCode ct kt dt ;; initCode M ;; mainLoop M ;; verdict acc

/-! ## Registers touched -/

section UsesBelow

open CookLevin.Lang.FrontWitness

/-- Discharge a register bound, unfolding `UsesBelow` on a single operation if needed. -/
macro "ubd" : tactic => `(tactic| first | decide | (simp only [Cmd.UsesBelow, Op.UsesBelow, nop]; decide))

theorem nop_ub : Cmd.UsesBelow nop KB := by ubd

theorem takeRep_ub (dst : Var) (hd : dst < KB) : ∀ n, Cmd.UsesBelow (takeRep n dst) KB
  | 0 => nop_ub
  | n + 1 => ⟨takeRep_ub dst hd n, ⟨by ubd, by ubd⟩, ⟨hd, hd, by ubd⟩,
      ⟨by ubd, by ubd⟩⟩

theorem takeTo_ub (n : Nat) (dst src : Var) (hd : dst < KB) (hs : src < KB) :
    Cmd.UsesBelow (takeTo n dst src) KB :=
  ⟨hd, ⟨by ubd, hs⟩, takeRep_ub dst hd n⟩

theorem dropRep_ub (r : Var) (hr : r < KB) : ∀ n, Cmd.UsesBelow (dropRep n r) KB
  | 0 => nop_ub
  | n + 1 => ⟨dropRep_ub r hr n, hr, hr⟩

theorem writeCode_ub (W : Nat) (w : Option Nat) : Cmd.UsesBelow (writeCode W w) KB := by
  cases w with
  | none => exact nop_ub
  | some v =>
      exact ⟨⟨by ubd, by ubd⟩, by ubd, nop_ub, dropRep_ub RT (by ubd) W,
        emitConst_usesBelow (by ubd), by ubd, by ubd, by ubd⟩

theorem moveCode_ub (W : Nat) (m : TMMove) : Cmd.UsesBelow (moveCode W m) KB := by
  cases m with
  | Nmove => exact nop_ub
  | Rmove =>
      exact ⟨⟨by ubd, by ubd⟩, by ubd,
        ⟨takeTo_ub W BK RT (by ubd) (by ubd), dropRep_ub RT (by ubd) W,
          by ubd, by ubd, by ubd⟩, by ubd⟩
  | Lmove =>
      exact ⟨⟨by ubd, by ubd⟩, by ubd, ⟨by ubd, by ubd⟩,
        takeTo_ub W BK LT (by ubd) (by ubd), dropRep_ub LT (by ubd) W,
          by ubd, by ubd, by ubd⟩

theorem testCode_ub (W : Nat) (e : FlatTMTransEntry) : Cmd.UsesBelow (testCode W e) KB :=
  ⟨emitConst_usesBelow (by ubd), ⟨by ubd, by ubd, by ubd⟩,
    emitConst_usesBelow (by ubd), ⟨by ubd, by ubd, by ubd⟩, by ubd,
    ⟨by ubd, by ubd⟩, by ubd⟩

theorem applyCode_ub (M : FlatTM) (W : Nat) (e : FlatTMTransEntry) :
    Cmd.UsesBelow (applyCode M W e) KB :=
  ⟨emitConst_usesBelow (by ubd), emitConst_usesBelow (by ubd), writeCode_ub W _,
    moveCode_ub W _⟩

theorem chainCode_ub (M : FlatTM) (W : Nat) :
    ∀ es, Cmd.UsesBelow (chainCode M W es) KB
  | [] => nop_ub
  | e :: es => ⟨testCode_ub W e, by ubd, applyCode_ub M W e, chainCode_ub M W es⟩

theorem clearList_ub : ∀ (l : List Var), (∀ r ∈ l, r < KB) → Cmd.UsesBelow (clearList l) KB
  | [], _ => nop_ub
  | r :: l, h => ⟨h r (by simp), clearList_ub l (fun x hx => h x (by simp [hx]))⟩

theorem loopBody_ub (M : FlatTM) : Cmd.UsesBelow (loopBody M) KB :=
  ⟨⟨by ubd, nop_ub, takeTo_ub _ SY RT (by ubd) (by ubd), chainCode_ub M _ _⟩,
    clearList_ub tempRegs (by ubd)⟩

theorem ub_mono {c : Cmd} (h : Cmd.UsesBelow c KB) : Cmd.UsesBelow c REGS :=
  Cmd.UsesBelow_mono (by ubd) h

theorem simTM_ub (M : FlatTM) (acc a k b ct kt dt : Nat) :
    Cmd.UsesBelow (simTM M acc a k b ct kt dt) REGS := by
  refine ⟨⟨tallyCells_usesBelow (by ubd) (by ubd) (by simp [XO, REGS]),
    emitConst_usesBelow (by ubd), powLoop_usesBelow k (by ubd) (by ubd) (by ubd)
      (by ubd), appendConst_usesBelow (ub_mono nop_ub) (by ubd), ⟨by ubd, by ubd⟩,
    emitConst_usesBelow (by ubd), by ubd, by ubd,
    ⟨by ubd, by ubd⟩, by ubd, ⟨by ubd, by ubd⟩,
      emitConst_usesBelow (by ubd)⟩, ?_, ?_, ?_, ?_⟩
  · exact ⟨tallyCells_usesBelow (by ubd) (by ubd) (by simp [XO, CI, REGS]),
      unaryMonomial_usesBelow (by ubd) (by ubd) (by ubd) (by ubd) (by ubd)⟩
  · refine ⟨by ubd, by ubd, emitConst_usesBelow (by ubd), ?_, ?_, ?_, ?_,
      emitConst_usesBelow (by ubd), emitConst_usesBelow (by ubd),
      ub_mono (clearList_ub tempRegs (by ubd))⟩ <;>
    first
      | exact appendConst_usesBelow (ub_mono nop_ub) (by ubd)
      | exact ⟨⟨by ubd, by ubd⟩, by ubd, by ubd,
          ⟨by ubd, by ubd⟩, ⟨by ubd, by ubd⟩, by ubd,
          appendConst_usesBelow (ub_mono nop_ub) (by ubd),
          appendConst_usesBelow (ub_mono nop_ub) (by ubd)⟩
  · exact ⟨by ubd, by ubd, ub_mono (loopBody_ub M)⟩
  · exact ⟨emitConst_usesBelow (by ubd), ⟨by ubd, by ubd, by ubd⟩, by ubd,
      emitConst_usesBelow (by ubd), ub_mono nop_ub⟩

end UsesBelow

/-! ## The program -/

/-- The input layout: `x` in `XO`, `c` in `CI`. -/
def inputState (x c : List Bool) : State := [bitsOf x, bitsOf c]

/-- **What `simTM` computes.** -/
theorem simTM_get (M : FlatTM) (hM : validFlatTM M) (h1 : M.tapes = 1)
    (acc a k b ct kt dt : Nat) (x c : List Bool) :
    State.get ((simTM M acc a k b ct kt dt).eval (inputState x c)) XO
      = (if ((stepCfg M)^[budget ct kt dt (x.length + c.length)]
              (initFlatConfig M [pairTape x c])).state_idx = acc
            ∧ c.length ≤ a * x.length ^ k + b
          then [1] else [0]) := by
  set s0 := inputState x c with hs0
  have hx0 : State.get s0 XO = bitsOf x := rfl
  have hc0 : State.get s0 CI = bitsOf c := rfl
  have hxl : (bitsOf x).length = x.length := by simp [bitsOf]
  have hcl : (bitsOf c).length = c.length := by simp [bitsOf]
  unfold simTM
  simp only [Cmd.eval_seq]
  obtain ⟨l1, l2⟩ := lenCode_run a k b s0
  set s1 := (lenCode a k b).eval s0 with hs1
  have hx1 : State.get s1 XO = bitsOf x := by rw [l2 _ (by decide), hx0]
  have hc1 : State.get s1 CI = bitsOf c := by rw [l2 _ (by decide), hc0]
  obtain ⟨m1, m2⟩ := timerCode_run ct kt dt s1
  set s2 := (timerCode ct kt dt).eval s1 with hs2
  have hx2 : State.get s2 XO = bitsOf x := by rw [m2 _ (by decide), hx1]
  have hc2 : State.get s2 CI = bitsOf c := by rw [m2 _ (by decide), hc1]
  obtain ⟨i1, -, i3⟩ := initCode_run M x c s2 hx2 hc2
  set s3 := (initCode M).eval s2 with hs3
  have hT3 : (State.get s3 TIMER).length = budget ct kt dt (x.length + c.length) := by
    rw [i3 _ (by decide), m1, hx1, hc1, hxl, hcl, List.length_replicate]
  have hF3 : State.get s3 FAIL
      = (if c.length ≤ a * x.length ^ k + b then [0] else [1]) := by
    rw [i3 _ (by decide), m2 _ (by decide), l1, hx0, hc0, hxl, hcl]
  have hR4 := mainLoop_run M hM h1 _ s3 i1
  rw [hT3] at hR4
  set s4 := (mainLoop M).eval s3 with hs4
  have hF4 : State.get s4 FAIL = State.get s3 FAIL := by
    rw [hs4, mainLoop, Cmd.eval_forBnd]
    exact Cmd.foldlState_frame (loopBody M) CNT _ s3 18 (by decide)
      (Cmd.UsesBelow_mono (by decide) (loopBody_ub M)) FAIL (by decide)
  obtain ⟨left, h, right, -, -, -, hST, -⟩ := hR4
  rw [verdict_run acc _ (decide (¬ c.length ≤ a * x.length ^ k + b)) s4 hST (by
    rw [hF4, hF3]; by_cases hh : c.length ≤ a * x.length ^ k + b <;> simp [hh])]
  by_cases hh : c.length ≤ a * x.length ^ k + b <;> simp [hh]

end CookLevin.Sim
