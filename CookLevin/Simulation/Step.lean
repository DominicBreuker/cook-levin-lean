import CookLevin.Simulation.Gadgets

set_option autoImplicit false

/-! # One step of a single-tape machine as a loop-free register program

`stepCode M` performs one step of the machine `M` on a configuration held in registers:

* `LT`, `RT`, `EX` hold the zipper of the tape (`Simulation/Zipper.lean`) as blocks of width
  `wid M` (`Simulation/Gadgets.lean`), the excess `EX` in unary;
* `ST` holds the state in unary, `HL` the bit `haltBit M state`.

The step reads the block under the head into `SY` and then tests the transition entries
in list order (`chainCode`): the first entry whose state and read symbol match is applied
(new state, write, move) and the rest are skipped, which is `List.find?` in `stepFlatTM`.
If no entry matches nothing changes, as in `runFlatTM`. `step_run` is the resulting
simulation lemma: from a representation of `cfg` the code produces a representation of
`stepCfg M cfg` (`loopBody` also skips halting configurations).
-/

namespace CookLevin.Sim

open CookLevin.Lang FrontPieces

/-- The block width used for `M`: larger than every symbol `M` writes and than the
symbols `0, …, 3` of the input conventions. -/
def wid (M : FlatTM) : Nat := M.sig + 4

/-- The halting bit of state `q`. -/
def haltBit (M : FlatTM) (q : Nat) : Nat := if M.halt.getD q false then 1 else 0

/-- The zipper registers hold `z`. -/
def ReprZ (W : Nat) (z : Zip) (s : State) : Prop :=
  State.get s LT = blocks W z.lft ∧ State.get s RT = blocks W z.rgt
    ∧ State.get s EX = List.replicate z.exc 1

/-- All cells of the zipper are at most `W`. -/
def Zip.Bounded (W : Nat) (z : Zip) : Prop := (∀ v ∈ z.lft, v ≤ W) ∧ ∀ v ∈ z.rgt, v ≤ W

/-! ## Writing -/

def writeCode (W : Nat) : Option Nat → Cmd
  | none => nop
  | some v => .op (.nonEmpty FL EX) ;; .ifBit FL nop
      (dropRep W RT ;; emitConst BK (blk W v) ;; .op (.concat RT BK RT))

theorem writeCode_run (W : Nat) (z : Zip) (w : Option Nat) (s : State)
    (hz : ReprZ W z s) (hb : z.Bounded W) :
    ReprZ W (z.write w) ((writeCode W w).eval s)
    ∧ State.get ((writeCode W w).eval s) ST = State.get s ST
    ∧ State.get ((writeCode W w).eval s) HL = State.get s HL := by
  obtain ⟨hL, hR, hE⟩ := hz
  cases w with
  | none =>
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
        (simp only [writeCode]; rw [nop_get _ _ (by decide)]) <;> assumption
  | some v =>
      simp only [writeCode, Cmd.eval_seq, Cmd.eval_op, Op.eval]
      set s1 := s.set FL (if (State.get s EX).isEmpty then [0] else [1]) with hs1
      by_cases he : z.exc = 0
      · have hFL : State.get s1 FL ≠ [1] := by
          rw [hs1, State.get_set_eq, hE, he]; simp
        rw [Cmd.eval_ifBit_false _ _ _ _ hFL]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
        obtain ⟨d1, d2⟩ := dropRep_run RT (by decide) W s1
        set s2 := (dropRep W RT).eval s1 with hs2
        set s3 := (emitConst BK (blk W v)).eval s2 with hs3
        have e3 : ∀ r, r ≠ BK → State.get s3 r = State.get s2 r :=
          fun r hr => emit_frame BK _ s2 r hr
        have hBK : State.get s3 BK = blk W v := emit_get BK _ s2 (blk_bits W v)
        have hs1g : ∀ r, r ≠ FL → State.get s1 r = State.get s r :=
          fun r hr => State.get_set_ne _ _ _ _ hr
        refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · simp only [Zip.write, if_pos he]
          rw [State.get_set_ne _ _ _ _ (by decide), e3 _ (by decide), d2 _ (by decide)
            (by decide), hs1g _ (by decide), hL]
        · simp only [Zip.write, if_pos he]
          rw [State.get_set_eq, hBK, e3 _ (by decide), d1, hs1g _ (by decide), hR,
            drop_blocks W _ hb.2, blocks_cons]
        · simp only [Zip.write, if_pos he]
          rw [State.get_set_ne _ _ _ _ (by decide), e3 _ (by decide), d2 _ (by decide)
            (by decide), hs1g _ (by decide), hE, he]
        · rw [State.get_set_ne _ _ _ _ (by decide), e3 _ (by decide), d2 _ (by decide)
            (by decide), hs1g _ (by decide)]
        · rw [State.get_set_ne _ _ _ _ (by decide), e3 _ (by decide), d2 _ (by decide)
            (by decide), hs1g _ (by decide)]
      · have hFL : State.get s1 FL = [1] := by
          rw [hs1, State.get_set_eq, hE]
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero he
          rw [hk]; simp
        rw [Cmd.eval_ifBit_true _ _ _ _ hFL]
        have hw : z.write (some v) = z := by simp [Zip.write, he]
        rw [hw]
        refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
          rw [nop_get _ _ (by decide), hs1, State.get_set_ne _ _ _ _ (by decide)]
        · exact hL
        · exact hR
        · exact hE

/-! ## Moving -/

def moveCode (W : Nat) : TMMove → Cmd
  | .Nmove => nop
  | .Rmove => .op (.nonEmpty FL RT) ;; .ifBit FL
      (takeTo W BK RT ;; dropRep W RT ;; .op (.concat LT BK LT)) (.op (.appendOne EX))
  | .Lmove => .op (.nonEmpty FL EX) ;; .ifBit FL (.op (.tail EX EX))
      (takeTo W BK LT ;; dropRep W LT ;; .op (.concat RT BK RT))

theorem moveCode_run (W : Nat) (hW : 0 < W) (z : Zip) (m : TMMove) (s : State)
    (hz : ReprZ W z s) (hb : z.Bounded W) :
    ReprZ W (z.move m) ((moveCode W m).eval s)
    ∧ State.get ((moveCode W m).eval s) ST = State.get s ST
    ∧ State.get ((moveCode W m).eval s) HL = State.get s HL := by
  obtain ⟨hL, hR, hE⟩ := hz
  cases m with
  | Nmove =>
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
        (simp only [moveCode]; rw [nop_get _ _ (by decide)]) <;> assumption
  | Rmove =>
      simp only [moveCode, Cmd.eval_seq, Cmd.eval_op, Op.eval]
      set s1 := s.set FL (if (State.get s RT).isEmpty then [0] else [1]) with hs1
      have hs1g : ∀ r, r ≠ FL → State.get s1 r = State.get s r :=
        fun r hr => State.get_set_ne _ _ _ _ hr
      rcases hrg : z.rgt with _ | ⟨a, rest⟩
      · have hFL : State.get s1 FL ≠ [1] := by
          rw [hs1, State.get_set_eq, hR, hrg]; simp
        rw [Cmd.eval_ifBit_false _ _ _ _ hFL]
        simp only [Cmd.eval_op, Op.eval, Zip.move, hrg]
        refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (by decide), hs1g _ (by decide), hL]
        · rw [State.get_set_ne _ _ _ _ (by decide), hs1g _ (by decide), hR, hrg]
        · rw [State.get_set_eq, hs1g _ (by decide), hE, List.replicate_succ']
        · rw [State.get_set_ne _ _ _ _ (by decide), hs1g _ (by decide)]
        · rw [State.get_set_ne _ _ _ _ (by decide), hs1g _ (by decide)]
      · have ha : a ≤ W := hb.2 a (by rw [hrg]; simp)
        have hFL : State.get s1 FL = [1] := by
          rw [hs1, State.get_set_eq, hR, hrg, blocks_cons]
          have := blk_ne_nil hW ha
          cases h : blk W a with
          | nil => exact absurd h this
          | cons _ _ => simp
        rw [Cmd.eval_ifBit_true _ _ _ _ hFL]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, Zip.move, hrg]
        obtain ⟨t1, t2⟩ := takeTo_run W BK RT s1 (by decide) (by decide) (by decide) (by decide)
        set s2 := (takeTo W BK RT).eval s1 with hs2
        obtain ⟨d1, d2⟩ := dropRep_run RT (by decide) W s2
        set s3 := (dropRep W RT).eval s2 with hs3
        have hRb : State.get s1 RT = blocks W (a :: rest) := by
          rw [hs1g _ (by decide), hR, hrg]
        have hbr : ∀ v ∈ a :: rest, v ≤ W := by rw [← hrg]; exact hb.2
        have hBK : State.get s3 BK = blk W a := by
          rw [d2 _ (by decide) (by decide), t1, hRb, take_blocks W _ hbr]; rfl
        refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · rw [State.get_set_eq, hBK, d2 _ (by decide) (by decide),
            t2 _ (by decide) (by decide) (by decide) (by decide), hs1g _ (by decide), hL,
            blocks_cons]
        · rw [State.get_set_ne _ _ _ _ (by decide), d1, t2 _ (by decide) (by decide)
            (by decide) (by decide), hRb, drop_blocks W _ hbr]; rfl
        · rw [State.get_set_ne _ _ _ _ (by decide), d2 _ (by decide) (by decide),
            t2 _ (by decide) (by decide) (by decide) (by decide), hs1g _ (by decide), hE]
        · rw [State.get_set_ne _ _ _ _ (by decide), d2 _ (by decide) (by decide),
            t2 _ (by decide) (by decide) (by decide) (by decide), hs1g _ (by decide)]
        · rw [State.get_set_ne _ _ _ _ (by decide), d2 _ (by decide) (by decide),
            t2 _ (by decide) (by decide) (by decide) (by decide), hs1g _ (by decide)]
  | Lmove =>
      simp only [moveCode, Cmd.eval_seq, Cmd.eval_op, Op.eval]
      set s1 := s.set FL (if (State.get s EX).isEmpty then [0] else [1]) with hs1
      have hs1g : ∀ r, r ≠ FL → State.get s1 r = State.get s r :=
        fun r hr => State.get_set_ne _ _ _ _ hr
      by_cases he : z.exc = 0
      · have hFL : State.get s1 FL ≠ [1] := by
          rw [hs1, State.get_set_eq, hE, he]; simp
        rw [Cmd.eval_ifBit_false _ _ _ _ hFL]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
        obtain ⟨t1, t2⟩ := takeTo_run W BK LT s1 (by decide) (by decide) (by decide) (by decide)
        set s2 := (takeTo W BK LT).eval s1 with hs2
        obtain ⟨d1, d2⟩ := dropRep_run LT (by decide) W s2
        set s3 := (dropRep W LT).eval s2 with hs3
        have hLb : State.get s1 LT = blocks W z.lft := by rw [hs1g _ (by decide), hL]
        have hBK : State.get s3 BK = symEnc W z.lft.head? := by
          rw [d2 _ (by decide) (by decide), t1, hLb, take_blocks W _ hb.1]
        have hLT : State.get s3 LT = blocks W z.lft.tail := by
          rw [d1, t2 _ (by decide) (by decide) (by decide) (by decide), hLb,
            drop_blocks W _ hb.1]
        have hRT : State.get s3 RT = blocks W z.rgt := by
          rw [d2 _ (by decide) (by decide), t2 _ (by decide) (by decide) (by decide)
            (by decide), hs1g _ (by decide), hR]
        have hEX : State.get s3 EX = List.replicate z.exc 1 := by
          rw [d2 _ (by decide) (by decide), t2 _ (by decide) (by decide) (by decide)
            (by decide), hs1g _ (by decide), hE]
        have hST : State.get s3 ST = State.get s ST := by
          rw [d2 _ (by decide) (by decide), t2 _ (by decide) (by decide) (by decide)
            (by decide), hs1g _ (by decide)]
        have hHL : State.get s3 HL = State.get s HL := by
          rw [d2 _ (by decide) (by decide), t2 _ (by decide) (by decide) (by decide)
            (by decide), hs1g _ (by decide)]
        refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (by decide), hLT]
          rcases hl : z.lft with _ | ⟨a, l⟩ <;> simp [Zip.move, he, hl]
        · rw [State.get_set_eq, hBK, hRT]
          rcases hl : z.lft with _ | ⟨a, l⟩ <;> simp [Zip.move, he, hl, symEnc, blocks_cons]
        · rw [State.get_set_ne _ _ _ _ (by decide), hEX]
          rcases hl : z.lft with _ | ⟨a, l⟩ <;> simp [Zip.move, he, hl]
        · rw [State.get_set_ne _ _ _ _ (by decide), hST]
        · rw [State.get_set_ne _ _ _ _ (by decide), hHL]
      · have hFL : State.get s1 FL = [1] := by
          rw [hs1, State.get_set_eq, hE]
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero he
          rw [hk]; simp
        rw [Cmd.eval_ifBit_true _ _ _ _ hFL]
        simp only [Cmd.eval_op, Op.eval, Zip.move, if_neg he]
        refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (by decide), hs1g _ (by decide), hL]
        · rw [State.get_set_ne _ _ _ _ (by decide), hs1g _ (by decide), hR]
        · rw [State.get_set_eq, hs1g _ (by decide), hE, List.tail_replicate]
        · rw [State.get_set_ne _ _ _ _ (by decide), hs1g _ (by decide)]
        · rw [State.get_set_ne _ _ _ _ (by decide), hs1g _ (by decide)]

/-! ## Bounds are preserved -/

theorem Zip.Bounded.write {W : Nat} {z : Zip} (hz : z.Bounded W) (w : Option Nat)
    (hw : ∀ v, w = some v → v ≤ W) : (z.write w).Bounded W := by
  cases w with
  | none => exact hz
  | some v =>
      unfold Zip.write
      split_ifs
      · refine ⟨hz.1, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hw x rfl
        · exact hz.2 x (List.mem_of_mem_tail hx)
      · exact hz

theorem Zip.Bounded.move {W : Nat} {z : Zip} (hz : z.Bounded W) (m : TMMove) :
    (z.move m).Bounded W := by
  obtain ⟨hl, hr⟩ := hz
  cases m with
  | Nmove => exact ⟨hl, hr⟩
  | Rmove =>
      rcases hrg : z.rgt with _ | ⟨a, r⟩
      · simp only [Zip.move, hrg]; exact ⟨hl, fun _ h => by cases h⟩
      · simp only [Zip.move, hrg]
        rw [hrg] at hr
        exact ⟨fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hr x (by simp)
          · exact hl x hx, fun x hx => hr x (by simp [hx])⟩
  | Lmove =>
      by_cases he : z.exc = 0
      · rcases hlf : z.lft with _ | ⟨a, l⟩
        · simp only [Zip.move, he, hlf, if_true]; exact ⟨hl, hr⟩
        · simp only [Zip.move, he, hlf, if_true]
          rw [hlf] at hl
          exact ⟨fun x hx => hl x (by simp [hx]), fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hl x (by simp)
            · exact hr x hx⟩
      · simp only [Zip.move, if_neg he]; exact ⟨hl, hr⟩

theorem zip_bounded {W h : Nat} {right : List Nat} (hr : ∀ v ∈ right, v < W) :
    (zip h right).Bounded W :=
  ⟨fun v hv => Nat.le_of_lt (hr v (List.mem_of_mem_take (List.mem_reverse.mp hv))),
   fun v hv => Nat.le_of_lt (hr v (List.mem_of_mem_drop hv))⟩

/-- The cells after a step are old cells or the written symbol. -/
theorem mem_tapeStep (left : List Nat) (h : Nat) (right : List Nat) (w : Option Nat)
    (m : TMMove) (x : Nat) (hx : x ∈ (tapeStep (left, h, right) w m).2.2) :
    x ∈ right ∨ w = some x := by
  have hmv : ∀ t : List Nat × Nat × List Nat, (moveTapeHead t m).2.2 = t.2.2 := by
    intro t; cases m <;> rfl
  unfold tapeStep at hx
  rw [hmv] at hx
  cases w with
  | none => exact Or.inl hx
  | some v =>
      simp only [writeCurrentTapeSymbol] at hx
      split_ifs at hx
      · rw [List.mem_append, List.mem_cons] at hx
        rcases hx with hx | rfl | hx
        · exact Or.inl (List.mem_of_mem_take hx)
        · exact Or.inr rfl
        · exact Or.inl (List.mem_of_mem_drop hx)
      · rw [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inl hx
        · exact Or.inr rfl
      · exact Or.inl hx

/-! ## Testing one entry -/

/-- The symbol an entry reads, the symbol it writes and its move, on a one-tape machine. -/
def srcSym (e : FlatTMTransEntry) : Option Nat := e.src_tape_vals.headD none
def wrSym (e : FlatTMTransEntry) : Option Nat := e.dst_write_vals.headD none
def mvDir (e : FlatTMTransEntry) : TMMove := e.move_dirs.headD .Nmove

/-- `TT := [1]` iff `ST` holds the entry's state and `SY` its read symbol. -/
def testCode (W : Nat) (e : FlatTMTransEntry) : Cmd :=
  emitConst CK (List.replicate e.src_state 1) ;; .op (.eqBit T1 ST CK) ;;
  emitConst CK (symEnc W (srcSym e)) ;; .op (.eqBit T2 SY CK) ;;
  .ifBit T1 (.op (.copy TT T2)) (.op (.clear TT))

theorem testCode_run (W : Nat) (e : FlatTMTransEntry) (s : State) :
    (State.get ((testCode W e).eval s) TT = [1] ↔
      (State.get s ST = List.replicate e.src_state 1 ∧ State.get s SY = symEnc W (srcSym e)))
    ∧ ∀ r, r ≠ CK → r ≠ T1 → r ≠ T2 → r ≠ TT →
        State.get ((testCode W e).eval s) r = State.get s r := by
  unfold testCode
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
  set s1 := (emitConst CK (List.replicate e.src_state 1)).eval s with hs1
  have h1CK : State.get s1 CK = List.replicate e.src_state 1 :=
    emit_get CK _ s (replicate_one_bits _)
  have h1 : ∀ r, r ≠ CK → State.get s1 r = State.get s r := fun r hr => emit_frame CK _ s r hr
  set s2 := s1.set T1 (if State.get s1 ST = State.get s1 CK then [1] else [0]) with hs2
  set s3 := (emitConst CK (symEnc W (srcSym e))).eval s2 with hs3
  have h3CK : State.get s3 CK = symEnc W (srcSym e) := emit_get CK _ s2 (symEnc_bits W _)
  have h3 : ∀ r, r ≠ CK → State.get s3 r = State.get s2 r := fun r hr => emit_frame CK _ s2 r hr
  set s4 := s3.set T2 (if State.get s3 SY = State.get s3 CK then [1] else [0]) with hs4
  have hT1 : State.get s4 T1 = if State.get s ST = List.replicate e.src_state 1 then [1] else [0] := by
    rw [hs4, State.get_set_ne _ _ _ _ (by decide), h3 _ (by decide), hs2, State.get_set_eq,
      h1 _ (by decide), h1CK]
  have hT2 : State.get s4 T2 = if State.get s SY = symEnc W (srcSym e) then [1] else [0] := by
    rw [hs4, State.get_set_eq, h3 _ (by decide), h3CK, hs2, State.get_set_ne _ _ _ _ (by decide),
      h1 _ (by decide)]
  have hfr : ∀ r, r ≠ CK → r ≠ T1 → r ≠ T2 → State.get s4 r = State.get s r := by
    intro r r1 r2 r3
    rw [hs4, State.get_set_ne _ _ _ _ r3, h3 _ r1, hs2, State.get_set_ne _ _ _ _ r2, h1 _ r1]
  by_cases hq : State.get s ST = List.replicate e.src_state 1
  · have hc : State.get s4 T1 = [1] := by rw [hT1, if_pos hq]
    rw [Cmd.eval_ifBit_true _ _ _ _ hc]
    simp only [Cmd.eval_op, Op.eval]
    refine ⟨?_, ?_⟩
    · rw [State.get_set_eq, hT2]
      by_cases hy : State.get s SY = symEnc W (srcSym e) <;> simp [hy, hq]
    · intro r r1 r2 r3 r4
      rw [State.get_set_ne _ _ _ _ r4, hfr r r1 r2 r3]
  · have hc : State.get s4 T1 ≠ [1] := by rw [hT1, if_neg hq]; simp
    rw [Cmd.eval_ifBit_false _ _ _ _ hc]
    simp only [Cmd.eval_op, Op.eval]
    refine ⟨?_, ?_⟩
    · rw [State.get_set_eq]; simp [hq]
    · intro r r1 r2 r3 r4
      rw [State.get_set_ne _ _ _ _ r4, hfr r r1 r2 r3]

/-! ## Applying one entry -/

def applyCode (M : FlatTM) (W : Nat) (e : FlatTMTransEntry) : Cmd :=
  emitConst ST (List.replicate e.dst_state 1) ;; emitConst HL [haltBit M e.dst_state] ;;
  writeCode W (wrSym e) ;; moveCode W (mvDir e)

theorem haltBit_bits (M : FlatTM) (q : Nat) : ∀ x ∈ [haltBit M q], x ≤ 1 := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx; unfold haltBit; split <;> omega

theorem applyCode_run (M : FlatTM) (W : Nat) (hW : 0 < W) (e : FlatTMTransEntry) (z : Zip)
    (s : State) (hz : ReprZ W z s) (hb : z.Bounded W) (hw : ∀ v, wrSym e = some v → v ≤ W) :
    ReprZ W (((z.write (wrSym e)).move (mvDir e))) ((applyCode M W e).eval s)
    ∧ State.get ((applyCode M W e).eval s) ST = List.replicate e.dst_state 1
    ∧ State.get ((applyCode M W e).eval s) HL = [haltBit M e.dst_state] := by
  unfold applyCode
  simp only [Cmd.eval_seq]
  set s1 := (emitConst ST (List.replicate e.dst_state 1)).eval s with hs1
  set s2 := (emitConst HL [haltBit M e.dst_state]).eval s1 with hs2
  have hz2 : ReprZ W z s2 := by
    obtain ⟨a, b, c⟩ := hz
    refine ⟨?_, ?_, ?_⟩ <;>
      rw [hs2, emit_frame _ _ _ _ (by decide), hs1, emit_frame _ _ _ _ (by decide)] <;>
      assumption
  obtain ⟨w1, w2, w3⟩ := writeCode_run W z (wrSym e) s2 hz2 hb
  obtain ⟨m1, m2, m3⟩ := moveCode_run W hW (z.write (wrSym e)) (mvDir e) _ w1 (hb.write _ hw)
  refine ⟨m1, ?_, ?_⟩
  · rw [m2, w2, hs2, emit_frame _ _ _ _ (by decide), hs1]
    exact emit_get _ _ _ (replicate_one_bits _)
  · rw [m3, w3, hs2]
    exact emit_get _ _ _ (haltBit_bits M _)

/-! ## The representation of a configuration -/

/-- The registers represent a one-tape configuration in state `q` with head `h` on the
written cells `right`. -/
def ReprC (M : FlatTM) (q h : Nat) (right : List Nat) (s : State) : Prop :=
  (∀ v ∈ right, v < wid M) ∧ ReprZ (wid M) (zip h right) s
    ∧ State.get s ST = List.replicate q 1 ∧ State.get s HL = [haltBit M q]

/-- The registers represent the configuration `cfg`. -/
def Repr (M : FlatTM) (cfg : FlatTMConfig) (s : State) : Prop :=
  ∃ left h right, cfg.tapes = [(left, h, right)] ∧ ReprC M cfg.state_idx h right s

/-- `ReprC` only reads `LT`, `RT`, `EX`, `ST`, `HL`. -/
theorem ReprC.frame {M : FlatTM} {q h : Nat} {right : List Nat} {s s' : State}
    (hR : ReprC M q h right s)
    (hfr : ∀ r, r = LT ∨ r = RT ∨ r = EX ∨ r = ST ∨ r = HL → State.get s' r = State.get s r) :
    ReprC M q h right s' := by
  obtain ⟨hb, ⟨h1, h2, h3⟩, h4, h5⟩ := hR
  refine ⟨hb, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hfr LT (by simp)]; exact h1
  · rw [hfr RT (by simp)]; exact h2
  · rw [hfr EX (by simp)]; exact h3
  · rw [hfr ST (by simp)]; exact h4
  · rw [hfr HL (by simp)]; exact h5

/-- What the first matching entry does, or nothing. -/
def chainRes (cfg : FlatTMConfig) (es : List FlatTMTransEntry) : FlatTMConfig :=
  match es.find? (fun e => entryMatchesConfig e cfg) with
  | none => cfg
  | some e => (applyTransitionEntry cfg e).getD cfg

/-- Test the entries in order; apply the first that matches. -/
def chainCode (M : FlatTM) (W : Nat) : List FlatTMTransEntry → Cmd
  | [] => nop
  | e :: es => testCode W e ;; .ifBit TT (applyCode M W e) (chainCode M W es)

/-- A valid entry of a one-tape machine has one read symbol, one write and one move. -/
theorem entry_shape {M : FlatTM} (h1 : M.tapes = 1) {e : FlatTMTransEntry}
    (he : flatTMTransEntryValid M e) :
    e.src_tape_vals = [srcSym e] ∧ e.dst_write_vals = [wrSym e] ∧ e.move_dirs = [mvDir e] := by
  obtain ⟨-, -, hs, hw, hm, -, -⟩ := he
  rw [h1] at hs hw hm
  refine ⟨?_, ?_, ?_⟩
  · match h : e.src_tape_vals, hs with
    | [a], _ => simp [srcSym, h]
  · match h : e.dst_write_vals, hw with
    | [a], _ => simp [wrSym, h]
  · match h : e.move_dirs, hm with
    | [a], _ => simp [mvDir, h]

theorem srcSym_bound {M : FlatTM} {e : FlatTMTransEntry} (h1 : M.tapes = 1)
    (he : flatTMTransEntryValid M e) : ∀ v, srcSym e = some v → v < M.sig := by
  intro v hv
  have hmem : srcSym e ∈ e.src_tape_vals := by rw [(entry_shape h1 he).1]; simp
  have := he.2.2.2.2.2.1 _ hmem
  rw [hv] at this; exact this

theorem wrSym_bound {M : FlatTM} {e : FlatTMTransEntry} (h1 : M.tapes = 1)
    (he : flatTMTransEntryValid M e) : ∀ v, wrSym e = some v → v < M.sig := by
  intro v hv
  have hmem : wrSym e ∈ e.dst_write_vals := by rw [(entry_shape h1 he).2.1]; simp
  have := he.2.2.2.2.2.2 _ hmem
  rw [hv] at this; exact this

/-- Applying a valid entry on a one-tape configuration. -/
theorem applyTransitionEntry_one {M : FlatTM} (h1 : M.tapes = 1) {e : FlatTMTransEntry}
    (he : flatTMTransEntryValid M e) (cfg : FlatTMConfig) (left : List Nat) (h : Nat)
    (right : List Nat) (ht : cfg.tapes = [(left, h, right)]) :
    applyTransitionEntry cfg e
      = some ⟨e.dst_state, [tapeStep (left, h, right) (wrSym e) (mvDir e)]⟩ := by
  obtain ⟨-, hw, hm⟩ := entry_shape h1 he
  unfold applyTransitionEntry
  rw [dif_pos (by rw [ht, hw, hm]; simp)]
  simp [ht, hw, hm]

theorem entryMatches_one {M : FlatTM} (h1 : M.tapes = 1) {e : FlatTMTransEntry}
    (he : flatTMTransEntryValid M e) (cfg : FlatTMConfig) (left : List Nat) (h : Nat)
    (right : List Nat) (ht : cfg.tapes = [(left, h, right)]) :
    entryMatchesConfig e cfg = true
      ↔ (e.src_state = cfg.state_idx ∧ srcSym e = (zip h right).rgt.head?) := by
  obtain ⟨hs, -, -⟩ := entry_shape h1 he
  unfold entryMatchesConfig
  rw [ht, hs]
  simp [currentTapeSymbol_eq]

theorem replicate_one_inj {a b : Nat} (h : List.replicate a 1 = List.replicate b 1) : a = b := by
  have := congrArg List.length h
  simpa using this

/-- **The first-match chain.** -/
theorem chain_run (M : FlatTM) (h1 : M.tapes = 1) (cfg : FlatTMConfig) (left : List Nat)
    (h : Nat) (right : List Nat) (ht : cfg.tapes = [(left, h, right)]) :
    ∀ (es : List FlatTMTransEntry) (s : State), (∀ e ∈ es, flatTMTransEntryValid M e) →
      ReprC M cfg.state_idx h right s →
      State.get s SY = symEnc (wid M) (zip h right).rgt.head? →
      Repr M (chainRes cfg es) ((chainCode M (wid M) es).eval s) := by
  have hW : 0 < wid M := by unfold wid; omega
  intro es
  induction es with
  | nil =>
      intro s _ hR _
      refine ⟨left, h, right, ht, hR.frame fun r hr => nop_get s r ?_⟩
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  | cons e es ih =>
      intro s hes hR hSY
      have heV := hes e (by simp)
      obtain ⟨t1, t2⟩ := testCode_run (wid M) e s
      set s1 := (testCode (wid M) e).eval s with hs1
      have hR1 : ReprC M cfg.state_idx h right s1 := hR.frame fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          exact t2 _ (by decide) (by decide) (by decide) (by decide)
      have hSY1 : State.get s1 SY = symEnc (wid M) (zip h right).rgt.head? := by
        rw [t2 _ (by decide) (by decide) (by decide) (by decide), hSY]
      -- the test decides the match
      have hmatch : State.get s1 TT = [1] ↔ entryMatchesConfig e cfg = true := by
        rw [t1, entryMatches_one h1 heV cfg left h right ht, hR.2.2.1, hSY]
        constructor
        · rintro ⟨hq, hy⟩
          refine ⟨(replicate_one_inj hq).symm, ?_⟩
          refine symEnc_inj hW ?_ ?_ hy.symm
          · intro v hv
            have := srcSym_bound h1 heV v hv
            unfold wid; omega
          · intro v hv
            rw [List.head?_eq_some_iff] at hv
            obtain ⟨t, ht'⟩ := hv
            exact (zip_bounded hR.1).2 v (by rw [ht']; simp)
        · rintro ⟨hq, hy⟩
          exact ⟨by rw [hq], by rw [hy]⟩
      show Repr M (chainRes cfg (e :: es))
        ((Cmd.ifBit TT (applyCode M (wid M) e) (chainCode M (wid M) es)).eval s1)
      by_cases hT : State.get s1 TT = [1]
      · rw [Cmd.eval_ifBit_true _ _ _ _ hT]
        have hm := hmatch.mp hT
        have hres : chainRes cfg (e :: es)
            = ⟨e.dst_state, [tapeStep (left, h, right) (wrSym e) (mvDir e)]⟩ := by
          unfold chainRes
          simp only [List.find?_cons, hm]
          rw [applyTransitionEntry_one h1 heV cfg left h right ht]
          rfl
        rw [hres]
        obtain ⟨a1, a2, a3⟩ := applyCode_run M (wid M) hW e (zip h right) s1 hR1.2.1
          (zip_bounded hR.1) (fun v hv => by
            have := wrSym_bound h1 heV v hv; unfold wid; omega)
        refine ⟨(tapeStep (left, h, right) (wrSym e) (mvDir e)).1,
          (tapeStep (left, h, right) (wrSym e) (mvDir e)).2.1,
          (tapeStep (left, h, right) (wrSym e) (mvDir e)).2.2, rfl, ?_⟩
        · refine ⟨?_, ?_, a2, a3⟩
          · intro x hx
            rcases mem_tapeStep left h right _ _ x hx with hx | hx
            · exact hR.1 x hx
            · have := wrSym_bound h1 heV x hx; unfold wid; omega
          · rw [zip_tapeStep]; exact a1
      · rw [Cmd.eval_ifBit_false _ _ _ _ hT]
        have hm : entryMatchesConfig e cfg = false := by
          cases hc : entryMatchesConfig e cfg
          · rfl
          · exact absurd (hmatch.mpr hc) hT
        have hres : chainRes cfg (e :: es) = chainRes cfg es := by
          unfold chainRes
          simp only [List.find?_cons, hm]
        rw [hres]
        exact ih s1 (fun e' he' => hes e' (by simp [he'])) hR1 hSY1

/-! ## One step -/

/-- One step of `M`: read the head block, then the first-match chain. -/
def stepCode (M : FlatTM) : Cmd :=
  takeTo (wid M) SY RT ;; chainCode M (wid M) M.trans

/-- One step unless halted. -/
def guardedStep (M : FlatTM) : Cmd := .ifBit HL nop (stepCode M)

theorem chainRes_trans (M : FlatTM) (cfg : FlatTMConfig)
    (hh : haltingStateReached M cfg = false) : stepCfg M cfg = chainRes cfg M.trans := by
  unfold stepCfg chainRes stepFlatTM
  rw [if_neg (by simp [hh])]
  cases M.trans.find? (fun e => entryMatchesConfig e cfg) <;> rfl

theorem haltBit_eq_one (M : FlatTM) (cfg : FlatTMConfig) :
    [haltBit M cfg.state_idx] = [1] ↔ haltingStateReached M cfg = true := by
  unfold haltBit haltingStateReached
  split <;> simp_all

/-- **The step lemma.** -/
theorem guardedStep_run (M : FlatTM) (hM : validFlatTM M) (h1 : M.tapes = 1)
    (cfg : FlatTMConfig) (s : State) (hR : Repr M cfg s) :
    Repr M (stepCfg M cfg) ((guardedStep M).eval s) := by
  obtain ⟨left, h, right, ht, hRC⟩ := hR
  by_cases hh : haltingStateReached M cfg = true
  · have hHL : State.get s HL = [1] := by rw [hRC.2.2.2]; exact (haltBit_eq_one M cfg).mpr hh
    unfold guardedStep
    rw [Cmd.eval_ifBit_true _ _ _ _ hHL]
    have hfix : stepCfg M cfg = cfg := by simp [stepCfg, hh]
    rw [hfix]
    refine ⟨left, h, right, ht, hRC.frame fun r hr => nop_get s r ?_⟩
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · have hHL : State.get s HL ≠ [1] := by
      rw [hRC.2.2.2]; exact fun hc => hh ((haltBit_eq_one M cfg).mp hc)
    unfold guardedStep stepCode
    rw [Cmd.eval_ifBit_false _ _ _ _ hHL, Cmd.eval_seq,
      chainRes_trans M cfg (by simpa using hh)]
    obtain ⟨k1, k2⟩ := takeTo_run (wid M) SY RT s (by decide) (by decide) (by decide) (by decide)
    refine chain_run M h1 cfg left h right ht M.trans _ hM.2.2
      (hRC.frame fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          exact k2 _ (by decide) (by decide) (by decide) (by decide)) ?_
    rw [k1, hRC.2.1.2.1, take_blocks _ _ (zip_bounded hRC.1).2]

end CookLevin.Sim
