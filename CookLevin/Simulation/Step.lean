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

end CookLevin.Sim
