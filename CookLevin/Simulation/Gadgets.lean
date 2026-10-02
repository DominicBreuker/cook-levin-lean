import CookLevin.Reductions.FrontPieces
import CookLevin.Simulation.Zipper

set_option autoImplicit false

/-! # Registers, blocks and gadgets of the machine simulation

The simulation of a single-tape machine by a register program (`Simulation/Step.lean`,
`Simulation/Program.lean`) stores tape cells as fixed-width *blocks*: the symbol `v` is
`1^v 0^(W-v)` for a width `W` larger than every symbol on the tape. A list of cells is the
concatenation of their blocks (`blocks`). Taking or dropping one block is then `W`
single-cell operations, a loop-free fragment (`takeTo`, `dropRep`).
-/

namespace CookLevin.Sim

open CookLevin.Lang FrontPieces

/-! ## Registers

Registers below `KB` are the registers of the step: the zipper (`LT`, `RT`, `EX`), the state
(`ST`), the halting flag (`HL`) and scratch. Registers `XO` and `CI` hold the input `x` and
the certificate `c`; `XO` receives the verdict. The registers from `KB` on are used outside
the step. -/

def XO : Var := 0
def CI : Var := 1
def LT : Var := 2
def RT : Var := 3
def EX : Var := 4
def ST : Var := 5
def HL : Var := 6
def SY : Var := 7
def CK : Var := 8
def T1 : Var := 9
def T2 : Var := 10
def TT : Var := 11
def TM : Var := 12
def HB : Var := 13
def FL : Var := 14
def BK : Var := 15
def JK : Var := 16
def KB : Nat := 17

/-- The command that does nothing visible: it clears the junk register `JK`. -/
def nop : Cmd := .op (.clear JK)

theorem nop_get (s : State) (r : Var) (hr : r ≠ JK) : State.get (nop.eval s) r = State.get s r :=
  State.get_set_ne _ _ _ _ hr

/-! ## Blocks -/

/-- The block of the symbol `v`: `1^v 0^(W-v)`. -/
def blk (W v : Nat) : List Nat := List.replicate v 1 ++ List.replicate (W - v) 0

/-- The blocks of a list of cells, concatenated. -/
def blocks (W : Nat) (l : List Nat) : List Nat := l.flatMap (blk W)

/-- The block of a read symbol; the blank (`none`) is the empty list. -/
def symEnc (W : Nat) : Option Nat → List Nat
  | none => []
  | some v => blk W v

@[simp] theorem blocks_nil (W : Nat) : blocks W [] = [] := rfl

theorem blocks_cons (W a : Nat) (l : List Nat) : blocks W (a :: l) = blk W a ++ blocks W l := by
  simp [blocks, List.flatMap_cons]

theorem blk_length {W v : Nat} (h : v ≤ W) : (blk W v).length = W := by
  simp [blk]; omega

theorem blk_bits (W v : Nat) : ∀ x ∈ blk W v, x ≤ 1 := by
  intro x hx
  simp only [blk, List.mem_append, List.mem_replicate] at hx
  omega

theorem blocks_bits (W : Nat) (l : List Nat) : ∀ x ∈ blocks W l, x ≤ 1 := by
  intro x hx
  simp only [blocks, List.mem_flatMap] at hx
  obtain ⟨a, _, ha⟩ := hx
  exact blk_bits W a x ha

theorem symEnc_bits (W : Nat) (o : Option Nat) : ∀ x ∈ symEnc W o, x ≤ 1 := by
  cases o with
  | none => intro x hx; cases hx
  | some v => exact blk_bits W v

theorem blocks_length (W : Nat) (l : List Nat) (h : ∀ v ∈ l, v ≤ W) :
    (blocks W l).length = W * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [blocks_cons, List.length_append, blk_length (h a (by simp)),
        ih (fun v hv => h v (by simp [hv])), List.length_cons]
      ring

theorem take_blocks (W : Nat) (l : List Nat) (h : ∀ v ∈ l, v ≤ W) :
    (blocks W l).take W = symEnc W l.head? := by
  cases l with
  | nil => simp [symEnc]
  | cons a t =>
      rw [blocks_cons, List.take_append_of_le_length (by rw [blk_length (h a (by simp))]),
        List.take_of_length_le (by rw [blk_length (h a (by simp))])]
      rfl

theorem drop_blocks (W : Nat) (l : List Nat) (h : ∀ v ∈ l, v ≤ W) :
    (blocks W l).drop W = blocks W l.tail := by
  cases l with
  | nil => simp
  | cons a t =>
      rw [blocks_cons, List.drop_append_of_le_length (by rw [blk_length (h a (by simp))]),
        List.drop_of_length_le (by rw [blk_length (h a (by simp))])]
      rfl

theorem blk_count (W v : Nat) : (blk W v).count 1 = v := by
  simp [blk, List.count_replicate]

theorem blk_inj {W u v : Nat} (h : blk W u = blk W v) : u = v := by
  have := congrArg (List.count 1) h
  rwa [blk_count, blk_count] at this

theorem blk_ne_nil {W v : Nat} (hW : 0 < W) (hv : v ≤ W) : blk W v ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [blk_length hv] at this
  simp at this; omega

theorem symEnc_inj {W : Nat} (hW : 0 < W) {o o' : Option Nat}
    (ho : ∀ v, o = some v → v ≤ W) (ho' : ∀ v, o' = some v → v ≤ W)
    (h : symEnc W o = symEnc W o') : o = o' := by
  cases o with
  | none =>
      cases o' with
      | none => rfl
      | some v' => exact absurd h.symm (blk_ne_nil hW (ho' v' rfl))
  | some v =>
      cases o' with
      | none => exact absurd h (blk_ne_nil hW (ho v rfl))
      | some v' => rw [blk_inj h]

/-! ## Taking and dropping cells -/

/-- Move the first `k` cells of `TM` to the end of `dst`, one cell at a time through `HB`. -/
def takeRep : Nat → Var → Cmd
  | 0, _ => nop
  | k + 1, dst =>
      takeRep k dst ;; .op (.head HB TM) ;; .op (.concat dst dst HB) ;; .op (.tail TM TM)

theorem op_head_eval (d src : Var) (s : State) :
    Op.eval (.head d src) s = s.set d ((State.get s src).take 1) := by
  show s.set d (match State.get s src with | [] => [] | x :: _ => [x]) = _
  cases State.get s src <;> rfl

theorem takeRep_run (dst : Var) (hd1 : dst ≠ TM) (hd2 : dst ≠ HB) (hd3 : dst ≠ JK) :
    ∀ (k : Nat) (s : State),
      State.get ((takeRep k dst).eval s) dst = State.get s dst ++ (State.get s TM).take k
      ∧ State.get ((takeRep k dst).eval s) TM = (State.get s TM).drop k
      ∧ ∀ r, r ≠ dst → r ≠ TM → r ≠ HB → r ≠ JK →
          State.get ((takeRep k dst).eval s) r = State.get s r := by
  intro k
  induction k with
  | zero =>
      intro s
      refine ⟨?_, ?_, fun r _ _ _ h4 => nop_get s r h4⟩
      · rw [List.take_zero, List.append_nil]; exact nop_get s dst hd3
      · rw [List.drop_zero]; exact nop_get s TM (by decide)
  | succ k ih =>
      intro s
      obtain ⟨h1, h2, h3⟩ := ih s
      set s1 := (takeRep k dst).eval s with hs1
      have hTH : TM ≠ HB := by decide
      have he : (takeRep (k + 1) dst).eval s = (Cmd.op (.tail TM TM)).eval
          ((Cmd.op (.concat dst dst HB)).eval ((Cmd.op (.head HB TM)).eval s1)) := rfl
      rw [he]
      simp only [Cmd.eval_op, Op.eval]
      refine ⟨?_, ?_, ?_⟩
      · rw [State.get_set_ne _ _ _ _ hd1, State.get_set_eq, State.get_set_ne _ _ _ _ hd2,
          State.get_set_eq, h1, h2, List.take_add_one, List.append_assoc]
        congr 2
        rw [← List.head?_drop]
        cases List.drop k (State.get s TM) <;> rfl
      · rw [State.get_set_eq, State.get_set_ne _ _ _ _ (Ne.symm hd1),
          State.get_set_ne _ _ _ _ hTH, h2, List.tail_drop]
      · intro r r1 r2 r3 r4
        rw [State.get_set_ne _ _ _ _ r2, State.get_set_ne _ _ _ _ r1,
          State.get_set_ne _ _ _ _ r3, h3 r r1 r2 r3 r4]

/-- `dst := take k src`, through `TM` and `HB`. -/
def takeTo (k : Nat) (dst src : Var) : Cmd :=
  .op (.clear dst) ;; .op (.copy TM src) ;; takeRep k dst

theorem takeTo_run (k : Nat) (dst src : Var) (s : State)
    (hd1 : dst ≠ TM) (hd2 : dst ≠ HB) (hd3 : dst ≠ JK) (hds : src ≠ dst) :
    State.get ((takeTo k dst src).eval s) dst = (State.get s src).take k
    ∧ ∀ r, r ≠ dst → r ≠ TM → r ≠ HB → r ≠ JK →
        State.get ((takeTo k dst src).eval s) r = State.get s r := by
  unfold takeTo
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
  obtain ⟨h1, -, h3⟩ := takeRep_run dst hd1 hd2 hd3 k ((s.set dst []).set TM (State.get (s.set dst []) src))
  refine ⟨?_, ?_⟩
  · rw [h1, State.get_set_ne _ _ _ _ hd1, State.get_set_eq, List.nil_append, State.get_set_eq,
      State.get_set_ne _ _ _ _ hds]
  · intro r r1 r2 r3 r4
    rw [h3 r r1 r2 r3 r4, State.get_set_ne _ _ _ _ r2, State.get_set_ne _ _ _ _ r1]

/-- Drop the first `k` cells of `r`. -/
def dropRep : Nat → Var → Cmd
  | 0, _ => nop
  | k + 1, r => dropRep k r ;; .op (.tail r r)

theorem dropRep_run (reg : Var) (hr : reg ≠ JK) :
    ∀ (k : Nat) (s : State),
      State.get ((dropRep k reg).eval s) reg = (State.get s reg).drop k
      ∧ ∀ r, r ≠ reg → r ≠ JK → State.get ((dropRep k reg).eval s) r = State.get s r := by
  intro k
  induction k with
  | zero => intro s; exact ⟨by rw [List.drop_zero]; exact nop_get s reg hr,
      fun r _ h => nop_get s r h⟩
  | succ k ih =>
      intro s
      obtain ⟨h1, h2⟩ := ih s
      have he : (dropRep (k + 1) reg).eval s
          = (Cmd.op (.tail reg reg)).eval ((dropRep k reg).eval s) := rfl
      rw [he]
      simp only [Cmd.eval_op, Op.eval]
      refine ⟨?_, ?_⟩
      · rw [State.get_set_eq, h1, List.tail_drop]
      · intro r r1 r2
        rw [State.get_set_ne _ _ _ _ r1, h2 r r1 r2]

/-- `emitConst` on a constant of bits writes exactly that constant. -/
theorem emit_get (dst : Var) (bits : List Nat) (s : State) (hb : ∀ x ∈ bits, x ≤ 1) :
    State.get ((emitConst dst bits).eval s) dst = bits :=
  emitConst_run_bits dst bits s hb

theorem emit_frame (dst : Var) (bits : List Nat) (s : State) (r : Var) (hr : r ≠ dst) :
    State.get ((emitConst dst bits).eval s) r = State.get s r :=
  (emitConst_run dst bits s).2.1 r hr

theorem replicate_one_bits (n : Nat) : ∀ x ∈ List.replicate n 1, x ≤ 1 := by
  intro x hx; rw [List.mem_replicate] at hx; omega

end CookLevin.Sim
