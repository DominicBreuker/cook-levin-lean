import CookLevin.Lang.SerializeStr

set_option autoImplicit false

/-! # From programs to Turing machines

The reductions and verifiers of this development are written as programs of the register
language (`Lang/Syntax.lean`) and compiled to Turing machines (`Lang/Compile.lean`). This
file states what the compiled machines do in the vocabulary of `Basic/StringTM.lean`:

* `PolyTimeComputableLang.toMachine` — a program computing `f : List Bool → List Bool` from
  the canonical one-register input layout, reading its output from register `0`, yields a
  single-tape Turing machine computing `f` in polynomial time (`computesInTime`);
* `DecidesLang.toMachine` — a program deciding a relation on pairs of strings from the
  canonical two-register layout yields a single-tape Turing machine deciding it in
  polynomial time (`decidesPairInTime`).

The compiled machine expects its input in the compiler's tape format `Compile.encodeTape`;
`stringTape_eq` and `pairTape_eq` show that this format, on the canonical layouts, is the
one fixed in `Basic/StringTM.lean`, and `outputString_eq` shows that reading the output
tape there agrees with the compiler's own decoder. -/

namespace CookLevin.Lang

open CookLevin

/-! ## The tape conventions agree with the compiler's -/

theorem symbolsOf_eq (x : List Bool) : symbolsOf x = Compile.shiftReg (strBits x) := by
  unfold symbolsOf Compile.shiftReg strBits
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  cases b <;> rfl

theorem stringTape_eq (x : List Bool) : stringTape x = Compile.encodeTape (certState x) := by
  show 3 :: (symbolsOf x ++ [0, 3])
    = Compile.endMark :: (Compile.encodeRegs [strBits x] ++ [Compile.endMark])
  rw [Compile.encodeRegs_cons, Compile.encodeRegs_nil, symbolsOf_eq]
  simp [Compile.endMark]

theorem pairTape_eq (x c : List Bool) :
    pairTape x c = Compile.encodeTape (certState x ++ certState c) := by
  show 3 :: (symbolsOf x ++ [0] ++ symbolsOf c ++ [0, 3])
    = Compile.endMark :: (Compile.encodeRegs [strBits x, strBits c] ++ [Compile.endMark])
  rw [Compile.encodeRegs_cons, Compile.encodeRegs_cons, Compile.encodeRegs_nil,
    symbolsOf_eq, symbolsOf_eq]
  simp [Compile.endMark]

private theorem splitOnZero_head :
    ∀ l : List Nat, ∃ rest, Compile.splitOnZero l = l.takeWhile (· != 0) :: rest
  | [] => ⟨[], rfl⟩
  | 0 :: xs => ⟨Compile.splitOnZero xs, by simp [Compile.splitOnZero]⟩
  | (x + 1) :: xs => by
      obtain ⟨rest, h⟩ := splitOnZero_head xs
      refine ⟨rest, ?_⟩
      simp [Compile.splitOnZero, h]

private theorem get_zero_dropTrailingEmpty (g : List Nat) (rest : List (List Nat)) :
    State.get ((Compile.dropTrailingEmpty (g :: rest)).map Compile.unshiftReg) 0
      = Compile.unshiftReg g := by
  cases g with
  | nil =>
      cases rest with
      | nil => rfl
      | cons r rs => rfl
  | cons a g' => rfl

private theorem decide_sub_one_eq (v : Nat) : decide (v - 1 = 1) = (v == 2) := by
  rcases v with _ | _ | _ | v <;> simp

theorem outputString_eq (cfg : FlatTMConfig) :
    outputString cfg = boolsOf (State.get (Compile.decodeTape cfg) 0) := by
  obtain ⟨q, tapes⟩ := cfg
  cases tapes with
  | nil => rfl
  | cons t ts =>
      obtain ⟨l, h, r⟩ := t
      show ((r.tail.takeWhile (· != 3)).takeWhile (· != 0)).map (· == 2)
        = boolsOf (State.get ((Compile.dropTrailingEmpty (Compile.splitOnZero
            ((Compile.flattenTape (l, h, r)).tail.takeWhile (· != Compile.endMark)))).map
              Compile.unshiftReg) 0)
      obtain ⟨rest, hs⟩ := splitOnZero_head
        ((Compile.flattenTape (l, h, r)).tail.takeWhile (· != Compile.endMark))
      rw [hs, get_zero_dropTrailingEmpty]
      show _ = List.map (fun v => decide (v = 1))
        (List.map (fun n => n - 1) ((r.tail.takeWhile (· != 3)).takeWhile (· != 0)))
      rw [List.map_map]
      apply List.map_congr_left
      intro v _
      exact (decide_sub_one_eq v).symm

/-! ## Reductions: a program computing `f` yields a machine computing `f` -/

/-- The time budget of the compiled machine, as a function of the input size. -/
private def PolyTimeComputableLang.padTimeBound {X Y : Type} [encodable X] [encodable Y]
    {f : X → Y} (W : PolyTimeComputableLang f) (n : Nat) : Nat :=
  (W.regBound + 2 * W.c.loopDepth + 2 + 1)
      * (2 * W.encBound n + 4 * (W.regBound + 2 * W.c.loopDepth + 2) + 14) + 1
    + Compile.physStepBudget
        (W.encBound n + 2 * (W.regBound + 2 * W.c.loopDepth + 2) + W.cost_bound n + 2)
        (W.cost_bound n)

private theorem PolyTimeComputableLang.budget_ge {X Y : Type} [encodable X] [encodable Y]
    {f : X → Y} (W : PolyTimeComputableLang f) (x : X) :
    Compile.padBudget (W.regBound + 2 * W.c.loopDepth + 2) (W.encodeIn x) + 1
        + Compile.physStepBudget (State.size (W.encodeIn x)
              + ((W.encodeIn x).length + (W.regBound + 2 * W.c.loopDepth + 2))
              + W.c.cost (W.encodeIn x) + 2) (W.c.cost (W.encodeIn x))
      ≤ W.padTimeBound (encodable.size x) := by
  have hsz : State.size (W.encodeIn x) ≤ W.encBound (encodable.size x) := W.encodeIn_size x
  have hw : (W.encodeIn x).length ≤ W.regBound := W.width_le x
  have hc : W.c.cost (W.encodeIn x) ≤ W.cost_bound (encodable.size x) := W.cost_le x
  unfold PolyTimeComputableLang.padTimeBound
  have hpb := Compile.padBudget_le (W.regBound + 2 * W.c.loopDepth + 2) (W.encodeIn x)
  have hpad : Compile.padBudget (W.regBound + 2 * W.c.loopDepth + 2) (W.encodeIn x)
      ≤ (W.regBound + 2 * W.c.loopDepth + 2 + 1)
          * (2 * W.encBound (encodable.size x) + 4 * (W.regBound + 2 * W.c.loopDepth + 2) + 14) :=
    le_trans hpb (Nat.mul_le_mul (Nat.le_succ _) (by omega))
  have hps : Compile.physStepBudget (State.size (W.encodeIn x)
            + ((W.encodeIn x).length + (W.regBound + 2 * W.c.loopDepth + 2))
            + W.c.cost (W.encodeIn x) + 2) (W.c.cost (W.encodeIn x))
      ≤ Compile.physStepBudget (W.encBound (encodable.size x)
          + 2 * (W.regBound + 2 * W.c.loopDepth + 2)
          + W.cost_bound (encodable.size x) + 2) (W.cost_bound (encodable.size x)) :=
    Compile.physStepBudget_mono (by omega) hc
  exact Nat.add_le_add (Nat.add_le_add hpad (Nat.le_refl 1)) hps

private theorem PolyTimeComputableLang.padTimeBound_poly {X Y : Type} [encodable X]
    [encodable Y] {f : X → Y} (W : PolyTimeComputableLang f) : inOPoly W.padTimeBound := by
  set RB : Nat := W.regBound + 2 * W.c.loopDepth + 2 with hRB
  unfold PolyTimeComputableLang.padTimeBound
  have hlin : inOPoly (fun n => (RB + 1) * (2 * W.encBound n + 4 * RB + 14)) :=
    inOPoly_mul (inOPoly_const _)
      (inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 2) W.encBound_poly)
        (inOPoly_const _)) (inOPoly_const 14))
  have hinner : inOPoly (fun n => W.encBound n + 2 * RB + W.cost_bound n + 2) :=
    inOPoly_add (inOPoly_add (inOPoly_add W.encBound_poly
      (inOPoly_const _)) W.cost_bound_poly) (inOPoly_const 2)
  have hcomp : inOPoly ((fun m => Compile.physStepBudget m m)
      ∘ (fun n => W.encBound n + 2 * RB + W.cost_bound n + 2)) :=
    inOPoly_comp hinner Compile.physStepBudget_poly
  have hphys : inOPoly (fun n =>
      Compile.physStepBudget (W.encBound n + 2 * RB + W.cost_bound n + 2) (W.cost_bound n)) := by
    refine inOPoly_of_le ?_ hcomp
    intro n
    show Compile.physStepBudget (W.encBound n + 2 * RB + W.cost_bound n + 2) (W.cost_bound n)
        ≤ Compile.physStepBudget (W.encBound n + 2 * RB + W.cost_bound n + 2)
            (W.encBound n + 2 * RB + W.cost_bound n + 2)
    exact Compile.physStepBudget_mono (Nat.le_refl _) (by omega)
  exact inOPoly_add (inOPoly_add hlin (inOPoly_const 1)) hphys

private theorem PolyTimeComputableLang.padTimeBound_mono {X Y : Type} [encodable X]
    [encodable Y] {f : X → Y} (W : PolyTimeComputableLang f) : monotonic W.padTimeBound := by
  intro a b hab
  have hd : W.cost_bound a ≤ W.cost_bound b := W.cost_bound_mono a b hab
  have he : W.encBound a ≤ W.encBound b := W.encBound_mono a b hab
  unfold PolyTimeComputableLang.padTimeBound
  have h1 : (W.regBound + 2 * W.c.loopDepth + 2 + 1)
        * (2 * W.encBound a + 4 * (W.regBound + 2 * W.c.loopDepth + 2) + 14)
      ≤ (W.regBound + 2 * W.c.loopDepth + 2 + 1)
        * (2 * W.encBound b + 4 * (W.regBound + 2 * W.c.loopDepth + 2) + 14) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : Compile.physStepBudget
        (W.encBound a + 2 * (W.regBound + 2 * W.c.loopDepth + 2) + W.cost_bound a + 2)
        (W.cost_bound a)
      ≤ Compile.physStepBudget
        (W.encBound b + 2 * (W.regBound + 2 * W.c.loopDepth + 2) + W.cost_bound b + 2)
        (W.cost_bound b) :=
    Compile.physStepBudget_mono (by omega) hd
  exact Nat.add_le_add (Nat.add_le_add h1 (Nat.le_refl 1)) h2

/-- **A program computing `f` yields a Turing machine computing `f`.** The program must read
its input from the canonical one-register layout `certState` and write its output to
register `0`. The machine is the compiled program, preceded by a register-padding phase. -/
theorem PolyTimeComputableLang.toMachine {f : List Bool → List Bool}
    (W : PolyTimeComputableLang f)
    (hin : ∀ x, W.encodeIn x = certState x)
    (hout : ∀ s, Compile.BitState s → W.decodeOut s = boolsOf (State.get s 0)) :
    ∃ (t : Nat → Nat) (M : FlatTM),
      inOPoly t ∧ validFlatTM M ∧ M.tapes = 1 ∧ computesInTime M f t := by
  refine ⟨fun n => W.padTimeBound (2 * n), Compile.paddedComputeTM W.c W.regBound, ?_,
    Compile.paddedComputeTM_valid _ _, Compile.paddedComputeTM_tapes _ _, ?_⟩
  · show inOPoly (W.padTimeBound ∘ fun n => 2 * n)
    exact inOPoly_comp (inOPoly_mul (inOPoly_const 2) inOPoly_id) W.padTimeBound_poly
  · intro x
    set RB : Nat := W.regBound + 2 * W.c.loopDepth + 2 with hRB
    have hbit_in : Compile.BitState (W.encodeIn x) := W.enc_bit x
    obtain ⟨res, _hres, hrun, hhalt⟩ :=
      Compile.paddedCompute_run W.c (W.encodeIn x) W.regBound hbit_in (W.width_le x)
        W.usesBelow
    set wide : State := W.encodeIn x ++ List.replicate RB [] with hwide
    have hbit_w : Compile.BitState wide := by
      rw [hwide]; exact Compile.BitState_append_replicate_nil (W.encodeIn x) RB hbit_in
    have hk_w : W.regBound ≤ wide.length := by
      rw [hwide, List.length_append, List.length_replicate]; omega
    have hbit_out : Compile.BitState (W.c.eval wide) :=
      Cmd.eval_preserves_BitState W.c W.regBound wide W.usesBelow hk_w hbit_w
    refine ⟨{ state_idx := Compile.exit W.regBound W.c + (Compile.padRegsTM RB).states,
              tapes := [([], 0, Compile.encodeTape (W.c.eval wide) ++ res)] }, ?_, hhalt, ?_⟩
    · show runFlatTM (W.padTimeBound (2 * x.length)) (Compile.paddedComputeTM W.c W.regBound)
          (initFlatConfig (Compile.paddedComputeTM W.c W.regBound) [stringTape x]) = some _
      rw [stringTape_eq, ← hin x]
      have hle : W.padTimeBound (encodable.size x) ≤ W.padTimeBound (2 * x.length) :=
        W.padTimeBound_mono _ _ (size_le_two_mul_length x)
      obtain ⟨k, hk⟩ := Nat.le.dest (le_trans (W.budget_ge x) hle)
      rw [← hk]
      exact runFlatTM_extend hrun hhalt
    · rw [outputString_eq, Compile.decodeTape_encodeTape_append _ _ _ _ hbit_out]
      have h1 : W.decodeOut (W.c.eval wide) = f x := by
        rw [hwide, W.decode_agree x RB]; exact W.computes x
      rw [← h1, hout _ hbit_out]

/-! ## Verifiers: a program deciding `R` yields a machine deciding `R` -/

private def DecidesLang.padTimeBound {X : Type} [encodable X]
    {P : X → Prop} {costBound : Nat → Nat} (D : DecidesLang P costBound) (n : Nat) : Nat :=
  (D.regBound + 2 * D.c.loopDepth + 2 + 1)
      * (2 * costBound n + 4 * (D.regBound + 2 * D.c.loopDepth + 2) + 12) + 1
    + (Compile.physStepBudget
        (2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2) (costBound n) + 3)

private theorem DecidesLang.budget_ge {X : Type} [encodable X]
    {P : X → Prop} {costBound : Nat → Nat} (D : DecidesLang P costBound) (x : X) :
    Compile.padBudget (D.regBound + 2 * D.c.loopDepth + 2) (D.encodeIn x) + 1
        + (Compile.physStepBudget (State.size (D.encodeIn x)
              + ((D.encodeIn x).length + (D.regBound + 2 * D.c.loopDepth + 2))
              + D.c.cost (D.encodeIn x) + 2)
            (D.c.cost (D.encodeIn x)) + 3)
      ≤ D.padTimeBound (encodable.size x) := by
  have h1 : State.size (D.encodeIn x) ≤ costBound (encodable.size x) := D.encodeIn_size x
  have hw : (D.encodeIn x).length ≤ D.regBound := D.width_le x
  have h2 : D.c.cost (D.encodeIn x) ≤ costBound (encodable.size x) := D.cost_bound x
  unfold DecidesLang.padTimeBound
  have hpb := Compile.padBudget_le (D.regBound + 2 * D.c.loopDepth + 2) (D.encodeIn x)
  have hpad : Compile.padBudget (D.regBound + 2 * D.c.loopDepth + 2) (D.encodeIn x)
      ≤ (D.regBound + 2 * D.c.loopDepth + 2 + 1)
          * (2 * costBound (encodable.size x) + 4 * (D.regBound + 2 * D.c.loopDepth + 2) + 12) :=
    le_trans hpb (Nat.mul_le_mul (Nat.le_succ _) (by omega))
  have hps : Compile.physStepBudget (State.size (D.encodeIn x)
            + ((D.encodeIn x).length + (D.regBound + 2 * D.c.loopDepth + 2))
            + D.c.cost (D.encodeIn x) + 2)
          (D.c.cost (D.encodeIn x))
      ≤ Compile.physStepBudget (2 * costBound (encodable.size x)
            + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)
          (costBound (encodable.size x)) :=
    Compile.physStepBudget_mono (by omega) h2
  exact Nat.add_le_add (Nat.add_le_add hpad (Nat.le_refl 1)) (Nat.add_le_add hps (Nat.le_refl 3))

private theorem DecidesLang.padTimeBound_poly {X : Type} [encodable X]
    {P : X → Prop} {costBound : Nat → Nat} (D : DecidesLang P costBound)
    (hpoly : inOPoly costBound) : inOPoly D.padTimeBound := by
  unfold DecidesLang.padTimeBound
  have hlin : inOPoly (fun n => (D.regBound + 2 * D.c.loopDepth + 2 + 1)
      * (2 * costBound n + 4 * (D.regBound + 2 * D.c.loopDepth + 2) + 12)) :=
    inOPoly_mul (inOPoly_const _)
      (inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 2) hpoly)
        (inOPoly_const _)) (inOPoly_const 12))
  have hinner : inOPoly (fun n => 2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2) :=
    inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 2) hpoly)
      (inOPoly_const _)) (inOPoly_const 2)
  have hcomp : inOPoly ((fun m => Compile.physStepBudget m m)
      ∘ (fun n => 2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)) :=
    inOPoly_comp hinner Compile.physStepBudget_poly
  have hphys : inOPoly (fun n =>
      Compile.physStepBudget (2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)
        (costBound n)) := by
    refine inOPoly_of_le ?_ hcomp
    intro n
    show Compile.physStepBudget (2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)
          (costBound n)
        ≤ Compile.physStepBudget (2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)
            (2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)
    exact Compile.physStepBudget_mono (Nat.le_refl _) (by omega)
  exact inOPoly_add (inOPoly_add hlin (inOPoly_const 1))
    (inOPoly_add hphys (inOPoly_const 3))

private theorem DecidesLang.padTimeBound_mono {X : Type} [encodable X]
    {P : X → Prop} {costBound : Nat → Nat} (D : DecidesLang P costBound)
    (hmono : monotonic costBound) : monotonic D.padTimeBound := by
  intro a b hab
  have hd : costBound a ≤ costBound b := hmono a b hab
  unfold DecidesLang.padTimeBound
  have h1 : (D.regBound + 2 * D.c.loopDepth + 2 + 1)
        * (2 * costBound a + 4 * (D.regBound + 2 * D.c.loopDepth + 2) + 12)
      ≤ (D.regBound + 2 * D.c.loopDepth + 2 + 1)
        * (2 * costBound b + 4 * (D.regBound + 2 * D.c.loopDepth + 2) + 12) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : Compile.physStepBudget
        (2 * costBound a + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2) (costBound a)
      ≤ Compile.physStepBudget
        (2 * costBound b + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2) (costBound b) :=
    Compile.physStepBudget_mono (by omega) hd
  exact Nat.add_le_add (Nat.add_le_add h1 (Nat.le_refl 1)) (Nat.add_le_add h2 (Nat.le_refl 3))

/-- **A program deciding `R` yields a Turing machine deciding `R`.** The program must read
the pair `(x, c)` from the canonical two-register layout. The machine is the compiled
program, preceded by a register-padding phase and followed by a test of register `0`. -/
theorem DecidesLang.toMachine {R : List Bool → List Bool → Prop} {costBound : Nat → Nat}
    (D : DecidesLang (fun p : List Bool × List Bool => R p.1 p.2) costBound)
    (hpoly : inOPoly costBound) (hmono : monotonic costBound)
    (hin : ∀ x c, D.encodeIn (x, c) = certState x ++ certState c) :
    ∃ (t : Nat → Nat) (M : FlatTM) (acc rej : Nat),
      inOPoly t ∧ validFlatTM M ∧ M.tapes = 1 ∧ decidesPairInTime M acc rej R t := by
  refine ⟨fun n => D.padTimeBound (2 * n + 1), Compile.paddedBitDeciderTM D.c D.regBound,
    1 + (Compile D.regBound D.c).states
      + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states,
    2 + (Compile D.regBound D.c).states
      + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states,
    ?_, Compile.paddedBitDeciderTM_valid _ _, Compile.paddedBitDeciderTM_tapes _ _, ?_⟩
  · show inOPoly (D.padTimeBound ∘ fun n => 2 * n + 1)
    exact inOPoly_comp
      (inOPoly_add (inOPoly_mul (inOPoly_const 2) inOPoly_id) (inOPoly_const 1))
      (D.padTimeBound_poly hpoly)
  · intro x c
    have hsize : encodable.size (x, c) ≤ 2 * (x.length + c.length) + 1 := by
      show encodable.size x + encodable.size c + 1 ≤ _
      have := size_le_two_mul_length x
      have := size_le_two_mul_length c
      omega
    have hle : D.padTimeBound (encodable.size (x, c))
        ≤ D.padTimeBound (2 * (x.length + c.length) + 1) :=
      D.padTimeBound_mono hmono _ _ hsize
    obtain ⟨k, hk⟩ := Nat.le.dest (le_trans (D.budget_ge (x, c)) hle)
    have hrun_of : ∀ (b : Nat), (b = 0 ∨ b = 1) → (D.c.eval (D.encodeIn (x, c))).get 0 = [b] →
        ∃ cfg, runFlatTM (D.padTimeBound (2 * (x.length + c.length) + 1))
            (Compile.paddedBitDeciderTM D.c D.regBound)
            (initFlatConfig (Compile.paddedBitDeciderTM D.c D.regBound) [pairTape x c])
          = some cfg ∧
          haltingStateReached (Compile.paddedBitDeciderTM D.c D.regBound) cfg = true ∧
          cfg.state_idx = (if b = 1 then 1 else 2) + (Compile D.regBound D.c).states
            + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states := by
      intro b hb h0
      obtain ⟨cfg, hrun, hhalt, hstate⟩ :=
        Compile.paddedBitDecider_run D.c (D.encodeIn (x, c)) b D.regBound
          (D.enc_bit _) (D.width_le _) D.usesBelow hb h0
      refine ⟨cfg, ?_, hhalt, hstate⟩
      rw [pairTape_eq, ← hin x c, ← hk]
      exact runFlatTM_extend hrun hhalt
    by_cases hR : R x c
    · obtain ⟨cfg, hrun, hhalt, hstate⟩ := hrun_of 1 (Or.inr rfl)
        (eq_of_beq ((D.decides (x, c)).1.mp hR))
      rw [if_pos rfl] at hstate
      exact ⟨cfg, hrun, hhalt, ⟨fun _ => hstate, fun _ => hR⟩,
        ⟨fun h => absurd hR h, fun h => by exfalso; rw [hstate] at h; omega⟩⟩
    · obtain ⟨cfg, hrun, hhalt, hstate⟩ := hrun_of 0 (Or.inl rfl)
        (eq_of_beq ((D.decides (x, c)).2.mp hR))
      rw [if_neg (by decide : (0 : Nat) ≠ 1)] at hstate
      exact ⟨cfg, hrun, hhalt, ⟨fun h => absurd h hR, fun h => by exfalso; rw [hstate] at h; omega⟩,
        ⟨fun _ => hstate, fun _ => hR⟩⟩

end CookLevin.Lang
