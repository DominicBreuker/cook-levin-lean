import CookLevin.Basic.StringTM
import Mathlib.Tactic

set_option autoImplicit false

/-! # A run of a machine as an iterated total step, and the tape as a zipper

Two facts about the machine model that the register-language simulation of a Turing
machine (`Simulation/Program.lean`) is built on.

* `runFlatTM n M cfg = some ((stepCfg M)^[n] cfg)`: a bounded run is the `n`-fold iterate of
  a total step function that leaves halting and stuck configurations unchanged.
* A tape `(left, h, right)` is represented by the zipper `zip h right`: the cells left of
  the head (nearest first), the cells from the head on, and the distance by which the head
  is beyond the written region. Reading, writing and moving are local operations on the
  zipper (`zip_tapeStep`, `currentTapeSymbol_eq`), which a register program can perform
  with a bounded number of operations per step.
-/

namespace CookLevin.Sim

/-! ## Runs as iterates -/

/-- One step of `runFlatTM` as a total function: halting and stuck configurations are
fixed points. -/
def stepCfg (M : FlatTM) (cfg : FlatTMConfig) : FlatTMConfig :=
  if haltingStateReached M cfg then cfg else (stepFlatTM M cfg).getD cfg

theorem runFlatTM_eq_iterate (M : FlatTM) :
    ∀ (n : Nat) (cfg : FlatTMConfig), runFlatTM n M cfg = some ((stepCfg M)^[n] cfg)
  | 0, _ => rfl
  | n + 1, cfg => by
      rw [Function.iterate_succ_apply]
      by_cases hh : haltingStateReached M cfg = true
      · have hfix : stepCfg M cfg = cfg := by simp [stepCfg, hh]
        rw [hfix, Function.iterate_fixed hfix, runFlatTM_of_halting M cfg _ hh]
      · cases hs : stepFlatTM M cfg with
        | none =>
            have hfix : stepCfg M cfg = cfg := by simp [stepCfg, hh, hs]
            rw [hfix, Function.iterate_fixed hfix,
              runFlatTM_stuck M cfg (by simpa using hh) hs]
        | some cfg' =>
            have hst : stepCfg M cfg = cfg' := by simp [stepCfg, hh, hs]
            rw [hst, ← runFlatTM_eq_iterate M n cfg']
            show (if haltingStateReached M cfg = true then some cfg
                  else match stepFlatTM M cfg with
                    | none => some cfg
                    | some cfg' => runFlatTM n M cfg') = _
            rw [if_neg hh, hs]

/-! ## The zipper -/

/-- The zipper of a tape with head `h` and written cells `right`: the cells left of the head
(nearest first), the cells from the head on, and how far the head is beyond the end. -/
structure Zip where
  lft : List Nat
  rgt : List Nat
  exc : Nat
  deriving DecidableEq

def zip (h : Nat) (right : List Nat) : Zip :=
  ⟨(right.take h).reverse, right.drop h, h - right.length⟩

/-- Writing on the zipper: replace the head cell, unless the head is beyond the end. -/
def Zip.write (z : Zip) : Option Nat → Zip
  | none => z
  | some v => if z.exc = 0 then ⟨z.lft, v :: z.rgt.tail, 0⟩ else z

/-- Moving on the zipper. -/
def Zip.move (z : Zip) : TMMove → Zip
  | .Rmove =>
      match z.rgt with
      | [] => ⟨z.lft, [], z.exc + 1⟩
      | a :: r => ⟨a :: z.lft, r, z.exc⟩
  | .Lmove =>
      if z.exc = 0 then
        match z.lft with
        | [] => z
        | a :: l => ⟨l, a :: z.rgt, 0⟩
      else ⟨z.lft, z.rgt, z.exc - 1⟩
  | .Nmove => z

theorem currentTapeSymbol_eq (left : List Nat) (h : Nat) (right : List Nat) :
    currentTapeSymbol (left, h, right) = (zip h right).rgt.head? := by
  unfold currentTapeSymbol zip
  simp only
  by_cases hh : h < right.length
  · rw [dif_pos hh, List.head?_drop, List.getElem?_eq_getElem hh]
    rfl
  · rw [dif_neg hh, List.drop_eq_nil_of_le (Nat.le_of_not_lt hh)]
    rfl

/-- The written tape after a write, as a pair (head, cells). -/
theorem zip_write (left : List Nat) (h : Nat) (right : List Nat) (w : Option Nat) :
    zip (writeCurrentTapeSymbol (left, h, right) w).2.1
        (writeCurrentTapeSymbol (left, h, right) w).2.2
      = (zip h right).write w := by
  cases w with
  | none => rfl
  | some v =>
      simp only [writeCurrentTapeSymbol, Zip.write, zip]
      by_cases hlt : h < right.length
      · rw [dif_pos hlt]
        have hle : h ≤ right.length := Nat.le_of_lt hlt
        have hlen : (right.take h).length = h := List.length_take_of_le hle
        rw [if_pos (by omega)]
        simp only [Zip.mk.injEq]
        refine ⟨?_, ?_, ?_⟩
        · rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        · rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
            List.nil_append, List.tail_drop]
        · simp [List.length_append, List.length_drop]; omega
      · rw [dif_neg hlt]
        by_cases heq : h = right.length
        · rw [if_pos heq, if_pos (by omega)]
          subst heq
          simp
        · rw [if_neg heq, if_neg (by omega)]

theorem zip_move (left : List Nat) (h : Nat) (right : List Nat) (m : TMMove) :
    zip (moveTapeHead (left, h, right) m).2.1 (moveTapeHead (left, h, right) m).2.2
      = (zip h right).move m := by
  cases m with
  | Nmove => rfl
  | Rmove =>
      simp only [moveTapeHead, Zip.move, zip]
      by_cases hlt : h < right.length
      · have hd : right.drop h = right[h] :: right.drop (h + 1) := List.drop_eq_getElem_cons hlt
        rw [hd]
        simp only [Zip.mk.injEq]
        refine ⟨?_, by simp, by omega⟩
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        simp
      · have hd : right.drop h = [] := List.drop_eq_nil_of_le (by omega)
        rw [hd]
        simp only [Zip.mk.injEq]
        refine ⟨?_, List.drop_eq_nil_of_le (by omega), by omega⟩
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  | Lmove =>
      simp only [moveTapeHead, Zip.move, zip]
      by_cases he : h - right.length = 0
      · rw [if_pos he]
        rcases Nat.eq_zero_or_pos h with h0 | hpos
        · subst h0
          simp
        · have hlt : h - 1 < right.length := by omega
          have ht : right.take h = right.take (h - 1) ++ [right[h - 1]] := by
            conv_lhs => rw [show h = (h - 1) + 1 by omega]
            rw [List.take_add_one, List.getElem?_eq_getElem hlt]
            simp
          rw [ht]
          simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.singleton_append]
          simp only [Zip.mk.injEq]
          refine ⟨by simp, ?_, by omega⟩
          rw [List.drop_eq_getElem_cons hlt, show h - 1 + 1 = h by omega]
      · rw [if_neg he]
        simp only [Zip.mk.injEq]
        refine ⟨?_, ?_, by omega⟩
        · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]

/-- **One tape step on the zipper.** -/
theorem zip_tapeStep (left : List Nat) (h : Nat) (right : List Nat) (w : Option Nat)
    (m : TMMove) :
    zip (tapeStep (left, h, right) w m).2.1 (tapeStep (left, h, right) w m).2.2
      = ((zip h right).write w).move m := by
  unfold tapeStep
  rw [← zip_write left h right w]
  obtain ⟨l', h', r'⟩ := writeCurrentTapeSymbol (left, h, right) w
  exact zip_move l' h' r' m

/-- The left part of the tape is never changed by a step. -/
theorem tapeStep_left (left : List Nat) (h : Nat) (right : List Nat) (w : Option Nat)
    (m : TMMove) : (tapeStep (left, h, right) w m).1 = left := by
  cases w <;> cases m <;>
    simp only [tapeStep, writeCurrentTapeSymbol, moveTapeHead] <;> split_ifs <;> rfl

end CookLevin.Sim
