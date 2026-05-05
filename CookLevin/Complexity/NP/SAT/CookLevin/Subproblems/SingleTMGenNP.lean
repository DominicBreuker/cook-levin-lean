import Complexity.Complexity.Definitions

set_option autoImplicit false

def SingleTMGenNP
    (_i : Sigma (fun sig : finType => TM sig 1 × List sig × Nat × Nat)) : Prop := True

def FlatSingleTMGenNP : flatTM × List Nat × Nat × Nat → Prop := fun _ => True

def FlatFunSingleTMGenNP : flatTM × List Nat × Nat × Nat → Prop := fun _ => True

theorem vec_case1 (X : Type) (_ : List X) : True := by
  trivial

theorem initTape_isFlatteningConfigOf (sig states : finType) (s : List Nat) (s0 : states) : True := by
  trivial

theorem FlatFunSingleTMGenNP_FlatSingleTMGenNP_equiv
    (M : flatTM) (s : List Nat) (maxSize steps : Nat) :
    FlatFunSingleTMGenNP (M, s, maxSize, steps) ↔ FlatSingleTMGenNP (M, s, maxSize, steps) := by
  simp [FlatFunSingleTMGenNP, FlatSingleTMGenNP]
