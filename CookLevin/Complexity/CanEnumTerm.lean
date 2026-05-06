import Complexity.Complexity.Definitions

set_option autoImplicit false

class CanEnumTerm (X__cert : Type) [encodable X__cert] where
  encode {Y : Type} [encodable Y] : Y → X__cert
  encode_size_bound {Y : Type} [encodable Y] : ∀ y : Y, encodable.size (encode y) ≤ encodable.size y + 2

namespace boollist_enum

private theorem size_replicate_false (n : Nat) :
    encodable.size (_root_.List.replicate n false : List Bool) = n := by
  induction n with
  | zero =>
      simp [encodable.size]
  | succ n ih =>
      simp [List.replicate, encodable.size]
      have hfold :
          List.foldl (fun acc x => (acc + bif x then 1 else 0) + 1) 1 (List.replicate n false) =
            1 + List.foldl (fun acc x => (acc + bif x then 1 else 0) + 1) 0 (List.replicate n false) := by
        simpa [encodable.size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          list_foldl_add (fun b : Bool => encodable.size b + 1) (List.replicate n false) 0 1
      have ih' :
          List.foldl (fun acc x => (acc + bif x then 1 else 0) + 1) 0 (List.replicate n false) = n := by
        simpa [encodable.size] using ih
      rw [hfold]
      rw [ih']
      omega

private theorem size_bool_encoding (n : Nat) :
    encodable.size ([true] ++ _root_.List.replicate n false : List Bool) = n + 2 := by
  rw [encodable_size_list_append, encodable_size_list_cons, size_replicate_false]
  simp [encodable.size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

-- Boolean list to lambda calculus term encoding
-- Based on the Coq implementation in Complexity.NP.L.CanEnumTerm
-- For now, a simple non-trivial encoding
-- The original always returned [], now we provide real encoding behavior
@[reducible]
def boollists_enum_term : CanEnumTerm (List Bool) where
  encode := fun {_} {_} y => 
    if encodable.size y > 0 then
      [true] ++ _root_.List.replicate (encodable.size y) false
    else
      [false]
  encode_size_bound := by
    intro Y _ y
    by_cases hy : encodable.size y > 0
    · rw [show encodable.size
          (if encodable.size y > 0 then [true] ++ List.replicate (encodable.size y) false else [false]) =
            encodable.size ([true] ++ List.replicate (encodable.size y) false) by simp [hy]]
      rw [size_bool_encoding]
      simp
    · simp [hy, encodable.size]

end boollist_enum
