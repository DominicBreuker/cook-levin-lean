import CookLevin.Lang.Serialize
import CookLevin.Lang.PolyTime
import CookLevin.Basic.StringTM

/-!
# Serializing bit strings

The canonical register layout of a bit string is one cell per bit (`strBits`, the register
of `certState`). `boolsOf` reads a register back as a string, `decBits` is the partial
inverse used by the `Serialize (List Bool)` instance, and `decodeD_eq_boolsOf` identifies
the two readers on the encoded registers.
-/

set_option autoImplicit false

namespace CookLevin.Lang

/-! ## The layout -/

/-- **The canonical cell layout of a bit string**: one `0`/`1` cell per bit.
This is the content of `certState x`'s only register. -/
def strBits (x : List Bool) : List Nat := x.map (fun b => if b then 1 else 0)

theorem strBits_length (x : List Bool) : (strBits x).length = x.length :=
  List.length_map _

theorem strBits_bit (x : List Bool) : ∀ v ∈ strBits x, v ≤ 1 := by
  intro v hv
  obtain ⟨b, -, hb⟩ := List.mem_map.mp hv
  rw [← hb]; cases b <;> simp

/-! ## The parser

Total and cell-wise: a `1` is `true`, a `0` is `false`, anything else fails the
whole parse. There is no fallback branch inside `decBits` that a wrong
layout could be routed through. -/

/-- Read the cells back. `none` on any cell that is not a bit. -/
def decBits : List Nat → Option (List Bool)
  | [] => some []
  | 0 :: rest => (decBits rest).map (fun l => false :: l)
  | 1 :: rest => (decBits rest).map (fun l => true :: l)
  | _ :: _ => none

/-- **`decBits` is a genuine left inverse of `strBits`** — no `Classical`. -/
theorem decBits_strBits (x : List Bool) : decBits (strBits x) = some x := by
  induction x with
  | nil => rfl
  | cons b t ih =>
      cases b
      · show (decBits (strBits t)).map (fun l => false :: l) = _
        rw [ih]; rfl
      · show (decBits (strBits t)).map (fun l => true :: l) = _
        rw [ih]; rfl

/-! ## Reading a bit-cell stream as a string

The inverse direction as a *total* function (not `Option`): any cell stream that
is already `0`/`1` — which is every stream this layer's `BitState` programs
produce — is the layout of exactly one bit string, and `boolsOf` names it. This
is the tool a reduction whose **output type** is `List Bool` uses to say what
its map is. -/

/-- The bit string a `0`/`1` cell stream spells out. -/
def boolsOf (l : List Nat) : List Bool := l.map (fun v => decide (v = 1))

/-- **`boolsOf` is a right inverse of `strBits` on bit streams.** The hypothesis
is not decoration: `boolsOf [2] = [false]` and `strBits [false] = [0] ≠ [2]`. -/
theorem strBits_boolsOf : ∀ {l : List Nat}, (∀ v ∈ l, v ≤ 1) → strBits (boolsOf l) = l
  | [], _ => rfl
  | v :: t, h => by
      have hv : v ≤ 1 := h v (List.mem_cons_self ..)
      have ht : ∀ w ∈ t, w ≤ 1 := fun w hw => h w (List.mem_cons_of_mem v hw)
      show (if decide (v = 1) then 1 else 0) :: strBits (boolsOf t) = v :: t
      rw [strBits_boolsOf ht]
      interval_cases v <;> rfl

/-! ## The instance -/

/-- **`Serialize (List Bool)`** — the canonical bit-string layout, i.e. exactly
the register `certState` puts a string in. A chain end whose output type is
`List Bool` takes `decodeOut := Serialize.decodeD [] ∘ State.get · OUT`. -/
instance instSerializeListBool : Serialize (List Bool) where
  enc := strBits
  dec := decBits
  dec_enc := decBits_strBits
  enc_bit := strBits_bit
  -- `encodable.size` charges 2 for a `true` and 1 for a `false`.
  sizeLB := fun n => 2 * n
  sizeLB_poly := inOPoly_mul (inOPoly_const 2) inOPoly_id
  sizeLB_mono := fun _ _ h => Nat.mul_le_mul_left 2 h
  size_le_enc_length := fun x => by
    rw [strBits_length]; exact size_le_two_mul_length x
  encLen := fun n => n
  encLen_poly := inOPoly_id
  encLen_mono := fun _ _ h => h
  enc_length_le := fun x => by
    rw [strBits_length]; exact length_le_size x

/-- On a bit stream the total decoder is `boolsOf`. -/
theorem decodeD_eq_boolsOf (l : List Nat) (hl : ∀ v ∈ l, v ≤ 1) :
    Serialize.decodeD ([] : List Bool) l = boolsOf l := by
  have h := decBits_strBits (boolsOf l)
  rw [strBits_boolsOf hl] at h
  show (decBits l).getD [] = boolsOf l
  rw [h]
  rfl

end CookLevin.Lang
