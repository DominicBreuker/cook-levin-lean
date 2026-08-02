import Complexity.Lang.Serialize
import Complexity.Lang.HardnessStr

set_option autoImplicit false

/-! # `Serialize (List Bool)` — the canonical bit-string layout

The `NPhardStr` statement already pins one canonical layout of a bit string:
`certState x` (`Lang/PolyTime.lean`), the single register holding one `0`/`1`
cell per bit. This file makes that layout a `Serialize` instance, so that a
witness whose **output** type is `List Bool` can take its `decodeOut` from
`Serialize.decodeD` instead of hand-writing an inverse — the chain-end
discipline of standing risk 1.

## Why this is the smallest possible honesty obligation

There is exactly one function to read, `strBits`, and it is a `List.map` of a
two-case `if`. `dec` reads the cells back the same way; a cell that is neither
`0` nor `1` makes the whole parse fail, so `dec` has no junk branch that could
be steered. Consequently:

```
Serialize.enc (x : List Bool) = strBits x      and      certState x = [strBits x]
```

— the serialization at a chain **end** and the canonical layout at the chain
**head** are literally the same function. Nothing has to be checked to see that
they agree.

## ⚠ FINDING AT — this instance is why `Serialize`'s no-compression law is a
polynomial law

`encodable.size` for `List Bool` charges one per element *plus* the element's
own size, and `encodable.size true = 1`. So

```
encodable.size ([true] : List Bool) = 2   >   1 = (strBits [true]).length
```

and the *identity* form of `size_le_enc_length` (`size x ≤ |enc x|`, the form
the class carried until 2026-08-05) is **unsatisfiable by the canonical
layout** — not because anything is compressed (`strBits` is a bijection onto
`{0,1}^n`) but because `encodable.size` over-counts by up to a factor two. The
class law was generalised to `size x ≤ sizeLB |enc x|` for a polynomial
`sizeLB`, exactly the shape `InNPWitnessLangFreeSplit.sizeLB` already had for
the same obligation; here `sizeLB := fun n => 2 * n` and the proof is
`Complexity.Lang.size_le_two_mul_length`, which was already in the development.
See `Lang/Serialize.lean` for the full note.
-/

namespace Complexity.Lang

/-! ## The layout -/

/-- **The canonical cell layout of a bit string**: one `0`/`1` cell per bit.
This is the content of `certState x`'s only register. -/
def strBits (x : List Bool) : List Nat := x.map (fun b => if b then 1 else 0)

theorem certState_eq_strBits (x : List Bool) : certState x = [strBits x] := rfl

theorem strBits_length (x : List Bool) : (strBits x).length = x.length :=
  List.length_map _

theorem strBits_bit (x : List Bool) : ∀ v ∈ strBits x, v ≤ 1 := by
  intro v hv
  obtain ⟨b, -, hb⟩ := List.mem_map.mp hv
  rw [← hb]; cases b <;> simp

/-! ## The parser

Total and cell-wise: a `1` is `true`, a `0` is `false`, anything else fails the
whole parse. There is no fallback branch inside `decBits` that a dishonest
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
  -- FINDING AT: the identity form is unsatisfiable here; `2 * ·` is exact
  -- (`encodable.size` charges 2 for a `true`, 1 for a `false`).
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

/-- The instance's encoder is `strBits`, definitionally. Pinned so a refactor of
the instance breaks a `rfl` rather than a reading. -/
theorem Serialize.enc_listBool (x : List Bool) : Serialize.enc x = strBits x := rfl

/-- …and the canonical *head* layout is the same function, in one register. -/
theorem Serialize.certState_eq_enc (x : List Bool) :
    certState x = [Serialize.enc x] := rfl

end Complexity.Lang
