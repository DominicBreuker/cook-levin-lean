import Complexity.Complexity.Definitions

set_option autoImplicit false

/-! # Tape encoding helpers (Part 2 Step 2)

We will need to lay structured data (pairs, lists of lists) onto a
single TM tape. We adopt the simplest convention compatible with the
1-tape `DecidesBy` interface:

- Symbol `0` is reserved as a delimiter on the tape.
- Payload symbols are shifted by `+1`.

This file is pure list arithmetic — no TMs are constructed here. The
goal is to have small, well-named building blocks and length lemmas so
that downstream files can quote them without re-deriving the same
inequalities.
-/

namespace TMEncoding

/-- Shift every symbol in a flat-tape word up by one, freeing `0` as a
delimiter. -/
def shiftSyms (xs : List Nat) : List Nat :=
  xs.map (· + 1)

@[simp]
theorem shiftSyms_nil : shiftSyms [] = [] := rfl

@[simp]
theorem shiftSyms_cons (x : Nat) (xs : List Nat) :
    shiftSyms (x :: xs) = (x + 1) :: shiftSyms xs := rfl

@[simp]
theorem shiftSyms_length (xs : List Nat) :
    (shiftSyms xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      show ((x + 1) :: shiftSyms xs).length = (x :: xs).length
      rw [List.length_cons, List.length_cons, ih]

theorem shiftSyms_append (xs ys : List Nat) :
    shiftSyms (xs ++ ys) = shiftSyms xs ++ shiftSyms ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      show shiftSyms ((x :: xs) ++ ys) = shiftSyms (x :: xs) ++ shiftSyms ys
      show shiftSyms (x :: (xs ++ ys)) = (x + 1) :: shiftSyms xs ++ shiftSyms ys
      show (x + 1) :: shiftSyms (xs ++ ys) = (x + 1) :: (shiftSyms xs ++ shiftSyms ys)
      rw [ih]

/-- Encoding of a pair of words on a single tape: place `xs`, a `0`
delimiter, then `ys`. The payload words are assumed to already be
delimiter-free (i.e. obtained via `shiftSyms`). -/
def encodePair (xs ys : List Nat) : List Nat :=
  xs ++ 0 :: ys

theorem encodePair_length (xs ys : List Nat) :
    (encodePair xs ys).length = xs.length + ys.length + 1 := by
  show (xs ++ 0 :: ys).length = xs.length + ys.length + 1
  rw [List.length_append, List.length_cons]
  exact (Nat.add_assoc xs.length ys.length 1).symm

/-- Encoding of a list of words on a single tape: write each word in
turn, separated by `0` delimiters, and bracket the whole sequence
with leading and trailing `0`s. Choosing this symmetric form makes the
left and right boundaries detectable by scanning until `0`. -/
def encodeList : List (List Nat) → List Nat
  | [] => [0]
  | xs :: rest => 0 :: xs ++ encodeList rest

theorem encodeList_nil : encodeList [] = [0] := rfl

theorem encodeList_cons (xs : List Nat) (rest : List (List Nat)) :
    encodeList (xs :: rest) = 0 :: xs ++ encodeList rest := rfl

/-- Pure-Nat helper: a 3-variable rearrangement we need below. -/
private theorem aux_rearrange (c a b : Nat) :
    c + 1 + (a + b + 1) = c + a + (b + 1) + 1 := by
  calc c + 1 + (a + b + 1)
      = c + (1 + (a + b + 1)) := Nat.add_assoc c 1 _
    _ = c + (a + b + 1 + 1)   := by rw [Nat.add_comm 1 (a + b + 1)]
    _ = c + (a + b + 1) + 1   := (Nat.add_assoc c (a + b + 1) 1).symm
    _ = c + (a + (b + 1)) + 1 := by rw [Nat.add_assoc a b 1]
    _ = c + a + (b + 1) + 1   := by rw [← Nat.add_assoc c a (b + 1)]

/-- Total length of `encodeList xss` is the sum of payload lengths
plus one delimiter per entry, plus one trailing terminator. -/
theorem encodeList_length :
    ∀ (xss : List (List Nat)),
      (encodeList xss).length =
        (xss.map List.length).sum + xss.length + 1
  | [] => rfl
  | xs :: rest => by
      have ih := encodeList_length rest
      show (0 :: xs ++ encodeList rest).length =
        ((xs :: rest).map List.length).sum + (xs :: rest).length + 1
      have hcons : (0 :: xs ++ encodeList rest).length
          = xs.length + 1 + (encodeList rest).length := by
        show ((0 :: xs) ++ encodeList rest).length
            = xs.length + 1 + (encodeList rest).length
        rw [List.length_append, List.length_cons, Nat.add_comm xs.length 1]
      rw [hcons, ih, List.map_cons, List.sum_cons, List.length_cons]
      exact aux_rearrange xs.length _ _

/-! ## Bounding payload sizes by `encodable.size`

The encoders consume tape symbols (`List Nat`) directly. Downstream
deciders provide a *shifted* encoding of their input as a `List Nat`,
and we want to bound that length by `encodable.size x + const`.

For inputs that are already `List Nat` (the only shape we need for
SAT and FlatClique), the relevant lemma is just `listNat_length_le_size`
below. -/

/-- For a list of natural numbers, the length is at most the encodable
size (which is `Σ (xᵢ + 1) ≥ |xs|`). -/
theorem listNat_length_le_size (xs : List Nat) :
    xs.length ≤ encodable.size xs := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
      rw [encodable_size_list_cons]
      show (x :: xs).length ≤ encodable.size x + 1 + encodable.size xs
      rw [List.length_cons]
      -- goal: xs.length + 1 ≤ encodable.size x + 1 + encodable.size xs
      have h1 : xs.length + 1 ≤ encodable.size xs + 1 := Nat.add_le_add_right ih 1
      have h2 : encodable.size xs + 1 ≤ encodable.size x + 1 + encodable.size xs := by
        rw [Nat.add_comm (encodable.size x + 1) (encodable.size xs)]
        exact Nat.add_le_add_left (Nat.le_add_left 1 (encodable.size x)) _
      exact Nat.le_trans h1 h2

end TMEncoding
