import Complexity.Lang.Semantics
import Complexity.Lang.Frame
import Complexity.Lang.AppendGadget
import Complexity.Lang.ClearGadget
import Complexity.Complexity.TMPrimitives
import Complexity.Complexity.TapeMono

set_option autoImplicit false

/-! # `Compile/Encoding` — tape encoding/decoding for the compiler

Extracted from `Compile.lean` (refactor Phase 1, see `REFACTOR-HANDOFF.md`).
The `State ↔ tape` encoding the whole compiler is stated against:

- `Compile.encodeTape`/`encodeRegs`/`shiftReg`/`endMark` — the leading-sentinel
  bit-level tape encoding (`encodeTape s = endMark :: encodeRegs s ++ [endMark]`).
- `Compile.decodeTape` (+ `splitOnZero`/`unshiftReg`/`dropTrailingEmpty`) and the
  round-trip lemmas (`decodeTape_encodeTape`).
- `Compile.BitState`/`ValidResidue` and the `encodeTape` structure lemmas
  (`encodeTape_split`, `encodeRegs_*`, `shiftReg_*`, …) the per-op rewind
  side-conditions and residue contracts consume.

Note: the former `private` modifiers were dropped on extraction so these symbols
export to the downstream `Compile` modules (they were file-private only because
everything used to live in one file). This module is a sibling of `Compile/Core`
(it references no `CompiledCmd`/combinator), depending only on the primitives. -/

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators

/-! ### Encoding / decoding tapes

Convention (alphabet `sig = 4`; Risk C1, option A):

- **Symbol 0** is the reserved register-delimiter.
- Register values are restricted to `{0, 1}` (bit strings) and are
  **shifted by +1** on encode: `0 ↦ 1`, `1 ↦ 2`. Decoding shifts
  back by `-1`. This keeps register values (`{1, 2}`) disjoint from
  both the delimiter `0` and the terminator below.
- **Symbol 3 = `endMark`** is the reserved end-of-tape terminator,
  appended once after all registers. Decoding reads only up to the
  first `endMark`. This is the device that makes length-*decreasing*
  `Op`s sound: such an `Op` cannot shrink the tape (the model only
  appends / overwrites), so it shifts content left and rewrites
  `endMark` one cell earlier — anything past the terminator is junk
  and is ignored by the decoder *and* by every navigation gadget,
  which stop at the terminator rather than reading past it.

So `encodeTape [[1, 0], [0, 1]] = [2, 1, 0, 1, 2, 0, 3]`, and decoding
takes the prefix before `3`, splits on `0`, shifts each chunk by `-1`,
and drops the trailing empty.

The shift+terminator scheme requires inputs to be **bit-shaped**
(`Compile.BitState`): with a register value of `2`, `shiftReg` would
emit `3` and collide with the terminator. `BitState` is the layer's
standing convention (NP-completeness inputs are bit strings) and is
preserved by `Op.eval`; it is also exactly what tape-validity needs
(every symbol `< sig = 4`). -/

/-- Encode the per-register shift `+1`. -/
def Compile.shiftReg (reg : List Nat) : List Nat := reg.map (· + 1)

/-- Reverse of `shiftReg`. Maps `0 ↦ 0` so the inverse is only valid
on tapes that contain no raw `0` (i.e., tapes produced by `shiftReg`). -/
def Compile.unshiftReg (reg : List Nat) : List Nat :=
  reg.map (fun n => n - 1)

/-- The reserved end-of-tape terminator symbol. -/
def Compile.endMark : Nat := 3

/-- A state is *bit-shaped* if every register holds only `0`/`1`.
The layer's standing convention; preserved by `Op.eval`. Keeps the
shifted values `{1, 2}` disjoint from the terminator `endMark = 3`. -/
def Compile.BitState (s : State) : Prop := ∀ reg ∈ s, ∀ x ∈ reg, x ≤ 1

/-- Encode the registers contiguously: each shifted by `+1` and
followed by the `0` delimiter. Does **not** include the terminator. -/
def Compile.encodeRegs (s : State) : List Nat :=
  s.foldr (fun reg acc => Compile.shiftReg reg ++ [0] ++ acc) []

theorem Compile.encodeRegs_nil :
    Compile.encodeRegs [] = [] := rfl

theorem Compile.encodeRegs_cons (reg : List Nat) (s : State) :
    Compile.encodeRegs (reg :: s) =
      Compile.shiftReg reg ++ [0] ++ Compile.encodeRegs s := rfl

/-- Encode a `State` as a flat tape: a **leading sentinel** `endMark`, the
registers (`encodeRegs`), and the end-of-tape terminator `endMark`.

The leading sentinel (reusing `endMark = 3`, so the alphabet stays `sig = 4`) is
the head-rewind anchor required to *compose* compiled fragments (Risk C2): a
compiled `Op` halts with its head mid-tape, but `composeFlatTM` resumes the next
machine on that exact head, while every per-`Op` soundness statement assumes the
head starts at `0`. `scanLeftUntilTM 4 3` (`ScanLeft.rewindToStart_run`) scans
left to this leading `3` at index `0`, since the interior carries only
`{0, 1, 2}` (`encodeRegs` of a `BitState`). The head starts at index `0` on the
sentinel; the scan/insert gadgets fold it into their first (marker-free) block,
so no head-bridge is needed. -/
def Compile.encodeTape (s : State) : List Nat :=
  Compile.endMark :: (Compile.encodeRegs s ++ [Compile.endMark])

/-- The encoded registers occupy `State.size s + s.length` cells: each register
contributes its (shifted) contents plus one `0` delimiter. -/
theorem Compile.encodeRegs_length (s : State) :
    (Compile.encodeRegs s).length = State.size s + s.length := by
  induction s with
  | nil => rfl
  | cons reg s ih =>
      rw [Compile.encodeRegs_cons]
      simp only [List.length_append, Compile.shiftReg, List.length_map, List.length_cons,
        List.length_nil, ih, State.size, List.map_cons, List.foldr_cons]
      omega

/-- **Tape length = contents + register count + 2.** The encoded tape is the
registers (`State.size s + s.length` cells) plus the leading and trailing
`endMark` sentinels. This is the link
between the per-op gadget step bounds (which grow with the *tape length*) and the
`State.size` / register-count bounds (`Cmd.size_eval_le` / `Cmd.eval_length_le`)
— so the intermediate tape length during a `Compile` run is bounded linearly in
`size + cost + regBound`. -/
theorem Compile.encodeTape_length (s : State) :
    (Compile.encodeTape s).length = State.size s + s.length + 2 := by
  rw [Compile.encodeTape, List.length_cons, List.length_append,
      Compile.encodeRegs_length]; rfl

/-- **Encoded-tape length balance for a register write (cross-register op
bookkeeping).** Writing `v` to an in-range register `dst` changes the encoded
tape length by `|v| − |old dst|`, stated in balance form to avoid ℕ subtraction:
`|encodeTape (s.set dst v)| + |old dst| = |encodeTape s| + |v|`.

Every cross-register op `dst := f (s.get src)` needs exactly this to express its
residue length (`res_out`) and bound its budget: a `set` in range preserves the
register count (`s.length`), so only the contents term moves — by
`State.size_set_add`. (Length-growing writes — `v` longer than the old register
— extend the tape; length-shrinking writes leave the freed cells as `0` residue,
which is why the deletion-op residue is `res_in ++ replicate (|old| − |v|) 0`.) -/
theorem Compile.encodeTape_set_length (s : State) (dst : Var) (v : List Nat)
    (h : dst < s.length) :
    (Compile.encodeTape (s.set dst v)).length + (s.get dst).length
      = (Compile.encodeTape s).length + v.length := by
  have hlen : (s.set dst v).length = s.length := by
    simp only [State.set, if_pos h, List.length_set]
  rw [Compile.encodeTape_length, Compile.encodeTape_length, hlen]
  have hbal := State.size_set_add s dst v
  omega

/-- Flatten a single TM tape `(left, head, right)` into a `List Nat`.

In this machine model (`MachineSemantics.lean`) the head is an *index*
into `right`, and the `left` component is never written by
`writeCurrentTapeSymbol` / `moveTapeHead` — it stays `[]` for every
configuration reachable from `initFlatConfig`. The full tape contents
are therefore exactly `right` (`tape.2.2`); `left` and the head index
carry no content. (The earlier definition concatenated
`left.reverse ++ [head] ++ right`, which spliced the head *index* into
the contents as if it were a symbol — that made the round-trip lemma
below unprovable.) -/
def Compile.flattenTape (tape : List Nat × Nat × List Nat) : List Nat :=
  tape.2.2

/-- Split a `List Nat` on `0`. Used to recover registers from an
encoded tape. -/
def Compile.splitOnZero : List Nat → List (List Nat)
  | []      => [[]]
  | 0 :: xs =>
      let rest := Compile.splitOnZero xs
      [] :: rest
  | x :: xs =>
      match Compile.splitOnZero xs with
      | []           => [[x]]   -- unreachable: splitOnZero never returns []
      | grp :: rest  => (x :: grp) :: rest

/-- Drop the trailing empty register if present (the encoding always
appends one). -/
def Compile.dropTrailingEmpty : List (List Nat) → List (List Nat)
  | []         => []
  | [[]]       => []
  | x :: rest  => x :: Compile.dropTrailingEmpty rest

/-- Decode an output configuration back into a `State`. Reads tape 0,
flattens, splits on the `0` delimiter, shifts each register back by
`-1`, and trims the trailing empty register. -/
def Compile.decodeTape (cfg : FlatTMConfig) : State :=
  match cfg.tapes with
  | []           => []
  | tape :: _    =>
      let flat := Compile.flattenTape tape
      -- Drop the leading sentinel, then read up to the trailing terminator.
      let content := flat.tail.takeWhile (· != Compile.endMark)
      let groups := Compile.splitOnZero content
      let trimmed := Compile.dropTrailingEmpty groups
      trimmed.map Compile.unshiftReg

/-! ### Round-trip lemmas for `decodeTape ∘ encodeTape`

These discharge the `decodeTape_encodeTape` obligation by a short
chain of structural inductions over the encoder's pieces. -/

/-- `splitOnZero` never returns the empty list (every branch produces
at least one group). -/
theorem Compile.splitOnZero_ne_nil :
    ∀ l : List Nat, Compile.splitOnZero l ≠ []
  | []          => by simp [Compile.splitOnZero]
  | 0 :: _      => by simp [Compile.splitOnZero]
  | (_ + 1) :: xs => by
      simp only [Compile.splitOnZero]
      cases Compile.splitOnZero xs <;> simp

/-- Shifted register contents contain no `0` (the delimiter), since
`shiftReg` maps every value to its successor. -/
theorem Compile.shiftReg_no_zero (reg : List Nat) :
    ∀ x ∈ Compile.shiftReg reg, x ≠ 0 := by
  intro x hx
  simp only [Compile.shiftReg, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  omega

/-- Splitting `a ++ 0 :: b` on the delimiter, when `a` has no
delimiter, peels off `a` as the first group. -/
theorem Compile.splitOnZero_append_zero :
    ∀ (a b : List Nat), (∀ x ∈ a, x ≠ 0) →
      Compile.splitOnZero (a ++ 0 :: b) = a :: Compile.splitOnZero b
  | [],          b, _ => by simp [Compile.splitOnZero]
  | (x :: a'), b, h => by
      have hx : x ≠ 0 := h x (by simp)
      have ha' : ∀ y ∈ a', y ≠ 0 := fun y hy => h y (by simp [hy])
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hx
      simp only [List.cons_append, Compile.splitOnZero,
        Compile.splitOnZero_append_zero a' b ha']

/-- The decoder's split step recovers exactly the shifted registers
plus the trailing empty group from the encoder's final delimiter. -/
theorem Compile.splitOnZero_encodeRegs :
    ∀ s : State,
      Compile.splitOnZero (Compile.encodeRegs s)
        = s.map Compile.shiftReg ++ [[]]
  | []          => by simp [Compile.encodeRegs, Compile.splitOnZero]
  | reg :: rest => by
      rw [Compile.encodeRegs_cons]
      have happ : Compile.shiftReg reg ++ [0] ++ Compile.encodeRegs rest
          = Compile.shiftReg reg ++ 0 :: Compile.encodeRegs rest := by simp
      rw [happ, Compile.splitOnZero_append_zero _ _ (Compile.shiftReg_no_zero reg),
          Compile.splitOnZero_encodeRegs rest, List.map_cons, List.cons_append]

/-- `encodeRegs` of a bit-shaped state never emits the terminator
`endMark`: delimiters are `0` and shifted bits are `{1, 2}`. -/
theorem Compile.encodeRegs_no_endMark :
    ∀ (s : State), Compile.BitState s →
      ∀ x ∈ Compile.encodeRegs s, x ≠ Compile.endMark
  | [],          _, x, hx => by simp [Compile.encodeRegs] at hx
  | reg :: rest, h, x, hx => by
      rw [Compile.encodeRegs_cons] at hx
      simp only [List.append_assoc, List.mem_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx
      · simp only [Compile.shiftReg, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have : y ≤ 1 := h reg (by simp) y hy
        simp only [Compile.endMark]; omega
      · simp only [Compile.endMark]; omega
      · exact Compile.encodeRegs_no_endMark rest
          (fun r hr => h r (by simp [hr])) x hx

/-- Taking the prefix before the terminator recovers the registers,
provided the registers themselves contain no terminator. -/
theorem Compile.takeWhile_no_endMark :
    ∀ (l : List Nat), (∀ x ∈ l, x ≠ Compile.endMark) →
      (l ++ [Compile.endMark]).takeWhile (· != Compile.endMark) = l
  | [],     _ => by decide
  | a :: t, h => by
      have ha : a ≠ Compile.endMark := h a (by simp)
      have ht : ∀ x ∈ t, x ≠ Compile.endMark := fun x hx => h x (by simp [hx])
      rw [List.cons_append, List.takeWhile_cons,
          if_pos (by simp [bne_iff_ne, ha]), Compile.takeWhile_no_endMark t ht]

/-- `dropTrailingEmpty` peels exactly one trailing empty group. -/
theorem Compile.dropTrailingEmpty_cons_ne_nil
    (x : List Nat) (ys : List (List Nat)) (h : ys ≠ []) :
    Compile.dropTrailingEmpty (x :: ys) = x :: Compile.dropTrailingEmpty ys := by
  cases ys with
  | nil => exact absurd rfl h
  | cons _ _ => cases x <;> rfl

/-- The encoder's trailing empty group is exactly what
`dropTrailingEmpty` removes, leaving the list of shifted registers. -/
theorem Compile.dropTrailingEmpty_append_nil :
    ∀ l : List (List Nat), Compile.dropTrailingEmpty (l ++ [[]]) = l
  | []        => rfl
  | x :: rest => by
      have h : rest ++ [[]] ≠ [] := by
        intro hc; simpa using congrArg List.length hc
      rw [List.cons_append, Compile.dropTrailingEmpty_cons_ne_nil x _ h,
          Compile.dropTrailingEmpty_append_nil rest]

/-- `unshiftReg` inverts `shiftReg`. -/
theorem Compile.unshiftReg_shiftReg (reg : List Nat) :
    Compile.unshiftReg (Compile.shiftReg reg) = reg := by
  simp only [Compile.unshiftReg, Compile.shiftReg, List.map_map]
  have h : ((fun n => n - 1) ∘ fun x => x + 1) = id := by funext n; simp
  rw [h, List.map_id]

/-- Decoding the shifted registers recovers the original state. -/
theorem Compile.map_unshift_shift (s : State) :
    (s.map Compile.shiftReg).map Compile.unshiftReg = s := by
  rw [List.map_map,
      show Compile.unshiftReg ∘ Compile.shiftReg = id from
        funext Compile.unshiftReg_shiftReg,
      List.map_id]

/-- Round-trip lemma — needed by `Compile_sound`. The decoder, applied
to the encoder's initial configuration, recovers the state exactly,
for any bit-shaped state. -/
theorem Compile.decodeTape_encodeTape (s : State) (h : Compile.BitState s) :
    Compile.decodeTape
        { tapes := [([], 0, Compile.encodeTape s)]
          state_idx := 0 } = s := by
  show (Compile.dropTrailingEmpty
        (Compile.splitOnZero
          ((Compile.flattenTape (([] : List Nat), (0 : Nat), Compile.encodeTape s)).tail.takeWhile
            (· != Compile.endMark)))).map Compile.unshiftReg = s
  rw [show (Compile.flattenTape (([] : List Nat), (0 : Nat), Compile.encodeTape s)).tail
        = Compile.encodeRegs s ++ [Compile.endMark] from rfl,
      Compile.takeWhile_no_endMark _ (Compile.encodeRegs_no_endMark s h),
      Compile.splitOnZero_encodeRegs, Compile.dropTrailingEmpty_append_nil,
      Compile.map_unshift_shift]

/-- Generalisation of `takeWhile_no_endMark`: taking the prefix before the first
terminator recovers `l`, even when arbitrary `rest` follows the terminator. -/
theorem Compile.takeWhile_no_endMark_append :
    ∀ (l rest : List Nat), (∀ x ∈ l, x ≠ Compile.endMark) →
      (l ++ Compile.endMark :: rest).takeWhile (· != Compile.endMark) = l
  | [],     rest, _ => by
      rw [List.nil_append, List.takeWhile_cons, if_neg (by simp [bne_iff_ne])]
  | a :: t, rest, h => by
      have ha : a ≠ Compile.endMark := h a (by simp)
      have ht : ∀ x ∈ t, x ≠ Compile.endMark := fun x hx => h x (by simp [hx])
      rw [List.cons_append, List.takeWhile_cons,
          if_pos (by simp [bne_iff_ne, ha]), Compile.takeWhile_no_endMark_append t rest ht]

/-- **Residue-tolerant decode (Risk C2 resolution foundation).** `decodeTape`
ignores both the head position and any trailing residue after the encoded tape:
decoding `encodeTape s ++ residue` recovers `s` for *any* `residue` and *any*
head `hd`. This holds because `decodeTape` reads `takeWhile (· ≠ endMark)` of the
tail, which stops at the **first** (real) terminator — and `encodeRegs s` of a
`BitState` contains no terminator. This is the key lemma that makes the
recommended residue-tolerant physical contract decode correctly: a length-
decreasing op may leave `encodeTape (output) ++ residue` on the (non-shrinking)
tape (see `Complexity/Complexity/TapeMono.lean`), yet still decode to `output`.
-/
theorem Compile.decodeTape_encodeTape_append (s : State) (residue : List Nat)
    (q hd : Nat) (h : Compile.BitState s) :
    Compile.decodeTape
        { state_idx := q, tapes := [([], hd, Compile.encodeTape s ++ residue)] } = s := by
  show (Compile.dropTrailingEmpty (Compile.splitOnZero
        ((Compile.flattenTape (([] : List Nat), hd, Compile.encodeTape s ++ residue)).tail.takeWhile
          (· != Compile.endMark)))).map Compile.unshiftReg = s
  have htail : (Compile.flattenTape (([] : List Nat), hd, Compile.encodeTape s ++ residue)).tail
      = Compile.encodeRegs s ++ Compile.endMark :: residue := by
    show (Compile.encodeTape s ++ residue).tail = Compile.encodeRegs s ++ Compile.endMark :: residue
    rw [Compile.encodeTape, List.cons_append, List.tail_cons, List.append_assoc, List.cons_append,
        List.nil_append]
  rw [htail, Compile.takeWhile_no_endMark_append _ residue (Compile.encodeRegs_no_endMark s h),
      Compile.splitOnZero_encodeRegs, Compile.dropTrailingEmpty_append_nil,
      Compile.map_unshift_shift]

/-- After the leading sentinel, the encoded tape continues with `shiftReg`-ed
register `0`. When register `0` holds a single bit `b` (the decider answer
convention — `[1]` for accept, `[0]` for reject), the encoded tape is
`endMark :: (b + 1) :: …`. This is the only fact the tape→state bit-test gadget
needs about the encoding (it steps past the sentinel, then reads `b + 1`). -/
theorem Compile.encodeTape_eq_cons_of_get_zero (s : State) (b : Nat)
    (h : s.get 0 = [b]) :
    ∃ tl, Compile.encodeTape s = Compile.endMark :: (b + 1) :: tl := by
  cases s with
  | nil => simp [State.get] at h
  | cons r0 rest =>
      have hr0 : r0 = [b] := by simpa [State.get] using h
      refine ⟨[0] ++ Compile.encodeRegs rest ++ [Compile.endMark], ?_⟩
      show Compile.endMark :: (Compile.encodeRegs (r0 :: rest) ++ [Compile.endMark])
          = Compile.endMark :: (b + 1) :: ([0] ++ Compile.encodeRegs rest ++ [Compile.endMark])
      rw [Compile.encodeRegs_cons, hr0]
      simp [Compile.shiftReg]

/-! ## Cost / overhead

**Shape change vs. pre-decomposition skeleton.** The previous
`overhead : Nat → Nat` was applied to `State.size s`, the *input*
size. That bound is too loose, because during execution the tape
may grow by `+1` per `Cmd`-step (e.g. `appendOne`, `appendZero`).
After `cost c s` Cmd-steps the tape can have up to
`State.size s + cost c s` symbols, and the per-Cmd-step TM cost is
`O(tape length)`, so the cumulative TM cost is
`O((sizeIn + cost) * cost)`.

We now define `overhead` so that
`overhead (State.size s + cost c s)` upper-bounds the *total* TM-
step count for simulating `c` on `s`. The corollary
`Compile_polyBound` re-expresses this as a polynomial in input
size only, by composing with the caller-supplied `costBound`. -/

/-! ### (The old `Compile.overhead`/exact-tape lemma family is DELETED.)

The original decode-level obligations (`compileOp_sound`, `compileSeq_sound`,
`compileIfBit_sound`, `compileForBnd_sound`, `Compile_sound`, `Compile_polyBound`)
and the exact-tape physical family (`compileOp_sound_physical`,
`compileIfBit_sound_physical`, `compileForBnd_sound_physical`,
`Compile_run_physical`), together with their budget `Compile.overhead (m+1)²`,
were all **superseded by the residue-tolerant `physStepBudget` route**
(`Compile_run_physical_residue` + `paddedBitDecider_run`/`paddedCompute_run`) and
deleted 2026-06-11: the exact-tape contract is unsatisfiable for
length-decreasing ops (`clear_physical_unsatisfiable`) and the `overhead`
budget shape does not compose (ROADMAP Finding #3). Do not re-introduce. -/

/-! ### Encoding-seam helpers for the per-op soundness lemmas

The helpers below
(`encodeTape_split`, the `shiftReg`/`regBlocks` algebra, the `BitState`
preservation lemmas, and the `decodeTape`/`encodeTape` round trip) connect the
compiler's single-tape `encodeTape`/`decodeTape` contract to the proven gadget
library (`AppendGadget.appendAt_run_steps`, …). They feed the live per-op
soundness lemma `Compile.appendBit_sound` (general `dst`, linear step budget)
below, which discharges the behavioural + budget halves of `compileOp_sound`
for the two real ops `appendOne`/`appendZero`.

Note the **leading-sentinel encoding** (`encodeTape s = endMark :: encodeRegs s
++ [endMark]`): the gadget starts at head `0` on the sentinel, which
`appendBit_sound` folds into the first marker-free block so the scan still
begins at head `0` (no head-bridge needed). -/

theorem Compile.encodeRegs_append (a b : State) :
    Compile.encodeRegs (a ++ b)
      = Compile.encodeRegs a ++ Compile.encodeRegs b := by
  induction a with
  | nil => rfl
  | cons r a ih =>
      rw [List.cons_append, Compile.encodeRegs_cons, Compile.encodeRegs_cons, ih]
      simp [List.append_assoc]

theorem Compile.regBlocks_map_shiftReg (l : State) :
    AppendGadget.regBlocks (l.map Compile.shiftReg) = Compile.encodeRegs l := by
  induction l with
  | nil => rfl
  | cons r l ih =>
      rw [List.map_cons, AppendGadget.regBlocks_cons, Compile.encodeRegs_cons, ih]
      simp [List.append_assoc]

theorem Compile.shiftReg_append_one (l : List Nat) :
    Compile.shiftReg (l ++ [1]) = Compile.shiftReg l ++ [2] := by
  simp [Compile.shiftReg]

theorem Compile.shiftReg_append (l : List Nat) (b : Nat) :
    Compile.shiftReg (l ++ [b]) = Compile.shiftReg l ++ [b + 1] := by
  simp [Compile.shiftReg]

theorem Compile.list_set_eq_take_cons_drop {α : Type} :
    ∀ (l : List α) (i : Nat) (v : α), i < l.length →
      l.set i v = l.take i ++ v :: l.drop (i + 1)
  | _ :: _, 0, _, _ => by simp
  | a :: l, i + 1, v, h => by
      simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons,
        List.cons_append]
      rw [Compile.list_set_eq_take_cons_drop l i v (by simpa using h)]
  | [], _, _, h => by simp at h

theorem Compile.list_eq_take_getElem_drop {α : Type} :
    ∀ (l : List α) (i : Nat) (h : i < l.length),
      l = l.take i ++ l[i] :: l.drop (i + 1)
  | _ :: _, 0, _ => by simp
  | a :: l, i + 1, h => by
      simp only [List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ,
        List.cons_append]
      exact congrArg (a :: ·) (Compile.list_eq_take_getElem_drop l i (by simpa using h))
  | [], _, h => by simp at h

/-- The **registers part** of the encoded tape (i.e. `encodeTape s` with its
leading and trailing sentinels stripped — equivalently `encodeRegs s ++
[endMark]`) splits at register `dst` into the preceding register blocks, the
target register's shifted contents, its delimiter, and the rest — exactly the
shape `AppendGadget.appendAt_run` consumes (with empty prefix). The leading
sentinel of `encodeTape` is reattached by the caller (`appendBit_sound`). -/
theorem Compile.encodeTape_split (s : State) (dst : Var) (h : dst < s.length) :
    AppendGadget.regBlocks ((s.take dst).map Compile.shiftReg)
        ++ Compile.shiftReg (s.get dst)
        ++ 0 :: (Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark])
      = Compile.encodeRegs s ++ [Compile.endMark] := by
  have hget : s.get dst = s[dst] := by
    rw [State.get, List.getElem?_eq_getElem h]; rfl
  have hs : Compile.encodeRegs s
      = Compile.encodeRegs (s.take dst) ++ Compile.shiftReg s[dst]
          ++ [0] ++ Compile.encodeRegs (s.drop (dst + 1)) := by
    conv_lhs => rw [Compile.list_eq_take_getElem_drop s dst h]
    rw [Compile.encodeRegs_append, Compile.encodeRegs_cons]
    simp [List.append_assoc]
  rw [Compile.regBlocks_map_shiftReg, hget, hs]
  simp [List.append_assoc]

/-- **Master register-slot decomposition.** The encoded tape splits at register
`dst` into a prefix `pre`, that register's shifted content, its `0` delimiter, and
a suffix `rest` — and **`pre`/`rest` do not depend on the register's content**, so
writing any value `v` to register `dst` only swaps the middle block:
`encodeTape (s.set dst v) = pre ++ shiftReg v ++ 0 :: rest` for every `v`.
(`pre = endMark :: encodeRegs (s.take dst)`, `rest = encodeRegs (s.drop (dst+1)) ++
[endMark]`.) This is the workhorse every register-writing op uses: with `v = s.get
dst` it gives `encodeTape s` itself (`set` is the identity there), and varying `v`
gives the op's output tape with the same surrounding cells — so a gadget that edits
only the middle block discharges its `encodeTape`-level contract. -/
theorem Compile.encodeTape_reg_decomp (s : State) (dst : Var) (h : dst < s.length) :
    ∃ pre rest : List Nat,
      (∀ v : List Nat,
        Compile.encodeTape (s.set dst v) = pre ++ (Compile.shiftReg v ++ (0 :: rest))) ∧
      Compile.encodeTape s = pre ++ (Compile.shiftReg (s.get dst) ++ (0 :: rest)) := by
  refine ⟨Compile.endMark :: Compile.encodeRegs (s.take dst),
          Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark], ?_, ?_⟩
  · intro v
    have hset : s.set dst v = s.take dst ++ v :: s.drop (dst + 1) := by
      rw [State.set, if_pos h]; exact Compile.list_set_eq_take_cons_drop s dst v h
    have hs : Compile.encodeRegs (s.set dst v)
        = Compile.encodeRegs (s.take dst)
            ++ (Compile.shiftReg v ++ ([0] ++ Compile.encodeRegs (s.drop (dst + 1)))) := by
      rw [hset, Compile.encodeRegs_append, Compile.encodeRegs_cons]
      simp [List.append_assoc]
    rw [Compile.encodeTape, hs]
    simp [List.append_assoc]
  · have hget : s.get dst = s[dst] := by
      rw [State.get, List.getElem?_eq_getElem h]; rfl
    have hs : Compile.encodeRegs s
        = Compile.encodeRegs (s.take dst)
            ++ (Compile.shiftReg (s.get dst)
                ++ ([0] ++ Compile.encodeRegs (s.drop (dst + 1)))) := by
      conv_lhs => rw [Compile.list_eq_take_getElem_drop s dst h]
      rw [Compile.encodeRegs_append, Compile.encodeRegs_cons, ← hget]
      simp [List.append_assoc]
    rw [Compile.encodeTape, hs]
    simp [List.append_assoc]

/-- **Spec bridge for `clear` (the deletion gadget's input/output contract).**
Specialises `encodeTape_reg_decomp`: clearing register `dst` removes exactly the
contiguous `shiftReg (s.get dst)` block before that register's `0` delimiter. With
any incoming residue `res_in`:

1. the gadget's **input** tape `encodeTape s ++ res_in` is
   `pre ++ shiftReg (s.get dst) ++ (0 :: rest ++ res_in)` — block to delete is
   `shiftReg (s.get dst)`, of length `|s.get dst|` (conjunct 3); and
2. after deleting those `|s.get dst|` cells (each `deleteCarryTM` pushes one `0`
   filler to the far end), the tape is
   `encodeTape (Op.eval (clear dst) s) ++ (res_in ++ replicate |s.get dst| 0)`.

So `res_out = res_in ++ replicate |old| 0` (`ValidResidue` by
`ValidResidue_append_replicate_zero`); the freed cells become terminator-free `0`
residue past the real terminator, so the **two-phase rewind** applies. -/
theorem Compile.clear_block_decomp (s : State) (dst : Var) (res_in : List Nat)
    (h : dst < s.length) :
    ∃ pre rest : List Nat,
      Compile.encodeTape s ++ res_in
          = pre ++ (Compile.shiftReg (s.get dst) ++ (0 :: rest ++ res_in)) ∧
      pre ++ ((0 :: rest ++ res_in) ++ List.replicate (s.get dst).length 0)
          = Compile.encodeTape (Op.eval (Op.clear dst) s)
              ++ (res_in ++ List.replicate (s.get dst).length 0) ∧
      (Compile.shiftReg (s.get dst)).length = (s.get dst).length := by
  obtain ⟨pre, rest, hv, hs⟩ := Compile.encodeTape_reg_decomp s dst h
  refine ⟨pre, rest, ?_, ?_, ?_⟩
  · rw [hs]; simp [List.append_assoc]
  · -- `Op.eval (clear dst) s = s.set dst []`, and `shiftReg [] = []`.
    have hcl : Compile.encodeTape (Op.eval (Op.clear dst) s) = pre ++ (0 :: rest) := by
      show Compile.encodeTape (s.set dst []) = _
      rw [hv []]; simp [Compile.shiftReg]
    rw [hcl]; simp [List.append_assoc]
  · rw [Compile.shiftReg, List.length_map]

/-- **One `deleteCarryTM` pass deletes the head of a marker-free block.** From the
read state at head `pre.length + 1` on `pre ++ (c0+1) :: M` (a nonempty,
in-range `M`), after `3·|M| + 1` steps the machine halts having deleted the cell
`c0+1` and shifted `M` left by one with a `0` filler: tape `pre ++ M ++ [0]`. The
degenerate-suffix branch of `deleteCarryTM_loop_run` is ruled out by `M ≠ []`. -/
theorem Compile.deleteCarry_drop_head (pre M : List Nat) (c0 : Nat)
    (hc0 : c0 + 1 < 4) (hM : M ≠ []) (hMb : ∀ x ∈ M, x < 4) :
    runFlatTM (3 * M.length + 1) Complexity.Lang.ShiftTape.deleteCarryTM
        { state_idx := 0, tapes := [([], pre.length + 1, pre ++ (c0 + 1) :: M)] }
      = some { state_idx := 6,
               tapes := [([], pre.length + 1 + M.length, pre ++ M ++ [0])] } := by
  have h := Complexity.Lang.ShiftTape.deleteCarryTM_loop_run M pre (c0 + 1) hc0 hMb
  rw [if_neg hM, ← List.append_assoc] at h
  exact h

/-- `appendOne` preserves bit-shape (it appends the bit `1`). -/
theorem Compile.BitState_appendOne (s : State) (dst : Var)
    (h : Compile.BitState s) (hdst : dst < s.length) :
    Compile.BitState (Op.eval (Op.appendOne dst) s) := by
  show Compile.BitState (s.set dst (s.get dst ++ [1]))
  rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst]
  intro reg hreg x hx
  simp only [List.mem_append, List.mem_cons] at hreg
  rcases hreg with hr | hr | hr
  · exact h reg (List.mem_of_mem_take hr) x hx
  · subst hr
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have hmem : s.get dst ∈ s := by
        rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
      exact h _ hmem x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega
  · exact h reg (List.mem_of_mem_drop hr) x hx

/-- Appending any bit `b ≤ 1` to register `dst` preserves bit-shape. The
general form of `BitState_appendOne` covering both `appendOne` (`b = 1`) and
`appendZero` (`b = 0`). -/
theorem Compile.BitState_appendBit (b : Nat) (hb : b ≤ 1) (s : State)
    (dst : Var) (h : Compile.BitState s) (hdst : dst < s.length) :
    Compile.BitState (s.set dst (s.get dst ++ [b])) := by
  rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst]
  intro reg hreg x hx
  simp only [List.mem_append, List.mem_cons] at hreg
  rcases hreg with hr | hr | hr
  · exact h reg (List.mem_of_mem_take hr) x hx
  · subst hr
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have hmem : s.get dst ∈ s := by
        rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
      exact h _ hmem x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega
  · exact h reg (List.mem_of_mem_drop hr) x hx

/-- Every symbol of `encodeRegs t` is `< 4` when `t` is bit-shaped (shifted
bits are `1`/`2`, delimiters are `0`). -/
theorem Compile.encodeRegs_lt_four (t : State)
    (h : ∀ b ∈ t, ∀ x ∈ b, x ≤ 1) : ∀ y ∈ Compile.encodeRegs t, y < 4 := by
  induction t with
  | nil => intro y hy; simp [Compile.encodeRegs] at hy
  | cons r t ih =>
      intro y hy
      rw [Compile.encodeRegs_cons, List.mem_append, List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · rw [Compile.shiftReg, List.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        have := h r (List.mem_cons_self ..) z hz; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega
      · exact ih (fun b hb x hx => h b (List.mem_cons_of_mem _ hb) x hx) y hy

/-- `decodeTape` ignores the state index, head position and `left` track, so
the round-trip `decodeTape ∘ encodeTape = id` holds at any halting config. -/
theorem Compile.decodeTape_encodeTape' (q hd : Nat) (t : State)
    (h : Compile.BitState t) :
    Compile.decodeTape { state_idx := q, tapes := [([], hd, Compile.encodeTape t)] } = t :=
  Compile.decodeTape_encodeTape t h

/-! ### Structure of `encodeTape` (for the rewind side-conditions, step 1b-2)

The `appendAt_rewind_run` bracket needs three facts about the gadget's *exit*
tape (which is `encodeTape output`): its cell `0` is the leading sentinel `3`,
every cell is `< 4`, and the interior (everything but the trailing terminator)
is sentinel-free. -/

/-- Cell `0` of any `encodeTape` is the leading sentinel `endMark = 3`. -/
theorem Compile.encodeTape_get_zero (t : State)
    (h : 0 < (Compile.encodeTape t).length) :
    (Compile.encodeTape t).get ⟨0, h⟩ = 3 := rfl

/-- The **trailing terminator**: the last cell of `encodeTape t` is the `endMark`
`3`. This pins the real-terminator position for the residue-tolerant two-phase
rewind (`p = (encodeTape output).length - 1`). -/
theorem Compile.encodeTape_get_last (t : State)
    (h : (Compile.encodeTape t).length - 1 < (Compile.encodeTape t).length) :
    (Compile.encodeTape t).get ⟨(Compile.encodeTape t).length - 1, h⟩ = 3 := by
  rw [List.get_eq_getElem]
  -- Work at the proof-free `getElem?` level to avoid a dependent-index rewrite.
  have key : (Compile.encodeTape t)[(Compile.encodeTape t).length - 1]? = some 3 := by
    rw [Compile.encodeTape]
    rw [show (Compile.endMark :: (Compile.encodeRegs t ++ [Compile.endMark])).length - 1
          = (Compile.encodeRegs t).length + 1 by
        simp only [List.length_cons, List.length_append, List.length_nil]; omega]
    rw [List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _)]
    simp [Compile.endMark]
  exact (Option.some.inj (key.symm.trans (List.getElem?_eq_getElem h))).symm

/-- Every symbol of `encodeTape t` is `< 4` for a bit-shaped `t`. -/
theorem Compile.encodeTape_lt_four (t : State) (h : Compile.BitState t) :
    ∀ x ∈ Compile.encodeTape t, x < 4 := by
  intro x hx
  rw [Compile.encodeTape, List.mem_cons, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx | hx
  · subst hx; decide
  · exact Compile.encodeRegs_lt_four t h x hx
  · subst hx; decide

/-- Every interior cell of `encodeTape t` (i.e. every cell *except* the trailing
terminator) is `≠ endMark = 3`: cell `0` is the leading sentinel `3` but cell
`i ≥ 1` with `i + 1 < length` lands inside `encodeRegs t`, which is
sentinel-free. The leading sentinel at `0` is the rewind *target*, so the
interior-non-sentinel claim is restricted to `0 < i`. -/
theorem Compile.encodeTape_interior_ne_endMark (t : State) (h : Compile.BitState t) :
    ∀ i, 0 < i → i + 1 < (Compile.encodeTape t).length →
      ∃ (hi : i < (Compile.encodeTape t).length),
        (Compile.encodeTape t).get ⟨i, hi⟩ ≠ 3 := by
  intro i hi_pos hi_lt
  refine ⟨by omega, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  -- encodeTape t = 3 :: (encodeRegs t ++ [3]); cell j+1 = (encodeRegs t ++ [3])[j].
  have hlen : (Compile.encodeTape t).length = (Compile.encodeRegs t).length + 2 := by
    rw [Compile.encodeTape]; simp [List.length_append]
  have hj : j < (Compile.encodeRegs t).length := by omega
  simp only [List.get_eq_getElem, Compile.encodeTape, List.getElem_cons_succ]
  rw [List.getElem_append_left hj]
  exact Compile.encodeRegs_no_endMark t h _ (List.getElem_mem hj)

