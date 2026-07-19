import Complexity.Complexity.MachineSemantics
import Complexity.Lang.Compile.Encoding

set_option autoImplicit false

/-! # The chain-head input layout — FROZEN (2026-07-18)

The **input layout of the S1 free witness** (`FlatSingleTMGenNP → FlatTCC`,
the head of the honest reduction chain) and, equally, the **exit layout the
C8-5 per-`Q` front seam must hit** (`SeamData W_Q W_head`). Pinned as a
candidate by `probes/C8SeamProbe.lean` (2026-07-04, seam-targeting probed
GO) and frozen here per standing architecture risk #2 (seam discipline:
each witness's input layout is its predecessor's exit frame, documented for
both sides).

Layout (`headRegBound = 5`):

| reg | content |
|-----|---------|
| 0   | `[]` (output scratch — the emitted `FlatTCC` instance goes here) |
| 1   | the machine, `encSyms (flattenTM M)` — sentinel bit-stream |
| 2   | the input string, `encSyms s` |
| 3   | `maxSize` unary (`replicate maxSize 1`) |
| 4   | `steps` unary (`replicate steps 1`) |

Scratch registers of either witness live strictly `≥ headRegBound`.
`headEncodeIn_bitState` certifies the layout bit-level — it IS the future
S1 witness's `enc_bit` field, and the C8-4 front program's emit obligation.

**Do not change any definition in this file without re-running
`probes/C8SeamProbe.lean` and updating both the S1 and C8 build plans**
(HANDOFF: this is the S1↔C8 interface). -/

namespace HeadLayout

open Complexity.Lang

/-- Canonical flat code of a move (only used inside `flattenTM`). -/
def encMoveN : TMMove → Nat
  | .Lmove => 0
  | .Rmove => 1
  | .Nmove => 2

/-- Canonical flat code of an optional symbol. -/
def encOptN : Option Nat → List Nat
  | none => [0]
  | some v => [1, v]

/-- Canonical `Nat`-stream flattening of a transition entry. -/
def flattenEntry (e : FlatTMTransEntry) : List Nat :=
  [e.src_state, e.src_tape_vals.length]
    ++ e.src_tape_vals.foldl (fun a o => a ++ encOptN o) []
    ++ [e.dst_state, e.dst_write_vals.length]
    ++ e.dst_write_vals.foldl (fun a o => a ++ encOptN o) []
    ++ [e.move_dirs.length] ++ e.move_dirs.map encMoveN

/-- Canonical `Nat`-stream flattening of a `FlatTM`. The machine register
of the head layout carries `encSyms (flattenTM M)`. -/
def flattenTM (M : FlatTM) : List Nat :=
  [M.sig, M.tapes, M.states, M.start, M.halt.length]
    ++ M.halt.map (fun b => if b then 1 else 0)
    ++ [M.trans.length]
    ++ M.trans.foldl (fun a e => a ++ flattenEntry e) []

/-- Sentinel item view of a `Nat` stream: each value `v` becomes
`1 1^v 0` — the project's standard bit-level prefix-decodable item
encoding. -/
def encSyms (l : List Nat) : List Nat :=
  l.foldl (fun a v => a ++ 1 :: (List.replicate v 1 ++ [0])) []

/-- The head frame: registers `< headRegBound` are the interface, scratch
lives at `≥ headRegBound`. -/
def headRegBound : Nat := 5

/-- **The frozen chain-head input layout** (see the module docstring). -/
def headEncodeIn : FlatTM × List Nat × Nat × Nat → State :=
  fun (M, s, maxSize, steps) =>
    [[], encSyms (flattenTM M), encSyms s,
     List.replicate maxSize 1, List.replicate steps 1]

/-- `encSyms` unrolls one item at the right end — the incremental-emission
step every `encSyms`-producing loop invariant closes with. -/
theorem encSyms_snoc (l : List Nat) (v : Nat) :
    encSyms (l ++ [v]) = encSyms l ++ 1 :: (List.replicate v 1 ++ [0]) := by
  unfold encSyms
  rw [List.foldl_append]
  rfl

/-- A `foldl` that only appends to its accumulator factors the accumulator out
of the front — the algebraic core of `encSyms_append`. -/
private theorem foldl_append_acc (g : Nat → List Nat) (m : List Nat) :
    ∀ acc : List Nat,
      m.foldl (fun a v => a ++ g v) acc = acc ++ m.foldl (fun a v => a ++ g v) [] := by
  induction m with
  | nil => intro acc; simp
  | cons v vs ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih (acc ++ g v), ih ([] ++ g v),
        List.nil_append, List.append_assoc]

/-- `encSyms` is a monoid homomorphism: it distributes over `++`. Every
per-register/per-symbol emitter closes its `encSyms`-shaped goal with this. -/
theorem encSyms_append (l m : List Nat) :
    encSyms (l ++ m) = encSyms l ++ encSyms m := by
  unfold encSyms
  rw [List.foldl_append, foldl_append_acc]

private theorem encSyms_go (l : List Nat) (a : List Nat) (ha : ∀ x ∈ a, x ≤ 1) :
    ∀ x ∈ l.foldl (fun a v => a ++ 1 :: (List.replicate v 1 ++ [0])) a, x ≤ 1 := by
  induction l generalizing a with
  | nil => exact ha
  | cons v vs ih =>
    intro x hx
    refine ih _ ?_ x hx
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact ha y hy
    · rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · rcases List.mem_append.1 hy with hy | hy
        · have := List.eq_of_mem_replicate hy; omega
        · have := List.mem_singleton.1 hy; omega

/-- The sentinel item stream is bit-level. -/
theorem encSyms_bit (l : List Nat) : ∀ x ∈ encSyms l, x ≤ 1 :=
  encSyms_go l [] (by intro x hx; cases hx)

/-- The frozen layout is bit-level — the S1 witness's future `enc_bit`
field, and the bound every C8-4 front emitter must respect. -/
theorem headEncodeIn_bitState (inst : FlatTM × List Nat × Nat × Nat) :
    Compile.BitState (headEncodeIn inst) := by
  obtain ⟨M, s, maxSize, steps⟩ := inst
  intro reg hreg x hx
  simp only [headEncodeIn, List.mem_cons, List.not_mem_nil, or_false] at hreg
  rcases hreg with rfl | rfl | rfl | rfl | rfl
  · cases hx
  · exact encSyms_bit _ x hx
  · exact encSyms_bit _ x hx
  · have := List.eq_of_mem_replicate hx; omega
  · have := List.eq_of_mem_replicate hx; omega

end HeadLayout
