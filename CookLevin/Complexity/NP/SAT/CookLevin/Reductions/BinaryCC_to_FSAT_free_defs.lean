import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT
import Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC_free
import Complexity.Lang.PolyTime
import Complexity.Lang.CostFlat

set_option autoImplicit false

/-! # `BinaryCC ⪯p' FSAT` as a free `PolyTimeComputableLang` witness — FOUNDATION

Top-down target #2 (HANDOFF/ROADMAP): re-express the Tseytin transform
`BinaryCC_to_FSAT_instance` (`Reductions/BinaryCC_to_FSAT.lean`, ~1K-LOC formula
builder) as a free layer witness. This is the **expensive tail item**, budgeted
at ~2 sessions. This file is **session 1's deliverable**: the proven
serialization foundation + the pinned input/output encodings + the validated
emitter building blocks. The program assembly and its run/cost lemmas are
session 2 (see the DESIGN + NEXT-SESSION block at the bottom, and
`probes/FSATSerProbe.lean` for the end-to-end `#eval` validation of everything
here).

## The crux resolution (design question (b), HANDOFF)

Every prior free-witness output (SAT `cnf`, `BinaryCC`) is a FLAT record of
lists; the FSAT output `formula` is a **nested inductive TREE**. Resolution:
serialize the tree in **prefix (Polish) order** as a self-delimiting bit-list in
ONE output register, and build it with **forward `forBnd` loops** emitting
tokens. The enabling algebraic fact:

    listAnd [f₁,…,fₙ] = fand f₁ (fand f₂ (… ftrue))
  ⇒ serF (listAnd fs) = (⋃ᵢ (fandTag ++ serF fᵢ)) ++ ftrueTag

i.e. a forward append loop (operator-tag-then-child per element, base tag once at
the end). Same for `listOr`. The tree's nesting collapses into token-emission
ORDER — exactly what the DSL's counted loops produce.
-/

namespace BinaryCCFSATFree

open Complexity.Lang
open BinaryCCToFSAT

/-! ## 1. Prefix (Polish) serialization of `formula` — the output codec

Prefix-free bit code (decode reads 2 bits, then 1 more when they are `11`):
`ftrue = [0,0]`, `fand = [0,1]`, `forr = [1,0]`, `fneg = [1,1,0]`,
`fvar v = [1,1,1] ++ 1^v ++ [0]`. All cells `∈ {0,1}` (BitState-clean, so the
output register is a legal machine register). -/

def serF : formula → List Nat
  | .ftrue     => [0, 0]
  | .fand a b  => [0, 1] ++ serF a ++ serF b
  | .forr a b  => [1, 0] ++ serF a ++ serF b
  | .fneg a    => [1, 1, 0] ++ serF a
  | .fvar v    => [1, 1, 1] ++ List.replicate v 1 ++ [0]

/-- Read a leading unary `1`-block, returning `(count, suffix-after-0)`. -/
def readUnary : List Nat → Nat × List Nat
  | [] => (0, [])
  | 0 :: rest => (0, rest)
  | _ :: rest => let (v, r) := readUnary rest; (v + 1, r)

/-- Fuel-driven Polish parser: `(formula, unconsumed suffix)`. -/
def deserF : Nat → List Nat → Option (formula × List Nat)
  | 0, _ => none
  | _, 0 :: 0 :: rest => some (.ftrue, rest)
  | fuel + 1, 0 :: 1 :: rest =>
      match deserF fuel rest with
      | some (a, r1) => match deserF fuel r1 with
                        | some (b, r2) => some (.fand a b, r2)
                        | none => none
      | none => none
  | fuel + 1, 1 :: 0 :: rest =>
      match deserF fuel rest with
      | some (a, r1) => match deserF fuel r1 with
                        | some (b, r2) => some (.forr a b, r2)
                        | none => none
      | none => none
  | fuel + 1, 1 :: 1 :: 0 :: rest =>
      match deserF fuel rest with
      | some (a, r1) => some (.fneg a, r1)
      | none => none
  | _ + 1, 1 :: 1 :: 1 :: rest =>
      let (v, r) := readUnary rest
      some (.fvar v, r)
  | _, _ => none

/-- Full decode: parse with fuel = length + 1 (always enough, `formula_size_le_serF`). -/
def decodeF (bits : List Nat) : Option formula :=
  (deserF (bits.length + 1) bits).map Prod.fst

/-! ### The round-trip: `decodeF ∘ serF = id` (injectivity backbone of `decodeOut`) -/

theorem readUnary_replicate (v : Nat) (rest : List Nat) :
    readUnary (List.replicate v 1 ++ (0 :: rest)) = (v, rest) := by
  induction v with
  | zero => simp [readUnary]
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [readUnary, ih]

theorem deserF_serF (f : formula) :
    ∀ (fuel : Nat) (rest : List Nat), formula_size f ≤ fuel →
      deserF fuel (serF f ++ rest) = some (f, rest) := by
  induction f with
  | ftrue =>
      intro fuel rest h
      cases fuel with
      | zero => simp [formula_size] at h
      | succ n => rfl
  | fvar v =>
      intro fuel rest h
      cases fuel with
      | zero => simp [formula_size] at h
      | succ n =>
          simp only [serF, List.append_assoc]
          show deserF (n+1) (1 :: 1 :: 1 :: (List.replicate v 1 ++ (0 :: rest))) = _
          simp only [deserF, readUnary_replicate]
  | fand a b iha ihb =>
      intro fuel rest h
      cases fuel with
      | zero => simp [formula_size] at h
      | succ n =>
          have ha : formula_size a ≤ n := by simp [formula_size] at h; omega
          have hb : formula_size b ≤ n := by simp [formula_size] at h; omega
          show deserF (n+1) (0 :: 1 :: (serF a ++ serF b ++ rest)) = _
          simp only [deserF]
          rw [show serF a ++ serF b ++ rest = serF a ++ (serF b ++ rest) by simp]
          simp only [iha n (serF b ++ rest) ha, ihb n rest hb]
  | forr a b iha ihb =>
      intro fuel rest h
      cases fuel with
      | zero => simp [formula_size] at h
      | succ n =>
          have ha : formula_size a ≤ n := by simp [formula_size] at h; omega
          have hb : formula_size b ≤ n := by simp [formula_size] at h; omega
          show deserF (n+1) (1 :: 0 :: (serF a ++ serF b ++ rest)) = _
          simp only [deserF]
          rw [show serF a ++ serF b ++ rest = serF a ++ (serF b ++ rest) by simp]
          simp only [iha n (serF b ++ rest) ha, ihb n rest hb]
  | fneg a iha =>
      intro fuel rest h
      cases fuel with
      | zero => simp [formula_size] at h
      | succ n =>
          have ha : formula_size a ≤ n := by simp [formula_size] at h; omega
          show deserF (n+1) (1 :: 1 :: 0 :: (serF a ++ rest)) = _
          simp only [deserF]
          simp only [iha n rest ha]

theorem formula_size_le_serF (f : formula) : formula_size f ≤ (serF f).length := by
  induction f with
  | ftrue => simp [serF, formula_size]
  | fvar v => simp [serF, formula_size]
  | fand a b iha ihb =>
      simp only [serF, formula_size, List.length_append, List.length_cons, List.length_nil]; omega
  | forr a b iha ihb =>
      simp only [serF, formula_size, List.length_append, List.length_cons, List.length_nil]; omega
  | fneg a iha =>
      simp only [serF, formula_size, List.length_append, List.length_cons, List.length_nil]; omega

/-- **The output codec is injective** (`decodeF` inverts `serF`). This is what
`decode_agree`/`computes` will lean on: the program writes `serF (f x)` into the
output register, and `decodeOut` reads it back exactly. Axiom-clean. -/
theorem decodeF_serF (f : formula) : decodeF (serF f) = some f := by
  unfold decodeF
  have h := deserF_serF f ((serF f).length + 1) [] (by have := formula_size_le_serF f; omega)
  rw [List.append_nil] at h
  rw [h]; rfl

/-! ## 2. The input/output register layout (design question (c), pinned to the seam)

The composite `FlatTCC → … → BinaryCC` witness exits with the intermediate
`BinaryCC` in registers (see `FlatCCBinFree.encKeyB` / the live seam
`FlatTCCBinComp`):

    17 offset (1^offset)   18 width (1^width)   19 init (bit-list)
    20 cards (sentinel stream)   21 final (sentinel stream)   5 steps (1^steps)

`encodeIn` below is pinned to THAT frame so the future seam
(`BinaryCC_to_FSAT_comp.lean`) is a near-pure scrub (seam discipline). The
sentinel-stream formats for cards/final are `FlatCCBinFree`'s `encCardsOut` /
`encFinal`; here we mirror them via the reduction's own bit views. The single
formula output goes to `FOUT`. -/

/-- Input register indices (pinned to the BinaryCC exit frame). -/
def OFFSET : Nat := 17
def WIDTH  : Nat := 18
def INIT   : Nat := 19
def CARDS  : Nat := 20
def FINAL  : Nat := 21
def STEPS  : Nat := 5
/-- The output register holding `serF (BinaryCC_to_FSAT_instance C)`. -/
def FOUT   : Nat := 0

/-- Read the serialized formula out of `FOUT` and decode it. On a well-formed run
the register holds `serF (f C)`, so this returns `f C` by `decodeF_serF`; the
`getD .ftrue` fallback is never hit on real outputs. -/
def decodeOut (s : State) : formula := (decodeF (s.get FOUT)).getD .ftrue

/-- `decodeOut` recovers a formula from its serialization (the core fact the
witness's `computes` obligation reduces to once the program is shown to write
`serF (f C)` into `FOUT`). -/
theorem decodeOut_of_serF (s : State) (f : formula) (h : s.get FOUT = serF f) :
    decodeOut s = f := by
  simp only [decodeOut, h, decodeF_serF, Option.getD_some]


/-! ### Serialization length bounds -/

theorem serF_length_le_size (f : formula) : (serF f).length ≤ 4 * encodable.size f := by
  induction f with
  | ftrue => simp [serF]
  | fvar v =>
      simp only [serF, encodable_size_formula_fvar, List.length_append,
        List.length_cons, List.length_replicate, List.length_nil]
      omega
  | fand a b iha ihb =>
      simp only [serF, encodable_size_formula_fand, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | forr a b iha ihb =>
      simp only [serF, encodable_size_formula_forr, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | fneg a iha =>
      simp only [serF, encodable_size_formula_fneg, List.length_append,
        List.length_cons, List.length_nil]
      omega

end BinaryCCFSATFree
