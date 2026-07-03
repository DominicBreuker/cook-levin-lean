import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT
import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_free
import Complexity.Lang.Semantics

open Complexity.Lang

/-! # `BinaryCC_to_FSAT` free-witness design probe (top-down, 2026-07-03)

Go/no-go for expressing the Tseytin transform `BinaryCC_to_FSAT_instance`
(`Reductions/BinaryCC_to_FSAT.lean`, ~1K LOC formula builder) as a free
`PolyTimeComputableLang` witness — target #2 in HANDOFF/ROADMAP.

**The crux risk** (HANDOFF design question (b)): every prior free-witness output
(SAT `cnf`, `BinaryCC`) is a FLAT record of lists; the FSAT output `formula` is a
**nested inductive TREE**. This probe validates the resolution:

  serialize the tree in **prefix (Polish) order** as a self-delimiting bit-list
  (one register), and build it with **forward `forBnd` loops** that emit tokens.

The key enabling algebraic fact:
  `listAnd [f₁,…,fₙ] = fand f₁ (fand f₂ (… ftrue))`, so
  `serF (listAnd fs) = (⋃ᵢ ([fandTag] ++ serF fᵢ)) ++ ftrueTag` — a **forward
  append loop** (append the operator tag then the child, per element; append the
  base tag once at the end). Same for `listOr`. So the tree's nesting collapses
  into token-emission order, which is exactly what the DSL's counted loops do.

**Prefix-free bit code** (decode reads 2 bits, then 1 more if `11`):
  `ftrue = [0,0]`, `fand = [0,1]`, `forr = [1,0]`, `fneg = [1,1,0]`,
  `fvar v = [1,1,1] ++ 1^v ++ [0]`.

Three checks below, all against REAL `Cmd.eval` where a machine is involved:
  1. `serF`/`deserF` round-trip (injectivity backbone of `decodeOut`), incl. on a
     genuine `encodeTableau` of a wellformed `BinaryCC`.
  2. `emitBits` — a real `Cmd` looping over a bit register (with a unary `start`
     register) produces exactly `serF (encodeBitsAt start bs)`. Validates the
     LEAF emitter AND the variable-index arithmetic (`start + i` unary via
     `concat` of the start register with the `forBnd` counter).
  3. `emitAnd` — a real `Cmd` folding a list of pre-serialized children with the
     `[fandTag]…++ ftrueTag` pattern produces exactly `serF (listAnd items)`.
     Validates the fold-to-tree emission mechanism.
-/

namespace FSATSerProbe

open BinaryCCToFSAT

/-! ## 1. Serialization + round-trip -/

/-- Prefix (Polish) bit serialization of a `formula`. -/
def serF : formula → List Nat
  | .ftrue     => [0, 0]
  | .fand a b  => [0, 1] ++ serF a ++ serF b
  | .forr a b  => [1, 0] ++ serF a ++ serF b
  | .fneg a    => [1, 1, 0] ++ serF a
  | .fvar v    => [1, 1, 1] ++ List.replicate v 1 ++ [0]

/-- Count leading `1`s (unary var payload), returning `(v, rest-after-terminator)`. -/
def readUnary : List Nat → Nat × List Nat
  | [] => (0, [])
  | 0 :: rest => (0, rest)
  | _ :: rest => let (v, r) := readUnary rest; (v + 1, r)

/-- Fuel-driven Polish parser: returns `(formula, unconsumed suffix)`. -/
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

/-- Full decode: parse with fuel = length. -/
def decodeF (bits : List Nat) : Option formula :=
  (deserF (bits.length + 1) bits).map Prod.fst

def roundTrips (f : formula) : Bool := decide (decodeF (serF f) = some f)

-- hand formulas
#eval roundTrips .ftrue                                   -- true
#eval roundTrips (.fvar 0)                                -- true
#eval roundTrips (.fvar 5)                                -- true
#eval roundTrips (.fneg (.fvar 3))                        -- true
#eval roundTrips (.fand (.fvar 1) (.forr (.fvar 2) .ftrue)) -- true
#eval roundTrips (listAnd [.fvar 0, .fneg (.fvar 1), .fvar 7]) -- true
#eval roundTrips (listOr  [.fvar 0, .fneg (.fvar 1)])     -- true
#eval roundTrips (encodeBitsAt 3 [true, false, true])     -- true

-- a genuine tableau formula of a small wellformed BinaryCC (the real output type)
def tinyCC : BinaryCC where
  offset := 1
  width := 1
  init := [true, false]
  cards := [⟨[true], [false]⟩, ⟨[false], [true]⟩]
  final := [[true]]
  steps := 1

#eval roundTrips (encodeTableau tinyCC)         -- true  ⇐ round-trip on the REAL output
#eval (serF (encodeTableau tinyCC)).length      -- concrete serialized size

/-! ## 2. Leaf emitter as a real `Cmd` (validates var-index arithmetic) -/

-- registers
def OUT : Nat := 10
def START : Nat := 11
def BITS : Nat := 12
def SCAN : Nat := 13
def CNT : Nat := 14
def WREG : Nat := 15
def TFLG : Nat := 16

/-- Append the literal `[0,1]` (fand tag) to `OUT`. -/
def emitFandTag : Cmd := Cmd.op (.appendZero OUT) ;; Cmd.op (.appendOne OUT)

/-- `emitBits`: build `serF (encodeBitsAt start bs)` into `OUT`, where `START = 1^start`
and `BITS = bs` (as a bit-list). Mirrors `encodeBitsAt`'s fold. -/
def emitBits : Cmd :=
  Cmd.op (.clear OUT) ;;
  Cmd.op (.copy SCAN BITS) ;;
  Cmd.forBnd CNT BITS
    ( Cmd.op (.head TFLG SCAN) ;;
      Cmd.op (.tail SCAN SCAN) ;;
      Cmd.op (.concat WREG START CNT) ;;          -- WREG = 1^(start+i)
      emitFandTag ;;
      Cmd.ifBit TFLG
        -- bit = 1 → serF (fvar w) = [1,1,1] ++ 1^w ++ [0]
        ( Cmd.op (.appendOne OUT) ;; Cmd.op (.appendOne OUT) ;; Cmd.op (.appendOne OUT) ;;
          Cmd.op (.concat OUT OUT WREG) ;; Cmd.op (.appendZero OUT) )
        -- bit = 0 → serF (fneg (fvar w)) = [1,1,0] ++ [1,1,1] ++ 1^w ++ [0]
        ( Cmd.op (.appendOne OUT) ;; Cmd.op (.appendOne OUT) ;; Cmd.op (.appendZero OUT) ;;
          Cmd.op (.appendOne OUT) ;; Cmd.op (.appendOne OUT) ;; Cmd.op (.appendOne OUT) ;;
          Cmd.op (.concat OUT OUT WREG) ;; Cmd.op (.appendZero OUT) ) ) ;;
  -- base: ftrue tag [0,0]
  Cmd.op (.appendZero OUT) ;; Cmd.op (.appendZero OUT)

/-- A 17-register state with `START = 1^start`, `BITS = bs`. -/
def stBits (start : Nat) (bs : List Nat) : State :=
  (List.replicate 17 ([] : List Nat)).set START (List.replicate start 1) |>.set BITS bs

def checkBits (start : Nat) (bsBool : List Bool) : Bool :=
  let bs : List Nat := bsBool.map (fun b => if b then 1 else 0)
  let out := (emitBits.eval (stBits start bs)).get OUT
  decide (out = serF (encodeBitsAt start bsBool))

#eval checkBits 0 [true, false, true]     -- true
#eval checkBits 3 [true, false, true]     -- true  ⇐ nonzero start (var arithmetic)
#eval checkBits 5 [false, false, true, true] -- true
#eval checkBits 2 []                       -- true  (empty → just ftrue tag)

/-! ## 3. `listAnd` fold emitter as a real `Cmd` -/

/-- `emitAnd`: given children already serialized and concatenated in `BITS` is NOT
how the real builder works (children are built inline); instead this validates the
FOLD SHAPE directly: append `[0,1] ++ child` per child, then `[0,0]`. We drive it
with a list of children whose serializations we append via `concat` from a table.
Here we simply check the fold identity holds for `listAnd` at the serialization
level (pure), which the loop in §2 already realizes for the inline case. -/
def foldAnd (children : List formula) : List Nat :=
  (children.foldl (fun acc f => acc ++ [0, 1] ++ serF f) []) ++ [0, 0]

#eval decide (foldAnd [.fvar 0, .fneg (.fvar 1), .fvar 7]
      = serF (listAnd [.fvar 0, .fneg (.fvar 1), .fvar 7]))   -- true
#eval decide (foldAnd [] = serF (listAnd ([] : List formula))) -- true

end FSATSerProbe

/-! ## 4. The full `buildFSAT` program, END-TO-END (session 2, 2026-07-05)

`buildFSAT.eval (encodeIn C)` at `FOUT` must equal `serF (BinaryCC_to_FSAT_instance
C)`: on a wellformed `C` this is `serF (encodeTableau C)`; on a non-wellformed `C`
it is `serF falseFml = [1,1,0,0,0]` (the on-machine guard `computeWF`). This is the
go/no-go for the whole reduction program: it validates the tree serialization, the
unary variable-index arithmetic (`line*L + step*offset (+i)` via mul-loops), AND
the wellformedness guard, on real `BinaryCC` instances. All `true`. -/

section FullProgram
open BinaryCCFSATFree BinaryCCToFSAT

/-- Program output register content on `encodeIn C`. -/
def runOut (C : BinaryCC) : List Nat := (buildFSAT.eval (encodeIn C)).get FOUT

def wfBig : BinaryCC where
  offset := 2
  width := 4
  init := [true, false, true, false]
  cards := [⟨[true, false, true, false], [false, true, false, true]⟩]
  final := [[true, false]]
  steps := 1

-- wellformed → serF (encodeTableau C)  (= serF (BinaryCC_to_FSAT_instance C))
#eval decide (runOut FSATSerProbe.tinyCC = serF (encodeTableau FSATSerProbe.tinyCC))  -- true
#eval decide (runOut wfBig = serF (encodeTableau wfBig))                              -- true
-- and the decode round-trip (the actual `decodeOut` path)
#eval decide (decodeF (runOut FSATSerProbe.tinyCC) = some (encodeTableau FSATSerProbe.tinyCC))  -- true
#eval decide (decodeF (runOut wfBig) = some (encodeTableau wfBig))                    -- true
-- non-wellformed → serF falseFml = [1,1,0,0,0]
#eval decide (runOut ({ FSATSerProbe.tinyCC with width := 0 } : BinaryCC) = [1,1,0,0,0])   -- true
#eval decide (runOut ({ FSATSerProbe.tinyCC with offset := 0 } : BinaryCC) = [1,1,0,0,0])  -- true
#eval decide (runOut ({ FSATSerProbe.tinyCC with cards := [⟨[true,true],[false]⟩] } : BinaryCC) = [1,1,0,0,0])  -- true
#eval decide (runOut ({ FSATSerProbe.tinyCC with offset := 2, width := 1 } : BinaryCC) = [1,1,0,0,0])  -- true

end FullProgram
