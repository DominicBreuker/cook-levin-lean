import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT
import Complexity.Lang.PolyTime

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

/-! ## 3. Validated emitter building blocks (probe-backed, session-2 assembly)

These are the concrete DSL fragments the program is assembled from, each
`#eval`-validated end-to-end in `probes/FSATSerProbe.lean` against the pure
`serF`. They are pure `Cmd` DATA (no proof obligations yet); session 2 proves the
run lemmas (`emitBits_run`, `emitAnd_run`, …) mirroring the sentinel-loop lemmas
in `FlatCC_to_BinaryCC_free.lean`.

Working scratch registers (all `≥ 22`, above the pinned input frame). -/
def OUT  : Nat := 22   -- serialized-formula accumulator (moved to FOUT at the end)
def SCAN : Nat := 23   -- consumable copy of a stream being iterated
def CNT  : Nat := 24   -- forBnd loop counter (holds 1^i)
def WREG : Nat := 25   -- unary variable index being emitted
def TFLG : Nat := 26   -- bit/branch flag
def BASE : Nat := 27   -- running unary base offset for a row/segment

/-- Append the 2-bit tag of a binary node to `OUT`. `fand = [0,1]`, `forr = [1,0]`. -/
def emitTag (b0 b1 : Nat) : Cmd :=
  (if b0 = 1 then Cmd.op (.appendOne OUT) else Cmd.op (.appendZero OUT)) ;;
  (if b1 = 1 then Cmd.op (.appendOne OUT) else Cmd.op (.appendZero OUT))

/-- Emit `serF (fvar w)` where `WREG = 1^w`: `[1,1,1] ++ 1^w ++ [0]`. -/
def emitVar : Cmd :=
  Cmd.op (.appendOne OUT) ;; Cmd.op (.appendOne OUT) ;; Cmd.op (.appendOne OUT) ;;
  Cmd.op (.concat OUT OUT WREG) ;; Cmd.op (.appendZero OUT)

/-- Emit the literal for one tableau bit: `head`/`tail` off `SCAN` selects
`fvar w` (bit 1) vs `fneg (fvar w)` (bit 0); `WREG = 1^w` is the absolute index. -/
def emitLit : Cmd :=
  Cmd.op (.head TFLG SCAN) ;;
  Cmd.op (.tail SCAN SCAN) ;;
  Cmd.ifBit TFLG
    emitVar
    (Cmd.op (.appendOne OUT) ;; Cmd.op (.appendOne OUT) ;; Cmd.op (.appendZero OUT) ;; emitVar)

/-- `serF (encodeBitsAt start bs)` into `OUT`, with `BASE = 1^start`, `SCAN = bs`.
The `forBnd` counter `CNT = 1^i`, so `WREG := BASE ++ CNT = 1^(start+i)` is the
absolute variable index (validated by `probes/FSATSerProbe.lean` `checkBits`). -/
def emitBitsAt (bound : Nat) : Cmd :=
  Cmd.forBnd CNT bound
    ( Cmd.op (.concat WREG BASE CNT) ;;
      emitTag 0 1 ;;                 -- fand tag
      emitLit ) ;;
  Cmd.op (.appendZero OUT) ;; Cmd.op (.appendZero OUT)   -- ftrue base tag [0,0]

/-! ## DESIGN RESOLUTIONS + NEXT-SESSION PLAN (top-down session 2)

**(a) Guard-or-no-guard — GUARDED.** `BinaryCC_to_FSAT_instance C =
if BinaryCC_wellformed C then encodeTableau C else falseFml`. So the program must
reproduce the wellformedness guard (like `FlatCC_to_BinaryCC_free`'s validity
guard). `BinaryCC_wellformed` is a conjunction of decidable checks on the input
(`width>0`, `offset>0`, `∃k>0, width=k*offset`, `init.length ≥ width`, per-card
prem/conc length `= width`, `∃k, init.length=k*offset`). Encode as an on-machine
`FLAG`, and on `¬wellformed` write `serF falseFml = serF (fneg ftrue) =
[1,1,0,0,0]` into `FOUT` (constant). The `∃k` divisibility checks are unary
remainder loops (reuse `FlatCC_to_BinaryCC_free`'s `remCheck`/`mulLoop`).
*Probe whether the guard is strictly NECESSARY (paper): pick a tiny non-wf
instance, check if `encodeTableau` is accidentally SAT while `BinaryCCLang` is
false — if not necessary, the correctness proof still needs it because
`encodeTableau_correct` assumes `hWf`.*

**(b) Output codec — DONE & PROVEN above** (`serF`/`decodeF`/`decodeF_serF`).

**(c) Input layout — pinned above** to the BinaryCC exit frame (17/18/19/20/21/5).
`encodeIn` (session 2) lays `offset/width/steps` unary, `init` as a bit-list, and
`cards/final` as sentinel streams matching `FlatCCBinFree`'s output formats, so
the seam is a scrub. `encodeIn_size ≤ 2·size+1` holds (all unary/bit, no doubling).

**(d) `map`-over-lists — NOT needed for the core.** The builder is nested
`forBnd` loops emitting tokens (validated); no generic list-map gadget is
required. `parked/MapNatList_WIP.lean` stays parked.

**Program assembly `buildFSAT : Cmd` (session 2), mirroring `encodeTableau`:**
`encodeTableau C = fand (encodeBitsAt 0 init) (fand (allStepConstraints) (finalConstraint))`.
Polish emission order:
  1. guard → `FLAG`;
  2. `emitTag 0 1` (outer fand); `emitBitsAt` over `INIT` at `BASE=0`;
  3. `emitTag 0 1` (inner fand);
  4. `encodeAllStepConstraints` = `listAnd` over `range steps` of
     `encodeLineConstraints` = `listAnd` over `range (init.len+1)` of
     `encodeStepConstraint` (guarded `step*offset+width ≤ init.len`) =
     `encodeCardsAt` = `listOr` over `cards` of `encodeCardAt = fand (bitsAt startA prem)(bitsAt startB conc)`.
     ⇒ FOUR nested loops (line, step, card, bit) with `listAnd`/`listOr` folds.
     Absolute indices `startA = line*L + step*offset`, `startB = (line+1)*L + step*offset`
     (`L = init.length`) computed unary via nested `concat`/`mulLoop` from the
     loop counters (the `BASE` register threads the running offset).
  5. `encodeFinalConstraint` = `listOr` over `final` of `encodeFinalString` =
     `listOr` over offsets of `encodeFinalAtStep` (guarded), at `steps*L + step*offset`.
  6. `copy FOUT OUT`.
Each `listAnd`/`listOr` fold = a `forBnd` that emits `operatorTag ++ child` per
element then the base tag (`ftrue`/`falseFml`). The card/final streams are
consumed off `SCAN` copies exactly like `FlatCC_to_BinaryCC_free`'s `sentStep`.

**Run/cost lemmas (session 2), templates in `FlatCC_to_BinaryCC_free.lean`:**
prove `emitBitsAt_run` (fold invariant: after `i` iters `OUT = OUT₀ ++ serF-prefix`),
then the `listAnd`/`listOr` loop lemmas, then compose bottom-up to
`buildFSAT_run : (buildFSAT.eval (encodeIn C)).get FOUT = serF (BinaryCC_to_FSAT_instance C)`.
`computes` then follows from `decodeOut_of_serF` + `buildFSAT_run`. Cost is a
polynomial in the tableau size (nested-loop product; `physStepBudget` shape).
Budget the var-index unary arithmetic carefully — `mulLoop` per index is `Θ(index)`,
and there are `Θ(steps·L)` indices, so the honest cost is a low-degree polynomial;
confirm the degree with a `cost_forBnd_le` accounting pass (cf. CliqueRel's
quartic→quintic uniform-bound bump).
-/

end BinaryCCFSATFree
