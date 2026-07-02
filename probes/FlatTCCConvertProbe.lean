import Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC
import Complexity.Complexity.Deciders.CliqueRelTM

/-! # FlatTCC → FlatCC free-witness probe (top-down, S3 chain step, 2026-07-02)

Go/no-go `#eval` probe for the **`flatTCC_to_flatCC` reduction as a concrete
layer program** (HANDOFF top-down target #2.1): the `Cmd` `cardConvert` that
computes the (unguarded) structural map on the natural FlatTCC input layout:

* registers 1–5 hold `Sigma` (unary), `init` (bare unary blocks), `cards`
  (6 bare unary blocks per card), `final` (sentinel-list strings), `steps`
  (unary);
* the program writes `offset := [1]` (reg 6), `width := [1,1,1]` (reg 7), and
  re-formats the card stream (reg 3 → reg 8) from bare 6-block groups into the
  CCCard layout (two sentinel-delimited 3-element lists per card);
* `Sigma`/`init`/`final`/`steps` are shared-layout (identical encodings in the
  input and output layouts), so the program does not touch them.

**Check:** for a grid of `FlatTCC` inputs, the evaluated state's registers
`[1,6,7,2,8,4,5]` equal the output-layout key `encKey (flatTCC_to_flatCC C)`.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/FlatTCCConvertProbe.lean`
-/

open Complexity.Lang

namespace FlatTCCProbe

/-! Registers. `CliqueRelTM.readNum` pins `HEAD = 15`, `INBLK = 16`,
`SKIPR = 26` (via `cSkip`). -/
def SIGMA  : Var := 1
def INIT   : Var := 2
def CARDS  : Var := 3
def FINAL  : Var := 4
def STEPS  : Var := 5
def OFFSET : Var := 6
def WIDTH  : Var := 7
def OUT    : Var := 8
def SCAN   : Var := 9
def VALX   : Var := 10
def FLAG   : Var := 11
def IDXO   : Var := 12
def IDXR   : Var := 13

/-! ## Encodings -/

/-- Bare unary block: `1^v 0`. -/
def encNat (v : Nat) : List Nat := List.replicate v 1 ++ [0]

/-- A `List Nat` as a stream of bare blocks (self-delimiting, prefix-free). -/
def encNats (xs : List Nat) : List Nat := (xs.map encNat).flatten

/-- Sentinel element: `1 :: 1^v 0` (the leading `1` distinguishes an element
from the list terminator `0`). -/
def encSElem (v : Nat) : List Nat := 1 :: (List.replicate v 1 ++ [0])

/-- A `List Nat` as a sentinel-delimited, `0`-terminated list (nestable). -/
def encSList (xs : List Nat) : List Nat := (xs.map encSElem).flatten ++ [0]

/-- The 6 nats of a TCC card, prem-first. -/
def cardNats (c : TCCCard Nat) : List Nat :=
  [c.prem.cardEl1, c.prem.cardEl2, c.prem.cardEl3,
   c.conc.cardEl1, c.conc.cardEl2, c.conc.cardEl3]

def encCardIn (c : TCCCard Nat) : List Nat := encNats (cardNats c)

def encCardsIn (cs : List (TCCCard Nat)) : List Nat := (cs.map encCardIn).flatten

/-- A CC card: two sentinel lists (prem, conc). -/
def encCardOut (c : CCCard Nat) : List Nat := encSList c.prem ++ encSList c.conc

def encCardsOut (cs : List (CCCard Nat)) : List Nat := (cs.map encCardOut).flatten

def encFinal (fss : List (List Nat)) : List Nat := (fss.map encSList).flatten

/-- The natural FlatTCC input layout. -/
def encodeIn (C : FlatTCC) : State :=
  [[], List.replicate C.Sigma 1, encNats C.init, encCardsIn C.cards,
   encFinal C.final, List.replicate C.steps 1]

/-- The natural FlatCC output layout, as the 7-register key `decodeOut` inverts. -/
def encKey (P : FlatCC) : List (List Nat) :=
  [List.replicate P.Sigma 1, List.replicate P.offset 1, List.replicate P.width 1,
   encNats P.init, encCardsOut P.cards, encFinal P.final,
   List.replicate P.steps 1]

/-! ## The program -/

/-- Move one bare block off `SCAN` onto `OUT` as a sentinel element. -/
def blockMove : Cmd :=
  Cmd.op (.appendOne OUT) ;;
  CliqueRelTM.readNum VALX SCAN IDXR ;;
  Cmd.op (.concat OUT OUT VALX) ;;
  Cmd.op (.appendZero OUT)

/-- Consume one card (6 blocks) off `SCAN`, appending the CCCard layout
(3 sentinel elements + terminator, twice) to `OUT`; idle when `SCAN` is empty. -/
def cardStep : Cmd :=
  Cmd.op (.nonEmpty FLAG SCAN) ;;
  Cmd.ifBit FLAG
    (blockMove ;; blockMove ;; blockMove ;; Cmd.op (.appendZero OUT) ;;
     blockMove ;; blockMove ;; blockMove ;; Cmd.op (.appendZero OUT))
    CliqueRelTM.cSkip

/-- The whole reduction program. -/
def cardConvert : Cmd :=
  Cmd.op (.copy SCAN CARDS) ;;
  Cmd.op (.clear OUT) ;;
  Cmd.op (.clear OFFSET) ;; Cmd.op (.appendOne OFFSET) ;;
  Cmd.op (.clear WIDTH) ;;
  Cmd.op (.appendOne WIDTH) ;; Cmd.op (.appendOne WIDTH) ;;
  Cmd.op (.appendOne WIDTH) ;;
  Cmd.forBnd IDXO SCAN cardStep

/-! ## The checks -/

def extractKey (s : State) : List (List Nat) :=
  [State.get s SIGMA, State.get s OFFSET, State.get s WIDTH,
   State.get s INIT, State.get s OUT, State.get s FINAL, State.get s STEPS]

def checkOne (C : FlatTCC) : Bool :=
  extractKey (cardConvert.eval (encodeIn C)) == encKey (flatTCC_to_flatCC C)

def mkCard (a b c d e f : Nat) : TCCCard Nat :=
  ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩

/-- Empty everything. -/
def C0 : FlatTCC := ⟨0, [], [], [], 0⟩

/-- No cards, but data elsewhere. -/
def C1 : FlatTCC := ⟨3, [0, 1, 2], [], [[0], [], [2, 1]], 5⟩

/-- One all-zero card (the degenerate-block case). -/
def C2 : FlatTCC := ⟨1, [0, 0, 0], [mkCard 0 0 0 0 0 0], [[0, 0, 0]], 1⟩

/-- Two mixed cards. -/
def C3 : FlatTCC :=
  ⟨4, [1, 2, 3, 0], [mkCard 1 0 2 3 0 1, mkCard 0 2 0 1 1 3],
   [[3, 2], [0]], 2⟩

/-- Larger values (block lengths ≫ card count). -/
def C4 : FlatTCC :=
  ⟨7, [6, 5], [mkCard 6 5 4 3 2 1, mkCard 0 0 6 6 0 0, mkCard 1 1 1 1 1 1],
   [], 9⟩

#eval checkOne C0  -- expect true
#eval checkOne C1  -- expect true
#eval checkOne C2  -- expect true
#eval checkOne C3  -- expect true
#eval checkOne C4  -- expect true

/-- The frame: input registers 0–5 are untouched. -/
def checkFrame (C : FlatTCC) : Bool :=
  ((List.range 6).map (fun r => State.get (cardConvert.eval (encodeIn C)) r))
    == (List.range 6).map (fun r => State.get (encodeIn C) r)

#eval checkFrame C3  -- expect true
#eval checkFrame C4  -- expect true

-- Everything at once.
#eval [C0, C1, C2, C3, C4].all (fun C => checkOne C && checkFrame C)

end FlatTCCProbe
