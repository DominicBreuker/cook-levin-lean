import Complexity.NP.SAT.CookLevin.Reductions.FlatCC_to_BinaryCC
import Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC_free

/-! # FlatCC → BinaryCC free-witness probe (top-down, S3 chain step, 2026-07-02)

Go/no-go `#eval` probe for the **`FlatCC_to_BinaryCC_instance` reduction as a
concrete layer program** (HANDOFF top-down target #2, item 1).

**Design finding (paper probe, this session): the `isValidFlattening` guard
canNOT be dropped for this step.** Counterexample: `C = ⟨Sigma:=1, offset:=1,
width:=1, init:=[1], cards:=[], final:=[[1]], steps:=0⟩` is an INVALID
flattening (symbol `1 ≥ Sigma`), so `FlatCCLang C` is false; but the unguarded
per-symbol block encoding maps it to `init = [false,true]`,
`final = [[false,true]]`, `offset = width = 1` — a *wellformed* BinaryCC
yes-instance (`init.length = 2 = 2·offset`, `satFinal` at `step 0`). Unlike
`flatTCC_to_flatCC` (which preserves `Sigma` and symbol content, so invalidity
transfers), the binary image ERASES the alphabet bound — no pure per-symbol
encoding can transfer invalidity. Hence the program carries an **on-machine
validity check** (every unary symbol `< Sigma`, computed with the truncated-
subtraction trick from `ltBit`'s design) and a final guard branch writing the
no-instance (all-empty registers) when the check fails.

**Layout.** Input = the flatTCC witness's EXIT layout (seam discipline —
the first live `SeamData` then only scrubs scratch): reg 1 `Sigma` (unary),
reg 2 `init` (bare blocks), reg 4 `final` (sentinel lists), reg 5 `steps`
(unary), reg 6 `offset` (unary), reg 7 `width` (unary), reg 8 `cards`
(per card two sentinel lists). Output: reg 17 `offset` (unary), reg 18
`width` (unary), reg 19 `init` (raw bits), reg 20 `cards` (per card two
sentinel bit-lists), reg 21 `final` (sentinel bit-lists), reg 5 `steps`
(shared identity).

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/FlatCCBinProbe.lean`
-/

open Complexity.Lang FlatTCCFree

namespace FlatCCBinProbe

/-! ## Registers -/

def SIGMA  : Var := 1
def INIT   : Var := 2
def FINAL  : Var := 4
def STEPS  : Var := 5
def OFFSET : Var := 6
def WIDTH  : Var := 7
def CARDS  : Var := 8
def SCAN   : Var := 9
def VALX   : Var := 10
def FLAG   : Var := 11
def IDXO   : Var := 12
def IDXR   : Var := 13
def REM    : Var := 14
def BOFF   : Var := 17
def BWID   : Var := 18
def BINIT  : Var := 19
def BCARDS : Var := 20
def BFINAL : Var := 21
def TFLG   : Var := 23
def IDX2   : Var := 24

/-! ## The program -/

/-- `FLAG := [0]` (validity reject). -/
def setInvalid : Cmd := Cmd.op (.clear FLAG) ;; Cmd.op (.appendZero FLAG)

/-- Validity check + remainder: assumes `VALX = 1^v`, `SIGMA = 1^k`.
Leaves `REM = 1^(k-v-1)` (truncated) and ANDs `v < k` into `FLAG`. -/
def remCheck : Cmd :=
  Cmd.op (.copy REM SIGMA) ;;
  Cmd.forBnd IDX2 VALX (Cmd.op (.tail REM REM)) ;;
  Cmd.op (.nonEmpty TFLG REM) ;;
  Cmd.ifBit TFLG CliqueRelTM.cSkip setInvalid ;;
  Cmd.op (.tail REM REM)

/-- Append the bare-bit expansion of symbol `v` (`VALX = 1^v`) to `dst`:
`0^v 1 0^(k-v-1)`. -/
def expandBare (dst : Var) : Cmd :=
  Cmd.forBnd IDX2 VALX (Cmd.op (.appendZero dst)) ;;
  Cmd.op (.appendOne dst) ;;
  remCheck ;;
  Cmd.forBnd IDX2 REM (Cmd.op (.appendZero dst))

/-- Append the sentinel-format expansion of symbol `v` to `dst`: the `k` bits
of the block, each as a sentinel element (`0 ↦ [1,0]`, `1 ↦ [1,1,0]`). -/
def expandSent (dst : Var) : Cmd :=
  Cmd.forBnd IDX2 VALX (Cmd.op (.appendOne dst) ;; Cmd.op (.appendZero dst)) ;;
  Cmd.op (.appendOne dst) ;; Cmd.op (.appendOne dst) ;; Cmd.op (.appendZero dst) ;;
  remCheck ;;
  Cmd.forBnd IDX2 REM (Cmd.op (.appendOne dst) ;; Cmd.op (.appendZero dst))

/-- Consume one bare block off `SCAN`, appending its bit expansion to `BINIT`;
idle when exhausted. -/
def initStep : Cmd :=
  Cmd.op (.nonEmpty TFLG SCAN) ;;
  Cmd.ifBit TFLG
    (CliqueRelTM.readNum VALX SCAN IDXR ;; expandBare BINIT)
    CliqueRelTM.cSkip

/-- Consume one sentinel-stream item off `SCAN` (element `1 1^v 0` or list
terminator `0`), appending its expansion to `dst`; idle when exhausted. -/
def sentStep (dst : Var) : Cmd :=
  Cmd.op (.nonEmpty TFLG SCAN) ;;
  Cmd.ifBit TFLG
    (Cmd.op (.head TFLG SCAN) ;;
     Cmd.op (.tail SCAN SCAN) ;;
     Cmd.ifBit TFLG
       (CliqueRelTM.readNum VALX SCAN IDXR ;; expandSent dst)
       (Cmd.op (.appendZero dst)))
    CliqueRelTM.cSkip

/-- **The reduction program.** -/
def binConvert : Cmd :=
  Cmd.op (.clear FLAG) ;; Cmd.op (.appendOne FLAG) ;;
  Cmd.op (.clear BOFF) ;;
  Cmd.forBnd IDXO OFFSET (Cmd.op (.concat BOFF BOFF SIGMA)) ;;
  Cmd.op (.clear BWID) ;;
  Cmd.forBnd IDXO WIDTH (Cmd.op (.concat BWID BWID SIGMA)) ;;
  Cmd.op (.clear BINIT) ;;
  Cmd.op (.copy SCAN INIT) ;;
  Cmd.forBnd IDXO INIT initStep ;;
  Cmd.op (.clear BCARDS) ;;
  Cmd.op (.copy SCAN CARDS) ;;
  Cmd.forBnd IDXO CARDS (sentStep BCARDS) ;;
  Cmd.op (.clear BFINAL) ;;
  Cmd.op (.copy SCAN FINAL) ;;
  Cmd.forBnd IDXO FINAL (sentStep BFINAL) ;;
  Cmd.ifBit FLAG CliqueRelTM.cSkip
    (Cmd.op (.clear BOFF) ;; Cmd.op (.clear BWID) ;; Cmd.op (.clear BINIT) ;;
     Cmd.op (.clear BCARDS) ;; Cmd.op (.clear BFINAL) ;; Cmd.op (.clear STEPS))

/-! ## Expected values (the flat-level image the run lemma will assert) -/

/-- Bit expansion of one flat symbol (`Nat`-valued bits `0`/`1`). -/
def expandSym (k v : Nat) : List Nat :=
  List.replicate v 0 ++ 1 :: List.replicate (k - v - 1) 0

def expandStr (k : Nat) (xs : List Nat) : List Nat := xs.flatMap (expandSym k)

def expandCard (k : Nat) (c : CCCard Nat) : CCCard Nat :=
  ⟨expandStr k c.prem, expandStr k c.conc⟩

def validB (C : FlatCC) : Bool :=
  C.init.all (· < C.Sigma) &&
  C.cards.all (fun c => c.prem.all (· < C.Sigma) && c.conc.all (· < C.Sigma)) &&
  C.final.all (fun s => s.all (· < C.Sigma))

/-- The natural FlatCC input layout, on the flatTCC witness's exit frame. -/
def encodeIn (C : FlatCC) : State :=
  [[], List.replicate C.Sigma 1, encNats C.init, [], encFinal C.final,
   List.replicate C.steps 1, List.replicate C.offset 1,
   List.replicate C.width 1, encCardsOut C.cards]

def extractKey (s : State) : List (List Nat) :=
  [State.get s BOFF, State.get s BWID, State.get s BINIT,
   State.get s BCARDS, State.get s BFINAL, State.get s STEPS]

/-- What the run lemma will assert register-wise. -/
def expectedKey (C : FlatCC) : List (List Nat) :=
  if validB C then
    [List.replicate (C.Sigma * C.offset) 1, List.replicate (C.Sigma * C.width) 1,
     expandStr C.Sigma C.init, encCardsOut (C.cards.map (expandCard C.Sigma)),
     encFinal (C.final.map (expandStr C.Sigma)),
     List.replicate C.steps 1]
  else [[], [], [], [], [], []]

def checkOne (C : FlatCC) : Bool :=
  extractKey (binConvert.eval (encodeIn C)) == expectedKey C

/-! ## Cross-check the expected values against the REAL map's encodings
(`encodeString` over the unflattened `Fin` symbols, bit-mapped to `Nat`) -/

def bitsNat (bs : List Bool) : List Nat := bs.map (fun b => cond b 1 0)

/-- `expandSym` must be the `Nat`-bit image of `encodeSymbol` for valid symbols. -/
def checkSym (k v : Nat) (h : v < k) : Bool :=
  expandSym k v == bitsNat (encodeSymbol (⟨v, h⟩ : Fin k))

#eval checkSym 1 0 (by omega)   -- expect true
#eval checkSym 3 0 (by omega)   -- expect true
#eval checkSym 3 2 (by omega)   -- expect true
#eval checkSym 7 4 (by omega)   -- expect true

/-! ## Test instances -/

def mkC (Sigma offset width : Nat) (init : List Nat) (cards : List (CCCard Nat))
    (final : List (List Nat)) (steps : Nat) : FlatCC :=
  ⟨Sigma, offset, width, init, cards, final, steps⟩

/-- Empty everything (Sigma 0: vacuously valid, empty streams). -/
def C0 : FlatCC := mkC 0 0 0 [] [] [] 0

/-- Valid, no cards. -/
def C1 : FlatCC := mkC 3 1 3 [0, 1, 2] [] [[0], [], [2, 1]] 5

/-- Valid, one card. -/
def C2 : FlatCC := mkC 2 1 2 [0, 1] [⟨[0, 1], [1, 0]⟩] [[1, 1]] 1

/-- Valid, wider: two cards, empty prem lists exercised. -/
def C3 : FlatCC :=
  mkC 4 2 4 [1, 2, 3, 0] [⟨[1, 0, 2], [3, 0, 1]⟩, ⟨[], [2]⟩] [[3, 2], [0]] 2

/-- INVALID: symbol `1 ≥ Sigma = 1` in init and final (the paper-probe
counterexample) — must map to the all-empty no-instance key. -/
def C4 : FlatCC := mkC 1 1 1 [1] [] [[1]] 0

/-- INVALID: bad symbol hidden in a card conc only. -/
def C5 : FlatCC := mkC 2 1 2 [0, 1] [⟨[0, 1], [1, 2]⟩] [[1]] 3

/-- INVALID: bad symbol in final only. -/
def C6 : FlatCC := mkC 2 1 2 [0] [] [[0], [5]] 1

#eval checkOne C0  -- expect true
#eval checkOne C1  -- expect true
#eval checkOne C2  -- expect true
#eval checkOne C3  -- expect true
#eval checkOne C4  -- expect true
#eval checkOne C5  -- expect true
#eval checkOne C6  -- expect true

/-- Input registers 1–8 (minus nothing) are untouched in the VALID case;
in the invalid case only `STEPS` (reg 5) is cleared. -/
def checkFrame (C : FlatCC) : Bool :=
  let out := binConvert.eval (encodeIn C)
  ((List.range 9).filter (fun r => !(r == STEPS && !validB C))).all
    (fun r => State.get out r == State.get (encodeIn C) r)

#eval checkFrame C1  -- expect true
#eval checkFrame C3  -- expect true
#eval checkFrame C4  -- expect true

/-! ## End-to-end seam probe: flatTCC exit → scrub → binConvert

Validates the whole `SeamData` pipeline on a concrete FlatTCC: run the proven
`cardConvert`, scrub reg 3 + scratch 9–26 (the seam `mfc`), then `binConvert`,
and compare with the two-step expected key. -/

def scrub : Cmd :=
  Cmd.op (.clear 3) ;; Cmd.op (.clear 9) ;; Cmd.op (.clear 10) ;;
  Cmd.op (.clear 11) ;; Cmd.op (.clear 12) ;; Cmd.op (.clear 13) ;;
  Cmd.op (.clear 14) ;; Cmd.op (.clear 15) ;; Cmd.op (.clear 16) ;;
  Cmd.op (.clear 17) ;; Cmd.op (.clear 18) ;; Cmd.op (.clear 19) ;;
  Cmd.op (.clear 20) ;; Cmd.op (.clear 21) ;; Cmd.op (.clear 22) ;;
  Cmd.op (.clear 23) ;; Cmd.op (.clear 24) ;; Cmd.op (.clear 25) ;;
  Cmd.op (.clear 26)

def mkCardT (a b c d e f : Nat) : TCCCard Nat := ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩

def T1 : FlatTCC := ⟨3, [0, 1, 2], [mkCardT 1 0 2 2 0 1], [[2, 1], [0]], 2⟩

/-- Invalid FlatTCC (symbol 5 ≥ Sigma) — composite must give the no-instance. -/
def T2 : FlatTCC := ⟨2, [0, 5], [mkCardT 1 0 1 0 0 1], [[1]], 1⟩

def compositeEval (T : FlatTCC) : State :=
  binConvert.eval (scrub.eval (FlatTCCFree.cardConvert.eval (FlatTCCFree.encodeIn T)))

def checkComposite (T : FlatTCC) : Bool :=
  extractKey (compositeEval T) == expectedKey (flatTCC_to_flatCC T)

#eval checkComposite T1  -- expect true
#eval checkComposite T2  -- expect true

/-- The bridge check: after `cardConvert ;; scrub`, ALL registers < 27 agree
with `encodeIn (flatTCC_to_flatCC T)` (the seam's `AgreeBelow`). -/
def checkBridge (T : FlatTCC) : Bool :=
  let mid := scrub.eval (FlatTCCFree.cardConvert.eval (FlatTCCFree.encodeIn T))
  (List.range 27).all (fun r =>
    State.get mid r == State.get (encodeIn (flatTCC_to_flatCC T)) r)

#eval checkBridge T1  -- expect true
#eval checkBridge T2  -- expect true

-- Everything at once.
#eval ([C0, C1, C2, C3, C4, C5, C6].all (fun C => checkOne C && checkFrame C))
  && ([T1, T2].all (fun T => checkComposite T && checkBridge T))

end FlatCCBinProbe
