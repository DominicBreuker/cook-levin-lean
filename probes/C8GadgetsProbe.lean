import Complexity.Lang.AcceptHalt
import Complexity.Lang.FormatCheck

/-! # C8-2 gadget probe — accept-by-halting wrapper + tape-format check

**Bottom-up C8-2 session (2026-07-05).** `#eval` validation of the two TM
gadgets scoping findings F4/F5 demand, BEFORE their run lemmas are relied on
(standard method):

1. **`AcceptHalt.demoteHalt`** (F4): on a toy two-exit decider (accept state
   1, reject state 2), the wrapper must keep the accept run intact
   (`acceptsFlatTM` true) and turn the reject HALT into a stuck, never-halting
   run (`acceptsFlatTM` false at every budget).
2. **`FormatCheck.formatCheckTM`** (F5, added below when built): valid
   `encodeTape` tapes pass through with tape unchanged + head 0; every
   malformed-cert shape (separator `0` inside the cert, premature terminator,
   missing terminator, garbage after the terminator, out-of-alphabet cell)
   sticks forever.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/C8GadgetsProbe.lean`
-/

open Complexity.Lang

namespace C8GadgetsProbe

/-! ## 1. The accept-by-halting wrapper -/

/-- Toy compiled-decider shape: state 0 reads the first cell; `2` (bit 1,
shifted) → accept state 1; `1` (bit 0) → reject state 2. Both exits HALT
(exactly the `bitTestTM` shape after composition shifts). -/
def toyDecider : FlatTM :=
  { sig := 4, tapes := 1, states := 3,
    trans := [⟨0, [some 2], 1, [none], [.Nmove]⟩,
              ⟨0, [some 1], 2, [none], [.Nmove]⟩],
    start := 0, halt := [false, true, true] }

def wrapped : FlatTM := AcceptHalt.demoteHalt toyDecider 2

-- The raw decider accepts-by-halting on BOTH answers (the F4 problem):
#eval acceptsFlatTM toyDecider [[2]] 5   -- expect true  (accept exit)
#eval acceptsFlatTM toyDecider [[1]] 5   -- expect true  (reject exit also halts!)

-- The wrapped machine accepts exactly on the accept exit:
#eval acceptsFlatTM wrapped [[2]] 5      -- expect true
#eval acceptsFlatTM wrapped [[1]] 5      -- expect false
#eval acceptsFlatTM wrapped [[1]] 1000   -- expect false (stuck forever, any budget)

-- The stuck config parks at the demoted state 2 and never halts:
#eval (runFlatTM 1000 wrapped (initFlatConfig wrapped [[1]])).map
        (fun c => (c.state_idx, haltingStateReached wrapped c))  -- expect some (2, false)

-- Invalid tapes still reject (execFlatTM guard unchanged):
#eval acceptsFlatTM wrapped [[9]] 5      -- expect false (symbol ≥ sig)

def probe1 : Bool :=
  acceptsFlatTM toyDecider [[2]] 5 && acceptsFlatTM toyDecider [[1]] 5 &&
  acceptsFlatTM wrapped [[2]] 5 && !acceptsFlatTM wrapped [[1]] 5 &&
  !acceptsFlatTM wrapped [[1]] 1000 && !acceptsFlatTM wrapped [[9]] 5

#eval probe1  -- expect true

/-! ## 2. The tape-format-check gadget

`w = 2` (two input registers + the cert register): the valid split state is
`[[0], [1], [1, 0]]`, tape `[3, 1,0, 2,0, 2,1,0, 3]` (length 9). The gadget
must pass it in `2·9 + 1 = 19` steps, tape unchanged, head 0, halt at
`D = w + 6 = 8` — and stick forever on every malformed-cert variant. -/

def w2 : Nat := 2
def fmt : FlatTM := FormatCheck.formatCheckTM w2

def sx : State := [[0], [1]]
def prefixTape : List Nat := 3 :: Compile.encodeRegs sx  -- [3, 1,0, 2,0]

def goodCert : List Nat := Compile.shiftReg [1, 0] ++ [0, 3]   -- [2,1,0,3]
def goodTape : List Nat := prefixTape ++ goodCert

-- sanity: the split reassembly is the canonical encodeTape
#eval goodTape == Compile.encodeTape (sx ++ [[1, 0]])  -- expect true

def runFmt (tape : List Nat) (n : Nat) : Option (Nat × Nat × List Nat × Bool) :=
  (runFlatTM n fmt (initFlatConfig fmt [tape])).map
    (fun c => (c.state_idx, c.tapes.head!.2.1, c.tapes.head!.2.2,
               haltingStateReached fmt c))

-- Valid tape: exactly 2L+1 = 19 steps to D = 8, head 0, tape unchanged:
#eval runFmt goodTape 19       -- expect some (8, 0, goodTape, true)
#eval runFmt goodTape 18       -- expect state ≠ 8 (no early halt)
#eval runFmt goodTape 1000     -- stays at D

-- Empty cert register (w = 2, creg = []): tape [3,1,0,2,0,0,3]
#eval runFmt (prefixTape ++ ([0, 3] : List Nat)) 1000  -- expect some (8, 0, _, true)

-- Malformed certs — ALL must stick forever (halting = false at big budget):
#eval runFmt (prefixTape ++ ([2, 0, 1, 0, 3] : List Nat)) 1000  -- extra 0 (extra register)
#eval runFmt (prefixTape ++ ([2, 1, 3] : List Nat)) 1000        -- missing 0 delimiter
#eval runFmt (prefixTape ++ ([2, 1, 0] : List Nat)) 1000        -- missing terminator
#eval runFmt (prefixTape ++ ([2, 1, 0, 3, 1] : List Nat)) 1000  -- garbage after terminator
#eval runFmt (prefixTape ++ ([2, 3, 0, 3] : List Nat)) 1000     -- premature 3
#eval runFmt (prefixTape ++ ([] : List Nat)) 1000               -- empty cert region

def certBad (cert : List Nat) : Bool :=
  -- certOKB rejects, and the machine never halts (probe at a large budget)
  !FormatCheck.certOKB cert &&
    ((runFlatTM 1000 fmt (initFlatConfig fmt [prefixTape ++ cert])).map
      (fun c => haltingStateReached fmt c) == some false)

def certGood (creg : List Nat) : Bool :=
  let cert := Compile.shiftReg creg ++ [0, 3]
  let tape := prefixTape ++ cert
  FormatCheck.certOKB cert &&
    ((runFlatTM (2 * tape.length + 1) fmt (initFlatConfig fmt [tape])).map
      (fun c => (c.state_idx == w2 + 6 : Bool) &&
        (c.tapes.head!.2.1 == 0) && (c.tapes.head!.2.2 == tape) &&
        haltingStateReached fmt c) == some true) &&
    -- no early halt at any strictly smaller budget
    (List.range (2 * tape.length + 1)).all (fun k =>
      (runFlatTM k fmt (initFlatConfig fmt [tape])).map
        (fun c => haltingStateReached fmt c) == some false)

def probe2 : Bool :=
  certGood [] && certGood [0] && certGood [1] && certGood [1, 0] &&
  certGood [0, 1, 1, 0] &&
  certBad [2, 0, 1, 0, 3] && certBad [2, 1, 3] && certBad [2, 1, 0] &&
  certBad [2, 1, 0, 3, 1] && certBad [2, 3, 0, 3] && certBad [] &&
  certBad [0, 3, 3] && certBad [3] && certBad [5, 0, 3]

#eval probe2  -- expect true

#eval probe1 && probe2  -- the session verdict

end C8GadgetsProbe
