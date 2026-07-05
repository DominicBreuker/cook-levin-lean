import Complexity.Lang.AcceptHalt

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

end C8GadgetsProbe
