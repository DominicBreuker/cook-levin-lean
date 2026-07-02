import Complexity.NP.kSAT_to_SAT
import Complexity.Complexity.Deciders.CliqueRelTM

/-! # kCNF-3 re-encoder probe (top-down, S3 linchpin, 2026-07-01)

Go/no-go `#eval` probe for the **concrete `FreePrecomposeData` re-encoder**
(HANDOFF top-down target #1): the `Cmd` `kCnf3Check` that runs the reduction
`kSAT_to_SAT_reduction 3` *on-machine* over the SAT verifier's bespoke input
layout (`EvalCnfCmd.encodeState`).

The program:
1. copies `CNF_STREAM` (reg 2) to scratch and parses it clause by clause
   (outer bound = `CLAUSE_TALLY`, reg 1), counting each clause's literals in
   unary (`readNum` drains each literal's unary variable block) and comparing
   the count against `THREE = [1,1,1]`;
2. if every clause has exactly 3 literals (`kCNF 3 N`), leaves regs 1/2
   untouched, else rewrites them to `encodeState`'s layout of the canonical
   no-instance `[[]]` (`CLAUSE_TALLY := [1]`, `CNF_STREAM := [0]`);
3. scrubs the single below-16 scratch register `readNum` uses
   (`CliqueRelTM.HEAD = 15`).

**Check:** for a grid of inputs `(N, a)`, the evaluated state agrees on
registers `0..15` (the verifier frame, `regBound = 16`) with
`encodeState (kSAT_to_SAT_reduction 3 N, a)` — i.e. exactly the
`FreePrecomposeData.bridge` law, `#eval`-decided.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/KCnf3ReencoderProbe.lean`
-/

open Complexity.Lang

namespace KCnf3Probe

/-! Scratch registers. `CliqueRelTM.readNum` pins `HEAD = 15`, `INBLK = 16`,
`SKIPR = 26` (via `cSkip`) — everything else lives at `≥ 17`. -/
def SCAN  : Var := 17
def OK    : Var := 18
def THREE : Var := 19
def LCNT  : Var := 20
def CDONE : Var := 21
def RES   : Var := 22
def HEADC : Var := 23
def VALX  : Var := 24
def IDXO  : Var := 25
def IDXI  : Var := 27
def IDXV  : Var := 28

/-- One inner-loop iteration: consume one literal (or the clause-end `0`) off
`SCAN`. Idles once `CDONE = [1]`. -/
def litScan : Cmd :=
  Cmd.ifBit CDONE
    CliqueRelTM.cSkip
    (Cmd.op (.head HEADC SCAN) ;;
     Cmd.op (.tail SCAN SCAN) ;;
     Cmd.ifBit HEADC
       (Cmd.op (.tail SCAN SCAN) ;;
        CliqueRelTM.readNum VALX SCAN IDXV ;;
        Cmd.op (.appendOne LCNT))
       (Cmd.op (.clear CDONE) ;; Cmd.op (.appendOne CDONE)))

/-- Consume one encoded clause off `SCAN`, then AND `|C| = 3` into `OK`. -/
def clauseScan : Cmd :=
  Cmd.op (.clear LCNT) ;;
  Cmd.op (.clear CDONE) ;;
  Cmd.forBnd IDXI SCAN litScan ;;
  Cmd.op (.eqBit RES LCNT THREE) ;;
  Cmd.ifBit RES CliqueRelTM.cSkip
    (Cmd.op (.clear OK) ;; Cmd.op (.appendZero OK))

/-- The re-encoder: computes `kSAT_to_SAT_reduction 3` in-place on the
`EvalCnfCmd.encodeState` layout. -/
def kCnf3Check : Cmd :=
  Cmd.op (.copy SCAN EvalCnfCmd.CNF_STREAM) ;;
  Cmd.op (.clear OK) ;; Cmd.op (.appendOne OK) ;;
  Cmd.op (.clear THREE) ;;
  Cmd.op (.appendOne THREE) ;; Cmd.op (.appendOne THREE) ;;
  Cmd.op (.appendOne THREE) ;;
  Cmd.forBnd IDXO EvalCnfCmd.CLAUSE_TALLY clauseScan ;;
  Cmd.ifBit OK
    CliqueRelTM.cSkip
    (Cmd.op (.clear EvalCnfCmd.CLAUSE_TALLY) ;;
     Cmd.op (.appendOne EvalCnfCmd.CLAUSE_TALLY) ;;
     Cmd.op (.clear EvalCnfCmd.CNF_STREAM) ;;
     Cmd.op (.appendZero EvalCnfCmd.CNF_STREAM)) ;;
  Cmd.op (.clear CliqueRelTM.HEAD)

/-- The bridge law at one input, decided: registers `0..15` of
`kCnf3Check.eval (encodeState (N, a))` equal those of
`encodeState (kSAT_to_SAT_reduction 3 N, a)`. -/
def bridgeOK (N : cnf) (a : assgn) : Bool :=
  let s1 := kCnf3Check.eval (EvalCnfCmd.encodeState (N, a))
  let s2 := EvalCnfCmd.encodeState (kSAT_to_SAT_reduction 3 N, a)
  (List.range 16).all (fun r => State.get s1 r == State.get s2 r)

-- yes-instances (all clauses length 3; expect regs 1/2 preserved)
#eval bridgeOK [] []                                               -- empty cnf
#eval bridgeOK [[(true,0),(false,1),(true,2)]] [0,2]
#eval bridgeOK [[(true,0),(false,1),(true,2)]] []
#eval bridgeOK [[(true,3),(true,3),(false,0)],
                [(false,2),(true,1),(true,4)]] [1,3]
-- no-instances (some clause length ≠ 3; expect regs 1/2 := encode [[]])
#eval bridgeOK [[]] []                                             -- empty clause
#eval bridgeOK [[(true,0)]] [0]                                    -- 1-clause
#eval bridgeOK [[(true,0),(false,1)]] [1]                          -- 2-clause
#eval bridgeOK [[(true,0),(false,1),(true,2),(false,3)]] [2]       -- 4-clause
#eval bridgeOK [[(true,0),(false,1),(true,2)], [(true,5)]] [0,5]   -- mixed
#eval bridgeOK [[(true,5)], [(true,0),(false,1),(true,2)]] [3]     -- bad first
#eval bridgeOK [[(true,0),(false,1),(true,2)], [],
                [(true,0),(false,1),(true,2)]] []                  -- empty mid

/-- Exhaustive-ish grid: all bridge checks above must be `true`. -/
def allOK : Bool :=
  [ bridgeOK [] [],
    bridgeOK [[(true,0),(false,1),(true,2)]] [0,2],
    bridgeOK [[(true,0),(false,1),(true,2)]] [],
    bridgeOK [[(true,3),(true,3),(false,0)], [(false,2),(true,1),(true,4)]] [1,3],
    bridgeOK [[]] [],
    bridgeOK [[(true,0)]] [0],
    bridgeOK [[(true,0),(false,1)]] [1],
    bridgeOK [[(true,0),(false,1),(true,2),(false,3)]] [2],
    bridgeOK [[(true,0),(false,1),(true,2)], [(true,5)]] [0,5],
    bridgeOK [[(true,5)], [(true,0),(false,1),(true,2)]] [3],
    bridgeOK [[(true,0),(false,1),(true,2)], [], [(true,0),(false,1),(true,2)]] []
  ].all id

#eval allOK  -- expect: true

end KCnf3Probe
