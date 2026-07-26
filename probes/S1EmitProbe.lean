import Complexity.NP.SAT.CookLevin.Reductions.S1Emit

/-! # S1 probe — the emitter stages **Σ**, **F** (and, when it lands, **I**)

End-to-end `#eval` of the emitter stages against the values the S1 witness's
output key demands, on the same test machines as `probes/S1CardModelProbe.lean`.
Project methodology: probe the machine before (and after) proving its run lemma —
a green `#eval` on a real instance catches a layout slip that a type-correct
proof of the wrong statement would not.

§1 stage Σ: `EOUT_S = 1^(PSg M)`;
§2 stage F: `EOUT_F = encFinal (flattenFinal (guessFinal M))`;
§3 stage I: `EOUT_I = encNats (flattenString (preludeRow M s maxSize steps))`;
§4 scale: emitted register lengths (the cost ladder's raw numbers).

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1EmitProbe.lean`
-/

open Complexity.Lang Complexity.Simulators S1Emit

/-! ## Test machines -/

def eM0 : FlatTM :=
  { sig := 2, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some 0],
                dst_state := 1, dst_write_vals := [some 1],
                move_dirs := [TMMove.Rmove] }] }

/-- Three states, two of them halting. -/
def eM1 : FlatTM :=
  { eM0 with sig := 3, states := 3, halt := [false, true, true] }

/-- Degenerate alphabet, no halting state. -/
def eM2 : FlatTM :=
  { eM0 with sig := 0, states := 2, halt := [false, false], trans := [] }

/-- A machine whose halt list is SHORTER than `states` (invalid, but the
emitter must still agree with `M.halt.getD`). -/
def eM3 : FlatTM := { eM0 with states := 4, halt := [false, true] }

def eMs : List FlatTM := [eM0, eM1, eM2, eM3]

/-! ## The post-P/G state

Stages Σ / F read only `PSIG`, `PSTATES`, `PHALT`; stage I also reads the head
layout's registers `2` (`encSyms s`), `3` (`1^maxSize`) and `4` (`1^steps`). -/

def mkState (M : FlatTM) (s : List Nat) (maxSize steps : Nat) : State :=
  State.set (State.set (State.set (State.set (State.set (State.set
    ([] : State) 2 (HeadLayout.encSyms s)) 3 (List.replicate maxSize 1))
    4 (List.replicate steps 1)) S1Parse.PSIG (List.replicate M.sig 1))
    S1Parse.PSTATES (List.replicate M.states 1))
    S1Parse.PHALT (M.halt.map S1Parse.bitOf)

/-! ## §1 — stage Σ -/

def sigOK (M : FlatTM) : Bool :=
  State.get (stageSig.eval (mkState M [] 0 0)) EOUT_S == List.replicate (PSg M) 1

#eval eMs.map sigOK        -- expect [true, true, true, true]

/-! ## §2 — stage F -/

def finOK (M : FlatTM) : Bool :=
  State.get (stageFin.eval (mkState M [] 0 0)) EOUT_F
    == FlatTCCFree.encFinal (FlatTCC.flattenFinal (guessFinal M))

#eval eMs.map finOK        -- expect [true, true, true, true]

/-- Stage F must not disturb the head layout's registers or stage P's outputs. -/
def finFrameOK (M : FlatTM) : Bool :=
  let s := mkState M [1, 0] 2 3
  let t := stageFin.eval s
  ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List Nat).all
    (fun r => State.get t r == State.get s r)

#eval eMs.map finFrameOK   -- expect [true, true, true, true]

/-! ## §4 — scale

The two small registers: `PSg M` cells for Σ, `Θ(states·σ)` patterns for F. -/

#eval eMs.map (fun M => (PSg M,
  (State.get (stageFin.eval (mkState M [] 0 0)) EOUT_F).length))
