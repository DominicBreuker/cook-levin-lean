import Complexity.Lang.PolyTime
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP
import Complexity.NP.SAT.CookLevin.Reductions.HeadLayout

/-! # C8 scoping probe — the per-`Q` front witness's seam into the chain head

**Bottom-up C8 scoping session (2026-07-04).** Additive `#eval` probe for
standing architecture risk #2 as it applies to C8: *can the per-`Q` front
witness (the honest replacement of `hasDeciderClassical`) target the chain
head's fixed input layout?* The chain head is the future S1 free witness
`flatSingleTM_reductionLang : PolyTimeComputableLang (FlatSingleTMGenNP-inst →
FlatTCC-inst)`; its input type is `flatTM × List Nat × Nat × Nat`. That
witness does not exist yet, so this probe **pins a candidate natural layout**
(`headEncodeIn` below) and validates that a `Cmd` can hit it register-exactly.

What the per-`Q` front program must produce from `encX x` (the hypothesis
verifier's own x-part layout — the only honest access to an abstract `x : Y`):

1. **the machine `M_Q`** — a CONSTANT per `Q` (the compiled+padded verifier,
   wrapped accept-by-halting), emitted verbatim by an `emitBits` append chain;
2. **`s_x`** — a re-encoding of `encX x` into the instance's tape prefix
   (per-symbol expansion, the `expandSent` shape from `FlatCCBinProbe`);
3. **`maxSize x` / `steps x`** — unary values of concrete monomials
   (the abstract `inOPoly` bounds are overshot by `c·(n+1)^k` with `c`,`k`
   extracted classically ONCE per `Q`; the `Cmd` computes the monomial with
   the proven unary-multiplication loop shape);
4. **a scrubbed frame** — every register `< headRegBound` equal to
   `headEncodeIn (fQ x)`, scratch parked `≥ headRegBound` (seam discipline).

The probe builds a toy instance of exactly these four mechanisms and checks
`AgreeBelow headRegBound` against an independently defined `headEncodeIn`
(the `FlatCCBinProbe.checkBridge` pattern), plus the `enc_bit` obligation
(all emitted cells ∈ {0,1}).

**Also recorded here (found while scoping, machine-checked at the bottom):**
the current Lean `FlatSingleTMGenNP` demands `list_ofFlatType 1 s` — every
symbol of `s` and `cert` `< 1`, i.e. all-zeros. The Coq original demands
`list_ofFlatType (sig M) s` (+ `tapes M = 1`). Under the Lean version no
data-carrying instance exists (information could only live in the LENGTH,
which is exponentially wasteful), so the type must be corrected to the Coq
form before C8/S1 build sessions.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/C8SeamProbe.lean`
-/

open Complexity.Lang

namespace C8SeamProbe

/-! ## The chain-head input layout — now FROZEN in built code

**2026-07-18**: the layout this probe pinned as a candidate is FROZEN as
`Reductions/HeadLayout.lean` (`HeadLayout.headEncodeIn`, with the
`enc_bit` certification `headEncodeIn_bitState`). The probe consumes the
frozen definitions, so it cannot drift from the built contract. -/

open HeadLayout (encMoveN encOptN flattenEntry flattenTM encSyms
  headRegBound headEncodeIn)

-- the frozen frame is what this probe validated
example : headRegBound = 5 := rfl

/-! ## The toy per-`Q` front program

Toy `Q` over `Y := Nat` with `encX n := [1^n]` in register 0 (stand-in for
the hypothesis verifier's x-part layout). The front map is
`fQ n := (M0, 1^n-as-symbols, 2·n+3, (n+1)²)` — a constant machine, a
per-symbol re-encoded input, one linear and one *quadratic* unary parameter
(the quadratic exercises the mul-loop mechanism the real `steps x` needs). -/

/-- The constant stand-in machine (in the real C8 this is the compiled,
padded, accept-by-halting-wrapped verifier of the hypothesis witness). -/
def M0 : FlatTM :=
  { sig := 4, tapes := 1, states := 2,
    trans := [⟨0, [some 3], 1, [some 3], [.Nmove]⟩],
    start := 0, halt := [false, true] }

def fQ (n : Nat) : FlatTM × List Nat × Nat × Nat :=
  (M0, List.replicate n 1, 2 * n + 3, (n + 1) * (n + 1))

/-! Registers of the toy program. Scratch strictly `≥ headRegBound`. -/
def IN    : Var := 0
def MREG  : Var := 1
def SREG  : Var := 2
def MAXR  : Var := 3
def STEPR : Var := 4
def IDX   : Var := 5
def BREG  : Var := 6

/-- Emit a constant bit list into `dst` (clear, then one append per bit).
Cost/size linear in the constant — fine, the constant is per-`Q` fixed. -/
def emitBits (dst : Var) (bits : List Nat) : Cmd :=
  bits.foldl
    (fun c b => c ;; Cmd.op (if b = 1 then .appendOne dst else .appendZero dst))
    (Cmd.op (.clear dst))

/-- The toy front program: input `IN = 1^n`, output regs 1–4 in the head
layout, reg 0 scrubbed (the seam `mfc` here is folded into the program —
the real witness may split it out). -/
def buildFront : Cmd :=
  -- reg 1: the constant machine
  emitBits MREG (encSyms (flattenTM M0)) ;;
  -- reg 2: per-symbol sentinel expansion of the input (symbol 1 ↦ [1,1,0])
  Cmd.op (.clear SREG) ;;
  Cmd.forBnd IDX IN
    (Cmd.op (.appendOne SREG) ;; Cmd.op (.appendOne SREG) ;;
     Cmd.op (.appendZero SREG)) ;;
  -- reg 3: maxSize = 2n+3 unary
  Cmd.op (.clear MAXR) ;;
  Cmd.forBnd IDX IN (Cmd.op (.appendOne MAXR) ;; Cmd.op (.appendOne MAXR)) ;;
  Cmd.op (.appendOne MAXR) ;; Cmd.op (.appendOne MAXR) ;; Cmd.op (.appendOne MAXR) ;;
  -- reg 4: steps = (n+1)² unary, via the proven mul-loop shape
  Cmd.op (.copy BREG IN) ;; Cmd.op (.appendOne BREG) ;;
  Cmd.op (.clear STEPR) ;;
  Cmd.forBnd IDX BREG (Cmd.op (.concat STEPR STEPR BREG)) ;;
  -- scrub: head layout has [] at reg 0
  Cmd.op (.clear IN)

def encX (n : Nat) : State := [List.replicate n 1]

/-! ## The checks -/

/-- Boolean `AgreeBelow k`. -/
def agreeBelowB (k : Nat) (s t : State) : Bool :=
  (List.range k).all (fun r => State.get s r == State.get t r)

/-- The seam-targeting check: the program's exit frame equals the head's own
encoding of the front instance, register by register on the head frame. -/
def checkBridge (n : Nat) : Bool :=
  agreeBelowB headRegBound (buildFront.eval (encX n)) (headEncodeIn (fQ n))

/-- The `enc_bit` obligation on the produced frame: all cells ∈ {0,1}. -/
def checkBits (n : Nat) : Bool :=
  ((buildFront.eval (encX n)).take headRegBound).all (fun reg => reg.all (· < 2))

#eval checkBridge 0   -- expect true
#eval checkBridge 1   -- expect true
#eval checkBridge 2   -- expect true
#eval checkBridge 5   -- expect true
#eval checkBits 0     -- expect true
#eval checkBits 5     -- expect true

/-! ## The `list_ofFlatType 1` finding, machine-checked

Any data-carrying `s` (here: the canonical machine flattening, or even the
single symbol `1`) violates the CURRENT `FlatSingleTMGenNP`'s
`list_ofFlatType 1 s` (all symbols `< 1`). The Coq original requires
`list_ofFlatType (sig M) s`. -/

#eval (encSyms (flattenTM M0)).all (fun x => decide (x < 1))  -- expect false
#eval [1].all (fun x => decide (x < 1))                        -- expect false
#eval (encSyms (flattenTM M0)).all (fun x => decide (x < 4))  -- expect true (Coq form, sig = 4)

-- Summary verdict.
#eval ([0, 1, 2, 5].all (fun n => checkBridge n && checkBits n))
  && !((encSyms (flattenTM M0)).all (fun x => decide (x < 1)))

end C8SeamProbe
