import Complexity.NP.SAT.CookLevin.Reductions.BinaryCC_to_FSAT_free_run
import Complexity.NP.SAT.CookLevin.Reductions.HeadLayout

set_option autoImplicit false

/-! # C8-3 — the `Cmd` building blocks of the per-`Q` front program `W_Q`

The three reusable pieces every per-`Q` front witness (the honest replacement
of `hasDeciderClassical`, C8-4) assembles from, each with a run/frame lemma
(and a cost bound where it is cheap to state now):

1. **`emitConst`** — the constant-machine emitter: `dst := bits`, one append
   per cell of a per-`Q` literal list. Funds the machine register (`M_Q` is a
   constant per `Q`) and every fixed marker/separator segment of the head
   layout. Built on `appendConst`, whose seed-`Cmd` parameter lets constant
   tails glue onto a preceding program without a `nop`.
2. **`unaryMonomial`** — `dst := 1^(c·(n+1)^k + d)` from `src = 1^n`: the
   concrete overshoot monomial for the hypothesis's abstract `inOPoly` bounds
   (finding F6; funds the `maxSize x`/`steps x` registers). The `k`-fold
   multiply (`powLoop`/`mulStep`) consumes the proven
   `BinaryCCFSATFree.unaryMulLoop_run` — not re-derived.
3. **`reencLoop`** — the per-symbol re-encoder: drain a bit register and
   append, per bit `b`, the sentinel item `1 1^(b+off) 0` of the symbol
   `b + off` (`HeadLayout.encSyms` of the `(· + off)`-shifted stream).
   `off = 1` is the `Compile.shiftReg` cell shift that `s_x = 3 ::
   encodeRegs (encX x)` needs (the C8-4 tape prefix); `off = 0` is the raw
   symbol stream (the `C8SeamProbe` toy). The offset is a per-`Q` constant,
   so C8-4 picks it per segment — the shift question is surfaced at the
   assembly, not hard-coded here.

Registers are lemma parameters throughout (the `unaryMulLoop_run` style):
C8-4 owns the register map. Probe: `probes/C8FrontProbe.lean` (`#eval`,
register-exact against the pure models, including the `headEncodeIn` frame
rebuilt from these pieces — run it after any change here).
-/

namespace FrontPieces

open Complexity.Lang

/-! ## Piece 1 — the constant emitter -/

/-- The cell an append op writes for the constant bit `b` (`1` iff `b = 1`) —
the pure model of `appendBit`. -/
def bitVal (b : Nat) : Nat := if b = 1 then 1 else 0

/-- One constant-cell append (`appendOne` for a `1`-cell, `appendZero`
otherwise). -/
def appendBit (dst : Var) (b : Nat) : Cmd :=
  Cmd.op (if b = 1 then .appendOne dst else .appendZero dst)

/-- Append the constant `bits` to `dst` after running `c0`. The seed carries
the preceding program (there is no `nop` in `Cmd`), so a constant tail can be
glued onto any command — `emitConst` and `unaryMonomial`'s `+ d` tail are both
instances. -/
def appendConst (c0 : Cmd) (dst : Var) (bits : List Nat) : Cmd :=
  bits.foldl (fun c b => c ;; appendBit dst b) c0

/-- **The constant emitter** (C8-3 piece 1): `dst := bits.map bitVal` — for a
bit-level constant (all cells ≤ 1), `dst := bits` exactly. One `clear` + one
append per cell; cost `1 + 2·|bits|`, frame `dst`-only. -/
def emitConst (dst : Var) (bits : List Nat) : Cmd :=
  appendConst (Cmd.op (.clear dst)) dst bits

/-! ## Piece 3's per-item core — the sentinel item append -/

/-- Append the sentinel item `1 1^v 0` of symbol `v` (the `HeadLayout.encSyms`
item shape) to `dst`. -/
def appendItem (dst : Var) (v : Nat) : Cmd :=
  appendConst (Cmd.op (.appendOne dst)) dst (List.replicate v 1 ++ [0])

/-! ## Piece 3 — the per-symbol re-encoder -/

/-- One re-encoder step: pop the head bit `b` off `scan` and append the
sentinel item of the shifted symbol `b + off` to `dst`. -/
def reencBody (off : Nat) (scan dst tflg : Var) : Cmd :=
  Cmd.op (.head tflg scan) ;; Cmd.op (.tail scan scan) ;;
  Cmd.ifBit tflg (appendItem dst (1 + off)) (appendItem dst off)

/-- **The per-symbol re-encoder** (C8-3 piece 3): append
`HeadLayout.encSyms ((State.get s src).map (· + off))` to `dst`, draining a
working copy of `src` in `scan`. `src` itself is untouched (it is only read
by the leading `copy`); `scan`/`tflg`/`cnt` are scratch and exit dirty
(`scan` exits `[]`). -/
def reencLoop (off : Nat) (cnt scan tflg src dst : Var) : Cmd :=
  Cmd.op (.copy scan src) ;;
  Cmd.forBnd cnt scan (reencBody off scan dst tflg)

/-! ## Piece 2 — the unary monomial evaluator -/

/-- One multiply step of the power loop: `acc := 1^(|base| · a)` from
`acc = 1^a`, through the scratch product register `tmp` (the proven
`unaryMulLoop_run` shape — `forBnd cnt base (concat tmp tmp acc)`). -/
def mulStep (cnt base tmp acc : Var) : Cmd :=
  Cmd.op (.clear tmp) ;;
  Cmd.forBnd cnt base (Cmd.op (.concat tmp tmp acc)) ;;
  Cmd.op (.copy acc tmp)

/-- `acc := 1^(a · m^k)` from `acc = 1^a`, `base = 1^m`: `k`-fold `mulStep`
(`k` is a per-`Q` constant, so the fold is meta-level). The `k = 0` case is
the get-level identity `copy acc acc`. -/
def powLoop (cnt base tmp acc : Var) : Nat → Cmd
  | 0 => Cmd.op (.copy acc acc)
  | k + 1 => powLoop cnt base tmp acc k ;; mulStep cnt base tmp acc

/-- **The unary monomial evaluator** (C8-3 piece 2):
`dst := 1^(c·(n+1)^k + d)` from `src = 1^n` — build `base = 1^(n+1)`, seed
`dst = 1^c`, multiply by `base` `k` times, append `d` ones. `base`/`tmp`/`cnt`
are scratch and exit dirty. -/
def unaryMonomial (c k d : Nat) (cnt base tmp src dst : Var) : Cmd :=
  appendConst
    (Cmd.op (.copy base src) ;; Cmd.op (.appendOne base) ;;
     emitConst dst (List.replicate c 1) ;;
     powLoop cnt base tmp dst k)
    dst (List.replicate d 1)

end FrontPieces
