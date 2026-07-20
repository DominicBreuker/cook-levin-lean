import Complexity.NP.SAT.CookLevin.Reductions.FrontPieces

set_option autoImplicit false

/-! # C8-4 piece 2 — the reduction program emitting `fQ x`'s four registers

The honest reduction map `W_Q : Q ⪯p' FlatSingleTMGenNP` computes, from an
encoding of `x`, the four registers of the front instance
`fQ x = (M_Q, s_x, maxSize x, steps x)` laid out as `HeadLayout.headEncodeIn`
(regs 0–4). This module builds that program by **wiring the C8-3 gadgets**
(`emitConst`/`emitRegs`/`unaryMonomial` from `FrontPieces`) and proves the
register-exact run lemma `frontProgram_run` (the correctness crux of the
witness's `computes` field, piece 3).

## ⚠ Design finding (2026-07-20-c) — the F6 monomial argument

`fQ_correct`'s domination hypotheses `hmax`/`hsteps` (`FrontLifting.lean`)
require the emitted `maxSize x`/`steps x` registers to **dominate** budgets in
`encodable.size x` (via `certBoundOf`, `MQbudget ≤ dCap (size x)`). The earlier
plan (HANDOFF, `tallyCells`) fed the monomials `1^(State.size (encX x))` — a
value with only an **upper** bound to `size x` (`encX_size`), never a lower
bound (`encX` need not be injective — it only separates Q-values). No monomial
in that tally can be *proven* to dominate a `size x`-budget. The plan was
internally inconsistent (it demanded both "monomial ≥ stepsOf (size x)" and
"argument = tally"); `FrontLifting` had punted this exact obligation to piece 2.

**Resolution (Option A):** the reduction's input layout carries the input size
in unary — `encodeIn x = encX x ++ [1^(encodable.size x)]` (a unary size
register at index `xWidth`). This is honest (a poly-time reduction may read its
own input's size) and **local to `W_Q`** — it leaves the frozen C8-0 interface
`InNPWitnessLangFreeSplit` untouched. The monomial argument is then genuinely
`size x`, so the domination direction is correct and the F6 overshoot is
provable from `maxSizeOf_poly`/`stepsOf_poly`. (This relaxes the HANDOFF's
"`W_Q.encodeIn` MUST be `encX` verbatim" note; the `tallyCells` gadget is now
unused by C8-4. See the HANDOFF C8-4 section for the alternative, Option B: a
structural lower-bound field on the interface.)

## Register map

Scratch base `B` (`5 ≤ B`, `xWidth < B`; the witness picks
`B := max headRegBound (xWidth + 1)`). Input `s = encX x ++ [1^m]`: regs
`0..xWidth-1` are `encX x`, reg `xWidth` is the size register `1^m`.

| reg          | role                                             |
|--------------|--------------------------------------------------|
| `0..xWidth-1`| input `encX x` (read-only)                        |
| `xWidth`     | size register `1^m` (read-only)                   |
| `B`          | `SX` — `s_x` stream scratch                       |
| `B+1`,`B+2`  | `MX`,`ST` — the two budget monomials              |
| `B+3`        | `MC` — the machine constant                       |
| `B+4..B+8`   | `cnt`,`scan`,`tflg`,`base`,`tmp` — gadget scratch |

Output regs 0–4 hold `headEncodeIn (M_Q, s_x, Mmax, Mstep)`; scratch (`≥ B`)
exits dirty but is invisible to `decodeOut` and to the C8-5 seam
(`AgreeBelow headRegBound`).
-/

namespace FrontProgram

open Complexity.Lang FrontPieces
open HeadLayout (encSyms)

/-- **The C8-4 reduction program.** `MQconst = encSyms (flattenTM M_Q)` (a
per-`Q` constant); `xWidth` is the input width; `B` the scratch base; the six
`cm km dm`/`cs ks ds` are the F6 overshoot-monomial constants for
`maxSize`/`steps`. Builds `s_x`/the two budgets/the machine into scratch, then
moves them into output registers 0–4. -/
def frontProgram (MQconst : List Nat) (xWidth B : Nat)
    (cm km dm cs ks ds : Nat) : Cmd :=
  emitRegs (B + 4) (B + 5) (B + 6) B (List.range xWidth) ;;
  unaryMonomial cm km dm (B + 4) (B + 7) (B + 8) xWidth (B + 1) ;;
  unaryMonomial cs ks ds (B + 4) (B + 7) (B + 8) xWidth (B + 2) ;;
  emitConst (B + 3) MQconst ;;
  Cmd.op (.clear 0) ;;
  Cmd.op (.copy 1 (B + 3)) ;;
  Cmd.op (.copy 2 B) ;;
  Cmd.op (.copy 3 (B + 1)) ;;
  Cmd.op (.copy 4 (B + 2))

/-- **`frontProgram` is register-exact.** With the input split as
`encX x` (bit-level regs `0..xWidth-1`) followed by the size register
`1^m` at `xWidth`, the output registers 0–4 are exactly
`headEncodeIn (M_Q, 3 :: encodeRegs (encX x), cm·(m+1)^km+dm, cs·(m+1)^ks+ds)`.
This is the `computes` crux of the C8-4 witness (piece 3). -/
theorem frontProgram_run (MQconst : List Nat) (xWidth B : Nat)
    (cm km dm cs ks ds : Nat) (s : State) (m : Nat)
    (hB : 5 ≤ B) (hxW : xWidth < B)
    (hMQ : ∀ x ∈ MQconst, x ≤ 1)
    (hsize : State.get s xWidth = List.replicate m 1)
    (hbits : ∀ src ∈ List.range xWidth, ∀ x ∈ State.get s src, x ≤ 1) :
    State.get ((frontProgram MQconst xWidth B cm km dm cs ks ds).eval s) 0 = []
    ∧ State.get ((frontProgram MQconst xWidth B cm km dm cs ks ds).eval s) 1 = MQconst
    ∧ State.get ((frontProgram MQconst xWidth B cm km dm cs ks ds).eval s) 2
        = encSyms (3 :: Compile.encodeRegs ((List.range xWidth).map (State.get s)))
    ∧ State.get ((frontProgram MQconst xWidth B cm km dm cs ks ds).eval s) 3
        = List.replicate (cm * (m + 1) ^ km + dm) 1
    ∧ State.get ((frontProgram MQconst xWidth B cm km dm cs ks ds).eval s) 4
        = List.replicate (cs * (m + 1) ^ ks + ds) 1 := by
  -- distinctness facts (concrete registers; `omega` from `5 ≤ B`, `xWidth < B`).
  -- ⚠ each must be TYPE-ASCRIBED: an un-ascribed `by omega` in a gadget-call
  -- argument runs against a still-metavariable goal (`?scan ≠ ?cnt`) and fails.
  have hdist : ∀ src ∈ List.range xWidth,
      (src : Var) ≠ B ∧ src ≠ B + 5 ∧ src ≠ B + 6 ∧ src ≠ B + 4 := by
    intro src hsrc
    have : src < xWidth := List.mem_range.mp hsrc
    exact ⟨by omega, by omega, by omega, by omega⟩
  -- stage 1: emitRegs → s1, reg B = encSyms (3 :: encodeRegs (input regs))
  obtain ⟨hR1, hR2⟩ := emitRegs_run (B + 4) (B + 5) (B + 6) B (List.range xWidth) s
    (by omega : (B + 5 : Var) ≠ B + 4) (by omega : (B + 5 : Var) ≠ B)
    (by omega : (B + 5 : Var) ≠ B + 6) (by omega : (B : Var) ≠ B + 4)
    (by omega : (B : Var) ≠ B + 6) hdist hbits
  set s1 := (emitRegs (B + 4) (B + 5) (B + 6) B (List.range xWidth)).eval s with hs1
  -- (after each `set`, the gadget's run/frame hyps are folded to be about `sᵢ`)
  have hs1_size : State.get s1 xWidth = List.replicate m 1 := by
    rw [hR2 xWidth (by omega : (xWidth : Var) ≠ B) (by omega : (xWidth : Var) ≠ B + 5)
      (by omega : (xWidth : Var) ≠ B + 6) (by omega : (xWidth : Var) ≠ B + 4), hsize]
  -- stage 2: unaryMonomial → s2, reg B+1 = 1^(cm·(m+1)^km+dm)
  obtain ⟨hM1, hM2, -⟩ := unaryMonomial_run cm km dm (B + 4) (B + 7) (B + 8) xWidth (B + 1)
    s1 m (by omega : (B + 7 : Var) ≠ B + 1) (by omega : (B + 7 : Var) ≠ B + 8)
    (by omega : (B + 7 : Var) ≠ B + 4) (by omega : (B + 1 : Var) ≠ B + 8)
    (by omega : (B + 1 : Var) ≠ B + 4) (by omega : (B + 8 : Var) ≠ B + 4) hs1_size
  set s2 := (unaryMonomial cm km dm (B + 4) (B + 7) (B + 8) xWidth (B + 1)).eval s1 with hs2
  have hs2_size : State.get s2 xWidth = List.replicate m 1 := by
    rw [hM2 xWidth (by omega : (xWidth : Var) ≠ B + 1) (by omega : (xWidth : Var) ≠ B + 7)
      (by omega : (xWidth : Var) ≠ B + 8) (by omega : (xWidth : Var) ≠ B + 4), hs1_size]
  have hs2_SX : State.get s2 B = State.get s1 B :=
    hM2 B (by omega : (B : Var) ≠ B + 1) (by omega : (B : Var) ≠ B + 7)
      (by omega : (B : Var) ≠ B + 8) (by omega : (B : Var) ≠ B + 4)
  -- stage 3: unaryMonomial → s3, reg B+2 = 1^(cs·(m+1)^ks+ds)
  obtain ⟨hN1, hN2, -⟩ := unaryMonomial_run cs ks ds (B + 4) (B + 7) (B + 8) xWidth (B + 2)
    s2 m (by omega : (B + 7 : Var) ≠ B + 2) (by omega : (B + 7 : Var) ≠ B + 8)
    (by omega : (B + 7 : Var) ≠ B + 4) (by omega : (B + 2 : Var) ≠ B + 8)
    (by omega : (B + 2 : Var) ≠ B + 4) (by omega : (B + 8 : Var) ≠ B + 4) hs2_size
  set s3 := (unaryMonomial cs ks ds (B + 4) (B + 7) (B + 8) xWidth (B + 2)).eval s2 with hs3
  have hs3_SX : State.get s3 B = State.get s1 B := by
    rw [hN2 B (by omega : (B : Var) ≠ B + 2) (by omega : (B : Var) ≠ B + 7)
      (by omega : (B : Var) ≠ B + 8) (by omega : (B : Var) ≠ B + 4), hs2_SX]
  have hs3_MX : State.get s3 (B + 1) = List.replicate (cm * (m + 1) ^ km + dm) 1 := by
    rw [hN2 (B + 1) (by omega : (B + 1 : Var) ≠ B + 2) (by omega : (B + 1 : Var) ≠ B + 7)
      (by omega : (B + 1 : Var) ≠ B + 8) (by omega : (B + 1 : Var) ≠ B + 4), hM1]
  -- stage 4: emitConst → s4, reg B+3 = MQconst
  obtain ⟨-, hC2, -⟩ := emitConst_run (B + 3) MQconst s3
  set s4 := (emitConst (B + 3) MQconst).eval s3 with hs4
  have hs4_MC : State.get s4 (B + 3) = MQconst :=
    emitConst_run_bits (B + 3) MQconst s3 hMQ
  have hs4_SX : State.get s4 B = encSyms (3 :: Compile.encodeRegs ((List.range xWidth).map (State.get s))) := by
    rw [hC2 B (by omega : (B : Var) ≠ B + 3), hs3_SX, hR1]
  have hs4_MX : State.get s4 (B + 1) = List.replicate (cm * (m + 1) ^ km + dm) 1 := by
    rw [hC2 (B + 1) (by omega : (B + 1 : Var) ≠ B + 3), hs3_MX]
  have hs4_ST : State.get s4 (B + 2) = List.replicate (cs * (m + 1) ^ ks + ds) 1 := by
    rw [hC2 (B + 2) (by omega : (B + 2 : Var) ≠ B + 3), hN1]
  -- ⚠ `omega` whnf-chokes on the `set`-bound states (`let`s over big `eval`
  -- terms); clear their bodies (the `hsᵢ` equations survive) before the
  -- distinctness bundle below.
  clear_value s1 s2 s3 s4
  -- the program = the four gadgets (evaluated to `s4`) followed by the copy block
  have hps : (frontProgram MQconst xWidth B cm km dm cs ks ds).eval s
      = (Cmd.op (.clear 0) ;; Cmd.op (.copy 1 (B + 3)) ;; Cmd.op (.copy 2 B) ;;
         Cmd.op (.copy 3 (B + 1)) ;; Cmd.op (.copy 4 (B + 2))).eval s4 := by
    show (emitRegs (B + 4) (B + 5) (B + 6) B (List.range xWidth) ;; _).eval s = _
    rw [Cmd.eval_seq, ← hs1, Cmd.eval_seq, ← hs2, Cmd.eval_seq, ← hs3, Cmd.eval_seq, ← hs4]
  -- the copy block reduces to the explicit output state; each copy read survives
  -- the earlier writes (`B+k` distinct from `0..k-1`, ascribed single `≠` omegas).
  have hpost : (Cmd.op (.clear 0) ;; Cmd.op (.copy 1 (B + 3)) ;; Cmd.op (.copy 2 B) ;;
        Cmd.op (.copy 3 (B + 1)) ;; Cmd.op (.copy 4 (B + 2))).eval s4
      = (((((s4.set 0 []).set 1 (State.get s4 (B + 3))).set 2 (State.get s4 B)).set 3
          (State.get s4 (B + 1))).set 4 (State.get s4 (B + 2))) := by
    have r1 : State.get (s4.set 0 []) (B + 3) = State.get s4 (B + 3) :=
      State.get_set_ne _ _ _ _ (by omega : (B + 3 : Var) ≠ 0)
    have r2 : State.get ((s4.set 0 []).set 1 (State.get s4 (B + 3))) B = State.get s4 B :=
      (State.get_set_ne _ _ _ _ (by omega : (B : Var) ≠ 1)).trans
        (State.get_set_ne _ _ _ _ (by omega : (B : Var) ≠ 0))
    have r3 : State.get (((s4.set 0 []).set 1 (State.get s4 (B + 3))).set 2
          (State.get s4 B)) (B + 1) = State.get s4 (B + 1) :=
      (State.get_set_ne _ _ _ _ (by omega : (B + 1 : Var) ≠ 2)).trans
        ((State.get_set_ne _ _ _ _ (by omega : (B + 1 : Var) ≠ 1)).trans
          (State.get_set_ne _ _ _ _ (by omega : (B + 1 : Var) ≠ 0)))
    have r4 : State.get ((((s4.set 0 []).set 1 (State.get s4 (B + 3))).set 2
          (State.get s4 B)).set 3 (State.get s4 (B + 1))) (B + 2) = State.get s4 (B + 2) :=
      (State.get_set_ne _ _ _ _ (by omega : (B + 2 : Var) ≠ 3)).trans
        ((State.get_set_ne _ _ _ _ (by omega : (B + 2 : Var) ≠ 2)).trans
          ((State.get_set_ne _ _ _ _ (by omega : (B + 2 : Var) ≠ 1)).trans
            (State.get_set_ne _ _ _ _ (by omega : (B + 2 : Var) ≠ 0))))
    simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, r1, r2, r3, r4]
  rw [hps, hpost]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [State.get_set_ne _ _ _ _ (by decide : (0 : Var) ≠ 4),
        State.get_set_ne _ _ _ _ (by decide : (0 : Var) ≠ 3),
        State.get_set_ne _ _ _ _ (by decide : (0 : Var) ≠ 2),
        State.get_set_ne _ _ _ _ (by decide : (0 : Var) ≠ 1), State.get_set_eq]
  · rw [State.get_set_ne _ _ _ _ (by decide : (1 : Var) ≠ 4),
        State.get_set_ne _ _ _ _ (by decide : (1 : Var) ≠ 3),
        State.get_set_ne _ _ _ _ (by decide : (1 : Var) ≠ 2), State.get_set_eq, hs4_MC]
  · rw [State.get_set_ne _ _ _ _ (by decide : (2 : Var) ≠ 4),
        State.get_set_ne _ _ _ _ (by decide : (2 : Var) ≠ 3), State.get_set_eq, hs4_SX]
  · rw [State.get_set_ne _ _ _ _ (by decide : (3 : Var) ≠ 4), State.get_set_eq, hs4_MX]
  · rw [State.get_set_eq, hs4_ST]

end FrontProgram
