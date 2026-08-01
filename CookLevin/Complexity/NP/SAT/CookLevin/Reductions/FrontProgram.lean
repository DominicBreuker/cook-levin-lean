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

## ⚠ Design history — the F6 monomial argument, and its 2026-08-02 fix

`fQ_correct`'s domination hypotheses `hmax`/`hsteps` (`FrontLifting.lean`)
require the emitted `maxSize x`/`steps x` registers to **dominate** budgets in
`encodable.size x` (via `certBoundOf`, `MQbudget ≤ dCap (size x)`). The original
plan fed the monomials `1^(State.size (encX x))` — counted on-machine by
`FrontPieces.tallyCells` — and 2026-07-20-c found it *unprovable*: that tally
had only an **upper** bound to `size x` (`encX_size`), never a lower one, so no
monomial in it could be shown to dominate a `size x`-budget. The stop-gap
(Option A) was to have the reduction's input layout **hand over** the size:
`encodeIn x = encX x ++ [1^(encodable.size x)]`.

That stop-gap is now gone. `InNPWitnessLangFreeSplit` carries a `sizeLB` field
since 2026-08-02 (`Lang/PolyTime.lean`) — `encodable.size x ≤ sizeLB (State.size
(encX x))`, the missing lower bound, which the §7 cheat of
`probes/HonestyAuditProbe.lean` could not satisfy and an honest layout gets for
free. With it, `maxSizeOf ∘ sizeLB` and `stepsOf ∘ sizeLB` are still
polynomials, so `inOPoly_monomial_bound` extracts overshoot monomials **in the
tally** rather than in `size x`, and `tallyCells` — built and proven in 2026-07,
then parked as UNUSED for two weeks — finally does the job it was built for.

**The point is not the register, it is the statement.** The composite
reduction's `ComputesBy.encode` is now `W.encX` itself, with nothing appended;
under `NPhardStr` that is literally `certState`, the raw input string. There is
nothing at the head of the chain left for an auditor to read.

## Register map

Scratch base `B` (`5 ≤ B`, `xWidth < B`; the witness picks
`B := max headRegBound (xWidth + 1)`). The input is `encX x` and *only* that:
regs `0..xWidth-1`, nothing else.

| reg          | role                                             |
|--------------|--------------------------------------------------|
| `0..xWidth-1`| input `encX x` (read-only)                        |
| `B`          | `SX` — `s_x` stream scratch                       |
| `B+1`,`B+2`  | `MX`,`ST` — the two budget monomials              |
| `B+3`        | `MC` — the machine constant                       |
| `B+4..B+8`   | `cnt`,`scan`,`tflg`,`base`,`tmp` — gadget scratch |
| `B+9`        | `TL` — the on-machine input-cell tally `1^m`      |

Output regs 0–4 hold `headEncodeIn (M_Q, s_x, Mmax, Mstep)`; scratch (`≥ B`)
exits dirty but is invisible to `decodeOut` and to the C8-5 seam
(`AgreeBelow headRegBound`).

⚠ The tally runs **first**: `tallyCells` writes only `B+9`/`B+4`, so the input
registers it read are still intact for `emitRegs`, and `B+9` then survives both
`emitRegs` (which writes `B`,`B+4`,`B+5`,`B+6`) and either `unaryMonomial`
(which writes `dst`,`B+7`,`B+8`,`B+4`).
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
  tallyCells (B + 4) (B + 9) (List.range xWidth) ;;
  emitRegs (B + 4) (B + 5) (B + 6) B (List.range xWidth) ;;
  unaryMonomial cm km dm (B + 4) (B + 7) (B + 8) (B + 9) (B + 1) ;;
  unaryMonomial cs ks ds (B + 4) (B + 7) (B + 8) (B + 9) (B + 2) ;;
  emitConst (B + 3) MQconst ;;
  Cmd.op (.clear 0) ;;
  Cmd.op (.copy 1 (B + 3)) ;;
  Cmd.op (.copy 2 B) ;;
  Cmd.op (.copy 3 (B + 1)) ;;
  Cmd.op (.copy 4 (B + 2))

/-! ### The tally stage

Shared by the run and cost lemmas: `tallyCells` counts the input's cells into
`B+9` and leaves everything else — in particular the input itself — alone. -/

/-- The input registers are distinct from every scratch register the program
uses (`xWidth < B`). ⚠ `src` is bound at `Nat`, not at `Var`: `Var` is an
`abbrev` that `omega` does not see through, so a `Var`-typed hypothesis
`src < xWidth` is an opaque atom to it. -/
private theorem src_ne (xWidth B : Nat) (hxW : xWidth < B) {src : Nat}
    (hsrc : src ∈ List.range xWidth) :
    src ≠ B ∧ src ≠ B + 5 ∧ src ≠ B + 6 ∧ src ≠ B + 4 ∧ src ≠ B + 9 := by
  have : src < xWidth := List.mem_range.mp hsrc
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- **Stage 0 — the on-machine input-cell tally.** `B+9` holds `1^m` for
`m = Σ_{src < xWidth} |s[src]|`, and every other register (the input included)
is untouched apart from the loop counter `B+4`. -/
theorem tallyStage_run (xWidth B : Nat) (s : State) (m : Nat)
    (hxW : xWidth < B)
    (hsum : ((List.range xWidth).map (fun src => (State.get s src).length)).sum = m) :
    State.get ((tallyCells (B + 4) (B + 9) (List.range xWidth)).eval s) (B + 9)
        = List.replicate m 1
    ∧ (∀ r : Var, r ≠ B + 9 → r ≠ B + 4 →
        State.get ((tallyCells (B + 4) (B + 9) (List.range xWidth)).eval s) r
          = State.get s r) := by
  obtain ⟨h1, h2⟩ := tallyCells_run (B + 4) (B + 9) (List.range xWidth) s
    (by omega : (B + 4 : Var) ≠ B + 9)
    (fun _ hsrc =>
      ⟨(src_ne xWidth B hxW hsrc).2.2.2.2, (src_ne xWidth B hxW hsrc).2.2.2.1⟩)
  exact ⟨by rw [h1, hsum], h2⟩

/-- **`frontProgram` is register-exact.** The input is `encX x` and nothing
else (bit-level regs `0..xWidth-1`); the program counts its cells itself into
`m`, and the output registers 0–4 are exactly
`headEncodeIn (M_Q, 3 :: encodeRegs (encX x), cm·(m+1)^km+dm, cs·(m+1)^ks+ds)`.
This is the `computes` crux of the C8-4 witness (piece 3). -/
theorem frontProgram_run (MQconst : List Nat) (xWidth B : Nat)
    (cm km dm cs ks ds : Nat) (s : State) (m : Nat)
    (hB : 5 ≤ B) (hxW : xWidth < B)
    (hMQ : ∀ x ∈ MQconst, x ≤ 1)
    (hsize : ((List.range xWidth).map (fun src => (State.get s src).length)).sum = m)
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
      (src : Var) ≠ B ∧ src ≠ B + 5 ∧ src ≠ B + 6 ∧ src ≠ B + 4 := fun _ hsrc =>
    let h := src_ne xWidth B hxW hsrc
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  -- stage 0: tallyCells → s0, reg B+9 = 1^m; the input survives
  obtain ⟨hT1, hT2⟩ := tallyStage_run xWidth B s m hxW hsize
  set s0 := (tallyCells (B + 4) (B + 9) (List.range xWidth)).eval s with hs0
  have hget0 : ∀ i ∈ List.range xWidth, State.get s0 i = State.get s i := by
    intro i hi
    have hi' : i < xWidth := List.mem_range.mp hi
    exact hT2 i (by omega : (i : Nat) ≠ B + 9) (by omega : (i : Nat) ≠ B + 4)
  have hmap0 : (List.range xWidth).map (State.get s0)
      = (List.range xWidth).map (State.get s) := List.map_congr_left hget0
  have hbits0 : ∀ src ∈ List.range xWidth, ∀ x ∈ State.get s0 src, x ≤ 1 := by
    intro src hsrc x hx; rw [hget0 src hsrc] at hx; exact hbits src hsrc x hx
  -- stage 1: emitRegs → s1, reg B = encSyms (3 :: encodeRegs (input regs))
  obtain ⟨hR1, hR2⟩ := emitRegs_run (B + 4) (B + 5) (B + 6) B (List.range xWidth) s0
    (by omega : (B + 5 : Var) ≠ B + 4) (by omega : (B + 5 : Var) ≠ B)
    (by omega : (B + 5 : Var) ≠ B + 6) (by omega : (B : Var) ≠ B + 4)
    (by omega : (B : Var) ≠ B + 6) hdist hbits0
  rw [hmap0] at hR1
  set s1 := (emitRegs (B + 4) (B + 5) (B + 6) B (List.range xWidth)).eval s0 with hs1
  -- (after each `set`, the gadget's run/frame hyps are folded to be about `sᵢ`)
  have hs1_size : State.get s1 (B + 9) = List.replicate m 1 := by
    rw [hR2 (B + 9) (by omega : (B + 9 : Var) ≠ B) (by omega : (B + 9 : Var) ≠ B + 5)
      (by omega : (B + 9 : Var) ≠ B + 6) (by omega : (B + 9 : Var) ≠ B + 4), hT1]
  -- stage 2: unaryMonomial → s2, reg B+1 = 1^(cm·(m+1)^km+dm)
  obtain ⟨hM1, hM2, -⟩ := unaryMonomial_run cm km dm (B + 4) (B + 7) (B + 8) (B + 9) (B + 1)
    s1 m (by omega : (B + 7 : Var) ≠ B + 1) (by omega : (B + 7 : Var) ≠ B + 8)
    (by omega : (B + 7 : Var) ≠ B + 4) (by omega : (B + 1 : Var) ≠ B + 8)
    (by omega : (B + 1 : Var) ≠ B + 4) (by omega : (B + 8 : Var) ≠ B + 4) hs1_size
  set s2 := (unaryMonomial cm km dm (B + 4) (B + 7) (B + 8) (B + 9) (B + 1)).eval s1 with hs2
  have hs2_size : State.get s2 (B + 9) = List.replicate m 1 := by
    rw [hM2 (B + 9) (by omega : (B + 9 : Var) ≠ B + 1) (by omega : (B + 9 : Var) ≠ B + 7)
      (by omega : (B + 9 : Var) ≠ B + 8) (by omega : (B + 9 : Var) ≠ B + 4), hs1_size]
  have hs2_SX : State.get s2 B = State.get s1 B :=
    hM2 B (by omega : (B : Var) ≠ B + 1) (by omega : (B : Var) ≠ B + 7)
      (by omega : (B : Var) ≠ B + 8) (by omega : (B : Var) ≠ B + 4)
  -- stage 3: unaryMonomial → s3, reg B+2 = 1^(cs·(m+1)^ks+ds)
  obtain ⟨hN1, hN2, -⟩ := unaryMonomial_run cs ks ds (B + 4) (B + 7) (B + 8) (B + 9) (B + 2)
    s2 m (by omega : (B + 7 : Var) ≠ B + 2) (by omega : (B + 7 : Var) ≠ B + 8)
    (by omega : (B + 7 : Var) ≠ B + 4) (by omega : (B + 2 : Var) ≠ B + 8)
    (by omega : (B + 2 : Var) ≠ B + 4) (by omega : (B + 8 : Var) ≠ B + 4) hs2_size
  set s3 := (unaryMonomial cs ks ds (B + 4) (B + 7) (B + 8) (B + 9) (B + 2)).eval s2 with hs3
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
  clear_value s0 s1 s2 s3 s4
  -- the program = the five gadgets (evaluated to `s4`) followed by the copy block
  have hps : (frontProgram MQconst xWidth B cm km dm cs ks ds).eval s
      = (Cmd.op (.clear 0) ;; Cmd.op (.copy 1 (B + 3)) ;; Cmd.op (.copy 2 B) ;;
         Cmd.op (.copy 3 (B + 1)) ;; Cmd.op (.copy 4 (B + 2))).eval s4 := by
    show (tallyCells (B + 4) (B + 9) (List.range xWidth) ;; _).eval s = _
    rw [Cmd.eval_seq, ← hs0, Cmd.eval_seq, ← hs1, Cmd.eval_seq, ← hs2, Cmd.eval_seq, ← hs3,
      Cmd.eval_seq, ← hs4]
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

/-- **`frontProgram` cost bound.** The whole program's cost decomposes into the
`tallyCells` and `emitRegs` per-input-register sums, the two `unaryMonomial`
stage costs (`monomialCost`, now at the *tally* `m`), the constant `emitConst`,
and the five `clear`/`copy` ops (whose copy sources are the emitted registers,
of lengths `|MQconst|`, `|s_x|`, `Mmax`, `Mstep`). Piece 3's `cQ_cost_le`
consumes this against a single-monomial bound. -/
theorem frontProgram_cost_le (MQconst : List Nat) (xWidth B : Nat)
    (cm km dm cs ks ds : Nat) (s : State) (m : Nat)
    (hB : 5 ≤ B) (hxW : xWidth < B)
    (hMQ : ∀ x ∈ MQconst, x ≤ 1)
    (hsize : ((List.range xWidth).map (fun src => (State.get s src).length)).sum = m)
    (hbits : ∀ src ∈ List.range xWidth, ∀ x ∈ State.get s src, x ≤ 1) :
    (frontProgram MQconst xWidth B cm km dm cs ks ds).cost s
      ≤ ((List.range xWidth).map (fun src => tallyRegCost (State.get s src).length)).sum
        + ((List.range xWidth).map (fun src => emitRegCost (State.get s src).length)).sum
        + monomialCost cm km dm m + monomialCost cs ks ds m
        + 3 * MQconst.length
        + (encSyms (3 :: Compile.encodeRegs ((List.range xWidth).map (State.get s)))).length
        + (cm * (m + 1) ^ km + dm) + (cs * (m + 1) ^ ks + ds)
        + 34 := by
  -- distinctness for the sources (same as `frontProgram_run`)
  have hdist : ∀ src ∈ List.range xWidth,
      (src : Var) ≠ B ∧ src ≠ B + 5 ∧ src ≠ B + 6 ∧ src ≠ B + 4 := fun _ hsrc =>
    let h := src_ne xWidth B hxW hsrc
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  -- stage 0: tallyCells (cost hT3)
  obtain ⟨hT1, hT2⟩ := tallyStage_run xWidth B s m hxW hsize
  have hT3 : (tallyCells (B + 4) (B + 9) (List.range xWidth)).cost s
      ≤ 1 + ((List.range xWidth).map (fun src => tallyRegCost (State.get s src).length)).sum :=
    tallyCells_cost (B + 4) (B + 9) (List.range xWidth) s
      (by omega : (B + 4 : Var) ≠ B + 9)
      (fun _ hsrc =>
        ⟨(src_ne xWidth B hxW hsrc).2.2.2.2, (src_ne xWidth B hxW hsrc).2.2.2.1⟩)
  set s0 := (tallyCells (B + 4) (B + 9) (List.range xWidth)).eval s with hs0
  have hget0 : ∀ i ∈ List.range xWidth, State.get s0 i = State.get s i := by
    intro i hi
    have hi' : i < xWidth := List.mem_range.mp hi
    exact hT2 i (by omega : (i : Nat) ≠ B + 9) (by omega : (i : Nat) ≠ B + 4)
  have hmap0 : (List.range xWidth).map (State.get s0)
      = (List.range xWidth).map (State.get s) := List.map_congr_left hget0
  have hbits0 : ∀ src ∈ List.range xWidth, ∀ x ∈ State.get s0 src, x ≤ 1 := by
    intro src hsrc x hx; rw [hget0 src hsrc] at hx; exact hbits src hsrc x hx
  -- stage 1: emitRegs → s1 (cost hE3)
  obtain ⟨hR1, hR2⟩ := emitRegs_run (B + 4) (B + 5) (B + 6) B (List.range xWidth) s0
    (by omega : (B + 5 : Var) ≠ B + 4) (by omega : (B + 5 : Var) ≠ B)
    (by omega : (B + 5 : Var) ≠ B + 6) (by omega : (B : Var) ≠ B + 4)
    (by omega : (B : Var) ≠ B + 6) hdist hbits0
  have hE3 : (emitRegs (B + 4) (B + 5) (B + 6) B (List.range xWidth)).cost s0
      ≤ 11 + ((List.range xWidth).map (fun src => emitRegCost (State.get s src).length)).sum := by
    have h := emitRegs_cost (B + 4) (B + 5) (B + 6) B (List.range xWidth) s0
      (by omega : (B + 5 : Var) ≠ B + 4) (by omega : (B + 5 : Var) ≠ B)
      (by omega : (B + 5 : Var) ≠ B + 6) (by omega : (B : Var) ≠ B + 4)
      (by omega : (B : Var) ≠ B + 6) hdist hbits0
    have hm : (List.range xWidth).map (fun src => emitRegCost (State.get s0 src).length)
        = (List.range xWidth).map (fun src => emitRegCost (State.get s src).length) :=
      List.map_congr_left (fun i hi => by rw [hget0 i hi])
    rwa [hm] at h
  rw [hmap0] at hR1
  set s1 := (emitRegs (B + 4) (B + 5) (B + 6) B (List.range xWidth)).eval s0 with hs1
  have hs1_size : State.get s1 (B + 9) = List.replicate m 1 := by
    rw [hR2 (B + 9) (by omega : (B + 9 : Var) ≠ B) (by omega : (B + 9 : Var) ≠ B + 5)
      (by omega : (B + 9 : Var) ≠ B + 6) (by omega : (B + 9 : Var) ≠ B + 4), hT1]
  -- stage 2: unaryMonomial (cost hM3)
  obtain ⟨hM1, hM2, hM3⟩ := unaryMonomial_run cm km dm (B + 4) (B + 7) (B + 8) (B + 9) (B + 1)
    s1 m (by omega : (B + 7 : Var) ≠ B + 1) (by omega : (B + 7 : Var) ≠ B + 8)
    (by omega : (B + 7 : Var) ≠ B + 4) (by omega : (B + 1 : Var) ≠ B + 8)
    (by omega : (B + 1 : Var) ≠ B + 4) (by omega : (B + 8 : Var) ≠ B + 4) hs1_size
  set s2 := (unaryMonomial cm km dm (B + 4) (B + 7) (B + 8) (B + 9) (B + 1)).eval s1 with hs2
  have hs2_size : State.get s2 (B + 9) = List.replicate m 1 := by
    rw [hM2 (B + 9) (by omega : (B + 9 : Var) ≠ B + 1) (by omega : (B + 9 : Var) ≠ B + 7)
      (by omega : (B + 9 : Var) ≠ B + 8) (by omega : (B + 9 : Var) ≠ B + 4), hs1_size]
  have hs2_SX : State.get s2 B = State.get s1 B :=
    hM2 B (by omega : (B : Var) ≠ B + 1) (by omega : (B : Var) ≠ B + 7)
      (by omega : (B : Var) ≠ B + 8) (by omega : (B : Var) ≠ B + 4)
  -- stage 3: unaryMonomial (cost hN3)
  obtain ⟨hN1, hN2, hN3⟩ := unaryMonomial_run cs ks ds (B + 4) (B + 7) (B + 8) (B + 9) (B + 2)
    s2 m (by omega : (B + 7 : Var) ≠ B + 2) (by omega : (B + 7 : Var) ≠ B + 8)
    (by omega : (B + 7 : Var) ≠ B + 4) (by omega : (B + 2 : Var) ≠ B + 8)
    (by omega : (B + 2 : Var) ≠ B + 4) (by omega : (B + 8 : Var) ≠ B + 4) hs2_size
  set s3 := (unaryMonomial cs ks ds (B + 4) (B + 7) (B + 8) (B + 9) (B + 2)).eval s2 with hs3
  have hs3_SX : State.get s3 B = State.get s1 B := by
    rw [hN2 B (by omega : (B : Var) ≠ B + 2) (by omega : (B : Var) ≠ B + 7)
      (by omega : (B : Var) ≠ B + 8) (by omega : (B : Var) ≠ B + 4), hs2_SX]
  have hs3_MX : State.get s3 (B + 1) = List.replicate (cm * (m + 1) ^ km + dm) 1 := by
    rw [hN2 (B + 1) (by omega : (B + 1 : Var) ≠ B + 2) (by omega : (B + 1 : Var) ≠ B + 7)
      (by omega : (B + 1 : Var) ≠ B + 8) (by omega : (B + 1 : Var) ≠ B + 4), hM1]
  -- stage 4: emitConst (cost hC3)
  obtain ⟨-, hC2, hC3⟩ := emitConst_run (B + 3) MQconst s3
  set s4 := (emitConst (B + 3) MQconst).eval s3 with hs4
  have hs4_MC : State.get s4 (B + 3) = MQconst :=
    emitConst_run_bits (B + 3) MQconst s3 hMQ
  have hs4_SX : State.get s4 B
      = encSyms (3 :: Compile.encodeRegs ((List.range xWidth).map (State.get s))) := by
    rw [hC2 B (by omega : (B : Var) ≠ B + 3), hs3_SX, hR1]
  have hs4_MX : State.get s4 (B + 1) = List.replicate (cm * (m + 1) ^ km + dm) 1 := by
    rw [hC2 (B + 1) (by omega : (B + 1 : Var) ≠ B + 3), hs3_MX]
  have hs4_ST : State.get s4 (B + 2) = List.replicate (cs * (m + 1) ^ ks + ds) 1 := by
    rw [hC2 (B + 2) (by omega : (B + 2 : Var) ≠ B + 3), hN1]
  clear_value s0 s1 s2 s3 s4
  -- the whole program's cost = 5 seq nodes + the five gadget costs + the tail cost on s4
  have hcosts : (frontProgram MQconst xWidth B cm km dm cs ks ds).cost s
      = 1 + (tallyCells (B + 4) (B + 9) (List.range xWidth)).cost s
        + (1 + (emitRegs (B + 4) (B + 5) (B + 6) B (List.range xWidth)).cost s0
        + (1 + (unaryMonomial cm km dm (B + 4) (B + 7) (B + 8) (B + 9) (B + 1)).cost s1
        + (1 + (unaryMonomial cs ks ds (B + 4) (B + 7) (B + 8) (B + 9) (B + 2)).cost s2
        + (1 + (emitConst (B + 3) MQconst).cost s3
        + (Cmd.op (.clear 0) ;; Cmd.op (.copy 1 (B + 3)) ;; Cmd.op (.copy 2 B) ;;
           Cmd.op (.copy 3 (B + 1)) ;; Cmd.op (.copy 4 (B + 2))).cost s4)))) := by
    show (tallyCells (B + 4) (B + 9) (List.range xWidth) ;; _).cost s = _
    rw [Cmd.cost_seq, ← hs0, Cmd.cost_seq, ← hs1, Cmd.cost_seq, ← hs2, Cmd.cost_seq, ← hs3,
      Cmd.cost_seq, ← hs4]
  -- the tail cost: four copies whose sources are the emitted registers
  set a1 := (Cmd.op (.clear 0)).eval s4 with ha1
  set a2 := (Cmd.op (.copy 1 (B + 3))).eval a1 with ha2
  set a3 := (Cmd.op (.copy 2 B)).eval a2 with ha3
  set a4 := (Cmd.op (.copy 3 (B + 1))).eval a3 with ha4
  have hlen1 : (State.get a1 (B + 3)).length = MQconst.length := by
    rw [ha1]; show (State.get (s4.set 0 []) (B + 3)).length = _
    rw [State.get_set_ne _ _ _ _ (by omega : (B + 3 : Var) ≠ 0), hs4_MC]
  have hlen2 : (State.get a2 B).length
      = (encSyms (3 :: Compile.encodeRegs ((List.range xWidth).map (State.get s)))).length := by
    rw [ha2]; show (State.get (a1.set 1 (State.get a1 (B + 3))) B).length = _
    rw [State.get_set_ne _ _ _ _ (by omega : (B : Var) ≠ 1), ha1]
    show (State.get (s4.set 0 []) B).length = _
    rw [State.get_set_ne _ _ _ _ (by omega : (B : Var) ≠ 0), hs4_SX]
  have hlen3 : (State.get a3 (B + 1)).length = cm * (m + 1) ^ km + dm := by
    rw [ha3]; show (State.get (a2.set 2 (State.get a2 B)) (B + 1)).length = _
    rw [State.get_set_ne _ _ _ _ (by omega : (B + 1 : Var) ≠ 2), ha2]
    show (State.get (a1.set 1 (State.get a1 (B + 3))) (B + 1)).length = _
    rw [State.get_set_ne _ _ _ _ (by omega : (B + 1 : Var) ≠ 1), ha1]
    show (State.get (s4.set 0 []) (B + 1)).length = _
    rw [State.get_set_ne _ _ _ _ (by omega : (B + 1 : Var) ≠ 0), hs4_MX, List.length_replicate]
  have hlen4 : (State.get a4 (B + 2)).length = cs * (m + 1) ^ ks + ds := by
    rw [ha4]; show (State.get (a3.set 3 (State.get a3 (B + 1))) (B + 2)).length = _
    rw [State.get_set_ne _ _ _ _ (by omega : (B + 2 : Var) ≠ 3), ha3]
    show (State.get (a2.set 2 (State.get a2 B)) (B + 2)).length = _
    rw [State.get_set_ne _ _ _ _ (by omega : (B + 2 : Var) ≠ 2), ha2]
    show (State.get (a1.set 1 (State.get a1 (B + 3))) (B + 2)).length = _
    rw [State.get_set_ne _ _ _ _ (by omega : (B + 2 : Var) ≠ 1), ha1]
    show (State.get (s4.set 0 []) (B + 2)).length = _
    rw [State.get_set_ne _ _ _ _ (by omega : (B + 2 : Var) ≠ 0), hs4_ST, List.length_replicate]
  have htail : (Cmd.op (.clear 0) ;; Cmd.op (.copy 1 (B + 3)) ;; Cmd.op (.copy 2 B) ;;
        Cmd.op (.copy 3 (B + 1)) ;; Cmd.op (.copy 4 (B + 2))).cost s4
      = 4 + 1 + ((State.get a1 (B + 3)).length + 1) + ((State.get a2 B).length + 1)
        + ((State.get a3 (B + 1)).length + 1) + ((State.get a4 (B + 2)).length + 1) := by
    show (Cmd.op (.clear 0) ;; _).cost s4 = _
    rw [Cmd.cost_seq, ← ha1, Cmd.cost_seq, ← ha2, Cmd.cost_seq, ← ha3, Cmd.cost_seq, ← ha4]
    simp only [Cmd.cost_op, Op.cost]
    omega
  -- assemble
  rw [hcosts, htail, hlen1, hlen2, hlen3, hlen4]
  have := hM3
  have := hN3
  have := hT3
  have := hE3
  rw [hC3]
  omega

end FrontProgram
