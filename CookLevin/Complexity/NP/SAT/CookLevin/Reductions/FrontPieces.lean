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

/-! ## Piece 3b — the input-string emitter (the head layout's reg-2)

The C8-4 machine input string is `s_x = 3 :: encodeRegs (encX x)` (per the C8-2
gadget probe: `s_x ++ cert = encodeTape (encX x ++ certState c)` splits the
canonical tape at the certificate register). The head layout stores it as
`encSyms s_x` in reg 2. `emitRegs` builds exactly `encSyms (3 :: encodeRegs …)`
by folding `reencLoop` (`off = 1`, the `shiftReg` cell shift) over the input's
registers, wrapping each `+1`-shift with `[0]` separators — the `encSyms` image
of `encodeRegs`. The leading `3` is emitted as the `encSyms` item of symbol `3`.

`srcs` is the list of the input's register indices (`List.range xWidth` at the
assembly). It is register-generic (like `unaryMulLoop_run`): `dst`/`scan`/`tflg`/
`cnt` are scratch and MUST be distinct from every source — in particular the
assembly builds `s_x` in a scratch register ≥ `xWidth`, because reg 2 may itself
be a source (**read/write collision** — surfaced 2026-07-19-c; do not emit into a
register the loop still reads). `src` registers survive (read-only). -/
def emitRegs (cnt scan tflg dst : Var) (srcs : List Var) : Cmd :=
  srcs.foldl
    (fun c src => (c ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0)
    (Cmd.op (.clear dst) ;; appendItem dst 3)

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

/-! ## Run/frame/cost lemmas — piece 1 -/

/-- `appendConst` is exact: the constant lands on `dst` after whatever `c0`
did, the frame is `dst`-only relative to `c0`'s exit, and the cost is exactly
`c0`'s plus `2` per cell. Run lemma by induction on the constant. -/
theorem appendConst_run (dst : Var) (bits : List Nat) :
    ∀ (c0 : Cmd) (s : State),
      State.get ((appendConst c0 dst bits).eval s) dst
          = State.get (c0.eval s) dst ++ bits.map bitVal
      ∧ (∀ r : Var, r ≠ dst →
          State.get ((appendConst c0 dst bits).eval s) r
            = State.get (c0.eval s) r)
      ∧ (appendConst c0 dst bits).cost s = c0.cost s + 2 * bits.length := by
  induction bits with
  | nil =>
      intro c0 s
      exact ⟨(List.append_nil _).symm, fun r _ => rfl, by simp [appendConst]⟩
  | cons b bs ih =>
      intro c0 s
      obtain ⟨h1, h2, h3⟩ := ih (c0 ;; appendBit dst b) s
      have heb : (appendBit dst b).eval (c0.eval s)
          = (c0.eval s).set dst (State.get (c0.eval s) dst ++ [bitVal b]) := by
        by_cases hb : b = 1 <;>
          simp [appendBit, hb, bitVal, Cmd.eval_op, Op.eval, State.get]
      have hev : (c0 ;; appendBit dst b).eval s
          = (c0.eval s).set dst (State.get (c0.eval s) dst ++ [bitVal b]) := by
        rw [Cmd.eval_seq, heb]
      have hcb : (appendBit dst b).cost (c0.eval s) = 1 := by
        unfold appendBit; split <;> rfl
      refine ⟨?_, ?_, ?_⟩
      · show State.get ((appendConst (c0 ;; appendBit dst b) dst bs).eval s) dst = _
        rw [h1, hev, State.get_set_eq]
        simp [List.append_assoc]
      · intro r hr
        show State.get ((appendConst (c0 ;; appendBit dst b) dst bs).eval s) r = _
        rw [h2 r hr, hev, State.get_set_ne _ _ _ _ hr]
      · show (appendConst (c0 ;; appendBit dst b) dst bs).cost s = _
        rw [h3, Cmd.cost_seq, hcb, List.length_cons]
        omega

/-- On a bit-level constant `bitVal` is the identity. -/
theorem map_bitVal_of_bits (bits : List Nat) (hb : ∀ x ∈ bits, x ≤ 1) :
    bits.map bitVal = bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      have hb0 : b ≤ 1 := hb b (List.mem_cons_self ..)
      have hbv : bitVal b = b := by interval_cases b <;> rfl
      rw [List.map_cons, hbv, ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))]

/-- **`emitConst` is correct**: `dst := bits.map bitVal`, `dst`-only frame,
cost `1 + 2·|bits|`. -/
theorem emitConst_run (dst : Var) (bits : List Nat) (s : State) :
    State.get ((emitConst dst bits).eval s) dst = bits.map bitVal
    ∧ (∀ r : Var, r ≠ dst →
        State.get ((emitConst dst bits).eval s) r = State.get s r)
    ∧ (emitConst dst bits).cost s = 1 + 2 * bits.length := by
  obtain ⟨h1, h2, h3⟩ := appendConst_run dst bits (Cmd.op (.clear dst)) s
  have he : (Cmd.op (.clear dst)).eval s = s.set dst [] := rfl
  unfold emitConst
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, he, State.get_set_eq, List.nil_append]
  · intro r hr
    rw [h2 r hr, he, State.get_set_ne _ _ _ _ hr]
  · rw [h3]; rfl

/-- `emitConst` on a bit-level constant (the machine register, every fixed
head-layout segment): `dst := bits` exactly. -/
theorem emitConst_run_bits (dst : Var) (bits : List Nat) (s : State)
    (hb : ∀ x ∈ bits, x ≤ 1) :
    State.get ((emitConst dst bits).eval s) dst = bits := by
  rw [(emitConst_run dst bits s).1, map_bitVal_of_bits bits hb]

/-! ## Run/frame/cost lemmas — the sentinel item append -/

/-- **`appendItem` is correct**: appends exactly the `encSyms` item
`1 1^v 0` of symbol `v`; `dst`-only frame; cost `2·v + 3`. -/
theorem appendItem_run (dst : Var) (v : Nat) (s : State) :
    State.get ((appendItem dst v).eval s) dst
        = State.get s dst ++ 1 :: (List.replicate v 1 ++ [0])
    ∧ (∀ r : Var, r ≠ dst →
        State.get ((appendItem dst v).eval s) r = State.get s r)
    ∧ (appendItem dst v).cost s = 2 * v + 3 := by
  obtain ⟨h1, h2, h3⟩ :=
    appendConst_run dst (List.replicate v 1 ++ [0]) (Cmd.op (.appendOne dst)) s
  have he : (Cmd.op (.appendOne dst)).eval s
      = s.set dst (State.get s dst ++ [1]) := rfl
  have hbits : (List.replicate v 1 ++ [0]).map bitVal = List.replicate v 1 ++ [0] := by
    refine map_bitVal_of_bits _ ?_
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · have := List.eq_of_mem_replicate h; omega
    · have := List.mem_singleton.1 h; omega
  unfold appendItem
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, hbits, he, State.get_set_eq]
    simp [List.append_assoc]
  · intro r hr
    rw [h2 r hr, he, State.get_set_ne _ _ _ _ hr]
  · rw [h3, Cmd.cost_op]
    simp only [Op.cost, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega

/-! ## Run/frame/cost lemmas — piece 3 -/

/-- **`reencLoop` is correct**: appends exactly
`encSyms ((State.get s src).map (· + off))` to `dst`, exits with `scan = []`,
touches only `scan`/`dst`/`tflg`/`cnt`, at cost quadratic in `|src|`. -/
theorem reencLoop_run (off : Nat) (cnt scan tflg src dst : Var) (s : State)
    (l : List Nat)
    (hsc : scan ≠ cnt) (hsd : scan ≠ dst) (hst : scan ≠ tflg)
    (hdc : dst ≠ cnt) (hdt : dst ≠ tflg)
    (hsrc : State.get s src = l) (hbits : ∀ x ∈ l, x ≤ 1) :
    State.get ((reencLoop off cnt scan tflg src dst).eval s) dst
        = State.get s dst ++ HeadLayout.encSyms (l.map (· + off))
    ∧ State.get ((reencLoop off cnt scan tflg src dst).eval s) scan = []
    ∧ (∀ r : Var, r ≠ scan → r ≠ dst → r ≠ tflg → r ≠ cnt →
        State.get ((reencLoop off cnt scan tflg src dst).eval s) r
          = State.get s r)
    ∧ (reencLoop off cnt scan tflg src dst).cost s
        ≤ 3 + l.length + l.length * l.length
            + l.length * (l.length + 2 * off + 10) := by
  set L := l.length with hL
  -- the post-copy loop-entry state
  have e0 : (Cmd.op (.copy scan src)).eval s = s.set scan l := by
    rw [Cmd.eval_op]; simp only [Op.eval, hsrc]
  set u := s.set scan l with hu
  have huS : State.get u scan = l := State.get_set_eq _ _ _
  have huF : ∀ r : Var, r ≠ scan → State.get u r = State.get s r :=
    fun r hr => State.get_set_ne _ _ _ _ hr
  -- the loop motive
  set M : Nat → State → Prop := fun i st =>
    State.get st scan = l.drop i
    ∧ State.get st dst
        = State.get s dst ++ HeadLayout.encSyms ((l.take i).map (· + off))
    ∧ (∀ r : Var, r ≠ scan → r ≠ dst → r ≠ tflg → r ≠ cnt →
        State.get st r = State.get u r) with hM
  have hbase : M 0 u := by
    refine ⟨by rw [List.drop_zero]; exact huS, ?_, fun r _ _ _ _ => rfl⟩
    rw [List.take_zero, List.map_nil]
    show State.get u dst = State.get s dst ++ HeadLayout.encSyms []
    rw [show HeadLayout.encSyms [] = [] from rfl, List.append_nil,
      huF dst (Ne.symm hsd)]
  -- one body step: motive preservation + a uniform cost bound
  have hstep : ∀ i st, i < L → M i st →
      M (i + 1) ((reencBody off scan dst tflg).eval
        (st.set cnt (List.replicate i 1)))
      ∧ (reencBody off scan dst tflg).cost (st.set cnt (List.replicate i 1))
          ≤ L + 2 * off + 10 := by
    intro i st hi h
    obtain ⟨hS, hD, hF⟩ := h
    set w := st.set cnt (List.replicate i 1) with hw
    have hwS : State.get w scan = l.drop i := by
      rw [hw, State.get_set_ne _ _ _ _ hsc]; exact hS
    have hwD : State.get w dst
        = State.get s dst ++ HeadLayout.encSyms ((l.take i).map (· + off)) := by
      rw [hw, State.get_set_ne _ _ _ _ hdc]; exact hD
    have hilen : i < l.length := hi
    have hdrop : l.drop i = l[i] :: l.drop (i + 1) :=
      List.drop_eq_getElem_cons hilen
    -- head: latch the current bit
    have e1 : (Cmd.op (.head tflg scan)).eval w = w.set tflg [l[i]] := by
      rw [Cmd.eval_op]; simp only [Op.eval, hwS, hdrop]
    set w1 := w.set tflg [l[i]] with hw1
    have hw1S : State.get w1 scan = l.drop i := by
      rw [hw1, State.get_set_ne _ _ _ _ hst]; exact hwS
    -- tail: consume it
    have e2 : (Cmd.op (.tail scan scan)).eval w1 = w1.set scan (l.drop (i + 1)) := by
      rw [Cmd.eval_op]; simp only [Op.eval, hw1S, hdrop, List.tail_cons]
    set w2 := w1.set scan (l.drop (i + 1)) with hw2
    have hw2T : State.get w2 tflg = [l[i]] := by
      rw [hw2, State.get_set_ne _ _ _ _ (Ne.symm hst), hw1, State.get_set_eq]
    have hw2D : State.get w2 dst
        = State.get s dst ++ HeadLayout.encSyms ((l.take i).map (· + off)) := by
      rw [hw2, State.get_set_ne _ _ _ _ (Ne.symm hsd), hw1,
        State.get_set_ne _ _ _ _ hdt]
      exact hwD
    have hw2F : ∀ r : Var, r ≠ scan → r ≠ dst → r ≠ tflg → r ≠ cnt →
        State.get w2 r = State.get u r := by
      intro r h1 h2 h3 h4
      rw [hw2, State.get_set_ne _ _ _ _ h1, hw1, State.get_set_ne _ _ _ _ h3,
        hw, State.get_set_ne _ _ _ _ h4]
      exact hF r h1 h2 h3 h4
    have hw1len : (State.get w1 scan).length = L - i := by
      rw [hw1S, List.length_drop]
    -- the take-side snoc
    have htake : (l.take (i + 1)).map (· + off)
        = (l.take i).map (· + off) ++ [l[i] + off] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hilen, List.map_append]
      rfl
    have hsnoc : HeadLayout.encSyms ((l.take (i + 1)).map (· + off))
        = HeadLayout.encSyms ((l.take i).map (· + off))
            ++ 1 :: (List.replicate (l[i] + off) 1 ++ [0]) := by
      rw [htake, HeadLayout.encSyms_snoc]
    -- the two bit cases share everything up to the branch
    have hb01 : l[i] = 0 ∨ l[i] = 1 := by
      have := hbits l[i] (l.getElem_mem hilen); omega
    -- evaluate the branch and package
    rcases hb01 with hb | hb
    · -- bit 0 ⟹ else-branch, item `off`
      have hcond : State.get w2 tflg ≠ [1] := by rw [hw2T, hb]; simp
      obtain ⟨hA1, hA2, hA3⟩ := appendItem_run dst off w2
      have heval : (reencBody off scan dst tflg).eval w
          = (appendItem dst off).eval w2 := by
        unfold reencBody
        rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_ifBit_false _ _ _ _ hcond]
      have hcost : (reencBody off scan dst tflg).cost w
          = 1 + 1 + (1 + ((State.get w1 scan).length + 1)
              + (1 + (appendItem dst off).cost w2)) := by
        unfold reencBody
        rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, Cmd.cost_op, e2,
          Cmd.cost_ifBit_false _ _ _ _ hcond]
        rfl
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [heval, hA2 scan hsd, hw2, State.get_set_eq]
      · rw [heval, hA1, hw2D, hsnoc, hb, Nat.zero_add, List.append_assoc]
      · intro r h1 h2 h3 h4
        rw [heval, hA2 r h2, hw2F r h1 h2 h3 h4]
      · rw [hcost, hA3, hw1len]; omega
    · -- bit 1 ⟹ then-branch, item `1 + off`
      have hcond : State.get w2 tflg = [1] := by rw [hw2T, hb]
      obtain ⟨hA1, hA2, hA3⟩ := appendItem_run dst (1 + off) w2
      have heval : (reencBody off scan dst tflg).eval w
          = (appendItem dst (1 + off)).eval w2 := by
        unfold reencBody
        rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_ifBit_true _ _ _ _ hcond]
      have hcost : (reencBody off scan dst tflg).cost w
          = 1 + 1 + (1 + ((State.get w1 scan).length + 1)
              + (1 + (appendItem dst (1 + off)).cost w2)) := by
        unfold reencBody
        rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, Cmd.cost_op, e2,
          Cmd.cost_ifBit_true _ _ _ _ hcond]
        rfl
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [heval, hA2 scan hsd, hw2, State.get_set_eq]
      · rw [heval, hA1, hw2D, hsnoc, hb, List.append_assoc]
      · intro r h1 h2 h3 h4
        rw [heval, hA2 r h2, hw2F r h1 h2 h3 h4]
      · rw [hcost, hA3, hw1len]; omega
  -- run the loop
  have huLen : (State.get u scan).length = L := by rw [huS]
  have hInv : M L ((Cmd.forBnd cnt scan (reencBody off scan dst tflg)).eval u) := by
    have := Cmd.foldlState_range_induct (reencBody off scan dst tflg) cnt L u M
      hbase (fun i st hi h => (hstep i st hi h).1)
    rwa [Cmd.eval_forBnd, huLen]
  have hLoopCost : (Cmd.forBnd cnt scan (reencBody off scan dst tflg)).cost u
      ≤ 1 + L * (L + 2 * off + 10) + L * L := by
    have h := Cmd.cost_forBnd_le cnt scan (reencBody off scan dst tflg) u
      (L + 2 * off + 10) M hbase
      (fun i st hi h => (hstep i st (by rwa [huLen] at hi) h).1)
      (fun i st hi h => (hstep i st (by rwa [huLen] at hi) h).2)
    rwa [huLen] at h
  obtain ⟨hfS, hfD, hfF⟩ := hInv
  have heval : (reencLoop off cnt scan tflg src dst).eval s
      = (Cmd.forBnd cnt scan (reencBody off scan dst tflg)).eval u := by
    unfold reencLoop
    rw [Cmd.eval_seq, e0]
  have hcost : (reencLoop off cnt scan tflg src dst).cost s
      = 1 + (l.length + 1)
          + (Cmd.forBnd cnt scan (reencBody off scan dst tflg)).cost u := by
    unfold reencLoop
    rw [Cmd.cost_seq, Cmd.cost_op, e0]
    simp only [Op.cost, hsrc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heval, hfD, List.take_length]
  · rw [heval, hfS, List.drop_length]
  · intro r h1 h2 h3 h4
    rw [heval, hfF r h1 h2 h3 h4, huF r h1]
  · rw [hcost]; omega

/-- The core `foldl` induction behind `emitRegs`: from any seed `c0`, the loop
appends `encSyms (encodeRegs …)` of the sources to whatever `c0` left on `dst`,
and leaves every non-scratch register at `c0`'s value. -/
private theorem emitRegs_go (cnt scan tflg dst : Var) :
    ∀ (srcs : List Var) (c0 : Cmd) (s : State),
      scan ≠ cnt → scan ≠ dst → scan ≠ tflg → dst ≠ cnt → dst ≠ tflg →
      (∀ src ∈ srcs, src ≠ dst ∧ src ≠ scan ∧ src ≠ tflg ∧ src ≠ cnt) →
      (∀ src ∈ srcs, ∀ x ∈ State.get (c0.eval s) src, x ≤ 1) →
      State.get ((srcs.foldl
          (fun c src => (c ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0)
          c0).eval s) dst
        = State.get (c0.eval s) dst
            ++ HeadLayout.encSyms
                (Compile.encodeRegs (srcs.map (fun src => State.get (c0.eval s) src)))
      ∧ (∀ r : Var, r ≠ dst → r ≠ scan → r ≠ tflg → r ≠ cnt →
          State.get ((srcs.foldl
            (fun c src => (c ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0)
            c0).eval s) r = State.get (c0.eval s) r) := by
  intro srcs
  induction srcs with
  | nil =>
      intro c0 s _ _ _ _ _ _ _
      refine ⟨?_, fun r _ _ _ _ => rfl⟩
      simp only [List.foldl_nil, List.map_nil, Compile.encodeRegs_nil,
        HeadLayout.encSyms, List.foldl_nil, List.append_nil]
  | cons src rest ih =>
      intro c0 s hsc hsd hst hdc hdt hdist hbits
      -- the head source's per-register facts
      obtain ⟨hsrc_d, hsrc_s, hsrc_t, hsrc_c⟩ := hdist src (List.mem_cons_self ..)
      -- process the head: c1 = c0 ;; reencLoop ;; appendItem dst 0
      set c1 : Cmd := (c0 ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0 with hc1
      have hfold : (src :: rest).foldl
          (fun c src => (c ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0) c0
          = rest.foldl
            (fun c src => (c ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0) c1 := by
        rw [List.foldl_cons]
      -- evaluate c1 on s
      set s0 : State := c0.eval s with hs0
      obtain ⟨hR1, hR2, hR3, _⟩ :=
        reencLoop_run 1 cnt scan tflg src dst s0 (State.get s0 src)
          hsc hsd hst hdc hdt rfl (hbits src (List.mem_cons_self ..))
      set sR : State := (reencLoop 1 cnt scan tflg src dst).eval s0 with hsR
      obtain ⟨hI1, hI2, _⟩ := appendItem_run dst 0 sR
      have hc1eval : c1.eval s = (appendItem dst 0).eval sR := by
        rw [hc1, Cmd.eval_seq, Cmd.eval_seq, ← hs0, ← hsR]
      -- dst content after c1
      have hc1dst : State.get (c1.eval s) dst
          = State.get s0 dst
              ++ HeadLayout.encSyms (Compile.shiftReg (State.get s0 src) ++ [0]) := by
        rw [hc1eval, hI1, hR1, HeadLayout.encSyms_append]
        simp only [Compile.shiftReg]
        rw [show HeadLayout.encSyms [0] = 1 :: (List.replicate 0 1 ++ [0]) from rfl]
        rw [List.append_assoc]
      -- frame after c1: non-scratch registers keep their c0 value
      have hc1frame : ∀ r : Var, r ≠ dst → r ≠ scan → r ≠ tflg → r ≠ cnt →
          State.get (c1.eval s) r = State.get s0 r := by
        intro r h1 h2 h3 h4
        rw [hc1eval, hI2 r h1, hR3 r h2 h1 h3 h4]
      -- the remaining sources still see their c0 values through c1
      have hrest_bits : ∀ s' ∈ rest, ∀ x ∈ State.get (c1.eval s) s', x ≤ 1 := by
        intro s' hs' x hx
        obtain ⟨hd, hsc', ht', hcc'⟩ := hdist s' (List.mem_cons_of_mem _ hs')
        rw [hc1frame s' hd hsc' ht' hcc'] at hx
        exact hbits s' (List.mem_cons_of_mem _ hs') x hx
      -- apply IH to the remaining sources, seeded by c1
      obtain ⟨hIH1, hIH2⟩ := ih c1 s hsc hsd hst hdc hdt
        (fun src' hsrc' => hdist src' (List.mem_cons_of_mem _ hsrc')) hrest_bits
      -- rest.map (get (c1.eval s)) = rest.map (get s0)
      have hmap : rest.map (fun s' => State.get (c1.eval s) s')
          = rest.map (fun s' => State.get s0 s') := by
        apply List.map_congr_left
        intro s' hs'
        obtain ⟨hd, hsc', ht', hcc'⟩ := hdist s' (List.mem_cons_of_mem _ hs')
        exact hc1frame s' hd hsc' ht' hcc'
      refine ⟨?_, ?_⟩
      · rw [hfold, hIH1, hc1dst, hmap, List.append_assoc, ← HeadLayout.encSyms_append,
          ← Compile.encodeRegs_cons, List.map_cons]
      · intro r h1 h2 h3 h4
        rw [hfold, hIH2 r h1 h2 h3 h4, hc1frame r h1 h2 h3 h4]

/-- **`emitRegs` is correct**: `dst := encSyms (3 :: encodeRegs (input regs))`
— exactly the head layout's reg-2 content for `s_x = 3 :: encodeRegs (encX x)`
when `srcs` lists the input's registers. `src` registers survive; `dst`/`scan`/
`tflg`/`cnt` are the only registers touched. Requires each source bit-level
(the split-layout `encodeIn` is `BitState`) and all sources distinct from the
scratch registers. -/
theorem emitRegs_run (cnt scan tflg dst : Var) (srcs : List Var) (s : State)
    (hsc : scan ≠ cnt) (hsd : scan ≠ dst) (hst : scan ≠ tflg)
    (hdc : dst ≠ cnt) (hdt : dst ≠ tflg)
    (hdist : ∀ src ∈ srcs, src ≠ dst ∧ src ≠ scan ∧ src ≠ tflg ∧ src ≠ cnt)
    (hbits : ∀ src ∈ srcs, ∀ x ∈ State.get s src, x ≤ 1) :
    State.get ((emitRegs cnt scan tflg dst srcs).eval s) dst
        = HeadLayout.encSyms (3 :: Compile.encodeRegs (srcs.map (State.get s)))
    ∧ (∀ r : Var, r ≠ dst → r ≠ scan → r ≠ tflg → r ≠ cnt →
        State.get ((emitRegs cnt scan tflg dst srcs).eval s) r = State.get s r) := by
  -- the seed clears dst then emits the `encSyms` item of the leading `3`
  set c0 : Cmd := Cmd.op (.clear dst) ;; appendItem dst 3 with hc0
  have hclear : (Cmd.op (.clear dst)).eval s = s.set dst [] := rfl
  obtain ⟨hA1, hA2, _⟩ := appendItem_run dst 3 (s.set dst [])
  have hc0eval : c0.eval s = (appendItem dst 3).eval (s.set dst []) := by
    rw [hc0, Cmd.eval_seq, hclear]
  have hc0dst : State.get (c0.eval s) dst = HeadLayout.encSyms [3] := by
    rw [hc0eval, hA1, State.get_set_eq, List.nil_append]
    rfl
  have hc0frame : ∀ r : Var, r ≠ dst → State.get (c0.eval s) r = State.get s r := by
    intro r hr
    rw [hc0eval, hA2 r hr, State.get_set_ne _ _ _ _ hr]
  -- the sources still read their original values through the seed
  have hc0bits : ∀ src ∈ srcs, ∀ x ∈ State.get (c0.eval s) src, x ≤ 1 := by
    intro src hs' x hx
    rw [hc0frame src (hdist src hs').1] at hx
    exact hbits src hs' x hx
  obtain ⟨hG1, hG2⟩ := emitRegs_go cnt scan tflg dst srcs c0 s
    hsc hsd hst hdc hdt hdist hc0bits
  have hmap : srcs.map (fun src => State.get (c0.eval s) src) = srcs.map (State.get s) := by
    apply List.map_congr_left
    intro src hs'
    exact hc0frame src (hdist src hs').1
  refine ⟨?_, ?_⟩
  · rw [emitRegs, hG1, hc0dst, hmap, ← HeadLayout.encSyms_append]
    rfl
  · intro r h1 h2 h3 h4
    rw [emitRegs, hG2 r h1 h2 h3 h4, hc0frame r h1]

/-! ## Run/frame/cost lemmas — piece 2 -/

/-- **`mulStep` is correct**: `acc := 1^(m·a)` from `|base| = m`, `acc = 1^a`;
only `acc`/`tmp`/`cnt` change (`base` in particular survives, funding the next
iteration). -/
theorem mulStep_run (cnt base tmp acc : Var) (s : State) (m a : Nat)
    (hta : tmp ≠ acc) (htc : tmp ≠ cnt) (hac : acc ≠ cnt) (htb : tmp ≠ base)
    (hbase : (State.get s base).length = m)
    (hacc : State.get s acc = List.replicate a 1) :
    State.get ((mulStep cnt base tmp acc).eval s) acc
        = List.replicate (m * a) 1
    ∧ (∀ r : Var, r ≠ acc → r ≠ tmp → r ≠ cnt →
        State.get ((mulStep cnt base tmp acc).eval s) r = State.get s r)
    ∧ (mulStep cnt base tmp acc).cost s
        ≤ m * (2 * (m * a + a) + 1) + m * m + m * a + 5 := by
  have e1 : (Cmd.op (.clear tmp)).eval s = s.set tmp [] := rfl
  set s1 := s.set tmp [] with hs1
  have hs1acc : State.get s1 acc = List.replicate a 1 := by
    rw [hs1, State.get_set_ne _ _ _ _ (Ne.symm hta)]; exact hacc
  have hs1base : (State.get s1 base).length = m := by
    rw [hs1, State.get_set_ne _ _ _ _ (Ne.symm htb)]; exact hbase
  have hs1tmp : State.get s1 tmp = [] := State.get_set_eq _ _ _
  obtain ⟨hL1, hL2⟩ := BinaryCCFSATFree.unaryMulLoop_run cnt base acc tmp s1 a m
    hta htc hac hs1acc hs1base hs1tmp
  set s2 := (Cmd.forBnd cnt base (Cmd.op (.concat tmp tmp acc))).eval s1 with hs2
  have e3 : (Cmd.op (.copy acc tmp)).eval s2
      = s2.set acc (List.replicate (m * a) 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hL1]
  have heval : (mulStep cnt base tmp acc).eval s
      = s2.set acc (List.replicate (m * a) 1) := by
    unfold mulStep
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, ← hs2, e3]
  have hLoopCost : (Cmd.forBnd cnt base (Cmd.op (.concat tmp tmp acc))).cost s1
      ≤ 1 + m * (2 * (0 + m * a + a) + 1) + m * m := by
    refine cost_mulLoop_le cnt base tmp acc s1 0 a m hta htc hac ?_ ?_ hs1base
    · rw [hs1tmp]; simp
    · rw [hs1acc, List.length_replicate]
  refine ⟨?_, ?_, ?_⟩
  · rw [heval, State.get_set_eq]
  · intro r h1 h2 h3
    rw [heval, State.get_set_ne _ _ _ _ h1, hL2 r h2 h3, hs1,
      State.get_set_ne _ _ _ _ h2]
  · have hcost : (mulStep cnt base tmp acc).cost s
        = 1 + 1 + (1 + (Cmd.forBnd cnt base (Cmd.op (.concat tmp tmp acc))).cost s1
            + (m * a + 1)) := by
      unfold mulStep
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, ← hs2, Cmd.cost_op]
      simp only [Op.cost, hL1, List.length_replicate]
    rw [hcost]
    simp only [Nat.zero_add] at hLoopCost
    omega

/-- The exact-shape recursive cost of `powLoop` (`mulStep`'s bound summed over
the `k` levels; the acc at level `i` is `1^(a·m^i)`). Closed-form domination
is `powCost_le`. -/
def powCost (m a : Nat) : Nat → Nat
  | 0 => a + 1
  | k + 1 => powCost m a k
      + (m * (2 * (m * (a * m ^ k) + a * m ^ k) + 1) + m * m + m * (a * m ^ k) + 5)
      + 1

/-- **`powLoop` is correct**: `acc := 1^(a·m^k)` from `base = 1^m`,
`acc = 1^a`; only `acc`/`tmp`/`cnt` change; cost ≤ `powCost m a k`. -/
theorem powLoop_run (cnt base tmp acc : Var) (k : Nat) (s : State) (m a : Nat)
    (hta : tmp ≠ acc) (htc : tmp ≠ cnt) (hac : acc ≠ cnt)
    (hba : base ≠ acc) (hbt : base ≠ tmp) (hbc : base ≠ cnt)
    (hbase : State.get s base = List.replicate m 1)
    (hacc : State.get s acc = List.replicate a 1) :
    State.get ((powLoop cnt base tmp acc k).eval s) acc
        = List.replicate (a * m ^ k) 1
    ∧ (∀ r : Var, r ≠ acc → r ≠ tmp → r ≠ cnt →
        State.get ((powLoop cnt base tmp acc k).eval s) r = State.get s r)
    ∧ (powLoop cnt base tmp acc k).cost s ≤ powCost m a k := by
  induction k with
  | zero =>
      have he : (powLoop cnt base tmp acc 0).eval s = s.set acc (State.get s acc) := by
        show (Cmd.op (.copy acc acc)).eval s = _
        rw [Cmd.eval_op]; rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [he, State.get_set_eq, hacc, pow_zero, Nat.mul_one]
      · intro r h1 _ _
        rw [he, State.get_set_ne _ _ _ _ h1]
      · show (Cmd.op (.copy acc acc)).cost s ≤ a + 1
        rw [Cmd.cost_op]
        simp only [Op.cost, hacc, List.length_replicate, le_refl]
  | succ k ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      set s' := (powLoop cnt base tmp acc k).eval s with hs'
      have hs'base : State.get s' base = List.replicate m 1 := by
        rw [hs', ih2 base hba hbt hbc]; exact hbase
      have hs'baseLen : (State.get s' base).length = m := by
        rw [hs'base, List.length_replicate]
      obtain ⟨hm1, hm2, hm3⟩ := mulStep_run cnt base tmp acc s' m (a * m ^ k)
        hta htc hac (Ne.symm hbt) hs'baseLen ih1
      have heval : (powLoop cnt base tmp acc (k + 1)).eval s
          = (mulStep cnt base tmp acc).eval s' := by
        show ((powLoop cnt base tmp acc k) ;; mulStep cnt base tmp acc).eval s = _
        rw [Cmd.eval_seq, ← hs']
      have hpow : m * (a * m ^ k) = a * m ^ (k + 1) := by
        rw [pow_succ]; ring
      refine ⟨?_, ?_, ?_⟩
      · rw [heval, hm1, hpow]
      · intro r h1 h2 h3
        rw [heval, hm2 r h1 h2 h3, hs', ih2 r h1 h2 h3]
      · have hcost : (powLoop cnt base tmp acc (k + 1)).cost s
            = 1 + (powLoop cnt base tmp acc k).cost s
                + (mulStep cnt base tmp acc).cost s' := by
          show ((powLoop cnt base tmp acc k) ;; mulStep cnt base tmp acc).cost s = _
          rw [Cmd.cost_seq, ← hs']
        rw [hcost]
        show _ ≤ powCost m a (k + 1)
        unfold powCost
        omega

/-- The exact-shape total cost of `unaryMonomial` (assembled from the stage
costs; `powCost`'s closed form is `powCost_le`). -/
def monomialCost (c k d n : Nat) : Nat :=
  powCost (n + 1) c k + 2 * c + 2 * d + n + 6

/-- **`unaryMonomial` is correct**: `dst := 1^(c·(n+1)^k + d)` from
`src = 1^n`; only `dst`/`base`/`tmp`/`cnt` change (in particular `src`
survives for the next consumer); cost ≤ `monomialCost c k d n`. -/
theorem unaryMonomial_run (c k d : Nat) (cnt base tmp src dst : Var) (s : State)
    (n : Nat)
    (hbd : base ≠ dst) (hbt : base ≠ tmp) (hbc : base ≠ cnt)
    (hdt : dst ≠ tmp) (hdc : dst ≠ cnt) (htc : tmp ≠ cnt)
    (hsrc : State.get s src = List.replicate n 1) :
    State.get ((unaryMonomial c k d cnt base tmp src dst).eval s) dst
        = List.replicate (c * (n + 1) ^ k + d) 1
    ∧ (∀ r : Var, r ≠ dst → r ≠ base → r ≠ tmp → r ≠ cnt →
        State.get ((unaryMonomial c k d cnt base tmp src dst).eval s) r
          = State.get s r)
    ∧ (unaryMonomial c k d cnt base tmp src dst).cost s
        ≤ monomialCost c k d n := by
  -- stage 1: base := 1^n, then 1^(n+1)
  have e1 : (Cmd.op (.copy base src)).eval s = s.set base (List.replicate n 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval, hsrc]
  set s1 := s.set base (List.replicate n 1) with hs1
  have hs1base : State.get s1 base = List.replicate n 1 := State.get_set_eq _ _ _
  have e2 : (Cmd.op (.appendOne base)).eval s1
      = s1.set base (List.replicate (n + 1) 1) := by
    rw [Cmd.eval_op]
    simp only [Op.eval, hs1base, ← List.replicate_succ']
  set s2 := s1.set base (List.replicate (n + 1) 1) with hs2
  have hs2base : State.get s2 base = List.replicate (n + 1) 1 :=
    State.get_set_eq _ _ _
  -- stage 2: dst := 1^c
  obtain ⟨hE1, hE2, hE3⟩ := emitConst_run dst (List.replicate c 1) s2
  set s3 := (emitConst dst (List.replicate c 1)).eval s2 with hs3
  have hs3dst : State.get s3 dst = List.replicate c 1 := by
    rw [hs3, hE1, List.map_replicate]
    rfl
  have hs3base : State.get s3 base = List.replicate (n + 1) 1 := by
    rw [hs3, hE2 base hbd]; exact hs2base
  -- stage 3: dst := 1^(c·(n+1)^k)
  obtain ⟨hP1, hP2, hP3⟩ := powLoop_run cnt base tmp dst k s3 (n + 1) c
    (Ne.symm hdt) htc hdc hbd hbt hbc hs3base hs3dst
  set s4 := (powLoop cnt base tmp dst k).eval s3 with hs4
  -- the seed of the trailing appendConst
  obtain ⟨hA1, hA2, hA3⟩ := appendConst_run dst (List.replicate d 1)
    (Cmd.op (.copy base src) ;; Cmd.op (.appendOne base) ;;
     emitConst dst (List.replicate c 1) ;; powLoop cnt base tmp dst k) s
  have hseed : (Cmd.op (.copy base src) ;; Cmd.op (.appendOne base) ;;
      emitConst dst (List.replicate c 1) ;; powLoop cnt base tmp dst k).eval s
      = s4 := by
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, ← hs3, ← hs4]
  refine ⟨?_, ?_, ?_⟩
  · show State.get ((appendConst _ dst (List.replicate d 1)).eval s) dst = _
    rw [hA1, hseed, hP1, List.map_replicate]
    show List.replicate (c * (n + 1) ^ k) 1 ++ List.replicate d (bitVal 1) = _
    rw [show bitVal 1 = 1 from rfl, ← List.replicate_add]
  · intro r h1 h2 h3 h4
    show State.get ((appendConst _ dst (List.replicate d 1)).eval s) r = _
    rw [hA2 r h1, hseed, hs4, hP2 r h1 h3 h4, hs3, hE2 r h1, hs2,
      State.get_set_ne _ _ _ _ h2, hs1, State.get_set_ne _ _ _ _ h2]
  · show (appendConst _ dst (List.replicate d 1)).cost s ≤ _
    rw [hA3, List.length_replicate]
    have hseedCost : (Cmd.op (.copy base src) ;; Cmd.op (.appendOne base) ;;
        emitConst dst (List.replicate c 1) ;; powLoop cnt base tmp dst k).cost s
        = 1 + (n + 1) + (1 + 1 + (1 + (1 + 2 * c)
            + (powLoop cnt base tmp dst k).cost s3)) := by
      rw [Cmd.cost_seq, Cmd.cost_op, e1, Cmd.cost_seq, Cmd.cost_op, e2,
        Cmd.cost_seq, hE3, ← hs3]
      simp only [Op.cost, hsrc, List.length_replicate]
    rw [hseedCost]
    unfold monomialCost
    omega

/-- Closed-form domination of `powCost` (for `1 ≤ m`; the monomial's caller
has `m = n + 1`): `powCost` is `≤ (a+1) + 13·k·(m+1)²·(a+1)·(m^k+1)` — the
degree-`k`-monomial shape the C8-4 `inOPoly` obligations consume. -/
theorem powCost_le (m a k : Nat) (h1 : 1 ≤ m) :
    powCost m a k
      ≤ (a + 1) + k * (13 * ((m + 1) * ((m + 1) * ((a + 1) * (m ^ k + 1))))) := by
  induction k with
  | zero => simp [powCost]
  | succ k ih =>
      set X := (m + 1) * ((m + 1) * ((a + 1) * (m ^ k + 1))) with hX
      set Y := (m + 1) * ((m + 1) * ((a + 1) * (m ^ (k + 1) + 1))) with hY
      have hXY : X ≤ Y := by
        rw [hX, hY]
        have hp : m ^ k ≤ m ^ (k + 1) := Nat.pow_le_pow_right h1 (Nat.le_succ k)
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ (by omega)))
      -- the level-(k+1) mulStep bound is ≤ 13·Y
      have hstep : m * (2 * (m * (a * m ^ k) + a * m ^ k) + 1) + m * m
          + m * (a * m ^ k) + 5 + 1 ≤ 13 * Y := by
        have hexp : m * (2 * (m * (a * m ^ k) + a * m ^ k) + 1)
            = 2 * (m * (m * (a * m ^ k))) + 2 * (m * (a * m ^ k)) + m := by ring
        have hkk1 : a * m ^ k ≤ (a + 1) * (m ^ (k + 1) + 1) := by
          have hp : m ^ k ≤ m ^ (k + 1) := Nat.pow_le_pow_right h1 (Nat.le_succ k)
          calc a * m ^ k ≤ (a + 1) * (m ^ k + 1) :=
                Nat.mul_le_mul (Nat.le_succ a) (Nat.le_succ _)
            _ ≤ (a + 1) * (m ^ (k + 1) + 1) :=
                Nat.mul_le_mul_left _ (by omega)
        have t1 : m * (m * (a * m ^ k)) ≤ Y := by
          rw [hY]
          exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) hkk1)
        have t2 : m * (a * m ^ k) ≤ Y := by
          rw [hY]
          refine Nat.mul_le_mul (by omega) ?_
          calc a * m ^ k ≤ (a + 1) * (m ^ (k + 1) + 1) := hkk1
            _ ≤ (m + 1) * ((a + 1) * (m ^ (k + 1) + 1)) :=
                Nat.le_mul_of_pos_left _ (by omega)
        have t3 : m * m ≤ Y := by
          rw [hY]
          refine Nat.mul_le_mul (by omega) ?_
          calc m ≤ m + 1 := Nat.le_succ m
            _ ≤ (m + 1) * ((a + 1) * (m ^ (k + 1) + 1)) :=
                Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
        have t4 : m ≤ Y := by
          rw [hY]
          calc m ≤ m + 1 := Nat.le_succ m
            _ ≤ (m + 1) * ((m + 1) * ((a + 1) * (m ^ (k + 1) + 1))) :=
                Nat.le_mul_of_pos_right _
                  (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
        have t5 : 1 ≤ Y := by
          rw [hY]
          exact Nat.mul_pos (by omega)
            (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
        omega
      calc powCost m a (k + 1)
          = powCost m a k + (m * (2 * (m * (a * m ^ k) + a * m ^ k) + 1)
              + m * m + m * (a * m ^ k) + 5) + 1 := rfl
        _ ≤ ((a + 1) + k * (13 * X)) + (m * (2 * (m * (a * m ^ k) + a * m ^ k) + 1)
              + m * m + m * (a * m ^ k) + 5) + 1 := by
            exact Nat.add_le_add_right (Nat.add_le_add_right ih _) _
        _ ≤ ((a + 1) + k * (13 * Y)) + 13 * Y := by
            have hkXY : k * (13 * X) ≤ k * (13 * Y) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hXY)
            omega
        _ = (a + 1) + (k + 1) * (13 * Y) := by ring

/-! ## Piece 4 — the input-cell counter (the monomial argument, R2/F6)

`unaryMonomial` (regs 3/4) consumes `src = 1^n`, but the program's input is bit
registers, not a unary number. The natural argument is a unary measure of the
input the program can compute cheaply: the **total number of cells** across the
input registers. `tallyCells` emits exactly `1^(Σ |input reg|)`; for `srcs =
List.range xWidth` (the input's register indices) that is `State.size (encX x)`
— the split-layout input's aggregate size — the monomial argument `n` the C8-4
`maxSize x`/`steps x` registers feed into `unaryMonomial`. One `forBnd` per
register (bounded by that register's length, appending one `1` per cell)
accumulating into a cleared `dst`; every source is read-only, only `dst`/`cnt`
change.

Register-generic like every other piece: `cnt`/`dst` are scratch and MUST be
distinct from every source (`cnt` is the loop counter — reusing a source would
corrupt a later register's length read; `dst` is the accumulator). C8-4 owns the
register map. ⚠ this is the piece surfaced as "R2 — the one genuinely-unbuilt
gadget" (2026-07-19-c). The choice `n := State.size (encX x)` is settled here;
whether that measure over-shoots the hypothesis's abstract `certBound`/run budget
is the C8-4 machine-iff session's obligation (`encX_size` bounds
`State.size (encX x)`), NOT this gadget's. -/

/-- Append `1^|src|` to `dst`: a `forBnd` bounded by `src` (read-only) appending
one `1` per cell, through the scratch counter `cnt`. -/
def tallyReg (cnt src dst : Var) : Cmd :=
  Cmd.forBnd cnt src (Cmd.op (.appendOne dst))

/-- **The input-cell counter** (C8-3 piece 4): `dst := 1^(Σ_{src ∈ srcs}
|State.get s src|)` — the input registers' total cell count in unary. One
`tallyReg` per source, accumulating into a cleared `dst`. -/
def tallyCells (cnt dst : Var) (srcs : List Var) : Cmd :=
  srcs.foldl (fun c src => c ;; tallyReg cnt src dst) (Cmd.op (.clear dst))

/-- **`tallyReg` is correct**: appends exactly `1^|src|` to `dst`; `src` (the
loop bound) survives, only `dst`/`cnt` change; cost `≤ 1 + |src|·5 + |src|²`. -/
theorem tallyReg_run (cnt src dst : Var) (s : State)
    (hcd : cnt ≠ dst) :
    State.get ((tallyReg cnt src dst).eval s) dst
        = State.get s dst ++ List.replicate (State.get s src).length 1
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
        State.get ((tallyReg cnt src dst).eval s) r = State.get s r)
    ∧ (tallyReg cnt src dst).cost s
        ≤ 1 + (State.get s src).length * 5
            + (State.get s src).length * (State.get s src).length := by
  set M : Nat → State → Prop := fun i st =>
    State.get st dst = State.get s dst ++ List.replicate i 1
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt → State.get st r = State.get s r) with hMdef
  have h0 : M 0 s := ⟨by rw [List.replicate, List.append_nil], fun r _ _ => rfl⟩
  have hstep : ∀ i st, i < (State.get s src).length → M i st →
      M (i + 1) ((Cmd.op (.appendOne dst)).eval (st.set cnt (List.replicate i 1))) := by
    intro i st _ hM
    obtain ⟨hDi, hfr⟩ := hM
    set w := st.set cnt (List.replicate i 1) with hw
    refine ⟨?_, ?_⟩
    · rw [Cmd.eval_op, Op.eval, State.get_set_eq, hw,
        State.get_set_ne _ _ _ _ (Ne.symm hcd), hDi, List.append_assoc,
        ← List.replicate_succ']
    · intro r hr1 hr2
      rw [Cmd.eval_op, Op.eval, State.get_set_ne _ _ _ _ hr1, hw,
        State.get_set_ne _ _ _ _ hr2]
      exact hfr r hr1 hr2
  have hInv := Cmd.foldlState_range_induct (Cmd.op (.appendOne dst)) cnt
    (State.get s src).length s M h0 hstep
  refine ⟨?_, ?_, ?_⟩
  · rw [tallyReg, Cmd.eval_forBnd]; exact hInv.1
  · intro r h1 h2; rw [tallyReg, Cmd.eval_forBnd]; exact hInv.2 r h1 h2
  · rw [tallyReg]
    simpa [Cmd.flatK] using cost_constLoop_le cnt src (Cmd.op (.appendOne dst))
      rfl rfl s (State.get s src).length rfl

/-- The `foldl` induction behind `tallyCells`: from any seed `c0`, the loop
appends `1^(Σ |source|)` (source lengths read at `c0`'s exit) to whatever `c0`
left on `dst`, and leaves every non-scratch register at `c0`'s value. -/
private theorem tallyCells_go (cnt dst : Var) :
    ∀ (srcs : List Var) (c0 : Cmd) (s : State),
      cnt ≠ dst →
      (∀ src ∈ srcs, src ≠ dst ∧ src ≠ cnt) →
      State.get ((srcs.foldl
          (fun c src => c ;; tallyReg cnt src dst) c0).eval s) dst
        = State.get (c0.eval s) dst
            ++ List.replicate
                ((srcs.map (fun src => (State.get (c0.eval s) src).length)).sum) 1
      ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
          State.get ((srcs.foldl
            (fun c src => c ;; tallyReg cnt src dst) c0).eval s) r
            = State.get (c0.eval s) r) := by
  intro srcs
  induction srcs with
  | nil =>
      intro c0 s _ _
      refine ⟨?_, fun r _ _ => rfl⟩
      simp
  | cons src rest ih =>
      intro c0 s hcd hdist
      obtain ⟨hsrc_d, hsrc_c⟩ := hdist src (List.mem_cons_self ..)
      set c1 : Cmd := c0 ;; tallyReg cnt src dst with hc1
      have hfold : (src :: rest).foldl
          (fun c src => c ;; tallyReg cnt src dst) c0
          = rest.foldl (fun c src => c ;; tallyReg cnt src dst) c1 := by
        rw [List.foldl_cons]
      set s0 : State := c0.eval s with hs0
      obtain ⟨hR1, hR2, _⟩ := tallyReg_run cnt src dst s0 hcd
      have hc1eval : c1.eval s = (tallyReg cnt src dst).eval s0 := by
        rw [hc1, Cmd.eval_seq, ← hs0]
      have hc1dst : State.get (c1.eval s) dst
          = State.get s0 dst ++ List.replicate (State.get s0 src).length 1 := by
        rw [hc1eval, hR1]
      have hc1frame : ∀ r : Var, r ≠ dst → r ≠ cnt →
          State.get (c1.eval s) r = State.get s0 r := by
        intro r h1 h2; rw [hc1eval, hR2 r h1 h2]
      obtain ⟨hIH1, hIH2⟩ := ih c1 s hcd
        (fun s' hs' => hdist s' (List.mem_cons_of_mem _ hs'))
      have hmap : rest.map (fun s' => (State.get (c1.eval s) s').length)
          = rest.map (fun s' => (State.get s0 s').length) := by
        apply List.map_congr_left
        intro s' hs'
        obtain ⟨hd, hc⟩ := hdist s' (List.mem_cons_of_mem _ hs')
        rw [hc1frame s' hd hc]
      refine ⟨?_, ?_⟩
      · rw [hfold, hIH1, hc1dst, hmap, List.map_cons, List.sum_cons,
          List.append_assoc, ← List.replicate_add]
      · intro r h1 h2
        rw [hfold, hIH2 r h1 h2, hc1frame r h1 h2]

/-- **`tallyCells` is correct**: `dst := 1^(Σ_{src ∈ srcs} |State.get s src|)`
— the input registers' total cell count in unary. Sources survive (read-only),
only `dst`/`cnt` change. Requires `cnt`/`dst` distinct from every source. -/
theorem tallyCells_run (cnt dst : Var) (srcs : List Var) (s : State)
    (hcd : cnt ≠ dst)
    (hdist : ∀ src ∈ srcs, src ≠ dst ∧ src ≠ cnt) :
    State.get ((tallyCells cnt dst srcs).eval s) dst
        = List.replicate ((srcs.map (fun src => (State.get s src).length)).sum) 1
    ∧ (∀ r : Var, r ≠ dst → r ≠ cnt →
        State.get ((tallyCells cnt dst srcs).eval s) r = State.get s r) := by
  have hclear : (Cmd.op (.clear dst)).eval s = s.set dst [] := rfl
  obtain ⟨hG1, hG2⟩ := tallyCells_go cnt dst srcs (Cmd.op (.clear dst)) s hcd hdist
  have hc0dst : State.get ((Cmd.op (.clear dst)).eval s) dst = [] := by
    rw [hclear, State.get_set_eq]
  have hc0frame : ∀ r : Var, r ≠ dst →
      State.get ((Cmd.op (.clear dst)).eval s) r = State.get s r := by
    intro r hr; rw [hclear, State.get_set_ne _ _ _ _ hr]
  have hmap : srcs.map (fun src => (State.get ((Cmd.op (.clear dst)).eval s) src).length)
      = srcs.map (fun src => (State.get s src).length) := by
    apply List.map_congr_left
    intro src hs'
    rw [hc0frame src (hdist src hs').1]
  refine ⟨?_, ?_⟩
  · rw [tallyCells, hG1, hc0dst, hmap, List.nil_append]
  · intro r h1 h2
    rw [tallyCells, hG2 r h1 h2, hc0frame r h1]

/-- The per-register cost contribution of the `tallyCells` fold: the seq node
(`1`) plus `tallyReg`'s `1 + L·5 + L²` at that register's length `L`. -/
def tallyRegCost (L : Nat) : Nat := 2 + L * 5 + L * L

/-- The `foldl` cost induction behind `tallyCells_cost`. -/
private theorem tallyCells_cost_go (cnt dst : Var) :
    ∀ (srcs : List Var) (c0 : Cmd) (s : State),
      cnt ≠ dst →
      (∀ src ∈ srcs, src ≠ dst ∧ src ≠ cnt) →
      (srcs.foldl (fun c src => c ;; tallyReg cnt src dst) c0).cost s
        ≤ c0.cost s
          + (srcs.map (fun src => tallyRegCost (State.get (c0.eval s) src).length)).sum := by
  intro srcs
  induction srcs with
  | nil => intro c0 s _ _; simp
  | cons src rest ih =>
      intro c0 s hcd hdist
      obtain ⟨hsrc_d, hsrc_c⟩ := hdist src (List.mem_cons_self ..)
      set c1 : Cmd := c0 ;; tallyReg cnt src dst with hc1
      have hfold : (src :: rest).foldl
          (fun c src => c ;; tallyReg cnt src dst) c0
          = rest.foldl (fun c src => c ;; tallyReg cnt src dst) c1 := by
        rw [List.foldl_cons]
      set s0 : State := c0.eval s with hs0
      obtain ⟨_, hR2, hR3⟩ := tallyReg_run cnt src dst s0 hcd
      set L := (State.get s0 src).length with hL
      have hc1eval : c1.eval s = (tallyReg cnt src dst).eval s0 := by
        rw [hc1, Cmd.eval_seq, ← hs0]
      have hc1cost : c1.cost s ≤ c0.cost s + tallyRegCost L := by
        rw [hc1, Cmd.cost_seq, ← hs0]
        unfold tallyRegCost
        generalize L * 5 = A at hR3 ⊢
        generalize L * L = B at hR3 ⊢
        omega
      have hc1frame : ∀ r : Var, r ≠ dst → r ≠ cnt →
          State.get (c1.eval s) r = State.get s0 r := by
        intro r h1 h2; rw [hc1eval, hR2 r h1 h2]
      have hmap : rest.map (fun s' => tallyRegCost (State.get (c1.eval s) s').length)
          = rest.map (fun s' => tallyRegCost (State.get s0 s').length) := by
        apply List.map_congr_left
        intro s' hs'
        obtain ⟨hd, hc⟩ := hdist s' (List.mem_cons_of_mem _ hs')
        rw [hc1frame s' hd hc]
      have hIH := ih c1 s hcd (fun s' hs' => hdist s' (List.mem_cons_of_mem _ hs'))
      rw [hfold]
      calc (rest.foldl (fun c src => c ;; tallyReg cnt src dst) c1).cost s
          ≤ c1.cost s
              + (rest.map (fun s' => tallyRegCost (State.get (c1.eval s) s').length)).sum :=
            hIH
        _ = c1.cost s
              + (rest.map (fun s' => tallyRegCost (State.get s0 s').length)).sum := by
            rw [hmap]
        _ ≤ (c0.cost s + tallyRegCost L)
              + (rest.map (fun s' => tallyRegCost (State.get s0 s').length)).sum :=
            Nat.add_le_add_right hc1cost _
        _ = c0.cost s
              + ((src :: rest).map (fun s' => tallyRegCost (State.get s0 s').length)).sum := by
            rw [List.map_cons, List.sum_cons, ← hL, Nat.add_assoc]

/-- **`tallyCells` cost**: `≤ 1 + Σ_{src ∈ srcs} (2 + |src|·5 + |src|²)` — the
seed `clear` (`1`) plus, per register, the seq node and its cell-loop cost. A
polynomial in the input cell counts (the `inOPoly` input for the C8-4 witness's
cost field). -/
theorem tallyCells_cost (cnt dst : Var) (srcs : List Var) (s : State)
    (hcd : cnt ≠ dst)
    (hdist : ∀ src ∈ srcs, src ≠ dst ∧ src ≠ cnt) :
    (tallyCells cnt dst srcs).cost s
        ≤ 1 + (srcs.map (fun src => tallyRegCost (State.get s src).length)).sum := by
  have hc0cost : (Cmd.op (.clear dst)).cost s = 1 := rfl
  have hmap : srcs.map (fun src => tallyRegCost (State.get ((Cmd.op (.clear dst)).eval s) src).length)
      = srcs.map (fun src => tallyRegCost (State.get s src).length) := by
    apply List.map_congr_left
    intro src hs'
    have : (Cmd.op (.clear dst)).eval s = s.set dst [] := rfl
    rw [this, State.get_set_ne _ _ _ _ (hdist src hs').1]
  have h := tallyCells_cost_go cnt dst srcs (Cmd.op (.clear dst)) s hcd hdist
  rw [hc0cost, hmap] at h
  rw [tallyCells]; exact h

/-! ## Cost bound for `emitRegs` (C8-4)

The reg-2 input-string emitter's cost bound, missing from the 2026-07-19-c run
lemma. Mirrors the `tallyCells_cost` `foldl` induction (per-source cost that
depends on the register's length at that fold step, sources read-only so the
lengths reduce to the input's) but each step contributes the two seq nodes, the
`appendItem dst 0` (`3`) and `reencLoop`'s quadratic bound (off = 1). -/

/-- The per-register cost contribution of the `emitRegs` fold at register length
`L`: two seq nodes + `appendItem dst 0` (`3`) + `reencLoop`'s bound
`3 + 13L + 2L²` (off = 1). -/
def emitRegCost (L : Nat) : Nat := 8 + 13 * L + 2 * (L * L)

/-- The `foldl` cost induction behind `emitRegs_cost`. -/
private theorem emitRegs_cost_go (cnt scan tflg dst : Var) :
    ∀ (srcs : List Var) (c0 : Cmd) (s : State),
      scan ≠ cnt → scan ≠ dst → scan ≠ tflg → dst ≠ cnt → dst ≠ tflg →
      (∀ src ∈ srcs, src ≠ dst ∧ src ≠ scan ∧ src ≠ tflg ∧ src ≠ cnt) →
      (∀ src ∈ srcs, ∀ x ∈ State.get (c0.eval s) src, x ≤ 1) →
      (srcs.foldl
          (fun c src => (c ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0)
          c0).cost s
        ≤ c0.cost s
          + (srcs.map (fun src => emitRegCost (State.get (c0.eval s) src).length)).sum := by
  intro srcs
  induction srcs with
  | nil => intro c0 s _ _ _ _ _ _ _; simp
  | cons src rest ih =>
      intro c0 s hsc hsd hst hdc hdt hdist hbits
      obtain ⟨hsrc_d, hsrc_s, hsrc_t, hsrc_c⟩ := hdist src (List.mem_cons_self ..)
      set c1 : Cmd := (c0 ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0 with hc1
      have hfold : (src :: rest).foldl
          (fun c src => (c ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0) c0
          = rest.foldl
            (fun c src => (c ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0) c1 := by
        rw [List.foldl_cons]
      set s0 : State := c0.eval s with hs0
      obtain ⟨_, hR2, hR3, hR4⟩ :=
        reencLoop_run 1 cnt scan tflg src dst s0 (State.get s0 src)
          hsc hsd hst hdc hdt rfl (hbits src (List.mem_cons_self ..))
      set sR : State := (reencLoop 1 cnt scan tflg src dst).eval s0 with hsR
      obtain ⟨_, hI2, hI3⟩ := appendItem_run dst 0 sR
      set L := (State.get s0 src).length with hL
      have hc1eval : c1.eval s = (appendItem dst 0).eval sR := by
        rw [hc1, Cmd.eval_seq, Cmd.eval_seq, ← hs0, ← hsR]
      have hc1cost : c1.cost s ≤ c0.cost s + emitRegCost L := by
        rw [hc1, Cmd.cost_seq, Cmd.cost_seq, Cmd.eval_seq, ← hs0, ← hsR, hI3]
        unfold emitRegCost
        have hexp : L * (L + 2 * 1 + 10) = L * L + 12 * L := by ring
        rw [hexp] at hR4
        generalize L * L = B at hR4 ⊢
        omega
      have hc1frame : ∀ r : Var, r ≠ dst → r ≠ scan → r ≠ tflg → r ≠ cnt →
          State.get (c1.eval s) r = State.get s0 r := by
        intro r h1 h2 h3 h4
        rw [hc1eval, hI2 r h1, hR3 r h2 h1 h3 h4]
      have hrest_bits : ∀ s' ∈ rest, ∀ x ∈ State.get (c1.eval s) s', x ≤ 1 := by
        intro s' hs' x hx
        obtain ⟨hd, hsc', ht', hcc'⟩ := hdist s' (List.mem_cons_of_mem _ hs')
        rw [hc1frame s' hd hsc' ht' hcc'] at hx
        exact hbits s' (List.mem_cons_of_mem _ hs') x hx
      have hmap : rest.map (fun s' => emitRegCost (State.get (c1.eval s) s').length)
          = rest.map (fun s' => emitRegCost (State.get s0 s').length) := by
        apply List.map_congr_left
        intro s' hs'
        obtain ⟨hd, hsc', ht', hcc'⟩ := hdist s' (List.mem_cons_of_mem _ hs')
        rw [hc1frame s' hd hsc' ht' hcc']
      have hIH := ih c1 s hsc hsd hst hdc hdt
        (fun s' hs' => hdist s' (List.mem_cons_of_mem _ hs')) hrest_bits
      rw [hfold]
      calc (rest.foldl
              (fun c src => (c ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0)
              c1).cost s
          ≤ c1.cost s
              + (rest.map (fun s' => emitRegCost (State.get (c1.eval s) s').length)).sum := hIH
        _ = c1.cost s
              + (rest.map (fun s' => emitRegCost (State.get s0 s').length)).sum := by rw [hmap]
        _ ≤ (c0.cost s + emitRegCost L)
              + (rest.map (fun s' => emitRegCost (State.get s0 s').length)).sum :=
            Nat.add_le_add_right hc1cost _
        _ = c0.cost s
              + ((src :: rest).map (fun s' => emitRegCost (State.get s0 s').length)).sum := by
            rw [List.map_cons, List.sum_cons, ← hL, Nat.add_assoc]

/-- **`emitRegs` cost**: `≤ 11 + Σ_{src ∈ srcs} emitRegCost |src|` — the seed
`clear ;; appendItem dst 3` (`11`) plus, per source, the fold's per-register
contribution. A polynomial in the input register lengths (the `inOPoly` input
for the C8-4 witness's cost field). -/
theorem emitRegs_cost (cnt scan tflg dst : Var) (srcs : List Var) (s : State)
    (hsc : scan ≠ cnt) (hsd : scan ≠ dst) (hst : scan ≠ tflg)
    (hdc : dst ≠ cnt) (hdt : dst ≠ tflg)
    (hdist : ∀ src ∈ srcs, src ≠ dst ∧ src ≠ scan ∧ src ≠ tflg ∧ src ≠ cnt)
    (hbits : ∀ src ∈ srcs, ∀ x ∈ State.get s src, x ≤ 1) :
    (emitRegs cnt scan tflg dst srcs).cost s
        ≤ 11 + (srcs.map (fun src => emitRegCost (State.get s src).length)).sum := by
  set c0 : Cmd := Cmd.op (.clear dst) ;; appendItem dst 3 with hc0
  have hclear : (Cmd.op (.clear dst)).eval s = s.set dst [] := rfl
  have hc0eval : c0.eval s = (appendItem dst 3).eval (s.set dst []) := by
    rw [hc0, Cmd.eval_seq, hclear]
  have hc0frame : ∀ r : Var, r ≠ dst → State.get (c0.eval s) r = State.get s r := by
    intro r hr
    obtain ⟨_, hA2, _⟩ := appendItem_run dst 3 (s.set dst [])
    rw [hc0eval, hA2 r hr, State.get_set_ne _ _ _ _ hr]
  have hc0cost : c0.cost s = 11 := by
    obtain ⟨_, _, hA3⟩ := appendItem_run dst 3 (s.set dst [])
    rw [hc0, Cmd.cost_seq, Cmd.cost_op, hclear, hA3]
    rfl
  have hc0bits : ∀ src ∈ srcs, ∀ x ∈ State.get (c0.eval s) src, x ≤ 1 := by
    intro src hs' x hx
    rw [hc0frame src (hdist src hs').1] at hx
    exact hbits src hs' x hx
  have hmap : srcs.map (fun src => emitRegCost (State.get (c0.eval s) src).length)
      = srcs.map (fun src => emitRegCost (State.get s src).length) := by
    apply List.map_congr_left
    intro src hs'
    rw [hc0frame src (hdist src hs').1]
  have h := emitRegs_cost_go cnt scan tflg dst srcs c0 s hsc hsd hst hdc hdt hdist hc0bits
  rw [hc0cost, hmap] at h
  rw [emitRegs]; exact h

end FrontPieces
