import Complexity.NP.SAT.CookLevin.Reductions.FrontProgram
import Complexity.NP.SAT.CookLevin.Reductions.FrontLifting

set_option autoImplicit false

/-! # C8-4 piece 3 — the `PolyTimeComputableLang` front witness `W_Q`

The final piece of the C8-4 assembly. C8-0…C8-3, the front machine + machine-iff
(`FrontMachine.lean`), the abstract lifting (`FrontLifting.lean`,
`fQ_correct`/`fQ_correct_concrete`) and the reduction program
(`FrontProgram.lean`, `frontProgram_run`) are all done & axiom-clean. This module
consumes them as black boxes and produces the honest reduction witness

  `W_Q : PolyTimeComputableLang (fQ W Mmax Mstep)`

and, wrapping it with `fQ_correct`, the endpoint reduction
`Q ⪯p' FlatSingleTMGenNP`.

## The settled design (2026-08-02 — the input encoding is `encX`, full stop)

* **`encodeIn x := W.encX x`.** Nothing appended, nothing rearranged. This is
  the whole point of the top-down honesty programme at the head of the chain:
  by FINDING AK the composite's `ComputesBy.encode` *is* this function, so
  after this change there is no head-side encoding to audit at all — and under
  `NPhardStr` it is literally `certState`, the raw input string.
  ⚠ Until 2026-08-02 it was `W.encX x ++ [1^(encodable.size x)]`: the reduction
  was **handed** its input's size because the 2026-07-20-c finding showed the
  on-machine tally had no provable lower bound to `encodable.size x`. The
  `sizeLB` field of `InNPWitnessLangFreeSplit` supplies that bound, so the
  register is gone and `FrontPieces.tallyCells` counts the cells instead.
* **`Mmax`/`Mstep`** are F6 overshoot monomials in the **tally**
  `State.size (W.encX x)`, not in `encodable.size x`. Their constants come from
  `inOPoly_monomial_bound` applied **twice**: once to `maxSizeOf`/`stepsOf`
  (monomials in `size x`), then to that monomial composed with `W.sizeLB`
  (monomials in the tally). `inOPoly_comp` needs no monotonicity, and the
  intermediate monomial is monotone, which is what makes the two-step chain go
  through — see `front_reducesPolyMO'`.
* **`decodeOut`** reads the machine as the per-`Q` CONSTANT `M_Q` (honest: reg 1
  genuinely holds `encSyms (flattenTM M_Q)`), reg 2 through the `encSyms` inverse
  `decodeSyms` (a genuine left inverse — no `Classical`), and regs 3/4 by length.

The correctness iff is `fQ_correct` (NOT `fQ_correct_concrete` — the monomials
overshoot, they do not hit `maxSizeOf` exactly), with `hmax`/`hsteps` discharged
from the monomial bounds.
-/

namespace Complexity.Lang.FrontWitness

open Complexity.Lang
open Complexity.Lang.FrontMachine
open Complexity.Lang.FrontLifting
open FrontPieces
open FrontProgram (frontProgram)
open HeadLayout (encSyms encSyms_append encSyms_bit flattenTM headRegBound headEncodeIn)

/-! ## Foundational list/state helpers -/

/-- Reading a register strictly inside the input part of an appended state is
unaffected by the appendage. -/
theorem get_append_lt {l r : State} {i : Nat} (h : i < l.length) :
    State.get (l ++ r) i = State.get l i := by
  unfold State.get
  rw [List.getElem?_append_left h]

/-- The register appended just past the input part is read at index `l.length`. -/
theorem get_append_last (l : State) (v : List Nat) :
    State.get (l ++ [v]) l.length = v := by
  unfold State.get
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Enumerating `State.get` over `range l.length` recovers `l`. -/
theorem map_range_get (l : State) :
    (List.range l.length).map (State.get l) = l := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    show State.get l i = l[i]
    unfold State.get
    rw [List.getElem?_eq_getElem h2]
    rfl

/-- `State.size (w :: s) = |w| + State.size s`. -/
private theorem size_cons (w : List Nat) (s : State) :
    State.size (w :: s) = w.length + State.size s := rfl

/-- `State.size` is the sum of the register lengths. -/
theorem size_eq_sum_lengths (l : State) : State.size l = (l.map List.length).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [size_cons, ih, List.map_cons, List.sum_cons]

/-- **What `tallyCells` computes on a state of exactly `l.length` registers**:
summing the lengths of registers `0 … l.length-1` gives `State.size l`. This is
the arithmetic that lets the front program count its own input's cells instead
of being handed the count. -/
theorem sum_range_get_length (l : State) :
    ((List.range l.length).map (fun i => (State.get l i).length)).sum = State.size l :=
  calc ((List.range l.length).map (fun i => (State.get l i).length)).sum
      = (((List.range l.length).map (State.get l)).map List.length).sum := by
        rw [List.map_map]; rfl
    _ = (l.map List.length).sum := by rw [map_range_get l]
    _ = State.size l := (size_eq_sum_lengths l).symm

/-- `State.size` of an appended single register. -/
theorem size_append_one (l : State) (v : List Nat) :
    State.size (l ++ [v]) = State.size l + v.length := by
  induction l with
  | nil => show State.size [v] = State.size [] + v.length; simp [State.size]
  | cons a t ih =>
      show State.size (a :: (t ++ [v])) = State.size (a :: t) + v.length
      rw [size_cons, size_cons, ih]; omega

/-! ## The `encSyms` inverse (a genuine left inverse — no `Classical`)

`encSyms l` is a `0`-separated stream of unary blocks: each symbol `v` becomes
`1^(v+1) 0`. It is prefix-free, hence injective; we exhibit the decoder. -/

/-- The `encSyms` block of a single symbol is `1^(v+1)` followed by `0`. -/
theorem encSyms_cons (v : Nat) (l : List Nat) :
    encSyms (v :: l) = (List.replicate (v + 1) 1 ++ [0]) ++ encSyms l := by
  rw [show v :: l = [v] ++ l from rfl, encSyms_append]
  congr 1

/-- `takeWhile (·==1)` of `1^n 0 …` is exactly `1^n` — the run-length reader. -/
private theorem takeWhile_one_run (n : Nat) (t : List Nat) :
    (List.replicate n 1 ++ (0 :: t)).takeWhile (· == 1) = List.replicate n 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append,
        List.takeWhile_cons_of_pos (by simp), ih]

/-- **`encSyms` is injective.** Read the leading unary run length off each block. -/
theorem encSyms_injective : Function.Injective encSyms := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ h
      cases l₂ with
      | nil => rfl
      | cons b bs =>
          rw [show encSyms [] = ([] : List Nat) from rfl, encSyms_cons] at h
          simp [List.replicate_succ] at h
  | cons a as ih =>
      intro l₂ h
      cases l₂ with
      | nil =>
          rw [show encSyms [] = ([] : List Nat) from rfl, encSyms_cons] at h
          simp [List.replicate_succ] at h
      | cons b bs =>
          rw [encSyms_cons, encSyms_cons] at h
          -- read the leading run length off both sides
          have hlen : a + 1 = b + 1 := by
            have hc := congrArg (List.takeWhile (· == 1)) h
            rw [List.append_assoc, List.append_assoc,
              show ([0] ++ encSyms as) = (0 :: encSyms as) from rfl,
              show ([0] ++ encSyms bs) = (0 :: encSyms bs) from rfl,
              takeWhile_one_run, takeWhile_one_run] at hc
            have := congrArg List.length hc
            simpa using this
          have hab : a = b := by omega
          subst hab
          have hrest : encSyms as = encSyms bs := List.append_cancel_left h
          rw [ih hrest]

/-- The `encSyms` decoder (its genuine left inverse). -/
noncomputable def decodeSyms : List Nat → List Nat :=
  Function.invFun encSyms

theorem decodeSyms_encSyms (l : List Nat) : decodeSyms (encSyms l) = l :=
  Function.leftInverse_invFun encSyms_injective l

/-! ## The global monomial bound (F6 constants extractor)

`inOPoly f` gives `f n ≤ c·n^k` past `n0`; folding the `< n0` prefix into an
additive constant yields a bound of the form `c·(n+1)^k + d` valid for **all**
`n`. This is the reusable helper that extracts the F6 overshoot monomials'
constants for both `maxSize` and `steps`. -/

/-- **Global monomial bound.** A polynomially-bounded function is everywhere
dominated by a concrete monomial `c·(n+1)^k + d`. -/
theorem inOPoly_monomial_bound {f : Nat → Nat} (hf : inOPoly f) :
    ∃ c k d, ∀ n, f n ≤ c * (n + 1) ^ k + d := by
  obtain ⟨k, c, n0, h⟩ := hf
  refine ⟨c, k, maxPrefix f n0, ?_⟩
  intro n
  by_cases hn : n0 ≤ n
  · calc f n ≤ c * n ^ k := h n hn
      _ ≤ c * (n + 1) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ n) k)
      _ ≤ c * (n + 1) ^ k + maxPrefix f n0 := Nat.le_add_right _ _
  · calc f n ≤ maxPrefix f n0 := le_maxPrefix f (Nat.le_of_lt (Nat.lt_of_not_le hn))
      _ ≤ c * (n + 1) ^ k + maxPrefix f n0 := Nat.le_add_left _ _

/-! ## Register-frame (`UsesBelow`) lemmas for the gadgets and the program

`Cmd.UsesBelow c k` is a structural property (each op/branch touches only
registers `< k`). The gadgets are built by `foldl`/recursion, so their
`UsesBelow` needs the corresponding induction. These are the `usesBelow`/
`width_le`/`decode_agree` inputs of the witness (and are reusable by C8-5). -/

theorem appendBit_usesBelow {dst : Var} {b k : Nat} (hd : dst < k) :
    Cmd.UsesBelow (appendBit dst b) k := by
  unfold appendBit
  by_cases hb : b = 1 <;> simp only [hb, if_true, if_false, Cmd.UsesBelow, Op.UsesBelow] <;>
    first | exact hd | (split <;> exact hd)

theorem appendConst_usesBelow {c0 : Cmd} {dst : Var} {bits : List Nat} {k : Nat}
    (hc0 : Cmd.UsesBelow c0 k) (hd : dst < k) :
    Cmd.UsesBelow (appendConst c0 dst bits) k := by
  induction bits generalizing c0 with
  | nil => exact hc0
  | cons b bs ih => exact ih ⟨hc0, appendBit_usesBelow hd⟩

theorem emitConst_usesBelow {dst : Var} {bits : List Nat} {k : Nat} (hd : dst < k) :
    Cmd.UsesBelow (emitConst dst bits) k :=
  appendConst_usesBelow (show Cmd.UsesBelow (Cmd.op (.clear dst)) k from hd) hd

theorem appendItem_usesBelow {dst : Var} {v k : Nat} (hd : dst < k) :
    Cmd.UsesBelow (appendItem dst v) k :=
  appendConst_usesBelow (show Cmd.UsesBelow (Cmd.op (.appendOne dst)) k from hd) hd

theorem reencBody_usesBelow {off : Nat} {scan dst tflg k : Var}
    (hs : scan < k) (hd : dst < k) (ht : tflg < k) :
    Cmd.UsesBelow (reencBody off scan dst tflg) k :=
  ⟨⟨ht, hs⟩, ⟨hs, hs⟩, ht, appendItem_usesBelow hd, appendItem_usesBelow hd⟩

theorem reencLoop_usesBelow {off : Nat} {cnt scan tflg src dst k : Var}
    (hc : cnt < k) (hs : scan < k) (ht : tflg < k) (hsr : src < k) (hd : dst < k) :
    Cmd.UsesBelow (reencLoop off cnt scan tflg src dst) k :=
  ⟨⟨hs, hsr⟩, hc, hs, reencBody_usesBelow hs hd ht⟩

theorem emitRegs_usesBelow {cnt scan tflg dst : Var} {srcs : List Var} {k : Nat}
    (hc : cnt < k) (hs : scan < k) (ht : tflg < k) (hd : dst < k)
    (hsrcs : ∀ src ∈ srcs, src < k) :
    Cmd.UsesBelow (emitRegs cnt scan tflg dst srcs) k := by
  unfold emitRegs
  suffices h : ∀ (l : List Var) (c0 : Cmd), Cmd.UsesBelow c0 k → (∀ src ∈ l, src < k) →
      Cmd.UsesBelow (l.foldl
        (fun c src => (c ;; reencLoop 1 cnt scan tflg src dst) ;; appendItem dst 0) c0) k by
    exact h srcs _ ⟨hd, appendItem_usesBelow hd⟩ hsrcs
  intro l
  induction l with
  | nil => intro c0 hc0 _; exact hc0
  | cons src rest ih =>
      intro c0 hc0 hmem
      refine ih _ ⟨⟨hc0, reencLoop_usesBelow hc hs ht (hmem src (List.mem_cons_self ..)) hd⟩,
        appendItem_usesBelow hd⟩ (fun s hs' => hmem s (List.mem_cons_of_mem _ hs'))

theorem mulStep_usesBelow {cnt base tmp acc k : Var}
    (hc : cnt < k) (hb : base < k) (ht : tmp < k) (ha : acc < k) :
    Cmd.UsesBelow (mulStep cnt base tmp acc) k := by
  unfold mulStep
  exact ⟨ht, ⟨hc, hb, ⟨ht, ht, ha⟩⟩, ⟨ha, ht⟩⟩

theorem powLoop_usesBelow {cnt base tmp acc : Var} (K : Nat) {k : Nat}
    (hc : cnt < k) (hb : base < k) (ht : tmp < k) (ha : acc < k) :
    Cmd.UsesBelow (powLoop cnt base tmp acc K) k := by
  induction K with
  | zero => exact ⟨ha, ha⟩
  | succ K ih => exact ⟨ih, mulStep_usesBelow hc hb ht ha⟩

theorem unaryMonomial_usesBelow {c K d : Nat} {cnt base tmp src dst k : Var}
    (hc : cnt < k) (hb : base < k) (ht : tmp < k) (hsr : src < k) (hd : dst < k) :
    Cmd.UsesBelow (unaryMonomial c K d cnt base tmp src dst) k := by
  unfold unaryMonomial
  refine appendConst_usesBelow ⟨⟨hb, hsr⟩, hb, emitConst_usesBelow hd,
    powLoop_usesBelow K hc hb ht hd⟩ hd

theorem tallyReg_usesBelow {cnt src dst : Var} {k : Nat}
    (hc : cnt < k) (hs : src < k) (hd : dst < k) :
    Cmd.UsesBelow (tallyReg cnt src dst) k := ⟨hc, hs, hd⟩

theorem tallyCells_usesBelow {cnt dst : Var} {srcs : List Var} {k : Nat}
    (hc : cnt < k) (hd : dst < k) (hsrcs : ∀ src ∈ srcs, src < k) :
    Cmd.UsesBelow (tallyCells cnt dst srcs) k := by
  unfold tallyCells
  suffices h : ∀ (l : List Var) (c0 : Cmd), Cmd.UsesBelow c0 k → (∀ src ∈ l, src < k) →
      Cmd.UsesBelow (l.foldl (fun c src => c ;; tallyReg cnt src dst) c0) k by
    exact h srcs _ hd hsrcs
  intro l
  induction l with
  | nil => intro c0 hc0 _; exact hc0
  | cons src rest ih =>
      intro c0 hc0 hmem
      exact ih _ ⟨hc0, tallyReg_usesBelow hc (hmem src (List.mem_cons_self ..)) hd⟩
        (fun s hs' => hmem s (List.mem_cons_of_mem _ hs'))

/-- **`frontProgram` touches only registers `< B + 10`** (the witness's
`regBound`; `B+9` is the on-machine tally added 2026-08-02). -/
theorem frontProgram_usesBelow (MQconst : List Nat) (xWidth B : Nat)
    (cm km dm cs ks ds : Nat) (hB : 5 ≤ B) (hxW : xWidth < B) :
    Cmd.UsesBelow (frontProgram MQconst xWidth B cm km dm cs ks ds) (B + 10) := by
  -- ⚠ `Var` is an `abbrev` for `Nat` that `omega` does NOT see through; every
  -- register goal `x < k` must be `change (_ : Nat) < _`-retyped before `omega`.
  have ht : Cmd.UsesBelow (tallyCells (B + 4) (B + 9) (List.range xWidth)) (B + 10) := by
    refine tallyCells_usesBelow ?_ ?_ ?_
    · change (_ : Nat) < _; omega
    · change (_ : Nat) < _; omega
    · intro src hsrc; have := List.mem_range.mp hsrc; change (_ : Nat) < _; omega
  have he : Cmd.UsesBelow (emitRegs (B + 4) (B + 5) (B + 6) B (List.range xWidth)) (B + 10) := by
    refine emitRegs_usesBelow ?_ ?_ ?_ ?_ ?_
    · change (_ : Nat) < _; omega
    · change (_ : Nat) < _; omega
    · change (_ : Nat) < _; omega
    · change (_ : Nat) < _; omega
    · intro src hsrc; have := List.mem_range.mp hsrc; change (_ : Nat) < _; omega
  have hm1 : Cmd.UsesBelow
      (unaryMonomial cm km dm (B + 4) (B + 7) (B + 8) (B + 9) (B + 1)) (B + 10) := by
    refine unaryMonomial_usesBelow ?_ ?_ ?_ ?_ ?_ <;> · change (_ : Nat) < _; omega
  have hm2 : Cmd.UsesBelow
      (unaryMonomial cs ks ds (B + 4) (B + 7) (B + 8) (B + 9) (B + 2)) (B + 10) := by
    refine unaryMonomial_usesBelow ?_ ?_ ?_ ?_ ?_ <;> · change (_ : Nat) < _; omega
  have hec : Cmd.UsesBelow (emitConst (B + 3) MQconst) (B + 10) := by
    refine emitConst_usesBelow ?_; change (_ : Nat) < _; omega
  unfold frontProgram
  refine ⟨ht, he, hm1, hm2, hec, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    · change (_ : Nat) < _; omega

/-! ## The per-`Q` reduction witness `W_Q`

Everything is assembled over an honest split free-line verifier witness `W`, the
extracted F6 monomial constants `(cm,km,dm)`/`(cs,ks,ds)`, and their domination
bounds `hmB`/`hsB`. -/

variable {X : Type} [encodable X] {Q : X → Prop}

/-- Reading a register at an in-range index yields a member of the state. -/
theorem get_mem {l : State} {i : Nat} (h : i < l.length) : State.get l i ∈ l := by
  unfold State.get
  rw [List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- **The reduction's input layout: `encX`, and nothing else** (2026-08-02).
By FINDING AK this function *is* the composite reduction's `ComputesBy.encode`,
so keeping it equal to the hypothesis's own input layout is the entire head-side
honesty story — under `NPhardStr` it is `certState`, the raw input string.
The unary size register this used to append is now computed on-machine by
`FrontPieces.tallyCells` (see `FrontProgram`). -/
def encodeInQ (W : InNPWitnessLangFreeSplit Q) (x : X) : State := W.encX x

/-- The per-`Q` front machine (a constant). -/
def MmachineQ (W : InNPWitnessLangFreeSplit Q) : flatTM :=
  MQ W.verifier.c W.verifier.regBound W.xWidth

/-- The reg-1 machine constant — `encSyms (flattenTM M_Q)`. -/
def MconstQ (W : InNPWitnessLangFreeSplit Q) : List Nat :=
  encSyms (flattenTM (MmachineQ W))

/-- The scratch base: high enough for both the head layout and the input. -/
def BwidthQ (W : InNPWitnessLangFreeSplit Q) : Nat := max headRegBound (W.xWidth + 1)

/-- The F6 overshoot monomials, as functions of the **on-machine tally**
`State.size (W.encX x)` — the quantity the program can actually count. Their
constants are extracted through `W.sizeLB` in `front_reducesPolyMO'`. -/
def MmaxF (W : InNPWitnessLangFreeSplit Q) (cm km dm : Nat) (x : X) : Nat :=
  cm * (State.size (W.encX x) + 1) ^ km + dm
def MstepF (W : InNPWitnessLangFreeSplit Q) (cs ks ds : Nat) (x : X) : Nat :=
  cs * (State.size (W.encX x) + 1) ^ ks + ds

/-- **The reduction's output decoder.** The machine is the per-`Q` constant
`M_Q` (honest: reg 1 genuinely holds `encSyms (flattenTM M_Q)`); reg 2 through the
`encSyms` inverse; regs 3/4 by length. -/
noncomputable def decodeOutQ (W : InNPWitnessLangFreeSplit Q)
    (st : State) : flatTM × List Nat × Nat × Nat :=
  (MmachineQ W, decodeSyms (State.get st 2), (State.get st 3).length, (State.get st 4).length)

/-- The reduction program. -/
def cQ (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) : Cmd :=
  frontProgram (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds

theorem BwidthQ_ge5 (W : InNPWitnessLangFreeSplit Q) : 5 ≤ BwidthQ W := by
  unfold BwidthQ
  have : headRegBound ≤ max headRegBound (W.xWidth + 1) := le_max_left _ _
  simpa [headRegBound] using this

theorem xWidth_lt_BwidthQ (W : InNPWitnessLangFreeSplit Q) : W.xWidth < BwidthQ W :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

/-- **What the on-machine tally computes**: summing the lengths of the input
registers gives `State.size (encX x)` — the monomial argument. This is the
`frontProgram_run` hypothesis that replaced the handed-over size register. -/
theorem encodeInQ_tally (W : InNPWitnessLangFreeSplit Q) (x : X) :
    ((List.range W.xWidth).map (fun src => (State.get (encodeInQ W x) src).length)).sum
      = State.size (W.encX x) := by
  show ((List.range W.xWidth).map (fun src => (State.get (W.encX x) src).length)).sum = _
  rw [← W.encX_width x]
  exact sum_range_get_length (W.encX x)

/-- The input encoding is bit-level. -/
theorem encodeInQ_bit (W : InNPWitnessLangFreeSplit Q) (x : X) :
    Compile.BitState (encodeInQ W x) := encX_bit W x

/-- The `frontProgram_run` bit hypothesis for the input registers. -/
theorem encodeInQ_bits (W : InNPWitnessLangFreeSplit Q) (x : X) :
    ∀ src ∈ List.range W.xWidth, ∀ y ∈ State.get (encodeInQ W x) src, y ≤ 1 := by
  intro src hsrc y hy
  have hlt : src < W.xWidth := List.mem_range.mp hsrc
  have hsrc' : src < (W.encX x).length := by rw [W.encX_width x]; exact hlt
  exact encX_bit W x _ (get_mem hsrc') y hy

/-- **`computes`** — the decoded output is `fQ x`. Consumes `frontProgram_run`
(the four output registers), the `encSyms` left inverse, and the register
enumeration `map_range_get`. -/
theorem computesQ (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) (x : X) :
    decodeOutQ W ((cQ W cm km dm cs ks ds).eval (encodeInQ W x))
      = fQ W (MmaxF W cm km dm) (MstepF W cs ks ds) x := by
  obtain ⟨_h0, _h1, h2, h3, h4⟩ :=
    FrontProgram.frontProgram_run (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds
      (encodeInQ W x) (State.size (W.encX x)) (BwidthQ_ge5 W) (xWidth_lt_BwidthQ W)
      (fun v hv => encSyms_bit _ v hv) (encodeInQ_tally W x) (encodeInQ_bits W x)
  -- reg 2's source enumeration recovers `encX x`
  have hmap : (List.range W.xWidth).map (State.get (encodeInQ W x)) = W.encX x := by
    show (List.range W.xWidth).map (State.get (W.encX x)) = _
    rw [← W.encX_width x, map_range_get]
  unfold decodeOutQ fQ MmaxF MstepF cQ MmachineQ
  rw [h2, h3, h4, hmap, decodeSyms_encSyms, List.length_replicate, List.length_replicate]

/-- **`encodeIn_size`** — the input layout is the hypothesis's own, so its size
bound is the hypothesis's own (`encX_size`), with nothing added. -/
theorem encodeInQ_size_le (W : InNPWitnessLangFreeSplit Q) (x : X) :
    State.size (encodeInQ W x) ≤ W.dBound (encodable.size x) := W.encX_size x

/-- **`width_le`** — the input occupies `xWidth` registers, within the frame. -/
theorem encodeInQ_width (W : InNPWitnessLangFreeSplit Q) (x : X) :
    (encodeInQ W x).length ≤ BwidthQ W + 10 := by
  show (W.encX x).length ≤ _
  rw [W.encX_width x]
  have := xWidth_lt_BwidthQ W
  omega

/-- **`decode_agree`** — padding the input by empty registers past the frame
does not change the decoded output (regs 2/3/4 are inside the frame). -/
theorem decodeOutQ_agree (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat)
    (x : X) (m : Nat) :
    decodeOutQ W ((cQ W cm km dm cs ks ds).eval (encodeInQ W x ++ List.replicate m []))
      = decodeOutQ W ((cQ W cm km dm cs ks ds).eval (encodeInQ W x)) := by
  have hub := frontProgram_usesBelow (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds
    (BwidthQ_ge5 W) (xWidth_lt_BwidthQ W)
  have hagree : AgreeBelow (BwidthQ W + 10) (encodeInQ W x ++ List.replicate m []) (encodeInQ W x) :=
    fun r _ => State.get_append_replicate_nil (encodeInQ W x) m r
  have hR := fun r (hr : r < BwidthQ W + 10) =>
    Cmd.eval_agree (frontProgram (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds)
      (BwidthQ W + 10) hub hagree r hr
  unfold decodeOutQ cQ
  rw [hR 2 (by omega), hR 3 (by omega), hR 4 (by omega)]

/-! ### The cost bound

The two arithmetic obligations `cQ_cost_le` and `fQ_output_size_le`, closed
against a single-summand polynomial `costBoundQ` (2026-07-24-b). The program cost
decomposes (via `FrontProgram.frontProgram_cost_le`) into the `emitRegs` cost
(bounded by `emitRegs_cost` + a per-register length bound), the two
`unaryMonomial` stages (`monomialCost`, dominated by the closed-form `monoUB` via
`powCost_le`), the constant `emitConst`, and the five `clear`/`copy` ops; the
output size decomposes into the machine constant + the `encodeRegs` register + the
two budget monomials. Every piece is `monotonic` and `inOPoly`. -/

/-! #### Generic list/size/`inOPoly` helpers -/

/-- A member register's length is bounded by the aggregate state size. -/
theorem mem_length_le_size {s : State} {r : List Nat} (h : r ∈ s) :
    r.length ≤ State.size s := by
  induction s with
  | nil => cases h
  | cons a t ih =>
      rw [List.mem_cons] at h
      show r.length ≤ State.size (a :: t)
      rw [show State.size (a :: t) = a.length + State.size t from rfl]
      rcases h with h | h
      · subst h; omega
      · have := ih h; omega

/-- Reading a register at any index yields a length bounded by the state size. -/
theorem get_length_le_size (s : State) (i : Nat) :
    (State.get s i).length ≤ State.size s := by
  by_cases h : i < s.length
  · exact mem_length_le_size (get_mem h)
  · have : State.get s i = [] := by
      unfold State.get; rw [List.getElem?_eq_none (Nat.le_of_not_lt h)]; rfl
    rw [this]; simp

/-- `fun n => (n+1)^k` is polynomially bounded. -/
theorem inOPoly_pow_succ (k : Nat) : inOPoly (fun n => (n + 1) ^ k) := by
  refine ⟨k, 2 ^ k, 1, ?_⟩
  intro n hn
  calc (n + 1) ^ k ≤ (2 * n) ^ k := Nat.pow_le_pow_left (by omega) k
    _ = 2 ^ k * n ^ k := by rw [Nat.mul_pow]

/-- `fun n => (n+1)^k` is monotonic. -/
theorem monotonic_pow_succ (k : Nat) : monotonic (fun n => (n + 1) ^ k) := by
  intro x y h; exact Nat.pow_le_pow_left (by omega) k

/-- `emitRegCost` is monotonic in the register length. -/
theorem emitRegCost_mono {a b : Nat} (h : a ≤ b) : emitRegCost a ≤ emitRegCost b := by
  unfold emitRegCost; gcongr

/-- `fun n => emitRegCost (g n)` is `inOPoly` when `g` is. -/
theorem emitRegCost_comp_poly {g : Nat → Nat} (hg : inOPoly g) :
    inOPoly (fun n => emitRegCost (g n)) := by
  unfold emitRegCost
  exact inOPoly_add (inOPoly_add (inOPoly_const 8) (inOPoly_mul (inOPoly_const 13) hg))
    (inOPoly_mul (inOPoly_const 2) (inOPoly_mul hg hg))

/-- `tallyRegCost` is monotonic in the register length. -/
theorem tallyRegCost_mono {a b : Nat} (h : a ≤ b) : tallyRegCost a ≤ tallyRegCost b := by
  unfold tallyRegCost; gcongr

/-- `fun n => tallyRegCost (g n)` is `inOPoly` when `g` is. -/
theorem tallyRegCost_comp_poly {g : Nat → Nat} (hg : inOPoly g) :
    inOPoly (fun n => tallyRegCost (g n)) := by
  unfold tallyRegCost
  exact inOPoly_add (inOPoly_add (inOPoly_const 2) (inOPoly_mul hg (inOPoly_const 5)))
    (inOPoly_mul hg hg)

/-- `encodable.size` of a `List Nat` with cells `≤ c` is `≤ (c+1)·|l|`. -/
theorem list_nat_size_le (l : List Nat) (c : Nat) (h : ∀ v ∈ l, v ≤ c) :
    encodable.size l ≤ (c + 1) * l.length := by
  induction l with
  | nil => simp [encodable_size_list_nil]
  | cons a t ih =>
      rw [encodable_size_list_cons]
      have ha : a ≤ c := h a (List.mem_cons_self ..)
      have hsz : encodable.size a = a := rfl
      have := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
      rw [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- `encSyms` length with cells `≤ c` is `≤ (c+2)·|l|`. -/
theorem encSyms_length_le (l : List Nat) (c : Nat) (h : ∀ v ∈ l, v ≤ c) :
    (encSyms l).length ≤ (c + 2) * l.length := by
  induction l with
  | nil => simp [encSyms]
  | cons a t ih =>
      rw [encSyms_cons]
      have ha : a ≤ c := h a (List.mem_cons_self ..)
      have := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
      rw [List.length_append, List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- Cells of `encodeRegs s` for a `BitState` are `≤ 2` (shifted bits `{1,2}` and
the `0` separators). -/
theorem encodeRegs_cells_le {s : State} (h : Compile.BitState s) :
    ∀ v ∈ Compile.encodeRegs s, v ≤ 2 := by
  induction s with
  | nil => intro v hv; simp [Compile.encodeRegs_nil] at hv
  | cons reg t ih =>
      intro v hv
      rw [Compile.encodeRegs_cons, List.append_assoc, List.mem_append] at hv
      rcases hv with hv | hv
      · rw [Compile.shiftReg, List.mem_map] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        have := h reg (List.mem_cons_self ..) w hw; omega
      · rw [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | hv
        · omega
        · exact ih (fun r hr x hx => h r (List.mem_cons_of_mem _ hr) x hx) v hv

/-- The reg-2 source enumeration recovers `encX x` (also used inside `computesQ`). -/
theorem map_range_encX (W : InNPWitnessLangFreeSplit Q) (x : X) :
    (List.range W.xWidth).map (State.get (encodeInQ W x)) = W.encX x := by
  show (List.range W.xWidth).map (State.get (W.encX x)) = _
  rw [← W.encX_width x, map_range_get]

/-! #### The closed-form monomial bounds `monoUB` / `monoLin` -/

/-- The closed-form upper bound for `monomialCost c k d` (from `powCost_le`). -/
def monoUB (c k d : Nat) : Nat → Nat := fun n =>
  (c + 1) + k * (13 * ((n + 1 + 1) * ((n + 1 + 1) * ((c + 1) * ((n + 1) ^ k + 1)))))
    + 2 * c + 2 * d + n + 6

theorem monomialCost_le_monoUB (c k d n : Nat) : monomialCost c k d n ≤ monoUB c k d n := by
  unfold monomialCost monoUB
  have h := powCost_le (n + 1) c k (by omega)
  omega

theorem monoUB_poly (c k d : Nat) : inOPoly (monoUB c k d) := by
  have pLin : inOPoly (fun n => n + 1 + 1) :=
    inOPoly_add (inOPoly_add inOPoly_id (inOPoly_const 1)) (inOPoly_const 1)
  have pPow : inOPoly (fun n => (n + 1) ^ k + 1) :=
    inOPoly_add (inOPoly_pow_succ k) (inOPoly_const 1)
  have hMid : inOPoly (fun n =>
      k * (13 * ((n + 1 + 1) * ((n + 1 + 1) * ((c + 1) * ((n + 1) ^ k + 1)))))) :=
    inOPoly_mul (inOPoly_const k) (inOPoly_mul (inOPoly_const 13)
      (inOPoly_mul pLin (inOPoly_mul pLin (inOPoly_mul (inOPoly_const (c + 1)) pPow))))
  unfold monoUB
  exact inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add
    (inOPoly_add (inOPoly_const (c + 1)) hMid) (inOPoly_const (2 * c)))
    (inOPoly_const (2 * d))) inOPoly_id) (inOPoly_const 6)

theorem monoUB_mono (c k d : Nat) : monotonic (monoUB c k d) := by
  intro x y h; unfold monoUB; gcongr

/-- The closed-form budget monomial `c·(n+1)^k + d` (the `MmaxF`/`MstepF` shape). -/
def monoLin (c k d : Nat) : Nat → Nat := fun n => c * (n + 1) ^ k + d

theorem monoLin_poly (c k d : Nat) : inOPoly (monoLin c k d) :=
  inOPoly_add (inOPoly_mul (inOPoly_const c) (inOPoly_pow_succ k)) (inOPoly_const d)

theorem monoLin_mono (c k d : Nat) : monotonic (monoLin c k d) := by
  intro x y h; unfold monoLin; gcongr

/-! #### The bound `costBoundQ` -/

/-- **The per-`Q` cost/output bound.** A single polynomial dominating both the
reduction program's cost and the front instance's output size. ⚠ Since
2026-08-02 every monomial term is evaluated at `W.dBound n`, not at `n`: the
budget registers are monomials in the **on-machine tally**
`State.size (encX x) ≤ dBound n`, so the bound must be a polynomial in `n`
*through* `dBound`. The `2·monoLin` terms cover the two copy costs *and* the two
output budget monomials; the `tallyRegCost`/`emitRegCost` terms cover the two
per-input-register loops; `10·dBound n` covers the `s_x`/`encodeRegs` register
lengths; the constant absorbs the machine constant, `|MQconst|`, and slack. -/
noncomputable def costBoundQ (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    Nat → Nat := fun n =>
    monoUB cm km dm (W.dBound n) + monoUB cs ks ds (W.dBound n)
  + 2 * monoLin cm km dm (W.dBound n) + 2 * monoLin cs ks ds (W.dBound n)
  + W.xWidth * emitRegCost (W.dBound n)
  + W.xWidth * tallyRegCost (W.dBound n)
  + 10 * W.dBound n
  + (encodable.size (MmachineQ W) + 3 * (MconstQ W).length + 5 * W.xWidth + 100)

theorem costBoundQ_poly (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    inOPoly (costBoundQ W cm km dm cs ks ds) := by
  have hDn : inOPoly W.dBound := W.dBound_poly
  have comp : ∀ {g : Nat → Nat}, inOPoly g → inOPoly (fun n => g (W.dBound n)) :=
    fun hg => inOPoly_comp hDn hg
  unfold costBoundQ
  exact inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add
    (inOPoly_add (comp (monoUB_poly cm km dm)) (comp (monoUB_poly cs ks ds)))
    (inOPoly_mul (inOPoly_const 2) (comp (monoLin_poly cm km dm))))
    (inOPoly_mul (inOPoly_const 2) (comp (monoLin_poly cs ks ds))))
    (inOPoly_mul (inOPoly_const W.xWidth) (emitRegCost_comp_poly hDn)))
    (inOPoly_mul (inOPoly_const W.xWidth) (tallyRegCost_comp_poly hDn)))
    (inOPoly_mul (inOPoly_const 10) hDn))
    (inOPoly_const _)

theorem costBoundQ_mono (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    monotonic (costBoundQ W cm km dm cs ks ds) := by
  intro x y h
  have hD : W.dBound x ≤ W.dBound y := W.dBound_mono x y h
  have hm1 := monoUB_mono cm km dm _ _ hD
  have hm2 := monoUB_mono cs ks ds _ _ hD
  have hl1 := monoLin_mono cm km dm _ _ hD
  have hl2 := monoLin_mono cs ks ds _ _ hD
  have he : emitRegCost (W.dBound x) ≤ emitRegCost (W.dBound y) := emitRegCost_mono hD
  have ht : tallyRegCost (W.dBound x) ≤ tallyRegCost (W.dBound y) := tallyRegCost_mono hD
  unfold costBoundQ
  gcongr

/-! #### `cQ_cost_le` -/

theorem cQ_cost_le (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) (x : X) :
    (cQ W cm km dm cs ks ds).cost (encodeInQ W x)
      ≤ costBoundQ W cm km dm cs ks ds (encodable.size x) := by
  set n := encodable.size x with hn
  -- the tally value, and its bound by `dBound n`
  set t := State.size (W.encX x) with ht
  have htn : t ≤ W.dBound n := by rw [ht, hn]; exact W.encX_size x
  -- 1. the whole program cost, via frontProgram_cost_le
  have hfp := FrontProgram.frontProgram_cost_le (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds
    (encodeInQ W x) t (BwidthQ_ge5 W) (xWidth_lt_BwidthQ W)
    (fun y hy => encSyms_bit _ y hy) (encodeInQ_tally W x) (encodeInQ_bits W x)
  -- 2. each per-register sum is ≤ xWidth · (the cost at the whole state size)
  have hssize : State.size (encodeInQ W x) ≤ W.dBound n := encodeInQ_size_le W x
  have hsumE : ((List.range W.xWidth).map
        (fun src => emitRegCost (State.get (encodeInQ W x) src).length)).sum
      ≤ W.xWidth * emitRegCost (W.dBound n) := by
    have hbd : ∀ y ∈ (List.range W.xWidth).map
          (fun src => emitRegCost (State.get (encodeInQ W x) src).length),
        y ≤ emitRegCost (W.dBound n) := by
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨src, _, rfl⟩ := hy
      exact emitRegCost_mono (le_trans (get_length_le_size _ _) hssize)
    have := List.sum_le_card_nsmul _ _ hbd
    rw [List.length_map, List.length_range, smul_eq_mul] at this
    exact this
  have hsumT : ((List.range W.xWidth).map
        (fun src => tallyRegCost (State.get (encodeInQ W x) src).length)).sum
      ≤ W.xWidth * tallyRegCost (W.dBound n) := by
    have hbd : ∀ y ∈ (List.range W.xWidth).map
          (fun src => tallyRegCost (State.get (encodeInQ W x) src).length),
        y ≤ tallyRegCost (W.dBound n) := by
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨src, _, rfl⟩ := hy
      exact tallyRegCost_mono (le_trans (get_length_le_size _ _) hssize)
    have := List.sum_le_card_nsmul _ _ hbd
    rw [List.length_map, List.length_range, smul_eq_mul] at this
    exact this
  -- the s_x register-length bound
  have hsx : (encSyms (3 :: Compile.encodeRegs ((List.range W.xWidth).map (State.get (encodeInQ W x))))).length
      ≤ 5 * W.dBound n + 5 * W.xWidth + 5 := by
    rw [map_range_encX W x]
    have hcells : ∀ v ∈ (3 :: Compile.encodeRegs (W.encX x)), v ≤ 3 := by
      intro v hv
      rw [List.mem_cons] at hv
      rcases hv with rfl | hv
      · omega
      · have := encodeRegs_cells_le (encX_bit W x) v hv; omega
    have hlen := encSyms_length_le _ 3 hcells
    rw [List.length_cons, Compile.encodeRegs_length] at hlen
    have hw : (W.encX x).length = W.xWidth := W.encX_width x
    rw [hw] at hlen
    calc (encSyms (3 :: Compile.encodeRegs (W.encX x))).length
        ≤ (3 + 2) * (State.size (W.encX x) + W.xWidth + 1) := hlen
      _ ≤ 5 * W.dBound n + 5 * W.xWidth + 5 := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, ← ht]; omega
  -- monomialCost bounds, monotone in the argument, evaluated at `t ≤ dBound n`
  have hmc1 : monomialCost cm km dm t ≤ monoUB cm km dm (W.dBound n) :=
    le_trans (monomialCost_le_monoUB _ _ _ _) (monoUB_mono cm km dm _ _ htn)
  have hmc2 : monomialCost cs ks ds t ≤ monoUB cs ks ds (W.dBound n) :=
    le_trans (monomialCost_le_monoUB _ _ _ _) (monoUB_mono cs ks ds _ _ htn)
  have hml1 : cm * (t + 1) ^ km + dm ≤ monoLin cm km dm (W.dBound n) :=
    monoLin_mono cm km dm _ _ htn
  have hml2 : cs * (t + 1) ^ ks + ds ≤ monoLin cs ks ds (W.dBound n) :=
    monoLin_mono cs ks ds _ _ htn
  -- assemble
  unfold cQ costBoundQ
  omega

/-! #### `fQ_output_size_le` -/

theorem fQ_output_size_le (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) (x : X) :
    encodable.size (fQ W (MmaxF W cm km dm) (MstepF W cs ks ds) x)
      ≤ costBoundQ W cm km dm cs ks ds (encodable.size x) := by
  -- the product/list size decomposition (all defeq)
  have hfq : encodable.size (fQ W (MmaxF W cm km dm) (MstepF W cs ks ds) x)
      = encodable.size (MmachineQ W)
        + (encodable.size ((3 : Nat) :: Compile.encodeRegs (W.encX x))
          + (MmaxF W cm km dm x + MstepF W cs ks ds x + 1) + 1) + 1 := rfl
  -- the encodeRegs register size bound
  have hreg : encodable.size ((3 : Nat) :: Compile.encodeRegs (W.encX x))
      ≤ 4 * W.dBound (encodable.size x) + 4 * W.xWidth + 4 := by
    have hcells : ∀ v ∈ ((3 : Nat) :: Compile.encodeRegs (W.encX x)), v ≤ 3 := by
      intro v hv
      rw [List.mem_cons] at hv
      rcases hv with rfl | hv
      · omega
      · have := encodeRegs_cells_le (encX_bit W x) v hv; omega
    have hsize := list_nat_size_le _ 3 hcells
    rw [List.length_cons, Compile.encodeRegs_length, W.encX_width x] at hsize
    have hsz : State.size (W.encX x) ≤ W.dBound (encodable.size x) := W.encX_size x
    calc encodable.size ((3 : Nat) :: Compile.encodeRegs (W.encX x))
        ≤ (3 + 1) * (State.size (W.encX x) + W.xWidth + 1) := hsize
      _ ≤ 4 * W.dBound (encodable.size x) + 4 * W.xWidth + 4 := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
  -- the budget monomials are `monoLin` at the tally, itself ≤ `dBound n`
  have htn : State.size (W.encX x) ≤ W.dBound (encodable.size x) := W.encX_size x
  have hmx : MmaxF W cm km dm x ≤ monoLin cm km dm (W.dBound (encodable.size x)) :=
    monoLin_mono cm km dm _ _ htn
  have hms : MstepF W cs ks ds x ≤ monoLin cs ks ds (W.dBound (encodable.size x)) :=
    monoLin_mono cs ks ds _ _ htn
  unfold costBoundQ
  rw [hfq]
  omega

/-! ### The witness `W_Q` and the reduction -/

/-- **The per-`Q` front reduction witness** `W_Q : PolyTimeComputableLang (fQ …)`. -/
noncomputable def WQ (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    PolyTimeComputableLang (fQ W (MmaxF W cm km dm) (MstepF W cs ks ds)) where
  c := cQ W cm km dm cs ks ds
  encodeIn := encodeInQ W
  decodeOut := decodeOutQ W
  cost_bound := costBoundQ W cm km dm cs ks ds
  cost_bound_poly := costBoundQ_poly W cm km dm cs ks ds
  cost_bound_mono := costBoundQ_mono W cm km dm cs ks ds
  encBound := W.dBound
  encBound_poly := W.dBound_poly
  encBound_mono := W.dBound_mono
  encodeIn_size := encodeInQ_size_le W
  computes := computesQ W cm km dm cs ks ds
  cost_le := cQ_cost_le W cm km dm cs ks ds
  output_size_le := fQ_output_size_le W cm km dm cs ks ds
  enc_bit := encodeInQ_bit W
  regBound := BwidthQ W + 10
  usesBelow := frontProgram_usesBelow (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds
    (BwidthQ_ge5 W) (xWidth_lt_BwidthQ W)
  width_le := encodeInQ_width W
  decode_agree := decodeOutQ_agree W cm km dm cs ks ds

/-- **The F6 constants, extracted through `sizeLB`.** The budget registers the
program emits are monomials in the *on-machine tally* `State.size (encX x)`;
`fQ_correct` needs them to dominate budgets in `encodable.size x`. Two
applications of `inOPoly_monomial_bound` bridge the two:

1. `maxSizeOf`/`stepsOf` are `inOPoly`, so they are below `a·(size x + 1)^b + e`;
2. `encX_sizeLB` replaces `size x` by `sizeLB (tally)` inside that monomial
   (legitimate — the monomial is monotone), and the result is again `inOPoly`
   in the tally (`inOPoly_comp`, which needs no monotonicity of the outer
   function), so it is below `c·(tally + 1)^k + d`.

⚠ Step 2 is exactly what the 2026-07-20-c finding said was impossible without a
lower bound on the tally, and it is the whole reason the `sizeLB` field exists. -/
theorem exists_front_constants (W : InNPWitnessLangFreeSplit Q) :
    ∃ cm km dm cs ks ds : Nat,
      (∀ x, certBoundOf W (encodable.size x) + 2 ≤ MmaxF W cm km dm x)
      ∧ (∀ x c, W.rel x c → encodable.size c ≤ certBoundOf W (encodable.size x) →
          MQbudget W.verifier.c W.verifier.regBound (W.encX x ++ [certReg c])
            ≤ MstepF W cs ks ds x) := by
  obtain ⟨am, bm, em, hmB0⟩ := inOPoly_monomial_bound (maxSizeOf_poly W)
  obtain ⟨as, bs, es, hsB0⟩ := inOPoly_monomial_bound (stepsOf_poly W)
  have hpm : ∀ (a b e : Nat), inOPoly (fun t => a * (W.sizeLB t + 1) ^ b + e) := by
    intro a b e
    have hcomp : inOPoly (fun t => (W.sizeLB t + 1) ^ b) :=
      inOPoly_comp W.sizeLB_poly (inOPoly_pow_succ b)
    exact inOPoly_add (inOPoly_mul (inOPoly_const a) hcomp) (inOPoly_const e)
  obtain ⟨cm, km, dm, hmB⟩ := inOPoly_monomial_bound (hpm am bm em)
  obtain ⟨cs, ks, ds, hsB⟩ := inOPoly_monomial_bound (hpm as bs es)
  have chain : ∀ (a b e c k d : Nat), (∀ t, a * (W.sizeLB t + 1) ^ b + e ≤ c * (t + 1) ^ k + d) →
      ∀ (n : Nat) (x : X), n ≤ a * (encodable.size x + 1) ^ b + e →
        n ≤ c * (State.size (W.encX x) + 1) ^ k + d := by
    intro a b e c k d hlast n x hfirst
    refine le_trans hfirst (le_trans ?_ (hlast (State.size (W.encX x))))
    have := W.encX_sizeLB x
    gcongr
  exact ⟨cm, km, dm, cs, ks, ds,
    fun x => chain am bm em cm km dm hmB _ x (hmB0 (encodable.size x)),
    fun x c _hrel hsize => chain as bs es cs ks ds hsB _ x
      (le_trans (MQbudget_le W x c hsize) (hsB0 (encodable.size x)))⟩

/-- **C8-4 — the endpoint reduction `Q ⪯p' FlatSingleTMGenNP`.** For any NP
problem `Q` with an honest split free-line verifier witness, the per-`Q` front
construction is an honest TM-backed reduction into the corrected universal
front problem. The F6 monomial constants come from `exists_front_constants`;
correctness is `fQ_correct`. -/
theorem front_reducesPolyMO' (W : InNPWitnessLangFreeSplit Q) :
    Q ⪯p' FlatSingleTMGenNP := by
  obtain ⟨cm, km, dm, cs, ks, ds, hmax, hsteps⟩ := exists_front_constants W
  exact reducesPolyMO'_of_langFree (WQ W cm km dm cs ks ds)
    (fun x => (fQ_correct W (MmaxF W cm km dm) (MstepF W cs ks ds) hmax hsteps x).symm)

end Complexity.Lang.FrontWitness
