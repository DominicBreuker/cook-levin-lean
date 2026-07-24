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

## The settled design (HANDOFF C8-4, finding 2026-07-20-c — Option A)

The budget registers must dominate `size x`-bounds, so the F6 monomial argument
must be `encodable.size x`, materialized from a **unary size register** in the
input:

* **`encodeIn x := W.encX x ++ [1^(encodable.size x)]`** (size register at index
  `W.xWidth`). This is honest — a poly-time reduction may read its own input's
  size — and local to `W_Q` (the frozen C8-0 interface is untouched).
* **`Mmax`/`Mstep`** are the F6 overshoot monomials as functions of
  `encodable.size x`, with constants extracted classically from
  `maxSizeOf_poly`/`stepsOf_poly` via the global monomial bound
  `inOPoly_monomial_bound`.
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

/-- **`frontProgram` touches only registers `< B + 9`** (the witness's
`regBound`). -/
theorem frontProgram_usesBelow (MQconst : List Nat) (xWidth B : Nat)
    (cm km dm cs ks ds : Nat) (hB : 5 ≤ B) (hxW : xWidth < B) :
    Cmd.UsesBelow (frontProgram MQconst xWidth B cm km dm cs ks ds) (B + 9) := by
  -- ⚠ `Var` is an `abbrev` for `Nat` that `omega` does NOT see through; every
  -- register goal `x < k` must be `change (_ : Nat) < _`-retyped before `omega`.
  have he : Cmd.UsesBelow (emitRegs (B + 4) (B + 5) (B + 6) B (List.range xWidth)) (B + 9) := by
    refine emitRegs_usesBelow ?_ ?_ ?_ ?_ ?_
    · change (_ : Nat) < _; omega
    · change (_ : Nat) < _; omega
    · change (_ : Nat) < _; omega
    · change (_ : Nat) < _; omega
    · intro src hsrc; have := List.mem_range.mp hsrc; change (_ : Nat) < _; omega
  have hm1 : Cmd.UsesBelow
      (unaryMonomial cm km dm (B + 4) (B + 7) (B + 8) xWidth (B + 1)) (B + 9) := by
    refine unaryMonomial_usesBelow ?_ ?_ ?_ ?_ ?_ <;> · change (_ : Nat) < _; omega
  have hm2 : Cmd.UsesBelow
      (unaryMonomial cs ks ds (B + 4) (B + 7) (B + 8) xWidth (B + 2)) (B + 9) := by
    refine unaryMonomial_usesBelow ?_ ?_ ?_ ?_ ?_ <;> · change (_ : Nat) < _; omega
  have hec : Cmd.UsesBelow (emitConst (B + 3) MQconst) (B + 9) := by
    refine emitConst_usesBelow ?_; change (_ : Nat) < _; omega
  unfold frontProgram
  refine ⟨he, hm1, hm2, hec, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
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

/-- **The reduction's input layout** (Option A): the honest input part `encX x`
followed by the unary size register `1^(size x)` at index `xWidth`. -/
def encodeInQ (W : InNPWitnessLangFreeSplit Q) (x : X) : State :=
  W.encX x ++ [List.replicate (encodable.size x) 1]

/-- The per-`Q` front machine (a constant). -/
def MmachineQ (W : InNPWitnessLangFreeSplit Q) : flatTM :=
  MQ W.verifier.c W.verifier.regBound W.xWidth

/-- The reg-1 machine constant — `encSyms (flattenTM M_Q)`. -/
def MconstQ (W : InNPWitnessLangFreeSplit Q) : List Nat :=
  encSyms (flattenTM (MmachineQ W))

/-- The scratch base: high enough for both the head layout and the input. -/
def BwidthQ (W : InNPWitnessLangFreeSplit Q) : Nat := max headRegBound (W.xWidth + 1)

/-- The F6 overshoot monomials as functions of `encodable.size x`. -/
def MmaxF (cm km dm : Nat) (x : X) : Nat := cm * (encodable.size x + 1) ^ km + dm
def MstepF (cs ks ds : Nat) (x : X) : Nat := cs * (encodable.size x + 1) ^ ks + ds

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

/-- The size register reads `1^(size x)` at index `xWidth`. -/
theorem encodeInQ_size_reg (W : InNPWitnessLangFreeSplit Q) (x : X) :
    State.get (encodeInQ W x) W.xWidth = List.replicate (encodable.size x) 1 := by
  unfold encodeInQ
  rw [← W.encX_width x]
  exact get_append_last (W.encX x) _

/-- The input encoding is bit-level. -/
theorem encodeInQ_bit (W : InNPWitnessLangFreeSplit Q) (x : X) :
    Compile.BitState (encodeInQ W x) := by
  intro reg hreg y hy
  unfold encodeInQ at hreg
  rw [List.mem_append] at hreg
  rcases hreg with h | h
  · exact encX_bit W x reg h y hy
  · rw [List.mem_singleton] at h; subst h
    have := List.eq_of_mem_replicate hy; omega

/-- The `frontProgram_run` bit hypothesis for the input registers. -/
theorem encodeInQ_bits (W : InNPWitnessLangFreeSplit Q) (x : X) :
    ∀ src ∈ List.range W.xWidth, ∀ y ∈ State.get (encodeInQ W x) src, y ≤ 1 := by
  intro src hsrc y hy
  have hlt : src < W.xWidth := List.mem_range.mp hsrc
  have hsrc' : src < (W.encX x).length := by rw [W.encX_width x]; exact hlt
  have heq : State.get (encodeInQ W x) src = State.get (W.encX x) src := by
    unfold encodeInQ; exact get_append_lt hsrc'
  rw [heq] at hy
  exact encX_bit W x _ (get_mem hsrc') y hy

/-- **`computes`** — the decoded output is `fQ x`. Consumes `frontProgram_run`
(the four output registers), the `encSyms` left inverse, and the register
enumeration `map_range_get`. -/
theorem computesQ (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) (x : X) :
    decodeOutQ W ((cQ W cm km dm cs ks ds).eval (encodeInQ W x))
      = fQ W (fun x => MmaxF cm km dm x) (fun x => MstepF cs ks ds x) x := by
  obtain ⟨_h0, _h1, h2, h3, h4⟩ :=
    FrontProgram.frontProgram_run (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds
      (encodeInQ W x) (encodable.size x) (BwidthQ_ge5 W) (xWidth_lt_BwidthQ W)
      (fun v hv => encSyms_bit _ v hv) (encodeInQ_size_reg W x) (encodeInQ_bits W x)
  -- reg 2's source enumeration recovers `encX x`
  have hmap : (List.range W.xWidth).map (State.get (encodeInQ W x)) = W.encX x := by
    have hcong : (List.range W.xWidth).map (State.get (encodeInQ W x))
        = (List.range W.xWidth).map (State.get (W.encX x)) := by
      apply List.map_congr_left
      intro i hi
      have hlt : i < (W.encX x).length := by rw [W.encX_width x]; exact List.mem_range.mp hi
      unfold encodeInQ; exact get_append_lt hlt
    rw [hcong, ← W.encX_width x, map_range_get]
  unfold decodeOutQ fQ MmaxF MstepF cQ MmachineQ
  rw [h2, h3, h4, hmap, decodeSyms_encSyms, List.length_replicate, List.length_replicate]

/-- **`encodeIn_size`** — the input layout size is `≤ dBound n + n` (the input
part plus the unary size register). -/
theorem encodeInQ_size_le (W : InNPWitnessLangFreeSplit Q) (x : X) :
    State.size (encodeInQ W x) ≤ W.dBound (encodable.size x) + encodable.size x := by
  unfold encodeInQ
  rw [size_append_one, List.length_replicate]
  have := W.encX_size x
  omega

/-- **`width_le`** — the input occupies `xWidth + 1` registers, within the frame. -/
theorem encodeInQ_width (W : InNPWitnessLangFreeSplit Q) (x : X) :
    (encodeInQ W x).length ≤ BwidthQ W + 9 := by
  unfold encodeInQ
  rw [List.length_append, W.encX_width x]
  have := xWidth_lt_BwidthQ W
  simp only [List.length_cons, List.length_nil]
  omega

/-- **`decode_agree`** — padding the input by empty registers past the frame
does not change the decoded output (regs 2/3/4 are inside the frame). -/
theorem decodeOutQ_agree (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat)
    (x : X) (m : Nat) :
    decodeOutQ W ((cQ W cm km dm cs ks ds).eval (encodeInQ W x ++ List.replicate m []))
      = decodeOutQ W ((cQ W cm km dm cs ks ds).eval (encodeInQ W x)) := by
  have hub := frontProgram_usesBelow (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds
    (BwidthQ_ge5 W) (xWidth_lt_BwidthQ W)
  have hagree : AgreeBelow (BwidthQ W + 9) (encodeInQ W x ++ List.replicate m []) (encodeInQ W x) :=
    fun r _ => State.get_append_replicate_nil (encodeInQ W x) m r
  have hR := fun r (hr : r < BwidthQ W + 9) =>
    Cmd.eval_agree (frontProgram (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds)
      (BwidthQ W + 9) hub hagree r hr
  unfold decodeOutQ cQ
  rw [hR 2 (by omega), hR 3 (by omega), hR 4 (by omega)]

/-! ### The cost bound

⚠ **TODO (this session, next commit): the cost accounting is decomposed but not
yet closed.** `costBoundQ`/`cQ_cost_le` (needs the `emitRegs` cost bound —
`emitRegs_cost`, HANDOFF C8-4 — and the monomial-cost `inOPoly`/`monotonic`
proofs) and `fQ_output_size_le` are the two remaining arithmetic obligations.
The whole witness + reduction assembly below is validated modulo these. -/

/-- Placeholder cost bound (see the TODO above). -/
def costBoundQ : Nat → Nat := fun _ => 0

theorem costBoundQ_poly : inOPoly costBoundQ := inOPoly_const 0
theorem costBoundQ_mono : monotonic costBoundQ := fun _ _ _ => Nat.le_refl _

theorem cQ_cost_le (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) (x : X) :
    (cQ W cm km dm cs ks ds).cost (encodeInQ W x) ≤ costBoundQ (encodable.size x) := by
  sorry

theorem fQ_output_size_le (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) (x : X) :
    encodable.size (fQ W (fun x => MmaxF cm km dm x) (fun x => MstepF cs ks ds x) x)
      ≤ costBoundQ (encodable.size x) := by
  sorry

/-! ### The witness `W_Q` and the reduction -/

/-- **The per-`Q` front reduction witness** `W_Q : PolyTimeComputableLang (fQ …)`. -/
noncomputable def WQ (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    PolyTimeComputableLang
      (fQ W (fun x => MmaxF cm km dm x) (fun x => MstepF cs ks ds x)) where
  c := cQ W cm km dm cs ks ds
  encodeIn := encodeInQ W
  decodeOut := decodeOutQ W
  cost_bound := costBoundQ
  cost_bound_poly := costBoundQ_poly
  cost_bound_mono := costBoundQ_mono
  encBound := fun n => W.dBound n + n
  encBound_poly := inOPoly_add W.dBound_poly inOPoly_id
  encBound_mono := fun a b h => Nat.add_le_add (W.dBound_mono a b h) h
  encodeIn_size := encodeInQ_size_le W
  computes := computesQ W cm km dm cs ks ds
  cost_le := cQ_cost_le W cm km dm cs ks ds
  output_size_le := fQ_output_size_le W cm km dm cs ks ds
  enc_bit := encodeInQ_bit W
  regBound := BwidthQ W + 9
  usesBelow := frontProgram_usesBelow (MconstQ W) W.xWidth (BwidthQ W) cm km dm cs ks ds
    (BwidthQ_ge5 W) (xWidth_lt_BwidthQ W)
  width_le := encodeInQ_width W
  decode_agree := decodeOutQ_agree W cm km dm cs ks ds

/-- **C8-4 — the endpoint reduction `Q ⪯p' FlatSingleTMGenNP`.** For any NP
problem `Q` with an honest split free-line verifier witness, the per-`Q` front
construction is an honest TM-backed reduction into the corrected universal
front problem. The F6 monomial constants are extracted from the witness's own
polynomial budgets (`inOPoly_monomial_bound`); correctness is `fQ_correct`. -/
theorem front_reducesPolyMO' (W : InNPWitnessLangFreeSplit Q) :
    Q ⪯p' FlatSingleTMGenNP := by
  obtain ⟨cm, km, dm, hmB⟩ := inOPoly_monomial_bound (maxSizeOf_poly W)
  obtain ⟨cs, ks, ds, hsB⟩ := inOPoly_monomial_bound (stepsOf_poly W)
  refine reducesPolyMO'_of_langFree (WQ W cm km dm cs ks ds) (fun x => ?_)
  refine (fQ_correct W (fun x => MmaxF cm km dm x) (fun x => MstepF cs ks ds x)
    (fun x => ?_) (fun x c hrel hsize => ?_) x).symm
  · -- hmax: certBoundOf + 2 = maxSizeOf ≤ the monomial
    exact hmB (encodable.size x)
  · -- hsteps: MQbudget ≤ stepsOf ≤ the monomial
    exact le_trans (MQbudget_le W x c hsize) (hsB (encodable.size x))

end Complexity.Lang.FrontWitness
