import Complexity.NP.SAT.CookLevin.Reductions.FrontMachine
import Complexity.NP.SAT.CookLevin.Subproblems.SingleTMGenNP
import Complexity.Lang.PolyTime

set_option autoImplicit false

/-! # C8-4 piece 1 — the abstract lifting `FlatSingleTMGenNP (fQ x) ↔ Q x`

This is the **conceptual bridge** of the C8-4 assembly (HANDOFF "NEXT BOTTOM-UP
session — C8-4", piece 1): given an honest split free-line verifier witness
`W : InNPWitnessLangFreeSplit Q` for an arbitrary NP problem `Q`, the per-`Q`
front instance

  `fQ x = (M_Q, s_x, maxSize x, steps x)`,   `M_Q := MQ W.verifier.c W.verifier.regBound W.xWidth`,
                                              `s_x := 3 :: encodeRegs (W.encX x)`

is a yes-instance of the corrected universal front problem `FlatSingleTMGenNP`
**iff** `Q x`. This validates that `FrontMachine`'s two correctness lemmas
(`MQ_accepts_of_accept` / `MQ_no_reject_of_accepts`) exactly match what
`InNPWitnessLangFreeSplit` supplies — the interface-correctness risk the HANDOFF
flags to close FIRST.

The machine plumbing is consumed as a black box from `FrontMachine`; the only
new content here is the predicate-level lift:

* **yes → yes**: `Q x` → (completeness) a bit-cert `c` with `rel x c` → (verifier
  `decides`) `W.verifier.c` accepts the split pair `encX x ++ certState c` →
  (`MQ_accepts_of_accept`) `M_Q` halts on the reassembled tape;
* **yes → yes (backward)**: `M_Q` halts on some `s_x ++ cert` →
  (`MQ_no_reject_of_accepts`) `cert` is a grammar-valid bit register `creg` and
  `W.verifier.c` does not *reject* `encX x ++ [creg]` → (verifier `decides`
  totality) it *accepts* → `rel x (decode creg)` → (soundness) `Q x`.

The size/step registers `maxSize`/`steps` are abstracted as parameters with two
clean domination hypotheses (`hmax`, `hsteps`): the yes→yes direction needs the
budget registers to overshoot the certificate length and the `MQbudget` scan
budget. These are exactly the **F6 monomials** the reduction program materializes
(`unaryMonomial`); discharging them with concrete `inOPoly` bounds is piece 2's
job — see the HANDOFF C8-4 section.
-/

namespace Complexity.Lang.FrontLifting

open Complexity.Lang
open Complexity.Lang.FrontMachine

variable {X : Type} [encodable X] {Q : X → Prop}

/-! ## Certificate register codec

`certState c = [certReg c]` (the canonical one-register certificate layout);
`certReg` maps `List Bool → List Nat` bit-by-bit. -/

/-- The single certificate register holding the cert bits (`true ↦ 1`,
`false ↦ 0`) — the content of `certState c`'s only register. -/
def certReg (c : List Bool) : List Nat := c.map (fun b => if b then 1 else 0)

theorem certState_eq (c : List Bool) : certState c = [certReg c] := rfl

/-- Decode a bit register back to a `List Bool`; inverse of `certReg` on
bit-valued registers. -/
def decodeReg (r : List Nat) : List Bool := r.map (· == 1)

theorem certReg_decodeReg {r : List Nat} (h : ∀ b ∈ r, b ≤ 1) :
    certReg (decodeReg r) = r := by
  unfold certReg decodeReg
  rw [List.map_map]
  conv_rhs => rw [← List.map_id r]
  apply List.map_congr_left
  intro v hv
  have := h v hv
  interval_cases v <;> rfl

/-- A list's length never exceeds its `encodable.size` (each element pays `+1`). -/
theorem list_length_le_size {α : Type} [encodable α] (l : List α) :
    l.length ≤ encodable.size l := by
  induction l with
  | nil => simp [encodable_size_list_nil]
  | cons a t ih =>
      rw [encodable_size_list_cons]
      simp only [List.length_cons]
      omega

/-! ## Witness-derived facts

Basic consequences of the split layout used in both directions. -/

/-- The input part of any split-witness encoding is bit-level. -/
theorem encX_bit (W : InNPWitnessLangFreeSplit Q) (x : X) :
    Compile.BitState (W.encX x) := by
  have h := W.verifier.enc_bit (x, [])
  rw [W.encodeIn_eq x []] at h
  intro reg hreg y hy
  exact h reg (List.mem_append_left _ hreg) y hy

/-- The certificate register sits at index `xWidth`, which is strictly inside
the verifier's register frame. -/
theorem xWidth_succ_le (W : InNPWitnessLangFreeSplit Q) (x : X) :
    W.xWidth + 1 ≤ W.verifier.regBound := by
  have h := W.verifier.width_le (x, [])
  rw [W.encodeIn_eq x [], List.length_append, W.encX_width x, certState_eq] at h
  simpa using h

/-- The classical certificate-size bound extracted from `rel_correct`. -/
noncomputable def certBoundOf (W : InNPWitnessLangFreeSplit Q) : Nat → Nat :=
  (Classical.choice W.rel_correct).bound

/-- Completeness of the certificate relation, at the extracted bound. -/
theorem cert_complete (W : InNPWitnessLangFreeSplit Q) {x : X} (h : Q x) :
    ∃ c : List Bool, W.rel x c ∧ encodable.size c ≤ certBoundOf W (encodable.size x) :=
  (Classical.choice W.rel_correct).complete h

/-- Soundness of the certificate relation. -/
theorem cert_sound (W : InNPWitnessLangFreeSplit Q) {x : X} {c : List Bool}
    (h : W.rel x c) : Q x :=
  (Classical.choice W.rel_correct).sound h

/-! ## The per-`Q` front instance -/

/-- **The per-`Q` front instance.** `maxSize`/`steps` are supplied abstractly;
piece 2 (F6) instantiates them with concrete `inOPoly` monomials that discharge
`hmax`/`hsteps` below. -/
def fQ (W : InNPWitnessLangFreeSplit Q) (maxSize steps : X → Nat) (x : X) :
    flatTM × List Nat × Nat × Nat :=
  (MQ W.verifier.c W.verifier.regBound W.xWidth,
   3 :: Compile.encodeRegs (W.encX x), maxSize x, steps x)

/-! ## The abstract lifting -/

/-- **C8-4 piece 1 — the abstract correctness iff.** With the size/step budget
registers dominating the certificate length (`hmax`) and the front machine's
acceptance budget (`hsteps`), the produced front instance is a yes-instance of
`FlatSingleTMGenNP` exactly when `Q x`. -/
theorem fQ_correct (W : InNPWitnessLangFreeSplit Q) (maxSize steps : X → Nat)
    (hmax : ∀ x, certBoundOf W (encodable.size x) + 2 ≤ maxSize x)
    (hsteps : ∀ x c, W.rel x c → encodable.size c ≤ certBoundOf W (encodable.size x) →
      MQbudget W.verifier.c W.verifier.regBound (W.encX x ++ [certReg c]) ≤ steps x) :
    ∀ x, FlatSingleTMGenNP (fQ W maxSize steps x) ↔ Q x := by
  intro x
  constructor
  · -- backward: yes-instance ⇒ Q x
    rintro ⟨_hvalid, _htapes, _hs, cert, _hcertt, _hcertv, hacc⟩
    have hbitsx := encX_bit W x
    have hlen := W.encX_width x
    have hwk := xWidth_succ_le W x
    obtain ⟨creg, hcregbit, _hcerteq, hne⟩ :=
      MQ_no_reject_of_accepts W.verifier.c W.verifier.regBound W.xWidth (W.encX x) cert
        (steps x) hbitsx hlen hwk W.verifier.usesBelow hacc
    -- decode the register to a Bool cert; the split pair equals `encX x ++ [creg]`
    have hcreg : certReg (decodeReg creg) = creg := certReg_decodeReg hcregbit
    have hpair : W.verifier.encodeIn (x, decodeReg creg) = W.encX x ++ [creg] := by
      rw [W.encodeIn_eq x (decodeReg creg), certState_eq, hcreg]
    have hdec := (W.verifier.decides (x, decodeReg creg)).2
    -- `hne` says the verifier does not reject, i.e. `¬ isReject`
    have hnotrej : ¬ (W.verifier.c.eval (W.verifier.encodeIn (x, decodeReg creg))).isReject := by
      rw [hpair]
      simp only [State.isReject, beq_iff_eq]
      exact hne
    have hrel : W.rel x (decodeReg creg) := by
      by_contra hnrel
      exact hnotrej (hdec.mp hnrel)
    exact cert_sound W hrel
  · -- forward: Q x ⇒ yes-instance
    intro hQx
    obtain ⟨c, hrel, hsize⟩ := cert_complete W hQx
    -- the verifier accepts the split pair
    have hacc0 := (W.verifier.decides (x, c)).1.mp hrel
    rw [W.encodeIn_eq x c, certState_eq] at hacc0
    have haccept : (W.verifier.c.eval (W.encX x ++ [certReg c])).get 0 = [1] := by
      simpa only [State.isAccept, beq_iff_eq] using hacc0
    have hbit : Compile.BitState (W.encX x ++ [certReg c]) := by
      have h := W.verifier.enc_bit (x, c)
      rwa [W.encodeIn_eq x c, certState_eq] at h
    have hwle : (W.encX x ++ [certReg c]).length ≤ W.verifier.regBound := by
      rw [List.length_append, W.encX_width x]; exact xWidth_succ_le W x
    have hmqacc := MQ_accepts_of_accept W.verifier.c W.verifier.regBound W.xWidth
      (W.encX x) (certReg c) hbit (W.encX_width x) hwle W.verifier.usesBelow haccept
      (steps x) (hsteps x c hrel hsize)
    -- assemble the `FlatSingleTMGenNP` yes-instance
    have hsig : (MQ W.verifier.c W.verifier.regBound W.xWidth).sig = 4 :=
      MQ_sig W.verifier.c W.verifier.regBound W.xWidth
    refine ⟨MQ_valid _ _ _, MQ_tapes _ _ _, ?_,
      Compile.shiftReg (certReg c) ++ [0, 3], ?_, ?_, hmqacc⟩
    · -- list_ofFlatType M.sig (3 :: encodeRegs (encX x))
      rw [hsig]
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · show (3 : Nat) < 4; omega
      · exact Compile.encodeRegs_lt_four (W.encX x) (encX_bit W x) y hy
    · -- list_ofFlatType M.sig (shiftReg (certReg c) ++ [0, 3])
      rw [hsig]
      intro y hy
      rw [List.mem_append] at hy
      rcases hy with hy | hy
      · rw [Compile.shiftReg, List.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        rw [certReg, List.mem_map] at hz
        obtain ⟨b, _, rfl⟩ := hz
        unfold ofFlatType
        cases b <;> decide
      · rcases List.mem_cons.mp hy with rfl | hy
        · show (0 : Nat) < 4; omega
        · rw [List.mem_singleton] at hy; subst hy; show (3 : Nat) < 4; omega
    · -- isValidCert maxSize cert : cert.length ≤ maxSize x
      show (Compile.shiftReg (certReg c) ++ [0, 3]).length ≤ maxSize x
      rw [List.length_append, Compile.shiftReg, List.length_map, certReg, List.length_map]
      have h1 : c.length ≤ encodable.size c := list_length_le_size c
      have h2 := hmax x
      simp only [List.length_cons, List.length_nil]
      omega

/-! ## F6 — concrete `inOPoly` size/step budgets discharging `hmax`/`hsteps`

The two abstract hypotheses of `fQ_correct` are discharged with concrete budget
functions built from the witness's own polynomial bounds (`certBoundOf`,
`W.dBound`), extracted classically once per `Q`. This proves the F6 monomials
*exist* and are polynomial — the risk the HANDOFF flags for the reduction
program (piece 2) to materialize in unary via `unaryMonomial`. -/

/-- An `inOPoly` upper bound for `encodable.size (x, c)` over size-bounded certs. -/
noncomputable def argBound (W : InNPWitnessLangFreeSplit Q) (n : Nat) : Nat :=
  n + certBoundOf W n + 1

/-- The verifier's cost/size budget at `argBound` — dominates both
`State.size s` and `verifier.c.cost s` for the split pair `s = encX x ++ [certReg c]`. -/
noncomputable def dCap (W : InNPWitnessLangFreeSplit Q) (n : Nat) : Nat :=
  W.dBound (argBound W n)

/-- The `State.size` / cost / register-count bounds for the split pair,
uniformly in size-bounded certs — the raw material for `MQbudget_le`. -/
theorem front_state_bounds (W : InNPWitnessLangFreeSplit Q) (x : X) (c : List Bool)
    (hsize : encodable.size c ≤ certBoundOf W (encodable.size x)) :
    State.size (W.encX x ++ [certReg c]) ≤ dCap W (encodable.size x) ∧
    W.verifier.c.cost (W.encX x ++ [certReg c]) ≤ dCap W (encodable.size x) ∧
    (W.encX x ++ [certReg c]).length ≤ W.verifier.regBound := by
  have hpair : W.verifier.encodeIn (x, c) = W.encX x ++ [certReg c] := by
    rw [W.encodeIn_eq x c, certState_eq]
  have hprod : encodable.size ((x, c) : X × List Bool) ≤ argBound W (encodable.size x) := by
    show encodable.size x + encodable.size c + 1 ≤ argBound W (encodable.size x)
    unfold argBound; omega
  have hdmono : W.dBound (encodable.size ((x, c) : X × List Bool)) ≤ dCap W (encodable.size x) :=
    W.dBound_mono _ _ hprod
  refine ⟨?_, ?_, ?_⟩
  · have h := W.verifier.encodeIn_size (x, c); rw [hpair] at h; exact le_trans h hdmono
  · have h := W.verifier.cost_bound (x, c); rw [hpair] at h; exact le_trans h hdmono
  · have h := W.verifier.width_le (x, c); rw [hpair] at h; exact h

/-- **The concrete step budget** — a polynomial in `encodable.size x` that
dominates `MQbudget` for every size-bounded cert (`MQbudget_le`). The compiler
register frame `regBound + 2·loopDepth + 2` is inlined so the `omega` assembly
matches `MQbudget`'s unfolding syntactically. -/
noncomputable def stepsOf (W : InNPWitnessLangFreeSplit Q) (n : Nat) : Nat :=
  (2 * (dCap W n + W.verifier.regBound + 2) + 1) + 1 +
    ((W.verifier.regBound + 2 * W.verifier.c.loopDepth + 2)
        * (2 * dCap W n + 2 * W.verifier.regBound
            + 2 * (W.verifier.regBound + 2 * W.verifier.c.loopDepth + 2) + 12) + 1 +
      (Compile.physStepBudget
        (dCap W n + (W.verifier.regBound + (W.verifier.regBound + 2 * W.verifier.c.loopDepth + 2))
          + dCap W n + 2) (dCap W n) + 3))

/-- **`MQbudget` is dominated by `stepsOf`** on size-bounded certs. -/
theorem MQbudget_le (W : InNPWitnessLangFreeSplit Q) (x : X) (c : List Bool)
    (hsize : encodable.size c ≤ certBoundOf W (encodable.size x)) :
    MQbudget W.verifier.c W.verifier.regBound (W.encX x ++ [certReg c])
      ≤ stepsOf W (encodable.size x) := by
  obtain ⟨hSize, hCost, hLen⟩ := front_state_bounds W x c hsize
  set s := W.encX x ++ [certReg c] with hs
  set n := encodable.size x with hn
  set RB := W.verifier.regBound + 2 * W.verifier.c.loopDepth + 2 with hRB
  have hTape : (Compile.encodeTape s).length ≤ dCap W n + W.verifier.regBound + 2 := by
    rw [Compile.encodeTape_length]; omega
  have hPad : Compile.padBudget RB s
      ≤ RB * (2 * dCap W n + 2 * W.verifier.regBound + 2 * RB + 12) := by
    refine le_trans (Compile.padBudget_le RB s) ?_
    apply Nat.mul_le_mul_left
    omega
  have hPhys : Compile.physStepBudget
        (State.size s + (s.length + RB) + W.verifier.c.cost s + 2) (W.verifier.c.cost s)
      ≤ Compile.physStepBudget
        (dCap W n + (W.verifier.regBound + RB) + dCap W n + 2) (dCap W n) := by
    apply Compile.physStepBudget_mono
    · omega
    · exact hCost
  unfold MQbudget stepsOf
  set TL := (Compile.encodeTape s).length
  set PB := Compile.padBudget RB s
  set PB' := RB * (2 * dCap W n + 2 * W.verifier.regBound + 2 * RB + 12)
  set PS := Compile.physStepBudget
      (State.size s + (s.length + RB) + W.verifier.c.cost s + 2) (W.verifier.c.cost s)
  set PS' := Compile.physStepBudget
      (dCap W n + (W.verifier.regBound + RB) + dCap W n + 2) (dCap W n)
  omega

/-- The concrete certificate-size budget. -/
noncomputable def maxSizeOf (W : InNPWitnessLangFreeSplit Q) (n : Nat) : Nat :=
  certBoundOf W n + 2

/-! ### The concrete budgets are `inOPoly`

This proves the F6 monomials *exist* as polynomials — the standing risk that a
poly-time front witness can materialize the size/step registers. -/

theorem certBoundOf_poly (W : InNPWitnessLangFreeSplit Q) : inOPoly (certBoundOf W) :=
  (Classical.choice W.rel_correct).bound_poly

theorem argBound_poly (W : InNPWitnessLangFreeSplit Q) : inOPoly (argBound W) := by
  unfold argBound
  exact inOPoly_add (inOPoly_add inOPoly_id (certBoundOf_poly W)) (inOPoly_const 1)

theorem dCap_poly (W : InNPWitnessLangFreeSplit Q) : inOPoly (dCap W) := by
  unfold dCap
  exact inOPoly_comp (argBound_poly W) W.dBound_poly

theorem maxSizeOf_poly (W : InNPWitnessLangFreeSplit Q) : inOPoly (maxSizeOf W) := by
  unfold maxSizeOf
  exact inOPoly_add (certBoundOf_poly W) (inOPoly_const 2)

/-- Helper: a constant-linear combination of `dCap` is `inOPoly`. -/
private theorem lin_dCap_poly (W : InNPWitnessLangFreeSplit Q) (a b : Nat) :
    inOPoly (fun n => a * dCap W n + b) :=
  inOPoly_add (inOPoly_mul (inOPoly_const a) (dCap_poly W)) (inOPoly_const b)

theorem stepsOf_poly (W : InNPWitnessLangFreeSplit Q) : inOPoly (stepsOf W) := by
  unfold stepsOf
  set R := W.verifier.regBound with hR
  set RB := R + 2 * W.verifier.c.loopDepth + 2 with hRB
  -- the `physStepBudget` summand, dominated by its diagonal
  have hphys : inOPoly (fun n => Compile.physStepBudget
      (dCap W n + (R + RB) + dCap W n + 2) (dCap W n) + 3) := by
    refine inOPoly_of_le
      (g := fun n => Compile.physStepBudget (3 * dCap W n + (R + RB + 2))
        (3 * dCap W n + (R + RB + 2)) + 3) ?_ ?_
    · intro n
      have hmono := Compile.physStepBudget_mono
        (G := dCap W n + (R + RB) + dCap W n + 2) (G' := 3 * dCap W n + (R + RB + 2))
        (cost := dCap W n) (cost' := 3 * dCap W n + (R + RB + 2))
        (by omega) (by omega)
      show Compile.physStepBudget (dCap W n + (R + RB) + dCap W n + 2) (dCap W n) + 3
        ≤ Compile.physStepBudget (3 * dCap W n + (R + RB + 2)) (3 * dCap W n + (R + RB + 2)) + 3
      omega
    · have hPS : inOPoly (fun n => Compile.physStepBudget
          (3 * dCap W n + (R + RB + 2)) (3 * dCap W n + (R + RB + 2))) :=
        inOPoly_comp (f := fun n => 3 * dCap W n + (R + RB + 2))
          (g := fun m => Compile.physStepBudget m m)
          (lin_dCap_poly W 3 (R + RB + 2)) Compile.physStepBudget_poly
      have hsum := inOPoly_add hPS (inOPoly_const 3)
      exact hsum
  have hf : inOPoly (fun n => 2 * (dCap W n + R + 2) + 1 + 1) := by
    have e : (fun n => 2 * (dCap W n + R + 2) + 1 + 1)
        = (fun n => 2 * dCap W n + (2 * R + 6)) := by funext n; ring
    rw [e]; exact lin_dCap_poly W 2 (2 * R + 6)
  have hf' : inOPoly (fun n => RB * (2 * dCap W n + 2 * R + 2 * RB + 12) + 1) := by
    have e : (fun n => RB * (2 * dCap W n + 2 * R + 2 * RB + 12) + 1)
        = (fun n => (RB * 2) * dCap W n + (RB * (2 * R + 2 * RB + 12) + 1)) := by
      funext n; ring
    rw [e]; exact lin_dCap_poly W (RB * 2) (RB * (2 * R + 2 * RB + 12) + 1)
  exact inOPoly_add hf (inOPoly_add hf' hphys)

/-- **C8-4 piece 1 (concrete).** The abstract lifting with the two budget
hypotheses discharged by the concrete `maxSizeOf`/`stepsOf` polynomials — a
hypothesis-free correctness iff for the fully-determined front instance. -/
theorem fQ_correct_concrete (W : InNPWitnessLangFreeSplit Q) :
    ∀ x, FlatSingleTMGenNP
        (fQ W (fun x => maxSizeOf W (encodable.size x))
              (fun x => stepsOf W (encodable.size x)) x) ↔ Q x :=
  fQ_correct W _ _
    (fun _ => Nat.le_refl _)
    (fun x c _hrel hsize => MQbudget_le W x c hsize)

end Complexity.Lang.FrontLifting
