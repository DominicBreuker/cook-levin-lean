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

end Complexity.Lang.FrontLifting
