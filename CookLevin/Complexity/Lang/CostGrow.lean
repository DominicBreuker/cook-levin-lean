import Complexity.Lang.CostFlat
import Mathlib.Tactic

set_option autoImplicit false

/-! # `Cmd.CapCost` — a two-cap polynomial cost bound that survives a loop

The obvious cost predicate — a single cap `M` over `c.costReads`, concluding
`cost ≤ K·(M+1)^(D+1)` — **cannot survive a loop**: after one iteration the
body's outputs are bounded by `poly(M)`, so the next iteration's cap is
`poly(poly(M))`, and `m` iterations give a tower (FINDING Z). It was built
(`Lang/CostPoly.lean`, `Cmd.PolyCost`) and deleted 2026-07-30-b; do not rebuild
it.

This file uses **two** caps instead:

* `MF` bounds a set `F` of registers **frozen for the whole loop**;
* `N` bounds *every* register.

and states three conclusions:

```
c.cost s              ≤ K·(MF+1)^D · (N+1)        -- cost MAY be linear in N
∀ r, |c.eval s @ r|   ≤ N + K·(MF+1)^D            -- growth may NOT depend on N
∀ r ∈ F', |c.eval s @ r| ≤ MF + K·(MF+1)^D        -- and F' stays capped
```

The loop rule is then non-compounding: with `bnd ∈ F` the trip count is `≤ MF`,
each iteration adds `≤ P := K·(MF+1)^D` to the global cap, so `N_m ≤ N + MF·P`.

## Register sets are `Nat` BITMASKS, and that is not cosmetic

`r ∈ F` is `F.testBit r`. Every register of every program we analyse is `< 64`,
`Nat.land`/`lor`/`xor`/`testBit` are GMP-accelerated **in the kernel**, and the
sets the analysis threads are tiny. The previous `List Var` representation made
the checker quadratic in the program *size*: `Cmd.writes` of `S1Prelude.cPrelude`
is a **327411-element list**, and the frozen-set computation ran `List.contains`
on it once per candidate register per enclosing loop. That is why `cPrelude`
could not be checked at all. Do not put the lists back.

## ONE pass, not two

`Cmd.chk C c = (verdict, B)` is a single forward traversal returning

* `verdict = some C'` — a `Cmd.CapCost c C C'` certificate, or `none`;
* `B` — the registers whose growth across `c` is **not** certified additive.
  This half is **total**: it is sound even when the verdict is `none`, which is
  exactly what lets a loop promote a register before its own body is known
  analysable (`Cmd.chk`'s `forBnd` rule uses the failed run's `B`).

`B` is what the old `Cmd.GrowOk` computed, but *flow-sensitively* (it threads the
capped set) and for **all** registers at once (`GrowOk` re-walked the body once
per candidate register). Flow-sensitivity is what closes
`Cmd.op (.concat SSEEN SAX SSEEN)`: `SAX` is built by the straight-line prefix of
the very body that then appends it, so no flow-insensitive check can see that it
is capped.

## Layout

1. bitmask helpers.
2. `Cmd.NoGrow` — an *idempotent* `≤ max |r| 1`, so a `NoGrow` body may be
   iterated any number of times — and `Cmd.ngm`, its mask.
3. `Cmd.CapCost` and its `op` / `seq` / `ifBit` / `forBnd` algebra.
4. `Cmd.chk`, the decidable pass, and `Cmd.chk_sound`.
5. `Cmd.costLeSize_of_chk` — the one-liner a free witness's `cost_le` needs.
-/

namespace Complexity.Lang

/-! ## Part 0 — register sets as bitmasks -/

/-- The singleton mask `{v}`. -/
@[inline] def bitOf (v : Var) : Nat := 2 ^ v

/-- `a \ b`, written with kernel-accelerated ops only. **Do not use
`Nat.ldiff`**: it goes through `Nat.bitwise`, which the kernel cannot reduce, so
`decide` gets stuck on it. -/
@[inline] def mdiff (a b : Nat) : Nat := a ^^^ (a &&& b)

@[simp] theorem testBit_bitOf (v r : Var) : (bitOf v).testBit r = decide (v = r) := by
  simp [bitOf, Nat.testBit_two_pow]

@[simp] theorem testBit_mdiff (a b : Nat) (r : Var) :
    (mdiff a b).testBit r = (a.testBit r && !b.testBit r) := by
  simp only [mdiff, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit r <;> cases b.testBit r <;> rfl

/-- A mask is a *subset* of another. -/
def MaskSub (a b : Nat) : Prop := ∀ r : Var, a.testBit r = true → b.testBit r = true

/-! ## Part 1 — `NoGrow` and its mask

`c.NoGrow r` certifies `|c.eval s @ r| ≤ max |s@r| 1`. The bound is idempotent,
which is the whole point: it survives iteration without a trip-count hypothesis,
so a register a loop body never inflates stays capped for the whole loop *no
matter how many times it runs*. That is what freezes the drained cursor
`forBnd idx SCAN (… tail SCAN SCAN …)`, whose own bound register is the one
being consumed — and, because the frozen set a loop hands its body is built from
`NoGrow`, it is also what seeds the flow-sensitive pass with a usable cap. -/

def Op.NoGrow (o : Op) (r : Var) : Bool :=
  match o with
  | .clear _ => true
  | .appendOne dst => dst != r
  | .appendZero dst => dst != r
  | .head _ _ => true
  | .eqBit _ _ _ => true
  | .nonEmpty _ _ => true
  | .copy dst src => dst != r || src == r
  | .tail dst src => dst != r || src == r
  | .concat dst _ _ => dst != r

def Cmd.NoGrow : Cmd → Var → Bool
  | .op o, r => o.NoGrow r
  | .seq a b, r => a.NoGrow r && b.NoGrow r
  | .ifBit _ a b, r => a.NoGrow r && b.NoGrow r
  | .forBnd cnt _ body, r => cnt != r && body.NoGrow r

theorem Op.noGrow_sound (o : Op) (r : Var) (h : o.NoGrow r = true) (s : State) :
    (State.get (Op.eval o s) r).length ≤ max (State.get s r).length 1 := by
  cases o with
  | clear dst =>
      by_cases hr : r = dst
      · subst hr; simp [Op.eval, State.get_set_eq]
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | appendOne dst =>
      have hne : dst ≠ r := by
        simpa [Op.NoGrow, bne_iff_ne] using h
      simp only [Op.eval, State.get_set_ne _ _ _ _ (Ne.symm hne)]; omega
  | appendZero dst =>
      have hne : dst ≠ r := by
        simpa [Op.NoGrow, bne_iff_ne] using h
      simp only [Op.eval, State.get_set_ne _ _ _ _ (Ne.symm hne)]; omega
  | head dst src =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq]
        rcases State.get s src with _ | ⟨x, xs⟩ <;> simp
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | eqBit dst s1 s2 =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq]
        by_cases hh : State.get s s1 = State.get s s2 <;> simp [hh]
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | nonEmpty dst src =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq]
        by_cases hh : (State.get s src).isEmpty <;> simp [hh]
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | copy dst src =>
      by_cases hr : r = dst
      · subst hr
        have hs : src = r := by
          simp only [Op.NoGrow, bne_self_eq_false, Bool.false_or, beq_iff_eq] at h
          exact h
        subst hs; simp [Op.eval, State.get_set_eq]
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | tail dst src =>
      by_cases hr : r = dst
      · subst hr
        have hs : src = r := by
          simp only [Op.NoGrow, bne_self_eq_false, Bool.false_or, beq_iff_eq] at h
          exact h
        subst hs; simp only [Op.eval, State.get_set_eq, List.length_tail]; omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | concat dst a b =>
      have hne : dst ≠ r := by
        simpa [Op.NoGrow, bne_iff_ne] using h
      simp only [Op.eval, State.get_set_ne _ _ _ _ (Ne.symm hne)]; omega

/-- **`NoGrow` is sound, and its bound is idempotent.** -/
theorem Cmd.noGrow_sound : ∀ (c : Cmd) (r : Var), c.NoGrow r = true → ∀ s : State,
    (State.get (c.eval s) r).length ≤ max (State.get s r).length 1 := by
  intro c
  induction c with
  | op o => intro r h s; rw [Cmd.eval_op]; exact Op.noGrow_sound o r h s
  | seq c1 c2 ih1 ih2 =>
      intro r h s
      simp only [Cmd.NoGrow, Bool.and_eq_true] at h
      rw [Cmd.eval_seq]
      have h2 := ih2 r h.2 (c1.eval s)
      have h1 := ih1 r h.1 s
      omega
  | ifBit t cT cE ihT ihE =>
      intro r h s
      simp only [Cmd.NoGrow, Bool.and_eq_true] at h
      by_cases hb : State.get s t = [1]
      · rw [Cmd.eval_ifBit_true _ _ _ _ hb]; exact ihT r h.1 s
      · rw [Cmd.eval_ifBit_false _ _ _ _ hb]; exact ihE r h.2 s
  | forBnd cnt bnd body ih =>
      intro r h s
      simp only [Cmd.NoGrow, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      obtain ⟨hcnt, hbody⟩ := h
      rw [Cmd.eval_forBnd]
      refine Cmd.foldlState_range_induct body cnt (State.get s bnd).length s
        (fun _ st => (State.get st r).length ≤ max (State.get s r).length 1)
        (Nat.le_max_left _ _) (fun i st _ hM => ?_)
      show (State.get (body.eval (st.set cnt (List.replicate i 1))) r).length ≤ _
      have hset : State.get (st.set cnt (List.replicate i 1)) r = State.get st r :=
        State.get_set_ne _ _ _ _ (Ne.symm hcnt)
      have := ih r hbody (st.set cnt (List.replicate i 1))
      rw [hset] at this
      omega

/-- The mask of the registers a command may **inflate** — the complement of
`NoGrow`, computed for every register in one traversal. -/
def Op.ngm : Op → Nat
  | .clear _ => 0
  | .appendOne d => bitOf d
  | .appendZero d => bitOf d
  | .head _ _ => 0
  | .eqBit _ _ _ => 0
  | .nonEmpty _ _ => 0
  | .copy d s => if s = d then 0 else bitOf d
  | .tail d s => if s = d then 0 else bitOf d
  | .concat d _ _ => bitOf d

def Cmd.ngm : Cmd → Nat
  | .op o => Op.ngm o
  | .seq a b => a.ngm ||| b.ngm
  | .ifBit _ a b => a.ngm ||| b.ngm
  | .forBnd cnt _ body => bitOf cnt ||| body.ngm

theorem Op.noGrow_of_ngm (o : Op) (r : Var) (h : o.ngm.testBit r = false) :
    o.NoGrow r = true := by
  cases o with
  | clear _ => rfl
  | head _ _ => rfl
  | eqBit _ _ _ => rfl
  | nonEmpty _ _ => rfl
  | appendOne d =>
      simp only [Op.ngm, testBit_bitOf, decide_eq_false_iff_not] at h
      simpa [Op.NoGrow, bne_iff_ne] using h
  | appendZero d =>
      simp only [Op.ngm, testBit_bitOf, decide_eq_false_iff_not] at h
      simpa [Op.NoGrow, bne_iff_ne] using h
  | concat d a b =>
      simp only [Op.ngm, testBit_bitOf, decide_eq_false_iff_not] at h
      simpa [Op.NoGrow, bne_iff_ne] using h
  | copy d s =>
      simp only [Op.NoGrow, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq]
      by_cases hsd : s = d
      · by_cases hdr : d = r
        · right; rw [hsd, hdr]
        · left; exact hdr
      · simp only [Op.ngm, if_neg hsd, testBit_bitOf, decide_eq_false_iff_not] at h
        left; exact h
  | tail d s =>
      simp only [Op.NoGrow, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq]
      by_cases hsd : s = d
      · by_cases hdr : d = r
        · right; rw [hsd, hdr]
        · left; exact hdr
      · simp only [Op.ngm, if_neg hsd, testBit_bitOf, decide_eq_false_iff_not] at h
        left; exact h

theorem Cmd.noGrow_of_ngm : ∀ (c : Cmd) (r : Var), c.ngm.testBit r = false →
    c.NoGrow r = true := by
  intro c
  induction c with
  | op o => intro r h; exact Op.noGrow_of_ngm o r h
  | seq a b iha ihb =>
      intro r h
      simp only [Cmd.ngm, Nat.testBit_or, Bool.or_eq_false_iff] at h
      simp [Cmd.NoGrow, iha r h.1, ihb r h.2]
  | ifBit t a b iha ihb =>
      intro r h
      simp only [Cmd.ngm, Nat.testBit_or, Bool.or_eq_false_iff] at h
      simp [Cmd.NoGrow, iha r h.1, ihb r h.2]
  | forBnd cnt bnd body ih =>
      intro r h
      simp only [Cmd.ngm, Nat.testBit_or, Bool.or_eq_false_iff, testBit_bitOf,
        decide_eq_false_iff_not] at h
      simp [Cmd.NoGrow, bne_iff_ne, h.1, ih r h.2]

/-! ## Part 2 — `CapCost`, the two-cap predicate -/

/-- **The two-cap polynomial cost bound.** `F` is capped by `MF`, everything by
`N`. The cost may be linear in `N` (that is what pays for `copy r r` on a large
output register — FINDING X); the *growth* may not, which is what keeps a loop
from compounding. `F'` is the set still capped after the command. -/
def Cmd.CapCost (c : Cmd) (F F' : Nat) : Prop :=
  ∃ K D : Nat, ∀ (s : State) (MF N : Nat),
    (∀ r : Var, F.testBit r = true → (State.get s r).length ≤ MF) →
    (∀ r : Var, (State.get s r).length ≤ N) →
      c.cost s ≤ K * (MF + 1) ^ D * (N + 1)
    ∧ (∀ r : Var, (State.get (c.eval s) r).length ≤ N + K * (MF + 1) ^ D)
    ∧ (∀ r : Var, F'.testBit r = true →
        (State.get (c.eval s) r).length ≤ MF + K * (MF + 1) ^ D)

/-! ### Budget algebra

Every rule below is an exercise in `K·(MF+1)^D` bookkeeping; these facts do all
of it. -/

private theorem pb_mono {K1 K2 D1 D2 MF : Nat} (hK : K1 ≤ K2) (hD : D1 ≤ D2) :
    K1 * (MF + 1) ^ D1 ≤ K2 * (MF + 1) ^ D2 :=
  Nat.mul_le_mul hK (Nat.pow_le_pow_right (by omega) hD)

private theorem pb_one (D MF : Nat) : 1 ≤ (MF + 1) ^ D := Nat.one_le_pow _ _ (by omega)

/-- `MF + K·(MF+1)^D + 1 ≤ (K+1)·(MF+1)^(D+1)` — the step that turns "a cap plus
a budget" back into a budget one degree higher. -/
private theorem pb_shift (K D MF : Nat) :
    MF + K * (MF + 1) ^ D + 1 ≤ (K + 1) * (MF + 1) ^ (D + 1) := by
  have h1 : (MF + 1) ≤ (MF + 1) * (MF + 1) ^ D := by
    have := pb_one D MF; nlinarith
  have h2 : (K + 1) * (MF + 1) ^ (D + 1) = K * ((MF + 1) * (MF + 1) ^ D)
      + (MF + 1) * (MF + 1) ^ D := by ring
  have h3 : K * (MF + 1) ^ D ≤ K * ((MF + 1) * (MF + 1) ^ D) :=
    Nat.mul_le_mul_left _ (by nlinarith [pb_one D MF])
  omega

/-- Re-basing a budget stated at the cap `MF + 1` onto the cap `MF`. The frozen
set a loop hands its body is `NoGrow`-widened, so its cap is `MF + 1`; this is
what converts the body's constants back. -/
private theorem pb_succ (K D MF : Nat) :
    K * (MF + 1 + 1) ^ D ≤ (K * 2 ^ D) * (MF + 1) ^ D := by
  have h : (MF + 1 + 1) ^ D ≤ (2 * (MF + 1)) ^ D := Nat.pow_le_pow_left (by omega) _
  calc K * (MF + 1 + 1) ^ D ≤ K * (2 * (MF + 1)) ^ D := Nat.mul_le_mul_left _ h
    _ = (K * 2 ^ D) * (MF + 1) ^ D := by rw [mul_pow]; ring

/-- The whole `seq` budget algebra in one place. -/
private theorem seq_budget (K1 D1 K2 D2 MF : Nat) :
    1 + K1 * (MF + 1) ^ D1
      + K2 * (MF + K1 * (MF + 1) ^ D1 + 1) ^ D2 * (K1 * (MF + 1) ^ D1 + 1)
    ≤ (1 + K1 + K2 * (K1 + 1) ^ (D2 + 1)) * (MF + 1) ^ (D1 + (D1 + 1) * D2) := by
  have hone1 : (1 : Nat) ≤ (MF + 1) ^ D1 := pb_one D1 MF
  have h1 : MF + K1 * (MF + 1) ^ D1 + 1 ≤ (K1 + 1) * (MF + 1) ^ (D1 + 1) :=
    pb_shift K1 D1 MF
  have h2 : (MF + K1 * (MF + 1) ^ D1 + 1) ^ D2
      ≤ (K1 + 1) ^ D2 * (MF + 1) ^ ((D1 + 1) * D2) := by
    calc (MF + K1 * (MF + 1) ^ D1 + 1) ^ D2
        ≤ ((K1 + 1) * (MF + 1) ^ (D1 + 1)) ^ D2 := Nat.pow_le_pow_left h1 _
      _ = (K1 + 1) ^ D2 * ((MF + 1) ^ (D1 + 1)) ^ D2 := by rw [mul_pow]
      _ = (K1 + 1) ^ D2 * (MF + 1) ^ ((D1 + 1) * D2) := by rw [← pow_mul]
  have h3 : K1 * (MF + 1) ^ D1 + 1 ≤ (K1 + 1) * (MF + 1) ^ D1 := by nlinarith
  have hDe : (D1 + 1) * D2 + D1 = D1 + (D1 + 1) * D2 := by omega
  have h4 : K2 * (MF + K1 * (MF + 1) ^ D1 + 1) ^ D2 * (K1 * (MF + 1) ^ D1 + 1)
      ≤ K2 * (K1 + 1) ^ (D2 + 1) * (MF + 1) ^ (D1 + (D1 + 1) * D2) := by
    calc K2 * (MF + K1 * (MF + 1) ^ D1 + 1) ^ D2 * (K1 * (MF + 1) ^ D1 + 1)
        ≤ K2 * ((K1 + 1) ^ D2 * (MF + 1) ^ ((D1 + 1) * D2))
            * ((K1 + 1) * (MF + 1) ^ D1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h3
      _ = K2 * (K1 + 1) ^ (D2 + 1)
            * ((MF + 1) ^ ((D1 + 1) * D2) * (MF + 1) ^ D1) := by ring
      _ = K2 * (K1 + 1) ^ (D2 + 1) * (MF + 1) ^ ((D1 + 1) * D2 + D1) := by rw [← pow_add]
      _ = K2 * (K1 + 1) ^ (D2 + 1) * (MF + 1) ^ (D1 + (D1 + 1) * D2) := by rw [hDe]
  have h5 : K1 * (MF + 1) ^ D1 ≤ K1 * (MF + 1) ^ (D1 + (D1 + 1) * D2) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have h6 : (1 : Nat) ≤ (MF + 1) ^ (D1 + (D1 + 1) * D2) := pb_one _ MF
  have h7 : (1 + K1 + K2 * (K1 + 1) ^ (D2 + 1)) * (MF + 1) ^ (D1 + (D1 + 1) * D2)
      = (MF + 1) ^ (D1 + (D1 + 1) * D2) + K1 * (MF + 1) ^ (D1 + (D1 + 1) * D2)
        + K2 * (K1 + 1) ^ (D2 + 1) * (MF + 1) ^ (D1 + (D1 + 1) * D2) := by ring
  omega

theorem Cmd.CapCost.seq {c1 c2 : Cmd} {F F1 F2 : Nat}
    (h1 : c1.CapCost F F1) (h2 : c2.CapCost F1 F2) : (c1 ;; c2).CapCost F F2 := by
  obtain ⟨K1, D1, hb1⟩ := h1
  obtain ⟨K2, D2, hb2⟩ := h2
  refine ⟨1 + K1 + K2 * (K1 + 1) ^ (D2 + 1), D1 + (D1 + 1) * D2, fun s MF N hF hN => ?_⟩
  obtain ⟨hc1, hg1, hf1⟩ := hb1 s MF N hF hN
  obtain ⟨hc2, hg2, hf2⟩ := hb2 (c1.eval s) (MF + K1 * (MF + 1) ^ D1)
    (N + K1 * (MF + 1) ^ D1) hf1 hg1
  set B1 := K1 * (MF + 1) ^ D1 with hB1
  set B2 := K2 * (MF + B1 + 1) ^ D2 with hB2
  set Btot := 1 + B1 + B2 * (B1 + 1) with hBtot
  have hbudget : Btot ≤ (1 + K1 + K2 * (K1 + 1) ^ (D2 + 1))
      * (MF + 1) ^ (D1 + (D1 + 1) * D2) := by
    rw [hBtot, hB2, hB1]; exact seq_budget K1 D1 K2 D2 MF
  have hsplit : B1 + B2 ≤ Btot := by
    have : B2 ≤ B2 * (B1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  refine ⟨?_, fun r => ?_, fun r hr => ?_⟩
  · rw [Cmd.cost_seq]
    have hwide : N + B1 + 1 ≤ (N + 1) * (B1 + 1) := by nlinarith
    have hc2' : c2.cost (c1.eval s) ≤ B2 * ((N + 1) * (B1 + 1)) :=
      le_trans hc2 (Nat.mul_le_mul_left _ hwide)
    have hstep : 1 + c1.cost s + c2.cost (c1.eval s) ≤ (N + 1) * Btot := by
      have e : (N + 1) * Btot = (N + 1) + B1 * (N + 1) + B2 * ((N + 1) * (B1 + 1)) := by
        rw [hBtot]; ring
      omega
    refine le_trans hstep ?_
    rw [Nat.mul_comm (N + 1) Btot]
    exact Nat.mul_le_mul_right _ hbudget
  · rw [Cmd.eval_seq]
    have := hg2 r
    omega
  · rw [Cmd.eval_seq]
    have := hf2 r hr
    omega

theorem Cmd.CapCost.ifBit {t : Var} {cT cE : Cmd} {F F1 F2 F' : Nat}
    (hT : cT.CapCost F F1) (hE : cE.CapCost F F2)
    (hsub : ∀ r : Var, F'.testBit r = true → F1.testBit r = true ∧ F2.testBit r = true) :
    (Cmd.ifBit t cT cE).CapCost F F' := by
  obtain ⟨KT, DT, hbT⟩ := hT
  obtain ⟨KE, DE, hbE⟩ := hE
  refine ⟨1 + KT + KE, max DT DE, fun s MF N hF hN => ?_⟩
  set D := max DT DE with hD
  have hmT : KT * (MF + 1) ^ DT ≤ KT * (MF + 1) ^ D :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hmE : KE * (MF + 1) ^ DE ≤ KE * (MF + 1) ^ D :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hone : 1 ≤ (MF + 1) ^ D := pb_one D MF
  have hmul : ∀ a b : Nat, a ≤ b → a * (N + 1) ≤ b * (N + 1) :=
    fun a b h => Nat.mul_le_mul_right _ h
  have hexp : (1 + KT + KE) * (MF + 1) ^ D
      = (MF + 1) ^ D + KT * (MF + 1) ^ D + KE * (MF + 1) ^ D := by ring
  by_cases hb : State.get s t = [1]
  · obtain ⟨hc, hg, hf⟩ := hbT s MF N hF hN
    refine ⟨?_, fun r => ?_, fun r hr => ?_⟩
    · rw [Cmd.cost_ifBit_true _ _ _ _ hb]
      have h1 : KT * (MF + 1) ^ DT * (N + 1) ≤ KT * (MF + 1) ^ D * (N + 1) := hmul _ _ hmT
      have h2 : (1 : Nat) ≤ (MF + 1) ^ D * (N + 1) :=
        Nat.one_le_iff_ne_zero.2 (by positivity)
      have e : (1 + KT + KE) * (MF + 1) ^ D * (N + 1)
          = (MF + 1) ^ D * (N + 1) + KT * (MF + 1) ^ D * (N + 1)
            + KE * (MF + 1) ^ D * (N + 1) := by ring
      omega
    · rw [Cmd.eval_ifBit_true _ _ _ _ hb]; have := hg r; omega
    · rw [Cmd.eval_ifBit_true _ _ _ _ hb]; have := hf r (hsub r hr).1; omega
  · obtain ⟨hc, hg, hf⟩ := hbE s MF N hF hN
    refine ⟨?_, fun r => ?_, fun r hr => ?_⟩
    · rw [Cmd.cost_ifBit_false _ _ _ _ hb]
      have h1 : KE * (MF + 1) ^ DE * (N + 1) ≤ KE * (MF + 1) ^ D * (N + 1) := hmul _ _ hmE
      have h2 : (1 : Nat) ≤ (MF + 1) ^ D * (N + 1) :=
        Nat.one_le_iff_ne_zero.2 (by positivity)
      have e : (1 + KT + KE) * (MF + 1) ^ D * (N + 1)
          = (MF + 1) ^ D * (N + 1) + KT * (MF + 1) ^ D * (N + 1)
            + KE * (MF + 1) ^ D * (N + 1) := by ring
      omega
    · rw [Cmd.eval_ifBit_false _ _ _ _ hb]; have := hg r; omega
    · rw [Cmd.eval_ifBit_false _ _ _ _ hb]; have := hf r (hsub r hr).2; omega

/-- **Weakening.** A smaller exit set, or a larger frozen set, is always fine. -/
theorem Cmd.CapCost.mono {c : Cmd} {F F2 F' G' : Nat} (h : c.CapCost F F')
    (hF : MaskSub F F2) (hsub : MaskSub G' F') : c.CapCost F2 G' := by
  obtain ⟨K, D, hb⟩ := h
  refine ⟨K, D, fun s MF N hF2 hN => ?_⟩
  have hFcap : ∀ r : Var, F.testBit r = true → (State.get s r).length ≤ MF :=
    fun r hr => hF2 r (hF r hr)
  exact ⟨(hb s MF N hFcap hN).1, (hb s MF N hFcap hN).2.1,
    fun r hr => (hb s MF N hFcap hN).2.2 r (hsub r hr)⟩

/-! ### The `op` rule

`Op.chk` returns `(verdict, badGrowth)`. The only op that can fail is `concat`
with **both** sources uncapped: its output is `≤ 2N`, and `CapCost`'s growth
clause allows only `N + poly(MF)`. Everything else — including `copy dst dst` on
a huge output register (FINDING X) — is paid for by the `(N+1)` factor. -/

def Op.chk (C : Nat) : Op → Option Nat × Nat
  | .clear d => (some (C ||| bitOf d), 0)
  | .appendOne _ => (some C, 0)
  | .appendZero _ => (some C, 0)
  | .head d _ => (some (C ||| bitOf d), 0)
  | .eqBit d _ _ => (some (C ||| bitOf d), 0)
  | .nonEmpty d _ => (some (C ||| bitOf d), 0)
  | .copy d s =>
      if C.testBit s then (some (C ||| bitOf d), 0)
      else if s = d then (some C, 0)
      else (some (mdiff C (bitOf d)), bitOf d)
  | .tail d s =>
      if C.testBit s then (some (C ||| bitOf d), 0)
      else if s = d then (some C, 0)
      else (some (mdiff C (bitOf d)), bitOf d)
  | .concat d a b =>
      if C.testBit a && C.testBit b then (some (C ||| bitOf d), 0)
      else if (a = d ∧ C.testBit b) ∨ (b = d ∧ C.testBit a) then
        (some (mdiff C (bitOf d)), 0)
      else if C.testBit a || C.testBit b then (some (mdiff C (bitOf d)), bitOf d)
      else (none, bitOf d)

/-- The capped-after set, defined even when the *cost* verdict fails: a
`concat` with two uncapped sources has an unbounded output, but every *other*
register keeps its cap. Keeping this total is what stops the analysis degrading
after a rejected sub-command — which is what the promotion at an enclosing loop
reads. -/
def Op.cap (C : Nat) (o : Op) : Nat :=
  ((Op.chk C o).1).getD (mdiff C (bitOf o.writesTo))

/-- The `op` rule: all three halves at once. -/
theorem Cmd.capCost_op (o : Op) (C : Nat) :
    (∀ (s : State) (MF : Nat),
        (∀ r : Var, C.testBit r = true → (State.get s r).length ≤ MF) →
        (∀ r : Var, (Op.cap C o).testBit r = true →
          (State.get (Op.eval o s) r).length ≤ 6 * (MF + 1))
        ∧ (∀ r : Var, (Op.chk C o).2.testBit r = false →
          (State.get (Op.eval o s) r).length ≤ (State.get s r).length + 2 * (MF + 1)))
    ∧ (∀ C' : Nat, (Op.chk C o).1 = some C' → (Cmd.op o).CapCost C C') := by
  have key : ∀ C' : Nat, (Op.chk C o).1 = some C' →
      ∀ (s : State) (MF N : Nat),
        (∀ r : Var, C.testBit r = true → (State.get s r).length ≤ MF) →
        (∀ r : Var, (State.get s r).length ≤ N) →
        Op.cost o s ≤ 5 * (MF + 1) ^ 1 * (N + 1)
        ∧ (∀ r : Var, (State.get (Op.eval o s) r).length ≤ N + 5 * (MF + 1) ^ 1)
        ∧ (∀ r : Var, C'.testBit r = true →
            (State.get (Op.eval o s) r).length ≤ MF + 5 * (MF + 1) ^ 1) := by
    intro C' hC' s MF N hF hN
    have hone : (1 : Nat) ≤ 5 * (MF + 1) ^ 1 * (N + 1) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    have hlin : ∀ a : Nat, a ≤ N → 2 * a + 1 ≤ 5 * (MF + 1) ^ 1 * (N + 1) := by
      intro a ha
      have he : (5 : Nat) * (MF + 1) ^ 1 * (N + 1) = (5 * MF + 5) * (N + 1) := by ring
      nlinarith
    have hlin2 : ∀ a b : Nat, a ≤ N → b ≤ N →
        2 * (a + b) + 1 ≤ 5 * (MF + 1) ^ 1 * (N + 1) := by
      intro a b ha hb
      have he : (5 : Nat) * (MF + 1) ^ 1 * (N + 1) = (5 * MF + 5) * (N + 1) := by ring
      nlinarith
    have hpow : (MF + 1) ^ 1 = MF + 1 := pow_one _
    -- `r ∈ C ||| {d}` and `r ≠ d` gives `r ∈ C`
    have hcons : ∀ (d r : Var), (C ||| bitOf d).testBit r = true → r ≠ d →
        C.testBit r = true := by
      intro d r hr hrd
      simp only [Nat.testBit_or, testBit_bitOf, Bool.or_eq_true, decide_eq_true_eq] at hr
      rcases hr with hr | hr
      · exact hr
      · exact absurd hr.symm hrd
    have hfil : ∀ (d r : Var), (mdiff C (bitOf d)).testBit r = true →
        C.testBit r = true ∧ r ≠ d := by
      intro d r hr
      simp only [testBit_mdiff, testBit_bitOf, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at hr
      exact ⟨hr.1, fun h => hr.2 h.symm⟩
    cases o with
    | clear d =>
        simp only [Op.chk, Option.some.injEq] at hC'; subst hC'
        refine ⟨by simpa only [Op.cost, hpow] using hone, fun r => ?_, fun r hr => ?_⟩
        · by_cases hr' : r = d
          · subst hr'; simp [Op.eval, State.get_set_eq]
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
        · by_cases hr' : r = d
          · subst hr'; simp [Op.eval, State.get_set_eq]
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
            have := hF r (hcons d r hr hr'); omega
    | appendOne d =>
        simp only [Op.chk, Option.some.injEq] at hC'; subst hC'
        refine ⟨by simpa only [Op.cost, hpow] using hone, fun r => ?_, fun r hr => ?_⟩
        · by_cases hr' : r = d
          · subst hr'
            simp only [Op.eval, State.get_set_eq, List.length_append, List.length_cons,
              List.length_nil]
            have := hN r; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
        · by_cases hr' : r = d
          · subst hr'
            simp only [Op.eval, State.get_set_eq, List.length_append, List.length_cons,
              List.length_nil]
            have := hF r hr; have := pb_one 1 MF; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hF r hr; omega
    | appendZero d =>
        simp only [Op.chk, Option.some.injEq] at hC'; subst hC'
        refine ⟨by simpa only [Op.cost, hpow] using hone, fun r => ?_, fun r hr => ?_⟩
        · by_cases hr' : r = d
          · subst hr'
            simp only [Op.eval, State.get_set_eq, List.length_append, List.length_cons,
              List.length_nil]
            have := hN r; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
        · by_cases hr' : r = d
          · subst hr'
            simp only [Op.eval, State.get_set_eq, List.length_append, List.length_cons,
              List.length_nil]
            have := hF r hr; have := pb_one 1 MF; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hF r hr; omega
    | head d src =>
        simp only [Op.chk, Option.some.injEq] at hC'; subst hC'
        have hd : (State.get (Op.eval (.head d src) s) d).length ≤ 1 := by
          simp only [Op.eval, State.get_set_eq]
          rcases State.get s src with _ | ⟨x, xs⟩ <;> simp
        refine ⟨by simpa only [Op.cost, hpow] using hone, fun r => ?_, fun r hr => ?_⟩
        · by_cases hr' : r = d
          · subst hr'; have := pb_one 1 MF; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
        · by_cases hr' : r = d
          · subst hr'; have := pb_one 1 MF; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
            have := hF r (hcons d r hr hr'); omega
    | eqBit d s1 s2 =>
        simp only [Op.chk, Option.some.injEq] at hC'; subst hC'
        have hd : (State.get (Op.eval (.eqBit d s1 s2) s) d).length ≤ 1 := by
          simp only [Op.eval, State.get_set_eq]
          by_cases hh : State.get s s1 = State.get s s2 <;> simp [hh]
        have hc : Op.cost (.eqBit d s1 s2) s ≤ 5 * (MF + 1) ^ 1 * (N + 1) := by
          have := hlin2 (State.get s s1).length (State.get s s2).length (hN s1) (hN s2)
          simp only [Op.cost]; omega
        refine ⟨hc, fun r => ?_, fun r hr => ?_⟩
        · by_cases hr' : r = d
          · subst hr'; have := pb_one 1 MF; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
        · by_cases hr' : r = d
          · subst hr'; have := pb_one 1 MF; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
            have := hF r (hcons d r hr hr'); omega
    | nonEmpty d src =>
        simp only [Op.chk, Option.some.injEq] at hC'; subst hC'
        have hd : (State.get (Op.eval (.nonEmpty d src) s) d).length ≤ 1 := by
          simp only [Op.eval, State.get_set_eq]
          by_cases hh : (State.get s src).isEmpty <;> simp [hh]
        refine ⟨by simpa only [Op.cost, hpow] using hone, fun r => ?_, fun r hr => ?_⟩
        · by_cases hr' : r = d
          · subst hr'; have := pb_one 1 MF; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
        · by_cases hr' : r = d
          · subst hr'; have := pb_one 1 MF; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
            have := hF r (hcons d r hr hr'); omega
    | copy d src =>
        have hc : Op.cost (.copy d src) s ≤ 5 * (MF + 1) ^ 1 * (N + 1) := by
          have := hlin (State.get s src).length (hN src)
          simp only [Op.cost]; omega
        have hglob : ∀ r : Var, (State.get (Op.eval (.copy d src) s) r).length
            ≤ N + 5 * (MF + 1) ^ 1 := by
          intro r
          by_cases hr' : r = d
          · subst hr'; simp only [Op.eval, State.get_set_eq]; have := hN src; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
        simp only [Op.chk] at hC'
        split at hC'
        · rename_i hsrc
          simp only [Option.some.injEq] at hC'; subst hC'
          refine ⟨hc, hglob, fun r hr => ?_⟩
          by_cases hr' : r = d
          · subst hr'; simp only [Op.eval, State.get_set_eq]
            have := hF src hsrc; have := pb_one 1 MF; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
            have := hF r (hcons d r hr hr'); omega
        · split at hC'
          · rename_i hsd
            simp only [Option.some.injEq] at hC'; subst hC'
            refine ⟨hc, hglob, fun r hr => ?_⟩
            by_cases hr' : r = d
            · subst hr'; simp only [Op.eval, State.get_set_eq]
              have := hF r hr; rw [hsd]; omega
            · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
              have := hF r hr; omega
          · simp only [Option.some.injEq] at hC'; subst hC'
            refine ⟨hc, hglob, fun r hr => ?_⟩
            obtain ⟨hrC, hrd⟩ := hfil d r hr
            simp only [Op.eval, State.get_set_ne _ _ _ _ hrd]
            have := hF r hrC; omega
    | tail d src =>
        have hc : Op.cost (.tail d src) s ≤ 5 * (MF + 1) ^ 1 * (N + 1) := by
          have := hlin (State.get s src).length (hN src)
          simp only [Op.cost]; omega
        have hglob : ∀ r : Var, (State.get (Op.eval (.tail d src) s) r).length
            ≤ N + 5 * (MF + 1) ^ 1 := by
          intro r
          by_cases hr' : r = d
          · subst hr'; simp only [Op.eval, State.get_set_eq, List.length_tail]
            have := hN src; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
        simp only [Op.chk] at hC'
        split at hC'
        · rename_i hsrc
          simp only [Option.some.injEq] at hC'; subst hC'
          refine ⟨hc, hglob, fun r hr => ?_⟩
          by_cases hr' : r = d
          · subst hr'; simp only [Op.eval, State.get_set_eq, List.length_tail]
            have := hF src hsrc; have := pb_one 1 MF; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
            have := hF r (hcons d r hr hr'); omega
        · split at hC'
          · rename_i hsd
            simp only [Option.some.injEq] at hC'; subst hC'
            refine ⟨hc, hglob, fun r hr => ?_⟩
            by_cases hr' : r = d
            · subst hr'
              simp only [Op.eval, State.get_set_eq, List.length_tail]
              have := hF r hr; rw [hsd]; omega
            · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
              have := hF r hr; omega
          · simp only [Option.some.injEq] at hC'; subst hC'
            refine ⟨hc, hglob, fun r hr => ?_⟩
            obtain ⟨hrC, hrd⟩ := hfil d r hr
            simp only [Op.eval, State.get_set_ne _ _ _ _ hrd]
            have := hF r hrC; omega
    | concat d a b =>
        have hc : Op.cost (.concat d a b) s ≤ 5 * (MF + 1) ^ 1 * (N + 1) := by
          have := hlin2 (State.get s a).length (State.get s b).length (hN a) (hN b)
          simp only [Op.cost]; omega
        simp only [Op.chk] at hC'
        split at hC'
        · rename_i hboth
          simp only [Option.some.injEq] at hC'; subst hC'
          simp only [Bool.and_eq_true] at hboth
          have ha := hF a hboth.1
          have hb := hF b hboth.2
          refine ⟨hc, fun r => ?_, fun r hr => ?_⟩
          · by_cases hr' : r = d
            · subst hr'; simp only [Op.eval, State.get_set_eq, List.length_append]
              have := pb_one 1 MF; omega
            · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
          · by_cases hr' : r = d
            · subst hr'; simp only [Op.eval, State.get_set_eq, List.length_append]
              have : (5 : Nat) * (MF + 1) ^ 1 = 5 * MF + 5 := by rw [pow_one]; ring
              omega
            · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
              have := hF r (hcons d r hr hr'); omega
        · have hab : (State.get s a).length + (State.get s b).length ≤ N + MF := by
            split at hC'
            · rename_i hone'
              rcases hone' with ⟨_, hb⟩ | ⟨_, ha⟩
              · have := hF b hb; have := hN a; omega
              · have := hF a ha; have := hN b; omega
            · split at hC'
              · rename_i hone'
                simp only [Bool.or_eq_true] at hone'
                rcases hone' with hh | hh
                · have := hF a hh; have := hN b; omega
                · have := hF b hh; have := hN a; omega
              · exact absurd hC' (by simp)
          have hres : C' = mdiff C (bitOf d) := by
            split at hC'
            · simp only [Option.some.injEq] at hC'; exact hC'.symm
            · split at hC'
              · simp only [Option.some.injEq] at hC'; exact hC'.symm
              · exact absurd hC' (by simp)
          subst hres
          refine ⟨hc, fun r => ?_, fun r hr => ?_⟩
          · by_cases hr' : r = d
            · subst hr'; simp only [Op.eval, State.get_set_eq, List.length_append]
              have : (5 : Nat) * (MF + 1) ^ 1 = 5 * MF + 5 := by rw [pow_one]; ring
              omega
            · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
          · obtain ⟨hrC, hrd⟩ := hfil d r hr
            simp only [Op.eval, State.get_set_ne _ _ _ _ hrd]
            have := hF r hrC; omega
  refine ⟨fun s MF hF => ⟨fun r hr => ?_, fun r hr => ?_⟩,
    fun C' hC' => ⟨5, 1, fun s MF N hFc hN => by
      rw [Cmd.cost_op, Cmd.eval_op]; exact key C' hC' s MF N hFc hN⟩⟩
  -- the cap half
  · rcases hoc : (Op.chk C o).1 with _ | C'
    · have hcap : Op.cap C o = mdiff C (bitOf o.writesTo) := by simp [Op.cap, hoc]
      rw [hcap] at hr
      simp only [testBit_mdiff, testBit_bitOf, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at hr
      rw [Op.eval_get_ne_writesTo o s r (fun hc => hr.2 hc.symm)]
      have := hF r hr.1; omega
    · have hcap : Op.cap C o = C' := by simp [Op.cap, hoc]
      rw [hcap] at hr
      have hN : ∀ v : Var, (State.get s v).length ≤ State.size s :=
        fun v => State.get_length_le_size s v
      have := (key C' hoc s MF (State.size s) hF hN).2.2 r hr
      have he : (5 : Nat) * (MF + 1) ^ 1 = 5 * MF + 5 := by rw [pow_one]; ring
      omega
  -- the growth half
  revert hr
  revert r
  intro r hr
  cases o with
  | clear d =>
      by_cases hr' : r = d
      · subst hr'; simp [Op.eval, State.get_set_eq]
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; omega
  | appendOne d =>
      by_cases hr' : r = d
      · subst hr'
        simp only [Op.eval, State.get_set_eq, List.length_append, List.length_cons,
          List.length_nil]; omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; omega
  | appendZero d =>
      by_cases hr' : r = d
      · subst hr'
        simp only [Op.eval, State.get_set_eq, List.length_append, List.length_cons,
          List.length_nil]; omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; omega
  | head d src =>
      by_cases hr' : r = d
      · subst hr'
        simp only [Op.eval, State.get_set_eq]
        rcases State.get s src with _ | ⟨x, xs⟩ <;> simp <;> omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; omega
  | eqBit d s1 s2 =>
      by_cases hr' : r = d
      · subst hr'
        simp only [Op.eval, State.get_set_eq]
        by_cases hh : State.get s s1 = State.get s s2 <;> simp [hh] <;> omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; omega
  | nonEmpty d src =>
      by_cases hr' : r = d
      · subst hr'
        simp only [Op.eval, State.get_set_eq]
        by_cases hh : (State.get s src).isEmpty <;> simp [hh] <;> omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; omega
  | copy d src =>
      by_cases hr' : r = d
      · subst hr'
        simp only [Op.chk] at hr
        split at hr
        · rename_i hsrc
          simp only [Op.eval, State.get_set_eq]; have := hF src hsrc; omega
        · split at hr
          · rename_i hsd; subst hsd
            simp only [Op.eval, State.get_set_eq]; omega
          · simp at hr
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; omega
  | tail d src =>
      by_cases hr' : r = d
      · subst hr'
        simp only [Op.chk] at hr
        split at hr
        · rename_i hsrc
          simp only [Op.eval, State.get_set_eq, List.length_tail]
          have := hF src hsrc; omega
        · split at hr
          · rename_i hsd; subst hsd
            simp only [Op.eval, State.get_set_eq, List.length_tail]; omega
          · simp at hr
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; omega
  | concat d a b =>
      by_cases hr' : r = d
      · subst hr'
        simp only [Op.chk] at hr
        split at hr
        · rename_i hboth
          simp only [Bool.and_eq_true] at hboth
          simp only [Op.eval, State.get_set_eq, List.length_append]
          have := hF a hboth.1; have := hF b hboth.2; omega
        · split at hr
          · rename_i hone'
            simp only [Op.eval, State.get_set_eq, List.length_append]
            rcases hone' with ⟨ha, hb⟩ | ⟨hb, ha⟩
            · subst ha; have := hF b hb; omega
            · subst hb; have := hF a ha; omega
          · split at hr <;> simp at hr
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; omega

/-! ### The `forBnd` rule

The loop's budget is bought in two steps. A *growth* certificate (`hPromGrow`)
says each **promoted** register grows by at most `poly(MF)` per iteration, hence
stays `≤ MF + m·poly(MF) = poly(MF)` for the whole run; the body's own `CapCost`
then spends that cap. Both runs are over the same body and the same states, so
nothing is circular — and, crucially, the growth certificate is produced by the
*same* forward pass that produces the `CapCost`, one traversal earlier.

`Fz` is the **frozen** set: the loop counter, plus ambient registers the body
never *inflates*. `NoGrow`'s bound is idempotent, so those stay `≤ MF + 1` for
any number of iterations — no trip count needed, and no growth constant, which
is what keeps the stratification (`Fz` first, then `Prom`) free of circularity.
-/

/-- The loop's closing arithmetic: `1 + m·B + m²` with `m ≤ MF` and
`B = Pb·(N + m·Pb + 1)` is `poly(MF)·(N+1)`. -/
private theorem loop_budget (A dA KG DG MF Pb G : Nat)
    (hPb : Pb ≤ A * (MF + 1) ^ dA) (hG : G ≤ KG * (MF + 1) ^ DG) :
    1 + MF * Pb * (1 + MF * Pb) + MF * MF + MF * G
      ≤ (2 + A + A * A + KG) * (MF + 1) ^ (2 * dA + DG + 4) := by
  set E := 2 * dA + DG + 4 with hE
  have hb1 : MF * Pb ≤ A * (MF + 1) ^ (dA + 1) := by
    calc MF * Pb ≤ MF * (A * (MF + 1) ^ dA) := Nat.mul_le_mul_left _ hPb
      _ ≤ (MF + 1) * (A * (MF + 1) ^ dA) := Nat.mul_le_mul_right _ (by omega)
      _ = A * (MF + 1) ^ (dA + 1) := by ring
  have hb2 : MF * Pb * (MF * Pb) ≤ A * A * (MF + 1) ^ (2 * dA + 2) := by
    have h := Nat.mul_le_mul hb1 hb1
    have he : A * (MF + 1) ^ (dA + 1) * (A * (MF + 1) ^ (dA + 1))
        = A * A * ((MF + 1) ^ (dA + 1) * (MF + 1) ^ (dA + 1)) := by ring
    have he2 : (MF + 1) ^ (dA + 1) * (MF + 1) ^ (dA + 1) = (MF + 1) ^ (2 * dA + 2) := by
      rw [← pow_add]; congr 1; omega
    rw [he, he2] at h; exact h
  have hb3 : MF * MF ≤ (MF + 1) ^ 2 := by
    have he : (MF + 1) ^ 2 = (MF + 1) * (MF + 1) := by ring
    nlinarith
  have hb4 : MF * G ≤ KG * (MF + 1) ^ (DG + 1) := by
    calc MF * G ≤ MF * (KG * (MF + 1) ^ DG) := Nat.mul_le_mul_left _ hG
      _ ≤ (MF + 1) * (KG * (MF + 1) ^ DG) := Nat.mul_le_mul_right _ (by omega)
      _ = KG * (MF + 1) ^ (DG + 1) := by ring
  have l1 : A * (MF + 1) ^ (dA + 1) ≤ A * (MF + 1) ^ E := pb_mono le_rfl (by omega)
  have l2 : A * A * (MF + 1) ^ (2 * dA + 2) ≤ A * A * (MF + 1) ^ E := pb_mono le_rfl (by omega)
  have l3 : (MF + 1) ^ 2 ≤ (MF + 1) ^ E := Nat.pow_le_pow_right (by omega) (by omega)
  have l4 : KG * (MF + 1) ^ (DG + 1) ≤ KG * (MF + 1) ^ E := pb_mono le_rfl (by omega)
  have l5 : (1 : Nat) ≤ (MF + 1) ^ E := pb_one E MF
  have hexp : (2 + A + A * A + KG) * (MF + 1) ^ E
      = (MF + 1) ^ E + (MF + 1) ^ E + A * (MF + 1) ^ E + A * A * (MF + 1) ^ E
        + KG * (MF + 1) ^ E := by ring
  have hprod : MF * Pb * (1 + MF * Pb) = MF * Pb + MF * Pb * (MF * Pb) := by ring
  omega

theorem Cmd.capCost_forBnd (cnt bnd : Var) (body : Cmd) (F Fz Prom Fb' F' : Nat)
    (hbnd : F.testBit bnd = true)
    (hFzcnt : Fz.testBit cnt = true)
    (hFz : ∀ r : Var, r ≠ cnt → Fz.testBit r = true →
      F.testBit r = true ∧ body.NoGrow r = true)
    (hProm : ∀ r : Var, Prom.testBit r = true → F.testBit r = true)
    (hPromGrow : ∃ KG DG : Nat, ∀ (s : State) (MF : Nat),
      (∀ r : Var, Fz.testBit r = true → (State.get s r).length ≤ MF) →
      ∀ r : Var, Prom.testBit r = true →
        (State.get (body.eval s) r).length ≤ (State.get s r).length + KG * (MF + 1) ^ DG)
    (hbody : body.CapCost (Fz ||| Prom) Fb')
    (hF' : ∀ r : Var, F'.testBit r = true → F.testBit r = true ∧
      ((r ≠ cnt ∧ Fz.testBit r = true) ∨ Prom.testBit r = true ∨ Fb'.testBit r = true)) :
    (Cmd.forBnd cnt bnd body).CapCost F F' := by
  obtain ⟨KG, DG, hgrow⟩ := hPromGrow
  obtain ⟨Kb, Db, hbb⟩ := hbody
  set KG2 := KG * 2 ^ DG + 1 with hKG2
  set A := Kb * (KG2 + 1) ^ Db with hAdef
  refine ⟨2 + A + A * A + KG2, 2 * ((DG + 1) * Db) + DG + 4, fun s MF N hF hN => ?_⟩
  set G := KG * (MF + 1 + 1) ^ DG + 1 with hGdef
  set MFb := MF + (MF + 1) * G with hMFbdef
  set Pb := Kb * (MFb + 1) ^ Db with hPbdef
  set m := (State.get s bnd).length with hmdef
  have hmMF : m ≤ MF := hF bnd hbnd
  have hmN : m ≤ N := hN bnd
  have hG1 : 1 ≤ G := by rw [hGdef]; omega
  have hMFb1 : MF + 1 ≤ MFb := by
    rw [hMFbdef]
    have : 1 * 1 ≤ (MF + 1) * G := Nat.mul_le_mul (by omega) hG1
    omega
  -- the loop invariant
  set MI : Nat → State → Prop := fun i st =>
      (∀ v : Var, v ≠ cnt → Fz.testBit v = true → (State.get st v).length ≤ MF + 1)
    ∧ (∀ v : Var, Prom.testBit v = true → (State.get st v).length ≤ MF + i * G)
    ∧ (∀ v : Var, (State.get st v).length ≤ N + i * Pb)
    ∧ (0 < i → ∀ v : Var, Fb'.testBit v = true → (State.get st v).length ≤ MFb + Pb)
    with hMIdef
  have h0 : MI 0 s := by
    refine ⟨fun v hvc hv => ?_, fun v hv => ?_, fun v => by simpa using hN v, by omega⟩
    · have := hF v (hFz v hvc hv).1; omega
    · have := hF v (hProm v hv); simpa using this
  -- the per-iteration caps
  have hiter : ∀ i st, i < m → MI i st →
      (∀ v : Var, Fz.testBit v = true →
        (State.get (st.set cnt (List.replicate i 1)) v).length ≤ MF + 1)
      ∧ (∀ v : Var, (Fz ||| Prom).testBit v = true →
        (State.get (st.set cnt (List.replicate i 1)) v).length ≤ MFb)
      ∧ (∀ v : Var, (State.get (st.set cnt (List.replicate i 1)) v).length ≤ N + i * Pb) := by
    intro i st hi hM
    obtain ⟨hFzc, hPr, hAll, -⟩ := hM
    have hcapFz : ∀ v : Var, Fz.testBit v = true →
        (State.get (st.set cnt (List.replicate i 1)) v).length ≤ MF + 1 := by
      intro v hv
      by_cases hvc : v = cnt
      · subst hvc; rw [State.get_set_eq, List.length_replicate]; omega
      · rw [State.get_set_ne _ _ _ _ hvc]; exact hFzc v hvc hv
    refine ⟨hcapFz, fun v hv => ?_, fun v => ?_⟩
    · simp only [Nat.testBit_or, Bool.or_eq_true] at hv
      rcases hv with hz | hp
      · have := hcapFz v hz; omega
      · by_cases hvc : v = cnt
        · subst hvc; rw [State.get_set_eq, List.length_replicate]; omega
        · rw [State.get_set_ne _ _ _ _ hvc]
          have h1 := hPr v hp
          have h2 : i * G ≤ (MF + 1) * G := Nat.mul_le_mul_right _ (by omega)
          omega
    · by_cases hvc : v = cnt
      · subst hvc; rw [State.get_set_eq, List.length_replicate]; omega
      · rw [State.get_set_ne _ _ _ _ hvc]; exact hAll v
  have hstep : ∀ i st, i < m → MI i st →
      MI (i + 1) (body.eval (st.set cnt (List.replicate i 1))) := by
    intro i st hi hM
    obtain ⟨hcapFz, hcapFb, hcapN⟩ := hiter i st hi hM
    obtain ⟨hFzc, hPr, hAll, -⟩ := hM
    obtain ⟨-, hglob, hfb⟩ := hbb _ MFb (N + i * Pb) hcapFb hcapN
    refine ⟨fun v hvc hv => ?_, fun v hv => ?_, fun v => ?_, fun _ v hv => ?_⟩
    · have hng := (hFz v hvc hv).2
      have := Cmd.noGrow_sound body v hng (st.set cnt (List.replicate i 1))
      have h2 := hcapFz v hv
      omega
    · have hgr := hgrow _ (MF + 1) hcapFz v hv
      have harith : (i + 1) * G = i * G + G := by ring
      by_cases hvc : v = cnt
      · subst hvc
        rw [State.get_set_eq, List.length_replicate] at hgr
        have : i ≤ MF := by omega
        have hGle : KG * (MF + 1 + 1) ^ DG ≤ G := by rw [hGdef]; omega
        have : 0 ≤ i * G := Nat.zero_le _
        omega
      · rw [State.get_set_ne _ _ _ _ hvc] at hgr
        have hGle : KG * (MF + 1 + 1) ^ DG ≤ G := by rw [hGdef]; omega
        have := hPr v hv
        omega
    · have := hglob v
      have harith : (i + 1) * Pb = i * Pb + Pb := by ring
      have he : Kb * (MFb + 1) ^ Db = Pb := hPbdef.symm
      omega
    · have := hfb v hv
      have he : Kb * (MFb + 1) ^ Db = Pb := hPbdef.symm
      omega
  -- the closing budget
  have hGA : G ≤ KG2 * (MF + 1) ^ DG := by
    have h1 : KG * (MF + 1 + 1) ^ DG ≤ (KG * 2 ^ DG) * (MF + 1) ^ DG := pb_succ KG DG MF
    have h2 : (1 : Nat) ≤ (MF + 1) ^ DG := pb_one DG MF
    have h3 : KG2 * (MF + 1) ^ DG = (KG * 2 ^ DG) * (MF + 1) ^ DG + (MF + 1) ^ DG := by
      rw [hKG2]; ring
    rw [hGdef]; omega
  have hPbA : Pb ≤ A * (MF + 1) ^ ((DG + 1) * Db) := by
    have hg1 : 1 + G ≤ (KG2 + 1) * (MF + 1) ^ DG := by
      have := pb_one DG MF; nlinarith
    have hbase : MFb + 1 ≤ (KG2 + 1) * (MF + 1) ^ (DG + 1) := by
      have he : MFb + 1 = (MF + 1) * (1 + G) := by rw [hMFbdef]; ring
      calc MFb + 1 = (MF + 1) * (1 + G) := he
        _ ≤ (MF + 1) * ((KG2 + 1) * (MF + 1) ^ DG) := Nat.mul_le_mul_left _ hg1
        _ = (KG2 + 1) * (MF + 1) ^ (DG + 1) := by ring
    calc Pb ≤ Kb * ((KG2 + 1) * (MF + 1) ^ (DG + 1)) ^ Db :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
      _ = Kb * ((KG2 + 1) ^ Db * ((MF + 1) ^ (DG + 1)) ^ Db) := by rw [mul_pow]
      _ = A * (MF + 1) ^ ((DG + 1) * Db) := by rw [← pow_mul, hAdef]; ring
  set Btot := 1 + MF * Pb * (1 + MF * Pb) + MF * MF + MF * G with hBtotdef
  have hbudget : Btot ≤ (2 + A + A * A + KG2) * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4) :=
    loop_budget A ((DG + 1) * Db) KG2 DG MF Pb G hPbA hGA
  have hmPb : m * Pb ≤ Btot := by
    have h1 : m * Pb ≤ MF * Pb := Nat.mul_le_mul_right _ hmMF
    have h2 : MF * Pb ≤ MF * Pb * (1 + MF * Pb) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hmG : m * G ≤ Btot := by
    have h1 : m * G ≤ MF * G := Nat.mul_le_mul_right _ hmMF
    omega
  have hfinal : MI m ((Cmd.forBnd cnt bnd body).eval s) := by
    rw [Cmd.eval_forBnd]
    exact Cmd.foldlState_range_induct body cnt m s MI h0 hstep
  obtain ⟨hFzF, hPrF, hAllF, hFbF⟩ := hfinal
  refine ⟨?_, fun r => ?_, fun r hr => ?_⟩
  · -- cost
    have hC : ∀ i st, i < m → MI i st →
        body.cost (st.set cnt (List.replicate i 1)) ≤ Pb * (N + m * Pb + 1) := by
      intro i st hi hM
      obtain ⟨-, hcapFb, hcapN⟩ := hiter i st hi hM
      obtain ⟨hcost, -, -⟩ := hbb _ MFb (N + i * Pb) hcapFb hcapN
      have hle : i * Pb ≤ m * Pb := Nat.mul_le_mul_right _ (by omega)
      have he : Kb * (MFb + 1) ^ Db * (N + i * Pb + 1) = Pb * (N + i * Pb + 1) := by
        rw [hPbdef]
      calc body.cost (st.set cnt (List.replicate i 1))
          ≤ Kb * (MFb + 1) ^ Db * (N + i * Pb + 1) := hcost
        _ = Pb * (N + i * Pb + 1) := he
        _ ≤ Pb * (N + m * Pb + 1) := Nat.mul_le_mul_left _ (by omega)
    have hloop := Cmd.cost_forBnd_le cnt bnd body s (Pb * (N + m * Pb + 1)) MI h0 hstep hC
    rw [← hmdef] at hloop
    refine le_trans hloop ?_
    refine le_trans (?_ : 1 + m * (Pb * (N + m * Pb + 1)) + m * m ≤ Btot * (N + 1)) ?_
    · have h1 : m * (Pb * (N + m * Pb + 1)) ≤ MF * Pb * ((N + 1) * (1 + MF * Pb)) := by
        have hmp : m * Pb ≤ MF * Pb := Nat.mul_le_mul_right _ hmMF
        have hin : N + m * Pb + 1 ≤ (N + 1) * (1 + MF * Pb) := by
          have he : (N + 1) * (1 + MF * Pb) = (N + 1) + MF * Pb * (N + 1) := by ring
          have h4 : MF * Pb ≤ MF * Pb * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
          omega
        calc m * (Pb * (N + m * Pb + 1)) = (m * Pb) * (N + m * Pb + 1) := by ring
          _ ≤ (MF * Pb) * ((N + 1) * (1 + MF * Pb)) := Nat.mul_le_mul hmp hin
      have h2 : m * m ≤ MF * MF * (N + 1) := by
        have : m * m ≤ MF * MF := Nat.mul_le_mul hmMF hmMF
        have h3 : MF * MF ≤ MF * MF * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have he : Btot * (N + 1) = (N + 1) + MF * Pb * ((N + 1) * (1 + MF * Pb))
          + MF * MF * (N + 1) + MF * G * (N + 1) := by rw [hBtotdef]; ring
      omega
    · exact Nat.mul_le_mul_right _ hbudget
  · -- global growth
    have := hAllF r; omega
  · -- the capped exit set
    obtain ⟨hrF, hcase⟩ := hF' r hr
    have hbase : (1 : Nat) ≤ (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4) := pb_one _ MF
    have hbig : Btot ≤ (2 + A + A * A + KG2) * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4) :=
      hbudget
    rcases hcase with ⟨hrc, hrz⟩ | hrp | hrb
    · have := hFzF r hrc hrz
      have h1 : (1 : Nat) ≤ (2 + A + A * A + KG2) * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4) :=
        le_trans (by omega) (Nat.mul_le_mul_left _ hbase)
      omega
    · have h1 := hPrF r hrp
      have h2 : m * G ≤ (2 + A + A * A + KG2) * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4) := by
        omega
      omega
    · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- the loop never ran: the state is `s`
        have hev : (Cmd.forBnd cnt bnd body).eval s = s := by
          rw [Cmd.eval_forBnd, ← hmdef, hm0]; rfl
        rw [hev]
        have := hF r hrF; omega
      · have h1 := hFbF hmpos r hrb
        have hE1 : (MF + 1) * G
            ≤ KG2 * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4) := by
          calc (MF + 1) * G ≤ (MF + 1) * (KG2 * (MF + 1) ^ DG) := Nat.mul_le_mul_left _ hGA
            _ = KG2 * (MF + 1) ^ (DG + 1) := by ring
            _ ≤ KG2 * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4) := pb_mono le_rfl (by omega)
        have hE2 : Pb ≤ A * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4) :=
          le_trans hPbA (pb_mono le_rfl (by omega))
        have hK : (2 + A + A * A + KG2) * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4)
            = 2 * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4)
              + A * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4)
              + A * A * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4)
              + KG2 * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4) := by ring
        rw [hMFbdef] at h1
        omega


/-! ### The loop's cap-and-growth rule

Independent of the cost analysis, and that independence is the point: it is
sound even when the body's own cost check *fails*, which is what lets a loop
promote a register before knowing that its body is analysable. -/

theorem Cmd.loopStep (cnt bnd : Var) (body : Cmd) (C Fz B Cb : Nat)
    (hbnd : C.testBit bnd = true)
    (hFzcnt : Fz.testBit cnt = true)
    (hFz : ∀ r : Var, r ≠ cnt → Fz.testBit r = true →
      C.testBit r = true ∧ body.NoGrow r = true)
    (hb : ∃ K D : Nat, ∀ (s : State) (MF : Nat),
      (∀ r : Var, Fz.testBit r = true → (State.get s r).length ≤ MF) →
      (∀ r : Var, Cb.testBit r = true → (State.get (body.eval s) r).length ≤ K * (MF + 1) ^ D)
      ∧ (∀ r : Var, B.testBit r = false →
          (State.get (body.eval s) r).length ≤ (State.get s r).length + K * (MF + 1) ^ D)) :
    ∃ K D : Nat, ∀ (s : State) (MF : Nat),
      (∀ r : Var, C.testBit r = true → (State.get s r).length ≤ MF) →
      (∀ r : Var, r ≠ cnt → Fz.testBit r = true →
        (State.get ((Cmd.forBnd cnt bnd body).eval s) r).length ≤ MF + 1)
    ∧ (∀ r : Var, B.testBit r = false →
        (State.get ((Cmd.forBnd cnt bnd body).eval s) r).length
          ≤ (State.get s r).length + K * (MF + 1) ^ D)
    ∧ (∀ r : Var, C.testBit r = true → Cb.testBit r = true →
        (State.get ((Cmd.forBnd cnt bnd body).eval s) r).length ≤ K * (MF + 1) ^ D) := by
  obtain ⟨Kb, Db, hbb⟩ := hb
  refine ⟨1 + (Kb * 2 ^ Db + 1) + Kb * 2 ^ Db, Db + Db + 2, fun s MF hF => ?_⟩
  set KG2 := Kb * 2 ^ Db + 1 with hKG2
  set G := Kb * (MF + 1 + 1) ^ Db with hGdef
  set m := (State.get s bnd).length with hmdef
  have hmMF : m ≤ MF := hF bnd hbnd
  set MI : Nat → State → Prop := fun i st =>
      (∀ v : Var, v ≠ cnt → Fz.testBit v = true → (State.get st v).length ≤ MF + 1)
    ∧ (∀ v : Var, B.testBit v = false →
        (State.get st v).length ≤ (State.get s v).length + i * (MF + G))
    ∧ (0 < i → ∀ v : Var, Cb.testBit v = true → (State.get st v).length ≤ G) with hMIdef
  have h0 : MI 0 s := ⟨fun v hvc hv => by have := hF v (hFz v hvc hv).1; omega,
    fun v _ => by simp, by omega⟩
  have hstep : ∀ i st, i < m → MI i st →
      MI (i + 1) (body.eval (st.set cnt (List.replicate i 1))) := by
    intro i st hi hM
    obtain ⟨hFzc, hGr, -⟩ := hM
    set u := st.set cnt (List.replicate i 1) with hu
    have hcapFz : ∀ v : Var, Fz.testBit v = true → (State.get u v).length ≤ MF + 1 := by
      intro v hv
      by_cases hvc : v = cnt
      · subst hvc; rw [hu, State.get_set_eq, List.length_replicate]; omega
      · rw [hu, State.get_set_ne _ _ _ _ hvc]; exact hFzc v hvc hv
    have hshift : ∀ v : Var, (State.get u v).length ≤ (State.get st v).length + MF := by
      intro v
      by_cases hvc : v = cnt
      · subst hvc; rw [hu, State.get_set_eq, List.length_replicate]; omega
      · rw [hu, State.get_set_ne _ _ _ _ hvc]; omega
    obtain ⟨hbcap, hbgr⟩ := hbb u (MF + 1) hcapFz
    refine ⟨fun v hvc hv => ?_, fun v hv => ?_, fun _ v hv => ?_⟩
    · have hng := (hFz v hvc hv).2
      have := Cmd.noGrow_sound body v hng u
      have h2 := hcapFz v hv
      omega
    · have hgr := hbgr v hv
      have h1 := hshift v
      have h2 := hGr v hv
      have harith : (i + 1) * (MF + G) = i * (MF + G) + (MF + G) := by ring
      omega
    · have := hbcap v hv; rw [← hGdef] at this; exact this
  have hfinal : MI m ((Cmd.forBnd cnt bnd body).eval s) := by
    rw [Cmd.eval_forBnd]
    exact Cmd.foldlState_range_induct body cnt m s MI h0 hstep
  obtain ⟨hf1, hf2, hf3⟩ := hfinal
  -- `G ≤ KG2·(MF+1)^Db` and `m·(MF+G) ≤ (1+KG2)·(MF+1)^(Db+2)`
  have hGA : G ≤ KG2 * (MF + 1) ^ Db := by
    have h1 : Kb * (MF + 1 + 1) ^ Db ≤ (Kb * 2 ^ Db) * (MF + 1) ^ Db := pb_succ Kb Db MF
    have h2 : (1 : Nat) ≤ (MF + 1) ^ Db := pb_one Db MF
    have h3 : KG2 * (MF + 1) ^ Db = (Kb * 2 ^ Db) * (MF + 1) ^ Db + (MF + 1) ^ Db := by
      rw [hKG2]; ring
    rw [hGdef]; omega
  set K := 1 + KG2 + Kb * 2 ^ Db with hKdef
  set D := Db + Db + 2 with hDdef
  have hone : (1 : Nat) ≤ (MF + 1) ^ D := pb_one D MF
  have hKD : K * (MF + 1) ^ D
      = (MF + 1) ^ D + KG2 * (MF + 1) ^ D + Kb * 2 ^ Db * (MF + 1) ^ D := by
    rw [hKdef]; ring
  have hbig : m * (MF + G) ≤ (1 + KG2) * (MF + 1) ^ (Db + 2) := by
    have hmg : m * (MF + G) ≤ (MF + 1) * (MF + G) := Nat.mul_le_mul_right _ (by omega)
    have h1 : (MF + 1) * MF ≤ (MF + 1) ^ (Db + 2) := by
      have he : (MF + 1) ^ (Db + 2) = (MF + 1) ^ Db * ((MF + 1) * (MF + 1)) := by ring
      have := pb_one Db MF
      nlinarith
    have h2 : (MF + 1) * G ≤ KG2 * (MF + 1) ^ (Db + 2) := by
      calc (MF + 1) * G ≤ (MF + 1) * (KG2 * (MF + 1) ^ Db) := Nat.mul_le_mul_left _ hGA
        _ = KG2 * (MF + 1) ^ (Db + 1) := by ring
        _ ≤ KG2 * (MF + 1) ^ (Db + 2) := pb_mono le_rfl (by omega)
    have he : (MF + 1) * (MF + G) = (MF + 1) * MF + (MF + 1) * G := by ring
    have he2 : (1 + KG2) * (MF + 1) ^ (Db + 2)
        = (MF + 1) ^ (Db + 2) + KG2 * (MF + 1) ^ (Db + 2) := by ring
    omega
  have hbig2 : (1 + KG2) * (MF + 1) ^ (Db + 2) ≤ K * (MF + 1) ^ D := by
    have h1 : (MF + 1) ^ (Db + 2) ≤ (MF + 1) ^ D :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : KG2 * (MF + 1) ^ (Db + 2) ≤ KG2 * (MF + 1) ^ D := pb_mono le_rfl (by omega)
    have he : (1 + KG2) * (MF + 1) ^ (Db + 2)
        = (MF + 1) ^ (Db + 2) + KG2 * (MF + 1) ^ (Db + 2) := by ring
    omega
  have hGK : G ≤ K * (MF + 1) ^ D := by
    have h1 : KG2 * (MF + 1) ^ Db ≤ KG2 * (MF + 1) ^ D := pb_mono le_rfl (by omega)
    omega
  have hMFK : MF ≤ K * (MF + 1) ^ D := by
    have h1 : MF + 1 ≤ (MF + 1) ^ D := Nat.le_self_pow (by omega) _
    omega
  refine ⟨hf1, fun r hr => ?_, fun r hrC hrb => ?_⟩
  · have := hf2 r hr; omega
  · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have hev : (Cmd.forBnd cnt bnd body).eval s = s := by
        rw [Cmd.eval_forBnd, ← hmdef, hm0]; rfl
      rw [hev]
      have := hF r hrC; omega
    · have := hf3 hmpos r hrb; omega

/-! ## Part 4 — the decidable forward pass

`Cmd.chk C c = (ok, C', B)`:

* `ok` — a `Cmd.CapCost c C C'` certificate exists;
* `C'` — the registers still capped by `poly(MF)` after `c`;
* `B` — the registers whose growth across `c` is **not** certified additive.

**`C'` and `B` are sound whether or not `ok` holds.** That is the whole design:
a rejected sub-command must not blind the analysis to what happens after it,
because an enclosing loop reads exactly this information to decide what to
promote — and the promotion is what makes the sub-command acceptable on the
second pass.

The `forBnd` rule pays for a second traversal of the body **only** when the
first one is rejected. On `S1Program.s1Program` that happens inside
`S1CardEmit.cFive` and `S1Step.stepFam` and never inside `S1Prelude.cPrelude`,
the family that is 99% of the program. -/

def Cmd.chk (C : Nat) : Cmd → Bool × Nat × Nat
  | .op o => ((Op.chk C o).1.isSome, Op.cap C o, (Op.chk C o).2)
  | .seq a b =>
      match Cmd.chk C a with
      | (ok1, C1, B1) =>
          match Cmd.chk C1 b with
          | (ok2, C2, B2) => (ok1 && ok2, C2, B1 ||| B2)
  | .ifBit _ a b =>
      match Cmd.chk C a, Cmd.chk C b with
      | (ok1, C1, B1), (ok2, C2, B2) => (ok1 && ok2, C1 &&& C2, B1 ||| B2)
  | .forBnd cnt bnd body =>
      if C.testBit bnd then
        match Cmd.chk (bitOf cnt ||| mdiff C body.ngm) body with
        | (ok1, Cb, B) =>
            if ok1 then
              (true, mdiff C (bitOf cnt ||| body.ngm) ||| mdiff C B ||| (C &&& Cb), B)
            else
              match Cmd.chk (bitOf cnt ||| mdiff C body.ngm ||| mdiff C B) body with
              | (ok2, Cb2, _) =>
                  (ok2, mdiff C (bitOf cnt ||| body.ngm) ||| mdiff C B
                    ||| (C &&& Cb &&& Cb2), B)
      else (false, mdiff C (bitOf cnt ||| body.ngm), bitOf cnt ||| body.ngm)

/-- `(MF + Ka·(MF+1)^Da + 1)^E` is again a `poly(MF)` — the step every
composition of two analysed fragments needs. -/
private theorem pb_comp (Ka Da E MF : Nat) :
    (MF + Ka * (MF + 1) ^ Da + 1) ^ E ≤ (Ka + 1) ^ E * (MF + 1) ^ ((Da + 1) * E) := by
  calc (MF + Ka * (MF + 1) ^ Da + 1) ^ E
      ≤ ((Ka + 1) * (MF + 1) ^ (Da + 1)) ^ E := Nat.pow_le_pow_left (pb_shift Ka Da MF) _
    _ = (Ka + 1) ^ E * ((MF + 1) ^ (Da + 1)) ^ E := by rw [mul_pow]
    _ = (Ka + 1) ^ E * (MF + 1) ^ ((Da + 1) * E) := by rw [← pow_mul]

/-- **The pass is sound** — all three halves, in one induction. The cap and
growth halves are unconditional; the `CapCost` half is conditional on `ok`. -/
theorem Cmd.chk_sound : ∀ (c : Cmd) (C : Nat),
    (∃ K D : Nat, ∀ (s : State) (MF : Nat),
        (∀ r : Var, C.testBit r = true → (State.get s r).length ≤ MF) →
        (∀ r : Var, (c.chk C).2.1.testBit r = true →
          (State.get (c.eval s) r).length ≤ K * (MF + 1) ^ D)
      ∧ (∀ r : Var, (c.chk C).2.2.testBit r = false →
          (State.get (c.eval s) r).length ≤ (State.get s r).length + K * (MF + 1) ^ D))
    ∧ ((c.chk C).1 = true → c.CapCost C (c.chk C).2.1) := by
  intro c
  induction c with
  | op o =>
      intro C
      obtain ⟨hb, hcap⟩ := Cmd.capCost_op o C
      refine ⟨⟨6, 1, fun s MF hF => ⟨fun r hr => ?_, fun r hr => ?_⟩⟩, fun hok => ?_⟩
      · rw [Cmd.eval_op, pow_one]
        have := (hb s MF hF).1 r hr; omega
      · rw [Cmd.eval_op, pow_one]
        have := (hb s MF hF).2 r hr; omega
      · rcases hoc : (Op.chk C o).1 with _ | C'
        · simp [Cmd.chk, hoc] at hok
        · have : Op.cap C o = C' := by simp [Op.cap, hoc]
          show (Cmd.op o).CapCost C (Op.cap C o)
          rw [this]; exact hcap C' hoc
  | seq a b iha ihb =>
      intro C
      obtain ⟨⟨KA, DA, hba⟩, hca⟩ := iha C
      rcases hra : Cmd.chk C a with ⟨oka, C1, Ba⟩
      obtain ⟨⟨KB, DB, hbb⟩, hcb⟩ := ihb C1
      rcases hrb : Cmd.chk C1 b with ⟨okb, C2, Bb⟩
      have hsq : (a ;; b).chk C = (oka && okb, C2, Ba ||| Bb) := by
        simp [Cmd.chk, hra, hrb]
      have hA1 : (Cmd.chk C a).2.1 = C1 := by rw [hra]
      have hA2 : (Cmd.chk C a).2.2 = Ba := by rw [hra]
      have hB1 : (Cmd.chk C1 b).2.1 = C2 := by rw [hrb]
      have hB2 : (Cmd.chk C1 b).2.2 = Bb := by rw [hrb]
      refine ⟨⟨KB * (KA + 1) ^ DB + KA, max ((DA + 1) * DB) (max DA DB),
        fun s MF hF => ?_⟩, fun hok => ?_⟩
      · obtain ⟨hcapa, hgra⟩ := hba s MF hF
        have hC1 : ∀ r : Var, C1.testBit r = true →
            (State.get (a.eval s) r).length ≤ KA * (MF + 1) ^ DA :=
          fun r hr => hcapa r (by rw [hA1]; exact hr)
        obtain ⟨hcapb, hgrb⟩ := hbb (a.eval s) (KA * (MF + 1) ^ DA) hC1
        set E := max ((DA + 1) * DB) (max DA DB) with hE
        have hpc : KB * (KA * (MF + 1) ^ DA + 1) ^ DB
            ≤ KB * (KA + 1) ^ DB * (MF + 1) ^ E := by
          have h0 : KA * (MF + 1) ^ DA + 1 ≤ MF + KA * (MF + 1) ^ DA + 1 := by omega
          have h1 : (KA * (MF + 1) ^ DA + 1) ^ DB
              ≤ (KA + 1) ^ DB * (MF + 1) ^ ((DA + 1) * DB) :=
            le_trans (Nat.pow_le_pow_left h0 _) (pb_comp KA DA DB MF)
          calc KB * (KA * (MF + 1) ^ DA + 1) ^ DB
              ≤ KB * ((KA + 1) ^ DB * (MF + 1) ^ ((DA + 1) * DB)) :=
                Nat.mul_le_mul_left _ h1
            _ = KB * (KA + 1) ^ DB * (MF + 1) ^ ((DA + 1) * DB) := by ring
            _ ≤ KB * (KA + 1) ^ DB * (MF + 1) ^ E := pb_mono le_rfl (by omega)
        have hKA : KA * (MF + 1) ^ DA ≤ KA * (MF + 1) ^ E := pb_mono le_rfl (by omega)
        have hsum : (KB * (KA + 1) ^ DB + KA) * (MF + 1) ^ E
            = KB * (KA + 1) ^ DB * (MF + 1) ^ E + KA * (MF + 1) ^ E := by ring
        rw [Cmd.eval_seq]
        constructor
        · intro r hr
          rw [hsq] at hr
          have := hcapb r (by rw [hB1]; exact hr)
          omega
        · intro r hr
          rw [hsq] at hr
          simp only [Nat.testBit_or, Bool.or_eq_false_iff] at hr
          have g1 := hgra r (by rw [hA2]; exact hr.1)
          have g2 := hgrb r (by rw [hB2]; exact hr.2)
          omega
      · rw [hsq] at hok ⊢
        simp only [Bool.and_eq_true] at hok
        have h1 : a.CapCost C C1 := by have := hca (by rw [hra]; exact hok.1); rwa [hA1] at this
        have h2 : b.CapCost C1 C2 := by have := hcb (by rw [hrb]; exact hok.2); rwa [hB1] at this
        exact h1.seq h2
  | ifBit t a b iha ihb =>
      intro C
      obtain ⟨⟨KA, DA, hba⟩, hca⟩ := iha C
      obtain ⟨⟨KB, DB, hbb⟩, hcb⟩ := ihb C
      rcases hra : Cmd.chk C a with ⟨oka, C1, Ba⟩
      rcases hrb : Cmd.chk C b with ⟨okb, C2, Bb⟩
      have hif : (Cmd.ifBit t a b).chk C = (oka && okb, C1 &&& C2, Ba ||| Bb) := by
        simp [Cmd.chk, hra, hrb]
      have hA1 : (Cmd.chk C a).2.1 = C1 := by rw [hra]
      have hA2 : (Cmd.chk C a).2.2 = Ba := by rw [hra]
      have hB1 : (Cmd.chk C b).2.1 = C2 := by rw [hrb]
      have hB2 : (Cmd.chk C b).2.2 = Bb := by rw [hrb]
      refine ⟨⟨KA + KB, max DA DB, fun s MF hF => ?_⟩, fun hok => ?_⟩
      · obtain ⟨hcapa, hgra⟩ := hba s MF hF
        obtain ⟨hcapb, hgrb⟩ := hbb s MF hF
        have hd1 : KA * (MF + 1) ^ DA ≤ (KA + KB) * (MF + 1) ^ max DA DB :=
          pb_mono (by omega) (by omega)
        have hd2 : KB * (MF + 1) ^ DB ≤ (KA + KB) * (MF + 1) ^ max DA DB :=
          pb_mono (by omega) (by omega)
        rw [hif]
        by_cases hbit : State.get s t = [1]
        · rw [Cmd.eval_ifBit_true _ _ _ _ hbit]
          refine ⟨fun r hr => ?_, fun r hr => ?_⟩
          · simp only [Nat.testBit_and, Bool.and_eq_true] at hr
            have := hcapa r (by rw [hA1]; exact hr.1); omega
          · simp only [Nat.testBit_or, Bool.or_eq_false_iff] at hr
            have := hgra r (by rw [hA2]; exact hr.1); omega
        · rw [Cmd.eval_ifBit_false _ _ _ _ hbit]
          refine ⟨fun r hr => ?_, fun r hr => ?_⟩
          · simp only [Nat.testBit_and, Bool.and_eq_true] at hr
            have := hcapb r (by rw [hB1]; exact hr.2); omega
          · simp only [Nat.testBit_or, Bool.or_eq_false_iff] at hr
            have := hgrb r (by rw [hB2]; exact hr.2); omega
      · rw [hif] at hok ⊢
        simp only [Bool.and_eq_true] at hok
        have h1 : a.CapCost C C1 := by have := hca (by rw [hra]; exact hok.1); rwa [hA1] at this
        have h2 : b.CapCost C C2 := by have := hcb (by rw [hrb]; exact hok.2); rwa [hB1] at this
        refine Cmd.CapCost.ifBit h1 h2 (fun r hr => ?_)
        simp only [Nat.testBit_and, Bool.and_eq_true] at hr
        exact hr
  | forBnd cnt bnd body ih =>
      intro C
      set NG := body.ngm with hNG
      set Fz := bitOf cnt ||| mdiff C NG with hFzd
      have hFzcnt : Fz.testBit cnt = true := by rw [hFzd]; simp [Nat.testBit_or]
      have hFzmem : ∀ r : Var, r ≠ cnt → Fz.testBit r = true →
          C.testBit r = true ∧ body.NoGrow r = true := by
        intro r hrc hr
        rw [hFzd] at hr
        simp only [Nat.testBit_or, testBit_bitOf, testBit_mdiff, Bool.or_eq_true,
          decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true'] at hr
        rcases hr with hr | hr
        · exact absurd hr.symm hrc
        · exact ⟨hr.1, Cmd.noGrow_of_ngm body r hr.2⟩
      by_cases hbit : C.testBit bnd = true
      · obtain ⟨⟨Kb, Db, hbb⟩, hc0⟩ := ih Fz
        rcases hr0 : Cmd.chk Fz body with ⟨ok1, Cb, B⟩
        have h01 : (Cmd.chk Fz body).2.1 = Cb := by rw [hr0]
        have h02 : (Cmd.chk Fz body).2.2 = B := by rw [hr0]
        set Prom := mdiff C B with hPromd
        have hbodyPair : ∃ K D : Nat, ∀ (s : State) (MF : Nat),
            (∀ r : Var, Fz.testBit r = true → (State.get s r).length ≤ MF) →
            (∀ r : Var, Cb.testBit r = true →
              (State.get (body.eval s) r).length ≤ K * (MF + 1) ^ D)
            ∧ (∀ r : Var, B.testBit r = false →
              (State.get (body.eval s) r).length
                ≤ (State.get s r).length + K * (MF + 1) ^ D) :=
          ⟨Kb, Db, fun s MF hF =>
            ⟨fun r hr => (hbb s MF hF).1 r (by rw [h01]; exact hr),
             fun r hr => (hbb s MF hF).2 r (by rw [h02]; exact hr)⟩⟩
        obtain ⟨KL, DL, hLoop⟩ :=
          Cmd.loopStep cnt bnd body C Fz B Cb hbit hFzcnt hFzmem hbodyPair
        have hPromC : ∀ r : Var, Prom.testBit r = true → C.testBit r = true := by
          intro r hr; rw [hPromd] at hr
          simp only [testBit_mdiff, Bool.and_eq_true] at hr; exact hr.1
        have hPromGrow : ∃ KG DG : Nat, ∀ (s : State) (MF : Nat),
            (∀ r : Var, Fz.testBit r = true → (State.get s r).length ≤ MF) →
            ∀ r : Var, Prom.testBit r = true →
              (State.get (body.eval s) r).length
                ≤ (State.get s r).length + KG * (MF + 1) ^ DG := by
          refine ⟨Kb, Db, fun s MF hF r hr => (hbb s MF hF).2 r ?_⟩
          rw [hPromd] at hr
          simp only [testBit_mdiff, Bool.and_eq_true, Bool.not_eq_true'] at hr
          rw [h02]; exact hr.2
        -- the exit set, in whichever shape the branch produced
        have hexit : ∀ X : Nat, (∀ r : Var, X.testBit r = true → Cb.testBit r = true) →
            ∀ r : Var,
            (mdiff C (bitOf cnt ||| NG) ||| Prom ||| (C &&& X)).testBit r = true →
            C.testBit r = true ∧ ((r ≠ cnt ∧ Fz.testBit r = true)
              ∨ Prom.testBit r = true ∨ X.testBit r = true) := by
          intro X _ r hr
          simp only [Nat.testBit_or, Nat.testBit_and, testBit_mdiff, testBit_bitOf,
            Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
            Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
          rcases hr with (hr | hr) | hr
          · refine ⟨hr.1, Or.inl ⟨fun hc => hr.2.1 hc.symm, ?_⟩⟩
            rw [hFzd]; simp [Nat.testBit_or, testBit_mdiff, hr.1, hr.2.2]
          · exact ⟨hPromC r hr, Or.inr (Or.inl hr)⟩
          · exact ⟨hr.1, Or.inr (Or.inr hr.2)⟩
        -- the cap/growth half, uniform in the branch
        have hCapGrow : ∀ X : Nat, (∀ r : Var, X.testBit r = true → Cb.testBit r = true) →
            ∀ (s : State) (MF : Nat),
            (∀ r : Var, C.testBit r = true → (State.get s r).length ≤ MF) →
            (∀ r : Var, (mdiff C (bitOf cnt ||| NG) ||| Prom ||| (C &&& X)).testBit r = true →
              (State.get ((Cmd.forBnd cnt bnd body).eval s) r).length
                ≤ (1 + KL) * (MF + 1) ^ (DL + 1))
            ∧ (∀ r : Var, B.testBit r = false →
              (State.get ((Cmd.forBnd cnt bnd body).eval s) r).length
                ≤ (State.get s r).length + (1 + KL) * (MF + 1) ^ (DL + 1)) := by
          intro X hX s MF hF
          obtain ⟨hL1, hL2, hL3⟩ := hLoop s MF hF
          have hmono : KL * (MF + 1) ^ DL ≤ (1 + KL) * (MF + 1) ^ (DL + 1) :=
            pb_mono (by omega) (by omega)
          have hexp : (1 + KL) * (MF + 1) ^ (DL + 1)
              = (MF + 1) ^ (DL + 1) + KL * (MF + 1) ^ (DL + 1) := by ring
          have hge1 : MF + 1 ≤ (MF + 1) ^ (DL + 1) := Nat.le_self_pow (by omega) _
          have hge2 : KL * (MF + 1) ^ DL ≤ KL * (MF + 1) ^ (DL + 1) :=
            pb_mono le_rfl (by omega)
          refine ⟨fun r hr => ?_, fun r hr => ?_⟩
          · obtain ⟨hrC, hcase⟩ := hexit X hX r hr
            rcases hcase with ⟨hrc, hrz⟩ | hrp | hrx
            · have := hL1 r hrc hrz; omega
            · have hb0 : B.testBit r = false := by
                rw [hPromd] at hrp
                simp only [testBit_mdiff, Bool.and_eq_true, Bool.not_eq_true'] at hrp
                exact hrp.2
              have := hL2 r hb0
              have := hF r hrC
              omega
            · have := hL3 r hrC (hX r hrx); omega
          · have := hL2 r hr; omega
        by_cases hok1 : ok1 = true
        · have hchk : (Cmd.forBnd cnt bnd body).chk C
              = (true, mdiff C (bitOf cnt ||| NG) ||| Prom ||| (C &&& Cb), B) := by
            simp [Cmd.chk, hbit, ← hFzd, ← hNG, hr0, hok1, ← hPromd]
          refine ⟨⟨1 + KL, DL + 1, fun s MF hF => ?_⟩, fun _ => ?_⟩
          · rw [hchk]; exact hCapGrow Cb (fun _ h => h) s MF hF
          · rw [hchk]
            have hbodyCap : body.CapCost (Fz ||| Prom) Cb := by
              have := hc0 (by rw [hr0]; exact hok1)
              rw [h01] at this
              exact this.mono (fun r hr => by simp [Nat.testBit_or, hr]) (fun r hr => hr)
            exact Cmd.capCost_forBnd cnt bnd body C Fz Prom Cb _ hbit hFzcnt hFzmem
              hPromC hPromGrow hbodyCap (fun r hr => hexit Cb (fun _ h => h) r hr)
        · simp only [Bool.not_eq_true] at hok1
          obtain ⟨-, hc1⟩ := ih (Fz ||| Prom)
          rcases hr1 : Cmd.chk (Fz ||| Prom) body with ⟨ok2, Cb2, B2⟩
          have h11 : (Cmd.chk (Fz ||| Prom) body).2.1 = Cb2 := by rw [hr1]
          have hchk : (Cmd.forBnd cnt bnd body).chk C
              = (ok2, mdiff C (bitOf cnt ||| NG) ||| Prom ||| (C &&& (Cb &&& Cb2)), B) := by
            simp only [Cmd.chk, hbit, ← hFzd, ← hNG, hr0, hok1, ← hPromd, hr1,
              if_true, Bool.false_eq_true, if_false]
            simp [Nat.and_assoc]
          refine ⟨⟨1 + KL, DL + 1, fun s MF hF => ?_⟩, fun hok => ?_⟩
          · rw [hchk]
            have := hCapGrow (Cb &&& Cb2)
              (fun r hr => by simp only [Nat.testBit_and, Bool.and_eq_true] at hr; exact hr.1)
              s MF hF
            simpa [Nat.and_assoc] using this
          · rw [hchk] at hok ⊢
            have hbodyCap : body.CapCost (Fz ||| Prom) Cb2 := by
              have := hc1 (by rw [hr1]; exact hok)
              rwa [h11] at this
            refine Cmd.capCost_forBnd cnt bnd body C Fz Prom Cb2 _ hbit hFzcnt hFzmem
              hPromC hPromGrow hbodyCap (fun r hr => ?_)
            obtain ⟨hrC, hcase⟩ := hexit (Cb &&& Cb2)
              (fun r hr => by simp only [Nat.testBit_and, Bool.and_eq_true] at hr; exact hr.1)
              r (by simpa [Nat.and_assoc] using hr)
            refine ⟨hrC, ?_⟩
            rcases hcase with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · simp only [Nat.testBit_and, Bool.and_eq_true] at h
              exact Or.inr (Or.inr h.2)
      · simp only [Bool.not_eq_true] at hbit
        have hchk : (Cmd.forBnd cnt bnd body).chk C
            = (false, mdiff C (bitOf cnt ||| NG), bitOf cnt ||| NG) := by
          simp [Cmd.chk, hbit, ← hNG]
        refine ⟨⟨1, 1, fun s MF hF => ?_⟩, fun hok => by rw [hchk] at hok; simp at hok⟩
        rw [hchk]
        have hng : ∀ r : Var, (bitOf cnt ||| NG).testBit r = false →
            (Cmd.forBnd cnt bnd body).NoGrow r = true := by
          intro r hr
          simp only [Nat.testBit_or, testBit_bitOf, Bool.or_eq_false_iff,
            decide_eq_false_iff_not] at hr
          simp [Cmd.NoGrow, bne_iff_ne, hr.1, Cmd.noGrow_of_ngm body r hr.2]
        refine ⟨fun r hr => ?_, fun r hr => ?_⟩
        · simp only [testBit_mdiff, Bool.and_eq_true, Bool.not_eq_true'] at hr
          have := Cmd.noGrow_sound _ r (hng r hr.2) s
          have := hF r hr.1
          have h1 : (1 : Nat) ≤ (MF + 1) ^ 1 := pb_one 1 MF
          have h2 : (MF + 1) ^ 1 = MF + 1 := pow_one _
          omega
        · have := Cmd.noGrow_sound _ r (hng r hr) s
          have h2 : (1 : Nat) * (MF + 1) ^ 1 = MF + 1 := by rw [pow_one]; ring
          omega

/-! ## Part 5 — the bridge to a witness's `cost_le`

At a program's *entry* every register is bounded by the state's size, so both
caps may be taken to be `State.size s`. -/

theorem Cmd.CapCost.cost_le_size {c : Cmd} {F F' : Nat} (h : c.CapCost F F') :
    ∃ K D : Nat, ∀ (s : State) (n : Nat),
      State.size s ≤ n → c.cost s ≤ K * (n + 1) ^ (D + 1) := by
  obtain ⟨K, D, hb⟩ := h
  refine ⟨K, D, fun s n hn => ?_⟩
  have hcap : ∀ r : Var, (State.get s r).length ≤ n :=
    fun r => le_trans (State.get_length_le_size s r) hn
  have := (hb s n n (fun r _ => hcap r) hcap).1
  have he : K * (n + 1) ^ D * (n + 1) = K * (n + 1) ^ (D + 1) := by ring
  omega

/-- **The one-liner.** `Cmd.costLeSize_of_chk c F (by decide)` turns a successful
analysis into the cost bound a free witness needs. `F` is the mask of registers
the program may touch — at entry they are all bounded by the input size, so
`2 ^ regBound - 1` is the right choice. -/
theorem Cmd.costLeSize_of_chk (c : Cmd) (F : Nat) (h : (c.chk F).1 = true) :
    ∃ K D : Nat, ∀ (s : State) (n : Nat),
      State.size s ≤ n → c.cost s ≤ K * (n + 1) ^ (D + 1) :=
  ((Cmd.chk_sound c F).2 h).cost_le_size

end Complexity.Lang
