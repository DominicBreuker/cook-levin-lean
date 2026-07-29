import Complexity.Lang.CostPoly
import Mathlib.Tactic

set_option autoImplicit false

/-! # `Cmd.CapCost` — a two-cap polynomial cost bound that survives a loop

`Lang/CostPoly.lean` gives `Cmd.PolyCost`, whose cap is a single `M` over
`c.costReads`. That cap **cannot survive a loop**: after one iteration the
body's outputs are bounded by `poly(M)`, so the next iteration's cap is
`poly(poly(M))`, and `m` iterations give a tower. `Cmd.polyCost_forBnd` sidesteps
this by *forbidding* the body to write what it cost-reads — which is exactly the
4% of `S1Program.s1Program`'s loops that the residual consists of.

This file replaces the single cap by **two**:

* `MF` bounds a set `F` of registers that are **frozen for the whole loop** (the
  body never writes them; the loop counter joins them because `forBnd` re-sets it
  to `1^i` with `i < trips`);
* `N` bounds *every* register.

and states three conclusions:

```
c.cost s              ≤ K·(MF+1)^D · (N+1)        -- cost MAY be linear in N
∀ r, |c.eval s @ r|   ≤ N + K·(MF+1)^D            -- growth may NOT depend on N
∀ r ∈ F', |c.eval s @ r| ≤ MF + K·(MF+1)^D        -- and F' stays capped
```

The loop rule is then non-compounding: with `bnd ∈ F` the trip count is `≤ MF`,
each iteration adds `≤ P := K·(MF+1)^D` to the global cap, so `N_m ≤ N + MF·P` —
polynomial, not a tower.

Two payoffs over `PolyCost`:

* **FINDING X is free.** `Cmd.op (.copy EOUT_C EOUT_C)` — the `ifBit` else-branch
  no-op used on the *output* register throughout `S1CardEmit`/`S1Prelude` — costs
  `|EOUT_C| + 1 ≤ N + 1`. Under a `costReads`-only cap that is fatal; here the
  `(N+1)` factor pays for it and no pinned `_run` lemma has to be re-opened.
* **An accumulator may bound an inner loop.** `S1CardEmit.CH` is advanced by
  `tallyReg EK1 CS1 CH` and then used as `emitId`'s source; `S1Emit.EC` and every
  drained cursor are the same shape. `Cmd.GrowOk` certifies such a register's
  growth *additive against the strictly frozen set*, so it is `≤ MF + m·poly(MF)`
  at every iteration — a cap the main rule may then spend. Round 0 buys the
  invariant, round 1 spends it; both runs are over the same body and the same
  states, so nothing is circular.

## Layout

1. `Cmd.NoGrow` — "this command never inflates register `r`", an *idempotent*
   bound (`≤ max |r| 1`) so a `NoGrow` body may be iterated any number of times.
   Covers the drained cursor `forBnd idx SCAN (… tail SCAN SCAN …)`, whose own
   bound register is the one being consumed.
2. `Cmd.GrowOk` — "this command grows `r` by at most `poly(MF)`", per register.
3. `Cmd.CapCost` — the predicate above, with `op` / `seq` / `ifBit` / `forBnd`
   rules.
4. `Cmd.capChk` — the decidable forward analysis, and `Cmd.capCost_of_capChk`.
5. `Cmd.polyCost_of_capCost` — the bridge back to `Lang/CostPoly.lean`.
-/

namespace Complexity.Lang

/-! ## Part 1 — `NoGrow`

`c.NoGrow r` certifies `|c.eval s @ r| ≤ max |s@r| 1`. The bound is idempotent,
which is the whole point: it survives iteration without a trip-count hypothesis,
so a loop whose *bound register* is uncapped is still harmless for `r`. -/

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

/-! ## Part 2 — `GrowOk`

`c.GrowOk r F` certifies `|c.eval s @ r| ≤ |s@r| + poly(MF)` whenever `F`'s
registers are `≤ MF`. `F` is always a set the command **never writes**, so it is
genuinely frozen for the whole run — that is the `hfr` hypothesis below, and
every call site discharges it by construction.

The check is *total*: a loop contributes nothing to `r`'s growth unless it
writes `r`, so `GrowOk` can certify a register without first knowing that the
loops around it are analysable. That independence is what breaks the
chicken-and-egg in `Cmd.promote`. -/

def Op.GrowOk (o : Op) (r : Var) (F : List Var) : Bool :=
  match o with
  | .clear _ => true
  | .appendOne _ => true
  | .appendZero _ => true
  | .head _ _ => true
  | .eqBit _ _ _ => true
  | .nonEmpty _ _ => true
  | .copy dst src => dst != r || src == r || F.contains src
  | .tail dst src => dst != r || src == r || F.contains src
  | .concat dst a b =>
      dst != r || (a == dst && F.contains b) || (b == dst && F.contains a)
        || (F.contains a && F.contains b)

/-- The frozen set a loop body inherits: the ambient frozen registers the body
never writes, plus the loop's own counter — `forBnd` re-sets it to `1^i` with
`i < trips`, so it is capped by the trip count (and it is dropped again if the
body writes it). -/
def Cmd.freezeFor (F : List Var) (cnt : Var) (body : Cmd) : List Var :=
  (cnt :: F).filter (fun v => !body.writes.contains v)

theorem Cmd.mem_freezeFor {F : List Var} {cnt : Var} {body : Cmd} {v : Var}
    (h : v ∈ Cmd.freezeFor F cnt body) : (v = cnt ∨ v ∈ F) ∧ v ∉ body.writes := by
  simp only [Cmd.freezeFor, List.mem_filter, List.mem_cons] at h
  exact ⟨h.1, by have := h.2; simp at this; exact this⟩

def Cmd.GrowOk : Cmd → Var → List Var → Bool
  | .op o, r, F => o.GrowOk r F
  | .seq a b, r, F => a.GrowOk r F && b.GrowOk r F
  | .ifBit _ a b, r, F => a.GrowOk r F && b.GrowOk r F
  | .forBnd cnt bnd body, r, F =>
      !(cnt :: body.writes).contains r
        || (Cmd.forBnd cnt bnd body).NoGrow r
        || (F.contains bnd && body.GrowOk r (Cmd.freezeFor F cnt body))

theorem Op.growOk_sound (o : Op) (r : Var) (F : List Var) (h : o.GrowOk r F = true)
    (s : State) (MF : Nat) (hF : ∀ v ∈ F, (State.get s v).length ≤ MF) :
    (State.get (Op.eval o s) r).length ≤ (State.get s r).length + 2 * (MF + 1) := by
  have hmem : ∀ v : Var, F.contains v = true → (State.get s v).length ≤ MF := by
    intro v hv; exact hF v (by simpa using hv)
  cases o with
  | clear dst =>
      by_cases hr : r = dst
      · subst hr; simp [Op.eval, State.get_set_eq]
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | appendOne dst =>
      by_cases hr : r = dst
      · subst hr; simp only [Op.eval, State.get_set_eq, List.length_append]; simp; omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | appendZero dst =>
      by_cases hr : r = dst
      · subst hr; simp only [Op.eval, State.get_set_eq, List.length_append]; simp; omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | head dst src =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq]
        rcases State.get s src with _ | ⟨x, xs⟩ <;> simp <;> omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | eqBit dst s1 s2 =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq]
        by_cases hh : State.get s s1 = State.get s s2 <;> simp [hh] <;> omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | nonEmpty dst src =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq]
        by_cases hh : (State.get s src).isEmpty <;> simp [hh] <;> omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | copy dst src =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.GrowOk, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
          beq_iff_eq] at h
        simp only [Op.eval, State.get_set_eq]
        rcases h with hs | hs
        · subst hs; omega
        · have := hmem src hs; omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | tail dst src =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.GrowOk, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
          beq_iff_eq] at h
        simp only [Op.eval, State.get_set_eq, List.length_tail]
        rcases h with hs | hs
        · subst hs; omega
        · have := hmem src hs; omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | concat dst a b =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.GrowOk, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
          Bool.and_eq_true, beq_iff_eq] at h
        simp only [Op.eval, State.get_set_eq, List.length_append]
        rcases h with (⟨ha, hb⟩ | ⟨hb, ha⟩) | ⟨ha, hb⟩
        · subst ha; have := hmem b hb; omega
        · subst hb; have := hmem a ha; omega
        · have h1 := hmem a ha; have h2 := hmem b hb; omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega

/-- **`GrowOk` is sound.** `hfr` says `F` is frozen for `c`; every call site
builds `F` by `Cmd.freezeFor`, which enforces it. -/
theorem Cmd.growOk_sound : ∀ (c : Cmd) (r : Var) (F : List Var),
    (∀ v ∈ F, v ∉ c.writes) → c.GrowOk r F = true →
    ∃ KG DG : Nat, ∀ (s : State) (MF : Nat),
      (∀ v ∈ F, (State.get s v).length ≤ MF) →
      (State.get (c.eval s) r).length ≤ (State.get s r).length + KG * (MF + 1) ^ DG := by
  intro c
  induction c with
  | op o =>
      intro r F _ h
      exact ⟨2, 1, fun s MF hF => by
        rw [Cmd.eval_op, pow_one]; exact Op.growOk_sound o r F h s MF hF⟩
  | seq c1 c2 ih1 ih2 =>
      intro r F hfr h
      simp only [Cmd.GrowOk, Bool.and_eq_true] at h
      have hfr1 : ∀ v ∈ F, v ∉ c1.writes := fun v hv hw =>
        hfr v hv (by simp only [Cmd.writes]; exact List.mem_append_left _ hw)
      have hfr2 : ∀ v ∈ F, v ∉ c2.writes := fun v hv hw =>
        hfr v hv (by simp only [Cmd.writes]; exact List.mem_append_right _ hw)
      obtain ⟨K1, D1, hb1⟩ := ih1 r F hfr1 h.1
      obtain ⟨K2, D2, hb2⟩ := ih2 r F hfr2 h.2
      refine ⟨K1 + K2, max D1 D2, fun s MF hF => ?_⟩
      have hkeep : ∀ v ∈ F, (State.get (c1.eval s) v).length ≤ MF := by
        intro v hv
        rw [Cmd.eval_get_of_not_writes c1 s v (hfr1 v hv)]; exact hF v hv
      have e1 := hb1 s MF hF
      have e2 := hb2 (c1.eval s) MF hkeep
      have p1 : K1 * (MF + 1) ^ D1 ≤ K1 * (MF + 1) ^ max D1 D2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      have p2 : K2 * (MF + 1) ^ D2 ≤ K2 * (MF + 1) ^ max D1 D2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      have hsum : (K1 + K2) * (MF + 1) ^ max D1 D2
          = K1 * (MF + 1) ^ max D1 D2 + K2 * (MF + 1) ^ max D1 D2 := by ring
      rw [Cmd.eval_seq]
      omega
  | ifBit t cT cE ihT ihE =>
      intro r F hfr h
      simp only [Cmd.GrowOk, Bool.and_eq_true] at h
      have hfrT : ∀ v ∈ F, v ∉ cT.writes := fun v hv hw =>
        hfr v hv (by simp only [Cmd.writes]; exact List.mem_append_left _ hw)
      have hfrE : ∀ v ∈ F, v ∉ cE.writes := fun v hv hw =>
        hfr v hv (by simp only [Cmd.writes]; exact List.mem_append_right _ hw)
      obtain ⟨KT, DT, hbT⟩ := ihT r F hfrT h.1
      obtain ⟨KE, DE, hbE⟩ := ihE r F hfrE h.2
      refine ⟨KT + KE, max DT DE, fun s MF hF => ?_⟩
      have pT : KT * (MF + 1) ^ DT ≤ KT * (MF + 1) ^ max DT DE :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      have pE : KE * (MF + 1) ^ DE ≤ KE * (MF + 1) ^ max DT DE :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      have hsum : (KT + KE) * (MF + 1) ^ max DT DE
          = KT * (MF + 1) ^ max DT DE + KE * (MF + 1) ^ max DT DE := by ring
      by_cases hb : State.get s t = [1]
      · rw [Cmd.eval_ifBit_true _ _ _ _ hb]; have := hbT s MF hF; omega
      · rw [Cmd.eval_ifBit_false _ _ _ _ hb]; have := hbE s MF hF; omega
  | forBnd cnt bnd body ih =>
      intro r F hfr h
      simp only [Cmd.GrowOk, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with (hskip | hng) | ⟨hbnd, hgo⟩
      · -- the loop never writes `r`
        have hnot : r ∉ (Cmd.forBnd cnt bnd body).writes := by
          simp only [Cmd.writes]; simpa using hskip
        exact ⟨0, 0, fun s MF _ => by
          rw [Cmd.eval_get_of_not_writes _ s r hnot]; omega⟩
      · -- the loop never inflates `r`
        exact ⟨1, 0, fun s MF _ => by
          have := Cmd.noGrow_sound _ r hng s
          simp only [pow_zero, mul_one]
          omega⟩
      · -- the general case: bounded trips, additive per-iteration growth
        set Fz := Cmd.freezeFor F cnt body with hFz
        have hfrz : ∀ v ∈ Fz, v ∉ body.writes := fun v hv => (Cmd.mem_freezeFor hv).2
        obtain ⟨KG, DG, hbb⟩ := ih r Fz hfrz hgo
        refine ⟨KG + 1, max (DG + 1) 2, fun s MF hF => ?_⟩
        have hmM : (State.get s bnd).length ≤ MF := hF bnd (by simpa using hbnd)
        set m := (State.get s bnd).length with hm
        set G := KG * (MF + 1) ^ DG with hG
        set Gp := G + MF + 1 with hGp
        have hfrF : ∀ v ∈ F, v ≠ cnt ∧ v ∉ body.writes := by
          intro v hv
          have := hfr v hv
          simp only [Cmd.writes, List.mem_cons] at this
          exact ⟨fun hc => this (Or.inl hc), fun hw => this (Or.inr hw)⟩
        rw [Cmd.eval_forBnd]
        have key := Cmd.foldlState_range_induct body cnt m s
          (fun i st => (∀ v ∈ F, State.get st v = State.get s v)
            ∧ (State.get st r).length ≤ (State.get s r).length + i * Gp)
          ⟨fun _ _ => rfl, by simp⟩ (fun i st hi hM => ?_)
        · exact le_trans key.2 (by
            have h1 : m * Gp ≤ (MF + 1) * Gp := Nat.mul_le_mul_right _ (by omega)
            have h2 : (MF + 1) * Gp = (MF + 1) * G + (MF + 1) * (MF + 1) := by
              rw [hGp]; ring
            have h3 : (MF + 1) * G = KG * (MF + 1) ^ (DG + 1) := by rw [hG]; ring
            have h4 : (MF + 1) * (MF + 1) = (MF + 1) ^ 2 := by ring
            have h5 : KG * (MF + 1) ^ (DG + 1) ≤ KG * (MF + 1) ^ max (DG + 1) 2 :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
            have h6 : (MF + 1) ^ 2 ≤ (MF + 1) ^ max (DG + 1) 2 :=
              Nat.pow_le_pow_right (by omega) (by omega)
            have h7 : (KG + 1) * (MF + 1) ^ max (DG + 1) 2
                = KG * (MF + 1) ^ max (DG + 1) 2 + (MF + 1) ^ max (DG + 1) 2 := by ring
            omega)
        · obtain ⟨hEq, hLen⟩ := hM
          set u := st.set cnt (List.replicate i 1) with hu
          have hcap : ∀ v ∈ Fz, (State.get u v).length ≤ MF := by
            intro v hv
            obtain ⟨hor, _⟩ := Cmd.mem_freezeFor hv
            rcases hor with hc | hvF
            · subst hc; rw [hu, State.get_set_eq, List.length_replicate]; omega
            · rw [hu, State.get_set_ne _ _ _ _ (hfrF v hvF).1, hEq v hvF]
              exact hF v hvF
          have hgrow := hbb u MF hcap
          have hur : (State.get u r).length ≤ (State.get st r).length + MF := by
            by_cases hrc : r = cnt
            · rw [hu, hrc, State.get_set_eq, List.length_replicate]; omega
            · rw [hu, State.get_set_ne _ _ _ _ hrc]; omega
          refine ⟨fun v hv => ?_, ?_⟩
          · rw [Cmd.eval_get_of_not_writes body u v (hfrF v hv).2, hu,
              State.get_set_ne _ _ _ _ (hfrF v hv).1]
            exact hEq v hv
          · have harith : (i + 1) * Gp = i * Gp + Gp := by ring
            omega

/-- The list form: one pair of constants for a whole list of registers. The
`forBnd` rule needs a *uniform* promotion budget, and `Cmd.growOk_sound`'s
constants depend on which branch each register takes. -/
theorem Cmd.growOk_sound_list (c : Cmd) (F : List Var) (hfr : ∀ v ∈ F, v ∉ c.writes) :
    ∀ L : List Var, (∀ r ∈ L, c.GrowOk r F = true) →
    ∃ KG DG : Nat, ∀ (s : State) (MF : Nat),
      (∀ v ∈ F, (State.get s v).length ≤ MF) → ∀ r ∈ L,
      (State.get (c.eval s) r).length ≤ (State.get s r).length + KG * (MF + 1) ^ DG := by
  intro L
  induction L with
  | nil => exact fun _ => ⟨0, 0, fun _ _ _ r hr => absurd hr (by simp)⟩
  | cons a L ih =>
      intro h
      obtain ⟨K1, D1, hb1⟩ := Cmd.growOk_sound c a F hfr (h a (by simp))
      obtain ⟨K2, D2, hb2⟩ := ih (fun r hr => h r (by simp [hr]))
      refine ⟨K1 + K2, max D1 D2, fun s MF hF r hr => ?_⟩
      have p1 : K1 * (MF + 1) ^ D1 ≤ (K1 + K2) * (MF + 1) ^ max D1 D2 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      have p2 : K2 * (MF + 1) ^ D2 ≤ (K1 + K2) * (MF + 1) ^ max D1 D2 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      rcases List.mem_cons.1 hr with rfl | hr'
      · have := hb1 s MF hF; omega
      · have := hb2 s MF hF r hr'; omega

/-! ## Part 3 — `CapCost`, the two-cap predicate -/

/-- **The two-cap polynomial cost bound.** `F` is capped by `MF`, everything by
`N`. The cost may be linear in `N` (that is what pays for `copy r r` on a large
output register — FINDING X); the *growth* may not, which is what keeps a loop
from compounding. `F'` is the set still capped after the command. -/
def Cmd.CapCost (c : Cmd) (F F' : List Var) : Prop :=
  ∃ K D : Nat, ∀ (s : State) (MF N : Nat),
    (∀ r ∈ F, (State.get s r).length ≤ MF) →
    (∀ r, (State.get s r).length ≤ N) →
      c.cost s ≤ K * (MF + 1) ^ D * (N + 1)
    ∧ (∀ r, (State.get (c.eval s) r).length ≤ N + K * (MF + 1) ^ D)
    ∧ (∀ r ∈ F', (State.get (c.eval s) r).length ≤ MF + K * (MF + 1) ^ D)

/-! ### Budget algebra

Every rule below is an exercise in `K·(MF+1)^D` bookkeeping; these four facts do
all of it. -/

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

/-- `N + K·(MF+1)^D + 1 ≤ (N+1)·(K+1)·(MF+1)^D` — pushing an additive growth
budget into the `(N+1)` factor. -/
private theorem pb_widen (K D MF N : Nat) :
    N + K * (MF + 1) ^ D + 1 ≤ (N + 1) * ((K + 1) * (MF + 1) ^ D) := by
  have h1 : 1 ≤ (MF + 1) ^ D := pb_one D MF
  have h2 : (N + 1) * ((K + 1) * (MF + 1) ^ D)
      = (N + 1) * (K * (MF + 1) ^ D) + (N + 1) * (MF + 1) ^ D := by ring
  have h3 : K * (MF + 1) ^ D ≤ (N + 1) * (K * (MF + 1) ^ D) := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : N + 1 ≤ (N + 1) * (MF + 1) ^ D := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The whole `seq` budget algebra in one place: the composite budget
`1 + B1 + B2·(B1+1)` (where `B1` is the left factor's and `B2` the right
factor's, taken at the *widened* cap `MF + B1`) is again of the form
`K·(MF+1)^D`. -/
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

theorem Cmd.CapCost.seq {c1 c2 : Cmd} {F F1 F2 : List Var}
    (h1 : c1.CapCost F F1) (h2 : c2.CapCost F1 F2) : (c1 ;; c2).CapCost F F2 := by
  obtain ⟨K1, D1, hb1⟩ := h1
  obtain ⟨K2, D2, hb2⟩ := h2
  refine ⟨1 + K1 + K2 * (K1 + 1) ^ (D2 + 1), D1 + (D1 + 1) * D2, fun s MF N hF hN => ?_⟩
  obtain ⟨hc1, hg1, hf1⟩ := hb1 s MF N hF hN
  obtain ⟨hc2, hg2, hf2⟩ := hb2 (c1.eval s) (MF + K1 * (MF + 1) ^ D1)
    (N + K1 * (MF + 1) ^ D1) hf1 hg1
  -- `B1` the left budget, `B2` the right budget at the widened cap
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
  · -- cost
    rw [Cmd.cost_seq]
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
  · -- global growth
    rw [Cmd.eval_seq]
    have := hg2 r
    omega
  · -- the capped exit set
    rw [Cmd.eval_seq]
    have := hf2 r hr
    omega


theorem Cmd.CapCost.ifBit {t : Var} {cT cE : Cmd} {F F1 F2 F' : List Var}
    (hT : cT.CapCost F F1) (hE : cE.CapCost F F2)
    (hsub : ∀ r ∈ F', r ∈ F1 ∧ r ∈ F2) : (Cmd.ifBit t cT cE).CapCost F F' := by
  obtain ⟨KT, DT, hbT⟩ := hT
  obtain ⟨KE, DE, hbE⟩ := hE
  refine ⟨1 + KT + KE, max DT DE, fun s MF N hF hN => ?_⟩
  set D := max DT DE with hD
  have hmT : KT * (MF + 1) ^ DT ≤ KT * (MF + 1) ^ D :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hmE : KE * (MF + 1) ^ DE ≤ KE * (MF + 1) ^ D :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hone : 1 ≤ (MF + 1) ^ D := pb_one D MF
  have hexp : (1 + KT + KE) * (MF + 1) ^ D
      = (MF + 1) ^ D + KT * (MF + 1) ^ D + KE * (MF + 1) ^ D := by ring
  have hmul : ∀ a b : Nat, a ≤ b → a * (N + 1) ≤ b * (N + 1) :=
    fun a b h => Nat.mul_le_mul_right _ h
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

/-! ### The `op` rule

The only op that can fail is `concat`: it is the one whose *output length* is
not bounded by its destination's old length plus a capped amount unless one of
its sources is capped. Everything else — including `copy dst dst` on a huge
output register — is paid for by the `(N+1)` factor. -/

def Op.capChk (F : List Var) : Op → Option (List Var)
  | .clear dst => some (dst :: F)
  | .appendOne _ => some F
  | .appendZero _ => some F
  | .head dst _ => some (dst :: F)
  | .eqBit dst _ _ => some (dst :: F)
  | .nonEmpty dst _ => some (dst :: F)
  | .copy dst src => some (if F.contains src then dst :: F else F.filter (fun v => v != dst))
  | .tail dst src =>
      some (if F.contains src then dst :: F
            else if src == dst then F else F.filter (fun v => v != dst))
  | .concat dst a b =>
      if F.contains a && F.contains b then some (dst :: F)
      else if F.contains a || F.contains b then some (F.filter (fun v => v != dst))
      else none

theorem Cmd.capCost_op (o : Op) (F F' : List Var) (h : Op.capChk F o = some F') :
    (Cmd.op o).CapCost F F' := by
  refine ⟨5, 1, fun s MF N hF hN => ?_⟩
  have hmem : ∀ v : Var, F.contains v = true → (State.get s v).length ≤ MF :=
    fun v hv => hF v (by simpa using hv)
  have hfil : ∀ (dst v : Var), v ∈ F.filter (fun w => w != dst) → v ∈ F ∧ v ≠ dst := by
    intro dst v hv
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hv
    exact hv
  have hcons : ∀ (dst v : Var), v ∈ dst :: F → v ≠ dst → v ∈ F := by
    intro dst v hv hvd
    rcases List.mem_cons.1 hv with rfl | hh
    · exact absurd rfl hvd
    · exact hh
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
  have hpow1 : (MF + 1) ^ 1 = MF + 1 := pow_one _
  rw [Cmd.cost_op, Cmd.eval_op]
  cases o with
  | clear dst =>
      simp only [Op.capChk, Option.some.injEq] at h; subst h
      have hd : (State.get (Op.eval (.clear dst) s) dst).length = 0 := by
        simp [Op.eval, State.get_set_eq]
      refine ⟨by simpa only [Op.cost] using hone, fun r => ?_, fun r hr => ?_⟩
      · by_cases hr' : r = dst
        · subst hr'; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
      · by_cases hr' : r = dst
        · subst hr'; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
          have := hF r (hcons dst r hr hr'); omega
  | appendOne dst =>
      simp only [Op.capChk, Option.some.injEq] at h; subst h
      have hd : ∀ M : Nat, (State.get s dst).length ≤ M →
          (State.get (Op.eval (.appendOne dst) s) dst).length ≤ M + 1 := by
        intro M hM
        simp only [Op.eval, State.get_set_eq, List.length_append, List.length_cons,
          List.length_nil]
        omega
      refine ⟨by simpa only [Op.cost] using hone, fun r => ?_, fun r hr => ?_⟩
      · by_cases hr' : r = dst
        · subst hr'; have := hd N (hN r); omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
      · by_cases hr' : r = dst
        · subst hr'; have := hd MF (hF r hr); omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hF r hr; omega
  | appendZero dst =>
      simp only [Op.capChk, Option.some.injEq] at h; subst h
      have hd : ∀ M : Nat, (State.get s dst).length ≤ M →
          (State.get (Op.eval (.appendZero dst) s) dst).length ≤ M + 1 := by
        intro M hM
        simp only [Op.eval, State.get_set_eq, List.length_append, List.length_cons,
          List.length_nil]
        omega
      refine ⟨by simpa only [Op.cost] using hone, fun r => ?_, fun r hr => ?_⟩
      · by_cases hr' : r = dst
        · subst hr'; have := hd N (hN r); omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
      · by_cases hr' : r = dst
        · subst hr'; have := hd MF (hF r hr); omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hF r hr; omega
  | head dst src =>
      simp only [Op.capChk, Option.some.injEq] at h; subst h
      have hd : (State.get (Op.eval (.head dst src) s) dst).length ≤ 1 := by
        simp only [Op.eval, State.get_set_eq]
        rcases State.get s src with _ | ⟨x, xs⟩ <;> simp
      refine ⟨by simpa only [Op.cost] using hone, fun r => ?_, fun r hr => ?_⟩
      · by_cases hr' : r = dst
        · subst hr'; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
      · by_cases hr' : r = dst
        · subst hr'; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
          have := hF r (hcons dst r hr hr'); omega
  | eqBit dst s1 s2 =>
      simp only [Op.capChk, Option.some.injEq] at h; subst h
      have hd : (State.get (Op.eval (.eqBit dst s1 s2) s) dst).length ≤ 1 := by
        simp only [Op.eval, State.get_set_eq]
        by_cases hh : State.get s s1 = State.get s s2 <;> simp [hh]
      have hc : Op.cost (.eqBit dst s1 s2) s ≤ 5 * (MF + 1) ^ 1 * (N + 1) := by
        have h1 := hN s1; have h2 := hN s2
        have := hlin2 (State.get s s1).length (State.get s s2).length h1 h2
        simp only [Op.cost]; omega
      refine ⟨hc, fun r => ?_, fun r hr => ?_⟩
      · by_cases hr' : r = dst
        · subst hr'; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
      · by_cases hr' : r = dst
        · subst hr'; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
          have := hF r (hcons dst r hr hr'); omega
  | nonEmpty dst src =>
      simp only [Op.capChk, Option.some.injEq] at h; subst h
      have hd : (State.get (Op.eval (.nonEmpty dst src) s) dst).length ≤ 1 := by
        simp only [Op.eval, State.get_set_eq]
        by_cases hh : (State.get s src).isEmpty <;> simp [hh]
      refine ⟨by simpa only [Op.cost] using hone, fun r => ?_, fun r hr => ?_⟩
      · by_cases hr' : r = dst
        · subst hr'; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
      · by_cases hr' : r = dst
        · subst hr'; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
          have := hF r (hcons dst r hr hr'); omega
  | copy dst src =>
      have hc : Op.cost (.copy dst src) s ≤ 5 * (MF + 1) ^ 1 * (N + 1) := by
        have := hlin (State.get s src).length (hN src)
        simp only [Op.cost]; omega
      have hglob : ∀ r, (State.get (Op.eval (.copy dst src) s) r).length
          ≤ N + 5 * (MF + 1) ^ 1 := by
        intro r
        by_cases hr' : r = dst
        · subst hr'; simp only [Op.eval, State.get_set_eq]; have := hN src; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
      rw [Op.capChk] at h
      split at h
      · rename_i hsrc
        simp only [Option.some.injEq] at h; subst h
        refine ⟨hc, hglob, fun r hr => ?_⟩
        by_cases hr' : r = dst
        · subst hr'; simp only [Op.eval, State.get_set_eq]
          have := hmem src hsrc; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
          have := hF r (hcons dst r hr hr'); omega
      · simp only [Option.some.injEq] at h; subst h
        refine ⟨hc, hglob, fun r hr => ?_⟩
        obtain ⟨hrF, hrd⟩ := hfil dst r hr
        simp only [Op.eval, State.get_set_ne _ _ _ _ hrd]
        have := hF r hrF; omega
  | tail dst src =>
      have hc : Op.cost (.tail dst src) s ≤ 5 * (MF + 1) ^ 1 * (N + 1) := by
        have := hlin (State.get s src).length (hN src)
        simp only [Op.cost]; omega
      have hglob : ∀ r, (State.get (Op.eval (.tail dst src) s) r).length
          ≤ N + 5 * (MF + 1) ^ 1 := by
        intro r
        by_cases hr' : r = dst
        · subst hr'; simp only [Op.eval, State.get_set_eq, List.length_tail]
          have := hN src; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
      rw [Op.capChk] at h
      split at h
      · rename_i hsrc
        simp only [Option.some.injEq] at h; subst h
        refine ⟨hc, hglob, fun r hr => ?_⟩
        by_cases hr' : r = dst
        · subst hr'; simp only [Op.eval, State.get_set_eq, List.length_tail]
          have := hmem src hsrc; omega
        · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
          have := hF r (hcons dst r hr hr'); omega
      · split at h
        · rename_i hsd
          simp only [beq_iff_eq] at hsd
          simp only [Option.some.injEq] at h; subst h
          refine ⟨hc, hglob, fun r hr => ?_⟩
          by_cases hr' : r = dst
          · subst hr'
            simp only [Op.eval, State.get_set_eq, List.length_tail]
            have := hF r hr; rw [hsd]; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
            have := hF r hr; omega
        · simp only [Option.some.injEq] at h; subst h
          refine ⟨hc, hglob, fun r hr => ?_⟩
          obtain ⟨hrF, hrd⟩ := hfil dst r hr
          simp only [Op.eval, State.get_set_ne _ _ _ _ hrd]
          have := hF r hrF; omega
  | concat dst a b =>
      have hc : Op.cost (.concat dst a b) s ≤ 5 * (MF + 1) ^ 1 * (N + 1) := by
        have := hlin2 (State.get s a).length (State.get s b).length (hN a) (hN b)
        simp only [Op.cost]; omega
      rw [Op.capChk] at h
      split at h
      · rename_i hboth
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true] at hboth
        have ha := hmem a hboth.1
        have hb := hmem b hboth.2
        refine ⟨hc, fun r => ?_, fun r hr => ?_⟩
        · by_cases hr' : r = dst
          · subst hr'; simp only [Op.eval, State.get_set_eq, List.length_append]; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
        · by_cases hr' : r = dst
          · subst hr'; simp only [Op.eval, State.get_set_eq, List.length_append]; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']
            have := hF r (hcons dst r hr hr'); omega
      · split at h
        · rename_i hone'
          simp only [Option.some.injEq] at h
          subst h
          have hab : (State.get s a).length + (State.get s b).length ≤ N + MF := by
            simp only [Bool.or_eq_true] at hone'
            rcases hone' with hh | hh
            · have := hmem a hh; have := hN b; omega
            · have := hmem b hh; have := hN a; omega
          refine ⟨hc, fun r => ?_, fun r hr => ?_⟩
          · by_cases hr' : r = dst
            · subst hr'; simp only [Op.eval, State.get_set_eq, List.length_append]; omega
            · simp only [Op.eval, State.get_set_ne _ _ _ _ hr']; have := hN r; omega
          · obtain ⟨hrF, hrd⟩ := hfil dst r hr
            simp only [Op.eval, State.get_set_ne _ _ _ _ hrd]
            have := hF r hrF; omega
        · exact absurd h (by simp)

/-! ### The `forBnd` rule

The loop's budget is bought in two steps. `Cmd.GrowOk` (round 0, frozen set
`Fz`) certifies that each *promoted* register grows by at most `poly(MF)` per
iteration, hence stays `≤ MF + m·poly(MF) = poly(MF)` for the whole run; the
body's own `CapCost` (round 1, frozen set `Fz ++ Prom`) then spends that cap.
Both runs are over the same body and the same states, so nothing is circular. -/

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

theorem Cmd.capCost_forBnd (cnt bnd : Var) (body : Cmd) (F Prom Fb' F' : List Var)
    (hbnd : bnd ∈ F)
    (hPromF : ∀ r ∈ Prom, r ∈ F)
    (hPromGrow : ∀ r ∈ Prom, body.GrowOk r (Cmd.freezeFor F cnt body) = true)
    (hbody : body.CapCost (Cmd.freezeFor F cnt body ++ Prom) Fb')
    (hF' : ∀ r ∈ F', r ∈ F ∧ ((r ≠ cnt ∧ r ∉ body.writes) ∨ r ∈ Prom)) :
    (Cmd.forBnd cnt bnd body).CapCost F F' := by
  have hfrz : ∀ v ∈ Cmd.freezeFor F cnt body, v ∉ body.writes :=
    fun v hv => (Cmd.mem_freezeFor hv).2
  obtain ⟨KG, DG, hgrow⟩ :=
    Cmd.growOk_sound_list body (Cmd.freezeFor F cnt body) hfrz Prom hPromGrow
  obtain ⟨Kb, Db, hbb⟩ := hbody
  refine ⟨2 + Kb * (KG + 1) ^ Db + Kb * (KG + 1) ^ Db * (Kb * (KG + 1) ^ Db) + KG,
    2 * ((DG + 1) * Db) + DG + 4, fun s MF N hF hN => ?_⟩
  set Fz := Cmd.freezeFor F cnt body with hFzdef
  set G := KG * (MF + 1) ^ DG with hGdef
  set MFb := MF + (MF + 1) * G with hMFbdef
  set Pb := Kb * (MFb + 1) ^ Db with hPbdef
  set m := (State.get s bnd).length with hmdef
  have hmMF : m ≤ MF := hF bnd hbnd
  have hmN : m ≤ N := hN bnd
  -- the loop invariant
  set MI : Nat → State → Prop := fun i st =>
      (∀ v ∈ F, v ≠ cnt → v ∉ body.writes → State.get st v = State.get s v)
    ∧ (∀ v ∈ Prom, (State.get st v).length ≤ MF + i * G)
    ∧ (∀ v, (State.get st v).length ≤ N + i * Pb) with hMIdef
  have h0 : MI 0 s := by
    refine ⟨fun _ _ _ _ => rfl, fun v hv => ?_, fun v => by simpa using hN v⟩
    simpa using hF v (hPromF v hv)
  -- one iteration
  have hiter : ∀ i st, i < m → MI i st →
      (∀ v ∈ Fz, (State.get (st.set cnt (List.replicate i 1)) v).length ≤ MF)
      ∧ (∀ v ∈ Fz ++ Prom, (State.get (st.set cnt (List.replicate i 1)) v).length ≤ MFb)
      ∧ (∀ v, (State.get (st.set cnt (List.replicate i 1)) v).length ≤ N + i * Pb) := by
    intro i st hi hM
    obtain ⟨hEq, hPr, hAll⟩ := hM
    have hcapFz : ∀ v ∈ Fz, (State.get (st.set cnt (List.replicate i 1)) v).length ≤ MF := by
      intro v hv
      obtain ⟨hor, hnw⟩ := Cmd.mem_freezeFor hv
      by_cases hvc : v = cnt
      · subst hvc; rw [State.get_set_eq, List.length_replicate]; omega
      · rw [State.get_set_ne _ _ _ _ hvc]
        rcases hor with hc | hvF
        · exact absurd hc hvc
        · rw [hEq v hvF hvc hnw]; exact hF v hvF
    refine ⟨hcapFz, fun v hv => ?_, fun v => ?_⟩
    · rcases List.mem_append.1 hv with hz | hp
      · have := hcapFz v hz
        have : (0 : Nat) ≤ (MF + 1) * G := Nat.zero_le _
        omega
      · by_cases hvc : v = cnt
        · subst hvc; rw [State.get_set_eq, List.length_replicate]
          have : (0 : Nat) ≤ (MF + 1) * G := Nat.zero_le _
          omega
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
    obtain ⟨hEq, hPr, hAll⟩ := hM
    obtain ⟨-, hglob, -⟩ := hbb _ MFb (N + i * Pb) hcapFb hcapN
    refine ⟨fun v hvF hvc hnw => ?_, fun v hv => ?_, fun v => ?_⟩
    · rw [Cmd.eval_get_of_not_writes body _ v hnw, State.get_set_ne _ _ _ _ hvc]
      exact hEq v hvF hvc hnw
    · have hgr := hgrow _ MF hcapFz v hv
      have hu : (State.get (st.set cnt (List.replicate i 1)) v).length ≤ MF + i * G := by
        by_cases hvc : v = cnt
        · subst hvc; rw [State.get_set_eq, List.length_replicate]; omega
        · rw [State.get_set_ne _ _ _ _ hvc]; exact hPr v hv
      have harith : (i + 1) * G = i * G + G := by ring
      omega
    · have := hglob v
      have harith : (i + 1) * Pb = i * Pb + Pb := by ring
      omega
  -- the closing budget
  set A := Kb * (KG + 1) ^ Db with hAdef
  have hPbA : Pb ≤ A * (MF + 1) ^ ((DG + 1) * Db) := by
    have hg1 : 1 + G ≤ (KG + 1) * (MF + 1) ^ DG := by
      have := pb_one DG MF; rw [hGdef]; nlinarith
    have hbase : MFb + 1 ≤ (KG + 1) * (MF + 1) ^ (DG + 1) := by
      have he : MFb + 1 = (MF + 1) * (1 + G) := by rw [hMFbdef]; ring
      calc MFb + 1 = (MF + 1) * (1 + G) := he
        _ ≤ (MF + 1) * ((KG + 1) * (MF + 1) ^ DG) := Nat.mul_le_mul_left _ hg1
        _ = (KG + 1) * (MF + 1) ^ (DG + 1) := by ring
    calc Pb ≤ Kb * ((KG + 1) * (MF + 1) ^ (DG + 1)) ^ Db :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
      _ = Kb * ((KG + 1) ^ Db * ((MF + 1) ^ (DG + 1)) ^ Db) := by rw [mul_pow]
      _ = A * (MF + 1) ^ ((DG + 1) * Db) := by rw [← pow_mul, hAdef]; ring
  set Btot := 1 + MF * Pb * (1 + MF * Pb) + MF * MF + MF * G with hBtotdef
  have hbudget : Btot ≤ (2 + A + A * A + KG) * (MF + 1) ^ (2 * ((DG + 1) * Db) + DG + 4) :=
    loop_budget A ((DG + 1) * Db) KG DG MF Pb G hPbA (le_of_eq hGdef)
  have hmPb : m * Pb ≤ Btot := by
    have h1 : m * Pb ≤ MF * Pb := Nat.mul_le_mul_right _ hmMF
    have h2 : MF * Pb ≤ MF * Pb * (1 + MF * Pb) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hmG : m * G ≤ Btot := by
    have h1 : m * G ≤ MF * G := Nat.mul_le_mul_right _ hmMF
    omega
  -- the final state satisfies the invariant
  have hfinal : MI m ((Cmd.forBnd cnt bnd body).eval s) := by
    rw [Cmd.eval_forBnd]
    exact Cmd.foldlState_range_induct body cnt m s MI h0 hstep
  obtain ⟨hEqF, hPrF, hAllF⟩ := hfinal
  refine ⟨?_, fun r => ?_, fun r hr => ?_⟩
  · -- cost
    have hC : ∀ i st, i < m → MI i st →
        body.cost (st.set cnt (List.replicate i 1)) ≤ Pb * (N + m * Pb + 1) := by
      intro i st hi hM
      obtain ⟨_, hcapFb, hcapN⟩ := hiter i st hi hM
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
    rcases hcase with ⟨hrc, hrw⟩ | hrp
    · rw [hEqF r hrF hrc hrw]; have := hF r hrF; omega
    · have := hPrF r hrp; omega

/-- **Weakening.** A smaller exit set is always fine. -/
theorem Cmd.CapCost.mono {c : Cmd} {F F' G' : List Var} (h : c.CapCost F F')
    (hsub : ∀ r ∈ G', r ∈ F') : c.CapCost F G' := by
  obtain ⟨K, D, hb⟩ := h
  exact ⟨K, D, fun s MF N hF hN =>
    ⟨(hb s MF N hF hN).1, (hb s MF N hF hN).2.1,
     fun r hr => (hb s MF N hF hN).2.2 r (hsub r hr)⟩⟩

/-! ## Part 4 — the decidable forward analysis

`c.capChk F = some F'` is a `decide`-able certificate for `c.CapCost F F'`. It
is a single forward pass carrying the capped set; the only place it looks
twice at a subterm is a loop, where `Cmd.promote` runs the (independent)
`GrowOk` check to decide which written registers keep their cap. -/

/-- The registers a loop body writes but nevertheless leaves capped, because
their per-iteration growth is `poly(MF)` against the strictly frozen set. -/
def Cmd.promote (F : List Var) (cnt : Var) (body : Cmd) : List Var :=
  F.filter (fun r => body.writes.contains r && body.GrowOk r (Cmd.freezeFor F cnt body))

def Cmd.capChk : List Var → Cmd → Option (List Var)
  | F, .op o => Op.capChk F o
  | F, .seq a b => (Cmd.capChk F a).bind (fun F1 => Cmd.capChk F1 b)
  | F, .ifBit _ a b =>
      match Cmd.capChk F a, Cmd.capChk F b with
      | some F1, some F2 => some (F1.filter (fun r => F2.contains r))
      | _, _ => none
  | F, .forBnd cnt bnd body =>
      if F.contains bnd then
        match Cmd.capChk (Cmd.freezeFor F cnt body ++ Cmd.promote F cnt body) body with
        | some _ =>
            some (F.filter (fun r =>
              !(cnt :: body.writes).contains r || (Cmd.promote F cnt body).contains r))
        | none => none
      else none

/-- **The analysis is sound.** -/
theorem Cmd.capCost_of_capChk : ∀ (c : Cmd) (F F' : List Var),
    c.capChk F = some F' → c.CapCost F F' := by
  intro c
  induction c with
  | op o => intro F F' h; exact Cmd.capCost_op o F F' h
  | seq c1 c2 ih1 ih2 =>
      intro F F' h
      simp only [Cmd.capChk, Option.bind_eq_some_iff] at h
      obtain ⟨F1, h1, h2⟩ := h
      exact (ih1 F F1 h1).seq (ih2 F1 F' h2)
  | ifBit t cT cE ihT ihE =>
      intro F F' h
      simp only [Cmd.capChk] at h
      rcases hT : Cmd.capChk F cT with _ | F1
      · rw [hT] at h; simp at h
      rcases hE : Cmd.capChk F cE with _ | F2
      · rw [hT, hE] at h; simp at h
      rw [hT, hE] at h
      simp only [Option.some.injEq] at h
      subst h
      refine Cmd.CapCost.ifBit (ihT F F1 hT) (ihE F F2 hE) (fun r hr => ?_)
      simp only [List.mem_filter] at hr
      exact ⟨hr.1, by simpa using hr.2⟩
  | forBnd cnt bnd body ih =>
      intro F F' h
      simp only [Cmd.capChk] at h
      by_cases hb : F.contains bnd = true
      · rw [if_pos hb] at h
        rcases hbody : Cmd.capChk (Cmd.freezeFor F cnt body ++ Cmd.promote F cnt body) body
          with _ | Fb'
        · rw [hbody] at h; simp at h
        rw [hbody] at h
        simp only [Option.some.injEq] at h
        subst h
        refine Cmd.capCost_forBnd cnt bnd body F (Cmd.promote F cnt body) Fb' _
          (by simpa using hb) (fun r hr => ?_) (fun r hr => ?_)
          (ih _ _ hbody) (fun r hr => ?_)
        · simp only [Cmd.promote, List.mem_filter] at hr; exact hr.1
        · simp only [Cmd.promote, List.mem_filter, Bool.and_eq_true] at hr; exact hr.2.2
        · simp only [List.mem_filter, Bool.or_eq_true, Bool.not_eq_true'] at hr
          refine ⟨hr.1, ?_⟩
          rcases hr.2 with hno | hyes
          · left
            have : r ∉ cnt :: body.writes := by simpa using hno
            simp only [List.mem_cons, not_or] at this
            exact ⟨this.1, this.2⟩
          · right; simpa using hyes
      · rw [if_neg hb] at h; simp at h

/-! ## Part 5 — the bridge back to a witness's `cost_le`

At a program's *entry* every register is bounded by the state's size, so both
caps may be taken to be `State.size s`. The shape produced here is exactly
`Cmd.PolyCost.cost_le_size`'s, which `S1Witness.s1CostBound_of_costLeSize`
consumes. -/

theorem Cmd.CapCost.cost_le_size {c : Cmd} {F F' : List Var} (h : c.CapCost F F') :
    ∃ K D : Nat, ∀ (s : State) (n : Nat),
      State.size s ≤ n → c.cost s ≤ K * (n + 1) ^ (D + 1) := by
  obtain ⟨K, D, hb⟩ := h
  refine ⟨K, D, fun s n hn => ?_⟩
  have hcap : ∀ r : Var, (State.get s r).length ≤ n :=
    fun r => le_trans (State.get_length_le_size s r) hn
  have := (hb s n n (fun r _ => hcap r) hcap).1
  have he : K * (n + 1) ^ D * (n + 1) = K * (n + 1) ^ (D + 1) := by ring
  omega

/-- **The one-liner.** `Cmd.costLeSize_of_capChk c F (by decide)` turns a
successful analysis into the cost bound a free witness needs. `F` is the list of
registers the program may touch — at entry they are all bounded by the input
size, so `List.range regBound` is the right choice. -/
theorem Cmd.costLeSize_of_capChk (c : Cmd) (F : List Var) (h : (c.capChk F).isSome = true) :
    ∃ K D : Nat, ∀ (s : State) (n : Nat),
      State.size s ≤ n → c.cost s ≤ K * (n + 1) ^ (D + 1) := by
  obtain ⟨F', hF'⟩ := Option.isSome_iff_exists.1 h
  exact (Cmd.capCost_of_capChk c F F' hF').cost_le_size

end Complexity.Lang
