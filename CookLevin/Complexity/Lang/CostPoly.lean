import Complexity.Lang.CostFlat
import Mathlib.Tactic

set_option autoImplicit false

/-! # `Cmd.PolyCost` — a compositional, semantics-free polynomial cost bound

The free-line witnesses owe a `cost_le : c.cost (encodeIn x) ≤ cost_bound (size x)`.
Discharging that stage by stage means re-walking every gadget's semantics: for a
program the size of `S1Program.s1Program` (≈ 90 `forBnd`s) that is several
thousand lines of bespoke accounting. This file replaces it with **one
compositional predicate**:

```
Cmd.PolyCost c  :=  ∃ K D, ∀ s M, (every register c's cost READS is ≤ M at entry)
                                  → c.cost s ≤ K * (M + 1) ^ (D + 1)
```

`PolyCost` is closed under `seq`, `ifBit` and — this is the load-bearing case —
under `forBnd` **whenever the loop body does not write any register its own cost
reads** (`Cmd.CostSafe`, a `decide`-able syntactic check). That covers every
emitter loop in the project, because the output register is built by unit-cost
`appendOne`s (a locked project invariant) and the unit-cost ops carry **no**
`costReads` at all. The remaining loops — unary drains (`tail dst dst`), unary
products (`concat dst dst src`) and cursor accumulators — are covered by
`Cmd.polyCost_forBnd_grow`, which asks only for a per-iteration *growth* budget
driven by the loop's stable registers.

## Why this is not circular

Two facts do the work:

* **`Cmd.get_length_eval_le`** — `|c.eval s @ r| ≤ |s @ r| + c.cost s`: every
  register's growth is paid for in cost. This is what lets `seq` re-establish
  the cap for its right factor without knowing anything about `c1`'s semantics.
* **A cost-safe loop's cost-relevant registers are *frozen*** — the body never
  writes them, so the per-iteration cap is the loop's *entry* cap, and the
  iteration count `|s @ bnd|` is itself capped (`bnd ∈ costReads`). The loop
  therefore adds one to the degree instead of compounding it.

Without the second fact no generic bound exists: `forBnd cnt bnd (concat dst dst
dst)` squares `dst` every iteration, so *some* syntactic side condition is
unavoidable.

## How to use it

1. `Cmd.polyCost_of_costSafe (by decide)` closes a whole gadget in one line.
2. For a gadget with a self-referential loop, prove `PolyCost` for that loop
   with `Cmd.polyCost_forBnd_grow` (or the ready-made `Cmd.polyCost_tailLoop` /
   `Cmd.polyCost_mulLoop`) and glue with `Cmd.PolyCost.seq` / `.ifBit`.
3. At the top, `Cmd.PolyCost.cost_le_size` turns `PolyCost c` plus a bound on
   `State.size (encodeIn x)` into the witness's `cost_le` shape.
-/

namespace Complexity.Lang

/-! ## Growth is paid for in cost, register by register

`Cmd.size_eval_le` bounds the *total* state size by `size + cost`; that is too
coarse to re-establish a per-register cap after a `seq`, because the entry size
of a program that has already emitted a large output is not bounded by the cap.
The per-register form below is what composes. -/

/-- The cost-carrying loop fold (state × running cost); `Cmd.run`'s `forBnd`
branch is definitionally this fold. -/
private def costFoldP (body : Cmd) (counter : Var) :
    State × Nat → Nat → State × Nat :=
  fun acc i => (body.eval (acc.1.set counter (List.replicate i 1)),
    acc.2 + body.cost (acc.1.set counter (List.replicate i 1)))

private theorem eval_forBnd_foldP (cnt bnd : Var) (body : Cmd) (s : State) :
    (Cmd.forBnd cnt bnd body).eval s
      = ((List.range (State.get s bnd).length).foldl (costFoldP body cnt) (s, 0)).1 := rfl

private theorem cost_forBnd_foldP (cnt bnd : Var) (body : Cmd) (s : State) :
    (Cmd.forBnd cnt bnd body).cost s
      = 1 + ((List.range (State.get s bnd).length).foldl (costFoldP body cnt) (s, 0)).2
        + (State.get s bnd).length * (State.get s bnd).length := rfl

private theorem Op.get_length_eval_le (o : Op) (s : State) (r : Var) :
    (State.get (Op.eval o s) r).length ≤ (State.get s r).length + Op.cost o s := by
  cases o with
  | clear dst =>
      by_cases hr : r = dst
      · subst hr; simp only [Op.eval, State.get_set_eq]; simp
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | appendOne dst =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq, List.length_append, List.length_cons,
          List.length_nil, Op.cost]
        omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | appendZero dst =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq, List.length_append, List.length_cons,
          List.length_nil, Op.cost]
        omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | copy dst src =>
      by_cases hr : r = dst
      · subst hr; simp only [Op.eval, State.get_set_eq, Op.cost]; omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | tail dst src =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq, List.length_tail, Op.cost]
        omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | head dst src =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq, Op.cost]
        rcases State.get s src with _ | ⟨x, xs⟩
        · simp
        · simp
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | eqBit dst src1 src2 =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq, Op.cost]
        by_cases hh : State.get s src1 = State.get s src2 <;> simp [hh] <;> omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | nonEmpty dst src =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq, Op.cost]
        by_cases hh : (State.get s src).isEmpty <;> simp [hh]
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | concat dst src1 src2 =>
      by_cases hr : r = dst
      · subst hr
        simp only [Op.eval, State.get_set_eq, List.length_append, Op.cost]
        omega
      · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega

/-- **Per-register growth is bounded by cost.** The size-aware cost model pays
for every cell it writes, register by register — the composable strengthening of
`Cmd.size_eval_le`. This is what lets `PolyCost` survive `seq`. -/
theorem Cmd.get_length_eval_le (c : Cmd) (s : State) (r : Var) :
    (State.get (c.eval s) r).length ≤ (State.get s r).length + c.cost s := by
  induction c generalizing s with
  | op o => rw [Cmd.eval_op, Cmd.cost_op]; exact Op.get_length_eval_le o s r
  | seq c1 c2 ih1 ih2 =>
      rw [Cmd.eval_seq, Cmd.cost_seq]
      have h2 := ih2 (c1.eval s)
      have h1 := ih1 s
      omega
  | ifBit t cT cE ihT ihE =>
      by_cases hb : State.get s t = [1]
      · rw [Cmd.eval_ifBit_true _ _ _ _ hb, Cmd.cost_ifBit_true _ _ _ _ hb]
        have := ihT s; omega
      · rw [Cmd.eval_ifBit_false _ _ _ _ hb, Cmd.cost_ifBit_false _ _ _ _ hb]
        have := ihE s; omega
  | forBnd cnt bnd body ih =>
      have key : ∀ i, i ≤ (State.get s bnd).length →
          (State.get ((List.range i).foldl (costFoldP body cnt) (s, 0)).1 r).length
            ≤ (State.get s r).length
              + ((List.range i).foldl (costFoldP body cnt) (s, 0)).2
              + i * (State.get s bnd).length := by
        intro i
        induction i with
        | zero => intro _; simp
        | succ i ihi =>
            intro hi
            have hle := ihi (Nat.le_of_succ_le hi)
            rw [List.range_succ, List.foldl_append]
            simp only [List.foldl_cons, List.foldl_nil]
            set F := (List.range i).foldl (costFoldP body cnt) (s, 0) with hF
            show (State.get (body.eval (F.1.set cnt (List.replicate i 1))) r).length
                ≤ (State.get s r).length
                  + (F.2 + body.cost (F.1.set cnt (List.replicate i 1)))
                  + (i + 1) * (State.get s bnd).length
            have hset : (State.get (F.1.set cnt (List.replicate i 1)) r).length
                ≤ (State.get F.1 r).length + (State.get s bnd).length := by
              by_cases hr : r = cnt
              · subst hr
                rw [State.get_set_eq, List.length_replicate]
                have : i ≤ (State.get s bnd).length := Nat.le_of_succ_le hi
                omega
              · rw [State.get_set_ne _ _ _ _ hr]; omega
            have hbody := ih (F.1.set cnt (List.replicate i 1))
            have harith : (i + 1) * (State.get s bnd).length
                = i * (State.get s bnd).length + (State.get s bnd).length := by ring
            omega
      have hkey := key (State.get s bnd).length (Nat.le_refl _)
      rw [eval_forBnd_foldP, cost_forBnd_foldP]
      omega

/-! ## The predicate -/

/-- **A compositional polynomial cost bound.** `c.cost s` is at most
`K·(M+1)^(D+1)` whenever every register `c`'s cost can read has length `≤ M` at
entry. The exponent is written `D + 1` so that it is always positive (the `seq`
rule multiplies exponents). `K` and `D` are existential on purpose: the project
never needs their values — `cost_bound` is a *free* polynomial whose only
constraint is that it keeps dominating `output_size_le`. -/
def Cmd.PolyCost (c : Cmd) : Prop :=
  ∃ K D : Nat, ∀ (s : State) (M : Nat),
    (∀ r ∈ c.costReads, (State.get s r).length ≤ M) →
    c.cost s ≤ K * (M + 1) ^ (D + 1)

theorem Cmd.polyCost_op (o : Op) : (Cmd.op o).PolyCost := by
  refine ⟨5, 0, fun s M h => ?_⟩
  rw [Cmd.cost_op, pow_one]
  cases o with
  | clear dst => simp only [Op.cost]; omega
  | appendOne dst => simp only [Op.cost]; omega
  | appendZero dst => simp only [Op.cost]; omega
  | head dst src => simp only [Op.cost]; omega
  | nonEmpty dst src => simp only [Op.cost]; omega
  | copy dst src =>
      have := h src (by simp [Cmd.costReads, Op.costReads])
      simp only [Op.cost]; omega
  | tail dst src =>
      have := h src (by simp [Cmd.costReads, Op.costReads])
      simp only [Op.cost]; omega
  | eqBit dst src1 src2 =>
      have h1 := h src1 (by simp [Cmd.costReads, Op.costReads])
      have h2 := h src2 (by simp [Cmd.costReads, Op.costReads])
      simp only [Op.cost]; omega
  | concat dst src1 src2 =>
      have h1 := h src1 (by simp [Cmd.costReads, Op.costReads])
      have h2 := h src2 (by simp [Cmd.costReads, Op.costReads])
      simp only [Op.cost]; omega

theorem Cmd.PolyCost.seq {c1 c2 : Cmd} (h1 : c1.PolyCost) (h2 : c2.PolyCost) :
    (c1 ;; c2).PolyCost := by
  obtain ⟨K1, D1, hb1⟩ := h1
  obtain ⟨K2, D2, hb2⟩ := h2
  refine ⟨1 + K1 + K2 * (K1 + 1) ^ (D2 + 1), (D1 + 1) * (D2 + 1) - 1, fun s M hcap => ?_⟩
  have hpos : 1 ≤ (D1 + 1) * (D2 + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hexp : (D1 + 1) * (D2 + 1) - 1 + 1 = (D1 + 1) * (D2 + 1) := by omega
  rw [hexp]
  have hcap1 : ∀ r ∈ c1.costReads, (State.get s r).length ≤ M := by
    intro r hr
    exact hcap r (by simp only [Cmd.costReads]; exact List.mem_append_left _ hr)
  have hc1 : c1.cost s ≤ K1 * (M + 1) ^ (D1 + 1) := hb1 s M hcap1
  set A := K1 * (M + 1) ^ (D1 + 1) with hA
  have hcap2 : ∀ r ∈ c2.costReads, (State.get (c1.eval s) r).length ≤ M + A := by
    intro r hr
    have hg := Cmd.get_length_eval_le c1 s r
    have hm := hcap r (by simp only [Cmd.costReads]; exact List.mem_append_right _ hr)
    omega
  have hc2 : c2.cost (c1.eval s) ≤ K2 * (M + A + 1) ^ (D2 + 1) := hb2 _ _ hcap2
  have hone : M + 1 ≤ (M + 1) ^ (D1 + 1) := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ (D1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hstep : M + A + 1 ≤ (K1 + 1) * (M + 1) ^ (D1 + 1) := by
    rw [hA]; nlinarith [hone]
  have hpow : (M + A + 1) ^ (D2 + 1)
      ≤ (K1 + 1) ^ (D2 + 1) * (M + 1) ^ ((D1 + 1) * (D2 + 1)) := by
    calc (M + A + 1) ^ (D2 + 1)
        ≤ ((K1 + 1) * (M + 1) ^ (D1 + 1)) ^ (D2 + 1) := Nat.pow_le_pow_left hstep _
      _ = (K1 + 1) ^ (D2 + 1) * ((M + 1) ^ (D1 + 1)) ^ (D2 + 1) := by rw [mul_pow]
      _ = (K1 + 1) ^ (D2 + 1) * (M + 1) ^ ((D1 + 1) * (D2 + 1)) := by rw [← pow_mul]
  have hA' : A ≤ K1 * (M + 1) ^ ((D1 + 1) * (D2 + 1)) := by
    rw [hA]
    exact Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right _ (by omega)))
  have hmul := Nat.mul_le_mul_left K2 hpow
  have hone' : 1 ≤ (M + 1) ^ ((D1 + 1) * (D2 + 1)) := Nat.one_le_pow _ _ (by omega)
  rw [Cmd.cost_seq]
  calc 1 + c1.cost s + c2.cost (c1.eval s)
      ≤ 1 + A + K2 * (M + A + 1) ^ (D2 + 1) := by omega
    _ ≤ (M + 1) ^ ((D1 + 1) * (D2 + 1)) + K1 * (M + 1) ^ ((D1 + 1) * (D2 + 1))
        + K2 * ((K1 + 1) ^ (D2 + 1) * (M + 1) ^ ((D1 + 1) * (D2 + 1))) := by omega
    _ = (1 + K1 + K2 * (K1 + 1) ^ (D2 + 1)) * (M + 1) ^ ((D1 + 1) * (D2 + 1)) := by ring

theorem Cmd.PolyCost.ifBit {t : Var} {cT cE : Cmd} (hT : cT.PolyCost) (hE : cE.PolyCost) :
    (Cmd.ifBit t cT cE).PolyCost := by
  obtain ⟨KT, DT, hbT⟩ := hT
  obtain ⟨KE, DE, hbE⟩ := hE
  refine ⟨1 + KT + KE, max DT DE, fun s M hcap => ?_⟩
  have hmT : (M + 1) ^ (DT + 1) ≤ (M + 1) ^ (max DT DE + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hmE : (M + 1) ^ (DE + 1) ≤ (M + 1) ^ (max DT DE + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hone : 1 ≤ (M + 1) ^ (max DT DE + 1) := Nat.one_le_pow _ _ (by omega)
  have hexp : (1 + KT + KE) * (M + 1) ^ (max DT DE + 1)
      = (M + 1) ^ (max DT DE + 1) + KT * (M + 1) ^ (max DT DE + 1)
        + KE * (M + 1) ^ (max DT DE + 1) := by ring
  by_cases hb : State.get s t = [1]
  · rw [Cmd.cost_ifBit_true _ _ _ _ hb]
    have hT' := hbT s M (fun r hr =>
      hcap r (by simp only [Cmd.costReads]; exact List.mem_append_left _ hr))
    have := Nat.mul_le_mul_left KT hmT
    have := Nat.mul_le_mul_left KE hmE
    omega
  · rw [Cmd.cost_ifBit_false _ _ _ _ hb]
    have hE' := hbE s M (fun r hr =>
      hcap r (by simp only [Cmd.costReads]; exact List.mem_append_right _ hr))
    have := Nat.mul_le_mul_left KT hmT
    have := Nat.mul_le_mul_left KE hmE
    omega

/-! ## The loop rules -/

/-- **The cost-safe loop rule.** If the body never *writes* a register its own
cost *reads*, then those registers are frozen for the whole loop: the
per-iteration cap is the loop's entry cap, and the iteration count is capped too
(`bnd` is one of the loop's `costReads`). One extra degree per loop level.

The side condition is exactly what fails for `forBnd cnt bnd (concat dst dst
dst)`, whose cost really is exponential — see `Cmd.polyCost_forBnd_grow` for the
self-referential bodies that do occur in practice. -/
theorem Cmd.polyCost_forBnd (cnt bnd : Var) (body : Cmd)
    (hsafe : ∀ r ∈ body.costReads, r ∉ body.writes) (hb : body.PolyCost) :
    (Cmd.forBnd cnt bnd body).PolyCost := by
  obtain ⟨K, D, hbb⟩ := hb
  refine ⟨K + 2, D + 1, fun s M hcap => ?_⟩
  have hmM : (State.get s bnd).length ≤ M := hcap bnd (by simp [Cmd.costReads])
  set MI : Nat → State → Prop :=
    fun _ st => ∀ r ∈ body.costReads, r ≠ cnt → State.get st r = State.get s r with hMI
  have h0 : MI 0 s := fun _ _ _ => rfl
  have hstep : ∀ i st, i < (State.get s bnd).length → MI i st →
      MI (i + 1) (body.eval (st.set cnt (List.replicate i 1))) := by
    intro i st _ hM r hr hrc
    rw [Cmd.eval_get_of_not_writes body _ r (hsafe r hr), State.get_set_ne _ _ _ _ hrc]
    exact hM r hr hrc
  have hC : ∀ i st, i < (State.get s bnd).length → MI i st →
      body.cost (st.set cnt (List.replicate i 1)) ≤ K * (M + 1) ^ (D + 1) := by
    intro i st hi hM
    refine hbb _ M (fun r hr => ?_)
    by_cases hrc : r = cnt
    · subst hrc
      rw [State.get_set_eq, List.length_replicate]
      omega
    · rw [State.get_set_ne _ _ _ _ hrc, hM r hr hrc]
      exact hcap r (by simp only [Cmd.costReads]; exact List.mem_cons_of_mem _ hr)
  have hloop := Cmd.cost_forBnd_le cnt bnd body s (K * (M + 1) ^ (D + 1)) MI h0 hstep hC
  set m := (State.get s bnd).length with hm
  have hpow : (M + 1) ^ (D + 1 + 1) = (M + 1) ^ (D + 1) * (M + 1) := by ring
  have hone : 1 ≤ (M + 1) ^ (D + 1 + 1) := Nat.one_le_pow _ _ (by omega)
  have hmid : m * (K * (M + 1) ^ (D + 1)) ≤ K * (M + 1) ^ (D + 1 + 1) := by
    have h1 : m * (K * (M + 1) ^ (D + 1)) ≤ (M + 1) * (K * (M + 1) ^ (D + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [hpow]
    nlinarith
  have hsq : m * m ≤ (M + 1) ^ (D + 1 + 1) := by
    have h1 : m * m ≤ (M + 1) * (M + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (M + 1) * (M + 1) ≤ (M + 1) ^ (D + 1 + 1) := by
      calc (M + 1) * (M + 1) = (M + 1) ^ 2 := by ring
        _ ≤ (M + 1) ^ (D + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hfin : (K + 2) * (M + 1) ^ (D + 1 + 1)
      = K * (M + 1) ^ (D + 1 + 1) + (M + 1) ^ (D + 1 + 1) + (M + 1) ^ (D + 1 + 1) := by ring
  omega

/-- **A loop leaves its counter no longer than its bound register.** The small
fact every *outer* loop needs: an inner loop's counter is one of the outer
body's cost reads (the emitters emit the counter's value), so the outer rule's
growth invariant has to know the inner counter stays small. Needs only that the
body does not write the counter itself. -/
theorem Cmd.forBnd_counter_le (cnt bnd : Var) (body : Cmd) (s : State)
    (h : cnt ∉ body.writes) :
    (State.get ((Cmd.forBnd cnt bnd body).eval s) cnt).length
      ≤ max (State.get s cnt).length (State.get s bnd).length := by
  rw [Cmd.eval_forBnd]
  refine Cmd.foldlState_range_induct body cnt (State.get s bnd).length s
    (fun _ st => (State.get st cnt).length
      ≤ max (State.get s cnt).length (State.get s bnd).length)
    (Nat.le_max_left _ _) (fun i st hi _ => ?_)
  show (State.get (body.eval (st.set cnt (List.replicate i 1))) cnt).length ≤ _
  rw [Cmd.eval_get_of_not_writes body _ cnt h, State.get_set_eq,
    List.length_replicate]
  exact le_trans (Nat.le_of_lt hi) (Nat.le_max_right _ _)

/-! ### The syntactic check and its one-line entry point -/

/-- **Every loop in `c` is cost-safe**: no loop body writes a register its own
cost reads. `decide`-able on a closed `Cmd`. -/
def Cmd.CostSafe : Cmd → Bool
  | .op _ => true
  | .seq c1 c2 => c1.CostSafe && c2.CostSafe
  | .ifBit _ cT cE => cT.CostSafe && cE.CostSafe
  | .forBnd _ _ body => body.CostSafe && body.costReads.all (fun r => decide (r ∉ body.writes))

/-- **The one-liner.** A syntactically cost-safe command has a polynomial cost
bound — no semantics, no invariants, no register table. -/
theorem Cmd.polyCost_of_costSafe : ∀ c : Cmd, c.CostSafe = true → c.PolyCost
  | .op o, _ => Cmd.polyCost_op o
  | .seq c1 c2, h => by
      simp only [Cmd.CostSafe, Bool.and_eq_true] at h
      exact (Cmd.polyCost_of_costSafe c1 h.1).seq (Cmd.polyCost_of_costSafe c2 h.2)
  | .ifBit _ cT cE, h => by
      simp only [Cmd.CostSafe, Bool.and_eq_true] at h
      exact (Cmd.polyCost_of_costSafe cT h.1).ifBit (Cmd.polyCost_of_costSafe cE h.2)
  | .forBnd cnt bnd body, h => by
      simp only [Cmd.CostSafe, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      exact Cmd.polyCost_forBnd cnt bnd body (fun r hr => h.2 r hr)
        (Cmd.polyCost_of_costSafe body h.1)

/-! ### The self-referential loops

`CostSafe` rejects a body that writes what it reads. The shapes that actually
occur are all fine, because their per-iteration *growth* is driven by registers
the body leaves alone. -/

/-- The unary drain `forBnd cnt bnd (tail dst dst)` (`minReg`, every cursor
pop): `dst` only shrinks. -/
theorem Cmd.polyCost_tailLoop (cnt bnd dst : Var) (hdc : dst ≠ cnt) :
    (Cmd.forBnd cnt bnd (Cmd.op (.tail dst dst))).PolyCost := by
  refine ⟨3, 1, fun s M hcap => ?_⟩
  have hd : (State.get s dst).length ≤ M :=
    hcap dst (by simp [Cmd.costReads, Op.costReads])
  have hbnd : (State.get s bnd).length ≤ M := hcap bnd (by simp [Cmd.costReads])
  have h := cost_tailLoop_le cnt bnd dst s M (State.get s bnd).length hdc hd rfl
  set m := (State.get s bnd).length with hm
  have h1 : m * (M + 1) ≤ (M + 1) * (M + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : m * m ≤ (M + 1) * (M + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : (3 : Nat) * (M + 1) ^ (1 + 1) = (M + 1) * (M + 1) + (M + 1) * (M + 1)
      + (M + 1) * (M + 1) := by ring
  have h4 : 1 ≤ (M + 1) * (M + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

/-- The unary product `forBnd cnt bnd (concat dst dst src)` (`unaryMulLoop`,
`pushKey`): `dst` grows by `|src|` per iteration and `src` is untouched. -/
theorem Cmd.polyCost_mulLoop (cnt bnd dst src : Var)
    (hds : dst ≠ src) (hdc : dst ≠ cnt) (hsc : src ≠ cnt) :
    (Cmd.forBnd cnt bnd (Cmd.op (.concat dst dst src))).PolyCost := by
  refine ⟨7, 2, fun s M hcap => ?_⟩
  have hd : (State.get s dst).length ≤ M :=
    hcap dst (by simp [Cmd.costReads, Op.costReads])
  have hs : (State.get s src).length ≤ M :=
    hcap src (by simp [Cmd.costReads, Op.costReads])
  have hbnd : (State.get s bnd).length ≤ M := hcap bnd (by simp [Cmd.costReads])
  have h := cost_mulLoop_le cnt bnd dst src s M M (State.get s bnd).length
    hds hdc hsc hd hs rfl
  set m := (State.get s bnd).length with hm
  have hmM : m ≤ M := hbnd
  have hexp : (7 : Nat) * (M + 1) ^ (2 + 1) = 7 * ((M + 1) * ((M + 1) * (M + 1))) := by ring
  have hmm : m * M ≤ M * M := Nat.mul_le_mul_right _ hmM
  have hstep1 : m * (2 * (M + m * M + M) + 1) ≤ M * (2 * (M + M * M + M) + 1) :=
    Nat.mul_le_mul hmM (by omega)
  have hstep2 : m * m ≤ M * M := Nat.mul_le_mul hmM hmM
  have key : 1 + M * (2 * (M + M * M + M) + 1) + M * M
      ≤ 7 * ((M + 1) * ((M + 1) * (M + 1))) := by nlinarith [Nat.zero_le M]
  omega

/-- The one nonlinear step of `Cmd.polyCost_forBnd_grow`, isolated over abstract
naturals so `nlinarith` sees no `^`. -/
private theorem grow_base_bound (M m KG P : Nat) (hP : 1 ≤ P) (hm : m ≤ M) :
    M + m * (KG * P + 1) + 1 ≤ (KG + 2) * (P * (M + 1)) := by
  have h1 : m * (KG * P + 1) ≤ M * (KG * P + 1) := Nat.mul_le_mul_right _ hm
  have h2 : M ≤ P * M := Nat.le_mul_of_pos_left _ (by omega)
  have h3 : (KG + 2) * (P * (M + 1)) = M * (KG * P) + KG * P + 2 * (P * M) + 2 * P := by ring
  have h4 : M * (KG * P + 1) = M * (KG * P) + M := by ring
  omega

/-- **The general self-referential loop rule.** Split the body's `costReads`
into the registers it leaves alone — capped by the loop's entry cap `M` for the
whole run — and the rest (`U`). If one iteration grows *every* register by at
most `KG·(M+1)^(DG+1)`, a budget that may depend on `M` but **not** on the
accumulating registers, then the loop is `PolyCost`. This is the shape of every
cursor/accumulator loop: the carried register grows by a stable amount per
step. -/
theorem Cmd.polyCost_forBnd_grow (cnt bnd : Var) (body : Cmd) (U : List Var)
    (hb : body.PolyCost)
    (hsafe : ∀ r ∈ body.costReads, r ∉ U → r ∉ body.writes)
    (KG DG : Nat)
    (hgrow : ∀ (st : State) (M : Nat),
      (∀ r ∈ body.costReads, r ∉ U → (State.get st r).length ≤ M) →
      ∀ r, (State.get (body.eval st) r).length
            ≤ (State.get st r).length + KG * (M + 1) ^ (DG + 1)) :
    (Cmd.forBnd cnt bnd body).PolyCost := by
  obtain ⟨K, D, hbb⟩ := hb
  refine ⟨K * (KG + 2) ^ (D + 1) + 2, (DG + 2) * (D + 1), fun s M hcap => ?_⟩
  have hmM : (State.get s bnd).length ≤ M := hcap bnd (by simp [Cmd.costReads])
  set m := (State.get s bnd).length with hm
  -- the `+ 1` pays for the loop counter, whose own growth is `i ≤ m`
  set G := KG * (M + 1) ^ (DG + 1) + 1 with hG
  set MI : Nat → State → Prop := fun i st =>
    (∀ r ∈ body.costReads, r ∉ U → r ≠ cnt → State.get st r = State.get s r)
    ∧ (∀ r, (State.get st r).length ≤ (State.get s r).length + i * G) with hMI
  have h0 : MI 0 s := ⟨fun _ _ _ _ => rfl, fun r => by simp⟩
  have hstable : ∀ i st, i ≤ m → MI i st →
      ∀ r ∈ body.costReads, r ∉ U →
        (State.get (st.set cnt (List.replicate i 1)) r).length ≤ M := by
    intro i st hi hM r hr hU
    by_cases hrc : r = cnt
    · subst hrc; rw [State.get_set_eq, List.length_replicate]; omega
    · rw [State.get_set_ne _ _ _ _ hrc, hM.1 r hr hU hrc]
      exact hcap r (by simp only [Cmd.costReads]; exact List.mem_cons_of_mem _ hr)
  have hstep : ∀ i st, i < m → MI i st →
      MI (i + 1) (body.eval (st.set cnt (List.replicate i 1))) := by
    intro i st hi hM
    have hread := hstable i st (Nat.le_of_lt hi) hM
    refine ⟨fun r hr hU hrc => ?_, fun r => ?_⟩
    · rw [Cmd.eval_get_of_not_writes body _ r (hsafe r hr hU),
        State.get_set_ne _ _ _ _ hrc]
      exact hM.1 r hr hU hrc
    · have hg := hgrow (st.set cnt (List.replicate i 1)) M hread r
      have hset : (State.get (st.set cnt (List.replicate i 1)) r).length
          ≤ (State.get s r).length + i * G := by
        by_cases hrc : r = cnt
        · rw [hrc, State.get_set_eq, List.length_replicate]
          have hiG : i ≤ i * G := Nat.le_mul_of_pos_right _ (by omega)
          omega
        · rw [State.get_set_ne _ _ _ _ hrc]; exact hM.2 r
      have harith : (i + 1) * G = i * G + G := by ring
      have hKG : KG * (M + 1) ^ (DG + 1) ≤ G := by omega
      omega
  -- per-iteration cost against the *widened* cap `M + m·G`
  have hC : ∀ i st, i < m → MI i st →
      body.cost (st.set cnt (List.replicate i 1)) ≤ K * (M + m * G + 1) ^ (D + 1) := by
    intro i st hi hM
    refine hbb _ (M + m * G) (fun r hr => ?_)
    by_cases hrc : r = cnt
    · subst hrc; rw [State.get_set_eq, List.length_replicate]; omega
    · rw [State.get_set_ne _ _ _ _ hrc]
      have h1 := hM.2 r
      have h2 : (State.get s r).length ≤ M :=
        hcap r (by simp only [Cmd.costReads]; exact List.mem_cons_of_mem _ hr)
      have h3 : i * G ≤ m * G := Nat.mul_le_mul_right _ (Nat.le_of_lt hi)
      omega
  have hloop := Cmd.cost_forBnd_le cnt bnd body s (K * (M + m * G + 1) ^ (D + 1))
    MI h0 hstep hC
  rw [← hm] at hloop
  -- `M + m·G + 1 ≤ (KG + 2) · (M+1)^(DG+2)`
  have hbase : M + m * G + 1 ≤ (KG + 2) * (M + 1) ^ (DG + 2) := by
    have h2 : (M + 1) ^ (DG + 2) = (M + 1) ^ (DG + 1) * (M + 1) := by ring
    have h3 : 1 ≤ (M + 1) ^ (DG + 1) := Nat.one_le_pow _ _ (by omega)
    rw [h2, hG]
    exact grow_base_bound M m KG _ h3 hmM
  have hpow : (M + m * G + 1) ^ (D + 1)
      ≤ (KG + 2) ^ (D + 1) * (M + 1) ^ ((DG + 2) * (D + 1)) := by
    calc (M + m * G + 1) ^ (D + 1)
        ≤ ((KG + 2) * (M + 1) ^ (DG + 2)) ^ (D + 1) := Nat.pow_le_pow_left hbase _
      _ = (KG + 2) ^ (D + 1) * ((M + 1) ^ (DG + 2)) ^ (D + 1) := by rw [mul_pow]
      _ = (KG + 2) ^ (D + 1) * (M + 1) ^ ((DG + 2) * (D + 1)) := by rw [← pow_mul]
  set E := (M + 1) ^ ((DG + 2) * (D + 1) + 1) with hE
  have hEbig : (M + 1) * (M + 1) ^ ((DG + 2) * (D + 1)) = E := by rw [hE]; ring
  have hone : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
  have hmid : m * (K * (M + m * G + 1) ^ (D + 1)) ≤ K * (KG + 2) ^ (D + 1) * E := by
    calc m * (K * (M + m * G + 1) ^ (D + 1))
        ≤ (M + 1) * (K * ((KG + 2) ^ (D + 1) * (M + 1) ^ ((DG + 2) * (D + 1)))) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hpow)
      _ = K * (KG + 2) ^ (D + 1) * ((M + 1) * (M + 1) ^ ((DG + 2) * (D + 1))) := by ring
      _ = K * (KG + 2) ^ (D + 1) * E := by rw [hEbig]
  have hsq : m * m ≤ E := by
    have h1 : m * m ≤ (M + 1) * (M + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (M + 1) * (M + 1) ≤ E := by
      rw [hE]
      calc (M + 1) * (M + 1) = (M + 1) ^ 2 := by ring
        _ ≤ (M + 1) ^ ((DG + 2) * (D + 1) + 1) := by
            refine Nat.pow_le_pow_right (by omega) ?_
            have : 1 ≤ (DG + 2) * (D + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
            omega
    omega
  have hfin : (K * (KG + 2) ^ (D + 1) + 2) * E = K * (KG + 2) ^ (D + 1) * E + E + E := by ring
  omega

/-! ## From `PolyCost` to a witness's `cost_le`

The cap at the program's entry is trivial: every register's length is at most
the whole state's size (`State.get_length_le_size`), so a bound on
`State.size (encodeIn x)` — which every free witness already proves for its
`encodeIn_size` field — is all the semantic input the ladder needs. -/

/-- **The entry point.** `PolyCost c` plus a bound on the *entry state's size*
gives a cost bound as a concrete polynomial in that bound. -/
theorem Cmd.PolyCost.cost_le_size {c : Cmd} (h : c.PolyCost) :
    ∃ K D : Nat, ∀ (s : State) (n : Nat), State.size s ≤ n → c.cost s ≤ K * (n + 1) ^ (D + 1) := by
  obtain ⟨K, D, hb⟩ := h
  exact ⟨K, D, fun s n hn => hb s n (fun r _ =>
    le_trans (State.get_length_le_size s r) hn)⟩

end Complexity.Lang
