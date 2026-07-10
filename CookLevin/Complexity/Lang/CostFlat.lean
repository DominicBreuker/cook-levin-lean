import Complexity.Lang.Frame
import Mathlib.Tactic

set_option autoImplicit false

/-! # Generic cost accounting for loop-free command fragments (the `cost_le` toolkit)

The free-line witnesses' `cost_le` obligations need per-loop cost bounds
(`Cmd.cost_forBnd_le`), whose per-iteration ingredient is a bound on the cost
of the (typically loop-free) loop *body*. Deriving that bound op-by-op with
`Cmd.cost_seq` chains re-walks the body's whole evaluation — expensive and
noisy. This file provides the generic shortcut:

* `Op.costReads`/`Cmd.costReads` — the registers whose *lengths* a fragment's
  cost (and per-op output length) can depend on;
* `Cmd.loopFree` — no `forBnd` inside;
* `Cmd.flatK` — a structurally-computed cost coefficient;
* **`Cmd.cost_le_flat`** — for a loop-free `c`, if every register in
  `c.costReads` has length `≤ M` at entry, then `c.cost s ≤ c.flatK * (M + 1)`,
  and no register grows by more than `c.flatK * (M + 1)`.

The coefficient `flatK` compounds multiplicatively through `seq` (a later op
can read what an earlier `concat` doubled), so it is exponential in the
fragment's op count — irrelevant for the polynomial cost bounds it feeds
(fragments are constant-size program text), and it frees every call site from
op-by-op walking.

Also here: the syntactic write-set (`Op.writesTo`/`Cmd.writes`) with its frame
lemma `Cmd.eval_get_of_not_writes` (registers outside the write set never
change — frame facts without register-bound arithmetic), the register-length
vs. state-size bound `State.get_length_le_size`, and the two ubiquitous
simple-loop cost bounds `cost_mulLoop_le` (self-append unary product) and
`cost_tailLoop_le` (truncated subtraction / stream drain). -/

namespace Complexity.Lang

/-! ## The syntactic write set and its frame lemma -/

/-- The one register an op writes. -/
def Op.writesTo : Op → Var
  | .clear dst => dst
  | .appendOne dst => dst
  | .appendZero dst => dst
  | .copy dst _ => dst
  | .tail dst _ => dst
  | .head dst _ => dst
  | .eqBit dst _ _ => dst
  | .nonEmpty dst _ => dst
  | .concat dst _ _ => dst

theorem Op.eval_get_ne_writesTo (o : Op) (s : State) (r : Var) (h : r ≠ o.writesTo) :
    State.get (Op.eval o s) r = State.get s r := by
  cases o <;> exact State.get_set_ne _ _ _ _ h

/-- The registers a command can write (syntactic overapproximation; includes
loop counters). -/
def Cmd.writes : Cmd → List Var
  | .op o => [o.writesTo]
  | .seq c1 c2 => c1.writes ++ c2.writes
  | .ifBit _ cT cE => cT.writes ++ cE.writes
  | .forBnd cnt _ body => cnt :: body.writes

/-- **Write-set frame**: a register outside `c.writes` is untouched by `c`.
The register-enumeration-free frame lemma (contrast `Cmd.eval_get_frame`,
which needs a numeric bound). -/
theorem Cmd.eval_get_of_not_writes (c : Cmd) (s : State) (r : Var)
    (h : r ∉ c.writes) : State.get (c.eval s) r = State.get s r := by
  induction c generalizing s with
  | op o =>
      rw [Cmd.eval_op]
      exact Op.eval_get_ne_writesTo o s r (by simpa [Cmd.writes] using h)
  | seq c1 c2 ih1 ih2 =>
      rw [Cmd.eval_seq]
      have h1 : r ∉ c1.writes := fun hh => h (by simp [Cmd.writes, hh])
      have h2 : r ∉ c2.writes := fun hh => h (by simp [Cmd.writes, hh])
      rw [ih2 _ h2, ih1 _ h1]
  | ifBit t cT cE ihT ihE =>
      have hT : r ∉ cT.writes := fun hh => h (by simp [Cmd.writes, hh])
      have hE : r ∉ cE.writes := fun hh => h (by simp [Cmd.writes, hh])
      by_cases hb : State.get s t = [1]
      · rw [Cmd.eval_ifBit_true _ _ _ _ hb, ihT _ hT]
      · rw [Cmd.eval_ifBit_false _ _ _ _ hb, ihE _ hE]
  | forBnd cnt bnd body ih =>
      have hcnt : r ≠ cnt := fun hh => h (by simp [Cmd.writes, hh])
      have hbody : r ∉ body.writes := fun hh => h (by simp [Cmd.writes, hh])
      rw [Cmd.eval_forBnd]
      exact Cmd.foldlState_range_induct body cnt (State.get s bnd).length s
        (fun _ st => State.get st r = State.get s r) rfl
        (fun i st _ hM => by
          show State.get (body.eval (st.set cnt (List.replicate i 1))) r
              = State.get s r
          rw [ih _ hbody, State.get_set_ne _ _ _ _ hcnt]; exact hM)

/-! ## Register length vs. state size -/

private theorem getElem_length_le_size :
    ∀ (s : State) (i : Nat) (h : i < s.length), (s[i]'h).length ≤ State.size s
  | a :: t, 0, _ => by
      show a.length ≤ State.size (a :: t)
      simp only [State.size, List.map_cons, List.foldr_cons]
      omega
  | a :: t, i + 1, h => by
      have ih := getElem_length_le_size t i (by simpa using h)
      show (t[i]'_).length ≤ State.size (a :: t)
      simp only [State.size, List.map_cons, List.foldr_cons]
      simp only [State.size] at ih
      omega

/-- Any single register's length is at most the whole state's size. -/
theorem State.get_length_le_size (s : State) (r : Var) :
    (State.get s r).length ≤ State.size s := by
  by_cases h : r < s.length
  · have : State.get s r = s[r]'h := by
      unfold State.get; rw [List.getElem?_eq_getElem h]; rfl
    rw [this]
    exact getElem_length_le_size s r h
  · have : State.get s r = [] := by
      unfold State.get; rw [List.getElem?_eq_none (Nat.le_of_not_lt h)]; rfl
    simp [this]

/-! ## The loop-free flat cost bound -/

/-- The registers whose lengths an op's cost (and written value's length,
beyond its own prior content) can depend on. -/
def Op.costReads : Op → List Var
  | .clear _ => []
  | .appendOne _ => []
  | .appendZero _ => []
  | .copy _ src => [src]
  | .tail _ src => [src]
  | .head _ _ => []
  | .eqBit _ src1 src2 => [src1, src2]
  | .nonEmpty _ _ => []
  | .concat _ src1 src2 => [src1, src2]

/-- The registers whose lengths a command's cost can depend on. -/
def Cmd.costReads : Cmd → List Var
  | .op o => o.costReads
  | .seq c1 c2 => c1.costReads ++ c2.costReads
  | .ifBit _ cT cE => cT.costReads ++ cE.costReads
  | .forBnd _ bnd body => bnd :: body.costReads

/-- No `forBnd` inside. -/
def Cmd.loopFree : Cmd → Bool
  | .op _ => true
  | .seq c1 c2 => c1.loopFree && c2.loopFree
  | .ifBit _ cT cE => cT.loopFree && cE.loopFree
  | .forBnd _ _ _ => false

/-- The flat cost coefficient: `c.cost s ≤ c.flatK * (M + 1)` whenever every
register in `c.costReads` has length `≤ M` (loop-free `c`). Compounds
multiplicatively through `seq` (growth feeding later reads). -/
def Cmd.flatK : Cmd → Nat
  | .op _ => 5
  | .seq c1 c2 => 1 + c1.flatK + c2.flatK * (c1.flatK + 1)
  | .ifBit _ cT cE => 1 + cT.flatK + cE.flatK
  | .forBnd _ _ _ => 0

/-- **The flat cost bound.** For loop-free `c` with all `costReads` lengths
`≤ M` at entry: the cost is `≤ flatK·(M+1)` and no register grows by more.
One lemma, no op-by-op walking at call sites. -/
theorem Cmd.cost_le_flat (c : Cmd) (hlf : c.loopFree = true) (s : State) (M : Nat)
    (h : ∀ r ∈ c.costReads, (State.get s r).length ≤ M) :
    c.cost s ≤ c.flatK * (M + 1)
    ∧ ∀ r : Var, (State.get (c.eval s) r).length
        ≤ (State.get s r).length + c.flatK * (M + 1) := by
  induction c generalizing s M with
  | op o =>
      have hK : Cmd.flatK (Cmd.op o) = 5 := rfl
      rw [Cmd.cost_op, Cmd.eval_op, hK]
      cases o with
      | clear dst =>
          refine ⟨by simp [Op.cost]; omega, fun r => ?_⟩
          by_cases hr : r = dst
          · subst hr; simp only [Op.eval, State.get_set_eq]; simp
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
      | appendOne dst =>
          refine ⟨by simp [Op.cost]; omega, fun r => ?_⟩
          by_cases hr : r = dst
          · subst hr; simp only [Op.eval, State.get_set_eq, List.length_append,
              List.length_cons, List.length_nil]
            omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
      | appendZero dst =>
          refine ⟨by simp [Op.cost]; omega, fun r => ?_⟩
          by_cases hr : r = dst
          · subst hr; simp only [Op.eval, State.get_set_eq, List.length_append,
              List.length_cons, List.length_nil]
            omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
      | copy dst src =>
          have hs : (State.get s src).length ≤ M :=
            h src (by simp [Cmd.costReads, Op.costReads])
          refine ⟨by simp only [Op.cost]; omega, fun r => ?_⟩
          by_cases hr : r = dst
          · subst hr; simp only [Op.eval, State.get_set_eq]; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
      | tail dst src =>
          have hs : (State.get s src).length ≤ M :=
            h src (by simp [Cmd.costReads, Op.costReads])
          refine ⟨by simp only [Op.cost]; omega, fun r => ?_⟩
          by_cases hr : r = dst
          · subst hr; simp only [Op.eval, State.get_set_eq, List.length_tail]; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
      | head dst src =>
          refine ⟨by simp [Op.cost]; omega, fun r => ?_⟩
          by_cases hr : r = dst
          · subst hr; simp only [Op.eval, State.get_set_eq]
            rcases State.get s src with _ | ⟨x, xs⟩
            · simp
            · simp; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
      | eqBit dst src1 src2 =>
          have hs1 : (State.get s src1).length ≤ M :=
            h src1 (by simp [Cmd.costReads, Op.costReads])
          have hs2 : (State.get s src2).length ≤ M :=
            h src2 (by simp [Cmd.costReads, Op.costReads])
          refine ⟨by simp only [Op.cost]; omega, fun r => ?_⟩
          by_cases hr : r = dst
          · subst hr; simp only [Op.eval, State.get_set_eq]
            by_cases hh : State.get s src1 = State.get s src2 <;> simp [hh] <;> omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
      | nonEmpty dst src =>
          refine ⟨by simp [Op.cost]; omega, fun r => ?_⟩
          by_cases hr : r = dst
          · subst hr; simp only [Op.eval, State.get_set_eq]
            by_cases hh : (State.get s src).isEmpty <;> simp [hh] <;> omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
      | concat dst src1 src2 =>
          have hs1 : (State.get s src1).length ≤ M :=
            h src1 (by simp [Cmd.costReads, Op.costReads])
          have hs2 : (State.get s src2).length ≤ M :=
            h src2 (by simp [Cmd.costReads, Op.costReads])
          refine ⟨by simp only [Op.cost]; omega, fun r => ?_⟩
          by_cases hr : r = dst
          · subst hr; simp only [Op.eval, State.get_set_eq, List.length_append]; omega
          · simp only [Op.eval, State.get_set_ne _ _ _ _ hr]; omega
  | seq c1 c2 ih1 ih2 =>
      have hlf1 : c1.loopFree = true := by
        have := hlf; simp only [Cmd.loopFree, Bool.and_eq_true] at this; exact this.1
      have hlf2 : c2.loopFree = true := by
        have := hlf; simp only [Cmd.loopFree, Bool.and_eq_true] at this; exact this.2
      obtain ⟨h1c, h1g⟩ := ih1 hlf1 s M
        (fun r hr => h r (by simp [Cmd.costReads]; exact Or.inl hr))
      obtain ⟨h2c, h2g⟩ := ih2 hlf2 (c1.eval s) (M + c1.flatK * (M + 1))
        (fun r hr => by
          have := h1g r
          have hM : (State.get s r).length ≤ M :=
            h r (by simp [Cmd.costReads]; exact Or.inr hr)
          omega)
      have key : M + c1.flatK * (M + 1) + 1 = (c1.flatK + 1) * (M + 1) := by ring
      rw [key] at h2c h2g
      have hKe : Cmd.flatK (c1 ;; c2) * (M + 1)
          = (M + 1) + c1.flatK * (M + 1) + c2.flatK * ((c1.flatK + 1) * (M + 1)) := by
        show (1 + c1.flatK + c2.flatK * (c1.flatK + 1)) * (M + 1) = _
        ring
      constructor
      · rw [Cmd.cost_seq, hKe]
        set A := c1.flatK * (M + 1) with hA
        set B := c2.flatK * ((c1.flatK + 1) * (M + 1)) with hB
        clear_value A B
        omega
      · intro r
        rw [Cmd.eval_seq, hKe]
        have := h2g r
        have := h1g r
        set A := c1.flatK * (M + 1) with hA
        set B := c2.flatK * ((c1.flatK + 1) * (M + 1)) with hB
        clear_value A B
        omega
  | ifBit t cT cE ihT ihE =>
      have hlfT : cT.loopFree = true := by
        have := hlf; simp only [Cmd.loopFree, Bool.and_eq_true] at this; exact this.1
      have hlfE : cE.loopFree = true := by
        have := hlf; simp only [Cmd.loopFree, Bool.and_eq_true] at this; exact this.2
      have hKe : Cmd.flatK (Cmd.ifBit t cT cE) * (M + 1)
          = (M + 1) + cT.flatK * (M + 1) + cE.flatK * (M + 1) := by
        show (1 + cT.flatK + cE.flatK) * (M + 1) = _
        ring
      by_cases hb : State.get s t = [1]
      · obtain ⟨hc, hg⟩ := ihT hlfT s M
          (fun r hr => h r (by simp [Cmd.costReads]; exact Or.inl hr))
        constructor
        · rw [Cmd.cost_ifBit_true _ _ _ _ hb, hKe]
          set A := cT.flatK * (M + 1) with hA
          set B := cE.flatK * (M + 1) with hB
          clear_value A B
          omega
        · intro r
          rw [Cmd.eval_ifBit_true _ _ _ _ hb, hKe]
          have := hg r
          set A := cT.flatK * (M + 1) with hA
          set B := cE.flatK * (M + 1) with hB
          clear_value A B
          omega
      · obtain ⟨hc, hg⟩ := ihE hlfE s M
          (fun r hr => h r (by simp [Cmd.costReads]; exact Or.inr hr))
        constructor
        · rw [Cmd.cost_ifBit_false _ _ _ _ hb, hKe]
          set A := cT.flatK * (M + 1) with hA
          set B := cE.flatK * (M + 1) with hB
          clear_value A B
          omega
        · intro r
          rw [Cmd.eval_ifBit_false _ _ _ _ hb, hKe]
          have := hg r
          set A := cT.flatK * (M + 1) with hA
          set B := cE.flatK * (M + 1) with hB
          clear_value A B
          omega
  | forBnd cnt bnd body ih =>
      exact absurd hlf (by simp [Cmd.loopFree])

/-- The loop-cost wrapper for a loop-free body: pair a run invariant `Minv`
with per-iteration `costReads` ceilings `≤ B` and the whole loop costs
`≤ 1 + m·(flatK·(B+1)) + m²`. -/
theorem Cmd.cost_forBnd_flat_le (cnt bnd : Var) (body : Cmd)
    (hlf : body.loopFree = true) (s : State) (B : Nat)
    (Minv : Nat → State → Prop) (h0 : Minv 0 s)
    (hstep : ∀ i st, i < (State.get s bnd).length → Minv i st →
        Minv (i + 1) (body.eval (st.set cnt (List.replicate i 1))))
    (hread : ∀ i st, i < (State.get s bnd).length → Minv i st →
        ∀ r ∈ body.costReads,
          (State.get (st.set cnt (List.replicate i 1)) r).length ≤ B) :
    (Cmd.forBnd cnt bnd body).cost s
      ≤ 1 + (State.get s bnd).length * (body.flatK * (B + 1))
        + (State.get s bnd).length * (State.get s bnd).length :=
  Cmd.cost_forBnd_le cnt bnd body s (body.flatK * (B + 1)) Minv h0 hstep
    (fun i st hi hM => (Cmd.cost_le_flat body hlf _ B (hread i st hi hM)).1)

/-! ## The two ubiquitous simple loops -/

/-- Cost of the unary-product loop `forBnd cnt bnd (concat dst dst src)`:
with `|dst| ≤ a`, `|src| ≤ k` at entry and `m` iterations, the cost is
`≤ 1 + m·(2·(a + m·k + k) + 1) + m²` (the accumulator re-read makes each
iteration linear in the accumulated length). -/
theorem cost_mulLoop_le (cnt bnd dst src : Var) (s : State) (a k m : Nat)
    (hds : dst ≠ src) (hdc : dst ≠ cnt) (hsc : src ≠ cnt)
    (ha : (State.get s dst).length ≤ a) (hk : (State.get s src).length ≤ k)
    (hm : (State.get s bnd).length = m) :
    (Cmd.forBnd cnt bnd (Cmd.op (.concat dst dst src))).cost s
      ≤ 1 + m * (2 * (a + m * k + k) + 1) + m * m := by
  have h := Cmd.cost_forBnd_le cnt bnd (Cmd.op (.concat dst dst src)) s
    (2 * (a + m * k + k) + 1)
    (fun i st => (State.get st dst).length ≤ a + i * k
      ∧ (State.get st src).length ≤ k)
    ⟨by simpa using ha, hk⟩
    (fun i st hi hM => by
      obtain ⟨hd, hs'⟩ := hM
      have hwd : (State.get (st.set cnt (List.replicate i 1)) dst).length
          ≤ a + i * k := by
        rw [State.get_set_ne _ _ _ _ hdc]; exact hd
      have hws : (State.get (st.set cnt (List.replicate i 1)) src).length ≤ k := by
        rw [State.get_set_ne _ _ _ _ hsc]; exact hs'
      constructor
      · rw [Cmd.eval_op]
        simp only [Op.eval, State.get_set_eq, List.length_append]
        have : a + i * k + k = a + (i + 1) * k := by ring
        omega
      · rw [Cmd.eval_op]
        simp only [Op.eval]
        rw [State.get_set_ne _ _ _ _ (Ne.symm hds)]
        exact hws)
    (fun i st hi hM => by
      obtain ⟨hd, hs'⟩ := hM
      rw [Cmd.cost_op]
      show 2 * ((State.get (st.set cnt (List.replicate i 1)) dst).length
        + (State.get (st.set cnt (List.replicate i 1)) src).length) + 1 ≤ _
      rw [State.get_set_ne _ _ _ _ hdc, State.get_set_ne _ _ _ _ hsc]
      have hik : i * k ≤ m * k := Nat.mul_le_mul_right k (le_of_lt (hm ▸ hi))
      omega)
  rw [hm] at h
  exact h

/-- Cost of the drain loop `forBnd cnt bnd (tail dst dst)`: with `|dst| ≤ a`
at entry and `m` iterations, the cost is `≤ 1 + m·(a + 1) + m²`. -/
theorem cost_tailLoop_le (cnt bnd dst : Var) (s : State) (a m : Nat)
    (hdc : dst ≠ cnt)
    (ha : (State.get s dst).length ≤ a)
    (hm : (State.get s bnd).length = m) :
    (Cmd.forBnd cnt bnd (Cmd.op (.tail dst dst))).cost s
      ≤ 1 + m * (a + 1) + m * m := by
  have h := Cmd.cost_forBnd_le cnt bnd (Cmd.op (.tail dst dst)) s (a + 1)
    (fun _ st => (State.get st dst).length ≤ a)
    ha
    (fun i st _ hM => by
      have hwd : (State.get (st.set cnt (List.replicate i 1)) dst).length ≤ a := by
        rw [State.get_set_ne _ _ _ _ hdc]; exact hM
      rw [Cmd.eval_op]
      simp only [Op.eval, State.get_set_eq, List.length_tail]
      omega)
    (fun i st _ hM => by
      rw [Cmd.cost_op]
      show (State.get (st.set cnt (List.replicate i 1)) dst).length + 1 ≤ _
      rw [State.get_set_ne _ _ _ _ hdc]
      omega)
  rw [hm] at h
  exact h

/-- Cost of a constant-cost-body loop (`appendOne`/`appendZero`/`clear`/
`head`/`nonEmpty` bodies): `≤ 1 + m·5 + m²`. -/
theorem cost_constLoop_le (cnt bnd : Var) (body : Cmd)
    (hlf : body.loopFree = true) (hnr : body.costReads = [])
    (s : State) (m : Nat) (hm : (State.get s bnd).length = m) :
    (Cmd.forBnd cnt bnd body).cost s ≤ 1 + m * body.flatK + m * m := by
  have h := Cmd.cost_forBnd_le cnt bnd body s body.flatK
    (fun _ _ => True) trivial (fun _ _ _ _ => trivial)
    (fun i st _ _ => by
      have := (Cmd.cost_le_flat body hlf (st.set cnt (List.replicate i 1)) 0
        (fun r hr => by rw [hnr] at hr; cases hr)).1
      simpa using this)
  rw [hm] at h
  exact h

end Complexity.Lang
