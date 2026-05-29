import Complexity.Lang.Semantics

set_option autoImplicit false

/-! # Frame / locality for `Cmd.eval` (C5a foundation)

The C5a `map_fst` task ("apply `f` to a pair's first component") needs to run a
witness program `Wf.c` — contracted only on the single-register canonical state
`[enc x]` — as a *subroutine* inside a larger state that also carries the second
component `enc c`. For that to be sound we need two structural facts about
`Cmd.eval`, both keyed to a static **register bound** `k`:

* **Frame** (`Cmd.eval_get_frame`): a program touching only registers `< k`
  leaves every register `≥ k` unchanged — so we can stash `enc c` at register
  `k` and recover it.
* **Locality** (`Cmd.eval_agree`): a program touching only registers `< k`
  produces the same low-register results on any two states that agree on
  registers `< k` — so running on a padded-out `[enc x]` agrees with running on
  `[enc x]` itself.

Both are proved by induction on `Cmd`; the `forBnd` cases reduce to an inner
induction over the loop's range list.

(`omega` is avoided throughout: register indices have type `Var := Nat`, an
abbrev that `omega` does not see through, so the arithmetic side-goals use
explicit `Nat` order lemmas via the helpers below.) -/

namespace Complexity.Lang

/-- From `a < k ≤ r` conclude `r ≠ a` — the recurring "register `r` is above the
write index `a`" fact. -/
private theorem reg_ne {a k r : Nat} (ha : a < k) (hr : k ≤ r) : r ≠ a :=
  Nat.ne_of_gt (Nat.lt_of_lt_of_le ha hr)

/-! ## `State.get` / `State.set` interaction -/

/-- The padded list used by `State.set` in the out-of-range case has length
`v + 1`, so the write index `v` is in range. -/
private theorem State.lt_pad_len {s : State} {v : Var} (h : s.length ≤ v) :
    v < (s ++ List.replicate (v + 1 - s.length) ([] : List Nat)).length := by
  rw [List.length_append, List.length_replicate, Nat.add_sub_cancel' (Nat.le_succ_of_le h)]
  exact Nat.lt_succ_self v

theorem State.get_set_eq (s : State) (v : Var) (val : List Nat) :
    (s.set v val).get v = val := by
  rcases Nat.lt_or_ge v s.length with h | h
  · simp [State.get, State.set, h, List.getElem?_set_self]
  · simp [State.get, State.set, Nat.not_lt.mpr h, List.getElem?_set_self (State.lt_pad_len h)]

theorem State.get_set_ne (s : State) (v : Var) (val : List Nat) (r : Var) (hr : r ≠ v) :
    (s.set v val).get r = s.get r := by
  rcases Nat.lt_or_ge v s.length with h | h
  · simp [State.get, State.set, h, List.getElem?_set_ne hr.symm]
  · simp only [State.get, State.set, Nat.not_lt.mpr h, if_false, List.getElem?_set_ne hr.symm]
    rcases Nat.lt_or_ge r s.length with hrs | hrs
    · rw [List.getElem?_append_left hrs]
    · rw [List.getElem?_append_right hrs, List.getElem?_eq_none hrs]
      rcases Nat.lt_or_ge (r - s.length) (v + 1 - s.length) with hlt | hge
      · simp [List.getElem?_eq_getElem
          (show r - s.length < (List.replicate (v + 1 - s.length) ([] : List Nat)).length by
            rw [List.length_replicate]; exact hlt)]
      · rw [List.getElem?_eq_none
          (show (List.replicate (v + 1 - s.length) ([] : List Nat)).length ≤ r - s.length by
            rw [List.length_replicate]; exact hge)]

/-! ## `UsesBelow` — a static "touches only registers `< k`" predicate -/

/-- An operation reads and writes only registers `< k`. -/
def Op.UsesBelow : Op → Nat → Prop
  | .clear dst,            k => dst < k
  | .appendOne dst,        k => dst < k
  | .appendZero dst,       k => dst < k
  | .copy dst src,         k => dst < k ∧ src < k
  | .tail dst src,         k => dst < k ∧ src < k
  | .head dst src,         k => dst < k ∧ src < k
  | .eqBit dst src1 src2,  k => dst < k ∧ src1 < k ∧ src2 < k
  | .nonEmpty dst src,     k => dst < k ∧ src < k
  | .takeAt dst src lenReg, k => dst < k ∧ src < k ∧ lenReg < k
  | .dropAt dst src lenReg, k => dst < k ∧ src < k ∧ lenReg < k
  | .concat dst src1 src2, k => dst < k ∧ src1 < k ∧ src2 < k
  | .consLen dst lenSrc src, k => dst < k ∧ lenSrc < k ∧ src < k

/-- A command reads and writes only registers `< k`. -/
def Cmd.UsesBelow : Cmd → Nat → Prop
  | .op o,                k => Op.UsesBelow o k
  | .seq c1 c2,           k => Cmd.UsesBelow c1 k ∧ Cmd.UsesBelow c2 k
  | .ifBit t cT cE,       k => t < k ∧ Cmd.UsesBelow cT k ∧ Cmd.UsesBelow cE k
  | .forBnd cnt bnd body, k => cnt < k ∧ bnd < k ∧ Cmd.UsesBelow body k

/-- `UsesBelow` is monotone in the bound: touching only registers `< k` implies
touching only registers `< k'` for any `k ≤ k'`. Used to widen two witnesses'
register bounds to a common one when sequencing them. -/
theorem Op.UsesBelow_mono {o : Op} {k k' : Nat} (h : Op.UsesBelow o k) (hk : k ≤ k') :
    Op.UsesBelow o k' := by
  cases o
  case clear dst      => exact Nat.lt_of_lt_of_le h hk
  case appendOne dst  => exact Nat.lt_of_lt_of_le h hk
  case appendZero dst => exact Nat.lt_of_lt_of_le h hk
  case copy dst src   => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  case tail dst src   => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  case head dst src   => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  case eqBit dst a b  =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk, Nat.lt_of_lt_of_le h.2.2 hk⟩
  case nonEmpty dst src => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  case takeAt dst src lenReg =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk, Nat.lt_of_lt_of_le h.2.2 hk⟩
  case dropAt dst src lenReg =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk, Nat.lt_of_lt_of_le h.2.2 hk⟩
  case concat dst src1 src2 =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk, Nat.lt_of_lt_of_le h.2.2 hk⟩
  case consLen dst lenSrc src =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk, Nat.lt_of_lt_of_le h.2.2 hk⟩

theorem Cmd.UsesBelow_mono {k k' : Nat} (hk : k ≤ k') :
    ∀ {c : Cmd}, Cmd.UsesBelow c k → Cmd.UsesBelow c k' := by
  intro c
  induction c with
  | op o => intro h; exact Op.UsesBelow_mono h hk
  | seq c1 c2 ih1 ih2 => intro h; exact ⟨ih1 h.1, ih2 h.2⟩
  | ifBit t cT cE ihT ihE => intro h; exact ⟨Nat.lt_of_lt_of_le h.1 hk, ihT h.2.1, ihE h.2.2⟩
  | forBnd cnt bnd body ihb =>
      intro h; exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk, ihb h.2.2⟩

/-- Any program touches *some* register, so a valid register bound is positive.
(Every `Cmd` bottoms out in an `Op`, and every `Op` accesses a register `< k`,
forcing `0 < k`.) Lets the frame argument treat register `0` specially. -/
theorem Cmd.UsesBelow_pos {k : Nat} : ∀ {c : Cmd}, Cmd.UsesBelow c k → 0 < k := by
  intro c
  induction c with
  | op o =>
      intro h
      cases o with
      | clear dst      => change dst < k at h; exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h
      | appendOne dst  => change dst < k at h; exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h
      | appendZero dst => change dst < k at h; exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h
      | copy dst src   =>
          change dst < k ∧ src < k at h; exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h.1
      | tail dst src   =>
          change dst < k ∧ src < k at h; exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h.1
      | head dst src   =>
          change dst < k ∧ src < k at h; exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h.1
      | eqBit dst a b  =>
          change dst < k ∧ a < k ∧ b < k at h; exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h.1
      | nonEmpty dst src =>
          change dst < k ∧ src < k at h; exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h.1
      | takeAt dst src lenReg =>
          change dst < k ∧ src < k ∧ lenReg < k at h
          exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h.1
      | dropAt dst src lenReg =>
          change dst < k ∧ src < k ∧ lenReg < k at h
          exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h.1
      | concat dst src1 src2 =>
          change dst < k ∧ src1 < k ∧ src2 < k at h
          exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h.1
      | consLen dst lenSrc src =>
          change dst < k ∧ lenSrc < k ∧ src < k at h
          exact Nat.lt_of_le_of_lt (Nat.zero_le dst) h.1
  | seq c1 c2 ih1 _ => intro h; obtain ⟨h1, _⟩ := h; exact ih1 h1
  | ifBit t cT cE _ _ => intro h; obtain ⟨ht, _, _⟩ := h; exact Nat.lt_of_le_of_lt (Nat.zero_le t) ht
  | forBnd cnt bnd body _ =>
      intro h; obtain ⟨hc, _, _⟩ := h; exact Nat.lt_of_le_of_lt (Nat.zero_le cnt) hc

/-! ## Frame: registers `≥ k` are preserved -/

theorem Op.eval_get_frame (o : Op) (k : Nat) (h : Op.UsesBelow o k)
    (s : State) (r : Var) (hr : k ≤ r) :
    (Op.eval o s).get r = s.get r := by
  cases o with
  | clear dst      => exact State.get_set_ne s dst _ r (reg_ne h hr)
  | appendOne dst  => exact State.get_set_ne s dst _ r (reg_ne h hr)
  | appendZero dst => exact State.get_set_ne s dst _ r (reg_ne h hr)
  | copy dst src   => exact State.get_set_ne s dst _ r (reg_ne h.1 hr)
  | tail dst src   => exact State.get_set_ne s dst _ r (reg_ne h.1 hr)
  | head dst src   => exact State.get_set_ne s dst _ r (reg_ne h.1 hr)
  | eqBit dst a b  => exact State.get_set_ne s dst _ r (reg_ne h.1 hr)
  | nonEmpty dst src => exact State.get_set_ne s dst _ r (reg_ne h.1 hr)
  | takeAt dst src lenReg => exact State.get_set_ne s dst _ r (reg_ne h.1 hr)
  | dropAt dst src lenReg => exact State.get_set_ne s dst _ r (reg_ne h.1 hr)
  | concat dst src1 src2 => exact State.get_set_ne s dst _ r (reg_ne h.1 hr)
  | consLen dst lenSrc src => exact State.get_set_ne s dst _ r (reg_ne h.1 hr)

theorem Cmd.eval_get_frame (c : Cmd) (k : Nat) (h : Cmd.UsesBelow c k)
    (s : State) (r : Var) (hr : k ≤ r) :
    (c.eval s).get r = s.get r := by
  induction c generalizing s with
  | op o => exact Op.eval_get_frame o k h s r hr
  | seq c1 c2 ih1 ih2 =>
      obtain ⟨h1, h2⟩ := h
      rw [Cmd.eval_seq, ih2 h2, ih1 h1]
  | ifBit t cT cE ihT ihE =>
      obtain ⟨_, hT, hE⟩ := h
      by_cases hb : s.get t = [1]
      · rw [Cmd.eval_ifBit_true t cT cE s hb]; exact ihT hT s
      · rw [Cmd.eval_ifBit_false t cT cE s hb]; exact ihE hE s
  | forBnd cnt bnd body ihbody =>
      obtain ⟨hcnt, _, hbody⟩ := h
      have hrcnt : r ≠ cnt := reg_ne hcnt hr
      have fold_frame : ∀ (L : List Nat) (acc : State × Nat),
          (((L.foldl (fun acc i =>
              let s' := acc.1.set cnt (List.replicate i 1)
              let res := Cmd.run body s'
              (res.1, acc.2 + res.2)) acc)).1).get r = acc.1.get r := by
        intro L
        induction L with
        | nil => intro acc; rfl
        | cons i L ihL =>
            intro acc
            simp only [List.foldl_cons]
            rw [ihL]
            show (Cmd.eval body (acc.1.set cnt (List.replicate i 1))).get r = acc.1.get r
            rw [ihbody hbody]
            exact State.get_set_ne _ _ _ _ hrcnt
      show (((List.range (s.get bnd).length).foldl (fun acc i =>
          let s' := acc.1.set cnt (List.replicate i 1)
          let res := Cmd.run body s'
          (res.1, acc.2 + res.2)) (s, 0)).1).get r = s.get r
      rw [fold_frame]

/-! ## Locality: low registers depend only on low registers -/

/-- Two states agree on every register `< k`. -/
def AgreeBelow (k : Nat) (s₁ s₂ : State) : Prop := ∀ r, r < k → s₁.get r = s₂.get r

theorem AgreeBelow.set {k : Nat} {s₁ s₂ : State} (h : AgreeBelow k s₁ s₂)
    (v : Var) (val : List Nat) : AgreeBelow k (s₁.set v val) (s₂.set v val) := by
  intro r hr
  by_cases hrv : r = v
  · subst hrv; rw [State.get_set_eq, State.get_set_eq]
  · rw [State.get_set_ne _ _ _ _ hrv, State.get_set_ne _ _ _ _ hrv]; exact h r hr

theorem Op.eval_agree (o : Op) (k : Nat) (h : Op.UsesBelow o k)
    {s₁ s₂ : State} (hagree : AgreeBelow k s₁ s₂) :
    AgreeBelow k (Op.eval o s₁) (Op.eval o s₂) := by
  cases o with
  | clear dst => exact hagree.set dst []
  | appendOne dst =>
      show AgreeBelow k (s₁.set dst (s₁.get dst ++ [1])) (s₂.set dst (s₂.get dst ++ [1]))
      rw [hagree dst h]; exact hagree.set dst _
  | appendZero dst =>
      show AgreeBelow k (s₁.set dst (s₁.get dst ++ [0])) (s₂.set dst (s₂.get dst ++ [0]))
      rw [hagree dst h]; exact hagree.set dst _
  | copy dst src =>
      obtain ⟨_, hs⟩ := h
      show AgreeBelow k (s₁.set dst (s₁.get src)) (s₂.set dst (s₂.get src))
      rw [hagree src hs]; exact hagree.set dst _
  | tail dst src =>
      obtain ⟨_, hs⟩ := h
      show AgreeBelow k (s₁.set dst (s₁.get src).tail) (s₂.set dst (s₂.get src).tail)
      rw [hagree src hs]; exact hagree.set dst _
  | head dst src =>
      obtain ⟨_, hs⟩ := h
      show AgreeBelow k (s₁.set dst (match s₁.get src with | [] => [] | x :: _ => [x]))
                        (s₂.set dst (match s₂.get src with | [] => [] | x :: _ => [x]))
      rw [hagree src hs]; exact hagree.set dst _
  | eqBit dst src1 src2 =>
      obtain ⟨_, h1, h2⟩ := h
      show AgreeBelow k (s₁.set dst (if s₁.get src1 = s₁.get src2 then [1] else [0]))
                        (s₂.set dst (if s₂.get src1 = s₂.get src2 then [1] else [0]))
      rw [hagree src1 h1, hagree src2 h2]; exact hagree.set dst _
  | nonEmpty dst src =>
      obtain ⟨_, hs⟩ := h
      show AgreeBelow k (s₁.set dst (if (s₁.get src).isEmpty then [0] else [1]))
                        (s₂.set dst (if (s₂.get src).isEmpty then [0] else [1]))
      rw [hagree src hs]; exact hagree.set dst _
  | takeAt dst src lenReg =>
      obtain ⟨_, hs, hl⟩ := h
      show AgreeBelow k (s₁.set dst ((s₁.get src).take ((s₁.get lenReg).headD 0)))
                        (s₂.set dst ((s₂.get src).take ((s₂.get lenReg).headD 0)))
      rw [hagree src hs, hagree lenReg hl]; exact hagree.set dst _
  | dropAt dst src lenReg =>
      obtain ⟨_, hs, hl⟩ := h
      show AgreeBelow k (s₁.set dst ((s₁.get src).drop ((s₁.get lenReg).headD 0)))
                        (s₂.set dst ((s₂.get src).drop ((s₂.get lenReg).headD 0)))
      rw [hagree src hs, hagree lenReg hl]; exact hagree.set dst _
  | concat dst src1 src2 =>
      obtain ⟨_, h1, h2⟩ := h
      show AgreeBelow k (s₁.set dst (s₁.get src1 ++ s₁.get src2))
                        (s₂.set dst (s₂.get src1 ++ s₂.get src2))
      rw [hagree src1 h1, hagree src2 h2]; exact hagree.set dst _
  | consLen dst lenSrc src =>
      obtain ⟨_, hl, hs⟩ := h
      show AgreeBelow k (s₁.set dst ((s₁.get lenSrc).length :: s₁.get src))
                        (s₂.set dst ((s₂.get lenSrc).length :: s₂.get src))
      rw [hagree lenSrc hl, hagree src hs]; exact hagree.set dst _

theorem Cmd.eval_agree (c : Cmd) (k : Nat) (h : Cmd.UsesBelow c k)
    {s₁ s₂ : State} (hagree : AgreeBelow k s₁ s₂) :
    AgreeBelow k (c.eval s₁) (c.eval s₂) := by
  induction c generalizing s₁ s₂ with
  | op o => exact Op.eval_agree o k h hagree
  | seq c1 c2 ih1 ih2 =>
      obtain ⟨h1, h2⟩ := h
      rw [Cmd.eval_seq, Cmd.eval_seq]
      exact ih2 h2 (ih1 h1 hagree)
  | ifBit t cT cE ihT ihE =>
      obtain ⟨ht, hT, hE⟩ := h
      have htt : s₁.get t = s₂.get t := hagree t ht
      by_cases hb : s₁.get t = [1]
      · rw [Cmd.eval_ifBit_true t cT cE s₁ hb,
          Cmd.eval_ifBit_true t cT cE s₂ (htt ▸ hb)]
        exact ihT hT hagree
      · rw [Cmd.eval_ifBit_false t cT cE s₁ hb,
          Cmd.eval_ifBit_false t cT cE s₂ (htt ▸ hb)]
        exact ihE hE hagree
  | forBnd cnt bnd body ihbody =>
      obtain ⟨_, hbnd, hbody⟩ := h
      have hiters : (s₁.get bnd).length = (s₂.get bnd).length := by rw [hagree bnd hbnd]
      have fold_agree : ∀ (L : List Nat) (acc₁ acc₂ : State × Nat),
          AgreeBelow k acc₁.1 acc₂.1 →
          AgreeBelow k ((L.foldl (fun acc i =>
              let s' := acc.1.set cnt (List.replicate i 1)
              let res := Cmd.run body s'
              (res.1, acc.2 + res.2)) acc₁).1)
            ((L.foldl (fun acc i =>
              let s' := acc.1.set cnt (List.replicate i 1)
              let res := Cmd.run body s'
              (res.1, acc.2 + res.2)) acc₂).1) := by
        intro L
        induction L with
        | nil => intro acc₁ acc₂ hacc; exact hacc
        | cons i L ihL =>
            intro acc₁ acc₂ hacc
            simp only [List.foldl_cons]
            apply ihL
            show AgreeBelow k (Cmd.eval body (acc₁.1.set cnt (List.replicate i 1)))
                              (Cmd.eval body (acc₂.1.set cnt (List.replicate i 1)))
            exact ihbody hbody (hacc.set cnt (List.replicate i 1))
      show AgreeBelow k (((List.range (s₁.get bnd).length).foldl (fun acc i =>
          let s' := acc.1.set cnt (List.replicate i 1)
          let res := Cmd.run body s'
          (res.1, acc.2 + res.2)) (s₁, 0)).1)
        (((List.range (s₂.get bnd).length).foldl (fun acc i =>
          let s' := acc.1.set cnt (List.replicate i 1)
          let res := Cmd.run body s'
          (res.1, acc.2 + res.2)) (s₂, 0)).1)
      rw [hiters]
      exact fold_agree (List.range (s₂.get bnd).length) (s₁, 0) (s₂, 0) hagree

/-! ## Cost locality: the cost depends only on registers `< k` -/

/-- An op's (now size-aware) cost agrees on states that agree on registers
`< k`, provided it only reads registers `< k`. The unit-cost ops are
state-independent (`rfl`); the size-aware ones read a source register whose
length is fixed by the agreement. -/
theorem Op.cost_agree (o : Op) (k : Nat) (h : Op.UsesBelow o k)
    {s₁ s₂ : State} (hagree : AgreeBelow k s₁ s₂) :
    Op.cost o s₁ = Op.cost o s₂ := by
  cases o with
  | clear _ => rfl
  | appendOne _ => rfl
  | appendZero _ => rfl
  | head _ _ => rfl
  | eqBit _ _ _ => rfl
  | nonEmpty _ _ => rfl
  | copy _ src =>
      show (s₁.get src).length + 1 = (s₂.get src).length + 1
      rw [hagree src h.2]
  | tail _ src =>
      show (s₁.get src).length + 1 = (s₂.get src).length + 1
      rw [hagree src h.2]
  | takeAt _ src _ =>
      show (s₁.get src).length + 1 = (s₂.get src).length + 1
      rw [hagree src h.2.1]
  | dropAt _ src _ =>
      show (s₁.get src).length + 1 = (s₂.get src).length + 1
      rw [hagree src h.2.1]
  | concat _ src1 src2 =>
      show (s₁.get src1).length + (s₁.get src2).length + 1
          = (s₂.get src1).length + (s₂.get src2).length + 1
      rw [hagree src1 h.2.1, hagree src2 h.2.2]
  | consLen _ _ src =>
      show (s₁.get src).length + 1 = (s₂.get src).length + 1
      rw [hagree src h.2.2]

/-- A program touching only registers `< k` runs at the same cost on any two
states that agree on registers `< k`. Needed so composition can bound the cost
of the second program on the first's (scratch-bearing) output. -/
theorem Cmd.cost_agree (c : Cmd) (k : Nat) (h : Cmd.UsesBelow c k)
    {s₁ s₂ : State} (hagree : AgreeBelow k s₁ s₂) :
    c.cost s₁ = c.cost s₂ := by
  induction c generalizing s₁ s₂ with
  | op o => rw [Cmd.cost_op, Cmd.cost_op]; exact Op.cost_agree o k h hagree
  | seq c1 c2 ih1 ih2 =>
      obtain ⟨h1, h2⟩ := h
      rw [Cmd.cost_seq, Cmd.cost_seq, ih1 h1 hagree,
        ih2 h2 (Cmd.eval_agree c1 k h1 hagree)]
  | ifBit t cT cE ihT ihE =>
      obtain ⟨ht, hT, hE⟩ := h
      have htt : s₁.get t = s₂.get t := hagree t ht
      by_cases hb : s₁.get t = [1]
      · rw [Cmd.cost_ifBit_true t cT cE s₁ hb,
          Cmd.cost_ifBit_true t cT cE s₂ (htt ▸ hb), ihT hT hagree]
      · rw [Cmd.cost_ifBit_false t cT cE s₁ hb,
          Cmd.cost_ifBit_false t cT cE s₂ (htt ▸ hb), ihE hE hagree]
  | forBnd cnt bnd body ihbody =>
      obtain ⟨_, hbnd, hbody⟩ := h
      have hiters : (s₁.get bnd).length = (s₂.get bnd).length := by rw [hagree bnd hbnd]
      have fold : ∀ (L : List Nat) (a1 a2 : State × Nat),
          AgreeBelow k a1.1 a2.1 → a1.2 = a2.2 →
          ((L.foldl (fun acc i =>
              let s' := acc.1.set cnt (List.replicate i 1)
              let res := Cmd.run body s'
              (res.1, acc.2 + res.2)) a1).2
            = (L.foldl (fun acc i =>
              let s' := acc.1.set cnt (List.replicate i 1)
              let res := Cmd.run body s'
              (res.1, acc.2 + res.2)) a2).2) := by
        intro L
        induction L with
        | nil => intro a1 a2 _ hc; exact hc
        | cons i L ihL =>
            intro a1 a2 hag hc
            simp only [List.foldl_cons]
            apply ihL
            · show AgreeBelow k (Cmd.eval body (a1.1.set cnt (List.replicate i 1)))
                                (Cmd.eval body (a2.1.set cnt (List.replicate i 1)))
              exact Cmd.eval_agree body k hbody (hag.set cnt (List.replicate i 1))
            · show a1.2 + body.cost (a1.1.set cnt (List.replicate i 1))
                  = a2.2 + body.cost (a2.1.set cnt (List.replicate i 1))
              rw [hc, ihbody hbody (hag.set cnt (List.replicate i 1))]
      show 1 + ((List.range (s₁.get bnd).length).foldl (fun acc i =>
          let s' := acc.1.set cnt (List.replicate i 1)
          let res := Cmd.run body s'
          (res.1, acc.2 + res.2)) (s₁, 0)).2
        = 1 + ((List.range (s₂.get bnd).length).foldl (fun acc i =>
          let s' := acc.1.set cnt (List.replicate i 1)
          let res := Cmd.run body s'
          (res.1, acc.2 + res.2)) (s₂, 0)).2
      rw [hiters, fold (List.range (s₂.get bnd).length) (s₁, 0) (s₂, 0) hagree rfl]

/-! ## Counted-loop reasoning (`forBnd`)

`forBnd`'s semantics is a `foldl` over `List.range iters` threading both the
state and the accumulated cost. For *behavioural* reasoning (the cost is a
separate concern) the cost component is noise. This section isolates the
pure-state loop fold (`Cmd.foldlState`), shows `forBnd`'s `eval` *is* that fold
(`Cmd.eval_forBnd`), and provides the workhorse **invariant principle**
(`Cmd.foldlState_range_induct`). These are the reusable tools for building and
verifying loop-based layer programs — `map` over a list, the SAT verifier
`evalCnfCmd` (C7), the Tseytin-as-`Cmd` reduction tail (plan step 2) — none of
which had any loop-reasoning lemma to stand on before. -/

/-- State-only loop fold: apply `body` once per `i ∈ L`, with the counter
register set to the unary representation of `i` before each iteration. This is
the pure-state projection of `forBnd` (the cost component dropped). -/
def Cmd.foldlState (body : Cmd) (counter : Var) (L : List Nat) (s : State) : State :=
  L.foldl (fun st i => body.eval (st.set counter (List.replicate i 1))) s

theorem Cmd.foldlState_nil (body : Cmd) (counter : Var) (s : State) :
    Cmd.foldlState body counter [] s = s := rfl

/-- The cost-carrying loop fold's *state* component equals `foldlState` (the cost
accumulator does not feed back into the state). -/
private theorem run_fold_fst (body : Cmd) (counter : Var) :
    ∀ (L : List Nat) (st : State) (c0 : Nat),
      (L.foldl (fun acc i =>
        let s' := acc.1.set counter (List.replicate i 1)
        let r := Cmd.run body s'
        (r.1, acc.2 + r.2)) (st, c0)).1
      = Cmd.foldlState body counter L st
  | [], _, _ => rfl
  | i :: L, st, c0 => by
      simp only [List.foldl_cons, Cmd.foldlState, List.foldl_cons]
      rw [run_fold_fst body counter L]
      rfl

/-- **`forBnd` as a pure state fold.** The loop runs once per cell of the bound
register, with the counter holding the (unary) iteration index. -/
theorem Cmd.eval_forBnd (counter bound : Var) (body : Cmd) (s : State) :
    (Cmd.forBnd counter bound body).eval s
      = Cmd.foldlState body counter (List.range (s.get bound).length) s := by
  show (Cmd.run (Cmd.forBnd counter bound body) s).1 = _
  simp only [Cmd.run]
  exact run_fold_fst body counter (List.range (s.get bound).length) s 0

/-- **Loop invariant principle.** If a motive `M` holds at the start (`M 0 s`)
and every iteration preserves it (`hstep`), then it holds of the whole loop's
result over `List.range n` (`M n`). The workhorse for verifying loop-based
programs without unfolding the `foldl` by hand. -/
theorem Cmd.foldlState_range_induct (body : Cmd) (counter : Var) (n : Nat) (s : State)
    (M : Nat → State → Prop) (h0 : M 0 s)
    (hstep : ∀ i st, i < n → M i st →
      M (i + 1) (body.eval (st.set counter (List.replicate i 1)))) :
    M n (Cmd.foldlState body counter (List.range n) s) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
      rw [List.range_succ, Cmd.foldlState, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      refine hstep n _ (Nat.lt_succ_self n) ?_
      exact ih (fun i st hi hM => hstep i st (Nat.lt_succ_of_lt hi) hM)

/-- **Loop frame.** A loop whose body and counter touch only registers `< k`
preserves every register `≥ k` — so an output/result register at index `≥ k`
survives the loop. Proved from the invariant principle + the per-`Cmd` frame
lemma. -/
theorem Cmd.foldlState_frame (body : Cmd) (counter : Var) (n : Nat) (s : State)
    (k : Nat) (hcnt : counter < k) (hbody : Cmd.UsesBelow body k)
    (r : Var) (hr : k ≤ r) :
    (Cmd.foldlState body counter (List.range n) s).get r = s.get r := by
  refine Cmd.foldlState_range_induct body counter n s
    (fun _ st => st.get r = s.get r) rfl ?_
  intro i st _ hM
  rw [Cmd.eval_get_frame body k hbody _ r hr,
    State.get_set_ne _ _ _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hcnt hr))]
  exact hM

/-- The cost-carrying loop fold (the `forBnd` accumulator: state and running
cost). Its state component is `foldlState`; its cost component is what
`Cmd.cost_forBnd_le` bounds. -/
private def costFold (body : Cmd) (counter : Var) :
    State × Nat → Nat → State × Nat :=
  fun acc i => (body.eval (acc.1.set counter (List.replicate i 1)),
    acc.2 + body.cost (acc.1.set counter (List.replicate i 1)))

/-- **Loop cost bound.** If a motive `M` is a valid loop invariant (`hM`) and it
implies a *uniform* per-iteration body-cost bound `B` (`hC`), then the whole loop
costs at most `1 + iters · B`. The cost counterpart of the invariant principle:
the standard way to bound a loop-based program's running time (pair it with
`Cmd.eval_forBnd` + `Cmd.foldlState_range_induct` sharing the same `M`). -/
theorem Cmd.cost_forBnd_le (counter bound : Var) (body : Cmd) (s : State) (B : Nat)
    (M : Nat → State → Prop) (h0 : M 0 s)
    (hM : ∀ i st, i < (s.get bound).length → M i st →
        M (i + 1) (body.eval (st.set counter (List.replicate i 1))))
    (hC : ∀ i st, i < (s.get bound).length → M i st →
        body.cost (st.set counter (List.replicate i 1)) ≤ B) :
    (Cmd.forBnd counter bound body).cost s ≤ 1 + (s.get bound).length * B := by
  have key : ∀ n, n ≤ (s.get bound).length →
      M n ((List.range n).foldl (costFold body counter) (s, 0)).1
        ∧ ((List.range n).foldl (costFold body counter) (s, 0)).2 ≤ n * B := by
    intro n
    induction n with
    | zero => intro _; exact ⟨h0, by simp⟩
    | succ n ih =>
        intro hn
        have hnlt : n < (s.get bound).length := hn
        obtain ⟨hMn, hcn⟩ := ih (Nat.le_of_succ_le hn)
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        refine ⟨hM n _ hnlt hMn, ?_⟩
        have hb := hC n _ hnlt hMn
        show ((List.range n).foldl (costFold body counter) (s, 0)).2
            + body.cost (((List.range n).foldl (costFold body counter) (s, 0)).1.set counter
                (List.replicate n 1)) ≤ (n + 1) * B
        rw [Nat.succ_mul]
        omega
  have hcost : (Cmd.forBnd counter bound body).cost s
      = 1 + ((List.range (s.get bound).length).foldl (costFold body counter) (s, 0)).2 := rfl
  rw [hcost]
  have := (key (s.get bound).length (Nat.le_refl _)).2
  omega

end Complexity.Lang
