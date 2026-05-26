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

/-- A command reads and writes only registers `< k`. -/
def Cmd.UsesBelow : Cmd → Nat → Prop
  | .op o,                k => Op.UsesBelow o k
  | .seq c1 c2,           k => Cmd.UsesBelow c1 k ∧ Cmd.UsesBelow c2 k
  | .ifBit t cT cE,       k => t < k ∧ Cmd.UsesBelow cT k ∧ Cmd.UsesBelow cE k
  | .forBnd cnt bnd body, k => cnt < k ∧ bnd < k ∧ Cmd.UsesBelow body k

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

end Complexity.Lang
