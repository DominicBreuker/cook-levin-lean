import Complexity.Lang.Syntax

set_option autoImplicit false

/-! # Lang semantics (skeleton)

Denotational and cost semantics of the layer's commands. The
definitions are deferred to Part 3.2 of `ROADMAP.md`; the skeleton
commits to the *signatures* and key algebraic laws.

The natural implementation is mutually recursive: `eval` and `cost`
descend on `Cmd` structurally, but `forBnd`'s loop iterates over a
runtime-determined bound. The clean shape is

```lean
def Cmd.run : Cmd → State → State × Nat
  | .op o, s             => (Op.eval o s, Op.cost o s)
  | .seq c1 c2, s        =>
      let (s', n1) := Cmd.run c1 s
      let (s'', n2) := Cmd.run c2 s'
      (s'', 1 + n1 + n2)
  | .ifBit t c1 c2, s    =>
      let (s', n) :=
        if (s.get t) = [1] then Cmd.run c1 s else Cmd.run c2 s
      (s', 1 + n)
  | .forBnd cnt bnd b, s =>
      ((List.range (s.get bnd).length).foldl ...)
```

which is structurally recursive on `Cmd` (Lean accepts the foldl
because the body recurses on a smaller `Cmd`). It is deferred to
Part 3.2 so the skeleton does not commit to specific syntactic
choices (e.g. is `seq`'s cost `n1 + n2` or `1 + n1 + n2`?).
-/

namespace Complexity.Lang

/-! ## Operation semantics (concrete) -/

/-- Denotational semantics of an operation. -/
def Op.eval : Op → State → State
  | .clear      dst, s          => s.set dst []
  | .appendOne  dst, s          => s.set dst (s.get dst ++ [1])
  | .appendZero dst, s          => s.set dst (s.get dst ++ [0])
  | .copy       dst src, s      => s.set dst (s.get src)
  | .tail       dst src, s      => s.set dst (s.get src).tail
  | .head       dst src, s      =>
      s.set dst (match s.get src with | [] => [] | x :: _ => [x])
  | .eqBit      dst src1 src2, s =>
      s.set dst (if s.get src1 = s.get src2 then [1] else [0])
  | .nonEmpty   dst src, s      =>
      s.set dst (if (s.get src).isEmpty then [0] else [1])
  | .takeAt     dst src lenReg, s =>
      s.set dst ((s.get src).take ((s.get lenReg).headD 0))
  | .dropAt     dst src lenReg, s =>
      s.set dst ((s.get src).drop ((s.get lenReg).headD 0))
  | .concat     dst src1 src2, s =>
      s.set dst (s.get src1 ++ s.get src2)
  | .consLen    dst lenSrc src, s =>
      s.set dst ((s.get lenSrc).length :: s.get src)

/-- Cost of an operation — a **realistic** (size-aware) cost model.

Each op costs `1` for the control step plus the length of any **source data it
must read and re-materialise**. The size-increasing ops (`copy`, `tail`,
`takeAt`, `dropAt`, `concat`, `consLen`) therefore charge for their output, so
that cost dominates the per-step size growth (`Op.size_eval_le`). `eqBit` also
charges `|src1|+|src2|`: even though it only *writes* one cell, the compiled
register-equality tester copies and consumes both source registers, leaving a
`|src1|+|src2|` residue on the tape that the factor-1 W-invariant of the
physical-residue contract can only absorb if `Op.cost` accounts for it. This is the
fix for the cost-model gap: under the previous unit-cost model `concat`/`copy`
could grow `State.size` multiplicatively in one step, making the layer cost an
unfaithful proxy for the compiled TM's running time (output size — hence TM
steps — could be exponential in layer cost). With this cost the global invariant
`State.size (Op.eval o s) ≤ State.size s + Op.cost o s` holds. The ops that only
write `O(1)` cells and read no register data (`clear`, `appendOne/Zero`, `head`,
`nonEmpty`) remain unit cost. This mirrors the L-calculus cost the Coq port
extracts from. -/
def Op.cost : Op → State → Nat
  | .clear      _,            _ => 1
  | .appendOne  _,            _ => 1
  | .appendZero _,            _ => 1
  | .copy       _ src,        s => (s.get src).length + 1
  | .tail       _ src,        s => (s.get src).length + 1
  | .head       _ _,          _ => 1
  | .eqBit      _ src1 src2,  s => (s.get src1).length + (s.get src2).length + 1
  | .nonEmpty   _ _,          _ => 1
  | .takeAt     _ src _,      s => (s.get src).length + 1
  | .dropAt     _ src _,      s => (s.get src).length + 1
  | .concat     _ src1 src2,  s => (s.get src1).length + (s.get src2).length + 1
  | .consLen    _ _ src,      s => (s.get src).length + 1

/-! ## Size accounting (the cost-model soundness invariant)

`State.size_set_add` is the exact bookkeeping identity for `State.set`; from it
`Op.size_eval_le` shows each op's realistic cost dominates its size growth.
`Op.size_eval_le` is the invariant that was **false** under the old unit-cost
model (e.g. `concat dst src src` with empty `dst` grew size by `2·|src|` at cost
`1`); it now holds, validating the cost model. -/

/-- `State.set` on an in-range index is exactly `List.set`; its size obeys the
balance `size(set) + |old| = size + |new|`. -/
private theorem State.size_set_lt :
    ∀ (l : State) (i : Nat) (h : i < l.length) (v : List Nat),
      State.size (List.set l i v) + (l[i]'h).length = State.size l + v.length
  | [], _, h, _ => absurd h (by simp)
  | a :: t, 0, _, v => by
      simp only [List.set_cons_zero, List.getElem_cons_zero, State.size,
        List.map_cons, List.foldr_cons]
      omega
  | a :: t, i + 1, h, v => by
      have ih := State.size_set_lt t i (by simpa using h) v
      simp only [List.set_cons_succ, List.getElem_cons_succ, State.size,
        List.map_cons, List.foldr_cons]
      simp only [State.size] at ih
      omega

private theorem State.size_append (a b : State) :
    State.size (a ++ b) = State.size a + State.size b := by
  induction a with
  | nil => simp [State.size]
  | cons x t ih =>
      simp only [List.cons_append, State.size, List.map_cons, List.foldr_cons] at ih ⊢
      omega

private theorem State.size_replicate_nil (k : Nat) :
    State.size (List.replicate k ([] : List Nat)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, State.size, List.map_cons, List.foldr_cons,
        List.length_nil] at ih ⊢
      omega

/-- **Size balance for `State.set`.** Writing `v` to register `dst` changes the
total size by `|v| − |old dst|`: `size(set) + |old| = size + |v|`. Holds in both
the in-range and the padding branch (padding registers are `[]`, size `0`). -/
theorem State.size_set_add (s : State) (dst : Var) (v : List Nat) :
    State.size (s.set dst v) + (s.get dst).length = State.size s + v.length := by
  by_cases h : dst < s.length
  · have hget : (s.get dst).length = (s[dst]'h).length := by
      unfold State.get; rw [List.getElem?_eq_getElem h]; rfl
    rw [hget, show s.set dst v = List.set s dst v from by unfold State.set; rw [if_pos h]]
    exact State.size_set_lt s dst h v
  · have hge : s.length ≤ dst := Nat.le_of_not_lt h
    have hget : (s.get dst).length = 0 := by
      unfold State.get; rw [List.getElem?_eq_none hge]; rfl
    have hlen_pad :
        dst < (s ++ List.replicate (dst + 1 - s.length) ([] : List Nat)).length := by
      rw [List.length_append, List.length_replicate,
        Nat.add_sub_cancel' (Nat.le_succ_of_le hge)]
      exact Nat.lt_succ_self dst
    have hpad_elem :
        (s ++ List.replicate (dst + 1 - s.length) ([] : List Nat))[dst]'hlen_pad = [] := by
      rw [List.getElem_append_right hge]
      exact List.getElem_replicate _
    have hbal :=
      State.size_set_lt (s ++ List.replicate (dst + 1 - s.length) ([] : List Nat)) dst hlen_pad v
    have hsize_pad :
        State.size (s ++ List.replicate (dst + 1 - s.length) ([] : List Nat)) = State.size s := by
      rw [State.size_append, State.size_replicate_nil, Nat.add_zero]
    rw [hget, show s.set dst v
          = List.set (s ++ List.replicate (dst + 1 - s.length) ([] : List Nat)) dst v from by
          unfold State.set; rw [if_neg h]]
    rw [hpad_elem, List.length_nil] at hbal
    omega

/-- Convenience: if `|v| ≤ c + |old dst|` then writing `v` costs at most `c` in
size. The per-op specialisation of `State.size_set_add`. -/
private theorem State.size_set_le_cost (s : State) (dst : Var) (v : List Nat) (c : Nat)
    (hv : v.length ≤ c + (s.get dst).length) :
    State.size (s.set dst v) ≤ State.size s + c := by
  have h := State.size_set_add s dst v
  omega

/-- **Cost-model soundness (op level).** The realistic `Op.cost` dominates the
per-op size growth: `size(Op.eval o s) ≤ size s + Op.cost o s`. This is the
invariant the budget needs and the one the old unit-cost model violated. -/
theorem Op.size_eval_le (o : Op) (s : State) :
    State.size (Op.eval o s) ≤ State.size s + Op.cost o s := by
  cases o with
  | clear dst => exact State.size_set_le_cost s dst [] 1 (by simp)
  | appendOne dst =>
      exact State.size_set_le_cost s dst _ 1
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  | appendZero dst =>
      exact State.size_set_le_cost s dst _ 1
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  | copy dst src =>
      exact State.size_set_le_cost s dst _ ((s.get src).length + 1) (by omega)
  | tail dst src =>
      refine State.size_set_le_cost s dst _ ((s.get src).length + 1) ?_
      have : (s.get src).tail.length ≤ (s.get src).length := by
        rw [List.length_tail]; omega
      omega
  | head dst src =>
      refine State.size_set_le_cost s dst _ 1 ?_
      rcases s.get src with _ | ⟨x, xs⟩ <;> simp
  | eqBit dst s1 s2 =>
      refine State.size_set_le_cost s dst _ ((s.get s1).length + (s.get s2).length + 1) ?_
      by_cases hh : s.get s1 = s.get s2
      · rw [if_pos hh]; simp only [List.length_cons, List.length_nil]; omega
      · rw [if_neg hh]; simp only [List.length_cons, List.length_nil]; omega
  | nonEmpty dst src =>
      refine State.size_set_le_cost s dst _ 1 ?_
      by_cases hh : (s.get src).isEmpty <;> simp [hh]
  | takeAt dst src len =>
      refine State.size_set_le_cost s dst _ ((s.get src).length + 1) ?_
      have : ((s.get src).take ((s.get len).headD 0)).length ≤ (s.get src).length :=
        by rw [List.length_take]; omega
      omega
  | dropAt dst src len =>
      refine State.size_set_le_cost s dst _ ((s.get src).length + 1) ?_
      have : ((s.get src).drop ((s.get len).headD 0)).length ≤ (s.get src).length :=
        by rw [List.length_drop]; omega
      omega
  | concat dst s1 s2 =>
      refine State.size_set_le_cost s dst _ ((s.get s1).length + (s.get s2).length + 1) ?_
      rw [List.length_append]; omega
  | consLen dst lenSrc src =>
      refine State.size_set_le_cost s dst _ ((s.get src).length + 1) ?_
      rw [List.length_cons]; omega

/-! ## Command semantics (concrete, via `Cmd.run`)

`Cmd.run c s` returns the post-state and the accumulated cost. The
single-pass shape avoids a mutual recursion between `eval` and
`cost` and is structurally recursive on `Cmd` (the `forBnd` body
recurses on a structurally smaller `Cmd`).

`Cmd.eval` and `Cmd.cost` are the projections. -/

/-- Run a command. The pair is `(post-state, total-cost)`. -/
def Cmd.run : Cmd → State → State × Nat
  | .op o,                 s =>
      (Op.eval o s, Op.cost o s)
  | .seq c1 c2,            s =>
      let r1 := Cmd.run c1 s
      let r2 := Cmd.run c2 r1.1
      (r2.1, 1 + r1.2 + r2.2)
  | .ifBit test cT cE,     s =>
      let r := if s.get test = [1] then Cmd.run cT s else Cmd.run cE s
      (r.1, 1 + r.2)
  | .forBnd counter bound body, s =>
      let iters := (s.get bound).length
      let final := (List.range iters).foldl
        (fun acc i =>
          let s' := acc.1.set counter (List.replicate i 1)
          let r := Cmd.run body s'
          (r.1, acc.2 + r.2))
        (s, 0)
      -- `iters * iters` charges for materialising the unary loop counter
      -- `replicate i 1` (size `i ≤ iters`) before each of the `iters`
      -- iterations. This is uncharged in the fold accumulator above, yet
      -- it is real size the loop writes (and real TM time: writing `i`
      -- unary cells costs `Θ(i)` steps), so without it the cost model is
      -- not a faithful proxy for output size — exactly the cost-model
      -- faithfulness principle behind the size-aware `Op.cost`. With it,
      -- `Cmd.size_eval_le` (`size (eval) ≤ size + cost`) holds for `forBnd`
      -- too (the lump `iters*iters ≥ Σ_{i<iters} i` dominates the counter's
      -- cumulative size growth). See `Cmd.size_eval_le`.
      (final.1, 1 + final.2 + iters * iters)

/-- Denotational semantics of a command. -/
def Cmd.eval (c : Cmd) (s : State) : State := (Cmd.run c s).1

/-- Cost (= number of primitive operations executed) of running a
command on a state. -/
def Cmd.cost (c : Cmd) (s : State) : Nat := (Cmd.run c s).2

/-! ## Compositional laws

These follow by definitional unfolding from the `Cmd.run`-based
semantics above. -/

theorem Cmd.eval_op (o : Op) (s : State) :
    (Cmd.op o).eval s = Op.eval o s := rfl

theorem Cmd.eval_seq (c1 c2 : Cmd) (s : State) :
    (c1 ;; c2).eval s = c2.eval (c1.eval s) := rfl

theorem Cmd.eval_ifBit_true (t : Var) (cT cE : Cmd) (s : State)
    (h : s.get t = [1]) :
    (Cmd.ifBit t cT cE).eval s = cT.eval s := by
  show (Cmd.run (.ifBit t cT cE) s).1 = (Cmd.run cT s).1
  simp [Cmd.run, h]

theorem Cmd.eval_ifBit_false (t : Var) (cT cE : Cmd) (s : State)
    (h : s.get t ≠ [1]) :
    (Cmd.ifBit t cT cE).eval s = cE.eval s := by
  show (Cmd.run (.ifBit t cT cE) s).1 = (Cmd.run cE s).1
  simp [Cmd.run, h]

theorem Cmd.cost_op (o : Op) (s : State) :
    (Cmd.op o).cost s = Op.cost o s := rfl

theorem Cmd.cost_seq (c1 c2 : Cmd) (s : State) :
    (c1 ;; c2).cost s = 1 + c1.cost s + c2.cost (c1.eval s) := rfl

theorem Cmd.cost_ifBit_true (t : Var) (cT cE : Cmd) (s : State) (h : s.get t = [1]) :
    (Cmd.ifBit t cT cE).cost s = 1 + cT.cost s := by
  show (Cmd.run (.ifBit t cT cE) s).2 = 1 + (Cmd.run cT s).2
  simp [Cmd.run, h]

theorem Cmd.cost_ifBit_false (t : Var) (cT cE : Cmd) (s : State) (h : s.get t ≠ [1]) :
    (Cmd.ifBit t cT cE).cost s = 1 + cE.cost s := by
  show (Cmd.run (.ifBit t cT cE) s).2 = 1 + (Cmd.run cE s).2
  simp [Cmd.run, h]

/-! ## Cost-model soundness (command level)

`Op.size_eval_le` lifts to the whole command: the (realistic, size-aware) cost
dominates the size growth of every command. The `forBnd` case is exactly why
`Cmd.run` charges `iters * iters` for the loop counter — the bound is **false**
without that charge (witness: `forBnd 0 1 (op (appendOne 2))` on
`[[], replicate n 1, []]` has output size `3n−1`, but `size + (uncharged cost) =
2n+1`). The clean linear bound below is the invariant the compiler's tape-length
budget rests on (every intermediate tape in a `Compile c` run is `encodeTape` of
a sub-evaluation, whose size this bounds by `size s + cost`). -/

/-- **Loop-fold size invariant** (helper for `Cmd.size_eval_le`'s `forBnd` case).
After `n ≤ iters` iterations of the cost-carrying loop fold, the state size is
bounded by the input size, the accumulated body cost, and `n * iters` of counter
headroom. The `n * iters` term absorbs the per-iteration counter set (which
writes `replicate i 1`, size `i < iters`); at `n = iters` it matches the
`iters * iters` lump that `Cmd.run` charges for the loop. Stated as a `private`
helper because `set` is unavailable in this core-only file (so the fold is
written out explicitly). -/
private theorem Cmd.size_run_foldl_le (body : Cmd) (cnt : Var)
    (hbody : ∀ t, State.size (body.eval t) ≤ State.size t + body.cost t)
    (s : State) (iters : Nat) :
    ∀ n, n ≤ iters →
      State.size ((List.range n).foldl
          (fun acc i =>
            let s' := acc.1.set cnt (List.replicate i 1)
            let r := Cmd.run body s'
            (r.1, acc.2 + r.2)) (s, 0)).1
        ≤ State.size s
          + ((List.range n).foldl
              (fun acc i =>
                let s' := acc.1.set cnt (List.replicate i 1)
                let r := Cmd.run body s'
                (r.1, acc.2 + r.2)) (s, 0)).2
          + n * iters := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have hnlt : n < iters := hn
      have ihn := ih (Nat.le_of_succ_le hn)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      -- The counter set adds at most `n` to the size (`State.size_set_add`).
      have hset := State.size_set_add
        (((List.range n).foldl
          (fun acc i =>
            let s' := acc.1.set cnt (List.replicate i 1)
            let r := Cmd.run body s'
            (r.1, acc.2 + r.2)) (s, 0)).1) cnt (List.replicate n 1)
      rw [List.length_replicate] at hset
      -- The body grows size by at most its cost (`hbody`).
      have hb := hbody
        (((List.range n).foldl
          (fun acc i =>
            let s' := acc.1.set cnt (List.replicate i 1)
            let r := Cmd.run body s'
            (r.1, acc.2 + r.2)) (s, 0)).1.set cnt (List.replicate n 1))
      -- Expose the fold step's projections as `body.eval` / `body.cost` (defeq:
      -- `(Cmd.run body s').1 = body.eval s'`, `.2 = body.cost s'`).
      show State.size (body.eval
              (((List.range n).foldl
                (fun acc i =>
                  let s' := acc.1.set cnt (List.replicate i 1)
                  let r := Cmd.run body s'
                  (r.1, acc.2 + r.2)) (s, 0)).1.set cnt (List.replicate n 1)))
          ≤ State.size s
            + (((List.range n).foldl
                (fun acc i =>
                  let s' := acc.1.set cnt (List.replicate i 1)
                  let r := Cmd.run body s'
                  (r.1, acc.2 + r.2)) (s, 0)).2
              + body.cost
                (((List.range n).foldl
                  (fun acc i =>
                    let s' := acc.1.set cnt (List.replicate i 1)
                    let r := Cmd.run body s'
                    (r.1, acc.2 + r.2)) (s, 0)).1.set cnt (List.replicate n 1)))
            + (n + 1) * iters
      rw [Nat.succ_mul]
      omega

/-- **Cost-model soundness (command level).** The size of `c.eval s` is bounded
by the input size plus the running cost: `size (c.eval s) ≤ size s + c.cost s`.
Proved by induction on `c`; the `forBnd` case uses the counter charge in
`Cmd.run` (a per-iteration `+ iters` of size headroom, lumped as `iters*iters`)
to absorb the unary counter the loop materialises. -/
theorem Cmd.size_eval_le (c : Cmd) (s : State) :
    State.size (c.eval s) ≤ State.size s + c.cost s := by
  induction c generalizing s with
  | op o => exact Op.size_eval_le o s
  | seq c1 c2 ih1 ih2 =>
      rw [Cmd.eval_seq, Cmd.cost_seq]
      have h1 := ih1 s
      have h2 := ih2 (c1.eval s)
      omega
  | ifBit t cT cE ihT ihE =>
      by_cases hb : s.get t = [1]
      · rw [Cmd.eval_ifBit_true t cT cE s hb, Cmd.cost_ifBit_true t cT cE s hb]
        have := ihT s; omega
      · rw [Cmd.eval_ifBit_false t cT cE s hb, Cmd.cost_ifBit_false t cT cE s hb]
        have := ihE s; omega
  | forBnd cnt bnd body ihbody =>
      have key := Cmd.size_run_foldl_le body cnt ihbody s (s.get bnd).length
        (s.get bnd).length (Nat.le_refl _)
      -- `eval`/`cost` of `forBnd` are the fold's `.1` / `1 + .2 + iters*iters`.
      show State.size ((List.range (s.get bnd).length).foldl
              (fun acc i =>
                let s' := acc.1.set cnt (List.replicate i 1)
                let r := Cmd.run body s'
                (r.1, acc.2 + r.2)) (s, 0)).1
          ≤ State.size s
            + (1 + ((List.range (s.get bnd).length).foldl
                (fun acc i =>
                  let s' := acc.1.set cnt (List.replicate i 1)
                  let r := Cmd.run body s'
                  (r.1, acc.2 + r.2)) (s, 0)).2
              + (s.get bnd).length * (s.get bnd).length)
      omega

/-! ## Output projection

The Boolean output of running `c` on `s` is `(c.eval s).isAccept`. -/

/-- A program *decides* a predicate `P` if running it from `encode x`
ends in an accepting state when `P x` and a rejecting state otherwise.
The encoding is a parameter of the witness; cf. `Lang.PolyTime.lean`. -/
def Cmd.decides {X : Type} (c : Cmd) (encode : X → State) (P : X → Prop) : Prop :=
  ∀ x, (P x ↔ (c.eval (encode x)).isAccept) ∧
       (¬ P x ↔ (c.eval (encode x)).isReject)

end Complexity.Lang
