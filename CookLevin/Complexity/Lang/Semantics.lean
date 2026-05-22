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

/-- Cost of an operation. Every primitive is unit cost in the
intended semantics. -/
def Op.cost (_ : Op) (_ : State) : Nat := 1

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
      (final.1, 1 + final.2)

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

/-! ## Output projection

The Boolean output of running `c` on `s` is `(c.eval s).isAccept`. -/

/-- A program *decides* a predicate `P` if running it from `encode x`
ends in an accepting state when `P x` and a rejecting state otherwise.
The encoding is a parameter of the witness; cf. `Lang.PolyTime.lean`. -/
def Cmd.decides {X : Type} (c : Cmd) (encode : X → State) (P : X → Prop) : Prop :=
  ∀ x, (P x ↔ (c.eval (encode x)).isAccept) ∧
       (¬ P x ↔ (c.eval (encode x)).isReject)

end Complexity.Lang
