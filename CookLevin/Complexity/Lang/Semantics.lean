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

/-- Denotational semantics of an operation. -/
axiom Op.eval : Op → State → State

/-- Cost of an operation. Always `1` in the intended semantics. -/
axiom Op.cost : Op → State → Nat

/-- Denotational semantics of a command.

**Deferred to Part 3.2.** See file docstring for the intended
shape. -/
axiom Cmd.eval : Cmd → State → State

/-- Cost (= number of primitive operations executed) of running a
command on a state.

**Deferred to Part 3.2.** The cost is required to satisfy the
compositional laws below; together with `eval`, this nails the
semantics to a unique implementation. -/
axiom Cmd.cost : Cmd → State → Nat

/-! ## Compositional laws

The compiler soundness theorem (Part 3.4) depends on these. They
are listed as theorems with `sorry` bodies so that any future
change to the semantics' definition must re-establish them. -/

theorem Cmd.eval_op (o : Op) (s : State) :
    (Cmd.op o).eval s = Op.eval o s := by
  sorry

theorem Cmd.eval_seq (c1 c2 : Cmd) (s : State) :
    (c1 ;; c2).eval s = c2.eval (c1.eval s) := by
  sorry

theorem Cmd.eval_ifBit_true (t : Var) (cT cE : Cmd) (s : State)
    (h : s.get t = [1]) :
    (Cmd.ifBit t cT cE).eval s = cT.eval s := by
  sorry

theorem Cmd.eval_ifBit_false (t : Var) (cT cE : Cmd) (s : State)
    (h : s.get t ≠ [1]) :
    (Cmd.ifBit t cT cE).eval s = cE.eval s := by
  sorry

theorem Cmd.cost_op (o : Op) (s : State) :
    (Cmd.op o).cost s = Op.cost o s := by
  sorry

theorem Cmd.cost_seq (c1 c2 : Cmd) (s : State) :
    (c1 ;; c2).cost s = 1 + c1.cost s + c2.cost (c1.eval s) := by
  sorry

/-! ## Output projection

The Boolean output of running `c` on `s` is `(c.eval s).isAccept`. -/

/-- A program *decides* a predicate `P` if running it from `encode x`
ends in an accepting state when `P x` and a rejecting state otherwise.
The encoding is a parameter of the witness; cf. `Lang.PolyTime.lean`. -/
def Cmd.decides {X : Type} (c : Cmd) (encode : X → State) (P : X → Prop) : Prop :=
  ∀ x, (P x ↔ (c.eval (encode x)).isAccept) ∧
       (¬ P x ↔ (c.eval (encode x)).isReject)

end Complexity.Lang
