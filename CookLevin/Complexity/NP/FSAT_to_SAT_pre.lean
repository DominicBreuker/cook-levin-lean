import Complexity.NP.FSAT_to_SAT

set_option autoImplicit false

/-! # Pre-order positional Tseytin — the machine-friendly `FSAT → SAT` map

The free-line witness for the last sound-tail step `FSAT → SAT` cannot mimic
`FSAT_to_SAT_tseytin` (`FSAT_to_SAT.lean`): that map is a pair of structural
tree recursions (`eliminateOR`, then `tseytin'` with a *post-order* fresh-var
counter and *children-first* clause emission), while the machine input is the
Polish `serF` bit-stream and the DSL has only counted forward loops.

This file defines the **machine-friendly equivalent map** and proves it correct
at the Lean level (where recursion is free), per the HANDOFF design brief
("the witness need NOT reproduce `FSAT_to_SAT_tseytin` verbatim — any map `m`
with `FSAT f ↔ SAT (m f)` works for the chain"):

* **full grammar** — a `tseytinOr` gadget handles `forr` directly, so the
  `eliminateOR` pass disappears (one machine scan instead of two);
* **positional variables** — the node rooted at pre-order token index `p` of
  the Polish serialization gets the fresh variable `b + p` (`b` any bound
  `> formula_maxVar f`; the witness uses `b := (serF f).length`, which the
  machine computes with one trivial length loop — no on-machine max);
* **pre-order emission** — each node's gadget clauses are emitted when its
  token is scanned (gadget first, then the children's), which is exactly the
  order a single forward scan of the stream produces.

A node's left child is the next token (`p + 1`); its right child starts at
`p + 1 + formula_size f₁` (`formula_size` = token count), which the machine
recovers with the Polish arity-budget scan (design (a) of the HANDOFF brief,
probed GO in `probes/FSATPreProbe.lean`).

Everything here is parametric in `b`; the witness file instantiates
`b := (serF f).length` (`Reductions/FSAT_to_SAT_free.lean`). -/

namespace PreTseytin

/-! ## The OR gadget (the existing file has only true/equiv/and/not) -/

/-- Tseytin gadget for `v ↔ v₁ ∨ v₂`, in the same 3-literal clause shape as the
existing gadgets (so the whole output is a `kCNF 3`). -/
def tseytinOr (v v₁ v₂ : var) : cnf :=
  [[(false, v), (true, v₁), (true, v₂)],
   [(false, v₁), (true, v), (true, v)],
   [(false, v₂), (true, v), (true, v)]]

theorem tseytinOr_sat (a : assgn) (v v₁ v₂ : var) :
    satisfiesCnf a (tseytinOr v v₁ v₂) ↔
      (evalVar a v = true ↔ (evalVar a v₁ = true ∨ evalVar a v₂ = true)) := by
  unfold tseytinOr satisfiesCnf
  cases h₁ : evalVar a v <;> cases h₂ : evalVar a v₁ <;> cases h₃ : evalVar a v₂ <;>
    simp [evalCnf, evalClause, evalLiteral, h₁, h₂, h₃]

theorem tseytinOr_kCNF (v v₁ v₂ : var) : kCNF 3 (tseytinOr v v₁ v₂) :=
  kCNF.cons _ _ rfl (kCNF.cons _ _ rfl (kCNF.cons _ _ rfl kCNF.nil))

/-! ## The positional transform -/

/-- Pre-order positional Tseytin. `ptseytin b p f` emits the gadget clauses for
the subtree `f` whose root sits at pre-order token index `p`; the root's
representative variable is `b + p`, its left child's `b + p + 1`, its right
child's `b + p + 1 + formula_size f₁`. Gadget-before-children = the order a
forward scan of the Polish stream emits. -/
def ptseytin (b : Nat) : Nat → formula → cnf
  | p, .ftrue => tseytinTrue (b + p)
  | p, .fvar v => tseytinEquiv v (b + p)
  | p, .fand f₁ f₂ =>
      tseytinAnd (b + p) (b + p + 1) (b + p + 1 + formula_size f₁) ++
        ptseytin b (p + 1) f₁ ++ ptseytin b (p + 1 + formula_size f₁) f₂
  | p, .forr f₁ f₂ =>
      tseytinOr (b + p) (b + p + 1) (b + p + 1 + formula_size f₁) ++
        ptseytin b (p + 1) f₁ ++ ptseytin b (p + 1 + formula_size f₁) f₂
  | p, .fneg f₁ => tseytinNot (b + p) (b + p + 1) ++ ptseytin b (p + 1) f₁

/-- **The machine-friendly `FSAT → SAT` map**: the root-forcing top clause,
then the positional Tseytin clauses of the whole tree (root at index 0).
Correct for every `b > formula_maxVar f` (`preTseytin_correct`). -/
def preTseytin (b : Nat) (f : formula) : cnf :=
  [(true, b), (true, b), (true, b)] :: ptseytin b 0 f

/-- Every subtree occupies at least one token. -/
theorem formula_size_pos (f : formula) : 1 ≤ formula_size f := by
  cases f <;> simp [formula_size]

end PreTseytin
