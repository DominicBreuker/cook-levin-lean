import Complexity.Complexity.MachineSemantics

set_option autoImplicit false

/-! # The DSL skeleton (Part 3 of `ROADMAP.md`)

A small structured while-language with explicit cost semantics. The
language is the Lean analogue of the Coq port's L calculus: programs
are written here, a single one-time compiler emits `FlatTM`s, and
every downstream verifier / reduction is a short program in the
layer rather than a hand-rolled TM.

Skeleton status: types are concrete; `eval`, `cost`, and `Compile`
have committed signatures but are deferred to Part 3.2 / 3.3 of the
roadmap (declared as `axiom`s in `Semantics.lean` and `Compile.lean`).
The point of the skeleton is to nail down the *interfaces* so any
gaps in the high-level architecture surface immediately. -/

namespace Complexity.Lang

/-- Register index. Programs read and write a finite list of
"registers", each of which holds a `List Nat`. -/
abbrev Var := Nat

/-- The state of a Lang program: a list of registers, each a `List Nat`.

By convention, **register 0 holds the program's output**: the program
"accepts" iff register 0 contains `[1]` after evaluation and "rejects"
iff it contains `[0]`. Inputs are placed in registers 1, 2, …. -/
abbrev State := List (List Nat)

namespace State

/-- Read register `v`, returning `[]` if unset. -/
def get (s : State) (v : Var) : List Nat := (s[v]?).getD []

/-- Write `val` to register `v`, extending the state with `[]`-padding
if `v` is past the current length. -/
def set (s : State) (v : Var) (val : List Nat) : State :=
  if v < s.length then List.set s v val
  else
    let padded := s ++ List.replicate (v + 1 - s.length) []
    List.set padded v val

/-- The aggregate size of a state — used to express polynomial cost
bounds. -/
def size (s : State) : Nat := (s.map List.length).foldr (· + ·) 0

end State

/-- Primitive operations on the state. Each `Op` evaluates in unit
cost. Programs compose `Op`s via `Cmd.op`. -/
inductive Op : Type where
  /-- `clear dst` : `s[dst] := []` -/
  | clear  (dst : Var)
  /-- `appendOne dst` : `s[dst] := s[dst] ++ [1]` (used to extend a
  unary counter by one). -/
  | appendOne (dst : Var)
  /-- `appendZero dst` : `s[dst] := s[dst] ++ [0]` -/
  | appendZero (dst : Var)
  /-- `copy dst src` : `s[dst] := s[src]` -/
  | copy   (dst src : Var)
  /-- `tail dst src` : `s[dst] := (s[src]).tail` -/
  | tail   (dst src : Var)
  /-- `head dst src` : `s[dst] := if s[src] is empty then [] else [s[src].head]` -/
  | head   (dst src : Var)
  /-- `eqBit dst src1 src2` : `s[dst] := [1]` if `s[src1] = s[src2]`,
  else `[0]`. -/
  | eqBit  (dst src1 src2 : Var)
  /-- `nonEmpty dst src` : `s[dst] := [1]` if `s[src]` is non-empty,
  else `[0]`. -/
  | nonEmpty (dst src : Var)
  /-- `takeAt dst src lenReg` : `s[dst] := (s[src]).take (head of s[lenReg])`.
  Length-as-value prefix extraction (the count is read from a register). -/
  | takeAt (dst src lenReg : Var)
  /-- `dropAt dst src lenReg` : `s[dst] := (s[src]).drop (head of s[lenReg])`. -/
  | dropAt (dst src lenReg : Var)
  /-- `concat dst src1 src2` : `s[dst] := s[src1] ++ s[src2]`. -/
  | concat (dst src1 src2 : Var)
  /-- `consLen dst lenSrc src` : `s[dst] := (length of s[lenSrc]) :: s[src]`.
  Prepends the length of one register (as a single cell) onto another. -/
  | consLen (dst lenSrc src : Var)
  deriving Repr, BEq

/-- Commands. The layer is a structured while-language with:
- primitive operations (`op`),
- sequencing (`seq`),
- conditional on a one-bit register (`ifBit`),
- counted iteration (`forBnd`) — iterates `body` once per element of
  register `bound`, placing the iteration index (in unary, i.e.
  `List.replicate i 1`) into register `counter`.

`forBnd`'s bound is read from a register, not computed: the layer is
**total** by construction, and cost is closed-form in the input size. -/
inductive Cmd : Type where
  | op       (o : Op)
  | seq      (c1 c2 : Cmd)
  | ifBit    (test : Var) (cThen cElse : Cmd)
  | forBnd   (counter bound : Var) (body : Cmd)
  deriving Repr

/-- Sequencing notation. -/
infixr:30 " ;; " => Cmd.seq

/-- **`forBnd` nesting depth** — the number of loop levels along the deepest
path of the command. Drives the compiler's static scratch-register assignment
(Risk C2/C3): a `forBnd` compiled at scratch base `sb` keeps its loop counts in
the two scratch registers `sb`, `sb + 1` (which the machine requires empty at
entry and restores to empty at exit) and compiles its body at scratch base
`sb + 2`, so a program compiled at base `sb` touches registers
`< sb + 2 * loopDepth` in total. Sequential/branching composition *reuses*
scratch (each loop restores its pair to `[]`), so the depth — not the loop
count — is what widens the register footprint. -/
def Cmd.loopDepth : Cmd → Nat
  | .op _               => 0
  | .seq c1 c2          => max c1.loopDepth c2.loopDepth
  | .ifBit _ cT cE      => max cT.loopDepth cE.loopDepth
  | .forBnd _ _ body    => body.loopDepth + 1

/-- **An `Op` whose soundness case in `compileOp_sound_physical_residue` is
discharged (9/12).** The value-as-length trio `takeAt`/`dropAt`/`consLen` is the
only unsupported set; their soundness cases are still `sorry` (gated on the unary
migration — HANDOFF bottom-up step 2). This predicate isolates the proven ops so
the *live* `sat_NP` decider path (whose program uses none of the trio) discharges
its op cases without touching the stub `sorry`s — see `Cmd.AllOpsSupported`. -/
def Op.IsSupported : Op → Prop
  | .takeAt _ _ _  => False
  | .dropAt _ _ _  => False
  | .consLen _ _ _ => False
  | _              => True

/-- A `Cmd` all of whose ops have a discharged soundness case (`Op.IsSupported`).
This is the wall that makes a *concrete* trio-free decider (e.g. `evalCnfCmd`)
yield a `sorry`-free `compileOp_sound_physical_residue` discharge, so its
`bitDecider_run` (and hence `SAT_inNP.sat_NP`) is axiom-clean even while the trio
remains stubbed. Strictly stronger than `Cmd.NoConsLen` (it also rules out
`takeAt`/`dropAt`); dropped once the trio is proven (HANDOFF bottom-up step 2–3,
Route B). -/
def Cmd.AllOpsSupported : Cmd → Prop
  | .op o            => Op.IsSupported o
  | .seq c1 c2       => Cmd.AllOpsSupported c1 ∧ Cmd.AllOpsSupported c2
  | .ifBit _ cT cE   => Cmd.AllOpsSupported cT ∧ Cmd.AllOpsSupported cE
  | .forBnd _ _ body => Cmd.AllOpsSupported body

/-- Output convention: a state `s` is `accept` iff register 0
contains exactly `[1]`. -/
def State.isAccept (s : State) : Bool := s.get 0 == [1]

/-- Output convention: a state `s` is `reject` iff register 0
contains exactly `[0]`. -/
def State.isReject (s : State) : Bool := s.get 0 == [0]

end Complexity.Lang
