import CookLevin.Basic.Definitions

set_option autoImplicit false

/-! # Turing machines on bit strings

Conventions for running a Turing machine (`FlatTM`, `Basic/MachineSemantics.lean`) on
bit strings. A string `x : List Bool` is written on the single tape as

    3, s₁, …, sₙ, 0, 3      with `sᵢ = 1` if `xᵢ = false` and `sᵢ = 2` if `xᵢ = true`,

one symbol per bit, followed by the delimiter `0` and enclosed in the end markers `3`.
A pair `(x, c)` is written as `3, sym x, 0, sym c, 0, 3`. The output of a halted machine
is read back the same way: after the leading marker, the symbols up to the first `0` or
`3` are the output, `2` standing for `true` and any other symbol for `false`.

With these conventions the file defines polynomial-time computability of a function on
strings, polynomial-time many-one reducibility `⪯p`, and the class NP in its verifier
form. These are the notions the main theorem is stated with.
-/

namespace CookLevin

/-- One tape symbol per bit: `false ↦ 1`, `true ↦ 2`. -/
def symbolsOf (x : List Bool) : List Nat := x.map (fun b => if b then 2 else 1)

/-- The tape holding the bit string `x`. -/
def stringTape (x : List Bool) : List Nat := 3 :: (symbolsOf x ++ [0, 3])

/-- The tape holding the pair of bit strings `(x, c)`. -/
def pairTape (x c : List Bool) : List Nat :=
  3 :: (symbolsOf x ++ [0] ++ symbolsOf c ++ [0, 3])

/-- The bit string a halted machine has written on tape `0`: skip the leading marker and
read the symbols up to the first `0` or `3`; `2` is `true`, any other symbol `false`. -/
def outputString (cfg : FlatTMConfig) : List Bool :=
  match cfg.tapes with
  | [] => []
  | (_, _, right) :: _ =>
      ((right.tail.takeWhile (· != 3)).takeWhile (· != 0)).map (· == 2)

/-- `M` computes `f` within time `t`: started on the tape holding `x`, it reaches a halting
state within `t x.length` steps, with `f x` written on the tape. -/
def computesInTime (M : FlatTM) (f : List Bool → List Bool) (t : Nat → Nat) : Prop :=
  ∀ x, ∃ cfg,
    runFlatTM (t x.length) M (initFlatConfig M [stringTape x]) = some cfg ∧
    haltingStateReached M cfg = true ∧
    outputString cfg = f x

/-- `M` decides the relation `R` on pairs of strings within time `t`: started on the tape
holding `(x, c)`, it reaches a halting state within `t (x.length + c.length)` steps; that
state is `acc` exactly when `R x c` holds and `rej` exactly when it does not. -/
def decidesPairInTime (M : FlatTM) (acc rej : Nat) (R : List Bool → List Bool → Prop)
    (t : Nat → Nat) : Prop :=
  ∀ x c, ∃ cfg,
    runFlatTM (t (x.length + c.length)) M (initFlatConfig M [pairTape x c]) = some cfg ∧
    haltingStateReached M cfg = true ∧
    (R x c ↔ cfg.state_idx = acc) ∧
    (¬ R x c ↔ cfg.state_idx = rej)

/-- **Polynomial-time many-one reducibility.** `Q ⪯p P` holds when some function `f`,
computed by a valid single-tape Turing machine in polynomial time, satisfies
`x ∈ Q ↔ f x ∈ P` for every string `x`. -/
def reducesPoly (Q P : List Bool → Prop) : Prop :=
  ∃ (f : List Bool → List Bool) (t : Nat → Nat) (M : FlatTM),
    inOPoly t ∧ validFlatTM M ∧ M.tapes = 1 ∧ computesInTime M f t ∧
    ∀ x, Q x ↔ P (f x)

@[inherit_doc] infix:50 " ⪯p " => reducesPoly

/-- **The class NP** (verifier form). `Q` is in NP when there are a relation `R` on pairs
of strings, polynomials `p` and `t`, and a valid single-tape Turing machine `M` deciding
`R` within time `t`, such that `x ∈ Q` iff some certificate `c` of length at most
`p x.length` satisfies `R x c`. -/
def inNP (Q : List Bool → Prop) : Prop :=
  ∃ (R : List Bool → List Bool → Prop) (p t : Nat → Nat) (M : FlatTM) (acc rej : Nat),
    inOPoly p ∧ inOPoly t ∧ validFlatTM M ∧ M.tapes = 1 ∧
    (∀ x, Q x ↔ ∃ c, c.length ≤ p x.length ∧ R x c) ∧
    decidesPairInTime M acc rej R t

/-! ## `encodable.size` of a bit string

`encodable.size` (`Basic/Definitions.lean`) is the size measure the layer's cost bounds
are stated in. On bit strings it is between the length and twice the length. -/

theorem size_le_two_mul_length (x : List Bool) : encodable.size x ≤ 2 * x.length := by
  show x.foldl (fun acc b => acc + encodable.size b + 1) 0 ≤ 2 * x.length
  have key : ∀ (l : List Bool) (acc : Nat),
      l.foldl (fun acc b => acc + encodable.size b + 1) acc ≤ acc + 2 * l.length := by
    intro l
    induction l with
    | nil => intro acc; exact Nat.le_of_eq (by simp)
    | cons b t ih =>
        intro acc
        have hb : encodable.size b ≤ 1 := by
          cases b
          · exact Nat.zero_le 1
          · exact Nat.le_refl 1
        have h := ih (acc + encodable.size b + 1)
        simp only [List.foldl_cons, List.length_cons]
        omega
  have := key x 0
  omega

theorem length_le_size (x : List Bool) : x.length ≤ encodable.size x := by
  show x.length ≤ x.foldl (fun acc b => acc + encodable.size b + 1) 0
  have key : ∀ (l : List Bool) (acc : Nat),
      acc + l.length ≤ l.foldl (fun acc b => acc + encodable.size b + 1) acc := by
    intro l
    induction l with
    | nil => intro acc; exact Nat.le_of_eq (by simp)
    | cons b t ih =>
        intro acc
        have h := ih (acc + encodable.size b + 1)
        simp only [List.foldl_cons, List.length_cons]
        omega
  have := key x 0
  omega

end CookLevin
