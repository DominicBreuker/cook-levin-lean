set_option autoImplicit false

universe u v

class encodable (α : Sort u) : Prop where
  dummy : True := by
    trivial

instance instEncodableDefault (α : Sort u) : encodable α := ⟨by trivial⟩

abbrev finType := Type
abbrev flatTM := Unit
abbrev TM (_σ : Type) (_ : Nat) := Unit

abbrev var := Nat
abbrev literal := Bool × var
abbrev clause := List literal
abbrev cnf := List clause
abbrev assgn := List var

def evalVar (a : assgn) (v : var) : Bool := decide (v ∈ a)

inductive formula where
  | ftrue
  | fvar (v : var)
  | fand (φ ψ : formula)
  | forr (φ ψ : formula)
  | fneg (φ : formula)
deriving Repr, DecidableEq

structure FlatCC where
  Sigma : Nat
  offset : Nat
  width : Nat
  init : List Nat
  cards : List Unit
  final : List (List Nat)
  steps : Nat
deriving Repr

structure BinaryCC where
  offset : Nat
  width : Nat
  init : List Bool
  cards : List Unit
  final : List (List Bool)
  steps : Nat
deriving Repr

structure FlatTCC where
  Sigma : Nat
  init : List Nat
  cards : List Unit
  final : List (List Nat)
  steps : Nat
deriving Repr

abbrev CC := Unit
abbrev TCC := Unit
abbrev CCCard (_ : Type) := Unit
abbrev TCCCardP (_ : Type) := Unit
abbrev TCCCard (_ : Type) := Unit

abbrev fvertex := Nat
abbrev fedge := fvertex × fvertex
abbrev fgraph := Nat × List fedge

def fgraph_wf (_ : fgraph) : Prop := True

def list_ofFlatType (_ : Nat) (_ : List Nat) : Prop := True

def ofFlatType (_ _ : Nat) : Prop := True

def validFlatTM (_ : flatTM) : Prop := True

def isValidFlatTM (_ : flatTM) : Bool := true

def monotonic (_ : Nat → Nat) : Prop := True

def inOPoly (_ : Nat → Nat) : Prop := True

def computableTime' {α : Sort u} {β : Sort v} (_ : α) (_ : β) : Prop := True

def projT1 {α : Type u} {β : α → Type v} (x : Sigma β) : α := x.1

def index {F : Type} (_ : F) : Nat := 0
