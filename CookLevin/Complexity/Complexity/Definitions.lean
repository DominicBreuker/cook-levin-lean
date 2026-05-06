import Complexity.Complexity.MachineSemantics

set_option autoImplicit false

universe u v

class encodable (α : Sort u) where
  size : α → Nat
  size_ge_logical : ∀ x : α, ∃ n : Nat, size x ≥ n

instance instEncodableDefault (α : Sort u) : encodable α where
  size := fun _ => 0
  size_ge_logical := fun _ => ⟨0, by simp⟩

abbrev finType := Type
abbrev flatTM := FlatTM
abbrev TM (_σ : Type) (_ : Nat) := FlatTM

abbrev var := Nat
abbrev literal := Bool × var
abbrev clause := List literal
abbrev cnf := List clause
abbrev assgn := List var

def evalVar (a : assgn) (v : var) : Bool := decide (v ∈ a)

def assgnSubset (a a' : assgn) : Prop := ∀ ⦃v : var⦄, v ∈ a → v ∈ a'

def assgnEquiv (a a' : assgn) : Prop := assgnSubset a a' ∧ assgnSubset a' a

theorem evalVar_in_iff (a : assgn) (v : var) :
    evalVar a v = true ↔ v ∈ a := by
  simp [evalVar]

theorem evalVar_monotonic {a a' : assgn} (hSubset : assgnSubset a a') (v : var) :
    evalVar a v = true → evalVar a' v = true := by
  intro hEval
  rw [evalVar_in_iff] at hEval ⊢
  exact hSubset hEval

theorem evalVar_assgn_equiv {a a' : assgn} (hEq : assgnEquiv a a') (v : var) :
    evalVar a v = evalVar a' v := by
  by_cases hv : v ∈ a <;> by_cases hv' : v ∈ a'
  · simp [evalVar, hv, hv']
  · exfalso
    exact hv' (hEq.1 hv)
  · exfalso
    exact hv (hEq.2 hv')
  · simp [evalVar, hv, hv']

inductive formula where
  | ftrue
  | fvar (v : var)
  | fand (φ ψ : formula)
  | forr (φ ψ : formula)
  | fneg (φ : formula)
deriving Repr, DecidableEq

structure CCCard (α : Type u) where
  prem : List α
  conc : List α
deriving Repr

structure TCCCardP (α : Type u) where
  cardEl1 : α
  cardEl2 : α
  cardEl3 : α
deriving Repr

def TCCCardP.toList {α : Type u} (card : TCCCardP α) : List α :=
  [card.cardEl1, card.cardEl2, card.cardEl3]

instance {α : Type u} : Coe (TCCCardP α) (List α) where
  coe := TCCCardP.toList

structure TCCCard (α : Type u) where
  prem : TCCCardP α
  conc : TCCCardP α
deriving Repr

structure FlatCC where
  Sigma : Nat
  offset : Nat
  width : Nat
  init : List Nat
  cards : List (CCCard Nat)
  final : List (List Nat)
  steps : Nat
deriving Repr

structure BinaryCC where
  offset : Nat
  width : Nat
  init : List Bool
  cards : List (CCCard Bool)
  final : List (List Bool)
  steps : Nat
deriving Repr

structure FlatTCC where
  Sigma : Nat
  init : List Nat
  cards : List (TCCCard Nat)
  final : List (List Nat)
  steps : Nat
deriving Repr

structure CC where
  Sigma : Nat
  offset : Nat
  width : Nat
  init : List (Fin Sigma)
  cards : List (CCCard (Fin Sigma))
  final : List (List (Fin Sigma))
  steps : Nat
deriving Repr

structure TCC where
  Sigma : Nat
  init : List (Fin Sigma)
  cards : List (TCCCard (Fin Sigma))
  final : List (List (Fin Sigma))
  steps : Nat
deriving Repr

abbrev fvertex := Nat
abbrev fedge := fvertex × fvertex
abbrev fgraph := Nat × List fedge

def fgraph_wf (_ : fgraph) : Prop := True

def ofFlatType (k x : Nat) : Prop := x < k

def list_ofFlatType (k : Nat) (xs : List Nat) : Prop :=
  ∀ x, x ∈ xs → ofFlatType k x

theorem list_ofFlatType_nil (k : Nat) : list_ofFlatType k [] := by
  intro x hx
  cases hx

theorem list_ofFlatType_cons {k x : Nat} {xs : List Nat} :
    list_ofFlatType k (x :: xs) ↔ ofFlatType k x ∧ list_ofFlatType k xs := by
  constructor
  · intro h
    refine ⟨h x (by simp), ?_⟩
    intro y hy
    exact h y (by simp [hy])
  · rintro ⟨hx, hxs⟩ y hy
    simp at hy
    rcases hy with rfl | hy
    · exact hx
    · exact hxs y hy

theorem list_ofFlatType_app {k : Nat} {xs ys : List Nat} :
    list_ofFlatType k (xs ++ ys) ↔ list_ofFlatType k xs ∧ list_ofFlatType k ys := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx
      exact h x (by simp [hx])
    · intro y hy
      exact h y (by simp [hy])
  · rintro ⟨hxs, hys⟩ z hz
    simp at hz
    rcases hz with hz | hz
    · exact hxs z hz
    · exact hys z hz

def isPrefix {α : Type u} (xs ys : List α) : Prop :=
  ∃ rest, ys = xs ++ rest

def isSubstring {α : Type u} (subs s : List α) : Prop :=
  ∃ left right, s = left ++ subs ++ right

inductive relpower {α : Type u} (r : α → α → Prop) : Nat → α → α → Prop
  | refl (a : α) : relpower r 0 a a
  | step {n : Nat} {a b c : α} : r a b → relpower r n b c → relpower r (n + 1) a c

def flattenString {k : Nat} (xs : List (Fin k)) : List Nat :=
  xs.map Fin.val

def isFlatListOf {k : Nat} (flat : List Nat) (xs : List (Fin k)) : Prop :=
  flattenString xs = flat

theorem flattenString_list_ofFlatType {k : Nat} (xs : List (Fin k)) :
    list_ofFlatType k (flattenString xs) := by
  intro x hx
  simp [flattenString] at hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

theorem isFlatListOf_list_ofFlatType {k : Nat} {flat : List Nat} {xs : List (Fin k)}
    (h : isFlatListOf flat xs) : list_ofFlatType k flat := by
  rw [← h]
  exact flattenString_list_ofFlatType xs

def unflattenList (k : Nat) : (xs : List Nat) → list_ofFlatType k xs → List (Fin k)
  | [], _ => []
  | x :: xs, h =>
      have hx : x < k := h x (by simp)
      have hxs : list_ofFlatType k xs := by
        intro y hy
        exact h y (by simp [hy])
      ⟨x, hx⟩ :: unflattenList k xs hxs

theorem flatten_unflattenList (k : Nat) :
    ∀ xs (h : list_ofFlatType k xs), flattenString (unflattenList k xs h) = xs
  | [], _ => rfl
  | x :: xs, h => by
      have hxs : list_ofFlatType k xs := by
        intro y hy
        exact h y (by simp [hy])
      simp [unflattenList, flattenString]
      exact flatten_unflattenList k xs hxs

theorem isFlatListOf_unflattenList {k : Nat} (xs : List Nat) (h : list_ofFlatType k xs) :
    isFlatListOf xs (unflattenList k xs h) := by
  exact flatten_unflattenList k xs h

theorem fin_eta {k : Nat} (x : Fin k) : ⟨x.1, x.2⟩ = x := by
  cases x
  rfl

theorem unflatten_flattenString {k : Nat} :
    ∀ xs : List (Fin k), unflattenList k (flattenString xs) (flattenString_list_ofFlatType xs) = xs
  | [] => rfl
  | x :: xs => by
      simp [flattenString, unflattenList, fin_eta]
      exact unflatten_flattenString xs

def validFlatTM (_ : flatTM) : Prop := True

def isValidFlatTM (_ : flatTM) : Bool := true

-- A default/empty valid flatTM for use in test cases
def validFlatTM_default : flatTM :=
  FlatTM.mk 0 0 0 [] 0 []

def monotonic (f : Nat → Nat) : Prop :=
  ∀ x x' : Nat, x ≤ x' → f x ≤ f x'

def inO (f g : Nat → Nat) : Prop :=
  ∃ c n0 : Nat, ∀ n : Nat, n0 ≤ n → f n ≤ c * g n

def inOPoly (f : Nat → Nat) : Prop :=
  ∃ n : Nat, inO f (fun x => x ^ n)



def projT1 {α : Type u} {β : α → Type v} (x : Sigma β) : α := x.1

def index {F : Type} (_ : F) : Nat := 0
