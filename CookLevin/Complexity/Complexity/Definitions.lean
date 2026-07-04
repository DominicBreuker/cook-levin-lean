import Complexity.Complexity.MachineSemantics

set_option autoImplicit false

universe u v

class encodable (α : Sort u) where
  size : α → Nat
  size_ge_logical : ∀ x : α, ∃ n : Nat, size x ≥ n

-- Default instance for types without explicit encoding
-- This provides size 0 for all values, which should be overridden
-- by specific instances that provide meaningful sizes
instance (priority := low) instEncodableDefault (α : Sort u) : encodable α where
  size := fun _ => 0
  size_ge_logical := fun _ => ⟨0, by simp⟩

instance : encodable Nat where
  size := id
  size_ge_logical := fun n => ⟨n, Nat.le_refl n⟩

instance : encodable Bool where
  size := fun b => cond b 1 0
  size_ge_logical := fun b => ⟨cond b 1 0, Nat.le_refl _⟩

instance : encodable Unit where
  size := fun _ => 0
  size_ge_logical := fun _ => ⟨0, Nat.le_refl _⟩

instance {α : Type u} [encodable α] : encodable (List α) where
  size := fun xs => xs.foldl (fun acc x => acc + encodable.size x + 1) 0
  size_ge_logical := fun xs => ⟨xs.foldl (fun acc x => acc + encodable.size x + 1) 0, Nat.le_refl _⟩

instance {α : Type u} [encodable α] : encodable (Option α) where
  size
    | none => 0
    | some x => encodable.size x + 1
  size_ge_logical
    | none => ⟨0, Nat.le_refl _⟩
    | some x => ⟨encodable.size x + 1, Nat.le_refl _⟩

instance {α : Type u} {β : Type v} [encodable α] [encodable β] : encodable (α × β) where
  size := fun x => encodable.size x.1 + encodable.size x.2 + 1
  size_ge_logical := fun x => ⟨encodable.size x.1 + encodable.size x.2 + 1, Nat.le_refl _⟩

instance {k : Nat} : encodable (Fin k) where
  size := fun x => x.1
  size_ge_logical := fun x => ⟨x.1, Nat.le_refl _⟩

instance {α : Type u} {p : α → Prop} [encodable α] : encodable { x // p x } where
  size := fun x => encodable.size x.1 + 1
  size_ge_logical := fun x => ⟨encodable.size x.1 + 1, Nat.le_refl _⟩

instance {α : Type u} {β : α → Type v} [encodable α] [∀ a, encodable (β a)] :
    encodable (Sigma β) where
  size := fun x => encodable.size x.1 + encodable.size x.2 + 1
  size_ge_logical := fun x => ⟨encodable.size x.1 + encodable.size x.2 + 1, Nat.le_refl _⟩

abbrev finType := Type
abbrev flatTM := FlatTM
abbrev TM (_σ : Type) (_ : Nat) := FlatTM

instance : encodable TMMove where
  size
    | .Lmove => 1
    | .Rmove => 1
    | .Nmove => 1
  size_ge_logical := fun _ => ⟨_, Nat.le_refl _⟩

instance : encodable FlatTMConfig where
  size := fun cfg => encodable.size cfg.state_idx + encodable.size cfg.tapes + 1
  size_ge_logical := fun cfg => ⟨encodable.size cfg.state_idx + encodable.size cfg.tapes + 1, Nat.le_refl _⟩

instance : encodable FlatTMTransEntry where
  size := fun entry =>
    encodable.size entry.src_state + encodable.size entry.src_tape_vals +
      encodable.size entry.dst_state + encodable.size entry.dst_write_vals +
      encodable.size entry.move_dirs + 1
  size_ge_logical := fun entry =>
    ⟨encodable.size entry.src_state + encodable.size entry.src_tape_vals +
        encodable.size entry.dst_state + encodable.size entry.dst_write_vals +
        encodable.size entry.move_dirs + 1, Nat.le_refl _⟩

instance : encodable FlatTM where
  size := sizeFlatTM
  size_ge_logical := fun M => ⟨sizeFlatTM M, Nat.le_refl _⟩

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

private def formulaEncSize : formula → Nat
  | .ftrue => 1
  | .fvar v => v + 1
  | .fand φ ψ => formulaEncSize φ + formulaEncSize ψ + 1
  | .forr φ ψ => formulaEncSize φ + formulaEncSize ψ + 1
  | .fneg φ => formulaEncSize φ + 1

instance : encodable formula where
  size := formulaEncSize
  size_ge_logical := fun _ => ⟨_, Nat.le_refl _⟩

-- Simp lemmas for formula sizes (rfl since formulaEncSize is a proper recursive def)
@[simp]
theorem encodable_size_formula_ftrue : encodable.size formula.ftrue = 1 := rfl
@[simp]
theorem encodable_size_formula_fvar (v : var) : encodable.size (formula.fvar v) = v + 1 := rfl
@[simp]
theorem encodable_size_formula_fand (φ ψ : formula) :
    encodable.size (formula.fand φ ψ) = encodable.size φ + encodable.size ψ + 1 := rfl
@[simp]
theorem encodable_size_formula_forr (φ ψ : formula) :
    encodable.size (formula.forr φ ψ) = encodable.size φ + encodable.size ψ + 1 := rfl
@[simp]
theorem encodable_size_formula_fneg (φ : formula) :
    encodable.size (formula.fneg φ) = encodable.size φ + 1 := rfl

structure CCCard (α : Type u) where
  prem : List α
  conc : List α
deriving Repr

instance {α : Type u} [encodable α] : encodable (CCCard α) where
  size := fun c => encodable.size c.prem + encodable.size c.conc + 1
  size_ge_logical := fun c => ⟨encodable.size c.prem + encodable.size c.conc + 1, Nat.le_refl _⟩

structure TCCCardP (α : Type u) where
  cardEl1 : α
  cardEl2 : α
  cardEl3 : α
deriving Repr

instance {α : Type u} [encodable α] : encodable (TCCCardP α) where
  size := fun c => encodable.size c.cardEl1 + encodable.size c.cardEl2 + encodable.size c.cardEl3 + 1
  size_ge_logical := fun c =>
    ⟨encodable.size c.cardEl1 + encodable.size c.cardEl2 + encodable.size c.cardEl3 + 1, Nat.le_refl _⟩

def TCCCardP.toList {α : Type u} (card : TCCCardP α) : List α :=
  [card.cardEl1, card.cardEl2, card.cardEl3]

instance {α : Type u} : Coe (TCCCardP α) (List α) where
  coe := TCCCardP.toList

structure TCCCard (α : Type u) where
  prem : TCCCardP α
  conc : TCCCardP α
deriving Repr

instance {α : Type u} [encodable α] : encodable (TCCCard α) where
  size := fun c => encodable.size c.prem + encodable.size c.conc + 1
  size_ge_logical := fun c => ⟨encodable.size c.prem + encodable.size c.conc + 1, Nat.le_refl _⟩

structure FlatCC where
  Sigma : Nat
  offset : Nat
  width : Nat
  init : List Nat
  cards : List (CCCard Nat)
  final : List (List Nat)
  steps : Nat
deriving Repr

instance : encodable FlatCC where
  size := fun C =>
    encodable.size C.Sigma + encodable.size C.offset + encodable.size C.width +
      encodable.size C.init + encodable.size C.cards + encodable.size C.final +
      encodable.size C.steps + 1
  size_ge_logical := fun C =>
    ⟨encodable.size C.Sigma + encodable.size C.offset + encodable.size C.width +
        encodable.size C.init + encodable.size C.cards + encodable.size C.final +
        encodable.size C.steps + 1, Nat.le_refl _⟩

structure BinaryCC where
  offset : Nat
  width : Nat
  init : List Bool
  cards : List (CCCard Bool)
  final : List (List Bool)
  steps : Nat
deriving Repr

instance : encodable BinaryCC where
  size := fun C =>
    encodable.size C.offset + encodable.size C.width + encodable.size C.init +
      encodable.size C.cards + encodable.size C.final + encodable.size C.steps + 1
  size_ge_logical := fun C =>
    ⟨encodable.size C.offset + encodable.size C.width + encodable.size C.init +
        encodable.size C.cards + encodable.size C.final + encodable.size C.steps + 1, Nat.le_refl _⟩

structure FlatTCC where
  Sigma : Nat
  init : List Nat
  cards : List (TCCCard Nat)
  final : List (List Nat)
  steps : Nat
deriving Repr

instance : encodable FlatTCC where
  size := fun C =>
    encodable.size C.Sigma + encodable.size C.init + encodable.size C.cards +
      encodable.size C.final + encodable.size C.steps + 1
  size_ge_logical := fun C =>
    ⟨encodable.size C.Sigma + encodable.size C.init + encodable.size C.cards +
        encodable.size C.final + encodable.size C.steps + 1, Nat.le_refl _⟩

structure CC where
  Sigma : Nat
  offset : Nat
  width : Nat
  init : List (Fin Sigma)
  cards : List (CCCard (Fin Sigma))
  final : List (List (Fin Sigma))
  steps : Nat
deriving Repr

instance : encodable CC where
  size := fun C =>
    encodable.size C.Sigma + encodable.size C.offset + encodable.size C.width +
      encodable.size C.init + encodable.size C.cards + encodable.size C.final +
      encodable.size C.steps + 1
  size_ge_logical := fun C =>
    ⟨encodable.size C.Sigma + encodable.size C.offset + encodable.size C.width +
        encodable.size C.init + encodable.size C.cards + encodable.size C.final +
        encodable.size C.steps + 1, Nat.le_refl _⟩

structure TCC where
  Sigma : Nat
  init : List (Fin Sigma)
  cards : List (TCCCard (Fin Sigma))
  final : List (List (Fin Sigma))
  steps : Nat
deriving Repr

instance : encodable TCC where
  size := fun C =>
    encodable.size C.Sigma + encodable.size C.init + encodable.size C.cards +
      encodable.size C.final + encodable.size C.steps + 1
  size_ge_logical := fun C =>
    ⟨encodable.size C.Sigma + encodable.size C.init + encodable.size C.cards +
        encodable.size C.final + encodable.size C.steps + 1, Nat.le_refl _⟩

abbrev fvertex := Nat
abbrev fedge := fvertex × fvertex
abbrev fgraph := Nat × List fedge

def fgraph_wf (G : fgraph) : Prop :=
  ∀ e ∈ G.2, e.1 < G.1 ∧ e.2 < G.1

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

theorem encodable_size_list_nil {α : Type u} [encodable α] :
    encodable.size ([] : List α) = 0 := by
  rfl

/-- Shifting the initial accumulator by a constant shifts the whole `foldl` result
by the same constant for additive folds. -/
theorem list_foldl_add {α : Type u} (w : α → Nat) :
    ∀ (xs : List α) (base offset : Nat),
      xs.foldl (fun acc x => acc + w x) (offset + base) =
        offset + xs.foldl (fun acc x => acc + w x) base
  | [], base, offset => by
      simp
  | x :: xs, base, offset => by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        list_foldl_add w xs (base + w x) offset

theorem encodable_size_list_cons {α : Type u} [encodable α] (x : α) (xs : List α) :
    encodable.size (x :: xs) = encodable.size x + 1 + encodable.size xs := by
  simpa [encodable.size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    list_foldl_add (fun y : α => encodable.size y + 1) xs 0 (encodable.size x + 1)

theorem encodable_size_list_append {α : Type u} [encodable α] (xs ys : List α) :
    encodable.size (xs ++ ys) = encodable.size xs + encodable.size ys := by
  induction xs with
  | nil =>
      simp [encodable.size]
  | cons x xs ih =>
      simp [encodable_size_list_cons, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Flattening a list of lists never increases `encodable.size`: the flat list
keeps every element (and its per-element `+1`) but drops the per-sublist `+1`.
Stated over `foldr List.append []` because that is the spelling the front-chain
bridges use for tape concatenation. -/
theorem encodable_size_foldr_append_le {α : Type u} [encodable α] :
    ∀ L : List (List α), encodable.size (L.foldr List.append []) ≤ encodable.size L
  | [] => Nat.le_refl _
  | xs :: L => by
      have hfold : (xs :: L).foldr List.append [] = xs ++ L.foldr List.append [] := rfl
      rw [hfold, encodable_size_list_append, encodable_size_list_cons]
      have ih := encodable_size_foldr_append_le L
      calc
        encodable.size xs + encodable.size (L.foldr List.append [])
            ≤ encodable.size xs + encodable.size L := Nat.add_le_add_left ih _
        _ ≤ encodable.size xs + 1 + encodable.size L := by
            rw [Nat.add_assoc, Nat.add_comm 1 (encodable.size L), ← Nat.add_assoc]
            exact Nat.le_succ _

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

def flatTMOptionSymbolsBounded (sig : Nat) (xs : List (Option Nat)) : Prop :=
  ∀ x ∈ xs, match x with | none => True | some v => v < sig

def flatTMTransEntryValid (M : flatTM) (entry : FlatTMTransEntry) : Prop :=
  entry.src_state < M.states ∧
    entry.dst_state < M.states ∧
    entry.src_tape_vals.length = M.tapes ∧
    entry.dst_write_vals.length = M.tapes ∧
    entry.move_dirs.length = M.tapes ∧
    flatTMOptionSymbolsBounded M.sig entry.src_tape_vals ∧
    flatTMOptionSymbolsBounded M.sig entry.dst_write_vals

def validFlatTM (M : flatTM) : Prop :=
  M.start < M.states ∧
    M.halt.length = M.states ∧
    ∀ entry ∈ M.trans, flatTMTransEntryValid M entry

def isSomeNatBelow (sig : Nat) : Option Nat → Bool
  | none => true
  | some n => n < sig

def isValidFlatTM (M : flatTM) : Bool :=
  decide (M.start < M.states) &&
    decide (M.halt.length = M.states) &&
    M.trans.all (fun entry =>
      decide (entry.src_state < M.states) &&
      decide (entry.dst_state < M.states) &&
      decide (entry.src_tape_vals.length = M.tapes) &&
      decide (entry.dst_write_vals.length = M.tapes) &&
      decide (entry.move_dirs.length = M.tapes) &&
      entry.src_tape_vals.all (isSomeNatBelow M.sig) &&
      entry.dst_write_vals.all (isSomeNatBelow M.sig))

-- A default/empty valid flatTM for use in test cases
def validFlatTM_default : flatTM :=
  FlatTM.mk 1 1 1 [] 0 [true]

def monotonic (f : Nat → Nat) : Prop :=
  ∀ x x' : Nat, x ≤ x' → f x ≤ f x'

theorem subtype_size_val_le {α : Type u} {p : α → Prop} [encodable α] (x : { y // p y }) :
    encodable.size x.1 ≤ encodable.size x := by
  simp [encodable.size]

-- Monotonic composition lemma
theorem monotonic_comp {f g : Nat → Nat} : monotonic f → monotonic g → monotonic (g ∘ f) := by
  intros hf hg x x' hxx'
  apply hg
  apply hf
  exact hxx'

def inO (f g : Nat → Nat) : Prop :=
  ∃ c n0 : Nat, ∀ n : Nat, n0 ≤ n → f n ≤ c * g n

def inOPoly (f : Nat → Nat) : Prop :=
  ∃ n : Nat, inO f (fun x => x ^ n)

/-- `maxPrefix f n` is the maximum value of `f` on the finite prefix `{0, …, n}`.
It is used to control the small-output case in polynomial-composition arguments. -/
def maxPrefix (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => max (maxPrefix f n) (f (n + 1))

theorem le_maxPrefix (f : Nat → Nat) :
    ∀ {m n : Nat}, m ≤ n → f m ≤ maxPrefix f n
  | m, 0, h => by
      have hm : m = 0 := Nat.eq_zero_of_le_zero h
      subst hm
      simp [maxPrefix]
  | m, n + 1, h => by
      by_cases hm : m = n + 1
      · subst hm
        exact Nat.le_max_right _ _
      · have hmn : m ≤ n := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h hm)
        exact Nat.le_trans (le_maxPrefix f hmn) (Nat.le_max_left _ _)

theorem inOPoly_const (c : Nat) : inOPoly (fun _ => c) := by
  refine ⟨1, ?_⟩
  refine ⟨c, 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 1) hn
  calc
    c = c * 1 := by simp
    _ ≤ c * n := Nat.mul_le_mul_left _ hn1
    _ = c * n ^ 1 := by simp

theorem inOPoly_id : inOPoly (fun n => n) := by
  refine ⟨1, ?_⟩
  refine ⟨1, 0, ?_⟩
  intro n _
  simp

theorem inOPoly_add {f g : Nat → Nat} :
    inOPoly f → inOPoly g → inOPoly (fun n => f n + g n) := by
  rintro ⟨df, ⟨cf, n0f, hf⟩⟩ ⟨dg, ⟨cg, n0g, hg⟩⟩
  refine ⟨max df dg + 1, ⟨cf + cg, max (max n0f n0g) 1, ?_⟩⟩
  intro n hn
  have hn0f : n0f ≤ n := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hn0g : n0g ≤ n := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hn1 : 1 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hpowf : n ^ df ≤ n ^ (max df dg + 1) := by
    exact Nat.pow_le_pow_right hn1 (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _))
  have hpowg : n ^ dg ≤ n ^ (max df dg + 1) := by
    exact Nat.pow_le_pow_right hn1 (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _))
  have hf' := hf n hn0f
  have hg' := hg n hn0g
  calc
    f n + g n ≤ cf * n ^ df + cg * n ^ dg := Nat.add_le_add hf' hg'
    _ ≤ cf * n ^ (max df dg + 1) + cg * n ^ (max df dg + 1) := by
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hpowf) (Nat.mul_le_mul_left _ hpowg)
    _ = (cf + cg) * n ^ (max df dg + 1) := by rw [Nat.add_mul]

-- Polynomial composition lemma for inO functions
theorem inOPoly_comp {f g : Nat → Nat} : inOPoly f → inOPoly g → inOPoly (g ∘ f) := by
  rintro ⟨df, ⟨cf, n0f, hf⟩⟩ ⟨dg, ⟨cg, n0g, hg⟩⟩
  refine ⟨df * dg + 1, ⟨max (maxPrefix g n0g) (cg * cf ^ dg), max n0f 1, ?_⟩⟩
  intro n hn
  have hn0f : n0f ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hf' := hf n hn0f
  by_cases hsmall : f n < n0g
  · calc
      g (f n) ≤ maxPrefix g n0g := le_maxPrefix g (Nat.le_of_lt hsmall)
      _ ≤ max (maxPrefix g n0g) (cg * cf ^ dg) := Nat.le_max_left _ _
      _ = max (maxPrefix g n0g) (cg * cf ^ dg) * 1 := by simp
      _ ≤ max (maxPrefix g n0g) (cg * cf ^ dg) * n ^ (df * dg + 1) := by
        apply Nat.mul_le_mul_left
        exact Nat.one_le_pow _ _ hn1
  · have hn0g' : n0g ≤ f n := Nat.le_of_not_gt hsmall
    have hpowf : (f n) ^ dg ≤ (cf * n ^ df) ^ dg := by
      exact Nat.pow_le_pow_left hf' dg
    have hnPow : n ^ (df * dg) ≤ n ^ (df * dg + 1) := by
      exact Nat.pow_le_pow_right hn1 (Nat.le_succ _)
    calc
      g (f n) ≤ cg * (f n) ^ dg := hg (f n) hn0g'
      _ ≤ cg * (cf * n ^ df) ^ dg := Nat.mul_le_mul_left _ hpowf
      _ = cg * (cf ^ dg * (n ^ df) ^ dg) := by rw [Nat.mul_pow]
      _ = cg * (cf ^ dg * n ^ (df * dg)) := by rw [Nat.pow_mul]
      _ ≤ cg * (cf ^ dg * n ^ (df * dg + 1)) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_left _ hnPow
      _ = (cg * cf ^ dg) * n ^ (df * dg + 1) := by rw [Nat.mul_assoc]
      _ ≤ max (maxPrefix g n0g) (cg * cf ^ dg) * n ^ (df * dg + 1) := by
        exact Nat.mul_le_mul_right _ (Nat.le_max_right _ _)

-- Polynomial product lemma: the product of two polynomially-bounded functions is
-- polynomially bounded (degrees add, constants multiply). Needed for cost bounds
-- of loop-based programs, where a `n`-fold loop with poly per-iteration cost has
-- cost `≈ n · poly n`.
theorem inOPoly_mul {f g : Nat → Nat} :
    inOPoly f → inOPoly g → inOPoly (fun n => f n * g n) := by
  rintro ⟨df, cf, n0f, hf⟩ ⟨dg, cg, n0g, hg⟩
  refine ⟨df + dg, ⟨cf * cg, max n0f n0g, ?_⟩⟩
  intro n hn
  have hn0f : n0f ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn0g : n0g ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  show f n * g n ≤ (cf * cg) * n ^ (df + dg)
  calc f n * g n
      ≤ (cf * n ^ df) * (cg * n ^ dg) := Nat.mul_le_mul (hf n hn0f) (hg n hn0g)
    _ = (cf * cg) * (n ^ df * n ^ dg) := by
        rw [Nat.mul_assoc cf (n ^ df) (cg * n ^ dg), Nat.mul_left_comm (n ^ df) cg (n ^ dg),
          ← Nat.mul_assoc cf cg (n ^ df * n ^ dg)]
    _ = (cf * cg) * n ^ (df + dg) := by rw [← Nat.pow_add]



def projT1 {α : Type u} {β : α → Type v} (x : Sigma β) : α := x.1

-- Index function for finite types
-- Default implementation returns 0, but should be overridden
-- by specific instances for finite types
def index {F : Type} [encodable F] (x : F) : Nat := encodable.size x
