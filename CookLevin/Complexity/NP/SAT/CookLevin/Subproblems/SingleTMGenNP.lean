import Complexity.Complexity.Definitions

set_option autoImplicit false

def isValidCert {σ : Type} (k : Nat) (cert : List σ) : Prop :=
  cert.length ≤ k

def isValidInput {σ : Type} (s : List σ) (k : Nat) (inp : List σ) : Prop :=
  ∃ cert, isValidCert k cert ∧ inp = s ++ cert

def SingleTMGenNP
    (i : Sigma (fun sig : finType => TM sig 1 × List sig × Nat × Nat)) : Prop :=
  match i with
  | ⟨sig, (_, _s, maxSize, _steps)⟩ => ∃ cert : List sig, isValidCert maxSize cert

def FlatSingleTMGenNP : flatTM × List Nat × Nat × Nat → Prop
  | (M, s, maxSize, steps) =>
      validFlatTM M ∧
      list_ofFlatType 1 s ∧
      ∃ cert, list_ofFlatType 1 cert ∧ isValidCert maxSize cert ∧ acceptsFlatTM M [s ++ cert] steps = true

def FlatFunSingleTMGenNP : flatTM × List Nat × Nat × Nat → Prop
  | (M, s, maxSize, steps) =>
      validFlatTM M ∧
      list_ofFlatType 1 s ∧
      ∃ cert, list_ofFlatType 1 cert ∧ isValidCert maxSize cert ∧ acceptsFlatTM M [s ++ cert] steps = true

theorem vec_case1 (X : Type) (v : List X) :
    v.length = 1 → ∃ x, v = [x] := by
  cases v with
  | nil => simp
  | cons x xs =>
      cases xs with
      | nil => simp
      | cons y ys => simp

theorem initTape_isValidInput (_sig states : finType) (s : List Nat) :
    list_ofFlatType 1 s → isValidInput s 0 s := by
  intro hs
  refine ⟨[], ?_, by simp⟩
  simp [isValidCert]

theorem FlatFunSingleTMGenNP_FlatSingleTMGenNP_equiv
    (M : flatTM) (s : List Nat) (maxSize steps : Nat) :
    FlatFunSingleTMGenNP (M, s, maxSize, steps) ↔ FlatSingleTMGenNP (M, s, maxSize, steps) := by
  simp [FlatFunSingleTMGenNP, FlatSingleTMGenNP]

theorem flatSingleTMGenNP_yes :
    FlatSingleTMGenNP (validFlatTM_default, [], 0, 0) := by
  refine ⟨?_, list_ofFlatType_nil 1, ?_⟩
  constructor
  · simp [validFlatTM_default]
  constructor
  · simp [validFlatTM_default]
  · intro entry hentry
    cases hentry
  refine ⟨[], list_ofFlatType_nil 1, by simp [isValidCert], ?_⟩
  simp [acceptsFlatTM, execFlatTM, runFlatTM, haltingStateReached, validFlatTM_default, initFlatConfig]

theorem flatFunSingleTMGenNP_yes :
    FlatFunSingleTMGenNP (validFlatTM_default, [], 0, 0) := by
  simpa [FlatFunSingleTMGenNP, FlatSingleTMGenNP] using flatSingleTMGenNP_yes
