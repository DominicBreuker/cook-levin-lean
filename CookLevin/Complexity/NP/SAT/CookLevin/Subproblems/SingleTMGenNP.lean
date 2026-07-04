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

/-- The single-tape universal front problem, in the Coq original's form
(C8 finding F2, fixed 2026-07-04): the instance's strings are over the
*machine's* alphabet (`list_ofFlatType M.sig`, NOT the earlier port bug
`list_ofFlatType 1`, which admitted only all-zero strings), and the machine
is single-tape (`M.tapes = 1`). Acceptance is accept-by-HALTING
(`acceptsFlatTM` = a halt state is reached within `steps`). -/
def FlatSingleTMGenNP : flatTM × List Nat × Nat × Nat → Prop
  | (M, s, maxSize, steps) =>
      validFlatTM M ∧ M.tapes = 1 ∧
      list_ofFlatType M.sig s ∧
      ∃ cert, list_ofFlatType M.sig cert ∧ isValidCert maxSize cert ∧
        acceptsFlatTM M [s ++ cert] steps = true

def FlatFunSingleTMGenNP : flatTM × List Nat × Nat × Nat → Prop
  | (M, s, maxSize, steps) =>
      validFlatTM M ∧ M.tapes = 1 ∧
      list_ofFlatType M.sig s ∧
      ∃ cert, list_ofFlatType M.sig cert ∧ isValidCert maxSize cert ∧
        acceptsFlatTM M [s ++ cert] steps = true

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

theorem validFlatTM_default_valid : validFlatTM validFlatTM_default := by
  constructor
  · simp [validFlatTM_default]
  constructor
  · simp [validFlatTM_default]
  · intro entry hentry
    cases hentry

theorem flatSingleTMGenNP_yes :
    FlatSingleTMGenNP (validFlatTM_default, [], 0, 0) := by
  refine ⟨validFlatTM_default_valid, rfl, list_ofFlatType_nil _, ?_⟩
  refine ⟨[], list_ofFlatType_nil _, by simp [isValidCert], ?_⟩
  simp [acceptsFlatTM, execFlatTM, runFlatTM, haltingStateReached, validFlatTM_default,
    initFlatConfig, isValidFlatTapes, isValidFlatTape]

theorem flatFunSingleTMGenNP_yes :
    FlatFunSingleTMGenNP (validFlatTM_default, [], 0, 0) := by
  simpa [FlatFunSingleTMGenNP, FlatSingleTMGenNP] using flatSingleTMGenNP_yes
