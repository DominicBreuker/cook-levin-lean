import CookLevin.Basic.Definitions

/-!
# The generic NP problem

`FlatSingleTMGenNP (M, s, maxSize, steps)`: the single-tape machine `M` is valid, `s` is a
string over its alphabet, and some certificate of length at most `maxSize` appended to `s`
makes `M` halt within `steps` steps. Every language in `inNPCmd` reduces to it.
-/

set_option autoImplicit false

def isValidCert {σ : Type} (k : Nat) (cert : List σ) : Prop :=
  cert.length ≤ k

/-- The single-tape universal front problem, in the Coq original's form
: the instance's strings are over the
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
