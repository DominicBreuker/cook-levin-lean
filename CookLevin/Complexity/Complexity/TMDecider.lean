import Complexity.Complexity.Definitions
import Complexity.Complexity.MachineSemantics
import Complexity.Complexity.NP

set_option autoImplicit false

universe u

/-! # `DecidesBy` helpers (Part 2)

This file used to host both the `DecidesBy` structure and various
helpers. After Step 4 of `PART2.md` v2 the structure itself lives in
`Complexity/Complexity/NP.lean` (so it can appear in the body of
`inTimePoly`); only the *helpers* live here:

- `DecidesBy.decideFn` + `decideFn_correct` — extract a `Bool`
  decision function from a `DecidesBy` witness, with soundness.
- `DecidesBy.negate` / `inTimePolyTM_not` — same TM decides `¬ P` by
  swapping `acceptState` and `rejectState`.
- `DecidesBy.iff` / `inTimePolyTM_iff` — transport a `DecidesBy P`
  across a logical equivalence `P ↔ Q` without touching the TM.

We also expose `inTimePolyTM` as a back-compat alias for `inTimePoly`,
so existing theorem names like `inTimePolyTM_evalCnf` and
`inTimePolyTM_cliqueRel` keep their spelling.

### Output convention (reminder)

A `DecidesBy` witness designates two halting states, `acceptState`
and `rejectState`, **required to be distinct**. The TM's answer on an
input `x` is `true` iff, after running for `timeBound (encodable.size x)`
steps from the *initial multi-tape configuration*, the machine has
reached a halting configuration whose state is `acceptState` (resp.
`rejectState` for `false`).

The initial multi-tape configuration places `encode x` on tape 0 and
leaves all remaining `M.tapes - 1` work tapes empty. For single-tape
TMs (`M.tapes = 1`), this collapses to `[encode x]` — definitionally
the same as the original single-tape convention. -/

/-- Back-compat alias for `inTimePoly`. Kept so existing theorem
names like `inTimePolyTM_evalCnf` and `inTimePolyTM_cliqueRel` need
no rename. -/
abbrev inTimePolyTM {X : Type} [encodable X] (P : X → Prop) : Prop := inTimePoly P

/-! ## Bool decision function extraction -/

/-- The `Bool` decision function extracted from a `DecidesBy` witness:
encode the input, run the machine for `timeBound (size x)` steps, and
return `true` iff the resulting state index equals `acceptState`. -/
def DecidesBy.decideFn {X : Type} [encodable X]
    {P : X → Prop} {timeBound : Nat → Nat} (D : DecidesBy P timeBound)
    (x : X) : Bool :=
  match runFlatTM (timeBound (encodable.size x)) D.M
      (initFlatConfig D.M (initialTapes D.M (D.encode x))) with
  | none => false
  | some cfg => readOutput D.acceptState cfg

/-- Soundness: the extracted `Bool` decider decides `P`. -/
theorem DecidesBy.decideFn_correct {X : Type} [encodable X]
    {P : X → Prop} {timeBound : Nat → Nat} (D : DecidesBy P timeBound)
    (x : X) : P x ↔ D.decideFn x = true := by
  constructor
  · intro hPx
    rcases D.decides_pos x hPx with ⟨cfg, hRun, _hHalt, hState⟩
    show (match runFlatTM (timeBound (encodable.size x)) D.M
        (initFlatConfig D.M (initialTapes D.M (D.encode x))) with
      | none => false
      | some cfg => readOutput D.acceptState cfg) = true
    rw [hRun]
    show readOutput D.acceptState cfg = true
    unfold readOutput
    exact decide_eq_true hState
  · intro hDec
    by_cases hPx : P x
    · exact hPx
    · exfalso
      rcases D.decides_neg x hPx with ⟨cfg, hRun, _hHalt, hState⟩
      have hFn : D.decideFn x = readOutput D.acceptState cfg := by
        show (match runFlatTM (timeBound (encodable.size x)) D.M
            (initFlatConfig D.M (initialTapes D.M (D.encode x))) with
          | none => false
          | some cfg => readOutput D.acceptState cfg) = readOutput D.acceptState cfg
        rw [hRun]
      rw [hFn] at hDec
      have hcfg : cfg.state_idx = D.acceptState := of_decide_eq_true hDec
      exact D.accept_ne_reject (hcfg.symm.trans hState)

/-! ## Negation combinator

The same TM that decides `P` also decides `¬ P` — just swap the
`acceptState` and `rejectState`. The only subtlety is that
`decides_neg` for the negated predicate receives `¬ ¬ P x` and must
produce `P x`, which is only constructive when `P x` is decidable.
We require `[DecidablePred P]`. -/

/-- Any TM-backed decider for `P` yields a TM-backed decider for `¬ P`
by swapping accept and reject. -/
def DecidesBy.negate {X : Type} [encodable X]
    {P : X → Prop} [DecidablePred P]
    {timeBound : Nat → Nat} (D : DecidesBy P timeBound) :
    DecidesBy (fun x => ¬ P x) timeBound where
  encode := D.encode
  encode_size := D.encode_size
  M := D.M
  M_valid := D.M_valid
  M_tapes_pos := D.M_tapes_pos
  acceptState := D.rejectState
  rejectState := D.acceptState
  halting_acc := D.halting_rej
  halting_rej := D.halting_acc
  accept_ne_reject := fun h => D.accept_ne_reject h.symm
  decides_pos := fun x hnPx => D.decides_neg x hnPx
  decides_neg := fun x hnnPx =>
    D.decides_pos x (Decidable.byContradiction hnnPx)

/-- `inTimePolyTM P → inTimePolyTM (¬ P)` for decidable `P`. -/
theorem inTimePolyTM_not {X : Type} [encodable X]
    {P : X → Prop} [DecidablePred P] (h : inTimePolyTM P) :
    inTimePolyTM (fun x => ¬ P x) := by
  rcases h with ⟨f, ⟨D⟩, hPoly, hMono⟩
  exact ⟨f, ⟨D.negate⟩, hPoly, hMono⟩

/-- Transport a `DecidesBy P` across a logical equivalence `P ↔ Q`. The
underlying TM and time bound are unchanged — only the predicate slot
changes. -/
def DecidesBy.iff {X : Type} [encodable X]
    {P Q : X → Prop} {timeBound : Nat → Nat}
    (hEq : ∀ x, P x ↔ Q x) (D : DecidesBy P timeBound) :
    DecidesBy Q timeBound where
  encode := D.encode
  encode_size := D.encode_size
  M := D.M
  M_valid := D.M_valid
  M_tapes_pos := D.M_tapes_pos
  acceptState := D.acceptState
  rejectState := D.rejectState
  halting_acc := D.halting_acc
  halting_rej := D.halting_rej
  accept_ne_reject := D.accept_ne_reject
  decides_pos := fun x hQx => D.decides_pos x ((hEq x).mpr hQx)
  decides_neg := fun x hnQx => D.decides_neg x (fun hPx => hnQx ((hEq x).mp hPx))

/-- Transport `inTimePolyTM` across a logical equivalence. -/
theorem inTimePolyTM_iff {X : Type} [encodable X]
    {P Q : X → Prop} (hEq : ∀ x, P x ↔ Q x) (h : inTimePolyTM P) :
    inTimePolyTM Q := by
  rcases h with ⟨f, ⟨D⟩, hPoly, hMono⟩
  exact ⟨f, ⟨D.iff hEq⟩, hPoly, hMono⟩
