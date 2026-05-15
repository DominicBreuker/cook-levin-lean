import Complexity.Complexity.Definitions
import Complexity.Complexity.MachineSemantics
import Complexity.Complexity.NP

set_option autoImplicit false

universe u

/-! # TM-backed decision predicates (Part 2 scaffolding)

This file introduces a *Turing-machine-backed* notion of polynomial-time
decision, alongside the existing propositional `inTimePoly`. The new
predicate `inTimePolyTM` will become the canonical `inTimePoly` once
all consumers have been migrated (Part 2 Step 8 of `PART2.md`).

### Output convention

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

/-- Helper: the standard initial tape list for a decider — the
encoded input on tape 0, all other tapes blank. -/
def initialTapes (M : FlatTM) (input : List Nat) : List (List Nat) :=
  input :: List.replicate (M.tapes - 1) []

theorem initialTapes_length (M : FlatTM) (input : List Nat) (h : 0 < M.tapes) :
    (initialTapes M input).length = M.tapes := by
  show (input :: List.replicate (M.tapes - 1) []).length = M.tapes
  rw [List.length_cons, List.length_replicate]
  exact Nat.sub_add_cancel h

/-- Read the Boolean output of a halting configuration: `true` iff the
final state is the designated `acceptState`. -/
def readOutput (acceptState : Nat) (cfg : FlatTMConfig) : Bool :=
  decide (cfg.state_idx = acceptState)

/-- A TM-backed decision witness for a predicate `P : X → Prop` with
time budget `timeBound : Nat → Nat`.

Compared to the old `HasDecider X P f`, this structure forces the
existence of an actual `FlatTM` that, on the encoded input, halts
within `timeBound (encodable.size x)` steps with state index equal to
either `acceptState` (when `P x` holds) or `rejectState` (otherwise).
The time bound is no longer a phantom argument.

The TM may use multiple tapes: tape 0 holds the encoded input,
remaining tapes start empty. For single-tape TMs (`M.tapes = 1`),
`initialTapes` collapses to `[encode x]` definitionally. -/
structure DecidesBy {X : Type} [encodable X]
    (P : X → Prop) (timeBound : Nat → Nat) where
  /-- How to lay the input out on tape 0. -/
  encode      : X → List Nat
  /-- The encoded input length is linearly bounded by `encodable.size x`. -/
  encode_size : ∀ x, (encode x).length ≤ encodable.size x + 1
  /-- The underlying flat Turing machine. -/
  M           : FlatTM
  /-- It is a well-formed TM. -/
  M_valid     : validFlatTM M
  /-- The machine has at least one tape (the input tape). -/
  M_tapes_pos : 0 < M.tapes
  /-- Halting state index that signals `true`. -/
  acceptState : Nat
  /-- Halting state index that signals `false`. -/
  rejectState : Nat
  /-- `acceptState` is in fact a halting state. -/
  halting_acc : M.halt.getD acceptState false = true
  /-- `rejectState` is in fact a halting state. -/
  halting_rej : M.halt.getD rejectState false = true
  /-- The two output codes are different — without this the output
  carries no information. -/
  accept_ne_reject : acceptState ≠ rejectState
  /-- Running for `timeBound (size x)` steps from the encoded input
  reaches a halting configuration whose state index is `acceptState`
  (if `P x`) or `rejectState` (otherwise). We split the two branches
  to avoid an `[Decidable (P x)]` constraint on the structure. -/
  decides_pos : ∀ x, P x → ∃ cfg,
    runFlatTM (timeBound (encodable.size x)) M
        (initFlatConfig M (initialTapes M (encode x))) = some cfg ∧
      haltingStateReached M cfg = true ∧
      cfg.state_idx = acceptState
  decides_neg : ∀ x, ¬ P x → ∃ cfg,
    runFlatTM (timeBound (encodable.size x)) M
        (initFlatConfig M (initialTapes M (encode x))) = some cfg ∧
      haltingStateReached M cfg = true ∧
      cfg.state_idx = rejectState

/-- `P` is decided by a polynomial-time Turing machine. -/
def inTimePolyTM {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ f : Nat → Nat, Nonempty (DecidesBy P f) ∧ inOPoly f ∧ monotonic f

/-! ## Downgrade: a TM-backed decider yields a propositional decider

For now we keep the old `inTimePoly` definition. The new `inTimePolyTM`
implies it: extract a `Bool` decider by running the machine for the
prescribed number of steps and reading the resulting state index. -/

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

/-- A TM-backed decider yields an old-style `HasDecider`. -/
theorem HasDecider.of_DecidesBy {X : Type} [encodable X]
    {P : X → Prop} {timeBound : Nat → Nat} (D : DecidesBy P timeBound) :
    HasDecider X P timeBound :=
  ⟨D.decideFn, fun x => D.decideFn_correct x⟩

/-- The TM-backed predicate implies the old propositional one. -/
theorem inTimePoly_of_inTimePolyTM {X : Type} [encodable X]
    {P : X → Prop} (h : inTimePolyTM P) : inTimePoly P := by
  rcases h with ⟨f, ⟨D⟩, hPoly, hMono⟩
  exact ⟨f, HasDecider.of_DecidesBy D, hPoly, hMono⟩

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
