import Complexity.Complexity.Definitions
import Complexity.Complexity.MachineSemantics

set_option autoImplicit false

/-- A predicate indicating that a function is polynomial-time computable.
This means there exists a polynomial-time bound for computing the function. -/
structure PolyTimeComputableWitness {X Y : Type} [encodable X] [encodable Y]
    (f : X → Y) where
  bound : Nat → Nat
  bound_poly : inOPoly bound
  bound_mono : monotonic bound
  bound_valid : ∀ x : X, encodable.size (f x) ≤ bound (encodable.size x)

abbrev polyTimeComputable {X Y : Type} [encodable X] [encodable Y] (f : X → Y) : Prop :=
  Nonempty (PolyTimeComputableWitness f)

/-! ## TM-backed decision interface (Part 2, Step 4 onwards)

A `DecidesBy P timeBound` witness is a multi-tape `FlatTM` that, on
the encoded input `encode x`, halts within
`timeBound (encodable.size x)` steps in a designated `acceptState`
(when `P x` holds) or `rejectState` (otherwise). The two output
codes must be distinct so the answer carries information.

The new `inTimePoly` (below) is a strict upgrade of the old
propositional `HasDecider` predicate — a `DecidesBy` witness pins
down a real Turing machine. -/

/-- The standard initial tape list for a decider: the encoded input on
tape 0, all other tapes blank. -/
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
time budget `timeBound : Nat → Nat`. The TM may use multiple tapes:
tape 0 holds the encoded input, remaining tapes start empty. For
single-tape TMs (`M.tapes = 1`), `initialTapes` collapses to
`[encode x]` definitionally. -/
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
  /-- If `P x` holds, the machine reaches `acceptState` in budget. -/
  decides_pos : ∀ x, P x → ∃ cfg,
    runFlatTM (timeBound (encodable.size x)) M
        (initFlatConfig M (initialTapes M (encode x))) = some cfg ∧
      haltingStateReached M cfg = true ∧
      cfg.state_idx = acceptState
  /-- If `¬ P x` holds, the machine reaches `rejectState` in budget. -/
  decides_neg : ∀ x, ¬ P x → ∃ cfg,
    runFlatTM (timeBound (encodable.size x)) M
        (initFlatConfig M (initialTapes M (encode x))) = some cfg ∧
      haltingStateReached M cfg = true ∧
      cfg.state_idx = rejectState

/-- Phase-2 polynomial-time bookkeeping. Requires an actual
TM-backed decider with a polynomial time bound.

(The legacy propositional `HasDecider` predicate was deleted in
Step 9 of `PART2.md` v2 once its last consumer — `hasDeciderClassical`
— was retyped to produce `Nonempty (DecidesBy ...)` directly.) -/
def inTimePoly {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ f : Nat → Nat, Nonempty (DecidesBy P f) ∧ inOPoly f ∧ monotonic f

/-- A witness that `R` behaves like a certificate relation for `P`: witnesses
are sound for `P`, and every positive instance of `P` has some witness with
polynomially bounded size. -/
structure PolyCertRelWitness {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) (R : X → Y → Prop) where
  bound : Nat → Nat
  sound : ∀ ⦃x y⦄, R x y → P x
  complete : ∀ ⦃x⦄, P x → ∃ y, R x y ∧ encodable.size y ≤ bound (encodable.size x)
  bound_poly : inOPoly bound
  bound_mono : monotonic bound

abbrev polyCertRel {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) (R : X → Y → Prop) : Prop :=
  Nonempty (PolyCertRelWitness P R)

/-- A witness that `P` is in NP: an encodable certificate type together with a
polynomially bounded certificate relation that is sound and complete for `P`. -/
structure InNPWitness {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) where
  rel : X → Y → Prop
  rel_poly : inTimePoly (fun xy : X × Y => rel xy.1 xy.2)
  rel_correct : polyCertRel P rel

abbrev inNP {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ Y : Type, ∃ _ : encodable Y, Nonempty (@InNPWitness X Y _ _ P)

theorem inNP_intro {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (R : X → Y → Prop)
    (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2))
    (polyCert : polyCertRel P R) :
    inNP P := by
  exact ⟨Y, inferInstance, ⟨⟨R, hPoly, polyCert⟩⟩⟩

def inP (X : Type) [encodable X] (P : X → Prop) : Prop := inTimePoly P

/-- Lift a `DecidesBy P f` (on `X`) to a decider for the predicate
`fun (xy : X × Unit) => P xy.1`. The underlying TM and time bound
are unchanged; only the encoder threads through the projection. -/
private def DecidesBy.proj_left {X : Type} [encodable X]
    {P : X → Prop} {f : Nat → Nat}
    (D : DecidesBy P f) (hMono : monotonic f) :
    DecidesBy (fun xy : X × Unit => P xy.1) f where
  encode xy := D.encode xy.1
  encode_size xy := by
    -- (D.encode xy.1).length ≤ encodable.size xy.1 + 1
    -- and encodable.size xy = encodable.size xy.1 + 0 + 1 = encodable.size xy.1 + 1
    -- so the bound `≤ encodable.size xy + 1` is trivially loosened by +1.
    have h1 : (D.encode xy.1).length ≤ encodable.size xy.1 + 1 := D.encode_size xy.1
    have hsize : encodable.size xy.1 ≤ encodable.size xy := by
      show encodable.size xy.1 ≤ encodable.size xy.1 + encodable.size xy.2 + 1
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
    exact Nat.le_trans h1 (Nat.add_le_add_right hsize 1)
  M := D.M
  M_valid := D.M_valid
  M_tapes_pos := D.M_tapes_pos
  acceptState := D.acceptState
  rejectState := D.rejectState
  halting_acc := D.halting_acc
  halting_rej := D.halting_rej
  accept_ne_reject := D.accept_ne_reject
  decides_pos xy hPxy := by
    -- xy : X × Unit, hPxy : P xy.1
    rcases D.decides_pos xy.1 hPxy with ⟨cfg, hRun, hHalt, hState⟩
    refine ⟨cfg, ?_, hHalt, hState⟩
    -- runFlatTM (f (size xy.1)) M init = some cfg; pad to f (size xy).
    have hsize : encodable.size xy.1 ≤ encodable.size xy := by
      show encodable.size xy.1 ≤ encodable.size xy.1 + encodable.size xy.2 + 1
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
    have hmono : f (encodable.size xy.1) ≤ f (encodable.size xy) := hMono _ _ hsize
    rcases Nat.le.dest hmono with ⟨k, hk⟩
    -- hk : f (encodable.size xy.1) + k = f (encodable.size xy)
    have := runFlatTM_extend (k := k) hRun
        (h_halt := hHalt)
    rw [hk] at this
    exact this
  decides_neg xy hnPxy := by
    rcases D.decides_neg xy.1 hnPxy with ⟨cfg, hRun, hHalt, hState⟩
    refine ⟨cfg, ?_, hHalt, hState⟩
    have hsize : encodable.size xy.1 ≤ encodable.size xy := by
      show encodable.size xy.1 ≤ encodable.size xy.1 + encodable.size xy.2 + 1
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
    have hmono : f (encodable.size xy.1) ≤ f (encodable.size xy) := hMono _ _ hsize
    rcases Nat.le.dest hmono with ⟨k, hk⟩
    have := runFlatTM_extend (k := k) hRun (h_halt := hHalt)
    rw [hk] at this
    exact this

theorem P_NP_incl (X : Type) [encodable X] (P : X → Prop) : inP X P → inNP P := by
  intro hP
  refine inNP_intro (X := X) (Y := Unit) P (fun (x : X) (_ : Unit) => P x) ?_ ?_
  · -- inTimePoly slot: lift the X-decider to an (X × Unit)-decider.
    rcases hP with ⟨f, ⟨D⟩, hf_poly, hf_mono⟩
    exact ⟨f, ⟨D.proj_left hf_mono⟩, hf_poly, hf_mono⟩
  · -- polyCertRel slot: certificate is `()`, bound is 0.
    refine ⟨⟨fun _ => 0, ?_, ?_, ?_, ?_⟩⟩
    · intros _ _ h; exact h
    · intros x hx; exact ⟨(), hx, Nat.zero_le _⟩
    · exact ⟨0, ⟨0, 0, fun _ _ => Nat.zero_le _⟩⟩
    · intros _ _ _; exact Nat.zero_le _

/-- The current scaffold's universal NP source problem on `X`. Later phases can
refine this placeholder into the full generic NP source used by the Coq proof. -/
def NPUniversal (X : Type) [encodable X] : X → Prop := fun _ => True

/-- A witness that `P` polynomial-time reduces to `Q`: a map together with proofs of
polynomial-time computability and correctness (equivalence). -/
structure ReductionWitness {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) where
  reduction : X → Y
  reduction_poly : polyTimeComputable reduction
  reduction_correct : ∀ ⦃x⦄, P x ↔ Q (reduction x)

abbrev reducesPolyMO {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) : Prop :=
  Nonempty (ReductionWitness P Q)

infix:50 " ⪯p " => reducesPolyMO

theorem reducesPolyMO_elim {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → ∃ f : X → Y, (∀ x, P x → Q (f x)) ∧ (∀ x, P x ↔ Q (f x)) := by
  rintro ⟨⟨f, _, hf_correct⟩⟩
  refine ⟨f, fun x hx => (@hf_correct x).mp hx, fun x => @hf_correct x⟩

theorem reducesPolyMO_reflexive (X : Type) [encodable X] (P : X → Prop) : P ⪯p P := by
  refine ⟨⟨id, ?_, fun _ => Iff.rfl⟩⟩
  refine ⟨⟨fun n => n, ?_, ?_, ?_⟩⟩
  · have : inO (fun n => n) (fun x => x^1):= by
      apply Exists.intro 1
      apply Exists.intro 0
      intros n hn
      simp
    apply Exists.intro 1
    exact this
  · intros x x' h
    exact h
  · intros x
    simp

theorem reducesPolyMO_transitive {X Y Z : Type}
    [encodable X] [encodable Y] [encodable Z]
    (P : X → Prop) (Q : Y → Prop) (R : Z → Prop) :
    P ⪯p Q → Q ⪯p R → P ⪯p R := by
  intros hPQ hQR
  rcases hPQ with ⟨⟨f, hf_poly, hf_correct⟩⟩
  rcases hQR with ⟨⟨g, hg_poly, hg_correct⟩⟩
  refine ⟨⟨g ∘ f, ?_, fun {x} => ?_⟩⟩
  rcases hf_poly with ⟨⟨bound_f, hbound_poly_f, hbound_mono_f, hbound_valid_f⟩⟩
  rcases hg_poly with ⟨⟨bound_g, hbound_poly_g, hbound_mono_g, hbound_valid_g⟩⟩
  have hbound_valid_comp : ∀ x : X, encodable.size ((g ∘ f) x) ≤ (bound_g ∘ bound_f) (encodable.size x) := by
    intro x
    calc encodable.size ((g ∘ f) x)
      _ = encodable.size (g (f x)) := rfl
      _ ≤ bound_g (encodable.size (f x)) := hbound_valid_g (f x)
      _ ≤ bound_g (bound_f (encodable.size x)) := by apply hbound_mono_g; exact hbound_valid_f x
  · exact ⟨⟨bound_g ∘ bound_f, inOPoly_comp hbound_poly_f hbound_poly_g,
        monotonic_comp hbound_mono_f hbound_mono_g, hbound_valid_comp⟩⟩
  · simpa using Iff.trans (@hf_correct x) (@hg_correct (f x))


theorem red_inNP {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → inNP Q → inNP P := by
  intros hPQ hQinNP
  rcases hPQ with ⟨⟨f, hf_poly, hf_correct⟩⟩
  rcases hf_poly with ⟨⟨bound_f, hbound_poly_f, hbound_mono_f, hbound_valid_f⟩⟩
  rcases hQinNP with ⟨Y_cert, _, ⟨⟨R, _hR_poly, hR_cert⟩⟩⟩
  rcases hR_cert with ⟨⟨cert_bound, hsound_R, hcomplete_R, hcert_poly_R, hcert_mono_R⟩⟩
  refine ⟨Y_cert, inferInstance, ?_⟩
  refine ⟨⟨fun x cert => R (f x) cert, ?_, ?_⟩⟩
  · -- inTimePoly (fun (x, cert) => R (f x) cert)
    -- TODO(Part3:red_inNP_TMcompose): construct a TM that runs the
    -- reduction's TM on x, then the verifier's TM on (f x, cert).
    -- The reduction's TM is delivered by Part 3's TM-backed
    -- `polyTimeComputable`, which is the structural upgrade `red_inNP`
    -- is waiting on. The predicate-level argument (lines below) is
    -- already done, so once Part 3 lands this is the only gap.
    sorry
  · -- polyCertRel: certificate-bound composition is purely predicate-level
    -- and does not need any TM machinery — it carries over verbatim
    -- from the pre-Step-4 proof.
    refine ⟨⟨cert_bound ∘ bound_f, ?_, ?_, inOPoly_comp hbound_poly_f hcert_poly_R,
        monotonic_comp hbound_mono_f hcert_mono_R⟩⟩
    · intro x cert hrel
      exact hf_correct.mpr (hsound_R hrel)
    · intro x hx
      rcases hcomplete_R (hf_correct.mp hx) with ⟨cert, hcert, hsize⟩
      refine ⟨cert, hcert, ?_⟩
      calc
        encodable.size cert ≤ cert_bound (encodable.size (f x)) := hsize
        _ ≤ cert_bound (bound_f (encodable.size x)) := hcert_mono_R _ _ (hbound_valid_f x)

def NPhard {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∀ Y : Type, ∀ _ : encodable Y, ∀ Q : Y → Prop, inNP Q → Q ⪯p P

def NPcomplete {X : Type} [encodable X] (P : X → Prop) : Prop := NPhard P ∧ inNP P

theorem red_NPhard {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) :
    P ⪯p Q → NPhard P → NPhard Q := by
  intro hPQ hHard Z hEncZ R hR
  exact reducesPolyMO_transitive _ _ _ (hHard Z hEncZ R hR) hPQ

theorem NPhard_subtype_proj (X : Type) [encodable X] (subtype_pred : X → Prop) (P : X → Prop) :
    NPhard (fun x : {x // subtype_pred x} => P x.1) → NPhard P := by
  intro hHard
  intro Y hEncY Q hQ
  have subtype_reduction : (fun x : {x // subtype_pred x} => P x.1) ⪯p P := by
    refine ⟨⟨Subtype.val, ?_, fun {x} => Iff.rfl⟩⟩
    refine ⟨⟨fun n => n, ?_, ?_, ?_⟩⟩
    · exact inOPoly_id
    · intros x x' h
      exact h
    · intro x
      exact subtype_size_val_le x
  exact reducesPolyMO_transitive _ _ _ (hHard Y hEncY Q hQ) subtype_reduction
