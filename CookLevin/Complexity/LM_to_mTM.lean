import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

local instance : encodable Bool := instEncodableBool

namespace LMtoMTMBridge

def eraseBoolTape : List Bool → List Nat
  | [] => []
  | _ :: bs => 0 :: eraseBoolTape bs

def bridgeMachine : TM Bool 2 :=
  { sig := 2
    tapes := 2
    states := 1
    trans := []
    start := 0
    halt := [true] }

theorem bridgeMachine_valid : validFlatTM bridgeMachine := by
  constructor
  · simp [bridgeMachine]
  constructor
  · simp [bridgeMachine]
  · intro entry hentry
    cases hentry

theorem isValidFlatTape_eraseBoolTape (cert : List Bool) :
    isValidFlatTape 2 (eraseBoolTape cert) = true := by
  rw [isValidFlatTape, List.all_eq_true]
  intro x hx
  induction cert with
  | nil =>
      cases hx
  | cons b bs ih =>
      simp [eraseBoolTape] at hx ⊢
      rcases hx with rfl | hx
      · simp
      · simpa using ih hx

def tapes (cert : List Bool) : List (List Nat) := [[], eraseBoolTape cert]

theorem bridgeMachine_accepts (cert : List Bool) (steps : Nat) :
    acceptsFlatTM bridgeMachine (tapes cert) steps = true := by
  have hempty : isValidFlatTape 2 [] = true := by
    simp [isValidFlatTape]
  have hcert : isValidFlatTape 2 (eraseBoolTape cert) = true := isValidFlatTape_eraseBoolTape cert
  have hvalid : isValidFlatTapes bridgeMachine (tapes cert) = true := by
    simp [isValidFlatTapes, bridgeMachine, tapes, hempty, hcert]
  refine (acceptsFlatTM_eq_true_iff).2 ?_
  refine ⟨initFlatConfig bridgeMachine (tapes cert), ?_, ?_⟩
  · unfold execFlatTM
    rw [if_pos hvalid]
    apply runFlatTM_of_halting
    simp [haltingStateReached, bridgeMachine, initFlatConfig, tapes]
  · simp [haltingStateReached, bridgeMachine, initFlatConfig, tapes]

end LMtoMTMBridge

namespace M

def M : Sigma (fun _ : TM Bool 2 => Unit) := ⟨LMtoMTMBridge.bridgeMachine, ()⟩

end M

def lmToMTMInput (inst : LMGenNP.Instance (List Bool)) : mTMGenNPFixedInput Bool where
  workTapes := [[]]
  maxSize := inst.maxSize
  steps := inst.steps
  accepts := fun cert =>
      @certificateMeasure (List Bool) (@instEncodableList Bool instEncodableBool) cert ≤ inst.source.maxSize ∧
      inst.source.rel cert ∧
      acceptsFlatTM LMtoMTMBridge.bridgeMachine (LMtoMTMBridge.tapes cert) inst.steps = true

abbrev LMtoMTMTarget : mTMGenNPFixedInput Bool → Prop :=
  fun inst =>
    ∃ cert : List Bool,
      @certificateMeasure (List Bool) (@instEncodableList Bool instEncodableBool) cert ≤ inst.maxSize ∧
        inst.accepts cert

theorem LMGenNP_to_TMGenNP_mTM :
    LMGenNP.LMGenNP (List Bool) ⪯p LMtoMTMTarget := by
  refine ⟨⟨lmToMTMInput, ?_, fun {inst} => ?_⟩⟩
  -- The image drops the wrapped source instance (size ≥ 1) and adds the
  -- constant-size tape scaffold `[[]]` (size 1), so the identity bounds it.
  · refine ⟨⟨fun n => n, inOPoly_id, fun a b hab => hab, ?_⟩⟩
    intro inst
    show encodable.size (lmToMTMInput inst) ≤ encodable.size inst
    have hwt : encodable.size ([[]] : List (List Bool)) = 1 := rfl
    simp [lmToMTMInput, hwt]
  · constructor
    · rintro ⟨cert, hsize, hsource, hrel⟩
      have hsize' : certificateMeasure cert ≤ (lmToMTMInput inst).maxSize := by
        simpa [lmToMTMInput] using hsize
      exact ⟨cert, hsize', ⟨hsource, hrel, LMtoMTMBridge.bridgeMachine_accepts cert inst.steps⟩⟩
    · rintro ⟨cert, hsize, hrel⟩
      have hsize' : certificateMeasure cert ≤ inst.maxSize := by
        simpa [lmToMTMInput] using hsize
      exact ⟨cert, hsize', hrel.1, hrel.2.1⟩
