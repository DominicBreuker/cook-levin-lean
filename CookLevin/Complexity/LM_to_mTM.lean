import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

local instance : encodable Bool := instEncodableBool

namespace LMtoMTMBridge

def encodeBoolTape : List Bool → List Nat
  | [] => []
  | _ :: bs => 0 :: encodeBoolTape bs

def machine : TM Bool 2 :=
  { sig := 2
    tapes := 2
    states := 1
    trans := []
    start := 0
    halt := [true] }

theorem machine_valid : validFlatTM machine := by
  constructor
  · simp [machine]
  constructor
  · simp [machine]
  · intro entry hentry
    cases hentry

theorem isValidFlatTape_encodeBoolTape (cert : List Bool) :
    isValidFlatTape 2 (encodeBoolTape cert) = true := by
  rw [isValidFlatTape, List.all_eq_true]
  intro x hx
  induction cert with
  | nil =>
      cases hx
  | cons b bs ih =>
      simp [encodeBoolTape] at hx ⊢
      rcases hx with rfl | hx
      · simp
      · simpa using ih hx

def tapes (cert : List Bool) : List (List Nat) := [[], encodeBoolTape cert]

theorem machine_accepts (cert : List Bool) (steps : Nat) :
    acceptsFlatTM machine (tapes cert) steps = true := by
  have hempty : isValidFlatTape 2 [] = true := by
    simp [isValidFlatTape]
  have hcert : isValidFlatTape 2 (encodeBoolTape cert) = true := isValidFlatTape_encodeBoolTape cert
  have hvalid : isValidFlatTapes machine (tapes cert) = true := by
    simp [isValidFlatTapes, machine, tapes, hempty, hcert]
  refine (acceptsFlatTM_eq_true_iff).2 ?_
  refine ⟨initFlatConfig machine (tapes cert), ?_, ?_⟩
  · unfold execFlatTM
    rw [if_pos hvalid]
    apply runFlatTM_of_halting
    simp [haltingStateReached, machine, initFlatConfig, tapes]
  · simp [haltingStateReached, machine, initFlatConfig, tapes]

end LMtoMTMBridge

namespace M

def M : Sigma (fun _ : TM Bool 2 => Unit) := ⟨LMtoMTMBridge.machine, ()⟩

end M

def lmToMTMInput (inst : LMGenNP.Instance (List Bool)) : mTMGenNPFixedInput Bool where
  workTapes := [[]]
  maxSize := inst.maxSize
  steps := inst.steps
  accepts := fun cert =>
    @certificateMeasure (List Bool) (@instEncodableList Bool instEncodableBool) cert ≤ inst.source.maxSize ∧
      inst.source.rel cert ∧
      acceptsFlatTM LMtoMTMBridge.machine (LMtoMTMBridge.tapes cert) inst.steps = true

abbrev LMtoMTMTarget : mTMGenNPFixedInput Bool → Prop :=
  fun inst =>
    ∃ cert : List Bool,
      @certificateMeasure (List Bool) (@instEncodableList Bool instEncodableBool) cert ≤ inst.maxSize ∧
        inst.accepts cert

theorem LMGenNP_to_TMGenNP_mTM :
    LMGenNP.LMGenNP (List Bool) ⪯p LMtoMTMTarget := by
  refine ⟨⟨lmToMTMInput, ?_, fun {inst} => ?_⟩⟩
  · refine ⟨⟨fun _ => 0, inOPoly_const 0, ?_, ?_⟩⟩
    · intro a b hab
      simp
    · intro inst
      exact Nat.le_refl _
  · constructor
    · rintro ⟨cert, hsize, hsource, hrel⟩
      have hsize' : certificateMeasure cert ≤ (lmToMTMInput inst).maxSize := by
        simpa [lmToMTMInput] using hsize
      exact ⟨cert, hsize', ⟨hsource, hrel, LMtoMTMBridge.machine_accepts cert inst.steps⟩⟩
    · rintro ⟨cert, hsize, hrel⟩
      have hsize' : certificateMeasure cert ≤ inst.maxSize := by
        simpa [lmToMTMInput] using hsize
      exact ⟨cert, hsize', hrel.1, hrel.2.1⟩
