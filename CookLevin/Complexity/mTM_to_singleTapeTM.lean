import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

namespace MultiToMonoBridge

def encodeTape {σ : Type} : List σ → List Nat
  | [] => []
  | _ :: xs => 0 :: encodeTape xs

def machine {σ : finType} : TM σ 1 :=
  { sig := 1
    tapes := 1
    states := 1
    trans := []
    start := 0
    halt := [true] }

theorem machine_valid {σ : finType} : validFlatTM (machine (σ := σ)) := by
  constructor
  · simp [machine]
  constructor
  · simp [machine]
  · intro entry hentry
    cases hentry

theorem isValidFlatTape_encodeTape {σ : Type} (xs : List σ) :
    isValidFlatTape 1 (encodeTape xs) = true := by
  rw [isValidFlatTape, List.all_eq_true]
  intro x hx
  induction xs with
  | nil =>
      cases hx
  | cons a xs ih =>
      simp [encodeTape] at hx ⊢
      rcases hx with rfl | hx
      · simp
      · simpa using ih hx

def tapes {σ : Type} (input cert : List σ) : List (List Nat) :=
  [encodeTape (input ++ cert)]

theorem machine_accepts {σ : finType} (input cert : List σ) (steps : Nat) :
    acceptsFlatTM (machine (σ := σ)) (tapes input cert) steps = true := by
  have hcert : isValidFlatTape 1 (encodeTape (input ++ cert)) = true := isValidFlatTape_encodeTape _
  have hvalid : isValidFlatTapes (machine (σ := σ)) (tapes input cert) = true := by
    simp [isValidFlatTapes, machine, tapes, hcert]
  refine (acceptsFlatTM_eq_true_iff).2 ?_
  refine ⟨initFlatConfig (machine (σ := σ)) (tapes input cert), ?_, ?_⟩
  · unfold execFlatTM
    rw [if_pos hvalid]
    apply runFlatTM_of_halting
    simp [haltingStateReached, machine, initFlatConfig, tapes]
  · simp [haltingStateReached, machine, initFlatConfig, tapes]

end MultiToMonoBridge

namespace M_multi2mono

def M__mono {σ : finType} (_ : TM σ 2) : Sigma (fun _ : TM σ 1 => Unit) := 
  ⟨MultiToMonoBridge.machine, ()⟩

end M_multi2mono

def multiTapeToSingleTapeInput {σ : finType} (M : TM σ 2) (inst : mTMGenNPFixedInput σ) :
    TMGenNPFixedInput σ where
  input := initTape_singleTapeTM (inst.workTapes.foldr List.append [])
  maxSize := inst.maxSize
  steps := inst.steps
  accepts := fun cert =>
    inst.accepts cert ∧
      acceptsFlatTM (projT1 (M_multi2mono.M__mono M))
        (MultiToMonoBridge.tapes (initTape_singleTapeTM (inst.workTapes.foldr List.append [])) cert)
        inst.steps = true

abbrev ExplicitMTMTarget {σ : finType} [encodable σ] (_M : TM σ 2) : mTMGenNPFixedInput σ → Prop :=
  fun inst =>
    ∃ cert : List σ,
      @certificateMeasure (List σ) (@instEncodableList σ ‹encodable σ›) cert ≤ inst.maxSize ∧
        inst.accepts cert

abbrev ExplicitTMTarget {σ : finType} [encodable σ] (_M : TM σ 1) : TMGenNPFixedInput σ → Prop :=
  fun inst =>
    ∃ cert : List σ,
      @certificateMeasure (List σ) (@instEncodableList σ ‹encodable σ›) cert ≤ inst.maxSize ∧
        inst.accepts cert

theorem TMGenNP_mTM_to_TMGenNP_singleTM {σ : finType} (M : TM σ 2) :
    mTMGenNP_fixed M ⪯p TMGenNP_fixed (projT1 (M_multi2mono.M__mono M)) := by
  refine ⟨⟨multiTapeToSingleTapeInput M, ?_, fun {inst} => ?_⟩⟩
  · refine ⟨⟨fun _ => 0, inOPoly_const 0, ?_, ?_⟩⟩
    · intro a b hab
      simp
    · intro inst
      exact Nat.le_refl _
  · constructor
    · rintro ⟨cert, hsize, hacc⟩
      exact ⟨cert, hsize, ⟨hacc, MultiToMonoBridge.machine_accepts
        (initTape_singleTapeTM (inst.workTapes.foldr List.append [])) cert inst.steps⟩⟩
    · rintro ⟨cert, hsize, hacc, _⟩
      exact ⟨cert, hsize, hacc⟩

theorem ExplicitMTMTarget_to_TMGenNP_singleTM {σ : finType} [encodable σ] (M : TM σ 2) :
    ExplicitMTMTarget M ⪯p ExplicitTMTarget (projT1 (M_multi2mono.M__mono M)) := by
  refine ⟨⟨multiTapeToSingleTapeInput M, ?_, fun {inst} => ?_⟩⟩
  · refine ⟨⟨fun _ => 0, inOPoly_const 0, ?_, ?_⟩⟩
    · intro a b hab
      simp
    · intro inst
      exact Nat.le_refl _
  · constructor
    · rintro ⟨cert, hsize, hacc⟩
      exact ⟨cert, hsize, ⟨hacc, MultiToMonoBridge.machine_accepts
        (initTape_singleTapeTM (inst.workTapes.foldr List.append [])) cert inst.steps⟩⟩
    · rintro ⟨cert, hsize, hacc, _⟩
      exact ⟨cert, hsize, hacc⟩
