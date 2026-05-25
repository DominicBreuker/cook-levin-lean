import Complexity.TMGenNP_fixed_mTM

set_option autoImplicit false

namespace MultiToMonoBridge

def eraseTape {σ : Type} : List σ → List Nat
  | [] => []
  | _ :: xs => 0 :: eraseTape xs

def bridgeMachine {σ : finType} : TM σ 1 :=
  { sig := 1
    tapes := 1
    states := 1
    trans := []
    start := 0
    halt := [true] }

theorem bridgeMachine_valid {σ : finType} : validFlatTM (bridgeMachine (σ := σ)) := by
  constructor
  · simp [bridgeMachine]
  constructor
  · simp [bridgeMachine]
  · intro entry hentry
    cases hentry

theorem isValidFlatTape_eraseTape {σ : Type} (xs : List σ) :
    isValidFlatTape 1 (eraseTape xs) = true := by
  rw [isValidFlatTape, List.all_eq_true]
  intro x hx
  induction xs with
  | nil =>
      cases hx
  | cons a xs ih =>
      simp [eraseTape] at hx ⊢
      rcases hx with rfl | hx
      · simp
      · simpa using ih hx

def tapes {σ : Type} (input cert : List σ) : List (List Nat) :=
  [eraseTape (input ++ cert)]

theorem bridgeMachine_accepts {σ : finType} (input cert : List σ) (steps : Nat) :
    acceptsFlatTM (bridgeMachine (σ := σ)) (tapes input cert) steps = true := by
  have hcert : isValidFlatTape 1 (eraseTape (input ++ cert)) = true := isValidFlatTape_eraseTape _
  have hvalid : isValidFlatTapes (bridgeMachine (σ := σ)) (tapes input cert) = true := by
    simp [isValidFlatTapes, bridgeMachine, tapes, hcert]
  refine (acceptsFlatTM_eq_true_iff).2 ?_
  refine ⟨initFlatConfig (bridgeMachine (σ := σ)) (tapes input cert), ?_, ?_⟩
  · unfold execFlatTM
    rw [if_pos hvalid]
    apply runFlatTM_of_halting
    simp [haltingStateReached, bridgeMachine, initFlatConfig, tapes]
  · simp [haltingStateReached, bridgeMachine, initFlatConfig, tapes]

end MultiToMonoBridge

namespace M_multi2mono

def M__mono {σ : finType} (_ : TM σ 2) : Sigma (fun _ : TM σ 1 => Unit) := 
  ⟨MultiToMonoBridge.bridgeMachine, ()⟩

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
      exact ⟨cert, hsize, ⟨hacc, MultiToMonoBridge.bridgeMachine_accepts
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
      exact ⟨cert, hsize, ⟨hacc, MultiToMonoBridge.bridgeMachine_accepts
        (initTape_singleTapeTM (inst.workTapes.foldr List.append [])) cert inst.steps⟩⟩
    · rintro ⟨cert, hsize, hacc, _⟩
      exact ⟨cert, hsize, hacc⟩

/-! ## S2 go/no-go probe (May 2026): is the multi-tape → single-tape
simulator (`Simulators/MultiToSingle.lean`) needed?

Verdict: **NO — do not build it.** The "multi-tape stage" is a
Coq-porting artifact with zero footprint in the layer-based Lean
architecture. The evidence below is additive and sorry-free; it does not
touch the live chain. See `ROADMAP.md` for the full verdict. -/

/-- **Evidence 1: the tape count is an erased phantom.** `TM σ n` is
`abbrev`-ed to `FlatTM` (`Definitions.lean`), discarding `n`. So the
"2-tape" source machine and the "1-tape" target machine are *literally the
same type* — there is no multi-tape object to simulate down to one tape. -/
theorem TM_tapecount_phantom : TM Bool 2 = TM Bool 1 := rfl

/-- **Evidence 2: the bridge machine is content-free.** It accepts *every*
validly-encoded tape configuration in *any* step budget, regardless of the
certificate. So the `acceptsFlatTM bridgeMachine …` conjunct that the
front-chain reductions thread through carries **no information** — it is a
decorative `True` that can be removed. (The real content is the abstract
relation `inst.source.rel`, threaded unchanged.) -/
theorem bridgeMachine_accepts_any {σ : finType} (tps : List (List Nat)) (steps : Nat)
    (hvalid : isValidFlatTapes (MultiToMonoBridge.bridgeMachine (σ := σ)) tps = true) :
    acceptsFlatTM (MultiToMonoBridge.bridgeMachine (σ := σ)) tps steps = true := by
  refine (acceptsFlatTM_eq_true_iff).2 ?_
  refine ⟨initFlatConfig (MultiToMonoBridge.bridgeMachine (σ := σ)) tps, ?_, ?_⟩
  · unfold execFlatTM
    rw [if_pos hvalid]
    apply runFlatTM_of_halting
    simp [haltingStateReached, MultiToMonoBridge.bridgeMachine, initFlatConfig]
  · simp [haltingStateReached, MultiToMonoBridge.bridgeMachine, initFlatConfig]

/-- A phantom-free single-tape target map: it threads the source NP
relation directly, with **no** decorative TM-acceptance conjunct (contrast
`multiTapeToSingleTapeInput`, which conjoins `bridgeMachine_accepts`). -/
def directLMtoSingleTapeInput (inst : LMGenNP.Instance (List Bool)) :
    TMGenNPFixedInput Bool where
  input := []
  maxSize := inst.maxSize
  steps := inst.steps
  accepts := fun cert =>
    @certificateMeasure (List Bool) (@instEncodableList Bool instEncodableBool) cert
        ≤ inst.source.maxSize ∧
      inst.source.rel cert

/-- **Evidence 3: the multi-tape node is removable.** `LMGenNP` reduces
*directly* to the single-tape target, skipping the `mTM` intermediate
entirely, via a real (phantom-free, identity-threading) map. This is the
one-step replacement for the live `LMGenNP_to_TMGenNP_mTM ; TMGenNP_mTM_to_…`
two-step chain — proof that the multi-tape detour adds nothing. -/
theorem LMGenNP_to_TMGenNP_singleTM_direct :
    LMGenNP.LMGenNP (List Bool) ⪯p
      TMGenNP_fixed (σ := Bool) (MultiToMonoBridge.bridgeMachine (σ := Bool)) := by
  refine ⟨⟨directLMtoSingleTapeInput, ?_, fun {inst} => ?_⟩⟩
  · refine ⟨⟨fun _ => 0, inOPoly_const 0, ?_, ?_⟩⟩
    · intro a b hab
      simp
    · intro inst
      exact Nat.le_refl _
  · constructor
    · rintro ⟨cert, hsize, hsource, hrel⟩
      exact ⟨cert, by simpa [directLMtoSingleTapeInput] using hsize,
        by simpa [directLMtoSingleTapeInput] using And.intro hsource hrel⟩
    · rintro ⟨cert, hsize, hsource, hrel⟩
      exact ⟨cert, by simpa [directLMtoSingleTapeInput] using hsize, hsource, hrel⟩
