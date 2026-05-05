import Complexity.Complexity.NP
import Complexity.NP.SAT.CookLevin.Subproblems.BinaryCC
import Complexity.NP.FSAT
import Mathlib.Tactic

set_option autoImplicit false

open Classical

def allBitStrings : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (allBitStrings n).map (fun xs => false :: xs) ++
      (allBitStrings n).map (fun xs => true :: xs)

theorem allBitStrings_complete :
    ∀ {n} (xs : List Bool), xs.length = n → xs ∈ allBitStrings n
  | 0, [], _ => by simp [allBitStrings]
  | 0, _ :: _, h => by cases h
  | n + 1, b :: xs, h => by
      have hxs : xs.length = n := by simpa using h
      cases b <;> simp [allBitStrings, allBitStrings_complete xs hxs]

def litFormula (v : Nat) (b : Bool) : formula :=
  if b then .fvar v else .fneg (.fvar v)

def encodeBitsAt : Nat → List Bool → formula
  | _, [] => .ftrue
  | start, b :: bs => .fand (litFormula start b) (encodeBitsAt (start + 1) bs)

def trueVarsAt : Nat → List Bool → assgn
  | _, [] => []
  | start, b :: bs => (if b then [start] else []) ++ trueVarsAt (start + 1) bs

def concatBits : List (List Bool) → List Bool
  | [] => []
  | s :: ss => s ++ concatBits ss

def encodeTrace (trace : List (List Bool)) : formula :=
  encodeBitsAt 0 (concatBits trace)

theorem trueVarsAt_ge :
    ∀ start bs v, v ∈ trueVarsAt start bs → start ≤ v
  | _, [], _, hv => by cases hv
  | start, b :: bs, v, hv => by
      cases b <;> simp [trueVarsAt] at hv
      · have hge : start + 1 ≤ v := trueVarsAt_ge (start + 1) bs v hv
        omega
      · rcases hv with rfl | hv
        · omega
        · have hge : start + 1 ≤ v := trueVarsAt_ge (start + 1) bs v hv
          omega

theorem encodeBitsAt_sat_prefix (pre : assgn) (start : Nat) (bs : List Bool) :
    (∀ v, v ∈ pre → v < start) →
    evalFormula (pre ++ trueVarsAt start bs) (encodeBitsAt start bs) = true := by
  induction bs generalizing pre start with
  | nil =>
      intro _
      simp [encodeBitsAt, evalFormula]
  | cons b bs ih =>
      cases b
      · intro hprefix
        have hnotPrefix : start ∉ pre := by
          intro h
          exact Nat.ne_of_lt (hprefix start h) rfl
        have hnotTail : start ∉ trueVarsAt (start + 1) bs := by
          intro h
          have hge := trueVarsAt_ge (start + 1) bs start h
          omega
        have hfalse : evalVar (pre ++ trueVarsAt (start + 1) bs) start = false := by
          simp [evalVar, List.mem_append, hnotPrefix, hnotTail]
        have htail :
            evalFormula (pre ++ trueVarsAt (start + 1) bs) (encodeBitsAt (start + 1) bs) = true :=
          ih pre (start + 1) (by
            intro v hv
            exact Nat.lt_trans (hprefix v hv) (Nat.lt_succ_self _))
        change (!(evalVar (pre ++ trueVarsAt (start + 1) bs) start) &&
            evalFormula (pre ++ trueVarsAt (start + 1) bs) (encodeBitsAt (start + 1) bs)) = true
        simp [hfalse, htail]
      · intro hprefix
        have htrue : evalVar (pre ++ start :: trueVarsAt (start + 1) bs) start = true := by
          simp [evalVar, List.mem_append]
        have htail :
            evalFormula ((pre ++ [start]) ++ trueVarsAt (start + 1) bs) (encodeBitsAt (start + 1) bs) = true :=
          ih (pre ++ [start]) (start + 1) (by
            intro v hv
            simp at hv
            rcases hv with hv | rfl
            · exact Nat.lt_trans (hprefix v hv) (Nat.lt_succ_self _)
            · exact Nat.lt_succ_self _)
        have htail' :
            evalFormula (pre ++ start :: trueVarsAt (start + 1) bs) (encodeBitsAt (start + 1) bs) = true := by
          simpa [List.append_assoc] using htail
        simpa [encodeBitsAt, trueVarsAt, litFormula, evalFormula, List.append_assoc] using
          (show (evalVar (pre ++ start :: trueVarsAt (start + 1) bs) start &&
              evalFormula (pre ++ start :: trueVarsAt (start + 1) bs) (encodeBitsAt (start + 1) bs)) = true by
            simp [htrue, htail'])

theorem encodeBitsAt_sat :
    ∀ start bs, evalFormula (trueVarsAt start bs) (encodeBitsAt start bs) = true
  | start, bs => by
      simpa using encodeBitsAt_sat_prefix [] start bs (by intro v hv; cases hv)

theorem encodeBitsAt_sat_extra (extra start : Nat) (bs : List Bool) (hlt : extra < start) :
    evalFormula (extra :: trueVarsAt start bs) (encodeBitsAt start bs) = true := by
  simpa using encodeBitsAt_sat_prefix [extra] start bs (by
    intro v hv
    simp at hv
    rcases hv with rfl
    exact hlt)

theorem encodeBitsAt_sat_twoExtras (extra start : Nat) (bs : List Bool) (hlt : extra < start) :
    evalFormula (extra :: start :: trueVarsAt (start + 1) bs) (encodeBitsAt (start + 1) bs) = true := by
  simpa [List.append_assoc] using
    encodeBitsAt_sat_prefix [extra, start] (start + 1) bs (by
      intro v hv
      simp at hv
      rcases hv with rfl | rfl
      · exact Nat.lt_trans hlt (Nat.lt_succ_self _)
      · exact Nat.lt_succ_self _)

theorem encodeTrace_sat (trace : List (List Bool)) : FSAT (encodeTrace trace) := by
  refine ⟨trueVarsAt 0 (concatBits trace), ?_⟩
  simpa [encodeTrace] using encodeBitsAt_sat 0 (concatBits trace)

noncomputable def acceptingRunsFrom (C : BinaryCC) : Nat → List Bool → List (List (List Bool))
  | 0, s =>
      if satFinal C.offset C.init.length C.final s then [[s]] else []
  | n + 1, s =>
      let extendRun (t : List Bool) :=
        if validStep C.offset C.width C.cards s t then
          (acceptingRunsFrom C n t).map (fun trace => s :: trace)
        else []
      (allBitStrings C.init.length).flatMap extendRun

theorem acceptingRunsFrom_complete (C : BinaryCC) :
    ∀ {n s sf}, relpower (validStep C.offset C.width C.cards) n s sf →
      s.length = C.init.length →
      satFinal C.offset C.init.length C.final sf →
      ∃ trace, trace ∈ acceptingRunsFrom C n s
  | 0, s, _, .refl _, hlen, hfinal => by
      refine ⟨[s], ?_⟩
      simp [acceptingRunsFrom, hfinal]
  | n + 1, s, _, @relpower.step _ _ _ _ t _ hstep hrest, hlen, hfinal => by
      have hnextLen : t.length = C.init.length := hstep.1.symm.trans hlen
      have hnextMem : t ∈ allBitStrings C.init.length := allBitStrings_complete t hnextLen
      rcases acceptingRunsFrom_complete C hrest hnextLen hfinal with ⟨trace, htrace⟩
      refine ⟨s :: trace, ?_⟩
      have hmem :
          s :: trace ∈ List.flatMap
            (fun t =>
              if validStep C.offset C.width C.cards s t then
                (acceptingRunsFrom C n t).map (fun trace => s :: trace)
              else [])
            (allBitStrings C.init.length) := by
        rw [List.mem_flatMap]
        refine ⟨t, hnextMem, ?_⟩
        simp [hstep, htrace]
      simpa [acceptingRunsFrom] using hmem

def orList : List formula → formula
  | [] => .fneg .ftrue
  | f :: fs => .forr f (orList fs)

theorem FSAT_orList_of_mem :
    ∀ {fs f}, f ∈ fs → FSAT f → FSAT (orList fs)
  | [], _, h, _ => by cases h
  | g :: gs, f, h, hf => by
      rcases hf with ⟨a, ha⟩
      simp at h
      rcases h with rfl | h
      · exact ⟨a, by
          change (evalFormula a f || evalFormula a (orList gs)) = true
          simpa [satisfiesFormula, Bool.or_eq_true] using (Or.inl ha : evalFormula a f = true ∨ evalFormula a (orList gs) = true)⟩
      · rcases FSAT_orList_of_mem h ⟨a, ha⟩ with ⟨a', ha'⟩
        exact ⟨a', by
          change (evalFormula a' g || evalFormula a' (orList gs)) = true
          simpa [satisfiesFormula, Bool.or_eq_true] using (Or.inr ha' : evalFormula a' g = true ∨ evalFormula a' (orList gs) = true)⟩

noncomputable def BinaryCC_to_FSAT_instance (C : BinaryCC) : formula :=
  orList ((acceptingRunsFrom C C.steps C.init).map encodeTrace)

theorem BinaryCC_to_FSAT_poly : BinaryCCLang ⪯p FSAT := by
  refine ⟨BinaryCC_to_FSAT_instance, ?_⟩
  rintro C ⟨_, sf, hpow, hfinal⟩
  rcases acceptingRunsFrom_complete C hpow rfl hfinal with ⟨trace, htrace⟩
  have hmem : encodeTrace trace ∈ (acceptingRunsFrom C C.steps C.init).map encodeTrace := by
    exact List.mem_map.mpr ⟨trace, htrace, rfl⟩
  exact FSAT_orList_of_mem hmem (encodeTrace_sat trace)
