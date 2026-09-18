import CookLevin.Reductions.S1Witness
import CookLevin.Reductions.FSAT_to_SAT_comp

/-!
# FlatSingleTMGenNP ⪯p SAT

Composes the tableau reduction witness (`FlatSingleTMGenNP → FlatTCC`) with the witness of
`FlatTCC → SAT` into one program witness `s1_to_SAT_witness`.
-/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace S1SATComp

open CookLevin.Lang CookLevin.Tableau HeadLayout BinaryCCToFSAT

/-! ## `clearRange` — the reusable scrub gadget

Every seam so far spelled its `mfc` out as a literal chain of `clear`s and
then re-derived an `_eval` lemma by a 26-step `rw`. That does not scale to
the 42-register scrub this seam needs, so the scrub is a recursive `def` with ONE `get` lemma proven by
induction. Reuse it for every future seam. -/

/-- `clearRange lo n` clears registers `lo, lo+1, …, lo+n` (that is `n+1`
registers — the empty range is deliberately not representable, which is what
keeps the base case unit-cost: a `copy lo lo` no-op base would cost
`|s.get lo| + 1`, not `1`). -/
def clearRange (lo : Nat) : Nat → Cmd
  | 0     => Cmd.op (.clear lo)
  | n + 1 => Cmd.op (.clear lo) ;; clearRange (lo + 1) n

/-- **The scrub gadget's whole semantics**: registers in `[lo, lo+n]` read
`[]`, every other register is untouched. -/
theorem clearRange_get : ∀ (n : Nat) (lo : Nat) (t : State) (r : Nat),
    State.get ((clearRange lo n).eval t) r
      = if lo ≤ r ∧ r ≤ lo + n then [] else State.get t r
  | 0, lo, t, r => by
      show State.get ((Cmd.op (Op.clear lo)).eval t) r = _
      rw [Cmd.eval_op]
      show State.get (State.set t lo []) r = _
      by_cases h : r = lo
      · subst h
        have hin : r ≤ r ∧ r ≤ r + 0 := ⟨Nat.le_refl r, Nat.le_refl r⟩
        rw [State.get_set_eq, if_pos hin]
      · rw [State.get_set_ne _ _ _ _ h, if_neg]
        intro hcon
        exact h (Nat.le_antisymm hcon.2 hcon.1)
  | n + 1, lo, t, r => by
      show State.get ((clearRange (lo + 1) n).eval ((Cmd.op (Op.clear lo)).eval t)) r = _
      rw [clearRange_get n, Cmd.eval_op]
      by_cases h : lo + 1 ≤ r ∧ r ≤ lo + 1 + n
      · have ha := h.1
        have hb := h.2
        have hin : lo ≤ r ∧ r ≤ lo + (n + 1) := ⟨by omega, by omega⟩
        rw [if_pos h, if_pos hin]
      · rw [if_neg h]
        show State.get (State.set t lo []) r = _
        by_cases h0 : r = lo
        · subst h0
          have hin : r ≤ r ∧ r ≤ r + (n + 1) :=
            ⟨Nat.le_refl r, Nat.le_add_right r (n + 1)⟩
          rw [State.get_set_eq, if_pos hin]
        · rw [State.get_set_ne _ _ _ _ h0, if_neg]
          intro hcon
          have ha := hcon.1
          have hb := hcon.2
          exact h ⟨by omega, by omega⟩

/-- The scrub costs `2n+1`: `n+1` unit clears and `n` sequencing seams. -/
theorem clearRange_cost : ∀ (n : Nat) (lo : Nat) (t : State),
    (clearRange lo n).cost t ≤ 2 * n + 1
  | 0, lo, t => by
      show (Cmd.op (Op.clear lo)).cost t ≤ 2 * 0 + 1
      rw [Cmd.cost_op]
      show (1 : Nat) ≤ 2 * 0 + 1
      omega
  | n + 1, lo, t => by
      show (Cmd.op (Op.clear lo) ;; clearRange (lo + 1) n).cost t ≤ 2 * (n + 1) + 1
      rw [Cmd.cost_seq, Cmd.cost_op, Cmd.eval_op]
      have hrec := clearRange_cost n (lo + 1) (Op.eval (Op.clear lo) t)
      have hc : Op.cost (Op.clear lo) t = 1 := rfl
      rw [hc]
      omega

theorem clearRange_usesBelow : ∀ (n : Nat) (lo : Nat) (k : Nat), lo + n < k →
    Cmd.UsesBelow (clearRange lo n) k
  | 0, lo, k, h => h
  | n + 1, lo, k, h => by
      have hlo : lo < k := Nat.lt_of_le_of_lt (Nat.le_add_right lo (n + 1)) h
      have hrec : lo + 1 + n < k := by omega
      exact ⟨hlo, clearRange_usesBelow n (lo + 1) k hrec⟩

/-- `State.get` past the state's length is `[]` (the wider-right-frame
closer). -/
theorem get_nil_of_len_le (s : State) (r : Nat) (h : s.length ≤ r) :
    State.get s r = [] := by
  unfold State.get
  rw [List.getElem?_eq_none h]
  rfl

/-! ## The re-encoder -/

/-- The fourth seam's re-encoder: erase register `0` and the whole S1 scratch
block `[6, 48)`, keep the output key `1`–`5`. -/
def scrub4 : Cmd := Cmd.op (.clear 0) ;; clearRange 6 41

/-- `scrub4`'s whole semantics, in one clause. -/
theorem scrub4_get (t : State) (r : Nat) :
    State.get (scrub4.eval t) r
      = if r = 0 ∨ (6 ≤ r ∧ r ≤ 47) then [] else State.get t r := by
  unfold scrub4
  rw [Cmd.eval_seq, clearRange_get, Cmd.eval_op]
  by_cases h6 : 6 ≤ r ∧ r ≤ 6 + 41
  · have ha := h6.1
    have hb := h6.2
    have hin : r = 0 ∨ (6 ≤ r ∧ r ≤ 47) := Or.inr ⟨ha, by omega⟩
    rw [if_pos h6, if_pos hin]
  · rw [if_neg h6]
    show State.get (State.set t 0 []) r = _
    by_cases h0 : r = 0
    · subst h0
      have hin : (0 : Nat) = 0 ∨ (6 ≤ (0 : Nat) ∧ (0 : Nat) ≤ 47) := Or.inl rfl
      rw [State.get_set_eq, if_pos hin]
    · rw [State.get_set_ne _ _ _ _ h0, if_neg]
      intro hcon
      rcases hcon with h | h
      · exact h0 h
      · have ha := h.1
        have hb := h.2
        exact h6 ⟨ha, by omega⟩

theorem scrub4_cost (t : State) : scrub4.cost t ≤ 100 := by
  unfold scrub4
  rw [Cmd.cost_seq, Cmd.cost_op, Cmd.eval_op]
  have hrec := clearRange_cost 41 6 (Op.eval (Op.clear 0) t)
  have hc : Op.cost (Op.clear 0) t = 1 := rfl
  rw [hc]
  omega

theorem scrub4_usesBelow : Cmd.UsesBelow scrub4 48 := by
  refine ⟨?_, clearRange_usesBelow 41 6 48 (by omega)⟩
  show (0 : Nat) < 48
  omega

/-! ## The bridge — stated over an arbitrary S1 program

The two hypotheses are *exactly* `S1Program.s1Program_computes` and
`S1Program.s1Program_usesBelow`. Nothing else about the program is used, so
this theorem is axiom-clean while stage C is still a placeholder. -/

/-- The frozen head layout occupies exactly five registers. -/
theorem headEncodeIn_length (x : flatTM × List Nat × Nat × Nat) :
    (headEncodeIn x).length = 5 := by
  obtain ⟨M, s, maxSize, steps⟩ := x; rfl

/-- The tail composite's input layout occupies exactly six registers. -/
theorem flatTCC_encodeIn_length (C : FlatTCC) :
    (FlatTCCFree.encodeIn C).length = 6 := rfl

set_option maxHeartbeats 1000000 in
/-- **The fourth seam's bridge, over an arbitrary program `c`** satisfying the
S1 output-key contract and the S1 register frame. Axiom-clean. -/
theorem s1Bridge (c : Cmd)
    (hcomputes : ∀ x : flatTM × List Nat × Nat × Nat,
      S1Program.s1Extract (c.eval (headEncodeIn x)) = S1Program.s1Key (S1Map.s1Map x))
    (huses : Cmd.UsesBelow c S1Program.s1RegBound)
    (x : flatTM × List Nat × Nat × Nat) :
    AgreeBelow 57 (scrub4.eval (c.eval (headEncodeIn x)))
      (FlatTCCFree.encodeIn (S1Map.s1Map x)) := by
  intro r hr
  rw [scrub4_get]
  -- the five key registers, off the program's `computes` contract
  have hkey := hcomputes x
  simp only [S1Program.s1Extract, S1Program.s1Key, List.cons.injEq,
    and_true] at hkey
  obtain ⟨h1, h2, h3, h4, h5⟩ := hkey
  rcases Nat.lt_or_ge r 6 with h6 | h6
  · -- register 0 is scrubbed; registers 1–5 carry the output key
    interval_cases r
    · rw [if_pos (show (0 : Nat) = 0 ∨ (6 ≤ (0 : Nat) ∧ (0 : Nat) ≤ 47) from Or.inl rfl)]
      rfl
    · rw [if_neg (by decide)]; exact h1
    · rw [if_neg (by decide)]; exact h2
    · rw [if_neg (by decide)]; exact h3
    · rw [if_neg (by decide)]; exact h4
    · rw [if_neg (by decide)]; exact h5
  · rcases Nat.lt_or_ge r 48 with hlt | hge
    · -- the S1 scratch block: scrubbed here, missing there
      have hin : r = 0 ∨ (6 ≤ r ∧ r ≤ 47) := Or.inr ⟨h6, by omega⟩
      rw [if_pos hin]
      refine (get_nil_of_len_le _ _ ?_).symm
      rw [flatTCC_encodeIn_length]
      omega
    · -- above the left frame: neither side has such a register
      have hnot : ¬ (r = 0 ∨ (6 ≤ r ∧ r ≤ 47)) := by
        rintro (h | ⟨_, hb⟩)
        · omega
        · omega
      rw [if_neg hnot]
      have hlen : (c.eval (headEncodeIn x)).length ≤ 48 := by
        have hL := Cmd.eval_length_le c S1Program.s1RegBound huses (headEncodeIn x)
        rw [headEncodeIn_length] at hL
        have hmax : max 5 S1Program.s1RegBound = 48 := by decide
        rw [hmax] at hL
        exact hL
      rw [get_nil_of_len_le _ _ (le_trans hlen hge)]
      refine (get_nil_of_len_le _ _ ?_).symm
      rw [flatTCC_encodeIn_length]
      omega

/-! ## The seam and the composed witness

Everything below is stated **over the program parameter** (`…Of`) and
instantiated at `S1Program.s1Program` immediately after. -/

set_option maxHeartbeats 1000000 in
/-- **The seam**, over an arbitrary S1 program. Every field but
`bridge` is mechanical; `bridge` is `s1Bridge`. -/
noncomputable def s1_to_SAT_seamOf (c : Cmd)
    (hcomputes : ∀ x : flatTM × List Nat × Nat × Nat,
      S1Program.s1Extract (c.eval (headEncodeIn x)) = S1Program.s1Key (S1Map.s1Map x))
    (huses : Cmd.UsesBelow c S1Program.s1RegBound)
    (hcost : S1Witness.S1CostBound c) :
    (S1Witness.s1WitnessOf c hcomputes huses hcost).SeamData
      FSATSATComp.flatTCC_to_SAT_witness where
  mfc := scrub4
  bridge := s1Bridge c hcomputes huses
  decode_frame := fun s t hst => by
    show FSATSATFree.decodeOut s = FSATSATFree.decodeOut t
    unfold FSATSATFree.decodeOut
    rw [hst FSATSATFree.CNFOUT (by decide)]
  mfcBound := fun _ => 100
  mfcBound_poly := inOPoly_const 100
  mfcBound_mono := fun _ _ _ => le_refl 100
  mfc_cost := fun _ => scrub4_cost _
  mfc_usesBelow := by
    refine Cmd.UsesBelow_mono ?_ scrub4_usesBelow
    show 48 ≤ max S1Program.s1RegBound 57
    decide

/-- **The composed `FlatSingleTMGenNP → SAT` witness**, over an arbitrary S1
program: the S1 reduction followed by the whole sound tail, as ONE free layer
witness. -/
noncomputable def s1_to_SAT_witnessOf (c : Cmd)
    (hcomputes : ∀ x : flatTM × List Nat × Nat × Nat,
      S1Program.s1Extract (c.eval (headEncodeIn x)) = S1Program.s1Key (S1Map.s1Map x))
    (huses : Cmd.UsesBelow c S1Program.s1RegBound)
    (hcost : S1Witness.S1CostBound c) :
    PolyTimeComputableLang
      ((FSATSATFree.fsatToSat
        ∘ (BinaryCC_to_FSAT_instance
          ∘ (FlatCC_to_BinaryCC_instance ∘ flatTCC_to_flatCC))) ∘ S1Map.s1Map) :=
  PolyTimeComputableLang.comp (S1Witness.s1WitnessOf c hcomputes huses hcost)
    FSATSATComp.flatTCC_to_SAT_witness (s1_to_SAT_seamOf c hcomputes huses hcost)

/-- The composite's register frame is the tail's `57` (the S1 witness's `48`
is narrower). Needed as an *equation* downstream: with the program still a
parameter, `by decide` cannot run on a goal mentioning it. -/
theorem s1_to_SAT_witnessOf_regBound (c : Cmd)
    (hcomputes : ∀ x : flatTM × List Nat × Nat × Nat,
      S1Program.s1Extract (c.eval (headEncodeIn x)) = S1Program.s1Key (S1Map.s1Map x))
    (huses : Cmd.UsesBelow c S1Program.s1RegBound)
    (hcost : S1Witness.S1CostBound c) :
    (s1_to_SAT_witnessOf c hcomputes huses hcost).regBound = 57 := rfl

/-- **The composed witness for `FlatSingleTMGenNP → SAT`** at the real
program. -/
noncomputable def s1_to_SAT_witness :
    PolyTimeComputableLang
      ((FSATSATFree.fsatToSat
        ∘ (BinaryCC_to_FSAT_instance
          ∘ (FlatCC_to_BinaryCC_instance ∘ flatTCC_to_flatCC))) ∘ S1Map.s1Map) :=
  s1_to_SAT_witnessOf S1Program.s1Program S1Program.s1Program_computes
    S1Program.s1Program_usesBelow S1Witness.s1Program_costBound

/-- The composed map's pointwise correctness — the five chain steps chained
once. Extracted so the front seam can reuse it (its own correctness obligation is this
iff pre-composed with `fQ_correct`). -/
theorem s1_to_SAT_correct (x : flatTM × List Nat × Nat × Nat) :
    FlatSingleTMGenNP x
      ↔ SAT ((FSATSATFree.fsatToSat
          ∘ (BinaryCC_to_FSAT_instance
            ∘ (FlatCC_to_BinaryCC_instance ∘ flatTCC_to_flatCC))) (S1Map.s1Map x)) :=
  ((S1Map.s1Map_correct x).trans
      ((FlatTCCFree.flatTCC_to_flatCC_correct (S1Map.s1Map x)).trans
        ((FlatCCBinFree.flatCC_to_binaryCC_correct
            (flatTCC_to_flatCC (S1Map.s1Map x))).trans
          ((BinaryCC_to_FSAT_instance_correct
              (FlatCC_to_BinaryCC_instance
                (flatTCC_to_flatCC (S1Map.s1Map x)))).trans
            (FSATSATFree.fsatToSat_correct
              (BinaryCC_to_FSAT_instance
                (FlatCC_to_BinaryCC_instance
                  (flatTCC_to_flatCC (S1Map.s1Map x)))))))))

end S1SATComp
