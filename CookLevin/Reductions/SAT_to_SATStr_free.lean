import CookLevin.SAT.SATStr
import CookLevin.SAT.CnfSerialize
import CookLevin.Lang.SerializeStr

/-!
# SAT ⪯p SATStr

The program computing `satToStr N = boolsOf (encodeCnf N)`, the string whose bits are the
canonical encoding of the CNF `N`, and its program witness `satToStr_reductionLang`.
`satStr_satToStr` proves `SATStr (satToStr N) ↔ SAT N`.
-/

set_option autoImplicit false

namespace SATToSATStr

open CookLevin.Lang
open EvalCnfCmd (encodeCnf)

/-! ## The map -/

/-- **The reduction map**: the CNF's canonical cell stream, read as a bit
string. -/
def satToStr (N : cnf) : List Bool := boolsOf (encodeCnf N)

/-- **The map is the identity on tape cells** — the whole computational content
of this reduction, and the reason its program is a no-op. -/
theorem strBits_satToStr (N : cnf) : strBits (satToStr N) = encodeCnf N :=
  strBits_boolsOf (EvalCnfCmd.encodeCnf_bit N)

/-- **Correctness.** The reduction is sound and complete: a CNF is satisfiable
exactly when its canonical bit string is in `SATStr`.

The `⇒` half is where the content is: `SATStr.satStr_iff` hands back *some* CNF
`M` with `encodeCnf M = encodeCnf N`, and only the injectivity of `encodeCnf`
(from the canonical parser's `dec_enc`) identifies it with `N`. -/
theorem satStr_satToStr (N : cnf) : SATStr (satToStr N) ↔ SAT N := by
  constructor
  · intro h
    obtain ⟨M, hM, hsat⟩ := (SATStr.satStr_iff _).mp h
    rw [strBits_satToStr] at hM
    have : some N = some M := by
      rw [← CnfSerialize.decCnf_encodeCnf N, ← CnfSerialize.decCnf_encodeCnf M, hM]
    rw [Option.some.inj this]
    exact hsat
  · intro h
    exact (SATStr.satStr_iff _).mpr ⟨N, strBits_satToStr N, h⟩

/-! ## The program and its layouts -/

/-- The one register the witness uses: the CNF stream goes in, the bit string
comes out, and they are the same cells. -/
def OUT : Var := 0

/-- **The program**: the layer's no-op. -/
def strCmd : Cmd := Cmd.op (.copy OUT OUT)

/-- The input layout: the canonical CNF serialization, one register. -/
def encodeIn (N : cnf) : State := [Serialize.enc N]

/-- The output decoder: the canonical bit-string **parser** of one designated
register. Not a hand-written inverse and not `Function.invFun` — the chain-end
discipline of standing risk 1. -/
def decodeOut (s : State) : List Bool :=
  Serialize.decodeD ([] : List Bool) (State.get s OUT)

theorem encodeIn_lit (N : cnf) : encodeIn N = [encodeCnf N] := rfl

/-- On a bit-shaped state the decoder reads register `OUT` as a bit string. -/
theorem decodeOut_eq_boolsOf (s : State) (hs : Compile.BitState s) :
    decodeOut s = boolsOf (State.get s OUT) := by
  unfold decodeOut
  apply decodeD_eq_boolsOf
  intro v hv
  by_cases h : OUT < s.length
  · exact Compile.BitState_get s OUT hs h v hv
  · rw [Compile.get_of_length_le s OUT (Nat.le_of_not_lt h)] at hv
    cases hv

theorem encodeIn_get (N : cnf) : State.get (encodeIn N) OUT = encodeCnf N := rfl

/-- The no-op really is one: the exit state's output register is the input
register, unchanged. -/
theorem strCmd_get (s : State) : State.get (strCmd.eval s) OUT = State.get s OUT := by
  show State.get (State.set s OUT (State.get s OUT)) OUT = _
  exact State.get_set_eq _ _ _

/-- **`computes`.** -/
theorem strCmd_computes (N : cnf) : decodeOut (strCmd.eval (encodeIn N)) = satToStr N := by
  unfold decodeOut
  rw [strCmd_get, encodeIn_get, ← strBits_satToStr N]
  exact Serialize.decodeD_enc ([] : List Bool) (satToStr N)

/-! ## Sizes and cost — all three bounds are `encodeCnf`'s own -/

theorem encodeIn_size (N : cnf) : State.size (encodeIn N) = (encodeCnf N).length := by
  show (encodeCnf N).length + 0 = _
  exact Nat.add_zero _

theorem encodeIn_size_le (N : cnf) :
    State.size (encodeIn N) ≤ 5 * encodable.size N := by
  rw [encodeIn_size]; exact EvalCnfCmd.encodeCnf_length N

/-- The output bit string's `encodable.size`: at most twice its length, which is
`|encodeCnf N|`. -/
theorem satToStr_size_le (N : cnf) :
    encodable.size (satToStr N) ≤ 10 * encodable.size N := by
  have h1 : encodable.size (satToStr N) ≤ 2 * (satToStr N).length :=
    CookLevin.size_le_two_mul_length _
  have h2 : (satToStr N).length = (encodeCnf N).length := by
    rw [← strBits_satToStr N, strBits_length]
  have h3 := EvalCnfCmd.encodeCnf_length N
  rw [h2] at h1
  omega

/-- The program's cost: one `copy` over the input register. -/
theorem strCmd_cost (N : cnf) : strCmd.cost (encodeIn N) = (encodeCnf N).length + 1 := by
  show (State.get (encodeIn N) OUT).length + 1 = _
  rw [encodeIn_get]

theorem strCmd_cost_le (N : cnf) :
    strCmd.cost (encodeIn N) ≤ 10 * encodable.size N + 1 := by
  have h := EvalCnfCmd.encodeCnf_length N
  rw [strCmd_cost]
  omega

theorem encodeIn_bit (N : cnf) : Compile.BitState (encodeIn N) := by
  intro reg hreg z hz
  have : reg = encodeCnf N := by simpa [encodeIn_lit] using hreg
  rw [this] at hz
  exact EvalCnfCmd.encodeCnf_bit N z hz

theorem strCmd_usesBelow : Cmd.UsesBelow strCmd 1 := by
  show (0 : Nat) < 1 ∧ (0 : Nat) < 1
  exact ⟨Nat.zero_lt_one, Nat.zero_lt_one⟩

/-! ## The witness -/

/-- **`satToStr` as a free layer witness.** Both layouts are canonical
`Serialize` instances; the map is the identity on cells; the program is the
no-op. -/
noncomputable def satToStr_reductionLang : PolyTimeComputableLang satToStr where
  c := strCmd
  encodeIn := encodeIn
  decodeOut := decodeOut
  cost_bound := fun n => 10 * n + 1
  cost_bound_poly := inOPoly_add (inOPoly_mul (inOPoly_const 10) inOPoly_id) (inOPoly_const 1)
  cost_bound_mono := fun a b h => by
    have hm := Nat.mul_le_mul_left 10 h
    show 10 * a + 1 ≤ 10 * b + 1
    omega
  encBound := fun n => 5 * n
  encBound_poly := inOPoly_mul (inOPoly_const 5) inOPoly_id
  encBound_mono := fun _ _ h => Nat.mul_le_mul_left 5 h
  encodeIn_size := encodeIn_size_le
  computes := strCmd_computes
  cost_le := strCmd_cost_le
  output_size_le := fun N => le_trans (satToStr_size_le N) (Nat.le_succ _)
  enc_bit := encodeIn_bit
  regBound := 1
  usesBelow := strCmd_usesBelow
  width_le := fun _ => Nat.le_refl 1
  decode_agree := fun N m => by
    have hpad : AgreeBelow 1 (encodeIn N ++ List.replicate m []) (encodeIn N) :=
      fun r _ => State.get_append_replicate_nil (encodeIn N) m r
    have h := Cmd.eval_agree strCmd 1 strCmd_usesBelow hpad
    show decodeOut _ = decodeOut _
    unfold decodeOut
    rw [h OUT Nat.zero_lt_one]

end SATToSATStr
