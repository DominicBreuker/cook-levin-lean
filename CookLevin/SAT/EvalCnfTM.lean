import CookLevin.SAT.SAT
import CookLevin.Lang.PolyTime
import CookLevin.SAT.EvalCnfCmd

/-!
# The SAT verifier's decider witness

`evalCnfDecidesLang : DecidesLang …` packages `evalCnfCmd` with its polynomial time bound
`timeBound n = 200000 · (n + 1)^4`.
-/

set_option autoImplicit false

namespace EvalCnfTM

open CookLevin.Lang

/-- Polynomial time budget of the SAT verifier; see `EvalCnfCmd.evalCnfCmd_cost_bound`
for the derivation of the constant. -/
def timeBound (n : Nat) : Nat := 200000 * (n + 1) ^ 4

theorem timeBound_inOPoly : inOPoly timeBound := by
  refine ⟨4, ⟨3200000, 1, ?_⟩⟩
  intro n hn
  have hle : n + 1 ≤ n + n := Nat.add_le_add_left hn n
  show 200000 * (n + 1) ^ 4 ≤ 3200000 * n ^ 4
  calc 200000 * (n + 1) ^ 4
      ≤ 200000 * (n + n) ^ 4 :=
        Nat.mul_le_mul_left 200000 (Nat.pow_le_pow_left hle 4)
    _ = 3200000 * n ^ 4 := by ring

theorem timeBound_monotonic : monotonic timeBound :=
  fun _ _ h =>
    Nat.mul_le_mul_left 200000 (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 4)

/-! ## The verifier program in the layer

The concrete program and encoding live in
`Deciders/EvalCnfCmd.lean`. This file ties them into the
framework. -/

/-- The Lang-level decider witness. The program and encoding are concrete
(from `EvalCnfCmd`):
the four behaviour/frame fields by the proven assembly in `EvalCnfCmd.lean`
(`evalCnfCmd_decides` / `evalCnfCmd_cost_bound` / `evalCnfCmd_usesBelow` /
`evalCnfCmd_noConsLen`), themselves proven from the per-clause contracts
(`processOneClause_run`/`_cost`/`_usesBelow`/`_noConsLen`), all discharged. -/
noncomputable def evalCnfDecidesLang :
    DecidesLang (fun Na : cnf × assgn => satisfiesCnf Na.2 Na.1) timeBound where
  c := EvalCnfCmd.evalCnfCmd
  encodeIn := EvalCnfCmd.encodeState
  -- `State.size (encodeState x) ≤ 6·size` (the unary blow-up is charged by
  -- `size Nat = id`), dominated by the quartic budget.
  encodeIn_size := by
    intro x
    have h1 : State.size (EvalCnfCmd.encodeState x) ≤ 6 * encodable.size x :=
      EvalCnfCmd.encodeState_size_bound x
    have h2 : 6 * encodable.size x ≤ timeBound (encodable.size x) := by
      show 6 * encodable.size x ≤ 200000 * (encodable.size x + 1) ^ 4
      have hself : encodable.size x + 1 ≤ (encodable.size x + 1) ^ 4 :=
        Nat.le_self_pow (by norm_num) _
      omega
    exact h1.trans h2
  decides := EvalCnfCmd.evalCnfCmd_decides
  cost_bound := EvalCnfCmd.evalCnfCmd_cost_bound
  -- `Compile.BitState (encodeState x)`: discharged by the
  -- UNARY encoding (variables as `1`-blocks, markers/separators in `{0,1}`).
  enc_bit := fun x => EvalCnfCmd.encodeState_bit x
  -- Register frame: 16 (the inner bodies need 4 scratch registers beyond the encoded
  -- 12). `encodeState` lays out only 12 registers; the runtime padding
  -- (`Compile.paddedBitDeciderTM`) widens to 16.
  regBound := 16
  usesBelow := EvalCnfCmd.evalCnfCmd_usesBelow
  width_le := by
    intro x; rcases x with ⟨N, a⟩
    -- `encodeState (N, a)` is a 12-register literal; `12 ≤ 16`.
    show (EvalCnfCmd.encodeState (N, a)).length ≤ 16
    simp only [EvalCnfCmd.encodeState, List.length_cons, List.length_nil]
    omega

end EvalCnfTM

/-! ## `SAT ∈ NP`

`sat_NP` rebuilds against `inTimePolyTM_evalCnf` exactly as before
— the *signature* of `inTimePolyTM_evalCnf` is stable across the
pivot; only its construction internals changed. -/

namespace SAT_inNP

end SAT_inNP
