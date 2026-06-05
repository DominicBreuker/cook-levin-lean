import Complexity.Complexity.TMDecider
import Complexity.NP.SAT
import Complexity.Lang
import Complexity.Complexity.Deciders.EvalCnfCmd

set_option autoImplicit false

/-! # The SAT-verifier — closed via the Lang layer (Part 3.5)

This file owns the TM-backed decider for the SAT verification
relation `fun (N, a) => satisfiesCnf a N` — i.e., the witness that
`SAT ∈ NP`.

**Skeleton status (post-pivot, May 2026).** The construction is now
routed through the higher-level `Lang` layer (Part 3 of
`ROADMAP.md`):

1. `evalCnfCmd : Lang.Cmd` — the SAT verifier as a program in the DSL.
2. `evalCnfEncode : cnf × assgn → Lang.State` — input layout.
3. `evalCnfDecidesLang : Lang.DecidesLang …` — DSL-level decider witness.
4. `inTimePolyTM_evalCnf` — apply `Lang.inTimePolyLang_to_inTimePoly`.

The original single `sorry` for `decider` is now decomposed into a
handful of small, focused sorrys (the program itself, the encoding,
encoding-size bound, correctness, cost bound). These are the actual
content gaps Part 3.5 closes.

Note: `inTimePolyTM_evalCnf` keeps its full name + signature so
`sat_NP` (below) does not need to change.
-/

namespace EvalCnfTM

open Complexity.Lang

/-- Polynomial time budget for `evalCnfTM`. -/
def timeBound (n : Nat) : Nat := (n + 1) ^ 3

theorem timeBound_inOPoly : inOPoly timeBound := by
  refine ⟨3, ⟨8, 1, ?_⟩⟩
  intro n hn
  have hle : n + 1 ≤ n + n := Nat.add_le_add_left hn n
  show (n + 1) ^ 3 ≤ 8 * n ^ 3
  calc (n + 1) ^ 3
      ≤ (n + n) ^ 3 := Nat.pow_le_pow_left hle 3
    _ = 8 * n ^ 3 := by ring

theorem timeBound_monotonic : monotonic timeBound :=
  fun _ _ h => Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 3

/-! ## The verifier program in the layer

The concrete program and encoding live in
`Deciders/EvalCnfCmd.lean`. This file ties them into the
framework. -/

/-- The Lang-level decider witness. The program and encoding are
concrete (from `EvalCnfCmd`); the proofs are deferred to Part 3.5
sub-steps. The `encodeIn_size` obligation currently uses the
strict `≤ size + 1` bound from `DecidesLang`; relaxing that to
`≤ costBound size` is one of the gaps recorded in
`EvalCnfCmd.lean`. -/
noncomputable def evalCnfDecidesLang :
    DecidesLang (fun Na : cnf × assgn => satisfiesCnf Na.2 Na.1) timeBound where
  c := EvalCnfCmd.evalCnfCmd
  encodeIn := EvalCnfCmd.encodeState
  encodeIn_size := by intro x; sorry
    -- TODO(Part3.5-encode-size): obligation is
    -- `State.size (encodeState x) ≤ timeBound (encodable.size x)
    --  = (encodable.size x + 1)^3`.
    -- Closing: combine `EvalCnfCmd.encodeState_size_bound`
    -- (`≤ 5 · size + 20`) with `5 · n + 20 ≤ (n + 1)^3` for
    -- `n ≥ 3`, plus a base-case check for `n < 3`.
  decides := EvalCnfCmd.evalCnfCmd_decides
  cost_bound := EvalCnfCmd.evalCnfCmd_cost_bound
  enc_bit := by intro x; sorry
    -- TODO(C2, B′ — LIVE PATH): `Compile.BitState (EvalCnfCmd.encodeState x)`.
    -- `encodeState` currently lays cells `v+3` (variable values) and
    -- `CLAUSE_END = 2`, so it is NOT bit-level. This is the live `sat_NP`
    -- obligation: re-lay `encodeState` UNARY (variables as `1`-blocks, markers in
    -- `{0,1}`) so it satisfies `BitState`, then discharge here. See HANDOFF.md
    -- "The live path — EvalCnfCmd" — this, not a `LangEncodable (cnf × assgn)`
    -- instance, is what `Compile_sound`/`DecidesLang.toDecidesBy` need.

/-- The Lang-level `inTimePolyLang` witness. -/
theorem inTimePolyLang_evalCnf :
    inTimePolyLang (fun Na : cnf × assgn => satisfiesCnf Na.2 Na.1) :=
  ⟨timeBound, ⟨evalCnfDecidesLang⟩, timeBound_inOPoly, timeBound_monotonic⟩

/-- `fun (N, a) ↦ satisfiesCnf a N` is decided by a polynomial-time
Turing machine — the headline statement consumed by `sat_NP`. Now
routed through the Lang layer; the underlying TM is produced by
`Compile evalCnfCmd`. -/
theorem inTimePolyTM_evalCnf :
    inTimePolyTM (fun Na : cnf × assgn => satisfiesCnf Na.2 Na.1) :=
  inTimePolyLang_to_inTimePoly inTimePolyLang_evalCnf

end EvalCnfTM

/-! ## `SAT ∈ NP` (unchanged from the pre-pivot version)

`sat_NP` rebuilds against `inTimePolyTM_evalCnf` exactly as before
— the *signature* of `inTimePolyTM_evalCnf` is stable across the
pivot; only its construction internals changed. -/

namespace SAT_inNP

theorem sat_NP : inNP SAT := by
  refine inNP_intro SAT (fun N a => satisfiesCnf a N) ?_ ?_
  · -- inTimePoly slot: the layer-backed evalCnf decider.
    exact EvalCnfTM.inTimePolyTM_evalCnf
  · -- polyCertRel slot: certificate compression (unchanged).
    refine ⟨⟨fun n => n ^ 2 + 1, ?_, ?_, ?_, ?_⟩⟩
    · intro N a h; exact ⟨a, h⟩
    · intro N ⟨a, ha⟩
      exact ⟨compressAssignment a N, (compressAssignment_cnf_equiv a N).mp ha,
             compressAssignment_size_bound a N⟩
    · exact ⟨2, ⟨2, 1, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩
    · intro a b h; nlinarith [Nat.pow_le_pow_left h 2]

end SAT_inNP
