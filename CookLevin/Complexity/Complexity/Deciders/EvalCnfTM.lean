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

**2026-06-10: `evalCnfDecidesLang` is COMPLETE and axiom-clean** (`[propext,
Classical.choice, Quot.sound]`): the per-clause contracts and the three
inner-body `Cmd`s are concrete and proven in `EvalCnfCmd.lean`. The remaining
`sorryAx` on `sat_NP` is only the compiler gadget layer (Risk C2,
Compile.lean).

Note: `inTimePolyTM_evalCnf` keeps its full name + signature so
`sat_NP` (below) does not need to change.
-/

namespace EvalCnfTM

open Complexity.Lang

/-- Polynomial time budget for `evalCnfTM`.

**⚠ 2026-06-09 (top-down): quartic, NOT the old `(n+1)^3`.** The cubic was
unprovable: the only loop-cost tool (`Cmd.cost_forBnd_le`) charges a *uniform*
worst-case per-iteration bound, so the nested clause/slot/member loops compound
to degree 4 (amortization over no-op slots is invisible to it). Downstream only
needs `inOPoly`, so the degree is free — see `EvalCnfCmd.evalCnfCmd_cost_bound`
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
(from `EvalCnfCmd`), and **every field is PROVEN, axiom-clean** (2026-06-10):
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
  -- (C2, B′ — LIVE PATH) `Compile.BitState (encodeState x)`: discharged by the
  -- UNARY encoding (variables as `1`-blocks, markers/separators in `{0,1}`).
  enc_bit := fun x => EvalCnfCmd.encodeState_bit x
  -- WALL / register frame. 16 (NOT 12 — the inner bodies need 4 scratch
  -- registers beyond the encoded 12; see the register-layout finding in
  -- `EvalCnfCmd.lean`). `encodeState` still lays out only 12 registers; the
  -- runtime padding (`Compile.paddedBitDeciderTM`) widens to 16.
  regBound := 16
  usesBelow := EvalCnfCmd.evalCnfCmd_usesBelow
  width_le := by
    intro x; rcases x with ⟨N, a⟩
    -- `encodeState (N, a)` is a 12-register literal; `12 ≤ 16`.
    show (EvalCnfCmd.encodeState (N, a)).length ≤ 16
    simp only [EvalCnfCmd.encodeState, List.length_cons, List.length_nil]
    omega
  -- Like the canonical `c_noConsLen`, this field is dropped entirely once
  -- `Op.consLen` is re-laid UNARY (HANDOFF.md bottom-up Task 4).
  noConsLen := EvalCnfCmd.evalCnfCmd_noConsLen
  -- (Route A) `evalCnfCmd` is trio-free, so its op cases are all proven —
  -- this is what keeps `SAT_inNP.sat_NP` axiom-clean.
  allOpsSupported := EvalCnfCmd.evalCnfCmd_allOpsSupported

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

/-- **Free-encoding layer-native NP witness for SAT** (S3-linchpin foundation).
Bundles the live free-encoding `evalCnf` verifier (`evalCnfDecidesLang`, a
`DecidesLang`) with the certificate relation (a satisfying assignment). Unlike the
opaque framework `inNP SAT`, this keeps the verifier program a recoverable `Cmd`,
which is what a future layer-routed `red_inNP` needs to precompose. `sat_NP` is now
re-derived from this via `inNPLangFree_to_inNP` (identical decider path — stays
axiom-clean). -/
theorem SAT_inNPLangFree : inNPLangFree SAT :=
  ⟨assgn, inferInstance, ⟨{
    rel := fun N a => satisfiesCnf a N
    dBound := timeBound
    dBound_poly := timeBound_inOPoly
    dBound_mono := timeBound_monotonic
    verifier := evalCnfDecidesLang
    rel_correct := ⟨⟨fun n => n ^ 2 + 1,
      fun N a h => ⟨a, h⟩,
      fun N ⟨a, ha⟩ => ⟨SAT_inNP.compressAssignment a N,
        (SAT_inNP.compressAssignment_cnf_equiv a N).mp ha,
        SAT_inNP.compressAssignment_size_bound a N⟩,
      ⟨2, ⟨2, 1, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩,
      fun a b h => by nlinarith [Nat.pow_le_pow_left h 2]⟩⟩ }⟩⟩

end EvalCnfTM

/-! ## `SAT ∈ NP` (unchanged from the pre-pivot version)

`sat_NP` rebuilds against `inTimePolyTM_evalCnf` exactly as before
— the *signature* of `inTimePolyTM_evalCnf` is stable across the
pivot; only its construction internals changed. -/

namespace SAT_inNP

theorem sat_NP : inNP SAT :=
  -- Routed through the free-encoding layer-native NP witness, so the verifier `Cmd`
  -- is preserved (recoverable) up to this bridge. Same decider path as before ⇒
  -- still `[propext, Classical.choice, Quot.sound]`.
  Complexity.Lang.inNPLangFree_to_inNP EvalCnfTM.SAT_inNPLangFree

end SAT_inNP
