import Complexity.Lang.Semantics
import Complexity.Lang.Frame
import Complexity.Lang.AppendGadget
import Complexity.Lang.ClearGadget
import Complexity.Complexity.TMPrimitives
import Complexity.Complexity.TapeMono
import Complexity.Lang.Compile.Core
import Complexity.Lang.Compile.Encoding
import Complexity.Lang.Compile.OpMachines
import Complexity.Lang.Compile.Cmd
import Complexity.Lang.Compile.RunClear
import Complexity.Lang.Compile.RunMove
import Complexity.Lang.Compile.RunCopyTail
import Complexity.Lang.Compile.RunEqBit

set_option autoImplicit false

/-! # `Compile/OpSound` — the per-op soundness contract + `seq` composition

Extracted from `Compile.lean` (refactor Phase 3). The residue-tolerant per-`Op`
physical contract `compileOp_sound_physical_residue` (discharged for the 8 proven
ops; 4 stub ops carry `sorry`) and the `compileSeq` physical/residue composition
lemmas (`compileSeq_sound_physical`/`_traj`/`_residue`/`_traj_residue`) +
`Compile_exit_lt`. Depends on `Compile/RunLemmas` (the per-op run lemmas) + `Cmd`. -/

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators

/-! ### C2 design validation: the RESIDUE-TOLERANT contract composes

The exact-tape contract is unsatisfiable for length-decreasing ops (the tape
never shrinks — `Complexity/Complexity/TapeMono.lean`,
`Compile.clear_physical_unsatisfiable`). The recommended fix is a *residue-
tolerant* contract: a gadget run on `encodeTape s ++ residue` halts (head `0`)
with tape `encodeTape output ++ residue'`, where every residue is a
`Compile.ValidResidue` (only interior symbols `{0,1,2}` — `< 4` and `≠ endMark`,
the `0`-filler left-shifting writes and the interior cells append carries out).

Before anyone builds the delete gadget / two-phase rewind on this design, the
two lemmas below **validate that it composes** — i.e. that residue threads
mechanically through the one combinator the whole `Cmd` induction rests on
(`compileSeq`). They are the residue-tolerant generalisations of
`compileSeq_sound_physical` / `compileSeq_traj_physical`, and they go through by
the *same* proof: `compileSeq_compose_physical` is already polymorphic in the
inter-fragment tape, so the only new obligation is that the intermediate tape's
symbols stay `< 4` — discharged by `ValidResidue` on the residue and
`encodeTape_lt_four` on the content. This de-risks the redesign: composition
does **not** blow up. (The residue stays `ValidResidue` and polynomially bounded
— `|residue| ≤ physical tape length ≤ size + cost` — but those are per-gadget
obligations, not composition obligations.) -/

/-- **Residue-tolerant `compileSeq` composition (PROVEN — design validation).**
The residue-tolerant generalisation of `compileSeq_sound_physical`: given two
fragments satisfying the residue-tolerant contract (head-`0` exit, tape
`encodeTape output ++ residue`), `compileSeq r1 r2` satisfies it with additive
budget `t₁ + 1 + t₂`. The input residue `res0` is unconstrained; only the
*inter-fragment* residue `res1` must be `ValidResidue` (so the seam tape's
symbols stay `< 4`). -/
theorem compileSeq_sound_physical_residue
    (r1 r2 : CompiledCmd) (s mid final : State)
    (res0 res1 res2 : List Nat)
    (hbit_mid : Compile.BitState mid)
    (hres1 : Compile.ValidResidue res1)
    {t1 t2 : Nat}
    (h_run1 : runFlatTM t1 r1.M (initFlatConfig r1.M [Compile.encodeTape s ++ res0])
                = some { state_idx := r1.exit,
                         tapes := [([], 0, Compile.encodeTape mid ++ res1)] })
    (h_traj1 : ∀ k, k < t1 → ∀ ck,
        runFlatTM k r1.M (initFlatConfig r1.M [Compile.encodeTape s ++ res0]) = some ck →
        ck.state_idx ≠ r1.exit ∧ haltingStateReached r1.M ck = false)
    (h_run2 : runFlatTM t2 r2.M (initFlatConfig r2.M [Compile.encodeTape mid ++ res1])
                = some { state_idx := r2.exit,
                         tapes := [([], 0, Compile.encodeTape final ++ res2)] })
    (h_halt2 : haltingStateReached r2.M
        { state_idx := r2.exit,
          tapes := [([], 0, Compile.encodeTape final ++ res2)] } = true) :
    runFlatTM (t1 + 1 + t2) (compileSeq r1 r2).M
        (initFlatConfig (compileSeq r1 r2).M [Compile.encodeTape s ++ res0])
      = some { state_idx := (compileSeq r1 r2).exit,
               tapes := [([], 0, Compile.encodeTape final ++ res2)] } ∧
    haltingStateReached (compileSeq r1 r2).M
      { state_idx := (compileSeq r1 r2).exit,
        tapes := [([], 0, Compile.encodeTape final ++ res2)] } = true := by
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape mid ++ res1)
      = some v → v < 4 := by
    intro v hv
    simp only [currentTapeSymbol] at hv
    split at hv
    case isTrue h =>
      rw [Option.some.injEq] at hv; subst hv
      have hmem := List.getElem_mem h
      rw [List.mem_append] at hmem
      rcases hmem with hm | hr
      · exact Compile.encodeTape_lt_four mid hbit_mid _ hm
      · exact (hres1 _ hr).1
    case isFalse => exact absurd hv (by simp)
  have key := compileSeq_compose_physical r1 r2
    (Compile.encodeTape s ++ res0) (Compile.encodeTape mid ++ res1)
    h_sym h_run1 h_traj1 h_run2 h_halt2
  rw [show (compileSeq r1 r2).exit = r2.exit + r1.M.states from Nat.add_comm ..]
  exact key

/-- **Residue-tolerant `compileSeq` trajectory (PROVEN — design validation).**
The residue-tolerant generalisation of `compileSeq_traj_physical`: if both
fragments never halt before their exit on the residue-carrying tapes, neither
does the composition. -/
theorem compileSeq_traj_physical_residue
    (r1 r2 : CompiledCmd) (s mid : State)
    (res0 res1 : List Nat)
    (hbit_mid : Compile.BitState mid)
    (hres1 : Compile.ValidResidue res1)
    {t1 t2 : Nat}
    (h_run1 : runFlatTM t1 r1.M (initFlatConfig r1.M [Compile.encodeTape s ++ res0])
                = some { state_idx := r1.exit,
                         tapes := [([], 0, Compile.encodeTape mid ++ res1)] })
    (h_traj1 : ∀ k, k < t1 → ∀ ck,
        runFlatTM k r1.M (initFlatConfig r1.M [Compile.encodeTape s ++ res0]) = some ck →
        ck.state_idx ≠ r1.exit ∧ haltingStateReached r1.M ck = false)
    (h_traj2 : ∀ k, k < t2 → ∀ ck,
        runFlatTM k r2.M (initFlatConfig r2.M [Compile.encodeTape mid ++ res1]) = some ck →
        ck.state_idx ≠ r2.exit ∧ haltingStateReached r2.M ck = false) :
    ∀ k, k < t1 + 1 + t2 → ∀ ck,
      runFlatTM k (compileSeq r1 r2).M
          (initFlatConfig (compileSeq r1 r2).M [Compile.encodeTape s ++ res0]) = some ck →
      ck.state_idx ≠ (compileSeq r1 r2).exit ∧
      haltingStateReached (compileSeq r1 r2).M ck = false := by
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape mid ++ res1)
      = some v → v < max r1.M.sig r2.M.sig := by
    intro v hv
    rw [r1.M_sig, r2.M_sig]
    simp only [currentTapeSymbol] at hv
    split at hv
    case isTrue h =>
      rw [Option.some.injEq] at hv; subst hv
      have hmem := List.getElem_mem h
      rw [List.mem_append] at hmem
      rcases hmem with hm | hr
      · exact Compile.encodeTape_lt_four mid hbit_mid _ hm
      · exact (hres1 _ hr).1
    case isFalse => exact absurd hv (by simp)
  have h_traj2' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k r2.M
          { state_idx := r2.M.start, tapes := [([], 0, Compile.encodeTape mid ++ res1)] }
        = some ck → haltingStateReached r2.M ck = false := by
    intro k hk ck hck
    exact (h_traj2 k hk ck hck).2
  have h_nohalt := composeFlatTM_no_early_halt r1.M_valid r2.M_valid r1.exit_lt
    (initFlatConfig r1.M [Compile.encodeTape s ++ res0]) r1.M_valid.1
    [] 0 (Compile.encodeTape mid ++ res1) h_sym h_run1 h_traj1 h_traj2'
  intro k hk ck hck
  refine ⟨?_, h_nohalt k hk ck hck⟩
  intro heq
  have hnh : haltingStateReached (compileSeq r1 r2).M ck = false := h_nohalt k hk ck hck
  have hh : haltingStateReached (compileSeq r1 r2).M ck = true := by
    show (compileSeq r1 r2).M.halt.getD ck.state_idx false = true
    rw [heq]
    have := (compileSeq r1 r2).exit_is_halt
    simp only [List.getD, this, Option.getD]
  rw [hh] at hnh
  exact absurd hnh Bool.noConfusion

set_option maxHeartbeats 2000000 in
/-- **The `concat` 4-stage budget certificate.** The sum of the four per-stage
budgets (`opCopy sb src1` over tape `L`; `opCopyAppend sb src2` over tape `L+V`;
`opCopy dst sb` over tape `L+V`; `clear sb` over tape `L+2V`) plus the three
`compileSeq` seams is `≤ (54L²+54L+180)·(2V+2)` — exactly the per-op contract
budget at `cost = 2V+1` (`a = |src1|`, `b = |src2|`, `V = a+b`). Proven via the
nonneg products `(L−a)·…`, `(L−b)·…` (cast to ℤ); worst-case headroom ~12%
(`probes/`-validated). The binding hypotheses `a ≤ L`, `b ≤ L` hold because each
operand's length is `≤ State.size s ≤ L`. -/
private theorem Compile.concat_budget_arith (a b L : Nat) (haL : a ≤ L) (hbL : b ≤ L) :
    (9*L*L+9*L+30)*(a+2)
      + ((b+1)*(5*(L+(a+b))+23)+3*(L+(a+b))+4)
      + (9*(L+(a+b))*(L+(a+b))+9*(L+(a+b))+30)*((a+b)+2)
      + (9*(L+2*(a+b))*(L+2*(a+b))+9)
      + 3
    ≤ (54*L*L+54*L+180)*(2*(a+b)+2) := by
  have ha : (0:ℤ) ≤ (a:ℤ) := Int.natCast_nonneg a
  have hb : (0:ℤ) ≤ (b:ℤ) := Int.natCast_nonneg b
  have haL' : (a:ℤ) ≤ (L:ℤ) := by exact_mod_cast haL
  have hbL' : (b:ℤ) ≤ (L:ℤ) := by exact_mod_cast hbL
  have hL : (0:ℤ) ≤ (L:ℤ) := le_trans ha haL'
  have dA : (0:ℤ) ≤ (L:ℤ) - a := sub_nonneg.2 haL'
  have dB : (0:ℤ) ≤ (L:ℤ) - b := sub_nonneg.2 hbL'
  zify
  nlinarith [mul_nonneg (mul_nonneg dA hL) ha, mul_nonneg (mul_nonneg dA ha) ha,
    mul_nonneg (mul_nonneg dB hL) hb, mul_nonneg (mul_nonneg dB hb) hb,
    mul_nonneg (mul_nonneg dA hL) hb, mul_nonneg (mul_nonneg dA ha) hb,
    mul_nonneg (mul_nonneg dB ha) hb, mul_nonneg (mul_nonneg dB hL) ha,
    mul_nonneg dA ha, mul_nonneg dB hb, mul_nonneg dA hb, mul_nonneg dB ha,
    mul_nonneg (mul_nonneg hL hL) ha, mul_nonneg (mul_nonneg hL hL) hb,
    mul_nonneg hL hL, hL, ha, hb]

/-- **`opConcat` run lemma — the full 4-stage `concat` gadget (PROVEN).** From
`encodeTape s ++ res_in`, the aliasing-safe scratch chain `opCopy sb src1 ⨾
opCopyAppend sb src2 ⨾ opCopy dst sb ⨾ clear sb` produces
`encodeTape (s.set dst (src1 ++ src2)) ++ res_out`, head `0`, with the per-op
W-invariant (residue grows by `2(|src1|+|src2|)` ≤ `cost`) and the contract
budget. The scratch `sb` holds the operands before `dst` is touched, so every
aliasing combination is correct. The four per-stage budgets compose to the
contract bound via `concat_budget_arith`. -/
theorem Compile.opConcat_run (s : State) (sb dst src1 src2 : Var)
    (hbit : Compile.BitState s)
    (hdst : dst < s.length) (hsrc1 : src1 < s.length) (hsrc2 : src2 < s.length)
    (hsb1 : sb + 1 < s.length) (hsbe : State.get s sb = [])
    (hdst_sb : dst < sb) (hsrc1_sb : src1 < sb) (hsrc2_sb : src2 < sb)
    (res_in : List Nat) (hres_in : Compile.ValidResidue res_in) :
    ∃ (t : Nat) (res_out : List Nat),
      Compile.ValidResidue res_out ∧
      State.size (s.set dst (State.get s src1 ++ State.get s src2)) + res_out.length
          ≤ State.size s + res_in.length
            + (2 * ((State.get s src1).length + (State.get s src2).length) + 1) ∧
      runFlatTM t (Compile.opConcat sb dst src1 src2).M
          (initFlatConfig (Compile.opConcat sb dst src1 src2).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opConcat sb dst src1 src2).exit,
                 tapes := [([], 0, Compile.encodeTape
                   (s.set dst (State.get s src1 ++ State.get s src2)) ++ res_out)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.opConcat sb dst src1 src2).M
              (initFlatConfig (Compile.opConcat sb dst src1 src2).M
                [Compile.encodeTape s ++ res_in]) = some ck →
          ck.state_idx ≠ (Compile.opConcat sb dst src1 src2).exit ∧
          haltingStateReached (Compile.opConcat sb dst src1 src2).M ck = false)
      ∧ t ≤ (54 * (Compile.encodeTape s ++ res_in).length
               * (Compile.encodeTape s ++ res_in).length
               + 54 * (Compile.encodeTape s ++ res_in).length + 180)
            * (2 * ((State.get s src1).length + (State.get s src2).length) + 1 + 1) := by
  -- abbreviations
  have hsb : sb < s.length := Nat.lt_of_succ_lt hsb1
  have hne_sb_src1 : sb ≠ src1 := Nat.ne_of_gt hsrc1_sb
  have hne_sb_src2 : sb ≠ src2 := Nat.ne_of_gt hsrc2_sb
  have hne_dst_sb : dst ≠ sb := Nat.ne_of_lt hdst_sb
  set V := State.get s src1 ++ State.get s src2 with hV
  set a := (State.get s src1).length with haa
  set b := (State.get s src2).length with hbb
  have hVlen : V.length = a + b := by rw [hV, List.length_append]
  -- element bounds for BitState
  have helem_src1 : ∀ x ∈ State.get s src1, x ≤ 1 := by
    intro x hx
    have hmem : State.get s src1 ∈ s := by
      rw [State.get, List.getElem?_eq_getElem hsrc1]; exact List.getElem_mem hsrc1
    exact hbit _ hmem x hx
  have helem_src2 : ∀ x ∈ State.get s src2, x ≤ 1 := by
    intro x hx
    have hmem : State.get s src2 ∈ s := by
      rw [State.get, List.getElem?_eq_getElem hsrc2]; exact List.getElem_mem hsrc2
    exact hbit _ hmem x hx
  have helem_V : ∀ x ∈ V, x ≤ 1 := by
    intro x hx; rw [hV, List.mem_append] at hx
    rcases hx with h | h
    · exact helem_src1 x h
    · exact helem_src2 x h
  -- stage states
  set mid1 := s.set sb (State.get s src1) with hmid1
  set mid2 := s.set sb V with hmid2
  set mid3 := mid2.set dst V with hmid3
  have hbit1 : Compile.BitState mid1 := Compile.BitState_set s sb _ hbit hsb helem_src1
  have hbit2 : Compile.BitState mid2 := Compile.BitState_set s sb V hbit hsb helem_V
  have hlen2 : mid2.length = s.length := Compile.length_set s sb V hsb
  have hdst2 : dst < mid2.length := by rw [hlen2]; exact hdst
  have hbit3 : Compile.BitState mid3 := Compile.BitState_set mid2 dst V hbit2 hdst2 helem_V
  have hlen1 : mid1.length = s.length := Compile.length_set s sb _ hsb
  have hsb_1 : sb < mid1.length := by rw [hlen1]; exact hsb
  have hsrc2_1 : src2 < mid1.length := by rw [hlen1]; exact hsrc2
  have hlen3 : mid3.length = s.length := by rw [hmid3, Compile.length_set mid2 dst V hdst2, hlen2]
  have hsb_3 : sb < mid3.length := by rw [hlen3]; exact hsb
  have hsb_2 : sb < mid2.length := by rw [hlen2]; exact hsb
  -- algebraic identities of the stage states
  have hmid1_sb : State.get mid1 sb = State.get s src1 := Compile.get_set_eq s sb _ hsb
  have hmid1_src2 : State.get mid1 src2 = State.get s src2 :=
    Compile.get_set_ne s sb _ src2 hsb (Ne.symm hne_sb_src2)
  have hmid1_to_mid2 : mid1.set sb (State.get mid1 sb ++ State.get mid1 src2) = mid2 := by
    rw [hmid1_sb, hmid1_src2, hmid1, Compile.set_set s sb _ _ hsb, ← hV]
  have hmid2_sb : State.get mid2 sb = V := Compile.get_set_eq s sb V hsb
  have hmid2_dst : State.get mid2 dst = State.get s dst :=
    Compile.get_set_ne s sb V dst hsb hne_dst_sb
  have hmid2_to_mid3 : mid2.set dst (State.get mid2 sb) = mid3 := by rw [hmid2_sb, hmid3]
  have hmid3_sb : State.get mid3 sb = V := by
    rw [hmid3, Compile.get_set_ne mid2 dst V sb hdst2 (Ne.symm hne_dst_sb), hmid2_sb]
  have hmid3_to_mid4 : mid3.set sb ([] : List Nat) = s.set dst V := by
    rw [hmid3, Compile.set_comm mid2 dst sb V [] hdst2 hsb_2 hne_dst_sb, hmid2,
        Compile.set_set s sb V [] hsb, ← hsbe, Compile.set_get_self s sb hsb]
  -- residues
  set resC := res_in ++ List.replicate (State.get s dst).length 0 with hresC
  have hresC_valid : Compile.ValidResidue resC :=
    Compile.ValidResidue_append_replicate_zero res_in _ hres_in
  set res_out := resC ++ List.replicate V.length 0 with hres_out
  have hres_out_valid : Compile.ValidResidue res_out :=
    Compile.ValidResidue_append_replicate_zero resC _ hresC_valid
  -- =========== STAGE RUNS ===========
  -- Stage A: opCopy sb src1
  obtain ⟨tA, hA_run, hA_traj, hA_bud⟩ :=
    Compile.opCopy_run s sb src1 hne_sb_src1 hsb hsrc1 hbit res_in hres_in
  -- residue: res_in ++ replicate |s.get sb| 0 = res_in (sb empty); output state = mid1
  rw [hsbe] at hA_run
  simp only [List.replicate, List.append_nil] at hA_run
  rw [← hmid1] at hA_run
  -- Stage B: opCopyAppend sb src2 on mid1
  obtain ⟨tB, hB_run, hB_traj, hB_bud⟩ :=
    Compile.opCopyAppend_run mid1 sb src2 hne_sb_src2 hsb_1 hsrc2_1 hbit1 res_in hres_in
  rw [hmid1_to_mid2] at hB_run hB_bud
  rw [hmid1_src2] at hB_bud
  -- Stage C: opCopy dst sb on mid2
  obtain ⟨tC, hC_run, hC_traj, hC_bud⟩ :=
    Compile.opCopy_run mid2 dst sb hne_dst_sb hdst2 hsb_2 hbit2 res_in hres_in
  rw [hmid2_dst] at hC_run
  rw [hmid2_to_mid3] at hC_run
  rw [hmid2_sb] at hC_bud
  -- Stage D: opClear sb on mid3
  obtain ⟨tD, hD_run_raw, hD_traj_raw, hD_bud⟩ :=
    Compile.clearRegionTM_run mid3 sb resC hsb_3 hbit3 hresC_valid
  -- convert to (opClear sb).M / init form, identify output
  have hD_start : (Compile.opClear sb).M.start = 0 := ClearGadget.clearRegionTM_start sb
  have hD_init : initFlatConfig (Compile.opClear sb).M [Compile.encodeTape mid3 ++ resC]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape mid3 ++ resC)] } := by
    simp only [initFlatConfig, hD_start, List.map_cons, List.map_nil]
  have hDeval : Op.eval (Op.clear sb) mid3 = s.set dst V := by
    show mid3.set sb [] = s.set dst V; exact hmid3_to_mid4
  have hD_res : resC ++ List.replicate (State.get mid3 sb).length 0 = res_out := by
    rw [hmid3_sb, hres_out]
  have hD_run : runFlatTM tD (Compile.opClear sb).M
        (initFlatConfig (Compile.opClear sb).M [Compile.encodeTape mid3 ++ resC])
      = some { state_idx := (Compile.opClear sb).exit,
               tapes := [([], 0, Compile.encodeTape (s.set dst V) ++ res_out)] } := by
    rw [hD_init]
    show runFlatTM tD (ClearGadget.clearRegionTM sb) _ = _
    rw [hDeval, hD_res] at hD_run_raw
    exact hD_run_raw
  have hD_traj : ∀ k, k < tD → ∀ ck,
      runFlatTM k (Compile.opClear sb).M
          (initFlatConfig (Compile.opClear sb).M [Compile.encodeTape mid3 ++ resC]) = some ck →
      ck.state_idx ≠ (Compile.opClear sb).exit ∧
      haltingStateReached (Compile.opClear sb).M ck = false := by
    rw [hD_init]; exact hD_traj_raw
  have hD_halt : haltingStateReached (Compile.opClear sb).M
      { state_idx := (Compile.opClear sb).exit,
        tapes := [([], 0, Compile.encodeTape (s.set dst V) ++ res_out)] } = true :=
    Compile.haltingStateReached_of_halt (Compile.opClear sb).exit_is_halt
  -- =========== COMPOSE RUNS (inside out) ===========
  -- CD = compileSeq (opCopy dst sb) (opClear sb): mid2 -> s.set dst V
  obtain ⟨hCD_run, hCD_halt⟩ := compileSeq_sound_physical_residue
    (Compile.opCopy dst sb) (Compile.opClear sb) mid2 mid3 (s.set dst V)
    res_in resC res_out hbit3 hresC_valid hC_run hC_traj hD_run hD_halt
  have hCD_traj := compileSeq_traj_physical_residue
    (Compile.opCopy dst sb) (Compile.opClear sb) mid2 mid3
    res_in resC hbit3 hresC_valid hC_run hC_traj hD_traj
  -- BCD = compileSeq (opCopyAppend sb src2) CD: mid1 -> s.set dst V
  obtain ⟨hBCD_run, hBCD_halt⟩ := compileSeq_sound_physical_residue
    (Compile.opCopyAppend sb src2) (compileSeq (Compile.opCopy dst sb) (Compile.opClear sb))
    mid1 mid2 (s.set dst V) res_in res_in res_out hbit2 hres_in hB_run hB_traj hCD_run hCD_halt
  have hBCD_traj := compileSeq_traj_physical_residue
    (Compile.opCopyAppend sb src2) (compileSeq (Compile.opCopy dst sb) (Compile.opClear sb))
    mid1 mid2 res_in res_in hbit2 hres_in hB_run hB_traj hCD_traj
  -- ABCD = compileSeq (opCopy sb src1) BCD: s -> s.set dst V = opConcat
  obtain ⟨hABCD_run, hABCD_halt⟩ := compileSeq_sound_physical_residue
    (Compile.opCopy sb src1)
    (compileSeq (Compile.opCopyAppend sb src2)
      (compileSeq (Compile.opCopy dst sb) (Compile.opClear sb)))
    s mid1 (s.set dst V) res_in res_in res_out hbit1 hres_in hA_run hA_traj hBCD_run hBCD_halt
  have hABCD_traj := compileSeq_traj_physical_residue
    (Compile.opCopy sb src1)
    (compileSeq (Compile.opCopyAppend sb src2)
      (compileSeq (Compile.opCopy dst sb) (Compile.opClear sb)))
    s mid1 res_in res_in hbit1 hres_in hA_run hA_traj hBCD_traj
  -- opConcat = that compileSeq chain (defeq)
  have hopc : Compile.opConcat sb dst src1 src2
      = compileSeq (Compile.opCopy sb src1)
          (compileSeq (Compile.opCopyAppend sb src2)
            (compileSeq (Compile.opCopy dst sb) (Compile.opClear sb))) := rfl
  -- =========== ASSEMBLE ===========
  refine ⟨tA + 1 + (tB + 1 + (tC + 1 + tD)), res_out, hres_out_valid, ?_, ?_, ?_, ?_⟩
  · -- W-invariant ①
    have hsz := State.size_set_add s dst V
    rw [hVlen] at hsz
    rw [hres_out, hresC]
    simp only [List.length_append, List.length_replicate, hVlen]
    omega
  · rw [hopc]; exact hABCD_run
  · rw [hopc]; exact hABCD_traj
  · -- BUDGET
    -- tape length facts
    set L := (Compile.encodeTape s ++ res_in).length with hLdef
    have ha_le_size : a ≤ State.size s := by
      have h := State.size_set_add s src1 ([] : List Nat)
      simp only [List.length_nil, Nat.add_zero] at h; rw [haa]; omega
    have hb_le_size : b ≤ State.size s := by
      have h := State.size_set_add s src2 ([] : List Nat)
      simp only [List.length_nil, Nat.add_zero] at h; rw [hbb]; omega
    have hsize_le_L : State.size s ≤ L := by
      rw [hLdef, List.length_append, Compile.encodeTape_length]; omega
    have haL : a ≤ L := le_trans ha_le_size hsize_le_L
    have hbL : b ≤ L := le_trans hb_le_size hsize_le_L
    -- LB / LC = L + (a+b)
    have hLBC : (Compile.encodeTape mid2 ++ res_in).length = L + (a + b) := by
      have hbal := Compile.encodeTape_set_length s sb V hsb
      rw [hsbe, List.length_nil, hVlen, ← hmid2] at hbal
      rw [List.length_append, hLdef, List.length_append]; omega
    -- LD = L + 2(a+b)
    have hLD : (Compile.encodeTape mid3 ++ resC).length = L + 2 * (a + b) := by
      have hbal2 := Compile.encodeTape_set_length mid2 dst V hdst2
      rw [hmid2_dst, hVlen, ← hmid3] at hbal2
      have hbal := Compile.encodeTape_set_length s sb V hsb
      rw [hsbe, List.length_nil, hVlen, ← hmid2] at hbal
      have hLe : L = (Compile.encodeTape s).length + res_in.length := by
        rw [hLdef, List.length_append]
      simp only [hresC, List.length_append, List.length_replicate]
      omega
    -- budget bounds in cert-term form
    have hbA : tA ≤ (9*L*L+9*L+30)*(a+2) := by rw [haa]; exact hA_bud
    have hbB : tB ≤ (b+1)*(5*(L+(a+b))+23)+3*(L+(a+b))+4 := by
      rw [← hLBC, hbb]; exact hB_bud
    have hbC : tC ≤ (9*(L+(a+b))*(L+(a+b))+9*(L+(a+b))+30)*((a+b)+2) := by
      rw [hLBC, hVlen] at hC_bud; exact hC_bud
    have hbD : tD ≤ 9*(L+2*(a+b))*(L+2*(a+b))+9 := by rw [← hLD]; exact hD_bud
    calc tA + 1 + (tB + 1 + (tC + 1 + tD))
        = tA + tB + tC + tD + 3 := by ring
      _ ≤ (9*L*L+9*L+30)*(a+2)
            + ((b+1)*(5*(L+(a+b))+23)+3*(L+(a+b))+4)
            + (9*(L+(a+b))*(L+(a+b))+9*(L+(a+b))+30)*((a+b)+2)
            + (9*(L+2*(a+b))*(L+2*(a+b))+9)
            + 3 := by gcongr
      _ ≤ (54*L*L+54*L+180)*(2*(a+b)+2) := Compile.concat_budget_arith a b L haL hbL
      _ = (54 * L * L + 54 * L + 180) * (2 * (a + b) + 1 + 1) := by ring


/-- **Residue-tolerant per-op physical contract (Risk C2, step 1c).** The fix
for the unsatisfiable exact-tape contract: the exit tape is
`encodeTape (Op.eval o s) ++ res_out` where `res_out` is `ValidResidue`,
hiding the residue existentially. For growth ops (`appendOne`/`appendZero`)
`res_out = res_in` (the residue passes through unchanged); for deletion ops
`res_out = res_in ++ [0, …]` (filler cells appended by `deleteCarryTM`).
The residue stays terminator-free across composition (each gadget preserves
`ValidResidue`), and `decodeTape` ignores it (`decodeTape_encodeTape_append`).

Input: the start tape may carry residue (`res_in`), since the previous
fragment's exit tape may have residue. The contract is:
  exit tape = `encodeTape (Op.eval o s) ++ res_out` (where `res_out` is
  `ValidResidue`), head rewound to `0`, in ≤ `9·inputTapeLen² + 9` steps.

This is the replacement for `compileOp_sound_physical` (which demanded
exact tape `encodeTape output` and was **unsatisfiable** for deletion ops).
The `compileSeq_sound_physical_residue` combinator composes these directly.

**⚠ 2026-06-01 — budget is QUADRATIC, not linear.** The per-op budget was
`3·tapeLen + 8` (linear), which the append ops meet (one insert = one O(tapeLen)
pass). But every **multi-cell** op is inherently **Θ(tapeLen²)** on a single-tape
machine: `clear`/`tail`/`copy`/… must delete or move `Θ(tapeLen)` cells, and each
deletion/insertion shifts the suffix in a separate O(tapeLen) pass (a single head
cannot shift a block by a data-dependent distance in one pass — it would have to
carry that distance in finite state). So the linear bound is **unsatisfiable** for
them; the budget is loosened to the quadratic `9·tapeLen² + 9` (constant generous,
tunable when the gadgets land). This composes fine: `compileSeq_sound_physical`
uses the *additive* budget `t₁+1+t₂` (no linearity assumed), so summing per-op
quadratics over `≤ cost` fragments (each tape `≤` the global max) gives a
polynomial total — `toFrameworkWitness'` only needs `inOPoly`.

**⚠ 2026-06-11c — budget is COST-SCALED: `(9·L²+9·L+30)·(cost+1)`.** The
multi-cell ops are *compositions* of quadratic phases: `copy dst src` is
`clear dst` (whose own proven black-box bound is `9·L²+9`) plus a `|src|`-round
cursor loop (each round `O(L)`), so the unscaled `9·L²+9·L+30` is unprovable for
it (the clear phase alone exhausts it). Scaling by `Op.cost o s + 1` funds the
loop rounds (`cost = |src|+1` for `copy`/`tail`) and is free for the consumer:
`run_physical_residue_gen`'s ② discharge pays `physStepBudget`'s
`(9G²+9G+33)·(8·cost+8)`, and `(9G²+9G+30)·(cost+1)` sits under it termwise
(`#eval`-validated against the real machines in `probes/CursorCopyProbe.lean`).

**⚠ 2026-06-20c — budget constant LOOSENED `9 → 27` (the `eqBit` enabler).** A
risk probe of the *full* `compareRegsTM` + d1 wrapper (`probes/EqBitBudgetProbe.lean`)
found that while the REAL steps fit `(9·L²+…)·2` at ~70%, the *provable* loose
bounds (every sub-gadget's `t ≤ …` recovered via the 2×-loose `navSteps_le` etc.)
**compound to ~121%** of the `cost=1` budget — and even near-perfect tight bounds
land at ~97% (fragile). The fix is to loosen the per-op CONTRACT budget constant
`9 → 27`: this is **free** because the consumer `run_physical_residue_gen` ②
discharges against `physStepBudget`'s `(9G²+9G+33)·(8·cost+8)` — an ~8× headroom
(`27 ≤ 72 = 8·9`), so `physStepBudget` is untouched and `Op.cost`/EvalCnf are
untouched (degree unchanged). The 7 proven ops relax their tight `(9·L²+…)` bounds
through `Compile.opBudgetLoosen`. Do NOT re-tighten — the eqBit cascade needs the
room (see HANDOFF bottom-up task 1, d2-iv). -/
theorem compileOp_sound_physical_residue (sb : Nat) (o : Op) (s : State) (res_in : List Nat)
    (hbit : Compile.BitState s) (hbnd : o.inBounds s)
    (hres_in : Compile.ValidResidue res_in)
    -- **Resolution B scratch hypotheses (eqBit/concat only; unused by the other ops).**
    -- The two pre-existing scratch registers `sb`, `sb + 1` are on-tape and empty.
    -- Supplied by `run_physical_residue_gen`'s op case from `hk` (the `+2` padding
    -- reservation) + `hscratch`. See HANDOFF Task 0b.
    (hsb1 : sb + 1 < s.length)
    (hsbe : State.get s sb = []) (hsb1e : State.get s (sb + 1) = [])
    -- **Operands live below the scratch base** (eqBit/concat only; from the gen lemma's
    -- `huses : Op.UsesBelow o k` with the scratch base `sb = k`). The eqBit gadget copies
    -- the operands into scratch `sb`/`sb+1`, so it needs them disjoint from scratch.
    (hbsb : Op.UsesBelow o sb)
    -- **Op-supportedness wall (Route A).** The trio `takeAt`/`dropAt`/`consLen`
    -- is still stubbed (gated on the unary migration); this hypothesis discharges
    -- their cases by `absurd` so the body is `sorry`-free. A concrete trio-free
    -- decider (`evalCnfCmd`) supplies it through `Cmd.AllOpsSupported`.
    (hsupp : Op.IsSupported o) :
    ∃ (t : Nat) (res_out : List Nat),
      Compile.ValidResidue res_out ∧
      -- ① the **W-invariant** (joint size+residue grows by ≤ cost). Non-compounding;
      -- this is what keeps the residue polynomially bounded across the whole
      -- `Compile_run_physical_residue` induction (see `run_physical_residue_gen`).
      State.size (Op.eval o s) + res_out.length
          ≤ State.size s + res_in.length + Op.cost o s ∧
      runFlatTM t (compileOp sb o).M
          (initFlatConfig (compileOp sb o).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (compileOp sb o).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval o s) ++ res_out)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (compileOp sb o).M
              (initFlatConfig (compileOp sb o).M [Compile.encodeTape s ++ res_in]) = some ck →
          ck.state_idx ≠ (compileOp sb o).exit ∧
          haltingStateReached (compileOp sb o).M ck = false)
      ∧ t ≤ (54 * (Compile.encodeTape s ++ res_in).length
               * (Compile.encodeTape s ++ res_in).length
               + 54 * (Compile.encodeTape s ++ res_in).length + 180)
            * (Op.cost o s + 1) := by
  cases o with
  | appendOne dst =>
      -- `res_out = res_in`: the append grows `encodeTape s` by one cell; residue passes through.
      -- The append op meets the *linear* `3·L+8`; relax to the contract's quadratic.
      obtain ⟨t, hrun, htraj, hbudget⟩ :=
        Compile.opAppendBit_physical_residue 1 (by omega) s dst hbit hbnd res_in hres_in
      exact ⟨t, res_in, hres_in,
        (by have := Op.size_eval_le (Op.appendOne dst) s; omega), hrun, htraj,
        Compile.opBudgetLoosen
          (le_trans (le_trans hbudget (Compile.linear_le_quadratic_tapeLen s res_in))
            (by show _ ≤ _ * (1 + 1); omega))⟩
  | appendZero dst =>
      obtain ⟨t, hrun, htraj, hbudget⟩ :=
        Compile.opAppendBit_physical_residue 0 (by omega) s dst hbit hbnd res_in hres_in
      exact ⟨t, res_in, hres_in,
        (by have := Op.size_eval_le (Op.appendZero dst) s; omega), hrun, htraj,
        Compile.opBudgetLoosen
          (le_trans (le_trans hbudget (Compile.linear_le_quadratic_tapeLen s res_in))
            (by show _ ≤ _ * (1 + 1); omega))⟩
  -- The 9 cross-register stub ops still need their gadgets (`copyBlockTM`, see ROADMAP C2.c).
  | clear dst =>
      -- `clearRegionTM_run` (step 5b) provides the run + no-early-halt trajectory; the loop
      -- frees `|s.get dst|` cells, each becoming a `0` residue cell.
      -- res_out = res_in ++ replicate |s.get dst| 0.
      obtain ⟨t, hrun, htraj, hbud⟩ := Compile.clearRegionTM_run s dst res_in hbnd hbit hres_in
      have hstart0 : (compileOp sb (Op.clear dst)).M.start = 0 := ClearGadget.clearRegionTM_start dst
      have hinit : initFlatConfig (compileOp sb (Op.clear dst)).M [Compile.encodeTape s ++ res_in]
          = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
        simp only [initFlatConfig, hstart0, List.map_cons, List.map_nil]
      refine ⟨t, res_in ++ List.replicate (s.get dst).length 0,
        Compile.ValidResidue_append_replicate_zero res_in _ hres_in, ?_, ?_, ?_,
        Compile.opBudgetLoosen (le_trans hbud (by show _ ≤ _ * (1 + 1); omega))⟩
      · -- ① the freed `|dst|` cells move into the residue: `W` is unchanged (cost ≥ 0).
        have h := State.size_set_add s dst ([] : List Nat)
        simp only [List.length_nil, Nat.add_zero] at h
        simp only [Op.eval, Op.cost, List.length_append, List.length_replicate]
        omega
      · rw [hinit]; exact hrun
      · intro k hk ck hck
        rw [hinit] at hck
        exact htraj k hk ck hck
  | copy dst src =>
      by_cases hds : dst = src
      · -- compile-time no-op: `Op.eval` is the identity, the machine is the
        -- 1-state immediate halt (`compiledCmd_default`), `t = 0`.
        subst hds
        have hM : compileOp sb (Op.copy dst dst) = compiledCmd_default := by
          show Compile.opCopy dst dst = compiledCmd_default
          rw [Compile.opCopy, if_pos rfl]
        have heval : Op.eval (Op.copy dst dst) s = s := by
          show s.set dst (State.get s dst) = s
          exact Compile.set_get_self s dst hbnd.1
        refine ⟨0, res_in, hres_in, ?_, ?_, ?_, ?_⟩
        · rw [heval]; simp only [Op.cost]; omega
        · rw [hM, heval]
          show some _ = some _
          rfl
        · intro k hk ck hck; omega
        · omega
      · obtain ⟨t, hrun, htraj, hbud⟩ :=
          Compile.opCopy_run s dst src hds hbnd.1 hbnd.2 hbit res_in hres_in
        refine ⟨t, res_in ++ List.replicate (State.get s dst).length 0,
          Compile.ValidResidue_append_replicate_zero res_in _ hres_in, ?_, hrun, htraj, ?_⟩
        · -- ① the freed `|dst₀|` cells move to the residue; `dst` gains `|src|`.
          have h := State.size_set_add s dst (State.get s src)
          simp only [Op.eval, Op.cost, List.length_append, List.length_replicate]
          omega
        · -- budget: `(9L²+9L+30)·(|src|+2) = (9L²+9L+30)·(cost+1)`, loosened to `27`.
          exact Compile.opBudgetLoosen hbud
  | tail dst src =>
      by_cases hds : dst = src
      · subst hds
        by_cases hemp : s.get dst = []
        · -- in-place, done branch: tape unchanged, residue passes through.
          obtain ⟨t, hrun, htraj, hbud⟩ :=
            Compile.opTailSelf_run_done s dst hbnd.1 hbit hemp res_in hres_in
          have heval : Op.eval (Op.tail dst dst) s = s := by
            show s.set dst (s.get dst).tail = s
            rw [hemp]
            show s.set dst ([] : List Nat) = s
            rw [← hemp]
            exact Compile.set_get_self s dst hbnd.1
          refine ⟨t, res_in, hres_in, ?_, ?_, htraj, ?_⟩
          · rw [heval]
            simp only [Op.cost]
            omega
          · rw [heval]
            exact hrun
          · -- `6L+13 ≤ (9L²+9L+30)·2 ≤ (9L²+9L+30)·(cost+1)`.
            have h2 : (9 * (Compile.encodeTape s ++ res_in).length
                  * (Compile.encodeTape s ++ res_in).length
                  + 9 * (Compile.encodeTape s ++ res_in).length + 30) * 2
                ≤ (9 * (Compile.encodeTape s ++ res_in).length
                  * (Compile.encodeTape s ++ res_in).length
                  + 9 * (Compile.encodeTape s ++ res_in).length + 30)
                  * (Op.cost (Op.tail dst dst) s + 1) := by
              refine Nat.mul_le_mul_left _ ?_
              simp only [Op.cost]
              omega
            exact Compile.opBudgetLoosen (le_trans (le_trans hbud (by omega)) h2)
        · -- in-place, delete branch: exact residue `res_in ++ [0]`.
          obtain ⟨t, hrun, htraj, hbud⟩ :=
            Compile.opTailSelf_run_delete s dst hbnd.1 hbit hemp res_in hres_in
          refine ⟨t, res_in ++ [0],
            Compile.ValidResidue_append_replicate_zero res_in 1 hres_in, ?_, hrun, htraj, ?_⟩
          · -- ① the deleted cell moves to the residue: `W` is unchanged.
            have h := State.size_set_add s dst (s.get dst).tail
            have hlen : (s.get dst).tail.length = (s.get dst).length - 1 := List.length_tail
            have hpos : 0 < (s.get dst).length := List.length_pos_iff.mpr hemp
            simp only [Op.eval, Op.cost, List.length_append, List.length_cons,
              List.length_nil]
            omega
          · have h2 : (9 * (Compile.encodeTape s ++ res_in).length
                  * (Compile.encodeTape s ++ res_in).length
                  + 9 * (Compile.encodeTape s ++ res_in).length + 30) * 2
                ≤ (9 * (Compile.encodeTape s ++ res_in).length
                  * (Compile.encodeTape s ++ res_in).length
                  + 9 * (Compile.encodeTape s ++ res_in).length + 30)
                  * (Op.cost (Op.tail dst dst) s + 1) := by
              refine Nat.mul_le_mul_left _ ?_
              simp only [Op.cost]
              omega
            exact Compile.opBudgetLoosen (le_trans (le_trans hbud (by omega)) h2)
      · obtain ⟨t, hrun, htraj, hbud⟩ :=
          Compile.opTail_run s dst src hds hbnd.1 hbnd.2 hbit res_in hres_in
        refine ⟨t, res_in ++ List.replicate (State.get s dst).length 0,
          Compile.ValidResidue_append_replicate_zero res_in _ hres_in, ?_, hrun, htraj, ?_⟩
        · -- ① the freed `|dst₀|` cells move to the residue; `dst` gains `|src| − 1`.
          have h := State.size_set_add s dst (State.get s src).tail
          have hlen : (State.get s src).tail.length = (State.get s src).length - 1 :=
            List.length_tail
          simp only [Op.eval, Op.cost, List.length_append, List.length_replicate]
          omega
        · -- budget: `(9L²+9L+30)·(|src|+2) = (9L²+9L+30)·(cost+1)`, loosened to `27`.
          exact Compile.opBudgetLoosen hbud
  | head dst src =>
      obtain ⟨t, hrun, htraj, hbud⟩ :=
        Compile.opHead_run s dst src res_in hbit hbnd.1 hbnd.2 hres_in
      refine ⟨t, res_in ++ List.replicate (s.get dst).length 0,
        Compile.ValidResidue_append_replicate_zero res_in _ hres_in, ?_, hrun, htraj,
        Compile.opBudgetLoosen (le_trans hbud (by show _ ≤ _ * (1 + 1); omega))⟩
      · -- ① `head` writes `≤ 1` cell to `dst`; freed cells go to residue.
        rcases hsrc : s.get src with _ | ⟨x, xs⟩
        · have h := State.size_set_add s dst ([] : List Nat)
          simp only [Op.eval, Op.cost, hsrc, List.length_append, List.length_replicate,
            List.length_nil, Nat.add_zero] at h ⊢
          omega
        · have h := State.size_set_add s dst [x]
          simp only [Op.eval, Op.cost, hsrc, List.length_append, List.length_replicate,
            List.length_cons, List.length_nil] at h ⊢
          omega
  | eqBit dst src1 src2 =>
      -- Operands live below the scratch base (`hbsb`); feed the proven no-grow gadget.
      obtain ⟨hdst, hsrc1, hsrc2⟩ := hbsb
      obtain ⟨res_out, hres_valid, hres_len, t, hrun, htraj, hbud⟩ :=
        Compile.opEqBitNG_run s sb dst src1 src2 res_in hbit hsb1 hsbe hsb1e hdst hsrc1 hsrc2 hres_in
      have hM : compileOp sb (Op.eqBit dst src1 src2) = Compile.opEqBitNG sb dst src1 src2 := rfl
      refine ⟨t, res_out, hres_valid, ?_, ?_, ?_, ?_⟩
      · -- ① W-invariant equality: `eqBit` writes one bit to `dst`; `res_out` grows by
        -- `|src1|+|src2|+|dst|` = `cost + |dst| - 1`, exactly balancing the freed `|dst|` cells.
        have hval : (if s.get src1 = s.get src2 then ([1] : List Nat) else [0]).length = 1 := by
          by_cases hb : s.get src1 = s.get src2 <;> simp [hb]
        have hsz := State.size_set_add s dst (if s.get src1 = s.get src2 then ([1] : List Nat) else [0])
        rw [hval] at hsz
        simp only [Op.eval, Op.cost] at hsz ⊢
        omega
      · rw [hM]; exact hrun
      · rw [hM]; exact htraj
      · -- budget: `opEqBitNG_run` already proves the exact `(54·L²+54·L+180)·(cost+1)` form.
        exact hbud
  | nonEmpty dst src =>
      obtain ⟨t, hrun, htraj, hbud⟩ :=
        Compile.opNonEmpty_run s dst src res_in hbit hbnd.1 hbnd.2 hres_in
      refine ⟨t, res_in ++ List.replicate (s.get dst).length 0,
        Compile.ValidResidue_append_replicate_zero res_in _ hres_in, ?_, hrun, htraj,
        Compile.opBudgetLoosen (le_trans hbud (by show _ ≤ _ * (1 + 1); omega))⟩
      · -- ① `nonEmpty` writes exactly `1` cell to `dst`; freed cells go to residue.
        have h := State.size_set_add s dst (if (s.get src).isEmpty then ([0] : List Nat) else [1])
        have hv : (if (s.get src).isEmpty then ([0] : List Nat) else [1]).length = 1 := by
          by_cases hb : (s.get src).isEmpty <;> simp [hb]
        rw [hv] at h
        simp only [Op.eval, Op.cost, List.length_append, List.length_replicate]
        omega
  | takeAt dst src lenReg => simp only [Op.IsSupported] at hsupp
  | dropAt dst src lenReg => simp only [Op.IsSupported] at hsupp
  | concat dst src1 src2 =>
      obtain ⟨hdst_sb, hsrc1_sb, hsrc2_sb⟩ := hbsb
      exact Compile.opConcat_run s sb dst src1 src2 hbit hbnd.1 hbnd.2.1 hbnd.2.2
        hsb1 hsbe hdst_sb hsrc1_sb hsrc2_sb res_in hres_in
  | consLen dst lenSrc src => simp only [Op.IsSupported] at hsupp

/-- **Physical-contract `compileSeq` composition (PROVEN).** Given two
sub-machines each satisfying the physical contract (head-`0` exit, exact tape,
trajectory), `compileSeq r1 r2` satisfies it with additive budget `t₁ + 1 + t₂`.
This is the proved instance of `compileSeq_compose_physical` lifted to the
`CompiledCmd` level.

The head-`0` exit of `r1` makes its exit config literally equal to
`initFlatConfig r2.M [enc_output₁]`, so `r2`'s physical contract plugs
straight in. -/
theorem compileSeq_sound_physical
    (r1 r2 : CompiledCmd) (s mid final : State)
    (hbit_s : Compile.BitState s)
    (hbit_mid : Compile.BitState mid)
    {t1 t2 : Nat}
    (h_run1 : runFlatTM t1 r1.M (initFlatConfig r1.M [Compile.encodeTape s])
                = some { state_idx := r1.exit,
                         tapes := [([], 0, Compile.encodeTape mid)] })
    (h_traj1 : ∀ k, k < t1 → ∀ ck,
        runFlatTM k r1.M (initFlatConfig r1.M [Compile.encodeTape s]) = some ck →
        ck.state_idx ≠ r1.exit ∧ haltingStateReached r1.M ck = false)
    (h_run2 : runFlatTM t2 r2.M (initFlatConfig r2.M [Compile.encodeTape mid])
                = some { state_idx := r2.exit,
                         tapes := [([], 0, Compile.encodeTape final)] })
    (h_traj2 : ∀ k, k < t2 → ∀ ck,
        runFlatTM k r2.M (initFlatConfig r2.M [Compile.encodeTape mid]) = some ck →
        ck.state_idx ≠ r2.exit ∧ haltingStateReached r2.M ck = false)
    (h_halt2 : haltingStateReached r2.M
        { state_idx := r2.exit,
          tapes := [([], 0, Compile.encodeTape final)] } = true) :
    runFlatTM (t1 + 1 + t2) (compileSeq r1 r2).M
        (initFlatConfig (compileSeq r1 r2).M [Compile.encodeTape s])
      = some { state_idx := (compileSeq r1 r2).exit,
               tapes := [([], 0, Compile.encodeTape final)] } ∧
    haltingStateReached (compileSeq r1 r2).M
      { state_idx := (compileSeq r1 r2).exit,
        tapes := [([], 0, Compile.encodeTape final)] } = true := by
  -- The head-0 exit of r1 makes its config = initFlatConfig r2 [encodeTape mid].
  -- Feed into the already-proven `compileSeq_compose_physical`.
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape mid)
      = some v → v < 4 := by
    intro v hv
    simp only [currentTapeSymbol] at hv
    split at hv
    case isTrue h =>
      rw [Option.some.injEq] at hv; subst hv
      exact Compile.encodeTape_lt_four mid hbit_mid _
        (List.getElem_mem h)
    case isFalse => exact absurd hv (by simp)
  -- `compileSeq_compose_physical` produces `cfg2.state_idx + r1.M.states` where
  -- `cfg2 = { state_idx := r2.exit, … }`, giving `r2.exit + r1.M.states`.
  -- Our conclusion uses `(compileSeq r1 r2).exit = r1.M.states + r2.exit`.
  have key := compileSeq_compose_physical r1 r2 (Compile.encodeTape s) (Compile.encodeTape mid)
    h_sym h_run1 h_traj1 h_run2 h_halt2
  -- key : runFlatTM … = some { state_idx := r2.exit + r1.M.states, … } ∧ …
  -- goal : … (compileSeq r1 r2).exit = r1.M.states + r2.exit …
  rw [show (compileSeq r1 r2).exit = r2.exit + r1.M.states from Nat.add_comm ..]
  exact key

/-- **Physical-contract trajectory for `compileSeq` (PROVEN).** If both
sub-machines never halt before their exit, neither does the composition. -/
theorem compileSeq_traj_physical
    (r1 r2 : CompiledCmd) (s mid : State)
    (hbit_mid : Compile.BitState mid)
    {t1 t2 : Nat}
    (h_run1 : runFlatTM t1 r1.M (initFlatConfig r1.M [Compile.encodeTape s])
                = some { state_idx := r1.exit,
                         tapes := [([], 0, Compile.encodeTape mid)] })
    (h_traj1 : ∀ k, k < t1 → ∀ ck,
        runFlatTM k r1.M (initFlatConfig r1.M [Compile.encodeTape s]) = some ck →
        ck.state_idx ≠ r1.exit ∧ haltingStateReached r1.M ck = false)
    (h_traj2 : ∀ k, k < t2 → ∀ ck,
        runFlatTM k r2.M (initFlatConfig r2.M [Compile.encodeTape mid]) = some ck →
        ck.state_idx ≠ r2.exit ∧ haltingStateReached r2.M ck = false) :
    ∀ k, k < t1 + 1 + t2 → ∀ ck,
      runFlatTM k (compileSeq r1 r2).M
          (initFlatConfig (compileSeq r1 r2).M [Compile.encodeTape s]) = some ck →
      ck.state_idx ≠ (compileSeq r1 r2).exit ∧
      haltingStateReached (compileSeq r1 r2).M ck = false := by
  -- Use `composeFlatTM_no_early_halt` for `haltingStateReached = false`,
  -- then derive `state_idx ≠ exit` from `exit_is_halt` + `halt_unique`.
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape mid)
      = some v → v < max r1.M.sig r2.M.sig := by
    intro v hv
    rw [r1.M_sig, r2.M_sig]
    simp only [currentTapeSymbol] at hv
    split at hv
    case isTrue h =>
      rw [Option.some.injEq] at hv; subst hv
      exact Compile.encodeTape_lt_four mid hbit_mid _
        (List.getElem_mem h)
    case isFalse => exact absurd hv (by simp)
  have h_traj2' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k r2.M { state_idx := r2.M.start, tapes := [([], 0, Compile.encodeTape mid)] }
        = some ck → haltingStateReached r2.M ck = false := by
    intro k hk ck hck
    exact (h_traj2 k hk ck hck).2
  have h_nohalt := composeFlatTM_no_early_halt r1.M_valid r2.M_valid r1.exit_lt
    (initFlatConfig r1.M [Compile.encodeTape s]) r1.M_valid.1
    [] 0 (Compile.encodeTape mid) h_sym h_run1 h_traj1 h_traj2'
  -- h_nohalt : ∀ k < …, … haltingStateReached (composeFlatTM r1.M r2.M r1.exit) ck = false
  -- The goal's `(compileSeq r1 r2).M` = `composeFlatTM r1.M r2.M r1.exit` by definition,
  -- and `(compileSeq r1 r2).exit` = `r1.M.states + r2.exit`. Both unfold by `dsimp [compileSeq]`.
  intro k hk ck hck
  constructor
  · -- `state_idx ≠ exit`: if equal, `exit_is_halt` makes `haltingStateReached = true`.
    intro heq
    have hnh : haltingStateReached (compileSeq r1 r2).M ck = false :=
      h_nohalt k hk ck hck
    -- `exit_is_halt : M.halt[exit]? = some true`
    -- `haltingStateReached M ck = M.halt.getD ck.state_idx false`
    -- With heq, getD exit false = (some true).getD false = true.
    have hh : haltingStateReached (compileSeq r1 r2).M ck = true := by
      show (compileSeq r1 r2).M.halt.getD ck.state_idx false = true
      rw [heq]
      -- Now: (compileSeq r1 r2).M.halt.getD (compileSeq r1 r2).exit false = true
      -- This follows from exit_is_halt.
      have := (compileSeq r1 r2).exit_is_halt
      -- this : (compileSeq r1 r2).M.halt[(compileSeq r1 r2).exit]? = some true
      simp only [List.getD, this, Option.getD]
    rw [hh] at hnh
    exact absurd hnh Bool.noConfusion
  · exact h_nohalt k hk ck hck

theorem Compile_exit_lt (sb : Nat) (c : Cmd) : Compile.exit sb c < (Compile sb c).states :=
  (compileCmd sb c).exit_lt
