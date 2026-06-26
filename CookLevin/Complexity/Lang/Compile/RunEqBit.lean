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
import Complexity.Lang.Compile.RunCopyTail

/-! # `Compile/RunEqBit` — `eqBit` no-grow consume-loop run stack (Phase 1-refinement)

Last module of the `RunLemmas` split (see `REFACTOR-HANDOFF.md`). The `eqBit`
no-grow consume-loop run stack: the `iterTailsTM` ITERATE leaf, the
`navTestRewindM`/`readBitRewindM`/`eqVerdictM`/`bitCompareM`/`bothNonemptyM`
helpers, the `compareLoopTM` consume loop, and the relocated no-grow run stack
ending at `opEqBitNG_run`. Imports `RunCopyTail` (reuses copy/tail machinery). -/

set_option autoImplicit false

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators

/-! ### `eqBit` consume-loop body — the ITERATE machine (bottom-up, Risk C2)

The `eqBit` gadget (design A) compares two scratch copies by a `loopTM` whose body
ITERATEs — deleting BOTH heads — while the two scratch regs are nonempty and their
heads match. Entered with the head restored to `0`, that delete-both step is just
`opTail sc1 sc1 ⨾ opTail sc2 sc2`, a clean `composeFlatTM` of the proven in-place
self-tail run (`opTailSelf_run_delete`). This is `Compile.iterTailsTM`; its run
lemma below is the body's ITERATE leaf (reused by the consume-loop run lemma —
HANDOFF bottom-up task 1, d2a). Probe-validated end-to-end in
`probes/CompareBodyProbe.lean`. -/

/-! #### `iterTailsTM` structural lemmas (the loop-body ITERATE leaf) -/

/-- **ITERATE leaf run.** From `encodeTape s ++ res` at head `0` with `sc1 ≠ sc2`
both nonempty, `iterTailsTM` deletes both heads in place, landing at the composed
exit with `encodeTape ((s.set sc1 (s.get sc1).tail).set sc2 (s.get sc2).tail)`, the
residue gaining two `0` fillers. -/
theorem Compile.iterTails_run (s : State) (sc1 sc2 : Var) (hne : sc1 ≠ sc2)
    (h1 : sc1 < s.length) (h2 : sc2 < s.length) (hbit : Compile.BitState s)
    (hne1 : s.get sc1 ≠ []) (hne2 : s.get sc2 ≠ [])
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.iterTailsTM sc1 sc2)
          (initFlatConfig (Compile.iterTailsTM sc1 sc2) [Compile.encodeTape s ++ res])
        = some { state_idx := (Compile.opTail sc2 sc2).exit + (Compile.opTail sc1 sc1).M.states,
                 tapes := [([], 0,
                   Compile.encodeTape ((s.set sc1 (s.get sc1).tail).set sc2 (s.get sc2).tail)
                     ++ (res ++ [0, 0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.iterTailsTM sc1 sc2)
              (initFlatConfig (Compile.iterTailsTM sc1 sc2) [Compile.encodeTape s ++ res]) = some ck →
          haltingStateReached (Compile.iterTailsTM sc1 sc2) ck = false)
      ∧ t ≤ 12 * (Compile.encodeTape s ++ res).length + 29 := by
  obtain ⟨t1, hrun1, htraj1, ht1le⟩ := Compile.opTailSelf_run_delete s sc1 h1 hbit hne1 res hres
  set s' := s.set sc1 (s.get sc1).tail with hs'
  have hlen' : s'.length = s.length := Compile.length_set s sc1 _ h1
  have h2' : sc2 < s'.length := by rw [hlen']; exact h2
  have hbit' : Compile.BitState s' := by
    apply Compile.BitState_set s sc1 _ hbit h1
    intro x hx
    exact hbit (s.get sc1)
      (by rw [State.get, List.getElem?_eq_getElem h1]; exact List.getElem_mem h1) x
      (List.tail_subset _ hx)
  have hget' : s'.get sc2 = s.get sc2 := State.get_set_ne s sc1 _ sc2 (Ne.symm hne)
  have hne2' : s'.get sc2 ≠ [] := by rw [hget']; exact hne2
  have hres' : Compile.ValidResidue (res ++ [0]) := by
    have := Compile.ValidResidue_append_replicate_zero res 1 hres
    simpa using this
  obtain ⟨t2, hrun2, htraj2, ht2le⟩ :=
    Compile.opTailSelf_run_delete s' sc2 h2' hbit' hne2' (res ++ [0]) hres'
  set right1 : List Nat := Compile.encodeTape s' ++ (res ++ [0]) with hr1
  have hvalid1 : validFlatTM (Compile.opTail sc1 sc1).M := (Compile.opTail sc1 sc1).M_valid
  have hvalid2 : validFlatTM (Compile.opTail sc2 sc2).M := (Compile.opTail sc2 sc2).M_valid
  have hinit1 : initFlatConfig (Compile.opTail sc1 sc1).M [Compile.encodeTape s ++ res]
      = { state_idx := (Compile.opTail sc1 sc1).M.start,
          tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    simp only [initFlatConfig, List.map_cons, List.map_nil]
  rw [hinit1] at hrun1 htraj1
  have hinit2 : initFlatConfig (Compile.opTail sc2 sc2).M [Compile.encodeTape s' ++ (res ++ [0])]
      = { state_idx := (Compile.opTail sc2 sc2).M.start, tapes := [([], 0, right1)] } := by
    simp only [initFlatConfig, hr1, List.map_cons, List.map_nil]
  rw [hinit2] at hrun2 htraj2
  have hLpos : 0 < (Compile.encodeTape s').length := by rw [Compile.encodeTape]; simp
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, right1) = some v →
      v < max (Compile.opTail sc1 sc1).M.sig (Compile.opTail sc2 sc2).M.sig := by
    intro v hv
    have hlt : (0 : Nat) < right1.length := by rw [hr1, List.length_append]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have h0 : right1[0]? = some 3 := by
      rw [hr1, List.getElem?_append_left hLpos, Compile.encodeTape]; rfl
    have hhead : right1.get ⟨0, hlt⟩ = 3 := by
      rw [List.get_eq_getElem]
      exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans h0)
    have hv3 : v = 3 := by rw [← Option.some.inj hv]; exact hhead
    rw [hv3, (Compile.opTail sc1 sc1).M_sig, (Compile.opTail sc2 sc2).M_sig]; omega
  have hhalt2 : haltingStateReached (Compile.opTail sc2 sc2).M
      { state_idx := (Compile.opTail sc2 sc2).exit,
        tapes := [([], 0, Compile.encodeTape (s'.set sc2 (s'.get sc2).tail)
                    ++ ((res ++ [0]) ++ [0]))] } = true := by
    show (Compile.opTail sc2 sc2).M.halt.getD (Compile.opTail sc2 sc2).exit false = true
    rw [List.getD_eq_getElem?_getD, (Compile.opTail sc2 sc2).exit_is_halt]; rfl
  have hcomp := composeFlatTM_run hvalid1 hvalid2 (Compile.opTail sc1 sc1).exit_lt
    { state_idx := (Compile.opTail sc1 sc1).M.start,
      tapes := [([], 0, Compile.encodeTape s ++ res)] }
    hvalid1.1 [] 0 right1 hsym hrun1 htraj1 hrun2 hhalt2
  have hcomp_traj := composeFlatTM_no_early_halt hvalid1 hvalid2 (Compile.opTail sc1 sc1).exit_lt
    { state_idx := (Compile.opTail sc1 sc1).M.start,
      tapes := [([], 0, Compile.encodeTape s ++ res)] }
    hvalid1.1 [] 0 right1 hsym hrun1 htraj1
    (fun k hk ck hck => (htraj2 k hk ck hck).2)
  have hcfg0 : initFlatConfig (Compile.iterTailsTM sc1 sc2) [Compile.encodeTape s ++ res]
      = { state_idx := (Compile.opTail sc1 sc1).M.start,
          tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    simp only [initFlatConfig, Compile.iterTailsTM, composeFlatTM_start, List.map_cons, List.map_nil]
  refine ⟨t1 + 1 + t2, ?_, ?_, ?_⟩
  · rw [hcfg0]
    have htape : Compile.encodeTape (s'.set sc2 (s'.get sc2).tail) ++ ((res ++ [0]) ++ [0])
        = Compile.encodeTape ((s.set sc1 (s.get sc1).tail).set sc2 (s.get sc2).tail)
            ++ (res ++ [0, 0]) := by
      rw [hget', hs']; simp [List.append_assoc]
    show runFlatTM (t1 + 1 + t2)
        (composeFlatTM (Compile.opTail sc1 sc1).M (Compile.opTail sc2 sc2).M (Compile.opTail sc1 sc1).exit)
        _ = _
    rw [hcomp.1, ← htape]
  · rw [hcfg0]
    exact hcomp_traj
  · -- step bound: both in-place tails cost ≤ 6·L+14 on the invariant tape length L.
    have hbal := Compile.encodeTape_set_length s sc1 (s.get sc1).tail h1
    have htail : (s.get sc1).tail.length + 1 = (s.get sc1).length := by
      cases hh : s.get sc1 with
      | nil => exact absurd hh hne1
      | cons a t => simp
    have hLeq : right1.length ≤ (Compile.encodeTape s ++ res).length := by
      rw [hr1, hs']
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    omega

/-! ### `opRewindToZero` — a halt-unique "rewind to the leading sentinel" leaf
(bottom-up, Risk C2)

Every `eqBit` sub-machine whose *last* action is a rewind (the verdict's EQ/NEQ
leaves; the consume-loop testMachine's restored exits) needs a rewind that is a
clean single-exit `CompiledCmd`. `composeFlatTM` only zeroes the halts of its
**first** argument (`composedHalt = replicate M₁.states false ++ M₂.halt`), so a
rewind used as the *trailing* machine keeps its stray boundary halt (state `2` of
`scanLeftUntilTM`), violating `halt_unique`. `opRewindToZero` demotes that
boundary via `joinTwoHalts`, giving a reusable head-→`0` leaf. -/

/-- state `2` is a (static) halt of `justRewindTM`, so a config the trajectory
proves "not halting" cannot sit there. -/
private theorem Compile.justRewind_not_state2 {ck : FlatTMConfig}
    (hnh : haltingStateReached (ScanLeft.scanLeftUntilTM 4 3) ck = false) :
    ck.state_idx ≠ 2 := by
  intro hc
  have hhalt : haltingStateReached (ScanLeft.scanLeftUntilTM 4 3) ck = true := by
    show ([false, true, true] : List Bool).getD ck.state_idx false = true
    rw [hc]; rfl
  exact absurd (hhalt.symm.trans hnh) (by decide)

/-- **`opRewindToZero` run + no-early-exit/no-early-halt trajectory.** From an
interior head `head` on `(left, head, 3 :: rest)` with `rest[0..head)`
terminator-free (`< 4` and `≠ 3`), rewinds to head `0` in `head + 1` steps,
landing at the unique exit `1`. The demoted boundary `2` is never visited. -/
theorem Compile.opRewindToZero_run (left rest : List Nat) (head : Nat)
    (h_head : head ≤ rest.length)
    (h_cells : ∀ i, i < head → ∃ (h : i < rest.length),
      rest.get ⟨i, h⟩ < 4 ∧ rest.get ⟨i, h⟩ ≠ 3) :
    runFlatTM (head + 1) Compile.opRewindToZero.M
        { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
      = some { state_idx := Compile.opRewindToZero.exit, tapes := [(left, 0, 3 :: rest)] }
    ∧ (∀ k, k < head + 1 → ∀ ck,
        runFlatTM k Compile.opRewindToZero.M
            { state_idx := 0, tapes := [(left, head, 3 :: rest)] } = some ck →
        ck.state_idx ≠ Compile.opRewindToZero.exit ∧
        haltingStateReached Compile.opRewindToZero.M ck = false) := by
  have hrun := ScanLeft.rewindToStart_run 4 3 left rest head h_head h_cells
  have htraj := ScanLeft.rewindToStart_traj 4 3 left rest head h_head h_cells
  have hjr : ClearGadget.justRewindTM = ScanLeft.scanLeftUntilTM 4 3 := rfl
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [(left, head, (3 : Nat) :: rest)] } with hcfg0
  have hM : Compile.opRewindToZero.M = joinTwoHalts ClearGadget.justRewindTM 1 2 := rfl
  have hE : Compile.opRewindToZero.exit = 1 := rfl
  -- the M-run never visits the demoted state `2` within `head+1` steps.
  have hnv : ∀ k, k ≤ head + 1 → ∀ ck,
      runFlatTM k ClearGadget.justRewindTM cfg0 = some ck → ck.state_idx ≠ 2 := by
    intro k hk ck hck
    rw [hjr] at hck
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · exact Compile.justRewind_not_state2 (htraj k hlt ck hck).2
    · have heq : ck = { state_idx := 1, tapes := [(left, 0, (3 : Nat) :: rest)] } :=
        Option.some.inj (hck.symm.trans hrun)
      rw [heq]; show (1 : Nat) ≠ 2; omega
  refine ⟨?_, ?_⟩
  · rw [hM, hE, joinTwoHalts_run_eq _ 1 2 (head + 1) cfg0 hnv, hjr, hrun]
  · intro k hk ck hck
    rw [hM] at hck ⊢
    rw [hE]
    rw [joinTwoHalts_run_eq _ 1 2 k cfg0
          (fun j hj => hnv j (Nat.le_trans hj (Nat.le_of_lt hk)))] at hck
    rw [hjr] at hck
    obtain ⟨hne1, hnh⟩ := htraj k hk ck hck
    refine ⟨hne1, ?_⟩
    rw [joinTwoHalts_halting_eq _ 1 2 ck (Compile.justRewind_not_state2 hnh), hjr]; exact hnh

/-! ### `navTestRewindM` — test a register's emptiness, head restored to `0`
(bottom-up, Risk C2)

The `navigateAndTestTM` family decides empty-vs-content but leaves the head
displaced on `sc`. The `eqBit` verdict (and the consume-loop testMachine) need a
clean 2-exit tester that *also rewinds the head back to `0`* on both outcomes, so
its outcomes can feed a wrapping `branchComposeFlatTM` whose branch bodies start
at head `0`. `navTestRewindM sc = branchComposeFlatTM (navigateAndTestTM sc)
opRewindToZero opRewindToZero …`: both branch bodies are the halt-unique
`opRewindToZero`, so the machine has exactly two halts (content / delim). -/

/-- Shared setup: the branch tape-symbol bound at head `H` (the cell is inside
`encodeTape s`), plus the `opRewindToZero` rewind from head `H` to `0`, where
`H` is the post-navigation head position `1 + |regBlocks (map shiftReg (take sc))|`. -/
private theorem Compile.navTestRewind_rewind_run (s : State) (sc : Var) (res : List Nat)
    (hsc : sc < s.length) (hbit : Compile.BitState s) :
    (∀ v, currentTapeSymbol (([] : List Nat),
          1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length,
          Compile.encodeTape s ++ res) = some v →
        v < max (ClearGadget.navigateAndTestTM sc).sig
              (max Compile.opRewindToZero.M.sig Compile.opRewindToZero.M.sig)) ∧
    runFlatTM (1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length + 1)
        Compile.opRewindToZero.M
        { state_idx := Compile.opRewindToZero.M.start,
          tapes := [([], 1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.opRewindToZero.exit,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } ∧
    (∀ k, k < 1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length + 1 → ∀ ck,
        runFlatTM k Compile.opRewindToZero.M
            { state_idx := Compile.opRewindToZero.M.start,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.opRewindToZero.exit ∧
        haltingStateReached Compile.opRewindToZero.M ck = false) := by
  set H := 1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length with hHdef
  set rest := Compile.encodeRegs s ++ [Compile.endMark] ++ res with hrestdef
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s sc hsc)
    rw [Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    show 1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length ≤ _
    rw [Compile.regBlocks_map_shiftReg]
    omega
  have htape_eq : Compile.encodeTape s ++ res = (3 : Nat) :: rest := by
    rw [hrestdef, Compile.encodeTape]
    show Compile.endMark :: (Compile.encodeRegs s ++ [Compile.endMark]) ++ res = _
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hcells : ∀ i, i < H → ∃ (h : i < rest.length),
      rest.get ⟨i, h⟩ < 4 ∧ rest.get ⟨i, h⟩ ≠ 3 := by
    intro i hi
    have hi_regs : i < (Compile.encodeRegs s).length := lt_of_lt_of_le hi hH_le_regs
    have hi_rest : i < rest.length := by
      rw [hrestdef, List.length_append, List.length_append]; omega
    have hget : rest.get ⟨i, hi_rest⟩ = (Compile.encodeRegs s).get ⟨i, hi_regs⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      have hget? : rest[i]? = (Compile.encodeRegs s)[i]? := by
        conv_lhs => rw [hrestdef]
        rw [List.getElem?_append_left (by rw [List.length_append]; omega),
            List.getElem?_append_left hi_regs]
      rw [List.getElem?_eq_getElem hi_rest, List.getElem?_eq_getElem hi_regs] at hget?
      exact Option.some.inj hget?
    refine ⟨hi_rest, ?_, ?_⟩
    · rw [hget]; exact Compile.encodeRegs_lt_four s hbit _ (List.get_mem _ _)
    · rw [hget]; exact Compile.encodeRegs_no_endMark s hbit _ (List.get_mem _ _)
  have hH_le_rest : H ≤ rest.length := by
    rw [hrestdef, List.length_append, List.length_append]; omega
  obtain ⟨hrz_run, hrz_traj⟩ := Compile.opRewindToZero_run [] rest H hH_le_rest hcells
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have hmax : max (ClearGadget.navigateAndTestTM sc).sig
        (max Compile.opRewindToZero.M.sig Compile.opRewindToZero.M.sig) = 4 := by
      rw [ClearGadget.navigateAndTestTM_sig, Compile.opRewindToZero.M_sig]; rfl
    rw [hmax]
    have hHlt2 : H < (Compile.encodeTape s).length := by
      have h2 := Compile.encodeRegs_length s
      rw [Compile.encodeTape_length]
      omega
    have hHlt : H < (Compile.encodeTape s ++ res).length := by
      rw [List.length_append]; omega
    rw [currentTapeSymbol_in_range hHlt] at hv
    have hmem : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ ∈ Compile.encodeTape s := by
      rw [List.get_eq_getElem, List.getElem_append_left hHlt2]; exact List.getElem_mem hHlt2
    have hv4 : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ < 4 :=
      Compile.encodeTape_lt_four s hbit _ hmem
    rw [← Option.some.inj hv]; exact hv4
  · rw [Compile.opRewindToZero_start, htape_eq]; exact hrz_run
  · intro k hk ck hck
    rw [Compile.opRewindToZero_start, htape_eq] at hck
    exact hrz_traj k hk ck hck

/-- **Step-bound helper (eqBit d2-iv).** The preceding-register-blocks prefix of
the encoded tape is at least 3 cells short of the full tape length. This is the
single arithmetic fact every `navTestRewindM`-based tester needs to bound its
navigate-then-rewind step count linearly in the tape length `L`: with
`ClearGadget.navSteps_le` (`navSteps ≤ 2·rb+1`), the navigate cost `navSteps+2`
and rewind cost `rb+2` both fall under `2·L` / `L`. -/
theorem Compile.regBlocks_take_len_le (s : State) (sc : Var) (hsc : sc < s.length)
    (res : List Nat) :
    (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length + 3
      ≤ (Compile.encodeTape s ++ res).length := by
  have hlen := congrArg List.length (Compile.encodeTape_split s sc hsc)
  rw [Compile.regBlocks_map_shiftReg] at hlen
  simp only [List.length_append, List.length_cons] at hlen
  have htape : (Compile.encodeTape s).length = (Compile.encodeRegs s).length + 2 := by
    rw [Compile.encodeTape_length, Compile.encodeRegs_length]
  rw [List.length_append, htape, Compile.regBlocks_map_shiftReg]
  omega

/-- **`navTestRewindM` run + trajectory — content branch (`sc` nonempty).** -/
theorem Compile.navTestRewindM_run_content (s : State) (sc : Var) (res : List Nat)
    (hbit : Compile.BitState s) (hsc : sc < s.length) (hne : State.get s sc ≠ [])
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.navTestRewindM sc)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.navTestRewindM_exit_content sc,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.navTestRewindM sc)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.navTestRewindM_exit_content sc ∧
        ck.state_idx ≠ Compile.navTestRewindM_exit_delim sc ∧
        haltingStateReached (Compile.navTestRewindM sc) ck = false)
    ∧ t ≤ 3 * (Compile.encodeTape s ++ res).length := by
  obtain ⟨hsym, hrz_run, hrz_traj⟩ := Compile.navTestRewind_rewind_run s sc res hsc hbit
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content sc
      ≠ ClearGadget.navigateAndTestTM_exit_delim sc := by
    show (ClearGadget.navigateToRegTM sc).states + 1 ≠ (ClearGadget.navigateToRegTM sc).states + 2
    omega
  have hcfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM sc).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hpos := branchComposeFlatTM_run_pos hexit_neq
    (ClearGadget.navigateAndTestTM_valid sc) Compile.opRewindToZero.M_valid
    Compile.opRewindToZero.M_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt sc) (ClearGadget.navigateAndTestTM_exit_delim_lt sc)
    cfg0 hcfg_lt [] (1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length)
    (Compile.encodeTape s ++ res) hsym
    (Compile.navTestReg_run_content s sc res hsc hbit hne)
    (Compile.navTestReg_traj_content s sc res hsc hbit hne)
    hrz_run
    (Compile.haltingStateReached_of_halt Compile.opRewindToZero.exit_is_halt)
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.navigateAndTestTM_valid sc) Compile.opRewindToZero.M_valid
    Compile.opRewindToZero.M_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt sc) (ClearGadget.navigateAndTestTM_exit_delim_lt sc)
    cfg0 hcfg_lt [] (1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length)
    (Compile.encodeTape s ++ res) hsym
    (Compile.navTestReg_run_content s sc res hsc hbit hne)
    (Compile.navTestReg_traj_content s sc res hsc hbit hne)
    (fun k hk ck hck => (hrz_traj k hk ck hck).2)
  have hstate : Compile.opRewindToZero.exit + (ClearGadget.navigateAndTestTM sc).states
      = Compile.navTestRewindM_exit_content sc := by
    rw [Compile.navTestRewindM_exit_content]; omega
  refine ⟨_, ?_, (fun k hk ck hck =>
    ⟨ClearGadget.ne_of_not_halting (Compile.navTestRewindM_exit_content_is_halt sc) (hpos_traj k hk ck hck),
     ClearGadget.ne_of_not_halting (Compile.navTestRewindM_exit_delim_is_halt sc) (hpos_traj k hk ck hck),
     hpos_traj k hk ck hck⟩), ?_⟩
  · simpa only [hstate] using hpos.1
  · have hns := ClearGadget.navSteps_le ((s.take sc).map Compile.shiftReg)
    have hrb := Compile.regBlocks_take_len_le s sc hsc res
    omega

/-- **`navTestRewindM` run + trajectory — delim branch (`sc` empty).** -/
theorem Compile.navTestRewindM_run_delim (s : State) (sc : Var) (res : List Nat)
    (hbit : Compile.BitState s) (hsc : sc < s.length) (hempty : State.get s sc = [])
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.navTestRewindM sc)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.navTestRewindM_exit_delim sc,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.navTestRewindM sc)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.navTestRewindM_exit_content sc ∧
        ck.state_idx ≠ Compile.navTestRewindM_exit_delim sc ∧
        haltingStateReached (Compile.navTestRewindM sc) ck = false)
    ∧ t ≤ 3 * (Compile.encodeTape s ++ res).length := by
  obtain ⟨hsym, hrz_run, hrz_traj⟩ := Compile.navTestRewind_rewind_run s sc res hsc hbit
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content sc
      ≠ ClearGadget.navigateAndTestTM_exit_delim sc := by
    show (ClearGadget.navigateToRegTM sc).states + 1 ≠ (ClearGadget.navigateToRegTM sc).states + 2
    omega
  have hcfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM sc).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hneg := branchComposeFlatTM_run_neg hexit_neq
    (ClearGadget.navigateAndTestTM_valid sc) Compile.opRewindToZero.M_valid
    Compile.opRewindToZero.M_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt sc) (ClearGadget.navigateAndTestTM_exit_delim_lt sc)
    cfg0 hcfg_lt [] (1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length)
    (Compile.encodeTape s ++ res) hsym
    (Compile.navTestReg_run_delim s sc res hsc hbit hempty)
    (Compile.navTestReg_traj_delim s sc res hsc hbit hempty)
    hrz_run
    (Compile.haltingStateReached_of_halt Compile.opRewindToZero.exit_is_halt)
  have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
    (ClearGadget.navigateAndTestTM_valid sc) Compile.opRewindToZero.M_valid
    Compile.opRewindToZero.M_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt sc) (ClearGadget.navigateAndTestTM_exit_delim_lt sc)
    cfg0 hcfg_lt [] (1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length)
    (Compile.encodeTape s ++ res) hsym
    (Compile.navTestReg_run_delim s sc res hsc hbit hempty)
    (Compile.navTestReg_traj_delim s sc res hsc hbit hempty)
    (fun k hk ck hck => (hrz_traj k hk ck hck).2)
  have hstate : Compile.opRewindToZero.exit
        + ((ClearGadget.navigateAndTestTM sc).states + Compile.opRewindToZero.M.states)
      = Compile.navTestRewindM_exit_delim sc := by
    rw [Compile.navTestRewindM_exit_delim]; omega
  refine ⟨_, ?_, (fun k hk ck hck =>
    ⟨ClearGadget.ne_of_not_halting (Compile.navTestRewindM_exit_content_is_halt sc) (hneg_traj k hk ck hck),
     ClearGadget.ne_of_not_halting (Compile.navTestRewindM_exit_delim_is_halt sc) (hneg_traj k hk ck hck),
     hneg_traj k hk ck hck⟩), ?_⟩
  · simpa only [hstate] using hneg.1
  · have hns := ClearGadget.navSteps_le ((s.take sc).map Compile.shiftReg)
    have hrb := Compile.regBlocks_take_len_le s sc hsc res
    omega

/-! ### `readBitRewindM` — read a register's first bit, head restored to `0`
(bottom-up, Risk C2 — d2a)

For the `eqBit` consume-loop `testMachine`, after the emptiness guards
(`navTestRewindM`) establish both scratch registers nonempty, we must read and
compare their first *bits*. `readBitRewindM sc` is the clean 2-exit primitive:
from head `0` with `sc` nonempty, navigate to `sc`'s first cell, read its bit, and
rewind the head back to `0`, exiting in `BIT0`/`BIT1` with the tape unchanged. The
spurious delim exit (`sc` empty — never taken once guarded) is merged into `BIT0`.

  `readRewindInnerM := branchComposeFlatTM bitReadTM opRewindToZero opRewindToZero b0 b1`
  `readBitRewindRawM sc := branchComposeFlatTM (navigateAndTestTM sc)
       opRewindToZero readRewindInnerM (delim sc) (content sc)`   -- M₃ = the 2-exit reader
  `readBitRewindM sc := joinTwoHalts (readBitRewindRawM sc) raw_b0 raw_dead`

Reuses the proven `bitReadTM` (bit-value tester) + `opRewindToZero` (rewind leaf) +
`navTestReg_run_content`/`_traj_content` (navigation) + `navTestRewind_rewind_run`
(the rewind from the post-navigation head). The `head`/`moveContent` proofs are the
template. The bit-reader is the **M₃** (negative/content) branch so the halt
characterization reuses `branchComposeFlatTM_halt_only_M3two`. -/

/-- **Inner read+rewind run.** From the post-navigation head `H` on `sc`'s first
content cell (value `b+1`), read the bit and rewind to head `0`, landing at
`readRewindInner_exit b`, the tape unchanged. -/
theorem Compile.readRewindInner_run (s : State) (sc : Var) (res : List Nat)
    (b : Nat) (cs : List Nat) (hcons : s.get sc = b :: cs) (hb : b ≤ 1)
    (hsc : sc < s.length) (hbit : Compile.BitState s) :
    ∃ t,
      runFlatTM t Compile.readRewindInnerM
          { state_idx := Compile.readRewindInnerM.start,
            tapes := [([], 1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.readRewindInner_exit b,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k Compile.readRewindInnerM
            { state_idx := Compile.readRewindInnerM.start,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached Compile.readRewindInnerM ck = false)
    ∧ t ≤ (Compile.encodeTape s ++ res).length + 3 := by
  set skipped := (s.take sc).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  have hrb : (AppendGadget.regBlocks skipped).length + 3 ≤ (Compile.encodeTape s ++ res).length := by
    have h := Compile.regBlocks_take_len_le s sc hsc res
    rw [← hskdef] at h; exact h
  -- content decomposition (`sc` nonempty) ⇒ cell at `H` is `b+1`.
  set tail' := Compile.shiftReg cs ++ 0 :: (Compile.encodeRegs (s.drop (sc + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s sc hsc
    rw [← hskdef] at hsplit
    have hsr : Compile.shiftReg (s.get sc) = (b + 1) :: Compile.shiftReg cs := by
      rw [hcons]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hHlt : H < (Compile.encodeTape s ++ res).length := by
    rw [hdecomp, hHdef]; simp only [List.length_cons, List.length_append]; omega
  have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = b + 1 := by
    have h? : (Compile.encodeTape s ++ res)[H]? = some (b + 1) := by
      rw [hdecomp, hHdef,
          show ((3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail'))
            = ((3 : Nat) :: AppendGadget.regBlocks skipped) ++ ((b + 1) :: tail') from by simp,
          List.getElem?_append_right (by simp only [List.length_cons]; omega),
          show 1 + (AppendGadget.regBlocks skipped).length
            - ((3 : Nat) :: AppendGadget.regBlocks skipped).length = 0 from by
              simp only [List.length_cons]; omega]
      rfl
    rw [List.getElem?_eq_getElem hHlt] at h?
    rw [List.get_eq_getElem]; exact Option.some.inj h?
  -- the rewind from head `H` (reuse the shared `navTestRewind` rewind run).
  obtain ⟨_, hrz_run, hrz_traj⟩ := Compile.navTestRewind_rewind_run s sc res hsc hbit
  rw [← hskdef, ← hHdef] at hrz_run hrz_traj
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    with hcfg0def
  have h_cfg_lt : (0 : Nat) < Compile.bitReadTM.states := by rw [Compile.bitReadTM_states]; omega
  have hexit_neq : Compile.bitReadTM_exit_b0 ≠ Compile.bitReadTM_exit_b1 := by decide
  have hep_lt : Compile.bitReadTM_exit_b0 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide
  have hen_lt : Compile.bitReadTM_exit_b1 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
      v < max Compile.bitReadTM.sig
        (max Compile.opRewindToZero.M.sig Compile.opRewindToZero.M.sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    rw [Compile.bitReadTM_sig, Compile.opRewindToZero.M_sig]
    have : v = b + 1 := (Option.some.inj hv).symm
    omega
  have htest_run := Compile.bitReadTM_run b hb [] (Compile.encodeTape s ++ res) H hHlt hcellH
  have htest_traj : ∀ k, k < 1 → ∀ ck, runFlatTM k Compile.bitReadTM cfg0 = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧ ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧
      haltingStateReached Compile.bitReadTM ck = false :=
    fun k hk ck hck => Compile.bitReadTM_no_early_halt [] (Compile.encodeTape s ++ res) H k hk ck hck
  have hstart : Compile.readRewindInnerM.start = 0 := Compile.readRewindInnerM_start
  interval_cases b
  · -- bit 0: positive branch.
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      Compile.bitReadTM_valid Compile.opRewindToZero.M_valid Compile.opRewindToZero.M_valid
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hsym
      htest_run htest_traj hrz_run
      (Compile.haltingStateReached_of_halt Compile.opRewindToZero.exit_is_halt)
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.bitReadTM_valid Compile.opRewindToZero.M_valid Compile.opRewindToZero.M_valid
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hsym
      htest_run htest_traj (fun k hk ck hck => (hrz_traj k hk ck hck).2)
    refine ⟨1 + 1 + (H + 1), ?_, ?_, by omega⟩
    · rw [hstart, Compile.readRewindInnerM]
      rw [show Compile.readRewindInner_exit 0
          = Compile.opRewindToZero.exit + Compile.bitReadTM.states from by
            rw [Compile.readRewindInner_exit]; omega]
      exact hpos.1
    · intro k hk ck hck
      rw [hstart] at hck; rw [Compile.readRewindInnerM] at hck ⊢
      exact hpos_traj k hk ck hck
  · -- bit 1: negative branch.
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      Compile.bitReadTM_valid Compile.opRewindToZero.M_valid Compile.opRewindToZero.M_valid
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hsym
      htest_run htest_traj hrz_run
      (Compile.haltingStateReached_of_halt Compile.opRewindToZero.exit_is_halt)
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      Compile.bitReadTM_valid Compile.opRewindToZero.M_valid Compile.opRewindToZero.M_valid
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hsym
      htest_run htest_traj (fun k hk ck hck => (hrz_traj k hk ck hck).2)
    refine ⟨1 + 1 + (H + 1), ?_, ?_, by omega⟩
    · rw [hstart, Compile.readRewindInnerM]
      rw [show Compile.readRewindInner_exit 1
          = Compile.opRewindToZero.exit + Compile.bitReadTM.states + Compile.opRewindToZero.M.states
            from by rw [Compile.readRewindInner_exit]; omega]
      exact hneg.1
    · intro k hk ck hck
      rw [hstart] at hck; rw [Compile.readRewindInnerM] at hck ⊢
      exact hneg_traj k hk ck hck

/-- **`readBitRewindM` run + trajectory.** From head `0` with `sc` nonempty whose
first bit is `b`, navigate, read, and rewind, landing at `readBitRewindM_exit_b{b}
= readBitRewindRawM_bit sc b`, the tape unchanged; the dead empty-branch halt is
never visited. -/
theorem Compile.readBitRewindM_run (s : State) (sc : Var) (res : List Nat)
    (b : Nat) (cs : List Nat) (hcons : s.get sc = b :: cs) (hb : b ≤ 1)
    (hsc : sc < s.length) (hbit : Compile.BitState s) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.readBitRewindM sc)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.readBitRewindRawM_bit sc b,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.readBitRewindM sc)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.readBitRewindM_exit_b0 sc ∧
        ck.state_idx ≠ Compile.readBitRewindM_exit_b1 sc ∧
        haltingStateReached (Compile.readBitRewindM sc) ck = false)
    ∧ t ≤ 3 * (Compile.encodeTape s ++ res).length + 4 := by
  have hne : s.get sc ≠ [] := by rw [hcons]; exact List.cons_ne_nil _ _
  -- navigation to `sc`'s content (head `H`).
  have hnav_run := Compile.navTestReg_run_content s sc res hsc hbit hne
  have hnav_traj0 := Compile.navTestReg_traj_content s sc res hsc hbit hne
  -- `run_neg` has `exit_pos = delim`, `exit_neg = content`; swap the trajectory conjuncts.
  have hnav_traj : ∀ k, k < ClearGadget.navSteps ((s.take sc).map Compile.shiftReg) + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM sc)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim sc ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content sc ∧
      haltingStateReached (ClearGadget.navigateAndTestTM sc) ck = false :=
    fun k hk ck hck => ⟨(hnav_traj0 k hk ck hck).2.1, (hnav_traj0 k hk ck hck).1,
      (hnav_traj0 k hk ck hck).2.2⟩
  obtain ⟨t₃, hM3run, hM3traj, ht3le⟩ := Compile.readRewindInner_run s sc res b cs hcons hb hsc hbit
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0def
  set H := 1 + (AppendGadget.regBlocks ((s.take sc).map Compile.shiftReg)).length with hHdef
  -- symbol bound at `H`.
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
      v < max (ClearGadget.navigateAndTestTM sc).sig
        (max Compile.opRewindToZero.M.sig Compile.readRewindInnerM.sig) := by
    obtain ⟨hsym0, _, _⟩ := Compile.navTestRewind_rewind_run s sc res hsc hbit
    intro v hv
    have := hsym0 v hv
    rw [ClearGadget.navigateAndTestTM_sig, Compile.opRewindToZero.M_sig] at this
    rw [ClearGadget.navigateAndTestTM_sig, Compile.opRewindToZero.M_sig, Compile.readRewindInnerM_sig]
    simpa using this
  have hcfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM sc).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hM3run' : runFlatTM t₃ Compile.readRewindInnerM
      { state_idx := Compile.readRewindInnerM.start,
        tapes := [([], H, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.readRewindInner_exit b,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := hM3run
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_delim sc
      ≠ ClearGadget.navigateAndTestTM_exit_content sc := by
    show (ClearGadget.navigateToRegTM sc).states + 2 ≠ (ClearGadget.navigateToRegTM sc).states + 1
    omega
  have hhalt3 : Compile.readRewindInnerM.halt[Compile.readRewindInner_exit b]? = some true := by
    rcases (show b = 0 ∨ b = 1 from by omega) with h | h <;> subst h
    · exact Compile.readRewindInner_exit_b0_is_halt
    · exact Compile.readRewindInner_exit_b1_is_halt
  have hneg := branchComposeFlatTM_run_neg hexit_neq
    (ClearGadget.navigateAndTestTM_valid sc) Compile.opRewindToZero.M_valid
    Compile.readRewindInnerM_valid
    (ClearGadget.navigateAndTestTM_exit_delim_lt sc) (ClearGadget.navigateAndTestTM_exit_content_lt sc)
    cfg0 hcfg_lt [] H (Compile.encodeTape s ++ res) hsym
    hnav_run hnav_traj hM3run'
    (Compile.haltingStateReached_of_halt hhalt3)
  have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
    (ClearGadget.navigateAndTestTM_valid sc) Compile.opRewindToZero.M_valid
    Compile.readRewindInnerM_valid
    (ClearGadget.navigateAndTestTM_exit_delim_lt sc) (ClearGadget.navigateAndTestTM_exit_content_lt sc)
    cfg0 hcfg_lt [] H (Compile.encodeTape s ++ res) hsym
    hnav_run hnav_traj (fun k hk ck hck => hM3traj k hk ck hck)
  -- the raw run reaches `raw_b{b}`.
  have hraw_run : runFlatTM
      (ClearGadget.navSteps ((s.take sc).map Compile.shiftReg) + 1 + 1 + 1 + t₃)
      (Compile.readBitRewindRawM sc) cfg0
      = some { state_idx := Compile.readBitRewindRawM_bit sc b,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    have h := hneg.1
    have hstate : Compile.readRewindInner_exit b
          + ((ClearGadget.navigateAndTestTM sc).states + Compile.opRewindToZero.M.states)
        = Compile.readBitRewindRawM_bit sc b := by
      rw [Compile.readBitRewindRawM_bit]; omega
    rw [hstate] at h; exact h
  set tNav := ClearGadget.navSteps ((s.take sc).map Compile.shiftReg) + 1 + 1 with htNav
  have hnv : ∀ k, k ≤ tNav + 1 + t₃ → ∀ ck,
      runFlatTM k (Compile.readBitRewindRawM sc) cfg0 = some ck →
      ck.state_idx ≠ Compile.readBitRewindRawM_dead sc := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · exact ClearGadget.ne_of_not_halting (Compile.readBitRewindRawM_dead_is_halt sc)
        (hneg_traj k hlt ck hck)
    · rw [hraw_run] at hck; rw [← Option.some.inj hck]
      have hbne := Compile.readBitRewindRawM_dead_ne_b0 sc
      rw [Compile.readBitRewindRawM_bit, Compile.readBitRewindRawM_dead, Compile.readRewindInner_exit] at *
      have := Compile.opRewindToZero.exit_lt
      rcases (show b = 0 ∨ b = 1 from by omega) with h | h <;> subst h <;> simp_all <;> omega
  refine ⟨tNav + 1 + t₃, ?_, ?_, ?_⟩
  · rw [Compile.readBitRewindM, joinTwoHalts_run_eq _ _ _ (tNav + 1 + t₃) cfg0 hnv]
    exact hraw_run
  · intro k hk ck hck
    have hnv_k : ∀ j, j ≤ k → ∀ cj,
        runFlatTM j (Compile.readBitRewindRawM sc) cfg0 = some cj →
        cj.state_idx ≠ Compile.readBitRewindRawM_dead sc :=
      fun j hj cj hcj => hnv j (le_trans hj (Nat.le_of_lt hk)) cj hcj
    rw [Compile.readBitRewindM, joinTwoHalts_run_eq _ _ _ k cfg0 hnv_k] at hck
    have hnh := hneg_traj k (by omega) ck hck
    refine ⟨?_, ?_, ?_⟩
    · rw [Compile.readBitRewindM_exit_b0]
      exact ClearGadget.ne_of_not_halting (Compile.readBitRewindRawM_b0_is_halt sc) hnh
    · rw [Compile.readBitRewindM_exit_b1]
      exact ClearGadget.ne_of_not_halting (Compile.readBitRewindRawM_b1_is_halt sc) hnh
    · rw [Compile.readBitRewindM, joinTwoHalts_halting_eq _ _ _ ck
        (ClearGadget.ne_of_not_halting (Compile.readBitRewindRawM_dead_is_halt sc) hnh)]
      exact hnh
  · have hns := ClearGadget.navSteps_le ((s.take sc).map Compile.shiftReg)
    have hrb := Compile.regBlocks_take_len_le s sc hsc res
    omega

/-! ### `eqVerdictM` — the `eqBit` verdict: "are BOTH `sc1` and `sc2` empty?"
(bottom-up, Risk C2 — d2b)

After the consume loop has peeled matching head-pairs off scratch copies `sc1`/
`sc2`, the operands were equal **iff both scratch registers are now empty**
(`probes/EqBitProbe.lean#eqVerdict_correct`). `eqVerdictM` is the clean 2-exit
tester deciding that, head restored to `0` on both outcomes:

  `eqVerdictRawM sc1 sc2 := branchComposeFlatTM (navTestRewindM sc1) idTM
                              (navTestRewindM sc2) (content sc1) (delim sc1)`

`sc1` nonempty → `idTM` (immediate, head already `0`) = **NEQ**; `sc1` empty →
`navTestRewindM sc2` (content = NEQ, delim = EQ). Three halts {NEQ_a, NEQ_b, EQ}.
`eqVerdictM` merges the two NEQ halts with one `joinTwoHalts`, leaving the clean
2-exit `{NEQ, EQ}`. Reuse for the `eqBit` (d1) wrapper. -/

/-- Symbol bound at the leading sentinel (head `0`): the cell `< 4`. -/
private theorem Compile.eqVerdict_sym4 (s : State) (res : List Nat) (hbit : Compile.BitState s) :
    ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v → v < 4 := by
  intro v hv
  have h0lt : 0 < (Compile.encodeTape s ++ res).length := by
    rw [List.length_append]; have := Compile.encodeTape_length s; omega
  rw [currentTapeSymbol_in_range h0lt] at hv
  have h0lt' : 0 < (Compile.encodeTape s).length := by
    have := Compile.encodeTape_length s; omega
  have hmem : (Compile.encodeTape s ++ res).get ⟨0, h0lt⟩ ∈ Compile.encodeTape s := by
    rw [List.get_eq_getElem, List.getElem_append_left h0lt']; exact List.getElem_mem h0lt'
  rw [← Option.some.inj hv]; exact Compile.encodeTape_lt_four s hbit _ hmem

/-- The branch symbol bound (`v < max sigs`) at head `0`. -/
private theorem Compile.eqVerdict_symMax (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) :
    ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (Compile.navTestRewindM sc1).sig
            (max Compile.idTM.sig (Compile.navTestRewindM sc2).sig) := by
  intro v hv
  have hmax : max (Compile.navTestRewindM sc1).sig
      (max Compile.idTM.sig (Compile.navTestRewindM sc2).sig) = 4 := by
    rw [Compile.navTestRewindM_sig, Compile.navTestRewindM_sig]; decide
  rw [hmax]; exact Compile.eqVerdict_sym4 s res hbit v hv

/-- **`eqVerdictM` run — NEQ via the left operand (`sc1` nonempty).** -/
theorem Compile.eqVerdictM_run_neq_left (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) (hsc1 : sc1 < s.length) (hne1 : State.get s sc1 ≠ [])
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.eqVerdictM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.eqVerdictM_exit_neq sc1,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.eqVerdictM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.eqVerdictM_exit_neq sc1 ∧
        ck.state_idx ≠ Compile.eqVerdictM_exit_eq sc1 sc2 ∧
        haltingStateReached (Compile.eqVerdictM sc1 sc2) ck = false)
    ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 2 := by
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ := Compile.navTestRewindM_run_content s sc1 res hbit hsc1 hne1 hres
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hsymMax := Compile.eqVerdict_symMax s sc1 sc2 res hbit
  have hcfg_lt : (0 : Nat) < (Compile.navTestRewindM sc1).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.navTestRewindM_exit_content_lt sc1)
  have hpos := branchComposeFlatTM_run_pos
    (Compile.navTestRewindM_exit_content_ne_delim sc1)
    (Compile.navTestRewindM_valid sc1) Compile.idTM_valid (Compile.navTestRewindM_valid sc2)
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj
    (show runFlatTM 0 Compile.idTM
        { state_idx := (0 : Nat), tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := (0 : Nat), tapes := [([], 0, Compile.encodeTape s ++ res)] } from rfl)
    (Compile.haltingStateReached_of_halt (show Compile.idTM.halt[(0 : Nat)]? = some true from rfl))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (Compile.navTestRewindM_valid sc1) Compile.idTM_valid (Compile.navTestRewindM_valid sc2)
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj (fun k hk _ _ => absurd hk (Nat.not_lt_zero k))
  have hraw_run : runFlatTM (t₁ + 1) (Compile.eqVerdictRawM sc1 sc2) cfg0
      = some { state_idx := Compile.eqVerdictRawM_neqA sc1,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    have h := hpos.1
    rw [Nat.add_zero, Nat.zero_add] at h
    rw [Compile.eqVerdictRawM_neqA]; exact h
  have hnv : ∀ k, k ≤ t₁ + 1 → ∀ ck,
      runFlatTM k (Compile.eqVerdictRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.eqVerdictRawM_neqB sc1 sc2 := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · exact ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_neqB_is_halt sc1 sc2)
        (hpos_traj k (by omega) ck hck)
    · rw [hraw_run] at hck; rw [← Option.some.inj hck]
      exact Compile.eqVerdictRawM_neqA_ne_neqB sc1 sc2
  refine ⟨t₁ + 1, ?_, ?_, by omega⟩
  · rw [Compile.eqVerdictM, joinTwoHalts_run_eq _ _ _ (t₁ + 1) cfg0 hnv,
        Compile.eqVerdictM_exit_neq]
    exact hraw_run
  · intro k hk ck hck
    have hnv_k : ∀ j, j ≤ k → ∀ cj,
        runFlatTM j (Compile.eqVerdictRawM sc1 sc2) cfg0 = some cj →
        cj.state_idx ≠ Compile.eqVerdictRawM_neqB sc1 sc2 :=
      fun j hj cj hcj => hnv j (le_trans hj (Nat.le_of_lt hk)) cj hcj
    rw [Compile.eqVerdictM, joinTwoHalts_run_eq _ _ _ k cfg0 hnv_k] at hck
    have hnh := hpos_traj k (by omega) ck hck
    refine ⟨ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_neqA_is_halt sc1 sc2) hnh,
      ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_eq_is_halt sc1 sc2) hnh, ?_⟩
    rw [Compile.eqVerdictM, joinTwoHalts_halting_eq _ _ _ ck
      (ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_neqB_is_halt sc1 sc2) hnh)]
    exact hnh

/-- **`eqVerdictM` run — EQ (both `sc1` and `sc2` empty).** -/
theorem Compile.eqVerdictM_run_eq (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hempty1 : State.get s sc1 = []) (hempty2 : State.get s sc2 = [])
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.eqVerdictM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.eqVerdictM_exit_eq sc1 sc2,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.eqVerdictM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.eqVerdictM_exit_neq sc1 ∧
        ck.state_idx ≠ Compile.eqVerdictM_exit_eq sc1 sc2 ∧
        haltingStateReached (Compile.eqVerdictM sc1 sc2) ck = false)
    ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 2 := by
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ := Compile.navTestRewindM_run_delim s sc1 res hbit hsc1 hempty1 hres
  obtain ⟨t₃, hM3run, hM3traj, ht3le⟩ := Compile.navTestRewindM_run_delim s sc2 res hbit hsc2 hempty2 hres
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hsymMax := Compile.eqVerdict_symMax s sc1 sc2 res hbit
  have hcfg_lt : (0 : Nat) < (Compile.navTestRewindM sc1).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.navTestRewindM_exit_content_lt sc1)
  have hM3run' : runFlatTM t₃ (Compile.navTestRewindM sc2)
      { state_idx := (Compile.navTestRewindM sc2).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.navTestRewindM_exit_delim sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    rw [Compile.navTestRewindM_start]; exact hM3run
  have hM3traj' : ∀ k, k < t₃ → ∀ ck,
      runFlatTM k (Compile.navTestRewindM sc2)
          { state_idx := (Compile.navTestRewindM sc2).start,
            tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.navTestRewindM sc2) ck = false := by
    rw [Compile.navTestRewindM_start]
    exact fun k hk ck hck => (hM3traj k hk ck hck).2.2
  have hneg := branchComposeFlatTM_run_neg
    (Compile.navTestRewindM_exit_content_ne_delim sc1)
    (Compile.navTestRewindM_valid sc1) Compile.idTM_valid (Compile.navTestRewindM_valid sc2)
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM3run'
    (Compile.haltingStateReached_of_halt (Compile.navTestRewindM_exit_delim_is_halt sc2))
  have hneg_traj := branchComposeFlatTM_no_early_halt_neg
    (Compile.navTestRewindM_exit_content_ne_delim sc1)
    (Compile.navTestRewindM_valid sc1) Compile.idTM_valid (Compile.navTestRewindM_valid sc2)
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM3traj'
  have hraw_eq : runFlatTM (t₁ + 1 + t₃) (Compile.eqVerdictRawM sc1 sc2) cfg0
      = some { state_idx := Compile.eqVerdictRawM_eq sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    have h := hneg.1
    have hstate : Compile.navTestRewindM_exit_delim sc2
          + ((Compile.navTestRewindM sc1).states + Compile.idTM.states)
        = Compile.eqVerdictRawM_eq sc1 sc2 := by
      rw [Compile.eqVerdictRawM_eq]; omega
    rw [hstate] at h; exact h
  have hnv : ∀ k, k ≤ t₁ + 1 + t₃ → ∀ ck,
      runFlatTM k (Compile.eqVerdictRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.eqVerdictRawM_neqB sc1 sc2 := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · exact ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_neqB_is_halt sc1 sc2)
        (hneg_traj k hlt ck hck)
    · rw [hraw_eq] at hck; rw [← Option.some.inj hck]
      exact fun h => Compile.eqVerdictRawM_neqB_ne_eq sc1 sc2 h.symm
  refine ⟨t₁ + 1 + t₃, ?_, ?_, by omega⟩
  · rw [Compile.eqVerdictM, joinTwoHalts_run_eq _ _ _ (t₁ + 1 + t₃) cfg0 hnv,
        Compile.eqVerdictM_exit_eq]
    exact hraw_eq
  · intro k hk ck hck
    have hnv_k : ∀ j, j ≤ k → ∀ cj,
        runFlatTM j (Compile.eqVerdictRawM sc1 sc2) cfg0 = some cj →
        cj.state_idx ≠ Compile.eqVerdictRawM_neqB sc1 sc2 :=
      fun j hj cj hcj => hnv j (le_trans hj (Nat.le_of_lt hk)) cj hcj
    rw [Compile.eqVerdictM, joinTwoHalts_run_eq _ _ _ k cfg0 hnv_k] at hck
    have hnh := hneg_traj k (by omega) ck hck
    refine ⟨ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_neqA_is_halt sc1 sc2) hnh,
      ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_eq_is_halt sc1 sc2) hnh, ?_⟩
    rw [Compile.eqVerdictM, joinTwoHalts_halting_eq _ _ _ ck
      (ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_neqB_is_halt sc1 sc2) hnh)]
    exact hnh

/-- **`eqVerdictM` run — NEQ via the right operand (`sc1` empty, `sc2` nonempty).**
The raw machine reaches the demoted NEQ_b halt, then `joinTwoHalts` bridges it to
the kept NEQ exit in one extra step. -/
theorem Compile.eqVerdictM_run_neq_right (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hempty1 : State.get s sc1 = []) (hne2 : State.get s sc2 ≠ [])
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.eqVerdictM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.eqVerdictM_exit_neq sc1,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.eqVerdictM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.eqVerdictM_exit_neq sc1 ∧
        ck.state_idx ≠ Compile.eqVerdictM_exit_eq sc1 sc2 ∧
        haltingStateReached (Compile.eqVerdictM sc1 sc2) ck = false)
    ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 2 := by
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ := Compile.navTestRewindM_run_delim s sc1 res hbit hsc1 hempty1 hres
  obtain ⟨t₃, hM3run, hM3traj, ht3le⟩ := Compile.navTestRewindM_run_content s sc2 res hbit hsc2 hne2 hres
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hsymMax := Compile.eqVerdict_symMax s sc1 sc2 res hbit
  have hcfg_lt : (0 : Nat) < (Compile.navTestRewindM sc1).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.navTestRewindM_exit_content_lt sc1)
  have hM3run' : runFlatTM t₃ (Compile.navTestRewindM sc2)
      { state_idx := (Compile.navTestRewindM sc2).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.navTestRewindM_exit_content sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    rw [Compile.navTestRewindM_start]; exact hM3run
  have hM3traj' : ∀ k, k < t₃ → ∀ ck,
      runFlatTM k (Compile.navTestRewindM sc2)
          { state_idx := (Compile.navTestRewindM sc2).start,
            tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.navTestRewindM sc2) ck = false := by
    rw [Compile.navTestRewindM_start]
    exact fun k hk ck hck => (hM3traj k hk ck hck).2.2
  have hneg := branchComposeFlatTM_run_neg
    (Compile.navTestRewindM_exit_content_ne_delim sc1)
    (Compile.navTestRewindM_valid sc1) Compile.idTM_valid (Compile.navTestRewindM_valid sc2)
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM3run'
    (Compile.haltingStateReached_of_halt (Compile.navTestRewindM_exit_content_is_halt sc2))
  have hneg_traj := branchComposeFlatTM_no_early_halt_neg
    (Compile.navTestRewindM_exit_content_ne_delim sc1)
    (Compile.navTestRewindM_valid sc1) Compile.idTM_valid (Compile.navTestRewindM_valid sc2)
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM3traj'
  have hraw_neqB : runFlatTM (t₁ + 1 + t₃) (Compile.eqVerdictRawM sc1 sc2) cfg0
      = some { state_idx := Compile.eqVerdictRawM_neqB sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    have h := hneg.1
    have hstate : Compile.navTestRewindM_exit_content sc2
          + ((Compile.navTestRewindM sc1).states + Compile.idTM.states)
        = Compile.eqVerdictRawM_neqB sc1 sc2 := by
      rw [Compile.eqVerdictRawM_neqB]; omega
    rw [hstate] at h; exact h
  -- the raw run never visits neqB *strictly* before `t₁+1+t₃`.
  have hnv_strict : ∀ k, k < t₁ + 1 + t₃ → ∀ ck,
      runFlatTM k (Compile.eqVerdictRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.eqVerdictRawM_neqB sc1 sc2 :=
    fun k hk ck hck => ClearGadget.ne_of_not_halting
      (Compile.eqVerdictRawM_neqB_is_halt sc1 sc2) (hneg_traj k hk ck hck)
  have hweak : runFlatTM (t₁ + 1 + t₃) (Compile.eqVerdictM sc1 sc2) cfg0
      = some { state_idx := Compile.eqVerdictRawM_neqB sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    rw [Compile.eqVerdictM, joinTwoHalts_run_eq_weak _ _ _ (t₁ + 1 + t₃) cfg0 hnv_strict]
    exact hraw_neqB
  have hnh_neqB : haltingStateReached (Compile.eqVerdictM sc1 sc2)
      { state_idx := Compile.eqVerdictRawM_neqB sc1 sc2,
        tapes := [([], 0, Compile.encodeTape s ++ res)] } = false := by
    show ((Compile.eqVerdictRawM sc1 sc2).halt.set (Compile.eqVerdictRawM_neqB sc1 sc2) false).getD
      (Compile.eqVerdictRawM_neqB sc1 sc2) false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl]
    split <;> rfl
  have hsymRaw : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < (Compile.eqVerdictRawM sc1 sc2).sig := by
    intro v hv; rw [Compile.eqVerdictRawM_sig]; exact Compile.eqVerdict_sym4 s res hbit v hv
  have hstep : stepFlatTM (Compile.eqVerdictM sc1 sc2)
      { state_idx := Compile.eqVerdictRawM_neqB sc1 sc2,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.eqVerdictRawM_neqA sc1,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } :=
    joinTwoHalts_step_to_h1 (Compile.eqVerdictRawM sc1 sc2)
      (Compile.eqVerdictRawM_neqA sc1) (Compile.eqVerdictRawM_neqB sc1 sc2)
      [] (Compile.encodeTape s ++ res) 0 hsymRaw
  have hfull : runFlatTM (t₁ + 1 + t₃ + 1) (Compile.eqVerdictM sc1 sc2) cfg0
      = some { state_idx := Compile.eqVerdictRawM_neqA sc1,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } :=
    runFlatTM_extend_by_step (Compile.eqVerdictM sc1 sc2) (t₁ + 1 + t₃) cfg0 _ _
      hweak hnh_neqB hstep
  refine ⟨t₁ + 1 + t₃ + 1, ?_, ?_, by omega⟩
  · rw [Compile.eqVerdictM_exit_neq]; exact hfull
  · intro k hk ck hck
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
    · have hnv_k : ∀ j, j ≤ k → ∀ cj,
          runFlatTM j (Compile.eqVerdictRawM sc1 sc2) cfg0 = some cj →
          cj.state_idx ≠ Compile.eqVerdictRawM_neqB sc1 sc2 :=
        fun j hj cj hcj => hnv_strict j (by omega) cj hcj
      rw [Compile.eqVerdictM, joinTwoHalts_run_eq _ _ _ k cfg0 hnv_k] at hck
      have hnh := hneg_traj k (by omega) ck hck
      refine ⟨ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_neqA_is_halt sc1 sc2) hnh,
        ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_eq_is_halt sc1 sc2) hnh, ?_⟩
      rw [Compile.eqVerdictM, joinTwoHalts_halting_eq _ _ _ ck
        (ClearGadget.ne_of_not_halting (Compile.eqVerdictRawM_neqB_is_halt sc1 sc2) hnh)]
      exact hnh
    · rw [hweak] at hck
      have hck_eq : ck = { state_idx := Compile.eqVerdictRawM_neqB sc1 sc2,
                           tapes := [([], 0, Compile.encodeTape s ++ res)] } :=
        Option.some.inj hck.symm
      refine ⟨?_, ?_, ?_⟩
      · rw [hck_eq, Compile.eqVerdictM_exit_neq]
        exact fun h => Compile.eqVerdictRawM_neqA_ne_neqB sc1 sc2 h.symm
      · rw [hck_eq, Compile.eqVerdictM_exit_eq]
        exact Compile.eqVerdictRawM_neqB_ne_eq sc1 sc2
      · rw [hck_eq]; exact hnh_neqB

/-! ### `bitCompareM` — compare the first bits of two NONEMPTY registers
(bottom-up, Risk C2 — d2a)

In the `eqBit` consume-loop body, once the emptiness guards establish that both
scratch registers `sc1`/`sc2` are nonempty, we must read and compare their first
*bits*. `bitCompareM sc1 sc2` is the clean 2-exit tester deciding "are the first
bits equal?", head restored to `0` on both outcomes, tape unchanged:

  `bitCompareRawM sc1 sc2 :=
     branchComposeFlatTM (readBitRewindM sc1) (readBitRewindM sc2) (readBitRewindM sc2)
       (readBitRewindM_exit_b0 sc1) (readBitRewindM_exit_b1 sc1)`

`M₁ = readBitRewindM sc1` reads `sc1`'s bit `a` (`b0` → positive `M₂`, `b1` →
negative `M₃`); the **same** `readBitRewindM sc2` on both branches then reads
`sc2`'s bit `b`. The four raw halts are `m{a}{b}`; MATCH `= {m00, m11}`, NOMATCH
`= {m01, m10}`. `bitCompareM` merges them down to two with a **double**
`joinTwoHalts` (demote `m11 → m00` for MATCH, then `m10 → m01` for NOMATCH). -/

/-- **Transport — a raw exit `K` kept by BOTH joins** (`K ∈ {m00, m01}`).
The whole run agrees with the raw machine. -/
private theorem Compile.bitCompareM_transport_kept (sc1 sc2 : Var) (tp : List Nat) (T K : Nat)
    (hK_ne_m10 : K ≠ Compile.bitCompareRawM_m10 sc1 sc2)
    (hK_ne_m11 : K ≠ Compile.bitCompareRawM_m11 sc1 sc2)
    (hraw_run : runFlatTM T (Compile.bitCompareRawM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, tp)] }
      = some { state_idx := K, tapes := [([], 0, tp)] })
    (hraw_traj : ∀ k, k < T → ∀ ck, runFlatTM k (Compile.bitCompareRawM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, tp)] } = some ck →
        haltingStateReached (Compile.bitCompareRawM sc1 sc2) ck = false) :
    runFlatTM T (Compile.bitCompareM sc1 sc2) { state_idx := 0, tapes := [([], 0, tp)] }
      = some { state_idx := K, tapes := [([], 0, tp)] }
    ∧ (∀ k, k < T → ∀ ck, runFlatTM k (Compile.bitCompareM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, tp)] } = some ck →
        ck.state_idx ≠ Compile.bitCompareM_exit_match sc1 sc2 ∧
        ck.state_idx ≠ Compile.bitCompareM_exit_nomatch sc1 sc2 ∧
        haltingStateReached (Compile.bitCompareM sc1 sc2) ck = false) := by
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, tp)] } with hcfg0
  -- raw never visits `m11` within `[0,T]`.
  have hnv_m11 : ∀ k, k ≤ T → ∀ ck,
      runFlatTM k (Compile.bitCompareRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.bitCompareRawM_m11 sc1 sc2 := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m11_is_halt sc1 sc2)
        (hraw_traj k hlt ck hck)
    · rw [heq, hraw_run] at hck; rw [← Option.some.inj hck]; exact hK_ne_m11
  have hJ1 : ∀ t, t ≤ T →
      runFlatTM t (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
          (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)) cfg0
        = runFlatTM t (Compile.bitCompareRawM sc1 sc2) cfg0 :=
    fun t ht => joinTwoHalts_run_eq _ _ _ t cfg0
      (fun k hk ck hck => hnv_m11 k (le_trans hk ht) ck hck)
  -- the inner machine never visits `m10` within `[0,T]`.
  have hnv_m10 : ∀ k, k ≤ T → ∀ ck,
      runFlatTM k (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
          (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)) cfg0 = some ck →
      ck.state_idx ≠ Compile.bitCompareRawM_m10 sc1 sc2 := by
    intro k hk ck hck
    rw [hJ1 k hk] at hck
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m10_is_halt sc1 sc2)
        (hraw_traj k hlt ck hck)
    · rw [heq, hraw_run] at hck; rw [← Option.some.inj hck]; exact hK_ne_m10
  have hJ2 : ∀ t, t ≤ T →
      runFlatTM t (Compile.bitCompareM sc1 sc2) cfg0
        = runFlatTM t (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
            (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)) cfg0 := by
    intro t ht
    rw [Compile.bitCompareM]
    exact joinTwoHalts_run_eq _ _ _ t cfg0
      (fun k hk ck hck => hnv_m10 k (le_trans hk ht) ck hck)
  refine ⟨?_, ?_⟩
  · rw [hJ2 T (le_refl _), hJ1 T (le_refl _)]; exact hraw_run
  · intro k hk ck hck
    rw [hJ2 k (le_of_lt hk), hJ1 k (le_of_lt hk)] at hck
    have hnh := hraw_traj k hk ck hck
    refine ⟨?_, ?_, ?_⟩
    · rw [Compile.bitCompareM_exit_match]
      exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m00_is_halt sc1 sc2) hnh
    · rw [Compile.bitCompareM_exit_nomatch]
      exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m01_is_halt sc1 sc2) hnh
    · have hne10 := ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m10_is_halt sc1 sc2) hnh
      have hne11 := ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m11_is_halt sc1 sc2) hnh
      rw [Compile.bitCompareM, joinTwoHalts_halting_eq _ _ _ ck hne10,
          joinTwoHalts_halting_eq _ _ _ ck hne11]
      exact hnh

/-- **Transport — raw reaches `m11`** (demoted by the inner join → bridges to the
MATCH exit `m00` in one extra step). -/
private theorem Compile.bitCompareM_transport_m11 (sc1 sc2 : Var) (tp : List Nat) (T : Nat)
    (hsym4 : ∀ v, currentTapeSymbol (([] : List Nat), 0, tp) = some v → v < 4)
    (hraw_run : runFlatTM T (Compile.bitCompareRawM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, tp)] }
      = some { state_idx := Compile.bitCompareRawM_m11 sc1 sc2, tapes := [([], 0, tp)] })
    (hraw_traj : ∀ k, k < T → ∀ ck, runFlatTM k (Compile.bitCompareRawM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, tp)] } = some ck →
        haltingStateReached (Compile.bitCompareRawM sc1 sc2) ck = false) :
    runFlatTM (T + 1) (Compile.bitCompareM sc1 sc2) { state_idx := 0, tapes := [([], 0, tp)] }
      = some { state_idx := Compile.bitCompareM_exit_match sc1 sc2, tapes := [([], 0, tp)] }
    ∧ (∀ k, k < T + 1 → ∀ ck, runFlatTM k (Compile.bitCompareM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, tp)] } = some ck →
        ck.state_idx ≠ Compile.bitCompareM_exit_match sc1 sc2 ∧
        ck.state_idx ≠ Compile.bitCompareM_exit_nomatch sc1 sc2 ∧
        haltingStateReached (Compile.bitCompareM sc1 sc2) ck = false) := by
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, tp)] } with hcfg0
  obtain ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩ := Compile.bitCompareRawM_distinct sc1 sc2
  -- raw never `m11` strictly before `T`; inner run = raw run there.
  have hnv_m11_strict : ∀ k, k < T → ∀ ck,
      runFlatTM k (Compile.bitCompareRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.bitCompareRawM_m11 sc1 sc2 :=
    fun k hk ck hck => ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m11_is_halt sc1 sc2)
      (hraw_traj k hk ck hck)
  have hJ1_eq_raw : ∀ k, k < T →
      runFlatTM k (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
          (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)) cfg0
        = runFlatTM k (Compile.bitCompareRawM sc1 sc2) cfg0 :=
    fun k hk => joinTwoHalts_run_eq _ _ _ k cfg0
      (fun j hj cj hcj => hnv_m11_strict j (lt_of_le_of_lt hj hk) cj hcj)
  -- inner run reaches `m11` at `T` (weak preservation), then bridges to `m00`.
  have hJ1_T : runFlatTM T (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
        (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)) cfg0
      = some { state_idx := Compile.bitCompareRawM_m11 sc1 sc2, tapes := [([], 0, tp)] } := by
    rw [joinTwoHalts_run_eq_weak _ _ _ T cfg0 hnv_m11_strict]; exact hraw_run
  have hnh_J1_m11 : haltingStateReached (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
        (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2))
        { state_idx := Compile.bitCompareRawM_m11 sc1 sc2, tapes := [([], 0, tp)] } = false := by
    show ((Compile.bitCompareRawM sc1 sc2).halt.set (Compile.bitCompareRawM_m11 sc1 sc2) false).getD
      (Compile.bitCompareRawM_m11 sc1 sc2) false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl]; split <;> rfl
  have hstep_J1 : stepFlatTM (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
        (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2))
        { state_idx := Compile.bitCompareRawM_m11 sc1 sc2, tapes := [([], 0, tp)] }
      = some { state_idx := Compile.bitCompareRawM_m00 sc1 sc2, tapes := [([], 0, tp)] } :=
    joinTwoHalts_step_to_h1 (Compile.bitCompareRawM sc1 sc2)
      (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2) [] tp 0
      (fun v hv => by rw [Compile.bitCompareRawM_sig]; exact hsym4 v hv)
  have hJ1_T1 : runFlatTM (T + 1) (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
        (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)) cfg0
      = some { state_idx := Compile.bitCompareRawM_m00 sc1 sc2, tapes := [([], 0, tp)] } :=
    runFlatTM_extend_by_step _ T cfg0 _ _ hJ1_T hnh_J1_m11 hstep_J1
  -- the inner run never visits `m10` within `[0, T+1]`.
  have hnv_J1_m10 : ∀ k, k ≤ T + 1 → ∀ ck,
      runFlatTM k (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
          (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)) cfg0 = some ck →
      ck.state_idx ≠ Compile.bitCompareRawM_m10 sc1 sc2 := by
    intro k hk ck hck
    rcases (show k < T ∨ k = T ∨ k = T + 1 from by omega) with h | h | h
    · rw [hJ1_eq_raw k h] at hck
      exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m10_is_halt sc1 sc2)
        (hraw_traj k h ck hck)
    · rw [h, hJ1_T] at hck; rw [← Option.some.inj hck]; exact hd23.symm
    · rw [h, hJ1_T1] at hck; rw [← Option.some.inj hck]; exact hd02
  refine ⟨?_, ?_⟩
  · rw [Compile.bitCompareM, joinTwoHalts_run_eq _ _ _ (T + 1) cfg0 hnv_J1_m10,
        Compile.bitCompareM_exit_match]
    exact hJ1_T1
  · intro k hk ck hck
    rcases (show k < T ∨ k = T from by omega) with h | h
    · rw [Compile.bitCompareM,
          joinTwoHalts_run_eq _ _ _ k cfg0 (fun j hj cj hcj => hnv_J1_m10 j (by omega) cj hcj),
          hJ1_eq_raw k h] at hck
      have hnh := hraw_traj k h ck hck
      refine ⟨?_, ?_, ?_⟩
      · rw [Compile.bitCompareM_exit_match]
        exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m00_is_halt sc1 sc2) hnh
      · rw [Compile.bitCompareM_exit_nomatch]
        exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m01_is_halt sc1 sc2) hnh
      · have hne10 := ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m10_is_halt sc1 sc2) hnh
        have hne11 := ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m11_is_halt sc1 sc2) hnh
        rw [Compile.bitCompareM, joinTwoHalts_halting_eq _ _ _ ck hne10,
            joinTwoHalts_halting_eq _ _ _ ck hne11]
        exact hnh
    · rw [h, Compile.bitCompareM,
          joinTwoHalts_run_eq _ _ _ T cfg0 (fun j hj cj hcj => hnv_J1_m10 j (by omega) cj hcj),
          hJ1_T] at hck
      have hck_eq : ck = { state_idx := Compile.bitCompareRawM_m11 sc1 sc2, tapes := [([], 0, tp)] } :=
        (Option.some.inj hck).symm
      refine ⟨?_, ?_, ?_⟩
      · rw [hck_eq, Compile.bitCompareM_exit_match]; exact hd03.symm
      · rw [hck_eq, Compile.bitCompareM_exit_nomatch]; exact hd13.symm
      · rw [hck_eq, Compile.bitCompareM, joinTwoHalts_halting_eq _ _ _ _ hd23.symm]
        exact hnh_J1_m11

/-- **Transport — raw reaches `m10`** (kept by the inner join, demoted by the
outer join → bridges to the NOMATCH exit `m01` in one extra step). -/
private theorem Compile.bitCompareM_transport_m10 (sc1 sc2 : Var) (tp : List Nat) (T : Nat)
    (hsym4 : ∀ v, currentTapeSymbol (([] : List Nat), 0, tp) = some v → v < 4)
    (hraw_run : runFlatTM T (Compile.bitCompareRawM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, tp)] }
      = some { state_idx := Compile.bitCompareRawM_m10 sc1 sc2, tapes := [([], 0, tp)] })
    (hraw_traj : ∀ k, k < T → ∀ ck, runFlatTM k (Compile.bitCompareRawM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, tp)] } = some ck →
        haltingStateReached (Compile.bitCompareRawM sc1 sc2) ck = false) :
    runFlatTM (T + 1) (Compile.bitCompareM sc1 sc2) { state_idx := 0, tapes := [([], 0, tp)] }
      = some { state_idx := Compile.bitCompareM_exit_nomatch sc1 sc2, tapes := [([], 0, tp)] }
    ∧ (∀ k, k < T + 1 → ∀ ck, runFlatTM k (Compile.bitCompareM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, tp)] } = some ck →
        ck.state_idx ≠ Compile.bitCompareM_exit_match sc1 sc2 ∧
        ck.state_idx ≠ Compile.bitCompareM_exit_nomatch sc1 sc2 ∧
        haltingStateReached (Compile.bitCompareM sc1 sc2) ck = false) := by
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, tp)] } with hcfg0
  obtain ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩ := Compile.bitCompareRawM_distinct sc1 sc2
  -- raw never `m11` within `[0,T]` (`m10 ≠ m11` covers the endpoint); inner = raw.
  have hnv_m11 : ∀ k, k ≤ T → ∀ ck,
      runFlatTM k (Compile.bitCompareRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.bitCompareRawM_m11 sc1 sc2 := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m11_is_halt sc1 sc2)
        (hraw_traj k hlt ck hck)
    · rw [heq, hraw_run] at hck; rw [← Option.some.inj hck]; exact hd23
  have hJ1_eq_raw : ∀ k, k ≤ T →
      runFlatTM k (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
          (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)) cfg0
        = runFlatTM k (Compile.bitCompareRawM sc1 sc2) cfg0 :=
    fun k hk => joinTwoHalts_run_eq _ _ _ k cfg0
      (fun j hj cj hcj => hnv_m11 j (le_trans hj hk) cj hcj)
  have hJ1_T : runFlatTM T (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
        (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)) cfg0
      = some { state_idx := Compile.bitCompareRawM_m10 sc1 sc2, tapes := [([], 0, tp)] } := by
    rw [hJ1_eq_raw T (le_refl _)]; exact hraw_run
  -- inner never `m10` strictly before `T`.
  have hnv_J1_m10_strict : ∀ k, k < T → ∀ ck,
      runFlatTM k (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
          (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2)) cfg0 = some ck →
      ck.state_idx ≠ Compile.bitCompareRawM_m10 sc1 sc2 := by
    intro k hk ck hck
    rw [hJ1_eq_raw k (le_of_lt hk)] at hck
    exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m10_is_halt sc1 sc2)
      (hraw_traj k hk ck hck)
  -- outer run reaches `m10` at `T` (weak), then bridges to `m01`.
  have hJ2_T : runFlatTM T (Compile.bitCompareM sc1 sc2) cfg0
      = some { state_idx := Compile.bitCompareRawM_m10 sc1 sc2, tapes := [([], 0, tp)] } := by
    rw [Compile.bitCompareM, joinTwoHalts_run_eq_weak _ _ _ T cfg0 hnv_J1_m10_strict]
    exact hJ1_T
  have hnh_J2_m10 : haltingStateReached (Compile.bitCompareM sc1 sc2)
      { state_idx := Compile.bitCompareRawM_m10 sc1 sc2, tapes := [([], 0, tp)] } = false := by
    rw [Compile.bitCompareM]
    show ((joinTwoHalts (Compile.bitCompareRawM sc1 sc2) (Compile.bitCompareRawM_m00 sc1 sc2)
        (Compile.bitCompareRawM_m11 sc1 sc2)).halt.set (Compile.bitCompareRawM_m10 sc1 sc2) false).getD
      (Compile.bitCompareRawM_m10 sc1 sc2) false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl]; split <;> rfl
  have hstep_J2 : stepFlatTM (Compile.bitCompareM sc1 sc2)
      { state_idx := Compile.bitCompareRawM_m10 sc1 sc2, tapes := [([], 0, tp)] }
      = some { state_idx := Compile.bitCompareRawM_m01 sc1 sc2, tapes := [([], 0, tp)] } := by
    rw [Compile.bitCompareM]
    exact joinTwoHalts_step_to_h1 (joinTwoHalts (Compile.bitCompareRawM sc1 sc2)
      (Compile.bitCompareRawM_m00 sc1 sc2) (Compile.bitCompareRawM_m11 sc1 sc2))
      (Compile.bitCompareRawM_m01 sc1 sc2) (Compile.bitCompareRawM_m10 sc1 sc2) [] tp 0
      (fun v hv => by rw [joinTwoHalts_sig, Compile.bitCompareRawM_sig]; exact hsym4 v hv)
  refine ⟨?_, ?_⟩
  · rw [Compile.bitCompareM_exit_nomatch]
    exact runFlatTM_extend_by_step _ T cfg0 _ _ hJ2_T hnh_J2_m10 hstep_J2
  · intro k hk ck hck
    rcases (show k < T ∨ k = T from by omega) with h | h
    · rw [Compile.bitCompareM,
          joinTwoHalts_run_eq _ _ _ k cfg0
            (fun j hj cj hcj => hnv_J1_m10_strict j (by omega) cj hcj)] at hck
      rw [hJ1_eq_raw k (le_of_lt h)] at hck
      have hnh := hraw_traj k h ck hck
      refine ⟨?_, ?_, ?_⟩
      · rw [Compile.bitCompareM_exit_match]
        exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m00_is_halt sc1 sc2) hnh
      · rw [Compile.bitCompareM_exit_nomatch]
        exact ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m01_is_halt sc1 sc2) hnh
      · have hne10 := ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m10_is_halt sc1 sc2) hnh
        have hne11 := ClearGadget.ne_of_not_halting (Compile.bitCompareRawM_m11_is_halt sc1 sc2) hnh
        rw [Compile.bitCompareM, joinTwoHalts_halting_eq _ _ _ ck hne10,
            joinTwoHalts_halting_eq _ _ _ ck hne11]
        exact hnh
    · rw [h, hJ2_T] at hck
      have hck_eq : ck = { state_idx := Compile.bitCompareRawM_m10 sc1 sc2, tapes := [([], 0, tp)] } :=
        (Option.some.inj hck).symm
      refine ⟨?_, ?_, ?_⟩
      · rw [hck_eq, Compile.bitCompareM_exit_match]; exact hd02.symm
      · rw [hck_eq, Compile.bitCompareM_exit_nomatch]; exact fun heq => hd12 heq.symm
      · rw [hck_eq]; exact hnh_J2_m10

/-- The raw bit-comparison run: from head `0` with both `sc1`/`sc2` nonempty whose
first bits are `a`/`b`, `bitCompareRawM` reaches `m{a}{b}` (here written
`N1 + a·N2 + bit_b(sc2)`), tape unchanged, never halting before. -/
private theorem Compile.bitCompareRawM_run (s : State) (sc1 sc2 : Var) (res : List Nat)
    (a b : Nat) (cs1 cs2 : List Nat)
    (hc1 : State.get s sc1 = a :: cs1) (hc2 : State.get s sc2 = b :: cs2)
    (ha : a ≤ 1) (hb : b ≤ 1) (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.bitCompareRawM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := (Compile.readBitRewindM sc1).states
                   + a * (Compile.readBitRewindM sc2).states + Compile.readBitRewindRawM_bit sc2 b,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck, runFlatTM k (Compile.bitCompareRawM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.bitCompareRawM sc1 sc2) ck = false)
    ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 9 := by
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  -- the `M₂`/`M₃` phase: read `sc2`'s bit `b`.
  obtain ⟨t2, hM2run, hM2traj, ht2le⟩ := Compile.readBitRewindM_run s sc2 res b cs2 hc2 hb hsc2 hbit hres
  have hM2run' : runFlatTM t2 (Compile.readBitRewindM sc2)
      { state_idx := (Compile.readBitRewindM sc2).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.readBitRewindRawM_bit sc2 b,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    rw [Compile.readBitRewindM_start]; exact hM2run
  have hM2traj' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k (Compile.readBitRewindM sc2)
          { state_idx := (Compile.readBitRewindM sc2).start,
            tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.readBitRewindM sc2) ck = false := by
    rw [Compile.readBitRewindM_start]
    exact fun k hk ck hck => (hM2traj k hk ck hck).2.2
  have hhalt2 : haltingStateReached (Compile.readBitRewindM sc2)
      { state_idx := Compile.readBitRewindRawM_bit sc2 b,
        tapes := [([], 0, Compile.encodeTape s ++ res)] } = true := by
    have hh : (Compile.readBitRewindM sc2).halt[Compile.readBitRewindRawM_bit sc2 b]? = some true := by
      rcases (show b = 0 ∨ b = 1 from by omega) with h | h <;> subst h
      · exact Compile.readBitRewindM_exit_b0_is_halt sc2
      · exact Compile.readBitRewindM_exit_b1_is_halt sc2
    exact Compile.haltingStateReached_of_halt hh
  have hsymMax : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (Compile.readBitRewindM sc1).sig
            (max (Compile.readBitRewindM sc2).sig (Compile.readBitRewindM sc2).sig) := by
    intro v hv
    have hm : max (Compile.readBitRewindM sc1).sig
        (max (Compile.readBitRewindM sc2).sig (Compile.readBitRewindM sc2).sig) = 4 := by
      rw [Compile.readBitRewindM_sig, Compile.readBitRewindM_sig]; decide
    rw [hm]; exact Compile.eqVerdict_sym4 s res hbit v hv
  have hcfg_lt : (0 : Nat) < (Compile.readBitRewindM sc1).states := Compile.readBitRewindM_states_pos sc1
  -- the `M₁` phase: read `sc1`'s bit `a`.
  obtain ⟨t1, hM1run, hM1traj, ht1le⟩ := Compile.readBitRewindM_run s sc1 res a cs1 hc1 ha hsc1 hbit hres
  interval_cases a
  · -- `a = 0`: positive branch (`M₁` reaches `exit_b0 = exit_pos`).
    have hM1run' : runFlatTM t1 (Compile.readBitRewindM sc1) cfg0
        = some { state_idx := Compile.readBitRewindM_exit_b0 sc1,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
      rw [Compile.readBitRewindM_exit_b0]; exact hM1run
    have hpos := branchComposeFlatTM_run_pos (Compile.readBitRewindM_exit_b0_ne_b1 sc1)
      (Compile.readBitRewindM_valid sc1) (Compile.readBitRewindM_valid sc2)
      (Compile.readBitRewindM_valid sc2)
      (Compile.readBitRewindM_exit_b0_lt sc1) (Compile.readBitRewindM_exit_b1_lt sc1)
      cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax hM1run' hM1traj hM2run' hhalt2
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      (Compile.readBitRewindM_valid sc1) (Compile.readBitRewindM_valid sc2)
      (Compile.readBitRewindM_valid sc2)
      (Compile.readBitRewindM_exit_b0_lt sc1) (Compile.readBitRewindM_exit_b1_lt sc1)
      cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax hM1run' hM1traj hM2traj'
    refine ⟨t1 + 1 + t2, ?_, ?_, by omega⟩
    · have h := hpos.1
      rw [show Compile.readBitRewindRawM_bit sc2 b + (Compile.readBitRewindM sc1).states
            = (Compile.readBitRewindM sc1).states + 0 * (Compile.readBitRewindM sc2).states
              + Compile.readBitRewindRawM_bit sc2 b from by omega] at h
      rw [Compile.bitCompareRawM, Compile.readBitRewindM_exit_b0, Compile.readBitRewindM_exit_b1]
      exact h
    · intro k hk ck hck
      rw [Compile.bitCompareRawM, Compile.readBitRewindM_exit_b0, Compile.readBitRewindM_exit_b1] at hck ⊢
      exact hpos_traj k hk ck hck
  · -- `a = 1`: negative branch (`M₁` reaches `exit_b1 = exit_neg`).
    have hM1run' : runFlatTM t1 (Compile.readBitRewindM sc1) cfg0
        = some { state_idx := Compile.readBitRewindM_exit_b1 sc1,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
      rw [Compile.readBitRewindM_exit_b1]; exact hM1run
    have hneg := branchComposeFlatTM_run_neg (Compile.readBitRewindM_exit_b0_ne_b1 sc1)
      (Compile.readBitRewindM_valid sc1) (Compile.readBitRewindM_valid sc2)
      (Compile.readBitRewindM_valid sc2)
      (Compile.readBitRewindM_exit_b0_lt sc1) (Compile.readBitRewindM_exit_b1_lt sc1)
      cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax hM1run' hM1traj hM2run' hhalt2
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg (Compile.readBitRewindM_exit_b0_ne_b1 sc1)
      (Compile.readBitRewindM_valid sc1) (Compile.readBitRewindM_valid sc2)
      (Compile.readBitRewindM_valid sc2)
      (Compile.readBitRewindM_exit_b0_lt sc1) (Compile.readBitRewindM_exit_b1_lt sc1)
      cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax hM1run' hM1traj hM2traj'
    refine ⟨t1 + 1 + t2, ?_, ?_, by omega⟩
    · have h := hneg.1
      rw [show Compile.readBitRewindRawM_bit sc2 b
            + ((Compile.readBitRewindM sc1).states + (Compile.readBitRewindM sc2).states)
            = (Compile.readBitRewindM sc1).states + 1 * (Compile.readBitRewindM sc2).states
              + Compile.readBitRewindRawM_bit sc2 b from by omega] at h
      rw [Compile.bitCompareRawM, Compile.readBitRewindM_exit_b0, Compile.readBitRewindM_exit_b1]
      exact h
    · intro k hk ck hck
      rw [Compile.bitCompareRawM, Compile.readBitRewindM_exit_b0, Compile.readBitRewindM_exit_b1] at hck ⊢
      exact hneg_traj k hk ck hck

/-- **`bitCompareM` run + trajectory.** From head `0` with `sc1`/`sc2` nonempty
whose first bits are `a`/`b`, `bitCompareM` reaches the MATCH exit iff `a = b`
(NOMATCH otherwise), head restored to `0`, tape unchanged. -/
theorem Compile.bitCompareM_run (s : State) (sc1 sc2 : Var) (res : List Nat)
    (a b : Nat) (cs1 cs2 : List Nat)
    (hc1 : State.get s sc1 = a :: cs1) (hc2 : State.get s sc2 = b :: cs2)
    (ha : a ≤ 1) (hb : b ≤ 1) (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.bitCompareM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := if a = b then Compile.bitCompareM_exit_match sc1 sc2
                              else Compile.bitCompareM_exit_nomatch sc1 sc2,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.bitCompareM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.bitCompareM_exit_match sc1 sc2 ∧
        ck.state_idx ≠ Compile.bitCompareM_exit_nomatch sc1 sc2 ∧
        haltingStateReached (Compile.bitCompareM sc1 sc2) ck = false)
    ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 10 := by
  obtain ⟨t, hraw_run, hraw_traj, htle⟩ :=
    Compile.bitCompareRawM_run s sc1 sc2 res a b cs1 cs2 hc1 hc2 ha hb hsc1 hsc2 hbit hres
  have hsym4 : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < 4 := Compile.eqVerdict_sym4 s res hbit
  interval_cases a <;> interval_cases b
  · -- a=0,b=0 → MATCH (m00, kept)
    have hE : (Compile.readBitRewindM sc1).states + 0 * (Compile.readBitRewindM sc2).states
        + Compile.readBitRewindRawM_bit sc2 0 = Compile.bitCompareRawM_m00 sc1 sc2 := by
      rw [Compile.bitCompareRawM_m00, Compile.readBitRewindM_exit_b0]; omega
    rw [hE] at hraw_run
    obtain ⟨hrun, htraj⟩ := Compile.bitCompareM_transport_kept sc1 sc2 _ t _
      (Compile.bitCompareRawM_distinct sc1 sc2).2.1
      (Compile.bitCompareRawM_distinct sc1 sc2).2.2.1 hraw_run hraw_traj
    exact ⟨t, by simpa using hrun, htraj, by omega⟩
  · -- a=0,b=1 → NOMATCH (m01, kept)
    have hE : (Compile.readBitRewindM sc1).states + 0 * (Compile.readBitRewindM sc2).states
        + Compile.readBitRewindRawM_bit sc2 1 = Compile.bitCompareRawM_m01 sc1 sc2 := by
      rw [Compile.bitCompareRawM_m01, Compile.readBitRewindM_exit_b1]; omega
    rw [hE] at hraw_run
    obtain ⟨hrun, htraj⟩ := Compile.bitCompareM_transport_kept sc1 sc2 _ t _
      (Compile.bitCompareRawM_distinct sc1 sc2).2.2.2.1
      (Compile.bitCompareRawM_distinct sc1 sc2).2.2.2.2.1 hraw_run hraw_traj
    exact ⟨t, by simpa [Compile.bitCompareM_exit_nomatch] using hrun, htraj, by omega⟩
  · -- a=1,b=0 → NOMATCH (m10, demoted by outer)
    have hE : (Compile.readBitRewindM sc1).states + 1 * (Compile.readBitRewindM sc2).states
        + Compile.readBitRewindRawM_bit sc2 0 = Compile.bitCompareRawM_m10 sc1 sc2 := by
      rw [Compile.bitCompareRawM_m10, Compile.readBitRewindM_exit_b0]; omega
    rw [hE] at hraw_run
    obtain ⟨hrun, htraj⟩ :=
      Compile.bitCompareM_transport_m10 sc1 sc2 _ t hsym4 hraw_run hraw_traj
    exact ⟨t + 1, by simpa using hrun, htraj, by omega⟩
  · -- a=1,b=1 → MATCH (m11, demoted by inner)
    have hE : (Compile.readBitRewindM sc1).states + 1 * (Compile.readBitRewindM sc2).states
        + Compile.readBitRewindRawM_bit sc2 1 = Compile.bitCompareRawM_m11 sc1 sc2 := by
      rw [Compile.bitCompareRawM_m11, Compile.readBitRewindM_exit_b1]; omega
    rw [hE] at hraw_run
    obtain ⟨hrun, htraj⟩ :=
      Compile.bitCompareM_transport_m11 sc1 sc2 _ t hsym4 hraw_run hraw_traj
    exact ⟨t + 1, by simpa using hrun, htraj, by omega⟩

/-! ### `bothNonemptyM` — the consume-loop guard: "are BOTH `sc1` and `sc2`
nonempty?" (bottom-up, Risk C2 — d2a)

The consume-loop body ITERATEs only while both scratch registers are nonempty
*and* their heads match. `bothNonemptyM sc1 sc2` is the clean 2-exit guard for the
first conjunct, head restored to `0`:

  bothNonemptyRawM sc1 sc2 := branchComposeFlatTM (navTestRewindM sc1)
                                (navTestRewindM sc2) idTM
                                (navTestRewindM_exit_content sc1)
                                (navTestRewindM_exit_delim sc1)

`sc1` nonempty → `navTestRewindM sc2` (content = YES, delim = NO_b); `sc1` empty →
`idTM` (immediate, head already `0`) = NO_a. Three halts {YES, NO_b, NO_a}.
`bothNonemptyM` merges the two NO halts with one `joinTwoHalts`, leaving the clean
2-exit `{YES, NO}`. Structural mirror of `eqVerdictM` (idTM swapped to the negative
branch), `halt_only` via the new `_M2two`. Consumed by `testMachine`. -/

/-- The branch symbol bound (`v < max sigs`) at head `0` for `bothNonemptyM`. -/
private theorem Compile.bothNonempty_symMax (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) :
    ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (Compile.navTestRewindM sc1).sig
            (max (Compile.navTestRewindM sc2).sig Compile.idTM.sig) := by
  intro v hv
  have hmax : max (Compile.navTestRewindM sc1).sig
      (max (Compile.navTestRewindM sc2).sig Compile.idTM.sig) = 4 := by
    rw [Compile.navTestRewindM_sig, Compile.navTestRewindM_sig]; decide
  rw [hmax]; exact Compile.eqVerdict_sym4 s res hbit v hv

/-- **`bothNonemptyM` run — YES (both `sc1` and `sc2` nonempty).** -/
theorem Compile.bothNonemptyM_run_yes (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hne1 : State.get s sc1 ≠ []) (hne2 : State.get s sc2 ≠ [])
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.bothNonemptyM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.bothNonemptyM_exit_yes sc1 sc2,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.bothNonemptyM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.bothNonemptyM_exit_yes sc1 sc2 ∧
        ck.state_idx ≠ Compile.bothNonemptyM_exit_no sc1 sc2 ∧
        haltingStateReached (Compile.bothNonemptyM sc1 sc2) ck = false)
    ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 2 := by
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ := Compile.navTestRewindM_run_content s sc1 res hbit hsc1 hne1 hres
  obtain ⟨t₂, hM2run, hM2traj, ht2le⟩ := Compile.navTestRewindM_run_content s sc2 res hbit hsc2 hne2 hres
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hsymMax := Compile.bothNonempty_symMax s sc1 sc2 res hbit
  have hcfg_lt : (0 : Nat) < (Compile.navTestRewindM sc1).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.navTestRewindM_exit_content_lt sc1)
  have hM2run' : runFlatTM t₂ (Compile.navTestRewindM sc2)
      { state_idx := (Compile.navTestRewindM sc2).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.navTestRewindM_exit_content sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    rw [Compile.navTestRewindM_start]; exact hM2run
  have hM2traj' : ∀ k, k < t₂ → ∀ ck,
      runFlatTM k (Compile.navTestRewindM sc2)
          { state_idx := (Compile.navTestRewindM sc2).start,
            tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.navTestRewindM sc2) ck = false := by
    rw [Compile.navTestRewindM_start]
    exact fun k hk ck hck => (hM2traj k hk ck hck).2.2
  have hpos := branchComposeFlatTM_run_pos
    (Compile.navTestRewindM_exit_content_ne_delim sc1)
    (Compile.navTestRewindM_valid sc1) (Compile.navTestRewindM_valid sc2) Compile.idTM_valid
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM2run'
    (Compile.haltingStateReached_of_halt (Compile.navTestRewindM_exit_content_is_halt sc2))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (Compile.navTestRewindM_valid sc1) (Compile.navTestRewindM_valid sc2) Compile.idTM_valid
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM2traj'
  have hraw_run : runFlatTM (t₁ + 1 + t₂) (Compile.bothNonemptyRawM sc1 sc2) cfg0
      = some { state_idx := Compile.bothNonemptyRawM_yes sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    have h := hpos.1
    have hstate : Compile.navTestRewindM_exit_content sc2 + (Compile.navTestRewindM sc1).states
        = Compile.bothNonemptyRawM_yes sc1 sc2 := by
      rw [Compile.bothNonemptyRawM_yes]; omega
    rw [hstate] at h; exact h
  have hnv : ∀ k, k ≤ t₁ + 1 + t₂ → ∀ ck,
      runFlatTM k (Compile.bothNonemptyRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.bothNonemptyRawM_noB sc1 sc2 := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · exact ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_noB_is_halt sc1 sc2)
        (hpos_traj k hlt ck hck)
    · rw [hraw_run] at hck; rw [← Option.some.inj hck]
      exact Compile.bothNonemptyRawM_yes_ne_noB sc1 sc2
  refine ⟨t₁ + 1 + t₂, ?_, ?_, by omega⟩
  · rw [Compile.bothNonemptyM, joinTwoHalts_run_eq _ _ _ (t₁ + 1 + t₂) cfg0 hnv,
        Compile.bothNonemptyM_exit_yes]
    exact hraw_run
  · intro k hk ck hck
    have hnv_k : ∀ j, j ≤ k → ∀ cj,
        runFlatTM j (Compile.bothNonemptyRawM sc1 sc2) cfg0 = some cj →
        cj.state_idx ≠ Compile.bothNonemptyRawM_noB sc1 sc2 :=
      fun j hj cj hcj => hnv j (le_trans hj (Nat.le_of_lt hk)) cj hcj
    rw [Compile.bothNonemptyM, joinTwoHalts_run_eq _ _ _ k cfg0 hnv_k] at hck
    have hnh := hpos_traj k (by omega) ck hck
    refine ⟨ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_yes_is_halt sc1 sc2) hnh,
      ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_noA_is_halt sc1 sc2) hnh, ?_⟩
    rw [Compile.bothNonemptyM, joinTwoHalts_halting_eq _ _ _ ck
      (ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_noB_is_halt sc1 sc2) hnh)]
    exact hnh

/-- **`bothNonemptyM` run — NO via the left operand (`sc1` empty).** -/
theorem Compile.bothNonemptyM_run_no_left (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) (hsc1 : sc1 < s.length) (hempty1 : State.get s sc1 = [])
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.bothNonemptyM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.bothNonemptyM_exit_no sc1 sc2,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.bothNonemptyM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.bothNonemptyM_exit_yes sc1 sc2 ∧
        ck.state_idx ≠ Compile.bothNonemptyM_exit_no sc1 sc2 ∧
        haltingStateReached (Compile.bothNonemptyM sc1 sc2) ck = false)
    ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 2 := by
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ := Compile.navTestRewindM_run_delim s sc1 res hbit hsc1 hempty1 hres
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hsymMax := Compile.bothNonempty_symMax s sc1 sc2 res hbit
  have hcfg_lt : (0 : Nat) < (Compile.navTestRewindM sc1).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.navTestRewindM_exit_content_lt sc1)
  have hneg := branchComposeFlatTM_run_neg
    (Compile.navTestRewindM_exit_content_ne_delim sc1)
    (Compile.navTestRewindM_valid sc1) (Compile.navTestRewindM_valid sc2) Compile.idTM_valid
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj
    (show runFlatTM 0 Compile.idTM
        { state_idx := (0 : Nat), tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := (0 : Nat), tapes := [([], 0, Compile.encodeTape s ++ res)] } from rfl)
    (Compile.haltingStateReached_of_halt (show Compile.idTM.halt[(0 : Nat)]? = some true from rfl))
  have hneg_traj := branchComposeFlatTM_no_early_halt_neg
    (Compile.navTestRewindM_exit_content_ne_delim sc1)
    (Compile.navTestRewindM_valid sc1) (Compile.navTestRewindM_valid sc2) Compile.idTM_valid
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj (fun k hk _ _ => absurd hk (Nat.not_lt_zero k))
  have hraw_run : runFlatTM (t₁ + 1 + 0) (Compile.bothNonemptyRawM sc1 sc2) cfg0
      = some { state_idx := Compile.bothNonemptyRawM_noA sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    have h := hneg.1
    have hstate : (0 : Nat) + ((Compile.navTestRewindM sc1).states + (Compile.navTestRewindM sc2).states)
        = Compile.bothNonemptyRawM_noA sc1 sc2 := by
      rw [Compile.bothNonemptyRawM_noA]; omega
    rw [hstate] at h; exact h
  have hnv : ∀ k, k ≤ t₁ + 1 + 0 → ∀ ck,
      runFlatTM k (Compile.bothNonemptyRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.bothNonemptyRawM_noB sc1 sc2 := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · exact ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_noB_is_halt sc1 sc2)
        (hneg_traj k hlt ck hck)
    · rw [hraw_run] at hck; rw [← Option.some.inj hck]
      exact fun h => Compile.bothNonemptyRawM_noA_ne_noB sc1 sc2 h
  refine ⟨t₁ + 1 + 0, ?_, ?_, by omega⟩
  · rw [Compile.bothNonemptyM, joinTwoHalts_run_eq _ _ _ (t₁ + 1 + 0) cfg0 hnv,
        Compile.bothNonemptyM_exit_no]
    exact hraw_run
  · intro k hk ck hck
    have hnv_k : ∀ j, j ≤ k → ∀ cj,
        runFlatTM j (Compile.bothNonemptyRawM sc1 sc2) cfg0 = some cj →
        cj.state_idx ≠ Compile.bothNonemptyRawM_noB sc1 sc2 :=
      fun j hj cj hcj => hnv j (le_trans hj (Nat.le_of_lt hk)) cj hcj
    rw [Compile.bothNonemptyM, joinTwoHalts_run_eq _ _ _ k cfg0 hnv_k] at hck
    have hnh := hneg_traj k (by omega) ck hck
    refine ⟨ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_yes_is_halt sc1 sc2) hnh,
      ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_noA_is_halt sc1 sc2) hnh, ?_⟩
    rw [Compile.bothNonemptyM, joinTwoHalts_halting_eq _ _ _ ck
      (ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_noB_is_halt sc1 sc2) hnh)]
    exact hnh

/-- **`bothNonemptyM` run — NO via the right operand (`sc1` nonempty, `sc2` empty).**
The raw machine reaches the demoted NO_b halt, then `joinTwoHalts` bridges it to
the kept NO exit in one extra step. -/
theorem Compile.bothNonemptyM_run_no_right (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hne1 : State.get s sc1 ≠ []) (hempty2 : State.get s sc2 = [])
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.bothNonemptyM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.bothNonemptyM_exit_no sc1 sc2,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.bothNonemptyM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.bothNonemptyM_exit_yes sc1 sc2 ∧
        ck.state_idx ≠ Compile.bothNonemptyM_exit_no sc1 sc2 ∧
        haltingStateReached (Compile.bothNonemptyM sc1 sc2) ck = false)
    ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 2 := by
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ := Compile.navTestRewindM_run_content s sc1 res hbit hsc1 hne1 hres
  obtain ⟨t₂, hM2run, hM2traj, ht2le⟩ := Compile.navTestRewindM_run_delim s sc2 res hbit hsc2 hempty2 hres
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hsymMax := Compile.bothNonempty_symMax s sc1 sc2 res hbit
  have hcfg_lt : (0 : Nat) < (Compile.navTestRewindM sc1).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.navTestRewindM_exit_content_lt sc1)
  have hM2run' : runFlatTM t₂ (Compile.navTestRewindM sc2)
      { state_idx := (Compile.navTestRewindM sc2).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.navTestRewindM_exit_delim sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    rw [Compile.navTestRewindM_start]; exact hM2run
  have hM2traj' : ∀ k, k < t₂ → ∀ ck,
      runFlatTM k (Compile.navTestRewindM sc2)
          { state_idx := (Compile.navTestRewindM sc2).start,
            tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.navTestRewindM sc2) ck = false := by
    rw [Compile.navTestRewindM_start]
    exact fun k hk ck hck => (hM2traj k hk ck hck).2.2
  have hpos := branchComposeFlatTM_run_pos
    (Compile.navTestRewindM_exit_content_ne_delim sc1)
    (Compile.navTestRewindM_valid sc1) (Compile.navTestRewindM_valid sc2) Compile.idTM_valid
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM2run'
    (Compile.haltingStateReached_of_halt (Compile.navTestRewindM_exit_delim_is_halt sc2))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (Compile.navTestRewindM_valid sc1) (Compile.navTestRewindM_valid sc2) Compile.idTM_valid
    (Compile.navTestRewindM_exit_content_lt sc1) (Compile.navTestRewindM_exit_delim_lt sc1)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM2traj'
  have hraw_noB : runFlatTM (t₁ + 1 + t₂) (Compile.bothNonemptyRawM sc1 sc2) cfg0
      = some { state_idx := Compile.bothNonemptyRawM_noB sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    have h := hpos.1
    have hstate : Compile.navTestRewindM_exit_delim sc2 + (Compile.navTestRewindM sc1).states
        = Compile.bothNonemptyRawM_noB sc1 sc2 := by
      rw [Compile.bothNonemptyRawM_noB]; omega
    rw [hstate] at h; exact h
  have hnv_strict : ∀ k, k < t₁ + 1 + t₂ → ∀ ck,
      runFlatTM k (Compile.bothNonemptyRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.bothNonemptyRawM_noB sc1 sc2 :=
    fun k hk ck hck => ClearGadget.ne_of_not_halting
      (Compile.bothNonemptyRawM_noB_is_halt sc1 sc2) (hpos_traj k hk ck hck)
  have hweak : runFlatTM (t₁ + 1 + t₂) (Compile.bothNonemptyM sc1 sc2) cfg0
      = some { state_idx := Compile.bothNonemptyRawM_noB sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    rw [Compile.bothNonemptyM, joinTwoHalts_run_eq_weak _ _ _ (t₁ + 1 + t₂) cfg0 hnv_strict]
    exact hraw_noB
  have hnh_noB : haltingStateReached (Compile.bothNonemptyM sc1 sc2)
      { state_idx := Compile.bothNonemptyRawM_noB sc1 sc2,
        tapes := [([], 0, Compile.encodeTape s ++ res)] } = false := by
    show ((Compile.bothNonemptyRawM sc1 sc2).halt.set (Compile.bothNonemptyRawM_noB sc1 sc2) false).getD
      (Compile.bothNonemptyRawM_noB sc1 sc2) false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl]
    split <;> rfl
  have hsymRaw : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < (Compile.bothNonemptyRawM sc1 sc2).sig := by
    intro v hv; rw [Compile.bothNonemptyRawM_sig]; exact Compile.eqVerdict_sym4 s res hbit v hv
  have hstep : stepFlatTM (Compile.bothNonemptyM sc1 sc2)
      { state_idx := Compile.bothNonemptyRawM_noB sc1 sc2,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.bothNonemptyRawM_noA sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } :=
    joinTwoHalts_step_to_h1 (Compile.bothNonemptyRawM sc1 sc2)
      (Compile.bothNonemptyRawM_noA sc1 sc2) (Compile.bothNonemptyRawM_noB sc1 sc2)
      [] (Compile.encodeTape s ++ res) 0 hsymRaw
  have hfull : runFlatTM (t₁ + 1 + t₂ + 1) (Compile.bothNonemptyM sc1 sc2) cfg0
      = some { state_idx := Compile.bothNonemptyRawM_noA sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } :=
    runFlatTM_extend_by_step (Compile.bothNonemptyM sc1 sc2) (t₁ + 1 + t₂) cfg0 _ _
      hweak hnh_noB hstep
  refine ⟨t₁ + 1 + t₂ + 1, ?_, ?_, by omega⟩
  · rw [Compile.bothNonemptyM_exit_no]; exact hfull
  · intro k hk ck hck
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
    · have hnv_k : ∀ j, j ≤ k → ∀ cj,
          runFlatTM j (Compile.bothNonemptyRawM sc1 sc2) cfg0 = some cj →
          cj.state_idx ≠ Compile.bothNonemptyRawM_noB sc1 sc2 :=
        fun j hj cj hcj => hnv_strict j (by omega) cj hcj
      rw [Compile.bothNonemptyM, joinTwoHalts_run_eq _ _ _ k cfg0 hnv_k] at hck
      have hnh := hpos_traj k (by omega) ck hck
      refine ⟨ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_yes_is_halt sc1 sc2) hnh,
        ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_noA_is_halt sc1 sc2) hnh, ?_⟩
      rw [Compile.bothNonemptyM, joinTwoHalts_halting_eq _ _ _ ck
        (ClearGadget.ne_of_not_halting (Compile.bothNonemptyRawM_noB_is_halt sc1 sc2) hnh)]
      exact hnh
    · rw [hweak] at hck
      have hck_eq : ck = { state_idx := Compile.bothNonemptyRawM_noB sc1 sc2,
                           tapes := [([], 0, Compile.encodeTape s ++ res)] } :=
        Option.some.inj hck.symm
      refine ⟨?_, ?_, ?_⟩
      · rw [hck_eq, Compile.bothNonemptyM_exit_yes]
        exact fun h => Compile.bothNonemptyRawM_yes_ne_noB sc1 sc2 h.symm
      · rw [hck_eq, Compile.bothNonemptyM_exit_no]
        exact fun h => Compile.bothNonemptyRawM_noA_ne_noB sc1 sc2 h.symm
      · rw [hck_eq]; exact hnh_noB

/-! ### `testMachine` — the consume-loop body decision (bottom-up, Risk C2 — d2a)

`testMachine sc1 sc2` is the clean 2-exit decision the consume-loop body branches
on: ITER iff both scratch registers are nonempty AND their first bits match;
DONE otherwise (head restored to `0`, tape unchanged):

  testMachineRawM sc1 sc2 := branchComposeFlatTM (bothNonemptyM sc1 sc2)
                               (bitCompareM sc1 sc2) idTM
                               (bothNonemptyM_exit_yes sc1 sc2)
                               (bothNonemptyM_exit_no sc1 sc2)

both nonempty → `bitCompareM` (MATCH = ITER, NOMATCH); at least one empty → `idTM`
(immediate, head already `0`) = DONE_a. Three halts {ITER, NOMATCH, DONE_a}.
`testMachine` merges NOMATCH + DONE_a with one `joinTwoHalts`, leaving the clean
2-exit `{ITER, DONE}`. `halt_only` via `_M2two`. The loop body `B` then dispatches
ITER → `iterTailsTM` (delete both heads) and DONE → halt. -/

/-- The branch symbol bound (`v < max sigs`) at head `0` for `testMachine`. -/
private theorem Compile.testMachine_symMax (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) :
    ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (Compile.bothNonemptyM sc1 sc2).sig
            (max (Compile.bitCompareM sc1 sc2).sig Compile.idTM.sig) := by
  intro v hv
  have hmax : max (Compile.bothNonemptyM sc1 sc2).sig
      (max (Compile.bitCompareM sc1 sc2).sig Compile.idTM.sig) = 4 := by
    rw [Compile.bothNonemptyM_sig, Compile.bitCompareM_sig]; decide
  rw [hmax]; exact Compile.eqVerdict_sym4 s res hbit v hv

/-- **`testMachine` run — DONE from a `bothNonemptyM`-NO outcome.** The shared core
of the two DONE-by-empty cases: given `bothNonemptyM` reaches its NO exit, the
negative `idTM` branch lands on the kept DONE exit. -/
private theorem Compile.testMachine_run_done_of_no (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) (t₁ : Nat)
    (ht1le : t₁ ≤ 6 * (Compile.encodeTape s ++ res).length + 2)
    (hM1run : runFlatTM t₁ (Compile.bothNonemptyM sc1 sc2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.bothNonemptyM_exit_no sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] })
    (hM1traj : ∀ k, k < t₁ → ∀ ck,
        runFlatTM k (Compile.bothNonemptyM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.bothNonemptyM_exit_yes sc1 sc2 ∧
        ck.state_idx ≠ Compile.bothNonemptyM_exit_no sc1 sc2 ∧
        haltingStateReached (Compile.bothNonemptyM sc1 sc2) ck = false) :
    ∃ t,
      runFlatTM t (Compile.testMachine sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.testMachine_exit_done sc1 sc2,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.testMachine sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.testMachine_exit_iter sc1 sc2 ∧
        ck.state_idx ≠ Compile.testMachine_exit_done sc1 sc2 ∧
        haltingStateReached (Compile.testMachine sc1 sc2) ck = false)
    ∧ t ≤ 12 * (Compile.encodeTape s ++ res).length + 14 := by
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hsymMax := Compile.testMachine_symMax s sc1 sc2 res hbit
  have hcfg_lt : (0 : Nat) < (Compile.bothNonemptyM sc1 sc2).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.bothNonemptyM_exit_yes_lt sc1 sc2)
  have hneg := branchComposeFlatTM_run_neg
    (Compile.bothNonemptyM_exit_yes_ne_no sc1 sc2)
    (Compile.bothNonemptyM_valid sc1 sc2) (Compile.bitCompareM_valid sc1 sc2) Compile.idTM_valid
    (Compile.bothNonemptyM_exit_yes_lt sc1 sc2) (Compile.bothNonemptyM_exit_no_lt sc1 sc2)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj
    (show runFlatTM 0 Compile.idTM
        { state_idx := (0 : Nat), tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := (0 : Nat), tapes := [([], 0, Compile.encodeTape s ++ res)] } from rfl)
    (Compile.haltingStateReached_of_halt (show Compile.idTM.halt[(0 : Nat)]? = some true from rfl))
  have hneg_traj := branchComposeFlatTM_no_early_halt_neg
    (Compile.bothNonemptyM_exit_yes_ne_no sc1 sc2)
    (Compile.bothNonemptyM_valid sc1 sc2) (Compile.bitCompareM_valid sc1 sc2) Compile.idTM_valid
    (Compile.bothNonemptyM_exit_yes_lt sc1 sc2) (Compile.bothNonemptyM_exit_no_lt sc1 sc2)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj (fun k hk _ _ => absurd hk (Nat.not_lt_zero k))
  have hraw_run : runFlatTM (t₁ + 1 + 0) (Compile.testMachineRawM sc1 sc2) cfg0
      = some { state_idx := Compile.testMachineRawM_done sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    have h := hneg.1
    have hstate : (0 : Nat) + ((Compile.bothNonemptyM sc1 sc2).states + (Compile.bitCompareM sc1 sc2).states)
        = Compile.testMachineRawM_done sc1 sc2 := by
      rw [Compile.testMachineRawM_done]; omega
    rw [hstate] at h; exact h
  have hnv : ∀ k, k ≤ t₁ + 1 + 0 → ∀ ck,
      runFlatTM k (Compile.testMachineRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.testMachineRawM_nomatch sc1 sc2 := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · exact ClearGadget.ne_of_not_halting (Compile.testMachineRawM_nomatch_is_halt sc1 sc2)
        (hneg_traj k hlt ck hck)
    · rw [hraw_run] at hck; rw [← Option.some.inj hck]
      exact fun h => Compile.testMachineRawM_done_ne_nomatch sc1 sc2 h
  refine ⟨t₁ + 1 + 0, ?_, ?_, by omega⟩
  · rw [Compile.testMachine, joinTwoHalts_run_eq _ _ _ (t₁ + 1 + 0) cfg0 hnv,
        Compile.testMachine_exit_done]
    exact hraw_run
  · intro k hk ck hck
    have hnv_k : ∀ j, j ≤ k → ∀ cj,
        runFlatTM j (Compile.testMachineRawM sc1 sc2) cfg0 = some cj →
        cj.state_idx ≠ Compile.testMachineRawM_nomatch sc1 sc2 :=
      fun j hj cj hcj => hnv j (le_trans hj (Nat.le_of_lt hk)) cj hcj
    rw [Compile.testMachine, joinTwoHalts_run_eq _ _ _ k cfg0 hnv_k] at hck
    have hnh := hneg_traj k (by omega) ck hck
    refine ⟨ClearGadget.ne_of_not_halting (Compile.testMachineRawM_iter_is_halt sc1 sc2) hnh,
      ClearGadget.ne_of_not_halting (Compile.testMachineRawM_done_is_halt sc1 sc2) hnh, ?_⟩
    rw [Compile.testMachine, joinTwoHalts_halting_eq _ _ _ ck
      (ClearGadget.ne_of_not_halting (Compile.testMachineRawM_nomatch_is_halt sc1 sc2) hnh)]
    exact hnh

/-- **`testMachine` run — DONE (`sc1` empty).** -/
theorem Compile.testMachine_run_done_left (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) (hsc1 : sc1 < s.length) (hempty1 : State.get s sc1 = [])
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.testMachine sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.testMachine_exit_done sc1 sc2,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.testMachine sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.testMachine_exit_iter sc1 sc2 ∧
        ck.state_idx ≠ Compile.testMachine_exit_done sc1 sc2 ∧
        haltingStateReached (Compile.testMachine sc1 sc2) ck = false)
    ∧ t ≤ 12 * (Compile.encodeTape s ++ res).length + 14 := by
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ :=
    Compile.bothNonemptyM_run_no_left s sc1 sc2 res hbit hsc1 hempty1 hres
  exact Compile.testMachine_run_done_of_no s sc1 sc2 res hbit t₁ ht1le hM1run hM1traj

/-- **`testMachine` run — DONE (`sc1` nonempty, `sc2` empty).** -/
theorem Compile.testMachine_run_done_right (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hne1 : State.get s sc1 ≠ []) (hempty2 : State.get s sc2 = [])
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.testMachine sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.testMachine_exit_done sc1 sc2,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.testMachine sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.testMachine_exit_iter sc1 sc2 ∧
        ck.state_idx ≠ Compile.testMachine_exit_done sc1 sc2 ∧
        haltingStateReached (Compile.testMachine sc1 sc2) ck = false)
    ∧ t ≤ 12 * (Compile.encodeTape s ++ res).length + 14 := by
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ :=
    Compile.bothNonemptyM_run_no_right s sc1 sc2 res hbit hsc1 hsc2 hne1 hempty2 hres
  exact Compile.testMachine_run_done_of_no s sc1 sc2 res hbit t₁ ht1le hM1run hM1traj

/-- **`testMachine` run — ITER (both nonempty, first bits match).** -/
theorem Compile.testMachine_run_iter (s : State) (sc1 sc2 : Var) (res : List Nat)
    (a b : Nat) (cs1 cs2 : List Nat)
    (hc1 : State.get s sc1 = a :: cs1) (hc2 : State.get s sc2 = b :: cs2)
    (ha : a ≤ 1) (hb : b ≤ 1) (hab : a = b) (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.testMachine sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.testMachine_exit_iter sc1 sc2,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.testMachine sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.testMachine_exit_iter sc1 sc2 ∧
        ck.state_idx ≠ Compile.testMachine_exit_done sc1 sc2 ∧
        haltingStateReached (Compile.testMachine sc1 sc2) ck = false)
    ∧ t ≤ 12 * (Compile.encodeTape s ++ res).length + 14 := by
  have hne1 : State.get s sc1 ≠ [] := by rw [hc1]; exact List.cons_ne_nil _ _
  have hne2 : State.get s sc2 ≠ [] := by rw [hc2]; exact List.cons_ne_nil _ _
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ :=
    Compile.bothNonemptyM_run_yes s sc1 sc2 res hbit hsc1 hsc2 hne1 hne2 hres
  obtain ⟨t₂, hM2run, hM2traj, ht2le⟩ :=
    Compile.bitCompareM_run s sc1 sc2 res a b cs1 cs2 hc1 hc2 ha hb hsc1 hsc2 hbit hres
  rw [if_pos hab] at hM2run
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hsymMax := Compile.testMachine_symMax s sc1 sc2 res hbit
  have hcfg_lt : (0 : Nat) < (Compile.bothNonemptyM sc1 sc2).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.bothNonemptyM_exit_yes_lt sc1 sc2)
  have hM2run' : runFlatTM t₂ (Compile.bitCompareM sc1 sc2)
      { state_idx := (Compile.bitCompareM sc1 sc2).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.bitCompareM_exit_match sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    rw [Compile.bitCompareM_start]; exact hM2run
  have hM2traj' : ∀ k, k < t₂ → ∀ ck,
      runFlatTM k (Compile.bitCompareM sc1 sc2)
          { state_idx := (Compile.bitCompareM sc1 sc2).start,
            tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.bitCompareM sc1 sc2) ck = false := by
    rw [Compile.bitCompareM_start]
    exact fun k hk ck hck => (hM2traj k hk ck hck).2.2
  have hpos := branchComposeFlatTM_run_pos
    (Compile.bothNonemptyM_exit_yes_ne_no sc1 sc2)
    (Compile.bothNonemptyM_valid sc1 sc2) (Compile.bitCompareM_valid sc1 sc2) Compile.idTM_valid
    (Compile.bothNonemptyM_exit_yes_lt sc1 sc2) (Compile.bothNonemptyM_exit_no_lt sc1 sc2)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM2run'
    (Compile.haltingStateReached_of_halt (Compile.bitCompareM_exit_match_is_halt sc1 sc2))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (Compile.bothNonemptyM_valid sc1 sc2) (Compile.bitCompareM_valid sc1 sc2) Compile.idTM_valid
    (Compile.bothNonemptyM_exit_yes_lt sc1 sc2) (Compile.bothNonemptyM_exit_no_lt sc1 sc2)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM2traj'
  have hraw_run : runFlatTM (t₁ + 1 + t₂) (Compile.testMachineRawM sc1 sc2) cfg0
      = some { state_idx := Compile.testMachineRawM_iter sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    have h := hpos.1
    have hstate : Compile.bitCompareM_exit_match sc1 sc2 + (Compile.bothNonemptyM sc1 sc2).states
        = Compile.testMachineRawM_iter sc1 sc2 := by
      rw [Compile.testMachineRawM_iter]; omega
    rw [hstate] at h; exact h
  have hnv : ∀ k, k ≤ t₁ + 1 + t₂ → ∀ ck,
      runFlatTM k (Compile.testMachineRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.testMachineRawM_nomatch sc1 sc2 := by
    intro k hk ck hck
    rcases Nat.lt_or_eq_of_le hk with hlt | rfl
    · exact ClearGadget.ne_of_not_halting (Compile.testMachineRawM_nomatch_is_halt sc1 sc2)
        (hpos_traj k hlt ck hck)
    · rw [hraw_run] at hck; rw [← Option.some.inj hck]
      exact fun h => Compile.testMachineRawM_iter_ne_nomatch sc1 sc2 h
  refine ⟨t₁ + 1 + t₂, ?_, ?_, by omega⟩
  · rw [Compile.testMachine, joinTwoHalts_run_eq _ _ _ (t₁ + 1 + t₂) cfg0 hnv,
        Compile.testMachine_exit_iter]
    exact hraw_run
  · intro k hk ck hck
    have hnv_k : ∀ j, j ≤ k → ∀ cj,
        runFlatTM j (Compile.testMachineRawM sc1 sc2) cfg0 = some cj →
        cj.state_idx ≠ Compile.testMachineRawM_nomatch sc1 sc2 :=
      fun j hj cj hcj => hnv j (le_trans hj (Nat.le_of_lt hk)) cj hcj
    rw [Compile.testMachine, joinTwoHalts_run_eq _ _ _ k cfg0 hnv_k] at hck
    have hnh := hpos_traj k (by omega) ck hck
    refine ⟨ClearGadget.ne_of_not_halting (Compile.testMachineRawM_iter_is_halt sc1 sc2) hnh,
      ClearGadget.ne_of_not_halting (Compile.testMachineRawM_done_is_halt sc1 sc2) hnh, ?_⟩
    rw [Compile.testMachine, joinTwoHalts_halting_eq _ _ _ ck
      (ClearGadget.ne_of_not_halting (Compile.testMachineRawM_nomatch_is_halt sc1 sc2) hnh)]
    exact hnh

/-- **`testMachine` run — DONE (both nonempty, first bits differ).** The raw machine
reaches the demoted NOMATCH halt, then `joinTwoHalts` bridges it to the kept DONE
exit in one extra step. -/
theorem Compile.testMachine_run_done_neq (s : State) (sc1 sc2 : Var) (res : List Nat)
    (a b : Nat) (cs1 cs2 : List Nat)
    (hc1 : State.get s sc1 = a :: cs1) (hc2 : State.get s sc2 = b :: cs2)
    (ha : a ≤ 1) (hb : b ≤ 1) (hab : a ≠ b) (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.testMachine sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.testMachine_exit_done sc1 sc2,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.testMachine sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.testMachine_exit_iter sc1 sc2 ∧
        ck.state_idx ≠ Compile.testMachine_exit_done sc1 sc2 ∧
        haltingStateReached (Compile.testMachine sc1 sc2) ck = false)
    ∧ t ≤ 12 * (Compile.encodeTape s ++ res).length + 14 := by
  have hne1 : State.get s sc1 ≠ [] := by rw [hc1]; exact List.cons_ne_nil _ _
  have hne2 : State.get s sc2 ≠ [] := by rw [hc2]; exact List.cons_ne_nil _ _
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ :=
    Compile.bothNonemptyM_run_yes s sc1 sc2 res hbit hsc1 hsc2 hne1 hne2 hres
  obtain ⟨t₂, hM2run, hM2traj, ht2le⟩ :=
    Compile.bitCompareM_run s sc1 sc2 res a b cs1 cs2 hc1 hc2 ha hb hsc1 hsc2 hbit hres
  rw [if_neg hab] at hM2run
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hsymMax := Compile.testMachine_symMax s sc1 sc2 res hbit
  have hcfg_lt : (0 : Nat) < (Compile.bothNonemptyM sc1 sc2).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.bothNonemptyM_exit_yes_lt sc1 sc2)
  have hM2run' : runFlatTM t₂ (Compile.bitCompareM sc1 sc2)
      { state_idx := (Compile.bitCompareM sc1 sc2).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.bitCompareM_exit_nomatch sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    rw [Compile.bitCompareM_start]; exact hM2run
  have hM2traj' : ∀ k, k < t₂ → ∀ ck,
      runFlatTM k (Compile.bitCompareM sc1 sc2)
          { state_idx := (Compile.bitCompareM sc1 sc2).start,
            tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.bitCompareM sc1 sc2) ck = false := by
    rw [Compile.bitCompareM_start]
    exact fun k hk ck hck => (hM2traj k hk ck hck).2.2
  have hpos := branchComposeFlatTM_run_pos
    (Compile.bothNonemptyM_exit_yes_ne_no sc1 sc2)
    (Compile.bothNonemptyM_valid sc1 sc2) (Compile.bitCompareM_valid sc1 sc2) Compile.idTM_valid
    (Compile.bothNonemptyM_exit_yes_lt sc1 sc2) (Compile.bothNonemptyM_exit_no_lt sc1 sc2)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM2run'
    (Compile.haltingStateReached_of_halt (Compile.bitCompareM_exit_nomatch_is_halt sc1 sc2))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (Compile.bothNonemptyM_valid sc1 sc2) (Compile.bitCompareM_valid sc1 sc2) Compile.idTM_valid
    (Compile.bothNonemptyM_exit_yes_lt sc1 sc2) (Compile.bothNonemptyM_exit_no_lt sc1 sc2)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM2traj'
  have hraw_nomatch : runFlatTM (t₁ + 1 + t₂) (Compile.testMachineRawM sc1 sc2) cfg0
      = some { state_idx := Compile.testMachineRawM_nomatch sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    have h := hpos.1
    have hstate : Compile.bitCompareM_exit_nomatch sc1 sc2 + (Compile.bothNonemptyM sc1 sc2).states
        = Compile.testMachineRawM_nomatch sc1 sc2 := by
      rw [Compile.testMachineRawM_nomatch]; omega
    rw [hstate] at h; exact h
  have hnv_strict : ∀ k, k < t₁ + 1 + t₂ → ∀ ck,
      runFlatTM k (Compile.testMachineRawM sc1 sc2) cfg0 = some ck →
      ck.state_idx ≠ Compile.testMachineRawM_nomatch sc1 sc2 :=
    fun k hk ck hck => ClearGadget.ne_of_not_halting
      (Compile.testMachineRawM_nomatch_is_halt sc1 sc2) (hpos_traj k hk ck hck)
  have hweak : runFlatTM (t₁ + 1 + t₂) (Compile.testMachine sc1 sc2) cfg0
      = some { state_idx := Compile.testMachineRawM_nomatch sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    rw [Compile.testMachine, joinTwoHalts_run_eq_weak _ _ _ (t₁ + 1 + t₂) cfg0 hnv_strict]
    exact hraw_nomatch
  have hnh_nomatch : haltingStateReached (Compile.testMachine sc1 sc2)
      { state_idx := Compile.testMachineRawM_nomatch sc1 sc2,
        tapes := [([], 0, Compile.encodeTape s ++ res)] } = false := by
    show ((Compile.testMachineRawM sc1 sc2).halt.set (Compile.testMachineRawM_nomatch sc1 sc2) false).getD
      (Compile.testMachineRawM_nomatch sc1 sc2) false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl]
    split <;> rfl
  have hsymRaw : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < (Compile.testMachineRawM sc1 sc2).sig := by
    intro v hv; rw [Compile.testMachineRawM_sig]; exact Compile.eqVerdict_sym4 s res hbit v hv
  have hstep : stepFlatTM (Compile.testMachine sc1 sc2)
      { state_idx := Compile.testMachineRawM_nomatch sc1 sc2,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.testMachineRawM_done sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } :=
    joinTwoHalts_step_to_h1 (Compile.testMachineRawM sc1 sc2)
      (Compile.testMachineRawM_done sc1 sc2) (Compile.testMachineRawM_nomatch sc1 sc2)
      [] (Compile.encodeTape s ++ res) 0 hsymRaw
  have hfull : runFlatTM (t₁ + 1 + t₂ + 1) (Compile.testMachine sc1 sc2) cfg0
      = some { state_idx := Compile.testMachineRawM_done sc1 sc2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] } :=
    runFlatTM_extend_by_step (Compile.testMachine sc1 sc2) (t₁ + 1 + t₂) cfg0 _ _
      hweak hnh_nomatch hstep
  refine ⟨t₁ + 1 + t₂ + 1, ?_, ?_, by omega⟩
  · rw [Compile.testMachine_exit_done]; exact hfull
  · intro k hk ck hck
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
    · have hnv_k : ∀ j, j ≤ k → ∀ cj,
          runFlatTM j (Compile.testMachineRawM sc1 sc2) cfg0 = some cj →
          cj.state_idx ≠ Compile.testMachineRawM_nomatch sc1 sc2 :=
        fun j hj cj hcj => hnv_strict j (by omega) cj hcj
      rw [Compile.testMachine, joinTwoHalts_run_eq _ _ _ k cfg0 hnv_k] at hck
      have hnh := hpos_traj k (by omega) ck hck
      refine ⟨ClearGadget.ne_of_not_halting (Compile.testMachineRawM_iter_is_halt sc1 sc2) hnh,
        ClearGadget.ne_of_not_halting (Compile.testMachineRawM_done_is_halt sc1 sc2) hnh, ?_⟩
      rw [Compile.testMachine, joinTwoHalts_halting_eq _ _ _ ck
        (ClearGadget.ne_of_not_halting (Compile.testMachineRawM_nomatch_is_halt sc1 sc2) hnh)]
      exact hnh
    · rw [hweak] at hck
      have hck_eq : ck = { state_idx := Compile.testMachineRawM_nomatch sc1 sc2,
                           tapes := [([], 0, Compile.encodeTape s ++ res)] } :=
        Option.some.inj hck.symm
      refine ⟨?_, ?_, ?_⟩
      · rw [hck_eq, Compile.testMachine_exit_iter]
        exact fun h => Compile.testMachineRawM_iter_ne_nomatch sc1 sc2 h.symm
      · rw [hck_eq, Compile.testMachine_exit_done]
        exact fun h => Compile.testMachineRawM_done_ne_nomatch sc1 sc2 h.symm
      · rw [hck_eq]; exact hnh_nomatch

/-! ### `compareBodyTM` — the `eqBit` consume-loop body (bottom-up, Risk C2 — d2a)

`compareBodyTM sc1 sc2` is the `loopTM` body for the consume loop: dispatch on the
clean 2-exit `testMachine` (ITER iff both scratch regs nonempty AND first bits
match; DONE otherwise) and on ITER run `iterTailsTM` (delete both heads, residue
`++ [0,0]`), on DONE run `idTM` (no-op, head already `0`):

  compareBodyTM sc1 sc2 := branchComposeFlatTM (testMachine sc1 sc2)
                             (iterTailsTM sc1 sc2) idTM
                             (testMachine_exit_iter sc1 sc2)
                             (testMachine_exit_done sc1 sc2)

`exitLoop` (M₂ = `iterTailsTM` exit) is `loopTM`'s `exitLoop`; `exitDone` (M₃ =
`idTM` exit `0`) is its `exitDone`. Mirrors `forBndBodyTM`/`testMachineRawM`; like
those, a *bare* branch machine — `loopTM` tolerates `iterTailsTM`'s and `idTM`'s
stray boundary halts on a terminator-free residue, so no `joinTwoHalts` wrap is
needed. The two body contracts (`_iterate_run`/`_done_run`) feed `loopTM_run`. -/

/-- Symbol bound for the seam tape `([], 0, encodeTape s ++ res)` against the body's
three-way `max` of sigs (all `4`). -/
private theorem Compile.compareBody_symMax (s : State) (sc1 sc2 : Var) (res : List Nat)
    (hbit : Compile.BitState s) :
    ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (Compile.testMachine sc1 sc2).sig
            (max (Compile.iterTailsTM sc1 sc2).sig Compile.idTM.sig) := by
  intro v hv
  have hmax : max (Compile.testMachine sc1 sc2).sig
      (max (Compile.iterTailsTM sc1 sc2).sig Compile.idTM.sig) = 4 := by
    rw [Compile.testMachine_sig, Compile.iterTailsTM_sig]; decide
  rw [hmax]; exact Compile.eqVerdict_sym4 s res hbit v hv

/-- **Body ITERATE contract.** Both scratch regs nonempty with matching first bits:
`testMachine` says ITER, then `iterTailsTM` deletes both heads in place (residue
`++ [0,0]`). The body reaches `exitLoop` with the consumed state. Feeds
`loopTM_run`'s iteration contract. -/
theorem Compile.compareBody_iterate_run (s : State) (sc1 sc2 : Var) (res : List Nat)
    (a b : Nat) (cs1 cs2 : List Nat)
    (hc1 : State.get s sc1 = a :: cs1) (hc2 : State.get s sc2 = b :: cs2)
    (ha : a ≤ 1) (hb : b ≤ 1) (hab : a = b) (hne : sc1 ≠ sc2)
    (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.compareBodyTM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.compareBodyTM_exitLoop sc1 sc2,
                 tapes := [([], 0,
                   Compile.encodeTape ((s.set sc1 (s.get sc1).tail).set sc2 (s.get sc2).tail)
                     ++ (res ++ [0, 0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.compareBodyTM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.compareBodyTM_exitDone sc1 sc2 ∧
        ck.state_idx ≠ Compile.compareBodyTM_exitLoop sc1 sc2 ∧
        haltingStateReached (Compile.compareBodyTM sc1 sc2) ck = false)
    ∧ t ≤ 24 * (Compile.encodeTape s ++ res).length + 44 := by
  have hne1 : State.get s sc1 ≠ [] := by rw [hc1]; exact List.cons_ne_nil _ _
  have hne2 : State.get s sc2 ≠ [] := by rw [hc2]; exact List.cons_ne_nil _ _
  obtain ⟨t₁, hM1run, hM1traj, ht1le⟩ :=
    Compile.testMachine_run_iter s sc1 sc2 res a b cs1 cs2 hc1 hc2 ha hb hab hsc1 hsc2 hbit hres
  obtain ⟨t₂, hM2run, hM2traj, ht2le⟩ :=
    Compile.iterTails_run s sc1 sc2 hne hsc1 hsc2 hbit hne1 hne2 res hres
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0def
  have hinit2 : initFlatConfig (Compile.iterTailsTM sc1 sc2) [Compile.encodeTape s ++ res]
      = { state_idx := (Compile.iterTailsTM sc1 sc2).start,
          tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    simp only [initFlatConfig, List.map_cons, List.map_nil]
  rw [hinit2] at hM2run hM2traj
  have hsymMax := Compile.compareBody_symMax s sc1 sc2 res hbit
  have hcfg_lt : cfg0.state_idx < (Compile.testMachine sc1 sc2).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.testMachine_exit_iter_lt sc1 sc2)
  have hhalt2 : haltingStateReached (Compile.iterTailsTM sc1 sc2)
      { state_idx := Compile.iterTailsTM_exit sc1 sc2,
        tapes := [([], 0,
          Compile.encodeTape ((s.set sc1 (s.get sc1).tail).set sc2 (s.get sc2).tail)
            ++ (res ++ [0, 0]))] } = true :=
    Compile.haltingStateReached_of_halt (Compile.iterTailsTM_exit_is_halt sc1 sc2)
  have hM2run' : runFlatTM t₂ (Compile.iterTailsTM sc1 sc2)
      { state_idx := (Compile.iterTailsTM sc1 sc2).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.iterTailsTM_exit sc1 sc2,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set sc1 (s.get sc1).tail).set sc2 (s.get sc2).tail)
                   ++ (res ++ [0, 0]))] } := hM2run
  have hM2traj' : ∀ k, k < t₂ → ∀ ck,
      runFlatTM k (Compile.iterTailsTM sc1 sc2)
          { state_idx := (Compile.iterTailsTM sc1 sc2).start,
            tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.iterTailsTM sc1 sc2) ck = false := hM2traj
  have hpos := branchComposeFlatTM_run_pos
    (Compile.testMachine_exit_iter_ne_done sc1 sc2)
    (Compile.testMachine_valid sc1 sc2) (Compile.iterTailsTM_valid sc1 sc2) Compile.idTM_valid
    (Compile.testMachine_exit_iter_lt sc1 sc2) (Compile.testMachine_exit_done_lt sc1 sc2)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM2run' hhalt2
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (Compile.testMachine_valid sc1 sc2) (Compile.iterTailsTM_valid sc1 sc2) Compile.idTM_valid
    (Compile.testMachine_exit_iter_lt sc1 sc2) (Compile.testMachine_exit_done_lt sc1 sc2)
    cfg0 hcfg_lt [] 0 (Compile.encodeTape s ++ res) hsymMax
    hM1run hM1traj hM2traj'
  refine ⟨t₁ + 1 + t₂, ?_, ?_, by omega⟩
  · have h := hpos.1
    rw [Nat.add_comm (Compile.iterTailsTM_exit sc1 sc2) (Compile.testMachine sc1 sc2).states] at h
    rw [Compile.compareBodyTM_exitLoop]
    exact h
  · intro k hk ck hck
    have hnh := hpos_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.compareBodyTM_exitDone_is_halt sc1 sc2) hnh,
           ClearGadget.ne_of_not_halting (Compile.compareBodyTM_exitLoop_is_halt sc1 sc2) hnh,
           hnh⟩

/-- **Body DONE contract.** Given `testMachine` reaches its DONE exit (on the
abstract seam tape `([], 0, right)`), the negative `idTM` branch is a no-op: the
body reaches `exitDone`, tape unchanged. Generic over `right` so the loop's
terminal step can instantiate it with any of `testMachine`'s three DONE cases. -/
theorem Compile.compareBody_done_run (sc1 sc2 : Var) (right : List Nat) {t₁ : Nat}
    (hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, right) = some v →
      v < max (Compile.testMachine sc1 sc2).sig
            (max (Compile.iterTailsTM sc1 sc2).sig Compile.idTM.sig))
    (hM1run : runFlatTM t₁ (Compile.testMachine sc1 sc2)
        { state_idx := 0, tapes := [([], 0, right)] }
      = some { state_idx := Compile.testMachine_exit_done sc1 sc2, tapes := [([], 0, right)] })
    (hM1traj : ∀ k, k < t₁ → ∀ ck,
        runFlatTM k (Compile.testMachine sc1 sc2)
            { state_idx := 0, tapes := [([], 0, right)] } = some ck →
        ck.state_idx ≠ Compile.testMachine_exit_iter sc1 sc2 ∧
        ck.state_idx ≠ Compile.testMachine_exit_done sc1 sc2 ∧
        haltingStateReached (Compile.testMachine sc1 sc2) ck = false)
    (ht1le : t₁ ≤ 12 * right.length + 14) :
    ∃ t,
      runFlatTM t (Compile.compareBodyTM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, right)] }
        = some { state_idx := Compile.compareBodyTM_exitDone sc1 sc2,
                 tapes := [([], 0, right)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.compareBodyTM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, right)] } = some ck →
        ck.state_idx ≠ Compile.compareBodyTM_exitDone sc1 sc2 ∧
        ck.state_idx ≠ Compile.compareBodyTM_exitLoop sc1 sc2 ∧
        haltingStateReached (Compile.compareBodyTM sc1 sc2) ck = false)
    ∧ t ≤ 12 * right.length + 15 := by
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, right)] } with hcfg0def
  have hcfg_lt : cfg0.state_idx < (Compile.testMachine sc1 sc2).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.testMachine_exit_iter_lt sc1 sc2)
  have hrun3 : runFlatTM 0 Compile.idTM
      { state_idx := Compile.idTM.start, tapes := [([], 0, right)] }
      = some { state_idx := 0, tapes := [([], 0, right)] } := rfl
  have hhalt3 : haltingStateReached Compile.idTM
      { state_idx := 0, tapes := [([], 0, right)] } = true :=
    Compile.haltingStateReached_of_halt (show Compile.idTM.halt[(0 : Nat)]? = some true from rfl)
  have hneg := branchComposeFlatTM_run_neg
    (Compile.testMachine_exit_iter_ne_done sc1 sc2)
    (Compile.testMachine_valid sc1 sc2) (Compile.iterTailsTM_valid sc1 sc2) Compile.idTM_valid
    (Compile.testMachine_exit_iter_lt sc1 sc2) (Compile.testMachine_exit_done_lt sc1 sc2)
    cfg0 hcfg_lt [] 0 right hsym hM1run hM1traj hrun3 hhalt3
  have hneg_traj := branchComposeFlatTM_no_early_halt_neg
    (Compile.testMachine_exit_iter_ne_done sc1 sc2)
    (Compile.testMachine_valid sc1 sc2) (Compile.iterTailsTM_valid sc1 sc2) Compile.idTM_valid
    (Compile.testMachine_exit_iter_lt sc1 sc2) (Compile.testMachine_exit_done_lt sc1 sc2)
    cfg0 hcfg_lt [] 0 right hsym hM1run hM1traj
    (fun k hk ck hck => absurd hk (Nat.not_lt_zero k))
  refine ⟨t₁ + 1 + 0, ?_, ?_, by omega⟩
  · have h := hneg.1
    rw [Compile.compareBodyTM_exitDone]
    simpa using h
  · intro k hk ck hck
    have hnh := hneg_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.compareBodyTM_exitDone_is_halt sc1 sc2) hnh,
           ClearGadget.ne_of_not_halting (Compile.compareBodyTM_exitLoop_is_halt sc1 sc2) hnh,
           hnh⟩

/-! ### The consume-loop abstract semantics + State iteration (bottom-up, Risk C2)

`matchLen l1 l2` is the number of matched leading pairs the consume loop peels
(the iteration count). `consumeStep` is `iterTailsTM`'s state transform (delete
both scratch heads). The lemmas below give the per-iteration matching facts
(`matchLen_step`), the terminal stopping disjunction (`matchLen_stop`), and the
closed-form register contents along the iteration (`consumeIter_spec`). -/

/-- Number of matched leading pairs peeled by the consume loop. -/
def Compile.matchLen : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: r1, b :: r2 => if a = b then Compile.matchLen r1 r2 + 1 else 0

/-- One consume-loop iteration on the abstract `State`: delete the heads of both
scratch registers. Matches `iterTailsTM`'s state transform. -/
def Compile.consumeStep (sc1 sc2 : Var) (s : State) : State :=
  (s.set sc1 (State.get s sc1).tail).set sc2 (State.get s sc2).tail

/-- For `j` below the matched-prefix length, both operands' `j`-suffixes are
nonempty and share the same first element. -/
theorem Compile.matchLen_step : ∀ (l1 l2 : List Nat) (j : Nat), j < Compile.matchLen l1 l2 →
    ∃ a cs1 cs2, l1.drop j = a :: cs1 ∧ l2.drop j = a :: cs2
  | [], l2, j, hj => by simp [Compile.matchLen] at hj
  | _ :: _, [], j, hj => by simp [Compile.matchLen] at hj
  | a :: r1, b :: r2, j, hj => by
      rw [Compile.matchLen] at hj
      by_cases hab : a = b
      · rw [if_pos hab] at hj
        cases j with
        | zero =>
            refine ⟨a, r1, r2, ?_, ?_⟩
            · simp
            · simp [hab]
        | succ j =>
            have hj' : j < Compile.matchLen r1 r2 := by omega
            obtain ⟨c, cs1, cs2, h1, h2⟩ := Compile.matchLen_step r1 r2 j hj'
            exact ⟨c, cs1, cs2, by simpa using h1, by simpa using h2⟩
      · rw [if_neg hab] at hj; omega

/-- At the matched-prefix length the consume loop stops: one operand's suffix is
empty, or both are nonempty with differing first elements. -/
theorem Compile.matchLen_stop : ∀ (l1 l2 : List Nat),
    l1.drop (Compile.matchLen l1 l2) = [] ∨ l2.drop (Compile.matchLen l1 l2) = [] ∨
    ∃ a cs1 b cs2, l1.drop (Compile.matchLen l1 l2) = a :: cs1 ∧
      l2.drop (Compile.matchLen l1 l2) = b :: cs2 ∧ a ≠ b
  | [], l2 => Or.inl rfl
  | _ :: _, [] => Or.inr (Or.inl rfl)
  | a :: r1, b :: r2 => by
      rw [Compile.matchLen]
      by_cases hab : a = b
      · rw [if_pos hab]
        rcases Compile.matchLen_stop r1 r2 with h | h | ⟨c, cs1, d, cs2, h1, h2, hcd⟩
        · exact Or.inl (by simpa using h)
        · exact Or.inr (Or.inl (by simpa using h))
        · exact Or.inr (Or.inr ⟨c, cs1, d, cs2, by simpa using h1, by simpa using h2, hcd⟩)
      · rw [if_neg hab]
        exact Or.inr (Or.inr ⟨a, r1, b, r2, by simp, by simp, hab⟩)

/-- **The consume-loop decision.** The two operands are equal iff BOTH their
`matchLen`-dropped suffixes are empty — exactly what the post-loop "both empty?"
verdict (`eqVerdictM`) tests. This is the TM-level analogue of
`EqBitProbe.eqVerdict_correct`; the verdict assembly (d2) consumes it. -/
theorem Compile.matchLen_drop_empty_iff : ∀ (l1 l2 : List Nat),
    (l1.drop (Compile.matchLen l1 l2) = [] ∧ l2.drop (Compile.matchLen l1 l2) = []) ↔ l1 = l2
  | [], [] => by simp [Compile.matchLen]
  | [], _ :: _ => by simp [Compile.matchLen]
  | _ :: _, [] => by simp [Compile.matchLen]
  | a :: r1, b :: r2 => by
      rw [Compile.matchLen]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, List.drop_succ_cons, List.drop_succ_cons,
            Compile.matchLen_drop_empty_iff r1 r2]
        simp
      · rw [if_neg hab]
        simp only [List.drop_zero]
        constructor
        · rintro ⟨h, _⟩; exact absurd h (List.cons_ne_nil _ _)
        · intro h; injection h with ha _; exact absurd ha hab

/-- Closed-form register contents along the consume iteration: after `k` steps the
two scratch registers hold the `k`-dropped originals; length and `BitState` are
preserved. -/
theorem Compile.consumeIter_spec (s : State) (sc1 sc2 : Var) (hne : sc1 ≠ sc2)
    (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length) (hbit : Compile.BitState s) (k : Nat) :
    State.get ((Compile.consumeStep sc1 sc2)^[k] s) sc1 = (State.get s sc1).drop k ∧
    State.get ((Compile.consumeStep sc1 sc2)^[k] s) sc2 = (State.get s sc2).drop k ∧
    ((Compile.consumeStep sc1 sc2)^[k] s).length = s.length ∧
    Compile.BitState ((Compile.consumeStep sc1 sc2)^[k] s) := by
  induction k with
  | zero =>
      simp only [Function.iterate_zero, id_eq, List.drop_zero]
      exact ⟨trivial, trivial, trivial, hbit⟩
  | succ k ih =>
      obtain ⟨ih1, ih2, ihlen, ihbit⟩ := ih
      set sk := (Compile.consumeStep sc1 sc2)^[k] s with hsk
      have hsc1' : sc1 < sk.length := by rw [ihlen]; exact hsc1
      have hsc2' : sc2 < sk.length := by rw [ihlen]; exact hsc2
      have hsc2X : sc2 < (sk.set sc1 (State.get sk sc1).tail).length := by
        rw [Compile.length_set _ _ _ hsc1']; exact hsc2'
      rw [Function.iterate_succ_apply']
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Compile.consumeStep, State.get_set_ne _ _ _ _ hne, State.get_set_eq, ih1, List.tail_drop]
      · rw [Compile.consumeStep, State.get_set_eq, ih2, List.tail_drop]
      · rw [Compile.consumeStep, Compile.length_set _ _ _ hsc2X, Compile.length_set _ _ _ hsc1', ihlen]
      · have hbitX : Compile.BitState (sk.set sc1 (State.get sk sc1).tail) :=
          Compile.BitState_set_tail sk sc1 ihbit hsc1'
        have hgetX : State.get (sk.set sc1 (State.get sk sc1).tail) sc2 = State.get sk sc2 :=
          State.get_set_ne sk sc1 _ sc2 (Ne.symm hne)
        rw [Compile.consumeStep, ← hgetX]
        exact Compile.BitState_set_tail (sk.set sc1 (State.get sk sc1).tail) sc2 hbitX hsc2X

/-- `matchLen` is at most the length of the first operand (it peels at most one
matched pair per cell of `l1`). Gives `n = matchLen ≤ |g1| ≤ L` for the loop's
quadratic step bound. -/
theorem Compile.matchLen_le_left : ∀ (l1 l2 : List Nat), Compile.matchLen l1 l2 ≤ l1.length
  | [], _ => by simp [Compile.matchLen]
  | _ :: _, [] => by simp [Compile.matchLen]
  | a :: r1, b :: r2 => by
      rw [Compile.matchLen]
      split
      · have ih := Compile.matchLen_le_left r1 r2
        simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

/-- `matchLen` is also at most the length of the SECOND operand (each matched pair
peels one cell off both). The symmetric companion of `matchLen_le_left`; together
they give `2·matchLen + |g1.drop n| + |g2.drop n| = |g1| + |g2|` (the exact residue
length the eqBit W-invariant needs). -/
theorem Compile.matchLen_le_right : ∀ (l1 l2 : List Nat), Compile.matchLen l1 l2 ≤ l2.length
  | [], _ => by simp [Compile.matchLen]
  | _ :: _, [] => by simp [Compile.matchLen]
  | a :: r1, b :: r2 => by
      rw [Compile.matchLen]
      split
      · have ih := Compile.matchLen_le_right r1 r2
        simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

/-- **Loop tape-length invariance (eqBit d2-iv).** Within the matched prefix
(`m ≤ matchLen`) both scratch heads are nonempty, so each `consumeStep` deletes
exactly one cell from each of `sc1`/`sc2` — the encoded-tape length shrinks by
`2` per step. The loop's residue grows by `2` in lock-step (`T m` carries
`replicate (2·(n−m)) 0`), so the total loop tape length is invariant `= L`. This
is the keystone fact the `compareLoop_run` quadratic step bound needs (uniform
`M_body` across iterations). -/
theorem Compile.encodeTape_consumeStep_length (s : State) (sc1 sc2 : Var)
    (hne : sc1 ≠ sc2) (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length)
    (hbit : Compile.BitState s) :
    ∀ m, m ≤ Compile.matchLen (State.get s sc1) (State.get s sc2) →
      (Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[m] s)).length + 2 * m
        = (Compile.encodeTape s).length := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hm
      have hm' := ih (by omega)
      obtain ⟨hsp1, hsp2, hsplen, hspbit⟩ := Compile.consumeIter_spec s sc1 sc2 hne hsc1 hsc2 hbit m
      have hm_lt : m < Compile.matchLen (State.get s sc1) (State.get s sc2) := by omega
      obtain ⟨a, cs1, cs2, hd1, hd2⟩ :=
        Compile.matchLen_step (State.get s sc1) (State.get s sc2) m hm_lt
      set sm := (Compile.consumeStep sc1 sc2)^[m] s with hsm
      have hg1 : State.get sm sc1 = a :: cs1 := by rw [hsp1]; exact hd1
      have hg2 : State.get sm sc2 = a :: cs2 := by rw [hsp2]; exact hd2
      have hsc1m : sc1 < sm.length := by rw [hsplen]; exact hsc1
      have hbal1 := Compile.encodeTape_set_length sm sc1 (State.get sm sc1).tail hsc1m
      set s1 := sm.set sc1 (State.get sm sc1).tail with hs1
      have hsc2m1 : sc2 < s1.length := by rw [hs1, Compile.length_set _ _ _ hsc1m, hsplen]; exact hsc2
      have hget21 : State.get s1 sc2 = State.get sm sc2 :=
        State.get_set_ne sm sc1 _ sc2 (Ne.symm hne)
      have hbal2 := Compile.encodeTape_set_length s1 sc2 (State.get sm sc2).tail hsc2m1
      have htail1 : (State.get sm sc1).length = (State.get sm sc1).tail.length + 1 := by
        rw [hg1]; simp
      have htail2 : (State.get sm sc2).length = (State.get sm sc2).tail.length + 1 := by
        rw [hg2]; simp
      have hget21len : (State.get s1 sc2).length = (State.get sm sc2).length := by rw [hget21]
      have hstep : (Compile.consumeStep sc1 sc2)^[m + 1] s = s1.set sc2 (State.get sm sc2).tail := by
        rw [Function.iterate_succ_apply', ← hsm]
        simp only [Compile.consumeStep, ← hs1]
      rw [hstep]
      omega

/-! ### `compareLoopTM` — the `eqBit` consume loop (bottom-up, Risk C2 — d2a)

The counted loop over `compareBodyTM`: ITER (delete both heads) while both scratch
regs are nonempty with matching first bits, DONE otherwise. After
`matchLen (s.get sc1) (s.get sc2)` iterations the two registers hold the operands'
suffixes (`consumeLoop`'s residue); the post-loop "both empty?" verdict
(`eqVerdictM`, proven) then decides equality. -/

/-- **The consume loop runs to completion.** From `encodeTape s ++ res` at head `0`
(with `sc1 ≠ sc2` both bit-registers), the loop consumes the matched common prefix
of the two scratch registers and halts (at `compareBodyTM.states`) with the two
registers holding their `matchLen`-dropped suffixes (residue extended by the
per-iteration `[0,0]` fillers). -/
theorem Compile.compareLoop_run (s : State) (sc1 sc2 : Var) (hne : sc1 ≠ sc2)
    (hsc1 : sc1 < s.length) (hsc2 : sc2 < s.length) (hbit : Compile.BitState s)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.compareLoopTM sc1 sc2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := (Compile.compareBodyTM sc1 sc2).states,
                 tapes := [([], 0,
                   Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[Compile.matchLen (State.get s sc1) (State.get s sc2)] s)
                     ++ (res ++ List.replicate (2 * Compile.matchLen (State.get s sc1) (State.get s sc2)) 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.compareLoopTM sc1 sc2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.compareLoopTM sc1 sc2) ck = false)
    ∧ t ≤ (Compile.matchLen (State.get s sc1) (State.get s sc2) + 1)
            * (24 * (Compile.encodeTape s ++ res).length + 45) := by
  set n := Compile.matchLen (State.get s sc1) (State.get s sc2) with hn
  set T : Nat → (List Nat × Nat × List Nat) := fun m =>
    ([], 0, Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n - m] s)
      ++ (res ++ List.replicate (2 * (n - m)) 0)) with hTdef
  -- The tape head always reads the leading sentinel `3 < 4 = sig`.
  have hT_sym : ∀ m v, currentTapeSymbol (T m) = some v → v < (Compile.compareBodyTM sc1 sc2).sig := by
    intro m v hv
    rw [Compile.compareBodyTM_sig]
    simp only [hTdef] at hv
    have hLpos : 0 < (Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n - m] s)).length := by
      rw [Compile.encodeTape]; simp
    have hlt : (0 : Nat) < (Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n - m] s)
        ++ (res ++ List.replicate (2 * (n - m)) 0)).length := by rw [List.length_append]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have h0 : (Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n - m] s)
        ++ (res ++ List.replicate (2 * (n - m)) 0))[0]? = some 3 := by
      rw [List.getElem?_append_left hLpos, Compile.encodeTape]; rfl
    have hhead : (Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n - m] s)
        ++ (res ++ List.replicate (2 * (n - m)) 0)).get ⟨0, hlt⟩ = 3 := by
      rw [List.get_eq_getElem]
      exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans h0)
    have hv3 : v = 3 := by rw [← Option.some.inj hv]; exact hhead
    omega
  -- Per-iteration body contract (existence form, for `choose`).
  have hiter_ex : ∀ j, ∃ tj, j < n →
      runFlatTM tj (Compile.compareBodyTM sc1 sc2)
          { state_idx := (Compile.compareBodyTM sc1 sc2).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.compareBodyTM_exitLoop sc1 sc2, tapes := [T j] }
      ∧ (∀ k, k < tj → ∀ ck,
          runFlatTM k (Compile.compareBodyTM sc1 sc2)
              { state_idx := (Compile.compareBodyTM sc1 sc2).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ Compile.compareBodyTM_exitDone sc1 sc2 ∧
          ck.state_idx ≠ Compile.compareBodyTM_exitLoop sc1 sc2 ∧
          haltingStateReached (Compile.compareBodyTM sc1 sc2) ck = false)
      ∧ tj ≤ 24 * (Compile.encodeTape s ++ res).length + 44 := by
    intro j
    by_cases hj : j < n
    · obtain ⟨hspec1, hspec2, hspeclen, hspecbit⟩ :=
        Compile.consumeIter_spec s sc1 sc2 hne hsc1 hsc2 hbit (n - (j + 1))
      have hidx : n - (j + 1) < n := by omega
      obtain ⟨a, cs1, cs2, hd1, hd2⟩ :=
        Compile.matchLen_step (State.get s sc1) (State.get s sc2) (n - (j + 1)) hidx
      have hg1 : State.get ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s) sc1 = a :: cs1 := by
        rw [hspec1]; exact hd1
      have hg2 : State.get ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s) sc2 = a :: cs2 := by
        rw [hspec2]; exact hd2
      have hsc1' : sc1 < ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s).length := by
        rw [hspeclen]; exact hsc1
      have hsc2' : sc2 < ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s).length := by
        rw [hspeclen]; exact hsc2
      have hmem1 : State.get ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s) sc1
          ∈ (Compile.consumeStep sc1 sc2)^[n - (j + 1)] s := by
        rw [State.get, List.getElem?_eq_getElem hsc1']; exact List.getElem_mem hsc1'
      have ha : a ≤ 1 := hspecbit _ hmem1 a (by rw [hg1]; exact List.mem_cons_self)
      have hres' : Compile.ValidResidue (res ++ List.replicate (2 * (n - (j + 1))) 0) :=
        Compile.ValidResidue_append_replicate_zero res _ hres
      obtain ⟨tj, hrun, htraj, hbnd⟩ :=
        Compile.compareBody_iterate_run ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s) sc1 sc2
          (res ++ List.replicate (2 * (n - (j + 1))) 0) a a cs1 cs2 hg1 hg2 ha ha rfl hne
          hsc1' hsc2' hspecbit hres'
      -- rewrite the iterate tape length `|T (j+1)|` to the invariant `L` (the
      -- consume-loop tape-length invariance keystone).
      have hinv := Compile.encodeTape_consumeStep_length s sc1 sc2 hne hsc1 hsc2 hbit (n - (j + 1))
        (le_trans (Nat.sub_le n (j + 1)) (le_of_eq hn))
      have htape_len : (Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s)
          ++ (res ++ List.replicate (2 * (n - (j + 1))) 0)).length
          = (Compile.encodeTape s ++ res).length := by
        simp only [List.length_append, List.length_replicate]
        omega
      rw [htape_len] at hbnd
      have hstate_eq : (Compile.consumeStep sc1 sc2)^[n - j] s
          = (((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s).set sc1
                (State.get ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s) sc1).tail).set sc2
                (State.get ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s) sc2).tail := by
        rw [show n - j = (n - (j + 1)) + 1 from by omega, Function.iterate_succ_apply']
        rfl
      have hres_eq : res ++ List.replicate (2 * (n - j)) 0
          = (res ++ List.replicate (2 * (n - (j + 1))) 0) ++ [0, 0] := by
        rw [List.append_assoc, show ([0, 0] : List Nat) = List.replicate 2 0 from rfl,
            ← List.replicate_add, show 2 * (n - (j + 1)) + 2 = 2 * (n - j) from by omega]
      have hgoal_start : T (j + 1) = ([], 0,
          Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s)
            ++ (res ++ List.replicate (2 * (n - (j + 1))) 0)) := by simp only [hTdef]
      have hgoal_end : T j = ([], 0,
          Compile.encodeTape ((((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s).set sc1
                (State.get ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s) sc1).tail).set sc2
                (State.get ((Compile.consumeStep sc1 sc2)^[n - (j + 1)] s) sc2).tail)
            ++ ((res ++ List.replicate (2 * (n - (j + 1))) 0) ++ [0, 0])) := by
        simp only [hTdef]; rw [hstate_eq, hres_eq]
      refine ⟨tj, fun _ => ⟨?_, ?_, hbnd⟩⟩
      · rw [Compile.compareBodyTM_start, hgoal_start, hgoal_end]; exact hrun
      · intro k hk ck hck
        rw [Compile.compareBodyTM_start, hgoal_start] at hck
        exact htraj k hk ck hck
    · exact ⟨0, fun h => absurd h hj⟩
  choose tIter hIter using hiter_ex
  -- Terminal DONE body contract at `T 0` (dispatch the three stopping cases).
  have hdone : ∃ tD,
      runFlatTM tD (Compile.compareBodyTM sc1 sc2)
          { state_idx := (Compile.compareBodyTM sc1 sc2).start, tapes := [T 0] }
        = some { state_idx := Compile.compareBodyTM_exitDone sc1 sc2, tapes := [T 0] }
      ∧ (∀ k, k < tD → ∀ ck,
          runFlatTM k (Compile.compareBodyTM sc1 sc2)
              { state_idx := (Compile.compareBodyTM sc1 sc2).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ Compile.compareBodyTM_exitDone sc1 sc2 ∧
          ck.state_idx ≠ Compile.compareBodyTM_exitLoop sc1 sc2 ∧
          haltingStateReached (Compile.compareBodyTM sc1 sc2) ck = false)
      ∧ tD ≤ 12 * (Compile.encodeTape s ++ res).length + 15 := by
    obtain ⟨hsp1, hsp2, hsplen, hspbit⟩ := Compile.consumeIter_spec s sc1 sc2 hne hsc1 hsc2 hbit n
    have hsc1n : sc1 < ((Compile.consumeStep sc1 sc2)^[n] s).length := by rw [hsplen]; exact hsc1
    have hsc2n : sc2 < ((Compile.consumeStep sc1 sc2)^[n] s).length := by rw [hsplen]; exact hsc2
    have hresn : Compile.ValidResidue (res ++ List.replicate (2 * n) 0) :=
      Compile.ValidResidue_append_replicate_zero res _ hres
    have hT0 : T 0 = ([], 0,
        Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n] s)
          ++ (res ++ List.replicate (2 * n) 0)) := by simp only [hTdef, Nat.sub_zero]
    have hsym0 := Compile.compareBody_symMax ((Compile.consumeStep sc1 sc2)^[n] s) sc1 sc2
      (res ++ List.replicate (2 * n) 0) hspbit
    obtain ⟨tT, htmrun, htmtraj, htTle⟩ : ∃ tT,
        runFlatTM tT (Compile.testMachine sc1 sc2)
            { state_idx := 0, tapes := [([], 0,
              Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n] s)
                ++ (res ++ List.replicate (2 * n) 0))] }
          = some { state_idx := Compile.testMachine_exit_done sc1 sc2,
                   tapes := [([], 0,
                     Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n] s)
                       ++ (res ++ List.replicate (2 * n) 0))] }
        ∧ (∀ k, k < tT → ∀ ck,
            runFlatTM k (Compile.testMachine sc1 sc2)
                { state_idx := 0, tapes := [([], 0,
                  Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n] s)
                    ++ (res ++ List.replicate (2 * n) 0))] } = some ck →
            ck.state_idx ≠ Compile.testMachine_exit_iter sc1 sc2 ∧
            ck.state_idx ≠ Compile.testMachine_exit_done sc1 sc2 ∧
            haltingStateReached (Compile.testMachine sc1 sc2) ck = false)
        ∧ tT ≤ 12 * (Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n] s)
                      ++ (res ++ List.replicate (2 * n) 0)).length + 14 := by
      rcases Compile.matchLen_stop (State.get s sc1) (State.get s sc2) with
        hstop | hstop | ⟨a, cs1, b, cs2, hda, hdb, hab⟩
      · have hempty1 : State.get ((Compile.consumeStep sc1 sc2)^[n] s) sc1 = [] := by
          rw [hsp1, hn]; exact hstop
        exact Compile.testMachine_run_done_left ((Compile.consumeStep sc1 sc2)^[n] s) sc1 sc2
          (res ++ List.replicate (2 * n) 0) hspbit hsc1n hempty1 hresn
      · by_cases he1 : State.get ((Compile.consumeStep sc1 sc2)^[n] s) sc1 = []
        · exact Compile.testMachine_run_done_left ((Compile.consumeStep sc1 sc2)^[n] s) sc1 sc2
            (res ++ List.replicate (2 * n) 0) hspbit hsc1n he1 hresn
        · have hempty2 : State.get ((Compile.consumeStep sc1 sc2)^[n] s) sc2 = [] := by
            rw [hsp2, hn]; exact hstop
          exact Compile.testMachine_run_done_right ((Compile.consumeStep sc1 sc2)^[n] s) sc1 sc2
            (res ++ List.replicate (2 * n) 0) hspbit hsc1n hsc2n he1 hempty2 hresn
      · have hgc1 : State.get ((Compile.consumeStep sc1 sc2)^[n] s) sc1 = a :: cs1 := by
          rw [hsp1, hn]; exact hda
        have hgc2 : State.get ((Compile.consumeStep sc1 sc2)^[n] s) sc2 = b :: cs2 := by
          rw [hsp2, hn]; exact hdb
        have hamem : State.get ((Compile.consumeStep sc1 sc2)^[n] s) sc1
            ∈ (Compile.consumeStep sc1 sc2)^[n] s := by
          rw [State.get, List.getElem?_eq_getElem hsc1n]; exact List.getElem_mem hsc1n
        have hbmem : State.get ((Compile.consumeStep sc1 sc2)^[n] s) sc2
            ∈ (Compile.consumeStep sc1 sc2)^[n] s := by
          rw [State.get, List.getElem?_eq_getElem hsc2n]; exact List.getElem_mem hsc2n
        have ha : a ≤ 1 := hspbit _ hamem a (by rw [hgc1]; exact List.mem_cons_self)
        have hb : b ≤ 1 := hspbit _ hbmem b (by rw [hgc2]; exact List.mem_cons_self)
        exact Compile.testMachine_run_done_neq ((Compile.consumeStep sc1 sc2)^[n] s) sc1 sc2
          (res ++ List.replicate (2 * n) 0) a b cs1 cs2 hgc1 hgc2 ha hb hab hsc1n hsc2n hspbit hresn
    obtain ⟨tD, hdrun, hdtraj, hdbnd⟩ := Compile.compareBody_done_run sc1 sc2
      (Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n] s) ++ (res ++ List.replicate (2 * n) 0))
      hsym0 htmrun htmtraj htTle
    -- rewrite the done-tape length `|T 0|` to `L` (invariance at `m = n`).
    have hinvn := Compile.encodeTape_consumeStep_length s sc1 sc2 hne hsc1 hsc2 hbit n (le_of_eq hn)
    have hrlen : (Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n] s)
        ++ (res ++ List.replicate (2 * n) 0)).length = (Compile.encodeTape s ++ res).length := by
      simp only [List.length_append, List.length_replicate]
      omega
    rw [hrlen] at hdbnd
    refine ⟨tD, ?_, ?_, hdbnd⟩
    · rw [Compile.compareBodyTM_start, hT0]; exact hdrun
    · intro k hk ck hck
      rw [Compile.compareBodyTM_start, hT0] at hck
      exact hdtraj k hk ck hck
  -- Assemble via `loopTM_run`.
  obtain ⟨tDone, hdone_run, hdone_traj, hdone_bnd⟩ := hdone
  -- the loop-run lemmas consume the bare (run ∧ traj) iteration contract.
  have hIter' : ∀ j, j < n →
      runFlatTM (tIter j) (Compile.compareBodyTM sc1 sc2)
          { state_idx := (Compile.compareBodyTM sc1 sc2).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.compareBodyTM_exitLoop sc1 sc2, tapes := [T j] }
      ∧ (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (Compile.compareBodyTM sc1 sc2)
              { state_idx := (Compile.compareBodyTM sc1 sc2).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ Compile.compareBodyTM_exitDone sc1 sc2 ∧
          ck.state_idx ≠ Compile.compareBodyTM_exitLoop sc1 sc2 ∧
          haltingStateReached (Compile.compareBodyTM sc1 sc2) ck = false) :=
    fun j hj => ⟨(hIter j hj).1, (hIter j hj).2.1⟩
  have hmain := loopTM_run (Compile.compareBodyTM sc1 sc2) (Compile.compareBodyTM_exitDone sc1 sc2)
    (Compile.compareBodyTM_exitLoop sc1 sc2)
    (Compile.compareBodyTM_valid sc1 sc2) (Compile.compareBodyTM_exitDone_lt sc1 sc2)
    (Compile.compareBodyTM_exitLoop_lt sc1 sc2) (Compile.compareBodyTM_exitDone_ne_exitLoop sc1 sc2)
    T hT_sym tIter tDone ⟨hdone_run, hdone_traj⟩ n hIter'
  have hneh := loopTM_no_early_halt (Compile.compareBodyTM sc1 sc2) (Compile.compareBodyTM_exitDone sc1 sc2)
    (Compile.compareBodyTM_exitLoop sc1 sc2)
    (Compile.compareBodyTM_valid sc1 sc2) (Compile.compareBodyTM_exitDone_lt sc1 sc2)
    (Compile.compareBodyTM_exitLoop_lt sc1 sc2) (Compile.compareBodyTM_exitDone_ne_exitLoop sc1 sc2)
    T hT_sym tIter tDone ⟨hdone_run, hdone_traj⟩ n hIter'
  have hTn : T n = ([], 0, Compile.encodeTape s ++ res) := by
    simp only [hTdef, Nat.sub_self, Function.iterate_zero, id_eq, Nat.mul_zero, List.replicate_zero,
      List.append_nil]
  have hT0' : T 0 = ([], 0,
      Compile.encodeTape ((Compile.consumeStep sc1 sc2)^[n] s) ++ (res ++ List.replicate (2 * n) 0)) := by
    simp only [hTdef, Nat.sub_zero]
  -- budget: `loopBudget ≤ (n+1)·(24L+45) ≤ 24L²+69L+45` (every loop tape has length
  -- `L`, `n = matchLen ≤ |g1| ≤ L`).
  have h_iter_bnd : ∀ j, j < n →
      tIter j + 1 ≤ 24 * (Compile.encodeTape s ++ res).length + 45 :=
    fun j hj => by have := (hIter j hj).2.2; omega
  have h_done_bnd : tDone + 1 ≤ 24 * (Compile.encodeTape s ++ res).length + 45 := by omega
  refine ⟨loopBudget tIter tDone n, ?_, ?_, ?_⟩
  · rw [Compile.compareBodyTM_start, hTn, hT0'] at hmain
    rw [Compile.compareLoopTM]
    exact hmain
  · rw [Compile.compareBodyTM_start, hTn] at hneh
    rw [Compile.compareLoopTM]
    exact hneh
  · -- `loopBudget ≤ (matchLen+1)·(24·L+45)` directly (kept iteration-explicit: the
    -- assembly bounds `matchLen ≤ |g1| ≤ op-input-L`, while the loop tape `L` is the
    -- ~3× grown working tape — collapsing `matchLen → L` here busts the op budget).
    exact Compile.loopBudget_le tIter tDone
      (24 * (Compile.encodeTape s ++ res).length + 45) n h_done_bnd h_iter_bnd

/-- State extensionality from per-register reads + equal length. -/
theorem State.ext_of_get {s t : State} (hlen : s.length = t.length)
    (h : ∀ r, State.get s r = State.get t r) : s = t := by
  apply List.ext_getElem hlen
  intro r h1 h2
  have hr := h r
  rw [State.get, List.getElem?_eq_getElem h1, Option.getD_some] at hr
  rw [State.get, List.getElem?_eq_getElem h2, Option.getD_some] at hr
  exact hr

/-! ### `eqBit` no-grow run stack (relocated above the per-op contract so its
`eqBit` case can consume `opEqBitNG_run` — HANDOFF bottom-up Task 1(C)). -/
/-- **`copyEmptyRawTM` run lemma (TIGHT budget).** From `encodeTape s ++ res` at
head `0` with `dst` an EMPTY register, copies `src`'s content into `dst`
(non-destructive on `src`), rewinds head to `0`, residue unchanged. The step
count is the TIGHT `copyLoop_run` budget `(|src|+1)(5L+23)` plus `O(L)` for the
navigate and rewind — the reason the `compareRegsTM` scratch copies use this,
not `opCopy_run`. -/
theorem Compile.copyEmpty_run (s : State) (dst src : Var) (hne : dst ≠ src)
    (hdst : dst < s.length) (hsrc : src < s.length)
    (hbit : Compile.BitState s) (hdst_empty : State.get s dst = [])
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.copyEmptyRawTM dst src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.copyEmptyRawTM_exit dst src,
                 tapes := [([], 0, Compile.encodeTape (s.set dst (State.get s src)) ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.copyEmptyRawTM dst src)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.copyEmptyRawTM_exit dst src ∧
        haltingStateReached (Compile.copyEmptyRawTM dst src) ck = false)
    ∧ t ≤ ((State.get s src).length + 1)
            * (5 * (Compile.encodeTape (s.set dst (State.get s src)) ++ res).length + 23)
          + 3 * (Compile.encodeTape (s.set dst (State.get s src)) ++ res).length + 4 := by
  -- ### shared facts about the (unset) source register
  have hbit₂ : Compile.BitState (s.set dst (State.get s src)) :=
    Compile.BitState_set s dst _ hbit hdst (by
      intro x hx
      have hmem : State.get s src ∈ s := by
        rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
      exact hbit _ hmem x hx)
  have hs₂_len : (s.set dst (State.get s src)).length = s.length :=
    Compile.length_set s dst _ hdst
  have hsrc₂ : src < (s.set dst (State.get s src)).length := by rw [hs₂_len]; exact hsrc
  have hget₂_src : State.get (s.set dst (State.get s src)) src = State.get s src :=
    Compile.get_set_ne s dst _ src hdst (Ne.symm hne)
  -- ### phase 1: navigate to `src` (on the input tape; `dst` already empty)
  have hsk_len : ((List.take src s).map Compile.shiftReg).length = src :=
    Compile.skipped_length s src hsrc
  have hsk_ok : ∀ b ∈ (List.take src s).map Compile.shiftReg,
      (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := Compile.skipped_ok s src hbit
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks ((List.take src s).map Compile.shiftReg)
        ++ (Compile.shiftReg (State.get s src)
            ++ 0 :: (Compile.encodeRegs (List.drop (src + 1) s) ++ [Compile.endMark] ++ res))) := by
    have hsplit := Compile.encodeTape_split s src hsrc
    rw [Compile.encodeTape, List.cons_append, ← hsplit]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hnav_run := ClearGadget.navigateToRegTM_run
    ((List.take src s).map Compile.shiftReg)
    (Compile.shiftReg (State.get s src)
      ++ 0 :: (Compile.encodeRegs (List.drop (src + 1) s) ++ [Compile.endMark] ++ res)) hsk_ok
  have hnav_traj := ClearGadget.navigateToRegTM_no_early_halt
    ((List.take src s).map Compile.shiftReg)
    (Compile.shiftReg (State.get s src)
      ++ 0 :: (Compile.encodeRegs (List.drop (src + 1) s) ++ [Compile.endMark] ++ res)) hsk_ok
  rw [hsk_len, ← hdecomp, Compile.regBlocks_map_shiftReg] at hnav_run
  rw [hsk_len, ← hdecomp] at hnav_traj
  -- ### phase 2: the cursor loop
  obtain ⟨tl, hloop_run, hloop_traj, hloop_le⟩ :=
    Compile.copyLoop_run s dst src hne hdst hsrc hbit hdst_empty res hres
  -- ### phase 3: the final rewind (`justRewindTM` = scanLeftUntilTM 4 3)
  have hHF2 : 1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
        + (State.get s src).length + 2
      ≤ (Compile.encodeTape (s.set dst (State.get s src))).length := by
    have hdec := congrArg List.length
      (Compile.encodeTape_reg_decomp_at (s.set dst (State.get s src)) src hsrc₂).2
    rw [hget₂_src] at hdec
    simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map,
      List.length_nil] at hdec
    omega
  have hTF_lt4 : ∀ x ∈ Compile.encodeTape (s.set dst (State.get s src)) ++ res, x < 4 :=
    Compile.encodeTape_append_res_lt_four _ _ hbit₂ hres
  have h0F : 0 < (Compile.encodeTape (s.set dst (State.get s src)) ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length]; omega
  have htargetF : (Compile.encodeTape (s.set dst (State.get s src)) ++ res).get ⟨0, h0F⟩ = 3 := by
    have hkey : (Compile.encodeTape (s.set dst (State.get s src)) ++ res)[0]? = some 3 := by
      rw [Compile.encodeTape]; rfl
    rw [List.get_eq_getElem]
    exact Option.some_inj.mp ((List.getElem?_eq_getElem h0F).symm.trans hkey)
  have hcellsF : ∀ i, 0 < i →
      i ≤ 1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
        + (State.get s src).length →
      ∃ (h : i < (Compile.encodeTape (s.set dst (State.get s src)) ++ res).length),
        (Compile.encodeTape (s.set dst (State.get s src)) ++ res).get ⟨i, h⟩ < 4 ∧
        (Compile.encodeTape (s.set dst (State.get s src)) ++ res).get ⟨i, h⟩ ≠ 3 := by
    intro i hi0 hile
    have hi1 : i + 1 < (Compile.encodeTape (s.set dst (State.get s src))).length := by omega
    have hlt : i < (Compile.encodeTape (s.set dst (State.get s src)) ++ res).length := by
      rw [List.length_append]; omega
    refine ⟨hlt, ?_⟩
    have hilt_e : i < (Compile.encodeTape (s.set dst (State.get s src))).length := by omega
    have hkey : (Compile.encodeTape (s.set dst (State.get s src)) ++ res)[i]?
        = some ((Compile.encodeTape (s.set dst (State.get s src))).get ⟨i, hilt_e⟩) := by
      rw [List.getElem?_append_left hilt_e, List.getElem?_eq_getElem hilt_e, List.get_eq_getElem]
    have hgeteq : (Compile.encodeTape (s.set dst (State.get s src)) ++ res).get ⟨i, hlt⟩
        = (Compile.encodeTape (s.set dst (State.get s src))).get ⟨i, hilt_e⟩ := by
      rw [List.get_eq_getElem]
      exact Option.some_inj.mp ((List.getElem?_eq_getElem hlt).symm.trans hkey)
    rw [hgeteq]
    obtain ⟨hi', hne3⟩ := Compile.encodeTape_interior_ne_endMark _ hbit₂ i hi0 hi1
    exact ⟨Compile.encodeTape_lt_four _ hbit₂ _ (List.get_mem _ _), hne3⟩
  have hrew_run := ScanLeft.scanLeft_run 4 3 []
    (Compile.encodeTape (s.set dst (State.get s src)) ++ res) h0F htargetF
    (1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
      + (State.get s src).length)
    (by rw [List.length_append]; omega) hcellsF
  have hrew_traj := ScanLeft.scanLeft_no_early_halt 4 3 []
    (Compile.encodeTape (s.set dst (State.get s src)) ++ res)
    (1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
      + (State.get s src).length)
    (by rw [List.length_append]; omega) hcellsF
  -- ### level B: navigate ⨾ copy loop
  have hT_lt4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 :=
    Compile.encodeTape_append_res_lt_four _ _ hbit hres
  have hloopexit_halt : (Compile.copyLoopTM dst).halt[Compile.copyLoopTM_exit dst]? = some true := by
    show (List.replicate (Compile.copyBodyTM dst).states false
        ++ [true])[Compile.copyLoopTM_exit dst]? = some true
    rw [show Compile.copyLoopTM_exit dst = (Compile.copyBodyTM dst).states from by
          rw [Compile.copyBodyTM_states]; rfl,
        List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  have hsymB : ∀ v, currentTapeSymbol
      ([], 1 + (Compile.encodeRegs (List.take src s)).length, Compile.encodeTape s ++ res)
        = some v →
      v < max (ClearGadget.navigateToRegTM src).sig (Compile.copyLoopTM dst).sig := by
    intro v hv
    rw [show max (ClearGadget.navigateToRegTM src).sig (Compile.copyLoopTM dst).sig = 4
      from by rw [ClearGadget.navigateToRegTM_sig, Compile.copyLoopTM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hT_lt4 _ v hv
  have hBrun := composeFlatTM_run
    (ClearGadget.navigateToRegTM_valid src) (Compile.copyLoopTM_valid dst)
    (ClearGadget.navigateToRegTM_exit_lt src)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    (by show (0 : Nat) < (ClearGadget.navigateToRegTM src).states
        rw [ClearGadget.navigateToRegTM_states]; omega)
    [] (1 + (Compile.encodeRegs (List.take src s)).length) (Compile.encodeTape s ++ res)
    hsymB hnav_run
    (fun k hk ck hck => by
      have hh := hnav_traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateToRegTM_exit_is_halt src) hh, hh⟩)
    hloop_run (Compile.haltingStateReached_of_halt hloopexit_halt)
  have hBtraj := composeFlatTM_no_early_halt
    (ClearGadget.navigateToRegTM_valid src) (Compile.copyLoopTM_valid dst)
    (ClearGadget.navigateToRegTM_exit_lt src)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    (by show (0 : Nat) < (ClearGadget.navigateToRegTM src).states
        rw [ClearGadget.navigateToRegTM_states]; omega)
    [] (1 + (Compile.encodeRegs (List.take src s)).length) (Compile.encodeTape s ++ res)
    hsymB hnav_run
    (fun k hk ck hck => by
      have hh := hnav_traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateToRegTM_exit_is_halt src) hh, hh⟩)
    (fun k hk ck hck => (hloop_traj k hk ck hck).2)
  have hBhalt := Compile.composeFlatTM_halt_intro (ClearGadget.navigateToRegTM src)
    (Compile.copyLoopTM dst) (Compile.copyLoopTM_exit dst)
    (ClearGadget.navigateToRegTM_exit src) hloopexit_halt
  have heqB : Compile.copyLoopTM_exit dst + (ClearGadget.navigateToRegTM src).states
      = (2 + 3 * src) + (55 + 6 * dst) := by
    rw [ClearGadget.navigateToRegTM_states]
    show (55 + 6 * dst : Nat) + (2 + 3 * src) = _; omega
  rw [heqB] at hBrun
  rw [Nat.add_comm (ClearGadget.navigateToRegTM src).states (Compile.copyLoopTM_exit dst),
      heqB] at hBhalt
  -- ### level C: ⨾ the final rewind
  have hsymC : ∀ v, currentTapeSymbol
      ([], 1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
        + (State.get s src).length, Compile.encodeTape (s.set dst (State.get s src)) ++ res)
        = some v →
      v < max (composeFlatTM (ClearGadget.navigateToRegTM src) (Compile.copyLoopTM dst)
          (ClearGadget.navigateToRegTM_exit src)).sig ClearGadget.justRewindTM.sig := by
    intro v hv
    rw [show max (composeFlatTM (ClearGadget.navigateToRegTM src) (Compile.copyLoopTM dst)
          (ClearGadget.navigateToRegTM_exit src)).sig ClearGadget.justRewindTM.sig = 4
      from by
      show max (max (ClearGadget.navigateToRegTM src).sig (Compile.copyLoopTM dst).sig)
        ClearGadget.justRewindTM.sig = 4
      rw [ClearGadget.navigateToRegTM_sig, Compile.copyLoopTM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hTF_lt4 _ v hv
  have hexC_lt : (2 + 3 * src) + (55 + 6 * dst)
      < (composeFlatTM (ClearGadget.navigateToRegTM src) (Compile.copyLoopTM dst)
          (ClearGadget.navigateToRegTM_exit src)).states := by
    rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states src,
        Compile.copyLoopTM_states dst]
    simp only [Var]; omega
  have hCrun := composeFlatTM_run
    (composeFlatTM_valid _ _ _ (ClearGadget.navigateToRegTM_valid src)
      (Compile.copyLoopTM_valid dst) (ClearGadget.navigateToRegTM_exit_lt src)
      (ClearGadget.navigateToRegTM_tapes src) (Compile.copyLoopTM_tapes dst))
    ClearGadget.justRewindTM_valid hexC_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    (by show (0 : Nat) < (composeFlatTM _ _ _).states
        rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states]; omega)
    [] (1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
      + (State.get s src).length)
    (Compile.encodeTape (s.set dst (State.get s src)) ++ res)
    hsymC hBrun.1
    (fun k hk ck hck => by
      have hh := hBtraj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hBhalt hh, hh⟩)
    hrew_run rfl
  have hCtraj := composeFlatTM_no_early_halt
    (composeFlatTM_valid _ _ _ (ClearGadget.navigateToRegTM_valid src)
      (Compile.copyLoopTM_valid dst) (ClearGadget.navigateToRegTM_exit_lt src)
      (ClearGadget.navigateToRegTM_tapes src) (Compile.copyLoopTM_tapes dst))
    ClearGadget.justRewindTM_valid hexC_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    (by show (0 : Nat) < (composeFlatTM _ _ _).states
        rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states]; omega)
    [] (1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
      + (State.get s src).length)
    (Compile.encodeTape (s.set dst (State.get s src)) ++ res)
    hsymC hBrun.1
    (fun k hk ck hck => by
      have hh := hBtraj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hBhalt hh, hh⟩)
    (fun k hk ck hck => (hrew_traj k hk ck hck).2)
  -- ### conclude: state, tape, trajectory
  have hstate_eq : (1 : Nat) + (composeFlatTM (ClearGadget.navigateToRegTM src)
        (Compile.copyLoopTM dst) (ClearGadget.navigateToRegTM_exit src)).states
      = Compile.copyEmptyRawTM_exit dst src := by
    rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states, Compile.copyLoopTM_states,
        Compile.copyEmptyRawTM_exit, Compile.copyEmptyPreStates]
    omega
  -- the concrete run lemma (machine matches `copyEmptyRawTM` up to defeq).
  have hrun := hCrun.1
  simp only [hstate_eq] at hrun
  -- budget bounds. The run reaches the exit at exactly
  -- `navSteps + 1 + tl + 1 + (1 + f + g + 1)` (`composeFlatTM_run` accumulates
  -- `t₁ + 1 + t₂` per seam). Bound each piece by the output tape length.
  have hnav_le : ClearGadget.navSteps ((List.take src s).map Compile.shiftReg)
      ≤ 2 * (Compile.encodeTape s ++ res).length + 1 := by
    have h := ClearGadget.navSteps_le ((List.take src s).map Compile.shiftReg)
    rw [Compile.regBlocks_map_shiftReg] at h
    have hreglen : (Compile.encodeRegs (List.take src s)).length
        ≤ (Compile.encodeTape s ++ res).length := by
      rw [List.length_append]
      have hsplit := congrArg List.length hdecomp
      simp only [List.length_cons, List.length_append, Compile.regBlocks_map_shiftReg] at hsplit
      omega
    omega
  have hdst0 : (State.get s dst).length = 0 := by rw [hdst_empty]; rfl
  have hset_len : (Compile.encodeTape (s.set dst (State.get s src))).length
      = (Compile.encodeTape s).length + (State.get s src).length := by
    have hbal := Compile.encodeTape_set_length s dst (State.get s src) hdst
    rw [hdst0] at hbal; omega
  have hin_le : (Compile.encodeTape s ++ res).length
      ≤ (Compile.encodeTape (s.set dst (State.get s src)) ++ res).length := by
    rw [List.length_append, List.length_append, hset_len]; omega
  have hrew_le : 1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
      + (State.get s src).length + 1
      ≤ (Compile.encodeTape (s.set dst (State.get s src)) ++ res).length := by
    rw [List.length_append]; omega
  refine ⟨_, hrun, ?_, ?_⟩
  · -- trajectory
    intro k hk ck hck
    have hh := hCtraj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.copyEmptyRawTM_exit_is_halt dst src) hh, hh⟩
  · -- budget
    omega

theorem Compile.compareLoopTM_start (sc1 sc2 : Var) : (Compile.compareLoopTM sc1 sc2).start = 0 := by
  simp only [Compile.compareLoopTM, Compile.compareBodyTM, Compile.testMachine,
    Compile.testMachineRawM, Compile.bothNonemptyM, Compile.bothNonemptyRawM,
    Compile.navTestRewindM, loopTM_start, branchComposeFlatTM_start, Compile.joinTwoHalts_start,
    ClearGadget.navigateAndTestTM_start]

theorem Compile.compareLoopTM_exit_is_halt (sc1 sc2 : Var)
    (τ : List (List Nat × Nat × List Nat)) :
    haltingStateReached (Compile.compareLoopTM sc1 sc2)
      { state_idx := (Compile.compareBodyTM sc1 sc2).states, tapes := τ } = true := by
  show (loopHalt (Compile.compareBodyTM sc1 sc2)).getD (Compile.compareBodyTM sc1 sc2).states false = true
  show ((List.replicate (Compile.compareBodyTM sc1 sc2).states false ++ [true]).getD
      (Compile.compareBodyTM sc1 sc2).states false) = true
  rw [List.getD_append_right _ _ false (Compile.compareBodyTM sc1 sc2).states
        (by rw [List.length_replicate]),
      List.length_replicate, Nat.sub_self]; rfl

/-- The consume loop only touches `sc1`/`sc2`; every other register is unchanged. -/
theorem Compile.consumeStep_frame (sc1 sc2 : Var) (r : Var)
    (hr1 : r ≠ sc1) (hr2 : r ≠ sc2) (k : Nat) (s : State) :
    State.get ((Compile.consumeStep sc1 sc2)^[k] s) r = State.get s r := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih (Compile.consumeStep sc1 sc2 s),
          Compile.consumeStep, State.get_set_ne _ _ _ _ hr2, State.get_set_ne _ _ _ _ hr1]

/-- **The no-grow restore fact.** Copying the operands into interior scratch
`sb`/`sb+1` (both pre-existing empty), consuming the matched prefix `n` times, then
clearing both scratch registers returns the state to `s` exactly. (`s2 = (s.set sb
a).set (sb+1) b` is the post-copy state; `a`/`b` are bit-shaped operand copies.) -/
theorem Compile.consumeStep_clear_restore (s : State) (sb : Var) (a b : List Nat) (n : Nat)
    (hsb : sb < s.length) (hsb1 : sb + 1 < s.length)
    (hsbe : State.get s sb = []) (hsb1e : State.get s (sb + 1) = [])
    (ha : ∀ x ∈ a, x ≤ 1) (hb : ∀ x ∈ b, x ≤ 1) (hbit : Compile.BitState s) :
    (((Compile.consumeStep sb (sb + 1))^[n]
        ((s.set sb a).set (sb + 1) b)).set sb []).set (sb + 1) [] = s := by
  have hne : (sb : Var) ≠ sb + 1 := Nat.ne_of_lt (Nat.lt_succ_self sb)
  set s2 := (s.set sb a).set (sb + 1) b with hs2
  have hlen_s2 : s2.length = s.length := by
    rw [hs2, Compile.length_set _ _ _ (by rw [Compile.length_set _ _ _ hsb]; exact hsb1),
        Compile.length_set _ _ _ hsb]
  have hbit2 : Compile.BitState s2 := by
    rw [hs2]; exact Compile.BitState_set_pad _ _ _ (Compile.BitState_set_pad _ _ _ hbit ha) hb
  have hsb_s2 : sb < s2.length := by rw [hlen_s2]; exact hsb
  have hsb1_s2 : sb + 1 < s2.length := by rw [hlen_s2]; exact hsb1
  obtain ⟨_, _, hlen_iter, _⟩ := Compile.consumeIter_spec s2 sb (sb + 1) hne hsb_s2 hsb1_s2 hbit2 n
  set s3 := (Compile.consumeStep sb (sb + 1))^[n] s2 with hs3
  have hlen3 : s3.length = s.length := by rw [hlen_iter, hlen_s2]
  have hsb_s3 : sb < s3.length := by rw [hlen3]; exact hsb
  have hsb1_s3' : sb + 1 < (s3.set sb []).length := by
    rw [Compile.length_set _ _ _ hsb_s3, hlen3]; exact hsb1
  apply State.ext_of_get
  · rw [Compile.length_set _ _ _ hsb1_s3', Compile.length_set _ _ _ hsb_s3]; exact hlen3
  · intro r
    by_cases hrb1 : r = sb + 1
    · subst hrb1; rw [State.get_set_eq, hsb1e]
    · rw [State.get_set_ne _ _ _ _ hrb1]
      by_cases hrb : r = sb
      · subst hrb; rw [State.get_set_eq, hsbe]
      · rw [State.get_set_ne _ _ _ _ hrb, hs3,
            Compile.consumeStep_frame sb (sb + 1) r hrb hrb1 n s2, hs2,
            State.get_set_ne _ _ _ _ hrb1, State.get_set_ne _ _ _ _ hrb]

/-- **No-grow cleanup run.** From `encodeTape x ++ res` (head `0`), clears `sb` then
`sb + 1`, exiting at head `0` with `encodeTape ((x.set sb []).set (sb+1) [])` and the
cleared content moved to the residue. -/
theorem Compile.cmpNGCleanup_run (x : State) (sb : Var)
    (hsb : sb < x.length) (hsb1 : sb + 1 < x.length) (hbit : Compile.BitState x)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.cmpNGCleanupM sb)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape x ++ res)] }
      = some { state_idx := Compile.cmpNGCleanupM_exit sb,
               tapes := [([], 0, Compile.encodeTape ((x.set sb []).set (sb + 1) [])
                 ++ ((res ++ List.replicate (State.get x sb).length 0)
                      ++ List.replicate (State.get (x.set sb []) (sb + 1)).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.cmpNGCleanupM sb)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape x ++ res)] } = some ck →
        haltingStateReached (Compile.cmpNGCleanupM sb) ck = false)
    ∧ t ≤ 18 * (Compile.encodeTape x ++ res).length * (Compile.encodeTape x ++ res).length
            + 8 * (Compile.encodeTape x ++ res).length + 45 := by
  have hrep : ∀ n : Nat, Compile.ValidResidue (List.replicate n 0) := by
    intro n y hy; obtain ⟨_, rfl⟩ := List.mem_replicate.mp hy; exact ⟨by omega, by decide⟩
  have hbitA : Compile.BitState (x.set sb []) := Compile.BitState_set_pad x sb [] hbit (by simp)
  have hsb1A : sb + 1 < (x.set sb []).length := by rw [Compile.length_set _ _ _ hsb]; exact hsb1
  have hresA : Compile.ValidResidue (res ++ List.replicate (State.get x sb).length 0) :=
    Compile.ValidResidue_append _ _ hres (hrep _)
  -- stage runs
  obtain ⟨tA, hA_run, hA_traj, htbA⟩ := Compile.clearRegionTM_run x sb res hsb hbit hres
  have hevA : Op.eval (Op.clear sb) x = x.set sb [] := rfl
  rw [hevA] at hA_run
  obtain ⟨tB, hB_run, hB_traj, htbB⟩ :=
    Compile.clearRegionTM_run (x.set sb []) (sb + 1)
      (res ++ List.replicate (State.get x sb).length 0) hsb1A hbitA hresA
  have hevB : Op.eval (Op.clear (sb + 1)) (x.set sb []) = (x.set sb []).set (sb + 1) [] := rfl
  rw [hevB] at hB_run
  -- L-invariance of the second stage's tape length.
  have hbalA := Compile.encodeTape_set_length x sb [] hsb
  simp only [List.length_nil, Nat.add_zero] at hbalA
  have hLB : (Compile.encodeTape (x.set sb []) ++ (res ++ List.replicate (State.get x sb).length 0)).length
      = (Compile.encodeTape x ++ res).length := by
    simp only [List.length_append, List.length_replicate] at hbalA ⊢; omega
  rw [hLB] at htbB
  -- symbol bound for the seam.
  have htape4 : ∀ y ∈ Compile.encodeTape (x.set sb []) ++ (res ++ List.replicate (State.get x sb).length 0), y < 4 :=
    Compile.encodeTape_append_res_lt_four _ _ hbitA hresA
  have hsymB : ∀ v, currentTapeSymbol
      ([], 0, Compile.encodeTape (x.set sb []) ++ (res ++ List.replicate (State.get x sb).length 0)) = some v →
      v < max (ClearGadget.clearRegionTM sb).sig (ClearGadget.clearRegionTM (sb + 1)).sig := by
    intro v hv
    rw [show max (ClearGadget.clearRegionTM sb).sig (ClearGadget.clearRegionTM (sb + 1)).sig = 4
      from by rw [ClearGadget.clearRegionTM_sig, ClearGadget.clearRegionTM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ htape4 _ v hv
  have hexitA_lt : ClearGadget.clearRegionTM_exit sb < (ClearGadget.clearRegionTM sb).states :=
    Compile.clearRegionTM_exit_lt sb
  have hB_run' : runFlatTM tB (ClearGadget.clearRegionTM (sb + 1))
      { state_idx := (ClearGadget.clearRegionTM (sb + 1)).start,
        tapes := [([], 0, Compile.encodeTape (x.set sb []) ++ (res ++ List.replicate (State.get x sb).length 0))] }
        = some { state_idx := ClearGadget.clearRegionTM_exit (sb + 1),
                 tapes := [([], 0, Compile.encodeTape ((x.set sb []).set (sb + 1) [])
                   ++ ((res ++ List.replicate (State.get x sb).length 0)
                        ++ List.replicate (State.get (x.set sb []) (sb + 1)).length 0))] } := by
    rw [ClearGadget.clearRegionTM_start]; exact hB_run
  have h0lt : (0 : Nat) < (ClearGadget.clearRegionTM sb).states := by
    rw [ClearGadget.clearRegionTM_states]; omega
  have hBhalt := Compile.composeFlatTM_halt_intro (ClearGadget.clearRegionTM sb)
    (ClearGadget.clearRegionTM (sb + 1)) (ClearGadget.clearRegionTM_exit (sb + 1))
    (ClearGadget.clearRegionTM_exit sb) (Compile.opClear (sb + 1)).exit_is_halt
  have hrun := composeFlatTM_run (ClearGadget.clearRegionTM_valid sb)
    (ClearGadget.clearRegionTM_valid (sb + 1)) hexitA_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape x ++ res)] } h0lt
    [] 0 (Compile.encodeTape (x.set sb []) ++ (res ++ List.replicate (State.get x sb).length 0))
    hsymB hA_run hA_traj hB_run'
    (Compile.haltingStateReached_of_halt (Compile.opClear (sb + 1)).exit_is_halt)
  have htraj := composeFlatTM_no_early_halt (ClearGadget.clearRegionTM_valid sb)
    (ClearGadget.clearRegionTM_valid (sb + 1)) hexitA_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape x ++ res)] } h0lt
    [] 0 (Compile.encodeTape (x.set sb []) ++ (res ++ List.replicate (State.get x sb).length 0))
    hsymB hA_run hA_traj
    (fun k hk ck hck => (hB_traj k hk ck (by rw [ClearGadget.clearRegionTM_start] at hck; exact hck)).2)
  have heqB : ClearGadget.clearRegionTM_exit (sb + 1) + (ClearGadget.clearRegionTM sb).states
      = Compile.cmpNGCleanupM_exit sb := by rw [Compile.cmpNGCleanupM_exit]; omega
  rw [heqB] at hrun
  refine ⟨tA + 1 + tB, ?_, ?_, ?_⟩
  · rw [Compile.cmpNGCleanupM]; exact hrun.1
  · intro k hk ck hck
    rw [Compile.cmpNGCleanupM] at hck ⊢
    exact htraj k hk ck hck
  · nlinarith [htbA, htbB]

/-- **No-grow prefix run.** Copies `src1`/`src2` into the pre-existing empty scratch
`sb`/`sb+1`, then consumes the matched common prefix. Exits at head `0` on
`encodeTape (consumeStep^[matchLen g1 g2] s2)`, where `s2 = (s.set sb g1).set (sb+1) g2`
holds the two operand copies, residue extended by the `[0,0]`-per-iteration fillers. -/
theorem Compile.cmpNGPrefix_run (s : State) (sb src1 src2 : Var)
    (hsb : sb < s.length) (hsb1 : sb + 1 < s.length)
    (hsrc1 : src1 < s.length) (hsrc2 : src2 < s.length)
    (hsbsrc1 : sb ≠ src1) (hsbsrc2 : sb ≠ src2)
    (hsb1src2 : sb + 1 ≠ src2)
    (hsbe : State.get s sb = []) (hsb1e : State.get s (sb + 1) = [])
    (hbit : Compile.BitState s) (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.cmpNGPrefixM sb src1 src2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.cmpNGPrefixM_exit sb src1 src2,
                 tapes := [([], 0,
                   Compile.encodeTape ((Compile.consumeStep sb (sb + 1))^[
                       Compile.matchLen (State.get s src1) (State.get s src2)]
                       ((s.set sb (State.get s src1)).set (sb + 1) (State.get s src2)))
                     ++ (res ++ List.replicate
                          (2 * Compile.matchLen (State.get s src1) (State.get s src2)) 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.cmpNGPrefixM sb src1 src2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.cmpNGPrefixM sb src1 src2) ck = false)
    ∧ t ≤ ((State.get s src1).length + (State.get s src2).length + 2)
            * (29 * ((Compile.encodeTape s ++ res).length + (State.get s src1).length
                  + (State.get s src2).length) + 68)
          + 6 * ((Compile.encodeTape s ++ res).length + (State.get s src1).length
                + (State.get s src2).length) + 10 := by
  set g1 := State.get s src1 with hg1def
  set g2 := State.get s src2 with hg2def
  have hne : (sb : Var) ≠ sb + 1 := Nat.ne_of_lt (Nat.lt_succ_self sb)
  have hg1mem : g1 ∈ s := by
    rw [hg1def, State.get, List.getElem?_eq_getElem hsrc1, Option.getD_some]; exact List.getElem_mem hsrc1
  have hg2mem : g2 ∈ s := by
    rw [hg2def, State.get, List.getElem?_eq_getElem hsrc2, Option.getD_some]; exact List.getElem_mem hsrc2
  have hg1bit : ∀ x ∈ g1, x ≤ 1 := fun x hx => hbit g1 hg1mem x hx
  have hg2bit : ∀ x ∈ g2, x ≤ 1 := fun x hx => hbit g2 hg2mem x hx
  have hbit1 : Compile.BitState (s.set sb g1) := Compile.BitState_set_pad s sb g1 hbit hg1bit
  have hlen1 : (s.set sb g1).length = s.length := Compile.length_set s sb g1 hsb
  set s2 := (s.set sb g1).set (sb + 1) g2 with hs2def
  have hbit2 : Compile.BitState s2 := Compile.BitState_set_pad _ (sb + 1) g2 hbit1 hg2bit
  have hlen2 : s2.length = s.length := by rw [hs2def, Compile.length_set _ _ _ (by rw [hlen1]; exact hsb1), hlen1]
  -- intermediate get/set facts
  have hcp1get : State.get s src1 = g1 := hg1def.symm
  have hg2eq : State.get (s.set sb g1) src2 = g2 := by rw [State.get_set_ne _ _ _ _ (Ne.symm hsbsrc2), hg2def]
  have hsb1e' : State.get (s.set sb g1) (sb + 1) = [] := by
    rw [State.get_set_ne _ _ _ _ (Ne.symm hne), hsb1e]
  have hsb1_1 : sb + 1 < (s.set sb g1).length := by rw [hlen1]; exact hsb1
  have hsrc2_1 : src2 < (s.set sb g1).length := by rw [hlen1]; exact hsrc2
  have hsb_2 : sb < s2.length := by rw [hlen2]; exact hsb
  have hsb1_2 : sb + 1 < s2.length := by rw [hlen2]; exact hsb1
  have hs2sb : State.get s2 sb = g1 := by
    rw [hs2def, State.get_set_ne _ _ _ _ hne, State.get_set_eq]
  have hs2sb1 : State.get s2 (sb + 1) = g2 := by rw [hs2def, State.get_set_eq]
  -- stage runs
  obtain ⟨t1, hcp1_run, hcp1_traj, hb1⟩ := Compile.copyEmpty_run s sb src1 hsbsrc1 hsb hsrc1 hbit hsbe res hres
  rw [← hg1def] at hcp1_run hb1
  obtain ⟨t2, hcp2_run, hcp2_traj, hb2⟩ :=
    Compile.copyEmpty_run (s.set sb g1) (sb + 1) src2 hsb1src2 hsb1_1 hsrc2_1 hbit1 hsb1e' res hres
  rw [hg2eq] at hb2
  rw [hg2eq, ← hs2def] at hcp2_run
  rw [← hs2def] at hb2
  obtain ⟨t3, hcl_run, hcl_traj, hb3⟩ :=
    Compile.compareLoop_run s2 sb (sb + 1) hne hsb_2 hsb1_2 hbit2 res hres
  rw [hs2sb, hs2sb1] at hcl_run hb3
  -- tape-length facts: copy1 output is `L + |g1|`, copy2/compareLoop run on `M = L + |g1| + |g2|`
  have hsb0 : (State.get s sb).length = 0 := by rw [hsbe]; rfl
  have hbal1 : (Compile.encodeTape (s.set sb g1)).length = (Compile.encodeTape s).length + g1.length := by
    have h := Compile.encodeTape_set_length s sb g1 hsb; rw [hsb0] at h; omega
  have hsb1e0 : (State.get (s.set sb g1) (sb + 1)).length = 0 := by rw [hsb1e']; rfl
  have hbal2 : (Compile.encodeTape s2).length = (Compile.encodeTape s).length + g1.length + g2.length := by
    have h := Compile.encodeTape_set_length (s.set sb g1) (sb + 1) g2 hsb1_1
    rw [← hs2def, hsb1e0, hbal1] at h; omega
  have hL1eq : (Compile.encodeTape (s.set sb g1) ++ res).length
      = (Compile.encodeTape s ++ res).length + g1.length := by
    simp only [List.length_append, hbal1]; omega
  have hL2eq : (Compile.encodeTape s2 ++ res).length
      = (Compile.encodeTape s ++ res).length + g1.length + g2.length := by
    simp only [List.length_append, hbal2]; omega
  -- symbol bound helper
  have hsymtape : ∀ (sX : State), Compile.BitState sX → ∀ v,
      currentTapeSymbol ([], 0, Compile.encodeTape sX ++ res) = some v → v < 4 := by
    intro sX hbX v hv
    exact Compile.sym_bound_of_lt_four _ (Compile.encodeTape_append_res_lt_four _ _ hbX hres) _ v hv
  -- ### Level B: copy1 ⨾ copy2
  have hgrowpos : (0 : Nat) < (Compile.copyEmptyRawTM sb src1).states := by
    rw [Compile.copyEmptyRawTM_states]; omega
  have hsymB : ∀ v, currentTapeSymbol ([], 0, Compile.encodeTape (s.set sb g1) ++ res) = some v →
      v < max (Compile.copyEmptyRawTM sb src1).sig (Compile.copyEmptyRawTM (sb + 1) src2).sig := by
    intro v hv
    rw [show max (Compile.copyEmptyRawTM sb src1).sig (Compile.copyEmptyRawTM (sb + 1) src2).sig = 4 from by
      rw [Compile.copyEmptyRawTM_sig, Compile.copyEmptyRawTM_sig]; rfl]
    exact hsymtape _ hbit1 v hv
  have hcp2_run' : runFlatTM t2 (Compile.copyEmptyRawTM (sb + 1) src2)
      { state_idx := (Compile.copyEmptyRawTM (sb + 1) src2).start,
        tapes := [([], 0, Compile.encodeTape (s.set sb g1) ++ res)] }
        = some { state_idx := Compile.copyEmptyRawTM_exit (sb + 1) src2,
                 tapes := [([], 0, Compile.encodeTape s2 ++ res)] } := by
    rw [Compile.copyEmptyRawTM_start]; exact hcp2_run
  have hBrun := composeFlatTM_run (Compile.copyEmptyRawTM_valid sb src1)
    (Compile.copyEmptyRawTM_valid (sb + 1) src2) (Compile.copyEmptyRawTM_exit_lt sb src1)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } hgrowpos
    [] 0 (Compile.encodeTape (s.set sb g1) ++ res) hsymB hcp1_run hcp1_traj
    hcp2_run' (Compile.haltingStateReached_of_halt (Compile.copyEmptyRawTM_exit_is_halt (sb + 1) src2))
  have hBtraj := composeFlatTM_no_early_halt (Compile.copyEmptyRawTM_valid sb src1)
    (Compile.copyEmptyRawTM_valid (sb + 1) src2) (Compile.copyEmptyRawTM_exit_lt sb src1)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } hgrowpos
    [] 0 (Compile.encodeTape (s.set sb g1) ++ res) hsymB hcp1_run hcp1_traj
    (fun k hk ck hck => (hcp2_traj k hk ck (by rw [Compile.copyEmptyRawTM_start] at hck; exact hck)).2)
  have hBhalt := Compile.composeFlatTM_halt_intro (Compile.copyEmptyRawTM sb src1)
    (Compile.copyEmptyRawTM (sb + 1) src2) (Compile.copyEmptyRawTM_exit (sb + 1) src2)
    (Compile.copyEmptyRawTM_exit sb src1) (Compile.copyEmptyRawTM_exit_is_halt (sb + 1) src2)
  -- ### Level C: ⨾ compareLoop
  have hMB_valid := composeFlatTM_valid _ _ _ (Compile.copyEmptyRawTM_valid sb src1)
    (Compile.copyEmptyRawTM_valid (sb + 1) src2) (Compile.copyEmptyRawTM_exit_lt sb src1)
    (Compile.copyEmptyRawTM_tapes sb src1) (Compile.copyEmptyRawTM_tapes (sb + 1) src2)
  have hMB_states : (composeFlatTM (Compile.copyEmptyRawTM sb src1) (Compile.copyEmptyRawTM (sb + 1) src2)
      (Compile.copyEmptyRawTM_exit sb src1)).states
      = (Compile.copyEmptyRawTM sb src1).states + (Compile.copyEmptyRawTM (sb + 1) src2).states := by
    rw [composeFlatTM_states]
  have hexitC_lt : (Compile.copyEmptyRawTM sb src1).states + Compile.copyEmptyRawTM_exit (sb + 1) src2
      < (composeFlatTM (Compile.copyEmptyRawTM sb src1) (Compile.copyEmptyRawTM (sb + 1) src2)
          (Compile.copyEmptyRawTM_exit sb src1)).states := by
    rw [hMB_states]; exact Nat.add_lt_add_left (Compile.copyEmptyRawTM_exit_lt (sb + 1) src2) _
  have hsymC : ∀ v, currentTapeSymbol ([], 0, Compile.encodeTape s2 ++ res) = some v →
      v < max (composeFlatTM (Compile.copyEmptyRawTM sb src1) (Compile.copyEmptyRawTM (sb + 1) src2)
          (Compile.copyEmptyRawTM_exit sb src1)).sig (Compile.compareLoopTM sb (sb + 1)).sig := by
    intro v hv
    rw [show max (composeFlatTM (Compile.copyEmptyRawTM sb src1) (Compile.copyEmptyRawTM (sb + 1) src2)
          (Compile.copyEmptyRawTM_exit sb src1)).sig (Compile.compareLoopTM sb (sb + 1)).sig = 4 from by
      rw [composeFlatTM_sig, Compile.copyEmptyRawTM_sig, Compile.copyEmptyRawTM_sig,
          Compile.compareLoopTM_sig]; rfl]
    exact hsymtape _ hbit2 v hv
  have hBrun_eq : runFlatTM (t1 + 1 + t2)
      (composeFlatTM (Compile.copyEmptyRawTM sb src1) (Compile.copyEmptyRawTM (sb + 1) src2)
        (Compile.copyEmptyRawTM_exit sb src1))
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := (Compile.copyEmptyRawTM sb src1).states + Compile.copyEmptyRawTM_exit (sb + 1) src2,
               tapes := [([], 0, Compile.encodeTape s2 ++ res)] } := by
    have := hBrun.1; rwa [Nat.add_comm (Compile.copyEmptyRawTM_exit (sb + 1) src2)] at this
  have hcl_run' : runFlatTM t3 (Compile.compareLoopTM sb (sb + 1))
      { state_idx := (Compile.compareLoopTM sb (sb + 1)).start,
        tapes := [([], 0, Compile.encodeTape s2 ++ res)] }
        = some { state_idx := (Compile.compareBodyTM sb (sb + 1)).states,
                 tapes := [([], 0,
                   Compile.encodeTape ((Compile.consumeStep sb (sb + 1))^[Compile.matchLen g1 g2] s2)
                     ++ (res ++ List.replicate (2 * Compile.matchLen g1 g2) 0))] } := by
    rw [Compile.compareLoopTM_start]; exact hcl_run
  have hCrun := composeFlatTM_run hMB_valid (Compile.compareLoopTM_valid sb (sb + 1)) hexitC_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    (by rw [hMB_states]; exact Nat.lt_of_lt_of_le hgrowpos (Nat.le_add_right _ _))
    [] 0 (Compile.encodeTape s2 ++ res) hsymC hBrun_eq
    (fun k hk ck hck => ⟨ClearGadget.ne_of_not_halting hBhalt (hBtraj k hk ck hck), hBtraj k hk ck hck⟩)
    hcl_run' (Compile.compareLoopTM_exit_is_halt sb (sb + 1) _)
  have hCtraj := composeFlatTM_no_early_halt hMB_valid (Compile.compareLoopTM_valid sb (sb + 1)) hexitC_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    (by rw [hMB_states]; exact Nat.lt_of_lt_of_le hgrowpos (Nat.le_add_right _ _))
    [] 0 (Compile.encodeTape s2 ++ res) hsymC hBrun_eq
    (fun k hk ck hck => ⟨ClearGadget.ne_of_not_halting hBhalt (hBtraj k hk ck hck), hBtraj k hk ck hck⟩)
    (fun k hk ck hck => hcl_traj k hk ck (by rw [Compile.compareLoopTM_start] at hck; exact hck))
  have hstate_eq : (Compile.compareBodyTM sb (sb + 1)).states
      + (composeFlatTM (Compile.copyEmptyRawTM sb src1) (Compile.copyEmptyRawTM (sb + 1) src2)
          (Compile.copyEmptyRawTM_exit sb src1)).states
      = Compile.cmpNGPrefixM_exit sb src1 src2 := by
    rw [hMB_states, Compile.cmpNGPrefixM_exit]
  have hrun := hCrun.1
  rw [hstate_eq] at hrun
  refine ⟨_, hrun, ?_, ?_⟩
  · intro k hk ck hck
    exact hCtraj k hk ck hck
  · -- budget: copy1 (tape `L + |g1|`) + copy2 + compareLoop (both tape `M = L + |g1| + |g2|`)
    set M := (Compile.encodeTape s ++ res).length + g1.length + g2.length with hMdef
    have hL2M : (Compile.encodeTape s2 ++ res).length = M := by rw [hL2eq]
    have hm_le : Compile.matchLen g1 g2 ≤ g1.length := Compile.matchLen_le_left g1 g2
    have B1 : t1 ≤ (g1.length + 1) * (5 * M + 23) + 3 * M + 4 := by
      have hmul : (g1.length + 1) * (5 * (Compile.encodeTape (s.set sb g1) ++ res).length + 23)
          ≤ (g1.length + 1) * (5 * M + 23) :=
        Nat.mul_le_mul (Nat.le_refl _) (by rw [hL1eq]; omega)
      have h3 : 3 * (Compile.encodeTape (s.set sb g1) ++ res).length ≤ 3 * M := by rw [hL1eq]; omega
      omega
    have B2 : t2 ≤ (g2.length + 1) * (5 * M + 23) + 3 * M + 4 := by rw [hL2M] at hb2; exact hb2
    have B3 : t3 ≤ (g1.length + 1) * (24 * M + 45) := by
      rw [hL2M] at hb3
      exact le_trans hb3 (Nat.mul_le_mul (by omega) (Nat.le_refl _))
    have key : (g1.length + 1) * (5 * M + 23) + (g2.length + 1) * (5 * M + 23)
          + (g1.length + 1) * (24 * M + 45)
        ≤ (g1.length + g2.length + 2) * (29 * M + 68) := by
      nlinarith [Nat.zero_le g2.length, Nat.zero_le M,
        Nat.mul_le_mul (Nat.le_refl (g2.length + 1)) (Nat.zero_le M)]
    omega

/-- **`compareRegsNoGrowM` run — EQUAL.** With pre-existing empty scratch at the
interior base `sb`/`sb+1` and `s.get src1 = s.get src2`, reaches the EQ exit, tape
restored to `encodeTape s ++ residue`. -/
theorem Compile.compareRegsNoGrowM_run_eq (s : State) (sb src1 src2 : Var)
    (hsb : sb < s.length) (hsb1 : sb + 1 < s.length)
    (hsrc1 : src1 < s.length) (hsrc2 : src2 < s.length)
    (hsbsrc1 : sb ≠ src1) (hsbsrc2 : sb ≠ src2) (hsb1src2 : sb + 1 ≠ src2)
    (heqv : State.get s src1 = State.get s src2)
    (hsbe : State.get s sb = []) (hsb1e : State.get s (sb + 1) = [])
    (hbit : Compile.BitState s) (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ residue, Compile.ValidResidue residue ∧
      residue.length = res.length + (State.get s src1).length + (State.get s src2).length ∧ ∃ t,
      runFlatTM t (Compile.compareRegsNoGrowM sb src1 src2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.compareRegsNoGrowM_exit_eq sb src1 src2,
                 tapes := [([], 0, Compile.encodeTape s ++ residue)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.compareRegsNoGrowM sb src1 src2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.compareRegsNoGrowM sb src1 src2) ck = false)
    ∧ t ≤ ((State.get s src1).length + (State.get s src2).length + 2)
            * (29 * ((Compile.encodeTape s ++ res).length + (State.get s src1).length
                  + (State.get s src2).length) + 68)
          + 18 * ((Compile.encodeTape s ++ res).length + (State.get s src1).length
                + (State.get s src2).length)
              * ((Compile.encodeTape s ++ res).length + (State.get s src1).length
                + (State.get s src2).length)
          + 20 * ((Compile.encodeTape s ++ res).length + (State.get s src1).length
                + (State.get s src2).length) + 59 := by
  set g1 := State.get s src1 with hg1def
  set g2 := State.get s src2 with hg2def
  set n := Compile.matchLen g1 g2 with hndef
  have hne : (sb : Var) ≠ sb + 1 := Nat.ne_of_lt (Nat.lt_succ_self sb)
  have hg1mem : g1 ∈ s := by
    rw [hg1def, State.get, List.getElem?_eq_getElem hsrc1, Option.getD_some]; exact List.getElem_mem hsrc1
  have hg2mem : g2 ∈ s := by
    rw [hg2def, State.get, List.getElem?_eq_getElem hsrc2, Option.getD_some]; exact List.getElem_mem hsrc2
  have hg1bit : ∀ x ∈ g1, x ≤ 1 := fun x hx => hbit g1 hg1mem x hx
  have hg2bit : ∀ x ∈ g2, x ≤ 1 := fun x hx => hbit g2 hg2mem x hx
  have hbit1 : Compile.BitState (s.set sb g1) := Compile.BitState_set_pad s sb g1 hbit hg1bit
  have hlen1 : (s.set sb g1).length = s.length := Compile.length_set s sb g1 hsb
  set s2 := (s.set sb g1).set (sb + 1) g2 with hs2def
  have hbit2 : Compile.BitState s2 := Compile.BitState_set_pad _ (sb + 1) g2 hbit1 hg2bit
  have hlen2 : s2.length = s.length := by rw [hs2def, Compile.length_set _ _ _ (by rw [hlen1]; exact hsb1), hlen1]
  have hs2sb : State.get s2 sb = g1 := by rw [hs2def, State.get_set_ne _ _ _ _ hne, State.get_set_eq]
  have hs2sb1 : State.get s2 (sb + 1) = g2 := by rw [hs2def, State.get_set_eq]
  have hsb_s2 : sb < s2.length := by rw [hlen2]; exact hsb
  have hsb1_s2 : sb + 1 < s2.length := by rw [hlen2]; exact hsb1
  -- residue validity helpers
  have hrep : ∀ m : Nat, Compile.ValidResidue (List.replicate m 0) := by
    intro m x hx; obtain ⟨_, rfl⟩ := List.mem_replicate.mp hx; exact ⟨by omega, by decide⟩
  have hres' : Compile.ValidResidue (res ++ List.replicate (2 * n) 0) :=
    Compile.ValidResidue_append _ _ hres (hrep _)
  -- the post-loop state `s3` and its scratch contents
  set s3 := (Compile.consumeStep sb (sb + 1))^[n] s2 with hs3def
  obtain ⟨hs3sb', hs3sb1', hs3len, hbit3⟩ := Compile.consumeIter_spec s2 sb (sb + 1) hne hsb_s2 hsb1_s2 hbit2 n
  rw [hs2sb] at hs3sb'
  rw [hs2sb1] at hs3sb1'
  have hsb_s3 : sb < s3.length := by rw [hs3def, hs3len, hlen2]; exact hsb
  have hsb1_s3 : sb + 1 < s3.length := by rw [hs3def, hs3len, hlen2]; exact hsb1
  have hrestore : (s3.set sb []).set (sb + 1) [] = s :=
    Compile.consumeStep_clear_restore s sb g1 g2 n hsb hsb1 hsbe hsb1e hg1bit hg2bit hbit
  obtain ⟨he1, he2⟩ := (Compile.matchLen_drop_empty_iff g1 g2).mpr heqv
  have hs3sbe : State.get s3 sb = [] := by rw [hs3sb']; exact he1
  have hs3sb1e : State.get s3 (sb + 1) = [] := by rw [hs3sb1']; exact he2
  -- symbol bound (on `s3` tape)
  have hsym4 : ∀ v, currentTapeSymbol (([] : List Nat), 0,
      Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0)) = some v → v < 4 := by
    intro v hv
    exact Compile.sym_bound_of_lt_four _ (Compile.encodeTape_append_res_lt_four _ _ hbit3 hres') _ v hv
  -- prefix run
  obtain ⟨tP, hPrun, hPtraj, hPbud⟩ := Compile.cmpNGPrefix_run s sb src1 src2 hsb hsb1 hsrc1 hsrc2
    hsbsrc1 hsbsrc2 hsb1src2 hsbe hsb1e hbit res hres
  rw [← hg1def, ← hg2def, ← hndef, ← hs2def, ← hs3def] at hPrun
  rw [← hg1def, ← hg2def] at hPbud
  -- eqVerdict EQ run on `s3`
  obtain ⟨tV, hVrun, hVtraj, hVbud⟩ := Compile.eqVerdictM_run_eq s3 sb (sb + 1)
    (res ++ List.replicate (2 * n) 0) hbit3 hsb_s3 hsb1_s3 hs3sbe hs3sb1e hres'
  -- cleanup run on `s3`, then restore the tape to `encodeTape s`
  obtain ⟨tC, hCrun, hCtraj, hCbud⟩ := Compile.cmpNGCleanup_run s3 sb hsb_s3 hsb1_s3 hbit3
    (res ++ List.replicate (2 * n) 0) hres'
  rw [hrestore] at hCrun
  -- the eqVerdict/cleanup stage tape has length `M = L + |g1| + |g2|` (consume preserves
  -- total length; the clears below move freed cells into the residue).
  have htapeM : (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0)).length
      = (Compile.encodeTape s ++ res).length + g1.length + g2.length := by
    have hb_sb := Compile.encodeTape_set_length s3 sb [] hsb_s3
    have hsb1_set : sb + 1 < (s3.set sb []).length := by
      rw [Compile.length_set _ _ _ hsb_s3]; exact hsb1_s3
    have hb_sb1 := Compile.encodeTape_set_length (s3.set sb []) (sb + 1) [] hsb1_set
    rw [hrestore] at hb_sb1
    have hgsb : (State.get s3 sb).length = g1.length - n := by rw [hs3sb', List.length_drop]
    have hsetget' : State.get (s3.set sb []) (sb + 1) = State.get s3 (sb + 1) :=
      State.get_set_ne _ _ _ _ (Ne.symm hne)
    have hgsb1 : (State.get (s3.set sb []) (sb + 1)).length = g2.length - n := by
      rw [hsetget', hs3sb1', List.length_drop]
    have hn1 : n ≤ g1.length := Compile.matchLen_le_left g1 g2
    have hn2 : n ≤ g2.length := Compile.matchLen_le_right g1 g2
    simp only [List.length_append, List.length_replicate, List.length_nil, Nat.add_zero]
      at hb_sb hb_sb1 ⊢
    omega
  rw [htapeM] at hVbud hCbud
  set residue := ((res ++ List.replicate (2 * n) 0) ++ List.replicate (State.get s3 sb).length 0)
      ++ List.replicate (State.get (s3.set sb []) (sb + 1)).length 0 with hresidue
  have hresidue_valid : Compile.ValidResidue residue :=
    Compile.ValidResidue_append _ _ (Compile.ValidResidue_append _ _ hres' (hrep _)) (hrep _)
  -- the exact residue length: the two scratch suffixes are empty (EQ), so the residue
  -- grew by exactly `2·n = |g1| + |g2|` zero fillers.
  have hresidue_len : residue.length = res.length + g1.length + g2.length := by
    have hsetget : State.get (s3.set sb []) (sb + 1) = State.get s3 (sb + 1) :=
      State.get_set_ne _ _ _ _ (Ne.symm hne)
    have hnle : n ≤ g1.length := Compile.matchLen_le_left g1 g2
    have hgle : g1.length ≤ n := (List.drop_eq_nil_iff).mp he1
    have hg12 : g1.length = g2.length := by rw [heqv]
    rw [hresidue]
    simp only [List.length_append, List.length_replicate, hsetget, hs3sbe, hs3sb1e,
      List.length_nil, Nat.add_zero]
    omega
  -- branch (EQ → cleanup)
  set cfgB : FlatTMConfig :=
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))] } with hcfgB
  have hsymB : ∀ v, currentTapeSymbol (([] : List Nat), 0,
      Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0)) = some v →
      v < max (Compile.eqVerdictM sb (sb + 1)).sig
            (max (Compile.cmpNGCleanupM sb).sig (Compile.cmpNGCleanupM sb).sig) := by
    intro v hv
    rw [Compile.eqVerdictM_sig, Compile.cmpNGCleanupM_sig, Nat.max_self, Nat.max_self]
    exact hsym4 v hv
  have hcfgB_lt : cfgB.state_idx < (Compile.eqVerdictM sb (sb + 1)).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.eqVerdictM_exit_eq_lt sb (sb + 1))
  have hCrun' : runFlatTM tC (Compile.cmpNGCleanupM sb)
      { state_idx := (Compile.cmpNGCleanupM sb).start,
        tapes := [([], 0, Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))] }
        = some { state_idx := Compile.cmpNGCleanupM_exit sb,
                 tapes := [([], 0, Compile.encodeTape s ++ residue)] } := by
    rw [Compile.cmpNGCleanupM_start, hresidue]; exact hCrun
  have hbranchpos := branchComposeFlatTM_run_pos
    (Compile.eqVerdictM_exit_neq_ne_eq sb (sb + 1)).symm
    (Compile.eqVerdictM_valid sb (sb + 1)) (Compile.cmpNGCleanupM_valid sb)
    (Compile.cmpNGCleanupM_valid sb)
    (Compile.eqVerdictM_exit_eq_lt sb (sb + 1)) (Compile.eqVerdictM_exit_neq_lt sb (sb + 1))
    cfgB hcfgB_lt [] 0 (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))
    hsymB hVrun
    (fun k hk ck hck => ⟨(hVtraj k hk ck hck).2.1, (hVtraj k hk ck hck).1, (hVtraj k hk ck hck).2.2⟩)
    hCrun' (Compile.haltingStateReached_of_halt (Compile.cmpNGCleanupM_halt_getElem sb))
  have hbranchpos_traj := branchComposeFlatTM_no_early_halt_pos
    (Compile.eqVerdictM_valid sb (sb + 1)) (Compile.cmpNGCleanupM_valid sb)
    (Compile.cmpNGCleanupM_valid sb)
    (Compile.eqVerdictM_exit_eq_lt sb (sb + 1)) (Compile.eqVerdictM_exit_neq_lt sb (sb + 1))
    cfgB hcfgB_lt [] 0 (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))
    hsymB hVrun
    (fun k hk ck hck => ⟨(hVtraj k hk ck hck).2.1, (hVtraj k hk ck hck).1, (hVtraj k hk ck hck).2.2⟩)
    (fun k hk ck hck => hCtraj k hk ck (by rw [Compile.cmpNGCleanupM_start] at hck; exact hck))
  refine ⟨residue, hresidue_valid, hresidue_len, tP + 1 + (tV + 1 + tC), ?_, ?_, ?_⟩
  · have h := (composeFlatTM_run (Compile.cmpNGPrefixM_valid sb src1 src2)
      (Compile.cmpNGBranchM_valid sb)
      (Compile.cmpNGPrefixM_exit_lt sb src1 src2)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.cmpNGPrefixM_exit_lt sb src1 src2))
      [] 0 (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))
      (by intro v hv; rw [Compile.cmpNGPrefixM_sig, Compile.cmpNGBranchM_sig, Nat.max_self]; exact hsym4 v hv)
      hPrun
      (fun k hk ck hck => ⟨ClearGadget.ne_of_not_halting
        (Compile.cmpNGPrefixM_exit_is_halt sb src1 src2) (hPtraj k hk ck hck),
        hPtraj k hk ck hck⟩)
      (by rw [Compile.cmpNGBranchM_start]; exact hbranchpos.1)
      hbranchpos.2).1
    -- recognise the EQ exit and unfold the machine
    have hstate : (Compile.cmpNGCleanupM_exit sb + (Compile.eqVerdictM sb (sb + 1)).states)
          + (Compile.cmpNGPrefixM sb src1 src2).states
        = Compile.compareRegsNoGrowM_exit_eq sb src1 src2 := by
      rw [Compile.compareRegsNoGrowM_exit_eq]
    rw [Compile.cmpNGBranchM] at h
    rw [show Compile.compareRegsNoGrowM sb src1 src2
        = composeFlatTM (Compile.cmpNGPrefixM sb src1 src2)
            (branchComposeFlatTM (Compile.eqVerdictM sb (sb + 1)) (Compile.cmpNGCleanupM sb)
              (Compile.cmpNGCleanupM sb) (Compile.eqVerdictM_exit_eq sb (sb + 1))
              (Compile.eqVerdictM_exit_neq sb)) (Compile.cmpNGPrefixM_exit sb src1 src2) from rfl,
        ← hstate]
    exact h
  · intro k hk ck hck
    rw [show Compile.compareRegsNoGrowM sb src1 src2
        = composeFlatTM (Compile.cmpNGPrefixM sb src1 src2) (Compile.cmpNGBranchM sb)
            (Compile.cmpNGPrefixM_exit sb src1 src2) from rfl] at hck ⊢
    have := composeFlatTM_no_early_halt (Compile.cmpNGPrefixM_valid sb src1 src2)
      (Compile.cmpNGBranchM_valid sb)
      (Compile.cmpNGPrefixM_exit_lt sb src1 src2)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.cmpNGPrefixM_exit_lt sb src1 src2))
      [] 0 (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))
      (by intro v hv; rw [Compile.cmpNGPrefixM_sig, Compile.cmpNGBranchM_sig, Nat.max_self]; exact hsym4 v hv)
      hPrun
      (fun k hk ck hck => ⟨ClearGadget.ne_of_not_halting
        (Compile.cmpNGPrefixM_exit_is_halt sb src1 src2) (hPtraj k hk ck hck),
        hPtraj k hk ck hck⟩)
      (by rw [Compile.cmpNGBranchM_start]; exact hbranchpos_traj)
    exact this k hk ck hck
  · -- budget: prefix + verdict + cleanup; verdict/cleanup run on tape length `M`.
    omega

/-- **`compareRegsNoGrowM` run — NOT EQUAL.** Symmetric to the EQ case via the
negative (NEQ) branch; both `src1 ≠ src2` sub-cases route to the NEQ exit, tape
restored. -/
theorem Compile.compareRegsNoGrowM_run_neq (s : State) (sb src1 src2 : Var)
    (hsb : sb < s.length) (hsb1 : sb + 1 < s.length)
    (hsrc1 : src1 < s.length) (hsrc2 : src2 < s.length)
    (hsbsrc1 : sb ≠ src1) (hsbsrc2 : sb ≠ src2) (hsb1src2 : sb + 1 ≠ src2)
    (hneqv : State.get s src1 ≠ State.get s src2)
    (hsbe : State.get s sb = []) (hsb1e : State.get s (sb + 1) = [])
    (hbit : Compile.BitState s) (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ residue, Compile.ValidResidue residue ∧
      residue.length = res.length + (State.get s src1).length + (State.get s src2).length ∧ ∃ t,
      runFlatTM t (Compile.compareRegsNoGrowM sb src1 src2)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.compareRegsNoGrowM_exit_neq sb src1 src2,
                 tapes := [([], 0, Compile.encodeTape s ++ residue)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.compareRegsNoGrowM sb src1 src2)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.compareRegsNoGrowM sb src1 src2) ck = false)
    ∧ t ≤ ((State.get s src1).length + (State.get s src2).length + 2)
            * (29 * ((Compile.encodeTape s ++ res).length + (State.get s src1).length
                  + (State.get s src2).length) + 68)
          + 18 * ((Compile.encodeTape s ++ res).length + (State.get s src1).length
                + (State.get s src2).length)
              * ((Compile.encodeTape s ++ res).length + (State.get s src1).length
                + (State.get s src2).length)
          + 20 * ((Compile.encodeTape s ++ res).length + (State.get s src1).length
                + (State.get s src2).length) + 59 := by
  set g1 := State.get s src1 with hg1def
  set g2 := State.get s src2 with hg2def
  set n := Compile.matchLen g1 g2 with hndef
  have hne : (sb : Var) ≠ sb + 1 := Nat.ne_of_lt (Nat.lt_succ_self sb)
  have hg1mem : g1 ∈ s := by
    rw [hg1def, State.get, List.getElem?_eq_getElem hsrc1, Option.getD_some]; exact List.getElem_mem hsrc1
  have hg2mem : g2 ∈ s := by
    rw [hg2def, State.get, List.getElem?_eq_getElem hsrc2, Option.getD_some]; exact List.getElem_mem hsrc2
  have hg1bit : ∀ x ∈ g1, x ≤ 1 := fun x hx => hbit g1 hg1mem x hx
  have hg2bit : ∀ x ∈ g2, x ≤ 1 := fun x hx => hbit g2 hg2mem x hx
  have hbit1 : Compile.BitState (s.set sb g1) := Compile.BitState_set_pad s sb g1 hbit hg1bit
  have hlen1 : (s.set sb g1).length = s.length := Compile.length_set s sb g1 hsb
  set s2 := (s.set sb g1).set (sb + 1) g2 with hs2def
  have hbit2 : Compile.BitState s2 := Compile.BitState_set_pad _ (sb + 1) g2 hbit1 hg2bit
  have hlen2 : s2.length = s.length := by rw [hs2def, Compile.length_set _ _ _ (by rw [hlen1]; exact hsb1), hlen1]
  have hs2sb : State.get s2 sb = g1 := by rw [hs2def, State.get_set_ne _ _ _ _ hne, State.get_set_eq]
  have hs2sb1 : State.get s2 (sb + 1) = g2 := by rw [hs2def, State.get_set_eq]
  have hsb_s2 : sb < s2.length := by rw [hlen2]; exact hsb
  have hsb1_s2 : sb + 1 < s2.length := by rw [hlen2]; exact hsb1
  have hrep : ∀ m : Nat, Compile.ValidResidue (List.replicate m 0) := by
    intro m x hx; obtain ⟨_, rfl⟩ := List.mem_replicate.mp hx; exact ⟨by omega, by decide⟩
  have hres' : Compile.ValidResidue (res ++ List.replicate (2 * n) 0) :=
    Compile.ValidResidue_append _ _ hres (hrep _)
  set s3 := (Compile.consumeStep sb (sb + 1))^[n] s2 with hs3def
  obtain ⟨hs3sb', hs3sb1', hs3len, hbit3⟩ := Compile.consumeIter_spec s2 sb (sb + 1) hne hsb_s2 hsb1_s2 hbit2 n
  rw [hs2sb] at hs3sb'
  rw [hs2sb1] at hs3sb1'
  have hsb_s3 : sb < s3.length := by rw [hs3def, hs3len, hlen2]; exact hsb
  have hsb1_s3 : sb + 1 < s3.length := by rw [hs3def, hs3len, hlen2]; exact hsb1
  have hrestore : (s3.set sb []).set (sb + 1) [] = s :=
    Compile.consumeStep_clear_restore s sb g1 g2 n hsb hsb1 hsbe hsb1e hg1bit hg2bit hbit
  have hnotboth : ¬(g1.drop n = [] ∧ g2.drop n = []) :=
    fun h => hneqv ((Compile.matchLen_drop_empty_iff g1 g2).mp h)
  have hsym4 : ∀ v, currentTapeSymbol (([] : List Nat), 0,
      Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0)) = some v → v < 4 := by
    intro v hv
    exact Compile.sym_bound_of_lt_four _ (Compile.encodeTape_append_res_lt_four _ _ hbit3 hres') _ v hv
  obtain ⟨tP, hPrun, hPtraj, hPbud⟩ := Compile.cmpNGPrefix_run s sb src1 src2 hsb hsb1 hsrc1 hsrc2
    hsbsrc1 hsbsrc2 hsb1src2 hsbe hsb1e hbit res hres
  rw [← hg1def, ← hg2def, ← hndef, ← hs2def, ← hs3def] at hPrun
  rw [← hg1def, ← hg2def] at hPbud
  -- eqVerdict NEQ run on `s3` (left/right operand suffix nonempty)
  obtain ⟨tV, hVrun, hVtraj, hVbud⟩ : ∃ tV,
      runFlatTM tV (Compile.eqVerdictM sb (sb + 1))
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))] }
        = some { state_idx := Compile.eqVerdictM_exit_neq sb,
                 tapes := [([], 0, Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))] }
      ∧ (∀ k, k < tV → ∀ ck,
          runFlatTM k (Compile.eqVerdictM sb (sb + 1))
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))] } = some ck →
          ck.state_idx ≠ Compile.eqVerdictM_exit_neq sb ∧
          ck.state_idx ≠ Compile.eqVerdictM_exit_eq sb (sb + 1) ∧
          haltingStateReached (Compile.eqVerdictM sb (sb + 1)) ck = false)
      ∧ tV ≤ 6 * (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0)).length + 2 := by
    by_cases hd1 : g1.drop n = []
    · have hd2 : g2.drop n ≠ [] := fun h => hnotboth ⟨hd1, h⟩
      exact Compile.eqVerdictM_run_neq_right s3 sb (sb + 1)
        (res ++ List.replicate (2 * n) 0) hbit3 hsb_s3 hsb1_s3
        (by rw [hs3sb']; exact hd1) (by rw [hs3sb1']; exact hd2) hres'
    · exact Compile.eqVerdictM_run_neq_left s3 sb (sb + 1)
        (res ++ List.replicate (2 * n) 0) hbit3 hsb_s3
        (by rw [hs3sb']; exact hd1) hres'
  obtain ⟨tC, hCrun, hCtraj, hCbud⟩ := Compile.cmpNGCleanup_run s3 sb hsb_s3 hsb1_s3 hbit3
    (res ++ List.replicate (2 * n) 0) hres'
  rw [hrestore] at hCrun
  -- the eqVerdict/cleanup stage tape has length `M = L + |g1| + |g2|`.
  have htapeM : (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0)).length
      = (Compile.encodeTape s ++ res).length + g1.length + g2.length := by
    have hb_sb := Compile.encodeTape_set_length s3 sb [] hsb_s3
    have hsb1_set : sb + 1 < (s3.set sb []).length := by
      rw [Compile.length_set _ _ _ hsb_s3]; exact hsb1_s3
    have hb_sb1 := Compile.encodeTape_set_length (s3.set sb []) (sb + 1) [] hsb1_set
    rw [hrestore] at hb_sb1
    have hgsb : (State.get s3 sb).length = g1.length - n := by rw [hs3sb', List.length_drop]
    have hsetget' : State.get (s3.set sb []) (sb + 1) = State.get s3 (sb + 1) :=
      State.get_set_ne _ _ _ _ (Ne.symm hne)
    have hgsb1 : (State.get (s3.set sb []) (sb + 1)).length = g2.length - n := by
      rw [hsetget', hs3sb1', List.length_drop]
    have hn1 : n ≤ g1.length := Compile.matchLen_le_left g1 g2
    have hn2 : n ≤ g2.length := Compile.matchLen_le_right g1 g2
    simp only [List.length_append, List.length_replicate, List.length_nil, Nat.add_zero]
      at hb_sb hb_sb1 ⊢
    omega
  rw [htapeM] at hVbud hCbud
  set residue := ((res ++ List.replicate (2 * n) 0) ++ List.replicate (State.get s3 sb).length 0)
      ++ List.replicate (State.get (s3.set sb []) (sb + 1)).length 0 with hresidue
  have hresidue_valid : Compile.ValidResidue residue :=
    Compile.ValidResidue_append _ _ (Compile.ValidResidue_append _ _ hres' (hrep _)) (hrep _)
  -- the exact residue length: `2·n + |g1.drop n| + |g2.drop n| = |g1| + |g2|` since
  -- `matchLen ≤ |g1|` and `≤ |g2|` (the matched prefix peels one cell off both).
  have hresidue_len : residue.length = res.length + g1.length + g2.length := by
    have hnle1 : n ≤ g1.length := Compile.matchLen_le_left g1 g2
    have hnle2 : n ≤ g2.length := Compile.matchLen_le_right g1 g2
    have e1 : (State.get s3 sb).length = g1.length - n := by rw [hs3sb', List.length_drop]
    have e2 : (State.get (s3.set sb []) (sb + 1)).length = g2.length - n := by
      rw [State.get_set_ne _ _ _ _ (Ne.symm hne), hs3sb1', List.length_drop]
    rw [hresidue]
    simp only [List.length_append, List.length_replicate, e1, e2]
    omega
  set cfgB : FlatTMConfig :=
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))] } with hcfgB
  have hsymB : ∀ v, currentTapeSymbol (([] : List Nat), 0,
      Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0)) = some v →
      v < max (Compile.eqVerdictM sb (sb + 1)).sig
            (max (Compile.cmpNGCleanupM sb).sig (Compile.cmpNGCleanupM sb).sig) := by
    intro v hv
    rw [Compile.eqVerdictM_sig, Compile.cmpNGCleanupM_sig, Nat.max_self, Nat.max_self]
    exact hsym4 v hv
  have hcfgB_lt : cfgB.state_idx < (Compile.eqVerdictM sb (sb + 1)).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.eqVerdictM_exit_eq_lt sb (sb + 1))
  have hCrun' : runFlatTM tC (Compile.cmpNGCleanupM sb)
      { state_idx := (Compile.cmpNGCleanupM sb).start,
        tapes := [([], 0, Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))] }
        = some { state_idx := Compile.cmpNGCleanupM_exit sb,
                 tapes := [([], 0, Compile.encodeTape s ++ residue)] } := by
    rw [Compile.cmpNGCleanupM_start, hresidue]; exact hCrun
  have hbranchneg := branchComposeFlatTM_run_neg
    (Compile.eqVerdictM_exit_neq_ne_eq sb (sb + 1)).symm
    (Compile.eqVerdictM_valid sb (sb + 1)) (Compile.cmpNGCleanupM_valid sb)
    (Compile.cmpNGCleanupM_valid sb)
    (Compile.eqVerdictM_exit_eq_lt sb (sb + 1)) (Compile.eqVerdictM_exit_neq_lt sb (sb + 1))
    cfgB hcfgB_lt [] 0 (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))
    hsymB hVrun
    (fun k hk ck hck => ⟨(hVtraj k hk ck hck).2.1, (hVtraj k hk ck hck).1, (hVtraj k hk ck hck).2.2⟩)
    hCrun' (Compile.haltingStateReached_of_halt (Compile.cmpNGCleanupM_halt_getElem sb))
  have hbranchneg_traj := branchComposeFlatTM_no_early_halt_neg
    (Compile.eqVerdictM_exit_neq_ne_eq sb (sb + 1)).symm
    (Compile.eqVerdictM_valid sb (sb + 1)) (Compile.cmpNGCleanupM_valid sb)
    (Compile.cmpNGCleanupM_valid sb)
    (Compile.eqVerdictM_exit_eq_lt sb (sb + 1)) (Compile.eqVerdictM_exit_neq_lt sb (sb + 1))
    cfgB hcfgB_lt [] 0 (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))
    hsymB hVrun
    (fun k hk ck hck => ⟨(hVtraj k hk ck hck).2.1, (hVtraj k hk ck hck).1, (hVtraj k hk ck hck).2.2⟩)
    (fun k hk ck hck => hCtraj k hk ck (by rw [Compile.cmpNGCleanupM_start] at hck; exact hck))
  refine ⟨residue, hresidue_valid, hresidue_len, tP + 1 + (tV + 1 + tC), ?_, ?_, ?_⟩
  · have h := (composeFlatTM_run (Compile.cmpNGPrefixM_valid sb src1 src2)
      (Compile.cmpNGBranchM_valid sb)
      (Compile.cmpNGPrefixM_exit_lt sb src1 src2)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.cmpNGPrefixM_exit_lt sb src1 src2))
      [] 0 (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))
      (by intro v hv; rw [Compile.cmpNGPrefixM_sig, Compile.cmpNGBranchM_sig, Nat.max_self]; exact hsym4 v hv)
      hPrun
      (fun k hk ck hck => ⟨ClearGadget.ne_of_not_halting
        (Compile.cmpNGPrefixM_exit_is_halt sb src1 src2) (hPtraj k hk ck hck),
        hPtraj k hk ck hck⟩)
      (by rw [Compile.cmpNGBranchM_start]; exact hbranchneg.1)
      hbranchneg.2).1
    have hstate : (Compile.cmpNGCleanupM_exit sb
            + ((Compile.eqVerdictM sb (sb + 1)).states + (Compile.cmpNGCleanupM sb).states))
          + (Compile.cmpNGPrefixM sb src1 src2).states
        = Compile.compareRegsNoGrowM_exit_neq sb src1 src2 := by
      rw [Compile.compareRegsNoGrowM_exit_neq]
    rw [Compile.cmpNGBranchM] at h
    rw [show Compile.compareRegsNoGrowM sb src1 src2
        = composeFlatTM (Compile.cmpNGPrefixM sb src1 src2)
            (branchComposeFlatTM (Compile.eqVerdictM sb (sb + 1)) (Compile.cmpNGCleanupM sb)
              (Compile.cmpNGCleanupM sb) (Compile.eqVerdictM_exit_eq sb (sb + 1))
              (Compile.eqVerdictM_exit_neq sb)) (Compile.cmpNGPrefixM_exit sb src1 src2) from rfl,
        ← hstate]
    exact h
  · intro k hk ck hck
    rw [show Compile.compareRegsNoGrowM sb src1 src2
        = composeFlatTM (Compile.cmpNGPrefixM sb src1 src2) (Compile.cmpNGBranchM sb)
            (Compile.cmpNGPrefixM_exit sb src1 src2) from rfl] at hck ⊢
    have := composeFlatTM_no_early_halt (Compile.cmpNGPrefixM_valid sb src1 src2)
      (Compile.cmpNGBranchM_valid sb)
      (Compile.cmpNGPrefixM_exit_lt sb src1 src2)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.cmpNGPrefixM_exit_lt sb src1 src2))
      [] 0 (Compile.encodeTape s3 ++ (res ++ List.replicate (2 * n) 0))
      (by intro v hv; rw [Compile.cmpNGPrefixM_sig, Compile.cmpNGBranchM_sig, Nat.max_self]; exact hsym4 v hv)
      hPrun
      (fun k hk ck hck => ⟨ClearGadget.ne_of_not_halting
        (Compile.cmpNGPrefixM_exit_is_halt sb src1 src2) (hPtraj k hk ck hck),
        hPtraj k hk ck hck⟩)
      (by rw [Compile.cmpNGBranchM_start]; exact hbranchneg_traj)
    exact this k hk ck hck
  · -- budget: prefix + verdict + cleanup; verdict/cleanup run on tape length `M`.
    omega

/-- **`eqBit` budget arithmetic (HANDOFF bottom-up Task 1(a)).** The tester
(`tT`), the bridge step, and the answer-bit `clearAppendM` (`tC`) compose to the
per-op contract budget `(54·L²+54·L+180)·(cost+1)`. `M = L + a + b` is the working
tape length, `a = |src1|`, `b = |src2|`, `cost = a + b + 1`. The `27·M²`
cost-independent quadratic part fits because `a,b ≤ L` (each operand fits the tape,
`a+3 ≤ L`), so `M ≤ 3L` and the two products `56·c² ≤ 112·L·c` (`hA`, from `c ≤ 2L`)
and `141·L·c ≤ 54·L²·c` (`hB`, from `3 ≤ L`) close the certificate. Stated with
`t ≤ tT+1+tC+1` so both the EQ exit (`tT+1+tC`) and the NEQ demoted-halt bridge
(`tT+1+tC+1`) apply it. -/
theorem Compile.eqBit_budget_arith (L a b tT tC t : Nat)
    (ha3 : a + 3 ≤ L) (hb3 : b + 3 ≤ L)
    (ht : t ≤ tT + 1 + tC + 1)
    (hTbud : tT ≤ (a + b + 2) * (29 * (L + a + b) + 68)
              + 18 * (L + a + b) * (L + a + b) + 20 * (L + a + b) + 59)
    (hCAbud : tC ≤ 9 * (L + a + b) * (L + a + b) + 3 * (L + a + b) + 18) :
    t ≤ (54 * L * L + 54 * L + 180) * (a + b + 1 + 1) := by
  have hA : 56 * ((a + b) * (a + b)) ≤ 112 * (L * (a + b)) := by
    nlinarith [ha3, hb3, Nat.zero_le (a + b)]
  have hB : 141 * (L * (a + b)) ≤ 54 * (L * L * (a + b)) := by
    nlinarith [hb3, Nat.zero_le L, Nat.zero_le (a + b)]
  nlinarith [ht, hTbud, hCAbud, hA, hB, Nat.zero_le L, Nat.zero_le (a + b)]

/-- **`opEqBitNG` run + trajectory (the behavioural part of the `eqBit` residue
contract).** From head `0` on `encodeTape s ++ res_in`, with the two pre-existing empty
interior scratch registers `sb`/`sb+1` (and the operands `dst,src1,src2 < sb`), the
answer bit (`1` if `s.get src1 = s.get src2` else `0`) is written to a freshly cleared
register `dst`; the tape is `encodeTape (Op.eval (eqBit …) s) ++ res_out` with
`res_out.length = |res_in| + |src1| + |src2| + |dst|` (the exact W-invariant residue
growth: the tester consumes both operand copies, the clear frees the old `dst` block).
The two branches merge through `joinTwoHalts`. **No budget conjunct yet** — see HANDOFF
bottom-up Task 1 (budget threading through `cmpNGPrefix_run`/`compareRegsNoGrowM_run_*`). -/
theorem Compile.opEqBitNG_run (s : State) (sb dst src1 src2 : Var) (res_in : List Nat)
    (hbit : Compile.BitState s) (hsb1 : sb + 1 < s.length)
    (hsbe : State.get s sb = []) (hsb1e : State.get s (sb + 1) = [])
    (hdst : dst < sb) (hsrc1 : src1 < sb) (hsrc2 : src2 < sb)
    (hres_in : Compile.ValidResidue res_in) :
    ∃ res_out, Compile.ValidResidue res_out ∧
      res_out.length = res_in.length + (State.get s src1).length + (State.get s src2).length
        + (State.get s dst).length ∧ ∃ t,
      runFlatTM t (Compile.opEqBitNG sb dst src1 src2).M
          (initFlatConfig (Compile.opEqBitNG sb dst src1 src2).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opEqBitNG sb dst src1 src2).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval (Op.eqBit dst src1 src2) s)
                            ++ res_out)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opEqBitNG sb dst src1 src2).M
            (initFlatConfig (Compile.opEqBitNG sb dst src1 src2).M [Compile.encodeTape s ++ res_in]) = some ck →
        ck.state_idx ≠ (Compile.opEqBitNG sb dst src1 src2).exit ∧
        haltingStateReached (Compile.opEqBitNG sb dst src1 src2).M ck = false)
    ∧ t ≤ (54 * (Compile.encodeTape s ++ res_in).length
               * (Compile.encodeTape s ++ res_in).length
             + 54 * (Compile.encodeTape s ++ res_in).length + 180)
          * (Op.cost (Op.eqBit dst src1 src2) s + 1) := by
  -- derived bounds / disjointness (omega can't see through `Var`; use explicit Nat lemmas)
  have hsb : sb < s.length := Nat.lt_of_succ_lt hsb1
  have hdstL : dst < s.length := Nat.lt_trans hdst hsb
  have hsrc1L : src1 < s.length := Nat.lt_trans hsrc1 hsb
  have hsrc2L : src2 < s.length := Nat.lt_trans hsrc2 hsb
  have hsbsrc1 : (sb : Var) ≠ src1 := Ne.symm (Nat.ne_of_lt hsrc1)
  have hsbsrc2 : (sb : Var) ≠ src2 := Ne.symm (Nat.ne_of_lt hsrc2)
  have hsb1src2 : (sb + 1 : Var) ≠ src2 := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt hsrc2))
  -- each operand register fits in the tape: `|s.get srcᵢ| + 3 ≤ |encodeTape s ++ res_in|`.
  have ha3 : (State.get s src1).length + 3 ≤ (Compile.encodeTape s ++ res_in).length := by
    have hdec := congrArg List.length (Compile.encodeTape_reg_decomp_at s src1 hsrc1L).2
    simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map,
      List.length_nil] at hdec
    rw [List.length_append]; omega
  have hb3 : (State.get s src2).length + 3 ≤ (Compile.encodeTape s ++ res_in).length := by
    have hdec := congrArg List.length (Compile.encodeTape_reg_decomp_at s src2 hsrc2L).2
    simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map,
      List.length_nil] at hdec
    rw [List.length_append]; omega
  set raw := Compile.eqBitNGRawM sb dst src1 src2 with hrawdef
  set h1 := Compile.eqBitNGRawM_h1 sb dst src1 src2 with hh1def
  set h2 := Compile.eqBitNGRawM_h2 sb dst src1 src2 with hh2def
  have hraweq : branchComposeFlatTM (Compile.compareRegsNoGrowM sb src1 src2)
      (Compile.clearAppendM dst 2 (by decide)) (Compile.clearAppendM dst 1 (by decide))
      (Compile.compareRegsNoGrowM_exit_eq sb src1 src2)
      (Compile.compareRegsNoGrowM_exit_neq sb src1 src2) = raw := rfl
  have hMstart : (Compile.opEqBitNG sb dst src1 src2).M.start = 0 := by
    show (joinTwoHalts raw h1 h2).start = 0
    rw [joinTwoHalts_start, hrawdef, Compile.eqBitNGRawM, branchComposeFlatTM_start]
    exact Compile.compareRegsNoGrowM_start sb src1 src2
  have hinit : initFlatConfig (Compile.opEqBitNG sb dst src1 src2).M [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hMstart, List.map_cons, List.map_nil]
  have hMeq : (Compile.opEqBitNG sb dst src1 src2).M = joinTwoHalts raw h1 h2 := rfl
  have hexit : (Compile.opEqBitNG sb dst src1 src2).exit = h1 := rfl
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    with hcfg0
  have h_cfg_lt : cfg0.state_idx < (Compile.compareRegsNoGrowM sb src1 src2).states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Compile.compareRegsNoGrowM_exit_eq_lt sb src1 src2)
  have hCAstart2 : (Compile.clearAppendM dst 2 (by decide)).start = 0 := Compile.clearAppendM_start dst 2 (by decide)
  have hCAstart1 : (Compile.clearAppendM dst 1 (by decide)).start = 0 := Compile.clearAppendM_start dst 1 (by decide)
  have hh1_is := Compile.eqBitNGRawM_h1_is_halt sb dst src1 src2
  have hh2_is := Compile.eqBitNGRawM_h2_is_halt sb dst src1 src2
  have hh_ne := Compile.eqBitNGRawM_h1_ne_h2 sb dst src1 src2
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  rw [hinit, hMeq, hexit]
  by_cases he : State.get s src1 = State.get s src2
  · -- EQ: answer bit 1, Op.eval = s.set dst [1]; raw reaches h1 (kept).
    have hisE : Op.eval (Op.eqBit dst src1 src2) s = s.set dst [1] := by
      show s.set dst (if State.get s src1 = State.get s src2 then [1] else [0]) = s.set dst [1]
      rw [if_pos he]
    obtain ⟨residue, hres_valid, hres_len, tT, hTrun, hTtraj, hTbud⟩ :=
      Compile.compareRegsNoGrowM_run_eq s sb src1 src2 hsb hsb1 hsrc1L hsrc2L hsbsrc1 hsbsrc2
        hsb1src2 he hsbe hsb1e hbit res_in hres_in
    obtain ⟨tC, hCrun, hCtraj, hCAbud⟩ :=
      Compile.clearAppendM_run s dst 1 (by omega) hdstL hbit residue hres_valid
    -- the clearAppend stage tape has length `M = L + |g1| + |g2|`.
    have hclen : (Compile.encodeTape s ++ residue).length
        = (Compile.encodeTape s ++ res_in).length + (State.get s src1).length
            + (State.get s src2).length := by
      simp only [List.length_append] at hres_len ⊢; omega
    rw [hclen] at hCAbud
    -- symbol bound at the M1-exit tape (head 0): cell is the sentinel `3 < 4`.
    have hsymB : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ residue) = some v →
        v < max (Compile.compareRegsNoGrowM sb src1 src2).sig
              (max (Compile.clearAppendM dst 2 (by decide)).sig (Compile.clearAppendM dst 1 (by decide)).sig) := by
      intro v hv
      rw [Compile.compareRegsNoGrowM_sig, Compile.clearAppendM_sig, Compile.clearAppendM_sig,
          Nat.max_self, Nat.max_self]
      exact Compile.sym_bound_of_lt_four _ (Compile.encodeTape_append_res_lt_four s residue hbit hres_valid) _ v hv
    have hCrun' : runFlatTM tC (Compile.clearAppendM dst 2 (by decide))
        { state_idx := (Compile.clearAppendM dst 2 (by decide)).start,
          tapes := [([], 0, Compile.encodeTape s ++ residue)] }
        = some { state_idx := Compile.clearAppendM_exit dst 2 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [1])
                            ++ (residue ++ List.replicate (s.get dst).length 0))] } := by
      rw [hCAstart2]; exact hCrun
    have hpos := branchComposeFlatTM_run_pos
      (Compile.compareRegsNoGrowM_exit_eq_ne_neq sb src1 src2)
      (Compile.compareRegsNoGrowM_valid sb src1 src2)
      (Compile.clearAppendM_valid dst 2 (by decide)) (Compile.clearAppendM_valid dst 1 (by decide))
      (Compile.compareRegsNoGrowM_exit_eq_lt sb src1 src2)
      (Compile.compareRegsNoGrowM_exit_neq_lt sb src1 src2)
      cfg0 h_cfg_lt [] 0 (Compile.encodeTape s ++ residue) hsymB hTrun
      (fun k hk ck hck => ⟨ClearGadget.ne_of_not_halting
          (Compile.compareRegsNoGrowM_exit_eq_is_halt sb src1 src2) (hTtraj k hk ck hck),
        ClearGadget.ne_of_not_halting
          (Compile.compareRegsNoGrowM_exit_neq_is_halt sb src1 src2) (hTtraj k hk ck hck),
        hTtraj k hk ck hck⟩)
      hCrun' (Compile.haltingStateReached_of_halt (Compile.clearAppendM_exit_is_halt dst 2 (by decide)))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      (Compile.compareRegsNoGrowM_valid sb src1 src2)
      (Compile.clearAppendM_valid dst 2 (by decide)) (Compile.clearAppendM_valid dst 1 (by decide))
      (Compile.compareRegsNoGrowM_exit_eq_lt sb src1 src2)
      (Compile.compareRegsNoGrowM_exit_neq_lt sb src1 src2)
      cfg0 h_cfg_lt [] 0 (Compile.encodeTape s ++ residue) hsymB hTrun
      (fun k hk ck hck => ⟨ClearGadget.ne_of_not_halting
          (Compile.compareRegsNoGrowM_exit_eq_is_halt sb src1 src2) (hTtraj k hk ck hck),
        ClearGadget.ne_of_not_halting
          (Compile.compareRegsNoGrowM_exit_neq_is_halt sb src1 src2) (hTtraj k hk ck hck),
        hTtraj k hk ck hck⟩)
      (fun k hk ck hck => hCtraj k hk ck (by rw [hCAstart2] at hck; exact hck))
    have hstate_eq : Compile.clearAppendM_exit dst 2 (by decide)
        + (Compile.compareRegsNoGrowM sb src1 src2).states = h1 := by
      rw [hh1def, Compile.eqBitNGRawM_h1]; omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (s.set dst [1]) ++ (residue ++ List.replicate (s.get dst).length 0))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨residue ++ List.replicate (s.get dst).length 0,
      Compile.ValidResidue_append_replicate_zero residue _ hres_valid, ?_, _, ?_, hjoin_traj, ?_⟩
    · rw [List.length_append, List.length_replicate, hres_len]
    · rw [hisE]; exact hjoin
    · -- budget: tester (tT) + bridge + clearAppend (tC) ≤ contract quadratic × (cost+1).
      simp only [Op.cost]
      exact Compile.eqBit_budget_arith _ _ _ _ _ _ ha3 hb3 (by omega) hTbud hCAbud
  · -- NEQ: answer bit 0, Op.eval = s.set dst [0]; raw reaches h2 (demoted), bridges to h1.
    have hisE : Op.eval (Op.eqBit dst src1 src2) s = s.set dst [0] := by
      show s.set dst (if State.get s src1 = State.get s src2 then [1] else [0]) = s.set dst [0]
      rw [if_neg he]
    obtain ⟨residue, hres_valid, hres_len, tT, hTrun, hTtraj, hTbud⟩ :=
      Compile.compareRegsNoGrowM_run_neq s sb src1 src2 hsb hsb1 hsrc1L hsrc2L hsbsrc1 hsbsrc2
        hsb1src2 he hsbe hsb1e hbit res_in hres_in
    obtain ⟨tC, hCrun, hCtraj, hCAbud⟩ :=
      Compile.clearAppendM_run s dst 0 (by omega) hdstL hbit residue hres_valid
    have hclen : (Compile.encodeTape s ++ residue).length
        = (Compile.encodeTape s ++ res_in).length + (State.get s src1).length
            + (State.get s src2).length := by
      simp only [List.length_append] at hres_len ⊢; omega
    rw [hclen] at hCAbud
    have hsymB : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ residue) = some v →
        v < max (Compile.compareRegsNoGrowM sb src1 src2).sig
              (max (Compile.clearAppendM dst 2 (by decide)).sig (Compile.clearAppendM dst 1 (by decide)).sig) := by
      intro v hv
      rw [Compile.compareRegsNoGrowM_sig, Compile.clearAppendM_sig, Compile.clearAppendM_sig,
          Nat.max_self, Nat.max_self]
      exact Compile.sym_bound_of_lt_four _ (Compile.encodeTape_append_res_lt_four s residue hbit hres_valid) _ v hv
    have hCrun' : runFlatTM tC (Compile.clearAppendM dst 1 (by decide))
        { state_idx := (Compile.clearAppendM dst 1 (by decide)).start,
          tapes := [([], 0, Compile.encodeTape s ++ residue)] }
        = some { state_idx := Compile.clearAppendM_exit dst 1 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [0])
                            ++ (residue ++ List.replicate (s.get dst).length 0))] } := by
      rw [hCAstart1]; exact hCrun
    have hneg := branchComposeFlatTM_run_neg
      (Compile.compareRegsNoGrowM_exit_eq_ne_neq sb src1 src2)
      (Compile.compareRegsNoGrowM_valid sb src1 src2)
      (Compile.clearAppendM_valid dst 2 (by decide)) (Compile.clearAppendM_valid dst 1 (by decide))
      (Compile.compareRegsNoGrowM_exit_eq_lt sb src1 src2)
      (Compile.compareRegsNoGrowM_exit_neq_lt sb src1 src2)
      cfg0 h_cfg_lt [] 0 (Compile.encodeTape s ++ residue) hsymB hTrun
      (fun k hk ck hck => ⟨ClearGadget.ne_of_not_halting
          (Compile.compareRegsNoGrowM_exit_eq_is_halt sb src1 src2) (hTtraj k hk ck hck),
        ClearGadget.ne_of_not_halting
          (Compile.compareRegsNoGrowM_exit_neq_is_halt sb src1 src2) (hTtraj k hk ck hck),
        hTtraj k hk ck hck⟩)
      hCrun' (Compile.haltingStateReached_of_halt (Compile.clearAppendM_exit_is_halt dst 1 (by decide)))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg
      (Compile.compareRegsNoGrowM_exit_eq_ne_neq sb src1 src2)
      (Compile.compareRegsNoGrowM_valid sb src1 src2)
      (Compile.clearAppendM_valid dst 2 (by decide)) (Compile.clearAppendM_valid dst 1 (by decide))
      (Compile.compareRegsNoGrowM_exit_eq_lt sb src1 src2)
      (Compile.compareRegsNoGrowM_exit_neq_lt sb src1 src2)
      cfg0 h_cfg_lt [] 0 (Compile.encodeTape s ++ residue) hsymB hTrun
      (fun k hk ck hck => ⟨ClearGadget.ne_of_not_halting
          (Compile.compareRegsNoGrowM_exit_eq_is_halt sb src1 src2) (hTtraj k hk ck hck),
        ClearGadget.ne_of_not_halting
          (Compile.compareRegsNoGrowM_exit_neq_is_halt sb src1 src2) (hTtraj k hk ck hck),
        hTtraj k hk ck hck⟩)
      (fun k hk ck hck => hCtraj k hk ck (by rw [hCAstart1] at hck; exact hck))
    have hstate_eq : Compile.clearAppendM_exit dst 1 (by decide)
        + ((Compile.compareRegsNoGrowM sb src1 src2).states + (Compile.clearAppendM dst 2 (by decide)).states) = h2 := by
      rw [hh2def, Compile.eqBitNGRawM_h2]; omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (s.set dst [0]) ++ (residue ++ List.replicate (s.get dst).length 0)) 0
      hneg.1 (fun k hk ck hck => hneg_traj k hk ck hck) hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (s.set dst [0]) ++ (residue ++ List.replicate (s.get dst).length 0))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.eqBitNGRawM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨residue ++ List.replicate (s.get dst).length 0,
      Compile.ValidResidue_append_replicate_zero residue _ hres_valid, ?_, _, ?_, hjoin_traj, ?_⟩
    · rw [List.length_append, List.length_replicate, hres_len]
    · rw [hisE]; exact hjoin
    · -- budget: tester (tT) + bridge + clearAppend (tC) + demoted-halt bridge ≤ contract.
      simp only [Op.cost]
      exact Compile.eqBit_budget_arith _ _ _ _ _ _ ha3 hb3 (by omega) hTbud hCAbud

