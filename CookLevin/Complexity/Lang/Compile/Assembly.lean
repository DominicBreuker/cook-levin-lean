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
import Complexity.Lang.Compile.OpSound

set_option autoImplicit false

/-! # `Compile/Assembly` — C6 tester, assembly toolkit, loop run + program contract

Extracted from `Compile.lean` (refactor Phase 3). The program-level assembly:
the C6 `bitTestTM` tester; the C2 assembly toolkit (`Op.inBounds_of_UsesBelow`,
`Op.NotConsLen`/`Cmd.NoConsLen`, `Cmd.eval_preserves_BitState`, `physStepBudget`);
`compileIfBit_sound_physical_residue`; the full `forBnd` loop run stack
(`forBndIterate_run`, the fold invariants, `forBndBody_*`/`forBndLoop_*`,
`forBndLoop_eval`/`_run`); `compileForBnd_sound_physical_residue`; the program
contract `run_physical_residue_gen` + `Compile_run_physical_residue`; and the
`bitDeciderTM` + `bitDecider_run` decider. Depends on `Compile/OpSound`. -/

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators
/-! ## C6 — the tape→state bit-test gadget (`DecidesLang' → DecidesBy` bridge)

`Compile c` always halts in its single `exit` state with the answer written on
the **tape** (register `0` = `[1]` accept / `[0]` reject). `DecidesBy` instead
reads its answer from the **state index** (`acceptState` / `rejectState`). The
gap is closed by composing `Compile c` with a tiny gadget that reads the tape's
first symbol — `2` (shifted `1`, accept) or `1` (shifted `0`, reject), per the
`encodeTape` format — and halts in a *distinct* state for each.

This gadget and its run lemmas depend **only** on the encoding format, not on
`Compile_sound` / the physical run contract, so they are isolable and
`sorry`-free. -/

/-- The bit-test gadget: a single-tape, 4-symbol, 4-state `FlatTM`. The encoded
tape begins with the leading sentinel `endMark = 3`, so from the (non-halting)
start state `0` the gadget reads `3` and **steps right** past the sentinel into
state `3`; there, reading the answer bit `2` jumps to the halting state `1`
(accept) and `1` jumps to the halting state `2` (reject), without further
movement. -/
def Compile.bitTestTM : FlatTM where
  sig := 4
  tapes := 1
  states := 4
  trans :=
    [ { src_state := 0, src_tape_vals := [some 3], dst_state := 3,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] },
      { src_state := 3, src_tape_vals := [some 2], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] },
      { src_state := 3, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] } ]
  start := 0
  halt := [false, true, true, false]

theorem Compile.bitTestTM_valid : validFlatTM Compile.bitTestTM := by
  refine ⟨by decide, rfl, ?_⟩
  intro entry hentry
  have hmem : entry ∈
      [ ({ src_state := 0, src_tape_vals := [some 3], dst_state := 3,
           dst_write_vals := [none], move_dirs := [TMMove.Rmove] } : FlatTMTransEntry),
        { src_state := 3, src_tape_vals := [some 2], dst_state := 1,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] },
        { src_state := 3, src_tape_vals := [some 1], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } ] := hentry
  have hbound3 : flatTMOptionSymbolsBounded 4 [some 3] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide
  have hbound2 : flatTMOptionSymbolsBounded 4 [some 2] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide
  have hbound1 : flatTMOptionSymbolsBounded 4 [some 1] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide
  have hboundNone : flatTMOptionSymbolsBounded 4 [none] := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; trivial
  rcases List.mem_cons.mp hmem with h | hmem
  · subst h; exact ⟨by decide, by decide, rfl, rfl, rfl, hbound3, hboundNone⟩
  · rcases List.mem_cons.mp hmem with h | hmem
    · subst h; exact ⟨by decide, by decide, rfl, rfl, rfl, hbound2, hboundNone⟩
    · rcases List.mem_cons.mp hmem with h | h
      · subst h; exact ⟨by decide, by decide, rfl, rfl, rfl, hbound1, hboundNone⟩
      · simp at h

theorem Compile.bitTestTM_tapes : Compile.bitTestTM.tapes = 1 := rfl

theorem Compile.bitTestTM_sig : Compile.bitTestTM.sig = 4 := rfl

theorem Compile.bitTestTM_start : Compile.bitTestTM.start = 0 := rfl

/-- After the leading sentinel `3`, reading the answer `2` (accept) halts the
gadget in state `1` in two steps (one to step past the sentinel). -/
theorem Compile.bitTestTM_run_two (left rest : List Nat) :
    runFlatTM 2 Compile.bitTestTM { state_idx := 0, tapes := [(left, 0, 3 :: 2 :: rest)] }
      = some { state_idx := 1, tapes := [(left, 1, 3 :: 2 :: rest)] } := rfl

/-- After the leading sentinel `3`, reading the answer `1` (reject) halts the
gadget in state `2` in two steps. -/
theorem Compile.bitTestTM_run_one (left rest : List Nat) :
    runFlatTM 2 Compile.bitTestTM { state_idx := 0, tapes := [(left, 0, 3 :: 1 :: rest)] }
      = some { state_idx := 2, tapes := [(left, 1, 3 :: 1 :: rest)] } := rfl

/-- State `1` (accept) and state `2` (reject) are both halting states. -/
theorem Compile.bitTestTM_halt_one : Compile.bitTestTM.halt.getD 1 false = true := rfl
theorem Compile.bitTestTM_halt_two : Compile.bitTestTM.halt.getD 2 false = true := rfl

/-! ## ★ The C2 assembly toolkit (relocated upstream 2026-06-06 from PolyTime.lean)

Threading lemmas + the residue-induction assembly `run_physical_residue_gen`,
moved here so they sit BEFORE `Compile_run_physical_residue` and can discharge it
(they were downstream in PolyTime.lean). See HANDOFF.md. -/

/-- **`inBounds` from a static `UsesBelow` bound (the `inBounds`-threading
bridge; lives here because it relates `Op.UsesBelow` in `Frame` to `Op.inBounds`
in `Compile`).** An op that statically touches only registers `< k`, run on a
state of width `≥ k`, is in bounds. Combined with `Op.eval_length_ge` /
`Cmd.eval_length_ge` (the register count never shrinks) and `Cmd.UsesBelow`, this
supplies the `o.inBounds s` premise of `Op.eval_preserves_BitState` and of the
per-op gadgets at *every* fragment of the `Compile_run_physical_residue`
induction: fix `k ≤ s.length` with `Cmd.UsesBelow c k`, and every reached state
keeps width `≥ k`. -/
theorem Op.inBounds_of_UsesBelow (o : Op) (k : Nat) (s : State)
    (h : Op.UsesBelow o k) (hk : k ≤ s.length) : o.inBounds s := by
  cases o with
  | clear dst => exact Nat.lt_of_lt_of_le h hk
  | appendOne dst => exact Nat.lt_of_lt_of_le h hk
  | appendZero dst => exact Nat.lt_of_lt_of_le h hk
  | copy dst src => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  | tail dst src => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  | head dst src => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  | eqBit dst a b =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk,
             Nat.lt_of_lt_of_le h.2.2 hk⟩
  | nonEmpty dst src => exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2 hk⟩
  | concat dst a b =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hk, Nat.lt_of_lt_of_le h.2.1 hk,
             Nat.lt_of_lt_of_le h.2.2 hk⟩

/-- **`BitState` is preserved by every `Cmd` (the residue induction's
invariant, validated end-to-end).** Threads the two per-op atoms
(`Op.eval_preserves_BitState` for `BitState`, `Op.inBounds_of_UsesBelow` for
`inBounds`) and register-count monotonicity (`Cmd.eval_length_ge`,
`State.set_length_ge`) through the full `Cmd` induction — including the `forBnd`
fold, whose invariant is `k ≤ width ∧ BitState`. This is exactly the
invariant-threading `Compile_run_physical_residue` performs, so proving it
standalone de-risks that induction: the `forBnd` counter-write (`BitState_set_pad`
+ width growth) and the `seq` width-carry both go through.

The `Cmd.UsesBelow c k`/`k ≤ s.length` pair is the wellformedness hypothesis the
obligation carries. -/
theorem Cmd.eval_preserves_BitState (c : Cmd) (k : Nat) (s : State)
    (huses : Cmd.UsesBelow c k) (hk : k ≤ s.length)
    (hbit : Compile.BitState s) :
    Compile.BitState (c.eval s) := by
  induction c generalizing s with
  | op o =>
      exact Op.eval_preserves_BitState o s hbit
        (Op.inBounds_of_UsesBelow o k s huses hk)
  | seq c1 c2 ih1 ih2 =>
      rw [Cmd.eval_seq]
      have hbit1 : Compile.BitState (c1.eval s) := ih1 s huses.1 hk hbit
      have hk1 : k ≤ (c1.eval s).length := Nat.le_trans hk (Cmd.eval_length_ge c1 s)
      exact ih2 (c1.eval s) huses.2 hk1 hbit1
  | ifBit t cT cE ihT ihE =>
      by_cases hb : s.get t = [1]
      · rw [Cmd.eval_ifBit_true t cT cE s hb]
        exact ihT s huses.2.1 hk hbit
      · rw [Cmd.eval_ifBit_false t cT cE s hb]
        exact ihE s huses.2.2 hk hbit
  | forBnd cnt bnd body ihbody =>
      obtain ⟨_, _, hbody⟩ := huses
      rw [Cmd.eval_forBnd]
      refine (Cmd.foldlState_range_induct body cnt (s.get bnd).length s
        (fun _ st => k ≤ st.length ∧ Compile.BitState st) ⟨hk, hbit⟩ ?_).2
      intro i st _ hM
      obtain ⟨hkst, hbst⟩ := hM
      have hset_bit : Compile.BitState (st.set cnt (List.replicate i 1)) :=
        Compile.BitState_set_pad st cnt _ hbst (by
          intro x hx; obtain ⟨-, rfl⟩ := List.mem_replicate.mp hx; exact Nat.le_refl 1)
      have hset_k : k ≤ (st.set cnt (List.replicate i 1)).length :=
        Nat.le_trans hkst (State.set_length_ge st cnt _)
      exact ⟨Nat.le_trans hset_k (Cmd.eval_length_ge body _),
        ihbody (st.set cnt (List.replicate i 1)) hbody hset_k hset_bit⟩

/-! ## ★ TOP-DOWN ASSEMBLY DESIGN (2026-06-06) — the residue induction skeleton

This block is the **top-down** design of the proof of `Compile_run_physical_residue`
(`Compile.lean:8910`, the central C2 obligation). It pins the **shared interface**
between the two work streams (see `HANDOFF.md`): the four per-fragment
physical-residue contracts (op / seq / ifBit / forBnd) compose into the obligation
by induction on `Cmd`. The composition has been **validated by hand** (budget,
residue, defeq); the remaining work is mechanical (the W-invariant + budget Nat
arithmetic) plus the two `sorry`-bodied combinators below — which are gated on the
bottom-up stream building the real `compileForBnd` / `compileTestBit` machines (today
both are 0-transition stubs).

⚠ These lemmas live here (not in `Compile.lean`) because they call the threading
lemmas `Cmd.eval_preserves_BitState` / `Op.inBounds_of_UsesBelow` / `Cmd.NoConsLen`
which are defined above in this file — *downstream* of the obligation they must
discharge. **To actually close `Compile_run_physical_residue`, relocate those
threading lemmas (and this block) upstream into `Compile.lean`** (all their deps are
already available there). See HANDOFF.md "TOP-DOWN findings", GAP 3. -/

/-- **Compositional per-fragment TM-step budget.** A `Compile` fragment whose
physical tape stays `≤ G` cells and which runs `cost` layer-ops halts within
`(9·G² + 9·G + 33)·(8·cost + 8) + cost` steps: **8 budget units per cost item**
(each unit one `O(G²)` single-tape pass), plus `+cost` slack for `seq` control
steps.

Chosen because it is **exactly superadditive** under `seq`:
`physStepBudget G (1 + c₁ + c₂) = physStepBudget G c₁ + 1 + physStepBudget G c₂`.
The quadratic `Compile.overhead (·+1)²` fails this (ROADMAP Finding #3): summing
`~cost` per-op quadratics is cubic, and it dropped both the register count `s.length`
and the residue length. `inOPoly`/`monotonic` in both arguments, which is all the
downstream consumers (`toFrameworkWitness'`, `bitDecider_run`) need.

**⚠ Why 8 units per cost item, not 1 (2026-06-11 top-down finding — do not
re-tighten).** The `forBnd` machine must do per-iteration *bookkeeping* the layer
cost does not see: rebuild `counter := replicate i 1` from the scratch master
(one cursor-copy pass), maintain the remaining/done counts (`tail`/`appendOne`
passes), and run the loop test — ~5–6 `O(G²)` passes per iteration, plus
entry/exit snapshots. The loop's cost lump `iters²` grants `iters²` cost items
against `~6·iters` bookkeeping passes, which at 1 unit/item is **unsatisfiable
for `iters ≤ 5`** (machine-independent: `6·iters ≰ iters² + 2` at `iters = 1`).
With 8 units per item the worst case (`iters = 1`: 8 + bookkeeping ≤ 24 units)
clears with slack. Scaling the multiplier preserves exact superadditivity
(`U·(8a+8) + a + 1 + U·(8b+8) + b = U·(8(1+a+b)+8) + (1+a+b)`). -/
def Compile.physStepBudget (G cost : Nat) : Nat :=
  (9 * G * G + 9 * G + 33) * (8 * cost + 8) + cost

/-- **`physStepBudget` is exactly superadditive under `seq`.** The `seq`
control step (`+1`) plus the two fragments' budgets land exactly on the
composed budget — this is the algebraic fact that makes the `seq` case of
`Compile.run_physical_residue_gen` close (and that the quadratic `overhead`
failed, ROADMAP Finding #3). -/
theorem Compile.physStepBudget_seq (G a b : Nat) :
    Compile.physStepBudget G a + 1 + Compile.physStepBudget G b
      = Compile.physStepBudget G (1 + a + b) := by
  simp only [Compile.physStepBudget]; ring

/-- `physStepBudget` is monotone in both the tape bound and the op count. -/
theorem Compile.physStepBudget_mono {G G' cost cost' : Nat}
    (hG : G ≤ G') (hc : cost ≤ cost') :
    Compile.physStepBudget G cost ≤ Compile.physStepBudget G' cost' := by
  unfold Compile.physStepBudget; gcongr

/-- The diagonal of `physStepBudget` is a cubic, hence `inOPoly`. With
`physStepBudget_mono` this is the interface the budget restatement (GAP 4) feeds to
`toFrameworkWitness'` in place of `overhead_poly`/`overhead_mono`. -/
theorem Compile.physStepBudget_poly :
    inOPoly (fun m => Compile.physStepBudget m m) := by
  refine ⟨3, 817, 1, ?_⟩
  intro m hm
  show Compile.physStepBudget m m ≤ 817 * m ^ 3
  have hm1 : 1 ≤ m := hm
  have h0 : (1 : Nat) ≤ m ^ 3 := by
    calc (1 : Nat) = m ^ 0 := by simp
      _ ≤ m ^ 3 := Nat.pow_le_pow_right hm1 (by norm_num)
  have h1 : m ≤ m ^ 3 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 3 := Nat.pow_le_pow_right hm1 (by norm_num)
  have h2 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right hm1 (by norm_num)
  have e : Compile.physStepBudget m m = 72 * m ^ 3 + 144 * m ^ 2 + 337 * m + 264 := by
    simp only [Compile.physStepBudget]; ring
  rw [e]; omega

/-- **Residue-tolerant `compileIfBit` contract (GAP 1 — pinned interface, `sorry`).**
The incoming-residue generalisation of `compileIfBit_sound_physical`
(`Compile.lean:8565`), in the shape the `ifBit` case of `run_physical_residue_gen`
needs: the chosen branch's residue run, threaded through the tester (`+3` control
steps) and the `joinTwoHalts` rewind bracket. Gated on a real `compileTestBit`
(today a 0-transition stub). The `+3 ≤` one extra `physStepBudget` unit, so the
budget composes with room. -/
theorem compileIfBit_sound_physical_residue
    (t : Var) (rT rE : CompiledCmd)
    (evalT evalE : State → State) (costT costE : State → Nat)
    (G : Nat) (s : State) (res0 : List Nat)
    -- `ht`/`hG` (added 2026-06-11): the tester must physically navigate to
    -- register `t` (so it must exist), and its step count is linear in the tape
    -- length, so the budget needs the tape bound `G`. Both are available at the
    -- single call site (`run_physical_residue_gen`: `huses.1` + its own `hG`).
    (ht : t < s.length)
    (hbit : Compile.BitState s) (hres0 : Compile.ValidResidue res0)
    (hG : State.size s + s.length + res0.length + 2 ≤ G)
    (hT : s.get t = [1] →
      ∃ (tt : Nat) (res : List Nat),
        Compile.ValidResidue res ∧
        State.size (evalT s) + res.length ≤ State.size s + res0.length + costT s ∧
        runFlatTM tt rT.M (initFlatConfig rT.M [Compile.encodeTape s ++ res0])
          = some { state_idx := rT.exit,
                   tapes := [([], 0, Compile.encodeTape (evalT s) ++ res)] } ∧
        (∀ k, k < tt → ∀ ck,
            runFlatTM k rT.M (initFlatConfig rT.M [Compile.encodeTape s ++ res0]) = some ck →
            ck.state_idx ≠ rT.exit ∧ haltingStateReached rT.M ck = false) ∧
        tt ≤ Compile.physStepBudget G (costT s))
    (hE : s.get t ≠ [1] →
      ∃ (tt : Nat) (res : List Nat),
        Compile.ValidResidue res ∧
        State.size (evalE s) + res.length ≤ State.size s + res0.length + costE s ∧
        runFlatTM tt rE.M (initFlatConfig rE.M [Compile.encodeTape s ++ res0])
          = some { state_idx := rE.exit,
                   tapes := [([], 0, Compile.encodeTape (evalE s) ++ res)] } ∧
        (∀ k, k < tt → ∀ ck,
            runFlatTM k rE.M (initFlatConfig rE.M [Compile.encodeTape s ++ res0]) = some ck →
            ck.state_idx ≠ rE.exit ∧ haltingStateReached rE.M ck = false) ∧
        tt ≤ Compile.physStepBudget G (costE s)) :
    let chosen := if s.get t = [1] then evalT s else evalE s
    let chosenCost := if s.get t = [1] then costT s else costE s
    ∃ (tt : Nat) (res : List Nat),
      Compile.ValidResidue res ∧
      State.size chosen + res.length ≤ State.size s + res0.length + (1 + chosenCost) ∧
      runFlatTM tt (compileIfBit t rT rE).M
          (initFlatConfig (compileIfBit t rT rE).M [Compile.encodeTape s ++ res0])
        = some { state_idx := (compileIfBit t rT rE).exit,
                 tapes := [([], 0, Compile.encodeTape chosen ++ res)] } ∧
      (∀ k, k < tt → ∀ ck,
          runFlatTM k (compileIfBit t rT rE).M
              (initFlatConfig (compileIfBit t rT rE).M [Compile.encodeTape s ++ res0]) = some ck →
          ck.state_idx ≠ (compileIfBit t rT rE).exit ∧
          haltingStateReached (compileIfBit t rT rE).M ck = false) ∧
      tt ≤ Compile.physStepBudget G (1 + chosenCost) := by
  -- The tester is REAL now (`compileTestBit`, 2026-06-11): navigate + read +
  -- rewind, leaving the tape unchanged with the head at `0`, so the chosen
  -- branch literally starts from its own `initFlatConfig`.
  intro chosen chosenCost
  set tester := compileTestBit t with htester
  set branched := branchComposeFlatTM tester.M rT.M rE.M tester.exitPos tester.exitNeg
    with hbranched
  set haltE := tester.M.states + rT.M.states + rE.exit with hhaltE
  set haltT := tester.M.states + rT.exit with hhaltT
  have hMeq : (compileIfBit t rT rE).M = Compile.joinTwoHalts branched haltE haltT := rfl
  have hexit_eq : (compileIfBit t rT rE).exit = haltE := rfl
  have hstart : (compileIfBit t rT rE).M.start = 0 := by
    rw [hMeq, Compile.joinTwoHalts_start, hbranched, branchComposeFlatTM_start]
    exact compileTestBit_start t
  have hinit : initFlatConfig (compileIfBit t rT rE).M [Compile.encodeTape s ++ res0]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res0)] } := by
    simp only [initFlatConfig, hstart, List.map_cons, List.map_nil]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res0)] }
    with hcfg0
  have hLG : (Compile.encodeTape s ++ res0).length ≤ G := by
    rw [List.length_append, Compile.encodeTape_length]; omega
  have hbudget0 : Compile.physStepBudget G 0 = (9 * G * G + 9 * G + 33) * 8 := by
    simp only [Compile.physStepBudget]; omega
  have hcfg0_lt : (0 : Nat) < tester.M.states :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) tester.exitPos_lt
  -- the seam symbol at head 0 is the leading sentinel `3`.
  have hsym3 : ∀ (s' : State) (res' : List Nat),
      currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s' ++ res') = some 3 := by
    intro s' res'
    rw [show Compile.encodeTape s' ++ res'
        = 3 :: (Compile.encodeRegs s' ++ [Compile.endMark] ++ res') from by
      rw [Compile.encodeTape]
      simp only [Compile.endMark, List.cons_append, List.append_assoc]]
    rfl
  have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res0) = some v →
      v < max tester.M.sig (max rT.M.sig rE.M.sig) := by
    intro v hv
    rw [hsym3 s res0] at hv
    obtain rfl : (3 : Nat) = v := Option.some.inj hv
    calc (3 : Nat) < 4 := by omega
      _ = tester.M.sig := tester.M_sig.symm
      _ ≤ _ := le_max_left _ _
  have hh1 : branched.halt[haltE]? = some true := by
    rw [hbranched, hhaltE]
    exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _ rT.M_valid rE.exit_is_halt
  have hh2 : branched.halt[haltT]? = some true := by
    rw [hbranched, hhaltT]
    exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _ rT.M_valid rT.exit_lt
      rT.exit_is_halt
  have hne : haltE ≠ haltT := by
    have := rT.exit_lt
    rw [hhaltE, hhaltT]
    omega
  by_cases hb : s.get t = [1]
  · -- TRUE branch: tester POS → `rT` → demoted `haltT` → bridge to `haltE`.
    obtain ⟨tt, res, hres, hW, hrun, htraj, hbud⟩ := hT hb
    obtain ⟨Tt, htest_run, htest_traj, htest_bud⟩ :=
      Compile.testBitReg_run_pos t s res0 ht hbit hb
    have hinitT : initFlatConfig rT.M [Compile.encodeTape s ++ res0]
        = { state_idx := rT.M.start, tapes := [([], 0, Compile.encodeTape s ++ res0)] } := by
      simp only [initFlatConfig, List.map_cons, List.map_nil]
    rw [hinitT] at hrun htraj
    have hraw := branchComposeFlatTM_run_pos tester.exit_distinct
      tester.M_valid rT.M_valid rE.M_valid tester.exitPos_lt tester.exitNeg_lt
      cfg0 hcfg0_lt [] 0 (Compile.encodeTape s ++ res0) hsymb
      htest_run htest_traj hrun
      (Compile.haltingStateReached_of_halt rT.exit_is_halt)
    have hraw_traj := branchComposeFlatTM_no_early_halt_pos
      tester.M_valid rT.M_valid rE.M_valid tester.exitPos_lt tester.exitNeg_lt
      cfg0 hcfg0_lt [] 0 (Compile.encodeTape s ++ res0) hsymb
      htest_run htest_traj
      (fun k hk ck hck => (htraj k hk ck hck).2)
    have hstate_eq : rT.exit + tester.M.states = haltT := by
      rw [hhaltT]; omega
    rw [hstate_eq] at hraw
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted branched haltE haltT
      cfg0 (Tt + 1 + tt) [] (Compile.encodeTape (evalT s) ++ res) 0
      hraw.1 (fun k hk ck hck => hraw_traj k hk ck hck) hh1 hh2 hne
      (by
        intro v hv
        rw [hsym3 (evalT s) res] at hv
        obtain rfl : (3 : Nat) = v := Option.some.inj hv
        rw [hbranched, branchComposeFlatTM_sig, tester.M_sig, rT.M_sig, rE.M_sig]
        decide)
    refine ⟨Tt + 1 + tt + 1, res, hres, ?_, ?_, ?_, ?_⟩
    · -- ① W-invariant.
      show State.size chosen + res.length ≤ State.size s + res0.length + (1 + chosenCost)
      simp only [chosen, chosenCost, if_pos hb]
      omega
    · -- run.
      rw [hinit, hMeq, hexit_eq]
      simp only [chosen, if_pos hb]
      exact hjoin
    · -- trajectory.
      intro k hk ck hck
      rw [hinit, hMeq] at hck
      obtain ⟨hne1, hnh⟩ := hjoin_traj k hk ck hck
      rw [hexit_eq, hMeq]
      exact ⟨hne1, hnh⟩
    · -- ② budget: tester (≤ 3·G+12) + bridges fit one extra `physStepBudget` unit.
      simp only [chosenCost, if_pos hb]
      rw [show (1 : Nat) + costT s = 1 + 0 + costT s from by omega,
          ← Compile.physStepBudget_seq G 0 (costT s)]
      omega
  · -- FALSE branch: tester NEG → `rE` → the kept `haltE` directly.
    obtain ⟨tt, res, hres, hW, hrun, htraj, hbud⟩ := hE hb
    obtain ⟨Tt, htest_run, htest_traj, htest_bud⟩ :=
      Compile.testBitReg_run_neg t s res0 ht hbit hb
    have hinitE : initFlatConfig rE.M [Compile.encodeTape s ++ res0]
        = { state_idx := rE.M.start, tapes := [([], 0, Compile.encodeTape s ++ res0)] } := by
      simp only [initFlatConfig, List.map_cons, List.map_nil]
    rw [hinitE] at hrun htraj
    have hraw := branchComposeFlatTM_run_neg tester.exit_distinct
      tester.M_valid rT.M_valid rE.M_valid tester.exitPos_lt tester.exitNeg_lt
      cfg0 hcfg0_lt [] 0 (Compile.encodeTape s ++ res0) hsymb
      htest_run htest_traj hrun
      (Compile.haltingStateReached_of_halt rE.exit_is_halt)
    have hraw_traj := branchComposeFlatTM_no_early_halt_neg tester.exit_distinct
      tester.M_valid rT.M_valid rE.M_valid tester.exitPos_lt tester.exitNeg_lt
      cfg0 hcfg0_lt [] 0 (Compile.encodeTape s ++ res0) hsymb
      htest_run htest_traj
      (fun k hk ck hck => (htraj k hk ck hck).2)
    have hstate_eq : rE.exit + (tester.M.states + rT.M.states) = haltE := by
      rw [hhaltE]; omega
    rw [hstate_eq] at hraw
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept branched haltE haltT
      cfg0 (Tt + 1 + tt) ([], 0, Compile.encodeTape (evalE s) ++ res)
      hraw.1 (fun k hk ck hck => hraw_traj k hk ck hck) hh1 hh2
    refine ⟨Tt + 1 + tt, res, hres, ?_, ?_, ?_, ?_⟩
    · show State.size chosen + res.length ≤ State.size s + res0.length + (1 + chosenCost)
      simp only [chosen, chosenCost, if_neg hb]
      omega
    · rw [hinit, hMeq, hexit_eq]
      simp only [chosen, if_neg hb]
      exact hjoin
    · intro k hk ck hck
      rw [hinit, hMeq] at hck
      obtain ⟨hne1, hnh⟩ := hjoin_traj k hk ck hck
      rw [hexit_eq, hMeq]
      exact ⟨hne1, hnh⟩
    · simp only [chosenCost, if_neg hb]
      rw [show (1 : Nat) + costE s = 1 + 0 + costE s from by omega,
          ← Compile.physStepBudget_seq G 0 (costE s)]
      omega


/-- **★ Per-iteration run of the `forBnd` bookkeeping chain (TM-level W-invariant
validation).** On a `BitState` input whose `K1 = sb` register is nonempty (the
guard passed), `forBndIterate` reaches its exit on `forBndIterateState …`, with a
residue whose joint size+length growth is bounded by the iteration's cost
contribution `|K2| + body.cost (s.set counter K2) + 1` (the **W-invariant ①** — the
key accounting claim) and a cubic step budget. Discharged from the four PROVEN op
run lemmas (`opCopy_run` / the body contract `hbody` / `opAppendBit_physical_residue`
/ `opTailSelf_run_delete`) composed by `compileSeq_sound_physical_residue`. The
body contract `hbody` is verbatim `compileForBnd_sound_physical_residue`'s, so the
loop assembly threads it straight through. -/
theorem Compile.forBndIterate_run
    (counter sb : Var) (rbody : CompiledCmd) (body : Cmd)
    (s : State) (res : List Nat) (G : Nat)
    (hbit : Compile.BitState s)
    (hcnt : counter < sb)
    (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (hsbne : State.get s sb ≠ [])
    (hres : Compile.ValidResidue res)
    (huses_body : Cmd.UsesBelow body sb)
    (hscr : ∀ r, sb + 2 ≤ r → State.get s r = [])
    (hG : State.size s + s.length + res.length
            + ((State.get s (sb + 1)).length
               + body.cost (s.set counter (State.get s (sb + 1))) + 1) + 2 ≤ G)
    (hbody : ∀ (s' : State) (res' : List Nat) (G' : Nat),
      Compile.BitState s' → sb + 2 + 2 * body.loopDepth + 2 ≤ s'.length →
      (∀ r, sb + 2 ≤ r → State.get s' r = []) →
      Compile.ValidResidue res' →
      State.size s' + s'.length + res'.length + body.cost s' + 2 ≤ G' →
      ∃ (tt : Nat) (resb : List Nat),
        Compile.ValidResidue resb ∧
        State.size (body.eval s') + resb.length ≤ State.size s' + res'.length + body.cost s' ∧
        runFlatTM tt rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res'])
          = some { state_idx := rbody.exit,
                   tapes := [([], 0, Compile.encodeTape (body.eval s') ++ resb)] } ∧
        (∀ kk, kk < tt → ∀ ck,
            runFlatTM kk rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res']) = some ck →
            ck.state_idx ≠ rbody.exit ∧ haltingStateReached rbody.M ck = false) ∧
        tt ≤ Compile.physStepBudget G' (body.cost s')) :
    ∃ (t : Nat) (res' : List Nat),
      Compile.ValidResidue res' ∧
      State.size (Compile.forBndIterateState counter sb body s) + res'.length
        ≤ State.size s + res.length
          + ((State.get s (sb + 1)).length
             + body.cost (s.set counter (State.get s (sb + 1))) + 1) ∧
      runFlatTM t (Compile.forBndIterate counter sb rbody).M
          (initFlatConfig (Compile.forBndIterate counter sb rbody).M [Compile.encodeTape s ++ res])
        = some { state_idx := (Compile.forBndIterate counter sb rbody).exit,
                 tapes := [([], 0,
                   Compile.encodeTape (Compile.forBndIterateState counter sb body s) ++ res')] } ∧
      (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.forBndIterate counter sb rbody).M
              (initFlatConfig (Compile.forBndIterate counter sb rbody).M
                [Compile.encodeTape s ++ res]) = some ck →
          ck.state_idx ≠ (Compile.forBndIterate counter sb rbody).exit ∧
          haltingStateReached (Compile.forBndIterate counter sb rbody).M ck = false) ∧
      t ≤ (9 * G * G + 9 * G + 30) * ((State.get s (sb + 1)).length + 2)
          + Compile.physStepBudget G (body.cost (s.set counter (State.get s (sb + 1))))
          + 9 * G + 25 := by
  -- ### length facts (every op writes a register `< s.length`, so widths are constant `= s.length`)
  -- (`sb`/`counter : Var` are opaque to `omega`; derive the order facts with `Nat.*` lemmas)
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  have hcnt_lt : counter < s.length := Nat.lt_trans hcnt hsb_lt
  -- BitState of a register read in range
  have hbit_reg : ∀ (r : Var), r < s.length → ∀ x ∈ State.get s r, x ≤ 1 := by
    intro r hr x hx
    refine hbit (State.get s r) ?_ x hx
    rw [State.get, List.getElem?_eq_getElem hr]; exact List.getElem_mem hr
  -- ### s1 := copy counter K2
  set s1 : State := s.set counter (State.get s (sb + 1)) with hs1def
  have hbit1 : Compile.BitState s1 :=
    Compile.BitState_set s counter _ hbit hcnt_lt (hbit_reg (sb + 1) hsb1_lt)
  have hlen1 : s1.length = s.length := Compile.length_set s counter _ hcnt_lt
  have hget1_sb : State.get s1 sb = State.get s sb :=
    Compile.get_set_ne s counter _ sb hcnt_lt (Ne.symm (Nat.ne_of_lt hcnt))
  have hsize1 : State.size s1 + (State.get s counter).length
      = State.size s + (State.get s (sb + 1)).length := State.size_set_add s counter _
  -- residue after copy
  have hres1 : Compile.ValidResidue (res ++ List.replicate (State.get s counter).length 0) :=
    Compile.ValidResidue_append_replicate_zero res _ hres
  -- ### body contract instantiation at (s1, res1, G)
  have hlen1' : sb + 2 + 2 * body.loopDepth + 2 ≤ s1.length := by rw [hlen1]; exact hlen
  have hscr1 : ∀ r, sb + 2 ≤ r → State.get s1 r = [] := by
    intro r hr
    rw [hs1def, Compile.get_set_ne s counter _ r hcnt_lt
      (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hcnt (Nat.le_trans (Nat.le_add_right sb 2) hr))))]
    exact hscr r hr
  have hbodyG : State.size s1 + s1.length
      + (res ++ List.replicate (State.get s counter).length 0).length + body.cost s1 + 2 ≤ G := by
    rw [hlen1, List.length_append, List.length_replicate]
    -- `omega` from `hsize1` (State.size s1 balance) + `hG`; all atoms are `Nat` (no bare `sb`)
    omega
  obtain ⟨tb, resb, hresb, hWbody, hrunb, htrajb, hbudb⟩ :=
    hbody s1 (res ++ List.replicate (State.get s counter).length 0) G
      hbit1 hlen1' hscr1 hres1 hbodyG
  -- ### s2 := body.eval s1
  set s2 : State := body.eval s1 with hs2def
  have hbit2 : Compile.BitState s2 :=
    Cmd.eval_preserves_BitState body sb s1 huses_body
      (by rw [hlen1]; exact Nat.le_of_lt hsb_lt) hbit1
  have hs2len_ge : s1.length ≤ s2.length := Cmd.eval_length_ge body s1
  have hget2_sb : State.get s2 sb = State.get s sb := by
    rw [hs2def, Cmd.eval_get_frame body sb huses_body s1 sb (Nat.le_refl _), hget1_sb]
  have hsb1_lt2 : sb + 1 < s2.length := Nat.lt_of_lt_of_le hsb1_lt (hlen1 ▸ hs2len_ge)
  -- ### s3 := appendOne K2  (= s2.set (sb+1) (s2.get (sb+1) ++ [1]))
  set s3 : State := s2.set (sb + 1) (State.get s2 (sb + 1) ++ [1]) with hs3def
  have hbit2_reg : ∀ x ∈ State.get s2 (sb + 1), x ≤ 1 := by
    intro x hx
    refine hbit2 (State.get s2 (sb + 1)) ?_ x hx
    rw [State.get, List.getElem?_eq_getElem hsb1_lt2]; exact List.getElem_mem hsb1_lt2
  have hbit3 : Compile.BitState s3 := by
    rw [hs3def]
    exact Compile.BitState_set s2 (sb + 1) _ hbit2 hsb1_lt2
      (by intro x hx; rcases List.mem_append.mp hx with h | h
          · exact hbit2_reg x h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega)
  have hsize3 : State.size s3 + (State.get s2 (sb + 1)).length
      = State.size s2 + (State.get s2 (sb + 1) ++ [1]).length := by
    rw [hs3def]; exact State.size_set_add s2 (sb + 1) _
  have hget3_sb : State.get s3 sb = State.get s sb := by
    rw [hs3def, Compile.get_set_ne s2 (sb + 1) _ sb hsb1_lt2
      (Nat.ne_of_lt (Nat.lt_succ_self sb)), hget2_sb]
  have hsb_lt3 : sb < s3.length := by
    rw [hs3def]
    refine Nat.lt_of_lt_of_le hsb_lt ?_
    have h1 : s.length ≤ s2.length := hlen1 ▸ hs2len_ge
    exact Nat.le_trans h1 (State.set_length_ge s2 (sb + 1) _)
  -- ### s4 := tail K1 K1  (= s3.set sb (s3.get sb).tail)
  have hsbne3 : State.get s3 sb ≠ [] := by rw [hget3_sb]; exact hsbne
  -- the four op runs ------------------------------------------------------------
  -- (A) copy counter (sb+1)
  obtain ⟨tA, hrunA, htrajA, hbudA⟩ :=
    Compile.opCopy_run s counter (sb + 1)
      (Nat.ne_of_lt (Nat.lt_trans hcnt (Nat.lt_succ_self sb))) hcnt_lt hsb1_lt hbit res hres
  -- (C) appendOne (sb+1) on s2
  obtain ⟨tC, hrunC, htrajC, hbudC⟩ :=
    Compile.opAppendBit_physical_residue 1 (by omega) s2 (sb + 1) hbit2 hsb1_lt2 resb hresb
  -- (D) tail sb sb on s3
  obtain ⟨tD, hrunD, htrajD, hbudD⟩ :=
    Compile.opTailSelf_run_delete s3 sb hsb_lt3 hbit3 hsbne3 resb hresb
  -- output state equalities
  have hs4def : Compile.forBndIterateState counter sb body s
      = s3.set sb (State.get s3 sb).tail := rfl
  -- halts of the inner exits (for `compileSeq` `h_halt2`)
  have hhaltD : haltingStateReached (Compile.opTail sb sb).M
      { state_idx := (Compile.opTail sb sb).exit,
        tapes := [([], 0, Compile.encodeTape (s3.set sb (State.get s3 sb).tail) ++ (resb ++ [0]))] }
      = true := by
    have hex := (Compile.opTail sb sb).exit_is_halt
    show (Compile.opTail sb sb).M.halt.getD (Compile.opTail sb sb).exit false = true
    simp only [List.getD, hex, Option.getD]
  -- compose D-level inner `appendOne ⨾ tail` (input s2)
  set CD := compileSeq (Compile.opAppendBitRewind (1 + 1) (by omega) (sb + 1))
    (Compile.opTail sb sb) with hCDdef
  obtain ⟨hrunCD, hhaltCD⟩ :=
    compileSeq_sound_physical_residue
      (Compile.opAppendBitRewind (1 + 1) (by omega) (sb + 1)) (Compile.opTail sb sb)
      s2 s3 (s3.set sb (State.get s3 sb).tail) resb resb (resb ++ [0])
      hbit3 hresb hrunC htrajC hrunD hhaltD
  have htrajCD := compileSeq_traj_physical_residue
      (Compile.opAppendBitRewind (1 + 1) (by omega) (sb + 1)) (Compile.opTail sb sb)
      s2 s3 resb resb hbit3 hresb hrunC htrajC htrajD
  -- compose B-level `rbody ⨾ CD` (input s1)
  set BCD := compileSeq rbody CD with hBCDdef
  obtain ⟨hrunBCD, hhaltBCD⟩ :=
    compileSeq_sound_physical_residue rbody CD
      s1 s2 (s3.set sb (State.get s3 sb).tail)
      (res ++ List.replicate (State.get s counter).length 0) resb (resb ++ [0])
      hbit2 hresb hrunb htrajb hrunCD hhaltCD
  have htrajBCD := compileSeq_traj_physical_residue rbody CD
      s1 s2 (res ++ List.replicate (State.get s counter).length 0) resb
      hbit2 hresb hrunb htrajb htrajCD
  -- compose A-level `copy ⨾ BCD` (input s)
  obtain ⟨hrunAll, hhaltAll⟩ :=
    compileSeq_sound_physical_residue (Compile.opCopy counter (sb + 1)) BCD
      s s1 (s3.set sb (State.get s3 sb).tail)
      res (res ++ List.replicate (State.get s counter).length 0) (resb ++ [0])
      hbit1 hres1 hrunA htrajA hrunBCD hhaltBCD
  have htrajAll := compileSeq_traj_physical_residue (Compile.opCopy counter (sb + 1)) BCD
      s s1 res (res ++ List.replicate (State.get s counter).length 0)
      hbit1 hres1 hrunA htrajA htrajBCD
  -- ### assemble the existential
  refine ⟨tA + 1 + (tb + 1 + (tC + 1 + tD)), resb ++ [0],
    Compile.ValidResidue_append_replicate_zero resb 1 hresb, ?_, ?_, ?_, ?_⟩
  · -- ① W-invariant telescoping
    rw [hs4def, List.length_append, List.length_singleton]
    -- size after tail
    have hsize4 : State.size (s3.set sb (State.get s3 sb).tail) + (State.get s3 sb).length
        = State.size s3 + (State.get s3 sb).tail.length := State.size_set_add s3 sb _
    have htail_len : (State.get s3 sb).tail.length + 1 = (State.get s3 sb).length := by
      rw [List.length_tail]
      have : 1 ≤ (State.get s3 sb).length := by
        rcases hsbne3' : State.get s3 sb with _ | ⟨a, l⟩
        · exact absurd hsbne3' hsbne3
        · simp
      omega
    rw [List.length_append, List.length_replicate] at hWbody
    -- equations: hsize1, hsize3, hsize4, htail_len, hWbody (le); all atoms `Nat` (no bare `sb`)
    have e3 := hsize3
    rw [List.length_append, List.length_singleton] at e3
    omega
  · -- run
    rw [hs4def]
    exact hrunAll
  · -- trajectory
    exact htrajAll
  · -- ② budget: each op tape `≤ G`, then sum (all atoms `Nat`)
    rw [List.length_append, List.length_replicate] at hWbody
    have hslen2 : s2.length ≤ s.length := by
      rw [hs2def]
      exact Nat.le_trans (Cmd.eval_length_le body sb huses_body s1)
        (by rw [hlen1]; exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_of_lt hsb_lt⟩)
    have hslen3 : s3.length ≤ s.length := by
      rw [hs3def]
      exact Nat.le_trans (State.set_length_le s2 (sb + 1) _)
        (Nat.max_le.mpr ⟨hslen2, hsb1_lt⟩)
    have e3 := hsize3
    rw [List.length_append, List.length_singleton] at e3
    have hL : (Compile.encodeTape s ++ res).length ≤ G := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    -- ⚠ keep the copy SOURCE length `|K2| = (s.get (sb+1)).length` explicit (do NOT
    -- bound it by `G`): the loop sum `Σ_{i<iters}(|K2_i|+2) = Σ(i+2) ~ iters²/2`
    -- fits under `physStepBudget`'s `8·iters²` headroom, whereas a per-iteration
    -- `(G+2)` factor sums to `iters·G³` and overdraws (see `forBndLoop_run`).
    have hbA : tA ≤ (9 * G * G + 9 * G + 30) * ((State.get s (sb + 1)).length + 2) :=
      Nat.le_trans hbudA (Nat.mul_le_mul
        (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 9 hL) hL)
          (Nat.mul_le_mul_left 9 hL)) (Nat.le_refl 30)) (Nat.le_refl _))
    have hLa : (Compile.encodeTape s2 ++ resb).length ≤ G := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    have hbC : tC ≤ 3 * G + 8 := Nat.le_trans hbudC (by omega)
    have hLt : (Compile.encodeTape s3 ++ resb).length ≤ G := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    have hbD : tD ≤ 6 * G + 14 := Nat.le_trans hbudD (by omega)
    set A := (9 * G * G + 9 * G + 30) * ((State.get s (sb + 1)).length + 2) with hAdef
    set B := Compile.physStepBudget G (body.cost s1) with hBdef
    omega

/-! ### `forBndIterateState` fold invariants (for the loop induction)

The loop induction (`compileForBnd_sound_physical_residue`, GAP 1d) threads the
preconditions of `forBndBody_iterate_run` / `forBndBody_done_run` along the state
fold `A 0 = s`, `A (i+1) = forBndIterateState counter sb body (A i)`. These lemmas
discharge the inductive step: each iteration **decrements `K1 = sb` by exactly one
cell** (so `|K1|` counts down to the done branch) and **leaves every scratch
register `≥ sb + 2` untouched** (so the body contract `hbody` re-applies, and the
nested loops' scratch survives). `length`/`BitState` preservation are derived
inline in `forBndIterate_run`; re-export here for the induction. -/

/-- One iteration decrements `K1 = sb` by its head cell (the loop counter). -/
theorem Compile.forBndIterateState_get_sb (counter sb : Var) (body : Cmd) (s : State)
    (hcnt : counter < sb) (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (huses_body : Cmd.UsesBelow body sb) :
    State.get (Compile.forBndIterateState counter sb body s) sb = (State.get s sb).tail := by
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  have hcnt_lt : counter < s.length := Nat.lt_trans hcnt hsb_lt
  set s1 : State := s.set counter (State.get s (sb + 1)) with hs1def
  have hlen1 : s1.length = s.length := Compile.length_set s counter _ hcnt_lt
  set s2 : State := body.eval s1 with hs2def
  have hs2len_ge : s1.length ≤ s2.length := Cmd.eval_length_ge body s1
  set s3 : State := s2.set (sb + 1) (State.get s2 (sb + 1) ++ [1]) with hs3def
  have hget1_sb : State.get s1 sb = State.get s sb :=
    Compile.get_set_ne s counter _ sb hcnt_lt (Ne.symm (Nat.ne_of_lt hcnt))
  have hget2_sb : State.get s2 sb = State.get s sb := by
    rw [hs2def, Cmd.eval_get_frame body sb huses_body s1 sb (Nat.le_refl _), hget1_sb]
  have hget3_sb : State.get s3 sb = State.get s sb := by
    have hsb1_lt2 : sb + 1 < s2.length := Nat.lt_of_lt_of_le hsb1_lt (hlen1 ▸ hs2len_ge)
    rw [hs3def, Compile.get_set_ne s2 (sb + 1) _ sb hsb1_lt2 (Nat.ne_of_lt (Nat.lt_succ_self sb)),
        hget2_sb]
  have hsb_lt3 : sb < s3.length := by
    rw [hs3def]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hsb_lt (hlen1 ▸ hs2len_ge))
      (State.set_length_ge s2 (sb + 1) _)
  show State.get (s3.set sb (State.get s3 sb).tail) sb = (State.get s sb).tail
  rw [Compile.get_set_eq s3 sb _ hsb_lt3, hget3_sb]

/-- One iteration leaves every scratch register `≥ sb + 2` empty (it writes only
`counter < sb`, `K1 = sb`, `K2 = sb + 1`, and the body's registers `< sb`). -/
theorem Compile.forBndIterateState_scratch (counter sb : Var) (body : Cmd) (s : State)
    (hcnt : counter < sb) (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (huses_body : Cmd.UsesBelow body sb)
    (hscr : ∀ r, sb + 2 ≤ r → State.get s r = []) :
    ∀ r, sb + 2 ≤ r → State.get (Compile.forBndIterateState counter sb body s) r = [] := by
  intro r hr
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  have hcnt_lt : counter < s.length := Nat.lt_trans hcnt hsb_lt
  set s1 : State := s.set counter (State.get s (sb + 1)) with hs1def
  have hlen1 : s1.length = s.length := Compile.length_set s counter _ hcnt_lt
  set s2 : State := body.eval s1 with hs2def
  have hs2len_ge : s1.length ≤ s2.length := Cmd.eval_length_ge body s1
  set s3 : State := s2.set (sb + 1) (State.get s2 (sb + 1) ++ [1]) with hs3def
  -- `r` differs from each written register (`Var` is opaque to omega — use `Nat.*`)
  have hsb_le_r : sb ≤ r := Nat.le_trans (Nat.le_add_right sb 2) hr
  have hcnt_lt_r : counter < r := Nat.lt_of_lt_of_le hcnt hsb_le_r
  have hsb_lt_r : sb < r :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self sb)
      (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right sb 1)) hr)
  have hsb1_lt_r : sb + 1 < r := Nat.lt_of_lt_of_le (Nat.lt_succ_self (sb + 1)) hr
  have hr_ne_cnt : r ≠ counter := Ne.symm (Nat.ne_of_lt hcnt_lt_r)
  have hr_ne_sb : r ≠ sb := Ne.symm (Nat.ne_of_lt hsb_lt_r)
  have hr_ne_sb1 : r ≠ sb + 1 := Ne.symm (Nat.ne_of_lt hsb1_lt_r)
  have hget1_r : State.get s1 r = State.get s r :=
    Compile.get_set_ne s counter _ r hcnt_lt hr_ne_cnt
  have hget2_r : State.get s2 r = State.get s r := by
    rw [hs2def, Cmd.eval_get_frame body sb huses_body s1 r hsb_le_r, hget1_r]
  have hsb1_lt2 : sb + 1 < s2.length := Nat.lt_of_lt_of_le hsb1_lt (hlen1 ▸ hs2len_ge)
  have hget3_r : State.get s3 r = State.get s r := by
    rw [hs3def, Compile.get_set_ne s2 (sb + 1) _ r hsb1_lt2 hr_ne_sb1, hget2_r]
  have hsb_lt3 : sb < s3.length := by
    rw [hs3def]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hsb_lt (hlen1 ▸ hs2len_ge))
      (State.set_length_ge s2 (sb + 1) _)
  show State.get (s3.set sb (State.get s3 sb).tail) r = []
  rw [Compile.get_set_ne s3 sb _ r hsb_lt3 hr_ne_sb, hget3_r]
  exact hscr r hr

/-- One iteration appends `[1]` to `K2 = sb+1` (the done count). With `K2` empty at
loop entry this gives `|K2_i| = i` (the `i`-th iteration's copy-source length) — the
explicit factor the loop budget sum needs. -/
theorem Compile.forBndIterateState_get_sb1 (counter sb : Var) (body : Cmd) (s : State)
    (hcnt : counter < sb) (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (huses_body : Cmd.UsesBelow body sb) :
    State.get (Compile.forBndIterateState counter sb body s) (sb + 1)
      = State.get s (sb + 1) ++ [1] := by
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  have hcnt_lt : counter < s.length := Nat.lt_trans hcnt hsb_lt
  set s1 : State := s.set counter (State.get s (sb + 1)) with hs1def
  have hlen1 : s1.length = s.length := Compile.length_set s counter _ hcnt_lt
  set s2 : State := body.eval s1 with hs2def
  have hs2len_ge : s1.length ≤ s2.length := Cmd.eval_length_ge body s1
  have hsb1_lt2 : sb + 1 < s2.length := Nat.lt_of_lt_of_le hsb1_lt (hlen1 ▸ hs2len_ge)
  set s3 : State := s2.set (sb + 1) (State.get s2 (sb + 1) ++ [1]) with hs3def
  have hget1_sb1 : State.get s1 (sb + 1) = State.get s (sb + 1) :=
    Compile.get_set_ne s counter _ (sb + 1) hcnt_lt
      (Ne.symm (Nat.ne_of_lt (Nat.lt_trans hcnt (Nat.lt_succ_self sb))))
  have hget2_sb1 : State.get s2 (sb + 1) = State.get s (sb + 1) := by
    rw [hs2def, Cmd.eval_get_frame body sb huses_body s1 (sb + 1) (Nat.le_succ sb), hget1_sb1]
  have hget3_sb1 : State.get s3 (sb + 1) = State.get s (sb + 1) ++ [1] := by
    rw [hs3def, Compile.get_set_eq s2 (sb + 1) _ hsb1_lt2, hget2_sb1]
  have hsb_lt3 : sb < s3.length := by
    rw [hs3def]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hsb_lt (hlen1 ▸ hs2len_ge))
      (State.set_length_ge s2 (sb + 1) _)
  show State.get (s3.set sb (State.get s3 sb).tail) (sb + 1) = State.get s (sb + 1) ++ [1]
  rw [Compile.get_set_ne s3 sb _ (sb + 1) hsb_lt3 (Nat.succ_ne_self sb), hget3_sb1]

/-- One iteration cannot shrink the register count (every write is in range). -/
theorem Compile.forBndIterateState_length_ge (counter sb : Var) (body : Cmd) (s : State)
    (hcnt : counter < sb) (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length) :
    s.length ≤ (Compile.forBndIterateState counter sb body s).length := by
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  have hcnt_lt : counter < s.length := Nat.lt_trans hcnt hsb_lt
  set s1 : State := s.set counter (State.get s (sb + 1)) with hs1def
  have hlen1 : s1.length = s.length := Compile.length_set s counter _ hcnt_lt
  set s2 : State := body.eval s1 with hs2def
  have hs2len_ge : s1.length ≤ s2.length := Cmd.eval_length_ge body s1
  set s3 : State := s2.set (sb + 1) (State.get s2 (sb + 1) ++ [1]) with hs3def
  show s.length ≤ (s3.set sb (State.get s3 sb).tail).length
  refine Nat.le_trans ?_ (State.set_length_ge s3 sb _)
  rw [hs3def]
  exact Nat.le_trans (hlen1 ▸ hs2len_ge) (State.set_length_ge s2 (sb + 1) _)

/-- One iteration preserves `BitState` (every write stores a `≤ 1`-valued list, and
the body preserves it by `Cmd.eval_preserves_BitState`). -/
theorem Compile.forBndIterateState_bitState (counter sb : Var) (body : Cmd) (s : State)
    (hbit : Compile.BitState s) (hcnt : counter < sb)
    (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (huses_body : Cmd.UsesBelow body sb) :
    Compile.BitState (Compile.forBndIterateState counter sb body s) := by
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  have hcnt_lt : counter < s.length := Nat.lt_trans hcnt hsb_lt
  have hbit_reg : ∀ (rr : Var), rr < s.length → ∀ x ∈ State.get s rr, x ≤ 1 := by
    intro rr hrr x hx
    refine hbit (State.get s rr) ?_ x hx
    rw [State.get, List.getElem?_eq_getElem hrr]; exact List.getElem_mem hrr
  set s1 : State := s.set counter (State.get s (sb + 1)) with hs1def
  have hbit1 : Compile.BitState s1 :=
    Compile.BitState_set s counter _ hbit hcnt_lt (hbit_reg (sb + 1) hsb1_lt)
  have hlen1 : s1.length = s.length := Compile.length_set s counter _ hcnt_lt
  set s2 : State := body.eval s1 with hs2def
  have hbit2 : Compile.BitState s2 :=
    Cmd.eval_preserves_BitState body sb s1 huses_body
      (by rw [hlen1]; exact Nat.le_of_lt hsb_lt) hbit1
  have hs2len_ge : s1.length ≤ s2.length := Cmd.eval_length_ge body s1
  have hsb1_lt2 : sb + 1 < s2.length := Nat.lt_of_lt_of_le hsb1_lt (hlen1 ▸ hs2len_ge)
  set s3 : State := s2.set (sb + 1) (State.get s2 (sb + 1) ++ [1]) with hs3def
  have hbit2_reg : ∀ x ∈ State.get s2 (sb + 1), x ≤ 1 := by
    intro x hx
    refine hbit2 (State.get s2 (sb + 1)) ?_ x hx
    rw [State.get, List.getElem?_eq_getElem hsb1_lt2]; exact List.getElem_mem hsb1_lt2
  have hbit3 : Compile.BitState s3 := by
    rw [hs3def]
    exact Compile.BitState_set s2 (sb + 1) _ hbit2 hsb1_lt2
      (by intro x hx; rcases List.mem_append.mp hx with h | h
          · exact hbit2_reg x h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega)
  have hsb_lt3 : sb < s3.length := by
    rw [hs3def]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hsb_lt (hlen1 ▸ hs2len_ge))
      (State.set_length_ge s2 (sb + 1) _)
  have hbit3_sb : ∀ x ∈ (State.get s3 sb).tail, x ≤ 1 := by
    intro x hx
    refine hbit3 (State.get s3 sb) ?_ x (List.mem_of_mem_tail hx)
    rw [State.get, List.getElem?_eq_getElem hsb_lt3]; exact List.getElem_mem hsb_lt3
  show Compile.BitState (s3.set sb (State.get s3 sb).tail)
  exact Compile.BitState_set s3 sb _ hbit3 hsb_lt3 hbit3_sb

/-- **★ The fold-invariant induction (for `forBndLoop_run`).** Along the loop's
state fold `A i = (forBndIterateState …)^[i] s`, for every `i ≤ iters` (where
`iters = |K1| = (s.get sb).length`): `A i` is a `BitState` with scratch `≥ sb+2`
empty, register count `≥ sb+2+2·loopDepth`, `K1` of length `iters−i` (counts down
to the done branch at `i = iters`), and `K2` of length `i` (the `i`-th iteration's
copy-source length — the explicit factor the budget sum needs). Discharged by the
five `forBndIterateState_*` fold invariants. `K2` empty at entry (`hk2`) is what
makes `|K2_i| = i`. -/
theorem Compile.forBndLoop_invariant (counter sb : Var) (body : Cmd) (s : State)
    (hbit : Compile.BitState s) (hcnt : counter < sb)
    (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (huses_body : Cmd.UsesBelow body sb) 
    (hscr : ∀ r, sb + 2 ≤ r → State.get s r = [])
    (hk2 : State.get s (sb + 1) = []) :
    ∀ i, i ≤ (State.get s sb).length →
      Compile.BitState ((Compile.forBndIterateState counter sb body)^[i] s) ∧
      (∀ r, sb + 2 ≤ r →
        State.get ((Compile.forBndIterateState counter sb body)^[i] s) r = []) ∧
      sb + 2 + 2 * body.loopDepth + 2
        ≤ ((Compile.forBndIterateState counter sb body)^[i] s).length ∧
      (State.get ((Compile.forBndIterateState counter sb body)^[i] s) sb).length
        = (State.get s sb).length - i ∧
      (State.get ((Compile.forBndIterateState counter sb body)^[i] s) (sb + 1)).length = i := by
  intro i
  induction i with
  | zero =>
      intro _
      simp only [Function.iterate_zero, id_eq]
      exact ⟨hbit, hscr, hlen, by omega, by rw [hk2]; rfl⟩
  | succ i ih =>
      intro hi
      obtain ⟨hb, hsc, hl, hk1, hk2i⟩ := ih (Nat.le_of_succ_le hi)
      set a := (Compile.forBndIterateState counter sb body)^[i] s with hadef
      have hstep : (Compile.forBndIterateState counter sb body)^[i + 1] s
          = Compile.forBndIterateState counter sb body a := by
        rw [Function.iterate_succ_apply', ← hadef]
      rw [hstep]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact Compile.forBndIterateState_bitState counter sb body a hb hcnt hl huses_body
      · exact Compile.forBndIterateState_scratch counter sb body a hcnt hl huses_body hsc
      · exact Nat.le_trans hl (Compile.forBndIterateState_length_ge counter sb body a hcnt hl)
      · rw [Compile.forBndIterateState_get_sb counter sb body a hcnt hl huses_body,
            List.length_tail, hk1]
        omega
      · rw [Compile.forBndIterateState_get_sb1 counter sb body a hcnt hl huses_body]
        simp [hk2i]


/-! #### Loop body run lemmas (the `loopTM_run` contracts)

`forBndBody_done_run` is the **done contract** (register `K1 = sb` empty ⇒ rewind
and stop), structurally identical to `clearBody_done_run` with the content slot
swapped to `forBndContentTM`. The **iteration contract** (`forBndBody_iterate_run`,
next bottom-up step) composes `navigateAndTestTM_run_content` → the content branch
`justRewindTM`-rewind → `forBndIterate_run`. -/

/-- **`forBnd` loop body — done branch.** When register `K1 = sb` is empty, the
loop body navigates to it, finds the delimiter `0` (empty ⇒ delim branch), and
rewinds to head `0`, leaving the tape unchanged and landing at
`forBndBodyTM_exitDone`. Built by `branchComposeFlatTM_run_neg` over
`navigateAndTestTM_run_delim` and `rewindToStart_run` (`justRewindTM`). -/
theorem Compile.forBndBody_done_run (counter sb : Var) (rbody : CompiledCmd)
    (s : State) (res : List Nat)
    (h : sb < s.length) (hbit : Compile.BitState s) (hempty : s.get sb = [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.forBndBodyTM counter sb rbody)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.forBndBodyTM_exitDone counter sb rbody,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.forBndBodyTM counter sb rbody)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.forBndBodyTM_exitDone counter sb rbody ∧
          ck.state_idx ≠ Compile.forBndBodyTM_exitLoop counter sb rbody ∧
          haltingStateReached (Compile.forBndBodyTM counter sb rbody) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s sb h
  have hbit_take : Compile.BitState (s.take sb) :=
    fun reg hreg => hbit reg (List.mem_of_mem_take hreg)
  set skipped : List (List Nat) := (s.take sb).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take sb) :=
    Compile.regBlocks_map_shiftReg (s.take sb)
  have hsklen : skipped.length = sb := by
    rw [hskdef, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt h)]
  have hskip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    rw [hskdef]; intro b hb
    rw [List.mem_map] at hb
    obtain ⟨reg, hreg, rfl⟩ := hb
    have hregmem : reg ∈ s := List.mem_of_mem_take hreg
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; omega
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      have : y ≤ 1 := hbit reg hregmem y hy; omega
  set tail' : List Nat :=
    Compile.encodeRegs (s.drop (sb + 1)) ++ [Compile.endMark] ++ res with htaildef
  have htape_nav : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    rw [hs, hempty, hregBlocks, htaildef]
    simp [Compile.shiftReg, Compile.endMark, List.append_assoc]
  have h_rb_le : (AppendGadget.regBlocks skipped).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [htape_nav]; simp only [List.length_cons, List.length_append]; omega
  have h_nav_le : ClearGadget.navSteps skipped ≤ 2 * (AppendGadget.regBlocks skipped).length + 1 :=
    ClearGadget.navSteps_le skipped
  have hrb : ∀ x ∈ AppendGadget.regBlocks skipped, x < 4 ∧ x ≠ 3 := by
    rw [hregBlocks]; intro x hx
    exact ⟨Compile.encodeRegs_lt_four (s.take sb) hbit_take x hx,
           Compile.encodeRegs_no_endMark (s.take sb) hbit_take x hx⟩
  have hpref : ∀ x ∈ AppendGadget.regBlocks skipped ++ [0], x < 4 ∧ x ≠ 3 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrb x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  have hrestsplit : AppendGadget.regBlocks skipped ++ 0 :: tail'
      = (AppendGadget.regBlocks skipped ++ [0]) ++ tail' := by simp [List.append_assoc]
  have h_rewind := ScanLeft.rewindToStart_run 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind
  have h_rewind_traj := ScanLeft.rewindToStart_traj 4 3 []
    (AppendGadget.regBlocks skipped ++ 0 :: tail') (1 + (AppendGadget.regBlocks skipped).length)
    (by simp [List.length_append]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [0]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ 0 :: tail').length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ 0 :: tail')[i]?
          = (AppendGadget.regBlocks skipped ++ [0])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ 0 :: tail').get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [0])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind_traj
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM sb).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM sb).sig
        (max (Compile.forBndContentTM counter sb rbody).sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM sb).sig
          (max (Compile.forBndContentTM counter sb rbody).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.forBndContentTM_sig]; rfl,
        (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM sb)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim sb,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_delim skipped tail' hskip
    rw [← htape_nav, hsklen] at hn; exact hn
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM sb)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content sb ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim sb ∧
      haltingStateReached (ClearGadget.navigateAndTestTM sb) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM sb) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail' hskip
        (by decide) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt sb) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt sb) hh,
           hh⟩
  have h_ne : ClearGadget.navigateAndTestTM_exit_content sb
      ≠ ClearGadget.navigateAndTestTM_exit_delim sb := by
    show (ClearGadget.navigateToRegTM sb).states + 1
        ≠ (ClearGadget.navigateToRegTM sb).states + 2
    omega
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1
      + ((1 + (AppendGadget.regBlocks skipped).length) + 1), ?_, ?_, ?_⟩
  · rw [show Compile.forBndBodyTM counter sb rbody
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM sb)
            (Compile.forBndContentTM counter sb rbody) ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content sb)
            (ClearGadget.navigateAndTestTM_exit_delim sb) from rfl,
      show Compile.forBndBodyTM_exitDone counter sb rbody
        = ClearGadget.justRewindTM_exit
            + ((ClearGadget.navigateAndTestTM sb).states
                + (Compile.forBndContentTM counter sb rbody).states)
          from by
          show (ClearGadget.navigateAndTestTM sb).states
                + (Compile.forBndContentTM counter sb rbody).states + ClearGadget.justRewindTM_exit
            = ClearGadget.justRewindTM_exit
                + ((ClearGadget.navigateAndTestTM sb).states
                    + (Compile.forBndContentTM counter sb rbody).states)
          omega]
    exact (branchComposeFlatTM_run_neg h_ne
      (ClearGadget.navigateAndTestTM_valid sb) (Compile.forBndContentTM_valid counter sb rbody)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt sb)
      (ClearGadget.navigateAndTestTM_exit_delim_lt sb)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1 h_rewind
      (Compile.haltingStateReached_of_halt
        (show ClearGadget.justRewindTM.halt[1]? = some true from rfl))).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_neg h_ne
      (ClearGadget.navigateAndTestTM_valid sb) (Compile.forBndContentTM_valid counter sb rbody)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt sb)
      (ClearGadget.navigateAndTestTM_exit_delim_lt sb)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (fun k' hk' ck' hck' => (h_rewind_traj k' hk' ck' hck').2)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.forBndBodyTM_exitDone_is_halt counter sb rbody) hh,
           ClearGadget.ne_of_not_halting (Compile.forBndBodyTM_exitLoop_is_halt counter sb rbody) hh,
           hh⟩
  · omega

/-- **★ `forBnd` loop body — ITERATE branch (the `loopTM_run` `h_iter` contract).**
When register `K1 = sb` is nonempty (the guard passed), the loop body navigates to
it (content branch), the content machine `forBndContentTM` rewinds to the leading
sentinel and runs the per-iteration bookkeeping chain `forBndIterate`, landing at
`forBndBodyTM_exitLoop` on `forBndIterateState counter sb body s` (the decremented
loop state) with a residue whose joint size+length growth is bounded by the
iteration's cost contribution (the **W-invariant ①**). Mirrors
`clearBody_delete_run`, but the content M₂ slot is `forBndContentTM` (a
`composeFlatTM justRewindTM (forBndIterate …).M`), so its run/trajectory are built
by `composeFlatTM_run`/`composeFlatTM_no_early_halt` from `rewindToStart_run`
(`justRewindTM`) and the proven `forBndIterate_run`. Takes the verbatim
`compileForBnd_sound_physical_residue` body contract `hbody`, threaded straight
through to `forBndIterate_run`. -/
theorem Compile.forBndBody_iterate_run
    (counter sb : Var) (rbody : CompiledCmd) (body : Cmd)
    (s : State) (res : List Nat) (G : Nat)
    (hbit : Compile.BitState s)
    (hcnt : counter < sb)
    (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (hsbne : State.get s sb ≠ [])
    (hres : Compile.ValidResidue res)
    (huses_body : Cmd.UsesBelow body sb)
    (hscr : ∀ r, sb + 2 ≤ r → State.get s r = [])
    (hG : State.size s + s.length + res.length
            + ((State.get s (sb + 1)).length
               + body.cost (s.set counter (State.get s (sb + 1))) + 1) + 2 ≤ G)
    (hbody : ∀ (s' : State) (res' : List Nat) (G' : Nat),
      Compile.BitState s' → sb + 2 + 2 * body.loopDepth + 2 ≤ s'.length →
      (∀ r, sb + 2 ≤ r → State.get s' r = []) →
      Compile.ValidResidue res' →
      State.size s' + s'.length + res'.length + body.cost s' + 2 ≤ G' →
      ∃ (tt : Nat) (resb : List Nat),
        Compile.ValidResidue resb ∧
        State.size (body.eval s') + resb.length ≤ State.size s' + res'.length + body.cost s' ∧
        runFlatTM tt rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res'])
          = some { state_idx := rbody.exit,
                   tapes := [([], 0, Compile.encodeTape (body.eval s') ++ resb)] } ∧
        (∀ kk, kk < tt → ∀ ck,
            runFlatTM kk rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res']) = some ck →
            ck.state_idx ≠ rbody.exit ∧ haltingStateReached rbody.M ck = false) ∧
        tt ≤ Compile.physStepBudget G' (body.cost s')) :
    ∃ (t : Nat) (res' : List Nat),
      Compile.ValidResidue res' ∧
      State.size (Compile.forBndIterateState counter sb body s) + res'.length
        ≤ State.size s + res.length
          + ((State.get s (sb + 1)).length
             + body.cost (s.set counter (State.get s (sb + 1))) + 1) ∧
      runFlatTM t (Compile.forBndBodyTM counter sb rbody)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.forBndBodyTM_exitLoop counter sb rbody,
                 tapes := [([], 0,
                   Compile.encodeTape (Compile.forBndIterateState counter sb body s) ++ res')] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.forBndBodyTM counter sb rbody)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.forBndBodyTM_exitDone counter sb rbody ∧
          ck.state_idx ≠ Compile.forBndBodyTM_exitLoop counter sb rbody ∧
          haltingStateReached (Compile.forBndBodyTM counter sb rbody) ck = false)
      ∧ t ≤ (9 * G * G + 9 * G + 30) * ((State.get s (sb + 1)).length + 2)
          + Compile.physStepBudget G (body.cost (s.set counter (State.get s (sb + 1))))
          + 12 * G + 32 := by
  -- length facts (`sb`/`counter : Var` opaque to omega; use `Nat.*` lemmas)
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  -- tape decomposition at the (nonempty) register `sb` (copy of `clearBody_delete_run`)
  obtain ⟨c0, cs, hcons⟩ : ∃ c0 cs, s.get sb = c0 :: cs := by
    cases hg : s.get sb with
    | nil => exact absurd hg hsbne
    | cons c0 cs => exact ⟨c0, cs, rfl⟩
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s sb hsb_lt
  have hc0le : c0 ≤ 1 := by
    have hmem : s.get sb ∈ s := by
      rw [State.get, List.getElem?_eq_getElem hsb_lt]; exact List.getElem_mem hsb_lt
    exact hbit _ hmem c0 (by rw [hcons]; exact List.mem_cons_self ..)
  have hbit_take : Compile.BitState (s.take sb) :=
    fun reg hreg => hbit reg (List.mem_of_mem_take hreg)
  set skipped : List (List Nat) := (s.take sb).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take sb) :=
    Compile.regBlocks_map_shiftReg (s.take sb)
  have hsklen : skipped.length = sb := by
    rw [hskdef, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hsb_lt)]
  have hskip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    rw [hskdef]; intro b hb
    rw [List.mem_map] at hb
    obtain ⟨reg, hreg, rfl⟩ := hb
    have hregmem : reg ∈ s := List.mem_of_mem_take hreg
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, _, rfl⟩ := hx; omega
    · rw [Compile.shiftReg, List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      have : y ≤ 1 := hbit reg hregmem y hy; omega
  set midSuf : List Nat :=
    Compile.shiftReg cs ++ 0 :: (Compile.encodeRegs (s.drop (sb + 1)) ++ [Compile.endMark] ++ res)
    with hmidSufdef
  have hshift : Compile.shiftReg (c0 :: cs) = (c0 + 1) :: Compile.shiftReg cs := by
    simp [Compile.shiftReg]
  have htape_nav : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf) := by
    rw [hs, hcons, hshift, hregBlocks, hmidSufdef]; simp [Compile.endMark, List.append_assoc]
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have hrb : ∀ x ∈ AppendGadget.regBlocks skipped, x < 4 ∧ x ≠ 3 := by
    rw [hregBlocks]; intro x hx
    exact ⟨Compile.encodeRegs_lt_four (s.take sb) hbit_take x hx,
           Compile.encodeRegs_no_endMark (s.take sb) hbit_take x hx⟩
  have hpref : ∀ x ∈ AppendGadget.regBlocks skipped ++ [c0 + 1], x < 4 ∧ x ≠ 3 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrb x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega⟩
  have hrestsplit : AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf
      = (AppendGadget.regBlocks skipped ++ [c0 + 1]) ++ midSuf := by simp [List.append_assoc]
  have h_rb_le : (AppendGadget.regBlocks skipped).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [htape_nav]; simp only [List.length_cons, List.length_append]; omega
  have h_nav_le : ClearGadget.navSteps skipped ≤ 2 * (AppendGadget.regBlocks skipped).length + 1 :=
    ClearGadget.navSteps_le skipped
  have hLG : (Compile.encodeTape s ++ res).length ≤ G := by
    rw [List.length_append, Compile.encodeTape_length]; omega
  -- ### the per-iteration bookkeeping run (forBndIterate), from head 0
  obtain ⟨ti, resi, hresi, hWi, hruni, htraji, hbudi⟩ :=
    Compile.forBndIterate_run counter sb rbody body s res G hbit hcnt hlen hsbne hres
      huses_body hscr hG hbody
  -- ### the content machine `forBndContentTM` = rewind ⨾ forBndIterate, via composeFlatTM
  -- (i) the rewind (`justRewindTM = scanLeftUntilTM 4 3`) from the interior head to 0
  have h_rewind := ScanLeft.rewindToStart_run 4 3 []
    (AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf) (1 + (AppendGadget.regBlocks skipped).length)
    (by rw [hrestsplit]; simp only [List.length_append, List.length_cons]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [c0 + 1]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf).length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf)[i]?
          = (AppendGadget.regBlocks skipped ++ [c0 + 1])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf).get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [c0 + 1])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind
  have h_rewind_traj := ScanLeft.rewindToStart_traj 4 3 []
    (AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf) (1 + (AppendGadget.regBlocks skipped).length)
    (by rw [hrestsplit]; simp only [List.length_append, List.length_cons]; omega)
    (fun i hi => by
      have hi' : i < (AppendGadget.regBlocks skipped ++ [c0 + 1]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      have hir : i < (AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf).length := by
        rw [hrestsplit, List.length_append]; omega
      have hget? : (AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf)[i]?
          = (AppendGadget.regBlocks skipped ++ [c0 + 1])[i]? := by
        rw [hrestsplit, List.getElem?_append_left hi']
      have hget : (AppendGadget.regBlocks skipped ++ (c0 + 1) :: midSuf).get ⟨i, hir⟩
          = (AppendGadget.regBlocks skipped ++ [c0 + 1])[i]'hi' := by
        rw [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hi'] at hget?
        exact Option.some.inj hget?
      exact ⟨hir, by rw [hget]; exact (hpref _ (List.getElem_mem hi')).1,
                     by rw [hget]; exact (hpref _ (List.getElem_mem hi')).2⟩)
  rw [← htape_nav] at h_rewind_traj
  -- sym-bound at the seam (head 0 reads the leading sentinel `3`)
  have h_sym_seam : ∀ w, currentTapeSymbol ([], 0, Compile.encodeTape s ++ res) = some w →
      w < max ClearGadget.justRewindTM.sig (Compile.forBndIterate counter sb rbody).M.sig := by
    intro w hw
    have hlen0 : (0 : Nat) < (Compile.encodeTape s ++ res).length := by rw [htape_nav]; simp
    rw [currentTapeSymbol_in_range hlen0, List.get_eq_getElem] at hw
    rw [show max ClearGadget.justRewindTM.sig (Compile.forBndIterate counter sb rbody).M.sig = 4 from by
        rw [(Compile.forBndIterate counter sb rbody).M_sig]; rfl, (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hlen0)
  -- halt of forBndIterate's exit config
  have h_iterate_halt : haltingStateReached (Compile.forBndIterate counter sb rbody).M
      { state_idx := (Compile.forBndIterate counter sb rbody).exit,
        tapes := [([], 0,
          Compile.encodeTape (Compile.forBndIterateState counter sb body s) ++ resi)] } = true := by
    have hex := (Compile.forBndIterate counter sb rbody).exit_is_halt
    show (Compile.forBndIterate counter sb rbody).M.halt.getD
        (Compile.forBndIterate counter sb rbody).exit false = true
    simp only [List.getD, hex, Option.getD]
  -- assemble the content run (composeFlatTM justRewindTM forBndIterate.M)
  have h_content := composeFlatTM_run
    ClearGadget.justRewindTM_valid (Compile.forBndIterate counter sb rbody).M_valid
    (show ClearGadget.justRewindTM_exit < ClearGadget.justRewindTM.states from by decide)
    { state_idx := 0,
      tapes := [([], 1 + (AppendGadget.regBlocks skipped).length, Compile.encodeTape s ++ res)] }
    (show (0 : Nat) < ClearGadget.justRewindTM.states from by decide)
    [] 0 (Compile.encodeTape s ++ res)
    h_sym_seam h_rewind h_rewind_traj hruni h_iterate_halt
  have h_content_traj := composeFlatTM_no_early_halt
    ClearGadget.justRewindTM_valid (Compile.forBndIterate counter sb rbody).M_valid
    (show ClearGadget.justRewindTM_exit < ClearGadget.justRewindTM.states from by decide)
    { state_idx := 0,
      tapes := [([], 1 + (AppendGadget.regBlocks skipped).length, Compile.encodeTape s ++ res)] }
    (show (0 : Nat) < ClearGadget.justRewindTM.states from by decide)
    [] 0 (Compile.encodeTape s ++ res)
    h_sym_seam h_rewind h_rewind_traj
    (fun k hk ck hck => (htraji k hk ck hck).2)
  -- ### the outer branch (navigate K1 — content branch)
  have h_run1nav : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM sb)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_content sb,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_content skipped (c0 + 1) midSuf hskip
      (by omega) (by omega)
    rw [← htape_nav, hsklen] at hn; exact hn
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM sb).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM sb).sig
        (max (Compile.forBndContentTM counter sb rbody).sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM sb).sig
          (max (Compile.forBndContentTM counter sb rbody).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.forBndContentTM_sig]; rfl,
        (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_traj1nav : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM sb)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content sb ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim sb ∧
      haltingStateReached (ClearGadget.navigateAndTestTM sb) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM sb) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped (c0 + 1) midSuf hskip
        (by omega) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt sb) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt sb) hh,
           hh⟩
  have h_ne : ClearGadget.navigateAndTestTM_exit_content sb
      ≠ ClearGadget.navigateAndTestTM_exit_delim sb := by
    show (ClearGadget.navigateToRegTM sb).states + 1
        ≠ (ClearGadget.navigateToRegTM sb).states + 2
    omega
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1
      + (((1 + (AppendGadget.regBlocks skipped).length) + 1) + 1 + ti), resi, hresi, hWi, ?_, ?_, ?_⟩
  · -- run
    rw [show Compile.forBndBodyTM counter sb rbody
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM sb)
            (Compile.forBndContentTM counter sb rbody) ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content sb)
            (ClearGadget.navigateAndTestTM_exit_delim sb) from rfl,
      show Compile.forBndBodyTM_exitLoop counter sb rbody
        = ((Compile.forBndIterate counter sb rbody).exit + ClearGadget.justRewindTM.states)
            + (ClearGadget.navigateAndTestTM sb).states from by
          show (ClearGadget.navigateAndTestTM sb).states
                + (ClearGadget.justRewindTM.states + (Compile.forBndIterate counter sb rbody).exit)
            = ((Compile.forBndIterate counter sb rbody).exit + ClearGadget.justRewindTM.states)
                + (ClearGadget.navigateAndTestTM sb).states
          omega]
    exact (branchComposeFlatTM_run_pos h_ne
      (ClearGadget.navigateAndTestTM_valid sb) (Compile.forBndContentTM_valid counter sb rbody)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt sb)
      (ClearGadget.navigateAndTestTM_exit_delim_lt sb)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1nav h_traj1nav h_content.1 h_content.2).1
  · -- no-early-halt
    intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_pos
      (ClearGadget.navigateAndTestTM_valid sb) (Compile.forBndContentTM_valid counter sb rbody)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt sb)
      (ClearGadget.navigateAndTestTM_exit_delim_lt sb)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1nav h_traj1nav h_content_traj
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.forBndBodyTM_exitDone_is_halt counter sb rbody) hh,
           ClearGadget.ne_of_not_halting (Compile.forBndBodyTM_exitLoop_is_halt counter sb rbody) hh,
           hh⟩
  · -- budget (`|K2|`-explicit, so the loop sum closes — see `forBndIterate_run`)
    set A := (9 * G * G + 9 * G + 30) * ((State.get s (sb + 1)).length + 2) with hA
    set B := Compile.physStepBudget G (body.cost (s.set counter (State.get s (sb + 1)))) with hB
    omega

/-- **The pure state fold `foldlState` preserves the register count.** Every
iteration writes `counter < k ≤ s.length` (in range) and runs `body` (`UsesBelow
body k`, length-preserving in range), so the width stays `= s.length`. -/
theorem Cmd.foldlState_length (body : Cmd) (counter : Var) (n : Nat) (s : State) (k : Nat)
    (hcnt : counter < k) (huses : Cmd.UsesBelow body k) (hk : k ≤ s.length) :
    (Cmd.foldlState body counter (List.range n) s).length = s.length := by
  refine Cmd.foldlState_range_induct body counter n s
    (fun _ st => st.length = s.length) rfl ?_
  intro i st _ hst
  have hcl : counter < st.length := by rw [hst]; exact Nat.lt_of_lt_of_le hcnt hk
  have hsl : (st.set counter (List.replicate i 1)).length = s.length := by
    rw [Compile.length_set st counter _ hcl, hst]
  have hge := Cmd.eval_length_ge body (st.set counter (List.replicate i 1))
  have hle := Cmd.eval_length_le body k huses (st.set counter (List.replicate i 1))
  rw [hsl] at hge hle
  rw [Nat.max_eq_left hk] at hle
  omega

/-- **One iteration's effect on a register `r < sb` (a body/counter register).**
`forBndIterateState` writes `K1 = sb`/`K2 = sb+1` after the body, neither of which
is `< sb`, so a register `r < sb` reads through to `body.eval (s.set counter K2)`. -/
theorem Compile.forBndIterateState_get_below (counter sb : Var) (body : Cmd) (s : State)
    (hcnt : counter < sb) (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (huses_body : Cmd.UsesBelow body sb) (r : Var) (hr : r < sb) :
    State.get (Compile.forBndIterateState counter sb body s) r
      = State.get (body.eval (s.set counter (State.get s (sb + 1)))) r := by
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  have hcnt_lt : counter < s.length := Nat.lt_trans hcnt hsb_lt
  set s1 : State := s.set counter (State.get s (sb + 1)) with hs1def
  have hlen1 : s1.length = s.length := Compile.length_set s counter _ hcnt_lt
  set s2 : State := body.eval s1 with hs2def
  have hs2len_ge : s1.length ≤ s2.length := Cmd.eval_length_ge body s1
  have hsb1_lt2 : sb + 1 < s2.length := Nat.lt_of_lt_of_le hsb1_lt (hlen1 ▸ hs2len_ge)
  set s3 : State := s2.set (sb + 1) (State.get s2 (sb + 1) ++ [1]) with hs3def
  have hsb_lt3 : sb < s3.length := by
    rw [hs3def]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hsb_lt (hlen1 ▸ hs2len_ge))
      (State.set_length_ge s2 (sb + 1) _)
  have hr_ne_sb : r ≠ sb := Nat.ne_of_lt hr
  have hr_ne_sb1 : r ≠ sb + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt hr)
  show State.get (s3.set sb (State.get s3 sb).tail) r = State.get s2 r
  rw [Compile.get_set_ne s3 sb _ r hsb_lt3 hr_ne_sb, hs3def,
      Compile.get_set_ne s2 (sb + 1) _ r hsb1_lt2 hr_ne_sb1]

/-- **One iteration preserves the register count exactly** (every write is in
range). The exact form `_length_eq` (the proven `_length_ge` gives only `≥`). -/
theorem Compile.forBndIterateState_length_eq (counter sb : Var) (body : Cmd) (s : State)
    (hcnt : counter < sb) (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (huses_body : Cmd.UsesBelow body sb) :
    (Compile.forBndIterateState counter sb body s).length = s.length := by
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  have hcnt_lt : counter < s.length := Nat.lt_trans hcnt hsb_lt
  set s1 : State := s.set counter (State.get s (sb + 1)) with hs1def
  have hlen1 : s1.length = s.length := Compile.length_set s counter _ hcnt_lt
  set s2 : State := body.eval s1 with hs2def
  have hge := Cmd.eval_length_ge body s1
  have hle := Cmd.eval_length_le body sb huses_body s1
  rw [← hs2def] at hge hle
  rw [hlen1] at hge hle
  rw [Nat.max_eq_left (Nat.le_of_lt hsb_lt)] at hle
  have hs2eq : s2.length = s.length := by omega
  have hsb1_lt2 : sb + 1 < s2.length := by rw [hs2eq]; exact hsb1_lt
  set s3 : State := s2.set (sb + 1) (State.get s2 (sb + 1) ++ [1]) with hs3def
  have hs3eq : s3.length = s.length := by
    rw [hs3def, Compile.length_set s2 (sb + 1) _ hsb1_lt2, hs2eq]
  have hsb_lt3 : sb < s3.length := by rw [hs3eq]; exact hsb_lt
  show (s3.set sb (State.get s3 sb).tail).length = s.length
  rw [Compile.length_set s3 sb _ hsb_lt3, hs3eq]

/-- **★ The semantic connection for the `forBnd` loop assembly.** Iterating the
machine fold `forBndIterateState` exactly `iters = |s.get bound|` times from the
loop-entry state `s.set sb (s.get bound)` (`K1` snapshot, `K2` empty), then
clearing `K2 = sb + 1`, reproduces `(forBnd …).eval s`. The loop's scratch
bookkeeping (`K1`/`K2`) lives in registers `≥ sb` that the body (`UsesBelow body
sb`) and the counter never touch, so the `K2`-cleared/`K1`-emptied machine result
agrees register-by-register with the pure state fold `foldlState`. -/
theorem Compile.forBndLoop_eval (counter bound : Var) (sb : Nat) (body : Cmd) (s : State)
    (hbit : Compile.BitState s) (hcnt : counter < sb) (hbnd : bound < sb)
    (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (huses_body : Cmd.UsesBelow body sb) 
    (hscratch : ∀ r, sb ≤ r → State.get s r = []) :
    ((Compile.forBndIterateState counter sb body)^[(State.get s bound).length]
        (s.set sb (State.get s bound))).set (sb + 1) []
      = (Cmd.forBnd counter bound body).eval s := by
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  have hcnt_lt : counter < s.length := Nat.lt_trans hcnt hsb_lt
  have hbnd_lt : bound < s.length := Nat.lt_trans hbnd hsb_lt
  have hbit_reg : ∀ (r : Var), r < s.length → ∀ x ∈ State.get s r, x ≤ 1 := by
    intro r hr x hx
    refine hbit (State.get s r) ?_ x hx
    rw [State.get, List.getElem?_eq_getElem hr]; exact List.getElem_mem hr
  set e : State := s.set sb (State.get s bound) with hedef
  have helen : e.length = s.length := Compile.length_set s sb _ hsb_lt
  have hge_sb : State.get e sb = State.get s bound := Compile.get_set_eq s sb _ hsb_lt
  have hbit_e : Compile.BitState e :=
    Compile.BitState_set s sb _ hbit hsb_lt (hbit_reg bound hbnd_lt)
  have hFstep : ∀ j, Cmd.foldlState body counter (List.range (j + 1)) s
      = body.eval ((Cmd.foldlState body counter (List.range j) s).set counter
          (List.replicate j 1)) := by
    intro j
    simp only [Cmd.foldlState, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  -- the joint state-fold invariant
  have key : ∀ i, i ≤ (State.get s bound).length →
      AgreeBelow sb ((Compile.forBndIterateState counter sb body)^[i] e)
        (Cmd.foldlState body counter (List.range i) s) ∧
      State.get ((Compile.forBndIterateState counter sb body)^[i] e) (sb + 1)
        = List.replicate i 1 ∧
      ((Compile.forBndIterateState counter sb body)^[i] e).length = s.length := by
    intro i
    induction i with
    | zero =>
        intro _
        refine ⟨?_, ?_, ?_⟩
        · intro r hr
          simp only [Function.iterate_zero, id_eq, List.range_zero, Cmd.foldlState_nil]
          rw [hedef, Compile.get_set_ne s sb _ r hsb_lt (Nat.ne_of_lt hr)]
        · simp only [Function.iterate_zero, id_eq, List.replicate_zero]
          rw [hedef, Compile.get_set_ne s sb _ (sb + 1) hsb_lt (Nat.succ_ne_self sb)]
          exact hscratch (sb + 1) (Nat.le_succ sb)
        · simp only [Function.iterate_zero, id_eq]; exact helen
    | succ i ih =>
        intro hi
        obtain ⟨hAg, hK2, hAlen⟩ := ih (Nat.le_of_succ_le hi)
        set a := (Compile.forBndIterateState counter sb body)^[i] e with hadef
        have hstepA : (Compile.forBndIterateState counter sb body)^[i + 1] e
            = Compile.forBndIterateState counter sb body a := by
          rw [Function.iterate_succ_apply', ← hadef]
        have halen_sb : sb + 2 + 2 * body.loopDepth + 2 ≤ a.length := by rw [hAlen]; exact hlen
        have halen_cnt : counter < a.length := by rw [hAlen]; exact hcnt_lt
        set s1 : State := a.set counter (State.get a (sb + 1)) with hs1def
        have hs1_eq : s1 = a.set counter (List.replicate i 1) := by rw [hs1def, hK2]
        set s2 : State := body.eval s1 with hs2def
        set g : State := (Cmd.foldlState body counter (List.range i) s).set counter
          (List.replicate i 1) with hgdef
        have hag : AgreeBelow sb s1 g := by
          rw [hs1_eq, hgdef]; exact hAg.set counter (List.replicate i 1)
        have heval_ag : AgreeBelow sb s2 (body.eval g) := by
          rw [hs2def]; exact Cmd.eval_agree body sb huses_body hag
        refine ⟨?_, ?_, ?_⟩
        · rw [hstepA, hFstep i, ← hgdef]
          intro r hr
          rw [Compile.forBndIterateState_get_below counter sb body a hcnt halen_sb huses_body r hr,
              ← hs1def, ← hs2def]
          exact heval_ag r hr
        · rw [hstepA, Compile.forBndIterateState_get_sb1 counter sb body a hcnt halen_sb huses_body,
              hK2, ← List.replicate_succ']
        · rw [hstepA, Compile.forBndIterateState_length_eq counter sb body a hcnt halen_sb huses_body,
              hAlen]
  -- instantiate at `iters` and assemble the register-by-register equality
  obtain ⟨hAg, _, hAlen'⟩ := key (State.get s bound).length (Nat.le_refl _)
  have hscr_e : ∀ r, sb + 2 ≤ r → State.get e r = [] := by
    intro r hr
    have hsbr : sb < r := Nat.lt_of_lt_of_le (by omega) hr
    rw [hedef, Compile.get_set_ne s sb _ r hsb_lt (Ne.symm (Nat.ne_of_lt hsbr))]
    exact hscratch r (Nat.le_trans (Nat.le_add_right sb 2) hr)
  have hk2_e : State.get e (sb + 1) = [] := by
    rw [hedef, Compile.get_set_ne s sb _ (sb + 1) hsb_lt (Nat.succ_ne_self sb)]
    exact hscratch (sb + 1) (Nat.le_succ sb)
  have hinv := Compile.forBndLoop_invariant counter sb body e hbit_e hcnt
    (by rw [helen]; exact hlen) huses_body hscr_e hk2_e
    (State.get s bound).length (Nat.le_of_eq (by rw [hge_sb]))
  obtain ⟨_, hscr_n, _, hK1_n, _⟩ := hinv
  have hAsb_nil : State.get ((Compile.forBndIterateState counter sb body)^[(State.get s bound).length] e)
      sb = [] := by
    have h0 : (State.get ((Compile.forBndIterateState counter sb body)^[(State.get s bound).length] e)
        sb).length = 0 := by rw [hK1_n, hge_sb, Nat.sub_self]
    exact List.eq_nil_of_length_eq_zero h0
  have hFlen : (Cmd.foldlState body counter (List.range (State.get s bound).length) s).length
      = s.length :=
    Cmd.foldlState_length body counter (State.get s bound).length s sb hcnt huses_body
      (Nat.le_of_lt hsb_lt)
  have hgetall : ∀ r, State.get (((Compile.forBndIterateState counter sb body)^[(State.get s bound).length] e).set
        (sb + 1) []) r
      = State.get (Cmd.foldlState body counter (List.range (State.get s bound).length) s) r := by
    intro r
    by_cases hr : r < sb
    · rw [Compile.get_set_ne _ (sb + 1) _ r (by rw [hAlen']; exact hsb1_lt)
          (Nat.ne_of_lt (Nat.lt_succ_of_lt hr))]
      exact hAg r hr
    · push_neg at hr
      have hrhs : State.get (Cmd.foldlState body counter (List.range (State.get s bound).length) s) r
          = [] := by
        rw [Cmd.foldlState_frame body counter (State.get s bound).length s sb hcnt huses_body r hr]
        exact hscratch r hr
      rw [hrhs]
      by_cases hr1 : r = sb + 1
      · subst hr1
        rw [Compile.get_set_eq _ (sb + 1) _ (by rw [hAlen']; exact hsb1_lt)]
      · rw [Compile.get_set_ne _ (sb + 1) _ r (by rw [hAlen']; exact hsb1_lt) hr1]
        by_cases hr2 : r = sb
        · subst hr2; exact hAsb_nil
        · have hsb_lt_r : sb < r := Nat.lt_of_le_of_ne hr (Ne.symm hr2)
          have hr_ge : sb + 2 ≤ r := Nat.lt_of_le_of_ne hsb_lt_r (Ne.symm hr1)
          exact hscr_n r hr_ge
  rw [Cmd.eval_forBnd]
  apply List.ext_getElem
  · rw [Compile.length_set _ (sb + 1) _ (by rw [hAlen']; exact hsb1_lt), hAlen', hFlen]
  · intro idx h1 h2
    have e1 : ∀ (l : State) (h : idx < l.length), l[idx] = State.get l idx := by
      intro l h; rw [State.get, List.getElem?_eq_getElem h, Option.getD_some]
    rw [e1 _ h1, e1 _ h2]
    exact hgetall idx

/-! ### The `forBnd` loop run (the `loopTM_run` assembly for `compileForBnd`)

`forBndLoop_run` is the loop-fragment run (mirrors `clearRegionTM_run`): a
`.choose`-free residue/step-count fold (`forBndLoop_fold`) feeds `loopTM_run` /
`loopTM_no_early_halt`. The W-invariant and the budget are exposed as `Finset`
sums over the fold states; the budget collapse uses the superadditive
`physStepBudget_sum_le`. Consumed by `compileForBnd_sound_physical_residue`. -/

/-- **Machine↔pure fold agreement** (the `key` of `forBndLoop_eval`, exposed for the
cost-sum bridge). Along the loop fold from `e = s.set sb (s.get bound)`, each machine
state agrees with the pure `foldlState` below `sb`, and `K2` holds `replicate i 1`. -/
theorem Compile.forBndLoop_agree (counter bound : Var) (sb : Var) (body : Cmd) (s : State)
    (hbit : Compile.BitState s) (hcnt : counter < sb) (hbnd : bound < sb)
    (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (huses_body : Cmd.UsesBelow body sb) 
    (hscratch : ∀ r, sb ≤ r → State.get s r = []) :
    ∀ i, i ≤ (State.get s bound).length →
      AgreeBelow sb ((Compile.forBndIterateState counter sb body)^[i] (s.set sb (State.get s bound)))
        (Cmd.foldlState body counter (List.range i) s) ∧
      State.get ((Compile.forBndIterateState counter sb body)^[i] (s.set sb (State.get s bound))) (sb + 1)
        = List.replicate i 1 ∧
      ((Compile.forBndIterateState counter sb body)^[i] (s.set sb (State.get s bound))).length = s.length := by
  have hsb1_lt : sb + 1 < s.length :=
    Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen
  have hsb_lt : sb < s.length := Nat.lt_trans (Nat.lt_succ_self sb) hsb1_lt
  have hcnt_lt : counter < s.length := Nat.lt_trans hcnt hsb_lt
  have hbnd_lt : bound < s.length := Nat.lt_trans hbnd hsb_lt
  have hbit_reg : ∀ (r : Var), r < s.length → ∀ x ∈ State.get s r, x ≤ 1 := by
    intro r hr x hx
    refine hbit (State.get s r) ?_ x hx
    rw [State.get, List.getElem?_eq_getElem hr]; exact List.getElem_mem hr
  set e : State := s.set sb (State.get s bound) with hedef
  have helen : e.length = s.length := Compile.length_set s sb _ hsb_lt
  have hge_sb : State.get e sb = State.get s bound := Compile.get_set_eq s sb _ hsb_lt
  have hbit_e : Compile.BitState e :=
    Compile.BitState_set s sb _ hbit hsb_lt (hbit_reg bound hbnd_lt)
  have hFstep : ∀ j, Cmd.foldlState body counter (List.range (j + 1)) s
      = body.eval ((Cmd.foldlState body counter (List.range j) s).set counter
          (List.replicate j 1)) := by
    intro j
    simp only [Cmd.foldlState, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  intro i
  induction i with
  | zero =>
      intro _
      refine ⟨?_, ?_, ?_⟩
      · intro r hr
        simp only [Function.iterate_zero, id_eq, List.range_zero, Cmd.foldlState_nil]
        rw [hedef, Compile.get_set_ne s sb _ r hsb_lt (Nat.ne_of_lt hr)]
      · simp only [Function.iterate_zero, id_eq, List.replicate_zero]
        rw [hedef, Compile.get_set_ne s sb _ (sb + 1) hsb_lt (Nat.succ_ne_self sb)]
        exact hscratch (sb + 1) (Nat.le_succ sb)
      · simp only [Function.iterate_zero, id_eq]; exact helen
  | succ i ih =>
      intro hi
      obtain ⟨hAg, hK2, hAlen⟩ := ih (Nat.le_of_succ_le hi)
      set a := (Compile.forBndIterateState counter sb body)^[i] e with hadef
      have hstepA : (Compile.forBndIterateState counter sb body)^[i + 1] e
          = Compile.forBndIterateState counter sb body a := by
        rw [Function.iterate_succ_apply', ← hadef]
      have halen_sb : sb + 2 + 2 * body.loopDepth + 2 ≤ a.length := by rw [hAlen]; exact hlen
      have halen_cnt : counter < a.length := by rw [hAlen]; exact hcnt_lt
      set s1 : State := a.set counter (State.get a (sb + 1)) with hs1def
      have hs1_eq : s1 = a.set counter (List.replicate i 1) := by rw [hs1def, hK2]
      set s2 : State := body.eval s1 with hs2def
      set g : State := (Cmd.foldlState body counter (List.range i) s).set counter
        (List.replicate i 1) with hgdef
      have hag : AgreeBelow sb s1 g := by
        rw [hs1_eq, hgdef]; exact hAg.set counter (List.replicate i 1)
      have heval_ag : AgreeBelow sb s2 (body.eval g) := by
        rw [hs2def]; exact Cmd.eval_agree body sb huses_body hag
      refine ⟨?_, ?_, ?_⟩
      · rw [hstepA, hFstep i, ← hgdef]
        intro r hr
        rw [Compile.forBndIterateState_get_below counter sb body a hcnt halen_sb huses_body r hr,
            ← hs1def, ← hs2def]
        exact heval_ag r hr
      · rw [hstepA, Compile.forBndIterateState_get_sb1 counter sb body a hcnt halen_sb huses_body,
            hK2, ← List.replicate_succ']
      · rw [hstepA, Compile.forBndIterateState_length_eq counter sb body a hcnt halen_sb huses_body,
            hAlen]

/-- **`forBnd` cost as a `Finset` sum** over the pure fold states (the cost-model
counterpart of `eval_forBnd`). Used to tie the loop's body-cost sum to `(forBnd).cost`. -/
theorem Cmd.cost_forBnd_eq (counter bound : Var) (body : Cmd) (s : State) :
    (Cmd.forBnd counter bound body).cost s
      = 1 + (∑ i ∈ Finset.range (State.get s bound).length,
          body.cost ((Cmd.foldlState body counter (List.range i) s).set counter (List.replicate i 1)))
        + (State.get s bound).length * (State.get s bound).length := by
  have hfold : ∀ n, (List.range n).foldl
      (fun acc i => let s' := acc.1.set counter (List.replicate i 1)
                    let r := Cmd.run body s'; (r.1, acc.2 + r.2)) (s, 0)
      = (Cmd.foldlState body counter (List.range n) s,
         ∑ i ∈ Finset.range n,
           body.cost ((Cmd.foldlState body counter (List.range i) s).set counter (List.replicate i 1))) := by
    intro n
    induction n with
    | zero => simp [Cmd.foldlState]
    | succ n ih =>
        rw [List.range_succ, List.foldl_append, ih]
        simp only [List.foldl_cons, List.foldl_nil]
        have hfs : Cmd.foldlState body counter (List.range n ++ [n]) s
            = body.eval ((Cmd.foldlState body counter (List.range n) s).set counter (List.replicate n 1)) := by
          rw [Cmd.foldlState, List.foldl_append]; simp [Cmd.foldlState]
        rw [Finset.sum_range_succ, hfs]
        rfl
  show (Cmd.run (Cmd.forBnd counter bound body) s).2 = _
  simp only [Cmd.run]
  rw [hfold]

theorem Compile.physStepBudget_sum_le (G : Nat) (cc : Nat → Nat) :
    ∀ n, (∑ j ∈ Finset.range n, Compile.physStepBudget G (cc j))
      ≤ Compile.physStepBudget G ((∑ j ∈ Finset.range n, cc j) + n) := by
  intro n
  induction n with
  | zero => simp [Compile.physStepBudget]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hsuper : Compile.physStepBudget G ((∑ j ∈ Finset.range n, cc j) + n)
            + Compile.physStepBudget G (cc n)
          ≤ Compile.physStepBudget G ((∑ j ∈ Finset.range n, cc j) + cc n + (n + 1)) := by
        have := Compile.physStepBudget_seq G ((∑ j ∈ Finset.range n, cc j) + n) (cc n)
        have hmono : Compile.physStepBudget G (1 + ((∑ j ∈ Finset.range n, cc j) + n) + cc n)
            ≤ Compile.physStepBudget G ((∑ j ∈ Finset.range n, cc j) + cc n + (n + 1)) :=
          Compile.physStepBudget_mono (le_refl _) (by omega)
        omega
      have := Nat.add_le_add_right ih (Compile.physStepBudget G (cc n))
      omega

theorem Compile.loopBudget_eq_sum (tIter : Nat → Nat) (tDone : Nat) :
    ∀ n, loopBudget tIter tDone n = (∑ j ∈ Finset.range n, (tIter j + 1)) + (tDone + 1) := by
  intro n
  induction n with
  | zero => simp [loopBudget]
  | succ n ih =>
      have hstep : loopBudget tIter tDone (n + 1) = tIter n + 1 + loopBudget tIter tDone n := rfl
      rw [hstep, ih, Finset.sum_range_succ]; omega

-- the existence of the residue/step-count fold for the loop

-- The residue/step-count fold for the loop body, by induction on the prefix length.
theorem Compile.forBndLoop_fold (counter sb : Var) (rbody : CompiledCmd) (body : Cmd)
    (e : State) (res_in : List Nat) (G : Nat)
    (hbit : Compile.BitState e) (hcnt : counter < sb)
    (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ e.length)
    (huses_body : Cmd.UsesBelow body sb) 
    (hscr : ∀ r, sb + 2 ≤ r → State.get e r = [])
    (hk2 : State.get e (sb + 1) = [])
    (hres_in : Compile.ValidResidue res_in)
    (hG : State.size e + e.length + res_in.length
        + (∑ j ∈ Finset.range (State.get e sb).length,
            (j + body.cost (((Compile.forBndIterateState counter sb body)^[j] e).set counter
                (State.get ((Compile.forBndIterateState counter sb body)^[j] e) (sb + 1))) + 1)) + 2 ≤ G)
    (hbody : ∀ (s' : State) (res' : List Nat) (G' : Nat),
      Compile.BitState s' → sb + 2 + 2 * body.loopDepth + 2 ≤ s'.length →
      (∀ r, sb + 2 ≤ r → State.get s' r = []) →
      Compile.ValidResidue res' →
      State.size s' + s'.length + res'.length + body.cost s' + 2 ≤ G' →
      ∃ (tt : Nat) (resb : List Nat),
        Compile.ValidResidue resb ∧
        State.size (body.eval s') + resb.length ≤ State.size s' + res'.length + body.cost s' ∧
        runFlatTM tt rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res'])
          = some { state_idx := rbody.exit,
                   tapes := [([], 0, Compile.encodeTape (body.eval s') ++ resb)] } ∧
        (∀ kk, kk < tt → ∀ ck,
            runFlatTM kk rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res']) = some ck →
            ck.state_idx ≠ rbody.exit ∧ haltingStateReached rbody.M ck = false) ∧
        tt ≤ Compile.physStepBudget G' (body.cost s')) :
    ∀ N, N ≤ (State.get e sb).length →
      ∃ (Rf : Nat → List Nat) (Tf : Nat → Nat),
        Rf 0 = res_in ∧
        (∀ i, i ≤ N → Compile.ValidResidue (Rf i)) ∧
        State.size ((Compile.forBndIterateState counter sb body)^[N] e) + (Rf N).length
          ≤ State.size e + res_in.length
            + (∑ j ∈ Finset.range N,
                (j + body.cost (((Compile.forBndIterateState counter sb body)^[j] e).set counter
                  (State.get ((Compile.forBndIterateState counter sb body)^[j] e) (sb + 1))) + 1)) ∧
        (∀ i, i < N →
          runFlatTM (Tf i) (Compile.forBndBodyTM counter sb rbody)
              { state_idx := 0, tapes := [([], 0,
                Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[i] e) ++ Rf i)] }
            = some { state_idx := Compile.forBndBodyTM_exitLoop counter sb rbody,
                     tapes := [([], 0,
                       Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[i+1] e) ++ Rf (i+1))] }
          ∧ (∀ k, k < Tf i → ∀ ck,
              runFlatTM k (Compile.forBndBodyTM counter sb rbody)
                  { state_idx := 0, tapes := [([], 0,
                    Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[i] e) ++ Rf i)] } = some ck →
              ck.state_idx ≠ Compile.forBndBodyTM_exitDone counter sb rbody ∧
              ck.state_idx ≠ Compile.forBndBodyTM_exitLoop counter sb rbody ∧
              haltingStateReached (Compile.forBndBodyTM counter sb rbody) ck = false)
          ∧ Tf i ≤ (9 * G * G + 9 * G + 30) * (i + 2)
              + Compile.physStepBudget G (body.cost (((Compile.forBndIterateState counter sb body)^[i] e).set counter
                  (State.get ((Compile.forBndIterateState counter sb body)^[i] e) (sb + 1))))
              + 12 * G + 32) := by
  set iters := (State.get e sb).length with hiters
  set Wterm : Nat → Nat := fun j =>
    j + body.cost ((((Compile.forBndIterateState counter sb body)^[j] e)).set counter (State.get ((Compile.forBndIterateState counter sb body)^[j] e) (sb + 1))) + 1 with hWtermdef
  have hinv := Compile.forBndLoop_invariant counter sb body e hbit hcnt hlen huses_body hscr hk2
  have hAlen : ∀ i, i ≤ iters → ((Compile.forBndIterateState counter sb body)^[i] e).length = e.length := by
    intro i
    induction i with
    | zero => intro _; simp only [Function.iterate_zero, id_eq]
    | succ i ih =>
        intro hi
        have hi' : i ≤ iters := Nat.le_of_succ_le hi
        have hlenAi : sb + 2 + 2 * body.loopDepth + 2 ≤ ((Compile.forBndIterateState counter sb body)^[i] e).length := by rw [ih hi']; exact hlen
        rw [Function.iterate_succ_apply' (Compile.forBndIterateState counter sb body) i e,
          Compile.forBndIterateState_length_eq counter sb body ((Compile.forBndIterateState counter sb body)^[i] e) hcnt hlenAi huses_body, ih hi']
  intro N
  induction N with
  | zero =>
      intro _
      refine ⟨fun _ => res_in, fun _ => 0, rfl, ?_, ?_, ?_⟩
      · intro i hi; exact hres_in
      · simp only [Function.iterate_zero, id_eq, Finset.range_zero, Finset.sum_empty,
          Nat.add_zero, Nat.le_refl]
      · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ N ih =>
      intro hN1
      have hN : N ≤ iters := Nat.le_of_succ_le hN1
      have hNlt : N < iters := hN1
      obtain ⟨Rf, Tf, hRf0, hvalidAll, hWN, hsteps⟩ := ih hN
      obtain ⟨hbitN, hscrN, hlgeN, hK1N, hK2N⟩ := hinv N hN
      have hlenAN : sb + 2 + 2 * body.loopDepth + 2 ≤ ((Compile.forBndIterateState counter sb body)^[N] e).length := by rw [hAlen N hN]; exact hlen
      have hsbneN : State.get ((Compile.forBndIterateState counter sb body)^[N] e) sb ≠ [] := by
        intro hc
        have hz : (State.get ((Compile.forBndIterateState counter sb body)^[N] e) sb).length = 0 := by rw [hc]; rfl
        rw [hK1N] at hz; omega
      have hsub : Finset.range (N + 1) ⊆ Finset.range iters := by
        intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      have hsum_succ : (∑ j ∈ Finset.range N, Wterm j) + Wterm N
          = ∑ j ∈ Finset.range (N + 1), Wterm j := (Finset.sum_range_succ Wterm N).symm
      have hWtN : Wterm N = N + body.cost ((((Compile.forBndIterateState counter sb body)^[N] e)).set counter (State.get ((Compile.forBndIterateState counter sb body)^[N] e) (sb + 1))) + 1 := by
        rw [hWtermdef]
      have hGN : State.size ((Compile.forBndIterateState counter sb body)^[N] e) + ((Compile.forBndIterateState counter sb body)^[N] e).length + (Rf N).length
            + ((State.get ((Compile.forBndIterateState counter sb body)^[N] e) (sb + 1)).length
               + body.cost ((((Compile.forBndIterateState counter sb body)^[N] e)).set counter (State.get ((Compile.forBndIterateState counter sb body)^[N] e) (sb + 1))) + 1) + 2 ≤ G := by
        have hsum_le : (∑ j ∈ Finset.range (N + 1), Wterm j) ≤ ∑ j ∈ Finset.range iters, Wterm j :=
          Finset.sum_le_sum_of_subset hsub
        have hcomb : State.size ((Compile.forBndIterateState counter sb body)^[N] e) + (Rf N).length + Wterm N
            ≤ State.size e + res_in.length + ∑ j ∈ Finset.range iters, Wterm j := by
          calc State.size ((Compile.forBndIterateState counter sb body)^[N] e) + (Rf N).length + Wterm N
              ≤ (State.size e + res_in.length + ∑ j ∈ Finset.range N, Wterm j) + Wterm N :=
                Nat.add_le_add_right hWN _
            _ = State.size e + res_in.length + (∑ j ∈ Finset.range (N + 1), Wterm j) := by
                rw [← hsum_succ]; ring
            _ ≤ State.size e + res_in.length + ∑ j ∈ Finset.range iters, Wterm j :=
                Nat.add_le_add_left hsum_le _
        rw [hK2N, hAlen N hN]
        rw [hWtN] at hcomb
        have hGe : State.size e + e.length + res_in.length
            + (∑ j ∈ Finset.range iters, Wterm j) + 2 ≤ G := hG
        omega
      obtain ⟨tN, resN, hresN, hWstep, hrunN, htrajN, hbudN⟩ :=
        Compile.forBndBody_iterate_run counter sb rbody body ((Compile.forBndIterateState counter sb body)^[N] e) (Rf N) G
          hbitN hcnt hlenAN hsbneN (hvalidAll N (le_refl N)) huses_body hscrN hGN hbody
      refine ⟨fun i => if i = N + 1 then resN else Rf i,
              fun i => if i = N then tN else Tf i, ?_, ?_, ?_, ?_⟩
      · simp only [if_neg (by omega : (0 : Nat) ≠ N + 1)]; exact hRf0
      · intro i hi
        by_cases hiN1 : i = N + 1
        · simp only [hiN1, if_pos rfl]; exact hresN
        · simp only [if_neg hiN1]; exact hvalidAll i (by omega)
      · simp only [if_pos rfl]
        rw [Function.iterate_succ_apply' (Compile.forBndIterateState counter sb body) N e]
        have hWstep' : State.size (Compile.forBndIterateState counter sb body ((Compile.forBndIterateState counter sb body)^[N] e)) + resN.length
            ≤ State.size ((Compile.forBndIterateState counter sb body)^[N] e) + (Rf N).length + Wterm N := by
          have he : (State.get ((Compile.forBndIterateState counter sb body)^[N] e) (sb + 1)).length
              + body.cost ((((Compile.forBndIterateState counter sb body)^[N] e)).set counter (State.get ((Compile.forBndIterateState counter sb body)^[N] e) (sb + 1))) + 1 = Wterm N := by
            rw [hWtN, hK2N]
          rw [he] at hWstep; exact hWstep
        calc State.size (Compile.forBndIterateState counter sb body ((Compile.forBndIterateState counter sb body)^[N] e)) + resN.length
            ≤ State.size ((Compile.forBndIterateState counter sb body)^[N] e) + (Rf N).length + Wterm N := hWstep'
          _ ≤ (State.size e + res_in.length + ∑ j ∈ Finset.range N, Wterm j) + Wterm N :=
              Nat.add_le_add_right hWN _
          _ = State.size e + res_in.length + ∑ j ∈ Finset.range (N + 1), Wterm j := by
              rw [← hsum_succ]; ring
      · intro i hi
        by_cases hiN : i = N
        · subst hiN
          simp only [if_pos rfl, if_neg (by omega : i ≠ i + 1)]
          rw [Function.iterate_succ_apply' (Compile.forBndIterateState counter sb body) i e]
          refine ⟨hrunN, htrajN, ?_⟩
          calc tN ≤ (9 * G * G + 9 * G + 30) * ((State.get ((Compile.forBndIterateState counter sb body)^[i] e) (sb + 1)).length + 2)
                  + Compile.physStepBudget G (body.cost ((((Compile.forBndIterateState counter sb body)^[i] e)).set counter (State.get ((Compile.forBndIterateState counter sb body)^[i] e) (sb + 1))))
                  + 12 * G + 32 := hbudN
            _ = (9 * G * G + 9 * G + 30) * (i + 2)
                  + Compile.physStepBudget G (body.cost ((((Compile.forBndIterateState counter sb body)^[i] e)).set counter (State.get ((Compile.forBndIterateState counter sb body)^[i] e) (sb + 1))))
                  + 12 * G + 32 := by rw [hK2N]
        · have hilt : i < N := by omega
          have hold := hsteps i hilt
          simp only [if_neg (by omega : i ≠ N), if_neg (by omega : i ≠ N + 1),
            if_neg (by omega : i + 1 ≠ N + 1)]
          exact hold

theorem Compile.forBndLoop_run (counter sb : Var) (rbody : CompiledCmd) (body : Cmd)
    (e : State) (res_in : List Nat) (G : Nat)
    (hbit : Compile.BitState e) (hcnt : counter < sb)
    (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ e.length)
    (huses_body : Cmd.UsesBelow body sb) 
    (hscr : ∀ r, sb + 2 ≤ r → State.get e r = [])
    (hk2 : State.get e (sb + 1) = [])
    (hres_in : Compile.ValidResidue res_in)
    (hG : State.size e + e.length + res_in.length
        + (∑ j ∈ Finset.range (State.get e sb).length,
            (j + body.cost (((Compile.forBndIterateState counter sb body)^[j] e).set counter
                (State.get ((Compile.forBndIterateState counter sb body)^[j] e) (sb + 1))) + 1)) + 2 ≤ G)
    (hbody : ∀ (s' : State) (res' : List Nat) (G' : Nat),
      Compile.BitState s' → sb + 2 + 2 * body.loopDepth + 2 ≤ s'.length →
      (∀ r, sb + 2 ≤ r → State.get s' r = []) →
      Compile.ValidResidue res' →
      State.size s' + s'.length + res'.length + body.cost s' + 2 ≤ G' →
      ∃ (tt : Nat) (resb : List Nat),
        Compile.ValidResidue resb ∧
        State.size (body.eval s') + resb.length ≤ State.size s' + res'.length + body.cost s' ∧
        runFlatTM tt rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res'])
          = some { state_idx := rbody.exit,
                   tapes := [([], 0, Compile.encodeTape (body.eval s') ++ resb)] } ∧
        (∀ kk, kk < tt → ∀ ck,
            runFlatTM kk rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res']) = some ck →
            ck.state_idx ≠ rbody.exit ∧ haltingStateReached rbody.M ck = false) ∧
        tt ≤ Compile.physStepBudget G' (body.cost s')) :
    ∃ (t : Nat) (res_out : List Nat),
      Compile.ValidResidue res_out ∧
      State.size ((Compile.forBndIterateState counter sb body)^[(State.get e sb).length] e) + res_out.length
        ≤ State.size e + res_in.length
          + (∑ j ∈ Finset.range (State.get e sb).length,
              (j + body.cost (((Compile.forBndIterateState counter sb body)^[j] e).set counter
                (State.get ((Compile.forBndIterateState counter sb body)^[j] e) (sb + 1))) + 1)) ∧
      runFlatTM t (Compile.forBndLoopCmd counter sb rbody).M
          (initFlatConfig (Compile.forBndLoopCmd counter sb rbody).M [Compile.encodeTape e ++ res_in])
        = some { state_idx := (Compile.forBndLoopCmd counter sb rbody).exit,
                 tapes := [([], 0, Compile.encodeTape
                   ((Compile.forBndIterateState counter sb body)^[(State.get e sb).length] e) ++ res_out)] } ∧
      (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.forBndLoopCmd counter sb rbody).M
              (initFlatConfig (Compile.forBndLoopCmd counter sb rbody).M
                [Compile.encodeTape e ++ res_in]) = some ck →
          ck.state_idx ≠ (Compile.forBndLoopCmd counter sb rbody).exit ∧
          haltingStateReached (Compile.forBndLoopCmd counter sb rbody).M ck = false) ∧
      t ≤ (9 * G * G + 9 * G + 30) * (∑ i ∈ Finset.range (State.get e sb).length, (i + 2))
          + Compile.physStepBudget G ((∑ i ∈ Finset.range (State.get e sb).length,
              body.cost (((Compile.forBndIterateState counter sb body)^[i] e).set counter
                (State.get ((Compile.forBndIterateState counter sb body)^[i] e) (sb + 1)))) + (State.get e sb).length)
          + (State.get e sb).length * (12 * G + 33) + (6 * G + 13) := by
  set iters := (State.get e sb).length with hiters
  -- invariant + exact length
  have hinv := Compile.forBndLoop_invariant counter sb body e hbit hcnt hlen huses_body hscr hk2
  have hAlen : ∀ i, i ≤ iters → ((Compile.forBndIterateState counter sb body)^[i] e).length = e.length := by
    intro i
    induction i with
    | zero => intro _; simp only [Function.iterate_zero, id_eq]
    | succ i ih =>
        intro hi
        have hi' : i ≤ iters := Nat.le_of_succ_le hi
        have hlenAi : sb + 2 + 2 * body.loopDepth + 2 ≤ ((Compile.forBndIterateState counter sb body)^[i] e).length := by rw [ih hi']; exact hlen
        rw [Function.iterate_succ_apply' (Compile.forBndIterateState counter sb body) i e,
          Compile.forBndIterateState_length_eq counter sb body ((Compile.forBndIterateState counter sb body)^[i] e) hcnt hlenAi huses_body, ih hi']
  -- the residue/step fold at N = iters
  obtain ⟨Rf, Tf, hRf0, hvalidAll, hWN, hsteps⟩ :=
    Compile.forBndLoop_fold counter sb rbody body e res_in G hbit hcnt hlen huses_body hscr hk2
      hres_in hG hbody iters (Nat.le_refl _)
  -- the loop tape sequence: remaining `m` ↔ fold index `iters - m`
  set T : Nat → (List Nat × Nat × List Nat) := fun m =>
    ([], 0, Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters - m] e) ++ Rf (iters - m)) with hTdef
  have hT_val : ∀ n, ∀ x ∈ (T n).2.2, x < 4 := by
    intro n x hx
    simp only [hTdef] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four _ ((hinv (iters - n) (by omega)).1) x hx
    · exact (hvalidAll (iters - n) (by omega) x hx).1
  have h_sym : ∀ n v, currentTapeSymbol (T n) = some v → v < (Compile.forBndBodyTM counter sb rbody).sig := by
    intro n v hv
    rw [Compile.forBndBodyTM_sig]
    have hmem : v ∈ (T n).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e'; rw [← e']; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_val n v hmem
  have hBstart : (Compile.forBndBodyTM counter sb rbody).start = 0 := Compile.forBndBodyTM_start counter sb rbody
  -- done branch (fold index iters; K1 empty)
  have hsbiters : State.get ((Compile.forBndIterateState counter sb body)^[iters] e) sb = [] := by
    have h0 : (State.get ((Compile.forBndIterateState counter sb body)^[iters] e) sb).length = 0 := by
      rw [(hinv iters (Nat.le_refl _)).2.2.2.1]; omega
    exact List.eq_nil_of_length_eq_zero h0
  obtain ⟨tDone, hdr, hdt, hdb⟩ := Compile.forBndBody_done_run counter sb rbody ((Compile.forBndIterateState counter sb body)^[iters] e) (Rf iters)
    (by rw [hAlen iters (Nat.le_refl _)]
        exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans (Nat.le_add_right (sb+2) (2*body.loopDepth + 2)) hlen))
    ((hinv iters (Nat.le_refl _)).1) hsbiters (hvalidAll iters (Nat.le_refl _))
  have hT0 : T 0 = ([], 0, Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters] e) ++ Rf iters) := by
    simp only [hTdef, Nat.sub_zero]
  have h_done_full :
      runFlatTM tDone (Compile.forBndBodyTM counter sb rbody) { state_idx := (Compile.forBndBodyTM counter sb rbody).start, tapes := [T 0] }
        = some { state_idx := (Compile.forBndBodyTM_exitDone counter sb rbody), tapes := [T 0] } ∧
      (∀ k, k < tDone → ∀ ck,
          runFlatTM k (Compile.forBndBodyTM counter sb rbody) { state_idx := (Compile.forBndBodyTM counter sb rbody).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ (Compile.forBndBodyTM_exitDone counter sb rbody) ∧ ck.state_idx ≠ (Compile.forBndBodyTM_exitLoop counter sb rbody) ∧
          haltingStateReached (Compile.forBndBodyTM counter sb rbody) ck = false) := by
    refine ⟨?_, ?_⟩
    · rw [hBstart, hT0]; exact hdr
    · rw [hBstart, hT0]; exact hdt
  -- iteration step counts
  set tIter : Nat → Nat := fun m => Tf (iters - (m + 1)) with htIter
  have h_iter_full : ∀ m, m < iters →
      runFlatTM (tIter m) (Compile.forBndBodyTM counter sb rbody) { state_idx := (Compile.forBndBodyTM counter sb rbody).start, tapes := [T (m + 1)] }
        = some { state_idx := (Compile.forBndBodyTM_exitLoop counter sb rbody), tapes := [T m] } ∧
      (∀ k, k < tIter m → ∀ ck,
          runFlatTM k (Compile.forBndBodyTM counter sb rbody) { state_idx := (Compile.forBndBodyTM counter sb rbody).start, tapes := [T (m + 1)] } = some ck →
          ck.state_idx ≠ (Compile.forBndBodyTM_exitDone counter sb rbody) ∧ ck.state_idx ≠ (Compile.forBndBodyTM_exitLoop counter sb rbody) ∧
          haltingStateReached (Compile.forBndBodyTM counter sb rbody) ck = false) := by
    intro m hm
    have hfi : iters - (m + 1) < iters := by omega
    obtain ⟨hrun, htraj, _⟩ := hsteps (iters - (m + 1)) hfi
    have hidx : iters - (m + 1) + 1 = iters - m := by omega
    rw [hidx] at hrun
    have hTm1 : T (m + 1) = ([], 0, Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters - (m+1)] e) ++ Rf (iters - (m + 1))) := by
      simp only [hTdef]
    have hTmm : T m = ([], 0, Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters - m] e) ++ Rf (iters - m)) := by
      simp only [hTdef]
    refine ⟨?_, ?_⟩
    · rw [hBstart, hTm1, hTmm, htIter]; exact hrun
    · rw [hBstart, hTm1, htIter]; intro k hk ck hck; exact htraj k hk ck hck
  -- assemble via loopTM_run / loopTM_no_early_halt
  have hmain := loopTM_run (Compile.forBndBodyTM counter sb rbody) (Compile.forBndBodyTM_exitDone counter sb rbody) (Compile.forBndBodyTM_exitLoop counter sb rbody)
    (Compile.forBndBodyTM_valid counter sb rbody)
    (Compile.forBndBodyTM_exitDone_lt counter sb rbody)
    (Compile.forBndBodyTM_exitLoop_lt counter sb rbody)
    (Compile.forBndBodyTM_exitDone_ne_exitLoop counter sb rbody)
    T h_sym tIter tDone h_done_full iters h_iter_full
  have hmain_traj := loopTM_no_early_halt (Compile.forBndBodyTM counter sb rbody) (Compile.forBndBodyTM_exitDone counter sb rbody) (Compile.forBndBodyTM_exitLoop counter sb rbody)
    (Compile.forBndBodyTM_valid counter sb rbody)
    (Compile.forBndBodyTM_exitDone_lt counter sb rbody)
    (Compile.forBndBodyTM_exitLoop_lt counter sb rbody)
    (Compile.forBndBodyTM_exitDone_ne_exitLoop counter sb rbody)
    T h_sym tIter tDone h_done_full iters h_iter_full
  -- T iters = start tape, T 0 = end tape
  have hTiters : T iters = ([], 0, Compile.encodeTape e ++ res_in) := by
    simp only [hTdef, Nat.sub_self, Function.iterate_zero, id_eq, hRf0]
  rw [hBstart, hTiters, hT0] at hmain
  rw [hBstart, hTiters] at hmain_traj
  -- forBndLoopCmd packaging
  have hMeq : (Compile.forBndLoopCmd counter sb rbody).M
      = loopTM (Compile.forBndBodyTM counter sb rbody) (Compile.forBndBodyTM_exitDone counter sb rbody) (Compile.forBndBodyTM_exitLoop counter sb rbody) := rfl
  have hExeq : (Compile.forBndLoopCmd counter sb rbody).exit = (Compile.forBndBodyTM counter sb rbody).states := rfl
  have hinit : initFlatConfig (Compile.forBndLoopCmd counter sb rbody).M [Compile.encodeTape e ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape e ++ res_in)] } := by
    simp only [initFlatConfig, hMeq, loopTM_start, hBstart, List.map_cons, List.map_nil]
  refine ⟨loopBudget tIter tDone iters, Rf iters, hvalidAll iters (Nat.le_refl _), hWN, ?_, ?_, ?_⟩
  · rw [hinit, hMeq, hExeq]; exact hmain
  · rw [hinit]
    intro k hk ck hck
    rw [hMeq] at hck
    have hh := hmain_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.forBndLoopCmd counter sb rbody).exit_is_halt hh, hh⟩
  · -- budget
    set cc : Nat → Nat := fun i =>
      body.cost (((Compile.forBndIterateState counter sb body)^[i] e).set counter (State.get ((Compile.forBndIterateState counter sb body)^[i] e) (sb + 1))) with hccdef
    rw [Compile.loopBudget_eq_sum tIter tDone iters]
    have hL : (Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters] e) ++ Rf iters).length ≤ G := by
      rw [List.length_append, Compile.encodeTape_length, hAlen iters (Nat.le_refl _)]; omega
    have hdone1 : tDone + 1 ≤ 6 * G + 13 := by
      have h6 : 6 * (Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters] e) ++ Rf iters).length + 12 ≤ 6 * G + 12 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 6 hL) 12
      omega
    have href : (∑ m ∈ Finset.range iters, (tIter m + 1))
        = (∑ i ∈ Finset.range iters, Tf i) + iters := by
      have hcong : (∑ m ∈ Finset.range iters, tIter m)
          = ∑ m ∈ Finset.range iters, Tf (iters - 1 - m) := by
        apply Finset.sum_congr rfl
        intro m _
        simp only [htIter]
        rw [show iters - (m + 1) = iters - 1 - m from by omega]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one,
        hcong, Finset.sum_range_reflect]
    rw [href]
    have hTfsum : (∑ i ∈ Finset.range iters, Tf i)
        ≤ ∑ i ∈ Finset.range iters,
            ((9 * G * G + 9 * G + 30) * (i + 2) + Compile.physStepBudget G (cc i) + 12 * G + 32) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hsteps i (Finset.mem_range.mp hi)).2.2
    have hsplit : (∑ i ∈ Finset.range iters,
            ((9 * G * G + 9 * G + 30) * (i + 2) + Compile.physStepBudget G (cc i) + 12 * G + 32))
        = (9 * G * G + 9 * G + 30) * (∑ i ∈ Finset.range iters, (i + 2))
          + (∑ i ∈ Finset.range iters, Compile.physStepBudget G (cc i)) + iters * (12 * G + 32) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.sum_const, Finset.card_range, smul_eq_mul]
      ring
    have hTf2 : (∑ i ∈ Finset.range iters, Tf i)
        ≤ (9 * G * G + 9 * G + 30) * (∑ i ∈ Finset.range iters, (i + 2))
          + (∑ i ∈ Finset.range iters, Compile.physStepBudget G (cc i)) + iters * (12 * G + 32) :=
      le_trans hTfsum (le_of_eq hsplit)
    have hphys := Compile.physStepBudget_sum_le G cc iters
    have hmul : iters * (12 * G + 32) + iters = iters * (12 * G + 33) := by ring
    set P2 := (9 * G * G + 9 * G + 30) * (∑ i ∈ Finset.range iters, (i + 2)) with hP2def
    set SP := ∑ i ∈ Finset.range iters, Compile.physStepBudget G (cc i) with hSPdef
    set PHI := Compile.physStepBudget G ((∑ i ∈ Finset.range iters, cc i) + iters) with hPHIdef
    set Q32 := iters * (12 * G + 32) with hQ32def
    set Q33 := iters * (12 * G + 33) with hQ33def
    omega

/-- **Budget arithmetic for `compileForBnd`** — the three legs (entry `opCopy`,
the `loopTM` loop, exit `opClear`) sum under `physStepBudget G ((forBnd).cost s)`.
The loop's `physStepBudget G (∑ body-costs + iters)` is absorbed via the exact
superadditivity `physStepBudget_seq` (`cost = 1 + ∑ body-costs + iters²`); the
`Θ(G²·iters²)` headroom dominates the entry/exit `Θ(G²)` quadratics. -/
theorem Compile.forBndBudget_arith (G iters SC S2 : Nat)
    (hS2 : 2 * S2 = iters * iters + 3 * iters) :
    (9 * G * G + 9 * G + 30) * (iters + 2) + 1
      + ((9 * G * G + 9 * G + 30) * S2 + Compile.physStepBudget G (SC + iters)
          + iters * (12 * G + 33) + (6 * G + 13))
      + 1 + (9 * G * G + 9)
    ≤ Compile.physStepBudget G (1 + SC + iters * iters) := by
  have hle : iters ≤ iters * iters := by
    rcases Nat.eq_zero_or_pos iters with h | h
    · simp [h]
    · calc iters = iters * 1 := (Nat.mul_one iters).symm
        _ ≤ iters * iters := Nat.mul_le_mul_left iters h
  obtain ⟨q, hq⟩ : ∃ q, iters * iters = iters + q := ⟨iters * iters - iters, by omega⟩
  have hcost : 1 + SC + iters * iters = 1 + (SC + iters) + q := by omega
  rw [hcost, ← Compile.physStepBudget_seq]
  have hS2q : 2 * S2 = q + 4 * iters := by omega
  -- The `physStepBudget G (SC + iters)` term occurs on both sides; cancel it and
  -- prove the SC-free `core` so the `nlinarith` works on a smaller goal.
  have core : (9 * G * G + 9 * G + 30) * (iters + 2) + 1
        + (9 * G * G + 9 * G + 30) * S2 + iters * (12 * G + 33) + (6 * G + 13)
        + 1 + (9 * G * G + 9)
      ≤ 1 + Compile.physStepBudget G q := by
    simp only [Compile.physStepBudget]
    nlinarith [hS2q, hq, Nat.zero_le G, Nat.zero_le iters, Nat.zero_le q,
      Nat.zero_le (G * q), Nat.zero_le (G * G * q), Nat.zero_le (G * iters),
      Nat.zero_le (G * G * iters), Nat.zero_le (G * G),
      Nat.mul_le_mul_left (9 * G * G + 9 * G + 30) (show iters ≤ q + iters from by omega)]
  calc (9 * G * G + 9 * G + 30) * (iters + 2) + 1
          + ((9 * G * G + 9 * G + 30) * S2 + Compile.physStepBudget G (SC + iters)
              + iters * (12 * G + 33) + (6 * G + 13))
          + 1 + (9 * G * G + 9)
      = ((9 * G * G + 9 * G + 30) * (iters + 2) + 1
          + (9 * G * G + 9 * G + 30) * S2 + iters * (12 * G + 33) + (6 * G + 13)
          + 1 + (9 * G * G + 9)) + Compile.physStepBudget G (SC + iters) := by ring
    _ ≤ (1 + Compile.physStepBudget G q) + Compile.physStepBudget G (SC + iters) :=
        Nat.add_le_add_right core _
    _ = Compile.physStepBudget G (SC + iters) + 1 + Compile.physStepBudget G q := by ring

/-- **Residue-tolerant `compileForBnd` contract (GAP 1 — RE-PINNED 2026-06-11,
`sorry`).** The scratch-register fix for the snapshot-vs-clobber gap: the previous
pinning (no scratch interface) was **unprovable** — `Cmd.run` snapshots
`iters = |s.get bound|` at loop entry, the body may legally clobber `bound` AND
`counter` mid-loop, a TM cannot hold a runtime count in finite control, and no
tape region past the terminator survives a body run (the body contract's exit
residue is existential). The only sound storage is a register the body provably
never touches, so `compileForBnd` is now compiled at a **static scratch base
`sb`** with `K1 = sb` (remaining count, snapshotted from `bound` at entry) and
`K2 = sb + 1` (done count, an all-`1`s block — exactly the `replicate i 1` that
`counter` is re-materialised from each round). See `compileForBnd`'s docstring
for the pinned machine and the validated W-invariant/budget accounting.

Premises (mirroring what the `forBnd` case of `run_physical_residue_gen`
supplies):
- `hcnt`/`hbnd`: the program registers `counter`/`bound` lie below the scratch;
- `hlen`: the tape physically contains the scratch registers of this loop AND
  of every nested loop (`sb + 2 + 2·body.loopDepth ≤ s.length`);
- `hscratch`: all registers `≥ sb` are empty at entry (`K1`/`K2` start `[]`;
  the machine restores them to `[]` at exit — the exit tape is
  `encodeTape ((forBnd …).eval s) ++ res` and `(forBnd …).eval` never touches
  registers `≥ sb`, so emptiness at exit is forced by the contract shape);
- `hbody`: the body contract at scratch base `sb + 2`, quantified over every
  state with ITS scratch empty (the loop's fold states hold counts in `K1`/`K2 <
  sb + 2`, so they satisfy it) and its OWN per-call tape bound `G'` (the
  fold-state sizes grow, so a single fixed bound is dishonest). -/
theorem compileForBnd_sound_physical_residue
    (counter bound : Var) (sb : Nat) (rbody : CompiledCmd) (body : Cmd)
    (G : Nat) (s : State) (res0 : List Nat)
    (hbit : Compile.BitState s)
    (hcnt : counter < sb) (hbnd : bound < sb)
    (hlen : sb + 2 + 2 * body.loopDepth + 2 ≤ s.length)
    (huses_body : Cmd.UsesBelow body sb) 
    (hscratch : ∀ r, sb ≤ r → State.get s r = [])
    (hres0 : Compile.ValidResidue res0)
    (hG : State.size s + s.length + res0.length
            + (Cmd.forBnd counter bound body).cost s + 2 ≤ G)
    (hbody : ∀ (s' : State) (res' : List Nat) (G' : Nat),
      Compile.BitState s' → sb + 2 + 2 * body.loopDepth + 2 ≤ s'.length →
      (∀ r, sb + 2 ≤ r → State.get s' r = []) →
      Compile.ValidResidue res' →
      State.size s' + s'.length + res'.length + body.cost s' + 2 ≤ G' →
      ∃ (tt : Nat) (res : List Nat),
        Compile.ValidResidue res ∧
        State.size (body.eval s') + res.length ≤ State.size s' + res'.length + body.cost s' ∧
        runFlatTM tt rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res'])
          = some { state_idx := rbody.exit,
                   tapes := [([], 0, Compile.encodeTape (body.eval s') ++ res)] } ∧
        (∀ kk, kk < tt → ∀ ck,
            runFlatTM kk rbody.M (initFlatConfig rbody.M [Compile.encodeTape s' ++ res']) = some ck →
            ck.state_idx ≠ rbody.exit ∧ haltingStateReached rbody.M ck = false) ∧
        tt ≤ Compile.physStepBudget G' (body.cost s')) :
    ∃ (tt : Nat) (res : List Nat),
      Compile.ValidResidue res ∧
      State.size ((Cmd.forBnd counter bound body).eval s) + res.length
        ≤ State.size s + res0.length + (Cmd.forBnd counter bound body).cost s ∧
      runFlatTM tt (compileForBnd counter bound sb rbody).M
          (initFlatConfig (compileForBnd counter bound sb rbody).M [Compile.encodeTape s ++ res0])
        = some { state_idx := (compileForBnd counter bound sb rbody).exit,
                 tapes := [([], 0,
                   Compile.encodeTape ((Cmd.forBnd counter bound body).eval s) ++ res)] } ∧
      (∀ k, k < tt → ∀ ck,
          runFlatTM k (compileForBnd counter bound sb rbody).M
              (initFlatConfig (compileForBnd counter bound sb rbody).M
                [Compile.encodeTape s ++ res0]) = some ck →
          ck.state_idx ≠ (compileForBnd counter bound sb rbody).exit ∧
          haltingStateReached (compileForBnd counter bound sb rbody).M ck = false) ∧
      tt ≤ Compile.physStepBudget G ((Cmd.forBnd counter bound body).cost s) := by
  -- length facts
  have hsb_lt : sb < s.length :=
    Nat.lt_of_lt_of_le (by omega) (Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen)
  have hsb1_lt : sb + 1 < s.length :=
    Nat.lt_of_lt_of_le (by omega) (Nat.le_trans (Nat.le_add_right (sb + 2) (2 * body.loopDepth + 2)) hlen)
  have hbnd_lt : bound < s.length := Nat.lt_trans hbnd hsb_lt
  have hsbnil : State.get s sb = [] := hscratch sb (Nat.le_refl sb)
  set iters := (State.get s bound).length with hiters
  set e : State := s.set sb (State.get s bound) with hedef
  have helen : e.length = s.length := Compile.length_set s sb _ hsb_lt
  have hge_sb : State.get e sb = State.get s bound := Compile.get_set_eq s sb _ hsb_lt
  have hbit_reg_bound : ∀ x ∈ State.get s bound, x ≤ 1 := by
    intro x hx; exact hbit (State.get s bound) (by rw [State.get, List.getElem?_eq_getElem hbnd_lt]; exact List.getElem_mem hbnd_lt) x hx
  have hbit_e : Compile.BitState e := Compile.BitState_set s sb _ hbit hsb_lt hbit_reg_bound
  have hlen_e : sb + 2 + 2 * body.loopDepth + 2 ≤ e.length := by rw [helen]; exact hlen
  have hscr_e : ∀ r, sb + 2 ≤ r → State.get e r = [] := by
    intro r hr
    rw [hedef, Compile.get_set_ne s sb _ r hsb_lt (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by omega) hr)))]
    exact hscratch r (Nat.le_trans (Nat.le_add_right sb 2) hr)
  have hk2_e : State.get e (sb + 1) = [] := by
    rw [hedef, Compile.get_set_ne s sb _ (sb + 1) hsb_lt (Nat.succ_ne_self sb)]
    exact hscratch (sb + 1) (Nat.le_succ sb)
  have heitersb : (State.get e sb).length = iters := by rw [hge_sb]
  -- cost-sum bridge: machine body-costs = pure fold body-costs
  have hagree := Compile.forBndLoop_agree counter bound sb body s hbit hcnt hbnd hlen huses_body hscratch
  rw [← hedef, ← hiters] at hagree
  have hcc_eq : ∀ i, i < iters →
      body.cost (((Compile.forBndIterateState counter sb body)^[i] e).set counter (State.get ((Compile.forBndIterateState counter sb body)^[i] e) (sb + 1)))
        = body.cost ((Cmd.foldlState body counter (List.range i) s).set counter (List.replicate i 1)) := by
    intro i hi
    obtain ⟨hAg, hK2, _⟩ := hagree i (Nat.le_of_lt hi)
    rw [hK2]
    exact Cmd.cost_agree body sb huses_body (hAg.set counter (List.replicate i 1))
  have hcostsum : (Cmd.forBnd counter bound body).cost s
      = 1 + (∑ i ∈ Finset.range iters,
          body.cost (((Compile.forBndIterateState counter sb body)^[i] e).set counter (State.get ((Compile.forBndIterateState counter sb body)^[i] e) (sb + 1)))) + iters * iters := by
    rw [Cmd.cost_forBnd_eq counter bound body s, ← hiters]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    exact (hcc_eq i (Finset.mem_range.mp hi)).symm
  -- State.size e balance
  have hsize_e : State.size e = State.size s + iters := by
    have h := State.size_set_add s sb (State.get s bound)
    rw [hsbnil, List.length_nil, Nat.add_zero, ← hedef, ← hiters] at h
    omega
  -- ∑ j over range iters  (2*∑j + iters = iters*iters)
  have hsumj : 2 * (∑ j ∈ Finset.range iters, j) + iters = iters * iters := by
    have h := Finset.sum_range_id_mul_two iters
    have hpred : iters * (iters - 1) + iters = iters * iters := by
      cases iters with
      | zero => rfl
      | succ n => simp only [Nat.add_sub_cancel, Nat.succ_sub_one]; ring
    omega
  set cc : Nat → Nat := fun i =>
    body.cost (((Compile.forBndIterateState counter sb body)^[i] e).set counter (State.get ((Compile.forBndIterateState counter sb body)^[i] e) (sb + 1))) with hccdef
  have hquad : 3 * iters ≤ 2 + iters * iters := by
    rcases iters with _ | _ | n
    · omega
    · omega
    · -- `3(n+2) ≤ 2 + (n+2)² = n*n + 4n + 6`; `omega` closes once `n*n` is exposed.
      have h : (n + 1 + 1) * (n + 1 + 1) = n * n + 4 * n + 4 := by ring
      rw [h]; omega
  have hsumW : (∑ j ∈ Finset.range iters, (j + cc j + 1))
      = (∑ j ∈ Finset.range iters, j) + (∑ j ∈ Finset.range iters, cc j) + iters := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, Nat.mul_one]
  have hGe : State.size e + e.length + res0.length
      + (∑ j ∈ Finset.range iters, (j + cc j + 1)) + 2 ≤ G := by
    rw [hsumW, helen, hsize_e]
    -- atoms: hcostsum (FC = 1 + ∑cc + iters²), hsumj (2∑j+iters=iters²), hquad, hG
    set SJ := ∑ j ∈ Finset.range iters, j with hSJ
    set SC := ∑ j ∈ Finset.range iters, cc j with hSC
    omega
  -- d1: entry copy  (opCopy sb bound), residue stays res0
  obtain ⟨tc, hcopy_run, hcopy_traj, hcopy_bud⟩ :=
    Compile.opCopy_run s sb bound (Ne.symm (Nat.ne_of_lt hbnd)) hsb_lt hbnd_lt hbit res0 hres0
  simp only [hsbnil, List.length_nil, List.replicate_zero, List.append_nil] at hcopy_run
  rw [← hedef] at hcopy_run
  -- d2: the loop run
  obtain ⟨tl, res_out, hres_out, hWloop, hloop_run, hloop_traj, hloop_bud⟩ :=
    Compile.forBndLoop_run counter sb rbody body e res0 G hbit_e hcnt hlen_e huses_body
      hscr_e hk2_e hres0 (by rw [heitersb]; exact hGe) hbody
  rw [heitersb] at hloop_run hloop_bud hWloop
  -- d3: invariant + agree facts at iters
  have hinv := Compile.forBndLoop_invariant counter sb body e hbit_e hcnt hlen_e huses_body hscr_e hk2_e
  obtain ⟨hbit_iter, _, _, _, hK2iter⟩ := hinv iters (Nat.le_of_eq heitersb.symm)
  obtain ⟨_, hK2val, hlen_iter⟩ := hagree iters (Nat.le_refl iters)
  have hsb1_iter : sb + 1 < ((Compile.forBndIterateState counter sb body)^[iters] e).length := by rw [hlen_iter]; exact hsb1_lt
  obtain ⟨tcl, hclear_run, hclear_traj, hclear_bud⟩ :=
    Compile.clearRegionTM_run ((Compile.forBndIterateState counter sb body)^[iters] e) (sb + 1) res_out hsb1_iter hbit_iter hres_out
  -- forBndLoop_eval: cleared state = (forBnd).eval s
  have heval := Compile.forBndLoop_eval counter bound sb body s hbit hcnt hbnd hlen huses_body hscratch
  rw [← hiters, ← hedef] at heval
  -- the residue length after clear = res_out ++ replicate iters 0
  have hK2len : (State.get ((Compile.forBndIterateState counter sb body)^[iters] e) (sb + 1)).length = iters := by rw [hK2val, List.length_replicate]
  -- rewrite clear output: state → (forBnd).eval s ; residue replicate length → iters
  rw [show Op.eval (Op.clear (sb + 1)) ((Compile.forBndIterateState counter sb body)^[iters] e)
        = ((Compile.forBndIterateState counter sb body)^[iters] e).set (sb + 1) [] from rfl, heval, hK2len] at hclear_run
  -- opClear in initFlatConfig form (run + trajectory)
  have hstartcl : (Compile.opClear (sb + 1)).M.start = 0 := ClearGadget.clearRegionTM_start (sb + 1)
  have hinitcl : initFlatConfig (Compile.opClear (sb + 1)).M [Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters] e) ++ res_out]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters] e) ++ res_out)] } := by
    simp only [initFlatConfig, hstartcl, List.map_cons, List.map_nil]
  have hclear_run' : runFlatTM tcl (Compile.opClear (sb + 1)).M (initFlatConfig (Compile.opClear (sb + 1)).M [Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters] e) ++ res_out])
      = some { state_idx := (Compile.opClear (sb + 1)).exit,
               tapes := [([], 0, Compile.encodeTape ((Cmd.forBnd counter bound body).eval s) ++ (res_out ++ List.replicate iters 0))] } := by
    rw [hinitcl]; exact hclear_run
  have hclear_traj' : ∀ k, k < tcl → ∀ ck,
      runFlatTM k (Compile.opClear (sb + 1)).M (initFlatConfig (Compile.opClear (sb + 1)).M [Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters] e) ++ res_out]) = some ck →
      ck.state_idx ≠ (Compile.opClear (sb + 1)).exit ∧ haltingStateReached (Compile.opClear (sb + 1)).M ck = false := by
    rw [hinitcl]; exact hclear_traj
  have hhalt_cl : haltingStateReached (Compile.opClear (sb + 1)).M
      { state_idx := (Compile.opClear (sb + 1)).exit,
        tapes := [([], 0, Compile.encodeTape ((Cmd.forBnd counter bound body).eval s) ++ (res_out ++ List.replicate iters 0))] } = true := by
    have hex := (Compile.opClear (sb + 1)).exit_is_halt
    show (Compile.opClear (sb + 1)).M.halt.getD (Compile.opClear (sb + 1)).exit false = true
    simp only [List.getD, hex, Option.getD]
  obtain ⟨hinner_run, hinner_halt⟩ := compileSeq_sound_physical_residue
    (Compile.forBndLoopCmd counter sb rbody) (Compile.opClear (sb + 1)) e ((Compile.forBndIterateState counter sb body)^[iters] e) ((Cmd.forBnd counter bound body).eval s) res0 res_out (res_out ++ List.replicate iters 0)
    hbit_iter hres_out hloop_run hloop_traj hclear_run' hhalt_cl
  have hinner_traj := compileSeq_traj_physical_residue
    (Compile.forBndLoopCmd counter sb rbody) (Compile.opClear (sb + 1)) e ((Compile.forBndIterateState counter sb body)^[iters] e) res0 res_out hbit_iter hres_out hloop_run hloop_traj hclear_traj'
  obtain ⟨houter_run, _⟩ := compileSeq_sound_physical_residue
    (Compile.opCopy sb bound) (compileSeq (Compile.forBndLoopCmd counter sb rbody) (Compile.opClear (sb + 1)))
    s e ((Cmd.forBnd counter bound body).eval s) res0 res0 (res_out ++ List.replicate iters 0)
    hbit_e hres0 hcopy_run hcopy_traj hinner_run hinner_halt
  have houter_traj := compileSeq_traj_physical_residue
    (Compile.opCopy sb bound) (compileSeq (Compile.forBndLoopCmd counter sb rbody) (Compile.opClear (sb + 1)))
    s e res0 res0 hbit_e hres0 hcopy_run hcopy_traj hinner_traj
  have hsizefinal : State.size ((Cmd.forBnd counter bound body).eval s) + iters = State.size ((Compile.forBndIterateState counter sb body)^[iters] e) := by
    have h := State.size_set_add ((Compile.forBndIterateState counter sb body)^[iters] e) (sb + 1) ([] : List Nat)
    rw [hK2len, List.length_nil, Nat.add_zero] at h
    rw [← heval]; exact h
  rw [hsumW, hsize_e] at hWloop
  refine ⟨tc + 1 + (tl + 1 + tcl), res_out ++ List.replicate iters 0,
    Compile.ValidResidue_append_replicate_zero res_out iters hres_out, ?_, houter_run, houter_traj, ?_⟩
  · rw [List.length_append, List.length_replicate]
    have hccbr : (Finset.range iters).sum cc = ∑ j ∈ Finset.range iters, cc j := rfl
    omega
  · have hLc : (Compile.encodeTape s ++ res0).length ≤ G := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    have hLcl : (Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters] e) ++ res_out).length ≤ G := by
      rw [List.length_append, Compile.encodeTape_length, hlen_iter]; omega
    have htc : tc ≤ (9 * G * G + 9 * G + 30) * (iters + 2) := by
      have hbase : 9 * (Compile.encodeTape s ++ res0).length * (Compile.encodeTape s ++ res0).length + 9 * (Compile.encodeTape s ++ res0).length + 30 ≤ 9 * G * G + 9 * G + 30 :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 9 hLc) hLc)
          (Nat.mul_le_mul_left 9 hLc)) (Nat.le_refl 30)
      calc tc ≤ (9 * (Compile.encodeTape s ++ res0).length * (Compile.encodeTape s ++ res0).length + 9 * (Compile.encodeTape s ++ res0).length + 30) * ((State.get s bound).length + 2) := hcopy_bud
        _ = (9 * (Compile.encodeTape s ++ res0).length * (Compile.encodeTape s ++ res0).length + 9 * (Compile.encodeTape s ++ res0).length + 30) * (iters + 2) := by rw [← hiters]
        _ ≤ (9 * G * G + 9 * G + 30) * (iters + 2) := Nat.mul_le_mul_right _ hbase
    have htcl : tcl ≤ 9 * G * G + 9 := by
      calc tcl ≤ 9 * (Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters] e) ++ res_out).length * (Compile.encodeTape ((Compile.forBndIterateState counter sb body)^[iters] e) ++ res_out).length + 9 := hclear_bud
        _ ≤ 9 * G * G + 9 := Nat.add_le_add_right
            (Nat.mul_le_mul (Nat.mul_le_mul_left 9 hLcl) hLcl) 9
    have hS2sum : 2 * (∑ i ∈ Finset.range iters, (i + 2)) = iters * iters + 3 * iters := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
      omega
    have hbud := Compile.forBndBudget_arith G iters (∑ i ∈ Finset.range iters, cc i)
      (∑ i ∈ Finset.range iters, (i + 2)) hS2sum
    rw [← hcostsum] at hbud
    simp only [hccdef] at hbud
    refine le_trans ?_ hbud
    omega

/-- **★ The designed residue induction (the assembly of `Compile_run_physical_residue`).**
Carries an arbitrary incoming residue `res0` (live instance: `res0 = []`), a shared
tape bound `G` (`hG`), and the threading hyps. The conclusion bundles:
- **① the W-invariant** `State.size (c.eval s) + |res| ≤ State.size s + |res0| + c.cost s`
  (joint size+residue grows by ≤ cost; non-compounding — this is what keeps the
  residue polynomially bounded and lets one `G` bound every sub-fragment tape);
- the residue-tolerant physical run + trajectory;
- **② the budget** `t ≤ physStepBudget G (c.cost s)` (exactly superadditive).

**Proof design (induction on `c`):**
- `op o`: `compileOp_sound_physical_residue` (`hbnd` from `Op.inBounds_of_UsesBelow`);
  ① per-op from the residue formula (append/clear/head/nonEmpty: equality;
  the 7 sorry ops owe it — see HANDOFF top-down step 4); ② from `9·L²+9·L+30`, `L ≤ G`.
- `seq c1 c2`: IH₁ on `(s,res0)` → `(mid,res1)`; `BitState mid`,`k ≤ mid.length` via
  `Cmd.eval_preserves_BitState`/`Cmd.eval_length_ge`; IH₂ on `(mid,res1)`;
  `compileSeq_sound_physical_residue` (run+halt) + `compileSeq_traj_physical_residue`
  (trajectory). ① telescopes; ② is the exact `physStepBudget` superadditivity.
- `ifBit`/`forBnd`: dispatch to the two residue combinators above (their hyps are the IHs).

The `op`/`seq` cases are the structural heart; they reduce to PROVEN combinators.
Body is `sorry` pending the relocation upstream (GAP 3) + the two combinators. -/
theorem Compile.run_physical_residue_gen (c : Cmd) (k : Nat) (s : State)
    (res0 : List Nat) (G : Nat)
    (hbit : Compile.BitState s) (hk : k + 2 * c.loopDepth + 2 ≤ s.length)
    (huses : Cmd.UsesBelow c k)
    (hscratch : ∀ r, k ≤ r → State.get s r = [])
    (hres0 : Compile.ValidResidue res0)
    (hG : State.size s + s.length + res0.length + c.cost s + 2 ≤ G) :
    ∃ (t : Nat) (res : List Nat),
      Compile.ValidResidue res ∧
      State.size (c.eval s) + res.length ≤ State.size s + res0.length + c.cost s ∧
      runFlatTM t (Compile k c) (initFlatConfig (Compile k c) [Compile.encodeTape s ++ res0])
          = some { state_idx := Compile.exit k c,
                   tapes := [([], 0, Compile.encodeTape (c.eval s) ++ res)] } ∧
      (∀ k', k' < t → ∀ ck,
          runFlatTM k' (Compile k c)
              (initFlatConfig (Compile k c) [Compile.encodeTape s ++ res0]) = some ck →
          ck.state_idx ≠ Compile.exit k c ∧
          haltingStateReached (Compile k c) ck = false) ∧
      t ≤ Compile.physStepBudget G (c.cost s) := by
  induction c generalizing k s res0 G with
  | op o =>
      -- `op` reduces to the per-op residue contract. `inBounds` from the static bound.
      have hks : k ≤ s.length := by
        simp only [Cmd.loopDepth] at hk; omega
      have hbnd : o.inBounds s := Op.inBounds_of_UsesBelow o k s huses hks
      -- Resolution B: the op's scratch base is `k`; `k`, `k+1` exist (`+2` padding)
      -- and are empty (`hscratch`, since both are `≥ k`).
      have hsb1 : k + 1 < s.length := by simp only [Cmd.loopDepth] at hk; omega
      have hsbe : State.get s k = [] := hscratch k (Nat.le_refl k)
      have hsb1e : State.get s (k + 1) = [] := hscratch (k + 1) (Nat.le_succ k)
      obtain ⟨t, res_out, hres, hW, hrun, htraj, hbud⟩ :=
        compileOp_sound_physical_residue k o s res0 hbit hbnd hres0 hsb1 hsbe hsb1e huses
      refine ⟨t, res_out, hres, hW, hrun, htraj, ?_⟩
      · -- ② budget: `(9·L²+9·L+30)·(cost+1) ≤ physStepBudget G (Op.cost o s)`, since
        -- `L ≤ G` and `(9G²+9G+30)·(cost+1)` sits termwise under `(9G²+9G+33)·(8·cost+8)`.
        -- Explicit `Nat.*` monotonicity terms throughout: `omega`/`gcongr` hit `whnf`
        -- timeouts on products of two-atom sums (the recorded gotcha).
        have hL : (Compile.encodeTape s ++ res0).length ≤ G := by
          rw [List.length_append, Compile.encodeTape_length]; omega
        set L := (Compile.encodeTape s ++ res0).length with hLdef
        have h1 : (54 * L * L + 54 * L + 180) * (Op.cost o s + 1)
                  ≤ (54 * G * G + 54 * G + 180) * (Op.cost o s + 1) :=
          Nat.mul_le_mul_right _
            (Nat.add_le_add
              (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 54 hL) hL)
                (Nat.mul_le_mul_left 54 hL)) (Nat.le_refl 180))
        -- `54 ≤ 72 = 8·9`: the loosened constant still sits under physStepBudget's `(·)·(8·cost+8)`.
        have h2 : (54 * G * G + 54 * G + 180) * (Op.cost o s + 1)
                  ≤ (9 * G * G + 9 * G + 33) * (8 * Op.cost o s + 8) :=
          le_trans (Nat.mul_le_mul_right _ (by
              have hG : 54 * G ≤ 72 * G := Nat.mul_le_mul_right G (by norm_num)
              have hGG : 54 * G * G ≤ 72 * G * G := Nat.mul_le_mul_right G hG
              omega :
              54 * G * G + 54 * G + 180 ≤ 72 * G * G + 72 * G + 264))
            (Nat.le_of_eq (by ring))
        show t ≤ Compile.physStepBudget G (Op.cost o s)
        rw [Compile.physStepBudget]
        exact le_trans (le_trans hbud (le_trans h1 h2)) (Nat.le_add_right _ _)
  | seq c1 c2 ih1 ih2 =>
      -- thread residue `res0 → res1 → res2` through both fragments.
      simp only [Cmd.loopDepth] at hk
      have hd1 : c1.loopDepth ≤ max c1.loopDepth c2.loopDepth := Nat.le_max_left _ _
      have hd2 : c2.loopDepth ≤ max c1.loopDepth c2.loopDepth := Nat.le_max_right _ _
      have hks : k ≤ s.length := by omega
      have hk1' : k + 2 * c1.loopDepth + 2 ≤ s.length := by omega
      have hG1 : State.size s + s.length + res0.length + c1.cost s + 2 ≤ G := by
        rw [Cmd.cost_seq] at hG; omega
      obtain ⟨t1, res1, hres1, hW1, hrun1, htraj1, hbud1⟩ :=
        ih1 k s res0 G hbit hk1' huses.1 hscratch hres0 hG1
      have hbit_mid : Compile.BitState (c1.eval s) :=
        Cmd.eval_preserves_BitState c1 k s huses.1 hks hbit
      have hmidge : s.length ≤ (c1.eval s).length := Cmd.eval_length_ge c1 s
      have hk2' : k + 2 * c2.loopDepth + 2 ≤ (c1.eval s).length := by omega
      have hmidlen : (c1.eval s).length ≤ s.length := by
        have := Cmd.eval_length_le c1 k huses.1 s; rwa [Nat.max_eq_left hks] at this
      have hscratch_mid : ∀ r, k ≤ r → State.get (c1.eval s) r = [] := fun r hr => by
        rw [Cmd.eval_get_frame c1 k huses.1 s r hr]; exact hscratch r hr
      have hG2 : State.size (c1.eval s) + (c1.eval s).length + res1.length
                    + c2.cost (c1.eval s) + 2 ≤ G := by
        rw [Cmd.cost_seq] at hG; omega
      obtain ⟨t2, res2, hres2, hW2, hrun2, htraj2, hbud2⟩ :=
        ih2 k (c1.eval s) res1 G hbit_mid hk2' huses.2 hscratch_mid hres1 hG2
      have hhalt2 : haltingStateReached (compileCmd k c2).M
          { state_idx := (compileCmd k c2).exit,
            tapes := [([], 0, Compile.encodeTape (c2.eval (c1.eval s)) ++ res2)] } = true := by
        have hex := (compileCmd k c2).exit_is_halt
        show (compileCmd k c2).M.halt.getD (compileCmd k c2).exit false = true
        simp only [List.getD, hex, Option.getD]
      obtain ⟨hrunseq, _⟩ := compileSeq_sound_physical_residue (compileCmd k c1) (compileCmd k c2)
        s (c1.eval s) (c2.eval (c1.eval s)) res0 res1 res2 hbit_mid hres1
        hrun1 htraj1 hrun2 hhalt2
      have htrajseq := compileSeq_traj_physical_residue (compileCmd k c1) (compileCmd k c2)
        s (c1.eval s) res0 res1 hbit_mid hres1 hrun1 htraj1 htraj2
      refine ⟨t1 + 1 + t2, res2, hres2, ?_, ?_, ?_, ?_⟩
      · -- ① telescopes from hW1, hW2.
        rw [Cmd.eval_seq, Cmd.cost_seq]; omega
      · -- run.
        rw [Cmd.eval_seq]; exact hrunseq
      · -- trajectory.
        exact htrajseq
      · -- ② exact `physStepBudget` superadditivity.
        rw [Cmd.cost_seq, ← Compile.physStepBudget_seq]; omega
  | ifBit tt cT cE ihT ihE =>
      -- dispatch to the residue branch combinator; the IHs supply the branch contracts.
      simp only [Cmd.loopDepth] at hk
      have hdT : cT.loopDepth ≤ max cT.loopDepth cE.loopDepth := Nat.le_max_left _ _
      have hdE : cE.loopDepth ≤ max cT.loopDepth cE.loopDepth := Nat.le_max_right _ _
      have hks : k ≤ s.length := by omega
      have hT : s.get tt = [1] → _ := fun htrue =>
        ihT k s res0 G hbit (by omega) huses.2.1 hscratch hres0 (by
          have hc := Cmd.cost_ifBit_true tt cT cE s htrue; rw [hc] at hG; omega)
      have hE : s.get tt ≠ [1] → _ := fun hfalse =>
        ihE k s res0 G hbit (by omega) huses.2.2 hscratch hres0 (by
          have hc := Cmd.cost_ifBit_false tt cT cE s hfalse; rw [hc] at hG; omega)
      have htlt : tt < s.length := Nat.lt_of_lt_of_le huses.1 hks
      have hG' : State.size s + s.length + res0.length + 2 ≤ G := by omega
      have hcomb := compileIfBit_sound_physical_residue tt (compileCmd k cT) (compileCmd k cE)
        cT.eval cE.eval cT.cost cE.cost G s res0 htlt hbit hres0 hG' hT hE
      have heval : (Cmd.ifBit tt cT cE).eval s
          = if s.get tt = [1] then cT.eval s else cE.eval s := by
        by_cases hb : s.get tt = [1]
        · rw [Cmd.eval_ifBit_true tt cT cE s hb, if_pos hb]
        · rw [Cmd.eval_ifBit_false tt cT cE s hb, if_neg hb]
      have hcost : (Cmd.ifBit tt cT cE).cost s
          = 1 + if s.get tt = [1] then cT.cost s else cE.cost s := by
        by_cases hb : s.get tt = [1]
        · rw [Cmd.cost_ifBit_true tt cT cE s hb, if_pos hb]
        · rw [Cmd.cost_ifBit_false tt cT cE s hb, if_neg hb]
      obtain ⟨t', res', hres', hW', hrun', htraj', hbud'⟩ := hcomb
      rw [← heval] at hW' hrun'
      rw [← hcost] at hW' hbud'
      exact ⟨t', res', hres', hW', hrun', htraj', hbud'⟩
  | forBnd cnt bnd body ihbody =>
      -- dispatch to the residue loop combinator; the IH supplies the body contract
      -- at scratch base `k + 2` (with its own per-call tape bound `G'`, as the
      -- loop's fold-states grow). `K1 = k`/`K2 = k + 1` emptiness is `hscratch`.
      simp only [Cmd.loopDepth] at hk
      exact compileForBnd_sound_physical_residue cnt bnd k (compileCmd (k + 2) body) body
        G s res0 hbit huses.1 huses.2.1 (by omega) huses.2.2 hscratch hres0 hG
        (fun s' res' G' hb hlen' hscr' hr hg =>
          ihbody (k + 2) s' res' G' hb hlen'
            (Cmd.UsesBelow_mono (by omega) huses.2.2) hscr' hr hg)
/-- **★ The C2 obligation, residue-tolerant physical compiler contract (Risk C2),
PROVEN from the assembly** — the `res0 = []` instance of
`Compile.run_physical_residue_gen`. Accounts for the tape never shrinking: the
exit tape is `encodeTape (c.eval s) ++ res` for some `ValidResidue` residue `res`,
head rewound to `0`. Provable for ALL ops (including deletion ops like
`clear`/`tail`) because the residue absorbs the cells vacated by left-shifting.

The budget is `physStepBudget G (c.cost s)`, the **correct, provable** shape
(exactly superadditive under `seq`). The earlier `overhead (size + cost)` form was
unprovable — too small in both degree and the register count `s.length` (Finding A);
`physStepBudget`'s tape bound `G = State.size s + s.length + c.cost s + 2` carries
`s.length` explicitly. The threading hypotheses (`Cmd.UsesBelow c k` /
`k ≤ s.length` / `Cmd.NoConsLen c`) are what the bridge supplies (see the
register-count discussion in HANDOFF.md). Its proof body is `sorry`-free; the only
remaining gaps are the leaf gadgets (the 7 stub ops in
`compileOp_sound_physical_residue` + the 2 stub loop/branch machines feeding the
residue combinators).

The decider bridge (`bitDeciderTM`) reads the answer from register `0` via
`decodeTape`, which ignores the residue (`decodeTape_encodeTape_append`), so the
residue is invisible to the decider. -/
theorem Compile_run_physical_residue (c : Cmd) (k : Nat) (s : State)
    (hbit : Compile.BitState s) (hk : k + 2 * c.loopDepth + 2 ≤ s.length)
    (huses : Cmd.UsesBelow c k)
    (hscratch : ∀ r, k ≤ r → State.get s r = []) :
    ∃ (t : Nat) (res : List Nat),
      Compile.ValidResidue res ∧
      runFlatTM t (Compile k c) (initFlatConfig (Compile k c) [Compile.encodeTape s])
          = some { state_idx := Compile.exit k c,
                   tapes := [([], 0, Compile.encodeTape (c.eval s) ++ res)] } ∧
      (∀ k', k' < t → ∀ ck,
          runFlatTM k' (Compile k c)
              (initFlatConfig (Compile k c) [Compile.encodeTape s]) = some ck →
          ck.state_idx ≠ Compile.exit k c ∧
          haltingStateReached (Compile k c) ck = false) ∧
      t ≤ Compile.physStepBudget (State.size s + s.length + c.cost s + 2) (c.cost s) := by
  obtain ⟨t, res, hres, _hW, hrun, htraj, hbud⟩ :=
    Compile.run_physical_residue_gen c k s [] (State.size s + s.length + c.cost s + 2)
      hbit hk huses hscratch Compile.ValidResidue_nil (by rw [List.length_nil]; omega)
  refine ⟨t, res, hres, ?_, ?_, hbud⟩
  · rw [List.append_nil] at hrun; exact hrun
  · intro k' hk' ck hck
    exact htraj k' hk' ck (by rw [List.append_nil]; exact hck)

/-- The compiled decider machine: run `Compile k c` (scratch base `k`), then the
bit-test gadget. The gadget converts register `0`'s answer (on the tape) into a
distinct halting *state*, as `DecidesBy` requires. -/
def Compile.bitDeciderTM (c : Cmd) (k : Nat) : FlatTM :=
  composeFlatTM (Compile k c) Compile.bitTestTM (Compile.exit k c)

theorem Compile.bitDeciderTM_valid (c : Cmd) (k : Nat) : validFlatTM (Compile.bitDeciderTM c k) :=
  composeFlatTM_valid (Compile k c) Compile.bitTestTM (Compile.exit k c)
    (Compile_valid k c) Compile.bitTestTM_valid (Compile_exit_lt k c)
    (Compile_tapes k c) Compile.bitTestTM_tapes

theorem Compile.bitDeciderTM_tapes (c : Cmd) (k : Nat) : (Compile.bitDeciderTM c k).tapes = 1 := by
  show (composeFlatTM (Compile k c) Compile.bitTestTM (Compile.exit k c)).tapes = 1
  rw [composeFlatTM_tapes, Compile_tapes]

/-- The canonical single-register tape `encodeTape [r]` has length `r.length + 3`
(the leading sentinel, the shifted register, the `0` delimiter, and the trailing
`endMark`). Used to bound the `DecidesBy.encode_size` of the canonical decider
bridge. -/
theorem Compile.encodeTape_singleton_length (r : List Nat) :
    (Compile.encodeTape [r]).length = r.length + 3 := by
  simp [Compile.encodeTape, Compile.encodeRegs, Compile.shiftReg]

/-- **C6 headline.** Running `bitDeciderTM c` on `encodeTape s` halts, within
`physStepBudget G (cost s) + 3` steps (`G = size s + s.length + cost s + 2`), in
state `1 + (Compile c).states` when register `0` of `c.eval s` is `[1]` (accept)
and `2 + (Compile c).states` when it is `[0]` (reject). Combines the physical run
contract of `Compile c` (`Compile_run_physical_residue'`, the residue/`physStepBudget`
form — the unprimed `overhead` form is the wrong budget shape and is unprovable,
Finding A) with the `sorry`-free gadget run lemma, via `composeFlatTM_run`. The
`UsesBelow`/`NoConsLen`/`k ≤ s.length` hypotheses are what the primed contract
threads; consumers (`DecidesLang(')`) supply them. (The `+3` is one bridge step
plus the two gadget steps — step past the leading sentinel, then read.) -/
theorem Compile.bitDecider_run (c : Cmd) (s : State) (b : Nat) (k : Nat)
    (hbitst : Compile.BitState s) (hk : k + 2 * c.loopDepth + 2 ≤ s.length)
    (huses : Cmd.UsesBelow c k)
    (hscratch : ∀ r, k ≤ r → State.get s r = [])
    (hbit : b = 0 ∨ b = 1) (h0 : (c.eval s).get 0 = [b]) :
    ∃ cfg,
      runFlatTM (Compile.physStepBudget (State.size s + s.length + c.cost s + 2)
            (c.cost s) + 3) (Compile.bitDeciderTM c k)
          (initFlatConfig (Compile.bitDeciderTM c k) [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (Compile.bitDeciderTM c k) cfg = true ∧
      cfg.state_idx = (if b = 1 then 1 else 2) + (Compile k c).states := by
  obtain ⟨tl0, htl0⟩ := Compile.encodeTape_eq_cons_of_get_zero (c.eval s) b h0
  obtain ⟨t1, res, _hres, hrun1, htraj1, ht1⟩ :=
    Compile_run_physical_residue c k s hbitst hk huses hscratch
  -- Rewrite the physical exit tape via the encoding lemma (leading sentinel).
  -- The residue trails the encoded output; the gadget reads only positions 0–1,
  -- so fold the residue into the tail `tl := tl0 ++ res`.
  rw [htl0, List.cons_append, List.cons_append] at hrun1
  set tl : List Nat := tl0 ++ res with htl
  -- The gadget's exit state for this bit.
  set dst : Nat := if b = 1 then 1 else 2 with hdst
  -- Gadget run + halt (split on the bit): step past the sentinel `3`, then read.
  have hrun2 : runFlatTM 2 Compile.bitTestTM
      { state_idx := Compile.bitTestTM.start,
        tapes := [([], 0, Compile.endMark :: (b + 1) :: tl)] }
      = some { state_idx := dst, tapes := [([], 1, Compile.endMark :: (b + 1) :: tl)] } := by
    rcases hbit with hb | hb <;> subst hb <;>
      simp only [Compile.bitTestTM_start, hdst] <;> rfl
  have hhalt2 : haltingStateReached Compile.bitTestTM
      { state_idx := dst, tapes := [([], 1, Compile.endMark :: (b + 1) :: tl)] } = true := by
    rcases hbit with hb | hb <;> subst hb <;> rfl
  -- The first tape symbol is the leading sentinel `endMark = 3 < 4`.
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.endMark :: (b + 1) :: tl)
      = some v → v < max (Compile k c).sig Compile.bitTestTM.sig := by
    intro v hv
    have : v = Compile.endMark := by simpa [currentTapeSymbol] using hv.symm
    subst this
    rw [Compile_sig, Compile.bitTestTM_sig]
    decide
  have hstate0 : (initFlatConfig (Compile k c) [Compile.encodeTape s]).state_idx
      < (Compile k c).states := (Compile_valid k c).1
  -- Compose.
  have hcomp := composeFlatTM_run (M₁ := Compile k c) (M₂ := Compile.bitTestTM)
    (exit := Compile.exit k c) (Compile_valid k c) Compile.bitTestTM_valid
    (Compile_exit_lt k c)
    (initFlatConfig (Compile k c) [Compile.encodeTape s]) hstate0
    [] 0 (Compile.endMark :: (b + 1) :: tl) hsym hrun1 htraj1 hrun2 hhalt2
  obtain ⟨hcrun, hchalt⟩ := hcomp
  -- Pad the run up to the stated budget.
  obtain ⟨kpad, hkpad⟩ := Nat.le.dest ht1
  refine ⟨{ state_idx := dst + (Compile k c).states,
            tapes := [([], 1, Compile.endMark :: (b + 1) :: tl)] }, ?_, ?_, ?_⟩
  · show runFlatTM (Compile.physStepBudget (State.size s + s.length + c.cost s + 2)
          (c.cost s) + 3) (Compile.bitDeciderTM c k)
        (initFlatConfig (Compile.bitDeciderTM c k) [Compile.encodeTape s]) = _
    have hbudget : Compile.physStepBudget (State.size s + s.length + c.cost s + 2)
        (c.cost s) + 3 = (t1 + 1 + 2) + kpad := by omega
    rw [hbudget]
    exact runFlatTM_extend (M := Compile.bitDeciderTM c k) hcrun hchalt
  · exact hchalt
  · show dst + (Compile k c).states = (if b = 1 then 1 else 2) + (Compile k c).states
    rw [hdst]

/-- Halt bits of `bitDeciderTM` past `(Compile k c).states` are exactly the
gadget's: the composed halt vector is `replicate (Compile k c).states false ++
bitTestTM.halt`. Gives the two accept/reject states' `halting_*` obligations. -/
theorem Compile.bitDeciderTM_halt_shift (c : Cmd) (k : Nat) (i : Nat) :
    (Compile.bitDeciderTM c k).halt.getD (i + (Compile k c).states) false
      = Compile.bitTestTM.halt.getD i false := by
  show (composedHalt (Compile k c) Compile.bitTestTM).getD (i + (Compile k c).states) false
      = Compile.bitTestTM.halt.getD i false
  rw [composedHalt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [List.length_replicate]; exact Nat.le_add_left _ _),
      List.length_replicate, Nat.add_sub_cancel]
