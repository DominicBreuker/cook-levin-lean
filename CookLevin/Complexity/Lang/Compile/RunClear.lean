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

/-! # `Compile/RunClear` — append + residue toolkit + `clear` run stack (Phase 1-refinement)

First module of the `RunLemmas` split (see `REFACTOR-HANDOFF.md`). The base of
the run-lemma DAG: the two append ops' per-op soundness, the
`compileSeq_compose_physical` composition lemma, the shared residue-tolerant
tape toolkit (`ValidResidue`/`TapeOK` helpers, `BitState_*`/`set_*`), and the
`clear` op run stack ending at `clearRegionTM_run`. Consumed by `RunMove`,
`RunCopyTail`, `RunEqBit`. -/

set_option autoImplicit false

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators

/-! ### Per-op soundness for `appendOne`/`appendZero` (general `dst`, LINEAR budget)

The two append ops are the only `compileOp`s with real TM bodies. The lemma
below discharges `compileOp_sound` for both — at **general `dst`** and with the
**linear tape-length budget** `2 · (encodeTape s).length + 3`. This is the
*composable* per-fragment budget (ROADMAP Risk C2 / plan step 1b): the quadratic
`overhead` budget the earlier version used does **not** compose (summing `~cost`
quadratics → cubic; see the finding block below `compileSeq_sound`), whereas
linear per-fragment bounds sum to a quadratic total.

It composes `AppendGadget.appendAt_run_steps` (explicit step count) with
`appendAt_steps_le` (the step count is exactly `≤ 2·tapeLen + 3`). The leading
sentinel of `encodeTape` is folded into the first marker-free block so the
gadget runs from head `0`. (Recovering the old quadratic budget, if ever needed,
is just `Nat`-monotone padding: `2·tapeLen + 3 ≤ overhead (tapeLen + 1)`.) -/
theorem Compile.appendBit_sound (bit : Nat) (hb : bit ≤ 1)
    (s : State) (dst : Var) (hbit : Compile.BitState s) (hdst : dst < s.length) :
    ∃ cfg,
      runFlatTM (2 * (Compile.encodeTape s).length + 3)
          (AppendGadget.appendAtTM (bit + 1) dst)
          (initFlatConfig (AppendGadget.appendAtTM (bit + 1) dst)
            [Compile.encodeTape s]) = some cfg ∧
      haltingStateReached (AppendGadget.appendAtTM (bit + 1) dst) cfg = true ∧
      Compile.decodeTape cfg = s.set dst (s.get dst ++ [bit]) := by
  have h_ins : bit + 1 < 4 := by omega
  set post : List Nat := Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] with hpost
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskip
  set body : List Nat := Compile.shiftReg (s.get dst) with hbody
  have hget_mem : s.get dst ∈ s := by
    rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
  -- Side conditions for `appendAt_run_steps`, all from bit-shape.
  have hshift_lt : ∀ (r : List Nat), (∀ x ∈ r, x ≤ 1) → ∀ x ∈ Compile.shiftReg r, x < 4 := by
    intro r hr x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hr y hy; omega
  have hshift_ne : ∀ (r : List Nat), ∀ x ∈ Compile.shiftReg r, x ≠ 0 := by
    intro r x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; omega
  have hlen : skipped.length = dst := by
    rw [hskip, List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hdst)]
  have h_pre : ∀ x ∈ ([] : List Nat), x < 4 := by intro x hx; cases hx
  have h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    intro b hbm
    rw [hskip, List.mem_map] at hbm
    obtain ⟨r, hr, rfl⟩ := hbm
    exact ⟨hshift_ne r, hshift_lt r (fun x hx => hbit r (List.mem_of_mem_take hr) x hx)⟩
  have hbody_ne : ∀ x ∈ body, x ≠ 0 := by rw [hbody]; exact hshift_ne _
  have hbody_lt : ∀ x ∈ body, x < 4 := by
    rw [hbody]; exact hshift_lt _ (fun x hx => hbit _ hget_mem x hx)
  have hpost_lt : ∀ x ∈ post, x < 4 := by
    rw [hpost]; intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeRegs_lt_four _
        (fun b hbm y hy => hbit b (List.mem_of_mem_drop hbm) y hy) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide
  -- **Fold the leading sentinel into the first marker-free block.** The new
  -- `encodeTape` is `endMark :: (encodeRegs s ++ [endMark])`, but the gadget
  -- starts at head `0` (`initFlatConfig`). Rather than bridge head `0 → 1`, we
  -- absorb the leading `endMark` into the first scanned block: into `body` when
  -- `dst = 0` (no skipped registers), or into the first skipped register when
  -- `dst ≥ 1`. Both keep the gadget's head at `0` over the *full* tape.
  have key : ∃ (sk : List (List Nat)) (bd : List Nat),
      sk.length = dst ∧
      (∀ b ∈ sk, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) ∧
      (∀ x ∈ bd, x ≠ 0) ∧ (∀ x ∈ bd, x < 4) ∧
      AppendGadget.regBlocks sk ++ bd
        = Compile.endMark :: (AppendGadget.regBlocks skipped ++ body) := by
    cases hsk : skipped with
    | nil =>
        refine ⟨[], Compile.endMark :: body, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hlen, hsk]
        · intro b hb; cases hb
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_ne x h
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_lt x h
        · simp [AppendGadget.regBlocks_nil]
    | cons hd tl =>
        refine ⟨(Compile.endMark :: hd) :: tl, body, ?_, ?_, hbody_ne, hbody_lt, ?_⟩
        · rw [hsk] at hlen; simpa using hlen
        · intro b hb
          rcases List.mem_cons.mp hb with h | h
          · subst h
            refine ⟨?_, ?_⟩
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).1 x h0
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).2 x h0
          · exact h_skip b (by rw [hsk]; exact List.mem_cons_of_mem _ h)
        · simp [AppendGadget.regBlocks_cons]
  obtain ⟨sk, bd, hlen_sk, h_skip_sk, hbd_ne, hbd_lt, hsfold⟩ := key
  -- The gadget run lemma, with its explicit step count, on the folded blocks.
  obtain ⟨st', hrun, hhalt⟩ :=
    AppendGadget.appendAt_run_steps (bit + 1) h_ins dst [] sk bd post hlen_sk
      h_pre h_skip_sk hbd_ne hbd_lt hpost_lt
  -- Name the explicit exit head for convenience.
  set hd' : Nat := [].length + (AppendGadget.regBlocks sk).length + bd.length
      + (0 :: post).length with hd'_def
  -- The sentinel-free split: `regBlocks skipped ++ body ++ 0 :: post` is the
  -- registers part of `encodeTape s` (= `encodeRegs s ++ [endMark]`).
  have hsplit0 : AppendGadget.regBlocks skipped ++ body ++ 0 :: post
      = Compile.encodeRegs s ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost]; exact Compile.encodeTape_split s dst hdst
  -- Reattaching the leading sentinel recovers the full `encodeTape s`.
  have hsplit : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post
      = Compile.encodeTape s := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, hsplit0]
  rw [List.length_nil, hsplit] at hrun
  have hinit : initFlatConfig (AppendGadget.appendAtTM (bit + 1) dst) [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := by
    simp only [initFlatConfig, AppendGadget.appendAtTM_start, List.map_cons, List.map_nil]
  -- The explicit step count is **linear** in the tape length (`≤ 2·tapeLen + 3`,
  -- directly from `appendAt_steps_le`); this is the composable per-fragment bound.
  have hstep_le : AppendGadget.appendAt_steps sk bd post
      ≤ 2 * (Compile.encodeTape s).length + 3 := by
    have hb' := AppendGadget.appendAt_steps_le sk bd post
    have hL : (AppendGadget.regBlocks sk ++ bd ++ 0 :: post).length
        = (Compile.encodeTape s).length := by rw [← hsplit]; simp
    rw [hL] at hb'; exact hb'
  obtain ⟨k, hk⟩ := Nat.le.dest hstep_le
  -- The output tape decodes to the evaluated state.
  have htape0 : AppendGadget.regBlocks skipped ++ body ++ (bit + 1) :: 0 :: post
      = Compile.encodeRegs (s.set dst (s.get dst ++ [bit])) ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost, Compile.regBlocks_map_shiftReg]
    rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst,
        Compile.encodeRegs_append, Compile.encodeRegs_cons, Compile.shiftReg_append]
    simp [List.append_assoc]
  have htape : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post
      = Compile.encodeTape (s.set dst (s.get dst ++ [bit])) := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, htape0]
  refine ⟨{ state_idx := st',
            tapes := [([], hd',
              ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
                ++ (bit + 1) :: 0 :: post)] }, ?_, ?_, ?_⟩
  · rw [hinit, ← hk]; exact runFlatTM_extend hrun hhalt
  · exact hhalt
  · rw [show Compile.decodeTape
          { state_idx := st',
            tapes := [([], hd',
              ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
                ++ (bit + 1) :: 0 :: post)] }
        = Compile.decodeTape
          { state_idx := st',
            tapes := [([], hd',
              Compile.encodeTape (s.set dst (s.get dst ++ [bit])))] }
        from by rw [htape]]
    exact Compile.decodeTape_encodeTape' st' hd' _
      (Compile.BitState_appendBit bit hb s dst hbit hdst)

-- (The old `compileOp_appendOne_sound`/`_appendZero_sound` asserted the *exact-tape*,
-- non-rewinding contract about the bare `appendAtTM`. Since `compileOp` now dispatches
-- the append ops to the head-rewinding `opAppendBitRewind`, the live per-op contract is
-- the residue-tolerant `compileOp_sound_physical_residue` (append cases discharged by
-- `Compile.opAppendBit_physical_residue`). The single-phase `appendBit_sound` /
-- `appendBit_physical` remain as gadget-level lemmas about `appendAtTM`/`appendAtThenRewindTM`.)

/-- **Per-fragment physical contract for the append op (Risk C2, step 1b-2).**
The bracketed machine `appendAtThenRewindTM (bit+1) dst` run on `encodeTape s`
halts at the composite exit `3 + appendAtTM.states` with the **head rewound to
`0`** and the tape exactly `encodeTape (output)` — never halting earlier — in a
**linear** number of steps `≤ 3·(encodeTape s).length + 6`. This is the
`encodeTape`-level instance of `AppendGadget.appendAt_rewind_run`, and the form
`compileSeq_compose_physical` consumes when composing fragments (head `0` makes
the exit config equal `initFlatConfig` of the next fragment). The three rewind
side-conditions are discharged from the `encodeTape` structure. -/
theorem Compile.appendBit_physical (bit : Nat) (hb : bit ≤ 1)
    (s : State) (dst : Var) (hbit : Compile.BitState s) (hdst : dst < s.length) :
    ∃ t : Nat,
      runFlatTM t (AppendGadget.appendAtThenRewindTM (bit + 1) dst)
          (initFlatConfig (AppendGadget.appendAtThenRewindTM (bit + 1) dst)
            [Compile.encodeTape s])
        = some { state_idx := 3 + (AppendGadget.appendAtTM (bit + 1) dst).states,
                 tapes := [([], 0,
                   Compile.encodeTape (s.set dst (s.get dst ++ [bit])))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (AppendGadget.appendAtThenRewindTM (bit + 1) dst)
              (initFlatConfig (AppendGadget.appendAtThenRewindTM (bit + 1) dst)
                [Compile.encodeTape s]) = some ck →
          haltingStateReached (AppendGadget.appendAtThenRewindTM (bit + 1) dst) ck = false)
      ∧ t ≤ 3 * (Compile.encodeTape s).length + 6 := by
  have h_ins : bit + 1 < 4 := by omega
  set post : List Nat := Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] with hpost
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskip
  set body : List Nat := Compile.shiftReg (s.get dst) with hbody
  have hget_mem : s.get dst ∈ s := by
    rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
  have hshift_lt : ∀ (r : List Nat), (∀ x ∈ r, x ≤ 1) → ∀ x ∈ Compile.shiftReg r, x < 4 := by
    intro r hr x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hr y hy; omega
  have hshift_ne : ∀ (r : List Nat), ∀ x ∈ Compile.shiftReg r, x ≠ 0 := by
    intro r x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; omega
  have hlen : skipped.length = dst := by
    rw [hskip, List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hdst)]
  have h_pre : ∀ x ∈ ([] : List Nat), x < 4 := by intro x hx; cases hx
  have h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    intro b hbm
    rw [hskip, List.mem_map] at hbm
    obtain ⟨r, hr, rfl⟩ := hbm
    exact ⟨hshift_ne r, hshift_lt r (fun x hx => hbit r (List.mem_of_mem_take hr) x hx)⟩
  have hbody_ne : ∀ x ∈ body, x ≠ 0 := by rw [hbody]; exact hshift_ne _
  have hbody_lt : ∀ x ∈ body, x < 4 := by
    rw [hbody]; exact hshift_lt _ (fun x hx => hbit _ hget_mem x hx)
  have hpost_lt : ∀ x ∈ post, x < 4 := by
    rw [hpost]; intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeRegs_lt_four _
        (fun b hbm y hy => hbit b (List.mem_of_mem_drop hbm) y hy) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide
  have key : ∃ (sk : List (List Nat)) (bd : List Nat),
      sk.length = dst ∧
      (∀ b ∈ sk, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) ∧
      (∀ x ∈ bd, x ≠ 0) ∧ (∀ x ∈ bd, x < 4) ∧
      AppendGadget.regBlocks sk ++ bd
        = Compile.endMark :: (AppendGadget.regBlocks skipped ++ body) := by
    cases hsk : skipped with
    | nil =>
        refine ⟨[], Compile.endMark :: body, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hlen, hsk]
        · intro b hb; cases hb
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_ne x h
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_lt x h
        · simp [AppendGadget.regBlocks_nil]
    | cons hd tl =>
        refine ⟨(Compile.endMark :: hd) :: tl, body, ?_, ?_, hbody_ne, hbody_lt, ?_⟩
        · rw [hsk] at hlen; simpa using hlen
        · intro b hb
          rcases List.mem_cons.mp hb with h | h
          · subst h
            refine ⟨?_, ?_⟩
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).1 x h0
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).2 x h0
          · exact h_skip b (by rw [hsk]; exact List.mem_cons_of_mem _ h)
        · simp [AppendGadget.regBlocks_cons]
  obtain ⟨sk, bd, hlen_sk, h_skip_sk, hbd_ne, hbd_lt, hsfold⟩ := key
  have hsplit0 : AppendGadget.regBlocks skipped ++ body ++ 0 :: post
      = Compile.encodeRegs s ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost]; exact Compile.encodeTape_split s dst hdst
  have hsplit : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post
      = Compile.encodeTape s := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, hsplit0]
  have htape0 : AppendGadget.regBlocks skipped ++ body ++ (bit + 1) :: 0 :: post
      = Compile.encodeRegs (s.set dst (s.get dst ++ [bit])) ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost, Compile.regBlocks_map_shiftReg]
    rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst,
        Compile.encodeRegs_append, Compile.encodeRegs_cons, Compile.shiftReg_append]
    simp [List.append_assoc]
  have htape : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post
      = Compile.encodeTape (s.set dst (s.get dst ++ [bit])) := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, htape0]
  set output : State := s.set dst (s.get dst ++ [bit]) with houtput
  have hbit_out : Compile.BitState output :=
    Compile.BitState_appendBit bit hb s dst hbit hdst
  -- `htape : LT = encodeTape output`, where `LT` is the gadget's exit tape.
  -- Head/length relations (`HD = L`, `|encodeTape output| = HD + 1`).
  have hHD_L : ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
        + (0 :: post).length = (Compile.encodeTape s).length := by
    rw [← hsplit]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hEO_HD : (Compile.encodeTape output).length
      = ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
        + (0 :: post).length + 1 := by
    rw [← htape]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  -- `get`-equality across `htape` (no dependent rewrite: route through `getElem?`).
  have hget_eq : ∀ (i : Nat)
      (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post).length)
      (h' : i < (Compile.encodeTape output).length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post).get ⟨i, h⟩
        = (Compile.encodeTape output).get ⟨i, h'⟩ := by
    intro i h h'
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hopt := congrArg (fun l => l[i]?) htape
    simp only at hopt
    rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem h'] at hopt
    exact Option.some.inj hopt
  -- The three rewind side-conditions, from the `encodeTape output` structure.
  have h_tp_lt : ∀ x ∈ ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
      ++ (bit + 1) :: 0 :: post, x < 4 := by
    intro x hx; rw [htape] at hx; exact Compile.encodeTape_lt_four output hbit_out x hx
  have h_t0 : ∀ (h : 0 < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post).length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post).get ⟨0, h⟩
        = 3 := by
    intro h
    have h' : 0 < (Compile.encodeTape output).length := by rw [← htape]; exact h
    rw [hget_eq 0 h h']; exact Compile.encodeTape_get_zero output h'
  have h_interior_ne : ∀ i, 0 < i →
      i < ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
        + (0 :: post).length →
      ∃ (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
          ++ (bit + 1) :: 0 :: post).length),
        (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post).get ⟨i, h⟩
          ≠ 3 := by
    intro i hi hilt
    have hi1 : i + 1 < (Compile.encodeTape output).length := by rw [hEO_HD]; omega
    obtain ⟨hEO, hne⟩ := Compile.encodeTape_interior_ne_endMark output hbit_out i hi hi1
    have hlt : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post).length := by rw [htape]; exact hEO
    exact ⟨hlt, by rw [hget_eq i hlt hEO]; exact hne⟩
  -- The bracketed run and trajectory (over the *folded* blocks `sk`/`bd`).
  have hrun := AppendGadget.appendAt_rewind_run (bit + 1) h_ins dst [] sk bd post
    hlen_sk h_pre h_skip_sk hbd_ne hbd_lt hpost_lt h_tp_lt h_t0 h_interior_ne
  have htraj := AppendGadget.appendAt_rewind_no_early_halt (bit + 1) h_ins dst [] sk bd post
    hlen_sk h_pre h_skip_sk hbd_ne hbd_lt hpost_lt h_tp_lt h_t0 h_interior_ne
  -- Rewrite the gadget's count (`HD → L`), start tape (`→ encodeTape s`) and exit
  -- tape (`→ encodeTape output`) into the contract's canonical form.
  rw [hHD_L, hsplit, htape] at hrun
  rw [hHD_L, hsplit] at htraj
  -- The start config = initFlatConfig on `encodeTape s`.
  have hstart0 : (AppendGadget.appendAtThenRewindTM (bit + 1) dst).start = 0 := by
    show (composeFlatTM (AppendGadget.appendAtTM (bit + 1) dst) _ _).start = 0
    rw [composeFlatTM_start, AppendGadget.appendAtTM_start]
  have hinit : initFlatConfig (AppendGadget.appendAtThenRewindTM (bit + 1) dst)
        [Compile.encodeTape s]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s)] } := by
    simp only [initFlatConfig, hstart0, List.map_cons, List.map_nil]
  refine ⟨AppendGadget.appendAt_steps sk bd post + 1
      + (1 + 1 + (Compile.encodeTape s).length), ?_, ?_, ?_⟩
  · rw [hinit]; exact hrun.1
  · intro k hk ck hck
    rw [hinit] at hck
    exact htraj k hk ck hck
  · -- budget: appendAt_steps + 1 + (1 + 1 + L) ≤ 3·L + 6, via `appendAt_steps_le`.
    have hstep_le : AppendGadget.appendAt_steps sk bd post
        ≤ 2 * (Compile.encodeTape s).length + 3 := by
      have hb' := AppendGadget.appendAt_steps_le sk bd post
      have hL : (AppendGadget.regBlocks sk ++ bd ++ 0 :: post).length
          = (Compile.encodeTape s).length := by rw [← hsplit]; simp
      rw [hL] at hb'; exact hb'
    omega

/-! ### C2 validation: composition under the *physical* per-`Op` contract

The fixed-budget `decodeTape`-equality contract above cannot feed
`composeFlatTM_run` (it lacks the exact halt step, the no-early-halt
trajectory, and the head-`0` exit config). The lemma below is the decisive
check that the **physical** contract — each fragment halts at its `exit`
state with the head rewound to `0` and tape exactly `encodeTape (output)`,
reached at an explicit step `t` with a no-early-halt trajectory — composes
cleanly: with head `0`, `M₁`'s exit config *is* `initFlatConfig M₂ […]`, so
`M₂`'s contract plugs straight into `composeFlatTM_run`'s `h_run2`. It is
additive (the sorry'd `compileSeq_sound` above is left untouched pending the
file-wide contract restatement). See ROADMAP Risk C2. -/
theorem compileSeq_compose_physical
    (r1 r2 : CompiledCmd) (enc1 enc2 : List Nat) {t1 t2 : Nat} {cfg2 : FlatTMConfig}
    (h_sym2 : ∀ v, currentTapeSymbol (([] : List Nat), 0, enc2) = some v → v < 4)
    (h_run1 : runFlatTM t1 r1.M (initFlatConfig r1.M [enc1])
                = some { state_idx := r1.exit, tapes := [([], 0, enc2)] })
    (h_traj1 : ∀ k, k < t1 → ∀ ck,
        runFlatTM k r1.M (initFlatConfig r1.M [enc1]) = some ck →
        ck.state_idx ≠ r1.exit ∧ haltingStateReached r1.M ck = false)
    (h_run2 : runFlatTM t2 r2.M (initFlatConfig r2.M [enc2]) = some cfg2)
    (h_halt2 : haltingStateReached r2.M cfg2 = true) :
    runFlatTM (t1 + 1 + t2) (compileSeq r1 r2).M
        (initFlatConfig (compileSeq r1 r2).M [enc1])
      = some { state_idx := cfg2.state_idx + r1.M.states, tapes := cfg2.tapes } ∧
    haltingStateReached (compileSeq r1 r2).M
      { state_idx := cfg2.state_idx + r1.M.states, tapes := cfg2.tapes } = true := by
  have h_cfg0_state_lt :
      (initFlatConfig r1.M [enc1]).state_idx < r1.M.states := r1.M_valid.1
  have h_sym_bound :
      ∀ v, currentTapeSymbol (([] : List Nat), 0, enc2) = some v →
        v < max r1.M.sig r2.M.sig := by
    intro v hv
    rw [r1.M_sig, r2.M_sig]
    exact h_sym2 v hv
  exact composeFlatTM_run (M₁ := r1.M) (M₂ := r2.M) (exit := r1.exit)
    r1.M_valid r2.M_valid r1.exit_lt
    (initFlatConfig r1.M [enc1]) h_cfg0_state_lt
    [] 0 enc2 h_sym_bound h_run1 h_traj1 h_run2 h_halt2

/-! ### Physical-contract restated composition lemmas (Risk C2, step 1b-3)

The original `compileSeq_sound` / `compileIfBit_sound` / `compileForBnd_sound` /
`Compile_sound` are stated with the **quadratic** `Compile.overhead` per-fragment
budget — which is **unprovable** because quadratic budgets don't compose additively
(see the budget-shape finding above). The lemmas below restate every composition
combinator with the **physical** per-fragment contract: each sub-machine

  (1) halts at `exit` with head `0` and tape `= encodeTape output`,
  (2) has a no-early-halt trajectory,
  (3) satisfies a **linear** step budget `t ≤ A * tapeLen + B`.

Linear budgets compose: the composed machine runs in `t₁ + 1 + t₂` steps
(`compileSeq_compose_physical`), and bounding each `tᵢ` linearly in the tape
length at its entry gives a sum that telescopes into a quadratic total.

These restated lemmas are the **correct** decomposition for proving
`Compile_run_physical` by induction on `Cmd`. -/

/-- A residue block carries only **interior** symbols `{0, 1, 2}`: below the
alphabet bound (`< 4`) and free of the terminator `endMark = 3`. The left-shift
delete gadgets fill vacated cells with `0`; append carries interior symbols; so
the trailing residue on every physical tape stays `ValidResidue`. This is exactly
what the composition lemmas need to bound the inter-fragment tape symbols. -/
def Compile.ValidResidue (res : List Nat) : Prop :=
  ∀ x ∈ res, x < 4 ∧ x ≠ Compile.endMark

theorem Compile.ValidResidue_nil : Compile.ValidResidue [] := by
  intro x hx; simp at hx

theorem Compile.ValidResidue_append (a b : List Nat)
    (ha : Compile.ValidResidue a) (hb : Compile.ValidResidue b) :
    Compile.ValidResidue (a ++ b) := by
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with h | h
  · exact ha x h
  · exact hb x h

theorem Compile.ValidResidue_replicate_zero (n : Nat) :
    Compile.ValidResidue (List.replicate n 0) := by
  intro x hx
  rw [List.mem_replicate] at hx
  obtain ⟨_, rfl⟩ := hx
  exact ⟨by omega, by decide⟩

/-- The residue a length-decreasing op produces: the incoming residue with `n`
zero filler cells appended (the cells freed by a left-shift `deleteCarryTM`).
Stays `ValidResidue` — the convenience form of `ValidResidue_append` +
`ValidResidue_replicate_zero` that every deletion / shrinking-write op's residue
contract (`res_out = res_in ++ replicate n 0`) discharges with. -/
theorem Compile.ValidResidue_append_replicate_zero (res : List Nat) (n : Nat)
    (hres : Compile.ValidResidue res) :
    Compile.ValidResidue (res ++ List.replicate n 0) :=
  Compile.ValidResidue_append res _ hres (Compile.ValidResidue_replicate_zero n)

/-- **One deletion = the in-place `tail` step (the loop's inductive heart).**
Running `deleteCarryTM` from one past register `dst`'s content-start on
`encodeTape s ++ res` (register `dst` nonempty) deletes that register's first
content cell, yielding `encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0])`:
it drops one symbol from register `dst`, the incoming residue gaining one `0`
filler. Iterating this `|s.get dst|` times clears the register (the clear gadget's
loop body); a single application is the `tail`-in-place op. The content-start
position `p` and the shifted-suffix length `L` are existential (the caller's
navigation supplies the head position). Built from `deleteCarry_drop_head` +
`encodeTape_reg_decomp`. -/
theorem Compile.deleteCarry_tail_step (s : State) (dst : Var) (res : List Nat)
    (h : dst < s.length) (hbit : Compile.BitState s) (hne : s.get dst ≠ [])
    (hres : Compile.ValidResidue res) :
    ∃ p L : Nat,
      runFlatTM (3 * L + 1) Complexity.Lang.ShiftTape.deleteCarryTM
          { state_idx := 0, tapes := [([], p + 1, Compile.encodeTape s ++ res)] }
        = some { state_idx := 6,
                 tapes := [([], p + 1 + L,
                   Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))] } := by
  obtain ⟨pre, rest, hv, hs⟩ := Compile.encodeTape_reg_decomp s dst h
  obtain ⟨c0, cs, hcons⟩ : ∃ c0 cs, s.get dst = c0 :: cs := by
    cases hg : s.get dst with
    | nil => exact absurd hg hne
    | cons c0 cs => exact ⟨c0, cs, rfl⟩
  have hshift : Compile.shiftReg (c0 :: cs) = (c0 + 1) :: Compile.shiftReg cs := by
    simp [Compile.shiftReg]
  set M : List Nat := Compile.shiftReg cs ++ 0 :: rest ++ res with hMdef
  have htape : Compile.encodeTape s ++ res = pre ++ (c0 + 1) :: M := by
    rw [hs, hcons, hshift, hMdef]; simp [List.append_assoc]
  have hc0le : c0 ≤ 1 := by
    have hmem : s.get dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem c0 (by rw [hcons]; exact List.mem_cons_self ..)
  have hM : M ≠ [] := by
    rw [hMdef]; intro hc
    have := congrArg List.length hc; simp [List.append_assoc] at this
  have hMb : ∀ x ∈ M, x < 4 := by
    intro x hx
    have hxin : x ∈ Compile.encodeTape s ++ res := by
      rw [htape]; exact List.mem_append_right pre (List.mem_cons_of_mem _ hx)
    rw [List.mem_append] at hxin
    rcases hxin with hx' | hx'
    · exact Compile.encodeTape_lt_four s hbit x hx'
    · exact (hres x hx').1
  have hout : Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0])
      = pre ++ M ++ [0] := by
    rw [hcons]; show Compile.encodeTape (s.set dst cs) ++ (res ++ [0]) = _
    rw [hv cs, hMdef]; simp [List.append_assoc]
  refine ⟨pre.length, M.length, ?_⟩
  rw [htape, hout]
  exact Compile.deleteCarry_drop_head pre M c0 (by omega) hM hMb

/-- In-range, `State.set` is `List.set`. -/
theorem Compile.set_eq_list_set (s : State) (dst : Var) (w : List Nat) (h : dst < s.length) :
    s.set dst w = List.set s dst w := by rw [State.set, if_pos h]

/-- Reading back a just-written register (in range). (Local — `Frame`'s
`State.get_set_eq` is not imported here.) -/
theorem Compile.get_set_eq (s : State) (dst : Var) (v : List Nat) (h : dst < s.length) :
    (s.set dst v).get dst = v := by
  unfold State.get
  rw [Compile.set_eq_list_set s dst v h, List.getElem?_set_self h, Option.getD_some]

/-- Writing register `dst` to its current value is a no-op (in range). -/
theorem Compile.set_get_self (s : State) (dst : Var) (h : dst < s.length) :
    s.set dst (s.get dst) = s := by
  have hg : s.get dst = s[dst] := by rw [State.get, List.getElem?_eq_getElem h]; rfl
  rw [Compile.set_eq_list_set s dst _ h, hg]
  exact List.set_getElem_self h

/-- Two successive writes to the same register: the first is overwritten. -/
theorem Compile.set_set (s : State) (dst : Var) (a b : List Nat) (h : dst < s.length) :
    (s.set dst a).set dst b = s.set dst b := by
  have hla : dst < (s.set dst a).length := by
    rw [Compile.set_eq_list_set s dst a h, List.length_set]; exact h
  rw [Compile.set_eq_list_set (s.set dst a) dst b hla, Compile.set_eq_list_set s dst a h,
      List.set_set, Compile.set_eq_list_set s dst b h]

/-- Writing register `dst` (in range) preserves the register count. -/
theorem Compile.length_set (s : State) (dst : Var) (v : List Nat) (h : dst < s.length) :
    (s.set dst v).length = s.length := by
  rw [Compile.set_eq_list_set s dst v h, List.length_set]

/-- Reading a register other than the one just written (in range). (Local —
`Frame`'s `State.get_set_ne` is not imported here.) -/
theorem Compile.get_set_ne (s : State) (v : Var) (val : List Nat) (r : Var)
    (hv : v < s.length) (hr : r ≠ v) :
    (s.set v val).get r = s.get r := by
  unfold State.get
  rw [Compile.set_eq_list_set s v val hv, List.getElem?_set_ne hr.symm]

/-- Writes to distinct in-range registers commute. (Local — `Frame` not imported.) -/
theorem Compile.set_comm (s : State) (a b : Var) (u w : List Nat)
    (ha : a < s.length) (hb : b < s.length) (hab : a ≠ b) :
    (s.set a u).set b w = (s.set b w).set a u := by
  have hbla : b < (s.set a u).length := by rw [Compile.length_set s a u ha]; exact hb
  have halb : a < (s.set b w).length := by rw [Compile.length_set s b w hb]; exact ha
  rw [Compile.set_eq_list_set (s.set a u) b w hbla, Compile.set_eq_list_set s a u ha,
      Compile.set_eq_list_set (s.set b w) a u halb, Compile.set_eq_list_set s b w hb,
      List.set_comm u w hab]

/-- `BitState` is preserved by writing a `≤ 1`-valued register. The general form
of `BitState_set_tail` (used by the `clear` loop, where the register is a `drop`
of the original bit-shaped content). -/
theorem Compile.BitState_set (s : State) (dst : Var) (v : List Nat)
    (h : Compile.BitState s) (hdst : dst < s.length) (hv : ∀ x ∈ v, x ≤ 1) :
    Compile.BitState (s.set dst v) := by
  rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst]
  intro reg hreg x hx
  simp only [List.mem_append, List.mem_cons] at hreg
  rcases hreg with hr | hr | hr
  · exact h reg (List.mem_of_mem_take hr) x hx
  · subst hr; exact hv x hx
  · exact h reg (List.mem_of_mem_drop hr) x hx

/-- **Padding-tolerant `BitState_set`.** `BitState` is preserved by writing a
`≤ 1`-valued register to *any* index — including one past the current length,
where `State.set` pads with empty (hence bit-safe) registers. This is the
unconditional form the `forBnd` counter-write (`set counter (replicate i 1)`,
where `counter` may exceed the live register count) and the residue-tolerant
`Cmd` induction need; `BitState_set` requires `dst < s.length`. -/
theorem Compile.BitState_set_pad (s : State) (dst : Var) (v : List Nat)
    (h : Compile.BitState s) (hv : ∀ x ∈ v, x ≤ 1) :
    Compile.BitState (s.set dst v) := by
  by_cases hd : dst < s.length
  · exact Compile.BitState_set s dst v h hd hv
  · rw [State.set, if_neg hd]
    have hpad : Compile.BitState (s ++ List.replicate (dst + 1 - s.length) ([] : List Nat)) := by
      intro reg hreg x hx
      rw [List.mem_append] at hreg
      rcases hreg with hr | hr
      · exact h reg hr x hx
      · rw [List.mem_replicate] at hr; rw [hr.2] at hx; simp at hx
    have hlen : dst < (s ++ List.replicate (dst + 1 - s.length) ([] : List Nat)).length := by
      rw [List.length_append, List.length_replicate]
      have hle : s.length ≤ dst + 1 := Nat.le_succ_of_le (Nat.le_of_not_lt hd)
      rw [Nat.add_sub_cancel' hle]
      exact Nat.lt_succ_self dst
    rw [Compile.list_set_eq_take_cons_drop _ dst v hlen]
    intro reg hreg x hx
    simp only [List.mem_append, List.mem_cons] at hreg
    rcases hreg with hr | hr | hr
    · exact hpad reg (List.mem_of_mem_take hr) x hx
    · subst hr; exact hv x hx
    · exact hpad reg (List.mem_of_mem_drop hr) x hx

/-- **State-level invariant of the `clear` loop.** Iterating the in-place `tail`
body `t ↦ t.set dst t.tail` `n` times drops the first `n` symbols of register
`dst`: `(·.set dst ·.tail)^[n] s = s.set dst ((s.get dst).drop n)`. At
`n = |s.get dst|` (`drop` empties the register) this is `clear`. Combined with the
tape-level `deleteCarry_tail_step`, this is the loop's correctness content. -/
theorem Compile.set_tail_iterate (s : State) (dst : Var) (h : dst < s.length) :
    ∀ n, (fun t : State => t.set dst (t.get dst).tail)^[n] s
        = s.set dst ((s.get dst).drop n) := by
  intro n
  induction n with
  | zero => rw [Function.iterate_zero, id_eq, List.drop_zero, Compile.set_get_self s dst h]
  | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih,
          Compile.get_set_eq s dst _ h, Compile.set_set s dst _ _ h, List.tail_drop]

/-- **`clear` = iterating the `tail` body exactly `|s.get dst|` times.** The loop
count the clear gadget's `loopTM` runs: dropping every symbol of register `dst`
empties it (`Op.eval (clear dst) s = s.set dst []`). -/
theorem Compile.iterate_tail_clear (s : State) (dst : Var) (h : dst < s.length) :
    (fun t : State => t.set dst (t.get dst).tail)^[(s.get dst).length] s
      = Op.eval (Op.clear dst) s := by
  rw [Compile.set_tail_iterate s dst h, List.drop_length]; rfl

/-! ### `clear` run lemma — reusable building blocks (Risk C2, step 3)

The delete branch of `clearRegionTM`'s loop body deletes register `dst`'s first
content cell (`deleteCarryTM`), then rewinds the head to `0`. After
`deleteCarryTM` the head sits one cell *past* the tape end, so the rewind is
`stepLeftTM ⨾ rewindTwoPhaseTM` on the post-deletion tape, which has the shape
`encodeTape output ++ ValidResidue`. The helper below packages the two-phase
rewind for any such tape. -/

/-- **Two-phase rewind on `encodeTape output ++ residue`.** From the head one cell
*before* the end (where `stepLeftTM` lands after `deleteCarryTM`), the two-phase
rewind scans left to the trailing terminator, steps off it, and scans to the
leading sentinel at index `0`. Reaches `rewindTwoPhaseTM`'s "found" halt (state
`6`) with the head at `0` and the tape unchanged. -/
theorem Compile.encodeTape_residue_twoPhaseRewind (output : State) (residue : List Nat)
    (hbit : Compile.BitState output) (hres : Compile.ValidResidue residue) :
    ∃ steps, runFlatTM steps (ScanLeft.rewindTwoPhaseTM 4 3)
        { state_idx := 0,
          tapes := [([], (Compile.encodeTape output ++ residue).length - 1,
                     Compile.encodeTape output ++ residue)] }
      = some { state_idx := 6,
               tapes := [([], 0, Compile.encodeTape output ++ residue)] }
      ∧ (∀ k, k < steps → ∀ ck,
          runFlatTM k (ScanLeft.rewindTwoPhaseTM 4 3)
              { state_idx := 0,
                tapes := [([], (Compile.encodeTape output ++ residue).length - 1,
                           Compile.encodeTape output ++ residue)] } = some ck →
          haltingStateReached (ScanLeft.rewindTwoPhaseTM 4 3) ck = false)
      ∧ steps ≤ (Compile.encodeTape output ++ residue).length + 3 := by
  set tp := Compile.encodeTape output ++ residue with htp
  have hEO2 : 2 ≤ (Compile.encodeTape output).length := by rw [Compile.encodeTape_length]; omega
  have hEOle : (Compile.encodeTape output).length ≤ tp.length := by
    rw [htp, List.length_append]; omega
  have htp_pos : 0 < tp.length := by omega
  -- getElem transfers (proof-free via getElem?).
  have hleft : ∀ i (hi : i < (Compile.encodeTape output).length) (htpi : i < tp.length),
      tp.get ⟨i, htpi⟩ = (Compile.encodeTape output).get ⟨i, hi⟩ := by
    intro i hi htpi
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc : tp[i]? = (Compile.encodeTape output)[i]? := by
      rw [htp, List.getElem?_append_left hi]
    rw [List.getElem?_eq_getElem htpi, List.getElem?_eq_getElem hi] at hc
    exact Option.some.inj hc
  have hright : ∀ i (htpi : i < tp.length) (hge : (Compile.encodeTape output).length ≤ i)
      (hir : i - (Compile.encodeTape output).length < residue.length),
      tp.get ⟨i, htpi⟩ = residue.get ⟨i - (Compile.encodeTape output).length, hir⟩ := by
    intro i htpi hge hir
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc : tp[i]? = residue[i - (Compile.encodeTape output).length]? := by
      rw [htp, List.getElem?_append_right hge]
    rw [List.getElem?_eq_getElem htpi, List.getElem?_eq_getElem hir] at hc
    exact Option.some.inj hc
  -- side conditions, shared by the run and the trajectory.
  have h_sent : tp.get ⟨0, htp_pos⟩ = 3 := by
    rw [hleft 0 (by omega) htp_pos]; exact Compile.encodeTape_get_zero output (by omega)
  have hp_lt : (Compile.encodeTape output).length - 1 < tp.length := by omega
  have h_term : tp.get ⟨(Compile.encodeTape output).length - 1, hp_lt⟩ = 3 := by
    rw [hleft ((Compile.encodeTape output).length - 1) (by omega) hp_lt]
    exact Compile.encodeTape_get_last output (by omega)
  have h_int : ∀ i, 0 < i → i < (Compile.encodeTape output).length - 1 →
      ∃ (h : i < tp.length), tp.get ⟨i, h⟩ < 4 ∧ tp.get ⟨i, h⟩ ≠ 3 := by
    intro i hi0 hip
    have hiEO : i + 1 < (Compile.encodeTape output).length := by omega
    obtain ⟨hi_lt, hne⟩ := Compile.encodeTape_interior_ne_endMark output hbit i hi0 hiEO
    have hitp : i < tp.length := by omega
    refine ⟨hitp, ?_, ?_⟩
    · rw [hleft i hi_lt hitp]; exact Compile.encodeTape_lt_four output hbit _ (List.get_mem _ _)
    · rw [hleft i hi_lt hitp]; exact hne
  have h_res : ∀ i, (Compile.encodeTape output).length - 1 < i → i ≤ tp.length - 1 →
      ∃ (h : i < tp.length), tp.get ⟨i, h⟩ < 4 ∧ tp.get ⟨i, h⟩ ≠ 3 := by
    intro i hpi hih
    have hge : (Compile.encodeTape output).length ≤ i := by omega
    have hitp : i < tp.length := by omega
    have hir : i - (Compile.encodeTape output).length < residue.length := by
      rw [htp, List.length_append] at hitp; omega
    refine ⟨hitp, ?_, ?_⟩
    · rw [hright i hitp hge hir]; exact (hres _ (List.get_mem _ _)).1
    · rw [hright i hitp hge hir]; exact (hres _ (List.get_mem _ _)).2
  have hrun := ScanLeft.rewindTwoPhase_run 4 3 (by decide) [] tp
    ((Compile.encodeTape output).length - 1) (tp.length - 1)
    htp_pos h_sent hp_lt h_term (by omega) (by omega) (by omega) h_int h_res
  have htraj := ScanLeft.rewindTwoPhase_no_early_halt 4 3 (by decide) [] tp
    ((Compile.encodeTape output).length - 1) (tp.length - 1)
    htp_pos h_sent hp_lt h_term (by omega) (by omega) (by omega) h_int h_res
  -- the step count `(head−p+1)+1+(1+1+p)` with `head = tp.length−1`, `p = E−1`
  -- equals exactly `tp.length + 3`; bound it with `omega` (`2 ≤ E ≤ tp.length`).
  refine ⟨_, hrun, htraj, ?_⟩
  omega

/-- **Explicit register decomposition of `encodeTape`** (the existential `pre`/
`rest` of `encodeTape_reg_decomp` made concrete). `pre = endMark :: encodeRegs
(s.take dst)` and `rest = encodeRegs (s.drop (dst+1)) ++ [endMark]`, so the
literal-`3` navigation lemmas (`pre = 3 :: regBlocks ((s.take dst).map shiftReg)`,
via `regBlocks_map_shiftReg`) and the `deleteCarryTM` decomposition both apply. -/
theorem Compile.encodeTape_reg_decomp_at (s : State) (dst : Var) (h : dst < s.length) :
    (∀ v : List Nat, Compile.encodeTape (s.set dst v)
        = (Compile.endMark :: Compile.encodeRegs (s.take dst))
            ++ (Compile.shiftReg v
                ++ (0 :: (Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark])))) ∧
      Compile.encodeTape s
        = (Compile.endMark :: Compile.encodeRegs (s.take dst))
            ++ (Compile.shiftReg (s.get dst)
                ++ (0 :: (Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark]))) := by
  refine ⟨?_, ?_⟩
  · intro v
    have hset : s.set dst v = s.take dst ++ v :: s.drop (dst + 1) := by
      rw [State.set, if_pos h]; exact Compile.list_set_eq_take_cons_drop s dst v h
    have hs : Compile.encodeRegs (s.set dst v)
        = Compile.encodeRegs (s.take dst)
            ++ (Compile.shiftReg v ++ ([0] ++ Compile.encodeRegs (s.drop (dst + 1)))) := by
      rw [hset, Compile.encodeRegs_append, Compile.encodeRegs_cons]; simp [List.append_assoc]
    rw [Compile.encodeTape, hs]; simp [List.append_assoc]
  · have hget : s.get dst = s[dst] := by rw [State.get, List.getElem?_eq_getElem h]; rfl
    have hs : Compile.encodeRegs s
        = Compile.encodeRegs (s.take dst)
            ++ (Compile.shiftReg (s.get dst)
                ++ ([0] ++ Compile.encodeRegs (s.drop (dst + 1)))) := by
      conv_lhs => rw [Compile.list_eq_take_getElem_drop s dst h]
      rw [Compile.encodeRegs_append, Compile.encodeRegs_cons, ← hget]; simp [List.append_assoc]
    rw [Compile.encodeTape, hs]; simp [List.append_assoc]

/-- `BitState` is preserved by clearing register `dst`'s first cell. -/
theorem Compile.BitState_set_tail (s : State) (dst : Var)
    (h : Compile.BitState s) (hdst : dst < s.length) :
    Compile.BitState (s.set dst (s.get dst).tail) := by
  rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst]
  intro reg hreg x hx
  simp only [List.mem_append, List.mem_cons] at hreg
  rcases hreg with hr | hr | hr
  · exact h reg (List.mem_of_mem_take hr) x hx
  · subst hr
    have hmem : s.get dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
    exact h _ hmem x (List.mem_of_mem_tail hx)
  · exact h reg (List.mem_of_mem_drop hr) x hx

/-- `haltingStateReached` from a `halt[i]? = some true` fact. -/
theorem Compile.haltingStateReached_of_halt {M : FlatTM} {i : Nat} {tapes}
    (hi : M.halt[i]? = some true) :
    haltingStateReached M { state_idx := i, tapes := tapes } = true := by
  show M.halt.getD i false = true
  rw [List.getD_eq_getElem?_getD, hi]; rfl

/-- **Delete-branch core (Risk C2, step 3): `stepDeleteRewindRawTM` run.** From
register `dst`'s content start (head `1 + |encodeRegs (s.take dst)|`) on
`encodeTape s ++ res` (register `dst` nonempty), step right, delete the first
content cell (`deleteCarryTM`), step left off the past-the-end blank, and
two-phase rewind to head `0`. Lands at `stepDeleteRewindTM_exit = 17` with the
tape `encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0])`. -/
theorem Compile.stepDeleteRewind_run (s : State) (dst : Var) (res : List Nat)
    (h : dst < s.length) (hbit : Compile.BitState s) (hne : s.get dst ≠ [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t ClearGadget.stepDeleteRewindRawTM
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (s.take dst)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.stepDeleteRewindTM_exit,
               tapes := [([], 0,
                 Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k ClearGadget.stepDeleteRewindRawTM
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (s.take dst)).length,
                           Compile.encodeTape s ++ res)] } = some ck →
          haltingStateReached ClearGadget.stepDeleteRewindRawTM ck = false)
      ∧ t ≤ 4 * (Compile.encodeTape s ++ res).length + 9 := by
  obtain ⟨c0, cs, hcons⟩ : ∃ c0 cs, s.get dst = c0 :: cs := by
    cases hg : s.get dst with
    | nil => exact absurd hg hne
    | cons c0 cs => exact ⟨c0, cs, rfl⟩
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s dst h
  have hc0le : c0 ≤ 1 := by
    have hmem : s.get dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem c0 (by rw [hcons]; exact List.mem_cons_self ..)
  have hbit_out : Compile.BitState (s.set dst cs) := by
    have := Compile.BitState_set_tail s dst hbit h; rwa [hcons] at this
  have hres0 : Compile.ValidResidue (res ++ [0]) := by
    apply Compile.ValidResidue_append _ _ hres; intro x hx
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  set pre : List Nat := Compile.endMark :: Compile.encodeRegs (s.take dst) with hpredef
  set rest : List Nat := Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] with hrestdef
  set midSuf : List Nat := Compile.shiftReg cs ++ 0 :: (rest ++ res) with hmidSufdef
  have hpre_len : pre.length = 1 + (Compile.encodeRegs (s.take dst)).length := by
    rw [hpredef]; simp [Nat.add_comm]
  set Tout : List Nat := Compile.encodeTape (s.set dst cs) ++ (res ++ [0]) with hToutdef
  have hshift : Compile.shiftReg (c0 :: cs) = (c0 + 1) :: Compile.shiftReg cs := by
    simp [Compile.shiftReg]
  -- input/output tape decompositions.
  have htape_in : Compile.encodeTape s ++ res = pre ++ (c0 + 1) :: midSuf := by
    rw [hs, hcons, hshift, hmidSufdef]; simp [List.append_assoc]
  have htape_out : pre ++ midSuf ++ [0] = Tout := by
    rw [hToutdef, hv cs, hmidSufdef]; simp [List.append_assoc]
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have hmid4 : ∀ x ∈ midSuf, x < 4 := by
    intro x hx; exact htape4 x (by rw [htape_in]; exact List.mem_append_right pre (List.mem_cons_of_mem _ hx))
  have hmid_ne : midSuf ≠ [] := by rw [hmidSufdef]; simp
  obtain ⟨tt, suf, hts⟩ := List.exists_cons_of_ne_nil hmid_ne
  have hmidlen : 1 ≤ midSuf.length := by rw [hts]; simp
  have htt4 : tt < 4 := hmid4 tt (by rw [hts]; exact List.mem_cons_self ..)
  have hsuf4 : ∀ x ∈ suf, x < 4 := fun x hx => hmid4 x (by rw [hts]; exact List.mem_cons_of_mem tt hx)
  -- length facts.
  have hTout_len : Tout.length = pre.length + midSuf.length + 1 := by
    rw [← htape_out]; simp [List.length_append]; omega
  have hhead_eq : pre.length + 1 + (tt :: suf).length = Tout.length := by
    rw [← hts, hTout_len]; omega
  have hTout4 : ∀ x ∈ Tout, x < 4 := by
    intro x hx; rw [hToutdef, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four (s.set dst cs) hbit_out x hx
    · exact (hres0 x hx).1
  have htape_eq : pre ++ (c0 + 1) :: tt :: suf = Compile.encodeTape s ++ res := by
    rw [htape_in, hts]
  -- (1) inner rewind: stepLeft (blank) ⨾ rewindTwoPhase, on Tout, head Tout.length → 0.
  obtain ⟨t_rw, h_rw, h_rw_traj, h_rw_bnd⟩ :=
    Compile.encodeTape_residue_twoPhaseRewind (s.set dst cs) (res ++ [0]) hbit_out hres0
  rw [← hToutdef] at h_rw h_rw_traj h_rw_bnd
  -- length bridge: the output tape `Tout` has the same length as the input
  -- (`encodeTape s ++ res`), and `(tt :: suf).length` is bounded by it.
  have hLinTout : (Compile.encodeTape s ++ res).length = Tout.length := by
    rw [htape_in, hTout_len]
    simp [List.length_append, List.length_cons, Nat.add_assoc]
  have hsuf_le : (tt :: suf).length ≤ (Compile.encodeTape s ++ res).length := by
    rw [hLinTout, ← hhead_eq]; omega
  have h_innerRewind :
      runFlatTM (1 + 1 + t_rw)
        (composeFlatTM (ScanLeft.stepLeftTM 4) (ScanLeft.rewindTwoPhaseTM 4 3) 1)
        { state_idx := 0, tapes := [([], Tout.length, Tout)] }
      = some { state_idx := 8, tapes := [([], 0, Tout)] } := by
    have hcomp := composeFlatTM_run (ScanLeft.stepLeftTM_valid 4)
      (ScanLeft.rewindTwoPhaseTM_valid 4 3 (by decide)) (show (1 : Nat) < 2 by decide)
      { state_idx := 0, tapes := [([], Tout.length, Tout)] }
      (by show (0 : Nat) < (ScanLeft.stepLeftTM 4).states; decide)
      [] (Tout.length - 1) Tout
      (by intro w hw
          have hr : Tout.length - 1 < Tout.length := by omega
          rw [currentTapeSymbol_in_range hr] at hw
          injection hw with hw'
          rw [show max (ScanLeft.stepLeftTM 4).sig (ScanLeft.rewindTwoPhaseTM 4 3).sig = 4 from rfl,
              ← hw', List.get_eq_getElem]
          exact hTout4 _ (List.getElem_mem hr))
      (ScanLeft.stepLeftTM_run_blank 4 [] Tout Tout.length (Nat.le_refl _))
      (ScanLeft.stepLeftTM_no_early_halt 4 [] Tout Tout.length)
      (by rw [ScanLeft.rewindTwoPhaseTM_start]; exact h_rw)
      (Compile.haltingStateReached_of_halt (ScanLeft.rewindTwoPhaseTM_halt_six 4 3))
    exact hcomp.1
  have h_innerRewind_traj :
      ∀ k, k < (1 + 1 + t_rw) → ∀ ck,
        runFlatTM k (composeFlatTM (ScanLeft.stepLeftTM 4) (ScanLeft.rewindTwoPhaseTM 4 3) 1)
            { state_idx := 0, tapes := [([], Tout.length, Tout)] } = some ck →
        haltingStateReached
          (composeFlatTM (ScanLeft.stepLeftTM 4) (ScanLeft.rewindTwoPhaseTM 4 3) 1) ck = false := by
    apply composeFlatTM_no_early_halt (ScanLeft.stepLeftTM_valid 4)
      (ScanLeft.rewindTwoPhaseTM_valid 4 3 (by decide)) (show (1 : Nat) < 2 by decide)
      { state_idx := 0, tapes := [([], Tout.length, Tout)] }
      (by show (0 : Nat) < (ScanLeft.stepLeftTM 4).states; decide)
      [] (Tout.length - 1) Tout
      (by intro w hw
          have hr : Tout.length - 1 < Tout.length := by omega
          rw [currentTapeSymbol_in_range hr] at hw
          injection hw with hw'
          rw [show max (ScanLeft.stepLeftTM 4).sig (ScanLeft.rewindTwoPhaseTM 4 3).sig = 4 from rfl,
              ← hw', List.get_eq_getElem]
          exact hTout4 _ (List.getElem_mem hr))
      (ScanLeft.stepLeftTM_run_blank 4 [] Tout Tout.length (Nat.le_refl _))
      (ScanLeft.stepLeftTM_no_early_halt 4 [] Tout Tout.length)
      (by rw [ScanLeft.rewindTwoPhaseTM_start]; exact h_rw_traj)
  -- (2) deleteCarry ⨾ inner rewind = deleteRewindRawTM.
  have h_deleteCarry : runFlatTM (3 * (tt :: suf).length + 1) ShiftTape.deleteCarryTM
      { state_idx := 0, tapes := [([], pre.length + 1, Compile.encodeTape s ++ res)] }
      = some { state_idx := 6, tapes := [([], Tout.length, Tout)] } := by
    have hd := ShiftTape.deleteCarryTM_run pre (c0 + 1) tt suf (by omega) htt4 hsuf4
    rw [htape_eq, hhead_eq, show pre ++ tt :: suf ++ [0] = Tout by rw [← hts]; exact htape_out] at hd
    exact hd
  have h_deleteRewind :
      runFlatTM ((3 * (tt :: suf).length + 1) + 1 + (1 + 1 + t_rw)) ClearGadget.deleteRewindRawTM
        { state_idx := 0, tapes := [([], pre.length + 1, Compile.encodeTape s ++ res)] }
      = some { state_idx := 15, tapes := [([], 0, Tout)] } := by
    have hcomp := composeFlatTM_run ShiftTape.deleteCarryTM_valid
      ClearGadget.innerRewind_valid (show (6 : Nat) < 7 by decide)
      { state_idx := 0, tapes := [([], pre.length + 1, Compile.encodeTape s ++ res)] }
      (by show (0 : Nat) < ShiftTape.deleteCarryTM.states; decide)
      [] Tout.length Tout
      (by intro w hw
          rw [currentTapeSymbol_out_of_range (by omega)] at hw; exact absurd hw (by simp))
      h_deleteCarry
      (by intro k hk ck hck
          have hh := ShiftTape.deleteCarryTM_no_early_halt pre (c0 + 1) tt suf (by omega) htt4 hsuf4
            k hk ck (by rw [htape_eq]; exact hck)
          exact ⟨ClearGadget.ne_of_not_halting (show ShiftTape.deleteCarryTM.halt[6]? = some true from rfl) hh, hh⟩)
      h_innerRewind
      (Compile.haltingStateReached_of_halt ClearGadget.innerRewind_halt_eight)
    exact hcomp.1
  have h_deleteRewind_traj :
      ∀ k, k < ((3 * (tt :: suf).length + 1) + 1 + (1 + 1 + t_rw)) → ∀ ck,
        runFlatTM k ClearGadget.deleteRewindRawTM
            { state_idx := 0, tapes := [([], pre.length + 1, Compile.encodeTape s ++ res)] }
          = some ck →
        haltingStateReached ClearGadget.deleteRewindRawTM ck = false := by
    apply composeFlatTM_no_early_halt ShiftTape.deleteCarryTM_valid
      ClearGadget.innerRewind_valid (show (6 : Nat) < 7 by decide)
      { state_idx := 0, tapes := [([], pre.length + 1, Compile.encodeTape s ++ res)] }
      (by show (0 : Nat) < ShiftTape.deleteCarryTM.states; decide)
      [] Tout.length Tout
      (by intro w hw
          rw [currentTapeSymbol_out_of_range (by omega)] at hw; exact absurd hw (by simp))
      h_deleteCarry
      (by intro k hk ck hck
          have hh := ShiftTape.deleteCarryTM_no_early_halt pre (c0 + 1) tt suf (by omega) htt4 hsuf4
            k hk ck (by rw [htape_eq]; exact hck)
          exact ⟨ClearGadget.ne_of_not_halting (show ShiftTape.deleteCarryTM.halt[6]? = some true from rfl) hh, hh⟩)
      h_innerRewind_traj
  -- (3) stepRight ⨾ deleteRewindRawTM = stepDeleteRewindRawTM.
  have hcell : (Compile.encodeTape s ++ res).get
      ⟨pre.length, by rw [htape_in]; simp [List.length_append]⟩ = c0 + 1 := by
    have hlt : pre.length < (Compile.encodeTape s ++ res).length := by
      rw [htape_in]; simp [List.length_append]
    have hc? : (Compile.encodeTape s ++ res)[pre.length]? = some (c0 + 1) := by
      rw [htape_in, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
    rw [List.get_eq_getElem, List.getElem?_eq_getElem hlt] at *
    exact Option.some.inj hc?
  have hr1 : pre.length < (Compile.encodeTape s ++ res).length := by
    rw [htape_in]; simp [List.length_append]
  have hr2 : pre.length + 1 < (Compile.encodeTape s ++ res).length := by
    rw [htape_in]; simp [List.length_append]; omega
  refine ⟨(1 : Nat) + 1 + ((3 * (tt :: suf).length + 1) + 1 + (1 + 1 + t_rw)), ?_, ?_, ?_⟩
  · rw [show ClearGadget.stepDeleteRewindRawTM
          = composeFlatTM (ScanLeft.stepRightTM 4) ClearGadget.deleteRewindRawTM 1 from rfl,
        ← hpre_len, hcons]
    exact (composeFlatTM_run (ScanLeft.stepRightTM_valid 4)
      ClearGadget.deleteRewindRawTM_valid (show (1 : Nat) < 2 by decide)
      { state_idx := 0, tapes := [([], pre.length, Compile.encodeTape s ++ res)] }
      (by show (0 : Nat) < (ScanLeft.stepRightTM 4).states; decide)
      [] (pre.length + 1) (Compile.encodeTape s ++ res)
      (fun w hw => by
          rw [currentTapeSymbol_in_range hr2, List.get_eq_getElem] at hw
          rw [show max (ScanLeft.stepRightTM 4).sig ClearGadget.deleteRewindRawTM.sig = 4 from rfl,
              (Option.some.inj hw).symm]
          exact htape4 _ (List.getElem_mem hr2))
      (ScanLeft.stepRightTM_run 4 [] (Compile.encodeTape s ++ res) pre.length hr1
        (by rw [hcell]; omega))
      (ScanLeft.stepRightTM_no_early_halt 4 [] (Compile.encodeTape s ++ res) pre.length)
      h_deleteRewind
      (Compile.haltingStateReached_of_halt ClearGadget.deleteRewindRawTM_halt_fifteen)).1
  · rw [show ClearGadget.stepDeleteRewindRawTM
          = composeFlatTM (ScanLeft.stepRightTM 4) ClearGadget.deleteRewindRawTM 1 from rfl,
        ← hpre_len]
    exact composeFlatTM_no_early_halt (ScanLeft.stepRightTM_valid 4)
      ClearGadget.deleteRewindRawTM_valid (show (1 : Nat) < 2 by decide)
      { state_idx := 0, tapes := [([], pre.length, Compile.encodeTape s ++ res)] }
      (by show (0 : Nat) < (ScanLeft.stepRightTM 4).states; decide)
      [] (pre.length + 1) (Compile.encodeTape s ++ res)
      (fun w hw => by
          rw [currentTapeSymbol_in_range hr2, List.get_eq_getElem] at hw
          rw [show max (ScanLeft.stepRightTM 4).sig ClearGadget.deleteRewindRawTM.sig = 4 from rfl,
              (Option.some.inj hw).symm]
          exact htape4 _ (List.getElem_mem hr2))
      (ScanLeft.stepRightTM_run 4 [] (Compile.encodeTape s ++ res) pre.length hr1
        (by rw [hcell]; omega))
      (ScanLeft.stepRightTM_no_early_halt 4 [] (Compile.encodeTape s ++ res) pre.length)
      h_deleteRewind_traj
  · -- budget: `3·M + t_rw + 6 ≤ 4·Tout.length + 9 = 4·Lin + 9` (`M ≤ Tout`, `t_rw ≤ Tout+3`).
    rw [hLinTout]
    have hd : (tt :: suf).length ≤ Tout.length := by omega
    omega

/-- **Clear loop body — delete branch (Risk C2, step 3).** When register `dst` is
nonempty, the loop body `clearBodyRawTM dst` navigates to it, tests its content
start (nonzero → content branch), deletes the first cell and rewinds, landing at
`clearBodyRawTM_exitLoop dst` with the tape `encodeTape (s.set dst (s.get
dst).tail) ++ (res ++ [0])` and head `0`. Built by `branchComposeFlatTM_run_pos`
over `navigateAndTestTM_run_content` (step 2) and `stepDeleteRewind_run`. -/
theorem Compile.clearBody_delete_run (s : State) (dst : Var) (res : List Nat)
    (h : dst < s.length) (hbit : Compile.BitState s) (hne : s.get dst ≠ [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (ClearGadget.clearBodyRawTM dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.clearBodyRawTM_exitLoop dst,
               tapes := [([], 0,
                 Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (ClearGadget.clearBodyRawTM dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitDone dst ∧
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitLoop dst ∧
          haltingStateReached (ClearGadget.clearBodyRawTM dst) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨c0, cs, hcons⟩ : ∃ c0 cs, s.get dst = c0 :: cs := by
    cases hg : s.get dst with
    | nil => exact absurd hg hne
    | cons c0 cs => exact ⟨c0, cs, rfl⟩
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s dst h
  have hc0le : c0 ≤ 1 := by
    have hmem : s.get dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem c0 (by rw [hcons]; exact List.mem_cons_self ..)
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take dst) :=
    Compile.regBlocks_map_shiftReg (s.take dst)
  have hsklen : skipped.length = dst := by
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
  set midSuf : List Nat :=
    Compile.shiftReg cs ++ 0 :: (Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] ++ res)
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
  -- M₂: the deletion+rewind core (step 3 sub-lemma).
  obtain ⟨t2, h_sdr, h_sdr_traj, h_t2_bnd⟩ := Compile.stepDeleteRewind_run s dst res h hbit hne hres
  rw [← hregBlocks] at h_sdr h_sdr_traj
  -- `regBlocks skipped` and `midSuf` partition the tape after the leading sentinel
  -- and `dst`'s first cell, so `|regBlocks skipped| + 2 ≤ Lin`.
  have h_rb_le : (AppendGadget.regBlocks skipped).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [htape_nav]; simp only [List.length_cons, List.length_append]; omega
  have h_nav_le : ClearGadget.navSteps skipped ≤ 2 * (AppendGadget.regBlocks skipped).length + 1 :=
    ClearGadget.navSteps_le skipped
  -- navigation run, transported to `encodeTape` form.
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_content dst,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_content skipped (c0 + 1) midSuf hskip
      (by omega) (by omega)
    rw [← htape_nav, hsklen] at hn; exact hn
  -- shared `branchComposeFlatTM` inputs (M₁ navigation, sym-bound, M₁ trajectory).
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM dst).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM dst).sig
        (max ClearGadget.stepDeleteRewindRawTM.sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM dst).sig
          (max ClearGadget.stepDeleteRewindRawTM.sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig]; rfl, (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM dst)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content dst ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim dst ∧
      haltingStateReached (ClearGadget.navigateAndTestTM dst) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM dst) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped (c0 + 1) midSuf hskip
        (by omega) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt dst) hh,
           hh⟩
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [show ClearGadget.clearBodyRawTM dst
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM dst)
            ClearGadget.stepDeleteRewindRawTM ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content dst)
            (ClearGadget.navigateAndTestTM_exit_delim dst) from rfl,
      show ClearGadget.clearBodyRawTM_exitLoop dst
        = ClearGadget.stepDeleteRewindTM_exit + (ClearGadget.navigateAndTestTM dst).states from by
          show (ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindTM_exit
            = ClearGadget.stepDeleteRewindTM_exit + (ClearGadget.navigateAndTestTM dst).states
          omega]
    exact (branchComposeFlatTM_run_pos
      (show ClearGadget.navigateAndTestTM_exit_content dst
          ≠ ClearGadget.navigateAndTestTM_exit_delim dst from by
        show (ClearGadget.navigateToRegTM dst).states + 1
            ≠ (ClearGadget.navigateToRegTM dst).states + 2
        omega)
      (ClearGadget.navigateAndTestTM_valid dst) ClearGadget.stepDeleteRewindRawTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt dst)
      (ClearGadget.navigateAndTestTM_exit_delim_lt dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (by rw [show ClearGadget.stepDeleteRewindRawTM.start = 0 from rfl]; exact h_sdr)
      (Compile.haltingStateReached_of_halt ClearGadget.stepDeleteRewindRawTM_halt_seventeen)).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_pos
      (ClearGadget.navigateAndTestTM_valid dst) ClearGadget.stepDeleteRewindRawTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt dst)
      (ClearGadget.navigateAndTestTM_exit_delim_lt dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (by rw [show ClearGadget.stepDeleteRewindRawTM.start = 0 from rfl]; exact h_sdr_traj)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.clearBodyRawTM_exitDone_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.clearBodyRawTM_exitLoop_is_halt dst) hh, hh⟩
  · -- budget: `navSteps + 3 + t2 ≤ (2·rb+1) + 3 + (4·Lin+9) ≤ 6·Lin+12` (`rb+2 ≤ Lin`).
    omega

/-- **Clear loop body — done branch (Risk C2, step 4).** When register `dst` is
empty, the loop body `clearBodyRawTM dst` navigates to it, finds the delimiter `0`
(empty → delimiter branch), and rewinds to head `0`, leaving the tape unchanged
and landing at `clearBodyRawTM_exitDone dst`. Built by `branchComposeFlatTM_run_neg`
over `navigateAndTestTM_run_delim` (step 2) and `rewindToStart_run`
(`justRewindTM = scanLeftUntilTM 4 3`). -/
theorem Compile.clearBody_done_run (s : State) (dst : Var) (res : List Nat)
    (h : dst < s.length) (hbit : Compile.BitState s) (hempty : s.get dst = [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (ClearGadget.clearBodyRawTM dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.clearBodyRawTM_exitDone dst,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (ClearGadget.clearBodyRawTM dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitDone dst ∧
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitLoop dst ∧
          haltingStateReached (ClearGadget.clearBodyRawTM dst) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s dst h
  have hbit_take : Compile.BitState (s.take dst) :=
    fun reg hreg => hbit reg (List.mem_of_mem_take hreg)
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take dst) :=
    Compile.regBlocks_map_shiftReg (s.take dst)
  have hsklen : skipped.length = dst := by
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
    Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] ++ res with htaildef
  have htape_nav : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    rw [hs, hempty, hregBlocks, htaildef]
    simp [Compile.shiftReg, Compile.endMark, List.append_assoc]
  -- linear budget ingredients: `|regBlocks skipped| + 2 ≤ Lin` and `navSteps ≤ 2·rb+1`.
  have h_rb_le : (AppendGadget.regBlocks skipped).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [htape_nav]; simp only [List.length_cons, List.length_append]; omega
  have h_nav_le : ClearGadget.navSteps skipped ≤ 2 * (AppendGadget.regBlocks skipped).length + 1 :=
    ClearGadget.navSteps_le skipped
  -- `regBlocks skipped` is `{0,1,2}`-valued (no terminator).
  have hrb : ∀ x ∈ AppendGadget.regBlocks skipped, x < 4 ∧ x ≠ 3 := by
    rw [hregBlocks]; intro x hx
    exact ⟨Compile.encodeRegs_lt_four (s.take dst) hbit_take x hx,
           Compile.encodeRegs_no_endMark (s.take dst) hbit_take x hx⟩
  have hpref : ∀ x ∈ AppendGadget.regBlocks skipped ++ [0], x < 4 ∧ x ≠ 3 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrb x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  have hrestsplit : AppendGadget.regBlocks skipped ++ 0 :: tail'
      = (AppendGadget.regBlocks skipped ++ [0]) ++ tail' := by simp [List.append_assoc]
  -- M₃: rewind to the leading sentinel.
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
  -- shared `branchComposeFlatTM` inputs.
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM dst).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM dst).sig
        (max ClearGadget.stepDeleteRewindRawTM.sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM dst).sig
          (max ClearGadget.stepDeleteRewindRawTM.sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig]; rfl, (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim dst,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_delim skipped tail' hskip
    rw [← htape_nav, hsklen] at hn; exact hn
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM dst)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content dst ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim dst ∧
      haltingStateReached (ClearGadget.navigateAndTestTM dst) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM dst) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail' hskip
        (by decide) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt dst) hh,
           hh⟩
  have h_ne : ClearGadget.navigateAndTestTM_exit_content dst
      ≠ ClearGadget.navigateAndTestTM_exit_delim dst := by
    show (ClearGadget.navigateToRegTM dst).states + 1
        ≠ (ClearGadget.navigateToRegTM dst).states + 2
    omega
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1
      + ((1 + (AppendGadget.regBlocks skipped).length) + 1), ?_, ?_, ?_⟩
  · rw [show ClearGadget.clearBodyRawTM dst
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM dst)
            ClearGadget.stepDeleteRewindRawTM ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content dst)
            (ClearGadget.navigateAndTestTM_exit_delim dst) from rfl,
      show ClearGadget.clearBodyRawTM_exitDone dst
        = ClearGadget.justRewindTM_exit
            + ((ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindRawTM.states)
          from by
          show (ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindRawTM.states
              + ClearGadget.justRewindTM_exit
            = ClearGadget.justRewindTM_exit
                + ((ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindRawTM.states)
          omega]
    exact (branchComposeFlatTM_run_neg h_ne
      (ClearGadget.navigateAndTestTM_valid dst) ClearGadget.stepDeleteRewindRawTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt dst)
      (ClearGadget.navigateAndTestTM_exit_delim_lt dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1 h_rewind
      (Compile.haltingStateReached_of_halt (show ClearGadget.justRewindTM.halt[1]? = some true from rfl))).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_neg h_ne
      (ClearGadget.navigateAndTestTM_valid dst) ClearGadget.stepDeleteRewindRawTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt dst)
      (ClearGadget.navigateAndTestTM_exit_delim_lt dst)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (fun k' hk' ck' hck' => (h_rewind_traj k' hk' ck' hck').2)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.clearBodyRawTM_exitDone_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.clearBodyRawTM_exitLoop_is_halt dst) hh, hh⟩
  · -- budget: `navSteps + (rb + 5) ≤ (2·rb+1) + rb + 5 = 3·rb+6 ≤ 3·Lin ≤ 6·Lin+12`.
    omega

/-- An `Op` is in-bounds with respect to a state when all its register operands
are valid indices. Needed because the TM must physically navigate to each
register. -/
def Op.inBounds (o : Op) (s : State) : Prop :=
  match o with
  | .clear dst | .appendOne dst | .appendZero dst => dst < s.length
  | .copy dst src | .tail dst src | .head dst src | .nonEmpty dst src =>
      dst < s.length ∧ src < s.length
  | .eqBit dst src1 src2 => dst < s.length ∧ src1 < s.length ∧ src2 < s.length
  | .takeAt dst src lenReg | .dropAt dst src lenReg | .consLen dst lenReg src =>
      dst < s.length ∧ src < s.length ∧ lenReg < s.length
  | .concat dst src1 src2 => dst < s.length ∧ src1 < s.length ∧ src2 < s.length

/-- Reading an in-range register of a `BitState` yields a bit-shaped list (every
symbol `≤ 1`). The atom for `Op.eval_preserves_BitState`. -/
theorem Compile.BitState_get (s : State) (r : Var)
    (hbit : Compile.BitState s) (hr : r < s.length) :
    ∀ x ∈ s.get r, x ≤ 1 := by
  intro x hx
  refine hbit (s.get r) ?_ x hx
  rw [State.get, List.getElem?_eq_getElem hr]; exact List.getElem_mem hr

/-- **`BitState` is preserved by every op except `consLen` (HANDOFF bottom-up Task 4 — the
induction step the residue-tolerant compiler contract needs).**

`Compile_run_physical_residue` is proved by induction on `Cmd`, and every
per-fragment lemma it composes carries an `(hbit : BitState s)` premise (the
compiler's `sig = 4` alphabet has no room for a register cell `≥ 2`). So the
induction must re-establish `BitState` after each `Op`. This lemma is that step.

**Machine-checked risk finding (refines HANDOFF's "value-as-length ops are
non-`BitState`"):** of the three value-as-length ops, only **`consLen`** actually
*breaks* `BitState` — it writes `(s.get lenSrc).length` as a single cell, which is
`≥ 2` whenever `lenSrc` holds `≥ 2` symbols (witness `Op.consLen_breaks_BitState`).
`takeAt`/`dropAt` *preserve* `BitState` (their output is a sub-list of a bit-shaped
register); they are merely *useless* under `BitState` (the length read from a
`≤ 1` cell is `0` or `1`), not invariant-breaking. So Task 4's unary restatement is
required for **correctness** only for `consLen`; for `takeAt`/`dropAt` it is
required only for **expressiveness**. The `hcons` hypothesis isolates exactly the
`consLen` obligation: once HANDOFF bottom-up Task 4 restates `consLen` to write a unary block, the
written head cell is `≤ 1` and `hcons` is discharged unconditionally. -/
theorem Op.eval_preserves_BitState (o : Op) (s : State)
    (hbit : Compile.BitState s) (hbnd : o.inBounds s)
    (hcons : ∀ dst lenSrc src, o = Op.consLen dst lenSrc src →
        (s.get lenSrc).length ≤ 1) :
    Compile.BitState (Op.eval o s) := by
  cases o with
  | clear dst =>
      exact Compile.BitState_set s dst [] hbit hbnd (by simp)
  | appendOne dst =>
      refine Compile.BitState_set s dst _ hbit hbnd ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact Compile.BitState_get s dst hbit hbnd x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega
  | appendZero dst =>
      refine Compile.BitState_set s dst _ hbit hbnd ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact Compile.BitState_get s dst hbit hbnd x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega
  | copy dst src =>
      obtain ⟨hd, hs⟩ := hbnd
      exact Compile.BitState_set s dst _ hbit hd (Compile.BitState_get s src hbit hs)
  | tail dst src =>
      obtain ⟨hd, hs⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      exact Compile.BitState_get s src hbit hs x (List.mem_of_mem_tail hx)
  | head dst src =>
      obtain ⟨hd, hs⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      cases hsrc : s.get src with
      | nil => rw [hsrc] at hx; simp at hx
      | cons y ys =>
          rw [hsrc] at hx
          have hy : ∀ z ∈ (y :: ys), z ≤ 1 := by
            rw [← hsrc]; exact Compile.BitState_get s src hbit hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; exact hy y (List.mem_cons_self ..)
  | eqBit dst src1 src2 =>
      obtain ⟨hd, _, _⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      split at hx <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
  | nonEmpty dst src =>
      obtain ⟨hd, _⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      split at hx <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
  | takeAt dst src lenReg =>
      obtain ⟨hd, hs, _⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      exact Compile.BitState_get s src hbit hs x (List.mem_of_mem_take hx)
  | dropAt dst src lenReg =>
      obtain ⟨hd, hs, _⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      exact Compile.BitState_get s src hbit hs x (List.mem_of_mem_drop hx)
  | concat dst src1 src2 =>
      obtain ⟨hd, hs1, hs2⟩ := hbnd
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact Compile.BitState_get s src1 hbit hs1 x hx
      · exact Compile.BitState_get s src2 hbit hs2 x hx
  | consLen dst lenSrc src =>
      obtain ⟨hd, hs, _⟩ := hbnd
      have hlen := hcons dst lenSrc src rfl
      refine Compile.BitState_set s dst _ hbit hd ?_
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · subst hx; exact hlen
      · exact Compile.BitState_get s src hbit hs x hx

/-- **Machine-checked counterexample: `consLen` is the one op that breaks
`BitState`.** With `s = [[1, 1]]` (a valid `BitState`) and `o = consLen 0 0 0`,
the op writes `(s.get 0).length = 2` as a register cell, so the result `[[2,1,1]]`
is *not* a `BitState`. This is why HANDOFF bottom-up Task 4 must restate `consLen` to a unary block;
the corresponding `hcons` hypothesis of `Op.eval_preserves_BitState` fails here
(`(s.get 0).length = 2 > 1`). -/
theorem Op.consLen_breaks_BitState :
    ¬ Compile.BitState (Op.eval (Op.consLen 0 0 0) [[1, 1]]) := by
  intro h
  have : (2 : Nat) ≤ 1 := by
    refine h [2, 1, 1] ?_ 2 (by simp)
    show ([2, 1, 1] : List Nat) ∈ ([[2, 1, 1]] : State)
    simp
  omega

/-- **Risk C2 finding (machine-checked): the exact-tape physical contract is
unsatisfiable for length-decreasing ops.** No `FlatTM`, in any number of steps,
can run from `encodeTape s` to a configuration whose tape is *exactly*
`encodeTape (Op.eval (.clear dst) s)` when register `dst` is non-empty — because
the physical tape never shrinks (`runFlatTM_initFlatConfig_no_shrink`) yet
clearing a non-empty register *shortens* the encoded tape. Concrete witness
`s = [[1]]`, `dst = 0`: `encodeTape [[1]]` has length `4`, but
`encodeTape (clear 0 ↦ [[]])` has length `3`.

This is the obstruction behind `compileOp_sound_physical` (below): it **cannot**
be proved for `clear` / `tail` / shrinking `copy` / `head` / `eqBit` /
`nonEmpty` / the length ops as stated, since each can shorten the tape. Only
`appendOne` / `appendZero` (which purely grow it) fit the exact-tape contract.
See `Complexity/Complexity/TapeMono.lean` and ROADMAP Risk C2 for the resolution
(a residue-tolerant contract `encodeTape output ++ filler` + a left-shift delete
gadget). -/
theorem Compile.clear_physical_unsatisfiable (M : FlatTM) (n q : Nat) :
    runFlatTM n M (initFlatConfig M [Compile.encodeTape [[1]]])
      ≠ some { state_idx := q,
               tapes := [([], 0, Compile.encodeTape (Op.eval (Op.clear 0) [[1]]))] } := by
  intro h
  have hno : (Compile.encodeTape [[1]]).length
      ≤ (Compile.encodeTape (Op.eval (Op.clear 0) [[1]])).length :=
    runFlatTM_initFlatConfig_no_shrink M n (Compile.encodeTape [[1]]) _ _ h rfl
  have hin : (Compile.encodeTape [[1]]).length = 4 := by
    rw [Compile.encodeTape_length]; decide
  have hout : (Compile.encodeTape (Op.eval (Op.clear 0) [[1]])).length = 3 := by
    rw [Compile.encodeTape_length]; decide
  rw [hin, hout] at hno
  omega

/-- The **residue-tolerant** tape relation (Risk C2, the finding fix). A tape
satisfies `TapeOK out tp` when the `right` component is `encodeTape out ++ res`
for some terminator-free residue `res` (`ValidResidue`), and the head is rewound
to `0`. This replaces the exact-tape contract `tp = encodeTape out` which is
**unsatisfiable for length-decreasing ops** (the physical tape never shrinks,
`TapeMono.lean`).

Composition hides the residue existentially: the `compileSeq_sound_physical_residue`
combinator takes `TapeOK` inputs and produces a `TapeOK` output. Decode is
unaffected (`decodeTape_encodeTape_append`: `decodeTape` stops at the first
`endMark` terminator, so the trailing residue is invisible). -/
def Compile.TapeOK (out : State) (tp : List Nat) : Prop :=
  ∃ res : List Nat, Compile.ValidResidue res ∧ tp = Compile.encodeTape out ++ res

theorem Compile.TapeOK_exact (out : State) :
    Compile.TapeOK out (Compile.encodeTape out) :=
  ⟨[], Compile.ValidResidue_nil, (List.append_nil _).symm⟩

theorem Compile.TapeOK_append_residue (out : State) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    Compile.TapeOK out (Compile.encodeTape out ++ res) :=
  ⟨res, hres, rfl⟩


/-- **Reusable raw two-phase append run (Risk C2, Task 2 critical path).** Running
`appendAtThenTwoPhaseRewindTM (bit+1) dst` from head `0` on `encodeTape s ++ res`
appends bit `bit` to the end of register `dst` and two-phase-rewinds the head to
`0`, leaving `encodeTape (s.set dst (s.get dst ++ [bit])) ++ res` (residue passes
through unchanged), at the gadget's found exit `6 + (appendAtTM (bit+1) dst).states`,
never halting earlier, in `≤ 3·inputTapeLen + 8` steps. This is the bracket-free
core shared by `opAppendBit_physical_residue` (which wraps it in `rewindBracket`)
and the move gadget's `moveBitM2_run` (which composes it after a delete). -/
theorem Compile.appendBitTwoPhase_run (bit : Nat) (hb : bit ≤ 1)
    (s : State) (dst : Var) (hbit : Compile.BitState s) (hdst : dst < s.length)
    (res_in : List Nat) (hres_in : Compile.ValidResidue res_in) :
    ∃ t : Nat,
      runFlatTM t (AppendGadget.appendAtThenTwoPhaseRewindTM (bit + 1) dst)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := 6 + (AppendGadget.appendAtTM (bit + 1) dst).states,
                 tapes := [([], 0,
                   Compile.encodeTape (s.set dst (s.get dst ++ [bit])) ++ res_in)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (AppendGadget.appendAtThenTwoPhaseRewindTM (bit + 1) dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } = some ck →
          haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (bit + 1) dst) ck = false)
      ∧ t ≤ 3 * (Compile.encodeTape s ++ res_in).length + 8 := by
  have h_ins : bit + 1 < 4 := by omega
  -- === encodeTape decomposition (mirrors `opAppendBit_physical_residue`) ===
  set post : List Nat := Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] with hpost
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskip
  set body : List Nat := Compile.shiftReg (s.get dst) with hbody
  have hget_mem : s.get dst ∈ s := by
    rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
  have hshift_lt : ∀ (r : List Nat), (∀ x ∈ r, x ≤ 1) → ∀ x ∈ Compile.shiftReg r, x < 4 := by
    intro r hr x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hr y hy; omega
  have hshift_ne : ∀ (r : List Nat), ∀ x ∈ Compile.shiftReg r, x ≠ 0 := by
    intro r x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; omega
  have hlen : skipped.length = dst := by
    rw [hskip, List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hdst)]
  have h_pre : ∀ x ∈ ([] : List Nat), x < 4 := by intro x hx; cases hx
  have h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    intro b hbm
    rw [hskip, List.mem_map] at hbm
    obtain ⟨r, hr, rfl⟩ := hbm
    exact ⟨hshift_ne r, hshift_lt r (fun x hx => hbit r (List.mem_of_mem_take hr) x hx)⟩
  have hbody_ne : ∀ x ∈ body, x ≠ 0 := by rw [hbody]; exact hshift_ne _
  have hbody_lt : ∀ x ∈ body, x < 4 := by
    rw [hbody]; exact hshift_lt _ (fun x hx => hbit _ hget_mem x hx)
  have hpost_lt : ∀ x ∈ post, x < 4 := by
    rw [hpost]; intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeRegs_lt_four _
        (fun b hbm y hy => hbit b (List.mem_of_mem_drop hbm) y hy) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide
  have key : ∃ (sk : List (List Nat)) (bd : List Nat),
      sk.length = dst ∧
      (∀ b ∈ sk, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) ∧
      (∀ x ∈ bd, x ≠ 0) ∧ (∀ x ∈ bd, x < 4) ∧
      AppendGadget.regBlocks sk ++ bd
        = Compile.endMark :: (AppendGadget.regBlocks skipped ++ body) := by
    cases hsk : skipped with
    | nil =>
        refine ⟨[], Compile.endMark :: body, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hlen, hsk]
        · intro b hb; cases hb
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_ne x h
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_lt x h
        · simp [AppendGadget.regBlocks_nil]
    | cons hd tl =>
        refine ⟨(Compile.endMark :: hd) :: tl, body, ?_, ?_, hbody_ne, hbody_lt, ?_⟩
        · rw [hsk] at hlen; simpa using hlen
        · intro b hb
          rcases List.mem_cons.mp hb with h | h
          · subst h
            refine ⟨?_, ?_⟩
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).1 x h0
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).2 x h0
          · exact h_skip b (by rw [hsk]; exact List.mem_cons_of_mem _ h)
        · simp [AppendGadget.regBlocks_cons]
  obtain ⟨sk, bd, hlen_sk, h_skip_sk, hbd_ne, hbd_lt, hsfold⟩ := key
  have hsplit0 : AppendGadget.regBlocks skipped ++ body ++ 0 :: post
      = Compile.encodeRegs s ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost]; exact Compile.encodeTape_split s dst hdst
  have hsplit : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post
      = Compile.encodeTape s := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, hsplit0]
  have htape0 : AppendGadget.regBlocks skipped ++ body ++ (bit + 1) :: 0 :: post
      = Compile.encodeRegs (s.set dst (s.get dst ++ [bit])) ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost, Compile.regBlocks_map_shiftReg]
    rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst,
        Compile.encodeRegs_append, Compile.encodeRegs_cons, Compile.shiftReg_append]
    simp [List.append_assoc]
  have htape : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post
      = Compile.encodeTape (s.set dst (s.get dst ++ [bit])) := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, htape0]
  set output : State := s.set dst (s.get dst ++ [bit]) with houtput
  have hbit_out : Compile.BitState output :=
    Compile.BitState_appendBit bit hb s dst hbit hdst
  -- === residue extension: post' = post ++ res_in, terminator at p = |encodeTape output| - 1 ===
  set post' : List Nat := post ++ res_in with hpost'
  set p : Nat := (Compile.encodeTape output).length - 1 with hpdef
  have hsplitr : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post'
      = Compile.encodeTape s ++ res_in := by
    rw [hpost', show (0 : Nat) :: (post ++ res_in) = (0 :: post) ++ res_in from rfl,
        ← List.append_assoc, hsplit]
  have hTPr : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post'
      = Compile.encodeTape output ++ res_in := by
    rw [hpost', show (bit + 1 : Nat) :: 0 :: (post ++ res_in)
          = ((bit + 1) :: 0 :: post) ++ res_in from rfl,
        ← List.append_assoc, htape]
  have hEO_succ : (Compile.encodeTape output).length = (Compile.encodeTape s).length + 1 := by
    have hl1 := congrArg List.length htape
    have hl2 := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil] at hl1 hl2
    omega
  have hEO_pos : 0 < (Compile.encodeTape output).length := by omega
  have hEs_ge : 2 ≤ (Compile.encodeTape s).length := by rw [Compile.encodeTape_length]; omega
  have hHDlen : ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
      + (0 :: post').length = (Compile.encodeTape s ++ res_in).length := by
    have h := congrArg List.length hsplitr
    simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega
  have hleft : ∀ i (hiL : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length)
      (hi_lt : i < (Compile.encodeTape output).length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, hiL⟩
        = (Compile.encodeTape output).get ⟨i, hi_lt⟩ := by
    intro i hiL hi_lt
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc := congrArg (fun l => l[i]?) hTPr
    simp only [] at hc
    rw [List.getElem?_eq_getElem hiL, List.getElem?_append_left hi_lt,
        List.getElem?_eq_getElem hi_lt] at hc
    exact Option.some.inj hc
  have hright : ∀ i (hiL : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length)
      (hi_ge : (Compile.encodeTape output).length ≤ i)
      (hir : i - (Compile.encodeTape output).length < res_in.length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, hiL⟩
        = res_in.get ⟨i - (Compile.encodeTape output).length, hir⟩ := by
    intro i hiL hi_ge hir
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc := congrArg (fun l => l[i]?) hTPr
    simp only [] at hc
    rw [List.getElem?_eq_getElem hiL, List.getElem?_append_right hi_ge,
        List.getElem?_eq_getElem hir] at hc
    exact Option.some.inj hc
  have h_tp_lt : ∀ x ∈ ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
      ++ (bit + 1) :: 0 :: post', x < 4 := by
    intro x hx; rw [hTPr, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four output hbit_out x hx
    · exact (hres_in x hx).1
  have h_t0 : ∀ (h : 0 < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨0, h⟩
        = 3 := by
    intro h
    rw [hleft 0 h hEO_pos]
    exact Compile.encodeTape_get_zero output hEO_pos
  have h_term : ∀ (h : p < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨p, h⟩
        = 3 := by
    intro h
    have hpEO : p < (Compile.encodeTape output).length := by rw [hpdef]; omega
    rw [hleft p h hpEO]
    exact Compile.encodeTape_get_last output hpEO
  have h_interior_ne : ∀ i, 0 < i → i < p →
      ∃ (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
          ++ (bit + 1) :: 0 :: post').length),
        (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, h⟩
          ≠ 3 := by
    intro i hi hip
    have hiEO : i + 1 < (Compile.encodeTape output).length := by rw [hpdef] at hip; omega
    obtain ⟨hi_lt, hne⟩ := Compile.encodeTape_interior_ne_endMark output hbit_out i hi hiEO
    have hi_TPr : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length := by
      rw [hTPr, List.length_append]; omega
    refine ⟨hi_TPr, ?_⟩
    rw [hleft i hi_TPr hi_lt]
    exact hne
  have h_residue_ne : ∀ i, p < i →
      i ≤ ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
        + (0 :: post').length →
      ∃ (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
          ++ (bit + 1) :: 0 :: post').length),
        (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, h⟩
          ≠ 3 := by
    intro i hip hiHD
    have hiEO : (Compile.encodeTape output).length ≤ i := by rw [hpdef] at hip; omega
    have hir : i - (Compile.encodeTape output).length < res_in.length := by
      rw [hHDlen, List.length_append] at hiHD; omega
    have hi_TPr : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length := by
      rw [hTPr, List.length_append]; omega
    refine ⟨hi_TPr, ?_⟩
    rw [hright i hi_TPr hiEO hir]
    exact (hres_in _ (List.getElem_mem _)).2
  have hp_pos : 0 < p := by rw [hpdef]; omega
  have hp_le : p ≤ ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
      + (0 :: post').length := by
    rw [hHDlen, List.length_append, hpdef, hEO_succ]; omega
  have hpost'_lt : ∀ x ∈ post', x < 4 := by
    intro x hx; rw [hpost', List.mem_append] at hx
    rcases hx with hx | hx
    · exact hpost_lt x hx
    · exact (hres_in x hx).1
  have hrun_g := AppendGadget.appendAt_twoPhaseRewind_run (bit + 1) h_ins dst [] sk bd post' p
    hlen_sk h_pre h_skip_sk hbd_ne hbd_lt hpost'_lt
    h_tp_lt hp_pos hp_le h_t0 h_term h_interior_ne h_residue_ne
  have htraj_g := AppendGadget.appendAt_twoPhaseRewind_no_early_halt (bit + 1) h_ins dst [] sk bd
    post' p hlen_sk h_pre h_skip_sk hbd_ne hbd_lt hpost'_lt
    h_tp_lt hp_pos hp_le h_t0 h_term h_interior_ne h_residue_ne
  rw [hsplitr, hTPr] at hrun_g
  rw [hsplitr] at htraj_g
  refine ⟨AppendGadget.appendAt_steps sk bd post' + 1
      + (((([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
          + (0 :: post').length) - p + 1) + 1 + (1 + 1 + p)), hrun_g.1, htraj_g, ?_⟩
  -- budget: ≤ 3·L_in + 8.
  have hstep_le : AppendGadget.appendAt_steps sk bd post'
      ≤ 2 * (Compile.encodeTape s ++ res_in).length + 3 := by
    have hb' := AppendGadget.appendAt_steps_le sk bd post'
    have hL : (AppendGadget.regBlocks sk ++ bd ++ 0 :: post').length
        = (Compile.encodeTape s ++ res_in).length := by rw [← hsplitr]; simp
    rw [hL] at hb'; exact hb'
  have hp_le' : p ≤ (Compile.encodeTape s ++ res_in).length := by rw [← hHDlen]; exact hp_le
  omega

/-- **Residue-tolerant per-op physical contract for the append op (Risk C2, step
1c — the substantive per-op proof).** The rewinding append op `opAppendBitRewind
(bit+1) … dst` run on `encodeTape s ++ res_in` (the previous fragment may leave a
`ValidResidue res_in`) halts at the unique exit with the **head rewound to `0`**
and the tape `encodeTape (output) ++ res_in` — the residue **passes through
unchanged** (`res_out = res_in`) since the insert grows `encodeTape s` by exactly
one cell — never halting earlier, in `≤ 3·inputTapeLen + 8` steps.

Mechanism: `rewindBracket_transport` (the general halt-demotion run transport) fed
by the proven two-phase append gadget run `appendAt_twoPhaseRewind_run`/
`_no_early_halt`. The `encodeTape` decomposition (sentinel-folded blocks `sk`/`bd`,
the real-terminator position `p = (encodeTape output).length − 1`, the residue
sitting past `p`) discharges the gadget's tape side-conditions from
`encodeTape_get_zero`/`_get_last`/`_interior_ne_endMark` and `ValidResidue res_in`.

The budget is `+8` (not the single-phase `appendBit_physical`'s `+6`): the
two-phase rewind costs two extra `Lmove`s — one to step off the residue side of
the real terminator, plus the boundary-phase setup. Still linear, so it composes
into the quadratic `Compile_run_physical_residue` total with constant slack. -/
theorem Compile.opAppendBit_physical_residue (bit : Nat) (hb : bit ≤ 1)
    (s : State) (dst : Var) (hbit : Compile.BitState s) (hdst : dst < s.length)
    (res_in : List Nat) (hres_in : Compile.ValidResidue res_in) :
    ∃ t : Nat,
      runFlatTM t (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M
          (initFlatConfig (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M
            [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opAppendBitRewind (bit + 1) (by omega) dst).exit,
                 tapes := [([], 0,
                   Compile.encodeTape (s.set dst (s.get dst ++ [bit])) ++ res_in)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M
              (initFlatConfig (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M
                [Compile.encodeTape s ++ res_in]) = some ck →
          ck.state_idx ≠ (Compile.opAppendBitRewind (bit + 1) (by omega) dst).exit ∧
          haltingStateReached (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M ck = false)
      ∧ t ≤ 3 * (Compile.encodeTape s ++ res_in).length + 8 := by
  have h_ins : bit + 1 < 4 := by omega
  -- === encodeTape decomposition (mirrors `appendBit_physical`) ===
  set post : List Nat := Compile.encodeRegs (s.drop (dst + 1)) ++ [Compile.endMark] with hpost
  set skipped : List (List Nat) := (s.take dst).map Compile.shiftReg with hskip
  set body : List Nat := Compile.shiftReg (s.get dst) with hbody
  have hget_mem : s.get dst ∈ s := by
    rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
  have hshift_lt : ∀ (r : List Nat), (∀ x ∈ r, x ≤ 1) → ∀ x ∈ Compile.shiftReg r, x < 4 := by
    intro r hr x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hr y hy; omega
  have hshift_ne : ∀ (r : List Nat), ∀ x ∈ Compile.shiftReg r, x ≠ 0 := by
    intro r x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; omega
  have hlen : skipped.length = dst := by
    rw [hskip, List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hdst)]
  have h_pre : ∀ x ∈ ([] : List Nat), x < 4 := by intro x hx; cases hx
  have h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := by
    intro b hbm
    rw [hskip, List.mem_map] at hbm
    obtain ⟨r, hr, rfl⟩ := hbm
    exact ⟨hshift_ne r, hshift_lt r (fun x hx => hbit r (List.mem_of_mem_take hr) x hx)⟩
  have hbody_ne : ∀ x ∈ body, x ≠ 0 := by rw [hbody]; exact hshift_ne _
  have hbody_lt : ∀ x ∈ body, x < 4 := by
    rw [hbody]; exact hshift_lt _ (fun x hx => hbit _ hget_mem x hx)
  have hpost_lt : ∀ x ∈ post, x < 4 := by
    rw [hpost]; intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeRegs_lt_four _
        (fun b hbm y hy => hbit b (List.mem_of_mem_drop hbm) y hy) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide
  have key : ∃ (sk : List (List Nat)) (bd : List Nat),
      sk.length = dst ∧
      (∀ b ∈ sk, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) ∧
      (∀ x ∈ bd, x ≠ 0) ∧ (∀ x ∈ bd, x < 4) ∧
      AppendGadget.regBlocks sk ++ bd
        = Compile.endMark :: (AppendGadget.regBlocks skipped ++ body) := by
    cases hsk : skipped with
    | nil =>
        refine ⟨[], Compile.endMark :: body, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hlen, hsk]
        · intro b hb; cases hb
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_ne x h
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact hbody_lt x h
        · simp [AppendGadget.regBlocks_nil]
    | cons hd tl =>
        refine ⟨(Compile.endMark :: hd) :: tl, body, ?_, ?_, hbody_ne, hbody_lt, ?_⟩
        · rw [hsk] at hlen; simpa using hlen
        · intro b hb
          rcases List.mem_cons.mp hb with h | h
          · subst h
            refine ⟨?_, ?_⟩
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).1 x h0
            · intro x hx
              rcases List.mem_cons.mp hx with h0 | h0
              · subst h0; decide
              · exact (h_skip hd (by rw [hsk]; exact List.mem_cons_self ..)).2 x h0
          · exact h_skip b (by rw [hsk]; exact List.mem_cons_of_mem _ h)
        · simp [AppendGadget.regBlocks_cons]
  obtain ⟨sk, bd, hlen_sk, h_skip_sk, hbd_ne, hbd_lt, hsfold⟩ := key
  have hsplit0 : AppendGadget.regBlocks skipped ++ body ++ 0 :: post
      = Compile.encodeRegs s ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost]; exact Compile.encodeTape_split s dst hdst
  have hsplit : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post
      = Compile.encodeTape s := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, hsplit0]
  have htape0 : AppendGadget.regBlocks skipped ++ body ++ (bit + 1) :: 0 :: post
      = Compile.encodeRegs (s.set dst (s.get dst ++ [bit])) ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost, Compile.regBlocks_map_shiftReg]
    rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst,
        Compile.encodeRegs_append, Compile.encodeRegs_cons, Compile.shiftReg_append]
    simp [List.append_assoc]
  have htape : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post
      = Compile.encodeTape (s.set dst (s.get dst ++ [bit])) := by
    rw [Compile.encodeTape, List.nil_append, hsfold, List.cons_append, htape0]
  set output : State := s.set dst (s.get dst ++ [bit]) with houtput
  have hbit_out : Compile.BitState output :=
    Compile.BitState_appendBit bit hb s dst hbit hdst
  -- === residue extension: post' = post ++ res_in, terminator at p = |encodeTape output| - 1 ===
  set post' : List Nat := post ++ res_in with hpost'
  set p : Nat := (Compile.encodeTape output).length - 1 with hpdef
  -- start/exit tape equalities with the residue appended.
  have hsplitr : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post'
      = Compile.encodeTape s ++ res_in := by
    rw [hpost', show (0 : Nat) :: (post ++ res_in) = (0 :: post) ++ res_in from rfl,
        ← List.append_assoc, hsplit]
  have hTPr : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post'
      = Compile.encodeTape output ++ res_in := by
    rw [hpost', show (bit + 1 : Nat) :: 0 :: (post ++ res_in)
          = ((bit + 1) :: 0 :: post) ++ res_in from rfl,
        ← List.append_assoc, htape]
  -- length facts.
  have hEO_succ : (Compile.encodeTape output).length = (Compile.encodeTape s).length + 1 := by
    have hl1 := congrArg List.length htape
    have hl2 := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil] at hl1 hl2
    omega
  have hEO_pos : 0 < (Compile.encodeTape output).length := by omega
  have hEs_ge : 2 ≤ (Compile.encodeTape s).length := by rw [Compile.encodeTape_length]; omega
  -- `HD` (the head position = exit-tape length − 1) equals the input tape length.
  have hHDlen : ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
      + (0 :: post').length = (Compile.encodeTape s ++ res_in).length := by
    have h := congrArg List.length hsplitr
    simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega
  -- `get` transfer across `hTPr`, split into the `encodeTape output` part and the
  -- residue part (avoids a `Fin.val`-coercion mismatch in `getElem_append_*`).
  have hleft : ∀ i (hiL : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length)
      (hi_lt : i < (Compile.encodeTape output).length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, hiL⟩
        = (Compile.encodeTape output).get ⟨i, hi_lt⟩ := by
    intro i hiL hi_lt
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc := congrArg (fun l => l[i]?) hTPr
    simp only [] at hc
    rw [List.getElem?_eq_getElem hiL, List.getElem?_append_left hi_lt,
        List.getElem?_eq_getElem hi_lt] at hc
    exact Option.some.inj hc
  have hright : ∀ i (hiL : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length)
      (hi_ge : (Compile.encodeTape output).length ≤ i)
      (hir : i - (Compile.encodeTape output).length < res_in.length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, hiL⟩
        = res_in.get ⟨i - (Compile.encodeTape output).length, hir⟩ := by
    intro i hiL hi_ge hir
    rw [List.get_eq_getElem, List.get_eq_getElem]
    have hc := congrArg (fun l => l[i]?) hTPr
    simp only [] at hc
    rw [List.getElem?_eq_getElem hiL, List.getElem?_append_right hi_ge,
        List.getElem?_eq_getElem hir] at hc
    exact Option.some.inj hc
  -- === the gadget side-conditions, via the `encodeTape output ++ res_in` structure ===
  have h_tp_lt : ∀ x ∈ ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
      ++ (bit + 1) :: 0 :: post', x < 4 := by
    intro x hx; rw [hTPr, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four output hbit_out x hx
    · exact (hres_in x hx).1
  have h_t0 : ∀ (h : 0 < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨0, h⟩
        = 3 := by
    intro h
    rw [hleft 0 h hEO_pos]
    exact Compile.encodeTape_get_zero output hEO_pos
  have h_term : ∀ (h : p < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length),
      (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨p, h⟩
        = 3 := by
    intro h
    have hpEO : p < (Compile.encodeTape output).length := by rw [hpdef]; omega
    rw [hleft p h hpEO]
    exact Compile.encodeTape_get_last output hpEO
  have h_interior_ne : ∀ i, 0 < i → i < p →
      ∃ (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
          ++ (bit + 1) :: 0 :: post').length),
        (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, h⟩
          ≠ 3 := by
    intro i hi hip
    have hiEO : i + 1 < (Compile.encodeTape output).length := by rw [hpdef] at hip; omega
    obtain ⟨hi_lt, hne⟩ := Compile.encodeTape_interior_ne_endMark output hbit_out i hi hiEO
    have hi_TPr : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length := by
      rw [hTPr, List.length_append]; omega
    refine ⟨hi_TPr, ?_⟩
    rw [hleft i hi_TPr hi_lt]
    exact hne
  have h_residue_ne : ∀ i, p < i →
      i ≤ ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
        + (0 :: post').length →
      ∃ (h : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
          ++ (bit + 1) :: 0 :: post').length),
        (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (bit + 1) :: 0 :: post').get ⟨i, h⟩
          ≠ 3 := by
    intro i hip hiHD
    -- HD = |encodeTape s ++ res_in|; i ≤ HD < |encodeTape output ++ res_in|.
    have hiEO : (Compile.encodeTape output).length ≤ i := by rw [hpdef] at hip; omega
    have hir : i - (Compile.encodeTape output).length < res_in.length := by
      rw [hHDlen, List.length_append] at hiHD; omega
    have hi_TPr : i < (([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd
        ++ (bit + 1) :: 0 :: post').length := by
      rw [hTPr, List.length_append]; omega
    refine ⟨hi_TPr, ?_⟩
    rw [hright i hi_TPr hiEO hir]
    exact (hres_in _ (List.getElem_mem _)).2
  -- positivity/range for the gadget's terminator position.
  have hp_pos : 0 < p := by rw [hpdef]; omega
  have hp_le : p ≤ ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
      + (0 :: post').length := by
    rw [hHDlen, List.length_append, hpdef, hEO_succ]; omega
  -- === run the two-phase append gadget ===
  have hrun_g := AppendGadget.appendAt_twoPhaseRewind_run (bit + 1) h_ins dst [] sk bd post' p
    hlen_sk h_pre h_skip_sk hbd_ne hbd_lt
    (by intro x hx; rw [hpost', List.mem_append] at hx
        rcases hx with hx | hx
        · exact hpost_lt x hx
        · exact (hres_in x hx).1)
    h_tp_lt hp_pos hp_le h_t0 h_term h_interior_ne h_residue_ne
  have htraj_g := AppendGadget.appendAt_twoPhaseRewind_no_early_halt (bit + 1) h_ins dst [] sk bd
    post' p hlen_sk h_pre h_skip_sk hbd_ne hbd_lt
    (by intro x hx; rw [hpost', List.mem_append] at hx
        rcases hx with hx | hx
        · exact hpost_lt x hx
        · exact (hres_in x hx).1)
    h_tp_lt hp_pos hp_le h_t0 h_term h_interior_ne h_residue_ne
  -- the gadget machine is defeq to the rewindBracket composite; rewrite tapes/state.
  simp only [AppendGadget.appendAtThenTwoPhaseRewindTM] at hrun_g htraj_g
  rw [hsplitr, hTPr, show (6 : Nat) + (AppendGadget.appendAtTM (bit + 1) dst).states
        = (AppendGadget.appendAtTM (bit + 1) dst).states + 6 from Nat.add_comm ..] at hrun_g
  rw [hsplitr] at htraj_g
  -- feed through the general transport lemma.
  have htrans := Compile.rewindBracket_transport (AppendGadget.appendAtTM (bit + 1) dst)
    (AppendGadget.appendAtTM_exit dst)
    (AppendGadget.appendAtTM_valid (bit + 1) (by omega) dst)
    (AppendGadget.appendAtTM_exit_lt (bit + 1) dst)
    (AppendGadget.appendAtTM_tapes (bit + 1) dst) (AppendGadget.appendAtTM_sig (bit + 1) dst)
    hrun_g.1 htraj_g
  -- align the start config with `initFlatConfig`.
  have hstart0 : (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M.start = 0 := by
    show (Compile.rewindBracket (AppendGadget.appendAtTM (bit + 1) dst) _ _ _ _ _).M.start = 0
    rw [Compile.rewindBracket_M, Compile.joinTwoHalts_start, composeFlatTM_start,
        AppendGadget.appendAtTM_start]
  have hinit : initFlatConfig (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M
        [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hstart0, List.map_cons, List.map_nil]
  refine ⟨AppendGadget.appendAt_steps sk bd post' + 1
      + (((([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
          + (0 :: post').length) - p + 1) + 1 + (1 + 1 + p)), ?_, ?_, ?_⟩
  · -- `opAppendBitRewind` is defeq to the `rewindBracket` of `htrans`; normalise the
    -- start config with `hinit` (head `[].length` is defeq `0`), then close by defeq.
    rw [hinit]; exact htrans.1
  · intro k hk ck hck
    rw [hinit] at hck
    exact htrans.2 k hk ck hck
  · -- budget: ≤ 3·L_in + 8.
    have hstep_le : AppendGadget.appendAt_steps sk bd post'
        ≤ 2 * (Compile.encodeTape s ++ res_in).length + 3 := by
      have hb' := AppendGadget.appendAt_steps_le sk bd post'
      have hL : (AppendGadget.regBlocks sk ++ bd ++ 0 :: post').length
          = (Compile.encodeTape s ++ res_in).length := by rw [← hsplitr]; simp
      rw [hL] at hb'; exact hb'
    have hp_le' : p ≤ (Compile.encodeTape s ++ res_in).length := by rw [← hHDlen]; exact hp_le
    omega

/-- The append ops' linear budget `3·tapeLen + 8` implies the per-op contract's
quadratic budget `9·tapeLen² + 9` (every encoded tape has `tapeLen ≥ 2`). Lets
the linear append cases discharge the (necessarily quadratic, for multi-cell ops)
`compileOp_sound_physical_residue` budget. -/
theorem Compile.linear_le_quadratic_tapeLen (s : State) (res_in : List Nat) :
    3 * (Compile.encodeTape s ++ res_in).length + 8
      ≤ 9 * (Compile.encodeTape s ++ res_in).length
          * (Compile.encodeTape s ++ res_in).length + 9 := by
  have hL : 2 ≤ (Compile.encodeTape s ++ res_in).length := by
    rw [List.length_append, Compile.encodeTape_length]; omega
  set L := (Compile.encodeTape s ++ res_in).length with hLdef
  have h1 : 9 * L ≤ 9 * L * L := by
    calc 9 * L = 9 * L * 1 := by rw [Nat.mul_one]
      _ ≤ 9 * L * L := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Uniform per-term bound on `loopBudget`.** If every iteration body and the
done branch each run in `≤ M` steps (counting the `+1` backward/leave bridge),
then the whole counted loop runs in `≤ (n+1)·M` steps. The clear loop instantiates
`M` with a linear-in-tape-length bound, giving the quadratic total. -/
theorem Compile.loopBudget_le (tIter : Nat → Nat) (tDone M : Nat) :
    ∀ n, (tDone + 1 ≤ M) → (∀ j, j < n → tIter j + 1 ≤ M) →
      loopBudget tIter tDone n ≤ (n + 1) * M
  | 0, hDone, _ => by simp only [loopBudget]; omega
  | n + 1, hDone, hIter => by
      have ih := Compile.loopBudget_le tIter tDone M n hDone
        (fun j hj => hIter j (Nat.lt_succ_of_lt hj))
      have hI : tIter n + 1 ≤ M := hIter n (Nat.lt_succ_self n)
      have hstep : loopBudget tIter tDone (n + 1) = tIter n + 1 + loopBudget tIter tDone n := rfl
      have hexp : (n + 1 + 1) * M = (n + 1) * M + M := by ring
      rw [hstep, hexp]
      omega

/-- **Clear-loop budget arithmetic.** The per-iteration linear bound `6·L+13`
summed over `n+1 ≤ L−1` terms is dominated by the quadratic `9·L²+9`. Proven by
substituting `L = n+2+d` (legal since `n+2 ≤ L`): the difference is a polynomial
with non-negative coefficients. -/
theorem Compile.clearBudget_arith (n L : Nat) (h : n + 2 ≤ L) :
    (n + 1) * (6 * L + 13) ≤ 9 * L * L + 9 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  nlinarith [Nat.zero_le n, Nat.zero_le d, Nat.zero_le (n * d)]

/-- **Per-op contract budget loosening `9 → 54` (the `eqBit` enabler).** The
proven ops establish the tight `(9·L²+9·L+30)·c`; `compileOp_sound_physical_residue`
states the looser `(54·L²+54·L+180)·c` (room for the `eqBit` cascade — see the
finding above that theorem). The looser constant is free against `physStepBudget`
(8× headroom, `54 ≤ 72`). `omega` atomises `L*L`.

**2026-06-20d (bottom-up):** loosened `27 → 54`. The prior `27` was calibrated to
the `EqBitBudgetProbe` **#eval real** step counts (~70% of `(9·L²)·2`) times an
assumed `1.7×` "provable" factor. But the bounds actually *recoverable from the
sub-gadgets* (the d2-iv symbolic component sum: `navSteps_le` 2×, each
`branchComposeFlatTM`/`composeFlatTM` seam additive, `opTailSelf ≤ 6L+14`,
`clearRegion ≤ 9L²`, two scratch copies, the `(matchLen+1)·M_body` loop with the
provable `M_body ≈ 24·L`, the cleanup's two clears, plus the d1 wrapper's
`clear dst`) sum to **~60·L²** — *3-4× real*, not `1.7×`, because each gadget's
provable bound is `1.5–2×` real and they stack through the loop. `54` gives the
cascade comfortable (~57%) margin and is still free (`54 ≤ 72`); `physStepBudget`,
`Op.cost`, and EvalCnf are untouched. Do NOT re-tighten below the symbolic sum. -/
theorem Compile.opBudgetLoosen {L c d : Nat}
    (h : d ≤ (9 * L * L + 9 * L + 30) * c) :
    d ≤ (54 * L * L + 54 * L + 180) * c :=
  le_trans h (Nat.mul_le_mul_right _
    (by nlinarith [Nat.zero_le (L * L), Nat.zero_le L]))

/-- **`clearRegionTM` run (Risk C2, step 5b).** Assembled from `loopTM_run`. The
loop deletes register `dst`'s `n = |s.get dst|` leading cells one per iteration
(`clearBody_delete_run`), then the done branch fires when `dst` is empty
(`clearBody_done_run`). The tape sequence is `T j = encodeTape (s.set dst (drop
(n−j))) ++ (res_in ++ replicate (n−j) 0)`: `T n = encodeTape s ++ res_in` (start)
and `T 0 = encodeTape (clear dst s) ++ (res_in ++ replicate n 0)` (end). Each
deleted cell becomes a `0` filler appended to the residue. The total step count
is bounded by `9·L²+9` where `L = |encodeTape s ++ res_in|` (every loop tape has
length `L`, each iteration is `O(L)`, and there are `≤ L` iterations). -/
theorem Compile.clearRegionTM_run (s : State) (dst : Var) (res_in : List Nat)
    (h : dst < s.length) (hbit : Compile.BitState s) (hres : Compile.ValidResidue res_in) :
    ∃ t, runFlatTM t (ClearGadget.clearRegionTM dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
      = some { state_idx := ClearGadget.clearRegionTM_exit dst,
               tapes := [([], 0, Compile.encodeTape (Op.eval (Op.clear dst) s)
                                  ++ (res_in ++ List.replicate (s.get dst).length 0))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (ClearGadget.clearRegionTM dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } = some ck →
          ck.state_idx ≠ ClearGadget.clearRegionTM_exit dst ∧
          haltingStateReached (ClearGadget.clearRegionTM dst) ck = false)
      ∧ t ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length + 9
      := by
  set n := (s.get dst).length with hn
  -- the loop's tape after `n − j` deletions of `dst`'s leading cells.
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 0, Compile.encodeTape (s.set dst ((s.get dst).drop (n - j)))
              ++ (res_in ++ List.replicate (n - j) 0)) with hTdef
  have hBstart : (ClearGadget.clearBodyRawTM dst).start = 0 := by
    show (branchComposeFlatTM _ _ _ _ _).start = 0
    rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start dst
  -- every drop of `dst`'s (bit-shaped) content keeps the state bit-shaped.
  have hbit_drop : ∀ k, Compile.BitState (s.set dst ((s.get dst).drop k)) := by
    intro k
    refine Compile.BitState_set s dst _ hbit h (fun x hx => ?_)
    have hmem : s.get dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem x (List.mem_of_mem_drop hx)
  -- all tape symbols of `T j` are `< 4`.
  have hT_lt : ∀ j x, x ∈ (T j).2.2 → x < 4 := by
    intro j x hx
    simp only [hTdef] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four _ (hbit_drop _) x hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hres x hx).1
      · rw [List.mem_replicate] at hx; omega
  have h_sym : ∀ m v, currentTapeSymbol (T m) = some v → v < (ClearGadget.clearBodyRawTM dst).sig := by
    intro m v hv
    have hsig : (ClearGadget.clearBodyRawTM dst).sig = 4 := by
      show (branchComposeFlatTM _ _ _ _ _).sig = 4
      rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig]; rfl
    rw [hsig]
    have hmem : v ∈ (T m).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_lt m v hmem
  -- **Budget bookkeeping.** Every loop tape `T j` (`j ≤ n`) has the same length
  -- `L = |encodeTape s ++ res_in|` (a delete frees a cell but adds a `0` filler),
  -- and the cleared register satisfies `n + 2 ≤ L`.
  have hTlen : ∀ j, j ≤ n →
      (T j).2.2.length = (Compile.encodeTape s ++ res_in).length := by
    intro j hj
    have hdroplen : ((s.get dst).drop (n - j)).length = j := by
      rw [List.length_drop, ← hn]; omega
    have hbal := Compile.encodeTape_set_length s dst ((s.get dst).drop (n - j)) h
    rw [hdroplen, ← hn] at hbal
    simp only [hTdef, List.length_append, List.length_replicate]
    omega
  have hnL : n + 2 ≤ (Compile.encodeTape s ++ res_in).length := by
    have hsize := State.size_set_add s dst ([] : List Nat)
    simp only [List.length_nil, Nat.add_zero] at hsize
    rw [List.length_append, Compile.encodeTape_length]
    omega
  -- done branch: at `T 0`, register `dst` is empty.
  have hdone := Compile.clearBody_done_run (s.set dst ((s.get dst).drop n)) dst
    (res_in ++ List.replicate n 0)
    (by rw [Compile.length_set s dst _ h]; exact h)
    (hbit_drop n)
    (by rw [Compile.get_set_eq s dst _ h, hn]; exact List.drop_length)
    (Compile.ValidResidue_append_replicate_zero res_in n hres)
  obtain ⟨tDone, hdr, hdt, hdb⟩ := hdone
  -- done-branch tape is `T 0` (length `L`), so its bound becomes `tDone + 1 ≤ 6·L+13`.
  have h_done_bnd : tDone + 1 ≤ 6 * (Compile.encodeTape s ++ res_in).length + 13 := by
    have hlen0 := hTlen 0 (Nat.zero_le n)
    simp only [hTdef, Nat.sub_zero] at hlen0
    rw [hlen0] at hdb
    omega
  have hT0 : T 0 = ([], 0, Compile.encodeTape (s.set dst ((s.get dst).drop n))
      ++ (res_in ++ List.replicate n 0)) := by simp only [hTdef, Nat.sub_zero]
  -- per-iteration delete: `T (j+1) → T j` for `j < n`.
  have hiter_ex : ∀ j, j < n → ∃ t,
      runFlatTM t (ClearGadget.clearBodyRawTM dst)
          { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T (j + 1)] }
        = some { state_idx := ClearGadget.clearBodyRawTM_exitLoop dst, tapes := [T j] } ∧
      (∀ k, k < t → ∀ ck,
        runFlatTM k (ClearGadget.clearBodyRawTM dst)
            { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T (j + 1)] } = some ck →
        ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitDone dst ∧
        ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitLoop dst ∧
        haltingStateReached (ClearGadget.clearBodyRawTM dst) ck = false) ∧
      t ≤ 6 * (Compile.encodeTape s ++ res_in).length + 12 := by
    intro j hj
    obtain ⟨t, hr, ht, hb⟩ := Compile.clearBody_delete_run
      (s.set dst ((s.get dst).drop (n - (j + 1)))) dst (res_in ++ List.replicate (n - (j + 1)) 0)
      (by rw [Compile.length_set s dst _ h]; exact h)
      (hbit_drop _)
      (by rw [Compile.get_set_eq s dst _ h]
          intro hc
          have hlen : ((s.get dst).drop (n - (j + 1))).length = 0 := by rw [hc]; rfl
          rw [List.length_drop] at hlen; omega)
      (Compile.ValidResidue_append_replicate_zero res_in (n - (j + 1)) hres)
    -- the input tape is `T (j+1)`, whose length is `L`; rewrite the bound to `L`.
    have hlenj := hTlen (j + 1) (by omega)
    simp only [hTdef] at hlenj
    rw [hlenj] at hb
    -- bridge the delete output to `T j`.
    have hstate_eq :
        (s.set dst ((s.get dst).drop (n - (j + 1)))).set dst
            (((s.set dst ((s.get dst).drop (n - (j + 1)))).get dst).tail)
          = s.set dst ((s.get dst).drop (n - j)) := by
      rw [Compile.get_set_eq s dst _ h, List.tail_drop, Compile.set_set s dst _ _ h,
          show n - (j + 1) + 1 = n - j from by omega]
    have hres_eq : (res_in ++ List.replicate (n - (j + 1)) 0) ++ [0]
        = res_in ++ List.replicate (n - j) 0 := by
      rw [List.append_assoc, ← List.replicate_succ', show n - (j + 1) + 1 = n - j from by omega]
    rw [hstate_eq, hres_eq] at hr
    refine ⟨t, ?_, ?_, hb⟩
    · rw [hBstart]; simp only [hTdef]; exact hr
    · rw [hBstart]; simp only [hTdef]; exact ht
  -- choose per-iteration step counts.
  set tIter : Nat → Nat := fun j => if hj : j < n then (hiter_ex j hj).choose else 0 with htIter
  have h_ne_loop : ClearGadget.clearBodyRawTM_exitDone dst ≠ ClearGadget.clearBodyRawTM_exitLoop dst := by
    show (ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindRawTM.states
          + ClearGadget.justRewindTM_exit
        ≠ (ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindTM_exit
    show _ + 19 + 1 ≠ _ + 17
    omega
  have h_done_full :
      runFlatTM tDone (ClearGadget.clearBodyRawTM dst)
          { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T 0] }
        = some { state_idx := ClearGadget.clearBodyRawTM_exitDone dst, tapes := [T 0] } ∧
      (∀ k, k < tDone → ∀ ck,
          runFlatTM k (ClearGadget.clearBodyRawTM dst)
              { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitDone dst ∧
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitLoop dst ∧
          haltingStateReached (ClearGadget.clearBodyRawTM dst) ck = false) := by
    refine ⟨?_, ?_⟩
    · rw [hBstart, hT0]; exact hdr
    · rw [hBstart, hT0]; exact hdt
  have h_iter_full : ∀ j, j < n →
      runFlatTM (tIter j) (ClearGadget.clearBodyRawTM dst)
          { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T (j + 1)] }
        = some { state_idx := ClearGadget.clearBodyRawTM_exitLoop dst, tapes := [T j] } ∧
      (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (ClearGadget.clearBodyRawTM dst)
              { state_idx := (ClearGadget.clearBodyRawTM dst).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitDone dst ∧
          ck.state_idx ≠ ClearGadget.clearBodyRawTM_exitLoop dst ∧
          haltingStateReached (ClearGadget.clearBodyRawTM dst) ck = false) := by
    intro j hj
    have hspec := (hiter_ex j hj).choose_spec
    simp only [htIter, dif_pos hj]
    exact ⟨hspec.1, hspec.2.1⟩
  -- per-iteration linear bound, extracted from the (now bound-carrying) existential.
  have h_iter_bnd : ∀ j, j < n →
      tIter j + 1 ≤ 6 * (Compile.encodeTape s ++ res_in).length + 13 := by
    intro j hj
    have hb := (hiter_ex j hj).choose_spec.2.2
    simp only [htIter, dif_pos hj]
    omega
  have hmain := loopTM_run (ClearGadget.clearBodyRawTM dst)
    (ClearGadget.clearBodyRawTM_exitDone dst) (ClearGadget.clearBodyRawTM_exitLoop dst)
    (ClearGadget.clearBodyRawTM_valid dst)
    (ClearGadget.clearBodyRawTM_exitDone_lt dst) (ClearGadget.clearBodyRawTM_exitLoop_lt dst)
    h_ne_loop T h_sym tIter tDone h_done_full n h_iter_full
  have hmain_traj := loopTM_no_early_halt (ClearGadget.clearBodyRawTM dst)
    (ClearGadget.clearBodyRawTM_exitDone dst) (ClearGadget.clearBodyRawTM_exitLoop dst)
    (ClearGadget.clearBodyRawTM_valid dst)
    (ClearGadget.clearBodyRawTM_exitDone_lt dst) (ClearGadget.clearBodyRawTM_exitLoop_lt dst)
    h_ne_loop T h_sym tIter tDone h_done_full n h_iter_full
  -- convert `T n`, `T 0`, `B.start`, `B.states` to the stated forms.
  have hTn : T n = ([], 0, Compile.encodeTape s ++ res_in) := by
    simp only [hTdef, Nat.sub_self, List.drop_zero, List.replicate_zero, List.append_nil]
    rw [Compile.set_get_self s dst h]
  rw [hBstart, hTn, hT0] at hmain
  rw [hBstart, hTn] at hmain_traj
  have hMeq : ClearGadget.clearRegionTM dst
      = loopTM (ClearGadget.clearBodyRawTM dst) (ClearGadget.clearBodyRawTM_exitDone dst)
          (ClearGadget.clearBodyRawTM_exitLoop dst) := rfl
  have hExeq : ClearGadget.clearRegionTM_exit dst = (ClearGadget.clearBodyRawTM dst).states := rfl
  have hEval : Op.eval (Op.clear dst) s = s.set dst ((s.get dst).drop n) := by
    have hdn : (s.get dst).drop n = [] := by rw [hn]; exact List.drop_length
    rw [hdn]; rfl
  refine ⟨loopBudget tIter tDone n, ?_, ?_, ?_⟩
  · rw [hMeq, hExeq, hEval]; exact hmain
  · intro k hk ck hck
    rw [hMeq] at hck
    have hh := hmain_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.opClear dst).exit_is_halt hh, hh⟩
  · -- budget: `loopBudget ≤ (n+1)·(6L+13) ≤ 9L²+9` (each tape length `L`, `n+2 ≤ L`).
    exact le_trans
      (Compile.loopBudget_le tIter tDone (6 * (Compile.encodeTape s ++ res_in).length + 13)
        n h_done_bnd h_iter_bnd)
      (Compile.clearBudget_arith n (Compile.encodeTape s ++ res_in).length hnL)

