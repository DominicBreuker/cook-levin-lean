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

set_option autoImplicit false

/-! # `Compile/RunLemmas` — per-op run/behaviour lemmas + residue toolkit (Phase 3)

Extracted from `Compile.lean` (refactor Phase 3, see `REFACTOR-HANDOFF.md`).
The op *run/behaviour* layer: every per-`Op` machine's run lemma plus the
residue-tolerant tape toolkit they are stated against. Depends on
`Compile/Cmd` (uses `compileSeq`/`compileTestBit`) + `Compile/OpMachines` +
`Compile/Encoding` + `Compile/Core`; consumed downstream by the per-op
soundness contract `compileOp_sound_physical_residue` in `Compile.lean`.

Contents (file order): the `appendOne`/`appendZero` per-op soundness; the
`ValidResidue`/`TapeOK` residue toolkit + `clear` run stack + `clearRegionTM_run`;
the move-one-bit / dual-target transfer gadgets; `compileSeq_compose_physical`;
the `compileTestBit`/`navTestReg` run lemmas; `nonEmpty`/`head` run lemmas; the
cursor-copy (`copy`) run stack; the `tail` run stack; and the `eqBit` no-grow
consume-loop run stack (ending at `opEqBitNG_run`). -/

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
private theorem Compile.appendBit_sound (bit : Nat) (hb : bit ≤ 1)
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
private theorem Compile.BitState_set_tail (s : State) (dst : Var)
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
private theorem Compile.BitState_get (s : State) (r : Var)
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

/-! ### The move-one-bit transfer gadget (Risk C2, Task 2 critical path)

`moveRegionTM src dst` transfers register `src`'s content, **one bit at a time**,
to the **end** of register `dst` (FIFO — order preserved), emptying `src`. It is
the single building block of every remaining cross-register op
(`copy`/`tail`/`eqBit`/`takeAt`/`dropAt`/`concat`/`consLen`): e.g. `copy dst src sc`
= move `src→sc` then move `sc→`(`src`&`dst`).

**Structure — mirrors `clearRegionTM` exactly, with the content branch doing a
read+append instead of a bare delete.** The loop body navigates to `src`; on the
content branch (src non-empty) it reads the front bit (`bitReadTM`), deletes that
cell and rewinds (`stepDeleteRewindRawTM`, exactly as `clear`), then appends the
bit (`+1`) to `dst` and two-phase-rewinds; on the delim branch (src empty) it just
rewinds and the loop stops.

**✅ Probe-validated end-to-end** (2026-06-05, `#eval` on real `encodeTape`s, both
`dst>src` and `dst<src`): `encodeTape [[1,0],[1]] → encodeTape [[],[1,1,0]] ++ [0,0]`
and `encodeTape [[1],[0,1]] → encodeTape [[1,0,1],[]] ++ [0,0]` (residue =
`replicate (#moved bits) 0`). The exit-state offsets below were read off the probe
and verified to make the `loopTM` continue/terminate correctly. -/

/-- Single-bit transfer engine for a fixed bit `b`: delete `src`'s front cell and
rewind (`stepDeleteRewindRawTM`), then append `b+1` to `dst` and two-phase-rewind. -/
def Compile.moveBitM2TM (b dst : Nat) : FlatTM :=
  composeFlatTM ClearGadget.stepDeleteRewindRawTM
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ClearGadget.stepDeleteRewindTM_exit

/-- The surviving (found) exit of `moveBitM2TM` (independent of `b`): the
`stepDeleteRewindRawTM` state count plus the append bracket's found exit
(`appendAtTM.states + 6`). -/
def Compile.moveBitM2_exit (dst : Nat) : Nat :=
  ClearGadget.stepDeleteRewindRawTM.states + ((AppendGadget.appendAtTM 1 dst).states + 6)

/-- Content branch (src non-empty): read the front bit, then run the matching
single-bit transfer engine. The two bit paths exit at distinct states
(`moveContentExit0`/`moveContentExit1`), merged by `joinTwoHalts` below. -/
def Compile.moveContentRawTM (dst : Nat) : FlatTM :=
  branchComposeFlatTM Compile.bitReadTM (Compile.moveBitM2TM 0 dst) (Compile.moveBitM2TM 1 dst)
    Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1

/-- Bit-0 path exit of `moveContentRawTM`. -/
def Compile.moveContentExit0 (dst : Nat) : Nat :=
  Compile.bitReadTM.states + Compile.moveBitM2_exit dst

/-- Bit-1 path exit of `moveContentRawTM` (shifted by the bit-0 engine's states). -/
def Compile.moveContentExit1 (dst : Nat) : Nat :=
  Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states + Compile.moveBitM2_exit dst

/-- Content branch with the two bit-exits merged into one (`moveContentExit0`). -/
def Compile.moveContentTM (dst : Nat) : FlatTM :=
  Compile.joinTwoHalts (Compile.moveContentRawTM dst)
    (Compile.moveContentExit0 dst) (Compile.moveContentExit1 dst)

/-- The loop body: navigate to `src`, branch content (move one bit) vs delim
(src empty → rewind & stop). -/
def Compile.moveBodyRawTM (src dst : Nat) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM src) (Compile.moveContentTM dst)
    ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content src) (ClearGadget.navigateAndTestTM_exit_delim src)

/-- The loop's "continue" exit (content branch fired: one bit moved). -/
def Compile.moveBodyRawTM_exitLoop (src dst : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + Compile.moveContentExit0 dst

/-- The loop's "done" exit (delim branch fired: src empty). -/
def Compile.moveBodyRawTM_exitDone (src dst : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
    + ClearGadget.justRewindTM_exit

/-- The full move gadget: loop the body until `src` empties. -/
def Compile.moveRegionTM (src dst : Nat) : FlatTM :=
  loopTM (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)

/-- The single halt state of `moveRegionTM` (the `loopTM` done-exit, at `B.states`). -/
def Compile.moveRegionTM_exit (src dst : Nat) : Nat := (Compile.moveBodyRawTM src dst).states

theorem Compile.moveBitM2TM_tapes (b dst : Nat) : (Compile.moveBitM2TM b dst).tapes = 1 := by
  rw [Compile.moveBitM2TM, composeFlatTM_tapes]; exact ClearGadget.stepDeleteRewindRawTM_tapes

theorem Compile.moveContentRawTM_tapes (dst : Nat) : (Compile.moveContentRawTM dst).tapes = 1 := by
  rw [Compile.moveContentRawTM, branchComposeFlatTM_tapes]; exact Compile.bitReadTM_tapes

theorem Compile.moveContentTM_tapes (dst : Nat) : (Compile.moveContentTM dst).tapes = 1 := by
  rw [Compile.moveContentTM, Compile.joinTwoHalts_tapes]; exact Compile.moveContentRawTM_tapes dst

theorem Compile.moveBodyRawTM_tapes (src dst : Nat) : (Compile.moveBodyRawTM src dst).tapes = 1 := by
  rw [Compile.moveBodyRawTM, branchComposeFlatTM_tapes]; exact ClearGadget.navigateAndTestTM_tapes src

theorem Compile.moveRegionTM_tapes (src dst : Nat) : (Compile.moveRegionTM src dst).tapes = 1 := by
  rw [Compile.moveRegionTM, loopTM_tapes]; exact Compile.moveBodyRawTM_tapes src dst

theorem Compile.moveRegionTM_start (src dst : Nat) : (Compile.moveRegionTM src dst).start = 0 := by
  show (Compile.moveBodyRawTM src dst).start = 0
  show (branchComposeFlatTM _ _ _ _ _).start = 0
  rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src

/-- The branch that reaches the **kept** exit `h1`: `joinTwoHalts` agrees with the
raw machine, reaching `h1` at step `T`; the trajectory never hits `h1` and never
halts. -/
theorem Compile.joinTwoHalts_reaches_kept (raw : FlatTM) (h1 h2 : Nat) (cfg0 : FlatTMConfig)
    (T : Nat) (tape : List Nat × Nat × List Nat)
    (hraw : runFlatTM T raw cfg0 = some { state_idx := h1, tapes := [tape] })
    (hraw_traj : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck →
        haltingStateReached raw ck = false)
    (hh1 : raw.halt[h1]? = some true) (hh2 : raw.halt[h2]? = some true) :
    runFlatTM T (joinTwoHalts raw h1 h2) cfg0 = some { state_idx := h1, tapes := [tape] } ∧
    (∀ k, k < T → ∀ ck, runFlatTM k (joinTwoHalts raw h1 h2) cfg0 = some ck →
        ck.state_idx ≠ h1 ∧ haltingStateReached (joinTwoHalts raw h1 h2) ck = false) := by
  have hnv : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck → ck.state_idx ≠ h2 :=
    fun k hk ck hck => ClearGadget.ne_of_not_halting hh2 (hraw_traj k hk ck hck)
  refine ⟨?_, ?_⟩
  · rw [joinTwoHalts_run_eq_weak raw h1 h2 T cfg0 hnv]; exact hraw
  · intro k hk ck hck
    rw [joinTwoHalts_run_eq_weak raw h1 h2 k cfg0
        (fun j hj cj hcj => hnv j (by omega) cj hcj)] at hck
    have hnh := hraw_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting hh1 hnh, Compile.joinTwoHalts_halting_false raw h1 h2 ck hnh⟩

/-- The branch that reaches the **demoted** exit `h2`: `joinTwoHalts` reaches `h2`
at step `T`, then bridges to the kept exit `h1` in one more step. -/
theorem Compile.joinTwoHalts_reaches_demoted (raw : FlatTM) (h1 h2 : Nat) (cfg0 : FlatTMConfig)
    (T : Nat) (left right : List Nat) (head : Nat)
    (hraw : runFlatTM T raw cfg0 = some { state_idx := h2, tapes := [(left, head, right)] })
    (hraw_traj : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck →
        haltingStateReached raw ck = false)
    (hh1 : raw.halt[h1]? = some true) (hh2 : raw.halt[h2]? = some true) (hne : h1 ≠ h2)
    (h_sym : ∀ v, currentTapeSymbol (left, head, right) = some v → v < raw.sig) :
    runFlatTM (T + 1) (joinTwoHalts raw h1 h2) cfg0
        = some { state_idx := h1, tapes := [(left, head, right)] } ∧
    (∀ k, k < T + 1 → ∀ ck, runFlatTM k (joinTwoHalts raw h1 h2) cfg0 = some ck →
        ck.state_idx ≠ h1 ∧ haltingStateReached (joinTwoHalts raw h1 h2) ck = false) := by
  have hnv : ∀ k, k < T → ∀ ck, runFlatTM k raw cfg0 = some ck → ck.state_idx ≠ h2 :=
    fun k hk ck hck => ClearGadget.ne_of_not_halting hh2 (hraw_traj k hk ck hck)
  have hjoinT : runFlatTM T (joinTwoHalts raw h1 h2) cfg0
      = some { state_idx := h2, tapes := [(left, head, right)] } := by
    rw [joinTwoHalts_run_eq_weak raw h1 h2 T cfg0 hnv]; exact hraw
  have hjoinHalt_h2 : haltingStateReached (joinTwoHalts raw h1 h2)
      { state_idx := h2, tapes := [(left, head, right)] } = false := by
    show (raw.halt.set h2 false).getD h2 false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl]; split <;> rfl
  have hstep : stepFlatTM (joinTwoHalts raw h1 h2)
      { state_idx := h2, tapes := [(left, head, right)] }
      = some { state_idx := h1, tapes := [(left, head, right)] } :=
    joinTwoHalts_step_to_h1 raw h1 h2 left right head h_sym
  refine ⟨?_, ?_⟩
  · rw [runFlatTM_compose (joinTwoHalts raw h1 h2) T 1 cfg0 _ hjoinT]
    show (if haltingStateReached (joinTwoHalts raw h1 h2)
              { state_idx := h2, tapes := [(left, head, right)] } = true then _
          else match stepFlatTM (joinTwoHalts raw h1 h2)
              { state_idx := h2, tapes := [(left, head, right)] } with
            | none => _ | some c => runFlatTM 0 (joinTwoHalts raw h1 h2) c) = _
    rw [if_neg (by rw [hjoinHalt_h2]; decide), hstep]
    rfl
  · intro k hk ck hck
    rcases Nat.lt_or_ge k T with hkT | hkT
    · rw [joinTwoHalts_run_eq_weak raw h1 h2 k cfg0
          (fun j hj cj hcj => hnv j (by omega) cj hcj)] at hck
      have hnh := hraw_traj k hkT ck hck
      exact ⟨ClearGadget.ne_of_not_halting hh1 hnh, Compile.joinTwoHalts_halting_false raw h1 h2 ck hnh⟩
    · have hkeq : k = T := by omega
      subst hkeq
      rw [hjoinT] at hck
      obtain rfl := (Option.some.inj hck).symm
      exact ⟨Ne.symm hne, hjoinHalt_h2⟩

/-- `appendAtTM`'s state count is independent of the inserted symbol (`ins` only
enters via `insertCarryTM ins`, whose `states` field is the constant `6`). -/
theorem Compile.appendAtTM_states_eq (ins dst : Nat) :
    (AppendGadget.appendAtTM ins dst).states = (AppendGadget.appendAtTM 1 dst).states := by
  induction dst with
  | zero => rfl
  | succ d ih =>
      rw [show AppendGadget.appendAtTM ins (d + 1)
            = composeFlatTM (ScanPast.scanPastDelimTM 4 0) (AppendGadget.appendAtTM ins d) 1 from rfl,
          show AppendGadget.appendAtTM 1 (d + 1)
            = composeFlatTM (ScanPast.scanPastDelimTM 4 0) (AppendGadget.appendAtTM 1 d) 1 from rfl,
          composeFlatTM_states, composeFlatTM_states, ih]

/-- **The single-bit transfer engine run (Risk C2, Task 2).** Run from `src`'s
content start (head `1 + |encodeRegs (s.take src)|`) with `src`'s front bit `b`
(`s.get src = b :: cs`), `moveBitM2TM b dst` deletes that front cell, rewinds,
appends `b` to the end of `dst`, and two-phase-rewinds, landing at
`moveBitM2_exit dst` with the tape
`encodeTape ((s.set src cs).set dst (s.get dst ++ [b])) ++ (res ++ [0])` and head
`0`. Composes `stepDeleteRewind_run` (on `src`) with `appendBitTwoPhase_run` (on
the deleted state, appending to `dst`). -/
theorem Compile.moveBitM2_run (s : State) (src dst : Var) (b : Nat) (cs : List Nat)
    (hb : b ≤ 1) (hsd : src ≠ dst) (hsrc : src < s.length) (hdst : dst < s.length)
    (hbit : Compile.BitState s) (hcons : s.get src = b :: cs) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBitM2TM b dst)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBitM2_exit dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBitM2TM b dst)
            { state_idx := 0,
              tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.moveBitM2TM b dst) ck = false)
    ∧ t ≤ 7 * (Compile.encodeTape s ++ res).length + 18 := by
  have hne : s.get src ≠ [] := by rw [hcons]; exact List.cons_ne_nil _ _
  have htl : (s.get src).tail = cs := by rw [hcons, List.tail_cons]
  -- Phase 1: delete src's front cell + rewind.
  obtain ⟨t1, h_sdr, h_sdr_traj, h_t1_bnd⟩ :=
    Compile.stepDeleteRewind_run s src res hsrc hbit hne hres
  rw [htl] at h_sdr
  -- Phase 2 ingredients (on the post-delete state `s.set src cs`).
  have hbit1 : Compile.BitState (s.set src cs) := by
    have := Compile.BitState_set_tail s src hbit hsrc; rwa [htl] at this
  have hlen1 : (s.set src cs).length = s.length := Compile.length_set s src cs hsrc
  have hdst1 : dst < (s.set src cs).length := by rw [hlen1]; exact hdst
  have hres1 : Compile.ValidResidue (res ++ [0]) := by
    apply Compile.ValidResidue_append _ _ hres; intro x hx
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  obtain ⟨t2, h_app, h_app_traj, h_t2_bnd⟩ :=
    Compile.appendBitTwoPhase_run b hb (s.set src cs) dst hbit1 hdst1 (res ++ [0]) hres1
  have hgetdst : (s.set src cs).get dst = s.get dst :=
    Compile.get_set_ne s src cs dst hsrc (Ne.symm hsd)
  rw [hgetdst] at h_app
  -- length balance: deleting a bit and padding the residue with `[0]` keeps the length.
  have hLbal : (Compile.encodeTape (s.set src cs) ++ (res ++ [0])).length
      = (Compile.encodeTape s ++ res).length := by
    have hbalance := Compile.encodeTape_set_length s src cs hsrc
    rw [hcons] at hbalance
    simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil]
      at hbalance ⊢
    omega
  -- M₂ start (= 0).
  have hM2start : (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).start = 0 := by
    show (composeFlatTM (AppendGadget.appendAtTM (b + 1) dst) (ScanLeft.rewindTwoPhaseTM 4 3)
          (AppendGadget.appendAtTM_exit dst)).start = 0
    rw [composeFlatTM_start, AppendGadget.appendAtTM_start]
  set right₁ : List Nat := Compile.encodeTape (s.set src cs) ++ (res ++ [0]) with hr1
  -- shared compose inputs.
  have hvalid1 : validFlatTM ClearGadget.stepDeleteRewindRawTM := ClearGadget.stepDeleteRewindRawTM_valid
  have hvalid2 : validFlatTM (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) :=
    AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst
  have hexit_lt : ClearGadget.stepDeleteRewindTM_exit < ClearGadget.stepDeleteRewindRawTM.states := by
    show (17 : Nat) < ClearGadget.stepDeleteRewindRawTM.states
    show (17 : Nat) < 19; omega
  have hcfg0lt : (0 : Nat) < ClearGadget.stepDeleteRewindRawTM.states := by
    show (0 : Nat) < 19; omega
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, right₁) = some v →
      v < max ClearGadget.stepDeleteRewindRawTM.sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).sig := by
    intro v hv
    rw [hr1, show currentTapeSymbol (([] : List Nat), 0,
          Compile.encodeTape (s.set src cs) ++ (res ++ [0])) = some 3 from rfl] at hv
    rw [show max ClearGadget.stepDeleteRewindRawTM.sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).sig = 4 from by
        rw [AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl]
    have : v = 3 := (Option.some.inj hv).symm
    omega
  -- per-component trajectory hyps with the `≠ exit` part for M₁.
  have h_traj1 : ∀ k, k < t1 → ∀ ck,
      runFlatTM k ClearGadget.stepDeleteRewindRawTM
          { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                       Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.stepDeleteRewindTM_exit ∧
      haltingStateReached ClearGadget.stepDeleteRewindRawTM ck = false := by
    intro k hk ck hck
    have hh := h_sdr_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting ClearGadget.stepDeleteRewindRawTM_halt_seventeen hh, hh⟩
  have h_app_traj' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
          { state_idx := (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst).start,
            tapes := [([], 0, right₁)] } = some ck →
      haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ck = false := by
    rw [hM2start, hr1]; exact h_app_traj
  -- h_halt2 (the M₂ exit halts).
  have h_halt2 : haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
      { state_idx := 6 + (AppendGadget.appendAtTM (b + 1) dst).states,
        tapes := [([], 0, Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                    ++ (res ++ [0]))] } = true := by
    rw [show (6 : Nat) + (AppendGadget.appendAtTM (b + 1) dst).states
          = (AppendGadget.appendAtTM (b + 1) dst).states + 6 from Nat.add_comm ..]
    exact Compile.haltingStateReached_of_halt
      (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst)
  have hmoveeq : Compile.moveBitM2TM b dst
      = composeFlatTM ClearGadget.stepDeleteRewindRawTM
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
          ClearGadget.stepDeleteRewindTM_exit := rfl
  have hstate_eq : Compile.moveBitM2_exit dst
      = (6 + (AppendGadget.appendAtTM (b + 1) dst).states)
          + ClearGadget.stepDeleteRewindRawTM.states := by
    show ClearGadget.stepDeleteRewindRawTM.states + ((AppendGadget.appendAtTM 1 dst).states + 6)
        = (6 + (AppendGadget.appendAtTM (b + 1) dst).states)
            + ClearGadget.stepDeleteRewindRawTM.states
    rw [Compile.appendAtTM_states_eq (b + 1) dst]; omega
  have hmain := composeFlatTM_run hvalid1 hvalid2 hexit_lt
    { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                 Compile.encodeTape s ++ res)] }
    hcfg0lt [] 0 right₁ hsym h_sdr h_traj1
    (by rw [hM2start]; exact h_app) h_halt2
  refine ⟨t1 + 1 + t2, ?_, ?_, ?_⟩
  · rw [hmoveeq, hstate_eq]; exact hmain.1
  · intro k hk ck hck
    rw [hmoveeq] at hck ⊢
    exact composeFlatTM_no_early_halt hvalid1 hvalid2 hexit_lt
      { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                   Compile.encodeTape s ++ res)] }
      hcfg0lt [] 0 right₁ hsym h_sdr h_traj1 h_app_traj' k hk ck hck
  · rw [hLbal] at h_t2_bnd
    omega

/-! #### `moveContent` scaffolding (the bit-read branch over the transfer engine). -/

theorem Compile.moveBitM2TM_sig (b dst : Nat) : (Compile.moveBitM2TM b dst).sig = 4 := by
  rw [Compile.moveBitM2TM, composeFlatTM_sig, AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl

theorem Compile.moveBitM2TM_valid (b dst : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.moveBitM2TM b dst) :=
  composeFlatTM_valid ClearGadget.stepDeleteRewindRawTM
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ClearGadget.stepDeleteRewindTM_exit
    ClearGadget.stepDeleteRewindRawTM_valid
    (AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst)
    (by show (17 : Nat) < ClearGadget.stepDeleteRewindRawTM.states; show (17 : Nat) < 19; omega)
    ClearGadget.stepDeleteRewindRawTM_tapes
    (AppendGadget.appendAtThenTwoPhaseRewindTM_tapes (b + 1) dst)

theorem Compile.moveBitM2_exit_is_halt (b dst : Nat) :
    (Compile.moveBitM2TM b dst).halt[Compile.moveBitM2_exit dst]? = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro ClearGadget.stepDeleteRewindRawTM
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst) ClearGadget.stepDeleteRewindTM_exit
    ((AppendGadget.appendAtTM (b + 1) dst).states + 6)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst)
  rw [Compile.appendAtTM_states_eq (b + 1) dst] at h
  exact h

theorem Compile.moveBitM2_exit_lt (b dst : Nat) :
    Compile.moveBitM2_exit dst < (Compile.moveBitM2TM b dst).states := by
  show ClearGadget.stepDeleteRewindRawTM.states + ((AppendGadget.appendAtTM 1 dst).states + 6)
      < (composeFlatTM ClearGadget.stepDeleteRewindRawTM
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
          ClearGadget.stepDeleteRewindTM_exit).states
  rw [composeFlatTM_states, AppendGadget.appendAtThenTwoPhaseRewindTM_states,
      Compile.appendAtTM_states_eq (b + 1) dst,
      show (ScanLeft.rewindTwoPhaseTM 4 3).states = 8 from rfl]
  omega

theorem Compile.moveContentRawTM_valid (dst : Nat) : validFlatTM (Compile.moveContentRawTM dst) :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.bitReadTM_valid
    (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide)
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide)
    Compile.bitReadTM_tapes (Compile.moveBitM2TM_tapes 0 dst) (Compile.moveBitM2TM_tapes 1 dst)

theorem Compile.moveContentRawTM_sig (dst : Nat) : (Compile.moveContentRawTM dst).sig = 4 := by
  rw [Compile.moveContentRawTM, branchComposeFlatTM_sig, Compile.bitReadTM_sig,
      Compile.moveBitM2TM_sig 0 dst, Compile.moveBitM2TM_sig 1 dst]; rfl

theorem Compile.moveContentExit0_is_halt (dst : Nat) :
    (Compile.moveContentRawTM dst).halt[Compile.moveContentExit0 dst]? = some true := by
  rw [Compile.moveContentExit0, Compile.moveContentRawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2_exit_lt 0 dst)
    (Compile.moveBitM2_exit_is_halt 0 dst)

theorem Compile.moveContentExit1_is_halt (dst : Nat) :
    (Compile.moveContentRawTM dst).halt[Compile.moveContentExit1 dst]? = some true := by
  rw [Compile.moveContentExit1, Compile.moveContentRawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2_exit_is_halt 1 dst)

theorem Compile.moveContentExit0_ne_exit1 (dst : Nat) :
    Compile.moveContentExit0 dst ≠ Compile.moveContentExit1 dst := by
  show Compile.bitReadTM.states + Compile.moveBitM2_exit dst
      ≠ Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states + Compile.moveBitM2_exit dst
  have h0 : 0 < (Compile.moveBitM2TM 0 dst).states := by
    have := Compile.moveBitM2_exit_lt 0 dst; omega
  omega

/-- **The content-branch run (Risk C2, Task 2).** Run from `src`'s content start
(head `H = 1 + |regBlocks (map shiftReg (s.take src))|`) with front bit `b`
(`s.get src = b :: cs`), `moveContentTM dst` reads the bit and runs the matching
single-bit transfer, the two bit-paths merging through `joinTwoHalts` into
`moveContentExit0 dst`. The tape becomes
`encodeTape ((s.set src cs).set dst (s.get dst ++ [b])) ++ (res ++ [0])`. Mirrors
`opInnerBit_run`. -/
theorem Compile.moveContent_run (s : State) (src dst : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd : src ≠ dst)
    (hbit : Compile.BitState s) (hsrc : src < s.length) (hdst : dst < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveContentTM dst)
        { state_idx := 0,
          tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveContentExit0 dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveContentTM dst)
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.moveContentExit0 dst ∧
        haltingStateReached (Compile.moveContentTM dst) ck = false)
    ∧ t ≤ 7 * (Compile.encodeTape s ++ res).length + 21 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.moveContentRawTM dst with hrawdef
  set h1 := Compile.moveContentExit0 dst with hh1def
  set h2 := Compile.moveContentExit1 dst with hh2def
  have hraweq : branchComposeFlatTM Compile.bitReadTM
      (Compile.moveBitM2TM 0 dst) (Compile.moveBitM2TM 1 dst)
      Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1 = raw := rfl
  have hMeq : Compile.moveContentTM dst = joinTwoHalts raw h1 h2 := rfl
  rw [hMeq]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hHeq : (1 : Nat) + (Compile.encodeRegs (s.take src)).length = H := by
    rw [hHdef, hskdef, Compile.regBlocks_map_shiftReg]
  -- length facts.
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  -- content decomposition (`src` nonempty).
  set tail' := Compile.shiftReg cs ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src hsrc
    rw [← hskdef] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg cs := by
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
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max Compile.bitReadTM.sig
          (max (Compile.moveBitM2TM 0 dst).sig (Compile.moveBitM2TM 1 dst).sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    rw [Compile.bitReadTM_sig]
    have : v < 4 := by have : v = b + 1 := (Option.some.inj hv).symm; omega
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < Compile.bitReadTM.states := by rw [Compile.bitReadTM_states]; omega
  have hexit_neq : Compile.bitReadTM_exit_b0 ≠ Compile.bitReadTM_exit_b1 := by decide
  have hep_lt : Compile.bitReadTM_exit_b0 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide
  have hen_lt : Compile.bitReadTM_exit_b1 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide
  have hh1_is := Compile.moveContentExit0_is_halt dst
  have hh2_is := Compile.moveContentExit1_is_halt dst
  have hh_ne := Compile.moveContentExit0_ne_exit1 dst
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  have htest_run := Compile.bitReadTM_run b hb [] (Compile.encodeTape s ++ res) H hHlt hcellH
  have htest_traj : ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.bitReadTM cfg0 = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧ ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧
      haltingStateReached Compile.bitReadTM ck = false := by
    intro k hk ck hck
    exact Compile.bitReadTM_no_early_halt [] (Compile.encodeTape s ++ res) H k hk ck hck
  interval_cases b
  · -- bit 0 (cell value 1): pos branch, transfer engine for bit 0; kept exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM2_run s src dst 0 cs (by omega) hsd hsrc hdst hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM2_exit_is_halt 0 dst))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM2_exit dst + Compile.bitReadTM.states = h1 := by
      rw [hh1def]; show Compile.moveBitM2_exit dst + Compile.bitReadTM.states
        = Compile.bitReadTM.states + Compile.moveBitM2_exit dst
      omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [0])) ++ (res ++ [0]))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega
  · -- bit 1 (cell value 2): neg branch, transfer engine for bit 1; demoted exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM2_run s src dst 1 cs (by omega) hsd hsrc hdst hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM2_exit_is_halt 1 dst))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM2TM_valid 0 dst (by decide)) (Compile.moveBitM2TM_valid 1 dst (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM2_exit dst
        + (Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states) = h2 := by
      rw [hh2def]; show Compile.moveBitM2_exit dst
          + (Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states)
        = Compile.bitReadTM.states + (Compile.moveBitM2TM 0 dst).states + Compile.moveBitM2_exit dst
      omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [1])) ++ (res ++ [0])) 0
      hneg.1 (fun k hk ck hck => hneg_traj k hk ck hck) hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [1])) ++ (res ++ [0]))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.moveContentRawTM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega

/-! ### Residue-tolerant `navigateAndTest` reading (Class-A cross-register ops)

The Class-A cross-register ops (`nonEmpty`/`head`/`eqBit`: ≤ 1-cell output) all
start by reading register `src`'s first tape cell and branching. `ClearGadget`'s
`navigateAndTestTM_run_content`/`_run_delim` do exactly this, but are stated on a
clean tape `3 :: (regBlocks skipped ++ v :: tail')`. The lemmas below lift them to
the residue-tolerant `encodeTape s ++ res` shape (the input every compiled
fragment actually sees): register `src`'s slot sits between the leading sentinel
and the trailing terminator, so the residue (past the terminator) is irrelevant
to the read. The exit head lands on `src`'s first cell at index
`1 + |regBlocks (preceding registers)|`; the **content** exit means `src` is
non-empty (answer bit `1`), the **delim** exit means `src` is empty (answer bit
`0`). Reusable by every Class-A op. -/

/-- Helper bridge: `s.take src` mapped through `shiftReg` has length `src`. -/
private theorem Compile.skipped_length (s : State) (src : Var) (h : src < s.length) :
    ((s.take src).map Compile.shiftReg).length = src := by
  rw [List.length_map, List.length_take, Nat.min_eq_left (le_of_lt h)]

/-- The `h_skip` precondition: every preceding register block (`shiftReg` of a
`BitState` register) is delimiter-free and `< 4`. -/
private theorem Compile.skipped_ok (s : State) (src : Var) (hbit : Compile.BitState s) :
    ∀ b' ∈ (s.take src).map Compile.shiftReg, (∀ x ∈ b', x ≠ 0) ∧ (∀ x ∈ b', x < 4) := by
  intro b' hb'
  rw [List.mem_map] at hb'
  obtain ⟨reg, hreg, rfl⟩ := hb'
  have hregs : reg ∈ s := List.mem_of_mem_take hreg
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; omega
  · intro x hx
    rw [Compile.shiftReg, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hbit reg hregs y hy; omega

/-- **Residue-tolerant `navigateAndTest` — content branch (`src` non-empty).** -/
theorem Compile.navTestReg_run_content (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hne : s.get src ≠ []) :
    runFlatTM (ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1)
        (ClearGadget.navigateAndTestTM src)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_content src,
               tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                          Compile.encodeTape s ++ res)] } := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  obtain ⟨b, r, hbr⟩ : ∃ b r, s.get src = b :: r := by
    cases hsr : s.get src with
    | nil => exact absurd hsr hne
    | cons b r => exact ⟨b, r, rfl⟩
  have hb1 : b ≤ 1 := by
    have hmem : s.get src ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem b (by simp [hbr])
  set tail' := Compile.shiftReg r ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg r := by
      rw [hbr]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hcontent := ClearGadget.navigateAndTestTM_run_content skipped (b + 1) tail'
    (Compile.skipped_ok s src hbit) (by omega) (by omega)
  rw [hskiplen] at hcontent
  rw [← hdecomp] at hcontent
  exact hcontent

/-- **Residue-tolerant `navigateAndTest` — delim branch (`src` empty).** -/
theorem Compile.navTestReg_run_delim (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = []) :
    runFlatTM (ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1)
        (ClearGadget.navigateAndTestTM src)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim src,
               tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                          Compile.encodeTape s ++ res)] } := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  set tail' := Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = [] := by
      rw [hempty]; rfl
    rw [hsr, List.append_nil] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hdelim := ClearGadget.navigateAndTestTM_run_delim skipped tail'
    (Compile.skipped_ok s src hbit)
  rw [hskiplen] at hdelim
  rw [← hdecomp] at hdelim
  exact hdelim

/-- Navtest no-early-halt trajectory (avoids *both* exits), content branch. -/
theorem Compile.navTestReg_traj_content (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hne : s.get src ≠ []) :
    ∀ k, k < ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  obtain ⟨b, r, hbr⟩ : ∃ b r, s.get src = b :: r := by
    cases hsr : s.get src with
    | nil => exact absurd hsr hne
    | cons b r => exact ⟨b, r, rfl⟩
  have hb1 : b ≤ 1 := by
    have hmem : s.get src ∈ s := by
      rw [State.get, List.getElem?_eq_getElem h]; exact List.getElem_mem h
    exact hbit _ hmem b (by simp [hbr])
  set tail' := Compile.shiftReg r ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg r := by
      rw [hbr]; simp only [Compile.shiftReg, List.map_cons]
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  intro k hk ck hck
  have hsk_eq : ClearGadget.navigateAndTestTM src = ClearGadget.navigateAndTestTM skipped.length := by
    rw [hskiplen]
  rw [hsk_eq, hdecomp] at hck
  have hh := ClearGadget.navigateAndTestTM_no_early_halt skipped (b + 1) tail'
    (Compile.skipped_ok s src hbit) (by omega) k hk ck hck
  rw [← hsk_eq] at hh
  exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
         ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh, hh⟩

/-- Navtest no-early-halt trajectory (avoids *both* exits), delim branch. -/
theorem Compile.navTestReg_traj_delim (s : State) (src : Var) (res : List Nat)
    (h : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = []) :
    ∀ k, k < ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
  set skipped := (s.take src).map Compile.shiftReg with hsk
  have hskiplen : skipped.length = src := Compile.skipped_length s src h
  set tail' := Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ 0 :: tail') := by
    have hsplit := Compile.encodeTape_split s src h
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get src) = [] := by rw [hempty]; rfl
    rw [hsr, List.append_nil] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, htail]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  intro k hk ck hck
  have hsk_eq : ClearGadget.navigateAndTestTM src = ClearGadget.navigateAndTestTM skipped.length := by
    rw [hskiplen]
  rw [hsk_eq, hdecomp] at hck
  have hh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail'
    (Compile.skipped_ok s src hbit) (by omega) k hk ck hck
  rw [← hsk_eq] at hh
  exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
         ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh, hh⟩

/-! #### `compileTestBit` run lemmas (Risk C2, bottom-up Task 2)

The micro-steps of `exactOneOneTM`, the inner-tester composition, the raw
three-leaf tester, and the two packaged contracts `Compile.testBitReg_run_pos` /
`Compile.testBitReg_run_neg` that the `compileIfBit` residue combinator consumes:
the tester reaches `exitPos` iff `s.get t = [1]`, with the head back at `0` and
the tape **unchanged** (the branch bodies then start from their own
`initFlatConfig`). -/

/-- `exactOneOneTM` step, state 0 on a `1` cell (bit 0): → NEG, stay. -/
private theorem Compile.exactOneOne_step0_b0 (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 1) :
    stepFlatTM Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 2, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym' : cfg.tapes.map currentTapeSymbol = [some 1] := by
    show [currentTapeSymbol (left, head, right)] = [some 1]
    rw [currentTapeSymbol_in_range h, hget]
  show Option.bind (Compile.exactOneOneTM.trans.find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
  have hMatch : entryMatchesConfig
      { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
    show ((0 : Nat) == cfg.state_idx &&
        decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
    rw [hSym']; rfl
  rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
        = some { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
                 dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
    show List.find? _ (_ :: _) = _
    rw [List.find?_cons, hMatch]]
  rfl

/-- `exactOneOneTM` step, state 0 on a `2` cell (bit 1): → state 1, right. -/
private theorem Compile.exactOneOne_step0_b1 (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 2) :
    stepFlatTM Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 0, tapes := [(left, head, right)] }
  have hSym' : cfg.tapes.map currentTapeSymbol = [some 2] := by
    show [currentTapeSymbol (left, head, right)] = [some 2]
    rw [currentTapeSymbol_in_range h, hget]
  show Option.bind (Compile.exactOneOneTM.trans.find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
  have hNo : entryMatchesConfig
      { src_state := 0, src_tape_vals := [some 1], dst_state := 2,
        dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
    show ((0 : Nat) == cfg.state_idx &&
        decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
    rw [hSym']
    have h_ne : ([some 1] : List (Option Nat)) ≠ [some 2] := by decide
    simp [h_ne]
  have hMatch : entryMatchesConfig
      { src_state := 0, src_tape_vals := [some 2], dst_state := 1,
        dst_write_vals := [none], move_dirs := [TMMove.Rmove] } cfg = true := by
    show ((0 : Nat) == cfg.state_idx &&
        decide (([some 2] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
    rw [hSym']; rfl
  rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
        = some { src_state := 0, src_tape_vals := [some 2], dst_state := 1,
                 dst_write_vals := [none], move_dirs := [TMMove.Rmove] } from by
    show List.find? _ (_ :: _ :: _) = _
    rw [List.find?_cons, hNo, List.find?_cons, hMatch]]
  rfl

/-- `exactOneOneTM` step, state 1 on a cell `v ∈ {0, 1, 2}` (the block-end `0`
→ POS = 3; a bit cell → NEG = 2): stay. -/
private theorem Compile.exactOneOne_step1 (left right : List Nat) (head : Nat) (v : Nat)
    (hv : v ≤ 2) (h : head < right.length) (hget : right.get ⟨head, h⟩ = v) :
    stepFlatTM Compile.exactOneOneTM { state_idx := 1, tapes := [(left, head, right)] }
      = some { state_idx := if v = 0 then 3 else 2, tapes := [(left, head, right)] } := by
  set cfg : FlatTMConfig := { state_idx := 1, tapes := [(left, head, right)] }
  have hSym' : cfg.tapes.map currentTapeSymbol = [some v] := by
    show [currentTapeSymbol (left, head, right)] = [some v]
    rw [currentTapeSymbol_in_range h, hget]
  have hNo0 : ∀ (sv : List (Option Nat)) (d : Nat) (w : List (Option Nat)) (m : List TMMove),
      entryMatchesConfig
        { src_state := 0, src_tape_vals := sv, dst_state := d,
          dst_write_vals := w, move_dirs := m } cfg = false := by
    intro sv d w m
    show ((0 : Nat) == cfg.state_idx && _) = false
    rfl
  show Option.bind (Compile.exactOneOneTM.trans.find?
        (fun entry => entryMatchesConfig entry cfg)) (applyTransitionEntry cfg) = _
  interval_cases v
  · have hMatch : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 0] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
          = some { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
                   dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
      show List.find? _ (_ :: _ :: _ :: _) = _
      rw [List.find?_cons, hNo0, List.find?_cons, hNo0, List.find?_cons, hMatch]]
    rfl
  · have hNo2 : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 0] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
      rw [hSym']
      have h_ne : ([some 0] : List (Option Nat)) ≠ [some 1] := by decide
      simp [h_ne]
    have hMatch : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
          = some { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
                   dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
      show List.find? _ (_ :: _ :: _ :: _ :: _) = _
      rw [List.find?_cons, hNo0, List.find?_cons, hNo0, List.find?_cons, hNo2,
          List.find?_cons, hMatch]]
    rfl
  · have hNo2 : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 0], dst_state := 3,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 0] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
      rw [hSym']
      have h_ne : ([some 0] : List (Option Nat)) ≠ [some 2] := by decide
      simp [h_ne]
    have hNo3 : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 1], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = false := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 1] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = false
      rw [hSym']
      have h_ne : ([some 1] : List (Option Nat)) ≠ [some 2] := by decide
      simp [h_ne]
    have hMatch : entryMatchesConfig
        { src_state := 1, src_tape_vals := [some 2], dst_state := 2,
          dst_write_vals := [none], move_dirs := [TMMove.Nmove] } cfg = true := by
      show ((1 : Nat) == cfg.state_idx &&
          decide (([some 2] : List (Option Nat)) = cfg.tapes.map currentTapeSymbol)) = true
      rw [hSym']; rfl
    rw [show Compile.exactOneOneTM.trans.find? (fun entry => entryMatchesConfig entry cfg)
          = some { src_state := 1, src_tape_vals := [some 2], dst_state := 2,
                   dst_write_vals := [none], move_dirs := [TMMove.Nmove] } from by
      show List.find? _ (_ :: _ :: _ :: _ :: _) = _
      rw [List.find?_cons, hNo0, List.find?_cons, hNo0, List.find?_cons, hNo2,
          List.find?_cons, hNo3, List.find?_cons, hMatch]]
    rfl

/-- States `0`/`1` of `exactOneOneTM` are not halting. -/
private theorem Compile.exactOneOne_not_halting (tapes : List (List Nat × Nat × List Nat))
    (i : Nat) (hi : i ≤ 1) :
    haltingStateReached Compile.exactOneOneTM { state_idx := i, tapes := tapes } = false := by
  interval_cases i <;> rfl

/-- `exactOneOneTM` run, NEG via bit `0` first cell: 1 step. -/
private theorem Compile.exactOneOne_run_b0 (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 1) :
    runFlatTM 1 Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 2, tapes := [(left, head, right)] } := by
  show (if haltingStateReached Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.exactOneOneTM cfg') = _
  rw [show haltingStateReached Compile.exactOneOneTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.exactOneOne_step0_b0 left right head h hget]
  rfl

/-- `exactOneOneTM` run, two-cell read (`2` then `v ≤ 2`): 2 steps, head `+1`;
exit POS (`3`) iff the second cell is the block-end `0`. -/
private theorem Compile.exactOneOne_run_two (left right : List Nat) (head : Nat) (v : Nat)
    (hv : v ≤ 2) (h : head < right.length) (hget : right.get ⟨head, h⟩ = 2)
    (h1 : head + 1 < right.length) (hget1 : right.get ⟨head + 1, h1⟩ = v) :
    runFlatTM 2 Compile.exactOneOneTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := if v = 0 then 3 else 2,
               tapes := [(left, head + 1, right)] } := by
  show (if haltingStateReached Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 1 Compile.exactOneOneTM cfg') = _
  rw [show haltingStateReached Compile.exactOneOneTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.exactOneOne_step0_b1 left right head h hget]
  show (if haltingStateReached Compile.exactOneOneTM
            { state_idx := 1, tapes := [(left, head + 1, right)] } = true then _
        else match stepFlatTM Compile.exactOneOneTM
            { state_idx := 1, tapes := [(left, head + 1, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.exactOneOneTM cfg') = _
  rw [show haltingStateReached Compile.exactOneOneTM
        { state_idx := 1, tapes := [(left, head + 1, right)] } = false from rfl,
      Compile.exactOneOne_step1 left right (head + 1) v hv h1 hget1]
  rfl

/-- `exactOneOneTM` 1-step trajectory (avoids both exits, non-halting). -/
private theorem Compile.exactOneOne_traj_one (left right : List Nat) (head : Nat) :
    ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.exactOneOneTM
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ Compile.exactOneOneTM_exitPos ∧
      ck.state_idx ≠ Compile.exactOneOneTM_exitNeg ∧
      haltingStateReached Compile.exactOneOneTM ck = false := by
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  obtain rfl : ck = { state_idx := 0, tapes := [(left, head, right)] } :=
    (Option.some.inj hck).symm
  exact ⟨show (0 : Nat) ≠ 3 by omega, show (0 : Nat) ≠ 2 by omega, rfl⟩

/-- `exactOneOneTM` 2-step trajectory (avoids both exits, non-halting). -/
private theorem Compile.exactOneOne_traj_two (left right : List Nat) (head : Nat)
    (h : head < right.length) (hget : right.get ⟨head, h⟩ = 2) :
    ∀ k, k < 2 → ∀ ck,
      runFlatTM k Compile.exactOneOneTM
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ Compile.exactOneOneTM_exitPos ∧
      ck.state_idx ≠ Compile.exactOneOneTM_exitNeg ∧
      haltingStateReached Compile.exactOneOneTM ck = false := by
  intro k hk ck hck
  interval_cases k
  · obtain rfl : ck = { state_idx := 0, tapes := [(left, head, right)] } :=
      (Option.some.inj hck).symm
    exact ⟨show (0 : Nat) ≠ 3 by omega, show (0 : Nat) ≠ 2 by omega, rfl⟩
  · have hrun1 : runFlatTM 1 Compile.exactOneOneTM
        { state_idx := 0, tapes := [(left, head, right)] }
          = some { state_idx := 1, tapes := [(left, head + 1, right)] } := by
      show (if haltingStateReached Compile.exactOneOneTM
                { state_idx := 0, tapes := [(left, head, right)] } = true then _
            else match stepFlatTM Compile.exactOneOneTM
                { state_idx := 0, tapes := [(left, head, right)] } with
              | none => _ | some cfg' => runFlatTM 0 Compile.exactOneOneTM cfg') = _
      rw [show haltingStateReached Compile.exactOneOneTM
            { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
          Compile.exactOneOne_step0_b1 left right head h hget]
      rfl
    rw [hrun1] at hck
    obtain rfl : ck = { state_idx := 1, tapes := [(left, head + 1, right)] } :=
      (Option.some.inj hck).symm
    exact ⟨show (1 : Nat) ≠ 3 by omega, show (1 : Nat) ≠ 2 by omega, rfl⟩

/-- The `testBitInnerTM` symbol bound at the branch seam: any read cell value
`< 4` is below the composed alphabet. -/
private theorem Compile.testBitInner_sym_bound (left rest : List Nat) (head : Nat)
    (hlt : head < (3 :: rest).length) (v0 : Nat) (hv0 : v0 < 4)
    (hget : (3 :: rest).get ⟨head, hlt⟩ = v0) :
    ∀ v, currentTapeSymbol (left, head, (3 : Nat) :: rest) = some v →
      v < max Compile.exactOneOneTM.sig
        (max ClearGadget.justRewindTM.sig ClearGadget.justRewindTM.sig) := by
  intro v hv
  rw [currentTapeSymbol_in_range hlt, hget] at hv
  obtain rfl : v0 = v := Option.some.inj hv
  calc v0 < 4 := hv0
    _ = Compile.exactOneOneTM.sig := Compile.exactOneOneTM_sig.symm
    _ ≤ _ := le_max_left _ _

/-- Inner tester, NEG via first bit `0` (cell `1`): rewinds and exits at
`testBitInner_exitNeg` in `1 + 1 + (head + 1)` steps, tape unchanged. -/
private theorem Compile.testBitInner_run_b0 (left rest : List Nat) (head : Nat)
    (hcell : (3 :: rest)[head]? = some 1)
    (hcells : ∀ i, i < head → ∃ (hh : i < rest.length),
      rest.get ⟨i, hh⟩ < 4 ∧ rest.get ⟨i, hh⟩ ≠ 3) :
    runFlatTM (1 + 1 + (head + 1)) Compile.testBitInnerTM
        { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
      = some { state_idx := Compile.testBitInner_exitNeg,
               tapes := [(left, 0, 3 :: rest)] }
    ∧ ∀ k, k < 1 + 1 + (head + 1) → ∀ ck,
        runFlatTM k Compile.testBitInnerTM
            { state_idx := 0, tapes := [(left, head, 3 :: rest)] } = some ck →
        ck.state_idx ≠ Compile.testBitInner_exitPos ∧
        ck.state_idx ≠ Compile.testBitInner_exitNeg ∧
        haltingStateReached Compile.testBitInnerTM ck = false := by
  have hlt : head < (3 :: rest).length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hcell
    exact absurd hcell (by simp)
  have hget : (3 :: rest).get ⟨head, hlt⟩ = 1 := by
    rw [List.get_eq_getElem]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hcell)
  have hle : head ≤ rest.length := by
    simp only [List.length_cons] at hlt; omega
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
  have hrun1 := Compile.exactOneOne_run_b0 left (3 :: rest) head hlt hget
  have htraj1 := Compile.exactOneOne_traj_one left (3 :: rest) head
  have hrew := ScanLeft.rewindToStart_run 4 3 left rest head hle hcells
  have hrew_traj := ScanLeft.rewindToStart_traj 4 3 left rest head hle hcells
  have hsym := Compile.testBitInner_sym_bound left rest head hlt 1 (by omega) hget
  have hneg := branchComposeFlatTM_run_neg (by decide)
    Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
    ClearGadget.justRewindTM_valid (by decide) (by decide)
    cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left head (3 :: rest) hsym hrun1 htraj1 hrew
    (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
  have hneg_traj := branchComposeFlatTM_no_early_halt_neg (by decide)
    Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
    ClearGadget.justRewindTM_valid (by decide) (by decide)
    cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left head (3 :: rest) hsym hrun1 htraj1
    (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
  refine ⟨hneg.1, ?_⟩
  intro k hk ck hck
  have hh := hneg_traj k hk ck hck
  exact ⟨ClearGadget.ne_of_not_halting Compile.testBitInner_exitPos_is_halt hh,
         ClearGadget.ne_of_not_halting Compile.testBitInner_exitNeg_is_halt hh, hh⟩

/-- Inner tester, two-cell read (`2` then `v`): POS (`v = 0`, register `= [1]`)
or NEG (`v ∈ {1,2}`), rewinding from `head + 1`; `2 + 1 + (head + 1 + 1)` steps. -/
private theorem Compile.testBitInner_run_two (left rest : List Nat) (head : Nat) (v : Nat)
    (hv : v ≤ 2)
    (hcell : (3 :: rest)[head]? = some 2)
    (hcell1 : (3 :: rest)[head + 1]? = some v)
    (hcells : ∀ i, i < head + 1 → ∃ (hh : i < rest.length),
      rest.get ⟨i, hh⟩ < 4 ∧ rest.get ⟨i, hh⟩ ≠ 3) :
    runFlatTM (2 + 1 + (head + 1 + 1)) Compile.testBitInnerTM
        { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
      = some { state_idx := if v = 0 then Compile.testBitInner_exitPos
                            else Compile.testBitInner_exitNeg,
               tapes := [(left, 0, 3 :: rest)] }
    ∧ ∀ k, k < 2 + 1 + (head + 1 + 1) → ∀ ck,
        runFlatTM k Compile.testBitInnerTM
            { state_idx := 0, tapes := [(left, head, 3 :: rest)] } = some ck →
        ck.state_idx ≠ Compile.testBitInner_exitPos ∧
        ck.state_idx ≠ Compile.testBitInner_exitNeg ∧
        haltingStateReached Compile.testBitInnerTM ck = false := by
  have hlt1 : head + 1 < (3 :: rest).length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hcell1
    exact absurd hcell1 (by simp)
  have hlt : head < (3 :: rest).length := by omega
  have hget : (3 :: rest).get ⟨head, hlt⟩ = 2 := by
    rw [List.get_eq_getElem]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hcell)
  have hget1 : (3 :: rest).get ⟨head + 1, hlt1⟩ = v := by
    rw [List.get_eq_getElem]
    exact Option.some.inj ((List.getElem?_eq_getElem hlt1).symm.trans hcell1)
  have hle1 : head + 1 ≤ rest.length := by
    simp only [List.length_cons] at hlt1; omega
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [(left, head, 3 :: rest)] }
  have hrun1 := Compile.exactOneOne_run_two left (3 :: rest) head v hv hlt hget hlt1 hget1
  have htraj1 := Compile.exactOneOne_traj_two left (3 :: rest) head hlt hget
  have hrew := ScanLeft.rewindToStart_run 4 3 left rest (head + 1) hle1 hcells
  have hrew_traj := ScanLeft.rewindToStart_traj 4 3 left rest (head + 1) hle1 hcells
  have hsym := Compile.testBitInner_sym_bound left rest (head + 1) hlt1 v (by omega) hget1
  by_cases hv0 : v = 0
  · subst hv0
    rw [if_pos rfl] at hrun1 ⊢
    have hpos := branchComposeFlatTM_run_pos (by decide)
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1 hrew
      (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1
      (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
    refine ⟨hpos.1, ?_⟩
    intro k hk ck hck
    have hh := hpos_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting Compile.testBitInner_exitPos_is_halt hh,
           ClearGadget.ne_of_not_halting Compile.testBitInner_exitNeg_is_halt hh, hh⟩
  · rw [if_neg hv0] at hrun1 ⊢
    have hneg := branchComposeFlatTM_run_neg (by decide)
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1 hrew
      (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg (by decide)
      Compile.exactOneOneTM_valid ClearGadget.justRewindTM_valid
      ClearGadget.justRewindTM_valid (by decide) (by decide)
      cfg0 (show (0 : Nat) < Compile.exactOneOneTM.states by decide) left (head + 1) (3 :: rest) hsym hrun1 htraj1
      (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
    refine ⟨hneg.1, ?_⟩
    intro k hk ck hck
    have hh := hneg_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting Compile.testBitInner_exitPos_is_halt hh,
           ClearGadget.ne_of_not_halting Compile.testBitInner_exitNeg_is_halt hh, hh⟩

/-- Interior-cell facts for the tester rewinds: with `encodeTape s ++ res
= 3 :: rest` and `bound + 1 < |encodeTape s|`, every `rest` cell below `bound`
is in range, `< 4` and sentinel-free (it lies strictly inside the encoded
region, left of the trailing terminator). -/
private theorem Compile.testBit_rewind_cells (s : State) (res : List Nat)
    (hbit : Compile.BitState s) (rest : List Nat)
    (hrest : Compile.encodeTape s ++ res = 3 :: rest) (bound : Nat)
    (hbound : bound + 1 < (Compile.encodeTape s).length) :
    ∀ i, i < bound → ∃ (hh : i < rest.length),
      rest.get ⟨i, hh⟩ < 4 ∧ rest.get ⟨i, hh⟩ ≠ 3 := by
  intro i hi
  have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
    have h := congrArg List.length hrest
    simp only [List.length_append, List.length_cons] at h
    omega
  have hh : i < rest.length := by omega
  refine ⟨hh, ?_⟩
  have hi1lt : i + 1 < (Compile.encodeTape s).length := by omega
  have hgetE : rest.get ⟨i, hh⟩ = (Compile.encodeTape s).get ⟨i + 1, hi1lt⟩ := by
    have h1 : (3 :: rest)[i + 1]? = some (rest.get ⟨i, hh⟩) := by
      rw [List.getElem?_cons_succ, List.getElem?_eq_getElem hh, List.get_eq_getElem]
    have h2 : (Compile.encodeTape s ++ res)[i + 1]?
        = some ((Compile.encodeTape s).get ⟨i + 1, hi1lt⟩) := by
      rw [List.getElem?_append_left hi1lt, List.getElem?_eq_getElem hi1lt,
          List.get_eq_getElem]
    rw [hrest] at h2
    exact Option.some.inj (h1.symm.trans h2)
  constructor
  · rw [hgetE]
    exact Compile.encodeTape_lt_four s hbit _ (List.get_mem _ _)
  · rw [hgetE]
    obtain ⟨hi', hne⟩ :=
      Compile.encodeTape_interior_ne_endMark s hbit (i + 1) (by omega) (by omega)
    exact hne

/-- The head-`0` seam symbol of the joined tester is the leading sentinel `3`,
below the raw tester's alphabet. -/
private theorem Compile.testBitRaw_seam_sym (t : Var) (s : State) (res rest : List Nat)
    (hrest : Compile.encodeTape s ++ res = 3 :: rest) :
    ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < (Compile.testBitRawTM t).sig := by
  intro v hv
  rw [hrest] at hv
  rw [show currentTapeSymbol (([] : List Nat), 0, (3 : Nat) :: rest) = some 3 from rfl] at hv
  obtain rfl : (3 : Nat) = v := Option.some.inj hv
  rw [Compile.testBitRawTM_sig]
  omega

/-- **Tester contract — positive (`s.get t = [1]`).** `compileTestBit t` reaches
`exitPos` with the head back at `0` and the tape **unchanged**, visiting neither
exit nor any halt state before; within `3·L + 12` steps. -/
theorem Compile.testBitReg_run_pos (t : Var) (s : State) (res : List Nat)
    (ht : t < s.length) (hbit : Compile.BitState s) (hpos : s.get t = [1]) :
    ∃ T, runFlatTM T (compileTestBit t).M
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := (compileTestBit t).exitPos,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < T → ∀ ck,
        runFlatTM k (compileTestBit t).M
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ (compileTestBit t).exitPos ∧
        ck.state_idx ≠ (compileTestBit t).exitNeg ∧
        haltingStateReached (compileTestBit t).M ck = false)
    ∧ T ≤ 3 * (Compile.encodeTape s ++ res).length + 12 := by
  set skipped := (s.take t).map Compile.shiftReg with hsk
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set tail2 := Compile.encodeRegs (s.drop (t + 1)) ++ [Compile.endMark] ++ res with htail2
  set rest := AppendGadget.regBlocks skipped ++ 2 :: 0 :: tail2 with hrest_def
  have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
    have hsplit := Compile.encodeTape_split s t ht
    rw [← hsk] at hsplit
    have hsr : Compile.shiftReg (s.get t) = [2] := by rw [hpos]; rfl
    rw [hsr] at hsplit
    rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htail2]
    simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
  -- cell facts at H and H + 1.
  have hcell : (3 :: rest)[H]? = some 2 := by
    rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
          = (AppendGadget.regBlocks skipped).length + 1 from by omega,
        List.getElem?_cons_succ, hrest_def,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hcell1 : (3 :: rest)[H + 1]? = some 0 := by
    rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length + 1
          = ((AppendGadget.regBlocks skipped).length + 1) + 1 from by omega,
        List.getElem?_cons_succ, hrest_def,
        List.getElem?_append_right (Nat.le_succ_of_le (Nat.le_refl _)),
        show (AppendGadget.regBlocks skipped).length + 1
          - (AppendGadget.regBlocks skipped).length = 1 from by omega]
    rfl
  -- length bookkeeping.
  have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
    have h := congrArg List.length hdecomp
    simp only [List.length_append, List.length_cons] at h
    omega
  have hrest_len : rest.length
      = (AppendGadget.regBlocks skipped).length + 2 + tail2.length := by
    rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
  have htail2_len : tail2.length
      = (Compile.encodeRegs (s.drop (t + 1))).length + 1 + res.length := by
    rw [htail2]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hbound : H + 2 < (Compile.encodeTape s).length := by omega
  have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp (H + 1) (by omega)
  -- inner tester run (POS: cell 2 then block-end 0).
  have hinner := Compile.testBitInner_run_two [] rest H 0 (by omega) hcell hcell1 hcells
  rw [if_pos rfl] at hinner
  rw [← hdecomp] at hinner
  -- navtest run + trajectory.
  have hne_t : s.get t ≠ [] := by rw [hpos]; simp
  have hnav_run := Compile.navTestReg_run_content s t res ht hbit hne_t
  have hnav_traj := Compile.navTestReg_traj_content s t res ht hbit hne_t
  rw [← hsk, ← hHdef] at hnav_run
  rw [← hsk] at hnav_traj
  -- the outer branch composition.
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content t
      ≠ ClearGadget.navigateAndTestTM_exit_delim t := by
    show (ClearGadget.navigateToRegTM t).states + 1 ≠ (ClearGadget.navigateToRegTM t).states + 2
    omega
  have hHlt : H < (Compile.encodeTape s ++ res).length := by
    rw [hdecomp]; simp only [List.length_cons]; omega
  have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 2 := by
    rw [List.get_eq_getElem]
    have h2 : (Compile.encodeTape s ++ res)[H]? = some 2 := by rw [hdecomp]; exact hcell
    exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
  have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
      v < max (ClearGadget.navigateAndTestTM t).sig
        (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    obtain rfl : (2 : Nat) = v := Option.some.inj hv
    calc (2 : Nat) < 4 := by omega
      _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
      _ ≤ _ := le_max_left _ _
  have hpos' := branchComposeFlatTM_run_pos hexit_neq
    (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt t)
    (ClearGadget.navigateAndTestTM_exit_delim_lt t)
    cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
      rw [ClearGadget.navigateAndTestTM_states]; omega)
    [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hinner.1
    (Compile.haltingStateReached_of_halt Compile.testBitInner_exitPos_is_halt)
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt t)
    (ClearGadget.navigateAndTestTM_exit_delim_lt t)
    cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
      rw [ClearGadget.navigateAndTestTM_states]; omega)
    [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
    (fun k' hk' ck' hck' => (hinner.2 k' hk' ck' hck').2.2)
  have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
      Compile.testBitInnerTM ClearGadget.justRewindTM
      (ClearGadget.navigateAndTestTM_exit_content t)
      (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
  have hstate_eq : Compile.testBitInner_exitPos + (ClearGadget.navigateAndTestTM t).states
      = Compile.testBitRaw_exitPos t := by
    rw [Compile.testBitRaw_exitPos]; omega
  rw [hstate_eq, hraweq] at hpos'
  rw [hraweq] at hpos_traj
  -- join transport: the run never visits the demoted delim leaf.
  set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (2 + 1 + (H + 1 + 1)) with hTdef
  have hne12 : ∀ k, k ≤ T → ∀ ck, runFlatTM k (Compile.testBitRawTM t) cfg0 = some ck →
      ck.state_idx ≠ Compile.testBitRaw_exitNegDelim t := by
    intro k hk ck hck
    rcases Nat.lt_or_ge k T with hlt | hge
    · exact ClearGadget.ne_of_not_halting (Compile.testBitRaw_exitNegDelim_is_halt t)
        (hpos_traj k hlt ck hck)
    · have hkT : k = T := by omega
      subst hkT
      rw [hpos'.1] at hck
      obtain rfl := (Option.some.inj hck).symm
      show Compile.testBitRaw_exitPos t ≠ Compile.testBitRaw_exitNegDelim t
      rw [Compile.testBitRaw_exitPos, Compile.testBitRaw_exitNegDelim,
          Compile.testBitInnerTM_states]
      have h5 : Compile.testBitInner_exitPos = 5 := rfl
      have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
      omega
  refine ⟨T, ?_, ?_, ?_⟩
  · show runFlatTM T (Compile.joinTwoHalts (Compile.testBitRawTM t)
        (Compile.testBitRaw_exitNeg t) (Compile.testBitRaw_exitNegDelim t)) cfg0 = _
    rw [Compile.joinTwoHalts_run_eq _ _ _ T cfg0 hne12]
    exact hpos'.1
  · intro k hk ck hck
    have hck' : runFlatTM k (Compile.testBitRawTM t) cfg0 = some ck := by
      rw [← Compile.joinTwoHalts_run_eq (Compile.testBitRawTM t)
          (Compile.testBitRaw_exitNeg t) (Compile.testBitRaw_exitNegDelim t) k cfg0
          (fun j hj cj hcj => hne12 j (by omega) cj hcj)]
      exact hck
    have hnh := hpos_traj k hk ck hck'
    exact ⟨ClearGadget.ne_of_not_halting (Compile.testBitRaw_exitPos_is_halt t) hnh,
           ClearGadget.ne_of_not_halting (Compile.testBitRaw_exitNeg_is_halt t) hnh,
           Compile.joinTwoHalts_halting_false _ _ _ ck hnh⟩
  · have hnavle := ClearGadget.navSteps_le skipped
    have hLlen : (Compile.encodeTape s).length ≤ (Compile.encodeTape s ++ res).length := by
      rw [List.length_append]; omega
    omega

/-- Join transport for runs ending at the raw tester's kept NEG exit (`h1`):
the joined tester reproduces the run; the trajectory avoids both exits. -/
private theorem Compile.testBit_join_kept_neg (t : Var) (cfg0 : FlatTMConfig)
    (tape : List Nat) (T : Nat)
    (hraw : runFlatTM T (Compile.testBitRawTM t) cfg0
      = some { state_idx := Compile.testBitRaw_exitNeg t, tapes := [([], 0, tape)] })
    (htraj : ∀ k, k < T → ∀ ck, runFlatTM k (Compile.testBitRawTM t) cfg0 = some ck →
      haltingStateReached (Compile.testBitRawTM t) ck = false) :
    runFlatTM T (compileTestBit t).M cfg0
      = some { state_idx := (compileTestBit t).exitNeg, tapes := [([], 0, tape)] }
    ∧ (∀ k, k < T → ∀ ck, runFlatTM k (compileTestBit t).M cfg0 = some ck →
        ck.state_idx ≠ (compileTestBit t).exitPos ∧
        ck.state_idx ≠ (compileTestBit t).exitNeg ∧
        haltingStateReached (compileTestBit t).M ck = false) := by
  obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept
    (Compile.testBitRawTM t) (Compile.testBitRaw_exitNeg t)
    (Compile.testBitRaw_exitNegDelim t) cfg0 T ([], 0, tape) hraw htraj
    (Compile.testBitRaw_exitNeg_is_halt t) (Compile.testBitRaw_exitNegDelim_is_halt t)
  refine ⟨hjoin, ?_⟩
  intro k hk ck hck
  obtain ⟨hne1, hnh⟩ := hjoin_traj k hk ck hck
  exact ⟨ClearGadget.ne_of_not_halting (compileTestBit_exitPos_is_halt t) hnh, hne1, hnh⟩

/-- **Tester contract — negative (`s.get t ≠ [1]`).** `compileTestBit t` reaches
`exitNeg` with the head back at `0` and the tape **unchanged**, visiting neither
exit nor any halt state before; within `3·L + 12` steps. Three internal cases:
register empty (delim leaf), first bit `0`, or `≥ 2` bits. -/
theorem Compile.testBitReg_run_neg (t : Var) (s : State) (res : List Nat)
    (ht : t < s.length) (hbit : Compile.BitState s) (hneg : s.get t ≠ [1]) :
    ∃ T, runFlatTM T (compileTestBit t).M
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := (compileTestBit t).exitNeg,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
    ∧ (∀ k, k < T → ∀ ck,
        runFlatTM k (compileTestBit t).M
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ (compileTestBit t).exitPos ∧
        ck.state_idx ≠ (compileTestBit t).exitNeg ∧
        haltingStateReached (compileTestBit t).M ck = false)
    ∧ T ≤ 3 * (Compile.encodeTape s ++ res).length + 12 := by
  set skipped := (s.take t).map Compile.shiftReg with hsk
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set tail2 := Compile.encodeRegs (s.drop (t + 1)) ++ [Compile.endMark] ++ res with htail2
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  have htail2_len : tail2.length
      = (Compile.encodeRegs (s.drop (t + 1))).length + 1 + res.length := by
    rw [htail2]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content t
      ≠ ClearGadget.navigateAndTestTM_exit_delim t := by
    show (ClearGadget.navigateToRegTM t).states + 1 ≠ (ClearGadget.navigateToRegTM t).states + 2
    omega
  have hnavle := ClearGadget.navSteps_le skipped
  have hLlen : (Compile.encodeTape s).length ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append]; omega
  rcases hsgt : s.get t with _ | ⟨b, r⟩
  · -- Case A: register empty — the delim leaf (demoted), bridged to exitNeg.
    set rest := AppendGadget.regBlocks skipped ++ 0 :: tail2 with hrest_def
    have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
      have hsplit := Compile.encodeTape_split s t ht
      rw [← hsk] at hsplit
      have hsr : Compile.shiftReg (s.get t) = [] := by rw [hsgt]; rfl
      rw [hsr, List.append_nil] at hsplit
      rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htail2]
      simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
    have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
      have h := congrArg List.length hdecomp
      simp only [List.length_append, List.length_cons] at h
      omega
    have hrest_len : rest.length
        = (AppendGadget.regBlocks skipped).length + 1 + tail2.length := by
      rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
    have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp H (by omega)
    have hHle : H ≤ rest.length := by omega
    have hrew := ScanLeft.rewindToStart_run 4 3 [] rest H hHle hcells
    have hrew_traj := ScanLeft.rewindToStart_traj 4 3 [] rest H hHle hcells
    rw [← hdecomp] at hrew hrew_traj
    have hnav_run := Compile.navTestReg_run_delim s t res ht hbit hsgt
    have hnav_traj := Compile.navTestReg_traj_delim s t res ht hbit hsgt
    rw [← hsk, ← hHdef] at hnav_run
    rw [← hsk] at hnav_traj
    have hHlt : H < (Compile.encodeTape s ++ res).length := by
      rw [hdecomp]; simp only [List.length_cons]; omega
    have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 0 := by
      rw [List.get_eq_getElem]
      have h2 : (Compile.encodeTape s ++ res)[H]? = some 0 := by
        rw [hdecomp, hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
              = (AppendGadget.regBlocks skipped).length + 1 from by omega,
            List.getElem?_cons_succ, hrest_def,
            List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
    have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
        v < max (ClearGadget.navigateAndTestTM t).sig
          (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
      intro v hv
      rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
      obtain rfl : (0 : Nat) = v := Option.some.inj hv
      calc (0 : Nat) < 4 := by omega
        _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
        _ ≤ _ := le_max_left _ _
    have hneg' := branchComposeFlatTM_run_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt t)
      (ClearGadget.navigateAndTestTM_exit_delim_lt t)
      cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
        rw [ClearGadget.navigateAndTestTM_states]; omega)
      [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hrew
      (Compile.haltingStateReached_of_halt Compile.justRewindTM_exit_is_halt)
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt t)
      (ClearGadget.navigateAndTestTM_exit_delim_lt t)
      cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
        rw [ClearGadget.navigateAndTestTM_states]; omega)
      [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
      (fun k' hk' ck' hck' => (hrew_traj k' hk' ck' hck').2)
    have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
        Compile.testBitInnerTM ClearGadget.justRewindTM
        (ClearGadget.navigateAndTestTM_exit_content t)
        (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
    have hstate_eq : (1 : Nat) + ((ClearGadget.navigateAndTestTM t).states
          + Compile.testBitInnerTM.states) = Compile.testBitRaw_exitNegDelim t := by
      rw [Compile.testBitRaw_exitNegDelim]
      have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
      omega
    rw [hstate_eq, hraweq] at hneg'
    rw [hraweq] at hneg_traj
    set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (H + 1) with hTdef
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted
      (Compile.testBitRawTM t) (Compile.testBitRaw_exitNeg t)
      (Compile.testBitRaw_exitNegDelim t) cfg0 T [] (Compile.encodeTape s ++ res) 0
      hneg'.1 (fun k hk ck hck => hneg_traj k hk ck hck)
      (Compile.testBitRaw_exitNeg_is_halt t) (Compile.testBitRaw_exitNegDelim_is_halt t)
      (by rw [Compile.testBitRaw_exitNeg, Compile.testBitRaw_exitNegDelim,
              Compile.testBitInnerTM_states]
          have h8 : Compile.testBitInner_exitNeg = 8 := rfl
          have h1 : ClearGadget.justRewindTM_exit = 1 := rfl
          omega)
      (Compile.testBitRaw_seam_sym t s res rest hdecomp)
    refine ⟨T + 1, hjoin, ?_, ?_⟩
    · intro k hk ck hck
      obtain ⟨hne1, hnh⟩ := hjoin_traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting (compileTestBit_exitPos_is_halt t) hnh, hne1, hnh⟩
    · omega
  · -- register nonempty: first bit `b ≤ 1`.
    have hb1 : b ≤ 1 := by
      have hmem : s.get t ∈ s := by
        rw [State.get, List.getElem?_eq_getElem ht]; exact List.getElem_mem ht
      exact hbit _ hmem b (by simp [hsgt])
    have hne_t : s.get t ≠ [] := by rw [hsgt]; simp
    have hnav_run := Compile.navTestReg_run_content s t res ht hbit hne_t
    have hnav_traj := Compile.navTestReg_traj_content s t res ht hbit hne_t
    rw [← hsk, ← hHdef] at hnav_run
    rw [← hsk] at hnav_traj
    rcases hb : b with _ | b'
    · -- Case B: first bit `0` — NEG after one read.
      subst hb
      set tailp := Compile.shiftReg r ++ 0 :: tail2 with htailp
      set rest := AppendGadget.regBlocks skipped ++ 1 :: tailp with hrest_def
      have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
        have hsplit := Compile.encodeTape_split s t ht
        rw [← hsk] at hsplit
        have hsr : Compile.shiftReg (s.get t) = 1 :: Compile.shiftReg r := by
          rw [hsgt]; rfl
        rw [hsr] at hsplit
        rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htailp, htail2]
        simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
      have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
        have h := congrArg List.length hdecomp
        simp only [List.length_append, List.length_cons] at h
        omega
      have hrest_len : rest.length
          = (AppendGadget.regBlocks skipped).length + 1 + tailp.length := by
        rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
      have htailp_len : tailp.length = r.length + 1 + tail2.length := by
        rw [htailp]
        simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map]
        omega
      have hcell : (3 :: rest)[H]? = some 1 := by
        rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
              = (AppendGadget.regBlocks skipped).length + 1 from by omega,
            List.getElem?_cons_succ, hrest_def,
            List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp H (by omega)
      have hinner := Compile.testBitInner_run_b0 [] rest H hcell hcells
      rw [← hdecomp] at hinner
      have hHlt : H < (Compile.encodeTape s ++ res).length := by
        rw [hdecomp]; simp only [List.length_cons]; omega
      have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 1 := by
        rw [List.get_eq_getElem]
        have h2 : (Compile.encodeTape s ++ res)[H]? = some 1 := by rw [hdecomp]; exact hcell
        exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
      have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
          v < max (ClearGadget.navigateAndTestTM t).sig
            (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
        intro v hv
        rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
        obtain rfl : (1 : Nat) = v := Option.some.inj hv
        calc (1 : Nat) < 4 := by omega
          _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
          _ ≤ _ := le_max_left _ _
      have hpos' := branchComposeFlatTM_run_pos hexit_neq
        (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
        ClearGadget.justRewindTM_valid
        (ClearGadget.navigateAndTestTM_exit_content_lt t)
        (ClearGadget.navigateAndTestTM_exit_delim_lt t)
        cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
          rw [ClearGadget.navigateAndTestTM_states]; omega)
        [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hinner.1
        (Compile.haltingStateReached_of_halt Compile.testBitInner_exitNeg_is_halt)
      have hpos_traj := branchComposeFlatTM_no_early_halt_pos
        (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
        ClearGadget.justRewindTM_valid
        (ClearGadget.navigateAndTestTM_exit_content_lt t)
        (ClearGadget.navigateAndTestTM_exit_delim_lt t)
        cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
          rw [ClearGadget.navigateAndTestTM_states]; omega)
        [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
        (fun k' hk' ck' hck' => (hinner.2 k' hk' ck' hck').2.2)
      have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
          Compile.testBitInnerTM ClearGadget.justRewindTM
          (ClearGadget.navigateAndTestTM_exit_content t)
          (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
      have hstate_eq : Compile.testBitInner_exitNeg + (ClearGadget.navigateAndTestTM t).states
          = Compile.testBitRaw_exitNeg t := by
        rw [Compile.testBitRaw_exitNeg]; omega
      rw [hstate_eq, hraweq] at hpos'
      rw [hraweq] at hpos_traj
      set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (1 + 1 + (H + 1)) with hTdef
      obtain ⟨hjoin, hjoin_traj⟩ := Compile.testBit_join_kept_neg t cfg0
        (Compile.encodeTape s ++ res) T hpos'.1
        (fun k hk ck hck => hpos_traj k hk ck hck)
      exact ⟨T, hjoin, hjoin_traj, by omega⟩
    · -- Case C: first bit `1` and a second cell — NEG after two reads.
      subst hb
      rcases r with _ | ⟨c, r'⟩
      · -- register is exactly `[1]` — contradicts `hneg`.
        exfalso
        have hb'0 : b' = 0 := by omega
        subst hb'0
        exact hneg hsgt
      · have hb'0 : b' = 0 := by omega
        subst hb'0
        have hc1 : c ≤ 1 := by
          have hmem : s.get t ∈ s := by
            rw [State.get, List.getElem?_eq_getElem ht]; exact List.getElem_mem ht
          exact hbit _ hmem c (by simp [hsgt])
        set tailpp := Compile.shiftReg r' ++ 0 :: tail2 with htailpp
        set rest := AppendGadget.regBlocks skipped ++ 2 :: (c + 1) :: tailpp with hrest_def
        have hdecomp : Compile.encodeTape s ++ res = 3 :: rest := by
          have hsplit := Compile.encodeTape_split s t ht
          rw [← hsk] at hsplit
          have hsr : Compile.shiftReg (s.get t) = 2 :: (c + 1) :: Compile.shiftReg r' := by
            rw [hsgt]; rfl
          rw [hsr] at hsplit
          rw [Compile.encodeTape, List.cons_append, ← hsplit, hrest_def, htailpp, htail2]
          simp only [Compile.endMark, List.append_assoc, List.cons_append, List.nil_append]
        have hlenE : (Compile.encodeTape s).length + res.length = 1 + rest.length := by
          have h := congrArg List.length hdecomp
          simp only [List.length_append, List.length_cons] at h
          omega
        have hrest_len : rest.length
            = (AppendGadget.regBlocks skipped).length + 2 + tailpp.length := by
          rw [hrest_def]; simp only [List.length_append, List.length_cons]; omega
        have htailpp_len : tailpp.length = r'.length + 1 + tail2.length := by
          rw [htailpp]
          simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map]
          omega
        have hcell : (3 :: rest)[H]? = some 2 := by
          rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length
                = (AppendGadget.regBlocks skipped).length + 1 from by omega,
              List.getElem?_cons_succ, hrest_def,
              List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        have hcell1 : (3 :: rest)[H + 1]? = some (c + 1) := by
          rw [hHdef, show (1 : Nat) + (AppendGadget.regBlocks skipped).length + 1
                = ((AppendGadget.regBlocks skipped).length + 1) + 1 from by omega,
              List.getElem?_cons_succ, hrest_def,
              List.getElem?_append_right (Nat.le_succ_of_le (Nat.le_refl _)),
              show (AppendGadget.regBlocks skipped).length + 1
                - (AppendGadget.regBlocks skipped).length = 1 from by omega]
          rfl
        have hcells := Compile.testBit_rewind_cells s res hbit rest hdecomp (H + 1) (by omega)
        have hinner := Compile.testBitInner_run_two [] rest H (c + 1) (by omega)
          hcell hcell1 hcells
        rw [if_neg (by omega)] at hinner
        rw [← hdecomp] at hinner
        have hHlt : H < (Compile.encodeTape s ++ res).length := by
          rw [hdecomp]; simp only [List.length_cons]; omega
        have hcellH : (Compile.encodeTape s ++ res).get ⟨H, hHlt⟩ = 2 := by
          rw [List.get_eq_getElem]
          have h2 : (Compile.encodeTape s ++ res)[H]? = some 2 := by rw [hdecomp]; exact hcell
          exact Option.some.inj ((List.getElem?_eq_getElem hHlt).symm.trans h2)
        have hsymb : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res) = some v →
            v < max (ClearGadget.navigateAndTestTM t).sig
              (max Compile.testBitInnerTM.sig ClearGadget.justRewindTM.sig) := by
          intro v hv
          rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
          obtain rfl : (2 : Nat) = v := Option.some.inj hv
          calc (2 : Nat) < 4 := by omega
            _ = (ClearGadget.navigateAndTestTM t).sig := (ClearGadget.navigateAndTestTM_sig t).symm
            _ ≤ _ := le_max_left _ _
        have hpos' := branchComposeFlatTM_run_pos hexit_neq
          (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
          ClearGadget.justRewindTM_valid
          (ClearGadget.navigateAndTestTM_exit_content_lt t)
          (ClearGadget.navigateAndTestTM_exit_delim_lt t)
          cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
            rw [ClearGadget.navigateAndTestTM_states]; omega)
          [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj hinner.1
          (Compile.haltingStateReached_of_halt Compile.testBitInner_exitNeg_is_halt)
        have hpos_traj := branchComposeFlatTM_no_early_halt_pos
          (ClearGadget.navigateAndTestTM_valid t) Compile.testBitInnerTM_valid
          ClearGadget.justRewindTM_valid
          (ClearGadget.navigateAndTestTM_exit_content_lt t)
          (ClearGadget.navigateAndTestTM_exit_delim_lt t)
          cfg0 (show (0 : Nat) < (ClearGadget.navigateAndTestTM t).states from by
            rw [ClearGadget.navigateAndTestTM_states]; omega)
          [] H (Compile.encodeTape s ++ res) hsymb hnav_run hnav_traj
          (fun k' hk' ck' hck' => (hinner.2 k' hk' ck' hck').2.2)
        have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM t)
            Compile.testBitInnerTM ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content t)
            (ClearGadget.navigateAndTestTM_exit_delim t) = Compile.testBitRawTM t := rfl
        have hstate_eq : Compile.testBitInner_exitNeg + (ClearGadget.navigateAndTestTM t).states
            = Compile.testBitRaw_exitNeg t := by
          rw [Compile.testBitRaw_exitNeg]; omega
        rw [hstate_eq, hraweq] at hpos'
        rw [hraweq] at hpos_traj
        set T := ClearGadget.navSteps skipped + 1 + 1 + 1 + (2 + 1 + (H + 1 + 1)) with hTdef
        obtain ⟨hjoin, hjoin_traj⟩ := Compile.testBit_join_kept_neg t cfg0
          (Compile.encodeTape s ++ res) T hpos'.1
          (fun k hk ck hck => hpos_traj k hk ck hck)
        exact ⟨T, hjoin, hjoin_traj, by omega⟩

theorem Compile.moveContentExit0_lt (dst : Nat) :
    Compile.moveContentExit0 dst < (Compile.moveContentRawTM dst).states := by
  rw [Compile.moveContentExit0, Compile.moveContentRawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM2_exit_lt 0 dst; omega

theorem Compile.moveContentExit1_lt (dst : Nat) :
    Compile.moveContentExit1 dst < (Compile.moveContentRawTM dst).states := by
  rw [Compile.moveContentExit1, Compile.moveContentRawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM2_exit_lt 1 dst; omega

theorem Compile.moveContentTM_valid (dst : Nat) : validFlatTM (Compile.moveContentTM dst) :=
  joinTwoHalts_valid _ _ _ (Compile.moveContentRawTM_valid dst)
    (Compile.moveContentExit0_lt dst) (Compile.moveContentExit1_lt dst)
    (Compile.moveContentRawTM_tapes dst)

theorem Compile.moveContentTM_sig (dst : Nat) : (Compile.moveContentTM dst).sig = 4 := by
  rw [Compile.moveContentTM, joinTwoHalts_sig]; exact Compile.moveContentRawTM_sig dst

theorem Compile.moveContentTM_exit0_is_halt (dst : Nat) :
    (Compile.moveContentTM dst).halt[Compile.moveContentExit0 dst]? = some true :=
  joinTwoHalts_h1_is_halt _ _ _ (Compile.moveContentExit0_ne_exit1 dst)
    (Compile.moveContentExit0_is_halt dst)

theorem Compile.moveContentExit0_lt_states (dst : Nat) :
    Compile.moveContentExit0 dst < (Compile.moveContentTM dst).states := by
  rw [Compile.moveContentTM, joinTwoHalts_states]; exact Compile.moveContentExit0_lt dst

theorem Compile.moveBodyRawTM_valid (src dst : Nat) : validFlatTM (Compile.moveBodyRawTM src dst) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.navigateAndTestTM_valid src)
    (Compile.moveContentTM_valid dst) ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    (ClearGadget.navigateAndTestTM_tapes src) (Compile.moveContentTM_tapes dst)
    ClearGadget.justRewindTM_tapes

theorem Compile.moveBodyRawTM_exitLoop_is_halt (src dst : Nat) :
    (Compile.moveBodyRawTM src dst).halt[Compile.moveBodyRawTM_exitLoop src dst]? = some true := by
  rw [Compile.moveBodyRawTM_exitLoop, Compile.moveBodyRawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveContentTM_valid dst) (Compile.moveContentExit0_lt_states dst)
    (Compile.moveContentTM_exit0_is_halt dst)

theorem Compile.moveBodyRawTM_exitDone_is_halt (src dst : Nat) :
    (Compile.moveBodyRawTM src dst).halt[Compile.moveBodyRawTM_exitDone src dst]? = some true := by
  rw [Compile.moveBodyRawTM_exitDone, Compile.moveBodyRawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveContentTM_valid dst)
    (show ClearGadget.justRewindTM.halt[ClearGadget.justRewindTM_exit]? = some true from rfl)

theorem Compile.moveBodyRawTM_exitLoop_lt (src dst : Nat) :
    Compile.moveBodyRawTM_exitLoop src dst < (Compile.moveBodyRawTM src dst).states := by
  rw [Compile.moveBodyRawTM_exitLoop, Compile.moveBodyRawTM, branchComposeFlatTM_states]
  have := Compile.moveContentExit0_lt_states dst; omega

theorem Compile.moveBodyRawTM_exitDone_lt (src dst : Nat) :
    Compile.moveBodyRawTM_exitDone src dst < (Compile.moveBodyRawTM src dst).states := by
  rw [Compile.moveBodyRawTM_exitDone, Compile.moveBodyRawTM, branchComposeFlatTM_states]
  show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
      + ClearGadget.justRewindTM_exit
    < (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
      + ClearGadget.justRewindTM.states
  show _ + _ + 1 < _ + _ + 3; omega

theorem Compile.moveBodyRawTM_exitDone_ne_exitLoop (src dst : Nat) :
    Compile.moveBodyRawTM_exitDone src dst ≠ Compile.moveBodyRawTM_exitLoop src dst := by
  rw [Compile.moveBodyRawTM_exitDone, Compile.moveBodyRawTM_exitLoop]
  have := Compile.moveContentExit0_lt_states dst; omega

/-- **Validity of `moveRegionTM`.** Mirrors `clearRegionTM_valid`: a `loopTM` over
the valid `moveBodyRawTM` body with both exits in range and single-tape. Needed to
wire `moveRegionTM` into `composeFlatTM`/`branchComposeFlatTM` when assembling the
cross-register ops. -/
theorem Compile.moveRegionTM_valid (src dst : Nat) :
    validFlatTM (Compile.moveRegionTM src dst) :=
  loopTM_valid (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)
    (Compile.moveBodyRawTM_valid src dst)
    (Compile.moveBodyRawTM_exitDone_lt src dst) (Compile.moveBodyRawTM_exitLoop_lt src dst)
    (Compile.moveBodyRawTM_tapes src dst)

/-- The compiled-machine alphabet of `moveRegionTM` is the fixed `sig = 4`. -/
theorem Compile.moveRegionTM_sig (src dst : Nat) : (Compile.moveRegionTM src dst).sig = 4 := by
  rw [Compile.moveRegionTM, loopTM_sig]
  show (Compile.moveBodyRawTM src dst).sig = 4
  show (branchComposeFlatTM _ _ _ _ _).sig = 4
  rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig]
  show max 4 (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) = 4
  rw [Compile.moveContentTM_sig dst]
  rfl

/-! ### The dual-target *duplicating* move gadget `moveRegion2TM` (Risk C2)

`moveRegion2TM src dst1 dst2` transfers `src`'s content (FIFO, one bit/iter) to the
**end of BOTH** `dst1` and `dst2`, emptying `src`. It is the duplicating primitive
the `copy`/`tail`/`concat` ops need — a single-target move (`moveRegionTM`) cannot
duplicate data (the number of copies is invariant). The structure mirrors
`moveRegionTM` exactly; the content branch appends the read bit to **two** registers
instead of one (`moveBitM3TM = moveBitM2TM b dst1 ⨾ appendAtThenTwoPhaseRewind(b+1, dst2)`).
A TM-`#eval` probe confirms the dual-append body yields the exact `encodeTape`
(head→`0`, clean halt). Only the structural scaffolding (validity/halts) is built
here; the run lemma `moveRegion2TM_run` mirrors `moveRegionTM_run` (a three-register
coupled invariant) and is the next step. -/

/-- Single-bit dual-transfer engine for a fixed bit `b`: run `moveBitM2TM` (delete
`src`'s front, append `b+1` to `dst1`, rewind), then append `b+1` to `dst2` and
two-phase-rewind. -/
def Compile.moveBitM3TM (b dst1 dst2 : Nat) : FlatTM :=
  composeFlatTM (Compile.moveBitM2TM b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1)

/-- The surviving (found) exit of `moveBitM3TM` (b-independent: `moveBitM2TM`'s state
count and `appendAtTM`'s are both b-independent). -/
def Compile.moveBitM3_exit (dst1 dst2 : Nat) : Nat :=
  (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 6)

/-- `moveBitM2TM`'s state count does not depend on the bit `b`. -/
theorem Compile.moveBitM2TM_states_eq (b dst : Nat) :
    (Compile.moveBitM2TM b dst).states = (Compile.moveBitM2TM 0 dst).states := by
  show (composeFlatTM ClearGadget.stepDeleteRewindRawTM
        (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst)
        ClearGadget.stepDeleteRewindTM_exit).states
      = (composeFlatTM ClearGadget.stepDeleteRewindRawTM
        (AppendGadget.appendAtThenTwoPhaseRewindTM (0 + 1) dst)
        ClearGadget.stepDeleteRewindTM_exit).states
  rw [composeFlatTM_states, composeFlatTM_states,
      AppendGadget.appendAtThenTwoPhaseRewindTM_states,
      AppendGadget.appendAtThenTwoPhaseRewindTM_states,
      Compile.appendAtTM_states_eq (b + 1) dst, Compile.appendAtTM_states_eq (0 + 1) dst]

theorem Compile.moveBitM3TM_tapes (b dst1 dst2 : Nat) :
    (Compile.moveBitM3TM b dst1 dst2).tapes = 1 := by
  rw [Compile.moveBitM3TM, composeFlatTM_tapes]; exact Compile.moveBitM2TM_tapes b dst1

theorem Compile.moveBitM3TM_sig (b dst1 dst2 : Nat) :
    (Compile.moveBitM3TM b dst1 dst2).sig = 4 := by
  rw [Compile.moveBitM3TM, composeFlatTM_sig, Compile.moveBitM2TM_sig,
      AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl

theorem Compile.moveBitM3TM_valid (b dst1 dst2 : Nat) (hb : b ≤ 1) :
    validFlatTM (Compile.moveBitM3TM b dst1 dst2) :=
  composeFlatTM_valid (Compile.moveBitM2TM b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1)
    (Compile.moveBitM2TM_valid b dst1 hb)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst2)
    (Compile.moveBitM2_exit_lt b dst1)
    (Compile.moveBitM2TM_tapes b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_tapes (b + 1) dst2)

theorem Compile.moveBitM3_exit_is_halt (b dst1 dst2 : Nat) :
    (Compile.moveBitM3TM b dst1 dst2).halt[Compile.moveBitM3_exit dst1 dst2]? = some true := by
  have h := ScanLeft.composeFlatTM_halt_some_intro (Compile.moveBitM2TM b dst1)
    (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1)
    ((AppendGadget.appendAtTM (b + 1) dst2).states + 6)
    (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst2)
  rw [Compile.appendAtTM_states_eq (b + 1) dst2, Compile.moveBitM2TM_states_eq b dst1] at h
  exact h

theorem Compile.moveBitM3_exit_lt (b dst1 dst2 : Nat) :
    Compile.moveBitM3_exit dst1 dst2 < (Compile.moveBitM3TM b dst1 dst2).states := by
  rw [Compile.moveBitM3TM, composeFlatTM_states, Compile.moveBitM2TM_states_eq b dst1,
      AppendGadget.appendAtThenTwoPhaseRewindTM_states, Compile.appendAtTM_states_eq (b + 1) dst2,
      show (ScanLeft.rewindTwoPhaseTM 4 3).states = 8 from rfl]
  show (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 6)
      < (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 8)
  omega

/-- **The single-bit DUAL-transfer engine run (Risk C2).** From `src`'s content
start with front bit `b` (`s.get src = b :: cs`), `moveBitM3TM b dst1 dst2` deletes
`src`'s front cell, appends `b` to the end of **both** `dst1` and `dst2`, and
two-phase-rewinds, landing at `moveBitM3_exit` with the tape
`encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
  ++ (res ++ [0])` and head `0`. Composes `moveBitM2_run` (delete + append to `dst1`)
with `appendBitTwoPhase_run` (append to `dst2`). -/
theorem Compile.moveBitM3_run (s : State) (src dst1 dst2 : Var) (b : Nat) (cs : List Nat)
    (hb : b ≤ 1) (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2) (hd12 : dst1 ≠ dst2)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (hbit : Compile.BitState s) (hcons : s.get src = b :: cs) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBitM3TM b dst1 dst2)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBitM3_exit dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBitM3TM b dst1 dst2)
            { state_idx := 0,
              tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.moveBitM3TM b dst1 dst2) ck = false)
    ∧ t ≤ 10 * (Compile.encodeTape s ++ res).length + 30 := by
  -- Phase A: moveBitM2TM b dst1 (delete src front, append b to dst1).
  obtain ⟨tA, hA, hA_traj, hA_bud⟩ :=
    Compile.moveBitM2_run s src dst1 b cs hb hsd1 hsrc hdst1 hbit hcons res hres
  -- Phase B ingredients (on `mid`, appending b to dst2).
  have hbitA : Compile.BitState (s.set src cs) := by
    have := Compile.BitState_set_tail s src hbit hsrc
    rwa [show (s.get src).tail = cs from by rw [hcons, List.tail_cons]] at this
  have hgd1 : (s.set src cs).get dst1 = s.get dst1 :=
    Compile.get_set_ne s src cs dst1 hsrc (Ne.symm hsd1)
  have hdst1A : dst1 < (s.set src cs).length := by
    rw [Compile.length_set s src cs hsrc]; exact hdst1
  have hbitmid : Compile.BitState ((s.set src cs).set dst1 (s.get dst1 ++ [b])) := by
    refine Compile.BitState_set _ dst1 _ hbitA hdst1A ?_
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.BitState_get _ dst1 hbitA hdst1A x (by rw [hgd1]; exact hx)
    · simp only [List.mem_singleton] at hx; subst hx; omega
  have hdst2mid : dst2 < ((s.set src cs).set dst1 (s.get dst1 ++ [b])).length := by
    rw [Compile.length_set _ dst1 _ hdst1A, Compile.length_set s src cs hsrc]; exact hdst2
  have hgd2 : ((s.set src cs).set dst1 (s.get dst1 ++ [b])).get dst2 = s.get dst2 := by
    rw [Compile.get_set_ne (s.set src cs) dst1 (s.get dst1 ++ [b]) dst2 hdst1A (Ne.symm hd12),
        Compile.get_set_ne s src cs dst2 hsrc (Ne.symm hsd2)]
  have hres1 : Compile.ValidResidue (res ++ [0]) := by
    apply Compile.ValidResidue_append _ _ hres; intro x hx
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by decide⟩
  obtain ⟨tB, hB, hB_traj, hB_bud⟩ :=
    Compile.appendBitTwoPhase_run b hb ((s.set src cs).set dst1 (s.get dst1 ++ [b])) dst2
      hbitmid hdst2mid (res ++ [0]) hres1
  rw [hgd2] at hB
  -- length: phase A's exit tape is one cell longer than the input tape.
  have hmidlen : (Compile.encodeTape ((s.set src cs).set dst1 (s.get dst1 ++ [b])) ++ (res ++ [0])).length
      = (Compile.encodeTape s ++ res).length + 1 := by
    have e1 := Compile.encodeTape_set_length s src cs hsrc
    have e2 := Compile.encodeTape_set_length (s.set src cs) dst1 (s.get dst1 ++ [b]) hdst1A
    rw [hgd1] at e2
    rw [hcons] at e1
    simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at e1 e2 ⊢
    omega
  -- compose: moveBitM2TM b dst1 ⨾ appendAtThenTwoPhaseRewindTM (b+1) dst2.
  set right₁ : List Nat :=
    Compile.encodeTape ((s.set src cs).set dst1 (s.get dst1 ++ [b])) ++ (res ++ [0]) with hr1
  have hvalid1 : validFlatTM (Compile.moveBitM2TM b dst1) := Compile.moveBitM2TM_valid b dst1 hb
  have hvalid2 : validFlatTM (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) :=
    AppendGadget.appendAtThenTwoPhaseRewindTM_valid (b + 1) (by omega) dst2
  have hexit_lt : Compile.moveBitM2_exit dst1 < (Compile.moveBitM2TM b dst1).states :=
    Compile.moveBitM2_exit_lt b dst1
  have hcfg0lt : (0 : Nat) < (Compile.moveBitM2TM b dst1).states := by
    have := Compile.moveBitM2_exit_lt b dst1; omega
  have hM2start : (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).start = 0 := by
    show (composeFlatTM (AppendGadget.appendAtTM (b + 1) dst2) (ScanLeft.rewindTwoPhaseTM 4 3)
          (AppendGadget.appendAtTM_exit dst2)).start = 0
    rw [composeFlatTM_start, AppendGadget.appendAtTM_start]
  have hsym : ∀ v, currentTapeSymbol (([] : List Nat), 0, right₁) = some v →
      v < max (Compile.moveBitM2TM b dst1).sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).sig := by
    intro v hv
    rw [hr1, show currentTapeSymbol (([] : List Nat), 0,
          Compile.encodeTape ((s.set src cs).set dst1 (s.get dst1 ++ [b])) ++ (res ++ [0]))
        = some 3 from rfl] at hv
    rw [show max (Compile.moveBitM2TM b dst1).sig
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).sig = 4 from by
        rw [Compile.moveBitM2TM_sig, AppendGadget.appendAtThenTwoPhaseRewindTM_sig]; rfl]
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_traj1 : ∀ k, k < tA → ∀ ck,
      runFlatTM k (Compile.moveBitM2TM b dst1)
          { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                       Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ Compile.moveBitM2_exit dst1 ∧
      haltingStateReached (Compile.moveBitM2TM b dst1) ck = false := by
    intro k hk ck hck
    have hh := hA_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBitM2_exit_is_halt b dst1) hh, hh⟩
  have h_app_traj' : ∀ k, k < tB → ∀ ck,
      runFlatTM k (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2)
          { state_idx := (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2).start,
            tapes := [([], 0, right₁)] } = some ck →
      haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) ck = false := by
    rw [hM2start, hr1]; exact hB_traj
  have h_halt2 : haltingStateReached (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2)
      { state_idx := 6 + (AppendGadget.appendAtTM (b + 1) dst2).states,
        tapes := [([], 0,
          Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
            ++ (res ++ [0]))] } = true := by
    rw [show (6 : Nat) + (AppendGadget.appendAtTM (b + 1) dst2).states
          = (AppendGadget.appendAtTM (b + 1) dst2).states + 6 from Nat.add_comm ..]
    exact Compile.haltingStateReached_of_halt
      (AppendGadget.appendAtThenTwoPhaseRewindTM_exit_is_halt (b + 1) dst2)
  have hmoveeq : Compile.moveBitM3TM b dst1 dst2
      = composeFlatTM (Compile.moveBitM2TM b dst1)
          (AppendGadget.appendAtThenTwoPhaseRewindTM (b + 1) dst2) (Compile.moveBitM2_exit dst1) := rfl
  have hstate_eq : Compile.moveBitM3_exit dst1 dst2
      = (6 + (AppendGadget.appendAtTM (b + 1) dst2).states) + (Compile.moveBitM2TM b dst1).states := by
    show (Compile.moveBitM2TM 0 dst1).states + ((AppendGadget.appendAtTM 1 dst2).states + 6)
        = (6 + (AppendGadget.appendAtTM (b + 1) dst2).states) + (Compile.moveBitM2TM b dst1).states
    rw [Compile.moveBitM2TM_states_eq b dst1, Compile.appendAtTM_states_eq (b + 1) dst2]
    omega
  have hmain := composeFlatTM_run hvalid1 hvalid2 hexit_lt
    { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                 Compile.encodeTape s ++ res)] }
    hcfg0lt [] 0 right₁ hsym hA h_traj1
    (by rw [hM2start]; exact hB) h_halt2
  refine ⟨tA + 1 + tB, ?_, ?_, ?_⟩
  · rw [hmoveeq, hstate_eq]; exact hmain.1
  · intro k hk ck hck
    rw [hmoveeq] at hck ⊢
    exact composeFlatTM_no_early_halt hvalid1 hvalid2 hexit_lt
      { state_idx := 0, tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                                   Compile.encodeTape s ++ res)] }
      hcfg0lt [] 0 right₁ hsym hA h_traj1 h_app_traj' k hk ck hck
  · rw [hr1, hmidlen] at hB_bud
    omega

/-- Content branch (src non-empty): read the front bit, then run the matching
dual-bit transfer engine. The two bit paths exit at distinct states, merged by
`joinTwoHalts` below. -/
def Compile.moveContent2RawTM (dst1 dst2 : Nat) : FlatTM :=
  branchComposeFlatTM Compile.bitReadTM
    (Compile.moveBitM3TM 0 dst1 dst2) (Compile.moveBitM3TM 1 dst1 dst2)
    Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1

def Compile.moveContent2Exit0 (dst1 dst2 : Nat) : Nat :=
  Compile.bitReadTM.states + Compile.moveBitM3_exit dst1 dst2

def Compile.moveContent2Exit1 (dst1 dst2 : Nat) : Nat :=
  Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states + Compile.moveBitM3_exit dst1 dst2

/-- Content branch with the two bit-exits merged into one (`moveContent2Exit0`). -/
def Compile.moveContent2TM (dst1 dst2 : Nat) : FlatTM :=
  Compile.joinTwoHalts (Compile.moveContent2RawTM dst1 dst2)
    (Compile.moveContent2Exit0 dst1 dst2) (Compile.moveContent2Exit1 dst1 dst2)

theorem Compile.moveContent2RawTM_tapes (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).tapes = 1 := by
  rw [Compile.moveContent2RawTM, branchComposeFlatTM_tapes]; exact Compile.bitReadTM_tapes

theorem Compile.moveContent2TM_tapes (dst1 dst2 : Nat) :
    (Compile.moveContent2TM dst1 dst2).tapes = 1 := by
  rw [Compile.moveContent2TM, Compile.joinTwoHalts_tapes]
  exact Compile.moveContent2RawTM_tapes dst1 dst2

theorem Compile.moveContent2RawTM_sig (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).sig = 4 := by
  rw [Compile.moveContent2RawTM, branchComposeFlatTM_sig, Compile.bitReadTM_sig,
      Compile.moveBitM3TM_sig 0 dst1 dst2, Compile.moveBitM3TM_sig 1 dst1 dst2]; rfl

theorem Compile.moveContent2TM_sig (dst1 dst2 : Nat) :
    (Compile.moveContent2TM dst1 dst2).sig = 4 := by
  rw [Compile.moveContent2TM, joinTwoHalts_sig]; exact Compile.moveContent2RawTM_sig dst1 dst2

theorem Compile.moveContent2RawTM_valid (dst1 dst2 : Nat) :
    validFlatTM (Compile.moveContent2RawTM dst1 dst2) :=
  branchComposeFlatTM_valid _ _ _ _ _ Compile.bitReadTM_valid
    (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
    (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide)
    (by rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide)
    Compile.bitReadTM_tapes (Compile.moveBitM3TM_tapes 0 dst1 dst2)
    (Compile.moveBitM3TM_tapes 1 dst1 dst2)

theorem Compile.moveContent2Exit0_is_halt (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).halt[Compile.moveContent2Exit0 dst1 dst2]? = some true := by
  rw [Compile.moveContent2Exit0, Compile.moveContent2RawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide)) (Compile.moveBitM3_exit_lt 0 dst1 dst2)
    (Compile.moveBitM3_exit_is_halt 0 dst1 dst2)

theorem Compile.moveContent2Exit1_is_halt (dst1 dst2 : Nat) :
    (Compile.moveContent2RawTM dst1 dst2).halt[Compile.moveContent2Exit1 dst1 dst2]? = some true := by
  rw [Compile.moveContent2Exit1, Compile.moveContent2RawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide)) (Compile.moveBitM3_exit_is_halt 1 dst1 dst2)

theorem Compile.moveContent2Exit0_ne_exit1 (dst1 dst2 : Nat) :
    Compile.moveContent2Exit0 dst1 dst2 ≠ Compile.moveContent2Exit1 dst1 dst2 := by
  show Compile.bitReadTM.states + Compile.moveBitM3_exit dst1 dst2
      ≠ Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states
        + Compile.moveBitM3_exit dst1 dst2
  have h0 : 0 < (Compile.moveBitM3TM 0 dst1 dst2).states := by
    have := Compile.moveBitM3_exit_lt 0 dst1 dst2; omega
  omega

theorem Compile.moveContent2Exit0_lt (dst1 dst2 : Nat) :
    Compile.moveContent2Exit0 dst1 dst2 < (Compile.moveContent2RawTM dst1 dst2).states := by
  rw [Compile.moveContent2Exit0, Compile.moveContent2RawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM3_exit_lt 0 dst1 dst2; omega

theorem Compile.moveContent2Exit1_lt (dst1 dst2 : Nat) :
    Compile.moveContent2Exit1 dst1 dst2 < (Compile.moveContent2RawTM dst1 dst2).states := by
  rw [Compile.moveContent2Exit1, Compile.moveContent2RawTM, branchComposeFlatTM_states]
  have := Compile.moveBitM3_exit_lt 1 dst1 dst2; omega

theorem Compile.moveContent2TM_valid (dst1 dst2 : Nat) :
    validFlatTM (Compile.moveContent2TM dst1 dst2) :=
  joinTwoHalts_valid _ _ _ (Compile.moveContent2RawTM_valid dst1 dst2)
    (Compile.moveContent2Exit0_lt dst1 dst2) (Compile.moveContent2Exit1_lt dst1 dst2)
    (Compile.moveContent2RawTM_tapes dst1 dst2)

theorem Compile.moveContent2TM_exit0_is_halt (dst1 dst2 : Nat) :
    (Compile.moveContent2TM dst1 dst2).halt[Compile.moveContent2Exit0 dst1 dst2]? = some true :=
  joinTwoHalts_h1_is_halt _ _ _ (Compile.moveContent2Exit0_ne_exit1 dst1 dst2)
    (Compile.moveContent2Exit0_is_halt dst1 dst2)

theorem Compile.moveContent2Exit0_lt_states (dst1 dst2 : Nat) :
    Compile.moveContent2Exit0 dst1 dst2 < (Compile.moveContent2TM dst1 dst2).states := by
  rw [Compile.moveContent2TM, joinTwoHalts_states]; exact Compile.moveContent2Exit0_lt dst1 dst2

/-- **The dual-target content-branch run (Risk C2).** Mirrors `moveContent_run`:
run from `src`'s content start (head `H`) with front bit `b` (`s.get src = b :: cs`),
`moveContent2TM dst1 dst2` reads the bit and runs the matching dual-bit transfer
(`moveBitM3_run`), the two bit-paths merging through `joinTwoHalts` into
`moveContent2Exit0`. The tape becomes
`encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
  ++ (res ++ [0])`. -/
theorem Compile.moveContent2_run (s : State) (src dst1 dst2 : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2)
    (hd12 : dst1 ≠ dst2) (hbit : Compile.BitState s)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveContent2TM dst1 dst2)
        { state_idx := 0,
          tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                     Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveContent2Exit0 dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
                   ++ (res ++ [0]))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveContent2TM dst1 dst2)
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.moveContent2Exit0 dst1 dst2 ∧
        haltingStateReached (Compile.moveContent2TM dst1 dst2) ck = false)
    ∧ t ≤ 10 * (Compile.encodeTape s ++ res).length + 33 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.moveContent2RawTM dst1 dst2 with hrawdef
  set h1 := Compile.moveContent2Exit0 dst1 dst2 with hh1def
  set h2 := Compile.moveContent2Exit1 dst1 dst2 with hh2def
  have hraweq : branchComposeFlatTM Compile.bitReadTM
      (Compile.moveBitM3TM 0 dst1 dst2) (Compile.moveBitM3TM 1 dst1 dst2)
      Compile.bitReadTM_exit_b0 Compile.bitReadTM_exit_b1 = raw := rfl
  have hMeq : Compile.moveContent2TM dst1 dst2 = joinTwoHalts raw h1 h2 := rfl
  rw [hMeq]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    with hcfg0
  have hHeq : (1 : Nat) + (Compile.encodeRegs (s.take src)).length = H := by
    rw [hHdef, hskdef, Compile.regBlocks_map_shiftReg]
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  set tail' := Compile.shiftReg cs ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src hsrc
    rw [← hskdef] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg cs := by
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
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max Compile.bitReadTM.sig
          (max (Compile.moveBitM3TM 0 dst1 dst2).sig (Compile.moveBitM3TM 1 dst1 dst2).sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    rw [Compile.bitReadTM_sig]
    have : v < 4 := by have : v = b + 1 := (Option.some.inj hv).symm; omega
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < Compile.bitReadTM.states := by rw [Compile.bitReadTM_states]; omega
  have hexit_neq : Compile.bitReadTM_exit_b0 ≠ Compile.bitReadTM_exit_b1 := by decide
  have hep_lt : Compile.bitReadTM_exit_b0 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide
  have hen_lt : Compile.bitReadTM_exit_b1 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide
  have hh1_is := Compile.moveContent2Exit0_is_halt dst1 dst2
  have hh2_is := Compile.moveContent2Exit1_is_halt dst1 dst2
  have hh_ne := Compile.moveContent2Exit0_ne_exit1 dst1 dst2
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  have htest_run := Compile.bitReadTM_run b hb [] (Compile.encodeTape s ++ res) H hHlt hcellH
  have htest_traj : ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.bitReadTM cfg0 = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧ ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧
      haltingStateReached Compile.bitReadTM ck = false := by
    intro k hk ck hck
    exact Compile.bitReadTM_no_early_halt [] (Compile.encodeTape s ++ res) H k hk ck hck
  interval_cases b
  · -- bit 0: pos branch, dual transfer engine for bit 0; kept exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM3_run s src dst1 dst2 0 cs (by omega) hsd1 hsd2 hd12 hsrc hdst1 hdst2 hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM3_exit_is_halt 0 dst1 dst2))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM3_exit dst1 dst2 + Compile.bitReadTM.states = h1 := by
      rw [hh1def]; show Compile.moveBitM3_exit dst1 dst2 + Compile.bitReadTM.states
        = Compile.bitReadTM.states + Compile.moveBitM3_exit dst1 dst2
      omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [0])).set dst2
            (s.get dst2 ++ [0])) ++ (res ++ [0]))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega
  · -- bit 1: neg branch, dual transfer engine for bit 1; demoted exit.
    obtain ⟨t2, hmove, hmove_traj, hmove_bud⟩ :=
      Compile.moveBitM3_run s src dst1 dst2 1 cs (by omega) hsd1 hsd2 hd12 hsrc hdst1 hdst2 hbit hcons res hres
    rw [hHeq] at hmove hmove_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove
      (Compile.haltingStateReached_of_halt (Compile.moveBitM3_exit_is_halt 1 dst1 dst2))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      Compile.bitReadTM_valid (Compile.moveBitM3TM_valid 0 dst1 dst2 (by decide))
      (Compile.moveBitM3TM_valid 1 dst1 dst2 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hmove_traj
    have hstate_eq : Compile.moveBitM3_exit dst1 dst2
        + (Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states) = h2 := by
      rw [hh2def]; show Compile.moveBitM3_exit dst1 dst2
          + (Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states)
        = Compile.bitReadTM.states + (Compile.moveBitM3TM 0 dst1 dst2).states
            + Compile.moveBitM3_exit dst1 dst2
      omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [1])).set dst2
            (s.get dst2 ++ [1])) ++ (res ++ [0])) 0
      hneg.1 (fun k hk ck hck => hneg_traj k hk ck hck) hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (((s.set src cs).set dst1 (s.get dst1 ++ [1])).set dst2
                (s.get dst2 ++ [1])) ++ (res ++ [0]))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.moveContent2RawTM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hL := hLge; omega

/-- The loop body: navigate to `src`, branch content (move one bit to both targets)
vs delim (src empty → rewind & stop). -/
def Compile.moveBody2RawTM (src dst1 dst2 : Nat) : FlatTM :=
  branchComposeFlatTM (ClearGadget.navigateAndTestTM src) (Compile.moveContent2TM dst1 dst2)
    ClearGadget.justRewindTM
    (ClearGadget.navigateAndTestTM_exit_content src) (ClearGadget.navigateAndTestTM_exit_delim src)

def Compile.moveBody2RawTM_exitLoop (src dst1 dst2 : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + Compile.moveContent2Exit0 dst1 dst2

def Compile.moveBody2RawTM_exitDone (src dst1 dst2 : Nat) : Nat :=
  (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
    + ClearGadget.justRewindTM_exit

/-- The full dual-target move gadget: loop the body until `src` empties. -/
def Compile.moveRegion2TM (src dst1 dst2 : Nat) : FlatTM :=
  loopTM (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)

/-- The single halt state of `moveRegion2TM` (the `loopTM` done-exit). -/
def Compile.moveRegion2TM_exit (src dst1 dst2 : Nat) : Nat :=
  (Compile.moveBody2RawTM src dst1 dst2).states

theorem Compile.moveBody2RawTM_tapes (src dst1 dst2 : Nat) :
    (Compile.moveBody2RawTM src dst1 dst2).tapes = 1 := by
  rw [Compile.moveBody2RawTM, branchComposeFlatTM_tapes]
  exact ClearGadget.navigateAndTestTM_tapes src

theorem Compile.moveBody2RawTM_valid (src dst1 dst2 : Nat) :
    validFlatTM (Compile.moveBody2RawTM src dst1 dst2) :=
  branchComposeFlatTM_valid _ _ _ _ _ (ClearGadget.navigateAndTestTM_valid src)
    (Compile.moveContent2TM_valid dst1 dst2) ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    (ClearGadget.navigateAndTestTM_tapes src) (Compile.moveContent2TM_tapes dst1 dst2)
    ClearGadget.justRewindTM_tapes

theorem Compile.moveBody2RawTM_exitLoop_is_halt (src dst1 dst2 : Nat) :
    (Compile.moveBody2RawTM src dst1 dst2).halt[Compile.moveBody2RawTM_exitLoop src dst1 dst2]?
      = some true := by
  rw [Compile.moveBody2RawTM_exitLoop, Compile.moveBody2RawTM]
  exact Compile.branchComposeFlatTM_M2_halt_intro _ _ _ _ _ _
    (Compile.moveContent2TM_valid dst1 dst2) (Compile.moveContent2Exit0_lt_states dst1 dst2)
    (Compile.moveContent2TM_exit0_is_halt dst1 dst2)

theorem Compile.moveBody2RawTM_exitDone_is_halt (src dst1 dst2 : Nat) :
    (Compile.moveBody2RawTM src dst1 dst2).halt[Compile.moveBody2RawTM_exitDone src dst1 dst2]?
      = some true := by
  rw [Compile.moveBody2RawTM_exitDone, Compile.moveBody2RawTM]
  exact Compile.branchComposeFlatTM_M3_halt_intro _ _ _ _ _ _
    (Compile.moveContent2TM_valid dst1 dst2)
    (show ClearGadget.justRewindTM.halt[ClearGadget.justRewindTM_exit]? = some true from rfl)

theorem Compile.moveBody2RawTM_exitLoop_lt (src dst1 dst2 : Nat) :
    Compile.moveBody2RawTM_exitLoop src dst1 dst2 < (Compile.moveBody2RawTM src dst1 dst2).states := by
  rw [Compile.moveBody2RawTM_exitLoop, Compile.moveBody2RawTM, branchComposeFlatTM_states]
  have := Compile.moveContent2Exit0_lt_states dst1 dst2; omega

theorem Compile.moveBody2RawTM_exitDone_lt (src dst1 dst2 : Nat) :
    Compile.moveBody2RawTM_exitDone src dst1 dst2 < (Compile.moveBody2RawTM src dst1 dst2).states := by
  rw [Compile.moveBody2RawTM_exitDone, Compile.moveBody2RawTM, branchComposeFlatTM_states]
  show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
      + ClearGadget.justRewindTM_exit
    < (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
      + ClearGadget.justRewindTM.states
  show _ + _ + 1 < _ + _ + 3; omega

theorem Compile.moveBody2RawTM_exitDone_ne_exitLoop (src dst1 dst2 : Nat) :
    Compile.moveBody2RawTM_exitDone src dst1 dst2 ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 := by
  rw [Compile.moveBody2RawTM_exitDone, Compile.moveBody2RawTM_exitLoop]
  have := Compile.moveContent2Exit0_lt_states dst1 dst2; omega

theorem Compile.moveRegion2TM_tapes (src dst1 dst2 : Nat) :
    (Compile.moveRegion2TM src dst1 dst2).tapes = 1 := by
  rw [Compile.moveRegion2TM, loopTM_tapes]; exact Compile.moveBody2RawTM_tapes src dst1 dst2

theorem Compile.moveRegion2TM_start (src dst1 dst2 : Nat) :
    (Compile.moveRegion2TM src dst1 dst2).start = 0 := by
  show (Compile.moveBody2RawTM src dst1 dst2).start = 0
  show (branchComposeFlatTM _ _ _ _ _).start = 0
  rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src

/-- **Validity of `moveRegion2TM`.** Mirrors `moveRegionTM_valid`: a `loopTM` over
the valid dual-target body. -/
theorem Compile.moveRegion2TM_valid (src dst1 dst2 : Nat) :
    validFlatTM (Compile.moveRegion2TM src dst1 dst2) :=
  loopTM_valid (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)
    (Compile.moveBody2RawTM_valid src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_lt src dst1 dst2) (Compile.moveBody2RawTM_exitLoop_lt src dst1 dst2)
    (Compile.moveBody2RawTM_tapes src dst1 dst2)

theorem Compile.moveRegion2TM_sig (src dst1 dst2 : Nat) :
    (Compile.moveRegion2TM src dst1 dst2).sig = 4 := by
  rw [Compile.moveRegion2TM, loopTM_sig]
  show (Compile.moveBody2RawTM src dst1 dst2).sig = 4
  show (branchComposeFlatTM _ _ _ _ _).sig = 4
  rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig]
  show max 4 (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) = 4
  rw [Compile.moveContent2TM_sig dst1 dst2]
  rfl

/-- **Dual-target move loop body — done branch (`src` empty).** Mirrors
`moveBody_done_run`: navigate to `src`, find the delimiter (empty), rewind to head
`0`, tape unchanged, landing at `moveBody2RawTM_exitDone`. -/
theorem Compile.moveBody2_done_run (s : State) (src dst1 dst2 : Var) (res : List Nat)
    (hsrc : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBody2RawTM src dst1 dst2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBody2RawTM_exitDone src dst1 dst2,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s src hsrc
  have hbit_take : Compile.BitState (s.take src) :=
    fun reg hreg => hbit reg (List.mem_of_mem_take hreg)
  set skipped : List (List Nat) := (s.take src).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take src) :=
    Compile.regBlocks_map_shiftReg (s.take src)
  have hsklen : skipped.length = src := by
    rw [hskdef, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hsrc)]
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
    Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htaildef
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
    exact ⟨Compile.encodeRegs_lt_four (s.take src) hbit_take x hx,
           Compile.encodeRegs_no_endMark (s.take src) hbit_take x hx⟩
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
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM src).sig
        (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContent2TM_sig]; rfl,
        (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim src,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_delim skipped tail' hskip
    rw [← htape_nav, hsklen] at hn; exact hn
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail' hskip
        (by decide) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh,
           hh⟩
  have h_ne : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1
        ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1
      + ((1 + (AppendGadget.regBlocks skipped).length) + 1), ?_, ?_, ?_⟩
  · rw [show Compile.moveBody2RawTM src dst1 dst2
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
            (Compile.moveContent2TM dst1 dst2) ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content src)
            (ClearGadget.navigateAndTestTM_exit_delim src) from rfl,
      show Compile.moveBody2RawTM_exitDone src dst1 dst2
        = ClearGadget.justRewindTM_exit
            + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states)
          from by
          show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states
              + ClearGadget.justRewindTM_exit
            = ClearGadget.justRewindTM_exit
                + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContent2TM dst1 dst2).states)
          omega]
    exact (branchComposeFlatTM_run_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1 h_rewind
      (Compile.haltingStateReached_of_halt (show ClearGadget.justRewindTM.halt[1]? = some true from rfl))).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (fun k' hk' ck' hck' => (h_rewind_traj k' hk' ck' hck').2)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitDone_is_halt src dst1 dst2) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitLoop_is_halt src dst1 dst2) hh, hh⟩
  · omega

/-- **Dual-target move loop body — delete branch (`src` non-empty, front bit `b`).**
Navigate to `src`, the content branch reads `b` and runs the dual-bit transfer
(`moveContent2_run`), landing at `moveBody2RawTM_exitLoop` with the tape
`encodeTape (((s.set src cs).set dst1 (d1++[b])).set dst2 (d2++[b])) ++ (res ++ [0])`. -/
theorem Compile.moveBody2_delete_run (s : State) (src dst1 dst2 : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2)
    (hd12 : dst1 ≠ dst2) (hbit : Compile.BitState s)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBody2RawTM src dst1 dst2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBody2RawTM_exitLoop src dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set src cs).set dst1 (s.get dst1 ++ [b])).set dst2 (s.get dst2 ++ [b]))
                   ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false)
      ∧ t ≤ 12 * (Compile.encodeTape s ++ res).length + 38 := by
  have hne : s.get src ≠ [] := by rw [hcons]; exact List.cons_ne_nil _ _
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
    Compile.moveContent2_run s src dst1 dst2 b cs hcons hb hsd1 hsd2 hd12 hbit hsrc hdst1 hdst2 res hres
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) := by
    intro v hv
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContent2TM dst1 dst2).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContent2TM_sig]; rfl]
    have hmem : v ∈ Compile.encodeTape s ++ res := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact htape4 v hmem
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hpos := branchComposeFlatTM_run_pos hexit_neq
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne) hbody
    (Compile.haltingStateReached_of_halt (Compile.moveContent2TM_exit0_is_halt dst1 dst2))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContent2TM_valid dst1 dst2)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne)
    (fun k hk ck hck => (hbody_traj k hk ck hck).2)
  have hstate_eq : Compile.moveContent2Exit0 dst1 dst2 + (ClearGadget.navigateAndTestTM src).states
      = Compile.moveBody2RawTM_exitLoop src dst1 dst2 := by
    rw [Compile.moveBody2RawTM_exitLoop]; omega
  have hmoveeq : Compile.moveBody2RawTM src dst1 dst2
      = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
          (Compile.moveContent2TM dst1 dst2) ClearGadget.justRewindTM
          (ClearGadget.navigateAndTestTM_exit_content src)
          (ClearGadget.navigateAndTestTM_exit_delim src) := rfl
  rw [hstate_eq] at hpos
  refine ⟨(ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [hmoveeq]; exact hpos.1
  · intro k hk ck hck
    rw [hmoveeq] at hck
    have hh := hpos_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitDone_is_halt src dst1 dst2) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBody2RawTM_exitLoop_is_halt src dst1 dst2) hh, hh⟩
  · have hnav : ClearGadget.navSteps ((s.take src).map Compile.shiftReg)
        ≤ 2 * (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length + 1 :=
      ClearGadget.navSteps_le _
    have hrbL : (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length
        ≤ (Compile.encodeTape s ++ res).length := by
      have hsplit := congrArg List.length (Compile.encodeTape_split s src hsrc)
      simp only [List.length_append, List.length_cons, Compile.encodeRegs_length] at hsplit
      rw [List.length_append, Compile.encodeTape_length]
      omega
    omega

/-- **Move loop body — done branch (`src` empty).** Mirrors `clearBody_done_run`:
navigate to `src`, find the delimiter (empty), rewind to head `0`, tape unchanged,
landing at `moveBodyRawTM_exitDone`. The content machine `moveContentTM dst` is the
(unused) positive branch. -/
theorem Compile.moveBody_done_run (s : State) (src dst : Var) (res : List Nat)
    (hsrc : src < s.length) (hbit : Compile.BitState s) (hempty : s.get src = [])
    (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBodyRawTM src dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBodyRawTM_exitDone src dst,
               tapes := [([], 0, Compile.encodeTape s ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 12 := by
  obtain ⟨hv, hs⟩ := Compile.encodeTape_reg_decomp_at s src hsrc
  have hbit_take : Compile.BitState (s.take src) :=
    fun reg hreg => hbit reg (List.mem_of_mem_take hreg)
  set skipped : List (List Nat) := (s.take src).map Compile.shiftReg with hskdef
  have hregBlocks : AppendGadget.regBlocks skipped = Compile.encodeRegs (s.take src) :=
    Compile.regBlocks_map_shiftReg (s.take src)
  have hsklen : skipped.length = src := by
    rw [hskdef, List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hsrc)]
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
    Compile.encodeRegs (s.drop (src + 1)) ++ [Compile.endMark] ++ res with htaildef
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
    exact ⟨Compile.encodeRegs_lt_four (s.take src) hbit_take x hx,
           Compile.encodeRegs_no_endMark (s.take src) hbit_take x hx⟩
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
  have h_cfg0_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have h_sym : ∀ w, currentTapeSymbol ([], 1 + (AppendGadget.regBlocks skipped).length,
        Compile.encodeTape s ++ res) = some w →
      w < max (ClearGadget.navigateAndTestTM src).sig
        (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) := by
    intro w hw
    have hr : 1 + (AppendGadget.regBlocks skipped).length < (Compile.encodeTape s ++ res).length := by
      rw [htape_nav]; simp [List.length_append]; omega
    rw [currentTapeSymbol_in_range hr, List.get_eq_getElem] at hw
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContentTM_sig]; rfl,
        (Option.some.inj hw).symm]
    exact htape4 _ (List.getElem_mem hr)
  have h_run1 : runFlatTM (ClearGadget.navSteps skipped + 1 + 1) (ClearGadget.navigateAndTestTM src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.navigateAndTestTM_exit_delim src,
               tapes := [([], 1 + (AppendGadget.regBlocks skipped).length,
                          Compile.encodeTape s ++ res)] } := by
    have hn := ClearGadget.navigateAndTestTM_run_delim skipped tail' hskip
    rw [← htape_nav, hsklen] at hn; exact hn
  have h_traj1 : ∀ k, k < ClearGadget.navSteps skipped + 1 + 1 → ∀ ck,
      runFlatTM k (ClearGadget.navigateAndTestTM src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_content src ∧
      ck.state_idx ≠ ClearGadget.navigateAndTestTM_exit_delim src ∧
      haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
    intro k hk ck hck
    have hh : haltingStateReached (ClearGadget.navigateAndTestTM src) ck = false := by
      have hnh := ClearGadget.navigateAndTestTM_no_early_halt skipped 0 tail' hskip
        (by decide) k hk ck
      rw [hsklen, ← htape_nav] at hnh; exact hnh hck
    exact ⟨ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_content_is_halt src) hh,
           ClearGadget.ne_of_not_halting (ClearGadget.navigateAndTestTM_exit_delim_is_halt src) hh,
           hh⟩
  have h_ne : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1
        ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  refine ⟨(ClearGadget.navSteps skipped + 1 + 1) + 1
      + ((1 + (AppendGadget.regBlocks skipped).length) + 1), ?_, ?_, ?_⟩
  · rw [show Compile.moveBodyRawTM src dst
        = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
            (Compile.moveContentTM dst) ClearGadget.justRewindTM
            (ClearGadget.navigateAndTestTM_exit_content src)
            (ClearGadget.navigateAndTestTM_exit_delim src) from rfl,
      show Compile.moveBodyRawTM_exitDone src dst
        = ClearGadget.justRewindTM_exit
            + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states)
          from by
          show (ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states
              + ClearGadget.justRewindTM_exit
            = ClearGadget.justRewindTM_exit
                + ((ClearGadget.navigateAndTestTM src).states + (Compile.moveContentTM dst).states)
          omega]
    exact (branchComposeFlatTM_run_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1 h_rewind
      (Compile.haltingStateReached_of_halt (show ClearGadget.justRewindTM.halt[1]? = some true from rfl))).1
  · intro k hk ck hck
    have hh := branchComposeFlatTM_no_early_halt_neg h_ne
      (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
      ClearGadget.justRewindTM_valid
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      h_cfg0_lt
      [] (1 + (AppendGadget.regBlocks skipped).length) (Compile.encodeTape s ++ res)
      h_sym h_run1 h_traj1
      (fun k' hk' ck' hck' => (h_rewind_traj k' hk' ck' hck').2)
      k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitDone_is_halt src dst) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitLoop_is_halt src dst) hh, hh⟩
  · omega

/-- **Move loop body — delete branch (`src` non-empty, front bit `b`).** Navigate
to `src`, the content branch reads bit `b` and runs the single-bit transfer
(`moveContent_run`), landing at `moveBodyRawTM_exitLoop` with the tape
`encodeTape ((s.set src cs).set dst (s.get dst ++ [b])) ++ (res ++ [0])`. Mirrors
`opHead_run`'s content case. -/
theorem Compile.moveBody_delete_run (s : State) (src dst : Var) (b : Nat) (cs : List Nat)
    (hcons : s.get src = b :: cs) (hb : b ≤ 1) (hsd : src ≠ dst)
    (hbit : Compile.BitState s) (hsrc : src < s.length) (hdst : dst < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t, runFlatTM t (Compile.moveBodyRawTM src dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.moveBodyRawTM_exitLoop src dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set src cs).set dst (s.get dst ++ [b]))
                   ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false)
      ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length + 26 := by
  have hne : s.get src ≠ [] := by rw [hcons]; exact List.cons_ne_nil _ _
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    with hcfg0
  obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
    Compile.moveContent_run s src dst b cs hcons hb hsd hbit hsrc hdst res hres
  have htape4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four s hbit x hx
    · exact (hres x hx).1
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) := by
    intro v hv
    rw [show max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.moveContentTM dst).sig ClearGadget.justRewindTM.sig) = 4 from by
        rw [ClearGadget.navigateAndTestTM_sig, Compile.moveContentTM_sig]; rfl]
    have hmem : v ∈ Compile.encodeTape s ++ res := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact htape4 v hmem
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hpos := branchComposeFlatTM_run_pos hexit_neq
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne) hbody
    (Compile.haltingStateReached_of_halt (Compile.moveContentTM_exit0_is_halt dst))
  have hpos_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.navigateAndTestTM_valid src) (Compile.moveContentTM_valid dst)
    ClearGadget.justRewindTM_valid
    (ClearGadget.navigateAndTestTM_exit_content_lt src)
    (ClearGadget.navigateAndTestTM_exit_delim_lt src)
    cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
    (Compile.navTestReg_run_content s src res hsrc hbit hne)
    (Compile.navTestReg_traj_content s src res hsrc hbit hne)
    (fun k hk ck hck => (hbody_traj k hk ck hck).2)
  have hstate_eq : Compile.moveContentExit0 dst + (ClearGadget.navigateAndTestTM src).states
      = Compile.moveBodyRawTM_exitLoop src dst := by
    rw [Compile.moveBodyRawTM_exitLoop]; omega
  have hmoveeq : Compile.moveBodyRawTM src dst
      = branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
          (Compile.moveContentTM dst) ClearGadget.justRewindTM
          (ClearGadget.navigateAndTestTM_exit_content src)
          (ClearGadget.navigateAndTestTM_exit_delim src) := rfl
  rw [hstate_eq] at hpos
  refine ⟨(ClearGadget.navSteps ((s.take src).map Compile.shiftReg) + 1 + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [hmoveeq]; exact hpos.1
  · intro k hk ck hck
    rw [hmoveeq] at hck
    have hh := hpos_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitDone_is_halt src dst) hh,
           ClearGadget.ne_of_not_halting (Compile.moveBodyRawTM_exitLoop_is_halt src dst) hh, hh⟩
  · -- budget: navtest (≤ 2L+3) + bridge (1) + moveContent (≤ 7L+21) ≤ 9L+26.
    have hnav : ClearGadget.navSteps ((s.take src).map Compile.shiftReg)
        ≤ 2 * (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length + 1 :=
      ClearGadget.navSteps_le _
    have hrbL : (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length
        ≤ (Compile.encodeTape s ++ res).length := by
      have hsplit := congrArg List.length (Compile.encodeTape_split s src hsrc)
      simp only [List.length_append, List.length_cons, Compile.encodeRegs_length] at hsplit
      rw [List.length_append, Compile.encodeTape_length]
      omega
    omega

/-- **Move-loop budget arithmetic.** Each iteration is `O(L)` (a deletion + an
append, each one `O(current tape length) ≤ O(2·L)`), summed over `≤ L`
iterations — dominated by the quadratic `25·L²+25` (`n+2 ≤ L`). -/
theorem Compile.moveBudget_arith (n L : Nat) (h : n + 2 ≤ L) :
    (n + 1) * (18 * L + 27) ≤ 25 * L * L + 25 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  nlinarith [Nat.zero_le n, Nat.zero_le d, Nat.zero_le (n * d)]

/-- **The residue-tolerant move contract (Risk C2 — Task 2 critical path).**
Running `moveRegionTM src dst` on `encodeTape s ++ res_in` transfers `src`'s
content (FIFO) to the end of `dst`, empties `src`, rewinds the head to `0`, and
leaves the tape `encodeTape (moved s) ++ (res_in ++ replicate |s.get src| 0)`.
Assembled from `loopTM_run`; the per-iteration invariant `T j` couples BOTH
registers (`src = drop (n−j)` of `src₀`, `dst = dst₀ ++ first (n−j) bits`), and
the moved bit's value is threaded so `dst` gets the right bit. Unlike `clear`, the
tape **grows** one residue cell per iteration (`|T j| = L + (n−j)`), so the loop
budget is `25·L²+25` with `L = |encodeTape s ++ res_in|`. -/
theorem Compile.moveRegionTM_run (s : State) (src dst : Var) (res_in : List Nat)
    (hsd : src ≠ dst) (hsrc : src < s.length) (hdst : dst < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res_in) :
    ∃ t, runFlatTM t (Compile.moveRegionTM src dst)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
      = some { state_idx := Compile.moveRegionTM_exit src dst,
               tapes := [([], 0,
                 Compile.encodeTape ((s.set dst (s.get dst ++ s.get src)).set src [])
                   ++ (res_in ++ List.replicate (s.get src).length 0))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveRegionTM src dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } = some ck →
          ck.state_idx ≠ Compile.moveRegionTM_exit src dst ∧
          haltingStateReached (Compile.moveRegionTM src dst) ck = false)
      ∧ t ≤ 25 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
              + 25 := by
  set n := (s.get src).length with hn
  set st : Nat → State := fun m =>
    (s.set dst (s.get dst ++ (s.get src).take m)).set src ((s.get src).drop m) with hstdef
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 0, Compile.encodeTape (st (n - j)) ++ (res_in ++ List.replicate (n - j) 0)) with hTdef
  set L := (Compile.encodeTape s ++ res_in).length with hLdef
  have hsrc' : src < (s.set dst (s.get dst ++ (s.get src).take 0)).length := by
    rw [Compile.length_set s dst _ hdst]; exact hsrc
  have hv_bit : ∀ x ∈ s.get src, x ≤ 1 := Compile.BitState_get s src hbit hsrc
  have hd_bit : ∀ x ∈ s.get dst, x ≤ 1 := Compile.BitState_get s dst hbit hdst
  have hBstart : (Compile.moveBodyRawTM src dst).start = 0 := by
    show (branchComposeFlatTM _ _ _ _ _).start = 0
    rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src
  -- structural facts about `st m`.
  have hsrc_in : ∀ m, src < (s.set dst (s.get dst ++ (s.get src).take m)).length := by
    intro m; rw [Compile.length_set s dst _ hdst]; exact hsrc
  have hbit_st : ∀ m, Compile.BitState (st m) := by
    intro m
    have hbase : Compile.BitState (s.set dst (s.get dst ++ (s.get src).take m)) := by
      refine Compile.BitState_set s dst _ hbit hdst ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hd_bit x hx
      · exact hv_bit x (List.mem_of_mem_take hx)
    exact Compile.BitState_set _ src _ hbase (hsrc_in m)
      (fun x hx => hv_bit x (List.mem_of_mem_drop hx))
  have hlen_st : ∀ m, (st m).length = s.length := by
    intro m; rw [hstdef, Compile.length_set _ src _ (hsrc_in m), Compile.length_set s dst _ hdst]
  have hget_src_st : ∀ m, (st m).get src = (s.get src).drop m := by
    intro m; rw [hstdef]; exact Compile.get_set_eq _ src _ (hsrc_in m)
  have hget_dst_st : ∀ m, (st m).get dst = s.get dst ++ (s.get src).take m := by
    intro m; rw [hstdef, Compile.get_set_ne _ src _ dst (hsrc_in m) (Ne.symm hsd),
      Compile.get_set_eq s dst _ hdst]
  -- size of `st m` equals `State.size s` (bits move within the state).
  have hsize_st : ∀ m, m ≤ n → State.size (st m) = State.size s := by
    intro m hm
    have h1 := State.size_set_add s dst (s.get dst ++ (s.get src).take m)
    have h2 := State.size_set_add (s.set dst (s.get dst ++ (s.get src).take m)) src
      ((s.get src).drop m)
    rw [Compile.get_set_ne s dst _ src hdst hsd] at h2
    rw [List.length_append] at h1
    have htake : ((s.get src).take m).length = m := by rw [List.length_take, ← hn]; omega
    have hdrop : ((s.get src).drop m).length = n - m := by rw [List.length_drop, ← hn]
    rw [htake] at h1
    rw [hdrop] at h2
    simp only [hstdef] at h2 ⊢
    rw [← hn] at h2
    omega
  -- tape length of `T j`: grows by `n − j` residue cells.
  have hTlen : ∀ j, j ≤ n → (T j).2.2.length = L + (n - j) := by
    intro j hj
    simp only [hTdef, List.length_append, List.length_replicate]
    rw [Compile.encodeTape_length, hsize_st (n - j) (Nat.sub_le n j), hlen_st,
        hLdef, List.length_append, Compile.encodeTape_length]
    omega
  have hnL : n + 2 ≤ L := by
    have hsize := State.size_set_add s src ([] : List Nat)
    simp only [List.length_nil, Nat.add_zero] at hsize
    rw [hLdef, List.length_append, Compile.encodeTape_length]
    omega
  -- all tape symbols of `T j` are `< 4`.
  have hT_lt : ∀ j x, x ∈ (T j).2.2 → x < 4 := by
    intro j x hx
    simp only [hTdef] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four _ (hbit_st _) x hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hres x hx).1
      · rw [List.mem_replicate] at hx; omega
  have h_sym : ∀ m v, currentTapeSymbol (T m) = some v → v < (Compile.moveBodyRawTM src dst).sig := by
    intro m v hv
    have hsig : (Compile.moveBodyRawTM src dst).sig = 4 := by
      show (branchComposeFlatTM _ _ _ _ _).sig = 4
      rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig, Compile.moveContentTM_sig]; rfl
    rw [hsig]
    have hmem : v ∈ (T m).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_lt m v hmem
  -- done branch: `T 0`, register `src` empty.
  have hdone := Compile.moveBody_done_run (st n) src dst (res_in ++ List.replicate n 0)
    (by rw [hlen_st]; exact hsrc) (hbit_st n)
    (by rw [hget_src_st, hn]; exact List.drop_length)
    (Compile.ValidResidue_append_replicate_zero res_in n hres)
  obtain ⟨tDone, hdr, hdt, hdb⟩ := hdone
  have hT0 : T 0 = ([], 0, Compile.encodeTape (st n) ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero]
  have h_done_bnd : tDone + 1 ≤ 18 * L + 27 := by
    have hlen0 := hTlen 0 (Nat.zero_le n)
    simp only [hTdef, Nat.sub_zero] at hlen0
    rw [hlen0] at hdb
    omega
  -- per-iteration move: `T (j+1) → T j` for `j < n`, moving one bit.
  have hiter_ex : ∀ j, j < n → ∃ t,
      runFlatTM t (Compile.moveBodyRawTM src dst)
          { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBodyRawTM_exitLoop src dst, tapes := [T j] } ∧
      (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBodyRawTM src dst)
            { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] } = some ck →
        ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
        ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
        haltingStateReached (Compile.moveBodyRawTM src dst) ck = false) ∧
      t ≤ 18 * L + 26 := by
    intro j hj
    set m := n - (j + 1) with hm
    have hmn : m < n := by omega
    have hm1 : m + 1 = n - j := by omega
    have hmlen : m < (s.get src).length := by rw [← hn]; exact hmn
    -- the front bit of `st m`'s src content.
    have hdc : (s.get src).drop m = (s.get src)[m] :: (s.get src).drop (m + 1) :=
      List.drop_eq_getElem_cons hmlen
    have hb1 : (s.get src)[m] ≤ 1 := hv_bit _ (List.getElem_mem hmlen)
    have hsrc_cons : (st m).get src = (s.get src)[m] :: (s.get src).drop (m + 1) := by
      rw [hget_src_st]; exact hdc
    obtain ⟨t, hr, ht, hbnd⟩ := Compile.moveBody_delete_run (st m) src dst ((s.get src)[m])
      ((s.get src).drop (m + 1)) hsrc_cons hb1 hsd (hbit_st m) (by rw [hlen_st]; exact hsrc)
      (by rw [hlen_st]; exact hdst) (res_in ++ List.replicate m 0)
      (Compile.ValidResidue_append_replicate_zero res_in m hres)
    -- bridge the move output to `T j`.
    have hstate_eq : ((st m).set src ((s.get src).drop (m + 1))).set dst
          ((st m).get dst ++ [(s.get src)[m]]) = st (n - j) := by
      rw [hget_dst_st, hstdef]
      rw [Compile.set_set _ src _ _ (hsrc_in m)]
      rw [Compile.set_comm (s.set dst (s.get dst ++ (s.get src).take m)) src dst _ _
            (hsrc_in m) (by rw [Compile.length_set s dst _ hdst]; exact hdst) hsd,
          Compile.set_set s dst _ _ hdst]
      rw [show (s.get dst ++ (s.get src).take m) ++ [(s.get src)[m]]
            = s.get dst ++ (s.get src).take (m + 1) from by
            rw [List.append_assoc, List.take_succ_eq_append_getElem hmlen],
          ← hm1]
    have hres_eq : (res_in ++ List.replicate m 0) ++ [0] = res_in ++ List.replicate (n - j) 0 := by
      rw [List.append_assoc, ← List.replicate_succ', hm1]
    rw [hstate_eq, hres_eq] at hr
    have hlenj := hTlen (j + 1) (by omega)
    simp only [hTdef] at hlenj
    rw [show n - (j + 1) = m from rfl] at hlenj
    rw [hlenj] at hbnd
    refine ⟨t, ?_, ?_, by omega⟩
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact hr
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact ht
  -- assemble the loop.
  set tIter : Nat → Nat := fun j => if hj : j < n then (hiter_ex j hj).choose else 0 with htIter
  have h_done_full :
      runFlatTM tDone (Compile.moveBodyRawTM src dst)
          { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T 0] }
        = some { state_idx := Compile.moveBodyRawTM_exitDone src dst, tapes := [T 0] } ∧
      (∀ k, k < tDone → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false) := by
    refine ⟨?_, ?_⟩
    · rw [hBstart, hT0]; exact hdr
    · rw [hBstart, hT0]; exact hdt
  have h_iter_full : ∀ j, j < n →
      runFlatTM (tIter j) (Compile.moveBodyRawTM src dst)
          { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBodyRawTM_exitLoop src dst, tapes := [T j] } ∧
      (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (Compile.moveBodyRawTM src dst)
              { state_idx := (Compile.moveBodyRawTM src dst).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ Compile.moveBodyRawTM_exitDone src dst ∧
          ck.state_idx ≠ Compile.moveBodyRawTM_exitLoop src dst ∧
          haltingStateReached (Compile.moveBodyRawTM src dst) ck = false) := by
    intro j hj
    have hspec := (hiter_ex j hj).choose_spec
    simp only [htIter, dif_pos hj]
    exact ⟨hspec.1, hspec.2.1⟩
  have h_iter_bnd : ∀ j, j < n → tIter j + 1 ≤ 18 * L + 27 := by
    intro j hj
    have hb := (hiter_ex j hj).choose_spec.2.2
    simp only [htIter, dif_pos hj]
    omega
  have hmain := loopTM_run (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)
    (Compile.moveBodyRawTM_valid src dst)
    (Compile.moveBodyRawTM_exitDone_lt src dst) (Compile.moveBodyRawTM_exitLoop_lt src dst)
    (Compile.moveBodyRawTM_exitDone_ne_exitLoop src dst) T h_sym tIter tDone h_done_full n h_iter_full
  have hmain_traj := loopTM_no_early_halt (Compile.moveBodyRawTM src dst)
    (Compile.moveBodyRawTM_exitDone src dst) (Compile.moveBodyRawTM_exitLoop src dst)
    (Compile.moveBodyRawTM_valid src dst)
    (Compile.moveBodyRawTM_exitDone_lt src dst) (Compile.moveBodyRawTM_exitLoop_lt src dst)
    (Compile.moveBodyRawTM_exitDone_ne_exitLoop src dst) T h_sym tIter tDone h_done_full n h_iter_full
  -- convert `T n` (start) and `T 0` (end) to the stated forms.
  have hTn : T n = ([], 0, Compile.encodeTape s ++ res_in) := by
    simp only [hTdef, Nat.sub_self]
    rw [hstdef]
    simp only [List.take_zero, List.drop_zero, List.append_nil, List.replicate_zero]
    rw [Compile.set_get_self s dst hdst, Compile.set_get_self s src hsrc]
  have hTfin : T 0 = ([], 0, Compile.encodeTape ((s.set dst (s.get dst ++ s.get src)).set src [])
      ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero, hstdef]
    rw [show (s.get src).take n = s.get src from by rw [hn]; exact List.take_length,
        show (s.get src).drop n = [] from by rw [hn]; exact List.drop_length]
  rw [hBstart, hTn, hTfin] at hmain
  rw [hBstart, hTn] at hmain_traj
  have hMeq : Compile.moveRegionTM src dst
      = loopTM (Compile.moveBodyRawTM src dst) (Compile.moveBodyRawTM_exitDone src dst)
          (Compile.moveBodyRawTM_exitLoop src dst) := rfl
  have hExeq : Compile.moveRegionTM_exit src dst = (Compile.moveBodyRawTM src dst).states := rfl
  have hexit_halt : (Compile.moveRegionTM src dst).halt[(Compile.moveBodyRawTM src dst).states]?
      = some true := by
    rw [hMeq]
    show (loopHalt (Compile.moveBodyRawTM src dst))[(Compile.moveBodyRawTM src dst).states]? = some true
    show (List.replicate (Compile.moveBodyRawTM src dst).states false ++ [true])[(Compile.moveBodyRawTM src dst).states]?
        = some true
    rw [List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  refine ⟨loopBudget tIter tDone n, ?_, ?_, ?_⟩
  · rw [hMeq, hExeq]; exact hmain
  · intro k hk ck hck
    rw [hMeq] at hck
    have hh := hmain_traj k hk ck hck
    refine ⟨?_, hh⟩
    rw [hExeq]
    rw [hMeq] at hexit_halt
    exact ClearGadget.ne_of_not_halting hexit_halt hh
  · -- budget: `loopBudget ≤ (n+1)·(18L+27) ≤ 25L²+25` (`n+2 ≤ L`).
    rw [hLdef] at hnL ⊢
    exact le_trans
      (Compile.loopBudget_le tIter tDone (18 * L + 27) n h_done_bnd h_iter_bnd)
      (by rw [← hLdef]; exact Compile.moveBudget_arith n L (by rw [hLdef]; exact hnL))

/-- **Dual-target move-loop budget arithmetic.** `(n+1)` iterations each `≤ 36L+39`
(per-iter tape `≤ L + 2(n−j) ≤ 3L`, two appends/bit), `n+1 ≤ L`, gives a cubic-free
quadratic total. -/
theorem Compile.moveBudget2_arith (n L : Nat) (h : n + 2 ≤ L) :
    (n + 1) * (36 * L + 39) ≤ 36 * L * L + 39 * L := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  nlinarith [Nat.zero_le n, Nat.zero_le d, Nat.zero_le (n * d)]

/-- **The dual-target duplicating move contract (Risk C2).** Running
`moveRegion2TM src dst1 dst2` on `encodeTape s ++ res_in` transfers `src`'s content
(FIFO) to the end of **both** `dst1` and `dst2`, empties `src`, rewinds the head to
`0`, leaving `encodeTape (moved s) ++ (res_in ++ replicate |s.get src| 0)`. Mirrors
`moveRegionTM_run`, but the per-iteration invariant couples **three** registers and
the state size grows (each bit is duplicated), so the per-iteration tape length is
`L + 2(n−j)` and the loop budget is `36·L²+39·L`. -/
theorem Compile.moveRegion2TM_run (s : State) (src dst1 dst2 : Var) (res_in : List Nat)
    (hsd1 : src ≠ dst1) (hsd2 : src ≠ dst2) (hd12 : dst1 ≠ dst2)
    (hsrc : src < s.length) (hdst1 : dst1 < s.length) (hdst2 : dst2 < s.length)
    (hbit : Compile.BitState s) (hres : Compile.ValidResidue res_in) :
    ∃ t, runFlatTM t (Compile.moveRegion2TM src dst1 dst2)
        { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
      = some { state_idx := Compile.moveRegion2TM_exit src dst1 dst2,
               tapes := [([], 0,
                 Compile.encodeTape
                     (((s.set dst1 (s.get dst1 ++ s.get src)).set dst2 (s.get dst2 ++ s.get src)).set src [])
                   ++ (res_in ++ List.replicate (s.get src).length 0))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.moveRegion2TM src dst1 dst2)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } = some ck →
          ck.state_idx ≠ Compile.moveRegion2TM_exit src dst1 dst2 ∧
          haltingStateReached (Compile.moveRegion2TM src dst1 dst2) ck = false)
      ∧ t ≤ 36 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
              + 39 * (Compile.encodeTape s ++ res_in).length := by
  set n := (s.get src).length with hn
  set st : Nat → State := fun m =>
    ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2 (s.get dst2 ++ (s.get src).take m)).set src
      ((s.get src).drop m) with hstdef
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 0, Compile.encodeTape (st (n - j)) ++ (res_in ++ List.replicate (n - j) 0)) with hTdef
  set L := (Compile.encodeTape s ++ res_in).length with hLdef
  have hv_bit : ∀ x ∈ s.get src, x ≤ 1 := Compile.BitState_get s src hbit hsrc
  have hd1_bit : ∀ x ∈ s.get dst1, x ≤ 1 := Compile.BitState_get s dst1 hbit hdst1
  have hd2_bit : ∀ x ∈ s.get dst2, x ≤ 1 := Compile.BitState_get s dst2 hbit hdst2
  have hBstart : (Compile.moveBody2RawTM src dst1 dst2).start = 0 := by
    show (branchComposeFlatTM _ _ _ _ _).start = 0
    rw [branchComposeFlatTM_start]; exact ClearGadget.navigateAndTestTM_start src
  have hlenP : ∀ (m : Nat),
      (s.set dst1 (s.get dst1 ++ (s.get src).take m)).length = s.length :=
    fun m => Compile.length_set s dst1 _ hdst1
  have hlenQ : ∀ m, ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2
      (s.get dst2 ++ (s.get src).take m)).length = s.length :=
    fun m => by rw [Compile.length_set _ dst2 _ (by rw [hlenP]; exact hdst2), hlenP]
  have hlen_st : ∀ m, (st m).length = s.length := fun m => by
    simp only [hstdef]; rw [Compile.length_set _ src _ (by rw [hlenQ]; exact hsrc), hlenQ]
  have hget_src_st : ∀ m, (st m).get src = (s.get src).drop m := fun m => by
    simp only [hstdef]; exact Compile.get_set_eq _ src _ (by rw [hlenQ]; exact hsrc)
  have hget_dst1_st : ∀ m, (st m).get dst1 = s.get dst1 ++ (s.get src).take m := fun m => by
    simp only [hstdef]
    rw [Compile.get_set_ne _ src _ dst1 (by rw [hlenQ]; exact hsrc) (Ne.symm hsd1),
        Compile.get_set_ne _ dst2 _ dst1 (by rw [hlenP]; exact hdst2) hd12,
        Compile.get_set_eq s dst1 _ hdst1]
  have hget_dst2_st : ∀ m, (st m).get dst2 = s.get dst2 ++ (s.get src).take m := fun m => by
    simp only [hstdef]
    rw [Compile.get_set_ne _ src _ dst2 (by rw [hlenQ]; exact hsrc) (Ne.symm hsd2),
        Compile.get_set_eq _ dst2 _ (by rw [hlenP]; exact hdst2)]
  have hbit_st : ∀ m, Compile.BitState (st m) := fun m => by
    simp only [hstdef]
    refine Compile.BitState_set _ src _ ?_ (by rw [hlenQ]; exact hsrc)
      (fun x hx => hv_bit x (List.mem_of_mem_drop hx))
    refine Compile.BitState_set _ dst2 _ ?_ (by rw [hlenP]; exact hdst2) ?_
    · refine Compile.BitState_set s dst1 _ hbit hdst1 ?_
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hd1_bit x hx
      · exact hv_bit x (List.mem_of_mem_take hx)
    · intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hd2_bit x hx
      · exact hv_bit x (List.mem_of_mem_take hx)
  -- size of `st m` grows by `m` (each moved bit is duplicated into dst1 and dst2).
  have hsize_st : ∀ m, m ≤ n → State.size (st m) = State.size s + m := by
    intro m hm
    have htake : ((s.get src).take m).length = m := by rw [List.length_take, ← hn]; omega
    have hdrop : ((s.get src).drop m).length = n - m := by rw [List.length_drop, ← hn]
    have e1 := State.size_set_add s dst1 (s.get dst1 ++ (s.get src).take m)
    have hP_d2 : (s.set dst1 (s.get dst1 ++ (s.get src).take m)).get dst2 = s.get dst2 :=
      Compile.get_set_ne s dst1 _ dst2 hdst1 (Ne.symm hd12)
    have e2 := State.size_set_add (s.set dst1 (s.get dst1 ++ (s.get src).take m)) dst2
      (s.get dst2 ++ (s.get src).take m)
    rw [hP_d2] at e2
    have hQ_src : ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2
        (s.get dst2 ++ (s.get src).take m)).get src = s.get src := by
      rw [Compile.get_set_ne _ dst2 _ src (by rw [hlenP]; exact hdst2) hsd2,
          Compile.get_set_ne s dst1 _ src hdst1 hsd1]
    have e3 := State.size_set_add ((s.set dst1 (s.get dst1 ++ (s.get src).take m)).set dst2
      (s.get dst2 ++ (s.get src).take m)) src ((s.get src).drop m)
    rw [hQ_src] at e3
    simp only [hstdef, List.length_append, htake, hdrop] at e1 e2 e3 ⊢
    omega
  have hTlen : ∀ j, j ≤ n → (T j).2.2.length = L + 2 * (n - j) := by
    intro j hj
    simp only [hTdef, List.length_append, List.length_replicate]
    rw [Compile.encodeTape_length, hsize_st (n - j) (Nat.sub_le n j), hlen_st,
        hLdef, List.length_append, Compile.encodeTape_length]
    omega
  have hnL : n + 2 ≤ L := by
    have hsize := State.size_set_add s src ([] : List Nat)
    simp only [List.length_nil, Nat.add_zero] at hsize
    rw [hLdef, List.length_append, Compile.encodeTape_length]
    omega
  have hT_lt : ∀ j x, x ∈ (T j).2.2 → x < 4 := by
    intro j x hx
    simp only [hTdef] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Compile.encodeTape_lt_four _ (hbit_st _) x hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hres x hx).1
      · rw [List.mem_replicate] at hx; omega
  have h_sym : ∀ m v, currentTapeSymbol (T m) = some v → v < (Compile.moveBody2RawTM src dst1 dst2).sig := by
    intro m v hv
    have hsig : (Compile.moveBody2RawTM src dst1 dst2).sig = 4 := by
      show (branchComposeFlatTM _ _ _ _ _).sig = 4
      rw [branchComposeFlatTM_sig, ClearGadget.navigateAndTestTM_sig, Compile.moveContent2TM_sig]; rfl
    rw [hsig]
    have hmem : v ∈ (T m).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_lt m v hmem
  -- done branch: `T 0`, register `src` empty.
  have hdone := Compile.moveBody2_done_run (st n) src dst1 dst2 (res_in ++ List.replicate n 0)
    (by rw [hlen_st]; exact hsrc) (hbit_st n)
    (by rw [hget_src_st, hn]; exact List.drop_length)
    (Compile.ValidResidue_append_replicate_zero res_in n hres)
  obtain ⟨tDone, hdr, hdt, hdb⟩ := hdone
  have hT0 : T 0 = ([], 0, Compile.encodeTape (st n) ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero]
  have h_done_bnd : tDone + 1 ≤ 36 * L + 39 := by
    have hlen0 := hTlen 0 (Nat.zero_le n)
    simp only [hTdef, Nat.sub_zero] at hlen0
    rw [hlen0] at hdb
    have : n ≤ L := by omega
    omega
  -- per-iteration move: `T (j+1) → T j` for `j < n`, moving one bit to both dsts.
  have hiter_ex : ∀ j, j < n → ∃ t,
      runFlatTM t (Compile.moveBody2RawTM src dst1 dst2)
          { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBody2RawTM_exitLoop src dst1 dst2, tapes := [T j] } ∧
      (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
            { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] } = some ck →
        ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
        ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
        haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false) ∧
      t ≤ 36 * L + 38 := by
    intro j hj
    set m := n - (j + 1) with hm
    have hmn : m < n := by omega
    have hm1 : m + 1 = n - j := by omega
    have hmlen : m < (s.get src).length := by rw [← hn]; exact hmn
    have hdc : (s.get src).drop m = (s.get src)[m] :: (s.get src).drop (m + 1) :=
      List.drop_eq_getElem_cons hmlen
    have hb1 : (s.get src)[m] ≤ 1 := hv_bit _ (List.getElem_mem hmlen)
    have hsrc_cons : (st m).get src = (s.get src)[m] :: (s.get src).drop (m + 1) := by
      rw [hget_src_st]; exact hdc
    obtain ⟨t, hr, ht, hbnd⟩ := Compile.moveBody2_delete_run (st m) src dst1 dst2 ((s.get src)[m])
      ((s.get src).drop (m + 1)) hsrc_cons hb1 hsd1 hsd2 hd12 (hbit_st m)
      (by rw [hlen_st]; exact hsrc) (by rw [hlen_st]; exact hdst1) (by rw [hlen_st]; exact hdst2)
      (res_in ++ List.replicate m 0)
      (Compile.ValidResidue_append_replicate_zero res_in m hres)
    -- bridge the dual-move output to `T j` (3-register reshuffle).
    have hsrcQ : ∀ (m' : Nat), src < ((s.set dst1 (s.get dst1 ++ (s.get src).take m')).set dst2
        (s.get dst2 ++ (s.get src).take m')).length := fun m' => by rw [hlenQ]; exact hsrc
    have hstate_eq : (((st m).set src ((s.get src).drop (m + 1))).set dst1
          ((st m).get dst1 ++ [(s.get src)[m]])).set dst2 ((st m).get dst2 ++ [(s.get src)[m]])
        = st (n - j) := by
      rw [hget_dst1_st, hget_dst2_st, ← hm1,
          show (s.get dst1 ++ (s.get src).take m) ++ [(s.get src)[m]]
            = s.get dst1 ++ (s.get src).take (m + 1) from by
            rw [List.append_assoc, List.take_succ_eq_append_getElem hmlen],
          show (s.get dst2 ++ (s.get src).take m) ++ [(s.get src)[m]]
            = s.get dst2 ++ (s.get src).take (m + 1) from by
            rw [List.append_assoc, List.take_succ_eq_append_getElem hmlen]]
      simp only [hstdef]
      -- normalize LHS to `((s.set dst1 X).set dst2 Y).set src Z`.
      rw [Compile.set_set _ src _ _ (hsrcQ m)]
      rw [Compile.set_comm _ dst1 dst2 _ _ (by rw [Compile.length_set _ src _ (hsrcQ m), hlenQ]; exact hdst1)
            (by rw [Compile.length_set _ src _ (hsrcQ m), hlenQ]; exact hdst2) hd12]
      rw [Compile.set_comm _ src dst2 _ _ (hsrcQ m)
            (by rw [hlenQ]; exact hdst2) hsd2]
      rw [Compile.set_set _ dst2 _ _ (by rw [hlenP]; exact hdst2)]
      rw [Compile.set_comm _ src dst1 _ _ (by rw [Compile.length_set _ dst2 _ (by rw [hlenP]; exact hdst2), hlenP]; exact hsrc)
            (by rw [Compile.length_set _ dst2 _ (by rw [hlenP]; exact hdst2), hlenP]; exact hdst1) hsd1]
      rw [Compile.set_comm _ dst2 dst1 _ _ (by rw [hlenP]; exact hdst2)
            (by rw [hlenP]; exact hdst1) (Ne.symm hd12)]
      rw [Compile.set_set _ dst1 _ _ hdst1]
    have hres_eq : (res_in ++ List.replicate m 0) ++ [0] = res_in ++ List.replicate (n - j) 0 := by
      rw [List.append_assoc, ← List.replicate_succ', hm1]
    rw [hstate_eq, hres_eq] at hr
    have hlenj := hTlen (j + 1) (by omega)
    simp only [hTdef] at hlenj
    rw [show n - (j + 1) = m from rfl] at hlenj
    rw [hlenj] at hbnd
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact hr
    · rw [hBstart]; simp only [hTdef]; rw [show n - (j + 1) = m from rfl]; exact ht
    · have : m ≤ n := by omega
      omega
  set tIter : Nat → Nat := fun j => if hj : j < n then (hiter_ex j hj).choose else 0 with htIter
  have h_done_full :
      runFlatTM tDone (Compile.moveBody2RawTM src dst1 dst2)
          { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T 0] }
        = some { state_idx := Compile.moveBody2RawTM_exitDone src dst1 dst2, tapes := [T 0] } ∧
      (∀ k, k < tDone → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false) := by
    refine ⟨?_, ?_⟩
    · rw [hBstart, hT0]; exact hdr
    · rw [hBstart, hT0]; exact hdt
  have h_iter_full : ∀ j, j < n →
      runFlatTM (tIter j) (Compile.moveBody2RawTM src dst1 dst2)
          { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.moveBody2RawTM_exitLoop src dst1 dst2, tapes := [T j] } ∧
      (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (Compile.moveBody2RawTM src dst1 dst2)
              { state_idx := (Compile.moveBody2RawTM src dst1 dst2).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ Compile.moveBody2RawTM_exitDone src dst1 dst2 ∧
          ck.state_idx ≠ Compile.moveBody2RawTM_exitLoop src dst1 dst2 ∧
          haltingStateReached (Compile.moveBody2RawTM src dst1 dst2) ck = false) := by
    intro j hj
    have hspec := (hiter_ex j hj).choose_spec
    simp only [htIter, dif_pos hj]
    exact ⟨hspec.1, hspec.2.1⟩
  have h_iter_bnd : ∀ j, j < n → tIter j + 1 ≤ 36 * L + 39 := by
    intro j hj
    have hb := (hiter_ex j hj).choose_spec.2.2
    simp only [htIter, dif_pos hj]
    omega
  have hmain := loopTM_run (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)
    (Compile.moveBody2RawTM_valid src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_lt src dst1 dst2) (Compile.moveBody2RawTM_exitLoop_lt src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_ne_exitLoop src dst1 dst2) T h_sym tIter tDone h_done_full n h_iter_full
  have hmain_traj := loopTM_no_early_halt (Compile.moveBody2RawTM src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone src dst1 dst2) (Compile.moveBody2RawTM_exitLoop src dst1 dst2)
    (Compile.moveBody2RawTM_valid src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_lt src dst1 dst2) (Compile.moveBody2RawTM_exitLoop_lt src dst1 dst2)
    (Compile.moveBody2RawTM_exitDone_ne_exitLoop src dst1 dst2) T h_sym tIter tDone h_done_full n h_iter_full
  have hTn : T n = ([], 0, Compile.encodeTape s ++ res_in) := by
    simp only [hTdef, Nat.sub_self]
    rw [hstdef]
    simp only [List.take_zero, List.drop_zero, List.append_nil, List.replicate_zero]
    rw [Compile.set_get_self s dst1 hdst1, Compile.set_get_self s dst2 hdst2,
        Compile.set_get_self s src hsrc]
  have hTfin : T 0 = ([], 0, Compile.encodeTape
      (((s.set dst1 (s.get dst1 ++ s.get src)).set dst2 (s.get dst2 ++ s.get src)).set src [])
      ++ (res_in ++ List.replicate n 0)) := by
    simp only [hTdef, Nat.sub_zero, hstdef]
    rw [show (s.get src).take n = s.get src from by rw [hn]; exact List.take_length,
        show (s.get src).drop n = [] from by rw [hn]; exact List.drop_length]
  rw [hBstart, hTn, hTfin] at hmain
  rw [hBstart, hTn] at hmain_traj
  have hMeq : Compile.moveRegion2TM src dst1 dst2
      = loopTM (Compile.moveBody2RawTM src dst1 dst2) (Compile.moveBody2RawTM_exitDone src dst1 dst2)
          (Compile.moveBody2RawTM_exitLoop src dst1 dst2) := rfl
  have hExeq : Compile.moveRegion2TM_exit src dst1 dst2 = (Compile.moveBody2RawTM src dst1 dst2).states := rfl
  have hexit_halt : (Compile.moveRegion2TM src dst1 dst2).halt[(Compile.moveBody2RawTM src dst1 dst2).states]?
      = some true := by
    rw [hMeq]
    show (loopHalt (Compile.moveBody2RawTM src dst1 dst2))[(Compile.moveBody2RawTM src dst1 dst2).states]? = some true
    show (List.replicate (Compile.moveBody2RawTM src dst1 dst2).states false ++ [true])[(Compile.moveBody2RawTM src dst1 dst2).states]?
        = some true
    rw [List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  refine ⟨loopBudget tIter tDone n, ?_, ?_, ?_⟩
  · rw [hMeq, hExeq]; exact hmain
  · intro k hk ck hck
    rw [hMeq] at hck
    have hh := hmain_traj k hk ck hck
    refine ⟨?_, hh⟩
    rw [hExeq]
    rw [hMeq] at hexit_halt
    exact ClearGadget.ne_of_not_halting hexit_halt hh
  · rw [hLdef] at hnL ⊢
    exact le_trans
      (Compile.loopBudget_le tIter tDone (36 * L + 39) n h_done_bnd h_iter_bnd)
      (by rw [← hLdef]; exact Compile.moveBudget2_arith n L (by rw [hLdef]; exact hnL))

/-- **`clearAppendM` run + no-early-halt + budget.** From head `0` on
`encodeTape s ++ res`, clearing register `dst` then appending bit `bit` reaches
the unique exit at head `0` with tape `encodeTape (s.set dst [bit]) ++ res'`
(`res' = res ++ replicate |s.get dst| 0`). The tape length is preserved, so the
append's budget is `≤ 3·L + 8` and the total is `≤ 9·L² + 3·L + 18`. -/
theorem Compile.clearAppendM_run (s : State) (dst : Var) (bit : Nat) (hb : bit ≤ 1)
    (hdst : dst < s.length) (hbit : Compile.BitState s) (res : List Nat)
    (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.clearAppendM dst (bit + 1) (by omega))
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.clearAppendM_exit dst (bit + 1) (by omega),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [bit])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.clearAppendM dst (bit + 1) (by omega))
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.clearAppendM dst (bit + 1) (by omega)) ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 3 * (Compile.encodeTape s ++ res).length + 18 := by
  set res' := res ++ List.replicate (s.get dst).length 0 with hres'def
  have hmid_bit : Compile.BitState (s.set dst []) :=
    Compile.BitState_set s dst [] hbit hdst (by intro x hx; cases hx)
  have hmid_len : dst < (s.set dst []).length := by
    rw [Compile.length_set s dst [] hdst]; exact hdst
  have hres' : Compile.ValidResidue res' :=
    Compile.ValidResidue_append_replicate_zero res _ hres
  have hget : (s.set dst []).get dst = [] := Compile.get_set_eq s dst [] hdst
  have hset : (s.set dst []).set dst [bit] = s.set dst [bit] := Compile.set_set s dst [] [bit] hdst
  -- tape length preserved across clear: |encodeTape (s.set dst []) ++ res'| = |encodeTape s ++ res|
  have hlen_eq : (Compile.encodeTape (s.set dst []) ++ res').length
      = (Compile.encodeTape s ++ res).length := by
    have hbal := Compile.encodeTape_set_length s dst [] hdst
    simp only [List.length_nil, Nat.add_zero] at hbal
    simp only [hres'def, List.length_append, List.length_replicate]
    omega
  obtain ⟨t1, hrun1, htraj1, hbud1⟩ := Compile.clearRegionTM_run s dst res hdst hbit hres
  obtain ⟨t2, hrun2, htraj2, hbud2⟩ :=
    Compile.opAppendBit_physical_residue bit hb (s.set dst []) dst hmid_bit hmid_len res' hres'
  -- clean the append output tape: (s.set dst []).set dst ([] ++ [bit]) = s.set dst [bit]
  rw [hget, List.nil_append, hset] at hrun2
  -- expose the explicit start config of `opAppendBitRewind` (initFlatConfig form)
  simp only [initFlatConfig, List.map_cons, List.map_nil] at hrun2
  -- `clearRegionTM`'s exit tape is `encodeTape (s.set dst []) ++ res'` (defeq Op.eval)
  have hmid_eval : Op.eval (Op.clear dst) s = s.set dst [] := rfl
  rw [hmid_eval] at hrun1
  -- symbol bound at the seam
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape (s.set dst []) ++ res')
      = some v → v < max (ClearGadget.clearRegionTM dst).sig
        (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M.sig := by
    intro v hv
    have hmax : max (ClearGadget.clearRegionTM dst).sig
        (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M.sig = 4 := by
      rw [ClearGadget.clearRegionTM_sig, (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M_sig]
      rfl
    rw [hmax]
    have hlt : 0 < (Compile.encodeTape (s.set dst []) ++ res').length := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have hcell : (Compile.encodeTape (s.set dst []) ++ res').get ⟨0, hlt⟩ = 3 := rfl
    rw [hcell] at hv
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_cfg_lt : (0 : Nat) < (ClearGadget.clearRegionTM dst).states := by
    rw [ClearGadget.clearRegionTM_states]; exact Nat.succ_pos _
  have hcompose := composeFlatTM_run (ClearGadget.clearRegionTM_valid dst)
    (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M_valid
    (Compile.clearRegionTM_exit_lt dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    h_cfg_lt
    [] 0 (Compile.encodeTape (s.set dst []) ++ res') h_sym
    hrun1
    (fun k hk ck hck => htraj1 k hk ck hck)
    hrun2
    (Compile.haltingStateReached_of_halt (Compile.opAppendBitRewind (bit + 1) (by omega) dst).exit_is_halt)
  have hcompose_traj := composeFlatTM_no_early_halt (ClearGadget.clearRegionTM_valid dst)
    (Compile.opAppendBitRewind (bit + 1) (by omega) dst).M_valid
    (Compile.clearRegionTM_exit_lt dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    h_cfg_lt
    [] 0 (Compile.encodeTape (s.set dst []) ++ res') h_sym
    hrun1
    (fun k hk ck hck => htraj1 k hk ck hck)
    (fun k hk ck hck => (htraj2 k hk ck hck).2)
  refine ⟨t1 + 1 + t2, ?_, ?_, ?_⟩
  · rw [Compile.clearAppendM, Compile.clearAppendM_exit, Nat.add_comm (ClearGadget.clearRegionTM dst).states]
    exact hcompose.1
  · intro k hk ck hck
    rw [Compile.clearAppendM] at hck ⊢
    exact hcompose_traj k hk ck hck
  · -- budget: t1 ≤ 9L²+9, t2 ≤ 3L+8 (length preserved), total ≤ 9L²+3L+18
    have hb2' : t2 ≤ 3 * (Compile.encodeTape s ++ res).length + 8 := by
      rw [← hlen_eq]; exact hbud2
    omega

/-- **`nonEmptyBranchBody` run + no-early-halt + budget.** From the `navigateAndTest`
exit config (head on register `src`'s first cell), rewind to the leading sentinel,
then clear-and-append. Exits at head `0` with `encodeTape (s.set dst [bit]) ++ res'`. -/
theorem Compile.nonEmptyBranchBody_run (s : State) (dst src : Var) (bit : Nat) (hb : bit ≤ 1)
    (hdst : dst < s.length) (hsrc : src < s.length) (hbit : Compile.BitState s)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.nonEmptyBranchBody dst (bit + 1) (by omega))
          { state_idx := 0,
            tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst (bit + 1) (by omega),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [bit])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst (bit + 1) (by omega))
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst (bit + 1) (by omega)) ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 4 * (Compile.encodeTape s ++ res).length + 19 := by
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set rest := Compile.encodeRegs s ++ [Compile.endMark] ++ res with hrestdef
  have htape_cons : Compile.encodeTape s ++ res = (3 : Nat) :: rest := by
    rw [hrestdef, Compile.encodeTape]; simp only [Compile.endMark, List.cons_append, List.append_assoc]
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  -- rewind run + trajectory
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
  -- `3 :: rest` is defeq `encodeTape s ++ res` (cons_append), so `hrw` plugs in directly.
  have hrw := ScanLeft.rewindToStart_run 4 3 [] rest H hH_le_rest hcells
  have hrw_traj := ScanLeft.rewindToStart_traj 4 3 [] rest H hH_le_rest hcells
  -- clearAppend run (head 0); convert its start to M₂.start form
  obtain ⟨t2, hca_run, hca_traj, hca_bud⟩ := Compile.clearAppendM_run s dst bit hb hdst hbit res hres
  have hca_start : (Compile.clearAppendM dst (bit + 1) (by omega)).start = 0 := by
    rw [Compile.clearAppendM, composeFlatTM_start]; exact ClearGadget.clearRegionTM_start dst
  have hca_run' : runFlatTM t2 (Compile.clearAppendM dst (bit + 1) (by omega))
      { state_idx := (Compile.clearAppendM dst (bit + 1) (by omega)).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := Compile.clearAppendM_exit dst (bit + 1) (by omega),
               tapes := [([], 0, Compile.encodeTape (s.set dst [bit])
                          ++ (res ++ List.replicate (s.get dst).length 0))] } := by
    rw [hca_start]; exact hca_run
  have hca_traj' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k (Compile.clearAppendM dst (bit + 1) (by omega))
        { state_idx := (Compile.clearAppendM dst (bit + 1) (by omega)).start,
          tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (Compile.clearAppendM dst (bit + 1) (by omega)) ck = false := by
    rw [hca_start]; exact hca_traj
  -- symbol bound at the rewind exit head (head 0 = leading sentinel)
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (ScanLeft.scanLeftUntilTM 4 3).sig
        (Compile.clearAppendM dst (bit + 1) (by omega)).sig := by
    intro v hv
    have hmax : max (ScanLeft.scanLeftUntilTM 4 3).sig
        (Compile.clearAppendM dst (bit + 1) (by omega)).sig = 4 := by
      rw [Compile.clearAppendM_sig]; rfl
    rw [hmax]
    have hlt : 0 < (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have hcell : (Compile.encodeTape s ++ res).get ⟨0, hlt⟩ = 3 := rfl
    rw [hcell] at hv
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_cfg_lt : (0 : Nat) < (ScanLeft.scanLeftUntilTM 4 3).states := by decide
  have hcompose := composeFlatTM_run (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (Compile.clearAppendM_valid dst (bit + 1) (by omega)) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck) hca_run'
    (Compile.haltingStateReached_of_halt (Compile.clearAppendM_exit_is_halt dst (bit + 1) (by omega)))
  have hcompose_traj := composeFlatTM_no_early_halt (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (Compile.clearAppendM_valid dst (bit + 1) (by omega)) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck)
    (fun k hk ck hck => hca_traj' k hk ck hck)
  refine ⟨(H + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [Compile.nonEmptyBranchBody, Compile.nonEmptyBranchBody_exit,
        Nat.add_comm (ScanLeft.scanLeftUntilTM 4 3).states]
    exact hcompose.1
  · intro k hk ck hck
    rw [Compile.nonEmptyBranchBody] at hck ⊢
    exact hcompose_traj k hk ck hck
  · -- budget: rewind H+1 ≤ L, clearAppend ≤ 9L²+3L+18 ⇒ total ≤ 9L²+4L+19
    have hH_le_L : H + 1 ≤ (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]
      have h1 := hH_le_regs
      have h2 := Compile.encodeRegs_length s
      omega
    omega

/-- **`opNonEmpty` run + trajectory + budget (the residue contract for `nonEmpty`).**
Navtest `src`; the answer bit (`1` if non-empty else `0`) is written to a freshly
cleared register `dst`; the two branches merge through `joinTwoHalts`. Correct for
`dst = src` (the read precedes the clear). -/
theorem Compile.opNonEmpty_run (s : State) (dst src : Var) (res_in : List Nat)
    (hbit : Compile.BitState s) (hdst : dst < s.length) (hsrc : src < s.length)
    (hres_in : Compile.ValidResidue res_in) :
    ∃ t,
      runFlatTM t (Compile.opNonEmpty dst src).M
          (initFlatConfig (Compile.opNonEmpty dst src).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opNonEmpty dst src).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval (Op.nonEmpty dst src) s)
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opNonEmpty dst src).M
            (initFlatConfig (Compile.opNonEmpty dst src).M [Compile.encodeTape s ++ res_in]) = some ck →
        ck.state_idx ≠ (Compile.opNonEmpty dst src).exit ∧
        haltingStateReached (Compile.opNonEmpty dst src).M ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
            + 9 * (Compile.encodeTape s ++ res_in).length + 30 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.nonEmptyRawM dst src with hrawdef
  set h1 := Compile.nonEmptyRawM_h1 dst src with hh1def
  set h2 := Compile.nonEmptyRawM_h2 dst src with hh2def
  have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
      (Compile.nonEmptyBranchBody dst 2 (by decide)) (Compile.nonEmptyBranchBody dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content src)
      (ClearGadget.navigateAndTestTM_exit_delim src) = raw := rfl
  -- machine boilerplate: init config, exit, M.
  have hMstart : (Compile.opNonEmpty dst src).M.start = 0 := by
    show (joinTwoHalts raw h1 h2).start = 0
    rw [joinTwoHalts_start, hrawdef, Compile.nonEmptyRawM, branchComposeFlatTM_start]
    exact ClearGadget.navigateAndTestTM_start src
  have hinit : initFlatConfig (Compile.opNonEmpty dst src).M [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hMstart, List.map_cons, List.map_nil]
  have hMeq : (Compile.opNonEmpty dst src).M = joinTwoHalts raw h1 h2 := rfl
  have hexit : (Compile.opNonEmpty dst src).exit = h1 := rfl
  rw [hinit, hMeq, hexit]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    with hcfg0
  -- length facts.
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res_in).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  have hnav_le : ClearGadget.navSteps skipped ≤ 2 * (Compile.encodeRegs s).length := by
    have := ClearGadget.navSteps_le skipped
    rw [hHdef] at hH_le_regs; omega
  -- the branch-tape symbol bound (head H lands inside `encodeTape s`).
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res_in)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.nonEmptyBranchBody dst 2 (by decide)).sig
            (Compile.nonEmptyBranchBody dst 1 (by decide)).sig) := by
    intro v hv
    have hHlt2 : H < (Compile.encodeTape s).length := by
      rw [Compile.encodeTape_length]
      have h := hH_le_regs
      rw [Compile.encodeRegs_length] at h
      omega
    have hHlt : H < (Compile.encodeTape s ++ res_in).length := by
      rw [List.length_append]; omega
    rw [currentTapeSymbol_in_range hHlt] at hv
    have hmem : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ ∈ Compile.encodeTape s := by
      rw [List.get_eq_getElem, List.getElem_append_left hHlt2]; exact List.getElem_mem hHlt2
    have hv4 : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ < 4 :=
      Compile.encodeTape_lt_four s hbit _ hmem
    have : v < (ClearGadget.navigateAndTestTM src).sig := by
      rw [ClearGadget.navigateAndTestTM_sig, ← Option.some.inj hv]; exact hv4
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hbstart : ∀ ins (h : ins < 4), (Compile.nonEmptyBranchBody dst ins h).start = 0 := by
    intro ins h; rw [Compile.nonEmptyBranchBody, composeFlatTM_start]; rfl
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hh1_is := Compile.nonEmptyRawM_h1_is_halt dst src
  have hh2_is := Compile.nonEmptyRawM_h2_is_halt dst src
  have hh_ne := Compile.nonEmptyRawM_h1_ne_h2 dst src
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  by_cases he : s.get src = []
  · -- DELIM: answer bit 0, Op.eval = s.set dst [0]; raw reaches h2, bridges to h1.
    have hisE : Op.eval (Op.nonEmpty dst src) s = s.set dst [0] := by
      show s.set dst (if (s.get src).isEmpty then [0] else [1]) = s.set dst [0]
      rw [he]; rfl
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 0 (by omega) hdst hsrc hbit res_in hres_in
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 1 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 1 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [0])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 1 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 1 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 1 (by decide)) ck = false := by
      rw [hbstart 1 (by decide)]; exact hbody_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 1 (by decide)))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody_traj'
    -- recognise the branch machine/state as raw/h2.
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 1 (by decide)
        + ((ClearGadget.navigateAndTestTM src).states
            + (Compile.nonEmptyBranchBody dst 2 (by decide)).states) = h2 := by
      rw [hh2def, Compile.nonEmptyRawM_h2]; omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (s.set dst [0]) ++ (res_in ++ List.replicate (s.get dst).length 0)) 0
      hneg.1
      (fun k hk ck hck => hneg_traj k hk ck hck)
      hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (s.set dst [0]) ++ (res_in ++ List.replicate (s.get dst).length 0))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.nonEmptyRawM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega
  · -- CONTENT: answer bit 1, Op.eval = s.set dst [1]; raw reaches h1 directly.
    have hisE : Op.eval (Op.nonEmpty dst src) s = s.set dst [1] := by
      show s.set dst (if (s.get src).isEmpty then [0] else [1]) = s.set dst [1]
      have : (s.get src).isEmpty = false := by
        cases hsr : s.get src with
        | nil => exact absurd hsr he
        | cons _ _ => rfl
      rw [this]; rfl
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 1 (by omega) hdst hsrc hbit res_in hres_in
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 2 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 2 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [1])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 2 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 2 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 2 (by decide)) ck = false := by
      rw [hbstart 2 (by decide)]; exact hbody_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 2 (by decide)))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody_traj'
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 2 (by decide)
        + (ClearGadget.navigateAndTestTM src).states = h1 := by
      rw [hh1def, Compile.nonEmptyRawM_h1]; omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (s.set dst [1]) ++ (res_in ++ List.replicate (s.get dst).length 0))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega

/-- **`clearOnlyBranchBody` run + no-early-halt + budget.** From the navtest exit
config (head on register `src`'s first cell), rewind to the leading sentinel, then
clear `dst`. Exits at head `0` with `encodeTape (s.set dst []) ++ res'`. Mirror of
`nonEmptyBranchBody_run` with `clearRegionTM` in place of `clearAppendM`. -/
theorem Compile.clearOnlyBranchBody_run (s : State) (dst src : Var)
    (hdst : dst < s.length) (hsrc : src < s.length) (hbit : Compile.BitState s)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.clearOnlyBranchBody dst)
          { state_idx := 0,
            tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.clearOnlyBranchBody_exit dst,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.clearOnlyBranchBody dst)
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.clearOnlyBranchBody dst) ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 4 * (Compile.encodeTape s ++ res).length + 19 := by
  set H := 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length with hHdef
  set rest := Compile.encodeRegs s ++ [Compile.endMark] ++ res with hrestdef
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
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
  have hrw := ScanLeft.rewindToStart_run 4 3 [] rest H hH_le_rest hcells
  have hrw_traj := ScanLeft.rewindToStart_traj 4 3 [] rest H hH_le_rest hcells
  obtain ⟨t2, hcl_run, hcl_traj, hcl_bud⟩ := Compile.clearRegionTM_run s dst res hdst hbit hres
  have hcl_eval : Op.eval (Op.clear dst) s = s.set dst [] := rfl
  rw [hcl_eval] at hcl_run
  have hcl_start : (ClearGadget.clearRegionTM dst).start = 0 := ClearGadget.clearRegionTM_start dst
  have hcl_run' : runFlatTM t2 (ClearGadget.clearRegionTM dst)
      { state_idx := (ClearGadget.clearRegionTM dst).start,
        tapes := [([], 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := ClearGadget.clearRegionTM_exit dst,
               tapes := [([], 0, Compile.encodeTape (s.set dst [])
                          ++ (res ++ List.replicate (s.get dst).length 0))] } := by
    rw [hcl_start]; exact hcl_run
  have hcl_traj' : ∀ k, k < t2 → ∀ ck,
      runFlatTM k (ClearGadget.clearRegionTM dst)
        { state_idx := (ClearGadget.clearRegionTM dst).start,
          tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
      haltingStateReached (ClearGadget.clearRegionTM dst) ck = false := by
    rw [hcl_start]; intro k hk ck hck; exact (hcl_traj k hk ck hck).2
  have h_sym : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res) = some v →
      v < max (ScanLeft.scanLeftUntilTM 4 3).sig (ClearGadget.clearRegionTM dst).sig := by
    intro v hv
    have hmax : max (ScanLeft.scanLeftUntilTM 4 3).sig (ClearGadget.clearRegionTM dst).sig = 4 := by
      rw [ClearGadget.clearRegionTM_sig]; rfl
    rw [hmax]
    have hlt : 0 < (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have hcell : (Compile.encodeTape s ++ res).get ⟨0, hlt⟩ = 3 := rfl
    rw [hcell] at hv
    have : v = 3 := (Option.some.inj hv).symm
    omega
  have h_cfg_lt : (0 : Nat) < (ScanLeft.scanLeftUntilTM 4 3).states := by decide
  have hcompose := composeFlatTM_run (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (ClearGadget.clearRegionTM_valid dst) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck) hcl_run'
    (Compile.haltingStateReached_of_halt (Compile.opClear dst).exit_is_halt)
  have hcompose_traj := composeFlatTM_no_early_halt (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (ClearGadget.clearRegionTM_valid dst) (by decide)
    { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    h_cfg_lt [] 0 (Compile.encodeTape s ++ res) h_sym hrw
    (fun k hk ck hck => hrw_traj k hk ck hck)
    (fun k hk ck hck => hcl_traj' k hk ck hck)
  refine ⟨(H + 1) + 1 + t2, ?_, ?_, ?_⟩
  · rw [Compile.clearOnlyBranchBody, Compile.clearOnlyBranchBody_exit,
        Nat.add_comm (ScanLeft.scanLeftUntilTM 4 3).states]
    exact hcompose.1
  · intro k hk ck hck
    rw [Compile.clearOnlyBranchBody] at hck ⊢
    exact hcompose_traj k hk ck hck
  · have hH_le_L : H + 1 ≤ (Compile.encodeTape s ++ res).length := by
      rw [List.length_append, Compile.encodeTape_length]
      have h1 := hH_le_regs
      have h2 := Compile.encodeRegs_length s
      omega
    omega

/-- **`opInnerBit` run + trajectory + budget.** From the navtest content exit
(head on `src`'s first cell, value `b+1`), `bitReadTM` reads the bit and writes
`[b]` to a freshly-cleared `dst`. The two `bitReadTM` exits merge via
`joinTwoHalts`. Requires `src` non-empty (`s.get src = b :: r`). -/
theorem Compile.opInnerBit_run (s : State) (dst src : Var) (b : Nat) (r : List Nat)
    (hbr : s.get src = b :: r) (hb1 : b ≤ 1)
    (hbit : Compile.BitState s) (hdst : dst < s.length) (hsrc : src < s.length)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.opInnerBit dst).M
          { state_idx := 0,
            tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := (Compile.opInnerBit dst).exit,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [b])
                            ++ (res ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opInnerBit dst).M
            { state_idx := 0,
              tapes := [([], 1 + (AppendGadget.regBlocks ((s.take src).map Compile.shiftReg)).length,
                         Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ (Compile.opInnerBit dst).exit ∧
        haltingStateReached (Compile.opInnerBit dst).M ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res).length * (Compile.encodeTape s ++ res).length
            + 5 * (Compile.encodeTape s ++ res).length + 24 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.innerBitRawM dst with hrawdef
  set h1 := Compile.innerBitRawM_h1 dst with hh1def
  set h2 := Compile.innerBitRawM_h2 dst with hh2def
  have hraweq : branchComposeFlatTM Compile.bitReadTM
      (Compile.nonEmptyBranchBody dst 2 (by decide)) (Compile.nonEmptyBranchBody dst 1 (by decide))
      Compile.bitReadTM_exit_b1 Compile.bitReadTM_exit_b0 = raw := rfl
  have hMeq : (Compile.opInnerBit dst).M = joinTwoHalts raw h1 h2 := rfl
  have hexit : (Compile.opInnerBit dst).exit = h1 := rfl
  rw [hMeq, hexit]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, Compile.encodeTape s ++ res)] }
    with hcfg0
  -- length facts.
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  -- content decomposition (`src` nonempty)
  set tail' := Compile.shiftReg r ++ 0 :: (Compile.encodeRegs (s.drop (src + 1))
      ++ [Compile.endMark] ++ res) with htail
  have hdecomp : Compile.encodeTape s ++ res
      = (3 : Nat) :: (AppendGadget.regBlocks skipped ++ (b + 1) :: tail') := by
    have hsplit := Compile.encodeTape_split s src hsrc
    rw [← hskdef] at hsplit
    have hsr : Compile.shiftReg (s.get src) = (b + 1) :: Compile.shiftReg r := by
      rw [hbr]; simp only [Compile.shiftReg, List.map_cons]
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
  -- symbol bound at head H (cell value `b+1 < 4`).
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res)
      = some v → v < max Compile.bitReadTM.sig
          (max (Compile.nonEmptyBranchBody dst 2 (by decide)).sig
            (Compile.nonEmptyBranchBody dst 1 (by decide)).sig) := by
    intro v hv
    rw [currentTapeSymbol_in_range hHlt, hcellH] at hv
    have : v = b + 1 := (Option.some.inj hv).symm
    rw [Compile.bitReadTM_sig]
    have : v < 4 := by omega
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < Compile.bitReadTM.states := by rw [Compile.bitReadTM_states]; omega
  have hbstart : ∀ ins (h : ins < 4), (Compile.nonEmptyBranchBody dst ins h).start = 0 := by
    intro ins h; rw [Compile.nonEmptyBranchBody, composeFlatTM_start]; rfl
  have hexit_neq : Compile.bitReadTM_exit_b1 ≠ Compile.bitReadTM_exit_b0 := by decide
  have hep_lt : Compile.bitReadTM_exit_b1 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b1]; decide
  have hen_lt : Compile.bitReadTM_exit_b0 < Compile.bitReadTM.states := by
    rw [Compile.bitReadTM_states, Compile.bitReadTM_exit_b0]; decide
  have hh1_is := Compile.innerBitRawM_h1_is_halt dst
  have hh2_is := Compile.innerBitRawM_h2_is_halt dst
  have hh_ne := Compile.innerBitRawM_h1_ne_h2 dst
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  -- the `bitReadTM` test run + trajectory (reads cell `b+1` at head H).
  have htest_run := Compile.bitReadTM_run b hb1 [] (Compile.encodeTape s ++ res) H hHlt hcellH
  have htest_traj : ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.bitReadTM cfg0 = some ck →
      ck.state_idx ≠ Compile.bitReadTM_exit_b1 ∧ ck.state_idx ≠ Compile.bitReadTM_exit_b0 ∧
      haltingStateReached Compile.bitReadTM ck = false := by
    intro k hk ck hck
    obtain ⟨h0, h1', hh⟩ := Compile.bitReadTM_no_early_halt [] (Compile.encodeTape s ++ res) H k hk ck hck
    exact ⟨h1', h0, hh⟩
  interval_cases b
  · -- bit 0 (cell value 1): neg branch, body `dst 1` writes `[0]`; demoted exit.
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 0 (by omega) hdst hsrc hbit res hres
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 1 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 1 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [0])
                            ++ (res ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 1 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 1 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 1 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 1 (by decide)) ck = false := by
      rw [hbstart 1 (by decide)]; exact hbody_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 1 (by decide)))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody_traj'
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 1 (by decide)
        + (Compile.bitReadTM.states + (Compile.nonEmptyBranchBody dst 2 (by decide)).states) = h2 := by
      rw [hh2def, Compile.innerBitRawM_h2]; omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (s.set dst [0]) ++ (res ++ List.replicate (s.get dst).length 0)) 0
      hneg.1
      (fun k hk ck hck => hneg_traj k hk ck hck)
      hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (s.set dst [0]) ++ (res ++ List.replicate (s.get dst).length 0))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.innerBitRawM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hb := hbody_bud
    have hL := hLge
    omega
  · -- bit 1 (cell value 2): pos branch, body `dst 2` writes `[1]`; kept exit.
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.nonEmptyBranchBody_run s dst src 1 (by omega) hdst hsrc hbit res hres
    have hbody' : runFlatTM t2 (Compile.nonEmptyBranchBody dst 2 (by decide))
        { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
          tapes := [([], H, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.nonEmptyBranchBody_exit dst 2 (by decide),
                 tapes := [([], 0, Compile.encodeTape (s.set dst [1])
                            ++ (res ++ List.replicate (s.get dst).length 0))] } := by
      rw [hbstart 2 (by decide)]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.nonEmptyBranchBody dst 2 (by decide))
          { state_idx := (Compile.nonEmptyBranchBody dst 2 (by decide)).start,
            tapes := [([], H, Compile.encodeTape s ++ res)] } = some ck →
        haltingStateReached (Compile.nonEmptyBranchBody dst 2 (by decide)) ck = false := by
      rw [hbstart 2 (by decide)]; exact hbody_traj
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody'
      (Compile.haltingStateReached_of_halt (Compile.nonEmptyBranchBody_exit_is_halt dst 2 (by decide)))
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      Compile.bitReadTM_valid
      (Compile.nonEmptyBranchBody_valid dst 2 (by decide))
      (Compile.nonEmptyBranchBody_valid dst 1 (by decide))
      hep_lt hen_lt cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res) hbranch_sym
      htest_run htest_traj hbody_traj'
    have hstate_eq : Compile.nonEmptyBranchBody_exit dst 2 (by decide)
        + Compile.bitReadTM.states = h1 := by
      rw [hh1def, Compile.innerBitRawM_h1]; omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (s.set dst [1]) ++ (res ++ List.replicate (s.get dst).length 0))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, hjoin, hjoin_traj, ?_⟩
    have hb := hbody_bud
    have hL := hLge
    omega

/-- **`opHead` run + trajectory + budget (the residue contract for `head`).**
Navtest `src`; on content, `opInnerBit` writes `[first bit]`; on delim,
`clearOnlyBranchBody` writes `[]`. The outer branches merge through `joinTwoHalts`. -/
theorem Compile.opHead_run (s : State) (dst src : Var) (res_in : List Nat)
    (hbit : Compile.BitState s) (hdst : dst < s.length) (hsrc : src < s.length)
    (hres_in : Compile.ValidResidue res_in) :
    ∃ t,
      runFlatTM t (Compile.opHead dst src).M
          (initFlatConfig (Compile.opHead dst src).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opHead dst src).exit,
                 tapes := [([], 0, Compile.encodeTape (Op.eval (Op.head dst src) s)
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opHead dst src).M
            (initFlatConfig (Compile.opHead dst src).M [Compile.encodeTape s ++ res_in]) = some ck →
        ck.state_idx ≠ (Compile.opHead dst src).exit ∧
        haltingStateReached (Compile.opHead dst src).M ck = false)
    ∧ t ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
            + 9 * (Compile.encodeTape s ++ res_in).length + 30 := by
  set skipped := (s.take src).map Compile.shiftReg with hskdef
  set H := 1 + (AppendGadget.regBlocks skipped).length with hHdef
  set raw := Compile.headRawM dst src with hrawdef
  set h1 := Compile.headRawM_h1 dst src with hh1def
  set h2 := Compile.headRawM_h2 dst src with hh2def
  have hraweq : branchComposeFlatTM (ClearGadget.navigateAndTestTM src)
      (Compile.opInnerBit dst).M (Compile.clearOnlyBranchBody dst)
      (ClearGadget.navigateAndTestTM_exit_content src)
      (ClearGadget.navigateAndTestTM_exit_delim src) = raw := rfl
  have hMstart : (Compile.opHead dst src).M.start = 0 := by
    show (joinTwoHalts raw h1 h2).start = 0
    rw [joinTwoHalts_start, hrawdef, Compile.headRawM, branchComposeFlatTM_start]
    exact ClearGadget.navigateAndTestTM_start src
  have hinit : initFlatConfig (Compile.opHead dst src).M [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hMstart, List.map_cons, List.map_nil]
  have hMeq : (Compile.opHead dst src).M = joinTwoHalts raw h1 h2 := rfl
  have hexit : (Compile.opHead dst src).exit = h1 := rfl
  rw [hinit, hMeq, hexit]
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    with hcfg0
  have hLge : (Compile.encodeRegs s).length + 2 ≤ (Compile.encodeTape s ++ res_in).length := by
    rw [List.length_append, Compile.encodeTape_length, Compile.encodeRegs_length]; omega
  have hH_le_regs : H ≤ (Compile.encodeRegs s).length := by
    have hlen := congrArg List.length (Compile.encodeTape_split s src hsrc)
    rw [← hskdef, Compile.regBlocks_map_shiftReg] at hlen
    simp only [List.length_append, List.length_cons] at hlen
    rw [hHdef, Compile.regBlocks_map_shiftReg]
    omega
  have hnav_le : ClearGadget.navSteps skipped ≤ 2 * (Compile.encodeRegs s).length := by
    have := ClearGadget.navSteps_le skipped
    rw [hHdef] at hH_le_regs; omega
  have hbranch_sym : ∀ v, currentTapeSymbol (([] : List Nat), H, Compile.encodeTape s ++ res_in)
      = some v → v < max (ClearGadget.navigateAndTestTM src).sig
          (max (Compile.opInnerBit dst).M.sig (Compile.clearOnlyBranchBody dst).sig) := by
    intro v hv
    have hHlt2 : H < (Compile.encodeTape s).length := by
      rw [Compile.encodeTape_length]
      have h := hH_le_regs
      rw [Compile.encodeRegs_length] at h
      omega
    have hHlt : H < (Compile.encodeTape s ++ res_in).length := by
      rw [List.length_append]; omega
    rw [currentTapeSymbol_in_range hHlt] at hv
    have hmem : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ ∈ Compile.encodeTape s := by
      rw [List.get_eq_getElem, List.getElem_append_left hHlt2]; exact List.getElem_mem hHlt2
    have hv4 : (Compile.encodeTape s ++ res_in).get ⟨H, hHlt⟩ < 4 :=
      Compile.encodeTape_lt_four s hbit _ hmem
    have : v < (ClearGadget.navigateAndTestTM src).sig := by
      rw [ClearGadget.navigateAndTestTM_sig, ← Option.some.inj hv]; exact hv4
    exact lt_of_lt_of_le this (le_max_left _ _)
  have h_cfg_lt : (0 : Nat) < (ClearGadget.navigateAndTestTM src).states := by
    rw [ClearGadget.navigateAndTestTM_states]; omega
  have hexit_neq : ClearGadget.navigateAndTestTM_exit_content src
      ≠ ClearGadget.navigateAndTestTM_exit_delim src := by
    show (ClearGadget.navigateToRegTM src).states + 1 ≠ (ClearGadget.navigateToRegTM src).states + 2
    omega
  have hh1_is := Compile.headRawM_h1_is_halt dst src
  have hh2_is := Compile.headRawM_h2_is_halt dst src
  have hh_ne := Compile.headRawM_h1_ne_h2 dst src
  rw [← hrawdef] at hh1_is hh2_is
  rw [← hh1def] at hh1_is hh_ne
  rw [← hh2def] at hh2_is hh_ne
  by_cases he : s.get src = []
  · -- DELIM: Op.eval head = s.set dst []; raw reaches h2 (delim), bridges to h1.
    have hisE : Op.eval (Op.head dst src) s = s.set dst [] := by
      show s.set dst (match s.get src with | [] => [] | x :: _ => [x]) = s.set dst []
      rw [he]
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.clearOnlyBranchBody_run s dst src hdst hsrc hbit res_in hres_in
    have hbody' : runFlatTM t2 (Compile.clearOnlyBranchBody dst)
        { state_idx := (Compile.clearOnlyBranchBody dst).start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := Compile.clearOnlyBranchBody_exit dst,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [show (Compile.clearOnlyBranchBody dst).start = 0 from by
            rw [Compile.clearOnlyBranchBody, composeFlatTM_start]; rfl]
      exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.clearOnlyBranchBody dst)
          { state_idx := (Compile.clearOnlyBranchBody dst).start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.clearOnlyBranchBody dst) ck = false := by
      rw [show (Compile.clearOnlyBranchBody dst).start = 0 from by
            rw [Compile.clearOnlyBranchBody, composeFlatTM_start]; rfl]
      exact hbody_traj
    have hneg := branchComposeFlatTM_run_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.clearOnlyBranchBody_exit_is_halt dst))
    have hneg_traj := branchComposeFlatTM_no_early_halt_neg hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_delim s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_delim s src res_in hsrc hbit he) hbody_traj'
    have hstate_eq : Compile.clearOnlyBranchBody_exit dst
        + ((ClearGadget.navigateAndTestTM src).states + (Compile.opInnerBit dst).M.states) = h2 := by
      rw [hh2def, Compile.headRawM_h2]; omega
    rw [hstate_eq, hraweq] at hneg
    rw [hraweq] at hneg_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_demoted raw h1 h2 cfg0
      _ [] (Compile.encodeTape (s.set dst []) ++ (res_in ++ List.replicate (s.get dst).length 0)) 0
      hneg.1
      (fun k hk ck hck => hneg_traj k hk ck hck)
      hh1_is hh2_is hh_ne
      (by
        intro v hv
        rw [show currentTapeSymbol (([] : List Nat), 0,
              Compile.encodeTape (s.set dst []) ++ (res_in ++ List.replicate (s.get dst).length 0))
            = some 3 from rfl] at hv
        rw [hrawdef, Compile.headRawM_sig]
        have : v = 3 := (Option.some.inj hv).symm
        omega)
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega
  · -- CONTENT: s.get src = b :: r; opInnerBit writes [b]; raw reaches h1 directly.
    obtain ⟨b, r, hbr⟩ : ∃ b r, s.get src = b :: r := by
      cases hsr : s.get src with
      | nil => exact absurd hsr he
      | cons b r => exact ⟨b, r, rfl⟩
    have hb1 : b ≤ 1 := by
      have hmem : s.get src ∈ s := by
        rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
      exact hbit _ hmem b (by simp [hbr])
    have hisE : Op.eval (Op.head dst src) s = s.set dst [b] := by
      show s.set dst (match s.get src with | [] => [] | x :: _ => [x]) = s.set dst [b]
      rw [hbr]
    obtain ⟨t2, hbody, hbody_traj, hbody_bud⟩ :=
      Compile.opInnerBit_run s dst src b r hbr hb1 hbit hdst hsrc res_in hres_in
    have hbody' : runFlatTM t2 (Compile.opInnerBit dst).M
        { state_idx := (Compile.opInnerBit dst).M.start,
          tapes := [([], H, Compile.encodeTape s ++ res_in)] }
        = some { state_idx := (Compile.opInnerBit dst).exit,
                 tapes := [([], 0, Compile.encodeTape (s.set dst [b])
                            ++ (res_in ++ List.replicate (s.get dst).length 0))] } := by
      rw [Compile.opInnerBit_start]; exact hbody
    have hbody_traj' : ∀ k, k < t2 → ∀ ck,
        runFlatTM k (Compile.opInnerBit dst).M
          { state_idx := (Compile.opInnerBit dst).M.start,
            tapes := [([], H, Compile.encodeTape s ++ res_in)] } = some ck →
        haltingStateReached (Compile.opInnerBit dst).M ck = false := by
      rw [Compile.opInnerBit_start]; intro k hk ck hck; exact (hbody_traj k hk ck hck).2
    have hpos := branchComposeFlatTM_run_pos hexit_neq
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody'
      (Compile.haltingStateReached_of_halt (Compile.opInnerBit dst).exit_is_halt)
    have hpos_traj := branchComposeFlatTM_no_early_halt_pos
      (ClearGadget.navigateAndTestTM_valid src)
      (Compile.opInnerBit dst).M_valid
      (Compile.clearOnlyBranchBody_valid dst)
      (ClearGadget.navigateAndTestTM_exit_content_lt src)
      (ClearGadget.navigateAndTestTM_exit_delim_lt src)
      cfg0 h_cfg_lt [] H (Compile.encodeTape s ++ res_in) hbranch_sym
      (Compile.navTestReg_run_content s src res_in hsrc hbit he)
      (Compile.navTestReg_traj_content s src res_in hsrc hbit he) hbody_traj'
    have hstate_eq : (Compile.opInnerBit dst).exit
        + (ClearGadget.navigateAndTestTM src).states = h1 := by
      rw [hh1def, Compile.headRawM_h1]; omega
    rw [hstate_eq, hraweq] at hpos
    rw [hraweq] at hpos_traj
    obtain ⟨hjoin, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept raw h1 h2 cfg0
      _ ([], 0, Compile.encodeTape (s.set dst [b]) ++ (res_in ++ List.replicate (s.get dst).length 0))
      hpos.1 (fun k hk ck hck => hpos_traj k hk ck hck) hh1_is hh2_is
    refine ⟨_, ?_, hjoin_traj, ?_⟩
    · rw [hisE]; exact hjoin
    · have hb := hbody_bud
      have hn := hnav_le
      rw [hskdef] at hn
      have hL := hLge
      omega

/-! ### Cursor-copy run lemmas (`copy` op, Risk C2 — bottom-up task 1)

The lemma stack for the `#eval`-probe-validated cursor-copy machine
(`probes/CursorCopyProbe.lean`): step lemmas for the two custom machines, the
per-bit pipeline pass (`copyPipe_run`), the loop-body contracts in `loopTM_run`
form (`copyBody_run_iter`/`copyBody_run_done`), the loop (`copyLoop_run`), and
the per-op exact-residue lemma `opCopy_run` consumed by the contract case (and,
with its EXACT residue formula `res ++ replicate |dst₀| 0`, by the future
`compileForBnd` combinator — HANDOFF bottom-up task 2). -/

/-- `markBitTM` on a shifted bit `b+1`: write the mark `3` over it, step to
exit `1+b`, head unchanged. -/
theorem Compile.markBitTM_step (b : Nat) (hb : b ≤ 1) (left right : List Nat)
    (head : Nat) (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = b + 1) :
    stepFlatTM Compile.markBitTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1 + b,
               tapes := [(left, head, right.take head ++ 3 :: right.drop (head + 1))] } := by
  have hsym : currentTapeSymbol (left, head, right) = some (b + 1) := by
    rw [currentTapeSymbol_in_range hlt, hget]
  interval_cases b <;>
    simp_all [stepFlatTM, Compile.markBitTM, Compile.markBitEntry,
      entryMatchesConfig, applyTransitionEntry, tapeStep,
      writeCurrentTapeSymbol, moveTapeHead]

/-- `markBitTM_step` in `runFlatTM` form. -/
theorem Compile.markBitTM_run (b : Nat) (hb : b ≤ 1) (left right : List Nat)
    (head : Nat) (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = b + 1) :
    runFlatTM 1 Compile.markBitTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1 + b,
               tapes := [(left, head, right.take head ++ 3 :: right.drop (head + 1))] } := by
  show (if haltingStateReached Compile.markBitTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.markBitTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.markBitTM cfg') = _
  rw [show haltingStateReached Compile.markBitTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.markBitTM_step b hb left right head hlt hget]
  rfl

/-- `markBitTM` never halts before its single step (state `0` is non-halting). -/
theorem Compile.markBitTM_no_early_halt (left right : List Nat) (head : Nat) :
    ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.markBitTM
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      haltingStateReached Compile.markBitTM ck = false := by
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  simp [runFlatTM] at hck; subst hck; rfl

/-- `restoreStepTM b` at the mark: restore the shifted bit `b+1` and step right. -/
theorem Compile.restoreStepTM_step (b : Nat) (hb : b ≤ 1) (left right : List Nat)
    (head : Nat) (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = 3) :
    stepFlatTM (Compile.restoreStepTM b) { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1,
               tapes := [(left, head + 1,
                          right.take head ++ (b + 1) :: right.drop (head + 1))] } := by
  have hsym : currentTapeSymbol (left, head, right) = some 3 := by
    rw [currentTapeSymbol_in_range hlt, hget]
  interval_cases b <;>
    simp_all [stepFlatTM, Compile.restoreStepTM, Compile.restoreStepEntry,
      entryMatchesConfig, applyTransitionEntry, tapeStep, writeCurrentTapeSymbol,
      moveTapeHead]

/-- `restoreStepTM_step` in `runFlatTM` form. -/
theorem Compile.restoreStepTM_run (b : Nat) (hb : b ≤ 1) (left right : List Nat)
    (head : Nat) (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = 3) :
    runFlatTM 1 (Compile.restoreStepTM b) { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1,
               tapes := [(left, head + 1,
                          right.take head ++ (b + 1) :: right.drop (head + 1))] } := by
  show (if haltingStateReached (Compile.restoreStepTM b)
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM (Compile.restoreStepTM b)
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 0 (Compile.restoreStepTM b) cfg') = _
  rw [show haltingStateReached (Compile.restoreStepTM b)
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.restoreStepTM_step b hb left right head hlt hget]
  rfl

/-- `restoreStepTM` never halts before its single step. -/
theorem Compile.restoreStepTM_no_early_halt (b : Nat) (left right : List Nat) (head : Nat) :
    ∀ k, k < 1 → ∀ ck,
      runFlatTM k (Compile.restoreStepTM b)
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      haltingStateReached (Compile.restoreStepTM b) ck = false := by
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  simp [runFlatTM] at hck; subst hck; rfl

/-! #### Marked-tape structure helpers (cursor-copy lemma stack)

The cursor loop's working tape is `encodeTape (q.set src (w₁ ++ c :: w₂)) ++ res`
(`c = 2` is the mark — encoding to the cell `3` — and `c = b ≤ 1` the restored
bit). The helpers below pin its explicit list shape, length, the mark cell, the
off-mark cell agreement, the interior cell facts (`< 4`, `≠ 3`) the scans need,
and the take/drop re-marking bridge consumed by `markBitTM`/`restoreStepTM`. -/

/-- Explicit shape of the cursor tape with residue: an opaque prefix `X` of
length `1 + |encodeRegs (q.take src)| + |w₁|`, the (shifted) cursor cell
`c + 1`, and an opaque suffix `Z` (independent of `c`). Packaged this way so
`getElem?_append_left/right` rewrites are unambiguous. -/
private theorem Compile.encodeTape_set_cell_res (q : State) (src : Var)
    (hsrc : src < q.length) (w₁ w₂ : List Nat) (c : Nat) (res : List Nat) :
    Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res
      = ((3 : Nat) :: (Compile.encodeRegs (q.take src) ++ Compile.shiftReg w₁))
        ++ ((c + 1) :: (Compile.shiftReg w₂
              ++ (0 :: (Compile.encodeRegs (q.drop (src + 1)) ++ (3 :: res))))) := by
  rw [(Compile.encodeTape_reg_decomp_at q src hsrc).1 (w₁ ++ c :: w₂)]
  rw [show Compile.shiftReg (w₁ ++ c :: w₂)
        = Compile.shiftReg w₁ ++ (c + 1) :: Compile.shiftReg w₂ from by
      simp [Compile.shiftReg]]
  show (Compile.endMark :: _) ++ _ ++ _ = _
  simp [Compile.endMark, List.append_assoc]

/-- Length of the prefix up to the cursor cell. -/
private theorem Compile.cursorPrefix_length (q : State) (src : Var) (w₁ : List Nat) :
    ((3 : Nat) :: (Compile.encodeRegs (q.take src) ++ Compile.shiftReg w₁)).length
      = 1 + (Compile.encodeRegs (q.take src)).length + w₁.length := by
  simp only [List.length_cons, List.length_append, Compile.shiftReg, List.length_map]
  omega

/-- Length of the cursor tape (independent of the cursor cell value `c`). -/
private theorem Compile.encodeTape_set_cell_length (q : State) (src : Var)
    (hsrc : src < q.length) (w₁ w₂ : List Nat) (c : Nat) :
    (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂))).length
      = 1 + (Compile.encodeRegs (q.take src)).length + w₁.length
        + (w₂.length + (Compile.encodeRegs (q.drop (src + 1))).length + 3) := by
  have h := congrArg List.length
    (Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c [])
  rw [List.append_nil] at h
  rw [h]
  simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map,
    List.length_nil]
  omega

/-- The cursor cell itself: cell `1 + |encodeRegs (q.take src)| + |w₁|` of the
cursor tape is the shifted value `c + 1`. -/
private theorem Compile.markedTape_get_mark (q : State) (src : Var) (hsrc : src < q.length)
    (w₁ w₂ : List Nat) (c : Nat) (res : List Nat) :
    ∃ (h : 1 + (Compile.encodeRegs (q.take src)).length + w₁.length
        < (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).length),
      (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).get
          ⟨1 + (Compile.encodeRegs (q.take src)).length + w₁.length, h⟩ = c + 1 := by
  set P := 1 + (Compile.encodeRegs (q.take src)).length + w₁.length with hP
  set X := (3 : Nat) :: (Compile.encodeRegs (q.take src) ++ Compile.shiftReg w₁) with hX
  set Z := (c + 1) :: (Compile.shiftReg w₂
      ++ (0 :: (Compile.encodeRegs (q.drop (src + 1)) ++ (3 :: res)))) with hZ
  have hshape : Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res = X ++ Z :=
    Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c res
  have hXlen : X.length = P := Compile.cursorPrefix_length q src w₁
  have hkey : (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res)[P]?
      = some (c + 1) := by
    rw [hshape, List.getElem?_append_right (by omega), hXlen, Nat.sub_self, hZ,
        List.getElem?_cons_zero]
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hkey
  refine ⟨hlt, ?_⟩
  rw [List.get_eq_getElem]
  exact hget

/-- Off the cursor cell, the cursor tapes for any two cell values agree. -/
private theorem Compile.markedTape_getElem_off (q : State) (src : Var) (hsrc : src < q.length)
    (w₁ w₂ : List Nat) (c c' : Nat) (res : List Nat) :
    ∀ i, i ≠ 1 + (Compile.encodeRegs (q.take src)).length + w₁.length →
      (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res)[i]?
        = (Compile.encodeTape (State.set q src (w₁ ++ c' :: w₂)) ++ res)[i]? := by
  intro i hi
  set P := 1 + (Compile.encodeRegs (q.take src)).length + w₁.length with hP
  set X := (3 : Nat) :: (Compile.encodeRegs (q.take src) ++ Compile.shiftReg w₁) with hX
  set W := Compile.shiftReg w₂
      ++ (0 :: (Compile.encodeRegs (q.drop (src + 1)) ++ (3 :: res))) with hW
  have hXlen : X.length = P := Compile.cursorPrefix_length q src w₁
  rw [Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c res,
      Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c' res, ← hX, ← hW]
  rcases Nat.lt_or_ge i P with hlt | hge
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · have hgt : P < i := lt_of_le_of_ne hge (fun h => hi h.symm)
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hXlen]
    obtain ⟨j, hj⟩ : ∃ j, i - P = j + 1 := ⟨i - P - 1, by omega⟩
    rw [hj, List.getElem?_cons_succ, List.getElem?_cons_succ]

/-- **Re-marking bridge**: overwriting the cursor cell of the cursor tape with
`c' + 1` (the take/cons/drop form `markBitTM`/`restoreStepTM` produce) yields
the cursor tape for `c'`. -/
private theorem Compile.markedTape_take_drop (q : State) (src : Var) (hsrc : src < q.length)
    (w₁ w₂ : List Nat) (c c' : Nat) (res : List Nat) :
    (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).take
        (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
      ++ (c' + 1) :: (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).drop
        (1 + (Compile.encodeRegs (q.take src)).length + w₁.length + 1)
      = Compile.encodeTape (State.set q src (w₁ ++ c' :: w₂)) ++ res := by
  set P := 1 + (Compile.encodeRegs (q.take src)).length + w₁.length with hP
  set X := (3 : Nat) :: (Compile.encodeRegs (q.take src) ++ Compile.shiftReg w₁) with hX
  set W := Compile.shiftReg w₂
      ++ (0 :: (Compile.encodeRegs (q.drop (src + 1)) ++ (3 :: res))) with hW
  have hXlen : X.length = P := Compile.cursorPrefix_length q src w₁
  rw [Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c res,
      Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ c' res, ← hX, ← hW]
  have htake : (X ++ (c + 1) :: W).take P = X := by
    rw [← hXlen]; exact List.take_left
  have hsplit2 : X ++ (c + 1) :: W = (X ++ [c + 1]) ++ W := by
    simp [List.append_assoc]
  have hdrop : (X ++ (c + 1) :: W).drop (P + 1) = W := by
    rw [hsplit2]
    exact List.drop_left' (by rw [List.length_append, hXlen]; rfl)
  rw [htake, hdrop]

/-- `appendAtTM_exit` in closed form. -/
private theorem Compile.appendAtTM_exit_eq :
    ∀ d, AppendGadget.appendAtTM_exit d = 8 + 3 * d
  | 0 => rfl
  | d + 1 => by
      show 3 + AppendGadget.appendAtTM_exit d = _
      rw [Compile.appendAtTM_exit_eq d]; omega

/-- Generic seam symbol bound: every cell `< 4` ⇒ the current symbol is `< 4`. -/
private theorem Compile.sym_bound_of_lt_four (tape : List Nat) (hall : ∀ x ∈ tape, x < 4)
    (hd : Nat) : ∀ v, currentTapeSymbol (([] : List Nat), hd, tape) = some v → v < 4 := by
  intro v hv
  by_cases hlt : hd < tape.length
  · rw [currentTapeSymbol_in_range hlt] at hv
    exact (Option.some_inj.mp hv) ▸ hall _ (List.get_mem tape ⟨hd, hlt⟩)
  · rw [show currentTapeSymbol (([] : List Nat), hd, tape) = none from dif_neg hlt] at hv
    exact absurd hv (by simp)

/-- The trailing terminator of `encodeTape t` inside `encodeTape t ++ res`:
cell `|encodeRegs t| + 1` is `3`. -/
private theorem Compile.encodeTape_append_getElem_last (t : State) (res : List Nat) :
    (Compile.encodeTape t ++ res)[(Compile.encodeRegs t).length + 1]? = some 3 := by
  have hlt : (Compile.encodeRegs t).length + 1 < (Compile.encodeTape t).length := by
    rw [Compile.encodeTape]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  rw [List.getElem?_append_left hlt, Compile.encodeTape, List.getElem?_cons_succ,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- A register write with `≤ 2`-valued content keeps every register `≤ 2`
(the marked-state analogue of `BitState_set`). -/
private theorem Compile.le_two_set (s : State) (dst : Var) (v : List Nat)
    (h : Compile.BitState s) (hdst : dst < s.length) (hv : ∀ x ∈ v, x ≤ 2) :
    ∀ reg ∈ State.set s dst v, ∀ x ∈ reg, x ≤ 2 := by
  rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop s dst _ hdst]
  intro reg hreg x hx
  simp only [List.mem_append, List.mem_cons] at hreg
  rcases hreg with hr | hr | hr
  · exact le_trans (h reg (List.mem_of_mem_take hr) x hx) (by omega)
  · subst hr; exact hv x hx
  · exact le_trans (h reg (List.mem_of_mem_drop hr) x hx) (by omega)

/-- `encodeRegs` of a `≤ 2`-valued state has all cells `< 4`. -/
private theorem Compile.encodeRegs_lt_four_le_two (t : State)
    (h : ∀ b ∈ t, ∀ x ∈ b, x ≤ 2) : ∀ y ∈ Compile.encodeRegs t, y < 4 := by
  induction t with
  | nil => intro y hy; simp [Compile.encodeRegs] at hy
  | cons r t ih =>
      intro y hy
      rw [Compile.encodeRegs_cons, List.mem_append, List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · rw [Compile.shiftReg, List.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        have := h r (List.mem_cons_self ..) z hz; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega
      · exact ih (fun b hb x hx => h b (List.mem_cons_of_mem _ hb) x hx) y hy

/-- All cells of `encodeTape t ++ res` for a `≤ 2`-valued `t` are `< 4`. -/
private theorem Compile.encodeTape_append_res_lt_four_le_two (t : State) (res : List Nat)
    (h : ∀ b ∈ t, ∀ x ∈ b, x ≤ 2) (hres : Compile.ValidResidue res) :
    ∀ x ∈ Compile.encodeTape t ++ res, x < 4 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rw [Compile.encodeTape, List.mem_cons, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · subst hx; decide
    · exact Compile.encodeRegs_lt_four_le_two t h x hx
    · subst hx; decide
  · exact (hres x hx).1

/-- **Interior cells of the cursor tape, off the cursor.** Every cell `0 < i`
that is neither the cursor cell nor in the trailing-terminator-plus-residue
region is `< 4` and `≠ 3` — it agrees with the corresponding cell of the
*unmarked* `encodeTape q ++ res`, whose interior is sentinel-free. -/
private theorem Compile.markedTape_interior_cell (q : State) (src : Var)
    (hsrc : src < q.length) (hbit : Compile.BitState q) (w₁ w₂ : List Nat) (b : Nat)
    (hsplit : State.get q src = w₁ ++ b :: w₂) (c : Nat) (res : List Nat) :
    ∀ i, 0 < i → i ≠ 1 + (Compile.encodeRegs (q.take src)).length + w₁.length →
      i + 1 < (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂))).length →
      ∃ (h : i < (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).length),
        (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).get ⟨i, h⟩ < 4 ∧
        (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).get ⟨i, h⟩ ≠ 3 := by
  intro i hi0 hiP hilen
  have hq : State.set q src (w₁ ++ b :: w₂) = q := by
    rw [← hsplit]; exact Compile.set_get_self q src hsrc
  have hlt : i < (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).length := by
    rw [List.length_append]; omega
  refine ⟨hlt, ?_⟩
  -- the cell agrees with the unmarked tape's cell `i`.
  have hoff := Compile.markedTape_getElem_off q src hsrc w₁ w₂ c b res i hiP
  rw [hq] at hoff
  -- length transfer marked ↔ unmarked.
  have hlen_eq : (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂))).length
      = (Compile.encodeTape q).length := by
    conv_rhs => rw [← hq]
    rw [Compile.encodeTape_set_cell_length q src hsrc w₁ w₂ c,
        Compile.encodeTape_set_cell_length q src hsrc w₁ w₂ b]
  have hilen' : i + 1 < (Compile.encodeTape q).length := by omega
  have hltq : i < (Compile.encodeTape q ++ res).length := by
    rw [List.length_append]; omega
  have hgetq : (Compile.encodeTape (State.set q src (w₁ ++ c :: w₂)) ++ res).get ⟨i, hlt⟩
      = (Compile.encodeTape q ++ res).get ⟨i, hltq⟩ := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact Option.some_inj.mp (by
      rw [← List.getElem?_eq_getElem hlt, ← List.getElem?_eq_getElem hltq]; exact hoff)
  rw [hgetq]
  -- the unmarked cell is inside `encodeTape q`'s interior.
  have hilt_e : i < (Compile.encodeTape q).length := by omega
  have hkey : (Compile.encodeTape q ++ res)[i]?
      = some ((Compile.encodeTape q).get ⟨i, hilt_e⟩) := by
    rw [List.getElem?_append_left hilt_e, List.getElem?_eq_getElem hilt_e,
        List.get_eq_getElem]
  have hgetin : (Compile.encodeTape q ++ res).get ⟨i, hltq⟩
      = (Compile.encodeTape q).get ⟨i, hilt_e⟩ := by
    rw [List.get_eq_getElem]
    exact Option.some_inj.mp ((List.getElem?_eq_getElem hltq).symm.trans hkey)
  rw [hgetin]
  obtain ⟨hi', hne3⟩ := Compile.encodeTape_interior_ne_endMark q hbit i hi0 hilen'
  refine ⟨Compile.encodeTape_lt_four q hbit _ (List.get_mem _ _), ?_⟩
  exact hne3

/-- **`appendAtTM` on an encoded tape with residue (cursor-copy stage 3).**
For a `≤ 2`-valued state `p` (the marked loop state) and a shifted symbol
`v + 1` (`v ≤ 2`), the gadget started at head `0` on `encodeTape p ++ res`
appends `v` to register `dst`, exits at its unique halt `appendAtTM_exit dst`
with the head on the LAST cell of the output tape (index
`|encodeTape p| + |res|`), never halting earlier, within `2·L + 3` steps
(`L` the input tape length). The leading sentinel is folded into the first
marker-free block exactly as in `appendBit_sound`; the residue rides in `post`
(its cells are `< 4`, which is all the gadget needs). -/
private theorem Compile.appendAt_encTape_run (v : Nat) (hv : v ≤ 2)
    (p : State) (dst : Var) (hdst : dst < p.length)
    (hp : ∀ reg ∈ p, ∀ x ∈ reg, x ≤ 2)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (AppendGadget.appendAtTM (v + 1) dst)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape p ++ res)] }
        = some { state_idx := AppendGadget.appendAtTM_exit dst,
                 tapes := [([], (Compile.encodeTape p).length + res.length,
                            Compile.encodeTape (State.set p dst (State.get p dst ++ [v]))
                              ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (AppendGadget.appendAtTM (v + 1) dst)
              { state_idx := 0, tapes := [([], 0, Compile.encodeTape p ++ res)] } = some ck →
          ck.state_idx ≠ AppendGadget.appendAtTM_exit dst ∧
          haltingStateReached (AppendGadget.appendAtTM (v + 1) dst) ck = false)
      ∧ t ≤ 2 * (Compile.encodeTape p ++ res).length + 3 := by
  have h_ins : v + 1 < 4 := by omega
  set post₀ : List Nat := Compile.encodeRegs (p.drop (dst + 1)) ++ [Compile.endMark]
    with hpost₀
  set post : List Nat := post₀ ++ res with hpost
  set skipped : List (List Nat) := (p.take dst).map Compile.shiftReg with hskip
  set body : List Nat := Compile.shiftReg (State.get p dst) with hbody
  have hget_mem : State.get p dst ∈ p := by
    rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
  have hshift_lt : ∀ (r : List Nat), (∀ x ∈ r, x ≤ 2) →
      ∀ x ∈ Compile.shiftReg r, x < 4 := by
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
    exact ⟨hshift_ne r, hshift_lt r (fun x hx => hp r (List.mem_of_mem_take hr) x hx)⟩
  have hbody_ne : ∀ x ∈ body, x ≠ 0 := by rw [hbody]; exact hshift_ne _
  have hbody_lt : ∀ x ∈ body, x < 4 := by
    rw [hbody]; exact hshift_lt _ (fun x hx => hp _ hget_mem x hx)
  have hpost_lt : ∀ x ∈ post, x < 4 := by
    rw [hpost, hpost₀]; intro x hx
    rw [List.mem_append, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact Compile.encodeRegs_lt_four_le_two _
        (fun b hbm y hy => hp b (List.mem_of_mem_drop hbm) y hy) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; decide
    · exact (hres x hx).1
  -- Fold the leading sentinel into the first marker-free block.
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
  -- The sentinel-free split, with the residue attached.
  have hsplit0 : AppendGadget.regBlocks skipped ++ body ++ 0 :: post₀
      = Compile.encodeRegs p ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost₀]; exact Compile.encodeTape_split p dst hdst
  have hsplit : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post
      = Compile.encodeTape p ++ res := by
    rw [Compile.encodeTape, List.nil_append, hsfold, hpost]
    rw [show Compile.endMark :: (AppendGadget.regBlocks skipped ++ body) ++ 0 :: (post₀ ++ res)
          = Compile.endMark :: ((AppendGadget.regBlocks skipped ++ body ++ 0 :: post₀) ++ res)
        from by simp [List.append_assoc], hsplit0]
    simp [List.append_assoc]
  -- The output tape with the inserted symbol.
  have htape0 : AppendGadget.regBlocks skipped ++ body ++ (v + 1) :: 0 :: post₀
      = Compile.encodeRegs (State.set p dst (State.get p dst ++ [v]))
          ++ [Compile.endMark] := by
    rw [hskip, hbody, hpost₀, Compile.regBlocks_map_shiftReg]
    rw [State.set, if_pos hdst, Compile.list_set_eq_take_cons_drop p dst _ hdst,
        Compile.encodeRegs_append, Compile.encodeRegs_cons, Compile.shiftReg_append]
    simp [List.append_assoc]
  have htape : ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ (v + 1) :: 0 :: post
      = Compile.encodeTape (State.set p dst (State.get p dst ++ [v])) ++ res := by
    rw [Compile.encodeTape, List.nil_append, hsfold, hpost]
    rw [show Compile.endMark :: (AppendGadget.regBlocks skipped ++ body)
            ++ (v + 1) :: 0 :: (post₀ ++ res)
          = Compile.endMark
            :: ((AppendGadget.regBlocks skipped ++ body ++ (v + 1) :: 0 :: post₀) ++ res)
        from by simp [List.append_assoc], htape0]
    simp [List.append_assoc]
  -- The run, trajectory, and step bound.
  have hrun := AppendGadget.appendAt_run_exit (v + 1) h_ins dst [] sk bd post hlen_sk
    h_pre h_skip_sk hbd_ne hbd_lt hpost_lt
  have htraj := AppendGadget.appendAt_no_early_halt (v + 1) h_ins dst [] sk bd post hlen_sk
    h_pre h_skip_sk hbd_ne hbd_lt hpost_lt
  -- The exit head equals the input tape length.
  have hhead : ([] : List Nat).length + (AppendGadget.regBlocks sk).length + bd.length
      + ((0 : Nat) :: post).length = (Compile.encodeTape p).length + res.length := by
    have hL := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil] at hL ⊢
    omega
  have hstep_le : AppendGadget.appendAt_steps sk bd post
      ≤ 2 * (Compile.encodeTape p ++ res).length + 3 := by
    have hb' := AppendGadget.appendAt_steps_le sk bd post
    have hL : (AppendGadget.regBlocks sk ++ bd ++ 0 :: post).length
        = (Compile.encodeTape p ++ res).length := by
      rw [show AppendGadget.regBlocks sk ++ bd ++ 0 :: post
            = ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post from by simp,
          hsplit]
    rw [hL] at hb'; exact hb'
  refine ⟨AppendGadget.appendAt_steps sk bd post, ?_, ?_, hstep_le⟩
  · rw [show ({ state_idx := 0, tapes := [([], 0, Compile.encodeTape p ++ res)] }
          : FlatTMConfig)
        = { state_idx := 0,
            tapes := [([], ([] : List Nat).length,
              ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post)] }
      from by rw [hsplit]; rfl]
    rw [hrun, htape, hhead]
  · intro k hk ck hck
    rw [show ({ state_idx := 0, tapes := [([], 0, Compile.encodeTape p ++ res)] }
          : FlatTMConfig)
        = { state_idx := 0,
            tapes := [([], ([] : List Nat).length,
              ([] : List Nat) ++ AppendGadget.regBlocks sk ++ bd ++ 0 :: post)] }
      from by rw [hsplit]; rfl] at hck
    have hh := htraj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (AppendGadget.appendAtTM_exit_is_halt (v + 1) dst) hh,
           hh⟩

/-- The symbol under the cursor is below the body's alphabet bound `4`. -/
private theorem Compile.copyBody_sym_bound (dst : Nat) (H : Nat) (tape : List Nat)
    (hall : ∀ x ∈ tape, x < 4) :
    ∀ v, currentTapeSymbol (([] : List Nat), H, tape) = some v →
      v < max (ClearGadget.delimTestTM 4).sig
            (max (Compile.copyContentTM dst).sig Compile.idTM.sig) := by
  intro v hv
  have hmax : max (ClearGadget.delimTestTM 4).sig
      (max (Compile.copyContentTM dst).sig Compile.idTM.sig) = 4 := by
    rw [ClearGadget.delimTestTM_sig]
    show max 4 (max (Compile.copyContentRawTM dst).sig 4) = 4
    rw [Compile.copyContentRawTM_sig]
    rfl
  rw [hmax]
  by_cases hlt : H < tape.length
  · rw [currentTapeSymbol_in_range hlt] at hv
    exact (Option.some_inj.mp hv) ▸ hall _ (List.get_mem tape ⟨H, hlt⟩)
  · rw [show currentTapeSymbol (([] : List Nat), H, tape) = none from dif_neg hlt] at hv
    exact absurd hv (by simp)

/-- All cells of `encodeTape q ++ res` are `< 4` (bit state + valid residue). -/
private theorem Compile.encodeTape_append_res_lt_four (q : State) (res : List Nat)
    (hbit : Compile.BitState q) (hres : Compile.ValidResidue res) :
    ∀ x ∈ Compile.encodeTape q ++ res, x < 4 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact Compile.encodeTape_lt_four q hbit x h
  · exact (hres x h).1

/-- **Pipeline stages 1–2 (`copyRet1TM`) on the marked tape**: step left off the
mark, scan left through the (sentinel-free) prefix to the leading sentinel.
Exact step count `1 + 1 + P` (`P` the mark position), exit `3`, tape unchanged,
head `0`. -/
private theorem Compile.copyRet1_encTape_run (q : State) (src : Var) (hsrc : src < q.length)
    (hbit : Compile.BitState q) (w₁ w₂ : List Nat) (b : Nat)
    (hsplit : State.get q src = w₁ ++ b :: w₂)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    runFlatTM (1 + 1 + (1 + (Compile.encodeRegs (q.take src)).length + w₁.length))
        Compile.copyRet1TM
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                     Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
      = some { state_idx := 3,
               tapes := [([], 0,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    ∧ (∀ k, k < 1 + 1 + (1 + (Compile.encodeRegs (q.take src)).length + w₁.length) → ∀ ck,
        runFlatTM k Compile.copyRet1TM
            { state_idx := 0,
              tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                         Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
          = some ck →
        ck.state_idx ≠ 3 ∧ haltingStateReached Compile.copyRet1TM ck = false) := by
  obtain ⟨hPlt, hPget⟩ := Compile.markedTape_get_mark q src hsrc w₁ w₂ 2 res
  -- stage 1: one step left off the mark.
  have h1_run := ScanLeft.stepLeftTM_run 4 []
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length) hPlt
    (by rw [hPget]; decide)
  have h1_traj := ScanLeft.stepLeftTM_no_early_halt 4 []
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
  -- stage 2: scan left to the leading sentinel at index `0`.
  have h0 : 0 < (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res).length := by
    omega
  have htarget0 : (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res).get
      ⟨0, h0⟩ = 3 := by
    have hkey : (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)[0]?
        = some 3 := by
      rw [Compile.encodeTape_set_cell_res q src hsrc w₁ w₂ 2 res]
      rfl
    rw [List.get_eq_getElem]
    exact Option.some_inj.mp ((List.getElem?_eq_getElem h0).symm.trans hkey)
  have hLM := Compile.encodeTape_set_cell_length q src hsrc w₁ w₂ 2
  have hcells : ∀ i, 0 < i →
      i ≤ 1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1 →
      ∃ (h : i < (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res).length),
        (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res).get ⟨i, h⟩ < 4 ∧
        (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res).get ⟨i, h⟩ ≠ 3 :=
    fun i hi0 hile =>
      Compile.markedTape_interior_cell q src hsrc hbit w₁ w₂ b hsplit 2 res i hi0
        (by omega) (by omega)
  have h2_run := ScanLeft.scanLeft_run 4 3 []
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res) h0 htarget0
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1) (by omega) hcells
  have h2_traj := ScanLeft.scanLeft_no_early_halt 4 3 []
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1) (by omega) hcells
  -- compose.
  have hsym : ∀ v, currentTapeSymbol
      ([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1,
        Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res) = some v →
      v < max (ScanLeft.stepLeftTM 4).sig (ScanLeft.scanLeftUntilTM 4 3).sig := by
    intro v hv
    have hlt4 : ∀ x ∈ Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res,
        x < 4 := by
      refine Compile.encodeTape_append_res_lt_four_le_two _ res ?_ hres
      refine Compile.le_two_set q src _ hbit hsrc ?_
      intro x hx
      have hw : ∀ y ∈ w₁ ++ b :: w₂, y ≤ 1 := by
        rw [← hsplit]
        intro y hy
        have hmem : State.get q src ∈ q := by
          rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
        exact hbit _ hmem y hy
      rcases List.mem_append.mp hx with h | h
      · exact le_trans (hw x (List.mem_append_left _ h)) (by omega)
      · rcases List.mem_cons.mp h with h0 | h0
        · omega
        · exact le_trans (hw x (List.mem_append_right _ (List.mem_cons_of_mem _ h0)))
            (by omega)
    exact Compile.sym_bound_of_lt_four _ hlt4 _ v hv
  have hcomp := composeFlatTM_run (ScanLeft.stepLeftTM_valid 4)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide)) (by decide)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (ScanLeft.stepLeftTM 4).states; decide) []
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1)
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    hsym h1_run h1_traj h2_run rfl
  have hcomp_traj := composeFlatTM_no_early_halt (ScanLeft.stepLeftTM_valid 4)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide)) (by decide)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (ScanLeft.stepLeftTM 4).states; decide) []
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1)
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    hsym h1_run h1_traj
    (fun k hk ck hck => (h2_traj k hk ck hck).2)
  have hsteps : 1 + 1 + (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
      = 1 + 1 + (1 + (Compile.encodeRegs (q.take src)).length + w₁.length - 1 + 1) := by
    omega
  refine ⟨?_, ?_⟩
  · rw [hsteps]; exact hcomp.1
  · intro k hk ck hck
    have hh := hcomp_traj k (by omega) ck hck
    exact ⟨ClearGadget.ne_of_not_halting
      (show Compile.copyRet1TM.halt[3]? = some true from rfl) hh, hh⟩

/-- **One cursor-copy pipeline pass (`copyPipeTM b dst`).** Started with the head
ON the freshly written mark (src's cell `i = |w₁|`, the only interior `3`), the
pipeline rewinds to the sentinel, appends `b` to `dst` (`appendAtTM (b+1)`),
returns to the mark via scan-left-from-the-end (trailing terminator, step left,
mark), restores `b+1` over the mark and steps right onto the next cursor cell.
`q` is the un-marked loop-invariant state; `dst ≠ src`; the marked tape is
`encodeTape (q.set src (w₁ ++ 2 :: w₂))` (cell value `2` encodes to the mark `3`).
The residue passes through untouched. Budget: `≤ 5·L + 16` over the *final*
tape (`L = |encodeTape (q.set dst …) ++ res|`, one cell longer than the input). -/
theorem Compile.copyPipe_run (b : Nat) (hb : b ≤ 1) (q : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < q.length) (hsrc : src < q.length)
    (hbit : Compile.BitState q) (w₁ w₂ : List Nat)
    (hsplit : State.get q src = w₁ ++ b :: w₂)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ T,
      runFlatTM T (Compile.copyPipeTM b dst)
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                       Compile.encodeTape (q.set src (w₁ ++ 2 :: w₂)) ++ res)] }
        = some { state_idx := Compile.copyPipeTM_exit dst,
                 tapes := [([],
                   1 + (Compile.encodeRegs ((q.set dst (State.get q dst ++ [b])).take src)).length
                     + w₁.length + 1,
                   Compile.encodeTape (q.set dst (State.get q dst ++ [b])) ++ res)] }
      ∧ (∀ k, k < T → ∀ ck,
          runFlatTM k (Compile.copyPipeTM b dst)
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                           Compile.encodeTape (q.set src (w₁ ++ 2 :: w₂)) ++ res)] } = some ck →
          ck.state_idx ≠ Compile.copyPipeTM_exit dst ∧
          haltingStateReached (Compile.copyPipeTM b dst) ck = false)
      ∧ T ≤ 5 * (Compile.encodeTape (q.set dst (State.get q dst ++ [b])) ++ res).length + 16 := by
  -- ### shared bit-shape facts
  have hu_mem : State.get q dst ∈ q := by
    rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
  have hu_le : ∀ x ∈ State.get q dst, x ≤ 1 := hbit _ hu_mem
  have hw : ∀ y ∈ w₁ ++ b :: w₂, y ≤ 1 := by
    rw [← hsplit]
    intro y hy
    have hmem : State.get q src ∈ q := by
      rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
    exact hbit _ hmem y hy
  have hm_le2 : ∀ x ∈ w₁ ++ 2 :: w₂, x ≤ 2 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact le_trans (hw x (List.mem_append_left _ h)) (by omega)
    · rcases List.mem_cons.mp h with h0 | h0
      · omega
      · exact le_trans (hw x (List.mem_append_right _ (List.mem_cons_of_mem _ h0)))
          (by omega)
  have hqM_le2 : ∀ reg ∈ State.set q src (w₁ ++ 2 :: w₂), ∀ x ∈ reg, x ≤ 2 :=
    Compile.le_two_set q src _ hbit hsrc hm_le2
  have hqM_len : (State.set q src (w₁ ++ 2 :: w₂)).length = q.length :=
    Compile.length_set q src _ hsrc
  have hdstM : dst < (State.set q src (w₁ ++ 2 :: w₂)).length := by
    rw [hqM_len]; exact hdst
  -- ### the appended state `q' = q.set dst (u ++ [b])` and its facts
  have hq'_len : (State.set q dst (State.get q dst ++ [b])).length = q.length :=
    Compile.length_set q dst _ hdst
  have hsrc' : src < (State.set q dst (State.get q dst ++ [b])).length := by
    rw [hq'_len]; exact hsrc
  have hbit' : Compile.BitState (State.set q dst (State.get q dst ++ [b])) := by
    refine Compile.BitState_set q dst _ hbit hdst ?_
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hu_le x h
    · rcases List.mem_cons.mp h with h0 | h0
      · subst h0; exact hb
      · cases h0
  have hsplit' : State.get (State.set q dst (State.get q dst ++ [b])) src
      = w₁ ++ b :: w₂ := by
    rw [Compile.get_set_ne q dst _ src hdst (Ne.symm hne)]; exact hsplit
  have hqM'_eq : State.set (State.set q src (w₁ ++ 2 :: w₂)) dst (State.get q dst ++ [b])
      = State.set (State.set q dst (State.get q dst ++ [b])) src (w₁ ++ 2 :: w₂) :=
    Compile.set_comm q src dst _ _ hsrc hdst (Ne.symm hne)
  have hgetM : State.get (State.set q src (w₁ ++ 2 :: w₂)) dst = State.get q dst :=
    Compile.get_set_ne q src _ dst hsrc hne
  have hqM'_le2 : ∀ reg ∈ State.set (State.set q dst (State.get q dst ++ [b])) src
      (w₁ ++ 2 :: w₂), ∀ x ∈ reg, x ≤ 2 :=
    Compile.le_two_set _ src _ hbit' hsrc' hm_le2
  -- ### tape cell bounds
  have hTmIn_lt4 : ∀ x ∈ Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res,
      x < 4 := Compile.encodeTape_append_res_lt_four_le_two _ res hqM_le2 hres
  have hTmOut_lt4 : ∀ x ∈ Compile.encodeTape (State.set
      (State.set q dst (State.get q dst ++ [b])) src (w₁ ++ 2 :: w₂)) ++ res,
      x < 4 := Compile.encodeTape_append_res_lt_four_le_two _ res hqM'_le2 hres
  -- ### length bookkeeping
  have hLM := Compile.encodeTape_set_cell_length q src hsrc w₁ w₂ 2
  have hLM' := Compile.encodeTape_set_cell_length
    (State.set q dst (State.get q dst ++ [b])) src hsrc' w₁ w₂ 2
  have hE1' : (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
        src (w₁ ++ 2 :: w₂))).length
      = (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length + 1 := by
    have hbal := Compile.encodeTape_set_length (State.set q src (w₁ ++ 2 :: w₂)) dst
      (State.get q dst ++ [b]) hdstM
    rw [hgetM, hqM'_eq] at hbal
    have hlb : (State.get q dst ++ [b]).length = (State.get q dst).length + 1 := by simp
    omega
  -- ### stages 1–2: `copyRet1TM` (run + traj proved above)
  have hRet1 := Compile.copyRet1_encTape_run q src hsrc hbit w₁ w₂ b hsplit res hres
  -- ### stage 3: `appendAtTM (b+1) dst` on the marked tape
  obtain ⟨t₃, happ_run, happ_traj, happ_le⟩ :=
    Compile.appendAt_encTape_run b (by omega) (State.set q src (w₁ ++ 2 :: w₂)) dst hdstM
      hqM_le2 res hres
  rw [hgetM, hqM'_eq] at happ_run
  -- ### level A2: copyRet1TM ⨾ appendAtTM
  have hsymA2 : ∀ v, currentTapeSymbol
      ([], 0, Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res) = some v →
      v < max Compile.copyRet1TM.sig (AppendGadget.appendAtTM (b + 1) dst).sig := by
    intro v hv
    rw [show max Compile.copyRet1TM.sig (AppendGadget.appendAtTM (b + 1) dst).sig = 4 from by
      rw [Compile.copyRet1TM_sig, AppendGadget.appendAtTM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hTmIn_lt4 _ v hv
  have happ_run' : runFlatTM t₃ (AppendGadget.appendAtTM (b + 1) dst)
      { state_idx := (AppendGadget.appendAtTM (b + 1) dst).start,
        tapes := [([], 0, Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
      = some { state_idx := AppendGadget.appendAtTM_exit dst,
               tapes := [([],
                 (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length + res.length,
                 Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
                   src (w₁ ++ 2 :: w₂)) ++ res)] } := by
    rw [AppendGadget.appendAtTM_start]; exact happ_run
  have hA2run := composeFlatTM_run Compile.copyRet1TM_valid
    (AppendGadget.appendAtTM_valid (b + 1) (by omega) dst)
    (by show (3 : Nat) < Compile.copyRet1TM.states; rw [Compile.copyRet1TM_states]; omega)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < Compile.copyRet1TM.states; rw [Compile.copyRet1TM_states]; omega)
    [] 0 (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    hsymA2 hRet1.1 hRet1.2 happ_run'
    (Compile.haltingStateReached_of_halt (AppendGadget.appendAtTM_exit_is_halt (b + 1) dst))
  have hA2traj := composeFlatTM_no_early_halt Compile.copyRet1TM_valid
    (AppendGadget.appendAtTM_valid (b + 1) (by omega) dst)
    (by show (3 : Nat) < Compile.copyRet1TM.states; rw [Compile.copyRet1TM_states]; omega)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < Compile.copyRet1TM.states; rw [Compile.copyRet1TM_states]; omega)
    [] 0 (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
    hsymA2 hRet1.1 hRet1.2
    (fun k hk ck hck => (happ_traj k hk ck
      (by rw [AppendGadget.appendAtTM_start] at hck; exact hck)).2)
  -- repackage at the `copyPipeA2TM` machine with the named exit `13 + 3·dst`
  have hMA2 : Compile.copyPipeA2TM b dst
      = composeFlatTM Compile.copyRet1TM (AppendGadget.appendAtTM (b + 1) dst) 3 := rfl
  have hexA2 : AppendGadget.appendAtTM_exit dst + Compile.copyRet1TM.states
      = 13 + 3 * dst := by
    rw [Compile.appendAtTM_exit_eq, Compile.copyRet1TM_states]; omega
  rw [hexA2] at hA2run
  have hA2halt : (Compile.copyPipeA2TM b dst).halt[13 + 3 * dst]? = some true := by
    have h := Compile.composeFlatTM_halt_intro Compile.copyRet1TM
      (AppendGadget.appendAtTM (b + 1) dst) (AppendGadget.appendAtTM_exit dst) 3
      (AppendGadget.appendAtTM_exit_is_halt (b + 1) dst)
    rw [Compile.copyRet1TM_states, Compile.appendAtTM_exit_eq] at h
    rw [hMA2, show (13 + 3 * dst : Nat) = 5 + (8 + 3 * dst) from by omega]
    exact h
  -- ### stage 4: scan left from the tape end to the trailing terminator
  have hterm? : (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
        src (w₁ ++ 2 :: w₂)) ++ res)[
      (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length]? = some 3 := by
    have h := Compile.encodeTape_append_getElem_last
      (State.set (State.set q dst (State.get q dst ++ [b])) src (w₁ ++ 2 :: w₂)) res
    have hlen2 : (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂))).length
        = (Compile.encodeRegs (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂))).length + 2 := by
      rw [Compile.encodeTape]; simp
    rw [show (Compile.encodeRegs (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂))).length + 1
        = (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length from by omega] at h
    exact h
  obtain ⟨hterm_lt, hterm_get⟩ := List.getElem?_eq_some_iff.mp hterm?
  have hterm_get' : (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
        src (w₁ ++ 2 :: w₂)) ++ res).get
      ⟨(Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length, hterm_lt⟩ = 3 := by
    rw [List.get_eq_getElem]; exact hterm_get
  have hTmOut_len : (Compile.encodeTape (State.set (State.set q dst
        (State.get q dst ++ [b])) src (w₁ ++ 2 :: w₂)) ++ res).length
      = (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length + 1 + res.length := by
    rw [List.length_append]; omega
  have hcells4 : ∀ i, (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length < i →
      i ≤ (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length + res.length →
      ∃ (h : i < (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res).length),
        (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res).get ⟨i, h⟩ < 4 ∧
        (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res).get ⟨i, h⟩ ≠ 3 := by
    intro i hgt hle
    have hlt : i < (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
        src (w₁ ++ 2 :: w₂)) ++ res).length := by omega
    refine ⟨hlt, ?_⟩
    have hres_idx : i - (Compile.encodeTape (State.set (State.set q dst
        (State.get q dst ++ [b])) src (w₁ ++ 2 :: w₂))).length < res.length := by omega
    have hkey : (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res)[i]?
        = res[i - (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
            src (w₁ ++ 2 :: w₂))).length]? :=
      List.getElem?_append_right (by omega)
    have hmem := List.getElem_mem hres_idx
    have hval := hres _ hmem
    have hgetv : (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res).get ⟨i, hlt⟩
        = res[i - (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
            src (w₁ ++ 2 :: w₂))).length]'hres_idx := by
      rw [List.get_eq_getElem]
      exact Option.some_inj.mp ((List.getElem?_eq_getElem hlt).symm.trans
        (hkey.trans (List.getElem?_eq_getElem hres_idx)))
    rw [hgetv]
    refine ⟨hval.1, ?_⟩
    have h2 := hval.2
    simpa [Compile.endMark] using h2
  have h4_run := ScanLeft.scanLeftToMark_run 4 3 []
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length hterm_lt hterm_get'
    res.length
    ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length + res.length)
    rfl (by omega) hcells4
  have h4_traj := ScanLeft.scanLeftToMark_no_early_halt 4 3 []
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length hterm_lt hterm_get'
    res.length
    ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length + res.length)
    rfl (by omega) hcells4
  -- ### level A3: copyPipeA2TM ⨾ scanLeftUntilTM
  have hsymA3 : ∀ v, currentTapeSymbol
      ([], (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length + res.length,
        Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res) = some v →
      v < max (Compile.copyPipeA2TM b dst).sig (ScanLeft.scanLeftUntilTM 4 3).sig := by
    intro v hv
    rw [show max (Compile.copyPipeA2TM b dst).sig (ScanLeft.scanLeftUntilTM 4 3).sig = 4
      from by rw [Compile.copyPipeA2TM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hTmOut_lt4 _ v hv
  have hA3run := composeFlatTM_run (Compile.copyPipeA2TM_valid b dst hb)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (by show (13 + 3 * dst : Nat) < (Compile.copyPipeA2TM b dst).states
        rw [Compile.copyPipeA2TM_states]; omega)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (Compile.copyPipeA2TM b dst).states
        rw [Compile.copyPipeA2TM_states]; omega)
    [] ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length + res.length)
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    hsymA3 hA2run.1
    (fun k hk ck hck => by
      have hh := hA2traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hA2halt hh, hh⟩)
    h4_run rfl
  have hA3traj := composeFlatTM_no_early_halt (Compile.copyPipeA2TM_valid b dst hb)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (by show (13 + 3 * dst : Nat) < (Compile.copyPipeA2TM b dst).states
        rw [Compile.copyPipeA2TM_states]; omega)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (Compile.copyPipeA2TM b dst).states
        rw [Compile.copyPipeA2TM_states]; omega)
    [] ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length + res.length)
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    hsymA3 hA2run.1
    (fun k hk ck hck => by
      have hh := hA2traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hA2halt hh, hh⟩)
    (fun k hk ck hck => (h4_traj k hk ck hck).2)
  have hMA3 : Compile.copyPipeA3TM b dst
      = composeFlatTM (Compile.copyPipeA2TM b dst) (ScanLeft.scanLeftUntilTM 4 3)
          (13 + 3 * dst) := rfl
  have hexA3 : 1 + (Compile.copyPipeA2TM b dst).states = 15 + 3 * dst := by
    rw [Compile.copyPipeA2TM_states]; omega
  rw [hexA3] at hA3run
  have hA3halt : (Compile.copyPipeA3TM b dst).halt[15 + 3 * dst]? = some true := by
    have h := Compile.composeFlatTM_halt_intro (Compile.copyPipeA2TM b dst)
      (ScanLeft.scanLeftUntilTM 4 3) 1 (13 + 3 * dst) rfl
    rw [Compile.copyPipeA2TM_states] at h
    rw [hMA3, show (15 + 3 * dst : Nat) = 14 + 3 * dst + 1 from by omega]
    exact h
  -- ### stage 5: one step left off the terminator
  have h5_run := ScanLeft.stepLeftTM_run 4 []
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length hterm_lt
    (by rw [hterm_get']; decide)
  have h5_traj := ScanLeft.stepLeftTM_no_early_halt 4 []
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length
  -- ### level A4: copyPipeA3TM ⨾ stepLeftTM
  have hsymA4 : ∀ v, currentTapeSymbol
      ([], (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length,
        Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res) = some v →
      v < max (Compile.copyPipeA3TM b dst).sig (ScanLeft.stepLeftTM 4).sig := by
    intro v hv
    rw [show max (Compile.copyPipeA3TM b dst).sig (ScanLeft.stepLeftTM 4).sig = 4
      from by rw [Compile.copyPipeA3TM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hTmOut_lt4 _ v hv
  have hA4run := composeFlatTM_run (Compile.copyPipeA3TM_valid b dst hb)
    (ScanLeft.stepLeftTM_valid 4)
    (by show (15 + 3 * dst : Nat) < (Compile.copyPipeA3TM b dst).states
        rw [Compile.copyPipeA3TM_states]; omega)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (Compile.copyPipeA3TM b dst).states
        rw [Compile.copyPipeA3TM_states]; omega)
    [] (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    hsymA4 hA3run.1
    (fun k hk ck hck => by
      have hh := hA3traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hA3halt hh, hh⟩)
    h5_run rfl
  have hA4traj := composeFlatTM_no_early_halt (Compile.copyPipeA3TM_valid b dst hb)
    (ScanLeft.stepLeftTM_valid 4)
    (by show (15 + 3 * dst : Nat) < (Compile.copyPipeA3TM b dst).states
        rw [Compile.copyPipeA3TM_states]; omega)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (Compile.copyPipeA3TM b dst).states
        rw [Compile.copyPipeA3TM_states]; omega)
    [] (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    hsymA4 hA3run.1
    (fun k hk ck hck => by
      have hh := hA3traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hA3halt hh, hh⟩)
    (fun k hk ck hck => (h5_traj k hk ck hck).2)
  have hMA4 : Compile.copyPipeA4TM b dst
      = composeFlatTM (Compile.copyPipeA3TM b dst) (ScanLeft.stepLeftTM 4)
          (15 + 3 * dst) := rfl
  have hexA4 : 1 + (Compile.copyPipeA3TM b dst).states = 18 + 3 * dst := by
    rw [Compile.copyPipeA3TM_states]; omega
  rw [hexA4] at hA4run
  have hA4halt : (Compile.copyPipeA4TM b dst).halt[18 + 3 * dst]? = some true := by
    have h := Compile.composeFlatTM_halt_intro (Compile.copyPipeA3TM b dst)
      (ScanLeft.stepLeftTM 4) 1 (15 + 3 * dst) rfl
    rw [Compile.copyPipeA3TM_states] at h
    rw [hMA4, show (18 + 3 * dst : Nat) = 17 + 3 * dst + 1 from by omega]
    exact h
  -- ### stage 6: scan left to the mark (the only interior `3` of the q'-marked tape)
  obtain ⟨hP'lt, hP'get⟩ := Compile.markedTape_get_mark
    (State.set q dst (State.get q dst ++ [b])) src hsrc' w₁ w₂ 2 res
  have hP'3 : 1 + (Compile.encodeRegs ((State.set q dst
        (State.get q dst ++ [b])).take src)).length + w₁.length + 2
      ≤ (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length := by
    omega
  have hcells6 : ∀ i,
      1 + (Compile.encodeRegs ((State.set q dst
        (State.get q dst ++ [b])).take src)).length + w₁.length < i →
      i ≤ (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length - 1 →
      ∃ (h : i < (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res).length),
        (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res).get ⟨i, h⟩ < 4 ∧
        (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res).get ⟨i, h⟩ ≠ 3 := by
    intro i hgt hle
    exact Compile.markedTape_interior_cell (State.set q dst (State.get q dst ++ [b]))
      src hsrc' hbit' w₁ w₂ b hsplit' 2 res i (by omega) (by omega) (by omega)
  have hP'get3 : (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
        src (w₁ ++ 2 :: w₂)) ++ res).get
      ⟨1 + (Compile.encodeRegs ((State.set q dst
        (State.get q dst ++ [b])).take src)).length + w₁.length, hP'lt⟩ = 3 := by
    rw [hP'get]
  have h6_run := ScanLeft.scanLeftToMark_run 4 3 []
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    (1 + (Compile.encodeRegs ((State.set q dst
      (State.get q dst ++ [b])).take src)).length + w₁.length) hP'lt hP'get3
    ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length - 1
      - (1 + (Compile.encodeRegs ((State.set q dst
          (State.get q dst ++ [b])).take src)).length + w₁.length))
    ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length - 1)
    (by omega) (by omega) (fun i hgt hle => hcells6 i hgt hle)
  have h6_traj := ScanLeft.scanLeftToMark_no_early_halt 4 3 []
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    (1 + (Compile.encodeRegs ((State.set q dst
      (State.get q dst ++ [b])).take src)).length + w₁.length) hP'lt hP'get3
    ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length - 1
      - (1 + (Compile.encodeRegs ((State.set q dst
          (State.get q dst ++ [b])).take src)).length + w₁.length))
    ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length - 1)
    (by omega) (by omega) (fun i hgt hle => hcells6 i hgt hle)
  -- ### level A5: copyPipeA4TM ⨾ scanLeftUntilTM
  have hsymA5 : ∀ v, currentTapeSymbol
      ([], (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length - 1,
        Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res) = some v →
      v < max (Compile.copyPipeA4TM b dst).sig (ScanLeft.scanLeftUntilTM 4 3).sig := by
    intro v hv
    rw [show max (Compile.copyPipeA4TM b dst).sig (ScanLeft.scanLeftUntilTM 4 3).sig = 4
      from by rw [Compile.copyPipeA4TM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hTmOut_lt4 _ v hv
  have hA5run := composeFlatTM_run (Compile.copyPipeA4TM_valid b dst hb)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (by show (18 + 3 * dst : Nat) < (Compile.copyPipeA4TM b dst).states
        rw [Compile.copyPipeA4TM_states]; omega)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (Compile.copyPipeA4TM b dst).states
        rw [Compile.copyPipeA4TM_states]; omega)
    [] ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length - 1)
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    hsymA5 hA4run.1
    (fun k hk ck hck => by
      have hh := hA4traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hA4halt hh, hh⟩)
    h6_run rfl
  have hA5traj := composeFlatTM_no_early_halt (Compile.copyPipeA4TM_valid b dst hb)
    (ScanLeft.scanLeftUntilTM_valid 4 3 (by decide))
    (by show (18 + 3 * dst : Nat) < (Compile.copyPipeA4TM b dst).states
        rw [Compile.copyPipeA4TM_states]; omega)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (Compile.copyPipeA4TM b dst).states
        rw [Compile.copyPipeA4TM_states]; omega)
    [] ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length - 1)
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    hsymA5 hA4run.1
    (fun k hk ck hck => by
      have hh := hA4traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hA4halt hh, hh⟩)
    (fun k hk ck hck => (h6_traj k hk ck hck).2)
  have hMA5 : Compile.copyPipeA5TM b dst
      = composeFlatTM (Compile.copyPipeA4TM b dst) (ScanLeft.scanLeftUntilTM 4 3)
          (18 + 3 * dst) := rfl
  have hexA5 : 1 + (Compile.copyPipeA4TM b dst).states = 20 + 3 * dst := by
    rw [Compile.copyPipeA4TM_states]; omega
  rw [hexA5] at hA5run
  have hA5halt : (Compile.copyPipeA5TM b dst).halt[20 + 3 * dst]? = some true := by
    have h := Compile.composeFlatTM_halt_intro (Compile.copyPipeA4TM b dst)
      (ScanLeft.scanLeftUntilTM 4 3) 1 (18 + 3 * dst) rfl
    rw [Compile.copyPipeA4TM_states] at h
    rw [hMA5, show (20 + 3 * dst : Nat) = 19 + 3 * dst + 1 from by omega]
    exact h
  -- ### stage 7: restore the bit over the mark and step right
  have h7_run := Compile.restoreStepTM_run b hb []
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    (1 + (Compile.encodeRegs ((State.set q dst
      (State.get q dst ++ [b])).take src)).length + w₁.length) hP'lt hP'get3
  -- the restored tape is the un-marked `encodeTape q' ++ res`
  have hq'_restore : State.set (State.set q dst (State.get q dst ++ [b])) src
      (w₁ ++ b :: w₂) = State.set q dst (State.get q dst ++ [b]) := by
    rw [← hsplit']; exact Compile.set_get_self _ src hsrc'
  have hrestored := Compile.markedTape_take_drop
    (State.set q dst (State.get q dst ++ [b])) src hsrc' w₁ w₂ 2 b res
  rw [hq'_restore] at hrestored
  rw [hrestored] at h7_run
  -- ### final level: copyPipeA5TM ⨾ restoreStepTM
  have hsymF : ∀ v, currentTapeSymbol
      ([], 1 + (Compile.encodeRegs ((State.set q dst
        (State.get q dst ++ [b])).take src)).length + w₁.length,
        Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
          src (w₁ ++ 2 :: w₂)) ++ res) = some v →
      v < max (Compile.copyPipeA5TM b dst).sig (Compile.restoreStepTM b).sig := by
    intro v hv
    rw [show max (Compile.copyPipeA5TM b dst).sig (Compile.restoreStepTM b).sig = 4
      from by rw [Compile.copyPipeA5TM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hTmOut_lt4 _ v hv
  have hFrun := composeFlatTM_run (Compile.copyPipeA5TM_valid b dst hb)
    (Compile.restoreStepTM_valid b hb)
    (by show (20 + 3 * dst : Nat) < (Compile.copyPipeA5TM b dst).states
        rw [Compile.copyPipeA5TM_states]; omega)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (Compile.copyPipeA5TM b dst).states
        rw [Compile.copyPipeA5TM_states]; omega)
    [] (1 + (Compile.encodeRegs ((State.set q dst
      (State.get q dst ++ [b])).take src)).length + w₁.length)
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    hsymF hA5run.1
    (fun k hk ck hck => by
      have hh := hA5traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hA5halt hh, hh⟩)
    h7_run rfl
  have hFtraj := composeFlatTM_no_early_halt (Compile.copyPipeA5TM_valid b dst hb)
    (Compile.restoreStepTM_valid b hb)
    (by show (20 + 3 * dst : Nat) < (Compile.copyPipeA5TM b dst).states
        rw [Compile.copyPipeA5TM_states]; omega)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)] }
    (by show (0 : Nat) < (Compile.copyPipeA5TM b dst).states
        rw [Compile.copyPipeA5TM_states]; omega)
    [] (1 + (Compile.encodeRegs ((State.set q dst
      (State.get q dst ++ [b])).take src)).length + w₁.length)
    (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
      src (w₁ ++ 2 :: w₂)) ++ res)
    hsymF hA5run.1
    (fun k hk ck hck => by
      have hh := hA5traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hA5halt hh, hh⟩)
    (fun k hk ck hck => Compile.restoreStepTM_no_early_halt b [] _ _ k hk ck hck)
  have hMF : Compile.copyPipeTM b dst
      = composeFlatTM (Compile.copyPipeA5TM b dst) (Compile.restoreStepTM b)
          (20 + 3 * dst) := rfl
  have hexF : 1 + (Compile.copyPipeA5TM b dst).states = Compile.copyPipeTM_exit dst := by
    rw [Compile.copyPipeA5TM_states]
    show (1 + (22 + 3 * dst) : Nat) = 23 + 3 * dst
    omega
  rw [hexF] at hFrun
  -- ### assemble the statement
  have hLout : (Compile.encodeTape (State.set q dst (State.get q dst ++ [b]))
        ++ res).length
      = (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length + 1
        + res.length := by
    have hsame : (Compile.encodeTape (State.set q dst (State.get q dst ++ [b]))).length
        = (Compile.encodeTape (State.set (State.set q dst (State.get q dst ++ [b]))
            src (w₁ ++ 2 :: w₂))).length := by
      conv_lhs => rw [← hq'_restore]
      rw [Compile.encodeTape_set_cell_length _ src hsrc' w₁ w₂ b,
          Compile.encodeTape_set_cell_length _ src hsrc' w₁ w₂ 2]
    rw [List.length_append, hsame]
    omega
  have happ_le' : t₃ ≤ 2 * ((Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂))).length
      + res.length) + 3 := by
    rw [List.length_append] at happ_le; exact happ_le
  refine ⟨_, hFrun.1, ?_, ?_⟩
  · intro k hk ck hck
    have hh := hFtraj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.copyPipeTM_exit_is_halt b dst) hh, hh⟩
  · rw [hLout]
    omega

/-- **Cursor-loop body, ITERATE contract** (`loopTM_run`'s iteration shape).
From the un-marked cursor config (head ON src's cell `i = |w₁|`, a bit `b`),
`copyBodyTM dst` tests it (`delimTestTM`, content branch), marks it
(`markBitTM`), branch-bridges into `copyPipeTM b dst`, and (for `b = 1`, via
the extra `joinTwoHalts` bridge) lands at the merged iterate exit
`copyBody_exitLoop dst` on the next cursor config. -/
theorem Compile.copyBody_run_iter (q : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < q.length) (hsrc : src < q.length)
    (hbit : Compile.BitState q) (b : Nat) (hb : b ≤ 1) (w₁ w₂ : List Nat)
    (hsplit : State.get q src = w₁ ++ b :: w₂)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ T,
      runFlatTM T (Compile.copyBodyTM dst)
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                       Compile.encodeTape q ++ res)] }
        = some { state_idx := Compile.copyBody_exitLoop dst,
                 tapes := [([],
                   1 + (Compile.encodeRegs ((q.set dst (State.get q dst ++ [b])).take src)).length
                     + w₁.length + 1,
                   Compile.encodeTape (q.set dst (State.get q dst ++ [b])) ++ res)] }
      ∧ (∀ k, k < T → ∀ ck,
          runFlatTM k (Compile.copyBodyTM dst)
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                           Compile.encodeTape q ++ res)] } = some ck →
          ck.state_idx ≠ Compile.copyBody_exitDone dst ∧
          ck.state_idx ≠ Compile.copyBody_exitLoop dst ∧
          haltingStateReached (Compile.copyBodyTM dst) ck = false)
      ∧ T ≤ 5 * (Compile.encodeTape (q.set dst (State.get q dst ++ [b])) ++ res).length + 21 := by
  have hq : State.set q src (w₁ ++ b :: w₂) = q := by
    rw [← hsplit]; exact Compile.set_get_self q src hsrc
  -- work on the `set`-form of the input tape (the marked-tape helpers' shape).
  rw [show Compile.encodeTape q = Compile.encodeTape (State.set q src (w₁ ++ b :: w₂))
    from by rw [hq]]
  obtain ⟨hHlt, hHget⟩ := Compile.markedTape_get_mark q src hsrc w₁ w₂ b res
  -- bit-shape facts for the cell bounds
  have hw : ∀ y ∈ w₁ ++ b :: w₂, y ≤ 1 := by
    rw [← hsplit]
    intro y hy
    have hmem : State.get q src ∈ q := by
      rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
    exact hbit _ hmem y hy
  have hin_le2 : ∀ reg ∈ State.set q src (w₁ ++ b :: w₂), ∀ x ∈ reg, x ≤ 2 :=
    Compile.le_two_set q src _ hbit hsrc (fun x hx => le_trans (hw x hx) (by omega))
  have hTin_lt4 : ∀ x ∈ Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res,
      x < 4 := Compile.encodeTape_append_res_lt_four_le_two _ res hin_le2 hres
  have hqM_le2 : ∀ reg ∈ State.set q src (w₁ ++ 2 :: w₂), ∀ x ∈ reg, x ≤ 2 := by
    refine Compile.le_two_set q src _ hbit hsrc ?_
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact le_trans (hw x (List.mem_append_left _ h)) (by omega)
    · rcases List.mem_cons.mp h with h0 | h0
      · omega
      · exact le_trans (hw x (List.mem_append_right _ (List.mem_cons_of_mem _ h0)))
          (by omega)
  have hTm_lt4 : ∀ x ∈ Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res,
      x < 4 := Compile.encodeTape_append_res_lt_four_le_two _ res hqM_le2 hres
  have hbit' : Compile.BitState (State.set q dst (State.get q dst ++ [b])) := by
    refine Compile.BitState_set q dst _ hbit hdst ?_
    intro x hx
    have hu_mem : State.get q dst ∈ q := by
      rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
    rcases List.mem_append.mp hx with h | h
    · exact hbit _ hu_mem x h
    · rcases List.mem_cons.mp h with h0 | h0
      · subst h0; exact hb
      · cases h0
  have hTout_lt4 : ∀ x ∈ Compile.encodeTape (State.set q dst (State.get q dst ++ [b]))
      ++ res, x < 4 := Compile.encodeTape_append_res_lt_four _ res hbit' hres
  -- ### the `markBitTM` step: write the mark over the cursor bit
  have hmark_run := Compile.markBitTM_run b hb []
    (Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res)
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length) hHlt hHget
  have hmark_eq : (Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res).take
        (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
      ++ 3 :: (Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res).drop
        (1 + (Compile.encodeRegs (q.take src)).length + w₁.length + 1)
      = Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res := by
    have h := Compile.markedTape_take_drop q src hsrc w₁ w₂ b 2 res
    rw [show ((2 : Nat) + 1) = 3 from rfl] at h
    exact h
  rw [hmark_eq] at hmark_run
  -- ### the per-bit pipeline run on the marked tape
  obtain ⟨Tp, hpipe_run, hpipe_traj, hpipe_le⟩ :=
    Compile.copyPipe_run b hb q dst src hne hdst hsrc hbit w₁ w₂ hsplit res hres
  -- ### the content machine (markBit ⨾ branch into the two pipelines, joined)
  have hsym_content : ∀ v, currentTapeSymbol
      ([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
        Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res) = some v →
      v < max Compile.markBitTM.sig
            (max (Compile.copyPipeTM 0 dst).sig (Compile.copyPipeTM 1 dst).sig) := by
    intro v hv
    rw [show max Compile.markBitTM.sig
          (max (Compile.copyPipeTM 0 dst).sig (Compile.copyPipeTM 1 dst).sig) = 4 from by
      rw [Compile.markBitTM_sig, Compile.copyPipeTM_sig, Compile.copyPipeTM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hTm_lt4 _ v hv
  have hmark_traj : ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.markBitTM
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                       Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res)] }
        = some ck →
      ck.state_idx ≠ Compile.markBitTM_exit 0 ∧ ck.state_idx ≠ Compile.markBitTM_exit 1 ∧
      haltingStateReached Compile.markBitTM ck = false := by
    intro k hk ck hck
    have hk0 : k = 0 := by omega
    subst hk0
    simp [runFlatTM] at hck; subst hck
    exact ⟨show (0 : Nat) ≠ Compile.markBitTM_exit 0 from by decide,
           show (0 : Nat) ≠ Compile.markBitTM_exit 1 from by decide, rfl⟩
  have hh1 : (Compile.copyContentRawTM dst).halt[Compile.copyContent_exit0 dst]?
      = some true := by
    have h := Compile.branchComposeFlatTM_M2_halt_intro Compile.markBitTM
      (Compile.copyPipeTM 0 dst) (Compile.copyPipeTM 1 dst)
      (Compile.markBitTM_exit 0) (Compile.markBitTM_exit 1) (Compile.copyPipeTM_exit dst)
      (Compile.copyPipeTM_valid 0 dst (by decide))
      (by rw [Compile.copyPipeTM_states]
          show (23 + 3 * dst : Nat) < 24 + 3 * dst; omega)
      (Compile.copyPipeTM_exit_is_halt 0 dst)
    rw [Compile.markBitTM_states] at h
    exact h
  have hh2 : (Compile.copyContentRawTM dst).halt[Compile.copyContent_exit1 dst]?
      = some true := by
    have h := Compile.branchComposeFlatTM_M3_halt_intro Compile.markBitTM
      (Compile.copyPipeTM 0 dst) (Compile.copyPipeTM 1 dst)
      (Compile.markBitTM_exit 0) (Compile.markBitTM_exit 1) (Compile.copyPipeTM_exit dst)
      (Compile.copyPipeTM_valid 0 dst (by decide))
      (Compile.copyPipeTM_exit_is_halt 1 dst)
    rw [Compile.markBitTM_states, Compile.copyPipeTM_states] at h
    exact h
  have hexne : Compile.copyContent_exit0 dst ≠ Compile.copyContent_exit1 dst := by
    show (3 + (23 + 3 * dst) : Nat) ≠ 3 + (24 + 3 * dst) + (23 + 3 * dst); omega
  -- per-bit case split: assemble the joined content run.
  have hContent : ∃ Tc,
      runFlatTM Tc (Compile.copyContentTM dst)
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                       Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res)] }
        = some { state_idx := Compile.copyContent_exit0 dst,
                 tapes := [([],
                   1 + (Compile.encodeRegs ((q.set dst (State.get q dst ++ [b])).take
                     src)).length + w₁.length + 1,
                   Compile.encodeTape (q.set dst (State.get q dst ++ [b])) ++ res)] }
      ∧ (∀ k, k < Tc → ∀ ck,
          runFlatTM k (Compile.copyContentTM dst)
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                           Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res)] }
            = some ck →
          ck.state_idx ≠ Compile.copyContent_exit0 dst ∧
          haltingStateReached (Compile.copyContentTM dst) ck = false)
      ∧ Tc ≤ Tp + 3 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb0 | hb1
    · -- b = 0: positive branch of the raw content machine, exit kept by the join.
      subst hb0
      have hraw := branchComposeFlatTM_run_pos
        (show Compile.markBitTM_exit 0 ≠ Compile.markBitTM_exit 1 from by decide)
        Compile.markBitTM_valid (Compile.copyPipeTM_valid 0 dst (by decide))
        (Compile.copyPipeTM_valid 1 dst (by decide))
        (by rw [Compile.markBitTM_states]; decide)
        (by rw [Compile.markBitTM_states]; decide)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                     Compile.encodeTape (State.set q src (w₁ ++ 0 :: w₂)) ++ res)] }
        (by show (0 : Nat) < Compile.markBitTM.states; rw [Compile.markBitTM_states]; omega)
        [] (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
        (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
        hsym_content hmark_run hmark_traj
        (by rw [Compile.copyPipeTM_start]; exact hpipe_run)
        (Compile.haltingStateReached_of_halt (Compile.copyPipeTM_exit_is_halt 0 dst))
      have hraw_traj := branchComposeFlatTM_no_early_halt_pos
        Compile.markBitTM_valid (Compile.copyPipeTM_valid 0 dst (by decide))
        (Compile.copyPipeTM_valid 1 dst (by decide))
        (by rw [Compile.markBitTM_states]; decide)
        (by rw [Compile.markBitTM_states]; decide)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                     Compile.encodeTape (State.set q src (w₁ ++ 0 :: w₂)) ++ res)] }
        (by show (0 : Nat) < Compile.markBitTM.states; rw [Compile.markBitTM_states]; omega)
        [] (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
        (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
        hsym_content hmark_run hmark_traj
        (fun k hk ck hck => ((hpipe_traj k hk ck
          (by rw [Compile.copyPipeTM_start] at hck; exact hck)).2))
      have hst : Compile.copyPipeTM_exit dst + Compile.markBitTM.states
          = Compile.copyContent_exit0 dst := by
        rw [Compile.markBitTM_states]
        show (23 + 3 * dst : Nat) + 3 = 3 + (23 + 3 * dst); omega
      rw [hst] at hraw
      obtain ⟨hjrun, hjtraj⟩ := Compile.joinTwoHalts_reaches_kept
        (Compile.copyContentRawTM dst) (Compile.copyContent_exit0 dst)
        (Compile.copyContent_exit1 dst) _ _ _ hraw.1
        (fun k hk ck hck => hraw_traj k hk ck hck) hh1 hh2
      exact ⟨_, hjrun, hjtraj, by omega⟩
    · -- b = 1: negative branch, demoted exit, one extra join bridge step.
      subst hb1
      have hraw := branchComposeFlatTM_run_neg
        (show Compile.markBitTM_exit 0 ≠ Compile.markBitTM_exit 1 from by decide)
        Compile.markBitTM_valid (Compile.copyPipeTM_valid 0 dst (by decide))
        (Compile.copyPipeTM_valid 1 dst (by decide))
        (by rw [Compile.markBitTM_states]; decide)
        (by rw [Compile.markBitTM_states]; decide)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                     Compile.encodeTape (State.set q src (w₁ ++ 1 :: w₂)) ++ res)] }
        (by show (0 : Nat) < Compile.markBitTM.states; rw [Compile.markBitTM_states]; omega)
        [] (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
        (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
        hsym_content hmark_run hmark_traj
        (by rw [Compile.copyPipeTM_start]; exact hpipe_run)
        (Compile.haltingStateReached_of_halt (Compile.copyPipeTM_exit_is_halt 1 dst))
      have hraw_traj := branchComposeFlatTM_no_early_halt_neg
        (show Compile.markBitTM_exit 0 ≠ Compile.markBitTM_exit 1 from by decide)
        Compile.markBitTM_valid (Compile.copyPipeTM_valid 0 dst (by decide))
        (Compile.copyPipeTM_valid 1 dst (by decide))
        (by rw [Compile.markBitTM_states]; decide)
        (by rw [Compile.markBitTM_states]; decide)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                     Compile.encodeTape (State.set q src (w₁ ++ 1 :: w₂)) ++ res)] }
        (by show (0 : Nat) < Compile.markBitTM.states; rw [Compile.markBitTM_states]; omega)
        [] (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
        (Compile.encodeTape (State.set q src (w₁ ++ 2 :: w₂)) ++ res)
        hsym_content hmark_run hmark_traj
        (fun k hk ck hck => ((hpipe_traj k hk ck
          (by rw [Compile.copyPipeTM_start] at hck; exact hck)).2))
      have hst : Compile.copyPipeTM_exit dst
            + (Compile.markBitTM.states + (Compile.copyPipeTM 0 dst).states)
          = Compile.copyContent_exit1 dst := by
        rw [Compile.markBitTM_states, Compile.copyPipeTM_states]
        show (23 + 3 * dst : Nat) + (3 + (24 + 3 * dst))
            = 3 + (24 + 3 * dst) + (23 + 3 * dst)
        omega
      rw [hst] at hraw
      have hsym_final : ∀ v, currentTapeSymbol
          ([], 1 + (Compile.encodeRegs ((q.set dst (State.get q dst ++ [1])).take
              src)).length + w₁.length + 1,
            Compile.encodeTape (q.set dst (State.get q dst ++ [1])) ++ res) = some v →
          v < (Compile.copyContentRawTM dst).sig := by
        intro v hv
        rw [Compile.copyContentRawTM_sig]
        exact Compile.sym_bound_of_lt_four _ hTout_lt4 _ v hv
      obtain ⟨hjrun, hjtraj⟩ := Compile.joinTwoHalts_reaches_demoted
        (Compile.copyContentRawTM dst) (Compile.copyContent_exit0 dst)
        (Compile.copyContent_exit1 dst) _ _ _ _ _ hraw.1
        (fun k hk ck hck => hraw_traj k hk ck hck) hh1 hh2 hexne hsym_final
      exact ⟨_, hjrun, hjtraj, by omega⟩
  obtain ⟨Tc, hcontent_run, hcontent_traj, hTc_le⟩ := hContent
  -- ### the outer branch: delimiter test (content) ⨾ content machine
  have hdelim_run := ClearGadget.delimTestTM_run_content 4 (by decide) []
    (Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res)
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length) (b + 1) hHlt hHget
    (by omega) (by omega)
  have hsym_outer := Compile.copyBody_sym_bound dst
    (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
    (Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res) hTin_lt4
  have houter := branchComposeFlatTM_run_pos
    (show ClearGadget.delimTestTM_exit_content ≠ ClearGadget.delimTestTM_exit_delim
      from by decide)
    (ClearGadget.delimTestTM_valid 4 (by decide)) (Compile.copyContentTM_valid dst)
    Compile.idTM_valid
    (by rw [ClearGadget.delimTestTM_states]; decide)
    (by rw [ClearGadget.delimTestTM_states]; decide)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res)] }
    (by show (0 : Nat) < (ClearGadget.delimTestTM 4).states
        rw [ClearGadget.delimTestTM_states]; omega)
    [] (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
    (Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res)
    hsym_outer hdelim_run
    (fun k hk ck hck => ClearGadget.delimTestTM_no_early_halt 4 _ _ _ k hk ck hck)
    hcontent_run
    (Compile.haltingStateReached_of_halt (Compile.copyContentTM_exit_is_halt dst))
  have houter_traj := branchComposeFlatTM_no_early_halt_pos
    (ClearGadget.delimTestTM_valid 4 (by decide)) (Compile.copyContentTM_valid dst)
    Compile.idTM_valid
    (by rw [ClearGadget.delimTestTM_states]; decide)
    (by rw [ClearGadget.delimTestTM_states]; decide)
    { state_idx := 0,
      tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length + w₁.length,
                 Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res)] }
    (by show (0 : Nat) < (ClearGadget.delimTestTM 4).states
        rw [ClearGadget.delimTestTM_states]; omega)
    [] (1 + (Compile.encodeRegs (q.take src)).length + w₁.length)
    (Compile.encodeTape (State.set q src (w₁ ++ b :: w₂)) ++ res)
    hsym_outer hdelim_run
    (fun k hk ck hck => ClearGadget.delimTestTM_no_early_halt 4 _ _ _ k hk ck hck)
    (fun k hk ck hck => (hcontent_traj k hk ck hck).2)
  have hstout : Compile.copyContent_exit0 dst + (ClearGadget.delimTestTM 4).states
      = Compile.copyBody_exitLoop dst := by
    rw [ClearGadget.delimTestTM_states]
    show (3 + (23 + 3 * dst) : Nat) + 3 = 29 + 3 * dst
    omega
  rw [hstout] at houter
  refine ⟨_, houter.1, ?_, ?_⟩
  · intro k hk ck hck
    have hh := houter_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.copyBodyTM_exitDone_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (Compile.copyBodyTM_exitLoop_is_halt dst) hh, hh⟩
  · omega

/-- **The cursor cell.** Cell `1 + |encodeRegs (q.take src)| + i` of
`encodeTape q ++ res` is register `src`'s cell `i`: the shifted bit
`(q.get src)[i] + 1` for `i < |q.get src|`, and the register's `0` delimiter
for `i = |q.get src|`. -/
private theorem Compile.cursor_cell (q : State) (src : Var) (hsrc : src < q.length)
    (res : List Nat) (i : Nat) (hi : i ≤ (State.get q src).length) :
    ∃ (hlt : 1 + (Compile.encodeRegs (q.take src)).length + i
        < (Compile.encodeTape q ++ res).length),
      (Compile.encodeTape q ++ res).get
          ⟨1 + (Compile.encodeRegs (q.take src)).length + i, hlt⟩
        = if h : i < (State.get q src).length then (State.get q src)[i] + 1 else 0 := by
  have hdec := (Compile.encodeTape_reg_decomp_at q src hsrc).2
  set A := Compile.encodeRegs (q.take src) with hA
  set u := State.get q src with hu
  set R := Compile.encodeRegs (q.drop (src + 1)) ++ [Compile.endMark] with hR
  have htape : Compile.encodeTape q ++ res
      = ((3 : Nat) :: A) ++ (Compile.shiftReg u ++ 0 :: (R ++ res)) := by
    rw [hdec]
    show (Compile.endMark :: A) ++ (Compile.shiftReg u ++ (0 :: R)) ++ res = _
    simp [Compile.endMark, List.append_assoc]
  have hslen : (Compile.shiftReg u).length = u.length := by
    rw [Compile.shiftReg, List.length_map]
  have hmidlen : i < (Compile.shiftReg u ++ 0 :: (R ++ res)).length := by
    simp only [List.length_append, List.length_cons, hslen]; omega
  have hprelen : ((3 : Nat) :: A).length = 1 + A.length := by
    simp [Nat.add_comm]
  have hlt : 1 + A.length + i < (Compile.encodeTape q ++ res).length := by
    rw [htape, List.length_append, hprelen]
    omega
  refine ⟨hlt, ?_⟩
  have hcell? : (Compile.encodeTape q ++ res)[1 + A.length + i]?
      = (Compile.shiftReg u ++ 0 :: (R ++ res))[i]? := by
    rw [htape, List.getElem?_append_right (by rw [hprelen]; omega), hprelen,
        show 1 + A.length + i - (1 + A.length) = i from by omega]
  have hmid : (Compile.shiftReg u ++ 0 :: (R ++ res))[i]?
      = some (if h : i < u.length then u[i] + 1 else 0) := by
    by_cases h : i < u.length
    · rw [List.getElem?_append_left (by rw [hslen]; exact h), dif_pos h]
      rw [Compile.shiftReg, List.getElem?_map, List.getElem?_eq_getElem h]
      rfl
    · have hieq : i = u.length := by omega
      rw [List.getElem?_append_right (by rw [hslen]; omega), dif_neg h, hslen, hieq,
          Nat.sub_self]
      rfl
  rw [List.get_eq_getElem]
  have h2 := hcell?.trans hmid
  rw [List.getElem?_eq_getElem hlt] at h2
  exact Option.some_inj.mp h2

/-- **Cursor-loop body, DONE contract.** With the cursor ON src's `0` delimiter
(`i = |src|` — src exhausted), `delimTestTM` reads `0` (1 step) and the branch
bridge lands on `idTM`'s start = the done exit (1 step); tape and head
unchanged. -/
theorem Compile.copyBody_run_done (q : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < q.length) (hsrc : src < q.length)
    (hbit : Compile.BitState q)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    runFlatTM 2 (Compile.copyBodyTM dst)
        { state_idx := 0,
          tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length
                          + (State.get q src).length,
                     Compile.encodeTape q ++ res)] }
      = some { state_idx := Compile.copyBody_exitDone dst,
               tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length
                              + (State.get q src).length,
                          Compile.encodeTape q ++ res)] }
    ∧ (∀ k, k < 2 → ∀ ck,
        runFlatTM k (Compile.copyBodyTM dst)
            { state_idx := 0,
              tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length
                              + (State.get q src).length,
                         Compile.encodeTape q ++ res)] } = some ck →
        ck.state_idx ≠ Compile.copyBody_exitDone dst ∧
        ck.state_idx ≠ Compile.copyBody_exitLoop dst ∧
        haltingStateReached (Compile.copyBodyTM dst) ck = false) := by
  set H := 1 + (Compile.encodeRegs (q.take src)).length + (State.get q src).length with hHdef
  set tape := Compile.encodeTape q ++ res with htapedef
  obtain ⟨hlt, hcell⟩ := Compile.cursor_cell q src hsrc res (State.get q src).length le_rfl
  rw [dif_neg (lt_irrefl _)] at hcell
  set cfg0 : FlatTMConfig := { state_idx := 0, tapes := [([], H, tape)] } with hcfg0
  -- M₁ (delimTestTM) runs 1 step to the delimiter exit.
  have hrun1 : runFlatTM 1 (ClearGadget.delimTestTM 4) cfg0
      = some { state_idx := ClearGadget.delimTestTM_exit_delim, tapes := [([], H, tape)] } :=
    ClearGadget.delimTestTM_run_delim 4 (by decide) [] tape H hlt hcell
  have htraj1 : ∀ k, k < 1 → ∀ ck, runFlatTM k (ClearGadget.delimTestTM 4) cfg0 = some ck →
      ck.state_idx ≠ ClearGadget.delimTestTM_exit_content ∧
      ck.state_idx ≠ ClearGadget.delimTestTM_exit_delim ∧
      haltingStateReached (ClearGadget.delimTestTM 4) ck = false :=
    fun k hk ck hck => ClearGadget.delimTestTM_no_early_halt 4 [] tape H k hk ck hck
  -- M₃ (idTM) halts immediately.
  have hrun3 : runFlatTM 0 Compile.idTM
      { state_idx := Compile.idTM.start, tapes := [([], H, tape)] }
      = some { state_idx := 0, tapes := [([], H, tape)] } := rfl
  have hhalt3 : haltingStateReached Compile.idTM
      { state_idx := 0, tapes := [([], H, tape)] } = true := rfl
  have hsym := Compile.copyBody_sym_bound dst H tape
    (Compile.encodeTape_append_res_lt_four q res hbit hres)
  have hexitne : ClearGadget.delimTestTM_exit_content ≠ ClearGadget.delimTestTM_exit_delim := by
    decide
  have hcfg_lt : cfg0.state_idx < (ClearGadget.delimTestTM 4).states := by
    rw [ClearGadget.delimTestTM_states]; show 0 < 3; omega
  have hneg := branchComposeFlatTM_run_neg hexitne
    (ClearGadget.delimTestTM_valid 4 (by decide)) (Compile.copyContentTM_valid dst)
    Compile.idTM_valid
    (by rw [ClearGadget.delimTestTM_states]; decide)
    (by rw [ClearGadget.delimTestTM_states]; decide)
    cfg0 hcfg_lt [] H tape hsym hrun1 htraj1 hrun3 hhalt3
  have htrajneg := branchComposeFlatTM_no_early_halt_neg hexitne
    (ClearGadget.delimTestTM_valid 4 (by decide)) (Compile.copyContentTM_valid dst)
    Compile.idTM_valid
    (by rw [ClearGadget.delimTestTM_states]; decide)
    (by rw [ClearGadget.delimTestTM_states]; decide)
    cfg0 hcfg_lt [] H tape hsym (t₂ := 0) hrun1 htraj1
    (fun k hk ck hck => absurd hk (by omega))
  have hstate_eq : (0 : Nat) + ((ClearGadget.delimTestTM 4).states
      + (Compile.copyContentTM dst).states) = Compile.copyBody_exitDone dst := by
    rw [ClearGadget.delimTestTM_states, Compile.copyContentTM_states]
    show 0 + (3 + (51 + 6 * dst)) = 54 + 6 * dst; ring
  refine ⟨?_, ?_⟩
  · have h := hneg.1
    rw [hstate_eq] at h
    exact h
  · intro k hk ck hck
    have hh := htrajneg k (by omega) ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.copyBodyTM_exitDone_is_halt dst) hh,
           ClearGadget.ne_of_not_halting (Compile.copyBodyTM_exitLoop_is_halt dst) hh, hh⟩

/-- **The cursor-copy loop (`copyLoopTM dst`), assembled by `loopTM_run`.**
Entered with `dst` already cleared and the head on src's first cell, the loop
copies src bit-by-bit and halts at its dedicated halt state with the head on
src's delimiter. Tape sequence `T j = ([], cursor (n−j), encodeTape (s.set dst
(u.take (n−j))) ++ res)` (`u = s.get src`, `n = |u|`). -/
theorem Compile.copyLoop_run (s : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < s.length) (hsrc : src < s.length)
    (hbit : Compile.BitState s) (hdst_empty : State.get s dst = [])
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ T,
      runFlatTM T (Compile.copyLoopTM dst)
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.copyLoopTM_exit dst,
                 tapes := [([],
                   1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
                     + (State.get s src).length,
                   Compile.encodeTape (s.set dst (State.get s src)) ++ res)] }
      ∧ (∀ k, k < T → ∀ ck,
          runFlatTM k (Compile.copyLoopTM dst)
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                           Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.copyLoopTM_exit dst ∧
          haltingStateReached (Compile.copyLoopTM dst) ck = false)
      ∧ T ≤ ((State.get s src).length + 1)
              * (5 * (Compile.encodeTape (s.set dst (State.get s src)) ++ res).length + 23) := by
  set u := State.get s src with hu
  set n := u.length with hn
  -- the loop tape after `n − j` copied bits.
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 1 + (Compile.encodeRegs ((s.set dst (u.take (n - j))).take src)).length + (n - j),
     Compile.encodeTape (s.set dst (u.take (n - j))) ++ res) with hTdef
  have hu_le : ∀ x ∈ u, x ≤ 1 := by
    rw [hu]
    intro x hx
    have hmem : State.get s src ∈ s := by
      rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
    exact hbit _ hmem x hx
  have hset_nil : s.set dst ([] : List Nat) = s := by
    rw [← hdst_empty]; exact Compile.set_get_self s dst hdst
  -- per-`j` shared facts.
  have hbit_j : ∀ k, Compile.BitState (s.set dst (u.take k)) := fun k =>
    Compile.BitState_set s dst _ hbit hdst (fun x hx => hu_le x (List.mem_of_mem_take hx))
  have hlen_j : ∀ v : List Nat, (s.set dst v).length = s.length := fun v =>
    Compile.length_set s dst v hdst
  have hT_lt4 : ∀ j x, x ∈ (T j).2.2 → x < 4 := by
    intro j x hx
    simp only [hTdef] at hx
    exact Compile.encodeTape_append_res_lt_four _ res (hbit_j _) hres x hx
  have h_sym : ∀ m v, currentTapeSymbol (T m) = some v → v < (Compile.copyBodyTM dst).sig := by
    intro m v hv
    rw [Compile.copyBodyTM_sig]
    have hmem : v ∈ (T m).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_lt4 m v hmem
  -- tape lengths are monotone in the copied prefix (`dst` starts empty).
  have hLen_le : ∀ k, k ≤ n →
      (Compile.encodeTape (s.set dst (u.take k)) ++ res).length
        ≤ (Compile.encodeTape (s.set dst u) ++ res).length := by
    intro k hk
    have h1 := Compile.encodeTape_set_length s dst (u.take k) hdst
    have h2 := Compile.encodeTape_set_length s dst u hdst
    have h3 : (u.take k).length = k := by rw [List.length_take]; omega
    simp only [List.length_append]
    omega
  -- ### done contract at `T 0`... i.e. `j = 0`: `T 0` is the FINISHED tape.
  have hdone0 := Compile.copyBody_run_done (s.set dst u) dst src hne
    (by rw [hlen_j]; exact hdst) (by rw [hlen_j]; exact hsrc)
    (Compile.BitState_set s dst u hbit hdst hu_le) res hres
  have hget_src_set : State.get (s.set dst u) src = u := by
    rw [Compile.get_set_ne s dst u src hdst (Ne.symm hne), hu]
  have hT0 : T 0 = ([],
      1 + (Compile.encodeRegs ((s.set dst u).take src)).length + n,
      Compile.encodeTape (s.set dst u) ++ res) := by
    simp only [hTdef, Nat.sub_zero]
    rw [show u.take n = u from by rw [hn]; exact List.take_length]
  have h_done_full :
      runFlatTM 2 (Compile.copyBodyTM dst)
          { state_idx := (Compile.copyBodyTM dst).start, tapes := [T 0] }
        = some { state_idx := Compile.copyBody_exitDone dst, tapes := [T 0] } ∧
      (∀ k, k < 2 → ∀ ck,
          runFlatTM k (Compile.copyBodyTM dst)
              { state_idx := (Compile.copyBodyTM dst).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ Compile.copyBody_exitDone dst ∧
          ck.state_idx ≠ Compile.copyBody_exitLoop dst ∧
          haltingStateReached (Compile.copyBodyTM dst) ck = false) := by
    rw [hT0]
    have hdr := hdone0.1
    have hdt := hdone0.2
    rw [hget_src_set] at hdr hdt
    rw [show (Compile.copyBodyTM dst).start = 0 from rfl]
    exact ⟨by rw [← hn] at hdr; exact hdr, by rw [← hn] at hdt; exact hdt⟩
  -- ### iteration contract `T (j+1) → T j` for `j < n`.
  have hiter_ex : ∀ j, j < n → ∃ t,
      runFlatTM t (Compile.copyBodyTM dst)
          { state_idx := (Compile.copyBodyTM dst).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.copyBody_exitLoop dst, tapes := [T j] } ∧
      (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.copyBodyTM dst)
              { state_idx := (Compile.copyBodyTM dst).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ Compile.copyBody_exitDone dst ∧
          ck.state_idx ≠ Compile.copyBody_exitLoop dst ∧
          haltingStateReached (Compile.copyBodyTM dst) ck = false) ∧
      t ≤ 5 * (Compile.encodeTape (s.set dst u) ++ res).length + 21 := by
    intro j hj
    -- the cursor sits at bit `k₀ := n − j − 1` of `u`.
    have hk₀ : n - (j + 1) < u.length := by rw [← hn]; omega
    have hsplit_j : State.get (s.set dst (u.take (n - (j + 1)))) src
        = u.take (n - (j + 1)) ++ u[n - (j + 1)] :: u.drop (n - (j + 1) + 1) := by
      rw [Compile.get_set_ne s dst _ src hdst (Ne.symm hne), ← hu,
          ← List.drop_eq_getElem_cons hk₀, List.take_append_drop]
    obtain ⟨t, hrun, htraj, hbnd⟩ := Compile.copyBody_run_iter
      (s.set dst (u.take (n - (j + 1)))) dst src hne
      (by rw [hlen_j]; exact hdst) (by rw [hlen_j]; exact hsrc)
      (hbit_j _) u[n - (j + 1)]
      (hu_le _ (List.getElem_mem hk₀))
      (u.take (n - (j + 1))) (u.drop (n - (j + 1) + 1)) hsplit_j res hres
    -- rewrite the body's output state to `T j`'s state.
    have hstate_eq : (s.set dst (u.take (n - (j + 1)))).set dst
          (State.get (s.set dst (u.take (n - (j + 1)))) dst ++ [u[n - (j + 1)]])
        = s.set dst (u.take (n - j)) := by
      rw [Compile.get_set_eq s dst _ hdst, Compile.set_set s dst _ _ hdst,
          show u.take (n - (j + 1)) ++ [u[n - (j + 1)]] = u.take (n - (j + 1) + 1) from by
            rw [List.take_add_one, List.getElem?_eq_getElem hk₀]; rfl,
          show n - (j + 1) + 1 = n - j from by omega]
    rw [hstate_eq] at hrun hbnd
    -- align the heads with `T (j+1)` / `T j` (`|u.take k| = k`).
    have hhead_in : 1 + (Compile.encodeRegs ((s.set dst
          (u.take (n - (j + 1)))).take src)).length + (u.take (n - (j + 1))).length
        = 1 + (Compile.encodeRegs ((s.set dst
          (u.take (n - (j + 1)))).take src)).length + (n - (j + 1)) := by
      rw [List.length_take]; omega
    have hhead_out : 1 + (Compile.encodeRegs ((s.set dst
          (u.take (n - j))).take src)).length + (u.take (n - (j + 1))).length + 1
        = 1 + (Compile.encodeRegs ((s.set dst
          (u.take (n - j))).take src)).length + (n - j) := by
      rw [List.length_take]; omega
    rw [hhead_in, hhead_out] at hrun
    rw [hhead_in] at htraj
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [show (Compile.copyBodyTM dst).start = 0 from rfl]
      simp only [hTdef]
      exact hrun
    · rw [show (Compile.copyBodyTM dst).start = 0 from rfl]
      simp only [hTdef]
      exact htraj
    · have hmono := hLen_le (n - j) (by omega)
      omega
  -- ### assemble with `loopTM_run` / `loopTM_no_early_halt`.
  set tIter : Nat → Nat := fun j => if hj : j < n then (hiter_ex j hj).choose else 0
    with htIter
  have h_ne_exits : Compile.copyBody_exitDone dst ≠ Compile.copyBody_exitLoop dst := by
    show (54 + 6 * dst : Nat) ≠ 29 + 3 * dst; omega
  have h_done_lt : Compile.copyBody_exitDone dst < (Compile.copyBodyTM dst).states := by
    rw [Compile.copyBodyTM_states]
    show (54 + 6 * dst : Nat) < 55 + 6 * dst; omega
  have h_loop_lt : Compile.copyBody_exitLoop dst < (Compile.copyBodyTM dst).states := by
    rw [Compile.copyBodyTM_states]
    show (29 + 3 * dst : Nat) < 55 + 6 * dst; omega
  have h_iter_full : ∀ j, j < n →
      runFlatTM (tIter j) (Compile.copyBodyTM dst)
          { state_idx := (Compile.copyBodyTM dst).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.copyBody_exitLoop dst, tapes := [T j] } ∧
      (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (Compile.copyBodyTM dst)
              { state_idx := (Compile.copyBodyTM dst).start, tapes := [T (j + 1)] }
            = some ck →
          ck.state_idx ≠ Compile.copyBody_exitDone dst ∧
          ck.state_idx ≠ Compile.copyBody_exitLoop dst ∧
          haltingStateReached (Compile.copyBodyTM dst) ck = false) := by
    intro j hj
    have hspec := (hiter_ex j hj).choose_spec
    simp only [htIter, dif_pos hj]
    exact ⟨hspec.1, hspec.2.1⟩
  have h_iter_bnd : ∀ j, j < n → tIter j + 1
      ≤ 5 * (Compile.encodeTape (s.set dst u) ++ res).length + 23 := by
    intro j hj
    have hb := (hiter_ex j hj).choose_spec.2.2
    simp only [htIter, dif_pos hj]
    omega
  have hmain := loopTM_run (Compile.copyBodyTM dst) (Compile.copyBody_exitDone dst)
    (Compile.copyBody_exitLoop dst) (Compile.copyBodyTM_valid dst) h_done_lt h_loop_lt
    h_ne_exits T h_sym tIter 2 h_done_full n h_iter_full
  have hmain_traj := loopTM_no_early_halt (Compile.copyBodyTM dst)
    (Compile.copyBody_exitDone dst) (Compile.copyBody_exitLoop dst)
    (Compile.copyBodyTM_valid dst) h_done_lt h_loop_lt
    h_ne_exits T h_sym tIter 2 h_done_full n h_iter_full
  have hTn : T n = ([], 1 + (Compile.encodeRegs (s.take src)).length,
      Compile.encodeTape s ++ res) := by
    simp only [hTdef, Nat.sub_self, List.take_zero, hset_nil, Nat.add_zero]
  have hexit_halt : (Compile.copyLoopTM dst).halt[Compile.copyLoopTM_exit dst]?
      = some true := by
    show (List.replicate (Compile.copyBodyTM dst).states false
        ++ [true])[Compile.copyLoopTM_exit dst]? = some true
    rw [show Compile.copyLoopTM_exit dst = (Compile.copyBodyTM dst).states from by
          rw [Compile.copyBodyTM_states]; rfl,
        List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  have hex : (Compile.copyBodyTM dst).states = Compile.copyLoopTM_exit dst := by
    rw [Compile.copyBodyTM_states]; rfl
  rw [hex, hTn, hT0, show (Compile.copyBodyTM dst).start = 0 from rfl] at hmain
  rw [hTn, show (Compile.copyBodyTM dst).start = 0 from rfl] at hmain_traj
  refine ⟨loopBudget tIter 2 n, hmain, ?_, ?_⟩
  · intro k hk ck hck
    have hh := hmain_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting hexit_halt hh, hh⟩
  · exact Compile.loopBudget_le tIter 2
      (5 * (Compile.encodeTape (s.set dst u) ++ res).length + 23) n (by omega) h_iter_bnd

/-- **The `copy` op's exact-residue run lemma** (`dst ≠ src`): the full machine
`clear ⨾ navigate ⨾ cursor loop ⨾ rewind`, with the boundary halt demoted. The
residue formula is EXACT — `res_in ++ replicate |s.get dst| 0`, all of it from
the clear phase (the cursor loop adds none) — which is what the `compileForBnd`
combinator's tight W-invariant needs (HANDOFF bottom-up task 2). -/
theorem Compile.opCopy_run (s : State) (dst src : Var) (hne : dst ≠ src)
    (hdst : dst < s.length) (hsrc : src < s.length)
    (hbit : Compile.BitState s)
    (res_in : List Nat) (hres_in : Compile.ValidResidue res_in) :
    ∃ t,
      runFlatTM t (Compile.opCopy dst src).M
          (initFlatConfig (Compile.opCopy dst src).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opCopy dst src).exit,
                 tapes := [([], 0, Compile.encodeTape (s.set dst (State.get s src))
                            ++ (res_in ++ List.replicate (State.get s dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opCopy dst src).M
            (initFlatConfig (Compile.opCopy dst src).M [Compile.encodeTape s ++ res_in])
          = some ck →
        ck.state_idx ≠ (Compile.opCopy dst src).exit ∧
        haltingStateReached (Compile.opCopy dst src).M ck = false)
    ∧ t ≤ (9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
            + 9 * (Compile.encodeTape s ++ res_in).length + 30)
          * ((State.get s src).length + 2) := by
  -- unfold the `CompiledCmd` (the `dst = src` no-op branch is excluded by `hne`).
  have hM : (Compile.opCopy dst src).M
      = joinTwoHalts (Compile.copyRegionFullTM dst src)
          (Compile.copyRegionFullTM_exit dst src)
          (Compile.copyRegionFullTM_reject dst src) := by
    rw [Compile.opCopy, if_neg hne]
  have hexit : (Compile.opCopy dst src).exit = Compile.copyRegionFullTM_exit dst src := by
    rw [Compile.opCopy, if_neg hne]
  have hstart : (Compile.opCopy dst src).M.start = 0 := by
    rw [hM, joinTwoHalts_start]
    show (ClearGadget.navigateToRegTM dst).start = 0
    exact ClearGadget.navigateToRegTM_start dst
  have hinit : initFlatConfig (Compile.opCopy dst src).M [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hstart, List.map_cons, List.map_nil]
  rw [hinit, hM, hexit]
  -- ### shared abbreviation facts
  have hclear_eval : Op.eval (Op.clear dst) s = s.set dst [] := rfl
  have hs₁_len : (s.set dst ([] : List Nat)).length = s.length :=
    Compile.length_set s dst [] hdst
  have hdst₁ : dst < (s.set dst ([] : List Nat)).length := by rw [hs₁_len]; exact hdst
  have hsrc₁ : src < (s.set dst ([] : List Nat)).length := by rw [hs₁_len]; exact hsrc
  have hbit₁ : Compile.BitState (s.set dst ([] : List Nat)) :=
    Compile.BitState_set s dst [] hbit hdst (by intro x hx; cases hx)
  have hres₁ : Compile.ValidResidue (res_in ++ List.replicate (State.get s dst).length 0) :=
    Compile.ValidResidue_append_replicate_zero res_in _ hres_in
  have hget₁_src : State.get (s.set dst ([] : List Nat)) src = State.get s src :=
    Compile.get_set_ne s dst [] src hdst (Ne.symm hne)
  have hget₁_dst : State.get (s.set dst ([] : List Nat)) dst = [] :=
    Compile.get_set_eq s dst [] hdst
  have hset₁ : (s.set dst ([] : List Nat)).set dst (State.get s src)
      = s.set dst (State.get s src) := Compile.set_set s dst [] _ hdst
  -- ### phase 1: clear `dst`
  obtain ⟨tc, hclear_run, hclear_traj, hclear_le⟩ :=
    Compile.clearRegionTM_run s dst res_in hdst hbit hres_in
  rw [hclear_eval] at hclear_run
  -- ### phase 2: navigate to `src` (on the cleared tape)
  have hsk_len : ((List.take src (s.set dst ([] : List Nat))).map
      Compile.shiftReg).length = src := Compile.skipped_length _ src hsrc₁
  have hsk_ok : ∀ b ∈ (List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg,
      (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := Compile.skipped_ok _ src hbit₁
  have hdecomp : Compile.encodeTape (s.set dst ([] : List Nat))
        ++ (res_in ++ List.replicate (State.get s dst).length 0)
      = (3 : Nat) :: (AppendGadget.regBlocks
          ((List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg)
        ++ (Compile.shiftReg (State.get (s.set dst ([] : List Nat)) src)
            ++ 0 :: (Compile.encodeRegs (List.drop (src + 1) (s.set dst ([] : List Nat)))
              ++ [Compile.endMark]
              ++ (res_in ++ List.replicate (State.get s dst).length 0)))) := by
    have hsplit := Compile.encodeTape_split (s.set dst ([] : List Nat)) src hsrc₁
    rw [Compile.encodeTape, List.cons_append, ← hsplit]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hnav_run := ClearGadget.navigateToRegTM_run
    ((List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg)
    (Compile.shiftReg (State.get (s.set dst ([] : List Nat)) src)
      ++ 0 :: (Compile.encodeRegs (List.drop (src + 1) (s.set dst ([] : List Nat)))
        ++ [Compile.endMark]
        ++ (res_in ++ List.replicate (State.get s dst).length 0))) hsk_ok
  have hnav_traj := ClearGadget.navigateToRegTM_no_early_halt
    ((List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg)
    (Compile.shiftReg (State.get (s.set dst ([] : List Nat)) src)
      ++ 0 :: (Compile.encodeRegs (List.drop (src + 1) (s.set dst ([] : List Nat)))
        ++ [Compile.endMark]
        ++ (res_in ++ List.replicate (State.get s dst).length 0))) hsk_ok
  rw [hsk_len, ← hdecomp, Compile.regBlocks_map_shiftReg] at hnav_run
  rw [hsk_len, ← hdecomp] at hnav_traj
  -- ### phase 3: the cursor loop
  obtain ⟨tl, hloop_run, hloop_traj, hloop_le⟩ :=
    Compile.copyLoop_run (s.set dst ([] : List Nat)) dst src hne hdst₁ hsrc₁ hbit₁
      hget₁_dst (res_in ++ List.replicate (State.get s dst).length 0) hres₁
  rw [hget₁_src, hset₁] at hloop_run
  rw [hget₁_src, hset₁] at hloop_le
  -- ### phase 4: the final rewind (`justRewindTM` = scan left to the sentinel)
  have hs₂_len : (s.set dst (State.get s src)).length = s.length :=
    Compile.length_set s dst _ hdst
  have hsrc₂ : src < (s.set dst (State.get s src)).length := by rw [hs₂_len]; exact hsrc
  have hbit₂ : Compile.BitState (s.set dst (State.get s src)) :=
    Compile.BitState_set s dst _ hbit hdst (by
      intro x hx
      have hmem : State.get s src ∈ s := by
        rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
      exact hbit _ hmem x hx)
  have hget₂_src : State.get (s.set dst (State.get s src)) src = State.get s src :=
    Compile.get_set_ne s dst _ src hdst (Ne.symm hne)
  -- the rewind head sits on src's delimiter; at least the trailing terminator follows.
  have hHF2 : 1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
        + (State.get s src).length + 2
      ≤ (Compile.encodeTape (s.set dst (State.get s src))).length := by
    have hdec := congrArg List.length
      (Compile.encodeTape_reg_decomp_at (s.set dst (State.get s src)) src hsrc₂).2
    rw [hget₂_src] at hdec
    simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map,
      List.length_nil] at hdec
    omega
  have hTF_lt4 : ∀ x ∈ Compile.encodeTape (s.set dst (State.get s src))
      ++ (res_in ++ List.replicate (State.get s dst).length 0), x < 4 :=
    Compile.encodeTape_append_res_lt_four _ _ hbit₂ hres₁
  have h0F : 0 < (Compile.encodeTape (s.set dst (State.get s src))
      ++ (res_in ++ List.replicate (State.get s dst).length 0)).length := by
    rw [List.length_append, Compile.encodeTape_length]; omega
  have htargetF : (Compile.encodeTape (s.set dst (State.get s src))
      ++ (res_in ++ List.replicate (State.get s dst).length 0)).get ⟨0, h0F⟩ = 3 := by
    have hkey : (Compile.encodeTape (s.set dst (State.get s src))
        ++ (res_in ++ List.replicate (State.get s dst).length 0))[0]? = some 3 := by
      rw [Compile.encodeTape]; rfl
    rw [List.get_eq_getElem]
    exact Option.some_inj.mp ((List.getElem?_eq_getElem h0F).symm.trans hkey)
  have hcellsF : ∀ i, 0 < i →
      i ≤ 1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
        + (State.get s src).length →
      ∃ (h : i < (Compile.encodeTape (s.set dst (State.get s src))
          ++ (res_in ++ List.replicate (State.get s dst).length 0)).length),
        (Compile.encodeTape (s.set dst (State.get s src))
          ++ (res_in ++ List.replicate (State.get s dst).length 0)).get ⟨i, h⟩ < 4 ∧
        (Compile.encodeTape (s.set dst (State.get s src))
          ++ (res_in ++ List.replicate (State.get s dst).length 0)).get ⟨i, h⟩ ≠ 3 := by
    intro i hi0 hile
    have hi1 : i + 1 < (Compile.encodeTape (s.set dst (State.get s src))).length := by
      omega
    have hlt : i < (Compile.encodeTape (s.set dst (State.get s src))
        ++ (res_in ++ List.replicate (State.get s dst).length 0)).length := by
      rw [List.length_append]; omega
    refine ⟨hlt, ?_⟩
    have hilt_e : i < (Compile.encodeTape (s.set dst (State.get s src))).length := by omega
    have hkey : (Compile.encodeTape (s.set dst (State.get s src))
          ++ (res_in ++ List.replicate (State.get s dst).length 0))[i]?
        = some ((Compile.encodeTape (s.set dst (State.get s src))).get ⟨i, hilt_e⟩) := by
      rw [List.getElem?_append_left hilt_e, List.getElem?_eq_getElem hilt_e,
          List.get_eq_getElem]
    have hgeteq : (Compile.encodeTape (s.set dst (State.get s src))
          ++ (res_in ++ List.replicate (State.get s dst).length 0)).get ⟨i, hlt⟩
        = (Compile.encodeTape (s.set dst (State.get s src))).get ⟨i, hilt_e⟩ := by
      rw [List.get_eq_getElem]
      exact Option.some_inj.mp ((List.getElem?_eq_getElem hlt).symm.trans hkey)
    rw [hgeteq]
    obtain ⟨hi', hne3⟩ := Compile.encodeTape_interior_ne_endMark _ hbit₂ i hi0 hi1
    exact ⟨Compile.encodeTape_lt_four _ hbit₂ _ (List.get_mem _ _), hne3⟩
  have hrew_run := ScanLeft.scanLeft_run 4 3 []
    (Compile.encodeTape (s.set dst (State.get s src))
      ++ (res_in ++ List.replicate (State.get s dst).length 0)) h0F htargetF
    (1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
      + (State.get s src).length)
    (by rw [List.length_append]; omega) hcellsF
  have hrew_traj := ScanLeft.scanLeft_no_early_halt 4 3 []
    (Compile.encodeTape (s.set dst (State.get s src))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    (1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
      + (State.get s src).length)
    (by rw [List.length_append]; omega) hcellsF
  -- ### level C1: clear ⨾ navigate
  have hT1_lt4 : ∀ x ∈ Compile.encodeTape (s.set dst ([] : List Nat))
      ++ (res_in ++ List.replicate (State.get s dst).length 0), x < 4 :=
    Compile.encodeTape_append_res_lt_four _ _ hbit₁ hres₁
  have hsymC1 : ∀ v, currentTapeSymbol
      ([], 0, Compile.encodeTape (s.set dst ([] : List Nat))
        ++ (res_in ++ List.replicate (State.get s dst).length 0)) = some v →
      v < max (ClearGadget.clearRegionTM dst).sig (ClearGadget.navigateToRegTM src).sig := by
    intro v hv
    rw [show max (ClearGadget.clearRegionTM dst).sig (ClearGadget.navigateToRegTM src).sig = 4
      from by rw [ClearGadget.clearRegionTM_sig, ClearGadget.navigateToRegTM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hT1_lt4 _ v hv
  have hexC1_lt : ClearGadget.clearRegionTM_exit dst < (ClearGadget.clearRegionTM dst).states := by
    rw [ClearGadget.clearRegionTM_states]
    show (ClearGadget.clearBodyRawTM dst).states < (ClearGadget.clearBodyRawTM dst).states + 1
    omega
  have hC1run := composeFlatTM_run (ClearGadget.clearRegionTM_valid dst)
    (ClearGadget.navigateToRegTM_valid src) hexC1_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (ClearGadget.clearRegionTM dst).states
        rw [ClearGadget.clearRegionTM_states]; omega)
    [] 0 (Compile.encodeTape (s.set dst ([] : List Nat))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC1 hclear_run hclear_traj
    (by rw [ClearGadget.navigateToRegTM_start]; exact hnav_run)
    (Compile.haltingStateReached_of_halt (ClearGadget.navigateToRegTM_exit_is_halt src))
  have hC1traj := composeFlatTM_no_early_halt (ClearGadget.clearRegionTM_valid dst)
    (ClearGadget.navigateToRegTM_valid src) hexC1_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (ClearGadget.clearRegionTM dst).states
        rw [ClearGadget.clearRegionTM_states]; omega)
    [] 0 (Compile.encodeTape (s.set dst ([] : List Nat))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC1 hclear_run hclear_traj
    (fun k hk ck hck => hnav_traj k hk ck
      (by rw [ClearGadget.navigateToRegTM_start] at hck; exact hck))
  rw [Nat.add_comm (ClearGadget.navigateToRegTM_exit src)
      (ClearGadget.clearRegionTM dst).states] at hC1run
  have hC1halt := Compile.composeFlatTM_halt_intro (ClearGadget.clearRegionTM dst)
    (ClearGadget.navigateToRegTM src) (ClearGadget.navigateToRegTM_exit src)
    (ClearGadget.clearRegionTM_exit dst) (ClearGadget.navigateToRegTM_exit_is_halt src)
  -- ### level C2: ⨾ the cursor loop
  have hloopexit_halt : (Compile.copyLoopTM dst).halt[Compile.copyLoopTM_exit dst]?
      = some true := by
    show (List.replicate (Compile.copyBodyTM dst).states false
        ++ [true])[Compile.copyLoopTM_exit dst]? = some true
    rw [show Compile.copyLoopTM_exit dst = (Compile.copyBodyTM dst).states from by
          rw [Compile.copyBodyTM_states]; rfl,
        List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    rfl
  have hsymC2 : ∀ v, currentTapeSymbol
      ([], 1 + (Compile.encodeRegs (List.take src (s.set dst ([] : List Nat)))).length,
        Compile.encodeTape (s.set dst ([] : List Nat))
          ++ (res_in ++ List.replicate (State.get s dst).length 0)) = some v →
      v < max (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
          (ClearGadget.clearRegionTM_exit dst)).sig (Compile.copyLoopTM dst).sig := by
    intro v hv
    rw [show max (composeFlatTM (ClearGadget.clearRegionTM dst)
          (ClearGadget.navigateToRegTM src) (ClearGadget.clearRegionTM_exit dst)).sig
          (Compile.copyLoopTM dst).sig = 4 from by
      show max (max (ClearGadget.clearRegionTM dst).sig (ClearGadget.navigateToRegTM src).sig)
        (Compile.copyLoopTM dst).sig = 4
      rw [ClearGadget.clearRegionTM_sig, ClearGadget.navigateToRegTM_sig,
        Compile.copyLoopTM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hT1_lt4 _ v hv
  have hexC2_lt : (ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src
      < (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
          (ClearGadget.clearRegionTM_exit dst)).states := by
    rw [composeFlatTM_states]
    have := ClearGadget.navigateToRegTM_exit_lt src
    omega
  have hC2run := composeFlatTM_run
    (composeFlatTM_valid _ _ _ (ClearGadget.clearRegionTM_valid dst)
      (ClearGadget.navigateToRegTM_valid src) hexC1_lt
      (ClearGadget.clearRegionTM_tapes dst) (ClearGadget.navigateToRegTM_tapes src))
    (Compile.copyLoopTM_valid dst) hexC2_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (composeFlatTM _ _ _).states
        rw [composeFlatTM_states, ClearGadget.clearRegionTM_states]; omega)
    [] (1 + (Compile.encodeRegs (List.take src (s.set dst ([] : List Nat)))).length)
    (Compile.encodeTape (s.set dst ([] : List Nat))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC2 hC1run.1
    (fun k hk ck hck => by
      have hh := hC1traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hC1halt hh, hh⟩)
    hloop_run
    (Compile.haltingStateReached_of_halt hloopexit_halt)
  have hC2traj := composeFlatTM_no_early_halt
    (composeFlatTM_valid _ _ _ (ClearGadget.clearRegionTM_valid dst)
      (ClearGadget.navigateToRegTM_valid src) hexC1_lt
      (ClearGadget.clearRegionTM_tapes dst) (ClearGadget.navigateToRegTM_tapes src))
    (Compile.copyLoopTM_valid dst) hexC2_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (composeFlatTM _ _ _).states
        rw [composeFlatTM_states, ClearGadget.clearRegionTM_states]; omega)
    [] (1 + (Compile.encodeRegs (List.take src (s.set dst ([] : List Nat)))).length)
    (Compile.encodeTape (s.set dst ([] : List Nat))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC2 hC1run.1
    (fun k hk ck hck => by
      have hh := hC1traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hC1halt hh, hh⟩)
    (fun k hk ck hck => (hloop_traj k hk ck hck).2)
  have heq2 : Compile.copyLoopTM_exit dst
        + (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
            (ClearGadget.clearRegionTM_exit dst)).states
      = (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (55 + 6 * dst) := by
    rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states]
    show (55 + 6 * dst : Nat) + ((ClearGadget.clearRegionTM dst).states + (2 + 3 * src)) = _
    omega
  rw [heq2] at hC2run
  have hC2halt : (composeFlatTM
        (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
          (ClearGadget.clearRegionTM_exit dst))
        (Compile.copyLoopTM dst)
        ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src)).halt[
      (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (55 + 6 * dst)]?
      = some true := by
    have h := Compile.composeFlatTM_halt_intro
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.copyLoopTM dst) (Compile.copyLoopTM_exit dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src)
      hloopexit_halt
    rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states] at h
    rw [show (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (55 + 6 * dst)
          = (ClearGadget.clearRegionTM dst).states + (2 + 3 * src)
            + Compile.copyLoopTM_exit dst from by
        show _ = _ + (55 + 6 * dst); rfl]
    exact h
  -- ### level C3: ⨾ the final rewind
  have hTF_len_pos : 0 < (Compile.encodeTape (s.set dst (State.get s src))
      ++ (res_in ++ List.replicate (State.get s dst).length 0)).length := h0F
  have hsymC3 : ∀ v, currentTapeSymbol
      ([], 1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
        + (State.get s src).length,
        Compile.encodeTape (s.set dst (State.get s src))
          ++ (res_in ++ List.replicate (State.get s dst).length 0)) = some v →
      v < max (composeFlatTM
          (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
            (ClearGadget.clearRegionTM_exit dst))
          (Compile.copyLoopTM dst)
          ((ClearGadget.clearRegionTM dst).states
            + ClearGadget.navigateToRegTM_exit src)).sig ClearGadget.justRewindTM.sig := by
    intro v hv
    rw [show max (composeFlatTM
          (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
            (ClearGadget.clearRegionTM_exit dst))
          (Compile.copyLoopTM dst)
          ((ClearGadget.clearRegionTM dst).states
            + ClearGadget.navigateToRegTM_exit src)).sig ClearGadget.justRewindTM.sig = 4
      from by
      show max (max (max (ClearGadget.clearRegionTM dst).sig
          (ClearGadget.navigateToRegTM src).sig) (Compile.copyLoopTM dst).sig)
          ClearGadget.justRewindTM.sig = 4
      rw [ClearGadget.clearRegionTM_sig, ClearGadget.navigateToRegTM_sig,
        Compile.copyLoopTM_sig]
      rfl]
    exact Compile.sym_bound_of_lt_four _ hTF_lt4 _ v hv
  have hexC3_lt : (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (55 + 6 * dst)
      < (composeFlatTM
          (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
            (ClearGadget.clearRegionTM_exit dst))
          (Compile.copyLoopTM dst)
          ((ClearGadget.clearRegionTM dst).states
            + ClearGadget.navigateToRegTM_exit src)).states := by
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.copyLoopTM_states]
    omega
  have hC3run := composeFlatTM_run
    (composeFlatTM_valid _ _ _
      (composeFlatTM_valid _ _ _ (ClearGadget.clearRegionTM_valid dst)
        (ClearGadget.navigateToRegTM_valid src) hexC1_lt
        (ClearGadget.clearRegionTM_tapes dst) (ClearGadget.navigateToRegTM_tapes src))
      (Compile.copyLoopTM_valid dst) hexC2_lt
      (show (composeFlatTM _ _ _).tapes = 1 from ClearGadget.clearRegionTM_tapes dst)
      (Compile.copyLoopTM_tapes dst))
    ClearGadget.justRewindTM_valid hexC3_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (composeFlatTM _ _ _).states
        rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.clearRegionTM_states]
        omega)
    [] (1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
      + (State.get s src).length)
    (Compile.encodeTape (s.set dst (State.get s src))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC3 hC2run.1
    (fun k hk ck hck => by
      have hh := hC2traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hC2halt hh, hh⟩)
    hrew_run rfl
  have hC3traj := composeFlatTM_no_early_halt
    (composeFlatTM_valid _ _ _
      (composeFlatTM_valid _ _ _ (ClearGadget.clearRegionTM_valid dst)
        (ClearGadget.navigateToRegTM_valid src) hexC1_lt
        (ClearGadget.clearRegionTM_tapes dst) (ClearGadget.navigateToRegTM_tapes src))
      (Compile.copyLoopTM_valid dst) hexC2_lt
      (show (composeFlatTM _ _ _).tapes = 1 from ClearGadget.clearRegionTM_tapes dst)
      (Compile.copyLoopTM_tapes dst))
    ClearGadget.justRewindTM_valid hexC3_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (composeFlatTM _ _ _).states
        rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.clearRegionTM_states]
        omega)
    [] (1 + (Compile.encodeRegs ((s.set dst (State.get s src)).take src)).length
      + (State.get s src).length)
    (Compile.encodeTape (s.set dst (State.get s src))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC3 hC2run.1
    (fun k hk ck hck => by
      have hh := hC2traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hC2halt hh, hh⟩)
    (fun k hk ck hck => (hrew_traj k hk ck hck).2)
  have heq3 : (1 : Nat) + (composeFlatTM
        (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
          (ClearGadget.clearRegionTM_exit dst))
        (Compile.copyLoopTM dst)
        ((ClearGadget.clearRegionTM dst).states
          + ClearGadget.navigateToRegTM_exit src)).states
      = Compile.copyRegionFullTM_exit dst src := by
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.copyLoopTM_states]
    show (1 : Nat) + ((ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (56 + 6 * dst))
        = (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (56 + 6 * dst) + 1
    omega
  rw [heq3] at hC3run
  -- ### demote the boundary halt (joinTwoHalts) and conclude
  have hh2 : (Compile.copyRegionFullTM dst src).halt[
      Compile.copyRegionFullTM_reject dst src]? = some true := by
    have h := ScanLeft.composeFlatTM_halt_some_intro
      (composeFlatTM
        (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
          (ClearGadget.clearRegionTM_exit dst))
        (Compile.copyLoopTM dst)
        ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src))
      ClearGadget.justRewindTM
      ((ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (55 + 6 * dst))
      2 (by rfl)
    have hpre : (composeFlatTM
        (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
          (ClearGadget.clearRegionTM_exit dst))
        (Compile.copyLoopTM dst)
        ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src)).states
        = Compile.copyRegionPreStates dst src := by
      rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
          Compile.copyLoopTM_states]
      rfl
    rw [hpre] at h
    exact h
  obtain ⟨hjrun, hjtraj⟩ := Compile.joinTwoHalts_reaches_kept
    (Compile.copyRegionFullTM dst src) (Compile.copyRegionFullTM_exit dst src)
    (Compile.copyRegionFullTM_reject dst src)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    _ _ hC3run.1 (fun k hk ck hck => hC3traj k hk ck hck)
    (Compile.copyRegionFullTM_exit_is_halt dst src) hh2
  -- ### budget bookkeeping
  have hL1 : (Compile.encodeTape (s.set dst ([] : List Nat))
        ++ (res_in ++ List.replicate (State.get s dst).length 0)).length
      = (Compile.encodeTape s ++ res_in).length := by
    have hbal := Compile.encodeTape_set_length s dst [] hdst
    simp only [List.length_append, List.length_replicate, List.length_nil,
      Nat.add_zero] at hbal ⊢
    omega
  have hLF : (Compile.encodeTape (s.set dst (State.get s src))
        ++ (res_in ++ List.replicate (State.get s dst).length 0)).length
      = (Compile.encodeTape s ++ res_in).length + (State.get s src).length := by
    have hbal := Compile.encodeTape_set_length s dst (State.get s src) hdst
    simp only [List.length_append, List.length_replicate] at hbal ⊢
    omega
  have hnav_le : ClearGadget.navSteps
        ((List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg)
      ≤ 2 * (Compile.encodeTape s ++ res_in).length + 1 := by
    have h := ClearGadget.navSteps_le
      ((List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg)
    have hlen := congrArg List.length hdecomp
    rw [hL1] at hlen
    rw [Compile.regBlocks_map_shiftReg] at h
    simp only [List.length_cons, List.length_append, Compile.regBlocks_map_shiftReg] at hlen
    have hsplitq : (Compile.encodeTape s ++ res_in).length
        = (Compile.encodeTape s).length + res_in.length := by rw [List.length_append]
    omega
  have hn_le : (State.get s src).length + 3 ≤ (Compile.encodeTape s ++ res_in).length := by
    have hdec := congrArg List.length (Compile.encodeTape_reg_decomp_at s src hsrc).2
    simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map,
      List.length_nil] at hdec
    rw [List.length_append]
    omega
  have hbridge1 : 9 * (Compile.encodeTape s ++ res_in).length
      ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hinner : 5 * (Compile.encodeTape (s.set dst (State.get s src))
        ++ (res_in ++ List.replicate (State.get s dst).length 0)).length + 23
      ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
        + 9 * (Compile.encodeTape s ++ res_in).length + 30 := by
    rw [hLF]; omega
  have hloop2 : tl ≤ ((State.get s src).length + 1)
      * (9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
        + 9 * (Compile.encodeTape s ++ res_in).length + 30) :=
    le_trans hloop_le (Nat.mul_le_mul_left _ hinner)
  have hexpand : (9 * (Compile.encodeTape s ++ res_in).length
        * (Compile.encodeTape s ++ res_in).length
        + 9 * (Compile.encodeTape s ++ res_in).length + 30) * ((State.get s src).length + 2)
      = ((State.get s src).length + 1)
        * (9 * (Compile.encodeTape s ++ res_in).length
          * (Compile.encodeTape s ++ res_in).length
          + 9 * (Compile.encodeTape s ++ res_in).length + 30)
        + (9 * (Compile.encodeTape s ++ res_in).length
          * (Compile.encodeTape s ++ res_in).length
          + 9 * (Compile.encodeTape s ++ res_in).length + 30) := by
    ring
  refine ⟨_, hjrun, hjtraj, ?_⟩
  rw [hexpand]
  have hHF3 := hHF2
  have hf_le : (Compile.encodeTape (s.set dst (State.get s src))).length
      ≤ (Compile.encodeTape (s.set dst (State.get s src))
          ++ (res_in ++ List.replicate (State.get s dst).length 0)).length := by
    rw [List.length_append]; omega
  omega

/-! ### `tail` op run lemmas: `skipReadTM` steps, the offset cursor loop,
the branch stage, and the per-op assemblies (HANDOFF bottom-up task 1). -/

/-- `skipReadTM` on the `0` delimiter: exit `1`, no move, tape unchanged. -/
theorem Compile.skipReadTM_step_delim (left right : List Nat) (head : Nat)
    (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = 0) :
    stepFlatTM Compile.skipReadTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1, tapes := [(left, head, right)] } := by
  have hsym : currentTapeSymbol (left, head, right) = some 0 := by
    rw [currentTapeSymbol_in_range hlt, hget]
  simp_all [stepFlatTM, Compile.skipReadTM, Compile.skipReadDelimEntry,
    Compile.skipReadBitEntry, entryMatchesConfig, applyTransitionEntry, tapeStep,
    writeCurrentTapeSymbol, moveTapeHead]

/-- `skipReadTM_step_delim` in `runFlatTM` form. -/
theorem Compile.skipReadTM_run_delim (left right : List Nat) (head : Nat)
    (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = 0) :
    runFlatTM 1 Compile.skipReadTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 1, tapes := [(left, head, right)] } := by
  show (if haltingStateReached Compile.skipReadTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.skipReadTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.skipReadTM cfg') = _
  rw [show haltingStateReached Compile.skipReadTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.skipReadTM_step_delim left right head hlt hget]
  rfl

/-- `skipReadTM` on a content cell (shifted bit `b+1`): step right, exit `2`. -/
theorem Compile.skipReadTM_step_bit (b : Nat) (hb : b ≤ 1) (left right : List Nat)
    (head : Nat) (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = b + 1) :
    stepFlatTM Compile.skipReadTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 2, tapes := [(left, head + 1, right)] } := by
  have hsym : currentTapeSymbol (left, head, right) = some (b + 1) := by
    rw [currentTapeSymbol_in_range hlt, hget]
  interval_cases b <;>
    simp_all [stepFlatTM, Compile.skipReadTM, Compile.skipReadDelimEntry,
      Compile.skipReadBitEntry, entryMatchesConfig, applyTransitionEntry, tapeStep,
      writeCurrentTapeSymbol, moveTapeHead]

/-- `skipReadTM_step_bit` in `runFlatTM` form. -/
theorem Compile.skipReadTM_run_bit (b : Nat) (hb : b ≤ 1) (left right : List Nat)
    (head : Nat) (hlt : head < right.length) (hget : right.get ⟨head, hlt⟩ = b + 1) :
    runFlatTM 1 Compile.skipReadTM { state_idx := 0, tapes := [(left, head, right)] }
      = some { state_idx := 2, tapes := [(left, head + 1, right)] } := by
  show (if haltingStateReached Compile.skipReadTM
            { state_idx := 0, tapes := [(left, head, right)] } = true then _
        else match stepFlatTM Compile.skipReadTM
            { state_idx := 0, tapes := [(left, head, right)] } with
          | none => _ | some cfg' => runFlatTM 0 Compile.skipReadTM cfg') = _
  rw [show haltingStateReached Compile.skipReadTM
        { state_idx := 0, tapes := [(left, head, right)] } = false from rfl,
      Compile.skipReadTM_step_bit b hb left right head hlt hget]
  rfl

/-- `skipReadTM` never halts (nor sits on an exit) before its single step. -/
theorem Compile.skipReadTM_no_early_halt (left right : List Nat) (head : Nat) :
    ∀ k, k < 1 → ∀ ck,
      runFlatTM k Compile.skipReadTM
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ Compile.skipReadTM_exit_bit ∧
      ck.state_idx ≠ Compile.skipReadTM_exit_empty ∧
      haltingStateReached Compile.skipReadTM ck = false := by
  intro k hk ck hck
  have hk0 : k = 0 := by omega
  subst hk0
  simp [runFlatTM] at hck
  subst hck
  refine ⟨?_, ?_, rfl⟩
  · show (0 : Nat) ≠ 2; decide
  · show (0 : Nat) ≠ 1; decide

/-- **The cursor-copy loop entered ONE CELL INTO `src` — the `tail` instance.**
With `dst` pre-cleared and the head on `src`'s second cell (`skipReadTM` has
stepped over the first bit `b₀`), the loop copies `cs = (s.get src).tail`
bit-by-bit into `dst` and halts at its dedicated halt state with the head on
`src`'s delimiter. The mid-register start is free because the body contract
(`copyBody_run_iter`) is stated at an arbitrary split `w₁ ++ b :: w₂` — here
`w₁` always carries the skipped head bit `b₀`. Tape sequence
`T j = (cursor, encodeTape (s.set dst (cs.take (m−j))) ++ res)`, `m = |cs|`. -/
theorem Compile.tailLoop_run (s : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < s.length) (hsrc : src < s.length)
    (hbit : Compile.BitState s) (hdst_empty : State.get s dst = [])
    (b₀ : Nat) (cs : List Nat) (hsplit : State.get s src = b₀ :: cs)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ T,
      runFlatTM T (Compile.copyLoopTM dst)
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length + 1,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.copyLoopTM_exit dst,
                 tapes := [([],
                   1 + (Compile.encodeRegs ((s.set dst cs).take src)).length
                     + cs.length + 1,
                   Compile.encodeTape (s.set dst cs) ++ res)] }
      ∧ (∀ k, k < T → ∀ ck,
          runFlatTM k (Compile.copyLoopTM dst)
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length + 1,
                           Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.copyLoopTM_exit dst ∧
          haltingStateReached (Compile.copyLoopTM dst) ck = false)
      ∧ T ≤ (cs.length + 1)
              * (5 * (Compile.encodeTape (s.set dst cs) ++ res).length + 23) := by
  set m := cs.length with hm
  -- the loop tape after `m − j` copied bits (the cursor sits `1 + (m−j)` cells
  -- into src's block: the skipped `b₀` plus the copied prefix).
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 1 + (Compile.encodeRegs ((s.set dst (cs.take (m - j))).take src)).length
        + (m - j) + 1,
     Compile.encodeTape (s.set dst (cs.take (m - j))) ++ res) with hTdef
  have hsrc_mem : State.get s src ∈ s := by
    rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
  have hcs_le : ∀ x ∈ cs, x ≤ 1 := fun x hx =>
    hbit _ hsrc_mem x (by rw [hsplit]; exact List.mem_cons_of_mem _ hx)
  have hset_nil : s.set dst ([] : List Nat) = s := by
    rw [← hdst_empty]; exact Compile.set_get_self s dst hdst
  -- per-`j` shared facts.
  have hbit_j : ∀ k, Compile.BitState (s.set dst (cs.take k)) := fun k =>
    Compile.BitState_set s dst _ hbit hdst (fun x hx => hcs_le x (List.mem_of_mem_take hx))
  have hlen_j : ∀ v : List Nat, (s.set dst v).length = s.length := fun v =>
    Compile.length_set s dst v hdst
  have hT_lt4 : ∀ j x, x ∈ (T j).2.2 → x < 4 := by
    intro j x hx
    simp only [hTdef] at hx
    exact Compile.encodeTape_append_res_lt_four _ res (hbit_j _) hres x hx
  have h_sym : ∀ j v, currentTapeSymbol (T j) = some v → v < (Compile.copyBodyTM dst).sig := by
    intro j v hv
    rw [Compile.copyBodyTM_sig]
    have hmem : v ∈ (T j).2.2 := by
      simp only [currentTapeSymbol] at hv
      split at hv
      · injection hv with e; rw [← e]; exact List.get_mem _ _
      · exact absurd hv (by simp)
    exact hT_lt4 j v hmem
  -- tape lengths are monotone in the copied prefix (`dst` starts empty).
  have hLen_le : ∀ k, k ≤ m →
      (Compile.encodeTape (s.set dst (cs.take k)) ++ res).length
        ≤ (Compile.encodeTape (s.set dst cs) ++ res).length := by
    intro k hk
    have h1 := Compile.encodeTape_set_length s dst (cs.take k) hdst
    have h2 := Compile.encodeTape_set_length s dst cs hdst
    have h3 : (cs.take k).length = k := by rw [List.length_take]; omega
    simp only [List.length_append]
    omega
  -- ### done contract at `T 0` (all of `cs` copied; cursor on src's delimiter).
  have hget_src_set : State.get (s.set dst cs) src = b₀ :: cs := by
    rw [Compile.get_set_ne s dst cs src hdst (Ne.symm hne), hsplit]
  have hdone0 := Compile.copyBody_run_done (s.set dst cs) dst src hne
    (by rw [hlen_j]; exact hdst) (by rw [hlen_j]; exact hsrc)
    (Compile.BitState_set s dst cs hbit hdst hcs_le) res hres
  have hT0eq : T 0 = ([], 1 + (Compile.encodeRegs ((s.set dst cs).take src)).length
      + (State.get (s.set dst cs) src).length,
      Compile.encodeTape (s.set dst cs) ++ res) := by
    rw [hget_src_set]
    simp only [hTdef, Nat.sub_zero, List.length_cons]
    rw [show cs.take m = cs from by rw [hm]; exact List.take_length, hm,
        Nat.add_assoc (1 + (Compile.encodeRegs ((s.set dst cs).take src)).length) cs.length 1]
  have h_done_full :
      runFlatTM 2 (Compile.copyBodyTM dst)
          { state_idx := (Compile.copyBodyTM dst).start, tapes := [T 0] }
        = some { state_idx := Compile.copyBody_exitDone dst, tapes := [T 0] } ∧
      (∀ k, k < 2 → ∀ ck,
          runFlatTM k (Compile.copyBodyTM dst)
              { state_idx := (Compile.copyBodyTM dst).start, tapes := [T 0] } = some ck →
          ck.state_idx ≠ Compile.copyBody_exitDone dst ∧
          ck.state_idx ≠ Compile.copyBody_exitLoop dst ∧
          haltingStateReached (Compile.copyBodyTM dst) ck = false) := by
    rw [hT0eq, show (Compile.copyBodyTM dst).start = 0 from rfl]
    exact ⟨hdone0.1, hdone0.2⟩
  -- ### iteration contract `T (j+1) → T j` for `j < m`.
  have hiter_ex : ∀ j, j < m → ∃ t,
      runFlatTM t (Compile.copyBodyTM dst)
          { state_idx := (Compile.copyBodyTM dst).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.copyBody_exitLoop dst, tapes := [T j] } ∧
      (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.copyBodyTM dst)
              { state_idx := (Compile.copyBodyTM dst).start, tapes := [T (j + 1)] } = some ck →
          ck.state_idx ≠ Compile.copyBody_exitDone dst ∧
          ck.state_idx ≠ Compile.copyBody_exitLoop dst ∧
          haltingStateReached (Compile.copyBodyTM dst) ck = false) ∧
      t ≤ 5 * (Compile.encodeTape (s.set dst cs) ++ res).length + 21 := by
    intro j hj
    -- the cursor sits at bit `m − j − 1` of `cs` (cell `1 + (m − j − 1)` of src).
    have hk₀ : m - (j + 1) < cs.length := by omega
    have hsplit_j : State.get (s.set dst (cs.take (m - (j + 1)))) src
        = (b₀ :: cs.take (m - (j + 1))) ++ cs[m - (j + 1)] :: cs.drop (m - (j + 1) + 1) := by
      rw [Compile.get_set_ne s dst _ src hdst (Ne.symm hne), hsplit]
      show b₀ :: cs
          = b₀ :: (cs.take (m - (j + 1)) ++ cs[m - (j + 1)] :: cs.drop (m - (j + 1) + 1))
      rw [← List.drop_eq_getElem_cons hk₀, List.take_append_drop]
    obtain ⟨t, hrun, htraj, hbnd⟩ := Compile.copyBody_run_iter
      (s.set dst (cs.take (m - (j + 1)))) dst src hne
      (by rw [hlen_j]; exact hdst) (by rw [hlen_j]; exact hsrc)
      (hbit_j _) cs[m - (j + 1)]
      (hcs_le _ (List.getElem_mem hk₀))
      (b₀ :: cs.take (m - (j + 1))) (cs.drop (m - (j + 1) + 1)) hsplit_j res hres
    -- rewrite the body's output state to `T j`'s state.
    have hstate_eq : (s.set dst (cs.take (m - (j + 1)))).set dst
          (State.get (s.set dst (cs.take (m - (j + 1)))) dst ++ [cs[m - (j + 1)]])
        = s.set dst (cs.take (m - j)) := by
      rw [Compile.get_set_eq s dst _ hdst, Compile.set_set s dst _ _ hdst,
          show cs.take (m - (j + 1)) ++ [cs[m - (j + 1)]] = cs.take (m - (j + 1) + 1) from by
            rw [List.take_add_one, List.getElem?_eq_getElem hk₀]; rfl,
          show m - (j + 1) + 1 = m - j from by omega]
    rw [hstate_eq] at hrun hbnd
    -- align the heads with `T (j+1)` / `T j`.
    have hhead_in : 1 + (Compile.encodeRegs ((s.set dst
          (cs.take (m - (j + 1)))).take src)).length + (b₀ :: cs.take (m - (j + 1))).length
        = 1 + (Compile.encodeRegs ((s.set dst
          (cs.take (m - (j + 1)))).take src)).length + (m - (j + 1)) + 1 := by
      simp only [List.length_cons, List.length_take]
      omega
    have hhead_out : 1 + (Compile.encodeRegs ((s.set dst
          (cs.take (m - j))).take src)).length + (b₀ :: cs.take (m - (j + 1))).length + 1
        = 1 + (Compile.encodeRegs ((s.set dst
          (cs.take (m - j))).take src)).length + (m - j) + 1 := by
      simp only [List.length_cons, List.length_take]
      omega
    rw [hhead_in, hhead_out] at hrun
    rw [hhead_in] at htraj
    refine ⟨t, ?_, ?_, ?_⟩
    · rw [show (Compile.copyBodyTM dst).start = 0 from rfl]
      simp only [hTdef]
      exact hrun
    · rw [show (Compile.copyBodyTM dst).start = 0 from rfl]
      simp only [hTdef]
      exact htraj
    · have hmono := hLen_le (m - j) (by omega)
      omega
  -- ### assemble with `loopTM_run` / `loopTM_no_early_halt`.
  set tIter : Nat → Nat := fun j => if hj : j < m then (hiter_ex j hj).choose else 0
    with htIter
  have h_ne_exits : Compile.copyBody_exitDone dst ≠ Compile.copyBody_exitLoop dst := by
    show (54 + 6 * dst : Nat) ≠ 29 + 3 * dst; omega
  have h_done_lt : Compile.copyBody_exitDone dst < (Compile.copyBodyTM dst).states := by
    rw [Compile.copyBodyTM_states]
    show (54 + 6 * dst : Nat) < 55 + 6 * dst; omega
  have h_loop_lt : Compile.copyBody_exitLoop dst < (Compile.copyBodyTM dst).states := by
    rw [Compile.copyBodyTM_states]
    show (29 + 3 * dst : Nat) < 55 + 6 * dst; omega
  have h_iter_full : ∀ j, j < m →
      runFlatTM (tIter j) (Compile.copyBodyTM dst)
          { state_idx := (Compile.copyBodyTM dst).start, tapes := [T (j + 1)] }
        = some { state_idx := Compile.copyBody_exitLoop dst, tapes := [T j] } ∧
      (∀ k, k < tIter j → ∀ ck,
          runFlatTM k (Compile.copyBodyTM dst)
              { state_idx := (Compile.copyBodyTM dst).start, tapes := [T (j + 1)] }
            = some ck →
          ck.state_idx ≠ Compile.copyBody_exitDone dst ∧
          ck.state_idx ≠ Compile.copyBody_exitLoop dst ∧
          haltingStateReached (Compile.copyBodyTM dst) ck = false) := by
    intro j hj
    have hspec := (hiter_ex j hj).choose_spec
    simp only [htIter, dif_pos hj]
    exact ⟨hspec.1, hspec.2.1⟩
  have h_iter_bnd : ∀ j, j < m → tIter j + 1
      ≤ 5 * (Compile.encodeTape (s.set dst cs) ++ res).length + 23 := by
    intro j hj
    have hb := (hiter_ex j hj).choose_spec.2.2
    simp only [htIter, dif_pos hj]
    omega
  have hmain := loopTM_run (Compile.copyBodyTM dst) (Compile.copyBody_exitDone dst)
    (Compile.copyBody_exitLoop dst) (Compile.copyBodyTM_valid dst) h_done_lt h_loop_lt
    h_ne_exits T h_sym tIter 2 h_done_full m h_iter_full
  have hmain_traj := loopTM_no_early_halt (Compile.copyBodyTM dst)
    (Compile.copyBody_exitDone dst) (Compile.copyBody_exitLoop dst)
    (Compile.copyBodyTM_valid dst) h_done_lt h_loop_lt
    h_ne_exits T h_sym tIter 2 h_done_full m h_iter_full
  have hTm : T m = ([], 1 + (Compile.encodeRegs (s.take src)).length + 1,
      Compile.encodeTape s ++ res) := by
    simp only [hTdef, Nat.sub_self, List.take_zero, hset_nil]
  have hT0' : T 0 = ([], 1 + (Compile.encodeRegs ((s.set dst cs).take src)).length + m + 1,
      Compile.encodeTape (s.set dst cs) ++ res) := by
    simp only [hTdef, Nat.sub_zero]
    rw [show cs.take m = cs from by rw [hm]; exact List.take_length]
  have hexit_halt := Compile.copyLoopTM_exit_is_halt dst
  have hex : (Compile.copyBodyTM dst).states = Compile.copyLoopTM_exit dst := by
    rw [Compile.copyBodyTM_states]; rfl
  rw [hex, hTm, hT0', show (Compile.copyBodyTM dst).start = 0 from rfl] at hmain
  rw [hTm, show (Compile.copyBodyTM dst).start = 0 from rfl] at hmain_traj
  refine ⟨loopBudget tIter 2 m, hmain, ?_, ?_⟩
  · intro k hk ck hck
    have hh := hmain_traj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting hexit_halt hh, hh⟩
  · exact Compile.loopBudget_le tIter 2
      (5 * (Compile.encodeTape (s.set dst cs) ++ res).length + 23) m (by omega) h_iter_bnd

/-- **The `tail` branch stage (`tailBranchTM dst`).** Entered with `dst`
pre-cleared and the head ON register `src`'s first cell, it lands at the kept
exit with `dst = (src content).tail` and the head on `src`'s delimiter:
nonempty `src` → `skipReadTM` steps onto the second cell and the cursor loop
runs (kept exit directly); empty `src` → `skipReadTM` reads the delimiter, the
`idTM` no-op branch fires and the demoted empty exit bridges to the kept exit
(tape unchanged). -/
theorem Compile.tailBranch_run (q : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < q.length) (hsrc : src < q.length)
    (hbit : Compile.BitState q) (hdst_empty : State.get q dst = [])
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ T,
      runFlatTM T (Compile.tailBranchTM dst)
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length,
                       Compile.encodeTape q ++ res)] }
        = some { state_idx := Compile.tailBranch_keptExit dst,
                 tapes := [([],
                   1 + (Compile.encodeRegs
                       ((q.set dst (State.get q src).tail).take src)).length
                     + (State.get q src).length,
                   Compile.encodeTape (q.set dst (State.get q src).tail) ++ res)] }
      ∧ (∀ k, k < T → ∀ ck,
          runFlatTM k (Compile.tailBranchTM dst)
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (q.take src)).length,
                           Compile.encodeTape q ++ res)] } = some ck →
          ck.state_idx ≠ Compile.tailBranch_keptExit dst ∧
          haltingStateReached (Compile.tailBranchTM dst) ck = false)
      ∧ T ≤ (State.get q src).length
              * (5 * (Compile.encodeTape (q.set dst (State.get q src).tail) ++ res).length
                  + 23) + 3 := by
  have hq_lt4 : ∀ x ∈ Compile.encodeTape q ++ res, x < 4 :=
    Compile.encodeTape_append_res_lt_four _ res hbit hres
  have hexitne : Compile.skipReadTM_exit_bit ≠ Compile.skipReadTM_exit_empty := by
    show (2 : Nat) ≠ 1; decide
  have hcfg_lt : (0 : Nat) < Compile.skipReadTM.states := by
    rw [Compile.skipReadTM_states]; omega
  have hpos_lt : Compile.skipReadTM_exit_bit < Compile.skipReadTM.states := by
    rw [Compile.skipReadTM_states]; show (2 : Nat) < 3; omega
  have hneg_lt : Compile.skipReadTM_exit_empty < Compile.skipReadTM.states := by
    rw [Compile.skipReadTM_states]; show (1 : Nat) < 3; omega
  have hkept := Compile.tailBranchRawTM_keptExit_is_halt dst
  have hempty := Compile.tailBranchRawTM_emptyExit_is_halt dst
  have hne_ke : Compile.tailBranch_keptExit dst ≠ Compile.tailBranch_emptyExit dst := by
    rw [Compile.tailBranch_keptExit_eq, Compile.tailBranch_emptyExit_eq]; omega
  rcases hu : State.get q src with _ | ⟨b₀, cs⟩
  · -- ### empty src: the delimiter branch (idTM), demoted exit bridges to kept.
    obtain ⟨hlt, hcell⟩ := Compile.cursor_cell q src hsrc res 0 (Nat.zero_le _)
    rw [hu] at hcell
    rw [dif_neg (by simp)] at hcell
    have hskip := Compile.skipReadTM_run_delim []
      (Compile.encodeTape q ++ res) (1 + (Compile.encodeRegs (q.take src)).length) hlt hcell
    have hsymB : ∀ v, currentTapeSymbol (([] : List Nat),
        1 + (Compile.encodeRegs (q.take src)).length, Compile.encodeTape q ++ res) = some v →
        v < max Compile.skipReadTM.sig
            (max (Compile.copyLoopTM dst).sig Compile.idTM.sig) := by
      intro v hv
      rw [show max Compile.skipReadTM.sig
            (max (Compile.copyLoopTM dst).sig Compile.idTM.sig) = 4 from by
        rw [Compile.copyLoopTM_sig]; rfl]
      exact Compile.sym_bound_of_lt_four _ hq_lt4 _ v hv
    have hid : runFlatTM 0 Compile.idTM
        { state_idx := 0,
          tapes := [(([] : List Nat), 1 + (Compile.encodeRegs (q.take src)).length,
                     Compile.encodeTape q ++ res)] }
        = some { state_idx := 0,
                 tapes := [(([] : List Nat), 1 + (Compile.encodeRegs (q.take src)).length,
                            Compile.encodeTape q ++ res)] } := rfl
    have hneg := branchComposeFlatTM_run_neg hexitne Compile.skipReadTM_valid
      (Compile.copyLoopTM_valid dst) Compile.idTM_valid hpos_lt hneg_lt
      { state_idx := 0,
        tapes := [(([] : List Nat), 1 + (Compile.encodeRegs (q.take src)).length,
                   Compile.encodeTape q ++ res)] }
      hcfg_lt [] (1 + (Compile.encodeRegs (q.take src)).length) (Compile.encodeTape q ++ res)
      hsymB hskip (Compile.skipReadTM_no_early_halt _ _ _) hid rfl
    have htrajneg := branchComposeFlatTM_no_early_halt_neg hexitne Compile.skipReadTM_valid
      (Compile.copyLoopTM_valid dst) Compile.idTM_valid hpos_lt hneg_lt
      { state_idx := 0,
        tapes := [(([] : List Nat), 1 + (Compile.encodeRegs (q.take src)).length,
                   Compile.encodeTape q ++ res)] }
      hcfg_lt [] (1 + (Compile.encodeRegs (q.take src)).length) (Compile.encodeTape q ++ res)
      hsymB (t₂ := 0) hskip (Compile.skipReadTM_no_early_halt _ _ _)
      (fun k hk ck hck => absurd hk (by omega))
    have hstate_eq : (0 : Nat) + (Compile.skipReadTM.states + (Compile.copyLoopTM dst).states)
        = Compile.tailBranch_emptyExit dst := by
      rw [Compile.skipReadTM_states, Compile.tailBranch_emptyExit]
      omega
    have hrun_raw := hneg.1
    rw [hstate_eq] at hrun_raw
    obtain ⟨hjrun, hjtraj⟩ := Compile.joinTwoHalts_reaches_demoted
      (Compile.tailBranchRawTM dst) (Compile.tailBranch_keptExit dst)
      (Compile.tailBranch_emptyExit dst)
      { state_idx := 0,
        tapes := [(([] : List Nat), 1 + (Compile.encodeRegs (q.take src)).length,
                   Compile.encodeTape q ++ res)] }
      (1 + 1 + 0) [] (Compile.encodeTape q ++ res)
      (1 + (Compile.encodeRegs (q.take src)).length)
      hrun_raw (fun k hk ck hck => htrajneg k hk ck hck) hkept hempty hne_ke
      (fun v hv => by
        rw [Compile.tailBranchRawTM_sig]
        exact Compile.sym_bound_of_lt_four _ hq_lt4 _ v hv)
    have hsetq : q.set dst ([] : List Nat).tail = q := by
      show q.set dst ([] : List Nat) = q
      rw [← hdst_empty]
      exact Compile.set_get_self q dst hdst
    refine ⟨1 + 1 + 0 + 1, ?_, ?_, ?_⟩
    · rw [hsetq]
      simp only [List.length_nil, Nat.add_zero]
      exact hjrun
    · exact hjtraj
    · simp only [List.length_nil]
      omega
  · -- ### nonempty src: skip the head bit, run the cursor loop (kept exit).
    have hsrc_mem : State.get q src ∈ q := by
      rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
    have hb₀ : b₀ ≤ 1 :=
      hbit _ hsrc_mem b₀ (by rw [hu]; exact List.mem_cons_self ..)
    obtain ⟨hlt, hcell⟩ := Compile.cursor_cell q src hsrc res 0 (Nat.zero_le _)
    rw [hu] at hcell
    rw [dif_pos (by simp)] at hcell
    simp only [List.getElem_cons_zero] at hcell
    have hskip := Compile.skipReadTM_run_bit b₀ hb₀ []
      (Compile.encodeTape q ++ res) (1 + (Compile.encodeRegs (q.take src)).length) hlt hcell
    obtain ⟨Tl, hloop_run, hloop_traj, hloop_le⟩ :=
      Compile.tailLoop_run q dst src hne hdst hsrc hbit hdst_empty b₀ cs hu res hres
    have hsymB : ∀ v, currentTapeSymbol (([] : List Nat),
        1 + (Compile.encodeRegs (q.take src)).length + 1, Compile.encodeTape q ++ res)
          = some v →
        v < max Compile.skipReadTM.sig
            (max (Compile.copyLoopTM dst).sig Compile.idTM.sig) := by
      intro v hv
      rw [show max Compile.skipReadTM.sig
            (max (Compile.copyLoopTM dst).sig Compile.idTM.sig) = 4 from by
        rw [Compile.copyLoopTM_sig]; rfl]
      exact Compile.sym_bound_of_lt_four _ hq_lt4 _ v hv
    have hpos := branchComposeFlatTM_run_pos hexitne Compile.skipReadTM_valid
      (Compile.copyLoopTM_valid dst) Compile.idTM_valid hpos_lt hneg_lt
      { state_idx := 0,
        tapes := [(([] : List Nat), 1 + (Compile.encodeRegs (q.take src)).length,
                   Compile.encodeTape q ++ res)] }
      hcfg_lt [] (1 + (Compile.encodeRegs (q.take src)).length + 1)
      (Compile.encodeTape q ++ res)
      hsymB hskip (Compile.skipReadTM_no_early_halt _ _ _) hloop_run
      (Compile.haltingStateReached_of_halt (Compile.copyLoopTM_exit_is_halt dst))
    have htrajpos := branchComposeFlatTM_no_early_halt_pos Compile.skipReadTM_valid
      (Compile.copyLoopTM_valid dst) Compile.idTM_valid hpos_lt hneg_lt
      { state_idx := 0,
        tapes := [(([] : List Nat), 1 + (Compile.encodeRegs (q.take src)).length,
                   Compile.encodeTape q ++ res)] }
      hcfg_lt [] (1 + (Compile.encodeRegs (q.take src)).length + 1)
      (Compile.encodeTape q ++ res)
      hsymB hskip (Compile.skipReadTM_no_early_halt _ _ _)
      (fun k hk ck hck => (hloop_traj k hk ck hck).2)
    have hstate_eq : Compile.copyLoopTM_exit dst + Compile.skipReadTM.states
        = Compile.tailBranch_keptExit dst := by
      rw [Compile.skipReadTM_states, Compile.tailBranch_keptExit]
      omega
    have hrun_raw := hpos.1
    rw [hstate_eq] at hrun_raw
    obtain ⟨hjrun, hjtraj⟩ := Compile.joinTwoHalts_reaches_kept
      (Compile.tailBranchRawTM dst) (Compile.tailBranch_keptExit dst)
      (Compile.tailBranch_emptyExit dst)
      { state_idx := 0,
        tapes := [(([] : List Nat), 1 + (Compile.encodeRegs (q.take src)).length,
                   Compile.encodeTape q ++ res)] }
      (1 + 1 + Tl) _ hrun_raw (fun k hk ck hck => htrajpos k hk ck hck) hkept hempty
    refine ⟨1 + 1 + Tl, ?_, ?_, ?_⟩
    · simp only [List.tail_cons, List.length_cons]
      exact hjrun
    · exact hjtraj
    · simp only [List.tail_cons, List.length_cons]
      omega

/-- **`tail dst dst` (in-place), delete case** (`s.get dst ≠ []`): one
clear-style delete, exact residue `res ++ [0]`. The raw body run is
`clearBody_delete_run` (reaching the demoted content exit, bridged into the
kept done exit), then the `idTM` compose seam supplies the unique halt. -/
theorem Compile.opTailSelf_run_delete (s : State) (dst : Var)
    (hdst : dst < s.length) (hbit : Compile.BitState s) (hne : s.get dst ≠ [])
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.opTail dst dst).M
          (initFlatConfig (Compile.opTail dst dst).M [Compile.encodeTape s ++ res])
        = some { state_idx := (Compile.opTail dst dst).exit,
                 tapes := [([], 0,
                   Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.opTail dst dst).M
              (initFlatConfig (Compile.opTail dst dst).M [Compile.encodeTape s ++ res])
            = some ck →
          ck.state_idx ≠ (Compile.opTail dst dst).exit ∧
          haltingStateReached (Compile.opTail dst dst).M ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 14 := by
  have hM : (Compile.opTail dst dst).M = Compile.tailInPlaceTM dst := by
    rw [Compile.opTail, if_pos rfl]
  have hexit : (Compile.opTail dst dst).exit = Compile.tailInPlaceTM_exit dst := by
    rw [Compile.opTail, if_pos rfl]
  have hstart : (Compile.opTail dst dst).M.start = 0 := by
    rw [hM]; exact Compile.tailInPlaceTM_start dst
  have hinit : initFlatConfig (Compile.opTail dst dst).M [Compile.encodeTape s ++ res]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    simp only [initFlatConfig, hstart, List.map_cons, List.map_nil]
  rw [hinit, hM, hexit]
  obtain ⟨T, hraw_run, hraw_traj, hraw_le⟩ :=
    Compile.clearBody_delete_run s dst res hdst hbit hne hres
  -- output tape cell bound (for the bridge/seam symbol side-conditions)
  have hbit_out : Compile.BitState (s.set dst (s.get dst).tail) :=
    Compile.BitState_set_tail s dst hbit hdst
  have hres_out : Compile.ValidResidue (res ++ [0]) :=
    Compile.ValidResidue_append_replicate_zero res 1 hres
  have hout_lt4 : ∀ x ∈ Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]),
      x < 4 := Compile.encodeTape_append_res_lt_four _ _ hbit_out hres_out
  -- demote the content exit into the kept done exit
  have hne_exits : ClearGadget.clearBodyRawTM_exitDone dst
      ≠ ClearGadget.clearBodyRawTM_exitLoop dst := by
    show (ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindRawTM.states
          + ClearGadget.justRewindTM_exit
        ≠ (ClearGadget.navigateAndTestTM dst).states + ClearGadget.stepDeleteRewindTM_exit
    show _ + 19 + 1 ≠ _ + 17
    omega
  obtain ⟨hjrun, hjtraj⟩ := Compile.joinTwoHalts_reaches_demoted
    (ClearGadget.clearBodyRawTM dst) (ClearGadget.clearBodyRawTM_exitDone dst)
    (ClearGadget.clearBodyRawTM_exitLoop dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    T [] (Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0])) 0
    hraw_run (fun k hk ck hck => (hraw_traj k hk ck hck).2.2)
    (ClearGadget.clearBodyRawTM_exitDone_is_halt dst)
    (ClearGadget.clearBodyRawTM_exitLoop_is_halt dst)
    hne_exits
    (fun v hv => by
      rw [Compile.clearBodyRawTM_sig]
      exact Compile.sym_bound_of_lt_four _ hout_lt4 _ v hv)
  -- compose with `idTM` (the unique-halt seam)
  have hid : runFlatTM 0 Compile.idTM
      { state_idx := 0,
        tapes := [(([] : List Nat), 0,
                   Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))] }
      = some { state_idx := 0,
               tapes := [(([] : List Nat), 0,
                          Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))] } :=
    rfl
  have hsymC : ∀ v, currentTapeSymbol (([] : List Nat), 0,
      Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0])) = some v →
      v < max (Compile.tailInPlaceRawTM dst).sig Compile.idTM.sig := by
    intro v hv
    rw [show max (Compile.tailInPlaceRawTM dst).sig Compile.idTM.sig = 4 from by
      show max (ClearGadget.clearBodyRawTM dst).sig Compile.idTM.sig = 4
      rw [Compile.clearBodyRawTM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hout_lt4 _ v hv
  have hstart_lt : (0 : Nat) < (Compile.tailInPlaceRawTM dst).states := by
    have h := (Compile.tailInPlaceRawTM_valid dst).1
    rwa [show (Compile.tailInPlaceRawTM dst).start = 0
      from Compile.clearBodyRawTM_start dst] at h
  have hcomp := composeFlatTM_run (Compile.tailInPlaceRawTM_valid dst) Compile.idTM_valid
    (show ClearGadget.clearBodyRawTM_exitDone dst < (Compile.tailInPlaceRawTM dst).states
      from ClearGadget.clearBodyRawTM_exitDone_lt dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    hstart_lt
    [] 0 (Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))
    hsymC hjrun hjtraj hid rfl
  have htrajC := composeFlatTM_no_early_halt (Compile.tailInPlaceRawTM_valid dst)
    Compile.idTM_valid
    (show ClearGadget.clearBodyRawTM_exitDone dst < (Compile.tailInPlaceRawTM dst).states
      from ClearGadget.clearBodyRawTM_exitDone_lt dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    hstart_lt
    [] 0 (Compile.encodeTape (s.set dst (s.get dst).tail) ++ (res ++ [0]))
    hsymC hjrun hjtraj (t₂ := 0)
    (fun k hk ck hck => absurd hk (by omega))
  have hfix : (0 : Nat) + (Compile.tailInPlaceRawTM dst).states
      = Compile.tailInPlaceTM_exit dst := by
    rw [Compile.tailInPlaceRawTM_states]
    show (0 : Nat) + (ClearGadget.clearBodyRawTM dst).states
        = (ClearGadget.clearBodyRawTM dst).states
    omega
  have hcrun := hcomp.1
  rw [hfix] at hcrun
  refine ⟨T + 1 + 1 + 0, hcrun, ?_, ?_⟩
  · intro k hk ck hck
    have hh := htrajC k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.tailInPlaceTM_exit_is_halt dst) hh, hh⟩
  · omega

/-- **`tail dst dst` (in-place), done case** (`s.get dst = []`): the body's
delimiter branch fires, the tape is unchanged, residue passes through. -/
theorem Compile.opTailSelf_run_done (s : State) (dst : Var)
    (hdst : dst < s.length) (hbit : Compile.BitState s) (hemp : s.get dst = [])
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.opTail dst dst).M
          (initFlatConfig (Compile.opTail dst dst).M [Compile.encodeTape s ++ res])
        = some { state_idx := (Compile.opTail dst dst).exit,
                 tapes := [([], 0, Compile.encodeTape s ++ res)] }
      ∧ (∀ k, k < t → ∀ ck,
          runFlatTM k (Compile.opTail dst dst).M
              (initFlatConfig (Compile.opTail dst dst).M [Compile.encodeTape s ++ res])
            = some ck →
          ck.state_idx ≠ (Compile.opTail dst dst).exit ∧
          haltingStateReached (Compile.opTail dst dst).M ck = false)
      ∧ t ≤ 6 * (Compile.encodeTape s ++ res).length + 13 := by
  have hM : (Compile.opTail dst dst).M = Compile.tailInPlaceTM dst := by
    rw [Compile.opTail, if_pos rfl]
  have hexit : (Compile.opTail dst dst).exit = Compile.tailInPlaceTM_exit dst := by
    rw [Compile.opTail, if_pos rfl]
  have hstart : (Compile.opTail dst dst).M.start = 0 := by
    rw [hM]; exact Compile.tailInPlaceTM_start dst
  have hinit : initFlatConfig (Compile.opTail dst dst).M [Compile.encodeTape s ++ res]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } := by
    simp only [initFlatConfig, hstart, List.map_cons, List.map_nil]
  rw [hinit, hM, hexit]
  obtain ⟨T, hraw_run, hraw_traj, hraw_le⟩ :=
    Compile.clearBody_done_run s dst res hdst hbit hemp hres
  have hin_lt4 : ∀ x ∈ Compile.encodeTape s ++ res, x < 4 :=
    Compile.encodeTape_append_res_lt_four _ res hbit hres
  -- kept route through the join (the done exit is the kept `h1`)
  obtain ⟨hjrun, hjtraj⟩ := Compile.joinTwoHalts_reaches_kept
    (ClearGadget.clearBodyRawTM dst) (ClearGadget.clearBodyRawTM_exitDone dst)
    (ClearGadget.clearBodyRawTM_exitLoop dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    T ([], 0, Compile.encodeTape s ++ res)
    hraw_run (fun k hk ck hck => (hraw_traj k hk ck hck).2.2)
    (ClearGadget.clearBodyRawTM_exitDone_is_halt dst)
    (ClearGadget.clearBodyRawTM_exitLoop_is_halt dst)
  have hid : runFlatTM 0 Compile.idTM
      { state_idx := 0, tapes := [(([] : List Nat), 0, Compile.encodeTape s ++ res)] }
      = some { state_idx := 0,
               tapes := [(([] : List Nat), 0, Compile.encodeTape s ++ res)] } := rfl
  have hsymC : ∀ v, currentTapeSymbol (([] : List Nat), 0, Compile.encodeTape s ++ res)
      = some v → v < max (Compile.tailInPlaceRawTM dst).sig Compile.idTM.sig := by
    intro v hv
    rw [show max (Compile.tailInPlaceRawTM dst).sig Compile.idTM.sig = 4 from by
      show max (ClearGadget.clearBodyRawTM dst).sig Compile.idTM.sig = 4
      rw [Compile.clearBodyRawTM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hin_lt4 _ v hv
  have hstart_lt : (0 : Nat) < (Compile.tailInPlaceRawTM dst).states := by
    have h := (Compile.tailInPlaceRawTM_valid dst).1
    rwa [show (Compile.tailInPlaceRawTM dst).start = 0
      from Compile.clearBodyRawTM_start dst] at h
  have hcomp := composeFlatTM_run (Compile.tailInPlaceRawTM_valid dst) Compile.idTM_valid
    (show ClearGadget.clearBodyRawTM_exitDone dst < (Compile.tailInPlaceRawTM dst).states
      from ClearGadget.clearBodyRawTM_exitDone_lt dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    hstart_lt
    [] 0 (Compile.encodeTape s ++ res)
    hsymC hjrun hjtraj hid rfl
  have htrajC := composeFlatTM_no_early_halt (Compile.tailInPlaceRawTM_valid dst)
    Compile.idTM_valid
    (show ClearGadget.clearBodyRawTM_exitDone dst < (Compile.tailInPlaceRawTM dst).states
      from ClearGadget.clearBodyRawTM_exitDone_lt dst)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
    hstart_lt
    [] 0 (Compile.encodeTape s ++ res)
    hsymC hjrun hjtraj (t₂ := 0)
    (fun k hk ck hck => absurd hk (by omega))
  have hfix : (0 : Nat) + (Compile.tailInPlaceRawTM dst).states
      = Compile.tailInPlaceTM_exit dst := by
    rw [Compile.tailInPlaceRawTM_states]
    show (0 : Nat) + (ClearGadget.clearBodyRawTM dst).states
        = (ClearGadget.clearBodyRawTM dst).states
    omega
  have hcrun := hcomp.1
  rw [hfix] at hcrun
  refine ⟨T + 1 + 0, hcrun, ?_, ?_⟩
  · intro k hk ck hck
    have hh := htrajC k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.tailInPlaceTM_exit_is_halt dst) hh, hh⟩
  · omega

/-- **The `tail` op's exact-residue run lemma** (`dst ≠ src`): the full machine
`clear ⨾ navigate ⨾ (skipRead ⨠ cursor loop / idTM) ⨾ rewind`, with the rewind
boundary halt demoted. Exact residue `res_in ++ replicate |s.get dst| 0` — all
of it from the clear phase, exactly as `opCopy_run` (the branch stage adds
none), which is what the `compileForBnd` combinator's tight W-invariant needs. -/
theorem Compile.opTail_run (s : State) (dst src : Var) (hne : dst ≠ src)
    (hdst : dst < s.length) (hsrc : src < s.length)
    (hbit : Compile.BitState s)
    (res_in : List Nat) (hres_in : Compile.ValidResidue res_in) :
    ∃ t,
      runFlatTM t (Compile.opTail dst src).M
          (initFlatConfig (Compile.opTail dst src).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opTail dst src).exit,
                 tapes := [([], 0, Compile.encodeTape (s.set dst (State.get s src).tail)
                            ++ (res_in ++ List.replicate (State.get s dst).length 0))] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opTail dst src).M
            (initFlatConfig (Compile.opTail dst src).M [Compile.encodeTape s ++ res_in])
          = some ck →
        ck.state_idx ≠ (Compile.opTail dst src).exit ∧
        haltingStateReached (Compile.opTail dst src).M ck = false)
    ∧ t ≤ (9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
            + 9 * (Compile.encodeTape s ++ res_in).length + 30)
          * ((State.get s src).length + 2) := by
  -- unfold the `CompiledCmd` (the `dst = src` branch is excluded by `hne`).
  have hM : (Compile.opTail dst src).M
      = joinTwoHalts (Compile.tailRegionFullTM dst src)
          (Compile.tailRegionFullTM_exit dst src)
          (Compile.tailRegionFullTM_reject dst src) := by
    rw [Compile.opTail, if_neg hne]
  have hexit : (Compile.opTail dst src).exit = Compile.tailRegionFullTM_exit dst src := by
    rw [Compile.opTail, if_neg hne]
  have hstart : (Compile.opTail dst src).M.start = 0 := by
    rw [hM, joinTwoHalts_start]
    show (ClearGadget.navigateToRegTM dst).start = 0
    exact ClearGadget.navigateToRegTM_start dst
  have hinit : initFlatConfig (Compile.opTail dst src).M [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hstart, List.map_cons, List.map_nil]
  rw [hinit, hM, hexit]
  -- ### shared abbreviation facts
  have hclear_eval : Op.eval (Op.clear dst) s = s.set dst [] := rfl
  have hs₁_len : (s.set dst ([] : List Nat)).length = s.length :=
    Compile.length_set s dst [] hdst
  have hdst₁ : dst < (s.set dst ([] : List Nat)).length := by rw [hs₁_len]; exact hdst
  have hsrc₁ : src < (s.set dst ([] : List Nat)).length := by rw [hs₁_len]; exact hsrc
  have hbit₁ : Compile.BitState (s.set dst ([] : List Nat)) :=
    Compile.BitState_set s dst [] hbit hdst (by intro x hx; cases hx)
  have hres₁ : Compile.ValidResidue (res_in ++ List.replicate (State.get s dst).length 0) :=
    Compile.ValidResidue_append_replicate_zero res_in _ hres_in
  have hget₁_src : State.get (s.set dst ([] : List Nat)) src = State.get s src :=
    Compile.get_set_ne s dst [] src hdst (Ne.symm hne)
  have hget₁_dst : State.get (s.set dst ([] : List Nat)) dst = [] :=
    Compile.get_set_eq s dst [] hdst
  have hset₁ : (s.set dst ([] : List Nat)).set dst (State.get s src).tail
      = s.set dst (State.get s src).tail := Compile.set_set s dst [] _ hdst
  -- ### phase 1: clear `dst`
  obtain ⟨tc, hclear_run, hclear_traj, hclear_le⟩ :=
    Compile.clearRegionTM_run s dst res_in hdst hbit hres_in
  rw [hclear_eval] at hclear_run
  -- ### phase 2: navigate to `src` (on the cleared tape)
  have hsk_len : ((List.take src (s.set dst ([] : List Nat))).map
      Compile.shiftReg).length = src := Compile.skipped_length _ src hsrc₁
  have hsk_ok : ∀ b ∈ (List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg,
      (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4) := Compile.skipped_ok _ src hbit₁
  have hdecomp : Compile.encodeTape (s.set dst ([] : List Nat))
        ++ (res_in ++ List.replicate (State.get s dst).length 0)
      = (3 : Nat) :: (AppendGadget.regBlocks
          ((List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg)
        ++ (Compile.shiftReg (State.get (s.set dst ([] : List Nat)) src)
            ++ 0 :: (Compile.encodeRegs (List.drop (src + 1) (s.set dst ([] : List Nat)))
              ++ [Compile.endMark]
              ++ (res_in ++ List.replicate (State.get s dst).length 0)))) := by
    have hsplit := Compile.encodeTape_split (s.set dst ([] : List Nat)) src hsrc₁
    rw [Compile.encodeTape, List.cons_append, ← hsplit]
    simp only [Compile.endMark, List.append_assoc, List.cons_append]
  have hnav_run := ClearGadget.navigateToRegTM_run
    ((List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg)
    (Compile.shiftReg (State.get (s.set dst ([] : List Nat)) src)
      ++ 0 :: (Compile.encodeRegs (List.drop (src + 1) (s.set dst ([] : List Nat)))
        ++ [Compile.endMark]
        ++ (res_in ++ List.replicate (State.get s dst).length 0))) hsk_ok
  have hnav_traj := ClearGadget.navigateToRegTM_no_early_halt
    ((List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg)
    (Compile.shiftReg (State.get (s.set dst ([] : List Nat)) src)
      ++ 0 :: (Compile.encodeRegs (List.drop (src + 1) (s.set dst ([] : List Nat)))
        ++ [Compile.endMark]
        ++ (res_in ++ List.replicate (State.get s dst).length 0))) hsk_ok
  rw [hsk_len, ← hdecomp, Compile.regBlocks_map_shiftReg] at hnav_run
  rw [hsk_len, ← hdecomp] at hnav_traj
  -- ### phase 3: the branch stage (skip the head bit, cursor-copy the tail)
  obtain ⟨tb, hbr_run, hbr_traj, hbr_le⟩ :=
    Compile.tailBranch_run (s.set dst ([] : List Nat)) dst src hne hdst₁ hsrc₁ hbit₁
      hget₁_dst (res_in ++ List.replicate (State.get s dst).length 0) hres₁
  rw [hget₁_src, hset₁] at hbr_run
  rw [hget₁_src, hset₁] at hbr_le
  -- ### phase 4: the final rewind (`justRewindTM` = scan left to the sentinel)
  have hs₂_len : (s.set dst (State.get s src).tail).length = s.length :=
    Compile.length_set s dst _ hdst
  have hsrc₂ : src < (s.set dst (State.get s src).tail).length := by
    rw [hs₂_len]; exact hsrc
  have hbit₂ : Compile.BitState (s.set dst (State.get s src).tail) :=
    Compile.BitState_set s dst _ hbit hdst (by
      intro x hx
      have hmem : State.get s src ∈ s := by
        rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
      exact hbit _ hmem x (List.mem_of_mem_tail hx))
  have hget₂_src : State.get (s.set dst (State.get s src).tail) src = State.get s src :=
    Compile.get_set_ne s dst _ src hdst (Ne.symm hne)
  -- the rewind head sits on src's delimiter; at least the trailing terminator follows.
  have hHF2 : 1 + (Compile.encodeRegs ((s.set dst (State.get s src).tail).take src)).length
        + (State.get s src).length + 2
      ≤ (Compile.encodeTape (s.set dst (State.get s src).tail)).length := by
    have hdec := congrArg List.length
      (Compile.encodeTape_reg_decomp_at (s.set dst (State.get s src).tail) src hsrc₂).2
    rw [hget₂_src] at hdec
    simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map,
      List.length_nil] at hdec
    omega
  have hTF_lt4 : ∀ x ∈ Compile.encodeTape (s.set dst (State.get s src).tail)
      ++ (res_in ++ List.replicate (State.get s dst).length 0), x < 4 :=
    Compile.encodeTape_append_res_lt_four _ _ hbit₂ hres₁
  have h0F : 0 < (Compile.encodeTape (s.set dst (State.get s src).tail)
      ++ (res_in ++ List.replicate (State.get s dst).length 0)).length := by
    rw [List.length_append, Compile.encodeTape_length]; omega
  have htargetF : (Compile.encodeTape (s.set dst (State.get s src).tail)
      ++ (res_in ++ List.replicate (State.get s dst).length 0)).get ⟨0, h0F⟩ = 3 := by
    have hkey : (Compile.encodeTape (s.set dst (State.get s src).tail)
        ++ (res_in ++ List.replicate (State.get s dst).length 0))[0]? = some 3 := by
      rw [Compile.encodeTape]; rfl
    rw [List.get_eq_getElem]
    exact Option.some_inj.mp ((List.getElem?_eq_getElem h0F).symm.trans hkey)
  have hcellsF : ∀ i, 0 < i →
      i ≤ 1 + (Compile.encodeRegs ((s.set dst (State.get s src).tail).take src)).length
        + (State.get s src).length →
      ∃ (h : i < (Compile.encodeTape (s.set dst (State.get s src).tail)
          ++ (res_in ++ List.replicate (State.get s dst).length 0)).length),
        (Compile.encodeTape (s.set dst (State.get s src).tail)
          ++ (res_in ++ List.replicate (State.get s dst).length 0)).get ⟨i, h⟩ < 4 ∧
        (Compile.encodeTape (s.set dst (State.get s src).tail)
          ++ (res_in ++ List.replicate (State.get s dst).length 0)).get ⟨i, h⟩ ≠ 3 := by
    intro i hi0 hile
    have hi1 : i + 1 < (Compile.encodeTape (s.set dst (State.get s src).tail)).length := by
      omega
    have hlt : i < (Compile.encodeTape (s.set dst (State.get s src).tail)
        ++ (res_in ++ List.replicate (State.get s dst).length 0)).length := by
      rw [List.length_append]; omega
    refine ⟨hlt, ?_⟩
    have hilt_e : i < (Compile.encodeTape (s.set dst (State.get s src).tail)).length := by
      omega
    have hkey : (Compile.encodeTape (s.set dst (State.get s src).tail)
          ++ (res_in ++ List.replicate (State.get s dst).length 0))[i]?
        = some ((Compile.encodeTape (s.set dst (State.get s src).tail)).get ⟨i, hilt_e⟩) := by
      rw [List.getElem?_append_left hilt_e, List.getElem?_eq_getElem hilt_e,
          List.get_eq_getElem]
    have hgeteq : (Compile.encodeTape (s.set dst (State.get s src).tail)
          ++ (res_in ++ List.replicate (State.get s dst).length 0)).get ⟨i, hlt⟩
        = (Compile.encodeTape (s.set dst (State.get s src).tail)).get ⟨i, hilt_e⟩ := by
      rw [List.get_eq_getElem]
      exact Option.some_inj.mp ((List.getElem?_eq_getElem hlt).symm.trans hkey)
    rw [hgeteq]
    obtain ⟨hi', hne3⟩ := Compile.encodeTape_interior_ne_endMark _ hbit₂ i hi0 hi1
    exact ⟨Compile.encodeTape_lt_four _ hbit₂ _ (List.get_mem _ _), hne3⟩
  have hrew_run := ScanLeft.scanLeft_run 4 3 []
    (Compile.encodeTape (s.set dst (State.get s src).tail)
      ++ (res_in ++ List.replicate (State.get s dst).length 0)) h0F htargetF
    (1 + (Compile.encodeRegs ((s.set dst (State.get s src).tail).take src)).length
      + (State.get s src).length)
    (by rw [List.length_append]; omega) hcellsF
  have hrew_traj := ScanLeft.scanLeft_no_early_halt 4 3 []
    (Compile.encodeTape (s.set dst (State.get s src).tail)
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    (1 + (Compile.encodeRegs ((s.set dst (State.get s src).tail).take src)).length
      + (State.get s src).length)
    (by rw [List.length_append]; omega) hcellsF
  -- ### level C1: clear ⨾ navigate
  have hT1_lt4 : ∀ x ∈ Compile.encodeTape (s.set dst ([] : List Nat))
      ++ (res_in ++ List.replicate (State.get s dst).length 0), x < 4 :=
    Compile.encodeTape_append_res_lt_four _ _ hbit₁ hres₁
  have hsymC1 : ∀ v, currentTapeSymbol
      ([], 0, Compile.encodeTape (s.set dst ([] : List Nat))
        ++ (res_in ++ List.replicate (State.get s dst).length 0)) = some v →
      v < max (ClearGadget.clearRegionTM dst).sig (ClearGadget.navigateToRegTM src).sig := by
    intro v hv
    rw [show max (ClearGadget.clearRegionTM dst).sig (ClearGadget.navigateToRegTM src).sig = 4
      from by rw [ClearGadget.clearRegionTM_sig, ClearGadget.navigateToRegTM_sig]; rfl]
    exact Compile.sym_bound_of_lt_four _ hT1_lt4 _ v hv
  have hexC1_lt : ClearGadget.clearRegionTM_exit dst < (ClearGadget.clearRegionTM dst).states := by
    rw [ClearGadget.clearRegionTM_states]
    show (ClearGadget.clearBodyRawTM dst).states < (ClearGadget.clearBodyRawTM dst).states + 1
    omega
  have hC1run := composeFlatTM_run (ClearGadget.clearRegionTM_valid dst)
    (ClearGadget.navigateToRegTM_valid src) hexC1_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (ClearGadget.clearRegionTM dst).states
        rw [ClearGadget.clearRegionTM_states]; omega)
    [] 0 (Compile.encodeTape (s.set dst ([] : List Nat))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC1 hclear_run hclear_traj
    (by rw [ClearGadget.navigateToRegTM_start]; exact hnav_run)
    (Compile.haltingStateReached_of_halt (ClearGadget.navigateToRegTM_exit_is_halt src))
  have hC1traj := composeFlatTM_no_early_halt (ClearGadget.clearRegionTM_valid dst)
    (ClearGadget.navigateToRegTM_valid src) hexC1_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (ClearGadget.clearRegionTM dst).states
        rw [ClearGadget.clearRegionTM_states]; omega)
    [] 0 (Compile.encodeTape (s.set dst ([] : List Nat))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC1 hclear_run hclear_traj
    (fun k hk ck hck => hnav_traj k hk ck
      (by rw [ClearGadget.navigateToRegTM_start] at hck; exact hck))
  rw [Nat.add_comm (ClearGadget.navigateToRegTM_exit src)
      (ClearGadget.clearRegionTM dst).states] at hC1run
  have hC1halt := Compile.composeFlatTM_halt_intro (ClearGadget.clearRegionTM dst)
    (ClearGadget.navigateToRegTM src) (ClearGadget.navigateToRegTM_exit src)
    (ClearGadget.clearRegionTM_exit dst) (ClearGadget.navigateToRegTM_exit_is_halt src)
  -- ### level C2: ⨾ the branch stage
  have hsymC2 : ∀ v, currentTapeSymbol
      ([], 1 + (Compile.encodeRegs (List.take src (s.set dst ([] : List Nat)))).length,
        Compile.encodeTape (s.set dst ([] : List Nat))
          ++ (res_in ++ List.replicate (State.get s dst).length 0)) = some v →
      v < max (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
          (ClearGadget.clearRegionTM_exit dst)).sig (Compile.tailBranchTM dst).sig := by
    intro v hv
    rw [show max (composeFlatTM (ClearGadget.clearRegionTM dst)
          (ClearGadget.navigateToRegTM src) (ClearGadget.clearRegionTM_exit dst)).sig
          (Compile.tailBranchTM dst).sig = 4 from by
      show max (max (ClearGadget.clearRegionTM dst).sig (ClearGadget.navigateToRegTM src).sig)
        (Compile.tailBranchTM dst).sig = 4
      rw [ClearGadget.clearRegionTM_sig, ClearGadget.navigateToRegTM_sig,
        Compile.tailBranchTM_sig]
      rfl]
    exact Compile.sym_bound_of_lt_four _ hT1_lt4 _ v hv
  have hexC2_lt : (ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src
      < (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
          (ClearGadget.clearRegionTM_exit dst)).states := by
    rw [composeFlatTM_states]
    have := ClearGadget.navigateToRegTM_exit_lt src
    omega
  have hC2run := composeFlatTM_run
    (composeFlatTM_valid _ _ _ (ClearGadget.clearRegionTM_valid dst)
      (ClearGadget.navigateToRegTM_valid src) hexC1_lt
      (ClearGadget.clearRegionTM_tapes dst) (ClearGadget.navigateToRegTM_tapes src))
    (Compile.tailBranchTM_valid dst) hexC2_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (composeFlatTM _ _ _).states
        rw [composeFlatTM_states, ClearGadget.clearRegionTM_states]; omega)
    [] (1 + (Compile.encodeRegs (List.take src (s.set dst ([] : List Nat)))).length)
    (Compile.encodeTape (s.set dst ([] : List Nat))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC2 hC1run.1
    (fun k hk ck hck => by
      have hh := hC1traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hC1halt hh, hh⟩)
    hbr_run
    (Compile.haltingStateReached_of_halt (Compile.tailBranchTM_keptExit_is_halt dst))
  have hC2traj := composeFlatTM_no_early_halt
    (composeFlatTM_valid _ _ _ (ClearGadget.clearRegionTM_valid dst)
      (ClearGadget.navigateToRegTM_valid src) hexC1_lt
      (ClearGadget.clearRegionTM_tapes dst) (ClearGadget.navigateToRegTM_tapes src))
    (Compile.tailBranchTM_valid dst) hexC2_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (composeFlatTM _ _ _).states
        rw [composeFlatTM_states, ClearGadget.clearRegionTM_states]; omega)
    [] (1 + (Compile.encodeRegs (List.take src (s.set dst ([] : List Nat)))).length)
    (Compile.encodeTape (s.set dst ([] : List Nat))
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC2 hC1run.1
    (fun k hk ck hck => by
      have hh := hC1traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hC1halt hh, hh⟩)
    (fun k hk ck hck => (hbr_traj k hk ck hck).2)
  have heq2 : Compile.tailBranch_keptExit dst
        + (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
            (ClearGadget.clearRegionTM_exit dst)).states
      = (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (58 + 6 * dst) := by
    rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.tailBranch_keptExit_eq]
    omega
  rw [heq2] at hC2run
  have hC2halt : (composeFlatTM
        (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
          (ClearGadget.clearRegionTM_exit dst))
        (Compile.tailBranchTM dst)
        ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src)).halt[
      (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (58 + 6 * dst)]?
      = some true := by
    have h := Compile.composeFlatTM_halt_intro
      (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
        (ClearGadget.clearRegionTM_exit dst))
      (Compile.tailBranchTM dst) (Compile.tailBranch_keptExit dst)
      ((ClearGadget.clearRegionTM dst).states + ClearGadget.navigateToRegTM_exit src)
      (Compile.tailBranchTM_keptExit_is_halt dst)
    rw [composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.tailBranch_keptExit_eq] at h
    exact h
  -- ### level C3: ⨾ the final rewind
  have hsymC3 : ∀ v, currentTapeSymbol
      ([], 1 + (Compile.encodeRegs ((s.set dst (State.get s src).tail).take src)).length
        + (State.get s src).length,
        Compile.encodeTape (s.set dst (State.get s src).tail)
          ++ (res_in ++ List.replicate (State.get s dst).length 0)) = some v →
      v < max (composeFlatTM
          (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
            (ClearGadget.clearRegionTM_exit dst))
          (Compile.tailBranchTM dst)
          ((ClearGadget.clearRegionTM dst).states
            + ClearGadget.navigateToRegTM_exit src)).sig ClearGadget.justRewindTM.sig := by
    intro v hv
    rw [show max (composeFlatTM
          (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
            (ClearGadget.clearRegionTM_exit dst))
          (Compile.tailBranchTM dst)
          ((ClearGadget.clearRegionTM dst).states
            + ClearGadget.navigateToRegTM_exit src)).sig ClearGadget.justRewindTM.sig = 4
      from by
      show max (max (max (ClearGadget.clearRegionTM dst).sig
          (ClearGadget.navigateToRegTM src).sig) (Compile.tailBranchTM dst).sig)
          ClearGadget.justRewindTM.sig = 4
      rw [ClearGadget.clearRegionTM_sig, ClearGadget.navigateToRegTM_sig,
        Compile.tailBranchTM_sig]
      rfl]
    exact Compile.sym_bound_of_lt_four _ hTF_lt4 _ v hv
  have hexC3_lt : (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (58 + 6 * dst)
      < (composeFlatTM
          (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
            (ClearGadget.clearRegionTM_exit dst))
          (Compile.tailBranchTM dst)
          ((ClearGadget.clearRegionTM dst).states
            + ClearGadget.navigateToRegTM_exit src)).states := by
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.tailBranchTM_states]
    omega
  have hC3run := composeFlatTM_run
    (composeFlatTM_valid _ _ _
      (composeFlatTM_valid _ _ _ (ClearGadget.clearRegionTM_valid dst)
        (ClearGadget.navigateToRegTM_valid src) hexC1_lt
        (ClearGadget.clearRegionTM_tapes dst) (ClearGadget.navigateToRegTM_tapes src))
      (Compile.tailBranchTM_valid dst) hexC2_lt
      (show (composeFlatTM _ _ _).tapes = 1 from ClearGadget.clearRegionTM_tapes dst)
      (Compile.tailBranchTM_tapes dst))
    ClearGadget.justRewindTM_valid hexC3_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (composeFlatTM _ _ _).states
        rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.clearRegionTM_states]
        omega)
    [] (1 + (Compile.encodeRegs ((s.set dst (State.get s src).tail).take src)).length
      + (State.get s src).length)
    (Compile.encodeTape (s.set dst (State.get s src).tail)
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC3 hC2run.1
    (fun k hk ck hck => by
      have hh := hC2traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hC2halt hh, hh⟩)
    hrew_run rfl
  have hC3traj := composeFlatTM_no_early_halt
    (composeFlatTM_valid _ _ _
      (composeFlatTM_valid _ _ _ (ClearGadget.clearRegionTM_valid dst)
        (ClearGadget.navigateToRegTM_valid src) hexC1_lt
        (ClearGadget.clearRegionTM_tapes dst) (ClearGadget.navigateToRegTM_tapes src))
      (Compile.tailBranchTM_valid dst) hexC2_lt
      (show (composeFlatTM _ _ _).tapes = 1 from ClearGadget.clearRegionTM_tapes dst)
      (Compile.tailBranchTM_tapes dst))
    ClearGadget.justRewindTM_valid hexC3_lt
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    (by show (0 : Nat) < (composeFlatTM _ _ _).states
        rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.clearRegionTM_states]
        omega)
    [] (1 + (Compile.encodeRegs ((s.set dst (State.get s src).tail).take src)).length
      + (State.get s src).length)
    (Compile.encodeTape (s.set dst (State.get s src).tail)
      ++ (res_in ++ List.replicate (State.get s dst).length 0))
    hsymC3 hC2run.1
    (fun k hk ck hck => by
      have hh := hC2traj k hk ck hck
      exact ⟨ClearGadget.ne_of_not_halting hC2halt hh, hh⟩)
    (fun k hk ck hck => (hrew_traj k hk ck hck).2)
  have heq3 : (1 : Nat) + (composeFlatTM
        (composeFlatTM (ClearGadget.clearRegionTM dst) (ClearGadget.navigateToRegTM src)
          (ClearGadget.clearRegionTM_exit dst))
        (Compile.tailBranchTM dst)
        ((ClearGadget.clearRegionTM dst).states
          + ClearGadget.navigateToRegTM_exit src)).states
      = Compile.tailRegionFullTM_exit dst src := by
    rw [composeFlatTM_states, composeFlatTM_states, ClearGadget.navigateToRegTM_states,
        Compile.tailBranchTM_states]
    show (1 : Nat) + ((ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (60 + 6 * dst))
        = (ClearGadget.clearRegionTM dst).states + (2 + 3 * src) + (60 + 6 * dst) + 1
    omega
  rw [heq3] at hC3run
  -- ### demote the boundary halt (joinTwoHalts) and conclude
  obtain ⟨hjrun, hjtraj⟩ := Compile.joinTwoHalts_reaches_kept
    (Compile.tailRegionFullTM dst src) (Compile.tailRegionFullTM_exit dst src)
    (Compile.tailRegionFullTM_reject dst src)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    _ _ hC3run.1 (fun k hk ck hck => hC3traj k hk ck hck)
    (Compile.tailRegionFullTM_exit_is_halt dst src)
    (Compile.tailRegionFullTM_reject_is_halt dst src)
  -- ### budget bookkeeping
  have hL1 : (Compile.encodeTape (s.set dst ([] : List Nat))
        ++ (res_in ++ List.replicate (State.get s dst).length 0)).length
      = (Compile.encodeTape s ++ res_in).length := by
    have hbal := Compile.encodeTape_set_length s dst [] hdst
    simp only [List.length_append, List.length_replicate, List.length_nil,
      Nat.add_zero] at hbal ⊢
    omega
  have hLF : (Compile.encodeTape (s.set dst (State.get s src).tail)
        ++ (res_in ++ List.replicate (State.get s dst).length 0)).length
      = (Compile.encodeTape s ++ res_in).length + (State.get s src).tail.length := by
    have hbal := Compile.encodeTape_set_length s dst (State.get s src).tail hdst
    simp only [List.length_append, List.length_replicate] at hbal ⊢
    omega
  have htail_le : (State.get s src).tail.length ≤ (State.get s src).length := by
    have h : (State.get s src).tail.length = (State.get s src).length - 1 := List.length_tail
    omega
  have hnav_le : ClearGadget.navSteps
        ((List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg)
      ≤ 2 * (Compile.encodeTape s ++ res_in).length + 1 := by
    have h := ClearGadget.navSteps_le
      ((List.take src (s.set dst ([] : List Nat))).map Compile.shiftReg)
    have hlen := congrArg List.length hdecomp
    rw [hL1] at hlen
    rw [Compile.regBlocks_map_shiftReg] at h
    simp only [List.length_cons, List.length_append, Compile.regBlocks_map_shiftReg] at hlen
    have hsplitq : (Compile.encodeTape s ++ res_in).length
        = (Compile.encodeTape s).length + res_in.length := by rw [List.length_append]
    omega
  have hn_le : (State.get s src).length + 3 ≤ (Compile.encodeTape s ++ res_in).length := by
    have hdec := congrArg List.length (Compile.encodeTape_reg_decomp_at s src hsrc).2
    simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map,
      List.length_nil] at hdec
    rw [List.length_append]
    omega
  have hbridge1 : 9 * (Compile.encodeTape s ++ res_in).length
      ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hinner : 5 * (Compile.encodeTape (s.set dst (State.get s src).tail)
        ++ (res_in ++ List.replicate (State.get s dst).length 0)).length + 23
      ≤ 9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
        + 9 * (Compile.encodeTape s ++ res_in).length + 30 := by
    rw [hLF]; omega
  have hbranch2 : tb ≤ (State.get s src).length
      * (9 * (Compile.encodeTape s ++ res_in).length * (Compile.encodeTape s ++ res_in).length
        + 9 * (Compile.encodeTape s ++ res_in).length + 30) + 3 := by
    have hmul := Nat.mul_le_mul_left (State.get s src).length hinner
    omega
  have hexpand : (9 * (Compile.encodeTape s ++ res_in).length
        * (Compile.encodeTape s ++ res_in).length
        + 9 * (Compile.encodeTape s ++ res_in).length + 30) * ((State.get s src).length + 2)
      = (State.get s src).length
        * (9 * (Compile.encodeTape s ++ res_in).length
          * (Compile.encodeTape s ++ res_in).length
          + 9 * (Compile.encodeTape s ++ res_in).length + 30)
        + 2 * (9 * (Compile.encodeTape s ++ res_in).length
          * (Compile.encodeTape s ++ res_in).length
          + 9 * (Compile.encodeTape s ++ res_in).length + 30) := by
    ring
  refine ⟨_, hjrun, hjtraj, ?_⟩
  rw [hexpand]
  have hf_le : (Compile.encodeTape (s.set dst (State.get s src).tail)).length
      ≤ (Compile.encodeTape (s.set dst (State.get s src).tail)
          ++ (res_in ++ List.replicate (State.get s dst).length 0)).length := by
    rw [List.length_append]; omega
  omega

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

