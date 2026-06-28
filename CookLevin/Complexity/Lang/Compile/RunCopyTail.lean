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
import Complexity.Lang.Compile.RunMove

/-! # `Compile/RunCopyTail` — cursor-copy (`copy`) + `tail` run stacks (Phase 1-refinement)

Third module of the `RunLemmas` split (see `REFACTOR-HANDOFF.md`). The
cursor-copy run stack for the `copy` op (marked-tape toolkit, `copyPipe`/
`copyBody`/`copyLoop`/`opCopy`) and the `tail` op run stack. Imports `RunMove`
(transitively `RunClear`); consumed by `RunEqBit`. -/

set_option autoImplicit false

namespace Complexity.Lang

open TMPrimitives
open scoped BigOperators

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
    simp [hsym, hlt, stepFlatTM, Compile.markBitTM, Compile.markBitEntry,
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
    simp [hsym, hlt, stepFlatTM, Compile.restoreStepTM, Compile.restoreStepEntry,
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
theorem Compile.sym_bound_of_lt_four (tape : List Nat) (hall : ∀ x ∈ tape, x < 4)
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
theorem Compile.encodeTape_append_res_lt_four (q : State) (res : List Nat)
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

/-- **Generalised cursor-copy loop (`copyLoopTM dst`) — APPENDS src to dst.**
Entered with the head on src's first cell, the loop copies src bit-by-bit and
*appends* it to `dst`'s existing content `d₀`, halting at its dedicated halt
state with the head on src's delimiter. Tape sequence `T j = ([], cursor (n−j),
encodeTape (s.set dst (d₀ ++ u.take (n−j))) ++ res)` (`d₀ = s.get dst`,
`u = s.get src`, `n = |u|`). The empty-`dst` specialisation is `copyLoop_run`
below; `concat` needs this nonempty-`dst` form for its second copy. -/
theorem Compile.copyLoopAppend_run (s : State) (dst src : Var)
    (hne : dst ≠ src) (hdst : dst < s.length) (hsrc : src < s.length)
    (hbit : Compile.BitState s)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ T,
      runFlatTM T (Compile.copyLoopTM dst)
          { state_idx := 0,
            tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                       Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.copyLoopTM_exit dst,
                 tapes := [([],
                   1 + (Compile.encodeRegs ((s.set dst
                       (State.get s dst ++ State.get s src)).take src)).length
                     + (State.get s src).length,
                   Compile.encodeTape (s.set dst
                     (State.get s dst ++ State.get s src)) ++ res)] }
      ∧ (∀ k, k < T → ∀ ck,
          runFlatTM k (Compile.copyLoopTM dst)
              { state_idx := 0,
                tapes := [([], 1 + (Compile.encodeRegs (s.take src)).length,
                           Compile.encodeTape s ++ res)] } = some ck →
          ck.state_idx ≠ Compile.copyLoopTM_exit dst ∧
          haltingStateReached (Compile.copyLoopTM dst) ck = false)
      ∧ T ≤ ((State.get s src).length + 1)
              * (5 * (Compile.encodeTape (s.set dst
                  (State.get s dst ++ State.get s src)) ++ res).length + 23) := by
  set u := State.get s src with hu
  set n := u.length with hn
  set d₀ := State.get s dst with hd₀
  -- the loop tape after `n − j` copied bits (dst already holds `d₀`).
  set T : Nat → (List Nat × Nat × List Nat) := fun j =>
    ([], 1 + (Compile.encodeRegs ((s.set dst (d₀ ++ u.take (n - j))).take src)).length + (n - j),
     Compile.encodeTape (s.set dst (d₀ ++ u.take (n - j))) ++ res) with hTdef
  have hu_le : ∀ x ∈ u, x ≤ 1 := by
    rw [hu]
    intro x hx
    have hmem : State.get s src ∈ s := by
      rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
    exact hbit _ hmem x hx
  have hd_le : ∀ x ∈ d₀, x ≤ 1 := by
    rw [hd₀]
    intro x hx
    have hmem : State.get s dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
    exact hbit _ hmem x hx
  have hset_d₀ : s.set dst d₀ = s := by
    rw [hd₀]; exact Compile.set_get_self s dst hdst
  -- per-`j` shared facts.
  have hbit_j : ∀ k, Compile.BitState (s.set dst (d₀ ++ u.take k)) := fun k =>
    Compile.BitState_set s dst _ hbit hdst (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact hd_le x h
      · exact hu_le x (List.mem_of_mem_take h))
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
  -- tape lengths are monotone in the copied prefix.
  have hLen_le : ∀ k, k ≤ n →
      (Compile.encodeTape (s.set dst (d₀ ++ u.take k)) ++ res).length
        ≤ (Compile.encodeTape (s.set dst (d₀ ++ u)) ++ res).length := by
    intro k hk
    have h1 := Compile.encodeTape_set_length s dst (d₀ ++ u.take k) hdst
    have h2 := Compile.encodeTape_set_length s dst (d₀ ++ u) hdst
    have hdlen : d₀.length = (State.get s dst).length := by rw [hd₀]
    have h3 : (d₀ ++ u.take k).length = d₀.length + k := by
      rw [List.length_append, List.length_take]; omega
    have h4 : (d₀ ++ u).length = d₀.length + u.length := by rw [List.length_append]
    simp only [List.length_append]
    omega
  -- ### done contract at `T 0`... i.e. `j = 0`: `T 0` is the FINISHED tape.
  have hdone0 := Compile.copyBody_run_done (s.set dst (d₀ ++ u)) dst src hne
    (by rw [hlen_j]; exact hdst) (by rw [hlen_j]; exact hsrc)
    (Compile.BitState_set s dst (d₀ ++ u) hbit hdst (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact hd_le x h
      · exact hu_le x h)) res hres
  have hget_src_set : State.get (s.set dst (d₀ ++ u)) src = u := by
    rw [Compile.get_set_ne s dst (d₀ ++ u) src hdst (Ne.symm hne), hu]
  have hT0 : T 0 = ([],
      1 + (Compile.encodeRegs ((s.set dst (d₀ ++ u)).take src)).length + n,
      Compile.encodeTape (s.set dst (d₀ ++ u)) ++ res) := by
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
      t ≤ 5 * (Compile.encodeTape (s.set dst (d₀ ++ u)) ++ res).length + 21 := by
    intro j hj
    -- the cursor sits at bit `k₀ := n − j − 1` of `u`.
    have hk₀ : n - (j + 1) < u.length := by rw [← hn]; omega
    have hsplit_j : State.get (s.set dst (d₀ ++ u.take (n - (j + 1)))) src
        = u.take (n - (j + 1)) ++ u[n - (j + 1)] :: u.drop (n - (j + 1) + 1) := by
      rw [Compile.get_set_ne s dst _ src hdst (Ne.symm hne), ← hu,
          ← List.drop_eq_getElem_cons hk₀, List.take_append_drop]
    obtain ⟨t, hrun, htraj, hbnd⟩ := Compile.copyBody_run_iter
      (s.set dst (d₀ ++ u.take (n - (j + 1)))) dst src hne
      (by rw [hlen_j]; exact hdst) (by rw [hlen_j]; exact hsrc)
      (hbit_j _) u[n - (j + 1)]
      (hu_le _ (List.getElem_mem hk₀))
      (u.take (n - (j + 1))) (u.drop (n - (j + 1) + 1)) hsplit_j res hres
    -- rewrite the body's output state to `T j`'s state (appends to `d₀ ++ prefix`).
    have hstate_eq : (s.set dst (d₀ ++ u.take (n - (j + 1)))).set dst
          (State.get (s.set dst (d₀ ++ u.take (n - (j + 1)))) dst ++ [u[n - (j + 1)]])
        = s.set dst (d₀ ++ u.take (n - j)) := by
      rw [Compile.get_set_eq s dst _ hdst, Compile.set_set s dst _ _ hdst, List.append_assoc,
          show u.take (n - (j + 1)) ++ [u[n - (j + 1)]] = u.take (n - (j + 1) + 1) from by
            rw [List.take_add_one, List.getElem?_eq_getElem hk₀]; rfl,
          show n - (j + 1) + 1 = n - j from by omega]
    rw [hstate_eq] at hrun hbnd
    -- align the heads with `T (j+1)` / `T j` (`|u.take k| = k`).
    have hhead_in : 1 + (Compile.encodeRegs ((s.set dst
          (d₀ ++ u.take (n - (j + 1)))).take src)).length + (u.take (n - (j + 1))).length
        = 1 + (Compile.encodeRegs ((s.set dst
          (d₀ ++ u.take (n - (j + 1)))).take src)).length + (n - (j + 1)) := by
      rw [List.length_take]; omega
    have hhead_out : 1 + (Compile.encodeRegs ((s.set dst
          (d₀ ++ u.take (n - j))).take src)).length + (u.take (n - (j + 1))).length + 1
        = 1 + (Compile.encodeRegs ((s.set dst
          (d₀ ++ u.take (n - j))).take src)).length + (n - j) := by
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
      ≤ 5 * (Compile.encodeTape (s.set dst (d₀ ++ u)) ++ res).length + 23 := by
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
    simp only [hTdef, Nat.sub_self, List.take_zero, List.append_nil, hset_d₀, Nat.add_zero]
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
      (5 * (Compile.encodeTape (s.set dst (d₀ ++ u)) ++ res).length + 23) n (by omega) h_iter_bnd

/-- **The cursor-copy loop with `dst` already cleared** (the `opCopy` instance).
Empty-`dst` specialisation of `copyLoopAppend_run` (`[] ++ src = src`), kept so
the two existing callers (`opCopy_run`, eqBit) are unaffected. -/
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
  have h := Compile.copyLoopAppend_run s dst src hne hdst hsrc hbit res hres
  rw [hdst_empty, List.nil_append] at h
  exact h

/-- **`copyEmptyRawTM` run lemma — APPEND form (`dst` may be NONEMPTY).** From
`encodeTape s ++ res` at head `0`, the raw chain `navigate ⨾ cursor loop ⨾ rewind`
APPENDS `src`'s content to `dst`'s existing content (non-destructive on `src`),
rewinds head to `0`, residue unchanged. This is `copyEmpty_run` without the
`dst`-empty hypothesis (the loop is the nonempty-`dst` `copyLoopAppend_run`); the
budget shape is identical (over the OUTPUT tape). The `concat` second-copy
primitive. -/
theorem Compile.copyAppendRaw_run (s : State) (dst src : Var) (hne : dst ≠ src)
    (hdst : dst < s.length) (hsrc : src < s.length)
    (hbit : Compile.BitState s)
    (res : List Nat) (hres : Compile.ValidResidue res) :
    ∃ t,
      runFlatTM t (Compile.copyEmptyRawTM dst src)
          { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] }
        = some { state_idx := Compile.copyEmptyRawTM_exit dst src,
                 tapes := [([], 0, Compile.encodeTape
                   (s.set dst (State.get s dst ++ State.get s src)) ++ res)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.copyEmptyRawTM dst src)
            { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res)] } = some ck →
        ck.state_idx ≠ Compile.copyEmptyRawTM_exit dst src ∧
        haltingStateReached (Compile.copyEmptyRawTM dst src) ck = false)
    ∧ t ≤ ((State.get s src).length + 1)
            * (5 * (Compile.encodeTape
                (s.set dst (State.get s dst ++ State.get s src)) ++ res).length + 23)
          + 3 * (Compile.encodeTape
              (s.set dst (State.get s dst ++ State.get s src)) ++ res).length + 4 := by
  -- ### shared facts about the appended value (`dst₀ ++ src`)
  have hd_le : ∀ x ∈ State.get s dst, x ≤ 1 := by
    intro x hx
    have hmem : State.get s dst ∈ s := by
      rw [State.get, List.getElem?_eq_getElem hdst]; exact List.getElem_mem hdst
    exact hbit _ hmem x hx
  have hu_le : ∀ x ∈ State.get s src, x ≤ 1 := by
    intro x hx
    have hmem : State.get s src ∈ s := by
      rw [State.get, List.getElem?_eq_getElem hsrc]; exact List.getElem_mem hsrc
    exact hbit _ hmem x hx
  have hbit₂ : Compile.BitState (s.set dst (State.get s dst ++ State.get s src)) :=
    Compile.BitState_set s dst _ hbit hdst (by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hd_le x h
      · exact hu_le x h)
  have hs₂_len : (s.set dst (State.get s dst ++ State.get s src)).length = s.length :=
    Compile.length_set s dst _ hdst
  have hsrc₂ : src < (s.set dst (State.get s dst ++ State.get s src)).length := by
    rw [hs₂_len]; exact hsrc
  have hget₂_src : State.get (s.set dst (State.get s dst ++ State.get s src)) src
      = State.get s src :=
    Compile.get_set_ne s dst _ src hdst (Ne.symm hne)
  -- ### phase 1: navigate to `src` (on the input tape; navigate ignores `dst`'s content)
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
  -- ### phase 2: the cursor loop (APPEND form)
  obtain ⟨tl, hloop_run, hloop_traj, hloop_le⟩ :=
    Compile.copyLoopAppend_run s dst src hne hdst hsrc hbit res hres
  -- ### phase 3: the final rewind (`justRewindTM` = scanLeftUntilTM 4 3)
  have hHF2 : 1 + (Compile.encodeRegs
        ((s.set dst (State.get s dst ++ State.get s src)).take src)).length
        + (State.get s src).length + 2
      ≤ (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src))).length := by
    have hdec := congrArg List.length
      (Compile.encodeTape_reg_decomp_at (s.set dst (State.get s dst ++ State.get s src)) src hsrc₂).2
    rw [hget₂_src] at hdec
    simp only [List.length_append, List.length_cons, Compile.shiftReg, List.length_map,
      List.length_nil] at hdec
    omega
  have hTF_lt4 : ∀ x ∈ Compile.encodeTape
      (s.set dst (State.get s dst ++ State.get s src)) ++ res, x < 4 :=
    Compile.encodeTape_append_res_lt_four _ _ hbit₂ hres
  have h0F : 0 < (Compile.encodeTape
      (s.set dst (State.get s dst ++ State.get s src)) ++ res).length := by
    rw [List.length_append, Compile.encodeTape_length]; omega
  have htargetF : (Compile.encodeTape
      (s.set dst (State.get s dst ++ State.get s src)) ++ res).get ⟨0, h0F⟩ = 3 := by
    have hkey : (Compile.encodeTape
        (s.set dst (State.get s dst ++ State.get s src)) ++ res)[0]? = some 3 := by
      rw [Compile.encodeTape]; rfl
    rw [List.get_eq_getElem]
    exact Option.some_inj.mp ((List.getElem?_eq_getElem h0F).symm.trans hkey)
  have hcellsF : ∀ i, 0 < i →
      i ≤ 1 + (Compile.encodeRegs
          ((s.set dst (State.get s dst ++ State.get s src)).take src)).length
        + (State.get s src).length →
      ∃ (h : i < (Compile.encodeTape
          (s.set dst (State.get s dst ++ State.get s src)) ++ res).length),
        (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res).get ⟨i, h⟩ < 4 ∧
        (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res).get ⟨i, h⟩ ≠ 3 := by
    intro i hi0 hile
    have hi1 : i + 1 < (Compile.encodeTape
        (s.set dst (State.get s dst ++ State.get s src))).length := by omega
    have hlt : i < (Compile.encodeTape
        (s.set dst (State.get s dst ++ State.get s src)) ++ res).length := by
      rw [List.length_append]; omega
    refine ⟨hlt, ?_⟩
    have hilt_e : i < (Compile.encodeTape
        (s.set dst (State.get s dst ++ State.get s src))).length := by omega
    have hkey : (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res)[i]?
        = some ((Compile.encodeTape
            (s.set dst (State.get s dst ++ State.get s src))).get ⟨i, hilt_e⟩) := by
      rw [List.getElem?_append_left hilt_e, List.getElem?_eq_getElem hilt_e, List.get_eq_getElem]
    have hgeteq : (Compile.encodeTape
          (s.set dst (State.get s dst ++ State.get s src)) ++ res).get ⟨i, hlt⟩
        = (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src))).get ⟨i, hilt_e⟩ := by
      rw [List.get_eq_getElem]
      exact Option.some_inj.mp ((List.getElem?_eq_getElem hlt).symm.trans hkey)
    rw [hgeteq]
    obtain ⟨hi', hne3⟩ := Compile.encodeTape_interior_ne_endMark _ hbit₂ i hi0 hi1
    exact ⟨Compile.encodeTape_lt_four _ hbit₂ _ (List.get_mem _ _), hne3⟩
  have hrew_run := ScanLeft.scanLeft_run 4 3 []
    (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res) h0F htargetF
    (1 + (Compile.encodeRegs ((s.set dst (State.get s dst ++ State.get s src)).take src)).length
      + (State.get s src).length)
    (by rw [List.length_append]; omega) hcellsF
  have hrew_traj := ScanLeft.scanLeft_no_early_halt 4 3 []
    (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res)
    (1 + (Compile.encodeRegs ((s.set dst (State.get s dst ++ State.get s src)).take src)).length
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
      ([], 1 + (Compile.encodeRegs
          ((s.set dst (State.get s dst ++ State.get s src)).take src)).length
        + (State.get s src).length,
        Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res)
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
    [] (1 + (Compile.encodeRegs ((s.set dst (State.get s dst ++ State.get s src)).take src)).length
      + (State.get s src).length)
    (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res)
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
    [] (1 + (Compile.encodeRegs ((s.set dst (State.get s dst ++ State.get s src)).take src)).length
      + (State.get s src).length)
    (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res)
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
  have hrun := hCrun.1
  simp only [hstate_eq] at hrun
  -- budget bounds.
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
  have hset_len : (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src))).length
      = (Compile.encodeTape s).length + (State.get s src).length := by
    have hbal := Compile.encodeTape_set_length s dst (State.get s dst ++ State.get s src) hdst
    rw [List.length_append] at hbal; omega
  have hin_le : (Compile.encodeTape s ++ res).length
      ≤ (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res).length := by
    rw [List.length_append, List.length_append, hset_len]; omega
  have hrew_le : 1 + (Compile.encodeRegs
        ((s.set dst (State.get s dst ++ State.get s src)).take src)).length
      + (State.get s src).length + 1
      ≤ (Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res).length := by
    rw [List.length_append]; omega
  refine ⟨_, hrun, ?_, ?_⟩
  · intro k hk ck hck
    have hh := hCtraj k hk ck hck
    exact ⟨ClearGadget.ne_of_not_halting (Compile.copyEmptyRawTM_exit_is_halt dst src) hh, hh⟩
  · omega

/-- **The `opCopyAppend` CompiledCmd run lemma** (`dst ≠ src`): the wrapper around
`copyEmptyRawTM` (rewind boundary halt demoted) appends `src` to `dst`'s existing
content, residue UNCHANGED, head rewound to `0`. The `concat` second-copy stage.
Transports `copyAppendRaw_run` through `joinTwoHalts_reaches_kept`. -/
theorem Compile.opCopyAppend_run (s : State) (dst src : Var) (hne : dst ≠ src)
    (hdst : dst < s.length) (hsrc : src < s.length)
    (hbit : Compile.BitState s)
    (res_in : List Nat) (hres_in : Compile.ValidResidue res_in) :
    ∃ t,
      runFlatTM t (Compile.opCopyAppend dst src).M
          (initFlatConfig (Compile.opCopyAppend dst src).M [Compile.encodeTape s ++ res_in])
        = some { state_idx := (Compile.opCopyAppend dst src).exit,
                 tapes := [([], 0, Compile.encodeTape
                   (s.set dst (State.get s dst ++ State.get s src)) ++ res_in)] }
    ∧ (∀ k, k < t → ∀ ck,
        runFlatTM k (Compile.opCopyAppend dst src).M
            (initFlatConfig (Compile.opCopyAppend dst src).M [Compile.encodeTape s ++ res_in])
          = some ck →
        ck.state_idx ≠ (Compile.opCopyAppend dst src).exit ∧
        haltingStateReached (Compile.opCopyAppend dst src).M ck = false)
    ∧ t ≤ ((State.get s src).length + 1)
            * (5 * (Compile.encodeTape
                (s.set dst (State.get s dst ++ State.get s src)) ++ res_in).length + 23)
          + 3 * (Compile.encodeTape
              (s.set dst (State.get s dst ++ State.get s src)) ++ res_in).length + 4 := by
  obtain ⟨t, hraw_run, hraw_traj, hraw_le⟩ :=
    Compile.copyAppendRaw_run s dst src hne hdst hsrc hbit res_in hres_in
  have hstart : (Compile.opCopyAppend dst src).M.start = 0 := by
    show (Compile.joinTwoHalts _ _ _).start = 0
    rw [Compile.joinTwoHalts_start]; exact Compile.copyEmptyRawTM_start dst src
  have hinit : initFlatConfig (Compile.opCopyAppend dst src).M [Compile.encodeTape s ++ res_in]
      = { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] } := by
    simp only [initFlatConfig, hstart, List.map_cons, List.map_nil]
  have hM : (Compile.opCopyAppend dst src).M = Compile.joinTwoHalts (Compile.copyEmptyRawTM dst src)
      (Compile.copyEmptyRawTM_exit dst src) (Compile.copyEmptyRawTM_reject dst src) := rfl
  have hexit : (Compile.opCopyAppend dst src).exit = Compile.copyEmptyRawTM_exit dst src := rfl
  obtain ⟨hjoin_run, hjoin_traj⟩ := Compile.joinTwoHalts_reaches_kept
    (Compile.copyEmptyRawTM dst src) (Compile.copyEmptyRawTM_exit dst src)
    (Compile.copyEmptyRawTM_reject dst src)
    { state_idx := 0, tapes := [([], 0, Compile.encodeTape s ++ res_in)] }
    t ([], 0, Compile.encodeTape (s.set dst (State.get s dst ++ State.get s src)) ++ res_in)
    hraw_run
    (fun k hk ck hck => (hraw_traj k hk ck hck).2)
    (Compile.copyEmptyRawTM_exit_is_halt dst src)
    (Compile.copyEmptyRawTM_reject_is_halt dst src)
  refine ⟨t, ?_, ?_, hraw_le⟩
  · rw [hinit, hM, hexit]; exact hjoin_run
  · rw [hinit, hM, hexit]; exact hjoin_traj

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
  simp [hsym, stepFlatTM, Compile.skipReadTM, Compile.skipReadDelimEntry,
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
    simp [hsym, stepFlatTM, Compile.skipReadTM, Compile.skipReadDelimEntry,
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

