import Complexity.Lang.Navigate
import Complexity.Lang.ShiftTape
import Complexity.Lang.ScanPast

set_option autoImplicit false

/-! # Append gadget: scan-to-delimiter then insert (Risk C1 of `ROADMAP.md`)

This is the first end-to-end composition in the `Lang` layer: it glues the
register navigator (`Navigate.scan_to_mark`) ahead of the insert/shift-right
gadget (`ShiftTape.insertCarryTM_run`) via `composeFlatTM`, realizing the
`appendOne` / `appendZero` action on **register 0**.

Concretely, starting on the encoded tape `body ++ 0 :: post` (with `body =
shiftReg r₀` the marker-free shifted contents of register `0`, and `0 ::
post` the delimiter plus the remaining encoded registers and terminator),
the composed machine scans right to register `0`'s delimiter and inserts a
single symbol `ins` just before it, producing `body ++ ins :: 0 :: post`.

For `ins = 2` this is `appendOne 0` (shifted bit `1`); for `ins = 1` it is
`appendZero 0` (shifted bit `0`). General `dst > 0` will chain the scan via
a delimiter-counting navigator (future work); this lemma is the `dst = 0`
base case and the exercise that validates the composition spine. -/

namespace Complexity.Lang.AppendGadget

open TMPrimitives Complexity.Lang.Navigate Complexity.Lang.ShiftTape Complexity.Lang.ScanPast

/-- **Scan-then-insert run (register 0).** From the start state, head at the
left end of the encoded tape `body ++ 0 :: post`, the composed machine
`composeFlatTM (scanRightUntilTM 4 0) (insertCarryTM ins) 1` runs to a halt
having inserted `ins` immediately before register `0`'s terminating
delimiter: the tape becomes `body ++ ins :: 0 :: post`.

`body` is the (marker-free, in-range) shifted contents of register `0`, and
`post` collects the remaining encoded registers plus the end-of-tape
terminator (all symbols `< 4`). -/
theorem scan_then_insert_run (ins : Nat) (h_ins : ins < 4)
    (body post : List Nat)
    (h_no_zero : ∀ x ∈ body, x ≠ 0) (h_body_lt : ∀ x ∈ body, x < 4)
    (h_post_lt : ∀ x ∈ post, x < 4) :
    runFlatTM (body.length + 1 + 1 + ((0 :: post).length + 1))
        (composeFlatTM (scanRightUntilTM 4 0) (insertCarryTM ins) 1)
        { state_idx := 0, tapes := [([], 0, body ++ 0 :: post)] }
      = some { state_idx := 5 + (scanRightUntilTM 4 0).states,
               tapes := [([], body.length + (0 :: post).length,
                          body ++ ins :: 0 :: post)] }
    ∧ haltingStateReached (composeFlatTM (scanRightUntilTM 4 0) (insertCarryTM ins) 1)
        { state_idx := 5 + (scanRightUntilTM 4 0).states,
          tapes := [([], body.length + (0 :: post).length,
                     body ++ ins :: 0 :: post)] } = true := by
  -- The scanner run (clean form: head 0 → delimiter at `body.length`).
  have h_run1 :
      runFlatTM (body.length + 1) (scanRightUntilTM 4 0)
          { state_idx := 0, tapes := [([], 0, body ++ 0 :: post)] }
        = some { state_idx := 1, tapes := [([], body.length, body ++ 0 :: post)] } := by
    have h := scan_to_mark 0 [] body post h_no_zero h_body_lt
    simpa using h
  -- The scanner stays in state 0 (never the exit state 1, never halting)
  -- across all `body.length + 1` steps.
  have h_traj1 :
      ∀ k, k < body.length + 1 → ∀ ck,
        runFlatTM k (scanRightUntilTM 4 0)
            { state_idx := 0, tapes := [([], 0, body ++ 0 :: post)] } = some ck →
        ck.state_idx ≠ 1 ∧
        haltingStateReached (scanRightUntilTM 4 0) ck = false := by
    have h := scan_to_mark_traj 0 [] body post h_no_zero h_body_lt
    simpa using h
  -- The inserter run, from the scanner's exit tape.
  have hall : ∀ x ∈ (0 :: post), x < 4 := by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · subst h; decide
    · exact h_post_lt x h
  have h_run2 :
      runFlatTM ((0 :: post).length + 1) (insertCarryTM ins)
          { state_idx := 0, tapes := [([], body.length, body ++ 0 :: post)] }
        = some { state_idx := 5,
                 tapes := [([], body.length + (0 :: post).length,
                            body ++ ins :: 0 :: post)] } :=
    insertCarryTM_run ins (0 :: post) body hall
  have h_halt2 :
      haltingStateReached (insertCarryTM ins)
          { state_idx := 5,
            tapes := [([], body.length + (0 :: post).length,
                       body ++ ins :: 0 :: post)] } = true := rfl
  -- The symbol under the head at the exit tape is the delimiter `0 < 4`.
  have h_sym_bound :
      ∀ v, currentTapeSymbol (([] : List Nat), body.length, body ++ 0 :: post) = some v →
        v < max (scanRightUntilTM 4 0).sig (insertCarryTM ins).sig := by
    intro v hv
    have hlt : body.length < (body ++ 0 :: post).length := by simp
    rw [currentTapeSymbol_in_range hlt] at hv
    have hget : (body ++ 0 :: post).get ⟨body.length, hlt⟩ = 0 := by
      rw [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl _)]; simp
    rw [hget] at hv
    injection hv with hv'
    have hmax : max (scanRightUntilTM 4 0).sig (insertCarryTM ins).sig = 4 := rfl
    omega
  exact composeFlatTM_run
    (scanRightUntilTM_valid 4 0 (by decide))
    (insertCarryTM_valid ins h_ins)
    (by decide)
    { state_idx := 0, tapes := [([], 0, body ++ 0 :: post)] }
    (show (0 : Nat) < 3 from by decide)
    [] body.length (body ++ 0 :: post)
    h_sym_bound h_run1 h_traj1 h_run2 h_halt2

/-- **Scan-then-insert run, arbitrary prefix.** Generalizes
`scan_then_insert_run` to an arbitrary already-consumed prefix `pre`: from
head `pre.length` on `pre ++ body ++ 0 :: post`, scan over `body` to its
delimiter and insert `ins` just before it. This is the form the `dst`
recursion needs (each peeled register extends `pre`). -/
theorem scanInsert_run (ins : Nat) (h_ins : ins < 4)
    (pre body post : List Nat)
    (h_no_zero : ∀ x ∈ body, x ≠ 0) (h_body_lt : ∀ x ∈ body, x < 4)
    (h_post_lt : ∀ x ∈ post, x < 4) :
    runFlatTM (body.length + 1 + 1 + ((0 :: post).length + 1))
        (composeFlatTM (scanRightUntilTM 4 0) (insertCarryTM ins) 1)
        { state_idx := 0, tapes := [([], pre.length, pre ++ body ++ 0 :: post)] }
      = some { state_idx := 5 + (scanRightUntilTM 4 0).states,
               tapes := [([], pre.length + body.length + (0 :: post).length,
                          pre ++ body ++ ins :: 0 :: post)] }
    ∧ haltingStateReached (composeFlatTM (scanRightUntilTM 4 0) (insertCarryTM ins) 1)
        { state_idx := 5 + (scanRightUntilTM 4 0).states,
          tapes := [([], pre.length + body.length + (0 :: post).length,
                     pre ++ body ++ ins :: 0 :: post)] } = true := by
  have h_run1 :
      runFlatTM (body.length + 1) (scanRightUntilTM 4 0)
          { state_idx := 0, tapes := [([], pre.length, pre ++ body ++ 0 :: post)] }
        = some { state_idx := 1,
                 tapes := [([], pre.length + body.length, pre ++ body ++ 0 :: post)] } :=
    scan_to_mark 0 pre body post h_no_zero h_body_lt
  have h_traj1 := scan_to_mark_traj 0 pre body post h_no_zero h_body_lt
  have hall : ∀ x ∈ (0 :: post), x < 4 := by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · subst h; decide
    · exact h_post_lt x h
  have h_run2 :
      runFlatTM ((0 :: post).length + 1) (insertCarryTM ins)
          { state_idx := 0,
            tapes := [([], pre.length + body.length, pre ++ body ++ 0 :: post)] }
        = some { state_idx := 5,
                 tapes := [([], pre.length + body.length + (0 :: post).length,
                            pre ++ body ++ ins :: 0 :: post)] } := by
    have h := insertCarryTM_run ins (0 :: post) (pre ++ body) hall
    simpa [List.length_append] using h
  have h_halt2 :
      haltingStateReached (insertCarryTM ins)
          { state_idx := 5,
            tapes := [([], pre.length + body.length + (0 :: post).length,
                       pre ++ body ++ ins :: 0 :: post)] } = true := rfl
  have h_sym_bound :
      ∀ v, currentTapeSymbol (([] : List Nat), pre.length + body.length,
              pre ++ body ++ 0 :: post) = some v →
        v < max (scanRightUntilTM 4 0).sig (insertCarryTM ins).sig := by
    intro v hv
    have hlt : pre.length + body.length < (pre ++ body ++ 0 :: post).length := by
      simp only [List.length_append, List.length_cons]; omega
    rw [currentTapeSymbol_in_range hlt] at hv
    have hget : (pre ++ body ++ 0 :: post).get ⟨pre.length + body.length, hlt⟩ = 0 := by
      rw [List.get_eq_getElem,
          List.getElem_append_right (show (pre ++ body).length ≤ pre.length + body.length by simp)]
      simp
    rw [hget] at hv
    injection hv with hv'
    have hmax : max (scanRightUntilTM 4 0).sig (insertCarryTM ins).sig = 4 := rfl
    omega
  exact composeFlatTM_run
    (scanRightUntilTM_valid 4 0 (by decide))
    (insertCarryTM_valid ins h_ins)
    (by decide)
    { state_idx := 0, tapes := [([], pre.length, pre ++ body ++ 0 :: post)] }
    (show (0 : Nat) < 3 from by decide)
    [] (pre.length + body.length) (pre ++ body ++ 0 :: post)
    h_sym_bound h_run1 h_traj1 h_run2 h_halt2

/-- Navigation wrapper: scan over the marker-free block `body` and step one
cell past its delimiter, on the tape `pre ++ body ++ 0 :: post`. -/
theorem scanPast_block (pre body post : List Nat)
    (h_no_zero : ∀ x ∈ body, x ≠ 0) (h_lt : ∀ x ∈ body, x < 4) :
    runFlatTM (body.length + 1) (scanPastDelimTM 4 0)
        { state_idx := 0, tapes := [([], pre.length, pre ++ body ++ 0 :: post)] }
      = some { state_idx := 1,
               tapes := [([], pre.length + body.length + 1, pre ++ body ++ 0 :: post)] } := by
  have hir : pre.length + body.length < (pre ++ body ++ 0 :: post).length := by
    simp only [List.length_append, List.length_cons]; omega
  have hgt : (pre ++ body ++ 0 :: post).get ⟨pre.length + body.length, hir⟩ = 0 := by
    rw [List.get_eq_getElem,
        List.getElem_append_right (show (pre ++ body).length ≤ pre.length + body.length by simp)]
    simp
  exact scanPastDelim_run 4 0 [] (pre ++ body ++ 0 :: post) body.length pre.length
    hir hgt (scan_block_before 0 pre body post h_no_zero h_lt)

/-- Encoded prefix of the registers preceding the target register, each
followed by its `0` delimiter. -/
def regBlocks (skipped : List (List Nat)) : List Nat :=
  (skipped.map (· ++ [0])).flatten

theorem regBlocks_nil : regBlocks [] = [] := rfl

theorem regBlocks_cons (b : List Nat) (s : List (List Nat)) :
    regBlocks (b :: s) = b ++ 0 :: regBlocks s := by
  simp [regBlocks]

/-- The compiled machine for `appendOne`/`appendZero` at register `dst`:
walk past the `dst` preceding delimiters, then scan the target register and
insert `ins` before its delimiter. Recurses on `dst` with the recursive
machine always in the `M₂` slot, so only `scanPastDelimTM`'s (small, fixed)
trajectory is ever required. -/
def appendAtTM (ins : Nat) : Nat → FlatTM
  | 0     => composeFlatTM (scanRightUntilTM 4 0) (insertCarryTM ins) 1
  | d + 1 => composeFlatTM (scanPastDelimTM 4 0) (appendAtTM ins d) 1

theorem appendAtTM_tapes (ins dst : Nat) : (appendAtTM ins dst).tapes = 1 := by
  cases dst <;> rfl

theorem appendAtTM_start (ins dst : Nat) : (appendAtTM ins dst).start = 0 := by
  cases dst <;> rfl

theorem appendAtTM_sig (ins : Nat) : ∀ dst, (appendAtTM ins dst).sig = 4
  | 0     => rfl
  | d + 1 => by
      show (composeFlatTM (scanPastDelimTM 4 0) (appendAtTM ins d) 1).sig = 4
      rw [composeFlatTM_sig, appendAtTM_sig ins d]
      rfl

theorem appendAtTM_valid (ins : Nat) (h_ins : ins < 4) :
    ∀ dst, validFlatTM (appendAtTM ins dst)
  | 0     =>
      composeFlatTM_valid (scanRightUntilTM 4 0) (insertCarryTM ins) 1
        (scanRightUntilTM_valid 4 0 (by decide)) (insertCarryTM_valid ins h_ins)
        (by decide) rfl rfl
  | d + 1 =>
      composeFlatTM_valid (scanPastDelimTM 4 0) (appendAtTM ins d) 1
        (scanPastDelimTM_valid 4 0 (by decide)) (appendAtTM_valid ins h_ins d)
        (by decide) rfl (appendAtTM_tapes ins d)

/-- Every symbol of the encoded register prefix `regBlocks s` is `< 4`,
given each register is. -/
theorem regBlocks_lt (s : List (List Nat)) (h : ∀ b ∈ s, ∀ x ∈ b, x < 4) :
    ∀ x ∈ regBlocks s, x < 4 := by
  induction s with
  | nil => intro x hx; rw [regBlocks_nil] at hx; cases hx
  | cons b s' ih =>
      intro x hx
      rw [regBlocks_cons] at hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hbm | h0 | hrest
      · exact h b (List.mem_cons.mpr (Or.inl rfl)) x hbm
      · subst h0; decide
      · exact ih (fun bb hbb => h bb (List.mem_cons.mpr (Or.inr hbb))) x hrest

/-- **Append-at-register run lemma.** For the machine `appendAtTM ins dst`,
on the encoded tape `pre ++ regBlocks skipped ++ body ++ 0 :: post` — where
`skipped` are the `dst` registers preceding the target, `body` is the target
register's (shifted) contents, and `0 :: post` is its delimiter plus the
rest — the machine halts having inserted `ins` just before the target
register's delimiter, leaving `pre ++ regBlocks skipped ++ body ++ ins :: 0
:: post`. The step count, exit state and final head are existential (their
exact values are immaterial to the tape transformation; a step bound is a
separate concern). -/
theorem appendAt_run (ins : Nat) (h_ins : ins < 4) :
    ∀ (dst : Nat) (pre : List Nat) (skipped : List (List Nat)) (body post : List Nat),
      skipped.length = dst →
      (∀ x ∈ pre, x < 4) →
      (∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) →
      (∀ x ∈ body, x ≠ 0) → (∀ x ∈ body, x < 4) →
      (∀ x ∈ post, x < 4) →
      ∃ (steps state' head' : Nat),
        runFlatTM steps (appendAtTM ins dst)
            { state_idx := 0,
              tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] }
          = some { state_idx := state',
                   tapes := [([], head',
                     pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post)] }
        ∧ haltingStateReached (appendAtTM ins dst)
            { state_idx := state',
              tapes := [([], head',
                pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post)] } = true
  | 0, pre, skipped, body, post, hlen, _, _, h_no_zero, h_body_lt, h_post_lt => by
      cases skipped with
      | cons _ _ => simp at hlen
      | nil =>
        have h := scanInsert_run ins h_ins pre body post h_no_zero h_body_lt h_post_lt
        simp only [regBlocks_nil, List.append_nil]
        exact ⟨_, _, _, h.1, h.2⟩
  | d + 1, pre, skipped, body, post, hlen, h_pre_lt, h_skip, h_no_zero, h_body_lt, h_post_lt => by
      cases skipped with
      | nil => simp at hlen
      | cons b s' =>
        have hlen' : s'.length = d := by simpa using hlen
        have hb := h_skip b (List.mem_cons.mpr (Or.inl rfl))
        have hs' : ∀ bb ∈ s', (∀ x ∈ bb, x ≠ 0) ∧ (∀ x ∈ bb, x < 4) :=
          fun bb hbb => h_skip bb (List.mem_cons.mpr (Or.inr hbb))
        have h_pre'_lt : ∀ x ∈ pre ++ b ++ [0], x < 4 := by
          intro x hx
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with (hp | hbb) | h0
          · exact h_pre_lt x hp
          · exact hb.2 x hbb
          · subst h0; decide
        obtain ⟨steps_d, state_d, head_d, hrun_d, hhalt_d⟩ :=
          appendAt_run ins h_ins d (pre ++ b ++ [0]) s' body post hlen' h_pre'_lt hs'
            h_no_zero h_body_lt h_post_lt
        -- Canonical tape form (peel register `b` to the left).
        have hcanon0 :
            pre ++ regBlocks (b :: s') ++ body ++ 0 :: post
              = pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post) := by
          rw [regBlocks_cons]; simp [List.append_assoc]
        have hcanonf :
            pre ++ regBlocks (b :: s') ++ body ++ ins :: 0 :: post
              = pre ++ b ++ 0 :: (regBlocks s' ++ body ++ ins :: 0 :: post) := by
          rw [regBlocks_cons]; simp [List.append_assoc]
        rw [hcanon0, hcanonf]
        -- The scan-past run over `b`.
        have h_run1 := scanPast_block pre b (regBlocks s' ++ body ++ 0 :: post) hb.1 hb.2
        have h_traj1 :=
          scanPastDelim_no_early_halt 4 0 [] (pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post))
            pre.length b.length
            (scan_block_before 0 pre b (regBlocks s' ++ body ++ 0 :: post) hb.1 hb.2)
        -- The recursive run, massaged onto the scanner's exit tape/head.
        have hhead : pre.length + b.length + 1 = (pre ++ b ++ [0]).length := by
          simp only [List.length_append, List.length_cons, List.length_nil]
        have htape0 :
            pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post)
              = (pre ++ b ++ [0]) ++ regBlocks s' ++ body ++ 0 :: post := by
          simp [List.append_assoc]
        have htapef :
            pre ++ b ++ 0 :: (regBlocks s' ++ body ++ ins :: 0 :: post)
              = (pre ++ b ++ [0]) ++ regBlocks s' ++ body ++ ins :: 0 :: post := by
          simp [List.append_assoc]
        have h_run2 :
            runFlatTM steps_d (appendAtTM ins d)
                { state_idx := (appendAtTM ins d).start,
                  tapes := [([], pre.length + b.length + 1,
                    pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post))] }
              = some { state_idx := state_d,
                       tapes := [([], head_d,
                         pre ++ b ++ 0 :: (regBlocks s' ++ body ++ ins :: 0 :: post))] } := by
          rw [appendAtTM_start, hhead, htape0, htapef]; exact hrun_d
        -- All tape symbols are `< 4`, so the bridge symbol is in range.
        have hT0_lt : ∀ x ∈ pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post), x < 4 := by
          intro x hx
          simp only [List.mem_append, List.mem_cons] at hx
          rcases hx with (hp | hbb) | h0 | (hrest | hbo) | h0' | hpo
          · exact h_pre_lt x hp
          · exact hb.2 x hbb
          · subst h0; decide
          · exact regBlocks_lt s' (fun bb hbb => (hs' bb hbb).2) x hrest
          · exact h_body_lt x hbo
          · subst h0'; decide
          · exact h_post_lt x hpo
        have hmax : max (scanPastDelimTM 4 0).sig (appendAtTM ins d).sig = 4 := by
          rw [appendAtTM_sig ins d]; rfl
        have h_sym_bound :
            ∀ v, currentTapeSymbol (([] : List Nat), pre.length + b.length + 1,
                    pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post)) = some v →
              v < max (scanPastDelimTM 4 0).sig (appendAtTM ins d).sig := by
          intro v hv
          rw [hmax]
          by_cases hlt : pre.length + b.length + 1 <
              (pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post)).length
          · rw [currentTapeSymbol_in_range hlt] at hv
            injection hv with hv'
            rw [List.get_eq_getElem] at hv'
            have hmem : (pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post))[
                pre.length + b.length + 1]'hlt ∈
                  pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post) := List.getElem_mem hlt
            rw [hv'] at hmem
            exact hT0_lt v hmem
          · rw [currentTapeSymbol_out_of_range hlt] at hv; exact absurd hv (by simp)
        have hcomp := composeFlatTM_run
          (scanPastDelimTM_valid 4 0 (by decide)) (appendAtTM_valid ins h_ins d)
          (by decide)
          { state_idx := 0,
            tapes := [([], pre.length, pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post))] }
          (show (0 : Nat) < 3 from by decide)
          [] (pre.length + b.length + 1) (pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post))
          h_sym_bound h_run1 h_traj1 h_run2 hhalt_d
        exact ⟨_, _, _, hcomp.1, hcomp.2⟩

end Complexity.Lang.AppendGadget
