import Complexity.Lang.Navigate
import Complexity.Lang.ShiftTape

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

open TMPrimitives Complexity.Lang.Navigate Complexity.Lang.ShiftTape

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

end Complexity.Lang.AppendGadget
