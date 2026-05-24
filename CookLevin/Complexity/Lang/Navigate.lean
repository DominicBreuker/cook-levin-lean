import Complexity.Complexity.TMPrimitives

set_option autoImplicit false

/-! # Register navigation in encoded tapes (Risk C1 of `ROADMAP.md`)

`Compile.encodeTape` lays registers out contiguously, each shifted by
`+1` (so register contents are `≥ 1`) and terminated by the delimiter
`0`, with a single end-of-tape terminator `3` after the last register.
To act on register `dst`, a compiled `Op` must first move the head to
that register's boundary. The reusable navigation atom is `scan_to_mark`:
scanning right for a marker symbol from the start of a marker-free block
lands exactly on that marker. Two specializations:

- `scan_to_delim` (marker `0`) — find a register's terminating delimiter
  (chained `dst` times for register `dst`).
- `scan_to_end` (marker `3`) — find the end-of-tape terminator (used by
  the `dst ≥ length` padding branch, and by length-decreasing ops).

These are encoding-aware specializations of `scanRightUntilTM`'s "target
found" run lemma (`scanRightUntilTM_run_found`). -/

namespace Complexity.Lang.Navigate

open TMPrimitives

/-- Every cell of the marker-free block `body` is in-range (`< 4`) and
distinct from `target`, indexed within the full tape
`pre ++ body ++ target :: post` at offset `pre.length`. Shared by
`scan_to_mark` (its `h_before`) and `scan_to_mark_traj`. -/
theorem scan_block_before (target : Nat) (pre body post : List Nat)
    (h_no_target : ∀ x ∈ body, x ≠ target) (h_lt : ∀ x ∈ body, x < 4) :
    ∀ k, k < body.length →
      ∃ (h : pre.length + k < (pre ++ body ++ target :: post).length),
        (pre ++ body ++ target :: post).get ⟨pre.length + k, h⟩ < 4 ∧
        (pre ++ body ++ target :: post).get ⟨pre.length + k, h⟩ ≠ target := by
  intro k hk
  have hh : pre.length + k < (pre ++ body ++ target :: post).length := by
    simp only [List.length_append, List.length_cons]; omega
  have hval : (pre ++ body ++ target :: post).get ⟨pre.length + k, hh⟩ = body[k]'hk := by
    rw [List.get_eq_getElem,
        List.getElem_append_left
          (show pre.length + k < (pre ++ body).length by
            simp only [List.length_append]; omega),
        List.getElem_append_right (Nat.le_add_right pre.length k)]
    simp only [Nat.add_sub_cancel_left]
  have hmem : body[k]'hk ∈ body := List.getElem_mem hk
  exact ⟨hh, by rw [hval]; exact h_lt _ hmem, by rw [hval]; exact h_no_target _ hmem⟩

/-- **Navigation atom.** Scanning right for `target` from the start of a
`target`-free block lands on the first `target`.

The tape is `pre ++ body ++ target :: post`, head at `pre.length` (the
first cell of `body`); `body` contains no `target` and every symbol is
`< 4` (the alphabet bound). After `body.length + 1` steps the scanner
halts in its accept state `1` at the marker, head at
`pre.length + body.length`, tape unchanged. -/
theorem scan_to_mark (target : Nat) (pre body post : List Nat)
    (h_no_target : ∀ x ∈ body, x ≠ target) (h_lt : ∀ x ∈ body, x < 4) :
    runFlatTM (body.length + 1) (scanRightUntilTM 4 target)
        { state_idx := 0, tapes := [([], pre.length, pre ++ body ++ target :: post)] }
      = some { state_idx := 1,
               tapes := [([], pre.length + body.length, pre ++ body ++ target :: post)] } := by
  have h_in_range :
      pre.length + body.length < (pre ++ body ++ target :: post).length := by
    simp only [List.length_append, List.length_cons]; omega
  have h_get_target :
      (pre ++ body ++ target :: post).get ⟨pre.length + body.length, h_in_range⟩ = target := by
    rw [List.get_eq_getElem,
        List.getElem_append_right
          (show (pre ++ body).length ≤ pre.length + body.length by
            simp only [List.length_append]; omega)]
    simp
  exact scanRightUntilTM_run_found 4 target [] (pre ++ body ++ target :: post)
    body.length pre.length h_in_range h_get_target
    (scan_block_before target pre body post h_no_target h_lt)

/-- **Scan trajectory.** Every intermediate configuration of a right-scan
is in the (non-halting) state `0`, with the head advanced by exactly the
number of steps taken — provided each cell scanned so far is in-range and
not the `target`. After `k` steps (`k ≤` the gap to the marker) the
scanner sits at `{state 0, head+k}` on the unchanged tape.

This is the companion to `scan_to_mark` that discharges
`composeFlatTM_run`'s `h_traj1` obligation: the scanner never reaches its
accept state `1` (nor any halt state) before landing on the marker. -/
theorem scan_traj (sig target : Nat) (left right : List Nat) (head : Nat) :
    ∀ k, (∀ j, j < k → ∃ (h : head + j < right.length),
            right.get ⟨head + j, h⟩ < sig ∧ right.get ⟨head + j, h⟩ ≠ target) →
      runFlatTM k (scanRightUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] }
        = some { state_idx := 0, tapes := [(left, head + k, right)] }
  | 0, _ => by rw [Nat.add_zero]; rfl
  | k + 1, hb => by
      have ih := scan_traj sig target left right head k
        (fun j hj => hb j (Nat.lt_succ_of_lt hj))
      rcases hb k (Nat.lt_succ_self k) with ⟨h_lt, h_sym_lt, h_sym_ne⟩
      have h_step := scanRightUntilTM_step_advance sig target left right (head + k)
        h_lt h_sym_lt h_sym_ne
      have h_nothalt :
          haltingStateReached (scanRightUntilTM sig target)
            { state_idx := 0, tapes := [(left, head + k, right)] } = false := rfl
      have h := runFlatTM_extend_by_step (scanRightUntilTM sig target) k _ _ _
        ih h_nothalt h_step
      rw [show head + (k + 1) = (head + k) + 1 from by omega]
      exact h

/-- The trajectory packaged in exactly the shape `composeFlatTM_run`'s
`h_traj1` precondition wants, for `M₁ = scanRightUntilTM sig target` with
the accept state `1` as the composition exit: across the first `gap + 1`
steps (the run length of `scan_to_mark`) the scanner never reaches the
exit state and never halts. -/
theorem scan_no_early_halt (sig target : Nat) (left right : List Nat)
    (head gap : Nat)
    (hb : ∀ j, j < gap → ∃ (h : head + j < right.length),
            right.get ⟨head + j, h⟩ < sig ∧ right.get ⟨head + j, h⟩ ≠ target) :
    ∀ k, k < gap + 1 → ∀ ck,
      runFlatTM k (scanRightUntilTM sig target)
          { state_idx := 0, tapes := [(left, head, right)] } = some ck →
      ck.state_idx ≠ 1 ∧
      haltingStateReached (scanRightUntilTM sig target) ck = false := by
  intro k hk ck hck
  have hk' : k ≤ gap := Nat.lt_succ_iff.mp hk
  have htraj := scan_traj sig target left right head k
    (fun j hj => hb j (Nat.lt_of_lt_of_le hj hk'))
  rw [htraj] at hck
  obtain rfl : ck = { state_idx := 0, tapes := [(left, head + k, right)] } :=
    (Option.some.inj hck).symm
  exact ⟨Nat.zero_ne_one, rfl⟩

/-- `scan_to_mark`'s trajectory in `composeFlatTM_run`'s `h_traj1` shape:
across all `body.length + 1` steps of the block scan the machine stays out
of its accept state `1` and never halts. This is the precondition for
gluing `scan_to_mark` ahead of a follow-on machine with `composeFlatTM`
(exit state `1`). -/
theorem scan_to_mark_traj (target : Nat) (pre body post : List Nat)
    (h_no_target : ∀ x ∈ body, x ≠ target) (h_lt : ∀ x ∈ body, x < 4) :
    ∀ k, k < body.length + 1 → ∀ ck,
      runFlatTM k (scanRightUntilTM 4 target)
          { state_idx := 0, tapes := [([], pre.length, pre ++ body ++ target :: post)] }
        = some ck →
      ck.state_idx ≠ 1 ∧
      haltingStateReached (scanRightUntilTM 4 target) ck = false :=
  scan_no_early_halt 4 target [] (pre ++ body ++ target :: post) pre.length body.length
    (scan_block_before target pre body post h_no_target h_lt)

/-- Find a register's terminating delimiter `0`: scanning right from the
start of a register's shifted content `reg` (which contains no `0`)
lands on the `0` that terminates it. -/
theorem scan_to_delim (pre reg post : List Nat)
    (h_no_zero : ∀ x ∈ reg, x ≠ 0) (h_lt : ∀ x ∈ reg, x < 4) :
    runFlatTM (reg.length + 1) (scanRightUntilTM 4 0)
        { state_idx := 0, tapes := [([], pre.length, pre ++ reg ++ 0 :: post)] }
      = some { state_idx := 1,
               tapes := [([], pre.length + reg.length, pre ++ reg ++ 0 :: post)] } :=
  scan_to_mark 0 pre reg post h_no_zero h_lt

/-- Find the end-of-tape terminator `3`: scanning right from the start of
the encoded registers `body` (which contain no `3` for a bit-shaped
state) lands on the terminator. Used by the `dst ≥ length` padding
branch. -/
theorem scan_to_end (body post : List Nat)
    (h_no_end : ∀ x ∈ body, x ≠ 3) (h_lt : ∀ x ∈ body, x < 4) :
    runFlatTM (body.length + 1) (scanRightUntilTM 4 3)
        { state_idx := 0, tapes := [([], 0, body ++ 3 :: post)] }
      = some { state_idx := 1,
               tapes := [([], body.length, body ++ 3 :: post)] } := by
  have h := scan_to_mark 3 [] body post h_no_end h_lt
  simpa using h

end Complexity.Lang.Navigate
