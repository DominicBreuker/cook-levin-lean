import Complexity.Complexity.TMPrimitives

set_option autoImplicit false

/-! # Register navigation in encoded tapes (Risk C1 of `ROADMAP.md`)

`Compile.encodeTape` lays registers out contiguously, each shifted by
`+1` (so register contents are `≥ 1`) and terminated by the delimiter
`0`. To act on register `dst`, a compiled `Op` must first move the head
to that register's boundary. The reusable navigation atom is
`scan_to_delim`: scanning right for the delimiter `0` from the start of
a register's shifted content lands exactly on that register's
terminating delimiter.

This is the encoding-aware specialization of `scanRightUntilTM`'s
"target found" run lemma (`scanRightUntilTM_run_found`); it is the
building block every `Op` uses to find register `dst` (chained `dst`
times for `dst > 0`). It is independent of the open question about
length-*decreasing* `Op`s (see `ROADMAP.md`, C1), so it is sound to
build now. -/

namespace Complexity.Lang.Navigate

open TMPrimitives

/-- **Navigation atom.** Scanning right for the delimiter `0` from the
start of a register's shifted content lands on that register's
terminating delimiter.

The tape is `pre ++ reg ++ 0 :: post`, head at `pre.length` (the first
cell of `reg`); `reg` is one register's shifted content, so it contains
no `0` and every symbol is `< 4` (the alphabet bound). After
`reg.length + 1` steps the scanner halts in its accept state `1` at the
delimiter, head at `pre.length + reg.length`, tape unchanged. -/
theorem scan_to_delim (pre reg post : List Nat)
    (h_no_zero : ∀ x ∈ reg, x ≠ 0) (h_lt : ∀ x ∈ reg, x < 4) :
    runFlatTM (reg.length + 1) (scanRightUntilTM 4 0)
        { state_idx := 0, tapes := [([], pre.length, pre ++ reg ++ 0 :: post)] }
      = some { state_idx := 1,
               tapes := [([], pre.length + reg.length, pre ++ reg ++ 0 :: post)] } := by
  have h_in_range : pre.length + reg.length < (pre ++ reg ++ 0 :: post).length := by
    simp only [List.length_append, List.length_cons]; omega
  have h_get_target :
      (pre ++ reg ++ 0 :: post).get ⟨pre.length + reg.length, h_in_range⟩ = 0 := by
    rw [List.get_eq_getElem,
        List.getElem_append_right
          (show (pre ++ reg).length ≤ pre.length + reg.length by
            simp only [List.length_append]; omega)]
    simp
  have h_before : ∀ k, k < reg.length →
      ∃ (h : pre.length + k < (pre ++ reg ++ 0 :: post).length),
        (pre ++ reg ++ 0 :: post).get ⟨pre.length + k, h⟩ < 4 ∧
        (pre ++ reg ++ 0 :: post).get ⟨pre.length + k, h⟩ ≠ 0 := by
    intro k hk
    have hh : pre.length + k < (pre ++ reg ++ 0 :: post).length := by
      simp only [List.length_append, List.length_cons]; omega
    have hval : (pre ++ reg ++ 0 :: post).get ⟨pre.length + k, hh⟩ = reg[k]'hk := by
      rw [List.get_eq_getElem,
          List.getElem_append_left
            (show pre.length + k < (pre ++ reg).length by
              simp only [List.length_append]; omega),
          List.getElem_append_right (Nat.le_add_right pre.length k)]
      simp only [Nat.add_sub_cancel_left]
    have hmem : reg[k]'hk ∈ reg := List.getElem_mem hk
    exact ⟨hh, by rw [hval]; exact h_lt _ hmem, by rw [hval]; exact h_no_zero _ hmem⟩
  exact scanRightUntilTM_run_found 4 0 [] (pre ++ reg ++ 0 :: post)
    reg.length pre.length h_in_range h_get_target h_before

end Complexity.Lang.Navigate
