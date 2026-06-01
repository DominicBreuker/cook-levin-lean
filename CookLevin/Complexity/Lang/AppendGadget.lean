import Complexity.Lang.Navigate
import Complexity.Lang.ShiftTape
import Complexity.Lang.ScanPast
import Complexity.Lang.ScanLeft

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
  Complexity.Lang.ScanLeft

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

/-! ### Exit state and halt-vector invariants of `appendAtTM`

`appendAtTM ins dst` is a nest of `composeFlatTM`s whose innermost second
machine is `insertCarryTM ins` (unique halt state `5`). Composition zeroes
each outer `M₁`'s halt bits, so the composite has a single halt state,
shifted by the accumulated `M₁.states`. We package these facts so that
`Compile.opAppendOne`/`opAppendZero` can build a `CompiledCmd`. -/

/-- A halt state `e₂` of the second machine becomes the halt state
`M₁.states + e₂` of `composeFlatTM M₁ M₂ exit` (the composite zeroes
`M₁`'s own halt bits). -/
theorem composeFlatTM_shifted_is_halt (M₁ M₂ : FlatTM) (exit e₂ : Nat)
    (h_is : M₂.halt[e₂]? = some true) :
    (composeFlatTM M₁ M₂ exit).halt[M₁.states + e₂]? = some true := by
  show (composedHalt M₁ M₂)[M₁.states + e₂]? = some true
  unfold composedHalt
  have h_len : (List.replicate M₁.states false).length ≤ M₁.states + e₂ := by
    rw [List.length_replicate]; exact Nat.le_add_right _ _
  rw [List.getElem?_append_right h_len]
  have h_idx :
      M₁.states + e₂ - (List.replicate M₁.states false).length = e₂ := by
    rw [List.length_replicate]; omega
  rw [h_idx]; exact h_is

/-- If `e₂` is the unique halt state of `M₂`, then `M₁.states + e₂` is the
unique halt state of `composeFlatTM M₁ M₂ exit`. -/
theorem composeFlatTM_shifted_halt_unique (M₁ M₂ : FlatTM) (exit e₂ : Nat)
    (h_uniq : ∀ i, M₂.halt[i]? = some true → i = e₂) :
    ∀ i, (composeFlatTM M₁ M₂ exit).halt[i]? = some true →
      i = M₁.states + e₂ := by
  intro i hi
  change (composedHalt M₁ M₂)[i]? = some true at hi
  unfold composedHalt at hi
  by_cases hlt : i < M₁.states
  · exfalso
    have h_lt' : i < (List.replicate M₁.states false).length := by
      rw [List.length_replicate]; exact hlt
    rw [List.getElem?_append_left h_lt'] at hi
    rw [List.getElem?_replicate] at hi
    simp [hlt] at hi
  · rw [Nat.not_lt] at hlt
    have h_ge : (List.replicate M₁.states false).length ≤ i := by
      rw [List.length_replicate]; exact hlt
    rw [List.getElem?_append_right h_ge, List.length_replicate] at hi
    have h_idx : i - M₁.states = e₂ := h_uniq _ hi
    omega

/-- The unique halt (= designated exit) state of `appendAtTM ins dst`:
`8` for `dst = 0` (the `insertCarryTM` halt state `5`, shifted past
`scanRightUntilTM`'s `3` states), plus `3` for each skipped register's
`scanPastDelimTM`. -/
def appendAtTM_exit : Nat → Nat
  | 0     => 8
  | d + 1 => 3 + appendAtTM_exit d

/-- `insertCarryTM ins` halts only at state `5`. -/
theorem insertCarryTM_halt_unique (ins : Nat) :
    ∀ i, (insertCarryTM ins).halt[i]? = some true → i = 5 := by
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [insertCarryTM] at hi ⊢

theorem appendAtTM_exit_lt (ins : Nat) :
    ∀ dst, appendAtTM_exit dst < (appendAtTM ins dst).states
  | 0     => by
      show (8 : Nat) < 9
      decide
  | d + 1 => by
      show 3 + appendAtTM_exit d < 3 + (appendAtTM ins d).states
      exact Nat.add_lt_add_left (appendAtTM_exit_lt ins d) 3

theorem appendAtTM_exit_is_halt (ins : Nat) :
    ∀ dst, (appendAtTM ins dst).halt[appendAtTM_exit dst]? = some true
  | 0     => by
      show (composeFlatTM (scanRightUntilTM 4 0) (insertCarryTM ins) 1).halt[8]?
          = some true
      exact composeFlatTM_shifted_is_halt (scanRightUntilTM 4 0)
        (insertCarryTM ins) 1 5 (by simp [insertCarryTM])
  | d + 1 => by
      show (composeFlatTM (scanPastDelimTM 4 0) (appendAtTM ins d) 1).halt[3 +
          appendAtTM_exit d]? = some true
      exact composeFlatTM_shifted_is_halt (scanPastDelimTM 4 0)
        (appendAtTM ins d) 1 (appendAtTM_exit d) (appendAtTM_exit_is_halt ins d)

theorem appendAtTM_halt_unique (ins : Nat) :
    ∀ dst i, (appendAtTM ins dst).halt[i]? = some true → i = appendAtTM_exit dst
  | 0     => by
      show ∀ i,
        (composeFlatTM (scanRightUntilTM 4 0) (insertCarryTM ins) 1).halt[i]?
          = some true → i = 8
      exact composeFlatTM_shifted_halt_unique (scanRightUntilTM 4 0)
        (insertCarryTM ins) 1 5 (insertCarryTM_halt_unique ins)
  | d + 1 => by
      show ∀ i,
        (composeFlatTM (scanPastDelimTM 4 0) (appendAtTM ins d) 1).halt[i]?
          = some true → i = 3 + appendAtTM_exit d
      exact composeFlatTM_shifted_halt_unique (scanPastDelimTM 4 0)
        (appendAtTM ins d) 1 (appendAtTM_exit d) (appendAtTM_halt_unique ins d)

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

/-- **Explicit step count** for `appendAt_run_steps`. The scanner+inserter
base (register `dst`'s own block) costs `body.length + 1 + 1 + (post.length +
1 + 1)`; each *skipped* register `b` adds `(b.length + 1)` for the scan-past
plus `1` for the `composeFlatTM` bridge step. Independent of `pre` (scanning
and inserting depend only on the lengths to the right of the head). -/
def appendAt_steps : List (List Nat) → List Nat → List Nat → Nat
  | [],      body, post => body.length + 1 + 1 + ((0 :: post).length + 1)
  | b :: s', body, post => (b.length + 1) + 1 + appendAt_steps s' body post

/-- **Append-at-register run lemma, with explicit step count and exit head.**
For the machine `appendAtTM ins dst`, on the encoded tape `pre ++ regBlocks
skipped ++ body ++ 0 :: post` — where `skipped` are the `dst` registers preceding
the target, `body` is the target register's (shifted) contents, and `0 :: post`
is its delimiter plus the rest — the machine halts in **exactly**
`appendAt_steps skipped body post` steps having inserted `ins` just before the
target register's delimiter, leaving `pre ++ regBlocks skipped ++ body ++ ins
:: 0 :: post`. The exit **head** is now explicit too —
`pre.length + (regBlocks skipped).length + body.length + (0 :: post).length`.
⚠ **Verified (2026-05-30): this head is the *last* tape cell** (i.e. *on* the
trailing terminator, since `insertCarryTM_run` ends on the last cell), **not**
"to the left of" it. So the tail rewind must be `ScanLeft.rewindFromEndTM` (step
off the terminator first), not a bare `scanLeftUntilTM`. Only the exit *state*
stays existential here (it is pinned in `appendAt_run_exit`). The step count is
explicit (the ingredient `compileOp_sound`'s tape-length budget needs). -/
theorem appendAt_run_steps (ins : Nat) (h_ins : ins < 4) :
    ∀ (dst : Nat) (pre : List Nat) (skipped : List (List Nat)) (body post : List Nat),
      skipped.length = dst →
      (∀ x ∈ pre, x < 4) →
      (∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) →
      (∀ x ∈ body, x ≠ 0) → (∀ x ∈ body, x < 4) →
      (∀ x ∈ post, x < 4) →
      ∃ (state' : Nat),
        runFlatTM (appendAt_steps skipped body post) (appendAtTM ins dst)
            { state_idx := 0,
              tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] }
          = some { state_idx := state',
                   tapes := [([],
                     pre.length + (regBlocks skipped).length + body.length
                       + (0 :: post).length,
                     pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post)] }
        ∧ haltingStateReached (appendAtTM ins dst)
            { state_idx := state',
              tapes := [([],
                pre.length + (regBlocks skipped).length + body.length
                  + (0 :: post).length,
                pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post)] } = true
  | 0, pre, skipped, body, post, hlen, _, _, h_no_zero, h_body_lt, h_post_lt => by
      cases skipped with
      | cons _ _ => simp at hlen
      | nil =>
        have h := scanInsert_run ins h_ins pre body post h_no_zero h_body_lt h_post_lt
        simp only [regBlocks_nil, List.append_nil, List.length_nil, Nat.add_zero]
        exact ⟨_, h.1, h.2⟩
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
        obtain ⟨state_d, hrun_d, hhalt_d⟩ :=
          appendAt_run_steps ins h_ins d (pre ++ b ++ [0]) s' body post hlen' h_pre'_lt hs'
            h_no_zero h_body_lt h_post_lt
        -- The recursive exit head, made explicit, equals the goal's exit head.
        set head_d : Nat := (pre ++ b ++ [0]).length + (regBlocks s').length + body.length
          + (0 :: post).length with hhead_d
        have hhead_eq : head_d = pre.length + (regBlocks (b :: s')).length + body.length
            + (0 :: post).length := by
          rw [hhead_d, regBlocks_cons]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
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
            runFlatTM (appendAt_steps s' body post) (appendAtTM ins d)
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
        rw [← hhead_eq]
        exact ⟨_, hcomp.1, hcomp.2⟩

/-- The original existential-step form, recovered from `appendAt_run_steps`. -/
theorem appendAt_run (ins : Nat) (h_ins : ins < 4)
    (dst : Nat) (pre : List Nat) (skipped : List (List Nat)) (body post : List Nat)
    (hlen : skipped.length = dst)
    (h_pre : ∀ x ∈ pre, x < 4)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4))
    (h_no_zero : ∀ x ∈ body, x ≠ 0) (h_body_lt : ∀ x ∈ body, x < 4)
    (h_post_lt : ∀ x ∈ post, x < 4) :
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
              pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post)] } = true := by
  obtain ⟨state', hrun, hhalt⟩ :=
    appendAt_run_steps ins h_ins dst pre skipped body post hlen h_pre h_skip
      h_no_zero h_body_lt h_post_lt
  exact ⟨_, _, _, hrun, hhalt⟩

/-- **Exit state and head pinned (Risk C2, step 1b-1).** `appendAt_run_steps`
reaches a *halting* state; since `appendAtTM ins dst`'s halt vector is unique
(`appendAtTM_halt_unique`), that state is exactly `appendAtTM_exit dst`. The exit
**head** is also explicit —
`pre.length + (regBlocks skipped).length + body.length + (0 :: post).length` —
which is the *last* tape cell (on the trailing terminator), so the tail rewind
must be `ScanLeft.rewindFromEndTM` (see `appendAt_rewind_run`). This is the
explicit exit-configuration fact `composeFlatTM_run` needs when bracketing the
gadget with a tail rewind. -/
theorem appendAt_run_exit (ins : Nat) (h_ins : ins < 4)
    (dst : Nat) (pre : List Nat) (skipped : List (List Nat)) (body post : List Nat)
    (hlen : skipped.length = dst)
    (h_pre : ∀ x ∈ pre, x < 4)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4))
    (h_no_zero : ∀ x ∈ body, x ≠ 0) (h_body_lt : ∀ x ∈ body, x < 4)
    (h_post_lt : ∀ x ∈ post, x < 4) :
    runFlatTM (appendAt_steps skipped body post) (appendAtTM ins dst)
        { state_idx := 0,
          tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] }
      = some { state_idx := appendAtTM_exit dst,
               tapes := [([],
                 pre.length + (regBlocks skipped).length + body.length
                   + (0 :: post).length,
                 pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post)] } := by
  obtain ⟨state', hrun, hhalt⟩ :=
    appendAt_run_steps ins h_ins dst pre skipped body post hlen h_pre h_skip
      h_no_zero h_body_lt h_post_lt
  have hmem : (appendAtTM ins dst).halt[state']? = some true := by
    have hg : (appendAtTM ins dst).halt.getD state' false = true := hhalt
    rw [List.getD_eq_getElem?_getD] at hg
    rcases hopt : (appendAtTM ins dst).halt[state']? with _ | b
    · rw [hopt] at hg; simp at hg
    · rw [hopt] at hg; simp only [Option.getD_some] at hg; exact congrArg some hg
  have hexit : state' = appendAtTM_exit dst := appendAtTM_halt_unique ins dst state' hmem
  subst hexit
  exact hrun

/-- **Tape-length step bound.** `appendAt_steps` is at most `2 · (tape length)
+ 3` — linear in the encoded tape, hence below `Compile.overhead` of it. Each
skipped register `b` contributes `b.length + 2` to the steps but `b.length + 1`
to the tape, so the gap grows by at most `1` per register; the base leaves
slack `1`. -/
theorem appendAt_steps_le (skipped : List (List Nat)) (body post : List Nat) :
    appendAt_steps skipped body post
      ≤ 2 * (regBlocks skipped ++ body ++ 0 :: post).length + 3 := by
  induction skipped with
  | nil =>
      show body.length + 1 + 1 + ((0 :: post).length + 1) ≤ _
      simp only [regBlocks_nil, List.nil_append, List.length_append, List.length_cons]
      omega
  | cons b s' ih =>
      show (b.length + 1) + 1 + appendAt_steps s' body post ≤ _
      have hlen : (regBlocks (b :: s') ++ body ++ 0 :: post).length
          = b.length + 1 + (regBlocks s' ++ body ++ 0 :: post).length := by
        rw [regBlocks_cons]
        simp only [List.cons_append, List.append_assoc, List.length_append,
          List.length_cons]
        omega
      rw [hlen]; omega

/-- **No-early-halt trajectory of `appendAtTM` (Risk C2, step 1b-1).**
For `k < appendAt_steps skipped body post`, the machine has not reached a halting
state. Combined with `appendAt_run_exit`, this gives the full `h_traj1` needed by
an outer `composeFlatTM_no_early_halt` when bracketing the gadget with a tail
rewind (`scanLeftUntilTM`).

The proof mirrors `appendAt_run_steps`' recursion: at each level of `dst`,
`composeFlatTM_no_early_halt` combines the navigator's trajectory
(`scan_to_mark_traj` for `dst = 0`, `scanPastDelim_no_early_halt` for `dst > 0`)
with the inner machine's trajectory (IH). -/
theorem appendAt_no_early_halt (ins : Nat) (h_ins : ins < 4) :
    ∀ (dst : Nat) (pre : List Nat) (skipped : List (List Nat)) (body post : List Nat),
      skipped.length = dst →
      (∀ x ∈ pre, x < 4) →
      (∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4)) →
      (∀ x ∈ body, x ≠ 0) → (∀ x ∈ body, x < 4) →
      (∀ x ∈ post, x < 4) →
      ∀ k, k < appendAt_steps skipped body post → ∀ ck,
        runFlatTM k (appendAtTM ins dst)
            { state_idx := 0,
              tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] }
          = some ck →
        haltingStateReached (appendAtTM ins dst) ck = false
  | 0, pre, skipped, body, post, hlen, h_pre, _, h_no_zero, h_body_lt, h_post_lt => by
      cases skipped with
      | cons _ _ => simp at hlen
      | nil =>
        simp only [regBlocks_nil, List.append_nil]
        -- appendAtTM ins 0 = composeFlatTM (scanRightUntilTM 4 0) (insertCarryTM ins) 1
        -- Scanner run: head 0 → delimiter at body.length.
        have h_run1 :
            runFlatTM (body.length + 1) (scanRightUntilTM 4 0)
                { state_idx := 0, tapes := [([], pre.length, pre ++ body ++ 0 :: post)] }
              = some { state_idx := 1,
                       tapes := [([], pre.length + body.length,
                         pre ++ body ++ 0 :: post)] } :=
          scan_to_mark 0 pre body post h_no_zero h_body_lt
        -- Scanner trajectory.
        have h_traj1 := scan_to_mark_traj 0 pre body post h_no_zero h_body_lt
        -- Inserter trajectory.
        have hall : ∀ x ∈ (0 :: post), x < 4 := by
          intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; decide
          · exact h_post_lt x h
        have h_traj2 :
            ∀ k, k < (0 :: post).length + 1 → ∀ ck,
              runFlatTM k (insertCarryTM ins)
                  { state_idx := 0,
                    tapes := [([], pre.length + body.length,
                      pre ++ body ++ 0 :: post)] } = some ck →
              haltingStateReached (insertCarryTM ins) ck = false := by
          have h := insertCarryTM_no_early_halt ins (0 :: post) (pre ++ body) hall
          simpa [List.length_append] using h
        -- Symbol bound at transition point.
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
                List.getElem_append_right
                  (show (pre ++ body).length ≤ pre.length + body.length by simp)]
            simp
          rw [hget] at hv; injection hv with hv'
          have hmax : max (scanRightUntilTM 4 0).sig (insertCarryTM ins).sig = 4 := rfl
          omega
        -- Combine via composeFlatTM_no_early_halt.
        exact composeFlatTM_no_early_halt
          (scanRightUntilTM_valid 4 0 (by decide))
          (insertCarryTM_valid ins h_ins)
          (by decide)
          { state_idx := 0, tapes := [([], pre.length, pre ++ body ++ 0 :: post)] }
          (show (0 : Nat) < 3 from by decide)
          [] (pre.length + body.length) (pre ++ body ++ 0 :: post)
          h_sym_bound h_run1 h_traj1 h_traj2
  | d + 1, pre, skipped, body, post, hlen, h_pre, h_skip, h_no_zero, h_body_lt, h_post_lt => by
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
          · exact h_pre x hp
          · exact hb.2 x hbb
          · subst h0; decide
        -- Canonical tape form.
        have hcanon0 :
            pre ++ regBlocks (b :: s') ++ body ++ 0 :: post
              = pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post) := by
          rw [regBlocks_cons]; simp [List.append_assoc]
        rw [hcanon0]
        -- The scan-past run over `b`.
        have h_run1 := scanPast_block pre b (regBlocks s' ++ body ++ 0 :: post) hb.1 hb.2
        have h_traj1 :=
          scanPastDelim_no_early_halt 4 0 [] (pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post))
            pre.length b.length
            (scan_block_before 0 pre b (regBlocks s' ++ body ++ 0 :: post) hb.1 hb.2)
        -- Recursive trajectory on the inner tape.
        have htape0 :
            pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post)
              = (pre ++ b ++ [0]) ++ regBlocks s' ++ body ++ 0 :: post := by
          simp [List.append_assoc]
        have hhead : pre.length + b.length + 1 = (pre ++ b ++ [0]).length := by
          simp only [List.length_append, List.length_cons, List.length_nil]
        have h_traj2 :
            ∀ k, k < appendAt_steps s' body post → ∀ ck,
              runFlatTM k (appendAtTM ins d)
                  { state_idx := (appendAtTM ins d).start,
                    tapes := [([], pre.length + b.length + 1,
                      pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post))] }
                = some ck →
              haltingStateReached (appendAtTM ins d) ck = false := by
          rw [appendAtTM_start, hhead, htape0]
          exact appendAt_no_early_halt ins h_ins d (pre ++ b ++ [0]) s' body post
            hlen' h_pre'_lt hs' h_no_zero h_body_lt h_post_lt
        -- All tape symbols are `< 4`, so the bridge symbol is in range.
        have hT0_lt : ∀ x ∈ pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post), x < 4 := by
          intro x hx
          simp only [List.mem_append, List.mem_cons] at hx
          rcases hx with (hp | hbb) | h0 | (hrest | hbo) | h0' | hpo
          · exact h_pre x hp
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
        -- Combine via composeFlatTM_no_early_halt.
        exact composeFlatTM_no_early_halt
          (scanPastDelimTM_valid 4 0 (by decide)) (appendAtTM_valid ins h_ins d)
          (by decide)
          { state_idx := 0,
            tapes := [([], pre.length, pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post))] }
          (show (0 : Nat) < 3 from by decide)
          [] (pre.length + b.length + 1)
          (pre ++ b ++ 0 :: (regBlocks s' ++ body ++ 0 :: post))
          h_sym_bound h_run1 h_traj1 h_traj2

/-! ### Bracketing the gadget with a tail rewind (Risk C2, step 1b-2)

The per-fragment **physical contract** needs the gadget to halt with its head
back at the leading sentinel (index `0`), so the next fragment resumes from the
canonical start config. `composeFlatTM` *preserves* the head across the seam, so
the gadget must rewind itself.

⚠ The gadget exits with its head on the **trailing terminator** (the last tape
cell — see `ScanLeft.rewindFromEndTM`'s docstring and the verified finding), not
"just left of" it. So the rewind is `rewindFromEndTM 4 3` (step off the
terminator, then scan left to the leading sentinel), **not** a bare
`scanLeftUntilTM 4 3`. `appendAt_rewind_run` is the resulting bracket: it
composes `appendAt_run_exit` + `appendAt_no_early_halt` (the gadget) with
`rewindFromEndTM_run` (the rewind) via `composeFlatTM_run`. -/

/-- The append gadget bracketed with the tail rewind: run the insert, then
rewind the head from the trailing terminator back to the leading sentinel. -/
def appendAtThenRewindTM (ins dst : Nat) : FlatTM :=
  composeFlatTM (appendAtTM ins dst) (rewindFromEndTM 4 3) (appendAtTM_exit dst)

/-- **Bracketed append run (Risk C2, step 1b-2).** On the encoded tape
`pre ++ regBlocks skipped ++ body ++ 0 :: post`, the bracketed machine
`appendAtThenRewindTM ins dst` inserts `ins` before register `dst`'s delimiter
**and** rewinds the head to index `0`, leaving the head exactly on the leading
sentinel and the tape `pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post`.

The three rewind side-conditions are about the *exit* tape `TP` (the gadget's
output): its cell `0` is the leading sentinel `3` (`h_t0`), every cell is in
range (`h_tp_lt`), and the interior cells `1 … HD-1` are not the sentinel
(`h_interior_ne`). The `Compile`-level consumer discharges these from the
`encodeTape` structure (`encodeRegs` is sentinel-free and `< 4`). -/
theorem appendAt_rewind_run (ins : Nat) (h_ins : ins < 4)
    (dst : Nat) (pre : List Nat) (skipped : List (List Nat)) (body post : List Nat)
    (hlen : skipped.length = dst)
    (h_pre : ∀ x ∈ pre, x < 4)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4))
    (h_no_zero : ∀ x ∈ body, x ≠ 0) (h_body_lt : ∀ x ∈ body, x < 4)
    (h_post_lt : ∀ x ∈ post, x < 4)
    (h_tp_lt : ∀ x ∈ pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post, x < 4)
    (h_t0 : ∀ (h : 0 < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
      (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨0, h⟩ = 3)
    (h_interior_ne : ∀ i, 0 < i →
      i < pre.length + (regBlocks skipped).length + body.length + (0 :: post).length →
      ∃ (h : i < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
        (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨i, h⟩ ≠ 3) :
    runFlatTM (appendAt_steps skipped body post + 1
        + (1 + 1 + (pre.length + (regBlocks skipped).length + body.length
            + (0 :: post).length)))
        (appendAtThenRewindTM ins dst)
        { state_idx := 0,
          tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] }
      = some { state_idx := 3 + (appendAtTM ins dst).states,
               tapes := [([], 0, pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post)] }
    ∧ haltingStateReached (appendAtThenRewindTM ins dst)
        { state_idx := 3 + (appendAtTM ins dst).states,
          tapes := [([], 0, pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post)] } = true := by
  set TP : List Nat := pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post with hTP
  set HD : Nat := pre.length + (regBlocks skipped).length + body.length
    + (0 :: post).length with hHD
  -- The exit tape length and head-position facts.
  have hTPlen : TP.length = pre.length + (regBlocks skipped).length + body.length
      + (0 :: post).length + 1 := by
    rw [hTP]; simp only [List.length_append, List.length_cons]; omega
  have h0 : 0 < TP.length := by rw [hTPlen]; omega
  have hHDpos : 0 < HD := by rw [hHD]; simp only [List.length_cons]; omega
  have hHDlt : HD < TP.length := by rw [hTPlen]; omega
  -- Gadget exit (state + head pinned).
  have h_run1 := appendAt_run_exit ins h_ins dst pre skipped body post hlen h_pre h_skip
    h_no_zero h_body_lt h_post_lt
  have h_traj0 := appendAt_no_early_halt ins h_ins dst pre skipped body post hlen h_pre h_skip
    h_no_zero h_body_lt h_post_lt
  -- `composeFlatTM_run` needs the stronger trajectory `state ≠ exit ∧ not-halting`;
  -- the `≠ exit` part follows because `exit` is itself a halting state.
  have h_traj1 : ∀ k, k < appendAt_steps skipped body post → ∀ ck,
      runFlatTM k (appendAtTM ins dst)
          { state_idx := 0,
            tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] } = some ck →
      ck.state_idx ≠ appendAtTM_exit dst ∧
      haltingStateReached (appendAtTM ins dst) ck = false := by
    intro k hk ck hck
    have hnh := h_traj0 k hk ck hck
    refine ⟨fun hstate => ?_, hnh⟩
    have hhalt_exit : haltingStateReached (appendAtTM ins dst) ck = true := by
      show (appendAtTM ins dst).halt.getD ck.state_idx false = true
      rw [hstate, List.getD_eq_getElem?_getD, appendAtTM_exit_is_halt ins dst]; rfl
    rw [hhalt_exit] at hnh; exact Bool.noConfusion hnh
  -- Bridge symbol bound at the seam (the exit head cell).
  have h_start_lt : TP.get ⟨HD, hHDlt⟩ < 4 := h_tp_lt _ (List.getElem_mem hHDlt)
  have h_sym_bound :
      ∀ v, currentTapeSymbol (([] : List Nat), HD, TP) = some v →
        v < max (appendAtTM ins dst).sig (rewindFromEndTM 4 3).sig := by
    intro v hv
    have hmax : max (appendAtTM ins dst).sig (rewindFromEndTM 4 3).sig = 4 := by
      rw [appendAtTM_sig ins dst, rewindFromEndTM_sig]; rfl
    rw [hmax]
    rw [currentTapeSymbol_in_range hHDlt] at hv
    injection hv with hv'; rw [← hv']; exact h_start_lt
  -- The rewind run on the exit tape.
  have h_cells : ∀ i, 0 < i → i < HD → ∃ (h : i < TP.length),
      TP.get ⟨i, h⟩ < 4 ∧ TP.get ⟨i, h⟩ ≠ 3 := by
    intro i hi hilt
    obtain ⟨h, hne⟩ := h_interior_ne i hi hilt
    exact ⟨h, h_tp_lt _ (List.getElem_mem h), hne⟩
  have h_run2 : runFlatTM (1 + 1 + HD) (rewindFromEndTM 4 3)
      { state_idx := (rewindFromEndTM 4 3).start, tapes := [([], HD, TP)] }
        = some { state_idx := 3, tapes := [([], 0, TP)] } := by
    rw [rewindFromEndTM_start]
    exact rewindFromEndTM_run 4 3 (by decide) [] TP HD h0 (h_t0 h0) hHDpos hHDlt
      h_start_lt h_cells
  have h_halt2 : haltingStateReached (rewindFromEndTM 4 3)
      { state_idx := 3, tapes := [([], 0, TP)] } = true := rfl
  have hcomp := composeFlatTM_run
    (appendAtTM_valid ins h_ins dst) (rewindFromEndTM_valid 4 3 (by decide))
    (appendAtTM_exit_lt ins dst)
    { state_idx := 0,
      tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] }
    (by have h := (appendAtTM_valid ins h_ins dst).1; rwa [appendAtTM_start] at h)
    [] HD TP h_sym_bound h_run1 h_traj1 h_run2 h_halt2
  exact hcomp

/-- **Bracketed append no-early-halt trajectory (Risk C2, step 1b-2).** Before
the bracketed machine completes its `appendAt_steps + 1 + (1 + 1 + HD)` steps it
has not reached a halting state. Together with `appendAt_rewind_run` this is the
gadget-level **physical contract** (run to exit, head `0`, plus trajectory) that
`Compile.compileSeq_compose_physical` consumes when composing fragments. -/
theorem appendAt_rewind_no_early_halt (ins : Nat) (h_ins : ins < 4)
    (dst : Nat) (pre : List Nat) (skipped : List (List Nat)) (body post : List Nat)
    (hlen : skipped.length = dst)
    (h_pre : ∀ x ∈ pre, x < 4)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4))
    (h_no_zero : ∀ x ∈ body, x ≠ 0) (h_body_lt : ∀ x ∈ body, x < 4)
    (h_post_lt : ∀ x ∈ post, x < 4)
    (h_tp_lt : ∀ x ∈ pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post, x < 4)
    (h_t0 : ∀ (h : 0 < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
      (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨0, h⟩ = 3)
    (h_interior_ne : ∀ i, 0 < i →
      i < pre.length + (regBlocks skipped).length + body.length + (0 :: post).length →
      ∃ (h : i < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
        (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨i, h⟩ ≠ 3) :
    ∀ k, k < appendAt_steps skipped body post + 1
        + (1 + 1 + (pre.length + (regBlocks skipped).length + body.length
            + (0 :: post).length)) → ∀ ck,
      runFlatTM k (appendAtThenRewindTM ins dst)
          { state_idx := 0,
            tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] } = some ck →
      haltingStateReached (appendAtThenRewindTM ins dst) ck = false := by
  set TP : List Nat := pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post with hTP
  set HD : Nat := pre.length + (regBlocks skipped).length + body.length
    + (0 :: post).length with hHD
  have hTPlen : TP.length = pre.length + (regBlocks skipped).length + body.length
      + (0 :: post).length + 1 := by
    rw [hTP]; simp only [List.length_append, List.length_cons]; omega
  have h0 : 0 < TP.length := by rw [hTPlen]; omega
  have hHDpos : 0 < HD := by rw [hHD]; simp only [List.length_cons]; omega
  have hHDlt : HD < TP.length := by rw [hTPlen]; omega
  have h_run1 := appendAt_run_exit ins h_ins dst pre skipped body post hlen h_pre h_skip
    h_no_zero h_body_lt h_post_lt
  have h_traj0 := appendAt_no_early_halt ins h_ins dst pre skipped body post hlen h_pre h_skip
    h_no_zero h_body_lt h_post_lt
  have h_traj1 : ∀ k, k < appendAt_steps skipped body post → ∀ ck,
      runFlatTM k (appendAtTM ins dst)
          { state_idx := 0,
            tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] } = some ck →
      ck.state_idx ≠ appendAtTM_exit dst ∧
      haltingStateReached (appendAtTM ins dst) ck = false := by
    intro k hk ck hck
    have hnh := h_traj0 k hk ck hck
    refine ⟨fun hstate => ?_, hnh⟩
    have hhalt_exit : haltingStateReached (appendAtTM ins dst) ck = true := by
      show (appendAtTM ins dst).halt.getD ck.state_idx false = true
      rw [hstate, List.getD_eq_getElem?_getD, appendAtTM_exit_is_halt ins dst]; rfl
    rw [hhalt_exit] at hnh; exact Bool.noConfusion hnh
  have h_start_lt : TP.get ⟨HD, hHDlt⟩ < 4 := h_tp_lt _ (List.getElem_mem hHDlt)
  have h_sym_bound :
      ∀ v, currentTapeSymbol (([] : List Nat), HD, TP) = some v →
        v < max (appendAtTM ins dst).sig (rewindFromEndTM 4 3).sig := by
    intro v hv
    have hmax : max (appendAtTM ins dst).sig (rewindFromEndTM 4 3).sig = 4 := by
      rw [appendAtTM_sig ins dst, rewindFromEndTM_sig]; rfl
    rw [hmax]
    rw [currentTapeSymbol_in_range hHDlt] at hv
    injection hv with hv'; rw [← hv']; exact h_start_lt
  have h_cells : ∀ i, 0 < i → i < HD → ∃ (h : i < TP.length),
      TP.get ⟨i, h⟩ < 4 ∧ TP.get ⟨i, h⟩ ≠ 3 := by
    intro i hi hilt
    obtain ⟨h, hne⟩ := h_interior_ne i hi hilt
    exact ⟨h, h_tp_lt _ (List.getElem_mem h), hne⟩
  -- The rewind trajectory on the exit tape.
  have h_traj2 : ∀ k, k < 1 + 1 + HD → ∀ ck,
      runFlatTM k (rewindFromEndTM 4 3)
          { state_idx := (rewindFromEndTM 4 3).start, tapes := [([], HD, TP)] } = some ck →
      haltingStateReached (rewindFromEndTM 4 3) ck = false := by
    rw [rewindFromEndTM_start]
    exact rewindFromEndTM_no_early_halt 4 3 (by decide) [] TP HD h0 (h_t0 h0) hHDpos hHDlt
      h_start_lt h_cells
  exact composeFlatTM_no_early_halt
    (appendAtTM_valid ins h_ins dst) (rewindFromEndTM_valid 4 3 (by decide))
    (appendAtTM_exit_lt ins dst)
    { state_idx := 0,
      tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] }
    (by have h := (appendAtTM_valid ins h_ins dst).1; rwa [appendAtTM_start] at h)
    [] HD TP h_sym_bound h_run1 h_traj1 h_traj2

/-! ### Residue-tolerant bracketed append (`appendAtThenTwoPhaseRewindTM`)

The single-phase `appendAtThenRewindTM` rewinds correctly only when the head
exits **on** the trailing terminator (no residue after it). In a composed
`Cmd` every fragment after the first runs on `encodeTape s ++ residue`, so the
head exits **inside the residue**, past the real terminator. The two-phase
rewind (`rewindTwoPhaseTM`: scan-left through the residue to the real
terminator, then step off and scan-left to the leading sentinel) handles that.
This bracketed machine is the residue-tolerant analogue used by the
`compileOp` append op. -/
def appendAtThenTwoPhaseRewindTM (ins dst : Nat) : FlatTM :=
  composeFlatTM (appendAtTM ins dst) (rewindTwoPhaseTM 4 3) (appendAtTM_exit dst)

theorem appendAtThenTwoPhaseRewindTM_tapes (ins dst : Nat) :
    (appendAtThenTwoPhaseRewindTM ins dst).tapes = 1 := by
  show (composeFlatTM (appendAtTM ins dst) (rewindTwoPhaseTM 4 3) (appendAtTM_exit dst)).tapes = 1
  rw [composeFlatTM_tapes]; exact appendAtTM_tapes ins dst

theorem appendAtThenTwoPhaseRewindTM_sig (ins dst : Nat) :
    (appendAtThenTwoPhaseRewindTM ins dst).sig = 4 := by
  show (composeFlatTM (appendAtTM ins dst) (rewindTwoPhaseTM 4 3) (appendAtTM_exit dst)).sig = 4
  rw [composeFlatTM_sig, appendAtTM_sig, rewindTwoPhaseTM_sig]; rfl

theorem appendAtThenTwoPhaseRewindTM_states (ins dst : Nat) :
    (appendAtThenTwoPhaseRewindTM ins dst).states
      = (appendAtTM ins dst).states + (rewindTwoPhaseTM 4 3).states := by
  show (composeFlatTM (appendAtTM ins dst) (rewindTwoPhaseTM 4 3) (appendAtTM_exit dst)).states = _
  rw [composeFlatTM_states]

theorem appendAtThenTwoPhaseRewindTM_valid (ins : Nat) (h_ins : ins < 4) (dst : Nat) :
    validFlatTM (appendAtThenTwoPhaseRewindTM ins dst) :=
  composeFlatTM_valid (appendAtTM ins dst) (rewindTwoPhaseTM 4 3) (appendAtTM_exit dst)
    (appendAtTM_valid ins h_ins dst) (rewindTwoPhaseTM_valid 4 3 (by decide))
    (appendAtTM_exit_lt ins dst) (appendAtTM_tapes ins dst) (rewindTwoPhaseTM_tapes 4 3)

/-- The surviving exit (found-state) of the residue-tolerant append bracket. -/
theorem appendAtThenTwoPhaseRewindTM_exit_is_halt (ins dst : Nat) :
    (appendAtThenTwoPhaseRewindTM ins dst).halt[(appendAtTM ins dst).states + 6]? = some true :=
  composeFlatTM_halt_some_intro (appendAtTM ins dst) (rewindTwoPhaseTM 4 3) (appendAtTM_exit dst) 6
    (rewindTwoPhaseTM_halt_six 4 3)

/-- The boundary halt (`appendAtTM.states + 7`) of the append bracket — the one
demoted by `joinTwoHalts`. -/
theorem appendAtThenTwoPhaseRewindTM_halt_seven (ins dst : Nat) :
    (appendAtThenTwoPhaseRewindTM ins dst).halt[(appendAtTM ins dst).states + 7]? = some true :=
  composeFlatTM_halt_some_intro (appendAtTM ins dst) (rewindTwoPhaseTM 4 3) (appendAtTM_exit dst) 7
    (rewindTwoPhaseTM_halt_seven 4 3)

/-- The append bracket halts at exactly two states: the found-state
`appendAtTM.states + 6` (the real exit) and the unreachable boundary-state
`appendAtTM.states + 7` (to be demoted by `joinTwoHalts`). -/
theorem appendAtThenTwoPhaseRewindTM_halt_only (ins dst i : Nat)
    (hi : (appendAtThenTwoPhaseRewindTM ins dst).halt[i]? = some true) :
    i = (appendAtTM ins dst).states + 6 ∨ i = (appendAtTM ins dst).states + 7 := by
  obtain ⟨hge, hj⟩ :=
    composeFlatTM_halt_some_imp (appendAtTM ins dst) (rewindTwoPhaseTM 4 3)
      (appendAtTM_exit dst) i hi
  rcases rewindTwoPhaseTM_halt_only 4 3 _ hj with h | h <;> omega

/-- **Residue-tolerant bracketed append run.** Like `appendAt_rewind_run`, but
the exit tape carries a terminator-free residue after the real terminator (at
position `p`): the head exits at the last cell `HD` (in the residue) and the
two-phase rewind returns it to the leading sentinel `0`. The exit state is
`6 + (appendAtTM ins dst).states` (the two-phase rewind halts at its state `6`).
The conditions on the exit tape `TP = pre ++ regBlocks skipped ++ body ++ ins ::
0 :: post` are: cell `0` is the sentinel `3`, cell `p` is the real terminator
`3`, the interior `1 … p-1` and the residue `p+1 … HD` are both `≠ 3`. -/
theorem appendAt_twoPhaseRewind_run (ins : Nat) (h_ins : ins < 4)
    (dst : Nat) (pre : List Nat) (skipped : List (List Nat)) (body post : List Nat)
    (p : Nat)
    (hlen : skipped.length = dst)
    (h_pre : ∀ x ∈ pre, x < 4)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4))
    (h_no_zero : ∀ x ∈ body, x ≠ 0) (h_body_lt : ∀ x ∈ body, x < 4)
    (h_post_lt : ∀ x ∈ post, x < 4)
    (h_tp_lt : ∀ x ∈ pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post, x < 4)
    (h_p_pos : 0 < p)
    (h_p_le : p ≤ pre.length + (regBlocks skipped).length + body.length + (0 :: post).length)
    (h_t0 : ∀ (h : 0 < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
      (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨0, h⟩ = 3)
    (h_term : ∀ (h : p < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
      (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨p, h⟩ = 3)
    (h_interior_ne : ∀ i, 0 < i → i < p →
      ∃ (h : i < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
        (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨i, h⟩ ≠ 3)
    (h_residue_ne : ∀ i, p < i →
      i ≤ pre.length + (regBlocks skipped).length + body.length + (0 :: post).length →
      ∃ (h : i < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
        (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨i, h⟩ ≠ 3) :
    runFlatTM (appendAt_steps skipped body post + 1
        + (((pre.length + (regBlocks skipped).length + body.length
            + (0 :: post).length) - p + 1) + 1 + (1 + 1 + p)))
        (appendAtThenTwoPhaseRewindTM ins dst)
        { state_idx := 0,
          tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] }
      = some { state_idx := 6 + (appendAtTM ins dst).states,
               tapes := [([], 0, pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post)] }
    ∧ haltingStateReached (appendAtThenTwoPhaseRewindTM ins dst)
        { state_idx := 6 + (appendAtTM ins dst).states,
          tapes := [([], 0, pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post)] } = true := by
  set TP : List Nat := pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post with hTP
  set HD : Nat := pre.length + (regBlocks skipped).length + body.length
    + (0 :: post).length with hHD
  have hTPlen : TP.length = HD + 1 := by
    rw [hTP, hHD]; simp only [List.length_append, List.length_cons]; omega
  have h0 : 0 < TP.length := by rw [hTPlen]; omega
  have hHDlt : HD < TP.length := by rw [hTPlen]; omega
  have hp_lt : p < TP.length := by rw [hTPlen]; omega
  -- Gadget exit (state + head pinned at HD).
  have h_run1 := appendAt_run_exit ins h_ins dst pre skipped body post hlen h_pre h_skip
    h_no_zero h_body_lt h_post_lt
  have h_traj0 := appendAt_no_early_halt ins h_ins dst pre skipped body post hlen h_pre h_skip
    h_no_zero h_body_lt h_post_lt
  have h_traj1 : ∀ k, k < appendAt_steps skipped body post → ∀ ck,
      runFlatTM k (appendAtTM ins dst)
          { state_idx := 0,
            tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] } = some ck →
      ck.state_idx ≠ appendAtTM_exit dst ∧
      haltingStateReached (appendAtTM ins dst) ck = false := by
    intro k hk ck hck
    have hnh := h_traj0 k hk ck hck
    refine ⟨fun hstate => ?_, hnh⟩
    have hhalt_exit : haltingStateReached (appendAtTM ins dst) ck = true := by
      show (appendAtTM ins dst).halt.getD ck.state_idx false = true
      rw [hstate, List.getD_eq_getElem?_getD, appendAtTM_exit_is_halt ins dst]; rfl
    rw [hhalt_exit] at hnh; exact Bool.noConfusion hnh
  -- Bridge symbol bound at the seam (the exit head cell).
  have h_start_lt : TP.get ⟨HD, hHDlt⟩ < 4 := h_tp_lt _ (List.getElem_mem hHDlt)
  have h_sym_bound :
      ∀ v, currentTapeSymbol (([] : List Nat), HD, TP) = some v →
        v < max (appendAtTM ins dst).sig (rewindTwoPhaseTM 4 3).sig := by
    intro v hv
    have hmax : max (appendAtTM ins dst).sig (rewindTwoPhaseTM 4 3).sig = 4 := by
      rw [appendAtTM_sig ins dst, rewindTwoPhaseTM_sig]; rfl
    rw [hmax]
    rw [currentTapeSymbol_in_range hHDlt] at hv
    injection hv with hv'; rw [← hv']; exact h_start_lt
  -- Interior/residue ∃-conditions for `rewindTwoPhase_run` (add the `< 4` part).
  have h_int : ∀ i, 0 < i → i < p → ∃ (h : i < TP.length),
      TP.get ⟨i, h⟩ < 4 ∧ TP.get ⟨i, h⟩ ≠ 3 := by
    intro i hi hilt
    obtain ⟨h, hne⟩ := h_interior_ne i hi hilt
    exact ⟨h, h_tp_lt _ (List.getElem_mem h), hne⟩
  have h_res : ∀ i, p < i → i ≤ HD → ∃ (h : i < TP.length),
      TP.get ⟨i, h⟩ < 4 ∧ TP.get ⟨i, h⟩ ≠ 3 := by
    intro i hi hile
    obtain ⟨h, hne⟩ := h_residue_ne i hi hile
    exact ⟨h, h_tp_lt _ (List.getElem_mem h), hne⟩
  -- The two-phase rewind run on the exit tape.
  have h_run2 : runFlatTM ((HD - p + 1) + 1 + (1 + 1 + p)) (rewindTwoPhaseTM 4 3)
      { state_idx := (rewindTwoPhaseTM 4 3).start, tapes := [([], HD, TP)] }
        = some { state_idx := 6, tapes := [([], 0, TP)] } := by
    rw [rewindTwoPhaseTM_start]
    exact rewindTwoPhase_run 4 3 (by decide) [] TP p HD h0 (h_t0 h0) hp_lt (h_term hp_lt)
      h_p_pos hHDlt (by omega) h_int h_res
  have h_halt2 : haltingStateReached (rewindTwoPhaseTM 4 3)
      { state_idx := 6, tapes := [([], 0, TP)] } = true := rfl
  exact composeFlatTM_run
    (appendAtTM_valid ins h_ins dst) (rewindTwoPhaseTM_valid 4 3 (by decide))
    (appendAtTM_exit_lt ins dst)
    { state_idx := 0,
      tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] }
    (by have h := (appendAtTM_valid ins h_ins dst).1; rwa [appendAtTM_start] at h)
    [] HD TP h_sym_bound h_run1 h_traj1 h_run2 h_halt2

/-- **Residue-tolerant bracketed append no-early-halt trajectory.** The two-phase
analogue of `appendAt_rewind_no_early_halt`: before completing its
`appendAt_steps + 1 + ((HD - p + 1) + 1 + (1 + 1 + p))` steps the bracketed
machine has not reached a halting state. -/
theorem appendAt_twoPhaseRewind_no_early_halt (ins : Nat) (h_ins : ins < 4)
    (dst : Nat) (pre : List Nat) (skipped : List (List Nat)) (body post : List Nat)
    (p : Nat)
    (hlen : skipped.length = dst)
    (h_pre : ∀ x ∈ pre, x < 4)
    (h_skip : ∀ b ∈ skipped, (∀ x ∈ b, x ≠ 0) ∧ (∀ x ∈ b, x < 4))
    (h_no_zero : ∀ x ∈ body, x ≠ 0) (h_body_lt : ∀ x ∈ body, x < 4)
    (h_post_lt : ∀ x ∈ post, x < 4)
    (h_tp_lt : ∀ x ∈ pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post, x < 4)
    (h_p_pos : 0 < p)
    (h_p_le : p ≤ pre.length + (regBlocks skipped).length + body.length + (0 :: post).length)
    (h_t0 : ∀ (h : 0 < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
      (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨0, h⟩ = 3)
    (h_term : ∀ (h : p < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
      (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨p, h⟩ = 3)
    (h_interior_ne : ∀ i, 0 < i → i < p →
      ∃ (h : i < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
        (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨i, h⟩ ≠ 3)
    (h_residue_ne : ∀ i, p < i →
      i ≤ pre.length + (regBlocks skipped).length + body.length + (0 :: post).length →
      ∃ (h : i < (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).length),
        (pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post).get ⟨i, h⟩ ≠ 3) :
    ∀ k, k < appendAt_steps skipped body post + 1
        + (((pre.length + (regBlocks skipped).length + body.length
            + (0 :: post).length) - p + 1) + 1 + (1 + 1 + p)) → ∀ ck,
      runFlatTM k (appendAtThenTwoPhaseRewindTM ins dst)
          { state_idx := 0,
            tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] } = some ck →
      haltingStateReached (appendAtThenTwoPhaseRewindTM ins dst) ck = false := by
  set TP : List Nat := pre ++ regBlocks skipped ++ body ++ ins :: 0 :: post with hTP
  set HD : Nat := pre.length + (regBlocks skipped).length + body.length
    + (0 :: post).length with hHD
  have hTPlen : TP.length = HD + 1 := by
    rw [hTP, hHD]; simp only [List.length_append, List.length_cons]; omega
  have h0 : 0 < TP.length := by rw [hTPlen]; omega
  have hHDlt : HD < TP.length := by rw [hTPlen]; omega
  have hp_lt : p < TP.length := by rw [hTPlen]; omega
  have h_run1 := appendAt_run_exit ins h_ins dst pre skipped body post hlen h_pre h_skip
    h_no_zero h_body_lt h_post_lt
  have h_traj0 := appendAt_no_early_halt ins h_ins dst pre skipped body post hlen h_pre h_skip
    h_no_zero h_body_lt h_post_lt
  have h_traj1 : ∀ k, k < appendAt_steps skipped body post → ∀ ck,
      runFlatTM k (appendAtTM ins dst)
          { state_idx := 0,
            tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] } = some ck →
      ck.state_idx ≠ appendAtTM_exit dst ∧
      haltingStateReached (appendAtTM ins dst) ck = false := by
    intro k hk ck hck
    have hnh := h_traj0 k hk ck hck
    refine ⟨fun hstate => ?_, hnh⟩
    have hhalt_exit : haltingStateReached (appendAtTM ins dst) ck = true := by
      show (appendAtTM ins dst).halt.getD ck.state_idx false = true
      rw [hstate, List.getD_eq_getElem?_getD, appendAtTM_exit_is_halt ins dst]; rfl
    rw [hhalt_exit] at hnh; exact Bool.noConfusion hnh
  have h_start_lt : TP.get ⟨HD, hHDlt⟩ < 4 := h_tp_lt _ (List.getElem_mem hHDlt)
  have h_sym_bound :
      ∀ v, currentTapeSymbol (([] : List Nat), HD, TP) = some v →
        v < max (appendAtTM ins dst).sig (rewindTwoPhaseTM 4 3).sig := by
    intro v hv
    have hmax : max (appendAtTM ins dst).sig (rewindTwoPhaseTM 4 3).sig = 4 := by
      rw [appendAtTM_sig ins dst, rewindTwoPhaseTM_sig]; rfl
    rw [hmax]
    rw [currentTapeSymbol_in_range hHDlt] at hv
    injection hv with hv'; rw [← hv']; exact h_start_lt
  have h_int : ∀ i, 0 < i → i < p → ∃ (h : i < TP.length),
      TP.get ⟨i, h⟩ < 4 ∧ TP.get ⟨i, h⟩ ≠ 3 := by
    intro i hi hilt
    obtain ⟨h, hne⟩ := h_interior_ne i hi hilt
    exact ⟨h, h_tp_lt _ (List.getElem_mem h), hne⟩
  have h_res : ∀ i, p < i → i ≤ HD → ∃ (h : i < TP.length),
      TP.get ⟨i, h⟩ < 4 ∧ TP.get ⟨i, h⟩ ≠ 3 := by
    intro i hi hile
    obtain ⟨h, hne⟩ := h_residue_ne i hi hile
    exact ⟨h, h_tp_lt _ (List.getElem_mem h), hne⟩
  have h_traj2 : ∀ k, k < (HD - p + 1) + 1 + (1 + 1 + p) → ∀ ck,
      runFlatTM k (rewindTwoPhaseTM 4 3)
          { state_idx := (rewindTwoPhaseTM 4 3).start, tapes := [([], HD, TP)] } = some ck →
      haltingStateReached (rewindTwoPhaseTM 4 3) ck = false := by
    rw [rewindTwoPhaseTM_start]
    exact rewindTwoPhase_no_early_halt 4 3 (by decide) [] TP p HD h0 (h_t0 h0) hp_lt
      (h_term hp_lt) h_p_pos hHDlt (by omega) h_int h_res
  exact composeFlatTM_no_early_halt
    (appendAtTM_valid ins h_ins dst) (rewindTwoPhaseTM_valid 4 3 (by decide))
    (appendAtTM_exit_lt ins dst)
    { state_idx := 0,
      tapes := [([], pre.length, pre ++ regBlocks skipped ++ body ++ 0 :: post)] }
    (by have h := (appendAtTM_valid ins h_ins dst).1; rwa [appendAtTM_start] at h)
    [] HD TP h_sym_bound h_run1 h_traj1 h_traj2

end Complexity.Lang.AppendGadget
