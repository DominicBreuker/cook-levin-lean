import Complexity.Lang.Compile.Encoding

set_option autoImplicit false

/-! # Tape-format-check scan gadget (C8-2b, scoping finding F5)

The C8 front instance's `∃ cert` ranges over RAW strings over the machine
alphabet, but the compiled verifier's run lemmas only cover initial tapes of
the exact shape `Compile.encodeTape (encodeIn (x, c))`. `formatCheckTM w`
is the TM-level guard prefixed to the wrapped verifier: it scans the whole
tape and verifies the canonical `w + 1`-register grammar

    `3 ( {1,2}* 0 )^(w+1) 3⟨end-of-tape⟩`

(leading sentinel; each register = a block of shifted bit cells `{1,2}`
closed by its `0` delimiter, per `Compile.encodeRegs`; trailing terminator as
the LAST tape cell), then rewinds the head to `0` and halts in its unique
halt state `w + 6`. On any violation it gets STUCK mid-scan (no matching
transition, non-halting state), so under accept-by-halting a garbage
certificate can never produce an accept — closing the backward correctness
direction of the C8-4 iff.

The separator COUNT is what forces the per-`Q` state count `w + 7`
(`w = xWidth`, the split witness's input register width): a certificate
containing `0` cells would silently parse as EXTRA registers sitting exactly
where the compiled verifier's runtime-padded scratch must be empty, and the
verifier's behaviour on such states is unspecified — so `{1,2}`-only cert
cells must be enforced positionally, by counting delimiters.

States: `0` start (expect the leading sentinel); `1 + i` = phase `i ∈ [0,w]`
(inside register `i`); `w+2` = `F` (expect the trailing terminator); `w+3` =
`E` (end-of-tape check, fires on reading PAST the end); `w+4` = `B` (step
back off the terminator); `w+5` = `S` (rewind scan-left to the sentinel);
`w+6` = `D` (done — the unique halt state). The machine writes nothing.

Both run directions (the F5 obligation):
- `formatCheck_run`/`formatCheck_traj` — a valid `encodeTape s` tape
  (`BitState s`, `s.length = w + 1`) passes in exactly `2·|tape| + 1` steps,
  tape unchanged, head back at `0`, no early halt (the `composeFlatTM_run`
  input shape);
- `formatCheck_stuck` — a tape `(3 :: encodeRegs sx) ++ cert` whose cert
  region violates the grammar (`certOKB cert = false`) never reaches a
  halting configuration, at ANY budget.

`certOKB`/`certOKB_iff` pin the grammar of the adversarial region: the valid
certificates are exactly `Compile.shiftReg creg ++ [0, 3]` for a bit register
`creg` — so format-valid ⇒ decodes (`encodeTape_certSplit` reassembles the
full tape as `encodeTape (sx ++ [creg])`). -/

namespace Complexity.Lang.FormatCheck

/-- The start entry: expect the leading sentinel `3`, step right into
phase `0`. -/
def startEntry : FlatTMTransEntry :=
  ⟨0, [some 3], 1, [none], [.Rmove]⟩

/-- Phase block for register `i` (state `i + 1`): shifted bit cells `1`/`2`
keep scanning right; the `0` delimiter closes the register and advances to
state `i + 2` — the next phase, or `F = w + 2` when `i = w` (same index). -/
def phaseBlock (i : Nat) : List FlatTMTransEntry :=
  [⟨i + 1, [some 1], i + 1, [none], [.Rmove]⟩,
   ⟨i + 1, [some 2], i + 1, [none], [.Rmove]⟩,
   ⟨i + 1, [some 0], i + 2, [none], [.Rmove]⟩]

/-- The tail entries: terminator check (`F`), end-of-tape check (`E`),
step-back (`B`), rewind scan (`S`), and the `S → D` finish on the sentinel. -/
def tailEntries (w : Nat) : List FlatTMTransEntry :=
  [⟨w + 2, [some 3], w + 3, [none], [.Rmove]⟩,
   ⟨w + 3, [none],   w + 4, [none], [.Lmove]⟩,
   ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩,
   ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩,
   ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩,
   ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩,
   ⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩]

/-- The tape-format-check machine for `w + 1` registers (`w` = the split
witness's `xWidth`; register `w` is the certificate register). -/
def formatCheckTM (w : Nat) : FlatTM where
  sig := 4
  tapes := 1
  states := w + 7
  trans := startEntry ::
    ((List.range (w + 1)).flatMap phaseBlock ++ tailEntries w)
  start := 0
  halt := List.replicate (w + 6) false ++ [true]

theorem formatCheckTM_sig (w : Nat) : (formatCheckTM w).sig = 4 := rfl

theorem formatCheckTM_tapes (w : Nat) : (formatCheckTM w).tapes = 1 := rfl

theorem formatCheckTM_states (w : Nat) : (formatCheckTM w).states = w + 7 := rfl

theorem formatCheckTM_start (w : Nat) : (formatCheckTM w).start = 0 := rfl

theorem formatCheckTM_trans (w : Nat) :
    (formatCheckTM w).trans = startEntry ::
      ((List.range (w + 1)).flatMap phaseBlock ++ tailEntries w) := rfl

/-- The halt vector reads `true` exactly at the done state `w + 6`. -/
theorem formatCheck_halting_iff (w : Nat) (cfg : FlatTMConfig) :
    haltingStateReached (formatCheckTM w) cfg = true ↔ cfg.state_idx = w + 6 := by
  show (List.replicate (w + 6) false ++ [true]).getD cfg.state_idx false = true
    ↔ cfg.state_idx = w + 6
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy cfg.state_idx (w + 6) with hlt | heq | hgt
  · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hlt),
        List.getElem?_replicate_of_lt hlt]
    simp; omega
  · rw [heq, List.getElem?_append_right (by rw [List.length_replicate]),
        List.length_replicate, Nat.sub_self]
    simp
  · rw [List.getElem?_eq_none
        (by rw [List.length_append, List.length_replicate]; simpa using hgt)]
    simp; omega

theorem formatCheck_halting_of_ne (w : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx ≠ w + 6) :
    haltingStateReached (formatCheckTM w) cfg = false := by
  cases hh : haltingStateReached (formatCheckTM w) cfg
  · rfl
  · exact absurd ((formatCheck_halting_iff w cfg).mp hh) h

/-- Single-tape entry validity, symbols `< 4`. -/
private theorem entryValid (w : Nat) (src dst : Nat) (sv dv : Option Nat)
    (mv : TMMove) (hsrc : src < w + 7) (hdst : dst < w + 7)
    (hsv : ∀ v, sv = some v → v < 4) (hdv : ∀ v, dv = some v → v < 4) :
    flatTMTransEntryValid (formatCheckTM w) ⟨src, [sv], dst, [dv], [mv]⟩ := by
  refine ⟨hsrc, hdst, rfl, rfl, rfl, ?_, ?_⟩
  · intro x hx
    have hx' : x = sv := by simpa using hx
    rw [hx']
    cases sv with
    | none => trivial
    | some v => exact hsv v rfl
  · intro x hx
    have hx' : x = dv := by simpa using hx
    rw [hx']
    cases dv with
    | none => trivial
    | some v => exact hdv v rfl

/-- Validity: all states `< w + 7`, single tape, all symbols `< 4`. -/
theorem formatCheckTM_valid (w : Nat) : validFlatTM (formatCheckTM w) := by
  refine ⟨by show 0 < w + 7; omega, ?_, ?_⟩
  · show (List.replicate (w + 6) false ++ [true]).length = w + 7
    simp
  · intro e he
    rw [formatCheckTM_trans] at he
    have hsome : ∀ (a : Nat), a < 4 → ∀ v, (some a : Option Nat) = some v → v < 4 :=
      fun a ha v hv => by injection hv with h; omega
    have hnone : ∀ v, (none : Option Nat) = some v → v < 4 := fun v hv => by cases hv
    rcases List.mem_cons.mp he with rfl | he
    · exact entryValid w 0 1 (some 3) none .Rmove (by omega) (by omega)
        (hsome 3 (by omega)) hnone
    rcases List.mem_append.mp he with hph | htl
    · obtain ⟨i, hi, hei⟩ := List.mem_flatMap.mp hph
      have hiw : i < w + 1 := List.mem_range.mp hi
      have hsplit : e = (⟨i + 1, [some 1], i + 1, [none], [.Rmove]⟩ : FlatTMTransEntry)
          ∨ e = ⟨i + 1, [some 2], i + 1, [none], [.Rmove]⟩
          ∨ e = ⟨i + 1, [some 0], i + 2, [none], [.Rmove]⟩ := by
        simpa [phaseBlock] using hei
      rcases hsplit with rfl | rfl | rfl
      · exact entryValid w (i + 1) (i + 1) (some 1) none .Rmove (by omega) (by omega)
          (hsome 1 (by omega)) hnone
      · exact entryValid w (i + 1) (i + 1) (some 2) none .Rmove (by omega) (by omega)
          (hsome 2 (by omega)) hnone
      · exact entryValid w (i + 1) (i + 2) (some 0) none .Rmove (by omega) (by omega)
          (hsome 0 (by omega)) hnone
    · have hsplit : e = (⟨w + 2, [some 3], w + 3, [none], [.Rmove]⟩ : FlatTMTransEntry)
          ∨ e = ⟨w + 3, [none], w + 4, [none], [.Lmove]⟩
          ∨ e = ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩
          ∨ e = ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩
          ∨ e = ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩
          ∨ e = ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩
          ∨ e = ⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩ := by
        simpa [tailEntries] using htl
      rcases hsplit with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact entryValid w (w + 2) (w + 3) (some 3) none .Rmove (by omega) (by omega)
          (hsome 3 (by omega)) hnone
      · exact entryValid w (w + 3) (w + 4) none none .Lmove (by omega) (by omega)
          hnone hnone
      · exact entryValid w (w + 4) (w + 5) (some 3) none .Lmove (by omega) (by omega)
          (hsome 3 (by omega)) hnone
      · exact entryValid w (w + 5) (w + 5) (some 0) none .Lmove (by omega) (by omega)
          (hsome 0 (by omega)) hnone
      · exact entryValid w (w + 5) (w + 5) (some 1) none .Lmove (by omega) (by omega)
          (hsome 1 (by omega)) hnone
      · exact entryValid w (w + 5) (w + 5) (some 2) none .Lmove (by omega) (by omega)
          (hsome 2 (by omega)) hnone
      · exact entryValid w (w + 5) (w + 6) (some 3) none .Nmove (by omega) (by omega)
          (hsome 3 (by omega)) hnone

/-! ## The certificate grammar (list level)

`certOKB` follows the machine's cert-phase scan verbatim: shifted bit cells
`1`/`2`, then the closing delimiter `0` and the trailing terminator `3` as
the LAST two tape cells. -/

/-- Decidable cert-region grammar: `{1,2}* ++ [0, 3]`. -/
def certOKB : List Nat → Bool
  | [0, 3] => true
  | 1 :: rest => certOKB rest
  | 2 :: rest => certOKB rest
  | _ => false

@[simp] theorem certOKB_zero_three : certOKB [0, 3] = true := rfl

theorem certOKB_one (rest : List Nat) : certOKB (1 :: rest) = certOKB rest := by
  cases rest with
  | nil => rfl
  | cons b bs => rfl

theorem certOKB_two (rest : List Nat) : certOKB (2 :: rest) = certOKB rest := by
  cases rest with
  | nil => rfl
  | cons b bs => rfl

/-- Format-valid ⇔ decodes: the valid cert regions are exactly the encodings
`shiftReg creg ++ [0, 3]` of a bit register `creg`. -/
theorem certOKB_iff (cert : List Nat) :
    certOKB cert = true ↔
      ∃ creg : List Nat, (∀ b ∈ creg, b ≤ 1) ∧
        cert = Compile.shiftReg creg ++ [0, 3] := by
  constructor
  · intro h
    induction cert with
    | nil => exact absurd h (by decide)
    | cons v rest ih =>
        match v, rest, h with
        | 0, [3], _ => exact ⟨[], by simp, rfl⟩
        | 1, rest, h =>
            obtain ⟨creg, hbit, rfl⟩ := ih (by rwa [certOKB_one] at h)
            exact ⟨0 :: creg, by simpa using hbit, rfl⟩
        | 2, rest, h =>
            obtain ⟨creg, hbit, rfl⟩ := ih (by rwa [certOKB_two] at h)
            refine ⟨1 :: creg, ?_, rfl⟩
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact Nat.le_refl 1
            · exact hbit b hb
  · rintro ⟨creg, hbit, rfl⟩
    induction creg with
    | nil => rfl
    | cons b bs ih =>
        have hb : b ≤ 1 := hbit b (List.mem_cons_self ..)
        have hbs : ∀ x ∈ bs, x ≤ 1 := fun x hx => hbit x (List.mem_cons_of_mem _ hx)
        have hrec := ih hbs
        show certOKB ((b + 1) :: (Compile.shiftReg bs ++ [0, 3])) = true
        interval_cases b
        · rw [certOKB_one]; exact hrec
        · rw [certOKB_two]; exact hrec

/-- The full-tape reassembly: prefix `3 :: encodeRegs sx` plus a grammar-valid
cert region IS the canonical tape of the split state `sx ++ [creg]`. -/
theorem encodeTape_certSplit (sx : State) (creg : List Nat) :
    Compile.encodeTape (sx ++ [creg])
      = (3 :: Compile.encodeRegs sx) ++ (Compile.shiftReg creg ++ [0, 3]) := by
  show Compile.endMark :: (Compile.encodeRegs (sx ++ [creg]) ++ [Compile.endMark]) = _
  rw [Compile.encodeRegs_append, Compile.encodeRegs_cons, Compile.encodeRegs_nil]
  show (3 : Nat) :: (Compile.encodeRegs sx ++ (Compile.shiftReg creg ++ [0] ++ []) ++ [3]) = _
  simp [List.append_assoc]

/-! ## Step-evaluation infrastructure

The machine writes nothing, so every step is a pure (state, head) move over a
FIXED tape; each step lemma evaluates `find?` over the transition list for
one (state, symbol) pair. `find?` navigation: skip `startEntry` by source
state, locate the right `phaseBlock` inside the `range`-`flatMap` (or skip it
entirely), and fall through to `tailEntries`. -/

private theorem curSym_eq (l t : List Nat) (p : Nat) :
    currentTapeSymbol (l, p, t) = t[p]? := by
  unfold currentTapeSymbol
  split
  · next h => rw [List.getElem?_eq_getElem h]; rfl
  · next h => rw [List.getElem?_eq_none (Nat.le_of_not_lt h)]

private theorem not_matches_state (e : FlatTMTransEntry) (cfg : FlatTMConfig)
    (h : e.src_state ≠ cfg.state_idx) :
    entryMatchesConfig e cfg = false := by
  show (e.src_state == cfg.state_idx &&
    decide (e.src_tape_vals = cfg.tapes.map currentTapeSymbol)) = false
  rw [beq_eq_false_iff_ne.mpr h, Bool.false_and]

private theorem not_matches_sym (e : FlatTMTransEntry) (cfg : FlatTMConfig)
    (h : e.src_tape_vals ≠ cfg.tapes.map currentTapeSymbol) :
    entryMatchesConfig e cfg = false := by
  show (e.src_state == cfg.state_idx &&
    decide (e.src_tape_vals = cfg.tapes.map currentTapeSymbol)) = false
  rw [decide_eq_false h, Bool.and_false]

private theorem matches_of (e : FlatTMTransEntry) (cfg : FlatTMConfig)
    (hs : e.src_state = cfg.state_idx)
    (hv : e.src_tape_vals = cfg.tapes.map currentTapeSymbol) :
    entryMatchesConfig e cfg = true := by
  show (e.src_state == cfg.state_idx &&
    decide (e.src_tape_vals = cfg.tapes.map currentTapeSymbol)) = true
  rw [hs, decide_eq_true hv, Bool.and_true, beq_self_eq_true]

private theorem phaseBlock_src {i : Nat} {e : FlatTMTransEntry}
    (he : e ∈ phaseBlock i) : e.src_state = i + 1 := by
  have hsplit : e = (⟨i + 1, [some 1], i + 1, [none], [.Rmove]⟩ : FlatTMTransEntry)
      ∨ e = ⟨i + 1, [some 2], i + 1, [none], [.Rmove]⟩
      ∨ e = ⟨i + 1, [some 0], i + 2, [none], [.Rmove]⟩ := by
    simpa [phaseBlock] using he
  rcases hsplit with rfl | rfl | rfl <;> rfl

private theorem find?_append_none_right (p : FlatTMTransEntry → Bool)
    (l1 l2 : List FlatTMTransEntry) (h2 : l2.find? p = none) :
    (l1 ++ l2).find? p = l1.find? p := by
  rw [List.find?_append, h2]
  cases l1.find? p <;> rfl

private theorem find?_append_none_left (p : FlatTMTransEntry → Bool)
    (l1 l2 : List FlatTMTransEntry) (h1 : l1.find? p = none) :
    (l1 ++ l2).find? p = l2.find? p := by
  rw [List.find?_append, h1]
  rfl

/-- `find?` over a `range'`-indexed run of phase blocks whose sources all miss
the config's state. -/
private theorem find?_phases_none (cfg : FlatTMConfig) :
    ∀ (n a : Nat), (∀ j, a ≤ j → j < a + n → cfg.state_idx ≠ j + 1) →
      ((List.range' a n).flatMap phaseBlock).find?
        (fun e => entryMatchesConfig e cfg) = none
  | 0, a, _ => rfl
  | n + 1, a, h => by
      show ((phaseBlock a ++ (List.range' (a + 1) n).flatMap phaseBlock).find?
        (fun e => entryMatchesConfig e cfg)) = none
      rw [find?_append_none_left _ _ _ ?_,
          find?_phases_none cfg n (a + 1) (fun j hj hj2 => h j (by omega) (by omega))]
      rw [List.find?_eq_none]
      intro e he
      simp only [Bool.not_eq_true]
      exact not_matches_state e cfg
        (by rw [phaseBlock_src he]; exact fun hh => h a le_rfl (by omega) hh.symm)

/-- `find?` over the phase blocks localizes to block `i` when the config sits
in phase `i`. -/
private theorem find?_phases_eq (cfg : FlatTMConfig) (i : Nat)
    (hstate : cfg.state_idx = i + 1) :
    ∀ (n a : Nat), a ≤ i → i < a + n →
      ((List.range' a n).flatMap phaseBlock).find?
          (fun e => entryMatchesConfig e cfg)
        = (phaseBlock i).find? (fun e => entryMatchesConfig e cfg)
  | 0, a, ha, hin => by omega
  | n + 1, a, ha, hin => by
      show ((phaseBlock a ++ (List.range' (a + 1) n).flatMap phaseBlock).find?
        (fun e => entryMatchesConfig e cfg)) = _
      by_cases hai : a = i
      · subst hai
        rw [find?_append_none_right _ _ _
          (find?_phases_none cfg n (a + 1)
            (fun j hj _ => by rw [hstate]; omega))]
      · rw [find?_append_none_left _ _ _ ?_,
            find?_phases_eq cfg i hstate n (a + 1) (by omega) (by omega)]
        rw [List.find?_eq_none]
        intro e he
        simp only [Bool.not_eq_true]
        exact not_matches_state e cfg
          (by rw [phaseBlock_src he, hstate]; omega)

private theorem find?_tail_none (w : Nat) (cfg : FlatTMConfig)
    (h : cfg.state_idx < w + 2) :
    (tailEntries w).find? (fun e => entryMatchesConfig e cfg) = none := by
  rw [List.find?_eq_none]
  intro e he
  simp only [Bool.not_eq_true]
  have hsplit : e = (⟨w + 2, [some 3], w + 3, [none], [.Rmove]⟩ : FlatTMTransEntry)
      ∨ e = ⟨w + 3, [none], w + 4, [none], [.Lmove]⟩
      ∨ e = ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩
      ∨ e = ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩
      ∨ e = ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩
      ∨ e = ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩
      ∨ e = ⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩ := by
    simpa [tailEntries] using he
  rcases hsplit with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_matches_state _ cfg (by show w + 2 ≠ cfg.state_idx; omega)
  · exact not_matches_state _ cfg (by show w + 3 ≠ cfg.state_idx; omega)
  · exact not_matches_state _ cfg (by show w + 4 ≠ cfg.state_idx; omega)
  · exact not_matches_state _ cfg (by show w + 5 ≠ cfg.state_idx; omega)
  · exact not_matches_state _ cfg (by show w + 5 ≠ cfg.state_idx; omega)
  · exact not_matches_state _ cfg (by show w + 5 ≠ cfg.state_idx; omega)
  · exact not_matches_state _ cfg (by show w + 5 ≠ cfg.state_idx; omega)

/-- Master navigation: at a phase state the whole table's `find?` is the
phase block's. -/
private theorem find?_trans_phase (w i : Nat) (hi : i ≤ w) (cfg : FlatTMConfig)
    (hstate : cfg.state_idx = i + 1) :
    (formatCheckTM w).trans.find? (fun e => entryMatchesConfig e cfg)
      = (phaseBlock i).find? (fun e => entryMatchesConfig e cfg) := by
  rw [formatCheckTM_trans, List.find?_cons,
      not_matches_state startEntry cfg
        (by show (0 : Nat) ≠ cfg.state_idx; rw [hstate]; omega)]
  rw [List.range_eq_range',
      find?_append_none_right _ _ _ (find?_tail_none w cfg (by omega)),
      find?_phases_eq cfg i hstate (w + 1) 0 (by omega) (by omega)]

/-- Master navigation: at a tail state (`≥ w + 2`) the whole table's `find?`
is the tail entries'. -/
private theorem find?_trans_tail (w : Nat) (cfg : FlatTMConfig)
    (hstate : w + 2 ≤ cfg.state_idx) :
    (formatCheckTM w).trans.find? (fun e => entryMatchesConfig e cfg)
      = (tailEntries w).find? (fun e => entryMatchesConfig e cfg) := by
  rw [formatCheckTM_trans, List.find?_cons,
      not_matches_state startEntry cfg
        (by show (0 : Nat) ≠ cfg.state_idx; omega)]
  rw [List.range_eq_range',
      find?_append_none_left _ _ _
        (find?_phases_none cfg (w + 1) 0 (fun j _ hj => by omega))]

/-- `applyTransitionEntry` for a single-tape no-write entry: only the state
and the head move. -/
private theorem applyEntry_single (cfg_state new_state : Nat)
    (l t : List Nat) (p : Nat) (sym : Option Nat) (move : TMMove) :
    applyTransitionEntry
        { state_idx := cfg_state, tapes := [(l, p, t)] }
        { src_state := cfg_state, src_tape_vals := [sym], dst_state := new_state,
          dst_write_vals := [none], move_dirs := [move] }
      = some { state_idx := new_state, tapes := [moveTapeHead (l, p, t) move] } := rfl

private theorem step_eval (w : Nat) (cfg : FlatTMConfig) :
    stepFlatTM (formatCheckTM w) cfg
      = ((formatCheckTM w).trans.find?
          (fun e => entryMatchesConfig e cfg)).bind (applyTransitionEntry cfg) := rfl

private theorem tape_syms (q : Nat) (l t : List Nat) (p : Nat) :
    (FlatTMConfig.mk q [(l, p, t)]).tapes.map currentTapeSymbol = [t[p]?] := by
  show [currentTapeSymbol (l, p, t)] = [t[p]?]
  rw [curSym_eq]

/-! ### The per-(state, symbol) step lemmas -/

/-- Start: on the leading sentinel, enter phase `0` and step right. -/
private theorem step_start (w : Nat) (l t : List Nat)
    (h : t[0]? = some 3) :
    stepFlatTM (formatCheckTM w) ⟨0, [(l, 0, t)]⟩
      = some ⟨1, [(l, 1, t)]⟩ := by
  rw [step_eval, formatCheckTM_trans, List.find?_cons,
      matches_of startEntry _ rfl (by rw [tape_syms, h]; rfl)]
  exact applyEntry_single 0 1 l t 0 (some 3) .Rmove

/-- Phase `i`, shifted bit cell (`1` or `2`): stay, step right. -/
private theorem step_phase_bit (w i : Nat) (hi : i ≤ w) (l t : List Nat)
    (p v : Nat) (hget : t[p]? = some (v + 1)) (hv : v ≤ 1) :
    stepFlatTM (formatCheckTM w) ⟨i + 1, [(l, p, t)]⟩
      = some ⟨i + 1, [(l, p + 1, t)]⟩ := by
  rw [step_eval, find?_trans_phase w i hi _ rfl]
  show ((phaseBlock i).find? (fun e => entryMatchesConfig e _)).bind _ = _
  interval_cases v
  · -- cell `1`
    rw [show phaseBlock i = ⟨i + 1, [some 1], i + 1, [none], [.Rmove]⟩ ::
          [⟨i + 1, [some 2], i + 1, [none], [.Rmove]⟩,
           ⟨i + 1, [some 0], i + 2, [none], [.Rmove]⟩] from rfl,
        List.find?_cons, matches_of _ _ rfl (by rw [tape_syms, hget])]
    exact applyEntry_single (i + 1) (i + 1) l t p (some 1) .Rmove
  · -- cell `2`
    rw [show phaseBlock i = ⟨i + 1, [some 1], i + 1, [none], [.Rmove]⟩ ::
          ⟨i + 1, [some 2], i + 1, [none], [.Rmove]⟩ ::
          [⟨i + 1, [some 0], i + 2, [none], [.Rmove]⟩] from rfl,
        List.find?_cons,
        not_matches_sym _ _ (by rw [tape_syms, hget]; simp),
        List.find?_cons, matches_of _ _ rfl (by rw [tape_syms, hget])]
    exact applyEntry_single (i + 1) (i + 1) l t p (some 2) .Rmove

/-- Phase `i`, register delimiter `0`: close the register, advance to state
`i + 2` (the next phase, or `F` when `i = w`), step right. -/
private theorem step_phase_sep (w i : Nat) (hi : i ≤ w) (l t : List Nat)
    (p : Nat) (hget : t[p]? = some 0) :
    stepFlatTM (formatCheckTM w) ⟨i + 1, [(l, p, t)]⟩
      = some ⟨i + 2, [(l, p + 1, t)]⟩ := by
  rw [step_eval, find?_trans_phase w i hi _ rfl]
  rw [show phaseBlock i = ⟨i + 1, [some 1], i + 1, [none], [.Rmove]⟩ ::
        ⟨i + 1, [some 2], i + 1, [none], [.Rmove]⟩ ::
        [⟨i + 1, [some 0], i + 2, [none], [.Rmove]⟩] from rfl,
      List.find?_cons, not_matches_sym _ _ (by rw [tape_syms, hget]; simp),
      List.find?_cons, not_matches_sym _ _ (by rw [tape_syms, hget]; simp),
      List.find?_cons, matches_of _ _ rfl (by rw [tape_syms, hget])]
  exact applyEntry_single (i + 1) (i + 2) l t p (some 0) .Rmove

/-- Phase `i`, any other read (`3`, out-of-alphabet, or end of tape): STUCK. -/
private theorem step_phase_none (w i : Nat) (hi : i ≤ w) (l t : List Nat)
    (p : Nat) (hget : t[p]? = none ∨ ∃ v, t[p]? = some v ∧ v ≠ 0 ∧ v ≠ 1 ∧ v ≠ 2) :
    stepFlatTM (formatCheckTM w) ⟨i + 1, [(l, p, t)]⟩ = none := by
  rw [step_eval, find?_trans_phase w i hi _ rfl]
  have hne : ∀ (a : Nat), a = 0 ∨ a = 1 ∨ a = 2 →
      ([some a] : List (Option Nat)) ≠ [t[p]?] := by
    intro a ha hh
    have : (some a : Option Nat) = t[p]? := by injection hh
    rcases hget with hnone | ⟨v, hv, hv0, hv1, hv2⟩
    · rw [hnone] at this; cases this
    · rw [hv] at this
      have : a = v := by injection this
      omega
  rw [show phaseBlock i = ⟨i + 1, [some 1], i + 1, [none], [.Rmove]⟩ ::
        ⟨i + 1, [some 2], i + 1, [none], [.Rmove]⟩ ::
        [⟨i + 1, [some 0], i + 2, [none], [.Rmove]⟩] from rfl,
      List.find?_cons, not_matches_sym _ _ (by rw [tape_syms]; exact hne 1 (by omega)),
      List.find?_cons, not_matches_sym _ _ (by rw [tape_syms]; exact hne 2 (by omega)),
      List.find?_cons, not_matches_sym _ _ (by rw [tape_syms]; exact hne 0 (by omega))]
  rfl

/-- `F`, the trailing terminator: step right into the end-check `E`. -/
private theorem step_F (w : Nat) (l t : List Nat) (p : Nat)
    (hget : t[p]? = some 3) :
    stepFlatTM (formatCheckTM w) ⟨w + 2, [(l, p, t)]⟩
      = some ⟨w + 3, [(l, p + 1, t)]⟩ := by
  rw [step_eval, find?_trans_tail w _ (by show w + 2 ≤ w + 2; omega)]
  rw [show tailEntries w = ⟨w + 2, [some 3], w + 3, [none], [.Rmove]⟩ ::
        [⟨w + 3, [none], w + 4, [none], [.Lmove]⟩,
         ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩] from rfl,
      List.find?_cons, matches_of _ _ rfl (by rw [tape_syms, hget])]
  exact applyEntry_single (w + 2) (w + 3) l t p (some 3) .Rmove

/-- `F`, anything but the terminator: STUCK. -/
private theorem step_F_none (w : Nat) (l t : List Nat) (p : Nat)
    (hget : t[p]? ≠ some 3) :
    stepFlatTM (formatCheckTM w) ⟨w + 2, [(l, p, t)]⟩ = none := by
  rw [step_eval, find?_trans_tail w _ (by show w + 2 ≤ w + 2; omega)]
  rw [show tailEntries w = ⟨w + 2, [some 3], w + 3, [none], [.Rmove]⟩ ::
        [⟨w + 3, [none], w + 4, [none], [.Lmove]⟩,
         ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩] from rfl,
      List.find?_cons,
      not_matches_sym _ _ (by
        rw [tape_syms]
        intro hh
        injection hh with h
        exact hget h.symm)]
  have hnone : ∀ e ∈ [(⟨w + 3, [none], w + 4, [none], [.Lmove]⟩ : FlatTMTransEntry),
      ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩,
      ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩,
      ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩,
      ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩,
      ⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩],
      entryMatchesConfig e (⟨w + 2, [(l, p, t)]⟩ : FlatTMConfig) = false := by
    intro e he
    have hsplit : e = (⟨w + 3, [none], w + 4, [none], [.Lmove]⟩ : FlatTMTransEntry)
        ∨ e = ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩
        ∨ e = ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩
        ∨ e = ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩
        ∨ e = ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩
        ∨ e = ⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩ := by
      simpa using he
    rcases hsplit with rfl | rfl | rfl | rfl | rfl | rfl
    · exact not_matches_state _ _ (by show w + 3 ≠ w + 2; omega)
    · exact not_matches_state _ _ (by show w + 4 ≠ w + 2; omega)
    · exact not_matches_state _ _ (by show w + 5 ≠ w + 2; omega)
    · exact not_matches_state _ _ (by show w + 5 ≠ w + 2; omega)
    · exact not_matches_state _ _ (by show w + 5 ≠ w + 2; omega)
    · exact not_matches_state _ _ (by show w + 5 ≠ w + 2; omega)
  rw [List.find?_eq_none.mpr (fun e he => by simp only [Bool.not_eq_true]; exact hnone e he)]
  rfl

/-- `E` on end-of-tape: step back left into `B`. -/
private theorem step_E (w : Nat) (l t : List Nat) (p : Nat)
    (hget : t[p]? = none) :
    stepFlatTM (formatCheckTM w) ⟨w + 3, [(l, p, t)]⟩
      = some ⟨w + 4, [(l, p - 1, t)]⟩ := by
  rw [step_eval, find?_trans_tail w _ (by show w + 2 ≤ w + 3; omega)]
  rw [show tailEntries w = ⟨w + 2, [some 3], w + 3, [none], [.Rmove]⟩ ::
        ⟨w + 3, [none], w + 4, [none], [.Lmove]⟩ ::
        [⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩] from rfl,
      List.find?_cons, not_matches_state _ _ (by show w + 2 ≠ w + 3; omega),
      List.find?_cons, matches_of _ _ rfl (by rw [tape_syms, hget])]
  exact applyEntry_single (w + 3) (w + 4) l t p none .Lmove

/-- `E` on a genuine cell (garbage after the terminator): STUCK. -/
private theorem step_E_none (w : Nat) (l t : List Nat) (p v : Nat)
    (hget : t[p]? = some v) :
    stepFlatTM (formatCheckTM w) ⟨w + 3, [(l, p, t)]⟩ = none := by
  rw [step_eval, find?_trans_tail w _ (by show w + 2 ≤ w + 3; omega)]
  have hnone : ∀ e ∈ tailEntries w,
      entryMatchesConfig e (⟨w + 3, [(l, p, t)]⟩ : FlatTMConfig) = false := by
    intro e he
    have hsplit : e = (⟨w + 2, [some 3], w + 3, [none], [.Rmove]⟩ : FlatTMTransEntry)
        ∨ e = ⟨w + 3, [none], w + 4, [none], [.Lmove]⟩
        ∨ e = ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩
        ∨ e = ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩
        ∨ e = ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩
        ∨ e = ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩
        ∨ e = ⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩ := by
      simpa [tailEntries] using he
    rcases hsplit with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact not_matches_state _ _ (by show w + 2 ≠ w + 3; omega)
    · exact not_matches_sym _ _ (by rw [tape_syms, hget]; intro hh; injection hh with h; cases h)
    · exact not_matches_state _ _ (by show w + 4 ≠ w + 3; omega)
    · exact not_matches_state _ _ (by show w + 5 ≠ w + 3; omega)
    · exact not_matches_state _ _ (by show w + 5 ≠ w + 3; omega)
    · exact not_matches_state _ _ (by show w + 5 ≠ w + 3; omega)
    · exact not_matches_state _ _ (by show w + 5 ≠ w + 3; omega)
  rw [List.find?_eq_none.mpr (fun e he => by simp only [Bool.not_eq_true]; exact hnone e he)]
  rfl

/-- `B` on the trailing terminator: step left into the rewind scan `S`. -/
private theorem step_B (w : Nat) (l t : List Nat) (p : Nat)
    (hget : t[p]? = some 3) :
    stepFlatTM (formatCheckTM w) ⟨w + 4, [(l, p, t)]⟩
      = some ⟨w + 5, [(l, p - 1, t)]⟩ := by
  rw [step_eval, find?_trans_tail w _ (by show w + 2 ≤ w + 4; omega)]
  rw [show tailEntries w = ⟨w + 2, [some 3], w + 3, [none], [.Rmove]⟩ ::
        ⟨w + 3, [none], w + 4, [none], [.Lmove]⟩ ::
        ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩ ::
        [⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩,
         ⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩] from rfl,
      List.find?_cons, not_matches_state _ _ (by show w + 2 ≠ w + 4; omega),
      List.find?_cons, not_matches_state _ _ (by show w + 3 ≠ w + 4; omega),
      List.find?_cons, matches_of _ _ rfl (by rw [tape_syms, hget])]
  exact applyEntry_single (w + 4) (w + 5) l t p (some 3) .Lmove

/-- `S` on an interior cell (`< 3`): keep scanning left. -/
private theorem step_S_scan (w : Nat) (l t : List Nat) (p v : Nat)
    (hget : t[p]? = some v) (hv : v < 3) :
    stepFlatTM (formatCheckTM w) ⟨w + 5, [(l, p, t)]⟩
      = some ⟨w + 5, [(l, p - 1, t)]⟩ := by
  rw [step_eval, find?_trans_tail w _ (by show w + 2 ≤ w + 5; omega)]
  rw [show tailEntries w = ⟨w + 2, [some 3], w + 3, [none], [.Rmove]⟩ ::
        ⟨w + 3, [none], w + 4, [none], [.Lmove]⟩ ::
        ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩ ::
        ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩ ::
        ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩ ::
        ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩ ::
        [⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩] from rfl,
      List.find?_cons, not_matches_state _ _ (by show w + 2 ≠ w + 5; omega),
      List.find?_cons, not_matches_state _ _ (by show w + 3 ≠ w + 5; omega),
      List.find?_cons, not_matches_state _ _ (by show w + 4 ≠ w + 5; omega)]
  interval_cases v
  · rw [List.find?_cons, matches_of _ _ rfl (by rw [tape_syms, hget])]
    exact applyEntry_single (w + 5) (w + 5) l t p (some 0) .Lmove
  · rw [List.find?_cons, not_matches_sym _ _ (by rw [tape_syms, hget]; simp),
        List.find?_cons, matches_of _ _ rfl (by rw [tape_syms, hget])]
    exact applyEntry_single (w + 5) (w + 5) l t p (some 1) .Lmove
  · rw [List.find?_cons, not_matches_sym _ _ (by rw [tape_syms, hget]; simp),
        List.find?_cons, not_matches_sym _ _ (by rw [tape_syms, hget]; simp),
        List.find?_cons, matches_of _ _ rfl (by rw [tape_syms, hget])]
    exact applyEntry_single (w + 5) (w + 5) l t p (some 2) .Lmove

/-- `S` on the leading sentinel: DONE. -/
private theorem step_S_found (w : Nat) (l t : List Nat) (p : Nat)
    (hget : t[p]? = some 3) :
    stepFlatTM (formatCheckTM w) ⟨w + 5, [(l, p, t)]⟩
      = some ⟨w + 6, [(l, p, t)]⟩ := by
  rw [step_eval, find?_trans_tail w _ (by show w + 2 ≤ w + 5; omega)]
  rw [show tailEntries w = ⟨w + 2, [some 3], w + 3, [none], [.Rmove]⟩ ::
        ⟨w + 3, [none], w + 4, [none], [.Lmove]⟩ ::
        ⟨w + 4, [some 3], w + 5, [none], [.Lmove]⟩ ::
        ⟨w + 5, [some 0], w + 5, [none], [.Lmove]⟩ ::
        ⟨w + 5, [some 1], w + 5, [none], [.Lmove]⟩ ::
        ⟨w + 5, [some 2], w + 5, [none], [.Lmove]⟩ ::
        [⟨w + 5, [some 3], w + 6, [none], [.Nmove]⟩] from rfl,
      List.find?_cons, not_matches_state _ _ (by show w + 2 ≠ w + 5; omega),
      List.find?_cons, not_matches_state _ _ (by show w + 3 ≠ w + 5; omega),
      List.find?_cons, not_matches_state _ _ (by show w + 4 ≠ w + 5; omega),
      List.find?_cons, not_matches_sym _ _ (by rw [tape_syms, hget]; simp),
      List.find?_cons, not_matches_sym _ _ (by rw [tape_syms, hget]; simp),
      List.find?_cons, not_matches_sym _ _ (by rw [tape_syms, hget]; simp),
      List.find?_cons, matches_of _ _ rfl (by rw [tape_syms, hget])]
  exact applyEntry_single (w + 5) (w + 6) l t p (some 3) .Nmove

/-! ## The `Seg` framework — exact runs with a done-state-free trajectory -/

/-- Exact segment: the run reaches `c1` at step `n` and never sits on the
done state `w + 6` strictly before. Since `w + 6` is the machine's ONLY halt
state, this is simultaneously the run lemma and the no-early-halt
trajectory, and segments compose additively. -/
def Seg (w n : Nat) (c0 c1 : FlatTMConfig) : Prop :=
  runFlatTM n (formatCheckTM w) c0 = some c1 ∧
  ∀ k, k < n → ∀ ck, runFlatTM k (formatCheckTM w) c0 = some ck →
    ck.state_idx ≠ w + 6

theorem Seg.zero (w : Nat) (c : FlatTMConfig) : Seg w 0 c c :=
  ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

theorem Seg.single (w : Nat) {c0 c1 : FlatTMConfig}
    (hstep : stepFlatTM (formatCheckTM w) c0 = some c1)
    (hne : c0.state_idx ≠ w + 6) : Seg w 1 c0 c1 := by
  constructor
  · show (if haltingStateReached (formatCheckTM w) c0 = true then some c0
        else match stepFlatTM (formatCheckTM w) c0 with
          | none => some c0
          | some c => runFlatTM 0 (formatCheckTM w) c) = some c1
    rw [if_neg (by rw [formatCheck_halting_of_ne w c0 hne]; simp), hstep]
    rfl
  · intro k hk ck hck
    have hk0 : k = 0 := by omega
    subst hk0
    obtain rfl : c0 = ck := Option.some.inj hck
    exact hne

theorem Seg.comp {w n1 n2 : Nat} {c0 c1 c2 : FlatTMConfig}
    (h1 : Seg w n1 c0 c1) (h2 : Seg w n2 c1 c2) : Seg w (n1 + n2) c0 c2 := by
  constructor
  · rw [runFlatTM_compose (formatCheckTM w) n1 n2 c0 c1 h1.1]
    exact h2.1
  · intro k hk ck hck
    rcases Nat.lt_or_ge k n1 with hlt | hge
    · exact h1.2 k hlt ck hck
    · have heq : runFlatTM k (formatCheckTM w) c0
          = runFlatTM (k - n1) (formatCheckTM w) c1 := by
        conv_lhs => rw [show k = n1 + (k - n1) from by omega]
        exact runFlatTM_compose (formatCheckTM w) n1 (k - n1) c0 c1 h1.1
      rw [heq] at hck
      exact h2.2 (k - n1) (by omega) ck hck

/-! ### Drop-decomposition helpers -/

private theorem drop_head (t : List Nat) (p v : Nat) (rest : List Nat)
    (h : t.drop p = v :: rest) : t[p]? = some v ∧ t.drop (p + 1) = rest := by
  constructor
  · have h0 : (t.drop p)[0]? = some v := by rw [h]; rfl
    rwa [List.getElem?_drop, Nat.add_zero] at h0
  · have h1 : (t.drop p).drop 1 = rest := by rw [h]; rfl
    rwa [List.drop_drop] at h1

private theorem drop_none (t : List Nat) (p : Nat)
    (h : t.drop p = []) : t[p]? = none := by
  rw [List.getElem?_eq_none]
  exact (List.drop_eq_nil_iff).mp h

private theorem drop_append (t : List Nat) (p : Nat) (A B : List Nat)
    (h : t.drop p = A ++ B) : t.drop (p + A.length) = B := by
  have h1 : (t.drop p).drop A.length = B := by
    rw [h, List.drop_left]
  rwa [List.drop_drop] at h1

/-! ### The forward segments -/

/-- Scan one register's shifted bit block: phase unchanged, head advances. -/
theorem scanBits_seg (w i : Nat) (hi : i ≤ w) :
    ∀ (reg : List Nat) (p : Nat) (l t rest : List Nat),
      (∀ b ∈ reg, b ≤ 1) →
      t.drop p = Compile.shiftReg reg ++ rest →
      Seg w reg.length ⟨i + 1, [(l, p, t)]⟩ ⟨i + 1, [(l, p + reg.length, t)]⟩
  | [], p, l, t, rest, _, _ => by simpa using Seg.zero w _
  | b :: bs, p, l, t, rest, hbit, hdrop => by
      have hb : b ≤ 1 := hbit b (List.mem_cons_self ..)
      have hdrop' : t.drop p = (b + 1) :: (Compile.shiftReg bs ++ rest) := by
        rw [hdrop]
        show (List.map (· + 1) (b :: bs) ++ rest) = _
        rw [List.map_cons]
        rfl
      obtain ⟨hget, hdrop1⟩ := drop_head t p (b + 1) _ hdrop'
      have h1 : Seg w 1 ⟨i + 1, [(l, p, t)]⟩ ⟨i + 1, [(l, p + 1, t)]⟩ :=
        Seg.single w (step_phase_bit w i hi l t p b hget hb)
          (by show i + 1 ≠ w + 6; omega)
      have h2 := scanBits_seg w i hi bs (p + 1) l t rest
        (fun x hx => hbit x (List.mem_cons_of_mem _ hx)) hdrop1
      have hcomp := h1.comp h2
      rw [show 1 + bs.length = (b :: bs).length from by
            simp only [List.length_cons]; omega,
          show p + 1 + bs.length = p + (b :: bs).length from by
            simp only [List.length_cons]; omega] at hcomp
      exact hcomp

/-- Scan a run of complete registers (each block closed by its `0`): from
phase `i` to phase `i + s'.length` (state index `i + s'.length + 1`, which is
`F = w + 2` when the run ends the full `w + 1`-register scan). -/
theorem scanRegs_seg (w : Nat) :
    ∀ (s' : State) (i p : Nat) (l t rest : List Nat),
      i + s'.length ≤ w + 1 → Compile.BitState s' →
      t.drop p = Compile.encodeRegs s' ++ rest →
      Seg w (Compile.encodeRegs s').length ⟨i + 1, [(l, p, t)]⟩
        ⟨i + s'.length + 1, [(l, p + (Compile.encodeRegs s').length, t)]⟩
  | [], i, p, l, t, rest, _, _, _ => by simpa using Seg.zero w _
  | reg :: s'', i, p, l, t, rest, hlen, hbit, hdrop => by
      have hi : i ≤ w := by
        have : (reg :: s'').length = s''.length + 1 := rfl
        omega
      have hdropA : t.drop p
          = Compile.shiftReg reg ++ (0 :: (Compile.encodeRegs s'' ++ rest)) := by
        rw [hdrop, Compile.encodeRegs_cons]
        simp [List.append_assoc]
      have hbits : ∀ b ∈ reg, b ≤ 1 := fun b hb =>
        hbit reg (List.mem_cons_self ..) b hb
      have h1 := scanBits_seg w i hi reg p l t _ hbits hdropA
      have hdropB : t.drop (p + reg.length) = 0 :: (Compile.encodeRegs s'' ++ rest) := by
        have := drop_append t p (Compile.shiftReg reg) _ hdropA
        rwa [show (Compile.shiftReg reg).length = reg.length from by
          simp [Compile.shiftReg]] at this
      obtain ⟨hget0, hdropC⟩ := drop_head t (p + reg.length) 0 _ hdropB
      have h2 : Seg w 1 ⟨i + 1, [(l, p + reg.length, t)]⟩
          ⟨i + 2, [(l, p + reg.length + 1, t)]⟩ :=
        Seg.single w (step_phase_sep w i hi l t (p + reg.length) hget0)
          (by show i + 1 ≠ w + 6; omega)
      have hbit'' : Compile.BitState s'' := fun r hr x hx =>
        hbit r (List.mem_cons_of_mem _ hr) x hx
      have h3 := scanRegs_seg w s'' (i + 1) (p + reg.length + 1) l t rest
        (by have : (reg :: s'').length = s''.length + 1 := rfl; omega)
        hbit'' hdropC
      have hcomp := (h1.comp h2).comp h3
      have hRlen : (Compile.encodeRegs (reg :: s'')).length
          = reg.length + 1 + (Compile.encodeRegs s'').length := by
        rw [Compile.encodeRegs_cons]
        simp only [List.length_append, List.length_cons, List.length_nil,
          Compile.shiftReg, List.length_map]
      rw [show reg.length + 1 + (Compile.encodeRegs s'').length
            = (Compile.encodeRegs (reg :: s'')).length from hRlen.symm,
          show i + 1 + s''.length + 1 = i + (reg :: s'').length + 1 from by
            simp only [List.length_cons]; omega,
          show p + reg.length + 1 + (Compile.encodeRegs s'').length
            = p + (Compile.encodeRegs (reg :: s'')).length from by
            rw [hRlen]; omega] at hcomp
      exact hcomp

/-- The rewind scan: `S` walks left over interior cells (`< 3`) down to `0`. -/
theorem rewind_seg (w : Nat) (l t : List Nat) :
    ∀ (p : Nat),
      (∀ j, 1 ≤ j → j ≤ p → ∃ v, t[j]? = some v ∧ v < 3) →
      Seg w p ⟨w + 5, [(l, p, t)]⟩ ⟨w + 5, [(l, 0, t)]⟩
  | 0, _ => Seg.zero w _
  | p + 1, hcells => by
      obtain ⟨v, hv, hv3⟩ := hcells (p + 1) (by omega) (Nat.le_refl _)
      have hstep := step_S_scan w l t (p + 1) v hv hv3
      rw [Nat.add_sub_cancel] at hstep
      have h1 : Seg w 1 ⟨w + 5, [(l, p + 1, t)]⟩ ⟨w + 5, [(l, p, t)]⟩ :=
        Seg.single w hstep (by show w + 5 ≠ w + 6; omega)
      have h2 := rewind_seg w l t p (fun j hj hjp => hcells j hj (by omega))
      have hcomp := h1.comp h2
      rwa [Nat.add_comm 1 p] at hcomp

/-! ### The valid-tape forward run (F5 forward direction) -/

/-- **The full valid-tape segment**: on `encodeTape s` (`BitState s`,
`s.length = w + 1`) the format check runs `2·|tape| + 1` steps to the done
state with the head rewound to `0` and the tape untouched, never visiting the
done state earlier. -/
theorem formatCheck_seg (w : Nat) (s : State) (hbit : Compile.BitState s)
    (hlen : s.length = w + 1) :
    Seg w (2 * (Compile.encodeTape s).length + 1)
      ⟨0, [([], 0, Compile.encodeTape s)]⟩
      ⟨w + 6, [([], 0, Compile.encodeTape s)]⟩ := by
  set T := Compile.encodeTape s with hT
  set R := (Compile.encodeRegs s).length with hR
  have hTdef : T = 3 :: (Compile.encodeRegs s ++ [3]) := rfl
  have hTlen : T.length = R + 2 := by
    rw [hTdef]; simp [hR]
  -- 1. the start step
  have hget0 : T[0]? = some 3 := by rw [hTdef]; rfl
  have h1 : Seg w 1 ⟨0, [([], 0, T)]⟩ ⟨1, [([], 1, T)]⟩ :=
    Seg.single w (step_start w [] T hget0) (by show (0 : Nat) ≠ w + 6; omega)
  -- 2. all `w + 1` registers
  have hdrop1 : T.drop 1 = Compile.encodeRegs s ++ [3] := by rw [hTdef]; rfl
  have h2 := scanRegs_seg w s 0 1 [] T [3] (by omega) hbit hdrop1
  rw [hlen, ← hR] at h2
  -- h2 : Seg w R ⟨1, pos 1⟩ ⟨w + 2, pos 1 + R⟩ (modulo 0 + _ normalization)
  have h2' : Seg w R ⟨0 + 1, [([], 1, T)]⟩ ⟨w + 2, [([], 1 + R, T)]⟩ := by
    rw [show 0 + (w + 1) + 1 = w + 2 from by omega] at h2
    exact h2
  -- 3. `F` reads the trailing terminator at `1 + R`
  have hdrop2 : T.drop (1 + R) = [3] := by
    have := drop_append T 1 (Compile.encodeRegs s) [3] hdrop1
    rwa [← hR] at this
  have hget2 : T[1 + R]? = some 3 := (drop_head T (1 + R) 3 [] hdrop2).1
  have h3 : Seg w 1 ⟨w + 2, [([], 1 + R, T)]⟩ ⟨w + 3, [([], 1 + R + 1, T)]⟩ :=
    Seg.single w (step_F w [] T (1 + R) hget2) (by show w + 2 ≠ w + 6; omega)
  -- 4. `E` reads past the end at `R + 2 = |T|`
  have hget3 : T[1 + R + 1]? = none := by
    rw [List.getElem?_eq_none]
    omega
  have h4 : Seg w 1 ⟨w + 3, [([], 1 + R + 1, T)]⟩ ⟨w + 4, [([], 1 + R, T)]⟩ := by
    have := Seg.single w (step_E w [] T (1 + R + 1) hget3)
      (by show w + 3 ≠ w + 6; omega)
    rwa [Nat.add_sub_cancel] at this
  -- 5. `B` steps off the terminator
  have h5 : Seg w 1 ⟨w + 4, [([], 1 + R, T)]⟩ ⟨w + 5, [([], R, T)]⟩ := by
    have := Seg.single w (step_B w [] T (1 + R) hget2)
      (by show w + 4 ≠ w + 6; omega)
    rwa [show 1 + R - 1 = R from by omega] at this
  -- 6. the rewind: interior cells `1 … R` are `< 3`
  have hcells : ∀ j, 1 ≤ j → j ≤ R → ∃ v, T[j]? = some v ∧ v < 3 := by
    intro j hj1 hjR
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : k < R := by omega
    have hgetk : T[k + 1]? = some (Compile.encodeRegs s)[k] := by
      rw [hTdef]
      show (Compile.encodeRegs s ++ [3])[k]? = _
      rw [List.getElem?_append_left (by rw [← hR]; exact hk),
          List.getElem?_eq_getElem (hR ▸ hk)]
    refine ⟨(Compile.encodeRegs s)[k], hgetk, ?_⟩
    have hmem : (Compile.encodeRegs s)[k] ∈ Compile.encodeRegs s :=
      List.getElem_mem _
    have hlt4 : (Compile.encodeRegs s)[k] < 4 :=
      Compile.encodeRegs_lt_four s hbit _ hmem
    have hne3 : (Compile.encodeRegs s)[k] ≠ 3 :=
      Compile.encodeRegs_no_endMark s hbit _ hmem
    omega
  have h6 : Seg w R ⟨w + 5, [([], R, T)]⟩ ⟨w + 5, [([], 0, T)]⟩ :=
    rewind_seg w [] T R hcells
  -- 7. `S` finds the leading sentinel
  have h7 : Seg w 1 ⟨w + 5, [([], 0, T)]⟩ ⟨w + 6, [([], 0, T)]⟩ :=
    Seg.single w (step_S_found w [] T 0 hget0) (by show w + 5 ≠ w + 6; omega)
  have hcomp := ((((((h1.comp h2').comp h3).comp h4).comp h5).comp h6).comp h7)
  rwa [show 1 + R + 1 + 1 + 1 + R + 1 = 2 * T.length + 1 from by
    rw [hTlen]; omega] at hcomp

/-- **F5 forward run lemma** (the `composeFlatTM_run` `h_run1` shape): a valid
`encodeTape` passes the format check in `2·|tape| + 1` steps, tape unchanged,
head `0`, halting at the unique halt state `w + 6`. -/
theorem formatCheck_run (w : Nat) (s : State) (hbit : Compile.BitState s)
    (hlen : s.length = w + 1) :
    runFlatTM (2 * (Compile.encodeTape s).length + 1) (formatCheckTM w)
        (initFlatConfig (formatCheckTM w) [Compile.encodeTape s])
      = some ⟨w + 6, [([], 0, Compile.encodeTape s)]⟩ :=
  (formatCheck_seg w s hbit hlen).1

/-- **F5 forward trajectory** (the `composeFlatTM_run` `h_traj1` shape): no
early exit, no early halt. -/
theorem formatCheck_traj (w : Nat) (s : State) (hbit : Compile.BitState s)
    (hlen : s.length = w + 1) :
    ∀ k, k < 2 * (Compile.encodeTape s).length + 1 → ∀ ck,
      runFlatTM k (formatCheckTM w)
          (initFlatConfig (formatCheckTM w) [Compile.encodeTape s]) = some ck →
      ck.state_idx ≠ w + 6 ∧
      haltingStateReached (formatCheckTM w) ck = false := by
  intro k hk ck hck
  have hne := (formatCheck_seg w s hbit hlen).2 k hk ck hck
  exact ⟨hne, formatCheck_halting_of_ne w ck hne⟩

/-! ### The invalid-cert stuck direction (F5 backward direction) -/

private theorem stuck_forever (w : Nat) (cfg : FlatTMConfig)
    (hne : cfg.state_idx ≠ w + 6)
    (hstep : stepFlatTM (formatCheckTM w) cfg = none) :
    ∀ m cm, runFlatTM m (formatCheckTM w) cfg = some cm →
      haltingStateReached (formatCheckTM w) cm = false := by
  intro m cm hcm
  rw [runFlatTM_stuck (formatCheckTM w) cfg
        (formatCheck_halting_of_ne w cfg hne) hstep m] at hcm
  obtain rfl : cfg = cm := Option.some.inj hcm
  exact formatCheck_halting_of_ne w cfg hne

private theorem step_then (w : Nat) (cfg cfg' : FlatTMConfig)
    (hne : cfg.state_idx ≠ w + 6)
    (hstep : stepFlatTM (formatCheckTM w) cfg = some cfg')
    (ih : ∀ m cm, runFlatTM m (formatCheckTM w) cfg' = some cm →
        haltingStateReached (formatCheckTM w) cm = false) :
    ∀ m cm, runFlatTM m (formatCheckTM w) cfg = some cm →
      haltingStateReached (formatCheckTM w) cm = false := by
  intro m cm hcm
  cases m with
  | zero =>
      obtain rfl : cfg = cm := Option.some.inj hcm
      exact formatCheck_halting_of_ne w cfg hne
  | succ n =>
      have hunfold : runFlatTM (n + 1) (formatCheckTM w) cfg
          = runFlatTM n (formatCheckTM w) cfg' := by
        show (if haltingStateReached (formatCheckTM w) cfg = true then some cfg
              else match stepFlatTM (formatCheckTM w) cfg with
                | none => some cfg
                | some c => runFlatTM n (formatCheckTM w) c) = _
        rw [if_neg (by rw [formatCheck_halting_of_ne w cfg hne]; simp), hstep]
      rw [hunfold] at hcm
      exact ih n cm hcm

private theorem seg_then_stuck (w : Nat) {n : Nat} {c0 c1 : FlatTMConfig}
    (hseg : Seg w n c0 c1)
    (h1 : ∀ m cm, runFlatTM m (formatCheckTM w) c1 = some cm →
        haltingStateReached (formatCheckTM w) cm = false) :
    ∀ m cm, runFlatTM m (formatCheckTM w) c0 = some cm →
      haltingStateReached (formatCheckTM w) cm = false := by
  intro m cm hcm
  rcases Nat.lt_or_ge m n with hlt | hge
  · exact formatCheck_halting_of_ne w cm (hseg.2 m hlt cm hcm)
  · rw [show m = n + (m - n) from by omega,
        runFlatTM_compose (formatCheckTM w) n (m - n) c0 c1 hseg.1] at hcm
    exact h1 (m - n) cm hcm

/-- **The cert-region scan sticks on every grammar violation.** From the cert
phase (state `w + 1`) with the remaining tape equal to the (mis-formatted)
cert region, the machine never reaches a halting configuration. -/
theorem certScan_stuck (w : Nat) :
    ∀ (cert : List Nat) (p : Nat) (l t : List Nat),
      t.drop p = cert → certOKB cert = false →
      ∀ m cm, runFlatTM m (formatCheckTM w) ⟨w + 1, [(l, p, t)]⟩ = some cm →
        haltingStateReached (formatCheckTM w) cm = false := by
  intro cert
  induction cert with
  | nil =>
      intro p l t hdrop _
      exact stuck_forever w _ (by show w + 1 ≠ w + 6; omega)
        (step_phase_none w w (Nat.le_refl w) l t p (Or.inl (drop_none t p hdrop)))
  | cons v rest ih =>
      intro p l t hdrop hbad
      obtain ⟨hget, hdrop1⟩ := drop_head t p v rest hdrop
      by_cases hv1 : v = 1
      · subst hv1
        have hbad' : certOKB rest = false := by rwa [certOKB_one] at hbad
        exact step_then w _ _ (by show w + 1 ≠ w + 6; omega)
          (step_phase_bit w w (Nat.le_refl w) l t p 0 hget (by omega))
          (ih (p + 1) l t hdrop1 hbad')
      by_cases hv2 : v = 2
      · subst hv2
        have hbad' : certOKB rest = false := by rwa [certOKB_two] at hbad
        exact step_then w _ _ (by show w + 1 ≠ w + 6; omega)
          (step_phase_bit w w (Nat.le_refl w) l t p 1 hget (by omega))
          (ih (p + 1) l t hdrop1 hbad')
      by_cases hv0 : v = 0
      · subst hv0
        -- delimiter: enter `F` at `p + 1`; the only accepted continuation
        -- `[3]`-then-end would make the cert `[0, 3]`, excluded by `hbad`.
        have hF := step_phase_sep w w (Nat.le_refl w) l t p hget
        have hstepF : stepFlatTM (formatCheckTM w) ⟨w + 1, [(l, p, t)]⟩
            = some ⟨w + 2, [(l, p + 1, t)]⟩ := hF
        refine step_then w _ _ (by show w + 1 ≠ w + 6; omega) hstepF ?_
        match rest, hbad, hdrop1 with
        | [], _, hdrop1 =>
            exact stuck_forever w _ (by show w + 2 ≠ w + 6; omega)
              (step_F_none w l t (p + 1) (by rw [drop_none t (p + 1) hdrop1]; simp))
        | u :: rest2, hbad, hdrop1 =>
            obtain ⟨hgetu, hdrop2⟩ := drop_head t (p + 1) u rest2 hdrop1
            by_cases hu : u = 3
            · subst hu
              match rest2, hbad, hdrop2 with
              | [], hbad, _ => exact absurd hbad (by simp)
              | x :: rest3, _, hdrop2 =>
                  obtain ⟨hgetx, _⟩ := drop_head t (p + 1 + 1) x rest3 hdrop2
                  refine step_then w _ _ (by show w + 2 ≠ w + 6; omega)
                    (step_F w l t (p + 1) hgetu) ?_
                  exact stuck_forever w _ (by show w + 3 ≠ w + 6; omega)
                    (step_E_none w l t (p + 1 + 1) x hgetx)
            · exact stuck_forever w _ (by show w + 2 ≠ w + 6; omega)
                (step_F_none w l t (p + 1)
                  (by rw [hgetu]; intro hh; injection hh with h; exact hu h))
      · -- `v ∉ {0, 1, 2}`: the phase has no transition
        exact stuck_forever w _ (by show w + 1 ≠ w + 6; omega)
          (step_phase_none w w (Nat.le_refl w) l t p
            (Or.inr ⟨v, hget, hv0, hv1, hv2⟩))

/-- **F5 backward direction.** On a tape whose (well-formed) input prefix is
followed by a grammar-violating cert region, the format check NEVER reaches a
halting configuration — under accept-by-halting, garbage certificates cannot
produce an accept. -/
theorem formatCheck_stuck (w : Nat) (sx : State) (hbit : Compile.BitState sx)
    (hlen : sx.length = w) (cert : List Nat) (hbad : certOKB cert = false) :
    ∀ m cm, runFlatTM m (formatCheckTM w)
        (initFlatConfig (formatCheckTM w)
          [(3 :: Compile.encodeRegs sx) ++ cert]) = some cm →
      haltingStateReached (formatCheckTM w) cm = false := by
  set T : List Nat := (3 :: Compile.encodeRegs sx) ++ cert with hT
  set R : Nat := (Compile.encodeRegs sx).length with hR
  have hget0 : T[0]? = some 3 := by rw [hT]; rfl
  have h1 : Seg w 1 ⟨0, [([], 0, T)]⟩ ⟨1, [([], 1, T)]⟩ :=
    Seg.single w (step_start w [] T hget0) (by show (0 : Nat) ≠ w + 6; omega)
  have hdrop1 : T.drop 1 = Compile.encodeRegs sx ++ cert := by rw [hT]; rfl
  have h2 := scanRegs_seg w sx 0 1 [] T cert (by omega) hbit hdrop1
  rw [hlen, ← hR] at h2
  have h2' : Seg w R ⟨0 + 1, [([], 1, T)]⟩ ⟨w + 1, [([], 1 + R, T)]⟩ := by
    rw [show 0 + w + 1 = w + 1 from by omega] at h2
    exact h2
  have hdropC : T.drop (1 + R) = cert := by
    have := drop_append T 1 (Compile.encodeRegs sx) cert hdrop1
    rwa [← hR] at this
  exact seg_then_stuck w (h1.comp h2')
    (certScan_stuck w cert (1 + R) [] T hdropC hbad)

end Complexity.Lang.FormatCheck
