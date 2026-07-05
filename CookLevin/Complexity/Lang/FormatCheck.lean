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

end Complexity.Lang.FormatCheck
