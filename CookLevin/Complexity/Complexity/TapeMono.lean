import Complexity.Complexity.MachineSemantics

set_option autoImplicit false

/-! # Tape monotonicity — the physical tape never shrinks (Risk C2 finding)

A structural fact about the `FlatTM` machine model that bears directly on the
compiler's physical contract (Risk C2). In this model a configuration's tape is
a triple `(left, head, right)`; the *content* lives entirely in `right`
(`left` is always `[]` and the head is an index into `right` — see
`Compile.flattenTape`). The two tape primitives are:

* `writeCurrentTapeSymbol` — an in-range write replaces one cell
  (`right.take head ++ sym :: right.drop (head+1)`, **same length**); an
  out-of-range write pads and appends (**grows**); a `none`-write is a no-op.
* `moveTapeHead` — only changes the head index, never `right`.

Consequently **`right.length` is monotonically non-decreasing along every run**
(`runFlatTM_single_length_le`). The machine can grow its tape but can *never*
make it shorter.

## Why this matters (the finding)

The compiler's per-`Op` physical contract (`Compile.compileOp_sound_physical`)
requires the machine to halt with its tape **exactly** `encodeTape (Op.eval o s)`
so that compiled fragments compose (`compileSeq_compose_physical` resumes the
next fragment on that exact tape). For a *length-decreasing* op — `clear`,
`tail`, a shrinking `copy`, … — `encodeTape (Op.eval o s)` is a **shorter** list
than the input `encodeTape s`. By the monotonicity theorem below, **no run can
produce it**: the exact-tape contract is *unsatisfiable* for every deletion op.

`appendOne` / `appendZero` are the only ops implemented so far precisely because
they purely *grow* the tape (insert one cell), so the lengths match exactly. The
handoff's "implement `opClear` following the `appendBit_physical` pattern" path
is therefore blocked as stated. See `Compile.clear_physical_unsatisfiable` for
the concrete corollary and `HANDOFF.md` / `ROADMAP.md` Risk C2 for the
recommended resolution (a residue-tolerant physical contract: exit tape
`encodeTape output ++ filler`, decoded identically since `decodeTape` stops at
the first end-of-tape terminator, plus a left-shift "delete" gadget). -/

namespace Complexity

/-- A write never shortens the tape content `right`. An in-range write keeps the
length; an out-of-range write grows it; a `none`-write is a no-op. -/
theorem writeCurrentTapeSymbol_length_le (tape : List Nat × Nat × List Nat)
    (sym : Option Nat) :
    tape.2.2.length ≤ (writeCurrentTapeSymbol tape sym).2.2.length := by
  obtain ⟨left, head, right⟩ := tape
  cases sym with
  | none => simp [writeCurrentTapeSymbol]
  | some s =>
    simp only [writeCurrentTapeSymbol]
    by_cases h : head < right.length
    · rw [dif_pos h]
      simp only [List.length_append, List.length_take, List.length_cons,
        List.length_drop, Nat.min_eq_left (Nat.le_of_lt h)]
      omega
    · rw [dif_neg h]
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil]
      omega

/-- `moveTapeHead` leaves the tape content `right` untouched. -/
theorem moveTapeHead_content (tape : List Nat × Nat × List Nat) (m : TMMove) :
    (moveTapeHead tape m).2.2 = tape.2.2 := by
  cases m <;> rfl

/-- A single `tapeStep` (write then move) never shortens the content. -/
theorem tapeStep_length_le (tape : List Nat × Nat × List Nat)
    (w : Option Nat) (m : TMMove) :
    tape.2.2.length ≤ (tapeStep tape w m).2.2.length := by
  rw [tapeStep, moveTapeHead_content]
  exact writeCurrentTapeSymbol_length_le tape w

/-- **Single-tape step monotonicity.** If a one-tape configuration steps, the
result is again one-tape and its content is at least as long. -/
theorem stepFlatTM_single_length_le (M : FlatTM) (cfg cfg' : FlatTMConfig)
    (tp : List Nat × Nat × List Nat) (htape : cfg.tapes = [tp])
    (hstep : stepFlatTM M cfg = some cfg') :
    ∃ tp', cfg'.tapes = [tp'] ∧ tp.2.2.length ≤ tp'.2.2.length := by
  obtain ⟨entry, -, happly⟩ :
      ∃ entry, M.trans.find? (fun e => entryMatchesConfig e cfg) = some entry ∧
        applyTransitionEntry cfg entry = some cfg' := by
    simpa [stepFlatTM, Option.bind_eq_some_iff] using hstep
  rw [applyTransitionEntry, htape] at happly
  simp only [List.length_singleton] at happly
  split at happly
  · next hg =>
      obtain ⟨hw, hm⟩ := hg
      obtain ⟨w, hwe⟩ := List.length_eq_one_iff.mp hw.symm
      obtain ⟨m, hme⟩ := List.length_eq_one_iff.mp hm.symm
      rw [hwe, hme] at happly
      simp only [List.zip_cons_cons, List.zip_nil_right, List.zipWith_cons_cons,
        List.zipWith_nil_right, Option.some.injEq] at happly
      refine ⟨tapeStep tp w m, ?_, tapeStep_length_le tp w m⟩
      rw [← happly]
  · exact absurd happly (by simp)

/-- **Run monotonicity (single tape).** Along any run from a one-tape
configuration, the result is one-tape and its content never shrinks. -/
theorem runFlatTM_single_length_le (M : FlatTM) :
    ∀ (n : Nat) (cfg cfg' : FlatTMConfig) (tp : List Nat × Nat × List Nat),
      cfg.tapes = [tp] → runFlatTM n M cfg = some cfg' →
      ∃ tp', cfg'.tapes = [tp'] ∧ tp.2.2.length ≤ tp'.2.2.length := by
  intro n
  induction n with
  | zero =>
      intro cfg cfg' tp htape hrun
      simp only [runFlatTM, Option.some.injEq] at hrun
      exact ⟨tp, hrun ▸ htape, Nat.le_refl _⟩
  | succ n ih =>
      intro cfg cfg' tp htape hrun
      simp only [runFlatTM] at hrun
      by_cases hh : haltingStateReached M cfg = true
      · rw [if_pos hh, Option.some.injEq] at hrun
        exact ⟨tp, hrun ▸ htape, Nat.le_refl _⟩
      · rw [if_neg hh] at hrun
        cases hstep : stepFlatTM M cfg with
        | none => rw [hstep, Option.some.injEq] at hrun; exact ⟨tp, hrun ▸ htape, Nat.le_refl _⟩
        | some c =>
            rw [hstep] at hrun
            obtain ⟨tp1, hc, hle1⟩ := stepFlatTM_single_length_le M cfg c tp htape hstep
            obtain ⟨tp', hcfg', hle2⟩ := ih c cfg' tp1 hc hrun
            exact ⟨tp', hcfg', Nat.le_trans hle1 hle2⟩

/-- **No run shrinks the tape (the finding, packaged for the compiler).**
Starting from `initFlatConfig M [input]` (head `0`, content `input`), if the
machine halts with a one-tape configuration, that tape's content is **at least
as long as `input`**. A machine can never transform `input` into a strictly
shorter content list. -/
theorem runFlatTM_initFlatConfig_no_shrink (M : FlatTM) (n : Nat) (input : List Nat)
    (cfg' : FlatTMConfig) (tp' : List Nat × Nat × List Nat)
    (hrun : runFlatTM n M (initFlatConfig M [input]) = some cfg')
    (htape' : cfg'.tapes = [tp']) :
    input.length ≤ tp'.2.2.length := by
  have htape : (initFlatConfig M [input]).tapes = [([], 0, input)] := by
    simp [initFlatConfig]
  obtain ⟨tp'', hc, hle⟩ :=
    runFlatTM_single_length_le M n _ cfg' ([], 0, input) htape hrun
  rw [hc, List.cons.injEq] at htape'
  exact htape'.1 ▸ hle

end Complexity
