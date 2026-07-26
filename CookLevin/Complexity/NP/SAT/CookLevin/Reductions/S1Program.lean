import Complexity.NP.SAT.CookLevin.Reductions.S1Emit

set_option autoImplicit false
set_option maxRecDepth 8000

/-! # S1, part 6 — the program skeleton and the `computes` obligation

`S1Witness.s1_reductionLang`'s `computes` field, decomposed against the five
program stages. Two of them are still `sorry` (stage **C**, the card emitter,
and stage **M-yes**, the output multiplex); *everything else here is proven*,
including the **whole guard-false branch end to end**.

## Why this file exists (and why it is separate from `S1Witness.lean`)

The output-key layout (`s1Key` / `s1Extract` / `SIGMA`…`STEPS` / `s1RegBound`)
is a *program-layout* fact, not a witness fact: the program is what puts the
five registers where `s1Key` reads them. They moved here from `S1Witness.lean`,
which now imports this module (the dependency used to point the wrong way).

## The program

```
s1Program = stagePG ;; ifBit FLG yesBranch stageMNo
yesBranch = stageSig ;; stageInit ;; stageC ;; stageFin ;; stageMYes
```

* `S1Parse.stagePG` — parse + guard (proven, `S1Parse.lean`).
* `S1Cards.stageMNo` — the guard-false output (proven, `S1Cards.lean`).
* `S1Emit.stageSig` / `stageInit` / `stageFin` — Σ, I, F (proven, `S1Emit.lean`).
* `stageC` / `stageMYes` — **OPEN**, `def` + `sorry` here, each with the exact
  run-lemma contract the assembly consumes (`stageC_run`, `stageMYes_run`).

## The coarse frame predicates

Every stage's `_run` carries an explicit `r ≠ …` chain (Σ: 5 registers, F: 10,
I: 14 including `readNum`'s reserved trio). Composing five of those register by
register is unreadable, so the dirty sets are bundled once:

* **`EScratch`** — the shared emitter scratch `[37, 48)` plus the three
  registers `CliqueRelTM.readNum` hard-wires (`HEAD` 15, `INBLK` 16,
  `SKIPR` 26). Every one of Σ / I / F dirties **only** `EScratch` plus its own
  output register, which is exactly what `stageSig_frame` / `stageInit_frame` /
  `stageFin_frame` say.
* **`CDirty`** — stage C's larger licence: `EScratch`, its own output `EOUT_C`,
  and the whole P/G scratch block `[14, 32)`, which is free once stage G has
  run (HANDOFF's stage-C register budget). Nothing read after stage C lives
  there: F reads `PSIG`/`PSTATES`/`PHALT` (6/8/11) and M-yes reads register `4`
  and the four `EOUT_*`.

⚠ `EScratch`/`CDirty` at a concrete register are `by decide` (they are
`Nat` comparisons under the `Var` abbrev); `omega` cannot see `Var`.

## What the yes-branch assembly already establishes (the risk payoff)

`yesBranch_run` type-checks the five stage contracts *against each other* and
against `s1Key (guessTableau …)`. Three layout facts it pins, before the largest
remaining `Cmd` is written:

1. **No stage clobbers a later stage's input.** Σ/I/F only ever dirty
   `EScratch` + their own output, and stage C's wider `CDirty` licence is still
   disjoint from `{4, 6, 8, 11, EOUT_S, EOUT_I}`.
2. **`STEPS` is `1^(steps+1)`, not a copy of register `4`**
   (`guessTableauTyped.steps = steps + 1`) — the `+1` is visible in
   `stageMYes_run`'s conclusion, so stage M-yes cannot be built as five copies.
3. **Register `4` must still hold `1^steps` when stage M-yes runs**, i.e. the
   input layout survives all four emitter stages — which is why `HSTP` appears
   in `stageMYes_run`'s hypotheses rather than being read earlier and stashed.
-/

namespace S1Program

open Complexity.Lang Complexity.Simulators HeadLayout

/-! ## The output key (= `FlatTCCFree.encodeIn` registers 1–5)

Moved here from `S1Witness.lean` (2026-07-26): these are program-layout
definitions. -/

/-- The S1 program's output registers, in order: the successor witness's own
input layout (`FlatTCCFree.encodeIn` restricted to registers `1`–`5`). -/
def s1Key (C : FlatTCC) : List (List Nat) :=
  [List.replicate C.Sigma 1, FlatTCCFree.encNats C.init,
   FlatTCCFree.encCardsIn C.cards, FlatTCCFree.encFinal C.final,
   List.replicate C.steps 1]

def SIGMA : Var := 1
def INIT  : Var := 2
def CARDS : Var := 3
def FINAL : Var := 4
def STEPS : Var := 5

/-- Read the output key back off a state. -/
def s1Extract (s : State) : List (List Nat) :=
  [State.get s SIGMA, State.get s INIT, State.get s CARDS,
   State.get s FINAL, State.get s STEPS]

/-- The S1 program's register frame. Must be `≥ 6` (output `1`–`5` plus
scratch); keeping it `≤ 57` (the tail composite's frame) keeps the fourth
seam's `mfc` a constant-size scrub. -/
def s1RegBound : Nat := 48

/-! ## The coarse frame predicates -/

/-- The registers every emitter stage is free to dirty *besides its own
output*: the shared scratch block `[37, 48)` and `readNum`'s reserved trio. -/
abbrev EScratch (r : Var) : Prop :=
  (37 ≤ r ∧ r < 48) ∨ r = CliqueRelTM.HEAD ∨ r = CliqueRelTM.INBLK
    ∨ r = CliqueRelTM.SKIPR

/-- Stage C's dirty licence: the shared scratch, its own output, and the P/G
scratch block `[14, 32)` (free once stage G has run). -/
abbrev CDirty (r : Var) : Prop :=
  EScratch r ∨ r = S1Emit.EOUT_C ∨ (14 ≤ r ∧ r < 32)

/-- Turn a clean register into the `≠` a stage's `_run` frame clause wants. -/
theorem ne_of_not_scratch {r : Var} (h : ¬ EScratch r) (k : Var) (hk : EScratch k) :
    r ≠ k := fun he => h (by rw [he]; exact hk)

theorem ne_of_not_cdirty {r : Var} (h : ¬ CDirty r) (k : Var) (hk : CDirty k) :
    r ≠ k := fun he => h (by rw [he]; exact hk)

/-! ### The three built stages, in coarse-frame form -/

theorem stageSig_frame (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (r : Var) (hd : ¬ EScratch r) (hO : r ≠ S1Emit.EOUT_S) :
    State.get (S1Emit.stageSig.eval s) r = State.get s r :=
  (S1Emit.stageSig_run M s hsig hst).2 r
    (ne_of_not_scratch hd S1Emit.EA (by decide))
    (ne_of_not_scratch hd S1Emit.EB (by decide))
    (ne_of_not_scratch hd S1Emit.ESG (by decide))
    (ne_of_not_scratch hd S1Emit.EJ1 (by decide)) hO

theorem stageFin_frame (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (hph : State.get s S1Parse.PHALT = M.halt.map S1Parse.bitOf)
    (r : Var) (hd : ¬ EScratch r) (hO : r ≠ S1Emit.EOUT_F) :
    State.get (S1Emit.stageFin.eval s) r = State.get s r :=
  (S1Emit.stageFin_run M s hsig hst hph).2 r hO
    (ne_of_not_scratch hd S1Emit.EA (by decide))
    (ne_of_not_scratch hd S1Emit.EB (by decide))
    (ne_of_not_scratch hd S1Emit.EC (by decide))
    (ne_of_not_scratch hd S1Emit.ED (by decide))
    (ne_of_not_scratch hd S1Emit.EE (by decide))
    (ne_of_not_scratch hd S1Emit.EJ1 (by decide))
    (ne_of_not_scratch hd S1Emit.EJ2 (by decide))
    (ne_of_not_scratch hd S1Emit.EJ3 (by decide))
    (ne_of_not_scratch hd S1Emit.EK1 (by decide))

theorem stageInit_frame (M : flatTM) (str : List Nat) (maxSize steps : Nat) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (hS : State.get s S1Parse.SREG = encSyms str)
    (hmx : State.get s S1Emit.HMAX = List.replicate maxSize 1)
    (hsp : State.get s S1Emit.HSTP = List.replicate steps 1)
    (hb : list_ofFlatType M.sig str)
    (r : Var) (hd : ¬ EScratch r) (hO : r ≠ S1Emit.EOUT_I) :
    State.get (S1Emit.stageInit.eval s) r = State.get s r :=
  (S1Emit.stageInit_run M str maxSize steps s hsig hst hS hmx hsp hb).2 r
    ⟨hO, ne_of_not_scratch hd S1Emit.EC (by decide),
      ne_of_not_scratch hd S1Emit.ED (by decide),
      ne_of_not_scratch hd S1Emit.EE (by decide),
      ne_of_not_scratch hd S1Emit.EJ1 (by decide),
      ne_of_not_scratch hd S1Emit.EJ2 (by decide),
      ne_of_not_scratch hd S1Emit.EJ3 (by decide),
      ne_of_not_scratch hd S1Emit.EK1 (by decide),
      ne_of_not_scratch hd CliqueRelTM.HEAD (by decide),
      ne_of_not_scratch hd CliqueRelTM.INBLK (by decide),
      ne_of_not_scratch hd CliqueRelTM.SKIPR (by decide)⟩
    (ne_of_not_scratch hd S1Emit.EA (by decide))
    (ne_of_not_scratch hd S1Emit.EB (by decide))
    (ne_of_not_scratch hd S1Emit.ESG (by decide))

/-! ## Stage C — the card emitter (OPEN)

The largest remaining `Cmd`. Its target is pinned by `S1Cards.encCards_eq`:
`EOUT_C := FlatTCCFree.encNats (S1Cards.cardBlocks M)`, where `cardBlocks` is
an explicit `++` of seven `List.range` streams with one proven equation per
family. Build it family by family (HANDOFF "NEXT BOTTOM-UP", item 2); the
contract below is what the assembly consumes and must not change.

The validity hypotheses are free: stage C sits under `Cmd.ifBit S1Parse.FLG`,
so the guard has already established them. -/

/-- **OPEN (the S1 critical path).** The card emitter. -/
def stageC : Cmd := sorry

/-- **OPEN.** Stage C's contract. Every input register it names is a stage-P
output; `CDirty` is its dirty licence (see the module docstring). -/
theorem stageC_run (M : flatTM) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (hph : State.get s S1Parse.PHALT = M.halt.map S1Parse.bitOf)
    (hnt : State.get s S1Parse.PNTRANS = List.replicate M.trans.length 1)
    (htr : State.get s S1Parse.PTRANS = encSyms (S1Parse.transFlat M))
    (hV : validFlatTM M) (hT : M.tapes = 1) :
    State.get (stageC.eval s) S1Emit.EOUT_C
        = FlatTCCFree.encNats (S1Cards.cardBlocks M)
    ∧ (∀ r : Var, ¬ CDirty r → State.get (stageC.eval s) r = State.get s r) := by
  sorry

/-- **OPEN.** `decide`-able once `stageC` is a concrete `Cmd`. -/
theorem stageC_usesBelow : Cmd.UsesBelow stageC 48 := by
  sorry

/-! ## Stage M-yes — the output multiplex (OPEN)

`EOUT_T := 1^(steps + 1)` off register `4`, then five copies into registers
`1`–`5`.

⚠ **Order matters, twice over.** Registers `1`–`4` are the *input* layout, so
`EOUT_T` must be built from register `4` (`HSTP`, `1^steps`) *before*
`copy 4 EOUT_F` overwrites it, and nothing may read registers `1`–`4`
afterwards. And the `+ 1` is `guessTableauTyped.steps = steps + 1` — it is
**not** a copy of register `4`. -/

/-- **OPEN.** The output multiplex on the guard-true branch. -/
def stageMYes : Cmd := sorry

/-- **OPEN.** Stage M-yes's contract, stated so that the assembly consumes
exactly one fact: the five output registers hold `s1Key` of the tableau. -/
theorem stageMYes_run (M : flatTM) (str : List Nat) (maxSize steps : Nat) (s : State)
    (hsp : State.get s S1Emit.HSTP = List.replicate steps 1)
    (hS : State.get s S1Emit.EOUT_S = List.replicate (PSg M) 1)
    (hI : State.get s S1Emit.EOUT_I
        = FlatTCCFree.encNats (flattenString (preludeRow M str maxSize steps)))
    (hC : State.get s S1Emit.EOUT_C = FlatTCCFree.encNats (S1Cards.cardBlocks M))
    (hF : State.get s S1Emit.EOUT_F
        = FlatTCCFree.encFinal (FlatTCC.flattenFinal (guessFinal M))) :
    s1Extract (stageMYes.eval s) = s1Key (guessTableau M str maxSize steps) := by
  sorry

/-- **OPEN.** `decide`-able once `stageMYes` is a concrete `Cmd`. -/
theorem stageMYes_usesBelow : Cmd.UsesBelow stageMYes 48 := by
  sorry

/-! ## The yes branch -/

def ySuf3 : Cmd := S1Emit.stageFin ;; stageMYes
def ySuf2 : Cmd := stageC ;; ySuf3
def ySuf1 : Cmd := S1Emit.stageInit ;; ySuf2

/-- The guard-true branch: Σ, I, C, F, then the multiplex. -/
def yesBranch : Cmd := S1Emit.stageSig ;; ySuf1

/-- **The yes branch computes the tableau's output key.** Proven modulo the two
open stage contracts — everything *between* the stages (the frame reasoning
that says no stage clobbers a later one's input) is real. -/
theorem yesBranch_run (M : flatTM) (str : List Nat) (maxSize steps : Nat) (s : State)
    (hsig : State.get s S1Parse.PSIG = List.replicate M.sig 1)
    (hst : State.get s S1Parse.PSTATES = List.replicate M.states 1)
    (hph : State.get s S1Parse.PHALT = M.halt.map S1Parse.bitOf)
    (hnt : State.get s S1Parse.PNTRANS = List.replicate M.trans.length 1)
    (htr : State.get s S1Parse.PTRANS = encSyms (S1Parse.transFlat M))
    (hS : State.get s S1Parse.SREG = encSyms str)
    (hmx : State.get s S1Emit.HMAX = List.replicate maxSize 1)
    (hsp : State.get s S1Emit.HSTP = List.replicate steps 1)
    (hV : validFlatTM M) (hT : M.tapes = 1) (hb : list_ofFlatType M.sig str) :
    s1Extract (yesBranch.eval s) = s1Key (guessTableau M str maxSize steps) := by
  -- Σ
  obtain ⟨aS, -⟩ := S1Emit.stageSig_run M s hsig hst
  have aFr := stageSig_frame M s hsig hst
  set s1 := S1Emit.stageSig.eval s with hs1
  have a_sig : State.get s1 S1Parse.PSIG = List.replicate M.sig 1 := by
    rw [hs1, aFr S1Parse.PSIG (by decide) (by decide)]; exact hsig
  have a_st : State.get s1 S1Parse.PSTATES = List.replicate M.states 1 := by
    rw [hs1, aFr S1Parse.PSTATES (by decide) (by decide)]; exact hst
  have a_ph : State.get s1 S1Parse.PHALT = M.halt.map S1Parse.bitOf := by
    rw [hs1, aFr S1Parse.PHALT (by decide) (by decide)]; exact hph
  have a_nt : State.get s1 S1Parse.PNTRANS = List.replicate M.trans.length 1 := by
    rw [hs1, aFr S1Parse.PNTRANS (by decide) (by decide)]; exact hnt
  have a_tr : State.get s1 S1Parse.PTRANS = encSyms (S1Parse.transFlat M) := by
    rw [hs1, aFr S1Parse.PTRANS (by decide) (by decide)]; exact htr
  have a_sr : State.get s1 S1Parse.SREG = encSyms str := by
    rw [hs1, aFr S1Parse.SREG (by decide) (by decide)]; exact hS
  have a_mx : State.get s1 S1Emit.HMAX = List.replicate maxSize 1 := by
    rw [hs1, aFr S1Emit.HMAX (by decide) (by decide)]; exact hmx
  have a_sp : State.get s1 S1Emit.HSTP = List.replicate steps 1 := by
    rw [hs1, aFr S1Emit.HSTP (by decide) (by decide)]; exact hsp
  clear_value s1
  -- I
  obtain ⟨bI, -⟩ := S1Emit.stageInit_run M str maxSize steps s1 a_sig a_st a_sr a_mx a_sp hb
  have bFr := stageInit_frame M str maxSize steps s1 a_sig a_st a_sr a_mx a_sp hb
  set s2 := S1Emit.stageInit.eval s1 with hs2
  have b_S : State.get s2 S1Emit.EOUT_S = List.replicate (PSg M) 1 := by
    rw [hs2, bFr S1Emit.EOUT_S (by decide) (by decide)]; exact aS
  have b_sig : State.get s2 S1Parse.PSIG = List.replicate M.sig 1 := by
    rw [hs2, bFr S1Parse.PSIG (by decide) (by decide)]; exact a_sig
  have b_st : State.get s2 S1Parse.PSTATES = List.replicate M.states 1 := by
    rw [hs2, bFr S1Parse.PSTATES (by decide) (by decide)]; exact a_st
  have b_ph : State.get s2 S1Parse.PHALT = M.halt.map S1Parse.bitOf := by
    rw [hs2, bFr S1Parse.PHALT (by decide) (by decide)]; exact a_ph
  have b_nt : State.get s2 S1Parse.PNTRANS = List.replicate M.trans.length 1 := by
    rw [hs2, bFr S1Parse.PNTRANS (by decide) (by decide)]; exact a_nt
  have b_tr : State.get s2 S1Parse.PTRANS = encSyms (S1Parse.transFlat M) := by
    rw [hs2, bFr S1Parse.PTRANS (by decide) (by decide)]; exact a_tr
  have b_sp : State.get s2 S1Emit.HSTP = List.replicate steps 1 := by
    rw [hs2, bFr S1Emit.HSTP (by decide) (by decide)]; exact a_sp
  clear_value s2
  -- C
  obtain ⟨cC, cFr⟩ := stageC_run M s2 b_sig b_st b_ph b_nt b_tr hV hT
  set s3 := stageC.eval s2 with hs3
  have c_S : State.get s3 S1Emit.EOUT_S = List.replicate (PSg M) 1 := by
    rw [hs3, cFr S1Emit.EOUT_S (by decide)]; exact b_S
  have c_I : State.get s3 S1Emit.EOUT_I
      = FlatTCCFree.encNats (flattenString (preludeRow M str maxSize steps)) := by
    rw [hs3, cFr S1Emit.EOUT_I (by decide)]; exact bI
  have c_sig : State.get s3 S1Parse.PSIG = List.replicate M.sig 1 := by
    rw [hs3, cFr S1Parse.PSIG (by decide)]; exact b_sig
  have c_st : State.get s3 S1Parse.PSTATES = List.replicate M.states 1 := by
    rw [hs3, cFr S1Parse.PSTATES (by decide)]; exact b_st
  have c_ph : State.get s3 S1Parse.PHALT = M.halt.map S1Parse.bitOf := by
    rw [hs3, cFr S1Parse.PHALT (by decide)]; exact b_ph
  have c_sp : State.get s3 S1Emit.HSTP = List.replicate steps 1 := by
    rw [hs3, cFr S1Emit.HSTP (by decide)]; exact b_sp
  clear_value s3
  -- F
  obtain ⟨dF, -⟩ := S1Emit.stageFin_run M s3 c_sig c_st c_ph
  have dFr := stageFin_frame M s3 c_sig c_st c_ph
  set s4 := S1Emit.stageFin.eval s3 with hs4
  have d_S : State.get s4 S1Emit.EOUT_S = List.replicate (PSg M) 1 := by
    rw [hs4, dFr S1Emit.EOUT_S (by decide) (by decide)]; exact c_S
  have d_I : State.get s4 S1Emit.EOUT_I
      = FlatTCCFree.encNats (flattenString (preludeRow M str maxSize steps)) := by
    rw [hs4, dFr S1Emit.EOUT_I (by decide) (by decide)]; exact c_I
  have d_C : State.get s4 S1Emit.EOUT_C = FlatTCCFree.encNats (S1Cards.cardBlocks M) := by
    rw [hs4, dFr S1Emit.EOUT_C (by decide) (by decide)]; exact cC
  have d_sp : State.get s4 S1Emit.HSTP = List.replicate steps 1 := by
    rw [hs4, dFr S1Emit.HSTP (by decide) (by decide)]; exact c_sp
  clear_value s4
  -- M-yes
  have hev : yesBranch.eval s = stageMYes.eval s4 := by
    rw [hs4, hs3, hs2, hs1]
    unfold yesBranch ySuf1 ySuf2 ySuf3
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  rw [hev]
  exact stageMYes_run M str maxSize steps s4 d_sp d_S d_I d_C dF

/-! ## The program -/

/-- **The S1 reduction program.** -/
def s1Program : Cmd :=
  S1Parse.stagePG ;; Cmd.ifBit S1Parse.FLG yesBranch S1Cards.stageMNo

/-! ### The guard-false half of `computes` — PROVEN, end to end

Nothing here is conditional on stage C or stage M-yes: the guard-false branch
of the multiplex is `S1Cards.stageMNo`, which is built and proven. -/

/-- `s1Key` of the off-guard image is five empty registers. -/
theorem s1Key_s1No : s1Key S1Map.s1No = [[], [], [], [], []] := rfl

/-- **The guard-false branch is correct — for ANY yes branch.**

⚠ Stated over an arbitrary `yes : Cmd` on purpose. The obvious phrasing (about
`s1Program` itself) mentions `stageC`/`stageMYes` in its *statement*, so it
picks up `sorryAx` even though its proof is complete; this form is genuinely
axiom-clean, and `s1Program_computes_neg` below is its corollary. -/
theorem noBranch_computes (yes : Cmd) (M : flatTM) (str : List Nat)
    (maxSize steps : Nat) (s : State)
    (hM : State.get s S1Parse.MREG = encSyms (flattenTM M))
    (hS : State.get s S1Parse.SREG = encSyms str)
    (hg : ¬ S1Map.s1GuardB M str = true) :
    s1Extract ((S1Parse.stagePG ;; Cmd.ifBit S1Parse.FLG yes S1Cards.stageMNo).eval s)
      = s1Key (S1Map.s1Map (M, str, maxSize, steps)) := by
  obtain ⟨hF, -⟩ := S1Parse.stagePG_run M str s hM hS
  have hFlag : State.get (S1Parse.stagePG.eval s) S1Parse.FLG ≠ [1] := by
    rw [hF, if_neg hg]; exact fun h => by cases h
  have hev : (S1Parse.stagePG ;; Cmd.ifBit S1Parse.FLG yes S1Cards.stageMNo).eval s
      = S1Cards.stageMNo.eval (S1Parse.stagePG.eval s) := by
    rw [Cmd.eval_seq, Cmd.eval_ifBit_false _ _ _ _ hFlag]
  rw [S1Map.s1Map_neg M str maxSize steps hg, s1Key_s1No, hev]
  unfold s1Extract
  have hz : ∀ r : Var, r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 →
      State.get (S1Cards.stageMNo.eval (S1Parse.stagePG.eval s)) r = [] := by
    intro r hr
    rw [S1Cards.stageMNo_run _ r hr]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hz SIGMA (by decide), hz INIT (by decide), hz CARDS (by decide),
    hz FINAL (by decide), hz STEPS (by decide)]

/-- **The guard-false branch of `s1Program` is correct.** (`sorryAx` in its
axiom list comes from `s1Program` in the *statement*, not from the proof — see
`noBranch_computes`.) -/
theorem s1Program_computes_neg (M : flatTM) (str : List Nat) (maxSize steps : Nat)
    (s : State)
    (hM : State.get s S1Parse.MREG = encSyms (flattenTM M))
    (hS : State.get s S1Parse.SREG = encSyms str)
    (hg : ¬ S1Map.s1GuardB M str = true) :
    s1Extract (s1Program.eval s) = s1Key (S1Map.s1Map (M, str, maxSize, steps)) :=
  noBranch_computes yesBranch M str maxSize steps s hM hS hg

/-- **The guard-true branch is correct** — modulo the two open stage
contracts. -/
theorem s1Program_computes_pos (M : flatTM) (str : List Nat) (maxSize steps : Nat)
    (s : State)
    (hM : State.get s S1Parse.MREG = encSyms (flattenTM M))
    (hS : State.get s S1Parse.SREG = encSyms str)
    (hmx : State.get s S1Emit.HMAX = List.replicate maxSize 1)
    (hsp : State.get s S1Emit.HSTP = List.replicate steps 1)
    (hg : S1Map.s1GuardB M str = true) :
    s1Extract (s1Program.eval s) = s1Key (S1Map.s1Map (M, str, maxSize, steps)) := by
  obtain ⟨hF, -, hsig, -, hst, -, -, hph, hnt, htr⟩ := S1Parse.stagePG_run M str s hM hS
  have hFlag : State.get (S1Parse.stagePG.eval s) S1Parse.FLG = [1] := by
    rw [hF, if_pos hg]
  have hev : s1Program.eval s = yesBranch.eval (S1Parse.stagePG.eval s) := by
    unfold s1Program
    rw [Cmd.eval_seq, Cmd.eval_ifBit_true _ _ _ _ hFlag]
  obtain ⟨hV, hT, hb⟩ := (S1Map.s1GuardB_iff M str).1 hg
  -- the head-layout registers survive P + G
  have hS' : State.get (S1Parse.stagePG.eval s) S1Parse.SREG = encSyms str := by
    rw [S1Parse.stagePG_frame s S1Parse.SREG (by decide)]; exact hS
  have hmx' : State.get (S1Parse.stagePG.eval s) S1Emit.HMAX = List.replicate maxSize 1 := by
    rw [S1Parse.stagePG_frame s S1Emit.HMAX (by decide)]; exact hmx
  have hsp' : State.get (S1Parse.stagePG.eval s) S1Emit.HSTP = List.replicate steps 1 := by
    rw [S1Parse.stagePG_frame s S1Emit.HSTP (by decide)]; exact hsp
  rw [S1Map.s1Map_pos M str maxSize steps hg, hev]
  exact yesBranch_run M str maxSize steps _ hsig hst hph hnt htr hS' hmx' hsp' hV hT hb

/-- **The `computes` obligation of `S1Witness.s1_reductionLang`**, on the frozen
head layout. -/
theorem s1Program_computes (x : flatTM × List Nat × Nat × Nat) :
    s1Extract (s1Program.eval (headEncodeIn x)) = s1Key (S1Map.s1Map x) := by
  obtain ⟨M, str, maxSize, steps⟩ := x
  have hM : State.get (headEncodeIn (M, str, maxSize, steps)) S1Parse.MREG
      = encSyms (flattenTM M) := rfl
  have hS : State.get (headEncodeIn (M, str, maxSize, steps)) S1Parse.SREG
      = encSyms str := rfl
  have hmx : State.get (headEncodeIn (M, str, maxSize, steps)) S1Emit.HMAX
      = List.replicate maxSize 1 := rfl
  have hsp : State.get (headEncodeIn (M, str, maxSize, steps)) S1Emit.HSTP
      = List.replicate steps 1 := rfl
  by_cases hg : S1Map.s1GuardB M str = true
  · exact s1Program_computes_pos M str maxSize steps _ hM hS hmx hsp hg
  · exact s1Program_computes_neg M str maxSize steps _ hM hS hg

/-! ### The register frame -/

/-- **The program stays inside `s1RegBound = 48`** — modulo the two open
stages, whose `usesBelow`s are `decide`-able the moment they are concrete. -/
theorem s1Program_usesBelow : Cmd.UsesBelow s1Program s1RegBound := by
  refine ⟨S1Parse.stagePG_usesBelow_48, by decide, ?_, ?_⟩
  · exact ⟨S1Emit.stageSig_usesBelow, S1Emit.stageInit_usesBelow, stageC_usesBelow,
      S1Emit.stageFin_usesBelow, stageMYes_usesBelow⟩
  · exact Cmd.UsesBelow_mono (show 6 ≤ s1RegBound by unfold s1RegBound; omega)
      S1Cards.stageMNo_usesBelow

end S1Program
