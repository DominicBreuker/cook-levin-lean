import Complexity.NP.SAT.CookLevin.Reductions.S1Program

set_option autoImplicit false

/-! # S1, part 2 — the free witness SKELETON (`FlatSingleTMGenNP ⪯p' FlatTCC`)

**Status (2026-07-25, top-down): SKELETON.** The mathematical half is closed
(`S1Map.lean`: `s1Map_correct`, `s1Map_size_le`); the *mechanical* witness
fields are proven here; the **program** (`s1Program`) and its two run/cost
fields are the remaining work, decomposed below. This file exists so that every
downstream obligation of the honest chain head typechecks *now* — skeleton-first
(ROADMAP methodology 1/3).

## Layouts — both ends are pinned

**Input** = the FROZEN chain head `HeadLayout.headEncodeIn` (`headRegBound = 5`;
`Reductions/HeadLayout.lean`, standing architecture risk 2). Registers
`0 = []`, `1 = encSyms (flattenTM M)`, `2 = encSyms s`, `3 = 1^maxSize`,
`4 = 1^steps`. C8-5's seam must hit exactly this — C8-4 already emits it.

**Output** = `FlatTCCFree.encodeIn` **verbatim** on registers 1–5 (`s1Key`
below is its registers 1–5 in order). This is a deliberate seam choice: the
successor on the chain is the composed sound tail
`FSATSATComp.flatTCC_to_SAT_witness`, whose `encodeIn` *is*
`FlatTCCFree.encodeIn` (checked by `rfl`), so the fourth `SeamData`'s `mfc`
degenerates to a **pure scrub** — no re-encoding at all. Do not change `s1Key`
without re-checking that.

⚠ **The scrub target is 57, not 27.** The tail composite's `regBound` is
`57` (`max` over the four stacked witnesses — the HANDOFF's "final tail exit
layout"), and `FlatTCCFree.encodeIn` reads `[]` at every register `≥ 6` and at
register `0`. So the seam's `bridge` is `AgreeBelow 57`, and `mfc` must clear
register `0` **and** every scratch register this program touches in `[6, 57)`.
Keep `s1RegBound ≤ 57` if you want the scrub to stay a fixed constant-size
`Cmd`.

⚠ **Register collision (the R1 discipline of C8-4).** The output registers 1–5
OVERLAP the input registers 1–4. Every stage must build into scratch `≥ 6` and
only move into 1–5 at the very end, after the last read of the machine/input
registers.

## The program, decomposed (the build plan for the next sessions)

`s1Program` = seven stages. Registers named in `S1Witness.lean` once built.

* **P (parse).** Drain reg 1 (`encSyms (flattenTM M)`, a sentinel item stream —
  each value `v` is `1 1^v 0`) into scratch: `sig`, `tapes`, `states`, `start`,
  `|halt|`, the halt bit-stream, `|trans|`, and the transition stream (kept
  whole, re-scanned by later stages). `CliqueRelTM.readNum` is the per-item
  drain; `FlatCC_to_BinaryCC_free.sentLoop_run` is the stream-loop template.
* **G (guard).** `S1Map.s1GuardB M s`: `start < states`, `|halt| = states`, one
  pass over the transition stream checking the five length fields `= tapes` and
  the two symbol bounds `< sig`, and one pass over reg 2 checking `< sig`.
  Comparators: `leCheck_run` / `remCheck_run` (both proven). Result: one flag.
* **Σ (alphabet).** `PSg M = (sig+1)·(states+2) + 1 + 2·sig + 5` in unary —
  `unaryMulLoop_run` (proven).
* **I (init row).** `flattenString (preludeRow M s maxSize steps)` as `encNats`:
  a `forBnd` over `p < guessWidth = |s| + maxSize + steps + 3` emitting one
  number per cell — `pCell (pKindAt M s maxSize p)`, three positional cases
  (`p < |s|` → the symbol `s[p]`; `p < |s|+maxSize` → star; else blank) with the
  `p = 0` "init" variants — bracketed by the two `pDelim` cells. `s[p]` comes
  from a *sequential* scan of reg 2 (`p` is increasing), so no random access.
* **C (cards).** `encCardsIn (flattenCard <$> guessCards M)`. **The big one**
  (`Θ(|trans|·|Σ|⁴) + Θ(|Σ|⁶)` cards, 6 bare unary blocks each) — this is the
  bottom-up **card-emitter gadget** already scheduled in HANDOFF.
* **F (final).** `flattenFinal (guessFinal M)` as `encFinal`: `Θ(states·σ)`
  singleton patterns `[hCell M q b]`, emitted only for halting `q`.
* **M (multiplex).** On guard-false, emit `s1No` (five clears); else move the
  scratch results into registers 1–5.

### Three design facts that shrink the program (validated here)

1. **`emb` is the identity on cell *values*** (`GuessTableau.emb`
   `⟨c.1, _⟩`), so `embCard` is a **no-op on the flat encoding**: the emitter
   emits `cookCards M`'s numeric codes directly and never applies `emb`.
   Only the *alphabet size* changes (`Sg M → PSg M`).
2. **`M.tapes = 1` is guarded**, so every transition entry's
   `src_tape_vals` / `dst_write_vals` / `move_dirs` are singletons on the
   yes-branch. `normTrans`'s dedup key is then `(src_state, one Option Nat)` —
   a two-number comparison, not a list comparison.
3. **All cell codes are linear/product arithmetic** in `sig`/`states`
   (`tCell = b`, `hCell = (sig+1)(q+1)+b`, `bCell = (sig+1)(states+2)`,
   `pCell`'s band `= Sg M + …`), i.e. exactly what `unaryMulLoop_run` produces.
-/

namespace S1Witness

open Complexity.Lang

/-! ## The output key (= `FlatTCCFree.encodeIn` registers 1–5)

⚠ **Moved (2026-07-26).** `s1Key` / `s1Extract` / `SIGMA`…`STEPS` /
`s1RegBound` now live in `Reductions/S1Program.lean` — they are program-layout
definitions, and this file imports the program rather than the other way
round. Their injectivity, which is a *witness* fact (`decodeOut` honesty),
stays here. -/

open S1Program (s1Key s1Extract SIGMA INIT CARDS FINAL STEPS s1RegBound)

/-! ### Injectivity of the output key

The decode side of the design: `decodeOut = Function.invFun s1Key` is only
honest if `s1Key` really determines the `FlatTCC`. `encNats`/`encFinal`
injectivity are proven in `FlatTCC_to_FlatCC_free.lean`; the card stream
(`encCardsIn`, 6 bare blocks per card, no sentinels) needs its own argument —
fixed arity is what makes it decodable. -/

theorem encNats_append (xs ys : List Nat) :
    FlatTCCFree.encNats (xs ++ ys)
      = FlatTCCFree.encNats xs ++ FlatTCCFree.encNats ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      show FlatTCCFree.encNat x ++ FlatTCCFree.encNats (xs ++ ys)
        = (FlatTCCFree.encNat x ++ FlatTCCFree.encNats xs) ++ _
      rw [ih, List.append_assoc]

/-- The card stream is `encNats` of the flattened 6-nat blocks. -/
theorem encCardsIn_eq (cs : List (TCCCard Nat)) :
    FlatTCCFree.encCardsIn cs
      = FlatTCCFree.encNats (cs.flatMap FlatTCCFree.cardNats) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show FlatTCCFree.encCardIn c ++ FlatTCCFree.encCardsIn cs = _
      rw [ih, List.flatMap_cons, encNats_append]
      rfl

/-- A card is determined by its six nats. -/
theorem cardNats_injective : Function.Injective FlatTCCFree.cardNats := by
  intro a b h
  simp only [FlatTCCFree.cardNats, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases a with
  | mk ap ac =>
    cases b with
    | mk bp bc =>
      cases ap; cases ac; cases bp; cases bc
      simp_all

/-- `flatMap` of a constant-length-6 function is injective. -/
theorem flatMap_cardNats_injective :
    Function.Injective (fun cs : List (TCCCard Nat) => cs.flatMap FlatTCCFree.cardNats) := by
  intro cs
  induction cs with
  | nil =>
      intro ds h
      cases ds with
      | nil => rfl
      | cons d ds =>
          exfalso
          have hlen := congrArg List.length h
          simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil,
            List.length_append] at hlen
          have : (FlatTCCFree.cardNats d).length = 6 := rfl
          omega
  | cons c cs ih =>
      intro ds h
      cases ds with
      | nil =>
          exfalso
          have hlen := congrArg List.length h
          simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil,
            List.length_append] at hlen
          have : (FlatTCCFree.cardNats c).length = 6 := rfl
          omega
      | cons d ds =>
          simp only [List.flatMap_cons] at h
          have hc : (FlatTCCFree.cardNats c).length = (FlatTCCFree.cardNats d).length := rfl
          obtain ⟨h1, h2⟩ := (List.append_inj h hc)
          rw [cardNats_injective h1, ih h2]

theorem encCardsIn_injective : Function.Injective FlatTCCFree.encCardsIn := by
  intro cs ds h
  rw [encCardsIn_eq, encCardsIn_eq] at h
  exact flatMap_cardNats_injective (FlatTCCFree.encNats_injective h)

/-- **The output layout is decodable.** -/
theorem s1Key_injective : Function.Injective s1Key := by
  intro a b h
  simp only [S1Program.s1Key, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  cases a with
  | mk aS ai ac af ast =>
    cases b with
    | mk bS bi bc bf bst =>
      simp only at h1 h2 h3 h4 h5
      have e1 : aS = bS := CliqueRelTM.replicate_one_eq_iff.mp h1
      have e5 : ast = bst := CliqueRelTM.replicate_one_eq_iff.mp h5
      rw [e1, e5, FlatTCCFree.encNats_injective h2, encCardsIn_injective h3,
        FlatTCCFree.encFinal_injective h4]

/-! ## The input-encoding size bound

`PolyTimeComputableLang.encodeIn_size` wants
`State.size (headEncodeIn x) ≤ encBound (encodable.size x)` with `encBound`
polynomial. **This is exactly the field that forced the 2026-07-25 correction of
`encodable FlatTM`** (`Definitions.lean`): under the old flat-`5`-per-entry
measure it was *unsatisfiable* (`probes/S1SizeGapProbe.lean`). The reduction to
one arithmetic fact is done here; that fact is a bottom-up bite. -/

/-- The sentinel item stream's length: one `1`, `v` ones, one `0` per value. -/
theorem encSyms_length (l : List Nat) :
    (HeadLayout.encSyms l).length = l.sum + 2 * l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l v ih =>
      rw [HeadLayout.encSyms_snoc]
      simp only [List.length_append, List.length_cons, List.length_replicate,
        List.length_nil, List.sum_append, List.sum_cons, List.sum_nil, ih]
      omega

/-- `encodable.size` of a `List Nat` is `sum + length`. -/
theorem list_nat_size_eq (l : List Nat) : encodable.size l = l.sum + l.length := by
  show l.foldl (fun acc x => acc + encodable.size x + 1) 0 = _
  have h : ∀ (m : List Nat) (a : Nat),
      m.foldl (fun acc x => acc + encodable.size x + 1) a = a + m.sum + m.length := by
    intro m
    induction m with
    | nil => intro a; simp
    | cons y ys ih =>
        intro a
        rw [List.foldl_cons, ih]
        show a + encodable.size y + 1 + ys.sum + ys.length = a + (y + ys.sum) + (ys.length + 1)
        have : encodable.size y = y := rfl
        omega
  simpa using h l 0

/-- The item stream costs at most twice the list's own `encodable.size`. -/
theorem encSyms_length_le_size (l : List Nat) :
    (HeadLayout.encSyms l).length ≤ 2 * encodable.size l := by
  rw [encSyms_length, list_nat_size_eq]; omega

/-! ### The machine stream is linear in the honest machine size

⚠ **The additive `+ 3` is not slack — it is forced (2026-07-26).** The version
of this lemma stated before that session, `size (flattenTM M) ≤ 3 * size M`, is
**FALSE**: the trivial machine (`sig = tapes = states = start = 0`,
`halt = trans = []`) has `size M = 1` but `flattenTM M = [0,0,0,0,0,0]`, whose
`encodable.size` is `6`. `flattenTM` always writes six header cells, and the
header of a machine of size `1` cannot be paid for multiplicatively. The bound
below is TIGHT at that machine (`6 = 3·1 + 3`) and at
`trans = [⟨0,[],0,[],[]⟩]` (`12 = 3·3 + 3`). `probes/S1SizeGapProbe.lean` §3
carries all three witnesses — **any future re-statement must keep an additive
term.** (The old probe only ever evaluated the claim on machines with a
non-degenerate header, which is why it printed `true`.) -/

private theorem nat_size_append (a b : List Nat) :
    encodable.size (a ++ b) = encodable.size a + encodable.size b := by
  rw [list_nat_size_eq, list_nat_size_eq, list_nat_size_eq, List.sum_append,
    List.length_append]
  omega

/-- `encodable.size` of a list, as the sum of its elements' charges. -/
private theorem list_size_map_sum {α : Type} [encodable α] (l : List α) :
    encodable.size l = (l.map (fun x => encodable.size x + 1)).sum := by
  show l.foldl (fun acc x => acc + encodable.size x + 1) 0 = _
  have h : ∀ (m : List α) (a : Nat),
      m.foldl (fun acc x => acc + encodable.size x + 1) a
        = a + (m.map (fun x => encodable.size x + 1)).sum := by
    intro m
    induction m with
    | nil => intro a; simp
    | cons y ys ih =>
        intro a
        rw [List.foldl_cons, ih]
        simp only [List.map_cons, List.sum_cons]
        omega
  simpa using h l 0

private theorem list_size_cons {α : Type} [encodable α] (a : α) (l : List α) :
    encodable.size (a :: l) = encodable.size a + 1 + encodable.size l := by
  rw [list_size_map_sum (a :: l), list_size_map_sum l]
  simp only [List.map_cons, List.sum_cons]

private theorem nat_size_flatMap {α : Type} (f : α → List Nat) (l : List α) :
    encodable.size (l.flatMap f) = (l.map (fun a => encodable.size (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.flatMap_cons, nat_size_append, ih]
      simp only [List.map_cons, List.sum_cons]

/-- One `Option Nat` costs at most twice its charge, *including* its own item
slot — the shape the entry bound needs. -/
private theorem opts_size_le : ∀ l : List (Option Nat),
    encodable.size (S1Parse.optsFlat l) + l.length ≤ 2 * encodable.size l
  | [] => by exact Nat.zero_le _
  | o :: l => by
      have ih := opts_size_le l
      have hflat : S1Parse.optsFlat (o :: l)
          = HeadLayout.encOptN o ++ S1Parse.optsFlat l := List.flatMap_cons ..
      have hb : encodable.size (HeadLayout.encOptN o) + 1
          ≤ 2 * (encodable.size o + 1) := by
        cases o with
        | none =>
            show encodable.size ([0] : List Nat) + 1 ≤ 2 * (0 + 1)
            rw [list_nat_size_eq]; simp
        | some v =>
            have hv : encodable.size (some v : Option Nat) = v + 1 := rfl
            show encodable.size ([1, v] : List Nat) + 1 ≤ _
            rw [list_nat_size_eq, hv]; simp; omega
      rw [hflat, nat_size_append, list_size_cons, List.length_cons]
      omega

private theorem moves_size_le : ∀ l : List TMMove,
    encodable.size (l.map HeadLayout.encMoveN) + l.length ≤ 2 * encodable.size l
  | [] => by exact Nat.zero_le _
  | m :: l => by
      have ih := moves_size_le l
      have hm : encodable.size (m :: l) = 2 + encodable.size l := by
        rw [list_size_cons]; cases m <;> rfl
      have hs : encodable.size ((m :: l).map HeadLayout.encMoveN)
          = HeadLayout.encMoveN m + 1 + encodable.size (l.map HeadLayout.encMoveN) := by
        rw [List.map_cons, list_size_cons]; rfl
      have hle : HeadLayout.encMoveN m ≤ 2 := by cases m <;> decide
      rw [hs, hm, List.length_cons]
      omega

private theorem halt_size_le : ∀ l : List Bool,
    encodable.size (l.map (fun b => if b then 1 else 0)) + l.length
      ≤ 2 * encodable.size l
  | [] => by exact Nat.zero_le _
  | b :: l => by
      have ih := halt_size_le l
      have hs : encodable.size ((b :: l).map (fun b => if b then 1 else 0))
          = (if b then 1 else 0) + 1
            + encodable.size (l.map (fun b => if b then 1 else 0)) := by
        rw [List.map_cons, list_size_cons]; rfl
      have hm : encodable.size (b :: l) = (if b then 1 else 0) + 1 + encodable.size l := by
        rw [list_size_cons]; cases b <;> rfl
      rw [hs, hm, List.length_cons]
      cases b <;> simp <;> omega

private theorem entry_size_le (e : FlatTMTransEntry) :
    encodable.size (HeadLayout.flattenEntry e) ≤ 2 * encodable.size e + 3 := by
  have h1 := opts_size_le e.src_tape_vals
  have h2 := opts_size_le e.dst_write_vals
  have h3 := moves_size_le e.move_dirs
  have hsz : encodable.size e
      = encodable.size e.src_state + encodable.size e.src_tape_vals
        + encodable.size e.dst_state + encodable.size e.dst_write_vals
        + encodable.size e.move_dirs + 1 := rfl
  have hst : encodable.size e.src_state = e.src_state := rfl
  have hdt : encodable.size e.dst_state = e.dst_state := rfl
  have hA : encodable.size ([e.src_state, e.src_tape_vals.length] : List Nat)
      = e.src_state + e.src_tape_vals.length + 2 := by
    rw [list_nat_size_eq]; simp
  have hB : encodable.size ([e.dst_state, e.dst_write_vals.length] : List Nat)
      = e.dst_state + e.dst_write_vals.length + 2 := by
    rw [list_nat_size_eq]; simp
  have hC : encodable.size ([e.move_dirs.length] : List Nat)
      = e.move_dirs.length + 1 := by
    rw [list_nat_size_eq]; simp
  rw [S1Parse.flattenEntry_eq, nat_size_append, nat_size_append, nat_size_append,
    nat_size_append, nat_size_append, hA, hB, hC]
  omega

private theorem length_eq_sum_ones {α : Type} (l : List α) :
    l.length = (l.map (fun _ => 1)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

private theorem mul_sum_map {α : Type} (c : Nat) (f : α → Nat) (l : List α) :
    c * (l.map f).sum = (l.map (fun a => c * f a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Nat.mul_add, ih]

private theorem trans_sum_le : ∀ l : List FlatTMTransEntry,
    (l.map (fun e => encodable.size (HeadLayout.flattenEntry e))).sum
        + (l.map (fun _ : FlatTMTransEntry => 1)).sum
      ≤ (l.map (fun e => 3 * (encodable.size e + 1))).sum
  | [] => by simp
  | a :: l => by
      have ih := trans_sum_le l
      have ha := entry_size_le a
      have hge : 1 ≤ encodable.size a := by
        show 1 ≤ encodable.size a.src_state + _ + _ + _ + _ + 1
        omega
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **The flattened machine stream is linear in the machine's honest
`encodable.size`** — with a forced additive constant, see the section note. -/
theorem flattenTM_size_le (M : FlatTM) :
    encodable.size (HeadLayout.flattenTM M) ≤ 3 * encodable.size M + 3 := by
  have hH := halt_size_le M.halt
  have hT : encodable.size (S1Parse.transFlat M) + M.trans.length
      ≤ 3 * encodable.size M.trans := by
    unfold S1Parse.transFlat
    rw [nat_size_flatMap, list_size_map_sum M.trans, length_eq_sum_ones M.trans,
      mul_sum_map 3 (fun e => encodable.size e + 1) M.trans]
    exact trans_sum_le M.trans
  have hA : encodable.size ([M.sig, M.tapes, M.states, M.start, M.halt.length] : List Nat)
      = M.sig + M.tapes + M.states + M.start + M.halt.length + 5 := by
    rw [list_nat_size_eq]; simp; omega
  have hB : encodable.size ([M.trans.length] : List Nat) = M.trans.length + 1 := by
    rw [list_nat_size_eq]; simp
  have hM : encodable.size M
      = M.sig + M.tapes + M.states + M.start
        + encodable.size M.halt + encodable.size M.trans + 1 := rfl
  rw [S1Parse.flattenTM_eq, nat_size_append, nat_size_append, nat_size_append, hA, hB]
  omega

/-- The frozen head layout's total register content is linear in the instance
size — `encodeIn_size` with `encBound n = 8·n + 4`. -/
theorem headEncodeIn_size_le (x : flatTM × List Nat × Nat × Nat) :
    State.size (HeadLayout.headEncodeIn x) ≤ 8 * encodable.size x + 4 := by
  obtain ⟨M, s, maxSize, steps⟩ := x
  have hM := le_trans (encSyms_length_le_size (HeadLayout.flattenTM M))
    (Nat.mul_le_mul_left 2 (flattenTM_size_le M))
  have hs := encSyms_length_le_size s
  have hprod : encodable.size ((M, s, maxSize, steps) : flatTM × List Nat × Nat × Nat)
      = encodable.size M + (encodable.size s + (maxSize + steps + 1) + 1) + 1 := rfl
  show State.size [[], HeadLayout.encSyms (HeadLayout.flattenTM M),
    HeadLayout.encSyms s, List.replicate maxSize 1, List.replicate steps 1] ≤ _
  simp only [State.size, List.map_cons, List.map_nil, List.foldr_cons,
    List.foldr_nil, List.length_replicate, List.length_nil]
  omega

/-! ## The program — ASSEMBLED (`Reductions/S1Program.lean`)

`S1Program.s1Program = stagePG ;; ifBit FLG yesBranch stageMNo`. Five of its
seven stages are built and proven; **stage C and stage M-yes** are the only
`sorry`s left in it, and the whole guard-false branch of `computes` is proven
end to end (`S1Program.s1Program_computes_neg`). What remains open *in this
file* is the cost ladder. -/

/-! ## The witness

⚠ **The witness is built in two steps on purpose (2026-07-27, top-down).**
`s1WitnessOf` takes the program as a PARAMETER together with the three
contracts it has to meet, and `s1_reductionLang` is its instantiation at
`S1Program.s1Program`. That is the project's skeleton-phase discipline
applied to the witness itself: every downstream construction (both seams, the
composed chain, `NPhard'' SAT`) can be stated over `s1WitnessOf` and is then
**axiom-clean**, so `#print axioms` keeps distinguishing "this interface is
validated" from "stage C is still a placeholder". Do not inline
`s1WitnessOf` back into `s1_reductionLang`.

The three contracts are exactly the remaining S1 obligations:

1. `hcomputes` — `S1Program.s1Program_computes` (open only through
   `stageC_run`);
2. `huses` — `S1Program.s1Program_usesBelow` (open only through
   `stageC_usesBelow`);
3. `hcost` — `s1Program_cost_le` below, the cost ladder, **still open**.
-/

private instance : Nonempty FlatTCC := ⟨S1Map.s1No⟩

/-- **The S1 free reduction witness, over an arbitrary program meeting the
three S1 contracts.** Every other field is discharged from a proven lemma of
this file / `S1Map`. -/
noncomputable def s1WitnessOf (c : Cmd)
    (hcomputes : ∀ x : flatTM × List Nat × Nat × Nat,
      s1Extract (c.eval (HeadLayout.headEncodeIn x)) = s1Key (S1Map.s1Map x))
    (huses : Cmd.UsesBelow c s1RegBound)
    (hcost : ∀ x : flatTM × List Nat × Nat × Nat,
      c.cost (HeadLayout.headEncodeIn x) ≤ S1Map.s1Bound (encodable.size x)) :
    PolyTimeComputableLang S1Map.s1Map where
  c := c
  encodeIn := HeadLayout.headEncodeIn
  decodeOut := fun s => Function.invFun s1Key (s1Extract s)
  -- The cost ceiling: the card stream dominates, `Θ(|trans|·|Σ|⁴)` blocks of
  -- unary cells, each emitted by a quadratic-in-its-length loop. Degree 10
  -- matches `S1Map.s1Bound` (the output-size ceiling) with room to spare;
  -- tighten only if the built program refuses it.
  cost_bound := fun n => S1Map.s1Bound n
  cost_bound_poly := S1Map.s1Bound_poly
  cost_bound_mono := S1Map.s1Bound_mono
  encBound := fun n => 8 * n + 4
  encBound_poly :=
    inOPoly_add (inOPoly_mul (inOPoly_const 8) inOPoly_id) (inOPoly_const 4)
  encBound_mono := fun a b h => Nat.add_le_add_right (Nat.mul_le_mul_left 8 h) 4
  encodeIn_size := headEncodeIn_size_le
  computes := fun x => by
    rw [hcomputes x]
    exact Function.leftInverse_invFun s1Key_injective _
  cost_le := hcost
  output_size_le := S1Map.s1Map_size_le
  enc_bit := HeadLayout.headEncodeIn_bitState
  regBound := s1RegBound
  usesBelow := huses
  width_le := fun x => by
    obtain ⟨M, s, maxSize, steps⟩ := x
    show (HeadLayout.headEncodeIn (M, s, maxSize, steps)).length ≤ s1RegBound
    simp [HeadLayout.headEncodeIn, S1Program.s1RegBound]
  decode_agree := fun x m => by
    have hagree : AgreeBelow s1RegBound
        (HeadLayout.headEncodeIn x ++ List.replicate m []) (HeadLayout.headEncodeIn x) :=
      fun r _ => State.get_append_replicate_nil _ _ _
    have h := Cmd.eval_agree c s1RegBound huses hagree
    show Function.invFun s1Key (s1Extract _) = Function.invFun s1Key (s1Extract _)
    unfold S1Program.s1Extract
    rw [h SIGMA (by decide), h INIT (by decide), h CARDS (by decide),
      h FINAL (by decide), h STEPS (by decide)]

/-- **OPEN — the whole-program cost ladder**, the LAST item of the S1 build
plan and the only S1 obligation that is not a program contract.

Everything a bottom-up session needs is here in the statement: bound the seven
stages' `Cmd.cost` on the frozen head layout by `S1Map.s1Bound` (the *same*
free polynomial that already carries `output_size_le`, degree 10 — raise it
rather than fight for a degree, its only constraint is that it keeps
dominating `S1Map.s1Map_size_le`). Measured leaves: P+G is cubic
(`probes/S1ParseProbe.lean`), `S1Emit.emitBlk_cost ≤ 3 + 5v + v²` is the
emitter leaf, `Cmd.cost_forBnd_le` sits above each loop, and
`preludeBlocks` is ~96% of the emitted output
(`probes/S1CardEmitProbe.lean` §3), so budget the program as that family's
cost plus a constant factor. -/
theorem s1Program_cost_le (x : flatTM × List Nat × Nat × Nat) :
    S1Program.s1Program.cost (HeadLayout.headEncodeIn x)
      ≤ S1Map.s1Bound (encodable.size x) := by
  sorry

/-- **The S1 free reduction witness** — `s1WitnessOf` at the real program.
Its `computes`/`usesBelow` are conditional only on stage C, its `cost_le`
only on `s1Program_cost_le`. -/
noncomputable def s1_reductionLang : PolyTimeComputableLang S1Map.s1Map :=
  s1WitnessOf S1Program.s1Program S1Program.s1Program_computes
    S1Program.s1Program_usesBelow s1Program_cost_le

/-- **The honest chain head — SKELETON (`sorry`-backed via `s1Program`).**
Once `s1Program` lands this is the real `FlatSingleTMGenNP ⪯p' FlatTCC`, and
`Q ⪯p' FlatSingleTMGenNP ⪯p' FlatTCC ⪯p' SAT` closes `NPhard'' SAT`. -/
theorem s1_reducesPolyMO' :
    reducesPolyMO' FlatSingleTMGenNP FlatTCC.FlatTCCLang :=
  reducesPolyMO'_of_langFree s1_reductionLang S1Map.s1Map_correct

end S1Witness
