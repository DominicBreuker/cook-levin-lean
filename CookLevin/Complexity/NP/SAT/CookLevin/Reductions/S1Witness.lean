import Complexity.NP.SAT.CookLevin.Reductions.S1Map
import Complexity.NP.SAT.CookLevin.Reductions.HeadLayout
import Complexity.NP.SAT.CookLevin.Reductions.FlatTCC_to_FlatCC_free

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

/-! ## The output key (= `FlatTCCFree.encodeIn` registers 1–5) -/

/-- The S1 program's output registers, in order: the successor witness's own
input layout. -/
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
  simp only [s1Key, List.cons.injEq, and_true] at h
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

/-- **BOTTOM-UP BITE (open).** The flattened machine stream is linear in the
machine's honest `encodable.size`.

Every piece of `HeadLayout.flattenTM M` is a data field of `M` (or a length of
one), and `encOptN` charges `v + 2` per `Option Nat` whose `encodable.size` is
`v + 1`; so the constant `3` has slack. The proof is a routine — but not
short — chain: turn the two `foldl (fun a e => a ++ f e)` accumulators into
`flatMap` (the private `HeadLayout.foldl_append_acc` is exactly this), push
`encodable.size` through `++` and `flatMap`, then bound each entry field
against `encodable FlatTMTransEntry`. Numerically checked in
`probes/S1SizeGapProbe.lean`. -/
theorem flattenTM_size_le (M : FlatTM) :
    encodable.size (HeadLayout.flattenTM M) ≤ 3 * encodable.size M := by
  sorry

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

/-! ## The program — NOT YET BUILT

`def` + `sorry` (project policy: never `axiom`). The stages are specified in
the module docstring; the run and cost fields below are the two obligations
this placeholder carries. -/

/-- **OPEN (the S1 critical path).** The `Cmd` emitting `S1Map.s1Map` from the
frozen head layout. See the module docstring for the seven-stage
decomposition. -/
def s1Program : Cmd := sorry

/-- Provisional program frame. The final value is whatever the built program
needs; it must be `≥ 6` (output 1–5 plus scratch). Keeping it `≤ 57` (the
tail composite's frame) keeps the fourth seam's `mfc` a constant-size scrub —
see the module docstring. -/
def s1RegBound : Nat := 48

/-! ## The witness -/

private instance : Nonempty FlatTCC := ⟨S1Map.s1No⟩

/-- **The S1 free reduction witness — SKELETON.** Mechanical fields proven;
`computes` / `cost_le` / `usesBelow` wait on `s1Program`. -/
noncomputable def s1_reductionLang : PolyTimeComputableLang S1Map.s1Map where
  c := s1Program
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
  computes := by
    -- OPEN: `s1Extract (s1Program.eval (headEncodeIn x)) = s1Key (s1Map x)`,
    -- then `Function.leftInverse_invFun s1Key_injective`.
    sorry
  cost_le := by
    -- OPEN: the cost ladder over the seven stages.
    sorry
  output_size_le := S1Map.s1Map_size_le
  enc_bit := HeadLayout.headEncodeIn_bitState
  regBound := s1RegBound
  usesBelow := by
    -- OPEN: `decide`-able once `s1Program` is a concrete `Cmd`.
    sorry
  width_le := fun x => by
    obtain ⟨M, s, maxSize, steps⟩ := x
    show (HeadLayout.headEncodeIn (M, s, maxSize, steps)).length ≤ s1RegBound
    simp [HeadLayout.headEncodeIn, s1RegBound]
  decode_agree := by
    -- OPEN: `Cmd.eval_agree` on the padded state (the template is
    -- `FlatTCCFree.flatTCC_reductionLang.decode_agree`); needs `usesBelow`.
    sorry

/-- **The honest chain head — SKELETON (`sorry`-backed via `s1Program`).**
Once `s1Program` lands this is the real `FlatSingleTMGenNP ⪯p' FlatTCC`, and
`Q ⪯p' FlatSingleTMGenNP ⪯p' FlatTCC ⪯p' SAT` closes `NPhard'' SAT`. -/
theorem s1_reducesPolyMO' :
    reducesPolyMO' FlatSingleTMGenNP FlatTCC.FlatTCCLang :=
  reducesPolyMO'_of_langFree s1_reductionLang S1Map.s1Map_correct

end S1Witness
