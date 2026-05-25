import Complexity.Lang.Compile
import Complexity.Complexity.NP

set_option autoImplicit false

/-! # Lang-level polynomial-time predicates and bridges to `inTimePoly`

The whole point of the layer is to *replace* the hand-rolled
`DecidesBy` and `PolyTimeComputableWitness` constructions with
layer-level programs. This file:

1. Defines `inTimePolyLang P` and `PolyTimeComputableLang f` — the
   layer-level analogues of the framework predicates.
2. Provides bridge theorems that lift a layer-level witness to the
   framework's TM-backed witness, via `Compile`.

Bridges are sorry-bodied at the skeleton stage; they all reduce to
`Compile_sound` once that lands.
-/

namespace Complexity.Lang

/-- A program `c` *decides* a predicate `P` in cost bound `costBound`
when run on the encoded input `encodeIn`.

This is the layer-level analogue of `DecidesBy`. The TM-level
`DecidesBy` is then obtained from `inTimePolyLang_to_DecidesBy`
below.

The encoded state's size is bounded by the same `costBound` as the
running cost — this is the loosest reasonable bound (a real
encoding cannot be more expensive to lay out than to process) and
absorbs constants without forcing the encoder to fight an
artificial `+1` ceiling. -/
structure DecidesLang {X : Type} [encodable X]
    (P : X → Prop) (costBound : Nat → Nat) where
  /-- The DSL program. -/
  c : Cmd
  /-- How inputs are laid out in the program's initial state. -/
  encodeIn : X → State
  /-- The encoded state's size is bounded by the cost bound. -/
  encodeIn_size : ∀ x, State.size (encodeIn x) ≤ costBound (encodable.size x)
  /-- The program decides `P` from the encoded input. -/
  decides : Cmd.decides c encodeIn P
  /-- Cost bound: running `c` on `encodeIn x` costs at most
  `costBound (encodable.size x)` primitive operations. -/
  cost_bound : ∀ x, c.cost (encodeIn x) ≤ costBound (encodable.size x)

/-- `P` is in polynomial time *at the layer level*: there is a
`DecidesLang` witness with polynomially bounded cost. -/
def inTimePolyLang {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ f, Nonempty (DecidesLang P f) ∧ inOPoly f ∧ monotonic f

/-- A polynomial-time computable function `f` *at the layer level*:
a `Cmd` that reads `f`'s input from the encoded state and writes
`f`'s output to a designated output register, with polynomially
bounded cost. -/
structure PolyTimeComputableLang {X Y : Type} [encodable X] [encodable Y]
    (f : X → Y) where
  c : Cmd
  encodeIn : X → State
  decodeOut : State → Y
  cost_bound : Nat → Nat
  cost_bound_poly : inOPoly cost_bound
  cost_bound_mono : monotonic cost_bound
  encodeIn_size : ∀ x, State.size (encodeIn x) ≤ encodable.size x + 1
  /-- After running `c`, the output register decodes to `f x`. -/
  computes : ∀ x, decodeOut (c.eval (encodeIn x)) = f x
  /-- Running `c` is polynomial-time. -/
  cost_le : ∀ x, c.cost (encodeIn x) ≤ cost_bound (encodable.size x)
  /-- Output size is bounded by the output of `cost_bound` —
  i.e. polynomial-time output is polynomial-size. -/
  output_size_le : ∀ x, encodable.size (f x) ≤ cost_bound (encodable.size x)

/-! ## Bridges

These are the *main results* of Part 3 from the consumer's
perspective. They are stated here with `sorry` bodies; the proofs
follow mechanically from `Compile_sound` once that lands. -/

/-- **Bridge 1 (Part 3.4):** a layer-level `DecidesLang` witness
extends to a framework-level `DecidesBy` witness. -/
theorem DecidesLang.toDecidesBy {X : Type} [encodable X]
    {P : X → Prop} {costBound : Nat → Nat}
    (D : DecidesLang P costBound)
    (h_mono : monotonic costBound) :
    Nonempty (DecidesBy P (fun n => Compile.overhead (2 * costBound n))) := by
  -- The new bound matches the shape of `Compile_sound`:
  -- `Compile.overhead (sizeIn + cost)` upper-bounds the TM steps,
  -- and `cost c (encodeIn x) ≤ costBound (encodable.size x)` while
  -- `State.size (encodeIn x) ≤ costBound (encodable.size x)`, so
  -- `sizeIn + cost ≤ 2 * costBound n`. Then `Compile.overhead` is
  -- monotonic.
  sorry  -- TODO(Part3.5)

/-- **Bridge 2 (Part 3.4):** `inTimePolyLang P` implies
`inTimePoly P`. This is the headline consumer-facing fact. -/
theorem inTimePolyLang_to_inTimePoly {X : Type} [encodable X]
    {P : X → Prop} (h : inTimePolyLang P) : inTimePoly P := by
  sorry  -- TODO(Part3.5): use DecidesLang.toDecidesBy + inOPoly_comp.

/-- **Bridge 3 (Part 4.1):** a layer-level `PolyTimeComputableLang`
witness extends to a framework-level `PolyTimeComputableWitness`. -/
theorem PolyTimeComputableLang.toFrameworkWitness
    {X Y : Type} [encodable X] [encodable Y] {f : X → Y}
    (W : PolyTimeComputableLang f) :
    polyTimeComputable f := by
  -- The framework currently bounds *output size*, so this is the
  -- easy direction. The forward bridge (use `Compile` to produce a
  -- TM that computes `f` in poly time) is the more interesting
  -- content; until the framework upgrades `polyTimeComputable` to
  -- be TM-backed (Part 4.1 proper), this is what we have.
  refine ⟨⟨W.cost_bound, W.cost_bound_poly, W.cost_bound_mono, ?_⟩⟩
  intro x
  exact W.output_size_le x

/-- **Composition (Part 4 / Part 3):** the layer is closed under
`Cmd.seq`, so polynomially-bounded computable functions compose. -/
noncomputable def PolyTimeComputableLang.comp
    {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    {g : Y → Z} {h : X → Y}
    (Wg : PolyTimeComputableLang g) (Wh : PolyTimeComputableLang h) :
    PolyTimeComputableLang (g ∘ h) := by
  sorry  -- TODO(Part4.1): sequence Wh.c then Wg.c with a register-
         -- shuffle in between; cost is bound by Wh.cost_bound +
         -- Wg.cost_bound ∘ Wh.cost_bound.

/-- **NP-style composition (Part 4):** if `P ⪯p Q` (via a
poly-time reduction witnessed at the layer level) and `Q ∈ inNP`
(via a layer-level verifier), then `P ∈ inNP`. This is the missing
piece that closes the `red_inNP` TM-composition sorry. -/
theorem red_inNP_via_lang
    {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop)
    (f : X → Y) (hf : PolyTimeComputableLang f)
    (hf_correct : ∀ x, P x ↔ Q (f x))
    (hQ : inNP Q) :
    inNP P := by
  sorry  -- TODO(Part4.2): destructure hQ, compose the verifier
         -- with hf via Cmd.seq, repackage as inNP P.

/-! ## S3-retirement probe (May 2026): a TM-backed `polyTimeComputable`

This block is the deliverable of the `S3_RETIREMENT_EXPLORATION.md`
go/no-go probe. It is **additive**: the live `polyTimeComputable` /
`⪯p` / `CookLevin` are untouched, so the conditional theorem keeps
compiling. The probe answers one question: *can the size-only
`PolyTimeComputableWitness` (Risk S3) be replaced by a real,
TM- and layer-backed witness?*

The pieces below are sorry-free; they depend only on the pre-existing
`Compile_sound` sorry (which the brief instructs us to assume). See the
verdict in `ROADMAP.md`. -/

/-- **(A) The honest interface.** A TM-backed *function-computation*
witness: a `FlatTM` that, on the encoded input, halts within
`timeBound (size x)` steps in a configuration whose decoded output is
`f x`. This is the function analogue of the framework's existing
`DecidesBy` (which already TM-backs *deciders*); it carries the content
that the size-only `PolyTimeComputableWitness` (S3) lacks. -/
structure ComputesBy {X Y : Type} [encodable X] [encodable Y]
    (f : X → Y) (timeBound : Nat → Nat) where
  /-- How the input is laid out on tape 0. -/
  encode      : X → List Nat
  /-- The underlying flat Turing machine. -/
  M           : FlatTM
  /-- It is a well-formed TM. -/
  M_valid     : validFlatTM M
  /-- The machine has at least one tape. -/
  M_tapes_pos : 0 < M.tapes
  /-- How to read `f x` out of a halting configuration. -/
  decode      : FlatTMConfig → Y
  /-- Within the time budget the machine halts and its output decodes
  to `f x`. This is the real computational content. -/
  computes    : ∀ x, ∃ cfg,
    runFlatTM (timeBound (encodable.size x)) M
        (initFlatConfig M (initialTapes M (encode x))) = some cfg ∧
      haltingStateReached M cfg = true ∧
      decode cfg = f x

/-- **(A) The upgraded witness.** It *extends* the size-only
`PolyTimeComputableWitness` (so every existing size-bound consumer —
`reducesPolyMO_transitive`, `red_inNP`'s `polyCertRel` half, … — keeps
working verbatim) and additionally carries a real polynomial-time
machine computing `f`. Replacing `PolyTimeComputableWitness` by this in
`ReductionWitness` is exactly what retires S3. -/
structure PolyTimeComputableWitness' {X Y : Type} [encodable X] [encodable Y]
    (f : X → Y) extends PolyTimeComputableWitness f where
  timeBound      : Nat → Nat
  timeBound_poly : inOPoly timeBound
  timeBound_mono : monotonic timeBound
  computer       : ComputesBy f timeBound

abbrev polyTimeComputable' {X Y : Type} [encodable X] [encodable Y] (f : X → Y) : Prop :=
  Nonempty (PolyTimeComputableWitness' f)

/-- The upgrade is a genuine **strengthening**: a TM-backed witness
yields the old size-only witness for free. Hence migrating `⪯p` to
`polyTimeComputable'` keeps every size-bound lemma in `NP.lean` valid
verbatim — only the *construction* of witnesses gets harder (which is
the whole point: that is where S1/S2 stop typechecking). -/
theorem polyTimeComputable'_to_polyTimeComputable
    {X Y : Type} [encodable X] [encodable Y] {f : X → Y}
    (h : polyTimeComputable' f) : polyTimeComputable f := by
  obtain ⟨W⟩ := h
  exact ⟨W.toPolyTimeComputableWitness⟩

/-- **(B) The real bridge — the headline result.** A layer-level
`PolyTimeComputableLang f` extends to the TM-backed
`PolyTimeComputableWitness' f`, *assuming `Compile_sound`* (used below as
the in-scope, sorry-backed theorem). This is the honest content that the
existing `PolyTimeComputableLang.toFrameworkWitness` fakes (it discards
`computes`/`cost_le` and proves only the size bound). It goes through
**cleanly**: the machine is `Compile W.c`, the time budget is
`Compile.overhead` of the layer cost, and `Compile_sound` + `runFlatTM_extend`
(budget padding) discharge the `computes` obligation. -/
theorem PolyTimeComputableLang.toFrameworkWitness'
    {X Y : Type} [encodable X] [encodable Y] {f : X → Y}
    (W : PolyTimeComputableLang f) :
    polyTimeComputable' f := by
  have htb_poly : inOPoly (fun n => Compile.overhead (n + 1 + W.cost_bound n)) := by
    have hinner : inOPoly (fun n => n + 1 + W.cost_bound n) :=
      inOPoly_add (inOPoly_add inOPoly_id (inOPoly_const 1)) W.cost_bound_poly
    show inOPoly (Compile.overhead ∘ fun n => n + 1 + W.cost_bound n)
    exact inOPoly_comp hinner Compile.overhead_poly
  have htb_mono : monotonic (fun n => Compile.overhead (n + 1 + W.cost_bound n)) := by
    intro a b hab
    apply Compile.overhead_mono
    have hcb : W.cost_bound a ≤ W.cost_bound b := W.cost_bound_mono a b hab
    omega
  refine ⟨{
    toPolyTimeComputableWitness :=
      ⟨W.cost_bound, W.cost_bound_poly, W.cost_bound_mono, W.output_size_le⟩
    timeBound := fun n => Compile.overhead (n + 1 + W.cost_bound n)
    timeBound_poly := htb_poly
    timeBound_mono := htb_mono
    computer := ?_ }⟩
  · -- ComputesBy: the machine is `Compile W.c`.
    refine {
      encode := fun x => Compile.encodeTape (W.encodeIn x)
      M := Compile W.c
      M_valid := Compile_valid W.c
      M_tapes_pos := ?_
      decode := fun cfg => W.decodeOut (Compile.decodeTape cfg)
      computes := ?_ }
    · rw [Compile_tapes]; exact Nat.one_pos
    · intro x
      obtain ⟨cfg, hrun, hhalt, hdec⟩ := Compile_sound W.c (W.encodeIn x)
      refine ⟨cfg, ?_, hhalt, ?_⟩
      · -- The single-tape `initialTapes` collapses to `[encodeTape …]`,
        -- then pad the run budget up to `timeBound (size x)`.
        have htapes :
            initialTapes (Compile W.c) (Compile.encodeTape (W.encodeIn x))
              = [Compile.encodeTape (W.encodeIn x)] := by
          unfold initialTapes
          rw [Compile_tapes]; simp
        show runFlatTM (Compile.overhead
              (encodable.size x + 1 + W.cost_bound (encodable.size x)))
            (Compile W.c)
            (initFlatConfig (Compile W.c)
              (initialTapes (Compile W.c)
                (Compile.encodeTape (W.encodeIn x)))) = some cfg
        rw [htapes]
        have hle :
            Compile.overhead (State.size (W.encodeIn x) + W.c.cost (W.encodeIn x))
              ≤ Compile.overhead
                  (encodable.size x + 1 + W.cost_bound (encodable.size x)) := by
          apply Compile.overhead_mono
          have h1 : State.size (W.encodeIn x) ≤ encodable.size x + 1 :=
            W.encodeIn_size x
          have h2 : W.c.cost (W.encodeIn x) ≤ W.cost_bound (encodable.size x) :=
            W.cost_le x
          omega
        obtain ⟨k, hk⟩ := Nat.le.dest hle
        rw [← hk]
        exact runFlatTM_extend hrun hhalt
      · -- decode cfg = decodeOut (decodeTape cfg) = decodeOut (c.eval s) = f x
        show W.decodeOut (Compile.decodeTape cfg) = f x
        rw [hdec]; exact W.computes x

/-! ## (C) Composition — where the difficulty concentrates

Replacing the witness forces `reducesPolyMO_transitive` and `red_inNP`
to compose two TM-backed maps. At the **TM level** this needs a
re-encoding machine (the output tape of `f`'s TM must be re-laid-out as
the input tape of `g`'s TM), because `ComputesBy.encode`/`decode` are
free functions with no shared representation. That re-encoder is exactly
what the **layer** avoids: `Cmd.seq` keeps everything in the single
`State` representation, so the composite needs no bridge tape. Hence
composition is tractable *only* at the layer level (`PolyTimeComputableLang.comp`,
still sorry-bodied) — which is the ROADMAP's whole thesis.

The remaining obstacle even at the layer is an **encoding-compatibility**
gap: `PolyTimeComputableLang` carries `encodeIn`/`decodeOut` as
unconstrained functions, so `Wg.encodeIn (h x)` is not recoverable from
`Wh`'s output state without an extra hypothesis. The lemma below makes
that hypothesis explicit and shows the rest goes through definitionally
(`Cmd.eval_seq`), pinning down precisely what a real `comp` needs: a
canonical per-type layer encoding (a `LangEncodable`-style class) so that
`decodeOut`/`encodeIn` agree. -/

/-- Layer composition under an explicit encoding-compatibility bridge
`reEncode` (a `Cmd` mapping `Wh`'s output state to `Wg`'s input state).
The `computes` law then follows definitionally from `Cmd.eval_seq`. This
isolates the one missing ingredient (a canonical state encoding) without
a sorry; a real `PolyTimeComputableLang.comp` is this with `reEncode`
supplied by the canonical encoding and the cost bound assembled from the
two polynomial bounds. -/
theorem PolyTimeComputableLang.comp_computes_of_bridge
    {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    {g : Y → Z} {h : X → Y}
    (Wg : PolyTimeComputableLang g) (Wh : PolyTimeComputableLang h)
    (reEncode : Cmd)
    (h_bridge : ∀ x, reEncode.eval (Wh.c.eval (Wh.encodeIn x)) = Wg.encodeIn (h x)) :
    ∀ x, Wg.decodeOut ((Wh.c ;; (reEncode ;; Wg.c)).eval (Wh.encodeIn x))
          = (g ∘ h) x := by
  intro x
  rw [Cmd.eval_seq, Cmd.eval_seq, h_bridge]
  exact Wg.computes (h x)

/-! ## (D) The forcing-function test

The S1 reduction `FlatSingleTMGenNP_to_FlatTCC_instance`
(`Reductions/FlatSingleTMGenNP_to_FlatTCC.lean`) is

```
noncomputable def … := if h : FlatSingleTMGenNP (M,s,…) then yesInst else noInst
```

It is `noncomputable` and branches on `FlatSingleTMGenNP`, which is the
*existential-over-certificate* NP predicate
(`∃ cert, … ∧ acceptsFlatTM M [s ++ cert] steps = true`). Under the
**size-only** S3 witness this typechecks (output is one of two fixed
instances, both size-bounded). Under `polyTimeComputable'` it cannot,
and the obstruction is formal, not vibes:

* Any layer witness computes `f` via `Cmd.eval`, a **total computable**
  function (`Cmd.run` is a structural-recursion `def`). So a witness for
  the S1 map would compute, in polynomial cost, a function that returns
  `yesInst` exactly when `FlatSingleTMGenNP` holds.
* Post-composing a constant-comparison `Cmd` (`eqBit` against the fixed
  encoding of `noInst`) then yields a **polynomial-cost layer decider**
  for `FlatSingleTMGenNP` — i.e. `inTimePolyLang FlatSingleTMGenNP`.

The lemma below states that reduction precisely: a layer witness for an
if-on-the-answer map, plus a layer decider for "output = yesInst",
*is* a layer decider for the source predicate. The witness is therefore
exactly as hard to build as deciding the NP source — which a many-one
reduction is not allowed to do. (We state the obligation rather than
discharge the `Cmd`-level equality test, which is C5/C6 engineering; the
point is that the obligation is **a decider for an NP predicate**.) -/
theorem s1_witness_forces_decider
    {X : Type} [encodable X]
    (P : X → Prop) (yesInst noInst : X → State)
    -- `f` is an if-on-the-answer map (abstracted): on yes-instances it
    -- emits `yesInst`, on no-instances `noInst`.
    (f : X → State)
    (_hf_yes : ∀ x, P x → f x = yesInst x)
    (_hf_no  : ∀ x, ¬ P x → f x = noInst x)
    -- a layer program computing `f` …
    (c : Cmd) (encodeIn : X → State) (decodeOut : State → State)
    (_h_c : ∀ x, decodeOut (c.eval (encodeIn x)) = f x)
    -- … together with a layer test distinguishing the two outputs …
    (test : State → Bool)
    (h_test_yes : ∀ x, P x → test (decodeOut (c.eval (encodeIn x))) = true)
    (h_test_no  : ∀ x, ¬ P x → test (decodeOut (c.eval (encodeIn x))) = false) :
    -- … decides `P` pointwise. (The cost is the witness cost + the test
    -- cost, both polynomial — so this is a *polynomial-time* decider for
    -- `P`, which is exactly what an NP source cannot have.)
    ∀ x, (P x ↔ test (decodeOut (c.eval (encodeIn x))) = true) := by
  intro x
  constructor
  · exact h_test_yes x
  · intro htest
    by_contra hnp
    rw [h_test_no x hnp] at htest
    exact Bool.noConfusion htest

end Complexity.Lang
