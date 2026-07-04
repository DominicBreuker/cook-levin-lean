import Complexity.Lang.Compile
import Complexity.Lang.Frame
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

/-! ## Linear tape-length bound (C2 budget ingredient)

The corrected per-fragment compiler budget must be **linear** in the encoded
tape length (ROADMAP Risk C2 / plan step 1b — the quadratic `overhead` per
fragment does not compose). This lemma supplies the missing analytic fact: the
output tape of any sub-program is linear in `size + cost + regBound`. It joins
the three pieces that previously lived in separate files —
`Compile.encodeTape_length` (tape = contents + count + 1), `Cmd.size_eval_le`
(contents ≤ `size + cost`), and `Cmd.eval_length_le` (count ≤ `max start
regBound`) — so it lives here (PolyTime imports both `Compile` and `Frame`). -/

/-- **Linear output-tape bound.** For a program `c` touching only registers
`< k`, the encoded tape of its result is bounded linearly:
`(encodeTape (c.eval s)).length ≤ State.size s + c.cost s + max s.length k + 1`.
Each fragment boundary in a `Compile c` run is `encodeTape` of such a
sub-evaluation, so this is the per-fragment tape-length cap the linear step
bounds (`AppendGadget.appendAt_steps_le : ≤ 2·tapeLen+3`) compose against. -/
theorem Cmd.encodeTape_eval_length_le (c : Cmd) (k : Nat) (h : Cmd.UsesBelow c k)
    (s : State) :
    (Compile.encodeTape (c.eval s)).length
      ≤ State.size s + c.cost s + max s.length k + 2 := by
  rw [Compile.encodeTape_length]
  have h1 := Cmd.size_eval_le c s
  have h2 := Cmd.eval_length_le c k h s
  omega

/-- **`inOPoly` is closed under pointwise domination.** If `f ≤ g` pointwise and
`g` is `inOPoly`, so is `f` (same degree/constant witnesses). The missing
companion to `inOPoly_mono`-style reasoning for the `physStepBudget` budgets.
(Relocated upstream so the reduction-side `toFrameworkWitness'` can use it too.) -/
theorem inOPoly_of_le {f g : Nat → Nat} (hle : ∀ n, f n ≤ g n) (hg : inOPoly g) :
    inOPoly f := by
  obtain ⟨d, c, n0, h⟩ := hg
  exact ⟨d, c, n0, fun n hn => Nat.le_trans (hle n) (h n hn)⟩

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
  /-- **(B′, Risk C2) Bit-level encoding obligation.** The compiled machine has a
  fixed 4-symbol alphabet (`Compile.sig = 4`); `encodeTape` only stays inside it
  when every register cell is `0`/`1` (`Compile.BitState`). `Compile_sound`
  therefore requires `BitState (encodeIn x)`, supplied here by the witness. Bit-
  level (unary) encodings discharge it; see HANDOFF.md. -/
  enc_bit : ∀ x, Compile.BitState (encodeIn x)
  /-- **(WALL, Risk C2) Register frame.** The program touches only registers
  `< regBound`; the runtime tape-padding (`Compile.paddedBitDeciderTM`) widens the
  narrow input to `regBound` so the per-op gadgets' `Op.inBounds` precondition holds
  (see `DecidesLang.toDecidesBy` and HANDOFF.md "THE WALL"). -/
  regBound : Nat
  /-- The program only reads/writes registers below `regBound`. -/
  usesBelow : Cmd.UsesBelow c regBound
  /-- The input encoding fits within the register frame (so its width is bounded by
  the per-decider constant `regBound`, keeping the framework `encode_size`
  polynomial). Satisfiable by every layer encoding (data is packed into register
  *contents*, not spread across registers). -/
  width_le : ∀ x, (encodeIn x).length ≤ regBound

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
  /-- **Per-witness input-encoding size bound** (C8 finding F3, generalized
  2026-07-04 from the hard-coded `2·n+1`; precedent: the per-decider
  `DecidesBy.encodeBound`, owner decision 2026-06-07). The C8 per-`Q` front
  witness must take `encodeIn := encX` from the *hypothesis's* verifier, whose
  size bound is that witness's own polynomial — a fixed linear bound is not
  satisfiable there. Chain-step witnesses keep supplying `fun n => 2 * n + 1`. -/
  encBound : Nat → Nat
  encBound_poly : inOPoly encBound
  encBound_mono : monotonic encBound
  encodeIn_size : ∀ x, State.size (encodeIn x) ≤ encBound (encodable.size x)
  /-- After running `c`, the output register decodes to `f x`. -/
  computes : ∀ x, decodeOut (c.eval (encodeIn x)) = f x
  /-- Running `c` is polynomial-time. -/
  cost_le : ∀ x, c.cost (encodeIn x) ≤ cost_bound (encodable.size x)
  /-- Output size is bounded by the output of `cost_bound` —
  i.e. polynomial-time output is polynomial-size. -/
  output_size_le : ∀ x, encodable.size (f x) ≤ cost_bound (encodable.size x)
  /-- **(B′, Risk C2) Bit-level input obligation** — see `DecidesLang.enc_bit`. -/
  enc_bit : ∀ x, Compile.BitState (encodeIn x)
  /-- **(WALL, Risk C2) Register frame** — mirrors `DecidesLang.regBound`. The program
  touches only registers `< regBound`; the runtime tape-padding (`paddedComputeTM`)
  widens the narrow input to `regBound` so the per-op gadgets' `Op.inBounds` holds.
  See `toFrameworkWitness'` and `Compile.paddedCompute_run`. -/
  regBound : Nat
  /-- The program only reads/writes registers below `regBound`. -/
  usesBelow : Cmd.UsesBelow c regBound
  /-- The input encoding fits within the register frame (keeps the padded budget
  polynomial in `encodable.size x`). Satisfiable by every layer encoding (data is
  packed into register *contents*, not spread across registers). -/
  width_le : ∀ x, (encodeIn x).length ≤ regBound
  /-- **(WALL, Risk C2) Decode is padding-insensitive.** Widening the input by
  empty registers (any count `m` — the padded machine uses
  `regBound + 2 * c.loopDepth`, program frame plus compiler scratch) does not
  change the decoded output — the output register is `< regBound`, so
  `Cmd.eval_agree` transports it. This is what lets the padded machine's output
  (computed on the *wide* state) decode to `f x`. -/
  decode_agree : ∀ x (m : Nat),
    decodeOut (c.eval (encodeIn x ++ List.replicate m []))
      = decodeOut (c.eval (encodeIn x))

/-! ## Bridges

These are the *main results* of Part 3 from the consumer's perspective. -/

/-! **Bridge 1 / Bridge 2 (Part 3.4)** — the decider bridges (the live `sat_NP`
path: see `EvalCnfTM.lean`). They are defined further down:

* `DecidesLang.toDecidesBy : DecidesLang P costBound → DecidesBy P D.padTimeBound`
* `inTimePolyLang_to_inTimePoly : inTimePolyLang P → inTimePoly P`

Resolved by runtime tape-padding (`Compile.paddedBitDecider_run` — **no
`k ≤ s.length`**); the framework's `DecidesBy.encode_size` is a **per-decider
polynomial** `encodeBound` (owner-decision 2026-06-07; see `DecidesBy` in
`NP.lean`), so the multi-register `EvalCnfCmd.encodeState` (`≤ 5·size+20`) is
admissible. -/

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

/-! ### Layer composition & NP-routing — pointers (the live, proven route)

The layer is closed under `Cmd.seq`; composition across two witnesses' *free*
encodings needs a per-seam re-encoder `Cmd`. The proven entry points (defined
further down) are:

* **`comp_computes_of_bridge`** — free composition under an explicit re-encoder
  bridge (the seam obligation, stated without sorry).
* **`DecidesLang.FreePrecomposeData` / `precomposeFree`** — the verifier-side
  seam: precompose a free decider with a reduction via a concrete re-encoder.
  LIVE (`kSAT_to_SAT_free.lean`).
* **`red_inNP_of_langFree`** — NP-style composition: from a free reduction
  witness, a re-encoder bundle, and a free NP witness for `Q`, the framework's
  `inNP P`. LIVE (`inNP_kSAT3_free`).

**Removed (RETIRED 2026-07-02):** the whole canonical shared-encoding layer
(`LangEncodable`/`BitEncodable`, `PolyTimeComputableLang'`, `DecidesLang'`,
`InNPWitnessLang`/`inNPLang`/`red_inNPLang`/`inNPLang_to_inNP`,
`red_inNP_of_lang`, the `swap`/`map_fst`/`map_snd` product toolkit and the
trio-op-based product encoding). Its generic `LangEncodable (X × Y)` product
encoding is **size-unsound** (no polynomial `enc_size` exists —
`probes/UnaryProductSizeProbe.lean`), so the canonical engine could never be
populated for the live pair-typed states; every live witness and the whole
planned S3 chain use bespoke bit-level free encodings instead. Do not rebuild
it. -/

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

/-- The padded-compute time budget (numeric form), mirroring
`DecidesLang.padTimeBound`: the runtime register-padding cost, the `+1` splice
step, and the inner compiler's `physStepBudget`. `regBound` is a per-witness
constant, so this is polynomial in `n` whenever `cost_bound` is. -/
private def PolyTimeComputableLang.padTimeBound {X Y : Type} [encodable X] [encodable Y]
    {f : X → Y} (W : PolyTimeComputableLang f) (n : Nat) : Nat :=
  (W.regBound + 2 * W.c.loopDepth + 2 + 1)
      * (2 * W.encBound n + 4 * (W.regBound + 2 * W.c.loopDepth + 2) + 14) + 1
    + Compile.physStepBudget
        (W.encBound n + 2 * (W.regBound + 2 * W.c.loopDepth + 2) + W.cost_bound n + 2)
        (W.cost_bound n)

/-- The padded compute machine's actual run cost on `encodeIn x` is dominated by
`padTimeBound (size x)`. (Uses `encodeIn_size`, `cost_le`, and `width_le`; resolves
the register-count WALL via the runtime padding `Compile.paddedCompute_run`.) -/
private theorem PolyTimeComputableLang.budget_ge {X Y : Type} [encodable X] [encodable Y]
    {f : X → Y} (W : PolyTimeComputableLang f) (x : X) :
    Compile.padBudget (W.regBound + 2 * W.c.loopDepth + 2) (W.encodeIn x) + 1
        + Compile.physStepBudget (State.size (W.encodeIn x)
              + ((W.encodeIn x).length + (W.regBound + 2 * W.c.loopDepth + 2))
              + W.c.cost (W.encodeIn x) + 2) (W.c.cost (W.encodeIn x))
      ≤ W.padTimeBound (encodable.size x) := by
  have hsz : State.size (W.encodeIn x) ≤ W.encBound (encodable.size x) := W.encodeIn_size x
  have hw : (W.encodeIn x).length ≤ W.regBound := W.width_le x
  have hc : W.c.cost (W.encodeIn x) ≤ W.cost_bound (encodable.size x) := W.cost_le x
  unfold PolyTimeComputableLang.padTimeBound
  have hpb := Compile.padBudget_le (W.regBound + 2 * W.c.loopDepth + 2) (W.encodeIn x)
  have hpad : Compile.padBudget (W.regBound + 2 * W.c.loopDepth + 2) (W.encodeIn x)
      ≤ (W.regBound + 2 * W.c.loopDepth + 2 + 1)
          * (2 * W.encBound (encodable.size x) + 4 * (W.regBound + 2 * W.c.loopDepth + 2) + 14) :=
    le_trans hpb (Nat.mul_le_mul (Nat.le_succ _) (by omega))
  have hps : Compile.physStepBudget (State.size (W.encodeIn x)
            + ((W.encodeIn x).length + (W.regBound + 2 * W.c.loopDepth + 2))
            + W.c.cost (W.encodeIn x) + 2) (W.c.cost (W.encodeIn x))
      ≤ Compile.physStepBudget (W.encBound (encodable.size x)
          + 2 * (W.regBound + 2 * W.c.loopDepth + 2)
          + W.cost_bound (encodable.size x) + 2) (W.cost_bound (encodable.size x)) :=
    Compile.physStepBudget_mono (by omega) hc
  -- `omega` blows up (whnf) on the two-atom product atoms; explicit monotone adds.
  exact Nat.add_le_add (Nat.add_le_add hpad (Nat.le_refl 1)) hps

/-- **(B) The real bridge — the headline result, NOW on the residue contract.**
A layer-level `PolyTimeComputableLang f` extends to the TM-backed
`PolyTimeComputableWitness' f`. This is the function-computation analogue of the
decider side's `DecidesLang.toDecidesBy`: the machine is the runtime-padded
`Compile.paddedComputeTM W.c W.regBound` (pad the narrow input to `regBound`
registers, then run `Compile W.c`), the time budget is the polynomial
`padTimeBound`, and `Compile.paddedCompute_run` + `runFlatTM_extend` discharge the
`computes` obligation. The decode reads the output through `decodeTape` (residue-
invisible, `decodeTape_encodeTape_append`) and transports it from the *wide* state
back to the input via `decode_agree` (the WALL resolution). Sorry-free as written;
residual sorrys = the pinned bottom-up leaf gadgets (via `paddedCompute_run`). -/
theorem PolyTimeComputableLang.toFrameworkWitness'
    {X Y : Type} [encodable X] [encodable Y] {f : X → Y}
    (W : PolyTimeComputableLang f) :
    polyTimeComputable' f := by
  set RB : Nat := W.regBound + 2 * W.c.loopDepth + 2 with hRB
  have htb_poly : inOPoly W.padTimeBound := by
    unfold PolyTimeComputableLang.padTimeBound
    have hlin : inOPoly (fun n => (RB + 1) * (2 * W.encBound n + 4 * RB + 14)) :=
      inOPoly_mul (inOPoly_const _)
        (inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 2) W.encBound_poly)
          (inOPoly_const _)) (inOPoly_const 14))
    have hinner : inOPoly (fun n => W.encBound n + 2 * RB + W.cost_bound n + 2) :=
      inOPoly_add (inOPoly_add (inOPoly_add W.encBound_poly
        (inOPoly_const _)) W.cost_bound_poly) (inOPoly_const 2)
    have hcomp : inOPoly ((fun m => Compile.physStepBudget m m)
        ∘ (fun n => W.encBound n + 2 * RB + W.cost_bound n + 2)) :=
      inOPoly_comp hinner Compile.physStepBudget_poly
    have hphys : inOPoly (fun n =>
        Compile.physStepBudget (W.encBound n + 2 * RB + W.cost_bound n + 2) (W.cost_bound n)) := by
      refine inOPoly_of_le ?_ hcomp
      intro n
      show Compile.physStepBudget (W.encBound n + 2 * RB + W.cost_bound n + 2) (W.cost_bound n)
          ≤ Compile.physStepBudget (W.encBound n + 2 * RB + W.cost_bound n + 2)
              (W.encBound n + 2 * RB + W.cost_bound n + 2)
      exact Compile.physStepBudget_mono (Nat.le_refl _) (by omega)
    exact inOPoly_add (inOPoly_add hlin (inOPoly_const 1)) hphys
  have htb_mono : monotonic W.padTimeBound := by
    intro a b hab
    have hd : W.cost_bound a ≤ W.cost_bound b := W.cost_bound_mono a b hab
    have he : W.encBound a ≤ W.encBound b := W.encBound_mono a b hab
    unfold PolyTimeComputableLang.padTimeBound
    have h1 : (RB + 1) * (2 * W.encBound a + 4 * RB + 14)
        ≤ (RB + 1) * (2 * W.encBound b + 4 * RB + 14) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : Compile.physStepBudget (W.encBound a + 2 * RB + W.cost_bound a + 2) (W.cost_bound a)
        ≤ Compile.physStepBudget (W.encBound b + 2 * RB + W.cost_bound b + 2) (W.cost_bound b) :=
      Compile.physStepBudget_mono (by omega) hd
    exact Nat.add_le_add (Nat.add_le_add h1 (Nat.le_refl 1)) h2
  refine ⟨{
    toPolyTimeComputableWitness :=
      ⟨W.cost_bound, W.cost_bound_poly, W.cost_bound_mono, W.output_size_le⟩
    timeBound := W.padTimeBound
    timeBound_poly := htb_poly
    timeBound_mono := htb_mono
    computer := ?_ }⟩
  · -- ComputesBy: the machine is the runtime-padded `paddedComputeTM W.c W.regBound`
    -- (pad width `regBound + 2 * c.loopDepth`: program frame + compiler scratch).
    refine {
      encode := fun x => Compile.encodeTape (W.encodeIn x)
      M := Compile.paddedComputeTM W.c W.regBound
      M_valid := Compile.paddedComputeTM_valid W.c W.regBound
      M_tapes_pos := ?_
      decode := fun cfg => W.decodeOut (Compile.decodeTape cfg)
      computes := ?_ }
    · rw [Compile.paddedComputeTM_tapes]; exact Nat.one_pos
    · intro x
      have hbit_in : Compile.BitState (W.encodeIn x) := W.enc_bit x
      obtain ⟨res, _hres, hrun, hhalt⟩ :=
        Compile.paddedCompute_run W.c (W.encodeIn x) W.regBound hbit_in (W.width_le x)
          W.usesBelow
      set wide : State := W.encodeIn x ++ List.replicate RB [] with hwide
      have hbit_w : Compile.BitState wide := by
        rw [hwide]; exact Compile.BitState_append_replicate_nil (W.encodeIn x) RB hbit_in
      have hk_w : W.regBound ≤ wide.length := by
        rw [hwide, List.length_append, List.length_replicate]; omega
      have hbit_out : Compile.BitState (W.c.eval wide) :=
        Cmd.eval_preserves_BitState W.c W.regBound wide W.usesBelow hk_w hbit_w
      refine ⟨{ state_idx := Compile.exit W.regBound W.c + (Compile.padRegsTM RB).states,
                tapes := [([], 0, Compile.encodeTape (W.c.eval wide) ++ res)] }, ?_, hhalt, ?_⟩
      · -- The single-tape `initialTapes` collapses to `[encodeTape …]`,
        -- then pad the actual run budget up to `padTimeBound (size x)`.
        have htapes :
            initialTapes (Compile.paddedComputeTM W.c W.regBound)
                (Compile.encodeTape (W.encodeIn x))
              = [Compile.encodeTape (W.encodeIn x)] := by
          unfold initialTapes
          rw [Compile.paddedComputeTM_tapes]; simp
        show runFlatTM (W.padTimeBound (encodable.size x))
            (Compile.paddedComputeTM W.c W.regBound)
            (initFlatConfig (Compile.paddedComputeTM W.c W.regBound)
              (initialTapes (Compile.paddedComputeTM W.c W.regBound)
                (Compile.encodeTape (W.encodeIn x)))) = some _
        rw [htapes]
        obtain ⟨k, hk⟩ := Nat.le.dest (W.budget_ge x)
        rw [← hk]
        exact runFlatTM_extend hrun hhalt
      · -- decode: residue-invisible (`decodeTape_encodeTape_append`), then transport
        -- from the wide state back to the input via `decode_agree`.
        show W.decodeOut (Compile.decodeTape
            { state_idx := Compile.exit W.regBound W.c + (Compile.padRegsTM RB).states,
              tapes := [([], 0, Compile.encodeTape (W.c.eval wide) ++ res)] }) = f x
        rw [Compile.decodeTape_encodeTape_append (W.c.eval wide) res _ _ hbit_out, hwide,
          W.decode_agree x RB]
        exact W.computes x

/-! ## (C) Composition — where the difficulty concentrates

Replacing the witness forces `reducesPolyMO_transitive` and `red_inNP`
to compose two TM-backed maps. At the **TM level** this needs a
re-encoding machine (the output tape of `f`'s TM must be re-laid-out as
the input tape of `g`'s TM), because `ComputesBy.encode`/`decode` are
free functions with no shared representation. In particular there is **no
honest generic transitivity for `⪯p'`**: two opaque `polyTimeComputable'`
witnesses cannot be composed (no re-encoder can be recovered from them).

The layer answer is **`Cmd`-level composition with explicit re-encoders**:
compose the programs BEFORE bridging to the framework, supplying a
per-seam re-encoder `Cmd` that maps one program's output layout to the
next one's input layout. The lemma below (`comp_computes_of_bridge`)
states exactly that seam obligation for computable maps; the verifier
side is `DecidesLang.FreePrecomposeData`/`precomposeFree` (further down),
which is LIVE (`kSAT_to_SAT_free.lean`). A canonical shared-encoding
layer (`LangEncodable`/`PolyTimeComputableLang'`) that would have made
the seams disappear definitionally was built and then **retired
(2026-07-02)**: its product encoding is size-unsound (no polynomial
`enc_size` exists — `probes/UnaryProductSizeProbe.lean`), so it could
never cover the live pair-typed states. Per-seam re-encoders over
bespoke bit-level layouts, with the layouts **pinned by discipline**
(each type's natural layout, all work in the `Cmd`), are the working
architecture. -/

/-- Layer composition under an explicit encoding-compatibility bridge
`reEncode` (a `Cmd` mapping `Wh`'s output state to `Wg`'s input state).
The `computes` law then follows definitionally from `Cmd.eval_seq`. This
isolates the per-seam obligation of `Cmd`-level chain composition without
a sorry: build `reEncode` per seam (the `FreePrecomposeData` pattern),
never try to compose opaque framework witnesses. -/
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

/-! ## `SeamData` / `comp` — Cmd-level chain composition (SETTLED DESIGN, 2026-07-02)

**This is the migrated `red_NPhard`.** Since two opaque `polyTimeComputable'`
witnesses cannot be honestly composed (no `⪯p'`-transitivity, see below), the
reduction chain composes **at the witness level, before bridging**: a per-seam
re-encoder `Cmd` `mfc` maps the left witness's exit state onto the right
witness's input layout, *register-wise on the right witness's frame*
(`AgreeBelow Wg.regBound`, the same law as the live verifier-side
`FreePrecomposeData.bridge` / `kCnf3Check_bridge`). `comp` then produces a
single free witness for the composite map, from which ONE application of
`reducesPolyMO'_of_langFree` yields the composed `⪯p'`.

The two per-seam obligations beyond the bridge itself:
* `decode_frame` — the right witness's `decodeOut` reads only its register
  frame (true of every honest decode: they extract named registers
  `< regBound`; e.g. `extractKey` in `FlatTCC_to_FlatCC_free.lean`).
* `mfc_cost` — the re-encoder runs in polynomial cost on the left witness's
  actual exit states.

**Seam discipline for chain-step witnesses**: a step's program should exit
with the canonical layout of its *output type* on the next frame — scrub your
scratch, or let the seam's `mfc` (a short copy/clear program) do it. -/

/-- The per-seam re-encoder bundle for composing two free reduction witnesses
`Wf : PolyTimeComputableLang f` and `Wg : PolyTimeComputableLang g` into a
witness for `g ∘ f`. -/
structure PolyTimeComputableLang.SeamData
    {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    {f : X → Y} {g : Y → Z}
    (Wf : PolyTimeComputableLang f) (Wg : PolyTimeComputableLang g) where
  /-- The re-encoder: maps `Wf`'s exit layout to `Wg`'s input layout. -/
  mfc : Cmd
  /-- The seam law: after `Wf.c ;; mfc`, the state agrees on `Wg`'s whole
  register frame with `Wg`'s own encoding of the intermediate value. -/
  bridge : ∀ x, AgreeBelow Wg.regBound
    (mfc.eval (Wf.c.eval (Wf.encodeIn x))) (Wg.encodeIn (f x))
  /-- `Wg.decodeOut` reads only `Wg`'s register frame. -/
  decode_frame : ∀ s t, AgreeBelow Wg.regBound s t →
    Wg.decodeOut s = Wg.decodeOut t
  /-- Cost bound for the re-encoder on `Wf`'s actual exit states. -/
  mfcBound : Nat → Nat
  mfcBound_poly : inOPoly mfcBound
  mfcBound_mono : monotonic mfcBound
  mfc_cost : ∀ x, mfc.cost (Wf.c.eval (Wf.encodeIn x))
    ≤ mfcBound (encodable.size x)
  /-- The re-encoder stays inside the composite register frame. -/
  mfc_usesBelow : Cmd.UsesBelow mfc (max Wf.regBound Wg.regBound)

/-- Padding a state with empty registers changes no register read (`get` of a
missing or padded register is `[]` either way). -/
theorem State.get_append_replicate_nil (s : State) (m : Nat) (r : Var) :
    State.get (s ++ List.replicate m []) r = State.get s r := by
  unfold State.get
  rcases Nat.lt_or_ge r s.length with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_eq_none h]
    rcases Nat.lt_or_ge r (s ++ List.replicate m ([] : List Nat)).length with h2 | h2
    · rw [List.getElem?_eq_getElem h2]
      have hnil : (s ++ List.replicate m ([] : List Nat))[r]'h2 = [] := by
        rw [List.getElem_append_right h]
        exact List.getElem_replicate _
      rw [hnil]
      rfl
    · rw [List.getElem?_eq_none h2]

/-- **Cmd-level composition of free reduction witnesses** — the chain
composition primitive of the S3 endgame (the honest replacement for
`⪯p'`-transitivity). All fields are discharged from the seam bundle; no new
per-composite proof obligations arise. -/
def PolyTimeComputableLang.comp
    {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    {f : X → Y} {g : Y → Z}
    (Wf : PolyTimeComputableLang f) (Wg : PolyTimeComputableLang g)
    (S : Wf.SeamData Wg) : PolyTimeComputableLang (g ∘ f) where
  c := Wf.c ;; (S.mfc ;; Wg.c)
  encodeIn := Wf.encodeIn
  decodeOut := Wg.decodeOut
  cost_bound := fun n =>
    Wf.cost_bound n + S.mfcBound n + Wg.cost_bound (Wf.cost_bound n) + 2
  cost_bound_poly :=
    inOPoly_add (inOPoly_add (inOPoly_add Wf.cost_bound_poly S.mfcBound_poly)
      (inOPoly_comp Wf.cost_bound_poly Wg.cost_bound_poly)) (inOPoly_const 2)
  cost_bound_mono := fun a b h => by
    have h1 := Wf.cost_bound_mono a b h
    have h2 := S.mfcBound_mono a b h
    have h3 := Wg.cost_bound_mono _ _ h1
    show Wf.cost_bound a + S.mfcBound a + Wg.cost_bound (Wf.cost_bound a) + 2
        ≤ Wf.cost_bound b + S.mfcBound b + Wg.cost_bound (Wf.cost_bound b) + 2
    omega
  encBound := Wf.encBound
  encBound_poly := Wf.encBound_poly
  encBound_mono := Wf.encBound_mono
  encodeIn_size := Wf.encodeIn_size
  computes := fun x => by
    show Wg.decodeOut ((Wf.c ;; (S.mfc ;; Wg.c)).eval (Wf.encodeIn x)) = g (f x)
    rw [Cmd.eval_seq, Cmd.eval_seq]
    have hagree := Cmd.eval_agree Wg.c Wg.regBound Wg.usesBelow (S.bridge x)
    rw [S.decode_frame _ _ hagree]
    exact Wg.computes (f x)
  cost_le := fun x => by
    have h1 := Wf.cost_le x
    have h2 := S.mfc_cost x
    have hgc : Wg.c.cost (S.mfc.eval (Wf.c.eval (Wf.encodeIn x)))
        = Wg.c.cost (Wg.encodeIn (f x)) :=
      Cmd.cost_agree Wg.c Wg.regBound Wg.usesBelow (S.bridge x)
    have h3 := Wg.cost_le (f x)
    have h4 := Wg.cost_bound_mono _ _ (Wf.output_size_le x)
    show (Wf.c ;; (S.mfc ;; Wg.c)).cost (Wf.encodeIn x) ≤ _
    rw [Cmd.cost_seq, Cmd.cost_seq]
    omega
  output_size_le := fun x => by
    show encodable.size (g (f x)) ≤ _
    have h1 := Wg.output_size_le (f x)
    have h2 := Wg.cost_bound_mono _ _ (Wf.output_size_le x)
    omega
  enc_bit := Wf.enc_bit
  regBound := max Wf.regBound Wg.regBound
  usesBelow :=
    ⟨Cmd.UsesBelow_mono (Nat.le_max_left _ _) Wf.usesBelow,
     S.mfc_usesBelow,
     Cmd.UsesBelow_mono (Nat.le_max_right _ _) Wg.usesBelow⟩
  width_le := fun x =>
    le_trans (Wf.width_le x) (Nat.le_max_left _ _)
  decode_agree := fun x m => by
    have hpad : AgreeBelow (max Wf.regBound Wg.regBound)
        (Wf.encodeIn x ++ List.replicate m []) (Wf.encodeIn x) :=
      fun r _ => State.get_append_replicate_nil (Wf.encodeIn x) m r
    show Wg.decodeOut ((Wf.c ;; (S.mfc ;; Wg.c)).eval
        (Wf.encodeIn x ++ List.replicate m []))
      = Wg.decodeOut ((Wf.c ;; (S.mfc ;; Wg.c)).eval (Wf.encodeIn x))
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
    have h1 := Cmd.eval_agree Wf.c _
      (Cmd.UsesBelow_mono (Nat.le_max_left _ _) Wf.usesBelow) hpad
    have h2 := Cmd.eval_agree S.mfc _ S.mfc_usesBelow h1
    have h3 := Cmd.eval_agree Wg.c _
      (Cmd.UsesBelow_mono (Nat.le_max_right _ _) Wg.usesBelow) h2
    exact S.decode_frame _ _
      (fun r hr => h3 r (Nat.lt_of_lt_of_le hr (Nat.le_max_right _ _)))

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

/-! ## The decider bridge: `DecidesLang → DecidesBy → inTimePoly`

The bridge the **live `sat_NP` path** walks (`EvalCnfTM.lean`). The input
encoding is the witness's own `encodeIn` (multi-register), bounded in size by
`costBound` and in width by the per-decider `regBound`. The framework
`encode_size` is per-decider polynomial (`costBound + regBound + 2`), so the
multi-register encoding is admissible; the runtime tape-padding
(`paddedBitDecider_run`) handles the register-count WALL. -/

/-- The padded-decider time budget (numeric form): the runtime
register-padding cost, the `+1` splice step, and the inner bit-decider's
`physStepBudget … + 3`. `regBound` is a per-decider constant, so this is
polynomial in `n` whenever `costBound` is. -/
private def DecidesLang.padTimeBound {X : Type} [encodable X]
    {P : X → Prop} {costBound : Nat → Nat} (D : DecidesLang P costBound) (n : Nat) : Nat :=
  (D.regBound + 2 * D.c.loopDepth + 2 + 1)
      * (2 * costBound n + 4 * (D.regBound + 2 * D.c.loopDepth + 2) + 12) + 1
    + (Compile.physStepBudget
        (2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2) (costBound n) + 3)

/-- The free-path padded decider's actual run cost on `encodeIn x` is dominated by
`padTimeBound (size x)`. (Uses `encodeIn_size`, `cost_bound`, and the width bound
`width_le`; resolves the register-count WALL via runtime padding.) -/
private theorem DecidesLang.budget_ge {X : Type} [encodable X]
    {P : X → Prop} {costBound : Nat → Nat} (D : DecidesLang P costBound) (x : X) :
    Compile.padBudget (D.regBound + 2 * D.c.loopDepth + 2) (D.encodeIn x) + 1
        + (Compile.physStepBudget (State.size (D.encodeIn x)
              + ((D.encodeIn x).length + (D.regBound + 2 * D.c.loopDepth + 2))
              + D.c.cost (D.encodeIn x) + 2)
            (D.c.cost (D.encodeIn x)) + 3)
      ≤ D.padTimeBound (encodable.size x) := by
  have h1 : State.size (D.encodeIn x) ≤ costBound (encodable.size x) := D.encodeIn_size x
  have hw : (D.encodeIn x).length ≤ D.regBound := D.width_le x
  have h2 : D.c.cost (D.encodeIn x) ≤ costBound (encodable.size x) := D.cost_bound x
  unfold DecidesLang.padTimeBound
  have hpb := Compile.padBudget_le (D.regBound + 2 * D.c.loopDepth + 2) (D.encodeIn x)
  have hpad : Compile.padBudget (D.regBound + 2 * D.c.loopDepth + 2) (D.encodeIn x)
      ≤ (D.regBound + 2 * D.c.loopDepth + 2 + 1)
          * (2 * costBound (encodable.size x) + 4 * (D.regBound + 2 * D.c.loopDepth + 2) + 12) :=
    le_trans hpb (Nat.mul_le_mul (Nat.le_succ _) (by omega))
  have hps : Compile.physStepBudget (State.size (D.encodeIn x)
            + ((D.encodeIn x).length + (D.regBound + 2 * D.c.loopDepth + 2))
            + D.c.cost (D.encodeIn x) + 2)
          (D.c.cost (D.encodeIn x))
      ≤ Compile.physStepBudget (2 * costBound (encodable.size x)
            + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)
          (costBound (encodable.size x)) :=
    Compile.physStepBudget_mono (by omega) h2
  exact Nat.add_le_add (Nat.add_le_add hpad (Nat.le_refl 1)) (Nat.add_le_add hps (Nat.le_refl 3))

/-- **Bridge 1 (free path, WALL resolved):** a free-encoding `DecidesLang P costBound`
witness yields a framework `DecidesBy P` whose budget is polynomial in `costBound`.
The machine is `Compile.paddedBitDeciderTM D.c D.regBound` (pad the tape to `regBound`
registers at runtime, then bit-decide). The encoding is the witness's own multi-register
`encodeIn`, admitted by the now-polynomial `DecidesBy.encode_size`
(`encodeBound = costBound + regBound + 2`). The encoding/correctness/halting/budget
parts are sorry-free; residual gaps are the pinned bottom-up obligations (`padRegsTM`
run/traj). -/
def DecidesLang.toDecidesBy {X : Type} [encodable X]
    {P : X → Prop} {costBound : Nat → Nat} (D : DecidesLang P costBound)
    (hpoly : inOPoly costBound) (hmono : monotonic costBound) :
    DecidesBy P D.padTimeBound where
  encode := fun x => Compile.encodeTape (D.encodeIn x)
  encodeBound := fun n => costBound n + D.regBound + 2
  encodeBound_poly :=
    inOPoly_add (inOPoly_add hpoly (inOPoly_const D.regBound)) (inOPoly_const 2)
  encodeBound_mono := fun a b h => by
    have := hmono a b h
    show costBound a + D.regBound + 2 ≤ costBound b + D.regBound + 2
    omega
  encode_size := fun x => by
    have hlen : (Compile.encodeTape (D.encodeIn x)).length
        = State.size (D.encodeIn x) + (D.encodeIn x).length + 2 :=
      Compile.encodeTape_length (D.encodeIn x)
    have h1 := D.encodeIn_size x
    have hw := D.width_le x
    show (Compile.encodeTape (D.encodeIn x)).length
        ≤ costBound (encodable.size x) + D.regBound + 2
    omega
  M := Compile.paddedBitDeciderTM D.c D.regBound
  M_valid := Compile.paddedBitDeciderTM_valid D.c D.regBound
  M_tapes_pos := by rw [Compile.paddedBitDeciderTM_tapes]; exact Nat.one_pos
  acceptState := 1 + (Compile D.regBound D.c).states
    + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states
  rejectState := 2 + (Compile D.regBound D.c).states
    + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states
  halting_acc :=
    (Compile.paddedBitDeciderTM_halt_shift D.c D.regBound 1).trans Compile.bitTestTM_halt_one
  halting_rej :=
    (Compile.paddedBitDeciderTM_halt_shift D.c D.regBound 2).trans Compile.bitTestTM_halt_two
  accept_ne_reject := by omega
  decides_pos := fun x hPx => by
    have hb : (D.c.eval (D.encodeIn x)).get 0 = [1] :=
      eq_of_beq ((D.decides x).1.mp hPx)
    obtain ⟨cfg, hrun, hhalt, hstate⟩ :=
      Compile.paddedBitDecider_run D.c (D.encodeIn x) 1 D.regBound
        (D.enc_bit x) (D.width_le x) D.usesBelow (Or.inr rfl) hb
    refine ⟨cfg, ?_, hhalt, ?_⟩
    · have hinit : initialTapes (Compile.paddedBitDeciderTM D.c D.regBound)
            (Compile.encodeTape (D.encodeIn x))
          = [Compile.encodeTape (D.encodeIn x)] := by
        show Compile.encodeTape (D.encodeIn x)
              :: List.replicate ((Compile.paddedBitDeciderTM D.c D.regBound).tapes - 1) [] = _
        rw [Compile.paddedBitDeciderTM_tapes]
        rfl
      obtain ⟨k, hk⟩ := Nat.le.dest (D.budget_ge x)
      show runFlatTM (D.padTimeBound (encodable.size x))
            (Compile.paddedBitDeciderTM D.c D.regBound)
            (initFlatConfig (Compile.paddedBitDeciderTM D.c D.regBound)
              (initialTapes (Compile.paddedBitDeciderTM D.c D.regBound)
                (Compile.encodeTape (D.encodeIn x)))) = some cfg
      rw [hinit, ← hk]
      exact runFlatTM_extend hrun hhalt
    · show cfg.state_idx
          = 1 + (Compile D.regBound D.c).states
            + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states
      rw [hstate]; norm_num
  decides_neg := fun x hnPx => by
    have hb : (D.c.eval (D.encodeIn x)).get 0 = [0] :=
      eq_of_beq ((D.decides x).2.mp hnPx)
    obtain ⟨cfg, hrun, hhalt, hstate⟩ :=
      Compile.paddedBitDecider_run D.c (D.encodeIn x) 0 D.regBound
        (D.enc_bit x) (D.width_le x) D.usesBelow (Or.inl rfl) hb
    refine ⟨cfg, ?_, hhalt, ?_⟩
    · have hinit : initialTapes (Compile.paddedBitDeciderTM D.c D.regBound)
            (Compile.encodeTape (D.encodeIn x))
          = [Compile.encodeTape (D.encodeIn x)] := by
        show Compile.encodeTape (D.encodeIn x)
              :: List.replicate ((Compile.paddedBitDeciderTM D.c D.regBound).tapes - 1) [] = _
        rw [Compile.paddedBitDeciderTM_tapes]
        rfl
      obtain ⟨k, hk⟩ := Nat.le.dest (D.budget_ge x)
      show runFlatTM (D.padTimeBound (encodable.size x))
            (Compile.paddedBitDeciderTM D.c D.regBound)
            (initFlatConfig (Compile.paddedBitDeciderTM D.c D.regBound)
              (initialTapes (Compile.paddedBitDeciderTM D.c D.regBound)
                (Compile.encodeTape (D.encodeIn x)))) = some cfg
      rw [hinit, ← hk]
      exact runFlatTM_extend hrun hhalt
    · show cfg.state_idx
          = 2 + (Compile D.regBound D.c).states
            + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states
      rw [hstate]; norm_num

/-- **Bridge 2 (free path):** `DecidesLang P costBound` (with `costBound` polynomial
& monotonic) puts `P` in `inTimePoly`. The headline fact the live `sat_NP` path
consumes (via `inTimePolyLang_to_inTimePoly`). -/
theorem DecidesLang.toInTimePoly {X : Type} [encodable X]
    {P : X → Prop} {costBound : Nat → Nat} (D : DecidesLang P costBound)
    (hpoly : inOPoly costBound) (hmono : monotonic costBound) :
    inTimePoly P := by
  refine ⟨D.padTimeBound, ⟨D.toDecidesBy hpoly hmono⟩, ?_, ?_⟩
  · -- `inOPoly`: a linear-in-`costBound` pad term + the `physStepBudget` term
    -- (dominated by its poly diagonal) + constants.
    unfold DecidesLang.padTimeBound
    have hlin : inOPoly (fun n => (D.regBound + 2 * D.c.loopDepth + 2 + 1)
        * (2 * costBound n + 4 * (D.regBound + 2 * D.c.loopDepth + 2) + 12)) :=
      inOPoly_mul (inOPoly_const _)
        (inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 2) hpoly)
          (inOPoly_const _)) (inOPoly_const 12))
    have hinner : inOPoly (fun n => 2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2) :=
      inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 2) hpoly)
        (inOPoly_const _)) (inOPoly_const 2)
    have hcomp : inOPoly ((fun m => Compile.physStepBudget m m)
        ∘ (fun n => 2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)) :=
      inOPoly_comp hinner Compile.physStepBudget_poly
    have hphys : inOPoly (fun n =>
        Compile.physStepBudget (2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)
          (costBound n)) := by
      refine inOPoly_of_le ?_ hcomp
      intro n
      show Compile.physStepBudget (2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)
            (costBound n)
          ≤ Compile.physStepBudget (2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)
              (2 * costBound n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2)
      exact Compile.physStepBudget_mono (Nat.le_refl _) (by omega)
    exact inOPoly_add (inOPoly_add hlin (inOPoly_const 1))
      (inOPoly_add hphys (inOPoly_const 3))
  · intro a b hab
    have hd : costBound a ≤ costBound b := hmono a b hab
    unfold DecidesLang.padTimeBound
    have h1 : (D.regBound + 2 * D.c.loopDepth + 2 + 1)
          * (2 * costBound a + 4 * (D.regBound + 2 * D.c.loopDepth + 2) + 12)
        ≤ (D.regBound + 2 * D.c.loopDepth + 2 + 1)
          * (2 * costBound b + 4 * (D.regBound + 2 * D.c.loopDepth + 2) + 12) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : Compile.physStepBudget
          (2 * costBound a + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2) (costBound a)
        ≤ Compile.physStepBudget
          (2 * costBound b + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 2) (costBound b) :=
      Compile.physStepBudget_mono (by omega) hd
    exact Nat.add_le_add (Nat.add_le_add h1 (Nat.le_refl 1)) (Nat.add_le_add h2 (Nat.le_refl 3))

/-- **Bridge 2 (headline, free path):** `inTimePolyLang P` implies `inTimePoly P`.
The consumer-facing fact (`EvalCnfTM.lean` / `CliqueRelTM.lean`). -/
theorem inTimePolyLang_to_inTimePoly {X : Type} [encodable X]
    {P : X → Prop} (h : inTimePolyLang P) : inTimePoly P := by
  obtain ⟨costBound, ⟨D⟩, hpoly, hmono⟩ := h
  exact D.toInTimePoly hpoly hmono

/-! ## Free-encoding layer-native NP (`inNPLangFree`) — the S3 linchpin

The layer-native NP class. The two *live, axiom-clean* verifiers
(`evalCnfDecidesLang`, `cliqueRelDecidesLang`) are **free-encoding**
`DecidesLang`s: a bespoke `encodeIn : X × Cert → State` laying the whole pair
out directly, with no per-type canonical encoding (the retired canonical
alternative needed a `LangEncodable (X × Cert)` product encoding, which is
size-unsound — see the retirement note above `comp_computes_of_bridge`).

**What this buys.** The framework `inNP P` (built via `inNP_intro`) immediately
erases its verifier into an opaque `inTimePoly` (a `FlatTM`), from which no `Cmd`
is recoverable — which is exactly why `red_inNP` (`NP.lean`) cannot route through
the layer. An `inNPLangFree P` witness instead *preserves* the free verifier
`Cmd`, so the reduction closure (`InNPWitnessLangFree.precompose`, below) can
precompose it with a concrete re-encoder. This is the load-bearing foundation
for retiring S3's opaque `inNP`; first live application:
`KSat3Free.inNP_kSAT3_free` (`NP/kSAT_to_SAT_free.lean`). -/

/-- **Free-encoding layer-native NP witness.** The layer analogue of the
framework's `InNPWitness`, with the certificate relation decided by a
*free-encoding* `DecidesLang` (the bespoke-`encodeIn` form the live verifiers
`evalCnfDecidesLang`/`cliqueRelDecidesLang` actually have). The verifier program
is a recoverable `Cmd`, so it can be precomposed with a (free) reduction — which
an opaque `FlatTM` `inNP` cannot offer. No `LangEncodable Cert`-style canonical
instance is needed: the free verifier encodes the whole pair `X × Cert`
bespokely. -/
structure InNPWitnessLangFree {X Cert : Type} [encodable X] [encodable Cert]
    (P : X → Prop) where
  /-- The certificate relation. -/
  rel : X → Cert → Prop
  /-- Verifier cost bound. -/
  dBound : Nat → Nat
  dBound_poly : inOPoly dBound
  dBound_mono : monotonic dBound
  /-- The verifier: a *free-encoding* layer decider for the certificate relation,
  read as a predicate on the pair `(input, certificate)`. -/
  verifier : DecidesLang (fun xc : X × Cert => rel xc.1 xc.2) dBound
  /-- The relation is a sound and complete, polynomially-bounded certificate
  relation for `P` (the predicate-level NP content, identical to the framework). -/
  rel_correct : polyCertRel P rel

/-- `P` is in NP *at the layer level, free-encoding*: there is a certificate type
with a free-encoding layer verifier (`DecidesLang`) and a polynomial certificate
relation. Mirrors `inNP`, existentially quantifying the certificate type and its
`encodable` instance (but not a `LangEncodable` — the free verifier needs none). -/
def inNPLangFree {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ Cert : Type, ∃ _ : encodable Cert, Nonempty (@InNPWitnessLangFree X Cert _ _ P)

/-- **Framework decider bridge (free path).** `inNPLangFree Q → inNP Q`: a
free-encoding layer-native NP witness yields a framework-level NP witness. The
verifier crosses via `DecidesLang.toInTimePoly` (the *identical* path the live
`sat_NP` / `FlatClique_in_NP` already take, so it preserves axiom-cleanliness); the
certificate relation is carried verbatim. -/
theorem inNPLangFree_to_inNP {Y : Type} [encodable Y]
    {Q : Y → Prop} (h : inNPLangFree Q) : inNP Q := by
  obtain ⟨Cert, eC, ⟨W⟩⟩ := h
  letI := eC
  exact inNP_intro Q W.rel (W.verifier.toInTimePoly W.dBound_poly W.dBound_mono) W.rel_correct

/-! ## Free precompose — the verifier-side seam

Free encodings have **no shared layout**, so a reduction map's output must be
**re-encoded** into the decider's bespoke input layout by an explicit `Cmd` —
the `mfc` below — satisfying a register-wise agreement law (`bridge`). This is
exactly the re-encoder gap `PolyTimeComputableLang.comp_computes_of_bridge`
isolates, packaged for the verifier side.

Everything except the *decides* law is passed through as data about the composite
`mfc ;; D.c` (cost / size / frame / bit); `precomposeFree` proves `decides` from
`bridge` alone. The whole per-reduction obligation is thus concentrated,
**sorry-free**, in one `FreePrecomposeData` value — a concrete re-encoder program
plus its bounds. Building that value for a specific reduction is ordinary
verifier engineering (like any `DecidesLang`), NOT a structural unknown — LIVE
example: `KSat3Free.kSAT3_precomposeData`.

⚠ **Honesty is per-witness discipline, not enforced by the structure**: the
trivial instantiation `eIn := D.encodeIn ∘ gmap`, `mfc := no-op` satisfies every
field (encoding-hides-computation, the S3 weakness one level up). `eIn` must be
the natural layout of the INPUT — never of `gmap v` — with all reduction work in
the `Cmd`. Review every future witness against this until encodings are pinned. -/

/-- The re-encoder bundle for free precomposition of a decider `D : DecidesLang Q`
with a map `gmap : V → W`: a `Cmd` `mfc` and an input encoding `eIn : V → State` such
that `mfc.eval (eIn v)` agrees, on `D`'s register frame, with `D.encodeIn (gmap v)`
(so running `D.c` afterwards decides `Q (gmap v)`), together with the composite's
cost/size/frame/bit bounds. The **only** per-reduction obligation. -/
structure DecidesLang.FreePrecomposeData {V W : Type} [encodable V] [encodable W]
    {Q : W → Prop} {dBound : Nat → Nat} (D : DecidesLang Q dBound) (gmap : V → W) where
  /-- The re-encoder: computes `gmap v` (running the reduction) and re-lays it into
  `D`'s bespoke input layout. -/
  mfc : Cmd
  /-- The composite decider's input encoding. -/
  eIn : V → State
  /-- Cost/size bound of the composite. -/
  newBound : Nat → Nat
  newBound_poly : inOPoly newBound
  newBound_mono : monotonic newBound
  /-- **The re-encoding law**: after `mfc`, the state agrees with `D`'s own
  input layout on `D`'s register frame. -/
  bridge : ∀ v, AgreeBelow D.regBound (mfc.eval (eIn v)) (D.encodeIn (gmap v))
  encodeIn_size : ∀ v, State.size (eIn v) ≤ newBound (encodable.size v)
  cost_bound : ∀ v, (mfc ;; D.c).cost (eIn v) ≤ newBound (encodable.size v)
  enc_bit : ∀ v, Compile.BitState (eIn v)
  regBound : Nat
  usesBelow : Cmd.UsesBelow (mfc ;; D.c) regBound
  width_le : ∀ v, (eIn v).length ≤ regBound

/-- **Free precompose.** Given a free decider `D : DecidesLang Q` and a re-encoder
bundle for `gmap`, produce a free decider for `fun v => Q (gmap v)`. Only the
`decides` law is proved here (via `bridge` + `Cmd.eval_agree` at register `0`, where
accept/reject is read); all other fields are the composite bounds carried by `data`.
Sorry-free. The free-encoding engine of `red_inNP` at the layer. -/
def DecidesLang.precomposeFree {V W : Type} [encodable V] [encodable W]
    {Q : W → Prop} {dBound : Nat → Nat} (D : DecidesLang Q dBound) (gmap : V → W)
    (data : D.FreePrecomposeData gmap) :
    DecidesLang (fun v => Q (gmap v)) data.newBound where
  c := data.mfc ;; D.c
  encodeIn := data.eIn
  encodeIn_size := data.encodeIn_size
  decides := fun v => by
    have hagree : AgreeBelow D.regBound (D.c.eval (data.mfc.eval (data.eIn v)))
        (D.c.eval (D.encodeIn (gmap v))) :=
      Cmd.eval_agree D.c D.regBound D.usesBelow (data.bridge v)
    have h0 : State.get ((data.mfc ;; D.c).eval (data.eIn v)) 0
        = State.get (D.c.eval (D.encodeIn (gmap v))) 0 := by
      rw [Cmd.eval_seq]
      exact hagree 0 (Cmd.UsesBelow_pos D.usesBelow)
    have hacc : ((data.mfc ;; D.c).eval (data.eIn v)).isAccept
        = (D.c.eval (D.encodeIn (gmap v))).isAccept := by
      show (State.get ((data.mfc ;; D.c).eval (data.eIn v)) 0 == [1])
          = (State.get (D.c.eval (D.encodeIn (gmap v))) 0 == [1])
      rw [h0]
    have hrej : ((data.mfc ;; D.c).eval (data.eIn v)).isReject
        = (D.c.eval (D.encodeIn (gmap v))).isReject := by
      show (State.get ((data.mfc ;; D.c).eval (data.eIn v)) 0 == [0])
          = (State.get (D.c.eval (D.encodeIn (gmap v))) 0 == [0])
      rw [h0]
    refine ⟨?_, ?_⟩
    · rw [hacc]; exact (D.decides (gmap v)).1
    · rw [hrej]; exact (D.decides (gmap v)).2
  cost_bound := data.cost_bound
  enc_bit := data.enc_bit
  regBound := data.regBound
  usesBelow := data.usesBelow
  width_le := data.width_le

/-- **Free-encoding reduction closure at the witness level.** From a concrete
free-encoding NP witness `W : InNPWitnessLangFree Q`, a reduction `f` (with a
size-bound witness `Wf`), a re-encoder bundle for the pair-map `(x,c) ↦ (f x, c)`,
and correctness `P x ↔ Q (f x)`, build an `InNPWitnessLangFree P`. The verifier is
`W.verifier.precomposeFree`; the certificate relation transports exactly as in the
framework's `red_inNP`.

This operates on the **concrete** witness `W` (not the existential
`inNPLangFree Q`): the re-encoder depends on `W.verifier`'s bespoke `encodeIn`,
which is not recoverable from `Wf` alone (the free encodings do not share a
layout), so it must be supplied against a known verifier. -/
def InNPWitnessLangFree.precompose {X Y Cert : Type}
    [encodable X] [encodable Y] [encodable Cert]
    {P : X → Prop} {Q : Y → Prop} {f : X → Y}
    (W : @InNPWitnessLangFree Y Cert _ _ Q) (Wf : PolyTimeComputableLang f)
    (data : W.verifier.FreePrecomposeData (fun xc : X × Cert => (f xc.1, xc.2)))
    (hcorrect : ∀ x, P x ↔ Q (f x)) :
    @InNPWitnessLangFree X Cert _ _ P where
  rel := fun x c => W.rel (f x) c
  dBound := data.newBound
  dBound_poly := data.newBound_poly
  dBound_mono := data.newBound_mono
  verifier := W.verifier.precomposeFree (fun xc : X × Cert => (f xc.1, xc.2)) data
  rel_correct := by
    obtain ⟨cert_bound, hsound_R, hcomplete_R, hcert_poly_R, hcert_mono_R⟩ := W.rel_correct
    refine ⟨⟨cert_bound ∘ Wf.cost_bound, ?_, ?_,
      inOPoly_comp Wf.cost_bound_poly hcert_poly_R,
      monotonic_comp Wf.cost_bound_mono hcert_mono_R⟩⟩
    · intro x c hrel
      exact (hcorrect x).mpr (hsound_R hrel)
    · intro x hx
      rcases hcomplete_R ((hcorrect x).mp hx) with ⟨c, hc, hsize⟩
      refine ⟨c, hc, ?_⟩
      calc encodable.size c
          ≤ cert_bound (encodable.size (f x)) := hsize
        _ ≤ cert_bound (Wf.cost_bound (encodable.size x)) :=
            hcert_mono_R _ _ (Wf.output_size_le x)

/-- **The free-encoding layer-routed `red_inNP`.** From a concrete free NP witness
for `Q`, a reduction `f` with size bound `Wf`, a re-encoder bundle, and `P x ↔ Q (f x)`,
conclude the framework's `inNP P`. Composes `InNPWitnessLangFree.precompose` with the
framework bridge `inNPLangFree_to_inNP`. The remaining input, the re-encoder
`data`, is per-reduction engineering with **no structural unknown** — LIVE
example: `KSat3Free.inNP_kSAT3_free`. -/
theorem red_inNP_of_langFree {X Y Cert : Type}
    [encodable X] [encodable Y] [encodable Cert]
    {P : X → Prop} {Q : Y → Prop} {f : X → Y}
    (W : @InNPWitnessLangFree Y Cert _ _ Q) (Wf : PolyTimeComputableLang f)
    (data : W.verifier.FreePrecomposeData (fun xc : X × Cert => (f xc.1, xc.2)))
    (hcorrect : ∀ x, P x ↔ Q (f x)) : inNP P :=
  inNPLangFree_to_inNP ⟨Cert, inferInstance, ⟨W.precompose Wf data hcorrect⟩⟩

/-! ## `ReductionWitness'` / `⪯p'` — additive TM-backed reduction type

The re-typing target of the S3 migration: swap `ReductionWitness.reduction_poly`'s
`polyTimeComputable` for `polyTimeComputable'`. We introduce the upgraded type
**additively** so the live `⪯p` chain keeps compiling. The bridge `⪯p' → ⪯p` is
immediate from `polyTimeComputable'_to_polyTimeComputable`; per-step `⪯p'`
witnesses come from free layer witnesses via `reducesPolyMO'_of_langFree`.

⚠ **There is deliberately NO generic `⪯p'`-transitivity.** Composing two opaque
`polyTimeComputable'` witnesses is not honestly possible — their `ComputesBy`
encodings share no layout and no re-encoder is recoverable. Any migrated
NPhard-transport (`red_NPhard`-style, which today leans on
`reducesPolyMO_transitive`) must instead compose reductions at the `Cmd` level
(per-seam re-encoders over pinned layouts, the `FreePrecomposeData` pattern)
BEFORE bridging to `⪯p'`. Design the migrated `NPhard'` around that constraint
— this is the key open design question of ROADMAP step 2. -/

/-- A **TM-backed reduction witness**: the reduction is `polyTimeComputable'`
(carries a real `FlatTM` computing it), not merely size-bounded. -/
structure ReductionWitness' {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) where
  reduction : X → Y
  reduction_poly : polyTimeComputable' reduction
  reduction_correct : ∀ ⦃x⦄, P x ↔ Q (reduction x)

/-- The upgraded `⪯p`: a TM-backed reduction. -/
abbrev reducesPolyMO' {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (Q : Y → Prop) : Prop :=
  Nonempty (ReductionWitness' P Q)

@[inherit_doc] infix:50 " ⪯p' " => reducesPolyMO'

/-- `⪯p'` is a strengthening of `⪯p`: a TM-backed reduction is in
particular a size-only reduction. The framework's reduction chain (every
`⪯p` lemma in `NP.lean`) survives the migration verbatim through this
bridge. -/
theorem reducesPolyMO'_to_reducesPolyMO {X Y : Type} [encodable X] [encodable Y]
    {P : X → Prop} {Q : Y → Prop} : P ⪯p' Q → P ⪯p Q := by
  rintro ⟨⟨f, hf_poly, hf_correct⟩⟩
  exact ⟨⟨f, polyTimeComputable'_to_polyTimeComputable hf_poly, hf_correct⟩⟩

/-- **The per-step `⪯p'` engine.** A free layer reduction witness (a concrete
`Cmd` computing `f`) plus correctness yields the TM-backed `P ⪯p' Q`, via the
free framework bridge `PolyTimeComputableLang.toFrameworkWitness'`. Every chain
step of the S3 migration gets its honest `⪯p'` from its free witness through
this lemma — first live instance: `KSat3Free.kSAT3_reducesPolyMO'`
(`kSAT 3 ⪯p' SAT`). Chains still compose at the `Cmd` level (see the
no-generic-transitivity note above), not at `⪯p'`. -/
theorem reducesPolyMO'_of_langFree {X Y : Type} [encodable X] [encodable Y]
    {P : X → Prop} {Q : Y → Prop} {f : X → Y}
    (Wf : PolyTimeComputableLang f) (hcorrect : ∀ x, P x ↔ Q (f x)) :
    P ⪯p' Q :=
  ⟨⟨f, Wf.toFrameworkWitness', fun {x} => hcorrect x⟩⟩

/-! ## `NPhard'` / `NPcomplete'` — the migrated hardness (SETTLED DESIGN, 2026-07-02)

`NPhard'` mirrors `NPhard` verbatim over `⪯p'`. The load-bearing design
decision is what it does **not** come with:

**There is NO `red_NPhard` analogue for `NPhard'`, and none is needed.**
`red_NPhard` transports hardness along the chain via
`reducesPolyMO_transitive`; `⪯p'` has no transitivity (opaque TM-backed
witnesses cannot be honestly composed), so the migrated endgame *never states
`NPhard'` of a chain intermediate*. Instead:

1. **The chain composes at the witness level.** Each chain step is a free
   `PolyTimeComputableLang` witness (live: `flatTCC_reductionLang`;
   remaining: `FlatCC → BinaryCC`, `BinaryCC → FSAT` (Tseytin),
   `FSAT → SAT`, and the S1 tableau step). Adjacent steps are joined by a
   concrete `SeamData` (re-encoder `Cmd` + `AgreeBelow`-bridge), folded by
   `PolyTimeComputableLang.comp` into ONE witness
   `W_chain : PolyTimeComputableLang (front-instance → cnf)`.
2. **The per-`Q` front is C8's job.** For an arbitrary NP problem `Q`, the
   universal-source construction must produce a free witness `W_Q` for the
   map from `Q`-instances into the front instance type, **together with a
   `SeamData W_Q W_chain`** — its output layout pinned to the chain's fixed
   input layout. (This replaces `hasDeciderClassical` + the size-0 bound.)
3. **`NPhard' SAT` is then proven at the endpoint only**:
   `fun Y _ Q hQ => reducesPolyMO'_of_langFree ((W_Q).comp W_chain seam) hcorrect`.
   The single bridge to `⪯p'` happens after all composition.
4. The old `⪯p` chain (`NPhard`/`red_NPhard`) keeps compiling untouched until
   the endpoint proof exists, then `NPcomplete` swaps to `NPcomplete'` (that
   is the moment S1/S2 must be honest — plan as one batch).

Consequently `NPhard'` facts do not decompose; the decomposition lives in the
`SeamData`/`comp` layer above. -/

/-- The migrated `NPhard`: every NP problem `⪯p'`-reduces (TM-backed) to `P`.
Proved at chain *endpoints only* — see the design note above. -/
def NPhard' {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∀ Y : Type, ∀ _ : encodable Y, ∀ Q : Y → Prop, inNP Q → Q ⪯p' P

/-- The migrated `NPcomplete` — the faithful final statement of the S3
retirement (`CookLevin' : NPcomplete' SAT` is the endgame headline). -/
def NPcomplete' {X : Type} [encodable X] (P : X → Prop) : Prop :=
  NPhard' P ∧ inNP P

/-- `NPhard'` strengthens `NPhard`: the current conditional chain survives the
migration through this bridge. -/
theorem NPhard'_to_NPhard {X : Type} [encodable X] {P : X → Prop}
    (h : NPhard' P) : NPhard P :=
  fun Y eY Q hQ => reducesPolyMO'_to_reducesPolyMO (h Y eY Q hQ)

/-- `NPcomplete'` strengthens `NPcomplete`. -/
theorem NPcomplete'_to_NPcomplete {X : Type} [encodable X] {P : X → Prop}
    (h : NPcomplete' P) : NPcomplete P :=
  ⟨NPhard'_to_NPhard h.1, h.2⟩

end Complexity.Lang
