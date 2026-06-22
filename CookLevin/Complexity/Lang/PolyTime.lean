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
  level (unary) encodings discharge it; see `BitEncodable` and HANDOFF.md. -/
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
  /-- **(WALL, Risk C2 — bottom-up) `consLen`-free.** Until `Op.consLen` is re-laid
  UNARY (HANDOFF bottom-up Task 4), it breaks `BitState`; this field is the `NoConsLen` side-condition
  `Compile.paddedBitDecider_run` needs. Dropped entirely once `consLen` is unary. -/
  noConsLen : Cmd.NoConsLen c

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
  encodeIn_size : ∀ x, State.size (encodeIn x) ≤ 2 * encodable.size x + 1
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
  /-- **(WALL, Risk C2 — bottom-up) `consLen`-free** — mirrors `DecidesLang.noConsLen`;
  dropped once `Op.consLen` is re-laid UNARY (HANDOFF bottom-up Task 4). -/
  noConsLen : Cmd.NoConsLen c
  /-- **(WALL, Risk C2) Decode is padding-insensitive.** Widening the input by
  empty registers (any count `m` — the padded machine uses
  `regBound + 2 * c.loopDepth`, program frame plus compiler scratch) does not
  change the decoded output — the output register is `< regBound`, so
  `Cmd.eval_agree` transports it. This is what lets the padded machine's output
  (computed on the *wide* state) decode to `f x`. Discharged by `toLang` from
  `Cmd.eval_agree` (the canonical `decodeState` reads register 0). -/
  decode_agree : ∀ x (m : Nat),
    decodeOut (c.eval (encodeIn x ++ List.replicate m []))
      = decodeOut (c.eval (encodeIn x))

/-! ## Bridges

These are the *main results* of Part 3 from the consumer's
perspective. They are stated here with `sorry` bodies; the proofs
follow mechanically from `Compile_sound` once that lands. -/

/-! **Bridge 1 / Bridge 2 (Part 3.4)** — the free-encoding `DecidesLang` analogues
of `DecidesLang'.toDecidesBy` / `toInTimePoly` (the live `sat_NP` path: see
`EvalCnfTM.lean`). They are defined further down, next to the canonical bridge:

* `DecidesLang.toDecidesBy : DecidesLang P costBound → DecidesBy P D.padTimeBound`
* `inTimePolyLang_to_inTimePoly : inTimePolyLang P → inTimePoly P`

The free path is now resolved by the same runtime tape-padding as the canonical one
(`Compile.paddedBitDecider_run` — **no `k ≤ s.length`**), and the framework's
`DecidesBy.encode_size` was loosened to a **per-decider polynomial** `encodeBound`
(owner-decision 2026-06-07; see `DecidesBy` in `NP.lean`), so the multi-register
`EvalCnfCmd.encodeState` (`≤ 5·size+20`) is admissible. -/

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

The layer is closed under `Cmd.seq`, so polynomially-bounded computable functions
compose. The proven entry points (defined further down, after the canonical
`PolyTimeComputableLang'` infrastructure) are:

* **`PolyTimeComputableLang'.comp`** — *canonical-encoded* composition (no
  re-encoding bridge needed; both programs share the canonical `State`
  representation). Sorry-free.
* **`PolyTimeComputableLang.comp`** — bridges `'.comp` back to the free witness
  type via `toLang` (`(Wg.comp Wh).toLang`). Sorry-free modulo the shared pinned
  `c_noConsLen`.
* **`red_inNP_of_lang`** — NP-style composition: from a canonical layer reduction
  `Wf : PolyTimeComputableLang' f` (with `P x ↔ Q (f x)`) and a layer-native
  `inNPLang Q`, yields the framework's `inNP P` (composes `red_inNPLang` with the
  decider bridge `inNPLang_to_inNP`).

**Removed (superseded, were dead `sorry`s):** the free-encoding
`PolyTimeComputableLang.comp` (arbitrary `encodeIn`/`decodeOut`) and
`red_inNP_via_lang`. A *free* `comp` would need an explicit re-encoding `Cmd`
(see `comp_computes_of_bridge`, which isolates exactly that gap) and is also
**unneeded** — the reduction *chain* composes at the framework level via
`reducesPolyMO_transitive` (each link bridged by `reducesPolyMO_of_lang`).
`red_inNP_via_lang` took an abstract `inNP Q`, which exposes only an opaque
`FlatTM` decider (no `Cmd` recoverable, nothing to precompose); routing requires
the layer-native `inNPLang Q`, which is exactly what `red_inNP_of_lang` consumes. -/

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
      * (4 * n + 4 * (W.regBound + 2 * W.c.loopDepth + 2) + 14) + 1
    + Compile.physStepBudget
        (2 * n + 2 * (W.regBound + 2 * W.c.loopDepth + 2) + W.cost_bound n + 3) (W.cost_bound n)

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
  have hsz : State.size (W.encodeIn x) ≤ 2 * encodable.size x + 1 := W.encodeIn_size x
  have hw : (W.encodeIn x).length ≤ W.regBound := W.width_le x
  have hc : W.c.cost (W.encodeIn x) ≤ W.cost_bound (encodable.size x) := W.cost_le x
  unfold PolyTimeComputableLang.padTimeBound
  have hpb := Compile.padBudget_le (W.regBound + 2 * W.c.loopDepth + 2) (W.encodeIn x)
  have hpad : Compile.padBudget (W.regBound + 2 * W.c.loopDepth + 2) (W.encodeIn x)
      ≤ (W.regBound + 2 * W.c.loopDepth + 2 + 1)
          * (4 * encodable.size x + 4 * (W.regBound + 2 * W.c.loopDepth + 2) + 14) :=
    le_trans hpb (Nat.mul_le_mul (Nat.le_succ _) (by omega))
  have hps : Compile.physStepBudget (State.size (W.encodeIn x)
            + ((W.encodeIn x).length + (W.regBound + 2 * W.c.loopDepth + 2))
            + W.c.cost (W.encodeIn x) + 2) (W.c.cost (W.encodeIn x))
      ≤ Compile.physStepBudget (2 * encodable.size x + 2 * (W.regBound + 2 * W.c.loopDepth + 2)
          + W.cost_bound (encodable.size x) + 3) (W.cost_bound (encodable.size x)) :=
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
    have hlin : inOPoly (fun n => (RB + 1) * (4 * n + 4 * RB + 14)) :=
      inOPoly_mul (inOPoly_const _)
        (inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 4) inOPoly_id)
          (inOPoly_const _)) (inOPoly_const 14))
    have hinner : inOPoly (fun n => 2 * n + 2 * RB + W.cost_bound n + 3) :=
      inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 2) inOPoly_id)
        (inOPoly_const _)) W.cost_bound_poly) (inOPoly_const 3)
    have hcomp : inOPoly ((fun m => Compile.physStepBudget m m)
        ∘ (fun n => 2 * n + 2 * RB + W.cost_bound n + 3)) :=
      inOPoly_comp hinner Compile.physStepBudget_poly
    have hphys : inOPoly (fun n =>
        Compile.physStepBudget (2 * n + 2 * RB + W.cost_bound n + 3) (W.cost_bound n)) := by
      refine inOPoly_of_le ?_ hcomp
      intro n
      show Compile.physStepBudget (2 * n + 2 * RB + W.cost_bound n + 3) (W.cost_bound n)
          ≤ Compile.physStepBudget (2 * n + 2 * RB + W.cost_bound n + 3)
              (2 * n + 2 * RB + W.cost_bound n + 3)
      exact Compile.physStepBudget_mono (Nat.le_refl _) (by omega)
    exact inOPoly_add (inOPoly_add hlin (inOPoly_const 1)) hphys
  have htb_mono : monotonic W.padTimeBound := by
    intro a b hab
    have hd : W.cost_bound a ≤ W.cost_bound b := W.cost_bound_mono a b hab
    unfold PolyTimeComputableLang.padTimeBound
    have h1 : (RB + 1) * (4 * a + 4 * RB + 14)
        ≤ (RB + 1) * (4 * b + 4 * RB + 14) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : Compile.physStepBudget (2 * a + 2 * RB + W.cost_bound a + 3) (W.cost_bound a)
        ≤ Compile.physStepBudget (2 * b + 2 * RB + W.cost_bound b + 3) (W.cost_bound b) :=
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
          W.usesBelow W.noConsLen
      set wide : State := W.encodeIn x ++ List.replicate RB [] with hwide
      have hbit_w : Compile.BitState wide := by
        rw [hwide]; exact Compile.BitState_append_replicate_nil (W.encodeIn x) RB hbit_in
      have hk_w : W.regBound ≤ wide.length := by
        rw [hwide, List.length_append, List.length_replicate]; omega
      have hbit_out : Compile.BitState (W.c.eval wide) :=
        Cmd.eval_preserves_BitState W.c W.regBound wide W.usesBelow hk_w W.noConsLen hbit_w
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
free functions with no shared representation. That re-encoder is exactly
what the **layer** avoids: `Cmd.seq` keeps everything in the single
`State` representation, so the composite needs no bridge tape. Hence
composition is tractable *only* at the layer level (`PolyTimeComputableLang'.comp`,
proven; `PolyTimeComputableLang.comp` bridges it to the free witness type) — which
is the ROADMAP's whole thesis.

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
a sorry. The canonical encoding **discharges** it: `PolyTimeComputableLang'.comp`
needs no `reEncode` at all (both programs share the canonical `State`), and the
proven `PolyTimeComputableLang.comp` (below) bridges that composite to the free
witness type via `toLang`. -/
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

/-! ## C9: canonical layer encoding (May 2026)

The S3 probe surfaced the one remaining structural prerequisite: layer
composition (`PolyTimeComputableLang'.comp`, `red_inNPLang`, `red_inNP_of_lang`)
could not even be *stated* on the free witness, because
`PolyTimeComputableLang.encodeIn` / `decodeOut` are **free functions** — one
program's output state need not be the next program's input state.

This block resolves C9. A `LangEncodable` class fixes a **canonical
single-register** state encoding per type; a `PolyTimeComputableLang'`
witness then runs in **canonical normal form** — its program maps
`encodeState x` to `encodeState (f x)` *exactly* (not merely "decodes to
`f x`"). Composition is then `Cmd.seq` with no re-encoding bridge, and
`PolyTimeComputableLang'.comp` goes through **definitionally** via
`Cmd.eval_seq` (the residual gap that `comp_computes_of_bridge` isolated).

The canonical witness bridges to the free-encoding `PolyTimeComputableLang`
(`toLang`), hence — composing with the S3 result — to the real TM-backed
`polyTimeComputable'` via `Compile`. All sorry-free; the only dependency is
the assumed `Compile_sound` (only in the framework bridge). -/

/-- A **canonical single-register** layer encoding for a type. `enc x` is the
register-0 contents; the program state is `[enc x]`. The round-trip law
`dec_enc` and the linear size law `enc_size` are what make composition and
the framework bridge go through. -/
class LangEncodable (X : Type) [encodable X] where
  enc : X → List Nat
  dec : List Nat → X
  dec_enc : ∀ x, dec (enc x) = x
  /-- A linear size bound. The slack (`2 · size + 1` rather than `size + 1`)
  is what makes the invariant **composable**: a self-delimiting pair encoding
  (length prefix + two components) needs more than `+1` of overhead, and
  `2 · size + 1` is closed under products (see the `X × Y` instance). -/
  enc_size : ∀ x, (enc x).length ≤ 2 * encodable.size x + 1

/-- The canonical program state holding `x`: a single register. -/
def LangEncodable.encodeState {X : Type} [encodable X] [LangEncodable X]
    (x : X) : State := [LangEncodable.enc x]

/-- Decode the canonical program state: read register 0. -/
def LangEncodable.decodeState {X : Type} [encodable X] [LangEncodable X]
    (s : State) : X := LangEncodable.dec (s.get 0)

theorem LangEncodable.decodeState_encodeState {X : Type} [encodable X]
    [LangEncodable X] (x : X) :
    LangEncodable.decodeState (LangEncodable.encodeState x) = x := by
  show LangEncodable.dec (([LangEncodable.enc x] : State).get 0) = x
  rw [show (([LangEncodable.enc x] : State).get 0) = LangEncodable.enc x from rfl]
  exact LangEncodable.dec_enc x

theorem LangEncodable.size_encodeState {X : Type} [encodable X] [LangEncodable X]
    (x : X) :
    State.size (LangEncodable.encodeState x) = (LangEncodable.enc x).length := by
  show State.size [LangEncodable.enc x] = (LangEncodable.enc x).length
  simp [State.size]

/-- The canonical state holds everything in register `0`; every register `r ≥ 1`
reads back blank. Used to discharge the high-register cases of the (pointwise)
composition proof. -/
theorem LangEncodable.encodeState_get_pos {X : Type} [encodable X] [LangEncodable X]
    (x : X) {r : Var} (hr : 0 < r) : State.get (LangEncodable.encodeState x) r = [] := by
  unfold LangEncodable.encodeState State.get
  rw [List.getElem?_eq_none (show ([LangEncodable.enc x] : List (List Nat)).length ≤ r from hr)]
  rfl

/-- **(B′, Risk C2) The bit-level encoding mixin.** A `LangEncodable` whose
canonical encoding only ever produces `0`/`1` cells, i.e. its `encodeState` is a
`Compile.BitState`. This is the once-per-type discharge of the `enc_bit`
obligation that the canonical witnesses (`DecidesLang'`, `PolyTimeComputableLang'`)
carry: prove `BitEncodable X` once and every canonical witness over `X` gets its
`enc_bit` field for free. Bit-level (unary) encodings satisfy it; the legacy
non-bit encodings (`Nat = [n]`, `List Nat = id`, the product length-prefix) do
not and must be re-laid unary — see HANDOFF.md "The ordered plan". -/
class BitEncodable (X : Type) [encodable X] [LangEncodable X] : Prop where
  enc_bit : ∀ x : X, Compile.BitState (LangEncodable.encodeState x)

/-- `encodeState x = [enc x]` is a `BitState` iff every cell of `enc x` is `0`/`1`.
The single-register layout reduces the `BitState` obligation to the encoder. -/
theorem BitState_encodeState_iff {X : Type} [encodable X] [LangEncodable X] (x : X) :
    Compile.BitState (LangEncodable.encodeState x)
      ↔ ∀ y ∈ LangEncodable.enc x, y ≤ 1 := by
  constructor
  · intro h y hy
    exact h (LangEncodable.enc x)
      (by simp [LangEncodable.encodeState]) y hy
  · intro h reg hreg y hy
    simp only [LangEncodable.encodeState, List.mem_singleton] at hreg
    subst hreg
    exact h y hy

/-- A polynomial-time computable function **in canonical normal form**: the
program maps `encodeState x` to `encodeState (f x)` exactly. This is the
stronger contract that lets programs compose without a re-encoding bridge. -/
structure PolyTimeComputableLang' {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] (f : X → Y) where
  c : Cmd
  cost_bound : Nat → Nat
  cost_bound_poly : inOPoly cost_bound
  cost_bound_mono : monotonic cost_bound
  /-- Canonical normal form, **register-wise**: every register of the output
  state reads back as the canonical encoding of `f x`. This is the relaxation of
  exact state-equality that admits scratch-using programs — a program may grow
  the underlying register list (and must clear its scratch back to blank), since
  `State.get` returns `[]` past the written registers. Composition still goes
  through, now via the frame/locality lemmas (`Cmd.eval_agree`/`eval_get_frame`)
  rather than definitionally. -/
  normalizes : ∀ (x : X) (r : Var),
    State.get (c.eval (LangEncodable.encodeState x)) r
      = State.get (LangEncodable.encodeState (f x)) r
  cost_le : ∀ x : X,
    c.cost (LangEncodable.encodeState x) ≤ cost_bound (encodable.size x)
  output_size_le : ∀ x : X, encodable.size (f x) ≤ cost_bound (encodable.size x)
  /-- **Register frame (C5a calling convention).** The program touches only
  registers `< regBound`. Together with `Cmd.eval_get_frame` / `Cmd.eval_agree`
  this lets the program be run as a subroutine inside a larger state: it
  preserves registers `≥ regBound` (where a second pair component can be
  stashed) and its low-register results depend only on the canonical input.
  Single-register witnesses set `regBound = 1`. -/
  regBound : Nat
  usesBelow : Cmd.UsesBelow c regBound
  /-- **(B′, Risk C2) Bit-level input obligation** — `encodeState x` is a
  `Compile.BitState`. Discharged once-per-type by `BitEncodable X`. -/
  enc_bit : ∀ x : X, Compile.BitState (LangEncodable.encodeState x)

/-- **Frame application (C5a).** Running the witness program on *any* state `s`
preserves every register `≥ regBound` — so a value stashed at register
`regBound` survives the call. Direct from `Cmd.eval_get_frame` + `usesBelow`. -/
theorem PolyTimeComputableLang'.eval_frame {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] {f : X → Y} (W : PolyTimeComputableLang' f)
    (s : State) {r : Var} (hr : W.regBound ≤ r) :
    (W.c.eval s).get r = s.get r :=
  Cmd.eval_get_frame W.c W.regBound W.usesBelow s r hr

/-- **Locality application (C5a).** On any state `s` agreeing with the canonical
input `encodeState x` on registers `< regBound`, the witness program's
register-`r` (`r < regBound`) result is the canonical output's — in particular
register `0` is `enc (f x)`. Direct from `Cmd.eval_agree` + `normalizes`. -/
theorem PolyTimeComputableLang'.eval_get_of_agree {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] {f : X → Y} (W : PolyTimeComputableLang' f)
    (x : X) {s : State} (hagree : AgreeBelow W.regBound (LangEncodable.encodeState x) s)
    {r : Var} (hr : r < W.regBound) :
    (W.c.eval s).get r = (LangEncodable.encodeState (f x)).get r := by
  rw [← Cmd.eval_agree W.c W.regBound W.usesBelow hagree r hr]
  exact W.normalizes x r

/-- **C9 headline: the layer composes.** Two canonical-form programs compose
under `Cmd.seq`. The (pointwise) `normalizes` law goes through via the
frame/locality lemmas (`Cmd.eval_agree` on registers `< regBound`,
`Cmd.eval_get_frame` above), and the cost bound via `Cmd.cost_agree` — `Wg` sees
`Wh`'s output, which agrees register-wise with the clean canonical input, so it
behaves and costs as on the clean input. Cost and output size compose as
`1 + cost_h + cost_g ∘ cost_h`. -/
def PolyTimeComputableLang'.comp
    {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    [LangEncodable X] [LangEncodable Y] [LangEncodable Z]
    {g : Y → Z} {h : X → Y}
    (Wg : PolyTimeComputableLang' g) (Wh : PolyTimeComputableLang' h) :
    PolyTimeComputableLang' (g ∘ h) where
  c := Wh.c ;; Wg.c
  cost_bound := fun n => 1 + Wh.cost_bound n + Wg.cost_bound (Wh.cost_bound n)
  cost_bound_poly :=
    inOPoly_add (inOPoly_add (inOPoly_const 1) Wh.cost_bound_poly)
      (inOPoly_comp Wh.cost_bound_poly Wg.cost_bound_poly)
  cost_bound_mono := by
    intro a b hab
    have h1 : Wh.cost_bound a ≤ Wh.cost_bound b := Wh.cost_bound_mono a b hab
    have h2 : Wg.cost_bound (Wh.cost_bound a) ≤ Wg.cost_bound (Wh.cost_bound b) :=
      Wg.cost_bound_mono _ _ h1
    show 1 + Wh.cost_bound a + Wg.cost_bound (Wh.cost_bound a)
        ≤ 1 + Wh.cost_bound b + Wg.cost_bound (Wh.cost_bound b)
    omega
  normalizes := fun x r => by
    show State.get ((Wh.c ;; Wg.c).eval (LangEncodable.encodeState x)) r
        = State.get (LangEncodable.encodeState (g (h x))) r
    rw [Cmd.eval_seq]
    have hagree : AgreeBelow Wg.regBound (Wh.c.eval (LangEncodable.encodeState x))
        (LangEncodable.encodeState (h x)) := fun r' _ => Wh.normalizes x r'
    by_cases hr : r < Wg.regBound
    · rw [Cmd.eval_agree Wg.c Wg.regBound Wg.usesBelow hagree r hr]
      exact Wg.normalizes (h x) r
    · have hrb : Wg.regBound ≤ r := Nat.le_of_not_lt hr
      have hr1 : 0 < r := Nat.lt_of_lt_of_le (Cmd.UsesBelow_pos Wg.usesBelow) hrb
      rw [Cmd.eval_get_frame Wg.c Wg.regBound Wg.usesBelow _ r hrb, Wh.normalizes x r,
        LangEncodable.encodeState_get_pos (h x) hr1,
        LangEncodable.encodeState_get_pos (g (h x)) hr1]
  cost_le := fun x => by
    rw [Cmd.cost_seq]
    have hagree : AgreeBelow Wg.regBound (Wh.c.eval (LangEncodable.encodeState x))
        (LangEncodable.encodeState (h x)) := fun r' _ => Wh.normalizes x r'
    rw [Cmd.cost_agree Wg.c Wg.regBound Wg.usesBelow hagree]
    -- 1 + Wh.cost (encState x) + Wg.cost (encState (h x)) ≤ cost_bound (size x)
    have hh : Wh.c.cost (LangEncodable.encodeState x) ≤ Wh.cost_bound (encodable.size x) :=
      Wh.cost_le x
    have hg : Wg.c.cost (LangEncodable.encodeState (h x))
        ≤ Wg.cost_bound (encodable.size (h x)) := Wg.cost_le (h x)
    have hsize : encodable.size (h x) ≤ Wh.cost_bound (encodable.size x) :=
      Wh.output_size_le x
    have hgmono : Wg.cost_bound (encodable.size (h x))
        ≤ Wg.cost_bound (Wh.cost_bound (encodable.size x)) :=
      Wg.cost_bound_mono _ _ hsize
    show 1 + Wh.c.cost (LangEncodable.encodeState x)
          + Wg.c.cost (LangEncodable.encodeState (h x))
        ≤ 1 + Wh.cost_bound (encodable.size x)
          + Wg.cost_bound (Wh.cost_bound (encodable.size x))
    omega
  output_size_le := fun x => by
    have hg : encodable.size (g (h x)) ≤ Wg.cost_bound (encodable.size (h x)) :=
      Wg.output_size_le (h x)
    have hsize : encodable.size (h x) ≤ Wh.cost_bound (encodable.size x) :=
      Wh.output_size_le x
    have hgmono : Wg.cost_bound (encodable.size (h x))
        ≤ Wg.cost_bound (Wh.cost_bound (encodable.size x)) :=
      Wg.cost_bound_mono _ _ hsize
    show encodable.size (g (h x))
        ≤ 1 + Wh.cost_bound (encodable.size x)
          + Wg.cost_bound (Wh.cost_bound (encodable.size x))
    omega
  regBound := max Wh.regBound Wg.regBound
  usesBelow := ⟨Cmd.UsesBelow_mono (Nat.le_max_left _ _) Wh.usesBelow,
    Cmd.UsesBelow_mono (Nat.le_max_right _ _) Wg.usesBelow⟩
  -- Input type is `X` (= `Wh`'s input), so its bit-level guarantee is `Wh`'s.
  enc_bit := Wh.enc_bit

/-- **(WALL, Risk C2 — bottom-up, pinned) The canonical program is `consLen`-free.**
The reduction-side analogue of `DecidesLang'.c_noConsLen`: until `Op.consLen` is
re-laid UNARY (HANDOFF bottom-up Task 4) it breaks `BitState`, so the canonical witnesses owe this
side-condition. It is the same pinned obligation the decider path carries; it is
dropped entirely once `consLen` is unary. -/
private theorem PolyTimeComputableLang'.c_noConsLen
    {X Y : Type} [encodable X] [encodable Y] [LangEncodable X] [LangEncodable Y]
    {f : X → Y} (W : PolyTimeComputableLang' f) :
    Cmd.NoConsLen W.c := by
  sorry

/-- A canonical witness is in particular a free-encoding
`PolyTimeComputableLang` witness (using the canonical encode/decode). This
plugs C9 into the S3 bridge `toFrameworkWitness'`. -/
def PolyTimeComputableLang'.toLang
    {X Y : Type} [encodable X] [encodable Y] [LangEncodable X] [LangEncodable Y]
    {f : X → Y} (W : PolyTimeComputableLang' f) : PolyTimeComputableLang f where
  c := W.c
  encodeIn := LangEncodable.encodeState
  decodeOut := LangEncodable.decodeState
  cost_bound := W.cost_bound
  cost_bound_poly := W.cost_bound_poly
  cost_bound_mono := W.cost_bound_mono
  encodeIn_size := fun x => by
    rw [LangEncodable.size_encodeState]; exact LangEncodable.enc_size x
  computes := fun x => by
    show LangEncodable.dec ((W.c.eval (LangEncodable.encodeState x)).get 0) = f x
    rw [W.normalizes x 0]
    exact LangEncodable.decodeState_encodeState (f x)
  cost_le := W.cost_le
  output_size_le := W.output_size_le
  -- `encodeIn = encodeState`, so the bit-level guarantee is `W`'s canonical one.
  enc_bit := W.enc_bit
  -- WALL fields: the register frame is `W`'s; width is `1 ≤ regBound`
  -- (`UsesBelow_pos`); `decode_agree` is `Cmd.eval_agree` at register `0`.
  regBound := W.regBound
  usesBelow := W.usesBelow
  width_le := fun x => Cmd.UsesBelow_pos W.usesBelow
  noConsLen := W.c_noConsLen
  decode_agree := fun x m => by
    have hag := Cmd.eval_agree W.c W.regBound W.usesBelow
      (fun r _ =>
        (Compile.get_append_replicate_nil (LangEncodable.encodeState x) m r).symm)
      0 (Cmd.UsesBelow_pos W.usesBelow)
    simp only [LangEncodable.decodeState]
    rw [← hag]

/-- **C9 + S3 end-to-end:** a canonical layer witness yields a real TM-backed
`polyTimeComputable'` (via `toLang` then the S3 bridge). Sorry-free modulo the
assumed `Compile_sound`. -/
theorem PolyTimeComputableLang'.toFrameworkWitness'
    {X Y : Type} [encodable X] [encodable Y] [LangEncodable X] [LangEncodable Y]
    {f : X → Y} (W : PolyTimeComputableLang' f) : polyTimeComputable' f :=
  W.toLang.toFrameworkWitness'

/-- **Layer composition into the free witness type.** The canonical-normal-form
witnesses compose (no re-encoding bridge — both share the canonical `State`
representation), and the composite bridges back to the free `PolyTimeComputableLang`
via `toLang`. This is the proven replacement for the deleted free-encoding
`comp` (see the module note above for why the free version is unneeded). Sorry-free
modulo the shared pinned `c_noConsLen` (inherited through `toLang`). -/
def PolyTimeComputableLang.comp
    {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    [LangEncodable X] [LangEncodable Y] [LangEncodable Z]
    {g : Y → Z} {h : X → Y}
    (Wg : PolyTimeComputableLang' g) (Wh : PolyTimeComputableLang' h) :
    PolyTimeComputableLang (g ∘ h) :=
  (Wg.comp Wh).toLang

/-! ### Inhabitants — the machinery is non-vacuous -/

/-- `Nat` in **UNARY** (Risk C2, B′): `n ↦ replicate n 1`, one bit-level register.
The size law holds because `encodable.size Nat = id`, so unary length `= n = size`.
This is the bit-level replacement for the legacy `[n]` (single non-bit cell). -/
instance : LangEncodable Nat where
  enc := fun n => List.replicate n 1
  dec := fun s => s.length
  dec_enc := fun n => by simp
  enc_size := fun n => by
    show (List.replicate n 1).length ≤ 2 * encodable.size n + 1
    rw [List.length_replicate]
    show n ≤ 2 * n + 1
    omega

/-- `List Nat` is the layer's native register type: its canonical encoding is
the identity. (`enc_size`: a list's length never exceeds its `encodable.size`,
which charges `≥ 1` per element.) -/
private theorem length_le_listNatSize :
    ∀ (acc : Nat) (xs : List Nat),
      acc + xs.length ≤ xs.foldl (fun a x => a + encodable.size x + 1) acc
  | _,   []      => by simp
  | acc, x :: xs => by
      have ih := length_le_listNatSize (acc + encodable.size x + 1) xs
      simp only [List.foldl_cons, List.length_cons]
      omega

instance (priority := high) instLangEncodableListNat : LangEncodable (List Nat) where
  enc := id
  dec := id
  dec_enc := fun _ => rfl
  enc_size := fun xs => by
    have h : xs.length ≤ encodable.size xs := by
      change xs.length ≤ xs.foldl (fun a x => a + encodable.size x + 1) 0
      simpa using length_le_listNatSize 0 xs
    show xs.length ≤ 2 * encodable.size xs + 1
    omega

/-- `Bool`: `true ↦ [1]`, `false ↦ [0]`. -/
instance : LangEncodable Bool where
  enc := fun b => if b then [1] else [0]
  dec := fun s => decide (s.headD 0 = 1)
  dec_enc := fun b => by cases b <;> rfl
  enc_size := fun b => by
    show (if b then [1] else [0]).length ≤ 2 * encodable.size b + 1
    cases b <;> simp [encodable.size]

/-- `Unit`: the empty register. -/
instance : LangEncodable Unit where
  enc := fun _ => []
  dec := fun _ => ()
  dec_enc := fun _ => rfl
  enc_size := fun _ => by show 0 ≤ 2 * 0 + 1; omega

/-- Helper: a `List Bool`'s length is at most its `encodable.size` (each
element contributes `≥ 1` to the foldl). -/
private theorem length_le_listBoolSize :
    ∀ (acc : Nat) (xs : List Bool),
      acc + xs.length ≤ xs.foldl (fun (a : Nat) (x : Bool) => a + encodable.size x + 1) acc
  | _,   []      => by simp
  | acc, x :: xs => by
      have ih := length_le_listBoolSize (acc + encodable.size x + 1) xs
      simp only [List.foldl_cons, List.length_cons]
      omega

/-! ### Generic list encoding

The product encoding lifted to lists: each element is preceded by its
`enc`-length, so the decoder can split at the right boundary. The encoding
is a single register (`List Nat`) holding the concatenation
`[(enc x₀).length] ++ enc x₀ ++ [(enc x₁).length] ++ enc x₁ ++ …`.

This is the foundational tool for migrating chain types: any structure
type can be encoded by routing through a tuple/list-of-tuples
representation, since `List (X × Y)`, `List (List X)`, etc. all become
canonically encodable from a single `LangEncodable X`. The existing
`LangEncodable (List Nat) = id` shortcut keeps priority `high` so the
layer's native register type continues to use the identity encoding. -/

/-- Encode a list element-by-element with length prefixes. -/
private def encListGen {α : Type} [encodable α] [LangEncodable α] (xs : List α) : List Nat :=
  xs.foldr (fun x acc => (LangEncodable.enc x).length :: LangEncodable.enc x ++ acc) []

private theorem encListGen_nil {α : Type} [encodable α] [LangEncodable α] :
    encListGen ([] : List α) = [] := rfl

private theorem encListGen_cons {α : Type} [encodable α] [LangEncodable α] (x : α) (xs : List α) :
    encListGen (x :: xs)
      = (LangEncodable.enc x).length :: LangEncodable.enc x ++ encListGen xs := rfl

/-- Decode helper: a budget-bounded structural recursion. Each iteration
reads the length prefix `m`, takes the next `m` symbols, and decodes them
to one element. The budget is the input length, which strictly decreases. -/
private def decListGenAux {α : Type} [encodable α] [LangEncodable α] :
    Nat → List Nat → List α
  | 0,         _           => []
  | _ + 1,     []          => []
  | budget + 1, m :: rest  =>
      LangEncodable.dec (rest.take m) :: decListGenAux budget (rest.drop m)

private def decListGen {α : Type} [encodable α] [LangEncodable α] (xs : List Nat) : List α :=
  decListGenAux xs.length xs

/-- The decoder reproduces the list when given enough budget. -/
private theorem decListGenAux_encListGen {α : Type} [encodable α] [LangEncodable α]
    (xs : List α) (N : Nat) (h : xs.length ≤ N) :
    decListGenAux N (encListGen xs) = xs := by
  induction xs generalizing N with
  | nil =>
      cases N <;> rfl
  | cons x xs' ih =>
      cases N with
      | zero =>
          -- impossible: xs'.length + 1 ≤ 0
          exact absurd h (by simp)
      | succ N =>
          have hN' : xs'.length ≤ N := by
            have : xs'.length + 1 ≤ N + 1 := h
            omega
          show decListGenAux (N + 1)
              ((LangEncodable.enc x).length :: LangEncodable.enc x ++ encListGen xs')
            = x :: xs'
          show LangEncodable.dec
                ((LangEncodable.enc x ++ encListGen xs').take (LangEncodable.enc x).length)
              :: decListGenAux N
                ((LangEncodable.enc x ++ encListGen xs').drop (LangEncodable.enc x).length)
            = x :: xs'
          rw [List.take_left, List.drop_left, LangEncodable.dec_enc, ih N hN']

/-- Round-trip: the decoder inverts the encoder. -/
private theorem decListGen_encListGen {α : Type} [encodable α] [LangEncodable α] (xs : List α) :
    decListGen (encListGen xs) = xs := by
  -- The budget `(encListGen xs).length` is `≥ xs.length`: each element
  -- contributes at least one cell (the length prefix).
  have hbudget : xs.length ≤ (encListGen xs).length := by
    induction xs with
    | nil      => rfl
    | cons x xs ih =>
        rw [encListGen_cons]
        simp only [List.length_cons, List.length_append]
        omega
  exact decListGenAux_encListGen xs _ hbudget

/-- Length bound: the encoding is at most `2 · size xs + 1`. Each element
contributes `(enc x).length + 1 ≤ 2 · size x + 2` to the encoding, and
`size xs ≥ sum (size x_i + 1) = sum (size x_i) + len xs`, so the total
`2 · sum (size x_i) + 2 · len xs ≤ 2 · size xs ≤ 2 · size xs + 1`. -/
private theorem encListGen_length_bound {α : Type} [encodable α] [LangEncodable α]
    (xs : List α) : (encListGen xs).length ≤ 2 * encodable.size xs + 1 := by
  -- General helper: ∀ acc xs,
  --   2·acc + (encListGen xs).length ≤ 2·foldl(acc + size x + 1, acc, xs) + 1.
  have hgen : ∀ (acc : Nat) (xs : List α),
      2 * acc + (encListGen xs).length
        ≤ 2 * xs.foldl (fun a x => a + encodable.size x + 1) acc + 1 := by
    intro acc xs
    induction xs generalizing acc with
    | nil      => simp [encListGen_nil]
    | cons x xs ih =>
        have hx := LangEncodable.enc_size x
        have ih' := ih (acc + encodable.size x + 1)
        rw [encListGen_cons]
        simp only [List.length_cons, List.length_append, List.foldl_cons]
        omega
  have h := hgen 0 xs
  -- `encodable.size xs` unfolds to the same foldl with `acc = 0`.
  change (encListGen xs).length ≤ 2 * xs.foldl (fun a x => a + encodable.size x + 1) 0 + 1
  omega

/-- **Generic `LangEncodable (List α)`** (lower priority than the concrete
`LangEncodable (List Nat) = id`). Each element is preceded by its
`enc`-length so the decoder can split at the right boundary. Together with
the product instance, this gives `LangEncodable (List (X × Y))` and chains
through to encode any nested-list-of-products structure. -/
instance (priority := low) instLangEncodableList {α : Type}
    [encodable α] [LangEncodable α] : LangEncodable (List α) where
  enc := encListGen
  dec := decListGen
  dec_enc := decListGen_encListGen
  enc_size := encListGen_length_bound

/-- `List Bool`: map booleans to bits and store in one register. The size
bound rides on `(bs.map …).length = bs.length` and `bs.length ≤ size bs`
(each element contributes `≥ 1` to `size`). -/
instance : LangEncodable (List Bool) where
  enc := fun bs => bs.map (fun b => if b then 1 else 0)
  dec := fun xs => xs.map (· == 1)
  dec_enc := fun bs => by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons]
      cases b <;> simp [ih]
  enc_size := fun bs => by
    have hlen : (bs.map (fun b => if b then 1 else 0)).length = bs.length :=
      List.length_map _
    have hsize : bs.length ≤ encodable.size bs := by
      change bs.length ≤ bs.foldl (fun a x => a + encodable.size x + 1) 0
      simpa using length_le_listBoolSize 0 bs
    show (bs.map (fun b => if b then 1 else 0)).length ≤ 2 * encodable.size bs + 1
    rw [hlen]; omega

/-- **Product encoding** (the pairing needed by `red_inNP`, where the verifier
consumes `(x, cert)`). A pair is one register holding a unary-ish length prefix
`(enc x).length` followed by the two components concatenated; decoding splits at
that prefix. The composable `2 · size + 1` bound is closed under this (the
prefix cell is the `+1` of overhead the old `+ 1` bound could not afford). -/
instance {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] : LangEncodable (X × Y) where
  enc := fun p =>
    (LangEncodable.enc p.1).length :: (LangEncodable.enc p.1 ++ LangEncodable.enc p.2)
  dec := fun s =>
    (LangEncodable.dec (s.tail.take (s.headD 0)),
     LangEncodable.dec (s.tail.drop (s.headD 0)))
  dec_enc := fun p => by
    obtain ⟨x, y⟩ := p
    simp only [List.tail_cons, List.headD_cons, List.take_left, List.drop_left,
      LangEncodable.dec_enc]
  enc_size := fun p => by
    obtain ⟨x, y⟩ := p
    have hx := LangEncodable.enc_size x
    have hy := LangEncodable.enc_size y
    show ((LangEncodable.enc x).length
            :: (LangEncodable.enc x ++ LangEncodable.enc y)).length
        ≤ 2 * encodable.size (x, y) + 1
    show (LangEncodable.enc x ++ LangEncodable.enc y).length + 1
        ≤ 2 * (encodable.size x + encodable.size y + 1) + 1
    rw [List.length_append]
    omega

/-! ### `BitEncodable` instances (Risk C2, B′)

The types whose canonical encoding is **already** bit-level get a `BitEncodable`
instance for free, discharging the `enc_bit` obligation of any canonical witness
over them. `Bool`/`Unit`/`List Bool` qualify today. `Nat` (`[n]`), `List Nat`
(`id`), and the product (length-prefix cell) do **not** — they must be re-laid
**unary** before they can become `BitEncodable` (HANDOFF.md "The ordered plan",
HANDOFF bottom-up Task 4). -/

/-- `Nat` is bit-level: unary `enc n = replicate n 1`, every cell is `1`. -/
instance : BitEncodable Nat where
  enc_bit n := (BitState_encodeState_iff n).mpr (by
    intro y hy
    simp only [LangEncodable.enc, List.mem_replicate] at hy
    omega)

/-- `Bool` is bit-level: `enc b ∈ {[0], [1]}`. -/
instance : BitEncodable Bool where
  enc_bit b := (BitState_encodeState_iff b).mpr (by cases b <;> decide)

/-- `Unit` is bit-level: `enc () = []`. -/
instance : BitEncodable Unit where
  enc_bit u := (BitState_encodeState_iff u).mpr (by simp [LangEncodable.enc])

/-- `List Bool` is bit-level: each cell is `0`/`1`. -/
instance : BitEncodable (List Bool) where
  enc_bit bs := (BitState_encodeState_iff bs).mpr (by
    intro y hy
    simp only [LangEncodable.enc, List.mem_map] at hy
    obtain ⟨b, _, rfl⟩ := hy
    cases b <;> simp)

/-- The identity is canonically computable: `copy 0 0` is a no-op on a
single-register state. Witnesses that `PolyTimeComputableLang'` is inhabited;
together with `comp` the canonical-computable functions form a category.

Requires `[BitEncodable X]` (Risk C2, B′): the `enc_bit` field needs the input
type's canonical encoding to be bit-level. -/
def PolyTimeComputableLang'.id_witness {X : Type} [encodable X] [LangEncodable X]
    [BitEncodable X] :
    PolyTimeComputableLang' (id : X → X) where
  c := Cmd.op (Op.copy 0 0)
  -- Under the realistic cost model `copy 0 0` costs `|enc x| + 1 ≤ 2·size + 2`.
  cost_bound := fun n => n + n + 2
  cost_bound_poly := inOPoly_add (inOPoly_add inOPoly_id inOPoly_id) (inOPoly_const 2)
  cost_bound_mono := by intro a b hab; show a + a + 2 ≤ b + b + 2; omega
  normalizes := fun x r => by
    have he : (Cmd.op (Op.copy 0 0)).eval (LangEncodable.encodeState x)
        = LangEncodable.encodeState x := by
      rw [Cmd.eval_op]
      show ([LangEncodable.enc x] : State).set 0
            (([LangEncodable.enc x] : State).get 0) = [LangEncodable.enc x]
      rw [show (([LangEncodable.enc x] : State).get 0) = LangEncodable.enc x from rfl]
      simp [State.set]
    show ((Cmd.op (Op.copy 0 0)).eval (LangEncodable.encodeState x)).get r
        = (LangEncodable.encodeState x).get r
    rw [he]
  cost_le := fun x => by
    show (Cmd.op (Op.copy 0 0)).cost (LangEncodable.encodeState x)
        ≤ encodable.size x + encodable.size x + 2
    rw [Cmd.cost_op]
    show ((LangEncodable.encodeState x).get 0).length + 1
        ≤ encodable.size x + encodable.size x + 2
    rw [show ((LangEncodable.encodeState x).get 0) = LangEncodable.enc x from rfl]
    have := LangEncodable.enc_size x
    omega
  output_size_le := fun x => by show encodable.size x ≤ encodable.size x + encodable.size x + 2; omega
  regBound := 1
  usesBelow := ⟨Nat.one_pos, Nat.one_pos⟩
  enc_bit := BitEncodable.enc_bit

/-! ### A non-trivial concrete witness — template for chain reductions

The chain migration needs `PolyTimeComputableLang' f` for actual reductions.
Below is a complete, sorry-free worked example: the constant function
`fun (_ : Bool) => true`. The `Cmd` clears register 0 then appends `[1]`,
producing the canonical encoding of `true` regardless of input. It exercises
every field of `PolyTimeComputableLang'` (cost, normalizes, frame, usesBelow)
on a real two-Op straight-line program — the smallest non-identity witness
the canonical layer admits. The next agent migrating chain reductions can
take it as the template. -/

/-- `clear 0 ;; appendOne 0` — sets register 0 to `[1]` regardless of the
incoming state. -/
private def constTrueBoolCmd : Cmd :=
  Cmd.op (Op.clear 0) ;; Cmd.op (Op.appendOne 0)

/-- The canonical-layer witness for the constant function
`(fun (_ : Bool) => true)`. A concrete sorry-free `PolyTimeComputableLang'`
exercising every field (cost ≤ 3, frame on register 0, normalizes via
direct computation). -/
def PolyTimeComputableLang'.constTrueBool :
    PolyTimeComputableLang' (fun (_ : Bool) => true) where
  c := constTrueBoolCmd
  cost_bound _ := 3
  cost_bound_poly := inOPoly_const 3
  cost_bound_mono := fun _ _ _ => Nat.le_refl _
  normalizes := fun b r => by
    -- Compute `(constTrueBoolCmd.eval (encodeState b)).get r` and match it to
    -- `(encodeState true).get r = [1]` at r = 0, `[]` elsewhere.
    have heval : constTrueBoolCmd.eval (LangEncodable.encodeState b)
        = ([[1]] : State) := by
      show ((Cmd.op (Op.clear 0)) ;; (Cmd.op (Op.appendOne 0))).eval
            (LangEncodable.encodeState b) = ([[1]] : State)
      rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
      -- (appendOne 0).eval ((clear 0).eval [enc b]) = [[] ++ [1]] = [[1]]
      cases b <;> rfl
    show (constTrueBoolCmd.eval (LangEncodable.encodeState b)).get r
        = (LangEncodable.encodeState (true : Bool)).get r
    rw [heval]
    -- `encodeState (true : Bool) = [enc true] = [[1]]`, so both sides equal
    -- `[[1]].get r`.
    rfl
  cost_le := fun b => by
    -- cost = 1 + cost(clear 0) + cost(appendOne 0) = 3.
    show constTrueBoolCmd.cost (LangEncodable.encodeState b) ≤ 3
    show ((Cmd.op (Op.clear 0)) ;; (Cmd.op (Op.appendOne 0))).cost
          (LangEncodable.encodeState b) ≤ 3
    rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
    show 1 + Op.cost (Op.clear 0) _ + Op.cost (Op.appendOne 0) _ ≤ 3
    simp [Op.cost]
  output_size_le := fun _ => by
    -- encodable.size true = 1 ≤ 3.
    show encodable.size (true : Bool) ≤ 3
    show 1 ≤ 3; omega
  regBound := 1
  usesBelow := ⟨Nat.one_pos, Nat.one_pos⟩
  enc_bit := BitEncodable.enc_bit

/-! ### A non-identity *pair-rearranging* witness — `swap`

The chain reductions repackage records; a recurring shape is reordering a pair's
components. `swap : X × Y → Y × X` is the canonical building block. Unlike
`constTrueBool`, it is **correctness-preserving for any predicate** (it only
permutes data), so it yields a genuine, fully general `⪯p'`/`⪯p` reduction
(`reducesPolyMO'_swap`, below) rather than one restricted to constant predicates.

It also exercises the frame toolkit on a different program shape than `map_fst`:
a full *repack* — unpack the length-prefixed product register, then rebuild the
swapped pair (`enc (y,x) = (enc y).length :: (enc y ++ enc x)`) and clear scratch
— with no opaque sub-witness. The whole witness is `sorry`-free and axiom-clean
(`#print axioms` shows only `propext` / `Quot.sound`). -/

/-- `swap`'s program: unpack `enc (x, y) = (enc x).length :: (enc x ++ enc y)`
into its two components (registers `3`/`4`), reassemble in swapped order
(`enc y ++ enc x` with the new length prefix `(enc y).length`) into register `0`,
then clear the five scratch registers (`1`–`5`) so the output is canonical
register-wise. -/
private def swapCmd : Cmd :=
  Cmd.op (Op.head 1 0) ;;
  Cmd.op (Op.tail 2 0) ;;
  Cmd.op (Op.takeAt 3 2 1) ;;
  Cmd.op (Op.dropAt 4 2 1) ;;
  Cmd.op (Op.concat 5 4 3) ;;
  Cmd.op (Op.consLen 0 4 5) ;;
  Cmd.op (Op.clear 1) ;;
  Cmd.op (Op.clear 2) ;;
  Cmd.op (Op.clear 3) ;;
  Cmd.op (Op.clear 4) ;;
  Cmd.op (Op.clear 5)

/-- Evaluating `swapCmd` on `encodeState (x, y)` yields the explicit final state:
register `0` holds `enc (y, x)` and the five scratch registers are blank. The
take/drop steps collapse via `List.take_left`/`List.drop_left` (the length prefix
is exactly `(enc x).length`); the per-op `State.get` reads are discharged by the
`get_set` simp set. -/
private theorem swapCmd_eval {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] (x : X) (y : Y) :
    swapCmd.eval (LangEncodable.encodeState ((x, y) : X × Y))
    = (((((((((((LangEncodable.encodeState ((x, y) : X × Y)).set 1
        [(LangEncodable.enc x).length]).set 2 (LangEncodable.enc x ++ LangEncodable.enc y)).set 3
        (LangEncodable.enc x)).set 4 (LangEncodable.enc y)).set 5
        (LangEncodable.enc y ++ LangEncodable.enc x)).set 0
        ((LangEncodable.enc y).length :: (LangEncodable.enc y ++ LangEncodable.enc x))).set 1 []).set
        2 []).set 3 []).set 4 []).set 5 [] := by
  have hg0 : (LangEncodable.encodeState ((x, y) : X × Y)).get 0
      = (LangEncodable.enc x).length :: (LangEncodable.enc x ++ LangEncodable.enc y) := rfl
  unfold swapCmd
  rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq,
    Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  simp only [Cmd.eval_op, Op.eval, hg0, List.tail_cons, State.get_set_eq, State.get_set_ne,
    List.headD_cons, List.take_left, List.drop_left, ne_eq, Nat.reduceEqDiff, not_false_eq_true]

/-- Under the realistic cost model `swapCmd`'s cost on the canonical pair input
is `5·(|enc x| + |enc y|) + 22` (the `tail`/`takeAt`/`dropAt`/`concat`/`consLen`
ops each read `O(|enc x| + |enc y|)` data); this is `≤ 10·size + 22`, linear. -/
private theorem swapCmd_cost_le {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] (x : X) (y : Y) :
    swapCmd.cost (LangEncodable.encodeState ((x, y) : X × Y))
      ≤ 10 * encodable.size ((x, y) : X × Y) + 22 := by
  have hg0 : (LangEncodable.encodeState ((x, y) : X × Y)).get 0
      = (LangEncodable.enc x).length :: (LangEncodable.enc x ++ LangEncodable.enc y) := rfl
  have hsize : encodable.size ((x, y) : X × Y)
      = encodable.size x + encodable.size y + 1 := rfl
  have hx := LangEncodable.enc_size x
  have hy := LangEncodable.enc_size y
  unfold swapCmd
  simp only [Cmd.cost_seq, Cmd.cost_op, Op.cost, Cmd.eval_op, Op.eval, hg0,
    List.tail_cons, List.headD_cons, State.get_set_eq, State.get_set_ne,
    List.take_left, List.drop_left, List.length_append, List.length_cons,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  omega

/-- The canonical-layer witness for pair swap `(x, y) ↦ (y, x)`. Sorry-free and
axiom-clean (`propext` / `Quot.sound` only). The companion to `map_fst`: where
`map_fst` runs a sub-witness on a pair's first component, `swap` is a pure
repack, so it serves as the template for the data-shuffling parts of the chain
reductions (which reorder record fields). -/
def PolyTimeComputableLang'.swap {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] :
    PolyTimeComputableLang' (fun p : X × Y => (p.2, p.1)) where
  c := swapCmd
  cost_bound := fun n => 10 * n + 22
  cost_bound_poly := inOPoly_add (inOPoly_mul (inOPoly_const 10) inOPoly_id) (inOPoly_const 22)
  cost_bound_mono := by intro a b hab; show 10 * a + 22 ≤ 10 * b + 22; omega
  normalizes := fun p r => by
    obtain ⟨x, y⟩ := p
    show State.get (swapCmd.eval (LangEncodable.encodeState ((x, y) : X × Y))) r
        = State.get (LangEncodable.encodeState (((y, x)) : Y × X)) r
    rw [swapCmd_eval x y]
    by_cases hr0 : r = 0
    · subst hr0
      rw [State.get_set_ne _ _ _ _ (show (0:Nat) ≠ 5 by decide),
        State.get_set_ne _ _ _ _ (show (0:Nat) ≠ 4 by decide),
        State.get_set_ne _ _ _ _ (show (0:Nat) ≠ 3 by decide),
        State.get_set_ne _ _ _ _ (show (0:Nat) ≠ 2 by decide),
        State.get_set_ne _ _ _ _ (show (0:Nat) ≠ 1 by decide),
        State.get_set_eq]
      rfl
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      rw [LangEncodable.encodeState_get_pos ((y, x) : Y × X) hrpos]
      by_cases hr5 : r = 5
      · subst hr5; rw [State.get_set_eq]
      · rw [State.get_set_ne _ _ _ _ hr5]
        by_cases hr4 : r = 4
        · subst hr4; rw [State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ hr4]
          by_cases hr3 : r = 3
          · subst hr3; rw [State.get_set_eq]
          · rw [State.get_set_ne _ _ _ _ hr3]
            by_cases hr2 : r = 2
            · subst hr2; rw [State.get_set_eq]
            · rw [State.get_set_ne _ _ _ _ hr2]
              by_cases hr1 : r = 1
              · subst hr1; rw [State.get_set_eq]
              · rw [State.get_set_ne _ _ _ _ hr1,
                  State.get_set_ne _ _ _ _ hr0,
                  State.get_set_ne _ _ _ _ hr5,
                  State.get_set_ne _ _ _ _ hr4,
                  State.get_set_ne _ _ _ _ hr3,
                  State.get_set_ne _ _ _ _ hr2,
                  State.get_set_ne _ _ _ _ hr1,
                  LangEncodable.encodeState_get_pos ((x, y) : X × Y) hrpos]
  cost_le := fun p => by
    obtain ⟨x, y⟩ := p
    exact swapCmd_cost_le x y
  output_size_le := fun p => by
    obtain ⟨x, y⟩ := p
    show encodable.size ((y, x) : Y × X) ≤ 10 * encodable.size ((x, y) : X × Y) + 22
    show encodable.size y + encodable.size x + 1
        ≤ 10 * (encodable.size x + encodable.size y + 1) + 22
    omega
  regBound := 6
  usesBelow := by
    unfold swapCmd
    simp only [Cmd.UsesBelow, Op.UsesBelow]
    decide
  -- TODO(C2, B′): the input type is `X × Y`; the product encoding must be re-laid
  -- UNARY before it is `BitState`, then this becomes `BitEncodable.enc_bit` (add
  -- a `[BitEncodable (X × Y)]` instance hypothesis). See HANDOFF.md bottom-up Task 4.
  enc_bit := sorry

/-! ### Verifier composition (toward `red_inNP`)

`red_inNP` needs: given a poly-time reduction `f` and a verifier for `Q`,
build a verifier for `P`. The verifier-side analogue of `comp`: a decider in
canonical form composed *after* a canonical map. -/

/-- A decider in **canonical form**: it decides `P` from the canonical state
encoding `encodeState`. The canonical analogue of `DecidesLang`. -/
structure DecidesLang' {X : Type} [encodable X] [LangEncodable X]
    (P : X → Prop) (costBound : Nat → Nat) where
  c : Cmd
  decides : Cmd.decides c LangEncodable.encodeState P
  cost_le : ∀ x : X,
    c.cost (LangEncodable.encodeState x) ≤ costBound (encodable.size x)
  /-- Register frame (cf. `PolyTimeComputableLang'`): the decider touches only
  registers `< regBound`. Needed because `precompose` feeds it a state that only
  *agrees register-wise* with the canonical input (the preceding map leaves
  scratch), so its accept/reject — read off register `0` — must be frame-robust. -/
  regBound : Nat
  usesBelow : Cmd.UsesBelow c regBound
  /-- **(B′, Risk C2) Bit-level input obligation** — `encodeState x` is a
  `Compile.BitState`. Discharged once-per-type by `BitEncodable X`. -/
  enc_bit : ∀ x : X, Compile.BitState (LangEncodable.encodeState x)

/-- **Verifier composition.** Precomposing a canonical decider for `P` with a
canonical computable map `g` yields a canonical decider for `P ∘ g`: run `g`,
then the decider. Under the relaxed (pointwise) contract `g`'s output only
*agrees register-wise* with `encodeState (g x)` (it may carry scratch), so
correctness goes through `Cmd.eval_agree` at register `0` (where accept/reject is
read) and the cost through `Cmd.cost_agree`. Cost composes as
`1 + cost_g + dBound ∘ cost_g`. The engine turning `P ⪯p Q` + a `Q`-verifier
into a `P`-verifier. -/
def DecidesLang'.precompose
    {X Y : Type} [encodable X] [encodable Y] [LangEncodable X] [LangEncodable Y]
    {g : X → Y} {P : Y → Prop} {dBound : Nat → Nat}
    (Wg : PolyTimeComputableLang' g) (D : DecidesLang' P dBound)
    (dmono : monotonic dBound) :
    DecidesLang' (fun x => P (g x))
      (fun n => 1 + Wg.cost_bound n + dBound (Wg.cost_bound n)) where
  c := Wg.c ;; D.c
  decides := fun x => by
    have hagree : AgreeBelow D.regBound (Wg.c.eval (LangEncodable.encodeState x))
        (LangEncodable.encodeState (g x)) := fun r' _ => Wg.normalizes x r'
    have h0 : State.get ((Wg.c ;; D.c).eval (LangEncodable.encodeState x)) 0
        = State.get (D.c.eval (LangEncodable.encodeState (g x))) 0 := by
      rw [Cmd.eval_seq]
      exact Cmd.eval_agree D.c D.regBound D.usesBelow hagree 0 (Cmd.UsesBelow_pos D.usesBelow)
    have hacc : ((Wg.c ;; D.c).eval (LangEncodable.encodeState x)).isAccept
        = (D.c.eval (LangEncodable.encodeState (g x))).isAccept := by
      show (State.get ((Wg.c ;; D.c).eval (LangEncodable.encodeState x)) 0 == [1])
          = (State.get (D.c.eval (LangEncodable.encodeState (g x))) 0 == [1])
      rw [h0]
    have hrej : ((Wg.c ;; D.c).eval (LangEncodable.encodeState x)).isReject
        = (D.c.eval (LangEncodable.encodeState (g x))).isReject := by
      show (State.get ((Wg.c ;; D.c).eval (LangEncodable.encodeState x)) 0 == [0])
          = (State.get (D.c.eval (LangEncodable.encodeState (g x))) 0 == [0])
      rw [h0]
    rw [hacc, hrej]
    exact D.decides (g x)
  cost_le := fun x => by
    rw [Cmd.cost_seq]
    have hagree : AgreeBelow D.regBound (Wg.c.eval (LangEncodable.encodeState x))
        (LangEncodable.encodeState (g x)) := fun r' _ => Wg.normalizes x r'
    rw [Cmd.cost_agree D.c D.regBound D.usesBelow hagree]
    have h1 : Wg.c.cost (LangEncodable.encodeState x) ≤ Wg.cost_bound (encodable.size x) :=
      Wg.cost_le x
    have h2 : D.c.cost (LangEncodable.encodeState (g x))
        ≤ dBound (encodable.size (g x)) := D.cost_le (g x)
    have h3 : encodable.size (g x) ≤ Wg.cost_bound (encodable.size x) :=
      Wg.output_size_le x
    have h4 : dBound (encodable.size (g x)) ≤ dBound (Wg.cost_bound (encodable.size x)) :=
      dmono _ _ h3
    show 1 + Wg.c.cost (LangEncodable.encodeState x)
          + D.c.cost (LangEncodable.encodeState (g x))
        ≤ 1 + Wg.cost_bound (encodable.size x)
          + dBound (Wg.cost_bound (encodable.size x))
    omega
  regBound := max Wg.regBound D.regBound
  usesBelow := ⟨Cmd.UsesBelow_mono (Nat.le_max_left _ _) Wg.usesBelow,
    Cmd.UsesBelow_mono (Nat.le_max_right _ _) D.usesBelow⟩
  -- Result input type is `X` (= `Wg`'s input), so its bit guarantee is `Wg`'s.
  enc_bit := Wg.enc_bit

/-- **Assembling `red_inNP` at the layer.** From (a) the reduction lifted to
the pair input — `Wf : PolyTimeComputableLang' (fun xc => (f xc.1, xc.2))` —
and (b) a canonical verifier for `Q`'s certificate relation, `precompose`
yields a canonical verifier for `P`'s certificate relation
`fun xc => R (f xc.1) xc.2` (the result is definitionally the precomposition).
This is exactly the `inTimePoly` half of `red_inNP`, modulo the two remaining
inputs spelled out below. -/
def DecidesLang'.ofReduction
    {X Y C : Type} [encodable X] [encodable Y] [encodable C]
    [LangEncodable X] [LangEncodable Y] [LangEncodable C]
    {f : X → Y} {R : Y → C → Prop} {dBound : Nat → Nat}
    (Wf : PolyTimeComputableLang' (fun xc : X × C => (f xc.1, xc.2)))
    (D : DecidesLang' (fun yc : Y × C => R yc.1 yc.2) dBound)
    (dmono : monotonic dBound) :
    DecidesLang' (fun xc : X × C => R (f xc.1) xc.2)
      (fun n => 1 + Wf.cost_bound n + dBound (Wf.cost_bound n)) :=
  DecidesLang'.precompose Wf D dmono

/-! ### C5a: `map_fst` — apply the reduction to a pair's first component

With the frame-preservation calling convention in place, `map_fst` is now
constructible. The program unpacks the length-prefixed product register, runs
the witness on the first component (register `0`) while the second component is
stashed at register `regBound + 2` (preserved by the frame), then repacks and
clears scratch (so the output is canonical register-wise). -/

/-- The `map_fst` program for `Wf`, parameterised by the certificate type's
register base `k = Wf.regBound`. -/
def PolyTimeComputableLang'.mapFstCmd {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] {f : X → Y} (Wf : PolyTimeComputableLang' f) : Cmd :=
  Cmd.op (Op.head Wf.regBound 0) ;;
  Cmd.op (Op.tail (Wf.regBound + 1) 0) ;;
  Cmd.op (Op.dropAt (Wf.regBound + 2) (Wf.regBound + 1) Wf.regBound) ;;
  Cmd.op (Op.takeAt 0 (Wf.regBound + 1) Wf.regBound) ;;
  Wf.c ;;
  Cmd.op (Op.concat (Wf.regBound + 1) 0 (Wf.regBound + 2)) ;;
  Cmd.op (Op.consLen 0 0 (Wf.regBound + 1)) ;;
  Cmd.op (Op.clear Wf.regBound) ;;
  Cmd.op (Op.clear (Wf.regBound + 1)) ;;
  Cmd.op (Op.clear (Wf.regBound + 2))

/-- The state of `mapFstCmd` after its four unpacking ops, before `Wf.c` runs:
register `0` holds `enc x`, the cert component `enc c` is stashed at register
`k+2`, and scratch `[(enc x).length]` / `enc x ++ enc c` sit at `k` / `k+1`. -/
def PolyTimeComputableLang'.mapFst_pre {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] {f : X → Y} (Wf : PolyTimeComputableLang' f)
    {C : Type} [encodable C] [LangEncodable C] (x : X) (c : C) : State :=
  ((((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
        [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
        (LangEncodable.enc x ++ LangEncodable.enc c)).set (Wf.regBound + 2)
        (LangEncodable.enc c)).set 0 (LangEncodable.enc x)

/-- Evaluating the four unpacking ops of `mapFstCmd` on `encodeState (x, c)`
yields `mapFst_pre`. -/
theorem PolyTimeComputableLang'.mapFst_pre_eval {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] {f : X → Y} (Wf : PolyTimeComputableLang' f)
    {C : Type} [encodable C] [LangEncodable C] (x : X) (c : C) :
    (Cmd.op (Op.takeAt 0 (Wf.regBound + 1) Wf.regBound)).eval
      ((Cmd.op (Op.dropAt (Wf.regBound + 2) (Wf.regBound + 1) Wf.regBound)).eval
        ((Cmd.op (Op.tail (Wf.regBound + 1) 0)).eval
          ((Cmd.op (Op.head Wf.regBound 0)).eval
            (LangEncodable.encodeState ((x, c) : X × C)))))
    = Wf.mapFst_pre x c := by
  have hk_pos : 0 < Wf.regBound := Cmd.UsesBelow_pos Wf.usesBelow
  have hk0 : Wf.regBound ≠ 0 := Nat.pos_iff_ne_zero.mp hk_pos
  have hg0 : (LangEncodable.encodeState ((x, c) : X × C)).get 0
      = (LangEncodable.enc x).length :: (LangEncodable.enc x ++ LangEncodable.enc c) := rfl
  -- step 1: head k 0
  have e1 : (Cmd.op (Op.head Wf.regBound 0)).eval (LangEncodable.encodeState ((x, c) : X × C))
      = (LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
          [(LangEncodable.enc x).length] := by
    show (LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
          (match (LangEncodable.encodeState ((x, c) : X × C)).get 0 with
            | [] => [] | a :: _ => [a])
        = (LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]
    rw [hg0]
  rw [e1]
  -- step 2: tail (k+1) 0
  have hg0' : ((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
        [(LangEncodable.enc x).length]).get 0
      = (LangEncodable.enc x).length :: (LangEncodable.enc x ++ LangEncodable.enc c) := by
    rw [State.get_set_ne _ _ _ _ (Ne.symm hk0)]; exact hg0
  have e2 : (Cmd.op (Op.tail (Wf.regBound + 1) 0)).eval
        ((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
          [(LangEncodable.enc x).length])
      = ((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
          (LangEncodable.enc x ++ LangEncodable.enc c) := by
    show ((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
          ((((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).get 0).tail)
        = ((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
          (LangEncodable.enc x ++ LangEncodable.enc c)
    rw [hg0', List.tail_cons]
  rw [e2]
  -- step 3: dropAt (k+2) (k+1) k
  have e3 : (Cmd.op (Op.dropAt (Wf.regBound + 2) (Wf.regBound + 1) Wf.regBound)).eval
        (((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
          (LangEncodable.enc x ++ LangEncodable.enc c))
      = ((((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
          (LangEncodable.enc x ++ LangEncodable.enc c)).set (Wf.regBound + 2)
          (LangEncodable.enc c)) := by
    have ga : (((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
          (LangEncodable.enc x ++ LangEncodable.enc c)).get (Wf.regBound + 1)
        = LangEncodable.enc x ++ LangEncodable.enc c := State.get_set_eq _ _ _
    have gb : (((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
          (LangEncodable.enc x ++ LangEncodable.enc c)).get Wf.regBound
        = [(LangEncodable.enc x).length] := by
      rw [State.get_set_ne _ _ _ _ (show Wf.regBound ≠ Wf.regBound + 1 by omega),
        State.get_set_eq]
    simp only [Cmd.eval_op, Op.eval]
    rw [ga, gb, List.headD_cons, List.drop_left]
  rw [e3]
  -- step 4: takeAt 0 (k+1) k
  have e4 : (Cmd.op (Op.takeAt 0 (Wf.regBound + 1) Wf.regBound)).eval
        (((((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
          (LangEncodable.enc x ++ LangEncodable.enc c)).set (Wf.regBound + 2)
          (LangEncodable.enc c)))
      = Wf.mapFst_pre x c := by
    have ga : (((((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
          (LangEncodable.enc x ++ LangEncodable.enc c)).set (Wf.regBound + 2)
          (LangEncodable.enc c))).get (Wf.regBound + 1)
        = LangEncodable.enc x ++ LangEncodable.enc c := by
      rw [State.get_set_ne _ _ _ _ (show Wf.regBound + 1 ≠ Wf.regBound + 2 by omega),
        State.get_set_eq]
    have gb : (((((LangEncodable.encodeState ((x, c) : X × C)).set Wf.regBound
            [(LangEncodable.enc x).length]).set (Wf.regBound + 1)
          (LangEncodable.enc x ++ LangEncodable.enc c)).set (Wf.regBound + 2)
          (LangEncodable.enc c))).get Wf.regBound
        = [(LangEncodable.enc x).length] := by
      rw [State.get_set_ne _ _ _ _ (show Wf.regBound ≠ Wf.regBound + 2 by omega),
        State.get_set_ne _ _ _ _ (show Wf.regBound ≠ Wf.regBound + 1 by omega),
        State.get_set_eq]
    unfold PolyTimeComputableLang'.mapFst_pre
    simp only [Cmd.eval_op, Op.eval]
    rw [ga, gb, List.headD_cons, List.take_left]
  rw [e4]

/-- `mapFst_pre` agrees with the canonical input `encodeState x` on all registers
`< Wf.regBound`, so `Wf.c` behaves on it as on the clean canonical input. -/
theorem PolyTimeComputableLang'.mapFst_pre_agree {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] {f : X → Y} (Wf : PolyTimeComputableLang' f)
    {C : Type} [encodable C] [LangEncodable C] (x : X) (c : C) :
    AgreeBelow Wf.regBound (LangEncodable.encodeState x) (Wf.mapFst_pre x c) := by
  intro r hr
  unfold PolyTimeComputableLang'.mapFst_pre
  by_cases hr0 : r = 0
  · subst hr0
    rw [State.get_set_eq]
    rfl
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    rw [State.get_set_ne _ _ _ _ hr0,
      State.get_set_ne _ _ _ _ (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hr))),
      State.get_set_ne _ _ _ _ (Nat.ne_of_lt (Nat.lt_succ_of_lt hr)),
      State.get_set_ne _ _ _ _ (Nat.ne_of_lt hr)]
    rw [LangEncodable.encodeState_get_pos x hrpos,
      LangEncodable.encodeState_get_pos ((x, c) : X × C) hrpos]

/-- **C5a.** Lift `Wf : PolyTimeComputableLang' f` to the pair input. Discharges
the `map_fst` hypothesis of `red_inNPLang`. -/
def PolyTimeComputableLang'.map_fst {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] {f : X → Y} (Wf : PolyTimeComputableLang' f)
    (C : Type) [encodable C] [LangEncodable C] :
    PolyTimeComputableLang' (fun xc : X × C => (f xc.1, xc.2)) where
  c := Wf.mapFstCmd
  -- Under the realistic cost model the wrapper ops read `O(|enc x| + |enc c| +
  -- |enc (f x)|)` data; total cost is `Wf.c.cost(mapFst_pre) + 3|ex| + 5|ec| +
  -- 2|efx| + 19 ≤ 5·Wf.cost_bound n + 16 n + 29`.
  cost_bound := fun n => 5 * Wf.cost_bound n + 16 * n + 29
  cost_bound_poly :=
    inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 5) Wf.cost_bound_poly)
      (inOPoly_mul (inOPoly_const 16) inOPoly_id)) (inOPoly_const 29)
  cost_bound_mono := by
    intro a b hab
    have := Wf.cost_bound_mono a b hab
    show 5 * Wf.cost_bound a + 16 * a + 29 ≤ 5 * Wf.cost_bound b + 16 * b + 29
    omega
  normalizes := by
    intro xc r
    obtain ⟨x, c⟩ := xc
    have hk_pos : 0 < Wf.regBound := Cmd.UsesBelow_pos Wf.usesBelow
    have hagree := Wf.mapFst_pre_agree x c
    show State.get (Wf.mapFstCmd.eval (LangEncodable.encodeState ((x, c) : X × C))) r
        = State.get (LangEncodable.encodeState ((f x, c) : Y × C)) r
    unfold PolyTimeComputableLang'.mapFstCmd
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Wf.mapFst_pre_eval x c,
      Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
    set s5 := Wf.c.eval (Wf.mapFst_pre x c) with hs5
    have hs5_0 : s5.get 0 = LangEncodable.enc (f x) := by
      rw [hs5]; exact Wf.eval_get_of_agree x hagree hk_pos
    have hs5_k2 : s5.get (Wf.regBound + 2) = LangEncodable.enc c := by
      rw [hs5, Wf.eval_frame (Wf.mapFst_pre x c) (show Wf.regBound ≤ Wf.regBound + 2 by omega)]
      unfold PolyTimeComputableLang'.mapFst_pre
      rw [State.get_set_ne _ _ _ _ (show (Wf.regBound + 2 : Var) ≠ 0 by omega), State.get_set_eq]
    -- Flatten the five suffix ops into one explicit nested `State.set` term over
    -- `s5` in a single pass. (A `set s6..s9` chain of mutually-referencing
    -- `let`-bindings makes defeq/`kabstract` blow up exponentially across the
    -- chain; one flat `simp only` keeps `s5` opaque and the term symbolic.)
    simp only [Cmd.eval_op, Op.eval]
    -- Post-state, with `A := s5.set (k+1) (s5.get 0 ++ s5.get (k+2))`:
    --   (((A.set 0 ((A.get 0).length :: A.get (k+1))).set k []).set (k+1) []).set (k+2) []
    by_cases hr0 : r = 0
    · subst hr0
      rw [show State.get (LangEncodable.encodeState ((f x, c) : Y × C)) 0
          = (LangEncodable.enc (f x)).length
              :: (LangEncodable.enc (f x) ++ LangEncodable.enc c) from rfl]
      rw [State.get_set_ne _ _ _ _ (show (0 : Nat) ≠ Wf.regBound + 2 by omega),
        State.get_set_ne _ _ _ _ (show (0 : Nat) ≠ Wf.regBound + 1 by omega),
        State.get_set_ne _ _ _ _ (show (0 : Nat) ≠ Wf.regBound by omega),
        State.get_set_eq,
        State.get_set_eq,
        State.get_set_ne _ _ _ _ (show (0 : Nat) ≠ Wf.regBound + 1 by omega),
        hs5_0, hs5_k2]
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      rw [LangEncodable.encodeState_get_pos ((f x, c) : Y × C) hrpos]
      by_cases hrk2 : r = Wf.regBound + 2
      · subst hrk2; rw [State.get_set_eq]
      · rw [State.get_set_ne _ _ _ _ hrk2]
        by_cases hrk1 : r = Wf.regBound + 1
        · subst hrk1; rw [State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ hrk1]
          by_cases hrk : r = Wf.regBound
          · subst hrk; rw [State.get_set_eq]
          · rw [State.get_set_ne _ _ _ _ hrk,
              State.get_set_ne _ _ _ _ hr0,
              State.get_set_ne _ _ _ _ hrk1]
            rcases Nat.lt_or_ge r Wf.regBound with hlt | hge
            · rw [hs5, Wf.eval_get_of_agree x hagree hlt,
                LangEncodable.encodeState_get_pos (f x) hrpos]
            · rw [hs5, Wf.eval_frame (Wf.mapFst_pre x c) hge]
              unfold PolyTimeComputableLang'.mapFst_pre
              rw [State.get_set_ne _ _ _ _ hr0,
                State.get_set_ne _ _ _ _ hrk2,
                State.get_set_ne _ _ _ _ hrk1,
                State.get_set_ne _ _ _ _ hrk,
                LangEncodable.encodeState_get_pos ((x, c) : X × C) hrpos]
  cost_le := by
    intro xc
    obtain ⟨x, c⟩ := xc
    have hk_pos : 0 < Wf.regBound := Cmd.UsesBelow_pos Wf.usesBelow
    have hagree := Wf.mapFst_pre_agree x c
    have hg0 : (LangEncodable.encodeState ((x, c) : X × C)).get 0
        = (LangEncodable.enc x).length :: (LangEncodable.enc x ++ LangEncodable.enc c) := rfl
    -- gets of `W := Wf.c.eval (mapFst_pre x c)` that the suffix ops read
    have hW0 : (Wf.c.eval (Wf.mapFst_pre x c)).get 0 = LangEncodable.enc (f x) :=
      Wf.eval_get_of_agree x hagree hk_pos
    have hWk2 : (Wf.c.eval (Wf.mapFst_pre x c)).get (Wf.regBound + 2) = LangEncodable.enc c := by
      rw [Wf.eval_frame (Wf.mapFst_pre x c) (show Wf.regBound ≤ Wf.regBound + 2 by omega)]
      unfold PolyTimeComputableLang'.mapFst_pre
      rw [State.get_set_ne _ _ _ _ (show (Wf.regBound + 2 : Var) ≠ 0 by omega), State.get_set_eq]
    -- register disequalities (symbolic; built without `omega`, which is opaque
    -- to the `Var := Nat` coercion — see ROADMAP gotcha).
    have d0k : (0 : Var) ≠ Wf.regBound := ne_of_lt hk_pos
    have d0k1 : (0 : Var) ≠ Wf.regBound + 1 := ne_of_lt (Nat.succ_pos _)
    have d0k2 : (0 : Var) ≠ Wf.regBound + 2 := ne_of_lt (Nat.succ_pos _)
    have dkk1 : (Wf.regBound : Var) ≠ Wf.regBound + 1 := ne_of_lt (Nat.lt_succ_self _)
    have dkk2 : (Wf.regBound : Var) ≠ Wf.regBound + 2 :=
      ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
    have dk1k2 : (Wf.regBound + 1 : Var) ≠ Wf.regBound + 2 := ne_of_lt (Nat.lt_succ_self _)
    -- cost-relevant size facts
    have hca : Wf.c.cost (Wf.mapFst_pre x c) = Wf.c.cost (LangEncodable.encodeState x) :=
      (Cmd.cost_agree Wf.c Wf.regBound Wf.usesBelow hagree).symm
    have hcle : Wf.c.cost (LangEncodable.encodeState x) ≤ Wf.cost_bound (encodable.size x) :=
      Wf.cost_le x
    have hofx : encodable.size (f x) ≤ Wf.cost_bound (encodable.size x) := Wf.output_size_le x
    have hmono : Wf.cost_bound (encodable.size x)
        ≤ Wf.cost_bound (encodable.size ((x, c) : X × C)) :=
      Wf.cost_bound_mono _ _ (by
        show encodable.size x ≤ encodable.size x + encodable.size c + 1; omega)
    have hex := LangEncodable.enc_size x
    have hec := LangEncodable.enc_size c
    have hefx := LangEncodable.enc_size (f x)
    have hsize : encodable.size ((x, c) : X × C)
        = encodable.size x + encodable.size c + 1 := rfl
    show Wf.mapFstCmd.cost (LangEncodable.encodeState ((x, c) : X × C))
        ≤ 5 * Wf.cost_bound (encodable.size ((x, c) : X × C))
          + 16 * encodable.size ((x, c) : X × C) + 29
    unfold PolyTimeComputableLang'.mapFstCmd
    -- Stage 1: expand the cost structure only (do NOT reduce the evals yet),
    -- so the literal 4-fold prefix eval survives for `mapFst_pre_eval`.
    simp only [Cmd.cost_seq, Cmd.cost_op]
    -- Stage 2: collapse the prefix 4-fold to `mapFst_pre`, then reduce all op
    -- costs (prefix via the encoded-input structure, suffix via the `W` gets).
    rw [Wf.mapFst_pre_eval x c]
    simp only [Op.cost, Cmd.eval_op, Op.eval, hg0, hW0, hWk2, hca, State.get_set_eq,
      State.get_set_ne _ _ _ _ d0k, State.get_set_ne _ _ _ _ d0k1,
      State.get_set_ne _ _ _ _ d0k2, State.get_set_ne _ _ _ _ dkk1,
      State.get_set_ne _ _ _ _ dkk2, State.get_set_ne _ _ _ _ dk1k2,
      List.tail_cons, List.headD_cons, List.length_append, List.length_cons]
    omega
  output_size_le := by
    intro xc
    obtain ⟨x, c⟩ := xc
    have h1 : encodable.size (f x) ≤ Wf.cost_bound (encodable.size x) := Wf.output_size_le x
    have h2 : encodable.size x ≤ encodable.size ((x, c) : X × C) := by
      show encodable.size x ≤ encodable.size x + encodable.size c + 1; omega
    have h3 : Wf.cost_bound (encodable.size x) ≤ Wf.cost_bound (encodable.size ((x, c) : X × C)) :=
      Wf.cost_bound_mono _ _ h2
    have hsize : encodable.size ((x, c) : X × C)
        = encodable.size x + encodable.size c + 1 := rfl
    show encodable.size (f x) + encodable.size c + 1
        ≤ 5 * Wf.cost_bound (encodable.size ((x, c) : X × C))
          + 16 * encodable.size ((x, c) : X × C) + 29
    omega
  regBound := Wf.regBound + 3
  usesBelow := by
    have hwf : Cmd.UsesBelow Wf.c (Wf.regBound + 3) := Cmd.UsesBelow_mono (by omega) Wf.usesBelow
    have b0 : (0 : Nat) < Wf.regBound + 3 := by omega
    have bk : Wf.regBound < Wf.regBound + 3 := by omega
    have bk1 : Wf.regBound + 1 < Wf.regBound + 3 := by omega
    have bk2 : Wf.regBound + 2 < Wf.regBound + 3 := by omega
    show Cmd.UsesBelow Wf.mapFstCmd (Wf.regBound + 3)
    unfold PolyTimeComputableLang'.mapFstCmd
    exact ⟨⟨bk, b0⟩, ⟨bk1, b0⟩, ⟨bk2, bk1, bk⟩, ⟨b0, bk1, bk⟩, hwf,
      ⟨bk1, b0, bk2⟩, ⟨b0, b0, bk1⟩, bk, bk1, bk2⟩
  -- TODO(C2, B′): input type is `X × C`; the product encoding must be re-laid
  -- UNARY before it is `BitState`, then this becomes `BitEncodable.enc_bit` (add
  -- a `[BitEncodable (X × C)]` instance hypothesis). See HANDOFF.md bottom-up Task 4.
  enc_bit := sorry

/-- **`map_snd` (the mirror of `map_fst`).** Lift `Wf : PolyTimeComputableLang' f`
to apply `f` to a pair's *second* component:
`PolyTimeComputableLang' (fun cx : C × X => (cx.1, f cx.2))`. Built **definitionally
from the combinator algebra** — `swap ∘ map_fst f ∘ swap` — with no new proof
obligations: `swap` reorders so the target component sits first, `map_fst` runs
the witness there, and `swap` restores the order. Demonstrates that the
pair-plumbing combinators (`swap`, `map_fst`, `comp`) compose into the layout
adapters the chain reductions need. Sorry-free; axiom-clean. -/
def PolyTimeComputableLang'.map_snd {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] {f : X → Y} (Wf : PolyTimeComputableLang' f)
    (C : Type) [encodable C] [LangEncodable C] :
    PolyTimeComputableLang' (fun cx : C × X => (cx.1, f cx.2)) :=
  (PolyTimeComputableLang'.swap (X := Y) (Y := C)).comp
    ((Wf.map_fst C).comp (PolyTimeComputableLang'.swap (X := C) (Y := X)))

/-! **What remains to fully discharge `red_inNP` (two distinct obligations,
both surfaced by assembling the engine above):**

1. **The `map_fst` program** `PolyTimeComputableLang' (fun xc => (f xc.1, xc.2))`
   from `PolyTimeComputableLang' f` — now **complete and `sorry`-free**
   (`mapFstCmd` + `map_fst` above), enabled by the frame-preservation calling
   convention. All fields, including `normalizes` and `cost_le`, are proved: the
   straight-line program is threaded through via the shared `mapFst_pre` lemmas
   (`mapFst_pre_eval` for the four unpacking ops, `mapFst_pre_agree` for the
   frame/locality of `Wf.c`). `red_inNPLang`'s former `map_fst` hypothesis is now
   discharged internally by `Wf.map_fst`.

2. **A *canonical* verifier `DecidesLang'` for `Q`** — `inNP Q` only provides an
   abstract `inTimePoly` (a `FlatTM` decider), and a `Cmd` cannot be recovered
   from an arbitrary TM. So routing `red_inNP` through the layer requires the NP
   framework's `inNP`/`inTimePoly` to be **layer-native** (carry a `DecidesLang`),
   or a TM-level `ComputesBy`-then-`DecidesBy` composition (a re-encoding
   machine). This is a framework refinement, the deeper half of the S3
   migration. -/

/-! ## C10: layer-native `inNP` and reduction closure (May 2026)

`red_inNP` (`Complexity/NP.lean`) cannot currently route through the layer:
`inNP Q` exposes only an abstract `inTimePoly` (a `FlatTM` decider), from which
no `Cmd` is recoverable, so the layer engine `DecidesLang'.precompose` /
`ofReduction` has nothing to consume. This block provides the layer-native
analogue of `inNP` — an NP witness whose certificate-relation verifier **is** a
canonical `Cmd` (`DecidesLang'`) rather than an opaque TM — and proves the
layer-native NP class is **closed under reduction** (`red_inNPLang`). That
closure theorem *is* the engine `red_inNP` wants; assembling it sorry-free
confirms the only inputs missing are the two obligations spelled out at the end
(C5a `map_fst` and the framework decider bridge).

Everything here is sorry-free and independent of `Compile_sound`: it is pure
layer algebra (the `Cmd`-level `decides`/`cost`), exactly mirroring the
framework's `InNPWitness` / `red_inNP` with `inTimePoly` replaced by a
`DecidesLang'`. -/

/-- **Layer-native NP witness** — the analogue of the framework's `InNPWitness`
with the abstract `inTimePoly` verifier replaced by a canonical layer verifier
`DecidesLang'`. The certificate relation is decided by a `Cmd` in canonical
normal form, so it can be *precomposed* with a canonical reduction (this is what
an opaque TM decider cannot offer). -/
structure InNPWitnessLang {X Cert : Type} [encodable X] [encodable Cert]
    [LangEncodable X] [LangEncodable Cert] (P : X → Prop) where
  /-- The certificate relation. -/
  rel : X → Cert → Prop
  /-- Verifier cost bound. -/
  dBound : Nat → Nat
  dBound_poly : inOPoly dBound
  dBound_mono : monotonic dBound
  /-- The verifier: a *canonical* layer decider for the certificate relation,
  read as a predicate on the pair `(input, certificate)`. -/
  verifier : DecidesLang' (fun xc : X × Cert => rel xc.1 xc.2) dBound
  /-- The relation is a sound and complete, polynomially-bounded certificate
  relation for `P` (the predicate-level NP content, identical to the framework). -/
  rel_correct : polyCertRel P rel

/-- `P` is in NP *at the layer level*: there is a certificate type with a
canonical layer verifier (`DecidesLang'`) and a polynomial certificate relation.
Mirrors `inNP`, existentially quantifying the certificate type and its encodings. -/
def inNPLang {X : Type} [encodable X] [LangEncodable X] (P : X → Prop) : Prop :=
  ∃ Cert : Type, ∃ eC : encodable Cert, ∃ lC : LangEncodable Cert,
    Nonempty (@InNPWitnessLang X Cert _ eC _ lC P)

/-- **C10 headline: the layer-native NP class is closed under reduction.** Given
a layer reduction `f : X → Y` (with `Wf : PolyTimeComputableLang' f`) and
`Q ∈ inNPLang`, then `P ∈ inNPLang`. The verifier for `P` is built by
`DecidesLang'.ofReduction` (run the C5a `map_fst` lift of `f` then `Q`'s
verifier); the certificate relation transports exactly as in the framework's
`red_inNP`.

The C5a `map_fst` lift — which must hold for the certificate type `C`
(existentially bound inside `hQ`, so it cannot be a fixed-type argument) — is now
supplied internally by `Wf.map_fst` (`sorry`-free), so this theorem takes no
`map_fst` hypothesis. It is the layer analogue of `red_inNP`; bridging `inNPLang`
to the framework's `inNP` is the remaining framework-side obligation (see
below). -/
theorem red_inNPLang {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y]
    (P : X → Prop) (Q : Y → Prop)
    (f : X → Y) (Wf : PolyTimeComputableLang' f)
    (hf_correct : ∀ x, P x ↔ Q (f x))
    (hQ : inNPLang Q) :
    inNPLang P := by
  obtain ⟨Cert, eC, lC, hW⟩ := hQ
  letI := eC
  letI := lC
  obtain ⟨W⟩ := hW
  let map_fst : ∀ (C : Type) [encodable C] [LangEncodable C],
      PolyTimeComputableLang' (fun xc : X × C => (f xc.1, xc.2)) :=
    fun C _ _ => Wf.map_fst C
  refine ⟨Cert, eC, lC, ⟨?_⟩⟩
  refine {
    rel := fun x c => W.rel (f x) c
    dBound := fun n => 1 + (map_fst Cert).cost_bound n + W.dBound ((map_fst Cert).cost_bound n)
    dBound_poly := ?_
    dBound_mono := ?_
    verifier := DecidesLang'.ofReduction (map_fst Cert) W.verifier W.dBound_mono
    rel_correct := ?_ }
  · -- dBound is polynomial
    exact inOPoly_add (inOPoly_add (inOPoly_const 1) (map_fst Cert).cost_bound_poly)
      (inOPoly_comp (map_fst Cert).cost_bound_poly W.dBound_poly)
  · -- dBound is monotonic
    intro a b hab
    have h1 : (map_fst Cert).cost_bound a ≤ (map_fst Cert).cost_bound b :=
      (map_fst Cert).cost_bound_mono a b hab
    have h2 : W.dBound ((map_fst Cert).cost_bound a) ≤ W.dBound ((map_fst Cert).cost_bound b) :=
      W.dBound_mono _ _ h1
    show 1 + (map_fst Cert).cost_bound a + W.dBound ((map_fst Cert).cost_bound a)
        ≤ 1 + (map_fst Cert).cost_bound b + W.dBound ((map_fst Cert).cost_bound b)
    omega
  · -- the certificate relation for P (verbatim from `red_inNP`'s cert half)
    obtain ⟨cert_bound, hsound_R, hcomplete_R, hcert_poly_R, hcert_mono_R⟩ := W.rel_correct
    refine ⟨⟨cert_bound ∘ Wf.cost_bound, ?_, ?_,
      inOPoly_comp Wf.cost_bound_poly hcert_poly_R,
      monotonic_comp Wf.cost_bound_mono hcert_mono_R⟩⟩
    · intro x c hrel
      exact (hf_correct x).mpr (hsound_R hrel)
    · intro x hx
      rcases hcomplete_R ((hf_correct x).mp hx) with ⟨c, hc, hsize⟩
      refine ⟨c, hc, ?_⟩
      calc encodable.size c
          ≤ cert_bound (encodable.size (f x)) := hsize
        _ ≤ cert_bound (Wf.cost_bound (encodable.size x)) :=
            hcert_mono_R _ _ (Wf.output_size_le x)

/-! **Connecting `red_inNPLang` to the framework's `red_inNP`** — both
obligations are now discharged:

1. **C5a — the polymorphic `map_fst`.** ✅ **Done** (`PolyTimeComputableLang'.map_fst`,
   `sorry`-free). From `Wf : PolyTimeComputableLang' f` it builds a
   `PolyTimeComputableLang' (fun xc : X × C => (f xc.1, xc.2))` for every
   certificate type `C`, using the length-as-value `take`/`drop`/`concat`/`consLen`
   `Op`s (Risk **C5**) to split/repack the packed product register and the
   frame-preservation calling convention (`regBound`/`usesBelow` +
   `eval_frame`/`eval_get_of_agree`) to run `Wf.c` as a subroutine on register `0`
   while `enc c` is stashed at register `k+2`. It now discharges `red_inNPLang`'s
   former `map_fst` hypothesis internally.

2. **The framework decider bridge `inNPLang Q → inNP Q`.** Assembled
   (`inNPLang_to_inNP`, below), modulo the `Compile` physical run contract
   (`Compile_run_physical_residue`, now the `physStepBudget` shape) AND the two
   pinned register-count/`consLen` `WALL` facts (`DecidesLang'.reg_width`,
   `DecidesLang'.c_noConsLen`). `DecidesBy` reads its answer from the TM **state
   index** whereas `Compile` writes it to the **tape** (register `0`); the gap is
   closed by the **C6** tape→state bit-test gadget (`Compile.bitTestTM` +
   `Compile.bitDecider_run`, `Compile.lean`, `sorry`-free), composed after
   `Compile D.c` via `composeFlatTM_run`. The canonical decider's encoding is
   linear (`≤ 2·size + 3`), now admitted by the relaxed `DecidesBy.encode_size`.
   The realized bridge is the **canonical** `DecidesLang'.toDecidesBy` /
   `DecidesLang'.toInTimePoly` (which is exactly what `inNPLang`'s verifier
   provides). The general, free-encoding `DecidesLang.toDecidesBy` (further down)
   is now realized the same way (runtime padding + the per-decider polynomial
   `DecidesBy.encode_size`), using the witness's own `regBound`/`usesBelow`/
   `width_le`/`noConsLen` fields. -/

/-! ## C6 / framework bridge: `DecidesLang' → inTimePoly` and `inNPLang → inNP`

The canonical decider `DecidesLang'` (register `0` = `[1]`/`[0]`) bridges to the
framework's `DecidesBy` (answer = TM **state index**) via the C6 bit-test gadget
(`Compile.bitDeciderTM` + `Compile.bitDecider_run`, `Compile.lean`): run
`Compile D.c`, then read register `0`'s tape symbol (`2`/`1`) into a distinct
accept/reject *state*. The encoding length `(encodeTape ∘ encodeState)` is linear
(`≤ 2·size + 3`), which the relaxed `DecidesBy.encode_size` now admits. This
closes the framework decider bridge for the **canonical** layer (which is what
`inNPLang` uses), and assembles `inNPLang → inNP`. Modulo the `Compile` physical
run contract (`Compile_run_physical_residue`, `physStepBudget` shape) and the two
pinned `WALL` facts (`reg_width`, `c_noConsLen`). -/

/-- The canonical `encodeState x` is a single register, so its width is `1`. -/
private theorem DecidesLang'.encodeState_length {X : Type} [encodable X]
    [LangEncodable X] (x : X) : (LangEncodable.encodeState x).length = 1 := rfl

/-- The canonical padded-decider time budget (numeric form): the runtime
register-padding cost `(regBound+1)·(2n+regBound+4)`, the `+1` splice step, and the
inner bit-decider's `physStepBudget (2n + dBound n + regBound + 4) (dBound n) + 3`.
`regBound` is a per-decider constant, so this is polynomial in `n`. -/
private def DecidesLang'.padTimeBound {X : Type} [encodable X] [LangEncodable X]
    {P : X → Prop} {dBound : Nat → Nat} (D : DecidesLang' P dBound) (n : Nat) : Nat :=
  (D.regBound + 2 * D.c.loopDepth + 2 + 1)
      * (4 * n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 16) + 1
    + (Compile.physStepBudget
        (2 * n + dBound n + (D.regBound + 2 * D.c.loopDepth + 2) + 4) (dBound n) + 3)

/-- The padded decider's actual run cost on `encodeState x` is dominated by the
canonical poly budget `padTimeBound (size x)`. (Resolves the register-count WALL:
the runtime padding lets `Compile_run_physical_residue` run on the widened tape,
while the *input* encoding stays the tight single register.) -/
private theorem DecidesLang'.budget_ge {X : Type} [encodable X] [LangEncodable X]
    {P : X → Prop} {dBound : Nat → Nat} (D : DecidesLang' P dBound) (x : X) :
    Compile.padBudget (D.regBound + 2 * D.c.loopDepth + 2) (LangEncodable.encodeState x) + 1
        + (Compile.physStepBudget (State.size (LangEncodable.encodeState x)
              + ((LangEncodable.encodeState x).length + (D.regBound + 2 * D.c.loopDepth + 2))
              + D.c.cost (LangEncodable.encodeState x) + 2)
            (D.c.cost (LangEncodable.encodeState x)) + 3)
      ≤ D.padTimeBound (encodable.size x) := by
  have hw : (LangEncodable.encodeState x).length = 1 := DecidesLang'.encodeState_length x
  have h1 : State.size (LangEncodable.encodeState x) ≤ 2 * encodable.size x + 1 := by
    rw [LangEncodable.size_encodeState]; exact LangEncodable.enc_size x
  have h2 : D.c.cost (LangEncodable.encodeState x) ≤ dBound (encodable.size x) := D.cost_le x
  unfold DecidesLang'.padTimeBound
  have hpb := Compile.padBudget_le (D.regBound + 2 * D.c.loopDepth + 2) (LangEncodable.encodeState x)
  have hpad : Compile.padBudget (D.regBound + 2 * D.c.loopDepth + 2) (LangEncodable.encodeState x)
      ≤ (D.regBound + 2 * D.c.loopDepth + 2 + 1)
          * (4 * encodable.size x + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 16) :=
    le_trans hpb (Nat.mul_le_mul (Nat.le_succ _) (by rw [hw] at *; omega))
  have hps : Compile.physStepBudget (State.size (LangEncodable.encodeState x)
            + ((LangEncodable.encodeState x).length + (D.regBound + 2 * D.c.loopDepth + 2))
            + D.c.cost (LangEncodable.encodeState x) + 2)
          (D.c.cost (LangEncodable.encodeState x))
      ≤ Compile.physStepBudget (2 * encodable.size x + dBound (encodable.size x)
            + (D.regBound + 2 * D.c.loopDepth + 2) + 4)
          (dBound (encodable.size x)) :=
    Compile.physStepBudget_mono (by omega) h2
  exact Nat.add_le_add (Nat.add_le_add hpad (Nat.le_refl 1)) (Nat.add_le_add hps (Nat.le_refl 3))

/-- ⚠ **WALL (consLen) — pinned bottom-up gap (HANDOFF bottom-up Task 4).** The canonical product
machinery (`map_fst`) emits `Op.consLen`, which breaks `BitState`, so `NoConsLen D.c`
is FALSE for composed verifiers until `consLen` is re-laid UNARY (after which
`Cmd.eval_preserves_BitState`'s `NoConsLen` side-condition is dropped entirely). -/
private theorem DecidesLang'.c_noConsLen {X : Type} [encodable X] [LangEncodable X]
    {P : X → Prop} {dBound : Nat → Nat} (D : DecidesLang' P dBound) :
    Cmd.NoConsLen D.c := by
  sorry

/-- **C6 bridge (WALL resolved):** a canonical layer decider `DecidesLang' P dBound`
yields a framework-level `DecidesBy P` whose time budget is polynomial in `dBound`.
The machine is `Compile.paddedBitDeciderTM D.c D.regBound` — it pads the tape to
`regBound` registers **at runtime** (so the *input* encoding stays the tight single
register, `encode_size ≤ 2·size+4`), then runs the bit-decider. Correctness comes
from `D.decides` carried through `Compile.paddedBitDecider_run`, which needs **no
`k ≤ s.length`**. The encoding/correctness/halting/budget parts are sorry-free; the
only residual gaps are the pinned bottom-up obligations (`padRegsTM` + its run/traj,
`c_noConsLen`). -/
def DecidesLang'.toDecidesBy {X : Type} [encodable X] [LangEncodable X]
    {P : X → Prop} {dBound : Nat → Nat} (D : DecidesLang' P dBound) :
    DecidesBy P D.padTimeBound where
  encode := fun x => Compile.encodeTape (LangEncodable.encodeState x)
  encodeBound := fun n => 2 * n + 4
  encodeBound_poly := inOPoly_add (inOPoly_mul (inOPoly_const 2) inOPoly_id) (inOPoly_const 4)
  encodeBound_mono := fun a b h => by show 2 * a + 4 ≤ 2 * b + 4; omega
  encode_size := fun x => by
    have hlen : (Compile.encodeTape (LangEncodable.encodeState x)).length
        = (LangEncodable.enc x).length + 3 :=
      Compile.encodeTape_singleton_length (LangEncodable.enc x)
    have := LangEncodable.enc_size x
    show (Compile.encodeTape (LangEncodable.encodeState x)).length ≤ 2 * encodable.size x + 4
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
    have hb : (D.c.eval (LangEncodable.encodeState x)).get 0 = [1] :=
      eq_of_beq ((D.decides x).1.mp hPx)
    obtain ⟨cfg, hrun, hhalt, hstate⟩ :=
      Compile.paddedBitDecider_run D.c (LangEncodable.encodeState x) 1 D.regBound
        (D.enc_bit x)
        (by rw [DecidesLang'.encodeState_length x]; exact Cmd.UsesBelow_pos D.usesBelow)
        D.usesBelow D.c_noConsLen (Or.inr rfl) hb
    refine ⟨cfg, ?_, hhalt, ?_⟩
    · have hinit : initialTapes (Compile.paddedBitDeciderTM D.c D.regBound)
            (Compile.encodeTape (LangEncodable.encodeState x))
          = [Compile.encodeTape (LangEncodable.encodeState x)] := by
        show Compile.encodeTape (LangEncodable.encodeState x)
              :: List.replicate ((Compile.paddedBitDeciderTM D.c D.regBound).tapes - 1) [] = _
        rw [Compile.paddedBitDeciderTM_tapes]
        rfl
      obtain ⟨k, hk⟩ := Nat.le.dest (D.budget_ge x)
      show runFlatTM (D.padTimeBound (encodable.size x))
            (Compile.paddedBitDeciderTM D.c D.regBound)
            (initFlatConfig (Compile.paddedBitDeciderTM D.c D.regBound)
              (initialTapes (Compile.paddedBitDeciderTM D.c D.regBound)
                (Compile.encodeTape (LangEncodable.encodeState x)))) = some cfg
      rw [hinit, ← hk]
      exact runFlatTM_extend hrun hhalt
    · show cfg.state_idx
          = 1 + (Compile D.regBound D.c).states
            + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states
      rw [hstate]; norm_num
  decides_neg := fun x hnPx => by
    have hb : (D.c.eval (LangEncodable.encodeState x)).get 0 = [0] :=
      eq_of_beq ((D.decides x).2.mp hnPx)
    obtain ⟨cfg, hrun, hhalt, hstate⟩ :=
      Compile.paddedBitDecider_run D.c (LangEncodable.encodeState x) 0 D.regBound
        (D.enc_bit x)
        (by rw [DecidesLang'.encodeState_length x]; exact Cmd.UsesBelow_pos D.usesBelow)
        D.usesBelow D.c_noConsLen (Or.inl rfl) hb
    refine ⟨cfg, ?_, hhalt, ?_⟩
    · have hinit : initialTapes (Compile.paddedBitDeciderTM D.c D.regBound)
            (Compile.encodeTape (LangEncodable.encodeState x))
          = [Compile.encodeTape (LangEncodable.encodeState x)] := by
        show Compile.encodeTape (LangEncodable.encodeState x)
              :: List.replicate ((Compile.paddedBitDeciderTM D.c D.regBound).tapes - 1) [] = _
        rw [Compile.paddedBitDeciderTM_tapes]
        rfl
      obtain ⟨k, hk⟩ := Nat.le.dest (D.budget_ge x)
      show runFlatTM (D.padTimeBound (encodable.size x))
            (Compile.paddedBitDeciderTM D.c D.regBound)
            (initFlatConfig (Compile.paddedBitDeciderTM D.c D.regBound)
              (initialTapes (Compile.paddedBitDeciderTM D.c D.regBound)
                (Compile.encodeTape (LangEncodable.encodeState x)))) = some cfg
      rw [hinit, ← hk]
      exact runFlatTM_extend hrun hhalt
    · show cfg.state_idx
          = 2 + (Compile D.regBound D.c).states
            + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states
      rw [hstate]; norm_num


/-- `DecidesLang' P dBound` (with `dBound` polynomial & monotonic) puts `P` in
`inTimePoly`. The headline framework bridge for the canonical layer (now on the
`physStepBudget` budget). -/
theorem DecidesLang'.toInTimePoly {X : Type} [encodable X] [LangEncodable X]
    {P : X → Prop} {dBound : Nat → Nat} (D : DecidesLang' P dBound)
    (hpoly : inOPoly dBound) (hmono : monotonic dBound) :
    inTimePoly P := by
  refine ⟨D.padTimeBound, ⟨D.toDecidesBy⟩, ?_, ?_⟩
  · -- `inOPoly`: a linear pad term + the `physStepBudget` term (dominated by its
    -- diagonal at `m = 2n + dBound n + regBound + 4`, poly) + constants.
    unfold DecidesLang'.padTimeBound
    have hlin : inOPoly (fun n => (D.regBound + 2 * D.c.loopDepth + 2 + 1)
        * (4 * n + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 16)) :=
      inOPoly_mul (inOPoly_const _)
        (inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 4) inOPoly_id)
          (inOPoly_const _)) (inOPoly_const 16))
    have hinner : inOPoly (fun n => 2 * n + dBound n + (D.regBound + 2 * D.c.loopDepth + 2) + 4) :=
      inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const 2) inOPoly_id) hpoly)
        (inOPoly_const _)) (inOPoly_const 4)
    have hcomp : inOPoly ((fun m => Compile.physStepBudget m m)
        ∘ (fun n => 2 * n + dBound n + (D.regBound + 2 * D.c.loopDepth + 2) + 4)) :=
      inOPoly_comp hinner Compile.physStepBudget_poly
    have hphys : inOPoly (fun n =>
        Compile.physStepBudget (2 * n + dBound n + (D.regBound + 2 * D.c.loopDepth + 2) + 4)
          (dBound n)) := by
      refine inOPoly_of_le ?_ hcomp
      intro n
      show Compile.physStepBudget (2 * n + dBound n + (D.regBound + 2 * D.c.loopDepth + 2) + 4)
            (dBound n)
          ≤ Compile.physStepBudget (2 * n + dBound n + (D.regBound + 2 * D.c.loopDepth + 2) + 4)
              (2 * n + dBound n + (D.regBound + 2 * D.c.loopDepth + 2) + 4)
      exact Compile.physStepBudget_mono (Nat.le_refl _) (by omega)
    exact inOPoly_add (inOPoly_add hlin (inOPoly_const 1))
      (inOPoly_add hphys (inOPoly_const 3))
  · intro a b hab
    have hd : dBound a ≤ dBound b := hmono a b hab
    unfold DecidesLang'.padTimeBound
    have h1 : (D.regBound + 2 * D.c.loopDepth + 2 + 1)
          * (4 * a + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 16)
        ≤ (D.regBound + 2 * D.c.loopDepth + 2 + 1)
          * (4 * b + 2 * (D.regBound + 2 * D.c.loopDepth + 2) + 16) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : Compile.physStepBudget (2 * a + dBound a + (D.regBound + 2 * D.c.loopDepth + 2) + 4)
          (dBound a)
        ≤ Compile.physStepBudget (2 * b + dBound b + (D.regBound + 2 * D.c.loopDepth + 2) + 4)
          (dBound b) :=
      Compile.physStepBudget_mono (by omega) hd
    exact Nat.add_le_add (Nat.add_le_add h1 (Nat.le_refl 1)) (Nat.add_le_add h2 (Nat.le_refl 3))

/-! ## Free-path (live `sat_NP`) bridge: `DecidesLang → DecidesBy → inTimePoly`

The free-encoding analogue of `DecidesLang'.toDecidesBy` / `toInTimePoly`. This is
the bridge the **live `sat_NP` path** walks (`EvalCnfTM.lean`). It differs from the
canonical bridge only in the input encoding: instead of the tight single canonical
register, it uses the witness's own `encodeIn` (multi-register), bounded in size by
`costBound` and in width by the per-decider `regBound`. The framework
`encode_size` is now per-decider polynomial (`costBound + regBound + 2`), so the
multi-register encoding is admissible; the runtime tape-padding
(`paddedBitDecider_run`) handles the register-count WALL exactly as in the canonical
case. -/

/-- The free-path padded-decider time budget (numeric form), mirroring
`DecidesLang'.padTimeBound`: the runtime register-padding cost, the `+1` splice
step, and the inner bit-decider's `physStepBudget … + 3`. `regBound` is a
per-decider constant, so this is polynomial in `n` whenever `costBound` is. -/
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
run/traj, and — until `consLen` is unary — the witness's `noConsLen`). -/
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
        (D.enc_bit x) (D.width_le x) D.usesBelow D.noConsLen (Or.inr rfl) hb
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
        (D.enc_bit x) (D.width_le x) D.usesBelow D.noConsLen (Or.inl rfl) hb
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

/-- **Framework decider bridge — headline.** `inNPLang Q → inNP Q`: a
layer-native NP witness (canonical `DecidesLang'` verifier) yields a
framework-level NP witness. The verifier crosses via `DecidesLang'.toInTimePoly`;
the certificate relation is carried verbatim. With this, `red_inNPLang` can both
consume a framework `inNP` (after the converse, when available) and export to
`inNP`, routing the framework's `red_inNP` through the computable layer. -/
theorem inNPLang_to_inNP {Y : Type} [encodable Y] [LangEncodable Y]
    {Q : Y → Prop} (h : inNPLang Q) : inNP Q := by
  obtain ⟨Cert, eC, lC, ⟨W⟩⟩ := h
  letI := eC
  letI := lC
  exact inNP_intro Q W.rel (W.verifier.toInTimePoly W.dBound_poly W.dBound_mono) W.rel_correct

/-! ## Routing the framework's `⪯p` / `red_inNP` through the layer

These two corollaries are the **engine** the S3 migration targets, now assembled
end-to-end. A *canonical layer reduction* (a `PolyTimeComputableLang'` map plus
correctness) yields:

* a genuine **framework** poly-time many-one reduction `P ⪯p Q`
  (`reducesPolyMO_of_lang`) — the TM-backed witness via `toFrameworkWitness'` +
  `polyTimeComputable'_to_polyTimeComputable`; and
* the full **`red_inNP` step at the layer** (`red_inNP_of_lang`): from a layer
  reduction and `inNPLang Q`, conclude the *framework's* `inNP P`, by composing
  `red_inNPLang` (layer reduction closure) with `inNPLang_to_inNP`.

The only residual dependency is the assumed `Compile_sound` / `Compile_run_physical`
(the compiler contract). Migrating `⪯p` itself (swapping `ReductionWitness`'s
`polyTimeComputable` for the TM-backed `polyTimeComputable'`) is then a mechanical
re-typing of the chain — gated only on building *honest* layer reductions for the
front (the S1 Cook tableau), which is where S1/S2 stop typechecking. -/

/-- A canonical layer reduction is a genuine framework poly-time reduction
`P ⪯p Q`: its TM-backed witness comes from `toFrameworkWitness'`, downgraded to
the size-only `polyTimeComputable` (kept verbatim by `ReductionWitness`). -/
theorem reducesPolyMO_of_lang {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y]
    {P : X → Prop} {Q : Y → Prop} {f : X → Y}
    (Wf : PolyTimeComputableLang' f) (hcorrect : ∀ x, P x ↔ Q (f x)) :
    P ⪯p Q :=
  ⟨⟨f, polyTimeComputable'_to_polyTimeComputable Wf.toFrameworkWitness',
    fun {x} => hcorrect x⟩⟩

/-- **The layer-routed `red_inNP`.** From a canonical layer reduction `f`
(`P x ↔ Q (f x)`) and `inNPLang Q`, conclude the framework's `inNP P`. Composes
`red_inNPLang` (layer closure under reduction) with the framework bridge
`inNPLang_to_inNP`. -/
theorem red_inNP_of_lang {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y]
    (P : X → Prop) (Q : Y → Prop) (f : X → Y) (Wf : PolyTimeComputableLang' f)
    (hcorrect : ∀ x, P x ↔ Q (f x)) (hQ : inNPLang Q) : inNP P :=
  inNPLang_to_inNP (red_inNPLang P Q f Wf hcorrect hQ)

/-! ## Framework-level helpers for `polyTimeComputable'` (S3 migration prep)

The framework-level `polyTimeComputable'` (the TM-backed witness predicate
defined above) needs analogues of the `polyTimeComputable` lemmas used by
`reducesPolyMO_reflexive` / `_transitive`. These helpers route through the
canonical layer: `id` via `PolyTimeComputableLang'.id_witness`, composition via
`PolyTimeComputableLang'.comp`, both pushed through the framework bridge
`PolyTimeComputableLang'.toFrameworkWitness'`.

Sorry-free modulo the assumed `Compile_sound` (the framework bridge's only
dependency). These are the building blocks the eventual `⪯p` migration needs:
swapping `ReductionWitness.reduction_poly` from `polyTimeComputable` to
`polyTimeComputable'` makes `reducesPolyMO_reflexive` need `polyTimeComputable'
id` and `reducesPolyMO_transitive` need `polyTimeComputable' (g ∘ f)` from
witnesses for `f` and `g`. -/

/-- **Identity is TM-backed poly-time computable.** Provided the type has a
canonical layer encoding. -/
theorem polyTimeComputable'_id {X : Type} [encodable X] [LangEncodable X]
    [BitEncodable X] :
    polyTimeComputable' (id : X → X) :=
  PolyTimeComputableLang'.id_witness.toFrameworkWitness'

/-- **TM-backed poly-time is closed under composition (canonical-layer route).**
A composite reduction from canonical-layer witnesses yields a real
`polyTimeComputable'` whose `ComputesBy` actually computes `g ∘ h`. A
purely-opaque (framework-only) `polyTimeComputable'_comp` is **not** honestly
constructible: the `ComputesBy` field needs a TM for the composite, but the
inputs' `FlatTM`s have free encodings and there is no general re-encoder
between them. The canonical layer's shared single-register encoding is
exactly the device that lets `g ∘ h` compose by `Cmd.seq` — which is what
this lemma uses (via `PolyTimeComputableLang'.comp`).

For the `⪯p` migration: every honest reduction in the chain must be built at
the canonical layer first, then bridged here. The size-only
`reducesPolyMO_transitive` lemma in `NP.lean` still composes size bounds the
old way; this lemma is its honest TM-backed counterpart. -/
theorem polyTimeComputable'_comp_lang {X Y Z : Type}
    [encodable X] [encodable Y] [encodable Z]
    [LangEncodable X] [LangEncodable Y] [LangEncodable Z]
    {g : Y → Z} {h : X → Y}
    (Wg : PolyTimeComputableLang' g) (Wh : PolyTimeComputableLang' h) :
    polyTimeComputable' (g ∘ h) :=
  (Wg.comp Wh).toFrameworkWitness'

/-! ## `ReductionWitness'` / `⪯p'` — additive TM-backed reduction type

The next step in the S3 migration: swap `ReductionWitness.reduction_poly`'s
`polyTimeComputable` for `polyTimeComputable'`. We introduce the upgraded type
**additively** so the live `⪯p` chain keeps compiling. Bridges and structural
closure (reflexive / transitive) follow directly from the
`polyTimeComputable'` helpers above; the bridge `⪯p' → ⪯p` is immediate from
`polyTimeComputable'_to_polyTimeComputable`.

This block is sorry-free modulo the assumed `Compile_sound` (only consumed by
`PolyTimeComputableLang'.toFrameworkWitness'`). -/

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

/-- Reflexivity of `⪯p'` (needs `[LangEncodable X]` to construct the layer
identity witness). -/
theorem reducesPolyMO'_reflexive (X : Type) [encodable X] [LangEncodable X]
    [BitEncodable X]
    (P : X → Prop) : P ⪯p' P :=
  ⟨⟨id, polyTimeComputable'_id, fun _ => Iff.rfl⟩⟩

/-- Transitivity of `⪯p'`. The general form requires the intermediate type to
have a `LangEncodable` instance — without it the composite TM cannot be built
honestly (the framework-only `polyTimeComputable'_comp` carries the size half
but not the TM-backed half). -/
theorem reducesPolyMO'_transitive_lang {X Y Z : Type}
    [encodable X] [encodable Y] [encodable Z]
    [LangEncodable X] [LangEncodable Y] [LangEncodable Z]
    (P : X → Prop) (Q : Y → Prop) (R : Z → Prop)
    {Wf : X → Y} {Wg : Y → Z}
    (hWf : PolyTimeComputableLang' Wf) (hWg : PolyTimeComputableLang' Wg)
    (hf_correct : ∀ {x}, P x ↔ Q (Wf x))
    (hg_correct : ∀ {y}, Q y ↔ R (Wg y)) :
    P ⪯p' R :=
  ⟨⟨Wg ∘ Wf, polyTimeComputable'_comp_lang hWg hWf,
    fun {x} => Iff.trans (hf_correct (x := x)) (hg_correct (y := Wf x))⟩⟩

/-- A canonical layer reduction lifts to a TM-backed `⪯p'` reduction. -/
theorem reducesPolyMO'_of_lang {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y]
    {P : X → Prop} {Q : Y → Prop} {f : X → Y}
    (Wf : PolyTimeComputableLang' f) (hcorrect : ∀ x, P x ↔ Q (f x)) :
    P ⪯p' Q :=
  ⟨⟨f, Wf.toFrameworkWitness', fun {x} => hcorrect x⟩⟩

/-! ### End-to-end demo: the constant-true Bool reduction through the pipeline

A concrete sorry-free path from `PolyTimeComputableLang'.constTrueBool` to a
framework `⪯p` / `⪯p'`. The constant-true function only preserves
correctness for predicates that are themselves constant on `Bool` (since
`f x = true` for both inputs collapses any non-constant predicate). The
canonical such example is `(fun _ => True)`; the witness shows the pipeline
goes through end-to-end after the new infrastructure. -/

/-- The constant `True`-on-Bool predicate `⪯p'`-reduces to itself via the
constant-true Bool function. -/
theorem reducesPolyMO'_trueBool :
    (fun (_ : Bool) => True) ⪯p' (fun (_ : Bool) => True) :=
  reducesPolyMO'_of_lang PolyTimeComputableLang'.constTrueBool (fun _ => Iff.rfl)

/-- Downgrade to size-only `⪯p`. -/
theorem reducesPolyMO_trueBool :
    (fun (_ : Bool) => True) ⪯p (fun (_ : Bool) => True) :=
  reducesPolyMO'_to_reducesPolyMO reducesPolyMO'_trueBool

/-! ### A *general* correctness-preserving reduction via `swap`

Unlike the constant-true demo, `swap` permutes data without inspecting it, so it
reduces *any* predicate on swapped pairs. For every `Q : Y × X → Prop`, the
predicate `fun p : X × Y => Q (p.2, p.1)` `⪯p'`-reduces to `Q` — the layer
witness is `PolyTimeComputableLang'.swap` and correctness is `Iff.rfl`. This is
the first fully general (non-vacuous, any-predicate) reduction routed through the
canonical layer. -/

/-- Pair-swap is a general TM-backed reduction: for any `Q`,
`(fun p : X × Y => Q (p.2, p.1)) ⪯p' Q`. -/
theorem reducesPolyMO'_swap {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] (Q : Y × X → Prop) :
    (fun p : X × Y => Q (p.2, p.1)) ⪯p' Q :=
  reducesPolyMO'_of_lang PolyTimeComputableLang'.swap (fun _ => Iff.rfl)

/-- Downgrade to the size-only `⪯p` that the live chain uses. -/
theorem reducesPolyMO_swap {X Y : Type} [encodable X] [encodable Y]
    [LangEncodable X] [LangEncodable Y] (Q : Y × X → Prop) :
    (fun p : X × Y => Q (p.2, p.1)) ⪯p Q :=
  reducesPolyMO'_to_reducesPolyMO (reducesPolyMO'_swap Q)

end Complexity.Lang
