import Complexity.Complexity.Definitions
import Complexity.Complexity.MachineSemantics

set_option autoImplicit false

/-! **`PolyTimeComputableWitness` / `polyTimeComputable` were DELETED
(2026-08-03), with the rest of the `⪯p` API at the bottom of this file.**

The structure bounded only the reduction's **output size** — nothing about
computing it — while being named as though it bounded time. Its four fields
(`bound`/`bound_poly`/`bound_mono`/`bound_valid`) live on, inlined into
`Lang.PolyTimeComputableWitness'`, which is the honest thing: an output-size
bound *plus* a real `FlatTM` computing `f` inside a polynomial time bound. -/

/-! ## TM-backed decision interface (Part 2, Step 4 onwards)

A `DecidesBy P timeBound` witness is a multi-tape `FlatTM` that, on
the encoded input `encode x`, halts within
`timeBound (encodable.size x)` steps in a designated `acceptState`
(when `P x` holds) or `rejectState` (otherwise). The two output
codes must be distinct so the answer carries information.

The new `inTimePoly` (below) is a strict upgrade of the old
propositional `HasDecider` predicate — a `DecidesBy` witness pins
down a real Turing machine. -/

/-- The standard initial tape list for a decider: the encoded input on
tape 0, all other tapes blank. -/
def initialTapes (M : FlatTM) (input : List Nat) : List (List Nat) :=
  input :: List.replicate (M.tapes - 1) []

theorem initialTapes_length (M : FlatTM) (input : List Nat) (h : 0 < M.tapes) :
    (initialTapes M input).length = M.tapes := by
  show (input :: List.replicate (M.tapes - 1) []).length = M.tapes
  rw [List.length_cons, List.length_replicate]
  exact Nat.sub_add_cancel h

/-- Read the Boolean output of a halting configuration: `true` iff the
final state is the designated `acceptState`. -/
def readOutput (acceptState : Nat) (cfg : FlatTMConfig) : Bool :=
  decide (cfg.state_idx = acceptState)

/-- A TM-backed decision witness for a predicate `P : X → Prop` with
time budget `timeBound : Nat → Nat`. The TM may use multiple tapes:
tape 0 holds the encoded input, remaining tapes start empty. For
single-tape TMs (`M.tapes = 1`), `initialTapes` collapses to
`[encode x]` definitionally. -/
structure DecidesBy {X : Type} [encodable X]
    (P : X → Prop) (timeBound : Nat → Nat) where
  /-- How to lay the input out on tape 0. -/
  encode      : X → List Nat
  /-- A monotone polynomial bounding the encoded-input length. -/
  encodeBound : Nat → Nat
  /-- The encoding bound is a polynomial. -/
  encodeBound_poly : inOPoly encodeBound
  /-- The encoding bound is monotone (so derived deciders — `proj_left`, the
  product lift — propagate `encode_size` by monotonicity alone). -/
  encodeBound_mono : monotonic encodeBound
  /-- The encoded input length is **polynomially** bounded by `encodable.size x`.
  This is the principled "poly-size encoding" requirement of complexity theory: a
  poly-size encoding processed in poly *time* (`timeBound`) is faithful. It is
  *per-decider* (each witness supplies its own `encodeBound`) rather than the old
  globally-fixed linear `2 · size + 4`, so encodings whose width is more than the
  tight single canonical register — e.g. the live `sat_NP` verifier's multi-register
  `EvalCnfCmd.encodeState` (`≤ 5 · size + 20`), or any future super-linear
  reduction-chain / tableau encoding — are admissible without another framework
  change. The canonical single-register layer (`DecidesLang'`) still uses the
  linear instance `encodeBound n = 2 · n + 4`. -/
  encode_size : ∀ x, (encode x).length ≤ encodeBound (encodable.size x)
  /-- The underlying flat Turing machine. -/
  M           : FlatTM
  /-- It is a well-formed TM. -/
  M_valid     : validFlatTM M
  /-- The machine has at least one tape (the input tape). -/
  M_tapes_pos : 0 < M.tapes
  /-- Halting state index that signals `true`. -/
  acceptState : Nat
  /-- Halting state index that signals `false`. -/
  rejectState : Nat
  /-- `acceptState` is in fact a halting state. -/
  halting_acc : M.halt.getD acceptState false = true
  /-- `rejectState` is in fact a halting state. -/
  halting_rej : M.halt.getD rejectState false = true
  /-- The two output codes are different — without this the output
  carries no information. -/
  accept_ne_reject : acceptState ≠ rejectState
  /-- If `P x` holds, the machine reaches `acceptState` in budget. -/
  decides_pos : ∀ x, P x → ∃ cfg,
    runFlatTM (timeBound (encodable.size x)) M
        (initFlatConfig M (initialTapes M (encode x))) = some cfg ∧
      haltingStateReached M cfg = true ∧
      cfg.state_idx = acceptState
  /-- If `¬ P x` holds, the machine reaches `rejectState` in budget. -/
  decides_neg : ∀ x, ¬ P x → ∃ cfg,
    runFlatTM (timeBound (encodable.size x)) M
        (initFlatConfig M (initialTapes M (encode x))) = some cfg ∧
      haltingStateReached M cfg = true ∧
      cfg.state_idx = rejectState

/-- Phase-2 polynomial-time bookkeeping. Requires an actual
TM-backed decider with a polynomial time bound.

(The legacy propositional `HasDecider` predicate was deleted in
Step 9 of `PART2.md` v2 once its last consumer — `hasDeciderClassical`
— was retyped to produce `Nonempty (DecidesBy ...)` directly.) -/
def inTimePoly {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ f : Nat → Nat, Nonempty (DecidesBy P f) ∧ inOPoly f ∧ monotonic f

/-- A witness that `R` behaves like a certificate relation for `P`: witnesses
are sound for `P`, and every positive instance of `P` has some witness with
polynomially bounded size. -/
structure PolyCertRelWitness {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) (R : X → Y → Prop) where
  bound : Nat → Nat
  sound : ∀ ⦃x y⦄, R x y → P x
  complete : ∀ ⦃x⦄, P x → ∃ y, R x y ∧ encodable.size y ≤ bound (encodable.size x)
  bound_poly : inOPoly bound
  bound_mono : monotonic bound

abbrev polyCertRel {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) (R : X → Y → Prop) : Prop :=
  Nonempty (PolyCertRelWitness P R)

/-- A witness that `P` is in NP: an encodable certificate type together with a
polynomially bounded certificate relation that is sound and complete for `P`. -/
structure InNPWitness {X Y : Type} [encodable X] [encodable Y] (P : X → Prop) where
  rel : X → Y → Prop
  rel_poly : inTimePoly (fun xy : X × Y => rel xy.1 xy.2)
  rel_correct : polyCertRel P rel

abbrev inNP {X : Type} [encodable X] (P : X → Prop) : Prop :=
  ∃ Y : Type, ∃ _ : encodable Y, Nonempty (@InNPWitness X Y _ _ P)

theorem inNP_intro {X Y : Type} [encodable X] [encodable Y]
    (P : X → Prop) (R : X → Y → Prop)
    (hPoly : inTimePoly (fun xy : X × Y => R xy.1 xy.2))
    (polyCert : polyCertRel P R) :
    inNP P := by
  exact ⟨Y, inferInstance, ⟨⟨R, hPoly, polyCert⟩⟩⟩

def inP (X : Type) [encodable X] (P : X → Prop) : Prop := inTimePoly P

/-- Lift a `DecidesBy P f` (on `X`) to a decider for the predicate
`fun (xy : X × Unit) => P xy.1`. The underlying TM and time bound
are unchanged; only the encoder threads through the projection. -/
private def DecidesBy.proj_left {X : Type} [encodable X]
    {P : X → Prop} {f : Nat → Nat}
    (D : DecidesBy P f) (hMono : monotonic f) :
    DecidesBy (fun xy : X × Unit => P xy.1) f where
  encode xy := D.encode xy.1
  encodeBound := D.encodeBound
  encodeBound_poly := D.encodeBound_poly
  encodeBound_mono := D.encodeBound_mono
  encode_size xy := by
    have hsize : encodable.size xy.1 ≤ encodable.size xy := by
      show encodable.size xy.1 ≤ encodable.size xy.1 + encodable.size xy.2 + 1
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
    exact Nat.le_trans (D.encode_size xy.1) (D.encodeBound_mono _ _ hsize)
  M := D.M
  M_valid := D.M_valid
  M_tapes_pos := D.M_tapes_pos
  acceptState := D.acceptState
  rejectState := D.rejectState
  halting_acc := D.halting_acc
  halting_rej := D.halting_rej
  accept_ne_reject := D.accept_ne_reject
  decides_pos xy hPxy := by
    -- xy : X × Unit, hPxy : P xy.1
    rcases D.decides_pos xy.1 hPxy with ⟨cfg, hRun, hHalt, hState⟩
    refine ⟨cfg, ?_, hHalt, hState⟩
    -- runFlatTM (f (size xy.1)) M init = some cfg; pad to f (size xy).
    have hsize : encodable.size xy.1 ≤ encodable.size xy := by
      show encodable.size xy.1 ≤ encodable.size xy.1 + encodable.size xy.2 + 1
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
    have hmono : f (encodable.size xy.1) ≤ f (encodable.size xy) := hMono _ _ hsize
    rcases Nat.le.dest hmono with ⟨k, hk⟩
    -- hk : f (encodable.size xy.1) + k = f (encodable.size xy)
    have := runFlatTM_extend (k := k) hRun
        (h_halt := hHalt)
    rw [hk] at this
    exact this
  decides_neg xy hnPxy := by
    rcases D.decides_neg xy.1 hnPxy with ⟨cfg, hRun, hHalt, hState⟩
    refine ⟨cfg, ?_, hHalt, hState⟩
    have hsize : encodable.size xy.1 ≤ encodable.size xy := by
      show encodable.size xy.1 ≤ encodable.size xy.1 + encodable.size xy.2 + 1
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
    have hmono : f (encodable.size xy.1) ≤ f (encodable.size xy) := hMono _ _ hsize
    rcases Nat.le.dest hmono with ⟨k, hk⟩
    have := runFlatTM_extend (k := k) hRun (h_halt := hHalt)
    rw [hk] at this
    exact this

theorem P_NP_incl (X : Type) [encodable X] (P : X → Prop) : inP X P → inNP P := by
  intro hP
  refine inNP_intro (X := X) (Y := Unit) P (fun (x : X) (_ : Unit) => P x) ?_ ?_
  · -- inTimePoly slot: lift the X-decider to an (X × Unit)-decider.
    rcases hP with ⟨f, ⟨D⟩, hf_poly, hf_mono⟩
    exact ⟨f, ⟨D.proj_left hf_mono⟩, hf_poly, hf_mono⟩
  · -- polyCertRel slot: certificate is `()`, bound is 0.
    refine ⟨⟨fun _ => 0, ?_, ?_, ?_, ?_⟩⟩
    · intros _ _ h; exact h
    · intros x hx; exact ⟨(), hx, Nat.zero_le _⟩
    · exact ⟨0, ⟨0, 0, fun _ _ => Nat.zero_le _⟩⟩
    · intros _ _ _; exact Nat.zero_le _

/-! **`red_inNP` was DELETED (2026-07-30-c).** It claimed `P ⪯p Q → inNP Q →
inNP P`, and its `polyCertRel` half really is free (certificate-bound
composition is predicate-level). Its `inTimePoly` half was a `sorry`, and it is
**unclosable honestly**: `⪯p` gives no program for `f`, so the composed verifier
"run `f`, then run `Q`'s verifier" cannot be built — the only way to produce the
`DecidesBy` is `hasDeciderClassical`'s cheat, which is true for *every*
predicate (standing risk #6). The honest, live replacement is
`Lang.red_inNP_of_langFree`: it takes a **free layer reduction witness** (a real
`Cmd` computing `f`) plus a per-seam re-encoder bundle, and composes the two
programs at the `Cmd` level. First live instance:
`KSat3Free.inNP_kSAT3_free`. -/

/-! ## **The `⪯p` API was DELETED (2026-08-03)** — `NPUniversal`,
`ReductionWitness`, `reducesPolyMO` (`⪯p`), `reducesPolyMO_elim`,
`reducesPolyMO_reflexive`, `reducesPolyMO_transitive`, `NPhard`, `NPcomplete`,
`red_NPhard`, `NPhard_subtype_proj`, and with them the nine wrapper theorems
that produced `⪯p` facts from the sound reductions and the three bridges down
from `⪯p'`/`NPhard'`/`NPcomplete'`.

**Why deleted rather than kept "for reference".** `⪯p` bounds only the
reduction's *output size* — never its runtime, and the reduction function need
not even be computable. So `NPhard`/`NPcomplete` as *defined here* were too weak
to be faithful, which is why the legacy headline `CookLevin : NPcomplete SAT`
was deleted on 2026-07-30-c and why there is deliberately **no**
`NPcomplete'' → NPcomplete` bridge. What was left after that was a vacuous
notion with no live consumer sitting next to the honest one, plus bridges whose
only effect was to let a reader derive the vacuous statement from the real one
and mistake it for a result. That is a *reading* hazard, and reading is the only
thing standing between this development and its claim.

The honest replacements, all live:

* `Lang.reducesPolyMO'` (`⪯p'`) — a reduction carrying a real `FlatTM`;
* `Lang.NPhard''` / `Lang.NPcompleteStr` — hardness over problems presented with
  a real verifier, the latter over string languages with the input layout pinned;
* `Lang.PolyTimeComputableLang.SeamData`/`comp` — chain composition at the `Cmd`
  level, which is what replaces `reducesPolyMO_transitive` (there is deliberately
  no generic `⪯p'`-transitivity: two opaque TM-backed witnesses share no layout,
  so no re-encoder is recoverable from them).

The *mathematics* the wrappers wrapped is untouched: every reduction map, its
correctness lemma and its output-size bound (`kSAT_to_SAT_correct`,
`kSAT_to_FlatClique_f_size_bound`, `FSAT_to_SAT_size_le`, …) is still here, and
is what a future `⪯p'` witness for those steps would be built from. -/
