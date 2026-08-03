import Complexity.StatementMeaning
import Complexity.MachineFaithfulness
import Complexity.CostFaithfulness
import Complexity.NonVacuity
import Complexity.HonestyGate

set_option autoImplicit false

/-! # The gate surfaces — *what believing the instruments costs*, measured

## Why this file exists (top-down, 2026-08-08)

`Complexity/StatementGate.lean` proves the reviewer's reading list for the
**headline** is complete. A reviewer is then told six further things, and told
that `lake build` establishes them:

* the library is `sorry`-free and axiom-clean (`Meta/AxiomGate.lean`);
* the two audited functions are what the audit says (`HonestyGate.lean`);
* `Op.cost` is a faithful proxy for machine time (`CostFaithfulness.lean`);
* the hypothesis class is inhabited and contains nothing undecidable
  (`NonVacuity.lean`);
* the reading list is complete (`StatementGate.lean`);
* the checkable verdicts of the audit of that list still hold
  (`StatementMeaning.lean`).

Every one of those is a **theorem whose statement a reviewer must also read**,
and until this file nothing measured those statements. That is the same hole
`StatementGate.lean` closed one level down: an instrument can drift from what it
is advertised to establish, silently, while staying green.

`#assert_statement_surface_delta` (`Meta/StatementSurface.lean`) is the
instrument, because a gate about the headline shares nearly all of the
headline's surface and only the **difference** carries information.

## ★ What the measurement found, and it reorganises the trust list

The instruments split cleanly into two kinds, and the split is not a matter of
taste — it is 0, 1 and 10 additional definitions against 265 and 1045.

**Reading gates** (§2) cost a reviewer who has read the headline almost nothing:
`StatementMeaning`'s restatements cost **zero** — they say nothing the headline
does not — and `NonVacuity`'s deciders cost ten. These can be audited the way
the headline is audited: by reading them.

**Construction gates** (§3) cannot. `Compile.cost_is_time_proxy` reaches **265**
definitions the headline does not, and `HonestyGate.str_encodeIn_eq_certState`
reaches **1045** — the whole compiler and the whole six-seam reduction chain
respectively. That is not a defect to be fixed: it is FINDING AW seen from the
other side. Both theorems are *about the witness we built*, and the witness is
existentially quantified out of the headline, so their statements can never live
inside the headline's surface. **The honest conclusion is that they are not
reading instruments at all.** They are regression gates: their value is that
`lake build` fails if the construction they describe changes, not that anyone
reads their statements' closures. §3 says so and gates the claims that *are*
readable.

## ★★ And the finding that reorganises the reviewer's work (§1)

Metering the two conjuncts of the published headline **separately** shows they
are stated over disjoint vocabularies:

| conjunct | mentions | does **not** mention |
|---|---|---|
| hardness — the reduction | `FlatTM`, `runFlatTM`, `stepFlatTM` | `Op.cost`, `Cmd.cost`, `Cmd` |
| membership — the verifier | `Op.cost`, `Cmd.cost`, `Cmd` | `FlatTM`, `runFlatTM`, `stepFlatTM` |

So the two irreducible trust items a reviewer is left with — *is `FlatTM` a
Turing machine?* and *is `Op.cost` a faithful proxy for time?* — do **not**
compound. Each is load-bearing for exactly one conjunct. And §1 goes one step
further: it restates the membership conjunct at the machine level too
(`satStr_membership_is_machine_time`), so that after reading it a reviewer needs
`Op.cost` for **neither** half.
-/

namespace Complexity.GateSurfaceGate

open Complexity.Lang Complexity.Meta

/-! ## §1 · The two conjuncts rest on disjoint vocabularies

`NPcompleteStr' SATStr = NPhardStr SATStr ∧ inNPStr SATStr`. Both conjuncts are
stated over *classes* (`inNPStr` appears in the hardness conjunct's hypothesis),
so metering them as they stand mixes the vocabulary of the hypothesis with that
of the conclusion. To measure what each conjunct actually *claims*, instantiate
each at a concrete language — then there is no hypothesis left, and the surface
is exactly the claim.

`SquareStr` (`NonVacuity.lean` §3) is the concrete NP string language; the
hardness conjunct applied to it is a reduction with no class in sight. -/

/-- **The hardness conjunct, at a concrete language.** `SquareStr` is in the
hypothesis class (`NonVacuity.inNPStr_squareStr`), so the published headline
hands us a reduction to `SATStr`. This is the whole chain — C8 front, S1, the
four-step sound tail and the sixth seam — instantiated. -/
theorem squareStr_reducesPolyMO'_SATStr : NonVacuity.SquareStr ⪯p' SATStr.SATStr :=
  SATStrComp.satStr_NPhardStr NonVacuity.SquareStr NonVacuity.inNPStr_squareStr

/-- **The membership conjunct, at the machine level.** `inNPStr SATStr` says the
verifier is a `Cmd` inside a `Cmd.cost` bound — the layer's cost model, with no
Turing machine anywhere in the statement. This is the same fact with the layer
discharged: a certificate relation that is sound, complete and polynomially
bounded for `SATStr`, decided by a **real `FlatTM`** within a real polynomial
bound on `runFlatTM` steps.

It is one line, because `DecidesLang.toInTimePoly` is exactly the bridge
`CostFaithfulness.lean` describes. The point is not that it was hard; it is that
until it is *stated*, "SAT is in NP" in this development is a statement about
`Op.cost`, and a reviewer cannot see that from the headline. -/
theorem satStr_membership_is_machine_time :
    ∃ rel : List Bool → List Bool → Prop,
      polyCertRel SATStr.SATStr rel ∧
      inTimePoly (fun p : List Bool × List Bool => rel p.1 p.2) :=
  let W := SATStr.satStrWitness.toInNPWitnessLangFreeSplit
  ⟨W.rel, W.rel_correct, W.verifier.toInTimePoly W.dBound_poly W.dBound_mono⟩

/-! ### The measurement

Six presences and six absences. Written as exact surfaces this would be two
lists totalling 131 names in which no reader would find the interesting part;
`_contains`/`_omits` say it directly. ⚠ These are **shape** assertions and are
deliberately weaker than `#assert_statement_surface` — they cannot catch growth.
The headlines themselves stay metered exactly, in `StatementGate.lean`. -/

/-! The reduction really is stated about a Turing machine. -/
#assert_statement_surface_contains
  Complexity.GateSurfaceGate.squareStr_reducesPolyMO'_SATStr =>
  FlatTM
  runFlatTM
  stepFlatTM
  validFlatTM

/-! ★ …and **not** about the cost model. So a reviewer who distrusts `Op.cost`
entirely still has the whole hardness half of Cook–Levin, unweakened: its
polynomial bound counts `stepFlatTM` steps. -/
#assert_statement_surface_omits
  Complexity.GateSurfaceGate.squareStr_reducesPolyMO'_SATStr =>
  Complexity.Lang.Op.cost
  Complexity.Lang.Cmd.cost
  Complexity.Lang.Cmd
  Complexity.Lang.Op

/-! The verifier conjunct, as the headline states it, rests on the cost model. -/
#assert_statement_surface_contains SATStr.inNPStr_SATStr =>
  Complexity.Lang.Op.cost
  Complexity.Lang.Cmd.cost
  Complexity.Lang.Cmd

/-! ★ …and mentions **no Turing machine at all.** This is the single most
surprising thing the metering found: read as it stands, "SAT is in NP" in this
development is a claim about `Cmd.cost`, and `Complexity/CostFaithfulness.lean`
is what makes it a claim about time. -/
#assert_statement_surface_omits SATStr.inNPStr_SATStr =>
  FlatTM
  runFlatTM
  stepFlatTM

/-! ★ …and the machine-level restatement puts it right: a real `FlatTM`, a real
`runFlatTM` bound, and the cost model gone. -/
#assert_statement_surface_contains
  Complexity.GateSurfaceGate.satStr_membership_is_machine_time =>
  FlatTM
  runFlatTM
  stepFlatTM
  validFlatTM
  polyCertRel

#assert_statement_surface_omits
  Complexity.GateSurfaceGate.satStr_membership_is_machine_time =>
  Complexity.Lang.Op.cost
  Complexity.Lang.Cmd.cost
  Complexity.Lang.Cmd
  Complexity.Lang.Op

/-! ## §2 · The reading gates — what they cost beyond the headline

Each is metered against the headline it is an instrument *for*. `hardness_
spelled_out` and `membership_spelled_out` restate `CookLevinStr`; the `strict_`
pair restate `SATStr_NPcompleteStr'`. Getting the baseline right matters: the
one name by which `hardness_spelled_out` exceeds the *string* headline is
`instEncodableNat`, which is exactly the 103-vs-112 difference (S8 verdict 12,
unary numbers) and says nothing about the restatement. -/

/-! ★ **The control, and it passes.** The ordinary-language restatement of the
headline reaches **nothing** the headline does not. A restatement that drifted —
that quietly said something about an extra definition of ours — would show up
here as a non-empty list. -/
#assert_statement_surface_delta Complexity.StatementMeaning.hardness_spelled_out
  beyond CookLevinHonest.CookLevinStr =>
  -- (empty)

#assert_statement_surface_delta Complexity.StatementMeaning.membership_spelled_out
  beyond CookLevinHonest.CookLevinStr =>
  -- (empty)

/-! The same control for the statement we actually publish. -/
#assert_statement_surface_delta Complexity.StatementMeaning.strict_hardness_spelled_out
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  -- (empty)

#assert_statement_surface_delta Complexity.StatementMeaning.strict_membership_spelled_out
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  -- (empty)

/-! ### The non-vacuity deciders

`NonVacuity.searchDecide_correct` is the reason the hypothesis class contains
nothing undecidable, and it costs **ten** definitions beyond the headline —
seven of them field projections a reader of the headline has already met as
part of the structures, and three (`searchDecide`, `bitStringsUpTo`,
`verifierAccepts`) the actual content: a brute-force enumerator and the two
functions it is built from. That is a readable gate. -/

#assert_statement_surface_delta Complexity.NonVacuity.searchDecide_correct
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  Complexity.Lang.DecidesLang.c
  Complexity.Lang.InNPWitnessLangFreeSplit.dBound
  Complexity.Lang.InNPWitnessLangFreeSplit.rel
  Complexity.Lang.InNPWitnessLangFreeSplit.verifier
  Complexity.Lang.InNPWitnessStr.toInNPWitnessLangFreeSplit
  Complexity.NonVacuity.bitStringsUpTo
  Complexity.NonVacuity.searchDecide
  Complexity.NonVacuity.strLayout
  Complexity.NonVacuity.verifierAccepts
  PolyCertRelWitness.bound

#assert_statement_surface_delta Complexity.NonVacuity.searchDecide_calls
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  Complexity.NonVacuity.bitStringsUpTo

/-! ### The cheap half of the honesty gate

`HonestyGate.lean` is a construction gate (§3) — but not uniformly. Its pins
about the **chain ends** are small enough to read, and they are the ones that
carry the S5 verdict a reviewer cares about: that the head layout and the tail
serialization are the same function, and that the tail decoder is a genuine left
inverse. Metering them separates the readable pins from the unreadable ones
inside one file, which prose could not do. -/

#assert_statement_surface_delta Complexity.HonestyGate.certState_size
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  -- (empty — `certState`'s cell count is stated purely in the headline's own
  -- vocabulary, which is what makes it the cheapest honesty pin in the file)

#assert_statement_surface_delta Complexity.HonestyGate.strTail_parser_left_inverse
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  Complexity.Lang.decBits

#assert_statement_surface_delta Complexity.HonestyGate.strTail_enc_eq_head
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  Complexity.Lang.Serialize
  Complexity.Lang.Serialize.enc
  Complexity.Lang.decBits
  Complexity.Lang.decBits_strBits
  Complexity.Lang.instSerializeListBool
  Complexity.Lang.strBits_bit
  inOPoly_id

/-! ### The machine gates (2026-08-09)

`Complexity/MachineFaithfulness.lean` is the instrument for the **last**
irreducible model question on a reviewer's list — *is `FlatTM` a Turing
machine?* — so it is the one gate whose surface most needs to be near zero: an
answer stated in vocabulary the reader has not already met would not be an
answer.

It is. The whole machine group of `StatementGate.lean` (`stepFlatTM`,
`tapeStep`, `writeCurrentTapeSymbol`, `moveTapeHead`, `currentTapeSymbol`,
`entryMatchesConfig`, `runFlatTM`, `validFlatTM`, …) is *already* in the
headline's surface, because the headline's hardness conjunct is stated in
`runFlatTM` steps. So these theorems say things about definitions a reviewer has
already been told to read.

★ **Measured: the whole file costs exactly two definitions.** Nine of the ten
gates below add either nothing or the single new name `tapeCell` — the cell-wise
view of the tape, four tokens long — and the tenth adds `tapeSymbolsBounded`,
which is the alphabet predicate `validFlatTM` is already stated with. There is
no cheaper way to answer a model question than in the model's own vocabulary,
and that is the strongest evidence that this is a **reading** gate and not a
regression gate (FINDING BA). -/

/-! The head reads one cell, and `tapeCell` is that cell. One new name, and it
is the only one the whole file introduces. -/
#assert_statement_surface_delta Complexity.MachineFaithfulness.currentTapeSymbol_eq_tapeCell
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  Complexity.MachineFaithfulness.tapeCell

/-! ★ Locality: one step changes at most the cell under the head. -/
#assert_statement_surface_delta Complexity.MachineFaithfulness.tapeCell_tapeStep_of_ne
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  Complexity.MachineFaithfulness.tapeCell

/-! The head moves at most one cell, and the tape grows by at most one cell —
both stated purely in the headline's own vocabulary. -/
#assert_statement_surface_delta Complexity.MachineFaithfulness.tapeStep_head_le
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  -- (empty)

#assert_statement_surface_delta Complexity.MachineFaithfulness.tapeStep_length_le_succ
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  -- (empty)

/-! The finite control consults only the state and the symbols under the heads. -/
#assert_statement_surface_delta Complexity.MachineFaithfulness.find?_congr_of_read
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  -- (empty)

/-! The alphabet is closed under a step. The one new name is the alphabet
predicate itself. -/
#assert_statement_surface_delta Complexity.MachineFaithfulness.tapeStep_bounded
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  tapeSymbolsBounded

/-! ★ …and it is enforced: an out-of-alphabet symbol stalls a valid machine. -/
#assert_statement_surface_delta Complexity.MachineFaithfulness.stuck_of_symbol_ge_sig
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  -- (empty)

/-! The control state set is finite and closed. -/
#assert_statement_surface_delta Complexity.MachineFaithfulness.stepFlatTM_state_lt
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  -- (empty)

/-! ★ Space ≤ time, and the head cannot jump. -/
#assert_statement_surface_delta Complexity.MachineFaithfulness.runFlatTM_init_local
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  -- (empty)

/-! The written region is always a prefix — the invariant the append-only write
rule maintains. -/
#assert_statement_surface_delta Complexity.MachineFaithfulness.written_prefix
  beyond SATStrComp.SATStr_NPcompleteStr' =>
  Complexity.MachineFaithfulness.tapeCell

/-! ## §3 · The construction gates — measured, and reclassified

`Compile.cost_is_time_proxy` costs **265** definitions beyond the headline;
`HonestyGate.str_encodeIn_eq_certState` costs **1045**. Pasting either list here
would be worse than useless: it would present the entire compiler, and the
entire six-seam reduction chain, as a *reading list*, which is exactly the thing
this development spent three sessions shrinking.

The reason is structural and was already known under another name. FINDING AW:
`reducesPolyMO'` quantifies over the reduction existentially, so no witness of
ours appears in any headline's surface. These two theorems are statements
*about our witness*. Their surfaces therefore cannot be subsets of the
headline's, no matter how they are phrased — the overlap (65 and 76 names) is
only the vocabulary the two share.

**So they are not reading instruments, and this file's verdict is that they
should stop being advertised as ones.** What they are is regression gates: if
the compiler or the chain is refactored so that the audited facts stop holding,
`lake build` fails. That is real and it is worth having. It is simply a
different kind of evidence from "read this and you will believe it", and
conflating the two costs a reviewer time they will not get back.

Three things *are* readable and are gated instead. -/

/-! ### (a) `cost_is_time_proxy` really covers both compiled machines

The claim the file makes for itself is that it bounds **both** machines the
proof path compiles — a claim about only the reduction machine would be an
overclaim. That is checkable without reading the compiler. -/

#assert_statement_surface_contains Complexity.Lang.Compile.cost_is_time_proxy =>
  Complexity.Lang.Op.cost
  Complexity.Lang.Cmd.cost
  Complexity.Lang.Compile.paddedComputeTM
  Complexity.Lang.Compile.paddedBitDeciderTM
  runFlatTM
  haltingStateReached

/-! ### (b) ★ the machine it bounds is the machine the membership bridge builds

**This is a gap the metering found, and it is the one that mattered.**
`cost_is_time_proxy` is a theorem about `Compile.paddedBitDeciderTM c k`.
Nothing in the build said that this is the machine a reader of §1's
`satStr_membership_is_machine_time` actually gets. If `DecidesLang.toDecidesBy`
were ever retargeted at a different machine, `CostFaithfulness.lean` would stay
green and would be about a machine no longer on the proof path.

It is a `rfl`, because `toDecidesBy` is a `def`. -/

theorem deciderBridge_machine {X : Type} [encodable X] {P : X → Prop}
    {costBound : Nat → Nat} (D : DecidesLang P costBound)
    (hpoly : inOPoly costBound) (hmono : monotonic costBound) :
    (D.toDecidesBy hpoly hmono).M = Compile.paddedBitDeciderTM D.c D.regBound := rfl

/-- …and its two halting states are the ones `cost_is_time_proxy` names. Without
this the time bound could be about a machine that halts somewhere else. -/
theorem deciderBridge_states {X : Type} [encodable X] {P : X → Prop}
    {costBound : Nat → Nat} (D : DecidesLang P costBound)
    (hpoly : inOPoly costBound) (hmono : monotonic costBound) :
    (D.toDecidesBy hpoly hmono).acceptState
        = 1 + (Compile D.regBound D.c).states
          + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states
      ∧ (D.toDecidesBy hpoly hmono).rejectState
        = 2 + (Compile D.regBound D.c).states
          + (Compile.padRegsTM (D.regBound + 2 * D.c.loopDepth + 2)).states :=
  ⟨rfl, rfl⟩

/-! ⚠ **The reduction side has no counterpart, deliberately, and it does not
need one.** `PolyTimeComputableLang.toFrameworkWitness'` is a *theorem* returning
`Nonempty (PolyTimeComputableWitness' f)`, so its machine is discarded and no
`rfl` can reach it. That is not a hole: by §1 the hardness conjunct does not
mention the cost model at all — its polynomial bound already counts `stepFlatTM`
steps, inside `ComputesBy`. `cost_is_time_proxy`'s first half is what makes
`toFrameworkWitness'` *provable*; the kernel checks that proof, and a reviewer
does not have to. -/

/-! ### (c) the honesty gate's expensive pins say what they are advertised to say

`str_encodeIn_eq_certState` is the whole head-side audit. Its surface is 1121
names because it mentions the composite witness by name; its *content* is that
the composite's `encodeIn` is `certState`. Pin the content. -/

#assert_statement_surface_contains
  Complexity.HonestyGate.str_encodeIn_eq_certState =>
  Complexity.Lang.certState
  Complexity.Lang.InNPWitnessStr
  Complexity.Lang.PolyTimeComputableLang.encodeIn
  FrontS1Comp.front_to_SAT_witness

/-! ## The gate -/

#assert_axioms_clean
  Complexity.GateSurfaceGate.squareStr_reducesPolyMO'_SATStr
  Complexity.GateSurfaceGate.satStr_membership_is_machine_time
  Complexity.GateSurfaceGate.deciderBridge_machine
  Complexity.GateSurfaceGate.deciderBridge_states

end Complexity.GateSurfaceGate
