import Complexity.NP.SAT.CookLevin.CookLevinHonest
import Complexity.Lang.HardnessStr

/-! # The honesty audit, machine-checked (top-down session 2026-07-30-c)

Standing risk #1: *honesty is per-witness discipline, the structures do not
enforce it.* `NPcomplete'' SAT` is machine-checked, so the only remaining way
`CookLevin''` could fail to mean what it says is that some witness's
`encodeIn`/`decodeOut` does the reduction's work instead of its program.

This probe is the audit's **evidence file**. It pins, as `rfl`/`decide`, the
facts the written verdicts in `CookLevin/ROADMAP.md` ("Risk S5") rest on, so a
future refactor that quietly breaks one goes red here rather than silently
weakening the theorem.

The audit's structural result (§1) is what makes the audit finite:

> For a witness built by `PolyTimeComputableLang.comp`, `encodeIn` is the
> **leftmost** witness's and `decodeOut` is the **rightmost** witness's.
> `toFrameworkWitness'` then hands exactly those two to `ComputesBy` as
> `encode`/`decode`. So the honesty surface of `Q ⪯p' SAT` is **two functions**,
> not twelve: every intermediate `encodeIn` appears only on the *right* of a
> `SeamData.bridge` obligation — i.e. the composed program is *required to
> produce it* — so a dishonest intermediate layout could only make the bridge
> harder to prove, never license a cheat.

§6 is the negative control: a witness that satisfies **every** field of
`PolyTimeComputableLang` while doing all of its work in `encodeIn`. It is the
machine-checked form of standing risk #1 — the reason the audit is a *reading*
obligation that no typechecker can discharge.

⚠ **Since 2026-08-02 the positive pins of §§1–3 and §8 also live in
`CookLevin/Complexity/HonestyGate.lean`, which IS part of `lake build`.** They
are kept here too, as narration with their reasoning attached; if the two ever
disagree the build is the one that is checked. The **negative controls (§6, §7b,
and §7's corpse) must stay here and only here** — they are constructions that are
*supposed* to typecheck, and a reader who found them inside the library would
rightly read them as claims of it.

**The state of the two ends of the chain (read this):**

* **§3** — the tail decoder is a real **parser** (`Serialize cnf` /
  `CnfSerialize.decCnf`, `dec_enc` proven) instead of `Function.invFun`
  (2026-08-01). One of the two audited functions is pinned by a typeclass law,
  not a reading.
* **§2/§8** — the head encoder is the hypothesis's own layout, verbatim
  (2026-08-02): `encodeIn = W.encX`, and under `NPhardStr` that is `certState`,
  the raw input string. The size register the reduction used to be handed is
  computed on-machine. The other audited function is now a `rfl`.
* **§6** — the standing negative control on the **conclusion** side: a witness
  satisfying every field of `PolyTimeComputableLang` while doing all its work in
  `encodeIn`. Still typechecks; still the reason honesty is a reading obligation
  at any chain end we do not pin.
* **§7** — ★ the negative control on the **hypothesis** side that **died**
  (2026-08-02). It was a complete `InNPWitnessLangFreeSplit Q` for an *arbitrary*
  predicate with the answer planted in `encX`; the new `sizeLB` field makes it
  unbuildable, and §7 now *proves* that (`badEncX_no_sizeLB`,
  `no_badEncX_witness`) while keeping the rest of the construction to show the
  obstruction is that field and nothing else.
* **§7b** — the cheat that **survives**, and why no further *field* can help: a
  layout that writes the whole raw input out (size-faithful, injective,
  `Serialize`-able, `sizeLB`-able — all discharged here) and merely *appends*
  the answer in a second register.
* **§8** — the actual fix: `NPhardStr` (`Lang/HardnessStr.lean`) quantifies over
  **string languages** with the canonical layout, where `encX` is not a field at
  all. `NPcompleteStr SAT` follows from `CookLevin''` in one line. **Quote
  `CookLevinStr`.**

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/HonestyAuditProbe.lean`
-/

open Complexity.Lang

namespace HonestyAuditProbe

/-! ## §1 — the composite's honesty surface is exactly two functions

The endpoint witness of the hardness half is
`FrontS1Comp.front_to_SAT_witness`, five `comp`s deep. These two `rfl`s say
that all five seams and all six intermediate layouts have dropped out of the
two fields honesty depends on. -/

section Composite
variable {X : Type} [encodable X] {Q : X → Prop}

/-- The composite's input layout is the **front** witness's, verbatim. -/
example (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).encodeIn
      = FrontWitness.encodeInQ W := rfl

/-- The composite's output decoder is the **last** witness's, verbatim
(`FSAT ⪯p' SAT`, the end of the sound tail). -/
example (W : InNPWitnessLangFreeSplit Q) (cm km dm cs ks ds : Nat) :
    (FrontS1Comp.front_to_SAT_witness W cm km dm cs ks ds).decodeOut
      = FSATSATFree.decodeOut := rfl

/-- Same for the S1-rooted composite (the `FlatSingleTMGenNP → SAT` half), so
the claim is checked at both nesting levels. -/
example : S1SATComp.s1_to_SAT_witness.encodeIn = HeadLayout.headEncodeIn := rfl

example : S1SATComp.s1_to_SAT_witness.decodeOut = FSATSATFree.decodeOut := rfl

end Composite

/-! ## §2 — the head layout is the hypothesis's own layout, FULL STOP

⚠ **Changed 2026-08-02 (top-down).** `encodeIn x` used to be
`W.encX x ++ [1^(encodable.size x)]` — honest (the extra register was a *metric*
of the input, not an answer), but still one thing an auditor had to read and
judge. It is now `W.encX x`: the reduction counts its own input's cells
on-machine (`FrontPieces.tallyCells`, licensed by the new `sizeLB` field) and
the handed-over register is gone.

The verdict this pins: the composite reduction's `ComputesBy.encode` is
**equal to the hypothesis witness's own input layout**, the very layout `Q`'s
verifier already reads. There is no head-side encoding of *ours* left to audit
— see §8 for what that means under `NPhardStr`. -/

section Head
variable {X : Type} [encodable X] {Q : X → Prop}

example (W : InNPWitnessLangFreeSplit Q) (x : X) :
    FrontWitness.encodeInQ W x = W.encX x := rfl

/-- The front instance the reduction actually emits: the machine is built from
`Q`'s **verifier program** (`W.verifier.c`), the string is a mechanical
re-encoding of `W.encX x`, and the two budgets are numbers. This is the
textbook Cook–Levin front, and it is what makes the hardness half non-vacuous:
the emitted machine genuinely simulates `Q`'s verifier. -/
example (W : InNPWitnessLangFreeSplit Q) (maxSize steps : X → Nat) (x : X) :
    FrontLifting.fQ W maxSize steps x
      = (FrontMachine.MQ W.verifier.c W.verifier.regBound W.xWidth,
         3 :: Compile.encodeRegs (W.encX x), maxSize x, steps x) := rfl

end Head

/-! ## §3 — the tail decoder is a PARSER of the output layout

⚠ **Changed 2026-08-01 (top-down).** `decodeOut` used to be
`Function.invFun encodeCnf (get s CNFOUT)` — classical, noncomputable, and
unconstrained off the image, so the audit had to argue the junk branch was
unreachable. It is now `Serialize.dec` of one designated register: the canonical
CNF parser `CnfSerialize.decCnf`, with `dec_enc` proven (no `Classical`), and a
*constant* fallback off the image. It still does not look at the input and does
not branch. -/

example (s : State) :
    FSATSATFree.decodeOut s
      = Serialize.decodeD ([] : cnf) (State.get s FSATSATFree.CNFOUT) := rfl

example : FSATSATFree.CNFOUT = 2 := rfl

/-- The parser is a genuine left inverse — the fact the whole tail verdict now
rests on. -/
example (N : cnf) : CnfSerialize.decCnf (EvalCnfCmd.encodeCnf N) = some N :=
  CnfSerialize.decCnf_encodeCnf N

/-- …and it really parses (round trip on a two-clause example, by `decide`). -/
example : CnfSerialize.decCnf (EvalCnfCmd.encodeCnf [[(true, 0)], [(false, 2)]])
    = some [[(true, 0)], [(false, 2)]] := by decide

/-- Junk does not decode to a CNF — there is no "junk branch" left to audit. -/
example : CnfSerialize.decCnf [1, 1, 0] = none := by decide

/-- `encodeCnf` is a mechanical, self-delimiting, bit-level serialization —
spelled out on a two-clause example so the "no work in the encoding" verdict is
data, not a reading of the definition. -/
example : EvalCnfCmd.encodeCnf [[(true, 0)], [(false, 2)]]
    = [1, 1, 0,        -- clause 0: literal `(+, x0)` = [1, pol=1, 0 ones, 0]
       0,              --           clause-end
       1, 0, 1, 1, 0,  -- clause 1: literal `(-, x2)` = [1, pol=0, 1 1, 0]
       0] := by decide

/-! ## §4 — the membership half's layout

`satEncX N` is *registers `0`–`2` of the live verifier's own `encodeState`* and
nothing else, and `satEIn` appends the raw certificate register. The bits are
turned into an assignment by `certDecode`, a `Cmd` — not by the encoder. -/

example (N : cnf) (a : assgn) :
    EvalCnfSplit.satEncX N
      = (EvalCnfCmd.encodeState (N, a)).take 3 := rfl

example (N : cnf) (c : List Bool) :
    EvalCnfSplit.satEIn (N, c) = EvalCnfSplit.satEncX N ++ certState c := rfl

/-- The certificate register holds the **raw** bits (characteristic vector), so
every bit string is in the image: no partial parse, no un-decodable garbage. -/
example (c : List Bool) : certState c = [c.map (fun b => if b then 1 else 0)] := rfl

/-- The verifier the split witness publishes really is the precomposed
`certDecode ;; evalCnfCmd` reading `satEIn` — the decode is machine work. -/
example : Cmd.UsesBelow EvalCnfSplit.certDecode 19 := EvalCnfSplit.certDecode_usesBelow

/-! ## §5 — where the two audited functions end up

`toFrameworkWitness'` builds `ComputesBy.encode := encodeTape ∘ W.encodeIn` and
`ComputesBy.decode := W.decodeOut ∘ decodeTape`. Those two fields are the whole
freedom `⪯p'` leaves; everything between them is `Compile.paddedComputeTM W.c`,
a real machine running a real program. (Not `rfl`-checkable here — the fields
are introduced inside `toFrameworkWitness'`'s proof term — so this section is a
pointer, and §1 is what makes it enough.)

## §6 — NEGATIVE CONTROL: a fully dishonest witness that typechecks

`PolyTimeComputableLang` does **not** enforce honesty. Below is a complete,
`sorry`-free witness for `fun n => n * n` whose program is the layer's no-op:
all of the "computation" happens in `encodeIn`, which lays the *answer* on the
tape. Every field is discharged.

This is standing risk #1 as a machine-checked fact. It is why the audit is a
reading obligation and why its verdicts live in the ROADMAP risk register. -/

namespace Dishonest

/-- The "program": `copy 0 0`, the layer's no-op (`S1CardEmit.copy_self_get`). -/
def nop : Cmd := Cmd.op (.copy 0 0)

/-- The dishonest layout: the answer, in unary, in register `0`. -/
def badEncodeIn (n : Nat) : State := [List.replicate (n * n) 1]

theorem nop_eval (s : State) : nop.eval s = s.set 0 (State.get s 0) := rfl

theorem nop_get0 (n : Nat) :
    State.get (nop.eval (badEncodeIn n)) 0 = List.replicate (n * n) 1 := rfl

/-- **The dishonest witness.** Note what it is *not* missing: the cost bound is
a genuine polynomial, the size bounds hold, the state is bit-level, the frame is
respected. It is a perfectly good inhabitant of the type — and it computes
nothing. -/
noncomputable def badWitness : PolyTimeComputableLang (fun n : Nat => n * n) where
  c := nop
  encodeIn := badEncodeIn
  decodeOut := fun s => (State.get s 0).length
  cost_bound := fun m => m * m + 1
  cost_bound_poly :=
    inOPoly_add (inOPoly_mul inOPoly_id inOPoly_id) (inOPoly_const 1)
  cost_bound_mono := fun a b h => Nat.add_le_add_right (Nat.mul_le_mul h h) 1
  encBound := fun m => m * m
  encBound_poly := inOPoly_mul inOPoly_id inOPoly_id
  encBound_mono := fun a b h => Nat.mul_le_mul h h
  encodeIn_size := fun n => by
    show ((badEncodeIn n).map List.length).foldr (· + ·) 0 ≤ n * n
    simp [badEncodeIn]
  computes := fun n => by
    show (State.get (nop.eval (badEncodeIn n)) 0).length = n * n
    rw [nop_get0]; exact List.length_replicate ..
  cost_le := fun n => by
    show nop.cost (badEncodeIn n) ≤ n * n + 1
    show (State.get (badEncodeIn n) 0).length + 1 ≤ n * n + 1
    show (List.replicate (n * n) 1).length + 1 ≤ n * n + 1
    rw [List.length_replicate]
  output_size_le := fun n => Nat.le_succ _
  enc_bit := fun n => by
    intro reg hreg y hy
    simp only [badEncodeIn, List.mem_singleton] at hreg
    subst hreg
    exact le_of_eq (List.eq_of_mem_replicate hy)
  regBound := 1
  usesBelow := ⟨Nat.one_pos, Nat.one_pos⟩
  width_le := fun _ => Nat.le_refl 1
  decode_agree := fun n m => by
    have hag : AgreeBelow 1 (badEncodeIn n ++ List.replicate m []) (badEncodeIn n) :=
      fun r _ => State.get_append_replicate_nil (badEncodeIn n) m r
    have := Cmd.eval_agree nop 1 (⟨Nat.one_pos, Nat.one_pos⟩) hag 0 Nat.one_pos
    show (State.get (nop.eval (badEncodeIn n ++ List.replicate m [])) 0).length = _
    rw [this]

/-- …and it yields a genuine `polyTimeComputable'`, i.e. a real `FlatTM` with a
real polynomial time bound. The machine is real; the *statement* is hollow,
because `ComputesBy.encode` was allowed to do the work. -/
theorem bad_polyTimeComputable' : polyTimeComputable' (fun n : Nat => n * n) :=
  badWitness.toFrameworkWitness'

end Dishonest

/-! ## §7 — ★ THE CHEAT THAT DIED (2026-08-02) — read this section first

This section used to be the sharpest finding in the file: a complete,
`sorry`-free `InNPWitnessLangFreeSplit Q` for an **arbitrary** predicate `Q` on
an **arbitrary** encodable type — `encX x = [[if Q x then 1 else 0]]`, verifier
= the layer's no-op `copy 0 0` reading the planted answer — which made
`CookLevinHonest.SAT_NPhard''` yield `Q ⪯p' SAT` for undecidable `Q`.

**It no longer typechecks.** `InNPWitnessLangFreeSplit` gained a `sizeLB` field
on 2026-08-02 (`Lang/PolyTime.lean`): `encodable.size x ≤ sizeLB (State.size
(encX x))` for some polynomial `sizeLB` — the input's size must be recoverable
from its own layout. What is kept below is *precisely* how it died, machine-
checked, and it is worth more than the cheat was:

* **`badVerifier` still exists** and every other field is still dischargeable —
  `badSplitWitnessOf` builds the whole witness from a `sizeLB` and its proof,
  so the obstruction is *exactly* that field and nothing else;
* **`badEncX_no_sizeLB`** proves no such `sizeLB` exists over `Y = Nat`: the
  layout is one cell wide for every input, so a bound would make `encodable.size`
  bounded on an unbounded type.

Together: the answer-planting layout survives only on types of bounded size,
i.e. it can no longer present an infinite problem. That is the whole content of
the `sizeLB` field, and it is the reason the front reduction may now count its
own input's cells instead of being handed the count (§2).

⚠ This did **not** close the hypothesis-side hole — §7b is the cheat that
survives every law *about* `encX`, and §8 is the actual fix. Do not read §7's
death as "`NPhard''` is now safe to quote"; quote `NPhardStr`. -/

namespace HypothesisCheat

attribute [local instance] Classical.propDecidable

variable {Y : Type} [encodable Y] (Q : Y → Prop)

/-- The answer-laying input layout: ONE register holding the answer bit. -/
noncomputable def badEncX (x : Y) : State := [[if Q x then 1 else 0]]

noncomputable def badEncodeIn (xc : Y × List Bool) : State :=
  badEncX Q xc.1 ++ certState xc.2

/-- The "verifier": the layer's no-op. Register 0 already holds the answer. -/
def badCmd : Cmd := Cmd.op (.copy 0 0)

theorem badCmd_get0 (s : State) : State.get (badCmd.eval s) 0 = State.get s 0 := by
  show State.get (State.set s 0 (State.get s 0)) 0 = State.get s 0
  rw [State.get_set_eq]

omit [encodable Y] in
theorem badEncodeIn_get0 (xc : Y × List Bool) :
    State.get (badEncodeIn Q xc) 0 = [if Q xc.1 then 1 else 0] := rfl

/-- A complete `DecidesLang` for `fun xc => Q xc.1` — over the dishonest
layout. The program does nothing; the layout already holds the answer. -/
noncomputable def badVerifier :
    DecidesLang (fun xc : Y × List Bool => Q xc.1) (fun n => n + 2) where
  c := badCmd
  encodeIn := badEncodeIn Q
  encodeIn_size := by
    intro xc
    show (1 : Nat) + ((xc.2.map (fun b => if b then 1 else 0)).length + 0)
      ≤ encodable.size xc + 2
    have h1 : xc.2.length ≤ encodable.size xc.2 := length_le_size xc.2
    have h2 : encodable.size xc = encodable.size xc.1 + encodable.size xc.2 + 1 := rfl
    rw [List.length_map]
    omega
  decides := by
    intro xc
    have hg : State.get (badCmd.eval (badEncodeIn Q xc)) 0
        = [if Q xc.1 then 1 else 0] := by
      rw [badCmd_get0, badEncodeIn_get0]
    constructor
    · show Q xc.1 ↔ (State.get (badCmd.eval (badEncodeIn Q xc)) 0 == [1]) = true
      rw [hg]
      by_cases h : Q xc.1 <;> simp [h]
    · show ¬ Q xc.1 ↔ (State.get (badCmd.eval (badEncodeIn Q xc)) 0 == [0]) = true
      rw [hg]
      by_cases h : Q xc.1 <;> simp [h]
  cost_bound := by
    intro xc
    show Op.cost (.copy 0 0) (badEncodeIn Q xc) ≤ encodable.size xc + 2
    show (State.get (badEncodeIn Q xc) 0).length + 1 ≤ encodable.size xc + 2
    rw [badEncodeIn_get0]
    show 1 + 1 ≤ encodable.size xc + 2
    omega
  enc_bit := by
    intro xc reg hreg y hy
    rcases List.mem_append.mp hreg with h | h
    · have hr : reg = [if Q xc.1 then 1 else 0] := by simpa [badEncX] using h
      subst hr
      have hy' : y = (if Q xc.1 then 1 else 0) := by simpa using hy
      subst hy'
      by_cases hq : Q xc.1 <;> simp [hq]
    · have hr : reg = xc.2.map (fun b => if b then 1 else 0) := by
        simpa [certState] using h
      subst hr
      obtain ⟨b, _, hb⟩ := List.mem_map.mp hy
      subst hb
      cases b <;> simp
  regBound := 2
  usesBelow := ⟨Nat.zero_lt_two, Nat.zero_lt_two⟩
  width_le := by
    intro xc
    show (badEncX Q xc.1 ++ certState xc.2).length ≤ 2
    simp [badEncX, certState]

/-- **The cheat, modulo exactly one field.** Every field of
`InNPWitnessLangFreeSplit` is dischargeable for the answer-planting layout
*except* `sizeLB`, which is taken as a parameter here. So this def is the
machine-checked statement "the `sizeLB` field, and nothing else, is what stops
the §7 cheat". -/
noncomputable def badSplitWitnessOf (sizeLB : Nat → Nat) (hpoly : inOPoly sizeLB)
    (hLB : ∀ x : Y, encodable.size x ≤ sizeLB (State.size (badEncX Q x))) :
    InNPWitnessLangFreeSplit Q where
  rel := fun x _ => Q x
  dBound := fun n => n + 2
  dBound_poly := inOPoly_add inOPoly_id (inOPoly_const 2)
  dBound_mono := fun _ _ h => Nat.add_le_add_right h 2
  verifier := badVerifier Q
  rel_correct := ⟨{
    bound := fun _ => 0
    sound := fun {_ _} h => h
    complete := fun {_} h => ⟨[], h, Nat.le_refl 0⟩
    bound_poly := inOPoly_const 0
    bound_mono := fun _ _ _ => Nat.le_refl 0 }⟩
  encX := badEncX Q
  encodeIn_eq := fun _ _ => rfl
  xWidth := 1
  encX_width := fun _ => rfl
  encX_size := by
    intro x
    show (1 : Nat) + 0 ≤ encodable.size x + 2
    omega
  sizeLB := sizeLB
  sizeLB_poly := hpoly
  encX_sizeLB := hLB

/-- **…and no such `sizeLB` exists.** The answer-planting layout is ONE cell
wide for every input, so a `sizeLB` would bound `encodable.size` on all of `Y`.
Over `Y = Nat` (where `encodable.size = id`) that is false, and the §7 cheat is
dead. ⚠ Note what this does *not* say: on a type of bounded size the cheat is
still constructible — and harmlessly so, since a finite problem is decidable
anyway. The freedom `sizeLB` removes is exactly the freedom to present an
unbounded problem in a bounded layout. -/
theorem badEncX_no_sizeLB (P : Nat → Prop) (sizeLB : Nat → Nat) :
    ¬ (∀ n : Nat, encodable.size n ≤ sizeLB (State.size (badEncX P n))) := by
  intro h
  have hone : ∀ n : Nat, State.size (badEncX P n) = 1 := fun _ => rfl
  have hbig := h (sizeLB 1 + 1)
  rw [hone] at hbig
  have : encodable.size (sizeLB 1 + 1) = sizeLB 1 + 1 := rfl
  omega

/-- The cheat is not presentable at all over `Nat`: no `InNPWitnessLangFreeSplit`
whose input layout is `badEncX` exists. -/
theorem no_badEncX_witness (P : Nat → Prop)
    (W : InNPWitnessLangFreeSplit P) (hW : W.encX = badEncX P) : False :=
  badEncX_no_sizeLB P W.sizeLB (fun n => by rw [← hW]; exact W.encX_sizeLB n)

end HypothesisCheat

/-! ## §7b — why the fix must be a RESTRICTION, not another field

The obvious patch to §7 is to forbid *compressing* layouts: add a field
`∀ x, encodable.size x ≤ sizeLB (State.size (encX x))` (`sizeLB` polynomial),
which would indeed kill §7 — its `encX x` has size `1` for every `x`.

It would not kill this one. Here the input type is already `List Bool`, the
layout writes the **whole raw string** into register `0`, and the answer is
merely *appended* in register `1`. The layout is size-faithful, injective, and
`Serialize`-able (`dec` reads register 0 and ignores register 1) — every
plausible "no compression" or "canonically serialized" law holds — and the
verifier is still a two-op program that reads the planted answer.

**That is the argument for `NPhardStr`.** No law *about* `encX` can rule out
"the honest encoding, plus one extra register"; only removing the field can.
`InNPWitnessStr` removes it. -/

namespace HypothesisCheat2

attribute [local instance] Classical.propDecidable

variable (Q : List Bool → Prop)

/-- Honest first register, planted answer in the second. -/
noncomputable def badEncX (x : List Bool) : State :=
  [x.map (fun b => if b then 1 else 0), [if Q x then 1 else 0]]

noncomputable def badEncodeIn (xc : List Bool × List Bool) : State :=
  badEncX Q xc.1 ++ certState xc.2

/-- The "verifier": copy the planted answer into the output register. -/
def badCmd : Cmd := Cmd.op (.copy 0 1)

theorem badCmd_get0 (s : State) : State.get (badCmd.eval s) 0 = State.get s 1 := by
  show State.get (State.set s 0 (State.get s 1)) 0 = State.get s 1
  rw [State.get_set_eq]

theorem badEncodeIn_get1 (xc : List Bool × List Bool) :
    State.get (badEncodeIn Q xc) 1 = [if Q xc.1 then 1 else 0] := rfl

noncomputable def badVerifier :
    DecidesLang (fun xc : List Bool × List Bool => Q xc.1) (fun n => 2 * n + 2) where
  c := badCmd
  encodeIn := badEncodeIn Q
  encodeIn_size := by
    intro xc
    show (xc.1.map (fun b => if b then 1 else 0)).length
        + (1 + ((xc.2.map (fun b => if b then 1 else 0)).length + 0))
      ≤ 2 * encodable.size xc + 2
    have h1 : xc.1.length ≤ encodable.size xc.1 := length_le_size xc.1
    have h2 : xc.2.length ≤ encodable.size xc.2 := length_le_size xc.2
    have h3 : encodable.size xc = encodable.size xc.1 + encodable.size xc.2 + 1 := rfl
    rw [List.length_map, List.length_map]
    omega
  decides := by
    intro xc
    have hg : State.get (badCmd.eval (badEncodeIn Q xc)) 0
        = [if Q xc.1 then 1 else 0] := by
      rw [badCmd_get0, badEncodeIn_get1]
    constructor
    · show Q xc.1 ↔ (State.get (badCmd.eval (badEncodeIn Q xc)) 0 == [1]) = true
      rw [hg]; by_cases h : Q xc.1 <;> simp [h]
    · show ¬ Q xc.1 ↔ (State.get (badCmd.eval (badEncodeIn Q xc)) 0 == [0]) = true
      rw [hg]; by_cases h : Q xc.1 <;> simp [h]
  cost_bound := by
    intro xc
    show (State.get (badEncodeIn Q xc) 1).length + 1 ≤ 2 * encodable.size xc + 2
    rw [badEncodeIn_get1]
    show 1 + 1 ≤ 2 * encodable.size xc + 2
    omega
  enc_bit := by
    intro xc reg hreg y hy
    rcases List.mem_append.mp hreg with h | h
    · rcases (by simpa [badEncX] using h :
        reg = xc.1.map (fun b => if b then 1 else 0)
          ∨ reg = [if Q xc.1 then 1 else 0]) with hr | hr
      · subst hr
        obtain ⟨b, _, hb⟩ := List.mem_map.mp hy
        subst hb; cases b <;> simp
      · subst hr
        have hy' : y = (if Q xc.1 then 1 else 0) := by simpa using hy
        subst hy'; by_cases hq : Q xc.1 <;> simp [hq]
    · have hr : reg = xc.2.map (fun b => if b then 1 else 0) := by
        simpa [certState] using h
      subst hr
      obtain ⟨b, _, hb⟩ := List.mem_map.mp hy
      subst hb; cases b <;> simp
  regBound := 3
  usesBelow := ⟨Nat.zero_lt_succ 2, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩
  width_le := by
    intro xc
    show (badEncX Q xc.1 ++ certState xc.2).length ≤ 3
    simp [badEncX, certState]

/-- A size-faithful, injective, answer-appending presentation of an arbitrary
predicate on bit strings. -/
noncomputable def badSplitWitness : InNPWitnessLangFreeSplit Q where
  rel := fun x _ => Q x
  dBound := fun n => 2 * n + 2
  dBound_poly := inOPoly_add (inOPoly_mul (inOPoly_const 2) inOPoly_id) (inOPoly_const 2)
  dBound_mono := fun _ _ h => Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 2
  verifier := badVerifier Q
  rel_correct := ⟨{
    bound := fun _ => 0
    sound := fun {_ _} h => h
    complete := fun {_} h => ⟨[], h, Nat.le_refl 0⟩
    bound_poly := inOPoly_const 0
    bound_mono := fun _ _ _ => Nat.le_refl 0 }⟩
  encX := badEncX Q
  encodeIn_eq := fun _ _ => rfl
  xWidth := 2
  encX_width := fun _ => rfl
  encX_size := by
    intro x
    show (x.map (fun b => if b then 1 else 0)).length + (1 + 0)
      ≤ 2 * encodable.size x + 2
    have h1 : x.length ≤ encodable.size x := length_le_size x
    rw [List.length_map]
    omega
  -- ⚠ THE POINT OF §7b: the `sizeLB` field that killed §7 is satisfied here
  -- without effort, because this layout really does write the whole input out.
  sizeLB := fun n => 2 * n
  sizeLB_poly := inOPoly_mul (inOPoly_const 2) inOPoly_id
  encX_sizeLB := by
    intro x
    show encodable.size x ≤ 2 * ((x.map (fun b => if b then 1 else 0)).length + (1 + 0))
    have h := size_le_two_mul_length x
    rw [List.length_map]
    omega

/-- **The layout is size-faithful** — it writes the input out in full — and the
witness is still a cheat. No `encX` law can separate these two facts. -/
theorem badEncX_size_faithful (x : List Bool) :
    encodable.size x ≤ 2 * State.size (badEncX Q x) := by
  show encodable.size x ≤ 2 * ((x.map (fun b => if b then 1 else 0)).length + (1 + 0))
  have h := size_le_two_mul_length x
  rw [List.length_map]
  omega

theorem cheat_reduction : Q ⪯p' SAT :=
  CookLevinHonest.SAT_NPhard'' (List Bool) inferInstance Q ⟨badSplitWitness Q⟩

/-! ### §7c — the corollary nobody had drawn: `inNPLangFreeSplit` is VACUOUS

§7b was written as a statement about the *hypothesis* side of `NPhard''`. It is
also, verbatim, a statement about the **conclusion** side of `NPcompleteStr`,
and that had gone unrecorded until the S8 audit of 2026-08-07.

`NPcompleteStr P = NPhardStr P ∧ inNPLangFreeSplit P`. The line below shows the
second conjunct holds for an **arbitrary** `Q : List Bool → Prop` — undecidable
ones included, since `Q` here is a bare variable. A conjunct that is true of
every language is not a claim about `P`; the whole informational content of
`NPcompleteStr`'s membership half is that the *instance* we supply is honest,
which is risk S5's business and cannot be read off the statement (FINDING AW,
again).

**The fix is the same shape as `NPhardStr`'s: remove the free field, do not add
a law.** `Complexity.Lang.NPcompleteStr' P = NPhardStr P ∧ inNPStr P` pins the
membership layout to `certState` too, and `SATStrComp.SATStr_NPcompleteStr'`
proves it for `SATStr` — at zero cost, because `SATStr.satStrWitness` was
already an `InNPWitnessStr` and the old headline was throwing the
`encX_canonical` field away. ⚠ The `#assert_statement_surface` block for the
strict headline is in `Complexity/StatementGate.lean`; do not let the two drift.

⚠ This does **not** apply to `CookLevinHonest.CookLevinStr : NPcompleteStr SAT`
in the same one-line way — `SAT`'s instances live in `cnf`, not `List Bool`, so
the cheat has to be re-run over that type — but nothing about the argument is
special to `List Bool`, and no `inNPStr` exists for a non-string language to
strengthen it with. That is a third reason to quote the `SATStr` headline. -/

/-- ⚠ **The membership conjunct of `NPcompleteStr` is satisfiable for every
string language.** `Q` is a variable: this is not a statement about a cleverly
chosen language, it is a statement about the class. -/
theorem membership_conjunct_is_vacuous : inNPLangFreeSplit Q :=
  ⟨badSplitWitness Q⟩

end HypothesisCheat2

/-! ## §8 — THE FIX: under `NPhardStr` there is nothing left to choose

`Complexity.Lang.InNPWitnessStr` pins the hypothesis to a **string language**
with the canonical one-register layout `certState`. Then the composite
reduction's input encoding is not a free function of the witness — and since
2026-08-02 it is not even a formula with a tally bolted on. It is

    encodeIn x = certState x

the raw input string, one register, one cell per bit. **That is the entire
head-side audit**, and it is now a `rfl` rather than a reading. -/

example (Q : List Bool → Prop) (W : InNPWitnessStr Q) (cm km dm cs ks ds : Nat)
    (x : List Bool) :
    (FrontS1Comp.front_to_SAT_witness W.toInNPWitnessLangFreeSplit cm km dm cs ks ds).encodeIn x
      = certState x := W.encX_canonical x

/-- The canonical layout is one register holding one cell per bit … -/
example (x : List Bool) : State.size (certState x) = x.length :=
  State.size_certState x

/-- … and it is size-faithful in **both** directions. The lower bound is the one
the C8-4 finding of 2026-07-20-c said could not exist for an abstract `encX`; it
is what `InNPWitnessLangFreeSplit.sizeLB` now demands in general, and it is why
`FrontPieces.tallyCells` — built 2026-07 and parked unused — is finally wired
into `FrontProgram.frontProgram`, retiring the handed-over register. -/
example (x : List Bool) : x.length ≤ encodable.size x ∧ encodable.size x ≤ 2 * x.length :=
  ⟨length_le_size x, size_le_two_mul_length x⟩

/-- The honest headline, from the theorem the development already proves. -/
example : NPcompleteStr SAT :=
  NPcomplete''_to_NPcompleteStr CookLevinHonest.CookLevin''

end HonestyAuditProbe
