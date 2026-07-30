import Complexity.NP.SAT.CookLevin.CookLevinHonest

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

/-! ## §2 — the head layout: `encodeInQ` is the input, plus a size tally

`encodeIn x = W.encX x ++ [1^(size x)]`. `W.encX` is the *hypothesis witness's
own* input layout — the layout `Q`'s verifier already reads — and the extra
register is `encodable.size x` in unary, a metric of the input. Neither
component mentions `fQ`, `s1Map`, satisfiability, or `Q x`.

The verdict this pins: the only non-`encX` register is a **tally**, and the
front program consumes it (`FrontProgram.unaryMonomial`) to build `maxSize`
and `steps` on-machine. -/

section Head
variable {X : Type} [encodable X] {Q : X → Prop}

example (W : InNPWitnessLangFreeSplit Q) (x : X) :
    FrontWitness.encodeInQ W x
      = W.encX x ++ [List.replicate (encodable.size x) 1] := rfl

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

/-! ## §3 — the tail decoder is the inverse of the output layout

`decodeOut s = invFun encodeCnf (get s CNFOUT)`: read one designated register
and invert an **injective** serialization (`KSat3Free.encodeCnf_injective`).
It does not look at the input, and it does not branch. -/

example (s : State) :
    FSATSATFree.decodeOut s
      = Function.invFun EvalCnfCmd.encodeCnf (State.get s FSATSATFree.CNFOUT) := rfl

example : FSATSATFree.CNFOUT = 2 := rfl

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

end HonestyAuditProbe
