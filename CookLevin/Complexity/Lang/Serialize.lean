import Complexity.Complexity.Definitions

set_option autoImplicit false

/-! # `Serialize` — a canonical, decodable, size-faithful tape encoding

**Why this class exists (top-down risk S5, structurally).** `⪯p'` bottoms out in
`ComputesBy`, which carries two *free functions* on either side of a real
machine:

```lean
structure ComputesBy (f : X → Y) (timeBound : Nat → Nat) where
  encode : X → List Nat        -- ← arbitrary, may even be noncomputable
  M      : FlatTM
  decode : FlatTMConfig → Y    -- ← arbitrary
  computes : …
```

Set `encode x := ⟨serialized f x⟩`, `M := id`, `decode := read it back` and every
field is discharged — `probes/HonestyAuditProbe.lean` §6 is exactly that witness,
sorry-free, yielding a real `polyTimeComputable'`. By FINDING AK the honesty
surface of a `comp`-built witness is only the **leftmost `encodeIn`** and the
**rightmost `decodeOut`**, so those two free functions are the *whole* hole, and
both ends of the chain have concrete types. Pinning them to a canonical
per-type serializer turns the standing per-witness *reading* obligation into a
one-time *typechecking* one.

## The four laws, and what each one buys

| field | what it rules out |
|---|---|
| `dec_enc` | a lossy/answer-only layout: `dec ∘ enc = some` forces injectivity, so `enc x` still determines `x` |
| `enc_bit` | numbers smuggled into a single cell (the layer's states are `BitState`) |
| `size_le_enc_length` | **compression**: `encodable.size x` is recoverable from the encoding's own cell count, up to a fixed polynomial `sizeLB` |
| `enc_length_le` | blow-up: the encoding is polynomially bounded in `encodable.size` |

The last two are the **sandwich** `size x ≤ sizeLB |enc x|` and
`|enc x| ≤ encLen (size x)`, and the lower half is the one the *head* of the
chain needs. `FrontProgram`'s monomial
argument must dominate budgets stated in `encodable.size x`; the front witness
currently gets that by having `encodeIn` **hand over** a unary size register
`1^(size x)` (`FrontWitness.encodeInQ`), because the C8-4 finding of 2026-07-20-c
established that `State.size (encX x)` has only an *upper* bound to
`encodable.size x` — `encX` need not be injective, so no program can recover
`size x` from the input. `size_le_enc_length` is exactly the missing direction:
with it the tally is computable on-machine (`FrontPieces.tallyCells`) and the
handed-over register can go.

## ⚠ FINDING AT (2026-08-05): the no-compression law is a POLYNOMIAL law

`size_le_enc_length` used to read `encodable.size x ≤ (enc x).length` — the
identity form. That form is **unsatisfiable for the canonical bit-string
layout**, and the canonical bit-string layout is not negotiable: it is
`certState`, the one register with one `0`/`1` cell per bit that the whole
`NPhardStr` statement is pinned to. The obstruction is arithmetic and has
nothing to do with compression:

```
encodable.size ([true] : List Bool) = 2      -- the generic list instance
                                             -- charges 1 per element PLUS
                                             -- `size true = 1`
(strBits [true]).length              = 1
```

i.e. `encodable.size` on `List Bool` *over*-counts by up to a factor two, so a
layout that is a bijection onto `{0,1}^n` — which cannot compress anything —
fails the identity form. Any instance that satisfied it would have to spend two
cells on a bit, and would then no longer agree with `certState`; the development
would carry two different serializations of a bit string and a reviewer would
have to check they denote the same strings. That is strictly worse.

The fix is the form the rest of the development already uses for exactly this
obligation: `InNPWitnessLangFreeSplit.sizeLB` (2026-08-02) asks for a
*polynomial* recovering `encodable.size x` from the layout's own cell count, and
`InNPWitnessStr` discharges it with `fun n => 2 * n`. The purpose of the law is
served identically — a program reading `enc x` builds `1^|enc x|` and applies
`sizeLB` on-machine (`FrontPieces.tallyCells` + `FrontProgram.unaryMonomial`) —
so the law is generalised here, not weakened in substance. `Serialize cnf` keeps
the identity (`sizeLB := id`, `CnfSerialize.size_le_encodeCnf_length`), so
nothing about the current chain end changes.

⚠ **What this does cost.** The identity form was checkable by eye; the
polynomial form is only meaningful because `sizeLB` must be `inOPoly` and
`monotonic`. An instance that supplied a huge `sizeLB` would satisfy the letter
of the law while encoding a single bit as `[]`; the guard against that is
`dec_enc` (injectivity), which no `sizeLB` can weaken. State a *small* `sizeLB`
or explain why not.

⚠ **This is NOT the retired `LangEncodable` layer.** That died because its
*generic, nestable product instance* was size-unsound
(`probes/UnaryProductSizeProbe.lean`: `enc (x,y) = 1^|enc x| ++ [0] ++ enc x ++
enc y` doubles the first component per nesting level). There is deliberately **no
generic product instance here**, and none is needed: by FINDING AK only the two
*ends* of the chain are honesty-relevant, and both are concrete types. The middle
of the chain keeps its bespoke bit-level layouts untouched.
-/

namespace Complexity.Lang

/-- A canonical tape serialization for `X`: a bit-level encoding with a real
parser, no compression against `encodable.size`, and polynomial blow-up.

Instances are **per concrete type and chosen once** — that is the point. A type
gets an instance because a human read the encoder and agreed it is the natural
one; every witness that uses the type then inherits that single reading, instead
of owing its own. -/
class Serialize (X : Type) [encodable X] where
  /-- The canonical layout of `x` as one register's worth of tape cells. -/
  enc : X → List Nat
  /-- The parser. Total: junk input maps to `none`. -/
  dec : List Nat → Option X
  /-- **The law that makes `enc` honest**: it is decodable, hence injective, so
  it cannot be "the answer" — it still carries all of `x`. -/
  dec_enc : ∀ x, dec (enc x) = some x
  /-- Every cell is a bit (`Compile.BitState` fodder). -/
  enc_bit : ∀ x, ∀ v ∈ enc x, v ≤ 1
  /-- **No compression**, as a polynomial law (FINDING AT). `encodable.size x`
  is recoverable from the encoding's own cell count up to `sizeLB` — so a
  program reading `enc x` can count its cells and build a unary register that
  dominates any `encodable.size x`-stated budget. Same shape as
  `InNPWitnessLangFreeSplit.sizeLB`; keep it small (`id` or `2 * ·`). -/
  sizeLB : Nat → Nat
  sizeLB_poly : inOPoly sizeLB
  sizeLB_mono : monotonic sizeLB
  size_le_enc_length : ∀ x, encodable.size x ≤ sizeLB (enc x).length
  /-- The blow-up bound, as a polynomial. -/
  encLen : Nat → Nat
  encLen_poly : inOPoly encLen
  encLen_mono : monotonic encLen
  enc_length_le : ∀ x, (enc x).length ≤ encLen (encodable.size x)

namespace Serialize

variable {X : Type} [encodable X] [Serialize X]

/-- `enc` is injective — the content of `dec_enc`, in the form the honesty
argument uses. -/
theorem enc_injective : Function.Injective (enc (X := X)) := by
  intro a b h
  have ha : dec (enc a) = some a := dec_enc a
  have hb : dec (enc b) = some b := dec_enc b
  rw [h, hb] at ha
  exact (Option.some.inj ha).symm

/-- The total decoder used at a chain end: parse, and fall back to `d` off the
image. The fallback is never reached on a real run (`dec_enc`), and it is a
*constant* — it cannot branch on anything. -/
def decodeD (d : X) (l : List Nat) : X := (dec l).getD d

@[simp] theorem decodeD_enc (d : X) (x : X) : decodeD d (enc x) = x := by
  unfold decodeD; rw [dec_enc x]; rfl

end Serialize

end Complexity.Lang
