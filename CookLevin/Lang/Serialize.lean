import CookLevin.Basic.Definitions

/-!
# Serializable data

`Serialize α` is a class of types with an injective encoding into bit registers and a
decoder that inverts it, so that a program computing a function into `α` can produce its
result in a register and have it read back by `decodeD`. Instances are given for the data
types occurring on the reduction chain.
-/

set_option autoImplicit false

namespace CookLevin.Lang

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
  /-- `enc` is decodable, hence injective. -/
  dec_enc : ∀ x, dec (enc x) = some x
  /-- Every cell is a bit (`Compile.BitState` fodder). -/
  enc_bit : ∀ x, ∀ v ∈ enc x, v ≤ 1
  /-- **No compression**, as a polynomial law. `encodable.size x`
  is recoverable from the encoding's own cell count up to `sizeLB` — so a
  program reading `enc x` can count its cells and build a unary register that
  dominates any `encodable.size x`-stated budget. Same shape as
  `NPWitness.sizeLB`; keep it small (`id` or `2 * ·`). -/
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

/-- The total decoder used at a chain end: parse, and fall back to `d` off the
image. The fallback is never reached on a real run (`dec_enc`), and it is a
*constant* — it cannot branch on anything. -/
def decodeD (d : X) (l : List Nat) : X := (dec l).getD d

@[simp] theorem decodeD_enc (d : X) (x : X) : decodeD d (enc x) = x := by
  unfold decodeD; rw [dec_enc x]; rfl

end Serialize

end CookLevin.Lang
