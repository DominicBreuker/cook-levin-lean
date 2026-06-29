/-! # Unary-product size-soundness probe (bottom-up, Risk C2, 2026-06-29)

**★ BLOCKING FINDING — the `UnaryMigrationProbe` (2026-06-28) was incomplete.**
It validated round-tripping and `BitState` of the proposed bit-level product
encoding `enc(x,y) = replicate |enc x| 1 ++ [0] ++ enc x ++ enc y`, but it never
checked the **`LangEncodable.enc_size` contract**
(`PolyTime.lean:572`):

```
enc_size : ∀ x, (enc x).length ≤ 2 * encodable.size x + 1
```

This `#eval` probe (axiom-free, pure core; run with
`lean probes/UnaryProductSizeProbe.lean`) shows the proposed encoding **violates
that contract — exponentially**. The unary length prefix has length `|enc x|`, so

```
|enc(x,y)| = |enc x| + 1 + |enc x| + |enc y| = 2·|enc x| + 1 + |enc y|
```

i.e. the **first component doubles at every nesting level**. For a left-nested
pair of depth `d` with leaves of size `m`, `|enc| = 2^d·(m+1) − 1`, while
`encodable.size = m + d` (so the bound `2·size+1` is linear in `d`). No fixed
polynomial `B` can satisfy the generic-instance obligation
`B(a+b+1) ≥ 2·B(a) + B(b) + 1` (the recurrence forces `B(n) = Θ(2^n)`), so the
**generic `LangEncodable (X × Y)` instance for this encoding cannot exist** — its
`enc_size` field is not merely hard to prove, it is *false* (witnessed below).

By contrast the **old** single-cell encoding `enc(x,y) = |enc x| :: (enc x ++
enc y)` is size-tight (`|enc| = 1 + |enc x| + |enc y| = encodable.size`) and
satisfies the bound — but its prefix cell holds the *value* `|enc x|`, which is
`≥ 2` whenever `|enc x| ≥ 2`, so it is **not `BitState`** (the very reason the
migration wanted to replace it).

**Conclusion: bit-level + polynomial-size + generic-nestable is not achievable
with a unary length prefix.** Any *inline* self-delimiting scheme (unary prefix,
continuation-bit interleave, bit-doubling escape) costs `Ω(|enc x|)` extra and
compounds under nesting. The only sound bit-level option is an `O(log)` **binary
length prefix** (e.g. Elias-γ), which forces (a) loosening `enc_size` to a
*polynomial* (a quadratic closes; the log term breaks any linear bound), and
(b) a runtime **binary→unary** count gadget for the restated trio. See
`CookLevin/HANDOFF.md` bottom-up step 2 for the redesign. -/

abbrev Reg := List Nat

/-- `encodable.size`: `Nat = id`; this probe uses unary `Nat` (bit-level). -/
def encNat (n : Nat) : Reg := List.replicate n 1

/-- NEW (proposed) product encoding — bit-level, but unary length prefix. -/
def encProd    (A B : Reg) : Reg := List.replicate A.length 1 ++ [0] ++ A ++ B
/-- OLD product encoding — size-tight single cell, but NOT bit-level. -/
def encProdOld (A B : Reg) : Reg := A.length :: (A ++ B)

/-- Left-nested pair of depth `d`, leaves of size `m`, `(·, 0)` at each level.
`encodable.size` of this value is `m + d`. -/
def leftNestNew : Nat → Nat → Reg
  | 0,   m => encNat m
  | d+1, m => encProd (leftNestNew d m) (encNat 0)
def leftNestOld : Nat → Nat → Reg
  | 0,   m => encNat m
  | d+1, m => encProdOld (leftNestOld d m) (encNat 0)

/-- The `enc_size` bound `2 · encodable.size + 1` at depth `d`, leaves `m`. -/
def encSizeBound (d m : Nat) : Nat := 2 * (m + d) + 1

def isBit (r : Reg) : Bool := r.all (· ≤ 1)

/-- Per-depth table: `(NEW length, OLD length, bound, NEW ≤ bound?, OLD ≤ bound?)`. -/
def row (d m : Nat) : Nat × Nat × Nat × Bool × Bool :=
  ((leftNestNew d m).length, (leftNestOld d m).length, encSizeBound d m,
   decide ((leftNestNew d m).length ≤ encSizeBound d m),
   decide ((leftNestOld d m).length ≤ encSizeBound d m))

/-! ## 1. Single-instance violation: `enc((10,5),0)` already overflows -/

-- `enc((10,5),0)` length `53` > bound `2·size+1 = 35`. Expect `false`.
#eval decide ((encProd (encProd (encNat 10) (encNat 5)) (encNat 0)).length ≤ 35)

/-! ## 2. Exponential blow-up (NEW) vs. linear (OLD) vs. the bound -/

-- depths 0..6, m=8. NEW lengths `8,17,35,71,143,287,575` (= `2^d·9−1`) — the
-- NEW `≤bound?` flag flips to `false` at depth 2; OLD stays `true` throughout.
#eval ((List.range 7).map (fun d => row d 8))

/-! ## 3. `BitState`: NEW is bit-level, OLD is not (the original motivation) -/

-- NEW depth-3 encoding is all `0/1`; OLD has a `≥ 2` value cell. `(true,false)`.
#eval (isBit (leftNestNew 3 8), isBit (leftNestOld 3 8))
