import Complexity.NP.SAT.CookLevin.Reductions.S1Witness

/-! # S1 probe — the head-layout size honesty gap, and the constants that fix it

**Finding (2026-07-25, top-down S1).** `PolyTimeComputableLang.encodeIn_size`
demands `State.size (HeadLayout.headEncodeIn x) ≤ encBound (encodable.size x)`
with `encBound` polynomial. The former `encodable FlatTM` (`sizeFlatTM`,
"Approximate: each transition has ~5 components") charged a **flat 5 per
transition entry**, ignoring the entry payloads — so the machine register
`encSyms (flattenTM M)` grew without bound at *constant* `encodable.size M`,
and the field was unsatisfiable. §1 exhibits the counterexample family; §2
checks the constants of the honest replacement.

Run: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/S1SizeGapProbe.lean`
-/

open HeadLayout Complexity.Simulators

/-! ## §1 — the gap (values below are for the CURRENT, honest instance;
under the old `sizeFlatTM` all four `size` entries read `12`). -/

/-- A one-entry machine whose transition carries a huge destination state. -/
def bigM (k : Nat) : FlatTM :=
  { sig := 2, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some 0],
                dst_state := k, dst_write_vals := [some 1],
                move_dirs := [TMMove.Rmove] }] }

/-- …and one with a huge symbol payload. -/
def bigW (k : Nat) : FlatTM :=
  { sig := 2, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some k],
                dst_state := 1, dst_write_vals := [some k],
                move_dirs := [TMMove.Rmove] }] }

-- (honest size, machine-register length). The OLD measure returned 12 for
-- every row while the register length is 52 / 1052 / 10052 / 10052.
#eval (encodable.size (bigM 0), (encSyms (flattenTM (bigM 0))).length)
#eval (encodable.size (bigM 1000), (encSyms (flattenTM (bigM 1000))).length)
#eval (encodable.size (bigM 10000), (encSyms (flattenTM (bigM 10000))).length)
#eval (encodable.size (bigW 5000), (encSyms (flattenTM (bigW 5000))).length)

/-! ## §2 — the constants asserted in `S1Witness.lean`

`flattenTM_size_le : encodable.size (flattenTM M) ≤ 3 * encodable.size M + 3`
(PROVEN 2026-07-26 — see §3 for why the additive term is forced) and,
downstream of it,
`headEncodeIn_size_le : State.size (headEncodeIn x) ≤ 8 * encodable.size x + 4`.
Both must print `true` on every row. -/

def checkFlatten (M : FlatTM) : Bool :=
  decide (encodable.size (flattenTM M) ≤ 3 * encodable.size M + 3)

def checkHead (M : FlatTM) (s : List Nat) (mx st : Nat) : Bool :=
  Complexity.Lang.State.size (headEncodeIn (M, s, mx, st))
    ≤ 8 * encodable.size ((M, s, mx, st) : flatTM × List Nat × Nat × Nat) + 4

/-- A wide machine: many entries, many tapes, many symbols. -/
def wideM : FlatTM :=
  { sig := 4, tapes := 3, states := 5, start := 2,
    halt := [false, false, true, false, true],
    trans := (List.range 7).map (fun i =>
      { src_state := i % 5, src_tape_vals := [some (i % 4), none, some 3],
        dst_state := (i + 2) % 5, dst_write_vals := [none, some 2, some (i % 4)],
        move_dirs := [TMMove.Lmove, TMMove.Nmove, TMMove.Rmove] }) }

#eval (checkFlatten validFlatTM_default, checkFlatten (bigM 0),
       checkFlatten (bigM 1000), checkFlatten (bigW 5000), checkFlatten wideM)

#eval (checkHead validFlatTM_default [] 0 0,
       checkHead (bigM 1000) [0, 1, 1] 4 6,
       checkHead (bigW 5000) [1, 0] 3 9,
       checkHead wideM [0, 1, 2, 3] 7 11)

/-! ## §3 — the emitter target

What the S1 program must actually produce on registers 1–5 for a tiny instance:
`S1Witness.s1Key (S1Map.s1Map x)`. Printed as register lengths — the card
register is the `Θ(|trans|·|Σ|⁴)` stream the bottom-up card-emitter owns. -/

def tinyM : FlatTM :=
  { sig := 1, tapes := 1, states := 2, start := 0, halt := [false, true],
    trans := [{ src_state := 0, src_tape_vals := [some 0],
                dst_state := 1, dst_write_vals := [some 0],
                move_dirs := [TMMove.Rmove] }] }

-- the guard must hold for this instance (`validFlatTM`, `tapes = 1`, `s` in range)
#eval S1Map.s1GuardB tinyM [0]

-- output register lengths: [Sigma, init, cards, final, steps]
#eval (S1Witness.s1Key (S1Map.s1Map (tinyM, [0], 1, 1))).map List.length

-- input register lengths of the frozen head layout, same instance
#eval (headEncodeIn (tinyM, [0], 1, 1)).map List.length

/-! ## §3 — why `flattenTM_size_le` needs an ADDITIVE term (2026-07-26)

The statement carried here until 2026-07-26 was
`encodable.size (flattenTM M) ≤ 3 * encodable.size M`, with the comment "the
constant `3` has slack". It is **FALSE**. `flattenTM` always writes six header
cells (`sig`, `tapes`, `states`, `start`, `|halt|`, `|trans|`), and a machine
whose `encodable.size` is `1` cannot pay for six cells multiplicatively.

The three witnesses below print `(size M, size (flattenTM M), old claim,
new claim)`. The old claim is `false` on all three; the new bound
`3·size M + 3` is TIGHT on the first and the third.

The lesson for future size lemmas: a bound on an encoding with a **fixed-size
header** always needs an additive term, and a probe that only samples
non-degenerate instances will not see it. Probe the empty/zero machine. -/

def degenM : List FlatTM :=
  [-- the trivial machine: size 1, stream [0,0,0,0,0,0] of size 6
   { sig := 0, tapes := 0, states := 0, start := 0, halt := [], trans := [] },
   -- one alphabet symbol: size 2, stream size 7
   { sig := 1, tapes := 0, states := 0, start := 0, halt := [], trans := [] },
   -- one empty transition entry: size 3, stream size 12 (tight at 3·3+3)
   { sig := 0, tapes := 0, states := 0, start := 0, halt := [],
     trans := [{ src_state := 0, src_tape_vals := [], dst_state := 0,
                 dst_write_vals := [], move_dirs := [] }] }]

#eval degenM.map (fun M => (encodable.size M, encodable.size (flattenTM M),
  decide (encodable.size (flattenTM M) ≤ 3 * encodable.size M),
  decide (encodable.size (flattenTM M) ≤ 3 * encodable.size M + 3)))
-- expect [(1, 6, false, true), (2, 7, false, true), (3, 12, false, true)]

#eval degenM.all checkFlatten     -- expect true
