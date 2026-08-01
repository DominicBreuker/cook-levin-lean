import Complexity.NonVacuity

/-! # Non-vacuity, executed (top-down session 2026-08-03)

`CookLevin/Complexity/NonVacuity.lean` proves that the hypothesis of
`NPhardStr SAT` is neither empty (§3: a complete `InNPWitnessStr`) nor free
(§2: any inhabitant is decidable by brute-force search over its own verifier).
Those are theorems, gated by `lake build`.

This probe is the *executable* evidence for the part where "it is a running
program, not a classical existence statement" is the whole claim. Everything
below `#eval`s. Runtime: ~5 s.

**Re-run after** any change to `Complexity/NonVacuity.lean`, to `certState`, to
`Cmd.eval`/`Op.eval`, or to `InNPWitnessStr`.

⚠ The search is exponential *by design* — `searchDecide` enumerates
`2^(bound+1) - 1` certificates. Keep every `#eval` here at inputs of length
`≤ 6`; `squareCertRel.bound = id` and `encodable.size` of a bit string is up to
twice its length, so a length-10 input already means ~2 million verifier runs.
-/

open Complexity.Lang Complexity.NonVacuity

/-! ## 1 — the certificate enumeration is what it says it is -/

-- every bit string of length ≤ 2, and nothing else
#eval bitStringsUpTo 2
-- 2^(n+1) - 1 candidates
#eval (List.range 6).map (fun n => (bitStringsUpTo n).length)
#eval (List.range 6).all (fun n => (bitStringsUpTo n).length == 2 ^ (n + 1) - 1)

/-! ## 2 — the verifier is a real program, and it reads the certificate

The same input, two different certificates, two different answers. This is what
distinguishes an inhabitant of `inNPStr` from `HonestyAuditProbe` §7's planted
answer: nothing in `certState x` decides the outcome on its own. -/

#eval verifierAccepts squareWitness [true, false, true, false] [true, false]  -- true
#eval verifierAccepts squareWitness [true, false, true, false] [true, true]   -- false
#eval verifierAccepts squareWitness [true, false, true, false] []             -- false

-- the raw register layout the verifier runs on: input bits, then certificate bits
#eval strLayout [true, false, true, false] [true, false]
-- and the state it leaves behind (register 0 = the verdict)
#eval squareCmd.eval (strLayout [true, false, true, false] [true, false])
#eval squareCmd.eval (strLayout [true, false, true, true] [true, false])

/-! ## 3 — the brute-force decider RUNS

`searchDecide squareWitness squareCertRel.bound` is the function
`searchDecide_correct` proves equal to `SquareStr`. It is a `def`, so this
section is the difference between "a decider exists" (classically trivial) and
"here it is, and it agrees with the predicate". -/

/-- The decider of §2 at `SquareStr`'s own certificate bound. -/
def sqDecide : List Bool → Bool := searchDecide squareWitness squareCertRel.bound

#eval sqDecide []                                -- true  ([] = [] ++ [])
#eval sqDecide [true]                            -- false (odd length)
#eval sqDecide [true, true]                      -- true
#eval sqDecide [true, false]                     -- false (even, but not a square)
#eval sqDecide [true, false, true, false]        -- true
#eval sqDecide [true, false, false, true]        -- false

/-- Cross-check against an independent brute-force reference — no `Cmd`, no
verifier, just the predicate. If these ever disagree, either `squareVerifier`
does not decide `squareRel` or the search radius is too small. -/
def sqRef (x : List Bool) : Bool :=
  (bitStringsUpTo x.length).any (fun c => x == c ++ c)

#eval (bitStringsUpTo 6).all (fun x => sqDecide x == sqRef x)

/-! ## 4 — the payoff is a real term

`CookLevinStr`'s hardness half, applied to §3's witness. Elaborating this file
at all is the check: the whole chain accepts a concrete NP problem. -/

#check (squareStr_reducesPolyMO'_SAT : SquareStr ⪯p' SAT)
#print axioms Complexity.NonVacuity.squareStr_reducesPolyMO'_SAT
#print axioms Complexity.NonVacuity.searchDecide_correct
#print axioms Complexity.NonVacuity.inNPStr_squareStr

/-! ## 5 — what is NOT here

There is deliberately no `#eval` of a `FlatTM` deciding `SquareStr` by search:
`searchDecide` is a Lean function, not a compiled machine. The `Cmd`-level
search — the rung that would give `inNPStr Q → ∃ f, Nonempty (DecidesBy Q f)`
inside this development's own computability model — is the top-down item in
`HANDOFF.md`. Do not add a `#eval` here that suggests otherwise. -/
