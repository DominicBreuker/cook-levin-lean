import Complexity.Lang.Semantics
open Complexity.Lang

/-! # `eqBit` op-gadget design probe (bottom-up, 2026-06-14b)

`eqBit dst src1 src2` sets `dst := [1]` if `s.get src1 = s.get src2` else `[0]`,
non-destructively on `src1`/`src2`. It is the ONLY op the live `sat_NP` decider
still needs (see HANDOFF). The settled design (HANDOFF "What this session did"):

* **Wrapper** = the proven `Compile.nonEmptyRawM` template verbatim — a
  `branchComposeFlatTM` whose tester is a comparison machine `compareRegsTM`
  halting in EQ/NEQ, with the two `nonEmptyBranchBody dst {2,1}` branches
  (rewind ⨾ clear `dst` ⨾ append the answer bit). Only `compareRegsTM` is novel.

* **`compareRegsTM` must be a clean 2-outcome `loopTM`** (`loopTM` has exactly one
  terminal halt: `loopHalt B = replicate B.states false ++ [true]`). The verdict
  EQ vs NEQ is therefore recovered AFTER the loop, not as two loop exits.

This probe validates — for ALL inputs, by a sorry-free induction, not just
`#eval` — the load-bearing **decision contract** of design (A)'s consume loop:

> Run a loop whose body ITERATEs while *both operands are nonempty AND their
> heads are equal* (deleting both heads) and DONEs otherwise. Then the operands
> were equal **iff both are empty when the loop stops**.

So the post-loop verdict is just "are both scratch registers empty?" — two proven
`navigateAndTestTM`s — with no on-tape flag and no scratch flag register. -/

namespace EqBitProbe

/-- The consume loop's pure semantics: peel matching heads off both lists,
stopping at the first mismatch or when either list empties. The returned pair is
the operands' residue when the loop halts (DONE). -/
def consumeLoop : List Nat → List Nat → (List Nat × List Nat)
  | [],      r2      => ([], r2)
  | r1,      []      => (r1, [])
  | a :: r1, b :: r2 => if a = b then consumeLoop r1 r2 else (a :: r1, b :: r2)

/-- The post-loop verdict: EQ iff BOTH residues are empty. -/
def eqVerdict (r1 r2 : List Nat) : Bool :=
  let (s1, s2) := consumeLoop r1 r2
  s1.isEmpty && s2.isEmpty

/-- **The decision contract is correct for all inputs.** This is the structural
fact design (A) rests on: the consume loop + "both empty?" test decides list
equality. (`compareRegsTM`'s run lemma must establish exactly this at the TM
level — the body ITERATE/DONE outcomes mirror the three match clauses below.) -/
theorem eqVerdict_correct : ∀ r1 r2 : List Nat, eqVerdict r1 r2 = (r1 = r2 : Bool) := by
  intro r1
  induction r1 with
  | nil =>
      intro r2
      cases r2 with
      | nil => rfl
      | cons b r2 => simp [eqVerdict, consumeLoop]
  | cons a r1 ih =>
      intro r2
      cases r2 with
      | nil => simp [eqVerdict, consumeLoop]
      | cons b r2 =>
          by_cases hab : a = b
          · subst hab
            simp only [eqVerdict, consumeLoop] at *
            simpa using ih r2
          · simp [eqVerdict, consumeLoop, hab, List.cons.injEq]

/-! ## `#eval` sanity checks (all `true`) -/

-- equal (incl. both empty) → true; differ in a bit / in length → false.
#eval eqVerdict [1, 0, 1] [1, 0, 1]            -- equal
#eval eqVerdict [] []                          -- both empty → equal
#eval !eqVerdict [1, 0] [1, 1]                 -- bit mismatch
#eval !eqVerdict [1, 0] [1, 0, 1]              -- r1 prefix of r2 (length)
#eval !eqVerdict [1, 0, 1] [1, 0]              -- r2 prefix of r1 (length)
#eval !eqVerdict [1] []                        -- one empty
#eval eqVerdict [0, 0, 0] [0, 0, 0]            -- equal, all-zero bits

/-! ## Budget / cost note (the open question for the build)

`Op.cost eqBit = 1` ⇒ the contract budget is `(9L²+9L+30)·(cost+1) ≈ 18L²`.
Design (A) (consume two **copies**) spends ~2 full `copyLoop`s (≈10 passes/bit)
+ the consume loop (≈5 passes/bit) ⇒ ~15–20 scan-passes/bit, i.e. BORDERLINE
against 18L². The next step (d2a in HANDOFF) is to `#eval` the assembled design-A
machine's real step count vs `18L²`; if it overshoots, take the owner-approved
`Op.cost eqBit` bump (only ripple: EvalCnf's `timeBound` constant), or switch to
design (B) (in-place caterpillar, ≈8 passes/bit, fits `cost=1`, no scratch). -/

end EqBitProbe
