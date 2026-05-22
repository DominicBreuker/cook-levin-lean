import Complexity.Lang
import Complexity.NP.SAT

set_option autoImplicit false

/-! # The SAT verifier as a `Lang.Cmd` (Part 3.5 of ROADMAP)

This file contains the concrete `Lang.Cmd` that decides
`fun (N, a) => satisfiesCnf a N` together with its input encoder
and its correctness / cost statements.

**Skeleton status.** The encoding is concrete. The verifier program
is committed at the outer-scaffolding level — the per-clause and
per-literal bookkeeping is marked with focused sorrys, each of
which is a small Cmd-engineering task (~10–30 lines of DSL per
sorry). The correctness and cost theorems are sorry-bodied.

The point of this file is to expose the *shape* of the SAT verifier
in the DSL so that any expressiveness gaps in `Lang.Cmd` surface
immediately. See the bottom of this file for a list of gaps
identified during the skeleton pass.
-/

namespace EvalCnfCmd

open Complexity.Lang

/-! ## Encoding of the input -/

/-- Encode one literal as a 2-cell block.
- positive literal `(true, v)`  → `[0, v + 3]`
- negative literal `(false, v)` → `[1, v + 3]`

Polarity uses cells `{0, 1}`; variable values are shifted by `+3`
to leave room for the polarity codes and the clause-end marker. -/
def encodeLit : literal → List Nat
  | (true,  v) => [0, v + 3]
  | (false, v) => [1, v + 3]

/-- Sentinel value marking the end of a clause inside the encoded CNF. -/
def CLAUSE_END : Nat := 2

/-- Encode one clause as `lit_0 ++ lit_1 ++ … ++ [CLAUSE_END]`. -/
def encodeClause (C : clause) : List Nat :=
  (C.foldr (fun l acc => encodeLit l ++ acc) []) ++ [CLAUSE_END]

/-- Encode a CNF as the concatenation of encoded clauses. -/
def encodeCnf (N : cnf) : List Nat :=
  N.foldr (fun C acc => encodeClause C ++ acc) []

/-- Encode an assignment: shift each variable by `+3` to match the
literal encoding's variable encoding. -/
def encodeAssgn (a : assgn) : List Nat := a.map (· + 3)

/-! ## Register layout

| Register | Contents                                                  |
|----------|-----------------------------------------------------------|
| 0        | output: `[1]` (accept) or `[0]` (reject)                  |
| 1        | clause-count tally: `List.replicate N.length 1` (loop bound) |
| 2        | encoded CNF (destructively consumed)                      |
| 3        | encoded assignment (read-only)                            |
| 4        | clause-sat OR-accumulator (`[0]` or `[1]`, per clause)    |
| 5        | current literal's polarity cell                           |
| 6        | current literal's variable cell                           |
| 7        | scratch: assignment scan copy (destructively consumed)    |
| 8        | scratch: member-check result (`[0]` or `[1]`)             |
| 9–11     | reserved for constant comparisons (e.g. `[2]` for CLAUSE_END)|
-/

-- Symbolic register names; using `def` over `abbrev` so the proofs
-- don't substitute them blindly.
def OUTPUT          : Var := 0
def CLAUSE_TALLY    : Var := 1
def CNF_STREAM      : Var := 2
def ASSGN           : Var := 3
def CLAUSE_SAT      : Var := 4
def LIT_POL         : Var := 5
def LIT_VAR         : Var := 6
def ASSGN_COPY      : Var := 7
def MEMBER_FOUND    : Var := 8
def CONST_CE        : Var := 9   -- holds `[CLAUSE_END] = [2]`
def OUTER_IDX       : Var := 10  -- outer loop iteration index
def INNER_IDX       : Var := 11  -- inner loop iteration index

/-- The encoded input state. -/
def encodeState : cnf × assgn → State
  | (N, a) =>
    [ []                                  -- 0: OUTPUT
    , List.replicate N.length 1           -- 1: CLAUSE_TALLY
    , encodeCnf N                         -- 2: CNF_STREAM
    , encodeAssgn a                       -- 3: ASSGN
    , []                                  -- 4: CLAUSE_SAT
    , []                                  -- 5: LIT_POL
    , []                                  -- 6: LIT_VAR
    , []                                  -- 7: ASSGN_COPY
    , []                                  -- 8: MEMBER_FOUND
    , [CLAUSE_END]                        -- 9: CONST_CE
    , []                                  -- 10: OUTER_IDX
    , []                                  -- 11: INNER_IDX
    ]

/-! ## The verifier program -/

/-- Per-clause work: process one clause from `CNF_STREAM` and fold
the result into `OUTPUT`. Concretely:

1. Reset `CLAUSE_SAT := [0]`.
2. Inner loop over `CNF_STREAM` (bounded by `|CNF_STREAM|`, with
   early no-op after the clause's `CLAUSE_END` marker has been seen).
3. After the inner loop: `OUTPUT := OUTPUT AND CLAUSE_SAT`.

**Skeleton stub.** -/
noncomputable def processOneClause : Cmd := sorry  -- TODO(Part3.5-clause)

/-- Per-literal work inside `processOneClause`'s inner loop: read
two cells (polarity, variable) from `CNF_STREAM`, check satisfaction
against `ASSGN`, OR the result into `CLAUSE_SAT`. -/
noncomputable def processOneLiteral : Cmd := sorry  -- TODO(Part3.5-literal)

/-- Membership test `LIT_VAR ∈ ASSGN`. Inner loop over a copy of
`ASSGN` comparing each element with `LIT_VAR`; sets `MEMBER_FOUND`
to `[1]` on match, `[0]` otherwise. -/
noncomputable def memberCheck : Cmd := sorry  -- TODO(Part3.5-member)

/-- The full SAT verifier. The outer scaffold is concrete; the
per-clause / per-literal bodies are deferred to focused sorrys. -/
noncomputable def evalCnfCmd : Cmd :=
  -- 1. Initialize OUTPUT := [1] (accept by default; reject on first
  --    unsatisfied clause).
  Cmd.op (.appendOne OUTPUT) ;;
  -- 2. Outer loop: once per clause.
  Cmd.forBnd OUTER_IDX CLAUSE_TALLY processOneClause

/-! ## Correctness and cost obligations -/

theorem encodeCnf_length (N : cnf) :
    (encodeCnf N).length ≤ 3 * encodable.size N + 1 := by
  sorry  -- TODO(Part3.5-encode-size)

theorem encodeAssgn_length (a : assgn) :
    (encodeAssgn a).length = a.length := by
  unfold encodeAssgn
  exact List.length_map _

/-- The encoded state's total size is linearly bounded by the input
size. (The exact constant doesn't matter — the cost bound
`(n + 1) ^ 3` absorbs any linear blow-up.) -/
theorem encodeState_size_bound (Na : cnf × assgn) :
    State.size (encodeState Na) ≤ 5 * encodable.size Na + 20 := by
  sorry  -- TODO(Part3.5-encode-size)

/-- **Correctness.** Running `evalCnfCmd` on the encoded input
produces `[1]` in `OUTPUT` iff `satisfiesCnf a N`. -/
theorem evalCnfCmd_decides :
    Cmd.decides evalCnfCmd encodeState
      (fun Na : cnf × assgn => satisfiesCnf Na.2 Na.1) := by
  sorry  -- TODO(Part3.5-correctness)

/-- **Cost bound.** Running `evalCnfCmd` is cubic in input size. The
outer loop runs `|N|` times; each `processOneClause` runs through the
full `|CNF_STREAM|`; each literal's `memberCheck` scans `|ASSGN|`.
Total: `|N| · |CNF_STREAM| · |ASSGN|` ≤ `(n + 1) ^ 3`. -/
theorem evalCnfCmd_cost_bound (Na : cnf × assgn) :
    evalCnfCmd.cost (encodeState Na) ≤ (encodable.size Na + 1) ^ 3 := by
  sorry  -- TODO(Part3.5-cost-bound)

/-! ## Gaps surfaced by writing this file

The Cmd-level sketch is structurally clean (5 small sorrys for the
inner bodies plus 4 sorrys for the bound/correctness obligations),
but it surfaces three issues with the current DSL that are worth
recording before we close the inner sorrys:

1. **No conditional loop.** The inner clause loop must iterate over
   `|CNF_STREAM|` cells (not just `|clause|` cells), with a
   `clauseDone` flag toggled to no-op after we've seen the clause's
   `CLAUSE_END`. With a `Cmd.while`-style guarded loop, this would
   be cleaner and asymptotically faster.

2. **No primitive constant comparison.** To test "is the head of
   `CNF_STREAM` equal to `CLAUSE_END`?" we have to preload `[2]`
   into a register (here `CONST_CE`) and use `Op.eqBit`. Cheap, but
   adds a register and a setup step per constant. A primitive
   `Op.headEqVal dst src (n : Nat)` would compress every literal
   parse from ~5 instructions to ~2.

3. **`DecidesLang.encodeIn_size`'s bound was too tight.** ✅
   Relaxed in this same pass: the field now reads
   `State.size (encodeIn x) ≤ costBound (encodable.size x)`,
   which makes any real linear encoding provable (the cost bound
   is polynomial). `evalCnfTM.lean` still has one sorry for this
   field — the obligation is `5·n + 20 ≤ (n+1)^3` for the input
   size `n`, with a base-case check for small `n`.

(1) and (2) are reasonable extensions to make before closing the
per-clause / per-literal sorrys, since they significantly shorten
the eventual Cmds.
-/

end EvalCnfCmd
