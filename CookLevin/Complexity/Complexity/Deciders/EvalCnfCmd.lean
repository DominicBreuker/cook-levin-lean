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

/-! ### UNARY, bit-level encoding (Risk C2, B′ — the LIVE `sat_NP` encoding)

Every cell is `0`/`1` so the encoded state is a `Compile.BitState` (the compiled
machine's `sig = 4` alphabet only stays inside `{0,1}`-cells; see HANDOFF.md "The
invariant: BitState"). Numbers (variable indices) are therefore **unary** blocks
of `1`s, and every field is **self-delimiting** using only `0`/`1`:

* **literal** `(pol, v)` → `[1, polBit] ++ replicate v 1 ++ [0]`: a leading `1`
  sentinel ("a literal follows"), the polarity bit (`1` positive / `0` negative),
  the variable index in unary, then a `0` terminator.
* **clause** → `lit₀ ++ lit₁ ++ … ++ [0]`: the literal blocks, then a single `0`
  clause-end marker. At a literal slot the parser reads one cell: `1` ⇒ a literal
  follows; `0` ⇒ the clause is done (a literal always *starts* with `1`, so the
  two cases are unambiguous).
* **CNF** → the clauses concatenated (the outer loop bound `replicate N.length 1`
  fixes the clause count, so no CNF-level terminator is needed).
* **assignment** → per variable `u`: `[1] ++ replicate u 1 ++ [0]` (sentinel,
  unary value, terminator), concatenated. -/

/-- Encode one literal as a bit-level self-delimiting block
`[1, polBit] ++ replicate v 1 ++ [0]`. Every cell is `0`/`1`. -/
def encodeLit : literal → List Nat
  | (pol, v) => 1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0])

/-- Encode one clause as `lit₀ ++ lit₁ ++ … ++ [0]` (a `0` clause-end marker). -/
def encodeClause (C : clause) : List Nat :=
  (C.foldr (fun l acc => encodeLit l ++ acc) []) ++ [0]

/-- Encode a CNF as the concatenation of encoded clauses. -/
def encodeCnf (N : cnf) : List Nat :=
  N.foldr (fun C acc => encodeClause C ++ acc) []

/-- Encode an assignment: each variable `u` → `[1] ++ replicate u 1 ++ [0]`
(sentinel, unary value, terminator). Every cell is `0`/`1`. -/
def encodeAssgn (a : assgn) : List Nat :=
  a.foldr (fun u acc => (1 :: (List.replicate u 1 ++ [0])) ++ acc) []

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
| 9–11     | reserved scratch (loop indices / comparison temporaries)  |

All cells across every register are `0`/`1`, so the state is a `Compile.BitState`
(no `[CLAUSE_END]` constant is needed any more — a clause-end is a `0` cell). -/

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
def CONST_SCRATCH   : Var := 9   -- reserved scratch (was the CLAUSE_END constant)
def OUTER_IDX       : Var := 10  -- outer loop iteration index
def INNER_IDX       : Var := 11  -- inner loop iteration index

/-- The encoded input state. All 12 registers are bit-level (`Compile.BitState`). -/
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
    , []                                  -- 9: CONST_SCRATCH
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

/-! ## Bit-level (`Compile.BitState`) facts — every cell is `0`/`1`

These discharge the live `sat_NP` path's `enc_bit` obligation
(`Compile.BitState (encodeState x)`, see `EvalCnfTM.evalCnfDecidesLang`). -/

theorem encodeLit_bit (l : literal) : ∀ x ∈ encodeLit l, x ≤ 1 := by
  rcases l with ⟨pol, v⟩
  intro x hx
  simp only [encodeLit, List.mem_cons, List.mem_append, List.mem_replicate,
    List.not_mem_nil, or_false] at hx
  rcases hx with h | h | ⟨_, h⟩ | h
  · omega
  · cases pol <;> simp_all
  · omega
  · omega

theorem encodeClause_bit (C : clause) : ∀ x ∈ encodeClause C, x ≤ 1 := by
  intro x hx
  simp only [encodeClause, List.mem_append, List.mem_singleton] at hx
  rcases hx with hlits | h0
  · -- inside the folded literal blocks
    induction C with
    | nil => simp at hlits
    | cons l C ih =>
      simp only [List.foldr_cons, List.mem_append] at hlits
      rcases hlits with hl | hrest
      · exact encodeLit_bit l x hl
      · exact ih hrest
  · subst h0; exact Nat.zero_le 1

theorem encodeCnf_bit (N : cnf) : ∀ x ∈ encodeCnf N, x ≤ 1 := by
  intro x hx
  induction N with
  | nil => simp [encodeCnf] at hx
  | cons C N ih =>
    simp only [encodeCnf, List.foldr_cons, List.mem_append] at hx
    rcases hx with hC | hrest
    · exact encodeClause_bit C x hC
    · exact ih hrest

theorem encodeAssgn_bit (a : assgn) : ∀ x ∈ encodeAssgn a, x ≤ 1 := by
  intro x hx
  induction a with
  | nil => simp [encodeAssgn] at hx
  | cons u a ih =>
    simp only [encodeAssgn, List.foldr_cons] at hx
    rw [List.mem_append] at hx
    rcases hx with hblock | hrest
    · simp only [List.mem_cons, List.mem_append, List.mem_replicate,
        List.not_mem_nil, or_false] at hblock
      rcases hblock with h | ⟨_, h⟩ | h <;> omega
    · exact ih hrest

/-- **`Compile.BitState` of the encoded state.** Every register holds only
`0`/`1` cells: the tally and the unary blocks are `1`s, the markers/separators are
`0`, the polarity bit is `0`/`1`, and the scratch registers are empty. -/
theorem encodeState_bit (Na : cnf × assgn) : Compile.BitState (encodeState Na) := by
  rcases Na with ⟨N, a⟩
  intro reg hreg x hx
  simp only [encodeState, List.mem_cons, List.not_mem_nil, or_false] at hreg
  rcases hreg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · simp at hx
  · simp only [List.mem_replicate] at hx; omega
  · exact encodeCnf_bit N x hx
  · exact encodeAssgn_bit a x hx
  all_goals simp at hx

/-! ## Size accounting (toward `encodeIn_size`)

Under the unary encoding the encoded length grows with the *magnitudes* of the
variables, but `encodable.size Nat = id` charges exactly those magnitudes, so the
total size stays **linear** in `encodable.size`. These lemmas package that. -/

/-- `encodable.size` of a list, with the foldl accumulator unrolled to a foldr
sum (so it splits cleanly over `cons`). -/
private theorem foldl_encsize_acc {α : Type} [encodable α] :
    ∀ (acc : Nat) (xs : List α),
      xs.foldl (fun a x => a + encodable.size x + 1) acc
        = acc + xs.foldr (fun x s => encodable.size x + 1 + s) 0
  | acc, [] => by simp
  | acc, x :: xs => by
      simp only [List.foldl_cons, List.foldr_cons]
      rw [foldl_encsize_acc (acc + encodable.size x + 1) xs]; omega

private theorem encsize_list_foldr {α : Type} [encodable α] (xs : List α) :
    encodable.size xs = xs.foldr (fun x s => encodable.size x + 1 + s) 0 := by
  show xs.foldl (fun a x => a + encodable.size x + 1) 0 = _
  rw [foldl_encsize_acc 0 xs]; omega

private theorem length_le_encsize {α : Type} [encodable α] (xs : List α) :
    xs.length ≤ encodable.size xs := by
  rw [encsize_list_foldr xs]
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.foldr_cons, List.length_cons]; omega

private theorem encodeLit_length (l : literal) : (encodeLit l).length = l.2 + 3 := by
  rcases l with ⟨pol, v⟩
  simp only [encodeLit, List.length_cons, List.length_append, List.length_replicate,
    List.length_nil]

private theorem encodeClause_inner_length (C : clause) :
    (C.foldr (fun l acc => encodeLit l ++ acc) []).length
      = C.foldr (fun l s => l.2 + 3 + s) 0 := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      simp only [List.foldr_cons, List.length_append, encodeLit_length, ih]

private theorem encodeClause_inner_le (C : clause) :
    C.foldr (fun l s => l.2 + 3 + s) 0
      ≤ 4 * C.foldr (fun l s => encodable.size l + 1 + s) 0 := by
  induction C with
  | nil => simp
  | cons l C ih =>
      -- `l.2 : var` is opaque to `omega`; bound it via explicit `Nat` lemmas.
      have hl2 : l.2 ≤ encodable.size l :=
        calc l.2 ≤ encodable.size l.1 + l.2 := Nat.le_add_left l.2 (encodable.size l.1)
          _ ≤ encodable.size l.1 + l.2 + 1 := Nat.le_succ _
          _ = encodable.size l := rfl
      simp only [List.foldr_cons]
      -- now reason about the (Nat-valued) `encodable.size l` and the foldr atoms.
      calc l.2 + 3 + C.foldr (fun l s => l.2 + 3 + s) 0
          ≤ encodable.size l + 3 + 4 * C.foldr (fun l s => encodable.size l + 1 + s) 0 :=
            Nat.add_le_add (Nat.add_le_add_right hl2 3) ih
        _ ≤ 4 * (encodable.size l + 1
              + C.foldr (fun l s => encodable.size l + 1 + s) 0) := by omega

private theorem encodeClause_length_le (C : clause) :
    (encodeClause C).length ≤ 4 * encodable.size C + 1 := by
  have h1 : (encodeClause C).length = C.foldr (fun l s => l.2 + 3 + s) 0 + 1 := by
    simp only [encodeClause, List.length_append, List.length_cons, List.length_nil,
      encodeClause_inner_length]
  have h2 := encodeClause_inner_le C
  rw [h1, encsize_list_foldr C]
  omega

/-- Linear length bound for the unary CNF encoding. -/
theorem encodeCnf_length (N : cnf) :
    (encodeCnf N).length ≤ 5 * encodable.size N := by
  induction N with
  | nil => simp [encodeCnf]
  | cons C N ih =>
      have hlen : (encodeCnf (C :: N)).length
          = (encodeClause C).length + (encodeCnf N).length := by
        simp [encodeCnf, List.foldr_cons, List.length_append]
      have hsize : encodable.size (C :: N)
          = encodable.size C + 1 + encodable.size N := by
        rw [encsize_list_foldr (C :: N), encsize_list_foldr N, List.foldr_cons]
      have hC := encodeClause_length_le C
      rw [hlen, hsize]; omega

/-- Linear length bound for the unary assignment encoding. -/
theorem encodeAssgn_length_le (a : assgn) :
    (encodeAssgn a).length ≤ 2 * encodable.size a := by
  induction a with
  | nil => simp [encodeAssgn]
  | cons u a ih =>
      have hlen : (encodeAssgn (u :: a)).length = (u + 2) + (encodeAssgn a).length := by
        simp only [encodeAssgn, List.foldr_cons, List.cons_append, List.length_cons,
          List.length_append, List.length_replicate, List.length_nil]
        omega
      have hsize : encodable.size (u :: a) = u + 1 + encodable.size a := by
        have hu : encodable.size u = u := rfl
        rw [encsize_list_foldr (u :: a), encsize_list_foldr a, List.foldr_cons, hu]
      rw [hlen, hsize]; omega

/-- The encoded state's total size is **linearly** bounded by the input size
(`≤ 6 · size`). The unary blow-up is charged by `encodable.size Nat = id`; the
cubic cost bound `(n+1)^3` then absorbs it (see `EvalCnfTM.encodeIn_size`). -/
theorem encodeState_size_bound (Na : cnf × assgn) :
    State.size (encodeState Na) ≤ 6 * encodable.size Na := by
  rcases Na with ⟨N, a⟩
  have hsize : State.size (encodeState (N, a))
      = N.length + (encodeCnf N).length + (encodeAssgn a).length := by
    simp only [encodeState, State.size, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil, List.length_replicate, List.length_nil]
    omega
  have h1 := encodeCnf_length N
  have h2 := encodeAssgn_length_le a
  have h3 := length_le_encsize N
  have hNa : encodable.size (N, a) = encodable.size N + encodable.size a + 1 := rfl
  rw [hsize, hNa]; omega

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

/-! ## Notes for the inner-body author (parsing the unary stream)

The encoding is now **unary / bit-level** (`BitState`, discharged by
`encodeState_bit`). When closing the inner bodies, parse the stream with the
proven gadgets — every field is `{0,1}` and self-delimiting:

* **literal slot** (in `processOneClause`'s inner loop): read one cell from
  `CNF_STREAM`. A `1` means "a literal follows" — then the next cell is the
  polarity bit, then a run of `1`s is the variable (copy into `LIT_VAR` as a
  unary block, terminated by the `0`). A `0` means the clause is finished.
* **`memberCheck`**: `LIT_VAR` holds the variable in unary; scan a copy of
  `ASSGN` block-by-block (`[1] ++ unary ++ [0]`) and `Op.eqBit` the extracted
  unary block against `LIT_VAR`.

Two DSL conveniences would shorten these (optional, not required):
1. **A conditional/guarded loop** (`Cmd.while`) — the inner clause loop currently
   has to iterate over `|CNF_STREAM|` with a `clauseDone` no-op flag.
2. **A primitive "head-equals-value" / scan-to-separator op** — would compress
   the per-literal parse from several instructions to one or two.

`encodeIn_size` (size bound) is still open — see `encodeState_size_bound` /
`encodeCnf_length` above; the obligation is `State.size (encodeState (N,a)) ≤
(size (N,a) + 1)^3`, provable from the linear bound `State.size ≤ 3·size` (each
literal `(pol,v)` contributes `v+3` cells, charged by `size Nat = id`; product
`size ≥ 1` rules out the degenerate base case) dominated by the cube. -/

end EvalCnfCmd
