import Complexity.Lang
import Complexity.NP.SAT

set_option autoImplicit false

/-! # The SAT verifier as a `Lang.Cmd` (Part 3.5 of ROADMAP)

This file contains the concrete `Lang.Cmd` that decides
`fun (N, a) => satisfiesCnf a N` together with its input encoder
and its correctness / cost statements.

**Status (2026-06-09, top-down).** The encoding is concrete (unary/bit-level,
proven `BitState`, linear size accounting). The verifier's outer scaffold is
concrete, and its four consumer-facing theorems — `evalCnfCmd_decides`,
`evalCnfCmd_cost_bound`, `evalCnfCmd_usesBelow`, `evalCnfCmd_noConsLen` (all
four `evalCnfDecidesLang` fields) — are **PROVEN** from the **pinned
per-clause contracts** (`processOneClause_run`/`_cost`/`_usesBelow`/
`_noConsLen`). The remaining sorrys in this file are exactly those pins, the
recommended lower-level pins (`processOneLiteral_*`, `memberCheck_*`), and the
three body `Cmd`s — the bottom-up build targets. See the "Pinned inner-body
contracts" section for the interface and the "Notes for the inner-body
author" section for the intended construction.
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

**⚠ 2026-06-09 finding (top-down): the old 12-register frame was too tight.**
Counting the scratch the inner bodies need *simultaneously* (a clause-done flag
and, inside `memberCheck`, a persistent unary block accumulator + an in-block
parse flag, plus per-slot head/compare scratch), 12 registers left no room. The
frame is now **16** (`regBound = 16` in `EvalCnfTM.evalCnfDecidesLang`) with
four named scratch registers. `encodeState` still lays out only the first 12
registers — 12–15 read as `[]` and pad on first write (`State.get`/`set`
semantics) — so `width_le` (`12 ≤ 16`) and `enc_bit` are unaffected. Bumping
further is a one-line change (`regBound` + the `UsesBelow` targets) if the
bottom-up build needs more.

| Register | Contents                                                  |
|----------|-----------------------------------------------------------|
| 0        | `OUTPUT`: `[1]` (accept) or `[0]` (reject)                |
| 1        | `CLAUSE_TALLY`: `replicate N.length 1` (outer loop bound) |
| 2        | `CNF_STREAM`: encoded CNF (destructively consumed)        |
| 3        | `ASSGN`: encoded assignment (read-only)                   |
| 4        | `CLAUSE_SAT`: clause OR-accumulator (`[0]` or `[1]`)      |
| 5        | `LIT_POL`: current literal's polarity bit (`[0]`/`[1]`)   |
| 6        | `LIT_VAR`: current literal's variable, unary `1`-block    |
| 7        | `ASSGN_COPY`: assignment scan copy (destructively consumed) |
| 8        | `MEMBER_FOUND`: member-check result (`[0]` or `[1]`)      |
| 9        | `CLAUSE_DONE`: flag — current clause fully consumed       |
| 10       | `OUTER_IDX`: outer loop counter (set by `forBnd` machinery) |
| 11       | `INNER_IDX`: inner loop counter — **reusable by nested loops** (`forBnd` re-sets its counter before every iteration, so no state survives in it anyway) |
| 12       | `HEAD_CELL`: per-slot head-cell scratch (`Op.head` target) |
| 13       | `CMP_FLAG`: per-slot comparison/branch scratch (`Op.eqBit` target) |
| 14       | `IN_BLOCK`: `memberCheck` parse-state flag (inside a unary block vs. at a sentinel) |
| 15       | `BLOCK_ACC`: `memberCheck` unary block accumulator        |

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
def CLAUSE_DONE     : Var := 9   -- clause-consumed flag (was CONST_SCRATCH)
def OUTER_IDX       : Var := 10  -- outer loop iteration index
def INNER_IDX       : Var := 11  -- inner loop iteration index (nested-reusable)
def HEAD_CELL       : Var := 12  -- per-slot head-cell scratch
def CMP_FLAG        : Var := 13  -- per-slot comparison/branch scratch
def IN_BLOCK        : Var := 14  -- memberCheck parse-state flag
def BLOCK_ACC       : Var := 15  -- memberCheck unary block accumulator

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
    , []                                  -- 9: CLAUSE_DONE
    , []                                  -- 10: OUTER_IDX
    , []                                  -- 11: INNER_IDX
    ]                                     -- 12–15 (scratch) read as [] unset

/-! ## The verifier program -/

/-- Per-clause work: consume exactly one encoded clause from `CNF_STREAM` and
AND its satisfaction into `OUTPUT`. The contract this `Cmd` must satisfy is
**pinned** below (`processOneClause_run`/`_cost`/`_usesBelow`/`_noConsLen`) —
those four lemmas are the ONLY facts the proven assembly consumes. Intended
construction (see "Notes for the inner-body author"):

1. Reset `CLAUSE_SAT := [0]`, `CLAUSE_DONE := [0]`.
2. Inner `forBnd INNER_IDX CNF_STREAM` over the stream *cells* (the bound is
   read once at loop entry, so destructive consumption inside is fine). Each
   iteration, unless `CLAUSE_DONE`: peek the head cell — `1` ⇒ a literal
   follows (run `processOneLiteral`); `0` ⇒ the clause is done (consume the
   `0`, fold `OUTPUT := OUTPUT AND CLAUSE_SAT`, set `CLAUSE_DONE`).

**Skeleton stub.** -/
noncomputable def processOneClause : Cmd := sorry  -- TODO(Part3.5-clause)

/-- Per-literal work inside `processOneClause`'s inner loop: consume one whole
literal block `[1, polBit] ++ replicate v 1 ++ [0]` from `CNF_STREAM` (its own
flag-guarded sub-loop extracts the unary variable into `LIT_VAR`), run
`memberCheck`, and OR the literal's satisfaction (`eqBit` of `MEMBER_FOUND`
against `LIT_POL` — satisfied iff `evalVar a v = pol`) into `CLAUSE_SAT`.
Contract pinned below (`processOneLiteral_run`/`_cost`/…). -/
noncomputable def processOneLiteral : Cmd := sorry  -- TODO(Part3.5-literal)

/-- Membership test "`LIT_VAR`'s unary value `∈ ASSGN`": scan a copy of `ASSGN`
(`ASSGN_COPY`) cell-by-cell, accumulating each `[1] ++ unary ++ [0]` block into
`BLOCK_ACC` (parse state in `IN_BLOCK`), `eqBit`-ing each completed block
against `LIT_VAR`; sets `MEMBER_FOUND` to `[1]` on any match, `[0]` otherwise.
Contract pinned below (`memberCheck_run`/`_cost`/…). -/
noncomputable def memberCheck : Cmd := sorry  -- TODO(Part3.5-member)

/-! ## Pinned inner-body contracts — the bottom-up ⇄ top-down interface

**(2026-06-09, top-down session.)** These sorry lemmas are the *build targets*
for the bottom-up stream. The assembly below (`evalCnfCmd_decides`,
`evalCnfCmd_cost_bound`, `evalCnfCmd_usesBelow`, `evalCnfCmd_noConsLen` — all
four remaining `evalCnfDecidesLang` obligations) is **proven** from the
`processOneClause_*` quartet alone; the `processOneLiteral_*` / `memberCheck_*`
pins are the recommended decomposition for *building* `processOneClause` and
may be reshaped freely as long as the `processOneClause_*` quartet survives.

Design notes baked into the statements (do not weaken silently):

* **Frame discipline.** Each body may clobber only its declared scratch (the
  `r ∉ [...]` clause). In particular `CLAUSE_DONE` must survive `memberCheck`
  and `processOneLiteral` (it is `processOneClause`'s loop flag), and `OUTPUT`/
  `CLAUSE_TALLY`/`ASSGN` must survive everything. Loop *counters* are exempt
  state: `forBnd` re-sets its counter before every iteration, so nested loops
  may all reuse `INNER_IDX`.
* **Cost shape (⚠ uniform-bound accounting, NOT amortized).** The only loop
  cost tool is `Cmd.cost_forBnd_le` (uniform per-iteration bound), so each
  contract charges its *worst-case* slot cost times the full iteration count —
  amortization over "no-op" slots is NOT available. That compounds: memberCheck
  is quadratic, processOneLiteral quadratic, processOneClause cubic, and the
  whole verifier **quartic** (`evalCnfCmd_cost_bound`). The constants (`100`/
  `300`/`1000`) carry ~3× headroom over a straightforward implementation; if a
  body still misses its budget, bump the constant — the assembly arithmetic and
  `EvalCnfTM.timeBound` are the only ripple. Costs are stated against the
  *entry-state register lengths*, which is what `cost_forBnd_le` hands you.
* The hypotheses of the `_cost` lemmas mirror the `_run` lemmas because the
  bodies' control flow (hence cost) depends on the parsed input shape. -/

/-- **(pinned, bottom-up) `memberCheck` behaviour.** With `LIT_VAR` holding `v`
in unary and `ASSGN` holding an encoded assignment, `memberCheck` writes
`[if evalVar a v then 1 else 0]` to `MEMBER_FOUND` (where `evalVar a v =
decide (v ∈ a)`) and touches nothing outside its declared scratch. -/
theorem memberCheck_run (st : State) (v : Nat) (a : assgn)
    (hvar : st.get LIT_VAR = List.replicate v 1)
    (hassgn : st.get ASSGN = encodeAssgn a) :
    ((memberCheck.eval st).get MEMBER_FOUND = [if evalVar a v then 1 else 0])
    ∧ (∀ r : Var,
        r ∉ [ASSGN_COPY, MEMBER_FOUND, INNER_IDX, HEAD_CELL, CMP_FLAG,
             IN_BLOCK, BLOCK_ACC] →
        (memberCheck.eval st).get r = st.get r) := by
  sorry  -- TODO(Part3.5-member): gated on the concrete `memberCheck`

/-- **(pinned, bottom-up) `memberCheck` cost** — quadratic in the entry
lengths of the registers it reads (uniform-bound accounting: one pass over
`ASSGN_COPY` at `O(len)` worst-case slot cost, plus the `forBnd` counter
charge). -/
theorem memberCheck_cost (st : State) (v : Nat) (a : assgn)
    (hvar : st.get LIT_VAR = List.replicate v 1)
    (hassgn : st.get ASSGN = encodeAssgn a) :
    memberCheck.cost st
      ≤ 100 * ((st.get ASSGN).length + (st.get LIT_VAR).length + 1) ^ 2 := by
  sorry  -- TODO(Part3.5-member)

theorem memberCheck_usesBelow : Cmd.UsesBelow memberCheck 16 := by
  sorry  -- TODO(Part3.5-member): falls out of the concrete body (registers 0–15)

theorem memberCheck_noConsLen : Cmd.NoConsLen memberCheck := by
  sorry  -- TODO(Part3.5-member): immediate once concrete (no `consLen` needed)

/-- **(pinned, bottom-up) `processOneLiteral` behaviour.** With one encoded
literal at the head of `CNF_STREAM` and `CLAUSE_SAT` a boolean cell, it
consumes exactly the literal block and ORs the literal's satisfaction into
`CLAUSE_SAT`. `OUTPUT`, `CLAUSE_TALLY`, `ASSGN`, `CLAUSE_DONE` (and everything
`≥ 16`) survive. -/
theorem processOneLiteral_run (st : State) (l : literal) (rest : List Nat)
    (a : assgn) (cs : Bool)
    (hstream : st.get CNF_STREAM = encodeLit l ++ rest)
    (hassgn : st.get ASSGN = encodeAssgn a)
    (hsat : st.get CLAUSE_SAT = [if cs then 1 else 0]) :
    ((processOneLiteral.eval st).get CLAUSE_SAT
        = [if cs || evalLiteral a l then 1 else 0])
    ∧ ((processOneLiteral.eval st).get CNF_STREAM = rest)
    ∧ (∀ r : Var,
        r ∉ [CNF_STREAM, CLAUSE_SAT, LIT_POL, LIT_VAR, ASSGN_COPY,
             MEMBER_FOUND, INNER_IDX, HEAD_CELL, CMP_FLAG, IN_BLOCK,
             BLOCK_ACC] →
        (processOneLiteral.eval st).get r = st.get r) := by
  sorry  -- TODO(Part3.5-literal): gated on the concrete `processOneLiteral`

/-- **(pinned, bottom-up) `processOneLiteral` cost** — quadratic: the
unary-variable extraction sub-loop is `O(len)` slots at `O(len)` worst-case
slot cost, plus one `memberCheck` (quadratic). -/
theorem processOneLiteral_cost (st : State) (l : literal) (rest : List Nat)
    (a : assgn) (cs : Bool)
    (hstream : st.get CNF_STREAM = encodeLit l ++ rest)
    (hassgn : st.get ASSGN = encodeAssgn a)
    (hsat : st.get CLAUSE_SAT = [if cs then 1 else 0]) :
    processOneLiteral.cost st
      ≤ 300 * ((st.get CNF_STREAM).length + (st.get ASSGN).length + 1) ^ 2 := by
  sorry  -- TODO(Part3.5-literal)

theorem processOneLiteral_usesBelow : Cmd.UsesBelow processOneLiteral 16 := by
  sorry  -- TODO(Part3.5-literal)

theorem processOneLiteral_noConsLen : Cmd.NoConsLen processOneLiteral := by
  sorry  -- TODO(Part3.5-literal)

/-- **(pinned, bottom-up — THE interface) `processOneClause` behaviour.** This
is the contract the proven assembly consumes (via the loop invariant
`LoopInv`): with one encoded clause at the head of `CNF_STREAM`, the encoded
assignment in `ASSGN`, and `OUTPUT` a boolean cell, running `processOneClause`

* ANDs the clause's satisfaction into `OUTPUT`,
* consumes exactly the clause's block from `CNF_STREAM` (leaving `rest` — the
  re-establishment of the loop invariant for the next clause), and
* preserves `ASSGN`.

Deliberately *minimal* (weakest precondition the assembly can supply, only the
postconditions it needs) — scratch registers are unconstrained on entry, so
the body must reset whatever it relies on. -/
theorem processOneClause_run (st : State) (C : clause) (rest : List Nat)
    (a : assgn) (b : Bool)
    (hstream : st.get CNF_STREAM = encodeClause C ++ rest)
    (hassgn : st.get ASSGN = encodeAssgn a)
    (hout : st.get OUTPUT = [if b then 1 else 0]) :
    ((processOneClause.eval st).get OUTPUT
        = [if b && evalClause a C then 1 else 0])
    ∧ ((processOneClause.eval st).get CNF_STREAM = rest)
    ∧ ((processOneClause.eval st).get ASSGN = encodeAssgn a) := by
  sorry  -- TODO(Part3.5-clause): gated on the concrete `processOneClause`

/-- **(pinned, bottom-up — THE interface) `processOneClause` cost** — cubic in
the entry lengths (uniform-bound accounting: `|CNF_STREAM|` slots at
worst-case `processOneLiteral` cost — quadratic — plus the counter charge). -/
theorem processOneClause_cost (st : State) (C : clause) (rest : List Nat)
    (a : assgn) (b : Bool)
    (hstream : st.get CNF_STREAM = encodeClause C ++ rest)
    (hassgn : st.get ASSGN = encodeAssgn a)
    (hout : st.get OUTPUT = [if b then 1 else 0]) :
    processOneClause.cost st
      ≤ 1000 * ((st.get CNF_STREAM).length + (st.get ASSGN).length + 1) ^ 3 := by
  sorry  -- TODO(Part3.5-clause)

/-- **(pinned, bottom-up)** `processOneClause` touches only registers `0–15`. -/
theorem processOneClause_usesBelow : Cmd.UsesBelow processOneClause 16 := by
  sorry  -- TODO(Part3.5-clause): falls out of the concrete body

/-- **(pinned, bottom-up)** `processOneClause` uses no `Op.consLen` (none is
needed — the live path is `consLen`-free). -/
theorem processOneClause_noConsLen : Cmd.NoConsLen processOneClause := by
  sorry  -- TODO(Part3.5-clause)

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

/-! ## The proven assembly (top-down, 2026-06-09)

`evalCnfCmd`'s four `DecidesLang` obligations, proven from the pinned
`processOneClause_*` quartet via the `Frame.lean` loop toolkit
(`Cmd.eval_forBnd` + `Cmd.foldlState_range_induct` + `Cmd.cost_forBnd_le`,
sharing one invariant `LoopInv`). -/

/-- `encodeCnf` splits over `cons` — the foldr unfolds definitionally. -/
private theorem encodeCnf_cons (C : clause) (N : cnf) :
    encodeCnf (C :: N) = encodeClause C ++ encodeCnf N := rfl

private theorem encodeCnf_append (A B : cnf) :
    encodeCnf (A ++ B) = encodeCnf A ++ encodeCnf B := by
  induction A with
  | nil => simp [encodeCnf]
  | cons C A ih => rw [List.cons_append, encodeCnf_cons, encodeCnf_cons, ih,
      List.append_assoc]

/-- The stream only shrinks as clauses are consumed (the uniform per-iteration
cost bound needs this). -/
private theorem encodeCnf_drop_length_le (N : cnf) (i : Nat) :
    (encodeCnf (N.drop i)).length ≤ (encodeCnf N).length := by
  conv_rhs => rw [← List.take_append_drop i N]
  rw [encodeCnf_append, List.length_append]
  omega

/-- **The outer clause-loop invariant.** After `i` iterations: `OUTPUT` holds
the conjunction of the first `i` clauses' satisfaction, the stream holds the
remaining clauses, and the assignment is untouched. Shared by the correctness
proof (`foldlState_range_induct`) and the cost proof (`cost_forBnd_le`). -/
private def LoopInv (N : cnf) (a : assgn) (i : Nat) (st : State) : Prop :=
  st.get OUTPUT = [if evalCnf a (N.take i) then 1 else 0]
  ∧ st.get CNF_STREAM = encodeCnf (N.drop i)
  ∧ st.get ASSGN = encodeAssgn a

/-- One loop iteration preserves `LoopInv` — the bridge from the pinned
`processOneClause_run` contract to the loop toolkit's step obligation (the
`forBnd` machinery writes the counter `OUTER_IDX` before each iteration; the
relevant registers see through it by `State.get_set_ne`). -/
private theorem loopInv_step (N : cnf) (a : assgn) (i : Nat) (st : State)
    (hi : i < N.length) (h : LoopInv N a i st) :
    LoopInv N a (i + 1)
      (processOneClause.eval (st.set OUTER_IDX (List.replicate i 1))) := by
  obtain ⟨hout, hstream, hassgn⟩ := h
  have hout' : (st.set OUTER_IDX (List.replicate i 1)).get OUTPUT
      = [if evalCnf a (N.take i) then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide)]; exact hout
  have hstream' : (st.set OUTER_IDX (List.replicate i 1)).get CNF_STREAM
      = encodeClause N[i] ++ encodeCnf (N.drop (i + 1)) := by
    rw [State.get_set_ne _ _ _ _ (by decide), hstream,
      List.drop_eq_getElem_cons hi, encodeCnf_cons]
  have hassgn' : (st.set OUTER_IDX (List.replicate i 1)).get ASSGN
      = encodeAssgn a := by
    rw [State.get_set_ne _ _ _ _ (by decide)]; exact hassgn
  obtain ⟨ho, hs, ha⟩ := processOneClause_run _ N[i] (encodeCnf (N.drop (i + 1)))
    a (evalCnf a (N.take i)) hstream' hassgn' hout'
  have htake : evalCnf a (N.take (i + 1))
      = (evalCnf a (N.take i) && evalClause a N[i]) := by
    rw [List.take_succ_eq_append_getElem hi]
    show (N.take i ++ [N[i]]).all (evalClause a)
        = ((N.take i).all (evalClause a) && evalClause a N[i])
    rw [List.all_append]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
  exact ⟨by rw [ho, htake], hs, ha⟩

/-- The init op (`appendOne OUTPUT`) on the encoded input sets `OUTPUT := [1]`. -/
private theorem init_eval (N : cnf) (a : assgn) :
    Op.eval (Op.appendOne OUTPUT) (encodeState (N, a))
      = (encodeState (N, a)).set OUTPUT [1] := by
  have h0 : (encodeState (N, a)).get OUTPUT = [] := by
    simp [encodeState, State.get, OUTPUT]
  show (encodeState (N, a)).set OUTPUT ((encodeState (N, a)).get OUTPUT ++ [1])
      = _
  rw [h0]; rfl

/-- The loop invariant holds at entry (after the init op). -/
private theorem loopInv_zero (N : cnf) (a : assgn) :
    LoopInv N a 0 ((encodeState (N, a)).set OUTPUT [1]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [State.get_set_eq]; simp [evalCnf]
  · rw [State.get_set_ne _ _ _ _ (by decide)]
    simp [encodeState, State.get, CNF_STREAM]
  · rw [State.get_set_ne _ _ _ _ (by decide)]
    simp [encodeState, State.get, ASSGN]

/-- The outer loop's bound register after the init op: `N.length` iterations. -/
private theorem init_tally (N : cnf) (a : assgn) :
    ((encodeState (N, a)).set OUTPUT [1]).get CLAUSE_TALLY
      = List.replicate N.length 1 := by
  rw [State.get_set_ne _ _ _ _ (by decide)]
  simp [encodeState, State.get, CLAUSE_TALLY]

/-- **Correctness (PROVEN from the pinned `processOneClause_run`).** Running
`evalCnfCmd` on the encoded input produces `[1]` in `OUTPUT` iff
`satisfiesCnf a N` — by the loop invariant `LoopInv` over the clause loop. -/
theorem evalCnfCmd_decides :
    Cmd.decides evalCnfCmd encodeState
      (fun Na : cnf × assgn => satisfiesCnf Na.2 Na.1) := by
  rintro ⟨N, a⟩
  have hrun : evalCnfCmd.eval (encodeState (N, a))
      = (Cmd.forBnd OUTER_IDX CLAUSE_TALLY processOneClause).eval
          ((encodeState (N, a)).set OUTPUT [1]) := by
    simp only [evalCnfCmd, Cmd.eval_seq, Cmd.eval_op, init_eval]
  have hfinal : LoopInv N a N.length (evalCnfCmd.eval (encodeState (N, a))) := by
    rw [hrun, Cmd.eval_forBnd, init_tally, List.length_replicate]
    exact Cmd.foldlState_range_induct processOneClause OUTER_IDX N.length _
      (LoopInv N a) (loopInv_zero N a)
      (fun i st hi h => loopInv_step N a i st hi h)
  obtain ⟨hO, -, -⟩ := hfinal
  rw [List.take_length] at hO
  have hO0 : (evalCnfCmd.eval (encodeState (N, a))).get 0
      = [if evalCnf a N then 1 else 0] := hO
  cases hEv : evalCnf a N <;>
    simp_all [satisfiesCnf, State.isAccept, State.isReject]

/-- The closing arithmetic for the cost bound: the assembled total against the
quartic budget. Atoms are kept linear for `omega` via explicit power facts. -/
private theorem cost_final_arith (m : Nat) :
    3 + 125000 * m ^ 4 + m * m ≤ 200000 * (m + 1) ^ 4 := by
  have hpos : 1 ≤ (m + 1) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos m)
  have h4 : m ^ 4 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_left (Nat.le_succ m) 4
  have h2 : m * m ≤ (m + 1) ^ 4 := by
    calc m * m ≤ (m + 1) * ((m + 1) * ((m + 1) * (m + 1))) := by nlinarith
      _ = (m + 1) ^ 4 := by ring
  have h4' : 125000 * m ^ 4 ≤ 125000 * (m + 1) ^ 4 :=
    Nat.mul_le_mul_left 125000 h4
  omega

/-- **Cost bound (PROVEN from the pinned `processOneClause_cost`).**

**⚠ 2026-06-09 finding (top-down): the old cubic budget `(n+1)^3` was
unprovable.** The only loop-cost tool is `Cmd.cost_forBnd_le` (a *uniform*
per-iteration bound), so the verifier's cost is charged as
`|clauses| × worst-case-clause-cost` — and the worst-case clause cost is itself
cubic in the stream length (slots × worst-case literal cost, with `memberCheck`
quadratic), NOT the amortized cubic total the old docstring assumed.
Amortization is invisible to uniform-bound accounting, and building an
amortized (potential-function) `cost_forBnd` is unjustified: downstream only
needs `inOPoly`, so the degree is free. Hence the **quartic** budget with an
explicit constant: `|N| · 1000·(7n+1)³ + |N|² + 3 ≤ 200000·(n+1)⁴`. -/
theorem evalCnfCmd_cost_bound (Na : cnf × assgn) :
    evalCnfCmd.cost (encodeState Na)
      ≤ 200000 * (encodable.size Na + 1) ^ 4 := by
  rcases Na with ⟨N, a⟩
  -- the per-iteration uniform budget
  set B := 1000 * ((encodeCnf N).length + (encodeAssgn a).length + 1) ^ 3 with hB
  -- the loop cost, via `cost_forBnd_le` with the shared invariant
  have hfor : (Cmd.forBnd OUTER_IDX CLAUSE_TALLY processOneClause).cost
      ((encodeState (N, a)).set OUTPUT [1])
      ≤ 1 + N.length * B + N.length * N.length := by
    have hlen : (((encodeState (N, a)).set OUTPUT [1]).get CLAUSE_TALLY).length
        = N.length := by rw [init_tally, List.length_replicate]
    have h := Cmd.cost_forBnd_le OUTER_IDX CLAUSE_TALLY processOneClause
      ((encodeState (N, a)).set OUTPUT [1]) B (LoopInv N a) (loopInv_zero N a)
      (fun i st hi h => loopInv_step N a i st (by rwa [hlen] at hi) h)
      (fun i st hi h => by
        -- per-iteration cost from the pinned contract, monotonized to `B`
        obtain ⟨hout, hstream, hassgn⟩ := h
        have hi' : i < N.length := by rwa [hlen] at hi
        have hout' : (st.set OUTER_IDX (List.replicate i 1)).get OUTPUT
            = [if evalCnf a (N.take i) then 1 else 0] := by
          rw [State.get_set_ne _ _ _ _ (by decide)]; exact hout
        have hstream' : (st.set OUTER_IDX (List.replicate i 1)).get CNF_STREAM
            = encodeCnf (N.drop i) := by
          rw [State.get_set_ne _ _ _ _ (by decide)]; exact hstream
        have hassgn' : (st.set OUTER_IDX (List.replicate i 1)).get ASSGN
            = encodeAssgn a := by
          rw [State.get_set_ne _ _ _ _ (by decide)]; exact hassgn
        have hdecomp : (st.set OUTER_IDX (List.replicate i 1)).get CNF_STREAM
            = encodeClause N[i] ++ encodeCnf (N.drop (i + 1)) := by
          rw [hstream', List.drop_eq_getElem_cons hi', encodeCnf_cons]
        have hc := processOneClause_cost _ N[i] (encodeCnf (N.drop (i + 1)))
          a (evalCnf a (N.take i)) hdecomp hassgn' hout'
        refine hc.trans ?_
        rw [hB]
        refine Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left ?_ 3)
        rw [hstream', hassgn']
        have := encodeCnf_drop_length_le N i
        omega)
    rwa [hlen] at h
  -- the seq/init overhead
  have htotal : evalCnfCmd.cost (encodeState (N, a))
      = 2 + (Cmd.forBnd OUTER_IDX CLAUSE_TALLY processOneClause).cost
          ((encodeState (N, a)).set OUTPUT [1]) := by
    simp only [evalCnfCmd, Cmd.cost_seq, Cmd.cost_op, Cmd.eval_op, init_eval]
    rfl
  -- size arithmetic: everything against `m := size (N, a)`
  have hsplit : encodable.size (N, a)
      = encodable.size N + encodable.size a + 1 := rfl
  have hNlen : N.length ≤ encodable.size (N, a) := by
    have := length_le_encsize N; omega
  have hBle : B ≤ 125000 * encodable.size (N, a) ^ 3 := by
    have hcnf := encodeCnf_length N
    have hass := encodeAssgn_length_le a
    have h5 : (encodeCnf N).length + (encodeAssgn a).length + 1
        ≤ 5 * encodable.size (N, a) := by omega
    calc B ≤ 1000 * (5 * encodable.size (N, a)) ^ 3 :=
          Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left h5 3)
      _ = 125000 * encodable.size (N, a) ^ 3 := by ring
  have hNB : N.length * B
      ≤ 125000 * encodable.size (N, a) ^ 4 := by
    calc N.length * B
        ≤ encodable.size (N, a) * (125000 * encodable.size (N, a) ^ 3) :=
          Nat.mul_le_mul hNlen hBle
      _ = 125000 * encodable.size (N, a) ^ 4 := by ring
  have hNN : N.length * N.length
      ≤ encodable.size (N, a) * encodable.size (N, a) :=
    Nat.mul_le_mul hNlen hNlen
  have := cost_final_arith (encodable.size (N, a))
  omega

/-- **Register frame (PROVEN from the pinned `processOneClause_usesBelow`).**
The whole verifier touches only registers `0–15`. -/
theorem evalCnfCmd_usesBelow : Cmd.UsesBelow evalCnfCmd 16 := by
  show Op.UsesBelow (.appendOne OUTPUT) 16
    ∧ (OUTER_IDX < 16 ∧ CLAUSE_TALLY < 16 ∧ Cmd.UsesBelow processOneClause 16)
  exact ⟨(by decide : OUTPUT < 16), by decide, by decide,
    processOneClause_usesBelow⟩

/-- **`consLen`-freedom (PROVEN from the pinned `processOneClause_noConsLen`).** -/
theorem evalCnfCmd_noConsLen : Cmd.NoConsLen evalCnfCmd := by
  show Op.NotConsLen (.appendOne OUTPUT) ∧ Cmd.NoConsLen processOneClause
  exact ⟨trivial, processOneClause_noConsLen⟩

/-! ## Notes for the inner-body author (parsing the unary stream)

The encoding is **unary / bit-level** (`BitState`, discharged by
`encodeState_bit`); every field is `{0,1}` and self-delimiting. The build
targets are exactly the pinned sorry lemmas above — the assembly is already
proven from the `processOneClause_*` quartet. Intended construction (the
`processOneLiteral_*`/`memberCheck_*` pins; reshape freely as long as the
quartet survives):

* **`processOneClause`** = reset (`CLAUSE_SAT := [0]`, `CLAUSE_DONE := [0]`)
  `;;` `forBnd INNER_IDX CNF_STREAM` over the stream *cells* (`forBnd` reads
  the bound's length once at entry, so consuming `CNF_STREAM` inside is fine;
  one whole clause needs at most `|encodeClause C| ≤ |CNF_STREAM|` active
  iterations — the rest no-op on `CLAUSE_DONE`). Per iteration, unless
  `CLAUSE_DONE`: `Op.head HEAD_CELL CNF_STREAM`; `ifBit HEAD_CELL` — `1` ⇒ run
  `processOneLiteral`; `0` ⇒ `Op.tail CNF_STREAM CNF_STREAM` (consume the
  clause-end), fold `OUTPUT := OUTPUT AND CLAUSE_SAT` (via `ifBit CLAUSE_SAT`:
  else-branch `clear OUTPUT ;; appendZero OUTPUT`), set `CLAUSE_DONE := [1]`.
* **`processOneLiteral`**: consume the leading `1` and the polarity bit (into
  `LIT_POL`, as `[0]`/`[1]`); extract the unary variable run into `LIT_VAR`
  with a flag-guarded sub-loop over `CNF_STREAM` (consume `1`-cells via
  `head`+`tail`+`appendOne LIT_VAR` until the `0` terminator, consume it too);
  run `memberCheck`; the literal is satisfied iff `MEMBER_FOUND = LIT_POL` as
  single-bit registers (`evalLiteral a (pol,v) = decide (evalVar a v = pol)`)
  — `Op.eqBit CMP_FLAG MEMBER_FOUND LIT_POL`, then `ifBit CMP_FLAG` ORs into
  `CLAUSE_SAT`.
* **`memberCheck`**: `copy ASSGN_COPY ASSGN`, clear `MEMBER_FOUND`/`IN_BLOCK`/
  `BLOCK_ACC`, then a cell-per-iteration `forBnd` over `ASSGN_COPY`: at a
  sentinel `1` (when `¬IN_BLOCK`) start a block (`clear BLOCK_ACC`, set
  `IN_BLOCK`); inside a block, a `1` appends to `BLOCK_ACC`, a `0` ends the
  block — `eqBit CMP_FLAG BLOCK_ACC LIT_VAR`, OR into `MEMBER_FOUND`, clear
  `IN_BLOCK`. (`v = 0` works: empty block vs. empty `LIT_VAR`, `eqBit [] []`.)
  Set `MEMBER_FOUND := [0]` initially so it is `[0]`/`[1]` in all cases.

**Probe each body end-to-end with `#eval` (`Cmd.run` is computable on concrete
states) before attempting its `_run`/`_cost` lemma** — the bodies are plain
data; only the `sorry` stubs make the defs `noncomputable` today.

Two DSL conveniences would shorten these (optional, not required):
1. **A conditional/guarded loop** (`Cmd.while`) — the cell loops must iterate
   `|CNF_STREAM|`/`|ASSGN_COPY|` times with done-flag no-ops. (This is also
   what forces the uniform-bound quartic cost — see `evalCnfCmd_cost_bound`.)
2. **A primitive scan-to-separator op** — would compress the per-literal parse.
Each new `Op` is another compiler soundness case (C5 policy: only add when it
materially shortens things); the flag-guarded loops above work with the ops we
have. -/

end EvalCnfCmd
