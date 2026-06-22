import Complexity.Lang
import Complexity.NP.SAT

set_option autoImplicit false

/-! # The SAT verifier as a `Lang.Cmd` (Part 3.5 of ROADMAP)

This file contains the concrete `Lang.Cmd` that decides
`fun (N, a) => satisfiesCnf a N` together with its input encoder
and its correctness / cost statements.

**Status (2026-06-10, bottom-up): COMPLETE — this file is sorry-free and
axiom-clean.** The encoding is concrete (unary/bit-level, proven `BitState`,
linear size accounting); the three inner bodies (`processOneClause`/
`processOneLiteral`/`memberCheck`) are concrete `Cmd`s, `#eval`-probe-validated
end-to-end and **proven** against the pinned contracts
(`processOneClause_run`/`_cost`/`_usesBelow`/`_noConsLen` and the lower-level
quartets); the four consumer-facing theorems (`evalCnfCmd_decides`/
`_cost_bound`/`_usesBelow`/`_noConsLen` — all four `evalCnfDecidesLang`
fields) are proven from them. `EvalCnfTM.evalCnfDecidesLang` is axiom-clean;
what `sat_NP` still owes is only the compiler gadgets (Risk C2, Compile.lean).
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

/-- A constant-cost (`3`) no-op (`CMP_FLAG := [1]`). Used as the idle branch of
flag-guarded loop bodies. `CMP_FLAG` is declared scratch in every contract
below. It is built from `clear ⨾ appendOne` (each `1`, plus `1` for the seq) so
its cost is a **state-independent constant**: this matters now that `eqBit` is
size-aware (`Op.cost eqBit = |src1|+|src2|+1`), under which the old
`eqBit CMP_FLAG CMP_FLAG CMP_FLAG` realisation would cost `2·|CMP_FLAG|+1` and a
`copy r r` "no-op" would cost `|r|+1` — either way data-dependent, breaking the
uniform per-iteration cost bound. -/
def mcSkip : Cmd := Cmd.op (.clear CMP_FLAG) ;; Cmd.op (.appendOne CMP_FLAG)

/-- One iteration of `memberCheck`'s scan: consume one cell of `ASSGN_COPY`
into `HEAD_CELL` and step the block parser (`IN_BLOCK`/`BLOCK_ACC`; on a
block-end `0`, compare the accumulated unary block against `LIT_VAR` and OR
the result into `MEMBER_FOUND`). Spec: `mcStep`. -/
def mcBody : Cmd :=
  Cmd.op (.head HEAD_CELL ASSGN_COPY) ;;
  Cmd.op (.tail ASSGN_COPY ASSGN_COPY) ;;
  Cmd.ifBit IN_BLOCK
    (Cmd.ifBit HEAD_CELL
      (Cmd.op (.appendOne BLOCK_ACC))
      (Cmd.op (.eqBit CMP_FLAG BLOCK_ACC LIT_VAR) ;;
       Cmd.ifBit CMP_FLAG
         (Cmd.op (.clear MEMBER_FOUND) ;; Cmd.op (.appendOne MEMBER_FOUND))
         mcSkip ;;
       Cmd.op (.clear IN_BLOCK) ;; Cmd.op (.appendZero IN_BLOCK)))
    (Cmd.ifBit HEAD_CELL
      (Cmd.op (.clear BLOCK_ACC) ;;
       Cmd.op (.clear IN_BLOCK) ;; Cmd.op (.appendOne IN_BLOCK))
      mcSkip)

/-- Membership test "`LIT_VAR`'s unary value `∈ ASSGN`": scan a copy of `ASSGN`
(`ASSGN_COPY`) cell-by-cell, accumulating each `[1] ++ unary ++ [0]` block into
`BLOCK_ACC` (parse state in `IN_BLOCK`), `eqBit`-ing each completed block
against `LIT_VAR`; sets `MEMBER_FOUND` to `[1]` on any match, `[0]` otherwise.
Contract pinned below (`memberCheck_run`/`_cost`/…). -/
def memberCheck : Cmd :=
  Cmd.op (.copy ASSGN_COPY ASSGN) ;;
  Cmd.op (.clear MEMBER_FOUND) ;; Cmd.op (.appendZero MEMBER_FOUND) ;;
  Cmd.op (.clear IN_BLOCK) ;; Cmd.op (.appendZero IN_BLOCK) ;;
  Cmd.op (.clear BLOCK_ACC) ;;
  Cmd.forBnd INNER_IDX ASSGN_COPY mcBody

/-- One iteration of `processOneLiteral`'s unary-variable extraction: while
`IN_BLOCK`, consume one cell of `CNF_STREAM` — a `1` extends `LIT_VAR`, the
`0` terminator ends the block (clears `IN_BLOCK`). Idle otherwise. -/
def varExtractBody : Cmd :=
  Cmd.ifBit IN_BLOCK
    (Cmd.op (.head HEAD_CELL CNF_STREAM) ;;
     Cmd.op (.tail CNF_STREAM CNF_STREAM) ;;
     Cmd.ifBit HEAD_CELL
       (Cmd.op (.appendOne LIT_VAR))
       (Cmd.op (.clear IN_BLOCK)))
    mcSkip

/-- Per-literal work inside `processOneClause`'s inner loop: consume one whole
literal block `[1, polBit] ++ replicate v 1 ++ [0]` from `CNF_STREAM` (its own
flag-guarded sub-loop extracts the unary variable into `LIT_VAR`), run
`memberCheck`, and OR the literal's satisfaction (`eqBit` of `MEMBER_FOUND`
against `LIT_POL` — satisfied iff `evalVar a v = pol`) into `CLAUSE_SAT`.
Contract pinned below (`processOneLiteral_run`/`_cost`/…). -/
def processOneLiteral : Cmd :=
  Cmd.op (.tail CNF_STREAM CNF_STREAM) ;;      -- consume the leading `1` sentinel
  Cmd.op (.head LIT_POL CNF_STREAM) ;;          -- LIT_POL := [polBit]
  Cmd.op (.tail CNF_STREAM CNF_STREAM) ;;       -- consume the polarity bit
  Cmd.op (.clear LIT_VAR) ;;
  Cmd.op (.clear IN_BLOCK) ;; Cmd.op (.appendOne IN_BLOCK) ;;
  Cmd.forBnd INNER_IDX CNF_STREAM varExtractBody ;;
  memberCheck ;;
  Cmd.op (.eqBit CMP_FLAG MEMBER_FOUND LIT_POL) ;;
  Cmd.ifBit CMP_FLAG
    (Cmd.op (.clear CLAUSE_SAT) ;; Cmd.op (.appendOne CLAUSE_SAT))
    mcSkip

/-- One iteration of `processOneClause`'s scan: unless `CLAUSE_DONE`, peek the
stream head — `1` ⇒ a literal follows (`processOneLiteral` consumes the whole
block); `0` ⇒ the clause is done (consume it, AND `CLAUSE_SAT` into `OUTPUT`,
set `CLAUSE_DONE`). Idle once done. -/
def clauseBody : Cmd :=
  Cmd.ifBit CLAUSE_DONE
    mcSkip
    (Cmd.op (.head HEAD_CELL CNF_STREAM) ;;
     Cmd.ifBit HEAD_CELL
       processOneLiteral
       (Cmd.op (.tail CNF_STREAM CNF_STREAM) ;;
        Cmd.ifBit CLAUSE_SAT
          mcSkip
          (Cmd.op (.clear OUTPUT) ;; Cmd.op (.appendZero OUTPUT)) ;;
        Cmd.op (.clear CLAUSE_DONE) ;; Cmd.op (.appendOne CLAUSE_DONE)))

/-- Per-clause work: consume exactly one encoded clause from `CNF_STREAM` and
AND its satisfaction into `OUTPUT`. The contract this `Cmd` must satisfy is
**pinned** below (`processOneClause_run`/`_cost`/`_usesBelow`/`_noConsLen`) —
those four lemmas are the ONLY facts the proven assembly consumes.

1. Reset `CLAUSE_SAT := [0]`, `CLAUSE_DONE := [0]`.
2. Inner `forBnd INNER_IDX CNF_STREAM` over the stream *cells* (the bound is
   read once at loop entry, so destructive consumption inside is fine), body
   `clauseBody` — one literal block per active iteration. -/
def processOneClause : Cmd :=
  Cmd.op (.clear CLAUSE_SAT) ;; Cmd.op (.appendZero CLAUSE_SAT) ;;
  Cmd.op (.clear CLAUSE_DONE) ;; Cmd.op (.appendZero CLAUSE_DONE) ;;
  Cmd.forBnd INNER_IDX CNF_STREAM clauseBody

/-! ## Inner-body proofs (bottom-up, 2026-06-10)

The bodies above are proven against the pinned contracts below via per-iteration
step lemmas (`mcBody_step`/`varExtractBody_step`/`clauseBody_step` — each a
single case-bash over the branch conditions, giving the evaluated registers AND
a uniform cost bound) plugged into the `Frame.lean` loop toolkit
(`Cmd.foldlState_range_induct` for behaviour, `Cmd.cost_forBnd_le` for cost,
sharing one invariant per loop). `memberCheck`'s loop is specified by a tiny
parser automaton `mcStep` folded over the consumed cells. -/

/-- `memberCheck`'s parser state: `(inBlock, accumulated unary length, found)`.
One automaton step per consumed cell of the encoded assignment. -/
private def mcStep (v : Nat) : Bool × Nat × Bool → Nat → Bool × Nat × Bool
  | (true, acc, found), cell =>
      if cell = 1 then (true, acc + 1, found)
      else (false, acc, found || decide (acc = v))
  | (false, acc, found), cell =>
      if cell = 1 then (true, 0, found) else (false, acc, found)

private theorem replicate_one_eq_iff {a b : Nat} :
    (List.replicate a (1 : Nat) = List.replicate b 1) ↔ a = b := by
  constructor
  · intro h
    have := congrArg List.length h
    simpa using this
  · rintro rfl; rfl

private theorem replicate_one_snoc (n : Nat) :
    List.replicate n (1 : Nat) ++ [1] = List.replicate (n + 1) 1 :=
  List.replicate_succ'.symm

/-- Folding the parser over a unary block's interior just counts it. -/
private theorem mcStep_foldl_replicate (v : Nat) (f : Bool) :
    ∀ (n acc : Nat),
      (List.replicate n 1).foldl (mcStep v) (true, acc, f) = (true, acc + n, f)
  | 0, acc => by simp
  | n + 1, acc => by
      rw [List.replicate_succ, List.foldl_cons]
      show (List.replicate n 1).foldl (mcStep v) (true, acc + 1, f) = _
      rw [mcStep_foldl_replicate v f n (acc + 1)]
      have : acc + 1 + n = acc + (n + 1) := by omega
      rw [this]

/-- **The parser is correct**: folding `mcStep` over an encoded assignment from
a block boundary ORs `evalVar a v` into the found-flag and returns to a block
boundary. -/
private theorem mcStep_foldl_encodeAssgn (v : Nat) :
    ∀ (a : assgn) (acc : Nat) (f : Bool), ∃ accF,
      (encodeAssgn a).foldl (mcStep v) (false, acc, f)
        = (false, accF, f || evalVar a v)
  | [], acc, f => ⟨acc, by simp [encodeAssgn, evalVar]⟩
  | u :: a, acc, f => by
      have hsplit : encodeAssgn (u :: a)
          = 1 :: (List.replicate u 1 ++ ([0] ++ encodeAssgn a)) := by
        show (1 :: (List.replicate u 1 ++ [0])) ++ encodeAssgn a = _
        simp [List.append_assoc]
      rw [hsplit, List.foldl_cons]
      show ∃ accF, (List.replicate u 1 ++ ([0] ++ encodeAssgn a)).foldl
          (mcStep v) (true, 0, f) = _
      rw [List.foldl_append, mcStep_foldl_replicate v f u 0, List.foldl_append,
        List.foldl_cons, List.foldl_nil, Nat.zero_add]
      show ∃ accF, (encodeAssgn a).foldl (mcStep v)
          (false, u, f || decide (u = v)) = _
      obtain ⟨accF, hF⟩ := mcStep_foldl_encodeAssgn v a u (f || decide (u = v))
      refine ⟨accF, hF.trans ?_⟩
      have hor : ((f || decide (u = v)) || evalVar a v) = (f || evalVar (u :: a) v) := by
        simp only [evalVar, List.mem_cons]
        by_cases h1 : u = v
        · subst h1; simp
        · have h1' : ¬ (v = u) := fun h => h1 h.symm
          simp [h1, h1']
      rw [hor]

/-- One parser step matches one more consumed cell. -/
private theorem mcStep_take_succ (v : Nat) (L : List Nat) (i : Nat)
    (hi : i < L.length) :
    (L.take (i + 1)).foldl (mcStep v) (false, 0, false)
      = mcStep v ((L.take i).foldl (mcStep v) (false, 0, false)) L[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

/-- The parser accumulator (`BLOCK_ACC`) grows by at most one per consumed cell,
so after folding over a prefix it is bounded by that prefix's length. This is
the uniform bound on the data `mcBody`'s `eqBit` (cost `|BLOCK_ACC|+|LIT_VAR|+1`)
re-materialises each iteration. -/
private theorem mcStep_acc_le (v : Nat) :
    ∀ (L : List Nat) (b : Bool) (acc : Nat) (f : Bool),
      (L.foldl (mcStep v) (b, acc, f)).2.1 ≤ acc + L.length := by
  intro L
  induction L with
  | nil => intro b acc f; simp
  | cons c cs ih =>
      intro b acc f
      rw [List.foldl_cons]
      have hstep : ∃ b' acc' f', mcStep v (b, acc, f) c = (b', acc', f') ∧ acc' ≤ acc + 1 := by
        cases b <;> simp only [mcStep] <;> split <;>
          exact ⟨_, _, _, rfl, by omega⟩
      obtain ⟨b', acc', f', heq, hle⟩ := hstep
      rw [heq]
      refine (ih b' acc' f').trans ?_
      simp only [List.length_cons]; omega

private theorem mcSkip_eval (s : State) : mcSkip.eval s = s.set CMP_FLAG [1] := by
  show ((Cmd.op (.clear CMP_FLAG)) ;; Cmd.op (.appendOne CMP_FLAG)).eval s = _
  rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
  simp only [Op.eval, State.get_set_eq, List.nil_append, State.set_set]

private theorem mcSkip_cost (s : State) : mcSkip.cost s = 3 := by
  show ((Cmd.op (.clear CMP_FLAG)) ;; Cmd.op (.appendOne CMP_FLAG)).cost s = _
  rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]; rfl

/-- **One `mcBody` iteration = one `mcStep`** (plus its uniform cost bound and
frame). The single case-bash over the branch conditions; everything above it
is loop plumbing. -/
private theorem mcBody_step (st : State) (cell : Nat) (restL : List Nat)
    (inB : Bool) (acc : Nat) (found : Bool) (v : Nat)
    (hcopy : st.get ASSGN_COPY = cell :: restL)
    (hin : st.get IN_BLOCK = [if inB then 1 else 0])
    (hacc : st.get BLOCK_ACC = List.replicate acc 1)
    (hfound : st.get MEMBER_FOUND = [if found then 1 else 0])
    (hvar : st.get LIT_VAR = List.replicate v 1) :
    (mcBody.eval st).get ASSGN_COPY = restL
    ∧ (mcBody.eval st).get IN_BLOCK
        = [if (mcStep v (inB, acc, found) cell).1 then 1 else 0]
    ∧ (mcBody.eval st).get BLOCK_ACC
        = List.replicate (mcStep v (inB, acc, found) cell).2.1 1
    ∧ (mcBody.eval st).get MEMBER_FOUND
        = [if (mcStep v (inB, acc, found) cell).2.2 then 1 else 0]
    ∧ (∀ r : Var, r ∉ [ASSGN_COPY, MEMBER_FOUND, INNER_IDX, HEAD_CELL,
          CMP_FLAG, IN_BLOCK, BLOCK_ACC] → (mcBody.eval st).get r = st.get r)
    ∧ mcBody.cost st ≤ restL.length + acc + v + 20 := by
  -- shared prefix: head + tail
  have e1 : (Cmd.op (.head HEAD_CELL ASSGN_COPY)).eval st
      = st.set HEAD_CELL [cell] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hcopy]
  have e2 : (Cmd.op (.tail ASSGN_COPY ASSGN_COPY)).eval (st.set HEAD_CELL [cell])
      = (st.set HEAD_CELL [cell]).set ASSGN_COPY restL := by
    rw [Cmd.eval_op]; simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ (by decide), hcopy, List.tail_cons]
  -- gets at the branch point
  have hIB2 : ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).get IN_BLOCK
      = [if inB then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide)]; exact hin
  have hHC2 : ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).get HEAD_CELL
      = [cell] := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
  have hBA2 : ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).get BLOCK_ACC
      = List.replicate acc 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide)]; exact hacc
  have hLV2 : ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).get LIT_VAR
      = List.replicate v 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide)]; exact hvar
  have hMF2 : ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).get MEMBER_FOUND
      = [if found then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide)]; exact hfound
  have heval : mcBody.eval st
      = (Cmd.ifBit IN_BLOCK
          (Cmd.ifBit HEAD_CELL
            (Cmd.op (.appendOne BLOCK_ACC))
            (Cmd.op (.eqBit CMP_FLAG BLOCK_ACC LIT_VAR) ;;
             Cmd.ifBit CMP_FLAG
               (Cmd.op (.clear MEMBER_FOUND) ;; Cmd.op (.appendOne MEMBER_FOUND))
               mcSkip ;;
             Cmd.op (.clear IN_BLOCK) ;; Cmd.op (.appendZero IN_BLOCK)))
          (Cmd.ifBit HEAD_CELL
            (Cmd.op (.clear BLOCK_ACC) ;;
             Cmd.op (.clear IN_BLOCK) ;; Cmd.op (.appendOne IN_BLOCK))
            mcSkip)).eval ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL) := by
    show (Cmd.eval (_ ;; _ ;; _) st) = _
    rw [Cmd.eval_seq, Cmd.eval_seq, e1, e2]
  have hcost : mcBody.cost st
      = 1 + 1 + (1 + (restL.length + 2)
          + (Cmd.ifBit IN_BLOCK
              (Cmd.ifBit HEAD_CELL
                (Cmd.op (.appendOne BLOCK_ACC))
                (Cmd.op (.eqBit CMP_FLAG BLOCK_ACC LIT_VAR) ;;
                 Cmd.ifBit CMP_FLAG
                   (Cmd.op (.clear MEMBER_FOUND) ;; Cmd.op (.appendOne MEMBER_FOUND))
                   mcSkip ;;
                 Cmd.op (.clear IN_BLOCK) ;; Cmd.op (.appendZero IN_BLOCK)))
              (Cmd.ifBit HEAD_CELL
                (Cmd.op (.clear BLOCK_ACC) ;;
                 Cmd.op (.clear IN_BLOCK) ;; Cmd.op (.appendOne IN_BLOCK))
                mcSkip)).cost ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL)) := by
    show (Cmd.cost (_ ;; _ ;; _) st) = _
    rw [Cmd.cost_seq, Cmd.cost_seq, e1, Cmd.cost_op, Cmd.cost_op, e2]
    have htl : Op.cost (.tail ASSGN_COPY ASSGN_COPY) (st.set HEAD_CELL [cell])
        = restL.length + 2 := by
      show ((st.set HEAD_CELL [cell]).get ASSGN_COPY).length + 1 = _
      rw [State.get_set_ne _ _ _ _ (by decide), hcopy]
      simp
    rw [htl]
    show 1 + Op.cost (.head HEAD_CELL ASSGN_COPY) st + _ = _
    simp only [Op.cost]
  cases inB with
  | true =>
      -- in a block: a `1` extends the accumulator, a `0` closes the block
      have hIB2t : ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).get IN_BLOCK
          = [1] := by rw [hIB2]; rfl
      rw [Cmd.eval_ifBit_true _ _ _ _ hIB2t] at heval
      rw [Cmd.cost_ifBit_true _ _ _ _ hIB2t] at hcost
      by_cases hc : cell = 1
      · -- interior `1` cell
        subst hc
        rw [Cmd.eval_ifBit_true _ _ _ _ hHC2] at heval
        rw [Cmd.cost_ifBit_true _ _ _ _ hHC2] at hcost
        rw [Cmd.eval_op] at heval
        simp only [Op.eval] at heval
        rw [hBA2, replicate_one_snoc] at heval
        have hstep : mcStep v (true, acc, found) 1 = (true, acc + 1, found) := by
          simp [mcStep]
        rw [heval, hstep]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ (by decide), hIB2]
        · rw [State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ (by decide)]; exact hMF2
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
          rw [State.get_set_ne _ _ _ _ h7, State.get_set_ne _ _ _ _ h1,
            State.get_set_ne _ _ _ _ h4]
        · rw [hcost, Cmd.cost_op]
          simp only [Op.cost]
          omega
      · -- block-end `0` cell: compare and fold into MEMBER_FOUND
        have hHC2f : ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).get HEAD_CELL
            ≠ [1] := by rw [hHC2]; simp [hc]
        rw [Cmd.eval_ifBit_false _ _ _ _ hHC2f] at heval
        rw [Cmd.cost_ifBit_false _ _ _ _ hHC2f] at hcost
        rw [Cmd.eval_seq, Cmd.eval_op] at heval
        simp only [Op.eval] at heval
        rw [hBA2, hLV2] at heval
        have hifred : (if List.replicate acc 1 = List.replicate v 1
            then ([1] : List Nat) else [0]) = if acc = v then [1] else [0] := by
          by_cases hav : acc = v
          · rw [if_pos (replicate_one_eq_iff.mpr hav), if_pos hav]
          · rw [if_neg (fun h => hav (replicate_one_eq_iff.mp h)), if_neg hav]
        rw [hifred] at heval
        -- the cost chain, normalized to the same branch point
        rw [Cmd.cost_seq, Cmd.cost_op, Cmd.eval_op] at hcost
        simp only [Op.eval, Op.cost] at hcost
        rw [hBA2, hLV2, hifred] at hcost
        have hstep : mcStep v (true, acc, found) cell
            = (false, acc, found || decide (acc = v)) := by
          simp [mcStep, hc]
        rw [hstep]
        by_cases hav : acc = v
        · -- match: MEMBER_FOUND := [1]
          rw [if_pos hav] at heval hcost
          have hCMP : (((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).set CMP_FLAG
              [1]).get CMP_FLAG = [1] := State.get_set_eq _ _ _
          rw [Cmd.eval_seq, Cmd.eval_ifBit_true _ _ _ _ hCMP] at heval
          rw [Cmd.cost_seq, Cmd.cost_ifBit_true _ _ _ _ hCMP] at hcost
          rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op] at heval
          simp only [Op.eval] at heval
          rw [State.get_set_eq, List.nil_append] at heval
          rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op] at heval
          simp only [Op.eval] at heval
          rw [State.get_set_eq, List.nil_append] at heval
          rw [heval]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
          · rw [State.get_set_eq]; rfl
          · rw [State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide)]
            exact hBA2
          · rw [State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
            simp [hav]
          · intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
            obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
            rw [State.get_set_ne _ _ _ _ h6, State.get_set_ne _ _ _ _ h6,
              State.get_set_ne _ _ _ _ h2, State.get_set_ne _ _ _ _ h2,
              State.get_set_ne _ _ _ _ h5, State.get_set_ne _ _ _ _ h1,
              State.get_set_ne _ _ _ _ h4]
          · rw [hcost]
            simp only [Cmd.cost_seq, Cmd.cost_op, Op.cost, List.length_replicate]
            omega
        · -- no match: MEMBER_FOUND unchanged (mcSkip)
          rw [if_neg hav] at heval hcost
          have hCMPf : (((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).set CMP_FLAG
              [0]).get CMP_FLAG ≠ [1] := by rw [State.get_set_eq]; decide
          rw [Cmd.eval_seq, Cmd.eval_ifBit_false _ _ _ _ hCMPf] at heval
          rw [Cmd.cost_seq, Cmd.cost_ifBit_false _ _ _ _ hCMPf] at hcost
          rw [mcSkip_eval] at heval
          rw [mcSkip_cost] at hcost
          rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op] at heval
          simp only [Op.eval] at heval
          rw [State.get_set_eq, List.nil_append] at heval
          rw [heval]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
          · rw [State.get_set_eq]; rfl
          · rw [State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide)]
            exact hBA2
          · rw [State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide), hMF2]
            simp [hav]
          · intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
            obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
            rw [State.get_set_ne _ _ _ _ h6, State.get_set_ne _ _ _ _ h6,
              State.get_set_ne _ _ _ _ h5, State.get_set_ne _ _ _ _ h5,
              State.get_set_ne _ _ _ _ h1, State.get_set_ne _ _ _ _ h4]
          · rw [hcost]
            simp only [Cmd.cost_seq, Cmd.cost_op, Op.cost, List.length_replicate]
            omega
  | false =>
      -- at a boundary: a `1` opens a block, a `0` is inert
      have hIB2f : ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).get IN_BLOCK
          ≠ [1] := by rw [hIB2]; decide
      rw [Cmd.eval_ifBit_false _ _ _ _ hIB2f] at heval
      rw [Cmd.cost_ifBit_false _ _ _ _ hIB2f] at hcost
      by_cases hc : cell = 1
      · -- block-open sentinel
        subst hc
        rw [Cmd.eval_ifBit_true _ _ _ _ hHC2] at heval
        rw [Cmd.cost_ifBit_true _ _ _ _ hHC2] at hcost
        rw [Cmd.eval_seq, Cmd.eval_op] at heval
        simp only [Op.eval] at heval
        rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op] at heval
        simp only [Op.eval] at heval
        rw [State.get_set_eq, List.nil_append] at heval
        have hstep : mcStep v (false, acc, found) 1 = (true, 0, found) := by
          simp [mcStep]
        rw [heval, hstep]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
        · rw [State.get_set_eq]; rfl
        · rw [State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
          rfl
        · rw [State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide)]
          exact hMF2
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
          rw [State.get_set_ne _ _ _ _ h6, State.get_set_ne _ _ _ _ h6,
            State.get_set_ne _ _ _ _ h7, State.get_set_ne _ _ _ _ h1,
            State.get_set_ne _ _ _ _ h4]
        · rw [hcost]
          simp only [Cmd.cost_seq, Cmd.cost_op, Op.cost]
          omega
      · -- inert `0` cell
        have hHC2f : ((st.set HEAD_CELL [cell]).set ASSGN_COPY restL).get HEAD_CELL
            ≠ [1] := by rw [hHC2]; simp [hc]
        rw [Cmd.eval_ifBit_false _ _ _ _ hHC2f] at heval
        rw [Cmd.cost_ifBit_false _ _ _ _ hHC2f] at hcost
        rw [mcSkip_eval] at heval
        rw [mcSkip_cost] at hcost
        have hstep : mcStep v (false, acc, found) cell = (false, acc, found) := by
          simp [mcStep, hc]
        rw [heval, hstep]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ (by decide)]; exact hIB2
        · rw [State.get_set_ne _ _ _ _ (by decide)]; exact hBA2
        · rw [State.get_set_ne _ _ _ _ (by decide)]; exact hMF2
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
          rw [State.get_set_ne _ _ _ _ h5, State.get_set_ne _ _ _ _ h1,
            State.get_set_ne _ _ _ _ h4]
        · rw [hcost]
          omega

/-- The `memberCheck` scan-loop invariant: after `i` iterations the copy holds
the unconsumed suffix and the parser registers mirror `mcStep` folded over the
consumed prefix; everything outside the declared scratch is untouched. -/
private def MCInv (v : Nat) (a : assgn) (st : State) (i : Nat) (s : State) : Prop :=
  s.get ASSGN_COPY = (encodeAssgn a).drop i
  ∧ s.get IN_BLOCK
      = [if (((encodeAssgn a).take i).foldl (mcStep v) (false, 0, false)).1
          then 1 else 0]
  ∧ s.get BLOCK_ACC
      = List.replicate
          (((encodeAssgn a).take i).foldl (mcStep v) (false, 0, false)).2.1 1
  ∧ s.get MEMBER_FOUND
      = [if (((encodeAssgn a).take i).foldl (mcStep v) (false, 0, false)).2.2
          then 1 else 0]
  ∧ ∀ r : Var, r ∉ [ASSGN_COPY, MEMBER_FOUND, INNER_IDX, HEAD_CELL, CMP_FLAG,
        IN_BLOCK, BLOCK_ACC] → s.get r = st.get r

/-- The loop step: `MCInv` is preserved by one (counter-set + `mcBody`) round. -/
private theorem MCInv_step (v : Nat) (a : assgn) (st : State)
    (hvar : st.get LIT_VAR = List.replicate v 1)
    (i : Nat) (s : State) (hi : i < (encodeAssgn a).length) (h : MCInv v a st i s) :
    MCInv v a st (i + 1) (mcBody.eval (s.set INNER_IDX (List.replicate i 1))) := by
  obtain ⟨hAC, hIB, hBA, hMF, hframe⟩ := h
  -- the counter write is invisible to every register the step lemma reads
  have hAC' : (s.set INNER_IDX (List.replicate i 1)).get ASSGN_COPY
      = (encodeAssgn a)[i] :: (encodeAssgn a).drop (i + 1) := by
    rw [State.get_set_ne _ _ _ _ (by decide), hAC, List.drop_eq_getElem_cons hi]
  have hIB' : (s.set INNER_IDX (List.replicate i 1)).get IN_BLOCK
          = [if (((encodeAssgn a).take i).foldl (mcStep v) (false, 0, false)).1
          then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide)]; exact hIB
  have hBA' : (s.set INNER_IDX (List.replicate i 1)).get BLOCK_ACC
          = List.replicate
          (((encodeAssgn a).take i).foldl (mcStep v) (false, 0, false)).2.1 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide)]; exact hBA
  have hMF' : (s.set INNER_IDX (List.replicate i 1)).get MEMBER_FOUND
          = [if (((encodeAssgn a).take i).foldl (mcStep v) (false, 0, false)).2.2
          then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide)]; exact hMF
  have hLV' : (s.set INNER_IDX (List.replicate i 1)).get LIT_VAR
      = List.replicate v 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide), hframe LIT_VAR (by decide)]
    exact hvar
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := mcBody_step _ _ _ _ _ _ _ hAC' hIB' hBA' hMF' hLV'
  refine ⟨c1, ?_, ?_, ?_, ?_⟩
  · rw [c2, mcStep_take_succ v _ i hi]
  · rw [c3, mcStep_take_succ v _ i hi]
  · rw [c4, mcStep_take_succ v _ i hi]
  · intro r hr
    rw [c5 r hr, State.get_set_ne _ _ _ _ ?_, hframe r hr]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact hr.2.2.1

/-- Combined behaviour + cost for `memberCheck` (the two pinned lemmas are
projections of this). -/
private theorem memberCheck_main (st : State) (v : Nat) (a : assgn)
    (hvar : st.get LIT_VAR = List.replicate v 1)
    (hassgn : st.get ASSGN = encodeAssgn a) :
    ((memberCheck.eval st).get MEMBER_FOUND = [if evalVar a v then 1 else 0])
    ∧ (∀ r : Var,
        r ∉ [ASSGN_COPY, MEMBER_FOUND, INNER_IDX, HEAD_CELL, CMP_FLAG,
             IN_BLOCK, BLOCK_ACC] →
        (memberCheck.eval st).get r = st.get r)
    ∧ memberCheck.cost st
        ≤ 100 * ((st.get ASSGN).length + (st.get LIT_VAR).length + 1) ^ 2 := by
  -- the state after the init prefix, written out
  have eP : memberCheck.eval st
      = (Cmd.forBnd INNER_IDX ASSGN_COPY mcBody).eval
          ((((((st.set ASSGN_COPY (encodeAssgn a)).set MEMBER_FOUND []).set
            MEMBER_FOUND [0]).set IN_BLOCK []).set IN_BLOCK [0]).set BLOCK_ACC []) := by
    show (Cmd.eval (_ ;; _ ;; _ ;; _ ;; _ ;; _ ;; _) st) = _
    simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
      List.nil_append, hassgn]
  have hbound :
      ((((((st.set ASSGN_COPY (encodeAssgn a)).set MEMBER_FOUND []).set
        MEMBER_FOUND [0]).set IN_BLOCK []).set IN_BLOCK [0]).set BLOCK_ACC []).get
        ASSGN_COPY = encodeAssgn a := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
  have hbase : MCInv v a st 0
      ((((((st.set ASSGN_COPY (encodeAssgn a)).set MEMBER_FOUND []).set
        MEMBER_FOUND [0]).set IN_BLOCK []).set IN_BLOCK [0]).set BLOCK_ACC []) := by
    refine ⟨by rw [hbound]; rfl, ?_, ?_, ?_, ?_⟩
    · show _ = [(0 : Nat)]
      rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
    · show _ = List.replicate 0 1
      rw [State.get_set_eq]
      rfl
    · show _ = [(0 : Nat)]
      rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
      rw [State.get_set_ne _ _ _ _ h7, State.get_set_ne _ _ _ _ h6,
        State.get_set_ne _ _ _ _ h6, State.get_set_ne _ _ _ _ h2,
        State.get_set_ne _ _ _ _ h2, State.get_set_ne _ _ _ _ h1]
  have hInv : MCInv v a st (encodeAssgn a).length (memberCheck.eval st) := by
    rw [eP, Cmd.eval_forBnd, hbound]
    exact Cmd.foldlState_range_induct mcBody INNER_IDX (encodeAssgn a).length _
      (MCInv v a st) hbase (fun i s hi h => MCInv_step v a st hvar i s hi h)
  obtain ⟨_, _, _, hMF, hframe⟩ := hInv
  obtain ⟨accF, hspec⟩ := mcStep_foldl_encodeAssgn v a 0 false
  refine ⟨?_, hframe, ?_⟩
  · rw [List.take_length] at hMF
    rw [hMF, hspec]
    simp
  · -- cost: prefix + uniform-bound loop
    have hcost_eq : memberCheck.cost st
        = (st.get ASSGN).length + 12
          + (Cmd.forBnd INNER_IDX ASSGN_COPY mcBody).cost
              ((((((st.set ASSGN_COPY (encodeAssgn a)).set MEMBER_FOUND []).set
                MEMBER_FOUND [0]).set IN_BLOCK []).set IN_BLOCK [0]).set
                BLOCK_ACC []) := by
      show (Cmd.cost (_ ;; _ ;; _ ;; _ ;; _ ;; _ ;; _) st) = _
      simp only [Cmd.cost_seq, Cmd.cost_op, Cmd.eval_seq, Cmd.eval_op, Op.eval,
        Op.cost, State.get_set_eq, List.nil_append, hassgn]
      omega
    have hC : ∀ i s, i < (encodeAssgn a).length → MCInv v a st i s →
        mcBody.cost (s.set INNER_IDX (List.replicate i 1))
          ≤ 2 * (encodeAssgn a).length + v + 20 := by
      intro i s hi h
      obtain ⟨hAC, hIB, hBA, hMF, hframe⟩ := h
      have hAC' : (s.set INNER_IDX (List.replicate i 1)).get ASSGN_COPY
          = (encodeAssgn a)[i] :: (encodeAssgn a).drop (i + 1) := by
        rw [State.get_set_ne _ _ _ _ (by decide), hAC,
          List.drop_eq_getElem_cons hi]
      have hIB' : (s.set INNER_IDX (List.replicate i 1)).get IN_BLOCK
          = [if (((encodeAssgn a).take i).foldl (mcStep v) (false, 0, false)).1
              then 1 else 0] := by
        rw [State.get_set_ne _ _ _ _ (by decide)]; exact hIB
      have hBA' : (s.set INNER_IDX (List.replicate i 1)).get BLOCK_ACC
          = List.replicate
              (((encodeAssgn a).take i).foldl (mcStep v) (false, 0, false)).2.1 1 := by
        rw [State.get_set_ne _ _ _ _ (by decide)]; exact hBA
      have hMF' : (s.set INNER_IDX (List.replicate i 1)).get MEMBER_FOUND
          = [if (((encodeAssgn a).take i).foldl (mcStep v) (false, 0, false)).2.2
              then 1 else 0] := by
        rw [State.get_set_ne _ _ _ _ (by decide)]; exact hMF
      have hLV' : (s.set INNER_IDX (List.replicate i 1)).get LIT_VAR
          = List.replicate v 1 := by
        rw [State.get_set_ne _ _ _ _ (by decide), hframe LIT_VAR (by decide)]
        exact hvar
      obtain ⟨_, _, _, _, _, hc⟩ :=
        mcBody_step _ _ _ _ _ _ _ hAC' hIB' hBA' hMF' hLV'
      refine hc.trans ?_
      have hdrop : (List.drop (i + 1) (encodeAssgn a)).length
          = (encodeAssgn a).length - (i + 1) := List.length_drop
      have hacc : (((encodeAssgn a).take i).foldl (mcStep v) (false, 0, false)).2.1
          ≤ (encodeAssgn a).length := by
        refine (mcStep_acc_le v ((encodeAssgn a).take i) false 0 false).trans ?_
        simp only [Nat.zero_add, List.length_take]; omega
      omega
    have hloop : (Cmd.forBnd INNER_IDX ASSGN_COPY mcBody).cost
        ((((((st.set ASSGN_COPY (encodeAssgn a)).set MEMBER_FOUND []).set
          MEMBER_FOUND [0]).set IN_BLOCK []).set IN_BLOCK [0]).set BLOCK_ACC [])
        ≤ 1 + (encodeAssgn a).length * (2 * (encodeAssgn a).length + v + 20)
          + (encodeAssgn a).length * (encodeAssgn a).length := by
      have h := Cmd.cost_forBnd_le INNER_IDX ASSGN_COPY mcBody
        ((((((st.set ASSGN_COPY (encodeAssgn a)).set MEMBER_FOUND []).set
          MEMBER_FOUND [0]).set IN_BLOCK []).set IN_BLOCK [0]).set BLOCK_ACC [])
        (2 * (encodeAssgn a).length + v + 20) (MCInv v a st) hbase
        (fun i s hi h => MCInv_step v a st hvar i s (by rwa [hbound] at hi) h)
        (fun i s hi h => hC i s (by rwa [hbound] at hi) h)
      rwa [hbound] at h
    -- assemble the arithmetic: 3n² + nv + 21n + 13 ≤ 100(n + v + 1)²
    rw [hcost_eq, hassgn, hvar]
    have hn := hloop
    set n := (encodeAssgn a).length with hndef
    rw [List.length_replicate]
    have he1 : n * (2 * n + v + 20) = 2 * (n * n) + n * v + 20 * n := by ring
    have he2 : (n + v + 1) ^ 2
        = n * n + v * v + 1 + 2 * (n * v) + 2 * n + 2 * v := by ring
    omega

/-! ## Pinned inner-body contracts — the bottom-up ⇄ top-down interface

**(Pinned 2026-06-09 top-down; DISCHARGED 2026-06-10 bottom-up.)** The
assembly below (`evalCnfCmd_decides`, `evalCnfCmd_cost_bound`,
`evalCnfCmd_usesBelow`, `evalCnfCmd_noConsLen` — all four `evalCnfDecidesLang`
obligations) is proven from the `processOneClause_*` quartet alone; the
`processOneLiteral_*` / `memberCheck_*` quartets are the (now proven)
decomposition.

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
  obtain ⟨h1, h2, _⟩ := memberCheck_main st v a hvar hassgn
  exact ⟨h1, h2⟩

/-- **(pinned, bottom-up) `memberCheck` cost** — quadratic in the entry
lengths of the registers it reads (uniform-bound accounting: one pass over
`ASSGN_COPY` at `O(len)` worst-case slot cost, plus the `forBnd` counter
charge). -/
theorem memberCheck_cost (st : State) (v : Nat) (a : assgn)
    (hvar : st.get LIT_VAR = List.replicate v 1)
    (hassgn : st.get ASSGN = encodeAssgn a) :
    memberCheck.cost st
      ≤ 100 * ((st.get ASSGN).length + (st.get LIT_VAR).length + 1) ^ 2 :=
  (memberCheck_main st v a hvar hassgn).2.2

theorem memberCheck_usesBelow : Cmd.UsesBelow memberCheck 16 := by
  simp only [memberCheck, mcBody, mcSkip, Cmd.UsesBelow, Op.UsesBelow]
  decide

theorem memberCheck_noConsLen : Cmd.NoConsLen memberCheck := by
  simp only [memberCheck, mcBody, mcSkip, Cmd.NoConsLen, Op.NotConsLen]
  trivial

/-! ### `processOneLiteral`: the unary-variable extraction loop -/

/-- The var-extraction loop invariant: through iteration `v` the loop is
consuming the unary block (one cell per iteration) into `LIT_VAR`; at
iteration `v` it consumes the `0` terminator and clears `IN_BLOCK`; afterwards
it idles. `st` is the loop-entry state (frame reference). -/
private def LVInv (v : Nat) (rest : List Nat) (st : State) (i : Nat) (s : State) :
    Prop :=
  (if i ≤ v then
    s.get IN_BLOCK = [1] ∧ s.get LIT_VAR = List.replicate i 1
      ∧ s.get CNF_STREAM = List.replicate (v - i) 1 ++ 0 :: rest
  else
    s.get IN_BLOCK = [] ∧ s.get LIT_VAR = List.replicate v 1
      ∧ s.get CNF_STREAM = rest)
  ∧ ∀ r : Var, r ∉ [CNF_STREAM, LIT_VAR, IN_BLOCK, HEAD_CELL, CMP_FLAG,
      INNER_IDX] → s.get r = st.get r

private theorem LVInv_step (v : Nat) (rest : List Nat) (st : State)
    (i : Nat) (s : State) (h : LVInv v rest st i s) :
    LVInv v rest st (i + 1)
      (varExtractBody.eval (s.set INNER_IDX (List.replicate i 1))) := by
  obtain ⟨hphase, hframe⟩ := h
  by_cases hiv : i ≤ v
  · rw [if_pos hiv] at hphase
    obtain ⟨hIB, hLV, hCS⟩ := hphase
    have hIB' : (s.set INNER_IDX (List.replicate i 1)).get IN_BLOCK = [1] := by
      rw [State.get_set_ne _ _ _ _ (by decide)]; exact hIB
    have hCS' : (s.set INNER_IDX (List.replicate i 1)).get CNF_STREAM
        = List.replicate (v - i) 1 ++ 0 :: rest := by
      rw [State.get_set_ne _ _ _ _ (by decide)]; exact hCS
    have hLV' : (s.set INNER_IDX (List.replicate i 1)).get LIT_VAR
        = List.replicate i 1 := by
      rw [State.get_set_ne _ _ _ _ (by decide)]; exact hLV
    have heval : varExtractBody.eval (s.set INNER_IDX (List.replicate i 1))
        = (Cmd.op (.head HEAD_CELL CNF_STREAM) ;;
           Cmd.op (.tail CNF_STREAM CNF_STREAM) ;;
           Cmd.ifBit HEAD_CELL (Cmd.op (.appendOne LIT_VAR))
             (Cmd.op (.clear IN_BLOCK))).eval
            (s.set INNER_IDX (List.replicate i 1)) := by
      show (Cmd.ifBit IN_BLOCK _ _).eval _ = _
      rw [Cmd.eval_ifBit_true _ _ _ _ hIB']
    by_cases hiv2 : i < v
    · -- interior `1` cell of the unary block
      have hsplit : List.replicate (v - i) (1 : Nat) ++ 0 :: rest
          = 1 :: (List.replicate (v - (i + 1)) 1 ++ 0 :: rest) := by
        have hvi : v - i = (v - (i + 1)) + 1 := by omega
        rw [hvi, List.replicate_succ, List.cons_append]
      rw [hsplit] at hCS'
      have e1 : (Cmd.op (.head HEAD_CELL CNF_STREAM)).eval
          (s.set INNER_IDX (List.replicate i 1))
          = (s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hCS']
      have e2 : (Cmd.op (.tail CNF_STREAM CNF_STREAM)).eval
          ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1])
          = ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).set
              CNF_STREAM (List.replicate (v - (i + 1)) 1 ++ 0 :: rest) := by
        rw [Cmd.eval_op]; simp only [Op.eval]
        rw [State.get_set_ne _ _ _ _ (by decide), hCS', List.tail_cons]
      have hHC : (((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).set
          CNF_STREAM (List.replicate (v - (i + 1)) 1 ++ 0 :: rest)).get HEAD_CELL
          = [1] := by
        rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_ifBit_true _ _ _ _ hHC,
        Cmd.eval_op] at heval
      simp only [Op.eval] at heval
      rw [State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide), hLV, replicate_one_snoc] at heval
      rw [heval]
      constructor
      · rw [if_pos (by omega : i + 1 ≤ v)]
        refine ⟨?_, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide)]
          exact hIB
        · rw [State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
        rw [State.get_set_ne _ _ _ _ h2, State.get_set_ne _ _ _ _ h1,
          State.get_set_ne _ _ _ _ h4, State.get_set_ne _ _ _ _ h6]
        exact hframe r (by simp [h1, h2, h3, h4, h5, h6])
    · -- the `0` terminator (i = v)
      have hiv3 : i = v := by omega
      subst hiv3
      have hsplit : List.replicate (i - i) (1 : Nat) ++ 0 :: rest
          = 0 :: rest := by
        rw [Nat.sub_self]; rfl
      rw [hsplit] at hCS'
      have e1 : (Cmd.op (.head HEAD_CELL CNF_STREAM)).eval
          (s.set INNER_IDX (List.replicate i 1))
          = (s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [0] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hCS']
      have e2 : (Cmd.op (.tail CNF_STREAM CNF_STREAM)).eval
          ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [0])
          = ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [0]).set
              CNF_STREAM rest := by
        rw [Cmd.eval_op]; simp only [Op.eval]
        rw [State.get_set_ne _ _ _ _ (by decide), hCS', List.tail_cons]
      have hHC : (((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [0]).set
          CNF_STREAM rest).get HEAD_CELL ≠ [1] := by
        rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]; decide
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_ifBit_false _ _ _ _ hHC,
        Cmd.eval_op] at heval
      simp only [Op.eval] at heval
      rw [heval]
      constructor
      · rw [if_neg (by omega : ¬ i + 1 ≤ i)]
        refine ⟨?_, ?_, ?_⟩
        · rw [State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide)]
          exact hLV
        · rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
        rw [State.get_set_ne _ _ _ _ h3, State.get_set_ne _ _ _ _ h1,
          State.get_set_ne _ _ _ _ h4, State.get_set_ne _ _ _ _ h6]
        exact hframe r (by simp [h1, h2, h3, h4, h5, h6])
  · -- idle phase
    rw [if_neg hiv] at hphase
    obtain ⟨hIB, hLV, hCS⟩ := hphase
    have hIB' : (s.set INNER_IDX (List.replicate i 1)).get IN_BLOCK ≠ [1] := by
      rw [State.get_set_ne _ _ _ _ (by decide), hIB]; decide
    have heval : varExtractBody.eval (s.set INNER_IDX (List.replicate i 1))
        = ((s.set INNER_IDX (List.replicate i 1)).set CMP_FLAG [1]) := by
      show (Cmd.ifBit IN_BLOCK _ _).eval _ = _
      rw [Cmd.eval_ifBit_false _ _ _ _ hIB', mcSkip_eval]
    rw [heval]
    constructor
    · rw [if_neg (by omega : ¬ i + 1 ≤ v)]
      refine ⟨?_, ?_, ?_⟩
      · rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hIB
      · rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hLV
      · rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hCS
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
      rw [State.get_set_ne _ _ _ _ h5, State.get_set_ne _ _ _ _ h6]
      exact hframe r (by simp [h1, h2, h3, h4, h5, h6])

/-- Uniform per-iteration cost of the var-extraction body. -/
private theorem LVInv_cost (v : Nat) (rest : List Nat) (st : State)
    (i : Nat) (s : State) (h : LVInv v rest st i s) :
    varExtractBody.cost (s.set INNER_IDX (List.replicate i 1))
      ≤ (v + 1 + rest.length) + 10 := by
  obtain ⟨hphase, hframe⟩ := h
  have hif : ∀ t : State, (Cmd.ifBit HEAD_CELL (Cmd.op (.appendOne LIT_VAR))
      (Cmd.op (.clear IN_BLOCK))).cost t ≤ 2 := by
    intro t
    by_cases hb : t.get HEAD_CELL = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ hb, Cmd.cost_op]; simp [Op.cost]
    · rw [Cmd.cost_ifBit_false _ _ _ _ hb, Cmd.cost_op]; simp [Op.cost]
  by_cases hiv : i ≤ v
  · rw [if_pos hiv] at hphase
    obtain ⟨hIB, hLV, hCS⟩ := hphase
    have hIB' : (s.set INNER_IDX (List.replicate i 1)).get IN_BLOCK = [1] := by
      rw [State.get_set_ne _ _ _ _ (by decide)]; exact hIB
    have hCS' : (s.set INNER_IDX (List.replicate i 1)).get CNF_STREAM
        = List.replicate (v - i) 1 ++ 0 :: rest := by
      rw [State.get_set_ne _ _ _ _ (by decide)]; exact hCS
    obtain ⟨c, tl, hct, htl⟩ : ∃ c tl,
        (s.set INNER_IDX (List.replicate i 1)).get CNF_STREAM = c :: tl
        ∧ tl.length = (v - i) + rest.length := by
      rw [hCS']
      cases hvi : v - i with
      | zero => exact ⟨0, rest, rfl, by omega⟩
      | succ k =>
          refine ⟨1, List.replicate k 1 ++ 0 :: rest, by
            rw [List.replicate_succ, List.cons_append], by
            simp only [List.length_append, List.length_replicate,
              List.length_cons]
            omega⟩
    have e1 : (Cmd.op (.head HEAD_CELL CNF_STREAM)).eval
        (s.set INNER_IDX (List.replicate i 1))
        = (s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [c] := by
      rw [Cmd.eval_op]; simp only [Op.eval]; rw [hct]
    have hc1 : varExtractBody.cost (s.set INNER_IDX (List.replicate i 1))
        = 1 + (Cmd.op (.head HEAD_CELL CNF_STREAM) ;;
            Cmd.op (.tail CNF_STREAM CNF_STREAM) ;;
            Cmd.ifBit HEAD_CELL (Cmd.op (.appendOne LIT_VAR))
              (Cmd.op (.clear IN_BLOCK))).cost
            (s.set INNER_IDX (List.replicate i 1)) := by
      show (Cmd.ifBit IN_BLOCK _ _).cost _ = _
      rw [Cmd.cost_ifBit_true _ _ _ _ hIB']
    have htlcost : Op.cost (.tail CNF_STREAM CNF_STREAM)
        ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [c])
        = tl.length + 2 := by
      show (((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [c]).get
        CNF_STREAM).length + 1 = _
      rw [State.get_set_ne _ _ _ _ (by decide), hct]
      simp
    have hc2 : (Cmd.op (.head HEAD_CELL CNF_STREAM) ;;
        Cmd.op (.tail CNF_STREAM CNF_STREAM) ;;
        Cmd.ifBit HEAD_CELL (Cmd.op (.appendOne LIT_VAR))
          (Cmd.op (.clear IN_BLOCK))).cost
        (s.set INNER_IDX (List.replicate i 1))
        = 1 + 1 + (1 + (tl.length + 2)
            + (Cmd.ifBit HEAD_CELL (Cmd.op (.appendOne LIT_VAR))
                (Cmd.op (.clear IN_BLOCK))).cost
                ((Cmd.op (.tail CNF_STREAM CNF_STREAM)).eval
                  ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [c]))) := by
      rw [Cmd.cost_seq, e1, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op, htlcost]
      simp only [Op.cost]
    have := hif ((Cmd.op (.tail CNF_STREAM CNF_STREAM)).eval
      ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [c]))
    rw [hc1, hc2]
    omega
  · rw [if_neg hiv] at hphase
    have hIB' : (s.set INNER_IDX (List.replicate i 1)).get IN_BLOCK ≠ [1] := by
      rw [State.get_set_ne _ _ _ _ (by decide), hphase.1]; decide
    have hcost : varExtractBody.cost (s.set INNER_IDX (List.replicate i 1))
        = 1 + 3 := by
      show (Cmd.ifBit IN_BLOCK _ _).cost _ = _
      rw [Cmd.cost_ifBit_false _ _ _ _ hIB', mcSkip_cost]
    omega

/-- Combined behaviour + cost for `processOneLiteral`, at explicit `(pol, v)`
and a pre-normalized stream shape. -/
private theorem processOneLiteral_main (st : State) (pol : Bool) (v : Nat)
    (rest : List Nat) (a : assgn) (cs : Bool)
    (hstream : st.get CNF_STREAM
      = 1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))
    (hassgn : st.get ASSGN = encodeAssgn a)
    (hsat : st.get CLAUSE_SAT = [if cs then 1 else 0]) :
    ((processOneLiteral.eval st).get CLAUSE_SAT
        = [if cs || evalLiteral a (pol, v) then 1 else 0])
    ∧ ((processOneLiteral.eval st).get CNF_STREAM = rest)
    ∧ (∀ r : Var,
        r ∉ [CNF_STREAM, CLAUSE_SAT, LIT_POL, LIT_VAR, ASSGN_COPY,
             MEMBER_FOUND, INNER_IDX, HEAD_CELL, CMP_FLAG, IN_BLOCK,
             BLOCK_ACC] →
        (processOneLiteral.eval st).get r = st.get r)
    ∧ processOneLiteral.cost st
        ≤ 300 * ((st.get CNF_STREAM).length + (st.get ASSGN).length + 1) ^ 2 := by
  -- prefix evaluation, op by op
  have e1 : (Cmd.op (.tail CNF_STREAM CNF_STREAM)).eval st = st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest)) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hstream, List.tail_cons]
  have e2 : (Cmd.op (.head LIT_POL CNF_STREAM)).eval (st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))) = (st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [State.get_set_eq]
  have hgetB : ((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).get CNF_STREAM
      = (if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest) := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
  have e3 : (Cmd.op (.tail CNF_STREAM CNF_STREAM)).eval ((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]) = ((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hgetB, List.tail_cons]
  have e4 : (Cmd.op (.clear LIT_VAR)).eval (((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)) = (((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e5 : (Cmd.op (.clear IN_BLOCK)).eval ((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []) = ((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e6 : (Cmd.op (.appendOne IN_BLOCK)).eval (((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []) = (((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [State.get_set_eq, List.nil_append]
  have eP : processOneLiteral.eval st
      = (Cmd.forBnd INNER_IDX CNF_STREAM varExtractBody ;; memberCheck ;;
       Cmd.op (.eqBit CMP_FLAG MEMBER_FOUND LIT_POL) ;;
       Cmd.ifBit CMP_FLAG
         (Cmd.op (.clear CLAUSE_SAT) ;; Cmd.op (.appendOne CLAUSE_SAT)) mcSkip).eval ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]) := by
    show (Cmd.eval (_ ;; _ ;; _ ;; _ ;; _ ;; _ ;; _) st) = _
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3, Cmd.eval_seq, e4,
      Cmd.eval_seq, e5, Cmd.eval_seq, e6]
  have hcost_eq : processOneLiteral.cost st
      = 2 * v + 2 * rest.length + 17 + (Cmd.forBnd INNER_IDX CNF_STREAM varExtractBody ;; memberCheck ;;
       Cmd.op (.eqBit CMP_FLAG MEMBER_FOUND LIT_POL) ;;
       Cmd.ifBit CMP_FLAG
         (Cmd.op (.clear CLAUSE_SAT) ;; Cmd.op (.appendOne CLAUSE_SAT)) mcSkip).cost ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]) := by
    show (Cmd.cost (_ ;; _ ;; _ ;; _ ;; _ ;; _ ;; _) st) = _
    rw [Cmd.cost_seq, e1, Cmd.cost_seq, e2, Cmd.cost_seq, e3, Cmd.cost_seq, e4,
      Cmd.cost_seq, e5, Cmd.cost_seq, e6, Cmd.cost_op, Cmd.cost_op, Cmd.cost_op,
      Cmd.cost_op, Cmd.cost_op, Cmd.cost_op]
    simp only [Op.cost]
    rw [hstream, hgetB]
    simp only [List.length_cons, List.length_append, List.length_replicate]
    omega
  -- the post-prefix register picture
  have hCSF : ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]).get CNF_STREAM = List.replicate v 1 ++ 0 :: rest := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
  have hIBF : ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]).get IN_BLOCK = [1] := State.get_set_eq _ _ _
  have hLVF : ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]).get LIT_VAR = List.replicate 0 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
      State.get_set_eq]
    rfl
  have hLPF : ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]).get LIT_POL = [(if pol then 1 else 0)] := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
      State.get_set_eq]
  have hframeF : ∀ r : Var, r ∉ [CNF_STREAM, LIT_POL, LIT_VAR, IN_BLOCK] →
      ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]).get r = st.get r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [State.get_set_ne _ _ _ _ h4, State.get_set_ne _ _ _ _ h4,
      State.get_set_ne _ _ _ _ h3, State.get_set_ne _ _ _ _ h1,
      State.get_set_ne _ _ _ _ h2, State.get_set_ne _ _ _ _ h1]
  have hnlen : (((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]).get CNF_STREAM).length = v + 1 + rest.length := by
    rw [hCSF]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  -- the var-extraction loop
  have base : LVInv v rest ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]) 0 ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]) := by
    constructor
    · rw [if_pos (Nat.zero_le v)]
      refine ⟨hIBF, hLVF, ?_⟩
      rw [Nat.sub_zero]
      exact hCSF
    · intro r _; rfl
  have hfin := Cmd.foldlState_range_induct varExtractBody INNER_IDX
    (((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]).get CNF_STREAM).length ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]) (LVInv v rest ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1])) base
    (fun i s _ h => LVInv_step v rest ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]) i s h)
  rw [hnlen] at hfin
  rw [Cmd.eval_seq, Cmd.eval_forBnd, hnlen] at eP
  obtain ⟨hphase7, hframe7⟩ := hfin
  rw [if_neg (by omega : ¬ (v + 1 + rest.length ≤ v))] at hphase7
  obtain ⟨hIB7, hLV7, hCS7⟩ := hphase7
  have hassgn7 : (Cmd.foldlState varExtractBody INNER_IDX (List.range (v + 1 + rest.length)) ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1])).get ASSGN = encodeAssgn a := by
    rw [hframe7 ASSGN (by decide), hframeF ASSGN (by decide)]
    exact hassgn
  obtain ⟨hMF8, hframe8, hcostMC⟩ := memberCheck_main (Cmd.foldlState varExtractBody INNER_IDX (List.range (v + 1 + rest.length)) ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1])) v a hLV7 hassgn7
  rw [Cmd.eval_seq] at eP
  have hCS8 : (memberCheck.eval (Cmd.foldlState varExtractBody INNER_IDX (List.range (v + 1 + rest.length)) ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]))).get CNF_STREAM = rest :=
    (hframe8 CNF_STREAM (by decide)).trans hCS7
  have hLP8 : (memberCheck.eval (Cmd.foldlState varExtractBody INNER_IDX (List.range (v + 1 + rest.length)) ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]))).get LIT_POL = [(if pol then 1 else 0)] :=
    (hframe8 LIT_POL (by decide)).trans
      ((hframe7 LIT_POL (by decide)).trans hLPF)
  have hCSAT8 : (memberCheck.eval (Cmd.foldlState varExtractBody INNER_IDX (List.range (v + 1 + rest.length)) ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]))).get CLAUSE_SAT = [if cs then 1 else 0] :=
    (hframe8 CLAUSE_SAT (by decide)).trans
      ((hframe7 CLAUSE_SAT (by decide)).trans
        ((hframeF CLAUSE_SAT (by decide)).trans hsat))
  have hsat_red : (if ([if evalVar a v then 1 else 0] : List Nat)
      = [(if pol then 1 else 0)] then ([1] : List Nat) else [0])
      = if evalLiteral a (pol, v) then [1] else [0] := by
    cases hev : evalVar a v <;> cases pol <;> simp [evalLiteral, hev]
  rw [Cmd.eval_seq, Cmd.eval_op] at eP
  simp only [Op.eval] at eP
  rw [hMF8, hLP8, hsat_red] at eP
  have hrun : ((processOneLiteral.eval st).get CLAUSE_SAT
        = [if cs || evalLiteral a (pol, v) then 1 else 0])
      ∧ ((processOneLiteral.eval st).get CNF_STREAM = rest)
      ∧ (∀ r : Var,
          r ∉ [CNF_STREAM, CLAUSE_SAT, LIT_POL, LIT_VAR, ASSGN_COPY,
               MEMBER_FOUND, INNER_IDX, HEAD_CELL, CMP_FLAG, IN_BLOCK,
               BLOCK_ACC] →
          (processOneLiteral.eval st).get r = st.get r) := by
    cases hlit : evalLiteral a (pol, v) with
    | true =>
        rw [hlit] at eP
        rw [if_pos rfl] at eP
        have hCMP9 : ((memberCheck.eval (Cmd.foldlState varExtractBody INNER_IDX (List.range (v + 1 + rest.length)) ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]))).set CMP_FLAG [1]).get CMP_FLAG = [1] :=
          State.get_set_eq _ _ _
        rw [Cmd.eval_ifBit_true _ _ _ _ hCMP9, Cmd.eval_seq, Cmd.eval_op,
          Cmd.eval_op] at eP
        simp only [Op.eval] at eP
        rw [State.get_set_eq, List.nil_append] at eP
        rw [eP]
        refine ⟨?_, ?_, ?_⟩
        · rw [State.get_set_eq]
          simp
        · rw [State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide)]
          exact hCS8
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hr
          rw [State.get_set_ne _ _ _ _ h2, State.get_set_ne _ _ _ _ h2,
            State.get_set_ne _ _ _ _ h9,
            hframe8 r (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨h5, h6, h7, h8, h9, h10, h11⟩),
            hframe7 r (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨h1, h4, h10, h8, h9, h7⟩),
            hframeF r (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨h1, h3, h4, h10⟩)]
    | false =>
        rw [hlit] at eP
        rw [if_neg (by decide : ¬ ((false : Bool) = true))] at eP
        have hCMP9 : ((memberCheck.eval (Cmd.foldlState varExtractBody INNER_IDX (List.range (v + 1 + rest.length)) ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]))).set CMP_FLAG [0]).get CMP_FLAG ≠ [1] := by
          rw [State.get_set_eq]; decide
        rw [Cmd.eval_ifBit_false _ _ _ _ hCMP9, mcSkip_eval] at eP
        rw [eP]
        refine ⟨?_, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide), hCSAT8, Bool.or_false]
        · rw [State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide)]
          exact hCS8
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hr
          rw [State.get_set_ne _ _ _ _ h9, State.get_set_ne _ _ _ _ h9,
            hframe8 r (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨h5, h6, h7, h8, h9, h10, h11⟩),
            hframe7 r (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨h1, h4, h10, h8, h9, h7⟩),
            hframeF r (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨h1, h3, h4, h10⟩)]
  refine ⟨hrun.1, hrun.2.1, hrun.2.2, ?_⟩
  -- the cost side
  have hForCost : (Cmd.forBnd INNER_IDX CNF_STREAM varExtractBody).cost ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1])
      ≤ 1 + (v + 1 + rest.length) * ((v + 1 + rest.length) + 10)
        + (v + 1 + rest.length) * (v + 1 + rest.length) := by
    have h := Cmd.cost_forBnd_le INNER_IDX CNF_STREAM varExtractBody ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1])
      ((v + 1 + rest.length) + 10) (LVInv v rest ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1])) base
      (fun i s _ h => LVInv_step v rest ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]) i s h)
      (fun i s _ h => LVInv_cost v rest ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]) i s h)
    rwa [hnlen] at h
  rw [hassgn7, hLV7, List.length_replicate] at hcostMC
  have hIfCost : ∀ t : State, (Cmd.ifBit CMP_FLAG
      (Cmd.op (.clear CLAUSE_SAT) ;; Cmd.op (.appendOne CLAUSE_SAT))
      mcSkip).cost t ≤ 4 := by
    intro t
    by_cases hb : t.get CMP_FLAG = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ hb, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
      simp only [Op.cost]
      omega
    · rw [Cmd.cost_ifBit_false _ _ _ _ hb, mcSkip_cost]
  have hLst : (st.get CNF_STREAM).length = v + rest.length + 3 := by
    rw [hstream]
    simp only [List.length_cons, List.length_append, List.length_replicate]
    omega
  have hAst : (st.get ASSGN).length = (encodeAssgn a).length := by rw [hassgn]
  rw [hcost_eq, hLst, hAst]
  rw [Cmd.cost_seq, Cmd.eval_forBnd, hnlen, Cmd.cost_seq, Cmd.cost_seq,
    Cmd.cost_op]
  simp only [Op.cost]
  -- the `eqBit MEMBER_FOUND LIT_POL` reads two 1-cell flags (cost `1+1+1`)
  rw [hMF8, hLP8]
  simp only [List.length_cons, List.length_nil]
  have hif := hIfCost ((Cmd.op (.eqBit CMP_FLAG MEMBER_FOUND LIT_POL)).eval
    (memberCheck.eval (Cmd.foldlState varExtractBody INNER_IDX (List.range (v + 1 + rest.length)) ((((((st.set CNF_STREAM ((if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest))).set LIT_POL [(if pol then 1 else 0)]).set CNF_STREAM (List.replicate v 1 ++ 0 :: rest)).set LIT_VAR []).set IN_BLOCK []).set IN_BLOCK [1]))))
  -- arithmetic: everything against the budget base
  have hXX : (v + rest.length + 3 + (encodeAssgn a).length + 1) ^ 2
      = (v + rest.length + 3 + (encodeAssgn a).length + 1)
        * (v + rest.length + 3 + (encodeAssgn a).length + 1) := by ring
  rw [hXX]
  have hForExp : (v + 1 + rest.length) * ((v + 1 + rest.length) + 10)
      = (v + 1 + rest.length) * (v + 1 + rest.length)
        + 10 * (v + 1 + rest.length) := by ring
  rw [hForExp] at hForCost
  have hP1 : (v + 1 + rest.length) * (v + 1 + rest.length)
      ≤ (v + rest.length + 3 + (encodeAssgn a).length + 1)
        * (v + rest.length + 3 + (encodeAssgn a).length + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hP3 : ((encodeAssgn a).length + v + 1) ^ 2
      ≤ (v + rest.length + 3 + (encodeAssgn a).length + 1)
        * (v + rest.length + 3 + (encodeAssgn a).length + 1) := by
    calc ((encodeAssgn a).length + v + 1) ^ 2
        ≤ (v + rest.length + 3 + (encodeAssgn a).length + 1) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
      _ = _ := hXX
  have h4X : 4 * (v + rest.length + 3 + (encodeAssgn a).length + 1)
      ≤ (v + rest.length + 3 + (encodeAssgn a).length + 1)
        * (v + rest.length + 3 + (encodeAssgn a).length + 1) :=
    Nat.mul_le_mul (by omega) (Nat.le_refl _)
  omega

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
  rcases l with ⟨pol, v⟩
  have hstream' : st.get CNF_STREAM
      = 1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest) := by
    rw [hstream]
    simp [encodeLit, List.cons_append, List.append_assoc, List.nil_append]
  obtain ⟨h1, h2, h3, _⟩ := processOneLiteral_main st pol v rest a cs hstream' hassgn hsat
  exact ⟨h1, h2, h3⟩

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
  rcases l with ⟨pol, v⟩
  have hstream' : st.get CNF_STREAM
      = 1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ 0 :: rest) := by
    rw [hstream]
    simp [encodeLit, List.cons_append, List.append_assoc, List.nil_append]
  exact (processOneLiteral_main st pol v rest a cs hstream' hassgn hsat).2.2.2

theorem processOneLiteral_usesBelow : Cmd.UsesBelow processOneLiteral 16 := by
  simp [processOneLiteral, varExtractBody, memberCheck, mcBody, mcSkip,
    Cmd.UsesBelow, Op.UsesBelow, CNF_STREAM, ASSGN, CLAUSE_SAT, LIT_POL,
    LIT_VAR, ASSGN_COPY, MEMBER_FOUND, INNER_IDX, HEAD_CELL, CMP_FLAG,
    IN_BLOCK, BLOCK_ACC]

theorem processOneLiteral_noConsLen : Cmd.NoConsLen processOneLiteral := by
  simp only [processOneLiteral, varExtractBody, memberCheck, mcBody, mcSkip,
    Cmd.NoConsLen, Op.NotConsLen]
  trivial

/-! ### `processOneClause`: the clause scan loop -/

/-- The literal blocks of a clause, without the clause-end marker. -/
private def encodeLits (C : clause) : List Nat :=
  C.foldr (fun l acc => encodeLit l ++ acc) []

private theorem encodeClause_eq_lits (C : clause) :
    encodeClause C = encodeLits C ++ [0] := rfl

private theorem encodeLits_cons (l : literal) (C : clause) :
    encodeLits (l :: C) = encodeLit l ++ encodeLits C := rfl

private theorem encodeLits_append (A B : clause) :
    encodeLits (A ++ B) = encodeLits A ++ encodeLits B := by
  induction A with
  | nil => rfl
  | cons l A ih =>
      rw [List.cons_append, encodeLits_cons, encodeLits_cons, ih,
        List.append_assoc]

private theorem encodeLits_length_ge (C : clause) :
    C.length ≤ (encodeLits C).length := by
  induction C with
  | nil => simp [encodeLits]
  | cons l C ih =>
      rw [encodeLits_cons, List.length_append, List.length_cons]
      have h1 : 1 ≤ (encodeLit l).length := by
        rcases l with ⟨pol, w⟩
        simp [encodeLit]
      omega

private theorem encodeLits_drop_length_le (C : clause) (i : Nat) :
    (encodeLits (C.drop i)).length ≤ (encodeLits C).length := by
  conv_rhs => rw [← List.take_append_drop i C]
  rw [encodeLits_append, List.length_append]
  omega

private theorem evalClause_take_succ (a : assgn) (C : clause) (i : Nat)
    (hi : i < C.length) :
    evalClause a (C.take (i + 1))
      = (evalClause a (C.take i) || evalLiteral a C[i]) := by
  rw [List.take_succ_eq_append_getElem hi]
  show ((C.take i) ++ [C[i]]).any _ = _
  rw [List.any_append]
  simp [evalClause]

/-- The clause-scan loop invariant: through iteration `C.length` the loop has
consumed `i` whole literal blocks (one per iteration) and ORed them into
`CLAUSE_SAT`; at iteration `C.length` it consumes the clause-end `0`, folds
`CLAUSE_SAT` into `OUTPUT` and sets `CLAUSE_DONE`; afterwards it idles. -/
private def CInv (C : clause) (rest : List Nat) (a : assgn) (b : Bool)
    (i : Nat) (s : State) : Prop :=
  (if i ≤ C.length then
    s.get CLAUSE_DONE = [0]
    ∧ s.get CNF_STREAM = encodeLits (C.drop i) ++ 0 :: rest
    ∧ s.get CLAUSE_SAT = [if evalClause a (C.take i) then 1 else 0]
    ∧ s.get OUTPUT = [if b then 1 else 0]
  else
    s.get CLAUSE_DONE = [1]
    ∧ s.get CNF_STREAM = rest
    ∧ s.get OUTPUT = [if b && evalClause a C then 1 else 0])
  ∧ s.get ASSGN = encodeAssgn a

private theorem CInv_step (C : clause) (rest : List Nat) (a : assgn) (b : Bool)
    (i : Nat) (s : State) (h : CInv C rest a b i s) :
    CInv C rest a b (i + 1)
      (clauseBody.eval (s.set INNER_IDX (List.replicate i 1))) := by
  obtain ⟨hphase, hASS⟩ := h
  by_cases hile : i ≤ C.length
  · rw [if_pos hile] at hphase
    obtain ⟨hCD, hCS, hCSAT, hOUT⟩ := hphase
    have hCD' : (s.set INNER_IDX (List.replicate i 1)).get CLAUSE_DONE ≠ [1] := by
      rw [State.get_set_ne _ _ _ _ (by decide), hCD]; decide
    have heval : clauseBody.eval (s.set INNER_IDX (List.replicate i 1))
        = (Cmd.op (.head HEAD_CELL CNF_STREAM) ;;
           Cmd.ifBit HEAD_CELL
             processOneLiteral
             (Cmd.op (.tail CNF_STREAM CNF_STREAM) ;;
              Cmd.ifBit CLAUSE_SAT
                mcSkip
                (Cmd.op (.clear OUTPUT) ;; Cmd.op (.appendZero OUTPUT)) ;;
              Cmd.op (.clear CLAUSE_DONE) ;; Cmd.op (.appendOne CLAUSE_DONE))).eval
            (s.set INNER_IDX (List.replicate i 1)) := by
      show (Cmd.ifBit CLAUSE_DONE _ _).eval _ = _
      rw [Cmd.eval_ifBit_false _ _ _ _ hCD']
    by_cases hlt : i < C.length
    · -- a literal block: one `processOneLiteral` consumes it whole
      have hdecomp : encodeLits (C.drop i) ++ 0 :: rest
          = encodeLit C[i] ++ (encodeLits (C.drop (i + 1)) ++ 0 :: rest) := by
        rw [List.drop_eq_getElem_cons hlt, encodeLits_cons, List.append_assoc]
      have hCS' : (s.set INNER_IDX (List.replicate i 1)).get CNF_STREAM
          = encodeLit C[i] ++ (encodeLits (C.drop (i + 1)) ++ 0 :: rest) := by
        rw [State.get_set_ne _ _ _ _ (by decide), hCS, hdecomp]
      have hhead1 : ∃ tl, encodeLit C[i] ++ (encodeLits (C.drop (i + 1)) ++ 0 :: rest)
          = 1 :: tl := by
        rcases hCi : C[i] with ⟨pol, w⟩
        exact ⟨_, rfl⟩
      obtain ⟨tl, htl⟩ := hhead1
      have e1 : (Cmd.op (.head HEAD_CELL CNF_STREAM)).eval
          (s.set INNER_IDX (List.replicate i 1))
          = (s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hCS', htl]
      have hHC : ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          HEAD_CELL = [1] := State.get_set_eq _ _ _
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_true _ _ _ _ hHC] at heval
      -- the pinned literal contract
      have hstream'' : ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          CNF_STREAM = encodeLit C[i] ++ (encodeLits (C.drop (i + 1)) ++ 0 :: rest) := by
        rw [State.get_set_ne _ _ _ _ (by decide)]; exact hCS'
      have hassgn'' : ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          ASSGN = encodeAssgn a := by
        rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hASS
      have hsat'' : ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          CLAUSE_SAT = [if evalClause a (C.take i) then 1 else 0] := by
        rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hCSAT
      obtain ⟨p1, p2, p3⟩ := processOneLiteral_run _ C[i]
        (encodeLits (C.drop (i + 1)) ++ 0 :: rest) a (evalClause a (C.take i))
        hstream'' hassgn'' hsat''
      rw [heval]
      constructor
      · rw [if_pos (by omega : i + 1 ≤ C.length)]
        refine ⟨?_, p2, ?_, ?_⟩
        · rw [p3 CLAUSE_DONE (by decide), State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide)]
          exact hCD
        · rw [p1, evalClause_take_succ a C i hlt]
        · rw [p3 OUTPUT (by decide), State.get_set_ne _ _ _ _ (by decide),
            State.get_set_ne _ _ _ _ (by decide)]
          exact hOUT
      · rw [p3 ASSGN (by decide), State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hASS
    · -- the clause-end `0`: fold CLAUSE_SAT into OUTPUT, set CLAUSE_DONE
      have hieq : i = C.length := by omega
      subst hieq
      have hCS0 : (s.set INNER_IDX (List.replicate C.length 1)).get CNF_STREAM
          = 0 :: rest := by
        rw [State.get_set_ne _ _ _ _ (by decide), hCS, List.drop_length]
        rfl
      have e1 : (Cmd.op (.head HEAD_CELL CNF_STREAM)).eval
          (s.set INNER_IDX (List.replicate C.length 1))
          = (s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL [0] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hCS0]
      have hHC : ((s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL
          [0]).get HEAD_CELL ≠ [1] := by
        rw [State.get_set_eq]; decide
      have e2 : (Cmd.op (.tail CNF_STREAM CNF_STREAM)).eval
          ((s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL [0])
          = ((s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL [0]).set
              CNF_STREAM rest := by
        rw [Cmd.eval_op]; simp only [Op.eval]
        rw [State.get_set_ne _ _ _ _ (by decide), hCS0, List.tail_cons]
      have hCSAT3 : (((s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL
          [0]).set CNF_STREAM rest).get CLAUSE_SAT
          = [if evalClause a C then 1 else 0] := by
        rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide), hCSAT, List.take_length]
      rw [Cmd.eval_seq, e1, Cmd.eval_ifBit_false _ _ _ _ hHC, Cmd.eval_seq, e2,
        Cmd.eval_seq] at heval
      cases hsatC : evalClause a C with
      | true =>
          have hCSAT3' : (((s.set INNER_IDX (List.replicate C.length 1)).set
              HEAD_CELL [0]).set CNF_STREAM rest).get CLAUSE_SAT = [1] := by
            rw [hCSAT3, hsatC]
            rfl
          rw [Cmd.eval_ifBit_true _ _ _ _ hCSAT3', mcSkip_eval, Cmd.eval_seq,
            Cmd.eval_op, Cmd.eval_op] at heval
          simp only [Op.eval] at heval
          rw [State.get_set_eq, List.nil_append] at heval
          rw [heval]
          constructor
          · rw [if_neg (by omega : ¬ C.length + 1 ≤ C.length)]
            refine ⟨?_, ?_, ?_⟩
            · rw [State.get_set_eq]
            · rw [State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
            · rw [State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide), hOUT, hsatC,
                Bool.and_true]
          · rw [State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide)]
            exact hASS
      | false =>
          have hCSAT3' : (((s.set INNER_IDX (List.replicate C.length 1)).set
              HEAD_CELL [0]).set CNF_STREAM rest).get CLAUSE_SAT ≠ [1] := by
            rw [hCSAT3, hsatC]; decide
          rw [Cmd.eval_ifBit_false _ _ _ _ hCSAT3', Cmd.eval_seq, Cmd.eval_op,
            Cmd.eval_op] at heval
          simp only [Op.eval] at heval
          rw [State.get_set_eq, List.nil_append] at heval
          rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op] at heval
          simp only [Op.eval] at heval
          rw [State.get_set_eq, List.nil_append] at heval
          rw [heval]
          constructor
          · rw [if_neg (by omega : ¬ C.length + 1 ≤ C.length)]
            refine ⟨?_, ?_, ?_⟩
            · rw [State.get_set_eq]
            · rw [State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide), State.get_set_eq]
            · rw [State.get_set_ne _ _ _ _ (by decide),
                State.get_set_ne _ _ _ _ (by decide), State.get_set_eq,
                hsatC, Bool.and_false]
              rfl
          · rw [State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide),
              State.get_set_ne _ _ _ _ (by decide)]
            exact hASS
  · -- idle iterations after the clause is done
    rw [if_neg hile] at hphase
    obtain ⟨hCD, hCS, hOUT⟩ := hphase
    have hCD' : (s.set INNER_IDX (List.replicate i 1)).get CLAUSE_DONE = [1] := by
      rw [State.get_set_ne _ _ _ _ (by decide)]; exact hCD
    have heval : clauseBody.eval (s.set INNER_IDX (List.replicate i 1))
        = ((s.set INNER_IDX (List.replicate i 1)).set CMP_FLAG [1]) := by
      show (Cmd.ifBit CLAUSE_DONE _ _).eval _ = _
      rw [Cmd.eval_ifBit_true _ _ _ _ hCD', mcSkip_eval]
    rw [heval]
    constructor
    · rw [if_neg (by omega : ¬ i + 1 ≤ C.length)]
      refine ⟨?_, ?_, ?_⟩
      · rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hCD
      · rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hCS
      · rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hOUT
    · rw [State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide)]
      exact hASS

/-- Uniform per-iteration cost of the clause-scan body (the worst case is a
whole-literal iteration: one `processOneLiteral`, quadratic). -/
private theorem CInv_cost (C : clause) (rest : List Nat) (a : assgn) (b : Bool)
    (i : Nat) (s : State) (h : CInv C rest a b i s) :
    clauseBody.cost (s.set INNER_IDX (List.replicate i 1))
      ≤ 300 * ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 2 + ((encodeClause C).length + rest.length) + 20 := by
  obtain ⟨hphase, hASS⟩ := h
  by_cases hile : i ≤ C.length
  · rw [if_pos hile] at hphase
    obtain ⟨hCD, hCS, hCSAT, hOUT⟩ := hphase
    have hCD' : (s.set INNER_IDX (List.replicate i 1)).get CLAUSE_DONE ≠ [1] := by
      rw [State.get_set_ne _ _ _ _ (by decide), hCD]; decide
    by_cases hlt : i < C.length
    · -- literal iteration: 4 + one processOneLiteral
      have hdecomp : encodeLits (C.drop i) ++ 0 :: rest
          = encodeLit C[i] ++ (encodeLits (C.drop (i + 1)) ++ 0 :: rest) := by
        rw [List.drop_eq_getElem_cons hlt, encodeLits_cons, List.append_assoc]
      have hCS' : (s.set INNER_IDX (List.replicate i 1)).get CNF_STREAM
          = encodeLit C[i] ++ (encodeLits (C.drop (i + 1)) ++ 0 :: rest) := by
        rw [State.get_set_ne _ _ _ _ (by decide), hCS, hdecomp]
      have hhead1 : ∃ tl, encodeLit C[i] ++ (encodeLits (C.drop (i + 1)) ++ 0 :: rest)
          = 1 :: tl := by
        rcases hCi : C[i] with ⟨pol, w⟩
        exact ⟨_, rfl⟩
      obtain ⟨tl, htl⟩ := hhead1
      have e1 : (Cmd.op (.head HEAD_CELL CNF_STREAM)).eval
          (s.set INNER_IDX (List.replicate i 1))
          = (s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hCS', htl]
      have hHC : ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          HEAD_CELL = [1] := State.get_set_eq _ _ _
      have hstream'' : ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          CNF_STREAM = encodeLit C[i] ++ (encodeLits (C.drop (i + 1)) ++ 0 :: rest) := by
        rw [State.get_set_ne _ _ _ _ (by decide)]; exact hCS'
      have hassgn'' : ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          ASSGN = encodeAssgn a := by
        rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hASS
      have hsat'' : ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          CLAUSE_SAT = [if evalClause a (C.take i) then 1 else 0] := by
        rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hCSAT
      have hpolcost := processOneLiteral_cost _ C[i]
        (encodeLits (C.drop (i + 1)) ++ 0 :: rest) a (evalClause a (C.take i))
        hstream'' hassgn'' hsat''
      have hc : clauseBody.cost (s.set INNER_IDX (List.replicate i 1))
          = 1 + (1 + 1 + (1 + processOneLiteral.cost
              ((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]))) := by
        show (Cmd.ifBit CLAUSE_DONE _ _).cost _ = _
        rw [Cmd.cost_ifBit_false _ _ _ _ hCD', Cmd.cost_seq, Cmd.cost_op, e1,
          Cmd.cost_ifBit_true _ _ _ _ hHC]
        simp only [Op.cost]
      -- the stream at this iteration is no longer than the whole clause block
      have hlen : (((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          CNF_STREAM).length ≤ (encodeClause C).length + rest.length := by
        rw [hstream'', ← hdecomp]
        have h1 : (encodeClause C).length = (encodeLits C).length + 1 := by
          rw [encodeClause_eq_lits, List.length_append]; rfl
        have h2 := encodeLits_drop_length_le C i
        simp only [List.length_append, List.length_cons]
        omega
      have hAlen : (((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          ASSGN).length = (encodeAssgn a).length := by rw [hassgn'']
      have hmono : ((((s.set INNER_IDX (List.replicate i 1)).set HEAD_CELL [1]).get
          CNF_STREAM).length + (((s.set INNER_IDX (List.replicate i 1)).set
          HEAD_CELL [1]).get ASSGN).length + 1) ^ 2 ≤ ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 2 := by
        refine Nat.pow_le_pow_left ?_ 2
        rw [hAlen]
        omega
      rw [hc]
      have h300 := Nat.mul_le_mul_left 300 hmono
      omega
    · -- the clause-end iteration
      have hieq : i = C.length := by omega
      subst hieq
      have hCS0 : (s.set INNER_IDX (List.replicate C.length 1)).get CNF_STREAM
          = 0 :: rest := by
        rw [State.get_set_ne _ _ _ _ (by decide), hCS, List.drop_length]
        rfl
      have e1 : (Cmd.op (.head HEAD_CELL CNF_STREAM)).eval
          (s.set INNER_IDX (List.replicate C.length 1))
          = (s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL [0] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hCS0]
      have hHC : ((s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL
          [0]).get HEAD_CELL ≠ [1] := by
        rw [State.get_set_eq]; decide
      have htail : Op.cost (.tail CNF_STREAM CNF_STREAM)
          ((s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL [0])
          = rest.length + 2 := by
        show (((s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL
          [0]).get CNF_STREAM).length + 1 = _
        rw [State.get_set_ne _ _ _ _ (by decide), hCS0]
        simp
      have hIfC : ∀ t : State, (Cmd.ifBit CLAUSE_SAT mcSkip
          (Cmd.op (.clear OUTPUT) ;; Cmd.op (.appendZero OUTPUT))).cost t ≤ 4 := by
        intro t
        by_cases hb : t.get CLAUSE_SAT = [1]
        · rw [Cmd.cost_ifBit_true _ _ _ _ hb, mcSkip_cost]
        · rw [Cmd.cost_ifBit_false _ _ _ _ hb, Cmd.cost_seq, Cmd.cost_op,
            Cmd.cost_op]
          simp only [Op.cost]
          omega
      have hCDtail : ∀ t : State, (Cmd.op (.clear CLAUSE_DONE) ;;
          Cmd.op (.appendOne CLAUSE_DONE)).cost t = 3 := by
        intro t
        rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
        simp only [Op.cost]
      have hc : clauseBody.cost (s.set INNER_IDX (List.replicate C.length 1))
          = 1 + (1 + 1 + (1 + (1 + (rest.length + 2)
              + (1 + (Cmd.ifBit CLAUSE_SAT mcSkip
                  (Cmd.op (.clear OUTPUT) ;; Cmd.op (.appendZero OUTPUT))).cost
                  (((s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL
                    [0]).set CNF_STREAM rest)
                + 3)))) := by
        show (Cmd.ifBit CLAUSE_DONE _ _).cost _ = _
        rw [Cmd.cost_ifBit_false _ _ _ _ hCD', Cmd.cost_seq, Cmd.cost_op, e1,
          Cmd.cost_ifBit_false _ _ _ _ hHC, Cmd.cost_seq, Cmd.cost_op, htail,
          Cmd.cost_seq, Cmd.eval_op]
        simp only [Op.eval, Op.cost]
        rw [State.get_set_ne _ _ _ _ (by decide), hCS0, List.tail_cons,
          hCDtail]
      rw [hc]
      have := hIfC (((s.set INNER_IDX (List.replicate C.length 1)).set HEAD_CELL
        [0]).set CNF_STREAM rest)
      have hRle : rest.length ≤ (encodeClause C).length + rest.length := by omega
      have hsq : 0 ≤ 300 * ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 2 := Nat.zero_le _
      omega
  · -- idle
    rw [if_neg hile] at hphase
    have hCD' : (s.set INNER_IDX (List.replicate i 1)).get CLAUSE_DONE = [1] := by
      rw [State.get_set_ne _ _ _ _ (by decide)]; exact hphase.1
    have hc : clauseBody.cost (s.set INNER_IDX (List.replicate i 1)) = 1 + 3 := by
      show (Cmd.ifBit CLAUSE_DONE _ _).cost _ = _
      rw [Cmd.cost_ifBit_true _ _ _ _ hCD', mcSkip_cost]
    rw [hc]
    omega

/-- Combined behaviour + cost for `processOneClause`. -/
private theorem processOneClause_main (st : State) (C : clause) (rest : List Nat)
    (a : assgn) (b : Bool)
    (hstream : st.get CNF_STREAM = encodeClause C ++ rest)
    (hassgn : st.get ASSGN = encodeAssgn a)
    (hout : st.get OUTPUT = [if b then 1 else 0]) :
    ((processOneClause.eval st).get OUTPUT
        = [if b && evalClause a C then 1 else 0])
    ∧ ((processOneClause.eval st).get CNF_STREAM = rest)
    ∧ ((processOneClause.eval st).get ASSGN = encodeAssgn a)
    ∧ processOneClause.cost st
        ≤ 1000 * ((st.get CNF_STREAM).length + (st.get ASSGN).length + 1) ^ 3 := by
  have eP : processOneClause.eval st
      = (Cmd.forBnd INNER_IDX CNF_STREAM clauseBody).eval ((((st.set CLAUSE_SAT []).set CLAUSE_SAT [0]).set CLAUSE_DONE []).set CLAUSE_DONE [0]) := by
    show (Cmd.eval (_ ;; _ ;; _ ;; _ ;; _) st) = _
    simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
      List.nil_append]
  have hCSb : ((((st.set CLAUSE_SAT []).set CLAUSE_SAT [0]).set CLAUSE_DONE []).set CLAUSE_DONE [0]).get CNF_STREAM = encodeClause C ++ rest := by
    rw [State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide),
      State.get_set_ne _ _ _ _ (by decide), State.get_set_ne _ _ _ _ (by decide)]
    exact hstream
  have hnlen : (((((st.set CLAUSE_SAT []).set CLAUSE_SAT [0]).set CLAUSE_DONE []).set CLAUSE_DONE [0]).get CNF_STREAM).length
      = (encodeClause C).length + rest.length := by
    rw [hCSb, List.length_append]
  have base : CInv C rest a b 0 ((((st.set CLAUSE_SAT []).set CLAUSE_SAT [0]).set CLAUSE_DONE []).set CLAUSE_DONE [0]) := by
    constructor
    · rw [if_pos (Nat.zero_le _)]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [State.get_set_eq]
      · rw [hCSb, List.drop_zero, encodeClause_eq_lits, List.append_assoc]
        rfl
      · rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide), State.get_set_eq,
          List.take_zero]
        rfl
      · rw [State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide),
          State.get_set_ne _ _ _ _ (by decide)]
        exact hout
    · rw [State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide),
        State.get_set_ne _ _ _ _ (by decide)]
      exact hassgn
  have hfin := Cmd.foldlState_range_induct clauseBody INNER_IDX
    (((((st.set CLAUSE_SAT []).set CLAUSE_SAT [0]).set CLAUSE_DONE []).set CLAUSE_DONE [0]).get CNF_STREAM).length ((((st.set CLAUSE_SAT []).set CLAUSE_SAT [0]).set CLAUSE_DONE []).set CLAUSE_DONE [0]) (CInv C rest a b) base
    (fun i s _ h => CInv_step C rest a b i s h)
  have hgtC : ¬ ((((((st.set CLAUSE_SAT []).set CLAUSE_SAT [0]).set CLAUSE_DONE []).set CLAUSE_DONE [0]).get CNF_STREAM).length ≤ C.length) := by
    rw [hnlen]
    have h1 : (encodeClause C).length = (encodeLits C).length + 1 := by
      rw [encodeClause_eq_lits, List.length_append]; rfl
    have h2 := encodeLits_length_ge C
    omega
  obtain ⟨hphase, hASSf⟩ := hfin
  rw [if_neg hgtC] at hphase
  obtain ⟨hCDf, hCSf, hOUTf⟩ := hphase
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eP, Cmd.eval_forBnd]; exact hOUTf
  · rw [eP, Cmd.eval_forBnd]; exact hCSf
  · rw [eP, Cmd.eval_forBnd]; exact hASSf
  · -- the cost side
    have hcost_eq : processOneClause.cost st
        = 8 + (Cmd.forBnd INNER_IDX CNF_STREAM clauseBody).cost ((((st.set CLAUSE_SAT []).set CLAUSE_SAT [0]).set CLAUSE_DONE []).set CLAUSE_DONE [0]) := by
      show (Cmd.cost (_ ;; _ ;; _ ;; _ ;; _) st) = _
      simp only [Cmd.cost_seq, Cmd.cost_op, Cmd.eval_op, Op.eval, Op.cost,
        State.get_set_eq, List.nil_append]
      omega
    have hB := Cmd.cost_forBnd_le INNER_IDX CNF_STREAM clauseBody ((((st.set CLAUSE_SAT []).set CLAUSE_SAT [0]).set CLAUSE_DONE []).set CLAUSE_DONE [0])
      (300 * ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 2 + ((encodeClause C).length + rest.length) + 20) (CInv C rest a b) base
      (fun i s _ h => CInv_step C rest a b i s h)
      (fun i s _ h => CInv_cost C rest a b i s h)
    rw [hnlen] at hB
    have hLst : (st.get CNF_STREAM).length
        = (encodeClause C).length + rest.length := by
      rw [hstream, List.length_append]
    have hAst : (st.get ASSGN).length = (encodeAssgn a).length := by rw [hassgn]
    rw [hcost_eq, hLst, hAst]
    -- arithmetic against the cubic budget
    have hBexp : ((encodeClause C).length + rest.length) * (300 * ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 2 + ((encodeClause C).length + rest.length) + 20)
        ≤ ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) * (300 * ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 2 + ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) + 20) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hMexp : ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) * (300 * ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 2 + ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) + 20)
        = 300 * ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 3 + ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 2 + 20 * ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) := by ring
    have hn2sq : ((encodeClause C).length + rest.length) * ((encodeClause C).length + rest.length) ≤ ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) * ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hMM : ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) * ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) = ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 2 := by ring
    have h23 : ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 2 ≤ ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h13 : ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ≤ ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 3 := by
      calc ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) = ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 1 := (pow_one _).symm
        _ ≤ ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h03 : 1 ≤ ((encodeClause C).length + rest.length + (encodeAssgn a).length + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    rw [hMexp] at hBexp
    omega

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
  obtain ⟨h1, h2, h3, _⟩ := processOneClause_main st C rest a b hstream hassgn hout
  exact ⟨h1, h2, h3⟩

/-- **(pinned, bottom-up — THE interface) `processOneClause` cost** — cubic in
the entry lengths (uniform-bound accounting: `|CNF_STREAM|` slots at
worst-case `processOneLiteral` cost — quadratic — plus the counter charge). -/
theorem processOneClause_cost (st : State) (C : clause) (rest : List Nat)
    (a : assgn) (b : Bool)
    (hstream : st.get CNF_STREAM = encodeClause C ++ rest)
    (hassgn : st.get ASSGN = encodeAssgn a)
    (hout : st.get OUTPUT = [if b then 1 else 0]) :
    processOneClause.cost st
      ≤ 1000 * ((st.get CNF_STREAM).length + (st.get ASSGN).length + 1) ^ 3 :=
  (processOneClause_main st C rest a b hstream hassgn hout).2.2.2

/-- **(pinned, bottom-up)** `processOneClause` touches only registers `0–15`. -/
theorem processOneClause_usesBelow : Cmd.UsesBelow processOneClause 16 := by
  simp [processOneClause, clauseBody, processOneLiteral, varExtractBody,
    memberCheck, mcBody, mcSkip, Cmd.UsesBelow, Op.UsesBelow, OUTPUT,
    CNF_STREAM, ASSGN, CLAUSE_SAT, LIT_POL, LIT_VAR, ASSGN_COPY, MEMBER_FOUND,
    CLAUSE_DONE, INNER_IDX, HEAD_CELL, CMP_FLAG, IN_BLOCK, BLOCK_ACC]

/-- **(pinned, bottom-up)** `processOneClause` uses no `Op.consLen` (none is
needed — the live path is `consLen`-free). -/
theorem processOneClause_noConsLen : Cmd.NoConsLen processOneClause := by
  simp only [processOneClause, clauseBody, processOneLiteral, varExtractBody,
    memberCheck, mcBody, mcSkip, Cmd.NoConsLen, Op.NotConsLen]
  trivial

/-- The full SAT verifier. -/
def evalCnfCmd : Cmd :=
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
quartic cost bound (`EvalCnfTM.timeBound`) then absorbs it (see
`EvalCnfTM.encodeIn_size`). -/
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

/-! ## Construction notes (parsing the unary stream) — as built & proven

The encoding is **unary / bit-level** (`BitState`, discharged by
`encodeState_bit`); every field is `{0,1}` and self-delimiting. The bodies
above implement exactly this plan:

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

The bodies were **probe-validated with `#eval` before proving** (exhaustive
small-CNF sweep against `evalCnf`; contract-level probes with garbage scratch
on entry; numeric cost-budget checks).

Two DSL conveniences would shorten these (optional, not required):
1. **A conditional/guarded loop** (`Cmd.while`) — the cell loops must iterate
   `|CNF_STREAM|`/`|ASSGN_COPY|` times with done-flag no-ops. (This is also
   what forces the uniform-bound quartic cost — see `evalCnfCmd_cost_bound`.)
2. **A primitive scan-to-separator op** — would compress the per-literal parse.
Each new `Op` is another compiler soundness case (C5 policy: only add when it
materially shortens things); the flag-guarded loops above work with the ops we
have. -/

end EvalCnfCmd
