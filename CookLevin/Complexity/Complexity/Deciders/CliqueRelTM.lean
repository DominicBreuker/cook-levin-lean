import Complexity.Complexity.TMDecider
import Complexity.NP.FlatClique
import Complexity.Lang

set_option autoImplicit false

/-! # The FlatClique-verifier — closed via the Lang layer (Part 3.5)

This file owns the TM-backed decider for the FlatClique verification
relation
`fun (Gkl : (fgraph × Nat) × List fvertex) => cliqueRel Gkl.1 Gkl.2`
— i.e., the witness that `FlatClique ∈ NP`.

**Status (2026-06-30b, top-down).** The input **encoding** (`cliqueRelEncode`) +
all encoding/structural witness fields are PROVEN & axiom-clean. The verifier
**program** `cliqueRelCmd` is concrete and trio-free. The **correctness layer** is
being built bottom-up against the proven `EvalCnfCmd` template: the leaves
`ltBit_run` + `readNum_run` and 3 of the 5 per-check run-lemmas
(`checkLen_run`/`checkOfType_run`/`checkWf_run`) are PROVEN & axiom-clean. The two
remaining `DecidesLang` fields `decides`/`cost_bound` stay `sorry` pending the
nested-loop checks (`memberEdge`/`checkNodup`/`checkClique`) + the assembly. See
HANDOFF.md top-down Task 1 for the concrete remaining steps.

Note: `inTimePolyTM_cliqueRel` keeps its full name + signature so
`FlatClique_in_NP` (below) does not need to change.
-/

namespace CliqueRelTM

open Complexity.Lang

/-- Polynomial time budget for `cliqueRelDecTM`.

**⚠ 2026-06-29 (top-down): quartic, NOT the old `(n+1)^3`.** Mirrors the
`EvalCnfTM.timeBound` finding: the only loop-cost tool (`Cmd.cost_forBnd_le`)
charges a *uniform* worst-case per-iteration bound, so the clique verifier's
nested loops (outer scan over `l`, inner scan over `l`, innermost membership
scan over the edge stream — `|l|²·|edges|·numV`) compound to degree ≥ 4.
Downstream only needs `inOPoly`/`monotonic`, so the degree is free.

**⚠ 2026-07-01 (top-down): bumped to QUINTIC `(n+1)^5`.** Proving `cost_bound`
surfaced that the depth-4 `checkClique` nest is degree **5** under uniform-bound
accounting, NOT 4: the innermost `readNum` costs `Θ(S²)` (a `tail` per drained
cell), and it sits under three `forBnd`s (outer `l` × inner `l` × `memberEdge`'s
edge scan), giving `|l|²·|edges|·|stream|² ~ n^5`. The true TM cost is quartic
(`readNum` on a block of size `v` out of a stream of length `S` costs `Θ(v·S)`,
and `Σ v = S` amortises one factor away), but amortisation is invisible to
`Cmd.cost_forBnd_le`'s uniform worst-case bound and building an amortised
`cost_forBnd` is unjustified when only `inOPoly` is needed. The `200000` constant
is generous. -/
def timeBound (n : Nat) : Nat := 200000 * (n + 1) ^ 5

theorem timeBound_inOPoly : inOPoly timeBound := by
  refine ⟨5, ⟨6400000, 1, ?_⟩⟩
  intro n hn
  have hle : n + 1 ≤ n + n := Nat.add_le_add_left hn n
  show 200000 * (n + 1) ^ 5 ≤ 6400000 * n ^ 5
  calc 200000 * (n + 1) ^ 5
      ≤ 200000 * (n + n) ^ 5 :=
        Nat.mul_le_mul_left 200000 (Nat.pow_le_pow_left hle 5)
    _ = 6400000 * n ^ 5 := by ring

theorem timeBound_monotonic : monotonic timeBound :=
  fun _ _ h =>
    Nat.mul_le_mul_left 200000 (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 5)

/-! ## Input encoding (bit-level, unary, self-delimiting)

Probe-validated in `probes/CliqueRelProbe.lean`. Every cell is `0`/`1` (so the
encoded state is a `Compile.BitState`, `Compile.sig = 4` — the precondition the
compiler needs, B′). Numbers are unary `1`-blocks terminated by a `0`; each list
carries a unary `replicate length 1` **tally** register (the `forBnd` loop
bound, so no list-level end sentinel is needed — the EvalCnf CNF-stream pattern).

| Reg | Contents (input data; scratch regs 7+ read as `[]`) |
|-----|------------------------------------------------------|
| 0   | `OUTPUT`                                              |
| 1   | `replicate G.1 1` — vertex count `numV`, unary        |
| 2   | `encEdges G.2` — edge stream (destructively consumed) |
| 3   | `replicate k 1` — clique size `k`, unary              |
| 4   | `encVerts l` — vertex stream (destructively consumed) |
| 5   | `replicate G.2.length 1` — edge tally (loop bound)    |
| 6   | `replicate l.length 1` — vertex tally (loop bound)    |
-/

/-- One number, unary with a `0` terminator: `replicate v 1 ++ [0]`. -/
def encNum (v : Nat) : List Nat := List.replicate v 1 ++ [0]

/-- One edge = two terminated unary numbers. -/
def encEdge (e : fedge) : List Nat := encNum e.1 ++ encNum e.2

/-- The edge stream: the edges' encodings concatenated. -/
def encEdges (edges : List fedge) : List Nat := (edges.map encEdge).flatten

/-- The vertex stream: the vertices' encodings concatenated. -/
def encVerts (l : List fvertex) : List Nat := (l.map encNum).flatten

theorem encNum_length (v : Nat) : (encNum v).length = v + 1 := by
  simp [encNum]

theorem encNum_bit (v : Nat) : ∀ x ∈ encNum v, x ≤ 1 := by
  intro x hx
  simp only [encNum, List.mem_append, List.mem_replicate, List.mem_singleton] at hx
  rcases hx with ⟨_, h⟩ | h <;> omega

/-! ### `encodable.size` accounting helpers (replicated from `EvalCnfCmd`)

Under the unary encoding the encoded length grows with the *magnitudes* of the
numbers, but `encodable.size Nat = id` charges exactly those magnitudes, so the
total stays **linear** in `encodable.size`. -/

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

/-- Peel one vertex block off the front of the vertex stream. -/
theorem encVerts_cons (v : fvertex) (rest : List fvertex) :
    encVerts (v :: rest) = List.replicate v 1 ++ 0 :: encVerts rest := by
  simp only [encVerts, List.map_cons, List.flatten_cons, encNum]
  rw [List.append_assoc]; rfl

/-- Peel one edge (two unary blocks) off the front of the edge stream. -/
theorem encEdges_cons (e : fedge) (rest : List fedge) :
    encEdges (e :: rest)
      = List.replicate e.1 1 ++ 0 :: (List.replicate e.2 1 ++ 0 :: encEdges rest) := by
  simp only [encEdges, List.map_cons, List.flatten_cons, encEdge, encNum]
  rw [List.append_assoc, List.append_assoc, List.append_assoc]; rfl

/-- The vertex stream's length equals the list's encoded size (`size Nat = id`
makes the unary block of a vertex `v` cost exactly `v + 1`). -/
theorem encVerts_length (l : List fvertex) :
    (encVerts l).length = encodable.size l := by
  rw [encsize_list_foldr l]
  induction l with
  | nil => simp [encVerts]
  | cons v l ih =>
    simp only [encVerts, List.map_cons, List.flatten_cons, List.length_append,
      List.foldr_cons] at ih ⊢
    rw [ih, encNum_length]
    show v + 1 + _ = encodable.size v + 1 + _
    rfl

/-- The edge stream's length is bounded by `2 ·` the list's encoded size: each
edge `(a,b)` costs `(a+1)+(b+1) = a+b+2` cells, while its `encodable.size` is
`a+b+1`, so the per-edge ratio is `< 2`. -/
theorem encEdges_length_le (edges : List fedge) :
    (encEdges edges).length ≤ 2 * encodable.size edges := by
  rw [encsize_list_foldr edges]
  induction edges with
  | nil => simp [encEdges]
  | cons e edges ih =>
    simp only [encEdges, List.map_cons, List.flatten_cons, List.length_append,
      List.foldr_cons] at ih ⊢
    have he : (encEdge e).length = e.1 + e.2 + 2 := by
      simp only [encEdge, List.length_append, encNum_length]; omega
    have hse : encodable.size e = e.1 + e.2 + 1 := rfl
    rw [he]; omega

theorem encEdges_bit (edges : List fedge) : ∀ x ∈ encEdges edges, x ≤ 1 := by
  intro x hx
  simp only [encEdges, List.mem_flatten, List.mem_map] at hx
  obtain ⟨_, ⟨e, _, rfl⟩, hxe⟩ := hx
  simp only [encEdge, List.mem_append] at hxe
  rcases hxe with h | h <;> exact encNum_bit _ x h

theorem encVerts_bit (l : List fvertex) : ∀ x ∈ encVerts l, x ≤ 1 := by
  intro x hx
  simp only [encVerts, List.mem_flatten, List.mem_map] at hx
  obtain ⟨_, ⟨v, _, rfl⟩, hxv⟩ := hx
  exact encNum_bit _ x hxv

/-- How to lay out a `((fgraph, Nat), List fvertex)` input as a `Lang.State`
(7 data registers; scratch registers `7+` read as `[]`). Probe-validated. -/
def cliqueRelEncode :
    (fgraph × Nat) × List fvertex → State
  | ((G, k), l) =>
    [ []                                  -- 0: OUTPUT
    , List.replicate G.1 1                -- 1: NUMV
    , encEdges G.2                        -- 2: EDGE_STREAM
    , List.replicate k 1                  -- 3: K
    , encVerts l                          -- 4: VERT_STREAM
    , List.replicate G.2.length 1         -- 5: EDGE_TALLY
    , List.replicate l.length 1           -- 6: VERT_TALLY
    ]

/-- Register frame for the verifier. Generous (the nested-loop clique check needs
more scratch than EvalCnf's 16 — two vertex values, an edge-membership flag, edge
endpoints, and counters for the triple nesting). Tighten once `cliqueRelCmd` is
concrete and `usesBelow` pins the real footprint. -/
def regBound : Nat := 32

/-- **`Compile.BitState (cliqueRelEncode x)`** — every cell is `0`/`1`. -/
theorem cliqueRelEncode_bit (x : (fgraph × Nat) × List fvertex) :
    Compile.BitState (cliqueRelEncode x) := by
  obtain ⟨⟨G, k⟩, l⟩ := x
  intro reg hreg y hy
  simp only [cliqueRelEncode, List.mem_cons, List.not_mem_nil, or_false] at hreg
  rcases hreg with h | h | h | h | h | h | h <;> subst h
  · simp at hy
  · simp only [List.mem_replicate] at hy; omega
  · exact encEdges_bit G.2 y hy
  · simp only [List.mem_replicate] at hy; omega
  · exact encVerts_bit l y hy
  · simp only [List.mem_replicate] at hy; omega
  · simp only [List.mem_replicate] at hy; omega

/-- **The encoded state's total size is linearly bounded by the input size**
(`≤ 3 · size`). The unary blow-up is charged by `encodable.size Nat = id`; the
quartic `timeBound` then absorbs it. -/
theorem cliqueRelEncode_size_bound (x : (fgraph × Nat) × List fvertex) :
    State.size (cliqueRelEncode x) ≤ 3 * encodable.size x := by
  obtain ⟨⟨G, k⟩, l⟩ := x
  -- unfold the 7-register sum
  have hsz : State.size (cliqueRelEncode ((G, k), l))
      = G.1 + (encEdges G.2).length + k + (encVerts l).length
          + G.2.length + l.length := by
    simp only [cliqueRelEncode, State.size, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, List.length_replicate, List.length_nil]
    omega
  -- per-register bounds
  have h2 := encEdges_length_le G.2
  have h4 := encVerts_length l
  have h5 := length_le_encsize G.2
  have h6 := length_le_encsize l
  -- decompose `encodable.size ((G, k), l)`
  have hn : encodable.size ((G, k), l)
      = G.1 + encodable.size G.2 + k + encodable.size l + 3 := by
    show encodable.size ((G, k) : fgraph × Nat) + encodable.size l + 1
        = G.1 + encodable.size G.2 + k + encodable.size l + 3
    show (encodable.size G + encodable.size k + 1) + encodable.size l + 1
        = G.1 + encodable.size G.2 + k + encodable.size l + 3
    show ((encodable.size G.1 + encodable.size G.2 + 1) + k + 1)
          + encodable.size l + 1
        = G.1 + encodable.size G.2 + k + encodable.size l + 3
    show ((G.1 + encodable.size G.2 + 1) + k + 1) + encodable.size l + 1
        = G.1 + encodable.size G.2 + k + encodable.size l + 3
    omega
  rw [hsz, hn]
  omega

/-! ## The verifier program in the layer

**Probe-validated design** (`probes/CliqueRelProbe.lean` for the 5-check
algorithm; `probes/CliqueLtProbe.lean` for the novel unary-`<` gadget). The
program ANDs five checks into `OUTPUT` (start `[1]`; set `[0]` on any failure),
mirroring `EvalCnfCmd`'s clause-AND structure.

**Register frame** (all `< regBound = 32`; the originals 1–6 are never consumed,
each scan works on a fresh copy so the checks compose in any order):

| Reg | Name          | Role                                                |
|-----|---------------|-----------------------------------------------------|
| 0   | `OUTPUT`      | accept `[1]` / reject `[0]`                          |
| 1   | `NUMV`        | `replicate G.1 1` (read-only)                       |
| 2   | `EDGE_STREAM` | edge stream (read-only; copied per scan)            |
| 3   | `K`           | `replicate k 1` (read-only)                          |
| 4   | `VERT_STREAM` | vertex stream (read-only; copied per scan)          |
| 5   | `EDGE_TALLY`  | `replicate edges.length 1` (edge loop bound)        |
| 6   | `VERT_TALLY`  | `replicate l.length 1` (vertex loop bound)          |
| 7   | `IDX1`        | loop counter, nesting depth 1                       |
| 8   | `IDX2`        | loop counter, nesting depth 2                       |
| 9   | `IDX3`        | loop counter, nesting depth 3                       |
| 10  | `IDX4`        | loop counter, nesting depth 4 (`readNum` in clique) |
| 11  | `ESCAN`       | edge-stream scan copy (`fgraph_wf`)                 |
| 12  | `VSCAN`       | vertex-stream scan copy (outer)                     |
| 13  | `VSCAN2`      | vertex-stream scan copy (inner)                     |
| 14  | `ESCAN2`      | edge-stream scan copy (membership)                  |
| 15  | `HEAD`        | `readNum` head-cell scratch                         |
| 16  | `INBLK`       | `readNum` in-block parse flag                       |
| 17  | `VALA`        | unary value accumulator A (outer vertex / endpoint) |
| 18  | `VALB`        | unary value accumulator B (inner vertex / endpoint) |
| 19  | `VALC`        | unary value C (membership edge endpoint 1)          |
| 20  | `VALD`        | unary value D (membership edge endpoint 2)          |
| 21  | `LT_A`        | `ltBit` operand copy A                              |
| 22  | `LT_B`        | `ltBit` operand copy B                              |
| 23  | `RES1`        | result/branch flag 1                                |
| 24  | `RES2`        | result/branch flag 2                                |
| 25  | `FOUND`       | membership found flag (clique)                      |
| 26  | `SKIPR`       | `cSkip` no-op target                                |

⚠ **FINDING (2026-06-29, top-down): two patterns here are NOT in the proven
`EvalCnfCmd` template** (the handoff's "pure EvalCnf grind" understated this):
* **unary `<`** — checks 1–2 need a strict-order test on unary blocks, but the
  only comparison op is `eqBit` (equality). Built as `ltBit` (a lockstep
  consume loop; design `#eval`-validated in `probes/CliqueLtProbe.lean` over a
  7×7 grid). EvalCnf only ever compares for equality.
* **loop-counter reads** — `Nodup` (check 4) must skip the diagonal `i = j`, so
  its body reads the *unary loop counters* `IDX1`/`IDX2` (= `replicate i 1`) and
  `eqBit`s them; EvalCnf never reads a counter. (The clique check 5 instead
  skips by *value* equality, matching the spec, so it needs no counter read.)

Both are sound and shallow, but each needs its own fold-invariant lemma in the
correctness proof — budget for them. -/

def OUTPUT      : Var := 0
def NUMV        : Var := 1
def EDGE_STREAM : Var := 2
def K           : Var := 3
def VERT_STREAM : Var := 4
def EDGE_TALLY  : Var := 5
def VERT_TALLY  : Var := 6
def IDX1        : Var := 7
def IDX2        : Var := 8
def IDX3        : Var := 9
def IDX4        : Var := 10
def ESCAN       : Var := 11
def VSCAN       : Var := 12
def VSCAN2      : Var := 13
def ESCAN2      : Var := 14
def HEAD        : Var := 15
def INBLK       : Var := 16
def VALA        : Var := 17
def VALB        : Var := 18
def VALC        : Var := 19
def VALD        : Var := 20
def LT_A        : Var := 21
def LT_B        : Var := 22
def RES1        : Var := 23
def RES2        : Var := 24
def FOUND       : Var := 25
def SKIPR       : Var := 26

/-- Constant-cost no-op (`SKIPR := [1]`), the idle branch of guarded bodies.
`clear ⨾ appendOne` so the cost is state-independent (mirrors `EvalCnfCmd.mcSkip`,
needed since `eqBit` is size-aware). -/
def cSkip : Cmd := Cmd.op (.clear SKIPR) ;; Cmd.op (.appendOne SKIPR)

/-- **`reject`**: set `OUTPUT := [0]`. -/
def cReject : Cmd := Cmd.op (.clear OUTPUT) ;; Cmd.op (.appendZero OUTPUT)

/-- `dst := [0]` (used as `ltBit`'s "a ≥ b" branch; `clear ⨾ appendZero` on an
arbitrary register). -/
def cReject_to (dst : Var) : Cmd :=
  Cmd.op (.clear dst) ;; Cmd.op (.appendZero dst)

/-- Read one terminated unary block `replicate v 1 ++ [0]` off the front of
`stream` into `dst` (as `replicate v 1`), consuming the block + terminator from
`stream`. `idx` is the loop counter; the loop bound is `stream`'s entry length
(generous — once the block's `0` terminator clears `INBLK`, the remaining
iterations idle). Mirrors `EvalCnfCmd.varExtractBody`. -/
def readNum (dst stream idx : Var) : Cmd :=
  Cmd.op (.clear dst) ;;
  Cmd.op (.clear INBLK) ;; Cmd.op (.appendOne INBLK) ;;
  Cmd.forBnd idx stream
    (Cmd.ifBit INBLK
      (Cmd.op (.head HEAD stream) ;;
       Cmd.op (.tail stream stream) ;;
       Cmd.ifBit HEAD
         (Cmd.op (.appendOne dst))
         (Cmd.op (.clear INBLK)))
      cSkip)

/-- **Unary strict-less-than** (`probes/CliqueLtProbe.lean`): `dst := [1]` if the
unary value in `A` is `< ` the unary value in `B`, else `[0]`.

⚠ **2026-06-30 design fix (top-down): the prior lockstep realization was
INCORRECT.** It guarded the per-iteration consume with `Cmd.ifBit LT_A` /
`Cmd.ifBit LT_B`, but `Cmd.ifBit t` branches on `s.get t = [1]` *exactly*
(`Semantics.Cmd.eval_ifBit_true`), i.e. it is true only when the register holds a
SINGLE `1`-cell — not "nonempty". So on operands of magnitude `> 1` the loop body
never fired and the gadget returned the wrong verdict (e.g. `ltBit 2 5` gave
`[0]` although `2 < 5`). The probe modelled the guard as *nonemptiness*, which
`ifBit` does not provide.

**Correct (and simpler) realization** — `tail []` is `[]`, so an *unconditional*
lockstep drain needs no guard: copy `B` into `LT_B`, then `tail LT_B` once per
cell of `A` (`|A| = a` iterations). After `a` iterations `LT_B = replicate (b−a) 1`
(truncated subtraction), so `LT_B` is non-empty iff `b > a` iff `a < b`. Read the
verdict with one `nonEmpty`. (`A` is the loop *bound* — `forBnd` reads its length
once at entry, so `A` is never consumed; only `LT_B`, `idx`, `dst` are written.)
Proven in `ltBit_run`. -/
def ltBit (dst A B idx : Var) : Cmd :=
  Cmd.op (.copy LT_B B) ;;
  Cmd.forBnd idx A (Cmd.op (.tail LT_B LT_B)) ;;
  Cmd.op (.nonEmpty dst LT_B)

/-- **Check 1 — `fgraph_wf G`**: every edge endpoint `< numV`. Scan a copy of the
edge stream (bound = edge tally); per edge read both unary endpoints and `ltBit`
each against `NUMV`. -/
def checkWf : Cmd :=
  Cmd.op (.copy ESCAN EDGE_STREAM) ;;
  Cmd.forBnd IDX1 EDGE_TALLY
    (readNum VALA ESCAN IDX2 ;;
     readNum VALB ESCAN IDX2 ;;
     ltBit RES1 VALA NUMV IDX3 ;;
     ltBit RES2 VALB NUMV IDX3 ;;
     Cmd.ifBit RES1
       (Cmd.ifBit RES2 cSkip cReject)
       cReject)

/-- **Check 2 — `list_ofFlatType G.1 l`**: every vertex `< numV`. Scan a copy of
the vertex stream (bound = vertex tally); per vertex `ltBit` against `NUMV`. -/
def checkOfType : Cmd :=
  Cmd.op (.copy VSCAN VERT_STREAM) ;;
  Cmd.forBnd IDX1 VERT_TALLY
    (readNum VALA VSCAN IDX2 ;;
     ltBit RES1 VALA NUMV IDX3 ;;
     Cmd.ifBit RES1 cSkip cReject)

/-- **Check 3 — `l.length = k`**: `eqBit` the vertex tally against `K` (both
unary). -/
def checkLen : Cmd :=
  Cmd.op (.eqBit RES1 VERT_TALLY K) ;;
  Cmd.ifBit RES1 cSkip cReject

/-- **Check 4 — `l.Nodup`**: for every pair of *positions* `i ≠ j`, the vertices
differ. Outer scan consumes `VSCAN` (so the outer body reads `l[i]`); inner scan
is over a fresh full copy `VSCAN2`. Positions are the unary loop counters
`IDX1`/`IDX2`; `eqBit IDX1 IDX2` detects the diagonal `i = j` (skipped). -/
def checkNodup : Cmd :=
  Cmd.op (.copy VSCAN VERT_STREAM) ;;
  Cmd.forBnd IDX1 VERT_TALLY
    (readNum VALA VSCAN IDX2 ;;
     Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
     Cmd.forBnd IDX2 VERT_TALLY
       (readNum VALB VSCAN2 IDX3 ;;
        Cmd.op (.eqBit RES1 IDX1 IDX2) ;;          -- i = j ?
        Cmd.ifBit RES1
          cSkip                                     -- diagonal: skip
          (Cmd.op (.eqBit RES2 VALA VALB) ;;        -- l[i] = l[j] ?
           Cmd.ifBit RES2 cReject cSkip)))

/-- Membership scan: `FOUND := [1]` iff the ordered pair (`VALA`, `VALB`) occurs
in the edge stream. Scan a copy of the edge stream (bound = edge tally); per edge
read both endpoints (`VALC`/`VALD`) and `eqBit` them against `VALA`/`VALB`. The
`EvalCnfCmd.memberCheck` pattern, comparing TWO unary values per edge. -/
def memberEdge : Cmd :=
  Cmd.op (.clear FOUND) ;; Cmd.op (.appendZero FOUND) ;;
  Cmd.op (.copy ESCAN2 EDGE_STREAM) ;;
  Cmd.forBnd IDX3 EDGE_TALLY
    (readNum VALC ESCAN2 IDX4 ;;
     readNum VALD ESCAN2 IDX4 ;;
     Cmd.op (.eqBit RES1 VALC VALA) ;;
     Cmd.op (.eqBit RES2 VALD VALB) ;;
     Cmd.ifBit RES1
       (Cmd.ifBit RES2
         (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND))
         cSkip)
       cSkip)

/-- **Check 5 — clique**: every pair of list elements with *distinct values* is
an edge. Outer scan reads `l[i]` (`VALA`), inner scan reads `l[j]` (`VALB`); when
`VALA ≠ VALB`, require (`VALA`,`VALB`) ∈ edges via `memberEdge`. (Value-equality
skip matches the spec `∀ v₁ v₂ ∈ l, v₁ ≠ v₂ → (v₁,v₂) ∈ G.2`.) Nesting depth 4. -/
def checkClique : Cmd :=
  Cmd.op (.copy VSCAN VERT_STREAM) ;;
  Cmd.forBnd IDX1 VERT_TALLY
    (readNum VALA VSCAN IDX2 ;;
     Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
     Cmd.forBnd IDX2 VERT_TALLY
       (readNum VALB VSCAN2 IDX3 ;;
        Cmd.op (.eqBit RES1 VALA VALB) ;;          -- v₁ = v₂ ?
        Cmd.ifBit RES1
          cSkip                                     -- equal values: skip
          (memberEdge ;;
           Cmd.ifBit FOUND cSkip cReject)))

/-- The FlatClique verifier as a `Lang.Cmd`. Start `OUTPUT := [1]`, then AND the
five probe-validated checks. **Concrete & transcribed** (2026-06-29); the
correctness/cost proofs are the remaining work (HANDOFF top-down Task 1). -/
def cliqueRelCmd : Cmd :=
  Cmd.op (.appendOne OUTPUT) ;;
  checkWf ;;
  checkOfType ;;
  checkLen ;;
  checkNodup ;;
  checkClique

/-! ### Structural fields (PROVEN — purely syntactic over the concrete program) -/

/-- Register-frame helper: unfold one check to its op leaves and discharge the
resulting conjunction of literal `_ < 32`. Per-check so each `decide`'s
`Decidable`-synthesis term stays small (the monolithic conjunction over the whole
program defeats both `decide` and `omega`). -/
private theorem checkWf_usesBelow : Cmd.UsesBelow checkWf 32 := by
  simp [checkWf, readNum, ltBit, cSkip, cReject, Cmd.UsesBelow,
    Op.UsesBelow, NUMV, EDGE_STREAM, EDGE_TALLY, OUTPUT, IDX1, IDX2, IDX3,
    ESCAN, HEAD, INBLK, VALA, VALB, LT_B, RES1, RES2, SKIPR]

private theorem checkOfType_usesBelow : Cmd.UsesBelow checkOfType 32 := by
  simp [checkOfType, readNum, ltBit, cSkip, cReject,
    Cmd.UsesBelow, Op.UsesBelow, NUMV, VERT_STREAM, VERT_TALLY, OUTPUT, IDX1,
    IDX2, IDX3, VSCAN, HEAD, INBLK, VALA, LT_B, RES1, SKIPR]

private theorem checkLen_usesBelow : Cmd.UsesBelow checkLen 32 := by
  simp [checkLen, cSkip, cReject, Cmd.UsesBelow, Op.UsesBelow, VERT_TALLY,
    K, OUTPUT, RES1, SKIPR]

private theorem checkNodup_usesBelow : Cmd.UsesBelow checkNodup 32 := by
  simp [checkNodup, readNum, cSkip, cReject, Cmd.UsesBelow, Op.UsesBelow,
    VERT_STREAM, VERT_TALLY, OUTPUT, IDX1, IDX2, IDX3, VSCAN, VSCAN2, HEAD,
    INBLK, VALA, VALB, RES1, RES2, SKIPR]

private theorem checkClique_usesBelow : Cmd.UsesBelow checkClique 32 := by
  simp [checkClique, readNum, memberEdge, cSkip, cReject, Cmd.UsesBelow,
    Op.UsesBelow, VERT_STREAM, VERT_TALLY, EDGE_STREAM, EDGE_TALLY, OUTPUT,
    IDX1, IDX2, IDX3, IDX4, VSCAN, VSCAN2, ESCAN2, HEAD, INBLK, VALA, VALB,
    VALC, VALD, RES1, RES2, FOUND, SKIPR]

/-- Every register the verifier touches is `< 32` (assembled from the per-check
helpers). -/
theorem cliqueRelCmd_usesBelow : Cmd.UsesBelow cliqueRelCmd 32 := by
  refine ⟨?_, checkWf_usesBelow, checkOfType_usesBelow, checkLen_usesBelow,
    checkNodup_usesBelow, checkClique_usesBelow⟩
  show OUTPUT < 32
  decide

/-- The verifier is `consLen`-free (it uses no `consLen` op). -/
theorem cliqueRelCmd_noConsLen : Cmd.NoConsLen cliqueRelCmd := by
  simp only [cliqueRelCmd, checkWf, checkOfType, checkLen, checkNodup,
    checkClique, memberEdge, readNum, ltBit, cSkip, cReject,
    Cmd.NoConsLen, Op.NotConsLen]
  trivial

/-- Op-supportedness (Route A): the verifier uses only proven ops (it is
`takeAt`/`dropAt`/`consLen`-free), so its `compileOp_sound_physical_residue`
discharge is axiom-clean. -/
theorem cliqueRelCmd_allOpsSupported : Cmd.AllOpsSupported cliqueRelCmd := by
  simp only [cliqueRelCmd, checkWf, checkOfType, checkLen, checkNodup,
    checkClique, memberEdge, readNum, ltBit, cSkip, cReject,
    Cmd.AllOpsSupported, Op.IsSupported]
  trivial

/-! ### Leaf run-lemmas for the verifier checks (top-down Task 1)

The reusable per-gadget correctness contracts the per-check loop invariants
consume. Built bottom-up; `ltBit_run` (the novel unary-`<` gadget) first, since
its design carried the most risk. -/

/-- `(replicate n 1).tail = replicate (n-1) 1` (the loop step of `ltBit`'s
drain). -/
private theorem tail_replicate_one (n : Nat) :
    (List.replicate n (1 : Nat)).tail = List.replicate (n - 1) 1 := by
  cases n with
  | zero => rfl
  | succ m => rfl

/-- `(replicate n 1).isEmpty = decide (n = 0)` (the verdict read of `ltBit`). -/
private theorem isEmpty_replicate_one (n : Nat) :
    (List.replicate n (1 : Nat)).isEmpty = decide (n = 0) := by
  cases n with
  | zero => rfl
  | succ m => rfl

/-- **The unary strict-less-than gadget is correct.** If `A` holds `replicate a 1`
and `B` holds `replicate b 1`, and the scratch register `LT_B`, the loop counter
`idx` and the output `dst` are disjoint from the operands, then `ltBit dst A B
idx` writes `[if a < b then 1 else 0]` to `dst` and leaves every register outside
`{LT_B, idx, dst}` untouched.

The loop drains `LT_B` (a copy of `B`) once per cell of `A` (`a` iterations);
after the loop `LT_B = replicate (b − a) 1`, non-empty iff `b > a`. -/
theorem ltBit_run (st : State) (a b : Nat) (dst A B idx : Var)
    (hA : State.get st A = List.replicate a 1)
    (hB : State.get st B = List.replicate b 1)
    (hALT : A ≠ LT_B) (hidxLT : idx ≠ LT_B) :
    State.get ((ltBit dst A B idx).eval st) dst = [if a < b then 1 else 0]
    ∧ (∀ r : Var, r ≠ LT_B → r ≠ idx → r ≠ dst →
        State.get ((ltBit dst A B idx).eval st) r = State.get st r) := by
  -- Phase 1 — the copy `LT_B := B`.
  have hcopy : (Cmd.op (.copy LT_B B)).eval st = State.set st LT_B (List.replicate b 1) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hB]
  -- Unfold `ltBit` into `loop ;; nonEmpty` over the post-copy state `st1`.
  have heval : (ltBit dst A B idx).eval st
      = (Cmd.op (.nonEmpty dst LT_B)).eval
          ((Cmd.forBnd idx A (Cmd.op (.tail LT_B LT_B))).eval
            (State.set st LT_B (List.replicate b 1))) := by
    simp only [ltBit]; rw [Cmd.eval_seq, Cmd.eval_seq, hcopy]
  rw [heval]
  -- The loop is a `foldlState` over `List.range a` (the bound `A`'s length).
  rw [Cmd.eval_forBnd]
  have hAlen : (State.get (State.set st LT_B (List.replicate b 1)) A).length = a := by
    rw [State.get_set_ne _ _ _ _ hALT, hA, List.length_replicate]
  rw [hAlen]
  -- Loop invariant: after `i` iterations `LT_B = replicate (b − i) 1`, and every
  -- register outside `{LT_B, idx}` is unchanged from the post-copy state.
  obtain ⟨hLT2, hfr2⟩ :
      State.get (Cmd.foldlState (Cmd.op (.tail LT_B LT_B)) idx (List.range a)
          (State.set st LT_B (List.replicate b 1))) LT_B = List.replicate (b - a) 1
      ∧ (∀ r : Var, r ≠ LT_B → r ≠ idx →
          State.get (Cmd.foldlState (Cmd.op (.tail LT_B LT_B)) idx (List.range a)
            (State.set st LT_B (List.replicate b 1))) r
            = State.get (State.set st LT_B (List.replicate b 1)) r) := by
    refine Cmd.foldlState_range_induct (Cmd.op (.tail LT_B LT_B)) idx a
      (State.set st LT_B (List.replicate b 1))
      (fun i s => State.get s LT_B = List.replicate (b - i) 1
        ∧ ∀ r : Var, r ≠ LT_B → r ≠ idx →
            State.get s r = State.get (State.set st LT_B (List.replicate b 1)) r)
      ⟨by rw [State.get_set_eq, Nat.sub_zero], fun _ _ _ => rfl⟩ ?_
    intro i s _ hM
    obtain ⟨hLT, hfr⟩ := hM
    refine ⟨?_, ?_⟩
    · rw [Cmd.eval_op]; simp only [Op.eval]
      rw [State.get_set_eq, State.get_set_ne _ _ _ _ (Ne.symm hidxLT), hLT,
        tail_replicate_one, Nat.sub_sub]
    · intro r hrLT hridx
      rw [Cmd.eval_op]; simp only [Op.eval]
      rw [State.get_set_ne _ _ _ _ hrLT, State.get_set_ne _ _ _ _ hridx]
      exact hfr r hrLT hridx
  -- Phase 3 — read the verdict with `nonEmpty dst LT_B`.
  refine ⟨?_, ?_⟩
  · rw [Cmd.eval_op]
    simp only [Op.eval, State.get_set_eq, hLT2, isEmpty_replicate_one,
      decide_eq_true_eq]
    by_cases hab : a < b
    · rw [if_neg (show ¬ (b - a = 0) by omega), if_pos hab]
    · rw [if_pos (show b - a = 0 by omega), if_neg hab]
  · intro r hrLT hridx hrdst
    rw [Cmd.eval_op]; simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ hrdst, hfr2 r hrLT hridx,
      State.get_set_ne _ _ _ _ hrLT]

/-! ### `readNum`: the unary-block reader (keystone leaf, used by all 5 checks)

`readNum dst stream idx` reads one terminated unary block `replicate v 1 ++ [0]`
off the front of `stream` into `dst` (as `replicate v 1`), consuming the block and
its terminator from `stream`. The structure mirrors the PROVEN
`EvalCnfCmd.varExtractBody` loop (`LVInv`/`LVInv_step`/`processOneLiteral_main`),
generalised so `dst`/`stream`/`idx` are *parameters* — hence the explicit
register-distinctness hypotheses (the EvalCnf proof used `by decide` on fixed
register `def`s). Callers discharge them by `decide` on the concrete registers
(`dst ∈ {17..20}`, `stream ∈ {11..14}`, `idx ∈ {8,9,10}`, `HEAD = 15`,
`INBLK = 16`, `SKIPR = 26` pairwise distinct). -/

private theorem cSkip_eval (s : State) : cSkip.eval s = s.set SKIPR [1] := by
  show ((Cmd.op (.clear SKIPR)) ;; Cmd.op (.appendOne SKIPR)).eval s = _
  rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
  simp only [Op.eval, State.get_set_eq, List.nil_append, State.set_set]

private theorem cSkip_cost (s : State) : cSkip.cost s = 3 := by
  show ((Cmd.op (.clear SKIPR)) ;; Cmd.op (.appendOne SKIPR)).cost s = _
  rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]; rfl

private theorem replicate_one_snoc (n : Nat) :
    List.replicate n (1 : Nat) ++ [1] = List.replicate (n + 1) 1 :=
  List.replicate_succ'.symm

private theorem replicate_one_eq_iff {a b : Nat} :
    (List.replicate a (1 : Nat) = List.replicate b 1) ↔ a = b := by
  constructor
  · intro h; have := congrArg List.length h; simpa using this
  · rintro rfl; rfl

/-- `cReject` sets `OUTPUT := [0]` (and touches nothing else). -/
private theorem cReject_eval (s : State) : cReject.eval s = s.set OUTPUT [0] := by
  show ((Cmd.op (.clear OUTPUT)) ;; Cmd.op (.appendZero OUTPUT)).eval s = _
  rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
  simp only [Op.eval, State.get_set_eq, List.nil_append, State.set_set]

private theorem cReject_cost (s : State) : cReject.cost s = 3 := by
  show ((Cmd.op (.clear OUTPUT)) ;; Cmd.op (.appendZero OUTPUT)).cost s = _
  rw [Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]; rfl

/-- The `readNum` loop invariant (cf. `EvalCnfCmd.LVInv`). Through iteration `v`
the loop consumes the unary block (one cell/iteration) into `dst`; at iteration
`v` it consumes the `0` terminator and clears `INBLK`; afterwards it idles. The
frame is relative to `st`, the loop-entry (post-init) state. -/
private def RNInv (v : Nat) (rest : List Nat) (dst stream idx : Var) (st : State)
    (i : Nat) (s : State) : Prop :=
  (if i ≤ v then
    s.get INBLK = [1] ∧ s.get dst = List.replicate i 1
      ∧ s.get stream = List.replicate (v - i) 1 ++ 0 :: rest
  else
    s.get INBLK = [] ∧ s.get dst = List.replicate v 1
      ∧ s.get stream = rest)
  ∧ ∀ r : Var, r ≠ stream → r ≠ dst → r ≠ INBLK → r ≠ HEAD → r ≠ SKIPR →
      r ≠ idx → s.get r = st.get r

/-- The `readNum` body shape (the `forBnd` iteration body). -/
private def readNumBody (dst stream : Var) : Cmd :=
  Cmd.ifBit INBLK
    (Cmd.op (.head HEAD stream) ;;
     Cmd.op (.tail stream stream) ;;
     Cmd.ifBit HEAD (Cmd.op (.appendOne dst)) (Cmd.op (.clear INBLK)))
    cSkip

private theorem readNum_step (v : Nat) (rest : List Nat) (dst stream idx : Var)
    (st : State)
    (hsd : stream ≠ dst) (hsi : stream ≠ idx) (hdi : dst ≠ idx)
    (hsHead : stream ≠ HEAD) (hsInbk : stream ≠ INBLK) (hsSkip : stream ≠ SKIPR)
    (hdHead : dst ≠ HEAD) (hdInbk : dst ≠ INBLK) (hdSkip : dst ≠ SKIPR)
    (hiHead : idx ≠ HEAD) (hiInbk : idx ≠ INBLK) (hiSkip : idx ≠ SKIPR)
    (i : Nat) (s : State) (h : RNInv v rest dst stream idx st i s) :
    RNInv v rest dst stream idx st (i + 1)
      ((readNumBody dst stream).eval (s.set idx (List.replicate i 1))) := by
  obtain ⟨hphase, hframe⟩ := h
  by_cases hiv : i ≤ v
  · rw [if_pos hiv] at hphase
    obtain ⟨hIB, hDS, hCS⟩ := hphase
    have hIB' : (s.set idx (List.replicate i 1)).get INBLK = [1] := by
      rw [State.get_set_ne _ _ _ _ hiInbk.symm]; exact hIB
    have hCS' : (s.set idx (List.replicate i 1)).get stream
        = List.replicate (v - i) 1 ++ 0 :: rest := by
      rw [State.get_set_ne _ _ _ _ hsi]; exact hCS
    have hDS' : (s.set idx (List.replicate i 1)).get dst
        = List.replicate i 1 := by
      rw [State.get_set_ne _ _ _ _ hdi]; exact hDS
    have heval : (readNumBody dst stream).eval (s.set idx (List.replicate i 1))
        = (Cmd.op (.head HEAD stream) ;;
           Cmd.op (.tail stream stream) ;;
           Cmd.ifBit HEAD (Cmd.op (.appendOne dst))
             (Cmd.op (.clear INBLK))).eval
            (s.set idx (List.replicate i 1)) := by
      show (Cmd.ifBit INBLK _ _).eval _ = _
      rw [Cmd.eval_ifBit_true _ _ _ _ hIB']
    by_cases hiv2 : i < v
    · -- interior `1` cell of the unary block
      have hsplit : List.replicate (v - i) (1 : Nat) ++ 0 :: rest
          = 1 :: (List.replicate (v - (i + 1)) 1 ++ 0 :: rest) := by
        have hvi : v - i = (v - (i + 1)) + 1 := by omega
        rw [hvi, List.replicate_succ, List.cons_append]
      rw [hsplit] at hCS'
      have e1 : (Cmd.op (.head HEAD stream)).eval
          (s.set idx (List.replicate i 1))
          = (s.set idx (List.replicate i 1)).set HEAD [1] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hCS']
      have e2 : (Cmd.op (.tail stream stream)).eval
          ((s.set idx (List.replicate i 1)).set HEAD [1])
          = ((s.set idx (List.replicate i 1)).set HEAD [1]).set
              stream (List.replicate (v - (i + 1)) 1 ++ 0 :: rest) := by
        rw [Cmd.eval_op]; simp only [Op.eval]
        rw [State.get_set_ne _ _ _ _ hsHead, hCS', List.tail_cons]
      have hHC : (((s.set idx (List.replicate i 1)).set HEAD [1]).set
          stream (List.replicate (v - (i + 1)) 1 ++ 0 :: rest)).get HEAD
          = [1] := by
        rw [State.get_set_ne _ _ _ _ hsHead.symm, State.get_set_eq]
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_ifBit_true _ _ _ _ hHC,
        Cmd.eval_op] at heval
      simp only [Op.eval] at heval
      rw [State.get_set_ne _ _ _ _ hsd.symm,
        State.get_set_ne _ _ _ _ hdHead,
        State.get_set_ne _ _ _ _ hdi, hDS, replicate_one_snoc] at heval
      rw [heval]
      constructor
      · rw [if_pos (by omega : i + 1 ≤ v)]
        refine ⟨?_, ?_, ?_⟩
        · rw [State.get_set_ne _ _ _ _ hdInbk.symm,
            State.get_set_ne _ _ _ _ hsInbk.symm,
            State.get_set_ne _ _ _ _ (by decide : (INBLK : Var) ≠ HEAD),
            State.get_set_ne _ _ _ _ hiInbk.symm]
          exact hIB
        · rw [State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ hsd, State.get_set_eq]
      · intro r hrs hrd hri hrh hrsk hridx
        rw [State.get_set_ne _ _ _ _ hrd, State.get_set_ne _ _ _ _ hrs,
          State.get_set_ne _ _ _ _ hrh, State.get_set_ne _ _ _ _ hridx]
        exact hframe r hrs hrd hri hrh hrsk hridx
    · -- the `0` terminator (`i = v`)
      have hiv3 : i = v := by omega
      subst hiv3
      have hsplit : List.replicate (i - i) (1 : Nat) ++ 0 :: rest
          = 0 :: rest := by
        rw [Nat.sub_self]; rfl
      rw [hsplit] at hCS'
      have e1 : (Cmd.op (.head HEAD stream)).eval
          (s.set idx (List.replicate i 1))
          = (s.set idx (List.replicate i 1)).set HEAD [0] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hCS']
      have e2 : (Cmd.op (.tail stream stream)).eval
          ((s.set idx (List.replicate i 1)).set HEAD [0])
          = ((s.set idx (List.replicate i 1)).set HEAD [0]).set
              stream rest := by
        rw [Cmd.eval_op]; simp only [Op.eval]
        rw [State.get_set_ne _ _ _ _ hsHead, hCS', List.tail_cons]
      have hHC : (((s.set idx (List.replicate i 1)).set HEAD [0]).set
          stream rest).get HEAD ≠ [1] := by
        rw [State.get_set_ne _ _ _ _ hsHead.symm, State.get_set_eq]; decide
      rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_ifBit_false _ _ _ _ hHC,
        Cmd.eval_op] at heval
      simp only [Op.eval] at heval
      rw [heval]
      constructor
      · rw [if_neg (by omega : ¬ i + 1 ≤ i)]
        refine ⟨?_, ?_, ?_⟩
        · rw [State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ hdInbk,
            State.get_set_ne _ _ _ _ hsd.symm,
            State.get_set_ne _ _ _ _ hdHead,
            State.get_set_ne _ _ _ _ hdi]
          exact hDS
        · rw [State.get_set_ne _ _ _ _ hsInbk, State.get_set_eq]
      · intro r hrs hrd hri hrh hrsk hridx
        rw [State.get_set_ne _ _ _ _ hri, State.get_set_ne _ _ _ _ hrs,
          State.get_set_ne _ _ _ _ hrh, State.get_set_ne _ _ _ _ hridx]
        exact hframe r hrs hrd hri hrh hrsk hridx
  · -- idle phase
    rw [if_neg hiv] at hphase
    obtain ⟨hIB, hDS, hCS⟩ := hphase
    have hIB' : (s.set idx (List.replicate i 1)).get INBLK ≠ [1] := by
      rw [State.get_set_ne _ _ _ _ hiInbk.symm, hIB]; decide
    have heval : (readNumBody dst stream).eval (s.set idx (List.replicate i 1))
        = (s.set idx (List.replicate i 1)).set SKIPR [1] := by
      show (Cmd.ifBit INBLK _ _).eval _ = _
      rw [Cmd.eval_ifBit_false _ _ _ _ hIB', cSkip_eval]
    rw [heval]
    constructor
    · rw [if_neg (by omega : ¬ i + 1 ≤ v)]
      refine ⟨?_, ?_, ?_⟩
      · rw [State.get_set_ne _ _ _ _ (by decide : (INBLK : Var) ≠ SKIPR),
          State.get_set_ne _ _ _ _ hiInbk.symm]
        exact hIB
      · rw [State.get_set_ne _ _ _ _ hdSkip,
          State.get_set_ne _ _ _ _ hdi]
        exact hDS
      · rw [State.get_set_ne _ _ _ _ hsSkip,
          State.get_set_ne _ _ _ _ hsi]
        exact hCS
    · intro r hrs hrd hri hrh hrsk hridx
      rw [State.get_set_ne _ _ _ _ hrsk, State.get_set_ne _ _ _ _ hridx]
      exact hframe r hrs hrd hri hrh hrsk hridx

/-- **The unary-block reader is correct.** With one terminated unary block
`replicate v 1 ++ [0] ++ rest` at the head of `stream`, `readNum dst stream idx`
writes `replicate v 1` into `dst`, advances `stream` past the block to `rest`, and
leaves every register outside `{stream, dst, INBLK, HEAD, SKIPR, idx}` untouched. -/
theorem readNum_run (st : State) (v : Nat) (rest : List Nat)
    (dst stream idx : Var)
    (hstream : st.get stream = List.replicate v 1 ++ 0 :: rest)
    (hsd : stream ≠ dst) (hsi : stream ≠ idx) (hdi : dst ≠ idx)
    (hsHead : stream ≠ HEAD) (hsInbk : stream ≠ INBLK) (hsSkip : stream ≠ SKIPR)
    (hdHead : dst ≠ HEAD) (hdInbk : dst ≠ INBLK) (hdSkip : dst ≠ SKIPR)
    (hiHead : idx ≠ HEAD) (hiInbk : idx ≠ INBLK) (hiSkip : idx ≠ SKIPR) :
    ((readNum dst stream idx).eval st).get dst = List.replicate v 1
    ∧ ((readNum dst stream idx).eval st).get stream = rest
    ∧ (∀ r : Var, r ≠ stream → r ≠ dst → r ≠ INBLK → r ≠ HEAD → r ≠ SKIPR →
        r ≠ idx → ((readNum dst stream idx).eval st).get r = st.get r) := by
  -- evaluate the `clear dst ;; clear INBLK ;; appendOne INBLK` init prefix
  have e1 : (Cmd.op (.clear dst)).eval st = st.set dst [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e2 : (Cmd.op (.clear INBLK)).eval (st.set dst [])
      = (st.set dst []).set INBLK [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e3 : (Cmd.op (.appendOne INBLK)).eval ((st.set dst []).set INBLK [])
      = ((st.set dst []).set INBLK []).set INBLK [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [State.get_set_eq, List.nil_append]
  have eP : (readNum dst stream idx).eval st
      = (Cmd.forBnd idx stream (readNumBody dst stream)).eval
          (((st.set dst []).set INBLK []).set INBLK [1]) := by
    show (Cmd.eval (_ ;; _ ;; _ ;; _) st) = _
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3]
    rfl
  have hslen : ((((st.set dst []).set INBLK []).set INBLK [1]).get stream).length
      = v + 1 + rest.length := by
    rw [State.get_set_ne _ _ _ _ hsInbk, State.get_set_ne _ _ _ _ hsInbk,
      State.get_set_ne _ _ _ _ hsd, hstream]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  have hbase : RNInv v rest dst stream idx
      (((st.set dst []).set INBLK []).set INBLK [1]) 0
      (((st.set dst []).set INBLK []).set INBLK [1]) := by
    refine ⟨?_, fun r _ _ _ _ _ _ => rfl⟩
    rw [if_pos (Nat.zero_le v)]
    refine ⟨?_, ?_, ?_⟩
    · rw [State.get_set_eq]
    · show _ = List.replicate 0 1
      rw [State.get_set_ne _ _ _ _ hdInbk, State.get_set_ne _ _ _ _ hdInbk,
        State.get_set_eq]
      rfl
    · rw [Nat.sub_zero, State.get_set_ne _ _ _ _ hsInbk,
        State.get_set_ne _ _ _ _ hsInbk, State.get_set_ne _ _ _ _ hsd, hstream]
  have hInv : RNInv v rest dst stream idx
      (((st.set dst []).set INBLK []).set INBLK [1]) (v + 1 + rest.length)
      ((readNum dst stream idx).eval st) := by
    rw [eP, Cmd.eval_forBnd, hslen]
    exact Cmd.foldlState_range_induct (readNumBody dst stream) idx
      (v + 1 + rest.length) (((st.set dst []).set INBLK []).set INBLK [1])
      (RNInv v rest dst stream idx (((st.set dst []).set INBLK []).set INBLK [1]))
      hbase
      (fun i s _ h => readNum_step v rest dst stream idx
        (((st.set dst []).set INBLK []).set INBLK [1])
        hsd hsi hdi hsHead hsInbk hsSkip hdHead hdInbk hdSkip
        hiHead hiInbk hiSkip i s h)
  obtain ⟨hphase, hframe⟩ := hInv
  rw [if_neg (by omega : ¬ (v + 1 + rest.length ≤ v))] at hphase
  obtain ⟨_, hDSfin, hSTfin⟩ := hphase
  refine ⟨hDSfin, hSTfin, ?_⟩
  intro r hrs hrd hri hrh hrsk hridx
  rw [hframe r hrs hrd hri hrh hrsk hridx,
    State.get_set_ne _ _ _ _ hri, State.get_set_ne _ _ _ _ hri,
    State.get_set_ne _ _ _ _ hrd]

/-! ### Per-check run-lemmas (AND-into-`OUTPUT`)

Each check ANDs its predicate into `OUTPUT`: starting from `OUTPUT = [if b then 1
else 0]`, after the check `OUTPUT = [if b && decide P then 1 else 0]` (the check
only ever *rejects*, never accepts), and the read-only input registers (1–6) are
preserved. The assembly (`cliqueRelCmd`) starts `OUTPUT = [1]` and chains them, so
the final bit is the conjunction of all five predicates = `cliqueRel`. -/

/-- **Check 3 — `l.length = k`.** The smallest check: one `eqBit` of the two
unary tallies, ANDed into `OUTPUT`. -/
theorem checkLen_run (st : State) (k llen : Nat) (b : Bool)
    (hVT : st.get VERT_TALLY = List.replicate llen 1)
    (hK : st.get K = List.replicate k 1)
    (hO : st.get OUTPUT = [if b then 1 else 0]) :
    (checkLen.eval st).get OUTPUT = [if b && decide (llen = k) then 1 else 0]
    ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ RES1 → r ≠ SKIPR →
        (checkLen.eval st).get r = st.get r) := by
  have heq : (if st.get VERT_TALLY = st.get K then ([1] : List Nat) else [0])
      = [if llen = k then 1 else 0] := by
    rw [hVT, hK]
    by_cases h : llen = k
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (by rw [replicate_one_eq_iff]; exact h), if_neg h]
  have he : checkLen.eval st
      = (Cmd.ifBit RES1 cSkip cReject).eval
          (st.set RES1 [if llen = k then 1 else 0]) := by
    show (Cmd.op (.eqBit RES1 VERT_TALLY K) ;; Cmd.ifBit RES1 cSkip cReject).eval st = _
    rw [Cmd.eval_seq, Cmd.eval_op]; simp only [Op.eval]; rw [heq]
  rw [he]
  by_cases hlk : llen = k
  · have hR : (st.set RES1 [if llen = k then 1 else 0]).get RES1 = [1] := by
      rw [State.get_set_eq, if_pos hlk]
    rw [Cmd.eval_ifBit_true _ _ _ _ hR, cSkip_eval]
    refine ⟨?_, ?_⟩
    · rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ SKIPR),
        State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ RES1), hO]
      simp [hlk]
    · intro r hrO hrR hrS
      rw [State.get_set_ne _ _ _ _ hrS, State.get_set_ne _ _ _ _ hrR]
  · have hR : (st.set RES1 [if llen = k then 1 else 0]).get RES1 ≠ [1] := by
      rw [State.get_set_eq, if_neg hlk]; decide
    rw [Cmd.eval_ifBit_false _ _ _ _ hR, cReject_eval]
    refine ⟨?_, ?_⟩
    · rw [State.get_set_eq]; simp [hlk]
    · intro r hrO hrR hrS
      rw [State.get_set_ne _ _ _ _ hrO, State.get_set_ne _ _ _ _ hrR]

/-- `Bool`-valued "every element `< numV`" (avoids the flaky `Decidable
(∀ x ∈ l, …)` instance; bridges to `list_ofFlatType` via `allLt_eq_true_iff`). -/
def allLt (numV : Nat) (l : List fvertex) : Bool := l.all (fun x => decide (x < numV))

theorem allLt_eq_true_iff (numV : Nat) (l : List fvertex) :
    allLt numV l = true ↔ list_ofFlatType numV l := by
  simp only [allLt, List.all_eq_true, decide_eq_true_eq, list_ofFlatType, ofFlatType]

/-- One element peeled off the front: `allLt` over `take (i+1)`. -/
private theorem allLt_take_succ (numV : Nat) (l : List fvertex) (i : Nat)
    (hi : i < l.length) :
    allLt numV (l.take (i + 1))
      = (allLt numV (l.take i) && decide (l[i]'hi < numV)) := by
  rw [allLt, allLt, List.take_succ_eq_append_getElem hi, List.all_append,
    List.all_cons, List.all_nil, Bool.and_true]

/-- `Bool`-valued "every edge endpoint `< numV`" (the `fgraph_wf` body). -/
def edgesWf (numV : Nat) (edges : List fedge) : Bool :=
  edges.all (fun e => decide (e.1 < numV) && decide (e.2 < numV))

theorem edgesWf_eq_true_iff (numV : Nat) (edges : List fedge) :
    edgesWf numV edges = true ↔ ∀ e ∈ edges, e.1 < numV ∧ e.2 < numV := by
  simp only [edgesWf, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]

private theorem edgesWf_take_succ (numV : Nat) (edges : List fedge) (i : Nat)
    (hi : i < edges.length) :
    edgesWf numV (edges.take (i + 1))
      = (edgesWf numV (edges.take i)
          && (decide ((edges[i]'hi).1 < numV) && decide ((edges[i]'hi).2 < numV))) := by
  rw [edgesWf, edgesWf, List.take_succ_eq_append_getElem hi, List.all_append,
    List.all_cons, List.all_nil, Bool.and_true]

/-- `ifBit RES1 (ifBit RES2 then cReject) cReject` only ever writes
`{SKIPR, OUTPUT}` (the nested "reject unless both bits set" guard). -/
private theorem ifReject2_frame (then2 : Cmd)
    (hthen2 : ∀ (u : State) (r : Var), r ≠ SKIPR → r ≠ OUTPUT →
      (then2.eval u).get r = u.get r)
    (t : State) (r : Var) (hrS : r ≠ SKIPR) (hrO : r ≠ OUTPUT) :
    ((Cmd.ifBit RES1 (Cmd.ifBit RES2 then2 cReject) cReject).eval t).get r
      = t.get r := by
  by_cases hb1 : t.get RES1 = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hb1]
    by_cases hb2 : t.get RES2 = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hb2]; exact hthen2 t r hrS hrO
    · rw [Cmd.eval_ifBit_false _ _ _ _ hb2, cReject_eval, State.get_set_ne _ _ _ _ hrO]
  · rw [Cmd.eval_ifBit_false _ _ _ _ hb1, cReject_eval, State.get_set_ne _ _ _ _ hrO]

/-- `ifBit RES1 cSkip cReject` only ever writes `{SKIPR, OUTPUT}`. -/
private theorem ifReject_frame (t : State) (r : Var) (hrS : r ≠ SKIPR)
    (hrO : r ≠ OUTPUT) :
    ((Cmd.ifBit RES1 cSkip cReject).eval t).get r = t.get r := by
  by_cases hb : t.get RES1 = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hb, cSkip_eval, State.get_set_ne _ _ _ _ hrS]
  · rw [Cmd.eval_ifBit_false _ _ _ _ hb, cReject_eval, State.get_set_ne _ _ _ _ hrO]

/-- The `checkOfType` outer-loop invariant: through iteration `i` the loop has
consumed `i` vertex blocks from `VSCAN` and ANDed each `< numV` test into
`OUTPUT`. The frame is relative to the loop-entry state `st`. -/
private def COInv (l : List fvertex) (numV : Nat) (b : Bool) (st : State)
    (i : Nat) (s : State) : Prop :=
  s.get VSCAN = encVerts (l.drop i)
  ∧ s.get OUTPUT = [if b && allLt numV (l.take i) then 1 else 0]
  ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ VSCAN → r ≠ VALA → r ≠ RES1 → r ≠ LT_B →
      r ≠ HEAD → r ≠ INBLK → r ≠ SKIPR → r ≠ IDX1 → r ≠ IDX2 → r ≠ IDX3 →
      s.get r = st.get r)

private theorem checkOfType_step (l : List fvertex) (numV : Nat) (b : Bool)
    (st : State) (hNUMV : st.get NUMV = List.replicate numV 1)
    (i : Nat) (s : State) (hi : i < l.length) (h : COInv l numV b st i s) :
    COInv l numV b st (i + 1)
      ((readNum VALA VSCAN IDX2 ;;
        ltBit RES1 VALA NUMV IDX3 ;;
        Cmd.ifBit RES1 cSkip cReject).eval (s.set IDX1 (List.replicate i 1))) := by
  obtain ⟨hVSCAN, hOUT, hframe⟩ := h
  -- expose the body as `ifBit (ltBit (readNum …))` (avoid whnf on the `;;` chain)
  rw [show (readNum VALA VSCAN IDX2 ;; ltBit RES1 VALA NUMV IDX3 ;;
        Cmd.ifBit RES1 cSkip cReject).eval (s.set IDX1 (List.replicate i 1))
      = (Cmd.ifBit RES1 cSkip cReject).eval
          ((ltBit RES1 VALA NUMV IDX3).eval
            ((readNum VALA VSCAN IDX2).eval (s.set IDX1 (List.replicate i 1))))
      from by rw [Cmd.eval_seq, Cmd.eval_seq]]
  -- stream shape at the head of `VSCAN`
  have hVS : (s.set IDX1 (List.replicate i 1)).get VSCAN
      = List.replicate (l[i]'hi) 1 ++ 0 :: encVerts (l.drop (i + 1)) := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VSCAN : Var) ≠ IDX1), hVSCAN,
      List.drop_eq_getElem_cons hi, encVerts_cons]
  -- run `readNum VALA VSCAN IDX2`
  obtain ⟨hVALA, hVS2, hRNframe⟩ := readNum_run (s.set IDX1 (List.replicate i 1))
    (l[i]'hi) (encVerts (l.drop (i + 1))) VALA VSCAN IDX2 hVS
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- `NUMV` survives `readNum`
  have hNUMV1 : ((readNum VALA VSCAN IDX2).eval
      (s.set IDX1 (List.replicate i 1))).get NUMV = List.replicate numV 1 := by
    rw [hRNframe NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      State.get_set_ne _ _ _ _ (by decide : (NUMV : Var) ≠ IDX1),
      hframe NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hNUMV]
  -- run `ltBit RES1 VALA NUMV IDX3`
  obtain ⟨hRES1, hLTframe⟩ := ltBit_run
    ((readNum VALA VSCAN IDX2).eval (s.set IDX1 (List.replicate i 1)))
    (l[i]'hi) numV RES1 VALA NUMV IDX3 hVALA hNUMV1 (by decide) (by decide)
  -- the post-`ltBit` state, abbreviated
  set s2 := (ltBit RES1 VALA NUMV IDX3).eval
    ((readNum VALA VSCAN IDX2).eval (s.set IDX1 (List.replicate i 1))) with hs2
  -- `VSCAN` and `OUTPUT` after `ltBit`
  have hVS3 : s2.get VSCAN = encVerts (l.drop (i + 1)) := by
    rw [hLTframe VSCAN (by decide) (by decide) (by decide), hVS2]
  have hOUT3 : s2.get OUTPUT
      = [if b && allLt numV (l.take i) then 1 else 0] := by
    rw [hLTframe OUTPUT (by decide) (by decide) (by decide),
      hRNframe OUTPUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ IDX1), hOUT]
  refine ⟨?_, ?_, ?_⟩
  · -- VSCAN
    rw [ifReject_frame _ _ (by decide) (by decide), hVS3]
  · -- OUTPUT
    by_cases hlt : l[i]'hi < numV
    · have hR : s2.get RES1 = [1] := by rw [hRES1, if_pos hlt]
      rw [Cmd.eval_ifBit_true _ _ _ _ hR, cSkip_eval,
        State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ SKIPR), hOUT3,
        allLt_take_succ numV l i hi]
      have hd : decide (l[i]'hi < numV) = true := by
        simp only [decide_eq_true_eq]; exact hlt
      rw [hd, Bool.and_true]
    · have hR : s2.get RES1 ≠ [1] := by rw [hRES1, if_neg hlt]; decide
      rw [Cmd.eval_ifBit_false _ _ _ _ hR, cReject_eval, State.get_set_eq,
        allLt_take_succ numV l i hi]
      have hd : decide (l[i]'hi < numV) = false := by
        simp only [decide_eq_false_iff_not]; exact hlt
      simp [hd]
  · -- frame
    intro r hrO hrV hrVA hrR hrLT hrH hrI hrS hr1 hr2 hr3
    rw [ifReject_frame _ _ hrS hrO, hLTframe r hrLT hr3 hrR,
      hRNframe r hrV hrVA hrI hrH hrS hr2,
      State.get_set_ne _ _ _ _ hr1,
      hframe r hrO hrV hrVA hrR hrLT hrH hrI hrS hr1 hr2 hr3]

/-- **Check 2 — `list_ofFlatType numV l`** (every vertex `< numV`), ANDed into
`OUTPUT`. The representative single-loop check: an outer `forBnd` over the vertex
tally whose body `readNum`s one vertex and `ltBit`s it against `NUMV`. -/
theorem checkOfType_run (st : State) (l : List fvertex) (numV : Nat) (b : Bool)
    (hVS : st.get VERT_STREAM = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hNUMV : st.get NUMV = List.replicate numV 1)
    (hO : st.get OUTPUT = [if b then 1 else 0]) :
    (checkOfType.eval st).get OUTPUT
        = [if b && allLt numV l then 1 else 0]
    ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ VSCAN → r ≠ VALA → r ≠ RES1 → r ≠ LT_B →
        r ≠ HEAD → r ≠ INBLK → r ≠ SKIPR → r ≠ IDX1 → r ≠ IDX2 → r ≠ IDX3 →
        (checkOfType.eval st).get r = st.get r) := by
  -- init: `copy VSCAN VERT_STREAM`
  have eInit : (Cmd.op (.copy VSCAN VERT_STREAM)).eval st
      = st.set VSCAN (encVerts l) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVS]
  have eP : checkOfType.eval st
      = (Cmd.forBnd IDX1 VERT_TALLY
          (readNum VALA VSCAN IDX2 ;;
           ltBit RES1 VALA NUMV IDX3 ;;
           Cmd.ifBit RES1 cSkip cReject)).eval (st.set VSCAN (encVerts l)) := by
    show (Cmd.op (.copy VSCAN VERT_STREAM) ;; _).eval st = _
    rw [Cmd.eval_seq, eInit]
  have hblen : ((st.set VSCAN (encVerts l)).get VERT_TALLY).length = l.length := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ VSCAN), hVT,
      List.length_replicate]
  have hbase : COInv l numV b (st.set VSCAN (encVerts l)) 0
      (st.set VSCAN (encVerts l)) := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [State.get_set_eq, List.drop_zero]
    · rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ VSCAN), hO,
        List.take_zero]
      simp only [allLt, List.all_nil, Bool.and_true]
  have hNUMV0 : (st.set VSCAN (encVerts l)).get NUMV = List.replicate numV 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (NUMV : Var) ≠ VSCAN), hNUMV]
  have hInv : COInv l numV b (st.set VSCAN (encVerts l)) l.length
      (checkOfType.eval st) := by
    rw [eP, Cmd.eval_forBnd, hblen]
    exact Cmd.foldlState_range_induct _ IDX1 l.length (st.set VSCAN (encVerts l))
      (COInv l numV b (st.set VSCAN (encVerts l))) hbase
      (fun i s hi h => checkOfType_step l numV b (st.set VSCAN (encVerts l))
        hNUMV0 i s hi h)
  obtain ⟨_, hOUTfin, hframefin⟩ := hInv
  refine ⟨?_, ?_⟩
  · rw [hOUTfin, List.take_length]
  · intro r hrO hrV hrVA hrR hrLT hrH hrI hrS hr1 hr2 hr3
    rw [hframefin r hrO hrV hrVA hrR hrLT hrH hrI hrS hr1 hr2 hr3,
      State.get_set_ne _ _ _ _ hrV]

/-- The `checkWf` outer-loop invariant: through iteration `i` the loop has
consumed `i` edges from `ESCAN` and ANDed each "both endpoints `< numV`" test
into `OUTPUT`. Frame relative to the loop-entry state `st`. -/
private def CWfInv (edges : List fedge) (numV : Nat) (b : Bool) (st : State)
    (i : Nat) (s : State) : Prop :=
  s.get ESCAN = encEdges (edges.drop i)
  ∧ s.get OUTPUT = [if b && edgesWf numV (edges.take i) then 1 else 0]
  ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ ESCAN → r ≠ VALA → r ≠ VALB → r ≠ RES1 →
      r ≠ RES2 → r ≠ LT_B → r ≠ HEAD → r ≠ INBLK → r ≠ SKIPR → r ≠ IDX1 →
      r ≠ IDX2 → r ≠ IDX3 → s.get r = st.get r)

private theorem checkWf_step (edges : List fedge) (numV : Nat) (b : Bool)
    (st : State) (hNUMV : st.get NUMV = List.replicate numV 1)
    (i : Nat) (s : State) (hi : i < edges.length) (h : CWfInv edges numV b st i s) :
    CWfInv edges numV b st (i + 1)
      ((readNum VALA ESCAN IDX2 ;;
        readNum VALB ESCAN IDX2 ;;
        ltBit RES1 VALA NUMV IDX3 ;;
        ltBit RES2 VALB NUMV IDX3 ;;
        Cmd.ifBit RES1 (Cmd.ifBit RES2 cSkip cReject) cReject).eval
          (s.set IDX1 (List.replicate i 1))) := by
  obtain ⟨hESCAN, hOUT, hframe⟩ := h
  rw [show (readNum VALA ESCAN IDX2 ;; readNum VALB ESCAN IDX2 ;;
        ltBit RES1 VALA NUMV IDX3 ;; ltBit RES2 VALB NUMV IDX3 ;;
        Cmd.ifBit RES1 (Cmd.ifBit RES2 cSkip cReject) cReject).eval
          (s.set IDX1 (List.replicate i 1))
      = (Cmd.ifBit RES1 (Cmd.ifBit RES2 cSkip cReject) cReject).eval
          ((ltBit RES2 VALB NUMV IDX3).eval
            ((ltBit RES1 VALA NUMV IDX3).eval
              ((readNum VALB ESCAN IDX2).eval
                ((readNum VALA ESCAN IDX2).eval (s.set IDX1 (List.replicate i 1))))))
      from by rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]]
  -- the edge at the head of `ESCAN`
  have hESCAN_in : (s.set IDX1 (List.replicate i 1)).get ESCAN
      = List.replicate (edges[i]'hi).1 1 ++ 0 ::
          (List.replicate (edges[i]'hi).2 1 ++ 0 :: encEdges (edges.drop (i + 1))) := by
    rw [State.get_set_ne _ _ _ _ (by decide : (ESCAN : Var) ≠ IDX1), hESCAN,
      List.drop_eq_getElem_cons hi, encEdges_cons]
  -- rn1: read `e.1` into `VALA`
  obtain ⟨hVALA, hESCAN1, hRN1frame⟩ := readNum_run (s.set IDX1 (List.replicate i 1))
    (edges[i]'hi).1
    (List.replicate (edges[i]'hi).2 1 ++ 0 :: encEdges (edges.drop (i + 1)))
    VALA ESCAN IDX2 hESCAN_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALA ESCAN IDX2).eval (s.set IDX1 (List.replicate i 1)) with hs1
  -- rn2: read `e.2` into `VALB`
  obtain ⟨hVALB, hESCAN2, hRN2frame⟩ := readNum_run s1
    (edges[i]'hi).2 (encEdges (edges.drop (i + 1)))
    VALB ESCAN IDX2 hESCAN1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s2 := (readNum VALB ESCAN IDX2).eval s1 with hs2
  have hVALA2 : s2.get VALA = List.replicate (edges[i]'hi).1 1 := by
    rw [hRN2frame VALA (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hVALA]
  have hNUMV2 : s2.get NUMV = List.replicate numV 1 := by
    rw [hRN2frame NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      hRN1frame NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      State.get_set_ne _ _ _ _ (by decide : (NUMV : Var) ≠ IDX1),
      hframe NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hNUMV]
  -- ltBit1: `RES1 := [e.1 < numV]`
  obtain ⟨hRES1, hLT1frame⟩ := ltBit_run s2 (edges[i]'hi).1 numV RES1 VALA NUMV IDX3
    hVALA2 hNUMV2 (by decide) (by decide)
  set s3 := (ltBit RES1 VALA NUMV IDX3).eval s2 with hs3
  have hVALB3 : s3.get VALB = List.replicate (edges[i]'hi).2 1 := by
    rw [hLT1frame VALB (by decide) (by decide) (by decide), hVALB]
  have hNUMV3 : s3.get NUMV = List.replicate numV 1 := by
    rw [hLT1frame NUMV (by decide) (by decide) (by decide), hNUMV2]
  -- ltBit2: `RES2 := [e.2 < numV]`
  obtain ⟨hRES2, hLT2frame⟩ := ltBit_run s3 (edges[i]'hi).2 numV RES2 VALB NUMV IDX3
    hVALB3 hNUMV3 (by decide) (by decide)
  set s4 := (ltBit RES2 VALB NUMV IDX3).eval s3 with hs4
  have hRES1' : s4.get RES1 = [if (edges[i]'hi).1 < numV then 1 else 0] := by
    rw [hLT2frame RES1 (by decide) (by decide) (by decide), hRES1]
  have hESCAN4 : s4.get ESCAN = encEdges (edges.drop (i + 1)) := by
    rw [hLT2frame ESCAN (by decide) (by decide) (by decide),
      hLT1frame ESCAN (by decide) (by decide) (by decide), hESCAN2]
  have hOUT4 : s4.get OUTPUT = [if b && edgesWf numV (edges.take i) then 1 else 0] := by
    rw [hLT2frame OUTPUT (by decide) (by decide) (by decide),
      hLT1frame OUTPUT (by decide) (by decide) (by decide),
      hRN2frame OUTPUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      hRN1frame OUTPUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ IDX1), hOUT]
  have hcSkipFrame : ∀ (u : State) (r : Var), r ≠ SKIPR → r ≠ OUTPUT →
      (cSkip.eval u).get r = u.get r := by
    intro u r hrS _; rw [cSkip_eval, State.get_set_ne _ _ _ _ hrS]
  refine ⟨?_, ?_, ?_⟩
  · -- ESCAN
    rw [ifReject2_frame cSkip hcSkipFrame _ _ (by decide) (by decide), hESCAN4]
  · -- OUTPUT
    rw [edgesWf_take_succ numV edges i hi]
    by_cases h1 : (edges[i]'hi).1 < numV
    · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hRES1', if_pos h1])]
      by_cases h2 : (edges[i]'hi).2 < numV
      · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hRES2, if_pos h2]), cSkip_eval,
          State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ SKIPR), hOUT4]
        have hd1 : decide ((edges[i]'hi).1 < numV) = true := by
          simp only [decide_eq_true_eq]; exact h1
        have hd2 : decide ((edges[i]'hi).2 < numV) = true := by
          simp only [decide_eq_true_eq]; exact h2
        rw [hd1, hd2, Bool.and_true, Bool.and_true]
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hRES2, if_neg h2]; decide),
          cReject_eval, State.get_set_eq]
        have hd2 : decide ((edges[i]'hi).2 < numV) = false := by
          simp only [decide_eq_false_iff_not]; exact h2
        simp [hd2]
    · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hRES1', if_neg h1]; decide),
        cReject_eval, State.get_set_eq]
      have hd1 : decide ((edges[i]'hi).1 < numV) = false := by
        simp only [decide_eq_false_iff_not]; exact h1
      simp [hd1]
  · -- frame
    intro r hrO hrE hrVA hrVB hrR1 hrR2 hrLT hrH hrI hrS hr1 hr2 hr3
    rw [ifReject2_frame cSkip hcSkipFrame _ _ hrS hrO,
      hLT2frame r hrLT hr3 hrR2, hLT1frame r hrLT hr3 hrR1,
      hRN2frame r hrE hrVB hrI hrH hrS hr2,
      hRN1frame r hrE hrVA hrI hrH hrS hr2,
      State.get_set_ne _ _ _ _ hr1,
      hframe r hrO hrE hrVA hrVB hrR1 hrR2 hrLT hrH hrI hrS hr1 hr2 hr3]

/-- **Check 1 — `fgraph_wf G`** (every edge endpoint `< numV`), ANDed into
`OUTPUT`. Outer `forBnd` over the edge tally; the body `readNum`s both unary
endpoints and `ltBit`s each against `NUMV`, rejecting unless both pass. -/
theorem checkWf_run (st : State) (edges : List fedge) (numV : Nat) (b : Bool)
    (hES : st.get EDGE_STREAM = encEdges edges)
    (hET : st.get EDGE_TALLY = List.replicate edges.length 1)
    (hNUMV : st.get NUMV = List.replicate numV 1)
    (hO : st.get OUTPUT = [if b then 1 else 0]) :
    (checkWf.eval st).get OUTPUT = [if b && edgesWf numV edges then 1 else 0]
    ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ ESCAN → r ≠ VALA → r ≠ VALB → r ≠ RES1 →
        r ≠ RES2 → r ≠ LT_B → r ≠ HEAD → r ≠ INBLK → r ≠ SKIPR → r ≠ IDX1 →
        r ≠ IDX2 → r ≠ IDX3 → (checkWf.eval st).get r = st.get r) := by
  have eInit : (Cmd.op (.copy ESCAN EDGE_STREAM)).eval st
      = st.set ESCAN (encEdges edges) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hES]
  have eP : checkWf.eval st
      = (Cmd.forBnd IDX1 EDGE_TALLY
          (readNum VALA ESCAN IDX2 ;; readNum VALB ESCAN IDX2 ;;
           ltBit RES1 VALA NUMV IDX3 ;; ltBit RES2 VALB NUMV IDX3 ;;
           Cmd.ifBit RES1 (Cmd.ifBit RES2 cSkip cReject) cReject)).eval
          (st.set ESCAN (encEdges edges)) := by
    show (Cmd.op (.copy ESCAN EDGE_STREAM) ;; _).eval st = _
    rw [Cmd.eval_seq, eInit]
  have hblen : ((st.set ESCAN (encEdges edges)).get EDGE_TALLY).length
      = edges.length := by
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ ESCAN), hET,
      List.length_replicate]
  have hbase : CWfInv edges numV b (st.set ESCAN (encEdges edges)) 0
      (st.set ESCAN (encEdges edges)) := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [State.get_set_eq, List.drop_zero]
    · rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ ESCAN), hO,
        List.take_zero]
      simp only [edgesWf, List.all_nil, Bool.and_true]
  have hNUMV0 : (st.set ESCAN (encEdges edges)).get NUMV = List.replicate numV 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (NUMV : Var) ≠ ESCAN), hNUMV]
  have hInv : CWfInv edges numV b (st.set ESCAN (encEdges edges)) edges.length
      (checkWf.eval st) := by
    rw [eP, Cmd.eval_forBnd, hblen]
    exact Cmd.foldlState_range_induct _ IDX1 edges.length
      (st.set ESCAN (encEdges edges))
      (CWfInv edges numV b (st.set ESCAN (encEdges edges))) hbase
      (fun i s hi h => checkWf_step edges numV b (st.set ESCAN (encEdges edges))
        hNUMV0 i s hi h)
  obtain ⟨_, hOUTfin, hframefin⟩ := hInv
  refine ⟨?_, ?_⟩
  · rw [hOUTfin, List.take_length]
  · intro r hrO hrE hrVA hrVB hrR1 hrR2 hrLT hrH hrI hrS hr1 hr2 hr3
    rw [hframefin r hrO hrE hrVA hrVB hrR1 hrR2 hrLT hrH hrI hrS hr1 hr2 hr3,
      State.get_set_ne _ _ _ _ hrE]

/-! ### `memberEdge`: the edge-membership FOUND-flag leaf (clique inner)

`memberEdge` sets `FOUND := [1]` iff the ordered pair `(va, vb)` (held unary in
`VALA`/`VALB`) occurs in the edge stream. A single `forBnd` over the edge tally
whose body reads both unary endpoints (`VALC`/`VALD`) and `eqBit`s them against
`VALA`/`VALB`. Unlike the AND-into-`OUTPUT` checks this is an OR-style
accumulator (set on match), so the invariant is phase-free. -/

/-- `Bool`-valued "the ordered pair `(va, vb)` occurs in `edges`" (avoids the
flaky `Decidable (∃ …)` instance; bridges to `∈` via `memB_eq_true_iff`). -/
def memB (va vb : Nat) (edges : List fedge) : Bool :=
  edges.any (fun e => decide (e.1 = va) && decide (e.2 = vb))

theorem memB_eq_true_iff (va vb : Nat) (edges : List fedge) :
    memB va vb edges = true ↔ (va, vb) ∈ edges := by
  simp only [memB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, h1, h2⟩
    obtain ⟨e1, e2⟩ := e; cases h1; cases h2; exact he
  · intro h; exact ⟨(va, vb), h, rfl, rfl⟩

private theorem memB_take_succ (va vb : Nat) (edges : List fedge) (i : Nat)
    (hi : i < edges.length) :
    memB va vb (edges.take (i + 1))
      = (memB va vb (edges.take i)
          || (decide ((edges[i]'hi).1 = va) && decide ((edges[i]'hi).2 = vb))) := by
  rw [memB, memB, List.take_succ_eq_append_getElem hi, List.any_append,
    List.any_cons, List.any_nil, Bool.or_false]

/-- `if replicate a 1 = replicate b 1 then [1] else [0]` collapses to the unary
equality test `[if a = b then 1 else 0]` (the `eqBit`-on-unary-blocks read). -/
private theorem eqBit_replicate (a b : Nat) :
    (if (List.replicate a (1 : Nat)) = List.replicate b 1 then ([1] : List Nat) else [0])
      = [if a = b then 1 else 0] := by
  by_cases h : a = b
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (by rw [replicate_one_eq_iff]; exact h), if_neg h]

/-- `FOUND := [1]` (the match branch of `memberEdge`). -/
private theorem setFound_eval (s : State) :
    ((Cmd.op (.clear FOUND)) ;; Cmd.op (.appendOne FOUND)).eval s = s.set FOUND [1] := by
  rw [Cmd.eval_seq, Cmd.eval_op, Cmd.eval_op]
  simp only [Op.eval, State.get_set_eq, List.nil_append, State.set_set]

/-- `ifBit RES1 (ifBit RES2 setFound cSkip) cSkip` only ever writes
`{FOUND, SKIPR}` (the nested "set FOUND iff both endpoints match" guard). -/
private theorem ifFound_frame (t : State) (r : Var) (hrF : r ≠ FOUND)
    (hrS : r ≠ SKIPR) :
    ((Cmd.ifBit RES1
        (Cmd.ifBit RES2 (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND)) cSkip)
        cSkip).eval t).get r = t.get r := by
  by_cases hb1 : t.get RES1 = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hb1]
    by_cases hb2 : t.get RES2 = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hb2, setFound_eval, State.get_set_ne _ _ _ _ hrF]
    · rw [Cmd.eval_ifBit_false _ _ _ _ hb2, cSkip_eval, State.get_set_ne _ _ _ _ hrS]
  · rw [Cmd.eval_ifBit_false _ _ _ _ hb1, cSkip_eval, State.get_set_ne _ _ _ _ hrS]

/-- The `memberEdge` loop invariant: through iteration `i` the loop has consumed
`i` edges from `ESCAN2` and ORed each "(va,vb) = this edge" test into `FOUND`.
Phase-free (the loop bound is exactly `edges.length`). Frame relative to the
loop-entry state `st`. -/
private def MEInv (va vb : Nat) (edges : List fedge) (st : State)
    (i : Nat) (s : State) : Prop :=
  s.get ESCAN2 = encEdges (edges.drop i)
  ∧ s.get FOUND = [if memB va vb (edges.take i) then 1 else 0]
  ∧ (∀ r : Var, r ≠ FOUND → r ≠ ESCAN2 → r ≠ VALC → r ≠ VALD → r ≠ RES1 →
      r ≠ RES2 → r ≠ HEAD → r ≠ INBLK → r ≠ SKIPR → r ≠ IDX3 → r ≠ IDX4 →
      s.get r = st.get r)

private theorem memberEdge_step (va vb : Nat) (edges : List fedge) (st : State)
    (hVALA : st.get VALA = List.replicate va 1)
    (hVALB : st.get VALB = List.replicate vb 1)
    (i : Nat) (s : State) (hi : i < edges.length) (h : MEInv va vb edges st i s) :
    MEInv va vb edges st (i + 1)
      ((readNum VALC ESCAN2 IDX4 ;;
        readNum VALD ESCAN2 IDX4 ;;
        Cmd.op (.eqBit RES1 VALC VALA) ;;
        Cmd.op (.eqBit RES2 VALD VALB) ;;
        Cmd.ifBit RES1
          (Cmd.ifBit RES2
            (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND))
            cSkip)
          cSkip).eval (s.set IDX3 (List.replicate i 1))) := by
  obtain ⟨hESCAN, hFOUND, hframe⟩ := h
  rw [show (readNum VALC ESCAN2 IDX4 ;; readNum VALD ESCAN2 IDX4 ;;
        Cmd.op (.eqBit RES1 VALC VALA) ;; Cmd.op (.eqBit RES2 VALD VALB) ;;
        Cmd.ifBit RES1
          (Cmd.ifBit RES2 (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND)) cSkip)
          cSkip).eval (s.set IDX3 (List.replicate i 1))
      = (Cmd.ifBit RES1
          (Cmd.ifBit RES2 (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND)) cSkip)
          cSkip).eval
          ((Cmd.op (.eqBit RES2 VALD VALB)).eval
            ((Cmd.op (.eqBit RES1 VALC VALA)).eval
              ((readNum VALD ESCAN2 IDX4).eval
                ((readNum VALC ESCAN2 IDX4).eval (s.set IDX3 (List.replicate i 1))))))
      from by rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]]
  -- the edge at the head of `ESCAN2`
  have hESCAN_in : (s.set IDX3 (List.replicate i 1)).get ESCAN2
      = List.replicate (edges[i]'hi).1 1 ++ 0 ::
          (List.replicate (edges[i]'hi).2 1 ++ 0 :: encEdges (edges.drop (i + 1))) := by
    rw [State.get_set_ne _ _ _ _ (by decide : (ESCAN2 : Var) ≠ IDX3), hESCAN,
      List.drop_eq_getElem_cons hi, encEdges_cons]
  -- rn1: read `e.1` into `VALC`
  obtain ⟨hVALC, hESCAN1, hRN1frame⟩ := readNum_run (s.set IDX3 (List.replicate i 1))
    (edges[i]'hi).1
    (List.replicate (edges[i]'hi).2 1 ++ 0 :: encEdges (edges.drop (i + 1)))
    VALC ESCAN2 IDX4 hESCAN_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALC ESCAN2 IDX4).eval (s.set IDX3 (List.replicate i 1)) with hs1
  -- rn2: read `e.2` into `VALD`
  obtain ⟨hVALD, hESCAN2', hRN2frame⟩ := readNum_run s1
    (edges[i]'hi).2 (encEdges (edges.drop (i + 1)))
    VALD ESCAN2 IDX4 hESCAN1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s2 := (readNum VALD ESCAN2 IDX4).eval s1 with hs2
  have hVALC2 : s2.get VALC = List.replicate (edges[i]'hi).1 1 := by
    rw [hRN2frame VALC (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hVALC]
  have hVALA2 : s2.get VALA = List.replicate va 1 := by
    rw [hRN2frame VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      hRN1frame VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ IDX3),
      hframe VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hVALA]
  have hVALB2 : s2.get VALB = List.replicate vb 1 := by
    rw [hRN2frame VALB (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      hRN1frame VALB (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ IDX3),
      hframe VALB (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hVALB]
  have hFOUND2 : s2.get FOUND = [if memB va vb (edges.take i) then 1 else 0] := by
    rw [hRN2frame FOUND (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      hRN1frame FOUND (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      State.get_set_ne _ _ _ _ (by decide : (FOUND : Var) ≠ IDX3), hFOUND]
  -- eqBit RES1 VALC VALA
  have e3 : (Cmd.op (.eqBit RES1 VALC VALA)).eval s2
      = s2.set RES1 [if (edges[i]'hi).1 = va then 1 else 0] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVALC2, hVALA2, eqBit_replicate]
  rw [e3]
  set s3 := s2.set RES1 [if (edges[i]'hi).1 = va then 1 else 0] with hs3
  have hVALD3 : s3.get VALD = List.replicate (edges[i]'hi).2 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VALD : Var) ≠ RES1), hVALD]
  have hVALB3 : s3.get VALB = List.replicate vb 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ RES1), hVALB2]
  -- eqBit RES2 VALD VALB
  have e4 : (Cmd.op (.eqBit RES2 VALD VALB)).eval s3
      = s3.set RES2 [if (edges[i]'hi).2 = vb then 1 else 0] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVALD3, hVALB3, eqBit_replicate]
  rw [e4]
  set s4 := s3.set RES2 [if (edges[i]'hi).2 = vb then 1 else 0] with hs4
  have hRES1_4 : s4.get RES1 = [if (edges[i]'hi).1 = va then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide : (RES1 : Var) ≠ RES2), State.get_set_eq]
  have hRES2_4 : s4.get RES2 = [if (edges[i]'hi).2 = vb then 1 else 0] := by
    rw [State.get_set_eq]
  have hESCAN4 : s4.get ESCAN2 = encEdges (edges.drop (i + 1)) := by
    rw [State.get_set_ne _ _ _ _ (by decide : (ESCAN2 : Var) ≠ RES2),
      State.get_set_ne _ _ _ _ (by decide : (ESCAN2 : Var) ≠ RES1), hESCAN2']
  have hFOUND4 : s4.get FOUND = [if memB va vb (edges.take i) then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide : (FOUND : Var) ≠ RES2),
      State.get_set_ne _ _ _ _ (by decide : (FOUND : Var) ≠ RES1), hFOUND2]
  refine ⟨?_, ?_, ?_⟩
  · -- ESCAN2
    rw [ifFound_frame _ _ (by decide) (by decide), hESCAN4]
  · -- FOUND
    rw [memB_take_succ va vb edges i hi]
    by_cases h1 : (edges[i]'hi).1 = va
    · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hRES1_4, if_pos h1])]
      by_cases h2 : (edges[i]'hi).2 = vb
      · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hRES2_4, if_pos h2]), setFound_eval,
          State.get_set_eq]
        have hd1 : decide ((edges[i]'hi).1 = va) = true := by simp only [decide_eq_true_eq]; exact h1
        have hd2 : decide ((edges[i]'hi).2 = vb) = true := by simp only [decide_eq_true_eq]; exact h2
        rw [hd1, hd2]; simp
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hRES2_4, if_neg h2]; decide), cSkip_eval,
          State.get_set_ne _ _ _ _ (by decide : (FOUND : Var) ≠ SKIPR), hFOUND4]
        have hd2 : decide ((edges[i]'hi).2 = vb) = false := by
          simp only [decide_eq_false_iff_not]; exact h2
        rw [hd2]; simp
    · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hRES1_4, if_neg h1]; decide), cSkip_eval,
        State.get_set_ne _ _ _ _ (by decide : (FOUND : Var) ≠ SKIPR), hFOUND4]
      have hd1 : decide ((edges[i]'hi).1 = va) = false := by
        simp only [decide_eq_false_iff_not]; exact h1
      rw [hd1]; simp
  · -- frame
    intro r hrF hrE hrVC hrVD hrR1 hrR2 hrH hrI hrS hr3 hr4
    rw [ifFound_frame _ _ hrF hrS, State.get_set_ne _ _ _ _ hrR2,
      State.get_set_ne _ _ _ _ hrR1,
      hRN2frame r hrE hrVD hrI hrH hrS hr4,
      hRN1frame r hrE hrVC hrI hrH hrS hr4,
      State.get_set_ne _ _ _ _ hr3,
      hframe r hrF hrE hrVC hrVD hrR1 hrR2 hrH hrI hrS hr3 hr4]

/-- **The edge-membership leaf is correct.** With `VALA`/`VALB` holding the unary
values `va`/`vb`, the edge stream in `EDGE_STREAM` and its tally in `EDGE_TALLY`,
`memberEdge` writes `[if memB va vb edges then 1 else 0]` to `FOUND` and leaves
every register outside its scratch set untouched (in particular `VALA`, `VALB`,
`OUTPUT` and the input registers 1–6 survive). -/
theorem memberEdge_run (st : State) (va vb : Nat) (edges : List fedge)
    (hVALA : st.get VALA = List.replicate va 1)
    (hVALB : st.get VALB = List.replicate vb 1)
    (hES : st.get EDGE_STREAM = encEdges edges)
    (hET : st.get EDGE_TALLY = List.replicate edges.length 1) :
    (memberEdge.eval st).get FOUND = [if memB va vb edges then 1 else 0]
    ∧ (∀ r : Var, r ≠ FOUND → r ≠ ESCAN2 → r ≠ VALC → r ≠ VALD → r ≠ RES1 →
        r ≠ RES2 → r ≠ HEAD → r ≠ INBLK → r ≠ SKIPR → r ≠ IDX3 → r ≠ IDX4 →
        (memberEdge.eval st).get r = st.get r) := by
  -- init: `clear FOUND ;; appendZero FOUND ;; copy ESCAN2 EDGE_STREAM`
  set st' := (st.set FOUND [0]).set ESCAN2 (encEdges edges) with hst'
  have e1 : (Cmd.op (.clear FOUND)).eval st = st.set FOUND [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e2 : (Cmd.op (.appendZero FOUND)).eval (st.set FOUND [])
      = st.set FOUND [0] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
    rw [State.get_set_eq, List.nil_append, State.set_set]
  have e3 : (Cmd.op (.copy ESCAN2 EDGE_STREAM)).eval (st.set FOUND [0]) = st' := by
    rw [Cmd.eval_op]; simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ FOUND), hES]
  have eP : memberEdge.eval st
      = (Cmd.forBnd IDX3 EDGE_TALLY
          (readNum VALC ESCAN2 IDX4 ;; readNum VALD ESCAN2 IDX4 ;;
           Cmd.op (.eqBit RES1 VALC VALA) ;; Cmd.op (.eqBit RES2 VALD VALB) ;;
           Cmd.ifBit RES1
             (Cmd.ifBit RES2 (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND)) cSkip)
             cSkip)).eval st' := by
    show (Cmd.op (.clear FOUND) ;; Cmd.op (.appendZero FOUND) ;;
      Cmd.op (.copy ESCAN2 EDGE_STREAM) ;; _).eval st = _
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3]
  have hblen : (st'.get EDGE_TALLY).length = edges.length := by
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ ESCAN2),
      State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ FOUND), hET,
      List.length_replicate]
  have hVALA' : st'.get VALA = List.replicate va 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ ESCAN2),
      State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ FOUND), hVALA]
  have hVALB' : st'.get VALB = List.replicate vb 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ ESCAN2),
      State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ FOUND), hVALB]
  have hbase : MEInv va vb edges st' 0 st' := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [State.get_set_eq, List.drop_zero]
    · rw [State.get_set_ne _ _ _ _ (by decide : (FOUND : Var) ≠ ESCAN2),
        State.get_set_eq, List.take_zero]
      simp [memB]
  have hInv : MEInv va vb edges st' edges.length (memberEdge.eval st) := by
    rw [eP, Cmd.eval_forBnd, hblen]
    exact Cmd.foldlState_range_induct _ IDX3 edges.length st'
      (MEInv va vb edges st') hbase
      (fun i s hi h => memberEdge_step va vb edges st' hVALA' hVALB' i s hi h)
  obtain ⟨_, hFOUNDfin, hframefin⟩ := hInv
  refine ⟨?_, ?_⟩
  · rw [hFOUNDfin, List.take_length]
  · intro r hrF hrE hrVC hrVD hrR1 hrR2 hrH hrI hrS hr3 hr4
    rw [hframefin r hrF hrE hrVC hrVD hrR1 hrR2 hrH hrI hrS hr3 hr4,
      State.get_set_ne _ _ _ _ hrE, State.get_set_ne _ _ _ _ hrF]

/-! ### `checkNodup`: the duplicate-free check (nested loop, counter reads) -/

/-- Inner-loop accumulator: scanning the first `m` positions `j'`, every
off-diagonal position (`i ≠ j'`) must differ in value from the outer value `va`. -/
def innerAll (i va : Nat) (l : List fvertex) (m : Nat) : Bool :=
  (List.range m).all (fun j' => decide (i = j') || decide (va ≠ l.getD j' 0))

private theorem innerAll_succ (i va : Nat) (l : List fvertex) (m : Nat) :
    innerAll i va l (m + 1)
      = (innerAll i va l m && (decide (i = m) || decide (va ≠ l.getD m 0))) := by
  rw [innerAll, innerAll, List.range_succ, List.all_append, List.all_cons,
    List.all_nil, Bool.and_true]

/-- `Bool`-valued `l.Nodup`: scanning every outer position `i`, the inner scan
over all positions must place every distinct pair at distinct values. -/
def nodupB (l : List fvertex) : Bool :=
  (List.range l.length).all (fun i => innerAll i (l.getD i 0) l l.length)

theorem nodupB_eq_true_iff (l : List fvertex) : nodupB l = true ↔ l.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  simp only [nodupB, innerAll, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq]
  constructor
  · intro h a b hl
    obtain ⟨a, ha⟩ := a; obtain ⟨b, hb⟩ := b
    simp only at hl
    rcases h a ha b hb with hij | hne
    · exact Fin.ext hij
    · exact absurd (by rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]; exact hl) hne
  · intro hinj i hi j hj
    by_cases hij : i = j
    · exact Or.inl hij
    · refine Or.inr ?_
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      intro heq
      exact hij (congrArg Fin.val (@hinj ⟨i, hi⟩ ⟨j, hj⟩ heq))

/-- The inner-loop guard `ifBit RES1 cSkip (eqBit RES2 VALA VALB ;; ifBit RES2
cReject cSkip)` only ever writes `{OUTPUT, RES2, SKIPR}`. -/
private theorem ifNodup_frame (t : State) (r : Var) (hrO : r ≠ OUTPUT)
    (hrR2 : r ≠ RES2) (hrS : r ≠ SKIPR) :
    ((Cmd.ifBit RES1 cSkip
        (Cmd.op (.eqBit RES2 VALA VALB) ;; Cmd.ifBit RES2 cReject cSkip)).eval t).get r
      = t.get r := by
  by_cases hb1 : t.get RES1 = [1]
  · rw [Cmd.eval_ifBit_true _ _ _ _ hb1, cSkip_eval, State.get_set_ne _ _ _ _ hrS]
  · rw [Cmd.eval_ifBit_false _ _ _ _ hb1, Cmd.eval_seq]
    have he : (Cmd.op (.eqBit RES2 VALA VALB)).eval t
        = t.set RES2 (if t.get VALA = t.get VALB then [1] else [0]) := by
      rw [Cmd.eval_op]; simp only [Op.eval]
    rw [he]
    by_cases hb2 : (t.set RES2 (if t.get VALA = t.get VALB then [1] else [0])).get RES2 = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hb2, cReject_eval,
        State.get_set_ne _ _ _ _ hrO, State.get_set_ne _ _ _ _ hrR2]
    · rw [Cmd.eval_ifBit_false _ _ _ _ hb2, cSkip_eval,
        State.get_set_ne _ _ _ _ hrS, State.get_set_ne _ _ _ _ hrR2]

/-- The `checkNodup` inner-loop invariant (fixed outer position `i`, value `va`):
through inner iteration `j` it has scanned `j` positions, ANDing each
off-diagonal-distinctness test into `OUTPUT`. Frame relative to inner-entry `st`
(`IDX1`/`VALA` survive — they are outside the inner write set). -/
private def NInnerInv (l : List fvertex) (i va : Nat) (b' : Bool) (st : State)
    (j : Nat) (s : State) : Prop :=
  s.get VSCAN2 = encVerts (l.drop j)
  ∧ s.get OUTPUT = [if b' && innerAll i va l j then 1 else 0]
  ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ VSCAN2 → r ≠ VALB → r ≠ IDX2 → r ≠ IDX3 →
      r ≠ RES1 → r ≠ RES2 → r ≠ HEAD → r ≠ INBLK → r ≠ SKIPR →
      s.get r = st.get r)

private theorem checkNodupInner_step (l : List fvertex) (i va : Nat) (b' : Bool)
    (st : State) (hIDX1 : st.get IDX1 = List.replicate i 1)
    (hVALA : st.get VALA = List.replicate va 1)
    (j : Nat) (s : State) (hj : j < l.length) (h : NInnerInv l i va b' st j s) :
    NInnerInv l i va b' st (j + 1)
      ((readNum VALB VSCAN2 IDX3 ;;
        Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
        Cmd.ifBit RES1
          cSkip
          (Cmd.op (.eqBit RES2 VALA VALB) ;;
           Cmd.ifBit RES2 cReject cSkip)).eval (s.set IDX2 (List.replicate j 1))) := by
  obtain ⟨hVSCAN2, hOUT, hframe⟩ := h
  rw [show (readNum VALB VSCAN2 IDX3 ;; Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
        Cmd.ifBit RES1 cSkip
          (Cmd.op (.eqBit RES2 VALA VALB) ;; Cmd.ifBit RES2 cReject cSkip)).eval
          (s.set IDX2 (List.replicate j 1))
      = (Cmd.ifBit RES1 cSkip
          (Cmd.op (.eqBit RES2 VALA VALB) ;; Cmd.ifBit RES2 cReject cSkip)).eval
          ((Cmd.op (.eqBit RES1 IDX1 IDX2)).eval
            ((readNum VALB VSCAN2 IDX3).eval (s.set IDX2 (List.replicate j 1))))
      from by rw [Cmd.eval_seq, Cmd.eval_seq]]
  have hVS_in : (s.set IDX2 (List.replicate j 1)).get VSCAN2
      = List.replicate (l[j]'hj) 1 ++ 0 :: encVerts (l.drop (j + 1)) := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ IDX2), hVSCAN2,
      List.drop_eq_getElem_cons hj, encVerts_cons]
  obtain ⟨hVALB, hVSCAN2', hRNframe⟩ := readNum_run (s.set IDX2 (List.replicate j 1))
    (l[j]'hj) (encVerts (l.drop (j + 1))) VALB VSCAN2 IDX3 hVS_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALB VSCAN2 IDX3).eval (s.set IDX2 (List.replicate j 1)) with hs1
  have hIDX1_1 : s1.get IDX1 = List.replicate i 1 := by
    rw [hRNframe IDX1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (IDX1 : Var) ≠ IDX2),
      hframe IDX1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), hIDX1]
  have hIDX2_1 : s1.get IDX2 = List.replicate j 1 := by
    rw [hRNframe IDX2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_eq]
  have hVALA1 : s1.get VALA = List.replicate va 1 := by
    rw [hRNframe VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ IDX2),
      hframe VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), hVALA]
  have hOUT1 : s1.get OUTPUT = [if b' && innerAll i va l j then 1 else 0] := by
    rw [hRNframe OUTPUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ IDX2),
      hOUT]
  have e2 : (Cmd.op (.eqBit RES1 IDX1 IDX2)).eval s1
      = s1.set RES1 [if i = j then 1 else 0] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hIDX1_1, hIDX2_1, eqBit_replicate]
  rw [e2]
  set s2 := s1.set RES1 [if i = j then 1 else 0] with hs2
  have hRES1_2 : s2.get RES1 = [if i = j then 1 else 0] := State.get_set_eq _ _ _
  have hVALA2 : s2.get VALA = List.replicate va 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ RES1), hVALA1]
  have hVALB2 : s2.get VALB = List.replicate (l[j]'hj) 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ RES1), hVALB]
  have hVSCAN2_2 : s2.get VSCAN2 = encVerts (l.drop (j + 1)) := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ RES1), hVSCAN2']
  have hOUT2 : s2.get OUTPUT = [if b' && innerAll i va l j then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ RES1), hOUT1]
  have hgetD : l.getD j 0 = l[j]'hj := List.getD_eq_getElem _ _ hj
  refine ⟨?_, ?_, ?_⟩
  · rw [ifNodup_frame _ _ (by decide) (by decide) (by decide), hVSCAN2_2]
  · rw [innerAll_succ, hgetD]
    by_cases hij : i = j
    · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hRES1_2, if_pos hij]), cSkip_eval,
        State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ SKIPR), hOUT2]
      have hd : decide (i = j) = true := by simp only [decide_eq_true_eq]; exact hij
      rw [hd]; simp
    · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hRES1_2, if_neg hij]; decide), Cmd.eval_seq]
      have he : (Cmd.op (.eqBit RES2 VALA VALB)).eval s2
          = s2.set RES2 [if va = l[j]'hj then 1 else 0] := by
        rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVALA2, hVALB2, eqBit_replicate]
      rw [he]
      have hd1 : decide (i = j) = false := by simp only [decide_eq_false_iff_not]; exact hij
      by_cases hvl : va = l[j]'hj
      · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [State.get_set_eq, if_pos hvl]),
          cReject_eval, State.get_set_eq]
        have hd2 : decide (va ≠ l[j]'hj) = false := by
          simp only [decide_eq_false_iff_not, not_not]; exact hvl
        rw [hd1, hd2]; simp
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [State.get_set_eq, if_neg hvl]; decide),
          cSkip_eval, State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ SKIPR),
          State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ RES2), hOUT2]
        have hd2 : decide (va ≠ l[j]'hj) = true := by simp only [decide_eq_true_eq]; exact hvl
        rw [hd1, hd2]; simp
  · intro r hrO hrV hrVB hr2 hr3 hrR1 hrR2 hrH hrI hrS
    rw [ifNodup_frame _ _ hrO hrR2 hrS, State.get_set_ne _ _ _ _ hrR1,
      hRNframe r hrV hrVB hrI hrH hrS hr3, State.get_set_ne _ _ _ _ hr2,
      hframe r hrO hrV hrVB hr2 hr3 hrR1 hrR2 hrH hrI hrS]

/-- **The `checkNodup` inner loop is correct.** From inner-entry with `VSCAN2`
holding the full vertex stream, `IDX1`/`VALA` the outer position/value, and
`OUTPUT = [if b' then 1 else 0]`, the inner `forBnd` produces
`OUTPUT = [if b' && innerAll i va l l.length then 1 else 0]`, preserving every
register outside its scratch set (in particular `VSCAN`, `IDX1`, `VALA`). -/
private theorem checkNodupInner_run (st : State) (l : List fvertex) (i va : Nat)
    (b' : Bool)
    (hVSCAN2 : st.get VSCAN2 = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hIDX1 : st.get IDX1 = List.replicate i 1)
    (hVALA : st.get VALA = List.replicate va 1)
    (hO : st.get OUTPUT = [if b' then 1 else 0]) :
    ((Cmd.forBnd IDX2 VERT_TALLY
        (readNum VALB VSCAN2 IDX3 ;;
         Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
         Cmd.ifBit RES1 cSkip
           (Cmd.op (.eqBit RES2 VALA VALB) ;;
            Cmd.ifBit RES2 cReject cSkip))).eval st).get OUTPUT
        = [if b' && innerAll i va l l.length then 1 else 0]
    ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ VSCAN2 → r ≠ VALB → r ≠ IDX2 → r ≠ IDX3 →
        r ≠ RES1 → r ≠ RES2 → r ≠ HEAD → r ≠ INBLK → r ≠ SKIPR →
        ((Cmd.forBnd IDX2 VERT_TALLY
          (readNum VALB VSCAN2 IDX3 ;;
           Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
           Cmd.ifBit RES1 cSkip
             (Cmd.op (.eqBit RES2 VALA VALB) ;;
              Cmd.ifBit RES2 cReject cSkip))).eval st).get r = st.get r) := by
  have hblen : (st.get VERT_TALLY).length = l.length := by
    rw [hVT, List.length_replicate]
  have hbase : NInnerInv l i va b' st 0 st := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [hVSCAN2, List.drop_zero]
    · rw [hO]; simp [innerAll]
  have hInv : NInnerInv l i va b' st l.length
      ((Cmd.forBnd IDX2 VERT_TALLY
        (readNum VALB VSCAN2 IDX3 ;;
         Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
         Cmd.ifBit RES1 cSkip
           (Cmd.op (.eqBit RES2 VALA VALB) ;;
            Cmd.ifBit RES2 cReject cSkip))).eval st) := by
    rw [Cmd.eval_forBnd, hblen]
    exact Cmd.foldlState_range_induct _ IDX2 l.length st
      (NInnerInv l i va b' st) hbase
      (fun j s hj h => checkNodupInner_step l i va b' st hIDX1 hVALA j s hj h)
  obtain ⟨_, hOUTfin, hframefin⟩ := hInv
  exact ⟨hOUTfin, hframefin⟩

/-- The `checkNodup` outer-loop invariant: through outer iteration `i` the loop
has scanned `i` outer positions, ANDing each one's full inner row into `OUTPUT`.
Frame relative to the loop-entry state `st`. -/
private def CNodupInv (l : List fvertex) (b : Bool) (st : State)
    (i : Nat) (s : State) : Prop :=
  s.get VSCAN = encVerts (l.drop i)
  ∧ s.get OUTPUT = [if b && (List.range i).all (fun i' => innerAll i' (l.getD i' 0) l l.length)
      then 1 else 0]
  ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ VSCAN → r ≠ VSCAN2 → r ≠ VALA → r ≠ VALB →
      r ≠ IDX1 → r ≠ IDX2 → r ≠ IDX3 → r ≠ RES1 → r ≠ RES2 → r ≠ HEAD →
      r ≠ INBLK → r ≠ SKIPR → s.get r = st.get r)

private theorem checkNodup_step (l : List fvertex) (b : Bool) (st : State)
    (hVERT : st.get VERT_STREAM = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (i : Nat) (s : State) (hi : i < l.length) (h : CNodupInv l b st i s) :
    CNodupInv l b st (i + 1)
      ((readNum VALA VSCAN IDX2 ;;
        Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
        Cmd.forBnd IDX2 VERT_TALLY
          (readNum VALB VSCAN2 IDX3 ;;
           Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
           Cmd.ifBit RES1 cSkip
             (Cmd.op (.eqBit RES2 VALA VALB) ;;
              Cmd.ifBit RES2 cReject cSkip))).eval (s.set IDX1 (List.replicate i 1))) := by
  obtain ⟨hVSCAN, hOUT, hframe⟩ := h
  rw [show (readNum VALA VSCAN IDX2 ;; Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
        Cmd.forBnd IDX2 VERT_TALLY
          (readNum VALB VSCAN2 IDX3 ;;
           Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
           Cmd.ifBit RES1 cSkip
             (Cmd.op (.eqBit RES2 VALA VALB) ;;
              Cmd.ifBit RES2 cReject cSkip))).eval (s.set IDX1 (List.replicate i 1))
      = (Cmd.forBnd IDX2 VERT_TALLY
          (readNum VALB VSCAN2 IDX3 ;;
           Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
           Cmd.ifBit RES1 cSkip
             (Cmd.op (.eqBit RES2 VALA VALB) ;;
              Cmd.ifBit RES2 cReject cSkip))).eval
          ((Cmd.op (.copy VSCAN2 VERT_STREAM)).eval
            ((readNum VALA VSCAN IDX2).eval (s.set IDX1 (List.replicate i 1))))
      from by rw [Cmd.eval_seq, Cmd.eval_seq]]
  have hVS_in : (s.set IDX1 (List.replicate i 1)).get VSCAN
      = List.replicate (l[i]'hi) 1 ++ 0 :: encVerts (l.drop (i + 1)) := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VSCAN : Var) ≠ IDX1), hVSCAN,
      List.drop_eq_getElem_cons hi, encVerts_cons]
  obtain ⟨hVALA, hVSCAN', hRNframe⟩ := readNum_run (s.set IDX1 (List.replicate i 1))
    (l[i]'hi) (encVerts (l.drop (i + 1))) VALA VSCAN IDX2 hVS_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALA VSCAN IDX2).eval (s.set IDX1 (List.replicate i 1)) with hs1
  have hVERT1 : s1.get VERT_STREAM = encVerts l := by
    rw [hRNframe VERT_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (VERT_STREAM : Var) ≠ IDX1),
      hframe VERT_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hVERT]
  have ecopy : (Cmd.op (.copy VSCAN2 VERT_STREAM)).eval s1 = s1.set VSCAN2 (encVerts l) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVERT1]
  rw [ecopy]
  set s2 := s1.set VSCAN2 (encVerts l) with hs2
  have hVSCAN2_2 : s2.get VSCAN2 = encVerts l := State.get_set_eq _ _ _
  have hVT2 : s2.get VERT_TALLY = List.replicate l.length 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ VSCAN2),
      hRNframe VERT_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ IDX1),
      hframe VERT_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hVT]
  have hIDX1_2 : s2.get IDX1 = List.replicate i 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (IDX1 : Var) ≠ VSCAN2),
      hRNframe IDX1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_eq]
  have hVALA2 : s2.get VALA = List.replicate (l[i]'hi) 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ VSCAN2), hVALA]
  have hOUT2 : s2.get OUTPUT
      = [if b && (List.range i).all (fun i' => innerAll i' (l.getD i' 0) l l.length)
          then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ VSCAN2),
      hRNframe OUTPUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ IDX1),
      hOUT]
  have hgetD : l.getD i 0 = l[i]'hi := List.getD_eq_getElem _ _ hi
  obtain ⟨hInnerOut, hInnerFrame⟩ := checkNodupInner_run s2 l i (l[i]'hi)
    (b && (List.range i).all (fun i' => innerAll i' (l.getD i' 0) l l.length))
    hVSCAN2_2 hVT2 hIDX1_2 hVALA2 hOUT2
  refine ⟨?_, ?_, ?_⟩
  · rw [hInnerFrame VSCAN (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
      State.get_set_ne _ _ _ _ (by decide : (VSCAN : Var) ≠ VSCAN2), hVSCAN']
  · rw [hInnerOut, List.range_succ, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true, hgetD, Bool.and_assoc]
  · intro r hrO hrV hrV2 hrVA hrVB hr1 hr2 hr3 hrR1 hrR2 hrH hrI hrS
    rw [hInnerFrame r hrO hrV2 hrVB hr2 hr3 hrR1 hrR2 hrH hrI hrS,
      State.get_set_ne _ _ _ _ hrV2,
      hRNframe r hrV hrVA hrI hrH hrS hr2, State.get_set_ne _ _ _ _ hr1,
      hframe r hrO hrV hrV2 hrVA hrVB hr1 hr2 hr3 hrR1 hrR2 hrH hrI hrS]

/-- **Check 4 — `l.Nodup`** (no repeated vertex), ANDed into `OUTPUT`. A double
`forBnd`: the outer scan reads `l[i]` into `VALA` (counter `IDX1`); the inner
scan over a fresh copy `VSCAN2` reads `l[j]` and, off the diagonal `i = j`
(detected by `eqBit IDX1 IDX2` on the unary counters), rejects if `l[i] = l[j]`. -/
theorem checkNodup_run (st : State) (l : List fvertex) (b : Bool)
    (hVS : st.get VERT_STREAM = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hO : st.get OUTPUT = [if b then 1 else 0]) :
    (checkNodup.eval st).get OUTPUT = [if b && nodupB l then 1 else 0]
    ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ VSCAN → r ≠ VSCAN2 → r ≠ VALA → r ≠ VALB →
        r ≠ IDX1 → r ≠ IDX2 → r ≠ IDX3 → r ≠ RES1 → r ≠ RES2 → r ≠ HEAD →
        r ≠ INBLK → r ≠ SKIPR → (checkNodup.eval st).get r = st.get r) := by
  have eInit : (Cmd.op (.copy VSCAN VERT_STREAM)).eval st = st.set VSCAN (encVerts l) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVS]
  have eP : checkNodup.eval st
      = (Cmd.forBnd IDX1 VERT_TALLY
          (readNum VALA VSCAN IDX2 ;;
           Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
           Cmd.forBnd IDX2 VERT_TALLY
             (readNum VALB VSCAN2 IDX3 ;;
              Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
              Cmd.ifBit RES1 cSkip
                (Cmd.op (.eqBit RES2 VALA VALB) ;;
                 Cmd.ifBit RES2 cReject cSkip)))).eval (st.set VSCAN (encVerts l)) := by
    show (Cmd.op (.copy VSCAN VERT_STREAM) ;; _).eval st = _
    rw [Cmd.eval_seq, eInit]
  have hblen : ((st.set VSCAN (encVerts l)).get VERT_TALLY).length = l.length := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ VSCAN), hVT,
      List.length_replicate]
  have hbase : CNodupInv l b (st.set VSCAN (encVerts l)) 0 (st.set VSCAN (encVerts l)) := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [State.get_set_eq, List.drop_zero]
    · rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ VSCAN), hO]; simp
  have hVERT0 : (st.set VSCAN (encVerts l)).get VERT_STREAM = encVerts l := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VERT_STREAM : Var) ≠ VSCAN), hVS]
  have hVT0 : (st.set VSCAN (encVerts l)).get VERT_TALLY = List.replicate l.length 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ VSCAN), hVT]
  have hInv : CNodupInv l b (st.set VSCAN (encVerts l)) l.length (checkNodup.eval st) := by
    rw [eP, Cmd.eval_forBnd, hblen]
    exact Cmd.foldlState_range_induct _ IDX1 l.length (st.set VSCAN (encVerts l))
      (CNodupInv l b (st.set VSCAN (encVerts l))) hbase
      (fun i s hi h => checkNodup_step l b (st.set VSCAN (encVerts l)) hVERT0 hVT0 i s hi h)
  obtain ⟨_, hOUTfin, hframefin⟩ := hInv
  refine ⟨?_, ?_⟩
  · rw [hOUTfin,
      show nodupB l = (List.range l.length).all (fun i => innerAll i (l.getD i 0) l l.length)
        from rfl]
  · intro r hrO hrV hrV2 hrVA hrVB hr1 hr2 hr3 hrR1 hrR2 hrH hrI hrS
    rw [hframefin r hrO hrV hrV2 hrVA hrVB hr1 hr2 hr3 hrR1 hrR2 hrH hrI hrS,
      State.get_set_ne _ _ _ _ hrV]

/-! ### `checkClique`: the clique-adjacency check (depth-4 nested loop) -/

/-- Inner-loop accumulator: scanning the first `m` positions `j'`, every
distinct-valued pair `(va, l[j'])` must be an edge. -/
def cliqueInnerAll (va : Nat) (edges : List fedge) (l : List fvertex) (m : Nat) : Bool :=
  (List.range m).all (fun j' => decide (va = l.getD j' 0) || memB va (l.getD j' 0) edges)

private theorem cliqueInnerAll_succ (va : Nat) (edges : List fedge) (l : List fvertex)
    (m : Nat) :
    cliqueInnerAll va edges l (m + 1)
      = (cliqueInnerAll va edges l m
          && (decide (va = l.getD m 0) || memB va (l.getD m 0) edges)) := by
  rw [cliqueInnerAll, cliqueInnerAll, List.range_succ, List.all_append, List.all_cons,
    List.all_nil, Bool.and_true]

/-- `Bool`-valued clique-adjacency: every ordered pair of positions with distinct
values is an edge. -/
def cliqueB (edges : List fedge) (l : List fvertex) : Bool :=
  (List.range l.length).all (fun i => cliqueInnerAll (l.getD i 0) edges l l.length)

theorem cliqueB_eq_true_iff (edges : List fedge) (l : List fvertex) :
    cliqueB edges l = true
      ↔ ∀ v₁ v₂ : fvertex, v₁ ∈ l → v₂ ∈ l → v₁ ≠ v₂ → (v₁, v₂) ∈ edges := by
  simp only [cliqueB, cliqueInnerAll, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq, memB_eq_true_iff]
  constructor
  · intro h v₁ v₂ hv1 hv2 hne
    obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hv1
    obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hv2
    have hh := h i hi j hj
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, hgi, hgj] at hh
    rcases hh with heq | hmem
    · exact absurd heq hne
    · exact hmem
  · intro h i hi j hj
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    by_cases heq : l[i] = l[j]
    · exact Or.inl heq
    · exact Or.inr (h l[i] l[j] (List.getElem_mem hi) (List.getElem_mem hj) heq)

/-- The `checkClique` inner-loop invariant (fixed outer value `va`): through inner
iteration `j` it has scanned `j` positions, ANDing each distinct-valued
edge-membership test into `OUTPUT`. Frame relative to inner-entry `st`. -/
private def CliqueInnerInv (edges : List fedge) (l : List fvertex) (va : Nat)
    (b' : Bool) (st : State) (j : Nat) (s : State) : Prop :=
  s.get VSCAN2 = encVerts (l.drop j)
  ∧ s.get OUTPUT = [if b' && cliqueInnerAll va edges l j then 1 else 0]
  ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ VSCAN2 → r ≠ VALB → r ≠ FOUND → r ≠ ESCAN2 →
      r ≠ VALC → r ≠ VALD → r ≠ IDX2 → r ≠ IDX3 → r ≠ IDX4 → r ≠ RES1 →
      r ≠ RES2 → r ≠ HEAD → r ≠ INBLK → r ≠ SKIPR → s.get r = st.get r)

private theorem checkCliqueInner_step (edges : List fedge) (l : List fvertex)
    (va : Nat) (b' : Bool) (st : State)
    (hVALA : st.get VALA = List.replicate va 1)
    (hES : st.get EDGE_STREAM = encEdges edges)
    (hET : st.get EDGE_TALLY = List.replicate edges.length 1)
    (j : Nat) (s : State) (hj : j < l.length) (h : CliqueInnerInv edges l va b' st j s) :
    CliqueInnerInv edges l va b' st (j + 1)
      ((readNum VALB VSCAN2 IDX3 ;;
        Cmd.op (.eqBit RES1 VALA VALB) ;;
        Cmd.ifBit RES1 cSkip
          (memberEdge ;; Cmd.ifBit FOUND cSkip cReject)).eval
            (s.set IDX2 (List.replicate j 1))) := by
  obtain ⟨hVSCAN2, hOUT, hframe⟩ := h
  rw [show (readNum VALB VSCAN2 IDX3 ;; Cmd.op (.eqBit RES1 VALA VALB) ;;
        Cmd.ifBit RES1 cSkip (memberEdge ;; Cmd.ifBit FOUND cSkip cReject)).eval
          (s.set IDX2 (List.replicate j 1))
      = (Cmd.ifBit RES1 cSkip (memberEdge ;; Cmd.ifBit FOUND cSkip cReject)).eval
          ((Cmd.op (.eqBit RES1 VALA VALB)).eval
            ((readNum VALB VSCAN2 IDX3).eval (s.set IDX2 (List.replicate j 1))))
      from by rw [Cmd.eval_seq, Cmd.eval_seq]]
  have hVS_in : (s.set IDX2 (List.replicate j 1)).get VSCAN2
      = List.replicate (l[j]'hj) 1 ++ 0 :: encVerts (l.drop (j + 1)) := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ IDX2), hVSCAN2,
      List.drop_eq_getElem_cons hj, encVerts_cons]
  obtain ⟨hVALB, hVSCAN2', hRNframe⟩ := readNum_run (s.set IDX2 (List.replicate j 1))
    (l[j]'hj) (encVerts (l.drop (j + 1))) VALB VSCAN2 IDX3 hVS_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALB VSCAN2 IDX3).eval (s.set IDX2 (List.replicate j 1)) with hs1
  have hVALA1 : s1.get VALA = List.replicate va 1 := by
    rw [hRNframe VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ IDX2),
      hframe VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), hVALA]
  have hES1 : s1.get EDGE_STREAM = encEdges edges := by
    rw [hRNframe EDGE_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ IDX2),
      hframe EDGE_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), hES]
  have hET1 : s1.get EDGE_TALLY = List.replicate edges.length 1 := by
    rw [hRNframe EDGE_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ IDX2),
      hframe EDGE_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), hET]
  have hOUT1 : s1.get OUTPUT = [if b' && cliqueInnerAll va edges l j then 1 else 0] := by
    rw [hRNframe OUTPUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ IDX2),
      hOUT]
  have e2 : (Cmd.op (.eqBit RES1 VALA VALB)).eval s1
      = s1.set RES1 [if va = l[j]'hj then 1 else 0] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVALA1, hVALB, eqBit_replicate]
  rw [e2]
  set s2 := s1.set RES1 [if va = l[j]'hj then 1 else 0] with hs2
  have hRES1_2 : s2.get RES1 = [if va = l[j]'hj then 1 else 0] := State.get_set_eq _ _ _
  have hVALA2 : s2.get VALA = List.replicate va 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ RES1), hVALA1]
  have hVALB2 : s2.get VALB = List.replicate (l[j]'hj) 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ RES1), hVALB]
  have hES2 : s2.get EDGE_STREAM = encEdges edges := by
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ RES1), hES1]
  have hET2 : s2.get EDGE_TALLY = List.replicate edges.length 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ RES1), hET1]
  have hVSCAN2_2 : s2.get VSCAN2 = encVerts (l.drop (j + 1)) := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ RES1), hVSCAN2']
  have hOUT2 : s2.get OUTPUT = [if b' && cliqueInnerAll va edges l j then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ RES1), hOUT1]
  have hgetD : l.getD j 0 = l[j]'hj := List.getD_eq_getElem _ _ hj
  by_cases heq : va = l[j]'hj
  · -- equal values: skip
    rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hRES1_2, if_pos heq]), cSkip_eval]
    refine ⟨?_, ?_, ?_⟩
    · rw [State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ SKIPR), hVSCAN2_2]
    · rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ SKIPR), hOUT2,
        cliqueInnerAll_succ, hgetD]
      have hd : decide (va = l[j]'hj) = true := by simp only [decide_eq_true_eq]; exact heq
      rw [hd]; simp
    · intro r hrO hrV2 hrVB hrF hrE2 hrVC hrVD hr2 hr3 hr4 hrR1 hrR2 hrH hrI hrS
      rw [State.get_set_ne _ _ _ _ hrS, State.get_set_ne _ _ _ _ hrR1,
        hRNframe r hrV2 hrVB hrI hrH hrS hr3, State.get_set_ne _ _ _ _ hr2,
        hframe r hrO hrV2 hrVB hrF hrE2 hrVC hrVD hr2 hr3 hr4 hrR1 hrR2 hrH hrI hrS]
  · -- distinct values: run the membership check
    rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hRES1_2, if_neg heq]; decide), Cmd.eval_seq]
    obtain ⟨hFOUND_mem, hMEframe⟩ :=
      memberEdge_run s2 va (l[j]'hj) edges hVALA2 hVALB2 hES2 hET2
    set s3 := memberEdge.eval s2 with hs3
    have hOUT3 : s3.get OUTPUT = [if b' && cliqueInnerAll va edges l j then 1 else 0] := by
      rw [hMEframe OUTPUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hOUT2]
    have hVSCAN2_3 : s3.get VSCAN2 = encVerts (l.drop (j + 1)) := by
      rw [hMEframe VSCAN2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hVSCAN2_2]
    have hd1 : decide (va = l[j]'hj) = false := by
      simp only [decide_eq_false_iff_not]; exact heq
    by_cases hmem : memB va (l[j]'hj) edges = true
    · -- is an edge: skip
      rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hFOUND_mem]; simp [hmem]), cSkip_eval]
      refine ⟨?_, ?_, ?_⟩
      · rw [State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ SKIPR), hVSCAN2_3]
      · rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ SKIPR), hOUT3,
          cliqueInnerAll_succ, hgetD, hd1, hmem]; simp
      · intro r hrO hrV2 hrVB hrF hrE2 hrVC hrVD hr2 hr3 hr4 hrR1 hrR2 hrH hrI hrS
        rw [State.get_set_ne _ _ _ _ hrS,
          hMEframe r hrF hrE2 hrVC hrVD hrR1 hrR2 hrH hrI hrS hr3 hr4,
          State.get_set_ne _ _ _ _ hrR1, hRNframe r hrV2 hrVB hrI hrH hrS hr3,
          State.get_set_ne _ _ _ _ hr2,
          hframe r hrO hrV2 hrVB hrF hrE2 hrVC hrVD hr2 hr3 hr4 hrR1 hrR2 hrH hrI hrS]
    · -- not an edge: reject
      have hmf : memB va (l[j]'hj) edges = false := by simpa using hmem
      rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hFOUND_mem, hmf]; decide), cReject_eval]
      refine ⟨?_, ?_, ?_⟩
      · rw [State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ OUTPUT), hVSCAN2_3]
      · rw [State.get_set_eq, cliqueInnerAll_succ, hgetD, hd1, hmf]; simp
      · intro r hrO hrV2 hrVB hrF hrE2 hrVC hrVD hr2 hr3 hr4 hrR1 hrR2 hrH hrI hrS
        rw [State.get_set_ne _ _ _ _ hrO,
          hMEframe r hrF hrE2 hrVC hrVD hrR1 hrR2 hrH hrI hrS hr3 hr4,
          State.get_set_ne _ _ _ _ hrR1, hRNframe r hrV2 hrVB hrI hrH hrS hr3,
          State.get_set_ne _ _ _ _ hr2,
          hframe r hrO hrV2 hrVB hrF hrE2 hrVC hrVD hr2 hr3 hr4 hrR1 hrR2 hrH hrI hrS]

/-- **The `checkClique` inner loop is correct.** From inner-entry with the full
vertex stream in `VSCAN2`, the edge stream/tally available, `VALA` the outer
value, and `OUTPUT = [if b' then 1 else 0]`, the inner `forBnd` produces
`OUTPUT = [if b' && cliqueInnerAll va edges l l.length then 1 else 0]`,
preserving every register outside its scratch set. -/
private theorem checkCliqueInner_run (st : State) (edges : List fedge)
    (l : List fvertex) (va : Nat) (b' : Bool)
    (hVSCAN2 : st.get VSCAN2 = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hVALA : st.get VALA = List.replicate va 1)
    (hES : st.get EDGE_STREAM = encEdges edges)
    (hET : st.get EDGE_TALLY = List.replicate edges.length 1)
    (hO : st.get OUTPUT = [if b' then 1 else 0]) :
    ((Cmd.forBnd IDX2 VERT_TALLY
        (readNum VALB VSCAN2 IDX3 ;;
         Cmd.op (.eqBit RES1 VALA VALB) ;;
         Cmd.ifBit RES1 cSkip
           (memberEdge ;; Cmd.ifBit FOUND cSkip cReject))).eval st).get OUTPUT
        = [if b' && cliqueInnerAll va edges l l.length then 1 else 0]
    ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ VSCAN2 → r ≠ VALB → r ≠ FOUND → r ≠ ESCAN2 →
        r ≠ VALC → r ≠ VALD → r ≠ IDX2 → r ≠ IDX3 → r ≠ IDX4 → r ≠ RES1 →
        r ≠ RES2 → r ≠ HEAD → r ≠ INBLK → r ≠ SKIPR →
        ((Cmd.forBnd IDX2 VERT_TALLY
          (readNum VALB VSCAN2 IDX3 ;;
           Cmd.op (.eqBit RES1 VALA VALB) ;;
           Cmd.ifBit RES1 cSkip
             (memberEdge ;; Cmd.ifBit FOUND cSkip cReject))).eval st).get r = st.get r) := by
  have hblen : (st.get VERT_TALLY).length = l.length := by
    rw [hVT, List.length_replicate]
  have hbase : CliqueInnerInv edges l va b' st 0 st := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [hVSCAN2, List.drop_zero]
    · rw [hO]; simp [cliqueInnerAll]
  have hInv : CliqueInnerInv edges l va b' st l.length
      ((Cmd.forBnd IDX2 VERT_TALLY
        (readNum VALB VSCAN2 IDX3 ;;
         Cmd.op (.eqBit RES1 VALA VALB) ;;
         Cmd.ifBit RES1 cSkip
           (memberEdge ;; Cmd.ifBit FOUND cSkip cReject))).eval st) := by
    rw [Cmd.eval_forBnd, hblen]
    exact Cmd.foldlState_range_induct _ IDX2 l.length st
      (CliqueInnerInv edges l va b' st) hbase
      (fun j s hj h => checkCliqueInner_step edges l va b' st hVALA hES hET j s hj h)
  obtain ⟨_, hOUTfin, hframefin⟩ := hInv
  exact ⟨hOUTfin, hframefin⟩

/-- The `checkClique` outer-loop invariant. -/
private def CCliqueInv (edges : List fedge) (l : List fvertex) (b : Bool) (st : State)
    (i : Nat) (s : State) : Prop :=
  s.get VSCAN = encVerts (l.drop i)
  ∧ s.get OUTPUT = [if b && (List.range i).all (fun i' => cliqueInnerAll (l.getD i' 0) edges l l.length)
      then 1 else 0]
  ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ VSCAN → r ≠ VSCAN2 → r ≠ VALA → r ≠ VALB →
      r ≠ FOUND → r ≠ ESCAN2 → r ≠ VALC → r ≠ VALD → r ≠ IDX1 → r ≠ IDX2 →
      r ≠ IDX3 → r ≠ IDX4 → r ≠ RES1 → r ≠ RES2 → r ≠ HEAD → r ≠ INBLK →
      r ≠ SKIPR → s.get r = st.get r)

private theorem checkClique_step (edges : List fedge) (l : List fvertex) (b : Bool)
    (st : State)
    (hVERT : st.get VERT_STREAM = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hES : st.get EDGE_STREAM = encEdges edges)
    (hET : st.get EDGE_TALLY = List.replicate edges.length 1)
    (i : Nat) (s : State) (hi : i < l.length) (h : CCliqueInv edges l b st i s) :
    CCliqueInv edges l b st (i + 1)
      ((readNum VALA VSCAN IDX2 ;;
        Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
        Cmd.forBnd IDX2 VERT_TALLY
          (readNum VALB VSCAN2 IDX3 ;;
           Cmd.op (.eqBit RES1 VALA VALB) ;;
           Cmd.ifBit RES1 cSkip
             (memberEdge ;; Cmd.ifBit FOUND cSkip cReject))).eval
              (s.set IDX1 (List.replicate i 1))) := by
  obtain ⟨hVSCAN, hOUT, hframe⟩ := h
  rw [show (readNum VALA VSCAN IDX2 ;; Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
        Cmd.forBnd IDX2 VERT_TALLY
          (readNum VALB VSCAN2 IDX3 ;;
           Cmd.op (.eqBit RES1 VALA VALB) ;;
           Cmd.ifBit RES1 cSkip
             (memberEdge ;; Cmd.ifBit FOUND cSkip cReject))).eval
          (s.set IDX1 (List.replicate i 1))
      = (Cmd.forBnd IDX2 VERT_TALLY
          (readNum VALB VSCAN2 IDX3 ;;
           Cmd.op (.eqBit RES1 VALA VALB) ;;
           Cmd.ifBit RES1 cSkip
             (memberEdge ;; Cmd.ifBit FOUND cSkip cReject))).eval
          ((Cmd.op (.copy VSCAN2 VERT_STREAM)).eval
            ((readNum VALA VSCAN IDX2).eval (s.set IDX1 (List.replicate i 1))))
      from by rw [Cmd.eval_seq, Cmd.eval_seq]]
  have hVS_in : (s.set IDX1 (List.replicate i 1)).get VSCAN
      = List.replicate (l[i]'hi) 1 ++ 0 :: encVerts (l.drop (i + 1)) := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VSCAN : Var) ≠ IDX1), hVSCAN,
      List.drop_eq_getElem_cons hi, encVerts_cons]
  obtain ⟨hVALA, hVSCAN', hRNframe⟩ := readNum_run (s.set IDX1 (List.replicate i 1))
    (l[i]'hi) (encVerts (l.drop (i + 1))) VALA VSCAN IDX2 hVS_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALA VSCAN IDX2).eval (s.set IDX1 (List.replicate i 1)) with hs1
  have hVERT1 : s1.get VERT_STREAM = encVerts l := by
    rw [hRNframe VERT_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (VERT_STREAM : Var) ≠ IDX1),
      hframe VERT_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hVERT]
  have ecopy : (Cmd.op (.copy VSCAN2 VERT_STREAM)).eval s1 = s1.set VSCAN2 (encVerts l) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVERT1]
  rw [ecopy]
  set s2 := s1.set VSCAN2 (encVerts l) with hs2
  have hVSCAN2_2 : s2.get VSCAN2 = encVerts l := State.get_set_eq _ _ _
  have hVT2 : s2.get VERT_TALLY = List.replicate l.length 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ VSCAN2),
      hRNframe VERT_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ IDX1),
      hframe VERT_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hVT]
  have hVALA2 : s2.get VALA = List.replicate (l[i]'hi) 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ VSCAN2), hVALA]
  have hES2 : s2.get EDGE_STREAM = encEdges edges := by
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ VSCAN2),
      hRNframe EDGE_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ IDX1),
      hframe EDGE_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hES]
  have hET2 : s2.get EDGE_TALLY = List.replicate edges.length 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ VSCAN2),
      hRNframe EDGE_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ IDX1),
      hframe EDGE_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hET]
  have hOUT2 : s2.get OUTPUT
      = [if b && (List.range i).all (fun i' => cliqueInnerAll (l.getD i' 0) edges l l.length)
          then 1 else 0] := by
    rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ VSCAN2),
      hRNframe OUTPUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ IDX1),
      hOUT]
  have hgetD : l.getD i 0 = l[i]'hi := List.getD_eq_getElem _ _ hi
  obtain ⟨hInnerOut, hInnerFrame⟩ := checkCliqueInner_run s2 edges l (l[i]'hi)
    (b && (List.range i).all (fun i' => cliqueInnerAll (l.getD i' 0) edges l l.length))
    hVSCAN2_2 hVT2 hVALA2 hES2 hET2 hOUT2
  refine ⟨?_, ?_, ?_⟩
  · rw [hInnerFrame VSCAN (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
      State.get_set_ne _ _ _ _ (by decide : (VSCAN : Var) ≠ VSCAN2), hVSCAN']
  · rw [hInnerOut, List.range_succ, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true, hgetD, Bool.and_assoc]
  · intro r hrO hrV hrV2 hrVA hrVB hrF hrE2 hrVC hrVD hr1 hr2 hr3 hr4 hrR1 hrR2
      hrH hrI hrS
    rw [hInnerFrame r hrO hrV2 hrVB hrF hrE2 hrVC hrVD hr2 hr3 hr4 hrR1 hrR2 hrH hrI hrS,
      State.get_set_ne _ _ _ _ hrV2,
      hRNframe r hrV hrVA hrI hrH hrS hr2, State.get_set_ne _ _ _ _ hr1,
      hframe r hrO hrV hrV2 hrVA hrVB hrF hrE2 hrVC hrVD hr1 hr2 hr3 hr4 hrR1 hrR2
        hrH hrI hrS]

/-- **Check 5 — clique adjacency** (every distinct-valued pair of list elements
is an edge), ANDed into `OUTPUT`. The depth-4 nested loop: outer/inner `forBnd`
over the vertex list reading `l[i]`/`l[j]`, and when their values differ the body
runs `memberEdge` (itself a `forBnd` over the edge stream). -/
theorem checkClique_run (st : State) (edges : List fedge) (l : List fvertex) (b : Bool)
    (hVS : st.get VERT_STREAM = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hES : st.get EDGE_STREAM = encEdges edges)
    (hET : st.get EDGE_TALLY = List.replicate edges.length 1)
    (hO : st.get OUTPUT = [if b then 1 else 0]) :
    (checkClique.eval st).get OUTPUT = [if b && cliqueB edges l then 1 else 0]
    ∧ (∀ r : Var, r ≠ OUTPUT → r ≠ VSCAN → r ≠ VSCAN2 → r ≠ VALA → r ≠ VALB →
        r ≠ FOUND → r ≠ ESCAN2 → r ≠ VALC → r ≠ VALD → r ≠ IDX1 → r ≠ IDX2 →
        r ≠ IDX3 → r ≠ IDX4 → r ≠ RES1 → r ≠ RES2 → r ≠ HEAD → r ≠ INBLK →
        r ≠ SKIPR → (checkClique.eval st).get r = st.get r) := by
  have eInit : (Cmd.op (.copy VSCAN VERT_STREAM)).eval st = st.set VSCAN (encVerts l) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVS]
  have eP : checkClique.eval st
      = (Cmd.forBnd IDX1 VERT_TALLY
          (readNum VALA VSCAN IDX2 ;;
           Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
           Cmd.forBnd IDX2 VERT_TALLY
             (readNum VALB VSCAN2 IDX3 ;;
              Cmd.op (.eqBit RES1 VALA VALB) ;;
              Cmd.ifBit RES1 cSkip
                (memberEdge ;; Cmd.ifBit FOUND cSkip cReject)))).eval
          (st.set VSCAN (encVerts l)) := by
    show (Cmd.op (.copy VSCAN VERT_STREAM) ;; _).eval st = _
    rw [Cmd.eval_seq, eInit]
  have hblen : ((st.set VSCAN (encVerts l)).get VERT_TALLY).length = l.length := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ VSCAN), hVT,
      List.length_replicate]
  have hbase : CCliqueInv edges l b (st.set VSCAN (encVerts l)) 0 (st.set VSCAN (encVerts l)) := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [State.get_set_eq, List.drop_zero]
    · rw [State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ VSCAN), hO]; simp
  have hVERT0 : (st.set VSCAN (encVerts l)).get VERT_STREAM = encVerts l := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VERT_STREAM : Var) ≠ VSCAN), hVS]
  have hVT0 : (st.set VSCAN (encVerts l)).get VERT_TALLY = List.replicate l.length 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ VSCAN), hVT]
  have hES0 : (st.set VSCAN (encVerts l)).get EDGE_STREAM = encEdges edges := by
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ VSCAN), hES]
  have hET0 : (st.set VSCAN (encVerts l)).get EDGE_TALLY = List.replicate edges.length 1 := by
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ VSCAN), hET]
  have hInv : CCliqueInv edges l b (st.set VSCAN (encVerts l)) l.length (checkClique.eval st) := by
    rw [eP, Cmd.eval_forBnd, hblen]
    exact Cmd.foldlState_range_induct _ IDX1 l.length (st.set VSCAN (encVerts l))
      (CCliqueInv edges l b (st.set VSCAN (encVerts l))) hbase
      (fun i s hi h => checkClique_step edges l b (st.set VSCAN (encVerts l))
        hVERT0 hVT0 hES0 hET0 i s hi h)
  obtain ⟨_, hOUTfin, hframefin⟩ := hInv
  refine ⟨?_, ?_⟩
  · rw [hOUTfin,
      show cliqueB edges l
          = (List.range l.length).all (fun i => cliqueInnerAll (l.getD i 0) edges l l.length)
        from rfl]
  · intro r hrO hrV hrV2 hrVA hrVB hrF hrE2 hrVC hrVD hr1 hr2 hr3 hr4 hrR1 hrR2
      hrH hrI hrS
    rw [hframefin r hrO hrV hrV2 hrVA hrVB hrF hrE2 hrVC hrVD hr1 hr2 hr3 hr4 hrR1 hrR2
        hrH hrI hrS, State.get_set_ne _ _ _ _ hrV]

/-! ### `decides` assembly — the 5 checks chained into `OUTPUT` -/

/-- The conjunction of the 5 Bool checks is exactly `cliqueRel`. -/
theorem cliqueRel_iff_checks (G : fgraph) (k : Nat) (l : List fvertex) :
    cliqueRel (G, k) l
      ↔ (edgesWf G.1 G.2 && allLt G.1 l && decide (l.length = k) && nodupB l
          && cliqueB G.2 l) = true := by
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    edgesWf_eq_true_iff, allLt_eq_true_iff, decide_eq_true_eq, nodupB_eq_true_iff,
    cliqueB_eq_true_iff]
  show (fgraph_wf G ∧ isfKClique k G l) ↔ _
  unfold fgraph_wf isfKClique isfClique
  tauto

/-- **The verifier program decides `cliqueRel`.** Start `OUTPUT := [1]`, then chain
the five proven per-check run-lemmas (each ANDs its predicate into `OUTPUT` while
preserving the read-only input registers 1–6), so the final bit is the
conjunction of all five predicates = `cliqueRel`. -/
theorem cliqueRelCmd_decides :
    Cmd.decides cliqueRelCmd cliqueRelEncode
      (fun Gkl : (fgraph × Nat) × List fvertex => cliqueRel Gkl.1 Gkl.2) := by
  intro x
  obtain ⟨⟨G, k⟩, l⟩ := x
  -- encode facts
  have hO0 : (cliqueRelEncode ((G, k), l)).get OUTPUT = [] := rfl
  have hN0 : (cliqueRelEncode ((G, k), l)).get NUMV = List.replicate G.1 1 := rfl
  have hE0 : (cliqueRelEncode ((G, k), l)).get EDGE_STREAM = encEdges G.2 := rfl
  have hK0 : (cliqueRelEncode ((G, k), l)).get K = List.replicate k 1 := rfl
  have hVS0 : (cliqueRelEncode ((G, k), l)).get VERT_STREAM = encVerts l := rfl
  have hET0 : (cliqueRelEncode ((G, k), l)).get EDGE_TALLY = List.replicate G.2.length 1 := rfl
  have hVT0 : (cliqueRelEncode ((G, k), l)).get VERT_TALLY = List.replicate l.length 1 := rfl
  -- unfold the program into nested check evals
  have heval : cliqueRelCmd.eval (cliqueRelEncode ((G, k), l))
      = checkClique.eval (checkNodup.eval (checkLen.eval (checkOfType.eval
          (checkWf.eval ((Cmd.op (.appendOne OUTPUT)).eval
            (cliqueRelEncode ((G, k), l))))))) := by
    show (Cmd.op (.appendOne OUTPUT) ;; checkWf ;; checkOfType ;; checkLen ;;
      checkNodup ;; checkClique).eval _ = _
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  -- step 0: `appendOne OUTPUT` makes `OUTPUT = [1]`
  set s1 := (Cmd.op (.appendOne OUTPUT)).eval (cliqueRelEncode ((G, k), l)) with hs1
  have hs1eq : s1 = (cliqueRelEncode ((G, k), l)).set OUTPUT [1] := by
    rw [hs1, Cmd.eval_op]; simp only [Op.eval, hO0, List.nil_append]
  have hO1 : s1.get OUTPUT = [if true then 1 else 0] := by
    rw [hs1eq, State.get_set_eq]; rfl
  have hN1 : s1.get NUMV = List.replicate G.1 1 := by
    rw [hs1eq, State.get_set_ne _ _ _ _ (by decide : (NUMV : Var) ≠ OUTPUT), hN0]
  have hE1 : s1.get EDGE_STREAM = encEdges G.2 := by
    rw [hs1eq, State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ OUTPUT), hE0]
  have hK1 : s1.get K = List.replicate k 1 := by
    rw [hs1eq, State.get_set_ne _ _ _ _ (by decide : (K : Var) ≠ OUTPUT), hK0]
  have hVS1 : s1.get VERT_STREAM = encVerts l := by
    rw [hs1eq, State.get_set_ne _ _ _ _ (by decide : (VERT_STREAM : Var) ≠ OUTPUT), hVS0]
  have hET1 : s1.get EDGE_TALLY = List.replicate G.2.length 1 := by
    rw [hs1eq, State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ OUTPUT), hET0]
  have hVT1 : s1.get VERT_TALLY = List.replicate l.length 1 := by
    rw [hs1eq, State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ OUTPUT), hVT0]
  -- check 1: fgraph_wf
  obtain ⟨hWfOut, hWfFr⟩ := checkWf_run s1 G.2 G.1 true hE1 hET1 hN1 hO1
  set s2 := checkWf.eval s1 with hs2
  have hN2 : s2.get NUMV = List.replicate G.1 1 := by
    rw [hWfFr NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hN1]
  have hK2 : s2.get K = List.replicate k 1 := by
    rw [hWfFr K (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hK1]
  have hVS2 : s2.get VERT_STREAM = encVerts l := by
    rw [hWfFr VERT_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hVS1]
  have hVT2 : s2.get VERT_TALLY = List.replicate l.length 1 := by
    rw [hWfFr VERT_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hVT1]
  have hE2 : s2.get EDGE_STREAM = encEdges G.2 := by
    rw [hWfFr EDGE_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hE1]
  have hET2 : s2.get EDGE_TALLY = List.replicate G.2.length 1 := by
    rw [hWfFr EDGE_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hET1]
  -- check 2: list_ofFlatType
  obtain ⟨hOtOut, hOtFr⟩ := checkOfType_run s2 l G.1 (true && edgesWf G.1 G.2)
    hVS2 hVT2 hN2 hWfOut
  set s3 := checkOfType.eval s2 with hs3
  have hK3 : s3.get K = List.replicate k 1 := by
    rw [hOtFr K (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hK2]
  have hVS3 : s3.get VERT_STREAM = encVerts l := by
    rw [hOtFr VERT_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hVS2]
  have hVT3 : s3.get VERT_TALLY = List.replicate l.length 1 := by
    rw [hOtFr VERT_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hVT2]
  have hE3 : s3.get EDGE_STREAM = encEdges G.2 := by
    rw [hOtFr EDGE_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hE2]
  have hET3 : s3.get EDGE_TALLY = List.replicate G.2.length 1 := by
    rw [hOtFr EDGE_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hET2]
  -- check 3: l.length = k
  obtain ⟨hLenOut, hLenFr⟩ := checkLen_run s3 k l.length
    (true && edgesWf G.1 G.2 && allLt G.1 l) hVT3 hK3 hOtOut
  set s4 := checkLen.eval s3 with hs4
  have hVS4 : s4.get VERT_STREAM = encVerts l := by
    rw [hLenFr VERT_STREAM (by decide) (by decide) (by decide), hVS3]
  have hVT4 : s4.get VERT_TALLY = List.replicate l.length 1 := by
    rw [hLenFr VERT_TALLY (by decide) (by decide) (by decide), hVT3]
  have hE4 : s4.get EDGE_STREAM = encEdges G.2 := by
    rw [hLenFr EDGE_STREAM (by decide) (by decide) (by decide), hE3]
  have hET4 : s4.get EDGE_TALLY = List.replicate G.2.length 1 := by
    rw [hLenFr EDGE_TALLY (by decide) (by decide) (by decide), hET3]
  -- check 4: l.Nodup
  obtain ⟨hNodupOut, hNodupFr⟩ := checkNodup_run s4 l
    (true && edgesWf G.1 G.2 && allLt G.1 l && decide (l.length = k)) hVS4 hVT4 hLenOut
  set s5 := checkNodup.eval s4 with hs5
  have hVS5 : s5.get VERT_STREAM = encVerts l := by
    rw [hNodupFr VERT_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hVS4]
  have hVT5 : s5.get VERT_TALLY = List.replicate l.length 1 := by
    rw [hNodupFr VERT_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hVT4]
  have hE5 : s5.get EDGE_STREAM = encEdges G.2 := by
    rw [hNodupFr EDGE_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hE4]
  have hET5 : s5.get EDGE_TALLY = List.replicate G.2.length 1 := by
    rw [hNodupFr EDGE_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hET4]
  -- check 5: clique adjacency
  obtain ⟨hClqOut, _⟩ := checkClique_run s5 G.2 l
    (true && edgesWf G.1 G.2 && allLt G.1 l && decide (l.length = k) && nodupB l)
    hVS5 hVT5 hE5 hET5 hNodupOut
  -- the final output bit
  have hfinal : (cliqueRelCmd.eval (cliqueRelEncode ((G, k), l))).get OUTPUT
      = [if (edgesWf G.1 G.2 && allLt G.1 l && decide (l.length = k) && nodupB l
            && cliqueB G.2 l) then 1 else 0] := by
    rw [heval, hClqOut]
    simp only [Bool.true_and]
  -- bridge to `cliqueRel`
  have hO0' : (cliqueRelCmd.eval (cliqueRelEncode ((G, k), l))).get (0 : Var)
      = [if (edgesWf G.1 G.2 && allLt G.1 l && decide (l.length = k) && nodupB l
            && cliqueB G.2 l) then 1 else 0] := hfinal
  refine ⟨?_, ?_⟩
  · show cliqueRel (G, k) l ↔ _
    rw [cliqueRel_iff_checks G k l, State.isAccept, hO0']
    cases (edgesWf G.1 G.2 && allLt G.1 l && decide (l.length = k) && nodupB l
      && cliqueB G.2 l) <;> simp
  · show ¬ cliqueRel (G, k) l ↔ _
    rw [cliqueRel_iff_checks G k l, State.isReject, hO0']
    cases (edgesWf G.1 G.2 && allLt G.1 l && decide (l.length = k) && nodupB l
      && cliqueB G.2 l) <;> simp

/-! ### Cost lemmas (top-down Task 1, step 5)

Mirrors `EvalCnfCmd`'s `_cost` quartet. **Key simplification (this session): the
cost proofs use *length-only* loop invariants** (`M i s := (s.get reg).length ≤ …`)
rather than the behavioural invariants (`RNInv`/`COInv`/…) the run-lemmas use.
Body cost depends only on the register *lengths* it touches, and those lengths are
non-increasing through every loop here (streams are consumed by `tail`, scratch
copies only shrink), so a length bound is preserved by `hM` regardless of the
control-flow branch — no need to track the exact stream contents or the accumulated
predicate. Each loop is closed by `Cmd.cost_forBnd_le` with `B` = a uniform
per-iteration body-cost bound. -/

/-- Dropping a prefix of the vertex list only shortens its encoding. -/
private theorem encVerts_drop_length_le (l : List fvertex) (i : Nat) :
    (encVerts (l.drop i)).length ≤ (encVerts l).length := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
    cases l with
    | nil => simp
    | cons v l =>
      rw [List.drop_succ_cons]
      refine (ih l).trans ?_
      rw [encVerts_cons]; simp only [List.length_append, List.length_cons]; omega

/-- Dropping a prefix of the edge list only shortens its encoding. -/
private theorem encEdges_drop_length_le (edges : List fedge) (i : Nat) :
    (encEdges (edges.drop i)).length ≤ (encEdges edges).length := by
  induction i generalizing edges with
  | zero => simp
  | succ i ih =>
    cases edges with
    | nil => simp
    | cons e edges =>
      rw [List.drop_succ_cons]
      refine (ih edges).trans ?_
      rw [encEdges_cons]; simp only [List.length_append, List.length_cons]; omega

/-- A vertex value is bounded by any ceiling on its stream's encoding (proved in
a clean context to avoid `omega` atom-pollution from the loop-body state). -/
private theorem vert_getElem_le (l : List fvertex) (i : Nat) (hi : i < l.length)
    (P : Nat) (hP : (encVerts (l.drop i)).length ≤ P) : l[i]'hi ≤ P := by
  refine Nat.le_trans ?_ hP
  rw [List.drop_eq_getElem_cons hi, encVerts_cons, List.length_append,
    List.length_replicate]
  exact Nat.le_add_right _ _

/-- Both endpoints of an edge are bounded by any ceiling on the edge stream's
encoding (clean-context helper, as `vert_getElem_le`). -/
private theorem edge_getElem_le (edges : List fedge) (i : Nat) (hi : i < edges.length)
    (P : Nat) (hP : (encEdges (edges.drop i)).length ≤ P) :
    (edges[i]'hi).1 ≤ P ∧ (edges[i]'hi).2 ≤ P := by
  constructor
  · refine Nat.le_trans ?_ hP
    rw [List.drop_eq_getElem_cons hi, encEdges_cons, List.length_append,
      List.length_replicate]
    exact Nat.le_add_right _ _
  · refine Nat.le_trans ?_ hP
    rw [List.drop_eq_getElem_cons hi, encEdges_cons, List.length_append]
    refine Nat.le_trans ?_ (Nat.le_add_left _ _)
    rw [List.length_cons]
    refine Nat.le_trans ?_ (Nat.le_succ _)
    rw [List.length_append, List.length_replicate]
    exact Nat.le_add_right _ _

/-- `readNumBody` never grows `stream` and costs at most `S + 7` when
`|stream| ≤ S`. The uniform per-iteration ingredient for `readNum_cost`. -/
private theorem readNumBody_effect (dst stream : Var) (S : Nat) (w : State)
    (hsd : stream ≠ dst) (hsHead : stream ≠ HEAD) (hsInbk : stream ≠ INBLK)
    (hsSkip : stream ≠ SKIPR) (hw : (State.get w stream).length ≤ S) :
    (State.get ((readNumBody dst stream).eval w) stream).length ≤ S
    ∧ (readNumBody dst stream).cost w ≤ S + 7 := by
  -- the inner `ifBit HEAD (appendOne dst) (clear INBLK)` never touches `stream`,
  -- and costs at most `2`
  have hif_frame : ∀ t : State,
      State.get ((Cmd.ifBit HEAD (Cmd.op (.appendOne dst))
          (Cmd.op (.clear INBLK))).eval t) stream = State.get t stream := by
    intro t
    by_cases hh : State.get t HEAD = [1]
    · rw [Cmd.eval_ifBit_true _ _ _ _ hh, Cmd.eval_op]; simp only [Op.eval]
      rw [State.get_set_ne _ _ _ _ hsd]
    · rw [Cmd.eval_ifBit_false _ _ _ _ hh, Cmd.eval_op]; simp only [Op.eval]
      rw [State.get_set_ne _ _ _ _ hsInbk]
  have hif_cost : ∀ t : State,
      (Cmd.ifBit HEAD (Cmd.op (.appendOne dst)) (Cmd.op (.clear INBLK))).cost t ≤ 2 := by
    intro t
    by_cases hh : State.get t HEAD = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ hh]; simp [Cmd.cost_op, Op.cost]
    · rw [Cmd.cost_ifBit_false _ _ _ _ hh]; simp [Cmd.cost_op, Op.cost]
  by_cases hIB : State.get w INBLK = [1]
  · -- active branch: head ;; tail stream ;; ifBit
    have hhead : State.get ((Cmd.op (.head HEAD stream)).eval w) stream
        = State.get w stream := by
      rw [Cmd.eval_op]; simp only [Op.eval]; rw [State.get_set_ne _ _ _ _ hsHead]
    have htail : State.get ((Cmd.op (.tail stream stream)).eval
        ((Cmd.op (.head HEAD stream)).eval w)) stream
        = (State.get w stream).tail := by
      rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq]; rw [hhead]
    constructor
    · -- length
      have heval : (readNumBody dst stream).eval w
          = (Cmd.ifBit HEAD (Cmd.op (.appendOne dst)) (Cmd.op (.clear INBLK))).eval
              ((Cmd.op (.tail stream stream)).eval ((Cmd.op (.head HEAD stream)).eval w)) := by
        show (Cmd.ifBit INBLK _ _).eval w = _
        rw [Cmd.eval_ifBit_true _ _ _ _ hIB, Cmd.eval_seq, Cmd.eval_seq]
      rw [heval, hif_frame, htail, List.length_tail]
      omega
    · -- cost
      have hcost : (readNumBody dst stream).cost w
          = 1 + (Cmd.op (.head HEAD stream) ;; Cmd.op (.tail stream stream) ;;
              Cmd.ifBit HEAD (Cmd.op (.appendOne dst)) (Cmd.op (.clear INBLK))).cost w := by
        show (Cmd.ifBit INBLK _ _).cost w = _
        rw [Cmd.cost_ifBit_true _ _ _ _ hIB]
      rw [hcost, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_seq, Cmd.cost_op]
      have htlcost : Op.cost (.tail stream stream) ((Cmd.op (.head HEAD stream)).eval w)
          = (State.get w stream).length + 1 := by
        show (State.get ((Cmd.op (.head HEAD stream)).eval w) stream).length + 1 = _
        rw [hhead]
      rw [htlcost]
      have hile := hif_cost ((Cmd.op (.tail stream stream)).eval
        ((Cmd.op (.head HEAD stream)).eval w))
      simp only [Op.cost]
      omega
  · -- idle branch: cSkip
    have heval : (readNumBody dst stream).eval w = w.set SKIPR [1] := by
      show (Cmd.ifBit INBLK _ _).eval w = _
      rw [Cmd.eval_ifBit_false _ _ _ _ hIB, cSkip_eval]
    have hcost : (readNumBody dst stream).cost w = 1 + 3 := by
      show (Cmd.ifBit INBLK _ _).cost w = _
      rw [Cmd.cost_ifBit_false _ _ _ _ hIB, cSkip_cost]
    constructor
    · rw [heval, State.get_set_ne _ _ _ _ hsSkip]; exact hw
    · omega

/-- **`readNum` cost bound.** Reading (draining) `stream` costs `≤ 2·S² + 7·S + 7`
where `S = |stream|` at entry. No block-form hypothesis: the bound holds for any
stream content (the loop drains one cell/iteration, each a `tail` of cost `≤ S`). -/
private theorem readNum_cost (st : State) (dst stream idx : Var)
    (hsd : stream ≠ dst) (hsi : stream ≠ idx)
    (hsHead : stream ≠ HEAD) (hsInbk : stream ≠ INBLK) (hsSkip : stream ≠ SKIPR) :
    (readNum dst stream idx).cost st
      ≤ 2 * (State.get st stream).length * (State.get st stream).length
          + 7 * (State.get st stream).length + 7 := by
  set S := (State.get st stream).length with hS
  have hstreamlen : (State.get st stream).length = S := hS.symm
  -- init prefix evaluation
  have e1 : (Cmd.op (.clear dst)).eval st = st.set dst [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e2 : (Cmd.op (.clear INBLK)).eval (st.set dst [])
      = (st.set dst []).set INBLK [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e3 : (Cmd.op (.appendOne INBLK)).eval ((st.set dst []).set INBLK [])
      = ((st.set dst []).set INBLK []).set INBLK [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [State.get_set_eq, List.nil_append]
  set s0 := ((st.set dst []).set INBLK []).set INBLK [1] with hs0
  have hcost_eq : (readNum dst stream idx).cost st
      = 6 + (Cmd.forBnd idx stream (readNumBody dst stream)).cost s0 := by
    show (Cmd.cost (_ ;; _ ;; _ ;; _) st) = _
    rw [Cmd.cost_seq, e1, Cmd.cost_seq, e2, Cmd.cost_seq, e3, Cmd.cost_op,
      Cmd.cost_op, Cmd.cost_op]
    simp only [Op.cost, readNumBody]; omega
  have hs0stream : State.get s0 stream = State.get st stream := by
    rw [State.get_set_ne _ _ _ _ hsInbk, State.get_set_ne _ _ _ _ hsInbk,
      State.get_set_ne _ _ _ _ hsd]
  have hbound : (State.get s0 stream).length = S := by rw [hs0stream, hstreamlen]
  have hloop : (Cmd.forBnd idx stream (readNumBody dst stream)).cost s0
      ≤ 1 + S * (S + 7) + S * S := by
    have h := Cmd.cost_forBnd_le idx stream (readNumBody dst stream) s0 (S + 7)
      (fun _ s => (State.get s stream).length ≤ S)
      hbound.le
      (fun i s _ hM => (readNumBody_effect dst stream S (s.set idx (List.replicate i 1))
          hsd hsHead hsInbk hsSkip
          (by rw [State.get_set_ne _ _ _ _ hsi]; exact hM)).1)
      (fun i s _ hM => (readNumBody_effect dst stream S (s.set idx (List.replicate i 1))
          hsd hsHead hsInbk hsSkip
          (by rw [State.get_set_ne _ _ _ _ hsi]; exact hM)).2)
    rw [hbound] at h; exact h
  rw [hcost_eq]
  have hr1 : S * (S + 7) = S * S + 7 * S := by ring
  have hr2 : 2 * S * S = S * S + S * S := by ring
  omega

/-- **`readNum` never grows its stream** (it drains one block, leaving a shorter
suffix). Used to bound the second `readNum`'s stream in double-read loops. -/
private theorem readNum_stream_le (st : State) (dst stream idx : Var)
    (hsd : stream ≠ dst) (hsi : stream ≠ idx) (hsHead : stream ≠ HEAD)
    (hsInbk : stream ≠ INBLK) (hsSkip : stream ≠ SKIPR) :
    (State.get ((readNum dst stream idx).eval st) stream).length
      ≤ (State.get st stream).length := by
  set S := (State.get st stream).length with hS
  have e1 : (Cmd.op (.clear dst)).eval st = st.set dst [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e2 : (Cmd.op (.clear INBLK)).eval (st.set dst [])
      = (st.set dst []).set INBLK [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e3 : (Cmd.op (.appendOne INBLK)).eval ((st.set dst []).set INBLK [])
      = ((st.set dst []).set INBLK []).set INBLK [1] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [State.get_set_eq, List.nil_append]
  set s0 := ((st.set dst []).set INBLK []).set INBLK [1] with hs0
  have eP : (readNum dst stream idx).eval st
      = (Cmd.forBnd idx stream (readNumBody dst stream)).eval s0 := by
    show (Cmd.eval (_ ;; _ ;; _ ;; _) st) = _
    rw [Cmd.eval_seq, e1, Cmd.eval_seq, e2, Cmd.eval_seq, e3]; rfl
  have hs0stream : State.get s0 stream = State.get st stream := by
    rw [State.get_set_ne _ _ _ _ hsInbk, State.get_set_ne _ _ _ _ hsInbk,
      State.get_set_ne _ _ _ _ hsd]
  rw [eP, Cmd.eval_forBnd]
  exact Cmd.foldlState_range_induct (readNumBody dst stream) idx
    (State.get s0 stream).length s0
    (fun _ s => (State.get s stream).length ≤ S)
    (le_of_eq (congrArg List.length hs0stream))
    (fun i s _ hM => (readNumBody_effect dst stream S (s.set idx (List.replicate i 1))
        hsd hsHead hsInbk hsSkip
        (by rw [State.get_set_ne _ _ _ _ hsi]; exact hM)).1)

/-- **`ltBit` cost bound.** The unary-`<` gadget costs `≤ a² + a·b + a + b + 5`
where `a = |A|`, `b = |B|` at entry (`copy` + a lockstep drain of `|A|` iterations,
each a `tail` on a register of length `≤ b`). -/
private theorem ltBit_cost (st : State) (dst A B idx : Var)
    (hALT : A ≠ LT_B) (hidxLT : idx ≠ LT_B) :
    (ltBit dst A B idx).cost st
      ≤ (State.get st A).length * (State.get st A).length
          + (State.get st A).length * (State.get st B).length
          + (State.get st A).length + (State.get st B).length + 5 := by
  set a := (State.get st A).length with ha
  set b := (State.get st B).length with hb
  have ecopy : (Cmd.op (.copy LT_B B)).eval st = st.set LT_B (State.get st B) := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set s1 := st.set LT_B (State.get st B) with hs1
  have hLT1 : (State.get s1 LT_B).length = b := by rw [State.get_set_eq]
  have hA1 : (State.get s1 A).length = a := by rw [State.get_set_ne _ _ _ _ hALT]
  have hcost_eq : (ltBit dst A B idx).cost st
      = 4 + b + (Cmd.forBnd idx A (Cmd.op (.tail LT_B LT_B))).cost s1 := by
    show (Cmd.cost (_ ;; _ ;; _) st) = _
    rw [Cmd.cost_seq, ecopy, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
    simp only [Op.cost]; omega
  have hloop : (Cmd.forBnd idx A (Cmd.op (.tail LT_B LT_B))).cost s1
      ≤ 1 + a * (b + 1) + a * a := by
    have h := Cmd.cost_forBnd_le idx A (Cmd.op (.tail LT_B LT_B)) s1 (b + 1)
      (fun _ s => (State.get s LT_B).length ≤ b)
      hLT1.le
      (fun i s _ hM => by
        show (State.get ((Cmd.op (.tail LT_B LT_B)).eval
            (s.set idx (List.replicate i 1))) LT_B).length ≤ b
        rw [Cmd.eval_op]; simp only [Op.eval, State.get_set_eq, List.length_tail]
        rw [State.get_set_ne _ _ _ _ (Ne.symm hidxLT)]
        have : (State.get s LT_B).length ≤ b := hM
        omega)
      (fun i s _ hM => by
        show (State.get (s.set idx (List.replicate i 1)) LT_B).length + 1 ≤ b + 1
        rw [State.get_set_ne _ _ _ _ (Ne.symm hidxLT)]
        have : (State.get s LT_B).length ≤ b := hM
        omega)
    rw [hA1] at h; exact h
  rw [hcost_eq]
  have hr : a * (b + 1) = a * b + a := by ring
  omega

/-- **`checkLen` cost bound.** Constant-cost above the two tally lengths. -/
private theorem checkLen_cost (st : State) :
    checkLen.cost st
      ≤ (State.get st VERT_TALLY).length + (State.get st K).length + 6 := by
  have he : checkLen.cost st
      = 1 + ((State.get st VERT_TALLY).length + (State.get st K).length + 1)
          + (Cmd.ifBit RES1 cSkip cReject).cost
              ((Cmd.op (.eqBit RES1 VERT_TALLY K)).eval st) := by
    show (Cmd.cost (_ ;; _) st) = _
    rw [Cmd.cost_seq, Cmd.cost_op]; simp only [Op.cost]
  have hif : (Cmd.ifBit RES1 cSkip cReject).cost
      ((Cmd.op (.eqBit RES1 VERT_TALLY K)).eval st) ≤ 4 := by
    by_cases hbit : State.get ((Cmd.op (.eqBit RES1 VERT_TALLY K)).eval st) RES1 = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ hbit, cSkip_cost]
    · rw [Cmd.cost_ifBit_false _ _ _ _ hbit, cReject_cost]
  omega

/-- Uniform per-iteration body-cost bound for the `checkOfType` loop, given a
length ceiling `P` on the encoded vertex stream and `numV`. Mirrors
`checkOfType_step` but accounts costs. -/
private theorem checkOfType_body_cost (l : List fvertex) (numV P : Nat) (b : Bool)
    (st : State) (hNUMV : st.get NUMV = List.replicate numV 1)
    (hVP : (encVerts l).length ≤ P) (hnP : numV ≤ P)
    (i : Nat) (s : State) (hi : i < l.length) (h : COInv l numV b st i s) :
    (readNum VALA VSCAN IDX2 ;; ltBit RES1 VALA NUMV IDX3 ;;
      Cmd.ifBit RES1 cSkip cReject).cost (s.set IDX1 (List.replicate i 1))
      ≤ 4 * (P * P) + 9 * P + 18 := by
  obtain ⟨hVSCAN, _, hframe⟩ := h
  set w := s.set IDX1 (List.replicate i 1) with hw
  have hVS_in : State.get w VSCAN
      = List.replicate (l[i]'hi) 1 ++ 0 :: encVerts (l.drop (i + 1)) := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VSCAN : Var) ≠ IDX1), hVSCAN,
      List.drop_eq_getElem_cons hi, encVerts_cons]
  -- length ceiling on VSCAN at loop entry
  have hVSlen : (State.get w VSCAN).length ≤ P := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VSCAN : Var) ≠ IDX1), hVSCAN]
    exact (encVerts_drop_length_le l i).trans hVP
  have hli : l[i]'hi ≤ P := by
    have h1 : l[i]'hi ≤ (encVerts (l.drop i)).length := by
      rw [List.drop_eq_getElem_cons hi, encVerts_cons, List.length_append,
        List.length_replicate]
      exact Nat.le_add_right _ _
    exact h1.trans ((encVerts_drop_length_le l i).trans hVP)
  -- run `readNum` to expose the mid-state registers
  obtain ⟨hVALA, hVS2, hRNframe⟩ := readNum_run w
    (l[i]'hi) (encVerts (l.drop (i + 1))) VALA VSCAN IDX2 hVS_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hNUMV1 : ((readNum VALA VSCAN IDX2).eval w).get NUMV = List.replicate numV 1 := by
    rw [hRNframe NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hw,
      State.get_set_ne _ _ _ _ (by decide : (NUMV : Var) ≠ IDX1),
      hframe NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hNUMV]
  -- cost decomposition
  have hcost : (readNum VALA VSCAN IDX2 ;; ltBit RES1 VALA NUMV IDX3 ;;
      Cmd.ifBit RES1 cSkip cReject).cost w
      = 1 + (readNum VALA VSCAN IDX2).cost w
          + (1 + (ltBit RES1 VALA NUMV IDX3).cost ((readNum VALA VSCAN IDX2).eval w)
             + (Cmd.ifBit RES1 cSkip cReject).cost
                 ((ltBit RES1 VALA NUMV IDX3).eval ((readNum VALA VSCAN IDX2).eval w))) := by
    rw [Cmd.cost_seq, Cmd.cost_seq]
  -- bound the three pieces
  have hrn := readNum_cost w VALA VSCAN IDX2 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hrn' : (readNum VALA VSCAN IDX2).cost w ≤ 2 * (P * P) + 7 * P + 7 := by
    refine hrn.trans ?_
    nlinarith [hVSlen, Nat.mul_le_mul hVSlen hVSlen]
  have hlt := ltBit_cost ((readNum VALA VSCAN IDX2).eval w) RES1 VALA NUMV IDX3
    (by decide) (by decide)
  have hlt' : (ltBit RES1 VALA NUMV IDX3).cost ((readNum VALA VSCAN IDX2).eval w)
      ≤ 2 * (P * P) + 2 * P + 5 := by
    refine hlt.trans ?_
    rw [hVALA, hNUMV1, List.length_replicate, List.length_replicate]
    nlinarith [hli, hnP, Nat.mul_le_mul hli hli, Nat.mul_le_mul hli hnP]
  have hif : (Cmd.ifBit RES1 cSkip cReject).cost
      ((ltBit RES1 VALA NUMV IDX3).eval ((readNum VALA VSCAN IDX2).eval w)) ≤ 4 := by
    by_cases hbit : State.get ((ltBit RES1 VALA NUMV IDX3).eval
        ((readNum VALA VSCAN IDX2).eval w)) RES1 = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ hbit, cSkip_cost]
    · rw [Cmd.cost_ifBit_false _ _ _ _ hbit, cReject_cost]
  rw [hcost]; omega

/-- **`checkOfType` cost bound** (single loop, cubic in the length ceiling `P`). -/
private theorem checkOfType_cost (st : State) (l : List fvertex) (numV P : Nat) (b : Bool)
    (hVS : st.get VERT_STREAM = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hNUMV : st.get NUMV = List.replicate numV 1)
    (hO : st.get OUTPUT = [if b then 1 else 0])
    (hVP : (encVerts l).length ≤ P) (hmP : l.length ≤ P) (hnP : numV ≤ P) :
    checkOfType.cost st ≤ 5 * (P * P * P) + 11 * (P * P) + 20 * P + 3 := by
  have eInit : (Cmd.op (.copy VSCAN VERT_STREAM)).eval st = st.set VSCAN (encVerts l) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVS]
  have hcost_eq : checkOfType.cost st
      = 1 + ((encVerts l).length + 1)
          + (Cmd.forBnd IDX1 VERT_TALLY
              (readNum VALA VSCAN IDX2 ;; ltBit RES1 VALA NUMV IDX3 ;;
               Cmd.ifBit RES1 cSkip cReject)).cost (st.set VSCAN (encVerts l)) := by
    show (Cmd.cost (Cmd.op (.copy VSCAN VERT_STREAM) ;; _) st) = _
    rw [Cmd.cost_seq, Cmd.cost_op, eInit]
    simp only [Op.cost]; rw [hVS]
  set s0 := st.set VSCAN (encVerts l) with hs0
  have hNUMV0 : s0.get NUMV = List.replicate numV 1 := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (NUMV : Var) ≠ VSCAN), hNUMV]
  have hVS0 : s0.get VERT_STREAM = encVerts l := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (VERT_STREAM : Var) ≠ VSCAN), hVS]
  have hVT0 : s0.get VERT_TALLY = List.replicate l.length 1 := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ VSCAN), hVT]
  have hO0 : s0.get OUTPUT = [if b then 1 else 0] := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ VSCAN), hO]
  have hbase : COInv l numV b s0 0 s0 := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [hs0, State.get_set_eq, List.drop_zero]
    · rw [hO0, List.take_zero]; simp only [allLt, List.all_nil, Bool.and_true]
  have hblen : (s0.get VERT_TALLY).length = l.length := by
    rw [hVT0, List.length_replicate]
  have hloop : (Cmd.forBnd IDX1 VERT_TALLY
      (readNum VALA VSCAN IDX2 ;; ltBit RES1 VALA NUMV IDX3 ;;
       Cmd.ifBit RES1 cSkip cReject)).cost s0
      ≤ 1 + l.length * (4 * (P * P) + 9 * P + 18) + l.length * l.length := by
    have h := Cmd.cost_forBnd_le IDX1 VERT_TALLY
      (readNum VALA VSCAN IDX2 ;; ltBit RES1 VALA NUMV IDX3 ;;
       Cmd.ifBit RES1 cSkip cReject) s0 (4 * (P * P) + 9 * P + 18)
      (COInv l numV b s0) hbase
      (fun i s hi h => checkOfType_step l numV b s0 hNUMV0 i s (by rwa [hblen] at hi) h)
      (fun i s hi h => checkOfType_body_cost l numV P b s0 hNUMV0 hVP hnP i s
        (by rwa [hblen] at hi) h)
    rw [hblen] at h; exact h
  rw [hcost_eq]
  have h1 : l.length * (4 * (P * P) + 9 * P + 18) ≤ P * (4 * (P * P) + 9 * P + 18) :=
    Nat.mul_le_mul_right _ hmP
  have h2 : l.length * l.length ≤ P * P := Nat.mul_le_mul hmP hmP
  have h3 : (encVerts l).length ≤ P := hVP
  have h4 : P * (4 * (P * P) + 9 * P + 18) = 4 * (P * P * P) + 9 * (P * P) + 18 * P := by ring
  omega

/-- Uniform per-iteration body-cost bound for the `checkWf` loop. -/
private theorem checkWf_body_cost (edges : List fedge) (numV P : Nat) (b : Bool)
    (st : State) (hNUMV : st.get NUMV = List.replicate numV 1)
    (hEP : (encEdges edges).length ≤ P) (hnP : numV ≤ P)
    (i : Nat) (s : State) (hi : i < edges.length) (h : CWfInv edges numV b st i s) :
    (readNum VALA ESCAN IDX2 ;; readNum VALB ESCAN IDX2 ;;
      ltBit RES1 VALA NUMV IDX3 ;; ltBit RES2 VALB NUMV IDX3 ;;
      Cmd.ifBit RES1 (Cmd.ifBit RES2 cSkip cReject) cReject).cost
        (s.set IDX1 (List.replicate i 1))
      ≤ 8 * (P * P) + 18 * P + 33 := by
  obtain ⟨hESCAN, _, hframe⟩ := h
  set w := s.set IDX1 (List.replicate i 1) with hw
  have hwNUMV : State.get w NUMV = State.get s NUMV := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (NUMV : Var) ≠ IDX1)]
  have hESCAN_in : State.get w ESCAN
      = List.replicate (edges[i]'hi).1 1 ++ 0 ::
          (List.replicate (edges[i]'hi).2 1 ++ 0 :: encEdges (edges.drop (i + 1))) := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (ESCAN : Var) ≠ IDX1), hESCAN,
      List.drop_eq_getElem_cons hi, encEdges_cons]
  have hESlen : (State.get w ESCAN).length ≤ P := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (ESCAN : Var) ≠ IDX1), hESCAN]
    exact (encEdges_drop_length_le edges i).trans hEP
  obtain ⟨he1, he2⟩ := edge_getElem_le edges i hi P
    ((encEdges_drop_length_le edges i).trans hEP)
  -- run the two readNums to expose the mid-state registers
  obtain ⟨hVALA1, hESCAN1, hRN1frame⟩ := readNum_run w (edges[i]'hi).1
    (List.replicate (edges[i]'hi).2 1 ++ 0 :: encEdges (edges.drop (i + 1)))
    VALA ESCAN IDX2 hESCAN_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALA ESCAN IDX2).eval w with hs1
  obtain ⟨hVALB2, hESCAN2, hRN2frame⟩ := readNum_run s1 (edges[i]'hi).2
    (encEdges (edges.drop (i + 1))) VALB ESCAN IDX2 hESCAN1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s2 := (readNum VALB ESCAN IDX2).eval s1 with hs2
  have hVALA2 : s2.get VALA = List.replicate (edges[i]'hi).1 1 := by
    rw [hRN2frame VALA (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hVALA1]
  have hNUMV2 : s2.get NUMV = List.replicate numV 1 := by
    rw [hRN2frame NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide),
      hRN1frame NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hwNUMV,
      hframe NUMV (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hNUMV]
  obtain ⟨hRES1, hLT1frame⟩ := ltBit_run s2 (edges[i]'hi).1 numV RES1 VALA NUMV IDX3
    hVALA2 hNUMV2 (by decide) (by decide)
  set s3 := (ltBit RES1 VALA NUMV IDX3).eval s2 with hs3
  have hVALB3 : s3.get VALB = List.replicate (edges[i]'hi).2 1 := by
    rw [hLT1frame VALB (by decide) (by decide) (by decide), hVALB2]
  have hNUMV3 : s3.get NUMV = List.replicate numV 1 := by
    rw [hLT1frame NUMV (by decide) (by decide) (by decide), hNUMV2]
  -- length ceiling on ESCAN at s1 (readNum does not grow it)
  have hES1len : (State.get s1 ESCAN).length ≤ P :=
    (readNum_stream_le w VALA ESCAN IDX2 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hESlen
  -- the five cost pieces
  have b1 : (readNum VALA ESCAN IDX2).cost w ≤ 2 * (P * P) + 7 * P + 7 := by
    refine (readNum_cost w VALA ESCAN IDX2 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ?_
    nlinarith [hESlen, Nat.mul_le_mul hESlen hESlen]
  have b2 : (readNum VALB ESCAN IDX2).cost s1 ≤ 2 * (P * P) + 7 * P + 7 := by
    refine (readNum_cost s1 VALB ESCAN IDX2 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ?_
    nlinarith [hES1len, Nat.mul_le_mul hES1len hES1len]
  have b3 : (ltBit RES1 VALA NUMV IDX3).cost s2 ≤ 2 * (P * P) + 2 * P + 5 := by
    refine (ltBit_cost s2 RES1 VALA NUMV IDX3 (by decide) (by decide)).trans ?_
    rw [hVALA2, hNUMV2, List.length_replicate, List.length_replicate]
    nlinarith [he1, hnP, Nat.mul_le_mul he1 he1, Nat.mul_le_mul he1 hnP]
  have b4 : (ltBit RES2 VALB NUMV IDX3).cost s3 ≤ 2 * (P * P) + 2 * P + 5 := by
    refine (ltBit_cost s3 RES2 VALB NUMV IDX3 (by decide) (by decide)).trans ?_
    rw [hVALB3, hNUMV3, List.length_replicate, List.length_replicate]
    nlinarith [he2, hnP, Nat.mul_le_mul he2 he2, Nat.mul_le_mul he2 hnP]
  have b5 : (Cmd.ifBit RES1 (Cmd.ifBit RES2 cSkip cReject) cReject).cost
      ((ltBit RES2 VALB NUMV IDX3).eval s3) ≤ 5 := by
    set X := (ltBit RES2 VALB NUMV IDX3).eval s3 with hX
    by_cases h1 : State.get X RES1 = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ h1]
      by_cases h2 : State.get X RES2 = [1]
      · rw [Cmd.cost_ifBit_true _ _ _ _ h2, cSkip_cost]
      · rw [Cmd.cost_ifBit_false _ _ _ _ h2, cReject_cost]
    · rw [Cmd.cost_ifBit_false _ _ _ _ h1, cReject_cost]; omega
  rw [Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, ← hs1, ← hs2, ← hs3]
  omega


/-- **`checkWf` cost bound** (single loop, cubic in the length ceiling `P`). -/
private theorem checkWf_cost (st : State) (edges : List fedge) (numV P : Nat) (b : Bool)
    (hES : st.get EDGE_STREAM = encEdges edges)
    (hET : st.get EDGE_TALLY = List.replicate edges.length 1)
    (hNUMV : st.get NUMV = List.replicate numV 1)
    (hO : st.get OUTPUT = [if b then 1 else 0])
    (hEP : (encEdges edges).length ≤ P) (hmP : edges.length ≤ P) (hnP : numV ≤ P) :
    checkWf.cost st ≤ 8 * (P * P * P) + 20 * (P * P) + 35 * P + 3 := by
  have eInit : (Cmd.op (.copy ESCAN EDGE_STREAM)).eval st = st.set ESCAN (encEdges edges) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hES]
  have hcost_eq : checkWf.cost st
      = 1 + ((encEdges edges).length + 1)
          + (Cmd.forBnd IDX1 EDGE_TALLY
              (readNum VALA ESCAN IDX2 ;; readNum VALB ESCAN IDX2 ;;
               ltBit RES1 VALA NUMV IDX3 ;; ltBit RES2 VALB NUMV IDX3 ;;
               Cmd.ifBit RES1 (Cmd.ifBit RES2 cSkip cReject) cReject)).cost
              (st.set ESCAN (encEdges edges)) := by
    show (Cmd.cost (Cmd.op (.copy ESCAN EDGE_STREAM) ;; _) st) = _
    rw [Cmd.cost_seq, Cmd.cost_op, eInit]; simp only [Op.cost]; rw [hES]
  set s0 := st.set ESCAN (encEdges edges) with hs0
  have hNUMV0 : s0.get NUMV = List.replicate numV 1 := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (NUMV : Var) ≠ ESCAN), hNUMV]
  have hES0 : s0.get EDGE_STREAM = encEdges edges := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ ESCAN), hES]
  have hET0 : s0.get EDGE_TALLY = List.replicate edges.length 1 := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ ESCAN), hET]
  have hO0 : s0.get OUTPUT = [if b then 1 else 0] := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ ESCAN), hO]
  have hbase : CWfInv edges numV b s0 0 s0 := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [hs0, State.get_set_eq, List.drop_zero]
    · rw [hO0, List.take_zero]; simp only [edgesWf, List.all_nil, Bool.and_true]
  have hblen : (s0.get EDGE_TALLY).length = edges.length := by
    rw [hET0, List.length_replicate]
  have hloop : (Cmd.forBnd IDX1 EDGE_TALLY
      (readNum VALA ESCAN IDX2 ;; readNum VALB ESCAN IDX2 ;;
       ltBit RES1 VALA NUMV IDX3 ;; ltBit RES2 VALB NUMV IDX3 ;;
       Cmd.ifBit RES1 (Cmd.ifBit RES2 cSkip cReject) cReject)).cost s0
      ≤ 1 + edges.length * (8 * (P * P) + 18 * P + 33) + edges.length * edges.length := by
    have h := Cmd.cost_forBnd_le IDX1 EDGE_TALLY
      (readNum VALA ESCAN IDX2 ;; readNum VALB ESCAN IDX2 ;;
       ltBit RES1 VALA NUMV IDX3 ;; ltBit RES2 VALB NUMV IDX3 ;;
       Cmd.ifBit RES1 (Cmd.ifBit RES2 cSkip cReject) cReject) s0
      (8 * (P * P) + 18 * P + 33) (CWfInv edges numV b s0) hbase
      (fun i s hi h => checkWf_step edges numV b s0 hNUMV0 i s (by rwa [hblen] at hi) h)
      (fun i s hi h => checkWf_body_cost edges numV P b s0 hNUMV0 hEP hnP i s
        (by rwa [hblen] at hi) h)
    rw [hblen] at h; exact h
  rw [hcost_eq]
  have h1 : edges.length * (8 * (P * P) + 18 * P + 33) ≤ P * (8 * (P * P) + 18 * P + 33) :=
    Nat.mul_le_mul_right _ hmP
  have h2 : edges.length * edges.length ≤ P * P := Nat.mul_le_mul hmP hmP
  have h4 : P * (8 * (P * P) + 18 * P + 33) = 8 * (P * P * P) + 18 * (P * P) + 33 * P := by ring
  omega

/-- Uniform per-iteration body-cost bound for the `memberEdge` loop. -/
private theorem memberEdge_body_cost (va vb : Nat) (edges : List fedge) (P : Nat)
    (st : State) (hVALA : (st.get VALA).length ≤ P) (hVALB : (st.get VALB).length ≤ P)
    (hEP : (encEdges edges).length ≤ P)
    (i : Nat) (s : State) (hi : i < edges.length) (h : MEInv va vb edges st i s) :
    (readNum VALC ESCAN2 IDX4 ;; readNum VALD ESCAN2 IDX4 ;;
      Cmd.op (.eqBit RES1 VALC VALA) ;; Cmd.op (.eqBit RES2 VALD VALB) ;;
      Cmd.ifBit RES1
        (Cmd.ifBit RES2 (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND)) cSkip)
        cSkip).cost (s.set IDX3 (List.replicate i 1))
      ≤ 4 * (P * P) + 18 * P + 26 := by
  obtain ⟨hESCAN, _, hframe⟩ := h
  set w := s.set IDX3 (List.replicate i 1) with hw
  have hESCAN_in : State.get w ESCAN2
      = List.replicate (edges[i]'hi).1 1 ++ 0 ::
          (List.replicate (edges[i]'hi).2 1 ++ 0 :: encEdges (edges.drop (i + 1))) := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (ESCAN2 : Var) ≠ IDX3), hESCAN,
      List.drop_eq_getElem_cons hi, encEdges_cons]
  have hESlen : (State.get w ESCAN2).length ≤ P := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (ESCAN2 : Var) ≠ IDX3), hESCAN]
    exact (encEdges_drop_length_le edges i).trans hEP
  obtain ⟨he1, he2⟩ := edge_getElem_le edges i hi P
    ((encEdges_drop_length_le edges i).trans hEP)
  have hVALAw : (State.get w VALA).length ≤ P := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ IDX3),
      hframe VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hVALA
  have hVALBw : (State.get w VALB).length ≤ P := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ IDX3),
      hframe VALB (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hVALB
  -- run the two readNums
  obtain ⟨hVALC1, hESCAN1, hRN1frame⟩ := readNum_run w (edges[i]'hi).1
    (List.replicate (edges[i]'hi).2 1 ++ 0 :: encEdges (edges.drop (i + 1)))
    VALC ESCAN2 IDX4 hESCAN_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALC ESCAN2 IDX4).eval w with hs1
  obtain ⟨hVALD2, hESCAN2', hRN2frame⟩ := readNum_run s1 (edges[i]'hi).2
    (encEdges (edges.drop (i + 1))) VALD ESCAN2 IDX4 hESCAN1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s2 := (readNum VALD ESCAN2 IDX4).eval s1 with hs2
  -- register lengths at s2 (eqBit1 entry)
  have hVALC2 : (State.get s2 VALC).length ≤ P := by
    rw [hRN2frame VALC (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hVALC1, List.length_replicate]; exact he1
  have hVALA2 : (State.get s2 VALA).length ≤ P := by
    rw [hRN2frame VALA (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hRN1frame VALA (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hVALAw
  -- s3 = eqBit1.eval s2 ; register lengths at s3 (eqBit2 entry)
  have he3eval : (Cmd.op (.eqBit RES1 VALC VALA)).eval s2
      = s2.set RES1 (if State.get s2 VALC = State.get s2 VALA then [1] else [0]) := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  set s3 := s2.set RES1 (if State.get s2 VALC = State.get s2 VALA then [1] else [0]) with hs3
  have hVALD3 : (State.get s3 VALD).length ≤ P := by
    rw [hs3, State.get_set_ne _ _ _ _ (by decide : (VALD : Var) ≠ RES1),
      hVALD2, List.length_replicate]; exact he2
  have hVALB3 : (State.get s3 VALB).length ≤ P := by
    rw [hs3, State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ RES1),
      hRN2frame VALB (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hRN1frame VALB (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]; exact hVALBw
  -- five cost pieces
  have b1 : (readNum VALC ESCAN2 IDX4).cost w ≤ 2 * (P * P) + 7 * P + 7 := by
    refine (readNum_cost w VALC ESCAN2 IDX4 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ?_
    nlinarith [hESlen, Nat.mul_le_mul hESlen hESlen]
  have hES1len : (State.get s1 ESCAN2).length ≤ P :=
    (readNum_stream_le w VALC ESCAN2 IDX4 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hESlen
  have b2 : (readNum VALD ESCAN2 IDX4).cost s1 ≤ 2 * (P * P) + 7 * P + 7 := by
    refine (readNum_cost s1 VALD ESCAN2 IDX4 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ?_
    nlinarith [hES1len, Nat.mul_le_mul hES1len hES1len]
  have b3 : (Cmd.op (.eqBit RES1 VALC VALA)).cost s2 ≤ 2 * P + 1 := by
    show (State.get s2 VALC).length + (State.get s2 VALA).length + 1 ≤ 2 * P + 1
    omega
  have b4 : (Cmd.op (.eqBit RES2 VALD VALB)).cost s3 ≤ 2 * P + 1 := by
    show (State.get s3 VALD).length + (State.get s3 VALB).length + 1 ≤ 2 * P + 1
    omega
  have b5 : (Cmd.ifBit RES1
      (Cmd.ifBit RES2 (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND)) cSkip)
      cSkip).cost ((Cmd.op (.eqBit RES2 VALD VALB)).eval s3) ≤ 5 := by
    set X := (Cmd.op (.eqBit RES2 VALD VALB)).eval s3 with hX
    by_cases h1 : State.get X RES1 = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ h1]
      by_cases h2 : State.get X RES2 = [1]
      · rw [Cmd.cost_ifBit_true _ _ _ _ h2, Cmd.cost_seq, Cmd.cost_op, Cmd.cost_op]
        simp only [Op.cost]; omega
      · rw [Cmd.cost_ifBit_false _ _ _ _ h2, cSkip_cost]
    · rw [Cmd.cost_ifBit_false _ _ _ _ h1, cSkip_cost]; omega
  rw [Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, ← hs1, ← hs2, he3eval]
  omega

/-- **`memberEdge` cost bound** (single loop, cubic in the length ceiling `P`). -/
private theorem memberEdge_cost (st : State) (va vb : Nat) (edges : List fedge) (P : Nat)
    (hVALA : st.get VALA = List.replicate va 1)
    (hVALB : st.get VALB = List.replicate vb 1)
    (hES : st.get EDGE_STREAM = encEdges edges)
    (hET : st.get EDGE_TALLY = List.replicate edges.length 1)
    (hEP : (encEdges edges).length ≤ P) (hmP : edges.length ≤ P)
    (hvaP : va ≤ P) (hvbP : vb ≤ P) :
    memberEdge.cost st ≤ 4 * (P * P * P) + 20 * (P * P) + 30 * P + 8 := by
  set st' := (st.set FOUND [0]).set ESCAN2 (encEdges edges) with hst'
  have e1 : (Cmd.op (.clear FOUND)).eval st = st.set FOUND [] := by
    rw [Cmd.eval_op]; simp only [Op.eval]
  have e2 : (Cmd.op (.appendZero FOUND)).eval (st.set FOUND []) = st.set FOUND [0] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [State.get_set_eq, List.nil_append, State.set_set]
  have e3 : (Cmd.op (.copy ESCAN2 EDGE_STREAM)).eval (st.set FOUND [0]) = st' := by
    rw [Cmd.eval_op]; simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ FOUND), hES]
  have hcost_eq : memberEdge.cost st
      = (encEdges edges).length + 6
          + (Cmd.forBnd IDX3 EDGE_TALLY
              (readNum VALC ESCAN2 IDX4 ;; readNum VALD ESCAN2 IDX4 ;;
               Cmd.op (.eqBit RES1 VALC VALA) ;; Cmd.op (.eqBit RES2 VALD VALB) ;;
               Cmd.ifBit RES1
                 (Cmd.ifBit RES2 (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND)) cSkip)
                 cSkip)).cost st' := by
    show (Cmd.cost (Cmd.op (.clear FOUND) ;; Cmd.op (.appendZero FOUND) ;;
      Cmd.op (.copy ESCAN2 EDGE_STREAM) ;; _) st) = _
    rw [Cmd.cost_seq, e1, Cmd.cost_seq, e2, Cmd.cost_seq, e3, Cmd.cost_op,
      Cmd.cost_op, Cmd.cost_op]
    simp only [Op.cost]
    rw [State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ FOUND), hES]
    omega
  have hVALAe : st'.get VALA = List.replicate va 1 := by
    rw [hst', State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ ESCAN2),
      State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ FOUND), hVALA]
  have hVALBe : st'.get VALB = List.replicate vb 1 := by
    rw [hst', State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ ESCAN2),
      State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ FOUND), hVALB]
  have hVALA' : (st'.get VALA).length ≤ P := by
    rw [hVALAe, List.length_replicate]; exact hvaP
  have hVALB' : (st'.get VALB).length ≤ P := by
    rw [hVALBe, List.length_replicate]; exact hvbP
  have hES0' : st'.get EDGE_STREAM = encEdges edges := by
    rw [hst', State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ ESCAN2),
      State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ FOUND), hES]
  have hET0' : st'.get EDGE_TALLY = List.replicate edges.length 1 := by
    rw [hst', State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ ESCAN2),
      State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ FOUND), hET]
  have hESCAN0' : st'.get ESCAN2 = encEdges edges := by
    rw [hst', State.get_set_eq]
  have hFOUND0' : st'.get FOUND = [0] := by
    rw [hst', State.get_set_ne _ _ _ _ (by decide : (FOUND : Var) ≠ ESCAN2),
      State.get_set_eq]
  have hbase : MEInv va vb edges st' 0 st' := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [hESCAN0', List.drop_zero]
    · rw [hFOUND0', List.take_zero]; simp [memB]
  have hblen : (st'.get EDGE_TALLY).length = edges.length := by
    rw [hET0', List.length_replicate]
  have hloop : (Cmd.forBnd IDX3 EDGE_TALLY
      (readNum VALC ESCAN2 IDX4 ;; readNum VALD ESCAN2 IDX4 ;;
       Cmd.op (.eqBit RES1 VALC VALA) ;; Cmd.op (.eqBit RES2 VALD VALB) ;;
       Cmd.ifBit RES1
         (Cmd.ifBit RES2 (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND)) cSkip)
         cSkip)).cost st'
      ≤ 1 + edges.length * (4 * (P * P) + 18 * P + 26) + edges.length * edges.length := by
    have h := Cmd.cost_forBnd_le IDX3 EDGE_TALLY
      (readNum VALC ESCAN2 IDX4 ;; readNum VALD ESCAN2 IDX4 ;;
       Cmd.op (.eqBit RES1 VALC VALA) ;; Cmd.op (.eqBit RES2 VALD VALB) ;;
       Cmd.ifBit RES1
         (Cmd.ifBit RES2 (Cmd.op (.clear FOUND) ;; Cmd.op (.appendOne FOUND)) cSkip)
         cSkip) st' (4 * (P * P) + 18 * P + 26) (MEInv va vb edges st') hbase
      (fun i s hi h => memberEdge_step va vb edges st'
        hVALAe hVALBe i s (by rwa [hblen] at hi) h)
      (fun i s hi h => memberEdge_body_cost va vb edges P st' hVALA' hVALB' hEP i s
        (by rwa [hblen] at hi) h)
    rw [hblen] at h; exact h
  rw [hcost_eq]
  have h1 : edges.length * (4 * (P * P) + 18 * P + 26) ≤ P * (4 * (P * P) + 18 * P + 26) :=
    Nat.mul_le_mul_right _ hmP
  have h2 : edges.length * edges.length ≤ P * P := Nat.mul_le_mul hmP hmP
  have h4 : P * (4 * (P * P) + 18 * P + 26) = 4 * (P * P * P) + 18 * (P * P) + 26 * P := by ring
  omega

/-- Uniform per-iteration body-cost bound for the `checkNodup` INNER loop. -/
private theorem checkNodupInner_body_cost (l : List fvertex) (i va : Nat) (b' : Bool)
    (P : Nat) (st : State) (hIDX1P : (st.get IDX1).length ≤ P)
    (hVALAP : (st.get VALA).length ≤ P) (hVP : (encVerts l).length ≤ P) (hmP : l.length ≤ P)
    (j : Nat) (s : State) (hj : j < l.length) (h : NInnerInv l i va b' st j s) :
    (readNum VALB VSCAN2 IDX3 ;; Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
      Cmd.ifBit RES1 cSkip
        (Cmd.op (.eqBit RES2 VALA VALB) ;; Cmd.ifBit RES2 cReject cSkip)).cost
        (s.set IDX2 (List.replicate j 1))
      ≤ 2 * (P * P) + 11 * P + 17 := by
  obtain ⟨hVSCAN2, _, hframe⟩ := h
  set w := s.set IDX2 (List.replicate j 1) with hw
  have hVSlen : (State.get w VSCAN2).length ≤ P := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ IDX2), hVSCAN2]
    exact (encVerts_drop_length_le l j).trans hVP
  have hlj : l[j]'hj ≤ P := vert_getElem_le l j hj P ((encVerts_drop_length_le l j).trans hVP)
  have hVS_in : State.get w VSCAN2
      = List.replicate (l[j]'hj) 1 ++ 0 :: encVerts (l.drop (j + 1)) := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ IDX2), hVSCAN2,
      List.drop_eq_getElem_cons hj, encVerts_cons]
  have hIDX1w : (State.get w IDX1).length ≤ P := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (IDX1 : Var) ≠ IDX2),
      hframe IDX1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hIDX1P
  have hVALAw : (State.get w VALA).length ≤ P := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ IDX2),
      hframe VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hVALAP
  have hIDX2w : (State.get w IDX2).length = j := by
    rw [hw, State.get_set_eq, List.length_replicate]
  -- run readNum VALB
  obtain ⟨hVALB1, hVSCAN2', hRNframe⟩ := readNum_run w (l[j]'hj)
    (encVerts (l.drop (j + 1))) VALB VSCAN2 IDX3 hVS_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALB VSCAN2 IDX3).eval w with hs1
  have hIDX1s1 : (State.get s1 IDX1).length ≤ P := by
    rw [hRNframe IDX1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hIDX1w
  have hIDX2s1 : (State.get s1 IDX2).length ≤ P := by
    rw [hRNframe IDX2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hIDX2w]; omega
  have hVALAs1 : (State.get s1 VALA).length ≤ P := by
    rw [hRNframe VALA (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hVALAw
  have hVALBs1 : (State.get s1 VALB).length ≤ P := by
    rw [hVALB1, List.length_replicate]; exact hlj
  -- VALA, VALB after eqBit1 (preserved, no `if`-materialization)
  have hVALAs2 : (State.get ((Cmd.op (.eqBit RES1 IDX1 IDX2)).eval s1) VALA).length ≤ P := by
    rw [Cmd.eval_op]; simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ RES1)]; exact hVALAs1
  have hVALBs2 : (State.get ((Cmd.op (.eqBit RES1 IDX1 IDX2)).eval s1) VALB).length ≤ P := by
    rw [Cmd.eval_op]; simp only [Op.eval]
    rw [State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ RES1)]; exact hVALBs1
  have b1 : (readNum VALB VSCAN2 IDX3).cost w ≤ 2 * (P * P) + 7 * P + 7 := by
    refine (readNum_cost w VALB VSCAN2 IDX3 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ?_
    nlinarith [hVSlen, Nat.mul_le_mul hVSlen hVSlen]
  have b2 : (Cmd.op (.eqBit RES1 IDX1 IDX2)).cost s1 ≤ 2 * P + 1 := by
    rw [Cmd.cost_op]; simp only [Op.cost]; omega
  have b3 : (Cmd.ifBit RES1 cSkip
      (Cmd.op (.eqBit RES2 VALA VALB) ;; Cmd.ifBit RES2 cReject cSkip)).cost
      ((Cmd.op (.eqBit RES1 IDX1 IDX2)).eval s1) ≤ 2 * P + 7 := by
    set s2 := (Cmd.op (.eqBit RES1 IDX1 IDX2)).eval s1 with hs2
    by_cases h1 : State.get s2 RES1 = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ h1, cSkip_cost]; omega
    · rw [Cmd.cost_ifBit_false _ _ _ _ h1, Cmd.cost_seq, Cmd.cost_op]
      have hif2 : (Cmd.ifBit RES2 cReject cSkip).cost
          ((Cmd.op (.eqBit RES2 VALA VALB)).eval s2) ≤ 4 := by
        by_cases h2 : State.get ((Cmd.op (.eqBit RES2 VALA VALB)).eval s2) RES2 = [1]
        · rw [Cmd.cost_ifBit_true _ _ _ _ h2, cReject_cost]
        · rw [Cmd.cost_ifBit_false _ _ _ _ h2, cSkip_cost]
      simp only [Op.cost]; omega
  rw [Cmd.cost_seq, Cmd.cost_seq, ← hs1]
  omega

/-- **`checkNodup` inner-loop cost bound.** -/
private theorem checkNodupInner_cost (l : List fvertex) (i va : Nat) (b' : Bool)
    (P : Nat) (st : State) (hIDX1P : (st.get IDX1).length ≤ P)
    (hVALAP : (st.get VALA).length ≤ P) (hVP : (encVerts l).length ≤ P)
    (hmP : l.length ≤ P)
    (hVSCAN2 : st.get VSCAN2 = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hIDX1 : st.get IDX1 = List.replicate i 1)
    (hVALA : st.get VALA = List.replicate va 1)
    (hO : st.get OUTPUT = [if b' then 1 else 0]) :
    (Cmd.forBnd IDX2 VERT_TALLY
        (readNum VALB VSCAN2 IDX3 ;;
         Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
         Cmd.ifBit RES1 cSkip
           (Cmd.op (.eqBit RES2 VALA VALB) ;;
            Cmd.ifBit RES2 cReject cSkip))).cost st
      ≤ 1 + l.length * (2 * (P * P) + 11 * P + 17) + l.length * l.length := by
  have hblen : (st.get VERT_TALLY).length = l.length := by
    rw [hVT, List.length_replicate]
  have hbase : NInnerInv l i va b' st 0 st := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [hVSCAN2, List.drop_zero]
    · rw [hO]; simp [innerAll]
  have h := Cmd.cost_forBnd_le IDX2 VERT_TALLY
    (readNum VALB VSCAN2 IDX3 ;; Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
     Cmd.ifBit RES1 cSkip
       (Cmd.op (.eqBit RES2 VALA VALB) ;; Cmd.ifBit RES2 cReject cSkip)) st
    (2 * (P * P) + 11 * P + 17) (NInnerInv l i va b' st) hbase
    (fun j s hj h => checkNodupInner_step l i va b' st hIDX1 hVALA j s
      (by rwa [hblen] at hj) h)
    (fun j s hj h => checkNodupInner_body_cost l i va b' P st hIDX1P hVALAP hVP hmP j s
      (by rwa [hblen] at hj) h)
  rw [hblen] at h; exact h

/-- Uniform per-iteration body-cost bound for the `checkNodup` OUTER loop. -/
private theorem checkNodup_body_cost (l : List fvertex) (b : Bool) (P : Nat)
    (st : State) (hVERT : st.get VERT_STREAM = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hVP : (encVerts l).length ≤ P) (hmP : l.length ≤ P)
    (i : Nat) (s : State) (hi : i < l.length) (h : CNodupInv l b st i s) :
    (readNum VALA VSCAN IDX2 ;;
      Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
      Cmd.forBnd IDX2 VERT_TALLY
        (readNum VALB VSCAN2 IDX3 ;;
         Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
         Cmd.ifBit RES1 cSkip
           (Cmd.op (.eqBit RES2 VALA VALB) ;;
            Cmd.ifBit RES2 cReject cSkip))).cost (s.set IDX1 (List.replicate i 1))
      ≤ 2 * (P * P * P) + 14 * (P * P) + 25 * P + 11 := by
  obtain ⟨hVSCAN, hOUT, hframe⟩ := h
  set w := s.set IDX1 (List.replicate i 1) with hw
  have hVS_in : State.get w VSCAN
      = List.replicate (l[i]'hi) 1 ++ 0 :: encVerts (l.drop (i + 1)) := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VSCAN : Var) ≠ IDX1), hVSCAN,
      List.drop_eq_getElem_cons hi, encVerts_cons]
  have hVSlen : (State.get w VSCAN).length ≤ P := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VSCAN : Var) ≠ IDX1), hVSCAN]
    exact (encVerts_drop_length_le l i).trans hVP
  have hli : l[i]'hi ≤ P := vert_getElem_le l i hi P ((encVerts_drop_length_le l i).trans hVP)
  obtain ⟨hVALA, hVSCAN', hRNframe⟩ := readNum_run w (l[i]'hi)
    (encVerts (l.drop (i + 1))) VALA VSCAN IDX2 hVS_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALA VSCAN IDX2).eval w with hs1
  have hVERT1 : s1.get VERT_STREAM = encVerts l := by
    rw [hRNframe VERT_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hw,
      State.get_set_ne _ _ _ _ (by decide : (VERT_STREAM : Var) ≠ IDX1),
      hframe VERT_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hVERT]
  have hVERT1len : (State.get s1 VERT_STREAM).length ≤ P := by rw [hVERT1]; exact hVP
  have ecopy : (Cmd.op (.copy VSCAN2 VERT_STREAM)).eval s1 = s1.set VSCAN2 (encVerts l) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVERT1]
  set s2 := s1.set VSCAN2 (encVerts l) with hs2
  have hVSCAN2_2 : s2.get VSCAN2 = encVerts l := State.get_set_eq _ _ _
  have hVT2 : s2.get VERT_TALLY = List.replicate l.length 1 := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ VSCAN2),
      hRNframe VERT_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hw,
      State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ IDX1),
      hframe VERT_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hVT]
  have hIDX1_2 : s2.get IDX1 = List.replicate i 1 := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide : (IDX1 : Var) ≠ VSCAN2),
      hRNframe IDX1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hw, State.get_set_eq]
  have hVALA2 : s2.get VALA = List.replicate (l[i]'hi) 1 := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ VSCAN2), hVALA]
  have hOUT2 : s2.get OUTPUT
      = [if b && (List.range i).all (fun i' => innerAll i' (l.getD i' 0) l l.length)
          then 1 else 0] := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ VSCAN2),
      hRNframe OUTPUT (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hw, State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ IDX1),
      hOUT]
  have hIDX1P : (State.get s2 IDX1).length ≤ P := by
    rw [hIDX1_2, List.length_replicate]; omega
  have hVALAP : (State.get s2 VALA).length ≤ P := by
    rw [hVALA2, List.length_replicate]; exact hli
  -- three cost pieces
  have b1 : (readNum VALA VSCAN IDX2).cost w ≤ 2 * (P * P) + 7 * P + 7 := by
    refine (readNum_cost w VALA VSCAN IDX2 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ?_
    nlinarith [hVSlen, Nat.mul_le_mul hVSlen hVSlen]
  have b2 : (Cmd.op (.copy VSCAN2 VERT_STREAM)).cost s1 ≤ P + 1 := by
    rw [Cmd.cost_op]; simp only [Op.cost]; omega
  have b3 := checkNodupInner_cost l i (l[i]'hi)
    (b && (List.range i).all (fun i' => innerAll i' (l.getD i' 0) l l.length)) P s2
    hIDX1P hVALAP hVP hmP hVSCAN2_2 hVT2 hIDX1_2 hVALA2 hOUT2
  rw [Cmd.cost_seq, Cmd.cost_seq, ← hs1, ecopy]
  have hmul : l.length * (2 * (P * P) + 11 * P + 17) ≤ P * (2 * (P * P) + 11 * P + 17) :=
    Nat.mul_le_mul_right _ hmP
  have hmul2 : l.length * l.length ≤ P * P := Nat.mul_le_mul hmP hmP
  have hexp : P * (2 * (P * P) + 11 * P + 17) = 2 * (P * P * P) + 11 * (P * P) + 17 * P := by ring
  omega

/-- **`checkNodup` cost bound** (double loop, quartic in the length ceiling `P`). -/
private theorem checkNodup_cost (st : State) (l : List fvertex) (b : Bool) (P : Nat)
    (hVS : st.get VERT_STREAM = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hO : st.get OUTPUT = [if b then 1 else 0])
    (hVP : (encVerts l).length ≤ P) (hmP : l.length ≤ P) :
    checkNodup.cost st ≤ 2 * (P * P * P * P) + 14 * (P * P * P) + 27 * (P * P) + 13 * P + 3 := by
  have eInit : (Cmd.op (.copy VSCAN VERT_STREAM)).eval st = st.set VSCAN (encVerts l) := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVS]
  have hcost_eq : checkNodup.cost st
      = (encVerts l).length + 2
          + (Cmd.forBnd IDX1 VERT_TALLY
              (readNum VALA VSCAN IDX2 ;;
               Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
               Cmd.forBnd IDX2 VERT_TALLY
                 (readNum VALB VSCAN2 IDX3 ;;
                  Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
                  Cmd.ifBit RES1 cSkip
                    (Cmd.op (.eqBit RES2 VALA VALB) ;;
                     Cmd.ifBit RES2 cReject cSkip)))).cost (st.set VSCAN (encVerts l)) := by
    show (Cmd.cost (Cmd.op (.copy VSCAN VERT_STREAM) ;; _) st) = _
    rw [Cmd.cost_seq, Cmd.cost_op, eInit]; simp only [Op.cost]; rw [hVS]; omega
  set s0 := st.set VSCAN (encVerts l) with hs0
  have hVERT0 : s0.get VERT_STREAM = encVerts l := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (VERT_STREAM : Var) ≠ VSCAN), hVS]
  have hVT0 : s0.get VERT_TALLY = List.replicate l.length 1 := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (VERT_TALLY : Var) ≠ VSCAN), hVT]
  have hO0 : s0.get OUTPUT = [if b then 1 else 0] := by
    rw [hs0, State.get_set_ne _ _ _ _ (by decide : (OUTPUT : Var) ≠ VSCAN), hO]
  have hbase : CNodupInv l b s0 0 s0 := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [hs0, State.get_set_eq, List.drop_zero]
    · rw [hO0]; simp
  have hblen : (s0.get VERT_TALLY).length = l.length := by
    rw [hVT0, List.length_replicate]
  have hloop : (Cmd.forBnd IDX1 VERT_TALLY
      (readNum VALA VSCAN IDX2 ;;
       Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
       Cmd.forBnd IDX2 VERT_TALLY
         (readNum VALB VSCAN2 IDX3 ;;
          Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
          Cmd.ifBit RES1 cSkip
            (Cmd.op (.eqBit RES2 VALA VALB) ;;
             Cmd.ifBit RES2 cReject cSkip)))).cost s0
      ≤ 1 + l.length * (2 * (P * P * P) + 14 * (P * P) + 25 * P + 11)
          + l.length * l.length := by
    have h := Cmd.cost_forBnd_le IDX1 VERT_TALLY
      (readNum VALA VSCAN IDX2 ;;
       Cmd.op (.copy VSCAN2 VERT_STREAM) ;;
       Cmd.forBnd IDX2 VERT_TALLY
         (readNum VALB VSCAN2 IDX3 ;;
          Cmd.op (.eqBit RES1 IDX1 IDX2) ;;
          Cmd.ifBit RES1 cSkip
            (Cmd.op (.eqBit RES2 VALA VALB) ;;
             Cmd.ifBit RES2 cReject cSkip))) s0
      (2 * (P * P * P) + 14 * (P * P) + 25 * P + 11) (CNodupInv l b s0) hbase
      (fun i s hi h => checkNodup_step l b s0 hVERT0 hVT0 i s (by rwa [hblen] at hi) h)
      (fun i s hi h => checkNodup_body_cost l b P s0 hVERT0 hVT0 hVP hmP i s
        (by rwa [hblen] at hi) h)
    rw [hblen] at h; exact h
  rw [hcost_eq]
  have h1 : l.length * (2 * (P * P * P) + 14 * (P * P) + 25 * P + 11)
      ≤ P * (2 * (P * P * P) + 14 * (P * P) + 25 * P + 11) := Nat.mul_le_mul_right _ hmP
  have h2 : l.length * l.length ≤ P * P := Nat.mul_le_mul hmP hmP
  have h4 : P * (2 * (P * P * P) + 14 * (P * P) + 25 * P + 11)
      = 2 * (P * P * P * P) + 14 * (P * P * P) + 25 * (P * P) + 11 * P := by ring
  omega

/-- Uniform per-iteration body-cost bound for the `checkClique` INNER loop
(contains `memberEdge`, hence cubic in `P`). -/
private theorem checkCliqueInner_body_cost (edges : List fedge) (l : List fvertex)
    (va : Nat) (b' : Bool) (P : Nat) (st : State)
    (hVALA : st.get VALA = List.replicate va 1)
    (hES : st.get EDGE_STREAM = encEdges edges)
    (hET : st.get EDGE_TALLY = List.replicate edges.length 1)
    (hvaP : va ≤ P) (hVP : (encVerts l).length ≤ P) (hmP : l.length ≤ P)
    (hEP : (encEdges edges).length ≤ P) (hmEP : edges.length ≤ P)
    (j : Nat) (s : State) (hj : j < l.length) (h : CliqueInnerInv edges l va b' st j s) :
    (readNum VALB VSCAN2 IDX3 ;;
      Cmd.op (.eqBit RES1 VALA VALB) ;;
      Cmd.ifBit RES1 cSkip
        (memberEdge ;; Cmd.ifBit FOUND cSkip cReject)).cost
        (s.set IDX2 (List.replicate j 1))
      ≤ 4 * (P * P * P) + 22 * (P * P) + 39 * P + 28 := by
  obtain ⟨hVSCAN2, _, hframe⟩ := h
  set w := s.set IDX2 (List.replicate j 1) with hw
  have hVSlen : (State.get w VSCAN2).length ≤ P := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ IDX2), hVSCAN2]
    exact (encVerts_drop_length_le l j).trans hVP
  have hlj : l[j]'hj ≤ P := vert_getElem_le l j hj P ((encVerts_drop_length_le l j).trans hVP)
  have hVS_in : State.get w VSCAN2
      = List.replicate (l[j]'hj) 1 ++ 0 :: encVerts (l.drop (j + 1)) := by
    rw [hw, State.get_set_ne _ _ _ _ (by decide : (VSCAN2 : Var) ≠ IDX2), hVSCAN2,
      List.drop_eq_getElem_cons hj, encVerts_cons]
  obtain ⟨hVALB1, hVSCAN2', hRNframe⟩ := readNum_run w (l[j]'hj)
    (encVerts (l.drop (j + 1))) VALB VSCAN2 IDX3 hVS_in
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  set s1 := (readNum VALB VSCAN2 IDX3).eval w with hs1
  have hVALA1 : s1.get VALA = List.replicate va 1 := by
    rw [hRNframe VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hw, State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ IDX2),
      hframe VALA (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), hVALA]
  have hES1 : s1.get EDGE_STREAM = encEdges edges := by
    rw [hRNframe EDGE_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hw, State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ IDX2),
      hframe EDGE_STREAM (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), hES]
  have hET1 : s1.get EDGE_TALLY = List.replicate edges.length 1 := by
    rw [hRNframe EDGE_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), hw, State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ IDX2),
      hframe EDGE_TALLY (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), hET]
  -- eqBit RES1 VALA VALB (materialised over Nats — safe, no nested-state `if`)
  have e2 : (Cmd.op (.eqBit RES1 VALA VALB)).eval s1
      = s1.set RES1 [if va = l[j]'hj then 1 else 0] := by
    rw [Cmd.eval_op]; simp only [Op.eval]; rw [hVALA1, hVALB1, eqBit_replicate]
  set s2 := s1.set RES1 [if va = l[j]'hj then 1 else 0] with hs2
  have hVALA2 : s2.get VALA = List.replicate va 1 := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide : (VALA : Var) ≠ RES1), hVALA1]
  have hVALB2 : s2.get VALB = List.replicate (l[j]'hj) 1 := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide : (VALB : Var) ≠ RES1), hVALB1]
  have hES2 : s2.get EDGE_STREAM = encEdges edges := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide : (EDGE_STREAM : Var) ≠ RES1), hES1]
  have hET2 : s2.get EDGE_TALLY = List.replicate edges.length 1 := by
    rw [hs2, State.get_set_ne _ _ _ _ (by decide : (EDGE_TALLY : Var) ≠ RES1), hET1]
  -- cost pieces
  have b1 : (readNum VALB VSCAN2 IDX3).cost w ≤ 2 * (P * P) + 7 * P + 7 := by
    refine (readNum_cost w VALB VSCAN2 IDX3 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ?_
    nlinarith [hVSlen, Nat.mul_le_mul hVSlen hVSlen]
  have b2 : (Cmd.op (.eqBit RES1 VALA VALB)).cost s1 ≤ 2 * P + 1 := by
    have hva : (State.get s1 VALA).length ≤ P := by rw [hVALA1, List.length_replicate]; exact hvaP
    have hvb : (State.get s1 VALB).length ≤ P := by rw [hVALB1, List.length_replicate]; exact hlj
    rw [Cmd.cost_op]; simp only [Op.cost]; omega
  have b3 : (Cmd.ifBit RES1 cSkip (memberEdge ;; Cmd.ifBit FOUND cSkip cReject)).cost s2
      ≤ 4 * (P * P * P) + 20 * (P * P) + 30 * P + 18 := by
    by_cases h1 : State.get s2 RES1 = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ h1, cSkip_cost]; omega
    · rw [Cmd.cost_ifBit_false _ _ _ _ h1, Cmd.cost_seq]
      have hmem := memberEdge_cost s2 va (l[j]'hj) edges P hVALA2 hVALB2 hES2 hET2
        hEP hmEP hvaP hlj
      have hif2 : (Cmd.ifBit FOUND cSkip cReject).cost (memberEdge.eval s2) ≤ 4 := by
        by_cases h2 : State.get (memberEdge.eval s2) FOUND = [1]
        · rw [Cmd.cost_ifBit_true _ _ _ _ h2, cSkip_cost]
        · rw [Cmd.cost_ifBit_false _ _ _ _ h2, cReject_cost]
      omega
  rw [Cmd.cost_seq, Cmd.cost_seq, ← hs1, e2]
  omega

/-- **`checkClique` inner-loop cost bound** (quartic — `memberEdge` × the inner
scan over `l`). -/
private theorem checkCliqueInner_cost (edges : List fedge) (l : List fvertex)
    (va : Nat) (b' : Bool) (P : Nat) (st : State)
    (hVALA : st.get VALA = List.replicate va 1)
    (hES : st.get EDGE_STREAM = encEdges edges)
    (hET : st.get EDGE_TALLY = List.replicate edges.length 1)
    (hvaP : va ≤ P) (hVP : (encVerts l).length ≤ P) (hmP : l.length ≤ P)
    (hEP : (encEdges edges).length ≤ P) (hmEP : edges.length ≤ P)
    (hVSCAN2 : st.get VSCAN2 = encVerts l)
    (hVT : st.get VERT_TALLY = List.replicate l.length 1)
    (hO : st.get OUTPUT = [if b' then 1 else 0]) :
    (Cmd.forBnd IDX2 VERT_TALLY
        (readNum VALB VSCAN2 IDX3 ;;
         Cmd.op (.eqBit RES1 VALA VALB) ;;
         Cmd.ifBit RES1 cSkip
           (memberEdge ;; Cmd.ifBit FOUND cSkip cReject))).cost st
      ≤ 1 + l.length * (4 * (P * P * P) + 22 * (P * P) + 39 * P + 28)
          + l.length * l.length := by
  have hblen : (st.get VERT_TALLY).length = l.length := by
    rw [hVT, List.length_replicate]
  have hbase : CliqueInnerInv edges l va b' st 0 st := by
    refine ⟨?_, ?_, fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    · rw [hVSCAN2, List.drop_zero]
    · rw [hO]; simp [cliqueInnerAll]
  have h := Cmd.cost_forBnd_le IDX2 VERT_TALLY
    (readNum VALB VSCAN2 IDX3 ;; Cmd.op (.eqBit RES1 VALA VALB) ;;
     Cmd.ifBit RES1 cSkip (memberEdge ;; Cmd.ifBit FOUND cSkip cReject)) st
    (4 * (P * P * P) + 22 * (P * P) + 39 * P + 28) (CliqueInnerInv edges l va b' st) hbase
    (fun j s hj h => checkCliqueInner_step edges l va b' st hVALA hES hET j s
      (by rwa [hblen] at hj) h)
    (fun j s hj h => checkCliqueInner_body_cost edges l va b' P st hVALA hES hET
      hvaP hVP hmP hEP hmEP j s (by rwa [hblen] at hj) h)
  rw [hblen] at h; exact h

/-- The Lang-level decider witness for the FlatClique verifier.

**Proven & axiom-clean**: `encodeIn_size`, `enc_bit`, `width_le`, `regBound`
(encoding side), `usesBelow`, `noConsLen`, `allOpsSupported` (structural), and
**`decides`** (the 5-check assembly, `cliqueRelCmd_decides`). **`cost_bound`
remains `sorry`** — the per-loop `cost_forBnd_le` cost bound (HANDOFF top-down
Task 1, step 5). -/
noncomputable def cliqueRelDecidesLang :
    DecidesLang
      (fun Gkl : (fgraph × Nat) × List fvertex => cliqueRel Gkl.1 Gkl.2)
      timeBound where
  c := cliqueRelCmd
  encodeIn := cliqueRelEncode
  encodeIn_size := by
    intro x
    have h1 := cliqueRelEncode_size_bound x
    have h2 : 3 * encodable.size x ≤ timeBound (encodable.size x) := by
      show 3 * encodable.size x ≤ 200000 * (encodable.size x + 1) ^ 5
      have hself : encodable.size x + 1 ≤ (encodable.size x + 1) ^ 5 :=
        Nat.le_self_pow (by norm_num) _
      omega
    exact h1.trans h2
  decides := cliqueRelCmd_decides
  cost_bound := by intro x; sorry      -- TODO(top-down Task 1, step 5): per-loop `cost_forBnd_le`
  enc_bit := cliqueRelEncode_bit
  regBound := regBound
  usesBelow := cliqueRelCmd_usesBelow
  width_le := by
    intro x; obtain ⟨⟨G, k⟩, l⟩ := x
    show (cliqueRelEncode ((G, k), l)).length ≤ regBound
    simp only [cliqueRelEncode, regBound, List.length_cons, List.length_nil]
    omega
  noConsLen := cliqueRelCmd_noConsLen
  allOpsSupported := cliqueRelCmd_allOpsSupported

/-- The Lang-level `inTimePolyLang` witness. -/
theorem inTimePolyLang_cliqueRel :
    inTimePolyLang
      (fun Gkl : (fgraph × Nat) × List fvertex => cliqueRel Gkl.1 Gkl.2) :=
  ⟨timeBound, ⟨cliqueRelDecidesLang⟩, timeBound_inOPoly, timeBound_monotonic⟩

/-- `fun ((G, k), l) ↦ cliqueRel (G, k) l` is decided by a
polynomial-time Turing machine — the headline statement consumed by
`FlatClique_in_NP`. -/
theorem inTimePolyTM_cliqueRel :
    inTimePolyTM
      (fun Gkl : (fgraph × Nat) × List fvertex => cliqueRel Gkl.1 Gkl.2) :=
  inTimePolyLang_to_inTimePoly inTimePolyLang_cliqueRel

end CliqueRelTM

/-! ## `FlatClique ∈ NP` (unchanged from the pre-pivot version) -/

theorem FlatClique_in_NP : inNP FlatClique := by
  refine inNP_intro FlatClique cliqueRel ?_ ?_
  · exact CliqueRelTM.inTimePolyTM_cliqueRel
  · refine ⟨⟨fun n => n ^ 2 + 1, ?_, ?_, ?_, ?_⟩⟩
    · rintro ⟨G, k⟩ l ⟨hwf, hclq⟩
      exact ⟨l, hwf, hclq⟩
    · rintro ⟨G, k⟩ ⟨l, hwf, hclq⟩
      exact ⟨l, ⟨hwf, hclq⟩, clique_size_bound _ l ⟨hwf, hclq⟩⟩
    · exact ⟨2, ⟨2, 1, by intro n hn; nlinarith [Nat.one_le_pow 2 n (by omega)]⟩⟩
    · intro a b h; nlinarith [Nat.pow_le_pow_left h 2]
