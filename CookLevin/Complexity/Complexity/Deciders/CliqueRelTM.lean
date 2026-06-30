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
Downstream only needs `inOPoly`/`monotonic`, so the degree is free. The `200000`
constant is a generous placeholder; tighten/justify it when `cost_bound` is
proven (it must dominate `cliqueRelCmd.cost (cliqueRelEncode x)`). -/
def timeBound (n : Nat) : Nat := 200000 * (n + 1) ^ 4

theorem timeBound_inOPoly : inOPoly timeBound := by
  refine ⟨4, ⟨3200000, 1, ?_⟩⟩
  intro n hn
  have hle : n + 1 ≤ n + n := Nat.add_le_add_left hn n
  show 200000 * (n + 1) ^ 4 ≤ 3200000 * n ^ 4
  calc 200000 * (n + 1) ^ 4
      ≤ 200000 * (n + n) ^ 4 :=
        Nat.mul_le_mul_left 200000 (Nat.pow_le_pow_left hle 4)
    _ = 3200000 * n ^ 4 := by ring

theorem timeBound_monotonic : monotonic timeBound :=
  fun _ _ h =>
    Nat.mul_le_mul_left 200000 (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 4)

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

/-- The Lang-level decider witness for the FlatClique verifier.

**Proven & axiom-clean**: `encodeIn_size`, `enc_bit`, `width_le`, `regBound`
(encoding side), and `usesBelow`, `noConsLen`, `allOpsSupported` (structural,
from the now-concrete `cliqueRelCmd`). **`decides`/`cost_bound` remain `sorry`** —
the per-check correctness invariants and the per-loop `cost_forBnd_le` cost bound
(HANDOFF top-down Task 1). -/
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
      show 3 * encodable.size x ≤ 200000 * (encodable.size x + 1) ^ 4
      have hself : encodable.size x + 1 ≤ (encodable.size x + 1) ^ 4 :=
        Nat.le_self_pow (by norm_num) _
      omega
    exact h1.trans h2
  decides := by sorry                  -- TODO(top-down Task 1): per-check correctness invariants
  cost_bound := by intro x; sorry      -- TODO(top-down Task 1): per-loop `cost_forBnd_le`
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
