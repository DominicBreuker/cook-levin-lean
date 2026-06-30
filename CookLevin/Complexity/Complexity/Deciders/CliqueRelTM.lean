import Complexity.Complexity.TMDecider
import Complexity.NP.FlatClique
import Complexity.Lang

set_option autoImplicit false

/-! # The FlatClique-verifier — closed via the Lang layer (Part 3.5)

This file owns the TM-backed decider for the FlatClique verification
relation
`fun (Gkl : (fgraph × Nat) × List fvertex) => cliqueRel Gkl.1 Gkl.2`
— i.e., the witness that `FlatClique ∈ NP`.

**Skeleton status (2026-06-29, top-down).** The input **encoding is now
concrete, probe-validated, and bit-level** (`cliqueRelEncode`), and its
encoding-side witness fields (`encodeIn_size`/`enc_bit`/`width_le`/`regBound`)
are PROVEN & axiom-clean. The verifier **program** `cliqueRelCmd` is still
`sorry` — its design is `#eval`-validated in `probes/CliqueRelProbe.lean` (the
encoding round-trips, stays `BitState`, and a stream-driven reference verifier
agrees with `cliqueRel`); transcribing it into the DSL (mirroring the proven
`EvalCnfCmd` template) is the next top-down session's task. The program-side
fields (`decides`/`cost_bound`/`usesBelow`/`noConsLen`/`allOpsSupported`) stay
`sorry` until then. See HANDOFF.md top-down Task 1.

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
