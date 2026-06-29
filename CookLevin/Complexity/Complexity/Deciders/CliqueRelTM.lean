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

**Probe-validated design (`probes/CliqueRelProbe.lean`).** The program ANDs five
checks into `OUTPUT` (start `[1]`; set `[0]` on any failure), mirroring
`EvalCnfCmd`'s clause-AND structure. Sub-checks, each a `forBnd` over a tally:
1. **`fgraph_wf G`** — scan `EDGE_STREAM` (bound = edge tally): per edge parse
   both unary endpoints, compare each length against `NUMV` (unary `<`).
2. **`list_ofFlatType G.1 l`** — scan `VERT_STREAM`: each vertex `< numV`.
3. **`l.length = k`** — `eqBit` on the vertex tally vs `K`.
4. **`l.Nodup`** — outer/inner `forBnd` over (a copy of) `VERT_STREAM`,
   `eqBit`-compare distinct vertices.
5. **clique** — triple nested: outer/inner over `l`, innermost membership scan
   over `EDGE_STREAM` for the ordered pair (the `EvalCnfCmd.memberCheck` pattern,
   comparing TWO unary values per edge).

Transcription is mechanical against the proven `EvalCnfCmd` gadgets (stream
parse = `head ⨾ tail ⨾ ifBit`; unary accumulate = `appendOne`; unary compare =
`eqBit`). The hard part is the correctness invariants (one fold invariant per
loop nest, à la `EvalCnfCmd.CInv`/`MCInv`). -/

/-- The FlatClique verifier as a `Lang.Cmd`. **Design probe-validated**
(`probes/CliqueRelProbe.lean`); DSL transcription is the next top-down task. -/
noncomputable def cliqueRelCmd : Cmd := sorry  -- TODO(top-down Task 1): transcribe the
  -- probe-validated 5-check program (see the design block above + EvalCnfCmd template).

/-- The Lang-level decider witness for the FlatClique verifier.

**Encoding-side fields PROVEN & axiom-clean** (2026-06-29): `encodeIn_size`,
`enc_bit`, `width_le`, `regBound`. **Program-side fields `sorry`** pending the
concrete `cliqueRelCmd` (probe-validated; HANDOFF top-down Task 1). -/
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
  decides := by sorry                  -- TODO(top-down Task 1): correctness invariants
  cost_bound := by intro x; sorry      -- TODO(top-down Task 1): per-loop `cost_forBnd_le`
  enc_bit := cliqueRelEncode_bit
  regBound := regBound
  usesBelow := by sorry                -- TODO(top-down Task 1): `Cmd.UsesBelow cliqueRelCmd regBound`
  width_le := by
    intro x; obtain ⟨⟨G, k⟩, l⟩ := x
    show (cliqueRelEncode ((G, k), l)).length ≤ regBound
    simp only [cliqueRelEncode, regBound, List.length_cons, List.length_nil]
    omega
  noConsLen := by sorry                -- TODO(top-down Task 1): trio-free program ⇒ `simp`/`decide`
  allOpsSupported := by sorry          -- TODO(top-down Task 1): trio-free program ⇒ `simp`/`decide`

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
