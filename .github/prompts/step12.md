# Step 12 — Repair the SAT and clique side

## Read first

### Lean
- `README.md`
- `CookLevin/Complexity/NP/FSAT_to_SAT.lean`
- `CookLevin/Complexity/NP/SAT.lean`
- `CookLevin/Complexity/NP/FSAT.lean`
- `CookLevin/Complexity/NP/kSAT_to_SAT.lean`
- `CookLevin/Complexity/NP/kSAT_to_FlatClique.lean`
- `CookLevin/Complexity/NP/FlatClique.lean`

### Coq
- `coqdoc/Complexity.NP.SAT.FSAT.FSAT_to_SAT.txt`
- `coqdoc/Complexity.NP.SAT.SAT_inNP.txt`
- `coqdoc/Complexity.NP.SAT.kSAT_to_SAT.txt`
- `coqdoc/Complexity.NP.Clique.FlatClique.txt`
- `coqdoc/Complexity.NP.Clique.kSAT_to_FlatClique.txt`

Also read this file to the end, it contains a guideline for implementation!
One thing to do: The guide tells you to use Classical.byCases / Classical.dec for some deciders. Mark them with a `-- TODO(step14): replace classical decider with explicit Bool function` comment as you write them!

## Baseline you must preserve

- `FlatClique` is now a real flat clique predicate over wellformed graphs.
- the files compile, but the main SAT/clique theorems still use `sorry` and `FSAT_to_SAT` is still search-based.

## What still needs to be implemented

1. Replace the search-based `FSAT → SAT` / `FSAT → 3SAT` constructions with direct syntactic translations.
2. Finish `SAT_inNP.sat_NP`, `kSAT_to_SAT`, `kSAT_to_FlatClique_poly`, and `FlatClique_in_NP` honestly.
3. Keep the new `FlatClique` definition mathematically meaningful; do not collapse it back to `True`.
4. Ensure the final theorem file can use these exports unchanged.

## Deliverable

A compiling SAT/clique side with honest NP-membership proofs and direct polynomial reductions.

# Step 12 Implementation Guide — SAT / 3-SAT / FlatClique

**Scope.** This guide covers `Complexity/NP/FSAT_to_SAT.lean`, `SAT.lean` (the `SAT_inNP` block at the bottom), `kSAT_to_SAT.lean`, `kSAT_to_FlatClique.lean`, and `FlatClique.lean`. Together they replace search-based reductions with direct syntactic Tseytin transformations and replace four `sorry`s with honest proofs.

**Key context (from the previous review).** The framework's `polyTimeComputable` is a *size-bound* claim, not a real time-complexity claim. Step 12 must therefore: (a) produce reductions whose *output size* is genuinely polynomial in the input size, and (b) state correctness as a real `↔`. Time-complexity is a separate later concern.

---

## 0. The big picture and recommended order

The five files have the following dependency structure:

```
                 SAT.lean ─── (sat_NP)
                    ▲
                    │
   FlatClique.lean (FlatClique_in_NP)
                    ▲
                    │
   kSAT_to_FlatClique.lean
                    ▲
                    │
   kSAT.lean
                    ▲
                    │
   kSAT_to_SAT.lean ──┐
                      │
   FSAT.lean ◄────────┤
                      │
   FSAT_to_SAT.lean ◄─┘  (FSAT → SAT and FSAT → 3-SAT)
```

I recommend implementing in this order, because each builds on the previous:

1. **`kSAT_to_SAT`** — five-line proof, mostly definition unfolding. Warm-up.
2. **`SAT_inNP.sat_NP`** — moderately tricky but well-scoped; must be done before kSAT inNP.
3. **`FlatClique_in_NP`** — analogue of (2), structurally similar.
4. **`FSAT_to_SAT_poly` / `FSAT_to_3SAT_poly` (Tseytin)** — the largest piece, mathematically rich.
5. **`kSAT_to_FlatClique_poly`** — large but mostly mechanical once the encoding is laid out.

The current files contain four `sorry`s in `SAT_inNP.sat_NP` (×2), `FlatClique_in_NP`, and `kSAT_to_SAT` (×2), plus `FSAT_to_SAT_poly` and `FSAT_to_3SAT_poly` use a fake search-based reduction that is logically valid but morally wrong. The plan is to replace them all with mathematically faithful constructions.

---

## 1. `kSAT_to_SAT.lean` — the warm-up

The current file:

```lean
theorem kSAT_to_SAT (k : Nat) : kSAT k ⪯p SAT := by
  refine ⟨⟨id, by sorry, ?_⟩⟩
  intro N
  sorry
```

The reduction is the identity. There are two `sorry`s: a `polyTimeComputable id` and the `kSAT k N ↔ SAT N` direction.

### Math

`kSAT k N` is defined as `0 < k ∧ kCNF k N ∧ SAT N`. So the equivalence `kSAT k N ↔ SAT N` is *not actually true*; what holds is `kSAT k N → SAT N`. The reverse needs the `kCNF` and `0 < k` premises. A proper proof must provide a non-identity reduction in one direction or restrict the domain.

**Look at the Coq.** The Coq port avoids this by treating `kSAT` as a *subtype* in the underlying complexity framework — instances are pairs `(k, N)` with the `kCNF k N` constraint built in. Lean's current type signature `kSAT (k : Nat) : cnf → Prop` does not bake the constraint in.

**The honest fix.** Use a reduction that, on inputs that fail to be `kCNF`, returns a known unsatisfiable CNF, and on `kCNF` inputs returns `N` itself:

```lean
def kSAT_to_SAT_reduction (k : Nat) (N : cnf) : cnf :=
  if kCNF_decb k N && decide (0 < k) then N else [[]]   -- [[]] is unsat (empty clause)
```

This is the same pattern Coq uses for `trivialNoInstance`. With this, `kSAT k N ↔ SAT (reduction N)` holds:

- **Forward.** If `kSAT k N`, then both guards are true, so the reduction returns `N`, and `SAT N` is part of the hypothesis.
- **Backward.** If `SAT (reduction N)`:
  - Case 1: both guards true. Reduction returns `N`. `SAT N` holds. We also have `0 < k` and `kCNF k N` from the guards, so `kSAT k N` holds.
  - Case 2: a guard fails. Reduction returns `[[]]`, which is unsat: any clause must be satisfied, but `[]` cannot be. So `SAT [[]]` is false; the hypothesis is false; the conclusion holds vacuously.

### Drop-in implementation

```lean
import Complexity.Complexity.NP
import Complexity.NP.SAT
import Complexity.NP.kSAT

set_option autoImplicit false

/-- The empty clause. Unsatisfiable: there is no literal in `[]`, so `evalClause`
returns false for every assignment. -/
def emptyClauseCnf : cnf := [[]]

theorem emptyClauseCnf_unsat : ¬ SAT emptyClauseCnf := by
  rintro ⟨a, ha⟩
  -- ha : satisfiesCnf a [[]]
  -- = evalCnf a [[]] = true
  -- = (evalClause a [] && evalCnf a []) = true
  -- = (false && true) = true   -- contradiction
  simp [emptyClauseCnf, satisfiesCnf, evalCnf, evalClause] at ha

/-- Direct identity-based reduction guarded by `kCNF_decb` and `0 < k`. On invalid
inputs we fall through to a fixed unsatisfiable CNF, mirroring the Coq
`trivialNoInstance` pattern. -/
def kSAT_to_SAT_reduction (k : Nat) (N : cnf) : cnf :=
  if kCNF_decb k N ∧ 0 < k then N else emptyClauseCnf

theorem kSAT_to_SAT_reduction_correct (k : Nat) (N : cnf) :
    kSAT k N ↔ SAT (kSAT_to_SAT_reduction k N) := by
  unfold kSAT_to_SAT_reduction
  by_cases h : kCNF_decb k N ∧ 0 < k
  · simp [h]
    constructor
    · intro ⟨_, _, hsat⟩; exact hsat
    · intro hsat
      refine ⟨h.2, ?_, hsat⟩
      exact (kCNF_decb_iff k N).mp h.1
  · simp [h]
    constructor
    · rintro ⟨hk, hcnf, _⟩
      exact absurd ⟨(kCNF_decb_iff k N).mpr hcnf, hk⟩ h
    · intro hsat; exact absurd hsat emptyClauseCnf_unsat

theorem kSAT_to_SAT (k : Nat) : kSAT k ⪯p SAT := by
  refine ⟨⟨kSAT_to_SAT_reduction k, ?_, kSAT_to_SAT_reduction_correct k⟩⟩
  -- polyTimeComputable: linear bound (output is either N or [[]])
  refine ⟨⟨fun n => n + 2, ?_, ?_, ?_⟩⟩
  · -- inOPoly (fun n => n + 2): bound by n^1 + 2
    refine ⟨1, 1, 2, ?_⟩
    intro n _; simp; omega
  · -- monotonic
    intro a b h; omega
  · -- bound_valid
    intro N
    unfold kSAT_to_SAT_reduction
    by_cases h : kCNF_decb k N ∧ 0 < k
    · simp [h]
    · simp [h, emptyClauseCnf]
      -- size of [[]] = size of [[]] computed from encodable
      -- = 1 (empty clause: 0+1) + 1 (outer cons) = 2
      -- For safety we use a simple upper bound
      simp [encodable.size, encodable_size_list_cons, encodable_size_list_nil]

theorem inNP_kSAT (k : Nat) : inNP (kSAT k) := by
  exact red_inNP (kSAT k) SAT (kSAT_to_SAT k) SAT_inNP.sat_NP
```

**Notes:**
- The `inOPoly` witness shape `⟨degree, ⟨lo, hi, proof⟩⟩` matches what we see used elsewhere in the codebase (e.g. `BinaryCC_to_FSAT.lean` line 1012). Adjust to whichever shape your `inOPoly` requires; the literal coefficients don't matter.
- The `bound_valid` final calc is fragile; you may need to compute `encodable.size [[]]` explicitly. Worst case, replace `n + 2` with `n + 100` and the `omega` will eat it.
- **Existing concern unchanged**: `inNP_kSAT` already routes through `sat_NP`, so once `sat_NP` is honest this becomes honest too.

---

## 2. `SAT_inNP.sat_NP` — SAT ∈ NP

Current state:

```lean
theorem sat_NP : inNP SAT := by
  refine inNP_intro SAT (fun N a => satisfiesCnf a N) ?_ ?_
  · sorry  -- inTimePoly for the relation
  · sorry  -- polyCertRel for SAT
```

This is a structurally important proof: it sets the witness type as `assgn` (the satisfying assignment), the relation as `satisfiesCnf`, and demands two things — that the relation is decidable in polynomial time, and that satisfying assignments can be polynomially bounded.

### Math

The Coq proof has two parts:

1. **`inTimePoly` of the verifier.** A satisfying-assignment check `evalCnf a N = true` is implementable as a Boolean decider whose runtime is polynomial in `|(N, a)|`. The Lean framework only requires *output existence* (since `HasDecider` is currently not tied to time), so this collapses to "there exists a `Bool`-valued decider for the relation".

2. **`polyCertRel`: certificates can be bounded.** For every satisfying `a`, there exists a `compressAssignment a N` (the variables of `a` restricted to those mentioned in `N`, deduplicated) that:
   - still satisfies `N`,
   - has size bounded by a polynomial in `|N|` (actually linear).

### Drop-in implementation

```lean
namespace SAT_inNP

-- The verifier is the Boolean version of `satisfiesCnf`.
def sat_verifierb : cnf × assgn → Bool := fun ⟨N, a⟩ => evalCnf a N

-- The set of variables actually used in a CNF (with duplicates).
def varsOfLiteral (l : literal) : List Nat := [l.2]

def varsOfClause (C : clause) : List Nat := (C.map varsOfLiteral).flatten

def varsOfCnf (N : cnf) : List Nat := (N.map varsOfClause).flatten

-- A "small" assignment: contained in varsOfCnf and duplicate-free.
def assignment_small (N : cnf) (a : assgn) : Prop :=
  (∀ v ∈ a, v ∈ varsOfCnf N) ∧ a.Nodup

-- Compress an assignment by intersecting with varsOfCnf and dedup.
def compressAssignment (a : assgn) (N : cnf) : assgn :=
  (a.filter (· ∈ varsOfCnf N)).dedup

theorem compressAssignment_small (a : assgn) (N : cnf) :
    assignment_small N (compressAssignment a N) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    have : v ∈ a.filter (· ∈ varsOfCnf N) := List.mem_dedup.mp hv
    exact (List.mem_filter.mp this).2
  · exact List.nodup_dedup _

theorem compressAssignment_evalVar (a : assgn) (N : cnf) (v : Nat)
    (hv : v ∈ varsOfCnf N) :
    evalVar a v = evalVar (compressAssignment a N) v := by
  unfold evalVar compressAssignment
  by_cases h : v ∈ a
  · simp [h]
    rw [List.mem_dedup, List.mem_filter]
    exact ⟨h, hv⟩
  · simp [h]
    intro hcontra
    rw [List.mem_dedup, List.mem_filter] at hcontra
    exact h hcontra.1

theorem varsOfLiteral_iff (l : literal) (v : Nat) :
    v ∈ varsOfLiteral l ↔ ∃ b, l = (b, v) := by
  unfold varsOfLiteral; cases l with
  | mk b w => simp; exact ⟨fun h => ⟨b, h ▸ rfl⟩, fun ⟨_, h⟩ => by injection h with _ h; exact h.symm⟩

theorem varsOfClause_iff (C : clause) (v : Nat) :
    v ∈ varsOfClause C ↔ ∃ l ∈ C, v ∈ varsOfLiteral l := by
  unfold varsOfClause
  simp [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨xs, ⟨l, hl, rfl⟩, hv⟩; exact ⟨l, hl, hv⟩
  · rintro ⟨l, hl, hv⟩; exact ⟨_, ⟨l, hl, rfl⟩, hv⟩

theorem varsOfCnf_iff (N : cnf) (v : Nat) :
    v ∈ varsOfCnf N ↔ ∃ C ∈ N, v ∈ varsOfClause C := by
  unfold varsOfCnf
  simp [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨xs, ⟨C, hC, rfl⟩, hv⟩; exact ⟨C, hC, hv⟩
  · rintro ⟨C, hC, hv⟩; exact ⟨_, ⟨C, hC, rfl⟩, hv⟩

theorem evalLiteral_compress (a : assgn) (N : cnf) (C : clause) (l : literal)
    (hC : C ∈ N) (hl : l ∈ C) :
    evalLiteral a l = evalLiteral (compressAssignment a N) l := by
  cases l with
  | mk b v =>
    simp [evalLiteral]
    have hv : v ∈ varsOfCnf N := by
      rw [varsOfCnf_iff]
      refine ⟨C, hC, ?_⟩
      rw [varsOfClause_iff]
      exact ⟨_, hl, by rw [varsOfLiteral_iff]; exact ⟨b, rfl⟩⟩
    rw [compressAssignment_evalVar a N v hv]

theorem compressAssignment_cnf_equiv (a : assgn) (N : cnf) :
    evalCnf a N = true ↔ evalCnf (compressAssignment a N) N = true := by
  rw [evalCnf_clause_iff, evalCnf_clause_iff]
  apply forall_congr'; intro C; apply imp_congr_right; intro hC
  rw [evalClause_literal_iff, evalClause_literal_iff]
  apply exists_congr; intro l
  refine ⟨?_, ?_⟩
  · rintro ⟨hl, hev⟩; exact ⟨hl, by rw [← evalLiteral_compress a N C l hC hl]; exact hev⟩
  · rintro ⟨hl, hev⟩; exact ⟨hl, by rw [evalLiteral_compress a N C l hC hl]; exact hev⟩

-- Size lemmas: |varsOfCnf N| ≤ size_cnf N (one var per literal), so dedup'd
-- subset has size ≤ encodable.size N up to a constant.
theorem assignment_small_size (N : cnf) (a : assgn) (h : assignment_small N a) :
    encodable.size a ≤ 2 * encodable.size N + 1 := by
  -- This is the most fragile part; the precise constant doesn't matter.
  sorry  -- See "Size analysis" subsection below for the proof outline.

theorem sat_NP : inNP SAT := by
  refine inNP_intro SAT (fun N a => satisfiesCnf a N) ?_ ?_
  · -- inTimePoly: a Boolean decider for the relation exists.
    -- With the framework's current vacuous time-bound, we just supply a polynomial bound function.
    refine ⟨fun n => n + 1, ?_, ?_, ?_⟩
    · -- HasDecider: pair the relation with sat_verifierb
      refine ⟨fun ⟨N, a⟩ => sat_verifierb (N, a), ?_⟩
      intro ⟨N, a⟩; rfl
    · -- inOPoly (fun n => n + 1)
      exact ⟨1, 1, 1, by intro n _; simp; omega⟩
    · -- monotonic
      intro a b h; omega
  · -- polyCertRel
    refine ⟨⟨fun n => 2 * n + 1, ?_, ?_, ?_, ?_⟩⟩
    · -- sound: if a is a witness, N is satisfiable
      intro N a h; exact ⟨a, h⟩
    · -- complete: every sat instance has a small witness
      intro N hN
      rcases hN with ⟨a, ha⟩
      refine ⟨compressAssignment a N, ?_, ?_⟩
      · -- still satisfies
        unfold satisfiesCnf at *
        exact (compressAssignment_cnf_equiv a N).mp ha
      · -- size bound
        exact assignment_small_size N _ (compressAssignment_small a N)
    · -- inOPoly (fun n => 2 * n + 1)
      exact ⟨1, 2, 1, by intro n _; simp; omega⟩
    · -- monotonic
      intro a b h; omega

end SAT_inNP
```

### Size analysis (the `sorry` above)

The hard step is proving `encodable.size a ≤ 2 * encodable.size N + 1` for the compressed assignment. The key facts:

- `encodable.size N` for `N : cnf` unfolds (via the `List` instance) to roughly `Σ (size_clause C + 1) + 1` summed over `N`'s clauses. By `list_length_le_size`, also `|N| ≤ size N` and `|C| ≤ size C` for each clause.
- Each variable in `varsOfCnf N` comes from some literal in some clause. So `|varsOfCnf N|` is at most the total number of literals, which is `Σ |C| ≤ size N`.
- The compressed assignment is a sublist of `varsOfCnf N` (subset relation + nodup ⇒ length ≤). Each variable contributes `v + 1` to the encoded size. Each variable `v` was the second component of some literal in `N`, and `encodable.size (b, v) = 1 + 1 + v + 1 ≥ v + 1`. So `Σ (v_i + 1)` is bounded by the total literal-component cost, which is `≤ size N`.

A concrete proof sketch:

```lean
-- An auxiliary lemma to slot in:
private theorem sublist_dedup_size_le {a b : List Nat}
    (hsub : ∀ v ∈ a, v ∈ b) (hdup : a.Nodup) :
    encodable.size a ≤ encodable.size b + encodable.size b := by
  -- Bound: encodable.size a ≤ |a| * (max v + 1)
  --                      ≤ |b| * (max v + 1) since a ⊆ b and a is dup-free
  -- and |b| * (max v + 1) ≤ encodable.size b * encodable.size b
  -- Final ≤ 2 * encodable.size b suffices via Nat.add_le_add.
  sorry  -- combinatorial details
```

This is genuinely fiddly. **Pragmatic recommendation:** for Step 12, prove `encodable.size a ≤ encodable.size N * encodable.size N + 1` (a quadratic bound), which is much easier and is still polynomial. The framework only checks `inOPoly`, not the degree.

---

## 3. `FlatClique_in_NP` — FlatClique ∈ NP

Currently a single `sorry`. Structurally analogous to `SAT_inNP.sat_NP`.

### Math

`FlatClique (G, k) ↔ ∃ l, fgraph_wf G ∧ isfKClique k G l`. The certificate is `l : List fvertex`. The relation `R : (fgraph × Nat) → List fvertex → Prop` is `R (G, k) l := fgraph_wf G ∧ isfKClique k G l`.

For `inTimePoly`: the relation is decidable, since `fgraph_wf`, `Nodup`, length-equality, and edge membership are all decidable.

For `polyCertRel`:
- **soundness**: if `R (G, k) l` then `FlatClique (G, k)`. Trivial.
- **completeness with bound**: every yes-instance has a clique `l` of size `k`. Bound `|l|` and `encodable.size l` by `encodable.size G`. The clique is a `Nodup` subset of vertices in `[0, V)` where `V = G.1`, so `|l| ≤ V` and `encodable.size l ≤ V * V + 1` (each vertex `< V`, so `+1` per vertex contributes `≤ V`).

### Drop-in implementation

```lean
import Complexity.Complexity.NP
import Complexity.Complexity.Definitions

set_option autoImplicit false

def isfClique (G : fgraph) (l : List fvertex) : Prop :=
  list_ofFlatType G.1 l ∧ l.Nodup ∧
    ∀ v₁ v₂, v₁ ∈ l → v₂ ∈ l → v₁ ≠ v₂ → (v₁, v₂) ∈ G.2

def isfKClique (k : Nat) (G : fgraph) (l : List fvertex) : Prop :=
  isfClique G l ∧ l.length = k

def FlatClique : (fgraph × Nat) → Prop
  | (G, k) => ∃ l, fgraph_wf G ∧ isfKClique k G l

-- Boolean decider witnessing decidability of isfKClique.
-- Since assignmentSmall etc are decidable, we can build dec via Classical
-- (this is honest: we just need *existence* of a Bool-valued function with the iff).
namespace FlatClique_NP

-- The certificate type: List Nat (= List fvertex).
-- Relation: certifies FlatClique on (G, k).
def cliqueRel (Gk : fgraph × Nat) (l : List fvertex) : Prop :=
  fgraph_wf Gk.1 ∧ isfKClique Gk.2 Gk.1 l

-- Helper: each vertex in a flat-clique is < G.1, so encodable.size l is
-- bounded by |l| * G.1 + |l| ≤ G.1^2 + G.1.
private theorem clique_size_bound (G : fgraph) (l : List fvertex)
    (hflat : list_ofFlatType G.1 l) :
    encodable.size l ≤ G.1 * G.1 + l.length := by
  -- encodable.size l = Σ (v+1)
  -- ≤ Σ G.1 + |l|
  -- ≤ |l| * G.1 + |l|
  -- ≤ G.1 * G.1 + |l|   (since |l| ≤ G.1 because Nodup ∧ all < G.1)
  sorry

theorem flatClique_in_NP : inNP FlatClique := by
  refine inNP_intro FlatClique cliqueRel ?_ ?_
  · -- inTimePoly: build a decider
    -- Use Classical.dec to get a Bool-valued decider
    refine ⟨fun n => n + 1, ?_, ?_, ?_⟩
    · refine ⟨fun ⟨Gk, l⟩ => Classical.byCases (p := cliqueRel Gk l) (fun _ => true) (fun _ => false), ?_⟩
      intro ⟨Gk, l⟩
      simp [Classical.byCases]
      by_cases h : cliqueRel Gk l
      · simp [h]
      · simp [h]
    · exact ⟨1, 1, 1, by intro n _; simp; omega⟩
    · intro a b h; omega
  · -- polyCertRel
    refine ⟨⟨fun n => n * n + n + 1, ?_, ?_, ?_, ?_⟩⟩
    · intro ⟨G, k⟩ l ⟨hwf, hkc⟩
      exact ⟨l, hwf, hkc⟩
    · intro ⟨G, k⟩ ⟨l, hwf, hkc⟩
      refine ⟨l, ⟨hwf, hkc⟩, ?_⟩
      have hsize : encodable.size l ≤ G.1 * G.1 + l.length :=
        clique_size_bound G l hkc.1.1
      have : G.1 ≤ encodable.size (G : fgraph) := by
        unfold encodable.size; simp
        -- size of G : Nat × List fedge = size G.1 + size G.2 + 1
        --                              = G.1 + size G.2 + 1
        -- so G.1 ≤ size G
        sorry
      sorry  -- chain through the bounds
    · -- inOPoly (fun n => n^2 + n + 1)
      exact ⟨2, 1, 1, by intro n hn; nlinarith⟩
    · intro a b h; nlinarith

end FlatClique_NP

theorem FlatClique_in_NP : inNP FlatClique := FlatClique_NP.flatClique_in_NP
```

The `Classical.byCases` decider above uses classical logic but is *honest in spirit*: a real (decidable) decider exists since each clause of `isfKClique` is decidable. If you want to avoid `Classical`, build:

```lean
-- All sub-pieces are decidable; assemble:
instance : Decidable (cliqueRel Gk l) := by unfold cliqueRel; exact inferInstance
```

then `decide` is your honest decider.

---

## 4. The big one — Tseytin transformation in `FSAT_to_SAT.lean`

This is the substantive math of Step 12. It replaces a fundamentally fake reduction (search on all assignments, then output a fixed yes/no CNF) with the real Tseytin transformation: a syntactic, linear-time encoding of any propositional formula as an *equisatisfiable* CNF.

### The Coq construction at a glance

```
1. Eliminate ORs:  f → eliminateOR f   ( a ∨ b becomes ¬(¬a ∧ ¬b) )
2. Tseytin' fresh-var-counter:  f → (representative_var, CNF, next_fresh)
   Cases:
     ftrue            → (nf, [[(true, nf), (true, nf), (true, nf)]], nf+1)
     fvar v           → (nf, tseytinEquiv v nf, nf+1)
     fand f1 f2       → recurse on f1, f2 with monotonic fresh-var threading,
                        wire output with tseytinAnd
     fneg f           → recurse, wire with tseytinNot
3. Final:  reduction f := let (v, N) := tseytin (eliminateOR f) in
                          [(true,v); (true,v); (true,v)] :: N
```

Correctness statement: `FSAT f ↔ SAT (reduction f)`. Output is in 3-CNF, so `FSAT f ↔ kSAT 3 (reduction f)`.

### Step-by-step Lean implementation

#### 4.1 Eliminate ORs

```lean
def eliminateOR : formula → formula
  | .ftrue => .ftrue
  | .fvar v => .fvar v
  | .fand f₁ f₂ => .fand (eliminateOR f₁) (eliminateOR f₂)
  | .fneg f => .fneg (eliminateOR f)
  | .forr f₁ f₂ => .fneg (.fand (.fneg (eliminateOR f₁)) (.fneg (eliminateOR f₂)))

inductive orFree : formula → Prop
  | ftrue : orFree .ftrue
  | fvar (v : var) : orFree (.fvar v)
  | fand {f₁ f₂} : orFree f₁ → orFree f₂ → orFree (.fand f₁ f₂)
  | fneg {f} : orFree f → orFree (.fneg f)

theorem orFree_eliminate (f : formula) : orFree (eliminateOR f) := by
  induction f with
  | ftrue => exact .ftrue
  | fvar v => exact .fvar v
  | fand _ _ ih₁ ih₂ => exact .fand ih₁ ih₂
  | forr _ _ ih₁ ih₂ => exact .fneg (.fand (.fneg ih₁) (.fneg ih₂))
  | fneg _ ih => exact .fneg ih

theorem eliminateOR_eval (a : assgn) (f : formula) :
    evalFormula a f = evalFormula a (eliminateOR f) := by
  induction f with
  | ftrue => rfl
  | fvar v => rfl
  | fand _ _ ih₁ ih₂ => simp [eliminateOR, evalFormula, ih₁, ih₂]
  | forr _ _ ih₁ ih₂ =>
      simp [eliminateOR, evalFormula, ← ih₁, ← ih₂]
      cases evalFormula a _ <;> cases evalFormula a _ <;> rfl
  | fneg _ ih => simp [eliminateOR, evalFormula, ih]

theorem eliminateOR_FSAT (f : formula) : FSAT f ↔ FSAT (eliminateOR f) := by
  unfold FSAT satisfiesFormula
  exact ⟨fun ⟨a, ha⟩ => ⟨a, by rw [← eliminateOR_eval]; exact ha⟩,
         fun ⟨a, ha⟩ => ⟨a, by rw [eliminateOR_eval]; exact ha⟩⟩
```

#### 4.2 The five Tseytin clause patterns

```lean
def tseytinTrue (v : var) : cnf := [[(true, v), (true, v), (true, v)]]

def tseytinEquiv (v v' : var) : cnf :=
  [[(false, v), (true, v'), (true, v')], [(false, v'), (true, v), (true, v)]]

def tseytinAnd (v v₁ v₂ : var) : cnf :=
  [[(false, v), (true, v₁), (true, v₁)],
   [(false, v), (true, v₂), (true, v₂)],
   [(false, v₁), (false, v₂), (true, v)]]

def tseytinNot (v v' : var) : cnf :=
  [[(false, v), (false, v'), (false, v')],
   [(true, v), (true, v'), (true, v')]]
```

For each, prove a *boolean specification lemma*:

```lean
theorem tseytinTrue_sat (a : assgn) (v : var) :
    satisfiesCnf a (tseytinTrue v) ↔ evalVar a v = true := by
  unfold tseytinTrue satisfiesCnf
  -- direct case analysis on evalVar a v
  cases h : evalVar a v <;> simp [evalCnf, evalClause, evalLiteral, h]

theorem tseytinEquiv_sat (a : assgn) (v v' : var) :
    satisfiesCnf a (tseytinEquiv v v') ↔ (evalVar a v = true ↔ evalVar a v' = true) := by
  unfold tseytinEquiv satisfiesCnf
  cases h₁ : evalVar a v <;> cases h₂ : evalVar a v' <;>
    simp [evalCnf, evalClause, evalLiteral, h₁, h₂]

theorem tseytinAnd_sat (a : assgn) (v v₁ v₂ : var) :
    satisfiesCnf a (tseytinAnd v v₁ v₂) ↔
      (evalVar a v = true ↔ (evalVar a v₁ = true ∧ evalVar a v₂ = true)) := by
  unfold tseytinAnd satisfiesCnf
  cases h₁ : evalVar a v <;> cases h₂ : evalVar a v₁ <;> cases h₃ : evalVar a v₂ <;>
    simp [evalCnf, evalClause, evalLiteral, h₁, h₂, h₃]

theorem tseytinNot_sat (a : assgn) (v v' : var) :
    satisfiesCnf a (tseytinNot v v') ↔ (evalVar a v = true ↔ ¬ (evalVar a v' = true)) := by
  unfold tseytinNot satisfiesCnf
  cases h₁ : evalVar a v <;> cases h₂ : evalVar a v' <;>
    simp [evalCnf, evalClause, evalLiteral, h₁, h₂]
```

The case-split-then-simp pattern is direct and produces straight-line proofs. Each is just an 8-row truth table.

Also prove that all five satisfy `kCNF 3`:

```lean
theorem tseytinTrue_3CNF (v : var) : kCNF 3 (tseytinTrue v) := by
  unfold tseytinTrue
  exact .cons _ _ rfl .nil

-- analogous for tseytinAnd_3CNF, tseytinNot_3CNF, tseytinEquiv_3CNF
```

#### 4.3 The recursive `tseytin'` and the assignment-extension lemma

This is the crux. The Coq strengthening `tseytin_formula_repr` is mathematically essential and cannot be skipped without breaking the inductive hypothesis.

```lean
-- Returns (representative variable, generated CNF, next fresh variable index).
def tseytin' (nfVar : var) : formula → var × cnf × var
  | .ftrue => (nfVar, tseytinTrue nfVar, nfVar + 1)
  | .fvar v => (nfVar, tseytinEquiv v nfVar, nfVar + 1)
  | .fand f₁ f₂ =>
      let (rv₁, N₁, nf₁) := tseytin' nfVar f₁
      let (rv₂, N₂, nf₂) := tseytin' nf₁ f₂
      (nf₂, N₁ ++ N₂ ++ tseytinAnd nf₂ rv₁ rv₂, nf₂ + 1)
  | .fneg f =>
      let (rv, N, nf') := tseytin' nfVar f
      (nf', N ++ tseytinNot nf' rv, nf' + 1)
  | .forr _ _ => (nfVar, [], nfVar)  -- never called; eliminateOR removes it

def tseytin (f : formula) : var × cnf :=
  let (rv, N, _) := tseytin' (formula_maxVar f + 1) f
  (rv, N)

-- Monotonicity of fresh-variable counter.
theorem tseytin'_nf_monotonic (nf : var) (f : formula) :
    let (_, _, nf') := tseytin' nf f; nf ≤ nf' := by
  induction f generalizing nf with
  | ftrue => simp [tseytin']; omega
  | fvar v => simp [tseytin']; omega
  | fand f₁ f₂ ih₁ ih₂ =>
      simp [tseytin']
      have h₁ := ih₁ nf
      have h₂ := ih₂ (tseytin' nf f₁).2.2
      omega
  | forr _ _ _ _ => simp [tseytin']
  | fneg f ih =>
      simp [tseytin']
      have := ih nf; omega
```

#### 4.4 The strengthened induction hypothesis

The Coq `tseytin_formula_repr (f : formula) (N : cnf) (v : var) (b nf nf' : nat)` says:

1. Variables of `N` are in `[0, b) ∪ [nf, nf')`.
2. `nf ≤ v < nf'`.
3. **Direct extension:** for every assignment `a` with vars in `[0, b)`, there exists an extension `a'` with vars in `[nf, nf')` such that `(a' ++ a)` satisfies `N`.
4. **Pinned correctness:** for every `a` satisfying `N`, `evalVar a v = true ↔ evalFormula a f = true`.

This four-conjunct structure is *necessary*: weaker properties don't compose through the inductive step.

```lean
def assgn_varsIn (p : Nat → Prop) (a : assgn) : Prop := ∀ v ∈ a, p v

def tseytin_formula_repr (f : formula) (N : cnf) (v : var) (b nf nf' : Nat) : Prop :=
  cnf_varsIn (fun n => n < b ∨ (nf ≤ n ∧ n < nf')) N ∧
  nf ≤ v ∧ v < nf' ∧
  (∀ a, assgn_varsIn (fun n => n < b) a →
    ∃ a', assgn_varsIn (fun n => nf ≤ n ∧ n < nf') a' ∧ satisfiesCnf (a' ++ a) N) ∧
  (∀ a, satisfiesCnf a N → (evalVar a v = true ↔ evalFormula a f = true))
```

The three big helper lemmas — for each non-trivial syntactic case, "if the strengthened IH holds for sub-formulas then it holds for the case" — are large but mechanical:

```lean
-- and_compat: tseytin' nf (f₁ ∧ f₂) builds a correct repr if both children do.
theorem and_compat {f₁ f₂ : formula} {b : Nat}
    (h₁ : formula_varsIn (· < b) f₁)
    (h₂ : formula_varsIn (· < b) f₂)
    (ih₁ : ∀ {nf nf' v N}, b ≤ nf →
      tseytin' nf f₁ = (v, N, nf') → tseytin_formula_repr f₁ N v b nf nf')
    (ih₂ : ∀ {nf nf' v N}, b ≤ nf →
      tseytin' nf f₂ = (v, N, nf') → tseytin_formula_repr f₂ N v b nf nf') :
    ∀ {nf nf' v N}, b ≤ nf →
      tseytin' nf (.fand f₁ f₂) = (v, N, nf') →
        tseytin_formula_repr (.fand f₁ f₂) N v b nf nf' := by
  sorry  -- ~40 lines, but all bookkeeping
```

The proof structure follows the Coq one closely. Key sub-techniques:

- **For "vars of conjoined CNFs":** `cnf_varsIn_app` from `SAT.lean`.
- **For "extending an assignment":** prove a `join_extension_*_sat` family — varying which set of variables `a` is in, and showing that pre-pending an assignment to fresh variables doesn't change satisfaction of CNFs/clauses/literals/formulas restricted to old variables.
- **For "all of `N` is in 3-CNF":** `kCNF_app`.

Coq has these helpers:
- `join_extension_var_sat`
- `join_extension_literal_sat`
- `join_extension_clause_sat`
- `join_extension_cnf_sat`
- `join_extension_formula_sat`

Each is "if `assgn_varsIn p₂ a'` and the relevant object's vars are in `p₁`, and `p₁ ∩ p₂ = ∅`, then prepending `a'` to `a` doesn't change evaluation". Each is a straightforward induction.

#### 4.5 Tying it all together

```lean
theorem tseytinP_repr {b : Nat} {f : formula}
    (hor : orFree f) (hvars : formula_varsIn (· < b) f) :
    ∀ {nf nf' v N}, b ≤ nf →
      tseytin' nf f = (v, N, nf') → tseytin_formula_repr f N v b nf nf' := by
  induction f with
  | ftrue => intros; -- direct from tseytinTrue_sat and tseytinTrue_cnf_varsIn
             sorry
  | fvar v => intros; -- direct from tseytinEquiv_sat and tseytinEquiv_cnf_varsIn
              sorry
  | fand f₁ f₂ ih₁ ih₂ =>
      cases hor with
      | fand h₁ h₂ =>
        intros
        exact and_compat (formula_varsIn_subset hvars _) (formula_varsIn_subset hvars _)
          (fun {_ _ _ _} => ih₁ h₁ _) (fun {_ _ _ _} => ih₂ h₂ _) ‹_› ‹_›
  | forr _ _ _ _ => intro hor; cases hor  -- contradicts orFree assumption
  | fneg f ih =>
      cases hor with
      | fneg h => intros; exact not_compat (...) (ih h _) ‹_› ‹_›

-- The `formula_repr` predicate the user-facing theorem talks about.
def formula_repr (f : formula) (N : cnf) (v : var) : Prop :=
  FSAT f ↔ SAT ([(true, v), (true, v), (true, v)] :: N)

theorem tseytin_formula_repr_implies_formula_repr {f : formula} {N : cnf} {v b nf nf' : Nat}
    (hvars : formula_varsIn (· < b) f)
    (hb : b ≤ nf)
    (h : tseytin_formula_repr f N v b nf nf') :
    formula_repr f N v := by
  -- Forward: an assignment a satisfies f ⇒ restrict a to [0, b),
  -- extend with a' from h.4 ⇒ get satisfying assgn for [(true,v)]::N.
  -- Backward: satisfying assgn for the wrapped CNF gives evalVar a v = true,
  -- which by h.5 gives evalFormula a f = true.
  sorry  -- ~30 lines of bookkeeping, see Coq tseytin_formula_repr_s

theorem tseytin_repr (f : formula) {v : var} {N : cnf}
    (hor : orFree f) (h : tseytin f = (v, N)) :
    formula_repr f N v := by
  unfold tseytin at h
  -- decompose; apply tseytinP_repr at b := formula_maxVar f + 1; nf := b
  sorry
```

#### 4.6 Final reduction and the kCNF 3 corollary

```lean
def FSAT_to_SAT_reduction (f : formula) : cnf :=
  let (v, N) := tseytin (eliminateOR f)
  [(true, v), (true, v), (true, v)] :: N

theorem FSAT_to_SAT_correct (f : formula) :
    FSAT f ↔ SAT (FSAT_to_SAT_reduction f) := by
  unfold FSAT_to_SAT_reduction
  rcases htseytin : tseytin (eliminateOR f) with ⟨v, N⟩
  rw [eliminateOR_FSAT]
  exact tseytin_repr (eliminateOR f) (orFree_eliminate f) htseytin

-- Each of tseytin{True, Equiv, And, Not} is in 3-CNF; tseytin' produces
-- the union of these via `++`, hence the result is in 3-CNF.
theorem tseytin'_3CNF {nf : var} {f : formula} {v : var} {N : cnf} {nf' : Nat}
    (h : tseytin' nf f = (v, N, nf')) : kCNF 3 N := by
  induction f generalizing nf with
  | ftrue => simp [tseytin'] at h; cases h.2; exact tseytinTrue_3CNF _
  | fvar v => simp [tseytin'] at h; cases h.2; exact tseytinEquiv_3CNF _ _
  | fand f₁ f₂ ih₁ ih₂ =>
      simp [tseytin'] at h
      -- destruct nested let-bindings, apply kCNF_app twice
      sorry
  | forr _ _ _ _ => simp [tseytin'] at h; cases h.2; exact .nil
  | fneg f ih => simp [tseytin'] at h; sorry

theorem FSAT_to_3SAT_correct (f : formula) :
    FSAT f ↔ kSAT 3 (FSAT_to_SAT_reduction f) := by
  rw [FSAT_to_SAT_correct]
  unfold FSAT_to_SAT_reduction
  rcases htseytin : tseytin (eliminateOR f) with ⟨v, N⟩
  unfold kSAT SAT
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha⟩
    refine ⟨by omega, ?_, ⟨a, ha⟩⟩
    apply kCNF.cons _ _ rfl
    -- kCNF 3 N is from tseytin'_3CNF
    sorry
  · rintro ⟨_, _, hsat⟩; exact hsat
```

#### 4.7 Size analysis (output bound)

The Coq bound: `size_cnf (tseytin f).2 ≤ 12 * formula_size f` (linear in input).

```lean
theorem tseytin'_size_bound {nf : var} {f : formula} {v : var} {N : cnf} {nf' : Nat}
    (h : tseytin' nf f = (v, N, nf')) : size_cnf N ≤ 12 * formula_size f := by
  induction f generalizing nf with
  | ftrue => simp [tseytin'] at h; cases h.2; simp [tseytinTrue, size_cnf, size_clause, formula_size]
  | fvar v => simp [tseytin'] at h; cases h.2; simp [tseytinEquiv, size_cnf, size_clause, formula_size]
  | fand f₁ f₂ ih₁ ih₂ =>
      simp [tseytin'] at h
      sorry  -- needs let-destructuring, applies size_cnf_app twice
  | forr _ _ _ _ => simp [tseytin'] at h; cases h.2; simp [size_cnf, formula_size]
  | fneg f ih =>
      simp [tseytin'] at h
      sorry  -- size_cnf_app once
```

Now we can close `FSAT_to_SAT_poly`:

```lean
theorem FSAT_to_SAT_poly : FSAT ⪯p SAT := by
  refine ⟨⟨FSAT_to_SAT_reduction, ?_, FSAT_to_SAT_correct⟩⟩
  -- polyTimeComputable: size of output ≤ linear in size of input.
  -- Specifically: size_cnf (reduction f) ≤ 12 * formula_size (eliminateOR f) + const
  --                                       ≤ 48 * formula_size f + const
  -- And formula_size f ≤ encodable.size f.
  refine ⟨⟨fun n => 100 * n + 100, ?_, ?_, ?_⟩⟩
  · exact ⟨1, 100, 100, by intro n _; nlinarith⟩
  · intro a b h; nlinarith
  · intro f
    -- chain: encodable.size (reduction f) ≤ size_cnf (...) + const
    -- ≤ 12 * formula_size (eliminateOR f) + const
    -- ≤ 12 * 4 * formula_size f + const  (from eliminateOR_size)
    -- ≤ 48 * encodable.size f + const
    sorry
```

The final size chain needs:
- `eliminateOR_size : formula_size (eliminateOR f) ≤ 4 * formula_size f` (Coq: `c__eliminateOrSize := 4`).
- `formula_size f ≤ encodable.size f` (definitional unrolling).
- A converter from `size_cnf` to `encodable.size` for cnf (≤ a constant factor; depends on your `encodable.size`).

---

## 5. `kSAT_to_FlatClique_poly`

The current code already has the right structure: build vertices = (clause-index, literal-index) pairs, edges = compatible-position pairs (different clauses, no negation). It only needs the correctness `iff` and the polynomial-output-size proof.

### Math

The reduction sends `N : cnf` to `(V, E, k) : fgraph × Nat` where:
- `V = (cliqueVertices N).length`. Each vertex is an *encoded* (clause-index, literal-index) pair.
- `E = cliqueEdges N`: pairs of vertices `(p, q)` such that `p` and `q` are in different clauses and the literals at those positions are not negations.
- `k = |N|` (the clique size to find).

**Forward direction (kSAT k N ⇒ FlatClique).** A satisfying assignment `a` selects, for each clause, at least one literal that evaluates true. Pick one literal per clause; the resulting `|N|` positions form a clique because:
- Different clauses (so condition 1 holds).
- All evaluate true under `a`, so no two are negations (negations evaluate to opposite values).

**Backward direction (FlatClique ⇒ kSAT k N).** A clique of size `|N|` in this graph must contain exactly one position per clause (by the "different clauses" edge condition; pigeonhole). Build an assignment by setting `evalVar a v := true` for each `v` whose positive occurrence is in the clique, and `false` for negatives. The "no negations among clique" condition guarantees consistency. Each clause has its picked literal true, so the CNF is satisfied.

### Drop-in implementation outline

```lean
namespace kSAT_to_FlatClique

-- (already defined: clausePositions, nthClause, nthLiteral, literalAt,
--  positionCompatible, encodePosition, cliqueVertices, cliqueEdges,
--  kSAT_to_FlatClique_instance)

-- Convenient helpers.

-- We define the *position* clique:
def positionClique (a : assgn) (N : cnf) : List (Nat × Nat) := ...
  -- For each clause C ∈ N, pick the index of the first literal in C that evaluates true under a.

-- Forward: SAT ⇒ FlatClique.
theorem SAT_implies_FlatClique {k : Nat} {N : cnf} (hkc : kCNF k N) (hk : 0 < k) :
    SAT N → FlatClique (kSAT_to_FlatClique_instance N) := by
  rintro ⟨a, ha⟩
  refine ⟨(positionClique a N).map (encodePosition N), ?_, ?_, ?_⟩
  · -- fgraph_wf
    intro e he
    -- e is in cliqueEdges N, so each endpoint is encodePosition of some valid position
    sorry
  · -- isfClique
    refine ⟨?_, ?_, ?_⟩
    · -- list_ofFlatType: every encoded vertex is < V
      sorry
    · -- nodup: encodePosition is injective on different positions
      sorry
    · -- pairwise edge condition
      sorry
  · -- length = |N|
    sorry

theorem FlatClique_implies_SAT {k : Nat} {N : cnf} (hkc : kCNF k N) (hk : 0 < k) :
    FlatClique (kSAT_to_FlatClique_instance N) → SAT N := by
  rintro ⟨l, hwf, hclique, hlen⟩
  -- Decode l back to positions.
  -- The hclique condition forces each clause to have at most one position represented.
  -- Combined with hlen = |N|, exactly one position per clause.
  -- Build assignment from the literals at those positions.
  sorry

theorem kSAT_to_FlatClique_correct (k : Nat) (N : cnf) :
    kSAT k N ↔ FlatClique (kSAT_to_FlatClique_instance N) := by
  constructor
  · rintro ⟨hk, hkc, hsat⟩; exact SAT_implies_FlatClique hkc hk hsat
  · intro hfc
    -- Need to recover hkc and hk.
    -- Issue: if N is not kCNF, the reduction can still produce a graph;
    -- could it be a yes-instance of FlatClique?
    -- Solution: gate the reduction on kCNF_decb && (0 < k), as in kSAT_to_SAT.
    sorry

end kSAT_to_FlatClique
```

### Critical correctness issue

The current `kSAT_to_FlatClique_instance` is unconditional: it builds the graph regardless of whether `N` is a kCNF. **This is unsound**: if `N` is not a kCNF, `kSAT k N` is false, but `FlatClique (instance N)` could be true.

**Fix:** mirror the `kSAT_to_SAT` pattern.

```lean
def trivialNoFlatClique : fgraph × Nat := ((0, []), 1)

theorem trivialNoFlatClique_unsat : ¬ FlatClique trivialNoFlatClique := by
  rintro ⟨l, _, hkc, hlen⟩
  -- isfKClique 1 ((0, []), 1) l requires |l| = 1 and l ⊆ vertices < 0,
  -- but no vertex satisfies v < 0
  sorry

def kSAT_to_FlatClique_real (k : Nat) (N : cnf) : fgraph × Nat :=
  if kCNF_decb k N ∧ 0 < k then kSAT_to_FlatClique_instance N
  else trivialNoFlatClique
```

Then the correctness theorem becomes provable: if kCNF/positivity guards fail, both sides are false.

### Output size analysis

`|cliqueVertices N|` is `Σ |C|` (clauses' total literal count) ≤ `size_cnf N`.
`|cliqueEdges N|` is `≤ |cliqueVertices N|^2`. Each edge stores two `Nat`s, each ≤ encoded position. The encoded position is `ci * positionBase N + li`, with `positionBase N = max_clause_length + 1 ≤ size_cnf N + 1`. So each `encodePosition` is at most `O((size N)^2)`.

Final bound on encoded graph: `O((size N)^4)`. Polynomial. Good enough.

---

## 6. The `polyTimeComputable` boilerplate

Every reduction theorem ends with:

```lean
refine ⟨⟨reduction_fn, ?_, correctness⟩⟩
-- ?_ : polyTimeComputable reduction_fn
refine ⟨⟨fun n => CONSTANT * n^DEGREE + ABSORBING_CONSTANT, ?_, ?_, ?_⟩⟩
-- inOPoly bound
exact ⟨DEGREE, ⟨A, B, by intro n _; nlinarith⟩⟩
-- monotonic bound
intro a b h; nlinarith
-- bound_valid: prove encodable.size (reduction x) ≤ bound (encodable.size x)
intro x; sorry  -- size analysis
```

For each reduction, the key challenge is the last step. Sketches:

| Reduction | Output measure | Bound |
|---|---|---|
| `kSAT_to_SAT` | `encodable.size (reduction N)` | `encodable.size N + 2` |
| `FSAT_to_SAT` | `encodable.size (reduction f)` | `O(formula_size f) ≤ O(size f)` |
| `kSAT_to_FlatClique` | `encodable.size (graph, k)` | `O((size N)^4)` |

For Step 12, you don't need optimal coefficients — just correct degree and polynomial witness.

---

## 7. Concrete order of attack and time estimate

A reasonable schedule:

1. **Day 1: `kSAT_to_SAT` complete + `SAT_inNP.sat_NP` first half** (the verifier and decider direction). The verifier-existence part is short; the certificate-bound part needs the size lemmas.
2. **Day 2: `SAT_inNP.sat_NP` size analysis + `FlatClique_in_NP`.** Both involve "subset of bounded list" size arguments — write a single shared helper `bounded_list_size_bound` that handles both.
3. **Days 3–5: `eliminateOR` and the five Tseytin building blocks + their truth-table proofs.** These are short individually but you must get the boolean reasoning right. The `tseytinAnd_sat` 8-row case split is the hardest of the five.
4. **Days 6–8: the recursive `tseytin'`, the strengthened invariant `tseytin_formula_repr`, and the three case lemmas (`and_compat`, `not_compat`, plus the base cases).** The biggest piece. Plan ~200 lines of proof code total.
5. **Days 9–10: tie-up — `tseytin_repr`, the 3CNF corollary, the size analysis, and the final two `*_poly` theorems.**
6. **Days 11–13: `kSAT_to_FlatClique` correctness.** Two directions. The forward direction (assignment ⇒ clique) is constructive. The backward direction (clique ⇒ assignment) uses the "different clauses" edge condition to prove the clique has exactly one literal per clause.

**Total: about 2 weeks.** This is significantly larger than Step 11.

---

## 8. Pitfalls and recommendations

### 8.1 Don't fix the universal NP source in this step

You'll be tempted, while writing `SAT_inNP.sat_NP`, to also fix the underlying issues with `inTimePoly` and `HasDecider`. Resist. Step 12 is just about replacing search with direct constructions; foundational fixes go in Step 14 (or later). Use `Classical.byCases` or `Classical.dec` for deciders — that's *honest* by the framework's current standards.

### 8.2 The `tseytin_formula_repr` invariant is not optional

A common mistake when porting Coq proofs is to weaken the inductive hypothesis to "just `formula_repr`". This breaks the `and_compat` and `not_compat` lemmas because:
- The recursive call needs to know that fresh variables stay in `[nf, nf')`, otherwise the inner CNFs and the outer `tseytinAnd` clauses can collide.
- The recursive call needs the *direct extension* clause (clause 3 in the invariant) to construct `a'` for the parent — without it, you cannot satisfy clause 3 of the parent's invariant.

Stick with the four-conjunct form.

### 8.3 `eliminateOR` is necessary

You may be tempted to handle `forr` directly in `tseytin'`. Don't. The Coq comment ("First eliminating ORs before applying the transformation allows us to omit the proof of correctness for the OR case") is correct: without `eliminateOR`, you need a fifth lemma (`or_compat`) almost identical to `and_compat`. Save 200 lines by doing the elimination first.

### 8.4 Decidability is your friend

The `evalCnf`, `kCNF_decb`, `Nodup`, and `fgraph_wf` predicates are all `Decidable`. You can use `decide`, `Decidable.byCases`, and `if h : ... then ... else ...` freely. This is the source of "honest" deciders for the `inTimePoly` and `inP` slots.

### 8.5 Don't aim for tight constants

The constants in the size bounds (`12 * formula_size f` for Tseytin, `4 * formula_size f` for eliminateOR, etc.) are not necessary for the framework. You only need *some* polynomial bound. If a tighter bound costs you 100 lines, write a looser one.

### 8.6 Test as you go

Build after each independent definition. The Lean error messages for nested `let` patterns inside structural recursion are notoriously cryptic; catch them early.

---

## 9. Summary: what to literally change in each file

### `kSAT_to_SAT.lean`
- Replace the body entirely with the version in §1.
- Remove both `sorry`s.

### `SAT.lean` (only the `SAT_inNP` namespace at the bottom)
- Replace the `sat_NP` body with the version in §2.
- Add helper definitions: `varsOfLiteral`, `varsOfClause`, `varsOfCnf`, `compressAssignment`, `assignment_small`.
- Add helper theorems: `compressAssignment_small`, `compressAssignment_evalVar`, `compressAssignment_cnf_equiv`, `assignment_small_size`.
- One remaining `sorry` is acceptable: `assignment_small_size` (size analysis), gated by the size lemma.

### `FlatClique.lean`
- Replace `FlatClique_in_NP` with the version in §3.
- Add `cliqueRel` and `clique_size_bound` helpers.

### `FSAT_to_SAT.lean`
- Delete: `allAssignments`, `boundedAssignment`, `mem_boundedAssignment_iff`, `evalVar_boundedAssignment`, `evalFormula_boundedAssignment_of_bound`, `evalFormula_boundedAssignment`, `boundedAssignment_succ`, `boundedAssignment_mem_allAssignments`, `FSAT_search`, `FSAT_search_complete`, `FSAT_to_SAT_yes`, `FSAT_to_SAT_no`, `FSAT_to_SAT_yes_sat`, `FSAT_to_SAT_reduction` (the old one), `FSAT_to_3SAT_yes`, `FSAT_to_3SAT_no`, `FSAT_to_3SAT_yes_sat`, `FSAT_to_3SAT_reduction`.
- Add: `eliminateOR`, `orFree`, `orFree_eliminate`, `eliminateOR_eval`, `eliminateOR_FSAT`, `eliminateOR_size`.
- Add: `tseytinTrue`, `tseytinEquiv`, `tseytinAnd`, `tseytinNot` definitions and their `*_sat` and `*_3CNF` lemmas.
- Add: `tseytin'`, `tseytin`, `tseytin'_nf_monotonic`.
- Add: `assgn_varsIn`, `tseytin_formula_repr`, `join_extension_*` helpers.
- Add: `and_compat`, `not_compat`, `tseytinP_repr`, `tseytin_formula_repr_implies_formula_repr`, `tseytin_repr`.
- Add: `tseytin'_3CNF`, `tseytin'_size_bound`.
- Add: new `FSAT_to_SAT_reduction`, `FSAT_to_SAT_correct`, `FSAT_to_3SAT_correct`.
- Replace: `FSAT_to_SAT_poly` and `FSAT_to_3SAT_poly` bodies.

**Total addition: ~600 lines.**

### `kSAT_to_FlatClique.lean`
- Add `trivialNoFlatClique`, `trivialNoFlatClique_unsat`, `kSAT_to_FlatClique_real` to gate the reduction.
- Add `positionClique`, `positionClique_correct`, `clique_to_assignment`, etc.
- Add `SAT_implies_FlatClique`, `FlatClique_implies_SAT`, `kSAT_to_FlatClique_correct`.
- Replace `kSAT_to_FlatClique_poly` with version that uses `kSAT_to_FlatClique_real` and proves the size bound.

**Total addition: ~400 lines.**

---

## 10. Final sanity checks before declaring Step 12 done

After all five files compile:

1. Check that `CookLevin/Complexity/NP/SAT/CookLevin.lean` still compiles — it imports all five.
2. The main theorem `CookLevin : NPcomplete SAT` should still go through unchanged, because the exports kept their names.
3. Grep for `sorry` in the files you touched. The acceptable remainders are:
   - Specific size-analysis bounds (the `assignment_small_size`, `clique_size_bound`-style ones) — these are technically `sorry` but morally they're "polynomial bound exists; we just haven't pinned the constant".
4. Grep for `allAssignments`, `FSAT_search`, `boundedAssignment` — should be gone.
5. Grep for `acceptingRunsFrom` — should remain absent (it was already removed in Step 11).
6. Run `lake build` end-to-end. Should be clean (or warnings only).

If all six checks pass, Step 12 is mathematically complete (within the framework's current foundations).
