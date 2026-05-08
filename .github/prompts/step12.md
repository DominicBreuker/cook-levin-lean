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

# Step 12 finishing guide — closing the remaining sorries

You have an excellent draft. Most of the structural work is done correctly: the Tseytin clause gadgets, their truth-table proofs, the recursive `tseytin'`, the `tseytin_formula_repr` invariant shape, the `eliminateOR` machinery, and the entire `FSAT_to_SAT_tseytin_correct` outer proof are sound. What remains are *gaps*, not architectural problems.

There are **10 sorries** total spread across four files:

| File | Line(s) | What's missing |
|---|---|---|
| `FSAT_to_SAT.lean` | 270 | `fvar` "ext" clause |
| `FSAT_to_SAT.lean` | 292, 332 | `fand`/`fneg` `cnf_varsIn` |
| `FSAT_to_SAT.lean` | 295, 335 | `fand`/`fneg` "ext" |
| `FSAT_to_SAT.lean` | 268 | `omega` bug in `fvar` `cnf_varsIn` |
| `FSAT_to_SAT.lean` | 424 | size bound |
| `SAT.lean` | 206 | compress assgn size bound |
| `FlatClique.lean` | 38 | clique cert size bound |
| `kSAT_to_FlatClique.lean` | 63, 64 | both sides of the reduction |

I'll address them in roughly the order you should attack them: easiest first, biggest last.

---

## Section A — `FSAT_to_SAT.lean` line 268 (the `omega` bug)

The error message shows the `omega` call at line 268 receives the goal `nf < b ∨ nf ≤ nf ∧ nf < nf + 1` *with `b ≤ nf` and `v₀ < b`* in context, which is solvable. But it fails because `omega` cannot dispatch a disjunction goal — it only solves linear arithmetic on a single hypothesis context, not goals with `∨` in them.

This is the actual issue: line 268 reads `right; omega`, which *first* picks the right disjunct, then asks `omega` to prove `nf ≤ nf ∧ nf < nf + 1`. The error message confusingly shows the *original* disjunction, not the post-`right` goal. The actual issue is somewhere else.

Looking at the `simp [tseytinEquiv, varInCnf, varInClause, varInLiteral]` on line 265: this simp call probably *over*-simplifies `hu`. The `tseytinEquiv` has two clauses with three literals each, where `(true, v')` appears twice in clause 1 and `(true, v)` appears twice in clause 2. After `simp` deduplication, you only get the two distinct *variable* values, but the `rcases hu with ⟨_, rfl⟩ | ⟨_, rfl⟩` pattern then matches against an even-flatter form than expected.

**The robust fix is to avoid `simp` flattening entirely and case on each literal explicitly.** Replace the whole `cnf_varsIn` block (lines 263–268) with:

```lean
· -- cnf_varsIn
  intro u hu
  obtain ⟨C, hC, l, hl, b', heq⟩ := hu
  simp only [tseytinEquiv, List.mem_cons, List.mem_singleton,
             List.mem_nil_iff, or_false] at hC
  rcases hC with rfl | rfl
  all_goals {
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl | rfl <;>
      (simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl⟩ := heq)
  }
  -- Now we have 6 goals: 2 clauses × 3 literals each
  · exact Or.inl hv_lt                            -- clause 1, literal 1: var = v₀
  · right; exact ⟨le_refl _, Nat.lt_succ_self _⟩  -- clause 1, literal 2: var = nf
  · right; exact ⟨le_refl _, Nat.lt_succ_self _⟩  -- clause 1, literal 3: var = nf
  · right; exact ⟨le_refl _, Nat.lt_succ_self _⟩  -- clause 2, literal 1: var = nf
  · exact Or.inl hv_lt                            -- clause 2, literal 2: var = v₀
  · exact Or.inl hv_lt                            -- clause 2, literal 3: var = v₀
```

If the goal count is different (perhaps `simp` already deduplicates duplicate literal positions), reduce the trailing list of `·` to match. Whichever order Lean produces them in, *each* goal is one of those two patterns.

**Quick alternative: a sledgehammer.** Replace lines 263–268 with:

```lean
· intro u hu
  obtain ⟨C, hC, l, hl, b', heq⟩ := hu
  simp only [tseytinEquiv] at hC
  rcases hC with rfl | rfl <;>
    (simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false,
                Prod.mk.injEq] at hl
     rcases hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
       first
       | (exact Or.inl hv_lt)
       | (right; exact ⟨le_refl _, Nat.lt_succ_self _⟩)
       | (subst heq; first | exact Or.inl hv_lt
                          | (right; exact ⟨le_refl _, Nat.lt_succ_self _⟩)))
```

The `first | ... | ... | ...` lets Lean pick whichever closes the goal. This is more brittle but shorter.

**Why this matters now.** Until line 268 compiles, Lean reports the error there and skips the remaining `sorry`s. So fix this one *first* — the others may show clearer errors once the file gets past it.

---

## Section B — The "ext" sorry for `fvar` (line 270)

This is the heart of the inductive invariant. The ext clause says:

> For every assignment `a` with vars only in `[0, b)`, there exists `a'` with vars only in `[nf, nf+1)` such that `a' ++ a` satisfies `tseytinEquiv v₀ nf`.

The mathematical content: `tseytinEquiv v₀ nf` says "var nf ↔ var v₀". So we need to make `nf`'s value match `v₀`'s value in `a`. Since `v₀ < b ≤ nf`, the value `evalVar a v₀` is determined by `a` alone (no influence from `a'`), and we can independently set `nf`'s value via `a'`.

**Construction:** if `evalVar a v₀ = true`, take `a' = [nf]`. Otherwise, `a' = []`.

```lean
· -- ext for fvar
  intro a ha
  by_cases hv₀ : evalVar a v₀ = true
  · refine ⟨[nf], ?_, ?_⟩
    · -- a' = [nf] has vars only in [nf, nf+1)
      intro v hv
      simp only [List.mem_singleton] at hv
      subst hv
      exact ⟨le_refl _, Nat.lt_succ_self _⟩
    · -- [nf] ++ a satisfies tseytinEquiv v₀ nf
      rw [tseytinEquiv_sat]
      have h1 : evalVar ([nf] ++ a) nf = true := by
        simp [evalVar]
      -- evalVar ([nf] ++ a) v₀ = evalVar a v₀ = true
      have h2 : evalVar ([nf] ++ a) v₀ = evalVar a v₀ := by
        apply evalVar_append_fresh [nf] a v₀ nf
        · intro w hw
          simp only [List.mem_singleton] at hw; subst hw; exact le_refl _
        · exact hv_lt.trans_le hnf
      rw [h2, h1, hv₀]
  · refine ⟨[], ?_, ?_⟩
    · intro v hv; simp at hv
    · -- [] ++ a satisfies tseytinEquiv v₀ nf
      simp only [List.nil_append]
      rw [tseytinEquiv_sat]
      have h1 : evalVar a nf = false := by
        -- nf is outside [0, b), so a (which has vars in [0, b)) doesn't contain nf
        simp only [evalVar]
        rw [if_neg]
        intro hmem
        have := ha nf hmem
        omega
      simp [Bool.not_eq_true.mp hv₀, h1]
```

**Three things to verify** in your codebase:

- The application of `evalVar_append_fresh` requires `b ≤ n` for vars in `a'`, and `v₀ < b`. The signature in your file (line 209) is `(a' a : assgn) (v b : Nat) (ha' : ... fun n => b ≤ n) (hv : v < b)`. So `evalVar_append_fresh [nf] a v₀ nf` (with `b := nf`) needs `[nf]` to have vars `≥ nf` (true) and `v₀ < nf` (true since `v₀ < b ≤ nf`).
- `evalVar a' v` for `a' : List Nat` is defined as `if v ∈ a' then true else false` (look at `Definitions.lean`). For `a' = [nf]`, `evalVar [nf] nf = true` because `nf ∈ [nf]`.
- The fact that `ha : assgn_varsIn (fun n => n < b) a` gives `n ∈ a → n < b`, so `nf ∉ a` (since `b ≤ nf`).

**Subtle point.** Your `evalVar_append_fresh` (line 209) is correctly stated: prepending fresh vars (≥ b) doesn't change the evaluation of any var (< b). But in this ext proof you also need the *converse* shape: for var `nf` itself, `evalVar (a' ++ a) nf = evalVar a' nf` (because `a` doesn't contain `nf`). It's worth adding a small dual lemma:

```lean
theorem evalVar_append_old (a' a : assgn) (v b : Nat)
    (ha : assgn_varsIn (fun n => n < b) a) (hv : b ≤ v) :
    evalVar (a' ++ a) v = evalVar a' v := by
  simp only [evalVar, List.mem_append]
  have hva : v ∉ a := fun hmem => absurd (ha v hmem) (by omega)
  by_cases h : v ∈ a' <;> simp [h, hva]
```

Add this once near `evalVar_append_fresh` and you can use it cleanly throughout.

**Note on `tseytinEquiv_sat`.** Looking at line 127: it gives `satisfiesCnf a (tseytinEquiv v v') ↔ (evalVar a v = true ↔ evalVar a v' = true)`. So you need *both* sides to match. After substituting `h2` (which makes the v₀ side `evalVar a v₀ = true`), you have `(evalVar a v₀ = true ↔ evalVar ([nf] ++ a) nf = true)`. With `hv₀ : evalVar a v₀ = true` and `h1 : evalVar ([nf] ++ a) nf = true`, this becomes `(true ↔ true)`, which is `True`.

In the `else` branch: `evalVar a v₀ = false` (from `hv₀`) and `evalVar ([] ++ a) nf = evalVar a nf = false` (since `a` has no vars ≥ b ≥ nf). Both sides false ⇒ iff holds.

**One last gotcha.** The `evalVar` definition might use `decide` rather than direct membership; double-check by viewing `Definitions.lean` around `def evalVar`:

```lean
def evalVar (a : assgn) (v : var) : Bool :=
  if v ∈ a then true else false
```

If it uses `Decidable` instances, the `simp [evalVar]` may not reduce cleanly — switch to explicit `unfold evalVar; rw [if_pos ...]` patterns.

---

## Section C — The "cnf_varsIn" sorries for `fand` and `fneg` (lines 292, 332)

These follow directly from `cnf_varsIn_app` and the inductive hypotheses. The pattern: `N₁ ++ N₂ ++ tseytinAnd ...` has vars in the union of the var-sets of each piece, and we need to show the union is contained in `[0, b) ∪ [nf, nf'+1)`.

For **`fand`** (line 292):

```lean
· -- cnf_varsIn for fand: N₁ ++ N₂ ++ tseytinAnd nf₂ rv₁ rv₂
  -- vars of N₁ are in [0, b) ∪ [nf, nf₁)
  -- vars of N₂ are in [0, b) ∪ [nf₁, nf₂)
  -- vars of tseytinAnd nf₂ rv₁ rv₂ are {nf₂, rv₁, rv₂}, all in [0, b) ∪ [nf, nf₂+1)
  rw [cnf_varsIn_app]
  refine ⟨?_, ?_⟩
  rw [cnf_varsIn_app]
  refine ⟨?_, ?_, ?_⟩
  · -- vars of N₁ are in [0, b) ∨ nf ≤ n < nf₂+1
    intro v hv
    have := repr₁.1 v hv  -- v < b ∨ nf ≤ v < (tseytin' nf f₁).2.2 = nf₁
    rcases this with h | ⟨h₁, h₂⟩
    · exact Or.inl h
    · right; refine ⟨h₁, ?_⟩; linarith [tseytin'_nf_mono _ f₂]
  · -- vars of N₂ are in [0, b) ∨ nf ≤ n < nf₂+1
    intro v hv
    have := repr₂.1 v hv  -- v < b ∨ nf₁ ≤ v < nf₂
    rcases this with h | ⟨h₁, h₂⟩
    · exact Or.inl h
    · right; refine ⟨?_, ?_⟩
      · linarith [mono₁]  -- nf ≤ nf₁ ≤ v
      · omega
  · -- vars of tseytinAnd nf₂ rv₁ rv₂ are {nf₂, rv₁, rv₂}
    intro v hv
    obtain ⟨C, hC, l, hl, b', heq⟩ := hv
    simp only [tseytinAnd, List.mem_cons, List.mem_singleton,
               List.mem_nil_iff, or_false] at hC
    -- C is one of three clauses
    -- Each clause's literals come from {nf₂, rv₁, rv₂}
    -- The conclusion is: each of these is in [0, b) ∪ [nf, nf₂+1)
    have h_rv₁ : (tseytin' nf f₁).1 < (tseytin' nf f₁).2.2 := hrv₁_hi
    have h_rv₁_lo : nf ≤ (tseytin' nf f₁).1 := hrv₁_lo
    have h_rv₂ : (tseytin' (tseytin' nf f₁).2.2 f₂).1 < (tseytin' (tseytin' nf f₁).2.2 f₂).2.2 := hrv₂_hi
    have h_rv₂_lo : (tseytin' nf f₁).2.2 ≤ (tseytin' (tseytin' nf f₁).2.2 f₂).1 := hrv₂_lo
    rcases hC with rfl | rfl | rfl <;>
      (simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false,
                  Prod.mk.injEq] at hl
       rcases hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
         (subst heq; right
          first
          | exact ⟨h_rv₁_lo, by linarith⟩
          | exact ⟨by linarith [mono₁, h_rv₂_lo], by linarith⟩
          | exact ⟨by linarith [mono₁, tseytin'_nf_mono _ f₂], by omega)))
```

This is mechanical but long. **You may want to factor out `tseytinAnd_varsIn`:**

```lean
private theorem tseytinAnd_varsIn (v v₁ v₂ : var) (p : Nat → Prop)
    (hv : p v) (hv₁ : p v₁) (hv₂ : p v₂) :
    cnf_varsIn p (tseytinAnd v v₁ v₂) := by
  intro u hu
  obtain ⟨C, hC, l, hl, b', heq⟩ := hu
  simp only [tseytinAnd, List.mem_cons, List.mem_singleton,
             List.mem_nil_iff, or_false] at hC hl
  rcases hC with rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl <;>
      (simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl⟩ := heq) <;>
      assumption
```

Then the `fand` cnf_varsIn becomes:

```lean
rw [cnf_varsIn_app, cnf_varsIn_app]
refine ⟨⟨?_, ?_⟩, ?_⟩
· -- repr₁ via monotonicity
  apply cnf_varsIn_monotonic _ _ _ ?_ repr₁.1
  intro n h; rcases h with h | ⟨hl, hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨hl, by linarith [tseytin'_nf_mono _ f₂]⟩
· -- repr₂ via monotonicity
  apply cnf_varsIn_monotonic _ _ _ ?_ repr₂.1
  intro n h; rcases h with h | ⟨hl, hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨by linarith [mono₁], by omega⟩
· -- tseytinAnd via the helper
  apply tseytinAnd_varsIn
  · exact Or.inr ⟨by linarith [mono₁, tseytin'_nf_mono _ f₂], Nat.lt_succ_self _⟩
  · exact Or.inr ⟨hrv₁_lo, by linarith [tseytin'_nf_mono _ f₂]⟩
  · exact Or.inr ⟨by linarith [mono₁, hrv₂_lo], by omega⟩
```

The factored version is **much** more readable and you'll thank yourself later.

For **`fneg`** (line 332), the structure is parallel but simpler — just one append and a `tseytinNot`:

```lean
private theorem tseytinNot_varsIn (v v' : var) (p : Nat → Prop)
    (hv : p v) (hv' : p v') :
    cnf_varsIn p (tseytinNot v v') := by
  intro u hu
  obtain ⟨C, hC, l, hl, b', heq⟩ := hu
  simp only [tseytinNot, List.mem_cons, List.mem_singleton,
             List.mem_nil_iff, or_false] at hC hl
  rcases hC with rfl | rfl <;>
    rcases hl with rfl | rfl | rfl <;>
      (simp only [Prod.mk.injEq] at heq; obtain ⟨_, rfl⟩ := heq) <;>
      assumption

-- in fneg case:
· rw [cnf_varsIn_app]
  refine ⟨?_, ?_⟩
  · apply cnf_varsIn_monotonic _ _ _ ?_ repr.1
    intro n h; rcases h with h | ⟨hl, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨hl, by omega⟩
  · apply tseytinNot_varsIn
    · exact Or.inr ⟨by linarith [mono], Nat.lt_succ_self _⟩
    · exact Or.inr ⟨hrv_lo, by omega⟩
```

---

## Section D — The "ext" sorries for `fand` and `fneg` (lines 295, 335)

This is conceptually the trickiest part. The ext clause produces an extension `a'` of the input assignment `a`. For composed cases, we need to *compose extensions*.

### Strategy for `fand`

We need to construct `a' ⊆ [nf, nf₂+1)` such that `a' ++ a` satisfies `N₁ ++ N₂ ++ tseytinAnd nf₂ rv₁ rv₂`.

The plan:
1. Apply `repr₁`'s ext to `a`. Get `a₁'` with vars in `[nf, nf₁)` such that `a₁' ++ a ⊨ N₁`.
2. Apply `repr₂`'s ext to `a₁' ++ a` (which has vars in `[0, nf₁) ⊆ [0, b ∨ in nf-range up to nf₁)`). But careful: `repr₂` requires the input assignment to have vars in `[0, b₂)` where `b₂` is the *new* base for the second invariant. **`b₂ = (tseytin' nf f₁).2.2 = nf₁`**. So `repr₂.1` (the cnf_varsIn part) talks about vars in `[0, b₂) ∪ [nf₁, nf₂)`. And `repr₂.4` (the ext part) requires *input* assgns to have vars in `[0, b₂) = [0, nf₁)`.

   So when we feed `a₁' ++ a` to `repr₂.4`, we need `a₁' ++ a` to have vars in `[0, nf₁)`. Both pieces qualify: `a` has vars in `[0, b) ⊆ [0, nf₁)` and `a₁'` has vars in `[nf, nf₁) ⊆ [0, nf₁)`. ✓

3. Apply repr₂'s ext to `a₁' ++ a`. Get `a₂'` with vars in `[nf₁, nf₂)` such that `a₂' ++ (a₁' ++ a) ⊨ N₂`.
4. Define the value of `nf₂`: it should equal `evalVar (a₁' ++ a) rv₁ ∧ evalVar (a₂' ++ a₁' ++ a) rv₂`. Since both sub-CNFs are satisfied, by `repr₁`'s and `repr₂`'s spec clauses, this matches `evalFormula (a₁' ++ a) f₁ ∧ evalFormula (a₂' ++ a₁' ++ a) f₂` = `evalFormula a (f₁ ∧ f₂)` (using append-fresh and `a` ⊆ b).
5. So set `a' := (if (the conjunction) then [nf₂] else []) ++ a₂' ++ a₁'`.

### Concrete code for `fand` ext

```lean
· -- ext for fand
  intro a ha
  -- Step 1: extend by a₁' for N₁
  obtain ⟨a₁', ha₁'_vars, ha₁'_sat⟩ :=
    repr₁.2.2.2.1 a ha  -- (4th component of conjunction in repr₁)

  -- Step 2: a₁' ++ a has vars in [0, nf₁)
  have h_join1_vars : assgn_varsIn (fun n => n < (tseytin' nf f₁).2.2) (a₁' ++ a) := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact (ha₁'_vars v h).2
    · linarith [ha v h, hnf, mono₁]

  -- Step 3: apply repr₂'s ext
  obtain ⟨a₂', ha₂'_vars, ha₂'_sat⟩ :=
    repr₂.2.2.2.1 (a₁' ++ a) h_join1_vars

  -- Step 4: compute the truth value at the new representative variable nf₂
  set rv₁ := (tseytin' nf f₁).1
  set rv₂ := (tseytin' (tseytin' nf f₁).2.2 f₂).1
  set nf₂ := (tseytin' (tseytin' nf f₁).2.2 f₂).2.2
  -- The value is: rv₁ true AND rv₂ true
  have hrv₁_val : evalVar (a₂' ++ a₁' ++ a) rv₁ = evalVar (a₁' ++ a) rv₁ := by
    -- a₂' has vars in [nf₁, nf₂), rv₁ < nf₁, so a₂' doesn't affect rv₁
    rw [List.append_assoc]
    apply evalVar_append_fresh a₂' (a₁' ++ a) rv₁ (tseytin' nf f₁).2.2
    · intro w hw; exact (ha₂'_vars w hw).1
    · exact hrv₁_hi  -- rv₁ < nf₁

  by_cases hcond : evalVar (a₁' ++ a) rv₁ = true ∧ evalVar (a₂' ++ a₁' ++ a) rv₂ = true
  · -- Case: both representatives are true
    refine ⟨[nf₂] ++ a₂' ++ a₁', ?_, ?_⟩
    · -- a' has vars in [nf, nf₂ + 1)
      intro v hv
      rcases List.mem_append.mp hv with h12 | h1
      · rcases List.mem_append.mp h12 with h_nf | h2
        · simp only [List.mem_singleton] at h_nf; subst h_nf
          exact ⟨by linarith [mono₁, tseytin'_nf_mono _ f₂], Nat.lt_succ_self _⟩
        · have := ha₂'_vars v h2
          exact ⟨by linarith [mono₁], by omega⟩
      · have := ha₁'_vars v h1
        exact ⟨this.1, by linarith [tseytin'_nf_mono _ f₂]⟩
    · -- a' ++ a satisfies N₁ ++ N₂ ++ tseytinAnd
      rw [satisfiesCnf, ← evalCnf_clause_iff]
      have heq : ([nf₂] ++ a₂' ++ a₁') ++ a = [nf₂] ++ (a₂' ++ (a₁' ++ a)) := by
        simp [List.append_assoc]
      rw [heq]
      intro C hC
      simp only [List.mem_append] at hC
      -- This case-split needs careful handling; expand below
      sorry
  · -- Case: one of them is false
    -- Set nf₂'s value to false (i.e. a' = a₂' ++ a₁', no [nf₂] prepended)
    refine ⟨a₂' ++ a₁', ?_, ?_⟩
    · -- vars in [nf, nf₂ + 1)
      sorry
    · sorry
```

I've left the inner "satisfies CNF" calculation as `sorry` because it's tedious bookkeeping. The full version requires:

- For each clause of `N₁`: it's already satisfied by `a₁' ++ a`; prepending `[nf₂] ++ a₂'` doesn't break it because `N₁`'s vars are in `[0, b) ∪ [nf, nf₁)`, all `< nf₁`, so the prepended pieces (in `[nf₁, nf₂+1)`) don't affect them. Use `evalVar_append_fresh` / `evalClause_append_fresh` / `evalCnf_append_fresh`.
- For each clause of `N₂`: already satisfied by `a₂' ++ (a₁' ++ a)`; prepending `[nf₂]` doesn't affect because `N₂`'s vars are in `[0, nf₁) ∪ [nf₁, nf₂)`, all `< nf₂`.
- For the three clauses of `tseytinAnd`: use `tseytinAnd_sat` to verify the iff matches the chosen `nf₂` value.

**Suggested helper to add early:**

```lean
theorem evalCnf_append_fresh (a' a : assgn) (b : Nat) (N : cnf)
    (ha' : assgn_varsIn (fun n => b ≤ n) a') (hN : cnf_varsIn (fun n => n < b) N) :
    evalCnf (a' ++ a) N = evalCnf a N := by
  rw [← evalCnf_clause_iff, ← evalCnf_clause_iff]
  apply forall₂_congr
  intro C
  apply imp_congr_right
  intro hC
  -- evalClause (a' ++ a) C = evalClause a C
  rw [evalClause_literal_iff, evalClause_literal_iff]
  apply exists_congr
  intro l
  apply and_congr_right
  intro hl
  rcases l with ⟨b', v⟩
  simp only [evalLiteral]
  rw [evalVar_append_fresh a' a v b ha']
  · -- v < b because hN says all vars in N (including this one) are < b
    exact hN v ⟨C, hC, ⟨b', v⟩, hl, b', rfl⟩
```

Or — even better — prove the more general:

```lean
theorem satisfiesCnf_append_fresh (a' a : assgn) (b : Nat) (N : cnf)
    (ha' : assgn_varsIn (fun n => b ≤ n) a') (hN : cnf_varsIn (fun n => n < b) N) :
    satisfiesCnf (a' ++ a) N ↔ satisfiesCnf a N
```

And use it twice in the inner case-split.

### Strategy for `fneg`

Simpler: only one inner CNF. The plan:

1. Apply `repr.4` (ext) to `a` to get `a'_inner` with `a'_inner ++ a ⊨ N`.
2. The truth value at `nf'` should be the *negation* of `evalVar (a'_inner ++ a) rv`.
3. So set `a' := if !evalVar (a'_inner ++ a) rv then [nf'] else [] ++ a'_inner`.

Concretely:

```lean
· -- ext for fneg
  intro a ha
  obtain ⟨a'_inner, ha'_vars, ha'_sat⟩ := repr.2.2.2.1 a ha
  set rv := (tseytin' nf f).1
  set nf' := (tseytin' nf f).2.2
  by_cases hrv : evalVar (a'_inner ++ a) rv = true
  · -- inner formula evaluates true, so fneg evaluates false; nf' should be false
    refine ⟨a'_inner, ?_, ?_⟩
    · -- vars in [nf, nf'+1)
      intro v hv
      have := ha'_vars v hv
      exact ⟨this.1, by omega⟩
    · -- a'_inner ++ a ⊨ N ++ tseytinNot nf' rv
      rw [satisfiesCnf, ← evalCnf_clause_iff]
      intro C hC
      simp only [List.mem_append] at hC
      rcases hC with hC | hC
      · exact (evalCnf_clause_iff _ _).mp ha'_sat C hC
      · -- C ∈ tseytinNot nf' rv with nf' = false, rv = true
        -- tseytinNot encodes nf' ↔ ¬rv; with rv = true, nf' should be false
        rw [← satisfiesCnf, satisfiesCnf, ← evalCnf_clause_iff] at *
        -- the C is one of the two clauses of tseytinNot
        have : satisfiesCnf (a'_inner ++ a) (tseytinNot nf' rv) := by
          rw [tseytinNot_sat]
          have hnf'_false : evalVar (a'_inner ++ a) nf' = false := by
            -- nf' ∉ a'_inner (which has vars < nf') and nf' ∉ a (vars < b ≤ nf < nf')
            simp only [evalVar]
            rw [if_neg]
            intro hmem
            rcases List.mem_append.mp hmem with h | h
            · have := (ha'_vars nf' h).2; omega
            · have := ha nf' h; omega
          rw [hnf'_false, hrv]; simp
        exact (evalCnf_clause_iff _ _).mp this C hC
  · -- inner false; nf' should be true
    refine ⟨[nf'] ++ a'_inner, ?_, ?_⟩
    · intro v hv
      rcases List.mem_append.mp hv with h | h
      · simp at h; subst h; exact ⟨by linarith [tseytin'_nf_mono _ f], Nat.lt_succ_self _⟩
      · have := ha'_vars v h
        exact ⟨this.1, by omega⟩
    · sorry  -- analogous; nf' is true now, need to verify both clauses
```

The two cases are mirror images. Once you have one working, the other is mechanical.

---

## Section E — The size bound for FSAT_to_SAT (line 424)

You currently have `encodable.size (FSAT_to_SAT_tseytin f) ≤ encodable.size f ^ 2 + 200`. This is a quadratic bound, but the *actual* size of the Tseytin output is **linear** in `formula_size f`. Even so, the framework only checks `inOPoly`, not the exponent. Make life easier by **switching to a higher polynomial degree** that you can prove without sweat.

**Practical recommendation:** prove `encodable.size (FSAT_to_SAT_tseytin f) ≤ 1000 * encodable.size f ^ 2 + 1000`. The constant 1000 absorbs all bookkeeping. Then update the polynomial witness lines (430–433, 438–441) to match.

The size analysis breaks down as:

```
encodable.size (FSAT_to_SAT_tseytin f)
  = size of [(true,rv),(true,rv),(true,rv)] + size of (tseytin (eliminateOR f)).2 + ...
  ≤ const + cnf-size of N
  ≤ const + (const' * formula_size of (eliminateOR f))      -- the Tseytin linear bound
  ≤ const + (const' * 4 * formula_size f)                   -- eliminateOR_size
  ≤ const + const'' * encodable.size f
  ≤ const + const'' * encodable.size f ^ 2                  -- (since size ≥ 1)
```

But proving even this clean linear bound requires:

1. `tseytin'_size_bound : size_cnf (tseytin' nf f).2.1 ≤ 12 * formula_size f`
2. `eliminateOR_size : formula_size (eliminateOR f) ≤ 4 * formula_size f`
3. A converter: `formula_size f ≤ encodable.size f`
4. A converter: `encodable.size N ≤ size_cnf N * (max var of N + 1) + something`

That's a lot of bridging. **My recommendation:** spend an hour trying to prove a simple bound first; if it gets too tangled, fall back to the **brute polynomial-bound trick**:

```lean
theorem FSAT_to_SAT_size_le (f : formula) :
    encodable.size (FSAT_to_SAT_tseytin f) ≤ encodable.size f ^ 6 + 1000 := by
  sorry  -- Prove this with a much looser bound; n^6 is not tight but gives slack.
```

Even `n^6` is fine for the framework. The looser the bound, the less detailed the size analysis.

**Actually — the simplest path is to give up on a tight bound and use a generous degree.** Here's a sketch you can flesh out:

```lean
-- Sketch of the size bound using formula_size as a proxy
-- size of tseytin' nf f ≤ 12 * formula_size f  (each clause has 3 literals)

theorem tseytin'_size_le_formula (nf : var) (f : formula) :
    size_cnf (tseytin' nf f).2.1 ≤ 12 * formula_size f + 12 := by
  induction f generalizing nf with
  | ftrue => simp [tseytin', tseytinTrue, size_cnf, size_clause, formula_size]
  | fvar v =>
      simp [tseytin', tseytinEquiv, size_cnf, size_clause, formula_size]
  | fand f₁ f₂ ih₁ ih₂ =>
      simp only [tseytin']
      rw [size_cnf_app, size_cnf_app]
      have h1 := ih₁ nf
      have h2 := ih₂ (tseytin' nf f₁).2.2
      have h3 : size_cnf (tseytinAnd _ _ _) = 6 := by
        simp [tseytinAnd, size_cnf, size_clause]
      simp only [formula_size]
      omega
  | forr _ _ _ _ => simp [tseytin', size_cnf, formula_size]; omega
  | fneg f ih =>
      simp only [tseytin']
      rw [size_cnf_app]
      have h1 := ih nf
      have h2 : size_cnf (tseytinNot _ _) = 5 := by
        simp [tseytinNot, size_cnf, size_clause]
      simp only [formula_size]
      omega
```

(Here you'd need to introduce `formula_size` if not already present — it's the count of constructors in the formula AST.)

**Then convert to encodable.size:**

```lean
theorem formula_size_le_encodable_size (f : formula) :
    formula_size f ≤ encodable.size f := by
  induction f with
  | ftrue => simp [formula_size, encodable.size]
  | fvar v => simp [formula_size, encodable.size]; omega
  | fand f₁ f₂ ih₁ ih₂ => simp [formula_size, encodable.size]; omega
  | forr f₁ f₂ ih₁ ih₂ => simp [formula_size, encodable.size]; omega
  | fneg f ih => simp [formula_size, encodable.size]; omega

theorem cnf_encodable_size_le (N : cnf) :
    encodable.size N ≤ (size_cnf N + 1) * (size_cnf N + N.length + 100) := by
  -- Each variable in N is bounded by size_cnf N, each clause length by size_cnf N.
  sorry  -- complete this with a similar quadratic blow-up
```

**Pragmatic recommendation: defer this to a follow-up.** Mark `FSAT_to_SAT_size_le` with a clearer `sorry` comment:

```lean
theorem FSAT_to_SAT_size_le (f : formula) :
    encodable.size (FSAT_to_SAT_tseytin f) ≤ encodable.size f ^ 6 + 1000 := by
  sorry  -- Output is linear in formula_size, which is ≤ encodable.size.
         -- The n^6 polynomial gives plenty of slack for a future tight proof.
```

Update `FSAT_to_SAT_poly`'s polynomial to `fun n => n ^ 6 + 1000` and the `inOPoly` proof to use degree 6. **The chain still composes correctly** — `polyTimeComputable` only requires *some* polynomial bound.

This is honest: you've left a `sorry` for the size analysis, but the *structure* of the proof is complete. As discussed in earlier conversations, that's an acceptable interim state, especially given that the framework's output-size checking is itself only a stand-in for real polytime computability.

---

## Section F — `SAT.lean` line 206 and `FlatClique.lean` line 38 (size bounds)

These are quadratic bounds on certificate sizes. Same advice as Section E: prove a **looser** bound that's easy.

### `compressAssignment_size_bound` (SAT.lean line 206)

Current statement:
```lean
encodable.size (compressAssignment a N) ≤ encodable.size N ^ 2 + 1
```

The math: `compressAssignment a N` is a sublist of `varsOfCnf N` (with no duplicates). So:

- `|compressAssignment a N| ≤ |varsOfCnf N|`
- Each variable in `compressAssignment a N` is some `v` from `varsOfCnf N`, with `v ≤ encodable.size N`
- `encodable.size [v₁, ..., v_k] = (v₁+1) + (v₂+1) + ... + (v_k+1) ≤ k * (max_v + 1) ≤ |varsOfCnf N| * encodable.size N`

The key bound to prove: `|varsOfCnf N| ≤ encodable.size N` (since each variable appears in some literal of N, and each literal contributes ≥ 1 to size).

```lean
theorem varsOfCnf_length_le (N : cnf) :
    (varsOfCnf N).length ≤ encodable.size N := by
  -- varsOfCnf N has length = sum over clauses of (literals × 1)
  -- size of N = sum over clauses of (size of clause + 1) ≥ sum of (literals × 2)
  sorry  -- do this with two induction-on-list arguments

theorem compressAssignment_size_bound (a : assgn) (N : cnf) :
    encodable.size (compressAssignment a N) ≤ encodable.size N ^ 2 + 1 := by
  -- size of compressed = sum of (v+1) for v in compressed
  -- compressed ⊆ varsOfCnf N (deduplicated)
  -- so length ≤ |varsOfCnf N| ≤ encodable.size N
  -- and each v ≤ encodable.size N (TODO: prove varInCnf v N → v < encodable.size N)
  sorry
```

**Same recommendation: switch to a higher-degree bound and defer the analysis:**

```lean
theorem compressAssignment_size_bound (a : assgn) (N : cnf) :
    encodable.size (compressAssignment a N) ≤ encodable.size N ^ 4 + 100 := by
  sorry  -- length and max-var of varsOfCnf N are each ≤ size N
```

### `clique_size_bound` (FlatClique.lean line 38)

Current statement:
```lean
encodable.size l ≤ encodable.size Gk ^ 2 + 1
```

The math: a clique `l` for graph `(V, E)` of size `k` has all elements `< V`, with `V = G.1 ≤ encodable.size G ≤ encodable.size Gk`. The list `l` has length `k`, and `k = (Gk.2)`, so `k ≤ encodable.size Gk`. So:

```
encodable.size l = Σ (v+1) ≤ |l| * (V + 1) ≤ encodable.size Gk * (encodable.size Gk + 1)
```

Same advice: **defer with looser bound:**

```lean
theorem clique_size_bound (Gk : fgraph × Nat) (l : List fvertex)
    (hl : cliqueRel Gk l) :
    encodable.size l ≤ encodable.size Gk ^ 4 + 100 := by
  sorry
```

Why `^4`? Because `(size Gk)^2` is the natural bound but proving the `+1`s is fiddly; `^4` gives extra slack. Update the corresponding `polyCertRel` `bound` to match (`fun n => n^4 + 100`).

---

## Section G — `kSAT_to_FlatClique.lean` (the big one)

This is the largest remaining piece. Let me lay out the math and proof structure carefully.

### The instance, restated

You have:

```lean
def kSAT_to_FlatClique_instance (N : cnf) : fgraph × Nat :=
  (((cliqueVertices N).length, cliqueEdges N), N.length)
```

So:
- **Vertices:** one per (clause-index, literal-index) pair, encoded via `encodePosition`.
- **Edges:** pairs `(p, q)` of positions where the clauses differ AND the literals are not negations of each other.
- **Clique size:** `N.length` (number of clauses).

**Math claim:** `kSAT k N ↔ FlatClique (kSAT_to_FlatClique_instance N)`.

But there's a problem: `kSAT k N` requires `kCNF k N`, which the reduction ignores. So the equivalence doesn't hold — if `N` is not `kCNF k`, `kSAT k N` is false but `FlatClique` could still be true. **Same fix as `kSAT_to_SAT`: gate the reduction.**

### Fix: gate the reduction

```lean
def trivialNoFlatClique : fgraph × Nat := ((0, []), 1)

theorem trivialNoFlatClique_unsat : ¬ FlatClique trivialNoFlatClique := by
  rintro ⟨l, _, ⟨_, hnodup, _⟩, hlen⟩
  -- l has length 1, so l = [v] for some v
  -- l ⊆ [0, 0) is impossible
  match l, hlen with
  | [], h => simp at h
  | v :: _, _ =>
      -- v < 0, contradiction
      have hwf := ‹fgraph_wf trivialNoFlatClique.1›
      sorry  -- prove vertex must be < 0; impossible

def kSAT_to_FlatClique_real (k : Nat) (N : cnf) : fgraph × Nat :=
  if 0 < k ∧ kCNF k N then kSAT_to_FlatClique_instance N
  else trivialNoFlatClique
```

(Verify what `fgraph_wf` and `list_ofFlatType 0` actually entail — if `list_ofFlatType 0 [v]` requires `v < 0`, that's impossible.)

### Forward direction (kSAT → FlatClique)

Given `kSAT k N`, i.e., `0 < k`, `kCNF k N`, `SAT N`. Get `a` with `satisfiesCnf a N`. For each clause `C ∈ N`, pick the first literal `l ∈ C` with `evalLiteral a l = true` (such `l` exists because `evalClause a C = true`). Encode the position as a vertex. The resulting list:

- Has length `N.length` (one vertex per clause). ✓
- All vertices encode valid positions, so `< (cliqueVertices N).length`. ✓
- Different clauses → different first-coordinates → different positions → different encoded vertices (Nodup). ✓
- Pairwise: any two picked literals satisfy the same assignment, so they can't be negations of each other. ✓

```lean
def pickPositionForClause (a : assgn) (C : clause) : Option Nat :=
  C.findIdx? (fun l => evalLiteral a l)

def positionClique (a : assgn) (N : cnf) : List (Nat × Nat) :=
  (List.range N.length).filterMap (fun ci =>
    match nthClause N ci with
    | none => none
    | some C => match pickPositionForClause a C with
                | none => none
                | some li => some (ci, li))

theorem positionClique_correct (a : assgn) (N : cnf) (h : satisfiesCnf a N) :
    (positionClique a N).length = N.length := by
  -- For each clause, there's a satisfying literal, so pickPositionForClause returns some
  sorry
```

Then build the clique:

```lean
def cliqueFromAssgn (a : assgn) (N : cnf) : List Nat :=
  (positionClique a N).map (encodePosition N)
```

Prove (1) length, (2) `list_ofFlatType`, (3) Nodup, (4) pairwise edge condition.

### Backward direction (FlatClique → SAT)

Given a clique `l` of size `N.length` in the constructed graph. Decode each vertex back to a position. The clique condition forces:
- All positions are in different clauses (because edges require different first coords, and the clique is `Nodup`).
- |clique| = |N| → exactly one position per clause (pigeonhole).
- No two literals at chosen positions are negations.

Build an assignment `a`: for each chosen position `(ci, li)` with literal `(b, v)`, set `a v = b`. Consistency: if two positions have literals `(b₁, v)` and `(b₂, v)` with the same variable, `b₁ = b₂` (else they'd be negations).

```lean
def decodePosition (N : cnf) (n : Nat) : Nat × Nat :=
  (n / positionBase N, n % positionBase N)

def assgnFromClique (N : cnf) (l : List Nat) : assgn :=
  l.filterMap (fun n =>
    let p := decodePosition N n
    match literalAt N p.1 p.2 with
    | some (true, v) => some v
    | _ => none)
```

The proof that `assgnFromClique N l ⊨ N` requires the no-negations property of cliques. Each clause `C` has *some* position `p` in the clique (pigeonhole), and the literal at `p` evaluates to true under `assgnFromClique N l` (because it's either `(true, v)` and we added `v`, or `(false, v)` and we didn't add `v` — and we didn't add `v` because no other clique-literal is `(true, v)`, since that would be a negation).

### Proof skeleton for the full reduction

```lean
theorem kSAT_to_FlatClique_correct (k : Nat) (N : cnf) :
    kSAT k N ↔ FlatClique (kSAT_to_FlatClique_real k N) := by
  unfold kSAT_to_FlatClique_real
  split_ifs with h
  · -- Both 0 < k and kCNF k N hold
    constructor
    · -- forward: kSAT → FlatClique
      rintro ⟨_, _, ha⟩
      sorry  -- Build positionClique, prove all four properties
    · -- backward: FlatClique → kSAT
      rintro ⟨l, hwf, hclq, hlen⟩
      refine ⟨h.1, h.2, ?_⟩
      sorry  -- Build assgnFromClique, prove satisfaction
  · -- Either k = 0 or N is not a kCNF: both sides false
    constructor
    · rintro ⟨hk, hkc, _⟩; exact absurd ⟨hk, hkc⟩ h
    · intro hfc; exact absurd hfc trivialNoFlatClique_unsat

theorem kSAT_to_FlatClique_poly (k : Nat) : kSAT k ⪯p FlatClique := by
  refine ⟨⟨kSAT_to_FlatClique_real k, ?_, kSAT_to_FlatClique_correct k⟩⟩
  -- Output size: bounded by |N|^2 (vertices) + |N|^4 (edges) ≤ encodable.size N ^ 6
  refine ⟨⟨fun n => n ^ 6 + 1000, ?_, ?_, ?_⟩⟩
  · exact ⟨6, ⟨2, 1000, by intro n hn; nlinarith [Nat.one_le_pow 6 n (by omega)]⟩⟩
  · intro a b h; nlinarith [Nat.pow_le_pow_left h 6]
  · intro N
    unfold kSAT_to_FlatClique_real
    split_ifs with h
    · sorry  -- Size of kSAT_to_FlatClique_instance N ≤ size N ^ 6 + 1000
    · -- trivialNoFlatClique has constant size
      simp [trivialNoFlatClique]
      sorry  -- compute and bound by 1000
```

**Realistic estimate.** Even with the gating fix, this section will be 200-500 lines of tedious bookkeeping. The forward direction is constructive and relatively clean. The backward direction (with pigeonhole) is genuinely harder.

**Pragmatic shortcut:** if you can get the *forward* direction proved cleanly, you have *one half* of the equivalence. The full bidirectional proof can be a `sorry` placeholder that you mark for completion in a follow-up. Just be aware: until both directions are proved, `kSAT_to_FlatClique_poly` carries a `sorry` and `FlatClique_in_NP` becomes the only honest part of FlatClique's NP-completeness.

---

## Section H — Recommended order of attack

For maximum momentum:

**Day 1: get FSAT_to_SAT.lean to compile.**
1. Fix line 268 (Section A). Should compile in 15 minutes.
2. Add helpers: `evalVar_append_old`, `tseytinAnd_varsIn`, `tseytinNot_varsIn`, `satisfiesCnf_append_fresh` (Sections B, C).
3. Close lines 270, 292, 332 (`fvar` ext, `fand` cnf_varsIn, `fneg` cnf_varsIn). 2-3 hours.

**Day 2-3: close the `fand` and `fneg` ext sorries (Section D).** This is the hard part. Allow yourself to use intermediate `sorry`s for the inner CNF-satisfaction calculations and progressively close them. Test the `fand` case first; once it works, `fneg` is easier.

**Day 4: declare FSAT_to_SAT.lean done — possibly with a `sorry` only for size (Section E).** Switch the polynomial degree to `n^6` to reduce pressure. Don't push for tight bounds.

**Day 5: do the SAT.lean and FlatClique.lean size sorries (Section F).** Quick if you accept generous bounds.

**Days 6+ : kSAT_to_FlatClique.lean (Section G).** This is its own sub-project. Plan a week minimum.

---

## Section I — Specific gotchas you may hit

### Issue 1: `evalVar` definition

I cited `evalVar a v = if v ∈ a then true else false` but the actual definition in your code may be different. Check `Definitions.lean` for the canonical form. If it uses `decide`, your `simp [evalVar]` calls may need to be replaced by `unfold evalVar; split_ifs`.

### Issue 2: `evalVar_append_fresh` direction

Your `evalVar_append_fresh` (line 209) handles "vars `< b` are unaffected by prepending vars `≥ b`". You also need the dual: "vars `≥ b` are determined by `a'` alone". I sketched this as `evalVar_append_old`. Add it early.

### Issue 3: `tseytin'_kCNF3` goal in `fand` step

Your tseytin'_kCNF3 (line 181) currently has:
```lean
| fand f₁ f₂ ih₁ ih₂ =>
    cases hor with | fand h₁ h₂ =>
    simp only [tseytin', ← List.append_assoc]
```
After `simp only [tseytin', ← List.append_assoc]`, you should be at a goal of `kCNF 3 (N₁ ++ N₂ ++ tseytinAnd ...)` form. If `simp` leaves the let-binding around, use `show kCNF 3 _` to force unfolding. The line 195 follows this pattern correctly.

### Issue 4: `let`-binding obstacles

Lean's `let` inside `def tseytin'` produces complicated goals. After matching `simp only [tseytin']`, the goal often contains `let`-binders like `let (rv₁, N₁, nf₁) := tseytin' nfVar f₁ in ...`. You may need `simp only [Prod.mk.eta]` or `change ...` to massage these.

### Issue 5: `formula_varsIn` vs. `varInFormula`

The codebase uses both. `formula_varsIn p f := ∀ v, varInFormula v f → p v`. Make sure when you destructure `varsIn` hypotheses, you produce `varInFormula` premises and walk the induction correctly.

### Issue 6: Be careful with `Mathlib.Tactic` imports

You're importing `Mathlib.Tactic` in some files, which brings in all of Mathlib's tactics including potentially-conflicting names. If you see strange errors about `kCNF` or `cnf` resolution, try `import Mathlib.Tactic.NLinarith` instead — pulling only what you need.

### Issue 7: Don't open Classical *unless you need it*

You have `open Classical` at the top of `FSAT_to_SAT.lean` and `FlatClique.lean`. This makes every proposition decidable, which is fine but obscures the actual computational content. In particular, `if h : P then ... else ...` will use `Classical.dec` rather than a registered instance, which sometimes confuses `simp`. If you find odd `simp` failures, try removing `open Classical` and seeing if anything breaks.

### Issue 8: The `noncomputable` keyword

You marked `cliqueRelDec` as `noncomputable`. That's fine for now, but if you ever want to `decide` a cliqueRel proposition, you'll need a computable replacement. Note this with `-- TODO(step14)` and move on.

---

Good luck. Most of the conceptual hard work is behind you — what remains is mechanical engineering. Slow and steady.
