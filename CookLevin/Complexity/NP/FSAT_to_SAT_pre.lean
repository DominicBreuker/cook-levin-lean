import Complexity.NP.FSAT_to_SAT

set_option autoImplicit false

/-! # Pre-order positional Tseytin — the machine-friendly `FSAT → SAT` map

The free-line witness for the last sound-tail step `FSAT → SAT` cannot mimic
`FSAT_to_SAT_tseytin` (`FSAT_to_SAT.lean`): that map is a pair of structural
tree recursions (`eliminateOR`, then `tseytin'` with a *post-order* fresh-var
counter and *children-first* clause emission), while the machine input is the
Polish `serF` bit-stream and the DSL has only counted forward loops.

This file defines the **machine-friendly equivalent map** and proves it correct
at the Lean level (where recursion is free), per the HANDOFF design brief
("the witness need NOT reproduce `FSAT_to_SAT_tseytin` verbatim — any map `m`
with `FSAT f ↔ SAT (m f)` works for the chain"):

* **full grammar** — a `tseytinOr` gadget handles `forr` directly, so the
  `eliminateOR` pass disappears (one machine scan instead of two);
* **positional variables** — the node rooted at pre-order token index `k` of
  the Polish serialization gets the fresh variable `b + k` (`b` any bound
  `> formula_maxVar f`; the witness uses `b := (serF f).length`, which the
  machine computes with one trivial length loop — no on-machine max). Here
  `ptseytin` carries the *absolute* variable `q = b + k` directly;
* **pre-order emission** — each node's gadget clauses are emitted when its
  token is scanned (gadget first, then the children's), which is exactly the
  order a single forward scan of the stream produces.

A node's left child is the next token (variable `q + 1`); its right child
starts after the left subtree (variable `q + 1 + formula_size f₁`;
`formula_size` = token count), which the machine recovers with the Polish
arity-budget scan (design (a) of the HANDOFF brief, probed GO in
`probes/FSATPreProbe.lean`).

Everything here is parametric in the base `b`; the witness file instantiates
`b := (serF f).length` (`Reductions/FSAT_to_SAT_free.lean`). -/

namespace PreTseytin

/-! ## The OR gadget (the existing file has only true/equiv/and/not) -/

/-- Tseytin gadget for `v ↔ v₁ ∨ v₂`, in the same 3-literal clause shape as the
existing gadgets (so the whole output is a `kCNF 3`). -/
def tseytinOr (v v₁ v₂ : var) : cnf :=
  [[(false, v), (true, v₁), (true, v₂)],
   [(false, v₁), (true, v), (true, v)],
   [(false, v₂), (true, v), (true, v)]]

theorem tseytinOr_sat (a : assgn) (v v₁ v₂ : var) :
    satisfiesCnf a (tseytinOr v v₁ v₂) ↔
      (evalVar a v = true ↔ (evalVar a v₁ = true ∨ evalVar a v₂ = true)) := by
  unfold tseytinOr satisfiesCnf
  cases h₁ : evalVar a v <;> cases h₂ : evalVar a v₁ <;> cases h₃ : evalVar a v₂ <;>
    simp [evalCnf, evalClause, evalLiteral, h₁, h₂, h₃]

theorem tseytinOr_kCNF (v v₁ v₂ : var) : kCNF 3 (tseytinOr v v₁ v₂) :=
  kCNF.cons _ _ rfl (kCNF.cons _ _ rfl (kCNF.cons _ _ rfl kCNF.nil))

/-! ## The positional transform -/

/-- Pre-order positional Tseytin. `ptseytin q f` emits the gadget clauses for
the subtree `f` whose root's representative variable is `q`; the left child's
is `q + 1`, the right child's `q + 1 + formula_size f₁` (pre-order position).
Gadget-before-children = the order a forward scan of the Polish stream emits.
The fresh block of the subtree is exactly `[q, q + formula_size f)`. -/
def ptseytin : Nat → formula → cnf
  | q, .ftrue => tseytinTrue q
  | q, .fvar v => tseytinEquiv v q
  | q, .fand f₁ f₂ =>
      tseytinAnd q (q + 1) (q + 1 + formula_size f₁) ++
        ptseytin (q + 1) f₁ ++ ptseytin (q + 1 + formula_size f₁) f₂
  | q, .forr f₁ f₂ =>
      tseytinOr q (q + 1) (q + 1 + formula_size f₁) ++
        ptseytin (q + 1) f₁ ++ ptseytin (q + 1 + formula_size f₁) f₂
  | q, .fneg f₁ => tseytinNot q (q + 1) ++ ptseytin (q + 1) f₁

/-- **The machine-friendly `FSAT → SAT` map**: the root-forcing top clause,
then the positional Tseytin clauses of the whole tree (root variable `b`).
Correct for every `b > formula_maxVar f` (`preTseytin_correct`). -/
def preTseytin (b : Nat) (f : formula) : cnf :=
  [(true, b), (true, b), (true, b)] :: ptseytin b f

/-- Every subtree occupies at least one token. -/
theorem formula_size_pos (f : formula) : 1 ≤ formula_size f := by
  cases f <;> simp [formula_size]

/-! ## The representation invariant

The positional analogue of `tseytin_formula_repr` (`FSAT_to_SAT.lean`), for the
FULL grammar. For a subtree at root variable `q ≥ b` (all original variables
`< b`):

1. the emitted clauses touch only original variables (`< b`) and the subtree's
   fresh block `[q, q + formula_size f)`;
2. any assignment over the original variables extends (by fresh-block variables
   only) to one satisfying the clauses;
3. any assignment satisfying the clauses evaluates `q` to the subtree's truth
   value. -/
theorem ptseytin_repr {b : Nat} (f : formula)
    (hvars : formula_varsIn (fun n => n < b) f) :
    ∀ q : Nat, b ≤ q →
      cnf_varsIn (fun n => n < b ∨ (q ≤ n ∧ n < q + formula_size f)) (ptseytin q f) ∧
      (∀ a, assgn_varsIn (fun n => n < b) a →
        ∃ a', assgn_varsIn (fun n => q ≤ n ∧ n < q + formula_size f) a' ∧
          satisfiesCnf (a' ++ a) (ptseytin q f)) ∧
      (∀ a, satisfiesCnf a (ptseytin q f) →
        (evalVar a q = true ↔ evalFormula a f = true)) := by
  induction f with
  | ftrue =>
      intro q hq
      simp only [ptseytin, formula_size]
      refine ⟨?_, ?_, ?_⟩
      · -- vars of tseytinTrue q: just q
        intro u hu
        obtain ⟨C, hC, l, hl, s, heq⟩ := hu
        simp only [tseytinTrue, List.mem_singleton] at hC
        subst hC
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl <;>
          (simp only [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq; right; omega)
      · -- ext: include q
        intro a _
        refine ⟨[q], ?_, ?_⟩
        · intro v hv
          simp only [List.mem_singleton] at hv; subst hv; omega
        · rw [tseytinTrue_sat]; simp [evalVar]
      · -- spec
        intro a ha
        exact ⟨fun _ => rfl, fun _ => (tseytinTrue_sat a q).mp ha⟩
  | fvar v₀ =>
      intro q hq
      have hv_lt : v₀ < b := hvars v₀ varInFormula.var
      simp only [ptseytin, formula_size]
      refine ⟨?_, ?_, ?_⟩
      · -- vars of tseytinEquiv v₀ q: v₀ and q
        intro u hu
        obtain ⟨C, hC, l, hl, s, heq⟩ := hu
        simp only [tseytinEquiv, List.mem_cons, List.not_mem_nil, or_false] at hC
        rcases hC with rfl | rfl <;>
          (simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
           rcases hl with rfl | rfl | rfl <;>
             (simp only [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq)) <;>
          first
          | exact Or.inl hv_lt
          | exact Or.inr ⟨le_refl _, by omega⟩
      · -- ext: include q iff v₀ is true
        intro a ha
        by_cases hv₀ : evalVar a v₀ = true
        · refine ⟨[q], ?_, ?_⟩
          · intro v hv
            simp only [List.mem_singleton] at hv; subst hv; omega
          · rw [tseytinEquiv_sat]
            have h_q : evalVar ([q] ++ a) q = true := by simp [evalVar]
            have h_v₀ : evalVar ([q] ++ a) v₀ = evalVar a v₀ :=
              evalVar_prepend_notmem [q] a v₀
                (by simp only [List.mem_singleton]
                    exact Nat.ne_of_lt (lt_of_lt_of_le hv_lt hq))
            rw [h_v₀, h_q, hv₀]
        · refine ⟨[], ?_, ?_⟩
          · intro v hv; simp at hv
          · simp only [List.nil_append]
            rw [tseytinEquiv_sat]
            have h_q : evalVar a q = false := by
              simp only [evalVar, decide_eq_false_iff_not]
              intro hmem
              exact absurd (ha q hmem) (by omega)
            simp [Bool.of_not_eq_true hv₀, h_q]
      · -- spec
        intro a ha
        have h := (tseytinEquiv_sat a v₀ q).mp ha
        constructor
        · intro hh; simp only [evalFormula]; exact h.mpr hh
        · intro hh; simp only [evalFormula] at hh; exact h.mp hh
  | fand f₁ f₂ ih₁ ih₂ =>
      intro q hq
      have hv₁ : formula_varsIn (fun n => n < b) f₁ :=
        fun v hv => hvars v (varInFormula.andLeft _ _ hv)
      have hv₂ : formula_varsIn (fun n => n < b) f₂ :=
        fun v hv => hvars v (varInFormula.andRight _ _ hv)
      have hs₁ := formula_size_pos f₁
      have hs₂ := formula_size_pos f₂
      obtain ⟨hcnf₁, hext₁, hspec₁⟩ := ih₁ hv₁ (q + 1) (by omega)
      obtain ⟨hcnf₂, hext₂, hspec₂⟩ := ih₂ hv₂ (q + 1 + formula_size f₁) (by omega)
      simp only [ptseytin, formula_size]
      refine ⟨?_, ?_, ?_⟩
      · -- vars: gadget ++ N₁ ++ N₂
        intro u hu
        obtain ⟨C, hC, hVar⟩ := hu
        rcases List.mem_append.mp hC with hC' | hC₂
        · rcases List.mem_append.mp hC' with hG | hC₁
          · obtain ⟨l, hl, s, heq⟩ := hVar
            simp only [tseytinAnd, List.mem_cons, List.not_mem_nil, or_false] at hG
            rcases hG with rfl | rfl | rfl <;>
              (simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
               rcases hl with rfl | rfl | rfl <;>
                 (simp only [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq;
                  right; omega))
          · rcases hcnf₁ u ⟨C, hC₁, hVar⟩ with h | ⟨h1, h2⟩
            · exact Or.inl h
            · right; omega
        · rcases hcnf₂ u ⟨C, hC₂, hVar⟩ with h | ⟨h1, h2⟩
          · exact Or.inl h
          · right; omega
      · -- ext: combine the children's extensions
        intro a ha
        obtain ⟨a₁', ha₁'v, ha₁'s⟩ := hext₁ a ha
        obtain ⟨a₂', ha₂'v, ha₂'s⟩ := hext₂ a ha
        set rv₁ := evalVar (a₁' ++ a) (q + 1) with hrv₁
        set rv₂ := evalVar (a₂' ++ a) (q + 1 + formula_size f₁) with hrv₂
        set piece : assgn := if (rv₁ && rv₂) = true then [q] else [] with hpiece
        have hpc : ∀ v, q < v → v ∉ piece := by
          intro v hv
          rw [hpiece]; split_ifs
          · simp only [List.mem_singleton]; omega
          · simp
        refine ⟨piece ++ a₂' ++ a₁', ?_, ?_⟩
        · intro v hv
          simp only [List.mem_append] at hv
          rcases hv with (hv | hv) | hv
          · rw [hpiece] at hv
            split_ifs at hv with h
            · simp only [List.mem_singleton] at hv; subst hv; omega
            · simp at hv
          · obtain ⟨h1, h2⟩ := ha₂'v v hv; omega
          · obtain ⟨h1, h2⟩ := ha₁'v v hv; omega
        · rw [show (piece ++ a₂' ++ a₁') ++ a = piece ++ (a₂' ++ (a₁' ++ a)) from by
            simp [List.append_assoc]]
          refine (satisfiesCnf_app _ _ _).mpr
            ⟨(satisfiesCnf_app _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
          · -- the gadget
            rw [tseytinAnd_sat]
            have h_rv₁ : evalVar (piece ++ (a₂' ++ (a₁' ++ a))) (q + 1) = rv₁ := by
              rw [evalVar_prepend_notmem _ _ _ (hpc _ (by omega)),
                  evalVar_prepend_notmem a₂' (a₁' ++ a) _ (by
                    intro hmem
                    exact absurd (ha₂'v _ hmem).1 (by omega))]
            have h_rv₂ : evalVar (piece ++ (a₂' ++ (a₁' ++ a)))
                (q + 1 + formula_size f₁) = rv₂ := by
              rw [evalVar_prepend_notmem _ _ _ (hpc _ (by omega)),
                  evalVar_insert_notmem a₂' a₁' a _ (by
                    intro hmem
                    exact absurd (ha₁'v _ hmem).2 (by omega))]
            have h_q : evalVar (piece ++ (a₂' ++ (a₁' ++ a))) q = (rv₁ && rv₂) := by
              by_cases hboth : (rv₁ && rv₂) = true
              · have hp : piece = [q] := by rw [hpiece, if_pos hboth]
                rw [hp, hboth]
                simp [evalVar]
              · have hp : piece = [] := by rw [hpiece, if_neg hboth]
                rw [hp, Bool.of_not_eq_true hboth]
                simp only [List.nil_append, evalVar, decide_eq_false_iff_not,
                  List.mem_append, not_or]
                refine ⟨?_, ?_, ?_⟩
                · intro hmem; exact absurd (ha₂'v _ hmem).1 (by omega)
                · intro hmem; exact absurd (ha₁'v _ hmem).1 (by omega)
                · intro hmem; exact absurd (ha _ hmem) (by omega)
            rw [h_q, h_rv₁, h_rv₂]
            simp [Bool.and_eq_true]
          · -- N₁: prepend (piece ++ a₂'), disjoint from N₁'s vars
            rw [← List.append_assoc]
            refine satisfiesCnf_prepend_notmem (piece ++ a₂') (a₁' ++ a) _ ?_ ha₁'s
            intro v hv
            simp only [List.mem_append, not_or]
            constructor
            · rw [hpiece]; split_ifs
              · simp only [List.mem_singleton]
                intro heq; subst heq
                rcases hcnf₁ _ hv with h | ⟨h1, h2⟩ <;> omega
              · simp
            · intro hmem
              rcases hcnf₁ v hv with h | ⟨h1, h2⟩
              · exact absurd (ha₂'v v hmem).1 (by omega)
              · exact absurd (ha₂'v v hmem).1 (by omega)
          · -- N₂: prepend piece, insert a₁' — both disjoint from N₂'s vars
            refine satisfiesCnf_prepend_notmem piece _ _ ?_ ?_
            · intro v hv
              rw [hpiece]; split_ifs
              · simp only [List.mem_singleton]
                intro heq; subst heq
                rcases hcnf₂ _ hv with h | ⟨h1, h2⟩ <;> omega
              · simp
            · refine satisfiesCnf_insert_notmem a₂' a₁' a _ ?_ ha₂'s
              intro v hv hmem
              rcases hcnf₂ v hv with h | ⟨h1, h2⟩
              · exact absurd (ha₁'v v hmem).1 (by omega)
              · exact absurd (ha₁'v v hmem).2 (by omega)
      · -- spec
        intro a ha
        rw [satisfiesCnf_app, satisfiesCnf_app] at ha
        obtain ⟨⟨haG, haN₁⟩, haN₂⟩ := ha
        have hG := (tseytinAnd_sat a _ _ _).mp haG
        constructor
        · intro h
          rw [evalFormula_and_iff]
          obtain ⟨h₁, h₂⟩ := hG.mp h
          exact ⟨(hspec₁ a haN₁).mp h₁, (hspec₂ a haN₂).mp h₂⟩
        · intro h
          apply hG.mpr
          rw [evalFormula_and_iff] at h
          exact ⟨(hspec₁ a haN₁).mpr h.1, (hspec₂ a haN₂).mpr h.2⟩
  | forr f₁ f₂ ih₁ ih₂ =>
      intro q hq
      have hv₁ : formula_varsIn (fun n => n < b) f₁ :=
        fun v hv => hvars v (varInFormula.orLeft _ _ hv)
      have hv₂ : formula_varsIn (fun n => n < b) f₂ :=
        fun v hv => hvars v (varInFormula.orRight _ _ hv)
      have hs₁ := formula_size_pos f₁
      have hs₂ := formula_size_pos f₂
      obtain ⟨hcnf₁, hext₁, hspec₁⟩ := ih₁ hv₁ (q + 1) (by omega)
      obtain ⟨hcnf₂, hext₂, hspec₂⟩ := ih₂ hv₂ (q + 1 + formula_size f₁) (by omega)
      simp only [ptseytin, formula_size]
      refine ⟨?_, ?_, ?_⟩
      · -- vars: gadget ++ N₁ ++ N₂
        intro u hu
        obtain ⟨C, hC, hVar⟩ := hu
        rcases List.mem_append.mp hC with hC' | hC₂
        · rcases List.mem_append.mp hC' with hG | hC₁
          · obtain ⟨l, hl, s, heq⟩ := hVar
            simp only [tseytinOr, List.mem_cons, List.not_mem_nil, or_false] at hG
            rcases hG with rfl | rfl | rfl <;>
              (simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
               rcases hl with rfl | rfl | rfl <;>
                 (simp only [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq;
                  right; omega))
          · rcases hcnf₁ u ⟨C, hC₁, hVar⟩ with h | ⟨h1, h2⟩
            · exact Or.inl h
            · right; omega
        · rcases hcnf₂ u ⟨C, hC₂, hVar⟩ with h | ⟨h1, h2⟩
          · exact Or.inl h
          · right; omega
      · -- ext: combine the children's extensions
        intro a ha
        obtain ⟨a₁', ha₁'v, ha₁'s⟩ := hext₁ a ha
        obtain ⟨a₂', ha₂'v, ha₂'s⟩ := hext₂ a ha
        set rv₁ := evalVar (a₁' ++ a) (q + 1) with hrv₁
        set rv₂ := evalVar (a₂' ++ a) (q + 1 + formula_size f₁) with hrv₂
        set piece : assgn := if (rv₁ || rv₂) = true then [q] else [] with hpiece
        have hpc : ∀ v, q < v → v ∉ piece := by
          intro v hv
          rw [hpiece]; split_ifs
          · simp only [List.mem_singleton]; omega
          · simp
        refine ⟨piece ++ a₂' ++ a₁', ?_, ?_⟩
        · intro v hv
          simp only [List.mem_append] at hv
          rcases hv with (hv | hv) | hv
          · rw [hpiece] at hv
            split_ifs at hv with h
            · simp only [List.mem_singleton] at hv; subst hv; omega
            · simp at hv
          · obtain ⟨h1, h2⟩ := ha₂'v v hv; omega
          · obtain ⟨h1, h2⟩ := ha₁'v v hv; omega
        · rw [show (piece ++ a₂' ++ a₁') ++ a = piece ++ (a₂' ++ (a₁' ++ a)) from by
            simp [List.append_assoc]]
          refine (satisfiesCnf_app _ _ _).mpr
            ⟨(satisfiesCnf_app _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
          · -- the gadget
            rw [tseytinOr_sat]
            have h_rv₁ : evalVar (piece ++ (a₂' ++ (a₁' ++ a))) (q + 1) = rv₁ := by
              rw [evalVar_prepend_notmem _ _ _ (hpc _ (by omega)),
                  evalVar_prepend_notmem a₂' (a₁' ++ a) _ (by
                    intro hmem
                    exact absurd (ha₂'v _ hmem).1 (by omega))]
            have h_rv₂ : evalVar (piece ++ (a₂' ++ (a₁' ++ a)))
                (q + 1 + formula_size f₁) = rv₂ := by
              rw [evalVar_prepend_notmem _ _ _ (hpc _ (by omega)),
                  evalVar_insert_notmem a₂' a₁' a _ (by
                    intro hmem
                    exact absurd (ha₁'v _ hmem).2 (by omega))]
            have h_q : evalVar (piece ++ (a₂' ++ (a₁' ++ a))) q = (rv₁ || rv₂) := by
              by_cases hboth : (rv₁ || rv₂) = true
              · have hp : piece = [q] := by rw [hpiece, if_pos hboth]
                rw [hp, hboth]
                simp [evalVar]
              · have hp : piece = [] := by rw [hpiece, if_neg hboth]
                rw [hp, Bool.of_not_eq_true hboth]
                simp only [List.nil_append, evalVar, decide_eq_false_iff_not,
                  List.mem_append, not_or]
                refine ⟨?_, ?_, ?_⟩
                · intro hmem; exact absurd (ha₂'v _ hmem).1 (by omega)
                · intro hmem; exact absurd (ha₁'v _ hmem).1 (by omega)
                · intro hmem; exact absurd (ha _ hmem) (by omega)
            rw [h_q, h_rv₁, h_rv₂]
            simp [Bool.or_eq_true]
          · -- N₁
            rw [← List.append_assoc]
            refine satisfiesCnf_prepend_notmem (piece ++ a₂') (a₁' ++ a) _ ?_ ha₁'s
            intro v hv
            simp only [List.mem_append, not_or]
            constructor
            · rw [hpiece]; split_ifs
              · simp only [List.mem_singleton]
                intro heq; subst heq
                rcases hcnf₁ _ hv with h | ⟨h1, h2⟩ <;> omega
              · simp
            · intro hmem
              rcases hcnf₁ v hv with h | ⟨h1, h2⟩
              · exact absurd (ha₂'v v hmem).1 (by omega)
              · exact absurd (ha₂'v v hmem).1 (by omega)
          · -- N₂
            refine satisfiesCnf_prepend_notmem piece _ _ ?_ ?_
            · intro v hv
              rw [hpiece]; split_ifs
              · simp only [List.mem_singleton]
                intro heq; subst heq
                rcases hcnf₂ _ hv with h | ⟨h1, h2⟩ <;> omega
              · simp
            · refine satisfiesCnf_insert_notmem a₂' a₁' a _ ?_ ha₂'s
              intro v hv hmem
              rcases hcnf₂ v hv with h | ⟨h1, h2⟩
              · exact absurd (ha₁'v v hmem).1 (by omega)
              · exact absurd (ha₁'v v hmem).2 (by omega)
      · -- spec
        intro a ha
        rw [satisfiesCnf_app, satisfiesCnf_app] at ha
        obtain ⟨⟨haG, haN₁⟩, haN₂⟩ := ha
        have hG := (tseytinOr_sat a _ _ _).mp haG
        constructor
        · intro h
          rw [evalFormula_or_iff]
          rcases hG.mp h with h₁ | h₂
          · exact Or.inl ((hspec₁ a haN₁).mp h₁)
          · exact Or.inr ((hspec₂ a haN₂).mp h₂)
        · intro h
          apply hG.mpr
          rw [evalFormula_or_iff] at h
          rcases h with h₁ | h₂
          · exact Or.inl ((hspec₁ a haN₁).mpr h₁)
          · exact Or.inr ((hspec₂ a haN₂).mpr h₂)
  | fneg f₁ ih =>
      intro q hq
      have hv₁ : formula_varsIn (fun n => n < b) f₁ :=
        fun v hv => hvars v (varInFormula.neg _ hv)
      have hs₁ := formula_size_pos f₁
      obtain ⟨hcnf₁, hext₁, hspec₁⟩ := ih hv₁ (q + 1) (by omega)
      simp only [ptseytin, formula_size]
      refine ⟨?_, ?_, ?_⟩
      · -- vars: gadget ++ N₁
        intro u hu
        obtain ⟨C, hC, hVar⟩ := hu
        rcases List.mem_append.mp hC with hG | hC₁
        · obtain ⟨l, hl, s, heq⟩ := hVar
          simp only [tseytinNot, List.mem_cons, List.not_mem_nil, or_false] at hG
          rcases hG with rfl | rfl <;>
            (simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
             rcases hl with rfl | rfl | rfl <;>
               (simp only [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq;
                right; omega))
        · rcases hcnf₁ u ⟨C, hC₁, hVar⟩ with h | ⟨h1, h2⟩
          · exact Or.inl h
          · right; omega
      · -- ext: include q iff the subformula is false
        intro a ha
        obtain ⟨a₁', ha₁'v, ha₁'s⟩ := hext₁ a ha
        by_cases hrv : evalVar (a₁' ++ a) (q + 1) = true
        · -- child true ⇒ q stays false
          refine ⟨a₁', ?_, ?_⟩
          · intro v hv; obtain ⟨h1, h2⟩ := ha₁'v v hv; omega
          · refine (satisfiesCnf_app _ _ _).mpr ⟨?_, ha₁'s⟩
            rw [tseytinNot_sat]
            have h_q : evalVar (a₁' ++ a) q = false := by
              simp only [evalVar, decide_eq_false_iff_not, List.mem_append, not_or]
              constructor
              · intro hmem; exact absurd (ha₁'v _ hmem).1 (by omega)
              · intro hmem; exact absurd (ha _ hmem) (by omega)
            rw [h_q, hrv]; simp
        · -- child false ⇒ include q
          refine ⟨[q] ++ a₁', ?_, ?_⟩
          · intro v hv
            rcases List.mem_append.mp hv with hv | hv
            · simp only [List.mem_singleton] at hv; subst hv; omega
            · obtain ⟨h1, h2⟩ := ha₁'v v hv; omega
          · rw [show ([q] ++ a₁') ++ a = [q] ++ (a₁' ++ a) from by
              simp [List.append_assoc]]
            refine (satisfiesCnf_app _ _ _).mpr ⟨?_, ?_⟩
            · rw [tseytinNot_sat]
              have h_q : evalVar ([q] ++ (a₁' ++ a)) q = true := by simp [evalVar]
              have h_c : evalVar ([q] ++ (a₁' ++ a)) (q + 1) =
                  evalVar (a₁' ++ a) (q + 1) :=
                evalVar_prepend_notmem [q] _ _
                  (by simp only [List.mem_singleton]; omega)
              rw [h_q, h_c, Bool.of_not_eq_true hrv]; simp
            · refine satisfiesCnf_prepend_notmem [q] (a₁' ++ a) _ ?_ ha₁'s
              intro v hv
              simp only [List.mem_singleton]
              intro heq; subst heq
              rcases hcnf₁ _ hv with h | ⟨h1, h2⟩ <;> omega
      · -- spec
        intro a ha
        rw [satisfiesCnf_app] at ha
        obtain ⟨haG, haN₁⟩ := ha
        have hG := (tseytinNot_sat a _ _).mp haG
        constructor
        · intro h
          simp only [evalFormula]
          cases hf : evalFormula a f₁
          · rfl
          · exact absurd ((hspec₁ a haN₁).mpr hf) (hG.mp h)
        · intro h
          simp only [evalFormula] at h
          apply hG.mpr
          intro hrv
          have hf : evalFormula a f₁ = true := (hspec₁ a haN₁).mp hrv
          simp [hf] at h

/-! ## The headline correctness -/

/-- **The map is correct** for every fresh-variable base `b > formula_maxVar f`
(the witness instantiates `b := (serF f).length`). -/
theorem preTseytin_correct (f : formula) (b : Nat) (hb : formula_maxVar f < b) :
    FSAT f ↔ SAT (preTseytin b f) := by
  have hvars : formula_varsIn (fun n => n < b) f := by
    intro v hv
    have := formula_maxVar_varsIn f v hv
    omega
  obtain ⟨hcnf, hext, hspec⟩ := ptseytin_repr f hvars b (le_refl b)
  simp only [preTseytin, FSAT, satisfiesFormula, SAT]
  constructor
  · rintro ⟨a, ha⟩
    set a_old := boundedAssignment b a with ha_old_def
    have ha_old : assgn_varsIn (fun n => n < b) a_old :=
      fun v hv => ((mem_boundedAssignment_iff b a v).mp hv).1
    obtain ⟨a', ha'v, ha's⟩ := hext a_old ha_old
    have heval : evalFormula (a' ++ a_old) f = true := by
      rw [evalFormula_append_fresh a' a_old b f (fun v hv => (ha'v v hv).1) hvars,
          ha_old_def, evalFormula_boundedAssignment_of_bound a f b hvars]
      exact ha
    have hq : evalVar (a' ++ a_old) b = true := (hspec _ ha's).mpr heval
    refine ⟨a' ++ a_old, ?_⟩
    rw [satisfiesCnf, evalCnf_clause_iff]
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · simp [evalClause, evalLiteral, hq]
    · exact (evalCnf_clause_iff _ _).mp ha's C hC
  · rintro ⟨a, ha⟩
    have hN : satisfiesCnf a (ptseytin b f) := by
      rw [satisfiesCnf, evalCnf_clause_iff]
      intro C hC
      exact (evalCnf_clause_iff a _).mp ha C (List.mem_cons_of_mem _ hC)
    have hb' : evalVar a b = true := by
      have hC := (evalCnf_clause_iff a _).mp ha [(true, b), (true, b), (true, b)]
        List.mem_cons_self
      simp only [evalClause, evalLiteral, List.any_cons, List.any_nil,
        Bool.or_false] at hC
      cases h : evalVar a b <;> simp_all
    exact ⟨a, (hspec a hN).mp hb'⟩

/-! ## `kCNF 3` (freebie — the output is also a 3-CNF, like the original map) -/

theorem ptseytin_kCNF3 (f : formula) : ∀ q, kCNF 3 (ptseytin q f) := by
  induction f with
  | ftrue => intro q; exact tseytinTrue_kCNF _
  | fvar v => intro q; exact tseytinEquiv_kCNF _ _
  | fand f₁ f₂ ih₁ ih₂ =>
      intro q
      simp only [ptseytin]
      exact (kCNF_app 3 _ _).mpr
        ⟨(kCNF_app 3 _ _).mpr ⟨tseytinAnd_kCNF _ _ _, ih₁ _⟩, ih₂ _⟩
  | forr f₁ f₂ ih₁ ih₂ =>
      intro q
      simp only [ptseytin]
      exact (kCNF_app 3 _ _).mpr
        ⟨(kCNF_app 3 _ _).mpr ⟨tseytinOr_kCNF _ _ _, ih₁ _⟩, ih₂ _⟩
  | fneg f₁ ih =>
      intro q
      simp only [ptseytin]
      exact (kCNF_app 3 _ _).mpr ⟨tseytinNot_kCNF _ _, ih _⟩

theorem preTseytin_kCNF3 (b : Nat) (f : formula) : kCNF 3 (preTseytin b f) :=
  kCNF.cons _ _ rfl (ptseytin_kCNF3 f b)

/-- The 3-SAT strengthening (for a possible future `kSAT 3` chain endpoint). -/
theorem preTseytin_3SAT_correct (f : formula) (b : Nat) (hb : formula_maxVar f < b) :
    FSAT f ↔ kSAT 3 (preTseytin b f) := by
  rw [preTseytin_correct f b hb]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨by omega, preTseytin_kCNF3 b f, ⟨a, ha⟩⟩
  · rintro ⟨-, -, hsat⟩; exact hsat

/-! ## Size bounds (fodder for the witness's `output_size_le`) -/

/-- Each node contributes at most 3 clauses. -/
theorem ptseytin_length_le (f : formula) :
    ∀ q, (ptseytin q f).length ≤ 3 * formula_size f := by
  induction f with
  | ftrue => intro q; simp [ptseytin, tseytinTrue, formula_size]
  | fvar v => intro q; simp [ptseytin, tseytinEquiv, formula_size]
  | fand f₁ f₂ ih₁ ih₂ =>
      intro q
      simp only [ptseytin, tseytinAnd, formula_size, List.length_append,
        List.length_cons, List.length_nil]
      have h₁ := ih₁ (q + 1)
      have h₂ := ih₂ (q + 1 + formula_size f₁)
      omega
  | forr f₁ f₂ ih₁ ih₂ =>
      intro q
      simp only [ptseytin, tseytinOr, formula_size, List.length_append,
        List.length_cons, List.length_nil]
      have h₁ := ih₁ (q + 1)
      have h₂ := ih₂ (q + 1 + formula_size f₁)
      omega
  | fneg f₁ ih =>
      intro q
      simp only [ptseytin, tseytinNot, formula_size, List.length_append,
        List.length_cons, List.length_nil]
      have h₁ := ih (q + 1)
      omega

/-- The whole output in one `encodable.size` bound, parametric in the base:
at most `3·size+1` clauses, each 3 literals over variables `< b + size`. -/
theorem preTseytin_size_le (b : Nat) (f : formula) (hb : formula_maxVar f < b) :
    encodable.size (preTseytin b f) ≤
      (3 * formula_size f + 1) * (3 * (b + formula_size f + 1) + 4) := by
  have hvars : formula_varsIn (fun n => n < b) f := by
    intro v hv
    have := formula_maxVar_varsIn f v hv
    omega
  obtain ⟨hcnf, -, -⟩ := ptseytin_repr f hvars b (le_refl b)
  have hs := formula_size_pos f
  have hClauses : ∀ C ∈ preTseytin b f, C.length = 3 :=
    (kCNF_clause_length 3 _).mp (preTseytin_kCNF3 b f)
  -- NB the explicit `Nat` binder: with the inferred `var` binder the `<`
  -- carrier is `var` and omega goes blind (HANDOFF `Var := Nat` gotcha)
  have hVars : ∀ v : Nat, varInCnf v (preTseytin b f) → v < b + formula_size f := by
    intro v hv
    obtain ⟨C, hC, hVar⟩ := hv
    rcases List.mem_cons.mp hC with rfl | hC
    · obtain ⟨l, hl, s, heq⟩ := hVar
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;>
        (simp only [Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq; omega)
    · rcases hcnf v ⟨C, hC, hVar⟩ with h | ⟨-, h⟩ <;> omega
  calc encodable.size (preTseytin b f)
      ≤ (preTseytin b f).length * (3 * (b + formula_size f + 1) + 4) :=
        encodable_size_cnf3_le hClauses hVars
    _ ≤ (3 * formula_size f + 1) * (3 * (b + formula_size f + 1) + 4) := by
        refine Nat.mul_le_mul_right _ ?_
        show (ptseytin b f).length + 1 ≤ 3 * formula_size f + 1
        have := ptseytin_length_le f b
        omega

end PreTseytin
