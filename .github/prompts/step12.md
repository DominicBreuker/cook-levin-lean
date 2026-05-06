# Step 12 — Replace the remaining SAT / clique placeholders

## Why this task still exists

Even after the Cook-Levin tableau chain is repaired, the repository still has separate placeholder reductions and NP-membership proofs on the SAT / clique side.

## Read these files first

### Lean files
- `README.md`
- `CookLevin/Complexity/NP/FSAT_to_SAT.lean`
- `CookLevin/Complexity/NP/SAT.lean`
- `CookLevin/Complexity/NP/FSAT.lean`
- `CookLevin/Complexity/NP/kSAT.lean`
- `CookLevin/Complexity/NP/kSAT_to_SAT.lean`
- `CookLevin/Complexity/NP/kSAT_to_FlatClique.lean`
- `CookLevin/Complexity/NP/FlatClique.lean`

### Coq reference files
- `coqdoc/Complexity.NP.SAT.FSAT.FSAT_to_SAT.txt`
- `coqdoc/Complexity.NP.SAT.FSAT.FSAT.txt`
- `coqdoc/Complexity.NP.SAT.FSAT.FormulaEncoding.txt`
- `coqdoc/Complexity.NP.SAT.SAT.txt`
- `coqdoc/Complexity.NP.SAT.SAT_inNP.txt`
- `coqdoc/Complexity.NP.SAT.kSAT.txt`
- `coqdoc/Complexity.NP.SAT.kSAT_to_SAT.txt`
- `coqdoc/Complexity.NP.Clique.FlatClique.txt`
- `coqdoc/Complexity.NP.Clique.kSAT_to_FlatClique.txt`

## Concrete problems visible today

- `FSAT_to_SAT.lean` still uses `FSAT_search` and constant yes/no output instances.
- `SAT_inNP.sat_NP` still has two `sorry`s.
- `kSAT_to_SAT_poly`, `kSAT_to_FlatClique_poly`, and `FlatClique_in_NP` are still unfinished.
- The final theorem file depends on all of these theorems directly.

## Required work

1. Replace the search-based `FSAT → SAT` / `FSAT → 3SAT` construction with a direct syntactic transformation, following Coq.
2. Finish the NP-membership proofs for SAT and FlatClique honestly.
3. Finish `kSAT_to_SAT_poly` and `kSAT_to_FlatClique_poly` under the repaired reduction API.
4. Keep theorem names stable so `CookLevin.lean` only needs minimal cleanup later.

## Done when

- no search-based SAT reduction remains,
- `sat_NP`, `kSAT_to_SAT_poly`, `kSAT_to_FlatClique_poly`, and `FlatClique_in_NP` are honest proofs,
- the README says the non-Cook-Levin side of the theorem chain is repaired.
