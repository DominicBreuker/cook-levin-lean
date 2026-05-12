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

# Step 12 finishing guide — closing the remaining sorries and remove errors

You have an excellent draft. Most of the structural work is done correctly: the Tseytin clause gadgets, their truth-table proofs, the recursive `tseytin'`, the `tseytin_formula_repr` invariant shape, the `eliminateOR` machinery, and the entire `FSAT_to_SAT_tseytin_correct` outer proof are sound. What remains are *gaps*, not architectural problems.

Good luck. Most of the conceptual hard work is behind you — what remains is mechanical engineering. Slow and steady.
