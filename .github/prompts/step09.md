# Step 09 — Replace `FSAT_to_SAT` and `FSAT_to_3SAT` with Tseitin-style reductions

## Objective
Eliminate assignment search from the satisfiability reductions and replace it with syntactic Tseitin-style transformations.

## Read first
- `/home/runner/work/cook-levin-lean/cook-levin-lean/README.md`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/FSAT_to_SAT.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/coqdoc/Complexity.NP.SAT.FSAT.FSAT_to_SAT.txt`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/FSAT.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/SAT.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/kSAT.lean`

## Required work
1. Remove `FSAT_search` and any related search-based reduction logic.
2. Port or reconstruct the Tseitin transformation from the Coq reference, including any preprocessing such as OR elimination if still needed.
3. Prove correctness of the generated CNF / 3-CNF encoding.
4. Prove polynomial output-size growth and polynomial-time computability.
5. Re-establish both `FSAT ⪯p SAT` and `FSAT ⪯p kSAT 3` using the repaired reduction notion.

## Concrete expectations
- The output instance must depend only on syntactic transformation of the input formula.
- Keep auxiliary correctness lemmas organized so later maintenance is possible.
- If helper definitions are imported from Coq in a slightly different shape, document that in code or README as appropriate.

## Definition of done
- Search-based satisfiability reduction code is gone.
- The Lean development contains a real Tseitin-style reduction with correctness and complexity proofs.
- Both FSAT reduction theorems compile under the strengthened `⪯p` definition.
- `lake build` succeeds.
- `README.md` records that the FSAT reductions are now syntactic and polynomial-time.
