# Step 03 — Redefine polynomial-time many–one reduction

## Objective
Strengthen `⪯p` so reductions include real polynomial-time computability and full correctness, not just a forward implication.

## Read first
- `/home/runner/work/cook-levin-lean/cook-levin-lean/README.md`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/Complexity/NP.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/coqdoc/Complexity.Complexity.NP.txt`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/coqdoc/Complexity.Complexity.PolyTimeComputable.txt`

## Required work
1. Redefine `ReductionWitness` / `reducesPolyMO` so a reduction includes:
   - the reduction function,
   - a polynomial-time computability proof for that function,
   - the intended correctness statement `P x ↔ Q (f x)`.
2. Re-prove the standard interface lemmas, at least reflexivity, transitivity, elimination, and `red_inNP`.
3. Ensure the new transitivity proof actually composes runtime and result-size bounds instead of bypassing them.
4. Update direct users of `⪯p` only as far as necessary to keep the repository compiling honestly.

## Concrete expectations
- Do not leave a one-way implication hidden anywhere in the reduction API.
- Reuse the Coq decomposition for composition lemmas where possible.
- Keep theorem names stable when practical.

## Definition of done
- A reduction theorem can no longer be proved without a real polynomial-time map.
- `reducesPolyMO_transitive` composes the stronger witnesses correctly.
- The main NP lemmas depending on reductions compile again.
- `lake build` succeeds.
- `README.md` clearly records that the reduction notion is now non-placeholder.
