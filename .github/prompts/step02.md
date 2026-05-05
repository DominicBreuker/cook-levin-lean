# Step 02 — Rebuild `inTimePoly`, `inNP`, and polynomial certificate relations

## Objective
Make the NP-membership layer mathematically meaningful by requiring an actual verifier/decider with polynomial running time and explicit certificate-size bounds.

## Read first
- `/home/runner/work/cook-levin-lean/cook-levin-lean/README.md`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/Complexity/NP.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/GenNP.lean`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/coqdoc/Complexity.Complexity.NP.txt`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/coqdoc/Complexity.Complexity.PolyTimeComputable.txt`

## Required work
1. Redefine `inTimePoly` so it depends on a real decider or verifier together with a polynomial bound.
2. Rework `polyCertRel` so witness existence is paired with an explicit polynomial size bound in the encoded input size.
3. Port or rebuild `inNP`, `inP`, `inNP_intro`, and `P_NP_incl` around the repaired complexity notions.
4. Update immediate downstream call sites that rely on the old placeholder API, but do not yet try to repair the entire reduction chain.
5. Remove any uses of the old trivial `inTimePoly_linear` shortcut in this layer.

## Concrete expectations
- Follow the Coq structure as closely as practical.
- Make the size bound part of the certificate relation API, not an informal side condition.
- Preserve theorem names when possible to minimize churn downstream.

## Definition of done
- `inNP P` now requires a concrete relation with a real polynomial-time verifier.
- Certificate-size bounds are explicit in the Lean structures.
- Core NP lemmas compile against the new definitions.
- `lake build` succeeds.
- `README.md` reflects that Step 2 is complete and summarizes the new NP API.
