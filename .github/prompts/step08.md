# Step 08 — Replace `BinaryCC_to_FSAT` brute-force trace enumeration

## Objective
Build the FSAT instance directly from tableau constraints instead of enumerating all traces.

## Read first
- `/home/runner/work/cook-levin-lean/cook-levin-lean/README.md`
- `/home/runner/work/cook-levin-lean/cook-levin-lean/CookLevin/Complexity/NP/SAT/CookLevin/Reductions/BinaryCC_to_FSAT.lean`
- matching Coq docs under `/home/runner/work/cook-levin-lean/cook-levin-lean/coqdoc/Complexity.NP.SAT.CookLevin.Reductions.*`
- the repaired BinaryCC and FSAT infrastructure from earlier steps

## Required work
1. Remove the current brute-force machinery that enumerates bitstrings and accepting traces.
2. Construct a formula that directly expresses the BinaryCC tableau constraints.
3. Prove semantic correctness in both directions using the strengthened reduction notion.
4. Prove explicit size growth and polynomial-time computability of the construction.
5. Update any helper lemmas needed for the direct encoding.

## Concrete expectations
- The target formula should be derived syntactically from the BinaryCC instance, not from a search over candidate runs.
- Avoid introducing a new hidden exponential-time helper.
- Keep the reduction theorem statement aligned with the repaired `⪯p` API.

## Definition of done
- `allBitStrings`, `acceptingRunsFrom`, and the disjunction-over-traces approach are removed from the reduction path.
- `BinaryCC_to_FSAT` is a real polynomial-time reduction.
- The proof uses explicit constraint and size lemmas instead of existential placeholders.
- `lake build` succeeds.
- `README.md` records that the brute-force BinaryCC reduction has been eliminated.
