# Step 10 — Re-audit every remaining reduction under the strengthened `⪯p`

## Objective
Ensure that no reduction theorem survives merely because the old reduction notion was too weak.

## Read first
- `README.md`
- every reduction file under `CookLevin/Complexity/NP/SAT/CookLevin/Reductions/`
- `CookLevin/Complexity/NP/kSAT_to_SAT.lean`
- `CookLevin/Complexity/NP/kSAT_to_FlatClique.lean`
- matching Coq docs for the corresponding reductions

## Required work
1. Visit every theorem of the form `P ⪯p Q` that still remains in the repository.
2. Check that each one now supplies:
   - a real polynomial-time map,
   - full correctness (`↔`),
   - any required output-size bounds or helper lemmas.
3. Repair or replace any reduction that still depends on search, placeholder semantics, or forward-only correctness.
4. Clean up theorem statements or helper APIs where earlier placeholder choices left technical debt.

## Concrete expectations
- This is a systematic audit, not just spot fixes.
- Prefer small local helper lemmas over ad hoc proof duplication.
- If a reduction must be deferred, document the exact blocker in `README.md` rather than silently leaving a weak theorem in place.

## Definition of done
- Every surviving `⪯p` theorem in the repository uses the strengthened reduction notion honestly.
- Remaining reduction files compile without relying on placeholder complexity facts.
- `lake build` succeeds.
- `README.md` lists any reductions still pending and why; ideally none remain in scope for this step.
