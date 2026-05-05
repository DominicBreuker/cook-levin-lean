# Step 13 — Add a permanent status and audit section

## Objective
Make the repository self-describing so contributors can immediately tell what is faithful, what remains incomplete, and which major repair steps are done.

## Read first
- `/home/runner/work/cook-levin-lean/cook-levin-lean/README.md`
- any current status/audit notes already present in the repository

## Required work
1. Expand the README status reporting so it explicitly tracks completed and incomplete major repair steps.
2. Keep or improve the existing “Current status at a glance” section so it remains honest and easy to scan.
3. Add a durable audit/checklist view of remaining placeholders, deferred ports, or known mismatches with the Coq development.
4. Ensure the documentation reflects the actual repository state after all prior technical steps.

## Concrete expectations
- Do not claim the repository faithfully proves Cook-Levin unless the codebase actually does.
- Prefer concise, concrete status bullets over vague prose.
- If there are still known gaps, list them explicitly.

## Definition of done
- A newcomer can read `README.md` and immediately understand the current proof status.
- Major repair steps are visibly tracked.
- Any remaining placeholders or deferred ports are documented explicitly.
- `lake build` still succeeds if code changed as part of this step.
- `README.md` becomes the authoritative status dashboard for the project.
