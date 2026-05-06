# Repository Agent Instructions

- Read `README.md` and the current target files before making changes.
- This repository is primarily a Lean4 project. Match the existing Lean style and keep changes small.
- Lean tooling is expected to be available before you start: `lean`, `lake`, Mathlib cache, `rg`, and the `lean-lsp` MCP server.
- Prefer Lean MCP tools over blind guessing when working on `.lean` files:
  - `lean_diagnostic_messages` for fast per-file errors/warnings
  - `lean_goal` / `lean_term_goal` to inspect proof states
  - `lean_local_search`, `lean_leansearch`, `lean_loogle`, and `lean_leanfinder` to find existing lemmas (loogle has a rate limit, 3 requests every 30 seconds)
  - `lean_multi_attempt` to compare tactic candidates
  - `lean_verify` before claiming a proof is complete or sound
- Use `import Mathlib` explicitly in proof files when you need Mathlib lemmas or tactics.
- A good Lean workflow is: inspect diagnostics/goals → search for existing lemmas → try candidate tactics/proof terms → re-check diagnostics and soundness → finish with `lake build`.
- Use `lake build` for whole-project checkpoints, but use Lean MCP diagnostics first for faster iteration.
