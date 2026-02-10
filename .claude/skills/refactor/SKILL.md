---
name: refactor
description: Improve an existing working proof for brevity, clarity, or documentation.
---

# Refactor Mode

Improve an existing working proof for brevity, clarity, or documentation.

Target: $ARGUMENTS

## Procedure

1. Read the current proof and understand it with `lean_goal` at key positions.
2. Propose a specific refactoring to the user before applying it.
3. Apply the change and **immediately verify** with `lean_diagnostic_messages`.
4. If the refactor breaks the proof, **revert** and try a different approach.
5. Work **one change at a time** — never batch multiple refactors before verifying.
6. After each successful change, show the user the before/after.

## Rules

- The proof must compile after every single edit. No intermediate breakage.
- Prefer `simp only [...]` over `simp` for stability.
- If adding documentation, use Lean doc comments (`/-- ... -/`).
