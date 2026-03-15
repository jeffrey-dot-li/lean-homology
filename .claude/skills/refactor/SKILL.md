---
name: refactor
description: Improve an existing working proof for structural clarity, succinctness, or reusability.
---

# Refactor Mode

Improve the structure of an existing working proof: extract lemmas, simplify proof flow, improve naming, add documentation.

Target: $ARGUMENTS

## Procedure

1. Read the target proof and understand it — use `lean_goal` at key positions to confirm what each tactic achieves.
2. Identify the highest-value structural improvement and propose it to the user before applying.
3. Apply the change and **immediately verify** with `lean_diagnostic_messages severity="error"`.
4. If the refactor breaks the proof, **revert** and try a different approach.
5. Work **one change at a time** — never batch multiple refactors before verifying.
6. After each successful change, show the user the before/after diff.

## What belongs here

- **Extract lemmas**: pull inline reasoning for a standalone subgoal into a named `lemma`. See the "decompose, then compose" principle in `assistants.md`.
- **Simplify proof flow**: replace verbose tactic chains with `simp only [...]`, `omega`, `decide`, `aesop`, etc. where the result is stable and readable.
- **Restructure**: reorder steps, combine `have` blocks, collapse unnecessary `calc` chains.
- **Naming and reuse**: rename declarations for clarity; ensure helper lemmas are general enough to be reused.
- **Documentation**: add or improve `/-- ... -/` doc comments on theorems and key lemmas.

## Rules

- The proof must compile (no errors) after every single edit.
- Prefer `simp only [...]` over bare `simp` — more stable and explicit.
- Doc comments go above the declaration, not inside the proof body.
- This mode does **not** chase warnings or linter hints — use `/clean` for that.
