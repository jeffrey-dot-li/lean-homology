---
name: clean
description: Fix warnings line by line and bring code into compliance with Mathlib style standards.
---

# Clean Mode

Fix compiler warnings and linter hints in an existing file, line by line, without changing proof structure.

Target: $ARGUMENTS

## Procedure

1. Run `lean_diagnostic_messages` on the target file with no severity filter to get the full list of warnings, hints, and infos.
2. Work through them **one at a time**, from top to bottom.
3. After each fix, re-run `lean_diagnostic_messages severity="error"` to confirm no new errors were introduced.
4. After clearing a batch of warnings, show the user a summary of what was fixed.

## Lean Linter Workflow

- Treat `lean_diagnostic_messages` and `runLinter` as different signals. `lean_diagnostic_messages` tells you whether the file currently compiles in the editor; `lake exe runLinter` checks extra style linters and may report issues from imported files too.
- If `runLinter` output looks stale or disagrees with the source you just edited, rebuild the target module first: `lake build <Module>` and then rerun `lake exe runLinter <Module>`.
- After changing a declaration that affects linter behavior directly (especially `@[simp]` lemmas and `simpNF` issues), do **not** trust an old terminal run. Always rerun `lake build <Module> && lake exe runLinter <Module>`.
- When linting a module, separate errors in the target file from errors coming from imports before deciding what to fix in `/clean`.

## What belongs here

- **Deprecation warnings**: replace deprecated names with their canonical Mathlib successors (use `lean_hover_info` or `lean_leansearch` to find the replacement).
- **Unused variable warnings** (`_` prefix or remove): rename `x` → `_x` or `_` as appropriate.
- **`Try this:` suggestions**: apply `simp only [...]`, `exact ...`, `apply ...` suggestions from `simp?`/`exact?`/`apply?`. Use `lean_diagnostic_messages severity="info"` to retrieve them.
- **Linter hints**: `@[simp]` on non-`simp`-normal forms, `protected` suggestions, `noncomputable` placement, etc.
- **Style**: `lemma` vs `theorem` per convention in `assistants.md`; doc string format (`/-- ... -/` with a period); whitespace.
- **Namespace hygiene**: remove redundant `open` statements; use fully qualified names where the open causes ambiguity.

## Rules

- The proof must compile (no errors) after every single edit.
- Never change proof *structure* — don't extract lemmas, rename theorems, or reorder steps. Use `/refactor` for that.
- If a warning cannot be fixed without restructuring, note it for the user and skip it.
- If a `Try this:` suggestion changes the meaning or makes the proof fragile, don't apply it blindly — flag it.
