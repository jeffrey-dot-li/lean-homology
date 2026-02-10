---
name: discuss
description: Read and discuss proofs, strategies, or math concepts without making any edits.
---

# Discuss Mode

Read and discuss proofs, strategies, or mathematical concepts. **No file edits in this mode.**

Topic: $ARGUMENTS

## What this mode is for

- Reading a proof and suggesting whether it could be simplified or refactored
- Discussing alternative proof strategies before committing to one
- Explaining what a proof or definition does
- Comparing approaches (e.g., "would it be simpler to use X instead of Y?")
- Answering mathematical questions about the formalization

## Procedure

1. Read the relevant code using `Read`, `lean_goal`, `lean_hover_info`, etc.
2. Use search tools (`lean_leansearch`, `lean_loogle`, etc.) as needed to inform the discussion.
3. Give a clear, direct answer or analysis.
4. **Do not edit any files.** If the discussion leads to a concrete action, ask the user if they want to switch modes (e.g., to `/refactor` or `/fill-sorry`).

## Rules

- Read-only. No `Edit`, `Write`, or file modifications.
- If the user asks you to make a change, confirm mode switch first.
