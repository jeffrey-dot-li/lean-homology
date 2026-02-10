---
name: research
description: Find whether a theorem/concept exists in Mathlib and locate building blocks for a new theorem.
---

# Research Mode

Find whether a theorem/concept exists in Mathlib, and locate the building blocks needed for a new theorem.

Research topic: $ARGUMENTS

## Procedure

1. Use `lean_leansearch`, `lean_loogle`, `lean_leanfinder` to search for the concept.
2. Use `lean_local_search` to check what already exists in this project.
3. For each relevant result, use `lean_hover_info` and/or `lean_declaration_file` to get the full signature and source location.
4. **Always cite results with `file_path:line_number` format** so they are alt+clickable in VSCode.
5. Summarize findings: what exists, what's missing, and what building blocks are available.

## Output

A structured summary with clickable references. **No code edits in this mode.**
