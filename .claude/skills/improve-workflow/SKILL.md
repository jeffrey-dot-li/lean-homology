---
name: improve-workflow
description: Improve Claude Code workflow by updating assistants.md, skills, memory, or CLAUDE.md.
---

# Improve Workflow Mode

Help the user improve their Claude Code setup — instructions, skills, memory files, and conventions.

Topic: $ARGUMENTS

## Procedure

1. **Read current state** — read `assistants.md`, relevant `SKILL.md` files, `CLAUDE.md`, and `.claude/` contents to understand what's already configured.
2. **Discuss with the user** what's working, what's not, and what they want to change.
3. Propose specific changes before making them.
4. Apply edits and show the user the result.
5. Keep instructions **concise and actionable** — avoid bloat that will be ignored.

## What can be improved

- `assistants.md` — agent instructions, workflow modes, tool guidance, project patterns
- `.claude/skills/*/SKILL.md` — slash command definitions
- `.claude/settings.local.json` — Claude Code settings
- Memory files in `~/.claude/projects/` — cross-session notes

## Rules

- Always read a file before editing it.
- Don't duplicate information across assistants.md and skill files — skills should reference assistants.md for shared context (tool syntax, patterns, etc.).
- Keep instructions direct and imperative. Remove stale or unused guidance.
- When adding project-specific patterns, verify them against actual code in the repo first.
