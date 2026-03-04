---
name: interactive
description: Fill a sorry one step at a time, directed by the user.
---

# Interactive Mode

Work through a proof one step at a time, with the user directing each move.

Target: $ARGUMENTS

## How this differs from `/fill-sorry`

`/fill-sorry` is autonomous — the agent tries tactics, searches Mathlib, and drives the proof to completion. `/interactive` is **user-driven** — the agent executes exactly what the user asks, shows the result, and waits.

## Procedure

1. Read the target lemma and show the initial goal state via `lean_goal` at the `sorry`.
2. **Wait for the user's instruction.** The user will say something like "apply Functor.map_comp" or "simplify with simp" or "rewrite using h".
3. Convert the user's instruction into clean Lean tactic(s). Write the minimal code needed — nothing extra.
4. Edit the file, then **check `lean_diagnostic_messages`** on the edited line(s) (`start_line`/`end_line`) to confirm no errors, then show the new goal state with `lean_goal`. A tactic can fail (e.g., "`simp` made no progress") while `lean_goal` on the next line still shows a goal (the unchanged one) — diagnostics catch this.
5. If diagnostics show an error, report it and revert. Do not attempt a fix unless the user asks.
6. **Stop and wait.** Do not attempt the next step, suggest tactics, or continue the proof unprompted.

## Rules

- **One step per turn.** Only do what the user asked. No speculative next steps, no "while we're here" additions.
- **Diagnostics before goals.** After every edit, check `lean_diagnostic_messages` on the edited line(s) first, then `lean_goal`. Never trust `lean_goal` alone — it shows a goal even when the tactic errored.
- **No autonomous searching.** Don't search Mathlib or try `lean_state_search` unless the user asks (e.g., "search for a lemma about X" or "what closes this?").
- **Keep edits minimal.** If the user says "destruct h", write `obtain ⟨a, b⟩ := h` — don't also rename variables, reorder goals, or add annotations.
- **Revert on failure.** If a tactic fails, undo the edit and report the error. Don't try alternatives unless asked.
- **Always verify before responding.** Never assume a tactic worked — confirm it compiles via diagnostics and show the actual resulting goal state, not what you think it should be.
- **Ask immediately when unclear.** If the instruction is ambiguous or would require structural changes (definition update, missing lemma, goal mismatch), ask a short clarifying question right away. Don't deliberate internally — a one-line question is cheaper than 1000 tokens of reasoning about what the user might have meant.
- It's fine to ask a brief clarifying question if the user's instruction is ambiguous (e.g., "there are two hypotheses named `h` — which one?"), but don't over-ask.
