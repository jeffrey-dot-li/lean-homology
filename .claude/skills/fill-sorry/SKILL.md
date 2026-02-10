---
name: fill-sorry
description: Prove a specific sorry'd lemma iteratively using Lean LSP tools.
---

# Fill Sorry Mode

Prove a specific `sorry`'d lemma using the LSP tools iteratively.

Target: $ARGUMENTS

## Procedure

1. **Check memory first** — read `proof-patterns.md` and `pitfalls.md` for strategies relevant to this proof shape.
2. Read the lemma and use `lean_goal` at the `sorry` to understand the proof state.
3. Try simple tactics first via `lean_multi_attempt`: `["simp", "ring", "omega", "exact?", "aesop"]`.
4. If those fail, use the search decision tree:
   - `lean_state_search` / `lean_hammer_premise` to find closing lemmas
   - `lean_leansearch` / `lean_loogle` for specific lemma lookup
5. Build the proof incrementally — add tactics one at a time, checking `lean_goal` after each.
6. **Verify completion** with `lean_diagnostic_messages` on the full lemma. No errors = done.
7. If stuck after several attempts, report the remaining goal state to the user and ask for guidance.

## After completion

If the proof involved a non-obvious strategy (took multiple attempts, required a surprising lemma, or used an unusual tactic pattern), **proactively save it to memory**:
- Tactic pattern → `proof-patterns.md`
- Useful Mathlib lemma → `mathlib-api.md`
- Gotcha or failed approach → `pitfalls.md`

Ask the user: "This proof used [strategy] — want me to save this pattern to memory for future use?"

## Rules

- Never leave a proof unverified.
- If a proof exceeds ~30 lines, suggest decomposing into helper lemmas.
- `lean_goal` is your most important tool — use it after every tactic.
