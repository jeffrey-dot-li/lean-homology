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


**Anti-looping protocol** (CRITICAL):
- **Test, don't theorize.** If you're unsure whether a tactic will work, *edit the file and check diagnostics*. Never spend more than 2-3 sentences reasoning about whether something will work — just try it. Lean's feedback is faster and more reliable than mental simulation.
- **Track your attempts.** After **3 failed approaches** to the same subgoal, **stop and report** to the user with:
  1. The current goal state
  2. What you tried and why each failed
  3. Your best hypothesis for the root cause
- **Detect cycles.** If you catch yourself considering an approach you already rejected, you are looping. Stop immediately and report.
- **Recognize structural problems.** If the issue is not "which tactic closes this goal" but "the definition/API doesn't support this proof strategy," that's a `/plan` problem, not a `/fill-sorry` problem. Report to the user: "This may need a restructuring — want to switch to `/plan`?"
- **Never silently struggle.** The user prefers a concise "I'm stuck because X" message over 5000 tokens of increasingly desperate attempts.
- **Narrate your reasoning.** Before each tool call, write a one-line summary of *why* you're making it (e.g., "Checking whether `liftFromProjective_comp` gives the rewrite I need" or "Goal has `biprod` — trying `simp` with biprod lemmas"). This lets the user follow your thought process and interrupt early if you're going down a wrong path.


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
