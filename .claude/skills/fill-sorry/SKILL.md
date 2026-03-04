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
4. If those fail, **simplify the goal first** before searching Mathlib:
   - Try `simp`, `dsimp`, `ext`, `change` to make the goal more concrete
   - Check `lean_goal` — often the simplified goal suggests the next step
   - Use `simpa using h` to see if existing hypotheses close it after simplification
5. Only search Mathlib (`lean_state_search`, `lean_leansearch`, `lean_loogle`) when you have a **specific** lemma shape in mind, not as a fishing expedition.
6. Build the proof incrementally — add tactics one at a time. **After every edit:**
   - First, check `lean_diagnostic_messages` on the edited line(s) (`start_line`/`end_line`) to confirm no errors. `lean_goal` succeeding does NOT mean the tactic compiled — a failing tactic (e.g., "`simp` made no progress") still shows a goal on the next line (the unchanged one).
   - Then, check `lean_goal` after the tactic to see the new proof state.
   - If diagnostics show an error, **revert the edit** before trying something else.
7. **Verify completion** with `lean_diagnostic_messages` on the full lemma. No errors = done.
8. If stuck after several attempts, report the remaining goal state to the user and ask for guidance.

## Core principle: EXTRACT, don't inline

When a subgoal looks like a standalone mathematical statement — general types, no proof-specific local variables — **extract it as a sorry'd lemma above the current proof**. Then:
1. Finish the main proof assuming the new lemma (it should become simple plumbing).
2. Go back and fill the extracted lemma separately.

Signs you should extract:
- The subgoal involves only types from the lemma signature (not local `let`/`have` bindings)
- You'd need >5 lines of non-trivial tactics to close it
- The statement would make sense out of context (e.g., "sigma inclusions are mono")
- You find yourself wanting to search Mathlib for it — it's probably a lemma-shaped gap

The main proof should read like an outline: named lemmas composed with `rw`, `exact`, `simp`.

## Core principle: TRY THINGS, don't search

**Bias toward editing the file and checking goals, not toward searching Mathlib.** The LSP feedback loop (edit → `lean_goal` → adjust) is faster and more reliable than trying to find the perfect abstract lemma. Concretely:

- If you're unsure whether `simp` / `ext` / `congr` will help, **just try it** — it takes one tool call. Don't spend 3 searches looking for a lemma that might do the same thing.
- When the goal looks complex, try `simp` or `dsimp` first to see what it simplifies to. The simplified form often makes the next step obvious.
- Searching Mathlib is valuable for **named theorems you can't guess** (e.g., `Sigma.mk.inj_iff`), not for finding the perfect API to avoid writing 3 lines of tactics.
- **Budget rule**: For every Mathlib search call, you should have made at least 2 edit-and-check cycles first.

## Anti-looping protocol (CRITICAL)

- **Test, don't theorize.** If you're unsure whether a tactic will work, *edit the file and check diagnostics*. Never spend more than 2-3 sentences reasoning about whether something will work — just try it.
- **Detect cycles.** If you catch yourself considering an approach you already rejected, you are looping. Stop immediately and report.
- **Recognize structural problems.** If the issue is not "which tactic closes this goal" but "the definition/API doesn't support this proof strategy," that's a `/draft` problem, not a `/fill-sorry` problem. Report to the user: "This may need a restructuring — want to switch to `/draft`?"
- **Never silently struggle.** The user prefers a concise "I'm stuck because X" message over 5000 tokens of increasingly desperate attempts.
- **Narrate your reasoning.** Before each tool call, write a one-line summary of *why* you're making it. This lets the user follow your thought process and interrupt early if you're going down a wrong path.


## After completion

If the proof involved a non-obvious strategy (took multiple attempts, required a surprising lemma, or used an unusual tactic pattern), **proactively save it to memory**:
- Tactic pattern → `proof-strategies.md`
- Useful Mathlib lemma or API pattern → appropriate `.claude/memory/api/` file
- Gotcha or failed approach → appropriate `.claude/memory/api/` file (under a "Pitfall" heading)

Ask the user: "This proof used [strategy] — want me to save this pattern to memory for future use?"

## Rules

- Never leave a proof unverified.
- If a proof exceeds ~30 lines, suggest decomposing into helper lemmas.
- `lean_goal` is your most important tool — use it after every tactic.
