# assistants.md

Guidance for Code Assistant Agents working in this repository.

## Project Overview

Lean 4 formalization of homotopy computations in algebraic topology.

## Terminal Settings

Commands use `fish` shell syntax.

## Workflow Modes

The user works in distinct modes. Modes are activated by slash commands (e.g., `/research`) or inferred from context.

### Modal behavior

- **Stay in the current mode** until the user explicitly switches (e.g., `/fill-sorry`) or the conversation ends.
- If the user's request fits a different mode, **ask before switching**: e.g., "This sounds like it needs `/refactor` — want me to switch modes?"
- If no mode has been set yet, infer from the first request. If ambiguous, ask.
- When in a read-only mode (`/research`, `/discuss`), **do not edit files** unless the user explicitly asks to switch to an editing mode.

### Mode 1: Research (`/research`)

**Goal**: Find whether a theorem/concept exists in Mathlib, and locate the building blocks needed for a new theorem.

**Procedure**:
1. Use `lean_leansearch`, `lean_loogle`, `lean_leanfinder` to search for the concept.
2. Use `lean_local_search` to check what already exists in this project.
3. For each relevant result, use `lean_hover_info` and/or `lean_declaration_file` to get the full signature and source location.
4. **Always cite results with `file_path:line_number`** format so the user can alt+click to navigate.
5. Summarize findings: what exists, what's missing, and what building blocks are available.

**Output**: A structured summary with clickable references. No code edits.

### Mode 2: Draft (`/draft`)

**Goal**: Draft the theorem/lemma structure needed to prove a larger result, given a proof sketch or mathematical reference (e.g., from Hatcher).

**Important**: `/draft` is a **custom skill**, not the builtin `/plan`. The builtin `/plan` enters a read-only mode that writes a markdown plan for approval before any code is written. `/draft` writes **actual Lean code** — sorry'd declarations that compile — directly in source files.

**Procedure**:
1. **Research first** — run Mode 1 to understand what Mathlib already provides.
2. Work **interactively** with the user to decompose the proof into lemmas.
3. Write all declarations with `sorry` proofs — no filled proofs in this mode.
4. Each lemma should be **provable independently in ~30 lines or fewer**.
5. Verify each `sorry`'d statement compiles with `lean_diagnostic_messages` before moving on.
6. Present the full dependency structure: which lemmas feed into which.

**Output**: A compilable file (or section) of `sorry`'d declarations with clear names and docstrings. Iterate with the user until the decomposition is right.

### Mode 3: Fill Sorry (`/fill-sorry`)

**Goal**: Prove a specific `sorry`'d lemma using the LSP tools iteratively.

**Procedure**:
1. Read the lemma and use `lean_goal` at the `sorry` to understand the proof state.
2. Try simple tactics first via `lean_multi_attempt`: `["simp", "ring", "omega", "exact?", "aesop"]`.
3. If those fail, use the search decision tree:
   - `lean_state_search` / `lean_hammer_premise` to find closing lemmas
   - `lean_leansearch` / `lean_loogle` for specific lemma lookup
4. Build the proof incrementally — add tactics one at a time, checking `lean_goal` after each.
5. **Verify completion** with `lean_diagnostic_messages` on the full lemma. No errors = done.
6. If stuck after several attempts, report the remaining goal state to the user and ask for guidance.

**Key rules**:
- Never leave a proof unverified.
- If a proof exceeds ~30 lines, suggest decomposing into helper lemmas (switch to Mode 2).

**Anti-looping protocol** (CRITICAL):
- **Test, don't theorize.** If you're unsure whether a tactic will work, *edit the file and check diagnostics*. Never spend more than 2-3 sentences reasoning about whether something will work — just try it. Lean's feedback is faster and more reliable than mental simulation.
- **Detect cycles.** If you catch yourself considering an approach you already rejected, you are looping. Stop immediately and report.
- **Recognize structural problems.** If the issue is not "which tactic closes this goal" but "the definition/API doesn't support this proof strategy," that's a `/draft` problem, not a `/fill-sorry` problem. Report to the user: "This may need a restructuring — want to switch to `/draft`?"
- **Never silently struggle.** The user prefers a concise "I'm stuck because X" message over 5000 tokens of increasingly desperate attempts.
- **Narrate your reasoning.** Before each tool call, write a one-line summary of *why* you're making it (e.g., "Checking whether `liftFromProjective_comp` gives the rewrite I need" or "Goal has `biprod` — trying `simp` with biprod lemmas"). This lets the user follow your thought process and interrupt early if you're going down a wrong path.

### Mode 4: Interactive (`/interactive`)

**Goal**: Work through a proof one step at a time, with the user directing each move.

**How this differs from `/fill-sorry`**: `/fill-sorry` is autonomous — the agent drives the proof to completion. `/interactive` is **user-driven** — execute exactly what the user asks, show the goal state, and wait.

**Procedure**:
1. Read the target and show the initial goal state at the `sorry`.
2. Wait for the user's instruction (e.g., "apply X", "rewrite with h", "simplify").
3. Convert to clean Lean, edit the file, show the new goal state.
4. Stop and wait. Do not attempt more steps.

**Key rules**:
- One step per turn. No speculative next steps.
- Show goal state after every edit.
- No autonomous Mathlib searching unless asked.
- Revert on failure — don't try alternatives unless asked.
- Always verify with `lean_diagnostic_messages` and `lean_goal` before responding. Never assume a tactic compiled.
- Flag structural issues before editing — if the step needs changes elsewhere (definition update, missing lemma), don't deliberate for hundreds of tokens. A short clarifying question is always cheaper.

### Mode 5: Refactor (`/refactor`)

**Goal**: Improve an existing working proof for brevity, clarity, or documentation.

**Procedure**:
1. Read the current proof and understand it with `lean_goal` at key positions.
2. Propose a specific refactoring (e.g., "replace lines 15-25 with `simp [lemma_a, lemma_b]`").
3. Apply the change and **immediately verify** with `lean_diagnostic_messages`.
4. If the refactor breaks the proof, **revert** and try a different approach.
5. Work **one change at a time** — never batch multiple refactors before verifying.
6. After each successful change, show the user the before/after diff.

**Key rules**:
- The proof must compile after every single edit. No intermediate breakage.
- Prefer `simp only [...]` over `simp` for stability.
- If adding documentation, use Lean doc comments (`/-- ... -/`).

### Mode 6: Discuss (`/discuss`)

**Goal**: Read and discuss proofs, strategies, or math concepts without making any edits.

**Use for**:
- "Can this proof be simplified?"
- "Would it be better to use X instead of Y?"
- "Explain what this definition does."
- Comparing proof strategies before committing.

**Procedure**:
1. Read the relevant code with `Read`, `lean_goal`, `lean_hover_info`, search tools, etc.
2. Give a clear, direct analysis or answer.
3. **Do not edit any files.** If the discussion leads to a concrete action, ask the user if they want to switch modes.

### Mode 7: Improve Workflow (`/improve-workflow`)

**Goal**: Improve the Claude Code setup — instructions, skills, memory, and conventions.

**Procedure**:
1. Read current state: `assistants.md`, relevant skill files, `CLAUDE.md`, `.claude/` contents.
2. Discuss with the user what's working and what to change.
3. Propose changes before applying them.
4. Keep instructions concise and actionable — avoid bloat.

**Key rules**:
- Don't duplicate content across `assistants.md` and skill files.
- Verify project-specific patterns against actual repo code.
- Remove stale guidance when adding new guidance.
- **All project config must be git-tracked.** The user works on multiple machines (laptop + VM). Store everything under the repo (`.claude/`, `assistants.md`, etc.), not in `~/.claude/`. The only exception is the auto-loaded `~/.claude/projects/.../memory/MEMORY.md` which should just redirect to the in-repo files.

## Lean Conventions

### Proof philosophy: decompose, then compose

Complex proofs should be structured as **compositions of obvious, standalone lemmas** that can each be proved independently. Concretely:

- **Extract general subgoals as lemmas.** If a subgoal involves only general types (no proof-specific local context), it should be a standalone lemma with a clear name — not proved inline. Sorry it first, finish the main proof assuming it, then fill it separately.
- **Main proofs should be plumbing.** The top-level proof of a complex theorem should mostly be `rw`, `simp`, `exact`, `apply` — composing named lemmas. If a step needs >5 lines of non-trivial tactics, a lemma is probably missing.
- **Name things for reuse.** A well-named lemma (e.g., `TopCat.sigmaι_cancel`) is a tool in the toolkit. Inline reasoning is disposable. Prefer building tools over solving problems ad hoc.
- **This applies in every mode.** `/draft` does the decomposition upfront. `/fill-sorry` should recognize when extraction is needed mid-proof. `/refactor` should extract inline reasoning into named lemmas.

### `lemma` vs `theorem`

In Lean 4 + Mathlib, `lemma` is a macro that expands to `theorem` — no semantic difference. Use the keyword to signal the result's role:

- **`theorem`** — main results, the "point" of a file or section (e.g., `fundamentalGroup_circle_eq_int`)
- **`lemma`** — supporting/auxiliary results that exist to serve a theorem (e.g., `liftPath_loop_endpoint_eq_int_mul_two_pi`)

When in doubt, use `lemma`. Reserve `theorem` for results a reader would want to find by scanning the file.

## General Operating Rules

1. **Always** verify the proof of a lemma or theorem upon completion before moving onto the next one.
2. Use `lean_diagnostic_messages` to check for errors after writing/editing proofs.
3. Use `lean_goal` to inspect proof states at specific positions.
4. Follow modal behavior rules: stay in the active mode, ask before switching.

## Build System: Lake

Lake is Lean's build system and package manager. Common commands:

```bash
# Build the entire project
lake build

# Build and update dependencies
lake update

# Execute Lake commands in the project environment
lake env <command>

# Clean build artifacts
lake clean
```

## MCP Lean LSP Tools - Essential Workflow

The Lean LSP MCP server provides powerful tools for interactive theorem proving. Use them in this order:

### 1. Understanding Proof States

**`lean_goal`**: View proof goals at a specific position
- Omit `column` to see `goals_before` and `goals_after` at line start/end
- Use this to understand what tactic transformations are needed
- "no goals" means the proof is complete at that point
- **MOST IMPORTANT TOOL** - use frequently!

**`lean_diagnostic_messages`**: Get compiler errors and warnings
- Filter by line range to focus on specific proof sections
- Check after every significant edit to catch type errors early
- **Always use this instead of `getDiagnostics`** — the IDE diagnostics tool returns cspell and other non-Lean noise that pollutes context

### 2. Finding Lemmas and Definitions

**`lean_local_search`**: Fast search for declarations in the local project
- Use BEFORE trying a lemma name to verify it exists
- Example: `lean_local_search "liftPath_lifts"`

**`lean_hover_info`**: Get type signature and documentation
- Column must be at START of identifier
- Essential for understanding API signatures

**`lean_leansearch`** (rate limited: 3/30s): Natural language search in Mathlib
- Examples: "sum of two even numbers is even", "Cauchy-Schwarz inequality"

**`lean_loogle`** (rate limited: 3/30s): Search by type signature
- Examples: `Real.sin`, `(?a → ?b) → List ?a → List ?b`

**`lean_leanfinder`** (rate limited: 10/30s): Semantic/conceptual search
- Examples: "commutativity of addition on natural numbers"

### 3. Exploring Code

**`lean_file_outline`**: Get imports and declarations with signatures (token-efficient but slow)
- Use to understand file structure before diving into details

**`lean_completions`**: Get IDE autocompletions
- Use on INCOMPLETE code (after `.` or partial name)
- Useful for discovering available methods/fields

### 4. Interactive Proof Development

**`lean_multi_attempt`**: Try multiple tactics without modifying the file
- Test 3+ tactics at once to find which works
- Example: `["simp", "ring", "omega"]`
- Returns goal state for each attempt

**`lean_state_search`** (rate limited: 3/30s): Find lemmas to close a goal
- Searches premise-search.com for closing lemmas

**`lean_hammer_premise`** (rate limited: 3/30s): Get premises for automation
- Returns lemma names to try with `simp only [...]` or `aesop`

### 5. Advanced Tools (Use Sparingly)

**`lean_build`**: Rebuild project and restart LSP
- SLOW! Only use when new imports are added

**`lean_profile_proof`**: Profile theorem performance
- SLOW! Shows per-line timing for optimization

## Lemma Search Decision Tree

1. "Does X exist locally?" → `lean_local_search`
2. "I need a lemma that says X" → `lean_leansearch`
3. "Find lemma with type pattern" → `lean_loogle`
4. "What's the Lean name for concept X?" → `lean_leanfinder`
5. "What closes this goal?" → `lean_state_search`
6. "What to feed simp?" → `lean_hammer_premise`

After finding a name: verify with `lean_local_search`, then get details with `lean_hover_info`.


## Output Formatting

- When referencing mathlib declarations in ANY response (including research answers), use the `file_path:line_number` format so they are alt+clickable in VSCode. Use `lean_declaration_file` or `lean_hover_info` to find the source location. Example: `.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Tor.lean:42` instead of just `CategoryTheory.Tor`.


## Loogle Query Syntax

Loogle accepts several query forms, but **bare unquoted names silently return nothing**.

| Query form     | Example                            | Notes                                    |
| -------------- | ---------------------------------- | ---------------------------------------- |
| Name substring | `"comm"`, `"ProjectiveResolution"` | **Must be in double quotes**             |
| Exact constant | `Real.sin`, `List.map`             | Fully qualified, no quotes               |
| Type pattern   | `(?a → ?b) → List ?a → List ?b`    | `?` for metavariables, `_` for wildcards |
| Subexpression  | `_ * (_ ^ _)`                      | Wildcards match any term                 |
| Goal pattern   | `                                  | - _ < _ → _ + 1 < _ + 1`                 | Prefix with ` | -` |

### Common mistakes

- `lean_loogle(query="ProjectiveResolution")` → **no results** (bare name)
- `lean_loogle(query="\"ProjectiveResolution\"")` → finds it (quoted substring)
- `lean_loogle(query="Measure.map")` → **no results** (unquoted partial name)
- `lean_loogle(query="\"Measure.map\"")` → finds it
- `lean_loogle(query="Measure ?X → (?X → ?Y) → Measure ?Y")` → finds Measure.map (type pattern)


## Learning and Memory

Project-specific patterns, useful Mathlib APIs, and pitfalls are stored in **memory files** at `.claude/memory/` (git-tracked, not in this document). Memory persists across sessions and machines.

Memory files:
- `.claude/memory/proof-patterns.md` — Tactics and strategies for recurring proof shapes
- `.claude/memory/mathlib-api.md` — Useful Mathlib lemmas/APIs discovered during work
- `.claude/memory/pitfalls.md` — Things that look like they should work but don't

Rules:
- **Before starting proof work**: Consult `proof-patterns.md` and `pitfalls.md` for relevant strategies.
- **After completing a tricky proof**: Proactively save reusable strategies to memory:
  - New tactic pattern or proof shape? → `proof-patterns.md`
  - Discovered a useful Mathlib lemma? → `mathlib-api.md`
  - Hit a surprising failure or gotcha? → `pitfalls.md`
- **Keep entries concise**: include the pattern, a code snippet, and a one-line explanation of when to use it.
- **Don't save trivial things**: only patterns that were non-obvious or took multiple attempts to discover.
