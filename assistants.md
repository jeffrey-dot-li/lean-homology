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
Find whether a theorem/concept exists in Mathlib and locate building blocks for a new theorem. Full procedure: `.claude/skills/research/SKILL.md`.

### Mode 2: Draft (`/draft`)
Draft sorry'd theorem/lemma structure from a proof sketch. **Not the builtin `/plan`** — writes actual Lean code directly. Full procedure: `.claude/skills/draft/SKILL.md`.

### Mode 3: Fill Sorry (`/fill-sorry`)
Prove a specific sorry'd lemma iteratively using LSP tools. Before starting, read `.claude/memory/proof-strategies.md`. Full procedure: `.claude/skills/fill-sorry/SKILL.md`.

### Mode 4: Interactive (`/interactive`)
Work through a proof one step at a time, user-directed. The agent executes exactly what the user asks, shows the goal state, and waits. Full procedure: `.claude/skills/interactive/SKILL.md`.

### Mode 5: Refactor (`/refactor`)
Improve an existing working proof for brevity, clarity, or documentation. Full procedure: `.claude/skills/refactor/SKILL.md`.

### Mode 6: Discuss (`/discuss`)
Read and discuss proofs or math concepts. **No file edits.** Full procedure: `.claude/skills/discuss/SKILL.md`.

### Mode 7: Improve Workflow (`/improve-workflow`)
Improve the Claude Code setup — instructions, skills, memory, conventions. **All config must be git-tracked** (store under the repo, not `~/.claude/`). Full procedure: `.claude/skills/improve-workflow/SKILL.md`.

## Lean Conventions

### Proof philosophy: decompose, then compose

Complex proofs should be structured as **compositions of obvious, standalone lemmas** that can each be proved independently. Concretely:

- **Extract general subgoals as lemmas.** If a subgoal involves only general types (no proof-specific local context), it should be a standalone lemma with a clear name — not proved inline. Sorry it first, finish the main proof assuming it, then fill it separately.
- **Main proofs should be plumbing.** The top-level proof of a complex theorem should mostly be `rw`, `simp`, `exact`, `apply` — composing named lemmas. If a step needs >5 lines of non-trivial tactics, a lemma is probably missing.
- **Name things for reuse.** A well-named lemma (e.g., `TopCat.sigmaι_cancel`) is a tool in the toolkit. Inline reasoning is disposable. Prefer building tools over solving problems ad hoc.
- **This applies in every mode.** `/draft` does the decomposition upfront. `/fill-sorry` should recognize when extraction is needed mid-proof. `/refactor` should extract inline reasoning into named lemmas.

### Comments: explain *what* + *why* for non-obvious steps

Don't narrate obvious code. But **do** add a comment whenever a tactic step is non-obvious or a workaround. The comment must explain **both**:
1. **What** the rewrite/tactic achieves — describe it mathematically, showing the before → after transformation. Write it so someone unfamiliar with the proof's helper lemma names can follow.
2. **Why** it's done this way (if non-obvious) — e.g., why the obvious tactic doesn't work.

Example:

```lean
-- Rewrite δᵢ(simplexProdMap μ) ↦ simplexProdMap(μ ∘ δᵢ) — the face map acts on a
-- shuffle simplex by precomposition, absorbing it into the OrderHom.
-- simp_rw can't match under the ∑ binders; drill down with conv + erw instead.
conv_lhs =>
  enter [2, x]; enter [2]; enter [2, x_1]; enter [2]
  erw [δ_cast_simplexProdMap hrel]
```

This is especially important for `conv` blocks, `erw` instead of `rw`, `convert`, universe workarounds, and anything involving casts or `eqToHom`.

### `lemma` vs `theorem`

In Lean 4 + Mathlib, `lemma` is a macro that expands to `theorem` — no semantic difference. Use the keyword to signal the result's role:

- **`theorem`** — main results, the "point" of a file or section (e.g., `fundamentalGroup_circle_eq_int`)
- **`lemma`** — supporting/auxiliary results that exist to serve a theorem (e.g., `liftPath_loop_endpoint_eq_int_mul_two_pi`)

When in doubt, use `lemma`. Reserve `theorem` for results a reader would want to find by scanning the file.

## General Operating Rules

1. **At the start of every session**: Read `.claude/memory/proof-strategies.md` and `.claude/memory/MEMORY.md`. Then `rg` the `.claude/memory/api/` folder for concepts relevant to the current task and read matching sections.
2. **Always** verify the proof of a lemma or theorem upon completion before moving onto the next one.
3. Use `lean_diagnostic_messages` to check for errors after writing/editing proofs.
4. Use `lean_goal` to inspect proof states at specific positions.
5. Follow modal behavior rules: stay in the active mode, ask before switching.

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

### 0. First step in any Lean task: verify Lean MCP is available (MANDATORY)

First, make a trivial Lean MCP call (e.g. `lean_diagnostic_messages` on the target file) to confirm `lean-lsp` is reachable. If it fails, **say so explicitly** and suggest checking `.mcp.json` / restarting MCP or the editor; **do not** fall back to `lake env lean`/`lake build` unless the user explicitly asks.

### 1. Understanding Proof States

**`lean_goal`**: View proof goals at a specific position
- Omit `column` to see `goals_before` and `goals_after` at line start/end
- Use this to understand what tactic transformations are needed
- "no goals" means the proof is complete at that point
- **MOST IMPORTANT TOOL** - use frequently!

**`lean_diagnostic_messages`**: Get compiler errors and warnings
- Filter by line range to focus on specific proof sections
- **Use `severity` to filter**: `"error"`, `"warning"`, `"info"`, or `"hint"`. Omit for all levels.
  - **During proof filling** (`/fill-sorry`, `/interactive`, `/draft`): use `severity="error"` — you only care whether it compiles. Warnings and infos (linter, "Try this") are noise that bloats context.
  - **During refactoring** (`/refactor`): omit `severity` or use `severity="warning"` — you want lint-clean output too.
  - **For "Try this" suggestions**: use `severity="info"` after `simp?`/`exact?`/`apply?`/`decide?` to retrieve suggestions without the warning clutter. Also useful for reading `#check`/`#print`/`#eval`/`#print axioms` output, which are all info-level.
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

Project-specific patterns, useful Mathlib APIs, and gotchas are stored in **memory files** at `.claude/memory/` (git-tracked, not in this document). Memory persists across sessions and machines.

Memory files (see `.claude/memory/MEMORY.md` for the full index):
- `.claude/memory/proof-strategies.md` — General tactic patterns, goal state discipline, Lean gotchas
- `.claude/memory/api/` — API-specific proof patterns, pitfalls, and useful lemmas, one file per subsystem

Rules:
- **Before starting proof work**: Read `proof-strategies.md` and `MEMORY.md`. Then `rg` the `api/` folder for concepts relevant to the task and read matching sections.
- **After completing a tricky proof**: Proactively save reusable strategies to memory:
  - New general tactic pattern or Lean gotcha? → `proof-strategies.md`
  - API-specific proof pattern, pitfall, or useful lemma? → appropriate `api/` file (create a new one if no file fits)
- **Keep entries concise**: include the pattern, a code snippet, and a one-line explanation of when to use it.
- **Don't save trivial things**: only patterns that were non-obvious or took multiple attempts to discover.
