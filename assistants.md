# assistants.md

Guidance for Code Assistant Agents working in this repository.

## Project Overview

Lean 4 formalization of homotopy computations in algebraic topology.

## Terminal Settings

Commands use `fish` shell syntax.

## Operating Instructions

1. **Always** verify the proof of a lemma or theorem upon completion before moving onto the next one.
2. Use `lean_diagnostic_messages` to check for errors after writing/editing proofs.
3. Use `lean_goal` to inspect proof states at specific positions.

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

## Effective Proof Development Workflow

### Step 1: Start with Type Signatures and `sorry`

```lean
theorem my_theorem (x : X) : P x := by
  sorry
```

Verify the theorem statement compiles before attempting the proof.

### Step 2: Explore the Goal State

Use `lean_goal` at the `sorry` to understand what needs to be proven:
- What hypotheses are available?
- What is the goal structure?
- Are there obvious tactics to try?

### Step 3: Incremental Proof Development

1. **Try simple tactics first**: `rfl`, `simp`, `ring`, `norm_num`, `exact`
2. **Check goal after each tactic**: Use `lean_goal` after adding each line
3. **Use `lean_diagnostic_messages`** to catch errors immediately
4. **Use `lean_multi_attempt`** to test multiple approaches

### Step 4: Finding the Right Lemmas

**Decision tree**:
1. "Does X exist locally?" → `lean_local_search`
2. "I need a lemma that says X" → `lean_leansearch`
3. "Find lemma with type pattern" → `lean_loogle`
4. "What closes this goal?" → `lean_state_search`
5. "What to feed simp?" → `lean_hammer_premise`

After finding a name: verify with `lean_local_search`, then get details with `lean_hover_info`.

### Step 5: Verify and Move Forward

- Use `lean_diagnostic_messages` on the entire theorem
- Ensure no errors before proceeding to the next proof
- **Never leave a theorem without verifying it compiles**


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


## Project-Specific Patterns

### Working with Quotients

```lean
have h := Quotient.mk_out q          -- extract representative
exact Quotient.exact (some_equality)  -- quotient equality → relation
exact Quotient.sound (some_relation)  -- relation → quotient equality
```

### Working with Homotopies

```lean
-- Path.Homotopic ≈ ContinuousMap.HomotopyRel ... {0, 1}
refine ⟨{
  toFun := fun ⟨s, t⟩ => ...
  continuous_toFun := by continuity / fun_prop
  map_zero_left := by ...
  map_one_left := by ...
  prop' := by ...
}⟩
```

### Using Covering Maps

```lean
set lift := cov.liftPath γ e γ_0
have h_lifts := cov.liftPath_lifts γ e γ_0
have h_mono := cov.liftPath_apply_one_eq_of_homotopicRel h e₁ e₂
```
