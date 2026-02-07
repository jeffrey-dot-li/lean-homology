# Addendum: search-mathlib

Project-specific corrections and tips for the `lean4-theorem-proving:search-mathlib` skill.

## Loogle Query Syntax

Loogle accepts several query forms, but **bare unquoted names silently return nothing**.

| Query form | Example | Notes |
|------------|---------|-------|
| Name substring | `"comm"`, `"ProjectiveResolution"` | **Must be in double quotes** |
| Exact constant | `Real.sin`, `List.map` | Fully qualified, no quotes |
| Type pattern | `(?a → ?b) → List ?a → List ?b` | `?` for metavariables, `_` for wildcards |
| Subexpression | `_ * (_ ^ _)` | Wildcards match any term |
| Goal pattern | `|- _ < _ → _ + 1 < _ + 1` | Prefix with `|-` |

### Common mistakes

- `lean_loogle(query="ProjectiveResolution")` → **no results** (bare name)
- `lean_loogle(query="\"ProjectiveResolution\"")` → finds it (quoted substring)
- `lean_loogle(query="Measure.map")` → **no results** (unquoted partial name)
- `lean_loogle(query="\"Measure.map\"")` → finds it
- `lean_loogle(query="Measure ?X → (?X → ?Y) → Measure ?Y")` → finds Measure.map (type pattern)
