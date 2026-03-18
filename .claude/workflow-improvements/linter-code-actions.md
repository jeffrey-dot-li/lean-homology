# Linter code actions — auto-fix common warnings

**Status**: Idea
**Effort**: Small (~30-40 lines TypeScript per action, VS Code extension)
**Motivation**: Repetitive manual fixes during proof cleanup

## Problem

Several common linter warnings have completely mechanical fixes that you currently apply by hand. During cleanup passes (especially after `simp?` iteration), these pile up and waste time.

## Proposed code actions

### 1. Remove unused simp arguments

**Warning**: `This simp argument is unused: \`lemmaName\``

**Fix**: Parse the `simp only [...]` on the flagged line, remove the named lemma, clean up commas/whitespace.

Example:
```lean
-- Before (warning on `mul_one`):
simp only [Int.reduceNeg, mul_one, Linear.comp_smul]
-- After:
simp only [Int.reduceNeg, Linear.comp_smul]
```

### 2. Auto-wrap long lines

**Warning**: `This line exceeds the 100 character limit, please shorten it!`

**Fix**: Break the line at a natural split point. Rules by context:
- **`simp only [...]`**: Break after commas inside the bracket list, aligning continuation lines
- **Tactic arguments**: Break before keyword arguments or after commas
- **Term-mode expressions**: Break after `≫`, `⊗ₘ`, `+`, or other binary operators
- **General fallback**: Break at the last space before column 100

Example:
```lean
-- Before (>100 chars):
    simp only [Units.smul_def, Int.reduceNeg, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, smul_smul]
-- After:
    simp only [Units.smul_def, Int.reduceNeg, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one, smul_smul]
```

## Implementation

VS Code extension (or contribution to the existing Lean 4 extension):

1. Listen for diagnostics matching the target warning patterns
2. Register a Quick Fix code action on each diagnostic
3. Parse the relevant syntax, apply the mechanical transformation, produce a `WorkspaceEdit`

Each action is independent — can be built and shipped incrementally.
