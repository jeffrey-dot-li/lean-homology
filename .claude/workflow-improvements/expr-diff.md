# `#diff` / `diff_goals` — structural diff between expressions

**Status**: Idea
**Effort**: Medium (~60-80 lines core tree walk, plus formatting)
**Motivation**: `singularChain_chainHomotopy_of_homotopy` in `HomotopyInvariance2.lean`

## Problem

When two terms look identical in the infoview but aren't definitionally equal, finding the actual difference is extremely painful. The infoview fails because:

- **`⋯` hides differences**: Two different proof terms both print as `⋯`. The difference is literally invisible.
- **Long terms overflow**: When each term is 10+ lines, visual diffing is error-prone. You miss a `singChain` vs `SCF.obj` or `chainH` vs `SCF.map (homotopyMap H)` buried on line 7 of 12.
- **Implicit arguments**: Two terms can look identical in the infoview but differ in an implicit argument that's not displayed.

This was the root cause of the entire `abel` debugging session in this proof: `abel` couldn't cancel two terms that looked identical, and it took extensive investigation to discover they differed only in hidden proof witnesses.

## Proposed tool

### `#diff A B` (standalone command)

```lean
#diff A B
-- Infoview output:
-- A and B differ at 2 positions:
--
-- Position 1: argument 8 of HomologicalComplex.ιMapBifunctor
--   A: ⋯ : (n + 1) + 0 = n + 1    [proof: Nat.add_zero (n+1)]
--   B: ⋯ : (n + 1) + 0 = n + 1    [proof: ComplexShape.down_mk ...]
--   Same type: ✓ (use Subsingleton.elim)
--
-- Position 2: argument 3 of ...
--   A: SCF.map (homotopyMap H)
--   B: chainH
--   Same type: ✓ (definitionally equal, use rfl/dsimp)
```

### `diff_goals` (tactic, most common use case)

Diffs the LHS and RHS of an `=` goal directly — no need to name things first.

```lean
-- ⊢ big_expr_A = big_expr_B
diff_goals
-- Shows divergence points between LHS and RHS
```

### `diff_hyps h1 h2` (tactic)

Diffs the types (or values) of two hypotheses in context.

## Key features

1. **Structural diff**: Walk both `Expr` trees in parallel, report where they diverge
2. **Type comparison at divergence points**: Show whether divergent subexpressions have the same type (bridgeable via `Subsingleton.elim`, `congr`, or `dsimp`) or different types (real rewrite needed)
3. **Proof witness awareness**: Specifically flag when differences are `Prop`-valued — this is the most common case and the hardest to spot visually
4. **Path reporting**: Show where in the expression tree the difference is, so you know which `conv` path or `congr` argument to target
5. **Actionable suggestions**: "Same type ✓ → use `Subsingleton.elim`" or "Definitionally equal → use `dsimp`"

## Implementation

Purely a display tool — no tactic state modification:

1. Take two expressions (local context variables, or LHS/RHS of goal)
2. Call `Lean.Meta.isDefEq` first — if definitionally equal, report that
3. If not, recursively walk both `Expr` trees in parallel:
   - When they match (`Lean.Meta.isDefEq` on subexpressions), continue
   - When they diverge, record the path and both subexpressions
4. For each divergence point, check if the *types* are equal
5. For `Prop`-typed divergences, flag as proof witness mismatch
6. Format and display in the infoview

## Concrete example from this proof

At line 550, after `abel` cancelled the `-B + B` terms, the goal had `LHS_term` on the left and visually identical `LHS_term'` on the right. `diff_goals` would have immediately shown:

```
LHS and RHS differ at 1 position:

  argument 8 of HomologicalComplex.ιMapBifunctor:
    LHS: ⋯ : (ComplexShape.down ℕ).π ... = n + 1
    RHS: ⋯ : (ComplexShape.down ℕ).π ... = n + 1
    Same type: ✓ → use generalize_proofs + Subsingleton.elim
```

This would have saved the entire debugging session — straight to the fix in seconds instead of 30+ minutes of investigating `abel` internals.
