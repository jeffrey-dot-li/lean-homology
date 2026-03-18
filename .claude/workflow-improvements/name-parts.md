# `name_parts` — pattern-match goal structure and bind names

**Status**: Idea
**Effort**: Medium (~80-120 lines tactic elaborator)
**Motivation**: `singularChain_chainHomotopy_of_homotopy` in `HomotopyInvariance2.lean`

## Problem

When the goal is a huge expression like `A = B + C + D` where each of `A`, `B`, `C`, `D` is a 5-line morphism composition, you want to name the parts so you can reason about the *structure* without drowning in the *content*.

Current Lean tools all fail at this:

| Tool | Problem |
|------|---------|
| `set A := <expr>` | Have to type out the full expression — impractical for 5-line terms with hidden proof witnesses (`⋯`) |
| `have`/`suffices` | Same re-elaboration problem — Lean may not reconstruct what's in the goal |
| `refine ?_ = ?_ + ?_` | Metavariables become new *goals*, not named context variables |
| `generalize` | Replaces a subexpr with a fresh var, but you must *specify* the subexpr (same typing problem) |
| `conv` | Navigates *into* expressions, but doesn't give names to chunks |

The fundamental issue: **you can see the structure in the infoview, but you can't name its parts without re-typing them.**

## Proposed tactic

```lean
name_parts ?A = ?B + ?C + ?D
-- Context gains:
-- A : X ⟶ Y := (the LHS expression)
-- B : X ⟶ Y := (first summand)
-- C : X ⟶ Y := (second summand)
-- D : X ⟶ Y := (third summand)
-- Goal becomes: A = B + C + D
```

You describe only the *skeleton* (`?A = ?B + ?C + ?D`), and Lean fills in the flesh from the actual goal.

## Experimental validation

Tested at line 550 of `HomotopyInvariance2.lean`:

| Attempt | Result |
|---------|--------|
| `refine ?_ = ?_ + ?_ + ?_` | **Fails** — `HAdd` instance stuck, metavariable types unconstrained |
| `refine (?_ : _ ⟶ _) = ...` | **Fails** — `Quiver` instance stuck, category unknown |
| `change _ = _ + _ + _` | **Succeeds** — proves unification *can* work, but doesn't bind names |

Key finding: `change` proves the unification succeeds. The missing piece is capturing the matched subexpressions as context variables.

## Implementation

The tactic would:

1. Parse the pattern (a `term` with named holes like `?A`, `?B`)
2. Elaborate the pattern against the goal type (same mechanism as `change` — it works, as demonstrated)
3. For each named metavariable, read off what it was assigned to by unification
4. Introduce a `let` binding for each (`Lean.MVarId.define`), like `set` does internally
5. Fold the goal to use the new names

Step 2 is the key: `change _ = _ + _ + _` already does this successfully, proving the unification is strong enough. The tactic just adds steps 3-5.

## Design considerations

- **Associativity**: `a + b + c` is `(a + b) + c`, so `?B + ?C + ?D` matches `B = a + b, C = c, D = ???` (fails). Need to write `(?B + ?C) + ?D` or handle associativity-aware matching.
- **Typeclass resolution**: The `change`-style elaboration resolves typeclasses from the goal's type, avoiding the stuck-instance problem that bare `refine` hits.
- **Folding**: Since expressions are extracted *from* the goal (not re-elaborated from user input), the folding problem that plagues `set` largely disappears.
- **Depth**: Should named holes be greedy or lazy? E.g., does `?A ≫ ?B` in `a ≫ b ≫ c ≫ d` give `A = a, B = b ≫ c ≫ d` or try to match more `≫`s? Default should be greedy (match the entire remaining expression).

## Relation to "don't write giant `have`"

This is the same principle. The reason `have h : giant_expr = other_thing` is painful isn't the logic — it's the *re-elaboration*. The goal already contains the expression in fully elaborated form. Writing a `have` asks you to re-elaborate it from scratch, and any tiny mismatch (universe, implicit, proof witness, notation) causes failure. `name_parts` sidesteps this entirely — you never re-elaborate anything.
