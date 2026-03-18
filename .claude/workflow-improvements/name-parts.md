# `name_parts` — pattern-match goal structure and bind names

**Status**: Implemented (v2), context pollution fixed
**File**: `HomologyLean/Tactic/NameParts.lean` (~85 lines)
**Tests**: `HomologyLean/Tactic/NamePartsTest.lean`
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

## Tactic syntax

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

## Implementation summary

The tactic (in `NameParts.lean`):

1. Elaborates the pattern with `inPattern := true` so `?name` holes become **natural** metavariables (not `syntheticOpaque`). This is the key insight — natural mvars can be assigned by `isDefEq`, avoiding stuck typeclass issues.
2. Unifies the elaborated pattern against the goal type via `isDefEq`.
3. Collects named mvar assignments, filtering by mvar ID snapshot (only mvars created during our elaboration) and by fvar safety (values must only reference fvars in the goal's local context).
4. Introduces `let` bindings via `MVarId.define` + `intro1P` (Phase 1).
5. Folds occurrences of each value with its new fvar via `kabstract` + `replaceTargetDefEq` (Phase 2, best-effort per binding).

### Key technical decisions

- **`inPattern := true`**: The `?name` syntax normally creates `syntheticOpaque` mvars. Under `inPattern`, they become `natural`, which allows `isDefEq` to assign them freely. Without this, two named holes under the same operator (e.g. `?A + ?B`) cause "typeclass instance problem is stuck" errors because the elaborator can't resolve `HAdd ?A ?B ?out` when both `?A` and `?B` are syntheticOpaque.

- **Mvar ID snapshot**: Before elaboration, all existing `MVarId`s are collected into a `HashSet`. After elaboration, only mvars *not* in this set are considered. This prevents stale mvars from prior sub-proofs (which share the `MetavarContext`) from being picked up. The original approach of comparing `mvarCounter` was wrong because `MVarId.name.num` indices use a different counter than `MetavarContext.mvarCounter`.

- **Safe binding filter**: After elaboration, some mvar assignments may reference fvars created internally by the elaborator (typeclass instances, etc.) that don't exist in the goal's local context. These are filtered out with `hasAnyFVar` before calling `define`.

- **Best-effort folding**: Phase 2 wraps each `kabstract`/`replaceTargetDefEq` in `try/catch`. If a particular binding can't be folded (e.g. complex expressions with proof terms), the let-binding still exists in the context — just the goal display won't show the name.

## Fixed: context pollution (v2)

**Bug (v1)**: The original implementation used `mvarCounter` to filter which mvars were "new" (created by our elaboration). But `mvarCounter` is a sequential allocation counter, while `MVarId.name` uses `.num _ n` where `n` is a hygiene counter — a completely different numbering. This meant old mvars from prior sub-proofs (e.g. `apply prod.hom_ext`) passed the filter and got materialized as unwanted let-bindings.

**Fix**: Snapshot the full set of `MVarId`s before elaboration (`Std.HashSet MVarId`), then only collect mvars whose ID is *not* in the snapshot. This correctly excludes all pre-existing mvars regardless of their name encoding.

**Result**: In the regression test (`NamePartsTest.lean`), hypothesis count goes from 13 → 15 after `name_parts ?LHS = ?RHS` (exactly +2), where v1 produced 13 → 25 (+12 pollutants).

## What works today

- Basic patterns: `?LHS = ?RHS`, `?A + ?B = _`, `?P * ?Q = ?Z`, `?A ∧ ?B`
- Mixed named/anonymous holes: `?S = _` names only `S`
- Folding: goal displays the new names (verified with `guard_target` in tests)
- Real-world usage: works at the motivating location (`HomotopyInvariance2.lean:303`) — names `LHS`/`RHS`, `module` closes the goal through the let-bindings
- Subsequent `module`, `ring`, `abel`, `exact` tactics work through the let-bindings

## Design notes

- **Associativity**: `a + b + c` is `(a + b) + c`, so `?B + ?C + ?D` matches `B = a + b, C = c, D = ???` (fails). Need to write `(?B + ?C) + ?D` or handle associativity-aware matching.
- **Typeclass resolution**: The `inPattern := true` approach resolves typeclasses from the goal's type, avoiding the stuck-instance problem that bare `refine` hits.
- **Folding**: Since expressions are extracted *from* the goal (not re-elaborated from user input), the folding problem that plagues `set` largely disappears.
- **Depth**: Named holes are greedy — `?A ≫ ?B` in `a ≫ b ≫ c ≫ d` gives `A = a, B = b ≫ c ≫ d`.

## Relation to "don't write giant `have`"

This is the same principle. The reason `have h : giant_expr = other_thing` is painful isn't the logic — it's the *re-elaboration*. The goal already contains the expression in fully elaborated form. Writing a `have` asks you to re-elaborate it from scratch, and any tiny mismatch (universe, implicit, proof witness, notation) causes failure. `name_parts` sidesteps this entirely — you never re-elaborate anything.
