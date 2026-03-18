# `name_parts` — pattern-match goal structure and bind names

**Status**: Implemented (v1), one known issue remaining
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
3. Collects named mvar assignments, filtering for fvars that are safe (present in the goal's local context).
4. Introduces `let` bindings via `MVarId.define` + `intro1P` (Phase 1).
5. Folds occurrences of each value with its new fvar via `kabstract` + `replaceTargetDefEq` (Phase 2, best-effort per binding).

### Key technical decisions

- **`inPattern := true`**: The `?name` syntax normally creates `syntheticOpaque` mvars. Under `inPattern`, they become `natural`, which allows `isDefEq` to assign them freely. Without this, two named holes under the same operator (e.g. `?A + ?B`) cause "typeclass instance problem is stuck" errors because the elaborator can't resolve `HAdd ?A ?B ?out` when both `?A` and `?B` are syntheticOpaque.

- **Safe binding filter**: After elaboration, some mvar assignments may reference fvars created internally by the elaborator (typeclass instances, etc.) that don't exist in the goal's local context. These are filtered out with `hasAnyFVar` before calling `define`.

- **Best-effort folding**: Phase 2 wraps each `kabstract`/`replaceTargetDefEq` in `try/catch`. If a particular binding can't be folded (e.g. complex expressions with proof terms), the let-binding still exists in the context — just the goal display won't show the name.

## Known issue: context pollution

**Bug**: The current implementation runs `Term.elabTermEnsuringType` directly in the tactic's `TermElabM` context (not sandboxed in `runTermElab`). This means typeclass resolution during pattern elaboration introduces fvars into the **goal's local context** — dozens of extra hypotheses like `inst✝⁴⁷`, `Y₂✝`, `c✝⁴`, etc. appear after `name_parts` runs.

**Why `runTermElab` was removed**: The sandboxed `runTermElab` created its own elaboration context. The matched values (mvar assignments) then contained fvars from that sandbox, causing "unknown free variable" errors when passed to `MVarId.define` on the real goal.

**Planned fix**: Re-introduce `runTermElab` for elaboration, but resolve the fvar issue by either:
- Abstracting matched values over sandbox-local fvars before `define`
- Using `Lean.Meta.abstractMVars` or `zetaReduce` to eliminate sandbox references
- Running elaboration in a temporary mvar context that shares the goal's lctx but isolates new fvars

This is the main remaining work item.

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
