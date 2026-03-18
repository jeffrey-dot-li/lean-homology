# `normalize_proofs` — automated proof witness unification

**Status**: Idea
**Effort**: Small (~50 lines tactic code, single file)
**Motivation**: `singularChain_chainHomotopy_of_homotopy` in `HomotopyInvariance2.lean`

## Problem

When `generalize_proofs` introduces named variables for hidden `⋯` proof witnesses, pairs with the same type signature (e.g., two proofs of `(ComplexShape.down ℕ).π ... (n + 1, 0) = n + 1`) block `abel`/`module` from recognizing syntactically identical terms. You have to manually identify the pairs and `rw [Subsingleton.elim pᵢ pⱼ]` each one.

## Current manual workflow

```lean
generalize_proofs _ _ _ _ _ p3 _ p2 _ _ _ p1 _ p0
rw [Subsingleton.elim p0 p3]
-- ... later ...
rw [Subsingleton.elim p1 p2]
```

## Proposed tactic

A single `normalize_proofs` that:

1. Runs `generalize_proofs` (naming all `Prop`-valued proof terms in the goal)
2. Scans the context for pairs of hypotheses with identical types where the type is a `Prop`
3. For each such pair, rewrites via `Subsingleton.elim` to unify them (canonical choice: keep the one with smaller index / earlier in context)

## Design considerations

- Should be a `Lean.Elab.Tactic` macro or elaborator (not a `simp` extension — this is a rewrite pass, not a simplification)
- Direction of rewrite: pick a canonical representative per type (e.g., first-introduced) and rewrite all others to it
- May want to expose a syntax variant `normalize_proofs at h` for hypotheses
- ~50 lines of tactic code, single file

## Where it helps

Every proof involving `HomologicalComplex.ιMapBifunctor`, `HomologicalComplex.mapBifunctor.d_eq`, `chainCrossProduct`, or any construction that carries degree-arithmetic proof obligations. These all generate `⋯` witnesses that differ only in proof term but agree in type.
