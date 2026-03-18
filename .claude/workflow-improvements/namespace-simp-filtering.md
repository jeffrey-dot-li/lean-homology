# Namespace-level simp filtering

**Status**: Idea (long-term)
**Effort**: Medium–Large (~100-200 lines metaprogramming for pre-filter, or ~50-80 for post-filter)
**Motivation**: `singularChain_chainHomotopy_of_homotopy` in `HomotopyInvariance2.lean`

## Core insight

The real issue isn't "which 25 lemmas do I want" — it's "which *level of abstraction* should simp stop at." Lean namespaces naturally mirror the mathematical abstraction stack:

```
Int.*, Units.*, Preadditive.*, Linear.*      ← always simplify (scalar/algebraic cleanup)
MonoidalCategory.*, Category.*               ← always simplify (categorical plumbing)
────────────── abstraction floor ──────────────
HomologicalComplex.*, SimplexCategory.*       ← stop here (domain-specific structure)
TopCat.*, SSet.*, SCF.*                       ← never unfold (concrete internals)
```

## Why namespaces are the right granularity

- Namespaces in Lean/Mathlib tend to capture mathematical abstraction levels
- New Mathlib `@[simp]` lemmas automatically land in the right bucket (no manual curation)
- You only need to manually curate **corner cases** — e.g., a lemma in `Category` that you *don't* want, or one in `HomologicalComplex` that you *do*
- Different proofs need different abstraction floors — `hBoundary₀` wants to unfold `SimplexCategory` stuff (computing with `δ 0`, `δ 1`), while the Leibniz cleanup wants to stay at the preadditive/monoidal level

## Hypothetical syntax

```lean
simp (floor := MonoidalCategory)    -- unfold everything above monoidal level
simp (floor := SimplexCategory)     -- unfold down to simplex level but no further
simp (floor := TopCat)              -- go all the way down to carrier sets
```

## Implementation approaches

### Approach A: Post-filter `simp?` output (simplest, build first)

The actual interactive workflow is: run `simp?`, get the "Try this" suggestion with 20 lemmas, mentally remove the ones that unfold too far, paste back the filtered list. This is completely mechanical — just string processing on lemma names.

Options:
1. **Editor script/keybinding**: Take a `simp only [...]` line, filter out names matching a blocklist of prefixes, output the cleaned version. No Lean metaprogramming needed at all.
2. **Custom tactic `hsimp?`**: A tactic elaborator that calls the same `simp` internals as `simp?`, gets back the list of used lemmas (already exposed — that's how `simp?` works), filters by namespace, and emits a modified "Try this" suggestion. ~50-80 lines of metaprogramming.

### Approach B: Pre-filter the simp set (cleaner, harder)

Build a filtered `SimpTheorems` before running simp:
```
get global SimpTheorems → drop entries whose origin matches blocklist → run simp with filtered set
```

The hard part: `SimpTheorems` uses discrimination trees indexed by **head symbol** (the outermost function of the LHS, e.g., `CategoryStruct.comp` for `f ≫ g`), not by lemma origin. Entries from different namespaces are interleaved in the same tree buckets. You can't selectively remove entries without rebuilding the tree. ~100-200 lines of metaprogramming.

### Approach C: Upstream contribution

Propose namespace-filtering as a core `simp` feature to Mathlib/Lean. This is a general-purpose need — anyone working at a specific abstraction level benefits (algebraic geometry people don't want `TopCat` unfolding either).

## Recommended build order

1. **Now**: `@[chain_simp]` curated set — see [chain-simp.md](chain-simp.md)
2. **Soon**: `hsimp?` post-filter tactic (approach A.2 — moderate effort, high ergonomic payoff)
3. **Later**: Pre-filtered simp set (approach B) or upstream proposal (approach C)
