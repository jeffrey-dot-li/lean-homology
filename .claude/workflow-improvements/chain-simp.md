# `@[chain_simp]` — curated simp extension for chain homotopy proofs

**Status**: Idea
**Effort**: Small (no metaprogramming, just `register_simp_attr` + tagging)
**Motivation**: `singularChain_chainHomotopy_of_homotopy` in `HomotopyInvariance2.lean`

## Problem

During interactive proof development, you want a "lightsaber" `simp` that:
- **Always** cleans up integer/unit scalar arithmetic (`(-1 • 1)^n → (-1)^n`, etc.)
- **Always** distributes preadditive operations through composition
- **Never** unfolds past the `SimplexCategory` / `TopCat` / `SSet` / `SCF` abstraction level

The default `simp` set fails on both counts: it misses domain-specific cleanup lemmas (requiring tedious `simp?` hunts) and includes lemmas like `SimplexCategory.toTop_obj`, `Functor.op_obj`, `yoneda_obj_obj` that blow the goal state down to carrier-set level.

## Current pain

Finding the right lemma set was the hardest part of the proof:

```lean
-- Took many iterations of simp? to find this:
simp only [Units.smul_def, Int.reduceNeg, Units.val_pow_eq_pow_val,
  Units.val_neg, Units.val_one, smul_smul, ← pow_add, ← two_mul,
  pow_mul, neg_one_pow_two, one_pow]

-- And this:
simp only [Int.reduceNeg, Int.zsmul_eq_mul, mul_one, Linear.comp_smul, right_eq_add]
```

These lemmas are "obvious" mathematically but scattered across Mathlib namespaces.

## Proposed solution

Define a `simp` extension `chain_simp` and tag ~25 lemmas:

**Sign/scalar cleanup:**
- `Int.reduceNeg`, `Int.zsmul_eq_mul`, `mul_one`, `one_mul`, `one_smul`
- `Units.smul_def`, `Units.val_pow_eq_pow_val`, `Units.val_neg`, `Units.val_one`
- `smul_smul`, `neg_one_pow_two`, `one_pow`, `pow_one`
- `← pow_add`, `← two_mul`, `pow_mul` (directional — may need `simp` lemma wrappers)

**Preadditive distributivity:**
- `Preadditive.comp_zsmul`, `Preadditive.zsmul_comp`
- `Preadditive.comp_add`, `Preadditive.add_comp`
- `Linear.comp_smul`

**Category plumbing:**
- `Category.assoc`
- `Iso.inv_hom_id_assoc`, `Iso.hom_inv_id_assoc`
- `MonoidalCategory.whiskerRight_id`, `MonoidalCategory.whisker_exchange_assoc`

**Equation manipulation:**
- `right_eq_add` (or `add_right_cancel_iff`)

## Usage pattern

```lean
-- During proving: use as workhorse (never unfolds too far)
simp only [chain_simp]

-- During cleanup: simp? shows which specific chain_simp lemmas fired
simp only [Int.reduceNeg, Linear.comp_smul, ...]
```

## Implementation

- Single file (e.g., `HomologyLean/Tactic/ChainSimp.lean`)
- `register_simp_attr chain_simp` to create the extension
- Tag each lemma with `attribute [chain_simp]` in a setup section
- Directional lemmas (`← pow_add`, `← two_mul`) need wrapper `@[chain_simp]` lemmas stated in the desired direction
- Grow the set iteratively as more proofs are done

## Design considerations

- Keep the set **stable and predictable** — only add lemmas that are universally useful in chain homotopy proofs, not proof-specific rewrites
- The set should be **confluent** — applying all lemmas in any order should reach the same normal form
- Consider splitting into sub-extensions if the set grows: `@[sign_simp]` for scalar cleanup, `@[preadditive_simp]` for distributivity
- `norm_num` handles ground terms (`(-1)^3 = -1`) but not symbolic ones (`(-1 • 1)^n`); this set fills that gap

## Relation to namespace-level simp filtering

This is the pragmatic short-term solution. See [namespace-simp-filtering.md](namespace-simp-filtering.md) for the ideal long-term approach that would largely supersede a curated list.
