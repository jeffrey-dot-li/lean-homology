# Plan: Cross Product as a Chain Map

## Goal

Package the existing `chainCrossProduct` into a chain map:

```
crossProductChainMap : (singChain C X).tensorObj (singChain C Y) ⟶ singChain C (X ⨯ Y)
```

where `tensorObj` is Mathlib's tensor product of chain complexes (`Mathlib.Algebra.Homology.Monoidal`), with degree-`n` object `⨁_{p+q=n} C_p(X) ⊗ C_q(Y)`.

## What Exists

All in `HomotopyInvariance.lean`:

| Declaration | Line | Description |
|---|---|---|
| `chainCrossProduct` | 526 | `C_p(X) ⊗ C_q(Y) ⟶ C_n(X × Y)` for fixed `(p, q)` with `n = p + q` |
| `chainCrossProduct_leibniz` | 1471 | Leibniz rule for `(p+1, q+1)` — both indices ≥ 1 |
| `crossProduct_natural` | 913 | Naturality in `(X, Y)` |
| `chainCrossProduct_leibniz_left_zero_zero` | 1549 | Edge case: `(0, 1)` Leibniz rule |
| `simplexCrossProduct_zero_right` | 726 | Cross product with a 0-simplex on the right |
| `simplexCrossProduct_zero_left` | 793 | Cross product with a 0-simplex on the left |
| `curriedTensor_additive` | 1760 | Instance: `(curriedTensor C).Additive` |
| `hasCoproducts_zero_of_v` | 1765 | Instance: `HasCoproducts.{0} C` from `HasCoproducts.{v} C` |

With those two instances, `HasTensor (singChain C X) (singChain C Y)` synthesizes via `inferInstance`.

## Sign Conventions

For `ComplexShape.down ℕ` (from `ComplexShapeSigns.lean:155-164`):
- `π (p, q) = p + q`
- `ε₁ (p, q) = 1` — first differential has sign 1
- `ε₂ (p, q) = (-1)^p` — second differential has sign `(-1)^p`

The total differential on the `(p, q)` summand is: `d₁ ⊗ id + (-1)^p · id ⊗ d₂`.

This **matches** `chainCrossProduct_leibniz` exactly.

## Steps

### Step 1: Instances for `HasTensor` ✅ DONE

Two instances added:
1. `curriedTensor_additive` — from `MonoidalPreadditive.add_whiskerRight`
2. `hasCoproducts_zero_of_v` — resize `HasCoproducts.{v} C` to `HasCoproducts.{0} C`

Import added: `Mathlib.Algebra.Homology.Monoidal`.

### Step 2: Edge-case Leibniz rules

Prove for all `n`:

**`chainCrossProduct_leibniz_right_zero`**: `(p+1, 0)` case
```
chainCrossProduct(p+1, 0) ≫ d(p+1, p) =
  (d_X(p+1, p) ⊗ 𝟙) ≫ chainCrossProduct(p, 0)
```

**`chainCrossProduct_leibniz_left_zero`**: `(0, q+1)` case
```
chainCrossProduct(0, q+1) ≫ d(q+1, q) =
  (𝟙 ⊗ d_Y(q+1, q)) ≫ chainCrossProduct(0, q)
```

**Strategy**: These are simpler than the general Leibniz rule because there is a unique `(p+1, 0)`-shuffle and a unique `(0, q+1)`-shuffle, so no sign cancellation is needed.

- For `(p+1, 0)`: use `chainCrossProduct.ext` to reduce to simplex level, then `simplexCrossProduct_zero_right` on both sides. The boundary acts only on the first factor. The proof pattern is similar to `chainCrossProduct_leibniz_left_zero_zero` (line 1549) but generalized from `(0, 1)` to `(p+1, 0)`.

- For `(0, q+1)`: analogous via `simplexCrossProduct_zero_left`.

**Note**: `chainCrossProduct_leibniz_left_zero_zero` already proves the `(0, 1)` case of the left-zero rule. Consider whether to generalize it directly or prove the general case independently.

### Step 3: Define the chain map

```lean
noncomputable def crossProductChainMap (X Y : TopCat.{v}) :
    (singChain C X).tensorObj (singChain C Y) ⟶ singChain C (X ⨯ Y) where
  f n := HomologicalComplex.mapBifunctor.mapBifunctorDesc
    (fun p q (h : p + q = n) => chainCrossProduct (C := C) h)
  comm' n m hnm := by ...
```

The degree-`n` component is defined by the universal property of the coproduct: on the `(p, q)` summand with `p + q = n`, apply `chainCrossProduct`.

### Step 4: Prove the chain map condition

For `comm'`, need: `f n ≫ d_target = d_source ≫ f m` for `m + 1 = n`.

Use `mapBifunctor.hom_ext` to reduce to: for each `(p, q)` with `p + q = n`:
```
ι_{p,q} ≫ f n ≫ d_target = ι_{p,q} ≫ d_source ≫ f m
```

Since `n ≥ 1` and `p + q = n`, at least one of `p, q` is ≥ 1.

**Case A** (`p ≥ 1`, `q ≥ 1`): Write `p = p'+1, q = q'+1`. Dispatch to `chainCrossProduct_leibniz p' q'`.

**Case B** (`p ≥ 1`, `q = 0`): Write `p = p'+1`. Dispatch to `chainCrossProduct_leibniz_right_zero`.

**Case C** (`p = 0`, `q ≥ 1`): Write `q = q'+1`. Dispatch to `chainCrossProduct_leibniz_left_zero`.

The proof skeleton:
```lean
comm' n m hnm := by
  -- hnm : m + 1 = n (for ComplexShape.down ℕ)
  apply mapBifunctor.hom_ext
  intro p q hpq  -- hpq : p + q = n
  -- ι_{p,q} ≫ f n = chainCrossProduct(p, q)  by ι_mapBifunctorDesc
  -- ι_{p,q} ≫ d_source = d₁(p,q,m) + d₂(p,q,m)  by ι_D₁, ι_D₂
  -- d₁ uses ε₁ = 1, d₂ uses ε₂ = (-1)^p
  -- Case split on p, q and dispatch to appropriate Leibniz lemma
  sorry
```

**Key Mathlib API** for the `comm'` proof:
- `mapBifunctor.hom_ext` — extensionality on summands
- `mapBifunctor.ι_mapBifunctorDesc` — `ι ≫ desc f = f`
- `mapBifunctor.d_eq` — differential = `D₁ + D₂`
- `mapBifunctor.ι_D₁`, `mapBifunctor.ι_D₂` — inclusion composed with partial differentials
- `mapBifunctor.d₁_eq`, `mapBifunctor.d₂_eq` — expansion of `d₁`, `d₂` with signs

### Step 5 (optional): Naturality as natural transformation

Make the chain map functorial in `(X, Y)`, producing a natural transformation. This uses `crossProduct_natural` (line 913). Lower priority — the pointwise chain map is the main goal.

## Difficulty Estimate

| Step | Difficulty | Estimated effort |
|------|-----------|------------------|
| Step 1 (instances) | Easy | ✅ Done |
| Step 2 (edge Leibniz) | Medium | ~200 lines each, similar to `chainCrossProduct_leibniz_left_zero_zero` |
| Step 3 (define map) | Easy | ~10 lines |
| Step 4 (chain map condition) | Medium | ~50-100 lines of plumbing (case split + sign matching) |
| Step 5 (naturality) | Low priority | ~50 lines using `crossProduct_natural` |

The hardest part (general Leibniz with shuffle sign cancellation) is already done. Steps 2-4 are significantly easier.

## File Location

All in `HomologyLean/SingularHomology/HomotopyInvariance.lean`, after the existing chain homotopy section.
