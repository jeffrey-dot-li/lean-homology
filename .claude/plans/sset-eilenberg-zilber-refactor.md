# Plan: Generalize Eilenberg-Zilber from TopCat to SSet

## Goal

Refactor the Eilenberg-Zilber cross product construction so that the core lives at the
level of `SSet` (simplicial sets) rather than `TopCat`. The topological version becomes
a thin wrapper that precomposes with `TopCat.toSSet`.

**Current**: `eilenbergZilberNatTrans : singChainTensor ⟶ singChainProd` where both
functors are `TopCat × TopCat ⥤ ChainComplex C ℕ`.

**Target**: `SSet.eilenbergZilberNatTrans : SSet.singChainTensor ⟶ SSet.singChainProd`
where both functors are `SSet × SSet ⥤ ChainComplex C ℕ`, plus a derivation of the
`TopCat` version by whiskering with `TopCat.toSSet`.

## Motivation

1. The Eilenberg-Zilber map is fundamentally combinatorial — it depends only on shuffles
   (`OrderHom` data) and simplicial structure (face/degeneracy maps). No topology is involved.
2. Aligns with Mathlib's architecture: `singularChainComplexFunctor` is defined first on
   `SSet` (line 36 of `Basic.lean`), then the `TopCat` version precomposes with `toSSet` (line 42).
3. Eliminates `ULift` friction: `TopCat.toSSet` wraps everything in `ULift`, causing constant
   boilerplate (`SingularSimplex`, `singularSimplexEquivΔ`, `cast_ulift_toSSet_down`, etc.).
   Working directly in `SSet`, simplices are `SimplexCategory` morphisms via `stdSimplex.objEquiv`.
4. Products in `SSet` are computed levelwise (presheaf category), making them more transparent
   to `simp` and `rfl` than `TopCat` products (which go through limit machinery).

## Architecture Overview

```
Current:
  TopCat × TopCat ──eilenbergZilberNatTrans──▶ ChainComplex C ℕ

Target:
  SSet × SSet ──SSet.eilenbergZilberNatTrans──▶ ChainComplex C ℕ
       ▲
       │ TopCat.toSSet × TopCat.toSSet
       │
  TopCat × TopCat ──(derived)──▶ ChainComplex C ℕ
```

## Abbreviations and Notation

**Current file** uses:
- `SCF C : TopCat ⥤ ChainComplex C ℕ` = `(singularChainComplexFunctor C).obj (𝟙_ C)`
- `singChain C X` = `(SCF C).obj X` for `X : TopCat`
- `stdSimplex p : TopCat` = `SimplexCategory.toTop.obj [p]`
- `SingularSimplex X n` = `(TopCat.toSSet.obj X).obj (op [n])` (has `ULift`)

**New file** will use:
- `SSet.SCF C : SSet ⥤ ChainComplex C ℕ` = `(SSet.singularChainComplexFunctor C).obj (𝟙_ C)`
- `SSet.singChain C S` = `(SSet.SCF C).obj S` for `S : SSet`
- `Δ[p]` = `SSet.stdSimplex.obj [p]` (already in Mathlib)
- Simplices of `S` at level `n` = `S.obj (op [n])` (no `ULift`)

## Key Design Decision: Use `⊗` (monoidal tensor), not `⨯` (categorical product)

In `SSet`, the monoidal structure is cartesian (`CartesianMonoidalCategory SSet`), so
`⊗` and `⨯` are canonically isomorphic — but **not definitionally equal** (`rfl` fails
on `S ⊗ T = S ⨯ T`). They go through different limit cone constructions.

We use `⊗` throughout because:
1. `ProdStdSimplex.objEquiv` (Mathlib) identifies `(Δ[p] ⊗ Δ[q]) _⦋n⦌ ≃ (Fin (n+1) →o Fin (p+1) × Fin (q+1))` using `⊗`.
2. `SimplicialHomotopy.lean` (Mathlib) uses `X ⊗ Δ[1]` for homotopies.
3. `Monoidal.lean` provides simp lemmas (`tensorHom_app_apply`, etc.) for `⊗`.
4. Avoids needing an iso to bridge between `⊗` and `⨯` in every lemma.

This means `simplexProdMap` is replaced by `prodStdSimplex.objEquiv.symm` — no new
definition needed. The shuffle map `μ : Fin (r+1) →o Fin (p+1) × Fin (q+1)` maps
directly to an element of `(Δ[p] ⊗ Δ[q]) _⦋r⦌` via `objEquiv.symm`.

**Notation pitfall**: When both `MonoidalCategory C` (coefficient category) and
`MonoidalCategory SSet` are in scope, `⊗` is ambiguous. Use a local notation
`⊗ₛ` defined as `MonoidalCategory.tensorObj (C := SSet)` to disambiguate.

## What Changes vs What Stays

### Stays unchanged (in `Shuffle.lean`)
- `Shuffle p q`, `Shuffle.sign`, `Index`, all shuffle combinatorics
- These are pure `OrderHom`/`Fin` constructions, independent of both `TopCat` and `SSet`

### Stays unchanged (in `HomotopyMap.lean`)
- `homotopyMap`, `stdSimplex1_iso_I`, endpoint lemmas
- These are inherently topological (use `ContinuousMap.Homotopy`, unit interval)
- They become the bridge: `ContinuousMap.Homotopy → SSet.Homotopy`

### Needs rewriting (currently in `HomotopyInvariance.lean`)

Every definition/lemma currently parameterized by `X Y : TopCat` needs an `SSet` version.

## Detailed Steps

### Phase 1: SSet-level standard simplex maps

`simplexProdMap` is **not needed** — replaced by `prodStdSimplex.objEquiv.symm` from
Mathlib's `ProdStdSimplex.lean`. A shuffle `μ : Fin (r+1) →o Fin (p+1) × Fin (q+1)`
maps directly to `(Δ[p] ⊗ Δ[q]) _⦋r⦌` via `objEquiv.symm μ`.

| Current (TopCat) | New (SSet) | Notes |
|---|---|---|
| `simplexProdMap μ : Δ_top[r] ⟶ Δ_top[p] ⨯ Δ_top[q]` | `prodStdSimplex.objEquiv.symm μ : (Δ[p] ⊗ Δ[q]) _⦋r⦌` | Already in Mathlib, no new def needed |
| `simplexProdMap_comp` | `prodStdSimplex.objEquiv_naturality` or similar | Check what Mathlib provides |
| `δ_cast_simplexProdMap` | Should follow from `objEquiv_δ_apply` | Mathlib has `objEquiv_δ_apply` |
| `shuffleStdSimplexMap μ` | `prodStdSimplex.objEquiv.symm μ.toOrderHom` | Direct application |
| `insertLeftStep_comp_δ` | Derive from `objEquiv_δ_apply` + shuffle combinatorics | |
| `insertRightStep_comp_δ` | Derive from `objEquiv_δ_apply` + shuffle combinatorics | |
| `shuffleStdSimplexMap_insertLeft_face` | analogous | |
| `shuffleStdSimplexMap_insertRight_face` | analogous | |

**Key simplification**: The element `objEquiv.symm μ` lives in `(Δ[p] ⊗ Δ[q]) _⦋r⦌`
directly as data (a pair of simplices), not as a morphism. Face maps act by
`objEquiv_δ_apply`: `objEquiv ((Δ[p] ⊗ Δ[q]).δ i x) j = objEquiv x (i.succAbove j)`,
which is just precomposition with `succAbove` — pure combinatorics.

**No `ULift`, no `ConcreteCategory.comp_apply`, no `TopCat.toSSet` unfolding.**

### Phase 2: SSet-level cross product

Replace the simplex-level and chain-level cross products.

| Current | New | Notes |
|---|---|---|
| `SingularSimplex X n` | `S.obj (op [n])` | No dedicated type needed (no `ULift`) |
| `singularSimplexEquivΔ` | not needed | Simplices are already `SimplexCategory` morphisms via `objEquiv` |
| `SingularSimplex.ofΔ` / `⟪f⟫ₛ` | not needed | |
| `simplexCoprojection s` | `Sigma.ι _ s` | Direct coproduct inclusion |
| `prodSimplex s t` | `(s, t) : (S ⊗ T) _⦋n⦌` | Monoidal product is levelwise pairs |
| `shuffleSimplex s t μ` | `SSet.shuffleSimplex s t μ` | Apply `tensorHom` to shuffle element |
| `universalSimplexCrossProduct p q` | `SSet.universalSimplexCrossProduct p q` | Signed sum of coprojections |
| `simplexCrossProduct s t` | `SSet.simplexCrossProduct s t` | Universal version transported by `tensorHom` |
| `chainCrossProduct` | `SSet.chainCrossProduct` | Lift via `chainTensorHomEquiv` |

**Key difference**: The "singular simplex" type `SingularSimplex X n` (which is
`ULift (Δ_top[n] ⟶ X)`) becomes simply `S _⦋n⦌` — no wrapper. The
coprojection `simplexCoprojection` is just `Sigma.ι` directly.

Products use `⊗` (monoidal tensor), so `(S ⊗ T) _⦋n⦌ = S _⦋n⦌ × T _⦋n⦌` (levelwise
pairs). The `prodSimplex` construction becomes trivial: just `(s, t)`.

The chain group equivalence (`chainGroupIsoFree`, `chainTensorHomEquiv`) needs an
`SSet` version but should be structurally identical — `SSet.singularChainComplexFunctor`
builds chain groups as coproducts indexed by simplices, same as the `TopCat` version.

### Phase 3: SSet-level Leibniz rule and chain map

The Leibniz rule proofs (`chainCrossProduct_leibniz`, the edge cases) are the bulk of
the file (~800 lines). These proofs are mostly algebraic manipulations of signed sums
and coprojections — the `TopCat` vs `SSet` distinction matters mainly in:

1. How face maps act on simplices (via `δ_cast_simplexProdMap`)
2. How functoriality of `SCF C` is used

The proof *structure* should be identical. The individual steps should be shorter
because `SSet` face maps are definitional precomposition (vs going through `TopCat.toSSet`).

| Current | New |
|---|---|
| `universalSimplexCrossProduct_boundary` | `SSet.universalSimplexCrossProduct_boundary` |
| `simplexCrossProduct_boundary` | `SSet.simplexCrossProduct_boundary` |
| `chainCrossProduct_leibniz` | `SSet.chainCrossProduct_leibniz` |
| `chainCrossProduct_leibniz_right_zero` | `SSet.chainCrossProduct_leibniz_right_zero` |
| `chainCrossProduct_leibniz_left_zero` | `SSet.chainCrossProduct_leibniz_left_zero` |
| `eilenbergZilber` | `SSet.eilenbergZilber` |

### Phase 4: Naturality and natural transformation

| Current | New |
|---|---|
| `crossProduct_natural` | `SSet.crossProduct_natural` |
| `eilenbergZilber_natural` | `SSet.eilenbergZilber_natural` |
| `singChainTensor` | `SSet.singChainTensor : SSet × SSet ⥤ ChainComplex C ℕ` |
| `singChainProd` | `SSet.singChainProd : SSet × SSet ⥤ ChainComplex C ℕ` |
| `eilenbergZilberNatTrans` | `SSet.eilenbergZilberNatTrans` |

### Phase 5: Derive TopCat version

The topological Eilenberg-Zilber map is recovered by:

```lean
def eilenbergZilberNatTrans_TopCat :
    singChainTensor_TopCat ⟶ singChainProd_TopCat :=
  whiskerLeft (TopCat.toSSet.prod TopCat.toSSet) SSet.eilenbergZilberNatTrans
```

This requires showing that `TopCat.toSSet` interacts well with products:
- `TopCat.toSSet` preserves binary products, or at least there's a natural iso
  `toSSet.obj (X ⨯ Y) ≅ toSSet.obj X ⨯ toSSet.obj Y` in `SSet`
- This should already exist or be easy to construct since `toSSet` is a restricted
  Yoneda embedding and Yoneda preserves limits

### Phase 6: Recover homotopy invariance

The chain homotopy `singularChain_chainHomotopy_of_homotopy` currently goes:
```
ContinuousMap.Homotopy f g → chain homotopy on singChain C
```

The refactored version factors through:
1. `ContinuousMap.Homotopy f g → SSet.Homotopy (toSSet.map f) (toSSet.map g)`
   (bridge from topology to combinatorics — thin, in `HomotopyMap.lean`)
2. `SSet.Homotopy → SimplicialObject.Homotopy` (already in Mathlib: `toSimplicialHomotopy`)
3. `SimplicialObject.Homotopy → chain homotopy` (already in Mathlib: `ChainHomotopy.lean`)

Alternatively, the cross-product-with-interval approach can be done entirely in `SSet`:
- Build `SSet.eilenbergZilber` applied to `(S, Δ[1])` 
- Use the EZ map with `ι₀, ι₁ : Δ[0] → Δ[1]` to recover endpoints

This is a separate but related question of proof strategy.

## File Organization

**Option A**: New file `HomologyLean/SingularHomology/SSetEilenbergZilber.lean`
- Contains all `SSet`-level definitions and proofs
- `HomotopyInvariance.lean` imports it and derives the `TopCat` versions
- Cleanest separation

**Option B**: Refactor `HomotopyInvariance.lean` in-place
- Replace `TopCat` with `SSet` throughout
- Add `TopCat` derivations at the end
- Less file proliferation but messier during development

**Recommendation**: Option A. Create the new file, get it working, then thin out
`HomotopyInvariance.lean` to just the topological bridge + homotopy invariance theorem.

## Difficulty Estimate

| Phase | Difficulty | Estimated lines | Notes |
|-------|-----------|----------------|-------|
| Phase 1 (simplex maps) | Easy-Medium | ~150 | Mostly mechanical translation, should be shorter |
| Phase 2 (cross product) | Medium | ~250 | Chain group equivalences need care |
| Phase 3 (Leibniz rule) | Medium-Hard | ~600 | Bulk of the work, but proof structure is known |
| Phase 4 (naturality) | Easy | ~100 | Straightforward plumbing |
| Phase 5 (TopCat derivation) | Easy-Medium | ~50 | Depends on product preservation for `toSSet` |
| Phase 6 (homotopy invariance) | Medium | ~100 | May reuse Mathlib's `toSimplicialHomotopy` pipeline |

**Total**: ~1250 lines (vs current ~2200), plus ~100 lines of `TopCat` bridge.

The net reduction comes from eliminating `ULift` boilerplate, `ConcreteCategory` rewrites,
and `TopCat` limit machinery. The Leibniz proof structure is unchanged but each step
should be 20-30% shorter.

## Dependencies

- `Shuffle.lean` — unchanged, already pure combinatorics
- `SumInvolution.lean` — unchanged
- `Representable.lean` — check if it depends on `TopCat`; if so, may need `SSet` version
- `HomotopyMap.lean` — stays topological, becomes a thin bridge
- Mathlib imports: `SimplicialSet.StdSimplex`, `SimplicialSet.SimplicialHomotopy`,
  `SimplicialObject.ChainHomotopy`, `SingularHomology.Basic`

## Resolved Questions

1. **`⊗` vs `⨯` in SSet**: They are canonically isomorphic but **not** definitionally
   equal (`rfl` fails on `S ⊗ T = S ⨯ T`). **Decision**: use `⊗` throughout, since
   Mathlib's `ProdStdSimplex.lean` and `SimplicialHomotopy.lean` use `⊗`.

## Open Questions

1. **Does `TopCat.toSSet` interact well with `⊗`?** For Phase 5, we need either
   `toSSet.obj (X ⨯ Y) ≅ toSSet.obj X ⊗ toSSet.obj Y` or a natural comparison map.
   Since `toSSet` is a restricted Yoneda and `⊗` is the cartesian product in `SSet`,
   this should exist.

2. **Should the monoidal hypotheses change?** The current file has heavy monoidal
   prerequisites (`MonoidalCategory C`, `MonoidalClosed C`, etc.) for the
   `chainTensorHomEquiv` machinery. At the `SSet` level, the same machinery is needed
   to define `chainCrossProduct`, so the hypotheses likely stay the same.

3. **Can Phase 3 be simplified?** The Leibniz rule proof is ~800 lines. With `SSet`
   simplifications, is there a cleaner proof strategy? Possibly — the Mathlib
   `SimplicialObject.Homotopy` approach sidesteps the explicit Leibniz rule entirely
   by using the general `toChainHomotopy` construction. But our EZ map is a chain map
   (not a chain homotopy), so the Leibniz rule is still needed.

4. **Namespace**: Use `SSet.EilenbergZilber` or `HomologyLean.SSet.EilenbergZilber`?
   The former aligns with Mathlib style (`SSet.Homotopy`, `SSet.stdSimplex`).
