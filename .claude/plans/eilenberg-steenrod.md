# Plan: Eilenberg-Steenrod Axioms for Singular Homology

## Status: IN PROGRESS (3/6 files done)

## Completed Files

### 1. `HomologyLean/SingularHomology/DimensionAxiom.lean` ✅
- `singularHomology_point_isZero` — H_n(pt; R) = 0 for n ≠ 0
- `singularHomology_point_zero_iso` — H_0(pt; R) ≅ R
- **No sorry's.** Fully proven by specializing Mathlib's `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` and `coproductUniqueIso`.

### 2. `HomologyLean/SingularHomology/Relative.lean` ✅
- `singularChains` / `singularChainMap` — abbreviations for the Mathlib functors
- `relativeSingularChainComplex` — `cokernel` of the chain map `C_*(A) → C_*(X)`
- `relativeSingularHomology` — homology of the relative complex
- `relativeSingularChainSC` — the short complex `C_*(A) → C_*(X) → C_*(X,A)`
- `relativeSingularChainSC_exact` — exact via `exact_of_g_is_cokernel`
- `relativeSingularChainSES_shortExact` — short exact when `i` is mono
- `relativeSingularChainMap` — functoriality via `cokernel.map`
- **1 sorry:** `singularChainMap_mono` (mono inclusion ⟹ mono chain map). Needs: TopCat.toSSet preserves monos, free module functor preserves monos, alternating face map complex preserves degreewise monos.

### 3. `HomologyLean/SingularHomology/LongExactSequence.lean` ✅
- `connectingMorphism` — δ : H_n(X,A) → H_{n-1}(A) via `ShortExact.δ`
- `singularHomologyLES` — 6-term sequence via `composableArrows₅`
- `singularHomologyLES_exact` — exact via `composableArrows₅_exact`
- **1 sorry:** `connectingMorphism_natural` (naturality of δ w.r.t. maps of pairs). Should follow from `δ_naturality` in Mathlib.

## Remaining Files

### 4. `HomologyLean/SingularHomology/Additivity.lean` — NOT STARTED
**Goal**: `H_n(⊔_α X_α) ≅ ∏_α H_n(X_α)`

Key declarations needed:
- `singularChainComplex_coprod_iso` — `C_*(⊔_α X_α) ≅ ⊕_α C_*(X_α)`
- `singularHomology_coprod_iso` — `H_n(⊔_α X_α) ≅ ∏_α H_n(X_α)`

Key fact: Δⁿ is path-connected (instance exists: `SimplexCategory.instPathConnectedSpaceElemForallToTypeOrderHomFinHAddNatLenOfNatNNRealToTopObj`), so singular simplices into a coproduct land in a single component.

Mathlib building blocks:
- `TopCat.sigmaIsoSigma` — categorical coproduct ≅ Σ-type in TopCat
- `coproductUniqueIso` — coproduct over unique type ≅ object
- `HomologicalComplex.homologyMapIso` — homology of iso complexes

### 5. `HomologyLean/SingularHomology/HomotopyInvariance.lean` — NOT STARTED
**Goal**: Homotopic maps ⟹ equal maps on homology.

Key declarations needed:
- `singularChainPrismOperator` — P_n : C_n(X) → C_{n+1}(X × I)
- `prismOperator_boundary` — ∂P + P∂ = (i₁)_* - (i₀)_*
- `singularChain_chainHomotopy_of_homotopy` — chain homotopy from topological homotopy
- `singularHomology_map_eq_of_homotopy` — H_n(f) = H_n(g)

Mathlib building blocks:
- `TopCat.toSSetObjEquiv` — n-simplices ≃ C(Δⁿ, X)
- `SimplexCategory.toTop` — the cosimplicial topological simplex
- `Homotopy.homologyMap_eq` — abstract chain homotopy ⟹ equal homology maps (already in Mathlib)

**Difficulty**: Hard. The prism operator requires careful combinatorial/geometric work.

### 6. `HomologyLean/SingularHomology/Excision.lean` — NOT STARTED
**Goal**: Excision isomorphism on relative homology.

Key declarations needed:
- `barycentricSubdivision` — Sd : C_n(X) → C_n(X) chain map
- `barycentricSubdivision_homotopic_id` — Sd ≃ id via chain homotopy
- `iterated_subdivision_small` — iterated Sd makes chains small
- `excision` — the excision isomorphism

**Difficulty**: Very hard. Most technically demanding axiom.

## Key Lessons Learned

### Variable conventions
- The singular homology API uses `(C : Type u) [Category.{v} C] [HasCoproducts C] [Preadditive C] [CategoryWithHomology C]`.
- `[Abelian C]` does NOT imply `[HasCoproducts C]` — must add separately.
- For relative homology, also need `[Abelian C]` to get `HomologicalComplex C c` abelian (for cokernel existence).

### API patterns
- `singularChainComplexFunctor C` is a functor `C ⥤ TopCat ⥤ ChainComplex C ℕ`. Apply as `((singularChainComplexFunctor C).obj R).obj X` for chains, `.map i` for the induced chain map.
- Relative chain complex = `cokernel` of the chain map (works because `HomologicalComplex` is abelian).
- Exactness of `f → cokernel.π` is via `ShortComplex.exact_of_g_is_cokernel`.
- LES pattern: same as TorLES — apply `composableArrows₅_exact` to a `ShortExact` of chain complexes.
- Cokernel functoriality: `cokernel.map` takes a commutative square and produces a map between cokernels.
- For functor map composition: use `simp only [singularChainMap, ← Functor.map_comp, comm]` (not `rw` which can fail due to abbrev unfolding).

### Style
- Use `change` not `show` when the tactic changes the goal (linter enforces this).
- `point` defined as `TopCat.of PUnit` — PUnit is totally disconnected by `inferInstance`.
- `coproductUniqueIso` gives `∐ (fun _ : PUnit => R) ≅ R`.

## Dependency Graph

```
Relative.lean ──────► LongExactSequence.lean
     │
     ▼
DimensionAxiom.lean   HomotopyInvariance.lean   Additivity.lean   Excision.lean
```

Only LongExactSequence depends on Relative. The other 4 files are independent.

## Suggested Resume Order

1. **Additivity.lean** — next up, medium difficulty
2. **HomotopyInvariance.lean** — hard, needs prism operator
3. **Excision.lean** — very hard, needs barycentric subdivision
