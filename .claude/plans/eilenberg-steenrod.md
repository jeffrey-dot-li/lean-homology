# Plan: Eilenberg-Steenrod Axioms for Singular Homology

## Context

Mathlib's singular homology (`Mathlib.AlgebraicTopology.SingularHomology.Basic`) currently provides:
- `singularChainComplexFunctor` / `singularHomologyFunctor` — the functor definitions
- Computation for totally disconnected spaces (H_n = 0 for n > 0, H_0 ≅ ∐ R)

None of the 6 Eilenberg-Steenrod axioms beyond functoriality are formally proven. This plan drafts the sorry'd structure for all 6, organized into files under `HomologyLean/SingularHomology/`.

## Dependency Graph

```
Relative.lean ──────► LongExactSequence.lean
     │
     ▼
DimensionAxiom.lean   HomotopyInvariance.lean   Additivity.lean   Excision.lean
```

`Relative.lean` is the foundation — it defines relative singular homology, which is needed by the LES, excision, and other axioms.

## File Structure

### File 1: `HomologyLean/SingularHomology/Relative.lean`
**Goal**: Define relative singular chains and homology for a pair (X, A).

Key definitions (all sorry'd):
- `singularChainMap` — the chain map `C_*(A) → C_*(X)` induced by inclusion `A ↪ X`
  - Built from `singularChainComplexFunctor` applied to the subspace inclusion
- `relativeSingularChainComplex (X : TopCat) (A : TopCat) (i : A ⟶ X)` — quotient `C_*(X) / C_*(A)` as a chain complex
  - Uses the cokernel in the category of chain complexes (abelian category structure from `HomologicalComplexAbelian`)
- `relativeSingularHomology n` — H_n(X, A; R)
- `relativeSingularChainSES` — the SES `0 → C_*(A) → C_*(X) → C_*(X,A) → 0`
  - Mono follows from the chain map being degreewise mono (A ↪ X is mono in TopCat, singular set preserves mono, free abelian group on injective map is injective)

**Mathlib building blocks**:
- `singularChainComplexFunctor` — `.lake/packages/mathlib/.../SingularHomology/Basic.lean:42`
- `HomologicalComplex` is abelian when `C` is — `Mathlib.Algebra.Homology.HomologicalComplexAbelian`
- `ShortComplex.ShortExact` — `Mathlib.Algebra.Homology.ShortComplex.ShortExact`

**Difficulty**: Medium. The main challenge is showing the inclusion `C_*(A) → C_*(X)` is degreewise mono. This requires that `TopCat.toSSet` sends monos to degreewise monos, and that the chain complex functor preserves this.

### File 2: `HomologyLean/SingularHomology/DimensionAxiom.lean`
**Goal**: State and prove the dimension axiom: H_n(pt; R) = 0 for n > 0, H_0(pt; R) ≅ R.

Key declarations:
- `singularHomology_point_zero_iso` — `H_0(pt; R) ≅ R`
- `singularHomology_point_isZero` — `IsZero (H_n(pt; R))` for `n ≠ 0`

**Approach**: Specialize Mathlib's `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` and `singularHomologyFunctorZeroOfTotallyDisconnectedSpace` to a point (which is totally disconnected, and the coproduct over a singleton is R).

**Difficulty**: Easy. Essentially just specializing existing Mathlib results.

### File 3: `HomologyLean/SingularHomology/HomotopyInvariance.lean`
**Goal**: Homotopic maps induce equal maps on singular homology.

Key declarations:
- `singularChainPrismOperator (n : ℕ)` — the prism operator `P_n : C_n(X) → C_{n+1}(X × I)` decomposing Δⁿ × I into (n+1) simplices of dimension n+1
- `prismOperator_boundary` — `∂P + P∂ = (i₁)_* - (i₀)_*` where i₀, i₁ are the inclusions X → X × I
- `singularChain_chainHomotopy_of_homotopy` — given `H : ContinuousMap.Homotopy f g`, construct a chain homotopy between `C_*(f)` and `C_*(g)`
- `singularHomology_map_eq_of_homotopy` — `H_n(f) = H_n(g)` when `f ≃ g`

**Approach**: The prism operator is the core construction. For each n-simplex `σ : Δⁿ → X`, define `P(σ)` as the alternating sum of the (n+1) simplices obtained by "stretching" σ across X × I using the standard decomposition of Δⁿ × Δ¹ into (n+1)-simplices.

The decomposition of Δⁿ × Δ¹ uses the maps `Δⁿ⁺¹ → Δⁿ × Δ¹` indexed by `i ∈ {0,...,n}`, defined by:
```
v_j ↦ (v_j, 0)  for j ≤ i
v_j ↦ (v_{j-1}, 1)  for j > i
```

**Mathlib building blocks**:
- `TopCat.toSSetObjEquiv` — `.lake/packages/mathlib/.../SingularSet.lean:57`
- `stdSimplex` — the topological standard simplex
- `Homotopy.homologyMap_eq` — abstract chain homotopy → equal homology maps (already in Mathlib)
- `SimplexCategory.Hom` — order-preserving maps between `[n]`

**Difficulty**: Hard. The prism operator requires careful combinatorial/geometric work. The boundary formula `∂P + P∂ = i₁* - i₀*` is the main proof effort. However, once the chain homotopy is constructed, `Homotopy.homologyMap_eq` gives the result immediately.

### File 4: `HomologyLean/SingularHomology/LongExactSequence.lean`
**Goal**: The long exact sequence of a pair.

Key declarations:
- `relativeSingularChainSES_shortExact` — the SES `0 → C_*(A) → C_*(X) → C_*(X,A) → 0` is short exact
- `singularHomology_connectingMorphism` — the connecting homomorphism δ : H_n(X, A) → H_{n-1}(A)
- `singularHomology_LES` — the 6-term exact sequence
- `singularHomology_LES_exact` — exactness
- `singularHomology_LES_natural` — naturality of the LES with respect to maps of pairs

**Approach**: Apply `HomologicalComplex.HomologySequence.composableArrows₅_exact` to the SES of chain complexes from `Relative.lean`. This is the same pattern as the Tor LES in `TorLES.lean`.

**Mathlib building blocks**:
- `HomologicalComplex.HomologySequence.composableArrows₅_exact` — `.lake/packages/mathlib/.../HomologySequenceLemmas.lean`
- `ShortComplex.ShortExact.δ` — the connecting homomorphism
- `δ_naturality` — naturality of connecting homomorphism

**Difficulty**: Medium. The abstract machinery exists; the main work is setting up `Relative.lean` correctly and verifying the SES is short exact.

### File 5: `HomologyLean/SingularHomology/Excision.lean`
**Goal**: The excision theorem: if `closure(U) ⊆ interior(A)`, then the inclusion `(X \ U, A \ U) ↪ (X, A)` induces isomorphisms on relative homology.

Key declarations:
- `barycentricSubdivision (n : ℕ)` — the subdivision operator `Sd : C_n(X) → C_n(X)`
- `barycentricSubdivision_chainMap` — `Sd` is a chain map
- `barycentricSubdivision_homotopic_id` — `Sd` is chain homotopic to the identity
- `iterated_subdivision_small` — iterated subdivision makes chains small relative to an open cover
- `excision` — the excision isomorphism on relative homology

**Approach**: Classical barycentric subdivision proof. Sd replaces each n-simplex with (n+1)! smaller simplices. The key steps are:
1. Define Sd as a chain map on singular chains
2. Construct a chain homotopy T between Sd and id
3. Show iterated Sd makes chains U-small for any open cover U
4. Show the inclusion of small chains is a quasi-isomorphism
5. Deduce excision

**Difficulty**: Very hard. This is the most technically demanding axiom. The combinatorics of barycentric subdivision, the chain homotopy, and the smallness argument are all substantial. Consider decomposing into multiple helper files.

### File 6: `HomologyLean/SingularHomology/Additivity.lean`
**Goal**: Singular homology converts coproducts to products: `H_n(⊔_α X_α) ≅ ∏_α H_n(X_α)`.

Key declarations:
- `singularChainComplex_coprod_iso` — `C_*(⊔_α X_α) ≅ ⊕_α C_*(X_α)` (chains of a disjoint union decompose)
- `singularHomology_coprod_iso` — `H_n(⊔_α X_α) ≅ ∏_α H_n(X_α)`

**Approach**: A singular n-simplex `σ : Δⁿ → ⊔_α X_α` must land in a single component (since Δⁿ is connected). So the singular chain complex of the disjoint union decomposes as a direct sum. Homology commutes with direct sums.

**Mathlib building blocks**:
- `ConnectedSpace` for `stdSimplex`
- The singular set `TopCat.toSSet` — need to show it sends coproducts to "componentwise" simplicial sets
- Homology commutes with direct sums in abelian categories

**Difficulty**: Medium. The key geometric fact (Δⁿ is connected) should be available or easy to prove. The algebraic part (homology commutes with direct sums) may need the correct Mathlib API.

## Suggested Implementation Order

1. **DimensionAxiom.lean** — Easy warm-up, mostly specializing Mathlib
2. **Relative.lean** — Foundation for everything else
3. **LongExactSequence.lean** — Depends on Relative, uses existing abstract LES machinery
4. **Additivity.lean** — Independent, medium difficulty
5. **HomotopyInvariance.lean** — Hard, needs prism operator
6. **Excision.lean** — Very hard, needs barycentric subdivision

## Verification

After writing each file:
1. `lean_diagnostic_messages` to check all declarations compile (even with sorry)
2. Verify import structure is correct
3. Confirm no circular dependencies


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
