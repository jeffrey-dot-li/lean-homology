/-
  The Additivity Axiom for singular homology.

  Singular homology sends coproducts (disjoint unions) to products:
    H_n(∐_α X_α; R) ≅ ∏_α H_n(X_α; R)

  The key geometric fact is that the standard simplex Δⁿ is path-connected,
  so any singular simplex Δⁿ → ∐_α X_α must land entirely in one summand X_α.
  This gives a decomposition of the singular chain complex:
    C_*(∐_α X_α) ≅ ⊕_α C_*(X_α)
  from which the homology result follows.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Connected.Clopen
import Mathlib.Algebra.Homology.HomologicalComplexLimits

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u v

variable (C : Type u) [Category.{v} C] [HasCoproducts C] [Preadditive C]
  [CategoryWithHomology C]

namespace HomologyLean.SingularHomology

variable {ι : Type v} (X : ι → TopCat.{v})

/-! ## Geometric decomposition of singular simplices

The standard simplex `Δⁿ` is path-connected (and hence connected), so any
continuous map `Δⁿ → ∐_α X_α` must factor through a single summand `X_α`.
This is the key geometric input for the additivity axiom. -/

/-- A continuous map from a connected space to a sigma type factors through
one component. This is `Continuous.exists_lift_sigma` specialized to our setting.

For singular homology, we apply this with `α = toTop.obj [n]` (the standard
n-simplex), which is path-connected and hence connected. -/
theorem singular_simplex_factors_through_summand
    (n : SimplexCategory) (σ : SimplexCategory.toTop.obj n ⟶ TopCat.of ((i : ι) × (X i))) :
    ∃ (i : ι) (τ : SimplexCategory.toTop.obj n ⟶ X i),
      σ = τ ≫ TopCat.sigmaι X i := by
  sorry

/-! ## Chain complex decomposition

The singular chain complex of a coproduct decomposes as a coproduct of
chain complexes:
  C_*(∐_α X_α; R) ≅ ∐_α C_*(X_α; R)

This follows from the geometric decomposition: since each singular simplex
lands in exactly one summand, the free module on the set of singular simplices
decomposes accordingly. -/

/-- The singular chain complex of a coproduct is isomorphic to the coproduct
of the singular chain complexes.

**Proof sketch** (sorry'd): The geometric decomposition
`singular_simplex_factors_through_summand` shows that the set of n-simplices
of `∐_α X_α` is the disjoint union of the sets of n-simplices of each `X_α`.
Applying the free R-module functor (which preserves coproducts) gives the
degreewise isomorphism. The boundary maps are compatible because they are
defined by precomposition with face/degeneracy maps. -/
def singularChainComplex_coprod_iso (R : C) :
    ((singularChainComplexFunctor C).obj R).obj (∐ X) ≅
      ∐ (fun i => ((singularChainComplexFunctor C).obj R).obj (X i)) := by
  sorry

/-- The inclusion of each summand into the coproduct of chain complexes
corresponds to the chain map induced by the coproduct inclusion `X_i → ∐_α X_α`.

This expresses naturality of the isomorphism `singularChainComplex_coprod_iso`
with respect to the coproduct inclusions. -/
theorem singularChainComplex_coprod_iso_ι (R : C) (i : ι) :
    ((singularChainComplexFunctor C).obj R).map (Sigma.ι X i) =
      Sigma.ι (fun j => ((singularChainComplexFunctor C).obj R).obj (X j)) i ≫
        (singularChainComplex_coprod_iso C X R).inv := by
  sorry

/-! ## Homology of coproducts

From the chain complex decomposition, we derive that homology sends
coproducts to coproducts (and in abelian categories, finite coproducts
coincide with finite products). -/

/-- Singular homology sends coproducts to coproducts:
  H_n(∐_α X_α; R) ≅ ∐_α H_n(X_α; R)

This follows by applying the homology functor to the chain complex
isomorphism `singularChainComplex_coprod_iso`. -/
def singularHomology_coprod_iso (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (∐ X) ≅
      ∐ (fun i => ((singularHomologyFunctor C n).obj R).obj (X i)) := by
  sorry

/-- The homology isomorphism is natural with respect to the coproduct inclusions:
the following diagram commutes:
```
  H_n(X_i; R) ──ι──→ ∐_α H_n(X_α; R)
       |                    |
    id |                    | (singularHomology_coprod_iso).inv
       ↓                    ↓
  H_n(X_i; R) ─(ι_i)_*─→ H_n(∐_α X_α; R)
``` -/
theorem singularHomology_coprod_iso_ι (R : C) (n : ℕ) (i : ι) :
    ((singularHomologyFunctor C n).obj R).map (Sigma.ι X i) =
      Sigma.ι (fun j => ((singularHomologyFunctor C n).obj R).obj (X j)) i ≫
        (singularHomology_coprod_iso C X R n).inv := by
  sorry

end HomologyLean.SingularHomology
