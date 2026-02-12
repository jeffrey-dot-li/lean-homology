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
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u v

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts C] [AB4 C]

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
  obtain ⟨i, g, hg, hfg⟩ := σ.hom'.continuous_toFun.exists_lift_sigma
  exact ⟨i, ⟨g, hg⟩, TopCat.ext (congr_fun hfg)⟩

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
-- The key step: the degree-n evaluation of the singular chain complex functor
-- preserves coproducts. This follows because:
-- 1. The standard simplex Δⁿ is connected, so Hom(Δⁿ, ∐X) ≃ Σᵢ Hom(Δⁿ, Xᵢ)
-- 2. sigmaConst.obj R (free R-module functor) is a left adjoint, hence preserves colimits
instance singularChainComplexFunctor_preservesCoproducts (R : C) :
    PreservesColimitsOfShape (Discrete ι) (((singularChainComplexFunctor C).obj R) :
      TopCat.{v} ⥤ ChainComplex C ℕ) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  sorry

def singularChainComplex_coprod_iso (R : C) :
    ((singularChainComplexFunctor C).obj R).obj (∐ X) ≅
      ∐ (fun i => ((singularChainComplexFunctor C).obj R).obj (X i)) :=
  PreservesCoproduct.iso ((singularChainComplexFunctor C).obj R) X

/-- The inclusion of each summand into the coproduct of chain complexes
corresponds to the chain map induced by the coproduct inclusion `X_i → ∐_α X_α`.

This expresses naturality of the isomorphism `singularChainComplex_coprod_iso`
with respect to the coproduct inclusions. -/
theorem singularChainComplex_coprod_iso_ι (R : C) (i : ι) :
    ((singularChainComplexFunctor C).obj R).map (Sigma.ι X i) =
      Sigma.ι (fun j => ((singularChainComplexFunctor C).obj R).obj (X j)) i ≫
        (singularChainComplex_coprod_iso C X R).inv := by
  rw [singularChainComplex_coprod_iso, PreservesCoproduct.inv_hom]
  exact (ι_comp_sigmaComparison _ _ i).symm

/-! ## Homology of coproducts

From the chain complex decomposition, we derive that homology sends
coproducts to coproducts (and in abelian categories, finite coproducts
coincide with finite products). -/

/-- Singular homology sends coproducts to coproducts:
  H_n(∐_α X_α; R) ≅ ∐_α H_n(X_α; R)

This follows by applying the homology functor to the chain complex
isomorphism `singularChainComplex_coprod_iso`. -/
-- The homology functor on chain complexes preserves coproducts.
-- This holds in AB4 categories (abelian with exact coproducts), which includes
-- Ab, ModuleCat R, and other common coefficient categories.
-- shortComplexFunctor preserves colimits (since it's built from eval at three degrees)
instance shortComplexFunctor_preservesCoproducts (n : ℕ) :
    PreservesColimitsOfShape (Discrete ι)
      (HomologicalComplex.shortComplexFunctor C (ComplexShape.down ℕ) n) :=
  ⟨fun {_K} => ⟨fun {_c} hc => ⟨ShortComplex.isColimitOfIsColimitπ _
    (isColimitOfPreserves (HomologicalComplex.eval C _ ((ComplexShape.down ℕ).prev n)) hc)
    (isColimitOfPreserves (HomologicalComplex.eval C _ n) hc)
    (isColimitOfPreserves (HomologicalComplex.eval C _ ((ComplexShape.down ℕ).next n)) hc)⟩⟩⟩

-- AB4 gives colim preserves finite limits, hence preserves homology
instance colim_preservesHomology :
    (colim (J := Discrete ι) (C := C)).PreservesHomology := by
  have : HasExactColimitsOfShape (Discrete ι) C := AB4OfSize.ofShape ι
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

instance shortComplexHomologyFunctor_preservesCoproducts :
    PreservesColimitsOfShape (Discrete ι) (ShortComplex.homologyFunctor C) := by
  constructor; intro K
  apply preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone K)
  let S := (ShortComplex.functorEquivalence (Discrete ι) C).inverse.obj K
  let h := S.mapHomologyIso (colim (J := Discrete ι) (C := C))
  let η : S.homology ≅ K ⋙ ShortComplex.homologyFunctor C :=
    NatIso.ofComponents
      (fun j => ((ShortComplex.homologyFunctorIso
        ((evaluation (Discrete ι) C).obj j)).app S).symm)
      (fun {j₁ j₂} f => by
        have hf : j₁ = j₂ := Discrete.ext (Discrete.eq_of_hom f)
        subst hf; simp)
  let ptIso : (ShortComplex.colimitCocone K).pt.homology ≅
      colimit (K ⋙ ShortComplex.homologyFunctor C) :=
    h ≪≫ colim.mapIso η
  refine IsColimit.ofIsoColimit
    (colimit.isColimit (K ⋙ ShortComplex.homologyFunctor C))
    (Cocones.ext ptIso.symm (fun j => ?_))
  simp only [Functor.mapCocone_ι_app]
  change colimit.ι (K ⋙ ShortComplex.homologyFunctor C) j ≫
    (h ≪≫ colim.mapIso η).inv =
    (ShortComplex.homologyFunctor C).map
      ((ShortComplex.colimitCocone K).ι.app j)
  rw [Iso.trans_inv, Functor.mapIso_inv,
    ← Category.assoc, colimit.ι_map, Category.assoc]
  rw [← cancel_mono h.hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  let α : (evaluation (Discrete ι) C).obj j ⟶ colim :=
    { app := fun F => colimit.ι F j
      naturality := fun _ _ φ => (colimit.ι_map φ (j := j)).symm }
  have key := NatTrans.app_homology α S
  rw [show colimit.ι S.homology j = α.app S.homology from rfl,
    key, ← Category.assoc, ← Category.assoc]
  have h1 : η.inv.app j =
      (S.mapHomologyIso
        ((evaluation (Discrete ι) C).obj j)).hom := by
    simp [η, NatIso.ofComponents, ShortComplex.homologyFunctorIso]
  rw [h1, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
  have h2 : S.mapNatTrans α =
      (ShortComplex.colimitCocone K).ι.app j := by
    ext <;> simp [S, α, ShortComplex.colimitCocone,
      ShortComplex.functorEquivalence]
  rw [h2]; simp only [ShortComplex.homologyFunctor_map]; rfl

-- The homology functor ≅ shortComplexFunctor ⋙ ShortComplex.homologyFunctor,
-- so it preserves coproducts by composition + transfer via natural isomorphism.
instance homologyFunctor_preservesCoproducts (n : ℕ) :
    PreservesColimitsOfShape (Discrete ι)
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n) :=
  preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso C (ComplexShape.down ℕ) n).symm

def singularHomology_coprod_iso (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (∐ X) ≅
      ∐ (fun i => ((singularHomologyFunctor C n).obj R).obj (X i)) :=
  -- H_n(∐X) ≅ H_n(∐_i C_*(X_i)) via chain complex iso, then ≅ ∐_i H_n(X_i)
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).mapIso
    (singularChainComplex_coprod_iso C X R) ≪≫
    PreservesCoproduct.iso (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n)
      (fun i => ((singularChainComplexFunctor C).obj R).obj (X i))

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
  simp only [singularHomology_coprod_iso, Iso.trans_inv, PreservesCoproduct.inv_hom,
    Functor.mapIso_inv]
  change (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map
      (((singularChainComplexFunctor C).obj R).map (Sigma.ι X i)) =
    Sigma.ι (fun j => (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).obj
      (((singularChainComplexFunctor C).obj R).obj (X j))) i ≫
    (sigmaComparison (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n) fun i =>
      ((singularChainComplexFunctor C).obj R).obj (X i)) ≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map
      (singularChainComplex_coprod_iso C X R).inv
  rw [singularChainComplex_coprod_iso_ι, Functor.map_comp, ← Category.assoc,
    ι_comp_sigmaComparison]

end HomologyLean.SingularHomology
