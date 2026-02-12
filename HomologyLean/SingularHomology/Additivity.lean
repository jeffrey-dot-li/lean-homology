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

def singular_simplex_factors_through_summand_psigma
    (n : SimplexCategory)
    (σ : SimplexCategory.toTop.obj n ⟶ TopCat.of ((i : ι) × (X i))) :
    Σ' (i : ι) (τ : SimplexCategory.toTop.obj n ⟶ X i),
      σ = τ ≫ TopCat.sigmaι X i := by
  classical
  -- your original existence proof
  have hx : ∃ (i : ι) (τ : SimplexCategory.toTop.obj n ⟶ X i),
      σ = τ ≫ TopCat.sigmaι X i :=
    singular_simplex_factors_through_summand (X := X) (n := n) σ
  -- choose i
  refine ⟨Classical.choose hx, ?_⟩
  -- now choose τ for that i
  have hxτ :
      ∃ (τ : SimplexCategory.toTop.obj n ⟶ X (Classical.choose hx)),
        σ = τ ≫ TopCat.sigmaι X (Classical.choose hx) :=
    Classical.choose_spec hx
  refine ⟨Classical.choose hxτ, ?_⟩
  -- and the equality
  exact Classical.choose_spec hxτ
/-! ## Chain complex decomposition

The singular chain complex of a coproduct decomposes as a coproduct of
chain complexes:
  C_*(∐_α X_α; R) ≅ ∐_α C_*(X_α; R)

This follows from the geometric decomposition: since each singular simplex
lands in exactly one summand, the free module on the set of singular simplices
decomposes accordingly. -/

-- sigmaConst.obj R (the free R-module functor) is a left adjoint,
-- hence preserves all colimits.
noncomputable instance sigmaConst_isLeftAdjoint (R : C) :
    (sigmaConst.obj R : Type v ⥤ C).IsLeftAdjoint :=
  ⟨_, ⟨sigmaConstAdj R⟩⟩

@[simp] lemma TopCat.sigmaι_apply (k : ι) (x : f k) :
  (TopCat.sigmaι f k) x = ⟨k, x⟩ := by rfl
@[simp] lemma TopCat.sigmaι_hom_apply (k : ι) (x : f k) :
    (TopCat.Hom.hom (TopCat.sigmaι f k)) x = ⟨k, x⟩ := rfl
-- The singular simplicial set functor evaluated at degree n
-- preserves coproducts because Δⁿ is connected:
-- Hom(Δⁿ, ∐X) ≃ Σᵢ Hom(Δⁿ, Xᵢ).
instance toSSet_eval_preservesCoproducts (n : ℕ) :
    PreservesColimitsOfShape (Discrete ι)
      (TopCat.toSSet.{v} ⋙ (evaluation SimplexCategoryᵒᵖ
        (Type v)).obj (Opposite.op
          (SimplexCategory.mk n))) := by
  let F := TopCat.toSSet.{v} ⋙ (evaluation SimplexCategoryᵒᵖ
    (Type v)).obj (Opposite.op (SimplexCategory.mk n))
  constructor; intro K
  let f : ι → TopCat.{v} := K.obj ∘ Discrete.mk
  haveI : PreservesColimit (Discrete.functor f) F := by
    apply preservesColimit_of_preserves_colimit_cocone (TopCat.sigmaCofanIsColimit f)
    refine ⟨fun s => ?_, fun s j => ?_, fun s m hm => ?_⟩
    · -- desc: F.obj (TopCat.of (Σ i, f i)) → s.pt
      intro x
      classical
      obtain ⟨i, t, ht⟩ := singular_simplex_factors_through_summand_psigma f
        (SimplexCategory.mk n) x.down
      exact s.ι.app ⟨i⟩ (ULift.up t)
    · -- fac
      ext y
      simp only [Functor.comp_obj, Discrete.functor_obj_eq_as, Functor.mapCocone_pt,
        TopCat.sigmaCofan_pt, Functor.const_obj_obj, Functor.mapCocone_ι_app,
        TopCat.sigmaCofan_ι_app, SimplexCategory.toTop_obj, SimplexCategory.len_mk,
        Functor.op_obj, yoneda_obj_obj, types_comp_apply]
      simp only [] at y
      obtain ⟨i, t, ht⟩ := singular_simplex_factors_through_summand_psigma f
        (SimplexCategory.mk n) (F.map (TopCat.sigmaι f j.as) y).down
      simp only []
      -- 1) First rewrite `ht` into a pointwise equality in the sigma type.
      --    Typically you can simp the left side: (F.map (sigmaι ...) y).down = y.down ≫ sigmaι ...
      have ht' :
          y.down ≫ TopCat.sigmaι f j.as = t ≫ TopCat.sigmaι f i := by
        -- this is usually `simpa` from `ht` once you expand `(F.map ... y).down`
        -- e.g. `simpa` / `simpa [Functor.map]` / `simpa` using ht
        simpa using ht
      have hn : Nonempty (SimplexCategory.toTop.obj (SimplexCategory.mk n)) := by
        infer_instance
      -- Pick a point in the simplex (the domain is inhabited).
      let p : SimplexCategory.toTop.obj (SimplexCategory.mk n) := Classical.choice hn
            -- Turn ht' into an equality of values at p.
      have hp :
          (⟨j.as, (TopCat.Hom.hom y.down) p⟩ : (Σ k : ι, (f k))) = ⟨i, (TopCat.Hom.hom t) p⟩ := by
        -- ht' : y.down ≫ TopCat.sigmaι f j.as = t ≫ TopCat.sigmaι f i
        have := congrArg
          (fun (φ :
            SimplexCategory.toTop.obj (SimplexCategory.mk n) ⟶ TopCat.of (Σ k : ι, f k)) =>
              (TopCat.Hom.hom φ) p)
          ht'
        -- now simp should turn (sigmaι ...) applied to a point into Sigma.mk
        simpa using this
      have hij : i = j.as := by
        -- `Sigma.mk.inj_iff` is handy
        -- hp : Sigma.mk j.as (...) = Sigma.mk i (...)
        -- so the first components are equal
        exact (Sigma.mk.inj_iff.mp hp).1.symm
      subst hij
      simp
      have hty : t = y.down := by
        -- ext lemma for TopCat morphisms
        ext q
        -- build the sigma-equality at q (same construction as hp, but with q)
        have hSigma :
            (⟨j.as, (TopCat.Hom.hom y.down) q⟩ : (Σ k : ι, f k))
              = ⟨j.as, (TopCat.Hom.hom t) q⟩ := by
          -- exactly your congrArg trick, but evaluating at q
          have := congrArg
            (fun (φ :
              SimplexCategory.toTop.obj (SimplexCategory.mk n) ⟶ TopCat.of (Σ k : ι, f k)) =>
                (TopCat.Hom.hom φ) q)
            ht'
          simpa using this
        -- peel off second component; it’s HEq, convert to Eq
        exact eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2.symm
      subst hty
      rfl
    · -- Unique
      ext p
      simp only [SimplexCategory.toTop_obj, SimplexCategory.len_mk, TopCat.sigmaCofan_pt,
        Functor.op_obj, yoneda_obj_obj, Discrete.functor_obj_eq_as]
      obtain ⟨i, t, ht⟩ := singular_simplex_factors_through_summand_psigma f
        (SimplexCategory.mk n) p.down
      -- ht : p.down = t ≫ sigmaι f i
      -- Goal: m p = s.ι.app ⟨i⟩ ⟨t⟩
      -- Show p = F.map (sigmaι f i) ⟨t⟩, then use hm
      have hp : p = F.map (TopCat.sigmaι f i) ⟨t⟩ := by
        apply ULift.ext
        simp only [F, Functor.comp_map, evaluation_obj_map]
        change p.down = t ≫ TopCat.sigmaι f i
        exact ht
      conv_lhs => rw [hp]
      have := congr_fun (hm ⟨i⟩) (⟨t⟩ : ULift _)
      simpa [types_comp_apply, Functor.mapCocone_ι_app] using this
  exact preservesColimit_of_iso_diagram F Discrete.natIsoFunctor.symm

-- The degree-n evaluation of the singular chain complex functor
-- is definitionally equal to:
--   TopCat.toSSet ⋙ SSet.eval [n] ⋙ sigmaConst.obj R
-- Both factors preserve coproducts:
--   SSet evaluation at [n]: from toSSet_eval_preservesCoproducts
--   sigmaConst.obj R: left adjoint (sigmaConstAdj)
instance singularChainComplexFunctor_preservesCoproducts
    (R : C) :
    PreservesColimitsOfShape (Discrete ι)
      (((singularChainComplexFunctor C).obj R) :
        TopCat.{v} ⥤ ChainComplex C ℕ) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  -- (singularChainComplexFunctor C).obj R ⋙ eval n
  --   = TopCat.toSSet ⋙ SSet.eval [n] ⋙ sigmaConst.obj R
  -- definitionally (rfl). Rewrite goal for instance resolution:
  change PreservesColimitsOfShape (Discrete ι)
    ((TopCat.toSSet ⋙ (evaluation SimplexCategoryᵒᵖ
        (Type v)).obj (Opposite.op
          (SimplexCategory.mk n))) ⋙
      (sigmaConst.obj R : Type v ⥤ C))
  exact comp_preservesColimitsOfShape _ _

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

omit [HasCoproducts C] [AB4 C] in
/-- `ShortComplex.homologyFunctor` preserves colimits of any shape `J`
for which `colim : (J ⥤ C) ⥤ C` preserves homology.
In AB4 categories this applies to all coproducts
(via `colim_preservesHomology`). -/
instance shortComplexHomologyFunctor_preservesColimitsOfShape
    {J : Type v} [SmallCategory J] [HasColimitsOfShape J C]
    [(colim (J := J) (C := C)).PreservesHomology] :
    PreservesColimitsOfShape J
      (ShortComplex.homologyFunctor C) := by
  constructor; intro K
  apply preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone K)
  let S := (ShortComplex.functorEquivalence J C).inverse.obj K
  let h := S.mapHomologyIso (colim (J := J) (C := C))
  -- η : S.homology ≅ K ⋙ homologyFunctor C (pointwise)
  -- Build forward direction first for clean naturality proof
  let η : S.homology ≅ K ⋙ ShortComplex.homologyFunctor C :=
    (NatIso.ofComponents
      (fun j => (ShortComplex.homologyFunctorIso
        ((evaluation J C).obj j)).app S)
      (fun {j₁ j₂} f => by
        change ShortComplex.homologyMap (K.map f) ≫
          (S.mapHomologyIso ((evaluation J C).obj j₂)).hom =
          (S.mapHomologyIso ((evaluation J C).obj j₁)).hom ≫
            S.homology.map f
        have hmapNat :
            S.mapNatTrans ((evaluation J C).map f) =
              K.map f := by
          ext <;> simp [S, ShortComplex.functorEquivalence]
        rw [← hmapNat,
          ShortComplex.homologyMap_mapNatTrans,
          Category.assoc, Category.assoc,
          Iso.inv_hom_id, Category.comp_id]; rfl)).symm
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
  let α : (evaluation J C).obj j ⟶ colim :=
    { app := fun F => colimit.ι F j
      naturality := fun _ _ φ =>
        (colimit.ι_map φ (j := j)).symm }
  have key := NatTrans.app_homology α S
  rw [show colimit.ι S.homology j = α.app S.homology from rfl,
    key, ← Category.assoc, ← Category.assoc]
  have h1 : η.inv.app j =
      (S.mapHomologyIso
        ((evaluation J C).obj j)).hom := by
    simp [η, NatIso.ofComponents,
      ShortComplex.homologyFunctorIso]
  rw [h1, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
  have h2 : S.mapNatTrans α =
      (ShortComplex.colimitCocone K).ι.app j := by
    ext <;> simp [S, α, ShortComplex.colimitCocone,
      ShortComplex.functorEquivalence]
  rw [h2]; simp only [ShortComplex.homologyFunctor_map]; rfl

-- homologyFunctor ≅ shortComplexFunctor ⋙ ShortComplex.homologyFunctor.
-- Both factors preserve coproducts:
--   shortComplexFunctor: from shortComplexFunctor_preservesCoproducts
--   ShortComplex.homologyFunctor: from
--     shortComplexHomologyFunctor_preservesColimitsOfShape
-- Transfer preservation along the natural isomorphism.
instance homologyFunctor_preservesCoproducts (n : ℕ) :
    PreservesColimitsOfShape (Discrete ι)
      (HomologicalComplex.homologyFunctor C
        (ComplexShape.down ℕ) n) := by
  have : PreservesColimitsOfShape (Discrete ι)
      (HomologicalComplex.shortComplexFunctor C
          (ComplexShape.down ℕ) n ⋙
        ShortComplex.homologyFunctor C) :=
    comp_preservesColimitsOfShape _ _
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso C
      (ComplexShape.down ℕ) n).symm

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
