import Mathlib.Algebra.Homology.Homotopy
import HomologyLean.CategoryTheory.SubTensorHom
import HomologyLean.SingularHomology.HomotopyMap
import HomologyLean.SingularHomology.EilenbergZilber
import HomologyLean.Tactic.NameParts
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology unitInterval
open scoped MonoidalCategory

universe u v

namespace HomologyLean.SingularHomology.HomotopyInvariance2

-- TODO: move to TopologicalSimplex or similar
section ToTopEqToHom

open SimplexCategory in
/-- `toTop` maps `eqToHom` in `SimplexCategory` to `eqToHom` in `TopCat`.
Specialization of `eqToHom_map` that avoids unfolding `toTop` internals. -/
@[simp] lemma SimplexCategory.toTop_map_eqToHom_comp {m n : SimplexCategory} (h : m = n)
    {X : TopCat.{v}} (f : toTop.obj n ⟶ X) :
    toTop.map (eqToHom h) ≫ f = eqToHom (congrArg toTop.obj h) ≫ f := by
  rw [eqToHom_map]

/-- A singular simplex precomposed with `eqToHom` in `SimplexCategory` has the same
underlying map (up to `eqToHom` in `TopCat`). This avoids unfolding `toSSet` internals
when handling the `n + 0 = n` cast from the Eilenberg-Zilber zero-right formula. -/
@[simp] lemma TopCat.toSSet_obj_map_eqToHom_op_down {X : TopCat.{v}}
    {m n : SimplexCategory} (h : m = n)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op n)) :
    ((TopCat.toSSet.obj X).map (eqToHom h).op s).down =
      eqToHom (congrArg SimplexCategory.toTop.obj h) ≫ s.down := by
  subst h; simp [FunctorToTypes.map_id_apply]

end ToTopEqToHom

variable {ι : Type*} {V : Type*} [Category V] [Preadditive V]

def chainHtpyMap {C D : ChainComplex V ℕ} (f : ∀ i, C.X i ⟶ D.X (i + 1)) :=
  fun i j => if h : j = i + 1 then h ▸ f i else 0

-- TODO: move these to EilenbergZilber.lean or Shuffle.lean
section ShuffleZeroRight

open SSetEZ SimplexCategory in
@[simp] lemma Shuffle.fstHom_default_zero_right {n : ℕ} :
    Shuffle.fstHom (default : Shuffle n 0) =
      eqToHom (congrArg SimplexCategory.mk (Nat.add_zero n)) := by
  ext ⟨i, hi⟩; rfl

open SSetEZ SimplexCategory in
@[simp] lemma Shuffle.sndHom_default_zero_right {n : ℕ} :
    Shuffle.sndHom (default : Shuffle n 0) =
      SimplexCategory.const (SimplexCategory.mk (n + 0)) (SimplexCategory.mk 0) 0 := by
  ext ⟨i, hi⟩; rfl

end ShuffleZeroRight

variable {C : Type u} [Category.{v} C] [HasCoproducts C] [Preadditive C] [CategoryWithHomology C]
   [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
   [HasForget.{v} C] [MonoidalUnitorRepresentable (C := C)]
   [(forget C).IsRightAdjoint] [(forget C).leftAdjoint.Monoidal]
   [(forget C).LaxMonoidal] [(Adjunction.ofIsRightAdjoint (forget C)).IsMonoidal]
   [NatTrans.IsMonoidal (MonoidalUnitorRepresentable.forgetIso (C := C)).hom]
   [MonoidalLinear ℤ C]
   [∀ (X : C), PreservesFiniteCoproducts (MonoidalCategory.tensorRight X)]


/-- The fundamental singular `1`-simplex of `Δ[1]`. -/
abbrev intervalFundamentalSimplex : SingularSimplex (stdSimplex 1 : TopCat.{v}) 1 :=
  ULift.up (𝟙 (stdSimplex 1 : TopCat.{v}))

/-- Tensor on the right with the fundamental `1`-simplex of `Δ[1]`. -/
noncomputable def tensorι₁ {X : TopCat.{v}} (n : ℕ) :
    (singChain (C := C) X).X n ⟶
      (singChain (C := C) X).X n ⊗ (singChain (C := C) (stdSimplex 1 : TopCat.{v})).X 1 :=
  (ρ_ ((singChain (C := C) X).X n)).inv ≫
    (𝟙 ((singChain (C := C) X).X n) ⊗ₘ
      simplexCoprojection (C := C)
        (intervalFundamentalSimplex : SingularSimplex (stdSimplex 1 : TopCat.{v}) 1))

/-- The prism operator attached to a homotopy `H`, built from the interval fundamental class,
the Eilenberg-Zilber cross product, and the induced map `X × Δ[1] ⟶ Y`. -/
noncomputable def homotopyPrism {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') (n : ℕ) :
    (singChain (C := C) X).X n ⟶ (singChain (C := C) Y).X (n + 1) :=
  let Hmap : X ⨯ (stdSimplex 1 : TopCat.{v}) ⟶ Y := homotopyMap H
  (-1 : ℤ) ^ n •
    (tensorι₁ (X := X) n ≫
      chainCrossProduct (C := C) (X := X) (Y := (stdSimplex 1 : TopCat.{v}))
        (show n + 1 = n + 1 from rfl) ≫
      (SCF.map Hmap).f (n + 1))


/-- A topological homotopy induces a chain homotopy between the induced singular chain maps.

Dependency structure:
- `boundary_identity_1simplex_generic`
- `tensorι₁_comp_d`
- the endpoint specializations of the EZ zero-right formula, derived inline from the
  general zero-right cross-product behavior together with `homotopyMap_comp_delta0`
  and `homotopyMap_comp_delta1`
- the degree `(0, 1)` Leibniz step, derived inline from the general zero-edge EZ
  Leibniz rule
- `homotopyMap_comp_delta0`, `homotopyMap_comp_delta1` from `HomotopyMap.lean`. -/
noncomputable def singularChain_chainHomotopy_of_homotopy {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') :
    Homotopy
      ((SCF.map g) : singChain (C := C) X ⟶ singChain (C := C) Y)
      ((SCF.map f) : singChain (C := C) X ⟶ singChain (C := C) Y) := by
  let Hmap : X ⨯ (stdSimplex 1 : TopCat.{v}) ⟶ Y := homotopyMap H
  let chainH : singChain (C := C) (X ⨯ (stdSimplex 1 : TopCat.{v})) ⟶ singChain (C := C) Y :=
    (SCF.map Hmap)
  let c₀ : SingularSimplex (stdSimplex 1 : TopCat.{v}) 0 :=
    ULift.up (SimplexCategory.toTop.map (SimplexCategory.δ 0))
  let c₁ : SingularSimplex (stdSimplex 1 : TopCat.{v}) 0 :=
    ULift.up (SimplexCategory.toTop.map (SimplexCategory.δ 1))
  let endpointTerm := fun (c : SingularSimplex (stdSimplex 1 : TopCat.{v}) 0) (n : ℕ) =>
    (ρ_ ((singChain (C := C) X).X n)).inv ≫
      (𝟙 ((singChain (C := C) X).X n) ⊗ₘ simplexCoprojection (C := C) c) ≫
      chainCrossProduct (C := C) (X := X) (Y := (stdSimplex 1 : TopCat.{v}))
        (show n + 0 = n from by omega) ≫
      chainH.f n
  let P := homotopyPrism (C := C) H
  refine Homotopy.mk
    (fun i j => if h : j = i + 1 then h ▸ P i else 0)
    (by
      intro i j h
      dsimp
      rw [dif_neg]
      rw [ComplexShape.down_Rel] at h
      omega)
    ?_
  intro i
  rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i by simp [ComplexShape.down_Rel])]
  -- rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n by simp [ComplexShape.down_Rel])]
  -- (ComplexShape.down ℕ).next i
  -- dNext i (f(i, j)) = (SCF.obj X).d (i) ((ComplexShape.down ℕ).next i) >> f((ComplexShape.down ℕ).next i, i)
  simp only [dif_pos trivial]
  have endpointTerm_reduce :
      ∀ (c : SingularSimplex (stdSimplex 1 : TopCat.{v}) 0) (target : X ⟶ Y),
      (∀ (n : ℕ) (s : SimplexCategory.toTop.obj (SimplexCategory.mk n) ⟶ X),
        prod.lift s (SimplexCategory.toTop.map default ≫ c.down) ≫
          homotopyMap H = s ≫ target) →
      ∀ n, endpointTerm c n =
        (SSetEZ.SCF.map (TopCat.toSSet.map target)).f n := by
    intro c target hc n
    apply singChain_hom_ext
    intro s
    dsimp only [endpointTerm]
    rw [simplexCoprojection_comp_chainCrossProduct_assoc]
    dsimp only [simplexCrossProduct, chainH]
    simp only [Functor.comp_obj, Functor.prod_obj, MonoidalCategory.tensor_obj,
      Functor.comp_map, Category.assoc, SSetEZ.simplexCoprojection_comp_SCF_map,
      toSSet_map_app_singularSimplex, Functor.op_obj, SimplexCategory.toTop_obj,
      SimplexCategory.len_mk, yoneda_obj_obj]
    rw [SSetEZ.simplexCrossProduct_zero_right (C := C)]
    dsimp only [SSetEZ.shuffleSimplex, Hmap]
    simp only [Nat.add_zero, Shuffle.fstHom_default_zero_right, eqToHom_refl, op_id,
      FunctorToTypes.map_id_apply, Shuffle.sndHom_default_zero_right, Fin.isValue,
      const_zero_eq_default, toSSet_obj_map_singularSimplex, Functor.op_obj,
      SimplexCategory.toTop_obj, SimplexCategory.len_mk, yoneda_obj_obj, Nat.reduceAdd,
      SSetEZ.simplexCoprojection_comp_SCF_map_assoc,
      SSetEZ.simplexCoprojection_comp_SCF_map, toSSet_map_app_singularSimplex]
    congr 1; congr 1
    rw [toSSet_prodNatIso_inv_app_prodSimplex]
    exact hc n s.down
  have hBoundary₀ : ∀ n, endpointTerm c₀ n =
      (SSetEZ.SCF.map (TopCat.toSSet.map g)).f n :=
    endpointTerm_reduce c₀ g (fun n s => homotopyMap_comp_delta0 H s)
  have hBoundary₁ : ∀ n, endpointTerm c₁ n =
      (SSetEZ.SCF.map (TopCat.toSSet.map f)).f n :=
    endpointTerm_reduce c₁ f (fun n s => homotopyMap_comp_delta1 H s)
  simp only [dNext_nat, P, homotopyPrism, Preadditive.zsmul_comp, Category.assoc]
  simp only [Functor.comp_obj, Functor.comp_map, Int.reduceNeg, HomologicalComplex.Hom.comm]
  repeat' rw [chainCrossProduct_eq]
  simp only [Int.reduceNeg, Category.assoc, HomologicalComplex.Hom.comm_assoc]
  rw [HomologicalComplex.mapBifunctor.d_eq]
  conv_rhs => lhs; rhs; rhs; slice 2 3; rewrite [Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      -- HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (i ) i
        -- from by simp [ComplexShape.down_Rel]) 1 (i + 1) (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.down ℕ).Rel 1 0
        from by simp [ComplexShape.down_Rel]) (i) (show (i) + 0 = i by omega)
      ]
  unfold ComplexShape.ε₂
  simp only [Int.reduceNeg, MonoidalCategory.curriedTensor_obj_obj, ComplexShape.ε₂_def,
    ComplexShape.ε_down_ℕ, MonoidalCategory.curriedTensor_obj_map, Preadditive.add_comp,
    Linear.units_smul_comp, Category.assoc, Preadditive.comp_add, Linear.comp_units_smul, smul_add]
  -- rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n by simp [ComplexShape.down_Rel])]
  open HomologyLean.CategoryTheory in
  match i with
  | 0 =>
    norm_num

    rw[ HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
        (fun h => by simp [ComplexShape.down_Rel] at h)]
    norm_num
    rw [← MonoidalCategory.id_tensorHom]
    -- simp only [zero_comp, comp_zero, zero_add]
    simp only [tensorι₁, Category.assoc]
    rw [← Category.assoc (𝟙 _ ⊗ₘ simplexCoprojection (C := C) intervalFundamentalSimplex),
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
    rw [boundary_identity_1simplex_generic (C := C)]
    rw [tensorHom_sub, Preadditive.sub_comp, Preadditive.comp_sub]
    rw [←hBoundary₀ 0, ←hBoundary₁ 0]
    simp only [endpointTerm, chainCrossProduct_eq, HomologicalComplex.tensorObj,
      HomologicalComplex.ιTensorObj, Category.assoc, chainH, Functor.comp_map]
    abel
  | n + 1 =>
    norm_num
    simp only [Nat.add_one_sub_one, Int.reduceNeg]
    rw [Units.smul_def]
    norm_num
    repeat' rw [smul_smul, ← pow_add, ← two_mul]
    norm_num
    simp only [tensorι₁, Category.assoc, MonoidalCategory.id_tensorHom]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [boundary_identity_1simplex_generic (C := C)]
    rw [← MonoidalCategory.id_tensorHom
      (f := SingularHomology.simplexCoprojection
        (ULift.up (SimplexCategory.toTop.{v}.map (SimplexCategory.δ 0))) -
        SingularHomology.simplexCoprojection
        (ULift.up (SimplexCategory.toTop.{v}.map (SimplexCategory.δ 1))))]
    rw [tensorHom_sub, Preadditive.sub_comp, Preadditive.comp_sub]
    rw [← hBoundary₀ (n + 1), ← hBoundary₁ (n + 1)]
    -- simp
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (n + 1) n
        from by simp [ComplexShape.down_Rel]) 1 (n + 1) (by simp),
        ComplexShape.ε₁,
        ]
    rw [MonoidalCategory.rightUnitor_inv_naturality_assoc]
    simp only [← MonoidalCategory.id_tensorHom, endpointTerm,
      chainCrossProduct_eq, HomologicalComplex.tensorObj,
      HomologicalComplex.ιTensorObj, Category.assoc]
    -- simp only []
    -- unfold TotalComplexShape.ε₁
    simp only [TotalComplexShape.ε₁]
    unfold c₀ c₁
    simp only [singChain, ← Preadditive.comp_zsmul]
    abel_nf
    rw [← add_assoc]
    norm_num
    simp?
    rw [MonoidalCategory.whisker_exchange_assoc]
    simp?
    unfold chainH Hmap
    simp only [Fin.isValue, Functor.comp_map, Int.reduceNeg, neg_add_cancel, add_zero,
      right_eq_add]
    -- name_parts _ = ?LHS
    module

/-- Homotopic maps induce equal maps on singular homology. -/
theorem singularHomology_map_eq_of_homotopy {X Y : TopCat.{v}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom' g.hom') (n : ℕ) :
    ((singularHomologyFunctor C n).obj (𝟙_ C)).map f =
      ((singularHomologyFunctor C n).obj (𝟙_ C)).map g := by
  exact (singularChain_chainHomotopy_of_homotopy (C := C) H).homologyMap_eq n |>.symm

/-- Homotopy equivalent spaces have isomorphic singular homology. -/
noncomputable def singularHomology_iso_of_homotopyEquiv {X Y : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : ContinuousMap.Homotopy (f ≫ g : X ⟶ X).hom' (𝟙 X : X ⟶ X).hom')
    (hgf : ContinuousMap.Homotopy (g ≫ f : Y ⟶ Y).hom' (𝟙 Y : Y ⟶ Y).hom')
    (n : ℕ) :
    ((singularHomologyFunctor C n).obj (𝟙_ C)).obj X ≅
      ((singularHomologyFunctor C n).obj (𝟙_ C)).obj Y where
  hom := ((singularHomologyFunctor C n).obj (𝟙_ C)).map f
  inv := ((singularHomologyFunctor C n).obj (𝟙_ C)).map g
  hom_inv_id := by
    rw [← Functor.map_comp, singularHomology_map_eq_of_homotopy (C := C) hfg n]
    exact ((singularHomologyFunctor C n).obj (𝟙_ C)).map_id X
  inv_hom_id := by
    rw [← Functor.map_comp, singularHomology_map_eq_of_homotopy (C := C) hgf n]
    exact ((singularHomologyFunctor C n).obj (𝟙_ C)).map_id Y

end HomologyLean.SingularHomology.HomotopyInvariance2
