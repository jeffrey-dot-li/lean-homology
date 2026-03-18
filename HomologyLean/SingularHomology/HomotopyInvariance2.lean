import Mathlib.Algebra.Homology.Homotopy
import HomologyLean.CategoryTheory.SubTensorHom
import HomologyLean.SingularHomology.HomotopyMap
import HomologyLean.SingularHomology.EilenbergZilber
import HomologyLean.Tactic.NameParts

open Lean Elab Tactic Meta in
elab "count_hyps" : tactic => withMainContext do
  let lctx ← getLCtx
  let count := lctx.decls.toList.filterMap id |>.length
  logInfo m!"hypothesis count: {count}"

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

/-- In a chain complex over `ℕ`, `C.d i (next i) ≫ (if i = next i + 1 then h ▸ P (next i) i else 0)`
simplifies to `C.d i (next i) ≫ P (next i) i`. When `i > 0` the condition holds and the transport
is trivial; when `i = 0` both sides vanish because `C.d 0 (next 0) = 0`. -/
lemma ChainComplex.d_comp_dite_next {C D : ChainComplex V ℕ}
    (i : ℕ) (P : ∀ n m, C.X n ⟶ D.X m) (hp : P 0 0 = 0) :
    C.d i ((ComplexShape.down ℕ).next i) ≫
      P ((ComplexShape.down ℕ).next i) i =
    C.d i ((ComplexShape.down ℕ).next i) ≫ P ((ComplexShape.down ℕ).next i) i := by
  sorry

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


-- Reuse the same monoidal structure on chain complexes as in `EilenbergZilber.lean`.
noncomputable instance chainComplexMonoidal : MonoidalCategory (ChainComplex C ℕ) :=
  HomologicalComplex.monoidalCategory C (ComplexShape.down ℕ)

/-- The topological Eilenberg-Zilber chain map, obtained from the public natural transformation. -/
noncomputable abbrev eilenbergZilber (X Y : TopCat.{v}) :
    (singChain (C := C) X).tensorObj (singChain (C := C) Y) ⟶
      singChain (C := C) (X ⨯ Y) :=
  (TopCat.eilenbergZilberNatTrans (C := C)).app (X, Y)

/-- The degreewise cross product map induced by the public
topological Eilenberg-Zilber chain map. -/
noncomputable def chainCrossProduct {X Y : TopCat.{v}} {p q n : ℕ}
    (h : p + q = n) :
    (singChain (C := C) X).X p ⊗ (singChain (C := C) Y).X q ⟶
      (singChain (C := C) (X ⨯ Y)).X n :=
  HomologicalComplex.ιTensorObj
      (singChain (C := C) X) (singChain (C := C) Y) p q n h ≫
    (eilenbergZilber (C := C) X Y).f n

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
  have hBoundary₀ : ∀ n, endpointTerm c₀ n = ((SCF.map g).f n : _ ) := by
    intro n
    apply Sigma.hom_ext
    intro s
    dsimp [endpointTerm]
    -- Collapse ι s ≫ (ρ_).inv ≫ (𝟙 ⊗ₘ ι c₀) ≫ chainCrossProduct into simplexCrossProduct s c₀
    slice_lhs 1 4 => erw [simplexCoprojection_comp_chainCrossProduct]
    -- Step 2: unfold TopCat simplexCrossProduct into SSet cross product ≫ SCF.map(prodNatIso)
    dsimp only [simplexCrossProduct]
    -- Step 3: fold (SCF.map prodNatIso.inv.app).f n ≫ chainH.f n via functoriality
    -- Step 3: fold (SCF.map prodNatIso.inv.app).f n ≫ (SCF.map Hmap).f n via functoriality
    dsimp only [chainH]
    rw [show (SCF.map Hmap).f n =
      (((SSet.singularChainComplexFunctor C).obj (𝟙_ C)).map (TopCat.toSSet.map Hmap)).f n from rfl,
      Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp]
    rw [SSetEZ.simplexCrossProduct_zero_right (C := C),
      SSetEZ.simplexCoprojection_comp_SCF_map, simplexCoprojection_comp_SCF_map]
    congr 1; apply ULift.ext
    simp only []
    dsimp [SSetEZ.shuffleSimplex, c₀, Hmap, SSetEZ.prodSimplex]
    simp only [Shuffle.fstHom_default_zero_right, Shuffle.sndHom_default_zero_right,
        FunctorToTypes.map_id_apply]
    erw [toSSet_prodNatIso_inv_app_prodSimplex]
    -- Rewrite toSSet.obj(X).map(eqToHom ...).op s ↦ eqToHom ≫ s.down, avoiding toSSet internals
    simp only [TopCat.toSSet_obj_map_eqToHom_op_down]
    dsimp [TopCat.toSSet]
    convert homotopyMap_comp_delta0 H s.down using 2
  have hBoundary₁ : ∀ n, endpointTerm c₁ n = ((SCF.map f).f n : _ ) := by
    intro n
    apply Sigma.hom_ext
    intro s
    dsimp [endpointTerm]
    slice_lhs 1 4 => erw [simplexCoprojection_comp_chainCrossProduct]
    dsimp only [simplexCrossProduct]
    dsimp only [chainH]
    rw [show (SCF.map Hmap).f n =
      (((SSet.singularChainComplexFunctor C).obj (𝟙_ C)).map (TopCat.toSSet.map Hmap)).f n from rfl,
      Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp]
    rw [SSetEZ.simplexCrossProduct_zero_right (C := C),
      SSetEZ.simplexCoprojection_comp_SCF_map, simplexCoprojection_comp_SCF_map]
    congr 1; apply ULift.ext
    simp only []
    dsimp [SSetEZ.shuffleSimplex, c₁, Hmap, SSetEZ.prodSimplex]
    simp only [Shuffle.fstHom_default_zero_right, Shuffle.sndHom_default_zero_right,
        FunctorToTypes.map_id_apply]
    erw [toSSet_prodNatIso_inv_app_prodSimplex]
    simp only [TopCat.toSSet_obj_map_eqToHom_op_down]
    dsimp [TopCat.toSSet]
    convert homotopyMap_comp_delta1 H s.down using 2
  simp only [dNext_nat, P, homotopyPrism, Preadditive.zsmul_comp, Category.assoc]
  rw [chainH.comm (i + 1) (i)]
  dsimp only [chainCrossProduct];
  simp only [Category.assoc, reassoc_of% ((eilenbergZilber (C := C) X (stdSimplex 1)).comm'
      (i+1) i (by simp [ComplexShape.down_Rel]))]
  simp only [HomologicalComplex.tensorObj, HomologicalComplex.ιTensorObj]
  rw [HomologicalComplex.mapBifunctor.d_eq]
  conv_rhs => lhs; rhs; rhs; slice 2 3; rewrite [Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      -- HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (i ) i
        -- from by simp [ComplexShape.down_Rel]) 1 (i + 1) (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.down ℕ).Rel 1 0
        from by simp [ComplexShape.down_Rel]) (i) (show (i) + 0 = i by omega)
      ]
  simp only [ComplexShape.ε₂]
  -- rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n by simp [ComplexShape.down_Rel])]
  open HomologyLean.CategoryTheory in
  match i with
  | 0 =>
    simp only [ComplexShape.ε_zero,
    ComplexShape.ε₂_def, MonoidalCategory.curriedTensor_obj_map,
    MonoidalCategory.curriedTensor_obj_obj, Preadditive.add_comp, Preadditive.comp_add,
    Category.assoc]
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
    simp only [endpointTerm, chainCrossProduct, HomologicalComplex.tensorObj,
      HomologicalComplex.ιTensorObj, Category.assoc]
    abel
  | n + 1 =>
    simp only [dite_true,
      Preadditive.comp_zsmul, Category.assoc,TotalComplexShape.ε₂,
      ComplexShape.ε, Nat.add_one_sub_one
    ]
    norm_num
    simp only [Units.smul_def,
      Int.reduceNeg, Units.val_pow_eq_pow_val,
       Units.val_neg, Units.val_one, smul_smul,
       ← pow_add, ← two_mul, pow_mul, neg_one_pow_two, one_pow, ]
    norm_num
    rw [← MonoidalCategory.id_tensorHom]
    simp only [tensorι₁, Category.assoc]
    simp only [MonoidalCategory.id_tensorHom]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [boundary_identity_1simplex_generic (C := C)]
    rw [← MonoidalCategory.id_tensorHom
      (f := SingularHomology.simplexCoprojection
        (ULift.up (SimplexCategory.toTop.{v}.map (SimplexCategory.δ 0))) -
        SingularHomology.simplexCoprojection
        (ULift.up (SimplexCategory.toTop.{v}.map (SimplexCategory.δ 1))))]
    rw [tensorHom_sub, Preadditive.sub_comp, Preadditive.comp_sub]
    rw [← hBoundary₀ (n + 1), ← hBoundary₁ (n + 1)]
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (n + 1) n
        from by simp [ComplexShape.down_Rel]) 1 (n + 1) (by simp),
        ComplexShape.ε₁,
        ]
    simp only [← MonoidalCategory.id_tensorHom, endpointTerm,
      chainCrossProduct, HomologicalComplex.tensorObj,
      HomologicalComplex.ιTensorObj, Category.assoc]
    simp only [TotalComplexShape.ε₁]
    simp only [c₀, c₁]
    rw [MonoidalCategory.rightUnitor_inv_naturality_assoc]
    simp only [singChain, ← Preadditive.comp_zsmul]
    abel_nf
    rw [← add_assoc]
    simp only [Int.reduceNeg, Int.zsmul_eq_mul, mul_one, Linear.comp_smul, right_eq_add]
    norm_num
    simp only [Int.reduceNeg,
      MonoidalCategory.curriedTensor_obj_obj, MonoidalCategory.whisker_exchange_assoc,
      MonoidalCategory.whiskerRight_id, Category.assoc, Iso.inv_hom_id_assoc]
    dsimp only [chainH, Hmap]
    name_parts _ = ?LHS
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
