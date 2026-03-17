import Mathlib.Algebra.Homology.Homotopy
import HomologyLean.CategoryTheory.SubTensorHom
import HomologyLean.SingularHomology.HomotopyMap
import HomologyLean.SingularHomology.EilenbergZilber

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

/-- The standard topological `p`-simplex. -/
abbrev stdSimplex (p : ℕ) : TopCat.{v} :=
  SimplexCategory.toTop.obj (SimplexCategory.mk p)

/-- Singular chains with coefficients in the monoidal unit. -/
abbrev SCF : TopCat.{v} ⥤ ChainComplex C ℕ :=
  (singularChainComplexFunctor.{v} C).obj (𝟙_ C)

/-- The singular chain complex of a topological space with coefficients in `𝟙_ C`. -/
abbrev singChain (X : TopCat.{v}) : ChainComplex C ℕ :=
  (SCF (C := C)).obj X

/-- A singular `n`-simplex in `X`. -/
abbrev SingularSimplex (X : TopCat.{v}) (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- Convenience constructor from a map `Δ[n] ⟶ X` to the corresponding singular simplex. -/
noncomputable abbrev SingularSimplex.ofΔ {X : TopCat.{v}} {n : ℕ} (f : stdSimplex n ⟶ X) :
    SingularSimplex X n :=
  ULift.up f

/- The coprojection of a singular simplex into the corresponding chain group. -/
noncomputable abbrev simplexCoprojection {X : TopCat.{v}} {n : ℕ}
    (s : SingularSimplex X n) : 𝟙_ C ⟶ (singChain (C := C) X).X n :=
  Sigma.ι (fun _ : SingularSimplex X n => 𝟙_ C) s

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
  SingularSimplex.ofΔ (𝟙 (stdSimplex 1 : TopCat.{v}))

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
    SingularSimplex.ofΔ (SimplexCategory.toTop.map (SimplexCategory.δ 0))
  let c₁ : SingularSimplex (stdSimplex 1 : TopCat.{v}) 0 :=
    SingularSimplex.ofΔ (SimplexCategory.toTop.map (SimplexCategory.δ 1))
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
  have hLeibniz (n : ℕ) :
      chainCrossProduct (C := C) (X := X) (Y := (stdSimplex 1 : TopCat.{v}))
          (show (n + 1) + 1 = (n + 1) + 1 from rfl) ≫
        (singChain (C := C) (X ⨯ (stdSimplex 1 : TopCat.{v}))).d ((n + 1) + 1) (n + 1) =
      ((singChain (C := C) X).d (n + 1) n ⊗ₘ
          𝟙 ((singChain (C := C) (stdSimplex 1 : TopCat.{v})).X 1)) ≫
        chainCrossProduct (C := C) (X := X) (Y := (stdSimplex 1 : TopCat.{v}))
          (show n + 1 = n + 1 from rfl) +
      ((-1 : ℤ) ^ (n + 1)) •
        ((𝟙 ((singChain (C := C) X).X (n + 1)) ⊗ₘ
            (singChain (C := C) (stdSimplex 1 : TopCat.{v})).d 1 0) ≫
          chainCrossProduct (C := C) (X := X) (Y := (stdSimplex 1 : TopCat.{v}))
            (show (n + 1) + 0 = n + 1 from by omega)) := by
    dsimp only [chainCrossProduct]
    rw [Category.assoc, (eilenbergZilber (C := C) X (stdSimplex 1)).comm'
      ((n + 1) + 1) (n + 1) (by simp [ComplexShape.down_Rel]),
      ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [HomologicalComplex.tensorObj, HomologicalComplex.ιTensorObj]
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (n + 1) n
        from by simp [ComplexShape.down_Rel]) 1 (n + 1) (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.down ℕ).Rel 1 0
        from by simp [ComplexShape.down_Rel]) (n + 1) (show (n + 1) + 0 = n + 1 by omega)]
    simp [ComplexShape.ε₁, ComplexShape.ε₂, ComplexShape.ε, MonoidalCategory.curriedTensor]
    rfl
  have hLeibniz₀ :
      chainCrossProduct (C := C) (X := X) (Y := (stdSimplex 1 : TopCat.{v}))
          (show 0 + 1 = 0 + 1 from rfl) ≫
        (singChain (C := C) (X ⨯ (stdSimplex 1 : TopCat.{v}))).d 1 0 =
      (𝟙 ((singChain (C := C) X).X 0) ⊗ₘ
          (singChain (C := C) (stdSimplex 1 : TopCat.{v})).d 1 0) ≫
        chainCrossProduct (C := C) (X := X) (Y := (stdSimplex 1 : TopCat.{v}))
          (show 0 + 0 = 0 from by omega) := by
    dsimp only [chainCrossProduct]
    rw [Category.assoc, (eilenbergZilber (C := C) X (stdSimplex 1)).comm' 1 0
      (by simp [ComplexShape.down_Rel]), ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [HomologicalComplex.tensorObj, HomologicalComplex.ιTensorObj]
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
        (fun h => by simp [ComplexShape.down_Rel] at h),
      zero_add,
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
        (show (ComplexShape.down ℕ).Rel 1 0 from by simp [ComplexShape.down_Rel]) 0 (by simp)]
    simp [ComplexShape.ε₂, ComplexShape.ε, MonoidalCategory.curriedTensor]
  open HomologyLean.CategoryTheory in

  match i with
  | 0 =>
    rw [dNext_eq_zero _ 0 (by simp [ComplexShape.down_Rel])]
    simp
    conv_rhs => lhs; rw [show P 0 = tensorι₁ 0 ≫
        chainCrossProduct (C := C) (show 0 + 1 = 0 + 1 from rfl) ≫ chainH.f 1 from by
      simp [P, homotopyPrism]; rfl]
    simp only [Category.assoc]
    rw [chainH.comm 1 0]
    rw [← Category.assoc (chainCrossProduct (C := C) (show 0 + 1 = 0 + 1 from rfl)),
        hLeibniz₀]
    simp only [tensorι₁, Category.assoc]
    rw [← Category.assoc (𝟙 _ ⊗ₘ simplexCoprojection (C := C) intervalFundamentalSimplex),
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
    rw [boundary_identity_1simplex_generic (C := C)]
    rw [tensorHom_sub, Preadditive.sub_comp, Preadditive.comp_sub]
    rw [←hBoundary₀ 0, ←hBoundary₁ 0]
    abel
  | n + 1 =>
    -- Higher degrees: use `tensorι₁_comp_d`, the general Leibniz rule at `(n, 0)`,
    -- and again discharge the interval-boundary term via `hBoundary₀` / `hBoundary₁`.
    rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n by simp [ComplexShape.down_Rel])]
    simp
    simp only [P, homotopyPrism, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    rw [chainH.comm (n + 2) (n + 1)]
    rw [← Category.assoc (chainCrossProduct (C := C) (show (n + 1) + 1 = (n + 1) + 1 from rfl)),
        hLeibniz n]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, Category.assoc]
    simp only [smul_add, smul_smul, ← pow_add, ← two_mul,
      pow_mul, neg_one_pow_two, one_pow, one_smul]
    conv_rhs => lhs; rw [← add_assoc]
    let Xbdy := tensorι₁ (n + 1) ≫
      ((singChain (C := C) X).d (n + 1) n ⊗ₘ 𝟙 ((singChain (C := C) (stdSimplex 1 : TopCat.{v})).X 1)) ≫
        chainCrossProduct (C := C) (show n + 1 = n + 1 from rfl) ≫ chainH.f (n + 1)
    let Δbdy := tensorι₁ (n + 1) ≫
      (𝟙 ((singChain (C := C) X).X (n + 1)) ⊗ₘ (singChain (C := C) (stdSimplex 1 : TopCat.{v})).d 1 0) ≫
        chainCrossProduct (C := C) (show (n + 1) + 0 = n + 1 from by omega) ≫
          chainH.f (n + 1)
    change _ = (-1) ^ n • (((SCF (C := C)).obj X).d (n + 1) n ≫
        tensorι₁ n ≫ chainCrossProduct (C := C) (show n + 1 = n + 1 from rfl) ≫
          chainH.f (n + 1)) +
      (-1) ^ (n + 1) • Xbdy + Δbdy + ((SCF (C := C)).map f).f (n + 1)
    have hΔbdy : Δbdy = ((SCF (C := C)).map g).f (n + 1) - ((SCF (C := C)).map f).f (n + 1) := by
      simp only [Δbdy, tensorι₁, Category.assoc]
      rw [← Category.assoc (𝟙 _ ⊗ₘ simplexCoprojection (C := C) intervalFundamentalSimplex),
        MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
      erw [boundary_identity_1simplex_generic (C := C)]
      rw [tensorHom_sub, Preadditive.sub_comp, Preadditive.comp_sub]
      rw [show (ρ_ ((singChain (C := C) X).X (n + 1))).inv ≫
            (𝟙 ((singChain (C := C) X).X (n + 1)) ⊗ₘ
              simplexCoprojection (SingularSimplex.ofΔ (SimplexCategory.toTop.map (SimplexCategory.δ 0)))) ≫
            chainCrossProduct (C := C) (show (n + 1) + 0 = n + 1 from by omega) ≫ chainH.f (n + 1) =
          endpointTerm c₀ (n + 1) from rfl,
        show (ρ_ ((singChain (C := C) X).X (n + 1))).inv ≫
            (𝟙 ((singChain (C := C) X).X (n + 1)) ⊗ₘ
              simplexCoprojection (SingularSimplex.ofΔ (SimplexCategory.toTop.map (SimplexCategory.δ 1)))) ≫
            chainCrossProduct (C := C) (show (n + 1) + 0 = n + 1 from by omega) ≫ chainH.f (n + 1) =
          endpointTerm c₁ (n + 1) from rfl,
        hBoundary₀ (n + 1), hBoundary₁ (n + 1)]
    rw [hΔbdy]
    abel
    simp only [Xbdy]
    have htensor_nat : tensorι₁ (n + 1) ≫
        ((singChain (C := C) X).d (n + 1) n ⊗ₘ 𝟙 ((singChain (C := C) (stdSimplex 1 : TopCat.{v})).X 1)) =
        ((SCF (C := C)).obj X).d (n + 1) n ≫ tensorι₁ n := by
      simp only [tensorι₁, Category.assoc]
      rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      conv_rhs =>
        rw [← Category.assoc, MonoidalCategory.rightUnitor_inv_naturality, Category.assoc]
      congr 1
      rw [← MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    simp only [← Category.assoc (tensorι₁ (n + 1)), htensor_nat, Category.assoc]
    norm_num
    rw [pow_succ, mul_neg_one, neg_smul]
    abel

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
