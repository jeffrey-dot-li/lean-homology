import HomologyLean.SingularHomology.Bisimplicial
import HomologyLean.SingularHomology.BisimplicialNormalizedDefs
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# Bridge₁ scaffolding

This file isolates the `bridge₁ : HomotopyEquiv (N₁.obj X) (F₁.obj X)` work from the normalized
Eilenberg–Zilber proof file. It intentionally depends on `BisimplicialNormalizedDefs.lean` but not
on `BisimplicialNormalized.lean`.

The intended factorization is

`N₁(X) ≃ M₁(X) ≃ F₁(X)`,

where `M₁` is outer-unnormalized and inner-normalized.
-/

open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial
open HomologyLean.SingularHomology

/-- The symmetry of the total complex shape on `ChainComplex _ ℕ` bicomplexes, with respect to the
canonical `TotalComplexShape (down ℕ) (down ℕ) (down ℕ)`. The sign `σ i₁ i₂ = (-1)^(i₁ * i₂)`
(written via the alternating sign `ε`) is exactly what is needed for the flip symmetry
`HomologicalComplex₂.totalFlipIso`. Mirrors the `up ℤ` instance in Mathlib. -/
instance : TotalComplexShapeSymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) where
  symm i₁ i₂ := add_comm i₂ i₁
  σ i₁ i₂ := (ComplexShape.down ℕ).ε (i₁ * i₂)
  σ_ε₁ := by
    intro i₁ i₁' h₁ i₂
    obtain rfl : i₁' + 1 = i₁ := h₁
    change (ComplexShape.down ℕ).ε ((i₁' + 1) * i₂) * 1 =
      (ComplexShape.down ℕ).ε i₂ * (ComplexShape.down ℕ).ε (i₁' * i₂)
    rw [mul_one, add_mul, one_mul, ComplexShape.ε_add, mul_comm]
  σ_ε₂ := by
    intro i₁ i₂ i₂' h₂
    obtain rfl : i₂' + 1 = i₂ := h₂
    change (ComplexShape.down ℕ).ε (i₁ * (i₂' + 1)) * (ComplexShape.down ℕ).ε i₁ =
      1 * (ComplexShape.down ℕ).ε (i₁ * i₂')
    rw [one_mul, mul_add, mul_one, ComplexShape.ε_add, mul_assoc, Int.units_mul_self, mul_one]

namespace CategoryTheory

namespace BisimplicialObject

variable {C : Type*} [Category* C] [Abelian C]

/-- The intermediate total complex for `bridge₁`: outer unnormalized, inner normalized. -/
noncomputable abbrev M₁ (X : BisimplicialObject C) : ChainComplex C ℕ :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).obj
    (((normalizedMooreComplex C).mapHomologicalComplex _).obj
      ((alternatingFaceMapComplex (SimplicialObject C)).obj X))

variable (X : BisimplicialObject C)

/-- The outer normalization inclusion `N₁(X) ⟶ M₁(X)`. -/
noncomputable def inclusionM₁ : N₁.obj X ⟶ M₁ X :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).map
    (((normalizedMooreComplex C).mapHomologicalComplex _).map (inclusionOfMooreComplexMap X))

/-- The outer normalization retraction `M₁(X) ⟶ N₁(X)`. -/
noncomputable def retractionM₁ : M₁ X ⟶ N₁.obj X :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).map
    (((normalizedMooreComplex C).mapHomologicalComplex _).map (PInftyToNormalizedMooreComplex X))

/-- The inner normalization inclusion `M₁(X) ⟶ F₁(X)`. -/
noncomputable def inclusionF₁ : M₁ X ⟶ F₁.obj X :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).map
    ((NatTrans.mapHomologicalComplex mooreInclusion _).app
      ((alternatingFaceMapComplex (SimplicialObject C)).obj X))

/-- The inner normalization retraction `F₁(X) ⟶ M₁(X)`. -/
noncomputable def retractionF₁ : F₁.obj X ⟶ M₁ X :=
  (HomologicalComplex₂.totalFunctor _ _ _ _).map
    ((NatTrans.mapHomologicalComplex mooreRetraction _).app
      ((alternatingFaceMapComplex (SimplicialObject C)).obj X))

@[reassoc]
lemma inclusionM₁_comp_inclusionF₁ :
    inclusionM₁ X ≫ inclusionF₁ X = inclusionN₁ X := by
  dsimp only [inclusionM₁, inclusionF₁, inclusionN₁, HomologicalComplex₂.totalFunctor]
  rw [← HomologicalComplex₂.total.map_comp]

@[reassoc]
lemma retractionF₁_comp_retractionM₁ :
    retractionF₁ X ≫ retractionM₁ X = retractionN₁ X := by
  dsimp only [retractionF₁, retractionM₁, retractionN₁, HomologicalComplex₂.totalFunctor]
  rw [← HomologicalComplex₂.total.map_comp]

@[reassoc]
lemma inclusionM₁_comp_retractionM₁ :
    inclusionM₁ X ≫ retractionM₁ X = 𝟙 (N₁.obj X) := by
  dsimp only [inclusionM₁, retractionM₁, HomologicalComplex₂.totalFunctor]
  rw [← HomologicalComplex₂.total.map_comp]
  have h :
      (((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (inclusionOfMooreComplexMap X) ≫
        ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (PInftyToNormalizedMooreComplex X)) =
      𝟙 _ := by
    rw [← Functor.map_comp]
    change ((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (inclusionOfMooreComplexMap X ≫ (splitMonoInclusionOfMooreComplexMap X).retraction) = _
    rw [(splitMonoInclusionOfMooreComplexMap X).id, Functor.map_id]
  rw [h, HomologicalComplex₂.total.map_id]
  rfl

private lemma mooreInclusion_comp_mooreRetraction :
    mooreInclusion ≫ mooreRetraction = 𝟙 (normalizedMooreComplex C) := by
  ext Y : 2
  exact (splitMonoInclusionOfMooreComplexMap Y).id

@[reassoc]
lemma inclusionF₁_comp_retractionF₁ :
    inclusionF₁ X ≫ retractionF₁ X = 𝟙 (M₁ X) := by
  dsimp only [inclusionF₁, retractionF₁, HomologicalComplex₂.totalFunctor]
  rw [← HomologicalComplex₂.total.map_comp]
  have h :
      (NatTrans.mapHomologicalComplex mooreInclusion (ComplexShape.down ℕ)).app
          ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
        (NatTrans.mapHomologicalComplex mooreRetraction (ComplexShape.down ℕ)).app
          ((alternatingFaceMapComplex (SimplicialObject C)).obj X) =
      𝟙 _ := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      mooreInclusion_comp_mooreRetraction, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  rw [h, HomologicalComplex₂.total.map_id]
  rfl

namespace HomologicalComplex₂

section OuterLift

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape J}
  [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c] [L.HasTotal c]
  {φ ψ : K ⟶ L}

private noncomputable def totalMapHomotopyHom (h : Homotopy φ ψ) (j j' : J) :
    (K.total c).X j ⟶ (L.total c).X j' :=
  K.totalDesc (c₁₂ := c)
    (fun i₁ i₂ _ =>
      ComplexShape.ε₁ c₁ c₂ c (c₁.prev i₁, i₂) •
        (h.hom i₁ (c₁.prev i₁)).f i₂ ≫
          L.ιTotalOrZero c (c₁.prev i₁) i₂ j')

@[reassoc]
private lemma ιTotal_totalMapHomotopyHom (h : Homotopy φ ψ) (i₁ : I₁) (i₂ : I₂) (j j' : J)
    (hj : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    K.ιTotal c i₁ i₂ j hj ≫ totalMapHomotopyHom h j j' =
      ComplexShape.ε₁ c₁ c₂ c (c₁.prev i₁, i₂) •
        (h.hom i₁ (c₁.prev i₁)).f i₂ ≫
          L.ιTotalOrZero c (c₁.prev i₁) i₂ j' := by
  simp [totalMapHomotopyHom]

private lemma totalMapHomotopy_zero (h : Homotopy φ ψ) (j j' : J)
    (hj : ¬ c.Rel j' j) :
    totalMapHomotopyHom (c := c) h j j' = 0 := by
  apply HomologicalComplex₂.total.hom_ext (c₁₂ := c)
  intro i₁ i₂ hi
  rw [ιTotal_totalMapHomotopyHom]
  by_cases h₁ : c₁.Rel (c₁.prev i₁) i₁
  · rw [L.ιTotalOrZero_eq_zero c (c₁.prev i₁) i₂ j']
    · simp
    · intro h'
      apply hj
      rw [← hi, ← h']
      exact ComplexShape.rel_π₁ c₂ c h₁ i₂
  · rw [h.zero i₁ (c₁.prev i₁) h₁, HomologicalComplex.zero_f, zero_comp,
      smul_zero, comp_zero]

private lemma totalMapHomotopy_comm_aux (h : Homotopy φ ψ)
    {i₁ i₁' : I₁} (hi₁ : c₁.Rel i₁ i₁')
    {i₂ i₂' : I₂} (hi₂ : c₂.Rel i₂ i₂') (j : J)
    (hj : ComplexShape.π c₁ c₂ c (i₁', i₂) = j) :
    ComplexShape.ε₁ c₁ c₂ c (i₁, i₂) •
        (h.hom i₁' i₁).f i₂ ≫ L.d₂ c i₁ i₂ j =
      -(K.d₂ c i₁' i₂ (c.next j) ≫
        totalMapHomotopyHom h (c.next j) j) := by
  have hj' : ComplexShape.π c₁ c₂ c (i₁, i₂') = j := by
    rw [← hj, ← ComplexShape.next_π₂ c₁ c i₁ hi₂,
      ComplexShape.next_π₁ c₂ c hi₁ i₂]
  rw [HomologicalComplex₂.d₂_eq _ c _ hi₂ _ hj', HomologicalComplex₂.d₂_eq _ c _ hi₂ _
        (by rw [← c.next_eq'
          (ComplexShape.rel_π₂ c₁ c i₁' hi₂), hj]),
    Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    ιTotal_totalMapHomotopyHom h _ _ _ _
      (by rw [← c.next_eq'
        (ComplexShape.rel_π₂ c₁ c i₁' hi₂), hj]),
    c₁.prev_eq' hi₁,
    HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ hj',
    Linear.comp_units_smul, smul_smul, smul_smul,
    ComplexShape.ε₁_ε₂ c hi₁ hi₂, neg_mul, Units.neg_smul, neg_inj,
    smul_left_cancel_iff, HomologicalComplex.Hom.comm_assoc]

private lemma totalMapHomotopy_comm (h : Homotopy φ ψ) (j : J) :
    (HomologicalComplex₂.total.map φ c).f j =
      dNext j (totalMapHomotopyHom h) + prevD j (totalMapHomotopyHom h) +
        (HomologicalComplex₂.total.map ψ c).f j := by
  apply HomologicalComplex₂.total.hom_ext (c₁₂ := c)
  intro i₁ i₂ hj
  simp only [h.comm i₁, dNext_eq_dFrom_fromNext, HomologicalComplex.dFrom, fromNext,
    AddMonoidHom.mk'_apply, prevD_eq_toPrev_dTo, toPrev, HomologicalComplex.dTo,
    Preadditive.add_comp, Preadditive.comp_add, HomologicalComplex₂.total_d,
    HomologicalComplex₂.ιTotal_map, HomologicalComplex₂.ι_D₁_assoc,
    HomologicalComplex₂.ι_D₂_assoc]
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, Preadditive.add_comp,
    Category.assoc, add_left_inj]
  have : ∀ {X Y : C} (a b c d e f : X ⟶ Y), a = c → b = e → f = -d →
      a + b = c + d + (e + f) := by
    rintro X Y a b _ d _ _ rfl rfl rfl
    abel
  apply this
  · by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
    · rw [HomologicalComplex₂.d₁_eq _ c h₃ _ _
        (by rw [← hj, ComplexShape.next_π₁ c₂ c h₃ i₂]),
        Linear.units_smul_comp, Category.assoc,
        ιTotal_totalMapHomotopyHom h _ _ _ _
          (by
            rw [← ComplexShape.next_π₁ c₂ c h₃ i₂, hj]),
        c₁.prev_eq' h₃, L.ιTotalOrZero_eq c i₁ i₂ j hj,
        Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
    · rw [K.shape_f _ _ h₃, zero_comp,
        HomologicalComplex₂.d₁_eq_zero _ c _ _ _ h₃, zero_comp]
  · rw [ιTotal_totalMapHomotopyHom_assoc h _ _ _ _ hj]
    by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
    · rw [L.ιTotalOrZero_eq c (c₁.prev i₁) i₂
          (c.prev j) (by
            rw [← ComplexShape.prev_π₁ c₂ c h₃, hj]),
        Linear.units_smul_comp, Category.assoc, HomologicalComplex₂.ι_D₁,
        HomologicalComplex₂.d₁_eq _ c h₃ _ _ hj, Linear.comp_units_smul,
        smul_smul, Int.units_mul_self, one_smul]
    · rw [h.zero _ _ h₃, HomologicalComplex.zero_f, zero_comp, zero_comp, smul_zero, zero_comp]
  · rw [ιTotal_totalMapHomotopyHom_assoc h _ _ _ _ hj]
    by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
    · rw [Linear.units_smul_comp, Category.assoc,
        L.ιTotalOrZero_eq c (c₁.prev i₁) i₂
          (c.prev j) (by
            rw [← ComplexShape.prev_π₁ c₂ c h₃, hj]),
        HomologicalComplex₂.ι_D₂]
      by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
      · exact totalMapHomotopy_comm_aux h h₃ h₄ j hj
      · rw [HomologicalComplex₂.d₂_eq_zero _ c _ _ _ h₄, comp_zero,
          smul_zero, HomologicalComplex₂.d₂_eq_zero _ c _ _ _ h₄,
          zero_comp, neg_zero]
    · rw [h.zero _ _ h₃, HomologicalComplex.zero_f, zero_comp, smul_zero, zero_comp, zero_eq_neg]
      by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
      · by_cases h₅ : c.Rel j (c.next j)
        · rw [HomologicalComplex₂.d₂_eq _ c _ h₄ _ (by
              rw [← ComplexShape.next_π₂ c₁ c i₁ h₄, hj]),
            Linear.units_smul_comp, Category.assoc, ιTotal_totalMapHomotopyHom h _ _ _ _
              (by rw [← ComplexShape.next_π₂ c₁ c i₁ h₄,
                hj]),
            h.zero _ _ h₃, HomologicalComplex.zero_f, zero_comp, smul_zero, comp_zero, smul_zero]
        · rw [totalMapHomotopy_zero h _ _ h₅, comp_zero]
      · rw [HomologicalComplex₂.d₂_eq_zero _ c _ _ _ h₄, zero_comp]

/-- A homotopy of bicomplex morphisms in the outer direction induces a homotopy on total
complexes. -/
noncomputable def totalMapHomotopy (h : Homotopy φ ψ) :
    Homotopy (HomologicalComplex₂.total.map φ c)
      (HomologicalComplex₂.total.map ψ c) where
  hom := totalMapHomotopyHom h
  zero := totalMapHomotopy_zero h
  comm := totalMapHomotopy_comm h

end OuterLift

section InnerLift

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape J}
  [DecidableEq J] [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
  [TotalComplexShapeSymmetry c₁ c₂ c]
  {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c] [L.HasTotal c]

/-- Bridges `(flipFunctor.obj K).HasTotal c` (as it appears in `total.map (flipFunctor.map φ)`) to
the existing `K.flip.HasTotal c` instance, which are definitionally equal. -/
instance flipObj_hasTotal : ((HomologicalComplex₂.flipFunctor C c₁ c₂).obj K).HasTotal c :=
  inferInstanceAs (K.flip.HasTotal c)

/-- Naturality of the flip symmetry isomorphism `totalFlipIso` with respect to a bicomplex
morphism `φ : K ⟶ L`: the totalization of `φ` and of its flip are related by conjugation. -/
@[reassoc]
lemma totalFlipIso_hom_naturality (φ : K ⟶ L) :
    (K.totalFlipIso c).hom ≫ HomologicalComplex₂.total.map φ c =
      HomologicalComplex₂.total.map ((HomologicalComplex₂.flipFunctor C c₁ c₂).map φ) c ≫
        (L.totalFlipIso c).hom := by
  ext j i₂ i₁ hj
  simp only [HomologicalComplex.comp_f, HomologicalComplex₂.ιTotal_totalFlipIso_f_hom_assoc,
    Linear.units_smul_comp, HomologicalComplex₂.ιTotal_map, HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.flipFunctor_obj, HomologicalComplex₂.flipFunctor_map_f_f,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom, Linear.comp_units_smul]

/-- The total complex of a bicomplex morphism equals the totalization of its flip, conjugated by
`totalFlipIso`. This is the bridge that lets the *outer* lift `totalMapHomotopy` serve the *inner*
direction after flipping. -/
lemma total_map_eq_flipConjugate (φ : K ⟶ L) :
    HomologicalComplex₂.total.map φ c =
      (K.totalFlipIso c).inv ≫
        HomologicalComplex₂.total.map ((HomologicalComplex₂.flipFunctor C c₁ c₂).map φ) c ≫
        (L.totalFlipIso c).hom := by
  rw [← totalFlipIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- The inner-direction analog of `totalMapHomotopy`. A homotopy between the *flips* of two
bicomplex morphisms `φ, ψ : K ⟶ L` (equivalently, a homotopy in the inner direction of `K`/`L`)
induces a homotopy between their totalizations.

Mirrors Mathlib's `mapBifunctorMapHomotopy₂` (`BifunctorHomotopy.lean:185`): apply the outer lift
`totalMapHomotopy h` on `K.flip` to get a homotopy of the flipped totalizations, then transport
along `totalFlipIso` via `Homotopy.compLeft`/`compRight`, gluing with `Homotopy.ofEq` of
`total_map_eq_flipConjugate`. Stated over abstract shapes so the `c₂ c₁ c` and symmetry instances
do not collide with a diagonal canonical instance. -/
noncomputable def totalMapHomotopy₂ {φ ψ : K ⟶ L}
    (h : Homotopy ((HomologicalComplex₂.flipFunctor C c₁ c₂).map φ)
        ((HomologicalComplex₂.flipFunctor C c₁ c₂).map ψ)) :
    Homotopy (HomologicalComplex₂.total.map φ c) (HomologicalComplex₂.total.map ψ c) :=
  (Homotopy.ofEq (total_map_eq_flipConjugate φ)).trans
    ((((totalMapHomotopy h).compRight (L.totalFlipIso c).hom).compLeft
        (K.totalFlipIso c).inv).trans (Homotopy.ofEq (total_map_eq_flipConjugate ψ).symm))

end InnerLift

end HomologicalComplex₂

/-- The outer Dold–Kan homotopy equivalence before totalization. The remaining `bridge₁Outer`
step is to transport this equivalence through `totalFunctor`. -/
noncomputable def bridge₁OuterPreTotal :
    HomotopyEquiv
      (((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((normalizedMooreComplex (SimplicialObject C)).obj X))
      (((normalizedMooreComplex C).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((alternatingFaceMapComplex (SimplicialObject C)).obj X)) :=
  (normalizedMooreComplex C).mapHomotopyEquiv <|
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (A := SimplicialObject C) (Y := X)

/-- The outer half of `bridge₁`. The remaining work is to lift
`bridge₁OuterPreTotal.homotopyInvHomId` through `totalFunctor`. -/
noncomputable def bridge₁Outer : HomotopyEquiv (N₁.obj X) (M₁ X) where
  hom := inclusionM₁ X
  inv := retractionM₁ X
  homotopyHomInvId := Homotopy.ofEq (inclusionM₁_comp_retractionM₁ X)
  homotopyInvHomId := by
    simpa [retractionM₁, inclusionM₁, M₁, bridge₁OuterPreTotal, HomologicalComplex₂.totalFunctor]
      using HomologicalComplex₂.totalMapHomotopy (c := ComplexShape.down ℕ)
        ((bridge₁OuterPreTotal (C := C) X).homotopyInvHomId)

/-- **General flip-lift (reusable).** A family of homotopies `α.app Y ≃ β.app Y` between two
natural transformations of additive `ChainComplex C ℕ`-valued functors, *natural in `Y`* (the
condition `hnat`), lifts — after `flip` — to a homotopy between the `mapHomologicalComplex`-lifted
bicomplex maps `(mapHomologicalComplex α).app W` and `(mapHomologicalComplex β).app W`.

The point: `(mapHomologicalComplex α).app W` shifts the *outer* (`𝒜`/`W`) degree by `0` and is
`α.app` levelwise; after `flip`, the inner `ChainComplex C ℕ` degree becomes the outer one, and the
homotopy operator is the family `h` applied levelwise. `hnat` is exactly the statement that each
operator `h _ .hom i j` is a chain map in the `𝒜`-direction (commutes with `W`'s differential),
which is what lets the levelwise operators assemble into a genuine bicomplex homotopy. -/
noncomputable def flipMapHomologicalComplexHomotopy {𝒜 : Type*} [Category* 𝒜] [Preadditive 𝒜]
    {F G : 𝒜 ⥤ ChainComplex C ℕ} [F.Additive] [G.Additive] {α β : F ⟶ G}
    (h : ∀ Y, Homotopy (α.app Y) (β.app Y))
    (hnat : ∀ {Y Z : 𝒜} (f : Y ⟶ Z) (i j : ℕ),
      (F.map f).f i ≫ (h Z).hom i j = (h Y).hom i j ≫ (G.map f).f j)
    (W : HomologicalComplex 𝒜 (ComplexShape.down ℕ)) :
    Homotopy
      ((HomologicalComplex₂.flipFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app W))
      ((HomologicalComplex₂.flipFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map
        ((NatTrans.mapHomologicalComplex β (ComplexShape.down ℕ)).app W)) where
  hom m m' :=
    { f := fun r => (h (W.X r)).hom m m'
      comm' := fun r r' _ => by
        simp only [HomologicalComplex₂.flipFunctor_obj, HomologicalComplex₂.flip_X_d,
          Functor.mapHomologicalComplex_obj_d]
        exact (hnat (W.d r r') m m').symm }
  zero m m' hmm' := by
    ext r
    exact (h (W.X r)).zero m m' hmm'
  comm m := by
    ext r
    have key := (h (W.X r)).comm m
    simp only [dNext, prevD, AddMonoidHom.mk'_apply] at key
    simp only [HomologicalComplex.add_f_apply, HomologicalComplex₂.flipFunctor_map_f_f,
      NatTrans.mapHomologicalComplex_app_f, dNext, prevD, AddMonoidHom.mk'_apply,
      HomologicalComplex.comp_f, HomologicalComplex₂.flipFunctor_obj,
      HomologicalComplex₂.flip_d_f, Functor.mapHomologicalComplex_obj_X]
    exact key

/-- Naturality in the simplicial object of the inductive Dold–Kan homotopy `homotopyPToId`'s
operator. Proved by induction on `q`, using `P_f_naturality` (the projections `P q` are natural)
and `hσ'_naturality` (the homotopy operators `hσ'` are natural). -/
lemma alternatingFaceMapComplex_map_f_comp_homotopyPToId_hom {Y Z : SimplicialObject C}
    (f : Y ⟶ Z) (q i j : ℕ) :
    ((alternatingFaceMapComplex C).map f).f i ≫ (homotopyPToId Z q).hom i j =
      (homotopyPToId Y q).hom i j ≫ ((alternatingFaceMapComplex C).map f).f j := by
  simp only [alternatingFaceMapComplex_map_f]
  induction q with
  | zero => simp [homotopyPToId]
  | succ q ih =>
    -- Unfold `homotopyPToId (q+1)` into `(homotopyPToId q).hom + (P q) ≫ (nullHomotopy' (hσ' q))`.
    simp only [homotopyPToId, homotopyHσToZero, Homotopy.trans_hom, Homotopy.ofEq_hom,
      Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom, Homotopy.nullHomotopy'_hom,
      Pi.add_apply, add_zero, zero_add]
    rw [Preadditive.comp_add, Preadditive.add_comp, ih]
    congr 1
    -- Remaining: the `hσ'` summand `f.app ≫ (P q).f i ≫ hσ'… = (P q).f i ≫ hσ'… ≫ f.app`.
    split_ifs with h
    · rw [← Category.assoc, P_f_naturality, Category.assoc, hσ'_naturality, Category.assoc]
    · simp

/-- Naturality, in the simplicial object, of the Dold–Kan contraction homotopy operator for
`PInfty ≃ 𝟙` (i.e. `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.homotopyInvHomId`).
This is the `hnat` input to `flipMapHomologicalComplexHomotopy` for the inner half of `bridge₁`. -/
lemma homotopyInvHomId_hom_naturality {Y Z : SimplicialObject C} (f : Y ⟶ Z) (i j : ℕ) :
    ((alternatingFaceMapComplex C).map f).f i ≫
        (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (A := C) (Y := Z)).homotopyInvHomId.hom i j =
      (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (A := C) (Y := Y)).homotopyInvHomId.hom i j ≫
        ((alternatingFaceMapComplex C).map f).f j := by
  simp only [homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex_homotopyInvHomId,
    Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.add_apply, Pi.zero_apply, zero_add,
    homotopyPInftyToId_hom]
  exact alternatingFaceMapComplex_map_f_comp_homotopyPToId_hom f (j + 1) i j

/-- The inner Dold–Kan homotopy feeding `totalMapHomotopy₂` for `bridge₁Inner`.

`retractionF₁`/`inclusionF₁` are `totalFunctor.map` of the bicomplex maps `R`/`I` obtained by
applying `NatTrans.mapHomologicalComplex` (in the inner functor direction) to
`mooreRetraction`/`mooreInclusion`. The composite `R ≫ I` is `PInfty` in the inner direction, which
is homotopic to `𝟙` (Dold–Kan). This def packages that homotopy after `flip`, so its operator shifts
the (flipped) outer = inner-normalization degree — exactly the shape `totalMapHomotopy₂` consumes.

Assembled from the general `flipMapHomologicalComplexHomotopy` applied to the Dold–Kan contraction
family `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.homotopyInvHomId` (with `α`
the `PInfty`-natural transformation `mooreRetraction ≫ mooreInclusion` and `β = 𝟙`) and its
naturality `homotopyInvHomId_hom_naturality`. -/
noncomputable def retractionF₁InclusionF₁FlipHomotopy :
    Homotopy
      ((HomologicalComplex₂.flipFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map
        ((NatTrans.mapHomologicalComplex mooreRetraction _).app
            ((alternatingFaceMapComplex (SimplicialObject C)).obj X) ≫
          (NatTrans.mapHomologicalComplex mooreInclusion _).app
            ((alternatingFaceMapComplex (SimplicialObject C)).obj X)))
      ((HomologicalComplex₂.flipFunctor C (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map (𝟙 _)) :=
  flipMapHomologicalComplexHomotopy
    (α := mooreRetraction ≫ mooreInclusion) (β := 𝟙 (alternatingFaceMapComplex C))
    (fun Y => (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (A := C) (Y := Y)).homotopyInvHomId)
    (fun f i j => homotopyInvHomId_hom_naturality f i j)
    ((alternatingFaceMapComplex (SimplicialObject C)).obj X)

/-- The inner half of `bridge₁`. Assembled from the inner lift `totalMapHomotopy₂` applied to the
flipped inner Dold–Kan homotopy `retractionF₁InclusionF₁FlipHomotopy`. -/
noncomputable def bridge₁Inner : HomotopyEquiv (M₁ X) (F₁.obj X) where
  hom := inclusionF₁ X
  inv := retractionF₁ X
  homotopyHomInvId := Homotopy.ofEq (inclusionF₁_comp_retractionF₁ X)
  homotopyInvHomId := by
    have H := HomologicalComplex₂.totalMapHomotopy₂ (c := ComplexShape.down ℕ)
      (retractionF₁InclusionF₁FlipHomotopy X)
    -- H : Homotopy (total.map (R ≫ I)) (total.map (𝟙 _)); reduce via map_comp / map_id to
    -- `retractionF₁ X ≫ inclusionF₁ X ≃ 𝟙 (F₁.obj X)`.
    simpa [retractionF₁, inclusionF₁, HomologicalComplex₂.totalFunctor,
      HomologicalComplex₂.total.map_comp, HomologicalComplex₂.total.map_id] using H

/-- The full `bridge₁ : N₁(X) ≃ F₁(X)` assembled from the outer and inner
normalization equivalences. -/
noncomputable def bridge₁ : HomotopyEquiv (N₁.obj X) (F₁.obj X) :=
  (bridge₁Outer X).trans (bridge₁Inner X)

@[reassoc]
lemma bridge₁_hom_eq :
    (bridge₁ X).hom = inclusionN₁ X := by
  show inclusionM₁ X ≫ inclusionF₁ X = inclusionN₁ X
  exact inclusionM₁_comp_inclusionF₁ X

@[reassoc]
lemma bridge₁_inv_eq :
    (bridge₁ X).inv = retractionN₁ X := by
  show retractionF₁ X ≫ retractionM₁ X = retractionN₁ X
  exact retractionF₁_comp_retractionM₁ X

end BisimplicialObject

end CategoryTheory

/-!
## Bridge₁ remaining-work checklist

Architecture is correct and matches the plan (`N₁ ≃ M₁ ≃ F₁`); the strict half is done. Items below
are ordered by dependency. Steps 1–3 are low-risk mechanical ports of Mathlib's
`mapBifunctorMapHomotopy₁`; step 4 is the one genuinely new construction.

- [x] Factorization `N₁ ≃ M₁ ≃ F₁` with `M₁` outer-unnormalized / inner-normalized.
- [x] Four strict identities (`inclusionM₁_comp_inclusionF₁`, `retractionF₁_comp_retractionM₁`,
      `inclusionM₁_comp_retractionM₁`, `inclusionF₁_comp_retractionF₁`) — proved by functoriality.
- [x] `totalMapHomotopyHom` / `ιTotal_totalMapHomotopyHom` / `totalMapHomotopy_zero` — outer (`₁`)
      lift scaffolding, faithful clone of Mathlib `mapBifunctorMapHomotopy.hom₁`/`zero₁`.

- [x] **(1) Port `comm₁_aux` → `totalMapHomotopy_comm_aux`.** Analog of
      `Mathlib/Algebra/Homology/BifunctorHomotopy.lean:94` (`comm₁_aux`). Simpler than the bifunctor
      version: since `h.hom i₁' i₁` is directly an inner chain map, the bifunctor's
      `NatTrans.naturality_assoc` + `f₂.comm` collapse to a single `HomologicalComplex.Hom.comm_assoc`;
      the sign bookkeeping (`ε₁_ε₂`, `neg_mul`, `Units.neg_smul`) and `d₂_eq` /
      `ιTotal_totalMapHomotopyHom` / `ιTotalOrZero_eq` rewrites are otherwise the same.

- [x] **(2) Finish `totalMapHomotopy_comm`.** Ported from Mathlib `comm₁`
      (`BifunctorHomotopy.lean:114`). Two adjustments vs. the literal port, both because our `total`
      terms have one fewer `≫`-factor than the bifunctor terms (no `F.map ≫ F.obj.map` split):
      each branch drops one `Category.assoc` (and branch ② one `Linear.comp_units_smul`); the
      degenerate `K.d` is killed by `HomologicalComplex₂.shape_f` (one-step, no `zero_f`). Also
      split the goal-normalizing `simp only` so `add_left_inj` (cancelling the common `ψ` summand)
      runs only *after* `add_f_apply`/`comp_f` distribute the LHS.

- [x] **(3) Verify `bridge₁Outer.homotopyInvHomId`.** Resolved automatically — once
      `totalMapHomotopy` became `sorry`-free, the existing `simpa … using totalMapHomotopy …`
      closes with no further changes.

- [x] **(4a) Drafted the decomposition for the inner half.** `bridge₁Inner.homotopyInvHomId` is now
      `sorry`-free: it is `totalMapHomotopy₂ retractionF₁InclusionF₁FlipHomotopy` with the
      `total.map_comp` / `total.map_id` plumbing handled by `simpa`. The work reduces to two `sorry`d
      leaves below.

- [x] **(4b) Fill `totalMapHomotopy₂` (inner lift).** Done via **Path B (generalize)**: the whole
      outer-lift block (`totalMapHomotopyHom`, `…_zero`, `…_comm_aux`, `…_comm`, `totalMapHomotopy`)
      was generalized from `(down ℕ, down ℕ, down ℕ)` to abstract `c₁ c₂ c` with
      `[TotalComplexShape c₁ c₂ c] [DecidableEq J] [K.HasTotal c]`. `totalMapHomotopy₂` then lives in
      a separate `InnerLift` section over abstract shapes (with `[TotalComplexShape c₂ c₁ c]`,
      `[TotalComplexShapeSymmetry c₁ c₂ c]`): it conjugates `totalMapHomotopy` of the flipped homotopy
      by `totalFlipIso` via `Homotopy.compLeft`/`compRight`/`ofEq` of `total_map_eq_flipConjugate`
      (proved from the new `totalFlipIso_hom_naturality`). Because the shapes are abstract there is no
      diagonal diamond. At `down ℕ` the previously-missing
      `TotalComplexShapeSymmetry (down ℕ)³` is supplied as a top-level instance w.r.t. the *canonical*
      `TotalComplexShape` (sign `σ i₁ i₂ = ε (i₁ * i₂)`), so the `down ℕ` instantiation is fully
      coherent (no `letI`, no diamond).

- [x] **(4c) Drafted the decomposition for `retractionF₁InclusionF₁FlipHomotopy`.** The def itself
      is now `sorry`-free: it is `flipMapHomologicalComplexHomotopy` applied to the Dold–Kan
      contraction family `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.homotopyInvHomId`
      (with `α = mooreRetraction ≫ mooreInclusion`, `β = 𝟙`) and its naturality
      `homotopyInvHomId_hom_naturality`. The `(mapHomologicalComplex α).app W = R ≫ I` and
      `(mapHomologicalComplex β).app W = 𝟙` matches hold definitionally (both are levelwise `α.app`),
      so no transport plumbing is needed. The work reduces to two `sorry`d leaves below.

- [x] **(4c-i) Fill `flipMapHomologicalComplexHomotopy` (general, reusable flip-lift).** Done. Built
      the `Homotopy` structure directly: operator `hom m m'` is the chain map in the `𝒜`-direction
      with component `(h (W.X r)).hom m m'`, whose `comm'` is exactly `(hnat (W.d r r') m m').symm`
      after `flip_X_d` + `mapHomologicalComplex_obj_d`; `zero` is `ext r` + `(h (W.X r)).zero`; and
      `comm` reduces — after `ext r`, `flipFunctor_map_f_f`/`mapHomologicalComplex_app_f`, and
      expanding `dNext`/`prevD` on both sides (with `flip_d_f`, keeping `next`/`prev` symbolic so no
      `m = 0` case split) — to exactly `(h (W.X r)).comm m`.

- [x] **(4c-ii) Fill `homotopyInvHomId_hom_naturality` (Dold–Kan operator naturality).** Done. Reduced
      (via the `@[simps]` forms `…homotopyInvHomId`, `homotopyPInftyToId_hom`) to naturality of
      `homotopyPToId`'s operator, extracted as the general lemma
      `alternatingFaceMapComplex_map_f_comp_homotopyPToId_hom`: induction on `q`, unfolding
      `homotopyPToId (q+1)` (`trans`/`add`/`compLeft`/`nullHomotopy'`) and closing with the Mathlib
      naturalities `P_f_naturality` (projections) and `hσ'_naturality` (homotopy operators).
-/
